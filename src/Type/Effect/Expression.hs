{-# OPTIONS_GHC -Wall #-}
module Type.Effect.Expression where

import Control.Arrow (second)
import qualified Control.Monad as Monad
import qualified Data.Map as Map

import qualified AST.Expression.General as E
import qualified AST.Expression.Canonical as Canonical
import qualified AST.Literal as Lit
import qualified AST.Pattern as P
import qualified AST.Type as ST
import qualified AST.Variable as V
import qualified Reporting.Annotation as A
import qualified Reporting.Error.Type as Error
import qualified Reporting.Region as R
import qualified Type.Effect.Literal as Literal
import qualified Type.Effect.Pattern as Pattern
--import qualified Type.Environment as Env
--import qualified Type.Fragment as Fragment
import qualified Type.Type

import Type.Effect as Effect

constrain
    :: Effect.Environment
    -> Canonical.Expr
    -> TypeAnnot
    -> IO AnnotConstr
constrain env annotatedExpr@(A.A region expression) tipe =
    let
        (<?) = CInstance region
    in
    case expression of
      E.Literal lit ->
          Literal.constrain env region lit tipe

      E.GLShader _uid _src gltipe -> error "GLSL not supported"
          {- exists $ \attr ->
          exists $ \unif ->
            let
                shaderTipe a u v =
                    Effect.getType env "WebGL.Shader" <| a <| u <| v

                glToType glTipe =
                    Effect.getType env (Lit.glTipeName glTipe)

                makeRec accessor baseRec =
                    let decls = accessor gltipe
                    in
                      if Map.size decls == 0 then
                          baseRec
                      else
                          error "TODO" --record (Map.map glToType decls) baseRec

                attribute = makeRec Lit.attribute attr
                uniform = makeRec Lit.uniform unif
                varying = makeRec Lit.varying (TermN EmptyRecord1)
            in
                return (CEqual Error.Shader region (shaderTipe attribute uniform varying) tipe) -}

      E.Var var ->
          let name = V.toString var
          in
              return (if name == E.saveEnvName then CSaveEnv else name <? tipe)

      --We never know if a range is empty or not without evaluating the input arguments
      E.Range lowExpr highExpr ->
        return $ CEqual (error "TODO range hint") region tipe (TopAnnot)
      {-
          existsNumber $ \n ->
              do  lowCon <- constrain env lowExpr n
                  highCon <- constrain env highExpr n
                  return $ CAnd
                    [ lowCon
                    , highCon
                    , CEqual Error.Range region (list n) tipe
                    ] -}

      E.ExplicitList exprs ->
          constrainList env region exprs tipe

      E.Binop op leftExpr rightExpr ->
          constrainBinop env region op leftExpr rightExpr tipe

      E.Lambda pattern body ->
          exists $ \argType ->
          exists $ \resType ->
              do  fragment <- Pattern.constrain env pattern argType
                  bodyCon <- constrain env body resType
                  let con =
                        ex (Effect.vars fragment)
                            (CLet [monoscheme (Effect.typeEnv fragment)]
                                  (Effect.typeConstraint fragment /\ bodyCon)
                            )
                  return $ con /\ CEqual Error.Lambda region (argType ==> resType) tipe

      E.App _ _ ->
          let
            (f:args) = E.collectApps annotatedExpr
          in
            constrainApp env region f args tipe

      E.If branches finally ->
          constrainIf env region branches finally tipe

      E.Case expr branches ->
          constrainCase env region expr branches tipe

      E.Data name exprs ->
          do  vars <- Monad.forM exprs $ \_ -> mkVar
              let pairs = zip exprs (map VarAnnot vars)
              argConstrs <- mapM (\(expr, tp) -> constrain env expr tp) pairs
              let dataTypeConstr =
                    CEqual (error "Hint TODO") region tipe $
                      ClosedSet [(name, map snd pairs)]
              --TODO why need ex here?
              return $ ex vars (CAnd $ dataTypeConstr : argConstrs)

      {-
      E.Access expr label ->
          exists $ \t ->
              constrain env expr (record (Map.singleton label tipe) t)

      E.Update expr fields ->
          exists $ \t ->
              do  oldVars <- mapM (\_ -> mkVar) fields
                  let oldFields = Map.fromList (zip (map fst fields) (map VarAnnot oldVars))
                  cOld <- ex oldVars <$> constrain env expr (record oldFields t)

                  newVars <- mapM (\_ -> mkVar) fields
                  let newFields = Map.fromList (zip (map fst fields) (map VarAnnot newVars))
                  let cNew = CEqual Error.Record region (record newFields t) tipe

                  cs <- Monad.zipWithM (constrain env) (map snd fields) (map VarAnnot newVars)

                  return $ cOld /\ ex newVars (CAnd (cNew : cs))

      E.Record fields ->
          do  vars <- Monad.forM fields (\_ -> mkVar)
              fieldCons <-
                  Monad.zipWithM
                      (constrain env)
                      (map snd fields)
                      (map VarAnnot vars)
              let fields' = Map.fromList (zip (map fst fields) (map VarAnnot vars))
              let recordType = record fields' (TermN EmptyRecord1)
              return (ex vars (CAnd (fieldCons ++ [CEqual Error.Record region recordType tipe])))
              -}

      E.Let defs body ->
          do  bodyCon <- constrain env body tipe

              (Info schemes rqs fqs headers c2 c1) <-
                  Monad.foldM
                      (constrainDef env)
                      (Info [] [] [] Map.empty CTrue CTrue)
                      (concatMap expandPattern defs)

              let letScheme =
                    [ Scheme rqs fqs (CLet [monoscheme headers] c2) headers ]

              return $ CLet schemes (CLet letScheme (c1 /\ bodyCon))

      E.Port impl ->
          case impl of
            E.In _ _ ->
                return CTrue

            E.Out _ expr _ ->
                constrain env expr tipe

            E.Task _ expr _ ->
                constrain env expr tipe


-- CONSTRAIN APP

constrainApp
    :: Effect.Environment
    -> R.Region
    -> Canonical.Expr
    -> [Canonical.Expr]
    -> TypeAnnot
    -> IO AnnotConstr
constrainApp env region f args tipe =
  do  funcVar <- mkVar
      funcCon <- constrain env f (VarAnnot funcVar)

      (vars, argCons, _, argMatchCons, _, returnVar) <-
          argConstraints env maybeName region (length args) funcVar 1 args

      let returnCon =
            CEqual (Error.Function maybeName) region (VarAnnot returnVar) tipe

      return $ ex (funcVar : vars) $
        CAnd (funcCon : argCons  ++ argMatchCons ++ [returnCon])
  where
    maybeName =
      case f of
        A.A _ (E.Var canonicalName) ->
            Just canonicalName

        _ ->
          Nothing


argConstraints
    :: Effect.Environment
    -> Maybe V.Canonical
    -> R.Region
    -> Int
    -> AnnVar
    -> Int
    -> [Canonical.Expr]
    -> IO ([AnnVar], [AnnotConstr], [AnnotConstr], [AnnotConstr], Maybe R.Region, AnnVar)
argConstraints env name region totalArgs overallVar index args =
  case args of
    [] ->
      return ([], [], [], [], Nothing, overallVar)

    expr@(A.A subregion _) : rest ->
      do  argVar <- mkVar
          argCon <- constrain env expr (VarAnnot argVar)
          argIndexVar <- mkVar
          localReturnVar <- mkVar

          (vars, argConRest, decomposeLambdaRest, subsetOfMatchedRest, restRegion, returnVar) <-
              argConstraints env name region totalArgs localReturnVar (index + 1) rest

          let arityRegion =
                maybe subregion (R.merge subregion) restRegion

          --Decompose our lambda into (to ==> From)
          let decomposeLambdaCon =
                CEqual
                  (Error.FunctionArity name (index - 1) totalArgs arityRegion)
                  region
                  (VarAnnot argIndexVar ==> VarAnnot localReturnVar)
                  (VarAnnot overallVar)

          --Constraint so that argument expressions contain no patterns
          --Which cannot be matched by the function (specified by the first)
          --Argument of the lambda annotation
          let subsetOfMatchedCon =
                CContainsOnly
                  region
                  (VarAnnot argIndexVar)
                  (VarAnnot argVar)

          return
            ( argVar : argIndexVar : localReturnVar : vars
            , argCon : argConRest
            , decomposeLambdaCon : decomposeLambdaRest
            , subsetOfMatchedCon : subsetOfMatchedRest
            , Just arityRegion
            , returnVar
            )




-- CONSTRAIN BINOP

constrainBinop
    :: Effect.Environment
    -> R.Region
    -> V.Canonical
    -> Canonical.Expr
    -> Canonical.Expr
    -> TypeAnnot
    -> IO AnnotConstr
constrainBinop env region op leftExpr@(A.A leftRegion _) rightExpr@(A.A rightRegion _) tipe =
  do  leftVar <- mkVar
      rightVar <- mkVar

      leftCon <- constrain env leftExpr (VarAnnot leftVar)
      rightCon <- constrain env rightExpr (VarAnnot rightVar)

      leftVar' <- mkVar
      rightVar' <- mkVar
      answerVar <- mkVar

      let opType = VarAnnot leftVar' ==> VarAnnot rightVar' ==> VarAnnot answerVar

      --Same as application, ensure that given arguments contain no patterns
      --That the binop can't match

      return $
        ex [leftVar,rightVar,leftVar',rightVar',answerVar] $ CAnd $
          [ leftCon
          , rightCon
          , CInstance region (V.toString op) opType
          , CContainsOnly region (VarAnnot leftVar) (VarAnnot leftVar')
          , CContainsOnly region (VarAnnot rightVar) (VarAnnot rightVar')
          , CEqual (Error.Binop op) region (VarAnnot answerVar) tipe
          ]


-- CONSTRAIN LISTS

constrainList
    :: Effect.Environment
    -> R.Region
    -> [Canonical.Expr]
    -> TypeAnnot
    -> IO AnnotConstr
constrainList env region exprs tipe =
  case exprs of
    [] ->
      return $ CEqual Error.List region tipe (ClosedSet [("[]", [])]) --TODO open or closed?

    (expr : rest) -> do
      restAnnot <- VarAnnot <$> mkVar
      restConstr <- constrainList env region rest  restAnnot
      let consConstr = CEqual Error.List region tipe (ClosedSet [("::", [restAnnot])])
      return $ CAnd [consConstr,  restConstr]
  {-
  do  (exprInfo, exprCons) <-
          unzip <$> mapM elementConstraint exprs

      (vars, cons) <- pairCons region Error.ListElement varToCon exprInfo

      return $ ex vars (CAnd (exprCons ++ cons))
  where
    elementConstraint expr@(A.A region' _) =
      do  var <- mkVar
          con <- constrain env expr (VarAnnot var)
          return ( (var, region'), con )

    varToCon var =
      CEqual Error.List region (Effect.getType env "List" <| VarAnnot var) tipe
-}

-- CONSTRAIN IF EXPRESSIONS

constrainIf
    :: Effect.Environment
    -> R.Region
    -> [(Canonical.Expr, Canonical.Expr)]
    -> Canonical.Expr
    -> TypeAnnot
    -> IO AnnotConstr
constrainIf env region branches finally tipe =
  do  let (conditions, branchExprs) =
            second (++ [finally]) (unzip branches)

      (condVars, condCons) <-
          unzip <$> mapM constrainCondition conditions

      (branchInfo, branchExprCons) <-
          unzip <$> mapM constrainBranch branchExprs

      (vars,cons) <- branchCons tipe branchInfo

      --TODO what is ex doing here?
      return $ ex (condVars ++ vars) (CAnd (condCons ++ branchExprCons ++ cons))
  where
    bool =
      Effect.getType env "Bool"

    constrainCondition condition@(A.A condRegion _) =
      do  condVar <- mkVar
          condCon <- constrain env condition (VarAnnot condVar)
          let boolCon = CEqual Error.IfCondition condRegion (VarAnnot condVar) bool
          return (condVar, CAnd [ condCon, boolCon ])

    constrainBranch expr@(A.A branchRegion _) =
      do  branchVar <- mkVar
          exprCon <- constrain env expr (VarAnnot branchVar)
          return
            ( (branchVar, branchRegion)
            , exprCon
            )

    --Constraint that the value of an if contains at least all patterns
    --As the annotation of a branch
    branchCons finalTipe branchInfo =
      case branchInfo of
        [(thenVar, _), (elseVar, _)] ->
            return
              ( [thenVar,elseVar]
              , [ CContainsAtLeast region finalTipe (VarAnnot thenVar)
                , CContainsAtLeast region finalTipe (VarAnnot elseVar)
                , varToCon thenVar
                ]
              )

        _ ->
            pairCons region Error.MultiIfBranch varToCon branchInfo

    varToCon var =
      CEqual Error.If region (VarAnnot var) tipe


-- CONSTRAIN CASE EXPRESSIONS

constrainCase
    :: Effect.Environment
    -> R.Region
    -> Canonical.Expr
    -> [(P.CanonicalPattern, Canonical.Expr)]
    -> TypeAnnot
    -> IO AnnotConstr
constrainCase env region expr branches tipe =
  do  exprVar <- mkVar
      exprCon <- constrain env expr (VarAnnot exprVar)

      (branchResultInfo, branchResultConstraints, branchPatternAnnots) <-
          unzip3 <$> mapM branch branches

      --TODO what is this?
      (vars, cons) <- pairCons region Error.CaseBranch varToCon branchResultInfo

      --The type of the value we split on must contain only the patterns we match on
      let inPatternsConstrs = error "TODO join patterns"

      --The annotation of the case statement must contain each possible branch result annotation
      let joinBranchesConstr = --TODO which region
            CAnd $ map (\branchVar -> CContainsAtLeast region tipe (VarAnnot branchVar)) $ vars

      --TODO what is ex doing?
      return $ ex (exprVar : vars) $
        CAnd (exprCon : joinBranchesConstr : cons ++ branchResultConstraints ++ inPatternsConstrs)
  where
    branch (pattern, branchExpr@(A.A branchRegion _)) =
        do  branchVar <- mkVar
            patternVar <- mkVar
            fragment <- Pattern.constrain env pattern (VarAnnot patternVar)
            branchCon <- constrain env branchExpr (VarAnnot branchVar)
            return
                ( (branchVar, branchRegion)
                , CLet [Effect.toScheme fragment] branchCon
                , VarAnnot patternVar
                )

    varToCon var =
      CEqual Error.Case region tipe (VarAnnot var)


-- COLLECT PAIRS

data Pair = Pair
    { _index :: Int
    , _var1 :: AnnVar
    , _var2 :: AnnVar
    , _region :: R.Region
    }


pairCons
    :: R.Region
    -> (Int -> R.Region -> Error.Hint)
    -> (AnnVar -> AnnotConstr)
    -> [(AnnVar, R.Region)]
    -> IO ([AnnVar], [AnnotConstr])
pairCons region pairHint varToCon items =
  let
    pairToCon (Pair index var1 var2 subregion) =
      CEqual (pairHint index subregion) region (VarAnnot var1) (VarAnnot var2)
  in
  case collectPairs 2 items of
    Nothing ->
        do  var <- mkVar
            return ([var], [varToCon var])

    Just (pairs, var) ->
        return (map fst items, map pairToCon pairs ++ [varToCon var])


collectPairs :: Int -> [(AnnVar, R.Region)] -> Maybe ([Pair], AnnVar)
collectPairs index items =
  case items of
    [] ->
        Nothing

    (var,_) : [] ->
        Just ([], var)

    (var,_) : rest@((var',region) : _) ->
        do  (pairs, summaryVar) <- collectPairs (index+1) rest
            return (Pair index var var' region : pairs, summaryVar)


-- EXPAND PATTERNS

expandPattern :: Canonical.Def -> [Canonical.Def]
expandPattern def@(Canonical.Definition facts lpattern expr maybeType) =
  let (A.A patternRegion pattern) = lpattern
  in
  case pattern of
    P.Var _ ->
        [def]

    _ ->
        mainDef : map toDef vars
      where
        vars = P.boundVarList lpattern

        combinedName = "$" ++ concat vars

        pvar name =
            A.A patternRegion (P.Var name)

        localVar name =
            A.A patternRegion (E.localVar name)

        mainDef = Canonical.Definition facts (pvar combinedName) expr maybeType

        toDef name =
            let extract =
                  E.Case (localVar combinedName) [(lpattern, localVar name)]
            in
                Canonical.Definition facts (pvar name) (A.A patternRegion extract) Nothing


-- CONSTRAIN DEFINITIONS

data Info = Info
    { iSchemes :: [AnnScheme]
    , iRigid :: [AnnVar]
    , iFlex :: [AnnVar]
    , iHeaders :: Map.Map String (A.Located TypeAnnot)
    , iC2 :: AnnotConstr
    , iC1 :: AnnotConstr
    }


constrainDef :: Effect.Environment -> Info -> Canonical.Def -> IO Info
constrainDef env info (Canonical.Definition _ (A.A patternRegion pattern) expr maybeTipe) =
  let qs = [] -- should come from the def, but I'm not sure what would live there...
  in
  case (pattern, maybeTipe) of
    (P.Var name, Just (A.A typeRegion tipe)) ->
        constrainAnnotatedDef env info qs patternRegion typeRegion name expr tipe

    (P.Var name, Nothing) ->
        constrainUnannotatedDef env info qs patternRegion name expr

    _ ->
        error "canonical definitions must not have complex patterns as names in the contstraint generation phase"


constrainAnnotatedDef
    :: Effect.Environment
    -> Info
    -> [String]
    -> R.Region
    -> R.Region
    -> String
    -> Canonical.Expr
    -> ST.Canonical
    -> IO Info
constrainAnnotatedDef env info qs patternRegion typeRegion name expr tipe =
  do  -- Some mistake may be happening here. Currently, qs is always [].
      rigidVars <- mapM mkRigid qs

      flexiVars <- mapM mkNamedVar qs

      let env' = Effect.addValues env (zip qs flexiVars)

      (vars, typ) <- Effect.instantiateType env tipe Map.empty

      let scheme =
            Scheme
              { _rigidQuantifiers = []
              , _flexibleQuantifiers = flexiVars ++ vars
              , _constraint = CTrue
              , _header = Map.singleton name (A.A patternRegion typ)
              }

      var <- mkVar
      defCon <- constrain env' expr (VarAnnot var)
      let annCon =
            CEqual (Error.BadTypeAnnotation name) typeRegion typ (VarAnnot var)

      return $ info
          { iSchemes = scheme : iSchemes info
          , iC1 = iC1 info /\ ex [var] (defCon /\ fl rigidVars annCon)
          }


constrainUnannotatedDef
    :: Effect.Environment
    -> Info
    -> [String]
    -> R.Region
    -> String
    -> Canonical.Expr
    -> IO Info
constrainUnannotatedDef env info qs patternRegion name expr =
  do  -- Some mistake may be happening here. Currently, qs is always [].
      rigidVars <- mapM mkRigid qs

      v <- mkVar

      let tipe = VarAnnot v

      let env' = Effect.addValues env (zip qs rigidVars)

      con <- constrain env' expr tipe

      return $ info
          { iRigid = rigidVars ++ iRigid info
          , iFlex = v : iFlex info
          , iHeaders = Map.insert name (A.A patternRegion tipe) (iHeaders info)
          , iC2 = con /\ iC2 info
          }