{-# OPTIONS_GHC -Wall #-}
module Type.Effect.Expression where

import Control.Arrow (second)
import qualified Control.Monad as Monad
import qualified Data.Map as Map
import qualified Data.List as List

import qualified AST.Expression.General as E
import qualified AST.Expression.Canonical as Canonical
import qualified AST.Pattern as P
import qualified AST.Type as ST
import qualified AST.Variable as V
import qualified AST.Module.Name as ModName
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

      E.Var var ->
        case (V.home var) of
          --We always assume that a Native value accepts and returns all patterns
          V.Module (ModName.Canonical _ raw)
            | ModName.isNative raw ->
              return $ CEqual region tipe TopAnnot
          _ ->
            let name = V.toString var
            in
              return (if name == E.saveEnvName then CSaveEnv else name <? tipe)

      --We never know if a range is empty or not without evaluating the input arguments
      E.Range lowExpr highExpr ->
        return $ CEqual region tipe (TopAnnot)
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

      E.Lambda pattern body -> do
          argType <- VarAnnot <$> mkVar
          resType <- VarAnnot <$> mkVar
          fragment <- Pattern.constrain env pattern argType
          bodyCon <- constrain env body resType
          let con =
                ex (Effect.vars fragment)
                    (CLet [monoscheme (Effect.typeEnv fragment)]
                          (Effect.typeConstraint fragment /\ bodyCon)
                    )
          return $ con /\ CEqual region (argType ==> resType) tipe

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
                    CEqual region tipe $
                      SinglePattern name $ map snd pairs
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

              (Info vars headers constr) <-
                  Monad.foldM
                      (constrainDef env)
                      (Info [] Map.empty CTrue)
                      (concatMap expandPattern defs)
              --We solve our def constraints with our defs in a monoscheme
              --But we generalize them in the body
              let letScheme =
                    [ Scheme vars (CLet [monoscheme headers] constr) headers ]

              return $ CLet letScheme bodyCon

      E.Port impl ->
          case impl of
            E.In _ _ ->
                return CTrue

            E.Out _ expr _ ->
                constrain env expr tipe

            E.Task _ expr _ ->
                constrain env expr tipe

      _ -> return CTrue

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
            CEqual region (VarAnnot returnVar) tipe

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
                  region
                  (VarAnnot argIndexVar ==> VarAnnot localReturnVar)
                  (VarAnnot overallVar)

          --The constraints from the functon apply to the arguments
          --TODO enforce subset constraints here?
          let subsetOfMatchedCon =
                CEqual
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

      --The constraints from the functon apply to the arguments
      --TODO enforce subset constraints here?

      return $
        ex [leftVar,rightVar,leftVar',rightVar',answerVar] $ CAnd $
          [ leftCon
          , rightCon
          , CInstance region (V.toString op) opType
          , CEqual region (VarAnnot leftVar) (VarAnnot leftVar')
          , CEqual region (VarAnnot rightVar) (VarAnnot rightVar')
          , CEqual region (VarAnnot answerVar) tipe
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
      return $ CEqual region tipe (SinglePattern "[]" [])

    (expr : rest) -> do
      restAnnot <- VarAnnot <$> mkVar
      restConstr <- constrainList env region rest  restAnnot
      let consConstr = CEqual region tipe (SinglePattern "::" [restAnnot])
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
          let boolCon = CEqual condRegion (VarAnnot condVar) bool
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
              , [ CSubEffect region (VarAnnot thenVar) finalTipe
                , CSubEffect region (VarAnnot elseVar) finalTipe
                , varToCon thenVar
                ]
              )

        _ ->
            pairCons region Error.MultiIfBranch varToCon branchInfo

    varToCon var =
      CEqual region (VarAnnot var) tipe


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

      let matchedSet = Pattern.patternLitAnnot env $ map fst branches
      --The type of the value we split on must contain only the patterns we match on
      let wrapReal = error "TODO better pattern constr solution"
      let inPatternsConstr = CSubEffect region (VarAnnot exprVar) (wrapReal matchedSet) -- TODO join patterns

      --The annotation of the case statement must contain each possible branch result annotation
      let joinBranchesConstr = --TODO which region
            CAnd $ map (\branchVar -> CSubEffect region (VarAnnot branchVar) tipe) $ vars

      --TODO what is ex doing?
      return $ ex (exprVar : vars) $
        CAnd (exprCon : joinBranchesConstr  : inPatternsConstr : branchResultConstraints ++ cons )
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
      CEqual region tipe (VarAnnot var)


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
      CEqual region (VarAnnot var1) (VarAnnot var2)
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
-- We don't need schemes, they're for annotations
data Info = Info
    {
      iVars :: [AnnVar]
    , iHeaders :: Map.Map String (A.Located TypeAnnot)
    , iConstr :: AnnotConstr
    }


constrainDef :: Effect.Environment -> Info -> Canonical.Def -> IO Info
constrainDef env info (Canonical.Definition _ (A.A patternRegion pattern) expr maybeTipe) =
  case pattern of
    P.Var name ->
        do  -- Some mistake may be happening here. Currently, qs is always [].
            rhsVar <- mkVar

            let tipe = VarAnnot rhsVar

            --TODO what do we add to env here?
            con <- constrain env expr tipe

            return $ info
                { iVars = rhsVar : iVars info
                , iHeaders = Map.insert name (A.A patternRegion tipe) (iHeaders info)
                , iConstr = con /\ iConstr info
                }

    _ ->
        error "canonical definitions must not have complex patterns as names in the contstraint generation phase"
