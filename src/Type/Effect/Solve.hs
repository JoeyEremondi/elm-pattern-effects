module Type.Effect.Solve where

import Type.Effect
import Control.Monad.Writer
import qualified  Control.Monad.State as State
--import Control.Monad.Trans
--import Control.Monad (forM, forM_, filterM)

import qualified Data.List as List
import qualified Data.Set as Set

import Reporting.Annotation as A
import Reporting.Warning as Warning

import qualified Data.UnionFind.IO as UF

import qualified Data.Map as Map
import qualified Data.Maybe as Maybe

import qualified Reporting.Region as R
import Debug.Trace (trace)

solve
  :: AnnotConstr
  -> IO ( [(R.Region, Warning.Warning)]
     , Map.Map String (CanonicalAnnot, [Int], [CanonicalConstr]))
solve c = do
  let
      stateComp = runWriterT $ solveSubsetConstraints c
      ioComp = State.runStateT stateComp $ SolverState Map.empty Map.empty
  (((), warnings), finalState) <- ioComp
  finalEnv <- forM (Map.toList $ sSavedEnv finalState) $ \(s, StoredScheme quants constrList annVar) -> do
    ourAnnot <- toCanonicalAnnot (VarAnnot annVar)
    quantData <- forM quants $ \(AnnVar (p, _)) -> UF.descriptor p
    let quantIDs = List.map _uniqueId quantData
    finalConstrs <- forM constrList toCanonicalConstr
    return (s, (ourAnnot, quantIDs, finalConstrs)) --TODO translate constraints
  return (warnings, Map.fromList finalEnv)

toCanonicalConstr :: EmittedConstr -> IO CanonicalConstr
toCanonicalConstr c = case c of
  ESubEffect r a1 a2 -> CanonSubtype <$> toCanonicalAnnot a1 <*> toCanonicalAnnot a2
  ECanBeMatchedBy r a1 real -> CanonSubtype <$> toCanonicalAnnot a1 <*> return (CanonLit real)
  EMatchesImplies _ (a1, real) (a2, a3) -> do
    c1 <- toCanonicalAnnot a1
    c2 <- toCanonicalAnnot a2
    c3 <- toCanonicalAnnot a3
    return $ CanonImpl (c1, real) (c2, c3)

toCanonicalAnnot :: TypeAnnot -> IO CanonicalAnnot
toCanonicalAnnot = toCanonicalHelper toCanonicalAnnot canonLowerBound _ub

canonLowerBound :: TypeAnnot -> IO CanonicalAnnot
canonLowerBound = toCanonicalHelper canonLowerBound toCanonicalAnnot _lb

emitWarnings x = do
  forM x $ \_ -> liftIO $ putStrLn $ "Emitting warning"
  tell x

toCanonicalHelper co contra getCo a = case a of
  VarAnnot (AnnVar (pt, _)) -> do
    ourData <- UF.descriptor pt

    ourData <- UF.descriptor pt
    case (_annRepr ourData) of
      Nothing ->
        return $ CanonVar $ _uniqueId ourData
      Just repr ->
        co repr
  SinglePattern s subs -> do
    canonSubs <- forM subs co
    return $ CanonPatDict $ Set.singleton (s, canonSubs)
  LambdaAnn a b ->
    CanonLambda <$> contra a <*> co b
  TopAnnot ->
    return CanonTop
  ReturnsTop ->
    --TODO find out if has function type?
    return CanonTop

data StoredScheme = StoredScheme [AnnVar] [EmittedConstr] AnnVar | StoredMono AnnVar

--TODO shouldn't this hold schemes, not vars?
type Env = Map.Map String StoredScheme

data SolverState =
  SolverState
  { sEnv :: Env
  , sSavedEnv :: Env
  }

data EmittedConstr =
    ESubEffect R.Region TypeAnnot TypeAnnot
  | ECanBeMatchedBy R.Region TypeAnnot RealAnnot
  | EMatchesImplies R.Region (TypeAnnot, RealAnnot) (TypeAnnot, TypeAnnot)
  deriving (Show)

getEnv :: SolverM' a Env
getEnv =
    State.gets sEnv

modifyEnv :: (Env -> Env) -> SolverM' a ()
modifyEnv f =
    State.modify $ \state -> state { sEnv = f (sEnv state) }

saveLocalEnv :: SolverM' a ()
saveLocalEnv =
  do  currentEnv <- getEnv
      State.modify $ \state -> state { sSavedEnv = currentEnv }

type SolverM' a =  WriterT [a] (State.StateT SolverState IO)

type WorklistM = SolverM' (R.Region, Warning.Warning)

type SolverM = WorklistM

type Point = UF.Point AnnotData

getRepr :: AnnVar -> SolverM' a (Maybe TypeAnnot)
getRepr (AnnVar (pt, _)) =
   liftIO $ _annRepr <$> UF.descriptor pt


setRepr :: AnnVar -> TypeAnnot -> SolverM' a ()
setRepr (AnnVar (pt, _)) repr = liftIO $
  case repr of
    (VarAnnot _) -> error "Should never set repr to another var"
    _ -> do
      annData <- UF.descriptor pt
      UF.setDescriptor pt $ annData {_annRepr = Just repr}

union :: AnnVar -> AnnVar -> SolverM' a ()
union (AnnVar (pt1, _)) (AnnVar (pt2, _)) =
  liftIO $ UF.union pt1 pt2

areSame :: AnnVar -> AnnVar -> SolverM' a Bool
areSame (AnnVar (pt1, _)) (AnnVar (pt2, _)) = liftIO $ UF.equivalent pt1 pt2

applyUnifications :: AnnotConstr -> SolverM [EmittedConstr]
applyUnifications con =
  case con of
    CEqual _ r1 r2 -> do
      _ <- unifyAnnots r1 r2
      return []
    CAnd constrs -> do
      andConstraints <- forM constrs applyUnifications
      return $ concat andConstraints
    CLet schemes letConstr -> do
      oldEnv <- getEnv
      --TODO do something with vars in the scheme?
      schemeSolutions <- forM schemes (solveScheme oldEnv)
      let (schemeEmitted, headerList) = unzip schemeSolutions
      let headers =  Map.unions headerList
      modifyEnv $ \env -> Map.union headers env
      letEmitted <- applyUnifications letConstr
      --TODO occurs check?
      modifyEnv $ \_ -> oldEnv
      return $ letEmitted ++ (concat schemeEmitted)
    CInstance r var annot -> do
      env <- getEnv
      emittedFromFresh <-
        case Map.lookup var env of
          Nothing -> error $ "Could not find name " ++ show var ++ " in Effect.Solve\nenv:\n" ++ show (Map.keys env)
          Just (StoredMono storedVar) ->
            applyUnifications $ CEqual r (VarAnnot storedVar) annot
          Just (StoredScheme quants constr annVar) -> do
            (freshEmitted, newVar) <- makeFreshCopy quants constr annVar
            --Unify the type of the variable use with our newly instantiated type
            unifyAnnots annot (VarAnnot newVar)
            --Apply our instantiated constraints to that type
            return freshEmitted
      return emittedFromFresh
    CSaveEnv -> do
      saveLocalEnv
      return []
    CTrue -> return []
    CSubEffect r a b ->
      return [ESubEffect r a b]
    CCanBeMatchedBy r a b ->
      return [ECanBeMatchedBy r a b]
    CMatchesImplies r pair1 pair2 ->
      return [EMatchesImplies r pair1 pair2]


--makeWHelper :: EmittedConstr -> SolverM [WConstr]
makeWHelper (ESubEffect r left right ) =
  makeSubEffectConstrs r left right
makeWHelper (ECanBeMatchedBy r a exact) = do
  vinter <- liftIO $ mkVar
  varMatchesAnn <- makeSubEffectConstrs r a (VarAnnot vinter)
  return $ (WSubEffectOfLit r vinter exact) : varMatchesAnn
makeWHelper (EMatchesImplies r (a1, real) (a2, a3)) = do
  vinter1 <- liftIO $ mkVar
  vinter2 <- liftIO $ mkVar
  vinter3 <- liftIO $ mkVar
  varMatchesAnn1 <- makeSubEffectConstrs r a1 (VarAnnot vinter1)
  varMatchesAnn2 <- makeSubEffectConstrs r a2 (VarAnnot vinter2)
  varMatchesAnn3 <- makeSubEffectConstrs r a3 (VarAnnot vinter3)
  let combinedConstrs = varMatchesAnn1 ++ varMatchesAnn2 ++ varMatchesAnn3
  let implConstr = WSimpleImplies r vinter1 real $ WSubEffect r vinter2 vinter3
  return  $ implConstr : combinedConstrs


    --For our other constraints, we defer solving until after unification is done
makeSubEffectConstrs :: R.Region -> TypeAnnot -> TypeAnnot -> SolverM [WConstr]
makeSubEffectConstrs r aLeft aRight = case (aLeft, aRight) of
    (_, VarAnnot vRight) -> do
      mreprRight <- getRepr vRight
      case mreprRight of
        Just rep1 ->
          makeSubEffectConstrs r aLeft rep1

        Nothing -> do
          case aLeft of
            VarAnnot vLeft -> do
              mreprLeft <- getRepr vLeft
              case mreprLeft of
                Nothing -> do
                  return [WSubEffect r vLeft vRight]

                Just repLeft -> do
                  makeSubEffectConstrs  r repLeft (VarAnnot vRight)

            SinglePattern ctor subPats -> do
                let numArgs = length subPats
                let indices = [0 .. numArgs - 1]
                subVars <- forM subPats $ \_ -> liftIO mkVar
                let varPatTriples = zip3 subPats subVars indices
                --Constrain our new variables to the sub-annotations they're linked to
                --as well as adding a constraint for our overall variable to that var as a sub-pattern
                listsPerTriple <- forM varPatTriples  $ \(subPat, subVar, i) -> do
                  --Constrs: each new argument variable is a contains at least the given pattern
                  subConstrs <- makeSubEffectConstrs  r subPat (VarAnnot subVar)
                  --liftIO $ putStrLn $ "Single pat subs" ++ show (i, subVar, subConstrs)
                  return $ (WPatSubEffectOf r numArgs ctor i subVar vRight) : subConstrs
                --Ensure we have this ctor, even if there are no args
                let ctorConstr = WLitSubEffectOf r (RealAnnot $ Set.singleton(ctor, List.replicate numArgs realBottom)) vRight
                return $ ctorConstr : (concat listsPerTriple)


            LambdaAnn _ _ -> do
              --If there are only subset constraints stating that this variable is a lambda
              --We unify it now to be a lambda
              varg <- liftIO mkVar
              vret <- liftIO mkVar
              let newRepr = (LambdaAnn (VarAnnot varg) (VarAnnot vret))
              setRepr vRight newRepr
              makeSubEffectConstrs r newRepr aLeft

            TopAnnot ->
              return [WLitSubEffectOf r RealTop vRight]
            ReturnsTop -> --If subeffect of var, is not in function position, so is top
              return [WLitSubEffectOf r RealTop vRight]

    (VarAnnot vLeft, _) -> do
            mreprLeft <- getRepr vLeft
            case mreprLeft of
              Just repr -> makeSubEffectConstrs r repr aRight

              Nothing -> case aRight of

                SinglePattern ctor subPats -> do
                    let numArgs = length subPats
                    let indices = [0 .. numArgs - 1]
                    subVars <- forM subPats $ \_ -> liftIO mkVar
                    let varPatTriples = zip3 subPats subVars indices
                    --Constrain our new variables to the sub-annotations they're linked to
                    --as well as adding a constraint for our overall variable to that var as a sub-pattern
                    listsPerTriple <- forM varPatTriples  $ \(subPat, subVar, i) -> do
                      --Ensure that our new variable is a subeffect of the pattern
                      subConstrs <- makeSubEffectConstrs  r (VarAnnot subVar) subPat
                      --Specify that the i'th arg of our left side is a subEffect of our variable
                      return $ (WSubEffectOfPat r numArgs vLeft ctor i subVar) : subConstrs
                    --Ensure we have this ctor, even if there are no args
                    let ctorConstr = WSubEffectOfLit r vLeft (RealAnnot $ Set.singleton (ctor, List.replicate numArgs RealTop))
                    return $ ctorConstr : concat listsPerTriple


                LambdaAnn _ _  -> do
                  --If there are only subset constraints stating that this variable is a lambda
                  --We unify it now to be a lambda
                  varg <- liftIO mkVar
                  vret <- liftIO mkVar
                  let newRepr = (LambdaAnn (VarAnnot varg) (VarAnnot vret))
                  setRepr vLeft newRepr
                  makeSubEffectConstrs r newRepr aRight

                TopAnnot ->
                  return [WSubEffectOfLit r vLeft RealTop]

                ReturnsTop ->
                  return [WSubEffectOfLit r vLeft RealTop]


    (SinglePattern s1 subs1, SinglePattern s2 subs2) -> do
      case (s1 == s2) of
        False
          -> do
               emitWarnings [(r,
                  Warning.MissingCase
                    (RealAnnot $ Set.singleton (s1, [])) (RealAnnot $ Set.singleton (s2, [])) )] --TODO better error
               return []

        True -> do
          subLists <- forM (zip subs1 subs2) $ \(s1, s2) ->
            makeSubEffectConstrs r s1 s2
          return $ concat subLists

    {-
      do
      listPerCtor <- forM d2 $ \(ctor, subPats) ->
        case (Map.lookup ctor d1) of
          Nothing -> return [WWarning r ctor]
          Just leftSubPats -> do
            listPerArg <- forM (zip leftSubPats subPats) $ \(left, right) ->
              makeSubEffectConstrs  r left right
            return $ concat listPerArg
      return $ concat listPerCtor
      -}

    (LambdaAnn a1 a2, LambdaAnn b1 b2) -> do
      --Constrain that the argument variable matches at most our lambda
      --And the return matches at least our lambda
      --Basic covariance and contravariance stuff
      argList <- makeSubEffectConstrs r b1 a1
      retList <- makeSubEffectConstrs r a2 b2
      return $ argList ++ retList

    (TopAnnot, TopAnnot) -> return []

    (x,y) -> error $ "Mismatch in underlying type system\n" ++ show x ++ "\n" ++ show y



      --Make a new variable for each constructor of the pattern

freeVarsInAnnot a =
  case a of
    VarAnnot v -> do
      mrepr <- getRepr v
      case mrepr of
        Nothing -> return [v]
        Just rep -> ([v] ++) <$> freeVarsInAnnot rep --Can't quantify over if have repr
    SinglePattern _s subs ->
     concat <$> forM subs freeVarsInAnnot
    LambdaAnn a1 a2 ->
      (++) <$> freeVarsInAnnot a1 <*> freeVarsInAnnot a2
    TopAnnot ->
      return []
    ReturnsTop ->
      return []

freeVarsInConstr :: EmittedConstr -> SolverM [AnnVar]
freeVarsInConstr c = case c of
  ESubEffect _ a1 a2 -> (++) <$> freeVarsInAnnot a1 <*> freeVarsInAnnot a2
  ECanBeMatchedBy _ a1 _ -> freeVarsInAnnot a1
  EMatchesImplies _ (a1, _) (a2, a3) -> concat <$> forM [a1, a2, a3] (freeVarsInAnnot)


freeVarsInEnv :: Env -> SolverM [AnnVar]
freeVarsInEnv env =
  (fmap concat) $ forM (Map.elems env) $ \sch ->
    case sch of
      (StoredScheme quants constrList var) -> do
        freeInTy <- freeVarsInAnnot (VarAnnot var)
        freeInConstr <- concat <$> forM constrList freeVarsInConstr
        filterM (varNotInList quants) (freeInTy ++ freeInConstr)
      StoredMono var -> do
        freeInTy <- freeVarsInAnnot (VarAnnot var)
        filterM (varNotInList []) (freeInTy)


varNotInList :: [AnnVar] -> AnnVar -> SolverM' a Bool
varNotInList vl v = do
  boolList <- forM vl (areSame v)
  return $ not $ List.or boolList

notFreeInEnv env v = do
  freeInEnv <- freeVarsInEnv env
  varNotInList freeInEnv v


solveScheme :: Env -> AnnScheme -> SolverM ([EmittedConstr], Env)
solveScheme oldEnv (Scheme constr hdr) = do
  let oldHeader = Map.toList hdr
  --Solve the relationships between variables before we quantify
  schemeEmitted <- applyUnifications constr
  newSchemeHeaders <- forM oldHeader $ \(nm, (A.A _ ann)) -> do
    newVar <- liftIO mkVar
    allVars <- freeVarsInAnnot ann
    goodQuants <- filterM (notFreeInEnv oldEnv) allVars
    unifyAnnots (VarAnnot newVar) ann
    --liftIO $ putStrLn $ "Unified new scheme var " ++ (show newVar) ++ " with " ++ show ann
    --liftIO $ putStrLn $ "Quantified scheme " ++ (show scheme) ++ "\nnew constr " ++ show constr
    return (schemeEmitted, (nm, StoredScheme goodQuants schemeEmitted  newVar))
  --Now that we have a new header with variables, actually solve the constraint
  --On our scheme
  let (allSchemesEmitted, newHeader) = unzip newSchemeHeaders
  return (concat allSchemesEmitted, Map.fromList newHeader)
solveScheme _ (MonoScheme hdr) = do
  let oldHeader = Map.toList hdr
  newHeader <- forM oldHeader $ \(nm, A.A _ ann) -> do
    newVar <- liftIO mkVar
    unifyAnnots (VarAnnot newVar) ann
    return (nm, StoredMono newVar)
  --Now that we have a new header with variables, actually solve the constraint
  --On our scheme
  return $ ([], Map.fromList newHeader)

makeFreshCopy :: [AnnVar] -> [EmittedConstr] -> AnnVar -> SolverM ([EmittedConstr], AnnVar)
makeFreshCopy quants inConstrList inVar = do
  let --TODO check if free or not?
    isQuant v = isQuantHelper quants v
    isQuantHelper [] _ = return False
    isQuantHelper (vfree : rest) v = do
      b <- areSame vfree v
      case b of
        True -> return True
        False ->
          isQuantHelper rest v
    copyConHelper c = case c of
      ECanBeMatchedBy r a1 exact -> do
        (subAnn, subPairs) <- copyHelper a1
        return (ECanBeMatchedBy r subAnn exact, subPairs)
      ESubEffect r a1 a2 -> do
        (b1, pairs1) <- copyHelper a1
        (b2, pairs2) <- copyHelper a2
        return (ESubEffect r b1 b2, pairs1 ++ pairs2)
      EMatchesImplies r (a1, real) (a2, a3) -> do
        (sub1, pairs1) <- copyHelper a1
        (sub2, pairs2) <- copyHelper a2
        (sub3, pairs3) <- copyHelper a3
        return (EMatchesImplies r (sub1, real) (sub2, sub3), pairs1 ++ pairs2 ++ pairs3)
    --We only need to copy our subtyping constraints
    copyHelper :: TypeAnnot -> SolverM (TypeAnnot, [(AnnVar, AnnVar)])
    copyHelper a = case a of
      VarAnnot v -> do
        vIsFree <- isQuant v
        case vIsFree of
          True -> do
            vnew <- liftIO $ mkVar
            mOldRepr <- getRepr v
            repPairs <- case mOldRepr of
              Nothing -> do
                return []
              Just rep -> do
                (newRep, newPairs) <- copyHelper rep
                setRepr vnew newRep
                return newPairs
            return $ (VarAnnot vnew, [(v, vnew)] ++ repPairs)
          False ->
            return (VarAnnot v, [])
      SinglePattern s subPats -> do
        (newSubPats, newVarLists) <- unzip <$> forM subPats copyHelper
        return (SinglePattern s newSubPats, concat newVarLists)
      LambdaAnn a1 a2 -> do
        (b1, pairs1) <- copyHelper a1
        (b2, pairs2) <- copyHelper a2
        return (LambdaAnn b1 b2, pairs1 ++ pairs2)
      TopAnnot -> return (TopAnnot, [])
      ReturnsTop -> return (ReturnsTop, [])

    unifyPairs pairList =
      forM_ pairList $ \(old1, new1) -> forM_ pairList $ \(old2, new2) -> do
        sm <- areSame old1 old2
        case sm of
          True -> union new1 new2
          False -> return ()

  (newConstrs, pairList) <- unzip <$> forM inConstrList copyConHelper
  newVar <- liftIO $ mkVar
  (newAnn, varPairs) <- copyHelper (VarAnnot inVar)
  --Unify the var for our new annotation with the annotation itself
  unifyAnnots (VarAnnot newVar) newAnn
  unifyPairs $ varPairs ++ (concat pairList)
  instRepr <- getRepr newVar
  return (newConstrs, newVar)


unifyAnnots :: TypeAnnot -> TypeAnnot -> SolverM TypeAnnot
unifyAnnots r1 r2 =
  case (r1, r2) of
    (TopAnnot, TopAnnot) ->
      return TopAnnot

    --Unify two vars: combine their reprs
    (VarAnnot v1, VarAnnot v2) -> do
      mrepr1 <- getRepr v1
      mrepr2 <- getRepr v2
      union v1 v2
      case (mrepr1, mrepr2) of
        (Nothing, Nothing) -> do
          union v1 v2
          return $ VarAnnot v1
        (Just rep, Nothing) -> do
          setRepr v2 rep
          return $ rep
        (Nothing, Just rep) -> do
          setRepr v2 rep
          return $ rep
        (Just rep1, Just rep2) -> do
          newRepr <- unifyAnnots rep1 rep2
          setRepr v1 newRepr
          return newRepr

      --Unify a var with something: unify the var's repr with that thing
    (VarAnnot v, repr2) -> do
          mrepr1 <- getRepr v
          case mrepr1 of
            Nothing -> do
              setRepr v repr2
              return repr2
            Just repr1 -> do
              newRepr <- unifyAnnots repr1 repr2
              setRepr v newRepr
              return newRepr
    --Same as above but flipped
    (repr2, VarAnnot v) -> do
          mrepr1 <- getRepr v
          case mrepr1 of
            Nothing -> do
              setRepr v repr2
              return repr2
            Just repr1 -> do
              newRepr <- unifyAnnots repr1 repr2
              setRepr v newRepr
              return newRepr

    (LambdaAnn a1 a2, LambdaAnn b1 b2) ->
      LambdaAnn <$> unifyAnnots a1 b1 <*> unifyAnnots a2 b2

    --Special cases: we can unify lambda with Top, giving a TopLambda
    --This helps us deal with Native values, or any other places our analysis fails
    (LambdaAnn a1 a2, TopAnnot) -> do
      unifyAnnots a1 TopAnnot
      unifyAnnots a2 TopAnnot
      return $ LambdaAnn TopAnnot TopAnnot
    (TopAnnot, LambdaAnn a1 a2) -> do
        unifyAnnots a1 TopAnnot
        unifyAnnots a2 TopAnnot
        return $ LambdaAnn TopAnnot TopAnnot

    (LambdaAnn a1 a2, ReturnsTop) -> do
      unifyAnnots a2 ReturnsTop
      return $ LambdaAnn a1 ReturnsTop
    (ReturnsTop, LambdaAnn a1 a2) -> do
        unifyAnnots a2 ReturnsTop
        return $ LambdaAnn a1 ReturnsTop
    (ReturnsTop, TopAnnot) ->
      return TopAnnot
    (TopAnnot, ReturnsTop) ->
      return TopAnnot

    _ -> error $ "Invalid unify " ++ show r1 ++ " " ++ show r2


-------------------------
-- Worklist algorithm for solving subset constraints
-------------------------

--Constraints we can actually deal with in our workList algorithm
data WConstr' v =
  WSubEffect R.Region v v
  | WSubEffectOfPat R.Region Int v String Int v --Specific sub-pattern constraints
  | WPatSubEffectOf R.Region Int String Int v v
  | WSubEffectOfLit R.Region v RealAnnot
  | WLitSubEffectOf R.Region RealAnnot v
  | WSimpleImplies R.Region v RealAnnot WConstr
  deriving (Show)

type WConstr = WConstr' AnnVar


unionAnn :: RealAnnot -> RealAnnot -> RealAnnot
unionAnn RealTop _ = RealTop
unionAnn _ RealTop = RealTop
unionAnn (RealAnnot dict1) (RealAnnot dict2) =
  RealAnnot $  Set.union dict1 dict2


intersectPairs :: (String, [RealAnnot]) -> (String, [RealAnnot]) -> Maybe (String, [RealAnnot])
intersectPairs (s1, args1) (s2, args2) =
  if s1 == s2 then
    let
      argIntersections = zipWith intersectAnn args1 args2
    in
      Just (s1, argIntersections)
  else
      Nothing


intersectAnn :: RealAnnot -> RealAnnot -> RealAnnot
intersectAnn RealTop x = x
intersectAnn x RealTop = x
intersectAnn (RealAnnot dict1) (RealAnnot dict2) =
  --Take the pairwise intersection of all elements then union them
  --TODO do this faster?
  let
    l1 = Set.toList dict1
    l2 = Set.toList dict2
  in
    RealAnnot $ Set.fromList $ Maybe.catMaybes [intersectPairs p1 p2 | p1 <- l1, p2 <- l2 ]

--Return a waring if the single pattern (S, p1 ... pn) is not matched by (S', p1' ... pn')
elemMismatches :: R.Region -> (String, [RealAnnot]) -> (String, [RealAnnot]) -> [(R.Region, Warning.Warning)]
elemMismatches region pr1@(s1,args1) pr2@(s2, args2) =
  if (s1 == s2) then
    concat $ zipWith (mismatches region) args1 args2
  else
    [(region, Warning.MissingCase (RealAnnot $ Set.singleton pr1) (RealAnnot $ Set.singleton pr2))]

--Return a warning for every element in a1 that is not matched by any element of a2
mismatches :: R.Region -> RealAnnot -> RealAnnot -> [(R.Region, Warning.Warning)]
mismatches _ _ RealTop = []
mismatches r RealTop x = [(r, Warning.MissingCase RealTop x)]
mismatches region (RealAnnot subs1) (RealAnnot subs2) =
  let
    forSet s f = Set.map f s
    for = flip List.map
    ctors1 = Set.map fst subs1
    ctors2 = Set.map fst subs2
    ctorFails = Set.toList $ Set.difference ctors1 ctors2
    ctorsCanMatch = RealAnnot $ Set.map (\(ctor, _) -> (ctor, [])) subs2
    ctorWarnings = for ctorFails $ \ctor -> (region, Warning.MissingCase (RealAnnot $ Set.singleton (ctor, [])) ctorsCanMatch)
    failsForAllSubs =
      for (Set.toList subs1) $ \sub1 ->
        let
          failsForSub1 = for (Set.toList subs2) $ \sub2 ->
            elemMismatches region sub1 sub2
        in
          --Check if there were any elements in subs2 that matched subs1
          if (List.any List.null failsForSub1) then
            []
          else
            [(region, Warning.MissingCase (RealAnnot $ Set.singleton sub1) (RealAnnot subs2))]
            --concat failsForSub1
  in --trace ("Mismatches for " ++ show (RealAnnot subs1, RealAnnot subs2) ++ ":\n  " ++ show (length ctorWarnings, length failsForAllSubs) ) $
    ctorWarnings ++ concat failsForAllSubs
{-
  concatMap (\(s, subPatsToMatch) ->
      case Map.lookup s d1 of
        Nothing -> [(r, Warning.MissingCase s)] --TODO better error messages
        --TODO assert same size lists?
        Just subPats -> concat $ zipWith (canMatchAll r) subPats subPatsToMatch
      )  (Map.toList d2)
-}


getAnnData :: AnnVar -> SolverM' a (AnnotData)
getAnnData v@(AnnVar (pt, _)) = do
   ret <- liftIO $ UF.descriptor pt
   --liftIO $ putStrLn $ "Data for " ++ show v ++ " (LB, UB) " ++ show (_lb ret, _ub ret)
   return ret

canMatchAll :: RealAnnot -> RealAnnot -> Bool
canMatchAll r1 r2 = case mismatches (error "matchall region") r2 r1 of
  [] -> True
  _ -> False


--Return true if this union makes a change, false otherwise
unionUB :: R.Region -> AnnVar -> RealAnnot -> WorklistM Bool
unionUB r (AnnVar (pt, _)) ann = do
  annData <- liftIO $ UF.descriptor pt
  let newUB = _ub annData `unionAnn` ann
  liftIO $ UF.setDescriptor pt $ annData {_ub = newUB}
  --Check if we changed the set at all
  --TODO faster shortcut method
  return $ not $ (_ub annData) `canMatchAll` newUB


  --TODO emit warning

intersectLB :: R.Region -> AnnVar -> RealAnnot -> WorklistM Bool
intersectLB r (AnnVar (pt, vn)) ann =  do
  --liftIO $ putStrLn $ "Setting LB of " ++ show vn ++ " to" ++ show ann
  annData <- liftIO $ UF.descriptor pt
  let newLB = _lb annData `intersectAnn` ann
  liftIO $ UF.setDescriptor pt $ annData {_lb = newLB}
  return $ not $ newLB `canMatchAll` (_lb annData)

data VarPosition = Sub | Super
  deriving (Show)

--All constraints where some type is a supertype of the given var
constraintEdges :: WConstr -> [(AnnVar, VarPosition)]
constraintEdges c = case c of
  WSubEffect _ v1 v2 -> [(v1, Sub), (v2, Super)]
  WSubEffectOfPat _ _ v1 _ _ v2 -> [(v1, Sub), (v2, Super)]
  WPatSubEffectOf _ _ _ _ v1 v2 -> [(v1, Super), (v2, Sub)]
  WLitSubEffectOf _ _ v2 -> [(v2, Super)]
  WSubEffectOfLit _ v1 _ -> [(v1, Sub)]
  WSimpleImplies _ v1 _ subConstr -> [(v1, Sub)] ++ constraintEdges subConstr

allVars  c = case c of
  WSubEffect _ v1 v2 -> [v1, v2]
  WSubEffectOfPat _ _ v1 _ _ v2 -> [v1, v2]
  WPatSubEffectOf _ _ _ _ v1 v2 -> [v1, v2]
  WLitSubEffectOf _ _ v2 -> [v2]
  WSubEffectOfLit _ v1 _ -> [v1]
  WSimpleImplies _ v1 _ subConstr -> [v1] ++ allVars subConstr


addConstraintEdge :: Int -> (AnnVar, VarPosition) -> WorklistM ()
addConstraintEdge i (AnnVar (pt, _), Sub) = liftIO $ do
  desc <- UF.descriptor pt
  UF.setDescriptor pt $ desc {_superOf = i : (_superOf desc)}
addConstraintEdge i (AnnVar (pt, _), Super) = liftIO $ do
  desc <- UF.descriptor pt
  UF.setDescriptor pt $ desc {_subOf = i : (_subOf desc)}

solveSubsetConstraints :: AnnotConstr -> WorklistM ()
solveSubsetConstraints inCon = do
  emittedConstrs <- applyUnifications inCon
  wConstraints <-  concat <$> forM emittedConstrs makeWHelper

  let constrPairs = zip [1..] wConstraints
  forM constrPairs $ \(i, c) -> forM (constraintEdges c) $ \v ->
    addConstraintEdge i v
  --TODO avoid list ops here?
  workList (Map.fromList constrPairs) wConstraints
  --One last check: once we've solved our constraints, check the constraint
  --That all possible values (upperBound) are covered by least possible matches
  --(lower bound)
  --TODO notation backwards
  finalLowerBoundsCheck wConstraints
  --liftIO $ putStrLn $ "WConstraints: " ++ show wConstraints

--TODO lower bounds for pat and lit cases?

finalLowerBoundsCheck :: [WConstr] -> WorklistM ()
finalLowerBoundsCheck constrList = forM_ constrList $ \c -> do
  --liftIO $ putStrLn $ "\nFinal bounds check on " ++ show c
  case c of
      WSubEffect r v1 v2 -> do
        data1 <- getAnnData v1
        data2 <- getAnnData v2
        emitWarnings $ mismatches r (_ub data1) (_lb data1)
        emitWarnings $ mismatches r (_ub data2) (_lb data2)
      WSubEffectOfPat r _ v1 _ _ v2 -> do
        data1 <- getAnnData v1
        data2 <- getAnnData v2
        emitWarnings $ mismatches r (_ub data1) (_lb data1)
        emitWarnings $ mismatches r (_ub data2) (_lb data2)
      WPatSubEffectOf r _ _ _ v1 v2 -> do
        data1 <- getAnnData v1
        data2 <- getAnnData v2
        emitWarnings $ mismatches r (_ub data1) (_lb data1)
        emitWarnings $ mismatches r (_ub data2) (_lb data2)
      WLitSubEffectOf r _ v2 -> do
        data2 <- getAnnData v2
        emitWarnings $ mismatches r (_ub data2) (_lb data2)
      WSubEffectOfLit r v1 _ -> do
        data1 <- getAnnData v1
        emitWarnings $ mismatches r (_ub data1) (_lb data1)
      WSimpleImplies r v real subCon -> do
        data1 <- getAnnData v
        emitWarnings $ mismatches r (_ub data1) (_lb data1)
        --liftIO $ putStrLn "Checking imp RHS"
        finalLowerBoundsCheck [subCon]
        --liftIO $ putStrLn "Done imp RHS"



workList :: (Map.Map Int WConstr) -> [WConstr] -> WorklistM ()
workList _ [] = return () --When we're finished
workList allConstrs (c:rest) = case c of
  WSubEffect r v1 v2 -> do
    data1 <- getAnnData v1
    data2 <- getAnnData v2
    changed1 <- unionUB r v2 (_ub data1)
    changed2 <- intersectLB r v1 (_lb data2)

    let needsUpdate1 =
          case changed1 of
            False -> []
            True -> List.map (allConstrs Map.! ) $ _superOf data2

    let needsUpdate2 =
          case changed2 of
            False -> []
            True -> List.map (allConstrs Map.! ) $ _subOf data1
    workList allConstrs (needsUpdate1 ++ needsUpdate2 ++ rest)

  WSubEffectOfLit r v1 realAnn -> do
    changed <- intersectLB r v1 realAnn
    ourData <- getAnnData v1
    let needsUpdate =
          case changed of
            False -> []
            True -> List.map (allConstrs Map.! ) $ _superOf ourData
    workList allConstrs (needsUpdate ++ rest)

  WLitSubEffectOf r realAnn v1 -> do
    changed <- unionUB r v1 realAnn
    ourData <- getAnnData v1
    let needsUpdate =
          case changed of
            False -> []
            True -> List.map (allConstrs Map.! ) $ _subOf ourData
    workList allConstrs (needsUpdate ++ rest)

  WPatSubEffectOf r numArgs ctor argNum argVar wholeVal -> do
    argData <- getAnnData argVar
    wholeData <- getAnnData wholeVal
    let nBottoms =
          (List.replicate argNum realBottom) ++ [_ub argData] ++ (List.replicate (numArgs - argNum - 1) realBottom)
    changedWhole <- unionUB r wholeVal $ RealAnnot $ Set.singleton (ctor, nBottoms)
    {-
    let lbPartOfWhole =
          case _lb wholeData of
            RealTop -> RealTop
            RealAnnot pats ->
              RealAnnot $ Set.filter ((== ctor) . fst) pats

    changedPart <- intersectLB r argVar lbPartOfWhole
    -} --TODO need to constrain part?

    {-let needsUpdate1 =
          case changedPart of
            False -> []
            True -> List.map (allConstrs Map.! ) $ _superOf argData-}

    let needsUpdate2 =
          case changedWhole of
            False -> []
            True -> List.map (allConstrs Map.! ) $ _subOf wholeData
    workList allConstrs (needsUpdate2 ++ {-needsUpdate1 ++-} rest)

  WSubEffectOfPat r numArgs wholeVal ctor argNum argVar -> do
    argData <- getAnnData argVar
    wholeData <- getAnnData wholeVal
    let nBottoms =
          (List.replicate argNum RealTop) ++ [_lb argData] ++ (List.replicate (numArgs - argNum - 1) RealTop)
    changedWhole <- intersectLB r wholeVal $ RealAnnot $ Set.singleton (ctor, nBottoms)
    {-let wholeMatchingCtor =
          case _ub wholeData of
            RealTop -> RealTop
            RealAnnot pats ->
              RealAnnot $ Set.filter ((== ctor) . fst) pats

    changedPart <- unionUB r argVar wholeMatchingCtor-}

    {-let needsUpdate1 =
          case changedPart of
            False -> []
            True -> List.map (allConstrs Map.! ) $ _subOf argData-}

    let needsUpdate2 =
          case changedWhole of
            False -> []
            True -> List.map (allConstrs Map.! ) $ _superOf wholeData
    workList allConstrs ({-needsUpdate1 ++-} needsUpdate2 ++ rest)

  WSimpleImplies _ v real subConstr -> do
    ourUB <- _ub <$> getAnnData v
    --Check if our implication condition is true, and if it is solve the sub-constraint
    let condsToAdd =
          case ourUB `canMatchAll` real of
            True -> [subConstr]
            False -> []
    workList allConstrs (condsToAdd ++ rest)
