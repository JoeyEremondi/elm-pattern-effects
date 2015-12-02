module Type.Effect.Solve where

import Type.Effect
import Control.Monad.Writer
import qualified  Control.Monad.State as State
import Control.Monad.Trans
import Control.Monad (forM, forM_, filterM)

import qualified Data.List as List

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
     , Map.Map String CanonicalAnnot)
solve c = do
  let emittedComp = applyUnifications c
      stateComp = runWriterT $ solveSubsetConstraints emittedComp
      ioComp = State.runStateT stateComp $ SolverState Map.empty Map.empty
  (((), warnings), finalState) <- ioComp
  finalEnv <- forM (Map.toList $ sSavedEnv finalState) $ \(s, StoredScheme frees constr annVar) -> do
    ourAnnot <- toCanonicalAnnot (VarAnnot annVar)
    return (s, ourAnnot)
  return (warnings, Map.fromList finalEnv)

toCanonicalAnnot :: TypeAnnot -> IO CanonicalAnnot
toCanonicalAnnot = toCanonicalHelper toCanonicalAnnot canonLowerBound _ub

canonLowerBound :: TypeAnnot -> IO CanonicalAnnot
canonLowerBound = toCanonicalHelper canonLowerBound toCanonicalAnnot _lb

toCanonicalHelper co contra getCo a = case a of
  VarAnnot (AnnVar (pt, _)) -> do
    ourData <- UF.descriptor pt
    case (_annRepr ourData) of
      Nothing ->
        --TODO better way? use schemes?
        case (_lb ourData, _ub ourData) of
          --Completely unconstrained sets
          (RealTop, RealAnnot d) | List.length d == 0 ->
            return $ CanonVar $ _uniqueId ourData
          _ ->
            --TODO UB or LB? Based on position?
            return $ CanonLit  $ getCo ourData
      Just repr ->
        co repr
  SinglePattern s subs -> do
    canonSubs <- forM subs co
    return $ CanonPatDict [(s, canonSubs)]
  LambdaAnn a b ->
    CanonLambda <$> contra a <*> co b
  TopAnnot ->
    return CanonTop

data StoredScheme = StoredScheme [AnnVar] AnnotConstr AnnVar | StoredMono AnnVar

--TODO shouldn't this hold schemes, not vars?
type Env = Map.Map String StoredScheme

data SolverState =
  SolverState
  { sEnv :: Env
  , sSavedEnv :: Env
  }

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

applyUnifications :: AnnotConstr -> SolverM [AnnotConstr]
applyUnifications con =
  case con of
    CEqual _ r1 r2 -> trace "con Equal" $ do
      _ <- unifyAnnots r1 r2
      return []
    CAnd constrs -> trace "con AND" $
      concat <$> forM constrs applyUnifications
    CLet schemes letConstr -> trace "con Let" $ do
      oldEnv <- getEnv
      --TODO do something with vars in the scheme?
      headers <- Map.unions <$> forM schemes (solveScheme oldEnv)
      modifyEnv $ \env -> Map.union headers env
      letEmitted <- applyUnifications letConstr
      --TODO occurs check?
      modifyEnv $ \_ -> oldEnv
      return letEmitted
    CInstance r var annot -> trace "con Inst" $ do
      env <- getEnv
      case Map.lookup var env of
          Nothing -> error $ "Could not find name " ++ show var ++ " in Effect.Solve\nenv:\n" ++ show (Map.keys env)
          Just (StoredMono storedVar) ->
            applyUnifications $ CEqual r (VarAnnot storedVar) annot
          Just (StoredScheme quants constr annVar) -> do
            (freshConstr, newVar) <- makeFreshCopy quants constr annVar
            --Unify the type of the variable use with our newly instantiated type
            unifyAnnots annot (VarAnnot newVar)
            --Apply our instantiated constraints to that type
            instEmitted <- applyUnifications freshConstr
            liftIO $ putStrLn $ "Made instance of " ++ show var ++ " with constr " ++ show freshConstr ++ " and var " ++ show newVar
            liftIO $ putStrLn $ "Unified with " ++ show annot
            return instEmitted
    CSaveEnv -> do
      saveLocalEnv
      return []
    CTrue -> return []
    c -> return [c]

makeWHelper (CSubEffect r left right ) =
  makeSubEffectConstrs r left right
makeWHelper (CCanBeMatchedBy r a exact) =
  makeExactMatchConstrs r a exact


makeExactMatchConstrs :: R.Region -> TypeAnnot -> RealAnnot -> SolverM' a [WConstr]
makeExactMatchConstrs r a exact = do
  vinter <- liftIO $ mkVar
  varMatchesAnn <- makeSubEffectConstrs r a (VarAnnot vinter)
  return $ (WSubEffectOfLit r vinter exact) : varMatchesAnn


    --For our other constraints, we defer solving until after unification is done
makeSubEffectConstrs :: R.Region -> TypeAnnot -> TypeAnnot -> SolverM' a [WConstr]
makeSubEffectConstrs r aLeft aRight = case (aLeft, aRight) of
    (_, VarAnnot vRight) -> do
      mreprRight <- getRepr vRight
      case mreprRight of
        Just rep1 ->
          makeSubEffectConstrs r aLeft rep1

        Nothing -> do
          case aLeft of
            VarAnnot vLeft -> do
              mrepr2 <- getRepr vLeft
              case mrepr2 of
                Nothing ->
                  return [WSubEffect r vLeft vRight]

                Just rep2 ->
                  makeSubEffectConstrs  r rep2 (VarAnnot vRight)

            SinglePattern ctor subPats -> trace "Single pat suppsed case" $ do
                let numArgs = length subPats
                let indices = [0 .. numArgs - 1]
                subVars <- forM subPats $ \_ -> liftIO mkVar
                let varPatTriples = zip3 subPats subVars indices
                --Constrain our new variables to the sub-annotations they're linked to
                --as well as adding a constraint for our overall variable to that var as a sub-pattern
                listsPerTriple <- forM varPatTriples  $ \(subPat, subVar, i) -> do
                  subConstrs <- makeSubEffectConstrs  r (VarAnnot subVar) subPat
                  return $ (WPatSubEffectOf r numArgs ctor i subVar vRight) : subConstrs
                --Ensure we have this ctor, even if there are no args
                let ctorConstr = WLitSubEffectOf r (RealAnnot [(ctor, List.replicate numArgs realBottom)]) vRight
                return $ ctorConstr : (concat listsPerTriple)


            LambdaAnn arg ret -> do
              --If there are only subset constraints stating that this variable is a lambda
              --We unify it now to be a lambda
              varg <- liftIO mkVar
              vret <- liftIO mkVar
              let newRepr = (LambdaAnn (VarAnnot varg) (VarAnnot vret))
              setRepr vRight newRepr
              makeSubEffectConstrs r newRepr aLeft

            TopAnnot ->
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
                      subConstrs <- makeSubEffectConstrs  r (VarAnnot subVar) subPat
                      return $ (WSubEffectOfPat r numArgs vLeft ctor i subVar) : subConstrs
                    --Ensure we have this ctor, even if there are no args
                    let ctorConstr = WSubEffectOfLit r vLeft (RealAnnot [(ctor, List.replicate numArgs RealTop)])
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


    (SinglePattern s1 subs1, SinglePattern s2 subs2) -> do
      case (s1 == s2) of
        False
          -> return [WWarning r (s1 ++ " " ++ s2)] --TODO better error
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
    SinglePattern s subs ->
     concat <$> forM subs freeVarsInAnnot
    LambdaAnn a1 a2 ->
      (++) <$> freeVarsInAnnot a1 <*> freeVarsInAnnot a2
    TopAnnot ->
      return []

freeVarsInConstr :: AnnotConstr -> SolverM [AnnVar]
freeVarsInConstr c = case c of
  CAnd constrs -> concat <$> forM constrs freeVarsInConstr
  CTrue -> return []
  CEqual _ a1 a2 -> (++) <$> freeVarsInAnnot a1 <*> freeVarsInAnnot a2
  CSaveEnv -> return []
  CSubEffect _ a1 a2 -> (++) <$> freeVarsInAnnot a1 <*> freeVarsInAnnot a2
  CCanBeMatchedBy _ a1 _ -> freeVarsInAnnot a1
  CInstance _ _ a1 -> freeVarsInAnnot a1
  CLet schemes constr -> do
    freeInCon <- freeVarsInConstr constr
    freeInSchemes <- forM schemes $ \sch ->
      case sch of
        (Scheme scon hdr) -> do
          let headerAnnots = List.map (\(A.A _ a) -> a) $ Map.elems hdr
          headerVars <- concat <$> forM headerAnnots freeVarsInAnnot
          (headerVars ++) <$> freeVarsInConstr scon
        (MonoScheme hdr) -> do
          let headerAnnots = List.map (\(A.A _ a) -> a) $ Map.elems hdr
          concat <$> forM headerAnnots freeVarsInAnnot

    return $ freeInCon ++ (concat freeInSchemes)

freeVarsInEnv :: Env -> SolverM [AnnVar]
freeVarsInEnv env =
  (fmap concat) $ forM (Map.elems env) $ \sch ->
    case sch of
      (StoredScheme quants constr var) -> do
        freeInTy <- freeVarsInAnnot (VarAnnot var)
        freeInConstr <- freeVarsInConstr constr
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


solveScheme :: Env -> AnnScheme -> SolverM Env
solveScheme oldEnv scheme@(Scheme constr hdr) = do
  let oldHeader = Map.toList hdr
  --Solve the relationships between variables before we quantify
  applyUnifications constr
  newHeader <- forM oldHeader $ \(nm, (A.A _ ann)) -> do
    newVar <- liftIO mkVar
    allVars <- freeVarsInAnnot ann
    goodQuants <- filterM (notFreeInEnv oldEnv) allVars
    unifyAnnots (VarAnnot newVar) ann
    --liftIO $ putStrLn $ "Unified new scheme var " ++ (show newVar) ++ " with " ++ show ann
    --liftIO $ putStrLn $ "Quantified scheme " ++ (show scheme) ++ "\nnew constr " ++ show constr
    return (nm, StoredScheme goodQuants constr  newVar)
  --Now that we have a new header with variables, actually solve the constraint
  --On our scheme
  return $ Map.fromList newHeader
solveScheme oldEnv scheme@(MonoScheme hdr) = do
  let oldHeader = Map.toList hdr
  newHeader <- forM oldHeader $ \(nm, A.A _ ann) -> do
    newVar <- liftIO mkVar
    unifyAnnots (VarAnnot newVar) ann
    return (nm, StoredMono newVar)
  --Now that we have a new header with variables, actually solve the constraint
  --On our scheme
  return $ Map.fromList newHeader

makeFreshCopy :: [AnnVar] -> AnnotConstr -> AnnVar -> SolverM (AnnotConstr, AnnVar)
makeFreshCopy quants inConstr inVar = do
  let --TODO check if free or not?
    isQuant v = isQuantHelper quants v
    isQuantHelper [] _ = return False
    isQuantHelper (vfree : rest) v = do
      b <- areSame vfree v
      case b of
        True -> return True
        False ->
          isQuantHelper rest v
    --We only need to copy our subtyping constraints
    copyConHelper :: AnnotConstr -> SolverM (AnnotConstr, [(AnnVar, AnnVar)])
    copyConHelper c = case c of
       CAnd constrs -> do
         (subAnns, subPairs) <- unzip <$> forM constrs copyConHelper
         return (CAnd subAnns, concat subPairs)
       CSaveEnv -> return (CSaveEnv, [])
       CInstance r nm ann -> do
         (newVarInst, newVarPairs) <- copyHelper ann
         return (CInstance r nm newVarInst, newVarPairs)

       CSubEffect r a1 a2 -> do
         (b1, pairs1) <- copyHelper a1
         (b2, pairs2) <- copyHelper a2
         return (CSubEffect r b1 b2, pairs1 ++ pairs2)
       CCanBeMatchedBy r a1 exact -> do
         (subAnn, subPairs) <- copyHelper a1
         return (CCanBeMatchedBy r subAnn exact, subPairs)
       CLet schemes constr -> do
         (newSchemes, newPairs) <- unzip <$> forM schemes copySchemeHelper
         (newConstr, cPairs) <- copyConHelper constr
         return (CLet newSchemes newConstr, (concat  newPairs) ++ cPairs)
       --We don't need our unification constraints, we can solve those when we generalize
       _ ->
        return (CTrue, [])

    copySchemeHelper (Scheme constr hdr) = do
      --TODO need to do quantifiers?
      (newConstr, conPairs) <- copyConHelper constr
      let (hdrStrings, hdrAnns) = unzip $ Map.toList hdr
      (newHeaderAnns, hdrPairs) <- unzip <$> forM hdrAnns (\(A.A r a) -> do
         (newAnn, pairList) <- copyHelper a
         return (A.A r newAnn, pairList))
      return ( Scheme  newConstr (Map.fromList $ zip hdrStrings newHeaderAnns)
             , conPairs ++ concat hdrPairs)

    copySchemeHelper (MonoScheme hdr) = do
        --TODO need to do quantifiers?
        let (hdrStrings, hdrAnns) = unzip $ Map.toList hdr
        (newHeaderAnns, hdrPairs) <- unzip <$> forM hdrAnns (\(A.A r a) -> do
           (newAnn, pairList) <- copyHelper a
           return (A.A r newAnn, pairList))
        return ( MonoScheme (Map.fromList $ zip hdrStrings newHeaderAnns)
               , concat hdrPairs)

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
                liftIO $ putStrLn "Input var had no repr"
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

    unifyPairs pairList =
      forM_ pairList $ \(old1, new1) -> forM_ pairList $ \(old2, new2) -> do
        sm <- areSame old1 old2
        case sm of
          True -> union new1 new2
          False -> return ()

  (newCopy, pairList) <- copyConHelper inConstr
  newVar <- liftIO $ mkVar
  (newAnn, varPairs) <- copyHelper (VarAnnot inVar)
  liftIO $ putStrLn $ "Final copied ann " ++ show newAnn
  --Unify the var for our new annotation with the annotation itself
  unifyAnnots (VarAnnot newVar) newAnn
  unifyPairs $ varPairs ++ pairList
  return (newCopy, newVar)


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
    _ -> error $ "Invalid unify " ++ show r1 ++ " " ++ show r2


-------------------------
-- Worklist algorithm for solving subset constraints
-------------------------

--Constraints we can actually deal with in our workList algorithm
data WConstr =
  WSubEffect R.Region AnnVar AnnVar
  | WSubEffectOfPat R.Region Int AnnVar String Int AnnVar --Specific sub-pattern constraints
  | WPatSubEffectOf R.Region Int String Int AnnVar AnnVar
  | WSubEffectOfLit R.Region AnnVar RealAnnot
  | WLitSubEffectOf R.Region RealAnnot AnnVar
  | WWarning R.Region String --Directly throw a warning
  deriving (Show)


unionAnn :: RealAnnot -> RealAnnot -> RealAnnot
unionAnn RealTop _ = RealTop
unionAnn _ RealTop = RealTop
unionAnn (RealAnnot dict1) (RealAnnot dict2) =
  RealAnnot $  dict1 ++ dict2


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
  RealAnnot $ Maybe.catMaybes [intersectPairs p1 p2 | p1 <- dict1, p2 <- dict2 ]


elemMismatches :: R.Region -> (String, [RealAnnot]) -> (String, [RealAnnot]) -> [(R.Region, Warning.Warning)]
elemMismatches region (s1,args1) (s2, args2) =
  if (s1 == s2) then
    concat $ zipWith (mismatches region) args1 args2
  else
    [(region, Warning.MissingCase s1)]

--Return a warning for every element in a1 that is not matched by any element of a2
mismatches :: R.Region -> RealAnnot -> RealAnnot -> [(R.Region, Warning.Warning)]
mismatches _ _ RealTop = trace "MM top" $ []
mismatches r RealTop _ = trace "MM topfirst" $ [(r, Warning.MissingCase "_")]
mismatches region (RealAnnot subs1) (RealAnnot subs2) = trace ("Mismatches for " ++ show (subs1, subs2)) $
  let
    for = flip List.map
    failsForAllSubs =
      for subs1 $ \sub1 ->
        let
          failsForSub1 = for subs2 $ \sub2 ->
            elemMismatches region sub1 sub2
        in
          if (List.any List.null failsForSub1) then
            []
          else
            concat failsForSub1
  in
    trace ("Found mismatches " ++ show (length $ concat failsForAllSubs)) $ concat failsForAllSubs
{-
  concatMap (\(s, subPatsToMatch) ->
      case Map.lookup s d1 of
        Nothing -> [(r, Warning.MissingCase s)] --TODO better error messages
        --TODO assert same size lists?
        Just subPats -> concat $ zipWith (canMatchAll r) subPats subPatsToMatch
      )  (Map.toList d2)
-}


getAnnData :: AnnVar -> SolverM' a (AnnotData)
getAnnData (AnnVar (pt, _)) =  liftIO $ UF.descriptor pt


--Return true if this union makes a change, false otherwise
unionUB :: R.Region -> AnnVar -> RealAnnot -> WorklistM Bool
unionUB r (AnnVar (pt, _)) ann = trace "unionUB" $ do
  annData <- liftIO $ UF.descriptor pt
  let newUB = _ub annData `unionAnn` ann
  trace ("Old, new UB " ++ show (_ub annData, newUB)) $ liftIO $ UF.setDescriptor pt $ annData {_ub = newUB}
  --Check if we changed the set at all
  --TODO faster shortcut method
  case (mismatches r (_ub annData) newUB) of
    [] -> return False
    _ -> do
      tell $ mismatches r newUB (_lb annData)
      return True

  --TODO emit warning

intersectLB :: R.Region -> AnnVar -> RealAnnot -> WorklistM Bool
intersectLB r (AnnVar (pt, _)) ann = trace "interLB" $ do
  annData <- liftIO $ UF.descriptor pt
  let newLB = _lb annData `intersectAnn` ann
  trace ("Old, new LB " ++ show (_lb annData, newLB)) $ liftIO $ UF.setDescriptor pt $ annData {_lb = newLB}
  case (mismatches r newLB (_lb annData)) of
      [] -> return False
      _ -> do
        tell $ mismatches r (_ub annData) newLB
        return True


data VarPosition = Sub | Super
  deriving (Show)

--All constraints where some type is a supertype of the given var
constraintEdges :: WConstr -> [(AnnVar, VarPosition)]
constraintEdges c = case c of
  WSubEffect _ v1 v2 -> [(v1, Sub), (v2, Super)]
  WSubEffectOfPat _ _ v1 _ _ v2 -> [(v1, Sub), (v2, Super)]
  WPatSubEffectOf _ _ _ _ v1 v2 -> [(v1, Sub), (v2, Super)]
  WLitSubEffectOf _ _ v2 -> [(v2, Super)]
  WSubEffectOfLit _ v1 _ -> [(v1, Sub)]
  WWarning _ _ -> []

allVars  c = case c of
  WSubEffect _ v1 v2 -> [v1, v2]
  WSubEffectOfPat _ _ v1 _ _ v2 -> [v1, v2]
  WPatSubEffectOf _ _ _ _ v1 v2 -> [v1, v2]
  WLitSubEffectOf _ _ v2 -> [v2]
  WSubEffectOfLit _ v1 _ -> [v1]
  WWarning _ _ -> []


addConstraintEdge :: Int -> (AnnVar, VarPosition) -> WorklistM ()
addConstraintEdge i (AnnVar (pt, _), Sub) = liftIO $ do
  desc <- UF.descriptor pt
  UF.setDescriptor pt $ desc {_superOf = i : (_superOf desc)}
addConstraintEdge i (AnnVar (pt, _), Super) = liftIO $ do
  desc <- UF.descriptor pt
  UF.setDescriptor pt $ desc {_subOf = i : (_subOf desc)}

solveSubsetConstraints :: SolverM [AnnotConstr] -> WorklistM ()
solveSubsetConstraints emittedComp = do
  emittedConstrs <- emittedComp
  wConstraints <- trace ("Emitted " ++ show emittedConstrs) $ concat <$> forM emittedConstrs makeWHelper
  let constrPairs = zip [1..] wConstraints
  trace ("Constraint pairs " ++ show constrPairs) $ forM constrPairs $ \(i, c) -> forM (constraintEdges c) $ \v -> trace ("Adding cedges " ++ show (i,c,v)) addConstraintEdge i v
  --TODO avoid list ops here?
  trace ("\n\n\n" ++ show wConstraints) $ workList (Map.fromList constrPairs) wConstraints
  --One last check: once we've solved our constraints, check the constraint
  --That all possible values (upperBound) are covered by least possible matches
  --(lower bound)
  --TODO notation backwards
  finalLowerBoundsCheck wConstraints

--TODO lower bounds for pat and lit cases?

finalLowerBoundsCheck :: [WConstr] -> WorklistM ()
finalLowerBoundsCheck constrList = forM_ constrList $ \c -> do
  liftIO $ putStrLn ("Final bounds check" ++ show c)
  case c of
      WSubEffect r v1 v2 -> do
        data1 <- getAnnData v1
        data2 <- getAnnData v2
        tell $ mismatches r (_ub data1) (_lb data1)
        tell $ mismatches r (_ub data2) (_lb data2)
      WSubEffectOfPat r _ v1 _ _ v2 -> do
        data1 <- getAnnData v1
        data2 <- getAnnData v2
        tell $ mismatches r (_ub data1) (_lb data1)
        tell $ mismatches r (_ub data2) (_lb data2)
      WPatSubEffectOf r _ _ _ v1 v2 -> do
        data1 <- getAnnData v1
        data2 <- getAnnData v2
        tell $ mismatches r (_ub data1) (_lb data1)
        tell $ mismatches r (_ub data2) (_lb data2)
      WLitSubEffectOf r _ v2 -> do
        data2 <- getAnnData v2
        trace ("Data2 " ++ show (_lb data2, _ub data2)) $ tell $ mismatches r (_ub data2) (_lb data2)
      WSubEffectOfLit r v1 _ -> do
        data1 <- getAnnData v1
        trace ("Data1 " ++ show (_lb data1, _ub data1)) $ tell $ mismatches r (_ub data1) (_lb data1)
      WWarning r _ -> return ()


workList :: (Map.Map Int WConstr) -> [WConstr] -> WorklistM ()
workList _ [] = trace "Worklist done" $ return () --When we're finished
workList allConstrs (c:rest) = trace ("Worklist top " ++ show (c:rest) ) $ case c of
  WWarning r s -> do
    tell [(r, Warning.MissingCase s)]
    workList allConstrs rest
  WSubEffect r v1 v2 -> trace "WS" $do
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

  WSubEffectOfLit r v1 realAnn -> trace "WSL" $ do
    changed <- intersectLB r v1 realAnn
    ourData <- getAnnData v1
    let needsUpdate =
          case changed of
            False -> []
            True -> List.map (allConstrs Map.! ) $ _superOf ourData
    workList allConstrs (needsUpdate ++ rest)

  WLitSubEffectOf r realAnn v1 -> trace "WLS" $ do
    changed <- unionUB r v1 realAnn
    ourData <- getAnnData v1
    let needsUpdate =
          case changed of
            False -> []
            True -> List.map (allConstrs Map.! ) $ _subOf ourData
    trace ("WLS subs of our data " ++ show (_subOf ourData, needsUpdate)) $ workList allConstrs (needsUpdate ++ rest)

  WSubEffectOfPat r numArgs wholeVal ctor argNum argVar -> trace "WSP" $ do
    argData <- getAnnData argVar
    wholeData <- getAnnData wholeVal
    let nBottoms =
          (List.replicate argNum realBottom) ++ [_ub argData] ++ (List.replicate (numArgs - argNum - 1) realBottom)
    changedWhole <- unionUB r wholeVal $ RealAnnot  [(ctor, nBottoms)]

    let lbPartOfWhole =
          case _lb wholeData of
            RealTop -> RealTop
            RealAnnot pats ->
              RealAnnot $ List.filter ((== ctor) . fst) pats

    changedPart <- intersectLB r argVar lbPartOfWhole

    let needsUpdate1 =
          case changedPart of
            False -> []
            True -> List.map (allConstrs Map.! ) $ _superOf argData

    let needsUpdate2 =
          case changedWhole of
            False -> []
            True -> List.map (allConstrs Map.! ) $ _subOf wholeData
    workList allConstrs (needsUpdate1 ++ needsUpdate2 ++ rest)

  WPatSubEffectOf r numArgs ctor argNum argVar wholeVal -> trace "WPS" $ do
    argData <- getAnnData argVar
    wholeData <- getAnnData wholeVal
    let nBottoms =
          (List.replicate argNum realBottom) ++ [_lb argData] ++ (List.replicate (numArgs - argNum - 1) realBottom)
    changedWhole <- intersectLB r wholeVal $ RealAnnot [(ctor, nBottoms)]
    let lbPartOfWhole =
          case _ub wholeData of
            RealTop -> RealTop
            RealAnnot pats ->
              RealAnnot $ List.filter ((== ctor) . fst) pats

    changedPart <- unionUB r argVar lbPartOfWhole

    let needsUpdate1 =
          case changedPart of
            False -> []
            True -> List.map (allConstrs Map.! ) $ _subOf argData

    let needsUpdate2 =
          case changedWhole of
            False -> []
            True -> List.map (allConstrs Map.! ) $ _superOf wholeData
    workList allConstrs (needsUpdate1 ++ needsUpdate2 ++ rest)
