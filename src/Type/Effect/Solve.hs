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

import qualified Reporting.Region as R

import Debug.Trace (trace)

solve
  :: AnnotConstr
  -> IO ( [(R.Region, Warning.Warning)]
     , TypeAnnot -> IO CanonicalAnnot)
solve c = trace ("In solver, constraint " ++ show c ++ "\n\n" ) $ do
  let solverComp = applyUnifications c
      stateComp = runWriterT $ solveSubsetConstraints solverComp
      ioComp = State.evalStateT stateComp $ SolverState Map.empty Map.empty
  (_, warnings) <- ioComp
  return (warnings, toCanonicalAnnot)

toCanonicalAnnot :: TypeAnnot -> IO CanonicalAnnot
toCanonicalAnnot a = case a of
  VarAnnot (AnnVar (pt, _)) -> do
    ourData <- UF.descriptor pt
    case (_annRepr ourData) of
      Nothing ->
        --TODO better way? use schemes?
        case (_lb ourData, _ub ourData) of
          (RealTop, RealAnnot d) | Map.size d == 0 ->
            return $ VarAnnot $ _uniqueId ourData
          _ ->
            return $ wrapReal $ _ub ourData
      Just repr ->
        toCanonicalAnnot repr
  PatternSet s ->
    PatternSet <$> (dictMapM $ Map.map (mapM toCanonicalAnnot) s )
  LambdaAnn a b ->
    LambdaAnn <$> toCanonicalAnnot a <*> toCanonicalAnnot b
  TopAnnot ->
    return TopAnnot


--TODO shouldn't this hold schemes, not vars?
type Env = Map.Map String (A.Located AnnVar)

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

type SolverM = SolverM' (R.Region, TypeAnnot, TypeAnnot)

type WorklistM = SolverM' (R.Region, Warning.Warning)

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

applyUnifications :: AnnotConstr -> SolverM ()
applyUnifications con = trace ("Applying uni to constraint " ++ show con ++"\n\n") $
  case con of
    CEqual _ r1 r2 -> trace "con Equal" $ do
      _ <- unifyAnnots r1 r2
      return ()
    CAnd constrs -> trace "con AND" $
      forM_ constrs applyUnifications
    CLet schemes letConstr -> trace "con Let" $ do
      oldEnv <- getEnv
      --TODO do something with vars in the scheme?
      headers <- Map.unions <$> forM schemes solveScheme
      modifyEnv $ \env -> Map.union headers env
      applyUnifications letConstr
      --TODO occurs check?
      modifyEnv $ \_ -> oldEnv
    CInstance _ var annot -> trace "con Inst" $ do
      env <- getEnv
      freshCopy <-
        case Map.lookup var env of
          Nothing -> error $ "Could not find name " ++ show var ++ " in Effect.Solve"
          Just (A.A _ annVar) -> do
            mrepr <- getRepr annVar
            case mrepr of
              Nothing -> error "Can't make fresh copy of blank var"
              Just repr -> makeFreshCopy repr
      unifyAnnots freshCopy annot
      return ()
    CSaveEnv -> trace "con Save" $ saveLocalEnv
    CTrue -> trace "con ConTrue" $return ()
    CSubEffect r a1 a2 -> trace ("TELLING " ++ show [(r, a1, a2)]) $ tell [(r, a1, a2)]


    --For our other constraints, we defer solving until after unification is done
makeWConstrs :: R.Region -> TypeAnnot -> TypeAnnot -> SolverM' a [WConstr]
makeWConstrs r aLeft aRight = case (aLeft, aRight) of
    (_, VarAnnot vRight) -> do
      mreprRight <- getRepr vRight
      case mreprRight of
        Just rep1 ->
          makeWConstrs r aLeft rep1

        Nothing -> do
          case aLeft of
            VarAnnot vLeft -> do
              mrepr2 <- getRepr vLeft
              case mrepr2 of
                Nothing ->
                  return [WSubEffect r vLeft vRight]

                Just rep2 ->
                  makeWConstrs  r rep2 (VarAnnot vRight)

            PatternSet s -> do
              let allPairs = Map.toList s
              subLists <- forM allPairs $ \(ctor, subPats) -> do
                let numArgs = length subPats
                let indices = [0 .. numArgs - 1]
                subVars <- forM subPats $ \_ -> liftIO mkVar
                let varPatTriples = zip3 subPats subVars indices
                --Constrain our new variables to the sub-annotations they're linked to
                --as well as adding a constraint for our overall variable to that var as a sub-pattern
                listsPerTriple <- forM varPatTriples  $ \(subPat, subVar, i) -> do
                  subConstrs <- makeWConstrs  r (VarAnnot subVar) subPat
                  return $ (WPatSubEffectOf r numArgs ctor i subVar vRight) : subConstrs
                return $ concat listsPerTriple
              return $ concat subLists

            LambdaAnn arg ret -> do
              --If there are only subset constraints stating that this variable is a lambda
              --We unify it now to be a lambda
              varg <- liftIO mkVar
              vret <- liftIO mkVar
              let newRepr = (LambdaAnn (VarAnnot varg) (VarAnnot vret))
              setRepr vRight newRepr
              makeWConstrs r newRepr aLeft

            TopAnnot ->
              return [WLitSubEffectOf r RealTop vRight]

    (VarAnnot vLeft, _) -> do
            mreprLeft <- getRepr vLeft
            case mreprLeft of
              Just repr -> makeWConstrs r repr aRight

              Nothing -> case aRight of

                PatternSet s -> do
                  let allPairs = Map.toList s
                  subLists <- forM allPairs $ \(ctor, subPats) -> do
                    let numArgs = length subPats
                    let indices = [0 .. numArgs - 1]
                    subVars <- forM subPats $ \_ -> liftIO mkVar
                    let varPatTriples = zip3 subPats subVars indices
                    --Constrain our new variables to the sub-annotations they're linked to
                    --as well as adding a constraint for our overall variable to that var as a sub-pattern
                    listsPerTriple <- forM varPatTriples  $ \(subPat, subVar, i) -> do
                      subConstrs <- makeWConstrs  r (VarAnnot subVar) subPat
                      return $ (WSubEffectOfPat r numArgs vLeft ctor i subVar) : subConstrs
                    return $ concat listsPerTriple
                  return $ concat subLists

                LambdaAnn _ _  -> do
                  --If there are only subset constraints stating that this variable is a lambda
                  --We unify it now to be a lambda
                  varg <- liftIO mkVar
                  vret <- liftIO mkVar
                  let newRepr = (LambdaAnn (VarAnnot varg) (VarAnnot vret))
                  setRepr vLeft newRepr
                  makeWConstrs r newRepr aRight

                TopAnnot ->
                  return [WSubEffectOfLit r vLeft RealTop]


    (PatternSet d1, PatternSet d2) -> do
      listPerCtor <- forM (Map.toList d2) $ \(ctor, subPats) ->
        case (Map.lookup ctor d1) of
          Nothing -> return [WWarning r ctor]
          Just leftSubPats -> do
            listPerArg <- forM (zip leftSubPats subPats) $ \(left, right) ->
              makeWConstrs  r left right
            return $ concat listPerArg
      return $ concat listPerCtor

    (LambdaAnn a1 a2, LambdaAnn b1 b2) -> do
      --Constrain that the argument variable matches at most our lambda
      --And the return matches at least our lambda
      --Basic covariance and contravariance stuff
      argList <- makeWConstrs r b1 a1
      retList <- makeWConstrs r a2 b2
      return $ argList ++ retList

    (TopAnnot, TopAnnot) -> return []

    (x,y) -> error $ "Mismatch in underlying type system\n" ++ show x ++ "\n" ++ show y



      --Make a new variable for each constructor of the pattern


solveScheme :: AnnScheme -> SolverM Env
solveScheme s = do
  let oldHeader = Map.toList $ _header s
  newHeader <- forM oldHeader $ \(nm, (A.A region ann)) -> do
    newVar <- liftIO mkVar
    unifyAnnots (VarAnnot newVar) ann
    return (nm, A.A region newVar)
  --Now that we have a new header with variables, actually solve the constraint
  --On our scheme
  applyUnifications $ _constraint s
  return $ Map.fromList newHeader

makeFreshCopy :: TypeAnnot -> SolverM TypeAnnot
makeFreshCopy ann = do
  let --TODO check if free or not?
    copyHelper :: TypeAnnot -> SolverM (TypeAnnot, [(AnnVar, AnnVar)])
    copyHelper a = case a of
      VarAnnot v -> do
        vnew <- liftIO $ mkVar
        return $ (VarAnnot vnew, [(v, vnew)])
      PatternSet pats -> do
        let patsList = Map.toList pats
        newVarPairs <- forM patsList (\(s, subPats) -> (\x -> (s, x)) <$> forM subPats copyHelper)
        let allPairs = concatMap ((concatMap snd) . snd) newVarPairs
        let newPatList = List.map (\(s, pl) -> (s, List.map fst pl)) newVarPairs
        return (PatternSet $ Map.fromList newPatList, allPairs)
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

  (newCopy, pairList) <- copyHelper ann
  unifyPairs pairList
  return newCopy


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
  RealAnnot $ Map.unionWith (zipWith unionAnn) dict1 dict2

intersectAnn :: RealAnnot -> RealAnnot -> RealAnnot
intersectAnn RealTop x = x
intersectAnn x RealTop = x
intersectAnn (RealAnnot dict1) (RealAnnot dict2) =
  RealAnnot $ Map.intersectionWith (zipWith intersectAnn) dict1 dict2


canMatchAll :: R.Region -> RealAnnot -> RealAnnot -> [(R.Region, Warning.Warning)]
canMatchAll r RealTop _ = []
canMatchAll r _ RealTop = [(r, Warning.MissingCase "_")]
canMatchAll r (RealAnnot d1) (RealAnnot d2) =
  concatMap (\(s, subPatsToMatch) ->
      case Map.lookup s d1 of
        Nothing -> [(r, Warning.MissingCase s)] --TODO better error messages
        --TODO assert same size lists?
        Just subPats -> concat $ zipWith (canMatchAll r) subPats subPatsToMatch
      )  (Map.toList d2)


getAnnData :: AnnVar -> SolverM' a (AnnotData)
getAnnData (AnnVar (pt, _)) =  liftIO $ UF.descriptor pt


--Return true if this union makes a change, false otherwise
unionUB :: R.Region -> AnnVar -> RealAnnot -> WorklistM Bool
unionUB r (AnnVar (pt, _)) ann = do
  annData <- liftIO $ UF.descriptor pt
  let newUB = _ub annData `unionAnn` ann
  liftIO $ UF.setDescriptor pt $ annData {_ub = newUB}
  --Check if we changed the set at all
  --TODO faster shortcut method
  case (canMatchAll r (_ub annData) newUB) of
    [] -> return False
    _ -> do
      tell $ canMatchAll r newUB (_lb annData)
      return True

  --TODO emit warning

intersectLB :: R.Region -> AnnVar -> RealAnnot -> WorklistM Bool
intersectLB r (AnnVar (pt, _)) ann = do
  annData <- liftIO $ UF.descriptor pt
  let newLB = _lb annData `intersectAnn` ann
  liftIO $ UF.setDescriptor pt $ annData {_ub = _ub annData `unionAnn` ann}
  case (canMatchAll r newLB (_lb annData)) of
      [] -> return False
      _ -> do
        tell $ canMatchAll r (_ub annData) newLB
        return True


data VarPosition = Sub | Super

--All constraints where some type is a supertype of the given var
constraintEdges :: WConstr -> [(AnnVar, VarPosition)]
constraintEdges c = case c of
  WSubEffect _ v1 v2 -> [(v1, Sub), (v2, Super)]
  WSubEffectOfPat _ _ v1 _ _ v2 -> [(v1, Sub), (v2, Super)]
  WPatSubEffectOf _ _ _ _ v1 v2 -> [(v1, Sub), (v2, Super)]
  WLitSubEffectOf _ _ v2 -> [(v2, Super)]
  WSubEffectOfLit _ v1 _ -> [(v1, Sub)]
  WWarning _ _ -> []

addConstraintEdge :: Int -> (AnnVar, VarPosition) -> WorklistM ()
addConstraintEdge i (AnnVar (pt, _), Sub) = liftIO $ do
  desc <- UF.descriptor pt
  UF.setDescriptor pt $ desc {_superOf = i : (_superOf desc)}
addConstraintEdge i (AnnVar (pt, _), Super) = liftIO $ do
  desc <- UF.descriptor pt
  UF.setDescriptor pt $ desc {_superOf = i : (_subOf desc)}

solveSubsetConstraints :: SolverM () -> WorklistM ()
solveSubsetConstraints sm = do
  emittedConstrs <- mapWriterT (\ios -> do
      ((), clist) <- ios
      return (clist, [])
      ) sm
  wConstraints <- trace ("\n\n\nEmitted:\n" ++ show emittedConstrs) $ concat <$> forM emittedConstrs  (\(a,b,c) -> makeWConstrs a b c)
  let constrPairs = zip [1..] wConstraints
  forM constrPairs $ \(i, c) -> forM (constraintEdges c) $ addConstraintEdge i
  --TODO avoid list ops here?
  trace ("\n\n\n" ++ show wConstraints) $ workList (Map.fromList constrPairs) [] --TODO emittedConstrs emittedConstrs
  return ()

--TODO lower bounds for pat and lit cases?

workList :: (Map.Map Int WConstr) -> [WConstr] -> WorklistM ()
workList _ [] = return () --When we're finished
workList allConstrs (c:rest) = case c of
  WWarning r s -> do
    tell [(r, Warning.MissingCase s)]
    workList allConstrs rest
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

  WSubEffectOfPat r numArgs wholeVal ctor argNum argVar -> do
    argData <- getAnnData argVar
    wholeData <- getAnnData wholeVal
    let nBottoms =
          (List.replicate argNum realBottom) ++ [_ub argData] ++ (List.replicate (numArgs - argNum - 1) realBottom)
    changedWhole <- unionUB r wholeVal $ RealAnnot $ Map.fromList [(ctor, nBottoms)]
    let lbPartOfWhole =
          case _lb wholeData of
            RealTop -> RealTop
            RealAnnot dict ->
              case Map.lookup ctor dict of
                Nothing -> error "Should have just added this ctor"
                Just argVals -> argVals List.!! argNum

    changedPart <- intersectLB r argVar lbPartOfWhole

    let needsUpdate1 =
          case changedPart of
            False -> []
            True -> List.map (allConstrs Map.! ) $ _superOf argData

    let needsUpdate2 =
          case changedPart of
            False -> []
            True -> List.map (allConstrs Map.! ) $ _subOf wholeData
    workList allConstrs (needsUpdate1 ++ needsUpdate2 ++ rest)

  WPatSubEffectOf r numArgs ctor argNum argVar wholeVal -> do
    argData <- getAnnData argVar
    wholeData <- getAnnData wholeVal
    let nBottoms =
          (List.replicate argNum realBottom) ++ [_lb argData] ++ (List.replicate (numArgs - argNum - 1) realBottom)
    changedWhole <- intersectLB r wholeVal $ RealAnnot $ Map.fromList [(ctor, nBottoms)]
    let lbPartOfWhole =
          case _ub wholeData of
            RealTop -> RealTop
            RealAnnot dict ->
              case Map.lookup ctor dict of
                Nothing -> error "Should have just added this ctor"
                Just argVals -> argVals List.!! argNum

    changedPart <- unionUB r argVar lbPartOfWhole

    let needsUpdate1 =
          case changedPart of
            False -> []
            True -> List.map (allConstrs Map.! ) $ _subOf argData

    let needsUpdate2 =
          case changedPart of
            False -> []
            True -> List.map (allConstrs Map.! ) $ _superOf wholeData
    workList allConstrs (needsUpdate1 ++ needsUpdate2 ++ rest)
