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

type WorklistM = SolverM' Warning.Warning

type Point = UF.Point AnnotData

getRepr :: AnnVar -> SolverM' a (Maybe TypeAnnot)
getRepr (AnnVar (pt, _)) = do
  AnnotData repr _ _ <- liftIO $ UF.descriptor pt
  return repr

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
applyUnifications con =
  case con of
    CEqual _ r1 r2 -> do
      _ <- unifyAnnots r1 r2
      return ()
    CAnd constrs -> forM_ constrs applyUnifications
    CLet schemes letConstr -> do
      oldEnv <- getEnv
      --TODO do something with vars in the scheme?
      headers <- Map.unions <$> forM schemes solveScheme
      modifyEnv $ \env -> Map.union headers env
      applyUnifications letConstr
      --TODO occurs check?
      modifyEnv $ \_ -> oldEnv
    CInstance _ var annot -> do
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
    CSaveEnv -> saveLocalEnv
    CTrue -> return ()
    CSubEffect r a1 a2 -> tell [(r, a1, a2)]


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

    (_, VarAnnot vLeft) -> do
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
          Nothing -> error "Literal violates pattern constraint"
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

    _ -> error "Mismatch in underlying type system"



      --Make a new variable for each constructor of the pattern


solveScheme :: AnnScheme -> SolverM Env
solveScheme s = do
  let oldHeader = Map.toList $ _header s
  newHeader <- forM oldHeader $ \(nm, (A.A region ann)) -> do
    newVar <- liftIO mkVar
    unifyAnnots (VarAnnot newVar) ann
    return (nm, A.A region newVar)
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

--Constraints we can actually deal with in our worklist algorithm
data WConstr =
  WSubEffect R.Region AnnVar AnnVar
  | WSubEffectOfPat R.Region Int AnnVar String Int AnnVar --Specific sub-pattern constraints
  | WPatSubEffectOf R.Region Int String Int AnnVar AnnVar
  | WSubEffectOfLit R.Region AnnVar RealAnnot
  | WLitSubEffectOf R.Region RealAnnot AnnVar


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


canMatchAll :: RealAnnot -> RealAnnot -> [Warning.Warning]
canMatchAll RealTop _ = []
canMatchAll _ RealTop = [error "All cases must be matched here"]
canMatchAll (RealAnnot d1) (RealAnnot d2) =
  concatMap (\(s, subPatsToMatch) ->
      case Map.lookup s d1 of
        Nothing -> [error "TODO warning for unmatched pattern"]
        --TODO assert same size lists?
        Just subPats -> concat $ zipWith canMatchAll subPats subPatsToMatch
      )  (Map.toList d2)


getAnnData :: AnnVar -> SolverM' a (AnnotData)
getAnnData (AnnVar (pt, _)) =  liftIO $ UF.descriptor pt


--Return true if this union makes a change, false otherwise
unionUB :: AnnVar -> RealAnnot -> WorklistM Bool
unionUB (AnnVar (pt, _)) ann = do
  annData <- liftIO $ UF.descriptor pt
  let newUB = _ub annData `unionAnn` ann
  liftIO $ UF.setDescriptor pt $ annData {_ub = newUB}
  --Check if we changed the set at all
  --TODO faster shortcut method
  case (canMatchAll (_ub annData) newUB) of
    [] -> return False
    _ -> do
      tell $ canMatchAll newUB (_lb annData)
      return True

  --TODO emit warning

intersectLB :: AnnVar -> RealAnnot -> WorklistM Bool
intersectLB (AnnVar (pt, _)) ann = do
  annData <- liftIO $ UF.descriptor pt
  let newLB = _lb annData `intersectAnn` ann
  liftIO $ UF.setDescriptor pt $ annData {_ub = _ub annData `unionAnn` ann}
  case (canMatchAll newLB (_lb annData)) of
      [] -> return False
      _ -> do
        tell $ canMatchAll (_ub annData) newLB
        return True





outgoingEdges :: [AnnotConstr] -> AnnVar -> WorklistM [AnnotConstr]
outgoingEdges allConstrs v = error "TODO edges"



solveSubsetConstraints :: SolverM () -> WorklistM ()
solveSubsetConstraints sm = do
  emittedConstrs <- mapWriterT (\ios -> do
      ((), clist) <- ios
      return (clist, [])
      ) sm
  workList [] [] --TODO emittedConstrs emittedConstrs
  return ()

--TODO lower bounds for pat and lit cases?

workList :: [WConstr] -> [WConstr] -> WorklistM ()
worklist _ [] = return () --When we're finished
workList allConstrs (c:rest) = case c of
  WSubEffect r v1 v2 -> do
    data1 <- getAnnData v1
    data2 <- getAnnData v2
    changed1 <- unionUB v2 (_ub data1)
    changed2 <- intersectLB v1 (_lb data2)

    needsUpdate1 <-
      case changed1 of
        False -> return []
        True -> error "TODO"

    needsUpdate2 <-
      case changed2 of
        False -> return []
        True -> error "TODO"
    worklist allConstrs (needsUpdate1 ++ needsUpdate2 ++ rest)

  WSubEffectOfLit r v1 realAnn -> do
    changed <- intersectLB v1 realAnn
    needsUpdate <-
      case changed of
        False -> return []
        True -> error "TODO"
    worklist allConstrs (needsUpdate ++ rest)

  WLitSubEffectOf r realAnn v1 -> do
    changed <- unionUB v1 realAnn
    needsUpdate <-
      case changed of
        False -> return []
        True -> error "TODO"
    worklist allConstrs (needsUpdate ++ rest)

  WSubEffectOfPat r numArgs wholeVal ctor argNum argVar -> do
    argData <- getAnnData argVar
    wholeData <- getAnnData wholeVal
    let nBottoms =
          (List.replicate argNum realBottom) ++ [_ub argData] ++ (List.replicate (numArgs - argNum - 1) realBottom)
    changedWhole <- unionUB wholeVal $ RealAnnot $ Map.fromList [(ctor, nBottoms)]
    let lbPartOfWhole =
          case _lb wholeData of
            RealTop -> RealTop
            RealAnnot dict ->
              case Map.lookup ctor dict of
                Nothing -> error "Should have just added this ctor"
                Just argVals -> argVals List.!! argNum

    changedPart <- intersectLB argVar lbPartOfWhole

    needsUpdate1 <-
      case changedPart of
        False -> return []
        True -> error "TODO"

    needsUpdate2 <-
      case changedWhole of
        False -> return []
        True -> error "TODO"
    worklist allConstrs (needsUpdate1 ++ needsUpdate2 ++ rest)

  WPatSubEffectOf r numArgs ctor argNum argVar wholeVal -> do
    argData <- getAnnData argVar
    wholeData <- getAnnData wholeVal
    let nBottoms =
          (List.replicate argNum realBottom) ++ [_lb argData] ++ (List.replicate (numArgs - argNum - 1) realBottom)
    changedWhole <- intersectLB wholeVal $ RealAnnot $ Map.fromList [(ctor, nBottoms)]
    let lbPartOfWhole =
          case _ub wholeData of
            RealTop -> RealTop
            RealAnnot dict ->
              case Map.lookup ctor dict of
                Nothing -> error "Should have just added this ctor"
                Just argVals -> argVals List.!! argNum

    changedPart <- unionUB argVar lbPartOfWhole

    needsUpdate1 <-
      case changedPart of
        False -> return []
        True -> error "TODO"

    needsUpdate2 <-
      case changedWhole of
        False -> return []
        True -> error "TODO"
    worklist allConstrs (needsUpdate1 ++ needsUpdate2 ++ rest)
