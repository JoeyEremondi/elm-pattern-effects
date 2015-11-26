module Type.Effect.Solve where

import Type.Effect
import Control.Monad.Writer
import qualified  Control.Monad.State as State
import Control.Monad.Trans
import Control.Monad (forM, forM_)

import qualified Data.List as List

import Reporting.Annotation as A
import Reporting.Warning as Warning

import qualified Data.UnionFind.IO as UF

import qualified Data.Map as Map

--TODO shouldn't this hold schemes, not vars?
type Env = Map.Map String (A.Located AnnVar)

data SolverState =
  SolverState
  { sEnv :: Env
  , sSavedEnv :: Env
  }

getEnv :: SolverM Env
getEnv =
    State.gets sEnv

modifyEnv :: (Env -> Env) -> SolverM ()
modifyEnv f =
    State.modify $ \state -> state { sEnv = f (sEnv state) }

saveLocalEnv :: SolverM ()
saveLocalEnv =
  do  currentEnv <- getEnv
      State.modify $ \state -> state { sSavedEnv = currentEnv }

type SolverM' a =  WriterT [a] (State.StateT SolverState IO)

type SolverM = SolverM' AnnotConstr

type WorklistM = SolverM' Warning.Warning

type Point = UF.Point AnnotData

getRepr :: AnnVar -> SolverM (Maybe TypeAnnot)
getRepr (AnnVar (pt, _)) = do
  AnnotData (repr, _, _) <- liftIO $ UF.descriptor pt
  return repr

setRepr :: AnnVar -> TypeAnnot -> SolverM ()
setRepr (AnnVar (pt, _)) repr = liftIO $ do
  AnnotData (_, lb, ub) <- UF.descriptor pt
  UF.setDescriptor pt $ AnnotData (Just repr, lb, ub)

union :: AnnVar -> AnnVar -> SolverM ()
union (AnnVar (pt1, _)) (AnnVar (pt2, _)) =
  liftIO $ UF.union pt1 pt2

areSame :: AnnVar -> AnnVar -> SolverM Bool
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
    --For our other constraints, we defer solving until after unification is done
    c -> tell [c]

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
        newVarPairs <- forM pats (\(s, subPats) -> (\x -> (s, x)) <$> forM subPats copyHelper)
        let allPairs = concatMap ((concatMap snd) . snd) newVarPairs
        let newPatList = List.map (\(s, pl) -> (s, List.map fst pl)) newVarPairs
        return (PatternSet newPatList, allPairs)
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

outgoingUB :: [AnnotConstr] -> AnnVar -> [AnnotConstr]
outgoingUB allConstrs v = do
  return [] --TODO impelement

solveSubsetConstraints :: SolverM () -> WorklistM ()
solveSubsetConstraints sm = do
  emittedConstrs <- mapWriterT (\ios -> do
      ((), clist) <- ios
      return (clist, [])
      ) sm
  return ()


workList :: [AnnotConstr] -> WorklistM ()
worklist [] = return () --When we're finished
workList (c:rest) = case c of
  CContainsAtLeast _ (VarAnnot v1) (VarAnnot v2) ->
    error "TODO"
