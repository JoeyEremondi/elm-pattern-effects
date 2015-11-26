module Type.Effect.Solve where

import Type.Effect
import Control.Monad.Writer
import qualified  Control.Monad.State as State
import Control.Monad.Trans
import Control.Monad (forM, forM_)

import Reporting.Annotation as A

import qualified Data.UnionFind.IO as UF

import qualified Data.Map as Map

type Env = Map.Map String (A.Located AnnVar)

data SolverState =
  SolverState
  { sEnv :: Env
  , sSavedEnv :: Env
  }

getEnv :: SolverM Env
getEnv =
    State.gets sEnv

saveLocalEnv :: SolverM ()
saveLocalEnv =
  do  currentEnv <- getEnv
      State.modify $ \state -> state { sSavedEnv = currentEnv }

type SolverM = State.StateT SolverState (WriterT [AnnotConstr] IO)

type Point = UF.Point AnnotData

getRepr :: AnnVar -> SolverM (Maybe TypeAnnot)
getRepr (AnnVar (pt, _)) = do
  AnnotData (repr, _, _) <- liftIO $ UF.descriptor pt
  return repr

setRepr :: AnnVar -> TypeAnnot -> SolverM ()
setRepr (AnnVar (pt, _)) repr = liftIO $ do
  AnnotData (_, lb, ub) <- UF.descriptor pt
  dummyPoint <- UF.fresh $ AnnotData (Just repr, lb, ub)
  UF.union pt dummyPoint
  return ()

union :: AnnVar -> AnnVar -> SolverM ()
union (AnnVar (pt1, _)) (AnnVar (pt2, _)) =
  liftIO $ UF.union pt1 pt2

applyUnifications :: AnnotConstr -> SolverM ()
applyUnifications con =
  case con of
    CEqual _ r1 r2 -> do
      _ <- unifyAnnots r1 r2
      return ()
    CAnd constrs -> forM_ constrs applyUnifications
    CLet schemes constrs -> error "TODO what is CLet?"
    CInstance _ var annot -> error "TODO get instance"
    CSaveEnv -> saveLocalEnv
    CTrue -> return ()
    --For our other constraints, we defer solving until after unification is done
    c -> tell [c]

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
