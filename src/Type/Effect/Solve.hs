module Type.Effect.Solve where

import Type.Effect
import Control.Monad.Writer
import Control.Monad.Trans
import Control.Monad (forM, forM_)

import qualified Data.UnionFind.IO as UF

import qualified Data.Map as Map


type SolverM = WriterT [AnnotConstr] IO

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

applyUnifications :: Environment -> AnnotConstr -> SolverM ()
applyUnifications env con =
  case con of
    CEqual _ r1 r2 -> do
      _ <- unifyAnnots env r1 r2
      return ()
    CAnd constrs -> forM_ constrs $ applyUnifications env
    CLet schemes constrs -> error "TODO what is CLet?"
    CInstance _ var annot -> error "TODO get instance"
    CSaveEnv -> return () --TODO what is this?
    CTrue -> return ()
    --For our other constraints, we defer solving until after unification is done
    c -> tell [c]

unifyAnnots :: Environment -> TypeAnnot -> TypeAnnot -> SolverM TypeAnnot
unifyAnnots env r1 r2 =
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
          newRepr <- unifyAnnots env rep1 rep2
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
              newRepr <- unifyAnnots env repr1 repr2
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
              newRepr <- unifyAnnots env repr1 repr2
              setRepr v newRepr
              return newRepr

    (LambdaAnn a1 a2, LambdaAnn b1 b2) ->
      LambdaAnn <$> unifyAnnots env a1 b1 <*> unifyAnnots env a2 b2

    --Special cases: we can unify lambda with Top, giving a TopLambda
    --This helps us deal with Native values, or any other places our analysis fails
    (LambdaAnn a1 a2, TopAnnot) -> do
      unifyAnnots env a1 TopAnnot
      unifyAnnots env a2 TopAnnot
      return $ LambdaAnn TopAnnot TopAnnot
    (TopAnnot, LambdaAnn a1 a2) -> do
        unifyAnnots env a1 TopAnnot
        unifyAnnots env a2 TopAnnot
        return $ LambdaAnn TopAnnot TopAnnot
    _ -> error $ "Invalid unify " ++ show r1 ++ " " ++ show r2
