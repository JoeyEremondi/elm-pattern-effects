module Type.Effect where

import System.IO.Unsafe
import qualified Data.IORef as IORef
import qualified Data.UnionFind.IO as UF

import Reporting.Annotation as A
import qualified Data.Map as Map

import qualified Data.List as List
import qualified Reporting.Error.Type as Error
import qualified Reporting.Region as R


--TODO beter solution?
globalIntFeed :: IORef.IORef Int
{-# NOINLINE globalIntFeed #-}
globalIntFeed = unsafePerformIO (IORef.newIORef 1)

freshInt :: IO Int
freshInt = do
  i <- IORef.readIORef globalIntFeed
  IORef.writeIORef globalIntFeed (i+1)
  return i

newtype AnnVar = AnnVar (UF.Point RealAnnot, Int)


mkVar :: IO AnnVar
mkVar = do
  newPoint <- UF.fresh $ OpenRealSet []
  i <- freshInt
  return $ AnnVar (newPoint, i)


data RealAnnot =
  ClosedRealSet [(String, [RealAnnot])]
  | OpenRealSet [(String, [RealAnnot])]


data TypeAnnot =
  VarAnnot AnnVar
  | OpenSet [(String, [TypeAnnot])]
  | ClosedSet [(String, [TypeAnnot])]
  | LambdaAnn TypeAnnot TypeAnnot
  | TopAnnot


data AnnotConstr =
  CTrue
  | CSaveEnv
  | CEqual Error.Hint R.Region TypeAnnot TypeAnnot
  | CAnd [AnnotConstr]
  | CLet [AnnScheme] (AnnotConstr)
  | CInstance R.Region String TypeAnnot


data AnnScheme = Scheme
    { _rigidQuantifiers :: [AnnVar]
    , _flexibleQuantifiers :: [AnnVar]
    , _constraint :: AnnotConstr
    , _header :: Map.Map String ()
    }


data AnnFragment = Fragment
    { typeEnv :: Map.Map String (A.Located TypeAnnot)
    , vars :: [AnnVar]
    , typeConstraint :: AnnotConstr
    }

emptyFragment :: AnnFragment
emptyFragment = Fragment Map.empty [] CTrue

joinFragment :: AnnFragment -> AnnFragment -> AnnFragment
joinFragment f1 f2 =
    Fragment
      { typeEnv =
          Map.union (typeEnv f1) (typeEnv f2)

      , vars =
          vars f1 ++ vars f2

      , typeConstraint =
          typeConstraint f1 /\ typeConstraint f2
      }

joinFragments :: [AnnFragment] -> AnnFragment
joinFragments =
    List.foldl' (flip joinFragment) emptyFragment


(==>) :: TypeAnnot -> TypeAnnot -> TypeAnnot
(==>) a b =
  LambdaAnn a b

(/\) a b = CAnd [a,b]


-- ex qs constraint == exists qs. constraint
ex :: [AnnVar] -> AnnotConstr -> AnnotConstr
ex fqs constraint =
    CLet [Scheme [] fqs constraint Map.empty] CTrue


-- fl qs constraint == forall qs. constraint
fl :: [AnnVar] -> AnnotConstr -> AnnotConstr
fl rqs constraint =
    CLet [Scheme rqs [] constraint Map.empty] CTrue


exists :: (TypeAnnot -> IO AnnotConstr) -> IO AnnotConstr
exists f =
  do  v <- mkVar
      ex [v] <$> f (VarAnnot v)
