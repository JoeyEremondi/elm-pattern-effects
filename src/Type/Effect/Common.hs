{-# LANGUAGE DeriveGeneric, FlexibleInstances #-}
module Type.Effect.Common where


import qualified Data.UnionFind.IO as UF
import Data.Binary
import GHC.Generics (Generic)
import qualified Data.List as List
import Control.Monad (forM)



newtype AnnVar = AnnVar (UF.Point AnnotData, Int)

instance Show AnnVar where
  show (AnnVar (_, i)) = show i

--During unification, we store a (possibly empty) representation of
--our type so far, and our currently calculated lower and upper bounds,
--which are used if our point is a variable
data AnnotData = AnnotData
  { _annRepr :: Maybe TypeAnnot
  , _lb :: RealAnnot
  , _ub :: RealAnnot
  , _superOf :: [Int]
  , _subOf :: [Int]
  , _uniqueId :: Int
  }

realBottom = RealAnnot []

data RealAnnot =
  RealAnnot [(String, [RealAnnot])]
  | RealTop
  deriving (Show, Generic)


data TypeAnnot' v =
  VarAnnot v
  | SinglePattern String [TypeAnnot' v]
  | LambdaAnn (TypeAnnot' v) (TypeAnnot' v)
  | TopAnnot
  deriving (Show, Generic)

mapPatSetM :: (Monad m) => (TypeAnnot' v -> m b) -> [(String, [TypeAnnot' v])] -> m [(String, [b])]
mapPatSetM f inL = forM inL $ \(s,annList) -> do
  newAnn <- forM annList f
  return (s, newAnn)

type TypeAnnot = TypeAnnot' AnnVar

--type CanonicalAnnot = TypeAnnot' Int
data CanonicalAnnot =
    CanonVar Int
  | CanonLit RealAnnot
  | CanonLambda (CanonicalAnnot) (CanonicalAnnot)
  | CanonTop
  deriving (Show, Generic)

instance (Binary a) => Binary (TypeAnnot' a)
instance Binary RealAnnot
instance Binary CanonicalAnnot

{-
prettyAnn :: CanonicalAnnot -> String
prettyAnn ann = case ann of
  VarAnnot i -> "_" ++ show i
  SinglePattern s subPats -> show $ (s, map prettyAnn subPats)
  LambdaAnn from to -> prettyAnn from ++ " ==> " ++ prettyAnn to
  TopAnnot -> "T"
  -}
