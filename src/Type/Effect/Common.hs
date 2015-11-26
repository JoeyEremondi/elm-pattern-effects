{-# LANGUAGE DeriveGeneric, FlexibleInstances #-}
module Type.Effect.Common where


import qualified Data.UnionFind.IO as UF
import Data.Binary
import GHC.Generics (Generic)



newtype AnnVar = AnnVar (UF.Point RealAnnot, Int)

instance Show AnnVar where
  show (AnnVar (_, i)) = show i


data RealAnnot =
  ClosedRealSet [(String, [RealAnnot])]
  | OpenRealSet [(String, [RealAnnot])]
  deriving (Show, Generic)


data TypeAnnot' v =
  VarAnnot v
  | OpenSet [(String, [TypeAnnot' v])]
  | ClosedSet [(String, [TypeAnnot' v])]
  | LambdaAnn (TypeAnnot' v) (TypeAnnot' v)
  | TopAnnot
  deriving (Show, Generic)

type TypeAnnot = TypeAnnot' AnnVar

type CanonicalAnnot = TypeAnnot' Int

instance (Binary a) => Binary (TypeAnnot' a)
