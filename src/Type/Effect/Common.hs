module Type.Effect.Common where


import qualified Data.UnionFind.IO as UF



newtype AnnVar = AnnVar (UF.Point RealAnnot, Int)

instance Show AnnVar where
  show (AnnVar (_, i)) = show i


data RealAnnot =
  ClosedRealSet [(String, [RealAnnot])]
  | OpenRealSet [(String, [RealAnnot])]
  deriving (Show)


data TypeAnnot' v =
  VarAnnot v
  | OpenSet [(String, [TypeAnnot])]
  | ClosedSet [(String, [TypeAnnot])]
  | LambdaAnn TypeAnnot TypeAnnot
  | TopAnnot
  deriving (Show)

type TypeAnnot = TypeAnnot' AnnVar

type CanonicalAnnot = TypeAnnot' Int
