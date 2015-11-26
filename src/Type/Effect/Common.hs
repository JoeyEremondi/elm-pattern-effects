{-# LANGUAGE DeriveGeneric, FlexibleInstances #-}
module Type.Effect.Common where


import qualified Data.UnionFind.IO as UF
import Data.Binary
import GHC.Generics (Generic)



newtype AnnVar = AnnVar (UF.Point AnnotData, Int)

instance Show AnnVar where
  show (AnnVar (_, i)) = show i

--During unification, we store a (possibly empty) representation of
--our type so far, and our currently calculated lower and upper bounds,
--which are used if our point is a variable
newtype AnnotData = AnnotData (Maybe TypeAnnot, RealAnnot, RealAnnot )


data RealAnnot =
  RealAnnot [(String, [RealAnnot])]
  | RealTop
  deriving (Show, Generic)


data TypeAnnot' v =
  VarAnnot v
  | PatternSet [(String, [TypeAnnot' v])]
  | LambdaAnn (TypeAnnot' v) (TypeAnnot' v)
  | TopAnnot
  deriving (Show, Generic)

type TypeAnnot = TypeAnnot' AnnVar

type CanonicalAnnot = TypeAnnot' Int

instance (Binary a) => Binary (TypeAnnot' a)

prettyAnn :: CanonicalAnnot -> String
prettyAnn ann = case ann of
  VarAnnot i -> "_" ++ show i
  PatternSet sset -> show $ map (\(s,a) -> (s, map prettyAnn a) ) sset
  LambdaAnn from to -> prettyAnn from ++ " ==> " ++ prettyAnn to
  TopAnnot -> "T"
