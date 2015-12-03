{-# LANGUAGE DeriveGeneric, FlexibleInstances #-}
module Type.Effect.Common where


import qualified Data.UnionFind.IO as UF
import Data.Binary
import GHC.Generics (Generic)
import Control.Monad (forM)
import qualified Data.Set as Set
import qualified Data.List as List



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

realBottom = RealAnnot Set.empty

data RealAnnot =
  RealAnnot (Set.Set (String, [RealAnnot]))
  | RealTop
  deriving (Eq, Ord, Show, Generic)


data TypeAnnot' v =
  VarAnnot v
  | SinglePattern String [TypeAnnot' v]
  | LambdaAnn (TypeAnnot' v) (TypeAnnot' v)
  | TopAnnot
  | ReturnsTop --Special case for recursive calls
  deriving (Eq, Ord, Show, Generic)

mapPatSetM :: (Monad m) => (TypeAnnot' v -> m b) -> [(String, [TypeAnnot' v])] -> m [(String, [b])]
mapPatSetM f inL = forM inL $ \(s,annList) -> do
  newAnn <- forM annList f
  return (s, newAnn)

type TypeAnnot = TypeAnnot' AnnVar

--type CanonicalAnnot = TypeAnnot' Int
data CanonicalAnnot =
    CanonVar Int
  | CanonLit RealAnnot
  | CanonPatDict (Set.Set (String, [CanonicalAnnot]))
  | CanonLambda (CanonicalAnnot) (CanonicalAnnot)
  | CanonTop
  deriving (Show, Generic)

data CanonicalConstr =
  CanonSubtype CanonicalAnnot CanonicalAnnot
  deriving (Show, Generic)

instance (Binary a) => Binary (TypeAnnot' a)
instance Binary RealAnnot
instance Binary CanonicalAnnot
instance Binary CanonicalConstr

prettyReal (RealTop) = "T"
prettyReal (RealAnnot subPatsSet) =
  "{"
  ++ (List.intercalate ", " $ Set.toList $ Set.map (\(s,argList) ->
      s ++ "(" ++  (List.intercalate ", " $ map prettyReal argList) ++ ")" ) subPatsSet)
  ++ "}"


prettyAnn :: CanonicalAnnot -> String
prettyAnn ann = case ann of
  CanonVar i -> "_" ++ show i
  CanonLit subPatsSet -> "{" ++ prettyReal subPatsSet ++ "}"
  CanonLambda from to -> prettyAnn from ++ " -> " ++ prettyAnn to
  CanonTop -> "T"
  CanonPatDict subPatsSet ->
    "{" ++
    (List.intercalate ", " $ Set.toList $ Set.map (\(s,argList) ->
      s ++ "(" ++ (List.intercalate ", " $ map prettyAnn argList) ++ ")" ) subPatsSet)
    ++ "}"


prettyConstr :: CanonicalConstr -> String
prettyConstr c = case c of
  CanonSubtype a1 a2 -> prettyAnn a1 ++ " < " ++ prettyAnn a2
