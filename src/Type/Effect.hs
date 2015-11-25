{-# LANGUAGE FlexibleInstances #-}
module Type.Effect where

import System.IO.Unsafe
import qualified Data.IORef as IORef
import qualified Data.UnionFind.IO as UF

import qualified AST.Type as T
import qualified AST.Variable as V
import qualified AST.Module as Module
import qualified AST.Module.Name as ModuleName


import Reporting.Annotation as A
import qualified Data.Map as Map

import qualified Data.List as List
import qualified Reporting.Error.Type as Error
import qualified Reporting.Region as R

import qualified Control.Monad.State as State

import Control.Monad (forM)
import Data.Map ((!))


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

instance Show AnnVar where
  show (AnnVar (_, i)) = show i


mkVar :: IO AnnVar
mkVar = do
  newPoint <- UF.fresh $ OpenRealSet []
  i <- freshInt
  return $ AnnVar (newPoint, i)


data RealAnnot =
  ClosedRealSet [(String, [RealAnnot])]
  | OpenRealSet [(String, [RealAnnot])]
  deriving (Show)


data TypeAnnot =
  VarAnnot AnnVar
  | OpenSet [(String, [TypeAnnot])]
  | ClosedSet [(String, [TypeAnnot])]
  | LambdaAnn TypeAnnot TypeAnnot
  | TopAnnot
  deriving (Show)


data AnnotConstr =
  CTrue
  | CSaveEnv
  | CEqual Error.Hint R.Region TypeAnnot TypeAnnot
  | CAnd [AnnotConstr]
  | CLet [AnnScheme] (AnnotConstr)
  | CInstance R.Region String TypeAnnot
  | CContainsAtLeast R.Region TypeAnnot TypeAnnot
  | CContainsOnly R.Region TypeAnnot TypeAnnot
  deriving (Show)


data AnnScheme = Scheme
    { _rigidQuantifiers :: [AnnVar]
    , _flexibleQuantifiers :: [AnnVar]
    , _constraint :: AnnotConstr
    , _header :: Map.Map String (A.Located TypeAnnot)
    }
    deriving (Show)

instance Show Error.Hint where
  show _ = ""

instance Show (Annotated R.Region TypeAnnot) where
  show (A.A r a) = show a

data AnnFragment = Fragment
    { typeEnv :: Map.Map String (A.Located TypeAnnot)
    , vars :: [AnnVar]
    , typeConstraint :: AnnotConstr
    }
    deriving (Show)

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


infixr 9 ==>
(==>) :: TypeAnnot -> TypeAnnot -> TypeAnnot
(==>) a b =
  LambdaAnn a b


infixl 8 /\
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

monoscheme :: Map.Map String (A.Located TypeAnnot) -> AnnScheme
monoscheme headers =
  Scheme [] [] CTrue headers

mkRigid :: String -> IO AnnVar
mkRigid = error "TODO mkRigid"

mkNamedVar :: String -> IO AnnVar
mkNamedVar name = error "TODO mkNamedVar"

toScheme :: AnnFragment -> AnnScheme
toScheme fragment =
    Scheme [] (vars fragment) (typeConstraint fragment) (typeEnv fragment)


data Environment = Environment
    { _constructor :: Map.Map String (IO (Int, [AnnVar], [TypeAnnot], TypeAnnot))
    , _types :: (Map.Map String TypeAnnot)
    , _value :: (Map.Map String TypeAnnot)
    }


get :: (Environment -> Map.Map String a) -> Environment -> String -> a
get subDict env key =
    Map.findWithDefault (error msg) key (subDict env)
  where
    msg = "Could not find type constructor `" ++ key ++ "` while checking types."


getType :: Environment -> String -> TypeAnnot
getType = get _types


addValues :: Environment -> [(String, AnnVar)] -> Environment
addValues env newValues =
  env
    { _value =
        List.foldl'
          (\dict (name, var) -> Map.insert name (VarAnnot var) dict)
          (_value env)
          newValues
    }


instantiateType = error "TODO instantiateType"


initializeEnv :: [Module.CanonicalAdt] -> IO Environment
initializeEnv datatypes =
  do  types <- adtAnnots datatypes
      let env =
            Environment
              { _constructor = Map.empty
              , _value = Map.empty
              , _types = types
              }
      return $ env { _constructor = makeConstructors env datatypes }

adtAnnots :: [Module.CanonicalAdt] -> IO (Map.Map String TypeAnnot)
adtAnnots datatypes =
  do  adts <- mapM makeImported datatypes
      bs   <- mapM makeBuiltin builtins
      return (Map.fromList (adts ++ bs)) --TODO check this whole thing
  where
    makeImported (name, _) =
      do  tvar <- mkVar
          return (V.toString name, VarAnnot tvar)

    makeBuiltin (name, _) =
      do  name' <- mkVar
          return (name, VarAnnot name')

    builtins =
        concat
          [ List.map tuple [0..9]
          , kind 1 ["List"]
          , kind 0 ["Int","Float","Char","String","Bool"]
          ]
      where
        tuple n = ("_Tuple" ++ show n, n)
        kind n names = List.map (\name -> (name, n)) names


makeConstructors
    :: Environment
    -> [Module.CanonicalAdt]
    -> Map.Map String (IO (Int, [AnnVar], [TypeAnnot], TypeAnnot))
makeConstructors env datatypes =
    Map.fromList builtins
  where
    list t =
      (_types env ! "List")

    inst :: Int -> ([TypeAnnot] -> ([TypeAnnot], TypeAnnot)) -> IO (Int, [AnnVar], [TypeAnnot], TypeAnnot)
    inst numTVars tipe =
      do  vars <- mapM (\_ -> mkVar) [1..numTVars]
          let (args, result) = tipe (List.map (VarAnnot) vars)
          return (length args, vars, args, result)

    tupleCtor n =
        let name = "_Tuple" ++ show n
        in  (name, inst n $ \vs -> (vs, (_types env ! name) ))

    builtins :: [ (String, IO (Int, [AnnVar], [TypeAnnot], TypeAnnot)) ]
    builtins =
        [ ("[]", inst 1 $ \ [t] -> ([], list t))
        , ("::", inst 1 $ \ [t] -> ([t, list t], list t))
        ] ++ List.map tupleCtor [0..9]
          ++ concatMap annotationForCtor datatypes


annotationForCtor
    :: (V.Canonical, Module.AdtInfo V.Canonical)
    -> [(String, IO (Int, [AnnVar], [TypeAnnot], TypeAnnot))]
annotationForCtor (_, (_, ctors)) =
    zip (List.map (V.toString . fst) ctors) (List.map inst ctors)
  where
    inst :: (V.Canonical, [T.Canonical]) -> IO (Int, [AnnVar], [TypeAnnot], TypeAnnot)
    inst (nm, args) =
      do  let numArgs = length args
          argTypes <- forM args $ \_ -> mkVar
          return (numArgs
                 , [] --TODO what is this?
                 , List.map VarAnnot argTypes
                 , ClosedSet [(V.toString nm, List.map VarAnnot argTypes)]
                 )



canonicalizeValues
    :: Environment
    -> (ModuleName.Canonical, Module.Interface)
    -> IO [(String, ([AnnVar], TypeAnnot))]
canonicalizeValues env (moduleName, iface)=
  forM (Map.toList (Module.iTypes iface)) $ \(name,tipe) ->
        do  tipe' <- instantiateType env tipe Map.empty
            return
              ( ModuleName.canonicalToString moduleName ++ "." ++ name
              , tipe'
              )

freshDataScheme :: Environment -> String -> IO (Int, [AnnVar], [TypeAnnot], TypeAnnot)
freshDataScheme = error "Error freshData"


ctorNames env =
  Map.keys (_constructor env)
