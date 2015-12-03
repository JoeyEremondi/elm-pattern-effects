{-# LANGUAGE FlexibleInstances #-}
module Type.Effect (module Type.Effect.Common, module Type.Effect) where

import Type.Effect.Common

import System.IO.Unsafe
import qualified Data.IORef as IORef
import qualified Data.UnionFind.IO as UF

import qualified AST.Type as T
import qualified AST.Variable as V
import qualified AST.Module as Module
import qualified AST.Module.Name as ModuleName

import qualified Reporting.Warning as Warning

import Reporting.Annotation as A
import qualified Data.Map as Map

import qualified Data.List as List
import qualified Data.Set as Set
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



mkVar :: IO AnnVar
mkVar = do
  i <- freshInt
  newPoint <- UF.fresh $ AnnotData Nothing RealTop realBottom [] [] i
  return $ AnnVar (newPoint, i)

{-
wrapReal :: RealAnnot -> TypeAnnot' a
wrapReal realAnn =
  case realAnn of
    RealTop -> TopAnnot
    RealAnnot pats -> PatternSet $ List.map (\(s,x) -> (s, List.map wrapReal x)) pats
    -}


data AnnotConstr =
  CTrue
  | CSaveEnv
  | CEqual R.Region TypeAnnot TypeAnnot
  | CAnd [AnnotConstr]
  | CLet [AnnScheme] (AnnotConstr) --Solve AnnotConstr with the given schemes added to the env
  | CInstance R.Region String TypeAnnot
  | CSubEffect R.Region TypeAnnot TypeAnnot
  | CCanBeMatchedBy R.Region TypeAnnot RealAnnot
  | CMatchesImplies R.Region (TypeAnnot, RealAnnot) (TypeAnnot, TypeAnnot)
--  | COnlyMatches R.Region TypeAnnot TypeAnnot
  deriving (Show)


data AnnScheme = Scheme
    { -- _quantifiers :: [AnnVar] --Variables we instantiate
    _constraint :: AnnotConstr
    , _header :: Map.Map String (A.Located TypeAnnot) --Maps the name for this scheme to their innerType reprs
    }
    | MonoScheme (Map.Map String (A.Located TypeAnnot) )
    deriving (Show)

instance Show Error.Hint where
  show _ = ""

instance Show (Annotated R.Region TypeAnnot) where
  show (A.A _ a) = show a

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
--ex :: [AnnVar] -> AnnotConstr -> AnnotConstr
--ex fqs constraint =
--    CLet [Scheme fqs constraint Map.empty] CTrue


{-
-- fl qs constraint == forall qs. constraint
fl :: [AnnVar] -> AnnotConstr -> AnnotConstr
fl rqs constraint =
    CLet [Scheme rqs [] constraint Map.empty] CTrue
-}


--exists :: (TypeAnnot -> IO AnnotConstr) -> IO AnnotConstr
--exists f =
--  do  v <- mkVar
--      ex [v] <$> f (VarAnnot v)

monoscheme :: Map.Map String (A.Located TypeAnnot) -> AnnScheme
monoscheme headers =
  MonoScheme headers


--toScheme :: AnnFragment -> AnnScheme
--toScheme fragment =
--    Scheme (vars fragment) (typeConstraint fragment) (typeEnv fragment)

--toMono :: AnnFragment -> AnnScheme
--toMono fragment =
--    MonoScheme (typeEnv fragment)


data Environment = Environment
    { _constructor :: Map.Map String (IO (Int, [AnnVar], [TypeAnnot], TypeAnnot))
    , _types :: (Map.Map String TypeAnnot)
    , _value :: (Map.Map String TypeAnnot)
    , _moduleName :: String
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



initializeEnv :: String -> [Module.CanonicalAdt] -> IO Environment
initializeEnv mname datatypes =
  do  types <- adtAnnots datatypes
      let env =
            Environment
              { _constructor = Map.empty
              , _value = Map.empty
              , _types = types
              , _moduleName = mname
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
        --[ ("[]", inst 1 $ \ [t] -> ([], list t))
        --, ("::", inst 1 $ \ [t] -> ([t, list t], list t))
        --] ++ List.map tupleCtor [0..9] ++
           concatMap annotationForCtor datatypes


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
                 , SinglePattern (V.toString nm) $ List.map VarAnnot argTypes
                 )



canonicalizeValues
    :: Environment
    -> (ModuleName.Canonical, Module.Interface)
    -> IO [(String, ([AnnVar], TypeAnnot), AnnotConstr)]
canonicalizeValues _env (moduleName, iface)=
  forM (Map.toList (Module.iAnnots iface)) $ \(name,canonTriple) ->
        do  ((instResult, instConstr), finalState) <- State.runStateT (fromCanonicalTriple canonTriple) Map.empty
            let allVars = Map.elems  finalState
            return
              ( ModuleName.canonicalToString moduleName ++ "." ++ name
              , (allVars, instResult)
              , instConstr
              )

dictMapM :: (Ord k, Monad m) => Map.Map k (m a) -> m (Map.Map k a)
dictMapM dict = do
  let (klist, mlist) = unzip $ Map.toList dict
  vlist <- sequence mlist
  return $ Map.fromList $ zip klist vlist


fromReal :: RealAnnot -> State.StateT (Map.Map Int AnnVar) IO (TypeAnnot, AnnotConstr)
fromReal RealTop = return (TopAnnot, CTrue)
fromReal (RealAnnot l) = do
   --TODO set-way to do this?
   let (ctors, subAnns) = List.unzip $ Set.toList l
   pairList <-  forM subAnns $ \annList -> do
     (newSubAnns, subConstrLists) <- unzip <$> forM annList fromReal
     return (newSubAnns, subConstrLists)
   let (newAnns, constrList) = unzip pairList
   ourResult <- State.liftIO $ VarAnnot <$> mkVar
   let containedPatterns = zipWith SinglePattern ctors newAnns
   let ourConstraints =
          List.map (\p -> CSubEffect dummyRegion p ourResult)
            containedPatterns
   return (ourResult , CAnd $ ourConstraints ++ concat constrList)

dummyRegion = R.Region (R.Position 0 0) (R.Position 0 0)

warningString w = case w of
  Warning.MissingCase s -> "Missing case " ++ show s
  _ -> ""

fromCanonicalTriple (canonAnnot, _, _) = fromCanonical canonAnnot

fromCanonical :: CanonicalAnnot -> State.StateT (Map.Map Int AnnVar) IO (TypeAnnot, AnnotConstr)
fromCanonical canonAnnot = do
  currentMap <- State.get
  case canonAnnot of

    CanonVar i ->
      case (Map.lookup i currentMap) of
        Nothing -> do
          varI <- State.lift $ mkVar
          State.put (Map.insert i varI currentMap)
          return (VarAnnot varI, CTrue)

        Just v -> return (VarAnnot v, CTrue)
    CanonLit r -> fromReal r
    CanonLambda t1 t2 -> do
      (arg, argCon) <- fromCanonical t1
      (res, resCon) <- fromCanonical t2
      return (LambdaAnn arg res, CAnd [argCon, resCon])

    CanonPatDict theList -> do
      ourReturn <- State.liftIO $ VarAnnot <$> mkVar
      let (ctors, argLists) = List.unzip $ Set.toList theList
      newResult <- forM argLists $ \argList -> do
        (newArgs, constrList) <- unzip <$> forM argList fromCanonical
        return (newArgs, constrList)
      let (newLists, constrs) = unzip newResult
      let patsWeContain = zipWith SinglePattern ctors newLists
      let ourConstrs = List.map (\p -> CSubEffect dummyRegion p ourReturn) patsWeContain
      return (ourReturn, CAnd (ourConstrs ++ concat constrs))

    CanonTop -> return (TopAnnot, CTrue)

freshDataScheme :: Environment -> String -> IO (Int, [AnnVar], [TypeAnnot], TypeAnnot)
freshDataScheme = envGet _constructor

envGet :: (Environment -> Map.Map String a) -> Environment -> String -> a
envGet subDict env key =
    Map.findWithDefault (error msg) key (subDict env)
  where
    msg = "Could not find type constructor `" ++ key ++ "` while checking types."


ctorNames env =
  Map.keys (_constructor env)
