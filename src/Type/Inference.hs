module Type.Inference where

import Control.Arrow (first, second)
import Control.Monad.Except (Except, forM, liftIO, runExceptT, throwError)
import qualified Data.Map as Map
import qualified Data.Traversable as Traverse

import AST.Module as Module
import qualified AST.Module.Name as ModuleName
import qualified AST.Type as Type
import qualified AST.Variable as Var
import qualified Reporting.Annotation as A
import qualified Reporting.Error.Type as Error
import qualified Reporting.Warning as Warning
import qualified Reporting.Region as R
import qualified Type.Constrain.Expression as TcExpr
import qualified Type.Environment as Env
import qualified Type.Solve as Solve
import qualified Type.State as TS
import qualified Type.Type as T
import qualified Type.Effect as Effect
import qualified Type.Effect.Expression
import qualified Type.Effect.Solve

import System.IO.Unsafe
    -- Maybe possible to switch over to ST instead of IO.
    -- I don't think that'd be worthwhile though.


infer
    :: Module.Interfaces
    -> Module.CanonicalModule
    -> Except [A.Located Error.Error] (Map.Map String Type.Canonical, Map.Map String Effect.CanonicalAnnot, [(R.Region, Warning.Warning)])
infer interfaces modul =
  either throwError return $ unsafePerformIO $ runExceptT $
    do  (header, constraint) <-
            liftIO (genConstraints interfaces modul)


        state <- Solve.solve constraint

        let header' = Map.delete "::" header
        let types = Map.map A.drop (Map.difference (TS.sSavedEnv state) header')

        (annotHeader, annotWarns, annotFun) <- liftIO $ genPatternWarnings interfaces modul

        finalAnnots <-
          Map.fromList <$>  forM (Map.toList annotHeader) (\(s, a) -> ((,) s) <$> (liftIO $ annotFun a))

        typeDict <- liftIO (Traverse.traverse T.toSrcType types)
        return (typeDict, finalAnnots, annotWarns)


genConstraints
    :: Module.Interfaces
    -> Module.CanonicalModule
    -> IO (Map.Map String T.Type, T.TypeConstraint)
genConstraints interfaces modul =
  do  env <- Env.initialize (canonicalizeAdts interfaces modul)

      ctors <-
          forM (Env.ctorNames env) $ \name ->
            do  (_, vars, args, result) <- Env.freshDataScheme env name
                return (name, (vars, foldr (T.==>) result args))

      importedVars <-
          mapM (canonicalizeValues env) (Map.toList interfaces)

      let allTypes = concat (ctors : importedVars)
      let vars = concatMap (fst . snd) allTypes
      let header = Map.map snd (Map.fromList allTypes)
      let environ = T.CLet [ T.Scheme vars [] T.CTrue (Map.map (A.A undefined) header) ]

      fvar <- T.mkVar Nothing

      constraint <-
          TcExpr.constrain env (program (body modul)) (T.VarN fvar)

      return (header, environ constraint)


genPatternWarnings
    :: Module.Interfaces
    -> Module.CanonicalModule
    -> IO ( Map.Map String Effect.TypeAnnot
          , [(R.Region, Warning.Warning)]
          , (Effect.TypeAnnot -> IO Effect.CanonicalAnnot))
genPatternWarnings interfaces modul =
  do  env <- Effect.initializeEnv (canonicalizeAdts interfaces modul)

      ctors <- forM (Effect.ctorNames env) $ \name ->
          do  (_, vars, args, result) <- Effect.freshDataScheme env name
              return (name, (vars, foldr (Effect.==>) result args))

      importedVars <-
          mapM (Effect.canonicalizeValues env) (Map.toList interfaces)

      let allTypes = concat (ctors : importedVars)
      let vars = concatMap (fst . snd) allTypes
      let header = Map.map snd (Map.fromList allTypes)
      --Adds our initial values to our env, basically
      let environ c = Effect.CLet [ Effect.Scheme vars Effect.CTrue (Map.map (A.A undefined) header) ] c

      fvar <- Effect.mkVar

      constraint <-
          Type.Effect.Expression.constrain env (program (body modul)) (Effect.VarAnnot fvar)

      putStrLn $ show constraint

      (warnings, canonFun) <- Type.Effect.Solve.solve (environ constraint)

      return (header, warnings, canonFun)


canonicalizeValues
    :: Env.Environment
    -> (ModuleName.Canonical, Interface)
    -> IO [(String, ([T.Variable], T.Type))]
canonicalizeValues env (moduleName, iface) =
    forM (Map.toList (iTypes iface)) $ \(name,tipe) ->
        do  tipe' <- Env.instantiateType env tipe Map.empty
            return
              ( ModuleName.canonicalToString moduleName ++ "." ++ name
              , tipe'
              )


canonicalizeAdts :: Module.Interfaces -> Module.CanonicalModule -> [CanonicalAdt]
canonicalizeAdts interfaces modul =
    localAdts ++ importedAdts
  where
    localAdts :: [CanonicalAdt]
    localAdts =
      format (Module.name modul, datatypes (body modul))

    importedAdts :: [CanonicalAdt]
    importedAdts =
      concatMap (format . second iAdts) (Map.toList interfaces)


format :: (ModuleName.Canonical, Module.ADTs) -> [CanonicalAdt]
format (home, adts) =
    map canonical (Map.toList adts)
  where
    canonical :: (String, AdtInfo String) -> CanonicalAdt
    canonical (name, (tvars, ctors)) =
        ( toVar name
        , (tvars, map (first toVar) ctors)
        )

    toVar :: String -> Var.Canonical
    toVar name =
        Var.fromModule home name
