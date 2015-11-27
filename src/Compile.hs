module Compile (compile, compileFile) where

import qualified Data.Map as Map

import qualified AST.Module as Module
import qualified AST.Module.Name as ModuleName
import qualified Canonicalize
import Elm.Utils ((|>))
import qualified Elm.Package as Package
import qualified Nitpick.PatternMatches as Nitpick
import qualified Nitpick.TopLevelTypes as Nitpick
import qualified Optimize
import qualified Parse.Helpers as Parse
import qualified Parse.Parse as Parse
import qualified Reporting.Error as Error
import qualified Reporting.Result as Result
import qualified Reporting.Warning as Warning
import qualified Type.Inference as TI

import Control.Monad (forM)

compileFile :: String -> IO String
compileFile fileName = do
  source <- readFile fileName
  let result = compile (Package.Name "elm-lang" "core") True [] Map.empty source
  case result of
    (Result.Result _ (Result.Ok _)) -> return "Ok"
    _ -> return "Error"

compile
    :: Package.Name
    -> Bool
    -> [ModuleName.Canonical]
    -> Module.Interfaces
    -> String
    -> Result.Result Warning.Warning Error.Error Module.Optimized

compile packageName isRoot canonicalImports interfaces source =
  do
      -- Parse the source code
      validModule <-
          Result.mapError Error.Syntax $
            Parse.program packageName isRoot (getOpTable interfaces) source

      -- Canonicalize all variables, pinning down where they came from.
      canonicalModule <-
          Canonicalize.module' canonicalImports interfaces validModule

      -- Run type inference on the program.
      (types, annots, patWarnings) <-
          Result.from Error.Type $
            TI.infer interfaces canonicalModule

      forM patWarnings $ \(r, w) -> Result.warn r w

      -- One last round of checks
      Result.mapError Error.Type $
        Nitpick.topLevelTypes types (Module.body validModule)

      tagDict <-
        Result.mapError Error.Pattern $
          Nitpick.patternMatches interfaces canonicalModule

      -- Add the real list of types
      let body =
            (Module.body canonicalModule) { Module.types = types, Module.annots = annots }

      -- Do some basic optimizations
      let optModule =
            Optimize.optimize tagDict (canonicalModule { Module.body = body })

      return optModule


getOpTable :: Module.Interfaces -> Parse.OpTable
getOpTable interfaces =
  Map.elems interfaces
    |> concatMap Module.iFixities
    |> map (\(assoc,lvl,op) -> (op,(lvl,assoc)))
    |> Map.fromList
