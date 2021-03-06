{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE OverloadedStrings #-}
module Reporting.Warning where

import Data.Aeson ((.=))
import qualified Data.Aeson as Json
import Text.PrettyPrint.ANSI.Leijen (text)

import qualified AST.Module.Name as ModuleName
import qualified AST.Type as Type
import qualified Reporting.Annotation as A
import qualified Reporting.Error.Helpers as Help
import qualified Reporting.Report as Report
import qualified Reporting.Render.Type as RenderType

import qualified Type.Effect.Common as Effect



-- ALL POSSIBLE WARNINGS


data Warning
    = UnusedImport ModuleName.Raw
    | MissingTypeAnnotation String Type.Canonical
    | MissingCase Effect.RealAnnot Effect.RealAnnot



-- TO REPORT


toReport :: RenderType.Localizer -> Warning -> Report.Report
toReport localizer warning =
  case warning of
    UnusedImport moduleName ->
        Report.report
          "unused import"
          Nothing
          ("Module `" ++ ModuleName.toString moduleName ++ "` is unused.")
          (text "Best to remove it. Don't save code quality for later!")

    MissingTypeAnnotation name inferredType ->
        Report.report
          "missing type annotation"
          Nothing
          ("Top-level value " ++ Help.functionName name ++ " does not have a type annotation.")
          ( Help.stack
              [ text "I inferred the type annotation so you can copy it into your code:"
              , RenderType.annotation localizer name inferredType
              ]
          )

    MissingCase theCase onesShouldMatch ->
        Report.report
          "unmatched case"
          Nothing
          ("The pattern " ++ Effect.prettyReal theCase ++ " is not matched by " ++ Effect.prettyReal onesShouldMatch)
          (text "TODO put a helpful hint here")



-- TO JSON


toJson :: RenderType.Localizer -> FilePath -> A.Located Warning -> Json.Value
toJson localizer filePath (A.A region warning) =
  let
    (maybeRegion, additionalFields) =
        Report.toJson [] (toReport localizer warning)
  in
      Json.object $
        [ "file" .= filePath
        , "region" .= maybe region id maybeRegion
        , "type" .= ("warning" :: String)
        ]
        ++ additionalFields
