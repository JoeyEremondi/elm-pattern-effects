module Type.Effect.Literal where

import qualified AST.Literal as L
import qualified Reporting.Region as R
--import qualified Type.Environment as Env

import Type.Effect


constrain
    :: Environment
    -> R.Region
    -> L.Literal
    -> TypeAnnot
    -> IO AnnotConstr
constrain _ region literal tipe =
  return (CEqual region tipe $ PatternSet [(toCtorString literal, [])] )




toCtorString :: L.Literal -> String
toCtorString literal =
      case literal of
        L.IntNum i ->
            ( show i
            )

        L.FloatNum f ->
            (show f
            )

        L.Chr c ->
            ( show c
            )

        L.Str s ->
            ( "\"" ++ s ++ "\""
            )

        L.Boolean b ->
            ( show b
            )
