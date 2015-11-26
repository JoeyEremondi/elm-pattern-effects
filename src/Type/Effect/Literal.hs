module Type.Effect.Literal where

import qualified AST.Literal as L
import qualified Reporting.Error.Type as Error
import qualified Reporting.Region as R
import qualified Type.Type as T
--import qualified Type.Environment as Env

import Type.Effect


constrain
    :: Environment
    -> R.Region
    -> L.Literal
    -> TypeAnnot
    -> IO AnnotConstr
constrain env region literal tipe =
  do  return (CEqual (error "TODO lit hint") region tipe $ OpenSet [(asString, [])])
  where
    prim name =
        return (getType env name)

    asString =
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
