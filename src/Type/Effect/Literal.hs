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
  do  definiteType <- litType
      return (CEqual (error "TODO") region tipe $ OpenSet [(asString, [])])
  where
    prim name =
        return (getType env name)

    (name, litType, asString) =
        case literal of
          L.IntNum i ->
              ( "number"
              , T.VarN <$> T.mkVar (Just T.Number)
              , show i
              )

          L.FloatNum f ->
              ( "float"
              , prim "Float"
              , show f
              )

          L.Chr c ->
              ( "character"
              , prim "Char"
              , show c
              )

          L.Str _ ->
              ( "string"
              , prim "String"
              , error "TODO string as list"
              )

          L.Boolean b ->
              ( "boolean"
              , prim "Bool"
              , show b
              )
