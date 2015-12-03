module Type.Effect.Pattern where

import Control.Arrow (second)
import qualified Control.Monad as Monad
import qualified Data.Map as Map
import qualified Data.List as List
import qualified Data.Set as Set

import qualified AST.Pattern as P
import qualified AST.Variable as V
import qualified Reporting.Annotation as A
import qualified Type.Effect.Literal as Literal
--import qualified Type.Environment as Env


import Type.Effect

constrain
    :: Environment
    -> P.CanonicalPattern
    -> TypeAnnot
    -> IO AnnFragment
constrain env (A.A region pattern) tipe =
  let
    equal leftType rightType =
      CEqual region leftType rightType

    rvar v =
      A.A region (VarAnnot v)
  in
  case pattern of
    P.Anything ->
        --TODO wildcard as top?
        return emptyFragment

    P.Literal lit ->
        do  c <- Literal.constrain env region lit tipe
            return $ emptyFragment { typeConstraint = c }

    P.Var name ->
        --TODO variables top?
        do  variable <- mkVar
            return $ Fragment
                { typeEnv = Map.singleton name (rvar variable)
                , vars = [variable]
                , typeConstraint =
                    equal (VarAnnot variable) tipe
                }

    P.Alias name p ->
        do  variable <- mkVar
            fragment <- constrain env p tipe
            return $ fragment
              { typeEnv = Map.insert name (rvar variable) (typeEnv fragment)
              , vars = variable : vars fragment
              , typeConstraint =
                  equal (VarAnnot variable) tipe
                  /\ typeConstraint fragment
              }

    P.Data name patterns ->
        do  let stringName = V.toString name

            (_kind, cvars, args, result) <-
                freshDataScheme env stringName

            fragList <- Monad.zipWithM (constrain env) patterns args
            let fragment = joinFragments fragList
            return $ fragment
                { vars = cvars ++ vars fragment
                , typeConstraint =
                    typeConstraint fragment
                    /\ equal tipe result
                }

    P.Record fields ->
        do  pairs <-
                mapM (\name -> (,) name <$> mkVar) fields

            let tenv =
                  Map.fromList (map (second rvar) pairs)

            let unannotatedTenv =
                  Map.map A.drop tenv

            con <- return CTrue -- exists $ \t ->
              --return $ error "TODO record case" -- (equal Error.PRecord tipe (record unannotatedTenv t))

            return $ Fragment
                { typeEnv = tenv
                , vars = map snd pairs
                , typeConstraint = con
                }

isWildcard (A.A _ P.Anything) = True
isWildcard (A.A _ (P.Var _)) = True
isWildcard (A.A _ (P.Record _)) = True --TODO remove
isWildcard _ = False

isTotal patList _ = --TODO check if all cases are exhaustive
  List.any isWildcard patList

requiredMatches = patternListToAnnot RealTop
possibleMatches = patternListToAnnot realBottom

patternToAnnot :: RealAnnot -> Environment -> P.CanonicalPattern -> (String, [RealAnnot])
patternToAnnot varCase env (A.A reg pat) = case pat of
  P.Anything -> error "Should have filtered out top"
  P.Var _ -> error "Should have filtered out top"
  P.Record fields -> error "TODO record patterns"
  P.Alias _ p1 -> patternToAnnot varCase env p1
  P.Literal l -> (Literal.toCtorString l, [])
  P.Data s args -> (V.toString s, map (\x -> patternListToAnnot varCase env [x]) args)


patternListToAnnot :: RealAnnot -> Environment -> [P.CanonicalPattern] -> RealAnnot
patternListToAnnot varCase env patList =
  if (isTotal patList env)
  then varCase
  else
    --TODO faster way, always sets?
    RealAnnot $ Set.fromList $ List.map (patternToAnnot varCase env) patList
