module Type.Effect.Pattern where

import Control.Arrow (second)
import qualified Control.Monad as Monad
import qualified Data.Map as Map
import qualified Data.List as List

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
isWildcard _ = False

isTotal patList _ = --TODO check if all cases are exhaustive
  List.any isWildcard patList

patternLitAnnot :: Environment -> [P.CanonicalPattern]  -> RealAnnot
patternLitAnnot env patList =
  if (isTotal patList env)
  then RealTop
  else
    let
      dictAppend nm ann dict =
        case (Map.lookup nm dict) of
          Nothing -> Map.insert nm [ann] dict
          Just listSoFar -> Map.insert nm (ann:listSoFar) dict
      dictInit nm dict =
        case (Map.lookup nm dict) of
          Nothing -> Map.insert nm [] dict
          _ -> dict

      --Assumes our lists form a rectangular matrix
      transpose :: [[a]] -> [[a]]
      transpose [] = []
      transpose l = (map head l):(transpose $ map tail l)

      extendPatDict (A.A _ pat) dict = case pat of
        P.Anything -> error "Missed total case"
        P.Var _ -> error "Missed total case"
        P.Alias _ subPat -> extendPatDict subPat dict
        P.Literal lit -> dictInit (Literal.toCtorString lit) dict --We know there are never arguments to a literal
        P.Data name subPats -> dictAppend (V.toString name) subPats dict

      --Gives us a dict mapping strings to lists of lists patterns
      --We go through and convert our "list matrix" from horozontal to vertical
      -- i.e. instead of having a list of lists containing one pattern for each arg,
      --We have a list which, for each arg, contains a list of possible patterns
      --TODO does this lose precision?
      patternTree = List.foldr extendPatDict Map.empty patList
      tposedPatTree = Map.map transpose patternTree


    in RealAnnot $ Map.map (map $ patternLitAnnot env) tposedPatTree
