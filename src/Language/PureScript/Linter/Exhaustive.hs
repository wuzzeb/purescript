-----------------------------------------------------------------------------
--
-- Module      :  Language.PureScript.Exhaustive
-- Copyright   :  (c) 2013-14 Phil Freeman, (c) 2014 Gary Burgess, and other contributors
-- License     :  MIT
--
-- Maintainer  :  Phil Freeman <paf31@cantab.net>
-- Stability   :  experimental
-- Portability :
--
-- |
-- | Module for exhaustivity checking over pattern matching definitions
-- | The algorithm analyses the clauses of a definition one by one from top
-- | to bottom, where in each step it has the cases already missing (uncovered),
-- | and it generates the new set of missing cases.
-- 
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.PureScript.Linter.Exhaustive 
  ( checkExhaustive
  , checkExhaustiveModule
  ) where

import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import Data.List (foldl', sortBy, nub)
import Data.Function (on)

import Control.Monad (unless)
import Control.Applicative
import Control.Monad.Writer.Class

import Language.PureScript.AST.Binders
import Language.PureScript.AST.Declarations
import Language.PureScript.Environment
import Language.PureScript.Names as P
import Language.PureScript.Kinds
import Language.PureScript.Types as P
import Language.PureScript.Errors

import Language.PureScript.AST.Traversals (everywhereOnValuesTopDownM)

-- |
-- Qualifies a propername from a given qualified propername and a default module name
--
qualifyName :: a -> ModuleName -> Qualified a -> Qualified a
qualifyName n defmn qn = Qualified (Just mn) n
  where
  (mn, _) = qualify defmn qn

-- |
-- Given an environment and a datatype or newtype name,
-- this function returns the associated data constructors if it is the case of a datatype
-- where: - ProperName is the name of the constructor (for example, "Nothing" in Maybe)
--        - [Type] is the list of arguments, if it has (for example, "Just" has [TypeVar "a"])
--
getConstructors :: Environment -> ModuleName -> (Qualified ProperName) -> [(ProperName, [Type])]
getConstructors env defmn n = extractConstructors lnte
  where
  qpn :: Qualified ProperName
  qpn = getConsDataName n

  getConsDataName :: (Qualified ProperName) -> (Qualified ProperName)
  getConsDataName con = qualifyName nm defmn con
    where
    nm = case getConsInfo con of
           Nothing -> error $ "ProperName " ++ show con ++ " not in the scope of the current environment in getConsDataName."
           Just (_, pm, _, _) -> pm

  getConsInfo :: (Qualified ProperName) -> Maybe (DataDeclType, ProperName, Type, [Ident])
  getConsInfo con = M.lookup con dce
    where
    dce :: M.Map (Qualified ProperName) (DataDeclType, ProperName, Type, [Ident])
    dce = dataConstructors env

  lnte :: Maybe (Kind, TypeKind)
  lnte = M.lookup qpn (types env)

  extractConstructors :: Maybe (Kind, TypeKind) -> [(ProperName, [Type])]
  extractConstructors (Just (_, DataType _ pt)) = pt
  extractConstructors _ = error "Data name not in the scope of the current environment in extractConstructors"

-- |
-- Replicates a wildcard binder
--
initialize :: Int -> [Binder]
initialize l = replicate l NullBinder

-- |
-- Applies a function over two lists of tuples that may lack elements
--
genericMerge :: Ord a =>
  (a -> Maybe b -> Maybe c -> d) ->
  [(a, b)] ->
  [(a, c)] ->
  [d]
genericMerge _ [] [] = []
genericMerge f bs [] = map (\(s, b) -> f s (Just b) Nothing) bs
genericMerge f [] bs = map (\(s, b) -> f s Nothing (Just b)) bs
genericMerge f bsl@((s, b):bs) bsr@((s', b'):bs')
  | s < s' = (f s (Just b) Nothing) : genericMerge f bs bsr
  | s > s' = (f s' Nothing (Just b')) : genericMerge f bsl bs'
  | otherwise = (f s (Just b) (Just b')) : genericMerge f bs bs'

-- |
-- Find the uncovered set between two binders:
-- the first binder is the case we are trying to cover the second one is the matching binder
--
missingCasesSingle :: Environment -> ModuleName -> Binder -> Binder -> [Binder]
missingCasesSingle _ _ _ NullBinder = []
missingCasesSingle _ _ _ (VarBinder _) = []
missingCasesSingle env mn (VarBinder _) b = missingCasesSingle env mn NullBinder b
missingCasesSingle env mn br (NamedBinder _ bl) = missingCasesSingle env mn br bl
missingCasesSingle env mn NullBinder cb@(ConstructorBinder con _) =
  concatMap (\cp -> missingCasesSingle env mn cp cb) allPatterns
  where
  allPatterns = map (\(p, t) -> ConstructorBinder (qualifyName p mn con) (initialize $ length t))
                  $ getConstructors env mn con
missingCasesSingle env mn cb@(ConstructorBinder con bs) (ConstructorBinder con' bs')
  | con == con' = map (ConstructorBinder con) (missingCasesMultiple env mn bs bs')
  | otherwise = [cb]
missingCasesSingle _ _ NullBinder (ArrayBinder bs)
  | null bs = [] 
  | otherwise = []
missingCasesSingle env mn NullBinder (ObjectBinder bs) =
  map (ObjectBinder . zip (map fst bs)) allMisses
  where
  allMisses = missingCasesMultiple env mn (initialize $ length bs) (map snd bs)
missingCasesSingle env mn (ObjectBinder bs) (ObjectBinder bs') =
  map (ObjectBinder . zip sortedNames) $ uncurry (missingCasesMultiple env mn) (unzip binders)
  where
  sortNames = sortBy (compare `on` fst)

  (sbs, sbs') = (sortNames bs, sortNames bs')

  compB :: a -> Maybe a -> Maybe a -> (a, a)
  compB e b b' = (fm b, fm b')
    where
    fm = fromMaybe e

  compBS :: Eq a => b -> a -> Maybe b -> Maybe b -> (a, (b, b))
  compBS e s b b' = (s, compB e b b')

  (sortedNames, binders) = unzip $ genericMerge (compBS NullBinder) sbs sbs'
missingCasesSingle _ _ NullBinder (BooleanBinder b) = [BooleanBinder $ not b]
missingCasesSingle _ _ (BooleanBinder bl) (BooleanBinder br)
  | bl == br = []
  | otherwise = [BooleanBinder bl]
missingCasesSingle env mn b (PositionedBinder _ _ cb) = missingCasesSingle env mn b cb
missingCasesSingle _ _ b _ = [b]

-- |
-- Returns the uncovered set of binders
-- the first argument is the list of uncovered binders at step i
-- the second argument is the (i+1)th clause of a pattern matching definition
--
-- The idea of the algorithm is as follows:
-- it processes each binder of the two lists (say, `x` and `y`) one by one
-- at each step two cases arises:
--   - there are no missing cases between `x` and `y`: this is very straightforward, it continues with the remaining cases
--       but keeps the uncovered binder in its position.
--   - there are missing cases, let us call it the set `U`: on the one hand, we mix each new uncovered case in `U`
--       with the current tail of uncovered set. On the other hand, it continues with the remaining cases: here we
--       can use `x` (but it will generate overlapping cases), or `y`, which will generate non-overlapping cases.
--
--     As an example, consider:
--
--       data N = Z | S N
--       f Z Z = Z   --> {[S _, _], [Z, S _]} which are the right non-overlapping cases (GHC uses this).
--
--       if we use `x` instead of `y` (in this case, `y` stands for `Z` and `x` for `_`) we obtain:
--       f Z Z = Z   --> {[S _, _], [_, S _]} you can see that both cases overlaps each other.
--
--       Up to now, we've decided to use `x` just because we expect to generate uncovered cases which might be
--       redundant or not, but uncovered at least. If we use `y` instead, we'll need to have a redundancy checker
--       (which ought to be available soon), or increase the complexity of the algorithm.
--
missingCasesMultiple :: Environment -> ModuleName -> [Binder] -> [Binder] -> [[Binder]]
missingCasesMultiple env mn = go
  where
  go [] _ = []
  go (x:xs) (y:ys)
    | null miss = map (x :) (go xs ys)
    | otherwise = map (: xs) miss ++ map (x :) (go xs ys)
    where
    miss = missingCasesSingle env mn x y
  go _ _ = error "Argument lengths did not match in missingCasesMultiple."

-- |
-- Guard handling
--
-- We say a guard is exhaustive iff it has an `otherwise` (or `true`) expression.
-- Example:
--   f x | x < 0 = 0
--       | otherwise = 1
--   is exhaustive, whereas `f x | x < 0` is not
--
-- The function below say whether or not a guard has an `otherwise` expression
-- It is considered that `otherwise` is defined in Prelude
--
isExhaustiveGuard :: Either [(Guard, Expr)] Expr -> Bool
isExhaustiveGuard (Left gs) = not . null $ filter (\(g, _) -> isOtherwise g) gs
  where
  isOtherwise :: Expr -> Bool
  isOtherwise (TypedValue _ (BooleanLiteral True) _) = True
  isOtherwise (TypedValue _ (Var (Qualified (Just (ModuleName [ProperName "Prelude"])) (Ident "otherwise"))) _) = True
  isOtherwise _ = False
isExhaustiveGuard (Right _) = True 

-- |
-- Returns the uncovered set of case alternatives
--
missingCases :: Environment -> ModuleName -> [Binder] -> CaseAlternative -> [[Binder]]
missingCases env mn uncovered ca = missingCasesMultiple env mn uncovered (caseAlternativeBinders ca)

missingAlternative :: Environment -> ModuleName -> CaseAlternative -> [Binder] -> [[Binder]]
missingAlternative env mn ca uncovered
  | isExhaustiveGuard (caseAlternativeResult ca) = missingCases env mn uncovered ca
  | otherwise = [uncovered]

-- |
-- Main exhaustivity checking function
-- Starting with the set `uncovered = { _ }` (nothing covered, one `_` for each function argument),
-- it partitions that set with the new uncovered cases, until it consumes the whole set of clauses.
-- Then, returns the uncovered set of case alternatives.
-- 
checkExhaustive :: forall m. (MonadWriter MultipleErrors m) => Environment -> ModuleName -> [CaseAlternative] -> m ()
checkExhaustive env mn cas = makeResult . nub $ foldl' step [initial] cas
  where
  step :: [[Binder]] -> CaseAlternative -> [[Binder]]
  step uncovered ca = concatMap (missingAlternative env mn ca) uncovered

  initial :: [Binder]
  initial = initialize numArgs
    where
    numArgs = length . caseAlternativeBinders . head $ cas 

  makeResult :: [[Binder]] -> m ()
  makeResult bss = unless (null bss) tellWarning 
    where
    tellWarning = tell . errorMessage $ NotExhaustivePattern bss

-- |
-- Exhaustivity checking over a list of declarations
-- 
checkExhaustiveDecls :: forall m. (Applicative m, MonadWriter MultipleErrors m) => Environment -> ModuleName -> [Declaration] -> m ()
checkExhaustiveDecls env mn ds =
  let (f, _, _) = everywhereOnValuesTopDownM return checkExpr return

      f' :: Declaration -> m Declaration
      f' d@(BindingGroupDeclaration bs) = mapM_ (f' . convert) bs >> return d
        where
        convert :: (Ident, NameKind, Expr) -> Declaration
        convert (name, nk, e) = ValueDeclaration name nk [] (Right e)
      f' d@(ValueDeclaration name _ _ _) = censor (onErrorMessages (ErrorInValueDeclaration name)) $ f d
      f' (PositionedDeclaration pos com dec) = PositionedDeclaration pos com <$> censor (onErrorMessages (PositionedError pos)) (f' dec)
      -- Don't generate two warnings for desugared dictionaries.
      f' d@TypeInstanceDeclaration{} = return d
      f' d = f d

  in mapM_ f' ds
  where
  checkExpr :: Expr -> m Expr
  checkExpr c@(Case _ cas)  = checkExhaustive env mn cas >> return c
  checkExpr other = return other

-- |
-- Exhaustivity checking over a single module
-- 
checkExhaustiveModule :: forall m. (Applicative m, MonadWriter MultipleErrors m) => Environment -> Module -> m ()
checkExhaustiveModule env (Module _ mn ds _) = censor (onErrorMessages (ErrorInModule mn)) $ checkExhaustiveDecls env mn ds

