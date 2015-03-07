-----------------------------------------------------------------------------
--
-- Module      :  Language.PureScript.CoreFn.Evaluator 
-- Copyright   :  (c) 2013-15 Phil Freeman, (c) 2014 Gary Burgess, and other contributors
-- License     :  MIT
--
-- Maintainer  :  Phil Freeman <paf31@cantab.net>
-- Stability   :  experimental
-- Portability :
--
-- |
-- A (partial) evaluator for the core functional representation.
--
-----------------------------------------------------------------------------

{-# LANGUAGE RecordWildCards #-}

module Language.PureScript.CoreFn.Evaluator 
  ( Value(..)
  , EvalError(..)
  , evalModule
  , eval
  ) where
    
import Data.Monoid
import Data.Foldable (fold)   
import Data.Traversable (traverse)    
    
import Control.Monad (foldM, zipWithM)
import Control.Monad.Fix (mfix)
import Control.Applicative

import Language.PureScript.Names
import Language.PureScript.Traversals
    
import Language.PureScript.CoreFn.Expr
import Language.PureScript.CoreFn.Binders
import Language.PureScript.CoreFn.Literals
import Language.PureScript.CoreFn.Module
import Language.PureScript.CoreFn.Traversals

-- | A runtime value for the evaluator
--
data Value a
  = LiteralValue (Literal (Value a))
  | Tagged (Qualified ProperName) [Value a]
  | Closure (Environment a) Ident (Expr a)
  deriving (Show)
  
type Environment a = [(Qualified Ident, Value a)]

data EvalError
  = TypeMismatch String
  | ValueIsUndefined (Qualified Ident)
  | PropertyIsMissing String
  | FailedPatternMatch
  | NotSupported
  
instance Show EvalError where
  show (TypeMismatch ty) = "Type mismatch - expected value of type " ++ show ty ++ "."
  show (ValueIsUndefined ident) = "Value " ++ show ident ++ " is undefined."
  show (PropertyIsMissing prop) = "Property " ++ show prop ++ " is not present on object."
  show FailedPatternMatch = "Failed pattern match"
  show NotSupported = "Evaluation is not supported for this type of expression."

evalModule :: Module () -> Either EvalError (Environment ())
evalModule Module{..} = foldM (evalDecl moduleName) [] moduleDecls

evalDecl :: ModuleName -> Environment () -> Bind () -> Either EvalError (Environment ())
evalDecl mn e (NonRec name expr) = do
  val <- eval mn e expr
  return [(Qualified (Just mn) name, val)]
evalDecl mn e (Rec ds) = do
  e' <- mfix $ \e' -> do
    vs <- traverse (eval mn e' . snd) ds
    return $ zipWith (\(name, _) val -> (Qualified (Just mn) name, val)) ds vs
  return $ e' ++ e

eval :: ModuleName -> Environment () -> Expr () -> Either EvalError (Value ())
eval mn = go
  where
  go :: Environment () -> Expr () -> Either EvalError (Value ())
  go e (Literal _ lit) = LiteralValue <$> traverse (go e) lit
  go e (Accessor _ prop o) = do
    v <- go e o
    case v of
      LiteralValue (ObjectLiteral props) -> 
        case prop `lookup` props of
          Just val -> Right val
          Nothing -> Left (PropertyIsMissing prop)
      _ -> Left (TypeMismatch "object")
  go e (ObjectUpdate _ o props) = do
    v <- go e o
    case v of 
      LiteralValue (ObjectLiteral props') -> do
        vs <- mapM (sndM (go e)) props
        return $ LiteralValue (ObjectLiteral (vs ++ props'))
      _ -> Left (TypeMismatch "object")
  go e (Abs _ name body) = Right (Closure e name body)
  go e (App _ lhs rhs) = do
    f <- go e lhs
    case f of 
      Closure e' name body -> go e' (subst name rhs body)
      _ -> Left (TypeMismatch "function")
  go e (Var _ name) =
    case name `lookup` e of
      Nothing -> Left (ValueIsUndefined name)
      Just v -> Right v
  go e (Case _ es alts) = do
    vs <- mapM (go e) es
    matches <- mapM (evalAlt mn e vs) alts
    case getFirst $ fold (map First matches) of
      Nothing -> Left FailedPatternMatch
      Just v -> Right v
  go e (Let _ ds body) = do
    e' <- foldM (evalDecl mn) e ds
    go e' body
  go _ _ = Left NotSupported

-- | Evaluate a case alternative
-- | Nothing means a pattern failed to match, Just means all patterns matched
evalAlt :: ModuleName -> Environment () -> [Value ()] -> CaseAlternative () -> Either EvalError (Maybe (Value ()))
evalAlt mn e vs CaseAlternative{..} = do
  let ms = zipWithM evalPattern caseAlternativeBinders vs
  error "Not implemented yet"
  where
  evalPattern :: Binder () -> Value () -> Maybe [(Ident, Value ())]
  evalPattern (NullBinder _) _ = Just []
  evalPattern (VarBinder _ name) v = Just [(name, v)]
  evalPattern (LiteralBinder _ bs) (LiteralValue vs') = go bs vs'
    where
    go :: Literal a -> Literal b -> Maybe [(Ident, Value ())]
    go = error "Not implemented yet"
  evalPattern (ConstructorBinder _ _ name bs) (Tagged name' vs') | name == name' = do
    ms <- zipWithM evalPattern bs vs'
    return $ concat ms
  evalPattern (NamedBinder _ name b) v = do
    ms <- evalPattern b v
    return $ (name, v) : ms
  evalPattern _ _ = Nothing

-- | Assumes no shadowing, so it is necessary to run the renamer before evaluation
subst :: Ident -> Expr a -> Expr a -> Expr a
subst name repl = let (_, f', _) = everywhereOnValues id f id in f'
  where
  f (Var _ (Qualified Nothing name')) | name == name' = repl
  f other = other

ext :: Qualified Ident -> Value a -> Environment a -> Environment a
ext name e = ((name, e) :)