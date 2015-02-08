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

module Language.PureScript.CoreFn.Evaluator 
  ( Value(..)
  , EvalError(..)
  , eval
  ) where
    
import Data.Traversable (traverse)    

import Control.Applicative

import Language.PureScript.Names
import Language.PureScript.Traversals
    
import Language.PureScript.CoreFn.Expr
import Language.PureScript.CoreFn.Literals
import Language.PureScript.CoreFn.Traversals

-- | A runtime value for the evaluator
--
data Value a
  = LiteralValue (Literal (Value a))
  | Tagged ProperName [Value a]
  | Closure (Environment a) Ident (Expr a)
  deriving (Show)
  
type Environment a = [(Ident, Value a)]

data EvalError
  = TypeMismatch String
  | ValueIsUndefined Ident
  | PropertyIsMissing String
  | NotSupported
  
instance Show EvalError where
  show (TypeMismatch ty) = "Type mismatch - expected value of type " ++ show ty ++ "."
  show (ValueIsUndefined ident) = "Value " ++ show ident ++ " is undefined."
  show (PropertyIsMissing prop) = "Property " ++ show prop ++ " is not present on object."
  show NotSupported = "Evaluation is not supported for this type of expression."

eval :: Environment a -> Expr a -> Either EvalError (Value a)
eval e (Literal _ lit) = LiteralValue <$> traverse (eval e) lit
eval e (Constructor _ _ tag n) = Left NotSupported
eval e (Accessor _ prop o) = do
  v <- eval e o
  case v of
    LiteralValue (ObjectLiteral props) -> 
      case prop `lookup` props of
        Just val -> Right val
        Nothing -> Left (PropertyIsMissing prop)
    _ -> Left (TypeMismatch "object")
eval e (ObjectUpdate _ o props) = do
  v <- eval e o
  case v of 
    LiteralValue (ObjectLiteral props') -> do
      vs <- mapM (sndM (eval e)) props
      return $ LiteralValue (ObjectLiteral (vs ++ props'))
    _ -> Left (TypeMismatch "object")
eval e (Abs _ name body) = Right (Closure e name body)
eval e (App _ lhs rhs) = do
  f <- eval e lhs
  case f of 
    Closure e' name body -> eval e' (subst name rhs body)
    _ -> Left (TypeMismatch "function")
eval e (Var _ (Qualified Nothing name)) =
  case name `lookup` e of
    Nothing -> Left (ValueIsUndefined name)
    Just v -> Right v
eval _ (Case _ vals alts) = Left NotSupported
eval _ (Let _ binders body) = Left NotSupported
eval _ _ = Left NotSupported

-- | Assumes no shadowing, so it is necessary to run the renamer before evaluation
subst :: Ident -> Expr a -> Expr a -> Expr a
subst name repl = let (_, f', _) = everywhereOnValues id f id in f'
  where
  f (Var _ (Qualified Nothing name')) | name == name' = repl
  f other = other

ext :: Ident -> Value a -> Environment a -> Environment a
ext name e = ((name, e) :)