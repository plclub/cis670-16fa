{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes, GADTs #-}
-- This module requires GHC 8 to compile.
module Lang where

import Common
import DataDynamic
-- | This module defines a simple untyped language using the Dynamic module.

-- =======================================================================================
-- Simple untyped language.

data Exp where
  Lam  :: String -> Exp -> Exp     -- ^ Function abstraction as \x . e
  (:@) :: Exp -> Exp -> Exp        -- ^ Function application (e1 e2)
  Bin  :: BinOp -> Exp -> Exp -> Exp  -- ^ Binary operator.
  Uni  :: UniOp -> Exp -> Exp
  Lit  :: forall t. (LangType t) => t -> Exp  -- ^ literal.
  Var  :: String -> Exp            -- ^ Variable.
  If   :: Exp -> Exp -> Exp -> Exp -- ^ Conditional branching.
  Nill :: Exp                      -- ^ lists.
  -- Notice we can use Haskell's let and where syntax to define expressions.

-- Useful for debugging and simple viewing.
instance Show Exp where
  show (Lam str e) = "(Lam " ++ str ++ " " ++ show e ++ ")"
  show (e1 :@ e2)  = "(" ++ show e1 ++ " @ " ++ show e2 ++ ")"
  show (Bin op e1 e2) = "(" ++ show op ++ " " ++ show e1 ++ " " ++ show e2 ++ ")"
  show (Uni op e) = "(" ++ show op ++ " " ++ show e ++ ")"
  show (Lit x) = "Lit " ++ show x
  show (Var x) = "(Var " ++ x ++ ")"
  show (If e1 e2 e3) = "(If " ++ show e1 ++ " " ++ show e2 ++ " " ++ show e3 ++ ")"
  show Nill = "[]"


-- No alpha equivalance here :/
instance Eq Exp where
  Lam s e == Lam s' e' = s == s' && e == e'
  e1 :@ e2 == e1' :@ e2' = e1 == e1' && e2 == e2'
  Bin op e1 e2 ==  Bin op' e1' e2' = op == op' && e1 == e1' && e2 == e2'
  Uni op e == Uni op' e' = op == op' && e == e'
  -- There has to be a better way to do this?
  Lit x == Lit x' = toDynamic x == toDynamic x'
  Var s == Var s' = s == s'
  If e1 e2 e3 == If e1' e2' e3' = e1 == e1' && e2 == e2' && e3 == e3'
  Nill == Nill = True
  _ == _ = False
-- =======================================================================================

