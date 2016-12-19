{-# LANGUAGE GADTs, TypeOperators, DataKinds, FlexibleInstances #-}
-- | This module implements a version of the static lang implemented using
-- a nameless representation allowing De Brujin indices to stand in place of
-- variables. This allows us to keep track of the types of variables, functions,
-- and applications using an indexed type list.
-- I use these declarations, but I actually don't understand *why* it works.
-- This code is basically type magic :O
module LangSnl where

import DataDynamic
import DataTypeable hiding (App)
import Common(LangType, gFromDynamic)
import Data.Maybe(fromMaybe)

-- Notice the 'a' type variable remains the same. Meanwhile l represents a list of types.
-- As we build constant applications of (S ... (S (...))) this is reflected in the type
-- of our Index. That is, as we apply S to some (Index b a) we cons 'c' with 'b'.
-- Therefore when we use our Index in the `look` function, the l in "HList l" must match
-- the l in "Index l a", that is, the types must be the same.
-- I *think* the reason Z has (a ': b) is so that this type can "grow" to fit when we
-- are accessing lists of longer lengths. Say, the first element in a list of lenght 10.
data Index l a where
  Z :: Index (a ': b) a
  S :: Index b a -> Index (c : b) a

-- Heterogenous list. We keep track of the type of the elements with (a ': b),
-- a list of types.
data HList a where
  HNil :: HList '[]
  HCons :: a -> HList b -> HList (a ': b)

-- Recurse down a HList based on an Index and return the nth
-- element of HList. Notice the type guarantees no out of bounds accesses.
look :: HList l -> Index l a -> a
look (HCons x _) Z = x
look (HCons _ y) (S n) = look y n

-- Uses De Bruijn indices to represent variables.
-- l is a list of types, and the Index structure above selects a type from that list.
-- "Lang Static Nameless".
data LangSnl l a where
  -- Lambdas take a body with a bound variable of type `a` and return a function
  -- from a -> b.
  Lam :: LangSnl (a : l) b -> LangSnl l (a -> b)
  -- Given two expressions, apply the first to the second, this declaration
  -- enforces proper types :O
  (:@) :: LangSnl l (a -> b) -> LangSnl l a -> LangSnl l b
  Bin ::  BinT a b c -> LangSnl l a -> LangSnl l b -> LangSnl l c
  Uni :: UniT a b -> LangSnl l b
  Lit :: a -> LangSnl l a
  -- Variables are represented as De Brujin indices.
  Var :: Index l a -> LangSnl l a
  If  :: LangSnl l Bool -> LangSnl l a -> LangSnl l a -> LangSnl l a
  From :: Typeable a => LangSnl l Dynamic -> LangSnl l a
  To :: Typeable a => LangSnl l a -> LangSnl l Dynamic

-- | Types for our binary expressions.
-- Given operands of type 'a' and 'b', the operation will return a variable of
-- type 'c'.
-- (I had no idea you could do this!?)
data BinT a b c where
  Plus   :: BinT Integer Integer Integer
  Minus  :: BinT Integer Integer Integer
  Mult   :: BinT Integer Integer Integer
  And    :: BinT Bool Bool Bool
  Or     :: BinT Bool Bool Bool
  EqInt  :: BinT Integer Integer Bool
  EqBool :: BinT Bool Bool Bool
  EqDyn  :: BinT Dynamic Dynamic Bool

-- | Types for our binary expressions.
-- | Given operand of type a, the operation will return a variable of type b.
data UniT a b where
  Not :: UniT Bool Bool
  -- Implement operators for tuples and lists.

-- | Convenience instance.
instance Num (LangSnl l Integer) where
  (+) = Bin Plus
  (-) = Bin Minus
  (*) = Bin Mult
  abs = error "not used"
  signum = error "signum"
  fromInteger = Lit . fromInteger

-- Evaluation function for our language. It just works?! I'm amazed :D
eval :: HList l -> LangSnl l a -> a
eval env (Lam e) = \y -> eval (HCons y env) e
eval env (e1 :@ e2) = (eval env e1) (eval env e2)
eval env (Lit a) = a
eval env (Bin op e1 e2) = (mapOp op) (eval env e1) (eval env e2)
eval env (Var x) = look env x
eval env (If cond e1 e2) = if (eval env cond) then (eval env e1) else (eval env e2)
eval env (From e) = gFromDynamic (eval env e)
eval env (To e) = toDynamic (eval env e)

mapOp :: BinT a b c -> a -> b -> c
mapOp Plus   = (+)
mapOp Mult  = (*)
mapOp Minus  = (-)
mapOp EqInt  = (==)
mapOp EqBool = (==)
-- Dynamic has eq instance.
mapOp EqDyn = \ x x' -> x == x'
