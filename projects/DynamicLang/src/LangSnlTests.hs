-- Type inference works great for these terms.
module LangSnlTests where

import Test.HUnit
import DataDynamic
import LangSnl

-- De Brujin indices to play with
zero = Var Z
one = Var (S Z)
two = Var (S (S Z))

-- | No more dynamic needed B)
id :: LangSnl l (a -> a)
id = Lam zero

plusOne :: LangSnl l (Integer -> Integer)
plusOne = Lam (zero + 1)

-- | Hmmm... It's typed, so we get an infinite type error now. Not
-- | sure how to type the y combinator now. TODO.
--yComb = Lam (g :@  g)
--  where g = Lam (one :@ (zero :@ zero))

dynFun :: LangSnl l (Dynamic -> Integer)
dynFun = Lam (Bin Plus (From zero) 3)

-- It works with the minimal number of dynamic checks required!
appDynFun :: LangSnl l Integer
appDynFun = dynFun :@ (To (Lit (3 :: Integer)))
