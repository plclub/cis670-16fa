{-# LANGUAGE RebindableSyntax #-}
module StaticLangTests where

import qualified Prelude as P
import Prelude hiding (Num(..))
-- Haskell is unable to derive the type of of (Lit 3) as it is polymorphic through the
-- Num typeclass. So instead of writing (Lit (3 :: Int)) I prefer using the
-- RebindableSyntax extension.

import Test.HUnit
import StaticLang
import DataTypeable
import StaticEval
import DataDynamic
import qualified Common as C

fromInteger :: Integer -> Integer
fromInteger = id

-- Define a couple variables to play with.
x = Var "x"
y = Var "y"
z = Var "z"
f = Var "f"
n = Var "n"
i = Var "i"

fact = Var "fact"
zero = Lit 0
one = Lit 1

sLam :: StaticExp (Dynamic -> Dynamic)
sLam = Lam "x" x

plusOne :: StaticExp (Dynamic -> Integer)
plusOne = Lam "x" (BinInt Plus (Lit 1) (From x))

yComb :: StaticExp (Dynamic -> Dynamic)
yComb = Lam "f" (g :@ To g)
   where
     g :: StaticExp (Dynamic -> Dynamic) -- Not needed B)
     g = Lam "x" (From f :@ (From x :@ x))

sFact :: StaticExp Dynamic
sFact = yComb :@ To
   (Lam "f"
      (To (Lam "x"
        (To (If (BinEq x (To (Lit 0)))
             (Lit 1)
             (BinInt Mult (From x) (From (From f :@ To (BinInt Minus (From x) (Lit 1))))))))))

-- | Function to compute sum([1..i]).
sSumI :: StaticExp Dynamic
sSumI = yComb :@ To (Lam "f"
          (To (Lam "x"
               (If (BinEq x (To (Lit 0)))
                (Lit 0)
                (BinInt Plus (From x) (From f :@ (To (BinInt Minus (From x) (Lit 1)))))))))

sSumI5 :: StaticExp Integer
sSumI5 = (From sSumI :@ (To (Lit 5)))

-- | More optimized version of fact5
-- | Observation: if our function is not made to return a Dynamic then we
-- | can entirely omit a call to From.
sFact' :: StaticExp Dynamic
sFact' = yComb :@ To (Lam "fact"
           (To (Lam "x"
                  (If (BinEq x (To (Lit 0)))
                   (Lit 1)
                    (BinInt Mult (From x) (From fact :@ To (BinInt Minus (From x) (Lit 1))))
                    ))))

sFact5' :: StaticExp Integer
sFact5' = From sFact' :@ To (Lit 5)


-- Static Language tests. Make sure our evaluator behaves like we expect it to!
tests = TestList
  [
    "language literals" ~:
      5 ~=? sEval (Lit 5),

    "language literals" ~:
      True ~=? sEval (Lit True),
    "language literals" ~:
      "hello world!" ~=? sEval (Lit "hello world!"),

    -- "language literals" ~:
    --   (1,2) ~=? sEval (Lit (1, 2)),

    "simple ints" ~:
      10 ~=? sEval (BinInt Plus (Lit 5) (Lit 5)),
    "simple ints" ~:
      18 ~=? sEval (BinInt Plus (Lit 6) (BinInt Mult (Lit 3) (Lit 4))),

    "simple bools" ~:
      False ~=? sEval (BinBool And (Lit True) (Lit False)),
    "simple bools" ~:
      True ~=? sEval (BinBool Or (Lit True) (Lit False)),

    "int comparison" ~:
      True ~=? sEval (BinIntBool Lte (Lit 1) (Lit 3)),

    -- For now...
    "int eq" ~:
      True ~=? sEval (BinEq  (To (Lit 1)) (To (Lit 1))),

    "conditional tests" ~:
       1 ~=? sEval (If (Lit True) (Lit 1) (Lit 2)),
    "conditional tests" ~:
       2 ~=? sEval (If (Lit False) (Lit 1) (Lit 2)),
    "conditional tests" ~:
       2 ~=? sEval (If (UniNot (BinEq (To (Lit 0)) (To (Lit 0)))) (Lit 1) (Lit 2)),
    "conditional tests" ~:
       True ~=? sEval (If (BinIntBool Lte (Lit 10) (Lit 20)) (Lit True) (Lit False)),

    "lambda tests" ~:
       5 ~=? sEval (From (sLam :@ (To (Lit 5)))),
     "lambda tests" ~:
       10 ~=? sEval (BinInt Plus (Lit 5) (From (sLam :@ (To (Lit 5))))),
     "lambda tests" ~:
       1 ~=? sEval (plusOne :@ (To (Lit 0))),

     "factorial of 5" ~:
        120 ~=? sEval ((From (From sFact :@ To (Lit 5)))),

     "summation to 5" ~:
       15 ~=? sEval sSumI5,

     "factorial of 5, prime" ~:
       120 ~=? sEval sFact5',

    -- "tuple" ~:
    --   1 ~=? sEval (UniFst (Lit (1, 2))),

    -- "tuple" ~:
    --   (1,2) ~=? sEval (UniFst (Lit ((1, 2), 2))),

    -- "tuple" ~:
    --   2 ~=? sEval (UniSnd (Lit (1, 2))),

    -- "tuple" ~:
    --   (4, 6) ~=? sEval (UniSnd (UniFst (Lit ((1, (4, 6)), 2)))),

    "polymorphic equality" ~:
      True ~=? sEval ((Lam "x" (BinEq x x) :@ (To (Lit False)))),

    "polymorphic equality" ~:
      False ~=? sEval ((Lam "x" (UniNot (BinEq x x)) :@ (To (Lit False))))
  ]
