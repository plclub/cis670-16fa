{-# LANGUAGE RebindableSyntax #-}
module LangTest where

import Prelude hiding (Num(..))
-- Haskell is unable to derive the type of of (Lit 3) as it is polymorphic through the
-- Num typeclass. So instead of writing (Lit (3 :: Int)) I prefer using the
-- RebindableSyntax extension.
-- TODO: With a nice parser this won't be an issue!
-- In hindsight... it might have been use quick check for this...

import Test.HUnit
import DataTypeable
import DataDynamic

import Lang
import Eval
import Common

fromInteger :: Integer -> Integer
fromInteger = id

-- Define a couple variables to play with.
x = Var "x"
y = Var "y"
z = Var "z"
f = Var "f"
n = Var "n"
i = Var "i"
true = Lit True
false = Lit False

one = Lit 1
zero = Lit 0

yComb :: Exp
yComb = Lam "f" (e :@ e)
         where e = Lam "x" (f :@ (x :@ x))

fact :: Exp
fact = yComb :@ (Lam "f" (Lam "n"
                    (If (Bin Eq n zero)
                     one
                     (Bin Mult n (f :@ (Bin Minus n one)))
                      )))

-- Dynamic Language tests. Make sure our evaluator behaves like we expect it to!
-- This was also very useful for thinking about the language :)
tests = TestList
  [
    -- Literals
    "language literals 1" ~:
      5 ~=? dEval (Lit 5),
    "language literals 2" ~:
      True ~=? dEval (Lit True),
    "language literals 2" ~:
      "cat" ~=? dEval (Lit "cat"),
    "language literals 3" ~:
      'c' ~=? dEval (Lit 'c'),

    -- Lists
    "lists 1" ~:
      End ~=? dEval Nill,
    "lists 2" ~:
     1 +: End ~=? dEval (Bin Cons (Lit 1) Nill),
    "lists 3" ~:
      1 +: "cat" +: Tuple (toDynamic 2) (toDynamic 'c') +: End ~=?
      dEval (Bin Cons (Lit 1) (Bin Cons (Lit "cat")
                               (Bin Cons (Bin Tup (Lit 2) (Lit 'c')) Nill))),
    "lists 3" ~:
     (1 +: End) +: End ~=? dEval (Bin Cons (Bin Cons (Lit 1) Nill) Nill),
    "lists head 1" ~:
      1 ~=? dEval (Uni Head (Bin Cons (Lit 1) Nill)),
    "lists tail" ~:
      End ~=? dEval (Uni Tail (Bin Cons (Lit 1) Nill)),
    "lists head 2" ~:
      1 ~=? dEval (Uni Head (Bin Cons (Lit 1) (Bin Cons (Lit "cat")
                               (Bin Cons (Bin Tup (Lit 2) (Lit 'c')) Nill)))),
    "lists tail" ~:
      "cat" +: Tuple (toDynamic 2) (toDynamic 'c') +: End ~=?
      dEval (Uni Tail (Bin Cons (Lit 1) (Bin Cons (Lit "cat")
                               (Bin Cons (Bin Tup (Lit 2) (Lit 'c')) Nill)))),

    -- Integers
    "simple ints" ~:
      10 ~=? dEval (Bin Plus (Lit 5) (Lit 5)),
    "simple ints" ~:
      10 ~=? dEval (Bin Minus (Lit 15) (Lit 5)),
    "simple ints" ~:
      18 ~=? dEval (Bin Plus
                            (Lit 6)
                             (Bin Mult (Lit 3) (Lit 4))),

    -- Bools
    "simple bools" ~:
      False ~=? dEval (Bin And (Lit True) (Lit False)),
    "simple bools" ~:
      True ~=? dEval (Bin Or (Lit True) (Lit False)),

    -- Operators
    "int comparison" ~:
      True ~=? dEval (Bin Lte (Lit 3) (Lit 3)),
    "int comparison" ~:
      False ~=? dEval (Bin Lt (Lit 3) (Lit 3)),
    "int comparison" ~:
      True ~=? dEval (Bin Lt (Lit 3) (Lit 4)),
    "int comparison" ~:
      True ~=? dEval (Bin Gte (Lit 3) (Lit 3)),
    "int comparison" ~:
      True ~=? dEval (Bin Gt (Lit 4) (Lit 3)),

    "conditional tests" ~:
      1 ~=? dEval (If (Lit True) (Lit 1) (Lit 2)),
    "conditional tests" ~:
      2 ~=? dEval (If (Lit False) (Lit 1) (Lit 2)),
    "conditional tests" ~:
      2 ~=? dEval (If (Uni Not (Bin Eq (Lit 0) (Lit 0))) (Lit 1) (Lit 2)),
    "conditional tests" ~:
      True ~=? dEval (If (Bin Lte (Lit 0) (Lit 0))
                       (Lit True)
                       (Lit False)),

    -- Functions.
    "lambda tests" ~:
      "cat" ~=? dEval (Lam "x" x :@ (Lit "cat")),
    "factorial" ~:
      120 ~=? dEval (fact :@ (Lit 5)),

    -- Tuples
    "tuple" ~:
      Tuple (toDynamic 2) (toDynamic 2) ~=? dEval (Bin Tup (Lit 2) (Lit 2)),
    "tuple fst" ~:
      Tuple (toDynamic 1) (toDynamic 2) ~=?
      dEval (Uni Fst (Bin Tup (Bin Tup (Lit 1) (Lit 2)) (Lit 2))),
    "tuple snd" ~:
       2 ~=? dEval (Uni Snd (Bin Tup (Lit 1) (Lit 2))),
    "tuple fst snd" ~:
       Tuple (toDynamic 4) (toDynamic 6) ~=?
       dEval (Uni Snd (Uni Fst
                      (Bin Tup (Bin Tup (Lit 1) (Bin Tup (Lit 4) (Lit 6))) (Lit 2)))),
    "tuple" ~:
      Tuple (toDynamic 4) (toDynamic 6) ~=? dEval (Bin Tup (Lit 4) (Lit 6)),
    "construct tuple in function" ~:
      Tuple (toDynamic 1) (toDynamic 3) ~=?
      dEval ((Lam "x" (Bin Tup (Lit 1) x)) :@ (Lit 3)),
    "return tuple from function" ~:
      Tuple (toDynamic 1) (toDynamic 4) ~=?
      dEval ((Lam "x" (Bin Tup (Lit 1) (Lit 4))) :@ (Lit 3)),

    -- Equality.
    "dynamicEquality" ~:
      True ~=? dEval ((Lam "x" (Bin Eq x x)) :@ (Lit 3)),
    "dynamicEquality" ~:
      False ~=? dEval ((Lam "x" (Bin Eq x (Lit 4))) :@ (Lit 3)),

    "equality int" ~:
      False ~=? dEval (Bin Eq (Lit 5) (Lit 4)),
    "equality int" ~:
      True ~=? dEval (Bin Eq (Lit 5) (Lit 5)),
    "equality bool" ~:
      True ~=? dEval (Bin Eq (Lit True) (Lit True)),
    "equality bool" ~:
      False ~=? dEval (Bin Eq (Lit False) (Lit True)),
    "equality char" ~:
      True ~=? dEval (Bin Eq (Lit 'c') (Lit 'c')),
    "equality char" ~:
      False ~=? dEval (Bin Eq (Lit 'd') (Lit 'c')),
    "equality string" ~:
      True ~=? dEval (Bin Eq (Lit "cat") (Lit "cat")),
    "equality string" ~:
      True ~=? dEval (Bin Eq (Lit "tacocat") (Lit "tacocat")),
    "equality lists" ~:
      True ~=? dEval (Bin Eq Nill Nill),
    "equality lists" ~:
      False ~=? dEval (Bin Eq (Bin Cons (Lit 3) Nill) Nill),
    "equality lists" ~:
      True ~=? dEval (Bin Eq (Bin Cons (Lit 3) Nill) (Bin Cons (Lit 3) Nill)),
    "equality lists" ~:
      False ~=? dEval (Bin Eq (Bin Cons (Lit 3) (Bin Cons (Lit "cat") Nill))
                              (Bin Cons (Lit 3) Nill)),
    "equality lists" ~:
      True ~=? dEval (Bin Eq (Bin Cons (Lit 3) (Bin Cons (Lit "cat") Nill))
                             (Bin Cons (Lit 3) (Bin Cons (Lit "cat") Nill))),
    "equality tuple" ~:
      True ~=? dEval (Bin Eq (Bin Tup (Lit 2) (Lit 2)) (Bin Tup (Lit 2) (Lit 2))),
    "equality tuple" ~:
      False ~=? dEval (Bin Eq (Bin Tup (Lit 2) (Lit 2)) (Bin Tup (Lit 1) (Lit 2))),
    "equality tuple" ~:
      True ~=? dEval (Bin Eq (Bin Tup (Lit 2) (Lit 'c')) (Bin Tup (Lit 2) (Lit 'c'))),
        "equality tuple" ~:
      False ~=? dEval (Bin Eq (Bin Tup (Lit 2) (Lit 'c')) (Bin Tup (Lit 2) (Lit 'd')))
  ]
