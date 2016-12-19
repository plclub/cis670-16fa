-- We may tests the implementation of our compiler by
-- comparing the results of running our Exp through the dynamic evaluator
-- versus, compiling and running through the static evaluation. We expect
-- both to yield the same answer.
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RebindableSyntax #-}
module CompilerTests where

import qualified Prelude as P
import Prelude hiding (Num(..))
import LangTest(fact)

import Test.HUnit
import Lang
import DataTypeable
import StaticEval(sEval)
import Eval(dEval)
import Compiler
import Common
import StaticLang(StaticExp(From))

-- Haskell is unable to derive the type of of (Lit 3) as it is polymorphic through the
-- Num typeclass. So instead of writing (Lit (3 :: Int)) I prefer using the
-- RebindableSyntax extension.
fromInteger :: Integer -> Integer
fromInteger = id

-- Define a couple variables to play with.
x = Var "x"
y = Var "y"
z = Var "z"
f = Var "f"
n = Var "n"
i = Var "i"

testExpI :: String -> Exp -> Test
testExpI str e = str ~: dEval e ~=? sEval (compile trInte e)

testExpFact :: String -> Exp -> Test
testExpFact str e = str ~: (dEval e :: Integer) ~=? sEval (From (compile trDynamic e))

testExpB :: String -> Exp -> Test
testExpB str e = str ~: dEval e ~=? sEval (compile trBool e)

testExpS :: String -> Exp -> Test
testExpS str e = str ~: dEval e ~=? sEval (compile trString e)

testExpVar :: forall a. LangType a => String -> Exp -> TypeRep a -> Test
testExpVar str e tr = dEval e ~=? sEval (compile tr e)

literals :: String
literals = "language literals"

tests = TestList
  [
    -- Simple literals.
    testExpI literals (Lit 5),
    testExpB literals (Lit True),
    testExpS literals (Lit "cat"),
    --testExpVar literals (Lit [1]) (typeRep :: TypeRep [Integer]),
    --testExpVar literals (Lit [1, 2, 3, 4, 5]) (typeRep :: TypeRep [Integer]),
    --testExpVar literals (Lit  [(1,2), (3,4)]) (typeRep :: TypeRep [(Integer, Integer)]),
    --TODO testExpVar (Lit []),
    --testExpVar literals (Lit [[1], [2], [3]]) (typeRep :: TypeRep [[Integer]]),
    --testExpVar literals (Lit (1,2)) (typeRep :: TypeRep (Integer, Integer)),
    --testExpVar literals (Lit ([1,2,3], False)) (typeRep:: TypeRep ([Integer], Bool)),

    -- Integer arithmetic.
    testExpI "integer arithmetic" (Bin Plus (Lit 5) (Lit 5)),
    testExpI "integer arithmetic" (Bin Plus
                                   (Lit 6)
                                   (Bin Mult (Lit 3) (Lit 4))),

    -- Simple bools.
    testExpB "simple bools" (Bin And (Lit True) (Lit False)),
    testExpB "simple bools" (Bin Or (Lit True) (Lit False)),

    -- Integer comparison.
    testExpB "int comparison" (Bin Lt (Lit 5) (Lit 5)),
    testExpB "int comparison" (Bin Lte (Lit 5) (Lit 5)),
    testExpB "int comparison" (Bin Lte (Lit 6) (Lit 5)),
    testExpB "int comparison" (Bin Lte (Lit 3) (Lit 5)),
    testExpB "int comparison" (Bin Gt (Lit 5) (Lit 5)),
    testExpB "int comparison" (Bin Gte (Lit 5) (Lit 5)),
    testExpB "int comparison" (Bin Gte (Lit 6) (Lit 5)),
    testExpB "int comparison" (Bin Gte (Lit 3) (Lit 5)),

    -- Equality tests.
    testExpB "int eq" (Bin Eq  (Lit 1) (Lit 1)),
    testExpB "int eq" (Bin Eq  (Lit 1) (Lit 0)),
    testExpB "bool eq" (Bin Eq  (Lit True) (Lit False)),
    testExpB "char eq" (Bin Eq  (Lit 'c') (Lit 'd')),

    -- Not equal tests.
    testExpB "int neq" (Uni Not (Bin Eq  (Lit 1) (Lit 1))),
    testExpB "int neq" (Uni Not (Bin Eq  (Lit 1) (Lit 0))),
    testExpB "bool neq" (Uni Not (Bin Eq  (Lit True) (Lit False))),
    testExpB "char neq" (Uni Not (Bin Eq  (Lit 'c') (Lit 'd'))),

    -- Ifs.
    testExpI "conditional test 1" (If (Lit True) (Lit 1) (Lit 2)),
    testExpI "conditional test 2" (If (Lit False) (Lit 1) (Lit 2)),
    testExpI "conditional test 3" (If (Uni Not (Bin Eq (Lit 0) (Lit 0))) (Lit 1) (Lit 2)),
    testExpB "conditional test 4" (If (Bin Lte (Lit 0) (Lit 0))
                                   (Lit True)
                                   (Lit False)),

    testExpVar "function" (Lam "x" x :@ (Lit "cat")) trString,

    -- Does not currently work!
    testExpFact "(fact 5)" (fact :@ (Lit 5))

--      1 ~=? dEval (Uni Head (Lit [1, 2, 3])),

--      1 ~=? dEval (Uni Fst (Lit (1, 2))),

--      (1,2) ~=? dEval (Uni Fst (Lit ((1, 2), 2))),

--      2 ~=? dEval (Uni Snd (Lit (1, 2))),

--      (4, 6) ~=? dEval (Uni Snd (Uni Fst (Lit ((1, (4, 6)), 2))))
  ]
