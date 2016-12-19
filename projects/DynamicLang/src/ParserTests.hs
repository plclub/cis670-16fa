{-# LANGUAGE RebindableSyntax #-}
-- See LangTest.hs ^
module ParserTests where

import Prelude hiding (Num(..))

import Test.HUnit
import Lang
import Common
import Parser

fromInteger :: Integer -> Integer
fromInteger = id

n = Var "n"
f = Var "f"

tests = TestList
  [
    -- literals
    "Literals int" ~:
    tryParse "5" ~=? Lit 5,
    "Literals char" ~:
    tryParse "'c'" ~=? Lit 'c',
    "Literals string" ~:
    tryParse "\"cat\"" ~=? Lit "cat",
    "Literals bool" ~:
    tryParse "true" ~=? Lit True,
    "Literals bool" ~:
    tryParse "false" ~=? Lit False,
    -- Implement lists and tuples...

    -- Variable
    "var" ~:
    tryParse "x" ~=? Var "x",

    -- functions
    "function 1" ~:
    tryParse "(fun x. x)" ~=? Lam "x" (Var "x"),
    "function 2" ~:
    tryParse "(fun x. 5)" ~=? Lam "x" (Lit 5),
    "function 3" ~:
    tryParse "(fun x. (fun y. x))" ~=? Lam "x" (Lam "y" (Var "x")),

    -- Function application:
    "function application 1" ~:
    tryParse "(f 5)" ~=? (Var "f") :@ (Lit 5),
    "function application 2" ~:
    tryParse "('c' 5)" ~=? (Lit 'c') :@ (Lit 5),
    "function application 3" ~:
    tryParse "((fun x. x) 5)" ~=? (Lam "x" (Var "x")) :@ (Lit 5),

    -- Binary expressions:
    "Binary expression 1" ~:
    tryParse "(== 3 3)" ~=? (Bin Eq (Lit 3) (Lit 3)),
    "Binary expression 2" ~:
    tryParse "(== (+ 1 2) 3)" ~=? (Bin Eq (Bin Plus (Lit 1) (Lit 2)) (Lit 3)),
    "Binary expression 2" ~:
    tryParse "(== ((fun x . x) 3) 3)" ~=? (Bin Eq ((Lam "x" (Var "x")) :@ (Lit 3)) (Lit 3)),

    -- Uniary expressions.
    "Unary Expression 1" ~:
    tryParse "(tail 3)" ~=? (Uni Tail (Lit 3)),
    "Unary Expression 2" ~:
    tryParse "(not (== 1 2))" ~=? (Uni Not (Bin Eq (Lit 1) (Lit 2))),

    -- If
    "If 1" ~:
    tryParse "(if true 1 2)" ~=? (If (Lit True) (Lit 1) (Lit 2)),
    "If 2" ~:
    tryParse "(if (== 1 x) (- 1 x) 2)" ~=?
    (If (Bin Eq (Lit 1) (Var "x")) (Bin Minus (Lit 1) (Var "x")) (Lit 2)),

    "List parser 1" ~:
    tryParse "[1, 2, 3, 4, 5]" ~=?
    (Bin Cons (Lit 1) (Bin Cons (Lit 2) (Bin Cons (Lit 3)
     (Bin Cons (Lit 4) (Bin Cons (Lit 5) Nill))))),
    "List parser 2" ~:
    tryParse "[]" ~=? Nill,
   "List parser 2" ~:
    tryParse "(fun x. [1])" ~=? (Lam "x" (Bin Cons (Lit 1) Nill)),
    "List parser 3" ~:
    tryParse "(fun x. [x])" ~=? (Lam "x" (Bin Cons (Var "x") Nill)),

    "tuple 1" ~:
    tryParse "((fun x. x), 2)" ~=? (Bin Tup (Lam "x" (Var "x")) (Lit 2)),
    "tuple 2" ~:
    tryParse "(1, 2)"  ~=? (Bin Tup (Lit 1) (Lit 2)),

    {-
    (yComb (fun f. (fun n.
                    (if (== n 0)
                     1
                     (* n (f (- n 1)))))))
   -}
    "fact" ~:
    tryParse "(yComb (fun f. (fun n. (if (== n 0) 1 (* n (f (- n 1)))))))" ~=?
    (Var "yComb") :@ (Lam "f" (Lam "n"
                               (If (Bin Eq n (Lit 0))
                                    (Lit 1)
                                    (Bin Mult n (f :@ (Bin Minus n (Lit 1)))))))
  ]
