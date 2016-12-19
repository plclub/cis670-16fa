{-# LANGUAGE RankNTypes, GADTs, ScopedTypeVariables #-}
-- This module defines a compilers for converting between dynamic
-- programs to static programs omitting as many dynamic checks as possible.
module Compiler where

import Data.Map as Map

import qualified Common as C
import StaticLang
import PrettyPrint
import qualified Lang as DL

import DataDynamic
import qualified DataTypeable as TR
import DataTypeable

-- =======================================================================================
data ArrowRep t where
  ArrowRep :: TypeRep t1 -> TypeRep t2 -> ArrowRep (t1 -> t2)

-- | Attempt to turn a TypeRep (->), into an ArrowRep.
-- | tra should look as follows:
-- (((tr) tra1) tra2)
-- <= tra ==========>
--  <= tra' ==>
-- Where tr is -(>)
arrowUnify :: TypeRep a -> Maybe (ArrowRep a)
arrowUnify tra = do
  (TR.App tra' tra2) <- splitApp tra
  (TR.App tr tra1) <- splitApp tra'
  Refl <- eqT tr (typeRep :: TypeRep (->))
  return $ ArrowRep tra1 tra2

-- =======================================================================================
-- | Take a TypeRep 'tr' and a StaticExp Dynamic 'he' and check whether 'tr' is an
-- | ArrorRep of the

-- | Updated compiler. We use information about the current context to infer the types
-- | and we percolate this information down though an additional TypeRep parameter.

-- | TODO: We can define an ADT which holds the different types of errors we expect to
-- | have. Then we can  change the return value to Either (Static t) (MyErrors)
-- | Then we can return an error and unit test to ensure things that shouldn't
-- | compile, don't.
compile :: TypeRep t -> DL.Exp -> StaticExp t
compile tr (DL.Lam str e) =
  case arrowUnify tr of -- Ensure that we expect a function from our contex.
    Just (ArrowRep t1 t2) ->
      -- Our first argument must be a Dynamic. For now...
      case eqT t1 C.trDynamic of
        Just Refl -> Lam str (compile t2 e) -- Type of exp must be of t2.
        Nothing   -> error "Lam: First argument of arrow should be dynamic."
    Nothing -> -- Not a function, maybe a dynamic type? cast.
      case eqT tr C.trDynamic of
        Just Refl -> To (Lam str (compile C.trDynamic e))
        Nothing   -> error "Lam: Type is not arrow or dynamic."
compile tr (f DL.:@ e) =
  let trArrow = mkTyApp (mkTyApp (typeRep :: TypeRep (->)) C.trDynamic) tr in
     (compile trArrow f) :@  (compile C.trDynamic e)

-- Equality is hard... We should pass information up the tree as well as down.
-- TODO : This way, we can recurse until we know a type to type this expressions.
compile tr (DL.Bin C.Eq e1 e2) = checkTr tr $ BinEq (compile C.trDynamic e1)
                                       (compile C.trDynamic e2)

compile tr (DL.Uni C.Not e) = checkTr tr $ UniNot (compile trBool e)
-- We hit a binary expression. Based on the operator we can check if the types are
-- correct and infer the type of our subexpressions from those. We then check if
-- our results matches our passed tr.
compile tr (DL.Bin op e1 e2) =
  if intIntOperands op then
    checkTr tr $ BinInt (opToInt op) e1I' e2I' else
  if intBoolOperands op then
    checkTr tr $ BinIntBool (opIntToBool op) e1I' e2I' else
  if boolOperands op then
    checkTr tr $ BinBool (opToBool op) (compile trBool e1) (compile trBool e2) else
    error $ show op ++ ": Unimplemented Bin operator."
  where e1I' = compile trInte e1
        e2I' = compile trInte e2
--  checkTr tr $ Bin op (compile trInt e1) (compile trInt e2)
compile tr (DL.Lit n)             = checkTr tr (Lit n)
compile tr (DL.Var var)           = checkTr tr (Var var)
compile tr (DL.If cond e1 e2) =
  If (compile trBool cond) (compile tr e1) (compile tr e2)
-- =======================================================================================
-- | These function are used in `compile`. When we get a tr which is a trBool
-- | we don't know whether the subexpressions should be integers or bools, we can figure
-- | it out based on the operator though. Except in the case of Eq and Neq...
boolOperands :: C.BinOp -> Bool
boolOperands C.Or = True
boolOperands C.And = True
boolOperands _   = False

intIntOperands :: C.BinOp -> Bool
intIntOperands C.Plus = True
intIntOperands C.Minus = True
intIntOperands C.Mult = True
intIntOperands _ = False

intBoolOperands :: C.BinOp -> Bool
intBoolOperands C.Lte = True
intBoolOperands C.Gte = True
intBoolOperands C.Lt = True
intBoolOperands C.Gt = True
intBoolOperands _ = False

-- =======================================================================================
errorMessageTo = " is the wrong operator for this function."

opToInt :: C.BinOp -> IntIntOp
opToInt C.Plus = Plus
opToInt C.Minus = Minus
opToInt C.Mult = Mult
opToInt op = error $ show op ++ errorMessageTo

opToBool :: C.BinOp -> BoolBoolOp
opToBool C.And = And
opToBool C.Or = Or
opToBool op = error $ show op ++ errorMessageTo

opIntToBool :: C.BinOp -> IntBoolOp
opIntToBool C.Lte = Lte
opIntToBool C.Gte = Gte
opIntToBool C.Lt = Lt
opIntToBool C.Gt = Gt
opIntToBool op = error $ show op ++ errorMessageTo

-- =======================================================================================
-- | Given a type representation and an expression, check that the expression is
-- | of the type specified by the type represenation. Else it may be the case
-- | that we want a dynamic or we have a dynamic, then cast respectively.
checkTr :: forall a b. (Typeable b) => TypeRep a -> StaticExp b -> StaticExp a
checkTr tra exp =
  -- tra and trb are equal. Easy casting to a StaticExp a.
  case eqT tra trb of
    Just Refl -> exp :: StaticExp a
    -- We expected a Dynamic, but our term isn't so. So we cast it to one.
    Nothing   -> case eqT C.trDynamic tra of
      Just Refl -> To exp
      -- Our argument is Dynamic, cast it to the type it should be. We rely on
      -- withTypeable to do the work. Why?
      Nothing   -> case eqT C.trDynamic trb of
        Just Refl -> withTypeable tra (From exp)
        Nothing   -> error $ "checkTr: Type mismatch error.\n Expected: " ++ show tra ++
                  "\n Actual: " ++ show trb
  where trb = typeRep :: TypeRep b
