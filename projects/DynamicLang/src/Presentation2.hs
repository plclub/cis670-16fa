{-# LANGUAGE DataKinds, RankNTypes, ScopedTypeVariables, GADTs #-}

import DataDynamic
import DataTypeable
import Common(LangType)
import qualified Common as C
import StaticLang
import StaticLangTests
import qualified Lang as DL
import Data.Map as Map
import Compiler

{-======================================================================================= -}{-
                                   StaticLang, Lang                                       -}
-- We are in typeland now. Separte our operators.
data IntIntOp_   = Plus_ | Minus_ | Mult_
data BoolBoolOp_ = Or_   | And_
data IntBoolOp_  = Lte_  | Gte_   | Lt_ | Gt_
data EqOp_       = Eq_
data NotOp_      = Not_

data StaticExp_ t where -- Some cases have been ommited for breverity...
  Lam_  :: String -> StaticExp_ a -> StaticExp_ (Dynamic -> a)
  (::@) :: StaticExp_ (Dynamic -> t2) -> StaticExp_ Dynamic -> StaticExp_ t2
  BinIntBool_ :: IntBoolOp_ -> StaticExp_ Integer  -> StaticExp_ Integer -> StaticExp_ Bool
  BinEq_ :: StaticExp_ Dynamic -> StaticExp_ Dynamic -> StaticExp_ Bool
  UniFst_ :: (LangType a, LangType b) => StaticExp_ (a,b) -> StaticExp_ a
  Lit_  :: LangType a => a -> StaticExp_ a
  Var_  :: String -> StaticExp_ Dynamic
  If_   :: StaticExp_ Bool -> StaticExp_ t -> StaticExp_ t -> StaticExp_ t
  To_   :: Typeable t => StaticExp_ t -> StaticExp_ Dynamic
  From_ :: Typeable t => StaticExp_ Dynamic -> StaticExp_ t
{-                                                                                        11

======================================================================================= -}{-
                                   Bad things don't compile...                          -}


ex1_ = BinIntBool Lt (Lit 5) (Lit "cat")

ex2_ = BinIntBool Mult (Lit 5) (Lit 5)

-- And we can still use Dynamic types when needed.
yComb_ :: StaticExp (Dynamic -> Dynamic)
yComb_ = Lam "f" (g :@ To g)
   where
     g = Lam "x" (From f :@ (From x :@ x))

sFact_ :: StaticExp Dynamic
sFact_ = yComb :@ To
   (Lam "f"
      (To (Lam "x"
        (To (If (BinEq x (To zero))
             (Lit 1)
             (BinInt Mult (From x) (From (From f :@ To (BinInt Minus (From x) one)))))))))



{-                                                                                      12

======================================================================================= -}{-
                                  Lots and lots of casting...

   These StaticExp's are not fun to write:
-}

-- | Function to compute sum([1..i]).
sSumI_ :: StaticExp Dynamic
sSumI_ = yComb :@ To (Lam "f"
    -- Lam expects a StaticExp t as it's first argument. Instead we have
    -- StaticExp (Dynamic -> t2) from the Lam, so we cast to StaticExp Dynamic.
    (To (Lam "x"
          -- Here If returns a StaticExp Int, we want StaticExp Dynamic, so we cast.
          (To (If (UniNot (BinEq (From x) (To zero)))
                -- We use 2 `From` after the (+), the innermost converts the dynamic
                -- returned by Var into `StaticExp (Dynamic -> t)`, the outer From
                -- converts the Dynamic into `StaticExp Int`.
                -- Function applications expects StaticExp Dynamic, hence To.
                -- (-) expects StaticExp Int so we From since Var returns a Dynamic.
                -- Lots of casting... X(
                (BinInt Plus (From x) (From (From f :@ (To (BinInt Minus (From x) (Lit 1))))))
                ((Lit 0)))))))


{-                                                                                      13

======================================================================================= -}{-
                          Compiling from Lang to LangExp                                -}

-- Compile takes a typeRep representing the type we expect this expression to be of.
compile_ :: TypeRep t -> DL.Exp -> StaticExp t
compile_ tr (f DL.:@ e) =
  let trArrow = mkTyApp (mkTyApp (typeRep :: TypeRep (->)) C.trDynamic) tr in
    (compile_ trArrow f) :@ (compile_ C.trDynamic e)
-- ...
compile_ tr (DL.Bin op e1 e2) =
  if intIntOperands op then
    checkTr tr $ BinInt (opToInt op) e1I' e2I' else
-- ...
  if boolOperands op then
    checkTr tr $ BinBool (opToBool op) (compile_ trBool e1) (compile_ trBool e2) else
    error $ show op ++ ": Unimplemented Bin operator."
  where e1I' = compile_ trInte e1
        e2I' = compile_ trInte e2                                                      {-

   When trying to compile the expression "DL.Bin Plus (Lit 3) (Lit 4)" what should 'tr'
   be? Not necessarily trInte, if this expression is the argument to a function, then
   'tr' should be trDynamic, this is why we need checkTr!


                                                                                        14

======================================================================================= -}{-
                           Casting to and from the expected type                        -}


checkTr_ :: forall a b. (Typeable b) => TypeRep a -> StaticExp b -> StaticExp a
checkTr_ tra exp =
  -- tra and trb are equal. Easy casting to a StaticExp a.
  case eqT tra trb of
    Just Refl -> exp :: StaticExp a
    -- We expected a Dynamic, but our exp isn't so. So we cast it to one.
    Nothing -> case eqT C.trDynamic tra of
      Just Refl -> To exp
      -- Our argument is Dynamic, cast it to the type it should be. We rely on
      -- withTypeable to do the work. Why?
      Nothing   -> case eqT C.trDynamic trb of
        Just Refl -> withTypeable tra (From exp)
        Nothing   -> error $ "checkTr: Type mismatch error.\n Expected: " ++ show tra ++
                  "\n Actual: " ++ show trb
  where trb = typeRep :: TypeRep b


{-                                                                                        15

======================================================================================= -}{-
                              Equality... Again...

   Consider the following expression:                                                   -}
dynamicExp_ = DL.Bin C.Eq (DL.Lit "cat") (DL.Lit True)                                  {-

   When we try to compile this expression it would match the DL.Bin case:
   compile tr (DL.Bin op e1 e2)
     where tr = trBool, e1 = (DL.Lit "cat"), e2 = (DL.Lit True)

   we must call compile on our subexpressions e1 and e2:
   compile ??? e1
   compile ??? e2

   Problem: What should the type of our trRep be here?
   Answer: We do not know yet. The compiler should be extended to return type information.
           Then we could recurse down, find out the type, and type this expression.


   For now, we cast both arguments to Dynamic and call our dynEq:                       -}
compile__ tr (DL.Bin C.Eq e1 e2) = checkTr tr $
  BinEq (compile C.trDynamic e1) (compile C.trDynamic e2)


{-                                                                                      16

======================================================================================= -}{-
                                     Still to do.


   - Our function application requires the type of the argument to be dynamic. This
     constraint should be lifted.

   - Equality for expressions should not need casting to dynamics.

   - Lists are trickier to implement (Not shown).

   - Extend compiler to return type information of an expression when necessary.












                                                                                        17

======================================================================================= -}
