{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes, GADTs, ScopedTypeVariables #-}

-- This module defines a compilers for converting between dynamic
-- programs to static programs omitting as many dynamic checks as possible.
-- This module compiles to LangSnl.
module CompilerLangSnl where

import qualified Common as C
import LangSnl
import qualified Lang as DL

import DataDynamic
import qualified DataTypeable as TR
import DataTypeable

import qualified Data.Map.Strict as Map
-- =======================================================================================

-- Map from bound variable name to int representing De Brujin indice.
-- I wanted to use a map M : String -> DeBrujin, but I could get the types working X(
type NameEnv = Map.Map String Int

-- I couldn't get the types to work. For the lambda and the var case since l is
-- changing I get the rigid type variable error.
compile' :: TypeRep t -> NameEnv -> DL.Exp -> LangSnl l t
compile' tr env (DL.Lit x)      = checkTr tr (Lit x)
-- compile' tr env (DL.Var bVar)   =
--   case Map.lookup bVar env of
--     Just ind -> checkTr tr $ Var (intToDeBrujin ind)
--     Nothing -> error "Failed variable lookup. Free variable?"
compile' tr env (DL.If cond e1 e2) =
  If (compile' trBool env cond) (compile' tr env e1) (compile' tr env e2)
compile' tr env (DL.Bin op e1 e2) = checkTr tr $ case op of
    C.Plus -> Bin Plus ie1' ie2'
    C.Mult -> Bin Mult ie1' ie2'
    C.Minus -> Bin Minus ie1' ie2'
    -- Hmmm, this doesn't work. All expressions are expected to return Ints now...
    -- C.And   -> Bin And be1' be2'
  where ie1' = compile' trInte env e1
        ie2' = compile' trInte env e2
--compile' tr env (e1 DL.:@ e2) =
--  case eqT tr (compile' tr env e1) (compile' tr env e2)


-- =======================================================================================
checkTr :: forall a b l. (Typeable b) => TypeRep a -> LangSnl l b -> LangSnl l a
checkTr tra exp =
  -- tra and trb are equal. Easy casting to a StaticExp a.
  case eqT tra trb of
    Just Refl -> exp
    Nothing ->
      -- We expected a Dynamic, but our term isn't so. So we cast it to one.
      case eqT C.trDynamic tra of
        Just Refl -> To exp
        Nothing   ->
          -- Our argument is Dynamic, cast it to the type it should be. We rely on
          -- withTypeable to do the work. Why?
          case eqT C.trDynamic trb of
            Just Refl -> withTypeable tra (From exp)
            Nothing   ->
              error $ "checkTr: Type mismatch error.\n Expected: " ++ show tra ++
                  "\n Actual: " ++ show trb
  where trb = typeRep :: TypeRep b
-- =======================================================================================
-- Hmmm... It likes if I enumerate a few of them, but making a general n case
-- leads to an infinite type error. I don't think it know that it will terminate.
-- yeah... I don't know what this is doing X(
--intToDeBrujin :: Int -> Index (a : a : a : a : b) a
intToDeBrujin 0 = Z
intToDeBrujin 1 = S Z
intToDeBrujin 2 = S (S Z)
intToDeBrujin 3 = S (S (S Z))
--intToDeBrujin _ = error "Ran out of de brujin indices!"
-- intToDeBrujin n = S (intToDeBrujin (n - 1))
-- =======================================================================================
data ArrowRep t where
  ArrowRep :: TypeRep t1 -> TypeRep t2 -> ArrowRep (t1 -> t2)

arrowUnify :: TypeRep a -> Maybe (ArrowRep a)
arrowUnify tra = do
  (TR.App tra' tra2) <- splitApp tra
  (TR.App tr tra1) <- splitApp tra'
  Refl <- eqT tr (typeRep :: TypeRep (->))
  return $ ArrowRep tra1 tra2
-- =======================================================================================
