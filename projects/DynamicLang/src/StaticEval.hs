{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}


module StaticEval where

import StaticLang
import DataTypeable
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import DataDynamic
import Common hiding (BinOp(..), UniOp(..))

-- =======================================================================================
-- | Evaluator for StaticExp t.
staticEval :: Env -> StaticExp t -> t
staticEval env (Lam s e) = \ v -> staticEval (Map.insert s v env) e
staticEval env (e1 :@ e2) = (staticEval env e1) (staticEval env e2)

staticEval env (BinInt op e1 e2) = (intIntOp op) (staticEval env e1) (staticEval env e2)
staticEval env (BinBool op e1 e2) = (boolBoolOp op) (staticEval env e1) (staticEval env e2)
staticEval env (BinIntBool op e1 e2) = (intBoolOp op) (staticEval env e1) (staticEval env e2)
-- | TODO: This is bad. I shouldn't have to convert to dynamics just to check equality...
staticEval env (BinEq e1 e2) =
  dynEq (staticEval env e1) (staticEval env e2)

staticEval env (UniNot e) = not (staticEval env e)
staticEval env (UniFst e) = fst (staticEval env e)
staticEval env (UniSnd e) = snd (staticEval env e)

staticEval env (Lit x) = x
staticEval env (Var x) = fromMaybe (error (errorMsg1 x)) (Map.lookup x env)
staticEval env (If b e1 e2) = if (staticEval env b)
                              then staticEval env e1
                              else staticEval env e2

staticEval env (To e) = toDynamic (staticEval env e)
staticEval env (From e) = gFromDynamic (staticEval env e)

errorMsg1 s = "Cannot find variable " ++ s ++ " in current enviornment."

intIntOp :: IntIntOp -> (Integer -> Integer -> Integer)
intIntOp Plus = (+)
intIntOp Minus = (-)
intIntOp Mult = (*)

boolBoolOp :: BoolBoolOp -> (Bool -> Bool -> Bool)
boolBoolOp Or = (||)
boolBoolOp And = (&&)

intBoolOp :: IntBoolOp -> (Integer -> Integer -> Bool)
intBoolOp Lte = (<=)
intBoolOp Gte = (>=)
intBoolOp Lt  = (<)
intBoolOp Gt  = (>)

-- =======================================================================================
-- We can evaluate our terms:
sEval :: Typeable t => StaticExp t -> t
sEval s = staticEval Map.empty s

check :: (Typeable t1, Typeable t2) => StaticExp t1 -> StaticExp t2
check h1 =  case gcast h1 of
            Just i  -> i
            Nothing -> case gcast h1 of
              Just i -> From i
              Nothing ->
                -- this is a definite type error
                -- we could detect it here, or postpone it
                From (To h1)
