{-# LANGUAGE RankNTypes, GADTs, ScopedTypeVariables #-}

module Eval where
import Data.Maybe (fromMaybe)
import qualified Data.Map as Map

import Lang
import DataDynamic
import DataTypeable
import Common

-- =======================================================================================
{- We may define an evaluator for our simple language.

   given a dynamic value `d` and a default value `a` it will return the `d`
   of type `a` or the default value if it cannot be cast.
   fromDyn :: Typeable a => Dynamic -> a -> a

   Converts any type to a dynamic type.
   toDynamic :: Typeable a => a -> Dynamic -}
-- =======================================================================================
-- | Evaluate an Exp expression to a dynamic value of the expression.
evalExp :: Env -> Exp -> Dynamic
-- Create function over v, add v to our env and recurse on updated env.
evalExp env (Lam s e) = toDynamic $ \ v -> evalExp (Map.insert s v env) e
evalExp env (e1 :@ e2) = gFromDynamic (evalExp env e1) (evalExp env e2)

evalExp env (Bin op e1 e2) = evalBin env op e1 e2
evalExp env (Uni op e) = evalUni env op e

evalExp _   (Lit (n :: a)) = toDynamic n
-- Look up variable in our enviornment!
evalExp env (Var x) = fromMaybe (error err) $ Map.lookup x env
  where err = "Variable " ++ x ++ " not found in this enviornment."
-- b' must be converted to a bool.
evalExp env (If b e1 e2) = case gFromDynamic (evalExp env b) of
                             True   -> evalExp env e1
                             False  -> evalExp env e2
evalExp env Nill = toDynamic End
-- =======================================================================================
evalUni :: Env -> UniOp -> Exp -> Dynamic
evalUni env Not e = toDynamic . not . gFromDynamic $ evalExp env e
evalUni env Fst e = getFst (evalExp env e)
evalUni env Snd e = getSnd (evalExp env e)
evalUni env Head e = getHead (evalExp env e)
evalUni env Tail e = getTail (evalExp env e)

-- =======================================================================================
evalBin :: Env -> BinOp -> Exp -> Exp -> Dynamic
evalBin env Eq  e1 e2 = toDynamic $ dynEq (evalExp env e1) (evalExp env e2)
evalBin env Tup e1 e2 = toDynamic $ Tuple (evalExp env e1) (evalExp env e2)
evalBin env Cons e1 e2 = toDynamic $ Add (evalExp env e1) (gFromDynamic (evalExp env e2))
evalBin env op e1 e2
  | op == Plus = toDynamic $ eInt1' + eInt2'
  | op == Minus = toDynamic $ eInt1' - eInt2'
  | op == Mult = toDynamic $ eInt1' * eInt2'
  | op == Or = toDynamic $ eBool1' || eBool2'
  | op == And = toDynamic $ eBool1' && eBool2'
  | op == Lte = toDynamic $ eInt1' <= eInt2'
  | op == Gte = toDynamic $ eInt1' >= eInt2'
  | op == Lt = toDynamic $ eInt1' < eInt2'
  | op == Gt = toDynamic $ eInt1' > eInt2'
  | otherwise = error $ "Unkown operator: '" ++ show op ++ "'. Unimplemented operator?"
  where eInt1' = gFromDynamic (evalExp env e1) :: Integer
        eInt2' = gFromDynamic (evalExp env e2) :: Integer
        eBool1' = gFromDynamic (evalExp env e1)
        eBool2' = gFromDynamic (evalExp env e2)
-- =======================================================================================
dEval :: forall t. (Typeable t) => Exp -> t
dEval e = gFromDynamic (evalExp Map.empty e)

-- | Count the number of dynamics checks necessary to evaluate an expressions. These
-- numbers are hard coded based on the evaluator above.
countDChecks :: Exp -> Int
countDChecks (Lam _ e) = 1 + countDChecks e
countDChecks (e1 :@ e2) = 1 + countDChecks e1 + countDChecks e2
countDChecks (Bin op e1 e2) = 1 + 1 + 1 + countDChecks e1 + countDChecks e2
countDChecks (Uni _ e) = countDChecks e
countDChecks (Lit _) = 1
countDChecks (Var _) = 0
countDChecks (If b e1 e2) = 1 + countDChecks b + countDChecks e1 + countDChecks e2
