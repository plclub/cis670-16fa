{-# LANGUAGE TypeOperators, DataKinds, RankNTypes,
    ScopedTypeVariables, GADTs #-}

module StaticLang where

-- | The evaluator defined in `Eval` has to do a lot of dynamic checks and casting. Often,
-- unnecessarily. Instead we compile our `Exp` into a static language where we can omit many
-- of the dynamic checks.
import DataDynamic
import DataTypeable
import Common(LangType)

data IntIntOp = Plus | Minus | Mult
data BoolBoolOp = Or | And
data IntBoolOp = Lte | Gte | Lt | Gt
data EqOp = Eq
data NotOp = Not
-- TODO Lists.
data ListOp = Cons

data StaticExp t where
  Lam  :: String -> StaticExp a -> StaticExp (Dynamic -> a)
  (:@) :: StaticExp (Dynamic -> t2) -> StaticExp Dynamic -> StaticExp t2

  BinInt :: IntIntOp -> StaticExp Integer  -> StaticExp Integer -> StaticExp Integer
  BinBool :: BoolBoolOp -> StaticExp Bool  -> StaticExp Bool -> StaticExp Bool
  BinIntBool :: IntBoolOp -> StaticExp Integer  -> StaticExp Integer -> StaticExp Bool
  -- TODO: Equality should not have to be dynamic :/
  BinEq :: StaticExp Dynamic -> StaticExp Dynamic -> StaticExp Bool

  UniNot :: StaticExp Bool -> StaticExp Bool
  -- This implementation of tuples won't work when translating from
  -- dynamic to static.
  UniFst :: (LangType a, LangType b) => StaticExp (a,b) -> StaticExp a
  UniSnd :: (LangType a, LangType b) => StaticExp (a,b) -> StaticExp b


  Lit  :: LangType a => a -> StaticExp a
  Var  :: String -> StaticExp Dynamic
  If   :: StaticExp Bool -> StaticExp t -> StaticExp t -> StaticExp t
  To   :: Typeable t => StaticExp t -> StaticExp Dynamic
  From :: Typeable t => StaticExp Dynamic -> StaticExp t

-- =======================================================================================
-- | Count the number of casts we have to do from Dynamic. TODO This is wrong by now...
numChecks :: StaticExp t -> Int
numChecks (Lam _ e) = numChecks e
numChecks (e1 :@ e2) = numChecks e1 + numChecks e2
numChecks (Var _) = 0
numChecks (Lit _) = 0
numChecks (BinInt _ e1 e2) = numChecks e1 + numChecks e2
numChecks (If e1 e2 e3) = numChecks e1 + numChecks e2 + numChecks e3
numChecks (From e) = 1 + numChecks e
numChecks (To e) = numChecks e
-- =======================================================================================
