{-# LANGUAGE GADTs, ScopedTypeVariables, TypeOperators, DataKinds, FlexibleInstances, TypeFamilies #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns -fno-warn-name-shadowing  #-}
module DataDynamic where

import DataTypeable
-- =======================================================================================
-- | A Dynamic is a runtime representation of the actual type as a TypeRep and
-- | the actual element of that type.
data Dynamic where
  Dyn :: TypeRep a -> a -> Dynamic

-- | We can easily convert things to dynamic. Every class has an instace of Typeable
-- | automatically implemented by the compiler.
toDynamic :: Typeable a => a -> Dynamic
toDynamic x = Dyn typeRep x

{- WANT:
fromDynamic :: forall a. Typeable a => Dynamic -> Maybe a
fromDynamic (Dyn (rb :: TypeRep b) (x :: b)) =
  | ra == rb  = Just x
  | otherwise = Nothing
  where
    ra = typeRep :: TypeRep a
-}

-- | Compare types of the given Dynamic value to the expected value. If they are the same
-- | return the casted element, else Nothing.
fromDynamic :: forall a. Typeable a => Dynamic -> Maybe a
fromDynamic (Dyn (rb :: TypeRep b) (x :: b)) = case
  eqT (typeRep :: TypeRep a) rb of
    Just Refl -> Just x
    Nothing   -> Nothing

-- | Similar to fromDynamic except expects a default element in case of failure.
fromDyn :: Typeable a => Dynamic -> a -> a
fromDyn d def = case fromDynamic d of
  Just x  -> x
  Nothing -> def

-- =======================================================================================
-- decomposing type representations
dynFstWrong :: Dynamic -> Maybe Dynamic
dynFstWrong (Dyn pab x) = do
  Refl <- eqT pab (typeRep :: TypeRep (Dynamic,Dynamic))
  return (Dyn typeRep (fst x))

exampleWrong = do
  x <- dynFstWrong (toDynamic ('c', 'a'))
  y <- fromDynamic x
  return $ y == 'c'
-- =======================================================================================
-- | Given a Dynamic value representing a tuple (,) return the first element.
dynFst :: Dynamic -> Maybe Dynamic
dynFst (Dyn rpab x) = do
  -- intuition, make sure that pab is a pair type,
  -- then call fst on it
  App rpa rb <- splitApp rpab
  App rp ra  <- splitApp rpa
  Refl       <- eqT rp (typeRep :: TypeRep (,))
  return (Dyn ra (fst x))

example = do
  x <- dynFst (toDynamic ('c', 'a'))
  y <- fromDynamic x
  return $ y == 'c'

-- | Given a Dynamic value representing a tuple (,) return the snd element.
dynSnd :: Dynamic -> Maybe Dynamic
dynSnd (Dyn rpab x) = do
  -- intuition, make sure that pab is a pair type,
  -- then call fst on it
  App rpa rb <- splitApp rpab
  App rp ra  <- splitApp rpa
  Refl       <- eqT rp (typeRep :: TypeRep (,))
  return (Dyn rb (snd x))

showDynTypeRep :: Dynamic -> String
showDynTypeRep (Dyn ra (x :: a)) = show ra

instance Typeable Dynamic where typeRep = TR $ TC ty "Dynamic"
