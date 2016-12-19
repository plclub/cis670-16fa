{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, DataKinds, KindSignatures,
    FlexibleInstances#-}

-- | Common functions used across many modules.
module Common where

import qualified Data.Map as Map
import DataTypeable
import DataDynamic

-- =======================================================================================
-- | Enviornment mapping strings to values
type Env = Map.Map String Dynamic

-- | Eq instance for the dynamic types we use in our language. Helpful for debugging
-- | and showing.
instance Eq Dynamic where
  (==) = dynEq

-- | Show instance for the dynamic types we use in our language.
instance Show Dynamic where
  show x =
    case fromDynamic x of    -- Integers.
      Just (i1 :: Integer) -> show i1
      _ -> case fromDynamic x of
        Just (b1 :: Bool) -> show b1    -- Booleans.
        _ -> case fromDynamic x of
          Just (c1 :: Char) -> show c1    -- Chars.
          _ -> case fromDynamic x of
            Just (s1 :: String) -> show s1    -- Strings.
            _ -> case fromDynamic x of
              Just (l1 :: List) -> show l1    -- Lists.
              _ -> case fromDynamic x of
                Just (t1 :: Tuple) -> show t1    -- Tuples.
                _ -> error "Unimplemented/Unknown type."
-- =======================================================================================
data List where
  Add :: Dynamic -> List -> List
  End  :: List

instance Typeable List where typeRep = TR $ TC ty "List"

instance Eq List where
  End == End = True
  (Add x xs) == (Add y ys) = x == y && xs == ys
  -- Different sized lists.
  _ == _ = False

instance Show List where
  show l = "[" ++ showRec l ++ "]"
    where showRec End = ""
          showRec (Add x xs) = show x ++ ", " ++ show xs

(+:) :: Typeable a => a -> List -> List
(+:) x xs = Add (toDynamic x) xs
infixr 6 +:
-- =======================================================================================
data Tuple where
  Tuple :: Dynamic -> Dynamic -> Tuple

instance Eq Tuple where
  Tuple d1 d2 == Tuple d1' d2' = d1 == d1' && d2 == d2'

instance Show Tuple where
  show (Tuple d1 d2) = "(" ++ show d1 ++ ", " ++ show d2 ++ ")"


instance Typeable Tuple where typeRep = TR $ TC ty "Tuple"
-- =======================================================================================
-- | Typeclass for the Haskell types we want to allow in our language.
-- | We need the typeable constraint to make the Typecheker happy as we plan to user
-- | `toDynamic` and `fromDynamic` on our types. The `Eq` and `Show` instances are
-- | needed for typechecking the compiler unit tests test/CompileTests.hs.
class (Typeable a, Eq a, Show a) => LangType a

instance LangType Integer
instance LangType Char
instance LangType Bool
instance LangType String

-- =======================================================================================

-- Possible binary operators for our languages.
data BinOp =
  Plus | Minus | Mult   -- Integers.
  | Or | And            -- Bools.
  | Lte | Gte | Lt | Gt -- Integers tests.
  | Eq                  -- Equality tests.
  | Tup                 -- Make tuple.
  | Cons                -- Make list
  deriving (Show, Eq)

data UniOp =
  Not | Fst | Snd | Head | Tail
  deriving (Show, Eq)
-- =======================================================================================
-- | Convinience variables for typeReps.
trDynamic :: TypeRep Dynamic
trDynamic = typeRep

-- =======================================================================================
-- | More comprehensive error message for dynamic casting failure.
gFromDynamic :: forall a. Typeable a => Dynamic -> a
gFromDynamic d = case fromDynamic d of
  Just d' -> d'
  Nothing -> error (errorMsg (show tra) (showDynTypeRep d))
    where tra = typeRep :: TypeRep a
          errorMsg s1 s2 = "gFromDynamic: Casting to \"" ++ s1 ++
                           "\" failed. Actual type was \"" ++ s2 ++ "\"."

-- =======================================================================================
getFst :: Dynamic -> Dynamic
getFst d = case fromDynamic d of
             Just (Tuple d1 d2) -> d1 -- d1 is already dynamic.
             Nothing  -> error "evalUni Fst: expression not a tuple!"

getSnd :: Dynamic -> Dynamic
getSnd d = case fromDynamic d of
             Just (Tuple d1 d2) -> d2 -- d2 is already dynamic.
             Nothing  -> error "evalUni Snd: expression not a tuple!"

getHead :: Dynamic -> Dynamic
getHead d = case fromDynamic d of
  -- Head of [] should be []?
  Just End -> d
  Just (Add x xs) -> x -- x is already dynamic!
  _ -> error "evalUni Head: expression not a list!"

getTail :: Dynamic -> Dynamic
getTail d = case fromDynamic d of
  -- Tail of [] should be []?
  Just End -> toDynamic End
  Just (Add x xs) -> toDynamic xs
  _ -> error "evalUni Head: expression not a list!"
-- =======================================================================================
data TupleRep t where
  TupleRep :: TypeRep a -> TypeRep b -> TupleRep (a, b)

tupleUnify :: TypeRep t -> Maybe (TupleRep t)
tupleUnify tra = do
  (App tra' tra2) <- splitApp tra
  (App tr tra1) <- splitApp tra'
  Refl <- eqT tr (typeRep :: TypeRep (,))
  return $ TupleRep tra1 tra2

-- =======================================================================================
-- Dynamic language equality comparison function.
-- TODO: I don't know how to make it work for lists... Although I'm not sure there
-- is a simple way to do so. I think I will have to implement my own list version.
-- Notice gFromDynamics throw error if types mismatch.
dynEq :: Dynamic -> Dynamic -> Bool
dynEq d1 d2 =
  case (fromDynamic d1, fromDynamic d2) of    -- Integers.
      (Just (i1 :: Integer), Just (i2 :: Integer)) -> i1 == i2
      (_,_) -> case (fromDynamic d1, fromDynamic d2) of    -- Booleans.
        (Just (b1 :: Bool), Just (b2 :: Bool)) -> b1 == b2
        (_,_) -> case (fromDynamic d1, fromDynamic d2) of    -- Chars.
          (Just (c1 :: Char), Just (c2 :: Char)) -> c1 == c2
          (_,_) -> case (fromDynamic d1, fromDynamic d2) of    -- Strings.
            (Just (s1 :: String), Just (s2 :: String)) -> s1 == s2
            (_,_) -> case (fromDynamic d1, fromDynamic d2) of    -- Lists.
              (Just (l1 :: List), Just (l2 :: List)) -> l1 == l2
              -- Cheat a little bit... Only thing left is tuples X(
              (_,_) -> case (fromDynamic d1, fromDynamic d2) of
                (Just (t1 :: Tuple), Just (t2 :: Tuple)) -> t1 == t2
                _ ->   case (d1, d2) of
                  (Dyn tr1 x, Dyn tr2 y) -> case eqT tr1 tr2 of
                    Nothing -> error "Mismatching types in equality"
                    _       -> error "Unimplemented/Unknown type for equality check!"

-- =======================================================================================
