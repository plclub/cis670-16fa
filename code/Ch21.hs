{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE BangPatterns           #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances   #-}

module Ch20 where

import Prelude hiding (not)
import Data.Maybe
import Data.Typeable


-- We want to say:
--
--    data D where Lam :: (D -> D) -> D
--
-- but if we did this alone, we'd have no way to observe any value
-- of type D; the only thing we'd be able to do would be to feed it
-- another D as input, to no (observable) avail. So, we dirty our
-- abstraction as below.

data D x where
  Lam :: (D x -> D x) -> D x

  -- for observing convenience only...
  Prim :: (x -> x) -> D x
  Base :: x -> D x

-- For niceness when constructing terms
λ = Lam

unD :: D x -> (D x -> D x)
unD (Lam d) = d

-- the ugly cases...
unD (Prim f) = \case
  Base x -> Base (f x)
  Lam _ -> error "cannot apply primitive operation to lambda"
  Prim _ -> error "cannot apply primitive operation to another primitive operation"
unD (Base _) = error "cannot apply primitive type as a function"

infixl 9 ·
(·) :: D x -> D x -> D x
(·) = unD



-- Manipulating isomorphisms within a Scott domain

class Scotty x t | t -> x where
  scrunch :: t -> D x
  stretch :: D x -> t

instance Scotty x (D x) where
  scrunch = id
  stretch = id

instance (Scotty x t, Scotty x s) => Scotty x (t -> s) where
  scrunch f = Lam (scrunch . f . stretch)
  stretch f = stretch . unD f . scrunch

-- "Beam me up, Dr. Scott!"
beam :: forall x t s. (Scotty x t, Scotty x s) => t -> s
beam = stretch . scrunch

type E = D Integer

example :: E -> (E -> (E -> E) -> E) -> ((E -> E) -> E) -> ((E -> E) -> E)
example = beam (Lam id)



-- "Take me to church!"

toChurchNum :: (Ord x, Num x) => x -> D x
toChurchNum x | x > 0  = inc · toChurchNum (x - 1)
toChurchNum x | x <= 0 = zero

fromChurchNum :: (Enum x, Num x) => D x -> x
fromChurchNum f =
  case f · Prim succ · Base 0 of
    Base x -> x
    Prim _ -> error "can't convert primitive operation to base type"
    Lam _ -> error $ "you can take the church out of the lambda, " ++
                     "but you can't take the lambda out of the church"

-- natural numbers

zero = λ $ \s ->
       λ $ \z -> z

inc = λ $ \n ->
      λ $ \s ->
      λ $ \z ->
        --n · s · (s · z)
        s · (n · s · z)

dec = λ $ \n ->
      λ $ \s ->
      λ $ \z ->
        n · (λ $ \g -> λ $ \h -> h · (g · s))
          · (λ $ \u -> z)
          · (λ $ \u -> u)

plus = λ $ \m -> λ $ \n ->
       λ $ \s -> λ $ \z ->
         m · s · (n · s · z)

times = λ $ \m -> λ $ \n ->
        λ $ \s -> λ $ \z ->
          m · (n · s) · z

-- booleans

true  = λ $ \f ->
        λ $ \t -> t

false = λ $ \f ->
        λ $ \t -> f

not = λ $ \b ->
      λ $ \f ->
      λ $ \t ->
        b · t · f

isZero = λ $ \n ->
           n · (λ $ \_ -> true) · false

leq = λ $ \m ->
      λ $ \n ->
        isZero · (n · dec · m)

even = λ $ \n -> n · not · true

-- lists

nil = λ $ \c -> λ $ \n -> n

cons = λ $ \x -> λ $ \xs ->
       λ $ \c -> λ $ \n ->
         c · x · (xs · c · n)

-- What's the pattern? Hmm...

-- Encoding general recursion

-- This won't work in Haskell, because it fails the *occurs-check*:
-- yy = \f -> (\g -> f (g g)) (\g -> f (g g))

-- However, with the -rectypes flag, its analogue in OCaml will type-check:
--
--     fun f -> (fun g -> f (g g)) (fun g -> f (g g))
--
-- (but as discussed last class, that variant is too strict in a CBV language
-- like OCaml, so it won't terminate and you need a CBV version instead):
--
--     fun f -> (fun x a -> f (x x) a) (fun x a -> f (x x) a);;
--
-- Regardless, we can embed the y-combinator in Haskell, even though
-- Haskell has the occurs-check!

y = λ $ \f -> (λ $ \g -> f · (g · g))
            · (λ $ \g -> f · (g · g))

factorial =
  y · (λ $ \f -> λ $ \n ->
         isZero · n
         · (inc · zero)
         · (times · n · (f · (dec · n))))



-- Okay, but show me something new!

ackermann' 0 n = n + 1
ackermann' m 0 = ackermann' (m - 1) 1
ackermann' m n = ackermann' (m - 1) (ackermann' m (n - 1))

ackermann =
  y · (λ $ \a -> λ $ \m -> λ $ \n ->
         isZero · m
         · (inc · n)
         · (isZero · n
            · (a · (dec · m) · (inc · zero))
            · (a · (dec · m) · (a · m · (dec · n)))))



-- Random junk to make REPL interaction more convenient

instance Show x => Show (D x) where
  show (Lam _) = "Lam _"
  show (Prim _) = "Prim _"
  show (Base x) = "Base " ++ show x

instance (Ord x, Num x) => Num (D x) where
  fromInteger = toChurchNum . fromInteger
  (+)    = error "not implemented"
  (*)    = error "not implemented"
  (-)    = error "not implemented"
  abs    = error "not implemented"
  signum = error "not implemented"
