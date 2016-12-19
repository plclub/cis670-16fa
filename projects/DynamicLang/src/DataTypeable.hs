{-# LANGUAGE RankNTypes, PolyKinds, TypeOperators, ScopedTypeVariables,
             GADTs, MultiParamTypeClasses, ConstraintKinds,
             FunctionalDependencies, FlexibleContexts,
             AllowAmbiguousTypes,
             FlexibleInstances, TypeInType, UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-missing-methods #-}

module DataTypeable where

import GHC.Types hiding (TyCon)
import Unsafe.Coerce (unsafeCoerce)


-- |Data.Typeable| ------------------------------------------------------------

class Typeable (a :: k) where
   typeRep :: TypeRep a
   -- Typeable instances automatically generated for all type constructors

-- Note: type representations are polykinded

trInt :: TypeRep Int
trInt = typeRep

trInte :: TypeRep Integer
trInte = typeRep

trBool :: TypeRep Bool
trBool = typeRep

trChar :: TypeRep Char
trChar = typeRep

trArrow :: TypeRep (->)
trArrow = typeRep

trList :: TypeRep []
trList = typeRep

trString :: TypeRep String
trString = typeRep

trTuple :: TypeRep (,)
trTuple = typeRep

trIAI :: TypeRep (Int -> Int)
trIAI = typeRep

-------------------------------------------------------------------------------
-- type-aware equality

-- Informative propositional equality
data (a :: k1) :~~: (b :: k2) where
  Refl :: forall k (a :: k). a :~~: a

eqT :: forall k1 k2 (a :: k1) (b :: k2). TypeRep a -> TypeRep b -> Maybe (a :~~: b)
eqT = primitiveEqT

-------------------------------------------------------------------------------
-- type-safe cast

cast :: forall a b. (Typeable a, Typeable b) => a -> Maybe b
cast x = case eqT (typeRep :: TypeRep a) (typeRep :: TypeRep b) of
  Just Refl -> Just x
  Nothing   -> Nothing

gcast :: forall a b c. (Typeable a, Typeable b) => c a -> Maybe (c b)
gcast x = case eqT (typeRep :: TypeRep a) (typeRep :: TypeRep b) of
  Just Refl -> Just x
  Nothing   -> Nothing

-------------------------------------------------------------------------------
-- split-app

-- pattern matching
splitApp :: TypeRep a -> Maybe (AppResult a)
splitApp (TApp t1 t2) = Just $ App t1 t2
splitApp _ = Nothing

data AppResult (t :: k) where
  App :: TypeRep a -> TypeRep b -> AppResult (a b)



data TypeRep (a :: k) where
  TR   :: TyCon a   -> TypeRep a
  TApp :: TypeRep a -> TypeRep b -> TypeRep (a b)



{-------------- withTypeable (horrible hack) -------------------}

newtype NT a r = NT (Typeable a => Proxy a -> r)

-- | withTypeable takes a TypeRep a, and a function
-- | that has Typeable a constraint and uses our TypeRep a to generate
-- | the necessary Typeable contraint?
withTypeable ::  forall a r. TypeRep a -> (Typeable a => r) -> r
withTypeable a f = withTypeable' a (\ _ -> f)

withTypeable' :: forall a r. TypeRep a -> (Typeable a => Proxy a -> r) -> r
withTypeable' a f = unsafeCoerce (NT f :: NT a r) a Proxy
{-# INLINE withTypeable #-}

-- existential version
data TypeRepX where
   TypeRepX :: TypeRep a -> TypeRepX
instance Eq    TypeRepX
instance Ord   TypeRepX
instance Show  TypeRepX

kindRep :: TypeRep (a :: k) -> TypeRep k
kindRep (TR (TC kr _)) = kr
kindRep (TApp t1 _) = undefined {- case kindRep t1 of
  (TApp (TApp _ kr) _) -> kr
  _ -> error "BUG!" -}




-- construction
mkTyApp :: TypeRep a -> TypeRep b -> TypeRep (a b)
mkTyApp = TApp


tyConName     :: TypeRep a -> String
tyConName (TR (TC _ n)) = n
tyConName (TApp t1 _)   = tyConName t1


gcastR :: forall a b c. TypeRep a -> TypeRep b -> c a -> Maybe (c b)
gcastR ra rb x = case eqT ra rb of
  Just Refl -> Just x
  Nothing   -> Nothing


{-
toDyn :: Typeable a => a -> Dynamic
toDyn x = Dyn typeRep x
showDynTypeRep :: Dynamic -> String
showDynTypeRep (Dyn ra (x :: a)) = show ra
instance Typeable Dynamic where typeRep = TR $ TC ty "Dynamic"
-}

data Proxy a where
  Proxy :: Proxy a


---------------------------------------------------------------------
-- Dirty laundry past this point.

data TyCon (a :: k) =
  TC (TypeRep k) String

instance Show  (TypeRep a) where
  show (TR (TC _ ty))      = ty

  show (TApp (TApp t1 t2) t3)
                    | Just Refl <- eqT t1 (typeRep :: TypeRep (->)) = show t2 ++ " -> " ++ show t3

  show (TApp t1 t2) | Just Refl <- eqT t1 (typeRep :: TypeRep []),
                      Just Refl <- eqT t2 (typeRep :: TypeRep Char) = "String"

  show (TApp t1 t2@(TR _)) = show t1 ++ " " ++ show t2
  show (TApp t1 t2)        = show t1 ++ " (" ++ show t2  ++ ")"

ty :: TypeRep Type
ty = TR $ TC ty "Type"

tyM :: TypeRep Maybe
tyM = TR $ TC tyTT "Maybe"

tyTT :: TypeRep (Type -> Type)
tyTT = TApp (TApp tyA ty) ty

tyA :: TypeRep (->)
tyA = TR $ TC tyTTT "(->)"

tyTTT :: TypeRep (Type -> (Type -> Type))
tyTTT = TApp (TApp tyA ty) (TApp (TApp tyA ty) ty)

instance Typeable (Type :: Type) where
  typeRep = ty

instance Typeable Int where typeRep = TR $ TC ty "Int"
instance Typeable Integer where typeRep = TR $ TC ty "Integer"
instance Typeable Bool where typeRep = TR $ TC ty "Bool"
instance Typeable (->) where typeRep = tyA
instance Typeable (,) where typeRep = TR $ TC tyTTT "(,)"
instance (Typeable (a :: k1 -> k2), Typeable (b :: k1)) => Typeable (a b) where
  typeRep = TApp typeRep typeRep
instance Typeable Maybe where typeRep = tyM
instance Typeable Either where typeRep = TR $ TC tyTTT "Either"
instance Typeable Char where typeRep = TR $ TC ty "Char"
instance Typeable [] where typeRep = TR $ TC tyTT "[]"

primitiveEqT   :: forall k1 k2 (a :: k1) (b :: k2). TypeRep a -> TypeRep b -> Maybe (a :~~: b)
primitiveEqT (TR (TC _ s1))  (TR (TC _ s2)) | s1 == s2 = unsafeCoerce (Just Refl)
primitiveEqT (TApp ta1 ta2) (TApp tb1 tb2) = do
  Refl <- primitiveEqT ta1 tb1
  Refl <- primitiveEqT ta2 tb2
  return Refl
primitiveEqT _ _ = Nothing
