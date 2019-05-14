{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Control.Constrained.Category
  ( -- * Categories
    ObjKind, MorKind, CatKind
  , Category(..)
    -- * Cartesian, cocartesian, and closed categories
  , Cartesian(..)
  , const
  , runUnitArrow
  , Cocartesian(..)
  , Closed(..)
  ) where

import Prelude hiding (id, (.), const, curry, uncurry)
import qualified Prelude as P

import Data.Constraint
import Data.Kind
import Data.Void



--------------------------------------------------------------------------------



-- | The kind of an object
type ObjKind = Type -> Constraint
-- | The kind of a morphism
type MorKind = Type -> Type -> Type
-- | The kind of a category
type CatKind = MorKind



-- | A Category is defined by its morphisms
class Category (k :: CatKind) where
  -- | Objects in the category are defined by a constraint
  type Ok k :: ObjKind
  id :: Ok k a => k a a
  (.) :: Ok k a => Ok k b => Ok k c => k b c -> k a b -> k a c
  eval :: Ok k a => Ok k b => k a b -> a -> b



--------------------------------------------------------------------------------



-- | A Cartesian category has products
class (Category k, Ok k (Unit k)) => Cartesian k where
  {-# MINIMAL proveCartesian, prod, unit, exl, exr, (fork | dup), it,
              unitArrow #-}

  -- | Prove that the category is Cartesian, i.e. that the product is
  -- an object in the category
  proveCartesian :: forall a b. (Ok k a, Ok k b) :- Ok k (Product k a b)

  -- | The category's product type
  -- prop> a -> (p u a)                 -- lunit
  -- prop> a -> (p a u)                 -- runit
  -- prop> p a (p b c) -> p (p a b) c   -- assoc
  -- prop> p (p a b) c -> p a (p b c)   -- reassoc
  -- prop> p a b -> p b a               -- swap
  type Product k :: Type -> Type -> Type
  -- | A unit type for this product
  type Unit k :: Type

  -- | Bi-map over a product
  prod :: p ~ Product k => Ok k a => Ok k b => Ok k c => Ok k d
       => k a c -> k b d -> k (p a b) (p c d)
  -- | The unit
  unit :: u ~ Unit k => u

  -- | Extract left object from a product
  -- prop> exl . fork f g = f
  exl :: p ~ Product k => Ok k a => Ok k b => k (p a b) a
  -- | Extract right object from a product
  -- prop> exr . fork f g = g
  exr :: p ~ Product k => Ok k a => Ok k b => k (p a b) b

  -- | Create a product from two morphisms
  fork :: forall a b c p.
          p ~ Product k => Ok k a => Ok k b => Ok k c
       => k a b -> k a c -> k a (p b c)
  fork f g = prod f g . dup
             \\ proveCartesian @k @a @a *** proveCartesian @k @b @c

  -- | Duplicate an object into a product
  dup :: p ~ Product k => Ok k a => k a (p a a)
  dup = fork id id

  -- | Map any object to the unit object
  it :: u ~ Unit k => Ok k a => k a u

  -- | A value is equivalent to a morphism from the unit
  unitArrow :: u ~ Unit k => Ok k a => a -> k u a

const :: forall k a b. Cartesian k => Ok k a => Ok k b => a -> k b a
const x = unitArrow x . it

runUnitArrow :: forall k a u. Cartesian k => u ~ Unit k => Ok k a => k u a -> a
runUnitArrow f = eval f (unit @k)



--------------------------------------------------------------------------------



-- | A Cocartesian category has coproducts (sums)
class (Category k, Ok k (Zero k)) => Cocartesian k where
  {-# MINIMAL proveCocartesian, coprod, inl, inr, (join | jam), absurd #-}

  -- | Prove that the category is Cartesian, i.e. that the coproduct
  -- is an object in the category
  proveCocartesian :: (Ok k a, Ok k b) :- Ok k (Coproduct k a b)

  -- | The category's coproduct (sum) type
  -- prop> a -> (s z a)                 -- lzero
  -- prop> a -> (s a z)                 -- rzero
  -- prop> s a (s b c) -> s (s a b) c   -- coassoc
  -- prop> s (s a b) c -> s a (s b c)   -- coreassoc
  -- prop> s a b -> s b a               -- coswap
  type Coproduct k :: Type -> Type -> Type

  -- | A zero type for this coproduct
  type Zero k :: Type

  -- | Bi-map over a coproduct
  coprod :: s ~ Coproduct k => Ok k a => Ok k b => Ok k c => Ok k d
         => k a c -> k b d -> k (s a b) (s c d)

  -- | Inject left object into a coproduct
  inl :: s ~ Coproduct k => Ok k a => Ok k b => k a (s a b)
  -- | Inject right object into a coproduct
  inr :: s ~ Coproduct k => Ok k a => Ok k b => k b (s a b)

  -- | Create a coproduct from two morphisms
  join :: forall a b c s.
          s ~ Coproduct k => Ok k a => Ok k b => Ok k c
       => k a c -> k b c -> k (s a b) c
  join f g = jam . coprod f g
             \\ proveCocartesian @k @a @b *** proveCocartesian @k @c @c

  -- | Extract an object from a duplicate coproduct
  jam :: s ~ Coproduct k => Ok k a => k (s a a) a
  jam = join id id

  -- | Map the zero object to any object
  absurd :: z ~ Zero k => Ok k a => k z a



--------------------------------------------------------------------------------



-- | A closed category has exponentials, i.e. morphisms are objects
class Cartesian k => Closed k where
  -- | Prove that the category is closed, i.e. that morphisms are
  -- objects in the category
  proveClosed :: (Ok k a, Ok k b) :- Ok k (k a b)

  -- | Apply a function
  -- prop> apply . (curry f . fork exl exr) = f
  apply :: p ~ Product k => Ok k a => Ok k b => k (p (k a b) a) b

  -- | Curry a function
  curry :: p ~ Product k => Ok k a => Ok k b => Ok k c
        => k (p a b) c -> k a (k b c)
  -- | Uncurry a function
  uncurry :: p ~ Product k => Ok k a => Ok k b => Ok k c
          => k a (k b c) -> k (p a b) c



--------------------------------------------------------------------------------



class True1 a
instance True1 a

-- | Hask
instance Category (->) where
  type Ok (->) = True1
  id = P.id
  (.) = (P..)
  eval = P.id

instance Cartesian (->) where
  proveCartesian = Sub Dict
  type Product (->) = (,)
  type Unit (->) = ()
  prod f g = \(x, y) -> (f x, g y)
  unit = ()
  exl = fst
  exr = snd
  fork f g = \x -> (f x, g x)
  it = P.const ()
  unitArrow = P.const

instance Cocartesian (->) where
  proveCocartesian = Sub Dict
  type Coproduct (->) = Either
  type Zero (->) = Void
  coprod f g = \case Left x -> Left (f x)
                     Right y -> Right (g y)
  inl = Left
  inr = Right
  join = either
  absurd = Data.Void.absurd

instance Closed (->) where
  proveClosed = Sub Dict
  apply = \(f, x) -> f x
  curry = P.curry
  uncurry = P.uncurry
