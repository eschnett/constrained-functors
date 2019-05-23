{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Control.Constrained.Cartesian
  ( -- * Cartesian categories
    Cartesian(..)
  , const
  , runUnitArrow
  , mkProd
  , SubCartOf(..)
  , law_Cartesian_leftUnit1
  , law_Cartesian_leftUnit2
  , law_Cartesian_rightUnit1
  , law_Cartesian_rightUnit2
  , law_Cartesian_assoc
  , law_Cartesian_reassoc
  , law_Cartesian_swap
  , law_Cartesian_leftFork
  , law_Cartesian_rightFork
  , law_Cartesian_dup
  ) where

import qualified Prelude as P
import Control.Constrained.Prelude

import Control.Constrained.Category
import Data.Constraint
import Data.Kind



--------------------------------------------------------------------------------



-- | A Cartesian category has products
class (Category k, Ok k (Unit k)) => Cartesian k where
  {-# MINIMAL proveCartesian, prod, unit, exl, exr, (fork | dup), it, unitArrow,
              lunit, runit, assoc, reassoc, swap #-}

  -- | Prove that the category is Cartesian, i.e. that the product is
  -- an object in the category
  proveCartesian :: forall a b. (Ok k a, Ok k b) :- Ok k (Product k a b)

  -- | The category's product type
  -- prop> a -> p u a                   -- lunit
  -- prop> a -> p a u                   -- runit
  -- prop> p (p a b) c -> p a (p b c)   -- assoc
  -- prop> p a (p b c) -> p (p a b) c   -- reassoc
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

  lunit :: p ~ Product k => u ~ Unit k => Ok k a => k a (p u a)
  runit :: p ~ Product k => u ~ Unit k => Ok k a => k a (p a u)
  assoc :: p ~ Product k => Ok k a => Ok k b => Ok k c
        => k (p (p a b) c) (p a (p b c))
  reassoc :: p ~ Product k => Ok k a => Ok k b => Ok k c
          => k (p a (p b c)) (p (p a b) c)
  swap :: p ~ Product k => Ok k a => Ok k b => k (p a b) (p b a)

const :: forall k a b. Cartesian k => Ok k a => Ok k b => a -> k b a
const x = unitArrow x . it

runUnitArrow :: forall k a u.
                Cartesian k => HaskSubCat k => u ~ Unit k => Ok k a
             => k u a -> a
runUnitArrow f = eval f (unit @k)

mkProd :: forall k a b p.
          Cartesian k => HaskSubCat k => p ~ Product k => Ok k a => Ok k b
       => a -> b -> p a b
mkProd x y = runUnitArrow (fork @k (unitArrow x) (unitArrow y))
             \\ proveCartesian @k @a @b

class (k `SubCatOf` l, Cartesian k, Cartesian l) => SubCartOf k l where
  embedProd :: Ok k a => Ok k b => Product k a b -> Product l a b

instance Cartesian k => SubCartOf k k where
  embedProd = id



law_Cartesian_leftUnit1 :: forall k a u.
                           Cartesian k => u ~ Unit k => Ok k a
                        => (k a a, k a a)
law_Cartesian_leftUnit1 = (id, exr @k . lunit @k)
                          \\ proveCartesian @k @u @a

law_Cartesian_leftUnit2 :: forall k a p u.
                           Cartesian k => p ~ Product k => u ~ Unit k => Ok k a
                        => (k (p u a) (p u a), k (p u a) (p u a))
law_Cartesian_leftUnit2 = (id, lunit @k . exr @k)
                          \\ proveCartesian @k @u @a

law_Cartesian_rightUnit1 :: forall k a u.
                            Cartesian k => u ~ Unit k => Ok k a
                         => (k a a, k a a)
law_Cartesian_rightUnit1 = (id, exl @k . runit @k)
                           \\ proveCartesian @k @a @u

law_Cartesian_rightUnit2 :: forall k a p u.
                            Cartesian k => p ~ Product k => u ~ Unit k => Ok k a
                         => (k (p a u) (p a u), k (p a u) (p a u))
law_Cartesian_rightUnit2 = (id, runit @k . exl @k)
                           \\ proveCartesian @k @a @u

law_Cartesian_assoc :: forall k a b c p.
                       Cartesian k => p ~ Product k
                    => Ok k a => Ok k b => Ok k c
                    => ( k (p (p a b) c) (p (p a b) c)
                       , k (p (p a b) c) (p (p a b) c)
                       )
law_Cartesian_assoc = (id, reassoc @k . assoc @k)
                      \\ proveCartesian @k @(p a b) @c
                      \\ proveCartesian @k @a @(p b c)
                      \\ proveCartesian @k @a @b
                      \\ proveCartesian @k @b @c

law_Cartesian_reassoc :: forall k a b c p.
                         Cartesian k => p ~ Product k
                      => Ok k a => Ok k b => Ok k c
                      => ( k (p a (p b c)) (p a (p b c))
                         , k (p a (p b c)) (p a (p b c))
                         )
law_Cartesian_reassoc = (id,  assoc @k . reassoc @k)
                        \\ proveCartesian @k @(p a b) @c
                        \\ proveCartesian @k @a @(p b c)
                        \\ proveCartesian @k @a @b
                        \\ proveCartesian @k @b @c

law_Cartesian_swap :: forall k a b p.
                      Cartesian k => p ~ Product k => Ok k a => Ok k b
                   => (k (p a b) (p a b), k (p a b) (p a b))
law_Cartesian_swap = (id,  swap @k . swap @k)
                     \\ proveCartesian @k @b @a
                     \\ proveCartesian @k @a @b

law_Cartesian_leftFork :: forall k a b c p.
                          Cartesian k => p ~ Product k
                       => Ok k a => Ok k b => Ok k c
                       => k a b -> k a c -> (k a b, k a b)
law_Cartesian_leftFork f g = (f, exl . fork f g)
                             \\ proveCartesian @k @b @c

law_Cartesian_rightFork :: forall k a b c p.
                           Cartesian k => p ~ Product k
                        => Ok k a => Ok k b => Ok k c
                        => k a b -> k a c -> (k a c, k a c)
law_Cartesian_rightFork f g = (g, exr . fork f g)
                              \\ proveCartesian @k @b @c

law_Cartesian_dup :: forall k a p.
                     Cartesian k => p ~ Product k => Ok k a
                  => (k a (p a a), k a (p a a))
law_Cartesian_dup = (fork id id, dup)



--------------------------------------------------------------------------------



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
  lunit x = ((), x)
  runit x = (x, ())
  assoc ((x, y), z) = (x, (y, z))
  reassoc (x, (y, z)) = ((x, y), z)
  swap (x, y) = (y, x)
