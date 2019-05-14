{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Control.Constrained.Category
  ( -- * Categories
    ObjKind, MorKind, CatKind
  , Category(..)
  , law_Category_evalId
  , law_Category_leftId
  , law_Category_rightId
  , law_Category_assoc
    -- * Cartesian, cocartesian, and closed categories
  , Cartesian(..)
  , CartesianLaws(..)
  , law_Cartesian_leftUnit1
  , law_Cartesian_leftUnit2
  , law_Cartesian_rightUnit1
  , law_Cartesian_rightUnit2
  , law_Cartesian_assoc
  , law_Cartesian_reassoc
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



law_Category_evalId :: forall k a. Category k => Ok k a
                    => a -> (a, a)
law_Category_evalId x = (x, eval @k id x)

law_Category_leftId :: Category k => Ok k a => Ok k b
                    => k a b -> (k a b, k a b)
law_Category_leftId f = (id . f, f)

law_Category_rightId :: Category k => Ok k a => Ok k b
                     => k a b -> (k a b, k a b)
law_Category_rightId f = (f . id, f)

law_Category_assoc :: Category k => Ok k a => Ok k b => Ok k c => Ok k d
                   => k c d -> k b c -> k a b -> (k a d, k a d)
law_Category_assoc h g f = ((h . g) . f, h . (g . f))



--------------------------------------------------------------------------------



-- | A Cartesian category has products
class (Category k, Ok k (Unit k)) => Cartesian k where
  {-# MINIMAL proveCartesian, prod, unit, exl, exr, (fork | dup), it,
              unitArrow #-}

  -- | Prove that the category is Cartesian, i.e. that the product is
  -- an object in the category
  proveCartesian :: forall a b. (Ok k a, Ok k b) :- Ok k (Product k a b)

  -- | The category's product type
  -- prop> a -> p u a                   -- lunit
  -- prop> a -> p a u                   -- runit
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



class Cartesian k => CartesianLaws k where
  lunit :: p ~ Product k => u ~ Unit k => Ok k a => a -> p u a
  runit :: p ~ Product k => u ~ Unit k => Ok k a => a -> p a u
  assoc :: p ~ Product k => Ok k a => Ok k b => Ok k c
        => p a (p b c) -> p (p a b) c
  reassoc :: p ~ Product k => Ok k a => Ok k b => Ok k c
          => p (p a b) c -> p a (p b c)
  swap :: p ~ Product k => Ok k a => Ok k b => p a b -> p b a

law_Cartesian_leftUnit1 :: forall k a p u.
                           CartesianLaws k => p ~ Product k => u ~ Unit k
                        => Ok k a
                        => a -> (a, a)
law_Cartesian_leftUnit1 x = (x, eval (exr @k) (lunit @k x))
                            \\ proveCartesian @k @u @a

law_Cartesian_leftUnit2 :: forall k a p u.
                           CartesianLaws k => p ~ Product k => u ~ Unit k
                        => Ok k a
                        => p u a -> (p u a, p u a)
law_Cartesian_leftUnit2 p = (p, lunit @k (eval @k exr p))
                            \\ proveCartesian @k @u @a

law_Cartesian_rightUnit1 :: forall k a p u.
                            CartesianLaws k => p ~ Product k => u ~ Unit k
                         => Ok k a
                         => a -> (a, a)
law_Cartesian_rightUnit1 x = (x, eval (exl @k) (runit @k x))
                            \\ proveCartesian @k @a @u

law_Cartesian_rightUnit2 :: forall k a p u.
                            CartesianLaws k => p ~ Product k => u ~ Unit k
                         => Ok k a
                         => p a u -> (p a u, p a u)
law_Cartesian_rightUnit2 p = (p, runit @k (eval @k exl p))
                            \\ proveCartesian @k @a @u

law_Cartesian_assoc :: forall k a b c p.
                       CartesianLaws k
                    => p ~ Product k => Ok k a => Ok k b => Ok k c
                    => p a (p b c) -> (p a (p b c), p a (p b c))
law_Cartesian_assoc p = (p, (reassoc @k) (assoc @k p))

law_Cartesian_reassoc :: forall k a b c p.
                         CartesianLaws k
                      => p ~ Product k => Ok k a => Ok k b => Ok k c
                      => p (p a b) c -> (p (p a b) c, p (p a b) c)
law_Cartesian_reassoc p = (p, (assoc @k) (reassoc @k p))



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

instance CartesianLaws (->) where
  lunit = \x -> ((), x)
  runit = \x -> (x, ())
  assoc = \(x, (y, z)) -> ((x, y), z)
  reassoc = \((x, y), z) -> (x, (y, z))
  swap = \(x, y) -> (y, x)

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
