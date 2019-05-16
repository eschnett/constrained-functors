{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Control.Constrained.Category
  ( -- * Categories
    ObjKind, MorKind, CatKind
  , Semigroupoid(..)
  , law_Semigroupoid_assoc
  , Category(..)
  , law_Category_leftId
  , law_Category_rightId
  , SubCatOf(..)
  , law_SubCatOf_embedId
  , HaskSubCat
  , eval
    -- * Cartesian categories
  , Cartesian(..)
  , const
  , runUnitArrow
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
    -- * Cocartesian categories
  , Cocartesian(..)
  , law_Cocartesian_leftZero1
  , law_Cocartesian_leftZero2
  , law_Cocartesian_rightZero1
  , law_Cocartesian_rightZero2
  , law_Cocartesian_assoc
  , law_Cocartesian_reassoc
  , law_Cocartesian_swap
  , law_Cocartesian_leftJoin
  , law_Cocartesian_rightJoin
  , law_Cocartesian_jam
    -- * Closed categories
  , Closed(..)
  , law_Closed_apply
  , law_Closed_curry
  , law_Closed_uncurry
  ) where

import Prelude hiding ((.), const, curry, id, uncurry)
import qualified Prelude as P

import Data.Constraint
import Data.Kind
import Data.Void hiding (absurd)
import qualified Data.Void



--------------------------------------------------------------------------------



-- | The kind of an object
type ObjKind = Type -> Constraint
-- | The kind of a morphism
type MorKind = Type -> Type -> Type
-- | The kind of a category
type CatKind = MorKind



-- | A Semigroupoid is a Category without identity morphisms
class Semigroupoid (k :: CatKind) where
  -- | Objects in the category are defined by a constraint
  type Ok k :: ObjKind
  (.) :: Ok k a => Ok k b => Ok k c => k b c -> k a b -> k a c

-- | A Category is defined by its morphisms
-- TODO: Not all categories are subcategories of Hask -- can't have 'eval'!
class Semigroupoid k => Category (k :: CatKind) where
  id :: Ok k a => k a a

-- | A subcategory
-- A subcategories is a functors, but there is no data type associated with it.
class (Category k, Category l) => SubCatOf k l where
  proveSubCatOf :: Ok k a :- Ok l a
  embed :: Ok k a => Ok k b => k a b -> l a b

-- | A subcategory of Hask, where functions can be evaluated
class SubCatOf k (->) => HaskSubCat k
instance SubCatOf k (->) => HaskSubCat k

eval :: forall k a b.
        HaskSubCat k => Ok k a => Ok k b => k a b -> a -> b
eval = embed
       \\ proveSubCatOf @k @(->) @a



law_Semigroupoid_assoc :: Category k => Ok k a => Ok k b => Ok k c => Ok k d
                       => k c d -> k b c -> k a b -> (k a d, k a d)
law_Semigroupoid_assoc h g f = ((h . g) . f, h . (g . f))

law_Category_leftId :: Category k => Ok k a => Ok k b
                    => k a b -> (k a b, k a b)
law_Category_leftId f = (id . f, f)

law_Category_rightId :: Category k => Ok k a => Ok k b
                     => k a b -> (k a b, k a b)
law_Category_rightId f = (f . id, f)

law_SubCatOf_embedId :: forall k l a. SubCatOf k l => Ok k a
                       => (l a a, l a a)
law_SubCatOf_embedId = (id @l, embed (id @k))
                       \\ proveSubCatOf @k @l @a

-- TODO: also prove functor composition...



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



-- | A Cocartesian category has coproducts (sums)
class (Category k, Ok k (Zero k)) => Cocartesian k where
  {-# MINIMAL proveCocartesian, coprod, inl, inr, (join | jam), absurd, lzero,
              rzero, coassoc, coreassoc, coswap #-}

  -- | Prove that the category is Cartesian, i.e. that the coproduct
  -- is an object in the category
  proveCocartesian :: (Ok k a, Ok k b) :- Ok k (Coproduct k a b)

  -- | The category's coproduct (sum) type
  -- prop> s z a -> a                   -- lzero
  -- prop> s a z -> a                   -- rzero
  -- prop> s (s a b) c -> s a (s b c)   -- coassoc
  -- prop> s a (s b c) -> s (s a b) c   -- coreassoc
  -- prop> s a b -> s b a               -- coswap
  type Coproduct k :: Type -> Type -> Type

  -- | A zero type for this coproduct
  type Zero k :: Type

  -- | Bi-map over a coproduct
  coprod :: s ~ Coproduct k => Ok k a => Ok k b => Ok k c => Ok k d
         => k a c -> k b d -> k (s a b) (s c d)

  -- | Inject left object into a coproduct
  -- prop> join f g . inl = f
  inl :: forall a b s. s ~ Coproduct k => Ok k a => Ok k b => k a (s a b)
  -- | Inject right object into a coproduct
  -- prop> join f g . inr = g
  inr :: forall a b s. s ~ Coproduct k => Ok k a => Ok k b => k b (s a b)

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

  lzero :: s ~ Coproduct k => z ~ Zero k => Ok k a => k (s z a) a
  rzero :: s ~ Coproduct k => z ~ Zero k => Ok k a => k (s a z) a
  coassoc :: s ~ Coproduct k => Ok k a => Ok k b => Ok k c
          => k (s (s a b) c) (s a (s b c))
  coreassoc :: s ~ Coproduct k => Ok k a => Ok k b => Ok k c
            => k (s a (s b c)) (s (s a b) c)
  coswap :: s ~ Coproduct k => Ok k a => Ok k b => k (s a b) (s b a)



law_Cocartesian_leftZero1 :: forall k a s z.
                             Cocartesian k => s ~ Coproduct k => z ~ Zero k
                          => Ok k a
                          => (k a a, k a a)
law_Cocartesian_leftZero1 = (id, lzero @k . inr @k @z @a)
                            \\ proveCocartesian @k @z @a

law_Cocartesian_leftZero2 :: forall k a s z.
                             Cocartesian k => s ~ Coproduct k => z ~ Zero k
                          => Ok k a
                          => (k (s z a) (s z a), k (s z a) (s z a))
law_Cocartesian_leftZero2 = (id, inr @k . lzero @k)
                            \\ proveCocartesian @k @z @a

law_Cocartesian_rightZero1 :: forall k a s z.
                              Cocartesian k => s ~ Coproduct k => z ~ Zero k
                           => Ok k a
                           => (k a a, k a a)
law_Cocartesian_rightZero1 = (id, rzero @k . inl @k @a @z)
                             \\ proveCocartesian @k @a @z

law_Cocartesian_rightZero2 :: forall k a s z.
                              Cocartesian k => s ~ Coproduct k => z ~ Zero k
                           => Ok k a
                           => (k (s a z) (s a z), k (s a z) (s a z))
law_Cocartesian_rightZero2 = (id, inl @k . rzero @k)
                             \\ proveCocartesian @k @a @z

law_Cocartesian_assoc :: forall k a b c s.
                         Cocartesian k
                      => s ~ Coproduct k => Ok k a => Ok k b => Ok k c
                      => ( k (s (s a b) c) (s (s a b) c)
                         , k (s (s a b) c) (s (s a b) c)
                         )
law_Cocartesian_assoc = (id, coreassoc @k . coassoc @k)
                        \\ proveCocartesian @k @(s a b) @c
                        \\ proveCocartesian @k @a @(s b c)
                        \\ proveCocartesian @k @a @b
                        \\ proveCocartesian @k @b @c

law_Cocartesian_reassoc :: forall k a b c s.
                           Cocartesian k
                        => s ~ Coproduct k => Ok k a => Ok k b => Ok k c
                        => ( k (s a (s b c)) (s a (s b c))
                           ,  k (s a (s b c)) (s a (s b c))
                           )
law_Cocartesian_reassoc = (id, coassoc @k . coreassoc @k)
                          \\ proveCocartesian @k @(s a b) @c
                          \\ proveCocartesian @k @a @(s b c)
                          \\ proveCocartesian @k @a @b
                          \\ proveCocartesian @k @b @c

law_Cocartesian_swap :: forall k a b s.
                        Cocartesian k => s ~ Coproduct k => Ok k a => Ok k b
                     => (k (s a b) (s a b), k (s a b) (s a b))
law_Cocartesian_swap = (id, coswap @k . coswap @k)
                       \\ proveCocartesian @k @b @a
                       \\ proveCocartesian @k @a @b

law_Cocartesian_leftJoin :: forall k a b c s.
                            Cocartesian k => s ~ Coproduct k
                         => Ok k a => Ok k b => Ok k c
                         => k a c -> k b c -> (k a c, k a c)
law_Cocartesian_leftJoin f g = (f, join f g . inl)
                               \\ proveCocartesian @k @a @b

law_Cocartesian_rightJoin :: forall k a b c s.
                             Cocartesian k => s ~ Coproduct k
                          => Ok k a => Ok k b => Ok k c
                          => k a c -> k b c -> (k b c, k b c)
law_Cocartesian_rightJoin f g = (g, join f g . inr)
                                \\ proveCocartesian @k @a @b

law_Cocartesian_jam :: forall k a s.
                       Cocartesian k => s ~ Coproduct k => Ok k a
                    => (k (s a a) a, k (s a a) a)
law_Cocartesian_jam = (jam, join id id)



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

law_Closed_apply :: forall k a b c p. Closed k => p ~ Product k
                 => Ok k a => Ok k b => Ok k c
                 => k (p a b) c -> (k (p a b) c, k (p a b) c)
law_Closed_apply f = (f, apply @k . fork (curry @k f . exl) exr)
                     \\ proveCartesian @k @a @b
                     \\ proveCartesian @k @(k b c) @b
                     \\ proveClosed @k @b @c

law_Closed_curry :: Closed k => p ~ Product k => Ok k a => Ok k b => Ok k c
                 => k (p a b) c -> (k (p a b) c, k (p a b) c)
law_Closed_curry f = (f, uncurry (curry f))

law_Closed_uncurry :: Closed k => Ok k a => Ok k b => Ok k c
                   => k a (k b c) -> (k a (k b c), k a (k b c))
law_Closed_uncurry f = (f, curry (uncurry f))



--------------------------------------------------------------------------------



class True1 a
instance True1 a

-- | Hask
instance Semigroupoid (->) where
  type Ok (->) = True1
  (.) = (P..)

instance Category (->) where
  id = P.id

instance SubCatOf (->) (->) where
  proveSubCatOf = Sub Dict
  embed = P.id

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

  lzero = \case Left _ -> error "Void"
                Right x -> x
  rzero = \case Left x -> x
                Right _ -> error "Void"
  coassoc = \case Left (Left x) -> Left x
                  Left (Right y) -> Right (Left y)
                  Right z -> Right (Right z)
  coreassoc = \case Left x -> Left (Left x)
                    Right (Left y) -> Left (Right y)
                    Right (Right z) -> Right z
  coswap = \case Left x -> Right x
                 Right y -> Left y

instance Closed (->) where
  proveClosed = Sub Dict
  apply = \(f, x) -> f x
  curry = P.curry
  uncurry = P.uncurry
