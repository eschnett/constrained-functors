{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Control.Constrained.Cocartesian
  ( -- * Cocartesian categories
    Cocartesian(..)
  , mkCoprod
  , SubCocartOf(..)
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
  ) where

import Prelude ()
import Control.Constrained.Prelude

import Control.Constrained.Category
import Data.Constraint
import Data.Kind
import Data.Void hiding (absurd)



--------------------------------------------------------------------------------



-- | A Cocartesian category has coproducts (sums)
class (Category k, Ok k (Zero k)) => Cocartesian k where
  {-# MINIMAL proveCocartesian, coprod, inl, inr, (join | jam), lzero, rzero,
              coassoc, coreassoc, coswap #-}

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
             \\ proveCocartesian @k @a @b
             \\ proveCocartesian @k @c @c

  -- | Extract an object from a duplicate coproduct
  jam :: s ~ Coproduct k => Ok k a => k (s a a) a
  jam = join id id

  -- | Map the zero object to any object
  absurd :: z ~ Zero k => Ok k a => k z a
  absurd = undefined

  -- | Create a value from nothing ("ex falso quodlibet")
  zeroArrow :: z ~ Zero k => Ok k a => k a z -> a
  zeroArrow _ = undefined

  lzero :: s ~ Coproduct k => z ~ Zero k => Ok k a => k (s z a) a
  rzero :: s ~ Coproduct k => z ~ Zero k => Ok k a => k (s a z) a
  coassoc :: s ~ Coproduct k => Ok k a => Ok k b => Ok k c
          => k (s (s a b) c) (s a (s b c))
  coreassoc :: s ~ Coproduct k => Ok k a => Ok k b => Ok k c
            => k (s a (s b c)) (s (s a b) c)
  coswap :: s ~ Coproduct k => Ok k a => Ok k b => k (s a b) (s b a)

mkCoprod :: forall k a b s.
            Cocartesian k => HaskSubCat k => s ~ Coproduct k => Ok k a => Ok k b
         => Either a b -> s a b
mkCoprod = \case Left x -> eval (inl @k) x
                 Right y -> eval (inr @k) y
           \\ proveCocartesian @k @a @b

class (k `SubCatOf` l, Cocartesian k, Cocartesian l) => SubCocartOf k l where
  embedCoprod :: Ok k a => Ok k b => Coproduct k a b -> Coproduct l a b

instance Cocartesian k => SubCocartOf k k where
  embedCoprod = id



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



instance Cocartesian (->) where
  proveCocartesian = Sub Dict
  type Coproduct (->) = Either
  type Zero (->) = Void
  coprod f g = \case Left x -> Left (f x)
                     Right y -> Right (g y)
  inl = Left
  inr = Right
  join = either

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
