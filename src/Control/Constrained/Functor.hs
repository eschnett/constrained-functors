{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Control.Constrained.Functor
  ( Functor(..)
  , Foldable(..)
  , Apply(..)
  , Applicative(..)
  , Traversable(..)
  , Monad(..)
  , (=<<), (>>=)
  , Comonad(..)
  ) where

import Prelude hiding ( id, (.), const, curry, uncurry
                      , Applicative(..), Foldable(..), Functor(..), Monad(..)
                      , Traversable(..)
                      , (=<<))

import Control.Constrained.Category hiding (fork, join)
import Data.Constraint
import Data.Functor.Identity
import qualified Data.Functor.Compose as F
import qualified Data.Functor.Product as F
import qualified Data.Functor.Sum as F
import Data.Proxy



-- | A functor
class (Category (Dom f), Category (Cod f)) => Functor f where
  -- | Prove that this functor maps from its domain to its codomain
  proveFunctor :: Ok (Dom f) a :- Ok (Cod f) (f a)
  -- | Domain
  type Dom f :: CatKind
  -- | Codomain
  type Cod f :: CatKind
  -- | Map a morphism
  fmap :: Ok (Dom f) a => Ok (Dom f) b => Dom f a b -> Cod f (f a) (f b)



--------------------------------------------------------------------------------



-- | A foldable functor
class Functor f => Foldable f where
  -- | Fold with a monoid
  foldMap :: Monoid b => Ok (Dom f) a => Ok (Dom f) b => Dom f a b -> f a -> b



--------------------------------------------------------------------------------



-- | An applicative functor without 'pure'
-- (lax monoidal functor)
class (Functor f, Cartesian (Dom f), Cartesian (Cod f)) => Apply f where
  {-# MINIMAL liftA2uu #-}
  -- | Map a morphism over a pair of functors
  liftA2uu :: p ~ Product (Dom f) => q ~ Product (Cod f)
           => Ok (Dom f) a => Ok (Dom f) b => Ok (Dom f) c
           => Dom f (p a b) c -> Cod f (q (f a) (f b)) (f c)
  liftA2u :: forall a b c.
             forall p. p ~ Product (Dom f)
          => Closed (Cod f)
          => Ok (Dom f) a => Ok (Dom f) b => Ok (Dom f) c
          => Dom f (p a b) c -> Cod f (f a) (Cod f (f b) (f c))
  liftA2u f = curry (liftA2uu f)
    \\ proveFunctor @f @a *** proveFunctor @f @b *** proveFunctor @f @c
  liftA2 :: forall a b c.
            Closed (Dom f) => Closed (Cod f)
         => Ok (Dom f) a => Ok (Dom f) b => Ok (Dom f) c
         => Dom f a (Dom f b c) -> Cod f (f a) (Cod f (f b) (f c))
  liftA2 f = liftA2u (uncurry f)



--------------------------------------------------------------------------------



-- | Applicative
-- (pointed lax monoidal functor)
class Apply f => Applicative f where
  -- | Create a functor
  pure :: Ok (Dom f) a => a -> f a



--------------------------------------------------------------------------------



-- | Traversable:
-- TOOD: Only endofunctors are traversable? Really???
-- See Jaskelioff, Rypacek, "An Investigation of the Laws of
-- Traversals", <https://arxiv.org/pdf/1202.2919.pdf>
class (Foldable f, Dom f ~ Cod f) => Traversable f where
  {-# MINIMAL (sequenceA | mapTraverse) #-}
  sequenceA :: forall g a k.
               Applicative g => Dom g ~ Dom f => Cod g ~ Cod f
            => k ~ Dom f
            => Ok k a
            => k (f (g a)) (g (f a))
  sequenceA = mapTraverse id id
              \\ proveFunctor @g @a
              \\ proveFunctor @f @a
  mapTraverse :: forall g a b c k.
                 Applicative g => Dom g ~ Dom f => Cod g ~ Cod f
              => k ~ Dom f
              => Ok k a => Ok k b => Ok k c
              => k (f b) c -> k a (g b) -> k (f a) (g c)
  mapTraverse g f = fmap g . sequenceA . fmap f
                    \\ proveFunctor @g @(f b)
                    \\ proveFunctor @f @(g b)
                    \\ proveFunctor @g @b
                    \\ proveFunctor @g @c
                    \\ proveFunctor @f @a
                    \\ proveFunctor @f @b
  traverse :: forall g a b k.
              Applicative g => Dom g ~ Dom f => Cod g ~ Cod f
           => k ~ Dom f
           => Ok k a => Ok k b
           => k a (g b) -> k (f a) (g (f b))
  traverse = mapTraverse id
             \\ proveFunctor @f @b
  consume :: forall g a b k.
             Applicative g => Dom g ~ Dom f => Cod g ~ Cod f
          => k ~ Dom f
          => Ok k a => Ok k b
          => k (f a) b -> k (f (g a)) (g b)
  consume g = mapTraverse g id
              \\ proveFunctor @g @a



--------------------------------------------------------------------------------



-- TODO: class Alternative



--------------------------------------------------------------------------------



class (Functor f, Cod f ~ Dom f) => Monad f where
  {-# MINIMAL return, (join | (<=<)) #-}
  return :: k ~ Dom f => Ok k a => k a (f a)
  join :: forall a k. k ~ Dom f => Ok k a => k (f (f a)) (f a)
  join = id <=< id
         \\ proveFunctor @f @(f a) \\ proveFunctor @f @a

  (<=<) :: forall a b c k. k ~ Dom f => Ok k a => Ok k b => Ok k c
        => k b (f c) -> k a (f b) -> k a (f c)
  g <=< f = join . fmap g . f
            \\ proveFunctor @f @b
            \\ proveFunctor @f @(f c) \\ proveFunctor @f @c
  bind :: forall a b k. k ~ Dom f => Cartesian k => Ok k a => Ok k b
        => k a (f b) -> k (f a) (f b)
  bind f = f <=< id
           \\ proveFunctor @f @a

-- Note: <https://gitlab.haskell.org/ghc/ghc/wikis/linear-types> has
-- @
--   return :: a ->. m a
--   (>>=) :: m a ->. (a ->. m b) ->. m b
-- @
-- for linear types in the category '->.'. There is also an
-- explanation which rejects the ansatz above. Does this make sense
-- here as well? I think this requires a closed category which we
-- don't have.

(=<<) :: forall f a b k. Monad f => k ~ Dom f => Cartesian k => Ok k a => Ok k b
      => k a (f b) -> f a -> f b
(=<<) f = eval (bind f)
          \\ proveFunctor @f @a \\ proveFunctor @f @b
(>>=) :: forall f a b k. Monad f => k ~ Dom f => Cartesian k => Ok k a => Ok k b
      => f a -> k a (f b) -> f b
x >>= f = f =<< x



--------------------------------------------------------------------------------



class (Functor f, Cod f ~ Dom f) => Comonad f where
  {-# MINIMAL extract, (duplicate | (=<=)) #-}
  extract :: k ~ Dom f => Ok k a => k (f a) a
  duplicate :: forall a k. k ~ Dom f => Ok k a => k (f a) (f (f a))
  duplicate = id =<= id
              \\ proveFunctor @f @(f a) \\ proveFunctor @f @a

  (=<=) :: forall a b c k. k ~ Dom f => Ok k a => Ok k b => Ok k c
        => k (f b) c -> k (f a) b -> k (f a) c
  g =<= f = g . fmap f . duplicate
    \\ proveFunctor @f @(f a) \\ proveFunctor @f @a \\ proveFunctor @f @b
  extend :: forall a b k. k ~ Dom f => Cartesian k => Ok k a => Ok k b
         => k (f a) b -> k (f a) (f b)
  extend f = id =<= f
             \\ proveFunctor @f @b



--------------------------------------------------------------------------------



instance Functor Proxy where
  proveFunctor = Sub Dict
  type Dom Proxy = (->)
  type Cod Proxy = (->)
  fmap _ = \_ -> Proxy

instance Functor Identity where
  proveFunctor = Sub Dict
  type Dom Identity = (->)
  type Cod Identity = (->)
  fmap f = \(Identity x) -> Identity (f x)

instance Functor ((,) a) where
  proveFunctor = Sub Dict
  type Dom ((,) a) = (->)
  type Cod ((,) a) = (->)
  fmap f = \(a, x) -> (a, f x)

instance Functor (Either a) where
  proveFunctor = Sub Dict
  type Dom (Either a) = (->)
  type Cod (Either a) = (->)
  fmap f = \case Left a -> Left a
                 Right x -> Right (f x)

instance Functor [] where
  proveFunctor = Sub Dict
  type Dom [] = (->)
  type Cod [] = (->)
  fmap f = \case [] -> []
                 x : xs -> f x : fmap f xs

instance Functor ((->) a) where
  proveFunctor = Sub Dict
  type Dom ((->) a) = (->)
  type Cod ((->) a) = (->)
  fmap f = \g -> f . g

instance ( Functor f, Functor g, Dom f ~ Dom g, Cod f ~ Cod g
         , Dom f ~ (->), Cod f ~ (->)) =>
         Functor (F.Product f g) where
  proveFunctor = Sub Dict
  type Dom (F.Product f g) = Dom f
  type Cod (F.Product f g) = (->)
  fmap f = \(F.Pair xs ys) -> F.Pair (fmap f xs) (fmap f ys)

instance ( Functor f, Functor g, Dom f ~ Dom g, Cod f ~ Cod g
         , Dom f ~ (->), Cod f ~ (->)) =>
         Functor (F.Sum f g) where
  proveFunctor = Sub Dict
  type Dom (F.Sum f g) = Dom f
  type Cod (F.Sum f g) = (->)
  fmap f = \case (F.InL xs) -> F.InL (fmap f xs)
                 (F.InR ys) -> F.InR (fmap f ys)

instance ( Functor f, Functor g, Dom f ~ Cod g
         , Dom g ~ (->), Cod f ~ (->), Cod g ~ (->)) =>
         Functor (F.Compose f g) where
  proveFunctor = Sub Dict
  type Dom (F.Compose f g) = Dom g
  type Cod (F.Compose f g) = (->)
  fmap f = \(F.Compose xss) -> F.Compose (fmap (fmap f) xss)



instance Foldable Proxy where
  foldMap _ _ = mempty

instance Foldable Identity where
  foldMap f (Identity x) = f x

instance Foldable ((,) a) where
  foldMap f (_, x) = f x

instance Foldable (Either a) where
  foldMap f = \case Left a -> mempty
                    Right x -> f x

instance Foldable [] where
  foldMap f = \case [] -> mempty
                    x : xs -> f x <> foldMap f xs

instance ( Foldable f, Foldable g, Dom f ~ Dom g, Cod f ~ Cod g
         , Dom f ~ (->), Cod f ~ (->)) =>
         Foldable (F.Product f g) where
  foldMap f = \(F.Pair xs xs') -> foldMap f xs <> foldMap f xs'

instance ( Foldable f, Foldable g, Dom f ~ Dom g, Cod f ~ Cod g
         , Dom f ~ (->), Cod f ~ (->)) =>
         Foldable (F.Sum f g) where
  foldMap f = \case (F.InL xs) -> foldMap f xs
                    (F.InR xs') -> foldMap f xs'

instance ( Foldable f, Foldable g, Dom f ~ Cod g
         , Dom g ~ (->), Cod f ~ (->), Cod g ~ (->)) =>
         Foldable (F.Compose f g) where
  foldMap f = \(F.Compose xss) -> foldMap (foldMap f) xss



instance Apply Proxy where
  liftA2uu _ = \_ -> Proxy

instance Apply Identity where
  liftA2uu f = \(Identity x, Identity y) -> Identity (f (x, y))

instance Semigroup a => Apply ((,) a) where
  liftA2uu f = \((a, x), (b, y)) -> (a <> b, f (x, y))

instance Apply (Either a) where
  liftA2uu f = \case (Left a, _) -> Left a
                     (_, Left b) -> Left b
                     (Right x, Right y) -> Right (f (x, y))

instance Apply [] where
  liftA2uu f = \(xs, ys) -> [f (x, y) | x <- xs, y <- ys]

instance Apply ((->) a) where
  liftA2uu f = \(p, q) -> \x -> f (p x, q x)

instance (Apply f, Apply g, Dom f ~ Dom g, Cod f ~ Cod g
         , Dom f ~ (->), Cod f ~ (->)) =>
         Apply (F.Product f g) where
  liftA2uu f =
    \(F.Pair xs xs', F.Pair ys ys') ->
      F.Pair (liftA2uu f (xs, ys)) (liftA2uu f (xs', ys'))

instance (Apply f, Apply g, Dom f ~ Cod g
         , Dom g ~ (->), Cod f ~ (->), Cod g ~ (->)) =>
         Apply (F.Compose f g) where
  liftA2uu f =
    \(F.Compose xss, F.Compose yss) ->
      F.Compose (liftA2uu (liftA2uu f) (xss, yss))



instance Applicative Proxy where
  pure _ = Proxy

instance Applicative Identity where
  pure x = Identity x

instance Monoid a => Applicative ((,) a) where
  pure x = (mempty, x)

instance Applicative (Either a) where
  pure x = Right x

instance Applicative [] where
  pure x = [x]

instance Applicative ((->) a) where
  pure x = const x

instance ( Applicative f, Applicative g, Dom f ~ Dom g, Cod f ~ Cod g
         , Dom f ~ (->), Cod f ~ (->)) =>
         Applicative (F.Product f g) where
  pure x = F.Pair (pure x) (pure x)

instance (Applicative f, Applicative g, Dom f ~ Cod g
         , Dom g ~ (->), Cod f ~ (->), Cod g ~ (->)) =>
         Applicative (F.Compose f g) where
  pure x = F.Compose (pure (pure x))



instance Traversable Proxy where
  sequenceA = \_ -> pure Proxy
  mapTraverse g _ = \_ -> fmap g (pure Proxy)

instance Traversable Identity where
  sequenceA = \(Identity xs) -> fmap Identity xs
  mapTraverse g f = \(Identity x) -> fmap (g . Identity) (f x)

instance Traversable (Either a) where
  sequenceA = \case (Left a) -> pure (Left a)
                    (Right xs) -> fmap Right xs
  mapTraverse g f = \case (Left a) -> fmap g (pure (Left a))
                          (Right x) -> fmap (g . Right) (f x)

instance Traversable ((,) a) where
  sequenceA = \(a, xs) -> fmap (a,) xs
  mapTraverse g f = \(a, x) -> fmap (g . (a,)) (f x)

instance Traversable [] where
  sequenceA = \case [] -> pure []
                    (xs:xss) -> liftA2 (:) xs (sequenceA xss)
  mapTraverse g f = \case [] -> pure (g [])
                          (ys:yss) -> liftA2 go (f ys) (mapTraverse id f yss)
                            where go zs zss = g (zs : zss)

instance ( Traversable f, Traversable g, Dom f ~ Dom g, Cod f ~ Cod g
         , Dom f ~ (->), Cod f ~ (->)) =>
         Traversable (F.Product f g) where
  sequenceA = \(F.Pair xs xs') -> liftA2 F.Pair (sequenceA xs) (sequenceA xs')

instance ( Traversable f, Traversable g, Dom f ~ Dom g, Cod f ~ Cod g
         , Dom f ~ (->), Cod f ~ (->)) =>
         Traversable (F.Sum f g) where
  sequenceA = \case (F.InL xs) -> fmap F.InL (sequenceA xs)
                    (F.InR xs') -> fmap F.InR (sequenceA xs')

instance (Traversable f, Traversable g, Dom f ~ Cod g
         , Dom g ~ (->), Cod f ~ (->), Cod g ~ (->)) =>
         Traversable (F.Compose f g) where
  sequenceA = fmap F.Compose . sequenceA . fmap sequenceA . F.getCompose
  mapTraverse g f =
    mapTraverse (g . F.Compose) (mapTraverse id f) . F.getCompose



instance Monad Proxy where
  return = \_ -> Proxy
  _ <=< _ = \_ -> Proxy

instance Monad Identity where
  return = \x -> Identity x
  g <=< f = \x -> let Identity y = f x in g y

instance Monoid a => Monad ((,) a) where
  return = \x -> (mempty, x)
  g <=< f = \x -> let (a, y) = f x
                      (b, z) = g y
                  in (a <> b, z)

instance Monad (Either a) where
  return = \x -> Right x
  g <=< f = \x -> case f x of Left a -> Left a
                              Right y -> g y

instance Monad [] where
  return = \x -> [x]
  g <=< f = \x -> [z | y <- f x, z <- g y]

instance Monad ((->) a) where
  return = \x -> const x
  g <=< f = \a -> \x -> g (f a x) x

instance (Monad f, Monad g, Dom f ~ Dom g, Cod f ~ Cod g
         , Dom f ~ (->), Cod f ~ (->)) =>
         Monad (F.Product f g) where
  return = \x -> F.Pair (return x) (return x)
  g <=< f = mkProd ((pfst . g) <=< (pfst . f)) ((psnd . g) <=< (psnd . f))
    where pfst (F.Pair xs _) = xs
          psnd (F.Pair _ xs') = xs'
          mkProd p q = \x -> F.Pair (p x) (q x)

instance Comonad Identity where
  extract = \(Identity x) -> x
  g =<= f = \xs -> g (Identity (f xs))

instance Comonad ((,) a) where
  extract = \(a, x) -> x
  g =<= f = \(a, x) -> g (a, f (a, x))

instance ( Comonad f, Comonad g, Dom f ~ Dom g, Cod f ~ Cod g
         , Dom f ~ (->), Cod f ~ (->)) =>
         Comonad (F.Sum f g) where
  extract = \case (F.InL xs) -> extract xs
                  (F.InR xs') -> extract xs'
  g =<= f = \case (F.InL xs) -> ((g . F.InL) =<= (f . F.InL)) xs
                  (F.InR xs') -> ((g . F.InR) =<= (f . F.InR)) xs'
