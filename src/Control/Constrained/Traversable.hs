{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Control.Constrained.Traversable
  ( Traversable(..)
  ) where

import Prelude ()
import Control.Constrained.Prelude

import Control.Applicative (ZipList(..))
import Control.Constrained.Category
import Control.Constrained.Applicative
import Control.Constrained.Foldable
import Control.Constrained.Functor
import Data.Constraint
import Data.Functor.Identity
import qualified Data.Functor.Compose as F
import qualified Data.Functor.Product as F
import qualified Data.Functor.Sum as F
import Data.Proxy
import qualified Data.Vector as V



-- | Traversable:
-- TOOD: Only endofunctors are traversable? Really???
-- See Jaskelioff, Rypacek, "An Investigation of the Laws of
-- Traversals", <https://arxiv.org/abs/1202.2919>
class (Foldable f, Dom f ~ Cod f) => Traversable f where
  {-# MINIMAL sequenceA | mapTraverse | traverse #-}
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
  -- mapTraverse g f = fmap g . sequenceA . fmap f
  --                   \\ proveFunctor @g @(f b)
  --                   \\ proveFunctor @f @(g b)
  --                   \\ proveFunctor @g @b
  --                   \\ proveFunctor @g @c
  --                   \\ proveFunctor @f @a
  --                   \\ proveFunctor @f @b
  mapTraverse g f = fmap g . traverse f
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

instance Traversable ZipList where
  mapTraverse g f = mapTraverse (g . ZipList) f . getZipList

-- NonEmpty

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

instance Traversable V.Vector where
  traverse f = \xs ->
    let n = V.length xs
    in fmap (V.fromListN n) (traverse f (V.toList xs))
