{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Control.Constrained.Foldable
  ( Foldable(..)
  ) where

import qualified Prelude as P
import Control.Constrained.Prelude

import Control.Applicative (ZipList(..))
import Control.Constrained.Cartesian
import Control.Constrained.Category
import Control.Constrained.Closed
import Control.Constrained.Functor
import Data.Constraint
import Data.Functor.Identity
import qualified Data.Functor.Compose as F
import qualified Data.Functor.Product as F
import qualified Data.Functor.Sum as F
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Monoid as M
import Data.Monoid.Instances ()
import Data.Proxy
import qualified Data.Vector as V



-- | A foldable functor
class Functor f => Foldable f where
  {-# MINIMAL foldMap, foldru, foldlu #-}
  -- | Fold with a monoid
  foldMap :: Monoid b => Ok (Dom f) a => Ok (Dom f) b => Dom f a b -> f a -> b

  foldru :: k ~ Dom f => Cartesian k => p ~ Product k => Ok k a => Ok k b
         => k (p a b) b -> b -> f a -> b
  foldr :: forall a b k . k ~ Dom f => Closed k => Ok k a => Ok k b
        => k a (k b b) -> b -> f a -> b
  {-# INLINE foldr #-}
  foldr f = foldru (uncurry f)
  foldlu :: k ~ Dom f => Cartesian k => p ~ Product k => Ok k a => Ok k b
         => k (p a b) a -> a -> f b -> a
  foldl :: forall a b k . k ~ Dom f => Closed k => Ok k a => Ok k b
        => k a (k b a) -> a -> f b -> a
  {-# INLINE foldl #-}
  foldl f = foldlu (uncurry f)

  toList :: HaskSubCat (Dom f) => HaskSubCat (Cod f) => Ok (Dom f) a
         => f a -> [a]
  default toList :: Ok (Dom f) a => Dom f ~ (->) => f a -> [a]
  toList = foldMap (:[])

  length :: Ok (Dom f) a => Ok (Dom f) Int => f a -> Int
  default length :: forall a k.
                    k ~ Dom f
                 => Cartesian k => Ok k a => Ok k Int => Ok k (M.Sum Int)
                 => f a -> Int
  length = M.getSum . foldMap (const (M.Sum (1::Int)))
           \\ proveFunctor @f @Int
           \\ proveFunctor @f @a



--------------------------------------------------------------------------------



instance Foldable Proxy where
  foldMap _ _ = mempty
  foldru _ z _ = z
  foldlu _ z _ = z

instance Foldable Identity where
  foldMap f (Identity x) = f x
  foldru f z (Identity x) = f (x, z)
  foldlu f z (Identity x) = f (z, x)

instance Foldable ((,) a) where
  foldMap f (_, x) = f x
  foldru f z (_, x) = f (x, z)
  foldlu f z (_, x) = f (z, x)

instance Foldable (Either a) where
  foldMap f (Left a) = mempty
  foldMap f (Right x) = f x
  foldru f z (Left a) = z
  foldru f z (Right x) = f (x, z)
  foldlu f z (Left a) = z
  foldlu f z (Right x) = f (z, x)

instance Foldable [] where
  foldMap f [] = mempty
  foldMap f (x : xs) = f x <> foldMap f xs
  foldru f z [] = z
  foldru f z (x : xs) = f (x, foldru f z xs)
  foldlu f z []= z
  foldlu f z (x : xs) = foldlu f (f (z, x)) xs

instance Foldable ZipList where
  foldMap f = foldMap f . getZipList
  foldru f z = foldru f z . getZipList
  foldlu f z = foldlu f z . getZipList

instance Foldable NonEmpty where
  foldMap f (x :| xs) = f x <> foldMap f xs
  foldru f z (x :| xs) = f (x, foldru f z xs)
  -- | This will loop forever
  foldlu f z (x :| xs) = foldlu f (f (z, x)) xs

instance ( Foldable f, Foldable g, Dom f ~ Dom g, Cod f ~ Cod g
         , Dom f ~ (->), Cod f ~ (->)) =>
         Foldable (F.Product f g) where
  foldMap f (F.Pair xs xs') = foldMap f xs <> foldMap f xs'
  foldru f z (F.Pair xs xs') = foldru f (foldru f z xs') xs
  foldlu f z (F.Pair xs xs') = foldlu f (foldlu f z xs) xs'

instance ( Foldable f, Foldable g, Dom f ~ Dom g, Cod f ~ Cod g
         , Dom f ~ (->), Cod f ~ (->)) =>
         Foldable (F.Sum f g) where
  foldMap f (F.InL xs) = foldMap f xs
  foldMap f (F.InR xs') = foldMap f xs'
  foldru f z (F.InL xs) = foldru f z xs
  foldru f z (F.InR xs') = foldru f z xs'
  foldlu f z (F.InL xs) = foldlu f z xs
  foldlu f z (F.InR xs') = foldlu f z xs'

instance ( Foldable f, Foldable g, Dom f ~ Cod g
         , Dom g ~ (->), Cod f ~ (->), Cod g ~ (->)) =>
         Foldable (F.Compose f g) where
  foldMap f (F.Compose xss) = foldMap (foldMap f) xss
  foldru f z (F.Compose xss) = foldru (\(xs, z') -> foldru f z' xs) z xss
  foldlu f z (F.Compose xss) = foldlu (\(z', xs) -> foldlu f z' xs) z xss

instance Foldable V.Vector where
  foldMap f = P.foldMap f
  foldru f z = V.foldr (P.curry f) z
  foldlu f z = V.foldl (P.curry f) z
