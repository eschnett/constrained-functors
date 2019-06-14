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
  {-# MINIMAL foldMap, foldr, foldl #-}
  -- | Fold with a monoid
  foldMap :: Monoid b => Ok (Dom f) a => Ok (Dom f) b => Dom f a b -> f a -> b

  foldr :: k ~ Dom f => Cartesian k => p ~ Product k => Ok k a => Ok k b
        => k (p a b) b -> b -> f a -> b
  foldl :: k ~ Dom f => Cartesian k => p ~ Product k => Ok k a => Ok k b
        => k (p a b) a -> a -> f b -> a

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
  foldr _ z _ = z
  foldl _ z _ = z

instance Foldable Identity where
  foldMap f (Identity x) = f x
  foldr f z (Identity x) = f (x, z)
  foldl f z (Identity x) = f (z, x)

instance Foldable ((,) a) where
  foldMap f (_, x) = f x
  foldr f z (_, x) = f (x, z)
  foldl f z (_, x) = f (z, x)

instance Foldable (Either a) where
  foldMap f (Left a) = mempty
  foldMap f (Right x) = f x
  foldr f z (Left a) = z
  foldr f z (Right x) = f (x, z)
  foldl f z (Left a) = z
  foldl f z (Right x) = f (z, x)

instance Foldable [] where
  foldMap f [] = mempty
  foldMap f (x : xs) = f x <> foldMap f xs
  foldr f z [] = z
  foldr f z (x : xs) = f (x, foldr f z xs)
  foldl f z []= z
  foldl f z (x : xs) = foldl f (f (z, x)) xs

instance Foldable ZipList where
  foldMap f = foldMap f . getZipList
  foldr f z = foldr f z . getZipList
  foldl f z = foldl f z . getZipList

instance Foldable NonEmpty where
  foldMap f (x :| xs) = f x <> foldMap f xs
  foldr f z (x :| xs) = f (x, foldr f z xs)
  -- | This will loop forever
  foldl f z (x :| xs) = foldl f (f (z, x)) xs

instance ( Foldable f, Foldable g, Dom f ~ Dom g, Cod f ~ Cod g
         , Dom f ~ (->), Cod f ~ (->)) =>
         Foldable (F.Product f g) where
  foldMap f (F.Pair xs xs') = foldMap f xs <> foldMap f xs'
  foldr f z (F.Pair xs xs') = foldr f (foldr f z xs') xs
  foldl f z (F.Pair xs xs') = foldl f (foldl f z xs) xs'

instance ( Foldable f, Foldable g, Dom f ~ Dom g, Cod f ~ Cod g
         , Dom f ~ (->), Cod f ~ (->)) =>
         Foldable (F.Sum f g) where
  foldMap f (F.InL xs) = foldMap f xs
  foldMap f (F.InR xs') = foldMap f xs'
  foldr f z (F.InL xs) = foldr f z xs
  foldr f z (F.InR xs') = foldr f z xs'
  foldl f z (F.InL xs) = foldl f z xs
  foldl f z (F.InR xs') = foldl f z xs'

instance ( Foldable f, Foldable g, Dom f ~ Cod g
         , Dom g ~ (->), Cod f ~ (->), Cod g ~ (->)) =>
         Foldable (F.Compose f g) where
  foldMap f (F.Compose xss) = foldMap (foldMap f) xss
  foldr f z (F.Compose xss) = foldr (\(xs, z') -> foldr f z' xs) z xss
  foldl f z (F.Compose xss) = foldl (\(z', xs) -> foldl f z' xs) z xss

instance Foldable V.Vector where
  foldMap f = P.foldMap f
  foldr f z = V.foldr (P.curry f) z
  foldl f z = V.foldl (P.curry f) z
