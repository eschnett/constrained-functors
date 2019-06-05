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
import Data.Monoid
import Data.Monoid.Instances ()
import Data.Proxy
import qualified Data.Vector as V



-- | A foldable functor
class Functor f => Foldable f where
  {-# MINIMAL foldMap #-}
  -- | Fold with a monoid
  foldMap :: Monoid b => Ok (Dom f) a => Ok (Dom f) b => Dom f a b -> f a -> b

  length :: Ok (Dom f) a => Ok (Dom f) Int => f a -> Int
  default length :: forall a k.
                    k ~ Dom f
                 => Cartesian k => Ok k a => Ok k Int => Ok k (Sum Int)
                 => f a -> Int
  length = getSum . foldMap (const (Sum (1::Int)))
           \\ proveFunctor @f @Int
           \\ proveFunctor @f @a



--------------------------------------------------------------------------------



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

instance Foldable ZipList where
  foldMap f = foldMap f . getZipList

instance Foldable NonEmpty where
  foldMap f = \(x :| xs) -> f x <> foldMap f xs

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

instance Foldable V.Vector where
  foldMap f = P.foldMap f
