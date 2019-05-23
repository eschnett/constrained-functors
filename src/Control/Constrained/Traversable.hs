{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Control.Constrained.Traversable
  ( Traversable(..)
  ) where

import Prelude ()
import Control.Constrained.Prelude

import Control.Applicative (ZipList(..))
import Control.Constrained.Applicative
import Control.Constrained.Cartesian
import Control.Constrained.Category
import Control.Constrained.Closed
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
class (Foldable f, Dom f `SubCatOf` Cod f) => Traversable f where
  {-# MINIMAL mapTraverse #-}
  mapTraverse :: forall g a b c k l.
                 Applicative g => Dom g ~ Dom f => Cod g ~ Cod f
              => k ~ Dom f => l ~ Cod f
              => Ok k a => Ok k b => Ok k c
              => l (f b) c -> l a (g b) -> l (f a) (g c)
  -- mapTraverse g f = fmap g . sequenceA . fmap f
  -- mapTraverse g f = fmap g . traverse f
  sequenceA :: forall g a k.
               Applicative g => Dom f ~ Cod f => Dom g ~ Dom f => Cod g ~ Cod f
            => k ~ Dom f
            => Ok k a
            => k (f (g a)) (g (f a))
  sequenceA = mapTraverse id id
              \\ proveFunctor @g @a
              \\ proveFunctor @f @a
  traverse :: forall g a b k.
              Applicative g => Dom f ~ Cod f => Dom g ~ Dom f => Cod g ~ Cod f
           => k ~ Dom f
           => Ok k a => Ok k b
           => k a (g b) -> k (f a) (g (f b))
  traverse = mapTraverse id
             \\ proveFunctor @f @b
  consume :: forall g a b k.
             Applicative g => Dom f ~ Cod f => Dom g ~ Dom f => Cod g ~ Cod f
          => k ~ Dom f
          => Ok k a => Ok k b
          => k (f a) b -> k (f (g a)) (g b)
  consume g = mapTraverse g id
              \\ proveFunctor @g @a



--------------------------------------------------------------------------------



-- | An applicative transformation is a function
-- @
--   t :: (Applicative f, Applicative g) => f a -> g a
-- @
-- preserving the Applicative operations, i.e.
-- @
--   t (pure x) = pure x
--   t (x <*> y) = t x <*> t y
--   t (liftA2 f x y) = liftA2 f (t x) (t y)
-- @
law_AppTrans_pure :: forall f g a k.
                     Applicative f => Applicative g
                  => Dom f ~ Dom g
                  => k ~ Dom f
                  => Ok k a
                  => (forall x. Ok (Dom f) x => f x -> g x)
                  -> (a -> g a, a -> g a)
law_AppTrans_pure t = (t . pure, pure)
                      \\ proveFunctor @f @a
                      \\ proveFunctor @g @a

law_AppTrans_lift :: forall f g a b k p.
                     Apply f => Apply g
                  => Dom f ~ Dom g
                  => k ~ Dom f => p ~ Product k
                  => HaskSubCat (Cod f) => HaskSubCat (Cod g)
                  => Ok k a => Ok k b
                  => (forall x. Ok (Dom f) x => f x -> g x)
                  -> f a
                  -> f b
                  -> (g (p a b), g (p a b))
law_AppTrans_lift t xs ys =
  ( t (eval (liftA2uu @f (id @k)) (mkProd @(Cod f) xs ys))
  , eval (liftA2uu @g (id @k)) (mkProd @(Cod g) (t xs) (t ys))
  )
  \\ proveCartesian @(Cod f) @(f a) @(f b)
  \\ proveCartesian @(Cod g) @(g a) @(g b)
  \\ proveFunctor @f @(p a b)
  \\ proveFunctor @g @(p a b)
  \\ proveCartesian @k @a @b
  \\ proveFunctor @f @a
  \\ proveFunctor @f @b
  \\ proveFunctor @g @a
  \\ proveFunctor @g @b



-- | naturality
-- For every applicative transformationt 't':
-- prop> t . traverse f = traverse (t . f)
-- prop> fmap g . t . traverse f = mapTraverse g (t . f)
-- law_Traversable_nat :: forall f g a b c k l.
--                        Applicative f => Applicative g
--                     => Dom f ~ Dom g
--                     => k ~ Dom f => l ~ Cod f
--                     => Ok k a => Ok k b => Ok k c
--                     => (forall x. Ok (Dom f) x => f x -> g x)
--                     -> l (f b) c -> l a (g b)
--                     -> (l (f a) (g c), l (f a) (g c))
-- law_Traversable_nat t g f = (fmap g . t . traverse f, mapTraverse g (t . f))



-- | identity
-- prop> traverse Identity = Identity

-- | composition
-- prop> traverse (Compose . fmap g . f) = Compose . fmap (traverse g) . traverse f



--------------------------------------------------------------------------------



instance Traversable Proxy where
  sequenceA = \_ -> pure Proxy
  mapTraverse g f = fmap g . sequenceA . fmap f

instance Traversable Identity where
  sequenceA = \(Identity xs) -> fmap Identity xs
  mapTraverse g f = fmap g . sequenceA . fmap f

instance Traversable (Either a) where
  sequenceA = \case (Left a) -> pure (Left a)
                    (Right xs) -> fmap Right xs
  mapTraverse g f = fmap g . sequenceA . fmap f

instance Traversable ((,) a) where
  sequenceA = \(a, xs) -> fmap (a,) xs
  mapTraverse g f = fmap g . sequenceA . fmap f

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
  consume g = \(F.Pair xs xs') -> liftA2 go (sequenceA xs) (sequenceA xs')
      where go x x' = g (F.Pair x x')
  mapTraverse g f = consume g . fmap f

instance ( Traversable f, Traversable g, Dom f ~ Dom g, Cod f ~ Cod g
         , Dom f ~ (->), Cod f ~ (->)) =>
         Traversable (F.Sum f g) where
  consume g = \case (F.InL xs) -> fmap (g . F.InL) (sequenceA xs)
                    (F.InR xs') -> fmap (g . F.InR) (sequenceA xs')
  mapTraverse g f = consume g . fmap f

instance (Traversable f, Traversable g, Dom f ~ Cod g
         , Dom g ~ (->), Cod f ~ (->), Cod g ~ (->)) =>
         Traversable (F.Compose f g) where
  mapTraverse g f =
    mapTraverse (g . F.Compose) (mapTraverse id f) . F.getCompose

instance Traversable V.Vector where
  mapTraverse g f = \xs ->
    let n = V.length xs
    in fmap (g . V.fromListN n) (traverse f (V.toList xs))
