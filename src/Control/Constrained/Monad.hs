{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Control.Constrained.Monad
  ( Monad(..)
  , (=<<), (>>=)
  , Kleisli(..)
  ) where

import Prelude ()
import Control.Constrained.Prelude

import Control.Constrained.Cartesian
import Control.Constrained.Category
import Control.Constrained.Functor
import Data.Constraint
import Data.Functor.Identity
import qualified Data.Functor.Product as F
import Data.Proxy



-- Semimonad
-- Subcategories

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
  bind :: forall a b k. k ~ Dom f => Ok k a => Ok k b
        => k a (f b) -> k (f a) (f b)
  bind f = f <=< id
           \\ proveFunctor @f @a

-- liftM2 :: forall f a b c k p.
--           Monad f => k ~ Dom f => Closed k => p ~ Product k
--        => Ok k a => Ok k b => Ok k c
--        => k a (k b c) -> k (f a) (k (f b) (f c))
-- liftM2 f = let g = fmap f :: k (f a) (f (k b c))
--                q :: k b (f c)
--                h = bind q :: k b (f c) -> k (f b) (f c)
--            in _
--            \\ proveClosed @k @b @c
-- 
--            -- \(xs :: f a) ->
--            --   let ys :: f (k b c)
--            --       ys = fmap f xs
--            --       
--            --       q :: k b c
--            --       rs = \(zs :: f b) -> fmap q zs
--            --       rs :: k (f b) (f c)
--            --   in rs

-- liftM :: P.Monad m => (a -> b) -> m a -> m b
-- liftM f xs = P.fmap f xs
-- 
-- liftM2 :: P.Monad m => (a -> b -> c) -> m a -> m b -> m c
-- -- liftM2 f xs ys = P.fmap f xs `ap` ys
-- liftM2 f xs ys = P.fmap f xs P.>>= \g -> P.fmap g ys
-- 
-- ap :: forall m a b. P.Monad m => m (a -> b) -> m a -> m b
-- ap f xs = f P.>>= \g -> P.fmap g xs

-- Note: <https://gitlab.haskell.org/ghc/ghc/wikis/linear-types> has
-- @
--   return :: a ->. m a
--   (>>=) :: m a ->. (a ->. m b) ->. m b
-- @
-- for linear types in the category '->.'. There is also an
-- explanation which rejects the ansatz above. Does this make sense
-- here as well? I think this requires a closed category which we
-- don't have.

(=<<) :: forall f a b k.
         Monad f => k ~ Dom f => HaskSubCat k
      => Ok k a => Ok k b
      => k a (f b) -> f a -> f b
(=<<) f = eval (bind f)
          \\ proveFunctor @f @a \\ proveFunctor @f @b
(>>=) :: forall f a b k. Monad f => k ~ Dom f => HaskSubCat k
      => Ok k a => Ok k b
      => f a -> k a (f b) -> f b
x >>= f = f =<< x



newtype Kleisli f a b = Kleisli { runKleisli :: Dom f a (f b) }

instance Monad f => Semigroupoid (Kleisli f) where
  type Ok (Kleisli f) = Ok (Dom f)
  Kleisli g . Kleisli f = Kleisli (g <=< f)

instance Monad f => Category (Kleisli f) where
  id = Kleisli return



--------------------------------------------------------------------------------



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

-- instance Monad ZipList where
--   return = ZipList . return
--   g <=< f = ZipList . ((getZipList . g) <=< (getZipList . f))

-- Monad NonEmpty?

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

-- No Monad V.Vector, since Apply is zippy
