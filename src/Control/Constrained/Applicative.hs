{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Control.Constrained.Applicative
  ( Apply(..)
  , law_Apply_assoc
  , law_Apply_zippy
  , Applicative(..)
  , law_Applicative_leftUnit
  , law_Applicative_rightUnit
  ) where

import Prelude()
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
import Data.Proxy
import qualified Data.Vector as V



-- | An applicative functor (a lax monoidal functor) without 'pure'.
-- This class could also be called 'Monoidal'.
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



-- | Associativity (see <https://ncatlab.org/nlab/show/monoidal+functor>):
-- prop> ((f a, f b), f c) -> (f (a, b), f c) -> f ((a, b), c) -> f (a, (b, c))
-- prop> ((f a, f b), f c) -> (f a, (f b, f c)) -> (f a, f (b, c))
--                         -> f (a, (b, c))
law_Apply_assoc :: forall f a b c k l p q.
                   Apply f
                => k ~ Dom f => l ~ Cod f => p ~ Product k => q ~ Product l
                => Ok k a => Ok k b => Ok k c
                => ( l (q (q (f a) (f b)) (f c)) (f (p a (p b c)))
                   , l (q (q (f a) (f b)) (f c)) (f (p a (p b c)))
                   )
law_Apply_assoc =
  ( fmap (assoc @k) .
    liftA2uu @f (id @k)
    . prod @l (liftA2uu @f (id @k)) (id @l)
  , liftA2uu @f (id @k) .
    prod @l (id @l) (liftA2uu @f (id @k)) .
    assoc @l
  )
  \\ proveCartesian @l @(f a) @(q (f b) (f c))
  \\ proveCartesian @l @(q (f a) (f b)) @(f c)
  \\ proveCartesian @l @(f a) @(f (p b c))
  \\ proveCartesian @l @(f (p a b)) @(f c)
  \\ proveCartesian @l @(f b) @(f c)
  \\ proveCartesian @l @(f a) @(f b)
  \\ proveFunctor @f @(p a (p b c))
  \\ proveFunctor @f @(p (p a b) c)
  \\ proveFunctor @f @(p b c)
  \\ proveFunctor @f @(p a b)
  \\ proveCartesian @k @a @(p b c)
  \\ proveCartesian @k @(p a b) @c
  \\ proveCartesian @k @b @c
  \\ proveCartesian @k @a @b
  \\ proveFunctor @f @a
  \\ proveFunctor @f @b
  \\ proveFunctor @f @c

-- | For monadic functors
-- prop> liftA2 = liftM2
-- law_Apply_monadic

-- | For zippy functors (see Paul Chiusano
-- <http://pchiusano.blogspot.com/2010/06/alignable-functors-typeclass-for-zippy.html>)
-- prop> liftA2 f xs xs = fmap (\x -> f x x) xs
-- prop> liftA2 f . dup = fmap (f . dup)
law_Apply_zippy :: forall f a b k l p.
                   Apply f
                => k ~ Dom f => l ~ Cod f => p ~ Product k
                => Ok k a => Ok k b
                => k (p a a) b -> (l (f a) (f b), l (f a) (f b))
law_Apply_zippy f = (liftA2uu f . dup, fmap (f . dup))
                    \\ proveCartesian @l @(f a) @(f a)
                    \\ proveCartesian @k @a @a
                    \\ proveFunctor @f @a
                    \\ proveFunctor @f @b



--------------------------------------------------------------------------------



-- | Applicative
-- (pointed lax monoidal functor)
class Apply f => Applicative f where
  -- | Create a functor
  pure :: Ok (Dom f) a => a -> f a



-- | Unitality (see <https://ncatlab.org/nlab/show/monoidal+functor>):
-- Left unitality:
-- prop> (u, f a) -> f a
-- prop> (u, f a) -> (f u, f a) -> f (u, a) -> f a
-- Right unitality:
-- prop> (f a, u) -> f a
-- prop> (f a, u) -> (f a, f u) -> f (a, u) -> f a
law_Applicative_leftUnit :: forall f a k l p q u v.
                            Applicative f
                         => k ~ Dom f => p ~ Product k => u ~ Unit k
                         => l ~ Cod f => q ~ Product l => v ~ Unit l
                         => Ok k a
                         => (l (q v (f a)) (f a), l (q v (f a)) (f a))
law_Applicative_leftUnit =
  ( exr @l
  , fmap (exr @k) . liftA2uu @f (id @k) . prod @l pure' (id @l)
  )
  \\ proveCartesian @l @(f u) @(f a)
  \\ proveCartesian @l @v @(f a)
  \\ proveCartesian @k @u @a
  \\ proveFunctor @f @(p u a)
  \\ proveCartesian @k @u @a
  \\ proveFunctor @f @a
  \\ proveFunctor @f @u
  where -- pure :: a -> f a
        -- pure_u :: u -> f u
        pure' :: l v (f u)
        pure' = unitArrow @l (pure @f (unit @k))
                \\ proveFunctor @f @u

law_Applicative_rightUnit :: forall f a k l p q u v.
                             Applicative f
                          => k ~ Dom f => p ~ Product k => u ~ Unit k
                          => l ~ Cod f => q ~ Product l => v ~ Unit l
                          => Ok k a
                          => (l (q (f a) v) (f a), l (q (f a) v) (f a))
law_Applicative_rightUnit =
  ( exl @l
  , fmap (exl @k) . liftA2uu @f (id @k) . prod @l (id @l) pure'
  )
  \\ proveCartesian @l @(f a) @(f u)
  \\ proveCartesian @l @(f a) @v
  \\ proveCartesian @k @a @u
  \\ proveFunctor @f @(p a u)
  \\ proveCartesian @k @a @u
  \\ proveFunctor @f @a
  \\ proveFunctor @f @u
  where -- pure :: a -> f a
        -- pure_u :: u -> f u
        pure' :: l v (f u)
        pure' = unitArrow @l (pure @f (unit @k))
                \\ proveFunctor @f @u



--------------------------------------------------------------------------------



-- Alternative?



--------------------------------------------------------------------------------



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
  -- liftA2uu f = \(xs, ys) -> [f (x, y) | x <- xs, y <- ys]
  liftA2uu f = \(xs, ys) -> let g x = let h y = f (x, y)
                                      in map h ys
                            in concatMap g xs

instance Apply ZipList where
  liftA2uu f = \(xs, ys) -> zipWith' (\x y -> f (x, y)) xs ys
    where zipWith' g (ZipList xs) (ZipList ys) = ZipList (zipWith g xs ys)

-- NonEmpty

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

-- zippy
instance Apply V.Vector where
  liftA2uu f = uncurry (V.zipWith (curry f))



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

instance Applicative ZipList where
  pure x = ZipList (repeat x)

-- NonEmpty

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
