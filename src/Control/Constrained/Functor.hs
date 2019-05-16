{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Control.Constrained.Functor
  ( Functor(..)
  , law_Functor_id
  , law_Functor_compose
  , Foldable(..)
  , Apply(..)
  , law_Apply_assoc
  , Applicative(..)
  , law_Applicative_leftUnit
  , law_Applicative_rightUnit
  , Traversable(..)
  , Monad(..)
  , (=<<), (>>=)
  , Kleisli(..)
  , Semicomonad(..)
  , law_Semicomonad_assoc
  , law_Semicomonad_extend
  , law_Semicomonad_duplicate
  , Comonad(..)
  , law_Comonad_leftId
  , law_Comonad_rightId
  , Cokleisli(..)
  ) where

import Prelude hiding ( id, (.), const, curry, uncurry
                      , Applicative(..), Foldable(..), Functor(..), Monad(..)
                      , Traversable(..)
                      , (=<<))

import Control.Applicative (ZipList(..))
import Control.Constrained.Category hiding (fork, join)
import Data.Constraint
import Data.Functor.Identity
import qualified Data.Functor.Compose as F
import qualified Data.Functor.Product as F
import qualified Data.Functor.Sum as F
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
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



law_Functor_id :: forall f a k l.
                  Functor f => k ~ Dom f => l ~ Cod f => Ok k a
               => (l (f a) (f a), l (f a) (f a))
law_Functor_id = (fmap (id @k), id @l)
                 \\ proveFunctor @f @a

law_Functor_compose :: forall f a b c k l.
                       Functor f => k ~ Dom f => l ~ Cod f
                    => Ok k a => Ok k b => Ok k c
                    => k b c -> k a b -> (l (f a) (f c), l (f a) (f c))
law_Functor_compose g f = (fmap (g . f), fmap g . fmap f)
                          \\ proveFunctor @f @a
                          \\ proveFunctor @f @b
                          \\ proveFunctor @f @c



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



-- Semimonad?

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

(=<<) :: forall f a b k.
         Monad f => k ~ Dom f => Cartesian k => HaskSubCat k
      => Ok k a => Ok k b
      => k a (f b) -> f a -> f b
(=<<) f = eval (bind f)
          \\ proveFunctor @f @a \\ proveFunctor @f @b
(>>=) :: forall f a b k. Monad f => k ~ Dom f => Cartesian k => HaskSubCat k
      => Ok k a => Ok k b
      => f a -> k a (f b) -> f b
x >>= f = f =<< x

newtype Kleisli f a b = Kleisli { runKleisli :: Dom f a (f b) }

-- TODO: 'Kleisli' is a 'Category'



--------------------------------------------------------------------------------



class (Functor f, Cod f ~ Dom f) => Semicomonad f where
  {-# MINIMAL (duplicate | (=<=) | extend) #-}
  duplicate :: forall a k. k ~ Dom f => Ok k a => k (f a) (f (f a))
  -- duplicate = id =<= id
  --             \\ proveFunctor @f @(f a) \\ proveFunctor @f @a
  duplicate = extend id
              \\ proveFunctor @f @a
  (=<=) :: forall a b c k. k ~ Dom f => Ok k a => Ok k b => Ok k c
        => k (f b) c -> k (f a) b -> k (f a) c
  g =<= f = g . fmap f . duplicate
            \\ proveFunctor @f @(f a)
            \\ proveFunctor @f @b
            \\ proveFunctor @f @a
  extend :: forall a b k. k ~ Dom f => Ok k a => Ok k b
         => k (f a) b -> k (f a) (f b)
  extend f = id =<= f
             \\ proveFunctor @f @b

class Semicomonad f => Comonad f where
  {-# MINIMAL extract #-}
  extract :: k ~ Dom f => Ok k a => k (f a) a

newtype Cokleisli f a b = Cokleisli { runCokleisli :: Dom f (f a) b }

-- TOOD: make this work -- find out how to handle 'eval'
-- instance Comonad f => Category (Cokleisli f) where
--   type Ok (Cokleisli f) = Ok (Dom f)
--   id = Cokleisli extract
--   Cokleisli g . Cokleisli f = Cokleisli (g =<= f)
--   eval :: Ok (Dom f) a => Ok (Dom f) b => Cokleisli f a b -> a -> b
--   eval (Cokleisli f) = Cokleisli @(->) (eval f)



-- prop> (h =<= (g =<= f)) = ((h =<= g) =<= f)
law_Semicomonad_assoc :: forall f a b c d k.
                         Semicomonad f
                      => k ~ Dom f
                      => Ok k a => Ok k b => Ok k c => Ok k d
                      => k (f c) d -> k (f b) c -> k (f a) b
                      -> (k (f a) d, k (f a) d)
law_Semicomonad_assoc h g f = (h =<= (g =<= f), (h =<= g) =<= f)

law_Semicomonad_extend :: forall f a b k.
                          Semicomonad f
                       => k ~ Dom f
                       => Ok k a => Ok k b
                       => k (f a) b -> (k (f a) (f b), k (f a) (f b))
law_Semicomonad_extend f = (extend f, id =<= f)
                           \\ proveFunctor @f @b
law_Semicomonad_duplicate :: forall f a k.
                             Semicomonad f
                          => k ~ Dom f
                          => Ok k a
                          => (k (f a) (f (f a)), k (f a) (f (f a)))
law_Semicomonad_duplicate = (duplicate, extend id)
                            \\ proveFunctor @f @a

-- prop> extract =<= f = f
law_Comonad_leftId :: forall f a b k.
                      Comonad f
                   => k ~ Dom f
                   => Ok k a => Ok k b
                   => k (f a) b -> (k (f a) b, k (f a) b)
law_Comonad_leftId f = (f, extract =<= f)

-- prop> f =<= extract = f
law_Comonad_rightId :: forall f a b k.
                       Comonad f
                    => k ~ Dom f
                    => Ok k a => Ok k b
                    => k (f a) b -> (k (f a) b, k (f a) b)
law_Comonad_rightId f = (f , f =<= extract)



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

instance Functor ZipList where
  proveFunctor = Sub Dict
  type Dom ZipList = (->)
  type Cod ZipList = (->)
  fmap f = ZipList . fmap f . getZipList

instance Functor NonEmpty where
  proveFunctor = Sub Dict
  type Dom NonEmpty = (->)
  type Cod NonEmpty = (->)
  fmap f = \(x :| xs) -> f x :| fmap f xs

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

-- NonEmpty

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

instance Semicomonad Proxy where
  duplicate = \_ -> Proxy

instance Semicomonad Identity where
  duplicate = Identity

instance Semicomonad (Either a) where
  duplicate = fmap Right

instance Semicomonad ((,) a) where
  g =<= f = \(a, x) -> g (a, f (a, x))

instance Semicomonad [] where
  g =<= f = g . extend f
  extend f = extendList
    where extendList [] = []
          extendList l@(x:xs) = f l : extendList xs

instance Semicomonad NonEmpty where
  g =<= f = g . extend f
  extend f = NE.fromList . extendList . NE.toList
    where extendList [] = []
          extendList l@(x:xs) = (f . NE.fromList) l : extendList xs

instance ( Semicomonad f, Semicomonad g, Dom f ~ Dom g, Cod f ~ Cod g
         , Dom f ~ (->), Cod f ~ (->)) =>
         Semicomonad (F.Sum f g) where
  g =<= f = \case (F.InL xs) -> ((g . F.InL) =<= (f . F.InL)) xs
                  (F.InR xs') -> ((g . F.InR) =<= (f . F.InR)) xs'

instance Comonad Identity where
  extract = \(Identity x) -> x

instance Comonad ((,) a) where
  extract = \(a, x) -> x

instance Comonad NonEmpty where
  extract = \(x :| _) -> x

-- '(->) a' ?

instance ( Comonad f, Comonad g, Dom f ~ Dom g, Cod f ~ Cod g
         , Dom f ~ (->), Cod f ~ (->)) =>
         Comonad (F.Sum f g) where
  extract = \case (F.InL xs) -> extract xs
                  (F.InR xs') -> extract xs'
