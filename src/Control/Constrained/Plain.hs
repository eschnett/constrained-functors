{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Constrained.Plain
  ( PCon
  , type (-#>)(..)
  ) where

import Prelude hiding ( id, (.)
                      , Applicative(..), Foldable(..), Functor(..)
                      , Traversable(..))

import Control.Constrained.Category
import Control.Constrained.Functor
import Data.Binary
import Data.Constraint
import qualified Data.Monoid as M
import qualified Data.Vector.Unboxed as U
import Data.Vector.Unboxed.Deriving
import GHC.Generics



class (Binary a, U.Unbox a) => PCon a
instance (Binary a, U.Unbox a) => PCon a

newtype (-#>) a b = PFun { runPFun :: a -> b }



instance Category (-#>) where
  type Ok (-#>) = PCon
  id = PFun id
  PFun g . PFun f = PFun (g . f)
  eval (PFun f) = f

instance Cartesian (-#>) where
  proveCartesian = Sub Dict
  type Product (-#>) = (,)
  type Unit (-#>) = ()
  prod (PFun f) (PFun g) = PFun \(x, y) -> (f x, g y)
  unit = ()
  exl = PFun fst
  exr = PFun snd
  fork (PFun f) (PFun g) = PFun \x -> (f x, g x)
  it = PFun (\_ -> ())
  unitArrow x = PFun (\_ -> x)



derivingUnbox "Monoid_Sum"
    [t| forall a. U.Unbox a => M.Sum a -> a |]
    [| \(M.Sum x) -> x |]
    [| \x -> M.Sum x |]



data PProxy a = PProxy
  deriving (Eq, Ord, Read, Show, Generic)

instance Binary (PProxy a)

derivingUnbox "PProxy"
    [t| forall a. PProxy a -> () |]
    [| \PProxy -> () |]
    [| \() -> PProxy |]

newtype PIdentity a = PIdentity a
  deriving (Eq, Ord, Read, Show, Generic)

instance Binary a => Binary (PIdentity a)

derivingUnbox "PIdentity"
    [t| forall a. U.Unbox a => PIdentity a -> a |]
    [| \(PIdentity x) -> x |]
    [| \x -> PIdentity x |]

data PTuple a b = PTuple a b
  deriving (Eq, Ord, Read, Show, Generic)

instance (Binary a, Binary b) => Binary (PTuple a b)

derivingUnbox "PTuple"
    [t| forall a b. (U.Unbox a, U.Unbox b) => PTuple a b -> (a, b) |]
    [| \(PTuple x y) -> (x, y) |]
    [| \(x, y) -> PTuple x y |]

data PProduct f g a = PPair (f a) (g a)
  deriving (Eq, Ord, Read, Show, Generic)

instance (Binary (f a), Binary (g a)) => Binary (PProduct f g a)

derivingUnbox "PProduct"
    [t| forall f g a. (U.Unbox (f a), U.Unbox (g a))
     => PProduct f g a -> (f a, g a) |]
    [| \(PPair xs xs') -> (xs, xs') |]
    [| \(xs, xs') -> PPair xs xs' |]

newtype PCompose f g a = PCompose (f (g a))
  deriving (Eq, Ord, Read, Show, Generic)

instance Binary (f (g a)) => Binary (PCompose f g a)

derivingUnbox "PCompose"
    [t| forall f g a. U.Unbox (f (g a)) => PCompose f g a -> f (g a) |]
    [| \(PCompose xss) -> xss |]
    [| \xss -> PCompose xss |]



instance Functor PProxy where
  proveFunctor = Sub Dict
  type Dom PProxy = (-#>)
  type Cod PProxy = (-#>)
  fmap _ = PFun \_ -> PProxy

instance Functor PIdentity where
  proveFunctor = Sub Dict
  type Dom PIdentity = (-#>)
  type Cod PIdentity = (-#>)
  fmap (PFun f) = PFun \(PIdentity x) -> PIdentity (f x)

instance PCon a => Functor (PTuple a) where
  proveFunctor = Sub Dict
  type Dom (PTuple a) = (-#>)
  type Cod (PTuple a) = (-#>)
  fmap (PFun f) = PFun \(PTuple a x) -> PTuple a (f x)

instance ( Functor f, Functor g, Dom f ~ Dom g, Cod f ~ Cod g
         , Dom f ~ (-#>), Cod f ~ (-#>)) =>
         Functor (PProduct f g) where
  proveFunctor :: forall a. PCon a :- PCon (PProduct f g a)
  proveFunctor = trans pconpfga (pconfa &&& pconga)
    where
      pconfa = proveFunctor @f @a :: PCon a :- PCon (f a)
      pconga = proveFunctor @g @a :: PCon a :- PCon (g a)
      pconpfga = Sub Dict :: (PCon (f a), PCon (g a)) :- PCon (PProduct f g a)
  type Dom (PProduct f g) = Dom f
  type Cod (PProduct f g) = (-#>)
  fmap f = PFun \(PPair xs xs') ->
                  PPair (runPFun (fmap f) xs) (runPFun (fmap f) xs')

instance ( Functor f, Functor g, Dom f ~ Cod g
         , Dom g ~ (-#>), Cod f ~ (-#>), Cod g ~ (-#>)) =>
         Functor (PCompose f g) where
  proveFunctor :: forall a. PCon a :- PCon (PCompose f g a)
  proveFunctor = trans pconcfga (trans pconfga pconga)
    where
      pconga = proveFunctor @g @a :: PCon a :- PCon (g a)
      pconfga = proveFunctor @f @(g a) :: PCon (g a) :- PCon (f (g a))
      pconcfga = Sub Dict :: PCon (f (g a)) :- PCon (PCompose f g a)
  type Dom (PCompose f g) = Dom g
  type Cod (PCompose f g) = (-#>)
  fmap :: forall a b.
          forall pc. pc ~ PCompose f g
       => Ok (Dom pc) a => Ok (Dom pc) b => Dom pc a b -> Cod pc (pc a) (pc b)
  fmap f = PFun \(PCompose xss) -> PCompose (runPFun (fmap (fmap f)) xss)
    \\ proveFunctor @g @a \\ proveFunctor @g @b



instance Foldable PProxy where
  foldMap _ _ = mempty

instance Foldable PIdentity where
  foldMap (PFun f) (PIdentity x) = f x

instance PCon a => Foldable (PTuple a) where
  foldMap (PFun f) (PTuple _ x) = f x

instance ( Foldable f, Foldable g, Dom f ~ Dom g, Cod f ~ Cod g
         , Dom f ~ (-#>), Cod f ~ (-#>)) =>
         Foldable (PProduct f g) where
  foldMap f = \(PPair xs xs') -> foldMap f xs <> foldMap f xs'

instance ( Foldable f, Foldable g, Dom f ~ Cod g
         , Dom g ~ (-#>), Cod f ~ (-#>), Cod g ~ (-#>)) =>
         Foldable (PCompose f g) where
  foldMap :: forall a b pc.
             pc ~ PCompose f g
          => Monoid b => Ok (Dom pc) a => Ok (Dom pc) b
          => Dom pc a b -> pc a -> b
  foldMap f = \(PCompose xss) -> foldMap (PFun (foldMap f)) xss
    \\ proveFunctor @g @a
  


instance Apply PProxy where
  liftA2uu _ = PFun \_ -> PProxy

instance Apply PIdentity where
  liftA2uu (PFun f) = PFun \(PIdentity x, PIdentity y) -> PIdentity (f (x, y))

instance (PCon a, Semigroup a) => Apply (PTuple a) where
  liftA2uu (PFun f) =
    PFun \(PTuple a x, PTuple b y) -> PTuple (a <> b) (f (x, y))

instance (Apply f, Apply g, Dom f ~ Dom g, Cod f ~ Cod g
         , Dom f ~ (-#>), Cod f ~ (-#>)) =>
         Apply (PProduct f g) where
  liftA2uu f = PFun \(PPair xs xs', PPair ys ys') ->
                      PPair
                      (runPFun (liftA2uu f) (xs, ys))
                      (runPFun (liftA2uu f) (xs', ys'))

instance (Apply f, Apply g, Dom f ~ Cod g
         , Dom g ~ (-#>), Cod f ~ (-#>), Cod g ~ (-#>)) =>
         Apply (PCompose f g) where
  liftA2uu :: forall a b c pc p q.
              pc ~ PCompose f g => p ~ Product (Dom pc) => q ~ Product (Cod pc)
           => Ok (Dom pc) a => Ok (Dom pc) b => Ok (Dom pc) c
           => Dom pc (p a b) c -> Cod pc (q (pc a) (pc b)) (pc c)
  liftA2uu f = PFun \(PCompose xss, PCompose yss) ->
                      PCompose (runPFun (liftA2uu (liftA2uu f)) (xss, yss))
    \\ proveFunctor @g @a \\ proveFunctor @g @b \\ proveFunctor @g @c



instance Applicative PProxy where
  pure _ = PProxy

instance Applicative PIdentity where
  pure x = PIdentity x

instance (PCon a, Monoid a) => Applicative (PTuple a) where
  pure x = PTuple mempty x

instance ( Applicative f, Applicative g, Dom f ~ Dom g, Cod f ~ Cod g
         , Dom f ~ (-#>), Cod f ~ (-#>)) =>
         Applicative (PProduct f g) where
  pure x = PPair (pure x) (pure x)

instance ( Applicative f, Applicative g, Dom f ~ Cod g
         , Dom g ~ (-#>), Cod f ~ (-#>), Cod g ~ (-#>)) =>
         Applicative (PCompose f g) where
  pure :: forall a pc. pc ~ PCompose f g => Ok (Dom pc) a => a -> pc a
  pure x = PCompose (pure (pure x))
           \\ proveFunctor @g @a



instance Traversable PProxy where
  sequenceA = PFun (\_ -> pure PProxy)
  
instance Traversable PIdentity where
  sequenceA = PFun \(PIdentity xs) -> runPFun (fmap (PFun PIdentity)) xs

instance PCon a => Traversable (PTuple a) where
  sequenceA = PFun \(PTuple a xs) -> runPFun (fmap (PFun (PTuple a))) xs

-- TODO: F.Product F.Compose



instance Functor U.Vector where
  proveFunctor = Sub Dict
  type Dom U.Vector = (-#>)
  type Cod U.Vector = (->)
  fmap (PFun f) = U.map f

instance Foldable U.Vector where
  foldMap (PFun f) = U.foldl (\r x -> r <> f x) mempty

instance Apply U.Vector where
  liftA2uu (PFun f) = \(xs, ys) -> U.zipWith (\x y -> f (x, y)) xs ys
