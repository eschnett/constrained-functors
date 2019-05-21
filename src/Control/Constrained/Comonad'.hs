{-# LANGUAGE UndecidableInstances #-}

module Control.Constrained.Comonad'
  ( Semicomonad(..)
  , law_Semicomonad_compose
  , law_Semicomonad_assoc
  , Cokleisli(..)
  , Comonad(..)
  , law_Semicomonad_leftId
  , law_Semicomonad_rightId
  ) where

import Prelude()

import Control.Constrained.Category
import Control.Constrained.Functor
import Data.Constraint
import Data.Functor.Identity



class ( Functor f
      , Inclusion (Incl f), Dom (Incl f) ~ Dom f, Cod (Incl f) ~ Cod f) =>
      Semicomonad f where
  {-# MINIMAL extend #-}
  type Incl f :: FunctorKind
  (=<=) :: forall a b c k l.
           k ~ Dom f => l ~ Cod f => Ok k a => Ok k b => Ok k c
        => l (f b) (Incl f c) -> l (f a) (Incl f b) -> l (f a) (Incl f c)
  g =<= f = g . extend f
            \\ proveFunctor @(Incl f) @a
            \\ proveFunctor @(Incl f) @b
            \\ proveFunctor @(Incl f) @c
            \\ proveFunctor @f @a
            \\ proveFunctor @f @b
            \\ proveFunctor @f @c
  extend :: forall a b k l.
            k ~ Dom f => l ~ Cod f => Ok k a => Ok k b
         => l (f a) (Incl f b) -> l (f a) (f b)

class Semicomonad f => Comonad f where
  extract :: forall a k l. k ~ Dom f => l ~ Cod f => Ok k a
          => l (f a) (Incl f a)



newtype Cokleisli (f :: FunctorKind) a b =
  Cokleisli { runCokleisli :: Cod f (f a) (Incl f b) }

instance Semicomonad f => Semigroupoid (Cokleisli f) where
  type Ok (Cokleisli f) = Ok (Dom f)
  Cokleisli g . Cokleisli f = Cokleisli (g =<= f)

instance Comonad f => Category (Cokleisli f) where
  id = Cokleisli extract



--------------------------------------------------------------------------------



-- prop> extend f . extend g = extend (f . extend g)
law_Semicomonad_compose :: forall f a b c k l.
                           Semicomonad f
                        => k ~ Dom f => l ~ Cod f => Ok k a => Ok k b => Ok k c
                        => l (f b) (Incl f c) -> l (f a) (Incl f b)
                        -> (l (f a) (f c), l (f a) (f c))
law_Semicomonad_compose g f = (extend g . extend f, extend (g . extend f))
                              \\ proveFunctor @(Incl f) @a
                              \\ proveFunctor @(Incl f) @b
                              \\ proveFunctor @(Incl f) @c
                              \\ proveFunctor @f @a
                              \\ proveFunctor @f @b
                              \\ proveFunctor @f @c

-- prop> (h =<= (g =<= f)) = ((h =<= g) =<= f)
law_Semicomonad_assoc :: forall f a b c d k l.
                         Semicomonad f
                      => k ~ Dom f => l ~ Cod f
                      => Ok k a => Ok k b => Ok k c => Ok k d
                      => l (f c) (Incl f d)
                      -> l (f b) (Incl f c)
                      -> l (f a) (Incl f b)
                      -> (l (f a) (Incl f d), l (f a) (Incl f d))
law_Semicomonad_assoc h g f = (h =<= (g =<= f), (h =<= g) =<= f)



-- prop> extend extract = id
law_Semicomonad_leftId :: forall f a k l.
                          Comonad f
                       => k ~ Dom f => l ~ Cod f => Ok k a
                       => (l (f a) (f a), l (f a) (f a))
law_Semicomonad_leftId = (extend extract, id @l)
                         \\ proveFunctor @f @a

-- prop> extract . extend f = f
law_Semicomonad_rightId :: forall f a b k l.
                           Comonad f
                        => k ~ Dom f => l ~ Cod f => Ok k a => Ok k b
                        => l (f a) (Incl f b)
                        -> (l (f a) (Incl f b), l (f a) (Incl f b))
law_Semicomonad_rightId f = (extract . extend f, f)
                            \\ proveFunctor @(Incl f) @a
                            \\ proveFunctor @(Incl f) @b
                            \\ proveFunctor @f @b
                            \\ proveFunctor @f @a



--------------------------------------------------------------------------------



instance Semicomonad [] where
  type Incl [] = Identity
  extend f = extendList
    where extendList [] = []
          extendList l@(x:xs) = runIdentity (f l) : extendList xs
