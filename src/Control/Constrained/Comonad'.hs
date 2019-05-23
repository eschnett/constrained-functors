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

import Prelude ()

import Control.Constrained.Category
import Control.Constrained.Functor
import Data.Constraint



class (Functor f, Dom f `SubCatOf` Cod f) => Semicomonad f where
  {-# MINIMAL extend #-}
  (=<=) :: forall a b c k l.
           k ~ Dom f => l ~ Cod f => Ok k a => Ok k b => Ok k c
        => l (f b) c -> l (f a) b -> l (f a) c
  g =<= f = g . extend f
            \\ proveSubCatOf @(Dom f) @(Cod f) @a
            \\ proveSubCatOf @(Dom f) @(Cod f) @b
            \\ proveSubCatOf @(Dom f) @(Cod f) @c
            \\ proveFunctor @f @a
            \\ proveFunctor @f @b
            \\ proveFunctor @f @c
  extend :: forall a b k l.
            k ~ Dom f => l ~ Cod f => Ok k a => Ok k b
         => l (f a) b -> l (f a) (f b)

class Semicomonad f => Comonad f where
  extract :: forall a k l. k ~ Dom f => l ~ Cod f => Ok k a
          => l (f a) a



newtype Cokleisli (f :: FunctorKind) a b =
  Cokleisli { runCokleisli :: Cod f (f a) b }

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
                        => l (f b) c -> l (f a) b
                        -> (l (f a) (f c), l (f a) (f c))
law_Semicomonad_compose g f = (extend g . extend f, extend (g . extend f))
                              \\ proveSubCatOf @(Dom f) @(Cod f) @a
                              \\ proveSubCatOf @(Dom f) @(Cod f) @b
                              \\ proveSubCatOf @(Dom f) @(Cod f) @c
                              \\ proveFunctor @f @a
                              \\ proveFunctor @f @b
                              \\ proveFunctor @f @c

-- prop> (h =<= (g =<= f)) = ((h =<= g) =<= f)
law_Semicomonad_assoc :: forall f a b c d k l.
                         Semicomonad f
                      => k ~ Dom f => l ~ Cod f
                      => Ok k a => Ok k b => Ok k c => Ok k d
                      => l (f c) d
                      -> l (f b) c
                      -> l (f a) b
                      -> (l (f a) d, l (f a) d)
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
                        => l (f a) b
                        -> (l (f a) b, l (f a) b)
law_Semicomonad_rightId f = (extract . extend f, f)
                            \\ proveSubCatOf @(Dom f) @(Cod f) @a
                            \\ proveSubCatOf @(Dom f) @(Cod f) @b
                            \\ proveFunctor @f @a
                            \\ proveFunctor @f @b



--------------------------------------------------------------------------------



instance Semicomonad [] where
  -- type Incl [] = Identity
  extend f = extendList
    where extendList [] = []
          extendList l@(x:xs) = f l : extendList xs
