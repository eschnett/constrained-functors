{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Control.Constrained.Comonad
  ( Semicomonad(..)
  , law_Semicomonad_compose
  , law_Semicomonad_assoc
  , law_Semicomonad_extend
  , law_Semicomonad_duplicate
  , Comonad(..)
  , law_Comonad_leftId
  , law_Comonad_rightId
  , Cokleisli(..)
  ) where

import Prelude ()
import Control.Constrained.Prelude

import Control.Constrained.Category
import Control.Constrained.Functor
import Data.Constraint
import Data.Functor.Identity
import qualified Data.Functor.Sum as F
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Data.Proxy



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

duplicate :: forall f a k.
             Semicomonad f => Cod f ~ Dom f => k ~ Dom f => Ok k a
          => k (f a) (f (f a))
duplicate = extend id
            \\ proveFunctor @f @a

class Semicomonad f => Comonad f where
  {-# MINIMAL extract #-}
  extract :: forall a k l. k ~ Dom f => l ~ Cod f => Ok k a => l (f a) a



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

law_Semicomonad_extend :: forall f a b c k l.
                          Semicomonad f
                       => k ~ Dom f => l ~ Cod f
                       => Ok k a => Ok k b => Ok k c
                       => l (f b) c
                       -> l (f a) b
                       -> (l (f a) c, l (f a) c)
law_Semicomonad_extend g f = (g . extend f, g =<= f)
                             \\ proveSubCatOf @(Dom f) @(Cod f) @c
                             \\ proveFunctor @f @a
                             \\ proveFunctor @f @b
                             \\ proveFunctor @f @c

law_Semicomonad_duplicate :: forall f a k.
                             Semicomonad f
                          => Cod f ~ Dom f
                          => k ~ Dom f
                          => Ok k a
                          => (k (f a) (f (f a)), k (f a) (f (f a)))
law_Semicomonad_duplicate = (duplicate, extend id)
                            \\ proveFunctor @f @a



-- prop> extend extract = id
law_Comonad_leftId :: forall f a k l.
                      Comonad f
                   => k ~ Dom f => l ~ Cod f => Ok k a
                   => (l (f a) (f a), l (f a) (f a))
law_Comonad_leftId = (extend extract, id @l)
                     \\ proveFunctor @f @a

-- prop> extract . extend f = f
law_Comonad_rightId :: forall f a b k l.
                       Comonad f
                    => k ~ Dom f => l ~ Cod f => Ok k a => Ok k b
                    => l (f a) b
                    -> (l (f a) b, l (f a) b)
law_Comonad_rightId f = (extract . extend f, f)
                        \\ proveSubCatOf @(Dom f) @(Cod f) @a
                        \\ proveSubCatOf @(Dom f) @(Cod f) @b
                        \\ proveFunctor @f @a
                        \\ proveFunctor @f @b
  


--------------------------------------------------------------------------------



instance Semicomonad Proxy where
  extend _ = \_ -> Proxy

instance Semicomonad Identity where
  extend f = fmap f . Identity

instance Semicomonad (Either a) where
  extend f = fmap f . fmap Right

instance Semicomonad ((,) a) where
  extend f = \(a, x) -> (a, f (a, x))

instance Semicomonad [] where
  extend f = extendList
    where extendList [] = []
          extendList l@(x:xs) = f l : extendList xs

instance Semicomonad NonEmpty where
  extend f = NE.fromList . extendList . NE.toList
    where extendList [] = []
          extendList l@(x:xs) = (f . NE.fromList) l : extendList xs

instance ( Semicomonad f, Semicomonad g, Dom f ~ Dom g, Cod f ~ Cod g
         , Dom f ~ (->), Cod f ~ (->)) =>
         Semicomonad (F.Sum f g) where
  extend f = \case (F.InL xs) -> (F.InL =<= (f . F.InL)) xs
                   (F.InR xs') -> (F.InR =<= (f . F.InR)) xs'

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
