{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Control.Constrained.Comonad
  ( Semicomonad(..)
  , law_Semicomonad_assoc
  , law_Semicomonad_extend
  , law_Semicomonad_duplicate
  , Comonad(..)
  , law_Comonad_leftId
  , law_Comonad_rightId
  , Cokleisli(..)
  ) where

import Prelude()
import Control.Constrained.Prelude

import Control.Constrained.Category
import Control.Constrained.Functor
import Data.Constraint
import Data.Functor.Identity
import qualified Data.Functor.Sum as F
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Data.Proxy



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



newtype Cokleisli (f :: FunctorKind) a b =
  Cokleisli { runCokleisli :: Dom f (f a) b }

instance Semicomonad f => Semigroupoid (Cokleisli f) where
  type Ok (Cokleisli f) = Ok (Dom f)
  Cokleisli g . Cokleisli f = Cokleisli (g =<= f)

instance Comonad f => Category (Cokleisli f) where
  id = Cokleisli extract



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
