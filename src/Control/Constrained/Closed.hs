{-# LANGUAGE UndecidableSuperClasses #-}

module Control.Constrained.Closed
  ( -- * Closed categories
    Closed(..)
  , law_Closed_apply
  , law_Closed_curry
  , law_Closed_uncurry
  ) where

import qualified Prelude as P

import Control.Constrained.Cartesian
import Control.Constrained.Category
import Data.Constraint



--------------------------------------------------------------------------------



-- | A closed category has exponentials, i.e. morphisms are objects
class Cartesian k => Closed k where
  -- | Prove that the category is closed, i.e. that morphisms are
  -- objects in the category
  proveClosed :: (Ok k a, Ok k b) :- Ok k (k a b)

  -- | Apply a function
  -- prop> apply . (curry f . fork exl exr) = f
  apply :: p ~ Product k => Ok k a => Ok k b => k (p (k a b) a) b

  -- | Curry a function
  curry :: p ~ Product k => Ok k a => Ok k b => Ok k c
        => k (p a b) c -> k a (k b c)
  -- | Uncurry a function
  uncurry :: p ~ Product k => Ok k a => Ok k b => Ok k c
          => k a (k b c) -> k (p a b) c

law_Closed_apply :: forall k a b c p. Closed k => p ~ Product k
                 => Ok k a => Ok k b => Ok k c
                 => k (p a b) c -> (k (p a b) c, k (p a b) c)
law_Closed_apply f = (f, apply @k . fork (curry @k f . exl) exr)
                     \\ proveCartesian @k @a @b
                     \\ proveCartesian @k @(k b c) @b
                     \\ proveClosed @k @b @c

law_Closed_curry :: Closed k => p ~ Product k => Ok k a => Ok k b => Ok k c
                 => k (p a b) c -> (k (p a b) c, k (p a b) c)
law_Closed_curry f = (f, uncurry (curry f))

law_Closed_uncurry :: Closed k => Ok k a => Ok k b => Ok k c
                   => k a (k b c) -> (k a (k b c), k a (k b c))
law_Closed_uncurry f = (f, curry (uncurry f))



--------------------------------------------------------------------------------



instance Closed (->) where
  proveClosed = Sub Dict
  apply = \(f, x) -> f x
  curry = P.curry
  uncurry = P.uncurry
