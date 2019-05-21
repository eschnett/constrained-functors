{-# LANGUAGE UndecidableInstances #-}

module Control.Constrained.IVector
  ( IVector
  , ivector
  , getIVector
  , getIndex
  ) where

import qualified Prelude as P
import Control.Constrained.Prelude

import Control.Constrained.Applicative
import Control.Constrained.Closed
import Control.Constrained.Comonad
import Control.Constrained.Foldable
import Control.Constrained.Functor
import Data.Constraint
import qualified Data.Vector as V
import GHC.Generics
import Test.QuickCheck
import Test.QuickCheck.Instances()



data IVector a = IVector { getIndex :: Int
                         , getIVector :: V.Vector a
                         }
  deriving (Eq, Ord, Read, Show, Generic)

ivector :: V.Vector a -> IVector a
ivector xs = IVector 0 xs

instance Arbitrary (V.Vector a) => Arbitrary (IVector a) where
  arbitrary = do xs <- arbitrary
                 let n = V.length xs
                 i <- if n == 0 then P.return (-1) else choose (0, n-1)
                 P.return (IVector i xs)
  shrink xs = limitIndex <$> genericShrink xs
    where limitIndex (IVector j ys) = IVector (min j (V.length ys - 1)) ys
instance CoArbitrary (V.Vector a) => CoArbitrary (IVector a)
instance Function (V.Vector a) => Function (IVector a)



instance Functor IVector where
  type Dom IVector = (->)
  type Cod IVector = (->)
  proveFunctor = Sub Dict
  fmap f = \(IVector i xs) -> IVector i (fmap f xs)

instance Foldable IVector where
  foldMap f = \(IVector _ xs) -> foldMap f xs

instance Apply IVector where
  liftA2uu f = \(IVector i xs, IVector j ys) ->
                 IVector (min i j) (V.zipWith (curry f) xs ys)

instance Semicomonad IVector where
  extend f = \(IVector i xs) ->
               let n = V.length xs
               in IVector i (V.fromListN n [f (IVector j xs) | j <- [0..n-1]])
