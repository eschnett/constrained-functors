import Prelude ()
import Control.Constrained.Prelude

import Control.Constrained.Cartesian
import Control.Constrained.Category
import Control.Constrained.Foldable
import Control.Constrained.Functor
import Control.Constrained.Plain
import qualified Data.Monoid as M
import Data.Monoid.Instances ()
import qualified Data.Vector.Unboxed as U



count :: Foldable f => Dom f ~ (-#>) => PCon a => f a -> Int
count xs = M.getSum (foldMap (PFun M.Sum . const 1) xs)

sum :: Foldable f => Dom f ~ (-#>) => Num a => PCon a => PCon (M.Sum a)
    => f a -> a
sum xs = M.getSum (foldMap (PFun M.Sum) xs)

sum2 :: Foldable f => Dom f ~ (-#>) => Num a => PCon a => PCon (M.Sum a)
     => f a -> a
sum2 xs = M.getSum (foldMap (PFun M.Sum . PFun \x -> x^(2::Int)) xs)

norm2 :: PCon a => Floating a => U.Vector a -> a
norm2 xs = rms (sum2 xs) (count xs)
      where rms :: Floating a => Integral i => a -> i -> a
            rms s2 c = sqrt (s2 / fromIntegral c)



coords :: forall a. PCon a => Fractional a => Int -> Int -> U.Vector (a, a)
coords ni nj = U.fromList [ (xi i, yj j) | i <- [0..ni-1], j <- [0..nj-1] ]
       where -- physical boundaries
             xmin = 0
             ymin = 0
             xmax = 1
             ymax = 1
             -- discrete boundaries
             imin = 0 + 1/2
             jmin = 0 + 1/2
             imax = fi ni - 1/2
             jmax = fi nj - 1/2
             -- auxiliary functions
             iavg = (imin + imax) / 2
             javg = (jmin + jmax) / 2
             irad = (imax - imin) / 2
             jrad = (jmax - jmin) / 2
             xavg = (xmin + xmax) / 2
             yavg = (ymin + ymax) / 2
             xrad = (xmax - xmin) / 2
             yrad = (ymax - ymin) / 2
             xi i = xavg + xrad / irad * (fi i - iavg)
             yj j = yavg + yrad / jrad * (fi j - javg)
             fi = fromIntegral

setup :: PCon a => Floating a => Functor f => Dom f ~ (-#>) => Cod f ~ (->)
      => f (a, a) -> f a
setup xs = fmap (PFun f) xs
  where f (x, y) = sin (2*pi*x) * sin (2*pi*y)

-- grad :: PCon a => Fractional a => U.Vector a -> U.Vector (a, a)
-- grad us = 



main :: IO ()
main = do putStrLn "Constrained categories: Numeric functions"
          let xs = coords @Double 100 100
          let us = setup xs
          let u2 = norm2 us
          putStrLn $ "L2[u] = " ++ show u2
          putStrLn "Done."
