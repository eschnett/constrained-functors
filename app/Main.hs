import Prelude()
import Control.Constrained.Prelude

import Control.Constrained.Cartesian
import Control.Constrained.Category
import Control.Constrained.Foldable
import Control.Constrained.Functor
import Control.Constrained.Plain
import qualified Data.Monoid as M
import qualified Data.Vector.Unboxed as U



sum :: Foldable f => Dom f ~ (-#>) => Num a => PCon a => PCon (M.Sum a)
    => f a -> a
sum xs = M.getSum (foldMap (PFun M.Sum) xs)

sum2 :: Foldable f => Dom f ~ (-#>) => Num a => PCon a => PCon (M.Sum a)
     => f a -> a
sum2 xs = M.getSum (foldMap (PFun M.Sum . PFun \x -> x^(2::Int)) xs)

count :: Foldable f => Dom f ~ (-#>) => PCon a => f a -> Int
count xs = M.getSum (foldMap (PFun M.Sum . const 1) xs)

norm2 :: PCon a => Floating a => U.Vector a -> a
norm2 xs = rms (sum2 xs) (count xs)
      where rms :: Floating a => Integral i => a -> i -> a
            rms s2 c = sqrt (s2 / fromIntegral c)



coords :: forall a. PCon a => Fractional a => Int -> U.Vector a
coords n = U.fromList [ xavg + xrad / irad * (fi i - iavg)
                      | i <- [0..n-1] ]
       where fi = fromIntegral
             imin = 0 + 1/2
             imax = fi n - 1/2
             xmin = 0
             xmax = 1
             iavg = (imin + imax) / 2
             irad = (imax - imin) / 2
             xavg = (xmin + xmax) / 2
             xrad = (xmax - xmin) / 2

setup :: PCon a => Floating a => U.Vector a -> U.Vector a
setup xs = fmap (PFun \x -> sin (2*pi*x)) xs



main :: IO ()
main = do putStrLn "Constrained categories: Numeric functions"
          let xs = coords @Double 1000
          let us = setup xs
          let u2 = norm2 us
          putStrLn $ "L2[u] = " ++ show u2
          putStrLn "Done."
