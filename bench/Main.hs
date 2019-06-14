-- You can benchmark your code quickly and effectively with Criterion. See its
-- website for help: <http://www.serpentine.com/criterion/>.
import Criterion.Main

import qualified Prelude as P
import Control.Constrained.Prelude

import Control.Constrained.Applicative
import Control.Constrained.Comonad
import Control.Constrained.Foldable
import Control.Constrained.Plain
import Data.Monoid.Instances ()
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import System.IO.Unsafe



bench_VVector_sum :: forall a. Num a => Int -> a -> a
bench_VVector_sum n z = V.foldl (+) z xs
  where xs = V.fromListN n [fromIntegral i | i <- [0 .. n-1]]

bench_UVector_sum :: forall a. Num a => U.Unbox a => Int -> a -> a
bench_UVector_sum n z = U.foldl (+) z xs
  where xs = U.fromListN n [fromIntegral i | i <- [0 .. n-1]]

bench_UIVector_sum :: forall a. Num a => PCon a => Int -> a -> a
bench_UIVector_sum n z = foldl add z xs
  where xs = uivector $ U.fromListN n [fromIntegral i | i <- [0 .. n-1]]
        add = PFun \(x, y) -> x + y



bench_UVector_make :: forall a. Num a => U.Unbox a => Int -> a -> a
bench_UVector_make n z = U.foldl (+) 0 xs
  where xs = U.fromListN n [fromIntegral i | i <- [0 .. n-1]]

bench_UIVector_make :: forall a. Num a => PCon a => Int -> a -> a
bench_UIVector_make n z = foldl add 0 xs
  where xs = uivector $ U.fromListN n [fromIntegral i | i <- [0 .. n-1]]
        add = PFun \(x, y) -> x + y



bench_UVector_add :: forall a. Num a => U.Unbox a => Int -> a -> a
bench_UVector_add n z = U.foldl (+) z $ U.zipWith (+) xs ys
  where xs = U.fromListN n [fromIntegral i | i <- [0 .. n-1]]
        ys = U.fromListN n [fromIntegral i | i <- [n-1, n-2 .. 0]]

bench_UIVector_add :: forall a. Num a => PCon a => Int -> a -> a
bench_UIVector_add n z = foldl add z $ liftA2u add xs ys
  where xs = uivector $ U.fromListN n [fromIntegral i | i <- [0 .. n-1]]
        ys = uivector $ U.fromListN n [fromIntegral i | i <- [n-1, n-2 .. 0]]
        add = PFun \(x, y) -> x + y



bench_UVector_deriv :: forall a. Fractional a => U.Unbox a => Int -> a -> a
bench_UVector_deriv n z = U.foldl (+) z $
                          U.fromListN n [dx xs i | i <- [0 .. n-1]]
  where xs = U.fromListN n [fromIntegral i | i <- [0 .. n-1]]
        dx xs i = let n = U.length xs
                  in if | n == 1 -> 0
                        | i == 0 -> (xs U.! (i+1)) - (xs U.! i)
                        | i == n-1 -> (xs U.! i) - (xs U.! (i-1))
                        | otherwise -> ((xs U.! (i+1)) - (xs U.! (i-1))) / 2

bench_UIVector_deriv :: forall a. Fractional a => PCon a => Int -> a -> a
bench_UIVector_deriv n z = foldl add z $ extend dx xs
  where xs = uivector $ U.fromListN n [fromIntegral i | i <- [0 .. n-1]]
        dx xs = let i = pos xs
                    n = length xs
                in if | n == 1 -> 0
                      | i == 0 -> peek (i+1) xs - peek i xs
                      | i == n-1 -> peek i xs - peek (i-1) xs
                      | otherwise -> (peek (i+1) xs - peek (i-1) xs) / 2
        add = PFun \(x, y) -> x + y


vsize :: Int
vsize = 1_000_000

main :: IO ()
main = defaultMain
  [ bgroup "sum"
    [ bench "Boxed" (nf (bench_VVector_sum @Double vsize) 0)
    , bench "Unboxed" (nf (bench_UVector_sum @Double vsize) 0)
    , bench "Plain" (nf (bench_UIVector_sum @Double vsize) 0)
    ]
  , bgroup "make"
    [ bench "Unboxed" (nf (bench_UVector_make @Double vsize) 0)
    , bench "Plain" (nf (bench_UIVector_make @Double vsize) 0)
    ]
  , bgroup "add"
    [ bench "Unboxed" (nf (bench_UVector_add @Double vsize) 0)
    , bench "Plain" (nf (bench_UIVector_add @Double vsize) 0)
    ]
  , bgroup "deriv"
    [ bench "Unboxed" (nf (bench_UVector_deriv @Double vsize) 0)
    , bench "Plain" (nf (bench_UIVector_deriv @Double vsize) 0)
    ]
  ]
