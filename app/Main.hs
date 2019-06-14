import qualified Prelude as P
import Control.Constrained.Prelude

import Control.Constrained.Applicative
import Control.Constrained.Category
import Control.Constrained.Comonad
import Control.Constrained.Foldable
import Control.Constrained.Functor
import Control.Constrained.Plain
import qualified Control.Monad as P
import Data.Aeson (genericToEncoding, defaultOptions)
import Data.Complex
import qualified Data.Monoid as M
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid.Instances ()
import qualified Data.Vector.Unboxed as U
import Data.Text (Text)
import Data.Yaml
import Formatting
import System.Directory



sum :: Foldable f => Dom f ~ (-#>) => Num a => PCon a => PCon (M.Sum a)
    => f a -> a
sum xs = M.getSum (foldMap (PFun M.Sum) xs)

sum2 :: Foldable f => Dom f ~ (-#>) => Num a => PCon a => PCon (M.Sum a)
     => f a -> a
sum2 xs = M.getSum (foldMap (PFun M.Sum . PFun \x -> x^(2::Int)) xs)

integral :: PCon a => Floating a => UIVector a -> a
integral xs = sum xs / fromIntegral (length xs)

norm2 :: PCon a => Floating a => UIVector a -> a
norm2 xs = rms (sum2 xs) (length xs)
  where rms :: Floating a => Integral i => a -> i -> a
        rms s2 c = sqrt (s2 / fromIntegral c)



-- physical boundaries
xmin :: Fractional a => a
xmin = 0
xmax :: Fractional a => a
xmax = 1

-- discretization
npts :: Int
npts = 100
hgsp :: Fractional a => a
hgsp = (xmax - xmin) / fromIntegral npts

cfl :: Fractional a => a
cfl = 0.5
nsteps :: Int
nsteps = 200



coord :: Fractional a => Int -> a
coord i = xavg + xrad / irad * (fromIntegral i - iavg)
  where -- discrete boundaries
        imin = -1/2
        imax = fromIntegral npts + 1/2
        -- auxiliary functions
        iavg = (imin + imax) / 2
        irad = (imax - imin) / 2
        xavg = (xmin + xmax) / 2
        xrad = (xmax - xmin) / 2

-- TODO: implement 'ToList UIVector', use it
coords :: PCon a => Fractional a => UIVector a
coords = uivector . U.fromListN npts . fmap coord $ [0..npts-1]



setup :: Floating a => a -#> Complex a
setup = PFun \x -> sin (2*pi*x) :+ 0

setups :: Functor f => Dom f ~ (-#>) => Cod f ~ (->)
       => PCon a => Floating a
       => f a -> f (Complex a)
setups = fmap setup



deriv :: ComonadStore f
      => Cod f ~ (->) => Eq (Index f) => Num (Index f)
      => Ok (Dom f) a => Fractional a
      => f a -> a
deriv xs = if | n == 0 -> 0
              | i == 0 -> (peek (i+1) xs - peek i xs) / hgsp
              | i == n-1 -> (peek i xs - peek (i-1) xs) / hgsp
              | otherwise -> (peek (i+1) xs - peek (i-1) xs) / (2 * hgsp)
  where i = pos xs
        n = fromIntegral npts

derivs :: ComonadStore f
       => Cod f ~ (->) => Eq (Index f) => Num (Index f)
       => Ok (Dom f) a => Fractional a
       => f a -> f a
derivs = extend deriv



energy :: ComonadStore f
       => Cod f ~ (->) => Eq (Index f) => Num (Index f)
       => Ok (Dom f) (Complex a) => RealFloat a
       => f (Complex a) -> a
energy us = (realPart du ^^ (2::Int) + imagPart du ^^ (2::Int)) / 2
   where du = deriv us

energies :: ComonadStore f
         => Cod f ~ (->) => Eq (Index f) => Num (Index f)
         => Ok (Dom f) a => Ok (Dom f) (Complex a) => RealFloat a
         => f (Complex a) -> f a
energies = extend energy



rhs :: ComonadStore f
    => Cod f ~ (->) => Eq (Index f) => Num (Index f)
    => Ok (Dom f) (Complex a) => RealFloat a
    => f (Complex a) -> Complex a
rhs us = du
   where du = deriv us

rhss :: ComonadStore f
     => Cod f ~ (->) => Eq (Index f) => Num (Index f)
     => Ok (Dom f) (Complex a) => RealFloat a
     => f (Complex a) -> f (Complex a)
rhss = extend rhs



rk2 :: Apply f
    => Dom f ~ (-#>) => Cod f ~ (->)
    => Ok (Dom f) a => Fractional a
    => (f a -> f a) -> a -> f a -> f a
rk2 f dx y0 = let k0 = f y0
                  y1 = liftA2u (PFun \(y, k) -> y + 0.5 * dx * k) y0 k0
                  k1 = f y1
                  y2 = liftA2u (PFun \(y, k) -> y + dx * k) y0 k1
              in y2



outputFilePath :: Int -> FilePath
outputFilePath i =
  formatToString ("output/wavetoy.it" % (left 6 '0' %. int) % ".yaml") i

instance (ToJSON a, PCon a) => ToJSON (Complex a) where
  toEncoding = genericToEncoding defaultOptions

instance (ToJSON a, PCon a) => ToJSON (UIVector a) where
  toJSON = toJSON . getUIVector
  toEncoding = toEncoding . getUIVector

data JSONData where
  JD :: ToJSON a => a -> JSONData

instance ToJSON JSONData where
  toJSON (JD x) = toJSON x
  toEncoding (JD x) = toEncoding x

output :: FilePath -> Map Text JSONData -> IO ()
output = encodeFile



main':: IO ()
main'= do putStrLn "Constrained functors: Numeric functions"
          let x = coords @Double
          putStrLn $ "L2[x] = " ++ show (norm2 x)
          let u0 = setups x
          putStrLn $ "L2[u0] = " ++ show (realPart (norm2 u0))
          let e0 = energies u0
          putStrLn $ "E0 = " ++ show (integral e0)
          -- let du = rhss u0
          -- putStrLn $ "L2[du] = " ++ show (realPart (norm2 du))
          -- let u1 = rk2 rhss (cfl * hgsp) u0
          -- putStrLn $ "L2[u1] = " ++ show (realPart (norm2 u1))
          let step :: PCon a => RealFloat a
                   => UIVector (Complex a) -> UIVector (Complex a)
              step = rk2 rhss (cfl * hgsp)
          let uis = take (nsteps + 1) (P.iterate step u0)
          createDirectoryIfMissing True "output"
          P.forM (zip [0..] uis) \(i, u) ->
            do putStrLn $ "Iteration " ++ show i
               putStrLn $ "  L2[u] = " ++ show (realPart (norm2 u))
               let e = energies u
               putStrLn $ "  E = " ++ show (integral e)
               let vars = Map.fromList [ ("iteration", JD i)
                                       , ("x", JD x)
                                       , ("u", JD u0)
                                       , ("e", JD e0)
                                       ]
               P.when (i `mod` 10 == 0) $
                 output (outputFilePath i) vars
          putStrLn "Done."



bench_UIVector_add :: forall a. Enum a => Num a => PCon a => Int -> a -> a
bench_UIVector_add n z = foldl add z $ liftA2u add xs ys
  where xs = uivector $ U.fromListN n [0 .. fromIntegral n - 1]
        ys = uivector $
             U.fromListN n [fromIntegral n - 1, fromIntegral n - 2 .. 0]
        add = PFun \(x, y) -> x + y

main :: IO ()
main = putStrLn $ show $ bench_UIVector_add @Double 1000000 0
