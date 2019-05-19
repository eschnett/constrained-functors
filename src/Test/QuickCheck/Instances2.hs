{-# OPTIONS_GHC -Wno-orphans #-}

module Test.QuickCheck.Instances2 () where

import qualified Data.Functor.Sum as F
import Data.Proxy
import Test.QuickCheck
import Test.QuickCheck.Poly



instance Semigroup A where A x <> A y = A (x + y)
instance Monoid A where mempty = A 0

instance Semigroup B where B x <> B y = B (x + y)
instance Monoid B where mempty = B 0

instance Semigroup C where C x <> C y = C (x + y)
instance Monoid C where mempty = C 0



instance Arbitrary (Proxy a) where
  arbitrary = (\() -> Proxy) <$> arbitrary
instance CoArbitrary (Proxy a)
instance Function (Proxy a)



fs2e :: F.Sum f g a -> Either (f a) (g a)
fs2e (F.InL xs) = Left xs
fs2e (F.InR ys) = Right ys

e2fs :: Either (f a) (g a) -> F.Sum f g a
e2fs (Left xs) = F.InL xs
e2fs (Right xs) = F.InR xs

instance (Arbitrary (f a), Arbitrary (g a)) => Arbitrary (F.Sum f g a) where
  arbitrary = e2fs <$> arbitrary
  shrink x = e2fs <$> shrink (fs2e x)
instance (CoArbitrary (f a), CoArbitrary (g a)) => CoArbitrary (F.Sum f g a)
instance (Function (f a), Function (g a)) => Function (F.Sum f g a)
