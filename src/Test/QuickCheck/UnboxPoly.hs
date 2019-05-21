{-# LANGUAGE TemplateHaskell #-}

module Test.QuickCheck.UnboxPoly (A(..), B(..), C(..)) where

import Data.Binary
import Data.Coerce
import Data.Vector.Unboxed.Deriving
import GHC.Generics hiding (C)
import Test.QuickCheck



newtype A = A Int
        deriving (Eq, Ord, Read, Show, Generic)
        deriving (Arbitrary, Binary, CoArbitrary) via Int
derivingUnbox "A" [t| A -> Int |] [| coerce |] [| coerce |]
instance Function A

instance Semigroup A where A x <> A y = A (x + y)
instance Monoid A where mempty = A 0



newtype B = B Int
        deriving (Eq, Ord, Read, Show, Generic)
        deriving (Arbitrary, Binary, CoArbitrary) via Int
derivingUnbox "B" [t| B -> Int |] [| coerce |] [| coerce |]
instance Function B

instance Semigroup B where B x <> B y = B (x + y)
instance Monoid B where mempty = B 0



newtype C = C Int
        deriving (Eq, Ord, Read, Show, Generic)
        deriving (Arbitrary, Binary, CoArbitrary) via Int
derivingUnbox "C" [t| C -> Int |] [| coerce |] [| coerce |]
instance Function C

instance Semigroup C where C x <> C y = C (x + y)
instance Monoid C where mempty = C 0
