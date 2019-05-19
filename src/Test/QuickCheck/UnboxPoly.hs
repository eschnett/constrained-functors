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

newtype B = B Int
        deriving (Eq, Ord, Read, Show, Generic)
        deriving (Arbitrary, Binary, CoArbitrary) via Int
derivingUnbox "B" [t| B -> Int |] [| coerce |] [| coerce |]
instance Function B

newtype C = C Int
        deriving (Eq, Ord, Read, Show, Generic)
        deriving (Arbitrary, Binary, CoArbitrary) via Int
derivingUnbox "C" [t| C -> Int |] [| coerce |] [| coerce |]
instance Function C
