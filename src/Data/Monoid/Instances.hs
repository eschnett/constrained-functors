{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Data.Monoid.Instances () where

import Data.Coerce
import qualified Data.Monoid as M
import qualified Data.Vector.Unboxed as U
import Data.Vector.Unboxed.Deriving



derivingUnbox "Monoid_All"
    [t| M.All -> Bool |] [| coerce |] [| coerce |]

derivingUnbox "Monoid_Any"
    [t| M.Any -> Bool |] [| coerce |] [| coerce |]

derivingUnbox "Monoid_Dual"
    [t| forall a. U.Unbox a => M.Dual a -> a |] [| coerce |] [| coerce |]

derivingUnbox "Monoid_Product"
    [t| forall a. U.Unbox a => M.Product a -> a |] [| coerce |] [| coerce |]

derivingUnbox "Monoid_Sum"
    [t| forall a. U.Unbox a => M.Sum a -> a |] [| coerce |] [| coerce |]
