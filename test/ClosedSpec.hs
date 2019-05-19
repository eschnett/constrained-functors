{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module ClosedSpec where

import qualified Prelude as P
import Control.Constrained.Prelude

import Control.Constrained.Closed
import Test.QuickCheck
import Test.QuickCheck.Poly



cmp :: Eq a => Show a => (a, a) -> Property
cmp (x, y) = x === y

fcmp :: Eq b => Show b => (a -> b, a -> b) -> a -> Property
fcmp (f, g) x = f x === g x

ffcmp :: Eq c => Show c => (a -> b -> c, a -> b -> c) -> a -> b -> Property
ffcmp (f, g) x y = f x y === g x y



prop_Hask_Closed_apply :: Fun (A, B) C -> (A, B) -> Property
prop_Hask_Closed_apply (Fn f) = fcmp $ law_Closed_apply @(->) f

prop_Hask_Closed_curry :: Fun (A, B) C -> (A, B) -> Property
prop_Hask_Closed_curry (Fn f) = fcmp $ law_Closed_curry @(->) f

prop_Hask_Closed_uncurry :: Fun A (Fun B C) -> A -> B -> Property
prop_Hask_Closed_uncurry (Fn f) = ffcmp $ law_Closed_uncurry @(->) f'
  where f' x = applyFun (f x)
