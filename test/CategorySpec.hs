{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module CategorySpec where

import Prelude()
import Control.Constrained.Prelude

import Control.Constrained.Category
import Test.QuickCheck
import Test.QuickCheck.Poly



cmp :: Eq a => Show a => (a, a) -> Property
cmp (x, y) = x === y

fcmp :: Eq b => Show b => (a -> b, a -> b) -> a -> Property
fcmp (f, g) x = f x === g x

ffcmp :: Eq c => Show c => (a -> b -> c, a -> b -> c) -> a -> b -> Property
ffcmp (f, g) x y = f x y === g x y



prop_Hask_Semigroupoid_assoc :: Fun C A -> Fun B C -> Fun A B -> A -> Property
prop_Hask_Semigroupoid_assoc (Fn h) (Fn g) (Fn f) =
  fcmp $ law_Semigroupoid_assoc @(->) h g f

prop_Hask_Category_leftId :: Fun A B -> A -> Property
prop_Hask_Category_leftId (Fn f) = fcmp $ law_Category_leftId @(->) f

prop_Hask_Category_rightId :: Fun A B -> A -> Property
prop_Hask_Category_rightId (Fn f) = fcmp $ law_Category_rightId @(->) f

prop_Hask_SubCatOf_evalId :: A -> Property
prop_Hask_SubCatOf_evalId = fcmp $ law_SubCatOf_embedId @(->)
