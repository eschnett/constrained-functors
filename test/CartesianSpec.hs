{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module CartesianSpec where

import Prelude ()
import Control.Constrained.Prelude

import Control.Constrained.Cartesian
import Test.QuickCheck
import Test.QuickCheck.Poly



cmp :: Eq a => Show a => (a, a) -> Property
cmp (x, y) = x === y

fcmp :: Eq b => Show b => (a -> b, a -> b) -> a -> Property
fcmp (f, g) x = f x === g x

ffcmp :: Eq c => Show c => (a -> b -> c, a -> b -> c) -> a -> b -> Property
ffcmp (f, g) x y = f x y === g x y



prop_Hask_Cartesian_leftUnit1 :: A -> Property
prop_Hask_Cartesian_leftUnit1 = fcmp $ law_Cartesian_leftUnit1 @(->)

prop_Hask_Cartesian_leftUnit2 :: ((), A) -> Property
prop_Hask_Cartesian_leftUnit2 = fcmp $ law_Cartesian_leftUnit2 @(->)

prop_Hask_Cartesian_rightUnit1 :: A -> Property
prop_Hask_Cartesian_rightUnit1 = fcmp $ law_Cartesian_rightUnit1 @(->)

prop_Hask_Cartesian_rightUnit2 :: (A, ()) -> Property
prop_Hask_Cartesian_rightUnit2 = fcmp $ law_Cartesian_rightUnit2 @(->)

prop_Hask_Cartesian_assoc :: ((A, B), C) -> Property
prop_Hask_Cartesian_assoc = fcmp $ law_Cartesian_assoc @(->)

prop_Hask_Cartesian_reassoc :: (A, (B, C)) -> Property
prop_Hask_Cartesian_reassoc = fcmp $ law_Cartesian_reassoc @(->)

prop_Hask_Cartesian_swap :: (A, B) -> Property
prop_Hask_Cartesian_swap = fcmp $ law_Cartesian_swap @(->)

prop_Hask_Cartesian_leftFork :: Fun A B -> Fun A C -> A -> Property
prop_Hask_Cartesian_leftFork (Fn f) (Fn g) =
  fcmp $ law_Cartesian_leftFork @(->) f g

prop_Hask_Cartesian_rightFork :: Fun A B -> Fun A C -> A -> Property
prop_Hask_Cartesian_rightFork (Fn f) (Fn g) =
  fcmp $ law_Cartesian_rightFork @(->) f g

prop_Hask_Cartesian_dup :: A -> Property
prop_Hask_Cartesian_dup = fcmp $ law_Cartesian_dup @(->)
