{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module CocartesianSpec where

import Prelude()
import Control.Constrained.Prelude

import Control.Constrained.Cocartesian
import Test.QuickCheck
import Test.QuickCheck.Poly



cmp :: Eq a => Show a => (a, a) -> Property
cmp (x, y) = x === y

fcmp :: Eq b => Show b => (a -> b, a -> b) -> a -> Property
fcmp (f, g) x = f x === g x

ffcmp :: Eq c => Show c => (a -> b -> c, a -> b -> c) -> a -> b -> Property
ffcmp (f, g) x y = f x y === g x y



prop_Hask_Cocartesian_leftZero1 :: A -> Property
prop_Hask_Cocartesian_leftZero1 = fcmp $ law_Cocartesian_leftZero1 @(->)

prop_Hask_Cocartesian_leftZero2 :: A -> Property
prop_Hask_Cocartesian_leftZero2 x =
  (fcmp $ law_Cocartesian_leftZero2 @(->)) (Right x)

prop_Hask_Cocartesian_rightZero1 :: A -> Property
prop_Hask_Cocartesian_rightZero1 = fcmp $ law_Cocartesian_rightZero1 @(->)

prop_Hask_Cocartesian_rightZero2 :: A -> Property
prop_Hask_Cocartesian_rightZero2 x =
  (fcmp $ law_Cocartesian_rightZero2 @(->)) (Left x)

prop_Hask_Cocartesian_assoc :: Either (Either A B) C -> Property
prop_Hask_Cocartesian_assoc = fcmp $ law_Cocartesian_assoc @(->)

prop_Hask_Cocartesian_reassoc :: Either A (Either B C) -> Property
prop_Hask_Cocartesian_reassoc = fcmp $ law_Cocartesian_reassoc @(->)

prop_Hask_Cocartesian_swap :: Either A B -> Property
prop_Hask_Cocartesian_swap = fcmp $ law_Cocartesian_swap @(->)

prop_Hask_Cocartesian_leftJoin :: Fun A C -> Fun B C -> A -> Property
prop_Hask_Cocartesian_leftJoin (Fn f) (Fn g) =
  fcmp $ law_Cocartesian_leftJoin @(->) f g

prop_Hask_Cocartesian_rightJoin :: Fun A C -> Fun B C -> B -> Property
prop_Hask_Cocartesian_rightJoin (Fn f) (Fn g) =
  fcmp $ law_Cocartesian_rightJoin @(->) f g

prop_Hask_Cocartesian_jam :: Either A A -> Property
prop_Hask_Cocartesian_jam = fcmp $ law_Cocartesian_jam @(->)
