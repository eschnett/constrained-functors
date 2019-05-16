{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module CategorySpec where

import qualified Prelude as P
import Control.Constrained.Prelude

import Control.Constrained.Category
import Data.Void
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



prop_Hask_Closed_apply :: Fun (A, B) C -> (A, B) -> Property
prop_Hask_Closed_apply (Fn f) = fcmp $ law_Closed_apply @(->) f

prop_Hask_Closed_curry :: Fun (A, B) C -> (A, B) -> Property
prop_Hask_Closed_curry (Fn f) = fcmp $ law_Closed_curry @(->) f

prop_Hask_Closed_uncurry :: Fun A (Fun B C) -> A -> B -> Property
prop_Hask_Closed_uncurry (Fn f) = ffcmp $ law_Closed_uncurry @(->) f'
  where f' x = applyFun (f x)
