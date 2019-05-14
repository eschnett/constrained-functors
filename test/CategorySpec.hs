{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module CategorySpec where

import Control.Constrained.Category
import Test.QuickCheck.Function
import Test.QuickCheck.Poly



cmp :: Eq a => (a, a) -> Bool
cmp (x, y) = x == y

fcmp :: Eq b => (a -> b, a -> b) -> a -> Bool
fcmp (f, g) x = f x == g x

ffcmp :: Eq c => (a -> b -> c, a -> b -> c) -> a -> b -> Bool
ffcmp (f, g) x y = f x y == g x y



prop_Hask_Category_evalId :: A -> Bool
prop_Hask_Category_evalId x = cmp $ law_Category_evalId @(->) x

prop_Hask_Category_leftId :: Fun A B -> A -> Bool
prop_Hask_Category_leftId (Fn f) = fcmp $ law_Category_leftId @(->) f

prop_Hask_Category_rightId :: Fun A B -> A -> Bool
prop_Hask_Category_rightId (Fn f) = fcmp $ law_Category_rightId @(->) f

prop_Hask_Category_assoc :: Fun C A -> Fun B C -> Fun A B -> A -> Bool
prop_Hask_Category_assoc (Fn h) (Fn g) (Fn f) =
  fcmp $ law_Category_assoc @(->) h g f



prop_Hask_Cartesian_leftUnit1 :: A -> Bool
prop_Hask_Cartesian_leftUnit1 x = cmp $ law_Cartesian_leftUnit1 @(->) x

prop_Hask_Cartesian_leftUnit2 :: A -> Bool
prop_Hask_Cartesian_leftUnit2 x = cmp $ law_Cartesian_leftUnit2 @(->) ((), x)

prop_Hask_Cartesian_rightUnit1 :: A -> Bool
prop_Hask_Cartesian_rightUnit1 x = cmp $ law_Cartesian_rightUnit1 @(->) x

prop_Hask_Cartesian_rightUnit2 :: A -> Bool
prop_Hask_Cartesian_rightUnit2 x = cmp $ law_Cartesian_rightUnit2 @(->) (x, ())

prop_Hask_Cartesian_assoc :: (A, (B, C)) -> Bool
prop_Hask_Cartesian_assoc p = cmp $ law_Cartesian_assoc @(->) p

prop_Hask_Cartesian_reassoc :: ((A, B), C) -> Bool
prop_Hask_Cartesian_reassoc p = cmp $ law_Cartesian_reassoc @(->) p

prop_Hask_Cartesian_swap :: (A, B) -> Bool
prop_Hask_Cartesian_swap p = cmp $ law_Cartesian_swap @(->) p

prop_Hask_Cartesian_leftFork :: Fun A B -> Fun A C -> A -> Bool
prop_Hask_Cartesian_leftFork (Fn f) (Fn g) =
  fcmp $ law_Cartesian_leftFork @(->) f g

prop_Hask_Cartesian_rightFork :: Fun A B -> Fun A C -> A -> Bool
prop_Hask_Cartesian_rightFork (Fn f) (Fn g) =
  fcmp $ law_Cartesian_rightFork @(->) f g



prop_Hask_Cocartesian_leftZero1 :: A -> Bool
prop_Hask_Cocartesian_leftZero1 x = cmp $ law_Cocartesian_leftZero1 @(->) x

prop_Hask_Cocartesian_leftZero2 :: A -> Bool
prop_Hask_Cocartesian_leftZero2 x =
  cmp $ law_Cocartesian_leftZero2 @(->) (Right x)

prop_Hask_Cocartesian_rightZero1 :: A -> Bool
prop_Hask_Cocartesian_rightZero1 x = cmp $ law_Cocartesian_rightZero1 @(->) x

prop_Hask_Cocartesian_rightZero2 :: A -> Bool
prop_Hask_Cocartesian_rightZero2 x =
  cmp $ law_Cocartesian_rightZero2 @(->) (Left x)

prop_Hask_Cocartesian_assoc :: Either A (Either B C) -> Bool
prop_Hask_Cocartesian_assoc s = cmp $ law_Cocartesian_assoc @(->) s

prop_Hask_Cocartesian_reassoc :: Either (Either A B) C -> Bool
prop_Hask_Cocartesian_reassoc s = cmp $ law_Cocartesian_reassoc @(->) s

prop_Hask_Cocartesian_swap :: Either A B -> Bool
prop_Hask_Cocartesian_swap s = cmp $ law_Cocartesian_swap @(->) s

prop_Hask_Cocartesian_leftJoin :: Fun A C -> Fun B C -> A -> Bool
prop_Hask_Cocartesian_leftJoin (Fn f) (Fn g) =
  fcmp $ law_Cocartesian_leftJoin @(->) f g

prop_Hask_Cocartesian_rightJoin :: Fun A C -> Fun B C -> B -> Bool
prop_Hask_Cocartesian_rightJoin (Fn f) (Fn g) =
  fcmp $ law_Cocartesian_rightJoin @(->) f g



prop_Hask_Closed_apply :: Fun (A, B) C -> (A, B) -> Bool
prop_Hask_Closed_apply (Fn f) = fcmp $ law_Closed_apply @(->) f

prop_Hask_Closed_curry :: Fun (A, B) C -> (A, B) -> Bool
prop_Hask_Closed_curry (Fn f) = fcmp $ law_Closed_curry @(->) f

prop_Hask_Closed_uncurry :: Fun A (Fun B C) -> A -> B -> Bool
prop_Hask_Closed_uncurry (Fn f) = ffcmp $ law_Closed_uncurry @(->) f'
  where f' x = applyFun (f x)
