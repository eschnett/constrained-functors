{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module CategorySpec where

import Control.Constrained.Category
import Test.QuickCheck.Function
import Test.QuickCheck.Poly



cmp :: Eq a => (a, a) -> Bool
cmp (x, y) = x == y

fcmp :: Eq b => (a -> b, a -> b) -> a -> Bool
fcmp (f, g) x = f x == g x



prop_Category_evalId :: A -> Bool
prop_Category_evalId x = cmp $ law_Category_evalId @(->) x

prop_Category_leftId :: Fun A B -> A -> Bool
prop_Category_leftId (Fn f) = fcmp $ law_Category_leftId @(->) f

prop_Category_rightId :: Fun A B -> A -> Bool
prop_Category_rightId (Fn f) = fcmp $ law_Category_rightId @(->) f

prop_Category_assoc :: Fun C A -> Fun B C -> Fun A B -> A -> Bool
prop_Category_assoc (Fn h) (Fn g) (Fn f) = fcmp $ law_Category_assoc @(->) h g f



prop_Cartesian_leftUnit1 :: A -> Bool
prop_Cartesian_leftUnit1 x = cmp $ law_Cartesian_leftUnit1 @(->) x

prop_Cartesian_leftUnit2 :: A -> Bool
prop_Cartesian_leftUnit2 x = cmp $ law_Cartesian_leftUnit2 @(->) ((), x)

prop_Cartesian_rightUnit1 :: A -> Bool
prop_Cartesian_rightUnit1 x = cmp $ law_Cartesian_rightUnit1 @(->) x

prop_Cartesian_rightUnit2 :: A -> Bool
prop_Cartesian_rightUnit2 x = cmp $ law_Cartesian_rightUnit2 @(->) (x, ())

prop_Cartesian_assoc :: A -> B -> C -> Bool
prop_Cartesian_assoc x y z = cmp $ law_Cartesian_assoc @(->) (x, (y, z))

prop_Cartesian_reassoc :: A -> B -> C -> Bool
prop_Cartesian_reassoc x y z = cmp $ law_Cartesian_reassoc @(->) ((x, y), z)
