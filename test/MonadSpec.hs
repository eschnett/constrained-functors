{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module MonadSpec where

import Prelude ()
import Control.Constrained.Prelude

import Control.Constrained.Category
import Control.Constrained.Monad
import Test.QuickCheck
import Test.QuickCheck.Poly



cmp :: Eq a => Show a => (a, a) -> Property
cmp (x, y) = x === y

fcmp :: Eq b => Show b => (a -> b, a -> b) -> a -> Property
fcmp (f, g) x = f x === g x

ffcmp :: Eq c => Show c => (a -> b -> c, a -> b -> c) -> a -> b -> Property
ffcmp (f, g) x y = f x y === g x y



prop_Kleisli_List_Semigroupoid_assoc ::
  Fun C [A] -> Fun B [C] -> Fun A [B] -> A -> Property
prop_Kleisli_List_Semigroupoid_assoc (Fn h) (Fn g) (Fn f) =
  fcmp $ hask $ law_Semigroupoid_assoc @(Kleisli []) h' g' f'
  where f' = Kleisli f
        g' = Kleisli g
        h' = Kleisli h
        hask (Kleisli p, Kleisli q) = (p, q)

prop_Kleisli_List_Category_leftId :: Fun A [B] -> A -> Property
prop_Kleisli_List_Category_leftId (Fn f) =
  fcmp $ hask $ law_Category_leftId @(Kleisli []) f'
  where f' = Kleisli f
        hask (Kleisli p, Kleisli q) = (p, q)

prop_Kleisli_List_Category_rightId :: Fun A [B] -> A -> Property
prop_Kleisli_List_Category_rightId (Fn f) =
  fcmp $ hask $ law_Category_rightId @(Kleisli []) f'
  where f' = Kleisli f
        hask (Kleisli p, Kleisli q) = (p, q)
