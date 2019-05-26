{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module IVectorSpec where

import Control.Constrained.Applicative
import Control.Constrained.Category
import Control.Constrained.Comonad
import Control.Constrained.Functor
import Control.Constrained.IVector
import Test.QuickCheck
import Test.QuickCheck.Poly



cmp :: Eq a => Show a => (a, a) -> Property
cmp (x, y) = x === y

fcmp :: Eq b => Show b => (a -> b, a -> b) -> a -> Property
fcmp (f, g) x = f x === g x

ffcmp :: Eq c => Show c => (a -> b -> c, a -> b -> c) -> a -> b -> Property
ffcmp (f, g) x y = f x y === g x y



prop_IVector_Functor_id :: IVector A -> Property
prop_IVector_Functor_id = fcmp $ law_Functor_id

prop_IVector_Functor_compose :: Fun B C -> Fun A B -> IVector A -> Property
prop_IVector_Functor_compose (Fn g) (Fn f) = fcmp $ law_Functor_compose g f



prop_IVector_Apply_assoc :: ((IVector A, IVector B), IVector C) -> Property
prop_IVector_Apply_assoc = fcmp $ law_Apply_assoc



prop_IVector_Semicomonad_compose :: Fun (IVector B) C
                                 -> Fun (IVector A) B
                                 -> IVector A
                                 -> Property
prop_IVector_Semicomonad_compose (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_compose g f

prop_IVector_Semicomonad_assoc :: Fun (IVector C) A
                               -> Fun (IVector B) C
                               -> Fun (IVector A) B
                               -> IVector A
                               -> Property
prop_IVector_Semicomonad_assoc (Fn h) (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_assoc h g f

prop_IVector_Semicomonad_extend :: Fun (IVector B) C
                                -> Fun (IVector A) B
                                -> IVector A
                                -> Property
prop_IVector_Semicomonad_extend (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_extend g f

prop_IVector_Semicomonad_duplicate :: IVector A -> Property
prop_IVector_Semicomonad_duplicate = fcmp $ law_Semicomonad_duplicate

prop_Cokleisli_IVector_Semigroupoid_assoc
  :: Fun (IVector C) A
  -> Fun (IVector B) C
  -> Fun (IVector A) B
  -> IVector A
  -> Property
prop_Cokleisli_IVector_Semigroupoid_assoc (Fn h) (Fn g) (Fn f) =
  fcmp $ hask $ law_Semigroupoid_assoc h' g' f'
  where f' = Cokleisli f
        g' = Cokleisli g
        h' = Cokleisli h
        hask (Cokleisli p, Cokleisli q) = (p, q)
