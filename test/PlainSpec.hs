{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module PlainSpec where

import Prelude()
import Control.Constrained.Prelude

import Control.Constrained.Applicative
import Control.Constrained.Cartesian
import Control.Constrained.Category
import Control.Constrained.Comonad'
import Control.Constrained.Functor
import Control.Constrained.Plain
import Test.QuickCheck
import Test.QuickCheck.UnboxPoly



cmp :: Eq a => Show a => (a, a) -> Property
cmp (x, y) = x === y

fcmp :: HaskSubCat k => Ok k a => Ok k b => Eq b => Show b
     => (k a b, k a b) -> a -> Property
fcmp (f, g) x = eval f x === eval g x



--------------------------------------------------------------------------------

-- Category



prop_PFun_Semigroupoid_assoc :: Fun C A -> Fun B C -> Fun A B -> A -> Property
prop_PFun_Semigroupoid_assoc (Fn h) (Fn g) (Fn f) =
  fcmp $ law_Semigroupoid_assoc @(-#>) (PFun h) (PFun g) (PFun f)

prop_PFun_Category_leftId :: Fun A B -> A -> Property
prop_PFun_Category_leftId (Fn f) = fcmp $ law_Category_leftId @(-#>) (PFun f)

prop_PFun_Category_rightId :: Fun A B -> A -> Property
prop_PFun_Category_rightId (Fn f) = fcmp $ law_Category_rightId @(-#>) (PFun f)

prop_PFun_SubCatOf_embedId :: A -> Property
prop_PFun_SubCatOf_embedId = fcmp $ law_SubCatOf_embedId @(-#>) @(->)



prop_PFun_Cartesian_leftUnit1 :: A -> Property
prop_PFun_Cartesian_leftUnit1 = fcmp $ law_Cartesian_leftUnit1 @(-#>)

prop_PFun_Cartesian_leftUnit2 :: ((), A) -> Property
prop_PFun_Cartesian_leftUnit2 = fcmp $ law_Cartesian_leftUnit2 @(-#>)

prop_PFun_Cartesian_rightUnit1 :: A -> Property
prop_PFun_Cartesian_rightUnit1 = fcmp $ law_Cartesian_rightUnit1 @(-#>)

prop_PFun_Cartesian_rightUnit2 :: (A, ()) -> Property
prop_PFun_Cartesian_rightUnit2 = fcmp $ law_Cartesian_rightUnit2 @(-#>)

prop_PFun_Cartesian_assoc :: ((A, B), C) -> Property
prop_PFun_Cartesian_assoc = fcmp $ law_Cartesian_assoc @(-#>)

prop_PFun_Cartesian_reassoc :: (A, (B, C)) -> Property
prop_PFun_Cartesian_reassoc = fcmp $ law_Cartesian_reassoc @(-#>)

prop_PFun_Cartesian_swap :: (A, B) -> Property
prop_PFun_Cartesian_swap = fcmp $ law_Cartesian_swap @(-#>)

prop_PFun_Cartesian_leftFork :: Fun A B -> Fun A C -> A -> Property
prop_PFun_Cartesian_leftFork (Fn f) (Fn g) =
  fcmp $ law_Cartesian_leftFork @(-#>) (PFun f) (PFun g)

prop_PFun_Cartesian_rightFork :: Fun A B -> Fun A C -> A -> Property
prop_PFun_Cartesian_rightFork (Fn f) (Fn g) =
  fcmp $ law_Cartesian_rightFork @(-#>) (PFun f) (PFun g)

prop_PFun_Cartesian_dup :: A -> Property
prop_PFun_Cartesian_dup = fcmp $ law_Cartesian_dup @(-#>)



--------------------------------------------------------------------------------

-- Endofunctors



prop_PPProxy_Functor_id :: PProxy A -> Property
prop_PPProxy_Functor_id = fcmp $ law_Functor_id

prop_PPProxy_Functor_compose :: Fun B C -> Fun A B -> PProxy A -> Property
prop_PPProxy_Functor_compose (Fn g) (Fn f) =
  fcmp $ law_Functor_compose (PFun g) (PFun f)

prop_PProxy_Apply_assoc :: ((PProxy A, PProxy B), PProxy C) -> Property
prop_PProxy_Apply_assoc = fcmp $ law_Apply_assoc

prop_PProxy_Applicative_leftUnit :: ((), PProxy A) -> Property
prop_PProxy_Applicative_leftUnit = fcmp $ law_Applicative_leftUnit

prop_PProxy_Applicative_rightUnit :: (PProxy A, ()) -> Property
prop_PProxy_Applicative_rightUnit = fcmp $ law_Applicative_rightUnit



prop_PIdentity_Functor_id :: PIdentity A -> Property
prop_PIdentity_Functor_id = fcmp $ law_Functor_id

prop_PIdentity_Functor_compose :: Fun B C -> Fun A B -> PIdentity A -> Property
prop_PIdentity_Functor_compose (Fn g) (Fn f) =
  fcmp $ law_Functor_compose (PFun g) (PFun f)

prop_PIdentity_Apply_assoc :: ((PIdentity A, PIdentity B), PIdentity C)
                           -> Property
prop_PIdentity_Apply_assoc = fcmp $ law_Apply_assoc

prop_PIdentity_Applicative_leftUnit :: ((), PIdentity A) -> Property
prop_PIdentity_Applicative_leftUnit = fcmp $ law_Applicative_leftUnit

prop_PIdentity_Applicative_rightUnit :: (PIdentity A, ()) -> Property
prop_PIdentity_Applicative_rightUnit = fcmp $ law_Applicative_rightUnit



prop_PTuple_Functor_id :: PTuple B A -> Property
prop_PTuple_Functor_id = fcmp $ law_Functor_id

prop_PTuple_Functor_compose :: Fun B C -> Fun A B -> PTuple B A -> Property
prop_PTuple_Functor_compose (Fn g) (Fn f) =
  fcmp $ law_Functor_compose (PFun g) (PFun f)

prop_PTuple_Apply_assoc :: ((PTuple B A, PTuple B B), PTuple B C) -> Property
prop_PTuple_Apply_assoc = fcmp $ law_Apply_assoc

prop_PTuple_Applicative_leftUnit :: ((), PTuple B A) -> Property
prop_PTuple_Applicative_leftUnit = fcmp $ law_Applicative_leftUnit

prop_PTuple_Applicative_rightUnit :: (PTuple B A, ()) -> Property
prop_PTuple_Applicative_rightUnit = fcmp $ law_Applicative_rightUnit



type PProd a = PProduct (PTuple B) PIdentity a

prop_PProduct_Functor_id :: PProd A -> Property
prop_PProduct_Functor_id = fcmp $ law_Functor_id

prop_PProduct_Functor_compose :: Fun B C -> Fun A B -> PProd A -> Property
prop_PProduct_Functor_compose (Fn g) (Fn f) =
  fcmp $ law_Functor_compose (PFun g) (PFun f)

prop_PProduct_Apply_assoc :: ((PProd A, PProd B), PProd C) -> Property
prop_PProduct_Apply_assoc = fcmp $ law_Apply_assoc

prop_PProduct_Applicative_leftUnit :: ((), PProd A) -> Property
prop_PProduct_Applicative_leftUnit = fcmp $ law_Applicative_leftUnit

prop_PProduct_Applicative_rightUnit :: (PProd A, ()) -> Property
prop_PProduct_Applicative_rightUnit = fcmp $ law_Applicative_rightUnit



type PComp a = PCompose (PTuple B) PIdentity a

prop_PCompose_Functor_id :: PComp A -> Property
prop_PCompose_Functor_id = fcmp $ law_Functor_id

prop_PCompose_Functor_compose :: Fun B C -> Fun A B -> PComp A -> Property
prop_PCompose_Functor_compose (Fn g) (Fn f) =
  fcmp $ law_Functor_compose (PFun g) (PFun f)

prop_PCompose_Apply_assoc :: ((PComp A, PComp B), PComp C) -> Property
prop_PCompose_Apply_assoc = fcmp $ law_Apply_assoc

prop_PCompose_Applicative_leftUnit :: ((), PComp A) -> Property
prop_PCompose_Applicative_leftUnit = fcmp $ law_Applicative_leftUnit

prop_PCompose_Applicative_rightUnit :: (PComp A, ()) -> Property
prop_PCompose_Applicative_rightUnit = fcmp $ law_Applicative_rightUnit



--------------------------------------------------------------------------------

-- Exofunctors



prop_UIdentity_Functor_id :: UIdentity A -> Property
prop_UIdentity_Functor_id = fcmp $ law_Functor_id

prop_UIdentity_Functor_compose :: Fun B C -> Fun A B -> UIdentity A -> Property
prop_UIdentity_Functor_compose (Fn g) (Fn f) =
  fcmp $ law_Functor_compose (PFun g) (PFun f)

prop_UIdentity_Inclusion_faithful :: A -> Property
prop_UIdentity_Inclusion_faithful x = cmp $ law_Inclusion_faithful @UIdentity x

prop_UIdentity_Apply_assoc :: ((UIdentity A, UIdentity B), UIdentity C)
                           -> Property
prop_UIdentity_Apply_assoc = fcmp $ law_Apply_assoc



prop_UIVector_Functor_id :: UIVector A -> Property
prop_UIVector_Functor_id = fcmp $ law_Functor_id

prop_UIVector_Functor_compose :: Fun B C -> Fun A B -> UIVector A -> Property
prop_UIVector_Functor_compose (Fn g) (Fn f) =
  fcmp $ law_Functor_compose (PFun g) (PFun f)

prop_UIVector_Apply_assoc :: ((UIVector A, UIVector B), UIVector C) -> Property
prop_UIVector_Apply_assoc = fcmp $ law_Apply_assoc

prop_UIVector_Semicomonad_compose :: Fun (UIVector B) (UIdentity C)
                                  -> Fun (UIVector A) (UIdentity B)
                                  -> UIVector A
                                  -> Property
prop_UIVector_Semicomonad_compose (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_compose g f

prop_UIVector_Semicomonad_assoc :: Fun (UIVector C) (UIdentity A)
                                -> Fun (UIVector B) (UIdentity C)
                                -> Fun (UIVector A) (UIdentity B)
                                -> UIVector A
                                -> Property
prop_UIVector_Semicomonad_assoc (Fn h) (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_assoc h g f

prop_Cokleisli_UIVector_Semigroupoid_assoc
  :: Fun (UIVector C) (UIdentity A)
  -> Fun (UIVector B) (UIdentity C)
  -> Fun (UIVector A) (UIdentity B)
  -> UIVector A
  -> Property
prop_Cokleisli_UIVector_Semigroupoid_assoc (Fn h) (Fn g) (Fn f) =
  fcmp $ hask $ law_Semigroupoid_assoc h' g' f'
  where f' = Cokleisli f
        g' = Cokleisli g
        h' = Cokleisli h
        hask (Cokleisli p, Cokleisli q) = (p, q)
