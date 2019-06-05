{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module PlainSpec where

import Prelude ()
import Control.Constrained.Prelude

import Control.Constrained.Applicative
import Control.Constrained.Cartesian
import Control.Constrained.Category
import Control.Constrained.Comonad
import Control.Constrained.Foldable
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

prop_PFun_SubCatOf_id :: A -> Property
prop_PFun_SubCatOf_id = fcmp $ law_SubCatOf_id @(-#>) @(->)

prop_Hask_SubCatOf_compose :: Fun B C -> Fun A B -> A -> Property
prop_Hask_SubCatOf_compose (Fn g) (Fn f) =
  fcmp $ law_SubCatOf_compose @(-#>) @(->) (PFun g) (PFun f)



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

-- prop_UIdentity_Inclusion_faithful :: A -> Property
-- prop_UIdentity_Inclusion_faithful x = cmp $ law_Inclusion_faithful @UIdentity x

prop_UIdentity_Apply_assoc :: ((UIdentity A, UIdentity B), UIdentity C)
                           -> Property
prop_UIdentity_Apply_assoc = fcmp $ law_Apply_assoc

prop_UIdentity_Applicative_leftUnit :: ((), UIdentity A) -> Property
prop_UIdentity_Applicative_leftUnit = fcmp $ law_Applicative_leftUnit

prop_UIdentity_Applicative_rightUnit :: (UIdentity A, ()) -> Property
prop_UIdentity_Applicative_rightUnit = fcmp $ law_Applicative_rightUnit

prop_UIdentity_Semicomonad_compose :: Fun (UIdentity B) C
                                   -> Fun (UIdentity A) B
                                   -> UIdentity A
                                   -> Property
prop_UIdentity_Semicomonad_compose (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_compose g f

prop_UIdentity_Semicomonad_assoc :: Fun (UIdentity C) A
                                 -> Fun (UIdentity B) C
                                 -> Fun (UIdentity A) B
                                 -> UIdentity A
                                 -> Property
prop_UIdentity_Semicomonad_assoc (Fn h) (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_assoc h g f

prop_UIdentity_Semicomonad_extend :: Fun (UIdentity B) C
                                  -> Fun (UIdentity A) B
                                  -> UIdentity A
                                  -> Property
prop_UIdentity_Semicomonad_extend (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_extend g f

prop_UIdentity_Comonad_leftId :: UIdentity A -> Property
prop_UIdentity_Comonad_leftId = fcmp $ law_Comonad_leftId

prop_UIdentity_Comonad_rightId :: Fun (UIdentity A) B
                               -> UIdentity A
                               -> Property
prop_UIdentity_Comonad_rightId (Fn f) = fcmp $ law_Comonad_rightId f

prop_Cokleisli_UIdentity_Semigroupoid_assoc
  :: Fun (UIdentity C) A
  -> Fun (UIdentity B) C
  -> Fun (UIdentity A) B
  -> UIdentity A
  -> Property
prop_Cokleisli_UIdentity_Semigroupoid_assoc (Fn h) (Fn g) (Fn f) =
  fcmp $ hask $ law_Semigroupoid_assoc h' g' f'
  where f' = Cokleisli f
        g' = Cokleisli g
        h' = Cokleisli h
        hask (Cokleisli p, Cokleisli q) = (p, q)

prop_Cokleisli_UIdentity_Category_leftId ::
  Fun (UIdentity A) B -> UIdentity A -> Property
prop_Cokleisli_UIdentity_Category_leftId (Fn f) =
  fcmp $ hask $ law_Category_leftId @(Cokleisli UIdentity) f'
  where f' = Cokleisli f
        hask (Cokleisli p, Cokleisli q) = (p, q)

prop_Cokleisli_UIdentity_Category_rightId ::
  Fun (UIdentity A) B -> UIdentity A -> Property
prop_Cokleisli_UIdentity_Category_rightId (Fn f) =
  fcmp $ hask $ law_Category_rightId @(Cokleisli UIdentity) f'
  where f' = Cokleisli f
        hask (Cokleisli p, Cokleisli q) = (p, q)



prop_UPair_Functor_id :: UPair B A -> Property
prop_UPair_Functor_id = fcmp $ law_Functor_id

prop_UPair_Functor_compose :: Fun B C -> Fun A B -> UPair B A -> Property
prop_UPair_Functor_compose (Fn g) (Fn f) =
  fcmp $ law_Functor_compose (PFun g) (PFun f)

prop_UPair_Apply_assoc :: ((UPair B A, UPair B B), UPair B C)
                           -> Property
prop_UPair_Apply_assoc = fcmp $ law_Apply_assoc

prop_UPair_Applicative_leftUnit :: ((), UPair B A) -> Property
prop_UPair_Applicative_leftUnit = fcmp $ law_Applicative_leftUnit

prop_UPair_Applicative_rightUnit :: (UPair B A, ()) -> Property
prop_UPair_Applicative_rightUnit = fcmp $ law_Applicative_rightUnit

prop_UPair_Semicomonad_compose :: Fun (UPair B B) C
                                   -> Fun (UPair B A) B
                                   -> UPair B A
                                   -> Property
prop_UPair_Semicomonad_compose (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_compose g f

prop_UPair_Semicomonad_assoc :: Fun (UPair B C) A
                                 -> Fun (UPair B B) C
                                 -> Fun (UPair B A) B
                                 -> UPair B A
                                 -> Property
prop_UPair_Semicomonad_assoc (Fn h) (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_assoc h g f

prop_UPair_Semicomonad_extend :: Fun (UPair B B) C
                                  -> Fun (UPair B A) B
                                  -> UPair B A
                                  -> Property
prop_UPair_Semicomonad_extend (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_extend g f

prop_UPair_Comonad_leftId :: UPair B A -> Property
prop_UPair_Comonad_leftId = fcmp $ law_Comonad_leftId

prop_UPair_Comonad_rightId :: Fun (UPair B A) B
                               -> UPair B A
                               -> Property
prop_UPair_Comonad_rightId (Fn f) = fcmp $ law_Comonad_rightId f

prop_Cokleisli_UPair_Semigroupoid_assoc
  :: Fun (UPair B C) A
  -> Fun (UPair B B) C
  -> Fun (UPair B A) B
  -> UPair B A
  -> Property
prop_Cokleisli_UPair_Semigroupoid_assoc (Fn h) (Fn g) (Fn f) =
  fcmp $ hask $ law_Semigroupoid_assoc h' g' f'
  where f' = Cokleisli f
        g' = Cokleisli g
        h' = Cokleisli h
        hask (Cokleisli p, Cokleisli q) = (p, q)

prop_Cokleisli_UPair_Category_leftId ::
  Fun (UPair B A) B -> UPair B A -> Property
prop_Cokleisli_UPair_Category_leftId (Fn f) =
  fcmp $ hask $ law_Category_leftId @(Cokleisli (UPair B)) f'
  where f' = Cokleisli f
        hask (Cokleisli p, Cokleisli q) = (p, q)

prop_Cokleisli_UPair_Category_rightId ::
  Fun (UPair B A) B -> UPair B A -> Property
prop_Cokleisli_UPair_Category_rightId (Fn f) =
  fcmp $ hask $ law_Category_rightId @(Cokleisli (UPair B)) f'
  where f' = Cokleisli f
        hask (Cokleisli p, Cokleisli q) = (p, q)

prop_UPair_ComonadStore_getPut :: (B, UPair B A) -> Property
prop_UPair_ComonadStore_getPut = fcmp $ law_ComonadStore_getPut

prop_UPair_ComonadStore_putPut :: ((B, B), UPair B A) -> Property
prop_UPair_ComonadStore_putPut = fcmp $ law_ComonadStore_putPut

prop_UPair_ComonadStore_putGet :: UPair B A -> Property
prop_UPair_ComonadStore_putGet = fcmp $ law_ComonadStore_putGet

prop_UPair_ComonadStore_extract :: UPair B A -> Property
prop_UPair_ComonadStore_extract = fcmp $ law_ComonadStore_extract

prop_UPair_ComonadStore_seek :: (B, UPair B A) -> Property
prop_UPair_ComonadStore_seek = fcmp $ law_ComonadStore_extract



prop_UIVector_Functor_id :: UIVector A -> Property
prop_UIVector_Functor_id = fcmp $ law_Functor_id

prop_UIVector_Functor_compose :: Fun B C -> Fun A B -> UIVector A -> Property
prop_UIVector_Functor_compose (Fn g) (Fn f) =
  fcmp $ law_Functor_compose (PFun g) (PFun f)

prop_UIVector_Apply_assoc :: ((UIVector A, UIVector B), UIVector C) -> Property
prop_UIVector_Apply_assoc = fcmp $ law_Apply_assoc

prop_UIVector_Semicomonad_compose :: Fun (UIVector B) C
                                  -> Fun (UIVector A) B
                                  -> UIVector A
                                  -> Property
prop_UIVector_Semicomonad_compose (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_compose g f

prop_UIVector_Semicomonad_assoc :: Fun (UIVector C) A
                                -> Fun (UIVector B) C
                                -> Fun (UIVector A) B
                                -> UIVector A
                                -> Property
prop_UIVector_Semicomonad_assoc (Fn h) (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_assoc h g f

prop_UIVector_Comonad_leftId :: UIVector A -> Property
prop_UIVector_Comonad_leftId = fcmp $ law_Comonad_leftId

prop_UIVector_Comonad_rightId :: Fun (UIVector A) B -> UIVector A -> Property
prop_UIVector_Comonad_rightId (Fn f) = fcmp $ law_Comonad_rightId f

prop_Cokleisli_UIVector_Semigroupoid_assoc
  :: Fun (UIVector C) A
  -> Fun (UIVector B) C
  -> Fun (UIVector A) B
  -> UIVector A
  -> Property
prop_Cokleisli_UIVector_Semigroupoid_assoc (Fn h) (Fn g) (Fn f) =
  fcmp $ hask $ law_Semigroupoid_assoc h' g' f'
  where f' = Cokleisli f
        g' = Cokleisli g
        h' = Cokleisli h
        hask (Cokleisli p, Cokleisli q) = (p, q)

prop_Cokleisli_UIVector_Category_leftId ::
  Fun (UIVector A) B -> UIVector A -> Property
prop_Cokleisli_UIVector_Category_leftId (Fn f) =
  fcmp $ hask $ law_Category_leftId @(Cokleisli UIVector) f'
  where f' = Cokleisli f
        hask (Cokleisli p, Cokleisli q) = (p, q)

prop_Cokleisli_UIVector_Category_rightId ::
  Fun (UIVector A) B -> UIVector A -> Property
prop_Cokleisli_UIVector_Category_rightId (Fn f) =
  fcmp $ hask $ law_Category_rightId @(Cokleisli UIVector) f'
  where f' = Cokleisli f
        hask (Cokleisli p, Cokleisli q) = (p, q)

prop_UIVector_ComonadStore_getPut :: (NonNegative Int, UIVector A) -> Property
prop_UIVector_ComonadStore_getPut (NonNegative i, xs) =
  i < length xs ==>
  cover 50 (i > 0) "non-trivial" $
  fcmp law_ComonadStore_getPut (i, xs)

prop_UIVector_ComonadStore_putPut ::
  ((NonNegative Int, NonNegative Int), UIVector A) -> Property
prop_UIVector_ComonadStore_putPut ((NonNegative i, NonNegative j), xs) =
  i < length xs && j < length xs ==>
  cover 50 (i > 0 && j > 0) "non-trivial" $
  fcmp law_ComonadStore_putPut ((i, j), xs)

prop_UIVector_ComonadStore_putGet :: UIVector A -> Property
prop_UIVector_ComonadStore_putGet = fcmp law_ComonadStore_putGet

prop_UIVector_ComonadStore_extract :: UIVector A -> Property
prop_UIVector_ComonadStore_extract = fcmp law_ComonadStore_extract

prop_UIVector_ComonadStore_seek :: (NonNegative Int, UIVector A) -> Property
prop_UIVector_ComonadStore_seek (NonNegative i, xs) =
  i < length xs ==>
  cover 50 (i > 0) "non-trivial" $
  fcmp law_ComonadStore_extract (i, xs)
