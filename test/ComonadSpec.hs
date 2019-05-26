{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module ComonadSpec where

import Prelude ()
import Control.Constrained.Prelude

import Control.Constrained.Category
import Control.Constrained.Comonad
import Data.Functor.Identity
import qualified Data.Functor.Sum as F
import qualified Data.List.NonEmpty as NE
import Data.Proxy
import Test.QuickCheck
import Test.QuickCheck.Instances.Semigroup ()
import Test.QuickCheck.Poly



cmp :: Eq a => Show a => (a, a) -> Property
cmp (x, y) = x === y

fcmp :: Eq b => Show b => (a -> b, a -> b) -> a -> Property
fcmp (f, g) x = f x === g x

ffcmp :: Eq c => Show c => (a -> b -> c, a -> b -> c) -> a -> b -> Property
ffcmp (f, g) x y = f x y === g x y



prop_Proxy_Semicomonad_compose :: Fun (Proxy B) C
                               -> Fun (Proxy A) B
                               -> Proxy A
                               -> Property
prop_Proxy_Semicomonad_compose (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_compose g f

prop_Proxy_Semicomonad_assoc :: Fun (Proxy C) A
                             -> Fun (Proxy B) C
                             -> Fun (Proxy A) B
                             -> Proxy A
                             -> Property
prop_Proxy_Semicomonad_assoc (Fn h) (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_assoc h g f

prop_Proxy_Semicomonad_extend :: Fun (Proxy B) C
                              -> Fun (Proxy A) B
                              -> Proxy A
                              -> Property
prop_Proxy_Semicomonad_extend (Fn g) (Fn f) = fcmp $ law_Semicomonad_extend g f

prop_Proxy_Semicomonad_duplicate :: Proxy A -> Property
prop_Proxy_Semicomonad_duplicate = fcmp $ law_Semicomonad_duplicate



prop_Identity_Semicomonad_compose :: Fun (Identity B) C
                                  -> Fun (Identity A) B
                                  -> Identity A
                                  -> Property
prop_Identity_Semicomonad_compose (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_compose g f

prop_Identity_Semicomonad_assoc :: Fun (Identity C) A
                                -> Fun (Identity B) C
                                -> Fun (Identity A) B
                                -> Identity A
                                -> Property
prop_Identity_Semicomonad_assoc (Fn h) (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_assoc h g f

prop_Identity_Semicomonad_extend :: Fun (Identity B) C
                                 -> Fun (Identity A) B
                                 -> Identity A
                                 -> Property
prop_Identity_Semicomonad_extend (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_extend g f

prop_Identity_Semicomonad_duplicate :: Identity A -> Property
prop_Identity_Semicomonad_duplicate = fcmp $ law_Semicomonad_duplicate

prop_Identity_Comonad_leftId :: Identity A -> Property
prop_Identity_Comonad_leftId = fcmp $ law_Comonad_leftId

prop_Identity_Comonad_rightId :: Fun (Identity A) B -> Identity A -> Property
prop_Identity_Comonad_rightId (Fn f) = fcmp $ law_Comonad_rightId f



prop_Tuple_Semicomonad_compose :: Fun (B, B) C
                               -> Fun (B, A) B
                               -> (B, A)
                               -> Property
prop_Tuple_Semicomonad_compose (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_compose g f

prop_Tuple_Semicomonad_assoc :: Fun (B, C) A
                             -> Fun (B, B) C
                             -> Fun (B, A) B
                             -> (B, A)
                             -> Property
prop_Tuple_Semicomonad_assoc (Fn h) (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_assoc h g f

prop_Tuple_Semicomonad_extend :: Fun (B, B) C
                              -> Fun (B, A) B
                              -> (B, A)
                              -> Property
prop_Tuple_Semicomonad_extend (Fn g) (Fn f) = fcmp $ law_Semicomonad_extend g f

prop_Tuple_Semicomonad_duplicate :: (B, A) -> Property
prop_Tuple_Semicomonad_duplicate = fcmp $ law_Semicomonad_duplicate

prop_Tuple_Comonad_leftId :: (B, A) -> Property
prop_Tuple_Comonad_leftId = fcmp $ law_Comonad_leftId

prop_Tuple_Comonad_rightId :: Fun (B, A) B -> (B, A) -> Property
prop_Tuple_Comonad_rightId (Fn f) = fcmp $ law_Comonad_rightId f



prop_Either_Semicomonad_compose :: Fun (Either B B) C
                                -> Fun (Either B A) B
                                -> Either B A
                                -> Property
prop_Either_Semicomonad_compose (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_compose g f

prop_Either_Semicomonad_assoc :: Fun (Either B C) A
                              -> Fun (Either B B) C
                              -> Fun (Either B A) B
                              -> Either B A
                              -> Property
prop_Either_Semicomonad_assoc (Fn h) (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_assoc h g f

prop_Either_Semicomonad_extend :: Fun (Either B B) C
                               -> Fun (Either B A) B
                               -> Either B A
                               -> Property
prop_Either_Semicomonad_extend (Fn g) (Fn f) = fcmp $ law_Semicomonad_extend g f

prop_Either_Semicomonad_duplicate :: Either B A -> Property
prop_Either_Semicomonad_duplicate = fcmp $ law_Semicomonad_duplicate



prop_List_Semicomonad_compose :: Fun ([B]) C
                              -> Fun ([A]) B
                              -> [A]
                              -> Property
prop_List_Semicomonad_compose (Fn g) (Fn f) = fcmp $ law_Semicomonad_compose g f

prop_List_Semicomonad_assoc :: Fun ([C]) A
                            -> Fun ([B]) C
                            -> Fun ([A]) B
                            -> [A]
                            -> Property
prop_List_Semicomonad_assoc (Fn h) (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_assoc h g f

prop_List_Semicomonad_extend :: Fun ([B]) C -> Fun ([A]) B -> [A] -> Property
prop_List_Semicomonad_extend (Fn g) (Fn f) = fcmp $ law_Semicomonad_extend g f

prop_List_Semicomonad_duplicate :: [A] -> Property
prop_List_Semicomonad_duplicate = fcmp $ law_Semicomonad_duplicate



prop_NonEmpty_Semicomonad_compose :: Fun (NE.NonEmpty B) C
                                  -> Fun (NE.NonEmpty A) B
                                  -> NE.NonEmpty A
                                  -> Property
prop_NonEmpty_Semicomonad_compose (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_compose g f

prop_NonEmpty_Semicomonad_assoc :: Fun (NE.NonEmpty C) A
                                -> Fun (NE.NonEmpty B) C
                                -> Fun (NE.NonEmpty A) B
                                -> NE.NonEmpty A
                                -> Property
prop_NonEmpty_Semicomonad_assoc (Fn h) (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_assoc h g f

prop_NonEmpty_Semicomonad_extend :: Fun (NE.NonEmpty B) C
                                 -> Fun (NE.NonEmpty A) B
                                 -> NE.NonEmpty A
                                 -> Property
prop_NonEmpty_Semicomonad_extend (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_extend g f

prop_NonEmpty_Semicomonad_duplicate :: NE.NonEmpty A -> Property
prop_NonEmpty_Semicomonad_duplicate = fcmp $ law_Semicomonad_duplicate

prop_NonEmpty_Comonad_leftId :: NE.NonEmpty A -> Property
prop_NonEmpty_Comonad_leftId = fcmp $ law_Comonad_leftId

prop_NonEmpty_Comonad_rightId :: Fun (NE.NonEmpty A) B
                              -> NE.NonEmpty A
                              -> Property
prop_NonEmpty_Comonad_rightId (Fn f) = fcmp $ law_Comonad_rightId f

prop_Cokleisli_NonEmpty_Semigroupoid_assoc
  :: Fun (NE.NonEmpty C) A
  -> Fun (NE.NonEmpty B) C
  -> Fun (NE.NonEmpty A) B
  -> NE.NonEmpty A
  -> Property
prop_Cokleisli_NonEmpty_Semigroupoid_assoc (Fn h) (Fn g) (Fn f) =
  fcmp $ hask $ law_Semigroupoid_assoc @(Cokleisli NE.NonEmpty) h' g' f'
  where f' = Cokleisli f
        g' = Cokleisli g
        h' = Cokleisli h
        hask (Cokleisli p, Cokleisli q) = (p, q)

prop_Cokleisli_NonEmpty_Category_leftId ::
  Fun (NE.NonEmpty A) B -> NE.NonEmpty A -> Property
prop_Cokleisli_NonEmpty_Category_leftId (Fn f) =
  fcmp $ hask $ law_Category_leftId @(Cokleisli NE.NonEmpty) f'
  where f' = Cokleisli f
        hask (Cokleisli p, Cokleisli q) = (p, q)

prop_Cokleisli_NonEmpty_Category_rightId ::
  Fun (NE.NonEmpty A) B -> NE.NonEmpty A -> Property
prop_Cokleisli_NonEmpty_Category_rightId (Fn f) =
  fcmp $ hask $ law_Category_rightId @(Cokleisli NE.NonEmpty) f'
  where f' = Cokleisli f
        hask (Cokleisli p, Cokleisli q) = (p, q)



type FSum a = F.Sum ((,) B) Identity a

prop_Sum_Semicomonad_compose :: Fun (FSum B) C
                             -> Fun (FSum A) B
                             -> FSum A
                             -> Property
prop_Sum_Semicomonad_compose (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_compose g f

prop_Sum_Semicomonad_assoc :: Fun (FSum C) A
                           -> Fun (FSum B) C
                           -> Fun (FSum A) B
                           -> FSum A
                           -> Property
prop_Sum_Semicomonad_assoc (Fn h) (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_assoc h g f

prop_Sum_Semicomonad_extend :: Fun (FSum B) C
                            -> Fun (FSum A) B
                            -> FSum A
                            -> Property
prop_Sum_Semicomonad_extend (Fn g) (Fn f) = fcmp $ law_Semicomonad_extend g f

prop_Sum_Semicomonad_duplicate :: FSum A -> Property
prop_Sum_Semicomonad_duplicate = fcmp $ law_Semicomonad_duplicate

prop_Sum_Comonad_leftId :: FSum A -> Property
prop_Sum_Comonad_leftId = fcmp $ law_Comonad_leftId

prop_Sum_Comonad_rightId :: Fun (FSum A) B -> FSum A -> Property
prop_Sum_Comonad_rightId (Fn f) = fcmp $ law_Comonad_rightId f
