{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module FunctorSpec where

import qualified Prelude as P
import Control.Constrained.Prelude

import Control.Constrained.Category
import Control.Constrained.Functor
import Data.Functor.Identity
import qualified Data.Functor.Compose as F
import qualified Data.Functor.Product as F
import qualified Data.Functor.Sum as F
import qualified Data.List.NonEmpty as NE
-- import Data.Monoid
import Data.Proxy
-- import Data.Semigroup
import Test.QuickCheck
import Test.QuickCheck.Poly



cmp :: Eq a => Show a => (a, a) -> Property
cmp (x, y) = x === y

fcmp :: Eq b => Show b => (a -> b, a -> b) -> a -> Property
fcmp (f, g) x = f x === g x

ffcmp :: Eq c => Show c => (a -> b -> c, a -> b -> c) -> a -> b -> Property
ffcmp (f, g) x y = f x y === g x y



instance Semigroup A where A x <> A y = A (x + y)
instance Monoid A where mempty = A 0

instance Semigroup B where B x <> B y = B (x + y)
instance Monoid B where mempty = B 0

instance Semigroup C where C x <> C y = C (x + y)
instance Monoid C where mempty = C 0



instance Arbitrary (Proxy a) where
  arbitrary = (\() -> Proxy) <$> arbitrary
instance CoArbitrary (Proxy a)
instance Function (Proxy a)

instance Arbitrary a => Arbitrary (NE.NonEmpty a) where
  arbitrary = NE.fromList . getNonEmpty <$> arbitrary
  shrink = map (NE.fromList . getNonEmpty) . shrink . NonEmpty . NE.toList
instance CoArbitrary a =>CoArbitrary (NE.NonEmpty a)
instance Function a => Function (NE.NonEmpty a)



fs2e :: F.Sum f g a -> Either (f a) (g a)
fs2e (F.InL xs) = Left xs
fs2e (F.InR ys) = Right ys

e2fs :: Either (f a) (g a) -> F.Sum f g a
e2fs (Left xs) = F.InL xs
e2fs (Right xs) = F.InR xs

instance (Arbitrary (f a), Arbitrary (g a)) => Arbitrary (F.Sum f g a) where
  arbitrary = e2fs <$> arbitrary
  shrink x = e2fs <$> shrink (fs2e x)
instance (CoArbitrary (f a), CoArbitrary (g a)) => CoArbitrary (F.Sum f g a)
instance (Function (f a), Function (g a)) => Function (F.Sum f g a)



prop_Proxy_Functor_id :: Proxy A -> Property
prop_Proxy_Functor_id = fcmp $ law_Functor_id

prop_Proxy_Functor_compose :: Fun B C -> Fun A B -> Proxy A -> Property
prop_Proxy_Functor_compose (Fn g) (Fn f) = fcmp $ law_Functor_compose g f

prop_Proxy_Apply_assoc :: ((Proxy A, Proxy B), Proxy C) -> Property
prop_Proxy_Apply_assoc = fcmp $ law_Apply_assoc

prop_Proxy_Applicative_leftUnit :: ((), Proxy A) -> Property
prop_Proxy_Applicative_leftUnit = fcmp $ law_Applicative_leftUnit

prop_Proxy_Applicative_rightUnit :: (Proxy A, ()) -> Property
prop_Proxy_Applicative_rightUnit = fcmp $ law_Applicative_rightUnit

prop_Proxy_Semicomonad_assoc :: Fun (Proxy C) A
                             -> Fun (Proxy B) C
                             -> Fun (Proxy A) B
                             -> Proxy A
                             -> Property
prop_Proxy_Semicomonad_assoc (Fn h) (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_assoc h g f

prop_Proxy_Semicomonad_extend :: Fun (Proxy A) B -> Proxy A -> Property
prop_Proxy_Semicomonad_extend (Fn f) = fcmp $ law_Semicomonad_extend f

prop_Proxy_Semicomonad_duplicate :: Proxy A -> Property
prop_Proxy_Semicomonad_duplicate = fcmp $ law_Semicomonad_duplicate



prop_Identity_Functor_id :: Identity A -> Property
prop_Identity_Functor_id = fcmp $ law_Functor_id

prop_Identity_Functor_compose :: Fun B C -> Fun A B -> Identity A -> Property
prop_Identity_Functor_compose (Fn g) (Fn f) = fcmp $ law_Functor_compose g f

prop_Identity_Apply_assoc :: ((Identity A, Identity B), Identity C) -> Property
prop_Identity_Apply_assoc = fcmp $ law_Apply_assoc

prop_Identity_Applicative_leftUnit :: ((), Identity A) -> Property
prop_Identity_Applicative_leftUnit = fcmp $ law_Applicative_leftUnit

prop_Identity_Applicative_rightUnit :: (Identity A, ()) -> Property
prop_Identity_Applicative_rightUnit = fcmp $ law_Applicative_rightUnit

prop_Identity_Semicomonad_assoc :: Fun (Identity C) A
                                -> Fun (Identity B) C
                                -> Fun (Identity A) B
                                -> Identity A
                                -> Property
prop_Identity_Semicomonad_assoc (Fn h) (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_assoc h g f

prop_Identity_Semicomonad_extend :: Fun (Identity A) B -> Identity A -> Property
prop_Identity_Semicomonad_extend (Fn f) = fcmp $ law_Semicomonad_extend f

prop_Identity_Semicomonad_duplicate :: Identity A -> Property
prop_Identity_Semicomonad_duplicate = fcmp $ law_Semicomonad_duplicate

prop_Identity_Comonad_leftId :: Fun (Identity A) B -> Identity A -> Property
prop_Identity_Comonad_leftId (Fn f) = fcmp $ law_Comonad_leftId f

prop_Identity_Comonad_rightId :: Fun (Identity A) B -> Identity A -> Property
prop_Identity_Comonad_rightId (Fn f) = fcmp $ law_Comonad_rightId f



prop_Tuple_Functor_id :: (B, A) -> Property
prop_Tuple_Functor_id = fcmp $ law_Functor_id

prop_Tuple_Functor_compose :: Fun B C -> Fun A B -> (B, A) -> Property
prop_Tuple_Functor_compose (Fn g) (Fn f) = fcmp $ law_Functor_compose g f

prop_Tuple_Apply_assoc :: (((B, A), (B, B)), (B, C)) -> Property
prop_Tuple_Apply_assoc = fcmp $ law_Apply_assoc

prop_Tuple_Applicative_leftUnit :: ((), (B, A)) -> Property
prop_Tuple_Applicative_leftUnit = fcmp $ law_Applicative_leftUnit

prop_Tuple_Applicative_rightUnit :: ((B, A), ()) -> Property
prop_Tuple_Applicative_rightUnit = fcmp $ law_Applicative_rightUnit

prop_Tuple_Semicomonad_assoc :: Fun (B, C) A
                             -> Fun (B, B) C
                             -> Fun (B, A) B
                             -> (B, A)
                             -> Property
prop_Tuple_Semicomonad_assoc (Fn h) (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_assoc h g f

prop_Tuple_Semicomonad_extend :: Fun (B, A) B -> (B, A) -> Property
prop_Tuple_Semicomonad_extend (Fn f) = fcmp $ law_Semicomonad_extend f

prop_Tuple_Semicomonad_duplicate :: (B, A) -> Property
prop_Tuple_Semicomonad_duplicate = fcmp $ law_Semicomonad_duplicate

prop_Tuple_Comonad_leftId :: Fun (B, A) B -> (B, A) -> Property
prop_Tuple_Comonad_leftId (Fn f) = fcmp $ law_Comonad_leftId f

prop_Tuple_Comonad_rightId :: Fun (B, A) B -> (B, A) -> Property
prop_Tuple_Comonad_rightId (Fn f) = fcmp $ law_Comonad_rightId f



prop_Either_Functor_id :: Either B A -> Property
prop_Either_Functor_id = fcmp $ law_Functor_id

prop_Either_Functor_compose :: Fun B C -> Fun A B -> Either B A -> Property
prop_Either_Functor_compose (Fn g) (Fn f) = fcmp $ law_Functor_compose g f

prop_Either_Apply_assoc :: ((Either B A, Either B B), Either B C) -> Property
prop_Either_Apply_assoc = fcmp $ law_Apply_assoc

prop_Either_Applicative_leftUnit :: ((), Either B A) -> Property
prop_Either_Applicative_leftUnit = fcmp $ law_Applicative_leftUnit

prop_Either_Applicative_rightUnit :: (Either B A, ()) -> Property
prop_Either_Applicative_rightUnit = fcmp $ law_Applicative_rightUnit

prop_Either_Semicomonad_assoc :: Fun (Either B C) A
                              -> Fun (Either B B) C
                              -> Fun (Either B A) B
                              -> Either B A
                              -> Property
prop_Either_Semicomonad_assoc (Fn h) (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_assoc h g f

prop_Either_Semicomonad_extend :: Fun (Either B A) B -> Either B A -> Property
prop_Either_Semicomonad_extend (Fn f) = fcmp $ law_Semicomonad_extend f

prop_Either_Semicomonad_duplicate :: Either B A -> Property
prop_Either_Semicomonad_duplicate = fcmp $ law_Semicomonad_duplicate



prop_List_Functor_id :: [A] -> Property
prop_List_Functor_id = fcmp $ law_Functor_id

prop_List_Functor_compose :: Fun B C -> Fun A B -> [A] -> Property
prop_List_Functor_compose (Fn g) (Fn f) = fcmp $ law_Functor_compose g f

prop_List_Apply_assoc :: (([A], [B]), [C]) -> Property
prop_List_Apply_assoc = fcmp $ law_Apply_assoc

prop_List_Applicative_leftUnit :: ((), [A]) -> Property
prop_List_Applicative_leftUnit = fcmp $ law_Applicative_leftUnit

prop_List_Applicative_rightUnit :: ([A], ()) -> Property
prop_List_Applicative_rightUnit = fcmp $ law_Applicative_rightUnit

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

prop_List_Semicomonad_assoc :: Fun ([C]) A
                            -> Fun ([B]) C
                            -> Fun ([A]) B
                            -> [A]
                            -> Property
prop_List_Semicomonad_assoc (Fn h) (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_assoc h g f

prop_List_Semicomonad_extend :: Fun ([A]) B -> [A] -> Property
prop_List_Semicomonad_extend (Fn f) = fcmp $ law_Semicomonad_extend f

prop_List_Semicomonad_duplicate :: [A] -> Property
prop_List_Semicomonad_duplicate = fcmp $ law_Semicomonad_duplicate



prop_NonEmpty_Functor_id :: NE.NonEmpty A -> Property
prop_NonEmpty_Functor_id = fcmp $ law_Functor_id

prop_NonEmpty_Functor_compose :: Fun B C -> Fun A B -> NE.NonEmpty A -> Property
prop_NonEmpty_Functor_compose (Fn g) (Fn f) = fcmp $ law_Functor_compose g f

prop_NonEmpty_Semicomonad_assoc :: Fun (NE.NonEmpty C) A
                                -> Fun (NE.NonEmpty B) C
                                -> Fun (NE.NonEmpty A) B
                                -> NE.NonEmpty A
                                -> Property
prop_NonEmpty_Semicomonad_assoc (Fn h) (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_assoc h g f

prop_NonEmpty_Semicomonad_extend ::
  Fun (NE.NonEmpty A) B -> NE.NonEmpty A -> Property
prop_NonEmpty_Semicomonad_extend (Fn f) = fcmp $ law_Semicomonad_extend f

prop_NonEmpty_Semicomonad_duplicate :: NE.NonEmpty A -> Property
prop_NonEmpty_Semicomonad_duplicate = fcmp $ law_Semicomonad_duplicate

prop_NonEmpty_Comonad_leftId ::
  Fun (NE.NonEmpty A) B -> NE.NonEmpty A -> Property
prop_NonEmpty_Comonad_leftId (Fn f) = fcmp $ law_Comonad_leftId f

prop_NonEmpty_Comonad_rightId ::
  Fun (NE.NonEmpty A) B -> NE.NonEmpty A -> Property
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



prop_Function_Functor_id :: Fun B A -> B -> Property
prop_Function_Functor_id (Fn x) = (ffcmp $ law_Functor_id) x

prop_Function_Functor_compose :: Fun B C -> Fun A B -> Fun B A -> B -> Property
prop_Function_Functor_compose (Fn g) (Fn f) (Fn x) =
  (ffcmp $ law_Functor_compose g f) x

prop_Function_Apply_assoc :: ((Fun B A, Fun B B), Fun B C) -> B -> Property
prop_Function_Apply_assoc xs = ffcmp law_Apply_assoc xs'
  where xs' = let ((Fn f, Fn g), Fn h) = xs in ((f, g), h)

prop_Function_Applicative_leftUnit :: ((), Fun B A) -> B -> Property
prop_Function_Applicative_leftUnit xs = ffcmp law_Applicative_leftUnit xs'
  where xs' = let ((), Fn f) = xs in ((), f)

prop_Function_Applicative_rightUnit :: (Fun B A, ()) -> B -> Property
prop_Function_Applicative_rightUnit xs = ffcmp law_Applicative_rightUnit xs'
  where xs' = let (Fn f, ()) = xs in (f, ())



type FProd a = F.Product ((,) B) (Either C) a

prop_Product_Functor_id :: FProd A -> Property
prop_Product_Functor_id = fcmp $ law_Functor_id

prop_Product_Functor_compose :: Fun B C -> Fun A B -> FProd A -> Property
prop_Product_Functor_compose (Fn g) (Fn f) = fcmp $ law_Functor_compose g f

prop_Product_Apply_assoc :: ((FProd A, FProd B), FProd C) -> Property
prop_Product_Apply_assoc = fcmp $ law_Apply_assoc

prop_Product_Applicative_leftUnit :: ((), FProd A) -> Property
prop_Product_Applicative_leftUnit = fcmp $ law_Applicative_leftUnit

prop_Product_Applicative_rightUnit :: (FProd A, ()) -> Property
prop_Product_Applicative_rightUnit = fcmp $ law_Applicative_rightUnit



type FSum a = F.Sum ((,) B) Identity a

prop_Sum_Functor_id :: FSum A -> Property
prop_Sum_Functor_id = fcmp $ law_Functor_id

prop_Sum_Functor_compose :: Fun B C -> Fun A B -> FSum A -> Property
prop_Sum_Functor_compose (Fn g) (Fn f) = fcmp $ law_Functor_compose g f

prop_Sum_Semicomonad_assoc :: Fun (FSum C) A
                           -> Fun (FSum B) C
                           -> Fun (FSum A) B
                           -> FSum A
                           -> Property
prop_Sum_Semicomonad_assoc (Fn h) (Fn g) (Fn f) =
  fcmp $ law_Semicomonad_assoc h g f

prop_Sum_Semicomonad_extend :: Fun (FSum A) B -> FSum A -> Property
prop_Sum_Semicomonad_extend (Fn f) = fcmp $ law_Semicomonad_extend f

prop_Sum_Semicomonad_duplicate :: FSum A -> Property
prop_Sum_Semicomonad_duplicate = fcmp $ law_Semicomonad_duplicate

prop_Sum_Comonad_leftId :: Fun (FSum A) B -> FSum A -> Property
prop_Sum_Comonad_leftId (Fn f) = fcmp $ law_Comonad_leftId f

prop_Sum_Comonad_rightId :: Fun (FSum A) B -> FSum A -> Property
prop_Sum_Comonad_rightId (Fn f) = fcmp $ law_Comonad_rightId f



type FComp a = F.Compose ((,) B) (Either C) a

prop_Compose_Functor_id :: FComp A -> Property
prop_Compose_Functor_id = fcmp $ law_Functor_id

prop_Compose_Functor_compose :: Fun B C -> Fun A B -> FComp A -> Property
prop_Compose_Functor_compose (Fn g) (Fn f) = fcmp $ law_Functor_compose g f

prop_Compose_Apply_assoc :: ((FComp A, FComp B), FComp C) -> Property
prop_Compose_Apply_assoc = fcmp $ law_Apply_assoc

prop_Compose_Applicative_leftUnit :: ((), FComp A) -> Property
prop_Compose_Applicative_leftUnit = fcmp $ law_Applicative_leftUnit

prop_Compose_Applicative_rightUnit :: (FComp A, ()) -> Property
prop_Compose_Applicative_rightUnit = fcmp $ law_Applicative_rightUnit
