{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module ApplicativeSpec where

import Prelude ()
import Control.Constrained.Prelude

import Control.Constrained.Applicative
import Data.Functor.Identity
import qualified Data.Functor.Compose as F
import qualified Data.Functor.Product as F
import Data.Proxy
import Test.QuickCheck
import Test.QuickCheck.Instances2()
import Test.QuickCheck.Poly



cmp :: Eq a => Show a => (a, a) -> Property
cmp (x, y) = x === y

fcmp :: Eq b => Show b => (a -> b, a -> b) -> a -> Property
fcmp (f, g) x = f x === g x

ffcmp :: Eq c => Show c => (a -> b -> c, a -> b -> c) -> a -> b -> Property
ffcmp (f, g) x y = f x y === g x y



prop_Proxy_Apply_assoc :: ((Proxy A, Proxy B), Proxy C) -> Property
prop_Proxy_Apply_assoc = fcmp $ law_Apply_assoc

prop_Proxy_Applicative_leftUnit :: ((), Proxy A) -> Property
prop_Proxy_Applicative_leftUnit = fcmp $ law_Applicative_leftUnit

prop_Proxy_Applicative_rightUnit :: (Proxy A, ()) -> Property
prop_Proxy_Applicative_rightUnit = fcmp $ law_Applicative_rightUnit



prop_Identity_Apply_assoc :: ((Identity A, Identity B), Identity C) -> Property
prop_Identity_Apply_assoc = fcmp $ law_Apply_assoc

prop_Identity_Applicative_leftUnit :: ((), Identity A) -> Property
prop_Identity_Applicative_leftUnit = fcmp $ law_Applicative_leftUnit

prop_Identity_Applicative_rightUnit :: (Identity A, ()) -> Property
prop_Identity_Applicative_rightUnit = fcmp $ law_Applicative_rightUnit



prop_Tuple_Apply_assoc :: (((B, A), (B, B)), (B, C)) -> Property
prop_Tuple_Apply_assoc = fcmp $ law_Apply_assoc

prop_Tuple_Applicative_leftUnit :: ((), (B, A)) -> Property
prop_Tuple_Applicative_leftUnit = fcmp $ law_Applicative_leftUnit

prop_Tuple_Applicative_rightUnit :: ((B, A), ()) -> Property
prop_Tuple_Applicative_rightUnit = fcmp $ law_Applicative_rightUnit



prop_Either_Apply_assoc :: ((Either B A, Either B B), Either B C) -> Property
prop_Either_Apply_assoc = fcmp $ law_Apply_assoc

prop_Either_Applicative_leftUnit :: ((), Either B A) -> Property
prop_Either_Applicative_leftUnit = fcmp $ law_Applicative_leftUnit

prop_Either_Applicative_rightUnit :: (Either B A, ()) -> Property
prop_Either_Applicative_rightUnit = fcmp $ law_Applicative_rightUnit



prop_List_Apply_assoc :: (([A], [B]), [C]) -> Property
prop_List_Apply_assoc = fcmp $ law_Apply_assoc

prop_List_Applicative_leftUnit :: ((), [A]) -> Property
prop_List_Applicative_leftUnit = fcmp $ law_Applicative_leftUnit

prop_List_Applicative_rightUnit :: ([A], ()) -> Property
prop_List_Applicative_rightUnit = fcmp $ law_Applicative_rightUnit



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

prop_Product_Apply_assoc :: ((FProd A, FProd B), FProd C) -> Property
prop_Product_Apply_assoc = fcmp $ law_Apply_assoc

prop_Product_Applicative_leftUnit :: ((), FProd A) -> Property
prop_Product_Applicative_leftUnit = fcmp $ law_Applicative_leftUnit

prop_Product_Applicative_rightUnit :: (FProd A, ()) -> Property
prop_Product_Applicative_rightUnit = fcmp $ law_Applicative_rightUnit



type FComp a = F.Compose ((,) B) (Either C) a

prop_Compose_Apply_assoc :: ((FComp A, FComp B), FComp C) -> Property
prop_Compose_Apply_assoc = fcmp $ law_Apply_assoc

prop_Compose_Applicative_leftUnit :: ((), FComp A) -> Property
prop_Compose_Applicative_leftUnit = fcmp $ law_Applicative_leftUnit

prop_Compose_Applicative_rightUnit :: (FComp A, ()) -> Property
prop_Compose_Applicative_rightUnit = fcmp $ law_Applicative_rightUnit
