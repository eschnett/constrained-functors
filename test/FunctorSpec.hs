{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module FunctorSpec where

import Prelude()
import Control.Constrained.Prelude

import Control.Constrained.Functor
import Data.Functor.Identity
import qualified Data.Functor.Compose as F
import qualified Data.Functor.Product as F
import qualified Data.Functor.Sum as F
import qualified Data.List.NonEmpty as NE
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



prop_Proxy_Functor_id :: Proxy A -> Property
prop_Proxy_Functor_id = fcmp $ law_Functor_id

prop_Proxy_Functor_compose :: Fun B C -> Fun A B -> Proxy A -> Property
prop_Proxy_Functor_compose (Fn g) (Fn f) = fcmp $ law_Functor_compose g f



prop_Identity_Functor_id :: Identity A -> Property
prop_Identity_Functor_id = fcmp $ law_Functor_id

prop_Identity_Functor_compose :: Fun B C -> Fun A B -> Identity A -> Property
prop_Identity_Functor_compose (Fn g) (Fn f) = fcmp $ law_Functor_compose g f



prop_Tuple_Functor_id :: (B, A) -> Property
prop_Tuple_Functor_id = fcmp $ law_Functor_id

prop_Tuple_Functor_compose :: Fun B C -> Fun A B -> (B, A) -> Property
prop_Tuple_Functor_compose (Fn g) (Fn f) = fcmp $ law_Functor_compose g f



prop_Either_Functor_id :: Either B A -> Property
prop_Either_Functor_id = fcmp $ law_Functor_id

prop_Either_Functor_compose :: Fun B C -> Fun A B -> Either B A -> Property
prop_Either_Functor_compose (Fn g) (Fn f) = fcmp $ law_Functor_compose g f



prop_List_Functor_id :: [A] -> Property
prop_List_Functor_id = fcmp $ law_Functor_id

prop_List_Functor_compose :: Fun B C -> Fun A B -> [A] -> Property
prop_List_Functor_compose (Fn g) (Fn f) = fcmp $ law_Functor_compose g f



prop_NonEmpty_Functor_id :: NE.NonEmpty A -> Property
prop_NonEmpty_Functor_id = fcmp $ law_Functor_id

prop_NonEmpty_Functor_compose :: Fun B C -> Fun A B -> NE.NonEmpty A -> Property
prop_NonEmpty_Functor_compose (Fn g) (Fn f) = fcmp $ law_Functor_compose g f



prop_Function_Functor_id :: Fun B A -> B -> Property
prop_Function_Functor_id (Fn x) = (ffcmp $ law_Functor_id) x

prop_Function_Functor_compose :: Fun B C -> Fun A B -> Fun B A -> B -> Property
prop_Function_Functor_compose (Fn g) (Fn f) (Fn x) =
  (ffcmp $ law_Functor_compose g f) x



type FProd a = F.Product ((,) B) (Either C) a

prop_Product_Functor_id :: FProd A -> Property
prop_Product_Functor_id = fcmp $ law_Functor_id

prop_Product_Functor_compose :: Fun B C -> Fun A B -> FProd A -> Property
prop_Product_Functor_compose (Fn g) (Fn f) = fcmp $ law_Functor_compose g f



type FSum a = F.Sum ((,) B) Identity a

prop_Sum_Functor_id :: FSum A -> Property
prop_Sum_Functor_id = fcmp $ law_Functor_id

prop_Sum_Functor_compose :: Fun B C -> Fun A B -> FSum A -> Property
prop_Sum_Functor_compose (Fn g) (Fn f) = fcmp $ law_Functor_compose g f



type FComp a = F.Compose ((,) B) (Either C) a

prop_Compose_Functor_id :: FComp A -> Property
prop_Compose_Functor_id = fcmp $ law_Functor_id

prop_Compose_Functor_compose :: Fun B C -> Fun A B -> FComp A -> Property
prop_Compose_Functor_compose (Fn g) (Fn f) = fcmp $ law_Functor_compose g f
