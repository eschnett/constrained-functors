{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Control.Constrained.Functor
  ( FunctorKind
  , Functor(..)
  , law_Functor_id
  , law_Functor_compose
  , Inclusion(..)
  , law_Inclusion_faithful
  ) where

import qualified Prelude as P
import Control.Constrained.Prelude

import Control.Applicative (ZipList(..))
import Control.Constrained.Category
import Data.Constraint
import Data.Functor.Identity
import qualified Data.Functor.Compose as F
import qualified Data.Functor.Product as F
import qualified Data.Functor.Sum as F
import Data.Kind
import Data.List.NonEmpty (NonEmpty(..))
import Data.Proxy
import qualified Data.Vector as V



-- | The kind of a functor
type FunctorKind = Type -> Type



-- | A functor
class (Category (Dom f), Category (Cod f)) => Functor (f :: FunctorKind) where
  -- | Prove that this functor maps from its domain to its codomain
  proveFunctor :: Ok (Dom f) a :- Ok (Cod f) (f a)
  -- | Domain
  type Dom f :: CatKind
  -- | Codomain
  type Cod f :: CatKind
  -- | Map a morphism
  fmap :: Ok (Dom f) a => Ok (Dom f) b => Dom f a b -> Cod f (f a) (f b)



law_Functor_id :: forall f a k l.
                  Functor f => k ~ Dom f => l ~ Cod f => Ok k a
               => (l (f a) (f a), l (f a) (f a))
law_Functor_id = (fmap (id @k), id @l)
                 \\ proveFunctor @f @a

law_Functor_compose :: forall f a b c k l.
                       Functor f => k ~ Dom f => l ~ Cod f
                    => Ok k a => Ok k b => Ok k c
                    => k b c -> k a b -> (l (f a) (f c), l (f a) (f c))
law_Functor_compose g f = (fmap (g . f), fmap g . fmap f)
                          \\ proveFunctor @f @a
                          \\ proveFunctor @f @b
                          \\ proveFunctor @f @c



--------------------------------------------------------------------------------



-- | An inclusion functor of a subcategory
-- 'f' needs to be injective; how do we test that?
class (Functor f, SubCatOf (Dom f) (Cod f)) => Inclusion f where
  inclusion :: Ok (Dom f) a => a -> f a
  runInclusion :: Ok (Dom f) a => f a -> a

law_Inclusion_faithful :: forall f a k.
                          Inclusion f => k ~ Dom f => Ok k a
                       => a -> (a, a)
law_Inclusion_faithful x = (x, runInclusion @f (inclusion x))



--------------------------------------------------------------------------------



instance Functor Proxy where
  proveFunctor = Sub Dict
  type Dom Proxy = (->)
  type Cod Proxy = (->)
  fmap _ = \_ -> Proxy

instance Functor Identity where
  proveFunctor = Sub Dict
  type Dom Identity = (->)
  type Cod Identity = (->)
  fmap f = \(Identity x) -> Identity (f x)

instance Functor ((,) a) where
  proveFunctor = Sub Dict
  type Dom ((,) a) = (->)
  type Cod ((,) a) = (->)
  fmap f = \(a, x) -> (a, f x)

instance Functor (Either a) where
  proveFunctor = Sub Dict
  type Dom (Either a) = (->)
  type Cod (Either a) = (->)
  fmap f = \case Left a -> Left a
                 Right x -> Right (f x)

instance Functor [] where
  proveFunctor = Sub Dict
  type Dom [] = (->)
  type Cod [] = (->)
  fmap f = \case [] -> []
                 x : xs -> f x : fmap f xs

instance Functor ZipList where
  proveFunctor = Sub Dict
  type Dom ZipList = (->)
  type Cod ZipList = (->)
  fmap f = ZipList . fmap f . getZipList

instance Functor NonEmpty where
  proveFunctor = Sub Dict
  type Dom NonEmpty = (->)
  type Cod NonEmpty = (->)
  fmap f = \(x :| xs) -> f x :| fmap f xs

instance Functor ((->) a) where
  proveFunctor = Sub Dict
  type Dom ((->) a) = (->)
  type Cod ((->) a) = (->)
  fmap f = \g -> f . g

instance ( Functor f, Functor g, Dom f ~ Dom g, Cod f ~ Cod g
         , Dom f ~ (->), Cod f ~ (->)) =>
         Functor (F.Product f g) where
  proveFunctor = Sub Dict
  type Dom (F.Product f g) = Dom f
  type Cod (F.Product f g) = (->)
  fmap f = \(F.Pair xs ys) -> F.Pair (fmap f xs) (fmap f ys)

instance ( Functor f, Functor g, Dom f ~ Dom g, Cod f ~ Cod g
         , Dom f ~ (->), Cod f ~ (->)) =>
         Functor (F.Sum f g) where
  proveFunctor = Sub Dict
  type Dom (F.Sum f g) = Dom f
  type Cod (F.Sum f g) = (->)
  fmap f = \case (F.InL xs) -> F.InL (fmap f xs)
                 (F.InR ys) -> F.InR (fmap f ys)

instance ( Functor f, Functor g, Dom f ~ Cod g
         , Dom g ~ (->), Cod f ~ (->), Cod g ~ (->)) =>
         Functor (F.Compose f g) where
  proveFunctor = Sub Dict
  type Dom (F.Compose f g) = Dom g
  type Cod (F.Compose f g) = (->)
  fmap f = \(F.Compose xss) -> F.Compose (fmap (fmap f) xss)

instance Functor V.Vector where
  proveFunctor = Sub Dict
  type Dom V.Vector = (->)
  type Cod V.Vector = (->)
  fmap f = P.fmap f



instance Inclusion Identity where
  inclusion = Identity
  runInclusion = runIdentity
