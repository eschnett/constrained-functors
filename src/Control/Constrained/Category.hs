{-# LANGUAGE UndecidableInstances #-}

module Control.Constrained.Category
  ( -- * Categories
    ObjKind, MorKind, CatKind
  , Semigroupoid(..)
  , law_Semigroupoid_assoc
  , Category(..)
  , law_Category_leftId
  , law_Category_rightId
  , SubCatOf(..)
  , law_SubCatOf_id
  , law_SubCatOf_compose
  , HaskSubCat
  , eval
  ) where

import qualified Prelude as P

import Data.Constraint
import Data.Kind



--------------------------------------------------------------------------------



-- | The kind of an object
type ObjKind = Type -> Constraint
-- | The kind of a morphism
type MorKind = Type -> Type -> Type
-- | The kind of a category
type CatKind = MorKind



-- | A Semigroupoid is a Category without identity morphisms
class Semigroupoid (k :: CatKind) where
  -- | Objects in the category are defined by a constraint
  type Ok k :: ObjKind
  (.) :: Ok k a => Ok k b => Ok k c => k b c -> k a b -> k a c

-- | A Category is defined by its morphisms
-- TODO: Not all categories are subcategories of Hask -- can't have 'eval'!
class Semigroupoid k => Category (k :: CatKind) where
  id :: Ok k a => k a a

-- | A (full) subcategory
-- A subcategory has an inclusion functor, but we don't require that
-- there is a concrete data type associated with it.
class (Semigroupoid k, Semigroupoid l) => SubCatOf k l where
  proveSubCatOf :: Ok k a :- Ok l a
  embed :: Ok k a => Ok k b => k a b -> l a b

-- | Each category is a subcategory of itself
instance Semigroupoid k => SubCatOf k k where
  proveSubCatOf = Sub Dict
  embed = id

-- The subcategory relationship is transitive, but we don't describe
-- this to avoid duplicate instances.

-- | A subcategory of Hask, where functions can be evaluated
class k `SubCatOf` (->) => HaskSubCat k
instance k `SubCatOf` (->) => HaskSubCat k

eval :: forall k a b.
        HaskSubCat k => Ok k a => Ok k b => k a b -> a -> b
eval = embed
       \\ proveSubCatOf @k @(->) @a



law_Semigroupoid_assoc :: Semigroupoid k => Ok k a => Ok k b => Ok k c => Ok k d
                       => k c d -> k b c -> k a b -> (k a d, k a d)
law_Semigroupoid_assoc h g f = ((h . g) . f, h . (g . f))

law_Category_leftId :: Category k => Ok k a => Ok k b
                    => k a b -> (k a b, k a b)
law_Category_leftId f = (id . f, f)

law_Category_rightId :: Category k => Ok k a => Ok k b
                     => k a b -> (k a b, k a b)
law_Category_rightId f = (f . id, f)

law_SubCatOf_id :: forall k l a.
                   (Category k, Category l, SubCatOf k l) => Ok k a
                => (l a a, l a a)
law_SubCatOf_id = (id @l, embed (id @k))
                  \\ proveSubCatOf @k @l @a

law_SubCatOf_compose :: forall k l a b c.
                        SubCatOf k l => Ok k a => Ok k b => Ok k c
                     => k b c -> k a b -> (l a c, l a c)
law_SubCatOf_compose g f = (embed (g . f), embed g . embed f)
                           \\ proveSubCatOf @k @l @a
                           \\ proveSubCatOf @k @l @b
                           \\ proveSubCatOf @k @l @c



--------------------------------------------------------------------------------



class True1 a
instance True1 a

-- | Hask
instance Semigroupoid (->) where
  type Ok (->) = True1
  (.) = (P..)

instance Category (->) where
  id = P.id
