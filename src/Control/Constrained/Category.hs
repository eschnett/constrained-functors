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
  , law_SubCatOf_embedId
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

-- | A subcategory
-- A subcategories is a functors, but there is no data type associated with it.
class (Category k, Category l) => SubCatOf k l where
  proveSubCatOf :: Ok k a :- Ok l a
  embed :: Ok k a => Ok k b => k a b -> l a b

-- | A subcategory of Hask, where functions can be evaluated
class SubCatOf k (->) => HaskSubCat k
instance SubCatOf k (->) => HaskSubCat k

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

law_SubCatOf_embedId :: forall k l a. SubCatOf k l => Ok k a
                       => (l a a, l a a)
law_SubCatOf_embedId = (id @l, embed (id @k))
                       \\ proveSubCatOf @k @l @a

-- TODO: also prove functor composition...



--------------------------------------------------------------------------------



class True1 a
instance True1 a

-- | Hask
instance Semigroupoid (->) where
  type Ok (->) = True1
  (.) = (P..)

instance Category (->) where
  id = P.id

instance SubCatOf (->) (->) where
  proveSubCatOf = Sub Dict
  embed = P.id
