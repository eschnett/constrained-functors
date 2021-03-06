{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Constrained.Plain
  ( PCon
  , type (-#>)(..)
    -- Endofunctors
  , PProxy(..)
  , PIdentity(..)
  , PTuple(..)
  , PProduct(..)
  , PCompose(..)
    -- Exofunctors
  , UIdentity(..)
  , UPair(..)
  , UIVector
  , uivector
  , getUIVector
  , getUIndex
  ) where

import qualified Prelude as P
import Control.Constrained.Prelude

import Control.Constrained.Applicative
import Control.Constrained.Cartesian
import Control.Constrained.Category
import Control.Constrained.Closed
import Control.Constrained.Comonad
import Control.Constrained.Foldable
import Control.Constrained.Functor
import Control.Constrained.Traversable
import Control.Exception (assert)
import Data.Binary
import Data.Constraint
import Data.Coerce
import qualified Data.Vector.Unboxed as U
import Data.Vector.Unboxed.Deriving
import GHC.Generics
import Test.QuickCheck
import Test.QuickCheck.Instances()



-- | Consider also 'Storable' instead of 'Unbox'
class (Binary a, U.Unbox a) => PCon a
instance (Binary a, U.Unbox a) => PCon a

newtype (-#>) a b = PFun { runPFun :: a -> b }



instance Semigroupoid (-#>) where
  type Ok (-#>) = PCon
  PFun g . PFun f = PFun (g . f)

instance Category (-#>) where
  id = PFun id

instance SubCatOf (-#>) (->) where
  proveSubCatOf = Sub Dict
  embed (PFun f) = f

instance Cartesian (-#>) where
  proveCartesian = Sub Dict
  type Product (-#>) = (,)
  type Unit (-#>) = ()
  prod (PFun f) (PFun g) = PFun \(x, y) -> (f x, g y)
  unit = ()
  exl = PFun fst
  exr = PFun snd
  fork (PFun f) (PFun g) = PFun \x -> (f x, g x)
  it = PFun (\_ -> ())
  unitArrow x = PFun (\_ -> x)
  lunit = PFun \x -> ((), x)
  runit = PFun \x -> (x, ())
  assoc = PFun \((x, y), z) -> (x, (y, z))
  reassoc = PFun \(x, (y, z)) -> ((x, y), z)
  swap = PFun \(x, y) -> (y, x)



--------------------------------------------------------------------------------



data PProxy a = PProxy
  deriving (Eq, Ord, Read, Show, Generic)

instance Binary (PProxy a)

derivingUnbox "PProxy"
    [t| forall a. PProxy a -> () |] [| \PProxy -> () |] [| \() -> PProxy |]

instance Arbitrary (PProxy a) where
  arbitrary = (\() -> PProxy) <$> arbitrary
instance CoArbitrary (PProxy a)
instance Function (PProxy a)

newtype PIdentity a = PIdentity a
  deriving (Eq, Ord, Read, Show, Generic)

instance Binary a => Binary (PIdentity a)

derivingUnbox "PIdentity"
    [t| forall a. U.Unbox a => PIdentity a -> a |] [| coerce |] [| coerce |]

instance Arbitrary a => Arbitrary (PIdentity a) where
  arbitrary = PIdentity <$> arbitrary
instance CoArbitrary a => CoArbitrary (PIdentity a)
instance Function a => Function (PIdentity a)

data PTuple a b = PTuple !a !b
  deriving (Eq, Ord, Read, Show, Generic)

instance (Binary a, Binary b) => Binary (PTuple a b)

derivingUnbox "PTuple"
    [t| forall a b. (U.Unbox a, U.Unbox b) => PTuple a b -> (a, b) |]
    [| \(PTuple x y) -> (x, y) |]
    [| \(x, y) -> PTuple x y |]

instance Arbitrary (a, b) => Arbitrary (PTuple a b) where
  arbitrary = uncurry PTuple <$> arbitrary
instance (CoArbitrary a, CoArbitrary b) => CoArbitrary (PTuple a b)
instance (Function a, Function b) => Function (PTuple a b)

data PProduct f g a = PPair !(f a) !(g a)
  deriving (Eq, Ord, Read, Show, Generic)

instance (Binary (f a), Binary (g a)) => Binary (PProduct f g a)

derivingUnbox "PProduct"
    [t| forall f g a. (U.Unbox (f a), U.Unbox (g a))
     => PProduct f g a -> (f a, g a) |]
    [| \(PPair xs xs') -> (xs, xs') |]
    [| \(xs, xs') -> PPair xs xs' |]

instance Arbitrary (f a, g a) => Arbitrary (PProduct f g a) where
  arbitrary = uncurry PPair <$> arbitrary
instance (CoArbitrary (f a), CoArbitrary (g a)) => CoArbitrary (PProduct f g a)
instance (Function (f a), Function (g a)) => Function (PProduct f g a)

newtype PCompose f g a = PCompose (f (g a))
  deriving (Eq, Ord, Read, Show, Generic)

instance Binary (f (g a)) => Binary (PCompose f g a)

derivingUnbox "PCompose"
    [t| forall f g a. U.Unbox (f (g a)) => PCompose f g a -> f (g a) |]
    [| coerce |]
    [| coerce |]

instance Arbitrary (f (g a)) => Arbitrary (PCompose f g a) where
  arbitrary = PCompose <$> arbitrary
instance CoArbitrary (f (g a)) => CoArbitrary (PCompose f g a)
instance Function (f (g a)) => Function (PCompose f g a)



instance Functor PProxy where
  proveFunctor = Sub Dict
  type Dom PProxy = (-#>)
  type Cod PProxy = (-#>)
  fmap _ = PFun \_ -> PProxy

instance Functor PIdentity where
  proveFunctor = Sub Dict
  type Dom PIdentity = (-#>)
  type Cod PIdentity = (-#>)
  fmap (PFun f) = PFun \(PIdentity x) -> PIdentity (f x)

instance PCon a => Functor (PTuple a) where
  proveFunctor = Sub Dict
  type Dom (PTuple a) = (-#>)
  type Cod (PTuple a) = (-#>)
  fmap (PFun f) = PFun \(PTuple a x) -> PTuple a (f x)

instance ( Functor f, Functor g, Dom f ~ Dom g, Cod f ~ Cod g
         , Dom f ~ (-#>), Cod f ~ (-#>)) =>
         Functor (PProduct f g) where
  proveFunctor :: forall a. PCon a :- PCon (PProduct f g a)
  proveFunctor = trans pconpfga (pconfa &&& pconga)
    where
      pconfa = proveFunctor @f @a :: PCon a :- PCon (f a)
      pconga = proveFunctor @g @a :: PCon a :- PCon (g a)
      pconpfga = Sub Dict :: (PCon (f a), PCon (g a)) :- PCon (PProduct f g a)
  type Dom (PProduct f g) = Dom f
  type Cod (PProduct f g) = (-#>)
  fmap f = PFun \(PPair xs xs') ->
                  PPair (runPFun (fmap f) xs) (runPFun (fmap f) xs')

instance ( Functor f, Functor g, Dom f ~ Cod g
         , Dom g ~ (-#>), Cod f ~ (-#>), Cod g ~ (-#>)) =>
         Functor (PCompose f g) where
  proveFunctor :: forall a. PCon a :- PCon (PCompose f g a)
  proveFunctor = trans pconcfga (trans pconfga pconga)
    where
      pconga = proveFunctor @g @a :: PCon a :- PCon (g a)
      pconfga = proveFunctor @f @(g a) :: PCon (g a) :- PCon (f (g a))
      pconcfga = Sub Dict :: PCon (f (g a)) :- PCon (PCompose f g a)
  type Dom (PCompose f g) = Dom g
  type Cod (PCompose f g) = (-#>)
  fmap :: forall a b.
          forall pc. pc ~ PCompose f g
       => Ok (Dom pc) a => Ok (Dom pc) b => Dom pc a b -> Cod pc (pc a) (pc b)
  fmap f = PFun \(PCompose xss) -> PCompose (runPFun (fmap (fmap f)) xss)
    \\ proveFunctor @g @a \\ proveFunctor @g @b



instance Foldable PProxy where
  foldMap _ _ = mempty
  foldru _ z _ = z
  foldlu _ z _ = z
  toList _ = []

instance Foldable PIdentity where
  foldMap (PFun f) (PIdentity x) = f x
  foldru (PFun f) z (PIdentity x) = f (x, z)
  foldlu (PFun f) z (PIdentity x) = f (z, x)
  toList (PIdentity x) = [x]

instance PCon a => Foldable (PTuple a) where
  foldMap (PFun f) (PTuple _ x) = f x
  foldru (PFun f) z (PTuple _ x) = f (x, z)
  foldlu (PFun f) z (PTuple _ x) = f (z, x)
  toList (PTuple _ x) = [x]

instance ( Foldable f, Foldable g, Dom f ~ Dom g, Cod f ~ Cod g
         , Dom f ~ (-#>), Cod f ~ (-#>)) =>
         Foldable (PProduct f g) where
  foldMap f (PPair xs xs') = foldMap f xs <> foldMap f xs'
  foldru f z (PPair xs xs') = foldru f (foldru f z xs') xs
  foldlu f z (PPair xs xs') = foldlu f (foldlu f z xs) xs'
  toList (PPair xs xs') = toList xs ++ toList xs'

instance ( Foldable f, Foldable g, Dom f ~ Cod g
         , Dom g ~ (-#>), Cod f ~ (-#>), Cod g ~ (-#>)) =>
         Foldable (PCompose f g) where
  foldMap :: forall a b pc.
             pc ~ PCompose f g
          => Monoid b => Ok (Dom pc) a => Ok (Dom pc) b
          => Dom pc a b -> pc a -> b
  foldMap f (PCompose xss) = foldMap (PFun (foldMap f)) xss
                             \\ proveFunctor @g @a
  foldru :: forall a b pc k p.
            pc ~ PCompose f g => k ~ Dom pc => Cartesian k => p ~ Product k
         => Ok k a => Ok k b
         => k (p a b) b -> b -> pc a -> b
  foldru f z (PCompose xss) = foldru (PFun \(xs, z') -> foldru f z' xs) z xss
                             \\ proveFunctor @g @a
  foldlu :: forall a b pc k p.
            pc ~ PCompose f g => k ~ Dom pc => Cartesian k => p ~ Product k
         => Ok k a => Ok k b
         => k (p a b) a -> a -> pc b -> a
  foldlu f z (PCompose xss) = foldlu (PFun \(z', xs) -> foldlu f z' xs) z xss
                              \\ proveFunctor @g @b
  toList :: forall a pc.
            pc ~ PCompose f g
         => Ok (Dom pc) a => pc a -> [a]
  toList (PCompose xss) = P.concat (fmap toList (toList xss))
                          \\ proveFunctor @g @a



instance Apply PProxy where
  liftA2uu _ = PFun \_ -> PProxy

instance Apply PIdentity where
  liftA2uu (PFun f) = PFun \(PIdentity x, PIdentity y) -> PIdentity (f (x, y))

instance (PCon a, Semigroup a) => Apply (PTuple a) where
  liftA2uu (PFun f) =
    PFun \(PTuple a x, PTuple b y) -> PTuple (a <> b) (f (x, y))

instance (Apply f, Apply g, Dom f ~ Dom g, Cod f ~ Cod g
         , Dom f ~ (-#>), Cod f ~ (-#>)) =>
         Apply (PProduct f g) where
  liftA2uu f = PFun \(PPair xs xs', PPair ys ys') ->
                      PPair
                      (runPFun (liftA2uu f) (xs, ys))
                      (runPFun (liftA2uu f) (xs', ys'))

instance (Apply f, Apply g, Dom f ~ Cod g
         , Dom g ~ (-#>), Cod f ~ (-#>), Cod g ~ (-#>)) =>
         Apply (PCompose f g) where
  liftA2uu :: forall a b c pc p q.
              pc ~ PCompose f g => p ~ Product (Dom pc) => q ~ Product (Cod pc)
           => Ok (Dom pc) a => Ok (Dom pc) b => Ok (Dom pc) c
           => Dom pc (p a b) c -> Cod pc (q (pc a) (pc b)) (pc c)
  liftA2uu f = PFun \(PCompose xss, PCompose yss) ->
                      PCompose (runPFun (liftA2uu (liftA2uu f)) (xss, yss))
    \\ proveFunctor @g @a \\ proveFunctor @g @b \\ proveFunctor @g @c



instance Applicative PProxy where
  pure _ = PProxy

instance Applicative PIdentity where
  pure x = PIdentity x

instance (PCon a, Monoid a) => Applicative (PTuple a) where
  pure x = PTuple mempty x

instance ( Applicative f, Applicative g, Dom f ~ Dom g, Cod f ~ Cod g
         , Dom f ~ (-#>), Cod f ~ (-#>)) =>
         Applicative (PProduct f g) where
  pure x = PPair (pure x) (pure x)

instance ( Applicative f, Applicative g, Dom f ~ Cod g
         , Dom g ~ (-#>), Cod f ~ (-#>), Cod g ~ (-#>)) =>
         Applicative (PCompose f g) where
  pure :: forall a pc. pc ~ PCompose f g => Ok (Dom pc) a => a -> pc a
  pure x = PCompose (pure (pure x))
           \\ proveFunctor @g @a



instance Traversable PProxy where
  mapTraverse g _ = PFun \_ -> pure (runPFun g PProxy)
  
instance Traversable PIdentity where
  mapTraverse g f =
    PFun \(PIdentity x) -> runPFun (fmap (g . PFun PIdentity)) (runPFun f x)

instance PCon p => Traversable (PTuple p) where
  mapTraverse g f =
    PFun \(PTuple a x) -> runPFun (fmap (g . PFun (PTuple a))) (runPFun f x)

-- TODO: F.Product F.Compose



--------------------------------------------------------------------------------



newtype UIdentity a = UIdentity { runUIdentity :: a }
  deriving (Eq, Ord, Read, Show, Generic)

instance Arbitrary a => Arbitrary (UIdentity a) where
  arbitrary = UIdentity <$> arbitrary
instance CoArbitrary a => CoArbitrary (UIdentity a)
instance Function a => Function (UIdentity a)

data UPair a b = UPair { ufst :: !a, usnd :: !b}
  deriving (Eq, Ord, Read, Show, Generic)

instance (Arbitrary a, Arbitrary b) => Arbitrary (UPair a b) where
  arbitrary = uncurry UPair <$> arbitrary
instance (CoArbitrary a, CoArbitrary b) => CoArbitrary (UPair a b)
instance (Function a, Function b) => Function (UPair a b)

data UIVector a = UIVector { getUIndex :: !Int
                           , getUIVector :: !(U.Vector a)
                           }
  deriving (Eq, Ord, Read, Show, Generic)

uivector :: U.Unbox a => U.Vector a -> UIVector a
uivector xs = assert (not (U.null xs)) $ UIVector 0 xs

instance (Arbitrary (U.Vector a), U.Unbox a) => Arbitrary (UIVector a) where
  arbitrary = do xs <- arbitrary `suchThat` (not P.. U.null)
                 let n = U.length xs
                 i <- choose (0, n-1)
                 P.return (UIVector i xs)
  shrink xs = limitIndex <$> genericShrink xs
    where limitIndex (UIVector j ys) = UIVector (min j (U.length ys - 1)) ys
instance CoArbitrary (U.Vector a) => CoArbitrary (UIVector a)
instance Function (U.Vector a) => Function (UIVector a)



instance Functor UIdentity where
  proveFunctor = Sub Dict
  type Dom UIdentity = (-#>)
  type Cod UIdentity = (->)
  fmap (PFun f) = \(UIdentity x) -> UIdentity (f x)

-- instance Inclusion UIdentity where
--   inclusion = UIdentity
--   runInclusion = runUIdentity

instance Foldable UIdentity where
  foldMap (PFun f) (UIdentity x) = f x
  foldru (PFun f) z (UIdentity x) = f (x, z)
  foldlu (PFun f) z (UIdentity x) = f (z, x)
  toList (UIdentity x) = [x]

instance Apply UIdentity where
  liftA2uu (PFun f) = \(UIdentity x, UIdentity y) -> UIdentity (f (x, y))

instance Applicative UIdentity where
  pure x = UIdentity x

instance Traversable UIdentity where
  mapTraverse g f = \(UIdentity x) -> fmap (PFun (g . UIdentity)) (f x)

instance Semicomonad UIdentity where
  extend f = \xs -> UIdentity (f xs)

instance Comonad UIdentity where
  extract = \(UIdentity x) -> x



instance Functor (UPair a) where
  proveFunctor = Sub Dict
  type Dom (UPair a) = (-#>)
  type Cod (UPair a) = (->)
  fmap (PFun f) = \(UPair a x) -> UPair a (f x)

instance Foldable (UPair a) where
  foldMap (PFun f) (UPair _ x) = f x
  foldru (PFun f) z (UPair _ x) = f (x, z)
  foldlu (PFun f) z (UPair _ x) = f (z, x)
  toList (UPair _ x) = [x]

instance Semigroup a => Apply (UPair a) where
  liftA2uu (PFun f) = \(UPair a x, UPair b y) -> UPair (a <> b) (f (x, y))

instance Monoid a => Applicative (UPair a) where
  pure x = UPair mempty x

instance Traversable (UPair a) where
  mapTraverse g f = \(UPair a x) -> fmap (PFun (g . (UPair a))) (f x)

instance Semicomonad (UPair a) where
  extend f = \xs@(UPair a _) -> UPair a (f xs)

instance Comonad (UPair a) where
  extract = \(UPair _ x) -> x

-- instance ComonadEnv (UPair e) where
--   type Env (UPair e) = e
--   ask = \(UPair e _) -> e

instance ComonadStore (UPair s) where
  type Index (UPair s) = s
  pos = \(UPair s _) -> s
  peeku = \(_, UPair _ x) -> x
  seeku = \(s, UPair _ x) -> UPair s x



instance Functor U.Vector where
  proveFunctor = Sub Dict
  type Dom U.Vector = (-#>)
  type Cod U.Vector = (->)
  {-# INLINE fmap #-}
  fmap (PFun f) = U.map f

instance Foldable U.Vector where
  {-# INLINE foldMap #-}
  foldMap (PFun f) = U.foldl (\r x -> r <> f x) mempty
  {-# INLINE foldru #-}
  foldru (PFun f) z = U.foldr (P.curry f) z
  {-# INLINE foldlu #-}
  foldlu (PFun f) z = U.foldl (P.curry f) z
  {-# INLINE toList #-}
  toList = U.toList
  {-# INLINE length #-}
  length = U.length

instance Apply U.Vector where
  {-# INLINE liftA2uu #-}
  liftA2uu (PFun f) = uncurry (U.zipWith (curry f))



instance Functor UIVector where
  type Dom UIVector = (-#>)
  type Cod UIVector = (->)
  proveFunctor = Sub Dict
  {-# INLINE fmap #-}
  fmap f = \(UIVector i xs) -> UIVector i (fmap f xs)

instance Foldable UIVector where
  {-# INLINE foldMap #-}
  foldMap f (UIVector _ xs) = foldMap f xs
  {-# INLINE foldru #-}
  foldru f z (UIVector _ xs) = foldru f z xs
  {-# INLINE foldlu #-}
  foldlu f z (UIVector _ xs) = foldlu f z xs
  {-# INLINE toList #-}
  toList (UIVector _ xs) = U.toList xs
  {-# INLINE length #-}
  length (UIVector _ xs) = U.length xs

instance Apply UIVector where
  {-# INLINE liftA2uu #-}
  liftA2uu (PFun f) = \(UIVector i xs, UIVector j ys) ->
                        UIVector (min i j) (U.zipWith (curry f) xs ys)
  -- liftA2uu (PFun f) = \(UIVector i xs, UIVector j ys) ->
  --                       UIVector (min i j) (U.fromListN (min (length xs) (length ys)) (P.zipWith (curry f) (U.toList xs) (U.toList ys)))

instance Semicomonad UIVector where
  extend f = \(UIVector i xs) ->
               let n = U.length xs
                   ys = [f (UIVector j xs) | j <- [0..n-1]]
               in UIVector i (U.fromListN n ys)

instance Comonad UIVector where
  extract = \(UIVector i xs) -> xs U.! i

-- instance ComonadEnv UIVector where
--   type Env UIVector = Int
--   ask = \(UIVector i _) -> i

instance ComonadStore UIVector where
  type Index UIVector = Int
  pos = \(UIVector i _) -> i
  peeku = \(i, UIVector _ xs) -> xs U.! i
  seeku = \(i, UIVector _ xs) ->
    assert (i >= 0 && i < U.length xs) $ UIVector i xs
