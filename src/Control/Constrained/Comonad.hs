{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Control.Constrained.Comonad
  ( Semicomonad(..)
  , law_Semicomonad_compose
  , law_Semicomonad_assoc
  , law_Semicomonad_extend
  , law_Semicomonad_duplicate
  , Comonad(..)
  , law_Comonad_leftId
  , law_Comonad_rightId
  , Cokleisli(..)
  , ComonadStore(..)
  , law_ComonadStore_getPut
  , law_ComonadStore_putPut
  , law_ComonadStore_putGet
  , law_ComonadStore_extract
  , law_ComonadStore_seek
  ) where

import Prelude ()
import Control.Constrained.Prelude

import Control.Constrained.Cartesian
import Control.Constrained.Category
import Control.Constrained.Closed
import Control.Constrained.Functor
import Data.Constraint
import Data.Functor.Const
import Data.Functor.Identity
import qualified Data.Functor.Sum as F
import Data.Kind
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Data.Proxy



class (Functor f, Dom f `SubCatOf` Cod f) => Semicomonad f where
  {-# MINIMAL extend #-}
  (=<=) :: forall a b c k l.
           k ~ Dom f => l ~ Cod f => Ok k a => Ok k b => Ok k c
        => l (f b) c -> l (f a) b -> l (f a) c
  g =<= f = g . extend f
            \\ proveSubCatOf @(Dom f) @(Cod f) @a
            \\ proveSubCatOf @(Dom f) @(Cod f) @b
            \\ proveSubCatOf @(Dom f) @(Cod f) @c
            \\ proveFunctor @f @a
            \\ proveFunctor @f @b
            \\ proveFunctor @f @c
  extend :: forall a b k l.
            k ~ Dom f => l ~ Cod f => Ok k a => Ok k b
         => l (f a) b -> l (f a) (f b)

duplicate :: forall f a k.
             Semicomonad f => Cod f ~ Dom f => k ~ Dom f => Ok k a
          => k (f a) (f (f a))
duplicate = extend id
            \\ proveFunctor @f @a

class Semicomonad f => Comonad f where
  {-# MINIMAL extract #-}
  extract :: forall a k l. k ~ Dom f => l ~ Cod f => Ok k a => l (f a) a



newtype Cokleisli (f :: FunctorKind) a b =
  Cokleisli { runCokleisli :: Cod f (f a) b }

instance Semicomonad f => Semigroupoid (Cokleisli f) where
  type Ok (Cokleisli f) = Ok (Dom f)
  Cokleisli g . Cokleisli f = Cokleisli (g =<= f)

instance Comonad f => Category (Cokleisli f) where
  id = Cokleisli extract



--------------------------------------------------------------------------------



-- | Store (costate) comonad
class (Comonad f, Ok (Cod f) (Index f), Cartesian (Cod f)) =>
      ComonadStore f where
-- get-put
-- prop> pos (seek s xs) = s
-- put-put
-- prop> seek t (seek s xs) = seek t xs
-- put-get
-- prop> seek (pos xs) xs = xs
-- prop> peek (pos xs) xs = extract xs
-- prop> seek s = peek s . duplicate
  type Index f :: Type
  pos :: s ~ Index f
      => k ~ Dom f => l ~ Cod f => Ok k a
      => l (f a) s
  peeku :: s ~ Index f
        => k ~ Dom f => l ~ Cod f => q ~ Product l => Ok k a
        => l (q s (f a)) a
  peek :: forall a s k l.
          s ~ Index f
       => k ~ Dom f => l ~ Cod f => Closed l => Ok k a
       => l s (l (f a) a)
  peek = curry peeku
         \\ proveSubCatOf @k @l @a
         \\ proveFunctor @f @a
  -- peeks :: s ~ Index f => Ok (Dom f) a => (s -> s) -> f a -> a

  seeku :: s ~ Index f
        => k ~ Dom f => l ~ Cod f => q ~ Product l => Ok k a
        => l (q s (f a)) (f a)
  seek :: forall a s k l.
          s ~ Index f => k ~ Dom f => l ~ Cod f => Closed l => Ok k a
       => l s (l (f a) (f a))
  seek = curry seeku
         \\ proveFunctor @f @a
  -- seeks :: s ~ Index f => Ok (Dom f) a => (s -> s) -> f a -> f a

  -- experiment :: Functor g => Dom g ~ Dom f => Cod g ~ Cod f
  --            => s ~ Index f => Ok (Dom f) a
  --            => (s -> g s) -> f a -> g a

  -- default pos :: Dom f ~ (->) => Cod f ~ (->)
  --             => s ~ Index f => Ok (Dom f) a => f a -> s
  -- pos xs = getConst (experiment Const xs)
  -- default peek :: Dom f ~ (->) => Cod f ~ (->)
  --              => s ~ Index f => Ok (Dom f) a => s -> f a -> a
  -- peek s xs = runIdentity (experiment (\_ -> Identity s) xs)
  -- default seek :: Dom f ~ (->) => Cod f ~ (->)
  --              => s ~ Index f => Ok (Dom f) a => s -> f a -> f a
  -- seek s = peek s . duplicate
  -- default experiment :: Dom f ~ (->) => Cod f ~ (->)
  --                    => Functor g => Dom g ~ Dom f => Cod g ~ Cod f
  --                    => s ~ Index f => Ok (Dom f) a
  --                    => (s -> g s) -> f a -> g a
  -- experiment f xs = fmap (\s -> peek s xs) (f (pos xs))



-- Laws:
-- <https://r6research.livejournal.com/23705.html>
-- prop> extract . l = id
-- prop> fmap l . l = duplicate . l

-- Laws:
-- get-put
-- prop> pos (seek s xs) = s
-- put-put
-- prop> seek t (seek s xs) = seek t xs
-- put-get
-- prop> seek (pos xs) xs = xs

-- prop> peek (pos xs) xs = extract xs

-- prop> seek s = peek s . duplicate



-- TODO: Provide 'Co'



--------------------------------------------------------------------------------



-- prop> extend f . extend g = extend (f . extend g)
law_Semicomonad_compose :: forall f a b c k l.
                           Semicomonad f
                        => k ~ Dom f => l ~ Cod f => Ok k a => Ok k b => Ok k c
                        => l (f b) c -> l (f a) b
                        -> (l (f a) (f c), l (f a) (f c))
law_Semicomonad_compose g f = (extend g . extend f, extend (g . extend f))
                              \\ proveSubCatOf @(Dom f) @(Cod f) @a
                              \\ proveSubCatOf @(Dom f) @(Cod f) @b
                              \\ proveSubCatOf @(Dom f) @(Cod f) @c
                              \\ proveFunctor @f @a
                              \\ proveFunctor @f @b
                              \\ proveFunctor @f @c

-- prop> (h =<= (g =<= f)) = ((h =<= g) =<= f)
law_Semicomonad_assoc :: forall f a b c d k l.
                         Semicomonad f
                      => k ~ Dom f => l ~ Cod f
                      => Ok k a => Ok k b => Ok k c => Ok k d
                      => l (f c) d
                      -> l (f b) c
                      -> l (f a) b
                      -> (l (f a) d, l (f a) d)
law_Semicomonad_assoc h g f = (h =<= (g =<= f), (h =<= g) =<= f)

law_Semicomonad_extend :: forall f a b c k l.
                          Semicomonad f
                       => k ~ Dom f => l ~ Cod f
                       => Ok k a => Ok k b => Ok k c
                       => l (f b) c
                       -> l (f a) b
                       -> (l (f a) c, l (f a) c)
law_Semicomonad_extend g f = (g . extend f, g =<= f)
                             \\ proveSubCatOf @(Dom f) @(Cod f) @c
                             \\ proveFunctor @f @a
                             \\ proveFunctor @f @b
                             \\ proveFunctor @f @c

law_Semicomonad_duplicate :: forall f a k.
                             Semicomonad f
                          => Cod f ~ Dom f
                          => k ~ Dom f
                          => Ok k a
                          => (k (f a) (f (f a)), k (f a) (f (f a)))
law_Semicomonad_duplicate = (duplicate, extend id)
                            \\ proveFunctor @f @a



-- prop> extend extract = id
law_Comonad_leftId :: forall f a k l.
                      Comonad f
                   => k ~ Dom f => l ~ Cod f => Ok k a
                   => (l (f a) (f a), l (f a) (f a))
law_Comonad_leftId = (extend extract, id @l)
                     \\ proveFunctor @f @a

-- prop> extract . extend f = f
law_Comonad_rightId :: forall f a b k l.
                       Comonad f
                    => k ~ Dom f => l ~ Cod f => Ok k a => Ok k b
                    => l (f a) b
                    -> (l (f a) b, l (f a) b)
law_Comonad_rightId f = (extract . extend f, f)
                        \\ proveSubCatOf @(Dom f) @(Cod f) @a
                        \\ proveSubCatOf @(Dom f) @(Cod f) @b
                        \\ proveFunctor @f @a
                        \\ proveFunctor @f @b



--------------------------------------------------------------------------------



-- | get-put:
-- prop> pos (seek s xs) = s
law_ComonadStore_getPut :: forall f a s k l q.
                           ComonadStore f
                        => s ~ Index f
                        => k ~ Dom f => l ~ Cod f => q ~ Product l
                        => Ok k a
                        => ( l (q s (f a)) s
                           , l (q s (f a)) s
                           )
law_ComonadStore_getPut = (pos . seeku, exl)
                          \\ proveCartesian @l @s @(f a)
                          \\ proveFunctor @f @a

-- | put-put
-- prop> seek t (seek s xs) = seek t xs
law_ComonadStore_putPut :: forall f a s k l q.
                           ComonadStore f
                        => s ~ Index f
                        => k ~ Dom f => l ~ Cod f => q ~ Product l
                        => Ok k a
                        => ( l (q (q s s) (f a)) (f a)
                           , l (q (q s s) (f a)) (f a)
                           )
law_ComonadStore_putPut = ( seeku . prod id seeku . assoc . prod swap id
                          , seeku . prod exr id
                          )
                          \\ proveCartesian @l @(q s s) @(f a)
                          \\ proveCartesian @l @s @(q s (f a))
                          \\ proveCartesian @l @s @(f a)
                          \\ proveCartesian @l @s @s
                          \\ proveFunctor @f @a

-- \ put-get
-- prop> seek (pos xs) xs = xs
law_ComonadStore_putGet :: forall f a s k l q.
                           ComonadStore f
                        => s ~ Index f
                        => k ~ Dom f => l ~ Cod f => q ~ Product l
                        => Ok k a
                        => (l (f a) (f a), l (f a) (f a))
law_ComonadStore_putGet = ( seeku . prod pos id . dup
                          , id
                          )
                          \\ proveCartesian @l @(f a) @(f a)
                          \\ proveCartesian @l @s @(f a)
                          \\ proveFunctor @f @a

-- prop> peek (pos xs) xs = extract xs
law_ComonadStore_extract :: forall f a s k l q.
                            ComonadStore f
                         => s ~ Index f
                         => k ~ Dom f => l ~ Cod f => q ~ Product l
                         => Ok k a
                         => (l (f a) a, l (f a) a)
law_ComonadStore_extract = ( peeku . prod pos id . dup
                           , extract
                           )
                           \\ proveCartesian @l @(f a) @(f a)
                           \\ proveCartesian @l @s @(f a)
                           \\ proveFunctor @f @a
                           \\ proveSubCatOf @k @l @a

-- prop> seek s = peek s . duplicate
law_ComonadStore_seek :: forall f a s k l q.
                         ComonadStore f
                      => s ~ Index f
                      => k ~ Dom f => l ~ Cod f => q ~ Product l
                      => k ~ l
                      => Ok k a
                      => (l (q s (f a)) (f a), l (q s (f a)) (f a))
law_ComonadStore_seek = ( seeku
                        , peeku . prod id duplicate
                        )
                        \\ proveCartesian @l @s @(f (f a))
                        \\ proveCartesian @l @s @(f a)
                        \\ proveFunctor @f @(f a)
                        \\ proveFunctor @f @a



--------------------------------------------------------------------------------



instance Semicomonad Proxy where
  extend _ = \_ -> Proxy

instance Semicomonad (Const a) where
  extend _ = \(Const x) -> Const x

instance Semicomonad Identity where
  extend f = fmap f . Identity

instance Semicomonad (Either a) where
  extend f = fmap f . fmap Right

instance Semicomonad ((,) a) where
  extend f = \(a, x) -> (a, f (a, x))

instance Semicomonad [] where
  extend f = extendList
    where extendList [] = []
          extendList l@(x:xs) = f l : extendList xs

instance Semicomonad NonEmpty where
  extend f = NE.fromList . extendList . NE.toList
    where extendList [] = []
          extendList l@(x:xs) = (f . NE.fromList) l : extendList xs

instance ( Semicomonad f, Semicomonad g, Dom f ~ Dom g, Cod f ~ Cod g
         , Dom f ~ (->), Cod f ~ (->)) =>
         Semicomonad (F.Sum f g) where
  extend f = \case (F.InL xs) -> (F.InL =<= (f . F.InL)) xs
                   (F.InR xs') -> (F.InR =<= (f . F.InR)) xs'

instance Comonad Identity where
  extract = \(Identity x) -> x

instance Comonad ((,) a) where
  extract = \(_, x) -> x

instance Comonad NonEmpty where
  extract = \(x :| _) -> x

-- '(->) a' ?

instance ( Comonad f, Comonad g, Dom f ~ Dom g, Cod f ~ Cod g
         , Dom f ~ (->), Cod f ~ (->)) =>
         Comonad (F.Sum f g) where
  extract = \case (F.InL xs) -> extract xs
                  (F.InR xs') -> extract xs'

instance ComonadStore ((,) s) where
  type Index ((,) s) = s
  pos = \(s, _) -> s
  peeku = \(_, (_, x)) -> x
  seeku = \(s, (_, x)) -> (s, x)



-- <https://ncatlab.org/nlab/show/store+comonad>: reader monad in writer comonad
data Store s a = Store (s -> a) s

store :: (s -> a) -> s -> Store s a
store f s = Store f s

runStore :: Store s a -> (s -> a, s)
runStore (Store f s) = (f, s)

instance Functor (Store s) where
  proveFunctor = Sub Dict
  type Dom (Store s) = (->)
  type Cod (Store s) = (->)
  fmap g = \(Store f s) -> Store (g . f) s

-- TODO: instance Applicative (Store k s) where

instance Semicomonad (Store s) where
  extend g = \(Store f s) -> let go s' = g (Store f s') in Store go s

instance Comonad (Store s) where
  extract = \(Store f s) -> f s

instance ComonadStore (Store s) where
  type Index (Store s) = s
  pos = \(Store _ s) -> s
  peeku = \(s, Store f _) -> f s
  seeku = \(s, Store f _) -> Store f s



-- <https://r6research.livejournal.com/23705.html>
type Lens a b = a -> Store b a

get :: Lens a b -> a -> b
get lens a = b
  where Store f b = lens a

set :: Lens a b -> a -> b -> a
set lens a = f
  where Store f b = lens a

-- prop> get l (set l s b) = b
-- prop> set l s (get l s) = s
-- prop> set l (set l s b1) b2 = set l s b2

-- prop> extract . l = id
-- prop> fmap l . l = duplicate . l
