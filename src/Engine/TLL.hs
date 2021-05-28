{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FunctionalDependencies #-}
-- {-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs                 #-}


-- Parts of this file were written by Sjoerd Visscher

module Engine.TLL
  ( List(..)
  , Apply(..)
  , Unappend(..)
  , MapL(..)
  , FoldrL(..)
  , ConstMap(..)
  , SequenceList(..)
  , ToList(..)
  , type (+:+)
  , (+:+)
  , Vec(..)
  , Nat(..)
  , TNat(..)
  , Repeat(..)
  , CatRepeat(..)
  , repeat1Proof
  , repeatSuccProof
  , mkVec
  , vecHead
  ) where

import Control.Applicative
import Data.Type.Equality ((:~:)(..))
import Unsafe.Coerce (unsafeCoerce)

infixr 6 ::-
data List (ts :: [*]) where
  Nil :: List '[]
  (::-) :: t -> List ts -> List (t ': ts)

data SList (ls :: List ts) where
  SNil :: SList 'Nil
  SCons :: SList (t ::- ts)

instance Show (List '[]) where
    show Nil = "Nil"

instance (Show (List as), Show a)
    => Show (List (a ': as)) where
    show (a ::- rest) =
        show a ++ " ::- " ++ show rest

type family (+:+) (as :: [*]) (bs :: [*]) :: [*] where
  '[] +:+ bs = bs
  (a ': as) +:+ bs = a ': (as +:+ bs)

(+:+) :: List as -> List bs -> List (as +:+ bs)
(+:+) Nil bs = bs
(+:+) (a ::- as) bs = a ::- as +:+ bs

class Unappend as where
  unappend :: List (as +:+ bs) -> (List as, List bs)

instance Unappend '[] where
  unappend bs = (Nil, bs)

instance Unappend as => Unappend (a ': as) where
  unappend (a ::- abs) = case unappend abs of (as, bs) -> (a ::- as, bs)


appendNilNeutral :: ls +:+ '[] :~: ls
appendNilNeutral = unsafeCoerce Refl -- Two reasons for this:
                                     -- 1. we already know it works thanks to Idris
                                     -- 2. We don't want the runtime cost of
                                     --    iterating through `ls` to prove this

---------------------------------
-- Operations to transform output
-- Preliminary apply class

class Apply f a b where
  apply :: f -> a -> b

-- Map
class MapL f xs ys where
  mapL :: f -> List xs -> List ys

instance MapL f '[] '[] where
  mapL _ _ = Nil

instance (Apply f x y, MapL f xs ys)
  => MapL f (x ': xs) (y ': ys) where
  mapL f (x ::- xs) = apply f x ::- mapL f xs

-- Foldr
class FoldrL f acc xs where
  foldrL :: f -> acc -> List xs -> acc

instance FoldrL f acc '[] where
  foldrL _ acc _ = acc

instance (Apply f x (acc -> acc), FoldrL f acc xs)
  => FoldrL f acc (x ': xs) where
  foldrL f acc (x ::- xs) = apply f x $ foldrL f acc xs

type family ConstMap (t :: *) (xs :: [*]) :: [*] where
  ConstMap _      '[]  = '[]
  ConstMap t (x ': xs) = t ': (ConstMap t xs)

----------------------------------------
-- Features to ease feeding back outputs
--
class Applicative m => SequenceList m a b | a -> b, m b -> a where
    sequenceListA :: List a -> m (List b)

instance Applicative m => SequenceList m '[] '[] where
    sequenceListA _ = pure Nil

instance (Applicative m, SequenceList m as bs) => SequenceList m (m a ': as) (a ': bs) where
    sequenceListA (a ::- b) = liftA2 (::-) a (sequenceListA b)

data Nat = Z | S Nat

infixr 6 :>
data Vec (n :: Nat) (t :: *) where
  Empty :: Vec n a
  (:>) :: t -> Vec n t -> Vec (S n) t

class ToList f where
  toList :: f a -> [a]

instance ToList (Vec n) where
  toList Empty = []
  toList (x :> xs) = x : toList xs

instance (Show a) => Show (Vec n a) where
  show vec = show (toList vec)

mkVec :: a -> Vec (S Z) a
mkVec a = a :> Empty

vecHead :: Vec (S n) a -> a
vecHead (x :> _) = x

data TNat (n :: Nat) where
  Zero :: TNat Z
  Succ :: TNat n -> TNat (S n)

type family Repeat (n :: Nat) (e :: t) :: Vec n t where
  Repeat Z e = 'Empty
  Repeat (S n) e = e :> Repeat n e

type family RepeatLs (n :: Nat) (e :: [*]) :: [[*]] where
  RepeatLs Z ls = '[]

type family CatRepeat (n :: Nat) (ls :: [*]) :: [*]  where
  CatRepeat Z ls = '[]
  CatRepeat (S n) ls = ls +:+ CatRepeat n ls

repeat1Proof :: forall a. CatRepeat (S Z) a :~: a
repeat1Proof = appendNilNeutral

repeatSuccProof :: forall (n :: Nat) (ls :: [*]) . CatRepeat (S n) ls :~: (ls +:+ CatRepeat n ls)
repeatSuccProof = Refl

