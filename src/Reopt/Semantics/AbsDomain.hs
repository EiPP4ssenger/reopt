------------------------------------------------------------------------
-- |
-- Module           : Reopt.Semantics.AbsDomain
-- Description      : Control Flow Graph discovery support
-- Copyright        : (c) Galois, Inc 2015
-- Maintainer       : Simon Winwood <sjw@galois.com>
-- Stability        : provisional
--
-- A set of classes representing abstract domains with some
-- specialization for Reopt
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}

module Reopt.Semantics.AbsDomain where

import           Control.Lens
import qualified Data.Foldable as Fold
import           Data.Set (Set)
import qualified Data.Set as S

import           Reopt.Semantics.Representation
import qualified Reopt.Semantics.StateNames as N
import           Reopt.Semantics.Types


-- | Parially ordered sets
class POSet d where
  leq :: d a -> d a -> Bool

-- | Bounded lattices
class POSet d => Lattice d where
  -- | The top element
  top :: TypeRepr tp -> d tp

  -- | Least upper bound (always defined, as we have top)
  lub :: d tp -> d tp -> d tp

  glb :: d tp -> d tp -> d tp

  bottom :: TypeRepr tp -> d tp

  -- | Join the old and new states and return the updated state iff
  -- the result is larger than the old state.
  joinD :: d tp -> d tp -> Maybe (d tp)
  joinD new old
    | new `leq` old = Nothing
    | otherwise     = Just $ lub new old

  -- Predicates
  isTop :: d tp -> Bool

-- data Pointed a = Top | NotTop a

-- | Abstract domains
class Lattice d => AbsDomain d where
  -- | Compute the effect of the operation on the abstract value
  transfer :: App d tp -> d tp

  -- | Convert the abstract domain into a set of values, with Nothing
  -- if the set would be the universal set (i.e., convert into the
  -- pointed set)
  concretize :: d tp -> Maybe (Set Integer)

  -- | Abstract a set of integers into an abstract value
  abstract :: Fold.Foldable t => TypeRepr tp -> t Integer -> d tp
  abstract tp tv = Fold.foldl' (\d v -> singleton tp v `lub` d) (bottom tp) tv

  singleton :: TypeRepr tp -> Integer -> d tp
  singleton tp v = abstract tp (Identity v)

  -- ------------------------------------------------------------
  -- Reopt specific stuff
  
  finishBlock :: (forall cl. N.RegisterName cl -> d (N.RegisterType cl))
                 -> d tp -> d tp
  finishBlock _f d = d

  initialState :: N.RegisterName cl -> d (N.RegisterType cl)
  initialState r = top (N.registerType r)

--------------------------------------------------------------------------------
-- Lifted pairs.

data PairF (d :: k -> *) (d' :: k -> *) (a :: k) = PairF (d a) (d' a) 

instance Field1 (PairF d1 d' v) (PairF d2 d' v) (d1 v) (d2 v) where
  _1 = lens (\(PairF l _) -> l) (\(PairF _ r) l -> PairF l r)

instance Field2 (PairF d d1' v) (PairF d d2' v) (d1' v) (d2' v) where
  _2 = lens (\(PairF _ r) -> r) (\(PairF l _) r -> PairF l r)

instance (POSet d, POSet d') => POSet (PairF d d') where
  -- We have a choice here between lexical and pointwise inequality.  
  -- Pointwise is easier ...
  -- FIXME: check this obeys the various laws for posets
  leq (PairF l r) (PairF l' r') = l `leq` l' && r `leq` r'

instance (Lattice d, Lattice d') => Lattice (PairF d d') where
  top tp = PairF (top tp) (top tp)
  
  lub (PairF l r) (PairF l' r') = PairF (l `lub` l') (r `lub` r') 
  glb (PairF l r) (PairF l' r') = PairF (l `glb` l') (r `glb` r')
  
  bottom tp = PairF (bottom tp) (bottom tp)

  joinD (PairF l r) (PairF l' r') =
    case (joinD l l', joinD r r') of
     (Nothing, Nothing) -> Nothing
     (Just v, Nothing)  -> Just $ PairF v r'
     (Nothing, Just v)  -> Just $ PairF l' v
     (Just lv, Just rv) -> Just $ PairF lv rv

  isTop (PairF l r) = isTop l && isTop r

instance (AbsDomain d, AbsDomain d') => AbsDomain (PairF d d') where
  transfer v = PairF (transfer (mapApp (view _1) v))
                     (transfer (mapApp (view _2) v))
  
  concretize (PairF l r) = 
    case (concretize l, concretize r) of
     (Nothing, Nothing) -> Nothing
     (Just v, Nothing)  -> Just v
     (Nothing, Just v)  -> Just v
     (Just lv, Just rv) -> Just $ S.intersection lv rv

  singleton tp v = PairF (singleton tp v) (singleton tp v)

  abstract tp v = PairF (abstract tp v) (abstract tp v)
