{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UnicodeSyntax #-}

module TT.Judge where

import TT.Context
import TT.Operator
import TT.Model
import TT.Exception

import Abt.Class
import Abt.Types

import Control.Applicative
import Control.Lens hiding ((#))
import Control.Lens.Action
import Control.Monad hiding (void)
import Control.Monad.Catch
import Data.Foldable
import Data.Typeable
import Data.Vinyl
import Prelude hiding (pi, EQ)

data JudgeError t
  = NotType t
  | NotOfType t t
  | NotInferrable t
  | ExpectedPiType t
  | ExpectedSgType t
  deriving (Show, Functor, Foldable, Traversable, Typeable)

instance Typeable (DTm t) ⇒ Exception (JudgeError (DTm t))

makePrisms ''JudgeError

type JUDGE v t m =
  ( MonadVar v m
  , MonadThrow m
  , MonadCatch m
  , Abt v Op t
  , HEq1 t
  , Typeable (t Z)
  , Typeable v
  )

isType
  ∷ JUDGE v t m
  ⇒ Ctx v (t Z) -- ^ the context
  → t Z -- ^ the term
  → m (t Z) -- ^ the term turned into a type if possible
isType γ ty =
  out ty >>= \case
    UNIV :$ _ → return univ
    PI :$ α :& xβ :& _ → do
      α' ← isType γ α
      x :\ β ← out xβ
      pi α' . (x \\) <$> isType (γ >: (x, α')) β
    SG :$ α :& xβ :& _ → do
      α' ← isType γ α
      x :\ β ← out xβ
      sg α' . (x \\) <$> isType (γ >: (x, α')) β
    UNIT :$ _ → return unit
    VOID :$ _ → return void
    SING :$ α :& m :& _ → do
      α' ← isType γ α
      m' ← checkType γ α' m
      return $ sing α' m'
    SQUASH :$ α :& _ → 
      squash <$> isType γ α
    EQ :$ α :& β :& m :& n :& _ → do
      α' ← isType γ α
      β' ← isType γ β
      m' ← checkType γ α' m
      n' ← checkType γ β' n
      nbeOpenT γ $ eq α' β' m' n'
    _ → do
      ne ← neutral ty
      if ne then checkTypeNe γ univ ty else
        throwTT $ NotType ty

-- | Check the type of normal terms.
--
checkType
  ∷ JUDGE v t m
  ⇒ Ctx v (t Z) -- ^ the context
  → t Z -- ^ the type
  → t Z -- ^ the term
  → m (t Z) -- ^ the elaborated term
checkType γ ty tm = do
  ty' ← isType γ ty
  (,) <$> out ty' <*> out tm >>= \case
    (UNIV :$ _, PI :$ α :& xβ :& _) → do
      α' ← checkType γ ty α
      x :\ β ← out xβ
      pi α' . (x \\) <$> checkType (γ >: (x, α')) ty β
    (UNIV :$ _, SING :$ α :& m :& _) → do
      α' ← checkType γ ty α
      sing α' <$> checkType γ α' m
    (UNIV :$ _, UNIT :$ _) → return unit
    (UNIV :$ _, VOID :$ _) → return void
    (PI :$ α :& xβ :& _, LAM :$ ye :& _) → do
      z ← fresh
      βz ← xβ // var z
      ez ← ye // var z
      lam . (z \\) <$> checkType (γ >: (z, α)) βz ez
    (SG :$ α :& xβ :& _, PAIR :$ m :& n :& _) → do
      m' ← checkType γ α m
      βm ← nbeOpenT γ =<< xβ // m'
      pair m' <$> checkType γ βm n
    (SING :$ α :& m :& _, _) → do
      α' ← nbeOpenT γ α
      tm' ← checkType γ α' tm
      m' ← nbeOpen γ α m
      n' ← nbeOpen γ α tm'
      unify γ α m' n'
    (SQUASH :$ α :& _, BOX :$ m :& _) → do
      m' ← checkType γ α m
      return $ box m'
    (UNIT :$ _, AX :$ _) → return ax
    _ → do
      ne ← neutral tm
      if ne then checkTypeNe γ ty tm else
        throwTT $ NotOfType ty tm

-- | Unwrap singleton types
--
erase
  ∷ JUDGE v t m
  ⇒ t Z
  → m (t Z)
erase ty =
  out ty >>= \case
    SING :$ α :& _ :& _ → erase α
    _ → return ty

-- | Decide if a term is neutral.
--
neutral
  ∷ JUDGE v t m
  ⇒ t Z
  → m Bool
neutral tm =
  out tm <&> \case
    V _ → True
    APP :$ _ → True
    EQ :$ _ → True
    FST :$ _ → True
    SND :$ _ → True
    COE :$ _ → True
    COH :$ _ → True
    ABORT :$ _ → True
    REFL :$ _ → True
    _ → False

-- | Check the type of neutral terms.
--
checkTypeNe
  ∷ JUDGE v t m
  ⇒ Ctx v (t Z) -- ^ the context
  → t Z -- ^ the type
  → t Z -- ^ the neutral term
  → m (t Z)
checkTypeNe γ ty tm = do
  ty' ← erase =<< infType γ tm
  ty'' ← unify γ univ ty ty'
  nbeOpen γ ty'' tm


-- | Infer the type of neutral terms.
--
infType
  ∷ JUDGE v t m
  ⇒ Ctx v (t Z) -- ^ the context
  → t Z -- ^ the term
  → m (t Z) -- ^ the type
infType γ tm =
  out tm >>= \case
    V v → containsLocal γ v
    APP :$ m :& n :& _ → do
      mty ← erase =<< infType γ m
      α :& xβ :& _ ← (out mty ^!? acts . _ViewOp PI)
        >>= maybe (throwTT $ ExpectedPiType mty) return
      n' ← checkType γ α n
      nbeOpenT γ =<< xβ // n'
    FST :$ m :& _ → do
      mty ← erase =<< infType γ m
      α :& _ ← (out mty ^!? acts . _ViewOp SG)
        >>= maybe (throwTT $ ExpectedSgType mty) return
      return α
    SND :$ m :& _ → do
      mty ← erase =<< infType γ m
      _ :& xβ :& _ ← (out mty ^!? acts . _ViewOp SG)
        >>= maybe (throwTT $ ExpectedSgType mty) return
      nbeOpenT γ =<< xβ // pi1 m
    ABORT :$ α :& m :& _ → do
      _ ← checkType γ void m
      nbeOpenT γ α
    COE :$ α :& β :& q :& m :& _ → do
      _ ← checkType γ (eq univ univ α β) q
      _ ← checkType γ α m
      nbeOpenT γ β
    COH :$ α :& β :& q :& m :& _ → do
      q' ← checkType γ (eq univ univ α β) q
      m' ← checkType γ α m
      nbeOpenT γ $ eq α β m' (coe α β q' m)
    REFL :$ α :& m :& _ → do
      α' ← isType γ α 
      m' ← checkType γ α' m
      nbeOpenT γ $ eq α' α' m' m'
    _ → throwTT $ NotInferrable tm
