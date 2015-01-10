{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
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

import Abt.Class
import Abt.Types

import Control.Applicative
import Control.Lens hiding ((#))
import Control.Monad hiding (void)
import Control.Monad.Error.Class
import Control.Monad.Error.Hoist
import Data.Vinyl
import Prelude hiding (pi, EQ)

data JudgeError v t
  = CtxError (CtxError v t)
  | NotType t
  | NotOfType t t
  | NotInferrable t
  | NotEqual t t
  | ExpectedPiType t
  | ExpectedSgType t
  deriving Show

makePrisms ''JudgeError

instance IsCtxError v t (JudgeError v t) where
  _AsCtxError = _CtxError

type JUDGE v t m =
  ( MonadVar v m
  , MonadError (JudgeError v (t Z)) m
  , Abt v Op t
  , HEq1 t
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
    EQ :$ α :& β :& m :& n :& _ → do
      α' ← isType γ α
      β' ← isType γ β
      m' ← checkType γ α' m
      n' ← checkType γ β' n
      nbeOpenT γ $ eq α' β' m' n'
    APP :$ _ → checkTypeNe γ univ ty
    _ → throwError $ NotType ty

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
      unless (m' === n') $
        throwError $ NotEqual m' n'
      return m'
    (UNIT :$ _, AX :$ _) → return ax
    _ → do
      ne ← neutral tm
      if ne then checkTypeNe γ ty tm else
        throwError $ NotOfType ty tm

-- | Unwrap singleton types.
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
  unless (ty === ty') $
    throwError $ NotOfType ty tm
  return ty'

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
      α :& xβ :& _ ← (out mty <&> preview (_ViewOp PI)) <!?> ExpectedPiType mty
      n' ← checkType γ α n
      nbeOpenT γ =<< xβ // n'
    FST :$ m :& _ → do
      mty ← erase =<< infType γ m
      α :& _ ← (out mty <&> preview (_ViewOp SG)) <!?> ExpectedSgType mty
      return α
    SND :$ m :& _ → do
      mty ← erase =<< infType γ m
      _ :& xβ :& _ ← (out mty <&> preview (_ViewOp SG)) <!?> ExpectedSgType mty
      nbeOpenT γ =<< xβ // pi1 m
    ABORT :$ α :& m :& _ → do
      _ ← checkType γ void m
      nbeOpenT γ α
    _ → throwError $ NotInferrable tm
