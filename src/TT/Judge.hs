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
        throwError $ NotType ty

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
    (SQUASH :$ α :& _, _) → do
      m' ← checkType γ α tm
      return $ box m'
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
    FST :$ _ → True
    SND :$ _ → True
    COE :$ _ → True
    COH :$ _ → True
    ABORT :$ _ → True
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
  unify γ univ ty ty'

-- | Decide definitional equality
--
unify
  ∷ JUDGE v t m
  ⇒ Ctx v (t Z)
  → t Z
  → t Z
  → t Z
  → m (t Z)
unify γ α m n = do
  α' ← nbeOpenT γ α
  m' ← nbeOpen γ α' m
  n' ← nbeOpen γ α' n
  (,,) <$> out α' <*> out m' <*> out n' >>= \case
    _ | m' === n' → return m'
    (_, BOX :$ p :& _, BOX :$ _ :& _) → return $ box p
    (SQUASH :$ _, _, _) → return m'
    (UNIV :$ _, SQUASH :$ σ :& _, SQUASH :$ τ :& _) →
      squash <$> unify γ univ σ τ
    (UNIV :$ _, PI :$ σ :& xτ :& _, PI :$ σ' :& yτ' :& _) → do
      σ'' ← unify γ univ σ σ'
      pi σ'' <$> do
        z ← fresh
        τz ← xτ // var z
        τ'z ← yτ' // var z
        (z \\) <$> unify (γ >: (z, σ'')) univ τz τ'z
    (UNIV :$ _, SG :$ σ :& xτ :& _, SG :$ σ' :& yτ' :& _) → do
      σ'' ← unify γ univ σ σ'
      sg σ'' <$> do
        z ← fresh
        τz ← xτ // var z
        τ'z ← yτ' // var z
        (z \\) <$> unify (γ >: (z, σ'')) univ τz τ'z
    (UNIV :$ _, SING :$ σ :& s :& _, SING :$ σ' :& s' :& _) → do
      σ'' ← unify γ univ σ σ'
      sing σ'' <$> unify γ σ'' s s'
    (PI :$ σ :& uτ :& _, LAM :$ xe :& _, LAM :$ ye' :& _) → do
      z ← fresh
      ez ← xe // var z
      e'z ← ye' // var z
      τz ← uτ // var z
      lam . (z \\) <$> unify (γ >: (z, σ)) τz ez e'z
    (SG :$ σ :& uτ :& _, PAIR :$ p :& q :& _, PAIR :$ p' :& q' :& _) → do
      p'' ← unify γ σ p p'
      τp ← uτ // p''
      pair p'' <$> unify γ τp q q'
    _ → throwError $ NotEqual m' n'
   

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
    COE :$ α :& β :& q :& m :& _ → do
      _ ← checkType γ (eq univ univ α β) q
      _ ← checkType γ α m
      nbeOpenT γ β
    COH :$ α :& β :& q :& m :& _ → do
      q' ← checkType γ (eq univ univ α β) q
      m' ← checkType γ α m
      nbeOpenT γ $ eq α β m' (coe α β q' m)
    _ → throwError $ NotInferrable tm
