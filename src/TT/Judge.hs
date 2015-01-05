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
import Control.Lens
import Control.Monad hiding (void)
import Control.Monad.Error.Class
import Control.Monad.Error.Hoist
import Data.Vinyl

data JudgeError v t
  = CtxError (CtxError v t)
  | NotType t
  | NotOfType t t
  | NotInferrable t
  | NotEqual t t
  | ExpectedPiType t

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
  ⇒ Ctx v (t Z)
  → t Z
  → m ()
isType γ ty =
  out ty >>= \case
    UNIV :$ _ → return ()
    PI :$ α :& xβ :& _ → do
      isType γ α
      x :\ β ← out xβ
      isType (γ >: (x,α)) β
    UNIT :$ _ → return ()
    VOID :$ _ → return ()
    SING :$ α :& m :& _ → do
      isType γ α
      checkType γ α m
    APP :$ _ → checkTypeNe γ univ ty
    _ → throwError $ NotType ty

-- | Check the type of normal terms.
--
checkType
  ∷ JUDGE v t m
  ⇒ Ctx v (t Z) -- ^ the context
  → t Z -- ^ the type
  → t Z -- ^ the term
  → m ()
checkType γ ty tm =
  (,) <$> out ty <*> out tm >>= \case
    (UNIV :$ _, PI :$ α :& xβ :& _) → do
      checkType γ ty α
      x :\ β ← out xβ
      checkType (γ >: (x, α)) ty β
    (UNIV :$ _, SING :$ α :& m :& _) → do
      checkType γ ty α
      checkType γ α m
    (UNIV :$ _, UNIT :$ _) → return ()
    (UNIV :$ _, VOID :$ _) → return ()
    (PI :$ α :& xβ :& _, LAM :$ ye :& _) → do
      z ← fresh
      βz ← xβ // var z
      ez ← ye // var z
      checkType (γ >: (z,α)) βz ez
    (SING :$ α :& m :& _, _) → do
      α' ← nbeOpenT γ α
      checkType γ α' tm
      m' ← nbeOpen γ α m
      n' ← nbeOpen γ α tm
      unless (m' === n') $
        throwError $ NotEqual m' n'
    (UNIT :$ _, AX :$ _) → return ()
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
    _ → False

-- | Check the type of neutral terms.
--
checkTypeNe
  ∷ JUDGE v t m
  ⇒ Ctx v (t Z) -- ^ the context
  → t Z -- ^ the type
  → t Z -- ^ the neutral term
  → m ()
checkTypeNe γ ty tm = do
  ty' ← erase =<< infType γ tm
  unless (ty === ty') $
    throwError $ NotOfType ty tm

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
      α :& xβ :& RNil ← (out mty <&> preview (_ViewOp PI)) <!?> ExpectedPiType mty
      checkType γ α n
      nbeOpenT γ =<< xβ // n
    ABORT :$ α :& m :& _ → do
      checkType γ void m
      nbeOpenT γ α
    _ → throwError $ NotInferrable tm
