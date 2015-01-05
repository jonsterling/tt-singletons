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
    SG :$ α :& xβ :& _ → do
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
    (SG :$ α :& xβ :& _, PAIR :$ m :& n :& _) → do
      checkType γ α m
      βm ← nbeOpenT γ =<< xβ // m
      checkType γ βm n
    (SING :$ α :& m :& _, _) → do
      α' ← nbeOpenT γ α
      checkType γ α' tm
      m' ← nbeOpen γ α m
      n' ← nbeOpen γ α tm
      unless (m' === n') $
        throwError $ NotEqual m' n'
    (UNIT :$ _, AX :$ _) → return ()
    (EQ :$ α :& β :& m :& n :& _, AX :$ _) → do
      checkType γ α m
      checkType γ β n
      unless (α === β) $
        unless (m === n) $
          throwError $ NotEqual m n
    (EQ :$ α :& β :& m :& n :& _, _) → do
      prfTy ← computeEq γ (α, β, m, n)
      checkType γ prfTy tm
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
      α :& xβ :& _ ← (out mty <&> preview (_ViewOp PI)) <!?> ExpectedPiType mty
      checkType γ α n
      nbeOpenT γ =<< xβ // n
    FST :$ m :& _ → do
      mty ← erase =<< infType γ m
      α :& _ ← (out mty <&> preview (_ViewOp SG)) <!?> ExpectedSgType mty
      return α
    SND :$ m :& _ → do
      mty ← erase =<< infType γ m
      _ :& xβ :& _ ← (out mty <&> preview (_ViewOp SG)) <!?> ExpectedSgType mty
      nbeOpenT γ =<< xβ // pi1 m
    ABORT :$ α :& m :& _ → do
      checkType γ void m
      nbeOpenT γ α
    _ → throwError $ NotInferrable tm


-- | Given a tuple (α,β,m,n) compute the type of proofs of m:α=n:β.
--
computeEq
  ∷ JUDGE v t m
  ⇒ Ctx v (t Z)
  → (t Z, t Z, t Z, t Z)
  → m (t Z)
computeEq γ (α, β, m, n) = do
  (,,,)
    <$> (out =<< nbeOpenT γ α)
    <*> (out =<< nbeOpenT γ β)
    <*> (out =<< nbeOpen γ α m)
    <*> (out =<< nbeOpen γ β n)
  >>= \case
    (UNIV :$ _, UNIV :$ _, UNIV :$ _, UNIV :$ _) → pure unit
    (UNIV :$ _, UNIV :$ _, UNIT :$ _, UNIT :$ _) → pure unit
    (UNIV :$ _, UNIV :$ _, VOID :$ _, VOID :$ _) → pure unit
    (UNIV :$ _, UNIV :$ _, PI :$ φ :& xψ :& _, PI :$ φ' :& yψ' :& _) → do
      v ← fresh
      x ← fresh
      y ← fresh
      p ← fresh
      ψx ← xψ // var x
      ψ'y ← yψ' // var y
      let
        φφ' = eq univ univ φ φ'
        xy = eq φ φ' (var x) (var y)
        ψψ' = eq univ univ ψx ψ'y

      pure $ sg φφ' (v \\ pi φ (x \\ pi φ' (y \\ pi xy (p \\ ψψ'))))

    (UNIV :$ _, UNIV :$ _, SG :$ φ :& xψ :& _, SG :$ φ' :& yψ' :& _) → do
      v ← fresh
      x ← fresh
      y ← fresh
      p ← fresh

      ψx ← nbeOpenT γ =<< xψ // var x
      ψ'y ← nbeOpenT γ =<< yψ' // var y

      let
        φφ' = eq univ univ φ φ'
        xy = eq φ φ' (var x) (var y)
        ψxψ'y = eq univ univ ψx ψ'y

      pure $ sg φφ' (v \\ pi φ (x \\ pi φ' (y \\ pi xy (p \\ ψxψ'y))))

    (VOID :$ _, VOID :$ _, _, _) → pure unit
    (UNIT :$ _, UNIT :$ _, _, _) → pure unit
    (EQ :$ _, EQ :$ _, _, _) → pure unit

    (PI :$ φ :& xψ :& _, PI :$ φ' :& yψ' :& _, LAM :$ xf :& _, LAM :$ yg :& _) → do
      x ← fresh
      y ← fresh
      p ← fresh

      ψx ← nbeOpenT γ =<< xψ // var x
      ψ'y ← nbeOpenT γ =<< yψ' // var y

      fx ← nbeOpen γ ψx =<< xf // var x
      fy ← nbeOpen γ ψ'y =<< yg // var y

      let
        xy = eq φ φ' (var x) (var y)
        fxgy = eq ψx ψ'y fx fy

      pure $ pi φ (x \\ pi φ' (y \\ pi xy (p \\ fxgy)))

    (SG :$ φ :& xψ :& _, SG :$ φ' :& yψ' :& _, PAIR :$ l :& r :& _, PAIR :$ l' :& r' :& _) → do
      p ← fresh
      ψl ← nbeOpenT γ =<< xψ // l
      ψ'l' ← nbeOpenT γ =<< yψ' // l'
      pure $ sg (eq φ φ' l l') $ p \\ eq ψl ψ'l' r r'

    (α', β', m', n') →
      pure $ eq (into α') (into β') (into m') (into n')

