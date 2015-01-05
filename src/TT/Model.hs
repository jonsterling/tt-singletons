{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UnicodeSyntax #-}

-- | We'll do normalization by evaluation in the manner of "A modular
-- type-checking algorithm for type theory with singleton types and proof
-- irrelevance" (Abel, Coquand, Pagano), where eta expansion occurs entirely
-- within the semantic model.
--
module TT.Model where

import TT.Context
import TT.Operator

import Abt.Class
import Abt.Types
import Control.Applicative
import Data.Vinyl
import qualified Data.Map as M
import Prelude hiding (pi)

-- | A semantic model with neutral terms
--
data D v
  = Pi (DT v) (D v → D v)
  | Lam (D v → D v)
  | App (D v) (D v)
  | Sing (DT v) (D v)
  | Unit
  | Void
  | Abort (DT v) (D v)
  | Ax
  | Univ
  | FV v

-- | Semantic types
--
type DT v = D v

-- | Reflection expands variables to enable new reductions
--
reflect ∷ DT v → D v → D v
reflect ty k =
  case ty of
    Pi α β → Lam $ \d → reflect (β d) (App k (reify α d))
    Sing _ m → m
    _ → k

-- | Reification expands the result of β-normalization to obtain η-long forms.
--
reify ∷ DT v → D v → D v
reify ty d =
  case ty of
    Univ → reifyT d
    Pi α β | Lam f ← d → Lam $ \e → reify (β $ reflect α e) (f $ reflect α e)
    Sing α m → reify α m
    _ → d

-- | Reification for types.
--
reifyT ∷ DT v → DT v
reifyT = \case
  Pi α β → Pi (reifyT α) $ \d → reifyT . β $ reflect α d
  Sing α m → Sing (reifyT α) $ reify α m
  d → d

-- | Quote a semantic value as a syntactic term.
--
quote
  ∷ ( MonadVar v m
    , Abt v Op t
    )
  ⇒ D v -- ^ semantic value
  → m (t Z) -- ^ a syntactic term
quote = \case
  Univ → pure univ
  Pi α β →
    pi <$> quote α <*> do
      x ← fresh
      (x \\) <$> quote (β (FV x))
  Sing α m → sing <$> quote α <*> quote m
  Unit → pure unit
  Void → pure void
  Abort α m → abort <$> quote α <*> quote m
  Lam f → lam <$> do
    x ← fresh
    (x \\) <$> quote (f (FV x))
  App m n → (#) <$> quote m <*> quote n
  Ax → pure ax
  FV v → pure $ var v

-- | Semantic environments map variables to values.
--
type Env v = M.Map v (D v)

-- | Extend an environemnt with a value.
--
extendEnv
  ∷ Ord v
  ⇒ Env v -- ^ an environment
  → v -- ^ a variable
  → D v -- ^ a value
  → Env v -- ^ the extended environment
extendEnv ρ x d = M.insert x d ρ

eval
  ∷ ( MonadVar v m
    , Abt v Op t
    )
  ⇒ t Z -- ^ a syntactic term
  → m (Env v → D v)
eval tm =
  out tm >>= \case
    UNIV :$ _ → return $ const Univ
    PI :$ α :& xβ :& _ → do
      α' ← eval α
      x :\ β ← out xβ
      β' ← eval β
      return $ \ρ →
        Pi (α' ρ) (β' . extendEnv ρ x)
    SING :$ α :& m :& _ → do
      α' ← eval α
      m' ← eval m
      return $ \ρ →
        Sing (α' ρ) (m' ρ)
    UNIT :$ _ → return $ const Unit
    VOID :$ _ → return $ const Void
    ABORT :$ α :& m :& _→ do
      α' ← eval α
      m' ← eval m
      return $ \ρ →
        Abort (α' ρ) (m' ρ)
    LAM :$ xe :& _ → do
      x :\ e ← out xe
      e' ← eval e
      return $ \ρ →
        Lam (e' . extendEnv ρ x)
    APP :$ m :& n :& _ → do
      m' ← eval m
      n' ← eval n
      return $ \ρ →
        case m' ρ of
          Lam f → f (n' ρ)
          _ → App (m' ρ) (n' ρ)
    AX :$ _ → return $ const Ax
    V v → return $ \ρ →
      case M.lookup v ρ of
        Just d → d
        Nothing → FV v

    _ → fail "Impossible, but GHC sucks"

-- | Normalize a closed term.
--
nbe
  ∷ ( MonadVar v m
    , Abt v Op t
    )
  ⇒ t Z -- ^ a syntactic type
  → t Z -- ^ a synctactic term
  → m (t Z) -- ^ a normalized syntactic term
nbe ty t = do
  ty' ← eval ty
  t' ← eval t
  quote $ reify (ty' M.empty) (t' M.empty)

-- | Normalize a closed type.
--
nbeT
  ∷ ( MonadVar v m
    , Abt v Op t
    )
  ⇒ t Z -- ^ a syntactic type
  → m (t Z) -- ^ a normalized syntactic type
nbeT ty = do
  ty' ← eval ty
  quote . reifyT $ ty' M.empty

-- | Mock up an environment where each syntactic variable is mapped to a
-- semantic variable.
--
envFromCtx
  ∷ Ctx v (t Z)
  → Env v
envFromCtx =
  M.mapWithKey (\k _ → FV k) .
    contextAsMap

-- | Normalize an open term.
--
nbeOpen
  ∷ ( MonadVar v m
    , Abt v Op t
    )
  ⇒ Ctx v (t Z) -- ^ a context
  → t Z -- ^ a syntactic type
  → t Z -- ^ a syntactic term
  → m (t Z) -- ^ a normalized syntactic term
nbeOpen γ ty t = do
  let ρ = envFromCtx γ
  ty' ← eval ty
  t' ← eval t
  quote $ reify (ty' ρ) (t' ρ)

-- | Normalize an open type.
--
nbeOpenT
  ∷  ( MonadVar v m
     , Abt v Op t
     )
  ⇒ Ctx v (t Z) -- ^ a context
  → t Z -- ^ a syntactic type
  → m (t Z) -- ^ a normalized syntactic type
nbeOpenT γ ty = do
  let ρ = envFromCtx γ
  ty' ← eval ty
  quote $ reifyT (ty' ρ)

