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
import Prelude hiding (pi, EQ)

-- | A semantic model with neutral terms
--
data D v
  = Pi (DT v) (D v → D v)
  | Lam (D v → D v)
  | App (D v) (D v)
  | Sg (DT v) (D v → D v)
  | Pair (D v) (D v)
  | Fst (D v)
  | Snd (D v)
  | Sing (DT v) (D v)
  | Unit
  | Void
  | Abort (DT v) (D v)
  | Ax
  | Univ
  | Equal (DT v) (DT v) (D v) (D v)
  | FV v
  | Coe (DT v) (DT v) (D v) (D v)
  | Coh (DT v) (DT v) (D v) (D v)

-- | Perform application if possible
--
doApp
  ∷ D v
  → D v
  → D v
doApp (Lam f) m = f m
doApp m n = App m n

-- | Project the first component of a pair if possible
--
doFst
  ∷ D v
  → D v
doFst (Pair m _) = m
doFst m = Fst m

-- | Project the second component of a pair if possible
--
doSnd
  ∷ D v
  → D v
doSnd (Pair _ m) = m
doSnd m = Snd m

-- | Whether a semantic term is canonical
--
canon
  ∷ D v
  → Bool
canon = \case
  Pi _ _ → True
  Lam _ → True
  Sg _ _ → True
  Pair _ _ → True
  Sing _ _ → True
  Unit  → True
  Void  → True
  Ax → True
  Univ → True
  _ → False
  
-- | Semantic types
--
type DT v = D v

-- | Reflection expands variables to enable new reductions
--
reflect ∷ DT v → D v → D v
reflect ty k =
  case ty of
    Pi α β → Lam $ \d → reflect (β d) (App k (reify α d))
    Sg α β →
      let
        l = reflect α (Fst k)
        r = reflect (β l) (Snd k)
      in
       Pair l r
    Unit → Ax
    Sing _ m → m
    _ → k

-- | Reification expands the result of β-normalization to obtain η-long forms.
--
reify ∷ DT v → D v → D v
reify ty d =
  case ty of
    Univ → reifyT d
    Pi α β | Lam f ← d → Lam $ \e → reify (β $ reflect α e) (f $ reflect α e)
    Sg α β | Pair m n ← d →
      let
        l = reify α m
        r = reify (β l) n
      in
       Pair l r
    Sing α m → reify α m
    Unit → Ax
    _ → d

-- | Reification for types.
--
reifyT ∷ DT v → DT v
reifyT = \case
  Pi α β → Pi (reifyT α) $ \d → reifyT . β $ reflect α d
  Sg α β → Sg (reifyT α) $ \d → reifyT . β $ reflect α d
  Sing α m → Sing (reifyT α) $ reify α m
  Equal α β m n → Equal (reifyT α) (reifyT β) (reify α m) (reify β n)
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
  Sg α β →
    sg <$> quote α <*> do
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
  Pair m n → pair <$> quote m <*> quote n
  Fst m → pi1 <$> quote m
  Snd m → pi2 <$> quote m
  Ax → pure ax
  Equal α β m n → eq <$> quote α <*> quote β <*> quote m <*> quote n
  Coe α β p m → coe <$> quote α <*> quote β <*> quote p <*> quote m
  Coh α β p m → coh <$> quote α <*> quote β <*> quote p <*> quote m
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
    SG :$ α :& xβ :& _ → do
      α' ← eval α
      x :\ β ← out xβ
      β' ← eval β
      return $ \ρ →
        Sg (α' ρ) (β' . extendEnv ρ x)
    SING :$ α :& m :& _ → do
      α' ← eval α
      m' ← eval m
      return $ \ρ →
        Sing (α' ρ) (m' ρ)
    UNIT :$ _ → return $ const Unit
    VOID :$ _ → return $ const Void
    EQ :$ α :& β :& m :& n :& _→ do
      α' ← eval α
      β' ← eval β
      m' ← eval m
      n' ← eval n
      return $ \ρ →
        case (α' ρ, β' ρ, m' ρ, n' ρ) of
          (Univ, Univ, Univ, Univ) → Unit
          (Univ, Univ, Void, Void) → Unit
          (Univ, Univ, Unit, Unit) → Unit
          (Univ, Univ, Pi σ τ, Pi σ' τ') →
            Sg (Equal Univ Univ σ' σ) $ \_ →
              Pi σ $ \s → Pi σ' $ \s' →
                Pi (Equal σ σ' s s') $ \_ →
                  Equal Univ Univ (τ s) (τ' s')
          (Univ, Univ, Sg σ τ, Sg σ' τ') →
            Sg (Equal Univ Univ σ σ') $ \_ →
              Pi σ $ \s → Pi σ' $ \s' →
                Pi (Equal σ σ' s s') $ \_ →
                  Equal Univ Univ (τ s) (τ' s')
          (Univ, Univ, Sing σ s, Sing σ' s') →
            Equal σ σ' s s'
          (Univ, Univ, m'', n'') | canon m'' && canon n'' → Void
          (Void, Void, _, _) → Unit
          (Unit, Unit, _, _) → Unit
          (Pi σ τ, Pi σ' τ', f, g) →
            Pi σ $ \s → Pi σ' $ \s' →
              Pi (Equal σ σ' s s') $ \_ →
                Equal (τ s) (τ' s') (doApp f s) (doApp g s')
          (Sg σ τ, Sg σ' τ', p, q) →
            Sg (Equal σ σ' (doFst p) (doFst q)) $ \_ →
              Equal (τ (doFst p)) (τ' (doFst q)) (doSnd p) (doSnd q)
          (Sing σ s, Sing σ' s', _, _) → Equal σ σ' s s'
          (α'', β'', m'', n'')
            | canon α'' && canon β'' → Void
            | otherwise → Equal α'' β'' m'' n''
    COE :$ α :& β :& q :& m :& _ → do
      α' ← eval α
      β' ← eval β
      q' ← eval q
      m' ← eval m
      return $ \ρ → 
        case (α' ρ, β' ρ, q' ρ, m' ρ) of
          (Univ, Univ, _, m'') → m''
          (Void, Void, _, m'') → m''
          (Unit, Unit, _, m'') → m''
          (Sg σ τ, Sg σ' τ', q'', m'') →
            let
              s0 = doFst m''
              t0 = doSnd m''
              qσ = doFst q''
              qτ = doApp (doApp (doApp (doSnd q'') s0) s1) (Coh σ σ' qσ s0)
              s1 = Coe σ σ' qσ s0
              t1 = Coe (τ s0) (τ' s1) qτ t0
            in
             Pair s1 t1
          (Pi σ τ, Pi σ' τ', q'', m'') →
            Lam $ \s1 →
              let
                qσ = doFst q''
                qτ = doApp (doApp (doApp (doSnd q'') s1) s0) (Coh σ' σ qσ s1)
                s0 = Coe σ σ' qσ s1
                t0 = App m'' s0
              in
                Coe (τ s0) (τ' s1) qτ t0
          (Sing _ _, Sing _ s', _, _) → s'
          (α'', β'', q'', m'')
            | canon α'' && canon β'' → Abort β'' q''
            | otherwise → Coe α'' β'' q'' m''
    COH :$ α :& β :& q :& m :& _ → do
      α' ← eval α
      β' ← eval β
      q' ← eval q
      m' ← eval m
      return $ \ρ →
        Coh (α' ρ) (β' ρ) (q' ρ) (m' ρ)
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
      return $ \ρ → doApp (m' ρ) (n' ρ)
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
  ∷ ( MonadVar v m
    , Abt v Op t
    )
  ⇒ Ctx v (t Z) -- ^ a context
  → t Z -- ^ a syntactic type
  → m (t Z) -- ^ a normalized syntactic type
nbeOpenT γ ty = do
  let ρ = envFromCtx γ
  ty' ← eval ty
  quote $ reifyT (ty' ρ)

