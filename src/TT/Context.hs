{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UnicodeSyntax #-}

module TT.Context
( Ctx
, CtxError(..)
, contextAsMap
, containsLocal
, (>:)
) where

import Control.Monad.Catch
import qualified Data.Map as M
import Data.Monoid
import Data.Typeable

newtype Ctx v ty
  = Ctx
  { _ctx ∷ M.Map v ty
  } deriving Monoid

data CtxError v
  = VariableNotFound v
  deriving (Eq, Show, Typeable)

instance (Show v, Typeable v) ⇒ Exception (CtxError v)

contextAsMap
  ∷ Ctx v ty
  → M.Map v ty
contextAsMap = _ctx

containsLocal
  ∷ ( MonadThrow m
    , Ord v
    , Typeable v
    , Show v
    )
  ⇒ Ctx v ty
  → v
  → m ty
containsLocal (Ctx ctx) v =
  case M.lookup v ctx of
    Just ty → return ty
    Nothing → throwM $ VariableNotFound v

(>:)
  ∷ Ord v
  ⇒ Ctx v ty
  → (v, ty)
  → Ctx v ty
Ctx γ >: (x,t) = Ctx $ M.insert x t γ
