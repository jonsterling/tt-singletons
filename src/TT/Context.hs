{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UnicodeSyntax #-}

module TT.Context
( Ctx
, CtxError(..)
, IsCtxError(..)
, contextAsMap
, containsLocal
) where

import Control.Lens
import Control.Monad.Error.Class
import qualified Data.Map as M
import Data.Monoid

newtype Ctx v ty
  = Ctx
  { _ctx ∷ M.Map v ty
  } deriving Monoid

data CtxError v ty
  = VariableNotFound v

class IsCtxError v ty e | e → v ty where
  _CtxError ∷ Prism' e (CtxError v ty)

contextAsMap
  ∷ Ctx v ty
  → M.Map v ty
contextAsMap = _ctx

containsLocal
  ∷ ( MonadError e m
    , IsCtxError v ty e
    , Ord v
    )
  ⇒ Ctx v ty
  → v
  → m ty
containsLocal (Ctx ctx) v =
  case M.lookup v ctx of
    Just ty → return ty
    Nothing → throwError $ _CtxError # VariableNotFound v

