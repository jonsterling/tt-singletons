{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UnicodeSyntax #-}

module TT.Monad
( MT
, runMT
) where

import Abt.Class
import Abt.Concrete.LocallyNameless
import Control.Applicative
import Control.Monad.Catch
import Control.Monad.Trans
import Control.Monad.Trans.State

newtype MT m α
  = MT
  { _runMT ∷ StateT Int m α
  } deriving (Functor, Applicative, Monad, MonadIO, MonadThrow, MonadCatch)

runMT
  ∷ Monad m
  ⇒ MT m α
  → m α
runMT = flip evalStateT 0 . _runMT 

gen
  ∷ ( Monad m
    , Functor m
    )
  ⇒ StateT Int m Int
gen = do
  i ← (+1) <$> get
  put i
  return i

instance (Functor m, Monad m) ⇒ MonadVar Var (MT m) where
  fresh = MT $ Var Nothing <$> gen
  named str = MT $ Var (Just str) <$> gen
