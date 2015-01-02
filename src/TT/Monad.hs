{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UnicodeSyntax #-}

module TT.Monad where

import Abt.Class
import Abt.Concrete.LocallyNameless
import Control.Applicative
import Control.Monad.Error.Class
import Control.Monad.Gen

newtype M e α
  = M
  { _M ∷ GenT Int (Either e) α
  } deriving (Functor, Applicative, Monad, MonadError e)

instance MonadVar Var (M e) where
  fresh = M $ Var Nothing <$> gen
  named str = M $ Var (Just str) <$> gen

