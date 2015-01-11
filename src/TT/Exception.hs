{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UnicodeSyntax #-}

module TT.Exception where

import Abt.Class
import Abt.Types
import Abt.Concrete.LocallyNameless
import Control.Applicative
import Control.Monad
import Control.Monad.Catch
import Data.Traversable
import Data.Typeable

data DTm t =
  DTm
  { _dtmTerm ∷ !t 
  , _dtmString ∷ !String
  } deriving Typeable

instance Show (DTm t) where
  show = _dtmString
  
renderTerm
  ∷ ( Abt v o t
    , MonadVar v m
    )
  ⇒ t Z
  → m (DTm (t Z))
renderTerm tm = 
  DTm tm <$> toString tm

renderError
  ∷ ( Abt v o t
    , MonadVar v m
    , Traversable e
    )
  ⇒ e (t Z)
  → m (e (DTm (t Z)))
renderError = traverse renderTerm
  
throwTT
  ∷ ( MonadThrow m
    , MonadVar v m
    , Abt v o t
    , Traversable e
    , Exception (e (DTm (t Z)))
    )
  ⇒ e (t Z)
  → m α
throwTT = 
  renderError >=> throwM

deriving instance Typeable Var
deriving instance Typeable Z
deriving instance Typeable Tm
