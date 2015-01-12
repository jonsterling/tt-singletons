{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

module TT.Example where

import TT.Operator
import TT.Judge
import TT.Context
import TT.Monad

import Abt.Concrete.LocallyNameless
import Abt.Class
import Control.Monad hiding (void)
import Control.Monad.Trans
import Data.Monoid
import Prelude hiding (pi)


printTerm
  ∷ ( MonadIO m
    , MonadVar Var m
    )
  ⇒ Tm0 Op
  → m ()
printTerm =
  toString >=> liftIO . print
   

main ∷ IO ()
main = do
  runMT $ do
    printTerm =<< checkType mempty unit ax

    x ← fresh
    let
      f = lam (x \\ var x)
      g = lam (x \\ ax)
      ty = pi unit (x \\ unit)

    printTerm =<< 
      checkType mempty (eq ty ty f g) (refl ty f)

    z ← fresh

    do
      let
        plus α β = sg bool $ x \\ if' (z \\ univ) (var x) (var α) (var β)
        inl m = pair tt m
        inr m = pair ff m

      α ← fresh
      β ← fresh
      m ← fresh
      let
        γ = mempty >: (α, univ) >: (β, univ)
  
      printTerm =<< isType γ (plus α β) 
      printTerm =<< checkType (γ >: (m, var α)) (plus α β) (inl (var m))
      printTerm =<< checkType (γ >: (m, var β)) (plus α β) (inr (var m))
