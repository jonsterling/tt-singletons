{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

module TT.Example where

import TT.Operator
import TT.Judge
import TT.Monad

import Abt.Concrete.LocallyNameless
import Abt.Class
import Control.Monad hiding (void)
import Control.Monad.Gen
import Data.Monoid
import Prelude hiding (pi)

main ∷ IO ()
main = do
  res ← either (const $ fail "error") return . runGenT . _M $ do
    _ ← checkType mempty unit (ax ∷ Tm0 Op)

    x ← fresh
    let
      f = lam (x \\ var x)
      g = lam (x \\ ax)
      ty = pi unit (x \\ unit)

    toString =<< checkType mempty (eq ty ty f g) (refl ty f)

        
  print res
