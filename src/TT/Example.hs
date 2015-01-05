{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UnicodeSyntax #-}

module TT.Example where

import TT.Operator
import TT.Model
import TT.Judge
import TT.Monad

import Abt.Concrete.LocallyNameless
import Abt.Class
import Control.Monad hiding (void)
import Control.Monad.Gen
import Data.Monoid
import Prelude hiding (pi)

test ∷ M e (Tm0 Op)
test = do
  x ← fresh
  nbe (pi void (x \\ void)) $ 
    lam (x \\ var x)

main ∷ IO ()
main = do
  str ← either fail return . runGenT . _M $ test >>= toString
  print str

  res ← either (const $ fail "error") return . runGenT . _M $ do
    checkType mempty unit (ax ∷ Tm0 Op)

    x ← fresh
    let
      f = lam (x \\ var x)
      g = lam (x \\ ax)
      ty = pi unit (x \\ unit)

    y ← fresh
    p ← fresh

    checkType mempty (eq ty ty f g) $ lam (x \\ lam (y \\ (lam (p \\ ax))))

        
  print res
