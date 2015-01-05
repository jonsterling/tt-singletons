{-# LANGUAGE UnicodeSyntax #-}

module TT.Example where

import TT.Operator
import TT.Model
import TT.Monad

import Abt.Concrete.LocallyNameless
import Abt.Class
import Control.Monad.Gen
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
