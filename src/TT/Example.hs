{-# LANGUAGE UnicodeSyntax #-}

module TT.Example where

import TT.Operator
import TT.Model
import TT.Monad

import Abt.Concrete.LocallyNameless
import Abt.Class
import Control.Monad.Gen

test ∷ M e (Tm0 Op)
test = nbe unit =<< do
  x ← fresh
  return $
    lam (x \\ var x) # ax

main ∷ IO ()
main = do
  str ← either fail return . runGenT . _M $ test >>= toString
  print str

