{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UnicodeSyntax #-}

module TT.Operator
( Op(..)
) where

import Abt.Types.Nat
import Abt.Class.HEq1
import Abt.Class.Show1

data Op arity where
  PI ∷ Op '[Z, S Z]
  LAM ∷ Op '[S Z]
  APP ∷ Op '[Z, Z]

  SING ∷ Op '[Z, Z]

  UNIT ∷ Op '[]
  AX ∷ Op '[]

  UNIV ∷ Op '[]

instance HEq1 Op where
  heq1 PI PI = Just Refl
  heq1 APP APP = Just Refl
  heq1 SING SING = Just Refl
  heq1 UNIT UNIT = Just Refl
  heq1 AX AX = Just Refl
  heq1 UNIV UNIV = Just Refl
  heq1 _ _ = Nothing

instance Show1 Op where
  show1 = \case
    PI → "pi"
    LAM → "lam"
    APP → "ap"
    SING → "sing"
    UNIT → "unit"
    AX → "<>"
    UNIV → "univ"

