{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UnicodeSyntax #-}

module TT.Operator
( Op(..)
, pi
, lam
, (#)
, sing
, unit
, univ
, ax
, void
, abort
) where

import Abt.Types.Nat
import Abt.Class

import Data.Vinyl
import Prelude hiding (pi)

data Op arity where
  PI ∷ Op '[Z, S Z]
  LAM ∷ Op '[S Z]
  APP ∷ Op '[Z, Z]

  SING ∷ Op '[Z, Z]

  UNIT ∷ Op '[]
  AX ∷ Op '[]

  VOID ∷ Op '[]
  ABORT ∷ Op '[Z, Z]

  UNIV ∷ Op '[]

instance HEq1 Op where
  heq1 PI PI = Just Refl
  heq1 APP APP = Just Refl
  heq1 SING SING = Just Refl
  heq1 UNIT UNIT = Just Refl
  heq1 VOID VOID = Just Refl
  heq1 ABORT ABORT = Just Refl
  heq1 AX AX = Just Refl
  heq1 UNIV UNIV = Just Refl
  heq1 _ _ = Nothing

instance Show1 Op where
  show1 = \case
    PI → "pi"
    LAM → "lam"
    APP → "ap"
    SING → "sing"
    VOID → "void"
    ABORT → "abort"
    UNIT → "unit"
    AX → "<>"
    UNIV → "univ"

pi ∷ Abt v Op t ⇒ t Z → t (S Z) → t Z
pi α xβ = PI $$ α :& xβ :& RNil

lam ∷ Abt v Op t ⇒ t (S Z) → t Z
lam xe = LAM $$ xe :& RNil

(#) ∷ Abt v Op t ⇒ t Z → t Z → t Z
m # n = APP $$ m :& n :& RNil
infixl 3 #

sing ∷ Abt v Op t ⇒ t Z → t Z → t Z
sing α m = SING $$ α :& m :& RNil

unit ∷ Abt v Op t ⇒ t Z
unit = UNIT $$ RNil

void ∷ Abt v Op t ⇒ t Z
void = VOID $$ RNil

abort ∷ Abt v Op t ⇒ t Z → t Z → t Z
abort α m = ABORT $$ α :& m :& RNil

univ ∷ Abt v Op t ⇒ t Z
univ = UNIV $$ RNil

ax ∷ Abt v Op t ⇒ t Z
ax = AX $$ RNil
