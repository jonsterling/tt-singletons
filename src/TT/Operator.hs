{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UnicodeSyntax #-}

module TT.Operator
( Op(..)
, pi
, sg
, lam
, (#)
, sing
, unit
, univ
, ax
, void
, abort
, eq
, pair
, pi1
, pi2
, coe
, coh
) where

import Abt.Types.Nat
import Abt.Class

import Data.Vinyl
import Prelude hiding (pi, EQ)

data Op arity where
  PI ∷ Op '[Z, S Z]
  LAM ∷ Op '[S Z]
  APP ∷ Op '[Z, Z]

  SG ∷ Op '[Z, S Z]
  PAIR ∷ Op '[Z, Z]
  FST ∷ Op '[Z]
  SND ∷ Op '[Z]

  SING ∷ Op '[Z, Z]

  UNIT ∷ Op '[]
  AX ∷ Op '[]

  VOID ∷ Op '[]
  ABORT ∷ Op '[Z, Z]

  UNIV ∷ Op '[]

  EQ ∷ Op '[Z, Z, Z, Z]
  COE ∷ Op '[Z, Z, Z, Z]
  COH ∷ Op '[Z, Z, Z, Z]

instance HEq1 Op where
  heq1 PI PI = Just Refl
  heq1 SG SG = Just Refl
  heq1 APP APP = Just Refl
  heq1 PAIR PAIR = Just Refl
  heq1 FST FST = Just Refl
  heq1 SND SND = Just Refl
  heq1 SING SING = Just Refl
  heq1 UNIT UNIT = Just Refl
  heq1 VOID VOID = Just Refl
  heq1 ABORT ABORT = Just Refl
  heq1 AX AX = Just Refl
  heq1 UNIV UNIV = Just Refl
  heq1 EQ EQ = Just Refl
  heq1 COE COE = Just Refl
  heq1 COH COH = Just Refl
  heq1 _ _ = Nothing

instance Show1 Op where
  show1 = \case
    PI → "pi"
    SG → "sg"
    LAM → "lam"
    APP → "ap"
    PAIR → "pair"
    FST → "fst"
    SND → "snd"
    SING → "sing"
    VOID → "void"
    ABORT → "abort"
    UNIT → "unit"
    AX → "<>"
    EQ → "eq"
    UNIV → "univ"
    COE → "coe"
    COH → "coh"

pi ∷ Abt v Op t ⇒ t Z → t (S Z) → t Z
pi α xβ = PI $$ α :& xβ :& RNil

sg ∷ Abt v Op t ⇒ t Z → t (S Z) → t Z
sg α xβ = SG $$ α :& xβ :& RNil

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

pair ∷ Abt v Op t ⇒ t Z → t Z → t Z
pair m n = PAIR $$ m :& n :& RNil

pi1 ∷ Abt v Op t ⇒ t Z → t Z
pi1 m = FST $$ m :& RNil

pi2 ∷ Abt v Op t ⇒ t Z → t Z
pi2 m = SND $$ m :& RNil

eq ∷ Abt v Op t ⇒ t Z → t Z → t Z → t Z → t Z
eq α β m n = EQ $$ α :& β :& m :& n :& RNil

coe ∷ Abt v Op t ⇒ t Z → t Z → t Z → t Z → t Z
coe α β p m = COE $$ α :& β :& p :& m :& RNil

coh ∷ Abt v Op t ⇒ t Z → t Z → t Z → t Z → t Z
coh α β p m = COH $$ α :& β :& p :& m :& RNil
