{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UnicodeSyntax #-}

module TT.Operator
( Op(..)
, pi
, sg
, lam
, (#)
, sing
, squash
, unit
, univ
, box
, ax
, void
, abort
, eq
, pair
, pi1
, pi2
, coe
, coh
, refl
, bool
, tt
, ff
, if'
) where

import Abt.Types.Nat
import Abt.Class

import Data.Typeable hiding (Refl)
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
  SQUASH ∷ Op '[Z]
  BOX ∷ Op '[Z]

  UNIT ∷ Op '[]
  AX ∷ Op '[]

  BOOL ∷ Op '[]
  TT ∷ Op '[]
  FF ∷ Op '[]
  IF ∷ Op '[S Z, Z, Z, Z]

  VOID ∷ Op '[]
  ABORT ∷ Op '[Z, Z]

  UNIV ∷ Op '[]

  EQ ∷ Op '[Z, Z, Z, Z]
  COE ∷ Op '[Z, Z, Z, Z]
  COH ∷ Op '[Z, Z, Z, Z]
  REFL ∷ Op '[Z, Z]

deriving instance Typeable Op

instance HEq1 Op where
  heq1 PI PI = Just Refl
  heq1 SG SG = Just Refl
  heq1 APP APP = Just Refl
  heq1 PAIR PAIR = Just Refl
  heq1 FST FST = Just Refl
  heq1 SND SND = Just Refl
  heq1 SING SING = Just Refl
  heq1 SQUASH SQUASH = Just Refl
  heq1 BOX BOX = Just Refl
  heq1 UNIT UNIT = Just Refl
  heq1 VOID VOID = Just Refl
  heq1 ABORT ABORT = Just Refl
  heq1 AX AX = Just Refl
  heq1 UNIV UNIV = Just Refl
  heq1 EQ EQ = Just Refl
  heq1 COE COE = Just Refl
  heq1 COH COH = Just Refl
  heq1 REFL REFL = Just Refl
  heq1 BOOL BOOL = Just Refl
  heq1 TT TT = Just Refl
  heq1 FF FF = Just Refl
  heq1 IF IF = Just Refl
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
    SQUASH → "squash"
    BOX → "box"
    VOID → "void"
    ABORT → "abort"
    UNIT → "unit"
    AX → "<>"
    EQ → "eq"
    UNIV → "univ"
    COE → "coe"
    COH → "coh"
    REFL → "refl"
    BOOL → "bool"
    TT → "tt"
    FF → "ff"
    IF → "if"

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

squash ∷ Abt v Op t ⇒ t Z → t Z
squash α = SQUASH $$ α :& RNil

box ∷ Abt v Op t ⇒ t Z → t Z
box m = BOX $$ m :& RNil

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

refl ∷ Abt v Op t ⇒ t Z → t Z → t Z
refl α m = REFL $$ α :& m :& RNil

bool ∷ Abt v Op t ⇒ t Z
bool = BOOL $$ RNil

tt ∷ Abt v Op t ⇒ t Z
tt = TT $$ RNil

ff ∷ Abt v Op t ⇒ t Z
ff = FF $$ RNil

if' ∷ Abt v Op t ⇒ t (S Z) → t Z → t Z → t Z → t Z
if' xα m t f = IF $$ xα :& m :& t :& f :& RNil
