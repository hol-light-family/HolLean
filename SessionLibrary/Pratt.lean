/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/pratt.ml.                             -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Pratt.lean

  The session half of the pratt.ml translation: it supplies
  HolLibrary.Pratt's dependencies from Session and SessionLibrary.Prime, and
  exports every name under its HOL Light name.  Importing this module is
  `needs "Library/pratt.ml"`; its `needs "Library/prime.ml"` is the import of
  SessionLibrary.Prime.  The bundles are built by `initialize` when the
  module is loaded, in file order.
-/

import Session
import HolLibrary.Pratt
import SessionLibrary.Prime

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Pratt

/-- The core theorems pratt.ml uses. -/
def core1 : HolLibrary.Pratt.CoreThms1 where
  ADD_AC := Session.ADD_AC
  ADD_ASSOC := Session.ADD_ASSOC
  ADD_CLAUSES := Session.ADD_CLAUSES
  ALL := Session.listDefs.ALL
  ALL_IMP := Session.listThms1.ALL_IMP
  ARITH := Session.ARITH
  BEZOUT := SessionLibrary.Prime.«BEZOUT»
  BIT0 := Session.BIT0
  BIT1 := Session.BIT1
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARD_NUMSEG_LE := Session.CARD_NUMSEG_LE
  CARD_NUMSEG_LT := Session.CARD_NUMSEG_LT
  CARD_SUBSET := Session.CARD_SUBSET
  CARD_SUBSET_EQ := Session.CARD_SUBSET_EQ
  CONG := Session.CONG
  CONJ_ASSOC := Session.CONJ_ASSOC
  COPRIME_0 := SessionLibrary.Prime.«COPRIME_0»
  COPRIME_1 := SessionLibrary.Prime.«COPRIME_1»
  COPRIME_DIVPROD := SessionLibrary.Prime.«COPRIME_DIVPROD»
  COPRIME_EXP := SessionLibrary.Prime.«COPRIME_EXP»
  COPRIME_LMOD := Session.COPRIME_LMOD
  COPRIME_MUL := SessionLibrary.Prime.«COPRIME_MUL»
  COPRIME_REFL := SessionLibrary.Prime.«COPRIME_REFL»
  COPRIME_SYM := SessionLibrary.Prime.«COPRIME_SYM»
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DIVIDES_ADD := SessionLibrary.Prime.«DIVIDES_ADD»
  DIVIDES_ADD_REVR := SessionLibrary.Prime.«DIVIDES_ADD_REVR»
  DIVIDES_EXP := SessionLibrary.Prime.«DIVIDES_EXP»
  DIVIDES_EXP2 := SessionLibrary.Prime.«DIVIDES_EXP2»
  DIVIDES_LE := Session.DIVIDES_LE
  DIVIDES_LMUL := SessionLibrary.Prime.«DIVIDES_LMUL»
  DIVIDES_ONE := Session.DIVIDES_ONE
  DIVIDES_REFL := SessionLibrary.Prime.«DIVIDES_REFL»
  DIVIDES_RMUL := SessionLibrary.Prime.«DIVIDES_RMUL»
  DIVIDES_SUB := SessionLibrary.Prime.«DIVIDES_SUB»
  DIVIDES_ZERO := SessionLibrary.Prime.«DIVIDES_ZERO»
  DIVISION := Session.DIVISION
  DIV_MULT := Session.DIV_MULT
  DIV_UNIQ := Session.DIV_UNIQ
  EQ_TRANS := Session.EQ_TRANS
  EXP := Session.EXP
  EXP_ADD := Session.EXP_ADD
  EXP_EQ_1 := Session.EXP_EQ_1
  EXP_EXP := Session.EXP_EXP
  EXP_ONE := Session.EXP_ONE
  EXTENSION := Session.EXTENSION
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_NUMSEG_LE := Session.FINITE_NUMSEG_LE
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_RECURSION := Session.FINITE_RECURSION
  FINITE_RULES := Session.FINITE_RULES
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_AND_THM := Session.FORALL_AND_THM
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_0 := Session.HAS_SIZE_0
  IMAGE := Session.IMAGE
  IMAGE_CLAUSES := Session.IMAGE_CLAUSES
  IMP_CONJ := Session.IMP_CONJ
  IMP_IMP := Session.IMP_IMP
  INT_OF_NUM_SUB := Session.INT_OF_NUM_SUB
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_SING := Session.IN_SING
  ITLIST := Session.listDefs.ITLIST
  LEFT_ADD_DISTRIB := Session.LEFT_ADD_DISTRIB
  LEFT_SUB_DISTRIB := Session.LEFT_SUB_DISTRIB
  LE_0 := Session.LE_0
  LE_ANTISYM := Session.LE_ANTISYM
/-- The core theorems pratt.ml uses. -/
def core2 : HolLibrary.Pratt.CoreThms2 where
  LE_CASES := Session.LE_CASES
  LE_LT := Session.LE_LT
  LE_MULT_LCANCEL := Session.LE_MULT_LCANCEL
  LE_TRANS := Session.LE_TRANS
  LT := Session.LT
  LT_IMP_LE := Session.LT_IMP_LE
  LT_LE := Session.LT_LE
  LT_MULT_RCANCEL := Session.LT_MULT_RCANCEL
  LT_NZ := Session.LT_NZ
  LT_REFL := Session.LT_REFL
  LT_TRANS := Session.LT_TRANS
  MEM := Session.listDefs.MEM
  MOD_EQ_0 := Session.MOD_EQ_0
  MOD_EXP_MOD := Session.MOD_EXP_MOD
  MOD_LT := Session.MOD_LT
  MOD_MOD_REFL := Session.MOD_MOD_REFL
  MOD_MULT_LMOD := Session.MOD_MULT_LMOD
  MOD_MULT_RMOD := Session.MOD_MULT_RMOD
  MOD_UNIQ := Session.MOD_UNIQ
  MULT_AC := Session.MULT_AC
  MULT_ASSOC := Session.MULT_ASSOC
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_EQ_0 := Session.MULT_EQ_0
  MULT_SYM := Session.MULT_SYM
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NOT_LE := Session.NOT_LE
  NOT_LT := Session.NOT_LT
  NUMERAL := Session.NUMERAL
  PRIME_0 := SessionLibrary.Prime.«PRIME_0»
  PRIME_1 := SessionLibrary.Prime.«PRIME_1»
  PRIME_2 := SessionLibrary.Prime.«PRIME_2»
  PRIME_COPRIME := SessionLibrary.Prime.«PRIME_COPRIME»
  PRIME_DIVPROD := SessionLibrary.Prime.«PRIME_DIVPROD»
  PRIME_FACTOR := SessionLibrary.Prime.«PRIME_FACTOR»
  RIGHT_ADD_DISTRIB := Session.RIGHT_ADD_DISTRIB
  RIGHT_SUB_DISTRIB := Session.RIGHT_SUB_DISTRIB
  SUBSET := Session.SUBSET
  SUB_EQ_0 := Session.SUB_EQ_0
  SWAP_EXISTS_THM := Session.SWAP_EXISTS_THM
  cong := Session.cong
  coprime := Session.coprime
  divides := Session.divides
  num_WF := Session.num_WF
  num_WOP := Session.num_WOP
  num_congruent := Session.num_congruent
  num_divides := Session.num_divides
  prime := Session.prime
/-- The core theorems pratt.ml uses. -/
def core3 : HolLibrary.Pratt.CoreThms3 where
/-- The core theorems pratt.ml uses. -/
def core4 : HolLibrary.Pratt.CoreThms4 where

/-- What pratt.ml uses from Session. -/
def deps : HolLibrary.Pratt.PrattDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  prioritize_num := do
    match ← HolCore.Kernel.mk_type "num" [] with
    | .ok ty => Session.prioritize_overload ty
    | .error e => throw (IO.userError e)
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  INTEGER_RULE t := ExceptT.mk (Session.INTEGER_RULE t)
  NUMBER_RULE t := ExceptT.mk (Session.NUMBER_RULE t)
  NUMBER_TAC := Session.NUMBER_TAC
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  LIST_INDUCT_TAC := Session.LIST_INDUCT_TAC
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  let_CONV := Session.let_CONV
  NUM_EQ_CONV := Session.NUM_EQ_CONV
  NUM_LE_CONV := Session.NUM_LE_CONV
  NUM_SUB_CONV := Session.NUM_SUB_CONV
  NUM_MULT_CONV := Session.NUM_MULT_CONV
  NUM_DIV_CONV := Session.NUM_DIV_CONV
  mk_numeral := Session.mk_numeral
  mk_small_numeral := Session.mk_small_numeral
  mk_flist := Session.mk_flist
  core1 := core1
  core2 := core2
  core3 := core3
  core4 := core4

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} (name : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in pratt.ml order. -/
initialize BCompat : HolLibrary.Pratt.Compat ←
  ioB "setupCompat" (HolLibrary.Pratt.setupCompat deps).run
initialize BCong : HolLibrary.Pratt.Cong ←
  ioB "setupCong" (HolLibrary.Pratt.setupCong deps BCompat).run
initialize BPhi : HolLibrary.Pratt.Phi ←
  ioB "setupPhi" (HolLibrary.Pratt.setupPhi deps BCompat).run
initialize BFermat : HolLibrary.Pratt.Fermat ←
  ioB "setupFermat" (HolLibrary.Pratt.setupFermat deps BCompat BCong BPhi).run
initialize BLucas : HolLibrary.Pratt.Lucas ←
  ioB "setupLucas" (HolLibrary.Pratt.setupLucas deps BCong BPhi BFermat).run
initialize BPrimefact : HolLibrary.Pratt.Primefact ←
  ioB "setupPrimefact" (HolLibrary.Pratt.setupPrimefact deps BLucas).run
initialize BCertify : HolLibrary.Pratt.Certify ←
  ioB "setupCertify" (HolLibrary.Pratt.setupCertify deps BPrimefact).run

-- Compat
def nat_mod_lemma : thm := BCompat.nat_mod_lemma
def nat_mod : thm := BCompat.nat_mod
def PRIME : thm := BCompat.PRIME
def FINITE_NUMBER_SEGMENT : thm := BCompat.FINITE_NUMBER_SEGMENT

-- Cong
def CONG_MOD_0 : thm := BCong.CONG_MOD_0
def CONG_MOD_1 : thm := BCong.CONG_MOD_1
def CONG_0 : thm := BCong.CONG_0
def CONG_SUB_CASES : thm := BCong.CONG_SUB_CASES
def CONG_MULT_LCANCEL : thm := BCong.CONG_MULT_LCANCEL
def CONG_REFL : thm := BCong.CONG_REFL
def CONG_SYM : thm := BCong.CONG_SYM
def CONG_TRANS : thm := BCong.CONG_TRANS

-- Phi
def phi : thm := BPhi.phi
def PHI_ALT : thm := BPhi.PHI_ALT
def PHI_ANOTHER : thm := BPhi.PHI_ANOTHER
def PHI_LIMIT : thm := BPhi.PHI_LIMIT
def PHI_LIMIT_STRONG : thm := BPhi.PHI_LIMIT_STRONG
def PHI_0 : thm := BPhi.PHI_0
def PHI_1 : thm := BPhi.PHI_1
def PHI_LOWERBOUND_1_STRONG : thm := BPhi.PHI_LOWERBOUND_1_STRONG
def PHI_LOWERBOUND_1 : thm := BPhi.PHI_LOWERBOUND_1
def PHI_LOWERBOUND_2 : thm := BPhi.PHI_LOWERBOUND_2
def PHI_PRIME_EQ : thm := BPhi.PHI_PRIME_EQ
def PHI_PRIME : thm := BPhi.PHI_PRIME

-- Fermat
def DIFFERENCE_POS_LEMMA : thm := BFermat.DIFFERENCE_POS_LEMMA
def ITSET_MODMULT : thm := BFermat.ITSET_MODMULT
def ITSET_MODMULT_COPRIME : thm := BFermat.ITSET_MODMULT_COPRIME
def FERMAT_LITTLE : thm := BFermat.FERMAT_LITTLE
def FERMAT_LITTLE_PRIME : thm := BFermat.FERMAT_LITTLE_PRIME

-- Lucas
def LUCAS_COPRIME_LEMMA : thm := BLucas.LUCAS_COPRIME_LEMMA
def LUCAS_WEAK : thm := BLucas.LUCAS_WEAK
def LUCAS : thm := BLucas.LUCAS

-- Primefact
def primefact : thm := BPrimefact.primefact
def PRIMEFACT : thm := BPrimefact.PRIMEFACT
def PRIMAFACT_CONTAINS : thm := BPrimefact.PRIMAFACT_CONTAINS
def PRIMEFACT_VARIANT : thm := BPrimefact.PRIMEFACT_VARIANT
def LUCAS_PRIMEFACT : thm := BPrimefact.LUCAS_PRIMEFACT

-- Certify
def EXP_EQ_MOD_CONV : HolCore.Equal.ioconv := fun t => BCertify.EXP_EQ_MOD_CONV t
def prime_theorem_cache := BCertify.prime_theorem_cache
def check_certificate := BCertify.check_certificate
def PROVE_PRIME := BCertify.PROVE_PRIME
def PROVE_PRIMEFACT := BCertify.PROVE_PRIMEFACT
def PRIME_TEST : term → IO (Except String thm) := fun t => (BCertify.PRIME_TEST t).run
def PRIME_CONV : term → IO (Except String thm) := fun t => (BCertify.PRIME_CONV t).run

/-- `needs "Library/pratt.ml"`: already done by importing this module. -/
def ensurePratt : IO Unit := pure ()

end SessionLibrary.Pratt
