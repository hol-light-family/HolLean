/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/prime_split.ml                                . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/PrimeSplit.lean

  The session half of the prime_split.ml translation: it supplies HolANT.PrimeSplit's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/prime_split.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.PrimeSplit
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.RingTheory
import SessionLibrary.Matroids
import SessionLibrary.Permutations
import SessionLibrary.RingDet
import SessionLibrary.FieldTheory
import SessionLibrary.Products
import SessionANT.IdealArith
import SessionANT.Algmisc
import SessionANT.Integral
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionLibrary.Isum
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.RingOfIntegers

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.PrimeSplit

/-- The core theorems prime_split.ml uses. -/
def core1 : HolANT.PrimeSplit.CoreThms1 where
  CARD_EQ_NSUM := Session.CARD_EQ_NSUM
  CARD_EXTENSION_DEGREE := SessionLibrary.FieldTheory.«CARD_EXTENSION_DEGREE»
  CARD_PRIME_SUBRING := SessionLibrary.RingTheory.«CARD_PRIME_SUBRING»
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  DEDEKIND_IDEAL_FACTORIZATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_FACTORIZATION»
  DEDEKIND_IDEAL_PRODUCT_PRIME_POW_UNIQUE := SessionANT.Dedekind.«DEDEKIND_IDEAL_PRODUCT_PRIME_POW_UNIQUE»
  DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL := SessionANT.Dedekind.«DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL»
  DEDEKIND_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«DEDEKIND_RING_OF_INTEGERS»
  DIVIDES_ZERO := SessionLibrary.Prime.«DIVIDES_ZERO»
  EQ_EXP := Session.EQ_EXP
  EQ_TRANS := Session.EQ_TRANS
  ETA_AX := Session.ETA_AX
  EXISTS_UNIQUE := Session.EXISTS_UNIQUE
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXP := Session.EXP
  EXP_ADD := Session.EXP_ADD
  EXP_EXP := Session.EXP_EXP
  EXP_NSUM := SessionLibrary.Products.«EXP_NSUM»
  EXTENSION := Session.EXTENSION
  FIELD_EXTENSION_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_EXTENSION_SUBFIELD_GENERATED»
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_INTEGRAL_DOMAIN_CHAR := SessionLibrary.RingTheory.«FINITE_INTEGRAL_DOMAIN_CHAR»
  FINITE_INTEGRAL_DOMAIN_IMP_FIELD := SessionLibrary.RingTheory.«FINITE_INTEGRAL_DOMAIN_IMP_FIELD»
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  IDEAL_GENERATED_INC_GEN := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC_GEN»
  IDEAL_GENERATED_MINIMAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL»
  IDEAL_GENERATED_MINIMAL_EQ := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL_EQ»
  IDEAL_GENERATED_MONO := SessionLibrary.RingTheory.«IDEAL_GENERATED_MONO»
  IDEAL_NORM_FACTORIZATION := SessionANT.IdealNorm.«IDEAL_NORM_FACTORIZATION»
  IDEAL_NORM_GT_1 := SessionANT.IdealNorm.«IDEAL_NORM_GT_1»
  IDEAL_NORM_IDEAL_POW := SessionANT.IdealNorm.«IDEAL_NORM_IDEAL_POW»
  IDEAL_NORM_IDEAL_PRODUCT := SessionANT.IdealNorm.«IDEAL_NORM_IDEAL_PRODUCT»
  IDEAL_NORM_SUBSET_EQ := SessionANT.IdealNorm.«IDEAL_NORM_SUBSET_EQ»
  IDEAL_POW_EQ_ZERO := SessionANT.IdealArith.«IDEAL_POW_EQ_ZERO»
  IDEAL_PRODUCT_EQ := SessionANT.IdealArith.«IDEAL_PRODUCT_EQ»
  IDEAL_PRODUCT_IMAGE := SessionANT.IdealArith.«IDEAL_PRODUCT_IMAGE»
  IDEAL_PROD_SUBSET_LEFT := SessionANT.IdealArith.«IDEAL_PROD_SUBSET_LEFT»
  IDEAL_PROD_SUBSET_RIGHT := SessionANT.IdealArith.«IDEAL_PROD_SUBSET_RIGHT»
  IDEAL_VALUATION_EQ_0 := SessionANT.Dedekind.«IDEAL_VALUATION_EQ_0»
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INTEGRAL_DOMAIN_CHAR := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_CHAR»
  INTEGRAL_DOMAIN_QUOTIENT_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_QUOTIENT_RING»
  INTEGRAL_DOMAIN_RING_OF_INTEGERS := SessionANT.Numfield.«INTEGRAL_DOMAIN_RING_OF_INTEGERS»
  INT_ABS_NUM := Session.INT_ABS_NUM
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IDEAL_GENERATED_SELF := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SELF»
  IN_IDEAL_GENERATED_SING := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SING»
  IN_IMAGE := Session.IN_IMAGE
  IN_SING := Session.IN_SING
  IN_UNIV := Session.IN_UNIV
  ITERATE_EQ := Session.ITERATE_EQ
  LE_REFL := Session.LE_REFL
  LT_REFL := Session.LT_REFL
  MONOIDAL_MUL := Session.MONOIDAL_MUL
  MULT_EQ_0 := Session.MULT_EQ_0
  MULT_SYM := Session.MULT_SYM
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NPRODUCT_CLAUSES := Session.NPRODUCT_CLAUSES
  NPRODUCT_EQ := SessionLibrary.Products.«NPRODUCT_EQ»
  NSUM_CLAUSES := Session.NSUM_CLAUSES
  NSUM_LE := Session.NSUM_LE
  NSUM_POS_BOUND := Session.NSUM_POS_BOUND
  NUMBER_FIELD_DEGREE_POS := SessionANT.Numfield.«NUMBER_FIELD_DEGREE_POS»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUM_OF_INT_OF_NUM := Session.NUM_OF_INT_OF_NUM
  PAIR_EQ := Session.PAIR_EQ
  PRIME_EXP := SessionLibrary.Prime.«PRIME_EXP»
  PRIME_GE_2 := SessionLibrary.Prime.«PRIME_GE_2»
  PRIME_IDEAL_IMP_PSUBSET := SessionLibrary.RingTheory.«PRIME_IDEAL_IMP_PSUBSET»
  PRIME_IMP_NZ := SessionLibrary.Prime.«PRIME_IMP_NZ»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PRIME_SUBFIELD_EQ_SUBRING := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_EQ_SUBRING»
  QUOTIENT_RING_0 := SessionLibrary.RingTheory.«QUOTIENT_RING_0»
  RING_CHAR_DIVIDES_PRIME := SessionLibrary.RingTheory.«RING_CHAR_DIVIDES_PRIME»
  RING_COSET_EQ_IDEAL := SessionLibrary.RingTheory.«RING_COSET_EQ_IDEAL»
  RING_HOMOMORPHISM_RING_COSET := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_COSET»
  RING_HOMOMORPHISM_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_INT»
  RING_HOMOMORPHISM_RING_OF_NUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_NUM»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IDEAL_POW := SessionANT.IdealArith.«RING_IDEAL_IDEAL_POW»
  RING_IDEAL_IDEAL_PRODUCT := SessionANT.IdealArith.«RING_IDEAL_IDEAL_PRODUCT»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_FINITE_QUOTIENT := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FINITE_QUOTIENT»
  RING_OF_INTEGERS_IDEAL_NORM_INTEGER := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_IDEAL_NORM_INTEGER»
  RING_OF_INT_EQ_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_0»
  RING_OF_INT_IN_RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INT_IN_RING_OF_INTEGERS»
  RING_OF_INT_MUL := SessionLibrary.RingTheory.«RING_OF_INT_MUL»
  RING_OF_INT_OF_NUM := SessionLibrary.RingTheory.«RING_OF_INT_OF_NUM»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_OF_NUM_EQ_0 := SessionLibrary.RingTheory.«RING_OF_NUM_EQ_0»
  SELECT_UNIQUE := Session.SELECT_UNIQUE
  SIMPLE_IMAGE := Session.SIMPLE_IMAGE
  SING_SUBSET := Session.SING_SUBSET
  SUBRING_GENERATED_BY_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBRING_GENERATED_BY_SUBFIELD_GENERATED»
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  ideal_norm := SessionANT.IdealNorm.«ideal_norm»
  int_divides := Session.int_divides
  maximal_ideal := SessionLibrary.RingTheory.«maximal_ideal»
  nproduct := Session.nproduct
  number_field := SessionANT.Numfield.«number_field»
  o_DEF := Session.o_DEF
  o_THM := Session.o_THM
  prime_ideal := SessionLibrary.RingTheory.«prime_ideal»
  proper_ideal := SessionLibrary.RingTheory.«proper_ideal»
  ring_divides := SessionLibrary.RingTheory.«ring_divides»

/-- What prime_split.ml uses from Session. -/
def deps : HolANT.PrimeSplit.PrimeSplitDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  define s := do ExceptT.mk (Session.define (← HolLight.q s))
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  new_recursive_definition ax s := do
    ExceptT.mk (Session.new_recursive_definition ax (← HolLight.q s))
  LIST_INDUCT_TAC := Session.LIST_INDUCT_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  METIS_TAC := Session.METIS_TAC
  ASM_METIS_TAC := Session.ASM_METIS_TAC
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  TAUT t := ExceptT.mk (Session.TAUT t)
  ITAUT t := ExceptT.mk (Session.ITAUT t)
  REAL_ARITH t := ExceptT.mk (Session.REAL_ARITH t)
  REAL_FIELD t := ExceptT.mk (Session.REAL_FIELD t)
  REAL_ARITH_TAC := Session.REAL_ARITH_TAC
  ASM_REAL_ARITH_TAC := Session.ASM_REAL_ARITH_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  INT_ARITH t := ExceptT.mk (Session.INT_ARITH t)
  INT_ARITH_TAC := Session.INT_ARITH_TAC
  ASM_INT_ARITH_TAC := Session.ASM_INT_ARITH_TAC
  INTEGER_RULE t := ExceptT.mk (Session.INTEGER_RULE t)
  INTEGER_TAC := Session.INTEGER_TAC
  NUMBER_RULE := Session.NUMBER_RULE
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  INT_REDUCE_CONV := Session.INT_REDUCE_CONV
  INT_RED_CONV := Session.INT_RED_CONV
  INT_REM_DOWN_CONV := Session.INT_REM_DOWN_CONV
  HAS_SIZE_CONV := Session.HAS_SIZE_CONV
  let_CONV := Session.let_CONV
  num_CONV := Session.num_CONV
  mk_numeral := Session.mk_numeral
  PRIME_CONV t := ExceptT.mk (SessionLibrary.Pocklington.PRIME_CONV t)
  PRIME_RULE := SessionLibrary.Pocklington.PRIME_RULE
  RING_RULE t := ExceptT.mk (SessionLibrary.RingTheory.RING_RULE t)
  INTEGRAL_DOMAIN_RULE t := ExceptT.mk (SessionLibrary.RingTheory.INTEGRAL_DOMAIN_RULE t)
  FIELD_TAC := SessionLibrary.RingTheory.FIELD_TAC
  RING_CARRIER_TAC := SessionLibrary.RingTheory.RING_CARRIER_TAC
  RING_TAC := SessionLibrary.RingTheory.RING_TAC
  RING_PULL_DIV_TAC := SessionLibrary.RingTheory.RING_PULL_DIV_TAC
  LET_TAC := Session.LET_TAC
  basic_ss := Session.basic_ss
  INTEGER_MOD_RING_RED_CONV := SessionLibrary.RingTheory.INTEGER_MOD_RING_RED_CONV
  NUM_SUB_CONV := Session.NUM_SUB_CONV
  REAL_RAT_REDUCE_CONV := Session.REAL_RAT_REDUCE_CONV
  NUM_EQ_CONV := Session.NUM_EQ_CONV
  NUM_DIV_CONV := Session.NUM_DIV_CONV
  EXP_MOD_CONV := Session.EXP_MOD_CONV
  EXPAND_CASES_CONV := Session.EXPAND_CASES_CONV
  DIVIDES_CONV := SessionLibrary.Prime.DIVIDES_CONV
  COPRIME_CONV := SessionLibrary.Prime.COPRIME_CONV
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in prime_split.ml order. -/
initialize BPrimeSplit : HolANT.PrimeSplit.PrimeSplit ←
  ioB "setupPrimeSplit" (HolANT.PrimeSplit.setupPrimeSplit deps).run

-- PrimeSplit
def ramification_index : thm := BPrimeSplit.ramification_index
def residue_degree : thm := BPrimeSplit.residue_degree
def RAMIFICATION_INDEX_INTEGER_RING : thm := BPrimeSplit.RAMIFICATION_INDEX_INTEGER_RING
def RESIDUE_DEGREE_INTEGER_RING : thm := BPrimeSplit.RESIDUE_DEGREE_INTEGER_RING
def RING_OF_NUM_IN_PRIME_IDEAL : thm := BPrimeSplit.RING_OF_NUM_IN_PRIME_IDEAL
def RING_OF_INT_IN_PRIME_IDEAL : thm := BPrimeSplit.RING_OF_INT_IN_PRIME_IDEAL
def RAMIFICATION_INDEX_PRIME : thm := BPrimeSplit.RAMIFICATION_INDEX_PRIME
def IDEAL_NORM_RESIDUE_DEGREE_Q : thm := BPrimeSplit.IDEAL_NORM_RESIDUE_DEGREE_Q
def RING_OF_INTEGERS_PRIME_IDEAL_ABOVE : thm := BPrimeSplit.RING_OF_INTEGERS_PRIME_IDEAL_ABOVE
def RING_OF_INTEGERS_RESIDUE_FIELD : thm := BPrimeSplit.RING_OF_INTEGERS_RESIDUE_FIELD
def RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q : thm := BPrimeSplit.RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q
def NUMBER_FIELD_PRIME_IDEAL_DEGREE_ONE : thm := BPrimeSplit.NUMBER_FIELD_PRIME_IDEAL_DEGREE_ONE
def RING_OF_INTEGERS_IDEAL_GENERATED_PRIME : thm := BPrimeSplit.RING_OF_INTEGERS_IDEAL_GENERATED_PRIME
def NUMBER_FIELD_PRIME_FACTORIZATION_Q : thm := BPrimeSplit.NUMBER_FIELD_PRIME_FACTORIZATION_Q
def NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE_Q : thm := BPrimeSplit.NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE_Q
def NUMBER_FIELD_FUNDAMENTAL_IDENTITY_Q : thm := BPrimeSplit.NUMBER_FIELD_FUNDAMENTAL_IDENTITY_Q
def NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q : thm := BPrimeSplit.NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q
def NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q : thm := BPrimeSplit.NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q
def NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE_IMAGE : thm := BPrimeSplit.NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE_IMAGE
def NUMBER_FIELD_IDEAL_NORM_PRIME_PRODUCT : thm := BPrimeSplit.NUMBER_FIELD_IDEAL_NORM_PRIME_PRODUCT
def NUMBER_FIELD_PRIME_FACTORIZATION_SUBSET_EQ : thm := BPrimeSplit.NUMBER_FIELD_PRIME_FACTORIZATION_SUBSET_EQ
def NUMBER_FIELD_PRIME_IDEAL_PROD_EQ : thm := BPrimeSplit.NUMBER_FIELD_PRIME_IDEAL_PROD_EQ

/-- `needs "ANT/prime_split.ml"`: already done by importing this module. -/
def ensurePrimeSplit : IO Unit := pure ()

end SessionANT.PrimeSplit
