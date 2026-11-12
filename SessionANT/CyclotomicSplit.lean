/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/cyclotomic_split.ml                           . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/CyclotomicSplit.lean

  The session half of the cyclotomic_split.ml translation: it supplies HolANT.CyclotomicSplit's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/cyclotomic_split.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.CyclotomicSplit
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
import SessionANT.IdealArith
import SessionLibrary.Isum
import SessionLibrary.Products
import SessionANT.Algmisc
import SessionANT.Integral
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionANT.RingOfIntegers
import SessionANT.PrimeSplit
import SessionANT.NormIndex
import SessionANT.Discriminant
import SessionANT.TraceForm
import SessionANT.FiniteFieldTrace
import SessionANT.Ramification
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.Classgroup
import SessionANT.RelativeSplit
import SessionANT.RelativeDegree
import SessionANT.NfValuation
import SessionANT.Integrality
import SessionANT.DedekindKummer
import SessionANT.SplittingTypes
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
import SessionLibrary.SymmetricGroup
import SessionLibrary.Galois
import SessionLibrary.RingGroups
import SessionLibrary.FiniteFields
import SessionLibrary.Integer
import SessionLibrary.Multiplicative
import SessionLibrary.Primitive
import SessionANT.CyclotomicPoly
import SessionANT.PowerBasis
import SessionANT.CyclotomicField
import SessionANT.CyclotomicIntegers

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.CyclotomicSplit

/-- The core theorems cyclotomic_split.ml uses. -/
def core1 : HolANT.CyclotomicSplit.CoreThms1 where
  ADD_EQ_0 := Session.ADD_EQ_0
  ARITH := Session.ARITH
  ARITH_EQ := Session.ARITH_EQ
  CARD_IMAGE_INJ := Session.CARD_IMAGE_INJ
  CARD_INTEGER_MOD_RING := SessionLibrary.RingTheory.«CARD_INTEGER_MOD_RING»
  CARRIER_SUBRING_OF := SessionLibrary.RingTheory.«CARRIER_SUBRING_OF»
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  COPRIME_SYM := SessionLibrary.Prime.«COPRIME_SYM»
  CYCLOTOMIC_FIELD_DEGREE := SessionANT.CyclotomicField.«CYCLOTOMIC_FIELD_DEGREE»
  CYCLOTOMIC_FIELD_RING_OF_INTEGERS := SessionANT.CyclotomicIntegers.«CYCLOTOMIC_FIELD_RING_OF_INTEGERS»
  CYCLOTOMIC_POLY_1 := SessionANT.CyclotomicPoly.«CYCLOTOMIC_POLY_1»
  CYCLOTOMIC_POLY_DEG := SessionANT.CyclotomicPoly.«CYCLOTOMIC_POLY_DEG»
  CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE := SessionANT.CyclotomicPoly.«CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE»
  CYCLOTOMIC_POLY_IN_CARRIER := SessionANT.CyclotomicPoly.«CYCLOTOMIC_POLY_IN_CARRIER»
  CYCLOTOMIC_POLY_IRREDUCIBLE_FACTORIZATION := SessionANT.CyclotomicPoly.«CYCLOTOMIC_POLY_IRREDUCIBLE_FACTORIZATION»
  CYCLOTOMIC_POLY_MONIC := SessionANT.CyclotomicPoly.«CYCLOTOMIC_POLY_MONIC»
  CYCLOTOMIC_POLY_RING_CHAR := SessionANT.CyclotomicPoly.«CYCLOTOMIC_POLY_RING_CHAR»
  CYCLOTOMIC_POLY_ROOT := SessionANT.CyclotomicPoly.«CYCLOTOMIC_POLY_ROOT»
  DEDEKIND_KUMMER_EPIMORPHISM_Q := SessionANT.DedekindKummer.«DEDEKIND_KUMMER_EPIMORPHISM_Q»
  DEDEKIND_KUMMER_Q := SessionANT.DedekindKummer.«DEDEKIND_KUMMER_Q»
  DIVIDES_0 := SessionLibrary.Prime.«DIVIDES_0»
  DIVIDES_ONE := Session.DIVIDES_ONE
  DIVIDES_REFL := SessionLibrary.Prime.«DIVIDES_REFL»
  DIVIDES_REXP := SessionLibrary.Prime.«DIVIDES_REXP»
  DIVIDES_RMUL := SessionLibrary.Prime.«DIVIDES_RMUL»
  EQ_MULT_LCANCEL := Session.EQ_MULT_LCANCEL
  EXP := Session.EXP
  EXP_ADD := Session.EXP_ADD
  EXP_EQ_0 := Session.EXP_EQ_0
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_INTEGER_MOD_RING := SessionLibrary.RingTheory.«FIELD_INTEGER_MOD_RING»
  FINITE_INTEGER_MOD_RING := SessionLibrary.RingTheory.«FINITE_INTEGER_MOD_RING»
  FINITE_SING := Session.FINITE_SING
  FORALL_UNWIND_THM2 := Session.FORALL_UNWIND_THM2
  IDEALS_GENERATED_SUBSET := SessionLibrary.RingTheory.«IDEALS_GENERATED_SUBSET»
  IDEAL_GENERATED_INC_GEN := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC_GEN»
  IDEAL_GENERATED_NONEMPTY := SessionLibrary.RingTheory.«IDEAL_GENERATED_NONEMPTY»
  IDEAL_GENERATED_SUBSET := SessionLibrary.RingTheory.«IDEAL_GENERATED_SUBSET»
  IDEAL_PRODUCT_SING := SessionANT.IdealArith.«IDEAL_PRODUCT_SING»
  IMP_CONJ := Session.IMP_CONJ
  INDEX_DECOMPOSITION := SessionLibrary.Prime.«INDEX_DECOMPOSITION»
  INTEGER_MOD_RING_CHAR := SessionLibrary.RingTheory.«INTEGER_MOD_RING_CHAR»
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INTEGRAL_DOMAIN_RING_OF_INTEGERS := SessionANT.Numfield.«INTEGRAL_DOMAIN_RING_OF_INTEGERS»
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IDEAL_GENERATED_SELF := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SELF»
  IN_IDEAL_GENERATED_SING := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SING»
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_INTER := Session.IN_INTER
  IN_RING_IDEAL_SUB := SessionLibrary.RingTheory.«IN_RING_IDEAL_SUB»
  IN_SING := Session.IN_SING
  LE_1 := Session.LE_1
  LE_MULT2 := Session.LE_MULT2
  LT_REFL := Session.LT_REFL
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_EQ_0 := Session.MULT_EQ_0
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_PRIME_DECOMPOSITION_Q := SessionANT.SplittingTypes.«NUMBER_FIELD_PRIME_DECOMPOSITION_Q»
  NUMBER_FIELD_RAMIFIED_DISCRIMINANT := SessionANT.Ramification.«NUMBER_FIELD_RAMIFIED_DISCRIMINANT»
  NUMBER_FIELD_TOTALLY_SPLIT_CARD := SessionANT.SplittingTypes.«NUMBER_FIELD_TOTALLY_SPLIT_CARD»
  ORDER_EQ_1 := SessionLibrary.Pocklington.«ORDER_EQ_1»
  PHI_1 := SessionLibrary.Pocklington.«PHI_1»
  PHI_EQ_0 := SessionLibrary.Pocklington.«PHI_EQ_0»
  PHI_LOWERBOUND_1_STRONG := SessionLibrary.Pocklington.«PHI_LOWERBOUND_1_STRONG»
  PHI_PRIMEPOW_ALT := SessionLibrary.Pocklington.«PHI_PRIMEPOW_ALT»
  POLY_DEG_1_IMP_IRREDUCIBLE := SessionLibrary.RingTheory.«POLY_DEG_1_IMP_IRREDUCIBLE»
  POLY_EVAL_1 := SessionLibrary.RingTheory.«POLY_EVAL_1»
  POLY_EVAL_SUB := SessionLibrary.RingTheory.«POLY_EVAL_SUB»
  POLY_EVAL_VAR := SessionLibrary.RingTheory.«POLY_EVAL_VAR»
  POLY_EXTEND_EVALUATE := SessionLibrary.RingTheory.«POLY_EXTEND_EVALUATE»
  POLY_EXTEND_RING_OF_INTEGERS := SessionANT.DedekindKummer.«POLY_EXTEND_RING_OF_INTEGERS»
  POLY_RING_CLAUSES := SessionLibrary.RingTheory.«POLY_RING_CLAUSES»
  POLY_RING_INTEGER_MOD_RING_SUBSET := SessionANT.DedekindKummer.«POLY_RING_INTEGER_MOD_RING_SUBSET»
  PRIME_COPRIME_EQ := SessionLibrary.Prime.«PRIME_COPRIME_EQ»
  PRIME_GE_2 := SessionLibrary.Prime.«PRIME_GE_2»
  PRIME_IMP_NZ := SessionLibrary.Prime.«PRIME_IMP_NZ»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ASSOCIATES_PRIME_POWER_ORDER := SessionANT.CyclotomicIntegers.«RING_ASSOCIATES_PRIME_POWER_ORDER»
  RING_COSET_EQ := SessionLibrary.RingTheory.«RING_COSET_EQ»
  RING_DIVIDES_REFL := SessionLibrary.RingTheory.«RING_DIVIDES_REFL»
  RING_DIVIDES_RMUL := SessionLibrary.RingTheory.«RING_DIVIDES_RMUL»
  RING_DIVIDES_TRANS := SessionLibrary.RingTheory.«RING_DIVIDES_TRANS»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IDEAL_POW := SessionANT.IdealArith.«RING_IDEAL_IDEAL_POW»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_ORDER_DIVIDES := SessionLibrary.RingTheory.«RING_ORDER_DIVIDES»
  RING_ORDER_UNIQUE := SessionLibrary.RingTheory.«RING_ORDER_UNIQUE»
  RING_POLYNOMIAL_1 := SessionLibrary.RingTheory.«RING_POLYNOMIAL_1»
  RING_POLYNOMIAL_VAR := SessionLibrary.RingTheory.«RING_POLYNOMIAL_VAR»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_PRODUCT_POW := SessionLibrary.RingTheory.«RING_PRODUCT_POW»
  RING_PRODUCT_SING := SessionLibrary.RingTheory.«RING_PRODUCT_SING»
  RING_SETADD_RSUBSET := SessionLibrary.RingTheory.«RING_SETADD_RSUBSET»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  SUBRING_GENERATED_INC_GEN := SessionLibrary.RingTheory.«SUBRING_GENERATED_INC_GEN»
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM_EQ := Session.SUBSET_ANTISYM_EQ
  TRIVIAL_INTEGER_MOD_RING := SessionLibrary.RingTheory.«TRIVIAL_INTEGER_MOD_RING»
  TRIVIAL_RING_10 := SessionLibrary.RingTheory.«TRIVIAL_RING_10»
  divides := Session.divides
  poly_eval := SessionLibrary.RingTheory.«poly_eval»
  ring_associates := SessionLibrary.RingTheory.«ring_associates»
  ring_pow := SessionLibrary.RingTheory.«ring_pow»

/-- What cyclotomic_split.ml uses from Session. -/
def deps : HolANT.CyclotomicSplit.CyclotomicSplitDeps where
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
  GROUP_RULE t := ExceptT.mk (SessionLibrary.GroupTheory.GROUP_RULE t)
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

/- The bundles, in cyclotomic_split.ml order. -/
initialize BCyclotomicSplit : HolANT.CyclotomicSplit.CyclotomicSplit ←
  ioB "setupCyclotomicSplit" (HolANT.CyclotomicSplit.setupCyclotomicSplit deps).run

-- CyclotomicSplit
def CYCLOTOMIC_FIELD_DEDEKIND_KUMMER : thm := BCyclotomicSplit.CYCLOTOMIC_FIELD_DEDEKIND_KUMMER
def CYCLOTOMIC_FIELD_PRIME_DECOMPOSITION : thm := BCyclotomicSplit.CYCLOTOMIC_FIELD_PRIME_DECOMPOSITION
def CYCLOTOMIC_FIELD_RAMIFIED : thm := BCyclotomicSplit.CYCLOTOMIC_FIELD_RAMIFIED
def CYCLOTOMIC_FIELD_TOTALLY_SPLIT : thm := BCyclotomicSplit.CYCLOTOMIC_FIELD_TOTALLY_SPLIT
def CYCLOTOMIC_FIELD_PRIME_POWER_RAMIFIED : thm := BCyclotomicSplit.CYCLOTOMIC_FIELD_PRIME_POWER_RAMIFIED

/-- `needs "ANT/cyclotomic_split.ml"`: already done by importing this module. -/
def ensureCyclotomicSplit : IO Unit := pure ()

end SessionANT.CyclotomicSplit
