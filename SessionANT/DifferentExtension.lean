/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/different_extension.ml                        . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/DifferentExtension.lean

  The session half of the different_extension.ml translation: it supplies HolANT.DifferentExtension's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/different_extension.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.DifferentExtension
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
import SessionLibrary.Products
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
import SessionANT.PrimeSplit
import SessionANT.NormIndex
import SessionANT.Discriminant
import SessionANT.TraceForm
import SessionANT.FiniteFieldTrace
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.Classgroup
import SessionANT.RelativeSplit
import SessionANT.RelativeDegree
import SessionANT.NfValuation
import SessionANT.Integrality
import SessionANT.Different

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.DifferentExtension

/-- The core theorems different_extension.ml uses. -/
def core1 : HolANT.DifferentExtension.CoreThms1 where
  ALGEBRA_TRACE_FREE_BASIS_MATRIX := SessionLibrary.RingDet.«ALGEBRA_TRACE_FREE_BASIS_MATRIX»
  ALGEBRA_TRACE_NILPOTENT := SessionLibrary.RingDet.«ALGEBRA_TRACE_NILPOTENT»
  ALGEBRA_TRACE_NORM_IN_CARRIER := SessionLibrary.RingDet.«ALGEBRA_TRACE_NORM_IN_CARRIER»
  ALGEBRA_TRACE_NORM_TOWER := SessionLibrary.FieldTheory.«ALGEBRA_TRACE_NORM_TOWER»
  ALGEBRA_TRACE_QUOTIENT_COMAXIMAL_NONZERO := SessionANT.FiniteFieldTrace.«ALGEBRA_TRACE_QUOTIENT_COMAXIMAL_NONZERO»
  ALGEBRA_TRACE_SCALAR := SessionLibrary.RingDet.«ALGEBRA_TRACE_SCALAR»
  BASIS_COORDINATES_EXPAND := SessionLibrary.RingDet.«BASIS_COORDINATES_EXPAND»
  BASIS_COORDINATES_IN_CARRIER := SessionLibrary.RingDet.«BASIS_COORDINATES_IN_CARRIER»
  BASIS_DISCRIMINANT_TIMES_COORD := SessionLibrary.RingDet.«BASIS_DISCRIMINANT_TIMES_COORD»
  CARD_IMAGE_INJ := Session.CARD_IMAGE_INJ
  CARD_NUMSEG_LT := Session.CARD_NUMSEG_LT
  DEDEKIND_IDEAL_MEMBER_PRINCIPAL_MULTIPLE := SessionANT.Dedekind.«DEDEKIND_IDEAL_MEMBER_PRINCIPAL_MULTIPLE»
  DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT := SessionANT.Dedekind.«DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT»
  DEDEKIND_IDEAL_PROD_SUBSET_CANCEL := SessionANT.Dedekind.«DEDEKIND_IDEAL_PROD_SUBSET_CANCEL»
  DEDEKIND_IDEAL_SUBSET_POW_VALUATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_SUBSET_POW_VALUATION»
  DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL := SessionANT.Dedekind.«DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL»
  DEDEKIND_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«DEDEKIND_RING_OF_INTEGERS»
  EQ_EXP := Session.EQ_EXP
  EQ_TRANS := Session.EQ_TRANS
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXTENSION := Session.EXTENSION
  EXTENSION_LINCOMB_ADD := SessionLibrary.RingDet.«EXTENSION_LINCOMB_ADD»
  EXTENSION_LINCOMB_LMUL := SessionLibrary.RingDet.«EXTENSION_LINCOMB_LMUL»
  FIELD_HOMOMORPHISM_INV := SessionLibrary.RingTheory.«FIELD_HOMOMORPHISM_INV»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_QUOTIENT_RING := SessionLibrary.RingTheory.«FIELD_QUOTIENT_RING»
  FINITE_EXTENSION_RING_MATROID := SessionLibrary.FieldTheory.«FINITE_EXTENSION_RING_MATROID»
  FINITE_IMP_FIELD_EXTENSION := SessionLibrary.FieldTheory.«FINITE_IMP_FIELD_EXTENSION»
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FREE_BASIS_EXISTS := SessionLibrary.FieldTheory.«FREE_BASIS_EXISTS»
  FREE_BASIS_FIELD := SessionLibrary.FieldTheory.«FREE_BASIS_FIELD»
  FREE_BASIS_HAS_SIZE := SessionLibrary.RingDet.«FREE_BASIS_HAS_SIZE»
  FREE_BASIS_INDEPENDENT := SessionLibrary.RingDet.«FREE_BASIS_INDEPENDENT»
  FREE_BASIS_INDEPENDENT_EQ := SessionLibrary.FieldTheory.«FREE_BASIS_INDEPENDENT_EQ»
  FREE_BASIS_IN_CARRIER := SessionLibrary.RingDet.«FREE_BASIS_IN_CARRIER»
  FUN_IN_IMAGE := Session.FUN_IN_IMAGE
  HAS_SIZE := Session.HAS_SIZE
  IDEAL_EXTENSION_POW_SUPPLEMENT := SessionANT.IdealArith.«IDEAL_EXTENSION_POW_SUPPLEMENT»
  IDEAL_GENERATED_EQ_0 := SessionLibrary.RingTheory.«IDEAL_GENERATED_EQ_0»
  IDEAL_GENERATED_IMAGE_IDEAL_GENERATED := SessionANT.IdealArith.«IDEAL_GENERATED_IMAGE_IDEAL_GENERATED»
  IDEAL_GENERATED_INC := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC»
  IDEAL_GENERATED_MINIMAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL»
  IDEAL_GENERATED_RING_IDEAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_RING_IDEAL»
  IDEAL_GENERATED_SING_ALT := SessionLibrary.RingTheory.«IDEAL_GENERATED_SING_ALT»
  IDEAL_NORM_GT_1 := SessionANT.IdealNorm.«IDEAL_NORM_GT_1»
  IDEAL_POW_0 := SessionANT.IdealArith.«IDEAL_POW_0»
  IDEAL_POW_1 := SessionANT.IdealArith.«IDEAL_POW_1»
  IDEAL_POW_ANTIMONO := SessionANT.IdealArith.«IDEAL_POW_ANTIMONO»
  IDEAL_POW_MONO := SessionANT.IdealArith.«IDEAL_POW_MONO»
  IDEAL_POW_PRINCIPAL := SessionANT.IdealArith.«IDEAL_POW_PRINCIPAL»
  IDEAL_POW_SUC := SessionANT.IdealArith.«IDEAL_POW_SUC»
  IDEAL_PROD_CARRIER := SessionANT.IdealArith.«IDEAL_PROD_CARRIER»
  IDEAL_PROD_COMAXIMAL := SessionANT.IdealArith.«IDEAL_PROD_COMAXIMAL»
  IDEAL_PROD_COMM := SessionANT.IdealArith.«IDEAL_PROD_COMM»
  IDEAL_PROD_EQ_ZERO := SessionANT.IdealArith.«IDEAL_PROD_EQ_ZERO»
  IDEAL_PROD_HOMOMORPHIC_IMAGE := SessionANT.IdealArith.«IDEAL_PROD_HOMOMORPHIC_IMAGE»
  IDEAL_PROD_IDEAL_GENERATED := SessionANT.IdealArith.«IDEAL_PROD_IDEAL_GENERATED»
  IDEAL_PROD_MINIMAL := SessionANT.IdealArith.«IDEAL_PROD_MINIMAL»
  IDEAL_PROD_MONO := SessionANT.IdealArith.«IDEAL_PROD_MONO»
  IDEAL_PROD_RZERO := SessionANT.IdealArith.«IDEAL_PROD_RZERO»
  IMAGE_CLAUSES := Session.IMAGE_CLAUSES
  IMP_CONJ := Session.IMP_CONJ
  INTEGRAL_DOMAIN_MUL_LCANCEL := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_LCANCEL»
  INTEGRAL_DOMAIN_RING_OF_INTEGERS := SessionANT.Numfield.«INTEGRAL_DOMAIN_RING_OF_INTEGERS»
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IDEAL_GENERATED_SELF := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SELF»
  IN_IMAGE := Session.IN_IMAGE
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_RING_IDEAL_RMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_RMUL»
  IN_SING := Session.IN_SING
  IN_SUBRING_0 := SessionLibrary.RingTheory.«IN_SUBRING_0»
  IN_SUBRING_1 := SessionLibrary.RingTheory.«IN_SUBRING_1»
  IN_SUBRING_ADD := SessionLibrary.RingTheory.«IN_SUBRING_ADD»
  IN_SUBRING_MUL := SessionLibrary.RingTheory.«IN_SUBRING_MUL»
  IN_SUBRING_POW := SessionLibrary.RingTheory.«IN_SUBRING_POW»
  IN_SUBRING_SUB := SessionLibrary.RingTheory.«IN_SUBRING_SUB»
  LE_REFL := Session.LE_REFL
  MATROID_BASIS_LARGE_INDEPENDENT := SessionLibrary.Matroids.«MATROID_BASIS_LARGE_INDEPENDENT»
  MAXIMAL_IDEAL_COMAXIMAL := SessionANT.IdealArith.«MAXIMAL_IDEAL_COMAXIMAL»
  MAXIMAL_IDEAL_IMP_PSUBSET := SessionLibrary.RingTheory.«MAXIMAL_IDEAL_IMP_PSUBSET»
  MAXIMAL_IMP_RING_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_RING_IDEAL»
  MONO_EXISTS := Session.MONO_EXISTS
  MONO_FORALL := Session.MONO_FORALL
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NOT_LE := Session.NOT_LE
/-- The core theorems different_extension.ml uses. -/
def core2 : HolANT.DifferentExtension.CoreThms2 where
  NUMBER_FIELD_CODIFFERENT_BASIS_DISCRIMINANT := SessionANT.Different.«NUMBER_FIELD_CODIFFERENT_BASIS_DISCRIMINANT»
  NUMBER_FIELD_CODIFFERENT_DIFFERENT := SessionANT.Different.«NUMBER_FIELD_CODIFFERENT_DIFFERENT»
  NUMBER_FIELD_CODIFFERENT_DIV := SessionANT.Different.«NUMBER_FIELD_CODIFFERENT_DIV»
  NUMBER_FIELD_DIFFERENT_NONZERO := SessionANT.Different.«NUMBER_FIELD_DIFFERENT_NONZERO»
  NUMBER_FIELD_HOMOMORPHIC_PREIMAGE := SessionANT.RelativeSplit.«NUMBER_FIELD_HOMOMORPHIC_PREIMAGE»
  NUMBER_FIELD_IDEAL_NORM_EXTENSION_Q := SessionANT.RelativeDegree.«NUMBER_FIELD_IDEAL_NORM_EXTENSION_Q»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_INDEPENDENT_MOD_IDEAL := SessionANT.RelativeDegree.«NUMBER_FIELD_INDEPENDENT_MOD_IDEAL»
  NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS := SessionANT.RelativeDegree.«NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS»
  NUMBER_FIELD_TOWER_LAW := SessionANT.RelativeSplit.«NUMBER_FIELD_TOWER_LAW»
  NUMBER_FIELD_TRACE_INTEGRAL := SessionANT.Integrality.«NUMBER_FIELD_TRACE_INTEGRAL»
  PRIME_IDEAL_IMP_PSUBSET := SessionLibrary.RingTheory.«PRIME_IDEAL_IMP_PSUBSET»
  PRIME_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«PRIME_IDEAL_IMP_SUBSET»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PSUBSET := Session.PSUBSET
  PSUBSET_IRREFL := Session.PSUBSET_IRREFL
  QUOTIENT_RING_0 := SessionLibrary.RingTheory.«QUOTIENT_RING_0»
  QUOTIENT_RING_CARRIER := SessionLibrary.RingTheory.«QUOTIENT_RING_CARRIER»
  QUOTIENT_RING_MUL := SessionLibrary.RingTheory.«QUOTIENT_RING_MUL»
  RESIDUE_DEGREE_QUOTIENT_RING := SessionANT.RelativeSplit.«RESIDUE_DEGREE_QUOTIENT_RING»
  RIGHT_EXISTS_IMP_THM := Session.RIGHT_EXISTS_IMP_THM
  RING_ADD_LDISTRIB := SessionLibrary.RingTheory.«RING_ADD_LDISTRIB»
  RING_COSET_EQ := SessionLibrary.RingTheory.«RING_COSET_EQ»
  RING_COSET_EQ_IDEAL := SessionLibrary.RingTheory.«RING_COSET_EQ_IDEAL»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_COMPOSE := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_COMPOSE»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_POW := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POW»
  RING_HOMOMORPHISM_RING_COSET := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_COSET»
  RING_HOMOMORPHISM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_HOMOMORPHISM_RING_OF_INTEGERS»
  RING_HOMOMORPHISM_SUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUM»
  RING_HOMOMORPHISM_SUM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUM_MUL»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IDEAL_POW := SessionANT.IdealArith.«RING_IDEAL_IDEAL_POW»
  RING_IDEAL_IDEAL_PROD := SessionANT.IdealArith.«RING_IDEAL_IDEAL_PROD»
  RING_IDEAL_IDEAL_QUOTIENT := SessionANT.IdealArith.«RING_IDEAL_IDEAL_QUOTIENT»
  RING_IDEAL_IMP_NONEMPTY := SessionLibrary.RingTheory.«RING_IDEAL_IMP_NONEMPTY»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_IDEAL_NUMBER_FIELD_DIFFERENT := SessionANT.Different.«RING_IDEAL_NUMBER_FIELD_DIFFERENT»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_MATROID_BASIS := SessionLibrary.FieldTheory.«RING_MATROID_BASIS»
  RING_MATROID_INDEPENDENT := SessionLibrary.FieldTheory.«RING_MATROID_INDEPENDENT»
  RING_MONOMORPHISM_EQ_0 := SessionLibrary.RingTheory.«RING_MONOMORPHISM_EQ_0»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_ASSOC := SessionLibrary.RingTheory.«RING_MUL_ASSOC»
  RING_MUL_IN_IDEAL_PROD := SessionANT.IdealArith.«RING_MUL_IN_IDEAL_PROD»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_MUL_RNEG := SessionLibrary.RingTheory.«RING_MUL_RNEG»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_MUL_SYM := SessionLibrary.RingTheory.«RING_MUL_SYM»
  RING_NILPOTENT := SessionLibrary.RingTheory.«RING_NILPOTENT»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_FINITE_QUOTIENT := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FINITE_QUOTIENT»
  RING_OF_INTEGERS_IDEAL_EXTENSION := SessionANT.RelativeSplit.«RING_OF_INTEGERS_IDEAL_EXTENSION»
  RING_OF_INTEGERS_IDEAL_EXTENSION_CONTRACTION_PRIME := SessionANT.RelativeDegree.«RING_OF_INTEGERS_IDEAL_EXTENSION_CONTRACTION_PRIME»
  RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME := SessionANT.RelativeSplit.«RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME»
  RING_OF_INTEGERS_IN_IDEAL_GENERATED_SING := SessionANT.Numfield.«RING_OF_INTEGERS_IN_IDEAL_GENERATED_SING»
  RING_OF_INTEGERS_PRIME_IDEAL_BELOW := SessionANT.RelativeSplit.«RING_OF_INTEGERS_PRIME_IDEAL_BELOW»
  RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION := SessionANT.RelativeSplit.«RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION»
  RING_OF_INTEGERS_SUBRING := SessionANT.Numfield.«RING_OF_INTEGERS_SUBRING»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INTEGERS_SUBSET_CODIFFERENT := SessionANT.Different.«RING_OF_INTEGERS_SUBSET_CODIFFERENT»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_SPAN_SELF := SessionLibrary.FieldTheory.«RING_SPAN_SELF»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_EQ_0 := SessionLibrary.RingTheory.«RING_SUM_EQ_0»
  RING_SUM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_SUM_RING_OF_INTEGERS»
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SUBSET := Session.SUBSET
  SUBSET_REFL := Session.SUBSET_REFL
  SUBSET_TRANS := Session.SUBSET_TRANS
  extension_degree := SessionLibrary.FieldTheory.«extension_degree»
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  free_basis := SessionLibrary.RingDet.«free_basis»
  ideal_norm := SessionANT.IdealNorm.«ideal_norm»
  ideal_quotient := SessionANT.IdealArith.«ideal_quotient»
  number_field_codifferent := SessionANT.Different.«number_field_codifferent»
  number_field_different := SessionANT.Different.«number_field_different»
  o_DEF := Session.o_DEF
  ramification_index := SessionANT.PrimeSplit.«ramification_index»
  ring_ideal := SessionLibrary.RingTheory.«ring_ideal»
  ring_spanning := SessionLibrary.FieldTheory.«ring_spanning»
  subring_of := SessionLibrary.RingTheory.«subring_of»

/-- What different_extension.ml uses from Session. -/
def deps : HolANT.DifferentExtension.DifferentExtensionDeps where
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
  core2 := core2

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in different_extension.ml order. -/
initialize BDifferentExtension01 : HolANT.DifferentExtension.DifferentExtension01 ←
  ioB "setupDifferentExtension01" (HolANT.DifferentExtension.setupDifferentExtension01 deps).run
initialize BDifferentExtension02 : HolANT.DifferentExtension.DifferentExtension02 ←
  ioB "setupDifferentExtension02" (HolANT.DifferentExtension.setupDifferentExtension02 deps BDifferentExtension01).run
initialize BDifferentExtension03 : HolANT.DifferentExtension.DifferentExtension03 ←
  ioB "setupDifferentExtension03" (HolANT.DifferentExtension.setupDifferentExtension03 deps BDifferentExtension02).run
initialize BDifferentExtension04 : HolANT.DifferentExtension.DifferentExtension04 ←
  ioB "setupDifferentExtension04" (HolANT.DifferentExtension.setupDifferentExtension04 deps BDifferentExtension03).run

-- DifferentExtension01
def RING_OF_INTEGERS_BASIS_MOD_PRIME : thm := BDifferentExtension01.RING_OF_INTEGERS_BASIS_MOD_PRIME
def RING_OF_INTEGERS_BASIS_MOD_PRIME_FREE : thm := BDifferentExtension01.RING_OF_INTEGERS_BASIS_MOD_PRIME_FREE
def RING_OF_INTEGERS_LOCAL_BASIS : thm := BDifferentExtension01.RING_OF_INTEGERS_LOCAL_BASIS

-- DifferentExtension02
def RING_OF_INTEGERS_QUOTIENT_TRACE : thm := BDifferentExtension02.RING_OF_INTEGERS_QUOTIENT_TRACE
def NUMBER_FIELD_TRACE_NILPOTENT : thm := BDifferentExtension02.NUMBER_FIELD_TRACE_NILPOTENT
def NUMBER_FIELD_TRACE_COMAXIMAL : thm := BDifferentExtension02.NUMBER_FIELD_TRACE_COMAXIMAL
def NUMBER_FIELD_CODIFFERENT_TRACE_DIV : thm := BDifferentExtension02.NUMBER_FIELD_CODIFFERENT_TRACE_DIV

-- DifferentExtension03
def NUMBER_FIELD_DIFFERENT_TRACE : thm := BDifferentExtension03.NUMBER_FIELD_DIFFERENT_TRACE
def NUMBER_FIELD_DIFFERENT_SUBSET_RAMIFICATION : thm := BDifferentExtension03.NUMBER_FIELD_DIFFERENT_SUBSET_RAMIFICATION
def NUMBER_FIELD_DIFFERENT_RAMIFIED : thm := BDifferentExtension03.NUMBER_FIELD_DIFFERENT_RAMIFIED
def RING_OF_INTEGERS_IDEAL_DOUBLE_DUAL : thm := BDifferentExtension03.RING_OF_INTEGERS_IDEAL_DOUBLE_DUAL

-- DifferentExtension04
def NUMBER_FIELD_CODIFFERENT_TOWER : thm := BDifferentExtension04.NUMBER_FIELD_CODIFFERENT_TOWER
def NUMBER_FIELD_DIFFERENT_TOWER : thm := BDifferentExtension04.NUMBER_FIELD_DIFFERENT_TOWER

/-- `needs "ANT/different_extension.ml"`: already done by importing this module. -/
def ensureDifferentExtension : IO Unit := pure ()

end SessionANT.DifferentExtension
