/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/discriminant_extension.ml                     . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/DiscriminantExtension.lean

  The session half of the discriminant_extension.ml translation: it supplies HolANT.DiscriminantExtension's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/discriminant_extension.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.DiscriminantExtension
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
import SessionANT.NormIndex
import SessionANT.Discriminant
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.Classgroup
import SessionANT.PrimeSplit
import SessionANT.TraceForm
import SessionANT.RelativeSplit
import SessionANT.RelativeDegree
import SessionANT.NfValuation
import SessionANT.Integrality
import SessionANT.Different
import SessionANT.FiniteFieldTrace
import SessionANT.DifferentExtension
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
import SessionLibrary.SymmetricGroup
import SessionLibrary.Galois
import SessionLibrary.RingGroups
import SessionLibrary.FiniteFields
import SessionANT.Decomposition
import SessionANT.Ramification
import SessionANT.SplittingTypes
import SessionANT.NfDecomposition
import SessionANT.ConjugateIdeals
import SessionLibrary.Integer
import SessionLibrary.Multiplicative
import SessionLibrary.Primitive
import SessionANT.DedekindKummer
import SessionANT.DecompositionField
import SessionANT.SplitPrimes
import SessionANT.IdealNormExtension

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.DiscriminantExtension

/-- The core theorems discriminant_extension.ml uses. -/
def core1 : HolANT.DiscriminantExtension.CoreThms1 where
  ALGEBRA_NORM_EQ_0 := SessionLibrary.FieldTheory.«ALGEBRA_NORM_EQ_0»
  ALGEBRA_NORM_INV := SessionLibrary.RingDet.«ALGEBRA_NORM_INV»
  ALGEBRA_NORM_MUL := SessionLibrary.RingDet.«ALGEBRA_NORM_MUL»
  ALGEBRA_TRACE_DUAL_BASIS_EXISTS := SessionLibrary.RingDet.«ALGEBRA_TRACE_DUAL_BASIS_EXISTS»
  ALGEBRA_TRACE_LINCOMB_MUL := SessionLibrary.RingDet.«ALGEBRA_TRACE_LINCOMB_MUL»
  ALGEBRA_TRACE_NORM_BASE := SessionLibrary.FieldTheory.«ALGEBRA_TRACE_NORM_BASE»
  ALGEBRA_TRACE_NORM_IN_CARRIER := SessionLibrary.RingDet.«ALGEBRA_TRACE_NORM_IN_CARRIER»
  ALGEBRA_TRACE_SCALAR := SessionLibrary.RingDet.«ALGEBRA_TRACE_SCALAR»
  BASIS_DISCRIMINANT_MUL := SessionLibrary.RingDet.«BASIS_DISCRIMINANT_MUL»
  CARD_NUMSEG_LT := Session.CARD_NUMSEG_LT
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES := SessionANT.Dedekind.«DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES»
  DEDEKIND_IDEAL_SUBSET_POW_VALUATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_SUBSET_POW_VALUATION»
  DEDEKIND_IDEAL_SUBSET_VALUATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_SUBSET_VALUATION»
  DEDEKIND_IDEAL_WEAK_APPROXIMATION := SessionANT.DedekindStruct.«DEDEKIND_IDEAL_WEAK_APPROXIMATION»
  DEDEKIND_IN_IDEAL_POW_VALUATION := SessionANT.Dedekind.«DEDEKIND_IN_IDEAL_POW_VALUATION»
  DEDEKIND_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«DEDEKIND_RING_OF_INTEGERS»
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  EQ_TRANS := Session.EQ_TRANS
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_MUL_LINV := SessionLibrary.RingTheory.«FIELD_MUL_LINV»
  FIELD_MUL_RINV := SessionLibrary.RingTheory.«FIELD_MUL_RINV»
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FIELD_UNIT := SessionLibrary.RingTheory.«FIELD_UNIT»
  FINITE_IMP_FIELD_EXTENSION := SessionLibrary.FieldTheory.«FINITE_IMP_FIELD_EXTENSION»
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FREE_BASIS_EXTENSION_DEGREE := SessionLibrary.FieldTheory.«FREE_BASIS_EXTENSION_DEGREE»
  FUN_EQ_THM := Session.FUN_EQ_THM
  IDEAL_GENERATED_INC := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC»
  IDEAL_GENERATED_MINIMAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL»
  IDEAL_GENERATED_MINIMAL_EQ := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL_EQ»
  IDEAL_GENERATED_MONO := SessionLibrary.RingTheory.«IDEAL_GENERATED_MONO»
  IDEAL_GENERATED_SING_ALT := SessionLibrary.RingTheory.«IDEAL_GENERATED_SING_ALT»
  IDEAL_POW_1 := SessionANT.IdealArith.«IDEAL_POW_1»
  IDEAL_PROD_COMM := SessionANT.IdealArith.«IDEAL_PROD_COMM»
  IDEAL_PROD_RZERO := SessionANT.IdealArith.«IDEAL_PROD_RZERO»
  IDEAL_VALUATION_EQ_0 := SessionANT.Dedekind.«IDEAL_VALUATION_EQ_0»
  IDEAL_VALUATION_IDEAL_PROD := SessionANT.Dedekind.«IDEAL_VALUATION_IDEAL_PROD»
  IDEAL_VALUATION_PRINCIPAL_MUL := SessionANT.Dedekind.«IDEAL_VALUATION_PRINCIPAL_MUL»
  IDEAL_VALUATION_PRINCIPAL_POW := SessionANT.Dedekind.«IDEAL_VALUATION_PRINCIPAL_POW»
  IMAGE_I := Session.IMAGE_I
  IMAGE_o := Session.IMAGE_o
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  INTEGRAL_DOMAIN_POW_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_POW_EQ_0»
  INT_ABS_POS := Session.INT_ABS_POS
  INT_ABS_POW := Session.INT_ABS_POW
  INT_OF_NUM_MUL := Session.INT_OF_NUM_MUL
  INT_OF_NUM_OF_INT := Session.INT_OF_NUM_OF_INT
  INT_OF_NUM_POW := Session.INT_OF_NUM_POW
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IDEAL_GENERATED_SELF := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SELF»
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_RING_IDEAL_LMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_LMUL»
  IN_SING := Session.IN_SING
  IN_SUBRING_MUL := SessionLibrary.RingTheory.«IN_SUBRING_MUL»
  IN_SUBRING_SUM := SessionLibrary.RingTheory.«IN_SUBRING_SUM»
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_EQ_0 := Session.MULT_EQ_0
  MULT_SYM := Session.MULT_SYM
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NSUM_EQ := Session.NSUM_EQ
  NSUM_EQ_0 := Session.NSUM_EQ_0
  NSUM_EQ_0_IFF := Session.NSUM_EQ_0_IFF
  NUMBER_FIELD_CODIFFERENT_BASIS_DISCRIMINANT := SessionANT.Different.«NUMBER_FIELD_CODIFFERENT_BASIS_DISCRIMINANT»
  NUMBER_FIELD_CODIFFERENT_DIFFERENT := SessionANT.Different.«NUMBER_FIELD_CODIFFERENT_DIFFERENT»
  NUMBER_FIELD_CODIFFERENT_EQ_IMAGE := SessionANT.Different.«NUMBER_FIELD_CODIFFERENT_EQ_IMAGE»
  NUMBER_FIELD_DIFFERENT_NONZERO := SessionANT.Different.«NUMBER_FIELD_DIFFERENT_NONZERO»
  NUMBER_FIELD_DIFFERENT_RAMIFIED := SessionANT.DifferentExtension.«NUMBER_FIELD_DIFFERENT_RAMIFIED»
  NUMBER_FIELD_DIFFERENT_TOWER := SessionANT.DifferentExtension.«NUMBER_FIELD_DIFFERENT_TOWER»
  NUMBER_FIELD_FREE_BASIS_INTEGRAL := SessionANT.Different.«NUMBER_FIELD_FREE_BASIS_INTEGRAL»
  NUMBER_FIELD_HOMOMORPHIC_PREIMAGE := SessionANT.RelativeSplit.«NUMBER_FIELD_HOMOMORPHIC_PREIMAGE»
  NUMBER_FIELD_IDEAL_NORM_DIFFERENT := SessionANT.Different.«NUMBER_FIELD_IDEAL_NORM_DIFFERENT»
  NUMBER_FIELD_IDEAL_NORM_EQ_0 := SessionANT.IdealNormExtension.«NUMBER_FIELD_IDEAL_NORM_EQ_0»
  NUMBER_FIELD_IDEAL_NORM_EXTENSION := SessionANT.IdealNormExtension.«NUMBER_FIELD_IDEAL_NORM_EXTENSION»
  NUMBER_FIELD_IDEAL_NORM_EXTENSION_Q := SessionANT.RelativeDegree.«NUMBER_FIELD_IDEAL_NORM_EXTENSION_Q»
  NUMBER_FIELD_IDEAL_NORM_IDEAL := SessionANT.IdealNormExtension.«NUMBER_FIELD_IDEAL_NORM_IDEAL»
  NUMBER_FIELD_IDEAL_NORM_IDEAL_NORM := SessionANT.IdealNormExtension.«NUMBER_FIELD_IDEAL_NORM_IDEAL_NORM»
  NUMBER_FIELD_IDEAL_NORM_MUL := SessionANT.IdealNormExtension.«NUMBER_FIELD_IDEAL_NORM_MUL»
  NUMBER_FIELD_IDEAL_NORM_MUL_Q := SessionANT.NormIndex.«NUMBER_FIELD_IDEAL_NORM_MUL_Q»
  NUMBER_FIELD_IDEAL_NORM_POW := SessionANT.IdealNormExtension.«NUMBER_FIELD_IDEAL_NORM_POW»
  NUMBER_FIELD_IDEAL_NORM_TOWER := SessionANT.IdealNormExtension.«NUMBER_FIELD_IDEAL_NORM_TOWER»
  NUMBER_FIELD_IDEAL_NORM_VALUATION := SessionANT.IdealNormExtension.«NUMBER_FIELD_IDEAL_NORM_VALUATION»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_NORM_INTEGRAL := SessionANT.Integrality.«NUMBER_FIELD_NORM_INTEGRAL»
  NUMBER_FIELD_NORM_MULTIPLE := SessionANT.Integrality.«NUMBER_FIELD_NORM_MULTIPLE»
  NUMBER_FIELD_NORM_VALUATION := SessionANT.IdealNormExtension.«NUMBER_FIELD_NORM_VALUATION»
  NUMBER_FIELD_PRIME_IDEALS_ABOVE := SessionANT.RelativeSplit.«NUMBER_FIELD_PRIME_IDEALS_ABOVE»
  NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO := SessionANT.RelativeSplit.«NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO»
  NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS := SessionANT.RelativeDegree.«NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS»
  NUMBER_FIELD_TOWER_LAW := SessionANT.RelativeSplit.«NUMBER_FIELD_TOWER_LAW»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PRIME_SUBFIELD_MONOMORPHIC_IMAGE := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_MONOMORPHIC_IMAGE»
  RIGHT_EXISTS_IMP_THM := Session.RIGHT_EXISTS_IMP_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_DET := SessionLibrary.RingDet.«RING_DET»
  RING_DET_DIAGONAL := SessionLibrary.RingDet.«RING_DET_DIAGONAL»
  RING_DET_EQ := SessionLibrary.RingDet.«RING_DET_EQ»
  RING_DET_MUL := SessionLibrary.RingDet.«RING_DET_MUL»
  RING_DET_SUBRING := SessionLibrary.RingDet.«RING_DET_SUBRING»
  RING_HOMOMORPHISM_COMPOSE := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_COMPOSE»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_POW := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POW»
  RING_HOMOMORPHISM_SUBFIELD_INCLUSION := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_SUBFIELD_INCLUSION»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IDEAL_POW := SessionANT.IdealArith.«RING_IDEAL_IDEAL_POW»
  RING_IDEAL_IDEAL_PROD := SessionANT.IdealArith.«RING_IDEAL_IDEAL_PROD»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_IDEAL_NUMBER_FIELD_DIFFERENT := SessionANT.Different.«RING_IDEAL_NUMBER_FIELD_DIFFERENT»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_ASSOC := SessionLibrary.RingTheory.«RING_MUL_ASSOC»
  RING_MUL_IN_IDEAL_PROD := SessionANT.IdealArith.«RING_MUL_IN_IDEAL_PROD»
  RING_MUL_IN_PRIME_IDEAL := SessionLibrary.RingTheory.«RING_MUL_IN_PRIME_IDEAL»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_IDEAL_EXTENSION := SessionANT.RelativeSplit.«RING_OF_INTEGERS_IDEAL_EXTENSION»
  RING_OF_INTEGERS_IDEAL_GENERATED_SING_EQ_0 := SessionANT.Numfield.«RING_OF_INTEGERS_IDEAL_GENERATED_SING_EQ_0»
  RING_OF_INTEGERS_LOCAL_BASIS := SessionANT.DifferentExtension.«RING_OF_INTEGERS_LOCAL_BASIS»
  RING_OF_INTEGERS_SUBRING := SessionANT.Numfield.«RING_OF_INTEGERS_SUBRING»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INTEGERS_SUBSET_CODIFFERENT := SessionANT.Different.«RING_OF_INTEGERS_SUBSET_CODIFFERENT»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_IN_PRIME_IDEAL := SessionLibrary.RingTheory.«RING_POW_IN_PRIME_IDEAL»
  RING_PRODUCT_CONST := SessionLibrary.RingTheory.«RING_PRODUCT_CONST»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM_EQ := Session.SUBSET_ANTISYM_EQ
  SUBSET_TRANS := Session.SUBSET_TRANS
  basis_discriminant := SessionLibrary.RingDet.«basis_discriminant»
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  number_field_codifferent := SessionANT.Different.«number_field_codifferent»
  number_field_different := SessionANT.Different.«number_field_different»
  number_field_ideal_norm := SessionANT.IdealNormExtension.«number_field_ideal_norm»

/-- What discriminant_extension.ml uses from Session. -/
def deps : HolANT.DiscriminantExtension.DiscriminantExtensionDeps where
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

/- The bundles, in discriminant_extension.ml order. -/
initialize BDiscriminantExtension01 : HolANT.DiscriminantExtension.DiscriminantExtension01 ←
  ioB "setupDiscriminantExtension01" (HolANT.DiscriminantExtension.setupDiscriminantExtension01 deps).run
initialize BDiscriminantExtension02 : HolANT.DiscriminantExtension.DiscriminantExtension02 ←
  ioB "setupDiscriminantExtension02" (HolANT.DiscriminantExtension.setupDiscriminantExtension02 deps BDiscriminantExtension01).run

-- DiscriminantExtension01
def NUMBER_FIELD_BASIS_DISCRIMINANT_TWIST : thm := BDiscriminantExtension01.NUMBER_FIELD_BASIS_DISCRIMINANT_TWIST
def NUMBER_FIELD_DIFFERENT_LOCAL_GENERATOR : thm := BDiscriminantExtension01.NUMBER_FIELD_DIFFERENT_LOCAL_GENERATOR
def NUMBER_FIELD_BASIS_DISCRIMINANT_IN_NORM_DIFFERENT : thm := BDiscriminantExtension01.NUMBER_FIELD_BASIS_DISCRIMINANT_IN_NORM_DIFFERENT
def NUMBER_FIELD_CODIFFERENT_LOCAL_DUAL : thm := BDiscriminantExtension01.NUMBER_FIELD_CODIFFERENT_LOCAL_DUAL
def NUMBER_FIELD_BASIS_DISCRIMINANT_TWIST_LOCAL : thm := BDiscriminantExtension01.NUMBER_FIELD_BASIS_DISCRIMINANT_TWIST_LOCAL

-- DiscriminantExtension02
def NUMBER_FIELD_NORM_DIFFERENT_LOCAL_BASIS : thm := BDiscriminantExtension02.NUMBER_FIELD_NORM_DIFFERENT_LOCAL_BASIS
def NUMBER_FIELD_DISCRIMINANT_BASES : thm := BDiscriminantExtension02.NUMBER_FIELD_DISCRIMINANT_BASES
def NUMBER_FIELD_DISCRIMINANT_RAMIFIED : thm := BDiscriminantExtension02.NUMBER_FIELD_DISCRIMINANT_RAMIFIED
def NUMBER_FIELD_DISCRIMINANT_TOWER : thm := BDiscriminantExtension02.NUMBER_FIELD_DISCRIMINANT_TOWER
def NUMBER_FIELD_DISCRIMINANT_TOWER_Q : thm := BDiscriminantExtension02.NUMBER_FIELD_DISCRIMINANT_TOWER_Q
def NUMBER_FIELD_DISCRIMINANT_POW_DIVIDES : thm := BDiscriminantExtension02.NUMBER_FIELD_DISCRIMINANT_POW_DIVIDES

/-- `needs "ANT/discriminant_extension.ml"`: already done by importing this module. -/
def ensureDiscriminantExtension : IO Unit := pure ()

end SessionANT.DiscriminantExtension
