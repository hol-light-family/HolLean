/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/valuation_residue.ml                          . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/ValuationResidue.lean

  The session half of the valuation_residue.ml translation: it supplies HolANT.ValuationResidue's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/valuation_residue.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.ValuationResidue
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.Matroids
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.RingTheory
import SessionLibrary.Permutations
import SessionLibrary.RingDet
import SessionLibrary.FieldTheory
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
import SessionLibrary.SymmetricGroup
import SessionLibrary.Galois
import SessionANT.Integral
import SessionANT.IdealArith
import SessionLibrary.Products
import SessionANT.Algmisc
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.ValuationRing
import SessionLibrary.Isum
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.IdealNorm
import SessionANT.RingOfIntegers
import SessionANT.NormIndex
import SessionANT.Classgroup
import SessionANT.NfValuation
import SessionANT.PrimeSplit
import SessionANT.Discriminant
import SessionANT.TraceForm
import SessionANT.RelativeSplit
import SessionLibrary.RingGroups
import SessionLibrary.FiniteFields
import SessionANT.Decomposition
import SessionANT.RelativeDegree
import SessionANT.FiniteFieldTrace
import SessionANT.Ramification
import SessionANT.SplittingTypes
import SessionANT.NfDecomposition

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.ValuationResidue

/-- The core theorems valuation_residue.ml uses. -/
def core1 : HolANT.ValuationResidue.CoreThms1 where
  ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD := SessionLibrary.FieldTheory.«ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD»
  ALGEBRAIC_OVER_DIV := SessionLibrary.FieldTheory.«ALGEBRAIC_OVER_DIV»
  CARRIER_SUBFIELD_GENERATED_SUBFIELD := SessionLibrary.FieldTheory.«CARRIER_SUBFIELD_GENERATED_SUBFIELD»
  CARRIER_SUBRING_GENERATED_SUBRING := SessionLibrary.RingTheory.«CARRIER_SUBRING_GENERATED_SUBRING»
  COEFF := SessionLibrary.RingTheory.«COEFF»
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  DECOMPOSITION_GROUP := SessionANT.Decomposition.«DECOMPOSITION_GROUP»
  DECOMPOSITION_GROUP_RESIDUE_HOMOMORPHISM := SessionANT.Decomposition.«DECOMPOSITION_GROUP_RESIDUE_HOMOMORPHISM»
  DECOMPOSITION_GROUP_RING_OF_INTEGERS := SessionANT.NfDecomposition.«DECOMPOSITION_GROUP_RING_OF_INTEGERS»
  DEDEKIND_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«DEDEKIND_RING_OF_INTEGERS»
  DEDEKIND_VALUATION_IMAGE := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_IMAGE»
  DEDEKIND_VALUATION_INV := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_INV»
  DEDEKIND_VALUATION_MUL := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_MUL»
  DEDEKIND_VALUATION_POS := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_POS»
  DEDEKIND_VALUATION_PRIME_IDEAL := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_PRIME_IDEAL»
  DIVIDES_ONE := Session.DIVIDES_ONE
  EQ_IMP := Session.EQ_IMP
  ETA_AX := Session.ETA_AX
  EXTENSION := Session.EXTENSION
  FIELD_EXTENSION_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_EXTENSION_SUBFIELD_GENERATED»
  FIELD_HOMOMORPHISM_INV := SessionLibrary.RingTheory.«FIELD_HOMOMORPHISM_INV»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_INV_EQ_0 := SessionLibrary.RingTheory.«FIELD_INV_EQ_0»
  FIELD_MUL_RINV := SessionLibrary.RingTheory.«FIELD_MUL_RINV»
  FIELD_QUOTIENT_RING := SessionLibrary.RingTheory.«FIELD_QUOTIENT_RING»
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FIELD_UNIT := SessionLibrary.RingTheory.«FIELD_UNIT»
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FUN_EQ_THM := Session.FUN_EQ_THM
  GALOIS_GROUP_IMAGE_INVERSE := SessionLibrary.Galois.«GALOIS_GROUP_IMAGE_INVERSE»
  GALOIS_GROUP_INVERSE := SessionLibrary.Galois.«GALOIS_GROUP_INVERSE»
  GALOIS_GROUP_PERMUTES := SessionLibrary.Galois.«GALOIS_GROUP_PERMUTES»
  GALOIS_GROUP_RING_HOMOMORPHISM := SessionLibrary.Galois.«GALOIS_GROUP_RING_HOMOMORPHISM»
  GALOIS_GROUP_RING_OF_INTEGERS := SessionANT.NfDecomposition.«GALOIS_GROUP_RING_OF_INTEGERS»
  IMAGE_I := Session.IMAGE_I
  IMP_CONJ := Session.IMP_CONJ
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INTEGRAL_DOMAIN_CHAR := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_CHAR»
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  INTEGRAL_DOMAIN_SUBRING_GENERATED := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_SUBRING_GENERATED»
  INTEGRAL_ELEMENT_OVER_SUBRING := SessionANT.Integral.«INTEGRAL_ELEMENT_OVER_SUBRING»
  INT_LT_IMP_LE := Session.INT_LT_IMP_LE
  INT_NOT_LT := Session.INT_NOT_LT
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_INTER := Session.IN_INTER
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_RING_IDEAL_LMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_LMUL»
  IN_RING_IDEAL_RMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_RMUL»
  IN_RING_IDEAL_SUB := SessionLibrary.RingTheory.«IN_RING_IDEAL_SUB»
  IN_UNIV := Session.IN_UNIV
  I_DEF := Session.I_DEF
  I_O_ID := Session.I_O_ID
  I_THM := Session.I_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  MAXIMAL_IMP_PRIME_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_PRIME_IDEAL»
  MAXIMAL_IMP_RING_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_RING_IDEAL»
  MONIC_CMUL := SessionLibrary.RingTheory.«MONIC_CMUL»
  MONO_EXISTS := Session.MONO_EXISTS
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  PERMUTES_INJECTIVE := SessionLibrary.Permutations.«PERMUTES_INJECTIVE»
  PERMUTES_INVERSES := SessionLibrary.Permutations.«PERMUTES_INVERSES»
  PERMUTES_IN_IMAGE := SessionLibrary.Permutations.«PERMUTES_IN_IMAGE»
  POLY_DEG_EQ_COEFF_EQ := SessionLibrary.RingTheory.«POLY_DEG_EQ_COEFF_EQ»
  POLY_EVAL_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_EVAL_HOMOMORPHIC_IMAGE»
  POLY_EVAL_SUBRING_GENERATED := SessionLibrary.RingTheory.«POLY_EVAL_SUBRING_GENERATED»
  POLY_EXTEND_CONST := SessionLibrary.RingTheory.«POLY_EXTEND_CONST»
  POLY_EXTEND_MUL := SessionLibrary.RingTheory.«POLY_EXTEND_MUL»
  POLY_RING := SessionLibrary.RingTheory.«POLY_RING»
  PRIME_1 := SessionLibrary.Prime.«PRIME_1»
  PRIME_IDEAL_HOMOMORPHIC_PREIMAGE := SessionLibrary.RingTheory.«PRIME_IDEAL_HOMOMORPHIC_PREIMAGE»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PRIME_INT_DIVPROD_EQ := SessionLibrary.Prime.«PRIME_INT_DIVPROD_EQ»
  PRIME_SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_SUBFIELD_GENERATED»
  PRIME_SUBRING := SessionLibrary.RingTheory.«PRIME_SUBRING»
  PROPER_IDEAL := SessionLibrary.RingTheory.«PROPER_IDEAL»
  QUOTIENT_RING_0 := SessionLibrary.RingTheory.«QUOTIENT_RING_0»
  QUOTIENT_RING_CARRIER := SessionLibrary.RingTheory.«QUOTIENT_RING_CARRIER»
  QUOTIENT_RING_MUL := SessionLibrary.RingTheory.«QUOTIENT_RING_MUL»
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_CHAR_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_CHAR_SUBFIELD_GENERATED»
/-- The core theorems valuation_residue.ml uses. -/
def core2 : HolANT.ValuationResidue.CoreThms2 where
  RING_CHAR_UNIQUE := SessionLibrary.RingTheory.«RING_CHAR_UNIQUE»
  RING_COSET_EQ_IDEAL := SessionLibrary.RingTheory.«RING_COSET_EQ_IDEAL»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_BETWEEN_SUBRINGS := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_BETWEEN_SUBRINGS»
  RING_HOMOMORPHISM_I := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_I»
  RING_HOMOMORPHISM_INCLUSION := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INCLUSION»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_RING_COSET := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_COSET»
  RING_HOMOMORPHISM_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_INT»
  RING_HOMOMORPHISM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_HOMOMORPHISM_RING_OF_INTEGERS»
  RING_HOMOMORPHISM_RING_OF_NUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_NUM»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_INV_INV := SessionLibrary.RingTheory.«RING_INV_INV»
  RING_INV_MUL := SessionLibrary.RingTheory.«RING_INV_MUL»
  RING_INV_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_INV_SUBFIELD_GENERATED»
  RING_MONOMORPHISM_INCLUSION := SessionLibrary.RingTheory.«RING_MONOMORPHISM_INCLUSION»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_ALGEBRAIC := SessionANT.Numfield.«RING_OF_INTEGERS_ALGEBRAIC»
  RING_OF_INTEGERS_CARRIER := SessionANT.Numfield.«RING_OF_INTEGERS_CARRIER»
  RING_OF_INTEGERS_FRACTION_FIELD := SessionANT.NfValuation.«RING_OF_INTEGERS_FRACTION_FIELD»
  RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE := SessionANT.RelativeSplit.«RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE»
  RING_OF_INTEGERS_SUBFIELD_GENERATED := SessionANT.RelativeSplit.«RING_OF_INTEGERS_SUBFIELD_GENERATED»
  RING_OF_INTEGERS_SUBRING := SessionANT.Numfield.«RING_OF_INTEGERS_SUBRING»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INT_0 := SessionLibrary.RingTheory.«RING_OF_INT_0»
  RING_OF_INT_1 := SessionLibrary.RingTheory.«RING_OF_INT_1»
  RING_OF_INT_ADD := SessionLibrary.RingTheory.«RING_OF_INT_ADD»
  RING_OF_INT_EQ := SessionLibrary.RingTheory.«RING_OF_INT_EQ»
  RING_OF_INT_EQ_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_0»
  RING_OF_INT_MUL := SessionLibrary.RingTheory.«RING_OF_INT_MUL»
  RING_OF_INT_NEG := SessionLibrary.RingTheory.«RING_OF_INT_NEG»
  RING_OF_INT_OF_NUM := SessionLibrary.RingTheory.«RING_OF_INT_OF_NUM»
  RING_OF_INT_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_INT_SUBFIELD_GENERATED»
  RING_OF_INT_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_OF_INT_SUBRING_GENERATED»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_OF_NUM_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_OF_NUM_SUBRING_GENERATED»
  RING_POLYNOMIAL := SessionLibrary.RingTheory.«RING_POLYNOMIAL»
  RING_POLYNOMIAL_CONST := SessionLibrary.RingTheory.«RING_POLYNOMIAL_CONST»
  RING_POLYNOMIAL_MUL := SessionLibrary.RingTheory.«RING_POLYNOMIAL_MUL»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_SUB_SUBRING_GENERATED»
  RING_UNIT_SUBRING_OF_FIELD := SessionLibrary.RingTheory.«RING_UNIT_SUBRING_OF_FIELD»
  SIMPLE_IMAGE := Session.SIMPLE_IMAGE
  SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED»
  SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED»
  SUBFIELD_GENERATED_INC_GEN := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_INC_GEN»
  SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC»
  SUBFIELD_OF_IMP_SUBSET := SessionLibrary.FieldTheory.«SUBFIELD_OF_IMP_SUBSET»
  SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_SUBFIELD_GENERATED»
  SUBRING_GENERATED := SessionLibrary.RingTheory.«SUBRING_GENERATED»
  SUBSET := Session.SUBSET
  SUBSET_REFL := Session.SUBSET_REFL
  SUBSET_UNIV := Session.SUBSET_UNIV
  VALUATION_SUBRING_DOMINATES := SessionANT.ValuationRing.«VALUATION_SUBRING_DOMINATES»
  VALUATION_SUBRING_INTEGRAL_ELEMENT := SessionANT.ValuationRing.«VALUATION_SUBRING_INTEGRAL_ELEMENT»
  VALUATION_SUBRING_INV_MAXIMAL_IDEAL := SessionANT.ValuationRing.«VALUATION_SUBRING_INV_MAXIMAL_IDEAL»
  VALUATION_SUBRING_MAXIMAL_IDEAL := SessionANT.ValuationRing.«VALUATION_SUBRING_MAXIMAL_IDEAL»
  VALUATION_SUBRING_SUBFIELD := SessionANT.ValuationRing.«VALUATION_SUBRING_SUBFIELD»
  algebraic_extension := SessionLibrary.FieldTheory.«algebraic_extension»
  algebraically_closed_field := SessionLibrary.FieldTheory.«algebraically_closed_field»
  decomposition_group := SessionANT.Decomposition.«decomposition_group»
  field_of_fractions := SessionLibrary.RingTheory.«field_of_fractions»
  inertia_group := SessionANT.Decomposition.«inertia_group»
  integral_element := SessionANT.Integral.«integral_element»
  num_divides := Session.num_divides
  number_field := SessionANT.Numfield.«number_field»
  o_THM := Session.o_THM
  poly_deg := SessionLibrary.RingTheory.«poly_deg»
  poly_eval := SessionLibrary.RingTheory.«poly_eval»
  poly_evaluate := SessionLibrary.RingTheory.«poly_evaluate»
  poly_extend := SessionLibrary.RingTheory.«poly_extend»
  prime_ideal := SessionLibrary.RingTheory.«prime_ideal»
  ring_div := SessionLibrary.RingTheory.«ring_div»
  ring_homomorphism := SessionLibrary.RingTheory.«ring_homomorphism»
  ring_ideal := SessionLibrary.RingTheory.«ring_ideal»
  ring_polynomial := SessionLibrary.RingTheory.«ring_polynomial»
  ring_powerseries := SessionLibrary.RingTheory.«ring_powerseries»
  subring_of := SessionLibrary.RingTheory.«subring_of»
  valuation_subring := SessionANT.ValuationRing.«valuation_subring»

/-- What valuation_residue.ml uses from Session. -/
def deps : HolANT.ValuationResidue.ValuationResidueDeps where
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
  core2 := core2

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in valuation_residue.ml order. -/
initialize BValuationResidue01 : HolANT.ValuationResidue.ValuationResidue01 ←
  ioB "setupValuationResidue01" (HolANT.ValuationResidue.setupValuationResidue01 deps).run
initialize BValuationResidue02 : HolANT.ValuationResidue.ValuationResidue02 ←
  ioB "setupValuationResidue02" (HolANT.ValuationResidue.setupValuationResidue02 deps BValuationResidue01).run
initialize BValuationResidue03 : HolANT.ValuationResidue.ValuationResidue03 ←
  ioB "setupValuationResidue03" (HolANT.ValuationResidue.setupValuationResidue03 deps BValuationResidue01 BValuationResidue02).run

-- ValuationResidue01
def VALUATION_SUBRING_RESIDUE_ALGEBRAICALLY_CLOSED : thm := BValuationResidue01.VALUATION_SUBRING_RESIDUE_ALGEBRAICALLY_CLOSED
def VALUATION_SUBRING_OVER_PRIME : thm := BValuationResidue01.VALUATION_SUBRING_OVER_PRIME
def VALUATION_SUBRING_RESIDUE_CHAR : thm := BValuationResidue01.VALUATION_SUBRING_RESIDUE_CHAR
def VALUATION_SUBRING_RESIDUE_CHAR_CASES : thm := BValuationResidue01.VALUATION_SUBRING_RESIDUE_CHAR_CASES
def ALGEBRAICALLY_CLOSED_VALUATION_OVER_PRIME : thm := BValuationResidue01.ALGEBRAICALLY_CLOSED_VALUATION_OVER_PRIME
def VALUATION_SUBRING_DECOMPOSITION_GROUP : thm := BValuationResidue01.VALUATION_SUBRING_DECOMPOSITION_GROUP
def VALUATION_SUBRING_RESIDUE_HOMOMORPHISM : thm := BValuationResidue01.VALUATION_SUBRING_RESIDUE_HOMOMORPHISM
def VALUATION_SUBRING_RESIDUE_DIV : thm := BValuationResidue01.VALUATION_SUBRING_RESIDUE_DIV
def VALUATION_SUBRING_RING_OF_INTEGERS : thm := BValuationResidue01.VALUATION_SUBRING_RING_OF_INTEGERS
def VALUATION_SUBRING_CONTRACTION_RING_OF_INTEGERS : thm := BValuationResidue01.VALUATION_SUBRING_CONTRACTION_RING_OF_INTEGERS
def VALUATION_SUBRING_DECOMPOSITION_RESIDUE : thm := BValuationResidue01.VALUATION_SUBRING_DECOMPOSITION_RESIDUE

-- ValuationResidue02
def NUMBER_FIELD_VALUATION_SUBRING_LOCALIZATION : thm := BValuationResidue02.NUMBER_FIELD_VALUATION_SUBRING_LOCALIZATION
def VALUATION_SUBRING_NUMBER_SUBFIELD : thm := BValuationResidue02.VALUATION_SUBRING_NUMBER_SUBFIELD
def VALUATION_SUBRING_NUMBER_SUBFIELD_VALUATION : thm := BValuationResidue02.VALUATION_SUBRING_NUMBER_SUBFIELD_VALUATION
def ALGEBRAIC_VALUATION_SUBRING_LOCALIZATION : thm := BValuationResidue02.ALGEBRAIC_VALUATION_SUBRING_LOCALIZATION
def ALGEBRAIC_VALUATION_SUBRING_RESIDUE_ALGEBRAIC : thm := BValuationResidue02.ALGEBRAIC_VALUATION_SUBRING_RESIDUE_ALGEBRAIC
def ALGEBRAIC_CLOSURE_VALUATION_OVER_PRIME : thm := BValuationResidue02.ALGEBRAIC_CLOSURE_VALUATION_OVER_PRIME
def ALGEBRAIC_VALUATION_SUBRING_DECOMPOSITION_GROUP : thm := BValuationResidue02.ALGEBRAIC_VALUATION_SUBRING_DECOMPOSITION_GROUP

-- ValuationResidue03
def ALGEBRAIC_VALUATION_SUBRING_DECOMPOSITION_INERTIA : thm := BValuationResidue03.ALGEBRAIC_VALUATION_SUBRING_DECOMPOSITION_INERTIA
def ALGEBRAIC_VALUATION_SUBRING_RESIDUE_HOMOMORPHISM : thm := BValuationResidue03.ALGEBRAIC_VALUATION_SUBRING_RESIDUE_HOMOMORPHISM

/-- `needs "ANT/valuation_residue.ml"`: already done by importing this module. -/
def ensureValuationResidue : IO Unit := pure ()

end SessionANT.ValuationResidue
