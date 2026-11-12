/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/cyclotomic_subfields.ml                       . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/CyclotomicSubfields.lean

  The session half of the cyclotomic_subfields.ml translation: it supplies HolANT.CyclotomicSubfields's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/cyclotomic_subfields.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.CyclotomicSubfields
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
import SessionLibrary.Multiplicative
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
import SessionLibrary.SymmetricGroup
import SessionLibrary.Galois
import SessionLibrary.Integer
import SessionLibrary.Isum
import SessionLibrary.Primitive
import SessionLibrary.ModmulGroup
import SessionANT.Algmisc
import SessionANT.Integral
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.IdealArith
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionANT.RingOfIntegers
import SessionANT.PrimeSplit
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.NormIndex
import SessionANT.Classgroup
import SessionANT.Discriminant
import SessionANT.TraceForm
import SessionANT.RelativeSplit
import SessionLibrary.RingGroups
import SessionLibrary.FiniteFields
import SessionANT.CyclotomicPoly
import SessionANT.RelativeDegree
import SessionANT.NfValuation
import SessionANT.Integrality
import SessionANT.DedekindKummer
import SessionANT.PowerBasis
import SessionANT.CyclotomicField
import SessionANT.CyclotomicIntegers
import SessionLibrary.Cyclotomic
import SessionANT.CyclotomicGalois

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.CyclotomicSubfields

/-- The core theorems cyclotomic_subfields.ml uses. -/
def core1 : HolANT.CyclotomicSubfields.CoreThms1 where
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARRIER_SUBFIELD_GENERATED_SUBFIELD := SessionLibrary.FieldTheory.«CARRIER_SUBFIELD_GENERATED_SUBFIELD»
  CONG_SOLVE := SessionLibrary.Pocklington.«CONG_SOLVE»
  COPRIME_0 := SessionLibrary.Prime.«COPRIME_0»
  COPRIME_1 := SessionLibrary.Prime.«COPRIME_1»
  CYCLOTOMIC_FIELD_DEGREE := SessionANT.CyclotomicField.«CYCLOTOMIC_FIELD_DEGREE»
  CYCLOTOMIC_FIELD_GALOIS_EXTENSION := SessionANT.CyclotomicGalois.«CYCLOTOMIC_FIELD_GALOIS_EXTENSION»
  CYCLOTOMIC_FIELD_GALOIS_GROUP_EQ := SessionANT.CyclotomicGalois.«CYCLOTOMIC_FIELD_GALOIS_GROUP_EQ»
  CYCLOTOMIC_FIELD_GALOIS_GROUP_EXISTS := SessionANT.CyclotomicGalois.«CYCLOTOMIC_FIELD_GALOIS_GROUP_EXISTS»
  CYCLOTOMIC_FIELD_GALOIS_GROUP_HAS_SIZE := SessionANT.CyclotomicGalois.«CYCLOTOMIC_FIELD_GALOIS_GROUP_HAS_SIZE»
  CYCLOTOMIC_FIELD_GALOIS_GROUP_MODMUL := SessionANT.CyclotomicGalois.«CYCLOTOMIC_FIELD_GALOIS_GROUP_MODMUL»
  CYCLOTOMIC_FIELD_RING_OF_INTEGERS := SessionANT.CyclotomicIntegers.«CYCLOTOMIC_FIELD_RING_OF_INTEGERS»
  CYCLOTOMIC_POLY_EVAL_1 := SessionANT.CyclotomicPoly.«CYCLOTOMIC_POLY_EVAL_1»
  CYCLOTOMIC_POLY_SPLITS := SessionANT.CyclotomicPoly.«CYCLOTOMIC_POLY_SPLITS»
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DIVIDES_LE := Session.DIVIDES_LE
  DIVIDES_LMUL := SessionLibrary.Prime.«DIVIDES_LMUL»
  DIVIDES_REFL := SessionLibrary.Prime.«DIVIDES_REFL»
  DIVIDES_REXP := SessionLibrary.Prime.«DIVIDES_REXP»
  DIVIDES_RMUL := SessionLibrary.Prime.«DIVIDES_RMUL»
  DIV_MULT := Session.DIV_MULT
  EMPTY_SUBSET := Session.EMPTY_SUBSET
  EQ_MULT_LCANCEL := Session.EQ_MULT_LCANCEL
  EQ_TRANS := Session.EQ_TRANS
  EXP := Session.EXP
  EXTENSION := Session.EXTENSION
  EXTENSION_DEGREE_EQ_1 := SessionLibrary.FieldTheory.«EXTENSION_DEGREE_EQ_1»
  EXTENSION_DEGREE_TOWER_LAW := SessionLibrary.FieldTheory.«EXTENSION_DEGREE_TOWER_LAW»
  FIELD_ADD_INV_EQ := SessionLibrary.RingTheory.«FIELD_ADD_INV_EQ»
  FIELD_DIV_EQ_MUL := SessionLibrary.RingTheory.«FIELD_DIV_EQ_MUL»
  FIELD_EXTENSION_SUBFIELD_GENERATED_SUBSET := SessionLibrary.FieldTheory.«FIELD_EXTENSION_SUBFIELD_GENERATED_SUBSET»
  FIELD_HOMOMORPHISM_INV := SessionLibrary.RingTheory.«FIELD_HOMOMORPHISM_INV»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_MUL_LINV := SessionLibrary.RingTheory.«FIELD_MUL_LINV»
  FIELD_NONTRIVIAL := SessionLibrary.RingTheory.«FIELD_NONTRIVIAL»
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FIELD_UNIT := SessionLibrary.RingTheory.«FIELD_UNIT»
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_SING := Session.FINITE_SING
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_UNWIND_THM2 := Session.FORALL_UNWIND_THM2
  FUNDAMENTAL_THEOREM_OF_GALOIS_THEORY := SessionLibrary.Galois.«FUNDAMENTAL_THEOREM_OF_GALOIS_THEORY»
  GALOIS_COMPOSITUM_DEGREE := SessionLibrary.Galois.«GALOIS_COMPOSITUM_DEGREE»
  GALOIS_CYCLIC_INTERMEDIATE_UNIQUE := SessionLibrary.Galois.«GALOIS_CYCLIC_INTERMEDIATE_UNIQUE»
  GALOIS_GROUP_I := SessionLibrary.Galois.«GALOIS_GROUP_I»
  GALOIS_GROUP_IN_CARRIER := SessionLibrary.Galois.«GALOIS_GROUP_IN_CARRIER»
  GALOIS_GROUP_PERMUTES := SessionLibrary.Galois.«GALOIS_GROUP_PERMUTES»
  GALOIS_GROUP_RING_AUTOMORPHISM := SessionLibrary.Galois.«GALOIS_GROUP_RING_AUTOMORPHISM»
  GALOIS_GROUP_RING_HOMOMORPHISM := SessionLibrary.Galois.«GALOIS_GROUP_RING_HOMOMORPHISM»
  GALOIS_GROUP_RING_MONOMORPHISM := SessionLibrary.Galois.«GALOIS_GROUP_RING_MONOMORPHISM»
  GCD_ZERO := SessionLibrary.Prime.«GCD_ZERO»
  HAS_SIZE := Session.HAS_SIZE
  IMAGE_I := Session.IMAGE_I
  INSERT_SUBSET := Session.INSERT_SUBSET
  INTEGRAL_DOMAIN_ASSOCIATES := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_ASSOCIATES»
  INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING»
  INTEGRAL_DOMAIN_REGULAR := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_REGULAR»
  INTEGRAL_DOMAIN_RING_OF_INTEGERS := SessionANT.Numfield.«INTEGRAL_DOMAIN_RING_OF_INTEGERS»
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_FIXED_FIELD := SessionLibrary.Galois.«IN_FIXED_FIELD»
  IN_GALOIS_GROUP_SUBFIELD_GENERATED := SessionLibrary.Galois.«IN_GALOIS_GROUP_SUBFIELD_GENERATED»
  IN_INSERT := Session.IN_INSERT
  IN_INTER := Session.IN_INTER
  IN_SING := Session.IN_SING
  ISOMORPHIC_GROUP_CYCLICITY := SessionLibrary.GroupTheory.«ISOMORPHIC_GROUP_CYCLICITY»
  I_O_ID := Session.I_O_ID
  I_THM := Session.I_THM
  LCM_ZERO := SessionLibrary.Prime.«LCM_ZERO»
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MONO_EXISTS := Session.MONO_EXISTS
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_EQ_0 := Session.MULT_EQ_0
  MULT_SYM := Session.MULT_SYM
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q := SessionANT.PrimeSplit.«NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q»
  NUMBER_FIELD_SUBFIELD_GENERATED_ALGEBRAIC := SessionANT.Numfield.«NUMBER_FIELD_SUBFIELD_GENERATED_ALGEBRAIC»
  PERMUTES_I := SessionLibrary.Permutations.«PERMUTES_I»
  PHI_EQ_0 := SessionLibrary.Pocklington.«PHI_EQ_0»
  PHI_LCM_GCD := SessionLibrary.Multiplicative.«PHI_LCM_GCD»
  POLY_EVAL_CONST := SessionLibrary.RingTheory.«POLY_EVAL_CONST»
  POLY_EVAL_RING_PRODUCT := SessionLibrary.RingTheory.«POLY_EVAL_RING_PRODUCT»
  POLY_EVAL_SUB := SessionLibrary.RingTheory.«POLY_EVAL_SUB»
  POLY_EVAL_VAR := SessionLibrary.RingTheory.«POLY_EVAL_VAR»
  PRIMEPOW_FACTOR := SessionLibrary.Prime.«PRIMEPOW_FACTOR»
  PRIME_1 := SessionLibrary.Prime.«PRIME_1»
  PRIME_2 := SessionLibrary.Prime.«PRIME_2»
  PRIME_FACTOR := SessionLibrary.Prime.«PRIME_FACTOR»
  PRIME_GE_2 := SessionLibrary.Prime.«PRIME_GE_2»
  PRIME_SUBFIELD_MINIMAL := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_MINIMAL»
  PRIME_SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_SUBFIELD_GENERATED»
  RINGS_EQ := SessionLibrary.RingTheory.«RINGS_EQ»
  RING_0 := SessionLibrary.RingTheory.«RING_0»
/-- The core theorems cyclotomic_subfields.ml uses. -/
def core2 : HolANT.CyclotomicSubfields.CoreThms2 where
  RING_0_IN_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_0_IN_SUBRING_GENERATED»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_1_IN_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_1_IN_SUBRING_GENERATED»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_ADD_IN_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_ADD_IN_SUBRING_GENERATED»
  RING_ADD_LZERO := SessionLibrary.RingTheory.«RING_ADD_LZERO»
  RING_ADD_RZERO := SessionLibrary.RingTheory.«RING_ADD_RZERO»
  RING_ADD_SYM := SessionLibrary.RingTheory.«RING_ADD_SYM»
  RING_ASSOCIATES_PRIME_POWER_ORDER := SessionANT.CyclotomicIntegers.«RING_ASSOCIATES_PRIME_POWER_ORDER»
  RING_ASSOCIATES_UNIT := SessionLibrary.RingTheory.«RING_ASSOCIATES_UNIT»
  RING_AUTOMORPHISM_I := SessionLibrary.RingTheory.«RING_AUTOMORPHISM_I»
  RING_CARRIER_SUBFIELD_GENERATED_SUBSET := SessionLibrary.FieldTheory.«RING_CARRIER_SUBFIELD_GENERATED_SUBSET»
  RING_CARRIER_SUBRING_GENERATED_SUBSET := SessionLibrary.RingTheory.«RING_CARRIER_SUBRING_GENERATED_SUBSET»
  RING_DIVIDES_SUB_POW := SessionLibrary.RingTheory.«RING_DIVIDES_SUB_POW»
  RING_DIV_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_DIV_IN_SUBFIELD_GENERATED»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_ADD := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_ADD»
  RING_HOMOMORPHISM_SUBFIELD_INCLUSION := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_SUBFIELD_INCLUSION»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_INV_INV := SessionLibrary.RingTheory.«RING_INV_INV»
  RING_ISOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_ISOMORPHISM_IMP_HOMOMORPHISM»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_IN_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_MUL_IN_SUBRING_GENERATED»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_NEG_IN_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_NEG_IN_SUBRING_GENERATED»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_ALGEBRAIC := SessionANT.Numfield.«RING_OF_INTEGERS_ALGEBRAIC»
  RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE_EQ := SessionANT.RelativeSplit.«RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE_EQ»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_ORDER_1 := SessionLibrary.RingTheory.«RING_ORDER_1»
  RING_ORDER_DIVIDES := SessionLibrary.RingTheory.«RING_ORDER_DIVIDES»
  RING_ORDER_EQ_1 := SessionLibrary.RingTheory.«RING_ORDER_EQ_1»
  RING_ORDER_LCM_EXISTS := SessionLibrary.RingTheory.«RING_ORDER_LCM_EXISTS»
  RING_ORDER_POW := SessionLibrary.RingTheory.«RING_ORDER_POW»
  RING_ORDER_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_ORDER_SUBFIELD_GENERATED»
  RING_ORDER_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_ORDER_SUBRING_GENERATED»
  RING_POLYNOMIAL := SessionLibrary.RingTheory.«RING_POLYNOMIAL»
  RING_POLYNOMIAL_CONST := SessionLibrary.RingTheory.«RING_POLYNOMIAL_CONST»
  RING_POLYNOMIAL_SUB := SessionLibrary.RingTheory.«RING_POLYNOMIAL_SUB»
  RING_POLYNOMIAL_VAR := SessionLibrary.RingTheory.«RING_POLYNOMIAL_VAR»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_1 := SessionLibrary.RingTheory.«RING_POW_1»
  RING_POW_2 := SessionLibrary.RingTheory.«RING_POW_2»
  RING_POW_EQ := SessionLibrary.RingTheory.«RING_POW_EQ»
  RING_POW_IN_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_POW_IN_SUBRING_GENERATED»
  RING_POW_ONE := SessionLibrary.RingTheory.«RING_POW_ONE»
  RING_POW_POW := SessionLibrary.RingTheory.«RING_POW_POW»
  RING_POW_RING_ORDER := SessionLibrary.RingTheory.«RING_POW_RING_ORDER»
  RING_POW_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_POW_SUBFIELD_GENERATED»
  RING_POW_ZERO := SessionLibrary.RingTheory.«RING_POW_ZERO»
  RING_PRODUCT := SessionLibrary.RingTheory.«RING_PRODUCT»
  RING_PRODUCT_DELETE := SessionLibrary.RingDet.«RING_PRODUCT_DELETE»
  RING_PRODUCT_EQ := SessionLibrary.RingTheory.«RING_PRODUCT_EQ»
  RING_PRODUCT_RING_OF_INTEGERS := SessionANT.Numfield.«RING_PRODUCT_RING_OF_INTEGERS»
  RING_RINV_UNIQUE := SessionLibrary.RingTheory.«RING_RINV_UNIQUE»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_EQ_0 := SessionLibrary.RingTheory.«RING_SUB_EQ_0»
  RING_SUB_REFL := SessionLibrary.RingTheory.«RING_SUB_REFL»
  RING_SUB_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_SUB_SUBFIELD_GENERATED»
  RING_UNIT_0 := SessionLibrary.RingTheory.«RING_UNIT_0»
  RING_UNIT_NOT_IN_PRIME_IDEAL := SessionLibrary.RingTheory.«RING_UNIT_NOT_IN_PRIME_IDEAL»
  RING_UNIT_POW := SessionLibrary.RingTheory.«RING_UNIT_POW»
  ROOT_OF_UNITY_IN_RING_OF_INTEGERS := SessionANT.Numfield.«ROOT_OF_UNITY_IN_RING_OF_INTEGERS»
  SING_SUBSET := Session.SING_SUBSET
  SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED»
  SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED»
  SUBFIELD_GENERATED_IDEMPOT := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_IDEMPOT»
  SUBFIELD_GENERATED_INC := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_INC»
  SUBFIELD_GENERATED_MINIMAL := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_MINIMAL»
  SUBFIELD_GENERATED_MONO := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_MONO»
  SUBFIELD_GENERATED_ROOT_OF_UNITY := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_ROOT_OF_UNITY»
  SUBFIELD_GENERATED_ROOT_OF_UNITY_EQ := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_ROOT_OF_UNITY_EQ»
  SUBFIELD_GENERATED_SUBSET_EQ := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_SUBSET_EQ»
  SUBFIELD_GENERATED_UNION := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_UNION»
  SUBFIELD_OF_INTER := SessionLibrary.FieldTheory.«SUBFIELD_OF_INTER»
  SUBFIELD_SUBFIELD_GENERATED_EQ := SessionLibrary.FieldTheory.«SUBFIELD_SUBFIELD_GENERATED_EQ»
  SUBRING_GENERATED := SessionLibrary.RingTheory.«SUBRING_GENERATED»
  SUBRING_GENERATED_INC_GEN := SessionLibrary.RingTheory.«SUBRING_GENERATED_INC_GEN»
  SUBRING_GENERATED_MINIMAL := SessionLibrary.RingTheory.«SUBRING_GENERATED_MINIMAL»
  SUBRING_SUBRING_GENERATED := SessionLibrary.RingTheory.«SUBRING_SUBRING_GENERATED»
  SUBRING_SUBSET_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBRING_SUBSET_SUBFIELD_GENERATED»
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUBSET_INTER := Session.SUBSET_INTER
  coprime := Session.coprime
  divides := Session.divides
  isomorphic_group := SessionLibrary.GroupTheory.«isomorphic_group»
  number_field := SessionANT.Numfield.«number_field»
  ring_associates := SessionLibrary.RingTheory.«ring_associates»
  ring_automorphism := SessionLibrary.RingTheory.«ring_automorphism»
  ring_monomorphism := SessionLibrary.RingTheory.«ring_monomorphism»
  ring_of_integers := SessionANT.Numfield.«ring_of_integers»
  ring_pow := SessionLibrary.RingTheory.«ring_pow»
  ring_sub := SessionLibrary.RingTheory.«ring_sub»
  ring_unit := SessionLibrary.RingTheory.«ring_unit»
  subring_of := SessionLibrary.RingTheory.«subring_of»

/-- What cyclotomic_subfields.ml uses from Session. -/
def deps : HolANT.CyclotomicSubfields.CyclotomicSubfieldsDeps where
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
  NUM_RING := Session.NUM_RING
  core1 := core1
  core2 := core2

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in cyclotomic_subfields.ml order. -/
initialize BCyclotomicSubfields01 : HolANT.CyclotomicSubfields.CyclotomicSubfields01 ←
  ioB "setupCyclotomicSubfields01" (HolANT.CyclotomicSubfields.setupCyclotomicSubfields01 deps).run
initialize BCyclotomicSubfields02 : HolANT.CyclotomicSubfields.CyclotomicSubfields02 ←
  ioB "setupCyclotomicSubfields02" (HolANT.CyclotomicSubfields.setupCyclotomicSubfields02 deps).run

-- CyclotomicSubfields01
def CYCLOTOMIC_SUBFIELD_COMPOSITUM : thm := BCyclotomicSubfields01.CYCLOTOMIC_SUBFIELD_COMPOSITUM
def CYCLOTOMIC_SUBFIELD_DEGREE : thm := BCyclotomicSubfields01.CYCLOTOMIC_SUBFIELD_DEGREE
def CYCLOTOMIC_SUBFIELD_INTER : thm := BCyclotomicSubfields01.CYCLOTOMIC_SUBFIELD_INTER
def CYCLOTOMIC_FIELD_SUBFIELD_UNIQUE : thm := BCyclotomicSubfields01.CYCLOTOMIC_FIELD_SUBFIELD_UNIQUE
def CYCLOTOMIC_FIELD_INVERSION_EXISTS : thm := BCyclotomicSubfields01.CYCLOTOMIC_FIELD_INVERSION_EXISTS
def CYCLOTOMIC_FIELD_REAL_SUBFIELD : thm := BCyclotomicSubfields01.CYCLOTOMIC_FIELD_REAL_SUBFIELD
def CYCLOTOMIC_FIELD_REAL_SUBFIELD_RING_OF_INTEGERS : thm := BCyclotomicSubfields01.CYCLOTOMIC_FIELD_REAL_SUBFIELD_RING_OF_INTEGERS

-- CyclotomicSubfields02
def CYCLOTOMIC_UNIT : thm := BCyclotomicSubfields02.CYCLOTOMIC_UNIT
def ROOT_OF_UNITY_ONE_SUB_UNIT : thm := BCyclotomicSubfields02.ROOT_OF_UNITY_ONE_SUB_UNIT

/-- `needs "ANT/cyclotomic_subfields.ml"`: already done by importing this module. -/
def ensureCyclotomicSubfields : IO Unit := pure ()

end SessionANT.CyclotomicSubfields
