/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/numfield.ml                                   . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/Numfield.lean

  The session half of the numfield.ml translation: it supplies HolANT.Numfield's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/numfield.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.Numfield
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
import SessionLibrary.Isum
import SessionLibrary.Products
import SessionANT.Algmisc
import SessionANT.Integral
import SessionANT.Zlattice
import SessionLibrary.Floor

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.Numfield

/-- The core theorems numfield.ml uses. -/
def core1 : HolANT.Numfield.CoreThms1 where
  ALGEBRA_NORM_EQ_0 := SessionLibrary.FieldTheory.«ALGEBRA_NORM_EQ_0»
  ALGEBRA_NORM_MUL := SessionLibrary.RingDet.«ALGEBRA_NORM_MUL»
  ALGEBRA_NORM_SUBRING := SessionLibrary.RingDet.«ALGEBRA_NORM_SUBRING»
  ALGEBRA_NORM_SUB_CHARPOLY := SessionLibrary.RingDet.«ALGEBRA_NORM_SUB_CHARPOLY»
  ALGEBRA_TRACE_ADD := SessionLibrary.RingDet.«ALGEBRA_TRACE_ADD»
  ALGEBRA_TRACE_MUL_LINCOMB := SessionLibrary.RingDet.«ALGEBRA_TRACE_MUL_LINCOMB»
  ALGEBRA_TRACE_NORM_BASE := SessionLibrary.FieldTheory.«ALGEBRA_TRACE_NORM_BASE»
  ALGEBRA_TRACE_NORM_IN_CARRIER := SessionLibrary.RingDet.«ALGEBRA_TRACE_NORM_IN_CARRIER»
  ALGEBRA_TRACE_SCALAR := SessionLibrary.RingDet.«ALGEBRA_TRACE_SCALAR»
  ALGEBRA_TRACE_SUBRING := SessionLibrary.RingDet.«ALGEBRA_TRACE_SUBRING»
  BASIS_COORDINATES := SessionLibrary.RingDet.«BASIS_COORDINATES»
  CARRIER_SUBRING_GENERATED_SUBRING := SessionLibrary.RingTheory.«CARRIER_SUBRING_GENERATED_SUBRING»
  COND_RAND := Session.COND_RAND
  COND_RATOR := Session.COND_RATOR
  DIVIDES_ZERO := SessionLibrary.Prime.«DIVIDES_ZERO»
  EMPTY_GSPEC := Session.EMPTY_GSPEC
  EQ_IMP := Session.EQ_IMP
  EQ_MULT_LCANCEL := Session.EQ_MULT_LCANCEL
  EQ_TRANS := Session.EQ_TRANS
  ETA_AX := Session.ETA_AX
  EXTENSION := Session.EXTENSION
  EXTENSION_DEGREE_REFL := SessionLibrary.FieldTheory.«EXTENSION_DEGREE_REFL»
  EXTENSION_DEGREE_TOWER_LAW := SessionLibrary.FieldTheory.«EXTENSION_DEGREE_TOWER_LAW»
  EXTENSION_LINCOMB_LMUL := SessionLibrary.RingDet.«EXTENSION_LINCOMB_LMUL»
  EXTENSION_LINCOMB_MUL := SessionLibrary.RingDet.«EXTENSION_LINCOMB_MUL»
  EXTENSION_LINCOMB_SUM := SessionLibrary.RingDet.«EXTENSION_LINCOMB_SUM»
  EXTENSION_MUL_LINCOMB := SessionLibrary.RingDet.«EXTENSION_MUL_LINCOMB»
  FIELD_CHARPOLY_MINIMAL_POLYNOMIAL := SessionLibrary.FieldTheory.«FIELD_CHARPOLY_MINIMAL_POLYNOMIAL»
  FIELD_EXTENSION_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_EXTENSION_SUBFIELD_GENERATED»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«FIELD_IMP_NONTRIVIAL_RING»
  FIELD_MUL_LINV := SessionLibrary.RingTheory.«FIELD_MUL_LINV»
  FIELD_MUL_RINV := SessionLibrary.RingTheory.«FIELD_MUL_RINV»
  FIELD_NONTRIVIAL := SessionLibrary.RingTheory.«FIELD_NONTRIVIAL»
  FIELD_REAL_RING := SessionLibrary.RingTheory.«FIELD_REAL_RING»
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FIELD_UNIT := SessionLibrary.RingTheory.«FIELD_UNIT»
  FINITE_CROSS := Session.FINITE_CROSS
  FINITE_EXTENSION_BASIS := SessionLibrary.FieldTheory.«FINITE_EXTENSION_BASIS»
  FINITE_EXTENSION_FREE_BASIS := SessionLibrary.FieldTheory.«FINITE_EXTENSION_FREE_BASIS»
  FINITE_EXTENSION_ISOMORPHISM := SessionLibrary.FieldTheory.«FINITE_EXTENSION_ISOMORPHISM»
  FINITE_FINITELY_GENERATED_ALGEBRAIC_EXTENSION := SessionLibrary.FieldTheory.«FINITE_FINITELY_GENERATED_ALGEBRAIC_EXTENSION»
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_IMP_ALGEBRAIC_EXTENSION := SessionLibrary.FieldTheory.«FINITE_IMP_ALGEBRAIC_EXTENSION»
  FINITE_IMP_FIELD_EXTENSION := SessionLibrary.FieldTheory.«FINITE_IMP_FIELD_EXTENSION»
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_SING := Session.FINITE_SING
  FINITE_SUBSET_SUBFIELD_GENERATED_DENOMINATOR := SessionLibrary.FieldTheory.«FINITE_SUBSET_SUBFIELD_GENERATED_DENOMINATOR»
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  FORALL_UNWIND_THM2 := Session.FORALL_UNWIND_THM2
  FREE_BASIS_EXTENSION_DEGREE := SessionLibrary.FieldTheory.«FREE_BASIS_EXTENSION_DEGREE»
  FREE_BASIS_FIELD := SessionLibrary.FieldTheory.«FREE_BASIS_FIELD»
  FREE_BASIS_FROM_RING_BASIS := SessionLibrary.FieldTheory.«FREE_BASIS_FROM_RING_BASIS»
  FREE_BASIS_IN_CARRIER := SessionLibrary.RingDet.«FREE_BASIS_IN_CARRIER»
  FREE_BASIS_SCALE := SessionLibrary.RingDet.«FREE_BASIS_SCALE»
  FUN_EQ_THM := Session.FUN_EQ_THM
  IDEAL_GENERATED_EQ_0 := SessionLibrary.RingTheory.«IDEAL_GENERATED_EQ_0»
  IMAGE_I := Session.IMAGE_I
  IMP_CONJ := Session.IMP_CONJ
  IMP_IMP := Session.IMP_IMP
  IN := Session.IN
  INSERT_SUBSET := Session.INSERT_SUBSET
  INTEGER_REAL_OF_INT := Session.INTEGER_REAL_OF_INT
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INTEGER_RING_SUM := SessionLibrary.RingTheory.«INTEGER_RING_SUM»
  INTEGRAL_CLOSURE_SUBRING := SessionANT.Integral.«INTEGRAL_CLOSURE_SUBRING»
  INTEGRAL_CLOSURE_SUPSET_IMAGE := SessionANT.Integral.«INTEGRAL_CLOSURE_SUPSET_IMAGE»
  INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING»
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  INTEGRAL_DOMAIN_SUBRING_GENERATED := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_SUBRING_GENERATED»
  INTEGRAL_ELEMENT_EXPLICIT := SessionANT.Integral.«INTEGRAL_ELEMENT_EXPLICIT»
  INTEGRAL_ELEMENT_FINITE_MODULE := SessionANT.Integral.«INTEGRAL_ELEMENT_FINITE_MODULE»
  INTEGRAL_ELEMENT_HOMOMORPHIC_IMAGE := SessionANT.Integral.«INTEGRAL_ELEMENT_HOMOMORPHIC_IMAGE»
  INTEGRAL_ELEMENT_IMAGE := SessionANT.Integral.«INTEGRAL_ELEMENT_IMAGE»
  INTEGRAL_ELEMENT_MUL := SessionANT.Integral.«INTEGRAL_ELEMENT_MUL»
  INTEGRAL_ELEMENT_OVER_SUBRING := SessionANT.Integral.«INTEGRAL_ELEMENT_OVER_SUBRING»
  INTEGRAL_ELEMENT_PRIME_SUBFIELD := SessionANT.Integral.«INTEGRAL_ELEMENT_PRIME_SUBFIELD»
  INTEGRAL_OVER_FIELD_EQ_ALGEBRAIC := SessionANT.Integral.«INTEGRAL_OVER_FIELD_EQ_ALGEBRAIC»
  INT_LATTICE_FULL_RANK := SessionANT.Zlattice.«INT_LATTICE_FULL_RANK»
  INT_LATTICE_MATRIX_IMAGE := SessionANT.Zlattice.«INT_LATTICE_MATRIX_IMAGE»
  INT_MATRIX_IMAGE_INJECTIVE := SessionANT.Zlattice.«INT_MATRIX_IMAGE_INJECTIVE»
  INT_MUL_RID := Session.INT_MUL_RID
  INT_MUL_RZERO := Session.INT_MUL_RZERO
  INT_MUL_SYM := Session.INT_MUL_SYM
  INT_SUB_REFL := Session.INT_SUB_REFL
  IN_CROSS := Session.IN_CROSS
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IDEAL_GENERATED_SING_EQ := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SING_EQ»
  IN_IMAGE := Session.IN_IMAGE
  IN_INTER := Session.IN_INTER
  IN_SING := Session.IN_SING
  IN_SUBFIELD_0 := SessionLibrary.FieldTheory.«IN_SUBFIELD_0»
  IN_SUBRING_MUL := SessionLibrary.RingTheory.«IN_SUBRING_MUL»
  IN_UNIV := Session.IN_UNIV
  ISUM_0 := SessionLibrary.Isum.«ISUM_0»
  ISUM_DELTA_GEN := SessionLibrary.Isum.«ISUM_DELTA_GEN»
  I_O_ID := Session.I_O_ID
  I_THM := Session.I_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LT := Session.LT
  LT_NZ := Session.LT_NZ
  MINIMAL_POLYNOMIAL := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL»
  MONO_EXISTS := Session.MONO_EXISTS
  MONO_FORALL := Session.MONO_FORALL
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
/-- The core theorems numfield.ml uses. -/
def core2 : HolANT.Numfield.CoreThms2 where
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  POLY_EVAL_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«POLY_EVAL_SUBFIELD_GENERATED»
  POLY_POW_ALT := SessionLibrary.RingTheory.«POLY_POW_ALT»
  PRIME_SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_SUBFIELD_GENERATED»
  PRIME_SUBRING := SessionLibrary.RingTheory.«PRIME_SUBRING»
  REAL_RING_CHAR := SessionLibrary.RingTheory.«REAL_RING_CHAR»
  REAL_RING_CLAUSES := SessionLibrary.RingTheory.«REAL_RING_CLAUSES»
  REAL_RING_DIV := SessionLibrary.RingTheory.«REAL_RING_DIV»
  REAL_RING_OF_INT := SessionLibrary.RingTheory.«REAL_RING_OF_INT»
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RIGHT_IMP_EXISTS_THM := Session.RIGHT_IMP_EXISTS_THM
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD_EQ_RIGHT := SessionLibrary.RingTheory.«RING_ADD_EQ_RIGHT»
  RING_ADD_RNEG := SessionLibrary.RingTheory.«RING_ADD_RNEG»
  RING_CARRIER_SUBFIELD_GENERATED_SUBRING_QUOTIENTS := SessionLibrary.FieldTheory.«RING_CARRIER_SUBFIELD_GENERATED_SUBRING_QUOTIENTS»
  RING_CARRIER_SUBFIELD_GENERATED_SUBSET := SessionLibrary.FieldTheory.«RING_CARRIER_SUBFIELD_GENERATED_SUBSET»
  RING_CARRIER_SUBRING_GENERATED_0 := SessionLibrary.RingTheory.«RING_CARRIER_SUBRING_GENERATED_0»
  RING_CARRIER_SUBRING_GENERATED_SUBSET := SessionLibrary.RingTheory.«RING_CARRIER_SUBRING_GENERATED_SUBSET»
  RING_CHAR_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_CHAR_SUBFIELD_GENERATED»
  RING_HOMOMORPHISM_BETWEEN_SUBRINGS := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_BETWEEN_SUBRINGS»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  RING_HOMOMORPHISM_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_INT»
  RING_HOMOMORPHISM_SUBFIELD_INCLUSION := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_SUBFIELD_INCLUSION»
  RING_HOMOMORPHISM_SUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUM»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_INV_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_INV_IN_SUBFIELD_GENERATED»
  RING_ISOMORPHISM_I := SessionLibrary.RingTheory.«RING_ISOMORPHISM_I»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_ASSOC := SessionLibrary.RingTheory.«RING_MUL_ASSOC»
  RING_MUL_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_MUL_IN_SUBFIELD_GENERATED»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_LINV := SessionLibrary.RingTheory.«RING_MUL_LINV»
  RING_MUL_LNEG := SessionLibrary.RingTheory.«RING_MUL_LNEG»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_MUL_RINV := SessionLibrary.RingTheory.«RING_MUL_RINV»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_MUL_SYM := SessionLibrary.RingTheory.«RING_MUL_SYM»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_OF_INT_0 := SessionLibrary.RingTheory.«RING_OF_INT_0»
  RING_OF_INT_1 := SessionLibrary.RingTheory.«RING_OF_INT_1»
  RING_OF_INT_EQ_0_CHAR_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_0_CHAR_0»
  RING_OF_INT_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_INT_IN_SUBFIELD_GENERATED»
  RING_OF_INT_NEG := SessionLibrary.RingTheory.«RING_OF_INT_NEG»
  RING_OF_INT_OF_NUM := SessionLibrary.RingTheory.«RING_OF_INT_OF_NUM»
  RING_OF_INT_SUB := SessionLibrary.RingTheory.«RING_OF_INT_SUB»
  RING_OF_INT_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_INT_SUBFIELD_GENERATED»
  RING_OF_INT_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_OF_INT_SUBRING_GENERATED»
  RING_OF_NUM_0 := SessionLibrary.RingTheory.«RING_OF_NUM_0»
  RING_OF_NUM_1 := SessionLibrary.RingTheory.«RING_OF_NUM_1»
  RING_OF_NUM_EQ_0 := SessionLibrary.RingTheory.«RING_OF_NUM_EQ_0»
  RING_OF_NUM_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_NUM_SUBFIELD_GENERATED»
  RING_OF_NUM_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_OF_NUM_SUBRING_GENERATED»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_1 := SessionLibrary.RingTheory.«RING_POW_1»
  RING_POW_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_POW_SUBFIELD_GENERATED»
  RING_POW_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_POW_SUBRING_GENERATED»
  RING_PRODUCT_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_PRODUCT_SUBRING_GENERATED»
  RING_RINV_UNIQUE := SessionLibrary.RingTheory.«RING_RINV_UNIQUE»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_EQ_0 := SessionLibrary.RingTheory.«RING_SUB_EQ_0»
  RING_SUB_LDISTRIB := SessionLibrary.RingTheory.«RING_SUB_LDISTRIB»
  RING_SUB_RDISTRIB := SessionLibrary.RingTheory.«RING_SUB_RDISTRIB»
  RING_SUB_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_SUB_SUBRING_GENERATED»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_0 := SessionLibrary.RingTheory.«RING_SUM_0»
  RING_SUM_CLAUSES := SessionLibrary.RingTheory.«RING_SUM_CLAUSES»
  RING_SUM_DELTA := SessionLibrary.RingTheory.«RING_SUM_DELTA»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_EQ_0 := SessionLibrary.RingTheory.«RING_SUM_EQ_0»
  RING_SUM_LMUL := SessionLibrary.RingTheory.«RING_SUM_LMUL»
  RING_SUM_NEG := SessionLibrary.RingTheory.«RING_SUM_NEG»
  RING_SUM_SING := SessionLibrary.RingTheory.«RING_SUM_SING»
  RING_SUM_SUB := SessionLibrary.RingTheory.«RING_SUM_SUB»
  RING_SUM_SUBRING_GENERATED_GEN := SessionLibrary.RingTheory.«RING_SUM_SUBRING_GENERATED_GEN»
  RING_UNIT_0 := SessionLibrary.RingTheory.«RING_UNIT_0»
  RING_UNIT_IN_CARRIER := SessionLibrary.RingTheory.«RING_UNIT_IN_CARRIER»
  SING_GSPEC := Session.SING_GSPEC
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SUBFIELDS_GENERATED_EQ := SessionLibrary.FieldTheory.«SUBFIELDS_GENERATED_EQ»
  SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED»
  SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC»
  SUBFIELD_GENERATED_UNION_LEFT := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_UNION_LEFT»
  SUBRING_EQ_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBRING_EQ_SUBFIELD_GENERATED»
  SUBRING_GENERATED := SessionLibrary.RingTheory.«SUBRING_GENERATED»
  SUBRING_GENERATED_BY_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBRING_GENERATED_BY_SUBFIELD_GENERATED»
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM_EQ := Session.SUBSET_ANTISYM_EQ
  TRACE_FORM_NONDEGENERATE := SessionLibrary.RingDet.«TRACE_FORM_NONDEGENERATE»
  algebraic_extension := SessionLibrary.FieldTheory.«algebraic_extension»
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  finite_extension := SessionLibrary.FieldTheory.«finite_extension»
  free_basis := SessionLibrary.RingDet.«free_basis»
  int_eq := Session.int_eq
  int_lattice := SessionANT.Zlattice.«int_lattice»
  int_matrix_image := SessionANT.Zlattice.«int_matrix_image»
  int_of_num_th := Session.int_of_num_th
  int_tybij := Session.int_tybij
  isomorphic_ring := SessionLibrary.RingTheory.«isomorphic_ring»
  o_THM := Session.o_THM
  rational := SessionLibrary.Floor.«rational»
  ring_divides := SessionLibrary.RingTheory.«ring_divides»
  ring_isomorphism := SessionLibrary.RingTheory.«ring_isomorphism»
  ring_isomorphisms := SessionLibrary.RingTheory.«ring_isomorphisms»
  ring_monomorphism := SessionLibrary.RingTheory.«ring_monomorphism»
  ring_pow := SessionLibrary.RingTheory.«ring_pow»
  ring_unit := SessionLibrary.RingTheory.«ring_unit»

/-- What numfield.ml uses from Session. -/
def deps : HolANT.Numfield.NumfieldDeps where
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

/- The bundles, in numfield.ml order. -/
initialize BNumfield01 : HolANT.Numfield.Numfield01 ←
  ioB "setupNumfield01" (HolANT.Numfield.setupNumfield01 deps).run
initialize BNumfield02 : HolANT.Numfield.Numfield02 ←
  ioB "setupNumfield02" (HolANT.Numfield.setupNumfield02 deps BNumfield01).run
initialize BNumfield03 : HolANT.Numfield.Numfield03 ←
  ioB "setupNumfield03" (HolANT.Numfield.setupNumfield03 deps BNumfield01 BNumfield02).run

-- Numfield01
def number_field : thm := BNumfield01.number_field
def ring_of_integers : thm := BNumfield01.ring_of_integers
def RING_INT_LINCOMB_SWAP : thm := BNumfield01.RING_INT_LINCOMB_SWAP
def RING_INT_LINCOMB : thm := BNumfield01.RING_INT_LINCOMB
def RING_MUL_INT_LINCOMB : thm := BNumfield01.RING_MUL_INT_LINCOMB
def RING_INT_LINCOMB_LINCOMB : thm := BNumfield01.RING_INT_LINCOMB_LINCOMB
def RING_INT_LINCOMB_SANDWICH : thm := BNumfield01.RING_INT_LINCOMB_SANDWICH
def NUMBER_FIELD_IMP_FIELD : thm := BNumfield01.NUMBER_FIELD_IMP_FIELD
def NUMBER_FIELD_RING_OF_NUM_EQ_0 : thm := BNumfield01.NUMBER_FIELD_RING_OF_NUM_EQ_0
def NUMBER_FIELD_ALT : thm := BNumfield01.NUMBER_FIELD_ALT
def NUMBER_FIELD_FREE_BASIS_DEGREE : thm := BNumfield01.NUMBER_FIELD_FREE_BASIS_DEGREE
def NUMBER_FIELD_FREE_BASIS : thm := BNumfield01.NUMBER_FIELD_FREE_BASIS
def NUMBER_FIELD_DEGREE_POS : thm := BNumfield01.NUMBER_FIELD_DEGREE_POS
def NUMBER_FIELD_DEGREE_EQ_1 : thm := BNumfield01.NUMBER_FIELD_DEGREE_EQ_1
def NUMBER_FIELD_ALGEBRAIC : thm := BNumfield01.NUMBER_FIELD_ALGEBRAIC
def NUMBER_FIELD_PRIME_SUBFIELD : thm := BNumfield01.NUMBER_FIELD_PRIME_SUBFIELD
def NUMBER_FIELD_RATIONAL_FIELD : thm := BNumfield01.NUMBER_FIELD_RATIONAL_FIELD
def NUMBER_FIELD_SUBFIELD_GENERATED_ALGEBRAIC : thm := BNumfield01.NUMBER_FIELD_SUBFIELD_GENERATED_ALGEBRAIC
def PRIME_SUBFIELD_CHAR_0 : thm := BNumfield01.PRIME_SUBFIELD_CHAR_0
def REAL_PRIME_SUBFIELD : thm := BNumfield01.REAL_PRIME_SUBFIELD
def PRIME_SUBFIELD_COMMON_DENOMINATOR : thm := BNumfield01.PRIME_SUBFIELD_COMMON_DENOMINATOR
def FREE_BASIS_PRIME_SUBFIELD_DENOMINATOR : thm := BNumfield01.FREE_BASIS_PRIME_SUBFIELD_DENOMINATOR
def FREE_BASIS_PRIME_SUBFIELD_INT_LINCOMB : thm := BNumfield01.FREE_BASIS_PRIME_SUBFIELD_INT_LINCOMB
def NUMBER_FIELD_INT_LINCOMB_SANDWICH : thm := BNumfield01.NUMBER_FIELD_INT_LINCOMB_SANDWICH
def RING_OF_INTEGERS_CARRIER : thm := BNumfield01.RING_OF_INTEGERS_CARRIER
def RING_OF_INTEGERS_SUBSET : thm := BNumfield01.RING_OF_INTEGERS_SUBSET
def RING_OF_INTEGERS_SUBRING : thm := BNumfield01.RING_OF_INTEGERS_SUBRING
def RING_OF_INTEGERS : thm := BNumfield01.RING_OF_INTEGERS
def RING_SUM_RING_OF_INTEGERS : thm := BNumfield01.RING_SUM_RING_OF_INTEGERS
def RING_PRODUCT_RING_OF_INTEGERS : thm := BNumfield01.RING_PRODUCT_RING_OF_INTEGERS
def RING_OF_INT_IN_RING_OF_INTEGERS : thm := BNumfield01.RING_OF_INT_IN_RING_OF_INTEGERS
def ROOT_OF_UNITY_IN_RING_OF_INTEGERS : thm := BNumfield01.ROOT_OF_UNITY_IN_RING_OF_INTEGERS

-- Numfield02
def RING_OF_INTEGERS_ROOT_OF_UNITY_UNIT : thm := BNumfield02.RING_OF_INTEGERS_ROOT_OF_UNITY_UNIT
def INTEGRAL_DOMAIN_RING_OF_INTEGERS : thm := BNumfield02.INTEGRAL_DOMAIN_RING_OF_INTEGERS
def RING_OF_INTEGERS_UNIT_NONZERO : thm := BNumfield02.RING_OF_INTEGERS_UNIT_NONZERO
def RING_OF_INTEGERS_PRIME_SUBFIELD : thm := BNumfield02.RING_OF_INTEGERS_PRIME_SUBFIELD
def RING_OF_INTEGERS_ALGEBRAIC : thm := BNumfield02.RING_OF_INTEGERS_ALGEBRAIC
def RING_OF_INTEGERS_RING_OF_INT_MUL : thm := BNumfield02.RING_OF_INTEGERS_RING_OF_INT_MUL
def RING_HOMOMORPHISM_RING_OF_INTEGERS : thm := BNumfield02.RING_HOMOMORPHISM_RING_OF_INTEGERS
def RING_MONOMORPHISM_RING_OF_INTEGERS : thm := BNumfield02.RING_MONOMORPHISM_RING_OF_INTEGERS
def RING_ISOMORPHISM_RING_OF_INTEGERS : thm := BNumfield02.RING_ISOMORPHISM_RING_OF_INTEGERS
def ISOMORPHIC_RING_RING_OF_INTEGERS : thm := BNumfield02.ISOMORPHIC_RING_RING_OF_INTEGERS
def NUMBER_FIELD_INTEGRAL_MULTIPLE : thm := BNumfield02.NUMBER_FIELD_INTEGRAL_MULTIPLE
def RING_OF_INTEGERS_DENOMINATOR : thm := BNumfield02.RING_OF_INTEGERS_DENOMINATOR
def RING_OF_INTEGERS_COMMON_DENOMINATOR : thm := BNumfield02.RING_OF_INTEGERS_COMMON_DENOMINATOR
def RING_OF_INTEGERS_IN_IDEAL_GENERATED_SING : thm := BNumfield02.RING_OF_INTEGERS_IN_IDEAL_GENERATED_SING
def RING_OF_INTEGERS_IDEAL_GENERATED_SING_EQ_0 : thm := BNumfield02.RING_OF_INTEGERS_IDEAL_GENERATED_SING_EQ_0
def NUMBER_FIELD_INTEGRAL_FREE_BASIS : thm := BNumfield02.NUMBER_FIELD_INTEGRAL_FREE_BASIS
def NUMBER_FIELD_TRACE_ADD : thm := BNumfield02.NUMBER_FIELD_TRACE_ADD
def NUMBER_FIELD_NORM_MUL : thm := BNumfield02.NUMBER_FIELD_NORM_MUL
def NUMBER_FIELD_NORM_EQ_0 : thm := BNumfield02.NUMBER_FIELD_NORM_EQ_0
def NUMBER_FIELD_NORM_RATIONAL : thm := BNumfield02.NUMBER_FIELD_NORM_RATIONAL
def NUMBER_FIELD_NORM_SUB_MINIMAL_POLYNOMIAL : thm := BNumfield02.NUMBER_FIELD_NORM_SUB_MINIMAL_POLYNOMIAL
def NUMBER_FIELD_TRACE_RATIONAL : thm := BNumfield02.NUMBER_FIELD_TRACE_RATIONAL
def NUMBER_FIELD_TRACE_SCALAR_MUL : thm := BNumfield02.NUMBER_FIELD_TRACE_SCALAR_MUL
def NUMBER_FIELD_TRACE_MUL_LINCOMB : thm := BNumfield02.NUMBER_FIELD_TRACE_MUL_LINCOMB
def NUMBER_FIELD_TRACE_FORM_INJECTIVE : thm := BNumfield02.NUMBER_FIELD_TRACE_FORM_INJECTIVE
def RING_OF_INTEGERS_INTEGER_MATRIX : thm := BNumfield02.RING_OF_INTEGERS_INTEGER_MATRIX
def NUMBER_FIELD_TRACE_INTEGRAL_Q : thm := BNumfield02.NUMBER_FIELD_TRACE_INTEGRAL_Q
def NUMBER_FIELD_TRACE_IN_RING_OF_INTEGERS : thm := BNumfield02.NUMBER_FIELD_TRACE_IN_RING_OF_INTEGERS

-- Numfield03
def NUMBER_FIELD_NORM_INTEGRAL_Q : thm := BNumfield03.NUMBER_FIELD_NORM_INTEGRAL_Q

/-- `needs "ANT/numfield.ml"`: already done by importing this module. -/
def ensureNumfield : IO Unit := pure ()

end SessionANT.Numfield
