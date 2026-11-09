/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/normal_basis.ml.                            -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/NormalBasis.lean

  The session half of the normal_basis.ml translation: it supplies
  HolLibrary.NormalBasis's dependencies from Session and SessionLibrary.Galois
  (and the modules Galois imports), and exports every name under its HOL
  Light name.  Importing this module is `needs "Library/normal_basis.ml"`;
  its `needs` is the import of SessionLibrary.Galois.  The bundles are built
  by `initialize` when the module is loaded.
-/

import Session
import HolLibrary.NormalBasis
import SessionLibrary.Galois

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.NormalBasis

/-- The core theorems normal_basis.ml uses. -/
def core1 : HolLibrary.NormalBasis.CoreThms1 where
  BIJ := Session.BIJ
  CARD_EQ_0 := Session.CARD_EQ_0
  CARD_IMAGE_INJ := Session.CARD_IMAGE_INJ
  CONG_IMP_EQ := SessionLibrary.Pocklington.«CONG_IMP_EQ»
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  CYCLIC_GALOIS_GROUP_FINITE_FIELD := SessionLibrary.Galois.«CYCLIC_GALOIS_GROUP_FINITE_FIELD»
  CYCLIC_VECTOR_EXISTS := SessionLibrary.FieldTheory.«CYCLIC_VECTOR_EXISTS»
  EQ_IMP := Session.EQ_IMP
  EQ_SYM_EQ := Session.EQ_SYM_EQ
  EQ_TRANS := Session.EQ_TRANS
  EXTENSION := Session.EXTENSION
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_NONTRIVIAL := SessionLibrary.RingTheory.«FIELD_NONTRIVIAL»
  FINITE_CYCLIC_GROUP_POWERS := SessionLibrary.GroupTheory.«FINITE_CYCLIC_GROUP_POWERS»
  FINITE_DELETE := Session.FINITE_DELETE
  FINITE_EXTENSION_RING_MATROID := SessionLibrary.FieldTheory.«FINITE_EXTENSION_RING_MATROID»
  FINITE_FIELD_GALOIS_EXTENSION := SessionLibrary.Galois.«FINITE_FIELD_GALOIS_EXTENSION»
  FINITE_FINITE_FIELD_EXTENSION := SessionLibrary.FieldTheory.«FINITE_FINITE_FIELD_EXTENSION»
  FINITE_GALOIS_GROUP := SessionLibrary.Galois.«FINITE_GALOIS_GROUP»
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_IMP_FIELD_EXTENSION := SessionLibrary.FieldTheory.«FINITE_IMP_FIELD_EXTENSION»
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FREE_BASIS_FIELD := SessionLibrary.FieldTheory.«FREE_BASIS_FIELD»
  FUN_EQ_THM := Session.FUN_EQ_THM
  GALOIS_EXTENSION_EQ_CARD := SessionLibrary.Galois.«GALOIS_EXTENSION_EQ_CARD»
  GALOIS_GROUP := SessionLibrary.Galois.«GALOIS_GROUP»
  GALOIS_GROUP_COMPOSE := SessionLibrary.Galois.«GALOIS_GROUP_COMPOSE»
  GALOIS_GROUP_FINITE_FIELD := SessionLibrary.Galois.«GALOIS_GROUP_FINITE_FIELD»
  GALOIS_GROUP_FIXES := SessionLibrary.Galois.«GALOIS_GROUP_FIXES»
  GALOIS_GROUP_I := SessionLibrary.Galois.«GALOIS_GROUP_I»
  GALOIS_GROUP_INDEPENDENT := SessionLibrary.Galois.«GALOIS_GROUP_INDEPENDENT»
  GALOIS_GROUP_INVERSE := SessionLibrary.Galois.«GALOIS_GROUP_INVERSE»
  GALOIS_GROUP_IN_CARRIER := SessionLibrary.Galois.«GALOIS_GROUP_IN_CARRIER»
  GALOIS_GROUP_PERMUTES := SessionLibrary.Galois.«GALOIS_GROUP_PERMUTES»
  GALOIS_GROUP_POW_RING_POW := SessionLibrary.Galois.«GALOIS_GROUP_POW_RING_POW»
  GALOIS_GROUP_RING_HOMOMORPHISM := SessionLibrary.Galois.«GALOIS_GROUP_RING_HOMOMORPHISM»
  GALOIS_IMP_SEPARABLE_EXTENSION := SessionLibrary.Galois.«GALOIS_IMP_SEPARABLE_EXTENSION»
  GROUP_POW := SessionLibrary.GroupTheory.«GROUP_POW»
  INFINITE := Session.INFINITE
  INFINITE_IMAGE := Session.INFINITE_IMAGE
  INJ := Session.INJ
  INTEGRAL_DOMAIN_PRODUCT_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_PRODUCT_EQ_0»
  IN_DELETE := Session.IN_DELETE
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  ITER := SessionLibrary.Iter.«ITER»
  I_O_ID := Session.I_O_ID
  I_THM := Session.I_THM
  LE_REFL := Session.LE_REFL
  LT_NZ := Session.LT_NZ
  MATROID_BASIS_LARGE_INDEPENDENT := SessionLibrary.Matroids.«MATROID_BASIS_LARGE_INDEPENDENT»
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MONO_EXISTS := Session.MONO_EXISTS
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  PERMUTES_EQ := SessionLibrary.Permutations.«PERMUTES_EQ»
  PERMUTES_INVERSES_o := SessionLibrary.Permutations.«PERMUTES_INVERSES_o»
  PERMUTES_INVERSE_INVERSE := SessionLibrary.Permutations.«PERMUTES_INVERSE_INVERSE»
  POLY_CLAUSES := SessionLibrary.RingTheory.«POLY_CLAUSES»
  POLY_CONST := SessionLibrary.RingTheory.«POLY_CONST»
  POLY_EVAL_0 := SessionLibrary.RingTheory.«POLY_EVAL_0»
  POLY_EVAL_CONST := SessionLibrary.RingTheory.«POLY_EVAL_CONST»
  POLY_EVAL_RING_PRODUCT := SessionLibrary.RingTheory.«POLY_EVAL_RING_PRODUCT»
  POLY_EVAL_SUB := SessionLibrary.RingTheory.«POLY_EVAL_SUB»
  POLY_EVAL_VAR := SessionLibrary.RingTheory.«POLY_EVAL_VAR»
  POLY_RING_CLAUSES := SessionLibrary.RingTheory.«POLY_RING_CLAUSES»
  POLY_ROOT_BOUND := SessionLibrary.RingTheory.«POLY_ROOT_BOUND»
  POLY_VAR_UNIV := SessionLibrary.RingTheory.«POLY_VAR_UNIV»
  PRIMITIVE_ELEMENT_THEOREM := SessionLibrary.FieldTheory.«PRIMITIVE_ELEMENT_THEOREM»
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD_LZERO := SessionLibrary.RingTheory.«RING_ADD_LZERO»
  RING_ADD_RNEG := SessionLibrary.RingTheory.«RING_ADD_RNEG»
  RING_ADD_RZERO := SessionLibrary.RingTheory.«RING_ADD_RZERO»
  RING_DET := SessionLibrary.RingDet.«RING_DET»
  RING_DET_DEPENDENT_COLUMNS := SessionLibrary.RingDet.«RING_DET_DEPENDENT_COLUMNS»
  RING_DET_DIAGONAL := SessionLibrary.RingDet.«RING_DET_DIAGONAL»
  RING_DET_EQ := SessionLibrary.RingDet.«RING_DET_EQ»
  RING_DET_EQ_0_ROWS := SessionLibrary.RingDet.«RING_DET_EQ_0_ROWS»
  RING_DET_HOMOMORPHISM := SessionLibrary.RingDet.«RING_DET_HOMOMORPHISM»
  RING_HOMOMORPHISMS_EQ_FROM_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_HOMOMORPHISMS_EQ_FROM_SUBRING_GENERATED»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_1 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_1»
  RING_HOMOMORPHISM_ADD := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_ADD»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_NEG := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_NEG»
  RING_HOMOMORPHISM_POLY_EVAL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POLY_EVAL»
  RING_HOMOMORPHISM_PRODUCT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_PRODUCT»
  RING_HOMOMORPHISM_SUB := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUB»
  RING_HOMOMORPHISM_SUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUM»
  RING_INDEPENDENT_FINITE := SessionLibrary.FieldTheory.«RING_INDEPENDENT_FINITE»
  RING_MATROID_BASIS := SessionLibrary.FieldTheory.«RING_MATROID_BASIS»
  RING_MATROID_INDEPENDENT := SessionLibrary.FieldTheory.«RING_MATROID_INDEPENDENT»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_LNEG := SessionLibrary.RingTheory.«RING_MUL_LNEG»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_MUL_SYM := SessionLibrary.RingTheory.«RING_MUL_SYM»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  RING_POLYNOMIAL_CONST := SessionLibrary.RingTheory.«RING_POLYNOMIAL_CONST»
  RING_POLYNOMIAL_VAR := SessionLibrary.RingTheory.«RING_POLYNOMIAL_VAR»
  RING_PRODUCT := SessionLibrary.RingTheory.«RING_PRODUCT»
  RING_PRODUCT_EQ := SessionLibrary.RingTheory.«RING_PRODUCT_EQ»
  RING_PRODUCT_EQ_GENERAL_INVERSES := SessionLibrary.RingTheory.«RING_PRODUCT_EQ_GENERAL_INVERSES»
  RING_PRODUCT_ZERO := SessionLibrary.RingTheory.«RING_PRODUCT_ZERO»
  RING_SPAN_FINITE := SessionLibrary.FieldTheory.«RING_SPAN_FINITE»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_EQ_0 := SessionLibrary.RingTheory.«RING_SUB_EQ_0»
  RING_SUB_REFL := SessionLibrary.RingTheory.«RING_SUB_REFL»
  RING_SUM_ADD := SessionLibrary.RingTheory.«RING_SUM_ADD»
  RING_SUM_CYCLIC_GROUP := SessionLibrary.Galois.«RING_SUM_CYCLIC_GROUP»
  RING_SUM_DELTA := SessionLibrary.RingTheory.«RING_SUM_DELTA»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_EQ_0 := SessionLibrary.RingTheory.«RING_SUM_EQ_0»
  RING_SUM_EQ_GENERAL_INVERSES := SessionLibrary.RingTheory.«RING_SUM_EQ_GENERAL_INVERSES»
  RING_SUM_IMAGE := SessionLibrary.RingTheory.«RING_SUM_IMAGE»
  RING_SUM_LMUL := SessionLibrary.RingTheory.«RING_SUM_LMUL»
  RING_SUM_SWAP := SessionLibrary.RingTheory.«RING_SUM_SWAP»
  SUBSET := Session.SUBSET
  SURJ := Session.SURJ
  cyclic_group := SessionLibrary.GroupTheory.«cyclic_group»
  extension_degree := SessionLibrary.FieldTheory.«extension_degree»
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  group_pow := SessionLibrary.GroupTheory.«group_pow»
  o_ASSOC := Session.o_ASSOC
  o_DEF := Session.o_DEF
  o_THM := Session.o_THM
  ring_basis := SessionLibrary.FieldTheory.«ring_basis»
  ring_monomorphism := SessionLibrary.RingTheory.«ring_monomorphism»
  ring_spanning := SessionLibrary.FieldTheory.«ring_spanning»

/-- What normal_basis.ml uses from Session. -/
def deps : HolLibrary.NormalBasis.NormalBasisDeps where
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  TAUT t := ExceptT.mk (Session.TAUT t)
  INDUCT_TAC := Session.INDUCT_TAC
  SELECT_CONV t := pure (Session.SELECT_CONV t)
  NUMBER_RULE := Session.NUMBER_RULE
  RING_TAC := SessionLibrary.RingTheory.RING_TAC
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in normal_basis.ml order. -/
initialize BNormalElements : HolLibrary.NormalBasis.NormalElements ←
  ioB "setupNormalElements" (HolLibrary.NormalBasis.setupNormalElements deps).run
initialize BNormalBasisCyclic : HolLibrary.NormalBasis.NormalBasisCyclic ←
  ioB "setupNormalBasisCyclic" (HolLibrary.NormalBasis.setupNormalBasisCyclic deps BNormalElements).run
initialize BNormalBasisInfinite : HolLibrary.NormalBasis.NormalBasisInfinite ←
  ioB "setupNormalBasisInfinite" (HolLibrary.NormalBasis.setupNormalBasisInfinite deps BNormalElements).run
initialize BNormalBasisTheorem : HolLibrary.NormalBasis.NormalBasisTheorem ←
  ioB "setupNormalBasisTheorem" (HolLibrary.NormalBasis.setupNormalBasisTheorem deps BNormalElements BNormalBasisCyclic BNormalBasisInfinite).run

-- NormalElements
def NORMAL_BASIS_INDEPENDENT : thm := BNormalElements.NORMAL_BASIS_INDEPENDENT
def NORMAL_BASIS_DET_INDEPENDENT : thm := BNormalElements.NORMAL_BASIS_DET_INDEPENDENT
def NORMAL_BASIS_DETERMINANT : thm := BNormalElements.NORMAL_BASIS_DETERMINANT

-- NormalBasisCyclic
def NORMAL_BASIS_CYCLIC : thm := BNormalBasisCyclic.NORMAL_BASIS_CYCLIC

-- NormalBasisInfinite
def NORMAL_BASIS_INFINITE : thm := BNormalBasisInfinite.NORMAL_BASIS_INFINITE

-- NormalBasisTheorem
def NORMAL_BASIS_THEOREM : thm := BNormalBasisTheorem.NORMAL_BASIS_THEOREM
def NORMAL_BASIS_RING_BASIS : thm := BNormalBasisTheorem.NORMAL_BASIS_RING_BASIS
def NORMAL_BASIS_FREE_BASIS : thm := BNormalBasisTheorem.NORMAL_BASIS_FREE_BASIS
def FINITE_FIELD_NORMAL_BASIS : thm := BNormalBasisTheorem.FINITE_FIELD_NORMAL_BASIS

/-- `needs "Library/normal_basis.ml"`: already done by importing this module. -/
def ensureNormalBasis : IO Unit := pure ()

end SessionLibrary.NormalBasis
