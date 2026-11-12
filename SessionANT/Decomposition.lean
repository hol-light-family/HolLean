/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/decomposition.ml                              . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/Decomposition.lean

  The session half of the decomposition.ml translation: it supplies HolANT.Decomposition's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/decomposition.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.Decomposition
import SessionLibrary.Frag
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.Prime
import SessionLibrary.GroupTheory
import SessionLibrary.Matroids
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Pocklington
import SessionLibrary.RingTheory
import SessionLibrary.Permutations
import SessionLibrary.RingDet
import SessionLibrary.FieldTheory
import SessionLibrary.SymmetricGroup
import SessionLibrary.Galois
import SessionLibrary.RingGroups
import SessionLibrary.FiniteFields
import SessionANT.IdealArith

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.Decomposition

/-- The core theorems decomposition.ml uses. -/
def core1 : HolANT.Decomposition.CoreThms1 where
  CARD_EQ_0 := Session.CARD_EQ_0
  CARD_EQ_CARD := SessionLibrary.Card.«CARD_EQ_CARD»
  CARD_EQ_GROUP_IMAGE_KERNEL := SessionLibrary.GroupTheory.«CARD_EQ_GROUP_IMAGE_KERNEL»
  CARD_IMAGE_INJ := Session.CARD_IMAGE_INJ
  CARD_MUL_C := SessionLibrary.Card.«CARD_MUL_C»
  CARD_MUL_FINITE := SessionLibrary.Card.«CARD_MUL_FINITE»
  CARRIER_SUBFIELD_GENERATED_SUBFIELD := SessionLibrary.FieldTheory.«CARRIER_SUBFIELD_GENERATED_SUBFIELD»
  CARRIER_SUBGROUP_GENERATED_SUBGROUP := SessionLibrary.GroupTheory.«CARRIER_SUBGROUP_GENERATED_SUBGROUP»
  CARRIER_SUBRING_GENERATED_SUBRING := SessionLibrary.RingTheory.«CARRIER_SUBRING_GENERATED_SUBRING»
  CARRIER_SUBRING_OF := SessionLibrary.RingTheory.«CARRIER_SUBRING_OF»
  CHINESE_REMAINDER_IDEALS := SessionANT.IdealArith.«CHINESE_REMAINDER_IDEALS»
  CONJ_ASSOC := Session.CONJ_ASSOC
  EQ_MULT_LCANCEL := Session.EQ_MULT_LCANCEL
  EXISTS_IN_GSPEC := Session.EXISTS_IN_GSPEC
  EXP := Session.EXP
  EXTENSION := Session.EXTENSION
  FIELD_EXTENSION_SUBRING_GENERATED_FINITE := SessionLibrary.FieldTheory.«FIELD_EXTENSION_SUBRING_GENERATED_FINITE»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«FIELD_IMP_NONTRIVIAL_RING»
  FIELD_QUOTIENT_RING := SessionLibrary.RingTheory.«FIELD_QUOTIENT_RING»
  FINITE_EXTENSION_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FINITE_EXTENSION_SUBFIELD_GENERATED»
  FINITE_FIELD_PRIMITIVE_ROOT := SessionLibrary.FiniteFields.«FINITE_FIELD_PRIMITIVE_ROOT»
  FINITE_GALOIS_GROUP := SessionLibrary.Galois.«FINITE_GALOIS_GROUP»
  FINITE_GROUP_ORBIT := SessionLibrary.GroupTheory.«FINITE_GROUP_ORBIT»
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_INTEGRAL_DOMAIN_IMP_FIELD := SessionLibrary.RingTheory.«FINITE_INTEGRAL_DOMAIN_IMP_FIELD»
  FINITE_SUBRING_GENERATED := SessionLibrary.RingTheory.«FINITE_SUBRING_GENERATED»
  FINITE_SUBSET := Session.FINITE_SUBSET
  FIXED_FIELD_GALOIS_GROUP := SessionLibrary.Galois.«FIXED_FIELD_GALOIS_GROUP»
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FUN_EQ_THM := Session.FUN_EQ_THM
  FUN_IN_IMAGE := Session.FUN_IN_IMAGE
  GALOIS_EXTENSION_EQ_CARD := SessionLibrary.Galois.«GALOIS_EXTENSION_EQ_CARD»
  GALOIS_EXTENSION_SUBFIELD_GENERATED := SessionLibrary.Galois.«GALOIS_EXTENSION_SUBFIELD_GENERATED»
  GALOIS_GROUP := SessionLibrary.Galois.«GALOIS_GROUP»
  GALOIS_GROUP_ACTION := SessionLibrary.Galois.«GALOIS_GROUP_ACTION»
  GALOIS_GROUP_ANTIMONO := SessionLibrary.Galois.«GALOIS_GROUP_ANTIMONO»
  GALOIS_GROUP_COMPOSE := SessionLibrary.Galois.«GALOIS_GROUP_COMPOSE»
  GALOIS_GROUP_FINITE_FIELD := SessionLibrary.Galois.«GALOIS_GROUP_FINITE_FIELD»
  GALOIS_GROUP_FIXED_FIELD := SessionLibrary.Galois.«GALOIS_GROUP_FIXED_FIELD»
  GALOIS_GROUP_FIXES := SessionLibrary.Galois.«GALOIS_GROUP_FIXES»
  GALOIS_GROUP_I := SessionLibrary.Galois.«GALOIS_GROUP_I»
  GALOIS_GROUP_IMAGE_INVERSE := SessionLibrary.Galois.«GALOIS_GROUP_IMAGE_INVERSE»
  GALOIS_GROUP_INVERSE := SessionLibrary.Galois.«GALOIS_GROUP_INVERSE»
  GALOIS_GROUP_IN_CARRIER := SessionLibrary.Galois.«GALOIS_GROUP_IN_CARRIER»
  GALOIS_GROUP_PERMUTES := SessionLibrary.Galois.«GALOIS_GROUP_PERMUTES»
  GALOIS_GROUP_RING_AUTOMORPHISM := SessionLibrary.Galois.«GALOIS_GROUP_RING_AUTOMORPHISM»
  GALOIS_GROUP_RING_HOMOMORPHISM := SessionLibrary.Galois.«GALOIS_GROUP_RING_HOMOMORPHISM»
  GALOIS_PRODUCT_IN_BASE := SessionLibrary.Galois.«GALOIS_PRODUCT_IN_BASE»
  GROUP_ACTION_ON_SUBSET := SessionLibrary.GroupTheory.«GROUP_ACTION_ON_SUBSET»
  GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET := SessionLibrary.GroupTheory.«GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET»
  GROUP_EPIMORPHISM_ALT := SessionLibrary.GroupTheory.«GROUP_EPIMORPHISM_ALT»
  GROUP_HOMOMORPHISM := SessionLibrary.GroupTheory.«GROUP_HOMOMORPHISM»
  GROUP_ID := SessionLibrary.GroupTheory.«GROUP_ID»
  GROUP_ORBIT := SessionLibrary.GroupTheory.«GROUP_ORBIT»
  GROUP_POW := SessionLibrary.GroupTheory.«GROUP_POW»
  GROUP_STABILIZER_OF_ACTION := SessionLibrary.GroupTheory.«GROUP_STABILIZER_OF_ACTION»
  HAS_SIZE := Session.HAS_SIZE
  IMAGE_CLAUSES := Session.IMAGE_CLAUSES
  IMAGE_I := Session.IMAGE_I
  IMAGE_ID := Session.IMAGE_ID
  IMAGE_SUBSET := Session.IMAGE_SUBSET
  IMAGE_o := Session.IMAGE_o
  IMP_CONJ := Session.IMP_CONJ
  INTEGRAL_DOMAIN_SUBRING_GENERATED := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_SUBRING_GENERATED»
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_FIXED_FIELD := SessionLibrary.Galois.«IN_FIXED_FIELD»
  IN_GALOIS_GROUP := SessionLibrary.Galois.«IN_GALOIS_GROUP»
  IN_GALOIS_GROUP_INTERMEDIATE := SessionLibrary.Galois.«IN_GALOIS_GROUP_INTERMEDIATE»
  IN_IMAGE := Session.IN_IMAGE
  IN_INTER := Session.IN_INTER
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_RING_IDEAL_ADD := SessionLibrary.RingTheory.«IN_RING_IDEAL_ADD»
  IN_RING_IDEAL_SUB := SessionLibrary.RingTheory.«IN_RING_IDEAL_SUB»
  IN_RING_POLYNOMIAL_CARRIER_COMPOSE := SessionLibrary.RingTheory.«IN_RING_POLYNOMIAL_CARRIER_COMPOSE»
  IN_SING := Session.IN_SING
  IN_UNIONS := Session.IN_UNIONS
  IN_UNIV := Session.IN_UNIV
  I_DEF := Session.I_DEF
  I_THM := Session.I_THM
  MAXIMAL_IDEAL_COMAXIMAL := SessionANT.IdealArith.«MAXIMAL_IDEAL_COMAXIMAL»
  MAXIMAL_IDEAL_ISOMORPHIC_IMAGE_EQ := SessionLibrary.RingTheory.«MAXIMAL_IDEAL_ISOMORPHIC_IMAGE_EQ»
  MAXIMAL_IMP_PRIME_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_PRIME_IDEAL»
  MAXIMAL_IMP_PROPER_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_PROPER_IDEAL»
  MAXIMAL_IMP_RING_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_RING_IDEAL»
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MONO_EXISTS := Session.MONO_EXISTS
  MULT_SYM := Session.MULT_SYM
  NORMAL_SUBGROUP_GROUP_KERNEL := SessionLibrary.GroupTheory.«NORMAL_SUBGROUP_GROUP_KERNEL»
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  ORBIT_STABILIZER_MUL := SessionLibrary.GroupTheory.«ORBIT_STABILIZER_MUL»
  PERMUTES_BIJECTIONS := SessionLibrary.Permutations.«PERMUTES_BIJECTIONS»
  PERMUTES_INJECTIVE := SessionLibrary.Permutations.«PERMUTES_INJECTIVE»
  PERMUTES_INVERSES := SessionLibrary.Permutations.«PERMUTES_INVERSES»
/-- The core theorems decomposition.ml uses. -/
def core2 : HolANT.Decomposition.CoreThms2 where
  PERMUTES_INVERSE_INVERSE := SessionLibrary.Permutations.«PERMUTES_INVERSE_INVERSE»
  PERMUTES_IN_IMAGE := SessionLibrary.Permutations.«PERMUTES_IN_IMAGE»
  POLY_EVAL_CONST := SessionLibrary.RingTheory.«POLY_EVAL_CONST»
  POLY_EVAL_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_EVAL_HOMOMORPHIC_IMAGE»
  POLY_EVAL_RING_PRODUCT := SessionLibrary.RingTheory.«POLY_EVAL_RING_PRODUCT»
  POLY_EVAL_SUB := SessionLibrary.RingTheory.«POLY_EVAL_SUB»
  POLY_EVAL_VAR := SessionLibrary.RingTheory.«POLY_EVAL_VAR»
  POLY_X_MINUS_A_IN_CARRIER := SessionLibrary.RingTheory.«POLY_X_MINUS_A_IN_CARRIER»
  PRIME_AVOIDANCE := SessionANT.IdealArith.«PRIME_AVOIDANCE»
  PRIME_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«PRIME_IDEAL_IMP_SUBSET»
  PRIME_IDEAL_ISOMORPHIC_IMAGE_EQ := SessionLibrary.RingTheory.«PRIME_IDEAL_ISOMORPHIC_IMAGE_EQ»
  PRIME_IMP_PROPER_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_PROPER_IDEAL»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PSUBSET := Session.PSUBSET
  QUOTIENT_RING_0 := SessionLibrary.RingTheory.«QUOTIENT_RING_0»
  QUOTIENT_RING_CARRIER := SessionLibrary.RingTheory.«QUOTIENT_RING_CARRIER»
  QUOTIENT_RING_UNIVERSAL := SessionLibrary.RingTheory.«QUOTIENT_RING_UNIVERSAL»
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_CARRIER_NONEMPTY := SessionLibrary.RingTheory.«RING_CARRIER_NONEMPTY»
  RING_CARRIER_SUBRING_GENERATED_SUBSET := SessionLibrary.RingTheory.«RING_CARRIER_SUBRING_GENERATED_SUBSET»
  RING_COSET_EQ := SessionLibrary.RingTheory.«RING_COSET_EQ»
  RING_COSET_EQ_IDEAL := SessionLibrary.RingTheory.«RING_COSET_EQ_IDEAL»
  RING_HOMOMORPHISMS_EQ_FROM_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_HOMOMORPHISMS_EQ_FROM_SUBRING_GENERATED»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_ADD := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_ADD»
  RING_HOMOMORPHISM_BETWEEN_SUBRINGS := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_BETWEEN_SUBRINGS»
  RING_HOMOMORPHISM_COMPOSE := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_COMPOSE»
  RING_HOMOMORPHISM_EQ := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_EQ»
  RING_HOMOMORPHISM_I := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_I»
  RING_HOMOMORPHISM_POW := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POW»
  RING_HOMOMORPHISM_RING_COSET := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_COSET»
  RING_HOMOMORPHISM_SUB := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUB»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_IDEAL_ISOMORPHIC_IMAGE_EQ := SessionLibrary.RingTheory.«RING_IDEAL_ISOMORPHIC_IMAGE_EQ»
  RING_ISOMORPHISM_BETWEEN_SUBRINGS := SessionLibrary.RingTheory.«RING_ISOMORPHISM_BETWEEN_SUBRINGS»
  RING_ISOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_ISOMORPHISM_IMP_HOMOMORPHISM»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MONOMORPHISM_INCLUSION := SessionLibrary.RingTheory.«RING_MONOMORPHISM_INCLUSION»
  RING_NEG_SUB := SessionLibrary.RingTheory.«RING_NEG_SUB»
  RING_ORDER_0 := SessionLibrary.RingTheory.«RING_ORDER_0»
  RING_POLYNOMIAL_CONST := SessionLibrary.RingTheory.«RING_POLYNOMIAL_CONST»
  RING_POLYNOMIAL_VAR := SessionLibrary.RingTheory.«RING_POLYNOMIAL_VAR»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_1 := SessionLibrary.RingTheory.«RING_POW_1»
  RING_POW_IN_PRIME_IDEAL := SessionLibrary.RingTheory.«RING_POW_IN_PRIME_IDEAL»
  RING_POW_POW := SessionLibrary.RingTheory.«RING_POW_POW»
  RING_POW_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_POW_SUBRING_GENERATED»
  RING_PRODUCT := SessionLibrary.RingTheory.«RING_PRODUCT»
  RING_PRODUCT_EQ := SessionLibrary.RingTheory.«RING_PRODUCT_EQ»
  RING_PRODUCT_IN_PRIME_IDEAL := SessionLibrary.RingTheory.«RING_PRODUCT_IN_PRIME_IDEAL»
  RING_PRODUCT_SUBRING_GENERATED_GEN := SessionLibrary.RingTheory.«RING_PRODUCT_SUBRING_GENERATED_GEN»
  RING_PRODUCT_X_MINUS_A_IN_FIXED_FIELD := SessionLibrary.Galois.«RING_PRODUCT_X_MINUS_A_IN_FIXED_FIELD»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_REFL := SessionLibrary.RingTheory.«RING_SUB_REFL»
  RING_SUB_RZERO := SessionLibrary.RingTheory.«RING_SUB_RZERO»
  RING_SUB_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_SUB_SUBRING_GENERATED»
  SELECT_UNIQUE := Session.SELECT_UNIQUE
  SIMPLE_IMAGE := Session.SIMPLE_IMAGE
  SUBGROUP_GENERATED := SessionLibrary.GroupTheory.«SUBGROUP_GENERATED»
  SUBGROUP_OF_SUBGROUP_GENERATED := SessionLibrary.GroupTheory.«SUBGROUP_OF_SUBGROUP_GENERATED»
  SUBGROUP_SUBGROUP_GENERATED := SessionLibrary.GroupTheory.«SUBGROUP_SUBGROUP_GENERATED»
  SUBRING_GENERATED := SessionLibrary.RingTheory.«SUBRING_GENERATED»
  SUBRING_GENERATED_INC_GEN := SessionLibrary.RingTheory.«SUBRING_GENERATED_INC_GEN»
  SUBRING_OF_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«SUBRING_OF_HOMOMORPHIC_IMAGE»
  SUBRING_OF_HOMOMORPHIC_PREIMAGE := SessionLibrary.RingTheory.«SUBRING_OF_HOMOMORPHIC_PREIMAGE»
  SUBRING_SUBRING_GENERATED := SessionLibrary.RingTheory.«SUBRING_SUBRING_GENERATED»
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUBSET_REFL := Session.SUBSET_REFL
  SUBSET_UNIV := Session.SUBSET_UNIV
  TRIVIAL_RING_HAS_SIZE_1 := SessionLibrary.RingTheory.«TRIVIAL_RING_HAS_SIZE_1»
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  finite_extension := SessionLibrary.FieldTheory.«finite_extension»
  group_conjugation := SessionLibrary.GroupTheory.«group_conjugation»
  group_epimorphism := SessionLibrary.GroupTheory.«group_epimorphism»
  group_image := SessionLibrary.GroupTheory.«group_image»
  group_kernel := SessionLibrary.GroupTheory.«group_kernel»
  group_pow := SessionLibrary.GroupTheory.«group_pow»
  group_stabilizer := SessionLibrary.GroupTheory.«group_stabilizer»
  maximal_ideal := SessionLibrary.RingTheory.«maximal_ideal»
  o_DEF := Session.o_DEF
  o_THM := Session.o_THM
  pairwise := Session.pairwise
  permutes := SessionLibrary.Permutations.«permutes»
  ring_automorphism := SessionLibrary.RingTheory.«ring_automorphism»
  ring_coset := SessionLibrary.RingTheory.«ring_coset»
  ring_homomorphism := SessionLibrary.RingTheory.«ring_homomorphism»
  ring_ideal := SessionLibrary.RingTheory.«ring_ideal»
  ring_isomorphism := SessionLibrary.RingTheory.«ring_isomorphism»
  ring_isomorphisms := SessionLibrary.RingTheory.«ring_isomorphisms»
  ring_kernel := SessionLibrary.RingTheory.«ring_kernel»
  subgroup_of := SessionLibrary.GroupTheory.«subgroup_of»
  subring_of := SessionLibrary.RingTheory.«subring_of»

/-- What decomposition.ml uses from Session. -/
def deps : HolANT.Decomposition.DecompositionDeps where
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

/- The bundles, in decomposition.ml order. -/
initialize BDecomposition01 : HolANT.Decomposition.Decomposition01 ←
  ioB "setupDecomposition01" (HolANT.Decomposition.setupDecomposition01 deps).run
initialize BDecomposition02 : HolANT.Decomposition.Decomposition02 ←
  ioB "setupDecomposition02" (HolANT.Decomposition.setupDecomposition02 deps BDecomposition01).run
initialize BDecomposition03 : HolANT.Decomposition.Decomposition03 ←
  ioB "setupDecomposition03" (HolANT.Decomposition.setupDecomposition03 deps BDecomposition01 BDecomposition02).run
initialize BDecomposition04 : HolANT.Decomposition.Decomposition04 ←
  ioB "setupDecomposition04" (HolANT.Decomposition.setupDecomposition04 deps BDecomposition01 BDecomposition03).run

-- Decomposition01
def GALOIS_GROUP_SUBRING_IMAGE : thm := BDecomposition01.GALOIS_GROUP_SUBRING_IMAGE
def GALOIS_GROUP_PRIME_IDEAL_IMAGE : thm := BDecomposition01.GALOIS_GROUP_PRIME_IDEAL_IMAGE
def GALOIS_GROUP_IMAGE_RING_COSET : thm := BDecomposition01.GALOIS_GROUP_IMAGE_RING_COSET
def GALOIS_GROUP_ACTION_SUBRING : thm := BDecomposition01.GALOIS_GROUP_ACTION_SUBRING
def GALOIS_GROUP_TRANSITIVE_PRIME_IDEALS : thm := BDecomposition01.GALOIS_GROUP_TRANSITIVE_PRIME_IDEALS
def GALOIS_GROUP_ORBIT_MAXIMAL_IDEAL : thm := BDecomposition01.GALOIS_GROUP_ORBIT_MAXIMAL_IDEAL
def decomposition_group : thm := BDecomposition01.decomposition_group
def inertia_group : thm := BDecomposition01.inertia_group
def DECOMPOSITION_GROUP : thm := BDecomposition01.DECOMPOSITION_GROUP
def DECOMPOSITION_GROUP_SUBRING_IMAGE : thm := BDecomposition01.DECOMPOSITION_GROUP_SUBRING_IMAGE
def INERTIA_GROUP : thm := BDecomposition01.INERTIA_GROUP
def INERTIA_GROUP_SUBGROUP_OF_DECOMPOSITION_GROUP : thm := BDecomposition01.INERTIA_GROUP_SUBGROUP_OF_DECOMPOSITION_GROUP
def DECOMPOSITION_GROUP_INDEX : thm := BDecomposition01.DECOMPOSITION_GROUP_INDEX
def DECOMPOSITION_GROUP_CONJUGATE : thm := BDecomposition01.DECOMPOSITION_GROUP_CONJUGATE
def INERTIA_GROUP_CONJUGATE : thm := BDecomposition01.INERTIA_GROUP_CONJUGATE
def CARD_DECOMPOSITION_GROUP_CONJUGATE : thm := BDecomposition01.CARD_DECOMPOSITION_GROUP_CONJUGATE
def SUBRING_GENERATED_QUOTIENT_RING_IMAGE : thm := BDecomposition01.SUBRING_GENERATED_QUOTIENT_RING_IMAGE
def GALOIS_GROUP_QUOTIENT_RING_IMAGE : thm := BDecomposition01.GALOIS_GROUP_QUOTIENT_RING_IMAGE
def DECOMPOSITION_GROUP_IMAGE_RING_COSET : thm := BDecomposition01.DECOMPOSITION_GROUP_IMAGE_RING_COSET

-- Decomposition02
def DECOMPOSITION_GROUP_RESIDUE_AUTOMORPHISM : thm := BDecomposition02.DECOMPOSITION_GROUP_RESIDUE_AUTOMORPHISM
def DECOMPOSITION_GROUP_RESIDUE_HOMOMORPHISM : thm := BDecomposition02.DECOMPOSITION_GROUP_RESIDUE_HOMOMORPHISM
def INERTIA_GROUP_NORMAL_SUBGROUP : thm := BDecomposition02.INERTIA_GROUP_NORMAL_SUBGROUP
def GALOIS_GROUP_RESIDUE_CONJUGATE : thm := BDecomposition02.GALOIS_GROUP_RESIDUE_CONJUGATE

-- Decomposition03
def DECOMPOSITION_GROUP_RESIDUE_EPIMORPHISM : thm := BDecomposition03.DECOMPOSITION_GROUP_RESIDUE_EPIMORPHISM
def CARD_DECOMPOSITION_GROUP : thm := BDecomposition03.CARD_DECOMPOSITION_GROUP
def EXTENSION_DEGREE_RESIDUE_CONJUGATE : thm := BDecomposition03.EXTENSION_DEGREE_RESIDUE_CONJUGATE
def frobenius_element : thm := BDecomposition03.frobenius_element
def DECOMPOSITION_GROUP_FROBENIUS_EXISTS : thm := BDecomposition03.DECOMPOSITION_GROUP_FROBENIUS_EXISTS
def FROBENIUS_ELEMENT : thm := BDecomposition03.FROBENIUS_ELEMENT

-- Decomposition04
def FROBENIUS_ELEMENT_CONJUGATE : thm := BDecomposition04.FROBENIUS_ELEMENT_CONJUGATE
def DECOMPOSITION_GROUP_INTERMEDIATE : thm := BDecomposition04.DECOMPOSITION_GROUP_INTERMEDIATE
def INERTIA_GROUP_INTERMEDIATE : thm := BDecomposition04.INERTIA_GROUP_INTERMEDIATE
def INERTIA_GROUP_TOWER : thm := BDecomposition04.INERTIA_GROUP_TOWER
def DECOMPOSITION_GROUP_INTERMEDIATE_UNIQUE : thm := BDecomposition04.DECOMPOSITION_GROUP_INTERMEDIATE_UNIQUE
def DECOMPOSITION_FIELD_UNIQUE_PRIME : thm := BDecomposition04.DECOMPOSITION_FIELD_UNIQUE_PRIME
def FINITE_DECOMPOSITION_INERTIA_GROUPS : thm := BDecomposition04.FINITE_DECOMPOSITION_INERTIA_GROUPS
def FROBENIUS_ELEMENT_IN_DECOMPOSITION_GROUP : thm := BDecomposition04.FROBENIUS_ELEMENT_IN_DECOMPOSITION_GROUP
def DECOMPOSITION_GROUP_POW_CONGRUENCE : thm := BDecomposition04.DECOMPOSITION_GROUP_POW_CONGRUENCE
def DECOMPOSITION_GROUP_CONGRUENT_EQ : thm := BDecomposition04.DECOMPOSITION_GROUP_CONGRUENT_EQ

/-- `needs "ANT/decomposition.ml"`: already done by importing this module. -/
def ensureDecomposition : IO Unit := pure ()

end SessionANT.Decomposition
