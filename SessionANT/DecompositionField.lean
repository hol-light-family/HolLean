/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/decomposition_field.ml                        . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/DecompositionField.lean

  The session half of the decomposition_field.ml translation: it supplies HolANT.DecompositionField's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/decomposition_field.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.DecompositionField
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
import SessionANT.Decomposition
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
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.NormIndex
import SessionANT.Classgroup
import SessionANT.NfValuation
import SessionANT.PrimeSplit
import SessionANT.Discriminant
import SessionANT.TraceForm
import SessionANT.RelativeSplit
import SessionANT.RelativeDegree
import SessionANT.FiniteFieldTrace
import SessionANT.Ramification
import SessionANT.SplittingTypes
import SessionANT.NfDecomposition

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.DecompositionField

/-- The core theorems decomposition_field.ml uses. -/
def core1 : HolANT.DecompositionField.CoreThms1 where
  CARD_EQ_0 := Session.CARD_EQ_0
  CARD_IMAGE_SUBGROUP_KERNEL := SessionLibrary.GroupTheory.«CARD_IMAGE_SUBGROUP_KERNEL»
  CARD_SING := Session.CARD_SING
  CARD_SUBSET_EQ := Session.CARD_SUBSET_EQ
  CARRIER_SUBFIELD_GENERATED_SUBFIELD := SessionLibrary.FieldTheory.«CARRIER_SUBFIELD_GENERATED_SUBFIELD»
  CARRIER_SUBGROUP_GENERATED_BY_SING := SessionLibrary.GroupTheory.«CARRIER_SUBGROUP_GENERATED_BY_SING»
  CONJ_ASSOC := Session.CONJ_ASSOC
  DECOMPOSITION_GROUP := SessionANT.Decomposition.«DECOMPOSITION_GROUP»
  DECOMPOSITION_GROUP_CONGRUENT_EQ := SessionANT.Decomposition.«DECOMPOSITION_GROUP_CONGRUENT_EQ»
  DECOMPOSITION_GROUP_CONJUGATE := SessionANT.Decomposition.«DECOMPOSITION_GROUP_CONJUGATE»
  DECOMPOSITION_GROUP_INTERMEDIATE := SessionANT.Decomposition.«DECOMPOSITION_GROUP_INTERMEDIATE»
  DECOMPOSITION_GROUP_POW_CONGRUENCE := SessionANT.Decomposition.«DECOMPOSITION_GROUP_POW_CONGRUENCE»
  DECOMPOSITION_GROUP_RING_OF_INTEGERS := SessionANT.NfDecomposition.«DECOMPOSITION_GROUP_RING_OF_INTEGERS»
  EQ_MULT_LCANCEL := Session.EQ_MULT_LCANCEL
  EQ_MULT_RCANCEL := Session.EQ_MULT_RCANCEL
  EQ_TRANS := Session.EQ_TRANS
  EXISTS_IN_GSPEC := Session.EXISTS_IN_GSPEC
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXTENSION := Session.EXTENSION
  EXTENSION_DEGREE_TOWER_LAW := SessionLibrary.FieldTheory.«EXTENSION_DEGREE_TOWER_LAW»
  FIELD_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«FIELD_IMP_NONTRIVIAL_RING»
  FIELD_RING_HOMOMORPHISM_MONOMORPHISM := SessionLibrary.RingTheory.«FIELD_RING_HOMOMORPHISM_MONOMORPHISM»
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FINITE_DECOMPOSITION_INERTIA_GROUPS := SessionANT.Decomposition.«FINITE_DECOMPOSITION_INERTIA_GROUPS»
  FINITE_GALOIS_GROUP := SessionLibrary.Galois.«FINITE_GALOIS_GROUP»
  FINITE_INTER := Session.FINITE_INTER
  FIXED_FIELD_ANTIMONO := SessionLibrary.Galois.«FIXED_FIELD_ANTIMONO»
  FIXED_FIELD_SUBGROUP_GENERATED := SessionLibrary.Galois.«FIXED_FIELD_SUBGROUP_GENERATED»
  FORALL_AND_THM := Session.FORALL_AND_THM
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_UNWIND_THM2 := Session.FORALL_UNWIND_THM2
  FROBENIUS_ELEMENT_IN_DECOMPOSITION_GROUP := SessionANT.Decomposition.«FROBENIUS_ELEMENT_IN_DECOMPOSITION_GROUP»
  FUN_EQ_THM := Session.FUN_EQ_THM
  GALOIS_CORRESPONDENCE_DEGREE := SessionLibrary.Galois.«GALOIS_CORRESPONDENCE_DEGREE»
  GALOIS_EXTENSION_EQ_CARD := SessionLibrary.Galois.«GALOIS_EXTENSION_EQ_CARD»
  GALOIS_EXTENSION_SUBFIELD_GENERATED := SessionLibrary.Galois.«GALOIS_EXTENSION_SUBFIELD_GENERATED»
  GALOIS_GROUP := SessionLibrary.Galois.«GALOIS_GROUP»
  GALOIS_GROUP_FIXED_FIELD := SessionLibrary.Galois.«GALOIS_GROUP_FIXED_FIELD»
  GALOIS_GROUP_FIXES := SessionLibrary.Galois.«GALOIS_GROUP_FIXES»
  GALOIS_GROUP_I := SessionLibrary.Galois.«GALOIS_GROUP_I»
  GALOIS_GROUP_IMAGE_NORMAL_INTERMEDIATE := SessionLibrary.Galois.«GALOIS_GROUP_IMAGE_NORMAL_INTERMEDIATE»
  GALOIS_GROUP_INTERMEDIATE_SUBGROUP_GENERATED := SessionLibrary.Galois.«GALOIS_GROUP_INTERMEDIATE_SUBGROUP_GENERATED»
  GALOIS_GROUP_INVERSE := SessionLibrary.Galois.«GALOIS_GROUP_INVERSE»
  GALOIS_GROUP_IN_CARRIER := SessionLibrary.Galois.«GALOIS_GROUP_IN_CARRIER»
  GALOIS_GROUP_PERMUTES := SessionLibrary.Galois.«GALOIS_GROUP_PERMUTES»
  GALOIS_GROUP_PRIME_IDEAL_IMAGE := SessionANT.Decomposition.«GALOIS_GROUP_PRIME_IDEAL_IMAGE»
  GALOIS_GROUP_RESTRICTION := SessionLibrary.Galois.«GALOIS_GROUP_RESTRICTION»
  GALOIS_GROUP_RING_OF_INTEGERS := SessionANT.NfDecomposition.«GALOIS_GROUP_RING_OF_INTEGERS»
  GALOIS_IMP_FIELD_EXTENSION := SessionLibrary.Galois.«GALOIS_IMP_FIELD_EXTENSION»
  GALOIS_IMP_NORMAL_EXTENSION := SessionLibrary.Galois.«GALOIS_IMP_NORMAL_EXTENSION»
  GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET := SessionLibrary.GroupTheory.«GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET»
  GROUP_ID := SessionLibrary.GroupTheory.«GROUP_ID»
  GROUP_NPOW := SessionLibrary.GroupTheory.«GROUP_NPOW»
  GROUP_POW := SessionLibrary.GroupTheory.«GROUP_POW»
  GROUP_POW_MUL := SessionLibrary.GroupTheory.«GROUP_POW_MUL»
  GROUP_POW_SUBGROUP_GENERATED := SessionLibrary.GroupTheory.«GROUP_POW_SUBGROUP_GENERATED»
  GROUP_ZPOW_EQ := SessionLibrary.GroupTheory.«GROUP_ZPOW_EQ»
  GROUP_ZPOW_MUL := SessionLibrary.GroupTheory.«GROUP_ZPOW_MUL»
  IDEAL_NORM_RESIDUE_DEGREE := SessionANT.RelativeSplit.«IDEAL_NORM_RESIDUE_DEGREE»
  IDEAL_NORM_RESIDUE_IMAGE := SessionANT.NfDecomposition.«IDEAL_NORM_RESIDUE_IMAGE»
  IMAGE_EQ := Session.IMAGE_EQ
  IMAGE_I := Session.IMAGE_I
  IMAGE_ID := Session.IMAGE_ID
  IMAGE_INTER_INJ := Session.IMAGE_INTER_INJ
  IMP_CONJ := Session.IMP_CONJ
  INERTIA_GROUP := SessionANT.Decomposition.«INERTIA_GROUP»
  INERTIA_GROUP_CONJUGATE := SessionANT.Decomposition.«INERTIA_GROUP_CONJUGATE»
  INERTIA_GROUP_INTERMEDIATE := SessionANT.Decomposition.«INERTIA_GROUP_INTERMEDIATE»
  INERTIA_GROUP_SUBGROUP_OF_DECOMPOSITION_GROUP := SessionANT.Decomposition.«INERTIA_GROUP_SUBGROUP_OF_DECOMPOSITION_GROUP»
  INERT_RESIDUE_DEGREE := SessionANT.SplittingTypes.«INERT_RESIDUE_DEGREE»
  INTER_IDEMPOT := Session.INTER_IDEMPOT
  INTER_SUBSET := Session.INTER_SUBSET
  INT_OF_NUM_MUL := Session.INT_OF_NUM_MUL
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_FIXED_FIELD := SessionLibrary.Galois.«IN_FIXED_FIELD»
  IN_GALOIS_GROUP := SessionLibrary.Galois.«IN_GALOIS_GROUP»
  IN_GALOIS_GROUP_SUBFIELD_GENERATED := SessionLibrary.Galois.«IN_GALOIS_GROUP_SUBFIELD_GENERATED»
  IN_IMAGE := Session.IN_IMAGE
  IN_INTER := Session.IN_INTER
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_RING_IDEAL_SUB := SessionLibrary.RingTheory.«IN_RING_IDEAL_SUB»
  IN_SING := Session.IN_SING
  IN_UNION := Session.IN_UNION
  IN_UNIONS := Session.IN_UNIONS
  IN_UNIV := Session.IN_UNIV
  I_O_ID := Session.I_O_ID
  I_THM := Session.I_THM
/-- The core theorems decomposition_field.ml uses. -/
def core2 : HolANT.DecompositionField.CoreThms2 where
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MULT_AC := Session.MULT_AC
  MULT_ASSOC := Session.MULT_ASSOC
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_EQ_0 := Session.MULT_EQ_0
  MULT_EQ_1 := Session.MULT_EQ_1
  NORMAL_IMP_ALGEBRAIC_EXTENSION := SessionLibrary.FieldTheory.«NORMAL_IMP_ALGEBRAIC_EXTENSION»
  NUMBER_FIELD_DECOMPOSITION_GROUP := SessionANT.NfDecomposition.«NUMBER_FIELD_DECOMPOSITION_GROUP»
  NUMBER_FIELD_DECOMPOSITION_GROUP_FROBENIUS := SessionANT.NfDecomposition.«NUMBER_FIELD_DECOMPOSITION_GROUP_FROBENIUS»
  NUMBER_FIELD_FROBENIUS_ELEMENT := SessionANT.NfDecomposition.«NUMBER_FIELD_FROBENIUS_ELEMENT»
  NUMBER_FIELD_GALOIS_GROUP_TRANSITIVE := SessionANT.NfDecomposition.«NUMBER_FIELD_GALOIS_GROUP_TRANSITIVE»
  NUMBER_FIELD_HOMOMORPHIC_PREIMAGE := SessionANT.RelativeSplit.«NUMBER_FIELD_HOMOMORPHIC_PREIMAGE»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_PRIME_IDEALS_ABOVE := SessionANT.RelativeSplit.«NUMBER_FIELD_PRIME_IDEALS_ABOVE»
  NUMBER_FIELD_PRIME_IDEAL_ABOVE := SessionANT.RelativeSplit.«NUMBER_FIELD_PRIME_IDEAL_ABOVE»
  NUMBER_FIELD_RAMIFICATION_INDEX_CONJUGATE := SessionANT.NfDecomposition.«NUMBER_FIELD_RAMIFICATION_INDEX_CONJUGATE»
  NUMBER_FIELD_RAMIFICATION_INDEX_TOWER := SessionANT.RelativeSplit.«NUMBER_FIELD_RAMIFICATION_INDEX_TOWER»
  NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS := SessionANT.RelativeDegree.«NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS»
  NUMBER_FIELD_RESIDUE_DEGREE_TOWER := SessionANT.RelativeSplit.«NUMBER_FIELD_RESIDUE_DEGREE_TOWER»
  NUMBER_FIELD_SUBFIELD_GENERATED := SessionANT.RelativeSplit.«NUMBER_FIELD_SUBFIELD_GENERATED»
  NUMBER_FIELD_TOWER_LAW := SessionANT.RelativeSplit.«NUMBER_FIELD_TOWER_LAW»
  NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED := SessionANT.SplittingTypes.«NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED»
  NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP := SessionANT.NfDecomposition.«NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP»
  PERMUTES_IMAGE := SessionLibrary.Permutations.«PERMUTES_IMAGE»
  PERMUTES_INJECTIVE := SessionLibrary.Permutations.«PERMUTES_INJECTIVE»
  PERMUTES_INVERSES := SessionLibrary.Permutations.«PERMUTES_INVERSES»
  PERMUTES_INVERSES_o := SessionLibrary.Permutations.«PERMUTES_INVERSES_o»
  PERMUTES_INVERSE_INVERSE := SessionLibrary.Permutations.«PERMUTES_INVERSE_INVERSE»
  PRIME_IDEAL_HOMOMORPHIC_PREIMAGE := SessionLibrary.RingTheory.«PRIME_IDEAL_HOMOMORPHIC_PREIMAGE»
  PRIME_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«PRIME_IDEAL_IMP_SUBSET»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PRIME_SUBFIELD_MINIMAL := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_MINIMAL»
  PRIME_SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_SUBFIELD_GENERATED»
  RIGHT_AND_EXISTS_THM := Session.RIGHT_AND_EXISTS_THM
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RING_HOMOMORPHISM_INTO_SUBRING := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTO_SUBRING»
  RING_HOMOMORPHISM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_HOMOMORPHISM_RING_OF_INTEGERS»
  RING_HOMOMORPHISM_SUBFIELD_INCLUSION := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_SUBFIELD_INCLUSION»
  RING_MONOMORPHISM_EQ_0 := SessionLibrary.RingTheory.«RING_MONOMORPHISM_EQ_0»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MONOMORPHISM_INTO_SUBRING := SessionLibrary.RingTheory.«RING_MONOMORPHISM_INTO_SUBRING»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_PRIME_IDEAL_BELOW := SessionANT.RelativeSplit.«RING_OF_INTEGERS_PRIME_IDEAL_BELOW»
  RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION := SessionANT.RelativeSplit.«RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION»
  RING_OF_INTEGERS_PRIME_SUBFIELD_IDEAL := SessionANT.RelativeSplit.«RING_OF_INTEGERS_PRIME_SUBFIELD_IDEAL»
  RING_OF_INTEGERS_SUBFIELD_GENERATED := SessionANT.RelativeSplit.«RING_OF_INTEGERS_SUBFIELD_GENERATED»
  RING_OF_INTEGERS_SUBRING := SessionANT.Numfield.«RING_OF_INTEGERS_SUBRING»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_NUM_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_NUM_SUBFIELD_GENERATED»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_POW_SUBFIELD_GENERATED»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_SUB_SUBFIELD_GENERATED»
  SEPARABLE_EXTENSION_CHAR0 := SessionLibrary.FieldTheory.«SEPARABLE_EXTENSION_CHAR0»
  SING_SUBSET := Session.SING_SUBSET
  SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED»
  SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED»
  SUBFIELD_GENERATED_INC := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_INC»
  SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_SUBFIELD_GENERATED»
  SUBGROUP_SUBGROUP_GENERATED := SessionLibrary.GroupTheory.«SUBGROUP_SUBGROUP_GENERATED»
  SUBRING_GENERATED_BY_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBRING_GENERATED_BY_SUBFIELD_GENERATED»
  SUBSET := Session.SUBSET
  SUBSET_TRANS := Session.SUBSET_TRANS
  SWAP_FORALL_THM := Session.SWAP_FORALL_THM
  TOTALLY_RAMIFIED_RAMIFICATION_INDEX := SessionANT.SplittingTypes.«TOTALLY_RAMIFIED_RAMIFICATION_INDEX»
  TOTALLY_SPLIT_CARD := SessionANT.SplittingTypes.«TOTALLY_SPLIT_CARD»
  UNIONS_SUBSET := Session.UNIONS_SUBSET
  UNION_SUBSET := Session.UNION_SUBSET
  UNWIND_THM2 := Session.UNWIND_THM2
  abelian_group := SessionLibrary.GroupTheory.«abelian_group»
  decomposition_group := SessionANT.Decomposition.«decomposition_group»
  divides := Session.divides
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  galois_extension := SessionLibrary.Galois.«galois_extension»
  group_epimorphism := SessionLibrary.GroupTheory.«group_epimorphism»
  group_homomorphism := SessionLibrary.GroupTheory.«group_homomorphism»
  group_pow := SessionLibrary.GroupTheory.«group_pow»
  group_zpow := SessionLibrary.GroupTheory.«group_zpow»
  inertia_group := SessionANT.Decomposition.«inertia_group»
  num_divides := Session.num_divides
  number_field := SessionANT.Numfield.«number_field»
  o_ASSOC := Session.o_ASSOC
  o_THM := Session.o_THM
  subgroup_of := SessionLibrary.GroupTheory.«subgroup_of»
  totally_split := SessionANT.SplittingTypes.«totally_split»
  weakly_unramified := SessionANT.SplittingTypes.«weakly_unramified»

/-- What decomposition_field.ml uses from Session. -/
def deps : HolANT.DecompositionField.DecompositionFieldDeps where
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

/- The bundles, in decomposition_field.ml order. -/
initialize BDecompositionField01 : HolANT.DecompositionField.DecompositionField01 ←
  ioB "setupDecompositionField01" (HolANT.DecompositionField.setupDecompositionField01 deps).run
initialize BDecompositionField02 : HolANT.DecompositionField.DecompositionField02 ←
  ioB "setupDecompositionField02" (HolANT.DecompositionField.setupDecompositionField02 deps BDecompositionField01).run
initialize BDecompositionField03 : HolANT.DecompositionField.DecompositionField03 ←
  ioB "setupDecompositionField03" (HolANT.DecompositionField.setupDecompositionField03 deps BDecompositionField01).run
initialize BDecompositionField04 : HolANT.DecompositionField.DecompositionField04 ←
  ioB "setupDecompositionField04" (HolANT.DecompositionField.setupDecompositionField04 deps BDecompositionField01).run

-- DecompositionField01
def NUMBER_FIELD_INTERMEDIATE_FIELD : thm := BDecompositionField01.NUMBER_FIELD_INTERMEDIATE_FIELD
def NUMBER_FIELD_GALOIS_INTERMEDIATE : thm := BDecompositionField01.NUMBER_FIELD_GALOIS_INTERMEDIATE
def NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE : thm := BDecompositionField01.NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE
def NUMBER_FIELD_PRIME_IDEALS_INTERMEDIATE : thm := BDecompositionField01.NUMBER_FIELD_PRIME_IDEALS_INTERMEDIATE
def NUMBER_FIELD_SUBFIELD_PRIME_IDEALS_ABOVE : thm := BDecompositionField01.NUMBER_FIELD_SUBFIELD_PRIME_IDEALS_ABOVE
def NUMBER_FIELD_DECOMPOSITION_GROUP_INTERMEDIATE : thm := BDecompositionField01.NUMBER_FIELD_DECOMPOSITION_GROUP_INTERMEDIATE
def NUMBER_FIELD_INTERMEDIATE_SPLITTING : thm := BDecompositionField01.NUMBER_FIELD_INTERMEDIATE_SPLITTING
def NUMBER_FIELD_INTERMEDIATE_SPLITTING_TYPES : thm := BDecompositionField01.NUMBER_FIELD_INTERMEDIATE_SPLITTING_TYPES
def NUMBER_FIELD_GENERATED_SPLITTING_TYPES : thm := BDecompositionField01.NUMBER_FIELD_GENERATED_SPLITTING_TYPES
def NUMBER_FIELD_GALOIS_UNRAMIFIED_MONO : thm := BDecompositionField01.NUMBER_FIELD_GALOIS_UNRAMIFIED_MONO
def NUMBER_FIELD_GALOIS_SPLITTING_TYPES : thm := BDecompositionField01.NUMBER_FIELD_GALOIS_SPLITTING_TYPES

-- DecompositionField02
def NUMBER_FIELD_ABELIAN_DECOMPOSITION_GROUP : thm := BDecompositionField02.NUMBER_FIELD_ABELIAN_DECOMPOSITION_GROUP
def NUMBER_FIELD_DECOMPOSITION_FIELD : thm := BDecompositionField02.NUMBER_FIELD_DECOMPOSITION_FIELD
def NUMBER_FIELD_INERTIA_DECOMPOSITION_TOWER : thm := BDecompositionField02.NUMBER_FIELD_INERTIA_DECOMPOSITION_TOWER

-- DecompositionField03
def NUMBER_FIELD_FROBENIUS_ELEMENT_INTERMEDIATE : thm := BDecompositionField03.NUMBER_FIELD_FROBENIUS_ELEMENT_INTERMEDIATE
def NUMBER_FIELD_INTERMEDIATE_FROBENIUS_ORDER : thm := BDecompositionField03.NUMBER_FIELD_INTERMEDIATE_FROBENIUS_ORDER
def NUMBER_FIELD_DECOMPOSITION_GROUP_RESTRICTION : thm := BDecompositionField03.NUMBER_FIELD_DECOMPOSITION_GROUP_RESTRICTION
def NUMBER_FIELD_FROBENIUS_ELEMENT_RESTRICTION : thm := BDecompositionField03.NUMBER_FIELD_FROBENIUS_ELEMENT_RESTRICTION
def NUMBER_FIELD_COMPOSITUM_SPLITTING_TYPES : thm := BDecompositionField03.NUMBER_FIELD_COMPOSITUM_SPLITTING_TYPES

-- DecompositionField04
def NUMBER_FIELD_NORMAL_CLOSURE_SPLITTING_TYPES : thm := BDecompositionField04.NUMBER_FIELD_NORMAL_CLOSURE_SPLITTING_TYPES
def NUMBER_FIELD_UNRAMIFIED_INERTIA_FIXED_FIELD : thm := BDecompositionField04.NUMBER_FIELD_UNRAMIFIED_INERTIA_FIXED_FIELD

/-- `needs "ANT/decomposition_field.ml"`: already done by importing this module. -/
def ensureDecompositionField : IO Unit := pure ()

end SessionANT.DecompositionField
