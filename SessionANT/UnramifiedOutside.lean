/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/unramified_outside.ml                         . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/UnramifiedOutside.lean

  The session half of the unramified_outside.ml translation: it supplies HolANT.UnramifiedOutside's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/unramified_outside.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.UnramifiedOutside
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
import SessionANT.Algmisc
import SessionANT.Integral
import SessionANT.IdealArith
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.IdealNorm
import SessionLibrary.Isum
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.RingOfIntegers
import SessionANT.NormIndex
import SessionANT.Classgroup
import SessionANT.PrimeSplit
import SessionANT.Discriminant
import SessionANT.TraceForm
import SessionANT.RelativeSplit
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
import SessionLibrary.SymmetricGroup
import SessionLibrary.Galois
import SessionLibrary.RingGroups
import SessionLibrary.FiniteFields
import SessionANT.Decomposition
import SessionANT.NfValuation
import SessionANT.RelativeDegree
import SessionANT.FiniteFieldTrace
import SessionANT.Ramification
import SessionANT.SplittingTypes
import SessionANT.NfDecomposition

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.UnramifiedOutside

/-- The core theorems unramified_outside.ml uses. -/
def core1 : HolANT.UnramifiedOutside.CoreThms1 where
  ALGEBRAICALLY_CLOSED_IMP_NORMAL_EXTENSION := SessionLibrary.FieldTheory.«ALGEBRAICALLY_CLOSED_IMP_NORMAL_EXTENSION»
  ALGEBRAIC_IMP_FIELD_EXTENSION := SessionLibrary.FieldTheory.«ALGEBRAIC_IMP_FIELD_EXTENSION»
  CARRIER_SUBFIELD_GENERATED_SUBFIELD := SessionLibrary.FieldTheory.«CARRIER_SUBFIELD_GENERATED_SUBFIELD»
  DECOMPOSITION_GROUP_RING_OF_INTEGERS := SessionANT.NfDecomposition.«DECOMPOSITION_GROUP_RING_OF_INTEGERS»
  EMPTY_SUBSET := Session.EMPTY_SUBSET
  EQ_SYM_EQ := Session.EQ_SYM_EQ
  EXTENSION := Session.EXTENSION
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FINITE_EXTENSION_ISOMORPHISM := SessionLibrary.FieldTheory.«FINITE_EXTENSION_ISOMORPHISM»
  FINITE_EXTENSION_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FINITE_EXTENSION_SUBFIELD_GENERATED»
  FINITE_EXTENSION_SUBFIELD_GENERATORS := SessionLibrary.FieldTheory.«FINITE_EXTENSION_SUBFIELD_GENERATORS»
  FINITE_IMP_FIELD_EXTENSION := SessionLibrary.FieldTheory.«FINITE_IMP_FIELD_EXTENSION»
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FUN_EQ_THM := Session.FUN_EQ_THM
  GALOIS_EXTENSION_COMPOSITUM := SessionLibrary.Galois.«GALOIS_EXTENSION_COMPOSITUM»
  GALOIS_EXTENSION_ISOMORPHISM := SessionLibrary.Galois.«GALOIS_EXTENSION_ISOMORPHISM»
  GALOIS_EXTENSION_UNION_FINITE_GALOIS_SUBFIELDS := SessionLibrary.Galois.«GALOIS_EXTENSION_UNION_FINITE_GALOIS_SUBFIELDS»
  GALOIS_GROUP := SessionLibrary.Galois.«GALOIS_GROUP»
  GALOIS_GROUP_EQ_ON_GENERATORS := SessionLibrary.Galois.«GALOIS_GROUP_EQ_ON_GENERATORS»
  GALOIS_GROUP_I := SessionLibrary.Galois.«GALOIS_GROUP_I»
  GALOIS_GROUP_PERMUTES := SessionLibrary.Galois.«GALOIS_GROUP_PERMUTES»
  GALOIS_GROUP_RESTRICTION_NORMAL := SessionLibrary.Galois.«GALOIS_GROUP_RESTRICTION_NORMAL»
  GALOIS_IMP_NORMAL_EXTENSION := SessionLibrary.Galois.«GALOIS_IMP_NORMAL_EXTENSION»
  GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET := SessionLibrary.GroupTheory.«GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET»
  GROUP_ID := SessionLibrary.GroupTheory.«GROUP_ID»
  IMAGE_EQ := Session.IMAGE_EQ
  IMAGE_I := Session.IMAGE_I
  IMAGE_INTER_INJ := Session.IMAGE_INTER_INJ
  IMP_CONJ := Session.IMP_CONJ
  INERTIA_GROUP := SessionANT.Decomposition.«INERTIA_GROUP»
  INSERT_SUBSET := Session.INSERT_SUBSET
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_FINITE_GALOIS_SUBFIELDS := SessionLibrary.Galois.«IN_FINITE_GALOIS_SUBFIELDS»
  IN_INTER := Session.IN_INTER
  IN_SING := Session.IN_SING
  IN_UNION := Session.IN_UNION
  IN_UNIONS := Session.IN_UNIONS
  I_O_ID := Session.I_O_ID
  I_THM := Session.I_THM
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MONO_EXISTS := Session.MONO_EXISTS
  MULT_EQ_1 := Session.MULT_EQ_1
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_PRIME_IDEALS_ABOVE := SessionANT.RelativeSplit.«NUMBER_FIELD_PRIME_IDEALS_ABOVE»
  NUMBER_FIELD_PRIME_IDEAL_ABOVE := SessionANT.RelativeSplit.«NUMBER_FIELD_PRIME_IDEAL_ABOVE»
  NUMBER_FIELD_RAMIFICATION_INDEX_TOWER := SessionANT.RelativeSplit.«NUMBER_FIELD_RAMIFICATION_INDEX_TOWER»
  NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED := SessionANT.SplittingTypes.«NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED»
  NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP := SessionANT.NfDecomposition.«NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP»
  PERFECT_FIELD_CHAR_0 := SessionLibrary.FieldTheory.«PERFECT_FIELD_CHAR_0»
  PERFECT_FIELD_IMP_SEPARABLE_EXTENSION := SessionLibrary.FieldTheory.«PERFECT_FIELD_IMP_SEPARABLE_EXTENSION»
  PERMUTES_INJECTIVE := SessionLibrary.Permutations.«PERMUTES_INJECTIVE»
  PRIME_IDEAL_HOMOMORPHIC_PREIMAGE := SessionLibrary.RingTheory.«PRIME_IDEAL_HOMOMORPHIC_PREIMAGE»
  PRIME_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«PRIME_IDEAL_IMP_SUBSET»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PRIME_SUBFIELD_TOWER_LAW := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_TOWER_LAW»
  RING_HOMOMORPHISM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_HOMOMORPHISM_RING_OF_INTEGERS»
  RING_ISOMORPHISM_ONTO_SUBFIELD_IMAGE := SessionLibrary.FieldTheory.«RING_ISOMORPHISM_ONTO_SUBFIELD_IMAGE»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_OF_INTEGERS_SUBFIELD_GENERATED := SessionANT.RelativeSplit.«RING_OF_INTEGERS_SUBFIELD_GENERATED»
  RING_OF_INTEGERS_SUBRING := SessionANT.Numfield.«RING_OF_INTEGERS_SUBRING»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_SUB_SUBFIELD_GENERATED»
  SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED»
  SUBFIELD_GENERATED_IDEMPOT_GEN := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_IDEMPOT_GEN»
  SUBFIELD_GENERATED_INC := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_INC»
  SUBFIELD_GENERATED_MINIMAL := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_MINIMAL»
  SUBFIELD_OF_IMP_SUBSET := SessionLibrary.FieldTheory.«SUBFIELD_OF_IMP_SUBSET»
  SUBFIELD_OF_SUBFIELD_GENERATED_SUBFIELD_EQ := SessionLibrary.FieldTheory.«SUBFIELD_OF_SUBFIELD_GENERATED_SUBFIELD_EQ»
  SUBFIELD_OF_UNIONS_DIRECTED := SessionLibrary.FieldTheory.«SUBFIELD_OF_UNIONS_DIRECTED»
  SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_SUBFIELD_GENERATED»
  SUBGROUP_GENERATED := SessionLibrary.GroupTheory.«SUBGROUP_GENERATED»
  SUBSET := Session.SUBSET
  SUBSET_REFL := Session.SUBSET_REFL
  SUBSET_TRANS := Session.SUBSET_TRANS
  TRIVIAL_GALOIS_GROUP := SessionLibrary.Galois.«TRIVIAL_GALOIS_GROUP»
  TRIVIAL_GROUP_SUBGROUP_GENERATED := SessionLibrary.GroupTheory.«TRIVIAL_GROUP_SUBGROUP_GENERATED»
  UNION_SUBSET := Session.UNION_SUBSET
  UNRAMIFIED_IMP_WEAKLY_UNRAMIFIED := SessionANT.SplittingTypes.«UNRAMIFIED_IMP_WEAKLY_UNRAMIFIED»
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  galois_extension := SessionLibrary.Galois.«galois_extension»
  group_homomorphism := SessionLibrary.GroupTheory.«group_homomorphism»
  inertia_group := SessionANT.Decomposition.«inertia_group»
  number_field := SessionANT.Numfield.«number_field»
  ring_homomorphism := SessionLibrary.RingTheory.«ring_homomorphism»
  trivial_group := SessionLibrary.GroupTheory.«trivial_group»
  weakly_unramified := SessionANT.SplittingTypes.«weakly_unramified»

/-- What unramified_outside.ml uses from Session. -/
def deps : HolANT.UnramifiedOutside.UnramifiedOutsideDeps where
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

/- The bundles, in unramified_outside.ml order. -/
initialize BUnramifiedOutside : HolANT.UnramifiedOutside.UnramifiedOutside ←
  ioB "setupUnramifiedOutside" (HolANT.UnramifiedOutside.setupUnramifiedOutside deps).run

-- UnramifiedOutside
def FINITE_SUBEXTENSION_NUMBER_FIELD : thm := BUnramifiedOutside.FINITE_SUBEXTENSION_NUMBER_FIELD
def unramified_outside : thm := BUnramifiedOutside.unramified_outside
def UNRAMIFIED_OUTSIDE_BASE : thm := BUnramifiedOutside.UNRAMIFIED_OUTSIDE_BASE
def UNRAMIFIED_OUTSIDE_SUBFIELD : thm := BUnramifiedOutside.UNRAMIFIED_OUTSIDE_SUBFIELD
def INERTIA_GROUP_UNRAMIFIED_SUBFIELD : thm := BUnramifiedOutside.INERTIA_GROUP_UNRAMIFIED_SUBFIELD
def UNRAMIFIED_OUTSIDE_COMPOSITUM : thm := BUnramifiedOutside.UNRAMIFIED_OUTSIDE_COMPOSITUM
def maximal_unramified_outside : thm := BUnramifiedOutside.maximal_unramified_outside
def MAXIMAL_UNRAMIFIED_OUTSIDE_FINITE_SUBSET : thm := BUnramifiedOutside.MAXIMAL_UNRAMIFIED_OUTSIDE_FINITE_SUBSET
def MAXIMAL_UNRAMIFIED_OUTSIDE : thm := BUnramifiedOutside.MAXIMAL_UNRAMIFIED_OUTSIDE
def MAXIMAL_UNRAMIFIED_OUTSIDE_SUBEXTENSION : thm := BUnramifiedOutside.MAXIMAL_UNRAMIFIED_OUTSIDE_SUBEXTENSION
def MAXIMAL_UNRAMIFIED_OUTSIDE_FINITE_GALOIS : thm := BUnramifiedOutside.MAXIMAL_UNRAMIFIED_OUTSIDE_FINITE_GALOIS
def GALOIS_MAXIMAL_UNRAMIFIED_OUTSIDE : thm := BUnramifiedOutside.GALOIS_MAXIMAL_UNRAMIFIED_OUTSIDE
def NUMBER_FIELD_ALGEBRAIC_CLOSURE_GALOIS : thm := BUnramifiedOutside.NUMBER_FIELD_ALGEBRAIC_CLOSURE_GALOIS

/-- `needs "ANT/unramified_outside.ml"`: already done by importing this module. -/
def ensureUnramifiedOutside : IO Unit := pure ()

end SessionANT.UnramifiedOutside
