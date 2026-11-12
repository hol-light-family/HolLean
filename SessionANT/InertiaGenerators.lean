/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/inertia_generators.ml                         . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/InertiaGenerators.lean

  The session half of the inertia_generators.ml translation: it supplies HolANT.InertiaGenerators's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/inertia_generators.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.InertiaGenerators
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
import SessionANT.RelativeDegree
import SessionANT.FiniteFieldTrace
import SessionANT.Ramification
import SessionANT.SplittingTypes
import SessionANT.LinearForms
import SessionANT.ClassgroupGroup
import SessionANT.Quadratic
import SessionANT.NfValuation
import SessionANT.Integrality
import SessionLibrary.RingGroups
import SessionANT.FingenGroup
import SessionMultiLib.Misc
import SessionMultiLib.Metric
import SessionMultiLib.Homology
import SessionMultiLib.Vectors
import SessionMultiLib.Determinants
import SessionMultiLib.Topology
import SessionMultiLib.Convex
import SessionMultiLib.Paths
import SessionMultiLib.Polytope
import SessionMultiLib.Degree
import SessionMultiLib.Derivatives
import SessionMultiLib.Integration
import SessionMultiLib.Measure
import SessionMultiLib.ComplexAlgebra
import SessionMultiLib.Complexes
import SessionMultiLib.Canal
import SessionMultiLib.Transcendentals
import SessionMultiLib.RealAnalysis
import SessionMultiLib.MoreTop
import SessionMultiLib.Cauchy
import SessionMultiLib.ComplexRing
import SessionMultiLib.ComplexField
import SessionANT.ComplexEmbeddings
import SessionANT.PowerBasis
import SessionANT.InfinitePlaces
import SessionANT.MinkowskiTheory
import SessionLibrary.FiniteFields
import SessionANT.Decomposition
import SessionANT.NfDecomposition
import SessionANT.DecompositionField

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.InertiaGenerators

/-- The core theorems inertia_generators.ml uses. -/
def core1 : HolANT.InertiaGenerators.CoreThms1 where
  DIVIDES_ZERO := SessionLibrary.Prime.«DIVIDES_ZERO»
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXTENSION := Session.EXTENSION
  EXTENSION_DEGREE_EQ_1 := SessionLibrary.FieldTheory.«EXTENSION_DEGREE_EQ_1»
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  GALOIS_GROUP_FIXED_FIELD := SessionLibrary.Galois.«GALOIS_GROUP_FIXED_FIELD»
  GALOIS_IMP_FIELD_EXTENSION := SessionLibrary.Galois.«GALOIS_IMP_FIELD_EXTENSION»
  IN_GALOIS_GROUP := SessionLibrary.Galois.«IN_GALOIS_GROUP»
  IN_GALOIS_GROUP_SUBFIELD_GENERATED := SessionLibrary.Galois.«IN_GALOIS_GROUP_SUBFIELD_GENERATED»
  IN_SING := Session.IN_SING
  LE_MULT2 := Session.LE_MULT2
  LE_REFL := Session.LE_REFL
  LE_TRANS := Session.LE_TRANS
  MULT_CLAUSES := Session.MULT_CLAUSES
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NUMBER_FIELD_HOMOMORPHIC_PREIMAGE := SessionANT.RelativeSplit.«NUMBER_FIELD_HOMOMORPHIC_PREIMAGE»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_INTERMEDIATE_FIELD := SessionANT.DecompositionField.«NUMBER_FIELD_INTERMEDIATE_FIELD»
  NUMBER_FIELD_RAMIFICATION_INDEX_TOWER_Q := SessionANT.RelativeSplit.«NUMBER_FIELD_RAMIFICATION_INDEX_TOWER_Q»
  NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS := SessionANT.RelativeDegree.«NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS»
  NUMBER_FIELD_RAMIFIED_PRIME_EXISTS := SessionANT.MinkowskiTheory.«NUMBER_FIELD_RAMIFIED_PRIME_EXISTS»
  NUMBER_FIELD_TOWER_LAW := SessionANT.RelativeSplit.«NUMBER_FIELD_TOWER_LAW»
  NUMBER_FIELD_UNRAMIFIED_INERTIA_FIXED_FIELD := SessionANT.DecompositionField.«NUMBER_FIELD_UNRAMIFIED_INERTIA_FIXED_FIELD»
  PRIME_0 := SessionLibrary.Prime.«PRIME_0»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  RAMIFICATION_INDEX_PRIME_SUBFIELD := SessionANT.RelativeSplit.«RAMIFICATION_INDEX_PRIME_SUBFIELD»
  RING_HOMOMORPHISM_SUBFIELD_INCLUSION := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_SUBFIELD_INCLUSION»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_OF_INTEGERS_PRIME_IDEAL_BELOW := SessionANT.RelativeSplit.«RING_OF_INTEGERS_PRIME_IDEAL_BELOW»
  RING_OF_NUM_EQ_0 := SessionLibrary.RingTheory.«RING_OF_NUM_EQ_0»
  SUBFIELD_OF_IMP_SUBSET := SessionLibrary.FieldTheory.«SUBFIELD_OF_IMP_SUBSET»
  SUBGROUP_GENERATED_EQ := SessionLibrary.GroupTheory.«SUBGROUP_GENERATED_EQ»
  SUBGROUP_SUBGROUP_GENERATED := SessionLibrary.GroupTheory.«SUBGROUP_SUBGROUP_GENERATED»
  SUBSET_REFL := Session.SUBSET_REFL
  UNRAMIFIED_IMP_WEAKLY_UNRAMIFIED := SessionANT.SplittingTypes.«UNRAMIFIED_IMP_WEAKLY_UNRAMIFIED»
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  number_field := SessionANT.Numfield.«number_field»
  weakly_unramified := SessionANT.SplittingTypes.«weakly_unramified»

/-- What inertia_generators.ml uses from Session. -/
def deps : HolANT.InertiaGenerators.InertiaGeneratorsDeps where
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

/- The bundles, in inertia_generators.ml order. -/
initialize BInertiaGenerators : HolANT.InertiaGenerators.InertiaGenerators ←
  ioB "setupInertiaGenerators" (HolANT.InertiaGenerators.setupInertiaGenerators deps).run

-- InertiaGenerators
def NUMBER_FIELD_RATIONAL_RAMIFICATION_INDEX : thm := BInertiaGenerators.NUMBER_FIELD_RATIONAL_RAMIFICATION_INDEX
def NUMBER_FIELD_UNRAMIFIED_RATIONAL : thm := BInertiaGenerators.NUMBER_FIELD_UNRAMIFIED_RATIONAL
def NUMBER_FIELD_INERTIA_GROUPS_GENERATE : thm := BInertiaGenerators.NUMBER_FIELD_INERTIA_GROUPS_GENERATE

/-- `needs "ANT/inertia_generators.ml"`: already done by importing this module. -/
def ensureInertiaGenerators : IO Unit := pure ()

end SessionANT.InertiaGenerators
