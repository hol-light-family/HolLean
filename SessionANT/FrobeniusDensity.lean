/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/frobenius_density.ml                          . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/FrobeniusDensity.lean

  The session half of the frobenius_density.ml translation: it supplies HolANT.FrobeniusDensity's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/frobenius_density.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.FrobeniusDensity
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
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
import SessionLibrary.SymmetricGroup
import SessionLibrary.Galois
import SessionLibrary.Products
import SessionLibrary.Floor
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
import SessionLibrary.Isum
import SessionANT.Algmisc
import SessionANT.IdealArith
import SessionANT.Integral
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionANT.Zlattice
import SessionANT.Numfield
import SessionANT.RingOfIntegers
import SessionANT.NormIndex
import SessionANT.Classgroup
import SessionANT.PrimeSplit
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.Discriminant
import SessionANT.TraceForm
import SessionANT.RelativeSplit
import SessionANT.FiniteFieldTrace
import SessionANT.Ramification
import SessionANT.RelativeDegree
import SessionANT.SplittingTypes
import SessionLibrary.RingGroups
import SessionLibrary.FiniteFields
import SessionANT.Decomposition
import SessionANT.NfValuation
import SessionANT.NfDecomposition
import SessionANT.DecompositionField
import SessionANT.Integrality
import SessionANT.FingenGroup
import SessionMultiLib.MoreTop
import SessionMultiLib.Cauchy
import SessionMultiLib.ComplexRing
import SessionMultiLib.ComplexField
import SessionANT.ComplexEmbeddings
import SessionANT.PowerBasis
import SessionANT.InfinitePlaces
import SessionANT.DedekindZeta

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.FrobeniusDensity

/-- The core theorems frobenius_density.ml uses. -/
def core1 : HolANT.FrobeniusDensity.CoreThms1 where
  ADD_CLAUSES := Session.ADD_CLAUSES
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARD_CONJUGATES_INTO_CYCLIC_GENERATORS := SessionLibrary.GroupTheory.«CARD_CONJUGATES_INTO_CYCLIC_GENERATORS»
  CARD_CONJUGATES_IN_TORSION_NSUM := SessionLibrary.GroupTheory.«CARD_CONJUGATES_IN_TORSION_NSUM»
  CARD_CROSS := Session.CARD_CROSS
  CARD_CYCLIC_SUBGROUP_DIVISION := SessionLibrary.GroupTheory.«CARD_CYCLIC_SUBGROUP_DIVISION»
  CARD_EQ_0 := Session.CARD_EQ_0
  CARD_IMAGE_INJ := Session.CARD_IMAGE_INJ
  CARD_RESTRICT_POW_EQ_ID := SessionLibrary.GroupTheory.«CARD_RESTRICT_POW_EQ_ID»
  CARD_SING := Session.CARD_SING
  CARRIER_SUBGROUP_GENERATED_SUBGROUP := SessionLibrary.GroupTheory.«CARRIER_SUBGROUP_GENERATED_SUBGROUP»
  COND_ID := Session.COND_ID
  CONJ_ASSOC := Session.CONJ_ASSOC
  CYCLIC_SUBGROUP_TORSION_SUBGROUP := SessionLibrary.GroupTheory.«CYCLIC_SUBGROUP_TORSION_SUBGROUP»
  DECOMPOSITION_GROUP := SessionANT.Decomposition.«DECOMPOSITION_GROUP»
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DIRICHLET_SERIES_FINITE_PERTURBATION := SessionMultiLib.RealAnalysis.«DIRICHLET_SERIES_FINITE_PERTURBATION»
  DIVIDES_LE := Session.DIVIDES_LE
  DIVIDES_REFL := SessionLibrary.Prime.«DIVIDES_REFL»
  DIVIDES_TRANS := SessionLibrary.Prime.«DIVIDES_TRANS»
  EMPTY_GSPEC := Session.EMPTY_GSPEC
  EQ_TRANS := Session.EQ_TRANS
  EXISTS_PAIR_THM := Session.EXISTS_PAIR_THM
  EXTENSION := Session.EXTENSION
  FINITE_CROSS := Session.FINITE_CROSS
  FINITE_DIVISORS := SessionLibrary.Prime.«FINITE_DIVISORS»
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_GALOIS_GROUP := SessionLibrary.Galois.«FINITE_GALOIS_GROUP»
  FINITE_GROUP_ELEMENT_ORDER_NONZERO := SessionLibrary.GroupTheory.«FINITE_GROUP_ELEMENT_ORDER_NONZERO»
  FINITE_GROUP_NORMALIZER := SessionLibrary.GroupTheory.«FINITE_GROUP_NORMALIZER»
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_RAMIFIED := SessionANT.SplittingTypes.«FINITE_RAMIFIED»
  FINITE_RESTRICT := Session.FINITE_RESTRICT
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  FUN_EQ_THM := Session.FUN_EQ_THM
  GALOIS_EXTENSION_EQ_CARD := SessionLibrary.Galois.«GALOIS_EXTENSION_EQ_CARD»
  GALOIS_EXTENSION_SUBFIELD_GENERATED := SessionLibrary.Galois.«GALOIS_EXTENSION_SUBFIELD_GENERATED»
  GALOIS_GROUP := SessionLibrary.Galois.«GALOIS_GROUP»
  GALOIS_GROUP_FIXED_FIELD := SessionLibrary.Galois.«GALOIS_GROUP_FIXED_FIELD»
  GALOIS_GROUP_PERMUTES := SessionLibrary.Galois.«GALOIS_GROUP_PERMUTES»
  GALOIS_IMP_FIELD_EXTENSION := SessionLibrary.Galois.«GALOIS_IMP_FIELD_EXTENSION»
  GROUP_CARRIER_NONEMPTY := SessionLibrary.GroupTheory.«GROUP_CARRIER_NONEMPTY»
  GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET := SessionLibrary.GroupTheory.«GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET»
  GROUP_CONJUGATION_BY_ID := SessionLibrary.GroupTheory.«GROUP_CONJUGATION_BY_ID»
  GROUP_CONJUGATION_CONJUGATION := SessionLibrary.GroupTheory.«GROUP_CONJUGATION_CONJUGATION»
  GROUP_CONJUGATION_EQ_ID := SessionLibrary.GroupTheory.«GROUP_CONJUGATION_EQ_ID»
  GROUP_ID := SessionLibrary.GroupTheory.«GROUP_ID»
  GROUP_INV := SessionLibrary.GroupTheory.«GROUP_INV»
  GROUP_MUL := SessionLibrary.GroupTheory.«GROUP_MUL»
  GROUP_MUL_RCANCEL := SessionLibrary.GroupTheory.«GROUP_MUL_RCANCEL»
  GROUP_NORMALIZER_NONEMPTY := SessionLibrary.GroupTheory.«GROUP_NORMALIZER_NONEMPTY»
  HAS_DIRICHLET_DENSITY_INFINITE := SessionANT.DedekindZeta.«HAS_DIRICHLET_DENSITY_INFINITE»
  HAS_DIRICHLET_DENSITY_LOG := SessionANT.DedekindZeta.«HAS_DIRICHLET_DENSITY_LOG»
  IMAGE_CLAUSES := Session.IMAGE_CLAUSES
  IMAGE_I := Session.IMAGE_I
  IMAGE_o := Session.IMAGE_o
  IMP_CONJ := Session.IMP_CONJ
  IN_CROSS := Session.IN_CROSS
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_FIXED_FIELD := SessionLibrary.Galois.«IN_FIXED_FIELD»
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_INTER := Session.IN_INTER
  IN_SING := Session.IN_SING
  IN_SUBGROUP_CONJUGATION := SessionLibrary.GroupTheory.«IN_SUBGROUP_CONJUGATION»
  I_O_ID := Session.I_O_ID
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_0 := Session.LE_0
  LE_REFL := Session.LE_REFL
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MONO_EXISTS := Session.MONO_EXISTS
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_SYM := Session.MULT_SYM
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NSUM_CASES := Session.NSUM_CASES
  NSUM_CLAUSES := Session.NSUM_CLAUSES
  NSUM_CONST := Session.NSUM_CONST
  NSUM_EQ := Session.NSUM_EQ
  NSUM_LMUL := Session.NSUM_LMUL
  NSUM_RESTRICT_SET := Session.NSUM_RESTRICT_SET
  NSUM_SUBSET_SIMPLE := Session.NSUM_SUBSET_SIMPLE
  NSUM_SWAP := Session.NSUM_SWAP
  NUMBER_FIELD_DECOMPOSITION_GROUP_FROBENIUS := SessionANT.NfDecomposition.«NUMBER_FIELD_DECOMPOSITION_GROUP_FROBENIUS»
/-- The core theorems frobenius_density.ml uses. -/
def core2 : HolANT.FrobeniusDensity.CoreThms2 where
  NUMBER_FIELD_DEGREE_ONE_PRIMES_LOG := SessionANT.DedekindZeta.«NUMBER_FIELD_DEGREE_ONE_PRIMES_LOG»
  NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM := SessionANT.Classgroup.«NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM»
  NUMBER_FIELD_FROBENIUS_CONJUGATE_PRIME := SessionANT.NfDecomposition.«NUMBER_FIELD_FROBENIUS_CONJUGATE_PRIME»
  NUMBER_FIELD_FROBENIUS_ELEMENT := SessionANT.NfDecomposition.«NUMBER_FIELD_FROBENIUS_ELEMENT»
  NUMBER_FIELD_GALOIS_GROUP_TRANSITIVE := SessionANT.NfDecomposition.«NUMBER_FIELD_GALOIS_GROUP_TRANSITIVE»
  NUMBER_FIELD_GALOIS_SPLITTING_TYPES := SessionANT.DecompositionField.«NUMBER_FIELD_GALOIS_SPLITTING_TYPES»
  NUMBER_FIELD_HOMOMORPHIC_PREIMAGE := SessionANT.RelativeSplit.«NUMBER_FIELD_HOMOMORPHIC_PREIMAGE»
  NUMBER_FIELD_IDEAL_SUM_BY_NORM := SessionANT.DedekindZeta.«NUMBER_FIELD_IDEAL_SUM_BY_NORM»
  NUMBER_FIELD_INTERMEDIATE_FIELD := SessionANT.DecompositionField.«NUMBER_FIELD_INTERMEDIATE_FIELD»
  NUMBER_FIELD_INTERMEDIATE_SPLITTING := SessionANT.DecompositionField.«NUMBER_FIELD_INTERMEDIATE_SPLITTING»
  NUMBER_FIELD_NONPRIME_NORM_SUM_LE := SessionANT.DedekindZeta.«NUMBER_FIELD_NONPRIME_NORM_SUM_LE»
  NUMBER_FIELD_PRIME_IDEALS_ABOVE := SessionANT.RelativeSplit.«NUMBER_FIELD_PRIME_IDEALS_ABOVE»
  NUMBER_FIELD_PRIME_IDEALS_INTERMEDIATE := SessionANT.DecompositionField.«NUMBER_FIELD_PRIME_IDEALS_INTERMEDIATE»
  NUMBER_FIELD_PRIME_IDEAL_DEGREE_ONE := SessionANT.PrimeSplit.«NUMBER_FIELD_PRIME_IDEAL_DEGREE_ONE»
  NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE := SessionANT.DecompositionField.«NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE»
  NUMBER_FIELD_PRIME_NORM_CARD := SessionANT.RelativeSplit.«NUMBER_FIELD_PRIME_NORM_CARD»
  NUMBER_FIELD_TOWER_LAW := SessionANT.RelativeSplit.«NUMBER_FIELD_TOWER_LAW»
  NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED := SessionANT.SplittingTypes.«NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED»
  NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP := SessionANT.NfDecomposition.«NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP»
  PAIR_EQ := Session.PAIR_EQ
  PERMUTES_INJECTIVE := SessionLibrary.Permutations.«PERMUTES_INJECTIVE»
  PERMUTES_INVERSES_o := SessionLibrary.Permutations.«PERMUTES_INVERSES_o»
  PRIME_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«PRIME_IDEAL_IMP_SUBSET»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  REAL_ABS_INV := Session.REAL_ABS_INV
  REAL_ABS_MUL := Session.REAL_ABS_MUL
  REAL_ABS_NUM := Session.REAL_ABS_NUM
  REAL_ADD_LDISTRIB := Session.REAL_ADD_LDISTRIB
  REAL_ADD_LID := Session.REAL_ADD_LID
  REAL_ADD_RID := Session.REAL_ADD_RID
  REAL_DIV_EQ_0 := Session.REAL_DIV_EQ_0
  REAL_EQ_IMP_LE := Session.REAL_EQ_IMP_LE
  REAL_INFSUM_ADD := SessionMultiLib.RealAnalysis.«REAL_INFSUM_ADD»
  REAL_INFSUM_LMUL := SessionMultiLib.RealAnalysis.«REAL_INFSUM_LMUL»
  REAL_INFSUM_UNIQUE := SessionMultiLib.RealAnalysis.«REAL_INFSUM_UNIQUE»
  REAL_LE_DIV := Session.REAL_LE_DIV
  REAL_LE_INV_EQ := Session.REAL_LE_INV_EQ
  REAL_LE_LMUL := Session.REAL_LE_LMUL
  REAL_LE_TRANS := Session.REAL_LE_TRANS
  REAL_MUL_ASSOC := Session.REAL_MUL_ASSOC
  REAL_MUL_LID := Session.REAL_MUL_LID
  REAL_MUL_LINV := Session.REAL_MUL_LINV
  REAL_MUL_LZERO := Session.REAL_MUL_LZERO
  REAL_OF_NUM_ADD := Session.REAL_OF_NUM_ADD
  REAL_OF_NUM_EQ := Session.REAL_OF_NUM_EQ
  REAL_OF_NUM_LE := Session.REAL_OF_NUM_LE
  REAL_OF_NUM_MUL := Session.REAL_OF_NUM_MUL
  REAL_OF_NUM_SUM := Session.REAL_OF_NUM_SUM
  REAL_POS := Session.REAL_POS
  REAL_SERIES_FINITE_SUM := SessionMultiLib.RealAnalysis.«REAL_SERIES_FINITE_SUM»
  REAL_SERIES_POS := SessionMultiLib.RealAnalysis.«REAL_SERIES_POS»
  REAL_SERIES_SUB := SessionMultiLib.RealAnalysis.«REAL_SERIES_SUB»
  REAL_SUMMABLE_ADD := SessionMultiLib.RealAnalysis.«REAL_SUMMABLE_ADD»
  REAL_SUMMABLE_LMUL := SessionMultiLib.RealAnalysis.«REAL_SUMMABLE_LMUL»
  REAL_SUMMABLE_POS_PARTIAL_BOUND := SessionMultiLib.RealAnalysis.«REAL_SUMMABLE_POS_PARTIAL_BOUND»
  REAL_SUMS_INFSUM := SessionMultiLib.RealAnalysis.«REAL_SUMS_INFSUM»
  RIGHT_EXISTS_IMP_THM := Session.RIGHT_EXISTS_IMP_THM
  RIGHT_IMP_EXISTS_THM := Session.RIGHT_IMP_EXISTS_THM
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RPOW_POS_LE := SessionMultiLib.Transcendentals.«RPOW_POS_LE»
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED»
  SUBGROUP_GENERATED_INC := SessionLibrary.GroupTheory.«SUBGROUP_GENERATED_INC»
  SUBGROUP_OF_IMP_SUBSET := SessionLibrary.GroupTheory.«SUBGROUP_OF_IMP_SUBSET»
  SUBSET := Session.SUBSET
  SUM_ABS := Session.SUM_ABS
  SUM_ADD := Session.SUM_ADD
  SUM_CLAUSES := Session.SUM_CLAUSES
  SUM_EQ_NUMSEG := Session.SUM_EQ_NUMSEG
  SUM_LE := Session.SUM_LE
  SUM_RMUL := Session.SUM_RMUL
  SUM_SUBSET_SIMPLE := Session.SUM_SUBSET_SIMPLE
  TRIVIAL_SUBGROUP_OF := SessionLibrary.GroupTheory.«TRIVIAL_SUBGROUP_OF»
  UNRAMIFIED_IMP_WEAKLY_UNRAMIFIED := SessionANT.SplittingTypes.«UNRAMIFIED_IMP_WEAKLY_UNRAMIFIED»
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  num_WF := Session.num_WF
  real_div := Session.real_div
  real_summable := SessionMultiLib.RealAnalysis.«real_summable»
  subgroup_of := SessionLibrary.GroupTheory.«subgroup_of»
  totally_split := SessionANT.SplittingTypes.«totally_split»
  weakly_unramified := SessionANT.SplittingTypes.«weakly_unramified»

/-- What frobenius_density.ml uses from Session. -/
def deps : HolANT.FrobeniusDensity.FrobeniusDensityDeps where
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
  REAL_RING t := ExceptT.mk (Session.REAL_RING t)
  core1 := core1
  core2 := core2

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in frobenius_density.ml order. -/
initialize BFrobeniusDensity01 : HolANT.FrobeniusDensity.FrobeniusDensity01 ←
  ioB "setupFrobeniusDensity01" (HolANT.FrobeniusDensity.setupFrobeniusDensity01 deps).run
initialize BFrobeniusDensity02 : HolANT.FrobeniusDensity.FrobeniusDensity02 ←
  ioB "setupFrobeniusDensity02" (HolANT.FrobeniusDensity.setupFrobeniusDensity02 deps BFrobeniusDensity01).run
initialize BFrobeniusDensity03 : HolANT.FrobeniusDensity.FrobeniusDensity03 ←
  ioB "setupFrobeniusDensity03" (HolANT.FrobeniusDensity.setupFrobeniusDensity03 deps BFrobeniusDensity02).run

-- FrobeniusDensity01
def NUMBER_FIELD_FIXED_FIELD_PRIME_DEGREE_ONE : thm := BFrobeniusDensity01.NUMBER_FIELD_FIXED_FIELD_PRIME_DEGREE_ONE
def NUMBER_FIELD_FIXED_FIELD_DEGREE_ONE_CARD : thm := BFrobeniusDensity01.NUMBER_FIELD_FIXED_FIELD_DEGREE_ONE_CARD
def NUMBER_FIELD_DEGREE_ONE_CARD : thm := BFrobeniusDensity01.NUMBER_FIELD_DEGREE_ONE_CARD

-- FrobeniusDensity02
def NUMBER_FIELD_FIXED_FIELD_FROBENIUS_LOG : thm := BFrobeniusDensity02.NUMBER_FIELD_FIXED_FIELD_FROBENIUS_LOG
def DIRICHLET_SERIES_DIVISOR_INDUCTION : thm := BFrobeniusDensity02.DIRICHLET_SERIES_DIVISOR_INDUCTION
def DIRICHLET_SERIES_CYCLIC_CONJUGATES : thm := BFrobeniusDensity02.DIRICHLET_SERIES_CYCLIC_CONJUGATES
def NUMBER_FIELD_NONPRIME_NORM_SERIES : thm := BFrobeniusDensity02.NUMBER_FIELD_NONPRIME_NORM_SERIES

-- FrobeniusDensity03
def NUMBER_FIELD_NONPRIME_NORM_LOG : thm := BFrobeniusDensity03.NUMBER_FIELD_NONPRIME_NORM_LOG
def NUMBER_FIELD_FROBENIUS_DENSITY_LOG : thm := BFrobeniusDensity03.NUMBER_FIELD_FROBENIUS_DENSITY_LOG
def NUMBER_FIELD_FROBENIUS_DENSITY : thm := BFrobeniusDensity03.NUMBER_FIELD_FROBENIUS_DENSITY
def NUMBER_FIELD_FROBENIUS_INFINITE : thm := BFrobeniusDensity03.NUMBER_FIELD_FROBENIUS_INFINITE
def NUMBER_FIELD_TOTALLY_SPLIT_DENSITY : thm := BFrobeniusDensity03.NUMBER_FIELD_TOTALLY_SPLIT_DENSITY

/-- `needs "ANT/frobenius_density.ml"`: already done by importing this module. -/
def ensureFrobeniusDensity : IO Unit := pure ()

end SessionANT.FrobeniusDensity
