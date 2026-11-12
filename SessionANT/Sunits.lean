/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/sunits.ml                                     . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/Sunits.lean

  The session half of the sunits.ml translation: it supplies HolANT.Sunits's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/sunits.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.Sunits
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.RingTheory
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
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
import SessionANT.Numfield
import SessionANT.IdealArith
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.IdealNorm
import SessionANT.RingOfIntegers
import SessionANT.NormIndex
import SessionANT.Classgroup
import SessionANT.NfValuation
import SessionLibrary.RingGroups
import SessionANT.FingenGroup
import SessionANT.ClassgroupGroup
import SessionANT.FractionalIdeals
import SessionANT.DedekindCriteria
import SessionANT.SIntegers
import SessionANT.PrimeSplit
import SessionANT.Discriminant
import SessionANT.TraceForm
import SessionANT.RelativeSplit
import SessionANT.Integrality
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

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.Sunits

/-- The core theorems sunits.ml uses. -/
def core1 : HolANT.Sunits.CoreThms1 where
  ABELIAN_GROUP_HOMOMORPHISM_POWERING := SessionLibrary.GroupTheory.«ABELIAN_GROUP_HOMOMORPHISM_POWERING»
  ABELIAN_GROUP_SUM_CLAUSES := SessionLibrary.GroupTheory.«ABELIAN_GROUP_SUM_CLAUSES»
  ABELIAN_GROUP_SUM_MUL := SessionLibrary.GroupTheory.«ABELIAN_GROUP_SUM_MUL»
  ABELIAN_GROUP_SUM_POW := SessionLibrary.GroupTheory.«ABELIAN_GROUP_SUM_POW»
  ABELIAN_INTEGER_GROUP := SessionLibrary.GroupTheory.«ABELIAN_INTEGER_GROUP»
  ABELIAN_PRODUCT_GROUP := SessionLibrary.GroupTheory.«ABELIAN_PRODUCT_GROUP»
  ABELIAN_SUBGROUP_GENERATED := SessionLibrary.GroupTheory.«ABELIAN_SUBGROUP_GENERATED»
  ABELIAN_UNIT_GROUP := SessionLibrary.RingGroups.«ABELIAN_UNIT_GROUP»
  CARRIER_SUBGROUP_GENERATED_SUBGROUP := SessionLibrary.GroupTheory.«CARRIER_SUBGROUP_GENERATED_SUBGROUP»
  CYCLIC_IMP_FINITELY_GENERATED_GROUP := SessionLibrary.GroupTheory.«CYCLIC_IMP_FINITELY_GENERATED_GROUP»
  CYCLIC_INTEGER_GROUP := SessionLibrary.GroupTheory.«CYCLIC_INTEGER_GROUP»
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DIVISION := Session.DIVISION
  EXTENSION := Session.EXTENSION
  FIELD_DIV_EQ_0 := SessionLibrary.RingTheory.«FIELD_DIV_EQ_0»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_INV_EQ_0 := SessionLibrary.RingTheory.«FIELD_INV_EQ_0»
  FIELD_MUL_LINV := SessionLibrary.RingTheory.«FIELD_MUL_LINV»
  FIELD_NONTRIVIAL := SessionLibrary.RingTheory.«FIELD_NONTRIVIAL»
  FIELD_POW_EQ_0 := SessionLibrary.RingTheory.«FIELD_POW_EQ_0»
  FIELD_UNIT := SessionLibrary.RingTheory.«FIELD_UNIT»
  FIELD_UNIT_GROUP := SessionLibrary.RingGroups.«FIELD_UNIT_GROUP»
  FINITELY_GENERATED_ABELIAN_GROUP_MOD_POW := SessionANT.FingenGroup.«FINITELY_GENERATED_ABELIAN_GROUP_MOD_POW»
  FINITELY_GENERATED_ABELIAN_GROUP_POW := SessionLibrary.GroupTheory.«FINITELY_GENERATED_ABELIAN_GROUP_POW»
  FINITELY_GENERATED_ABELIAN_SUBGROUP := SessionLibrary.GroupTheory.«FINITELY_GENERATED_ABELIAN_SUBGROUP»
  FINITELY_GENERATED_GROUP_EXTENSION := SessionANT.FingenGroup.«FINITELY_GENERATED_GROUP_EXTENSION»
  FINITELY_GENERATED_PRODUCT_GROUP := SessionLibrary.GroupTheory.«FINITELY_GENERATED_PRODUCT_GROUP»
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_RESTRICT := Session.FINITE_RESTRICT
  FINITE_SUBSET := Session.FINITE_SUBSET
  FINITE_UNION := Session.FINITE_UNION
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET := SessionLibrary.GroupTheory.«GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET»
  GROUP_HOMOMORPHISM := SessionLibrary.GroupTheory.«GROUP_HOMOMORPHISM»
  GROUP_ISOMORPHISM_IMP_ISOMORPHIC := SessionLibrary.GroupTheory.«GROUP_ISOMORPHISM_IMP_ISOMORPHIC»
  GROUP_KERNEL_SUBSET_CARRIER := SessionLibrary.GroupTheory.«GROUP_KERNEL_SUBSET_CARRIER»
  GROUP_POW := SessionLibrary.GroupTheory.«GROUP_POW»
  GROUP_POW_ADD := SessionLibrary.GroupTheory.«GROUP_POW_ADD»
  GROUP_POW_POW := SessionLibrary.GroupTheory.«GROUP_POW_POW»
  GROUP_POW_SUBGROUP_GENERATED := SessionLibrary.GroupTheory.«GROUP_POW_SUBGROUP_GENERATED»
  GROUP_SUM := SessionLibrary.GroupTheory.«GROUP_SUM»
  GROUP_SUM_CLAUSES_EXISTS := SessionLibrary.GroupTheory.«GROUP_SUM_CLAUSES_EXISTS»
  GROUP_SUM_EQ := SessionLibrary.GroupTheory.«GROUP_SUM_EQ»
  IMP_CONJ := Session.IMP_CONJ
  INTEGER_GROUP := SessionLibrary.GroupTheory.«INTEGER_GROUP»
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  INTEGRAL_DOMAIN_POW_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_POW_EQ_0»
  INT_ADD_LID := Session.INT_ADD_LID
  INT_DIV_ZERO := Session.INT_DIV_ZERO
  INT_MUL_DIV_EQ := Session.INT_MUL_DIV_EQ
  INT_NEG_0 := Session.INT_NEG_0
  INT_SUB_0 := Session.INT_SUB_0
  IN_DIFF := Session.IN_DIFF
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_SING := Session.IN_SING
  IN_UNION := Session.IN_UNION
  IN_UNIV := Session.IN_UNIV
  ISOMORPHIC_GROUP_FINITE_GENERATION := SessionLibrary.GroupTheory.«ISOMORPHIC_GROUP_FINITE_GENERATION»
  I_THM := Session.I_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  MOD_LT_EQ := Session.MOD_LT_EQ
  MONO_EXISTS := Session.MONO_EXISTS
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_UNIT_GROUP_FINITELY_GENERATED := SessionANT.ComplexEmbeddings.«NUMBER_FIELD_UNIT_GROUP_FINITELY_GENERATED»
  NUMBER_FIELD_VALUATION_1 := SessionANT.NfValuation.«NUMBER_FIELD_VALUATION_1»
  NUMBER_FIELD_VALUATION_DIV := SessionANT.NfValuation.«NUMBER_FIELD_VALUATION_DIV»
  NUMBER_FIELD_VALUATION_FINITE := SessionANT.NfValuation.«NUMBER_FIELD_VALUATION_FINITE»
  NUMBER_FIELD_VALUATION_INV := SessionANT.NfValuation.«NUMBER_FIELD_VALUATION_INV»
  NUMBER_FIELD_VALUATION_MUL := SessionANT.NfValuation.«NUMBER_FIELD_VALUATION_MUL»
  NUMBER_FIELD_VALUATION_POW := SessionANT.NfValuation.«NUMBER_FIELD_VALUATION_POW»
  NUMBER_FIELD_VALUATION_PRINCIPAL_OUTSIDE := SessionANT.NfValuation.«NUMBER_FIELD_VALUATION_PRINCIPAL_OUTSIDE»
  NUMBER_FIELD_VALUATION_UNIT := SessionANT.NfValuation.«NUMBER_FIELD_VALUATION_UNIT»
  PRODUCT_GROUP := SessionLibrary.GroupTheory.«PRODUCT_GROUP»
  RESTRICTION := Session.RESTRICTION
  RESTRICTION_EXTENSION := Session.RESTRICTION_EXTENSION
  RESTRICTION_IN_CARTESIAN_PRODUCT := Session.RESTRICTION_IN_CARTESIAN_PRODUCT
  RIGHT_COSET_EQ := SessionLibrary.GroupTheory.«RIGHT_COSET_EQ»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_DIV := SessionLibrary.RingTheory.«RING_DIV»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_ASSOC := SessionLibrary.RingTheory.«RING_MUL_ASSOC»
  RING_MUL_POW := SessionLibrary.RingTheory.«RING_MUL_POW»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_FRACTION_FIELD := SessionANT.NfValuation.«RING_OF_INTEGERS_FRACTION_FIELD»
  RING_OF_INTEGERS_SUBRING := SessionANT.Numfield.«RING_OF_INTEGERS_SUBRING»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_PRODUCT_CLAUSES := SessionLibrary.RingTheory.«RING_PRODUCT_CLAUSES»
  RING_UNIT_IN_CARRIER := SessionLibrary.RingTheory.«RING_UNIT_IN_CARRIER»
  RING_UNIT_RING_OF_S_INTEGERS := SessionANT.SIntegers.«RING_UNIT_RING_OF_S_INTEGERS»
  SUBGROUP_GENERATED := SessionLibrary.GroupTheory.«SUBGROUP_GENERATED»
  SUBGROUP_GENERATED_IDEMPOT_GEN := SessionLibrary.GroupTheory.«SUBGROUP_GENERATED_IDEMPOT_GEN»
  SUBGROUP_GENERATED_MONO := SessionLibrary.GroupTheory.«SUBGROUP_GENERATED_MONO»
  SUBGROUP_GROUP_IMAGE := SessionLibrary.GroupTheory.«SUBGROUP_GROUP_IMAGE»
  SUBSET := Session.SUBSET
  SWAP_FORALL_THM := Session.SWAP_FORALL_THM
  UNIT_GROUP := SessionLibrary.RingGroups.«UNIT_GROUP»
  UNIT_GROUP_POW := SessionLibrary.RingGroups.«UNIT_GROUP_POW»
  UNIT_GROUP_SUBRING_GENERATED := SessionLibrary.RingGroups.«UNIT_GROUP_SUBRING_GENERATED»
  group_div := SessionLibrary.GroupTheory.«group_div»
  group_image := SessionLibrary.GroupTheory.«group_image»
  group_kernel := SessionLibrary.GroupTheory.«group_kernel»
  ring_div := SessionLibrary.RingTheory.«ring_div»
  ring_of_s_integers := SessionANT.SIntegers.«ring_of_s_integers»
  subgroup_of := SessionLibrary.GroupTheory.«subgroup_of»

/-- What sunits.ml uses from Session. -/
def deps : HolANT.Sunits.SunitsDeps where
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

/- The bundles, in sunits.ml order. -/
initialize BSunits : HolANT.Sunits.Sunits ←
  ioB "setupSunits" (HolANT.Sunits.setupSunits deps).run

-- Sunits
def s_unit_group : thm := BSunits.s_unit_group
def S_UNIT_GROUP : thm := BSunits.S_UNIT_GROUP
def S_UNIT_GROUP_POW : thm := BSunits.S_UNIT_GROUP_POW
def ABELIAN_S_UNIT_GROUP : thm := BSunits.ABELIAN_S_UNIT_GROUP
def S_UNIT_GROUP_EMPTY : thm := BSunits.S_UNIT_GROUP_EMPTY
def S_UNIT_GROUP_MONO : thm := BSunits.S_UNIT_GROUP_MONO
def S_UNIT_GROUP_SUM : thm := BSunits.S_UNIT_GROUP_SUM
def FINITELY_GENERATED_S_UNIT_GROUP : thm := BSunits.FINITELY_GENERATED_S_UNIT_GROUP
def S_UNIT_GROUP_GENERATORS : thm := BSunits.S_UNIT_GROUP_GENERATORS
def S_UNIT_GROUP_GENERATORS_MOD_POW : thm := BSunits.S_UNIT_GROUP_GENERATORS_MOD_POW
def NUMBER_FIELD_POW_S_UNIT_DECOMPOSITION : thm := BSunits.NUMBER_FIELD_POW_S_UNIT_DECOMPOSITION
def NUMBER_FIELD_KSM_FINITE : thm := BSunits.NUMBER_FIELD_KSM_FINITE
def NUMBER_FIELD_KSM_QUOTIENT_FINITE : thm := BSunits.NUMBER_FIELD_KSM_QUOTIENT_FINITE
def S_UNIT_GROUP_RING_OF_S_INTEGERS : thm := BSunits.S_UNIT_GROUP_RING_OF_S_INTEGERS
def FINITELY_GENERATED_UNIT_GROUP_RING_OF_S_INTEGERS : thm := BSunits.FINITELY_GENERATED_UNIT_GROUP_RING_OF_S_INTEGERS

/-- `needs "ANT/sunits.ml"`: already done by importing this module. -/
def ensureSunits : IO Unit := pure ()

end SessionANT.Sunits
