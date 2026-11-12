/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/ramification_groups.ml                        . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/RamificationGroups.lean

  The session half of the ramification_groups.ml translation: it supplies HolANT.RamificationGroups's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/ramification_groups.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.RamificationGroups
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
import SessionANT.Hensel
import SessionANT.IdealEuler

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.RamificationGroups

/-- The core theorems ramification_groups.ml uses. -/
def core1 : HolANT.RamificationGroups.CoreThms1 where
  ADD1 := Session.ADD1
  ADD_CLAUSES := Session.ADD_CLAUSES
  ADD_EQ_0 := Session.ADD_EQ_0
  ADD_SYM := Session.ADD_SYM
  ARITH := Session.ARITH
  ARITH_EQ := Session.ARITH_EQ
  CARD_DELETE := Session.CARD_DELETE
  CARD_EQ_0 := Session.CARD_EQ_0
  CARD_EQ_CARD_IMP := SessionLibrary.Card.«CARD_EQ_CARD_IMP»
  CARD_SING := Session.CARD_SING
  CARRIER_SUBGROUP_GENERATED_SUBGROUP := SessionLibrary.GroupTheory.«CARRIER_SUBGROUP_GENERATED_SUBGROUP»
  DECOMPOSITION_GROUP := SessionANT.Decomposition.«DECOMPOSITION_GROUP»
  DEDEKIND_IDEAL_POW_MUL_CANCEL := SessionANT.Dedekind.«DEDEKIND_IDEAL_POW_MUL_CANCEL»
  DEDEKIND_IDEAL_POW_UNIFORMIZER_SPLIT := SessionANT.Dedekind.«DEDEKIND_IDEAL_POW_UNIFORMIZER_SPLIT»
  DEDEKIND_IN_IDEAL_POW_VALUATION := SessionANT.Dedekind.«DEDEKIND_IN_IDEAL_POW_VALUATION»
  DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL := SessionANT.Dedekind.«DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL»
  DEDEKIND_PRIME_IDEAL_LOCAL_GENERATOR := SessionANT.Dedekind.«DEDEKIND_PRIME_IDEAL_LOCAL_GENERATOR»
  DEDEKIND_PRIME_IDEAL_UNIFORMIZER := SessionANT.Dedekind.«DEDEKIND_PRIME_IDEAL_UNIFORMIZER»
  DEDEKIND_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«DEDEKIND_RING_OF_INTEGERS»
  DIVIDES_ONE := Session.DIVIDES_ONE
  DIVIDES_PRIMEPOW := SessionLibrary.Prime.«DIVIDES_PRIMEPOW»
  DIVIDES_REFL := SessionLibrary.Prime.«DIVIDES_REFL»
  EQ_MULT_RCANCEL := Session.EQ_MULT_RCANCEL
  EQ_TRANS := Session.EQ_TRANS
  EXP := Session.EXP
  EXP_EQ_0 := Session.EXP_EQ_0
  EXTENSION := Session.EXTENSION
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_QUOTIENT_RING := SessionLibrary.RingTheory.«FIELD_QUOTIENT_RING»
  FIELD_UNIT_GROUP := SessionLibrary.RingGroups.«FIELD_UNIT_GROUP»
  FINITE_DIFF := Session.FINITE_DIFF
  FINITE_FIELD_CYCLIC_UNIT_GROUP := SessionLibrary.FiniteFields.«FINITE_FIELD_CYCLIC_UNIT_GROUP»
  FINITE_GALOIS_GROUP := SessionLibrary.Galois.«FINITE_GALOIS_GROUP»
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_IMP_FIELD_EXTENSION := SessionLibrary.FieldTheory.«FINITE_IMP_FIELD_EXTENSION»
  FINITE_INTEGRAL_DOMAIN_CHAR := SessionLibrary.RingTheory.«FINITE_INTEGRAL_DOMAIN_CHAR»
  FINITE_PGROUP_SING := SessionLibrary.GroupTheory.«FINITE_PGROUP_SING»
  FINITE_SUBSET := Session.FINITE_SUBSET
  FIRST_GROUP_ISOMORPHISM_THEOREM := SessionLibrary.GroupTheory.«FIRST_GROUP_ISOMORPHISM_THEOREM»
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FUN_EQ_THM := Session.FUN_EQ_THM
  FUN_IN_IMAGE := Session.FUN_IN_IMAGE
  GALOIS_GROUP := SessionLibrary.Galois.«GALOIS_GROUP»
  GALOIS_GROUP_PERMUTES := SessionLibrary.Galois.«GALOIS_GROUP_PERMUTES»
  GALOIS_GROUP_PRIME_IDEAL_IMAGE := SessionANT.Decomposition.«GALOIS_GROUP_PRIME_IDEAL_IMAGE»
  GALOIS_GROUP_RING_HOMOMORPHISM := SessionLibrary.Galois.«GALOIS_GROUP_RING_HOMOMORPHISM»
  GALOIS_GROUP_RING_OF_INTEGERS := SessionANT.NfDecomposition.«GALOIS_GROUP_RING_OF_INTEGERS»
  GALOIS_GROUP_SUBRING_IMAGE := SessionANT.Decomposition.«GALOIS_GROUP_SUBRING_IMAGE»
  GALOIS_IMP_FIELD_EXTENSION := SessionLibrary.Galois.«GALOIS_IMP_FIELD_EXTENSION»
  GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET := SessionLibrary.GroupTheory.«GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET»
  GROUP_HOMOMORPHISM := SessionLibrary.GroupTheory.«GROUP_HOMOMORPHISM»
  GROUP_ID := SessionLibrary.GroupTheory.«GROUP_ID»
  GROUP_INV := SessionLibrary.GroupTheory.«GROUP_INV»
  GROUP_MUL := SessionLibrary.GroupTheory.«GROUP_MUL»
  GROUP_MUL_RINV := SessionLibrary.GroupTheory.«GROUP_MUL_RINV»
  GROUP_POW_1 := SessionLibrary.GroupTheory.«GROUP_POW_1»
  GROUP_POW_EQ_ID := SessionLibrary.GroupTheory.«GROUP_POW_EQ_ID»
  GROUP_POW_MUL := SessionLibrary.GroupTheory.«GROUP_POW_MUL»
  GROUP_POW_SUBGROUP_GENERATED := SessionLibrary.GroupTheory.«GROUP_POW_SUBGROUP_GENERATED»
  IDEAL_POW_0 := SessionANT.IdealArith.«IDEAL_POW_0»
  IDEAL_POW_1 := SessionANT.IdealArith.«IDEAL_POW_1»
  IDEAL_POW_ANTIMONO := SessionANT.IdealArith.«IDEAL_POW_ANTIMONO»
  IDEAL_POW_SUBSET_PRIME_IDEAL := SessionANT.IdealArith.«IDEAL_POW_SUBSET_PRIME_IDEAL»
  INERTIA_GROUP := SessionANT.Decomposition.«INERTIA_GROUP»
  INERTIA_GROUP_NORMAL_SUBGROUP := SessionANT.Decomposition.«INERTIA_GROUP_NORMAL_SUBGROUP»
  INTEGRAL_DOMAIN_CHAR := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_CHAR»
  INTEGRAL_DOMAIN_MUL_LCANCEL := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_LCANCEL»
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_RING_IDEAL_ADD := SessionLibrary.RingTheory.«IN_RING_IDEAL_ADD»
  IN_RING_IDEAL_LMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_LMUL»
  IN_RING_IDEAL_RMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_RMUL»
  IN_RING_IDEAL_SUB := SessionLibrary.RingTheory.«IN_RING_IDEAL_SUB»
  IN_SING := Session.IN_SING
  ISOMORPHIC_GROUP_CARD_EQ := SessionLibrary.GroupTheory.«ISOMORPHIC_GROUP_CARD_EQ»
  ISOMORPHIC_GROUP_CYCLICITY := SessionLibrary.GroupTheory.«ISOMORPHIC_GROUP_CYCLICITY»
  I_THM := Session.I_THM
  LAGRANGE_THEOREM := SessionLibrary.GroupTheory.«LAGRANGE_THEOREM»
  LAGRANGE_THEOREM_RIGHT := SessionLibrary.GroupTheory.«LAGRANGE_THEOREM_RIGHT»
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_0 := Session.LE_0
  LE_ADD_RCANCEL := Session.LE_ADD_RCANCEL
  LE_TRANS := Session.LE_TRANS
  MAXIMAL_IDEAL_FINITE_QUOTIENT_POW_CARD := SessionANT.IdealEuler.«MAXIMAL_IDEAL_FINITE_QUOTIENT_POW_CARD»
  MONO_EXISTS := Session.MONO_EXISTS
  MULT_AC := Session.MULT_AC
/-- The core theorems ramification_groups.ml uses. -/
def core2 : HolANT.RamificationGroups.CoreThms2 where
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_SYM := Session.MULT_SYM
  NORMAL_PGROUP_SUBSET_COPRIME_INDEX := SessionLibrary.GroupTheory.«NORMAL_PGROUP_SUBSET_COPRIME_INDEX»
  NORMAL_SUBGROUP_GROUP_KERNEL := SessionLibrary.GroupTheory.«NORMAL_SUBGROUP_GROUP_KERNEL»
  NORMAL_SUBGROUP_IMP_SUBGROUP := SessionLibrary.GroupTheory.«NORMAL_SUBGROUP_IMP_SUBGROUP»
  NOT_SUC := Session.NOT_SUC
  NUMBER_FIELD_DECOMPOSITION_GROUP := SessionANT.NfDecomposition.«NUMBER_FIELD_DECOMPOSITION_GROUP»
  NUMBER_FIELD_PRIME_IDEAL_ABOVE := SessionANT.RelativeSplit.«NUMBER_FIELD_PRIME_IDEAL_ABOVE»
  NUMBER_FIELD_TOWER_LAW := SessionANT.RelativeSplit.«NUMBER_FIELD_TOWER_LAW»
  PERMUTES_IN_IMAGE := SessionLibrary.Permutations.«PERMUTES_IN_IMAGE»
  PGROUP_SING := SessionLibrary.GroupTheory.«PGROUP_SING»
  PRIME_GE_2 := SessionLibrary.Prime.«PRIME_GE_2»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  QUOTIENT_GROUP := SessionLibrary.GroupTheory.«QUOTIENT_GROUP»
  QUOTIENT_RING := SessionLibrary.RingTheory.«QUOTIENT_RING»
  QUOTIENT_RING_0 := SessionLibrary.RingTheory.«QUOTIENT_RING_0»
  QUOTIENT_RING_1 := SessionLibrary.RingTheory.«QUOTIENT_RING_1»
  QUOTIENT_RING_ADD := SessionLibrary.RingTheory.«QUOTIENT_RING_ADD»
  QUOTIENT_RING_CARRIER := SessionLibrary.RingTheory.«QUOTIENT_RING_CARRIER»
  QUOTIENT_RING_MUL := SessionLibrary.RingTheory.«QUOTIENT_RING_MUL»
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RIGHT_IMP_EXISTS_THM := Session.RIGHT_IMP_EXISTS_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_ADDITIVE_GROUP := SessionLibrary.RingGroups.«RING_ADDITIVE_GROUP»
  RING_CARRIER_NONEMPTY := SessionLibrary.RingTheory.«RING_CARRIER_NONEMPTY»
  RING_CARRIER_SUBRING_GENERATED_SUBSET := SessionLibrary.RingTheory.«RING_CARRIER_SUBRING_GENERATED_SUBSET»
  RING_CHAR_DIVIDES_ORDER := SessionLibrary.RingTheory.«RING_CHAR_DIVIDES_ORDER»
  RING_CHAR_FINITE := SessionLibrary.RingTheory.«RING_CHAR_FINITE»
  RING_COSET_0 := SessionLibrary.RingTheory.«RING_COSET_0»
  RING_COSET_EQ := SessionLibrary.RingTheory.«RING_COSET_EQ»
  RING_COSET_EQ_IDEAL := SessionLibrary.RingTheory.«RING_COSET_EQ_IDEAL»
  RING_HOMOMORPHISM_1 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_1»
  RING_HOMOMORPHISM_ADD := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_ADD»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_RING_COSET := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_COSET»
  RING_HOMOMORPHISM_RING_OF_NUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_NUM»
  RING_HOMOMORPHISM_SUB := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUB»
  RING_IDEAL_ADD_IN_EQ := SessionLibrary.RingTheory.«RING_IDEAL_ADD_IN_EQ»
  RING_IDEAL_IDEAL_POW := SessionANT.IdealArith.«RING_IDEAL_IDEAL_POW»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_ISOMORPHISM_IDEAL_POW := SessionANT.IdealArith.«RING_ISOMORPHISM_IDEAL_POW»
  RING_ISOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_ISOMORPHISM_IMP_HOMOMORPHISM»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_IN_IDEAL_POW := SessionANT.IdealArith.«RING_MUL_IN_IDEAL_POW»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_OF_INTEGERS_FRACTION_FIELD := SessionANT.NfValuation.«RING_OF_INTEGERS_FRACTION_FIELD»
  RING_OF_INTEGERS_SUBRING := SessionANT.Numfield.«RING_OF_INTEGERS_SUBRING»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_OF_NUM_0 := SessionLibrary.RingTheory.«RING_OF_NUM_0»
  RING_OF_NUM_EQ_0 := SessionLibrary.RingTheory.«RING_OF_NUM_EQ_0»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_EQ_0 := SessionLibrary.RingTheory.«RING_SUB_EQ_0»
  RING_SUB_REFL := SessionLibrary.RingTheory.«RING_SUB_REFL»
  RING_SUB_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_SUB_SUBRING_GENERATED»
  SKOLEM_THM := Session.SKOLEM_THM
  SUBGROUP_GROUP_IMAGE := SessionLibrary.GroupTheory.«SUBGROUP_GROUP_IMAGE»
  SUBGROUP_OF_CYCLIC_GROUP := SessionLibrary.GroupTheory.«SUBGROUP_OF_CYCLIC_GROUP»
  SUBGROUP_OF_IMP_SUBSET := SessionLibrary.GroupTheory.«SUBGROUP_OF_IMP_SUBSET»
  SUBGROUP_OF_SUBGROUP_GENERATED_SUBGROUP_EQ := SessionLibrary.GroupTheory.«SUBGROUP_OF_SUBGROUP_GENERATED_SUBGROUP_EQ»
  SUBRING_GENERATED := SessionLibrary.RingTheory.«SUBRING_GENERATED»
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUC_SUB1 := Session.SUC_SUB1
  TRIVIAL_SUBGROUP_OF := SessionLibrary.GroupTheory.«TRIVIAL_SUBGROUP_OF»
  UNIT_GROUP := SessionLibrary.RingGroups.«UNIT_GROUP»
  decomposition_group := SessionANT.Decomposition.«decomposition_group»
  divides := Session.divides
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  field_of_fractions := SessionLibrary.RingTheory.«field_of_fractions»
  group_kernel := SessionLibrary.GroupTheory.«group_kernel»
  group_pow := SessionLibrary.GroupTheory.«group_pow»
  inertia_group := SessionANT.Decomposition.«inertia_group»
  num_FINITE := Session.num_FINITE
  o_THM := Session.o_THM
  permutes := SessionLibrary.Permutations.«permutes»
  ring_homomorphism := SessionLibrary.RingTheory.«ring_homomorphism»
  ring_of_num := SessionLibrary.RingTheory.«ring_of_num»
  ring_pow := SessionLibrary.RingTheory.«ring_pow»
  ring_unit := SessionLibrary.RingTheory.«ring_unit»
  subgroup_of := SessionLibrary.GroupTheory.«subgroup_of»

/-- What ramification_groups.ml uses from Session. -/
def deps : HolANT.RamificationGroups.RamificationGroupsDeps where
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
  NUMBER_TAC := Session.NUMBER_TAC
  core1 := core1
  core2 := core2

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in ramification_groups.ml order. -/
initialize BRamificationGroups01 : HolANT.RamificationGroups.RamificationGroups01 ←
  ioB "setupRamificationGroups01" (HolANT.RamificationGroups.setupRamificationGroups01 deps).run
initialize BRamificationGroups02 : HolANT.RamificationGroups.RamificationGroups02 ←
  ioB "setupRamificationGroups02" (HolANT.RamificationGroups.setupRamificationGroups02 deps BRamificationGroups01).run
initialize BRamificationGroups03 : HolANT.RamificationGroups.RamificationGroups03 ←
  ioB "setupRamificationGroups03" (HolANT.RamificationGroups.setupRamificationGroups03 deps BRamificationGroups01 BRamificationGroups02).run

-- RamificationGroups01
def RING_HOMOMORPHISM_POW_DIFFERENCE : thm := BRamificationGroups01.RING_HOMOMORPHISM_POW_DIFFERENCE
def DEDEKIND_UNIFORMIZER_CONGRUENCE_STEP : thm := BRamificationGroups01.DEDEKIND_UNIFORMIZER_CONGRUENCE_STEP
def DEDEKIND_UNIFORMIZER_CONGRUENCE : thm := BRamificationGroups01.DEDEKIND_UNIFORMIZER_CONGRUENCE
def DECOMPOSITION_GROUP_IDEAL_POW : thm := BRamificationGroups01.DECOMPOSITION_GROUP_IDEAL_POW
def INERTIA_GROUP_IDEAL_POW_0 : thm := BRamificationGroups01.INERTIA_GROUP_IDEAL_POW_0
def INERTIA_GROUP_IDEAL_POW : thm := BRamificationGroups01.INERTIA_GROUP_IDEAL_POW
def INERTIA_GROUP_IDEAL_POW_MONO : thm := BRamificationGroups01.INERTIA_GROUP_IDEAL_POW_MONO
def INERTIA_GROUP_IDEAL_POW_NORMAL : thm := BRamificationGroups01.INERTIA_GROUP_IDEAL_POW_NORMAL
def INERTIA_GROUP_IDEAL_POW_EVENTUALLY_TRIVIAL : thm := BRamificationGroups01.INERTIA_GROUP_IDEAL_POW_EVENTUALLY_TRIVIAL
def INERTIA_GROUP_IDEAL_POW_UNIFORMIZER : thm := BRamificationGroups01.INERTIA_GROUP_IDEAL_POW_UNIFORMIZER
def DEDEKIND_IDEAL_POW_UNIFORMIZER_MUL : thm := BRamificationGroups01.DEDEKIND_IDEAL_POW_UNIFORMIZER_MUL
def DEDEKIND_IDEAL_POW_UNIFORMIZER_UNIQUE : thm := BRamificationGroups01.DEDEKIND_IDEAL_POW_UNIFORMIZER_UNIQUE
def INERTIA_GROUP_IDEAL_POW_AUTOMORPHISM : thm := BRamificationGroups01.INERTIA_GROUP_IDEAL_POW_AUTOMORPHISM
def INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_EXISTS : thm := BRamificationGroups01.INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_EXISTS

-- RamificationGroups02
def INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_MUL : thm := BRamificationGroups02.INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_MUL
def INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_ADD : thm := BRamificationGroups02.INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_ADD
def INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_KERNEL : thm := BRamificationGroups02.INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_KERNEL
def INERTIA_GROUP_TAME_HOMOMORPHISM : thm := BRamificationGroups02.INERTIA_GROUP_TAME_HOMOMORPHISM
def INERTIA_GROUP_TAME_QUOTIENT : thm := BRamificationGroups02.INERTIA_GROUP_TAME_QUOTIENT
def INERTIA_GROUP_WILD_MAP : thm := BRamificationGroups02.INERTIA_GROUP_WILD_MAP
def INERTIA_GROUP_WILD_HOMOMORPHISM : thm := BRamificationGroups02.INERTIA_GROUP_WILD_HOMOMORPHISM

-- RamificationGroups03
def INERTIA_GROUP_IDEAL_POW_CHAR_POW : thm := BRamificationGroups03.INERTIA_GROUP_IDEAL_POW_CHAR_POW
def INERTIA_GROUP_WILD_PGROUP : thm := BRamificationGroups03.INERTIA_GROUP_WILD_PGROUP
def INERTIA_GROUP_WILD_SUBSET : thm := BRamificationGroups03.INERTIA_GROUP_WILD_SUBSET
def INERTIA_GROUP_WILD_TRIVIAL : thm := BRamificationGroups03.INERTIA_GROUP_WILD_TRIVIAL
def NUMBER_FIELD_WILD_INERTIA_TRIVIAL : thm := BRamificationGroups03.NUMBER_FIELD_WILD_INERTIA_TRIVIAL

/-- `needs "ANT/ramification_groups.ml"`: already done by importing this module. -/
def ensureRamificationGroups : IO Unit := pure ()

end SessionANT.RamificationGroups
