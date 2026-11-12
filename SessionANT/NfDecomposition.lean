/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/nf_decomposition.ml                           . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/NfDecomposition.lean

  The session half of the nf_decomposition.ml translation: it supplies HolANT.NfDecomposition's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/nf_decomposition.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.NfDecomposition
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

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.NfDecomposition

/-- The core theorems nf_decomposition.ml uses. -/
def core1 : HolANT.NfDecomposition.CoreThms1 where
  BIJECTIONS_CARD_EQ := Session.BIJECTIONS_CARD_EQ
  CARD_DECOMPOSITION_GROUP := SessionANT.Decomposition.«CARD_DECOMPOSITION_GROUP»
  CARD_EQ_0 := Session.CARD_EQ_0
  CARD_IMAGE_INJ := Session.CARD_IMAGE_INJ
  CARD_SING := Session.CARD_SING
  CARD_SUBSET_EQ := Session.CARD_SUBSET_EQ
  CARRIER_SUBFIELD_GENERATED_SUBFIELD := SessionLibrary.FieldTheory.«CARRIER_SUBFIELD_GENERATED_SUBFIELD»
  DECOMPOSITION_GROUP := SessionANT.Decomposition.«DECOMPOSITION_GROUP»
  DECOMPOSITION_GROUP_IMAGE_RING_COSET := SessionANT.Decomposition.«DECOMPOSITION_GROUP_IMAGE_RING_COSET»
  DECOMPOSITION_GROUP_INDEX := SessionANT.Decomposition.«DECOMPOSITION_GROUP_INDEX»
  DECOMPOSITION_GROUP_RESIDUE_EPIMORPHISM := SessionANT.Decomposition.«DECOMPOSITION_GROUP_RESIDUE_EPIMORPHISM»
  DECOMPOSITION_GROUP_RESIDUE_HOMOMORPHISM := SessionANT.Decomposition.«DECOMPOSITION_GROUP_RESIDUE_HOMOMORPHISM»
  DEDEKIND_IDEAL_INDUCT := SessionANT.Dedekind.«DEDEKIND_IDEAL_INDUCT»
  DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL := SessionANT.Dedekind.«DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL»
  DEDEKIND_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«DEDEKIND_RING_OF_INTEGERS»
  DEDEKIND_VALUATION := SessionANT.DedekindValuation.«DEDEKIND_VALUATION»
  EQ_MULT_LCANCEL := Session.EQ_MULT_LCANCEL
  EQ_MULT_RCANCEL := Session.EQ_MULT_RCANCEL
  EQ_TRANS := Session.EQ_TRANS
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXTENSION := Session.EXTENSION
  EXTENSION_DEGREE_RESIDUE_CONJUGATE := SessionANT.Decomposition.«EXTENSION_DEGREE_RESIDUE_CONJUGATE»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«FIELD_IMP_NONTRIVIAL_RING»
  FIELD_QUOTIENT_RING := SessionLibrary.RingTheory.«FIELD_QUOTIENT_RING»
  FIELD_RING_HOMOMORPHISM_MONOMORPHISM := SessionLibrary.RingTheory.«FIELD_RING_HOMOMORPHISM_MONOMORPHISM»
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FINITE_GALOIS_GROUP := SessionLibrary.Galois.«FINITE_GALOIS_GROUP»
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_INTEGRAL_DOMAIN_IMP_FIELD := SessionLibrary.RingTheory.«FINITE_INTEGRAL_DOMAIN_IMP_FIELD»
  FINITE_QUOTIENT_RING_HOMOMORPHIC_PREIMAGE := SessionANT.RelativeSplit.«FINITE_QUOTIENT_RING_HOMOMORPHIC_PREIMAGE»
  FINITE_RESTRICT := Session.FINITE_RESTRICT
  FINITE_SUBRING_GENERATED := SessionLibrary.RingTheory.«FINITE_SUBRING_GENERATED»
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FROBENIUS_ELEMENT := SessionANT.Decomposition.«FROBENIUS_ELEMENT»
  FROBENIUS_ELEMENT_CONJUGATE := SessionANT.Decomposition.«FROBENIUS_ELEMENT_CONJUGATE»
  FUN_EQ_THM := Session.FUN_EQ_THM
  GALOIS_EXTENSION_SUBFIELD_GENERATED := SessionLibrary.Galois.«GALOIS_EXTENSION_SUBFIELD_GENERATED»
  GALOIS_GROUP := SessionLibrary.Galois.«GALOIS_GROUP»
  GALOIS_GROUP_COMPOSE := SessionLibrary.Galois.«GALOIS_GROUP_COMPOSE»
  GALOIS_GROUP_FINITE_FIELD := SessionLibrary.Galois.«GALOIS_GROUP_FINITE_FIELD»
  GALOIS_GROUP_FIXED_FIELD := SessionLibrary.Galois.«GALOIS_GROUP_FIXED_FIELD»
  GALOIS_GROUP_FIXES := SessionLibrary.Galois.«GALOIS_GROUP_FIXES»
  GALOIS_GROUP_INVERSE := SessionLibrary.Galois.«GALOIS_GROUP_INVERSE»
  GALOIS_GROUP_PERMUTES := SessionLibrary.Galois.«GALOIS_GROUP_PERMUTES»
  GALOIS_GROUP_PRIME_IDEAL_IMAGE := SessionANT.Decomposition.«GALOIS_GROUP_PRIME_IDEAL_IMAGE»
  GALOIS_GROUP_RING_AUTOMORPHISM := SessionLibrary.Galois.«GALOIS_GROUP_RING_AUTOMORPHISM»
  GALOIS_GROUP_RING_HOMOMORPHISM := SessionLibrary.Galois.«GALOIS_GROUP_RING_HOMOMORPHISM»
  GALOIS_GROUP_SUBRING_IMAGE := SessionANT.Decomposition.«GALOIS_GROUP_SUBRING_IMAGE»
  GALOIS_GROUP_TRANSITIVE_PRIME_IDEALS := SessionANT.Decomposition.«GALOIS_GROUP_TRANSITIVE_PRIME_IDEALS»
  GALOIS_IMP_FIELD_EXTENSION := SessionLibrary.Galois.«GALOIS_IMP_FIELD_EXTENSION»
  GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET := SessionLibrary.GroupTheory.«GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET»
  GROUP_ELEMENT_ORDER_MONOMORPHIC_IMAGE := SessionLibrary.GroupTheory.«GROUP_ELEMENT_ORDER_MONOMORPHIC_IMAGE»
  GROUP_ELEMENT_ORDER_SUBGROUP_GENERATED := SessionLibrary.GroupTheory.«GROUP_ELEMENT_ORDER_SUBGROUP_GENERATED»
  GROUP_ID := SessionLibrary.GroupTheory.«GROUP_ID»
  GROUP_INV := SessionLibrary.GroupTheory.«GROUP_INV»
  GROUP_MONOMORPHISM := SessionLibrary.GroupTheory.«GROUP_MONOMORPHISM»
  IDEAL_GENERATED_BY_EPIMORPHIC_IMAGE := SessionLibrary.RingTheory.«IDEAL_GENERATED_BY_EPIMORPHIC_IMAGE»
  IDEAL_GENERATED_IMAGE_IDEAL_GENERATED := SessionANT.IdealArith.«IDEAL_GENERATED_IMAGE_IDEAL_GENERATED»
  IDEAL_GENERATED_INC_GEN := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC_GEN»
  IDEAL_GENERATED_RING_IDEAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_RING_IDEAL»
  IDEAL_PROD_EPIMORPHIC_IMAGE := SessionANT.IdealArith.«IDEAL_PROD_EPIMORPHIC_IMAGE»
  IDEAL_VALUATION_HOMOMORPHIC_IMAGE := SessionANT.RelativeSplit.«IDEAL_VALUATION_HOMOMORPHIC_IMAGE»
  IDEAL_VALUATION_PRIME := SessionANT.Dedekind.«IDEAL_VALUATION_PRIME»
  IMAGE_CLAUSES := Session.IMAGE_CLAUSES
  IMAGE_EQ := Session.IMAGE_EQ
  IMAGE_I := Session.IMAGE_I
  IMAGE_o := Session.IMAGE_o
  IMP_CONJ := Session.IMP_CONJ
  INERTIA_GROUP := SessionANT.Decomposition.«INERTIA_GROUP»
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  INTEGRAL_DOMAIN_SUBRING_GENERATED := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_SUBRING_GENERATED»
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_SING := Session.IN_SING
  I_DEF := Session.I_DEF
  I_O_ID := Session.I_O_ID
  I_THM := Session.I_THM
  MAXIMAL_IMP_PRIME_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_PRIME_IDEAL»
/-- The core theorems nf_decomposition.ml uses. -/
def core2 : HolANT.NfDecomposition.CoreThms2 where
  MAXIMAL_IMP_RING_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_RING_IDEAL»
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MONO_EXISTS := Session.MONO_EXISTS
  MULT_CLAUSES := Session.MULT_CLAUSES
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NSUM_CONST := Session.NSUM_CONST
  NSUM_EQ := Session.NSUM_EQ
  NUMBER_FIELD_FUNDAMENTAL_IDENTITY := SessionANT.RelativeDegree.«NUMBER_FIELD_FUNDAMENTAL_IDENTITY»
  NUMBER_FIELD_HOMOMORPHIC_PREIMAGE := SessionANT.RelativeSplit.«NUMBER_FIELD_HOMOMORPHIC_PREIMAGE»
  NUMBER_FIELD_IDEAL_NORM_MUL_Q := SessionANT.NormIndex.«NUMBER_FIELD_IDEAL_NORM_MUL_Q»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_PRIME_IDEAL_ABOVE := SessionANT.RelativeSplit.«NUMBER_FIELD_PRIME_IDEAL_ABOVE»
  NUMBER_FIELD_TOWER_LAW := SessionANT.RelativeSplit.«NUMBER_FIELD_TOWER_LAW»
  PERMUTES_INVERSE := SessionLibrary.Permutations.«PERMUTES_INVERSE»
  PERMUTES_INVERSES := SessionLibrary.Permutations.«PERMUTES_INVERSES»
  PERMUTES_IN_IMAGE := SessionLibrary.Permutations.«PERMUTES_IN_IMAGE»
  PRIME_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«PRIME_IDEAL_IMP_SUBSET»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  QUOTIENT_RING_CARRIER := SessionLibrary.RingTheory.«QUOTIENT_RING_CARRIER»
  RAMIFICATION_INDEX_TOWER := SessionANT.RelativeSplit.«RAMIFICATION_INDEX_TOWER»
  RESIDUE_DEGREE_QUOTIENT_RING := SessionANT.RelativeSplit.«RESIDUE_DEGREE_QUOTIENT_RING»
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_CARRIER_SUBRING_GENERATED_SUBSET := SessionLibrary.RingTheory.«RING_CARRIER_SUBRING_GENERATED_SUBSET»
  RING_COSET_EQ := SessionLibrary.RingTheory.«RING_COSET_EQ»
  RING_EPIMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_EPIMORPHISM_IMP_HOMOMORPHISM»
  RING_EPIMORPHISM_RING_COSET := SessionLibrary.RingTheory.«RING_EPIMORPHISM_RING_COSET»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_POW := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POW»
  RING_HOMOMORPHISM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_HOMOMORPHISM_RING_OF_INTEGERS»
  RING_HOMOMORPHISM_SUBFIELD_INCLUSION := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_SUBFIELD_INCLUSION»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_ISOMORPHISM_IMP_EPIMORPHISM := SessionLibrary.RingTheory.«RING_ISOMORPHISM_IMP_EPIMORPHISM»
  RING_ISOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_ISOMORPHISM_IMP_HOMOMORPHISM»
  RING_ISOMORPHISM_IMP_MONOMORPHISM := SessionLibrary.RingTheory.«RING_ISOMORPHISM_IMP_MONOMORPHISM»
  RING_MONOMORPHISM_EQ_0 := SessionLibrary.RingTheory.«RING_MONOMORPHISM_EQ_0»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MONOMORPHISM_INCLUSION := SessionLibrary.RingTheory.«RING_MONOMORPHISM_INCLUSION»
  RING_MONOMORPHISM_INTO_SUBRING := SessionLibrary.RingTheory.«RING_MONOMORPHISM_INTO_SUBRING»
  RING_MONOMORPHISM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_MONOMORPHISM_RING_OF_INTEGERS»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_FINITE_QUOTIENT := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FINITE_QUOTIENT»
  RING_OF_INTEGERS_FRACTION_FIELD := SessionANT.NfValuation.«RING_OF_INTEGERS_FRACTION_FIELD»
  RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE_EQ := SessionANT.RelativeSplit.«RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE_EQ»
  RING_OF_INTEGERS_PRIME_IDEAL_BELOW := SessionANT.RelativeSplit.«RING_OF_INTEGERS_PRIME_IDEAL_BELOW»
  RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION := SessionANT.RelativeSplit.«RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION»
  RING_OF_INTEGERS_SUBRING := SessionANT.Numfield.«RING_OF_INTEGERS_SUBRING»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_POW_SUBRING_GENERATED»
  RING_SUB_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_SUB_SUBRING_GENERATED»
  SING_SUBSET := Session.SING_SUBSET
  SUBFIELD_OF_IMP_SUBSET := SessionLibrary.FieldTheory.«SUBFIELD_OF_IMP_SUBSET»
  SUBGROUP_GENERATED_ELEMENT_ORDER := SessionLibrary.GroupTheory.«SUBGROUP_GENERATED_ELEMENT_ORDER»
  SUBGROUP_GENERATED_IDEMPOT_GEN := SessionLibrary.GroupTheory.«SUBGROUP_GENERATED_IDEMPOT_GEN»
  SUBGROUP_GENERATED_INC := SessionLibrary.GroupTheory.«SUBGROUP_GENERATED_INC»
  SUBGROUP_GENERATED_MINIMAL := SessionLibrary.GroupTheory.«SUBGROUP_GENERATED_MINIMAL»
  SUBGROUP_SUBGROUP_GENERATED := SessionLibrary.GroupTheory.«SUBGROUP_SUBGROUP_GENERATED»
  SUBRING_GENERATED_BY_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBRING_GENERATED_BY_SUBFIELD_GENERATED»
  SUBRING_GENERATED_QUOTIENT_RING_IMAGE := SessionANT.Decomposition.«SUBRING_GENERATED_QUOTIENT_RING_IMAGE»
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUBSET_REFL := Session.SUBSET_REFL
  UNRAMIFIED_IMP_WEAKLY_UNRAMIFIED := SessionANT.SplittingTypes.«UNRAMIFIED_IMP_WEAKLY_UNRAMIFIED»
  decomposition_group := SessionANT.Decomposition.«decomposition_group»
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  field_of_fractions := SessionLibrary.RingTheory.«field_of_fractions»
  finite_extension := SessionLibrary.FieldTheory.«finite_extension»
  group_conjugation := SessionLibrary.GroupTheory.«group_conjugation»
  group_epimorphism := SessionLibrary.GroupTheory.«group_epimorphism»
  ideal_norm := SessionANT.IdealNorm.«ideal_norm»
  inertia_group := SessionANT.Decomposition.«inertia_group»
  o_ASSOC := Session.o_ASSOC
  o_THM := Session.o_THM
  ramification_index := SessionANT.PrimeSplit.«ramification_index»
  residue_degree := SessionANT.PrimeSplit.«residue_degree»
  ring_automorphism := SessionLibrary.RingTheory.«ring_automorphism»
  ring_homomorphism := SessionLibrary.RingTheory.«ring_homomorphism»
  ring_monomorphism := SessionLibrary.RingTheory.«ring_monomorphism»
  subgroup_of := SessionLibrary.GroupTheory.«subgroup_of»
  weakly_unramified := SessionANT.SplittingTypes.«weakly_unramified»

/-- What nf_decomposition.ml uses from Session. -/
def deps : HolANT.NfDecomposition.NfDecompositionDeps where
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

/- The bundles, in nf_decomposition.ml order. -/
initialize BNfDecomposition01 : HolANT.NfDecomposition.NfDecomposition01 ←
  ioB "setupNfDecomposition01" (HolANT.NfDecomposition.setupNfDecomposition01 deps).run
initialize BNfDecomposition02 : HolANT.NfDecomposition.NfDecomposition02 ←
  ioB "setupNfDecomposition02" (HolANT.NfDecomposition.setupNfDecomposition02 deps BNfDecomposition01).run
initialize BNfDecomposition03 : HolANT.NfDecomposition.NfDecomposition03 ←
  ioB "setupNfDecomposition03" (HolANT.NfDecomposition.setupNfDecomposition03 deps BNfDecomposition01 BNfDecomposition02).run

-- NfDecomposition01
def GALOIS_GROUP_RING_OF_INTEGERS : thm := BNfDecomposition01.GALOIS_GROUP_RING_OF_INTEGERS
def DECOMPOSITION_GROUP_RING_OF_INTEGERS : thm := BNfDecomposition01.DECOMPOSITION_GROUP_RING_OF_INTEGERS
def GALOIS_GROUP_RING_OF_INTEGERS_AUTOMORPHISM : thm := BNfDecomposition01.GALOIS_GROUP_RING_OF_INTEGERS_AUTOMORPHISM
def GALOIS_GROUP_RING_OF_INTEGERS_IDEAL : thm := BNfDecomposition01.GALOIS_GROUP_RING_OF_INTEGERS_IDEAL
def GALOIS_GROUP_IMAGE_IDEAL_GENERATED : thm := BNfDecomposition01.GALOIS_GROUP_IMAGE_IDEAL_GENERATED
def NUMBER_FIELD_GALOIS_GROUP_TRANSITIVE : thm := BNfDecomposition01.NUMBER_FIELD_GALOIS_GROUP_TRANSITIVE
def CARD_GALOIS_GROUP_IMAGE_FIBER : thm := BNfDecomposition01.CARD_GALOIS_GROUP_IMAGE_FIBER
def IDEAL_NORM_RESIDUE_IMAGE : thm := BNfDecomposition01.IDEAL_NORM_RESIDUE_IMAGE
def NUMBER_FIELD_RAMIFICATION_INDEX_CONJUGATE : thm := BNfDecomposition01.NUMBER_FIELD_RAMIFICATION_INDEX_CONJUGATE
def NUMBER_FIELD_IDEAL_NORM_CONJUGATE : thm := BNfDecomposition01.NUMBER_FIELD_IDEAL_NORM_CONJUGATE
def NUMBER_FIELD_IDEAL_NORM_GALOIS_IMAGE : thm := BNfDecomposition01.NUMBER_FIELD_IDEAL_NORM_GALOIS_IMAGE
def NUMBER_FIELD_DECOMPOSITION_GROUP : thm := BNfDecomposition01.NUMBER_FIELD_DECOMPOSITION_GROUP

-- NfDecomposition02
def NUMBER_FIELD_INERTIA_FIELD : thm := BNfDecomposition02.NUMBER_FIELD_INERTIA_FIELD
def NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP : thm := BNfDecomposition02.NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP
def NUMBER_FIELD_DEDEKIND_VALUATION_CONJUGATE : thm := BNfDecomposition02.NUMBER_FIELD_DEDEKIND_VALUATION_CONJUGATE
def NUMBER_FIELD_FROBENIUS_ELEMENT : thm := BNfDecomposition02.NUMBER_FIELD_FROBENIUS_ELEMENT
def DECOMPOSITION_GROUP_FROBENIUS_GENERATED : thm := BNfDecomposition02.DECOMPOSITION_GROUP_FROBENIUS_GENERATED
def NUMBER_FIELD_DECOMPOSITION_GROUP_FROBENIUS : thm := BNfDecomposition02.NUMBER_FIELD_DECOMPOSITION_GROUP_FROBENIUS

-- NfDecomposition03
def NUMBER_FIELD_FROBENIUS_CONJUGATE_PRIME : thm := BNfDecomposition03.NUMBER_FIELD_FROBENIUS_CONJUGATE_PRIME

/-- `needs "ANT/nf_decomposition.ml"`: already done by importing this module. -/
def ensureNfDecomposition : IO Unit := pure ()

end SessionANT.NfDecomposition
