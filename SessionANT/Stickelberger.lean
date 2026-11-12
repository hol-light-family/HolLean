/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/stickelberger.ml                              . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/Stickelberger.lean

  The session half of the stickelberger.ml translation: it supplies HolANT.Stickelberger's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/stickelberger.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.Stickelberger
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
import SessionLibrary.Isum
import SessionANT.Integral
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.IdealArith
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionANT.RingOfIntegers
import SessionANT.NormIndex
import SessionANT.Discriminant
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.Classgroup
import SessionANT.NfValuation
import SessionANT.PrimeSplit
import SessionANT.TraceForm
import SessionANT.RelativeSplit
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

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.Stickelberger

/-- The core theorems stickelberger.ml uses. -/
def core1 : HolANT.Stickelberger.CoreThms1 where
  ARITH_EQ := Session.ARITH_EQ
  COMPLEX_EMBEDDINGS_HAS_SIZE := SessionANT.ComplexEmbeddings.«COMPLEX_EMBEDDINGS_HAS_SIZE»
  COMPLEX_EMBEDDINGS_NONEMPTY := SessionANT.ComplexEmbeddings.«COMPLEX_EMBEDDINGS_NONEMPTY»
  COMPLEX_RING_CLAUSES := SessionMultiLib.ComplexRing.«COMPLEX_RING_CLAUSES»
  COMPLEX_RING_OF_INT := SessionMultiLib.ComplexRing.«COMPLEX_RING_OF_INT»
  COMPLEX_RING_POW := SessionMultiLib.ComplexRing.«COMPLEX_RING_POW»
  COMPLEX_RING_PRODUCT := SessionMultiLib.ComplexRing.«COMPLEX_RING_PRODUCT»
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXTENSION := Session.EXTENSION
  FIELD_COMPLEX_RING := SessionMultiLib.ComplexRing.«FIELD_COMPLEX_RING»
  FINITE_COMPLEX_EMBEDDINGS := SessionANT.ComplexEmbeddings.«FINITE_COMPLEX_EMBEDDINGS»
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_IMAGE_INJ_EQ := Session.FINITE_IMAGE_INJ_EQ
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_PERMUTATIONS := SessionLibrary.Permutations.«FINITE_PERMUTATIONS»
  FINITE_SUBSET := Session.FINITE_SUBSET
  FUN_EQ_THM := Session.FUN_EQ_THM
  HAS_SIZE_INDEX := Session.HAS_SIZE_INDEX
  INT_DIVISION_SIMP := Session.INT_DIVISION_SIMP
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_REM_2_CASES := Session.INT_REM_2_CASES
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INTER := Session.IN_INTER
  IN_SUBFIELD_LINV := SessionLibrary.FieldTheory.«IN_SUBFIELD_LINV»
  IN_SUBFIELD_MUL := SessionLibrary.FieldTheory.«IN_SUBFIELD_MUL»
  IN_SUBRING_0 := SessionLibrary.RingTheory.«IN_SUBRING_0»
  IN_SUBRING_1 := SessionLibrary.RingTheory.«IN_SUBRING_1»
  IN_SUBRING_INT := SessionLibrary.RingTheory.«IN_SUBRING_INT»
  IN_SUBRING_MUL := SessionLibrary.RingTheory.«IN_SUBRING_MUL»
  IN_SUBRING_NEG := SessionLibrary.RingTheory.«IN_SUBRING_NEG»
  IN_SUBRING_POW := SessionLibrary.RingTheory.«IN_SUBRING_POW»
  IN_SUBRING_PRODUCT := SessionLibrary.RingTheory.«IN_SUBRING_PRODUCT»
  IN_SUBRING_SUM := SessionLibrary.RingTheory.«IN_SUBRING_SUM»
  IN_UNIV := Session.IN_UNIV
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS := SessionANT.InfinitePlaces.«NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS»
  NUMBER_FIELD_NORM_COMPLEX_EMBEDDINGS := SessionANT.InfinitePlaces.«NUMBER_FIELD_NORM_COMPLEX_EMBEDDINGS»
  NUMBER_FIELD_NORM_INTEGRAL_Q := SessionANT.Numfield.«NUMBER_FIELD_NORM_INTEGRAL_Q»
  PERMUTES_IN_IMAGE := SessionLibrary.Permutations.«PERMUTES_IN_IMAGE»
  PRIME_SUBRING := SessionLibrary.RingTheory.«PRIME_SUBRING»
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD_LZERO := SessionLibrary.RingTheory.«RING_ADD_LZERO»
  RING_ADD_RZERO := SessionLibrary.RingTheory.«RING_ADD_RZERO»
  RING_CHAR_COMPLEX_RING := SessionMultiLib.ComplexRing.«RING_CHAR_COMPLEX_RING»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_INT»
  RING_HOMOMORPHISM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_HOMOMORPHISM_RING_OF_INTEGERS»
  RING_HOMOMORPHISM_SUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUM»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_LNEG := SessionLibrary.RingTheory.«RING_MUL_LNEG»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_OF_INTEGERS_FREE := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FREE»
  RING_OF_INTEGERS_PRIME_SUBFIELD := SessionANT.Numfield.«RING_OF_INTEGERS_PRIME_SUBFIELD»
  RING_OF_INTEGERS_SUBRING := SessionANT.Numfield.«RING_OF_INTEGERS_SUBRING»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INT_CLAUSES := SessionLibrary.RingTheory.«RING_OF_INT_CLAUSES»
  RING_OF_INT_EQ_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_0»
  RING_OF_INT_EQ_CHAR_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_CHAR_0»
  RING_PRODUCT := SessionLibrary.RingTheory.«RING_PRODUCT»
  RING_PRODUCT_EQ := SessionLibrary.RingTheory.«RING_PRODUCT_EQ»
  RING_PRODUCT_IMAGE := SessionLibrary.RingTheory.«RING_PRODUCT_IMAGE»
  RING_SUB_LZERO := SessionLibrary.RingTheory.«RING_SUB_LZERO»
  RING_SUB_RZERO := SessionLibrary.RingTheory.«RING_SUB_RZERO»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_ADD := SessionLibrary.RingTheory.«RING_SUM_ADD»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_PERMUTATIONS_RYSER := SessionLibrary.RingDet.«RING_SUM_PERMUTATIONS_RYSER»
  RING_SUM_SUB := SessionLibrary.RingTheory.«RING_SUM_SUB»
  SUBFIELD_IMP_SUBRING_OF := SessionLibrary.FieldTheory.«SUBFIELD_IMP_SUBRING_OF»
  SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_SUBFIELD_GENERATED»
  SUBSET := Session.SUBSET
  complex_embeddings := SessionANT.ComplexEmbeddings.«complex_embeddings»
  free_basis := SessionLibrary.RingDet.«free_basis»
  int_congruent := Session.int_congruent
  lemma := SessionMultiLib.Integration.«lemma»
  o_DEF := Session.o_DEF
  ring_det := SessionLibrary.RingDet.«ring_det»
  ring_sign := SessionLibrary.RingDet.«ring_sign»

/-- What stickelberger.ml uses from Session. -/
def deps : HolANT.Stickelberger.StickelbergerDeps where
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

/- The bundles, in stickelberger.ml order. -/
initialize BStickelberger : HolANT.Stickelberger.Stickelberger ←
  ioB "setupStickelberger" (HolANT.Stickelberger.setupStickelberger deps).run

-- Stickelberger
def RING_DET_PERMANENT_MOD_4 : thm := BStickelberger.RING_DET_PERMANENT_MOD_4
def NUMBER_FIELD_PERMANENT_INTEGRAL : thm := BStickelberger.NUMBER_FIELD_PERMANENT_INTEGRAL
def NUMBER_FIELD_DISCRIMINANT_MOD_4 : thm := BStickelberger.NUMBER_FIELD_DISCRIMINANT_MOD_4

/-- `needs "ANT/stickelberger.ml"`: already done by importing this module. -/
def ensureStickelberger : IO Unit := pure ()

end SessionANT.Stickelberger
