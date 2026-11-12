/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/roots_of_unity.ml                             . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/RootsOfUnity.lean

  The session half of the roots_of_unity.ml translation: it supplies HolANT.RootsOfUnity's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/roots_of_unity.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.RootsOfUnity
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
import SessionLibrary.Isum
import SessionLibrary.Products
import SessionANT.Algmisc
import SessionANT.Integral
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
import SessionLibrary.SymmetricGroup
import SessionLibrary.Galois
import SessionLibrary.RingGroups
import SessionLibrary.FiniteFields
import SessionLibrary.Integer
import SessionLibrary.Multiplicative
import SessionLibrary.Primitive
import SessionANT.CyclotomicPoly
import SessionANT.IdealArith
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionANT.RingOfIntegers
import SessionANT.PrimeSplit
import SessionANT.NormIndex
import SessionANT.Discriminant
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.Classgroup
import SessionANT.TraceForm
import SessionANT.RelativeSplit
import SessionANT.RelativeDegree
import SessionANT.NfValuation
import SessionANT.Integrality
import SessionANT.DedekindKummer
import SessionANT.PowerBasis
import SessionANT.CyclotomicField
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
import SessionANT.InfinitePlaces
import SessionANT.LinearForms
import SessionANT.ClassgroupGroup
import SessionANT.FiniteFieldTrace
import SessionANT.Ramification
import SessionANT.Quadratic
import SessionANT.MinkowskiTheory
import SessionANT.UnitTheorem

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.RootsOfUnity

/-- The core theorems roots_of_unity.ml uses. -/
def core1 : HolANT.RootsOfUnity.CoreThms1 where
  ARITH_EQ := Session.ARITH_EQ
  COMPLEX_EMBEDDINGS_MONOMORPHISM := SessionANT.ComplexEmbeddings.«COMPLEX_EMBEDDINGS_MONOMORPHISM»
  COMPLEX_EMBEDDINGS_ROOT_OF_UNITY := SessionANT.ComplexEmbeddings.«COMPLEX_EMBEDDINGS_ROOT_OF_UNITY»
  COMPLEX_NORM_CX := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_CX»
  COMPLEX_RING_CLAUSES := SessionMultiLib.ComplexRing.«COMPLEX_RING_CLAUSES»
  CONG_IMP_EQ := SessionLibrary.Pocklington.«CONG_IMP_EQ»
  CONG_REFL := SessionLibrary.Pocklington.«CONG_REFL»
  CONG_RMOD := Session.CONG_RMOD
  COPRIME_2 := SessionLibrary.Prime.«COPRIME_2»
  COPRIME_DIVPROD := SessionLibrary.Prime.«COPRIME_DIVPROD»
  CX_NEG := SessionMultiLib.ComplexAlgebra.«CX_NEG»
  CYCLOTOMIC_POLY_DEG := SessionANT.CyclotomicPoly.«CYCLOTOMIC_POLY_DEG»
  CYCLOTOMIC_POLY_MINIMAL_POLYNOMIAL := SessionANT.CyclotomicField.«CYCLOTOMIC_POLY_MINIMAL_POLYNOMIAL»
  DIVIDES_ZERO := SessionLibrary.Prime.«DIVIDES_ZERO»
  EXTENSION := Session.EXTENSION
  FIELD_NONTRIVIAL := SessionLibrary.RingTheory.«FIELD_NONTRIVIAL»
  FIELD_REGULAR := SessionLibrary.RingTheory.«FIELD_REGULAR»
  HAS_SIZE_IMAGE_INJ := Session.HAS_SIZE_IMAGE_INJ
  HAS_SIZE_NUMSEG_LT := Session.HAS_SIZE_NUMSEG_LT
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  LE_1 := Session.LE_1
  LE_REFL := Session.LE_REFL
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MINIMAL_POLYNOMIAL_DEG_DIVIDES_EXTENSION_DEGREE := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_DEG_DIVIDES_EXTENSION_DEGREE»
  MOD_LT_EQ := Session.MOD_LT_EQ
  MULT_SYM := Session.MULT_SYM
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NOT_ODD := Session.NOT_ODD
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_RING_OF_NUM_EQ_0 := SessionANT.Numfield.«NUMBER_FIELD_RING_OF_NUM_EQ_0»
  NUMBER_FIELD_ROOTS_OF_UNITY_CYCLIC := SessionANT.UnitTheorem.«NUMBER_FIELD_ROOTS_OF_UNITY_CYCLIC»
  NUMBER_FIELD_UNITS_ROOTS_OF_UNITY := SessionANT.UnitTheorem.«NUMBER_FIELD_UNITS_ROOTS_OF_UNITY»
  REAL_EXISTS := SessionMultiLib.ComplexAlgebra.«REAL_EXISTS»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD_LNEG := SessionLibrary.RingTheory.«RING_ADD_LNEG»
  RING_HOMOMORPHISM_1 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_1»
  RING_HOMOMORPHISM_NEG := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_NEG»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_LNEG := SessionLibrary.RingTheory.«RING_MUL_LNEG»
  RING_MUL_RNEG := SessionLibrary.RingTheory.«RING_MUL_RNEG»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  RING_NEG_NEG := SessionLibrary.RingTheory.«RING_NEG_NEG»
  RING_OF_INTEGERS_ROOT_OF_UNITY_UNIT := SessionANT.Numfield.«RING_OF_INTEGERS_ROOT_OF_UNITY_UNIT»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_NUM_1 := SessionLibrary.RingTheory.«RING_OF_NUM_1»
  RING_OF_NUM_ADD := SessionLibrary.RingTheory.«RING_OF_NUM_ADD»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_1 := SessionLibrary.RingTheory.«RING_POW_1»
  RING_POW_2 := SessionLibrary.RingTheory.«RING_POW_2»
  RING_POW_EQ := SessionLibrary.RingTheory.«RING_POW_EQ»
  RING_POW_EQ_1 := SessionLibrary.RingTheory.«RING_POW_EQ_1»
  RING_POW_MUL := SessionLibrary.RingTheory.«RING_POW_MUL»
  RING_POW_ONE := SessionLibrary.RingTheory.«RING_POW_ONE»
  RING_POW_RING_ORDER := SessionLibrary.RingTheory.«RING_POW_RING_ORDER»
  RING_POW_ZERO := SessionLibrary.RingTheory.«RING_POW_ZERO»
  RING_UNIT_IN_CARRIER := SessionLibrary.RingTheory.«RING_UNIT_IN_CARRIER»
  SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED»
  SUBSET := Session.SUBSET
  number_field := SessionANT.Numfield.«number_field»
  real_embeddings := SessionANT.InfinitePlaces.«real_embeddings»
  ring_monomorphism := SessionLibrary.RingTheory.«ring_monomorphism»

/-- What roots_of_unity.ml uses from Session. -/
def deps : HolANT.RootsOfUnity.RootsOfUnityDeps where
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

/- The bundles, in roots_of_unity.ml order. -/
initialize BRootsOfUnity : HolANT.RootsOfUnity.RootsOfUnity ←
  ioB "setupRootsOfUnity" (HolANT.RootsOfUnity.setupRootsOfUnity deps).run

-- RootsOfUnity
def NUMBER_FIELD_ROOT_OF_UNITY_PHI_DIVIDES : thm := BRootsOfUnity.NUMBER_FIELD_ROOT_OF_UNITY_PHI_DIVIDES
def NUMBER_FIELD_ROOTS_OF_UNITY_CARD : thm := BRootsOfUnity.NUMBER_FIELD_ROOTS_OF_UNITY_CARD
def NUMBER_FIELD_REAL_ROOTS_OF_UNITY : thm := BRootsOfUnity.NUMBER_FIELD_REAL_ROOTS_OF_UNITY
def NUMBER_FIELD_UNITS_EQ_ROOTS_OF_UNITY : thm := BRootsOfUnity.NUMBER_FIELD_UNITS_EQ_ROOTS_OF_UNITY

/-- `needs "ANT/roots_of_unity.ml"`: already done by importing this module. -/
def ensureRootsOfUnity : IO Unit := pure ()

end SessionANT.RootsOfUnity
