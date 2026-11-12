/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/complex_conjugation.ml                        . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/ComplexConjugation.lean

  The session half of the complex_conjugation.ml translation: it supplies HolANT.ComplexConjugation's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/complex_conjugation.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.ComplexConjugation
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
import SessionLibrary.Isum
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.IdealArith
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionANT.RingOfIntegers
import SessionANT.NormIndex
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.Classgroup
import SessionANT.NfValuation
import SessionANT.PrimeSplit
import SessionANT.Discriminant
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

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.ComplexConjugation

/-- The core theorems complex_conjugation.ml uses. -/
def core1 : HolANT.ComplexConjugation.CoreThms1 where
  ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING := SessionMultiLib.ComplexField.«ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING»
  ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD := SessionLibrary.FieldTheory.«ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD»
  ALGEBRAICALLY_CLOSED_FIELD_NTH_ROOT := SessionLibrary.FieldTheory.«ALGEBRAICALLY_CLOSED_FIELD_NTH_ROOT»
  ALGEBRAICALLY_CLOSED_IMP_NORMAL_EXTENSION := SessionLibrary.FieldTheory.«ALGEBRAICALLY_CLOSED_IMP_NORMAL_EXTENSION»
  ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM := SessionLibrary.FieldTheory.«ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM»
  ARITH_EQ := Session.ARITH_EQ
  ARTIN_FIXED_FIELD := SessionLibrary.Galois.«ARTIN_FIXED_FIELD»
  CARD_CLAUSES := Session.CARD_CLAUSES
  CNJ_ADD := SessionMultiLib.ComplexAlgebra.«CNJ_ADD»
  CNJ_CNJ := SessionMultiLib.ComplexAlgebra.«CNJ_CNJ»
  CNJ_CX := SessionMultiLib.ComplexAlgebra.«CNJ_CX»
  CNJ_MUL := SessionMultiLib.ComplexAlgebra.«CNJ_MUL»
  CNJ_NEG := SessionMultiLib.ComplexAlgebra.«CNJ_NEG»
  COMPLEX_RING_CLAUSES := SessionMultiLib.ComplexRing.«COMPLEX_RING_CLAUSES»
  COMPLEX_RING_POW := SessionMultiLib.ComplexRing.«COMPLEX_RING_POW»
  CX_INJ := SessionMultiLib.ComplexAlgebra.«CX_INJ»
  CX_NEG := SessionMultiLib.ComplexAlgebra.«CX_NEG»
  CX_POW := SessionMultiLib.ComplexAlgebra.«CX_POW»
  EXTENSION := Session.EXTENSION
  FIELD_COMPLEX_RING := SessionMultiLib.ComplexRing.«FIELD_COMPLEX_RING»
  FIELD_HOMOMORPHISM_IMP_MONOMORPHISM := SessionLibrary.RingTheory.«FIELD_HOMOMORPHISM_IMP_MONOMORPHISM»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_INSERT := Session.FINITE_INSERT
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  FUN_EQ_THM := Session.FUN_EQ_THM
  GALOIS_GROUP := SessionLibrary.Galois.«GALOIS_GROUP»
  GALOIS_GROUP_PERMUTES := SessionLibrary.Galois.«GALOIS_GROUP_PERMUTES»
  GALOIS_GROUP_RING_AUTOMORPHISM := SessionLibrary.Galois.«GALOIS_GROUP_RING_AUTOMORPHISM»
  GALOIS_GROUP_RING_HOMOMORPHISM := SessionLibrary.Galois.«GALOIS_GROUP_RING_HOMOMORPHISM»
  GROUP_ELEMENT_ORDER_EQ_2 := SessionLibrary.GroupTheory.«GROUP_ELEMENT_ORDER_EQ_2»
  GROUP_POW_2 := SessionLibrary.GroupTheory.«GROUP_POW_2»
  INVERSE_I := SessionLibrary.Permutations.«INVERSE_I»
  INVERSE_UNIQUE_o := SessionLibrary.Permutations.«INVERSE_UNIQUE_o»
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_FIXED_FIELD := SessionLibrary.Galois.«IN_FIXED_FIELD»
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  I_O_ID := Session.I_O_ID
  I_THM := Session.I_THM
  MONO_EXISTS := Session.MONO_EXISTS
  NORMAL_EXTENSION_IMAGES_EQ := SessionLibrary.FieldTheory.«NORMAL_EXTENSION_IMAGES_EQ»
  NORMAL_IMP_FIELD_EXTENSION := SessionLibrary.FieldTheory.«NORMAL_IMP_FIELD_EXTENSION»
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  PERMUTES_I := SessionLibrary.Permutations.«PERMUTES_I»
  PERMUTES_INVOLUTION := SessionLibrary.Permutations.«PERMUTES_INVOLUTION»
  PERMUTES_IN_IMAGE := SessionLibrary.Permutations.«PERMUTES_IN_IMAGE»
  PRIME_SUBFIELD_HOMOMORPHISM_EXISTS := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_HOMOMORPHISM_EXISTS»
  PRIME_SUBFIELD_MINIMAL := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_MINIMAL»
  REAL_CNJ := SessionMultiLib.ComplexAlgebra.«REAL_CNJ»
  REAL_EXISTS := SessionMultiLib.ComplexAlgebra.«REAL_EXISTS»
  REAL_LE_SQUARE := Session.REAL_LE_SQUARE
  REAL_POW_2 := Session.REAL_POW_2
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_AUTOMORPHISM_I := SessionLibrary.RingTheory.«RING_AUTOMORPHISM_I»
  RING_CARRIER_SUBFIELD_GENERATED_SUBSET := SessionLibrary.FieldTheory.«RING_CARRIER_SUBFIELD_GENERATED_SUBSET»
  RING_CHAR_COMPLEX_RING := SessionMultiLib.ComplexRing.«RING_CHAR_COMPLEX_RING»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_1 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_1»
  RING_HOMOMORPHISM_ADD := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_ADD»
  RING_HOMOMORPHISM_CNJ := SessionMultiLib.ComplexRing.«RING_HOMOMORPHISM_CNJ»
  RING_HOMOMORPHISM_COMPOSE := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_COMPOSE»
  RING_HOMOMORPHISM_I := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_I»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_NEG := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_NEG»
  RING_HOMOMORPHISM_POW := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POW»
  RING_MONOMORPHISM_INJECTIVE_EQ := SessionLibrary.RingTheory.«RING_MONOMORPHISM_INJECTIVE_EQ»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  SUBFIELD_OF_FIXED_FIELD := SessionLibrary.Galois.«SUBFIELD_OF_FIXED_FIELD»
  SUBFIELD_OF_HOMOMORPHIC_EQUALITIES := SessionLibrary.FieldTheory.«SUBFIELD_OF_HOMOMORPHIC_EQUALITIES»
  SUBSET := Session.SUBSET
  SYMMETRIC_GROUP := SessionLibrary.SymmetricGroup.«SYMMETRIC_GROUP»
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  o_THM := Session.o_THM
  permutes := SessionLibrary.Permutations.«permutes»
  ring_automorphism := SessionLibrary.RingTheory.«ring_automorphism»
  ring_endomorphism := SessionLibrary.RingTheory.«ring_endomorphism»
  ring_homomorphism := SessionLibrary.RingTheory.«ring_homomorphism»
  ring_isomorphism := SessionLibrary.RingTheory.«ring_isomorphism»
  ring_isomorphisms := SessionLibrary.RingTheory.«ring_isomorphisms»
  subgroup_of := SessionLibrary.GroupTheory.«subgroup_of»

/-- What complex_conjugation.ml uses from Session. -/
def deps : HolANT.ComplexConjugation.ComplexConjugationDeps where
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
  SELECT_CONV t := pure (Session.SELECT_CONV t)
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in complex_conjugation.ml order. -/
initialize BComplexConjugation : HolANT.ComplexConjugation.ComplexConjugation ←
  ioB "setupComplexConjugation" (HolANT.ComplexConjugation.setupComplexConjugation deps).run

-- ComplexConjugation
def GALOIS_GROUP_COMPLEX_CONJUGATION : thm := BComplexConjugation.GALOIS_GROUP_COMPLEX_CONJUGATION
def COMPLEX_CONJUGATION_REAL_SUBFIELD : thm := BComplexConjugation.COMPLEX_CONJUGATION_REAL_SUBFIELD
def ALGEBRAIC_CLOSURE_COMPLEX_CONJUGATION : thm := BComplexConjugation.ALGEBRAIC_CLOSURE_COMPLEX_CONJUGATION

/-- `needs "ANT/complex_conjugation.ml"`: already done by importing this module. -/
def ensureComplexConjugation : IO Unit := pure ()

end SessionANT.ComplexConjugation
