/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/quadratic_ideals.ml                           . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/QuadraticIdeals.lean

  The session half of the quadratic_ideals.ml translation: it supplies HolANT.QuadraticIdeals's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/quadratic_ideals.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.QuadraticIdeals
import SessionLibrary.Integer
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
import SessionANT.IdealArith
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
import SessionANT.NormIndex
import SessionANT.Discriminant
import SessionANT.Quadratic
import SessionANT.PrimeSplit
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.Classgroup
import SessionANT.TraceForm
import SessionANT.RelativeSplit
import SessionLibrary.RingGroups
import SessionLibrary.FiniteFields
import SessionANT.Decomposition
import SessionANT.NfValuation
import SessionANT.RelativeDegree
import SessionANT.FiniteFieldTrace
import SessionANT.Ramification
import SessionANT.SplittingTypes
import SessionANT.NfDecomposition
import SessionANT.ConjugateIdeals

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.QuadraticIdeals

/-- The core theorems quadratic_ideals.ml uses. -/
def core1 : HolANT.QuadraticIdeals.CoreThms1 where
  ALGEBRA_TRACE_NORM_GALOIS := SessionLibrary.Galois.«ALGEBRA_TRACE_NORM_GALOIS»
  ARITH_EQ := Session.ARITH_EQ
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARD_SUBSET_EQ := Session.CARD_SUBSET_EQ
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  EMPTY_SUBSET := Session.EMPTY_SUBSET
  EQ_TRANS := Session.EQ_TRANS
  EXTENSION := Session.EXTENSION
  FIELD_EXTENSION_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_EXTENSION_SUBFIELD_GENERATED»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_GALOIS_GROUP := SessionLibrary.Galois.«FINITE_GALOIS_GROUP»
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_SING := Session.FINITE_SING
  FORALL_UNWIND_THM2 := Session.FORALL_UNWIND_THM2
  GALOIS_EXTENSION_EQ_CARD := SessionLibrary.Galois.«GALOIS_EXTENSION_EQ_CARD»
  GALOIS_GROUP_EQ_ON_GENERATORS := SessionLibrary.Galois.«GALOIS_GROUP_EQ_ON_GENERATORS»
  GALOIS_GROUP_FIXES := SessionLibrary.Galois.«GALOIS_GROUP_FIXES»
  GALOIS_GROUP_I := SessionLibrary.Galois.«GALOIS_GROUP_I»
  GALOIS_GROUP_IMAGE_IDEAL_GENERATED := SessionANT.NfDecomposition.«GALOIS_GROUP_IMAGE_IDEAL_GENERATED»
  GALOIS_GROUP_IN_CARRIER := SessionLibrary.Galois.«GALOIS_GROUP_IN_CARRIER»
  GALOIS_GROUP_RING_HOMOMORPHISM := SessionLibrary.Galois.«GALOIS_GROUP_RING_HOMOMORPHISM»
  GALOIS_GROUP_RING_OF_INTEGERS_IDEAL := SessionANT.NfDecomposition.«GALOIS_GROUP_RING_OF_INTEGERS_IDEAL»
  HAS_SIZE := Session.HAS_SIZE
  IDEAL_GENERATED_PAIR_EQ := SessionLibrary.RingTheory.«IDEAL_GENERATED_PAIR_EQ»
  IDEAL_PRODUCT_INSERT := SessionANT.IdealArith.«IDEAL_PRODUCT_INSERT»
  IDEAL_PRODUCT_SING := SessionANT.IdealArith.«IDEAL_PRODUCT_SING»
  IMAGE_CLAUSES := Session.IMAGE_CLAUSES
  IMAGE_I := Session.IMAGE_I
  INSERT_SUBSET := Session.INSERT_SUBSET
  INTEGRAL_DOMAIN_MUL_LCANCEL := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_LCANCEL»
  INTEGRAL_ELEMENT_QUADRATIC := SessionANT.Quadratic.«INTEGRAL_ELEMENT_QUADRATIC»
  INT_MUL_DIV_EQ := Session.INT_MUL_DIV_EQ
  INT_MUL_SYM := Session.INT_MUL_SYM
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_INSERT := Session.IN_INSERT
  IN_RING_IDEAL_NEG := SessionLibrary.RingTheory.«IN_RING_IDEAL_NEG»
  IN_SING := Session.IN_SING
  I_THM := Session.I_THM
  KUMMER_EXTENSION_ABELIAN := SessionLibrary.Galois.«KUMMER_EXTENSION_ABELIAN»
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NUMBER_FIELD_GALOIS_PRODUCT_IDEAL := SessionANT.ConjugateIdeals.«NUMBER_FIELD_GALOIS_PRODUCT_IDEAL»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_RING_OF_NUM_EQ_0 := SessionANT.Numfield.«NUMBER_FIELD_RING_OF_NUM_EQ_0»
  PRIME_SUBFIELD_MINIMAL := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_MINIMAL»
  QUADRATIC_FIELD_COORDINATES := SessionANT.Quadratic.«QUADRATIC_FIELD_COORDINATES»
  QUADRATIC_FIELD_INTEGER_SQUARE := SessionANT.Quadratic.«QUADRATIC_FIELD_INTEGER_SQUARE»
  QUADRATIC_FIELD_TRACE := SessionANT.Quadratic.«QUADRATIC_FIELD_TRACE»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_1_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_1_IN_SUBFIELD_GENERATED»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_ADD_LZERO := SessionLibrary.RingTheory.«RING_ADD_LZERO»
  RING_ADD_RNEG := SessionLibrary.RingTheory.«RING_ADD_RNEG»
  RING_CARRIER_SUBFIELD_GENERATED_SUBSET := SessionLibrary.FieldTheory.«RING_CARRIER_SUBFIELD_GENERATED_SUBSET»
  RING_HOMOMORPHISM_1 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_1»
  RING_HOMOMORPHISM_ADD := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_ADD»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_POW := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POW»
  RING_HOMOMORPHISM_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_INT»
  RING_HOMOMORPHISM_RING_OF_NUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_NUM»
  RING_HOMOMORPHISM_SUB := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUB»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_SYM := SessionLibrary.RingTheory.«RING_MUL_SYM»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  RING_NEG_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_NEG_IN_SUBFIELD_GENERATED»
  RING_NEG_NEG := SessionLibrary.RingTheory.«RING_NEG_NEG»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_CARRIER := SessionANT.Numfield.«RING_OF_INTEGERS_CARRIER»
  RING_OF_INT_0 := SessionLibrary.RingTheory.«RING_OF_INT_0»
  RING_OF_INT_1 := SessionLibrary.RingTheory.«RING_OF_INT_1»
  RING_OF_INT_ADD := SessionLibrary.RingTheory.«RING_OF_INT_ADD»
  RING_OF_INT_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_INT_IN_SUBFIELD_GENERATED»
  RING_OF_INT_MUL := SessionLibrary.RingTheory.«RING_OF_INT_MUL»
  RING_OF_INT_NEG := SessionLibrary.RingTheory.«RING_OF_INT_NEG»
  RING_OF_INT_OF_NUM := SessionLibrary.RingTheory.«RING_OF_INT_OF_NUM»
  RING_OF_INT_POW := SessionLibrary.RingTheory.«RING_OF_INT_POW»
  RING_OF_INT_SUB := SessionLibrary.RingTheory.«RING_OF_INT_SUB»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_POW_SUBFIELD_GENERATED»
  RING_PRODUCT_CLAUSES := SessionLibrary.RingTheory.«RING_PRODUCT_CLAUSES»
  RING_PRODUCT_SING := SessionLibrary.RingTheory.«RING_PRODUCT_SING»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUM_CLAUSES := SessionLibrary.RingTheory.«RING_SUM_CLAUSES»
  RING_SUM_SING := SessionLibrary.RingTheory.«RING_SUM_SING»
  SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED»
  SUBFIELD_GENERATED_HALF_SUCC := SessionANT.Quadratic.«SUBFIELD_GENERATED_HALF_SUCC»
  SUBFIELD_GENERATED_INC := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_INC»
  SUBFIELD_GENERATED_MONO := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_MONO»
  SUBFIELD_GENERATED_SUPERSET := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_SUPERSET»
  SUBFIELD_SUBFIELD_GENERATED_EQ := SessionLibrary.FieldTheory.«SUBFIELD_SUBFIELD_GENERATED_EQ»
  SUBSET := Session.SUBSET

/-- What quadratic_ideals.ml uses from Session. -/
def deps : HolANT.QuadraticIdeals.QuadraticIdealsDeps where
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

/- The bundles, in quadratic_ideals.ml order. -/
initialize BQuadraticIdeals : HolANT.QuadraticIdeals.QuadraticIdeals ←
  ioB "setupQuadraticIdeals" (HolANT.QuadraticIdeals.setupQuadraticIdeals deps).run

-- QuadraticIdeals
def QUADRATIC_FIELD_SUBFIELD_GENERATED : thm := BQuadraticIdeals.QUADRATIC_FIELD_SUBFIELD_GENERATED
def QUADRATIC_FIELD_GALOIS_EXTENSION : thm := BQuadraticIdeals.QUADRATIC_FIELD_GALOIS_EXTENSION
def QUADRATIC_FIELD_GALOIS_GROUP : thm := BQuadraticIdeals.QUADRATIC_FIELD_GALOIS_GROUP
def QUADRATIC_FIELD_CONJUGATION_EXISTS : thm := BQuadraticIdeals.QUADRATIC_FIELD_CONJUGATION_EXISTS
def QUADRATIC_FIELD_NORM_TRACE_CONJUGATE : thm := BQuadraticIdeals.QUADRATIC_FIELD_NORM_TRACE_CONJUGATE
def QUADRATIC_FIELD_NORM : thm := BQuadraticIdeals.QUADRATIC_FIELD_NORM
def QUADRATIC_FIELD_NORM_TRACE_SQRT : thm := BQuadraticIdeals.QUADRATIC_FIELD_NORM_TRACE_SQRT
def QUADRATIC_FIELD_NORM_TRACE_HALF : thm := BQuadraticIdeals.QUADRATIC_FIELD_NORM_TRACE_HALF
def QUADRATIC_FIELD_NORM_TRACE_INTEGRAL_BASIS : thm := BQuadraticIdeals.QUADRATIC_FIELD_NORM_TRACE_INTEGRAL_BASIS
def QUADRATIC_FIELD_IDEAL_MUL_CONJUGATE : thm := BQuadraticIdeals.QUADRATIC_FIELD_IDEAL_MUL_CONJUGATE
def QUADRATIC_FIELD_CONJUGATE_PRIME_PAIR : thm := BQuadraticIdeals.QUADRATIC_FIELD_CONJUGATE_PRIME_PAIR

/-- `needs "ANT/quadratic_ideals.ml"`: already done by importing this module. -/
def ensureQuadraticIdeals : IO Unit := pure ()

end SessionANT.QuadraticIdeals
