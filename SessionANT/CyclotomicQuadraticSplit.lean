/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/cyclotomic_quadratic_split.ml                 . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/CyclotomicQuadraticSplit.lean

  The session half of the cyclotomic_quadratic_split.ml translation: it supplies HolANT.CyclotomicQuadraticSplit's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/cyclotomic_quadratic_split.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.CyclotomicQuadraticSplit
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
import SessionLibrary.Integer
import SessionLibrary.Isum
import SessionLibrary.Products
import SessionLibrary.Multiplicative
import SessionLibrary.Primitive
import SessionLibrary.Jacobi
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
import SessionLibrary.SymmetricGroup
import SessionLibrary.Galois
import SessionANT.IdealArith
import SessionANT.Algmisc
import SessionANT.Integral
import SessionANT.Dedekind
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionANT.RingOfIntegers
import SessionANT.PrimeSplit
import SessionANT.NormIndex
import SessionANT.Discriminant
import SessionANT.TraceForm
import SessionANT.FiniteFieldTrace
import SessionANT.Ramification
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.Classgroup
import SessionANT.RelativeSplit
import SessionANT.RelativeDegree
import SessionANT.SplittingTypes
import SessionANT.Quadratic
import SessionANT.NfValuation
import SessionANT.Integrality
import SessionANT.DedekindKummer
import SessionANT.QuadraticSplit
import SessionLibrary.ModmulGroup
import SessionLibrary.Cyclotomic
import SessionLibrary.RingGroups
import SessionLibrary.FiniteFields
import SessionANT.CyclotomicPoly
import SessionANT.PowerBasis
import SessionANT.CyclotomicField
import SessionANT.CyclotomicGalois
import SessionANT.Decomposition
import SessionANT.NfDecomposition
import SessionANT.DecompositionField
import SessionANT.CyclotomicFrobenius
import SessionANT.CyclotomicSubfieldSplit
import SessionANT.CyclotomicIntegers
import SessionANT.CyclotomicSubfields
import SessionANT.GaussSum

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.CyclotomicQuadraticSplit

/-- The core theorems cyclotomic_quadratic_split.ml uses. -/
def core1 : HolANT.CyclotomicQuadraticSplit.CoreThms1 where
  ARITH_EQ := Session.ARITH_EQ
  CARD_CLAUSES := Session.CARD_CLAUSES
  COPRIME_SYM := SessionLibrary.Prime.«COPRIME_SYM»
  CYCLOTOMIC_FIELD_GALOIS_GROUP_EXISTS := SessionANT.CyclotomicGalois.«CYCLOTOMIC_FIELD_GALOIS_GROUP_EXISTS»
  CYCLOTOMIC_FIELD_QUADRATIC_SUBFIELD := SessionANT.GaussSum.«CYCLOTOMIC_FIELD_QUADRATIC_SUBFIELD»
  CYCLOTOMIC_SUBFIELD_SPLITTING_TYPES := SessionANT.CyclotomicSubfieldSplit.«CYCLOTOMIC_SUBFIELD_SPLITTING_TYPES»
  DEDEKIND_IMP_INTEGRAL_DOMAIN := SessionANT.Dedekind.«DEDEKIND_IMP_INTEGRAL_DOMAIN»
  DEDEKIND_KRULL_DIMENSION_ONE := SessionANT.Dedekind.«DEDEKIND_KRULL_DIMENSION_ONE»
  DEDEKIND_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«DEDEKIND_RING_OF_INTEGERS»
  DIVIDES_PRIME_PRIME := SessionLibrary.Prime.«DIVIDES_PRIME_PRIME»
  DIVIDES_ZERO := SessionLibrary.Prime.«DIVIDES_ZERO»
  EQ_TRANS := Session.EQ_TRANS
  EXTENSION := Session.EXTENSION
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_INSERT := Session.FINITE_INSERT
  FORALL_UNWIND_THM2 := Session.FORALL_UNWIND_THM2
  GALOIS_GROUP := SessionLibrary.Galois.«GALOIS_GROUP»
  IDEAL_GENERATED_EQ_0 := SessionLibrary.RingTheory.«IDEAL_GENERATED_EQ_0»
  IDEAL_GENERATED_MINIMAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL»
  IDEAL_PROD_EQ_ZERO := SessionANT.IdealArith.«IDEAL_PROD_EQ_ZERO»
  IDEAL_PROD_SUBSET_LEFT := SessionANT.IdealArith.«IDEAL_PROD_SUBSET_LEFT»
  IDEAL_PROD_SUBSET_PRIME_IDEAL := SessionANT.IdealArith.«IDEAL_PROD_SUBSET_PRIME_IDEAL»
  IDEAL_PROD_SUBSET_RIGHT := SessionANT.IdealArith.«IDEAL_PROD_SUBSET_RIGHT»
  IMP_CONJ := Session.IMP_CONJ
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  INTEGRAL_DOMAIN_SQUARE_EQ := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_SQUARE_EQ»
  INT_ABS_MUL := Session.INT_ABS_MUL
  INT_ABS_NEG := Session.INT_ABS_NEG
  INT_ABS_NUM := Session.INT_ABS_NUM
  INT_ABS_POW := Session.INT_ABS_POW
  INT_DIVIDES_LNEG := SessionLibrary.Integer.«INT_DIVIDES_LNEG»
  INT_DIVIDES_RNEG := SessionLibrary.Integer.«INT_DIVIDES_RNEG»
  INT_DIVIDES_ZERO := SessionLibrary.Integer.«INT_DIVIDES_ZERO»
  INT_ENTIRE := Session.INT_ENTIRE
  INT_MUL_ASSOC := Session.INT_MUL_ASSOC
  INT_MUL_LID := Session.INT_MUL_LID
  INT_MUL_LNEG := Session.INT_MUL_LNEG
  INT_NEG_EQ_0 := Session.INT_NEG_EQ_0
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_POW := Session.INT_POW
  INT_POW_EQ_0 := Session.INT_POW_EQ_0
  INT_POW_ONE := Session.INT_POW_ONE
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IDEAL_GENERATED_SELF := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SELF»
  IN_INSERT := Session.IN_INSERT
  IN_SING := Session.IN_SING
  JACOBI_PRIME := SessionLibrary.Jacobi.«JACOBI_PRIME»
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_SPLITTING_TYPES_EXCLUSIVE := SessionANT.SplittingTypes.«NUMBER_FIELD_SPLITTING_TYPES_EXCLUSIVE»
  NUMBER_FIELD_SUBFIELD_GENERATED := SessionANT.RelativeSplit.«NUMBER_FIELD_SUBFIELD_GENERATED»
  NUMBER_FIELD_TOTALLY_SPLIT_CARD := SessionANT.SplittingTypes.«NUMBER_FIELD_TOTALLY_SPLIT_CARD»
  NUM_OF_INT_OF_NUM := Session.NUM_OF_INT_OF_NUM
  PRIME_1 := SessionLibrary.Prime.«PRIME_1»
  PRIME_COPRIME_EQ := SessionLibrary.Prime.«PRIME_COPRIME_EQ»
  PRIME_IMP_NZ := SessionLibrary.Prime.«PRIME_IMP_NZ»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PRIME_IMP_SQUAREFREE := SessionLibrary.Pocklington.«PRIME_IMP_SQUAREFREE»
  PRIME_SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_SUBFIELD_GENERATED»
  QUADRATIC_FIELD_ODD_PRIME := SessionANT.QuadraticSplit.«QUADRATIC_FIELD_ODD_PRIME»
  QUADRATIC_GAUSS_SUM := SessionANT.GaussSum.«QUADRATIC_GAUSS_SUM»
  QUADRATIC_GAUSS_SUM_HOMOMORPHISM := SessionANT.GaussSum.«QUADRATIC_GAUSS_SUM_HOMOMORPHISM»
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_HOMOMORPHISM_NEG := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_NEG»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_ISOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_ISOMORPHISM_IMP_HOMOMORPHISM»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_LNEG := SessionLibrary.RingTheory.«RING_MUL_LNEG»
  RING_MUL_RNEG := SessionLibrary.RingTheory.«RING_MUL_RNEG»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INT_1 := SessionLibrary.RingTheory.«RING_OF_INT_1»
  RING_OF_INT_EQ_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_0»
  RING_OF_INT_NEG := SessionLibrary.RingTheory.«RING_OF_INT_NEG»
  RING_OF_INT_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_INT_SUBFIELD_GENERATED»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_OF_NUM_EQ_0 := SessionLibrary.RingTheory.«RING_OF_NUM_EQ_0»
  RING_POW_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_POW_SUBFIELD_GENERATED»
  RING_POW_ZERO := SessionLibrary.RingTheory.«RING_POW_ZERO»
  RING_SUB_REFL := SessionLibrary.RingTheory.«RING_SUB_REFL»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  SING_SUBSET := Session.SING_SUBSET
  SPLITTING_TYPES_INTEGER_RING := SessionANT.SplittingTypes.«SPLITTING_TYPES_INTEGER_RING»
  SUBFIELD_GENERATED_INC := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_INC»
  num_divides := Session.num_divides
  number_field := SessionANT.Numfield.«number_field»
  ring_automorphism := SessionLibrary.RingTheory.«ring_automorphism»

/-- What cyclotomic_quadratic_split.ml uses from Session. -/
def deps : HolANT.CyclotomicQuadraticSplit.CyclotomicQuadraticSplitDeps where
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

/- The bundles, in cyclotomic_quadratic_split.ml order. -/
initialize BCyclotomicQuadraticSplit : HolANT.CyclotomicQuadraticSplit.CyclotomicQuadraticSplit ←
  ioB "setupCyclotomicQuadraticSplit" (HolANT.CyclotomicQuadraticSplit.setupCyclotomicQuadraticSplit deps).run

-- CyclotomicQuadraticSplit
def QUADRATIC_FIELD_TOTALLY_SPLIT_ODD_PRIME : thm := BCyclotomicQuadraticSplit.QUADRATIC_FIELD_TOTALLY_SPLIT_ODD_PRIME
def CYCLOTOMIC_QUADRATIC_SUBFIELD_TOTALLY_SPLIT : thm := BCyclotomicQuadraticSplit.CYCLOTOMIC_QUADRATIC_SUBFIELD_TOTALLY_SPLIT
def CYCLOTOMIC_QUADRATIC_SUBFIELD_DECOMPOSITION : thm := BCyclotomicQuadraticSplit.CYCLOTOMIC_QUADRATIC_SUBFIELD_DECOMPOSITION

/-- `needs "ANT/cyclotomic_quadratic_split.ml"`: already done by importing this module. -/
def ensureCyclotomicQuadraticSplit : IO Unit := pure ()

end SessionANT.CyclotomicQuadraticSplit
