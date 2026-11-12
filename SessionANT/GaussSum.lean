/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/gauss_sum.ml                                  . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/GaussSum.lean

  The session half of the gauss_sum.ml translation: it supplies HolANT.GaussSum's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/gauss_sum.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.GaussSum
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
import SessionLibrary.Integer
import SessionLibrary.Products
import SessionLibrary.Multiplicative
import SessionLibrary.Primitive
import SessionLibrary.Jacobi
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
import SessionLibrary.ModmulGroup
import SessionANT.Algmisc
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
import SessionANT.Quadratic
import SessionANT.PrimeSplit
import SessionANT.TraceForm
import SessionANT.FiniteFieldTrace
import SessionANT.Ramification
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.Classgroup
import SessionANT.RelativeSplit
import SessionANT.RelativeDegree
import SessionANT.NfValuation
import SessionANT.Integrality
import SessionANT.DedekindKummer
import SessionANT.QuadraticSplit
import SessionLibrary.SymmetricGroup
import SessionLibrary.Galois
import SessionLibrary.RingGroups
import SessionLibrary.FiniteFields
import SessionANT.CyclotomicPoly
import SessionANT.PowerBasis
import SessionANT.CyclotomicField
import SessionANT.CyclotomicIntegers
import SessionLibrary.Cyclotomic
import SessionANT.CyclotomicGalois
import SessionANT.CyclotomicSubfields

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.GaussSum

/-- The core theorems gauss_sum.ml uses. -/
def core1 : HolANT.GaussSum.CoreThms1 where
  COPRIME_0 := SessionLibrary.Prime.«COPRIME_0»
  COPRIME_SYM := SessionLibrary.Prime.«COPRIME_SYM»
  CYCLIC_MODMUL_GROUP := SessionLibrary.ModmulGroup.«CYCLIC_MODMUL_GROUP»
  CYCLOTOMIC_FIELD_SUBFIELD_UNIQUE := SessionANT.CyclotomicSubfields.«CYCLOTOMIC_FIELD_SUBFIELD_UNIQUE»
  DIVIDES_LE := Session.DIVIDES_LE
  DIVIDES_REFL := SessionLibrary.Prime.«DIVIDES_REFL»
  EQ_TRANS := Session.EQ_TRANS
  EXP_1 := Session.EXP_1
  EXP_2 := Session.EXP_2
  EXTENSION_DEGREE_SIMPLE := SessionLibrary.FieldTheory.«EXTENSION_DEGREE_SIMPLE»
  FIELD_EXTENSION_IMP_HOMOMORPHISM := SessionLibrary.FieldTheory.«FIELD_EXTENSION_IMP_HOMOMORPHISM»
  FIELD_EXTENSION_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_EXTENSION_SUBFIELD_GENERATED»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«FIELD_IMP_NONTRIVIAL_RING»
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  IMAGE_I := Session.IMAGE_I
  INT_ABS_MUL := Session.INT_ABS_MUL
  INT_ABS_NEG := Session.INT_ABS_NEG
  INT_ABS_NUM := Session.INT_ABS_NUM
  INT_ABS_POW := Session.INT_ABS_POW
  INT_MUL_LID := Session.INT_MUL_LID
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_POW_ONE := Session.INT_POW_ONE
  IN_ELIM_THM := Session.IN_ELIM_THM
  IRREDUCIBLE_IMP_POLY_DEG_NZ := SessionLibrary.RingTheory.«IRREDUCIBLE_IMP_POLY_DEG_NZ»
  I_THM := Session.I_THM
  JACOBI_EQ_0 := SessionLibrary.Jacobi.«JACOBI_EQ_0»
  JACOBI_LMUL := SessionLibrary.Jacobi.«JACOBI_LMUL»
  JACOBI_MINUS1 := SessionLibrary.Jacobi.«JACOBI_MINUS1»
  JACOBI_MOD := SessionLibrary.Jacobi.«JACOBI_MOD»
  JACOBI_PRIME := SessionLibrary.Jacobi.«JACOBI_PRIME»
  JACOBI_SQUARED := SessionLibrary.Jacobi.«JACOBI_SQUARED»
  JACOBI_SUM_RESIDUES := SessionLibrary.Jacobi.«JACOBI_SUM_RESIDUES»
  MINIMAL_POLYNOMIAL_DEG_EQ_1 := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_DEG_EQ_1»
  MINIMAL_POLYNOMIAL_DEG_LE := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_DEG_LE»
  MINIMAL_POLYNOMIAL_IRREDUCIBLE := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_IRREDUCIBLE»
  MULT_CLAUSES := Session.MULT_CLAUSES
  NUMBER_FIELD_ALGEBRAIC := SessionANT.Numfield.«NUMBER_FIELD_ALGEBRAIC»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUM_OF_INT_OF_NUM := Session.NUM_OF_INT_OF_NUM
  POLY_DEG_0 := SessionLibrary.RingTheory.«POLY_DEG_0»
  PRIME_1 := SessionLibrary.Prime.«PRIME_1»
  PRIME_COPRIME_EQ := SessionLibrary.Prime.«PRIME_COPRIME_EQ»
  PRIME_GE_2 := SessionLibrary.Prime.«PRIME_GE_2»
  PRIME_IMP_NZ := SessionLibrary.Prime.«PRIME_IMP_NZ»
  PRIME_IMP_SQUAREFREE := SessionLibrary.Pocklington.«PRIME_IMP_SQUAREFREE»
  PRIME_ODD := SessionLibrary.Prime.«PRIME_ODD»
  QUADRATIC_POLY_DEG := SessionANT.QuadraticSplit.«QUADRATIC_POLY_DEG»
  QUADRATIC_POLY_EXTEND := SessionANT.QuadraticSplit.«QUADRATIC_POLY_EXTEND»
  QUADRATIC_POLY_IN_CARRIER := SessionANT.QuadraticSplit.«QUADRATIC_POLY_IN_CARRIER»
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD_LZERO := SessionLibrary.RingTheory.«RING_ADD_LZERO»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_POW := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POW»
  RING_HOMOMORPHISM_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_INT»
  RING_HOMOMORPHISM_SUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUM»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_ASSOC := SessionLibrary.RingTheory.«RING_MUL_ASSOC»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_OF_INT_0 := SessionLibrary.RingTheory.«RING_OF_INT_0»
  RING_OF_INT_1 := SessionLibrary.RingTheory.«RING_OF_INT_1»
  RING_OF_INT_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_INT_IN_SUBFIELD_GENERATED»
  RING_OF_INT_ISUM := SessionLibrary.RingTheory.«RING_OF_INT_ISUM»
  RING_OF_INT_MUL := SessionLibrary.RingTheory.«RING_OF_INT_MUL»
  RING_OF_INT_OF_NUM := SessionLibrary.RingTheory.«RING_OF_INT_OF_NUM»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_2 := SessionLibrary.RingTheory.«RING_POW_2»
  RING_POW_ADD := SessionLibrary.RingTheory.«RING_POW_ADD»
  RING_POW_MOD_ORDER := SessionLibrary.RingTheory.«RING_POW_MOD_ORDER»
  RING_POW_POW := SessionLibrary.RingTheory.«RING_POW_POW»
  RING_SUB_REFL := SessionLibrary.RingTheory.«RING_SUB_REFL»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_DELTA := SessionLibrary.RingTheory.«RING_SUM_DELTA»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_LMUL := SessionLibrary.RingTheory.«RING_SUM_LMUL»
  RING_SUM_MOD_MULT_REINDEX := SessionLibrary.RingTheory.«RING_SUM_MOD_MULT_REINDEX»
  RING_SUM_RMUL := SessionLibrary.RingTheory.«RING_SUM_RMUL»
  RING_SUM_ROOT_OF_UNITY_POWERS := SessionLibrary.RingTheory.«RING_SUM_ROOT_OF_UNITY_POWERS»
  RING_SUM_SWAP := SessionLibrary.RingTheory.«RING_SUM_SWAP»
  SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD := SessionANT.Quadratic.«SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD»
  SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED»
  SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED»
  SUBFIELD_GENERATED_SING_ALGEBRAIC := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_SING_ALGEBRAIC»
  SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_SUBFIELD_GENERATED»
  SUBFIELD_SUBFIELD_GENERATED_EQ := SessionLibrary.FieldTheory.«SUBFIELD_SUBFIELD_GENERATED_EQ»
  number_field := SessionANT.Numfield.«number_field»
  o_THM := Session.o_THM
  ring_pow := SessionLibrary.RingTheory.«ring_pow»

/-- What gauss_sum.ml uses from Session. -/
def deps : HolANT.GaussSum.GaussSumDeps where
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

/- The bundles, in gauss_sum.ml order. -/
initialize BGaussSum : HolANT.GaussSum.GaussSum ←
  ioB "setupGaussSum" (HolANT.GaussSum.setupGaussSum deps).run

-- GaussSum
def QUADRATIC_GAUSS_SUM : thm := BGaussSum.QUADRATIC_GAUSS_SUM
def QUADRATIC_GAUSS_SUM_HOMOMORPHISM : thm := BGaussSum.QUADRATIC_GAUSS_SUM_HOMOMORPHISM
def NUMBER_FIELD_SQRT_DEGREE : thm := BGaussSum.NUMBER_FIELD_SQRT_DEGREE
def CYCLOTOMIC_FIELD_QUADRATIC_SUBFIELD : thm := BGaussSum.CYCLOTOMIC_FIELD_QUADRATIC_SUBFIELD
def CYCLOTOMIC_FIELD_QUADRATIC_SUBFIELD_GAUSS_SUM : thm := BGaussSum.CYCLOTOMIC_FIELD_QUADRATIC_SUBFIELD_GAUSS_SUM

/-- `needs "ANT/gauss_sum.ml"`: already done by importing this module. -/
def ensureGaussSum : IO Unit := pure ()

end SessionANT.GaussSum
