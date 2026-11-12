/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/ideal_euler.ml                                . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/IdealEuler.lean

  The session half of the ideal_euler.ml translation: it supplies HolANT.IdealEuler's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/ideal_euler.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.IdealEuler
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.RingTheory
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
import SessionLibrary.RingGroups
import SessionLibrary.Products
import SessionLibrary.Matroids
import SessionLibrary.Permutations
import SessionLibrary.RingDet
import SessionLibrary.FieldTheory
import SessionLibrary.SymmetricGroup
import SessionLibrary.Galois
import SessionLibrary.FiniteFields
import SessionANT.IdealArith
import SessionANT.Hensel
import SessionANT.Algmisc
import SessionANT.Integral
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.IdealEuler

/-- The core theorems ideal_euler.ml uses. -/
def core1 : HolANT.IdealEuler.CoreThms1 where
  CARD_DELETE := Session.CARD_DELETE
  CARD_DIFF := Session.CARD_DIFF
  CARD_EQ_0 := Session.CARD_EQ_0
  CARD_QUOTIENT_RING_CHAIN := SessionANT.IdealNorm.«CARD_QUOTIENT_RING_CHAIN»
  CARD_SING := Session.CARD_SING
  CARD_UNITS_PROD_RING := SessionLibrary.RingGroups.«CARD_UNITS_PROD_RING»
  CHINESE_REMAINDER_RING_ISOMORPHISM := SessionANT.IdealArith.«CHINESE_REMAINDER_RING_ISOMORPHISM»
  COMAXIMAL_IDEAL_POW := SessionANT.IdealArith.«COMAXIMAL_IDEAL_POW»
  COMAXIMAL_IDEAL_PRODUCT := SessionANT.IdealArith.«COMAXIMAL_IDEAL_PRODUCT»
  DEDEKIND_IDEAL_FACTORIZATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_FACTORIZATION»
  DEDEKIND_IMP_NOETHERIAN := SessionANT.Dedekind.«DEDEKIND_IMP_NOETHERIAN»
  DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL := SessionANT.Dedekind.«DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL»
  DEDEKIND_PRIME_IDEAL_UNIFORMIZER := SessionANT.Dedekind.«DEDEKIND_PRIME_IDEAL_UNIFORMIZER»
  EQ_MULT_LCANCEL := Session.EQ_MULT_LCANCEL
  EXP := Session.EXP
  EXTENSION := Session.EXTENSION
  FIELD_QUOTIENT_RING := SessionLibrary.RingTheory.«FIELD_QUOTIENT_RING»
  FIELD_UNIT := SessionLibrary.RingTheory.«FIELD_UNIT»
  FINITE_CROSS := Session.FINITE_CROSS
  FINITE_FIELD_PRIMITIVE_ROOT := SessionLibrary.FiniteFields.«FINITE_FIELD_PRIMITIVE_ROOT»
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_QUOTIENT_RING_IDEAL_PROD := SessionANT.IdealNorm.«FINITE_QUOTIENT_RING_IDEAL_PROD»
  FINITE_QUOTIENT_RING_MONO := SessionANT.IdealNorm.«FINITE_QUOTIENT_RING_MONO»
  FINITE_SING := Session.FINITE_SING
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  GROUP_POW_GROUP_ORDER := SessionLibrary.GroupTheory.«GROUP_POW_GROUP_ORDER»
  IDEAL_GENERATED_MINIMAL_EQ := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL_EQ»
  IDEAL_GENERATED_SING := SessionLibrary.RingTheory.«IDEAL_GENERATED_SING»
  IDEAL_GENERATED_SUBSET := SessionLibrary.RingTheory.«IDEAL_GENERATED_SUBSET»
  IDEAL_NORM_FACTORIZATION := SessionANT.IdealNorm.«IDEAL_NORM_FACTORIZATION»
  IDEAL_NORM_GT_1 := SessionANT.IdealNorm.«IDEAL_NORM_GT_1»
  IDEAL_NORM_IDEAL_POW := SessionANT.IdealNorm.«IDEAL_NORM_IDEAL_POW»
  IDEAL_NORM_IN_IDEAL := SessionANT.IdealNorm.«IDEAL_NORM_IN_IDEAL»
  IDEAL_NORM_POS := SessionANT.IdealNorm.«IDEAL_NORM_POS»
  IDEAL_POW_1 := SessionANT.IdealArith.«IDEAL_POW_1»
  IDEAL_POW_ANTIMONO := SessionANT.IdealArith.«IDEAL_POW_ANTIMONO»
  IDEAL_PRODUCT_EMPTY := SessionANT.IdealArith.«IDEAL_PRODUCT_EMPTY»
  IDEAL_PRODUCT_INSERT := SessionANT.IdealArith.«IDEAL_PRODUCT_INSERT»
  IDEAL_PROD_COMAXIMAL := SessionANT.IdealArith.«IDEAL_PROD_COMAXIMAL»
  IDEAL_VALUATION_EQ_0 := SessionANT.Dedekind.«IDEAL_VALUATION_EQ_0»
  IMP_CONJ := Session.IMP_CONJ
  IN_DELETE := Session.IN_DELETE
  IN_DIFF := Session.IN_DIFF
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_RING_IDEAL_ADD := SessionLibrary.RingTheory.«IN_RING_IDEAL_ADD»
  IN_RING_IDEAL_LMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_LMUL»
  IN_RING_IDEAL_NEG := SessionLibrary.RingTheory.«IN_RING_IDEAL_NEG»
  IN_RING_IDEAL_RMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_RMUL»
  IN_RING_IDEAL_SUB := SessionLibrary.RingTheory.«IN_RING_IDEAL_SUB»
  IN_SING := Session.IN_SING
  ISOMORPHIC_RING_CARD_UNITS := SessionLibrary.RingGroups.«ISOMORPHIC_RING_CARD_UNITS»
  ISOMORPHIC_RING_SYM := SessionLibrary.RingTheory.«ISOMORPHIC_RING_SYM»
  LEFT_AND_EXISTS_THM := Session.LEFT_AND_EXISTS_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LEFT_SUB_DISTRIB := Session.LEFT_SUB_DISTRIB
  LE_1 := Session.LE_1
  MAXIMAL_IDEAL_COMAXIMAL := SessionANT.IdealArith.«MAXIMAL_IDEAL_COMAXIMAL»
  MAXIMAL_IMP_PROPER_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_PROPER_IDEAL»
  MAXIMAL_IMP_RING_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_RING_IDEAL»
  MULT_AC := Session.MULT_AC
  MULT_CLAUSES := Session.MULT_CLAUSES
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NPRODUCT_CLAUSES := Session.NPRODUCT_CLAUSES
  PRIME_IMP_PROPER_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_PROPER_IDEAL»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PRODUCT_EQ := SessionLibrary.Products.«PRODUCT_EQ»
  PRODUCT_MUL := SessionLibrary.Products.«PRODUCT_MUL»
  PROD_RING := SessionLibrary.RingTheory.«PROD_RING»
  PROPER_IDEAL_ALT := SessionLibrary.RingTheory.«PROPER_IDEAL_ALT»
  PSUBSET := Session.PSUBSET
  QUOTIENT_RING := SessionLibrary.RingTheory.«QUOTIENT_RING»
  QUOTIENT_RING_0 := SessionLibrary.RingTheory.«QUOTIENT_RING_0»
  QUOTIENT_RING_1 := SessionLibrary.RingTheory.«QUOTIENT_RING_1»
  QUOTIENT_RING_CARRIER := SessionLibrary.RingTheory.«QUOTIENT_RING_CARRIER»
  REAL_OF_NUM_EQ := Session.REAL_OF_NUM_EQ
  REAL_OF_NUM_MUL := Session.REAL_OF_NUM_MUL
  REAL_OF_NUM_NPRODUCT := SessionLibrary.Products.«REAL_OF_NUM_NPRODUCT»
  REAL_OF_NUM_POW := Session.REAL_OF_NUM_POW
  REAL_OF_NUM_SUB := Session.REAL_OF_NUM_SUB
  RIGHT_AND_EXISTS_THM := Session.RIGHT_AND_EXISTS_THM
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_COSET_EQ := SessionLibrary.RingTheory.«RING_COSET_EQ»
  RING_COSET_EQ_IDEAL := SessionLibrary.RingTheory.«RING_COSET_EQ_IDEAL»
  RING_HOMOMORPHISM_POW := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POW»
  RING_HOMOMORPHISM_RING_COSET := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_COSET»
  RING_IDEAL_CARRIER := SessionLibrary.RingTheory.«RING_IDEAL_CARRIER»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IDEAL_POW := SessionANT.IdealArith.«RING_IDEAL_IDEAL_POW»
  RING_IDEAL_IDEAL_PRODUCT := SessionANT.IdealArith.«RING_IDEAL_IDEAL_PRODUCT»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_IN_IDEAL_POW := SessionANT.IdealArith.«RING_MUL_IN_IDEAL_POW»
  RING_NEG_SUB := SessionLibrary.RingTheory.«RING_NEG_SUB»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_ADD_SQUARE_CONGRUENCE := SessionLibrary.RingTheory.«RING_POW_ADD_SQUARE_CONGRUENCE»
  RING_SETADD_SYM := SessionLibrary.RingTheory.«RING_SETADD_SYM»
  RING_SUB_REFL := SessionLibrary.RingTheory.«RING_SUB_REFL»
  RING_UNIT_IN_CARRIER := SessionLibrary.RingTheory.«RING_UNIT_IN_CARRIER»
  RING_UNIT_QUOTIENT_RING_COSET := SessionLibrary.RingTheory.«RING_UNIT_QUOTIENT_RING_COSET»
  RING_UNIT_QUOTIENT_RING_IDEAL_POW := SessionANT.Hensel.«RING_UNIT_QUOTIENT_RING_IDEAL_POW»
  RING_UNIT_QUOTIENT_RING_MAXIMAL := SessionLibrary.RingTheory.«RING_UNIT_QUOTIENT_RING_MAXIMAL»
  SUBSET := Session.SUBSET
  SUB_ADD := Session.SUB_ADD
  TRIVIAL_QUOTIENT_RING := SessionLibrary.RingTheory.«TRIVIAL_QUOTIENT_RING»
  TRIVIAL_RING_10 := SessionLibrary.RingTheory.«TRIVIAL_RING_10»
  UNIT_GROUP := SessionLibrary.RingGroups.«UNIT_GROUP»
  UNIT_GROUP_POW := SessionLibrary.RingGroups.«UNIT_GROUP_POW»
  ideal_norm := SessionANT.IdealNorm.«ideal_norm»
  maximal_ideal := SessionLibrary.RingTheory.«maximal_ideal»
  real_pow := Session.real_pow
  ring_divides := SessionLibrary.RingTheory.«ring_divides»
  ring_pow := SessionLibrary.RingTheory.«ring_pow»
  ring_setadd := SessionLibrary.RingTheory.«ring_setadd»
  ring_unit := SessionLibrary.RingTheory.«ring_unit»
  trivial_ring := SessionLibrary.RingTheory.«trivial_ring»

/-- What ideal_euler.ml uses from Session. -/
def deps : HolANT.IdealEuler.IdealEulerDeps where
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

/- The bundles, in ideal_euler.ml order. -/
initialize BIdealEuler : HolANT.IdealEuler.IdealEuler ←
  ioB "setupIdealEuler" (HolANT.IdealEuler.setupIdealEuler deps).run

-- IdealEuler
def IDEAL_EULER : thm := BIdealEuler.IDEAL_EULER
def CARD_UNITS_QUOTIENT_RING_MAXIMAL : thm := BIdealEuler.CARD_UNITS_QUOTIENT_RING_MAXIMAL
def IDEAL_NORM_FERMAT : thm := BIdealEuler.IDEAL_NORM_FERMAT
def MAXIMAL_IDEAL_FINITE_QUOTIENT_POW_CARD : thm := BIdealEuler.MAXIMAL_IDEAL_FINITE_QUOTIENT_POW_CARD
def DEDEKIND_RESIDUE_GENERATOR_UNIFORMIZER : thm := BIdealEuler.DEDEKIND_RESIDUE_GENERATOR_UNIFORMIZER
def CARD_UNITS_QUOTIENT_RING_COPRIME : thm := BIdealEuler.CARD_UNITS_QUOTIENT_RING_COPRIME
def CARD_UNITS_QUOTIENT_RING_PRIME_POW : thm := BIdealEuler.CARD_UNITS_QUOTIENT_RING_PRIME_POW
def CARD_UNITS_QUOTIENT_RING_PRIME_PRODUCT : thm := BIdealEuler.CARD_UNITS_QUOTIENT_RING_PRIME_PRODUCT
def DEDEKIND_CARD_UNITS_QUOTIENT_RING : thm := BIdealEuler.DEDEKIND_CARD_UNITS_QUOTIENT_RING
def DEDEKIND_CARD_UNITS_QUOTIENT_RING_REAL : thm := BIdealEuler.DEDEKIND_CARD_UNITS_QUOTIENT_RING_REAL

/-- `needs "ANT/ideal_euler.ml"`: already done by importing this module. -/
def ensureIdealEuler : IO Unit := pure ()

end SessionANT.IdealEuler
