/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/ideal_norm.ml                                 . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/IdealNorm.lean

  The session half of the ideal_norm.ml translation: it supplies HolANT.IdealNorm's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/ideal_norm.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.IdealNorm
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.RingTheory
import SessionLibrary.Permutations
import SessionLibrary.RingDet
import SessionANT.IdealArith
import SessionLibrary.Products
import SessionANT.Algmisc
import SessionLibrary.Matroids
import SessionLibrary.FieldTheory
import SessionANT.Integral
import SessionANT.Dedekind
import SessionANT.DedekindStruct

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.IdealNorm

/-- The core theorems ideal_norm.ml uses. -/
def core1 : HolANT.IdealNorm.CoreThms1 where
  CARD_EQ_0 := Session.CARD_EQ_0
  CARD_EQ_CARD_IMP := SessionLibrary.Card.«CARD_EQ_CARD_IMP»
  CARD_EQ_IMAGES := SessionLibrary.Card.«CARD_EQ_IMAGES»
  CARD_EQ_REFL := SessionLibrary.Card.«CARD_EQ_REFL»
  CARD_EQ_RING_IMAGE_KERNEL := SessionLibrary.RingTheory.«CARD_EQ_RING_IMAGE_KERNEL»
  CARD_EQ_SYM := SessionLibrary.Card.«CARD_EQ_SYM»
  CARD_EQ_TRANS := SessionLibrary.Card.«CARD_EQ_TRANS»
  CARD_FINITE_CONG := SessionLibrary.Card.«CARD_FINITE_CONG»
  CARD_LE_1 := Session.CARD_LE_1
  CARD_MUL_C := SessionLibrary.Card.«CARD_MUL_C»
  CARD_MUL_CONG := SessionLibrary.Card.«CARD_MUL_CONG»
  CARD_MUL_FINITE := SessionLibrary.Card.«CARD_MUL_FINITE»
  CARD_MUL_FINITE_EQ := SessionLibrary.Card.«CARD_MUL_FINITE_EQ»
  DEDEKIND_IDEAL_FACTORIZATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_FACTORIZATION»
  DEDEKIND_IDEAL_QUOTIENT_CANCEL := SessionANT.Dedekind.«DEDEKIND_IDEAL_QUOTIENT_CANCEL»
  DEDEKIND_IMP_INTEGRAL_DOMAIN := SessionANT.Dedekind.«DEDEKIND_IMP_INTEGRAL_DOMAIN»
  DEDEKIND_IMP_NOETHERIAN := SessionANT.Dedekind.«DEDEKIND_IMP_NOETHERIAN»
  DEDEKIND_TWO_GENERATORS_STRONG := SessionANT.DedekindStruct.«DEDEKIND_TWO_GENERATORS_STRONG»
  EMPTY_SUBSET := Session.EMPTY_SUBSET
  EQ_IMP := Session.EQ_IMP
  EQ_MULT_LCANCEL := Session.EQ_MULT_LCANCEL
  ETA_AX := Session.ETA_AX
  EXP := Session.EXP
  FIELD_EQ_TRIVIAL_IDEALS := SessionLibrary.RingTheory.«FIELD_EQ_TRIVIAL_IDEALS»
  FINITE_FUNSPACE := Session.FINITE_FUNSPACE
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_IMAGE_INJ_EQ := Session.FINITE_IMAGE_INJ_EQ
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_INTEGRAL_DOMAIN_IMP_FIELD := SessionLibrary.RingTheory.«FINITE_INTEGRAL_DOMAIN_IMP_FIELD»
  FINITE_SUBSET := Session.FINITE_SUBSET
  FINITE_SUBSET_IMAGE := Session.FINITE_SUBSET_IMAGE
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  FUN_IN_IMAGE := Session.FUN_IN_IMAGE
  HAS_SIZE := Session.HAS_SIZE
  IDEAL_GENERATED_FINITE := SessionLibrary.RingTheory.«IDEAL_GENERATED_FINITE»
  IDEAL_GENERATED_INC_GEN := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC_GEN»
  IDEAL_GENERATED_INSERT := SessionLibrary.RingTheory.«IDEAL_GENERATED_INSERT»
  IDEAL_GENERATED_MINIMAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL»
  IDEAL_GENERATED_SING_ALT := SessionLibrary.RingTheory.«IDEAL_GENERATED_SING_ALT»
  IDEAL_POW_0 := SessionANT.IdealArith.«IDEAL_POW_0»
  IDEAL_POW_EQ_ZERO := SessionANT.IdealArith.«IDEAL_POW_EQ_ZERO»
  IDEAL_POW_SUC := SessionANT.IdealArith.«IDEAL_POW_SUC»
  IDEAL_PRODUCT_EMPTY := SessionANT.IdealArith.«IDEAL_PRODUCT_EMPTY»
  IDEAL_PRODUCT_EQ_ZERO := SessionANT.IdealArith.«IDEAL_PRODUCT_EQ_ZERO»
  IDEAL_PRODUCT_INSERT := SessionANT.IdealArith.«IDEAL_PRODUCT_INSERT»
  IDEAL_PROD_CARRIER_LEFT := SessionANT.IdealArith.«IDEAL_PROD_CARRIER_LEFT»
  IDEAL_PROD_COMM := SessionANT.IdealArith.«IDEAL_PROD_COMM»
  IDEAL_PROD_EQ_ZERO := SessionANT.IdealArith.«IDEAL_PROD_EQ_ZERO»
  IDEAL_PROD_LZERO := SessionANT.IdealArith.«IDEAL_PROD_LZERO»
  IDEAL_PROD_SUBSET_LEFT := SessionANT.IdealArith.«IDEAL_PROD_SUBSET_LEFT»
  IMAGE_EQ_EMPTY := Session.IMAGE_EQ_EMPTY
  IMP_CONJ := Session.IMP_CONJ
  INSERT_SUBSET := Session.INSERT_SUBSET
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_RING_IDEAL_LMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_LMUL»
  IN_RING_IDEAL_SUM := SessionLibrary.RingTheory.«IN_RING_IDEAL_SUM»
  IN_SING := Session.IN_SING
  ITERATE_EQ := Session.ITERATE_EQ
  LEFT_AND_EXISTS_THM := Session.LEFT_AND_EXISTS_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_REFL := Session.LE_REFL
  MONOIDAL_MUL := Session.MONOIDAL_MUL
  MONO_EXISTS := Session.MONO_EXISTS
  MULT_CLAUSES := Session.MULT_CLAUSES
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NPRODUCT_CLAUSES := Session.NPRODUCT_CLAUSES
  PRIME_1 := SessionLibrary.Prime.«PRIME_1»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PROPER_IDEAL_ALT := SessionLibrary.RingTheory.«PROPER_IDEAL_ALT»
  PSUBSET := Session.PSUBSET
  QUOTIENT_RING_0 := SessionLibrary.RingTheory.«QUOTIENT_RING_0»
  QUOTIENT_RING_CARRIER := SessionLibrary.RingTheory.«QUOTIENT_RING_CARRIER»
  QUOTIENT_RING_UNIVERSAL_EPIMORPHISM := SessionLibrary.RingTheory.«QUOTIENT_RING_UNIVERSAL_EPIMORPHISM»
  RIGHT_AND_EXISTS_THM := Session.RIGHT_AND_EXISTS_THM
  RIGHT_EXISTS_IMP_THM := Session.RIGHT_EXISTS_IMP_THM
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_CARRIER_NONEMPTY := SessionLibrary.RingTheory.«RING_CARRIER_NONEMPTY»
  RING_CHAR_DIVIDES_ORDER := SessionLibrary.RingTheory.«RING_CHAR_DIVIDES_ORDER»
  RING_COSET_EQ := SessionLibrary.RingTheory.«RING_COSET_EQ»
  RING_COSET_EQ_IDEAL := SessionLibrary.RingTheory.«RING_COSET_EQ_IDEAL»
  RING_COSET_TRIVIAL := SessionLibrary.RingTheory.«RING_COSET_TRIVIAL»
  RING_EPIMORPHISM := SessionLibrary.RingTheory.«RING_EPIMORPHISM»
  RING_EPIMORPHISM_RING_COSET := SessionLibrary.RingTheory.«RING_EPIMORPHISM_RING_COSET»
  RING_HOMOMORPHISM_RING_COSET := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_COSET»
  RING_HOMOMORPHISM_RING_OF_NUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_NUM»
  RING_IDEAL_0 := SessionLibrary.RingTheory.«RING_IDEAL_0»
  RING_IDEAL_CARRIER := SessionLibrary.RingTheory.«RING_IDEAL_CARRIER»
  RING_IDEAL_IDEAL_POW := SessionANT.IdealArith.«RING_IDEAL_IDEAL_POW»
  RING_IDEAL_IDEAL_PROD := SessionANT.IdealArith.«RING_IDEAL_IDEAL_PROD»
  RING_IDEAL_IDEAL_PRODUCT := SessionANT.IdealArith.«RING_IDEAL_IDEAL_PRODUCT»
  RING_IDEAL_IMP_NONEMPTY := SessionLibrary.RingTheory.«RING_IDEAL_IMP_NONEMPTY»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_IDEAL_QUOTIENT_LMUL := SessionLibrary.RingTheory.«RING_IDEAL_QUOTIENT_LMUL»
  RING_KERNEL_RING_COSET := SessionLibrary.RingTheory.«RING_KERNEL_RING_COSET»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_IN_IDEAL_PROD := SessionANT.IdealArith.«RING_MUL_IN_IDEAL_PROD»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_OF_NUM_EQ_0 := SessionLibrary.RingTheory.«RING_OF_NUM_EQ_0»
  RING_SETADD_MONO := SessionLibrary.RingTheory.«RING_SETADD_MONO»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_RDISTRIB := SessionLibrary.RingTheory.«RING_SUB_RDISTRIB»
  RING_SUB_RZERO := SessionLibrary.RingTheory.«RING_SUB_RZERO»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_SUB := SessionLibrary.RingTheory.«RING_SUM_SUB»
  SIMPLE_IMAGE := Session.SIMPLE_IMAGE
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUBSET_REFL := Session.SUBSET_REFL
  TRIVIAL_IMP_FINITE_RING := SessionLibrary.RingTheory.«TRIVIAL_IMP_FINITE_RING»
  TRIVIAL_QUOTIENT_RING := SessionLibrary.RingTheory.«TRIVIAL_QUOTIENT_RING»
  TRIVIAL_RING_HAS_SIZE_1 := SessionLibrary.RingTheory.«TRIVIAL_RING_HAS_SIZE_1»
  divides := Session.divides
  finitely_generated_ideal := SessionLibrary.RingTheory.«finitely_generated_ideal»
  ideal_quotient := SessionANT.IdealArith.«ideal_quotient»
  maximal_ideal := SessionLibrary.RingTheory.«maximal_ideal»
  noetherian_ring := SessionLibrary.RingTheory.«noetherian_ring»
  nproduct := Session.nproduct
  prime := Session.prime
  proper_ideal := SessionLibrary.RingTheory.«proper_ideal»
  ring_kernel := SessionLibrary.RingTheory.«ring_kernel»
  ring_setadd := SessionLibrary.RingTheory.«ring_setadd»

/-- What ideal_norm.ml uses from Session. -/
def deps : HolANT.IdealNorm.IdealNormDeps where
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

/- The bundles, in ideal_norm.ml order. -/
initialize BIdealNorm : HolANT.IdealNorm.IdealNorm ←
  ioB "setupIdealNorm" (HolANT.IdealNorm.setupIdealNorm deps).run

-- IdealNorm
def ideal_norm : thm := BIdealNorm.ideal_norm
def IDEAL_NORM_CARRIER : thm := BIdealNorm.IDEAL_NORM_CARRIER
def IDEAL_NORM_POS : thm := BIdealNorm.IDEAL_NORM_POS
def IDEAL_NORM_GT_1 : thm := BIdealNorm.IDEAL_NORM_GT_1
def IDEAL_NORM_IN_IDEAL : thm := BIdealNorm.IDEAL_NORM_IN_IDEAL
def CARD_EQ_QUOTIENT_RING_CHAIN : thm := BIdealNorm.CARD_EQ_QUOTIENT_RING_CHAIN
def FINITE_QUOTIENT_RING_CHAIN : thm := BIdealNorm.FINITE_QUOTIENT_RING_CHAIN
def FINITE_QUOTIENT_RING_MONO : thm := BIdealNorm.FINITE_QUOTIENT_RING_MONO
def CARD_QUOTIENT_RING_CHAIN : thm := BIdealNorm.CARD_QUOTIENT_RING_CHAIN
def IDEAL_NORM_SUBSET_EQ : thm := BIdealNorm.IDEAL_NORM_SUBSET_EQ
def IDEAL_NORM_SUBSET_DIVIDES : thm := BIdealNorm.IDEAL_NORM_SUBSET_DIVIDES
def FINITE_QUOTIENT_RING_IDEAL_PROD : thm := BIdealNorm.FINITE_QUOTIENT_RING_IDEAL_PROD
def FINITE_QUOTIENT_RING_IDEAL_POW : thm := BIdealNorm.FINITE_QUOTIENT_RING_IDEAL_POW
def IDEAL_NORM_PRIME_IMP_MAXIMAL : thm := BIdealNorm.IDEAL_NORM_PRIME_IMP_MAXIMAL
def CARD_EQ_QUOTIENT_RING_IDEAL_PROD : thm := BIdealNorm.CARD_EQ_QUOTIENT_RING_IDEAL_PROD
def IDEAL_NORM_MUL : thm := BIdealNorm.IDEAL_NORM_MUL
def IDEAL_NORM_IDEAL_POW : thm := BIdealNorm.IDEAL_NORM_IDEAL_POW
def IDEAL_NORM_PRIME_POWER : thm := BIdealNorm.IDEAL_NORM_PRIME_POWER
def IDEAL_NORM_IDEAL_PRODUCT : thm := BIdealNorm.IDEAL_NORM_IDEAL_PRODUCT
def IDEAL_NORM_FACTORIZATION : thm := BIdealNorm.IDEAL_NORM_FACTORIZATION
def DEDEKIND_IDEAL_NORM_PRIME_POWERS : thm := BIdealNorm.DEDEKIND_IDEAL_NORM_PRIME_POWERS

/-- `needs "ANT/ideal_norm.ml"`: already done by importing this module. -/
def ensureIdealNorm : IO Unit := pure ()

end SessionANT.IdealNorm
