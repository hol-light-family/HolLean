/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/dedekind_local.ml                             . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/DedekindLocal.lean

  The session half of the dedekind_local.ml translation: it supplies HolANT.DedekindLocal's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/dedekind_local.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.DedekindLocal
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
import SessionANT.Integral
import SessionANT.IdealArith
import SessionLibrary.Products
import SessionANT.Algmisc
import SessionANT.Dedekind
import SessionANT.DedekindStruct

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.DedekindLocal

/-- The core theorems dedekind_local.ml uses. -/
def core1 : HolANT.DedekindLocal.CoreThms1 where
  DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES := SessionANT.Dedekind.«DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES»
  DEDEKIND_IDEAL_SUBSET_POW_VALUATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_SUBSET_POW_VALUATION»
  DEDEKIND_IMP_INTEGRAL_DOMAIN := SessionANT.Dedekind.«DEDEKIND_IMP_INTEGRAL_DOMAIN»
  DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL := SessionANT.Dedekind.«DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL»
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DVR_IDEAL_MAXIMAL_POW := SessionANT.DedekindStruct.«DVR_IDEAL_MAXIMAL_POW»
  DVR_IFF_LOCAL_DEDEKIND := SessionANT.DedekindStruct.«DVR_IFF_LOCAL_DEDEKIND»
  DVR_IMP_DEDEKIND := SessionANT.DedekindStruct.«DVR_IMP_DEDEKIND»
  EXTENSION := Session.EXTENSION
  FIELD_EQ_TRIVIAL_IDEALS := SessionLibrary.RingTheory.«FIELD_EQ_TRIVIAL_IDEALS»
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  IDEAL_GENERATED_MINIMAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL»
  IDEAL_GENERATED_RING_LOCALIZATION := SessionLibrary.RingTheory.«IDEAL_GENERATED_RING_LOCALIZATION»
  IDEAL_POW_0 := SessionANT.IdealArith.«IDEAL_POW_0»
  IDEAL_POW_EQ_ZERO := SessionANT.IdealArith.«IDEAL_POW_EQ_ZERO»
  IDEAL_POW_SUC := SessionANT.IdealArith.«IDEAL_POW_SUC»
  IDEAL_PROD_LZERO := SessionANT.IdealArith.«IDEAL_PROD_LZERO»
  IDEAL_PROD_MINIMAL := SessionANT.IdealArith.«IDEAL_PROD_MINIMAL»
  IDEAL_PROD_RZERO := SessionANT.IdealArith.«IDEAL_PROD_RZERO»
  IDEAL_VALUATION_EQ_0 := SessionANT.Dedekind.«IDEAL_VALUATION_EQ_0»
  IDEAL_VALUATION_IDEAL_POW := SessionANT.Dedekind.«IDEAL_VALUATION_IDEAL_POW»
  IDEAL_VALUATION_IDEAL_PROD := SessionANT.Dedekind.«IDEAL_VALUATION_IDEAL_PROD»
  IDEAL_VALUATION_PRIME := SessionANT.Dedekind.«IDEAL_VALUATION_PRIME»
  IDEAL_VALUATION_UNIQUE := SessionANT.Dedekind.«IDEAL_VALUATION_UNIQUE»
  IMP_CONJ := Session.IMP_CONJ
  INTEGRALLY_CLOSED_LOCALIZATION := SessionANT.Integral.«INTEGRALLY_CLOSED_LOCALIZATION»
  INTEGRAL_DOMAIN_LOCALIZATION := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_LOCALIZATION»
  INTEGRAL_DOMAIN_REGULAR := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_REGULAR»
  IN_DIFF := Session.IN_DIFF
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_INTER := Session.IN_INTER
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_SING := Session.IN_SING
  LEFT_AND_EXISTS_THM := Session.LEFT_AND_EXISTS_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_REFL := Session.LE_REFL
  LOCAL_RING_LOCALIZATION := SessionLibrary.RingTheory.«LOCAL_RING_LOCALIZATION»
  MAXIMAL_AMONG_PRIME_IDEALS := SessionLibrary.RingTheory.«MAXIMAL_AMONG_PRIME_IDEALS»
  MAXIMAL_IMP_PRIME_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_PRIME_IDEAL»
  MAXIMAL_IMP_RING_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_RING_IDEAL»
  NOETHERIAN_RING_LOCALIZATION := SessionLibrary.RingTheory.«NOETHERIAN_RING_LOCALIZATION»
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  PRIME_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«PRIME_IDEAL_IMP_SUBSET»
  PRIME_IDEAL_LOCALIZATION := SessionLibrary.RingTheory.«PRIME_IDEAL_LOCALIZATION»
  PRIME_IDEAL_LOCALIZATION_CONTRACTION := SessionLibrary.RingTheory.«PRIME_IDEAL_LOCALIZATION_CONTRACTION»
  PRIME_IDEAL_LOCALIZATION_EXISTS := SessionLibrary.RingTheory.«PRIME_IDEAL_LOCALIZATION_EXISTS»
  PRIME_IMP_PROPER_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_PROPER_IDEAL»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PROPER_IDEAL_LOCALIZATION := SessionLibrary.RingTheory.«PROPER_IDEAL_LOCALIZATION»
  PSUBSET := Session.PSUBSET
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_1_IN_MULTSYS := SessionLibrary.RingTheory.«RING_1_IN_MULTSYS»
  RING_FRACTIONATE_IN_CARRIER := SessionLibrary.RingTheory.«RING_FRACTIONATE_IN_CARRIER»
  RING_HOMOMORPHISM_FRACTIONATE := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_FRACTIONATE»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_IDEAL_0 := SessionLibrary.RingTheory.«RING_IDEAL_0»
  RING_IDEAL_IDEAL_POW := SessionANT.IdealArith.«RING_IDEAL_IDEAL_POW»
  RING_IDEAL_IDEAL_PROD := SessionANT.IdealArith.«RING_IDEAL_IDEAL_PROD»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_IDEAL_LOCALIZATION := SessionLibrary.RingTheory.«RING_IDEAL_LOCALIZATION»
  RING_LOCALEQUIV_EQ_0_GEN := SessionLibrary.RingTheory.«RING_LOCALEQUIV_EQ_0_GEN»
  RING_LOCALIZATION_0 := SessionLibrary.RingTheory.«RING_LOCALIZATION_0»
  RING_LOCALIZATION_CARRIER := SessionLibrary.RingTheory.«RING_LOCALIZATION_CARRIER»
  RING_LOCALIZATION_MUL := SessionLibrary.RingTheory.«RING_LOCALIZATION_MUL»
  RING_LOCALIZATION_PRIME_IDEAL_CORRESPONDENCE := SessionLibrary.RingTheory.«RING_LOCALIZATION_PRIME_IDEAL_CORRESPONDENCE»
  RING_MULTSYS := SessionLibrary.RingTheory.«RING_MULTSYS»
  RING_MULTSYS_NONPRIME := SessionLibrary.RingTheory.«RING_MULTSYS_NONPRIME»
  RING_MUL_IN_IDEAL_PROD := SessionANT.IdealArith.«RING_MUL_IN_IDEAL_PROD»
  RING_MUL_IN_MULTSYS := SessionLibrary.RingTheory.«RING_MUL_IN_MULTSYS»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_REGULAR_MUL_EQ_0 := SessionANT.Integral.«RING_REGULAR_MUL_EQ_0»
  RING_SETMUL := SessionLibrary.RingTheory.«RING_SETMUL»
  SING_SUBSET := Session.SING_SUBSET
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUBSET_REFL := Session.SUBSET_REFL
  dedekind_domain := SessionANT.Dedekind.«dedekind_domain»
  ideal_prod := SessionANT.IdealArith.«ideal_prod»
  maximal_ideal := SessionLibrary.RingTheory.«maximal_ideal»
  proper_ideal := SessionLibrary.RingTheory.«proper_ideal»
  ring_fractionate := SessionLibrary.RingTheory.«ring_fractionate»
  ring_setmul := SessionLibrary.RingTheory.«ring_setmul»

/-- What dedekind_local.ml uses from Session. -/
def deps : HolANT.DedekindLocal.DedekindLocalDeps where
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

/- The bundles, in dedekind_local.ml order. -/
initialize BDedekindLocal : HolANT.DedekindLocal.DedekindLocal ←
  ioB "setupDedekindLocal" (HolANT.DedekindLocal.setupDedekindLocal deps).run

-- DedekindLocal
def MAXIMAL_IDEAL_LOCALIZATION : thm := BDedekindLocal.MAXIMAL_IDEAL_LOCALIZATION
def IDEAL_LOCALIZATION_EQ_ZERO : thm := BDedekindLocal.IDEAL_LOCALIZATION_EQ_ZERO
def IDEAL_PROD_LOCALIZATION : thm := BDedekindLocal.IDEAL_PROD_LOCALIZATION
def IDEAL_POW_LOCALIZATION : thm := BDedekindLocal.IDEAL_POW_LOCALIZATION
def DEDEKIND_LOCALIZATION : thm := BDedekindLocal.DEDEKIND_LOCALIZATION
def DVR_LOCALIZATION : thm := BDedekindLocal.DVR_LOCALIZATION
def IDEAL_VALUATION_LOCALIZATION : thm := BDedekindLocal.IDEAL_VALUATION_LOCALIZATION
def DEDEKIND_LOCALIZATION_IDEAL_POW : thm := BDedekindLocal.DEDEKIND_LOCALIZATION_IDEAL_POW

/-- `needs "ANT/dedekind_local.ml"`: already done by importing this module. -/
def ensureDedekindLocal : IO Unit := pure ()

end SessionANT.DedekindLocal
