/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/dedekind_criteria.ml                          . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/DedekindCriteria.lean

  The session half of the dedekind_criteria.ml translation: it supplies HolANT.DedekindCriteria's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/dedekind_criteria.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.DedekindCriteria
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
import SessionANT.DedekindLocal
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
import SessionLibrary.RingGroups
import SessionANT.DedekindValuation
import SessionLibrary.Isum
import SessionANT.IdealNorm
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.RingOfIntegers
import SessionANT.NormIndex
import SessionANT.Classgroup
import SessionANT.ClassgroupGroup
import SessionANT.FractionalIdeals

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.DedekindCriteria

/-- The core theorems dedekind_criteria.ml uses. -/
def core1 : HolANT.DedekindCriteria.CoreThms1 where
  DEDEKIND_FRACTIONAL_IDEAL_MUL_INV := SessionANT.FractionalIdeals.«DEDEKIND_FRACTIONAL_IDEAL_MUL_INV»
  DEDEKIND_IDEAL_EQ_VALUATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_EQ_VALUATION»
  DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE := SessionANT.Dedekind.«DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE»
  DEDEKIND_IMP_INTEGRAL_DOMAIN := SessionANT.Dedekind.«DEDEKIND_IMP_INTEGRAL_DOMAIN»
  DEDEKIND_IMP_NOETHERIAN := SessionANT.Dedekind.«DEDEKIND_IMP_NOETHERIAN»
  DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL := SessionANT.Dedekind.«DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL»
  DEDEKIND_WEAK_APPROXIMATION := SessionANT.DedekindStruct.«DEDEKIND_WEAK_APPROXIMATION»
  DVR := SessionANT.DedekindStruct.«DVR»
  DVR_IMP_DEDEKIND := SessionANT.DedekindStruct.«DVR_IMP_DEDEKIND»
  DVR_LOCALIZATION := SessionANT.DedekindLocal.«DVR_LOCALIZATION»
  EMPTY_GSPEC := Session.EMPTY_GSPEC
  EMPTY_SUBSET := Session.EMPTY_SUBSET
  EQ_TRANS := Session.EQ_TRANS
  FIELD_OF_FRACTIONS_IMP_MONOMORPHISM := SessionLibrary.RingTheory.«FIELD_OF_FRACTIONS_IMP_MONOMORPHISM»
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FRACTIONAL_IDEAL_FRACTIONAL_IDEAL_INV := SessionANT.FractionalIdeals.«FRACTIONAL_IDEAL_FRACTIONAL_IDEAL_INV»
  FRACTIONAL_IDEAL_SCALED_IDEAL := SessionANT.FractionalIdeals.«FRACTIONAL_IDEAL_SCALED_IDEAL»
  FRACTIONAL_IDEAL_SCALED_IDEAL_MUL := SessionANT.FractionalIdeals.«FRACTIONAL_IDEAL_SCALED_IDEAL_MUL»
  FUN_IN_IMAGE := Session.FUN_IN_IMAGE
  IDEAL_GENERATED_EMPTY := SessionLibrary.RingTheory.«IDEAL_GENERATED_EMPTY»
  IDEAL_GENERATED_EQ_0 := SessionLibrary.RingTheory.«IDEAL_GENERATED_EQ_0»
  IDEAL_GENERATED_INC := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC»
  IDEAL_GENERATED_MINIMAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL»
  IDEAL_GENERATED_SING := SessionLibrary.RingTheory.«IDEAL_GENERATED_SING»
  IDEAL_GENERATED_SUBSET := SessionLibrary.RingTheory.«IDEAL_GENERATED_SUBSET»
  IDEAL_PROD_AC := SessionANT.IdealArith.«IDEAL_PROD_AC»
  IDEAL_PROD_CARRIER := SessionANT.IdealArith.«IDEAL_PROD_CARRIER»
  IDEAL_PROD_COMM := SessionANT.IdealArith.«IDEAL_PROD_COMM»
  IDEAL_PROD_EXPLICIT := SessionANT.IdealArith.«IDEAL_PROD_EXPLICIT»
  IDEAL_PROD_MONO := SessionANT.IdealArith.«IDEAL_PROD_MONO»
  IDEAL_PROD_PRINCIPAL_CANCEL := SessionANT.IdealArith.«IDEAL_PROD_PRINCIPAL_CANCEL»
  IDEAL_PROD_SCALE := SessionANT.IdealArith.«IDEAL_PROD_SCALE»
  IDEAL_PROD_SUBSET_LEFT := SessionANT.IdealArith.«IDEAL_PROD_SUBSET_LEFT»
  IDEAL_PROD_SUBSET_PRIME_IDEAL := SessionANT.IdealArith.«IDEAL_PROD_SUBSET_PRIME_IDEAL»
  IMAGE_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«IMAGE_HOMOMORPHISM_MUL»
  IMAGE_o := Session.IMAGE_o
  IMP_IMP := Session.IMP_IMP
  INTEGRALLY_CLOSED_ALT := SessionANT.Integral.«INTEGRALLY_CLOSED_ALT»
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  INTEGRAL_DOMAIN_MUL_LCANCEL := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_LCANCEL»
  INTEGRAL_DOMAIN_MUL_RCANCEL := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_RCANCEL»
  INTEGRAL_DOMAIN_NONTRIVIAL := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_NONTRIVIAL»
  INTEGRAL_DOMAIN_POW_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_POW_EQ_0»
  INTEGRAL_DOMAIN_REGULAR := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_REGULAR»
  INTEGRAL_HOMOGENEOUS_HOMOMORPHIC_IMAGE := SessionANT.Integral.«INTEGRAL_HOMOGENEOUS_HOMOMORPHIC_IMAGE»
  IN_DIFF := Session.IN_DIFF
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IDEAL_GENERATED_SELF := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SELF»
  IN_IMAGE := Session.IN_IMAGE
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_RING_IDEAL_ADD := SessionLibrary.RingTheory.«IN_RING_IDEAL_ADD»
  IN_RING_IDEAL_LMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_LMUL»
  IN_RING_IDEAL_NEG := SessionLibrary.RingTheory.«IN_RING_IDEAL_NEG»
  IN_RING_IDEAL_SUM := SessionLibrary.RingTheory.«IN_RING_IDEAL_SUM»
  LEFT_AND_EXISTS_THM := Session.LEFT_AND_EXISTS_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_0 := Session.LE_0
  LT := Session.LT
  MAXIMAL_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«MAXIMAL_IDEAL_IMP_SUBSET»
  MAXIMAL_IMP_PRIME_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_PRIME_IDEAL»
  MAXIMAL_IMP_PROPER_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_PROPER_IDEAL»
  MAXIMAL_IMP_RING_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_RING_IDEAL»
  MAXIMAL_SUPERIDEAL_EXISTS := SessionLibrary.RingTheory.«MAXIMAL_SUPERIDEAL_EXISTS»
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  PID := SessionLibrary.RingTheory.«PID»
  PID_IMP_INTEGRALLY_CLOSED := SessionANT.Integral.«PID_IMP_INTEGRALLY_CLOSED»
  PRIME_IDEAL_LOCALIZATION := SessionLibrary.RingTheory.«PRIME_IDEAL_LOCALIZATION»
  PRIME_IMP_PROPER_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_PROPER_IDEAL»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PRINCIPAL_IDEAL_0 := SessionLibrary.RingTheory.«PRINCIPAL_IDEAL_0»
  PROPER_IDEAL_ALT := SessionLibrary.RingTheory.«PROPER_IDEAL_ALT»
  PSUBSET := Session.PSUBSET
  RIGHT_EXISTS_IMP_THM := Session.RIGHT_EXISTS_IMP_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_ADD_LDISTRIB := SessionLibrary.RingTheory.«RING_ADD_LDISTRIB»
  RING_ADD_RDISTRIB := SessionLibrary.RingTheory.«RING_ADD_RDISTRIB»
  RING_ADD_RZERO := SessionLibrary.RingTheory.«RING_ADD_RZERO»
  RING_DIVIDES_0 := SessionLibrary.RingTheory.«RING_DIVIDES_0»
  RING_DIVIDES_ADD := SessionLibrary.RingTheory.«RING_DIVIDES_ADD»
  RING_DIVIDES_LMUL := SessionLibrary.RingTheory.«RING_DIVIDES_LMUL»
  RING_DIVIDES_REFL := SessionLibrary.RingTheory.«RING_DIVIDES_REFL»
  RING_DIVIDES_RMUL := SessionLibrary.RingTheory.«RING_DIVIDES_RMUL»
  RING_FRACTIONATE_IN_CARRIER := SessionLibrary.RingTheory.«RING_FRACTIONATE_IN_CARRIER»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_1 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_1»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_IDEAL := SessionLibrary.RingTheory.«RING_IDEAL»
  RING_IDEAL_CARRIER := SessionLibrary.RingTheory.«RING_IDEAL_CARRIER»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IDEAL_PROD := SessionANT.IdealArith.«RING_IDEAL_IDEAL_PROD»
  RING_IDEAL_IMP_FRACTIONAL_IDEAL := SessionANT.FractionalIdeals.«RING_IDEAL_IMP_FRACTIONAL_IDEAL»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_LOCALEQUIV := SessionLibrary.RingTheory.«RING_LOCALEQUIV»
  RING_LOCALEQUIV_EQUIV := SessionLibrary.RingTheory.«RING_LOCALEQUIV_EQUIV»
  RING_LOCALEQUIV_IN_LOCALIZED_IDEAL := SessionLibrary.RingTheory.«RING_LOCALEQUIV_IN_LOCALIZED_IDEAL»
  RING_LOCALIZATION_CARRIER := SessionLibrary.RingTheory.«RING_LOCALIZATION_CARRIER»
  RING_LOCALIZATION_MUL := SessionLibrary.RingTheory.«RING_LOCALIZATION_MUL»
  RING_MONOMORPHISM_EQ_0 := SessionLibrary.RingTheory.«RING_MONOMORPHISM_EQ_0»
  RING_MONOMORPHISM_FRACTIONATE_GEN := SessionLibrary.RingTheory.«RING_MONOMORPHISM_FRACTIONATE_GEN»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MONOMORPHISM_INJECTIVE_EQ := SessionLibrary.RingTheory.«RING_MONOMORPHISM_INJECTIVE_EQ»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MULTSYS_NONPRIME := SessionLibrary.RingTheory.«RING_MULTSYS_NONPRIME»
  RING_MUL_ASSOC := SessionLibrary.RingTheory.«RING_MUL_ASSOC»
  RING_MUL_IN_IDEAL_PROD := SessionANT.IdealArith.«RING_MUL_IN_IDEAL_PROD»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_MUL_SYM := SessionLibrary.RingTheory.«RING_MUL_SYM»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_EQ_0 := SessionLibrary.RingTheory.«RING_SUB_EQ_0»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_CLAUSES := SessionLibrary.RingTheory.«RING_SUM_CLAUSES»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_LMUL := SessionLibrary.RingTheory.«RING_SUM_LMUL»
  RING_SUM_RMUL := SessionLibrary.RingTheory.«RING_SUM_RMUL»
  SKOLEM_THM := Session.SKOLEM_THM
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUBSET_REFL := Session.SUBSET_REFL
  SUBSET_TRANS := Session.SUBSET_TRANS
  SUB_0 := Session.SUB_0
  SUB_REFL := Session.SUB_REFL
  dedekind_domain := SessionANT.Dedekind.«dedekind_domain»
  finitely_generated_ideal := SessionLibrary.RingTheory.«finitely_generated_ideal»
  ideal_prod := SessionANT.IdealArith.«ideal_prod»
  maximal_ideal := SessionLibrary.RingTheory.«maximal_ideal»
  noetherian_ring := SessionLibrary.RingTheory.«noetherian_ring»
  num_CASES := Session.num_CASES
  o_DEF := Session.o_DEF
  principal_ideal := SessionLibrary.RingTheory.«principal_ideal»
  ring_divides := SessionLibrary.RingTheory.«ring_divides»
  ring_fractionate := SessionLibrary.RingTheory.«ring_fractionate»
  ring_multsys := SessionLibrary.RingTheory.«ring_multsys»
  ring_pow := SessionLibrary.RingTheory.«ring_pow»

/-- What dedekind_criteria.ml uses from Session. -/
def deps : HolANT.DedekindCriteria.DedekindCriteriaDeps where
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

/- The bundles, in dedekind_criteria.ml order. -/
initialize BDedekindCriteria01 : HolANT.DedekindCriteria.DedekindCriteria01 ←
  ioB "setupDedekindCriteria01" (HolANT.DedekindCriteria.setupDedekindCriteria01 deps).run
initialize BDedekindCriteria02 : HolANT.DedekindCriteria.DedekindCriteria02 ←
  ioB "setupDedekindCriteria02" (HolANT.DedekindCriteria.setupDedekindCriteria02 deps BDedekindCriteria01).run

-- DedekindCriteria01
def DEDEKIND_SEMILOCAL_IMP_PID : thm := BDedekindCriteria01.DEDEKIND_SEMILOCAL_IMP_PID
def INVERTIBLE_IDEAL_DIVIDES : thm := BDedekindCriteria01.INVERTIBLE_IDEAL_DIVIDES
def RING_HOMOGENEOUS_RELATION_IDEAL : thm := BDedekindCriteria01.RING_HOMOGENEOUS_RELATION_IDEAL
def INVERTIBLE_IDEALS_IMP_INTEGRALLY_CLOSED : thm := BDedekindCriteria01.INVERTIBLE_IDEALS_IMP_INTEGRALLY_CLOSED
def INVERTIBLE_IDEALS_IMP_NOETHERIAN : thm := BDedekindCriteria01.INVERTIBLE_IDEALS_IMP_NOETHERIAN
def INVERTIBLE_IDEAL_PROD_CANCEL : thm := BDedekindCriteria01.INVERTIBLE_IDEAL_PROD_CANCEL
def INVERTIBLE_IDEALS_PRIME_IMP_MAXIMAL : thm := BDedekindCriteria01.INVERTIBLE_IDEALS_PRIME_IMP_MAXIMAL
def DEDEKIND_EQ_IDEALS_INVERTIBLE : thm := BDedekindCriteria01.DEDEKIND_EQ_IDEALS_INVERTIBLE
def DEDEKIND_EQ_FRACTIONAL_IDEALS_INVERTIBLE : thm := BDedekindCriteria01.DEDEKIND_EQ_FRACTIONAL_IDEALS_INVERTIBLE
def INTEGRAL_DOMAIN_FRACTIONATE_PRIME_MONOMORPHISM : thm := BDedekindCriteria01.INTEGRAL_DOMAIN_FRACTIONATE_PRIME_MONOMORPHISM
def LOCALLY_DVR_PRIME_IMP_MAXIMAL : thm := BDedekindCriteria01.LOCALLY_DVR_PRIME_IMP_MAXIMAL

-- DedekindCriteria02
def LOCALLY_DVR_IMP_INTEGRALLY_CLOSED : thm := BDedekindCriteria02.LOCALLY_DVR_IMP_INTEGRALLY_CLOSED
def DEDEKIND_EQ_LOCALIZATIONS_DVR : thm := BDedekindCriteria02.DEDEKIND_EQ_LOCALIZATIONS_DVR

/-- `needs "ANT/dedekind_criteria.ml"`: already done by importing this module. -/
def ensureDedekindCriteria : IO Unit := pure ()

end SessionANT.DedekindCriteria
