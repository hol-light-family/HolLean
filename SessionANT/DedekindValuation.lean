/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/dedekind_valuation.ml                         . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/DedekindValuation.lean

  The session half of the dedekind_valuation.ml translation: it supplies HolANT.DedekindValuation's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/dedekind_valuation.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.DedekindValuation
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
import SessionANT.DedekindLocal

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.DedekindValuation

/-- The core theorems dedekind_valuation.ml uses. -/
def core1 : HolANT.DedekindValuation.CoreThms1 where
  AND_FORALL_THM := Session.AND_FORALL_THM
  CONJ_ASSOC := Session.CONJ_ASSOC
  DEDEKIND_IDEAL_EQ_VALUATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_EQ_VALUATION»
  DEDEKIND_IDEAL_FACTORIZATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_FACTORIZATION»
  DEDEKIND_IDEAL_SUBSET_VALUATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_SUBSET_VALUATION»
  DEDEKIND_IMP_INTEGRAL_DOMAIN := SessionANT.Dedekind.«DEDEKIND_IMP_INTEGRAL_DOMAIN»
  DEDEKIND_IN_IDEAL_POW_VALUATION := SessionANT.Dedekind.«DEDEKIND_IN_IDEAL_POW_VALUATION»
  DEDEKIND_LOCALIZATION := SessionANT.DedekindLocal.«DEDEKIND_LOCALIZATION»
  DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL := SessionANT.Dedekind.«DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL»
  DEDEKIND_WEAK_APPROXIMATION := SessionANT.DedekindStruct.«DEDEKIND_WEAK_APPROXIMATION»
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DVR := SessionANT.DedekindStruct.«DVR»
  DVR_IFF_LOCAL_DEDEKIND := SessionANT.DedekindStruct.«DVR_IFF_LOCAL_DEDEKIND»
  DVR_LOCALIZATION := SessionANT.DedekindLocal.«DVR_LOCALIZATION»
  EQ_TRANS := Session.EQ_TRANS
  EXISTS_UNIQUE_DEF := Session.EXISTS_UNIQUE_DEF
  EXTENSION := Session.EXTENSION
  FIELD_EQ_TRIVIAL_IDEALS := SessionLibrary.RingTheory.«FIELD_EQ_TRIVIAL_IDEALS»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_INV_EQ_0 := SessionLibrary.RingTheory.«FIELD_INV_EQ_0»
  FIELD_MUL_EQ_0 := SessionLibrary.RingTheory.«FIELD_MUL_EQ_0»
  FIELD_MUL_LINV := SessionLibrary.RingTheory.«FIELD_MUL_LINV»
  FIELD_MUL_RINV := SessionLibrary.RingTheory.«FIELD_MUL_RINV»
  FIELD_NONTRIVIAL := SessionLibrary.RingTheory.«FIELD_NONTRIVIAL»
  FIELD_POW_EQ_0 := SessionLibrary.RingTheory.«FIELD_POW_EQ_0»
  FIELD_UNIT := SessionLibrary.RingTheory.«FIELD_UNIT»
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_SUBSET := Session.FINITE_SUBSET
  FINITE_UNION := Session.FINITE_UNION
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FRACTION_FIELD_COMMON_DENOMINATOR := SessionLibrary.RingTheory.«FRACTION_FIELD_COMMON_DENOMINATOR»
  FRACTION_FIELD_MAP := SessionLibrary.RingTheory.«FRACTION_FIELD_MAP»
  IDEALS_GENERATED_SING_EQ := SessionLibrary.RingTheory.«IDEALS_GENERATED_SING_EQ»
  IDEAL_GENERATED_EQ_0 := SessionLibrary.RingTheory.«IDEAL_GENERATED_EQ_0»
  IDEAL_GENERATED_MINIMAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL»
  IDEAL_GENERATED_MINIMAL_EQ := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL_EQ»
  IDEAL_GENERATED_RING_LOCALIZATION := SessionLibrary.RingTheory.«IDEAL_GENERATED_RING_LOCALIZATION»
  IDEAL_GENERATED_SING_EQ_CARRIER := SessionLibrary.RingTheory.«IDEAL_GENERATED_SING_EQ_CARRIER»
  IDEAL_LOCALIZATION_EQ_ZERO := SessionANT.DedekindLocal.«IDEAL_LOCALIZATION_EQ_ZERO»
  IDEAL_POW_1 := SessionANT.IdealArith.«IDEAL_POW_1»
  IDEAL_POW_EQ_ZERO := SessionANT.IdealArith.«IDEAL_POW_EQ_ZERO»
  IDEAL_POW_PRINCIPAL := SessionANT.IdealArith.«IDEAL_POW_PRINCIPAL»
  IDEAL_PRODUCT_EQ_ZERO := SessionANT.IdealArith.«IDEAL_PRODUCT_EQ_ZERO»
  IDEAL_PROD_EQ_ZERO := SessionANT.IdealArith.«IDEAL_PROD_EQ_ZERO»
  IDEAL_VALUATION_CARRIER := SessionANT.Dedekind.«IDEAL_VALUATION_CARRIER»
  IDEAL_VALUATION_EQ_0 := SessionANT.Dedekind.«IDEAL_VALUATION_EQ_0»
  IDEAL_VALUATION_FINITE_SUPPORT := SessionANT.Dedekind.«IDEAL_VALUATION_FINITE_SUPPORT»
  IDEAL_VALUATION_IDEAL_POW := SessionANT.Dedekind.«IDEAL_VALUATION_IDEAL_POW»
  IDEAL_VALUATION_IDEAL_PROD := SessionANT.Dedekind.«IDEAL_VALUATION_IDEAL_PROD»
  IDEAL_VALUATION_IDEAL_PRODUCT_MONOMIAL := SessionANT.Dedekind.«IDEAL_VALUATION_IDEAL_PRODUCT_MONOMIAL»
  IDEAL_VALUATION_LOCALIZATION := SessionANT.DedekindLocal.«IDEAL_VALUATION_LOCALIZATION»
  IDEAL_VALUATION_PRIME := SessionANT.Dedekind.«IDEAL_VALUATION_PRIME»
  IDEAL_VALUATION_PRINCIPAL_ADD := SessionANT.Dedekind.«IDEAL_VALUATION_PRINCIPAL_ADD»
  IDEAL_VALUATION_PRINCIPAL_MUL := SessionANT.Dedekind.«IDEAL_VALUATION_PRINCIPAL_MUL»
  IDEAL_VALUATION_SETADD := SessionANT.Dedekind.«IDEAL_VALUATION_SETADD»
  IMAGE_CLAUSES := Session.IMAGE_CLAUSES
  IMP_CONJ := Session.IMP_CONJ
  IMP_CONJ_ALT := Session.IMP_CONJ_ALT
  IMP_IMP := Session.IMP_IMP
  INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING»
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  INTEGRAL_DOMAIN_MUL_LCANCEL := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_LCANCEL»
  INTEGRAL_DOMAIN_POW_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_POW_EQ_0»
  INTEGRAL_DOMAIN_REGULAR := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_REGULAR»
  INTER := Session.INTER
  INT_ADD_LID := Session.INT_ADD_LID
  INT_ADD_RINV := Session.INT_ADD_RINV
  INT_LE_REFL := Session.INT_LE_REFL
  INT_LT_REFL := Session.INT_LT_REFL
  INT_MUL_LZERO := Session.INT_MUL_LZERO
  INT_OF_NUM_ADD := Session.INT_OF_NUM_ADD
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_LE := Session.INT_OF_NUM_LE
  INT_OF_NUM_LT := Session.INT_OF_NUM_LT
  INT_OF_NUM_MIN := Session.INT_OF_NUM_MIN
  INT_OF_NUM_OF_INT := Session.INT_OF_NUM_OF_INT
  INT_OF_NUM_SUC := Session.INT_OF_NUM_SUC
  INT_POS := Session.INT_POS
  INT_SUB_LE := Session.INT_SUB_LE
  INT_SUB_REFL := Session.INT_SUB_REFL
  INT_SUB_RZERO := Session.INT_SUB_RZERO
  IN_DIFF := Session.IN_DIFF
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IDEAL_GENERATED_SING_EQ := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SING_EQ»
  IN_IMAGE := Session.IN_IMAGE
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_SING := Session.IN_SING
  IN_UNION := Session.IN_UNION
  ISOMORPHIC_RING_FIELDNESS := SessionLibrary.RingTheory.«ISOMORPHIC_RING_FIELDNESS»
  ISOMORPHIC_RING_LOCALITY := SessionLibrary.RingTheory.«ISOMORPHIC_RING_LOCALITY»
  ISOMORPHIC_RING_PIDNESS := SessionLibrary.RingTheory.«ISOMORPHIC_RING_PIDNESS»
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LOCALEQUIV_MUL_RCANCEL := SessionLibrary.RingTheory.«LOCALEQUIV_MUL_RCANCEL»
  LT_NZ := Session.LT_NZ
/-- The core theorems dedekind_valuation.ml uses. -/
def core2 : HolANT.DedekindValuation.CoreThms2 where
  MAXIMAL_IDEAL_0 := SessionLibrary.RingTheory.«MAXIMAL_IDEAL_0»
  MAXIMAL_IMP_PRIME_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_PRIME_IDEAL»
  MIN := Session.MIN
  MONOMIAL_RESTRICT_EQ := SessionLibrary.RingTheory.«MONOMIAL_RESTRICT_EQ»
  MONO_EXISTS := Session.MONO_EXISTS
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  PRIME_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«PRIME_IDEAL_IMP_SUBSET»
  PRIME_IDEAL_LOCALIZATION := SessionLibrary.RingTheory.«PRIME_IDEAL_LOCALIZATION»
  PRIME_IMP_PROPER_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_PROPER_IDEAL»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PROPER_IDEAL := SessionLibrary.RingTheory.«PROPER_IDEAL»
  PROPER_IDEAL_ALT := SessionLibrary.RingTheory.«PROPER_IDEAL_ALT»
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RIGHT_IMP_EXISTS_THM := Session.RIGHT_IMP_EXISTS_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_ADD_LZERO := SessionLibrary.RingTheory.«RING_ADD_LZERO»
  RING_ADD_RZERO := SessionLibrary.RingTheory.«RING_ADD_RZERO»
  RING_ASSOCIATES_NEG := SessionLibrary.RingTheory.«RING_ASSOCIATES_NEG»
  RING_ASSOCIATES_REFL := SessionLibrary.RingTheory.«RING_ASSOCIATES_REFL»
  RING_CARRIER_NONEMPTY := SessionLibrary.RingTheory.«RING_CARRIER_NONEMPTY»
  RING_FRACTIONATE_EQ_0_GEN := SessionLibrary.RingTheory.«RING_FRACTIONATE_EQ_0_GEN»
  RING_FRACTIONATE_IN_CARRIER := SessionLibrary.RingTheory.«RING_FRACTIONATE_IN_CARRIER»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_1 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_1»
  RING_HOMOMORPHISM_ADD := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_ADD»
  RING_HOMOMORPHISM_INV := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INV»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_NEG := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_NEG»
  RING_HOMOMORPHISM_SUM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUM_MUL»
  RING_IDEAL_CARRIER := SessionLibrary.RingTheory.«RING_IDEAL_CARRIER»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IDEAL_POW := SessionANT.IdealArith.«RING_IDEAL_IDEAL_POW»
  RING_IDEAL_IDEAL_PROD := SessionANT.IdealArith.«RING_IDEAL_IDEAL_PROD»
  RING_IDEAL_IDEAL_PRODUCT := SessionANT.IdealArith.«RING_IDEAL_IDEAL_PRODUCT»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_IDEAL_SETADD := SessionLibrary.RingTheory.«RING_IDEAL_SETADD»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_ISOMORPHISM_ONTO_IMAGE := SessionLibrary.RingTheory.«RING_ISOMORPHISM_ONTO_IMAGE»
  RING_LOCALEQUIV_EQ_0_GEN := SessionLibrary.RingTheory.«RING_LOCALEQUIV_EQ_0_GEN»
  RING_LOCALEQUIV_IN_CARRIER := SessionLibrary.RingTheory.«RING_LOCALEQUIV_IN_CARRIER»
  RING_LOCALIZATION_CARRIER := SessionLibrary.RingTheory.«RING_LOCALIZATION_CARRIER»
  RING_LOCALIZATION_UNIVERSAL := SessionLibrary.RingTheory.«RING_LOCALIZATION_UNIVERSAL»
  RING_MONOMORPHISM_ALT := SessionLibrary.RingTheory.«RING_MONOMORPHISM_ALT»
  RING_MONOMORPHISM_COMPOSE := SessionLibrary.RingTheory.«RING_MONOMORPHISM_COMPOSE»
  RING_MONOMORPHISM_EQ_0 := SessionLibrary.RingTheory.«RING_MONOMORPHISM_EQ_0»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MONOMORPHISM_INJECTIVE_EQ := SessionLibrary.RingTheory.«RING_MONOMORPHISM_INJECTIVE_EQ»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MULTSYS_IMP_SUBSET := SessionLibrary.RingTheory.«RING_MULTSYS_IMP_SUBSET»
  RING_MULTSYS_NONPRIME := SessionLibrary.RingTheory.«RING_MULTSYS_NONPRIME»
  RING_MUL_ASSOC := SessionLibrary.RingTheory.«RING_MUL_ASSOC»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  RING_NEG_EQ_0 := SessionLibrary.RingTheory.«RING_NEG_EQ_0»
  RING_NEG_NEG := SessionLibrary.RingTheory.«RING_NEG_NEG»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_LMUL := SessionLibrary.RingTheory.«RING_SUM_LMUL»
  RING_UNIT_0 := SessionLibrary.RingTheory.«RING_UNIT_0»
  RING_UNIT_1 := SessionLibrary.RingTheory.«RING_UNIT_1»
  RING_UNIT_IN_CARRIER := SessionLibrary.RingTheory.«RING_UNIT_IN_CARRIER»
  SELECT_UNIQUE := Session.SELECT_UNIQUE
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUBSET_IDEALS_GENERATED_SING := SessionLibrary.RingTheory.«SUBSET_IDEALS_GENERATED_SING»
  SUBSET_REFL := Session.SUBSET_REFL
  TRIVIAL_RING_SUBSET := SessionLibrary.RingTheory.«TRIVIAL_RING_SUBSET»
  field_of_fractions := SessionLibrary.RingTheory.«field_of_fractions»
  free_basis := SessionLibrary.RingDet.«free_basis»
  integral_domain := SessionLibrary.RingTheory.«integral_domain»
  isomorphic_ring := SessionLibrary.RingTheory.«isomorphic_ring»
  local_ring := SessionLibrary.RingTheory.«local_ring»
  monomial := SessionLibrary.RingTheory.«monomial»
  monomial_restrict := SessionLibrary.RingTheory.«monomial_restrict»
  monomial_vars := SessionLibrary.RingTheory.«monomial_vars»
  o_THM := Session.o_THM
  prime_ideal := SessionLibrary.RingTheory.«prime_ideal»
  proper_ideal := SessionLibrary.RingTheory.«proper_ideal»
  ring_div := SessionLibrary.RingTheory.«ring_div»
  ring_divides := SessionLibrary.RingTheory.«ring_divides»
  ring_image := SessionLibrary.RingTheory.«ring_image»
  ring_pow := SessionLibrary.RingTheory.«ring_pow»
  ring_setadd := SessionLibrary.RingTheory.«ring_setadd»
  ring_unit := SessionLibrary.RingTheory.«ring_unit»

/-- What dedekind_valuation.ml uses from Session. -/
def deps : HolANT.DedekindValuation.DedekindValuationDeps where
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
  SELECT_CONV t := pure (Session.SELECT_CONV t)
  core1 := core1
  core2 := core2

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in dedekind_valuation.ml order. -/
initialize BDedekindValuation01 : HolANT.DedekindValuation.DedekindValuation01 ←
  ioB "setupDedekindValuation01" (HolANT.DedekindValuation.setupDedekindValuation01 deps).run
initialize BDedekindValuation02 : HolANT.DedekindValuation.DedekindValuation02 ←
  ioB "setupDedekindValuation02" (HolANT.DedekindValuation.setupDedekindValuation02 deps BDedekindValuation01).run
initialize BDedekindValuation03 : HolANT.DedekindValuation.DedekindValuation03 ←
  ioB "setupDedekindValuation03" (HolANT.DedekindValuation.setupDedekindValuation03 deps).run

-- DedekindValuation01
def dedekind_valuation : thm := BDedekindValuation01.dedekind_valuation
def DEDEKIND_VALUATION : thm := BDedekindValuation01.DEDEKIND_VALUATION
def DEDEKIND_VALUATION_IMAGE : thm := BDedekindValuation01.DEDEKIND_VALUATION_IMAGE
def DEDEKIND_VALUATION_1 : thm := BDedekindValuation01.DEDEKIND_VALUATION_1
def FIELD_FRACTION_NONZERO : thm := BDedekindValuation01.FIELD_FRACTION_NONZERO
def DEDEKIND_VALUATION_MUL : thm := BDedekindValuation01.DEDEKIND_VALUATION_MUL
def DEDEKIND_VALUATION_INV : thm := BDedekindValuation01.DEDEKIND_VALUATION_INV
def DEDEKIND_VALUATION_DIV : thm := BDedekindValuation01.DEDEKIND_VALUATION_DIV
def DEDEKIND_VALUATION_POW : thm := BDedekindValuation01.DEDEKIND_VALUATION_POW
def DEDEKIND_VALUATION_NEG : thm := BDedekindValuation01.DEDEKIND_VALUATION_NEG
def DEDEKIND_VALUATION_COMPATIBLE : thm := BDedekindValuation01.DEDEKIND_VALUATION_COMPATIBLE
def DEDEKIND_VALUATION_ADD : thm := BDedekindValuation01.DEDEKIND_VALUATION_ADD
def DEDEKIND_VALUATION_ADD_STRICT : thm := BDedekindValuation01.DEDEKIND_VALUATION_ADD_STRICT
def DEDEKIND_VALUATION_FINITE : thm := BDedekindValuation01.DEDEKIND_VALUATION_FINITE
def DEDEKIND_VALUATION_INTEGRAL : thm := BDedekindValuation01.DEDEKIND_VALUATION_INTEGRAL
def DEDEKIND_VALUATION_UNIT : thm := BDedekindValuation01.DEDEKIND_VALUATION_UNIT
def DEDEKIND_VALUATION_PRIME_IDEAL : thm := BDedekindValuation01.DEDEKIND_VALUATION_PRIME_IDEAL
def DEDEKIND_VALUATION_EQ : thm := BDedekindValuation01.DEDEKIND_VALUATION_EQ
def DEDEKIND_IDEAL_PRESCRIBED_VALUATIONS : thm := BDedekindValuation01.DEDEKIND_IDEAL_PRESCRIBED_VALUATIONS
def ideal_of_valuations : thm := BDedekindValuation01.ideal_of_valuations
def IDEAL_OF_VALUATIONS : thm := BDedekindValuation01.IDEAL_OF_VALUATIONS
def IDEAL_OF_VALUATIONS_UNIQUE : thm := BDedekindValuation01.IDEAL_OF_VALUATIONS_UNIQUE
def IDEAL_OF_VALUATIONS_ADD : thm := BDedekindValuation01.IDEAL_OF_VALUATIONS_ADD
def IDEAL_OF_VALUATIONS_0 : thm := BDedekindValuation01.IDEAL_OF_VALUATIONS_0
def IDEAL_OF_VALUATIONS_EQ : thm := BDedekindValuation01.IDEAL_OF_VALUATIONS_EQ
def DEDEKIND_VALUATION_WEAK_APPROXIMATION : thm := BDedekindValuation01.DEDEKIND_VALUATION_WEAK_APPROXIMATION

-- DedekindValuation02
def DEDEKIND_VALUATION_APPROXIMATION : thm := BDedekindValuation02.DEDEKIND_VALUATION_APPROXIMATION
def DEDEKIND_DENOMINATOR_IDEAL : thm := BDedekindValuation02.DEDEKIND_DENOMINATOR_IDEAL
def DEDEKIND_IDEAL_MUL_INTEGRAL : thm := BDedekindValuation02.DEDEKIND_IDEAL_MUL_INTEGRAL
def DEDEKIND_VALUATION_POS : thm := BDedekindValuation02.DEDEKIND_VALUATION_POS
def DEDEKIND_VALUATION_RING_LOCALIZATION : thm := BDedekindValuation02.DEDEKIND_VALUATION_RING_LOCALIZATION
def DEDEKIND_VALUATION_LOCALIZATION : thm := BDedekindValuation02.DEDEKIND_VALUATION_LOCALIZATION
def ISOMORPHIC_RING_DVR : thm := BDedekindValuation02.ISOMORPHIC_RING_DVR
def DEDEKIND_VALUATION_RING_DVR : thm := BDedekindValuation02.DEDEKIND_VALUATION_RING_DVR
def DVR_DEDEKIND_VALUATION : thm := BDedekindValuation02.DVR_DEDEKIND_VALUATION
def DEDEKIND_UNIFORMIZER_CRITERION : thm := BDedekindValuation02.DEDEKIND_UNIFORMIZER_CRITERION

-- DedekindValuation03
def FREE_BASIS_FRACTION_FIELD_MAP : thm := BDedekindValuation03.FREE_BASIS_FRACTION_FIELD_MAP

/-- `needs "ANT/dedekind_valuation.ml"`: already done by importing this module. -/
def ensureDedekindValuation : IO Unit := pure ()

end SessionANT.DedekindValuation
