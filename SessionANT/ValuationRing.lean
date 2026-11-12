/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/valuation_ring.ml                             . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/ValuationRing.lean

  The session half of the valuation_ring.ml translation: it supplies HolANT.ValuationRing's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/valuation_ring.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.ValuationRing
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
import SessionANT.DedekindValuation

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.ValuationRing

/-- The core theorems valuation_ring.ml uses. -/
def core1 : HolANT.ValuationRing.CoreThms1 where
  ADD_CLAUSES := Session.ADD_CLAUSES
  ADD_SUB := Session.ADD_SUB
  ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD := SessionLibrary.FieldTheory.«ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD»
  BEZOUT_RING_2 := SessionLibrary.RingTheory.«BEZOUT_RING_2»
  CARRIER_SUBFIELD_GENERATED_SUBFIELD := SessionLibrary.FieldTheory.«CARRIER_SUBFIELD_GENERATED_SUBFIELD»
  CARRIER_SUBRING_GENERATED_SUBRING := SessionLibrary.RingTheory.«CARRIER_SUBRING_GENERATED_SUBRING»
  CARRIER_SUBRING_OF := SessionLibrary.RingTheory.«CARRIER_SUBRING_OF»
  COEFF_ABOVE_DEG := SessionLibrary.RingTheory.«COEFF_ABOVE_DEG»
  COEFF_COMPOSE := SessionLibrary.RingTheory.«COEFF_COMPOSE»
  COEFF_IN_CARRIER_ALT := SessionLibrary.RingTheory.«COEFF_IN_CARRIER_ALT»
  DEDEKIND_VALUATION_INV := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_INV»
  DEDEKIND_VALUATION_RING_LOCALIZATION := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_RING_LOCALIZATION»
  DVR := SessionANT.DedekindStruct.«DVR»
  DVR_IDEALS_TOTALLY_ORDERED := SessionANT.DedekindStruct.«DVR_IDEALS_TOTALLY_ORDERED»
  DVR_IDEAL_MAXIMAL_POW := SessionANT.DedekindStruct.«DVR_IDEAL_MAXIMAL_POW»
  DVR_IFF_LOCAL_DEDEKIND := SessionANT.DedekindStruct.«DVR_IFF_LOCAL_DEDEKIND»
  EMPTY_GSPEC := Session.EMPTY_GSPEC
  EMPTY_SUBSET := Session.EMPTY_SUBSET
  EQ_SYM_EQ := Session.EQ_SYM_EQ
  EQ_TRANS := Session.EQ_TRANS
  ETA_AX := Session.ETA_AX
  EXISTS_PAIR_THM := Session.EXISTS_PAIR_THM
  EXISTS_UNIQUE := Session.EXISTS_UNIQUE
  EXTENSION := Session.EXTENSION
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_INV_EQ_0 := SessionLibrary.RingTheory.«FIELD_INV_EQ_0»
  FIELD_MUL_LINV := SessionLibrary.RingTheory.«FIELD_MUL_LINV»
  FIELD_MUL_RINV := SessionLibrary.RingTheory.«FIELD_MUL_RINV»
  FIELD_NONTRIVIAL := SessionLibrary.RingTheory.«FIELD_NONTRIVIAL»
  FIELD_POW_EQ_0 := SessionLibrary.RingTheory.«FIELD_POW_EQ_0»
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FIELD_UNIT := SessionLibrary.RingTheory.«FIELD_UNIT»
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_NUMSEG := Session.FINITE_NUMSEG
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_SUBSET_UNIONS_CHAIN := Session.FINITE_SUBSET_UNIONS_CHAIN
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  FST := Session.FST
  IDEAL_GENERATED_ADJOIN_EXPLICIT := SessionLibrary.RingTheory.«IDEAL_GENERATED_ADJOIN_EXPLICIT»
  IDEAL_GENERATED_ADJOIN_INV := SessionLibrary.RingTheory.«IDEAL_GENERATED_ADJOIN_INV»
  IDEAL_GENERATED_ADJOIN_ROOT_UNIT := SessionLibrary.RingTheory.«IDEAL_GENERATED_ADJOIN_ROOT_UNIT»
  IDEAL_GENERATED_EQ_0 := SessionLibrary.RingTheory.«IDEAL_GENERATED_EQ_0»
  IDEAL_GENERATED_EXPLICIT := SessionLibrary.RingTheory.«IDEAL_GENERATED_EXPLICIT»
  IDEAL_GENERATED_INC := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC»
  IDEAL_GENERATED_MINIMAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL»
  IDEAL_GENERATED_MONO := SessionLibrary.RingTheory.«IDEAL_GENERATED_MONO»
  IDEAL_GENERATED_RING_IDEAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_RING_IDEAL»
  IDEAL_POW_PRINCIPAL := SessionANT.IdealArith.«IDEAL_POW_PRINCIPAL»
  IMAGE_I := Session.IMAGE_I
  IMP_CONJ := Session.IMP_CONJ
  IMP_IMP := Session.IMP_IMP
  INSERT_SUBSET := Session.INSERT_SUBSET
  INTEGRALLY_CLOSED_ALT := SessionANT.Integral.«INTEGRALLY_CLOSED_ALT»
  INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING»
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  INTEGRAL_DOMAIN_POW_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_POW_EQ_0»
  INTEGRAL_DOMAIN_QUOTIENT_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_QUOTIENT_RING»
  INTEGRAL_DOMAIN_SUBRING_GENERATED := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_SUBRING_GENERATED»
  INTEGRAL_ELEMENT_EXPLICIT := SessionANT.Integral.«INTEGRAL_ELEMENT_EXPLICIT»
  INTEGRAL_ELEMENT_IMAGE := SessionANT.Integral.«INTEGRAL_ELEMENT_IMAGE»
  INTEGRAL_ELEMENT_IN_ADJOIN_INV := SessionANT.Integral.«INTEGRAL_ELEMENT_IN_ADJOIN_INV»
  INTEGRAL_ELEMENT_OVER_SUBRING := SessionANT.Integral.«INTEGRAL_ELEMENT_OVER_SUBRING»
  IN_CROSS := Session.IN_CROSS
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IDEAL_GENERATED_SELF := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SELF»
  IN_IDEAL_GENERATED_SING := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SING»
  IN_IDEAL_GENERATED_SING_EQ := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SING_EQ»
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_INTER := Session.IN_INTER
  IN_INTERS := Session.IN_INTERS
  IN_NUMSEG := Session.IN_NUMSEG
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_RING_IDEAL_LMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_LMUL»
  IN_RING_IDEAL_RMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_RMUL»
  IN_RING_POLYNOMIAL_CARRIER_COMPOSE := SessionLibrary.RingTheory.«IN_RING_POLYNOMIAL_CARRIER_COMPOSE»
  IN_SING := Session.IN_SING
  IN_SUBFIELD_INV := SessionLibrary.FieldTheory.«IN_SUBFIELD_INV»
  IN_SUBRING_POW := SessionLibrary.RingTheory.«IN_SUBRING_POW»
  IN_UNIONS := Session.IN_UNIONS
  IN_UNIV := Session.IN_UNIV
  I_DEF := Session.I_DEF
  I_THM := Session.I_THM
  LE_0 := Session.LE_0
  LOCAL_RING_MAXIMAL_IDEAL_NONUNITS := SessionLibrary.RingTheory.«LOCAL_RING_MAXIMAL_IDEAL_NONUNITS»
  LT := Session.LT
  MAXIMAL_IDEAL_EXISTS := SessionLibrary.RingTheory.«MAXIMAL_IDEAL_EXISTS»
  MAXIMAL_IMP_PRIME_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_PRIME_IDEAL»
  MAXIMAL_IMP_RING_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_RING_IDEAL»
  MAXIMAL_SUPERIDEAL_EXISTS := SessionLibrary.RingTheory.«MAXIMAL_SUPERIDEAL_EXISTS»
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MONO_EXISTS := Session.MONO_EXISTS
  MONO_OR := Session.MONO_OR
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  PAIR_EQ := Session.PAIR_EQ
  PID_EQ_NOETHERIAN_BEZOUT_DOMAIN := SessionLibrary.RingTheory.«PID_EQ_NOETHERIAN_BEZOUT_DOMAIN»
  PID_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«PID_IMP_INTEGRAL_DOMAIN»
  PID_IMP_NOETHERIAN_RING := SessionLibrary.RingTheory.«PID_IMP_NOETHERIAN_RING»
  POLY_CONST := SessionLibrary.RingTheory.«POLY_CONST»
  POLY_EXTEND_CONST := SessionLibrary.RingTheory.«POLY_EXTEND_CONST»
  POLY_EXTEND_CONST_VARPOW := SessionLibrary.RingTheory.«POLY_EXTEND_CONST_VARPOW»
  POLY_EXTEND_EVALUATE := SessionLibrary.RingTheory.«POLY_EXTEND_EVALUATE»
  POLY_EXTEND_RING_SUM := SessionLibrary.RingTheory.«POLY_EXTEND_RING_SUM»
  POLY_EXTEND_UNIVARIATE := SessionLibrary.RingTheory.«POLY_EXTEND_UNIVARIATE»
  POLY_EXTEND_VAR := SessionLibrary.RingTheory.«POLY_EXTEND_VAR»
/-- The core theorems valuation_ring.ml uses. -/
def core2 : HolANT.ValuationRing.CoreThms2 where
  POLY_TOP_EQ_0 := SessionLibrary.RingTheory.«POLY_TOP_EQ_0»
  POLY_VAR := SessionLibrary.RingTheory.«POLY_VAR»
  PRIME_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«PRIME_IDEAL_IMP_SUBSET»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PROD_RING := SessionLibrary.RingTheory.«PROD_RING»
  PROPER_IDEAL_ALT := SessionLibrary.RingTheory.«PROPER_IDEAL_ALT»
  PROPER_IDEAL_IDEAL_GENERATED_SING := SessionLibrary.RingTheory.«PROPER_IDEAL_IDEAL_GENERATED_SING»
  PSUBSET := Session.PSUBSET
  QUOTIENT_RING_CARRIER := SessionLibrary.RingTheory.«QUOTIENT_RING_CARRIER»
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_ADD_ASSOC := SessionLibrary.RingTheory.«RING_ADD_ASSOC»
  RING_ADD_LDISTRIB := SessionLibrary.RingTheory.«RING_ADD_LDISTRIB»
  RING_ADD_LNEG := SessionLibrary.RingTheory.«RING_ADD_LNEG»
  RING_ADD_RNEG := SessionLibrary.RingTheory.«RING_ADD_RNEG»
  RING_ADD_RZERO := SessionLibrary.RingTheory.«RING_ADD_RZERO»
  RING_DIVIDES_0 := SessionLibrary.RingTheory.«RING_DIVIDES_0»
  RING_DIVIDES_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«RING_DIVIDES_HOMOMORPHIC_IMAGE»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_INCLUSION := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INCLUSION»
  RING_HOMOMORPHISM_PAIRED := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_PAIRED»
  RING_HOMOMORPHISM_POLY_EXTEND := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POLY_EXTEND»
  RING_HOMOMORPHISM_POW := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POW»
  RING_HOMOMORPHISM_RING_COSET := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_COSET»
  RING_HOMOMORPHISM_SUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUM»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_IDEAL_POLY_COMMON_ROOT := SessionLibrary.FieldTheory.«RING_IDEAL_POLY_COMMON_ROOT»
  RING_IDEAL_RING_KERNEL := SessionLibrary.RingTheory.«RING_IDEAL_RING_KERNEL»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_INV_INV := SessionLibrary.RingTheory.«RING_INV_INV»
  RING_INV_MUL := SessionLibrary.RingTheory.«RING_INV_MUL»
  RING_INV_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_INV_SUBFIELD_GENERATED»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_ASSOC := SessionLibrary.RingTheory.«RING_MUL_ASSOC»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_POW := SessionLibrary.RingTheory.«RING_MUL_POW»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  RING_POLYNOMIAL := SessionLibrary.RingTheory.«RING_POLYNOMIAL»
  RING_POLYNOMIAL_CONST := SessionLibrary.RingTheory.«RING_POLYNOMIAL_CONST»
  RING_POLYNOMIAL_MUL := SessionLibrary.RingTheory.«RING_POLYNOMIAL_MUL»
  RING_POLYNOMIAL_POW := SessionLibrary.RingTheory.«RING_POLYNOMIAL_POW»
  RING_POLYNOMIAL_VAR := SessionLibrary.RingTheory.«RING_POLYNOMIAL_VAR»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_1 := SessionLibrary.RingTheory.«RING_POW_1»
  RING_POW_ADD := SessionLibrary.RingTheory.«RING_POW_ADD»
  RING_POW_IN_PRIME_IDEAL := SessionLibrary.RingTheory.«RING_POW_IN_PRIME_IDEAL»
  RING_POW_ONE := SessionLibrary.RingTheory.«RING_POW_ONE»
  RING_POW_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_POW_SUBRING_GENERATED»
  RING_SUB_EQ_0 := SessionLibrary.RingTheory.«RING_SUB_EQ_0»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_ADD := SessionLibrary.RingTheory.«RING_SUM_ADD»
  RING_SUM_CLAUSES := SessionLibrary.RingTheory.«RING_SUM_CLAUSES»
  RING_SUM_CLAUSES_LEFT := SessionLibrary.RingTheory.«RING_SUM_CLAUSES_LEFT»
  RING_SUM_CLAUSES_NUMSEG := SessionLibrary.RingTheory.«RING_SUM_CLAUSES_NUMSEG»
  RING_SUM_CLAUSES_RIGHT := SessionLibrary.RingTheory.«RING_SUM_CLAUSES_RIGHT»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_EQ_GENERAL_INVERSES := SessionLibrary.RingTheory.«RING_SUM_EQ_GENERAL_INVERSES»
  RING_SUM_LMUL := SessionLibrary.RingTheory.«RING_SUM_LMUL»
  RING_SUM_RESTRICT_SET := SessionLibrary.RingTheory.«RING_SUM_RESTRICT_SET»
  RING_SUM_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_SUM_SUBRING_GENERATED»
  RING_UNIT_1 := SessionLibrary.RingTheory.«RING_UNIT_1»
  RING_UNIT_NOT_IN_PRIME_IDEAL := SessionLibrary.RingTheory.«RING_UNIT_NOT_IN_PRIME_IDEAL»
  RING_UNIT_SUBRING_OF_FIELD := SessionLibrary.RingTheory.«RING_UNIT_SUBRING_OF_FIELD»
  SELECT_UNIQUE := Session.SELECT_UNIQUE
  SING_SUBSET := Session.SING_SUBSET
  SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED»
  SUBFIELD_IMP_SUBRING_OF := SessionLibrary.FieldTheory.«SUBFIELD_IMP_SUBRING_OF»
  SUBFIELD_OF_IMP_SUBSET := SessionLibrary.FieldTheory.«SUBFIELD_OF_IMP_SUBSET»
  SUBRING_GENERATED := SessionLibrary.RingTheory.«SUBRING_GENERATED»
  SUBRING_GENERATED_BY_SUBRING_GENERATED := SessionLibrary.RingTheory.«SUBRING_GENERATED_BY_SUBRING_GENERATED»
  SUBRING_GENERATED_INC_GEN := SessionLibrary.RingTheory.«SUBRING_GENERATED_INC_GEN»
  SUBRING_OF_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«SUBRING_OF_HOMOMORPHIC_IMAGE»
  SUBRING_OF_UNIONS := SessionLibrary.RingTheory.«SUBRING_OF_UNIONS»
  SUBRING_RING_IMAGE := SessionLibrary.RingTheory.«SUBRING_RING_IMAGE»
  SUBRING_SUBRING_GENERATED := SessionLibrary.RingTheory.«SUBRING_SUBRING_GENERATED»
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUBSET_REFL := Session.SUBSET_REFL
  SUBSET_TRANS := Session.SUBSET_TRANS
  SUB_0 := Session.SUB_0
  SUB_ADD := Session.SUB_ADD
  TRIVIAL_RING_10 := SessionLibrary.RingTheory.«TRIVIAL_RING_10»
  ZL_SUBSETS_UNIONS_NONEMPTY := SessionLibrary.Wo.«ZL_SUBSETS_UNIONS_NONEMPTY»
  dedekind_domain := SessionANT.Dedekind.«dedekind_domain»
  field_of_fractions := SessionLibrary.RingTheory.«field_of_fractions»
  local_ring := SessionLibrary.RingTheory.«local_ring»
  maximal_ideal := SessionLibrary.RingTheory.«maximal_ideal»
  num_WF := Session.num_WF
  o_DEF := Session.o_DEF
  poly_eval := SessionLibrary.RingTheory.«poly_eval»
  prime_ideal := SessionLibrary.RingTheory.«prime_ideal»
  principal_ideal := SessionLibrary.RingTheory.«principal_ideal»
  ring_divides := SessionLibrary.RingTheory.«ring_divides»
  ring_homomorphism := SessionLibrary.RingTheory.«ring_homomorphism»
  ring_ideal := SessionLibrary.RingTheory.«ring_ideal»
  ring_image := SessionLibrary.RingTheory.«ring_image»
  ring_kernel := SessionLibrary.RingTheory.«ring_kernel»
  ring_pow := SessionLibrary.RingTheory.«ring_pow»
  ring_sub := SessionLibrary.RingTheory.«ring_sub»
  subring_of := SessionLibrary.RingTheory.«subring_of»

/-- What valuation_ring.ml uses from Session. -/
def deps : HolANT.ValuationRing.ValuationRingDeps where
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
  GEN_BETA_CONV := Session.GEN_BETA_CONV
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

/- The bundles, in valuation_ring.ml order. -/
initialize BValuationRing01 : HolANT.ValuationRing.ValuationRing01 ←
  ioB "setupValuationRing01" (HolANT.ValuationRing.setupValuationRing01 deps).run
initialize BValuationRing02 : HolANT.ValuationRing.ValuationRing02 ←
  ioB "setupValuationRing02" (HolANT.ValuationRing.setupValuationRing02 deps BValuationRing01).run
initialize BValuationRing03 : HolANT.ValuationRing.ValuationRing03 ←
  ioB "setupValuationRing03" (HolANT.ValuationRing.setupValuationRing03 deps BValuationRing01 BValuationRing02).run

-- ValuationRing01
def valuation_ring : thm := BValuationRing01.valuation_ring
def valuation_subring : thm := BValuationRing01.valuation_subring
def VALUATION_RING_IMP_INTEGRAL_DOMAIN : thm := BValuationRing01.VALUATION_RING_IMP_INTEGRAL_DOMAIN
def VALUATION_RING_IDEALS_TOTALLY_ORDERED : thm := BValuationRing01.VALUATION_RING_IDEALS_TOTALLY_ORDERED
def VALUATION_RING_IMP_LOCAL : thm := BValuationRing01.VALUATION_RING_IMP_LOCAL
def VALUATION_RING_IMP_INTEGRALLY_CLOSED : thm := BValuationRing01.VALUATION_RING_IMP_INTEGRALLY_CLOSED
def VALUATION_RING_QUOTIENT_RING : thm := BValuationRing01.VALUATION_RING_QUOTIENT_RING
def VALUATION_SUBRING_SUPERSET : thm := BValuationRing01.VALUATION_SUBRING_SUPERSET
def VALUATION_SUBRING_IMP_VALUATION_RING : thm := BValuationRing01.VALUATION_SUBRING_IMP_VALUATION_RING
def VALUATION_SUBRING_IMP_LOCAL : thm := BValuationRing01.VALUATION_SUBRING_IMP_LOCAL
def VALUATION_SUBRING_MAXIMAL_IDEAL : thm := BValuationRing01.VALUATION_SUBRING_MAXIMAL_IDEAL
def VALUATION_SUBRING_INV_MAXIMAL_IDEAL : thm := BValuationRing01.VALUATION_SUBRING_INV_MAXIMAL_IDEAL
def VALUATION_SUBRING_SUBFIELD : thm := BValuationRing01.VALUATION_SUBRING_SUBFIELD
def VALUATION_SUBRING_INTEGRAL_ELEMENT : thm := BValuationRing01.VALUATION_SUBRING_INTEGRAL_ELEMENT
def VALUATION_SUBRING_INTEGRAL_CLOSURE : thm := BValuationRing01.VALUATION_SUBRING_INTEGRAL_CLOSURE
def IDEAL_GENERATED_ADJOIN_OR_INV : thm := BValuationRing01.IDEAL_GENERATED_ADJOIN_OR_INV

-- ValuationRing02
def RING_HOMOMORPHISM_ADJOIN_ROOT : thm := BValuationRing02.RING_HOMOMORPHISM_ADJOIN_ROOT
def VALUATION_SUBRING_DOMINATES : thm := BValuationRing02.VALUATION_SUBRING_DOMINATES

-- ValuationRing03
def VALUATION_SUBRING_EXTEND_HOMOMORPHISM : thm := BValuationRing03.VALUATION_SUBRING_EXTEND_HOMOMORPHISM
def INTEGRAL_CLOSURE_EQ_INTERS_VALUATION_SUBRINGS : thm := BValuationRing03.INTEGRAL_CLOSURE_EQ_INTERS_VALUATION_SUBRINGS
def VALUATION_RING_IMP_BEZOUT_RING : thm := BValuationRing03.VALUATION_RING_IMP_BEZOUT_RING
def DVR_IMP_VALUATION_RING : thm := BValuationRing03.DVR_IMP_VALUATION_RING
def DVR_EQ_NOETHERIAN_VALUATION_RING : thm := BValuationRing03.DVR_EQ_NOETHERIAN_VALUATION_RING
def DVR_EQ_INTEGRALLY_CLOSED : thm := BValuationRing03.DVR_EQ_INTEGRALLY_CLOSED
def DVR_DIVIDES_UNIFORMIZER_POW : thm := BValuationRing03.DVR_DIVIDES_UNIFORMIZER_POW
def VALUATION_SUBRING_DEDEKIND_VALUATION : thm := BValuationRing03.VALUATION_SUBRING_DEDEKIND_VALUATION

/-- `needs "ANT/valuation_ring.ml"`: already done by importing this module. -/
def ensureValuationRing : IO Unit := pure ()

end SessionANT.ValuationRing
