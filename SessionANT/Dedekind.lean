/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/dedekind.ml                                   . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/Dedekind.lean

  The session half of the dedekind.ml translation: it supplies HolANT.Dedekind's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/dedekind.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.Dedekind
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.RingTheory
import SessionLibrary.Products
import SessionANT.Algmisc
import SessionLibrary.Matroids
import SessionLibrary.Permutations
import SessionLibrary.RingDet
import SessionLibrary.FieldTheory
import SessionANT.Integral
import SessionANT.IdealArith

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.Dedekind

/-- The core theorems dedekind.ml uses. -/
def core1 : HolANT.Dedekind.CoreThms1 where
  ADD1 := Session.ADD1
  ADD_CLAUSES := Session.ADD_CLAUSES
  ADD_SYM := Session.ADD_SYM
  ARITH := Session.ARITH
  ARITH_EQ := Session.ARITH_EQ
  COMAXIMAL_IDEAL_POW := SessionANT.IdealArith.«COMAXIMAL_IDEAL_POW»
  CONJ_ASSOC := Session.CONJ_ASSOC
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  EQ_TRANS := Session.EQ_TRANS
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXTENSION := Session.EXTENSION
  FIELD_IMP_PID := SessionLibrary.RingTheory.«FIELD_IMP_PID»
  FINITE_DELETE := Session.FINITE_DELETE
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_SUBSET := Session.FINITE_SUBSET
  FINITE_UNION := Session.FINITE_UNION
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  FUN_EQ_THM := Session.FUN_EQ_THM
  HAS_SIZE_IMAGE_INJ := Session.HAS_SIZE_IMAGE_INJ
  HAS_SIZE_NUMSEG_LE := Session.HAS_SIZE_NUMSEG_LE
  IDEAL_GENERATED_EQ_0 := SessionLibrary.RingTheory.«IDEAL_GENERATED_EQ_0»
  IDEAL_GENERATED_FINITE := SessionLibrary.RingTheory.«IDEAL_GENERATED_FINITE»
  IDEAL_GENERATED_INC := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC»
  IDEAL_GENERATED_INC_GEN := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC_GEN»
  IDEAL_GENERATED_MINIMAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL»
  IDEAL_GENERATED_MINIMAL_EQ := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL_EQ»
  IDEAL_GENERATED_SING_ALT := SessionLibrary.RingTheory.«IDEAL_GENERATED_SING_ALT»
  IDEAL_GENERATED_SING_EQ_CARRIER := SessionLibrary.RingTheory.«IDEAL_GENERATED_SING_EQ_CARRIER»
  IDEAL_GENERATED_SUBSET := SessionLibrary.RingTheory.«IDEAL_GENERATED_SUBSET»
  IDEAL_POW_0 := SessionANT.IdealArith.«IDEAL_POW_0»
  IDEAL_POW_1 := SessionANT.IdealArith.«IDEAL_POW_1»
  IDEAL_POW_ADD := SessionANT.IdealArith.«IDEAL_POW_ADD»
  IDEAL_POW_ANTIMONO := SessionANT.IdealArith.«IDEAL_POW_ANTIMONO»
  IDEAL_POW_CARRIER := SessionANT.IdealArith.«IDEAL_POW_CARRIER»
  IDEAL_POW_EQ_ZERO := SessionANT.IdealArith.«IDEAL_POW_EQ_ZERO»
  IDEAL_POW_PRINCIPAL := SessionANT.IdealArith.«IDEAL_POW_PRINCIPAL»
  IDEAL_POW_SUBSET_PRIME_IDEAL := SessionANT.IdealArith.«IDEAL_POW_SUBSET_PRIME_IDEAL»
  IDEAL_POW_SUC := SessionANT.IdealArith.«IDEAL_POW_SUC»
  IDEAL_PRODUCT_EMPTY := SessionANT.IdealArith.«IDEAL_PRODUCT_EMPTY»
  IDEAL_PRODUCT_EQ := SessionANT.IdealArith.«IDEAL_PRODUCT_EQ»
  IDEAL_PRODUCT_EQ_ZERO := SessionANT.IdealArith.«IDEAL_PRODUCT_EQ_ZERO»
  IDEAL_PRODUCT_INSERT := SessionANT.IdealArith.«IDEAL_PRODUCT_INSERT»
  IDEAL_PRODUCT_MONOMIAL_MUL := SessionANT.IdealArith.«IDEAL_PRODUCT_MONOMIAL_MUL»
  IDEAL_PRODUCT_PRINCIPAL := SessionANT.IdealArith.«IDEAL_PRODUCT_PRINCIPAL»
  IDEAL_PRODUCT_SING := SessionANT.IdealArith.«IDEAL_PRODUCT_SING»
  IDEAL_PRODUCT_SUBSET := SessionANT.IdealArith.«IDEAL_PRODUCT_SUBSET»
  IDEAL_PRODUCT_SUBSET_PRIME_IDEAL := SessionANT.IdealArith.«IDEAL_PRODUCT_SUBSET_PRIME_IDEAL»
  IDEAL_PRODUCT_SUPERSET := SessionANT.IdealArith.«IDEAL_PRODUCT_SUPERSET»
  IDEAL_PROD_AC := SessionANT.IdealArith.«IDEAL_PROD_AC»
  IDEAL_PROD_ASSOC := SessionANT.IdealArith.«IDEAL_PROD_ASSOC»
  IDEAL_PROD_CARRIER := SessionANT.IdealArith.«IDEAL_PROD_CARRIER»
  IDEAL_PROD_CARRIER_LEFT := SessionANT.IdealArith.«IDEAL_PROD_CARRIER_LEFT»
  IDEAL_PROD_COMAXIMAL := SessionANT.IdealArith.«IDEAL_PROD_COMAXIMAL»
  IDEAL_PROD_COMM := SessionANT.IdealArith.«IDEAL_PROD_COMM»
  IDEAL_PROD_EQ_ZERO := SessionANT.IdealArith.«IDEAL_PROD_EQ_ZERO»
  IDEAL_PROD_EXPLICIT := SessionANT.IdealArith.«IDEAL_PROD_EXPLICIT»
  IDEAL_PROD_IDEAL_GENERATED := SessionANT.IdealArith.«IDEAL_PROD_IDEAL_GENERATED»
  IDEAL_PROD_LZERO := SessionANT.IdealArith.«IDEAL_PROD_LZERO»
  IDEAL_PROD_MINIMAL := SessionANT.IdealArith.«IDEAL_PROD_MINIMAL»
  IDEAL_PROD_MONO := SessionANT.IdealArith.«IDEAL_PROD_MONO»
  IDEAL_PROD_PRINCIPAL := SessionANT.IdealArith.«IDEAL_PROD_PRINCIPAL»
  IDEAL_PROD_PRINCIPAL_CANCEL := SessionANT.IdealArith.«IDEAL_PROD_PRINCIPAL_CANCEL»
  IDEAL_PROD_PRINCIPAL_FACTOR := SessionANT.IdealArith.«IDEAL_PROD_PRINCIPAL_FACTOR»
  IDEAL_PROD_PRINCIPAL_SUBSET_CANCEL := SessionANT.IdealArith.«IDEAL_PROD_PRINCIPAL_SUBSET_CANCEL»
  IDEAL_PROD_RZERO := SessionANT.IdealArith.«IDEAL_PROD_RZERO»
  IDEAL_PROD_SCALE := SessionANT.IdealArith.«IDEAL_PROD_SCALE»
  IDEAL_PROD_SETADD_RDISTRIB := SessionANT.IdealArith.«IDEAL_PROD_SETADD_RDISTRIB»
  IDEAL_PROD_SUBSET_INTER := SessionANT.IdealArith.«IDEAL_PROD_SUBSET_INTER»
  IDEAL_PROD_SUBSET_LEFT := SessionANT.IdealArith.«IDEAL_PROD_SUBSET_LEFT»
  IDEAL_PROD_SUBSET_RIGHT := SessionANT.IdealArith.«IDEAL_PROD_SUBSET_RIGHT»
  IDEAL_SUBSET_IDEAL_QUOTIENT := SessionANT.IdealArith.«IDEAL_SUBSET_IDEAL_QUOTIENT»
  IMP_CONJ := Session.IMP_CONJ
  IMP_CONJ_ALT := Session.IMP_CONJ_ALT
  IMP_IMP := Session.IMP_IMP
  INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING»
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  INTEGRAL_DOMAIN_NONTRIVIAL := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_NONTRIVIAL»
  INTEGRAL_DOMAIN_REGULAR := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_REGULAR»
  INTEGRAL_ELEMENT_FINITE_MODULE := SessionANT.Integral.«INTEGRAL_ELEMENT_FINITE_MODULE»
  INTER_IDEMPOT := Session.INTER_IDEMPOT
  INTER_SUBSET := Session.INTER_SUBSET
  IN_DELETE := Session.IN_DELETE
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IDEAL_GENERATED_SELF := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SELF»
  IN_IDEAL_GENERATED_SING_EQ := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SING_EQ»
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_RING_IDEAL_ADD := SessionLibrary.RingTheory.«IN_RING_IDEAL_ADD»
  IN_RING_IDEAL_LMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_LMUL»
  IN_RING_IDEAL_NEG := SessionLibrary.RingTheory.«IN_RING_IDEAL_NEG»
  IN_RING_IDEAL_RMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_RMUL»
  IN_RING_IDEAL_SUB := SessionLibrary.RingTheory.«IN_RING_IDEAL_SUB»
  IN_SING := Session.IN_SING
  IN_SUBRING_0 := SessionLibrary.RingTheory.«IN_SUBRING_0»
  IN_SUBRING_ADD := SessionLibrary.RingTheory.«IN_SUBRING_ADD»
  IN_SUBRING_MUL := SessionLibrary.RingTheory.«IN_SUBRING_MUL»
  IN_SUBRING_POW := SessionLibrary.RingTheory.«IN_SUBRING_POW»
  IN_UNION := Session.IN_UNION
  LE := Session.LE
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_0 := Session.LE_0
  LE_ANTISYM := Session.LE_ANTISYM
  LE_MULT_RCANCEL := Session.LE_MULT_RCANCEL
  LE_REFL := Session.LE_REFL
  LT_EXISTS := Session.LT_EXISTS
  MAXIMAL_AMONG_PRIME_IDEALS := SessionLibrary.RingTheory.«MAXIMAL_AMONG_PRIME_IDEALS»
  MAXIMAL_IDEAL_COMAXIMAL := SessionANT.IdealArith.«MAXIMAL_IDEAL_COMAXIMAL»
  MAXIMAL_IDEAL_COMAXIMAL_MUL := SessionANT.IdealArith.«MAXIMAL_IDEAL_COMAXIMAL_MUL»
  MAXIMAL_IMP_PRIME_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_PRIME_IDEAL»
  MAXIMAL_IMP_RING_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_RING_IDEAL»
  MAXIMAL_SUPERIDEAL_EXISTS := SessionLibrary.RingTheory.«MAXIMAL_SUPERIDEAL_EXISTS»
  MONOMIAL_1 := SessionLibrary.RingTheory.«MONOMIAL_1»
/-- The core theorems dedekind.ml uses. -/
def core2 : HolANT.Dedekind.CoreThms2 where
  MONOMIAL_DIV := SessionLibrary.RingTheory.«MONOMIAL_DIV»
  MONOMIAL_DIV_LMUL := SessionLibrary.RingTheory.«MONOMIAL_DIV_LMUL»
  MONOMIAL_INDUCT := SessionLibrary.RingTheory.«MONOMIAL_INDUCT»
  MONOMIAL_MUL := SessionLibrary.RingTheory.«MONOMIAL_MUL»
  MONOMIAL_VAR := SessionLibrary.RingTheory.«MONOMIAL_VAR»
  MONOMIAL_VARS_1 := SessionLibrary.RingTheory.«MONOMIAL_VARS_1»
  MONOMIAL_VARS_VAR := SessionLibrary.RingTheory.«MONOMIAL_VARS_VAR»
  MONO_EXISTS := Session.MONO_EXISTS
  MULT_CLAUSES := Session.MULT_CLAUSES
  NOETHERIAN_PRIME_PRODUCT_SUBSET := SessionANT.IdealArith.«NOETHERIAN_PRIME_PRODUCT_SUBSET»
  NOETHERIAN_RING_INDUCT := SessionANT.IdealArith.«NOETHERIAN_RING_INDUCT»
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NOT_LE := Session.NOT_LE
  NOT_LT := Session.NOT_LT
  NSUM_CLAUSES := Session.NSUM_CLAUSES
  ONE := Session.ONE
  PID_IMP_INTEGRALLY_CLOSED := SessionANT.Integral.«PID_IMP_INTEGRALLY_CLOSED»
  PID_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«PID_IMP_INTEGRAL_DOMAIN»
  PID_IMP_NOETHERIAN_RING := SessionLibrary.RingTheory.«PID_IMP_NOETHERIAN_RING»
  PID_INTEGER_RING := SessionLibrary.RingTheory.«PID_INTEGER_RING»
  PID_MAXIMAL_EQ_PRIME_IDEAL := SessionLibrary.RingTheory.«PID_MAXIMAL_EQ_PRIME_IDEAL»
  PRIME_IDEAL_IMP_PSUBSET := SessionLibrary.RingTheory.«PRIME_IDEAL_IMP_PSUBSET»
  PRIME_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«PRIME_IDEAL_IMP_SUBSET»
  PRIME_IMP_PROPER_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_PROPER_IDEAL»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PROPER_IDEAL := SessionLibrary.RingTheory.«PROPER_IDEAL»
  PROPER_IDEAL_ALT := SessionLibrary.RingTheory.«PROPER_IDEAL_ALT»
  PSUBSET := Session.PSUBSET
  QUOTIENT_RING_REDUCED := SessionLibrary.RingTheory.«QUOTIENT_RING_REDUCED»
  RADICAL_PRIME_IDEAL := SessionLibrary.RingTheory.«RADICAL_PRIME_IDEAL»
  RADICAL_SUBSET := SessionLibrary.RingTheory.«RADICAL_SUBSET»
  RIGHT_EXISTS_IMP_THM := Session.RIGHT_EXISTS_IMP_THM
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_ADD_LZERO := SessionLibrary.RingTheory.«RING_ADD_LZERO»
  RING_ADD_RDISTRIB := SessionLibrary.RingTheory.«RING_ADD_RDISTRIB»
  RING_ADD_RZERO := SessionLibrary.RingTheory.«RING_ADD_RZERO»
  RING_DIVIDES_ZERO := SessionLibrary.RingTheory.«RING_DIVIDES_ZERO»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_SUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUM»
  RING_IDEAL_0 := SessionLibrary.RingTheory.«RING_IDEAL_0»
  RING_IDEAL_CARRIER := SessionLibrary.RingTheory.«RING_IDEAL_CARRIER»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IDEAL_POW := SessionANT.IdealArith.«RING_IDEAL_IDEAL_POW»
  RING_IDEAL_IDEAL_PROD := SessionANT.IdealArith.«RING_IDEAL_IDEAL_PROD»
  RING_IDEAL_IDEAL_PRODUCT := SessionANT.IdealArith.«RING_IDEAL_IDEAL_PRODUCT»
  RING_IDEAL_IDEAL_QUOTIENT := SessionANT.IdealArith.«RING_IDEAL_IDEAL_QUOTIENT»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_IDEAL_INTER := SessionLibrary.RingTheory.«RING_IDEAL_INTER»
  RING_IDEAL_SETADD := SessionLibrary.RingTheory.«RING_IDEAL_SETADD»
  RING_MONOMORPHISM_FRACTIONATE := SessionLibrary.RingTheory.«RING_MONOMORPHISM_FRACTIONATE»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MONOMORPHISM_INJECTIVE_EQ := SessionLibrary.RingTheory.«RING_MONOMORPHISM_INJECTIVE_EQ»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MULTSYS_REGULAR := SessionLibrary.RingTheory.«RING_MULTSYS_REGULAR»
  RING_MUL_ASSOC := SessionLibrary.RingTheory.«RING_MUL_ASSOC»
  RING_MUL_IN_IDEAL_POW := SessionANT.IdealArith.«RING_MUL_IN_IDEAL_POW»
  RING_MUL_IN_IDEAL_PROD := SessionANT.IdealArith.«RING_MUL_IN_IDEAL_PROD»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_LNEG := SessionLibrary.RingTheory.«RING_MUL_LNEG»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_SYM := SessionLibrary.RingTheory.«RING_MUL_SYM»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_2 := SessionLibrary.RingTheory.«RING_POW_2»
  RING_POW_IN_IDEAL_POW := SessionANT.IdealArith.«RING_POW_IN_IDEAL_POW»
  RING_SETADD_LZERO := SessionLibrary.RingTheory.«RING_SETADD_LZERO»
  RING_SETADD_RZERO := SessionLibrary.RingTheory.«RING_SETADD_RZERO»
  RING_SETADD_SUBSET_IDEAL := SessionLibrary.RingTheory.«RING_SETADD_SUBSET_IDEAL»
  RING_SETADD_SUPERSET_LEFT := SessionLibrary.RingTheory.«RING_SETADD_SUPERSET_LEFT»
  RING_SETADD_SUPERSET_RIGHT := SessionLibrary.RingTheory.«RING_SETADD_SUPERSET_RIGHT»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_REFL := SessionLibrary.RingTheory.«RING_SUB_REFL»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_RMUL := SessionLibrary.RingTheory.«RING_SUM_RMUL»
  RING_UNIT_1 := SessionLibrary.RingTheory.«RING_UNIT_1»
  RING_UNIT_FRACTIONATE := SessionLibrary.RingTheory.«RING_UNIT_FRACTIONATE»
  SELECT_UNIQUE := Session.SELECT_UNIQUE
  SIMPLE_IMAGE_GEN := Session.SIMPLE_IMAGE_GEN
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUBSET_ANTISYM_EQ := Session.SUBSET_ANTISYM_EQ
  SUBSET_IDEALS_GENERATED_SING := SessionLibrary.RingTheory.«SUBSET_IDEALS_GENERATED_SING»
  SUBSET_IDEAL_QUOTIENT := SessionANT.IdealArith.«SUBSET_IDEAL_QUOTIENT»
  SUBSET_INTER := Session.SUBSET_INTER
  SUBSET_REFL := Session.SUBSET_REFL
  SUBSET_TRANS := Session.SUBSET_TRANS
  UNION_SUBSET := Session.UNION_SUBSET
  finitely_generated_ideal := SessionLibrary.RingTheory.«finitely_generated_ideal»
  fraction_ring := SessionLibrary.RingTheory.«fraction_ring»
  integrally_closed := SessionANT.Integral.«integrally_closed»
  maximal_ideal := SessionLibrary.RingTheory.«maximal_ideal»
  monomial := SessionLibrary.RingTheory.«monomial»
  monomial_1 := SessionLibrary.RingTheory.«monomial_1»
  monomial_divides := SessionLibrary.RingTheory.«monomial_divides»
  monomial_mul := SessionLibrary.RingTheory.«monomial_mul»
  monomial_var := SessionLibrary.RingTheory.«monomial_var»
  monomial_vars := SessionLibrary.RingTheory.«monomial_vars»
  noetherian_ring := SessionLibrary.RingTheory.«noetherian_ring»
  num_CASES := Session.num_CASES
  o_THM := Session.o_THM
  prime_ideal := SessionLibrary.RingTheory.«prime_ideal»
  proper_ideal := SessionLibrary.RingTheory.«proper_ideal»
  radical := SessionLibrary.RingTheory.«radical»
  ring_divides := SessionLibrary.RingTheory.«ring_divides»
  ring_ideal := SessionLibrary.RingTheory.«ring_ideal»
  ring_pow := SessionLibrary.RingTheory.«ring_pow»
  ring_unit := SessionLibrary.RingTheory.«ring_unit»
  subring_of := SessionLibrary.RingTheory.«subring_of»
  trivial_ring := SessionLibrary.RingTheory.«trivial_ring»

/-- What dedekind.ml uses from Session. -/
def deps : HolANT.Dedekind.DedekindDeps where
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
  REFUTE_THEN := Session.REFUTE_THEN
  core1 := core1
  core2 := core2

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in dedekind.ml order. -/
initialize BDedekind01 : HolANT.Dedekind.Dedekind01 ←
  ioB "setupDedekind01" (HolANT.Dedekind.setupDedekind01 deps).run
initialize BDedekind02 : HolANT.Dedekind.Dedekind02 ←
  ioB "setupDedekind02" (HolANT.Dedekind.setupDedekind02 deps BDedekind01).run
initialize BDedekind03 : HolANT.Dedekind.Dedekind03 ←
  ioB "setupDedekind03" (HolANT.Dedekind.setupDedekind03 deps BDedekind01 BDedekind02).run
initialize BDedekind04 : HolANT.Dedekind.Dedekind04 ←
  ioB "setupDedekind04" (HolANT.Dedekind.setupDedekind04 deps BDedekind01 BDedekind03).run

-- Dedekind01
def dedekind_domain : thm := BDedekind01.dedekind_domain
def DEDEKIND_IMP_INTEGRAL_DOMAIN : thm := BDedekind01.DEDEKIND_IMP_INTEGRAL_DOMAIN
def DEDEKIND_IMP_NOETHERIAN : thm := BDedekind01.DEDEKIND_IMP_NOETHERIAN
def DEDEKIND_IMP_INTEGRALLY_CLOSED : thm := BDedekind01.DEDEKIND_IMP_INTEGRALLY_CLOSED
def DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL : thm := BDedekind01.DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL
def DEDEKIND_MAXIMAL_EQ_PRIME_IDEAL : thm := BDedekind01.DEDEKIND_MAXIMAL_EQ_PRIME_IDEAL
def DEDEKIND_KRULL_DIMENSION_ONE : thm := BDedekind01.DEDEKIND_KRULL_DIMENSION_ONE
def PID_IMP_DEDEKIND : thm := BDedekind01.PID_IMP_DEDEKIND
def FIELD_IMP_DEDEKIND : thm := BDedekind01.FIELD_IMP_DEDEKIND
def DEDEKIND_INTEGER_RING : thm := BDedekind01.DEDEKIND_INTEGER_RING
def INTEGRALLY_CLOSED_DIVIDES_IDEAL : thm := BDedekind01.INTEGRALLY_CLOSED_DIVIDES_IDEAL
def IDEAL_PRODUCT_MONOMIAL_VAR : thm := BDedekind01.IDEAL_PRODUCT_MONOMIAL_VAR
def IDEAL_PRODUCT_PRIME_MONOMIAL_MUL : thm := BDedekind01.IDEAL_PRODUCT_PRIME_MONOMIAL_MUL
def DEDEKIND_IDEAL_QUOTIENT_MAXIMAL_PSUBSET : thm := BDedekind01.DEDEKIND_IDEAL_QUOTIENT_MAXIMAL_PSUBSET
def DEDEKIND_MAXIMAL_IDEAL_INVERSE : thm := BDedekind01.DEDEKIND_MAXIMAL_IDEAL_INVERSE
def IDEAL_PROD_PRINCIPAL_COFACTOR : thm := BDedekind01.IDEAL_PROD_PRINCIPAL_COFACTOR
def DEDEKIND_IDEAL_FACTORIZATION_EXISTS : thm := BDedekind01.DEDEKIND_IDEAL_FACTORIZATION_EXISTS
def DEDEKIND_IDEAL_INDUCT : thm := BDedekind01.DEDEKIND_IDEAL_INDUCT
def DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE : thm := BDedekind01.DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE
def DEDEKIND_IDEAL_INVERTIBLE : thm := BDedekind01.DEDEKIND_IDEAL_INVERTIBLE
def DEDEKIND_IDEAL_PROD_SUBSET_CANCEL : thm := BDedekind01.DEDEKIND_IDEAL_PROD_SUBSET_CANCEL
def DEDEKIND_IDEAL_PROD_CANCEL : thm := BDedekind01.DEDEKIND_IDEAL_PROD_CANCEL
def DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES : thm := BDedekind01.DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES
def DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT : thm := BDedekind01.DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT

-- Dedekind02
def DEDEKIND_IDEAL_QUOTIENT_CANCEL : thm := BDedekind02.DEDEKIND_IDEAL_QUOTIENT_CANCEL
def DEDEKIND_IDEAL_MEMBER_PRINCIPAL_MULTIPLE : thm := BDedekind02.DEDEKIND_IDEAL_MEMBER_PRINCIPAL_MULTIPLE
def DEDEKIND_PRIMITIVE_MULTIPLE : thm := BDedekind02.DEDEKIND_PRIMITIVE_MULTIPLE
def DEDEKIND_IDEAL_POW_SUBSET : thm := BDedekind02.DEDEKIND_IDEAL_POW_SUBSET
def DEDEKIND_IDEAL_POW_EQ : thm := BDedekind02.DEDEKIND_IDEAL_POW_EQ
def DEDEKIND_PRIME_IDEAL_UNIFORMIZER : thm := BDedekind02.DEDEKIND_PRIME_IDEAL_UNIFORMIZER
def ideal_valuation : thm := BDedekind02.ideal_valuation
def IDEAL_VALUATION_UNIQUE : thm := BDedekind02.IDEAL_VALUATION_UNIQUE
def IDEAL_VALUATION_CARRIER : thm := BDedekind02.IDEAL_VALUATION_CARRIER
def IDEAL_PRODUCT_PRIME_MONOMIAL_DIVIDES : thm := BDedekind02.IDEAL_PRODUCT_PRIME_MONOMIAL_DIVIDES
def DEDEKIND_IDEAL_PRODUCT_SUBSET_POW : thm := BDedekind02.DEDEKIND_IDEAL_PRODUCT_SUBSET_POW
def IDEAL_VALUATION_IDEAL_PRODUCT_MONOMIAL : thm := BDedekind02.IDEAL_VALUATION_IDEAL_PRODUCT_MONOMIAL
def DEDEKIND_IDEAL_FACTORIZATION : thm := BDedekind02.DEDEKIND_IDEAL_FACTORIZATION
def DEDEKIND_IDEAL_FACTORIZATION_UNIQUE : thm := BDedekind02.DEDEKIND_IDEAL_FACTORIZATION_UNIQUE
def DEDEKIND_IDEAL_SUBSET_POW_VALUATION : thm := BDedekind02.DEDEKIND_IDEAL_SUBSET_POW_VALUATION
def IDEAL_VALUATION_EQ_0 : thm := BDedekind02.IDEAL_VALUATION_EQ_0
def IDEAL_VALUATION_FINITE_SUPPORT : thm := BDedekind02.IDEAL_VALUATION_FINITE_SUPPORT
def DEDEKIND_IDEAL_PRODUCT_PRIME_POW_UNIQUE : thm := BDedekind02.DEDEKIND_IDEAL_PRODUCT_PRIME_POW_UNIQUE
def DEDEKIND_IDEAL_PRODUCT_PRIME_POWERS : thm := BDedekind02.DEDEKIND_IDEAL_PRODUCT_PRIME_POWERS
def IDEAL_VALUATION_IDEAL_PROD : thm := BDedekind02.IDEAL_VALUATION_IDEAL_PROD
def IDEAL_VALUATION_PRINCIPAL_MUL : thm := BDedekind02.IDEAL_VALUATION_PRINCIPAL_MUL
def IDEAL_VALUATION_IDEAL_POW : thm := BDedekind02.IDEAL_VALUATION_IDEAL_POW
def IDEAL_VALUATION_PRINCIPAL_POW : thm := BDedekind02.IDEAL_VALUATION_PRINCIPAL_POW
def IDEAL_VALUATION_IDEAL_PRODUCT : thm := BDedekind02.IDEAL_VALUATION_IDEAL_PRODUCT
def IDEAL_VALUATION_PRINCIPAL_PRODUCT : thm := BDedekind02.IDEAL_VALUATION_PRINCIPAL_PRODUCT
def IDEAL_VALUATION_PRIME : thm := BDedekind02.IDEAL_VALUATION_PRIME
def DEDEKIND_IDEAL_SUBSET_VALUATION : thm := BDedekind02.DEDEKIND_IDEAL_SUBSET_VALUATION
def DEDEKIND_IDEAL_EQ_VALUATION : thm := BDedekind02.DEDEKIND_IDEAL_EQ_VALUATION

-- Dedekind03
def IDEAL_VALUATION_SETADD : thm := BDedekind03.IDEAL_VALUATION_SETADD
def IDEAL_VALUATION_INTER : thm := BDedekind03.IDEAL_VALUATION_INTER
def DEDEKIND_IDEAL_PROD_EQ_INTER : thm := BDedekind03.DEDEKIND_IDEAL_PROD_EQ_INTER
def DEDEKIND_FINITE_MAXIMAL_IDEALS_ABOVE : thm := BDedekind03.DEDEKIND_FINITE_MAXIMAL_IDEALS_ABOVE
def DEDEKIND_IDEAL_SUPERSET_PRIME_POW : thm := BDedekind03.DEDEKIND_IDEAL_SUPERSET_PRIME_POW
def DEDEKIND_RADICAL_IDEAL_VALUATION : thm := BDedekind03.DEDEKIND_RADICAL_IDEAL_VALUATION
def DEDEKIND_RADICAL_IDEAL : thm := BDedekind03.DEDEKIND_RADICAL_IDEAL
def DEDEKIND_QUOTIENT_RING_REDUCED : thm := BDedekind03.DEDEKIND_QUOTIENT_RING_REDUCED
def DEDEKIND_IDEAL_PROD_SETADD_INTER : thm := BDedekind03.DEDEKIND_IDEAL_PROD_SETADD_INTER
def DEDEKIND_IDEAL_PROD_INTER : thm := BDedekind03.DEDEKIND_IDEAL_PROD_INTER
def DEDEKIND_IDEAL_COPRIME_PROD_POW : thm := BDedekind03.DEDEKIND_IDEAL_COPRIME_PROD_POW
def DEDEKIND_IDEALS_SUPERSET_PRIME_POW : thm := BDedekind03.DEDEKIND_IDEALS_SUPERSET_PRIME_POW
def DEDEKIND_IN_IDEAL_POW_VALUATION : thm := BDedekind03.DEDEKIND_IN_IDEAL_POW_VALUATION
def DEDEKIND_RING_DIVIDES_VALUATION : thm := BDedekind03.DEDEKIND_RING_DIVIDES_VALUATION
def IDEAL_VALUATION_PRINCIPAL_ADD : thm := BDedekind03.IDEAL_VALUATION_PRINCIPAL_ADD
def IDEAL_VALUATION_PRINCIPAL_ADD_STRICT : thm := BDedekind03.IDEAL_VALUATION_PRINCIPAL_ADD_STRICT
def DEDEKIND_IDEAL_POW_MUL_CANCEL : thm := BDedekind03.DEDEKIND_IDEAL_POW_MUL_CANCEL
def DEDEKIND_PRIME_IDEAL_LOCAL_GENERATOR : thm := BDedekind03.DEDEKIND_PRIME_IDEAL_LOCAL_GENERATOR

-- Dedekind04
def DEDEKIND_IDEAL_POW_UNIFORMIZER_SPLIT : thm := BDedekind04.DEDEKIND_IDEAL_POW_UNIFORMIZER_SPLIT
def DEDEKIND_IDEAL_POW_UNIFORMIZER_POW : thm := BDedekind04.DEDEKIND_IDEAL_POW_UNIFORMIZER_POW
def DEDEKIND_SUBRING_DENSE : thm := BDedekind04.DEDEKIND_SUBRING_DENSE

/-- `needs "ANT/dedekind.ml"`: already done by importing this module. -/
def ensureDedekind : IO Unit := pure ()

end SessionANT.Dedekind
