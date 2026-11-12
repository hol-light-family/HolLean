/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/ideal_arith.ml                                . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/IdealArith.lean

  The session half of the ideal_arith.ml translation: it supplies HolANT.IdealArith's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/ideal_arith.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.IdealArith
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.RingTheory
import SessionLibrary.Permutations
import SessionLibrary.RingDet

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.IdealArith

/-- The core theorems ideal_arith.ml uses. -/
def core1 : HolANT.IdealArith.CoreThms1 where
  ADD_CLAUSES := Session.ADD_CLAUSES
  ADD_EQ_0 := Session.ADD_EQ_0
  CARD_DELETE := Session.CARD_DELETE
  CARD_EQ_0 := Session.CARD_EQ_0
  COMAXIMAL_RADICALS := SessionLibrary.RingTheory.«COMAXIMAL_RADICALS»
  EQ_IMP := Session.EQ_IMP
  EQ_SYM_EQ := Session.EQ_SYM_EQ
  EQ_TRANS := Session.EQ_TRANS
  ETA_AX := Session.ETA_AX
  EXISTS_IN_INSERT := Session.EXISTS_IN_INSERT
  EXISTS_UNIQUE_DEF := Session.EXISTS_UNIQUE_DEF
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXTENSION := Session.EXTENSION
  FINITELY_GENERATED_IMP_RING_IDEAL := SessionLibrary.RingTheory.«FINITELY_GENERATED_IMP_RING_IDEAL»
  FINITE_DELETE := Session.FINITE_DELETE
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_SUBSET := Session.FINITE_SUBSET
  FINITE_UNION := Session.FINITE_UNION
  FIRST_RING_EPIMORPHISM_THEOREM := SessionLibrary.RingTheory.«FIRST_RING_EPIMORPHISM_THEOREM»
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  FUN_IN_IMAGE := Session.FUN_IN_IMAGE
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_INDEX := Session.HAS_SIZE_INDEX
  IDEAL_GENERATED_0 := SessionLibrary.RingTheory.«IDEAL_GENERATED_0»
  IDEAL_GENERATED_BY_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«IDEAL_GENERATED_BY_HOMOMORPHIC_IMAGE»
  IDEAL_GENERATED_BY_IDEAL_GENERATED := SessionLibrary.RingTheory.«IDEAL_GENERATED_BY_IDEAL_GENERATED»
  IDEAL_GENERATED_EXPLICIT := SessionLibrary.RingTheory.«IDEAL_GENERATED_EXPLICIT»
  IDEAL_GENERATED_FINITE := SessionLibrary.RingTheory.«IDEAL_GENERATED_FINITE»
  IDEAL_GENERATED_INC := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC»
  IDEAL_GENERATED_INC_GEN := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC_GEN»
  IDEAL_GENERATED_INDUCT := SessionLibrary.RingTheory.«IDEAL_GENERATED_INDUCT»
  IDEAL_GENERATED_MINIMAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL»
  IDEAL_GENERATED_MONO := SessionLibrary.RingTheory.«IDEAL_GENERATED_MONO»
  IDEAL_GENERATED_RING_IDEAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_RING_IDEAL»
  IDEAL_GENERATED_SCALE := SessionLibrary.RingTheory.«IDEAL_GENERATED_SCALE»
  IDEAL_GENERATED_SING_ALT := SessionLibrary.RingTheory.«IDEAL_GENERATED_SING_ALT»
  IDEAL_GENERATED_SING_EQ_CARRIER := SessionLibrary.RingTheory.«IDEAL_GENERATED_SING_EQ_CARRIER»
  IDEAL_GENERATED_SUBSET := SessionLibrary.RingTheory.«IDEAL_GENERATED_SUBSET»
  IDEAL_GENERATED_SUBSET_CARRIER := SessionLibrary.RingTheory.«IDEAL_GENERATED_SUBSET_CARRIER»
  IDEAL_GENERATED_SUBSET_CARRIER_SUBSET := SessionLibrary.RingTheory.«IDEAL_GENERATED_SUBSET_CARRIER_SUBSET»
  IMAGE_CLAUSES := Session.IMAGE_CLAUSES
  IMAGE_SUBSET := Session.IMAGE_SUBSET
  IMP_CONJ := Session.IMP_CONJ
  INSERT_DELETE := Session.INSERT_DELETE
  INSERT_SUBSET := Session.INSERT_SUBSET
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  INTEGRAL_DOMAIN_MUL_LCANCEL := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_LCANCEL»
  INTEGRAL_DOMAIN_NONTRIVIAL := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_NONTRIVIAL»
  INTERS_0 := Session.INTERS_0
  INTERS_GSPEC := Session.INTERS_GSPEC
  INTERS_INSERT := Session.INTERS_INSERT
  INTER_IDEMPOT := Session.INTER_IDEMPOT
  INTER_UNIV := Session.INTER_UNIV
  IN_CARTESIAN_PRODUCT := Session.IN_CARTESIAN_PRODUCT
  IN_CROSS := Session.IN_CROSS
  IN_DELETE := Session.IN_DELETE
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IDEAL_GENERATED_SING_EQ := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SING_EQ»
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_INTER := Session.IN_INTER
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_RING_IDEAL_ADD := SessionLibrary.RingTheory.«IN_RING_IDEAL_ADD»
  IN_RING_IDEAL_LMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_LMUL»
  IN_RING_IDEAL_MUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_MUL»
  IN_RING_IDEAL_NEG := SessionLibrary.RingTheory.«IN_RING_IDEAL_NEG»
  IN_RING_IDEAL_RMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_RMUL»
  IN_RING_IDEAL_SUB := SessionLibrary.RingTheory.«IN_RING_IDEAL_SUB»
  IN_RING_IDEAL_SUM := SessionLibrary.RingTheory.«IN_RING_IDEAL_SUM»
  IN_SING := Session.IN_SING
  IN_UNION := Session.IN_UNION
  IN_UNIONS := Session.IN_UNIONS
  ITLIST := Session.listDefs.ITLIST
  JACOBSON_RADICAL_LOCAL_RING := SessionLibrary.RingTheory.«JACOBSON_RADICAL_LOCAL_RING»
  LEFT_AND_EXISTS_THM := Session.LEFT_AND_EXISTS_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LOCAL_RING_JACOBSON_RADICAL := SessionLibrary.RingTheory.«LOCAL_RING_JACOBSON_RADICAL»
  MAXIMAL_IDEAL_EXISTS := SessionLibrary.RingTheory.«MAXIMAL_IDEAL_EXISTS»
  MAXIMAL_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«MAXIMAL_IDEAL_IMP_SUBSET»
  MAXIMAL_IMP_PROPER_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_PROPER_IDEAL»
  MAXIMAL_IMP_RING_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_RING_IDEAL»
  MAXIMAL_SUPERIDEAL_EXISTS := SessionLibrary.RingTheory.«MAXIMAL_SUPERIDEAL_EXISTS»
  MONOMIAL_1 := SessionLibrary.RingTheory.«MONOMIAL_1»
  MONOMIAL_MONO := SessionLibrary.RingTheory.«MONOMIAL_MONO»
  MONOMIAL_VAR := SessionLibrary.RingTheory.«MONOMIAL_VAR»
  MONOMIAL_VARS_1 := SessionLibrary.RingTheory.«MONOMIAL_VARS_1»
  MONOMIAL_VARS_MUL := SessionLibrary.RingTheory.«MONOMIAL_VARS_MUL»
  MONOMIAL_VARS_VAR := SessionLibrary.RingTheory.«MONOMIAL_VARS_VAR»
  MONO_EXISTS := Session.MONO_EXISTS
  MULT_CLAUSES := Session.MULT_CLAUSES
  NOETHERIAN_RING := SessionLibrary.RingTheory.«NOETHERIAN_RING»
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NOT_SUC := Session.NOT_SUC
  PAIRWISE_INSERT := Session.PAIRWISE_INSERT
  PAIR_EQ := Session.PAIR_EQ
  PRIME_IDEAL_IMP_PSUBSET := SessionLibrary.RingTheory.«PRIME_IDEAL_IMP_PSUBSET»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PRINCIPAL_IDEAL_IDEAL_GENERATED_SING := SessionLibrary.RingTheory.«PRINCIPAL_IDEAL_IDEAL_GENERATED_SING»
  PRINCIPAL_IMP_FINITELY_GENERATED_IDEAL := SessionLibrary.RingTheory.«PRINCIPAL_IMP_FINITELY_GENERATED_IDEAL»
  PRODUCT_RING := SessionLibrary.RingTheory.«PRODUCT_RING»
  PROD_RING := SessionLibrary.RingTheory.«PROD_RING»
  PROPER_IDEAL := SessionLibrary.RingTheory.«PROPER_IDEAL»
  PROPER_IDEAL_ALT := SessionLibrary.RingTheory.«PROPER_IDEAL_ALT»
  PROPER_IDEAL_IMP_PSUBSET := SessionLibrary.RingTheory.«PROPER_IDEAL_IMP_PSUBSET»
  PROPER_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PROPER_IMP_RING_IDEAL»
  PSUBSET_ALT := Session.PSUBSET_ALT
  QUOTIENT_RING_0 := SessionLibrary.RingTheory.«QUOTIENT_RING_0»
  QUOTIENT_RING_1 := SessionLibrary.RingTheory.«QUOTIENT_RING_1»
  QUOTIENT_RING_CARRIER := SessionLibrary.RingTheory.«QUOTIENT_RING_CARRIER»
  QUOTIENT_RING_UNIVERSAL_EXPLICIT := SessionLibrary.RingTheory.«QUOTIENT_RING_UNIVERSAL_EXPLICIT»
  RADICAL_INTER := SessionLibrary.RingTheory.«RADICAL_INTER»
  RADICAL_MONO := SessionLibrary.RingTheory.«RADICAL_MONO»
  RADICAL_PRIME_IDEAL := SessionLibrary.RingTheory.«RADICAL_PRIME_IDEAL»
  REPLICATE := Session.listDefs.REPLICATE
  RESTRICTION := Session.RESTRICTION
  RESTRICTION_EXTENSION := Session.RESTRICTION_EXTENSION
  RESTRICTION_IN_CARTESIAN_PRODUCT := Session.RESTRICTION_IN_CARTESIAN_PRODUCT
  RESTRICTION_IN_EXTENSIONAL := Session.RESTRICTION_IN_EXTENSIONAL
  RESTRICTION_UNIQUE := Session.RESTRICTION_UNIQUE
  RIGHT_AND_EXISTS_THM := Session.RIGHT_AND_EXISTS_THM
  RIGHT_EXISTS_IMP_THM := Session.RIGHT_EXISTS_IMP_THM
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RIGHT_IMP_EXISTS_THM := Session.RIGHT_IMP_EXISTS_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_1_IN_MULTSYS := SessionLibrary.RingTheory.«RING_1_IN_MULTSYS»
  RING_1_NOT_IN_PRIME_IDEAL := SessionLibrary.RingTheory.«RING_1_NOT_IN_PRIME_IDEAL»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_ADD_LDISTRIB := SessionLibrary.RingTheory.«RING_ADD_LDISTRIB»
/-- The core theorems ideal_arith.ml uses. -/
def core2 : HolANT.IdealArith.CoreThms2 where
  RING_ADD_LZERO := SessionLibrary.RingTheory.«RING_ADD_LZERO»
  RING_ADD_RDISTRIB := SessionLibrary.RingTheory.«RING_ADD_RDISTRIB»
  RING_ADD_RZERO := SessionLibrary.RingTheory.«RING_ADD_RZERO»
  RING_ADD_SYM := SessionLibrary.RingTheory.«RING_ADD_SYM»
  RING_COMAXIMAL := SessionLibrary.RingTheory.«RING_COMAXIMAL»
  RING_COSET_EQ := SessionLibrary.RingTheory.«RING_COSET_EQ»
  RING_COSET_EQ_IDEAL := SessionLibrary.RingTheory.«RING_COSET_EQ_IDEAL»
  RING_DET := SessionLibrary.RingDet.«RING_DET»
  RING_DET_DEPENDENT_COLUMNS_MUL_IDEAL := SessionLibrary.RingDet.«RING_DET_DEPENDENT_COLUMNS_MUL_IDEAL»
  RING_DET_EQ := SessionLibrary.RingDet.«RING_DET_EQ»
  RING_DET_HOMOMORPHISM := SessionLibrary.RingDet.«RING_DET_HOMOMORPHISM»
  RING_DET_I := SessionLibrary.RingDet.«RING_DET_I»
  RING_EPIMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_EPIMORPHISM_IMP_HOMOMORPHISM»
  RING_FRACTIONATE_IN_CARRIER := SessionLibrary.RingTheory.«RING_FRACTIONATE_IN_CARRIER»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_1 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_1»
  RING_HOMOMORPHISM_COMPONENTWISE := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_COMPONENTWISE»
  RING_HOMOMORPHISM_FRACTIONATE := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_FRACTIONATE»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_NEG := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_NEG»
  RING_HOMOMORPHISM_PAIRED := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_PAIRED»
  RING_HOMOMORPHISM_RING_COSET := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_COSET»
  RING_IDEAL_0 := SessionLibrary.RingTheory.«RING_IDEAL_0»
  RING_IDEAL_CARRIER := SessionLibrary.RingTheory.«RING_IDEAL_CARRIER»
  RING_IDEAL_EPIMORPHIC_IMAGE := SessionLibrary.RingTheory.«RING_IDEAL_EPIMORPHIC_IMAGE»
  RING_IDEAL_EQ_CARRIER := SessionLibrary.RingTheory.«RING_IDEAL_EQ_CARRIER»
  RING_IDEAL_HOMOMORPHIC_PREIMAGE := SessionLibrary.RingTheory.«RING_IDEAL_HOMOMORPHIC_PREIMAGE»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IMP_NONEMPTY := SessionLibrary.RingTheory.«RING_IDEAL_IMP_NONEMPTY»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_IDEAL_INTER := SessionLibrary.RingTheory.«RING_IDEAL_INTER»
  RING_IDEAL_ISOMORPHIC_IMAGE_EQ := SessionLibrary.RingTheory.«RING_IDEAL_ISOMORPHIC_IMAGE_EQ»
  RING_IDEAL_QUOTIENT_LMUL := SessionLibrary.RingTheory.«RING_IDEAL_QUOTIENT_LMUL»
  RING_IDEAL_SETADD := SessionLibrary.RingTheory.«RING_IDEAL_SETADD»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_ISOMORPHISM := SessionLibrary.RingTheory.«RING_ISOMORPHISM»
  RING_ISOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_ISOMORPHISM_IMP_HOMOMORPHISM»
  RING_LOCALEQUIV_IN_CARRIER := SessionLibrary.RingTheory.«RING_LOCALEQUIV_IN_CARRIER»
  RING_LOCALEQUIV_SPLIT_EXPLICIT := SessionLibrary.RingTheory.«RING_LOCALEQUIV_SPLIT_EXPLICIT»
  RING_MONOMORPHISM_EPIMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_EPIMORPHISM»
  RING_MONOMORPHISM_EQ_0 := SessionLibrary.RingTheory.«RING_MONOMORPHISM_EQ_0»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_ASSOC := SessionLibrary.RingTheory.«RING_MUL_ASSOC»
  RING_MUL_IN_PRIME_IDEAL := SessionLibrary.RingTheory.«RING_MUL_IN_PRIME_IDEAL»
  RING_MUL_IN_SETMUL := SessionLibrary.RingTheory.«RING_MUL_IN_SETMUL»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_LINV := SessionLibrary.RingTheory.«RING_MUL_LINV»
  RING_MUL_LNEG := SessionLibrary.RingTheory.«RING_MUL_LNEG»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_MUL_SYM := SessionLibrary.RingTheory.«RING_MUL_SYM»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_ADD := SessionLibrary.RingTheory.«RING_POW_ADD»
  RING_PRODUCT := SessionLibrary.RingTheory.«RING_PRODUCT»
  RING_PRODUCT_CLAUSES := SessionLibrary.RingTheory.«RING_PRODUCT_CLAUSES»
  RING_PRODUCT_CLOSED := SessionLibrary.RingTheory.«RING_PRODUCT_CLOSED»
  RING_PRODUCT_EQ := SessionLibrary.RingTheory.«RING_PRODUCT_EQ»
  RING_PRODUCT_IMAGE := SessionLibrary.RingTheory.«RING_PRODUCT_IMAGE»
  RING_SCALE_SETMUL := SessionLibrary.RingTheory.«RING_SCALE_SETMUL»
  RING_SETADD := SessionLibrary.RingTheory.«RING_SETADD»
  RING_SETADD_LSUBSET := SessionLibrary.RingTheory.«RING_SETADD_LSUBSET»
  RING_SETADD_LZERO := SessionLibrary.RingTheory.«RING_SETADD_LZERO»
  RING_SETADD_RSUBSET := SessionLibrary.RingTheory.«RING_SETADD_RSUBSET»
  RING_SETADD_SUBSET_IDEAL := SessionLibrary.RingTheory.«RING_SETADD_SUBSET_IDEAL»
  RING_SETADD_SUPERSET_LEFT := SessionLibrary.RingTheory.«RING_SETADD_SUPERSET_LEFT»
  RING_SETADD_SUPERSET_RIGHT := SessionLibrary.RingTheory.«RING_SETADD_SUPERSET_RIGHT»
  RING_SETMUL := SessionLibrary.RingTheory.«RING_SETMUL»
  RING_SETMUL_ASSOC := SessionLibrary.RingTheory.«RING_SETMUL_ASSOC»
  RING_SETMUL_MONO := SessionLibrary.RingTheory.«RING_SETMUL_MONO»
  RING_SETMUL_SING := SessionLibrary.RingTheory.«RING_SETMUL_SING»
  RING_SETMUL_SUBSET_IDEAL := SessionLibrary.RingTheory.«RING_SETMUL_SUBSET_IDEAL»
  RING_SETMUL_SYM := SessionLibrary.RingTheory.«RING_SETMUL_SYM»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_EQ_0 := SessionLibrary.RingTheory.«RING_SUB_EQ_0»
  RING_SUB_LZERO := SessionLibrary.RingTheory.«RING_SUB_LZERO»
  RING_SUB_RDISTRIB := SessionLibrary.RingTheory.«RING_SUB_RDISTRIB»
  RING_SUB_REFL := SessionLibrary.RingTheory.«RING_SUB_REFL»
  RING_SUB_RZERO := SessionLibrary.RingTheory.«RING_SUB_RZERO»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_0 := SessionLibrary.RingTheory.«RING_SUM_0»
  RING_SUM_ADD := SessionLibrary.RingTheory.«RING_SUM_ADD»
  RING_SUM_CLAUSES := SessionLibrary.RingTheory.«RING_SUM_CLAUSES»
  RING_SUM_CLOSED := SessionLibrary.RingTheory.«RING_SUM_CLOSED»
  RING_SUM_DELTA := SessionLibrary.RingTheory.«RING_SUM_DELTA»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_IMAGE := SessionLibrary.RingTheory.«RING_SUM_IMAGE»
  RING_SUM_LMUL := SessionLibrary.RingTheory.«RING_SUM_LMUL»
  RING_SUM_NEG := SessionLibrary.RingTheory.«RING_SUM_NEG»
  RING_SUM_SUB := SessionLibrary.RingTheory.«RING_SUM_SUB»
  RING_UNIT_1 := SessionLibrary.RingTheory.«RING_UNIT_1»
  SELECT_UNIQUE := Session.SELECT_UNIQUE
  SIMPLE_IMAGE := Session.SIMPLE_IMAGE
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUBSET_ANTISYM_EQ := Session.SUBSET_ANTISYM_EQ
  SUBSET_INTER := Session.SUBSET_INTER
  SUBSET_REFL := Session.SUBSET_REFL
  SUBSET_TRANS := Session.SUBSET_TRANS
  SUBSET_UNION := Session.SUBSET_UNION
  TRANSITIVE_STEPWISE_LE := Session.TRANSITIVE_STEPWISE_LE
  TRIVIAL_RING_10 := SessionLibrary.RingTheory.«TRIVIAL_RING_10»
  UNIONS_MAXIMAL_IDEALS := SessionLibrary.RingTheory.«UNIONS_MAXIMAL_IDEALS»
  UNION_EMPTY := Session.UNION_EMPTY
  UNION_SUBSET := Session.UNION_SUBSET
  WF_IND := Session.WF_IND
  finitely_generated_ideal := SessionLibrary.RingTheory.«finitely_generated_ideal»
  local_ring := SessionLibrary.RingTheory.«local_ring»
  maximal_ideal := SessionLibrary.RingTheory.«maximal_ideal»
  monomial := SessionLibrary.RingTheory.«monomial»
  monomial_mul := SessionLibrary.RingTheory.«monomial_mul»
  monomial_var := SessionLibrary.RingTheory.«monomial_var»
  monomial_vars := SessionLibrary.RingTheory.«monomial_vars»
  num_RECURSION := Session.num_RECURSION
  o_DEF := Session.o_DEF
  o_THM := Session.o_THM
  prime_ideal := SessionLibrary.RingTheory.«prime_ideal»
  radical := SessionLibrary.RingTheory.«radical»
  ring_divides := SessionLibrary.RingTheory.«ring_divides»
  ring_epimorphism := SessionLibrary.RingTheory.«ring_epimorphism»
  ring_fractionate := SessionLibrary.RingTheory.«ring_fractionate»
  ring_homomorphism := SessionLibrary.RingTheory.«ring_homomorphism»
  ring_ideal := SessionLibrary.RingTheory.«ring_ideal»
  ring_kernel := SessionLibrary.RingTheory.«ring_kernel»
  ring_monomorphism := SessionLibrary.RingTheory.«ring_monomorphism»
  ring_pow := SessionLibrary.RingTheory.«ring_pow»
  ring_setadd := SessionLibrary.RingTheory.«ring_setadd»
  ring_setmul := SessionLibrary.RingTheory.«ring_setmul»
  ring_unit := SessionLibrary.RingTheory.«ring_unit»
  trivial_ring := SessionLibrary.RingTheory.«trivial_ring»

/-- What ideal_arith.ml uses from Session. -/
def deps : HolANT.IdealArith.IdealArithDeps where
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
  WF_INDUCT_TAC := Session.WF_INDUCT_TAC
  core1 := core1
  core2 := core2

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in ideal_arith.ml order. -/
initialize BIdealArith01 : HolANT.IdealArith.IdealArith01 ←
  ioB "setupIdealArith01" (HolANT.IdealArith.setupIdealArith01 deps).run
initialize BIdealArith02 : HolANT.IdealArith.IdealArith02 ←
  ioB "setupIdealArith02" (HolANT.IdealArith.setupIdealArith02 deps BIdealArith01).run
initialize BIdealArith03 : HolANT.IdealArith.IdealArith03 ←
  ioB "setupIdealArith03" (HolANT.IdealArith.setupIdealArith03 deps BIdealArith01 BIdealArith02).run
initialize BIdealArith04 : HolANT.IdealArith.IdealArith04 ←
  ioB "setupIdealArith04" (HolANT.IdealArith.setupIdealArith04 deps BIdealArith01 BIdealArith03).run

-- IdealArith01
def ideal_prod : thm := BIdealArith01.ideal_prod
def RING_IDEAL_IDEAL_PROD : thm := BIdealArith01.RING_IDEAL_IDEAL_PROD
def RING_MUL_IN_IDEAL_PROD : thm := BIdealArith01.RING_MUL_IN_IDEAL_PROD
def IDEAL_PROD_MINIMAL : thm := BIdealArith01.IDEAL_PROD_MINIMAL
def IDEAL_PROD_EXPLICIT : thm := BIdealArith01.IDEAL_PROD_EXPLICIT
def IDEAL_PROD_MONO : thm := BIdealArith01.IDEAL_PROD_MONO
def IDEAL_PROD_COMM : thm := BIdealArith01.IDEAL_PROD_COMM
def IDEAL_PROD_IDEAL_GENERATED : thm := BIdealArith01.IDEAL_PROD_IDEAL_GENERATED
def IDEAL_PROD_AC : thm := BIdealArith01.IDEAL_PROD_AC
def IDEAL_PROD_ASSOC : thm := BIdealArith01.IDEAL_PROD_ASSOC
def IDEAL_PROD_SUBSET_LEFT : thm := BIdealArith01.IDEAL_PROD_SUBSET_LEFT
def IDEAL_PROD_SUBSET_RIGHT : thm := BIdealArith01.IDEAL_PROD_SUBSET_RIGHT
def IDEAL_PROD_CARRIER : thm := BIdealArith01.IDEAL_PROD_CARRIER
def IDEAL_PROD_CARRIER_LEFT : thm := BIdealArith01.IDEAL_PROD_CARRIER_LEFT
def IDEAL_PROD_LZERO : thm := BIdealArith01.IDEAL_PROD_LZERO
def IDEAL_PROD_RZERO : thm := BIdealArith01.IDEAL_PROD_RZERO
def IDEAL_PROD_SUBSET_INTER : thm := BIdealArith01.IDEAL_PROD_SUBSET_INTER
def IDEAL_PROD_EQ_CARRIER : thm := BIdealArith01.IDEAL_PROD_EQ_CARRIER
def IDEAL_PROD_EQ_ZERO : thm := BIdealArith01.IDEAL_PROD_EQ_ZERO
def IDEAL_PROD_PRINCIPAL : thm := BIdealArith01.IDEAL_PROD_PRINCIPAL
def IDEAL_PROD_SCALE : thm := BIdealArith01.IDEAL_PROD_SCALE
def IDEAL_PROD_PRINCIPAL_SUBSET_CANCEL : thm := BIdealArith01.IDEAL_PROD_PRINCIPAL_SUBSET_CANCEL
def IDEAL_PROD_PRINCIPAL_CANCEL : thm := BIdealArith01.IDEAL_PROD_PRINCIPAL_CANCEL
def IDEAL_PROD_PRINCIPAL_FACTOR : thm := BIdealArith01.IDEAL_PROD_PRINCIPAL_FACTOR
def IDEAL_PROD_SETADD_LDISTRIB : thm := BIdealArith01.IDEAL_PROD_SETADD_LDISTRIB
def IDEAL_PROD_SETADD_RDISTRIB : thm := BIdealArith01.IDEAL_PROD_SETADD_RDISTRIB
def IDEAL_PROD_SUBSET_PRIME_IDEAL : thm := BIdealArith01.IDEAL_PROD_SUBSET_PRIME_IDEAL
def IDEAL_PROD_SETADD_SUBSET : thm := BIdealArith01.IDEAL_PROD_SETADD_SUBSET
def MAXIMAL_IDEAL_COMAXIMAL : thm := BIdealArith01.MAXIMAL_IDEAL_COMAXIMAL
def MAXIMAL_IDEAL_COMAXIMAL_MUL : thm := BIdealArith01.MAXIMAL_IDEAL_COMAXIMAL_MUL
def IDEAL_PROD_COMAXIMAL : thm := BIdealArith01.IDEAL_PROD_COMAXIMAL
def COMAXIMAL_IDEAL_PROD : thm := BIdealArith01.COMAXIMAL_IDEAL_PROD
def CHINESE_REMAINDER_RING_ISOMORPHISM : thm := BIdealArith01.CHINESE_REMAINDER_RING_ISOMORPHISM
def RING_ISOMORPHISM_PROD_QUOTIENT_RING : thm := BIdealArith01.RING_ISOMORPHISM_PROD_QUOTIENT_RING
def RING_ISOMORPHISM_QUOTIENT_RING_INTER : thm := BIdealArith01.RING_ISOMORPHISM_QUOTIENT_RING_INTER
def ideal_quotient : thm := BIdealArith01.ideal_quotient
def RING_IDEAL_IDEAL_QUOTIENT : thm := BIdealArith01.RING_IDEAL_IDEAL_QUOTIENT
def SUBSET_IDEAL_QUOTIENT : thm := BIdealArith01.SUBSET_IDEAL_QUOTIENT
def IDEAL_SUBSET_IDEAL_QUOTIENT : thm := BIdealArith01.IDEAL_SUBSET_IDEAL_QUOTIENT
def IDEAL_QUOTIENT_MONO : thm := BIdealArith01.IDEAL_QUOTIENT_MONO
def IDEAL_QUOTIENT_EQ_CARRIER : thm := BIdealArith01.IDEAL_QUOTIENT_EQ_CARRIER
def IDEAL_QUOTIENT_CARRIER : thm := BIdealArith01.IDEAL_QUOTIENT_CARRIER

-- IdealArith02
def IDEAL_QUOTIENT_IDEAL_PROD : thm := BIdealArith02.IDEAL_QUOTIENT_IDEAL_PROD
def IDEAL_QUOTIENT_SETADD : thm := BIdealArith02.IDEAL_QUOTIENT_SETADD
def IDEAL_QUOTIENT_INTER : thm := BIdealArith02.IDEAL_QUOTIENT_INTER
def IDEAL_QUOTIENT_PRIME_IDEAL : thm := BIdealArith02.IDEAL_QUOTIENT_PRIME_IDEAL
def ideal_pow : thm := BIdealArith02.ideal_pow
def IDEAL_POW_0 : thm := BIdealArith02.IDEAL_POW_0
def IDEAL_POW_SUC : thm := BIdealArith02.IDEAL_POW_SUC
def IDEAL_POW_ALT : thm := BIdealArith02.IDEAL_POW_ALT
def IDEAL_POW_1 : thm := BIdealArith02.IDEAL_POW_1
def IDEAL_POW_CARRIER : thm := BIdealArith02.IDEAL_POW_CARRIER
def RING_IDEAL_IDEAL_POW : thm := BIdealArith02.RING_IDEAL_IDEAL_POW
def IDEAL_POW_ADD : thm := BIdealArith02.IDEAL_POW_ADD
def IDEAL_POW_MUL : thm := BIdealArith02.IDEAL_POW_MUL
def RING_MUL_IN_IDEAL_POW : thm := BIdealArith02.RING_MUL_IN_IDEAL_POW
def RING_POW_IN_IDEAL_POW : thm := BIdealArith02.RING_POW_IN_IDEAL_POW
def IDEAL_POW_MONO : thm := BIdealArith02.IDEAL_POW_MONO
def IDEAL_POW_ANTIMONO : thm := BIdealArith02.IDEAL_POW_ANTIMONO
def IDEAL_POW_SUC_SUBSET : thm := BIdealArith02.IDEAL_POW_SUC_SUBSET
def IDEAL_POW_HOMOMORPHIC_IMAGE_SUBSET : thm := BIdealArith02.IDEAL_POW_HOMOMORPHIC_IMAGE_SUBSET
def IDEAL_POW_IDEAL_PROD : thm := BIdealArith02.IDEAL_POW_IDEAL_PROD
def IDEAL_POW_PRINCIPAL : thm := BIdealArith02.IDEAL_POW_PRINCIPAL
def IDEAL_POW_EQ_ZERO : thm := BIdealArith02.IDEAL_POW_EQ_ZERO
def IDEAL_POW_SUBSET_PRIME_IDEAL : thm := BIdealArith02.IDEAL_POW_SUBSET_PRIME_IDEAL
def RADICAL_IDEAL_PROD : thm := BIdealArith02.RADICAL_IDEAL_PROD
def RADICAL_IDEAL_POW : thm := BIdealArith02.RADICAL_IDEAL_POW
def RADICAL_PRIME_IDEAL_POW : thm := BIdealArith02.RADICAL_PRIME_IDEAL_POW
def COMAXIMAL_IDEAL_POW : thm := BIdealArith02.COMAXIMAL_IDEAL_POW
def IDEAL_POW_SETADD_SUBSET : thm := BIdealArith02.IDEAL_POW_SETADD_SUBSET
def ideal_product : thm := BIdealArith02.ideal_product
def RING_IDEAL_IDEAL_PRODUCT : thm := BIdealArith02.RING_IDEAL_IDEAL_PRODUCT
def RING_PRODUCT_IN_IDEAL_PRODUCT : thm := BIdealArith02.RING_PRODUCT_IN_IDEAL_PRODUCT
def IDEAL_PRODUCT_EMPTY : thm := BIdealArith02.IDEAL_PRODUCT_EMPTY
def IDEAL_PRODUCT_EQ : thm := BIdealArith02.IDEAL_PRODUCT_EQ
def IDEAL_PRODUCT_INSERT : thm := BIdealArith02.IDEAL_PRODUCT_INSERT
def IDEAL_PRODUCT_SING : thm := BIdealArith02.IDEAL_PRODUCT_SING
def IDEAL_PRODUCT_MONO : thm := BIdealArith02.IDEAL_PRODUCT_MONO
def IDEAL_PRODUCT_SUBSET : thm := BIdealArith02.IDEAL_PRODUCT_SUBSET
def IDEAL_PRODUCT_SUPERSET : thm := BIdealArith02.IDEAL_PRODUCT_SUPERSET
def IDEAL_PRODUCT_MUL : thm := BIdealArith02.IDEAL_PRODUCT_MUL
def IDEAL_PRODUCT_EQ_ZERO : thm := BIdealArith02.IDEAL_PRODUCT_EQ_ZERO
def IDEAL_PRODUCT_SUBSET_PRIME_IDEAL : thm := BIdealArith02.IDEAL_PRODUCT_SUBSET_PRIME_IDEAL
def COMAXIMAL_IDEAL_PRODUCT : thm := BIdealArith02.COMAXIMAL_IDEAL_PRODUCT
def CHINESE_REMAINDER_IDEALS : thm := BIdealArith02.CHINESE_REMAINDER_IDEALS
def IDEAL_PRODUCT_MONOMIAL_MUL : thm := BIdealArith02.IDEAL_PRODUCT_MONOMIAL_MUL
def IDEAL_PRODUCT_SETADD_SUBSET : thm := BIdealArith02.IDEAL_PRODUCT_SETADD_SUBSET
def IDEAL_PRODUCT_PRINCIPAL : thm := BIdealArith02.IDEAL_PRODUCT_PRINCIPAL
def IDEAL_PRODUCT_POW_SETADD_SUBSET : thm := BIdealArith02.IDEAL_PRODUCT_POW_SETADD_SUBSET
def IDEAL_PRODUCT_IMAGE : thm := BIdealArith02.IDEAL_PRODUCT_IMAGE
def IDEAL_GENERATED_IMAGE_IDEAL_GENERATED : thm := BIdealArith02.IDEAL_GENERATED_IMAGE_IDEAL_GENERATED
def IDEAL_PROD_HOMOMORPHIC_IMAGE : thm := BIdealArith02.IDEAL_PROD_HOMOMORPHIC_IMAGE
def IDEAL_PROD_EPIMORPHIC_IMAGE : thm := BIdealArith02.IDEAL_PROD_EPIMORPHIC_IMAGE
def RING_FRACTIONATE_IN_IDEAL_PROD : thm := BIdealArith02.RING_FRACTIONATE_IN_IDEAL_PROD
def RING_LOCALIZATION_IDEAL_PROD_SUBSET : thm := BIdealArith02.RING_LOCALIZATION_IDEAL_PROD_SUBSET
def IDEAL_POW_HOMOMORPHIC_IMAGE : thm := BIdealArith02.IDEAL_POW_HOMOMORPHIC_IMAGE

-- IdealArith03
def RING_ISOMORPHISM_IDEAL_POW : thm := BIdealArith03.RING_ISOMORPHISM_IDEAL_POW
def IDEAL_PRODUCT_HOMOMORPHIC_IMAGE : thm := BIdealArith03.IDEAL_PRODUCT_HOMOMORPHIC_IMAGE
def IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0 : thm := BIdealArith03.IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0
def IDEAL_EXTENSION_POW_SUPPLEMENT : thm := BIdealArith03.IDEAL_EXTENSION_POW_SUPPLEMENT
def IDEAL_PRODUCT_COMAXIMAL : thm := BIdealArith03.IDEAL_PRODUCT_COMAXIMAL
def CHINESE_REMAINDER_PRODUCT_RING : thm := BIdealArith03.CHINESE_REMAINDER_PRODUCT_RING
def NOETHERIAN_RING_INDUCT : thm := BIdealArith03.NOETHERIAN_RING_INDUCT
def NOETHERIAN_PRIME_PRODUCT_SUBSET : thm := BIdealArith03.NOETHERIAN_PRIME_PRODUCT_SUBSET
def PRIME_AVOIDANCE : thm := BIdealArith03.PRIME_AVOIDANCE
def IDEAL_PROD_IDEAL_GENERATED_FINITE : thm := BIdealArith03.IDEAL_PROD_IDEAL_GENERATED_FINITE
def NAKAYAMA_LEMMA : thm := BIdealArith03.NAKAYAMA_LEMMA
def NAKAYAMA_LEMMA_MAXIMAL : thm := BIdealArith03.NAKAYAMA_LEMMA_MAXIMAL
def NAKAYAMA_LEMMA_LOCAL : thm := BIdealArith03.NAKAYAMA_LEMMA_LOCAL

-- IdealArith04
def LOCAL_RING_GENERATORS_EXCHANGE : thm := BIdealArith04.LOCAL_RING_GENERATORS_EXCHANGE
def FINITELY_GENERATED_IDEAL_IDEMPOTENT : thm := BIdealArith04.FINITELY_GENERATED_IDEAL_IDEMPOTENT

/-- `needs "ANT/ideal_arith.ml"`: already done by importing this module. -/
def ensureIdealArith : IO Unit := pure ()

end SessionANT.IdealArith
