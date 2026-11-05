/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/ringtheory.ml.                            -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/RingTheory.lean

  The session half of the ringtheory.ml translation: it supplies
  HolLibrary.RingTheory's dependencies from Session and the parent
  libraries, and exports every name under its HOL Light name.  Importing
  this module is `needs "Library/ringtheory.ml"`; its `needs` of
  binomial.ml, pocklington.ml and card.ml are the imports of those modules.
  The parents' theorems are filled from their SessionLibrary modules, the
  last-loaded first, as OCaml's shadowing.  Each bundle is built by
  `initialize` when the module is loaded, in file order.
-/

import Session
import HolLibrary.RingTheory
import SessionLibrary.Binomial
import SessionLibrary.Pocklington
import SessionLibrary.Card

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.RingTheory

/-- The core theorems ringtheory.ml uses. -/
def core1 : HolLibrary.RingTheory.CoreThms1 where
  ADD1 := Session.ADD1
  ADD_CLAUSES := Session.ADD_CLAUSES
  ADD_EQ_0 := Session.ADD_EQ_0
  ADD_SUB := Session.ADD_SUB
  ADD_SUB2 := Session.ADD_SUB2
  ADD_SYM := Session.ADD_SYM
  AND_FORALL_THM := Session.AND_FORALL_THM
  ARITH := Session.ARITH
  ARITH_EQ := Session.ARITH_EQ
  BETA_THM := Session.BETA_THM
  BIJ := Session.BIJ
  BINOM_LT := SessionLibrary.Binomial.«BINOM_LT»
  BINOM_REFL := SessionLibrary.Binomial.«BINOM_REFL»
  CARD_ADD_C := SessionLibrary.Card.«CARD_ADD_C»
  CARD_ADD_FINITE_EQ := SessionLibrary.Card.«CARD_ADD_FINITE_EQ»
  CARD_BOOL := Session.CARD_BOOL
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARD_CROSS := Session.CARD_CROSS
  CARD_DELETE := Session.CARD_DELETE
  CARD_EQ_0 := Session.CARD_EQ_0
  CARD_EQ_CARD := SessionLibrary.Card.«CARD_EQ_CARD»
  CARD_EQ_CARD_IMP := SessionLibrary.Card.«CARD_EQ_CARD_IMP»
  CARD_EQ_CONG := SessionLibrary.Card.«CARD_EQ_CONG»
  CARD_EQ_EXP_INFINITE_FINITE := SessionLibrary.Card.«CARD_EQ_EXP_INFINITE_FINITE»
  CARD_EQ_FUNSPACE := SessionLibrary.Card.«CARD_EQ_FUNSPACE»
  CARD_EQ_IMAGE := SessionLibrary.Card.«CARD_EQ_IMAGE»
  CARD_EQ_IMAGE_MUL_FIBRES := SessionLibrary.Card.«CARD_EQ_IMAGE_MUL_FIBRES»
  CARD_EQ_IMP_LE := SessionLibrary.Card.«CARD_EQ_IMP_LE»
  CARD_EQ_INFINITE := SessionLibrary.Card.«CARD_EQ_INFINITE»
  CARD_EQ_REFL := SessionLibrary.Card.«CARD_EQ_REFL»
  CARD_EQ_REFL_IMP := SessionLibrary.Card.«CARD_EQ_REFL_IMP»
  CARD_EQ_RESTRICTED_FUNSPACE_INFINITE := SessionLibrary.Card.«CARD_EQ_RESTRICTED_FUNSPACE_INFINITE»
  CARD_EQ_SYM := SessionLibrary.Card.«CARD_EQ_SYM»
  CARD_EQ_TRANS := SessionLibrary.Card.«CARD_EQ_TRANS»
  CARD_EXP_ABSORB := SessionLibrary.Card.«CARD_EXP_ABSORB»
  CARD_EXP_CANTOR := SessionLibrary.Card.«CARD_EXP_CANTOR»
  CARD_EXP_CONG := SessionLibrary.Card.«CARD_EXP_CONG»
  CARD_EXP_UNIV := SessionLibrary.Card.«CARD_EXP_UNIV»
  CARD_FINITE_CONG := SessionLibrary.Card.«CARD_FINITE_CONG»
  CARD_HAS_SIZE_CONG := SessionLibrary.Card.«CARD_HAS_SIZE_CONG»
  CARD_IMAGE_EQ_INJ := Session.CARD_IMAGE_EQ_INJ
  CARD_IMAGE_INJ := Session.CARD_IMAGE_INJ
  CARD_IMAGE_LE := Session.CARD_IMAGE_LE
  CARD_LE_ANTISYM := SessionLibrary.Card.«CARD_LE_ANTISYM»
  CARD_LE_CARD := SessionLibrary.Card.«CARD_LE_CARD»
  CARD_LE_EQ_SUBSET := SessionLibrary.Card.«CARD_LE_EQ_SUBSET»
  CARD_LE_FINITE := SessionLibrary.Card.«CARD_LE_FINITE»
  CARD_LE_MUL := SessionLibrary.Card.«CARD_LE_MUL»
  CARD_LE_REFL := SessionLibrary.Card.«CARD_LE_REFL»
  CARD_LE_SUBSET := SessionLibrary.Card.«CARD_LE_SUBSET»
  CARD_LE_TRANS := SessionLibrary.Card.«CARD_LE_TRANS»
  CARD_LT_IMP_LE := SessionLibrary.Card.«CARD_LT_IMP_LE»
  CARD_MUL_ABSORB := SessionLibrary.Card.«CARD_MUL_ABSORB»
  CARD_MUL_CONG := SessionLibrary.Card.«CARD_MUL_CONG»
  CARD_MUL_FINITE_EQ := SessionLibrary.Card.«CARD_MUL_FINITE_EQ»
  CARD_MUL_LID := SessionLibrary.Card.«CARD_MUL_LID»
  CARD_MUL_SYM := SessionLibrary.Card.«CARD_MUL_SYM»
  CARD_NUMSEG_1 := Session.CARD_NUMSEG_1
  CARD_NUMSEG_LT := Session.CARD_NUMSEG_LT
  CARD_PSUBSET := Session.CARD_PSUBSET
  CARD_SING_LE := SessionLibrary.Card.«CARD_SING_LE»
  CARD_SUBSET := Session.CARD_SUBSET
  CARD_SUBSET_EQ := Session.CARD_SUBSET_EQ
  CARD_SUBSET_LE := Session.CARD_SUBSET_LE
  CARD_UNIONS := Session.CARD_UNIONS
  CARD_UNION_LE := Session.CARD_UNION_LE
  CARTESIAN_PRODUCT_AS_RESTRICTIONS := Session.CARTESIAN_PRODUCT_AS_RESTRICTIONS
  CARTESIAN_PRODUCT_CONST := SessionLibrary.Card.«CARTESIAN_PRODUCT_CONST»
  CARTESIAN_PRODUCT_EQ := Session.CARTESIAN_PRODUCT_EQ
  CARTESIAN_PRODUCT_EQ_EMPTY := Session.CARTESIAN_PRODUCT_EQ_EMPTY
  CARTESIAN_PRODUCT_SINGS_GEN := Session.CARTESIAN_PRODUCT_SINGS_GEN
  COND_CLAUSES := Session.COND_CLAUSES
  COND_ID := Session.COND_ID
/-- The core theorems ringtheory.ml uses. -/
def core2 : HolLibrary.RingTheory.CoreThms2 where
  COND_RAND := Session.COND_RAND
  COND_RATOR := Session.COND_RATOR
  COND_SWAP := Session.COND_SWAP
  CONG := Session.CONG
  CONG_IMP_EQ := SessionLibrary.Pocklington.«CONG_IMP_EQ»
  CONG_SYM := SessionLibrary.Pocklington.«CONG_SYM»
  CONJ_ACI := Session.CONJ_ACI
  CONJ_ASSOC := Session.CONJ_ASSOC
  CONJ_SYM := Session.CONJ_SYM
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  COPRIME_0 := SessionLibrary.Prime.«COPRIME_0»
  COPRIME_GCD := SessionLibrary.Prime.«COPRIME_GCD»
  COPRIME_SYM := SessionLibrary.Prime.«COPRIME_SYM»
  COUNTABLE_CASES := SessionLibrary.Card.«COUNTABLE_CASES»
  CROSS := Session.CROSS
  CROSS_EQ := Session.CROSS_EQ
  CROSS_SING := Session.CROSS_SING
  CROSS_UNIV := Session.CROSS_UNIV
  DEPENDENT_CHOICE := Session.DEPENDENT_CHOICE
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DIFF_RESTRICT := Session.DIFF_RESTRICT
  DISJOINT := Session.DISJOINT
  DISJOINT_EMPTY_REFL := Session.DISJOINT_EMPTY_REFL
  DISJOINT_SING := Session.DISJOINT_SING
  DISJOINT_SYM := Session.DISJOINT_SYM
  DISJ_ACI := Session.DISJ_ACI
  DISJ_ASSOC := Session.DISJ_ASSOC
  DISJ_SYM := Session.DISJ_SYM
  DIVIDES_0 := SessionLibrary.Prime.«DIVIDES_0»
  DIVIDES_1 := SessionLibrary.Prime.«DIVIDES_1»
  DIVIDES_ANTISYM := Session.DIVIDES_ANTISYM
  DIVIDES_EXP_LE_IMP := SessionLibrary.Prime.«DIVIDES_EXP_LE_IMP»
  DIVIDES_LCM_GCD := SessionLibrary.Prime.«DIVIDES_LCM_GCD»
  DIVIDES_LCM_LEFT := SessionLibrary.Prime.«DIVIDES_LCM_LEFT»
  DIVIDES_LE := Session.DIVIDES_LE
  DIVIDES_LMUL := SessionLibrary.Prime.«DIVIDES_LMUL»
  DIVIDES_ONE := Session.DIVIDES_ONE
  DIVIDES_PRIME_BINOM := SessionLibrary.Binomial.«DIVIDES_PRIME_BINOM»
  DIVIDES_REFL := SessionLibrary.Prime.«DIVIDES_REFL»
  DIVIDES_ZERO := SessionLibrary.Prime.«DIVIDES_ZERO»
  DIVISION := Session.DIVISION
  DIVISION_SIMP := Session.DIVISION_SIMP
  DIV_LT := Session.DIV_LT
  DIV_MULT := Session.DIV_MULT
  DIV_MULT_ADD := Session.DIV_MULT_ADD
  EMPTY_GSPEC := Session.EMPTY_GSPEC
  EMPTY_NUMSEG := Session.EMPTY_NUMSEG
  EMPTY_SUBSET := Session.EMPTY_SUBSET
  EMPTY_UNIONS := Session.EMPTY_UNIONS
  EQ_ADD_LCANCEL := Session.EQ_ADD_LCANCEL
  EQ_ADD_LCANCEL_0 := Session.EQ_ADD_LCANCEL_0
  EQ_ADD_RCANCEL := Session.EQ_ADD_RCANCEL
  EQ_ADD_RCANCEL_0 := Session.EQ_ADD_RCANCEL_0
  EQ_C_BIJECTIONS := SessionLibrary.Card.«EQ_C_BIJECTIONS»
  EQ_IMP := Session.EQ_IMP
  EQ_IMP_LE := Session.EQ_IMP_LE
  EQ_MULT_LCANCEL := Session.EQ_MULT_LCANCEL
  EQ_SYM_EQ := Session.EQ_SYM_EQ
  EQ_TRANS := Session.EQ_TRANS
  ETA_AX := Session.ETA_AX
  EVEN := Session.EVEN
  EVEN_EXISTS := Session.EVEN_EXISTS
  EXISTS_BOOL_THM := Session.EXISTS_BOOL_THM
  EXISTS_CARTESIAN_PRODUCT_ELEMENT := Session.EXISTS_CARTESIAN_PRODUCT_ELEMENT
  EXISTS_FINITE_SUBSET_IMAGE := Session.EXISTS_FINITE_SUBSET_IMAGE
  EXISTS_IN_GSPEC := Session.EXISTS_IN_GSPEC
  EXISTS_IN_IMAGE := Session.EXISTS_IN_IMAGE
  EXISTS_IN_INSERT := Session.EXISTS_IN_INSERT
  EXISTS_OR_THM := Session.EXISTS_OR_THM
  EXISTS_PAIR_THM := Session.EXISTS_PAIR_THM
  EXISTS_REFL := Session.EXISTS_REFL
  EXISTS_UNIQUE := Session.EXISTS_UNIQUE
  EXISTS_UNIQUE_DEF := Session.EXISTS_UNIQUE_DEF
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXISTS_UNIQUE_UNIONS_INTERS := Session.EXISTS_UNIQUE_UNIONS_INTERS
  EXISTS_UNPAIR_THM := Session.EXISTS_UNPAIR_THM
  EXP := Session.EXP
  EXTENSION := Session.EXTENSION
  EXTENSIONAL := Session.EXTENSIONAL
/-- The core theorems ringtheory.ml uses. -/
def core3 : HolLibrary.RingTheory.CoreThms3 where
  EXTENSIONAL_UNIV := Session.EXTENSIONAL_UNIV
  FINITE_1 := Session.FINITE_1
  FINITE_BOOL := Session.FINITE_BOOL
  FINITE_CARTESIAN_PRODUCT := SessionLibrary.Card.«FINITE_CARTESIAN_PRODUCT»
  FINITE_CROSS := Session.FINITE_CROSS
  FINITE_CROSS_EQ := Session.FINITE_CROSS_EQ
  FINITE_DELETE := Session.FINITE_DELETE
  FINITE_DIFF := Session.FINITE_DIFF
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_FUNSPACE := Session.FINITE_FUNSPACE
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_IMAGE_INJ_EQ := Session.FINITE_IMAGE_INJ_EQ
  FINITE_IMP_COUNTABLE := SessionLibrary.Card.«FINITE_IMP_COUNTABLE»
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_INTER := Session.FINITE_INTER
  FINITE_INT_SEG := Session.FINITE_INT_SEG
  FINITE_NUMSEG := Session.FINITE_NUMSEG
  FINITE_NUMSEG_LE := Session.FINITE_NUMSEG_LE
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_POWERSET := Session.FINITE_POWERSET
  FINITE_PRODUCT_DEPENDENT := Session.FINITE_PRODUCT_DEPENDENT
  FINITE_RESTRICT := Session.FINITE_RESTRICT
  FINITE_RULES := Session.FINITE_RULES
  FINITE_SING := Session.FINITE_SING
  FINITE_SUBSET := Session.FINITE_SUBSET
  FINITE_SUBSET_NUMSEG := Session.FINITE_SUBSET_NUMSEG
  FINITE_SUBSET_UNIONS_CHAIN := Session.FINITE_SUBSET_UNIONS_CHAIN
  FINITE_SUBSET_UNIONS_DIRECTED_EQ := Session.FINITE_SUBSET_UNIONS_DIRECTED_EQ
  FINITE_UNION := Session.FINITE_UNION
  FINITE_UNIONS := Session.FINITE_UNIONS
  FLD_RESTRICT_QOSET := SessionLibrary.Wo.«FLD_RESTRICT_QOSET»
  FORALL_AND_THM := Session.FORALL_AND_THM
  FORALL_BOOL_THM := Session.FORALL_BOOL_THM
  FORALL_CARTESIAN_PRODUCT_ELEMENTS := Session.FORALL_CARTESIAN_PRODUCT_ELEMENTS
  FORALL_CARTESIAN_PRODUCT_ELEMENTS_EQ := Session.FORALL_CARTESIAN_PRODUCT_ELEMENTS_EQ
  FORALL_FINITE_SUBSET_IMAGE := Session.FORALL_FINITE_SUBSET_IMAGE
  FORALL_INT_CASES := Session.FORALL_INT_CASES
  FORALL_IN_CROSS := Session.FORALL_IN_CROSS
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_IN_IMAGE_2 := Session.FORALL_IN_IMAGE_2
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  FORALL_IN_UNION := Session.FORALL_IN_UNION
  FORALL_IN_UNIONS := Session.FORALL_IN_UNIONS
  FORALL_ONE_THM := Session.FORALL_ONE_THM
  FORALL_PAIR_FUN_THM := Session.FORALL_PAIR_FUN_THM
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  FORALL_UNPAIR_THM := Session.FORALL_UNPAIR_THM
  FORALL_UNWIND_THM1 := Session.FORALL_UNWIND_THM1
  FORALL_UNWIND_THM2 := Session.FORALL_UNWIND_THM2
  FUNCTION_FACTORS_LEFT_GEN := Session.FUNCTION_FACTORS_LEFT_GEN
  FUN_EQ_THM := Session.FUN_EQ_THM
  FUN_IN_IMAGE := Session.FUN_IN_IMAGE
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_0 := Session.HAS_SIZE_0
  HAS_SIZE_1 := Session.HAS_SIZE_1
  HAS_SIZE_BOOL := Session.HAS_SIZE_BOOL
  HAS_SIZE_FUNSPACE := Session.HAS_SIZE_FUNSPACE
  HAS_SIZE_IMAGE_INJ := Session.HAS_SIZE_IMAGE_INJ
  HAS_SIZE_NUMSEG_LT := Session.HAS_SIZE_NUMSEG_LT
  IMAGE := Session.IMAGE
  IMAGE_CLAUSES := Session.IMAGE_CLAUSES
  IMAGE_CONST := Session.IMAGE_CONST
  IMAGE_EQ := Session.IMAGE_EQ
  IMAGE_EQ_EMPTY := Session.IMAGE_EQ_EMPTY
  IMAGE_FST_CROSS := Session.IMAGE_FST_CROSS
  IMAGE_I := Session.IMAGE_I
  IMAGE_ID := Session.IMAGE_ID
  IMAGE_PAIRED_CROSS := Session.IMAGE_PAIRED_CROSS
  IMAGE_PROJECTION_CARTESIAN_PRODUCT := Session.IMAGE_PROJECTION_CARTESIAN_PRODUCT
  IMAGE_SND_CROSS := Session.IMAGE_SND_CROSS
  IMAGE_SUBSET := Session.IMAGE_SUBSET
/-- The core theorems ringtheory.ml uses. -/
def core4 : HolLibrary.RingTheory.CoreThms4 where
  IMAGE_UNION := Session.IMAGE_UNION
  IMAGE_o := Session.IMAGE_o
  IMP_CONJ := Session.IMP_CONJ
  IMP_CONJ_ALT := Session.IMP_CONJ_ALT
  IMP_IMP := Session.IMP_IMP
  IN := Session.IN
  INFINITE := Session.INFINITE
  INFINITE_CARD_LE := SessionLibrary.Card.«INFINITE_CARD_LE»
  INFINITE_CROSS_UNIV := Session.INFINITE_CROSS_UNIV
  INFINITE_IMAGE := Session.INFINITE_IMAGE
  INFINITE_IMAGE_INJ := Session.INFINITE_IMAGE_INJ
  INFINITE_SUPERSET := Session.INFINITE_SUPERSET
  INJ := Session.INJ
  INJECTIVE_ALT := Session.INJECTIVE_ALT
  INJECTIVE_ON_ALT := Session.INJECTIVE_ON_ALT
  INJECTIVE_ON_LEFT_INVERSE := Session.INJECTIVE_ON_LEFT_INVERSE
  INSERT_DELETE := Session.INSERT_DELETE
  INSERT_RESTRICT := Session.INSERT_RESTRICT
  INSERT_SUBSET := Session.INSERT_SUBSET
  INTERS_1 := Session.INTERS_1
  INTERS_ANTIMONO_GEN := Session.INTERS_ANTIMONO_GEN
  INTERS_GSPEC := Session.INTERS_GSPEC
  INTER_ASSOC := Session.INTER_ASSOC
  INTER_COMM := Session.INTER_COMM
  INTER_CROSS := Session.INTER_CROSS
  INTER_RESTRICT := Session.INTER_RESTRICT
  INTER_SUBSET := Session.INTER_SUBSET
  INTER_UNIONS := Session.INTER_UNIONS
  INT_ABS_NUM := Session.INT_ABS_NUM
  INT_ABS_POS := Session.INT_ABS_POS
  INT_ADD_LID := Session.INT_ADD_LID
  INT_ADD_LINV := Session.INT_ADD_LINV
  INT_ADD_REM := Session.INT_ADD_REM
  INT_ADD_RID := Session.INT_ADD_RID
  INT_CONG_IMP_EQ := Session.INT_CONG_IMP_EQ
  INT_CONG_LREM := Session.INT_CONG_LREM
  INT_CONG_RREM := Session.INT_CONG_RREM
  INT_DIVIDES_RABS := Session.INT_DIVIDES_RABS
  INT_DIVISION := Session.INT_DIVISION
  INT_ENTIRE := Session.INT_ENTIRE
  INT_EXISTS_POS := Session.INT_EXISTS_POS
  INT_FORALL_ABS := Session.INT_FORALL_ABS
  INT_FORALL_POS := Session.INT_FORALL_POS
  INT_LE_REFL := Session.INT_LE_REFL
  INT_LT_REM := Session.INT_LT_REM
  INT_LT_REM_EQ := Session.INT_LT_REM_EQ
  INT_MUL_EQ_1 := Session.INT_MUL_EQ_1
  INT_MUL_LID := Session.INT_MUL_LID
  INT_MUL_LNEG := Session.INT_MUL_LNEG
  INT_MUL_REM := Session.INT_MUL_REM
  INT_MUL_RNEG := Session.INT_MUL_RNEG
  INT_MUL_RZERO := Session.INT_MUL_RZERO
  INT_NEG_0 := Session.INT_NEG_0
  INT_NEG_ADD := Session.INT_NEG_ADD
  INT_NEG_EQ := Session.INT_NEG_EQ
  INT_NEG_NEG := Session.INT_NEG_NEG
  INT_NEG_REM := Session.INT_NEG_REM
  INT_OF_NUM_ADD := Session.INT_OF_NUM_ADD
  INT_OF_NUM_CLAUSES := Session.INT_OF_NUM_CLAUSES
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_EXISTS := Session.INT_OF_NUM_EXISTS
  INT_OF_NUM_LE := Session.INT_OF_NUM_LE
  INT_OF_NUM_LT := Session.INT_OF_NUM_LT
  INT_OF_NUM_MUL := Session.INT_OF_NUM_MUL
  INT_OF_NUM_OF_INT := Session.INT_OF_NUM_OF_INT
  INT_OF_NUM_REM := Session.INT_OF_NUM_REM
  INT_OF_NUM_SUC := Session.INT_OF_NUM_SUC
  INT_POS := Session.INT_POS
  INT_POW := Session.INT_POW
  INT_POW2_ABS := Session.INT_POW2_ABS
  INT_REM_0 := Session.INT_REM_0
  INT_REM_1 := Session.INT_REM_1
/-- The core theorems ringtheory.ml uses. -/
def core5 : HolLibrary.RingTheory.CoreThms5 where
  INT_REM_EQ := Session.INT_REM_EQ
  INT_REM_EQ_SELF := Session.INT_REM_EQ_SELF
  INT_REM_LT := Session.INT_REM_LT
  INT_REM_POS := Session.INT_REM_POS
  INT_REM_POS_EQ := Session.INT_REM_POS_EQ
  INT_REM_REFL := Session.INT_REM_REFL
  INT_REM_REM := Session.INT_REM_REM
  INT_REM_REM_MUL := Session.INT_REM_REM_MUL
  INT_REM_ZERO := Session.INT_REM_ZERO
  INT_SUB := Session.INT_SUB
  INVERSE_MOD_BOUND := SessionLibrary.Pocklington.«INVERSE_MOD_BOUND»
  INVERSE_MOD_RMUL_EQ := SessionLibrary.Pocklington.«INVERSE_MOD_RMUL_EQ»
  INVERSE_MOD_UNIQUE := SessionLibrary.Pocklington.«INVERSE_MOD_UNIQUE»
  IN_CARTESIAN_PRODUCT := Session.IN_CARTESIAN_PRODUCT
  IN_CROSS := Session.IN_CROSS
  IN_DELETE := Session.IN_DELETE
  IN_DIFF := Session.IN_DIFF
  IN_DISJOINT := Session.IN_DISJOINT
  IN_ELIM_PAIR_THM := Session.IN_ELIM_PAIR_THM
  IN_ELIM_QUAD_THM := Session.IN_ELIM_QUAD_THM
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_ELIM_TRIPLE_THM := Session.IN_ELIM_TRIPLE_THM
  IN_GSPEC := Session.IN_GSPEC
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_INTER := Session.IN_INTER
  IN_INTERS := Session.IN_INTERS
  IN_NUMSEG := Session.IN_NUMSEG
  IN_SING := Session.IN_SING
  IN_UNION := Session.IN_UNION
  IN_UNIONS := Session.IN_UNIONS
  IN_UNIV := Session.IN_UNIV
  ITERATE_CLAUSES := Session.ITERATE_CLAUSES
  ITERATE_CLOSED := Session.ITERATE_CLOSED
  ITERATE_DIFF := Session.ITERATE_DIFF
  ITERATE_EQ := Session.ITERATE_EQ
  ITERATE_IMAGE := Session.ITERATE_IMAGE
  ITERATE_IMAGE_GEN := Session.ITERATE_IMAGE_GEN
  ITERATE_INCL_EXCL := Session.ITERATE_INCL_EXCL
  ITERATE_ITERATE_PRODUCT := Session.ITERATE_ITERATE_PRODUCT
  ITERATE_REFLECT := Session.ITERATE_REFLECT
  ITERATE_SUPERSET := Session.ITERATE_SUPERSET
  ITERATE_SUPPORT := Session.ITERATE_SUPPORT
  ITERATE_UNION := Session.ITERATE_UNION
  I_DEF := Session.I_DEF
  I_O_ID := Session.I_O_ID
  I_THM := Session.I_THM
  LAMBDA_PAIR := Session.LAMBDA_PAIR
  LAMBDA_PAIR_THM := Session.LAMBDA_PAIR_THM
  LCM := SessionLibrary.Prime.«LCM»
  LCM_0 := SessionLibrary.Prime.«LCM_0»
  LCM_COPRIME_DECOMP := SessionLibrary.Prime.«LCM_COPRIME_DECOMP»
  LE := Session.LE
  LEFT_AND_EXISTS_THM := Session.LEFT_AND_EXISTS_THM
  LEFT_FORALL_IMP_THM := Session.LEFT_FORALL_IMP_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LET_TRANS := Session.LET_TRANS
  LE_0 := Session.LE_0
  LE_1 := Session.LE_1
  LE_ADD := Session.LE_ADD
  LE_ADD2 := Session.LE_ADD2
  LE_ANTISYM := Session.LE_ANTISYM
  LE_C := Session.LE_C
  LE_CASES := Session.LE_CASES
  LE_EXISTS := Session.LE_EXISTS
  LE_LT := Session.LE_LT
  LE_MULT_LCANCEL := Session.LE_MULT_LCANCEL
  LE_MULT_RCANCEL := Session.LE_MULT_RCANCEL
  LE_REFL := Session.LE_REFL
  LE_SUC := Session.LE_SUC
  LE_TRANS := Session.LE_TRANS
  LT := Session.LT
  LTE_TRANS := Session.LTE_TRANS
  LT_ADD_RCANCEL := Session.LT_ADD_RCANCEL
  LT_ANTISYM := Session.LT_ANTISYM
  LT_IMP_LE := Session.LT_IMP_LE
/-- The core theorems ringtheory.ml uses. -/
def core6 : HolLibrary.RingTheory.CoreThms6 where
  LT_IMP_NE := Session.LT_IMP_NE
  LT_MULT_LCANCEL := Session.LT_MULT_LCANCEL
  LT_REFL := Session.LT_REFL
  LT_SUC_LE := Session.LT_SUC_LE
  LT_TRANS := Session.LT_TRANS
  MAX_LE_LCM := SessionLibrary.Prime.«MAX_LE_LCM»
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MINIMAL := Session.MINIMAL
  MINIMAL_LE := Session.MINIMAL_LE
  MINIMAL_UNIQUE := Session.MINIMAL_UNIQUE
  MOD_LT := Session.MOD_LT
  MOD_LT_EQ := Session.MOD_LT_EQ
  MOD_MULT_ADD := Session.MOD_MULT_ADD
  MONO_AND := Session.MONO_AND
  MONO_EXISTS := Session.MONO_EXISTS
  MONO_FORALL := Session.MONO_FORALL
  MONO_IMP := Session.MONO_IMP
  MONO_OR := Session.MONO_OR
  MULT_ASSOC := Session.MULT_ASSOC
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_EQ_0 := Session.MULT_EQ_0
  MULT_EQ_1 := Session.MULT_EQ_1
  MULT_SYM := Session.MULT_SYM
  MUL_C_UNIV := SessionLibrary.Card.«MUL_C_UNIV»
  NOT_CLAUSES := Session.NOT_CLAUSES
  NOT_EVEN := Session.NOT_EVEN
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NOT_INSERT_EMPTY := Session.NOT_INSERT_EMPTY
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NOT_LE := Session.NOT_LE
  NOT_LT := Session.NOT_LT
  NOT_SUC := Session.NOT_SUC
  NSUM_ADD := Session.NSUM_ADD
  NSUM_CLAUSES := Session.NSUM_CLAUSES
  NSUM_CONST := Session.NSUM_CONST
  NSUM_CONST_NUMSEG := Session.NSUM_CONST_NUMSEG
  NSUM_DELTA := Session.NSUM_DELTA
  NSUM_EQ := Session.NSUM_EQ
  NSUM_EQ_0_IFF := Session.NSUM_EQ_0_IFF
  NSUM_SING := Session.NSUM_SING
  NSUM_SUBSET_SIMPLE := Session.NSUM_SUBSET_SIMPLE
  NSUM_SUPERSET := Session.NSUM_SUPERSET
  NUMSEG_ADD_SPLIT := Session.NUMSEG_ADD_SPLIT
  NUMSEG_CLAUSES := Session.NUMSEG_CLAUSES
  NUMSEG_CLAUSES_LT := Session.NUMSEG_CLAUSES_LT
  NUMSEG_EMPTY := Session.NUMSEG_EMPTY
  NUMSEG_LREC := Session.NUMSEG_LREC
  NUMSEG_OFFSET_IMAGE := Session.NUMSEG_OFFSET_IMAGE
  NUMSEG_RREC := Session.NUMSEG_RREC
  NUMSEG_SING := Session.NUMSEG_SING
  NUM_GCD := Session.NUM_GCD
  NUM_LCM := Session.NUM_LCM
  NUM_OF_INT_OF_NUM := Session.NUM_OF_INT_OF_NUM
  ODD := Session.ODD
  ORDER_EXISTENCE_GEN := SessionLibrary.Iter.«ORDER_EXISTENCE_GEN»
  OR_EXISTS_THM := Session.OR_EXISTS_THM
  PAIR := Session.PAIR
  PAIRWISE_EMPTY := Session.PAIRWISE_EMPTY
  PAIRWISE_IMAGE := Session.PAIRWISE_IMAGE
  PAIRWISE_INSERT := Session.PAIRWISE_INSERT
  PAIR_EQ := Session.PAIR_EQ
  POSET_IMP_QOSET := SessionLibrary.Wo.«POSET_IMP_QOSET»
  POSET_MAX := SessionLibrary.Wo.«POSET_MAX»
  PRIME_1 := SessionLibrary.Prime.«PRIME_1»
  PRIME_GE_2 := SessionLibrary.Prime.«PRIME_GE_2»
  PRIME_IMP_NZ := SessionLibrary.Prime.«PRIME_IMP_NZ»
  PROPERLY_PROPERLY := SessionLibrary.Wo.«PROPERLY_PROPERLY»
  PSUBSET := Session.PSUBSET
  PSUBSET_ALT := Session.PSUBSET_ALT
  QOSET_FLD := SessionLibrary.Wo.«QOSET_FLD»
  RDIV_LT_EQ := Session.RDIV_LT_EQ
  REAL_ENTIRE := Session.REAL_ENTIRE
  REAL_INV_0 := Session.REAL_INV_0
  REAL_MUL_RINV := Session.REAL_MUL_RINV
  REAL_OF_NUM_EQ := Session.REAL_OF_NUM_EQ
  REAL_OF_NUM_SUC := Session.REAL_OF_NUM_SUC
/-- The core theorems ringtheory.ml uses. -/
def core7 : HolLibrary.RingTheory.CoreThms7 where
  RESTRICTION := Session.RESTRICTION
  RESTRICTION_EXTENSION := Session.RESTRICTION_EXTENSION
  RESTRICTION_IN_CARTESIAN_PRODUCT := Session.RESTRICTION_IN_CARTESIAN_PRODUCT
  RESTRICTION_IN_EXTENSIONAL := Session.RESTRICTION_IN_EXTENSIONAL
  RESTRICTION_UNIQUE := Session.RESTRICTION_UNIQUE
  RESTRICTION_UNIQUE_ALT := Session.RESTRICTION_UNIQUE_ALT
  RIGHT_AND_EXISTS_THM := Session.RIGHT_AND_EXISTS_THM
  RIGHT_EXISTS_AND_THM := Session.RIGHT_EXISTS_AND_THM
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RIGHT_IMP_EXISTS_THM := Session.RIGHT_IMP_EXISTS_THM
  RIGHT_IMP_FORALL_THM := Session.RIGHT_IMP_FORALL_THM
  RIGHT_OR_DISTRIB := Session.RIGHT_OR_DISTRIB
  SELECT_AX := Session.SELECT_AX
  SELECT_UNIQUE := Session.SELECT_UNIQUE
  SIMPLE_IMAGE := Session.SIMPLE_IMAGE
  SIMPLE_IMAGE_GEN := Session.SIMPLE_IMAGE_GEN
  SING_GSPEC := Session.SING_GSPEC
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SQUAREFREE_GCD_SQUARE := SessionLibrary.Pocklington.«SQUAREFREE_GCD_SQUARE»
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUBSET_ANTISYM_EQ := Session.SUBSET_ANTISYM_EQ
  SUBSET_CARTESIAN_PRODUCT := Session.SUBSET_CARTESIAN_PRODUCT
  SUBSET_CROSS := Session.SUBSET_CROSS
  SUBSET_EMPTY := Session.SUBSET_EMPTY
  SUBSET_INTER := Session.SUBSET_INTER
  SUBSET_INTERS := Session.SUBSET_INTERS
  SUBSET_NUMSEG := Session.SUBSET_NUMSEG
  SUBSET_REFL := Session.SUBSET_REFL
  SUBSET_RESTRICT := Session.SUBSET_RESTRICT
  SUBSET_TRANS := Session.SUBSET_TRANS
  SUBSET_UNION := Session.SUBSET_UNION
  SUBSET_UNIONS := Session.SUBSET_UNIONS
  SUBSET_UNIV := Session.SUBSET_UNIV
  SUB_0 := Session.SUB_0
  SUB_ADD := Session.SUB_ADD
  SUB_REFL := Session.SUB_REFL
  SUB_SUC := Session.SUB_SUC
  SUC_INJ := Session.SUC_INJ
  SURJ := Session.SURJ
  SURJECTIVE_IFF_INJECTIVE := Session.SURJECTIVE_IFF_INJECTIVE
  SURJECTIVE_IFF_INJECTIVE_GEN := Session.SURJECTIVE_IFF_INJECTIVE_GEN
  SURJECTIVE_ON_RIGHT_INVERSE := Session.SURJECTIVE_ON_RIGHT_INVERSE
  SWAP_EXISTS_THM := Session.SWAP_EXISTS_THM
  SWAP_FORALL_THM := Session.SWAP_FORALL_THM
  TOSET_IMP_POSET := SessionLibrary.Wo.«TOSET_IMP_POSET»
  TOSET_IMP_QOSET := SessionLibrary.Wo.«TOSET_IMP_QOSET»
  TOSET_MAX := SessionLibrary.Wo.«TOSET_MAX»
  TRANSITIVE_STEPWISE_LE := Session.TRANSITIVE_STEPWISE_LE
  TRUTH := Session.TRUTH
  UNIONS_0 := Session.UNIONS_0
  UNIONS_1 := Session.UNIONS_1
  UNIONS_GSPEC := Session.UNIONS_GSPEC
  UNIONS_IMAGE := Session.UNIONS_IMAGE
  UNIONS_INSERT := Session.UNIONS_INSERT
  UNIONS_SUBSET := Session.UNIONS_SUBSET
  UNIONS_UNION := Session.UNIONS_UNION
  UNION_COMM := Session.UNION_COMM
  UNION_EMPTY := Session.UNION_EMPTY
  UNION_OVER_INTER := Session.UNION_OVER_INTER
  UNION_RESTRICT := Session.UNION_RESTRICT
  UNION_SUBSET := Session.UNION_SUBSET
  UNIV_1 := Session.UNIV_1
  UNIV_GSPEC := Session.UNIV_GSPEC
  UNIV_NOT_EMPTY := Session.UNIV_NOT_EMPTY
  UNWIND_THM1 := Session.UNWIND_THM1
  UNWIND_THM2 := Session.UNWIND_THM2
  WF := Session.WF
  WF_ANTISYM := Session.WF_ANTISYM
  WF_DCHAIN := Session.WF_DCHAIN
/-- The core theorems ringtheory.ml uses. -/
def core8 : HolLibrary.RingTheory.CoreThms8 where
  WF_IND := Session.WF_IND
  WF_LEX := Session.WF_LEX
  WF_MEASURE_GEN := Session.WF_MEASURE_GEN
  WF_REC_EXISTS := Session.WF_REC_EXISTS
  WF_SUBSET := Session.WF_SUBSET
  WF_num := Session.WF_num
  WLOG_LE := Session.WLOG_LE
  WO := SessionLibrary.Wo.«WO»
  WOSET := SessionLibrary.Wo.«WOSET»
  WOSET_IMP_POSET := SessionLibrary.Wo.«WOSET_IMP_POSET»
  WOSET_IMP_TOSET := SessionLibrary.Wo.«WOSET_IMP_TOSET»
  WOSET_WF := SessionLibrary.Wo.«WOSET_WF»
  WOSET_WQOSET := SessionLibrary.Wo.«WOSET_WQOSET»
  WQOSET_IMP_WF := SessionLibrary.Wo.«WQOSET_IMP_WF»
  WQOSET_POINTWISE := SessionLibrary.Wo.«WQOSET_POINTWISE»
  WQOSET_RESTRICT := SessionLibrary.Wo.«WQOSET_RESTRICT»
  WQOSET_SUPERSET := SessionLibrary.Wo.«WQOSET_SUPERSET»
  WQOSET_num := SessionLibrary.Wo.«WQOSET_num»
  ZERO_ONE_OR_PRIME_DIVPROD := Session.ZERO_ONE_OR_PRIME_DIVPROD
  ZL_SUBSETS_INTERS_NONEMPTY := SessionLibrary.Wo.«ZL_SUBSETS_INTERS_NONEMPTY»
  ZL_SUBSETS_UNIONS_NONEMPTY := SessionLibrary.Wo.«ZL_SUBSETS_UNIONS_NONEMPTY»
  add_c := SessionLibrary.Card.«add_c»
  binom := SessionLibrary.Binomial.«binom»
  cartesian_product := Session.cartesian_product
  coprime := Session.coprime
  divides := Session.divides
  eq_c := Session.eq_c
  fld := SessionLibrary.Wo.«fld»
  int_INFINITE := SessionLibrary.Card.«int_INFINITE»
  int_coprime := Session.int_coprime
  int_divides := Session.int_divides
  int_gcd := Session.int_gcd
  int_mod := Session.int_mod
  int_neg_th := Session.int_neg_th
  int_of_num_th := Session.int_of_num_th
  inverse_mod := SessionLibrary.Pocklington.«inverse_mod»
  iproduct := Session.iproduct
  isum := Session.isum
  iterate := Session.iterate
  le_c := Session.le_c
  minimal := Session.minimal
  monoidal := Session.monoidal
  mul_c := SessionLibrary.Card.«mul_c»
  neutral := Session.neutral
  num_CASES := Session.num_CASES
  num_FINITE := Session.num_FINITE
  num_INDUCTION := Session.num_INDUCTION
  num_INFINITE := Session.num_INFINITE
  num_MAX := Session.num_MAX
  num_RECURSION := Session.num_RECURSION
  num_WF := Session.num_WF
  num_WOP := Session.num_WOP
  num_congruent := Session.num_congruent
  num_coprime := Session.num_coprime
  num_divides := Session.num_divides
  numseg := Session.numseg
  o_ASSOC := Session.o_ASSOC
  o_DEF := Session.o_DEF
  o_THM := Session.o_THM
  one := Session.one
  pairwise := Session.pairwise
  poset := SessionLibrary.Wo.«poset»
  prime := Session.prime
  product := Session.product
  properly := SessionLibrary.Wo.«properly»
  qoset := SessionLibrary.Wo.«qoset»
  real_pow := Session.real_pow
  strictly := SessionLibrary.Wo.«strictly»
  sum := Session.sum
  sum_DISTINCT := SessionLibrary.Card.«sum_DISTINCT»
  sum_INJECTIVE := SessionLibrary.Card.«sum_INJECTIVE»
  support := Session.support
  toset := SessionLibrary.Wo.«toset»

/-- What ringtheory.ml uses from Session. -/
def deps : HolLibrary.RingTheory.RingTheoryDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  new_type_definition ty names th :=
    ExceptT.mk (Session.new_type_definition ty names.1 names.2 th)
  new_recursive_definition ax s := do
    ExceptT.mk (Session.new_recursive_definition ax (← HolLight.q s))
  new_specification names th := ExceptT.mk (Session.new_specification names th)
  parse_as_infix := Session.parse_as_infix
  extend_basic_congs := Session.extend_basic_congs
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  ASM_INT_ARITH_TAC := Session.ASM_INT_ARITH_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  ASM_METIS_TAC := Session.ASM_METIS_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  INTEGER_RULE t := ExceptT.mk (Session.INTEGER_RULE t)
  INTEGER_TAC := Session.INTEGER_TAC
  INT_ARITH t := ExceptT.mk (Session.INT_ARITH t)
  INT_ARITH_TAC := Session.INT_ARITH_TAC
  INT_RING t := ExceptT.mk (Session.INT_RING t)
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  METIS_TAC := Session.METIS_TAC
  NUMBER_RULE t := ExceptT.mk (Session.NUMBER_RULE t)
  NUMBER_TAC := Session.NUMBER_TAC
  REAL_ARITH_TAC := Session.REAL_ARITH_TAC2
  REAL_FIELD t := ExceptT.mk (Session.REAL_FIELD t)
  REAL_RING t := ExceptT.mk (Session.REAL_RING t)
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  SIMP_RULE ths th := ExceptT.mk (Session.SIMP_RULE ths th)
  WF_INDUCT_TAC := Session.WF_INDUCT_TAC
  INTRO_TAC := Session.INTRO_TAC
  HAS_SIZE_CONV := Session.HAS_SIZE_CONV
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  MOD_DOWN_CONV := Session.MOD_DOWN_CONV
  INT_REM_DOWN_CONV := Session.INT_REM_DOWN_CONV
  INT_REDUCE_CONV := Session.INT_REDUCE_CONV
  REAL_RAT_REDUCE_CONV := Session.REAL_RAT_REDUCE_CONV
  SELECT_CONV t := pure (Session.SELECT_CONV t)
  let_CONV := Session.let_CONV
  PRESIMP_CONV := Session.PRESIMP_CONV
  CONDS_ELIM_CONV := Session.CONDS_ELIM_CONV
  NNFC_CONV := Session.NNFC_CONV
  CNF_CONV := Session.CNF_CONV
  SKOLEM_CONV := Session.SKOLEM_CONV
  PRENEX_CONV := Session.PRENEX_CONV
  DISJ_ACI_RULE := Session.DISJ_ACI_RULE
  prove_inductive_relations_exist := Session.prove_inductive_relations_exist
  prove_recursive_functions_exist ax t := ExceptT.mk (Session.prove_recursive_functions_exist ax t)
  derive_strong_induction := Session.derive_strong_induction
  num_CONV := Session.num_CONV
  basic_ss := Session.basic_ss
  INT_ADD_CONV := Session.INT_ADD_CONV
  INT_MUL_CONV := Session.INT_MUL_CONV
  INT_POW_CONV := Session.INT_POW_CONV
  INT_SUB_CONV := Session.INT_SUB_CONV
  INT_NEG_CONV := Session.INT_NEG_CONV
  INT_REM_CONV := Session.INT_REM_CONV
  INT_POW_REM_CONV := Session.INT_POW_REM_CONV
  NUM_RED_CONV := Session.NUM_RED_CONV
  COPRIME_CONV := SessionLibrary.Prime.COPRIME_CONV
  INVERSE_MOD_CONV := SessionLibrary.Pocklington.INVERSE_MOD_CONV
  mk_intconst := Session.mk_intconst
  SEMIRING_NORMALIZERS_CONV := Session.SEMIRING_NORMALIZERS_CONV
  RING_AND_IDEAL_CONV K := do
    let R ← HolMath.Grobner.setupRingCtx Session.GrG Session.numeralConstsNum (concl Session.TRUTH)
      Session.PRESIMP_CONV Session.CONDS_ELIM_CONV Session.NNF_CONV Session.WEAK_DNF_CONV
      Session.AND_FORALL_THM Session.LEFT_AND_FORALL_THM Session.RIGHT_AND_FORALL_THM
      Session.LEFT_OR_FORALL_THM Session.RIGHT_OR_FORALL_THM Session.OR_EXISTS_THM
      Session.LEFT_OR_EXISTS_THM Session.RIGHT_OR_EXISTS_THM Session.LEFT_AND_EXISTS_THM
      Session.RIGHT_AND_EXISTS_THM K
    pure (HolMath.Grobner.RING' R, HolMath.Grobner.ideal_cofactors R)
  core1 := core1
  core2 := core2
  core3 := core3
  core4 := core4
  core5 := core5
  core6 := core6
  core7 := core7
  core8 := core8

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in ringtheory.ml order. -/

initialize BBasics : HolLibrary.RingTheory.Basics ←
  ioB "setupBasics" <|
    (HolLibrary.RingTheory.setupBasics deps).run

initialize BNumbers : HolLibrary.RingTheory.Numbers ←
  ioB "setupNumbers" <|
    (HolLibrary.RingTheory.setupNumbers deps BBasics).run

initialize BSums : HolLibrary.RingTheory.Sums ←
  ioB "setupSums" <|
    (HolLibrary.RingTheory.setupSums deps BBasics BNumbers).run

initialize BProducts : HolLibrary.RingTheory.Products ←
  ioB "setupProducts" <|
    (HolLibrary.RingTheory.setupProducts deps BBasics BNumbers).run

initialize BDivides : HolLibrary.RingTheory.Divides ←
  ioB "setupDivides" <|
    (HolLibrary.RingTheory.setupDivides deps BBasics BNumbers BSums BProducts).run

initialize BSubrings : HolLibrary.RingTheory.Subrings ←
  ioB "setupSubrings" <|
    (HolLibrary.RingTheory.setupSubrings deps BBasics BNumbers BSums BProducts BDivides).run

initialize BIdeals : HolLibrary.RingTheory.Ideals ←
  ioB "setupIdeals" <|
    (HolLibrary.RingTheory.setupIdeals deps BBasics BNumbers BSums BProducts BDivides BSubrings).run

initialize BDomains : HolLibrary.RingTheory.Domains ←
  ioB "setupDomains" <|
    (HolLibrary.RingTheory.setupDomains deps BBasics BNumbers BSums BProducts BDivides BSubrings BIdeals).run

initialize BRules : HolLibrary.RingTheory.Rules ←
  ioB "setupRules" <|
    (HolLibrary.RingTheory.setupRules deps BBasics BNumbers BDivides BDomains).run

initialize BHoms : HolLibrary.RingTheory.Homs ←
  ioB "setupHoms" <|
    (HolLibrary.RingTheory.setupHoms deps BBasics BNumbers BSums BProducts BDivides BSubrings BIdeals BDomains BRules).run

initialize BIso : HolLibrary.RingTheory.Iso ←
  ioB "setupIso" <|
    (HolLibrary.RingTheory.setupIso deps BBasics BHoms).run

initialize BKernels : HolLibrary.RingTheory.Kernels ←
  ioB "setupKernels" <|
    (HolLibrary.RingTheory.setupKernels deps BBasics BDivides BSubrings BIdeals BDomains BHoms BIso).run

initialize BProdRings : HolLibrary.RingTheory.ProdRings ←
  ioB "setupProdRings" <|
    (HolLibrary.RingTheory.setupProdRings deps BBasics BNumbers BSums BDivides BSubrings BIdeals BHoms BIso BKernels).run

initialize BLimits : HolLibrary.RingTheory.Limits ←
  ioB "setupLimits" <|
    (HolLibrary.RingTheory.setupLimits deps BBasics BNumbers BHoms).run

initialize BRingRule : HolLibrary.RingTheory.RingRule ←
  ioB "setupRingRule" <|
    (HolLibrary.RingTheory.setupRingRule deps BBasics BNumbers BDivides BRules BHoms BIso BProdRings BLimits).run

initialize BCosets : HolLibrary.RingTheory.Cosets ←
  ioB "setupCosets" <|
    (HolLibrary.RingTheory.setupCosets deps BBasics BNumbers BDivides BSubrings BIdeals BHoms BIso BKernels BProdRings BRingRule).run

initialize BQuotients : HolLibrary.RingTheory.Quotients ←
  ioB "setupQuotients" <|
    (HolLibrary.RingTheory.setupQuotients deps BBasics BSubrings BIdeals BHoms BIso BKernels BRingRule BCosets).run

initialize BPrimes : HolLibrary.RingTheory.Primes ←
  ioB "setupPrimes" <|
    (HolLibrary.RingTheory.setupPrimes deps BBasics BNumbers BProducts BDivides BDomains BHoms BKernels).run

initialize BFactorizations : HolLibrary.RingTheory.Factorizations ←
  ioB "setupFactorizations" <|
    (HolLibrary.RingTheory.setupFactorizations deps BBasics BProducts BDivides BDomains BPrimes).run

initialize BSquarefree : HolLibrary.RingTheory.Squarefree ←
  ioB "setupSquarefree" <|
    (HolLibrary.RingTheory.setupSquarefree deps BBasics BNumbers BDivides BDomains BHoms BPrimes).run

initialize BLocalization : HolLibrary.RingTheory.Localization ←
  ioB "setupLocalization" <|
    (HolLibrary.RingTheory.setupLocalization deps BBasics BNumbers BDivides BIdeals BHoms BIso BKernels BRingRule BSquarefree).run

initialize BLocalization2 : HolLibrary.RingTheory.Localization2 ←
  ioB "setupLocalization2" <|
    (HolLibrary.RingTheory.setupLocalization2 deps BBasics BNumbers BDivides BIdeals BDomains BHoms BIso BKernels BRingRule BSquarefree BLocalization).run

initialize BSpecialIdeals : HolLibrary.RingTheory.SpecialIdeals ←
  ioB "setupSpecialIdeals" <|
    (HolLibrary.RingTheory.setupSpecialIdeals deps BBasics BNumbers BProducts BDivides BIdeals BHoms BKernels BProdRings BLocalization BLocalization2).run

initialize BSpecialIdeals2 : HolLibrary.RingTheory.SpecialIdeals2 ←
  ioB "setupSpecialIdeals2" <|
    (HolLibrary.RingTheory.setupSpecialIdeals2 deps BBasics BNumbers BDivides BIdeals BDomains BHoms BIso BKernels BRingRule BCosets BQuotients BPrimes BSquarefree BLocalization2 BSpecialIdeals).run

initialize BRadical : HolLibrary.RingTheory.Radical ←
  ioB "setupRadical" <|
    (HolLibrary.RingTheory.setupRadical deps BBasics BNumbers BSums BDivides BIdeals BDomains BHoms BRingRule BCosets BQuotients BSquarefree BLocalization BLocalization2 BSpecialIdeals BSpecialIdeals2).run

initialize BUFDs : HolLibrary.RingTheory.UFDs ←
  ioB "setupUFDs" <|
    (HolLibrary.RingTheory.setupUFDs deps BBasics BNumbers BProducts BDivides BIdeals BDomains BHoms BIso BKernels BRingRule BPrimes BFactorizations BSquarefree BLocalization BLocalization2 BSpecialIdeals BSpecialIdeals2 BRadical).run

initialize BEuclidean : HolLibrary.RingTheory.Euclidean ←
  ioB "setupEuclidean" <|
    (HolLibrary.RingTheory.setupEuclidean deps BBasics BDivides BIdeals BDomains BHoms BIso BQuotients BSpecialIdeals).run

initialize BNoetherian : HolLibrary.RingTheory.Noetherian ←
  ioB "setupNoetherian" <|
    (HolLibrary.RingTheory.setupNoetherian deps BBasics BIdeals BHoms BIso BKernels BProdRings BQuotients BSpecialIdeals BSpecialIdeals2 BUFDs).run

initialize BACCP : HolLibrary.RingTheory.ACCP ←
  ioB "setupACCP" <|
    (HolLibrary.RingTheory.setupACCP deps BBasics BProducts BDivides BIdeals BDomains BPrimes BFactorizations BSpecialIdeals BUFDs BNoetherian).run

initialize BRingGcd : HolLibrary.RingTheory.RingGcd ←
  ioB "setupRingGcd" <|
    (HolLibrary.RingTheory.setupRingGcd deps BBasics BNumbers BDivides BDomains BUFDs).run

initialize BBezout : HolLibrary.RingTheory.Bezout ←
  ioB "setupBezout" <|
    (HolLibrary.RingTheory.setupBezout deps BBasics BDivides BIdeals BHoms BIso BRingRule BQuotients BPrimes BSquarefree BLocalization BLocalization2 BSpecialIdeals BSpecialIdeals2 BUFDs BNoetherian BACCP BRingGcd).run

initialize BGcdDomain : HolLibrary.RingTheory.GcdDomain ←
  ioB "setupGcdDomain" <|
    (HolLibrary.RingTheory.setupGcdDomain deps BBasics BNumbers BProducts BDivides BDomains BPrimes BSpecialIdeals2 BUFDs BRingGcd BBezout).run

initialize BSquarefreeUFD : HolLibrary.RingTheory.SquarefreeUFD ←
  ioB "setupSquarefreeUFD" <|
    (HolLibrary.RingTheory.setupSquarefreeUFD deps BBasics BNumbers BProducts BDivides BDomains BRingRule BPrimes BSquarefree BUFDs BRingGcd BGcdDomain).run

initialize BBooleanRings : HolLibrary.RingTheory.BooleanRings ←
  ioB "setupBooleanRings" <|
    (HolLibrary.RingTheory.setupBooleanRings deps BBasics BNumbers BDivides BSubrings BIdeals BDomains BHoms BIso BKernels BProdRings BRingRule BQuotients BPrimes BSquarefree BSpecialIdeals BSpecialIdeals2 BRadical BBezout).run

initialize BLocalRings : HolLibrary.RingTheory.LocalRings ←
  ioB "setupLocalRings" <|
    (HolLibrary.RingTheory.setupLocalRings deps BBasics BDivides BIdeals BDomains BHoms BIso BKernels BRingRule BCosets BQuotients BSquarefree BLocalization BLocalization2 BSpecialIdeals BSpecialIdeals2 BRadical BUFDs BNoetherian).run

initialize BVonNeumann : HolLibrary.RingTheory.VonNeumann ←
  ioB "setupVonNeumann" <|
    (HolLibrary.RingTheory.setupVonNeumann deps BBasics BNumbers BDivides BIdeals BDomains BHoms BIso BProdRings BRingRule BQuotients BSquarefree BLocalization BLocalization2 BSpecialIdeals BUFDs BBezout BBooleanRings).run

initialize BBoolRing : HolLibrary.RingTheory.BoolRing ←
  ioB "setupBoolRing" <|
    (HolLibrary.RingTheory.setupBoolRing deps BBasics BDomains BHoms BIso BRingRule BBooleanRings).run

initialize BIntegerRing : HolLibrary.RingTheory.IntegerRing ←
  ioB "setupIntegerRing" <|
    (HolLibrary.RingTheory.setupIntegerRing deps BBasics BNumbers BSums BProducts BDivides BIdeals BDomains BHoms BKernels BCosets BUFDs BEuclidean BRingGcd BBezout).run

initialize BIntegerModRing : HolLibrary.RingTheory.IntegerModRing ←
  ioB "setupIntegerModRing" <|
    (HolLibrary.RingTheory.setupIntegerModRing deps BBasics BNumbers BDivides BIdeals BDomains BHoms BIso BKernels BProdRings BCosets BQuotients BVonNeumann BIntegerRing).run

initialize BIntegerModConv : HolLibrary.RingTheory.IntegerModConv ←
  ioB "setupIntegerModConv" <|
    (HolLibrary.RingTheory.setupIntegerModConv deps BBasics BDivides BIntegerModRing).run

initialize BRealRing : HolLibrary.RingTheory.RealRing ←
  ioB "setupRealRing" <|
    (HolLibrary.RingTheory.setupRealRing deps BBasics BNumbers BSums BProducts BDivides BDomains).run

initialize BMonomials : HolLibrary.RingTheory.Monomials ←
  ioB "setupMonomials" <|
    (HolLibrary.RingTheory.setupMonomials deps).run

initialize BPowerSeries : HolLibrary.RingTheory.PowerSeries ←
  ioB "setupPowerSeries" <|
    (HolLibrary.RingTheory.setupPowerSeries deps BBasics BSums BRingRule BMonomials).run

initialize BPolyRings : HolLibrary.RingTheory.PolyRings ←
  ioB "setupPolyRings" <|
    (HolLibrary.RingTheory.setupPolyRings deps BBasics BNumbers BSums BProducts BSubrings BHoms BMonomials BPowerSeries).run

initialize BHomExtend : HolLibrary.RingTheory.HomExtend ←
  ioB "setupHomExtend" <|
    (HolLibrary.RingTheory.setupHomExtend deps BBasics BNumbers BSums BProducts BSubrings BHoms BRingRule BMonomials BPowerSeries BPolyRings).run

initialize BNatIso : HolLibrary.RingTheory.NatIso ←
  ioB "setupNatIso" <|
    (HolLibrary.RingTheory.setupNatIso deps BBasics BSums BProducts BSubrings BHoms BIso BRingRule BMonomials BPowerSeries BPolyRings BHomExtend).run

initialize BRenaming : HolLibrary.RingTheory.Renaming ←
  ioB "setupRenaming" <|
    (HolLibrary.RingTheory.setupRenaming deps BBasics BSums BProducts BDivides BHoms BMonomials BPowerSeries BPolyRings BHomExtend BNatIso).run

initialize BMonomialOrders : HolLibrary.RingTheory.MonomialOrders ←
  ioB "setupMonomialOrders" <|
    (HolLibrary.RingTheory.setupMonomialOrders deps BMonomials).run

initialize BOneCoeff : HolLibrary.RingTheory.OneCoeff ←
  ioB "setupOneCoeff" <|
    (HolLibrary.RingTheory.setupOneCoeff deps BBasics BNumbers BSums BSubrings BMonomials BPowerSeries BPolyRings).run

initialize BDegree : HolLibrary.RingTheory.Degree ←
  ioB "setupDegree" <|
    (HolLibrary.RingTheory.setupDegree deps BBasics BNumbers BSums BDivides BSubrings BDomains BHoms BKernels BRingRule BMonomials BPowerSeries BPolyRings BNatIso BMonomialOrders BOneCoeff).run

initialize BCardinalities : HolLibrary.RingTheory.Cardinalities ←
  ioB "setupCardinalities" <|
    (HolLibrary.RingTheory.setupCardinalities deps BBasics BMonomials BPolyRings).run

initialize BEvaluation : HolLibrary.RingTheory.Evaluation ←
  ioB "setupEvaluation" <|
    (HolLibrary.RingTheory.setupEvaluation deps BBasics BNumbers BSums BProducts BDivides BSubrings BIdeals BHoms BKernels BRingRule BQuotients BSpecialIdeals2 BMonomials BPowerSeries BPolyRings BHomExtend BRenaming BOneCoeff BDegree).run

initialize BComposing : HolLibrary.RingTheory.Composing ←
  ioB "setupComposing" <|
    (HolLibrary.RingTheory.setupComposing deps BBasics BSums BDomains BHoms BKernels BMonomials BPowerSeries BPolyRings BDegree BEvaluation).run

initialize BZerodivisors : HolLibrary.RingTheory.Zerodivisors ←
  ioB "setupZerodivisors" <|
    (HolLibrary.RingTheory.setupZerodivisors deps BBasics BSums BProducts BDivides BIdeals BDomains BHoms BIso BKernels BRingRule BCosets BQuotients BPrimes BSpecialIdeals BSpecialIdeals2 BRadical BLocalRings BMonomials BPowerSeries BPolyRings BHomExtend BNatIso BRenaming BMonomialOrders BOneCoeff BDegree BEvaluation BComposing).run

initialize BXMinusA : HolLibrary.RingTheory.XMinusA ←
  ioB "setupXMinusA" <|
    (HolLibrary.RingTheory.setupXMinusA deps BBasics BNumbers BDivides BDomains BRingRule BPrimes BPowerSeries BPolyRings BDegree BEvaluation BZerodivisors).run

initialize BDivision : HolLibrary.RingTheory.Division ←
  ioB "setupDivision" <|
    (HolLibrary.RingTheory.setupDivision deps BBasics BNumbers BSums BDivides BIdeals BDomains BRules BIso BKernels BRingRule BCosets BQuotients BPrimes BSpecialIdeals2 BEuclidean BMonomials BPowerSeries BPolyRings BOneCoeff BDegree BEvaluation BZerodivisors).run

initialize BHilbert : HolLibrary.RingTheory.Hilbert ←
  ioB "setupHilbert" <|
    (HolLibrary.RingTheory.setupHilbert deps BBasics BNumbers BSums BIdeals BRules BHoms BIso BRingRule BSpecialIdeals BNoetherian BMonomials BPowerSeries BPolyRings BNatIso BOneCoeff BDegree BEvaluation BDivision).run

initialize BMonic : HolLibrary.RingTheory.Monic ←
  ioB "setupMonic" <|
    (HolLibrary.RingTheory.setupMonic deps BBasics BNumbers BSums BProducts BDivides BSubrings BIdeals BDomains BHoms BKernels BRingRule BPrimes BSpecialIdeals BMonomials BPowerSeries BPolyRings BHomExtend BOneCoeff BDegree BComposing BZerodivisors BXMinusA BDivision).run

initialize BSplits : HolLibrary.RingTheory.Splits ←
  ioB "setupSplits" <|
    (HolLibrary.RingTheory.setupSplits deps BBasics BNumbers BProducts BDivides BSubrings BDomains BHoms BKernels BRingRule BPrimes BSquarefree BSpecialIdeals2 BUFDs BPowerSeries BPolyRings BOneCoeff BDegree BEvaluation BComposing BZerodivisors BXMinusA BDivision BMonic).run

initialize BReciprocal : HolLibrary.RingTheory.Reciprocal ←
  ioB "setupReciprocal" <|
    (HolLibrary.RingTheory.setupReciprocal deps BBasics BNumbers BSums BDivides BDomains BRingRule BPrimes BPowerSeries BPolyRings BOneCoeff BDegree BEvaluation BZerodivisors BDivision).run

initialize BDerivative : HolLibrary.RingTheory.Derivative ←
  ioB "setupDerivative" <|
    (HolLibrary.RingTheory.setupDerivative deps BBasics BNumbers BSums BProducts BDivides BSubrings BIdeals BDomains BHoms BRingRule BPrimes BPowerSeries BPolyRings BOneCoeff BDegree BEvaluation BComposing BZerodivisors BDivision).run

initialize BSeparable : HolLibrary.RingTheory.Separable ←
  ioB "setupSeparable" <|
    (HolLibrary.RingTheory.setupSeparable deps BBasics BNumbers BDivides BDomains BHoms BKernels BRingRule BPrimes BSquarefree BUFDs BACCP BBezout BGcdDomain BPowerSeries BPolyRings BDegree BEvaluation BComposing BZerodivisors BXMinusA BDivision BDerivative).run

initialize BGaussA : HolLibrary.RingTheory.GaussA ←
  ioB "setupGaussA" <|
    (HolLibrary.RingTheory.setupGaussA deps BBasics BDivides BDomains BHoms BPrimes BSpecialIdeals BUFDs BACCP BMonomials BPowerSeries BPolyRings BNatIso BOneCoeff BDegree BZerodivisors BDivision).run

initialize BGaussB : HolLibrary.RingTheory.GaussB ←
  ioB "setupGaussB" <|
    (HolLibrary.RingTheory.setupGaussB deps BBasics BNumbers BDivides BIdeals BDomains BIso BRingRule BSpecialIdeals BSpecialIdeals2 BUFDs BPowerSeries BPolyRings BNatIso BRenaming BOneCoeff BDegree BZerodivisors BDivision BGaussA).run

initialize BGaussC : HolLibrary.RingTheory.GaussC ←
  ioB "setupGaussC" <|
    (HolLibrary.RingTheory.setupGaussC deps BBasics BDomains BHoms BRingRule BSquarefree BLocalization BLocalization2 BPowerSeries BPolyRings BComposing).run

initialize BGaussD : HolLibrary.RingTheory.GaussD ←
  ioB "setupGaussD" <|
    (HolLibrary.RingTheory.setupGaussD deps BBasics BDivides BDomains BHoms BKernels BRingRule BPrimes BLocalization2 BUFDs BPowerSeries BPolyRings BRenaming BDegree BComposing BZerodivisors BGaussB BGaussC).run

initialize BEisenstein : HolLibrary.RingTheory.Eisenstein ←
  ioB "setupEisenstein" <|
    (HolLibrary.RingTheory.setupEisenstein deps BBasics BNumbers BDivides BIdeals BDomains BHoms BKernels BCosets BQuotients BPrimes BLocalization2 BSpecialIdeals BSpecialIdeals2 BUFDs BMonomials BPowerSeries BPolyRings BOneCoeff BDegree BEvaluation BComposing BZerodivisors BDivision BGaussA BGaussD).run

initialize BRingOrder : HolLibrary.RingTheory.RingOrder ←
  ioB "setupRingOrder" <|
    (HolLibrary.RingTheory.setupRingOrder deps BBasics BNumbers BDivides BSubrings BIdeals BDomains BHoms BRingRule BSquarefree BPowerSeries BPolyRings BDegree BEvaluation BXMinusA BSplits BDerivative BSeparable).run

initialize BFrobenius : HolLibrary.RingTheory.Frobenius ←
  ioB "setupFrobenius" <|
    (HolLibrary.RingTheory.setupFrobenius deps BBasics BNumbers BSums BDivides BSubrings BDomains BHoms BKernels BCosets BPowerSeries BPolyRings BDegree BEvaluation BXMinusA BRingOrder).run

initialize BIntegralDomainRule : HolLibrary.RingTheory.IntegralDomainRule ←
  ioB "setupIntegralDomainRule" <|
    (HolLibrary.RingTheory.setupIntegralDomainRule deps BBasics BDivides BDomains BRules BHoms BIso BKernels BLimits BPolyRings BDegree BCardinalities).run

initialize BRingPullDiv : HolLibrary.RingTheory.RingPullDiv ←
  ioB "setupRingPullDiv" <|
    (HolLibrary.RingTheory.setupRingPullDiv deps BNumbers BDivides BDomains BRules BIntegralDomainRule).run


-- Basics
def ring_tybij : thm := BBasics.ring_tybij
def ring_carrier : thm := BBasics.ring_carrier
def ring_0 : thm := BBasics.ring_0
def ring_1 : thm := BBasics.ring_1
def ring_neg : thm := BBasics.ring_neg
def ring_add : thm := BBasics.ring_add
def ring_mul : thm := BBasics.ring_mul
def ring_sub : thm := BBasics.ring_sub
def RINGS_EQ : thm := BBasics.RINGS_EQ
def RING_PROPERTIES : thm := BBasics.RING_PROPERTIES
def RING_0 : thm := BBasics.RING_0
def RING_1 : thm := BBasics.RING_1
def RING_NEG : thm := BBasics.RING_NEG
def RING_ADD : thm := BBasics.RING_ADD
def RING_SUB : thm := BBasics.RING_SUB
def RING_MUL : thm := BBasics.RING_MUL
def RING_ADD_SYM : thm := BBasics.RING_ADD_SYM
def RING_MUL_SYM : thm := BBasics.RING_MUL_SYM
def RING_ADD_ASSOC : thm := BBasics.RING_ADD_ASSOC
def RING_MUL_ASSOC : thm := BBasics.RING_MUL_ASSOC
def RING_ADD_LDISTRIB : thm := BBasics.RING_ADD_LDISTRIB
def RING_ADD_RDISTRIB : thm := BBasics.RING_ADD_RDISTRIB
def RING_ADD_LZERO : thm := BBasics.RING_ADD_LZERO
def RING_ADD_RZERO : thm := BBasics.RING_ADD_RZERO
def RING_MUL_LID : thm := BBasics.RING_MUL_LID
def RING_MUL_RID : thm := BBasics.RING_MUL_RID
def RING_ADD_LNEG : thm := BBasics.RING_ADD_LNEG
def RING_ADD_RNEG : thm := BBasics.RING_ADD_RNEG
def RING_ADD_AC : thm := BBasics.RING_ADD_AC
def RING_MUL_AC : thm := BBasics.RING_MUL_AC
def RING_ADD_LCANCEL : thm := BBasics.RING_ADD_LCANCEL
def RING_ADD_RCANCEL : thm := BBasics.RING_ADD_RCANCEL
def RING_ADD_LCANCEL_IMP : thm := BBasics.RING_ADD_LCANCEL_IMP
def RING_ADD_RCANCEL_IMP : thm := BBasics.RING_ADD_RCANCEL_IMP
def RING_ADD_EQ_RIGHT : thm := BBasics.RING_ADD_EQ_RIGHT
def RING_ADD_EQ_LEFT : thm := BBasics.RING_ADD_EQ_LEFT
def RING_LZERO_UNIQUE : thm := BBasics.RING_LZERO_UNIQUE
def RING_RZERO_UNIQUE : thm := BBasics.RING_RZERO_UNIQUE
def RING_ADD_EQ_0 : thm := BBasics.RING_ADD_EQ_0
def RING_LNEG_UNIQUE : thm := BBasics.RING_LNEG_UNIQUE
def RING_RNEG_UNIQUE : thm := BBasics.RING_RNEG_UNIQUE
def RING_NEG_NEG : thm := BBasics.RING_NEG_NEG
def RING_NEG_EQ_SWAP : thm := BBasics.RING_NEG_EQ_SWAP
def RING_NEG_EQ : thm := BBasics.RING_NEG_EQ
def RING_NEG_0 : thm := BBasics.RING_NEG_0
def RING_NEG_EQ_0 : thm := BBasics.RING_NEG_EQ_0
def RING_MUL_LZERO : thm := BBasics.RING_MUL_LZERO
def RING_MUL_RZERO : thm := BBasics.RING_MUL_RZERO
def RING_MUL_LNEG : thm := BBasics.RING_MUL_LNEG
def RING_MUL_RNEG : thm := BBasics.RING_MUL_RNEG
def RING_NEG_ADD : thm := BBasics.RING_NEG_ADD
def RING_SUB_REFL : thm := BBasics.RING_SUB_REFL
def RING_SUB_LZERO : thm := BBasics.RING_SUB_LZERO
def RING_SUB_RZERO : thm := BBasics.RING_SUB_RZERO
def RING_SUB_EQ_0 : thm := BBasics.RING_SUB_EQ_0
def RING_SUB_LDISTRIB : thm := BBasics.RING_SUB_LDISTRIB
def RING_SUB_RDISTRIB : thm := BBasics.RING_SUB_RDISTRIB
def RING_EQ_SUB_LADD : thm := BBasics.RING_EQ_SUB_LADD
def RING_EQ_SUB_RADD : thm := BBasics.RING_EQ_SUB_RADD
def RING_SUB_TELESCOPE : thm := BBasics.RING_SUB_TELESCOPE
def RING_NEG_SUB : thm := BBasics.RING_NEG_SUB
def RING_CARRIER_NONEMPTY : thm := BBasics.RING_CARRIER_NONEMPTY
def trivial_ring : thm := BBasics.trivial_ring
def TRIVIAL_IMP_FINITE_RING : thm := BBasics.TRIVIAL_IMP_FINITE_RING
def TRIVIAL_RING_SUBSET : thm := BBasics.TRIVIAL_RING_SUBSET
def TRIVIAL_RING : thm := BBasics.TRIVIAL_RING
def TRIVIAL_RING_ALT : thm := BBasics.TRIVIAL_RING_ALT
def TRIVIAL_RING_10 : thm := BBasics.TRIVIAL_RING_10
def RING_CARRIER_HAS_SIZE_1 : thm := BBasics.RING_CARRIER_HAS_SIZE_1
def TRIVIAL_RING_HAS_SIZE_1 : thm := BBasics.TRIVIAL_RING_HAS_SIZE_1
def RING_CARRIER_HAS_SIZE_2 : thm := BBasics.RING_CARRIER_HAS_SIZE_2
def singleton_ring : thm := BBasics.singleton_ring
def SINGLETON_RING : thm := BBasics.SINGLETON_RING
def TRIVIAL_RING_SINGLETON_RING : thm := BBasics.TRIVIAL_RING_SINGLETON_RING
def FINITE_SINGLETON_RING : thm := BBasics.FINITE_SINGLETON_RING

-- Numbers
def ring_of_num : thm := BNumbers.ring_of_num
def ring_of_int : thm := BNumbers.ring_of_int
def RING_OF_NUM : thm := BNumbers.RING_OF_NUM
def RING_OF_INT : thm := BNumbers.RING_OF_INT
def RING_OF_INT_OF_NUM : thm := BNumbers.RING_OF_INT_OF_NUM
def RING_OF_NUM_0 : thm := BNumbers.RING_OF_NUM_0
def RING_OF_NUM_1 : thm := BNumbers.RING_OF_NUM_1
def RING_OF_NUM_ADD : thm := BNumbers.RING_OF_NUM_ADD
def RING_OF_NUM_MUL : thm := BNumbers.RING_OF_NUM_MUL
def RING_OF_INT_0 : thm := BNumbers.RING_OF_INT_0
def RING_OF_INT_1 : thm := BNumbers.RING_OF_INT_1
def RING_OF_INT_CASES : thm := BNumbers.RING_OF_INT_CASES
def RING_OF_INT_NEG : thm := BNumbers.RING_OF_INT_NEG
def RING_OF_INT_ADD : thm := BNumbers.RING_OF_INT_ADD
def RING_OF_INT_MUL : thm := BNumbers.RING_OF_INT_MUL
def RING_OF_INT_SUB : thm := BNumbers.RING_OF_INT_SUB
def RING_OF_NUM_EQ_0 : thm := BNumbers.RING_OF_NUM_EQ_0
def RING_CHAR_EQ_0 : thm := BNumbers.RING_CHAR_EQ_0
def RING_CHAR_EQ_1 : thm := BNumbers.RING_CHAR_EQ_1
def RING_OF_INT_EQ_0 : thm := BNumbers.RING_OF_INT_EQ_0
def RING_OF_INT_EQ : thm := BNumbers.RING_OF_INT_EQ
def RING_OF_INT_EQ_0_CHAR_0 : thm := BNumbers.RING_OF_INT_EQ_0_CHAR_0
def RING_OF_INT_EQ_CHAR_0 : thm := BNumbers.RING_OF_INT_EQ_CHAR_0
def RING_OF_NUM_EQ : thm := BNumbers.RING_OF_NUM_EQ
def RING_OF_INT_REM : thm := BNumbers.RING_OF_INT_REM
def RING_OF_NUM_MOD : thm := BNumbers.RING_OF_NUM_MOD
def RING_OF_NUM_CHAR : thm := BNumbers.RING_OF_NUM_CHAR
def RING_CHAR_INFINITE : thm := BNumbers.RING_CHAR_INFINITE
def RING_CHAR_FINITE : thm := BNumbers.RING_CHAR_FINITE
def RING_CHAR_UNIQUE : thm := BNumbers.RING_CHAR_UNIQUE
def ring_pow : thm := BNumbers.ring_pow
def RING_POW : thm := BNumbers.RING_POW
def RING_POW_ZERO : thm := BNumbers.RING_POW_ZERO
def RING_POW_0 : thm := BNumbers.RING_POW_0
def RING_POW_1 : thm := BNumbers.RING_POW_1
def RING_POW_2 : thm := BNumbers.RING_POW_2
def RING_POW_ONE : thm := BNumbers.RING_POW_ONE
def RING_POW_ADD : thm := BNumbers.RING_POW_ADD
def RING_POW_MUL : thm := BNumbers.RING_POW_MUL
def RING_POW_POW : thm := BNumbers.RING_POW_POW
def RING_MUL_POW : thm := BNumbers.RING_MUL_POW
def RING_OF_NUM_EXP : thm := BNumbers.RING_OF_NUM_EXP
def RING_OF_INT_POW : thm := BNumbers.RING_OF_INT_POW
def RING_POW_NEG : thm := BNumbers.RING_POW_NEG
def RING_POW_IDEMPOTENT : thm := BNumbers.RING_POW_IDEMPOTENT
def RING_OF_NUM_CLAUSES : thm := BNumbers.RING_OF_NUM_CLAUSES
def RING_OF_INT_CLAUSES : thm := BNumbers.RING_OF_INT_CLAUSES

-- Sums
def ring_sum : thm := BSums.ring_sum
def NEUTRAL_RING_ADD : thm := BSums.NEUTRAL_RING_ADD
def MONOIDAL_RING_ADD : thm := BSums.MONOIDAL_RING_ADD
def RING_SUM : thm := BSums.RING_SUM
def RING_SUM_RESTRICT : thm := BSums.RING_SUM_RESTRICT
def RING_SUM_SUPPORT : thm := BSums.RING_SUM_SUPPORT
def RING_SUM_TRIVIAL : thm := BSums.RING_SUM_TRIVIAL
def RING_SUM_CLAUSES : thm := BSums.RING_SUM_CLAUSES
def RING_SUM_SING : thm := BSums.RING_SUM_SING
def RING_SUM_CLAUSES_NUMSEG_ALT : thm := BSums.RING_SUM_CLAUSES_NUMSEG_ALT
def RING_SUM_CLAUSES_NUMSEG : thm := BSums.RING_SUM_CLAUSES_NUMSEG
def RING_SUM_CLAUSES_LEFT : thm := BSums.RING_SUM_CLAUSES_LEFT
def RING_SUM_CLAUSES_RIGHT : thm := BSums.RING_SUM_CLAUSES_RIGHT
def RING_SUM_LT_2 : thm := BSums.RING_SUM_LT_2
def RING_SUM_UNION : thm := BSums.RING_SUM_UNION
def RING_SUM_DIFF : thm := BSums.RING_SUM_DIFF
def RING_SUM_INCL_EXCL : thm := BSums.RING_SUM_INCL_EXCL
def RING_SUM_CLOSED : thm := BSums.RING_SUM_CLOSED
def RING_SUM_RELATED : thm := BSums.RING_SUM_RELATED
def RING_SUM_EQ_0 : thm := BSums.RING_SUM_EQ_0
def RING_SUM_0 : thm := BSums.RING_SUM_0
def RING_SUM_DELETE : thm := BSums.RING_SUM_DELETE
def RING_SUM_NEG : thm := BSums.RING_SUM_NEG
def RING_SUM_ADD : thm := BSums.RING_SUM_ADD
def RING_SUM_SUB : thm := BSums.RING_SUM_SUB
def RING_SUM_EQ : thm := BSums.RING_SUM_EQ
def RING_SUM_DELTA : thm := BSums.RING_SUM_DELTA
def RING_SUM_LMUL : thm := BSums.RING_SUM_LMUL
def RING_SUM_RMUL : thm := BSums.RING_SUM_RMUL
def RING_SUM_SWAP : thm := BSums.RING_SUM_SWAP
def RING_SUM_REFLECT : thm := BSums.RING_SUM_REFLECT
def RING_SUM_SUM_PRODUCT : thm := BSums.RING_SUM_SUM_PRODUCT
def RING_SUM_SUPERSET : thm := BSums.RING_SUM_SUPERSET
def RING_SUM_RESTRICT_SET : thm := BSums.RING_SUM_RESTRICT_SET
def RING_SUM_CASES : thm := BSums.RING_SUM_CASES
def RING_SUM_IMAGE : thm := BSums.RING_SUM_IMAGE
def RING_SUM_EQ_GENERAL_INVERSES : thm := BSums.RING_SUM_EQ_GENERAL_INVERSES
def RING_SUM_MUL_MOD_DIV : thm := BSums.RING_SUM_MUL_MOD_DIV
def RING_SUM_OFFSET : thm := BSums.RING_SUM_OFFSET
def RING_SUM_NUMSEG_LT_ADD : thm := BSums.RING_SUM_NUMSEG_LT_ADD
def RING_SUM_CONST : thm := BSums.RING_SUM_CONST
def RING_SUM_IMAGE_GEN : thm := BSums.RING_SUM_IMAGE_GEN
def RING_SUM_UNIONS_PAIRWISE_DISJOINT : thm := BSums.RING_SUM_UNIONS_PAIRWISE_DISJOINT
def RING_BINOMIAL_THEOREM : thm := BSums.RING_BINOMIAL_THEOREM
def RING_BINOMIAL_FRESHMAN : thm := BSums.RING_BINOMIAL_FRESHMAN
def RING_SUM_DIFFS : thm := BSums.RING_SUM_DIFFS
def RING_SUM_DIFFS_ALT : thm := BSums.RING_SUM_DIFFS_ALT
def RING_GEOM_SERIES_GEN : thm := BSums.RING_GEOM_SERIES_GEN
def RING_GEOM_SERIES : thm := BSums.RING_GEOM_SERIES

-- Products
def ring_product : thm := BProducts.ring_product
def NEUTRAL_RING_MUL : thm := BProducts.NEUTRAL_RING_MUL
def MONOIDAL_RING_MUL : thm := BProducts.MONOIDAL_RING_MUL
def RING_PRODUCT : thm := BProducts.RING_PRODUCT
def RING_PRODUCT_RESTRICT : thm := BProducts.RING_PRODUCT_RESTRICT
def RING_PRODUCT_SUPPORT : thm := BProducts.RING_PRODUCT_SUPPORT
def RING_PRODUCT_TRIVIAL : thm := BProducts.RING_PRODUCT_TRIVIAL
def RING_PRODUCT_CLAUSES : thm := BProducts.RING_PRODUCT_CLAUSES
def RING_PRODUCT_SING : thm := BProducts.RING_PRODUCT_SING
def RING_PRODUCT_CLAUSES_NUMSEG_ALT : thm := BProducts.RING_PRODUCT_CLAUSES_NUMSEG_ALT
def RING_PRODUCT_CLAUSES_NUMSEG : thm := BProducts.RING_PRODUCT_CLAUSES_NUMSEG
def RING_PRODUCT_CLAUSES_LEFT : thm := BProducts.RING_PRODUCT_CLAUSES_LEFT
def RING_PRODUCT_LT_2 : thm := BProducts.RING_PRODUCT_LT_2
def RING_PRODUCT_UNION : thm := BProducts.RING_PRODUCT_UNION
def RING_PRODUCT_INCL_EXCL : thm := BProducts.RING_PRODUCT_INCL_EXCL
def RING_PRODUCT_CLOSED : thm := BProducts.RING_PRODUCT_CLOSED
def RING_PRODUCT_RELATED : thm := BProducts.RING_PRODUCT_RELATED
def RING_PRODUCT_EQ_1 : thm := BProducts.RING_PRODUCT_EQ_1
def RING_PRODUCT_1 : thm := BProducts.RING_PRODUCT_1
def RING_PRODUCT_0 : thm := BProducts.RING_PRODUCT_0
def RING_PRODUCT_ZERO : thm := BProducts.RING_PRODUCT_ZERO
def RING_PRODUCT_MUL : thm := BProducts.RING_PRODUCT_MUL
def RING_PRODUCT_EQ : thm := BProducts.RING_PRODUCT_EQ
def RING_PRODUCT_DELTA : thm := BProducts.RING_PRODUCT_DELTA
def RING_PRODUCT_CONST : thm := BProducts.RING_PRODUCT_CONST
def RING_PRODUCT_LMUL : thm := BProducts.RING_PRODUCT_LMUL
def RING_PRODUCT_SWAP : thm := BProducts.RING_PRODUCT_SWAP
def RING_PRODUCT_REFLECT : thm := BProducts.RING_PRODUCT_REFLECT
def RING_PRODUCT_SUPERSET : thm := BProducts.RING_PRODUCT_SUPERSET
def RING_PRODUCT_RESTRICT_SET : thm := BProducts.RING_PRODUCT_RESTRICT_SET
def RING_PRODUCT_CASES : thm := BProducts.RING_PRODUCT_CASES
def RING_PRODUCT_IMAGE : thm := BProducts.RING_PRODUCT_IMAGE
def RING_PRODUCT_EQ_GENERAL_INVERSES : thm := BProducts.RING_PRODUCT_EQ_GENERAL_INVERSES
def RING_PRODUCT_OFFSET : thm := BProducts.RING_PRODUCT_OFFSET
def RING_PRODUCT_IMAGE_GEN : thm := BProducts.RING_PRODUCT_IMAGE_GEN
def RING_PRODUCT_UNIONS_PAIRWISE_DISJOINT : thm := BProducts.RING_PRODUCT_UNIONS_PAIRWISE_DISJOINT
def RING_PRODUCT_NSUM : thm := BProducts.RING_PRODUCT_NSUM
def RING_PRODUCT_POW : thm := BProducts.RING_PRODUCT_POW
def RING_PRODUCT_POW_NEG : thm := BProducts.RING_PRODUCT_POW_NEG
def RING_PRODUCT_PAIRS_LT : thm := BProducts.RING_PRODUCT_PAIRS_LT

-- Divides
def ring_divides : thm := BDivides.ring_divides
def ring_zerodivisor : thm := BDivides.ring_zerodivisor
def ring_regular : thm := BDivides.ring_regular
def ring_nilpotent : thm := BDivides.ring_nilpotent
def ring_unit : thm := BDivides.ring_unit
def ring_associates : thm := BDivides.ring_associates
def ring_coprime : thm := BDivides.ring_coprime
def ring_inv : thm := BDivides.ring_inv
def ring_div : thm := BDivides.ring_div
def RING_DIVIDES_ALT : thm := BDivides.RING_DIVIDES_ALT
def RING_DIVIDES_IN_CARRIER : thm := BDivides.RING_DIVIDES_IN_CARRIER
def RING_ZERODIVISOR_IN_CARRIER : thm := BDivides.RING_ZERODIVISOR_IN_CARRIER
def RING_REGULAR_IN_CARRIER : thm := BDivides.RING_REGULAR_IN_CARRIER
def RING_NILPOTENT_IN_CARRIER : thm := BDivides.RING_NILPOTENT_IN_CARRIER
def RING_UNIT_IN_CARRIER : thm := BDivides.RING_UNIT_IN_CARRIER
def RING_ASSOCIATES_IN_CARRIER : thm := BDivides.RING_ASSOCIATES_IN_CARRIER
def RING_COPRIME_IN_CARRIER : thm := BDivides.RING_COPRIME_IN_CARRIER
def RING_INV : thm := BDivides.RING_INV
def RING_MUL_RINV : thm := BDivides.RING_MUL_RINV
def RING_MUL_LINV : thm := BDivides.RING_MUL_LINV
def RING_DIV : thm := BDivides.RING_DIV
def RING_CLAUSES : thm := BDivides.RING_CLAUSES
def RING_RINV_UNIQUE : thm := BDivides.RING_RINV_UNIQUE
def RING_LINV_UNIQUE : thm := BDivides.RING_LINV_UNIQUE
def RING_INV_1 : thm := BDivides.RING_INV_1
def RING_DIV_1 : thm := BDivides.RING_DIV_1
def RING_1_DIV : thm := BDivides.RING_1_DIV
def RING_INV_ZERO : thm := BDivides.RING_INV_ZERO
def RING_INV_MUL : thm := BDivides.RING_INV_MUL
def RING_INV_POW : thm := BDivides.RING_INV_POW
def RING_POW_INV : thm := BDivides.RING_POW_INV
def RING_INV_INV : thm := BDivides.RING_INV_INV
def RING_INV_MUL_INV : thm := BDivides.RING_INV_MUL_INV
def RING_MUL_INV_CANCEL : thm := BDivides.RING_MUL_INV_CANCEL
def RING_MUL_RINV_EQ : thm := BDivides.RING_MUL_RINV_EQ
def RING_MUL_LINV_EQ : thm := BDivides.RING_MUL_LINV_EQ
def RING_UNIT_DIVIDES : thm := BDivides.RING_UNIT_DIVIDES
def RING_UNIT_0 : thm := BDivides.RING_UNIT_0
def RING_INV_0 : thm := BDivides.RING_INV_0
def RING_UNIT_1 : thm := BDivides.RING_UNIT_1
def RING_UNIT_NEG : thm := BDivides.RING_UNIT_NEG
def RING_UNIT_NEG_EQ : thm := BDivides.RING_UNIT_NEG_EQ
def RING_UNIT_INV : thm := BDivides.RING_UNIT_INV
def RING_UNIT_MUL : thm := BDivides.RING_UNIT_MUL
def RING_UNIT_DIV : thm := BDivides.RING_UNIT_DIV
def RING_MUL_IMP_UNITS : thm := BDivides.RING_MUL_IMP_UNITS
def RING_UNIT_MUL_EQ : thm := BDivides.RING_UNIT_MUL_EQ
def RING_UNIT_POW : thm := BDivides.RING_UNIT_POW
def RING_UNIT_POW_EQ : thm := BDivides.RING_UNIT_POW_EQ
def RING_UNIT_DIVIDES_ANY : thm := BDivides.RING_UNIT_DIVIDES_ANY
def RING_UNIT_DIVISOR : thm := BDivides.RING_UNIT_DIVISOR
def RING_UNIT_PRODUCT : thm := BDivides.RING_UNIT_PRODUCT
def RING_MUL_LCANCEL : thm := BDivides.RING_MUL_LCANCEL
def RING_MUL_LCANCEL_EQ : thm := BDivides.RING_MUL_LCANCEL_EQ
def RING_MUL_RCANCEL : thm := BDivides.RING_MUL_RCANCEL
def RING_MUL_RCANCEL_EQ : thm := BDivides.RING_MUL_RCANCEL_EQ
def RING_DIVIDES_REFL : thm := BDivides.RING_DIVIDES_REFL
def RING_DIVIDES_TRANS : thm := BDivides.RING_DIVIDES_TRANS
def RING_DIVIDES_CHAIN : thm := BDivides.RING_DIVIDES_CHAIN
def RING_DIVIDES_MORE_DIVISORS : thm := BDivides.RING_DIVIDES_MORE_DIVISORS
def RING_DIVIDES_ANTISYM : thm := BDivides.RING_DIVIDES_ANTISYM
def RING_DIVIDES_ASSOCIATES : thm := BDivides.RING_DIVIDES_ASSOCIATES
def RING_DIVIDES_0 : thm := BDivides.RING_DIVIDES_0
def RING_DIVIDES_ZERO : thm := BDivides.RING_DIVIDES_ZERO
def RING_DIVIDES_1 : thm := BDivides.RING_DIVIDES_1
def RING_DIVIDES_ONE : thm := BDivides.RING_DIVIDES_ONE
def RING_UNIT_DIVIDES_ALL : thm := BDivides.RING_UNIT_DIVIDES_ALL
def RING_DIVIDES_ADD : thm := BDivides.RING_DIVIDES_ADD
def RING_DIVIDES_SUB : thm := BDivides.RING_DIVIDES_SUB
def RING_DIVIDES_LNEG : thm := BDivides.RING_DIVIDES_LNEG
def RING_DIVIDES_NEG : thm := BDivides.RING_DIVIDES_NEG
def RING_DIVIDES_NEG_EQ : thm := BDivides.RING_DIVIDES_NEG_EQ
def RING_DIVIDES_RMUL : thm := BDivides.RING_DIVIDES_RMUL
def RING_DIVIDES_LMUL : thm := BDivides.RING_DIVIDES_LMUL
def RING_DIVIDES_LMUL_REV : thm := BDivides.RING_DIVIDES_LMUL_REV
def RING_DIVIDES_RMUL_REV : thm := BDivides.RING_DIVIDES_RMUL_REV
def RING_DIVIDES_MUL2 : thm := BDivides.RING_DIVIDES_MUL2
def RING_DIVIDES_LMUL2 : thm := BDivides.RING_DIVIDES_LMUL2
def RING_DIVIDES_RMUL2 : thm := BDivides.RING_DIVIDES_RMUL2
def RING_DIVIDES_SUB_POW : thm := BDivides.RING_DIVIDES_SUB_POW
def RING_DIVIDES_PRODUCTS : thm := BDivides.RING_DIVIDES_PRODUCTS
def RING_DIVIDES_PRODUCT_SUBSET : thm := BDivides.RING_DIVIDES_PRODUCT_SUBSET
def RING_DIVIDES_PRODUCT_POW : thm := BDivides.RING_DIVIDES_PRODUCT_POW
def RING_ASSOCIATES_REFL : thm := BDivides.RING_ASSOCIATES_REFL
def RING_ASSOCIATES_SYM : thm := BDivides.RING_ASSOCIATES_SYM
def RING_ASSOCIATES_TRANS : thm := BDivides.RING_ASSOCIATES_TRANS
def FINITE_ASSOCIATE_REPRESENTATIVES : thm := BDivides.FINITE_ASSOCIATE_REPRESENTATIVES
def RING_ASSOCIATES_SAME_DIVISORS : thm := BDivides.RING_ASSOCIATES_SAME_DIVISORS
def RING_ASSOCIATES_0 : thm := BDivides.RING_ASSOCIATES_0
def RING_ASSOCIATES_1 : thm := BDivides.RING_ASSOCIATES_1
def RING_ASSOCIATES_LNEG : thm := BDivides.RING_ASSOCIATES_LNEG
def RING_ASSOCIATES_NEG : thm := BDivides.RING_ASSOCIATES_NEG
def RING_ASSOCIATES_NEG_EQ : thm := BDivides.RING_ASSOCIATES_NEG_EQ
def RING_ASSOCIATES_MUL : thm := BDivides.RING_ASSOCIATES_MUL
def RING_ASSOCIATES_POW : thm := BDivides.RING_ASSOCIATES_POW
def RING_ASSOCIATES_PRODUCT : thm := BDivides.RING_ASSOCIATES_PRODUCT
def RING_ZERODIVISOR_0 : thm := BDivides.RING_ZERODIVISOR_0
def RING_REGULAR_0 : thm := BDivides.RING_REGULAR_0
def RING_ZERODIVISOR_1 : thm := BDivides.RING_ZERODIVISOR_1
def RING_REGULAR_1 : thm := BDivides.RING_REGULAR_1
def RING_ZERODIVISOR_LMUL : thm := BDivides.RING_ZERODIVISOR_LMUL
def RING_ZERODIVISOR_RMUL : thm := BDivides.RING_ZERODIVISOR_RMUL
def RING_ZERODIVISOR_MUL : thm := BDivides.RING_ZERODIVISOR_MUL
def RING_ZERODIVISOR_POW : thm := BDivides.RING_ZERODIVISOR_POW
def RING_REGULAR_MUL_EQ : thm := BDivides.RING_REGULAR_MUL_EQ
def RING_REGULAR_POW : thm := BDivides.RING_REGULAR_POW
def RING_REGULAR_MUL : thm := BDivides.RING_REGULAR_MUL
def RING_ZERODIVISOR_NEG : thm := BDivides.RING_ZERODIVISOR_NEG
def RING_ZERODIVISOR_NEG_EQ : thm := BDivides.RING_ZERODIVISOR_NEG_EQ
def RING_REGULAR_NEG : thm := BDivides.RING_REGULAR_NEG
def RING_REGULAR_NEG_EQ : thm := BDivides.RING_REGULAR_NEG_EQ
def RING_ZERODIVISOR_IMP_NONUNIT : thm := BDivides.RING_ZERODIVISOR_IMP_NONUNIT
def RING_UNIT_IMP_REGULAR : thm := BDivides.RING_UNIT_IMP_REGULAR
def RING_DIVIDES_UNIT : thm := BDivides.RING_DIVIDES_UNIT
def RING_COPRIME_REFL : thm := BDivides.RING_COPRIME_REFL
def RING_COPRIME_SYM : thm := BDivides.RING_COPRIME_SYM
def RING_COPRIME_0 : thm := BDivides.RING_COPRIME_0
def RING_COPRIME_00 : thm := BDivides.RING_COPRIME_00
def RING_COPRIME_DIVISORS : thm := BDivides.RING_COPRIME_DIVISORS
def RING_COPRIME_UNIT : thm := BDivides.RING_COPRIME_UNIT
def RING_ASSOCIATES_RMUL : thm := BDivides.RING_ASSOCIATES_RMUL
def RING_ASSOCIATES_LMUL : thm := BDivides.RING_ASSOCIATES_LMUL
def RING_ASSOCIATES_DIVIDES : thm := BDivides.RING_ASSOCIATES_DIVIDES
def RING_ASSOCIATES_ASSOCIATES : thm := BDivides.RING_ASSOCIATES_ASSOCIATES
def RING_ASSOCIATES_UNIT : thm := BDivides.RING_ASSOCIATES_UNIT
def RING_ASSOCIATES_EQ_0 : thm := BDivides.RING_ASSOCIATES_EQ_0
def RING_ASSOCIATES_COPRIME : thm := BDivides.RING_ASSOCIATES_COPRIME
def RING_ASSOCIATES_ZERODIVISOR : thm := BDivides.RING_ASSOCIATES_ZERODIVISOR
def RING_ASSOCIATES_REGULAR : thm := BDivides.RING_ASSOCIATES_REGULAR
def RING_ASSOCIATES_NILPOTENT : thm := BDivides.RING_ASSOCIATES_NILPOTENT
def RING_NILPOTENT_0 : thm := BDivides.RING_NILPOTENT_0
def RING_NILPOTENT_1 : thm := BDivides.RING_NILPOTENT_1
def RING_NILPOTENT : thm := BDivides.RING_NILPOTENT
def RING_NILPOTENT_POW : thm := BDivides.RING_NILPOTENT_POW
def RING_NILPOTENT_IMP_ZERODIVISOR : thm := BDivides.RING_NILPOTENT_IMP_ZERODIVISOR
def RING_NILPOTENT_NEG : thm := BDivides.RING_NILPOTENT_NEG
def RING_NILPOTENT_NEG_EQ : thm := BDivides.RING_NILPOTENT_NEG_EQ
def RING_UNIT_IDEMPOTENT_EQ_1 : thm := BDivides.RING_UNIT_IDEMPOTENT_EQ_1

-- Subrings
def subring_of : thm := BSubrings.subring_of
def subring_generated : thm := BSubrings.subring_generated
def IN_SUBRING_0 : thm := BSubrings.IN_SUBRING_0
def IN_SUBRING_1 : thm := BSubrings.IN_SUBRING_1
def IN_SUBRING_NEG : thm := BSubrings.IN_SUBRING_NEG
def IN_SUBRING_ADD : thm := BSubrings.IN_SUBRING_ADD
def IN_SUBRING_MUL : thm := BSubrings.IN_SUBRING_MUL
def IN_SUBRING_SUB : thm := BSubrings.IN_SUBRING_SUB
def IN_SUBRING_POW : thm := BSubrings.IN_SUBRING_POW
def IN_SUBRING_NUM : thm := BSubrings.IN_SUBRING_NUM
def IN_SUBRING_INT : thm := BSubrings.IN_SUBRING_INT
def IN_SUBRING_SUM : thm := BSubrings.IN_SUBRING_SUM
def IN_SUBRING_PRODUCT : thm := BSubrings.IN_SUBRING_PRODUCT
def SUBRING_OF_INTERS : thm := BSubrings.SUBRING_OF_INTERS
def SUBRING_OF_INTER : thm := BSubrings.SUBRING_OF_INTER
def SUBRING_OF_UNIONS : thm := BSubrings.SUBRING_OF_UNIONS
def SUBRING_OF_IMP_SUBSET : thm := BSubrings.SUBRING_OF_IMP_SUBSET
def SUBRING_OF_IMP_NONEMPTY : thm := BSubrings.SUBRING_OF_IMP_NONEMPTY
def CARRIER_SUBRING_OF : thm := BSubrings.CARRIER_SUBRING_OF
def PRIME_SUBRING : thm := BSubrings.PRIME_SUBRING
def PRIME_SUBRING_MINIMAL : thm := BSubrings.PRIME_SUBRING_MINIMAL
def SUBRING_GENERATED : thm := BSubrings.SUBRING_GENERATED
def SUBRING_GENERATED_EQ : thm := BSubrings.SUBRING_GENERATED_EQ
def RING_SUB_SUBRING_GENERATED : thm := BSubrings.RING_SUB_SUBRING_GENERATED
def RING_POW_SUBRING_GENERATED : thm := BSubrings.RING_POW_SUBRING_GENERATED
def RING_OF_NUM_SUBRING_GENERATED : thm := BSubrings.RING_OF_NUM_SUBRING_GENERATED
def RING_OF_INT_SUBRING_GENERATED : thm := BSubrings.RING_OF_INT_SUBRING_GENERATED
def RING_0_IN_SUBRING_GENERATED : thm := BSubrings.RING_0_IN_SUBRING_GENERATED
def RING_1_IN_SUBRING_GENERATED : thm := BSubrings.RING_1_IN_SUBRING_GENERATED
def RING_NEG_IN_SUBRING_GENERATED : thm := BSubrings.RING_NEG_IN_SUBRING_GENERATED
def RING_ADD_IN_SUBRING_GENERATED : thm := BSubrings.RING_ADD_IN_SUBRING_GENERATED
def RING_MUL_IN_SUBRING_GENERATED : thm := BSubrings.RING_MUL_IN_SUBRING_GENERATED
def RING_POW_IN_SUBRING_GENERATED : thm := BSubrings.RING_POW_IN_SUBRING_GENERATED
def SUBRING_GENERATED_RESTRICT : thm := BSubrings.SUBRING_GENERATED_RESTRICT
def SUBRING_SUBRING_GENERATED : thm := BSubrings.SUBRING_SUBRING_GENERATED
def SUBRING_GENERATED_MONO : thm := BSubrings.SUBRING_GENERATED_MONO
def SUBRING_GENERATED_MINIMAL : thm := BSubrings.SUBRING_GENERATED_MINIMAL
def SUBRINGS_GENERATED_EQ : thm := BSubrings.SUBRINGS_GENERATED_EQ
def SUBRING_GENERATED_INDUCT : thm := BSubrings.SUBRING_GENERATED_INDUCT
def SUBRING_GENERATED_INDUCT_STRONG : thm := BSubrings.SUBRING_GENERATED_INDUCT_STRONG
def RING_CARRIER_SUBRING_GENERATED_SUBSET : thm := BSubrings.RING_CARRIER_SUBRING_GENERATED_SUBSET
def SUBRING_OF_SUBRING_GENERATED_EQ : thm := BSubrings.SUBRING_OF_SUBRING_GENERATED_EQ
def SUBRING_GENERATED_SUPERSET : thm := BSubrings.SUBRING_GENERATED_SUPERSET
def FINITE_SUBRING_GENERATED : thm := BSubrings.FINITE_SUBRING_GENERATED
def SUBRING_GENERATED_SUBSET_CARRIER : thm := BSubrings.SUBRING_GENERATED_SUBSET_CARRIER
def SUBSET_CARRIER_SUBRING_GENERATED : thm := BSubrings.SUBSET_CARRIER_SUBRING_GENERATED
def CARRIER_SUBRING_GENERATED_SUBRING : thm := BSubrings.CARRIER_SUBRING_GENERATED_SUBRING
def RING_UNIT_SUBRING_GENERATED : thm := BSubrings.RING_UNIT_SUBRING_GENERATED
def RING_INV_SUBRING_GENERATED_GEN : thm := BSubrings.RING_INV_SUBRING_GENERATED_GEN
def SUBRING_GENERATED_MINIMAL_EQ : thm := BSubrings.SUBRING_GENERATED_MINIMAL_EQ
def SUBRING_OF_SUBRING_GENERATED_SUBRING_EQ : thm := BSubrings.SUBRING_OF_SUBRING_GENERATED_SUBRING_EQ
def SUBRING_GENERATED_RING_CARRIER : thm := BSubrings.SUBRING_GENERATED_RING_CARRIER
def SUBRING_OF_SUBRING_GENERATED : thm := BSubrings.SUBRING_OF_SUBRING_GENERATED
def SUBRING_GENERATED_SUBSET_CARRIER_SUBSET : thm := BSubrings.SUBRING_GENERATED_SUBSET_CARRIER_SUBSET
def SUBRING_GENERATED_REFL : thm := BSubrings.SUBRING_GENERATED_REFL
def SUBRING_GENERATED_INC : thm := BSubrings.SUBRING_GENERATED_INC
def SUBRING_GENERATED_INC_GEN : thm := BSubrings.SUBRING_GENERATED_INC_GEN
def SUBRING_OF_SUBRING_GENERATED_REV : thm := BSubrings.SUBRING_OF_SUBRING_GENERATED_REV
def TRIVIAL_RING_SUBRING_GENERATED : thm := BSubrings.TRIVIAL_RING_SUBRING_GENERATED
def SUBRING_GENERATED_BY_SUBRING_GENERATED : thm := BSubrings.SUBRING_GENERATED_BY_SUBRING_GENERATED
def SUBRING_GENERATED_INSERT_ZERO : thm := BSubrings.SUBRING_GENERATED_INSERT_ZERO
def RING_CARRIER_SUBRING_GENERATED_MONO : thm := BSubrings.RING_CARRIER_SUBRING_GENERATED_MONO
def SUBRING_GENERATED_IDEMPOT_GEN : thm := BSubrings.SUBRING_GENERATED_IDEMPOT_GEN
def SUBRING_GENERATED_IDEMPOT : thm := BSubrings.SUBRING_GENERATED_IDEMPOT
def SUBRING_GENERATED_SUBRING_GENERATED : thm := BSubrings.SUBRING_GENERATED_SUBRING_GENERATED
def SUBRING_GENERATED_BY_SUBRING_GENERATED_IDEMPOT : thm := BSubrings.SUBRING_GENERATED_BY_SUBRING_GENERATED_IDEMPOT
def SUBRING_GENERATED_UNION_LEFT : thm := BSubrings.SUBRING_GENERATED_UNION_LEFT
def SUBRING_GENERATED_UNION_RIGHT : thm := BSubrings.SUBRING_GENERATED_UNION_RIGHT
def SUBRING_GENERATED_UNION : thm := BSubrings.SUBRING_GENERATED_UNION
def SUBRING_GENERATED_INSERT : thm := BSubrings.SUBRING_GENERATED_INSERT
def RING_CHAR_SUBRING_GENERATED : thm := BSubrings.RING_CHAR_SUBRING_GENERATED
def IN_SUBRING_GENERATED_FINITARY : thm := BSubrings.IN_SUBRING_GENERATED_FINITARY
def SUBRING_GENERATED_FINITARY : thm := BSubrings.SUBRING_GENERATED_FINITARY
def SUBSET_SUBRING_GENERATED_FINITARY : thm := BSubrings.SUBSET_SUBRING_GENERATED_FINITARY
def SUBRING_GENERATED_PRIME_SUBRING : thm := BSubrings.SUBRING_GENERATED_PRIME_SUBRING
def RING_CARRIER_SUBRING_GENERATED_0 : thm := BSubrings.RING_CARRIER_SUBRING_GENERATED_0

-- Ideals
def ring_ideal : thm := BIdeals.ring_ideal
def RING_IDEAL : thm := BIdeals.RING_IDEAL
def RING_IDEAL_IMP_SUBSET : thm := BIdeals.RING_IDEAL_IMP_SUBSET
def RING_IDEAL_IMP_NONEMPTY : thm := BIdeals.RING_IDEAL_IMP_NONEMPTY
def RING_IDEAL_0 : thm := BIdeals.RING_IDEAL_0
def IN_RING_IDEAL_0 : thm := BIdeals.IN_RING_IDEAL_0
def IN_RING_IDEAL_NEG : thm := BIdeals.IN_RING_IDEAL_NEG
def IN_RING_IDEAL_ADD : thm := BIdeals.IN_RING_IDEAL_ADD
def IN_RING_IDEAL_SUB : thm := BIdeals.IN_RING_IDEAL_SUB
def IN_RING_IDEAL_MUL : thm := BIdeals.IN_RING_IDEAL_MUL
def IN_RING_IDEAL_LMUL : thm := BIdeals.IN_RING_IDEAL_LMUL
def IN_RING_IDEAL_RMUL : thm := BIdeals.IN_RING_IDEAL_RMUL
def RING_MULTIPLE_IN_IDEAL : thm := BIdeals.RING_MULTIPLE_IN_IDEAL
def RING_POW_IN_IDEAL : thm := BIdeals.RING_POW_IN_IDEAL
def IN_RING_IDEAL_SUM : thm := BIdeals.IN_RING_IDEAL_SUM
def RING_PRODUCT_IN_RING_IDEAL : thm := BIdeals.RING_PRODUCT_IN_RING_IDEAL
def RING_ASSOCIATES_IN_IDEAL : thm := BIdeals.RING_ASSOCIATES_IN_IDEAL
def RING_IDEAL_INTERS : thm := BIdeals.RING_IDEAL_INTERS
def RING_IDEAL_INTER : thm := BIdeals.RING_IDEAL_INTER
def RING_IDEAL_UNIONS : thm := BIdeals.RING_IDEAL_UNIONS
def RING_IDEAL_EQ_CARRIER : thm := BIdeals.RING_IDEAL_EQ_CARRIER
def RING_IDEAL_EQ_CARRIER_UNIT : thm := BIdeals.RING_IDEAL_EQ_CARRIER_UNIT
def TRIVIAL_RING_IDEAL : thm := BIdeals.TRIVIAL_RING_IDEAL
def RING_IDEAL_CARRIER : thm := BIdeals.RING_IDEAL_CARRIER
def RING_IDEAL_SUBRING_GENERATED_EQ : thm := BIdeals.RING_IDEAL_SUBRING_GENERATED_EQ
def RING_IDEAL_SUBRING_GENERATED : thm := BIdeals.RING_IDEAL_SUBRING_GENERATED
def RING_SUBRING_INTER_IDEAL : thm := BIdeals.RING_SUBRING_INTER_IDEAL
def RING_IDEAL_INTER_SUBRING : thm := BIdeals.RING_IDEAL_INTER_SUBRING
def ring_setneg : thm := BIdeals.ring_setneg
def ring_setadd : thm := BIdeals.ring_setadd
def ring_setmul : thm := BIdeals.ring_setmul
def RING_NEG_IN_SETNEG : thm := BIdeals.RING_NEG_IN_SETNEG
def RING_ADD_IN_SETADD : thm := BIdeals.RING_ADD_IN_SETADD
def RING_MUL_IN_SETMUL : thm := BIdeals.RING_MUL_IN_SETMUL
def RING_SETNEG_MONO : thm := BIdeals.RING_SETNEG_MONO
def RING_SETADD_MONO : thm := BIdeals.RING_SETADD_MONO
def RING_SETMUL_MONO : thm := BIdeals.RING_SETMUL_MONO
def SUBRING_OF_SETWISE : thm := BIdeals.SUBRING_OF_SETWISE
def RING_IDEAL_SETWISE : thm := BIdeals.RING_IDEAL_SETWISE
def RING_SETNEG_EQ_EMPTY : thm := BIdeals.RING_SETNEG_EQ_EMPTY
def RING_SETADD_EQ_EMPTY : thm := BIdeals.RING_SETADD_EQ_EMPTY
def RING_SETMUL_EQ_EMPTY : thm := BIdeals.RING_SETMUL_EQ_EMPTY
def RING_SETNEG_SING : thm := BIdeals.RING_SETNEG_SING
def RING_SETADD_SING : thm := BIdeals.RING_SETADD_SING
def RING_SETMUL_SING : thm := BIdeals.RING_SETMUL_SING
def RING_SETNEG : thm := BIdeals.RING_SETNEG
def RING_SETADD : thm := BIdeals.RING_SETADD
def RING_SETMUL : thm := BIdeals.RING_SETMUL
def RING_SETADD_SYM : thm := BIdeals.RING_SETADD_SYM
def RING_SETMUL_SYM : thm := BIdeals.RING_SETMUL_SYM
def RING_SETADD_LZERO : thm := BIdeals.RING_SETADD_LZERO
def RING_SETADD_RZERO : thm := BIdeals.RING_SETADD_RZERO
def RING_SETMUL_LID : thm := BIdeals.RING_SETMUL_LID
def RING_SETMUL_RID : thm := BIdeals.RING_SETMUL_RID
def RING_SETADD_ASSOC : thm := BIdeals.RING_SETADD_ASSOC
def RING_SETMUL_ASSOC : thm := BIdeals.RING_SETMUL_ASSOC
def RING_SETADD_AC : thm := BIdeals.RING_SETADD_AC
def RING_SETMUL_AC : thm := BIdeals.RING_SETMUL_AC
def RING_SETADD_SUPERSET_LEFT : thm := BIdeals.RING_SETADD_SUPERSET_LEFT
def RING_SETADD_SUPERSET_RIGHT : thm := BIdeals.RING_SETADD_SUPERSET_RIGHT
def RING_SETNEG_SETADD : thm := BIdeals.RING_SETNEG_SETADD
def RING_SETADD_LDISTRIB : thm := BIdeals.RING_SETADD_LDISTRIB
def RING_SETADD_RDISTRIB : thm := BIdeals.RING_SETADD_RDISTRIB
def RING_SETNEG_IDEAL : thm := BIdeals.RING_SETNEG_IDEAL
def RING_SETNEG_SUBRING : thm := BIdeals.RING_SETNEG_SUBRING
def RING_SETADD_LSUBSET : thm := BIdeals.RING_SETADD_LSUBSET
def RING_SETADD_RSUBSET : thm := BIdeals.RING_SETADD_RSUBSET
def RING_SETADD_LSUBSET_EQ : thm := BIdeals.RING_SETADD_LSUBSET_EQ
def RING_SETADD_RSUBSET_EQ : thm := BIdeals.RING_SETADD_RSUBSET_EQ
def RING_SETADD_SUBRING : thm := BIdeals.RING_SETADD_SUBRING
def RING_SETMUL_SUBRING : thm := BIdeals.RING_SETMUL_SUBRING
def RING_SETADD_SUBSET_IDEAL : thm := BIdeals.RING_SETADD_SUBSET_IDEAL
def RING_SETADD_IDEAL_LEFT : thm := BIdeals.RING_SETADD_IDEAL_LEFT
def RING_SETADD_IDEAL_RIGHT : thm := BIdeals.RING_SETADD_IDEAL_RIGHT
def RING_SETMUL_IDEAL_LEFT : thm := BIdeals.RING_SETMUL_IDEAL_LEFT
def RING_SETMUL_IDEAL_RIGHT : thm := BIdeals.RING_SETMUL_IDEAL_RIGHT
def RING_SETMUL_SUBSET_IDEAL : thm := BIdeals.RING_SETMUL_SUBSET_IDEAL
def RING_SETADD_LCANCEL : thm := BIdeals.RING_SETADD_LCANCEL
def RING_SETADD_RCANCEL : thm := BIdeals.RING_SETADD_RCANCEL
def RING_SETADD_LCANCEL_SET : thm := BIdeals.RING_SETADD_LCANCEL_SET
def RING_SETADD_RCANCEL_SET : thm := BIdeals.RING_SETADD_RCANCEL_SET
def RING_IDEAL_SETADD : thm := BIdeals.RING_IDEAL_SETADD
def SUBRING_SETADD_LEFT : thm := BIdeals.SUBRING_SETADD_LEFT
def SUBRING_SETADD_RIGHT : thm := BIdeals.SUBRING_SETADD_RIGHT
def RING_IDEAL_QUOTIENT : thm := BIdeals.RING_IDEAL_QUOTIENT
def RING_IDEAL_QUOTIENT_RMUL : thm := BIdeals.RING_IDEAL_QUOTIENT_RMUL
def RING_IDEAL_QUOTIENT_LMUL : thm := BIdeals.RING_IDEAL_QUOTIENT_LMUL
def RING_COMAXIMAL : thm := BIdeals.RING_COMAXIMAL
def ideal_generated : thm := BIdeals.ideal_generated
def IDEAL_GENERATED_RESTRICT : thm := BIdeals.IDEAL_GENERATED_RESTRICT
def RING_IDEAL_IDEAL_GENERATED : thm := BIdeals.RING_IDEAL_IDEAL_GENERATED
def IDEAL_GENERATED_NONEMPTY : thm := BIdeals.IDEAL_GENERATED_NONEMPTY
def IDEAL_GENERATED_MONO : thm := BIdeals.IDEAL_GENERATED_MONO
def IDEAL_GENERATED_MINIMAL : thm := BIdeals.IDEAL_GENERATED_MINIMAL
def IDEAL_GENERATED_INDUCT : thm := BIdeals.IDEAL_GENERATED_INDUCT
def IDEAL_GENERATED_INDUCT_STRONG : thm := BIdeals.IDEAL_GENERATED_INDUCT_STRONG
def IDEAL_GENERATED_SUBSET : thm := BIdeals.IDEAL_GENERATED_SUBSET
def FINITE_IDEAL_GENERATED : thm := BIdeals.FINITE_IDEAL_GENERATED
def IDEAL_GENERATED_SUBSET_CARRIER : thm := BIdeals.IDEAL_GENERATED_SUBSET_CARRIER
def IDEAL_GENERATED_MINIMAL_EQ : thm := BIdeals.IDEAL_GENERATED_MINIMAL_EQ
def IDEALS_GENERATED_SUBSET : thm := BIdeals.IDEALS_GENERATED_SUBSET
def IDEAL_GENERATED_RING_IDEAL : thm := BIdeals.IDEAL_GENERATED_RING_IDEAL
def IDEAL_GENERATED_RING_IDEAL_EQ : thm := BIdeals.IDEAL_GENERATED_RING_IDEAL_EQ
def IDEAL_GENERATED_RING_CARRIER : thm := BIdeals.IDEAL_GENERATED_RING_CARRIER
def IDEAL_GENERATED_SUBSET_CARRIER_SUBSET : thm := BIdeals.IDEAL_GENERATED_SUBSET_CARRIER_SUBSET
def IDEAL_GENERATED_REFL : thm := BIdeals.IDEAL_GENERATED_REFL
def IDEAL_GENERATED_INC : thm := BIdeals.IDEAL_GENERATED_INC
def IDEAL_GENERATED_INC_GEN : thm := BIdeals.IDEAL_GENERATED_INC_GEN
def IDEAL_GENERATED_BY_IDEAL_GENERATED : thm := BIdeals.IDEAL_GENERATED_BY_IDEAL_GENERATED
def IDEAL_GENERATED_INSERT_ZERO : thm := BIdeals.IDEAL_GENERATED_INSERT_ZERO
def IDEAL_GENERATED_0 : thm := BIdeals.IDEAL_GENERATED_0
def IDEAL_GENERATED_EMPTY : thm := BIdeals.IDEAL_GENERATED_EMPTY
def IDEAL_GENERATED_SING : thm := BIdeals.IDEAL_GENERATED_SING
def IDEAL_GENERATED_SING_ALT : thm := BIdeals.IDEAL_GENERATED_SING_ALT
def IN_IDEAL_GENERATED_SING_EQ : thm := BIdeals.IN_IDEAL_GENERATED_SING_EQ
def IN_IDEAL_GENERATED_SING : thm := BIdeals.IN_IDEAL_GENERATED_SING
def IN_IDEAL_GENERATED_SELF : thm := BIdeals.IN_IDEAL_GENERATED_SELF
def IDEAL_GENERATED_SING_EQ_CARRIER : thm := BIdeals.IDEAL_GENERATED_SING_EQ_CARRIER
def SUBSET_IDEALS_GENERATED_SING : thm := BIdeals.SUBSET_IDEALS_GENERATED_SING
def IDEALS_GENERATED_SING_EQ : thm := BIdeals.IDEALS_GENERATED_SING_EQ
def PSUBSET_IDEALS_GENERATED_SING : thm := BIdeals.PSUBSET_IDEALS_GENERATED_SING
def IDEAL_GENERATED_EQ_0 : thm := BIdeals.IDEAL_GENERATED_EQ_0
def IDEAL_GENERATED_SING_SETMUL_RIGHT : thm := BIdeals.IDEAL_GENERATED_SING_SETMUL_RIGHT
def IDEAL_GENERATED_SING_SETMUL_LEFT : thm := BIdeals.IDEAL_GENERATED_SING_SETMUL_LEFT
def RING_SETMUL_IDEAL_GENERATED_SING : thm := BIdeals.RING_SETMUL_IDEAL_GENERATED_SING
def IDEAL_GENERATED_UNION : thm := BIdeals.IDEAL_GENERATED_UNION
def IDEAL_GENERATED_INSERT : thm := BIdeals.IDEAL_GENERATED_INSERT
def IN_IDEAL_GENERATED_INSERT_IDEAL : thm := BIdeals.IN_IDEAL_GENERATED_INSERT_IDEAL
def IDEAL_GENERATED_2 : thm := BIdeals.IDEAL_GENERATED_2
def IDEAL_GENERATED_SETADD_SUBSET : thm := BIdeals.IDEAL_GENERATED_SETADD_SUBSET
def RING_SCALE_SETMUL : thm := BIdeals.RING_SCALE_SETMUL
def RING_IDEAL_SCALE : thm := BIdeals.RING_IDEAL_SCALE
def IDEAL_GENERATED_SCALE : thm := BIdeals.IDEAL_GENERATED_SCALE
def IDEAL_GENERATED_FINITARY : thm := BIdeals.IDEAL_GENERATED_FINITARY
def IDEAL_GENERATED_FINITARY_ALT : thm := BIdeals.IDEAL_GENERATED_FINITARY_ALT
def IDEAL_GENERATED_FINITE_IMAGE : thm := BIdeals.IDEAL_GENERATED_FINITE_IMAGE
def IDEAL_GENERATED_FINITE : thm := BIdeals.IDEAL_GENERATED_FINITE
def IDEAL_GENERATED_EXPLICIT : thm := BIdeals.IDEAL_GENERATED_EXPLICIT
def IDEAL_GENERATED_ADJOIN_EXPLICIT : thm := BIdeals.IDEAL_GENERATED_ADJOIN_EXPLICIT

-- Domains
def integral_domain : thm := BDomains.integral_domain
def field : thm := BDomains.field
def INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING : thm := BDomains.INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING
def FIELD_IMP_NONTRIVIAL_RING : thm := BDomains.FIELD_IMP_NONTRIVIAL_RING
def INTEGRAL_DOMAIN_NONTRIVIAL : thm := BDomains.INTEGRAL_DOMAIN_NONTRIVIAL
def FIELD_NONTRIVIAL : thm := BDomains.FIELD_NONTRIVIAL
def INTEGRAL_DOMAIN_EQ_NO_ZERODIVISORS : thm := BDomains.INTEGRAL_DOMAIN_EQ_NO_ZERODIVISORS
def INTEGRAL_DOMAIN_EQ_ALL_REGULAR : thm := BDomains.INTEGRAL_DOMAIN_EQ_ALL_REGULAR
def INTEGRAL_DOMAIN_ZERODIVISOR : thm := BDomains.INTEGRAL_DOMAIN_ZERODIVISOR
def INTEGRAL_DOMAIN_REGULAR : thm := BDomains.INTEGRAL_DOMAIN_REGULAR
def INTEGRAL_DOMAIN_MUL_EQ_0 : thm := BDomains.INTEGRAL_DOMAIN_MUL_EQ_0
def INTEGRAL_DOMAIN_POW_EQ_0 : thm := BDomains.INTEGRAL_DOMAIN_POW_EQ_0
def INTEGRAL_DOMAIN_SQUARE_EQ : thm := BDomains.INTEGRAL_DOMAIN_SQUARE_EQ
def INTEGRAL_DOMAIN_NILPOTENT : thm := BDomains.INTEGRAL_DOMAIN_NILPOTENT
def INTEGRAL_DOMAIN_PRODUCT_EQ_0 : thm := BDomains.INTEGRAL_DOMAIN_PRODUCT_EQ_0
def INTEGRAL_DOMAIN_MUL_LCANCEL : thm := BDomains.INTEGRAL_DOMAIN_MUL_LCANCEL
def INTEGRAL_DOMAIN_MUL_LCANCEL_EQ : thm := BDomains.INTEGRAL_DOMAIN_MUL_LCANCEL_EQ
def INTEGRAL_DOMAIN_MUL_RCANCEL : thm := BDomains.INTEGRAL_DOMAIN_MUL_RCANCEL
def INTEGRAL_DOMAIN_MUL_RCANCEL_EQ : thm := BDomains.INTEGRAL_DOMAIN_MUL_RCANCEL_EQ
def INTEGRAL_DOMAIN_DIVIDES_LMUL2 : thm := BDomains.INTEGRAL_DOMAIN_DIVIDES_LMUL2
def INTEGRAL_DOMAIN_DIVIDES_RMUL2 : thm := BDomains.INTEGRAL_DOMAIN_DIVIDES_RMUL2
def INTEGRAL_DOMAIN_ASSOCIATES_LMUL2 : thm := BDomains.INTEGRAL_DOMAIN_ASSOCIATES_LMUL2
def INTEGRAL_DOMAIN_ASSOCIATES_RMUL2 : thm := BDomains.INTEGRAL_DOMAIN_ASSOCIATES_RMUL2
def INTEGRAL_DOMAIN_MUL_EQ_SELF : thm := BDomains.INTEGRAL_DOMAIN_MUL_EQ_SELF
def INTEGRAL_DOMAIN_DIVIDES_MUL_SELF : thm := BDomains.INTEGRAL_DOMAIN_DIVIDES_MUL_SELF
def INTEGRAL_DOMAIN_DIVIDES_ASSOCIATES_MUL_SELF : thm := BDomains.INTEGRAL_DOMAIN_DIVIDES_ASSOCIATES_MUL_SELF
def FIELD_EQ_ALL_UNITS : thm := BDomains.FIELD_EQ_ALL_UNITS
def FIELD_EQ_ALL_DIVIDE_1 : thm := BDomains.FIELD_EQ_ALL_DIVIDE_1
def FIELD_UNIT : thm := BDomains.FIELD_UNIT
def FIELD_MUL_LINV : thm := BDomains.FIELD_MUL_LINV
def FIELD_MUL_RINV : thm := BDomains.FIELD_MUL_RINV
def RING_UNIT_SUBRING_OF_FIELD : thm := BDomains.RING_UNIT_SUBRING_OF_FIELD
def IDEAL_GENERATED_ADJOIN_INV : thm := BDomains.IDEAL_GENERATED_ADJOIN_INV
def FIELD_DIVIDES : thm := BDomains.FIELD_DIVIDES
def FIELD_ASSOCIATES : thm := BDomains.FIELD_ASSOCIATES
def FIELD_COPRIME : thm := BDomains.FIELD_COPRIME
def FIELD_IMP_INTEGRAL_DOMAIN : thm := BDomains.FIELD_IMP_INTEGRAL_DOMAIN
def FIELD_ZERODIVISOR : thm := BDomains.FIELD_ZERODIVISOR
def FIELD_REGULAR : thm := BDomains.FIELD_REGULAR
def FIELD_NILPOTENT : thm := BDomains.FIELD_NILPOTENT
def FIELD_MUL_EQ_0 : thm := BDomains.FIELD_MUL_EQ_0
def FIELD_POW_EQ_0 : thm := BDomains.FIELD_POW_EQ_0
def FIELD_PRODUCT_EQ_0 : thm := BDomains.FIELD_PRODUCT_EQ_0
def FINITE_INTEGRAL_DOMAIN_IMP_FIELD : thm := BDomains.FINITE_INTEGRAL_DOMAIN_IMP_FIELD
def FINITE_INTEGRAL_DOMAIN_EQ_FIELD : thm := BDomains.FINITE_INTEGRAL_DOMAIN_EQ_FIELD
def FINITE_FIELD_CARD_GE_2 : thm := BDomains.FINITE_FIELD_CARD_GE_2
def INTEGRAL_DOMAIN_CHAR : thm := BDomains.INTEGRAL_DOMAIN_CHAR
def RING_CHAR_DIVIDES_MUL : thm := BDomains.RING_CHAR_DIVIDES_MUL
def RING_CHAR_DIVIDES_PRIME : thm := BDomains.RING_CHAR_DIVIDES_PRIME
def FINITE_INTEGRAL_DOMAIN_CHAR : thm := BDomains.FINITE_INTEGRAL_DOMAIN_CHAR
def INTEGRAL_DOMAIN_SUBRING_GENERATED : thm := BDomains.INTEGRAL_DOMAIN_SUBRING_GENERATED
def INTEGRAL_DOMAIN_ASSOCIATES : thm := BDomains.INTEGRAL_DOMAIN_ASSOCIATES
def INTEGRAL_DOMAIN_10 : thm := BDomains.INTEGRAL_DOMAIN_10
def FIELD_10 : thm := BDomains.FIELD_10

-- Rules
def RING_CARRIER_RULE := BRules.RING_CARRIER_RULE
def RING_CARRIER_TAC : HolCore.Tactics.tactic := fun g => BRules.RING_CARRIER_TAC g
def RING_POLY_UNIVERSAL_CONV : HolCore.Equal.ioconv := fun t => BRules.RING_POLY_UNIVERSAL_CONV t
def RING_INTEGRAL_DOMAIN_UNIVERSAL := BRules.RING_INTEGRAL_DOMAIN_UNIVERSAL
def ring_ring_cofactors_universal := BRules.ring_ring_cofactors_universal

-- Homs
def ring_homomorphism : thm := BHoms.ring_homomorphism
def ring_monomorphism : thm := BHoms.ring_monomorphism
def ring_epimorphism : thm := BHoms.ring_epimorphism
def ring_endomorphism : thm := BHoms.ring_endomorphism
def ring_isomorphisms : thm := BHoms.ring_isomorphisms
def ring_isomorphism : thm := BHoms.ring_isomorphism
def ring_automorphism : thm := BHoms.ring_automorphism
def RING_HOMOMORPHISM_EQ : thm := BHoms.RING_HOMOMORPHISM_EQ
def RING_MONOMORPHISM_EQ : thm := BHoms.RING_MONOMORPHISM_EQ
def RING_EPIMORPHISM_EQ : thm := BHoms.RING_EPIMORPHISM_EQ
def RING_ENDOMORPHISM_EQ : thm := BHoms.RING_ENDOMORPHISM_EQ
def RING_ISOMORPHISMS_EQ : thm := BHoms.RING_ISOMORPHISMS_EQ
def RING_ISOMORPHISM_EQ : thm := BHoms.RING_ISOMORPHISM_EQ
def RING_AUTOMORPHISM_EQ : thm := BHoms.RING_AUTOMORPHISM_EQ
def RING_ISOMORPHISMS_SYM : thm := BHoms.RING_ISOMORPHISMS_SYM
def RING_ISOMORPHISMS_IMP_ISOMORPHISM : thm := BHoms.RING_ISOMORPHISMS_IMP_ISOMORPHISM
def RING_ISOMORPHISMS_IMP_ISOMORPHISM_ALT : thm := BHoms.RING_ISOMORPHISMS_IMP_ISOMORPHISM_ALT
def RING_HOMOMORPHISM : thm := BHoms.RING_HOMOMORPHISM
def RING_ISOMORPHISMS : thm := BHoms.RING_ISOMORPHISMS
def RING_HOMOMORPHISM_IN_CARRIER : thm := BHoms.RING_HOMOMORPHISM_IN_CARRIER
def RING_HOMOMORPHISM_0 : thm := BHoms.RING_HOMOMORPHISM_0
def RING_HOMOMORPHISM_1 : thm := BHoms.RING_HOMOMORPHISM_1
def RING_HOMOMORPHISM_NEG : thm := BHoms.RING_HOMOMORPHISM_NEG
def RING_HOMOMORPHISM_ADD : thm := BHoms.RING_HOMOMORPHISM_ADD
def RING_HOMOMORPHISM_MUL : thm := BHoms.RING_HOMOMORPHISM_MUL
def RING_HOMOMORPHISM_SUB : thm := BHoms.RING_HOMOMORPHISM_SUB
def RING_HOMOMORPHISM_POW : thm := BHoms.RING_HOMOMORPHISM_POW
def RING_HOMOMORPHISM_INV : thm := BHoms.RING_HOMOMORPHISM_INV
def RING_HOMOMORPHISM_MUL_INV : thm := BHoms.RING_HOMOMORPHISM_MUL_INV
def FIELD_HOMOMORPHISM_INV : thm := BHoms.FIELD_HOMOMORPHISM_INV
def FIELD_HOMOMORPHISM_DIV : thm := BHoms.FIELD_HOMOMORPHISM_DIV
def RING_HOMOMORPHISM_RING_OF_NUM : thm := BHoms.RING_HOMOMORPHISM_RING_OF_NUM
def RING_HOMOMORPHISM_RING_OF_INT : thm := BHoms.RING_HOMOMORPHISM_RING_OF_INT
def RING_HOMOMORPHISM_PUSH_CONV : thm → HolCore.Equal.ioconv := BHoms.RING_HOMOMORPHISM_PUSH_CONV
def RING_CHAR_HOMOMORPHIC_IMAGE : thm := BHoms.RING_CHAR_HOMOMORPHIC_IMAGE
def RING_HOMOMORPHISM_SUM : thm := BHoms.RING_HOMOMORPHISM_SUM
def RING_HOMOMORPHISM_SUM_MUL : thm := BHoms.RING_HOMOMORPHISM_SUM_MUL
def RING_HOMOMORPHISM_PRODUCT : thm := BHoms.RING_HOMOMORPHISM_PRODUCT
def RING_HOMOMORPHISM_PRODUCT_POW : thm := BHoms.RING_HOMOMORPHISM_PRODUCT_POW
def RING_MONOMORPHISM_SUM : thm := BHoms.RING_MONOMORPHISM_SUM
def RING_MONOMORPHISM_PRODUCT : thm := BHoms.RING_MONOMORPHISM_PRODUCT
def RING_MONOMORPHISM_SUM_GEN : thm := BHoms.RING_MONOMORPHISM_SUM_GEN
def RING_MONOMORPHISM_PRODUCT_GEN : thm := BHoms.RING_MONOMORPHISM_PRODUCT_GEN
def RING_HOMOMORPHISMS_EQ_FROM_SUBRING_GENERATED : thm := BHoms.RING_HOMOMORPHISMS_EQ_FROM_SUBRING_GENERATED
def RING_MONOMORPHISM_IMP_HOMOMORPHISM : thm := BHoms.RING_MONOMORPHISM_IMP_HOMOMORPHISM
def RING_EPIMORPHISM_IMP_HOMOMORPHISM : thm := BHoms.RING_EPIMORPHISM_IMP_HOMOMORPHISM
def RING_MONOMORPHISM_INJECTIVE_EQ : thm := BHoms.RING_MONOMORPHISM_INJECTIVE_EQ
def RING_MONOMORPHISM_EQ_0 : thm := BHoms.RING_MONOMORPHISM_EQ_0
def RING_HOMOMORPHISM_ID : thm := BHoms.RING_HOMOMORPHISM_ID
def RING_HOMOMORPHISM_I : thm := BHoms.RING_HOMOMORPHISM_I
def RING_MONOMORPHISM_ID : thm := BHoms.RING_MONOMORPHISM_ID
def RING_MONOMORPHISM_I : thm := BHoms.RING_MONOMORPHISM_I
def RING_EPIMORPHISM_ID : thm := BHoms.RING_EPIMORPHISM_ID
def RING_EPIMORPHISM_I : thm := BHoms.RING_EPIMORPHISM_I
def RING_ISOMORPHISMS_ID : thm := BHoms.RING_ISOMORPHISMS_ID
def RING_ISOMORPHISMS_I : thm := BHoms.RING_ISOMORPHISMS_I
def RING_ISOMORPHISM_ID : thm := BHoms.RING_ISOMORPHISM_ID
def RING_ISOMORPHISM_I : thm := BHoms.RING_ISOMORPHISM_I
def RING_AUTOMORPHISM_ID : thm := BHoms.RING_AUTOMORPHISM_ID
def RING_AUTOMORPHISM_I : thm := BHoms.RING_AUTOMORPHISM_I
def RING_HOMOMORPHISM_COMPOSE : thm := BHoms.RING_HOMOMORPHISM_COMPOSE
def RING_MONOMORPHISM_COMPOSE : thm := BHoms.RING_MONOMORPHISM_COMPOSE
def RING_MONOMORPHISM_COMPOSE_REV : thm := BHoms.RING_MONOMORPHISM_COMPOSE_REV
def RING_EPIMORPHISM_COMPOSE : thm := BHoms.RING_EPIMORPHISM_COMPOSE
def RING_EPIMORPHISM_COMPOSE_REV : thm := BHoms.RING_EPIMORPHISM_COMPOSE_REV
def RING_MONOMORPHISM_LEFT_INVERTIBLE : thm := BHoms.RING_MONOMORPHISM_LEFT_INVERTIBLE
def RING_EPIMORPHISM_RIGHT_INVERTIBLE : thm := BHoms.RING_EPIMORPHISM_RIGHT_INVERTIBLE
def RING_HOMOMORPHISM_INTO_SUBRING : thm := BHoms.RING_HOMOMORPHISM_INTO_SUBRING
def RING_HOMOMORPHISM_INTO_SUBRING_EQ_GEN : thm := BHoms.RING_HOMOMORPHISM_INTO_SUBRING_EQ_GEN
def RING_HOMOMORPHISM_INTO_SUBRING_EQ : thm := BHoms.RING_HOMOMORPHISM_INTO_SUBRING_EQ
def RING_HOMOMORPHISM_FROM_SUBRING_GENERATED : thm := BHoms.RING_HOMOMORPHISM_FROM_SUBRING_GENERATED
def RING_MONOMORPHISM_FROM_SUBRING_GENERATED : thm := BHoms.RING_MONOMORPHISM_FROM_SUBRING_GENERATED
def RING_HOMOMORPHISM_INCLUSION : thm := BHoms.RING_HOMOMORPHISM_INCLUSION
def RING_MONOMORPHISM_INCLUSION : thm := BHoms.RING_MONOMORPHISM_INCLUSION
def RING_HOMOMORPHISM_BETWEEN_SUBRINGS : thm := BHoms.RING_HOMOMORPHISM_BETWEEN_SUBRINGS
def RING_HOMOMORPHISM_BETWEEN_SUBRINGS_ALT : thm := BHoms.RING_HOMOMORPHISM_BETWEEN_SUBRINGS_ALT
def RING_MONOMORPHISM_INTO_SUBRING : thm := BHoms.RING_MONOMORPHISM_INTO_SUBRING
def RING_MONOMORPHISM_BETWEEN_SUBRINGS : thm := BHoms.RING_MONOMORPHISM_BETWEEN_SUBRINGS
def RING_MONOMORPHISM_INTO_SUPERRING : thm := BHoms.RING_MONOMORPHISM_INTO_SUPERRING
def RING_SUM_SUBRING_GENERATED_GEN : thm := BHoms.RING_SUM_SUBRING_GENERATED_GEN
def RING_SUM_SUBRING_GENERATED : thm := BHoms.RING_SUM_SUBRING_GENERATED
def RING_PRODUCT_SUBRING_GENERATED_GEN : thm := BHoms.RING_PRODUCT_SUBRING_GENERATED_GEN
def RING_PRODUCT_SUBRING_GENERATED : thm := BHoms.RING_PRODUCT_SUBRING_GENERATED
def SUBRING_GENERATED_BY_HOMOMORPHIC_IMAGE : thm := BHoms.SUBRING_GENERATED_BY_HOMOMORPHIC_IMAGE
def RING_EPIMORPHISM_BETWEEN_SUBRINGS : thm := BHoms.RING_EPIMORPHISM_BETWEEN_SUBRINGS
def RING_ISOMORPHISM : thm := BHoms.RING_ISOMORPHISM
def RING_ISOMORPHISM_SUBSET : thm := BHoms.RING_ISOMORPHISM_SUBSET
def SUBRING_OF_HOMOMORPHIC_IMAGE : thm := BHoms.SUBRING_OF_HOMOMORPHIC_IMAGE
def RING_IDEAL_EPIMORPHIC_IMAGE : thm := BHoms.RING_IDEAL_EPIMORPHIC_IMAGE
def SUBRING_OF_HOMOMORPHIC_PREIMAGE : thm := BHoms.SUBRING_OF_HOMOMORPHIC_PREIMAGE
def RING_HOMOMORPHISM_SUBRING_GENERATED_SUBSET : thm := BHoms.RING_HOMOMORPHISM_SUBRING_GENERATED_SUBSET
def SUBRING_OF_EPIMORPHIC_PREIMAGE : thm := BHoms.SUBRING_OF_EPIMORPHIC_PREIMAGE
def SUBRING_OF_HOMOMORPHIC_EQUALITIES : thm := BHoms.SUBRING_OF_HOMOMORPHIC_EQUALITIES
def SUBRING_OF_FIXPOINTS : thm := BHoms.SUBRING_OF_FIXPOINTS
def RING_IDEAL_HOMOMORPHIC_PREIMAGE : thm := BHoms.RING_IDEAL_HOMOMORPHIC_PREIMAGE
def IDEAL_GENERATED_BY_HOMOMORPHIC_IMAGE : thm := BHoms.IDEAL_GENERATED_BY_HOMOMORPHIC_IMAGE
def IDEAL_GENERATED_BY_EPIMORPHIC_IMAGE : thm := BHoms.IDEAL_GENERATED_BY_EPIMORPHIC_IMAGE
def RING_MONOMORPHISM_EPIMORPHISM : thm := BHoms.RING_MONOMORPHISM_EPIMORPHISM
def SUBRING_MONOMORPHISM_EPIMORPHISM : thm := BHoms.SUBRING_MONOMORPHISM_EPIMORPHISM
def RING_ISOMORPHISM_EPIMORPHISM : thm := BHoms.RING_ISOMORPHISM_EPIMORPHISM
def RING_ISOMORPHISM_MONOMORPHISM : thm := BHoms.RING_ISOMORPHISM_MONOMORPHISM
def RING_ISOMORPHISM_MONOMORPHISM_ALT : thm := BHoms.RING_ISOMORPHISM_MONOMORPHISM_ALT
def RING_ISOMORPHISM_IMP_MONOMORPHISM : thm := BHoms.RING_ISOMORPHISM_IMP_MONOMORPHISM
def RING_ISOMORPHISM_IMP_EPIMORPHISM : thm := BHoms.RING_ISOMORPHISM_IMP_EPIMORPHISM
def RING_ISOMORPHISM_IMP_HOMOMORPHISM : thm := BHoms.RING_ISOMORPHISM_IMP_HOMOMORPHISM
def RING_AUTOMORPHISM_IMP_ENDOMORPHISM : thm := BHoms.RING_AUTOMORPHISM_IMP_ENDOMORPHISM
def RING_ISOMORPHISMS_ISOMORPHISM : thm := BHoms.RING_ISOMORPHISMS_ISOMORPHISM
def RING_ISOMORPHISM_EQ_MONOMORPHISM_FINITE : thm := BHoms.RING_ISOMORPHISM_EQ_MONOMORPHISM_FINITE
def RING_ISOMORPHISM_EQ_EPIMORPHISM_FINITE : thm := BHoms.RING_ISOMORPHISM_EQ_EPIMORPHISM_FINITE
def RING_ISOMORPHISMS_BETWEEN_SUBRINGS : thm := BHoms.RING_ISOMORPHISMS_BETWEEN_SUBRINGS
def RING_ISOMORPHISMS_BETWEEN_SUBRINGS_ALT : thm := BHoms.RING_ISOMORPHISMS_BETWEEN_SUBRINGS_ALT
def RING_ISOMORPHISM_BETWEEN_SUBRINGS : thm := BHoms.RING_ISOMORPHISM_BETWEEN_SUBRINGS
def RING_ISOMORPHISMS_COMPOSE : thm := BHoms.RING_ISOMORPHISMS_COMPOSE
def RING_ISOMORPHISM_COMPOSE : thm := BHoms.RING_ISOMORPHISM_COMPOSE
def RING_AUTOMORPHISM_COMPOSE : thm := BHoms.RING_AUTOMORPHISM_COMPOSE
def RING_ISOMORPHISM_COMPOSE_REV : thm := BHoms.RING_ISOMORPHISM_COMPOSE_REV
def RING_EPIMORPHISM_ISOMORPHISM_COMPOSE_REV : thm := BHoms.RING_EPIMORPHISM_ISOMORPHISM_COMPOSE_REV
def RING_MONOMORPHISM_ISOMORPHISM_COMPOSE_REV : thm := BHoms.RING_MONOMORPHISM_ISOMORPHISM_COMPOSE_REV
def RING_ISOMORPHISM_INVERSE : thm := BHoms.RING_ISOMORPHISM_INVERSE
def RING_HOMOMORPHISM_FROM_TRIVIAL_RING : thm := BHoms.RING_HOMOMORPHISM_FROM_TRIVIAL_RING
def RING_MONOMORPHISM_FROM_TRIVIAL_RING : thm := BHoms.RING_MONOMORPHISM_FROM_TRIVIAL_RING
def RING_MONOMORPHISM_TO_TRIVIAL_RING : thm := BHoms.RING_MONOMORPHISM_TO_TRIVIAL_RING
def RING_EPIMORPHISM_FROM_TRIVIAL_RING : thm := BHoms.RING_EPIMORPHISM_FROM_TRIVIAL_RING
def RING_EPIMORPHISM_TO_TRIVIAL_RING : thm := BHoms.RING_EPIMORPHISM_TO_TRIVIAL_RING
def TRIVIAL_RING_MONOMORPHIC_PREIMAGE : thm := BHoms.TRIVIAL_RING_MONOMORPHIC_PREIMAGE
def TRIVIAL_RING_HOMOMORPHIC_IMAGE : thm := BHoms.TRIVIAL_RING_HOMOMORPHIC_IMAGE
def TRIVIAL_RING_MONOMORPHIC_IMAGE_EQ : thm := BHoms.TRIVIAL_RING_MONOMORPHIC_IMAGE_EQ
def RING_NILPOTENT_HOMOMORPHIC_IMAGE : thm := BHoms.RING_NILPOTENT_HOMOMORPHIC_IMAGE
def RING_NILPOTENT_MONOMORPHIC_IMAGE_EQ : thm := BHoms.RING_NILPOTENT_MONOMORPHIC_IMAGE_EQ
def RING_CHAR_MONOMORPHIC_IMAGE : thm := BHoms.RING_CHAR_MONOMORPHIC_IMAGE

-- Iso
def isomorphic_ring : thm := BIso.isomorphic_ring
def RING_ISOMORPHISM_IMP_ISOMORPHIC : thm := BIso.RING_ISOMORPHISM_IMP_ISOMORPHIC
def ISOMORPHIC_RING_REFL : thm := BIso.ISOMORPHIC_RING_REFL
def ISOMORPHIC_RING_EQ : thm := BIso.ISOMORPHIC_RING_EQ
def ISOMORPHIC_RING_SYM : thm := BIso.ISOMORPHIC_RING_SYM
def ISOMORPHIC_RING_TRANS : thm := BIso.ISOMORPHIC_RING_TRANS
def ISOMORPHIC_RING_TRIVIALITY : thm := BIso.ISOMORPHIC_RING_TRIVIALITY
def ISOMORPHIC_TO_TRIVIAL_RING : thm := BIso.ISOMORPHIC_TO_TRIVIAL_RING
def ISOMORPHIC_TRIVIAL_RINGS : thm := BIso.ISOMORPHIC_TRIVIAL_RINGS
def ISOMORPHIC_RING_SINGLETON_RING : thm := BIso.ISOMORPHIC_RING_SINGLETON_RING
def CARD_LE_RING_MONOMORPHIC_IMAGE : thm := BIso.CARD_LE_RING_MONOMORPHIC_IMAGE
def CARD_LE_RING_EPIMORPHIC_IMAGE : thm := BIso.CARD_LE_RING_EPIMORPHIC_IMAGE
def CARD_EQ_RING_ISOMORPHIC_IMAGE : thm := BIso.CARD_EQ_RING_ISOMORPHIC_IMAGE
def ISOMORPHIC_RING_CARD_EQ : thm := BIso.ISOMORPHIC_RING_CARD_EQ
def ISOMORPHIC_RING_FINITENESS : thm := BIso.ISOMORPHIC_RING_FINITENESS
def ISOMORPHIC_RING_INFINITENESS : thm := BIso.ISOMORPHIC_RING_INFINITENESS
def FINITE_RING_MONOMORPHIC_PREIMAGE : thm := BIso.FINITE_RING_MONOMORPHIC_PREIMAGE
def FINITE_RING_EPIMORPHIC_IMAGE : thm := BIso.FINITE_RING_EPIMORPHIC_IMAGE
def CARD_EQ_RING_MONOMORPHIC_IMAGE : thm := BIso.CARD_EQ_RING_MONOMORPHIC_IMAGE
def ISOMORPHIC_RING_SIZE : thm := BIso.ISOMORPHIC_RING_SIZE
def ISOMORPHIC_RING_CARD : thm := BIso.ISOMORPHIC_RING_CARD
def ISOMORPHIC_RING_CHAR : thm := BIso.ISOMORPHIC_RING_CHAR
def ISOMORPHIC_TRANSPORT_OF_RING : thm := BIso.ISOMORPHIC_TRANSPORT_OF_RING
def ISOMORPHIC_COPY_OF_RING : thm := BIso.ISOMORPHIC_COPY_OF_RING
def ISOMORPHIC_SUBCOPY_OF_RING : thm := BIso.ISOMORPHIC_SUBCOPY_OF_RING

-- Kernels
def ring_kernel : thm := BKernels.ring_kernel
def ring_image : thm := BKernels.ring_image
def RING_KERNEL_0 : thm := BKernels.RING_KERNEL_0
def RING_KERNEL_NONEMPTY : thm := BKernels.RING_KERNEL_NONEMPTY
def RING_KERNEL_SUBSET_CARRIER : thm := BKernels.RING_KERNEL_SUBSET_CARRIER
def IN_RING_KERNEL_SUB : thm := BKernels.IN_RING_KERNEL_SUB
def RING_MONOMORPHISM : thm := BKernels.RING_MONOMORPHISM
def RING_MONOMORPHISM_ALT : thm := BKernels.RING_MONOMORPHISM_ALT
def RING_MONOMORPHISM_ALT_EQ : thm := BKernels.RING_MONOMORPHISM_ALT_EQ
def RING_EPIMORPHISM : thm := BKernels.RING_EPIMORPHISM
def RING_EPIMORPHISM_ALT : thm := BKernels.RING_EPIMORPHISM_ALT
def RING_ISOMORPHISM_RING_KERNEL_RING_IMAGE : thm := BKernels.RING_ISOMORPHISM_RING_KERNEL_RING_IMAGE
def RING_ISOMORPHISM_ALT : thm := BKernels.RING_ISOMORPHISM_ALT
def CARD_EQ_RING_IMAGE_KERNEL : thm := BKernels.CARD_EQ_RING_IMAGE_KERNEL
def RING_IDEAL_RING_KERNEL : thm := BKernels.RING_IDEAL_RING_KERNEL
def SUBRING_RING_IMAGE : thm := BKernels.SUBRING_RING_IMAGE
def RING_KERNEL_TO_SUBRING_GENERATED : thm := BKernels.RING_KERNEL_TO_SUBRING_GENERATED
def RING_IMAGE_TO_SUBRING_GENERATED : thm := BKernels.RING_IMAGE_TO_SUBRING_GENERATED
def RING_KERNEL_FROM_SUBRING_GENERATED : thm := BKernels.RING_KERNEL_FROM_SUBRING_GENERATED
def RING_IMAGE_FROM_SUBRING_GENERATED : thm := BKernels.RING_IMAGE_FROM_SUBRING_GENERATED
def RING_ISOMORPHISM_ONTO_IMAGE : thm := BKernels.RING_ISOMORPHISM_ONTO_IMAGE
def SUBRING_IMP_MONOMORPHIC_PROPERTY : thm := BKernels.SUBRING_IMP_MONOMORPHIC_PROPERTY
def RING_KERNEL_FROM_TRIVIAL_RING : thm := BKernels.RING_KERNEL_FROM_TRIVIAL_RING
def RING_IMAGE_FROM_TRIVIAL_RING : thm := BKernels.RING_IMAGE_FROM_TRIVIAL_RING
def RING_KERNEL_TO_TRIVIAL_RING : thm := BKernels.RING_KERNEL_TO_TRIVIAL_RING
def RING_IMAGE_TO_TRIVIAL_RING : thm := BKernels.RING_IMAGE_TO_TRIVIAL_RING
def RING_HOMOMORPHISM_PREIMAGE_IMAGE_GEN : thm := BKernels.RING_HOMOMORPHISM_PREIMAGE_IMAGE_GEN
def RING_HOMOMORPHISM_IMAGE_PREIMAGE : thm := BKernels.RING_HOMOMORPHISM_IMAGE_PREIMAGE
def RING_HOMOMORPHISM_PREIMAGE_IMAGE : thm := BKernels.RING_HOMOMORPHISM_PREIMAGE_IMAGE
def RING_HOMOMORPHISM_IMAGE_PREIMAGE_EQ : thm := BKernels.RING_HOMOMORPHISM_IMAGE_PREIMAGE_EQ
def RING_EPIMORPHISM_IDEAL_CORRESPONDENCE : thm := BKernels.RING_EPIMORPHISM_IDEAL_CORRESPONDENCE
def RING_EPIMORPHISM_PREIMAGE_IDEAL_GENERATED : thm := BKernels.RING_EPIMORPHISM_PREIMAGE_IDEAL_GENERATED
def RING_EPIMORPHISM_SUBRING_CORRESPONDENCE : thm := BKernels.RING_EPIMORPHISM_SUBRING_CORRESPONDENCE
def RING_EPIMORPHISM_IDEAL_CORRESPONDENCE_ALT : thm := BKernels.RING_EPIMORPHISM_IDEAL_CORRESPONDENCE_ALT
def RING_EPIMORPHISM_SUBRING_CORRESPONDENCE_ALT : thm := BKernels.RING_EPIMORPHISM_SUBRING_CORRESPONDENCE_ALT
def RING_IDEAL_ISOMORPHIC_IMAGE_EQ : thm := BKernels.RING_IDEAL_ISOMORPHIC_IMAGE_EQ
def RING_DIVIDES_HOMOMORPHIC_IMAGE : thm := BKernels.RING_DIVIDES_HOMOMORPHIC_IMAGE
def RING_ASSOCIATES_HOMOMORPHIC_IMAGE : thm := BKernels.RING_ASSOCIATES_HOMOMORPHIC_IMAGE
def RING_UNIT_HOMOMORPHIC_IMAGE : thm := BKernels.RING_UNIT_HOMOMORPHIC_IMAGE
def RING_DIVIDES_ISOMORPHIC_IMAGE_EQ : thm := BKernels.RING_DIVIDES_ISOMORPHIC_IMAGE_EQ
def RING_ASSOCIATES_ISOMORPHIC_IMAGE_EQ : thm := BKernels.RING_ASSOCIATES_ISOMORPHIC_IMAGE_EQ
def RING_UNIT_ISOMORPHIC_IMAGE_EQ : thm := BKernels.RING_UNIT_ISOMORPHIC_IMAGE_EQ
def RING_ZERODIVISOR_MONOMORPHIC_IMAGE : thm := BKernels.RING_ZERODIVISOR_MONOMORPHIC_IMAGE
def RING_ZERODIVISOR_ISOMORPHIC_IMAGE_EQ : thm := BKernels.RING_ZERODIVISOR_ISOMORPHIC_IMAGE_EQ
def RING_REGULAR_ISOMORPHIC_IMAGE_EQ : thm := BKernels.RING_REGULAR_ISOMORPHIC_IMAGE_EQ
def ISOMORPHIC_RING_INTEGRAL_DOMAINNESS : thm := BKernels.ISOMORPHIC_RING_INTEGRAL_DOMAINNESS
def INTEGRAL_DOMAIN_MONOMORPHIC_PREIMAGE : thm := BKernels.INTEGRAL_DOMAIN_MONOMORPHIC_PREIMAGE
def FIELD_EPIMORPHIC_IMAGE : thm := BKernels.FIELD_EPIMORPHIC_IMAGE
def ISOMORPHIC_RING_FIELDNESS : thm := BKernels.ISOMORPHIC_RING_FIELDNESS
def RING_HOMOMORPHISM_EPIMORPHISM_FACTOR : thm := BKernels.RING_HOMOMORPHISM_EPIMORPHISM_FACTOR
def RING_HOMOMORPHISM_MONOMORPHISM_FACTOR : thm := BKernels.RING_HOMOMORPHISM_MONOMORPHISM_FACTOR

-- ProdRings
def prod_ring : thm := BProdRings.prod_ring
def PROD_RING : thm := BProdRings.PROD_RING
def RING_HOMOMORPHISM_PAIRWISE : thm := BProdRings.RING_HOMOMORPHISM_PAIRWISE
def RING_HOMOMORPHISM_PAIRED : thm := BProdRings.RING_HOMOMORPHISM_PAIRED
def RING_HOMOMORPHISM_DIAG : thm := BProdRings.RING_HOMOMORPHISM_DIAG
def RING_MONOMORPHISM_DIAG : thm := BProdRings.RING_MONOMORPHISM_DIAG
def RING_HOMOMORPHISM_PAIRED2 : thm := BProdRings.RING_HOMOMORPHISM_PAIRED2
def RING_ISOMORPHISMS_PAIRED2 : thm := BProdRings.RING_ISOMORPHISMS_PAIRED2
def RING_ISOMORPHISM_PAIRED2 : thm := BProdRings.RING_ISOMORPHISM_PAIRED2
def ISOMORPHIC_RING_PROD_RINGS : thm := BProdRings.ISOMORPHIC_RING_PROD_RINGS
def RING_HOMOMORPHISM_OF_FST : thm := BProdRings.RING_HOMOMORPHISM_OF_FST
def RING_HOMOMORPHISM_OF_SND : thm := BProdRings.RING_HOMOMORPHISM_OF_SND
def RING_EPIMORPHISM_OF_FST : thm := BProdRings.RING_EPIMORPHISM_OF_FST
def RING_EPIMORPHISM_OF_SND : thm := BProdRings.RING_EPIMORPHISM_OF_SND
def RING_HOMOMORPHISM_FST : thm := BProdRings.RING_HOMOMORPHISM_FST
def RING_HOMOMORPHISM_SND : thm := BProdRings.RING_HOMOMORPHISM_SND
def RING_SUM_PROD_RING : thm := BProdRings.RING_SUM_PROD_RING
def RING_EPIMORPHISM_FST : thm := BProdRings.RING_EPIMORPHISM_FST
def RING_EPIMORPHISM_SND : thm := BProdRings.RING_EPIMORPHISM_SND
def RING_ISOMORPHISM_FST : thm := BProdRings.RING_ISOMORPHISM_FST
def RING_ISOMORPHISM_SND : thm := BProdRings.RING_ISOMORPHISM_SND
def RING_ISOMORPHISMS_PROD_RING_SWAP : thm := BProdRings.RING_ISOMORPHISMS_PROD_RING_SWAP
def ISOMORPHIC_RING_PROD_RING_SYM : thm := BProdRings.ISOMORPHIC_RING_PROD_RING_SYM
def ISOMORPHIC_RING_PROD_RING_SWAP_LEFT : thm := BProdRings.ISOMORPHIC_RING_PROD_RING_SWAP_LEFT
def ISOMORPHIC_RING_PROD_RING_SWAP_RIGHT : thm := BProdRings.ISOMORPHIC_RING_PROD_RING_SWAP_RIGHT
def ISOMORPHIC_PROD_TRIVIAL_RING : thm := BProdRings.ISOMORPHIC_PROD_TRIVIAL_RING
def TRIVIAL_PROD_RING : thm := BProdRings.TRIVIAL_PROD_RING
def FINITE_PROD_RING : thm := BProdRings.FINITE_PROD_RING
def CROSS_SUBRING_OF_PROD_RING : thm := BProdRings.CROSS_SUBRING_OF_PROD_RING
def SUBRING_OF_PROD_RING_EQUALIZER : thm := BProdRings.SUBRING_OF_PROD_RING_EQUALIZER
def PROD_RING_SUBRING_GENERATED : thm := BProdRings.PROD_RING_SUBRING_GENERATED
def RING_IDEAL_CROSS : thm := BProdRings.RING_IDEAL_CROSS
def RING_IDEAL_PROD_RING : thm := BProdRings.RING_IDEAL_PROD_RING
def IDEAL_GENERATED_PAIRWISE : thm := BProdRings.IDEAL_GENERATED_PAIRWISE
def IDEAL_GENERATED_CROSS : thm := BProdRings.IDEAL_GENERATED_CROSS
def RING_POW_PROD_RING : thm := BProdRings.RING_POW_PROD_RING
def RING_DIVIDES_PROD_RING : thm := BProdRings.RING_DIVIDES_PROD_RING
def RING_OF_NUM_PROD_RING : thm := BProdRings.RING_OF_NUM_PROD_RING
def RING_OF_INT_PROD_RING : thm := BProdRings.RING_OF_INT_PROD_RING
def RING_ASSOCIATES_PROD_RING : thm := BProdRings.RING_ASSOCIATES_PROD_RING
def RING_ZERODIVISOR_PROD_RING : thm := BProdRings.RING_ZERODIVISOR_PROD_RING
def RING_REGULAR_PROD_RING : thm := BProdRings.RING_REGULAR_PROD_RING
def RING_NILPOTENT_PROD_RING : thm := BProdRings.RING_NILPOTENT_PROD_RING
def product_ring : thm := BProdRings.product_ring
def PRODUCT_RING : thm := BProdRings.PRODUCT_RING
def TRIVIAL_PRODUCT_RING : thm := BProdRings.TRIVIAL_PRODUCT_RING
def ISOMORPHIC_RING_PRODUCT_RING : thm := BProdRings.ISOMORPHIC_RING_PRODUCT_RING
def RING_HOMOMORPHISM_COMPONENTWISE : thm := BProdRings.RING_HOMOMORPHISM_COMPONENTWISE
def RING_HOMOMORPHISM_COMPONENTWISE_UNIV : thm := BProdRings.RING_HOMOMORPHISM_COMPONENTWISE_UNIV
def RING_PRODUCT_INJECTION : thm := BProdRings.RING_PRODUCT_INJECTION
def RING_HOMOMORPHISM_DIAGONAL : thm := BProdRings.RING_HOMOMORPHISM_DIAGONAL
def RING_HOMOMORPHISM_DIAGONAL_UNIV : thm := BProdRings.RING_HOMOMORPHISM_DIAGONAL_UNIV
def RING_MONOMORPHISM_DIAGONAL : thm := BProdRings.RING_MONOMORPHISM_DIAGONAL
def RING_MONOMORPHISM_DIAGONAL_UNIV : thm := BProdRings.RING_MONOMORPHISM_DIAGONAL_UNIV
def RING_HOMOMORPHISM_PRODUCT_PROJECTION : thm := BProdRings.RING_HOMOMORPHISM_PRODUCT_PROJECTION
def RING_EPIMORPHISM_PRODUCT_PROJECTION : thm := BProdRings.RING_EPIMORPHISM_PRODUCT_PROJECTION
def RING_ISOMORPHISM_PRODUCT_PROJECTION : thm := BProdRings.RING_ISOMORPHISM_PRODUCT_PROJECTION
def CARTESIAN_PRODUCT_SUBRING_OF_PRODUCT_RING : thm := BProdRings.CARTESIAN_PRODUCT_SUBRING_OF_PRODUCT_RING
def SUBRING_OF_PRODUCT_RING_EQUALIZER : thm := BProdRings.SUBRING_OF_PRODUCT_RING_EQUALIZER
def PRODUCT_RING_SUBRING_GENERATED : thm := BProdRings.PRODUCT_RING_SUBRING_GENERATED
def FINITE_PRODUCT_RING : thm := BProdRings.FINITE_PRODUCT_RING
def RING_IDEAL_CARTESIAN_PRODUCT : thm := BProdRings.RING_IDEAL_CARTESIAN_PRODUCT
def RING_SUM_PRODUCT_RING : thm := BProdRings.RING_SUM_PRODUCT_RING
def RING_IDEAL_PRODUCT_RING : thm := BProdRings.RING_IDEAL_PRODUCT_RING
def IDEAL_GENERATED_COMPONENTWISE : thm := BProdRings.IDEAL_GENERATED_COMPONENTWISE
def IDEAL_GENERATED_CARTESIAN_PRODUCT : thm := BProdRings.IDEAL_GENERATED_CARTESIAN_PRODUCT
def RING_POW_PRODUCT_RING : thm := BProdRings.RING_POW_PRODUCT_RING
def RING_DIVIDES_PRODUCT_RING : thm := BProdRings.RING_DIVIDES_PRODUCT_RING
def RING_UNIT_PRODUCT_RING : thm := BProdRings.RING_UNIT_PRODUCT_RING
def RING_INV_PRODUCT_RING : thm := BProdRings.RING_INV_PRODUCT_RING
def RING_ASSOCIATES_PRODUCT_RING : thm := BProdRings.RING_ASSOCIATES_PRODUCT_RING
def RING_ZERODIVISOR_PRODUCT_RING : thm := BProdRings.RING_ZERODIVISOR_PRODUCT_RING
def RING_REGULAR_PRODUCT_RING : thm := BProdRings.RING_REGULAR_PRODUCT_RING
def RING_NILPOTENT_PRODUCT_RING_GEN : thm := BProdRings.RING_NILPOTENT_PRODUCT_RING_GEN
def RING_NILPOTENT_PRODUCT_RING : thm := BProdRings.RING_NILPOTENT_PRODUCT_RING
def ISOMORPHIC_PRODUCT_RING_DISJOINT_UNION : thm := BProdRings.ISOMORPHIC_PRODUCT_RING_DISJOINT_UNION
def ISOMORPHIC_PRODUCT_RING_SING : thm := BProdRings.ISOMORPHIC_PRODUCT_RING_SING
def ISOMORPHIC_PRODUCT_RING_SUPPORT : thm := BProdRings.ISOMORPHIC_PRODUCT_RING_SUPPORT
def ISOMORPHIC_PRODUCT_RING_SYMDIFF : thm := BProdRings.ISOMORPHIC_PRODUCT_RING_SYMDIFF
def ISOMORPHIC_PRODUCT_RING_BIJECTIONS : thm := BProdRings.ISOMORPHIC_PRODUCT_RING_BIJECTIONS
def RING_ISOMORPHISMS_PRODUCT_RING_DISJOINT_UNION : thm := BProdRings.RING_ISOMORPHISMS_PRODUCT_RING_DISJOINT_UNION
def RING_ISOMORPHISM_PRODUCT_RING_DISJOINT_UNION : thm := BProdRings.RING_ISOMORPHISM_PRODUCT_RING_DISJOINT_UNION
def ISOMORPHIC_PRODUCT_RING_INSERT : thm := BProdRings.ISOMORPHIC_PRODUCT_RING_INSERT
def restricted_product_ring : thm := BProdRings.restricted_product_ring
def RESTRICTED_PRODUCT_RING_ALT : thm := BProdRings.RESTRICTED_PRODUCT_RING_ALT
def SUBRING_RESTRICTED_PRODUCT_RING : thm := BProdRings.SUBRING_RESTRICTED_PRODUCT_RING
def RESTRICTED_PRODUCT_RING : thm := BProdRings.RESTRICTED_PRODUCT_RING
def RESTRICTED_PRODUCT_RING_UNIONS : thm := BProdRings.RESTRICTED_PRODUCT_RING_UNIONS
def RESTRICTED_PRODUCT_RING_EQ_PRODUCT_RING : thm := BProdRings.RESTRICTED_PRODUCT_RING_EQ_PRODUCT_RING
def RESTRICTED_PRODUCT_RING_EQ : thm := BProdRings.RESTRICTED_PRODUCT_RING_EQ
def RESTRICTED_PRODUCT_RING_MONO : thm := BProdRings.RESTRICTED_PRODUCT_RING_MONO
def CARTESIAN_PRODUCT_SUBRING_OF_RESTRICTED_PRODUCT_RING : thm := BProdRings.CARTESIAN_PRODUCT_SUBRING_OF_RESTRICTED_PRODUCT_RING
def RING_HOMOMORPHISM_RESTRICTED_PRODUCT_PROJECTION : thm := BProdRings.RING_HOMOMORPHISM_RESTRICTED_PRODUCT_PROJECTION
def RING_HOMOMORPHISM_RESTRICTED_PRODUCT : thm := BProdRings.RING_HOMOMORPHISM_RESTRICTED_PRODUCT
def RING_HOMOMORPHISM_RESTRICTED_PRODUCT_COMPONENTWISE : thm := BProdRings.RING_HOMOMORPHISM_RESTRICTED_PRODUCT_COMPONENTWISE
def RING_UNIT_RESTRICTED_PRODUCT_RING : thm := BProdRings.RING_UNIT_RESTRICTED_PRODUCT_RING
def RING_INV_RESTRICTED_PRODUCT_RING : thm := BProdRings.RING_INV_RESTRICTED_PRODUCT_RING

-- Limits
def RING_DIRECT_LIMIT : thm := BLimits.RING_DIRECT_LIMIT
def RING_MONOMORPHIC_IMAGE_RULE := BLimits.RING_MONOMORPHIC_IMAGE_RULE

-- RingRule
def RING_RULE : term → IO (Except String thm) := fun t => (BRingRule.RING_RULE t).run
def RING_TAC : HolCore.Tactics.tactic := fun g => BRingRule.RING_TAC g
def RING_MUL_EQ_UNITS_CANCEL : thm := BRingRule.RING_MUL_EQ_UNITS_CANCEL

-- Cosets
def ring_coset : thm := BCosets.ring_coset
def RING_COSET_SETADD : thm := BCosets.RING_COSET_SETADD
def RING_COSET : thm := BCosets.RING_COSET
def RING_COSET_0 : thm := BCosets.RING_COSET_0
def RING_COSET_TRIVIAL : thm := BCosets.RING_COSET_TRIVIAL
def RING_COSET_CARRIER : thm := BCosets.RING_COSET_CARRIER
def RING_COSET_EQ : thm := BCosets.RING_COSET_EQ
def RING_COSET_MONO : thm := BCosets.RING_COSET_MONO
def RING_COSET_SUBSET_RING_COSET : thm := BCosets.RING_COSET_SUBSET_RING_COSET
def RING_COSET_EQ_IDEAL : thm := BCosets.RING_COSET_EQ_IDEAL
def RING_COSET_EQ_EMPTY : thm := BCosets.RING_COSET_EQ_EMPTY
def RING_COSET_NONEMPTY : thm := BCosets.RING_COSET_NONEMPTY
def IN_RING_COSET_SELF : thm := BCosets.IN_RING_COSET_SELF
def UNIONS_RING_COSETS : thm := BCosets.UNIONS_RING_COSETS
def RING_COSETS_EQ : thm := BCosets.RING_COSETS_EQ
def IN_RING_COSET : thm := BCosets.IN_RING_COSET
def RING_COSET_CHOICE : thm := BCosets.RING_COSET_CHOICE
def RING_COSET_RELATIONAL : thm := BCosets.RING_COSET_RELATIONAL
def RING_IDEAL_ADD_IN_EQ : thm := BCosets.RING_IDEAL_ADD_IN_EQ
def RING_IDEAL_SUB_TRANS : thm := BCosets.RING_IDEAL_SUB_TRANS
def IN_RING_IDEAL_SUB_ADD : thm := BCosets.IN_RING_IDEAL_SUB_ADD
def IN_RING_IDEAL_SUB_MUL : thm := BCosets.IN_RING_IDEAL_SUB_MUL
def DISJOINT_RING_COSETS : thm := BCosets.DISJOINT_RING_COSETS
def PAIRWISE_DISJOINT_RING_COSETS : thm := BCosets.PAIRWISE_DISJOINT_RING_COSETS
def IMAGE_RING_COSET_SWITCH : thm := BCosets.IMAGE_RING_COSET_SWITCH
def CARD_EQ_RING_COSETS : thm := BCosets.CARD_EQ_RING_COSETS
def CARD_EQ_RING_COSET_IDEAL : thm := BCosets.CARD_EQ_RING_COSET_IDEAL
def LAGRANGE_THEOREM_RING_EXPLICIT : thm := BCosets.LAGRANGE_THEOREM_RING_EXPLICIT
def LAGRANGE_THEOREM_RING : thm := BCosets.LAGRANGE_THEOREM_RING
def PRIME_SUBRING_FINITE : thm := BCosets.PRIME_SUBRING_FINITE
def HAS_SIZE_PRIME_SUBRING : thm := BCosets.HAS_SIZE_PRIME_SUBRING
def CARD_PRIME_SUBRING : thm := BCosets.CARD_PRIME_SUBRING
def FINITE_PRIME_SUBRING : thm := BCosets.FINITE_PRIME_SUBRING
def RING_CHAR_DIVIDES_ORDER : thm := BCosets.RING_CHAR_DIVIDES_ORDER
def CARD_DIVIDES_RING_MONOMORPHIC_IMAGE : thm := BCosets.CARD_DIVIDES_RING_MONOMORPHIC_IMAGE
def CARD_DIVIDES_RING_EPIMORPHIC_IMAGE : thm := BCosets.CARD_DIVIDES_RING_EPIMORPHIC_IMAGE
def CARD_RING_COSETS_DIVIDES : thm := BCosets.CARD_RING_COSETS_DIVIDES
def RING_SETADD_PROD_RING : thm := BCosets.RING_SETADD_PROD_RING
def RING_COSET_PROD_RING : thm := BCosets.RING_COSET_PROD_RING
def RING_SETADD_PRODUCT_RING : thm := BCosets.RING_SETADD_PRODUCT_RING
def RING_COSET_PRODUCT_RING : thm := BCosets.RING_COSET_PRODUCT_RING
def RING_SETNEG_SUBRING_GENERATED : thm := BCosets.RING_SETNEG_SUBRING_GENERATED
def RING_SETADD_SUBRING_GENERATED : thm := BCosets.RING_SETADD_SUBRING_GENERATED
def RING_SETNEG_COSET : thm := BCosets.RING_SETNEG_COSET
def RING_SETADD_COSETS : thm := BCosets.RING_SETADD_COSETS
def RING_SETMUL_COSETS : thm := BCosets.RING_SETMUL_COSETS
def RING_COSET_IDEAL_GENERATED_SING : thm := BCosets.RING_COSET_IDEAL_GENERATED_SING
def RING_COSET_IDEAL_GENERATED_SING_EQ : thm := BCosets.RING_COSET_IDEAL_GENERATED_SING_EQ

-- Quotients
def quotient_ring : thm := BQuotients.quotient_ring
def RING_HOMOMORPHISM_RING_COSET : thm := BQuotients.RING_HOMOMORPHISM_RING_COSET
def QUOTIENT_RING : thm := BQuotients.QUOTIENT_RING
def RING_COSET_SETOPS : thm := BQuotients.RING_COSET_SETOPS
def RING_EPIMORPHISM_RING_COSET : thm := BQuotients.RING_EPIMORPHISM_RING_COSET
def QUOTIENT_RING_PREIMAGE_IDEAL_GENERATED : thm := BQuotients.QUOTIENT_RING_PREIMAGE_IDEAL_GENERATED
def QUOTIENT_RING_CARRIER : thm := BQuotients.QUOTIENT_RING_CARRIER
def FINITE_IDEALS_SUPERSET : thm := BQuotients.FINITE_IDEALS_SUPERSET
def RING_MONOMORPHISM_QUOTIENT_CONTRACTION : thm := BQuotients.RING_MONOMORPHISM_QUOTIENT_CONTRACTION
def QUOTIENT_RING_0 : thm := BQuotients.QUOTIENT_RING_0
def QUOTIENT_RING_1 : thm := BQuotients.QUOTIENT_RING_1
def QUOTIENT_RING_NEG : thm := BQuotients.QUOTIENT_RING_NEG
def QUOTIENT_RING_ADD : thm := BQuotients.QUOTIENT_RING_ADD
def QUOTIENT_RING_MUL : thm := BQuotients.QUOTIENT_RING_MUL
def RING_KERNEL_RING_COSET : thm := BQuotients.RING_KERNEL_RING_COSET
def CARD_LE_QUOTIENT_RING : thm := BQuotients.CARD_LE_QUOTIENT_RING
def CARD_QUOTIENT_RING_DIVIDES : thm := BQuotients.CARD_QUOTIENT_RING_DIVIDES
def QUOTIENT_RING_UNIVERSAL_EXPLICIT : thm := BQuotients.QUOTIENT_RING_UNIVERSAL_EXPLICIT
def QUOTIENT_RING_UNIVERSAL : thm := BQuotients.QUOTIENT_RING_UNIVERSAL
def QUOTIENT_RING_HOMOMORPHISM_EXISTS : thm := BQuotients.QUOTIENT_RING_HOMOMORPHISM_EXISTS
def QUOTIENT_RING_UNIVERSAL_EPIMORPHISM : thm := BQuotients.QUOTIENT_RING_UNIVERSAL_EPIMORPHISM
def FIRST_RING_ISOMORPHISM_THEOREM : thm := BQuotients.FIRST_RING_ISOMORPHISM_THEOREM
def QUOTIENT_RING_ZERO_ISOMORPHIC : thm := BQuotients.QUOTIENT_RING_ZERO_ISOMORPHIC
def FIRST_RING_EPIMORPHISM_THEOREM : thm := BQuotients.FIRST_RING_EPIMORPHISM_THEOREM
def SECOND_RING_ISOMORPHISM_THEOREM : thm := BQuotients.SECOND_RING_ISOMORPHISM_THEOREM
def THIRD_RING_ISOMORPHISM_THEOREM : thm := BQuotients.THIRD_RING_ISOMORPHISM_THEOREM
def QUOTIENT_RING_SUBRING_CORRESPONDENCE : thm := BQuotients.QUOTIENT_RING_SUBRING_CORRESPONDENCE
def QUOTIENT_RING_IDEAL_CORRESPONDENCE : thm := BQuotients.QUOTIENT_RING_IDEAL_CORRESPONDENCE
def FIRST_RING_ISOMORPHISM_THEOREM_GEN : thm := BQuotients.FIRST_RING_ISOMORPHISM_THEOREM_GEN
def FIRST_RING_ISOMORPHISM_THEOREM_GEN_ALT : thm := BQuotients.FIRST_RING_ISOMORPHISM_THEOREM_GEN_ALT
def RING_ISOMORPHISM_QUOTIENT_RING_IMAGE : thm := BQuotients.RING_ISOMORPHISM_QUOTIENT_RING_IMAGE

-- Primes
def ring_prime : thm := BPrimes.ring_prime
def ring_irreducible : thm := BPrimes.ring_irreducible
def RING_PRIME_IN_CARRIER : thm := BPrimes.RING_PRIME_IN_CARRIER
def RING_IRREDUCIBLE_IN_CARRIER : thm := BPrimes.RING_IRREDUCIBLE_IN_CARRIER
def RING_PRIME_NEG : thm := BPrimes.RING_PRIME_NEG
def RING_IRREDUCIBLE_NEG : thm := BPrimes.RING_IRREDUCIBLE_NEG
def RING_PRIME_IMP_NONTRIVIAL_RING : thm := BPrimes.RING_PRIME_IMP_NONTRIVIAL_RING
def RING_IRREDUCIBLE_IMP_NONTRIVIAL_RING : thm := BPrimes.RING_IRREDUCIBLE_IMP_NONTRIVIAL_RING
def FIELD_PRIME : thm := BPrimes.FIELD_PRIME
def FIELD_IRREDUCIBLE : thm := BPrimes.FIELD_IRREDUCIBLE
def RING_ASSOCIATES_PRIME : thm := BPrimes.RING_ASSOCIATES_PRIME
def RING_NONUNIT_DIVIDES_IRREDUCIBLE : thm := BPrimes.RING_NONUNIT_DIVIDES_IRREDUCIBLE
def RING_PRIME_DIVIDES_IRREDUCIBLE : thm := BPrimes.RING_PRIME_DIVIDES_IRREDUCIBLE
def RING_PRIME_DIVIDES_MUL : thm := BPrimes.RING_PRIME_DIVIDES_MUL
def RING_PRIME_DIVIDES_POW : thm := BPrimes.RING_PRIME_DIVIDES_POW
def RING_PRIME_DIVIDES_PRODUCT : thm := BPrimes.RING_PRIME_DIVIDES_PRODUCT
def INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE : thm := BPrimes.INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE
def INTEGRAL_DOMAIN_IRREDUCIBLE : thm := BPrimes.INTEGRAL_DOMAIN_IRREDUCIBLE
def INTEGRAL_DOMAIN_IRREDUCIBLE_ALT : thm := BPrimes.INTEGRAL_DOMAIN_IRREDUCIBLE_ALT
def INTEGRAL_DOMAIN_IRREDUCIBLE_DIVISORS : thm := BPrimes.INTEGRAL_DOMAIN_IRREDUCIBLE_DIVISORS
def RING_ASSOCIATES_IRREDUCIBLE : thm := BPrimes.RING_ASSOCIATES_IRREDUCIBLE
def INTEGRAL_DOMAIN_DIVIDES_PRIME_LMUL : thm := BPrimes.INTEGRAL_DOMAIN_DIVIDES_PRIME_LMUL
def INTEGRAL_DOMAIN_DIVIDES_PRIME_RMUL : thm := BPrimes.INTEGRAL_DOMAIN_DIVIDES_PRIME_RMUL
def RING_IRREDUCIBLE_DIVIDES_OR_COPRIME : thm := BPrimes.RING_IRREDUCIBLE_DIVIDES_OR_COPRIME
def RING_IRREDUCIBLE_COPRIME_EQ : thm := BPrimes.RING_IRREDUCIBLE_COPRIME_EQ
def RING_IRREDUCIBLES_COPRIME_OR_ASSOCIATES : thm := BPrimes.RING_IRREDUCIBLES_COPRIME_OR_ASSOCIATES
def INTEGRAL_DOMAIN_PRIME_DIVIDES_OR_COPRIME : thm := BPrimes.INTEGRAL_DOMAIN_PRIME_DIVIDES_OR_COPRIME
def INTEGRAL_DOMAIN_PRIME_COPRIME_EQ : thm := BPrimes.INTEGRAL_DOMAIN_PRIME_COPRIME_EQ
def INTEGRAL_DOMAIN_PRIMES_COPRIME_OR_ASSOCIATES : thm := BPrimes.INTEGRAL_DOMAIN_PRIMES_COPRIME_OR_ASSOCIATES
def INTEGRAL_DOMAIN_PRIMES_DIVIDES_EQ_ASSOCIATES : thm := BPrimes.INTEGRAL_DOMAIN_PRIMES_DIVIDES_EQ_ASSOCIATES
def RING_PRIME_ISOMORPHIC_IMAGE_EQ : thm := BPrimes.RING_PRIME_ISOMORPHIC_IMAGE_EQ
def RING_IRREDUCIBLE_ISOMORPHIC_IMAGE_EQ : thm := BPrimes.RING_IRREDUCIBLE_ISOMORPHIC_IMAGE_EQ
def RING_PRIME_MUL_DIVIDES : thm := BPrimes.RING_PRIME_MUL_DIVIDES
def RING_PRIME_MUL_DIVIDES_EQ : thm := BPrimes.RING_PRIME_MUL_DIVIDES_EQ
def RING_PRIME_PRODUCT_DIVIDES : thm := BPrimes.RING_PRIME_PRODUCT_DIVIDES
def INTEGRAL_DOMAIN_PRIME_PRODUCT_DIVIDES : thm := BPrimes.INTEGRAL_DOMAIN_PRIME_PRODUCT_DIVIDES

-- Factorizations
def RING_DIVIDES_PRIMEFACTS_INJECTION : thm := BFactorizations.RING_DIVIDES_PRIMEFACTS_INJECTION
def RING_DIVIDES_PRIMEFACTS_INJECTION_EQ : thm := BFactorizations.RING_DIVIDES_PRIMEFACTS_INJECTION_EQ
def RING_DIVIDES_PRIMEFACTS_LE : thm := BFactorizations.RING_DIVIDES_PRIMEFACTS_LE
def RING_ASSOCIATES_PRIMEFACTS_BIJECTION : thm := BFactorizations.RING_ASSOCIATES_PRIMEFACTS_BIJECTION
def RING_ASSOCIATES_PRIMEFACTS_BIJECTIONS : thm := BFactorizations.RING_ASSOCIATES_PRIMEFACTS_BIJECTIONS
def RING_ASSOCIATES_PRIMEFACTS_BIJECTIONS_EQ : thm := BFactorizations.RING_ASSOCIATES_PRIMEFACTS_BIJECTIONS_EQ
def RING_ASSOCIATES_PRIMEFACTS_BIJECTION_EQ : thm := BFactorizations.RING_ASSOCIATES_PRIMEFACTS_BIJECTION_EQ
def RING_ASSOCIATES_PRIMEFACTS_EQ : thm := BFactorizations.RING_ASSOCIATES_PRIMEFACTS_EQ
def RING_DIVIDES_PRIMEFACTS_LT : thm := BFactorizations.RING_DIVIDES_PRIMEFACTS_LT

-- Squarefree
def ring_squarefree : thm := BSquarefree.ring_squarefree
def RING_SQUAREFREE_IN_CARRIER : thm := BSquarefree.RING_SQUAREFREE_IN_CARRIER
def RING_UNIT_IMP_SQUAREFREE : thm := BSquarefree.RING_UNIT_IMP_SQUAREFREE
def RING_SQUAREFREE_1 : thm := BSquarefree.RING_SQUAREFREE_1
def RING_SQUAREFREE_DIVISOR : thm := BSquarefree.RING_SQUAREFREE_DIVISOR
def RING_SQUAREFREE_ASSOCIATES : thm := BSquarefree.RING_SQUAREFREE_ASSOCIATES
def RING_SQUAREFREE_0 : thm := BSquarefree.RING_SQUAREFREE_0
def RING_SQUAREFREE_IMP_NONZERO : thm := BSquarefree.RING_SQUAREFREE_IMP_NONZERO
def RING_IRREDUCIBLE_IMP_SQUAREFREE : thm := BSquarefree.RING_IRREDUCIBLE_IMP_SQUAREFREE
def RING_PRIME_IMP_SQUAREFREE : thm := BSquarefree.RING_PRIME_IMP_SQUAREFREE
def RING_SQUAREFREE_IMP_NO_PRIME_SQUARE : thm := BSquarefree.RING_SQUAREFREE_IMP_NO_PRIME_SQUARE
def RING_SQUAREFREE_COPRIME : thm := BSquarefree.RING_SQUAREFREE_COPRIME
def RING_SQUAREFREE_COPRIME_DIVISORS : thm := BSquarefree.RING_SQUAREFREE_COPRIME_DIVISORS
def RING_SQUAREFREE_MUL_IMP : thm := BSquarefree.RING_SQUAREFREE_MUL_IMP
def RING_SQUAREFREE_POW : thm := BSquarefree.RING_SQUAREFREE_POW
def ring_multsys : thm := BSquarefree.ring_multsys
def RING_MULTSYS : thm := BSquarefree.RING_MULTSYS
def RING_MULTSYS_IMP_SUBSET : thm := BSquarefree.RING_MULTSYS_IMP_SUBSET
def RING_MULTSYS_IMP_NONEMPTY : thm := BSquarefree.RING_MULTSYS_IMP_NONEMPTY
def RING_MULYSYS_1 : thm := BSquarefree.RING_MULYSYS_1
def RING_MULYSYS_CARRIER : thm := BSquarefree.RING_MULYSYS_CARRIER
def RING_MULTSYS_REGULAR : thm := BSquarefree.RING_MULTSYS_REGULAR
def RING_MULTSYS_NONZERO : thm := BSquarefree.RING_MULTSYS_NONZERO
def RING_MULTSYS_POWERS : thm := BSquarefree.RING_MULTSYS_POWERS
def RING_MULTSYS_UNITS : thm := BSquarefree.RING_MULTSYS_UNITS
def RING_MULTSYS_IDEMPOT : thm := BSquarefree.RING_MULTSYS_IDEMPOT
def RING_MULTSYS_INTERS : thm := BSquarefree.RING_MULTSYS_INTERS
def RING_MULTSYS_INTER : thm := BSquarefree.RING_MULTSYS_INTER
def RING_MULTSYS_HOMOMORPHIC_IMAGE : thm := BSquarefree.RING_MULTSYS_HOMOMORPHIC_IMAGE
def RING_1_IN_MULTSYS : thm := BSquarefree.RING_1_IN_MULTSYS
def RING_MUL_IN_MULTSYS : thm := BSquarefree.RING_MUL_IN_MULTSYS
def RING_POW_IN_MULTSYS : thm := BSquarefree.RING_POW_IN_MULTSYS
def RING_MULTSYS_NILPOTENT_EXISTS : thm := BSquarefree.RING_MULTSYS_NILPOTENT_EXISTS

-- Localization
def ring_localequiv : thm := BLocalization.ring_localequiv
def RING_LOCALEQUIV : thm := BLocalization.RING_LOCALEQUIV
def RING_LOCALEQUIV_REFL : thm := BLocalization.RING_LOCALEQUIV_REFL
def RING_LOCALEQUIV_SYM : thm := BLocalization.RING_LOCALEQUIV_SYM
def RING_LOCALEQUIV_TRANS : thm := BLocalization.RING_LOCALEQUIV_TRANS
def RING_LOCALEQUIV_EQUIV : thm := BLocalization.RING_LOCALEQUIV_EQUIV
def RING_LOCALEQUIV_NEG : thm := BLocalization.RING_LOCALEQUIV_NEG
def RING_LOCALEQUIV_ADD : thm := BLocalization.RING_LOCALEQUIV_ADD
def RING_LOCALEQUIV_MUL : thm := BLocalization.RING_LOCALEQUIV_MUL
def ring_localization : thm := BLocalization.ring_localization
def RING_LOCALIZATION : thm := BLocalization.RING_LOCALIZATION
def RING_LOCALIZATION_NEG : thm := BLocalization.RING_LOCALIZATION_NEG
def RING_LOCALIZATION_ADD : thm := BLocalization.RING_LOCALIZATION_ADD
def RING_LOCALIZATION_MUL : thm := BLocalization.RING_LOCALIZATION_MUL
def RING_LOCALIZATION_CARRIER : thm := BLocalization.RING_LOCALIZATION_CARRIER
def RING_LOCALIZATION_0 : thm := BLocalization.RING_LOCALIZATION_0
def RING_LOCALIZATION_1 : thm := BLocalization.RING_LOCALIZATION_1
def RING_LOCALIZATION_POW : thm := BLocalization.RING_LOCALIZATION_POW
def TRIVIAL_RING_LOCALIZATION : thm := BLocalization.TRIVIAL_RING_LOCALIZATION
def RING_LOCALEQUIV_IN_CARRIER : thm := BLocalization.RING_LOCALEQUIV_IN_CARRIER
def RING_UNIT_LOCALEQUIV : thm := BLocalization.RING_UNIT_LOCALEQUIV
def RING_UNIT_LOCALEQUIV_EQ : thm := BLocalization.RING_UNIT_LOCALEQUIV_EQ
def RING_UNIT_LOCALIZATION : thm := BLocalization.RING_UNIT_LOCALIZATION
def RING_LOCALEQUIV_EQ_0_GEN : thm := BLocalization.RING_LOCALEQUIV_EQ_0_GEN
def RING_IDEAL_LOCALIZATION : thm := BLocalization.RING_IDEAL_LOCALIZATION
def ring_fractionate : thm := BLocalization.ring_fractionate
def RING_FRACTIONATE_IN_CARRIER : thm := BLocalization.RING_FRACTIONATE_IN_CARRIER
def RING_UNIT_FRACTIONATE : thm := BLocalization.RING_UNIT_FRACTIONATE
def RING_FRACTIONATE_EQ_0_GEN : thm := BLocalization.RING_FRACTIONATE_EQ_0_GEN
def RING_HOMOMORPHISM_FRACTIONATE : thm := BLocalization.RING_HOMOMORPHISM_FRACTIONATE
def RING_MONOMORPHISM_FRACTIONATE_GEN : thm := BLocalization.RING_MONOMORPHISM_FRACTIONATE_GEN
def RING_ISOMORPHISM_FRACTIONATE_GEN : thm := BLocalization.RING_ISOMORPHISM_FRACTIONATE_GEN
def RING_LOCALIZATION_UNCHANGED : thm := BLocalization.RING_LOCALIZATION_UNCHANGED
def RING_LOCALIZATION_UNIVERSAL : thm := BLocalization.RING_LOCALIZATION_UNIVERSAL
def RING_LOCALIZATION_HOMOMORPHISM_EXISTS : thm := BLocalization.RING_LOCALIZATION_HOMOMORPHISM_EXISTS
def RING_LOCALEQUIV_SPLIT_EXPLICIT : thm := BLocalization.RING_LOCALEQUIV_SPLIT_EXPLICIT
def RING_LOCALEQUIV_SPLIT : thm := BLocalization.RING_LOCALEQUIV_SPLIT
def LOCALEQUIV_MUL_RCANCEL : thm := BLocalization.LOCALEQUIV_MUL_RCANCEL
def LOCALEQUIV_MUL_LCANCEL : thm := BLocalization.LOCALEQUIV_MUL_LCANCEL
def RING_LOCALIZATION_HOMOMORPHISM_UNIQUE : thm := BLocalization.RING_LOCALIZATION_HOMOMORPHISM_UNIQUE
def localization_map : thm := BLocalization2.localization_map
def RING_LOCALEQUIV_HOMOMORPHIC_IMAGE : thm := BLocalization2.RING_LOCALEQUIV_HOMOMORPHIC_IMAGE
def LOCALIZATION_MAP : thm := BLocalization2.LOCALIZATION_MAP
def RING_HOMOMORPHISM_LOCALIZATION_MAP : thm := BLocalization2.RING_HOMOMORPHISM_LOCALIZATION_MAP
def LOCALIZATION_MAP_I : thm := BLocalization2.LOCALIZATION_MAP_I
def LOCALIZATION_MAP_COMPOSE : thm := BLocalization2.LOCALIZATION_MAP_COMPOSE
def RING_ISOMORPHISM_LOCALIZATION_MAP : thm := BLocalization2.RING_ISOMORPHISM_LOCALIZATION_MAP
def RING_ISOMORPHISM_LOCALIZATION_LOCALIZATION : thm := BLocalization2.RING_ISOMORPHISM_LOCALIZATION_LOCALIZATION
def RING_ISOMORPHISM_LOCALIZATION_LOCALIZATION_GEN : thm := BLocalization2.RING_ISOMORPHISM_LOCALIZATION_LOCALIZATION_GEN
def RING_ISOMORPHISM_LOCALIZATION_SATURATION : thm := BLocalization2.RING_ISOMORPHISM_LOCALIZATION_SATURATION
def RING_ISOMORPHISM_LOCALIZATION_RESTRICT : thm := BLocalization2.RING_ISOMORPHISM_LOCALIZATION_RESTRICT
def RING_LOCALIZATION_UNIQUE : thm := BLocalization2.RING_LOCALIZATION_UNIQUE
def IDEAL_LOCALIZATION_CONTRACTION : thm := BLocalization2.IDEAL_LOCALIZATION_CONTRACTION
def RING_LOCALEQUIV_IN_LOCALIZATION_IDEAL : thm := BLocalization2.RING_LOCALEQUIV_IN_LOCALIZATION_IDEAL
def RING_IDEAL_LOCALIZATION_EXTENSION_CONTRACTION : thm := BLocalization2.RING_IDEAL_LOCALIZATION_EXTENSION_CONTRACTION
def RING_IDEAL_LOCALIZATION_CONTRACTION_EXTENSION : thm := BLocalization2.RING_IDEAL_LOCALIZATION_CONTRACTION_EXTENSION
def RING_LOCALIZATION_CONTRACTION_SUBSET : thm := BLocalization2.RING_LOCALIZATION_CONTRACTION_SUBSET
def IDEAL_GENERATED_RING_LOCALIZATION : thm := BLocalization2.IDEAL_GENERATED_RING_LOCALIZATION
def fraction_ring : thm := BLocalization2.fraction_ring
def RING_LOCALEQUIV_EQ_0 : thm := BLocalization2.RING_LOCALEQUIV_EQ_0
def RING_FRACTIONATE_EQ_0 : thm := BLocalization2.RING_FRACTIONATE_EQ_0
def RING_MONOMORPHISM_FRACTIONATE : thm := BLocalization2.RING_MONOMORPHISM_FRACTIONATE
def FRACTION_RING_UNIVERSAL : thm := BLocalization2.FRACTION_RING_UNIVERSAL
def RING_UNIT_FRACTION_RING : thm := BLocalization2.RING_UNIT_FRACTION_RING
def RING_ZERODIVISOR_FRACTION_RING : thm := BLocalization2.RING_ZERODIVISOR_FRACTION_RING
def FRACTION_RING_UNIT_EQ_REGULAR : thm := BLocalization2.FRACTION_RING_UNIT_EQ_REGULAR
def FRACTION_RING_UNIT_OR_ZERODIVISOR : thm := BLocalization2.FRACTION_RING_UNIT_OR_ZERODIVISOR
def TRIVIAL_FRACTION_RING : thm := BLocalization2.TRIVIAL_FRACTION_RING
def FRACTION_FIELD : thm := BLocalization2.FRACTION_FIELD
def FRACTION_DOMAIN : thm := BLocalization2.FRACTION_DOMAIN
def field_of_fractions : thm := BLocalization2.field_of_fractions
def FIELD_OF_FRACTIONS_IMP_INTEGRAL_DOMAIN : thm := BLocalization2.FIELD_OF_FRACTIONS_IMP_INTEGRAL_DOMAIN
def FIELD_OF_FRACTIONS_FRACTION_RING : thm := BLocalization2.FIELD_OF_FRACTIONS_FRACTION_RING
def FIELD_OF_FRACTIONS_EQ : thm := BLocalization2.FIELD_OF_FRACTIONS_EQ
def FIELD_OF_FRACTIONS_ISOMORPHISM_RIGHT : thm := BLocalization2.FIELD_OF_FRACTIONS_ISOMORPHISM_RIGHT
def FIELD_OF_FRACTIONS_ISOMORPHISM_LEFT : thm := BLocalization2.FIELD_OF_FRACTIONS_ISOMORPHISM_LEFT
def FRACTION_FIELD_COMMON_DENOMINATOR : thm := BLocalization2.FRACTION_FIELD_COMMON_DENOMINATOR
def FIELD_OF_FRACTIONS_COMMON_DENOMINATOR : thm := BLocalization2.FIELD_OF_FRACTIONS_COMMON_DENOMINATOR
def FIELD_OF_FRACTIONS_PROPORTIONAL : thm := BLocalization2.FIELD_OF_FRACTIONS_PROPORTIONAL
def INTEGRAL_DOMAIN_LOCALIZATION : thm := BLocalization2.INTEGRAL_DOMAIN_LOCALIZATION

-- SpecialIdeals
def proper_ideal : thm := BSpecialIdeals.proper_ideal
def principal_ideal : thm := BSpecialIdeals.principal_ideal
def finitely_generated_ideal : thm := BSpecialIdeals.finitely_generated_ideal
def prime_ideal : thm := BSpecialIdeals.prime_ideal
def maximal_ideal : thm := BSpecialIdeals.maximal_ideal
def PID : thm := BSpecialIdeals.PID
def noetherian_ring : thm := BSpecialIdeals.noetherian_ring
def PROPER_IMP_RING_IDEAL : thm := BSpecialIdeals.PROPER_IMP_RING_IDEAL
def PROPER_IDEAL_IMP_SUBSET : thm := BSpecialIdeals.PROPER_IDEAL_IMP_SUBSET
def PROPER_IDEAL_IMP_PSUBSET : thm := BSpecialIdeals.PROPER_IDEAL_IMP_PSUBSET
def PRINCIPAL_IMP_RING_IDEAL : thm := BSpecialIdeals.PRINCIPAL_IMP_RING_IDEAL
def PRINCIPAL_IDEAL_IMP_SUBSET : thm := BSpecialIdeals.PRINCIPAL_IDEAL_IMP_SUBSET
def FINITELY_GENERATED_IMP_RING_IDEAL : thm := BSpecialIdeals.FINITELY_GENERATED_IMP_RING_IDEAL
def FINITELY_GENERATED_IDEAL_IMP_SUBSET : thm := BSpecialIdeals.FINITELY_GENERATED_IDEAL_IMP_SUBSET
def FINITELY_GENERATED_IDEAL_SUBSET : thm := BSpecialIdeals.FINITELY_GENERATED_IDEAL_SUBSET
def PRIME_IMP_PROPER_IDEAL : thm := BSpecialIdeals.PRIME_IMP_PROPER_IDEAL
def PRIME_IMP_RING_IDEAL : thm := BSpecialIdeals.PRIME_IMP_RING_IDEAL
def PRIME_IDEAL_IMP_SUBSET : thm := BSpecialIdeals.PRIME_IDEAL_IMP_SUBSET
def PRIME_IDEAL_IMP_PSUBSET : thm := BSpecialIdeals.PRIME_IDEAL_IMP_PSUBSET
def MAXIMAL_IMP_PROPER_IDEAL : thm := BSpecialIdeals.MAXIMAL_IMP_PROPER_IDEAL
def MAXIMAL_IMP_RING_IDEAL : thm := BSpecialIdeals.MAXIMAL_IMP_RING_IDEAL
def MAXIMAL_IDEAL_IMP_SUBSET : thm := BSpecialIdeals.MAXIMAL_IDEAL_IMP_SUBSET
def MAXIMAL_IDEAL_IMP_PSUBSET : thm := BSpecialIdeals.MAXIMAL_IDEAL_IMP_PSUBSET
def PROPER_IDEAL_0 : thm := BSpecialIdeals.PROPER_IDEAL_0
def PRINCIPAL_IMP_FINITELY_GENERATED_IDEAL : thm := BSpecialIdeals.PRINCIPAL_IMP_FINITELY_GENERATED_IDEAL
def PID_IMP_INTEGRAL_DOMAIN : thm := BSpecialIdeals.PID_IMP_INTEGRAL_DOMAIN
def PID_IMP_NOETHERIAN_RING : thm := BSpecialIdeals.PID_IMP_NOETHERIAN_RING
def PRINCIPAL_IDEAL_ALT : thm := BSpecialIdeals.PRINCIPAL_IDEAL_ALT
def PRINCIPAL_IDEAL_IDEAL_GENERATED_SING : thm := BSpecialIdeals.PRINCIPAL_IDEAL_IDEAL_GENERATED_SING
def PRINCIPAL_IDEAL_0 : thm := BSpecialIdeals.PRINCIPAL_IDEAL_0
def FINITELY_GENERATED_IDEAL_0 : thm := BSpecialIdeals.FINITELY_GENERATED_IDEAL_0
def PRINCIPAL_IDEAL_CARRIER : thm := BSpecialIdeals.PRINCIPAL_IDEAL_CARRIER
def FINITELY_GENERATED_IDEAL_CARRIER : thm := BSpecialIdeals.FINITELY_GENERATED_IDEAL_CARRIER
def PROPER_IDEAL_ALT : thm := BSpecialIdeals.PROPER_IDEAL_ALT
def NONPRINCIPAL_IMP_PROPER_IDEAL : thm := BSpecialIdeals.NONPRINCIPAL_IMP_PROPER_IDEAL
def NONFINITELY_GENERATED_IMP_PROPER_IDEAL : thm := BSpecialIdeals.NONFINITELY_GENERATED_IMP_PROPER_IDEAL
def FINITELY_GENERATED_IDEAL_ALT : thm := BSpecialIdeals.FINITELY_GENERATED_IDEAL_ALT
def FINITELY_GENERATED_IDEAL_GENERATED : thm := BSpecialIdeals.FINITELY_GENERATED_IDEAL_GENERATED
def FINITELY_GENERATED_IDEAL_SETADD : thm := BSpecialIdeals.FINITELY_GENERATED_IDEAL_SETADD
def PROPER_IDEAL : thm := BSpecialIdeals.PROPER_IDEAL
def PROPER_IDEAL_UNIT : thm := BSpecialIdeals.PROPER_IDEAL_UNIT
def PROPER_IDEAL_SUBSET_NONUNITS : thm := BSpecialIdeals.PROPER_IDEAL_SUBSET_NONUNITS
def PROPER_IDEAL_UNIONS : thm := BSpecialIdeals.PROPER_IDEAL_UNIONS
def PROPER_IDEAL_EXISTS : thm := BSpecialIdeals.PROPER_IDEAL_EXISTS
def FINITELY_GENERATED_IDEAL_EPIMORPHIC_IMAGE : thm := BSpecialIdeals.FINITELY_GENERATED_IDEAL_EPIMORPHIC_IMAGE
def PRINCIPAL_IDEAL_EPIMORPHIC_IMAGE : thm := BSpecialIdeals.PRINCIPAL_IDEAL_EPIMORPHIC_IMAGE
def FINITELY_GENERATED_IDEAL_LOCALIZATION : thm := BSpecialIdeals.FINITELY_GENERATED_IDEAL_LOCALIZATION
def PRINCIPAL_IDEAL_LOCALIZATION : thm := BSpecialIdeals.PRINCIPAL_IDEAL_LOCALIZATION
def PROPER_IDEAL_HOMOMORPHIC_PREIMAGE : thm := BSpecialIdeals.PROPER_IDEAL_HOMOMORPHIC_PREIMAGE
def PROPER_IDEAL_CORRESPONDENCE : thm := BSpecialIdeals.PROPER_IDEAL_CORRESPONDENCE
def PROPER_IDEAL_ISOMORPHIC_IMAGE_EQ : thm := BSpecialIdeals.PROPER_IDEAL_ISOMORPHIC_IMAGE_EQ
def PRIME_IDEAL_HOMOMORPHIC_PREIMAGE : thm := BSpecialIdeals.PRIME_IDEAL_HOMOMORPHIC_PREIMAGE
def PRIME_IDEAL_PROD_RING : thm := BSpecialIdeals.PRIME_IDEAL_PROD_RING
def PRIME_IDEAL_PRODUCT_RING : thm := BSpecialIdeals.PRIME_IDEAL_PRODUCT_RING
def RING_1_NOT_IN_PRIME_IDEAL : thm := BSpecialIdeals.RING_1_NOT_IN_PRIME_IDEAL
def RING_UNIT_NOT_IN_PRIME_IDEAL : thm := BSpecialIdeals.RING_UNIT_NOT_IN_PRIME_IDEAL
def PRIME_IDEAL_UNIT_MUL : thm := BSpecialIdeals.PRIME_IDEAL_UNIT_MUL
def RING_MUL_IN_PRIME_IDEAL : thm := BSpecialIdeals.RING_MUL_IN_PRIME_IDEAL
def RING_PRODUCT_IN_PRIME_IDEAL : thm := BSpecialIdeals.RING_PRODUCT_IN_PRIME_IDEAL
def PRIME_IDEAL_COLON_SING : thm := BSpecialIdeals.PRIME_IDEAL_COLON_SING
def RING_POW_IN_PRIME_IDEAL : thm := BSpecialIdeals.RING_POW_IN_PRIME_IDEAL
def MAXIMAL_SUPERIDEAL_EXISTS : thm := BSpecialIdeals.MAXIMAL_SUPERIDEAL_EXISTS
def MAXIMAL_IDEAL_EXISTS : thm := BSpecialIdeals2.MAXIMAL_IDEAL_EXISTS
def RING_MULTSYS_NONPRIME : thm := BSpecialIdeals2.RING_MULTSYS_NONPRIME
def RING_MULTSYS_NONPRIME_EQ : thm := BSpecialIdeals2.RING_MULTSYS_NONPRIME_EQ
def RING_SATURATED_MULTSYS_NONPRIME : thm := BSpecialIdeals2.RING_SATURATED_MULTSYS_NONPRIME
def MAXIMAL_EXCLUDING_IMP_PRIME_IDEAL : thm := BSpecialIdeals2.MAXIMAL_EXCLUDING_IMP_PRIME_IDEAL
def MAXIMAL_IMP_PRIME_IDEAL : thm := BSpecialIdeals2.MAXIMAL_IMP_PRIME_IDEAL
def RING_MULTSYS_MAXIMAL_COMPLEMENT : thm := BSpecialIdeals2.RING_MULTSYS_MAXIMAL_COMPLEMENT
def MAXIMAL_AMONG_PRIME_IDEALS : thm := BSpecialIdeals2.MAXIMAL_AMONG_PRIME_IDEALS
def PRIME_IDEAL_0 : thm := BSpecialIdeals2.PRIME_IDEAL_0
def MAXIMAL_IDEAL_0 : thm := BSpecialIdeals2.MAXIMAL_IDEAL_0
def PRIME_SUPERIDEAL_EXISTS : thm := BSpecialIdeals2.PRIME_SUPERIDEAL_EXISTS
def PRIME_IDEAL_EXISTS : thm := BSpecialIdeals2.PRIME_IDEAL_EXISTS
def PRIME_SUPERIDEAL_EXCLUDING_EXISTS : thm := BSpecialIdeals2.PRIME_SUPERIDEAL_EXCLUDING_EXISTS
def PRIME_IDEAL_EXCLUDING_EXISTS : thm := BSpecialIdeals2.PRIME_IDEAL_EXCLUDING_EXISTS
def MAXIMAL_NONFG_IMP_PRIME_IDEAL : thm := BSpecialIdeals2.MAXIMAL_NONFG_IMP_PRIME_IDEAL
def PRIME_IDEAL_SING : thm := BSpecialIdeals2.PRIME_IDEAL_SING
def RING_PRIME_IDEAL : thm := BSpecialIdeals2.RING_PRIME_IDEAL
def PROPER_IDEAL_IDEAL_GENERATED_SING : thm := BSpecialIdeals2.PROPER_IDEAL_IDEAL_GENERATED_SING
def MAXIMAL_CONTAINING_IDEAL_EXISTS : thm := BSpecialIdeals2.MAXIMAL_CONTAINING_IDEAL_EXISTS
def UNIONS_MAXIMAL_IDEALS : thm := BSpecialIdeals2.UNIONS_MAXIMAL_IDEALS
def UNIONS_PROPER_IDEALS : thm := BSpecialIdeals2.UNIONS_PROPER_IDEALS
def UNIONS_PRIME_IDEALS : thm := BSpecialIdeals2.UNIONS_PRIME_IDEALS
def PROPER_IDEAL_NONUNITS : thm := BSpecialIdeals2.PROPER_IDEAL_NONUNITS
def MAXIMAL_IDEAL_NONUNITS : thm := BSpecialIdeals2.MAXIMAL_IDEAL_NONUNITS
def PRIME_IDEAL_NONUNITS : thm := BSpecialIdeals2.PRIME_IDEAL_NONUNITS
def RING_IDEAL_NONUNITS : thm := BSpecialIdeals2.RING_IDEAL_NONUNITS
def RING_IRREDUCIBLE_IMP_MAXIMAL_PRINCIPAL_IDEAL : thm := BSpecialIdeals2.RING_IRREDUCIBLE_IMP_MAXIMAL_PRINCIPAL_IDEAL
def RING_IRREDUCIBLE_EQ_MAXIMAL_PRINCIPAL_IDEAL : thm := BSpecialIdeals2.RING_IRREDUCIBLE_EQ_MAXIMAL_PRINCIPAL_IDEAL
def MAXIMAL_IDEAL_SING_IMP_IRREDUCIBLE : thm := BSpecialIdeals2.MAXIMAL_IDEAL_SING_IMP_IRREDUCIBLE
def RING_IRREDUCIBLE_EQ_MAXIMAL_IDEAL : thm := BSpecialIdeals2.RING_IRREDUCIBLE_EQ_MAXIMAL_IDEAL
def MAXIMAL_IDEAL_SING : thm := BSpecialIdeals2.MAXIMAL_IDEAL_SING
def PID_IRREDUCIBLE_EQ_PRIME : thm := BSpecialIdeals2.PID_IRREDUCIBLE_EQ_PRIME
def FIELD_EQ_TRIVIAL_IDEALS : thm := BSpecialIdeals2.FIELD_EQ_TRIVIAL_IDEALS
def FIELD_EQ_TRIVIAL_IDEALS_EQ : thm := BSpecialIdeals2.FIELD_EQ_TRIVIAL_IDEALS_EQ
def FIELD_EQ_NO_PROPER_IDEALS : thm := BSpecialIdeals2.FIELD_EQ_NO_PROPER_IDEALS
def FIELD_EQ_NO_PROPER_IDEALS_EQ : thm := BSpecialIdeals2.FIELD_EQ_NO_PROPER_IDEALS_EQ
def FIELD_EQ_PROPER_IMP_MAXIMAL_IDEAL : thm := BSpecialIdeals2.FIELD_EQ_PROPER_IMP_MAXIMAL_IDEAL
def FIELD_EQ_PROPER_IMP_PRIME_IDEAL : thm := BSpecialIdeals2.FIELD_EQ_PROPER_IMP_PRIME_IDEAL
def FIELD_PRIME_IDEAL_ZERO : thm := BSpecialIdeals2.FIELD_PRIME_IDEAL_ZERO
def FIELD_PRIME_IDEAL_ZERO_EXISTS : thm := BSpecialIdeals2.FIELD_PRIME_IDEAL_ZERO_EXISTS
def FIELD_IMP_PID : thm := BSpecialIdeals2.FIELD_IMP_PID
def FIELD_IMP_NOETHERIAN_RING : thm := BSpecialIdeals2.FIELD_IMP_NOETHERIAN_RING
def PID_MAXIMAL_EQ_PRIME_IDEAL : thm := BSpecialIdeals2.PID_MAXIMAL_EQ_PRIME_IDEAL
def PID_EQ_INTEGRAL_DOMAIN_PRIME_PRINCIPAL : thm := BSpecialIdeals2.PID_EQ_INTEGRAL_DOMAIN_PRIME_PRINCIPAL
def TRIVIAL_QUOTIENT_RING : thm := BSpecialIdeals2.TRIVIAL_QUOTIENT_RING
def INTEGRAL_DOMAIN_QUOTIENT_RING : thm := BSpecialIdeals2.INTEGRAL_DOMAIN_QUOTIENT_RING
def FIELD_QUOTIENT_RING : thm := BSpecialIdeals2.FIELD_QUOTIENT_RING
def PRIME_IDEAL_RING_KERNEL : thm := BSpecialIdeals2.PRIME_IDEAL_RING_KERNEL
def MAXIMAL_IDEAL_EPIMORPHISM_KERNEL : thm := BSpecialIdeals2.MAXIMAL_IDEAL_EPIMORPHISM_KERNEL
def IDEAL_GENERATED_UNIT_FIELD_TEST : thm := BSpecialIdeals2.IDEAL_GENERATED_UNIT_FIELD_TEST
def PRIME_IDEAL_CORRESPONDENCE : thm := BSpecialIdeals2.PRIME_IDEAL_CORRESPONDENCE
def PRIME_IDEAL_QUOTIENT_RING_IMAGE : thm := BSpecialIdeals2.PRIME_IDEAL_QUOTIENT_RING_IMAGE
def QUOTIENT_RING_PRIME_IDEAL_CORRESPONDENCE : thm := BSpecialIdeals2.QUOTIENT_RING_PRIME_IDEAL_CORRESPONDENCE
def PRIME_IDEAL_ISOMORPHIC_IMAGE_EQ : thm := BSpecialIdeals2.PRIME_IDEAL_ISOMORPHIC_IMAGE_EQ
def MAXIMAL_IDEAL_CORRESPONDENCE : thm := BSpecialIdeals2.MAXIMAL_IDEAL_CORRESPONDENCE
def MAXIMAL_IDEAL_EPIMORPHIC_PREIMAGE : thm := BSpecialIdeals2.MAXIMAL_IDEAL_EPIMORPHIC_PREIMAGE
def MAXIMAL_IDEAL_ISOMORPHIC_IMAGE_EQ : thm := BSpecialIdeals2.MAXIMAL_IDEAL_ISOMORPHIC_IMAGE_EQ
def ISOMORPHIC_RING_PIDNESS : thm := BSpecialIdeals2.ISOMORPHIC_RING_PIDNESS
def FIELD_HOMOMORPHISM_IMP_MONOMORPHISM : thm := BSpecialIdeals2.FIELD_HOMOMORPHISM_IMP_MONOMORPHISM
def FIELD_EPIMORPHISM_IMP_ISOMORPHISM : thm := BSpecialIdeals2.FIELD_EPIMORPHISM_IMP_ISOMORPHISM
def RING_EPIMORPHISM_ONTO_FIELD_EXISTS : thm := BSpecialIdeals2.RING_EPIMORPHISM_ONTO_FIELD_EXISTS
def FIELD_RING_HOMOMORPHISM_MONOMORPHISM : thm := BSpecialIdeals2.FIELD_RING_HOMOMORPHISM_MONOMORPHISM
def fraction_field_map : thm := BSpecialIdeals2.fraction_field_map
def FRACTION_FIELD_MAP_EQ : thm := BSpecialIdeals2.FRACTION_FIELD_MAP_EQ
def FRACTION_FIELD_MAP : thm := BSpecialIdeals2.FRACTION_FIELD_MAP
def FRACTION_FIELD_MAP_ISOMORPHISM : thm := BSpecialIdeals2.FRACTION_FIELD_MAP_ISOMORPHISM

-- Radical
def radical : thm := BRadical.radical
def RADICAL_SUBSET : thm := BRadical.RADICAL_SUBSET
def RADICAL_MONO : thm := BRadical.RADICAL_MONO
def RING_IDEAL_RADICAL : thm := BRadical.RING_IDEAL_RADICAL
def RADICAL_0 : thm := BRadical.RADICAL_0
def NILRADICAL_SUBSET : thm := BRadical.NILRADICAL_SUBSET
def RING_IDEAL_NILRADICAL : thm := BRadical.RING_IDEAL_NILRADICAL
def RADICAL_RING_CARRIER : thm := BRadical.RADICAL_RING_CARRIER
def RADICAL_ALT : thm := BRadical.RADICAL_ALT
def RING_POW_IN_RADICAL : thm := BRadical.RING_POW_IN_RADICAL
def RING_NILPOTENT_QUOTIENT_RING : thm := BRadical.RING_NILPOTENT_QUOTIENT_RING
def QUOTIENT_RING_REDUCED : thm := BRadical.QUOTIENT_RING_REDUCED
def INTEGRAL_DOMAIN_NILRADICAL : thm := BRadical.INTEGRAL_DOMAIN_NILRADICAL
def FIELD_NILRADICAL : thm := BRadical.FIELD_NILRADICAL
def RADICAL : thm := BRadical.RADICAL
def RING_NILRADICAL : thm := BRadical.RING_NILRADICAL
def INTERS_PRIME_IDEALS : thm := BRadical.INTERS_PRIME_IDEALS
def IN_NILRADICAL : thm := BRadical.IN_NILRADICAL
def IN_RADICAL_PRIME_IDEALS : thm := BRadical.IN_RADICAL_PRIME_IDEALS
def RADICAL_EQ_INTERS_PRIME_IDEALS : thm := BRadical.RADICAL_EQ_INTERS_PRIME_IDEALS
def RADICAL_LOCALIZATION : thm := BRadical.RADICAL_LOCALIZATION
def NILRADICAL_LOCALIZATION : thm := BRadical.NILRADICAL_LOCALIZATION
def RADICAL_RADICAL : thm := BRadical.RADICAL_RADICAL
def RADICAL_EQ_CARRIER : thm := BRadical.RADICAL_EQ_CARRIER
def PROPER_RADICAL : thm := BRadical.PROPER_RADICAL
def RADICAL_UNIONS : thm := BRadical.RADICAL_UNIONS
def RADICAL_UNION : thm := BRadical.RADICAL_UNION
def RADICAL_INTER : thm := BRadical.RADICAL_INTER
def RADICAL_SETADD : thm := BRadical.RADICAL_SETADD
def COMAXIMAL_RADICALS : thm := BRadical.COMAXIMAL_RADICALS
def RADICAL_PRIME_IDEAL : thm := BRadical.RADICAL_PRIME_IDEAL
def RADICAL_SUBSET_PRIME_IDEAL_EQ : thm := BRadical.RADICAL_SUBSET_PRIME_IDEAL_EQ
def RADICAL_IDEAL_PRIME_IDEAL_EQ : thm := BRadical.RADICAL_IDEAL_PRIME_IDEAL_EQ
def PRIME_IDEAL_CONTAINS_NILPOTENTS : thm := BRadical.PRIME_IDEAL_CONTAINS_NILPOTENTS
def jacobson_radical : thm := BRadical.jacobson_radical
def JACOBSON_RADICAL_SUBSET : thm := BRadical.JACOBSON_RADICAL_SUBSET
def RING_IDEAL_JACOBSON_RADICAL : thm := BRadical.RING_IDEAL_JACOBSON_RADICAL
def IN_JACOBSON_RADICAL : thm := BRadical.IN_JACOBSON_RADICAL
def RING_UNIT_LIFT_JACOBSON_RADICAL : thm := BRadical.RING_UNIT_LIFT_JACOBSON_RADICAL
def JACOBSON_RADICAL_EQ_INTERS_MAXIMAL_IDEALS : thm := BRadical.JACOBSON_RADICAL_EQ_INTERS_MAXIMAL_IDEALS
def NILRADICAL_SUBSET_JACOBSON_RADICAL : thm := BRadical.NILRADICAL_SUBSET_JACOBSON_RADICAL
def minimal_prime_over : thm := BRadical.minimal_prime_over
def minimal_prime_ideal : thm := BRadical.minimal_prime_ideal
def MINIMAL_PRIME_IDEAL_OVER : thm := BRadical.MINIMAL_PRIME_IDEAL_OVER
def PRIME_IDEAL_INTERS_CHAIN : thm := BRadical.PRIME_IDEAL_INTERS_CHAIN
def MINIMAL_PRIME_OVER_EXISTS : thm := BRadical.MINIMAL_PRIME_OVER_EXISTS
def MINIMAL_PRIME_IDEAL_EXISTS : thm := BRadical.MINIMAL_PRIME_IDEAL_EXISTS
def IN_RADICAL_MINIMAL_PRIMES : thm := BRadical.IN_RADICAL_MINIMAL_PRIMES
def RADICAL_EQ_INTERS_MINIMAL_PRIMES : thm := BRadical.RADICAL_EQ_INTERS_MINIMAL_PRIMES
def NILRADICAL_EQ_INTERS_MINIMAL_PRIMES : thm := BRadical.NILRADICAL_EQ_INTERS_MINIMAL_PRIMES
def MINIMAL_PRIME_OVER_PRINCIPAL : thm := BRadical.MINIMAL_PRIME_OVER_PRINCIPAL
def MINIMAL_PRIME_OVER_GENERATED : thm := BRadical.MINIMAL_PRIME_OVER_GENERATED
def RING_NILPOTENT_ADD : thm := BRadical.RING_NILPOTENT_ADD
def RING_NILPOTENT_LMUL : thm := BRadical.RING_NILPOTENT_LMUL
def RING_NILPOTENT_RMUL : thm := BRadical.RING_NILPOTENT_RMUL
def RING_NILPOTENT_SUB : thm := BRadical.RING_NILPOTENT_SUB
def RING_NILPOTENT_SUM : thm := BRadical.RING_NILPOTENT_SUM
def RING_ZERODIVISOR_NILPOTENT_CLAUSES : thm := BRadical.RING_ZERODIVISOR_NILPOTENT_CLAUSES
def RING_REGULAR_NILPOTENT_CLAUSES : thm := BRadical.RING_REGULAR_NILPOTENT_CLAUSES
def RING_UNIT_NILPOTENT_CLAUSES_1 : thm := BRadical.RING_UNIT_NILPOTENT_CLAUSES_1
def RING_UNIT_NILPOTENT_CLAUSES : thm := BRadical.RING_UNIT_NILPOTENT_CLAUSES
def RING_UNIT_MOD_NIL_IDEAL : thm := BRadical.RING_UNIT_MOD_NIL_IDEAL
def RING_NILPOTENT_UNIT : thm := BRadical.RING_NILPOTENT_UNIT
def UNIQUE_PRIME_IDEAL : thm := BRadical.UNIQUE_PRIME_IDEAL

-- UFDs
def UFD : thm := BUFDs.UFD
def UFD_IMP_INTEGRAL_DOMAIN : thm := BUFDs.UFD_IMP_INTEGRAL_DOMAIN
def PID_IMP_UFD : thm := BUFDs.PID_IMP_UFD
def FIELD_IMP_UFD : thm := BUFDs.FIELD_IMP_UFD
def ISOMORPHIC_RING_UFDNESS : thm := BUFDs.ISOMORPHIC_RING_UFDNESS
def UFD_EQ_PRIMEFACT : thm := BUFDs.UFD_EQ_PRIMEFACT
def UFD_EQ_PRIMEFACT_NONUNIT : thm := BUFDs.UFD_EQ_PRIMEFACT_NONUNIT
def UFD_PRIME_FACTOR_EXISTS : thm := BUFDs.UFD_PRIME_FACTOR_EXISTS
def UFD_IRREDUCIBLE_EQ_PRIME : thm := BUFDs.UFD_IRREDUCIBLE_EQ_PRIME
def UFD_EQ_ATOMIC : thm := BUFDs.UFD_EQ_ATOMIC
def UFD_EQ_ATOMIC_NONUNIT : thm := BUFDs.UFD_EQ_ATOMIC_NONUNIT
def UFD_EQ_UNIQUE_FACTORIZATION : thm := BUFDs.UFD_EQ_UNIQUE_FACTORIZATION
def UFD_PRIME_POWER_FACTORIZATION : thm := BUFDs.UFD_PRIME_POWER_FACTORIZATION
def UFD_COPRIME : thm := BUFDs.UFD_COPRIME
def UFD_PRIME_FACTOR_INDUCT : thm := BUFDs.UFD_PRIME_FACTOR_INDUCT
def UFD_IMP_GCD_EXISTS : thm := BUFDs.UFD_IMP_GCD_EXISTS
def PID_EQ_UFD_PRIME_MAXIMAL : thm := BUFDs.PID_EQ_UFD_PRIME_MAXIMAL
def RING_DIVIDES_LOCALEQUIV : thm := BUFDs.RING_DIVIDES_LOCALEQUIV
def UFD_LOCALIZATION : thm := BUFDs.UFD_LOCALIZATION
def PROPER_IDEAL_LOCALIZATION : thm := BUFDs.PROPER_IDEAL_LOCALIZATION
def RING_LOCALEQUIV_IN_LOCALIZED_IDEAL : thm := BUFDs.RING_LOCALEQUIV_IN_LOCALIZED_IDEAL
def PRIME_IDEAL_LOCALIZATION_CONTRACTION : thm := BUFDs.PRIME_IDEAL_LOCALIZATION_CONTRACTION
def PRIME_IDEAL_LOCALIZATION : thm := BUFDs.PRIME_IDEAL_LOCALIZATION
def PRIME_IDEAL_LOCALIZATION_EXISTS : thm := BUFDs.PRIME_IDEAL_LOCALIZATION_EXISTS
def RING_LOCALIZATION_PRIME_IDEAL_CORRESPONDENCE : thm := BUFDs.RING_LOCALIZATION_PRIME_IDEAL_CORRESPONDENCE
def PROPER_IDEAL_LOCALIZATION_EQ : thm := BUFDs.PROPER_IDEAL_LOCALIZATION_EQ
def PRIME_IDEAL_LOCALIZATION_EXTENSION : thm := BUFDs.PRIME_IDEAL_LOCALIZATION_EXTENSION
def PRIME_IDEAL_LOCALIZATION_CONTRACTION_EXTENSION : thm := BUFDs.PRIME_IDEAL_LOCALIZATION_CONTRACTION_EXTENSION
def RING_LOCALIZATION_PRIME_IDEAL_BIJ : thm := BUFDs.RING_LOCALIZATION_PRIME_IDEAL_BIJ
def RING_LOCALIZATION_PRIME_IDEAL_SUBSET : thm := BUFDs.RING_LOCALIZATION_PRIME_IDEAL_SUBSET
def RING_LOCALIZATION_AT_PRIME_IDEAL_BIJ : thm := BUFDs.RING_LOCALIZATION_AT_PRIME_IDEAL_BIJ
def RING_LOCALIZATION_AT_PRIME_NONUNITS : thm := BUFDs.RING_LOCALIZATION_AT_PRIME_NONUNITS
def RING_ISOMORPHISM_LOCALIZATION_AT_PRIME_LOCALIZATION : thm := BUFDs.RING_ISOMORPHISM_LOCALIZATION_AT_PRIME_LOCALIZATION
def MINIMAL_PRIME_OVER_POW : thm := BUFDs.MINIMAL_PRIME_OVER_POW

-- Euclidean
def euclidean_ring : thm := BEuclidean.euclidean_ring
def EUCLIDEAN_RING : thm := BEuclidean.EUCLIDEAN_RING
def EUCLIDEAN_RING_ALT : thm := BEuclidean.EUCLIDEAN_RING_ALT
def EUCLIDEAN_IMP_PRINCIPAL_IDEAL_RING : thm := BEuclidean.EUCLIDEAN_IMP_PRINCIPAL_IDEAL_RING
def EUCLIDEAN_DOMAIN_IMP_PID : thm := BEuclidean.EUCLIDEAN_DOMAIN_IMP_PID
def EUCLIDEAN_RING_UNIVERSAL_SIDE_DIVISOR : thm := BEuclidean.EUCLIDEAN_RING_UNIVERSAL_SIDE_DIVISOR
def EUCLIDEAN_RING_EPIMORPHIC_IMAGE : thm := BEuclidean.EUCLIDEAN_RING_EPIMORPHIC_IMAGE
def EUCLIDEAN_QUOTIENT_RING : thm := BEuclidean.EUCLIDEAN_QUOTIENT_RING
def ISOMORPHIC_RING_EUCLIDEANNESS : thm := BEuclidean.ISOMORPHIC_RING_EUCLIDEANNESS

-- Noetherian
def NOETHERIAN_RING : thm := BNoetherian.NOETHERIAN_RING
def NOETHERIAN_RING_EQ_ACC : thm := BNoetherian.NOETHERIAN_RING_EQ_ACC
def NOETHERIAN_RING_EQ_MAXIMAL : thm := BNoetherian.NOETHERIAN_RING_EQ_MAXIMAL
def NOETHERIAN_RING_EPIMORPHIC_IMAGE : thm := BNoetherian.NOETHERIAN_RING_EPIMORPHIC_IMAGE
def NOETHERIAN_QUOTIENT_RING : thm := BNoetherian.NOETHERIAN_QUOTIENT_RING
def ISOMORPHIC_RING_NOETHERIANNESS : thm := BNoetherian.ISOMORPHIC_RING_NOETHERIANNESS
def NOETHERIAN_PROD_RING : thm := BNoetherian.NOETHERIAN_PROD_RING
def NOETHERIAN_PRODUCT_RING : thm := BNoetherian.NOETHERIAN_PRODUCT_RING
def NOETHERIAN_RING_EQ_FG_PRIME_IDEALS : thm := BNoetherian.NOETHERIAN_RING_EQ_FG_PRIME_IDEALS
def NOETHERIAN_RING_LOCALIZATION : thm := BNoetherian.NOETHERIAN_RING_LOCALIZATION

-- ACCP
def RING_ACCP : thm := BACCP.RING_ACCP
def RING_DIVIDES_WF : thm := BACCP.RING_DIVIDES_WF
def RING_PRINCIPAL_IDEALS_WF : thm := BACCP.RING_PRINCIPAL_IDEALS_WF
def ACCP_RING_PROPER_DIVISOR_INDUCT : thm := BACCP.ACCP_RING_PROPER_DIVISOR_INDUCT
def RING_PROPER_DIVISOR_INDUCT : thm := BACCP.RING_PROPER_DIVISOR_INDUCT
def ACCP_DOMAIN_ATOMIC : thm := BACCP.ACCP_DOMAIN_ATOMIC
def ACCP_DOMAIN_IRREDUCIBLE_FACTOR_EXISTS : thm := BACCP.ACCP_DOMAIN_IRREDUCIBLE_FACTOR_EXISTS
def NOETHERIAN_DOMAIN_ATOMIC : thm := BACCP.NOETHERIAN_DOMAIN_ATOMIC
def NOETHERIAN_DOMAIN_IRREDUCIBLE_FACTOR_EXISTS : thm := BACCP.NOETHERIAN_DOMAIN_IRREDUCIBLE_FACTOR_EXISTS
def UFD_EQ_ACCP : thm := BACCP.UFD_EQ_ACCP

-- RingGcd
def ring_gcd : thm := BRingGcd.ring_gcd
def RING_GCD_WORKS : thm := BRingGcd.RING_GCD_WORKS
def RING_GCD_UNIQUE : thm := BRingGcd.RING_GCD_UNIQUE
def RING_GCD_REFL : thm := BRingGcd.RING_GCD_REFL
def RING_GCD : thm := BRingGcd.RING_GCD
def RING_GCD_EQ : thm := BRingGcd.RING_GCD_EQ
def RING_GCD_SYM : thm := BRingGcd.RING_GCD_SYM
def RING_GCD_DIVIDES : thm := BRingGcd.RING_GCD_DIVIDES
def RING_UNIT_GCD : thm := BRingGcd.RING_UNIT_GCD
def RING_GCD_EQ_1 : thm := BRingGcd.RING_GCD_EQ_1
def UFD_DIVIDES_GCD : thm := BRingGcd.UFD_DIVIDES_GCD
def UFD_DIVIDES_GCD_EQ : thm := BRingGcd.UFD_DIVIDES_GCD_EQ
def RING_GCD_00 : thm := BRingGcd.RING_GCD_00
def FIELD_GCD : thm := BRingGcd.FIELD_GCD

-- Bezout
def bezout_ring : thm := BBezout.bezout_ring
def BEZOUT_RING_FINITELY_GENERATED_EQ_PRINCIPAL_IDEAL : thm := BBezout.BEZOUT_RING_FINITELY_GENERATED_EQ_PRINCIPAL_IDEAL
def PID_IMP_BEZOUT_RING : thm := BBezout.PID_IMP_BEZOUT_RING
def FIELD_IMP_BEZOUT_RING : thm := BBezout.FIELD_IMP_BEZOUT_RING
def BEZOUT_RING_2 : thm := BBezout.BEZOUT_RING_2
def BEZOUT_RING_SETADD : thm := BBezout.BEZOUT_RING_SETADD
def PID_EQ_NOETHERIAN_BEZOUT_DOMAIN : thm := BBezout.PID_EQ_NOETHERIAN_BEZOUT_DOMAIN
def BEZOUT_RING_IMP_BEZOUT : thm := BBezout.BEZOUT_RING_IMP_BEZOUT
def RING_IMP_GCD_EXISTS : thm := BBezout.RING_IMP_GCD_EXISTS
def BEZOUT_RING_IMP_GCD : thm := BBezout.BEZOUT_RING_IMP_GCD
def BEZOUT_RING : thm := BBezout.BEZOUT_RING
def BEZOUT_RING_COPRIME : thm := BBezout.BEZOUT_RING_COPRIME
def BEZOUT_RING_COPRIME_COMAXIMAL : thm := BBezout.BEZOUT_RING_COPRIME_COMAXIMAL
def BEZOUT_RING_COMAXIMAL_COPRIME : thm := BBezout.BEZOUT_RING_COMAXIMAL_COPRIME
def RING_DIVIDES_GCD : thm := BBezout.RING_DIVIDES_GCD
def RING_DIVIDES_GCD_EQ : thm := BBezout.RING_DIVIDES_GCD_EQ
def BEZOUT_RING_IRREDUCIBLE_IMP_PRIME : thm := BBezout.BEZOUT_RING_IRREDUCIBLE_IMP_PRIME
def BEZOUT_DOMAIN_IRREDUCIBLE_EQ_PRIME : thm := BBezout.BEZOUT_DOMAIN_IRREDUCIBLE_EQ_PRIME
def PID_EQ_ACCP_BEZOUT_DOMAIN : thm := BBezout.PID_EQ_ACCP_BEZOUT_DOMAIN
def PID_EQ_UFD_BEZOUT_RING : thm := BBezout.PID_EQ_UFD_BEZOUT_RING
def PID_EQ_BEZOUT_ATOMIC : thm := BBezout.PID_EQ_BEZOUT_ATOMIC
def BEZOUT_RING_EPIMORPHIC_IMAGE : thm := BBezout.BEZOUT_RING_EPIMORPHIC_IMAGE
def BEZOUT_QUOTIENT_RING : thm := BBezout.BEZOUT_QUOTIENT_RING
def ISOMORPHIC_RING_BEZOUTNESS : thm := BBezout.ISOMORPHIC_RING_BEZOUTNESS
def RING_COPRIME_HOMOMORPHIC_IMAGE : thm := BBezout.RING_COPRIME_HOMOMORPHIC_IMAGE
def BEZOUT_RING_LOCALIZATION : thm := BBezout.BEZOUT_RING_LOCALIZATION
def PID_RING_LOCALIZATION : thm := BBezout.PID_RING_LOCALIZATION

-- GcdDomain
def RING_GCD_LMUL : thm := BGcdDomain.RING_GCD_LMUL
def RING_GCD_RMUL : thm := BGcdDomain.RING_GCD_RMUL
def RING_COPRIME_DIVPROD_LEFT : thm := BGcdDomain.RING_COPRIME_DIVPROD_LEFT
def RING_COPRIME_DIVPROD_RIGHT : thm := BGcdDomain.RING_COPRIME_DIVPROD_RIGHT
def RING_DIVIDES_MUL : thm := BGcdDomain.RING_DIVIDES_MUL
def RING_DIVIDES_MUL_EQ : thm := BGcdDomain.RING_DIVIDES_MUL_EQ
def RING_COPRIME_LMUL : thm := BGcdDomain.RING_COPRIME_LMUL
def RING_COPRIME_RMUL : thm := BGcdDomain.RING_COPRIME_RMUL
def RING_COPRIME_PRODUCT_EQ : thm := BGcdDomain.RING_COPRIME_PRODUCT_EQ
def RING_COPRIME_PRODUCT : thm := BGcdDomain.RING_COPRIME_PRODUCT
def RING_COPRIME_RPOW : thm := BGcdDomain.RING_COPRIME_RPOW
def RING_COPRIME_LPOW : thm := BGcdDomain.RING_COPRIME_LPOW
def RING_COPRIME_PRODUCT_DIVIDES_ALT : thm := BGcdDomain.RING_COPRIME_PRODUCT_DIVIDES_ALT
def RING_COPRIME_PRODUCT_DIVIDES : thm := BGcdDomain.RING_COPRIME_PRODUCT_DIVIDES
def PID_COPRIME_PRIME_POWERS : thm := BGcdDomain.PID_COPRIME_PRIME_POWERS
def PID_DIVIDES_PRIME_POWERS : thm := BGcdDomain.PID_DIVIDES_PRIME_POWERS

-- SquarefreeUFD
def RING_SQUAREFREE_GCD : thm := BSquarefreeUFD.RING_SQUAREFREE_GCD
def RING_SQUAREFREE_PRIME_EQ : thm := BSquarefreeUFD.RING_SQUAREFREE_PRIME_EQ
def RING_SQUAREFREE_PRIME_DIVISOR_EQ : thm := BSquarefreeUFD.RING_SQUAREFREE_PRIME_DIVISOR_EQ
def RING_SQUAREFREE_DIVIDES : thm := BSquarefreeUFD.RING_SQUAREFREE_DIVIDES
def RING_SQUAREFREE_DIVPOW : thm := BSquarefreeUFD.RING_SQUAREFREE_DIVPOW
def RING_SQUAREFREE_DIVPOW_EQ : thm := BSquarefreeUFD.RING_SQUAREFREE_DIVPOW_EQ
def RING_SQUAREFREE_DIVIDES_SQUARE : thm := BSquarefreeUFD.RING_SQUAREFREE_DIVIDES_SQUARE
def RING_SQUAREFREE_MUL_EQ : thm := BSquarefreeUFD.RING_SQUAREFREE_MUL_EQ
def RING_SQUAREFREE_PRODUCT : thm := BSquarefreeUFD.RING_SQUAREFREE_PRODUCT
def RING_SQUAREFREE_ALT : thm := BSquarefreeUFD.RING_SQUAREFREE_ALT
def RING_SQUAREFREE : thm := BSquarefreeUFD.RING_SQUAREFREE
def RING_SQUAREFREE_DECOMPOSITION : thm := BSquarefreeUFD.RING_SQUAREFREE_DECOMPOSITION

-- BooleanRings
def boolean_ring : thm := BBooleanRings.boolean_ring
def BOOLEAN_RING_SQUARE : thm := BBooleanRings.BOOLEAN_RING_SQUARE
def BOOLEAN_RING_DOUBLE : thm := BBooleanRings.BOOLEAN_RING_DOUBLE
def BOOLEAN_RING_NEG : thm := BBooleanRings.BOOLEAN_RING_NEG
def BOOLEAN_RING_POW : thm := BBooleanRings.BOOLEAN_RING_POW
def BOOLEAN_RING_OF_NUM : thm := BBooleanRings.BOOLEAN_RING_OF_NUM
def BOOLEAN_RING_CHAR : thm := BBooleanRings.BOOLEAN_RING_CHAR
def BOOLEAN_RING_UNIT : thm := BBooleanRings.BOOLEAN_RING_UNIT
def BOOLEAN_RING_ZERODIVISOR : thm := BBooleanRings.BOOLEAN_RING_ZERODIVISOR
def BOOLEAN_RING_REGULAR : thm := BBooleanRings.BOOLEAN_RING_REGULAR
def BOOLEAN_RING_IRREDUCIBLE : thm := BBooleanRings.BOOLEAN_RING_IRREDUCIBLE
def BOOLEAN_RING_DIVIDES : thm := BBooleanRings.BOOLEAN_RING_DIVIDES
def BOOLEAN_RING_NILPOTENT : thm := BBooleanRings.BOOLEAN_RING_NILPOTENT
def BOOLEAN_RING_RADICAL : thm := BBooleanRings.BOOLEAN_RING_RADICAL
def TRIVIAL_IMP_BOOLEAN_RING : thm := BBooleanRings.TRIVIAL_IMP_BOOLEAN_RING
def BOOLEAN_RING_10 : thm := BBooleanRings.BOOLEAN_RING_10
def BOOLEAN_RING_2 : thm := BBooleanRings.BOOLEAN_RING_2
def ISOMORPHIC_RING_BOOLEANNESS : thm := BBooleanRings.ISOMORPHIC_RING_BOOLEANNESS
def BOOLEAN_RING_EPIMORPHIC_IMAGE : thm := BBooleanRings.BOOLEAN_RING_EPIMORPHIC_IMAGE
def BOOLEAN_QUOTIENT_RING : thm := BBooleanRings.BOOLEAN_QUOTIENT_RING
def BOOLEAN_RING_SUBRING_GENERATED : thm := BBooleanRings.BOOLEAN_RING_SUBRING_GENERATED
def BOOLEAN_RING_MONOMORPHIC_PREIMAGE : thm := BBooleanRings.BOOLEAN_RING_MONOMORPHIC_PREIMAGE
def BOOLEAN_PROD_RING : thm := BBooleanRings.BOOLEAN_PROD_RING
def BOOLEAN_PRODUCT_RING : thm := BBooleanRings.BOOLEAN_PRODUCT_RING
def BOOLEAN_IMP_BEZOUT_RING : thm := BBooleanRings.BOOLEAN_IMP_BEZOUT_RING
def BOOLEAN_RING_MAXIMAL_EQ_PRIME_IDEAL : thm := BBooleanRings.BOOLEAN_RING_MAXIMAL_EQ_PRIME_IDEAL
def BOOLEAN_RING_MULTSYS : thm := BBooleanRings.BOOLEAN_RING_MULTSYS
def BOOLEAN_PROPER_IDEAL_COMPLEMENT : thm := BBooleanRings.BOOLEAN_PROPER_IDEAL_COMPLEMENT
def BOOLEAN_INTEGRAL_DOMAIN : thm := BBooleanRings.BOOLEAN_INTEGRAL_DOMAIN

-- LocalRings
def local_ring : thm := BLocalRings.local_ring
def LOCAL_IMP_NONTRIVIAL_RING : thm := BLocalRings.LOCAL_IMP_NONTRIVIAL_RING
def LOCAL_RING_IDEAL_NONUNITS : thm := BLocalRings.LOCAL_RING_IDEAL_NONUNITS
def LOCAL_RING_MAXIMAL_IDEAL_NONUNITS : thm := BLocalRings.LOCAL_RING_MAXIMAL_IDEAL_NONUNITS
def LOCAL_RING_UNIT_ADD_NONUNIT : thm := BLocalRings.LOCAL_RING_UNIT_ADD_NONUNIT
def LOCAL_RING_PRIME_SUBSET_MAXIMAL : thm := BLocalRings.LOCAL_RING_PRIME_SUBSET_MAXIMAL
def LOCAL_RING_PROPER_IDEAL_SUBSET_MAXIMAL : thm := BLocalRings.LOCAL_RING_PROPER_IDEAL_SUBSET_MAXIMAL
def LOCAL_RING_SELECT_MAXIMAL_IDEAL : thm := BLocalRings.LOCAL_RING_SELECT_MAXIMAL_IDEAL
def JACOBSON_RADICAL_LOCAL_RING : thm := BLocalRings.JACOBSON_RADICAL_LOCAL_RING
def LOCAL_RING_JACOBSON_RADICAL : thm := BLocalRings.LOCAL_RING_JACOBSON_RADICAL
def MINIMAL_PRIME_OVER_LOCAL_RADICAL : thm := BLocalRings.MINIMAL_PRIME_OVER_LOCAL_RADICAL
def FIELD_IMP_LOCAL_RING : thm := BLocalRings.FIELD_IMP_LOCAL_RING
def UNIQUE_PRIME_IDEAL_IMP_LOCAL_RING : thm := BLocalRings.UNIQUE_PRIME_IDEAL_IMP_LOCAL_RING
def LOCAL_RING_EPIMORPHIC_IMAGE : thm := BLocalRings.LOCAL_RING_EPIMORPHIC_IMAGE
def LOCAL_QUOTIENT_RING : thm := BLocalRings.LOCAL_QUOTIENT_RING
def ISOMORPHIC_RING_LOCALITY : thm := BLocalRings.ISOMORPHIC_RING_LOCALITY
def LOCAL_RING_LOCALIZATION : thm := BLocalRings.LOCAL_RING_LOCALIZATION
def MAXIMAL_IDEAL_LOCALIZATION_AT_PRIME : thm := BLocalRings.MAXIMAL_IDEAL_LOCALIZATION_AT_PRIME
def MAXIMAL_IDEAL_LOCALIZATION_AT_PRIME_CONTRACTION : thm := BLocalRings.MAXIMAL_IDEAL_LOCALIZATION_AT_PRIME_CONTRACTION
def NOETHERIAN_LOCAL_RING_LOCALIZATION : thm := BLocalRings.NOETHERIAN_LOCAL_RING_LOCALIZATION
def residue_field : thm := BLocalRings.residue_field
def residue_hom : thm := BLocalRings.residue_hom
def RESIDUE_FIELD_LOCAL_FACTS : thm := BLocalRings.RESIDUE_FIELD_LOCAL_FACTS
def FIELD_RESIDUE_FIELD : thm := BLocalRings.FIELD_RESIDUE_FIELD
def RING_HOMOMORPHISM_RESIDUE_HOM : thm := BLocalRings.RING_HOMOMORPHISM_RESIDUE_HOM
def RESIDUE_HOM_EQ_0 : thm := BLocalRings.RESIDUE_HOM_EQ_0
def RESIDUE_FIELD_FRACTION : thm := BLocalRings.RESIDUE_FIELD_FRACTION
def RING_HOMOMORPHISMS_EQ_FROM_RESIDUE_FIELD : thm := BLocalRings.RING_HOMOMORPHISMS_EQ_FROM_RESIDUE_FIELD
def RESIDUE_HOM_FUNCTORIAL : thm := BLocalRings.RESIDUE_HOM_FUNCTORIAL
def RESIDUE_HOM_FUNCTORIAL_QUOTIENT : thm := BLocalRings.RESIDUE_HOM_FUNCTORIAL_QUOTIENT
def FIELD_OF_FRACTIONS_RESIDUE_FIELD : thm := BLocalRings.FIELD_OF_FRACTIONS_RESIDUE_FIELD
def RING_ISOMORPHISM_QUOTIENT_RESIDUE_FIELD : thm := BLocalRings.RING_ISOMORPHISM_QUOTIENT_RESIDUE_FIELD

-- VonNeumann
def vnregular_ring : thm := BVonNeumann.vnregular_ring
def FIELD_IMP_VNREGULAR_RING : thm := BVonNeumann.FIELD_IMP_VNREGULAR_RING
def BOOLEAN_IMP_VNREGULAR_RING : thm := BVonNeumann.BOOLEAN_IMP_VNREGULAR_RING
def VNREGULAR_RING_EPIMORPHIC_IMAGE : thm := BVonNeumann.VNREGULAR_RING_EPIMORPHIC_IMAGE
def VNREGULAR_QUOTIENT_RING : thm := BVonNeumann.VNREGULAR_QUOTIENT_RING
def ISOMORPHIC_RING_VNREGULARITY : thm := BVonNeumann.ISOMORPHIC_RING_VNREGULARITY
def VNREGULAR_PROD_RING : thm := BVonNeumann.VNREGULAR_PROD_RING
def VNREGULAR_PRODUCT_RING : thm := BVonNeumann.VNREGULAR_PRODUCT_RING
def VNREGULAR_IMP_REDUCED_RING : thm := BVonNeumann.VNREGULAR_IMP_REDUCED_RING
def VNREGULAR_RING_NILPOTENT : thm := BVonNeumann.VNREGULAR_RING_NILPOTENT
def VNREGULAR_RING_REGULAR : thm := BVonNeumann.VNREGULAR_RING_REGULAR
def VNREGULAR_DOMAIN : thm := BVonNeumann.VNREGULAR_DOMAIN
def VNREGULAR_RING_PRINCIPAL_IDEALS : thm := BVonNeumann.VNREGULAR_RING_PRINCIPAL_IDEALS
def VNREGULAR_IMP_BEZOUT_RING : thm := BVonNeumann.VNREGULAR_IMP_BEZOUT_RING
def VNREGULAR_RING_FINITELY_GENERATED_IDEALS : thm := BVonNeumann.VNREGULAR_RING_FINITELY_GENERATED_IDEALS
def VNREGULAR_RING_IDEAL_IDEMPOT : thm := BVonNeumann.VNREGULAR_RING_IDEAL_IDEMPOT
def VNREGULAR_RING : thm := BVonNeumann.VNREGULAR_RING
def VNREGULAR_RING_ALT : thm := BVonNeumann.VNREGULAR_RING_ALT
def VNREGULAR_RING_LOCALIZATION : thm := BVonNeumann.VNREGULAR_RING_LOCALIZATION
def VNREGULAR_FRACTION_RING : thm := BVonNeumann.VNREGULAR_FRACTION_RING

-- BoolRing
def bool_ring : thm := BBoolRing.bool_ring
def BOOL_RING : thm := BBoolRing.BOOL_RING
def FIELD_BOOL_RING : thm := BBoolRing.FIELD_BOOL_RING
def NOT_TRIVIAL_BOOL_RING : thm := BBoolRing.NOT_TRIVIAL_BOOL_RING
def BOOLEAN_RING_BOOL_RING : thm := BBoolRing.BOOLEAN_RING_BOOL_RING
def INTEGRAL_DOMAIN_BOOL_RING : thm := BBoolRing.INTEGRAL_DOMAIN_BOOL_RING
def BOOL_RING_CARRIER_HAS_SIZE_2 : thm := BBoolRing.BOOL_RING_CARRIER_HAS_SIZE_2
def ISOMORPHIC_RING_BOOL_RING : thm := BBoolRing.ISOMORPHIC_RING_BOOL_RING

-- IntegerRing
def integer_ring : thm := BIntegerRing.integer_ring
def INTEGER_RING : thm := BIntegerRing.INTEGER_RING
def INTEGER_RING_POW : thm := BIntegerRing.INTEGER_RING_POW
def INTEGER_RING_SUM : thm := BIntegerRing.INTEGER_RING_SUM
def INTEGER_RING_PRODUCT : thm := BIntegerRing.INTEGER_RING_PRODUCT
def INTEGER_RING_UNIT : thm := BIntegerRing.INTEGER_RING_UNIT
def INTEGER_RING_DIVIDES : thm := BIntegerRing.INTEGER_RING_DIVIDES
def NOT_TRIVIAL_INTEGER_RING : thm := BIntegerRing.NOT_TRIVIAL_INTEGER_RING
def NOT_FIELD_INTEGER_RING : thm := BIntegerRing.NOT_FIELD_INTEGER_RING
def RING_HOMOMORPHISM_INTEGER_RING_OF_INT : thm := BIntegerRing.RING_HOMOMORPHISM_INTEGER_RING_OF_INT
def RING_OF_INT_ISUM : thm := BIntegerRing.RING_OF_INT_ISUM
def RING_MONOMORPHISM_INTEGER_RING_OF_INT : thm := BIntegerRing.RING_MONOMORPHISM_INTEGER_RING_OF_INT
def INTEGRAL_DOMAIN_INTEGER_RING : thm := BIntegerRing.INTEGRAL_DOMAIN_INTEGER_RING
def EUCLIDEAN_INTEGER_RING : thm := BIntegerRing.EUCLIDEAN_INTEGER_RING
def PID_INTEGER_RING : thm := BIntegerRing.PID_INTEGER_RING
def UFD_INTEGER_RING : thm := BIntegerRing.UFD_INTEGER_RING
def BEZOUT_INTEGER_RING : thm := BIntegerRing.BEZOUT_INTEGER_RING
def INTEGER_RING_OF_NUM : thm := BIntegerRing.INTEGER_RING_OF_NUM
def INTEGER_RING_OF_INT : thm := BIntegerRing.INTEGER_RING_OF_INT
def INTEGER_RING_CHAR : thm := BIntegerRing.INTEGER_RING_CHAR
def INTEGER_RING_COPRIME : thm := BIntegerRing.INTEGER_RING_COPRIME
def INTEGER_RING_ASSOCIATES : thm := BIntegerRing.INTEGER_RING_ASSOCIATES
def INTEGER_RING_GCD : thm := BIntegerRing.INTEGER_RING_GCD
def INTEGER_RING_IDEAL_GENERATED_SING : thm := BIntegerRing.INTEGER_RING_IDEAL_GENERATED_SING
def INTEGER_RING_COSET_IDEAL_GENERATED_SING : thm := BIntegerRing.INTEGER_RING_COSET_IDEAL_GENERATED_SING

-- IntegerModRing
def integer_mod_ring : thm := BIntegerModRing.integer_mod_ring
def INTEGER_MOD_RING : thm := BIntegerModRing.INTEGER_MOD_RING
def IN_INTEGER_MOD_RING_CARRIER : thm := BIntegerModRing.IN_INTEGER_MOD_RING_CARRIER
def INTEGER_MOD_RING_CARRIER_REM_EQ : thm := BIntegerModRing.INTEGER_MOD_RING_CARRIER_REM_EQ
def RING_CARRIER_INTEGER_MOD_RING : thm := BIntegerModRing.RING_CARRIER_INTEGER_MOD_RING
def INTEGER_MOD_RING_CARRIER_REM : thm := BIntegerModRing.INTEGER_MOD_RING_CARRIER_REM
def INTEGER_MOD_RING_TRIVIAL : thm := BIntegerModRing.INTEGER_MOD_RING_TRIVIAL
def INTEGER_MOD_RING_SUB : thm := BIntegerModRing.INTEGER_MOD_RING_SUB
def INTEGER_MOD_RING_POW : thm := BIntegerModRing.INTEGER_MOD_RING_POW
def INTEGER_MOD_RING_OF_NUM : thm := BIntegerModRing.INTEGER_MOD_RING_OF_NUM
def INTEGER_MOD_RING_OF_INT : thm := BIntegerModRing.INTEGER_MOD_RING_OF_INT
def INTEGER_MOD_RING_CLAUSES : thm := BIntegerModRing.INTEGER_MOD_RING_CLAUSES
def INTEGER_MOD_RING_CHAR : thm := BIntegerModRing.INTEGER_MOD_RING_CHAR
def INTEGER_MOD_RING_DIVIDES : thm := BIntegerModRing.INTEGER_MOD_RING_DIVIDES
def INTEGER_MOD_RING_ASSOCIATES : thm := BIntegerModRing.INTEGER_MOD_RING_ASSOCIATES
def INTEGER_MOD_RING_UNIT : thm := BIntegerModRing.INTEGER_MOD_RING_UNIT
def TRIVIAL_INTEGER_MOD_RING : thm := BIntegerModRing.TRIVIAL_INTEGER_MOD_RING
def FINITE_INTEGER_MOD_RING : thm := BIntegerModRing.FINITE_INTEGER_MOD_RING
def CARD_INTEGER_MOD_RING : thm := BIntegerModRing.CARD_INTEGER_MOD_RING
def FIELD_INTEGER_MOD_RING : thm := BIntegerModRing.FIELD_INTEGER_MOD_RING
def INTEGRAL_DOMAIN_INTEGER_MOD_RING : thm := BIntegerModRing.INTEGRAL_DOMAIN_INTEGER_MOD_RING
def RING_HOMOMORPHISM_INTEGER_MOD_RING_OF_INT : thm := BIntegerModRing.RING_HOMOMORPHISM_INTEGER_MOD_RING_OF_INT
def RING_MONOMORPHISM_INTEGER_MOD_RING_OF_INT : thm := BIntegerModRing.RING_MONOMORPHISM_INTEGER_MOD_RING_OF_INT
def RING_HOMOMORPHISM_FROM_INTEGER_MOD_RING : thm := BIntegerModRing.RING_HOMOMORPHISM_FROM_INTEGER_MOD_RING
def RING_MONOMORPHISM_FROM_INTEGER_MOD_RING : thm := BIntegerModRing.RING_MONOMORPHISM_FROM_INTEGER_MOD_RING
def RING_HOMOMORPHISM_INTEGER_MOD_RINGS : thm := BIntegerModRing.RING_HOMOMORPHISM_INTEGER_MOD_RINGS
def RING_HOMOMORPHISM_INTEGER_MOD_RINGS_POW : thm := BIntegerModRing.RING_HOMOMORPHISM_INTEGER_MOD_RINGS_POW
def RING_HOMOMORPHISM_PROD_INTEGER_MOD_RING : thm := BIntegerModRing.RING_HOMOMORPHISM_PROD_INTEGER_MOD_RING
def RING_ISOMORPHISM_PROD_INTEGER_MOD_RING : thm := BIntegerModRing.RING_ISOMORPHISM_PROD_INTEGER_MOD_RING
def ISOMORPHIC_PROD_INTEGER_MOD_RING : thm := BIntegerModRing.ISOMORPHIC_PROD_INTEGER_MOD_RING
def VNREGULAR_INTEGER_MOD_RING : thm := BIntegerModRing.VNREGULAR_INTEGER_MOD_RING
def INTEGER_QUOTIENT_RING_ISOMORPHIC_MOD : thm := BIntegerModRing.INTEGER_QUOTIENT_RING_ISOMORPHIC_MOD
def RING_ISOMORPHISM_PRIME_SUBRING : thm := BIntegerModRing.RING_ISOMORPHISM_PRIME_SUBRING
def ISOMORPHIC_PRIME_SUBRING : thm := BIntegerModRing.ISOMORPHIC_PRIME_SUBRING
def FIELD_PRIME_SUBRING : thm := BIntegerModRing.FIELD_PRIME_SUBRING

-- IntegerModConv
def RING_INV_INTEGER_MOD_RING : thm := BIntegerModConv.RING_INV_INTEGER_MOD_RING
def INTEGER_MOD_RING_RED_CONV : HolCore.Equal.ioconv := fun t => BIntegerModConv.INTEGER_MOD_RING_RED_CONV t

-- RealRing
def real_ring : thm := BRealRing.real_ring
def REAL_RING_CLAUSES : thm := BRealRing.REAL_RING_CLAUSES
def FIELD_REAL_RING : thm := BRealRing.FIELD_REAL_RING
def INTEGRAL_DOMAIN_REAL_RING : thm := BRealRing.INTEGRAL_DOMAIN_REAL_RING
def REAL_RING_OF_NUM : thm := BRealRing.REAL_RING_OF_NUM
def REAL_RING_OF_INT : thm := BRealRing.REAL_RING_OF_INT
def REAL_RING_CHAR : thm := BRealRing.REAL_RING_CHAR
def REAL_RING_SUB : thm := BRealRing.REAL_RING_SUB
def REAL_RING_INV : thm := BRealRing.REAL_RING_INV
def REAL_RING_DIV : thm := BRealRing.REAL_RING_DIV
def REAL_RING_POW : thm := BRealRing.REAL_RING_POW
def REAL_RING_SUM : thm := BRealRing.REAL_RING_SUM
def REAL_RING_PRODUCT : thm := BRealRing.REAL_RING_PRODUCT
def REAL_FIELD_CLAUSES : thm := BRealRing.REAL_FIELD_CLAUSES

-- Monomials
def monomial_1 : thm := BMonomials.monomial_1
def monomial_mul : thm := BMonomials.monomial_mul
def monomial_div : thm := BMonomials.monomial_div
def monomial_restrict : thm := BMonomials.monomial_restrict
def monomial_divides : thm := BMonomials.monomial_divides
def monomial_var : thm := BMonomials.monomial_var
def monomial_vars : thm := BMonomials.monomial_vars
def monomial_deg : thm := BMonomials.monomial_deg
def monomial : thm := BMonomials.monomial
def MONOMIAL_POINTWISE_TAC : HolCore.Tactics.tactic := fun g => BMonomials.MONOMIAL_POINTWISE_TAC g
def MONOMIAL_TAC : HolCore.Tactics.tactic := fun g => BMonomials.MONOMIAL_TAC g
def MONOMIAL_RULE : term → IO (Except String thm) := fun t => (BMonomials.MONOMIAL_RULE t).run
def FINITE_MONOMIAL_VARS : thm := BMonomials.FINITE_MONOMIAL_VARS
def FINITE_MONOMIAL_VARS_1 : thm := BMonomials.FINITE_MONOMIAL_VARS_1
def MONOMIAL_DEG : thm := BMonomials.MONOMIAL_DEG
def MONOMIAL_VAR_1 : thm := BMonomials.MONOMIAL_VAR_1
def MONOMIAL_VARS_1 : thm := BMonomials.MONOMIAL_VARS_1
def MONOMIAL_VARS_EQ_EMPTY : thm := BMonomials.MONOMIAL_VARS_EQ_EMPTY
def MONOMIAL_VARS_MUL : thm := BMonomials.MONOMIAL_VARS_MUL
def MONOMIAL_VARS_VAR : thm := BMonomials.MONOMIAL_VARS_VAR
def MONOMIAL_VARS_RESTRICT : thm := BMonomials.MONOMIAL_VARS_RESTRICT
def MONOMIAL_RESTRICT_EQ : thm := BMonomials.MONOMIAL_RESTRICT_EQ
def MONOMIAL_RESTRICT_REFL : thm := BMonomials.MONOMIAL_RESTRICT_REFL
def MONOMIAL_MONO : thm := BMonomials.MONOMIAL_MONO
def MONOMIAL_UNIV : thm := BMonomials.MONOMIAL_UNIV
def MONOMIAL_1 : thm := BMonomials.MONOMIAL_1
def MONOMIAL_MUL : thm := BMonomials.MONOMIAL_MUL
def MONOMIAL_RESTRICT_MUL : thm := BMonomials.MONOMIAL_RESTRICT_MUL
def MONOMIAL_MUL_RESTRICT : thm := BMonomials.MONOMIAL_MUL_RESTRICT
def MONOMIAL_DIVISOR : thm := BMonomials.MONOMIAL_DIVISOR
def MONOMIAL_VAR : thm := BMonomials.MONOMIAL_VAR
def MONOMIAL_RESTRICT : thm := BMonomials.MONOMIAL_RESTRICT
def MONOMIAL : thm := BMonomials.MONOMIAL
def MONOMIAL_UNIV_1 : thm := BMonomials.MONOMIAL_UNIV_1
def MONOMIAL_DEG_1 : thm := BMonomials.MONOMIAL_DEG_1
def MONOMIAL_DEG_VAR : thm := BMonomials.MONOMIAL_DEG_VAR
def MONOMIAL_DEG_EQ_0_ALT : thm := BMonomials.MONOMIAL_DEG_EQ_0_ALT
def MONOMIAL_DEG_EQ_0 : thm := BMonomials.MONOMIAL_DEG_EQ_0
def MONOMIAL_DIV_DIVIDES : thm := BMonomials.MONOMIAL_DIV_DIVIDES
def MONOMIAL_DIV : thm := BMonomials.MONOMIAL_DIV
def MONOMIAL_DIVIDES_1 : thm := BMonomials.MONOMIAL_DIVIDES_1
def MONOMIAL_DIVIDES_EXISTS : thm := BMonomials.MONOMIAL_DIVIDES_EXISTS
def MONOMIAL_VAR_DIVIDES_MUL : thm := BMonomials.MONOMIAL_VAR_DIVIDES_MUL
def MONOMIAL_MUL_EQ_VAR : thm := BMonomials.MONOMIAL_MUL_EQ_VAR
def MONOMIAL_DEG_MUL : thm := BMonomials.MONOMIAL_DEG_MUL
def MONOMIAL_DEG_LE : thm := BMonomials.MONOMIAL_DEG_LE
def MONOMIAL_VAR_EQ : thm := BMonomials.MONOMIAL_VAR_EQ
def MONOMIAL_MUL_LID : thm := BMonomials.MONOMIAL_MUL_LID
def MONOMIAL_MUL_RID : thm := BMonomials.MONOMIAL_MUL_RID
def MONOMIAL_MUL_SYM : thm := BMonomials.MONOMIAL_MUL_SYM
def MONOMIAL_MUL_ASSOC : thm := BMonomials.MONOMIAL_MUL_ASSOC
def MONOMIAL_MUL_AC : thm := BMonomials.MONOMIAL_MUL_AC
def MONOMIAL_MUL_EQ_1 : thm := BMonomials.MONOMIAL_MUL_EQ_1
def MONOMIAL_MUL_LCANCEL : thm := BMonomials.MONOMIAL_MUL_LCANCEL
def MONOMIAL_MUL_RCANCEL : thm := BMonomials.MONOMIAL_MUL_RCANCEL
def MONOMIAL_DIVIDES_REFL : thm := BMonomials.MONOMIAL_DIVIDES_REFL
def MONOMIAL_DIVIDES_TRANS : thm := BMonomials.MONOMIAL_DIVIDES_TRANS
def MONOMIAL_DIVIDES_ANTISYM : thm := BMonomials.MONOMIAL_DIVIDES_ANTISYM
def MONOMIAL_DIVIDES_LMUL : thm := BMonomials.MONOMIAL_DIVIDES_LMUL
def MONOMIAL_DIVIDES_RMUL : thm := BMonomials.MONOMIAL_DIVIDES_RMUL
def MONOMIAL_DIV_LMUL_EQ : thm := BMonomials.MONOMIAL_DIV_LMUL_EQ
def MONOMIAL_DIV_LMUL : thm := BMonomials.MONOMIAL_DIV_LMUL
def MONOMIAL_DIV_RMUL_EQ : thm := BMonomials.MONOMIAL_DIV_RMUL_EQ
def MONOMIAL_DIV_RMUL : thm := BMonomials.MONOMIAL_DIV_RMUL
def MONOMIAL_VAR_DIVIDES : thm := BMonomials.MONOMIAL_VAR_DIVIDES
def MONOMIAL_VARS_DIVISOR : thm := BMonomials.MONOMIAL_VARS_DIVISOR
def MONOMIAL_FINITE_DIVISORS : thm := BMonomials.MONOMIAL_FINITE_DIVISORS
def MONOMIAL_FINITE_DIVISORPAIRS : thm := BMonomials.MONOMIAL_FINITE_DIVISORPAIRS
def MONOMIAL_INDUCT : thm := BMonomials.MONOMIAL_INDUCT
def MONOMIAL_VARS_UNIVARIATE : thm := BMonomials.MONOMIAL_VARS_UNIVARIATE
def MONOMIAL_DEG_UNIVARIATE : thm := BMonomials.MONOMIAL_DEG_UNIVARIATE
def MONOMIAL_MUL_VAR_ONE : thm := BMonomials.MONOMIAL_MUL_VAR_ONE
def MONOMIAL_DEG_ONE : thm := BMonomials.MONOMIAL_DEG_ONE

-- PowerSeries
def ring_powerseries : thm := BPowerSeries.ring_powerseries
def ring_polynomial : thm := BPowerSeries.ring_polynomial
def RING_POLYNOMIAL_IMP_POWERSERIES : thm := BPowerSeries.RING_POLYNOMIAL_IMP_POWERSERIES
def poly_vars : thm := BPowerSeries.poly_vars
def poly_const : thm := BPowerSeries.poly_const
def poly_0 : thm := BPowerSeries.poly_0
def poly_1 : thm := BPowerSeries.poly_1
def poly_neg : thm := BPowerSeries.poly_neg
def poly_add : thm := BPowerSeries.poly_add
def poly_sub : thm := BPowerSeries.poly_sub
def poly_mul : thm := BPowerSeries.poly_mul
def poly_var : thm := BPowerSeries.poly_var
def POLY_SUB : thm := BPowerSeries.POLY_SUB
def RING_POWERSERIES_MONOMIAL : thm := BPowerSeries.RING_POWERSERIES_MONOMIAL
def RING_POLYNOMIAL_MONOMIAL : thm := BPowerSeries.RING_POLYNOMIAL_MONOMIAL
def POLY_0 : thm := BPowerSeries.POLY_0
def POLY_CONST_0 : thm := BPowerSeries.POLY_CONST_0
def POLY_CONST_1 : thm := BPowerSeries.POLY_CONST_1
def RING_POWERSERIES_CONST : thm := BPowerSeries.RING_POWERSERIES_CONST
def RING_POWERSERIES_VAR : thm := BPowerSeries.RING_POWERSERIES_VAR
def RING_POWERSERIES_0 : thm := BPowerSeries.RING_POWERSERIES_0
def RING_POWERSERIES_1 : thm := BPowerSeries.RING_POWERSERIES_1
def POLY_VAR_MONOMIAL_1 : thm := BPowerSeries.POLY_VAR_MONOMIAL_1
def RING_POWERSERIES_NEG : thm := BPowerSeries.RING_POWERSERIES_NEG
def RING_POWERSERIES_ADD : thm := BPowerSeries.RING_POWERSERIES_ADD
def RING_POWERSERIES_SUB : thm := BPowerSeries.RING_POWERSERIES_SUB
def RING_POWERSERIES_MUL : thm := BPowerSeries.RING_POWERSERIES_MUL
def RING_POLYNOMIAL_CONST : thm := BPowerSeries.RING_POLYNOMIAL_CONST
def RING_POLYNOMIAL_VAR : thm := BPowerSeries.RING_POLYNOMIAL_VAR
def POLY_VAR_EQ_CONST : thm := BPowerSeries.POLY_VAR_EQ_CONST
def RING_POLYNOMIAL_0 : thm := BPowerSeries.RING_POLYNOMIAL_0
def RING_POLYNOMIAL_1 : thm := BPowerSeries.RING_POLYNOMIAL_1
def RING_POLYNOMIAL_NEG : thm := BPowerSeries.RING_POLYNOMIAL_NEG
def RING_POLYNOMIAL_ADD : thm := BPowerSeries.RING_POLYNOMIAL_ADD
def RING_POLYNOMIAL_SUB : thm := BPowerSeries.RING_POLYNOMIAL_SUB
def RING_POLYNOMIAL_MUL : thm := BPowerSeries.RING_POLYNOMIAL_MUL
def POLY_ADD_SYM : thm := BPowerSeries.POLY_ADD_SYM
def POLY_ADD_ASSOC : thm := BPowerSeries.POLY_ADD_ASSOC
def POLY_ADD_LZERO : thm := BPowerSeries.POLY_ADD_LZERO
def POLY_ADD_RZERO : thm := BPowerSeries.POLY_ADD_RZERO
def POLY_ADD_LNEG : thm := BPowerSeries.POLY_ADD_LNEG
def POLY_MUL_SYM : thm := BPowerSeries.POLY_MUL_SYM
def POLY_ADD_LDISTRIB : thm := BPowerSeries.POLY_ADD_LDISTRIB
def POLY_MUL_LID : thm := BPowerSeries.POLY_MUL_LID
def POLY_MUL_RID : thm := BPowerSeries.POLY_MUL_RID
def POLY_MUL_ASSOC : thm := BPowerSeries.POLY_MUL_ASSOC
def POWSER_MUL_0 : thm := BPowerSeries.POWSER_MUL_0
def POLY_MUL_0 : thm := BPowerSeries.POLY_MUL_0
def POWSER_MUL_MONOMIAL_1 : thm := BPowerSeries.POWSER_MUL_MONOMIAL_1
def POLY_MUL_MONOMIAL_1 : thm := BPowerSeries.POLY_MUL_MONOMIAL_1
def POWSER_MUL_CONST : thm := BPowerSeries.POWSER_MUL_CONST
def POLY_MUL_CONST : thm := BPowerSeries.POLY_MUL_CONST
def POWSER_VAR_MUL : thm := BPowerSeries.POWSER_VAR_MUL
def POWSER_MUL_VAR : thm := BPowerSeries.POWSER_MUL_VAR
def POLY_VAR_MUL : thm := BPowerSeries.POLY_VAR_MUL
def POLY_MUL_VAR : thm := BPowerSeries.POLY_MUL_VAR
def POLY_VARS_CONST : thm := BPowerSeries.POLY_VARS_CONST
def POLY_VARS_0 : thm := BPowerSeries.POLY_VARS_0
def POLY_VARS_1 : thm := BPowerSeries.POLY_VARS_1
def POLY_VARS_VAR : thm := BPowerSeries.POLY_VARS_VAR
def POLY_VARS_NEG : thm := BPowerSeries.POLY_VARS_NEG
def POLY_VARS_ADD : thm := BPowerSeries.POLY_VARS_ADD
def POLY_VARS_MUL : thm := BPowerSeries.POLY_VARS_MUL
def FINITE_POLYNOMIAL_VARS : thm := BPowerSeries.FINITE_POLYNOMIAL_VARS

-- PolyRings
def powser_ring : thm := BPolyRings.powser_ring
def poly_ring : thm := BPolyRings.poly_ring
def POWSER_RING : thm := BPolyRings.POWSER_RING
def POLY_RING_SUBRING_OF_POWSER_RING : thm := BPolyRings.POLY_RING_SUBRING_OF_POWSER_RING
def POLY_RING_AS_SUBRING : thm := BPolyRings.POLY_RING_AS_SUBRING
def POLY_RING_AS_SUBRING_ALT : thm := BPolyRings.POLY_RING_AS_SUBRING_ALT
def POLY_RING_AS_SUBRING_FINITE : thm := BPolyRings.POLY_RING_AS_SUBRING_FINITE
def POLY_CARRIER_SUBRING_OF_POWSER_RING : thm := BPolyRings.POLY_CARRIER_SUBRING_OF_POWSER_RING
def RING_MONOMORPHISM_POLY_POWSER : thm := BPolyRings.RING_MONOMORPHISM_POLY_POWSER
def POLY_RING : thm := BPolyRings.POLY_RING
def POLY_IN_POWSER_RING : thm := BPolyRings.POLY_IN_POWSER_RING
def poly_pow : thm := BPolyRings.poly_pow
def POLY_POW : thm := BPolyRings.POLY_POW
def POLY_POW_ALT : thm := BPolyRings.POLY_POW_ALT
def RING_POWERSERIES_POW : thm := BPolyRings.RING_POWERSERIES_POW
def RING_POLYNOMIAL_POW : thm := BPolyRings.RING_POLYNOMIAL_POW
def POLY_POW_1 : thm := BPolyRings.POLY_POW_1
def POLY_POW_0 : thm := BPolyRings.POLY_POW_0
def POLY_VARS_POW : thm := BPolyRings.POLY_VARS_POW
def POWSER_RING_CLAUSES : thm := BPolyRings.POWSER_RING_CLAUSES
def POWSER_CLAUSES : thm := BPolyRings.POWSER_CLAUSES
def POLY_RING_CLAUSES : thm := BPolyRings.POLY_RING_CLAUSES
def POLY_CLAUSES : thm := BPolyRings.POLY_CLAUSES
def POLY_SUBRING_GENERATED_CLAUSES : thm := BPolyRings.POLY_SUBRING_GENERATED_CLAUSES
def POLY_CONST_SUBRING_GENERATED : thm := BPolyRings.POLY_CONST_SUBRING_GENERATED
def POLY_VAR_SUBRING_GENERATED : thm := BPolyRings.POLY_VAR_SUBRING_GENERATED
def POWSER_MONOMIAL_IN_CARRIER : thm := BPolyRings.POWSER_MONOMIAL_IN_CARRIER
def POLY_MONOMIAL_IN_CARRIER : thm := BPolyRings.POLY_MONOMIAL_IN_CARRIER
def RING_POLYNOMIAL : thm := BPolyRings.RING_POLYNOMIAL
def RING_POWERSERIES : thm := BPolyRings.RING_POWERSERIES
def IN_POLY_RING_CARRIER : thm := BPolyRings.IN_POLY_RING_CARRIER
def RING_POLYNOMIAL_CARRIER_GEN : thm := BPolyRings.RING_POLYNOMIAL_CARRIER_GEN
def RING_POLYNOMIAL_CARRIER : thm := BPolyRings.RING_POLYNOMIAL_CARRIER
def POLY_MONOMIALS_FINITE : thm := BPolyRings.POLY_MONOMIALS_FINITE
def FINITE_POLY_VARS : thm := BPolyRings.FINITE_POLY_VARS
def RING_CARRIER_POLY_RING_FINITE : thm := BPolyRings.RING_CARRIER_POLY_RING_FINITE
def POWSER_RING_MONO : thm := BPolyRings.POWSER_RING_MONO
def POLY_RING_MONO : thm := BPolyRings.POLY_RING_MONO
def POLY_RING_POLY_VARS : thm := BPolyRings.POLY_RING_POLY_VARS
def POLY_RING_IN_POLY_VARS : thm := BPolyRings.POLY_RING_IN_POLY_VARS
def POLY_RING_IN_FINITE_VARIABLES : thm := BPolyRings.POLY_RING_IN_FINITE_VARIABLES
def IN_POLY_RING_SUBRING_GENERATED_FINITARY : thm := BPolyRings.IN_POLY_RING_SUBRING_GENERATED_FINITARY
def POLY_VAR : thm := BPolyRings.POLY_VAR
def POLY_VAR_UNIV : thm := BPolyRings.POLY_VAR_UNIV
def POLY_CONST : thm := BPolyRings.POLY_CONST
def POWSER_VAR : thm := BPolyRings.POWSER_VAR
def POWSER_VAR_UNIV : thm := BPolyRings.POWSER_VAR_UNIV
def POWSER_CONST : thm := BPolyRings.POWSER_CONST
def POLY_CONST_NEG : thm := BPolyRings.POLY_CONST_NEG
def POLY_CONST_ADD : thm := BPolyRings.POLY_CONST_ADD
def POLY_CONST_MUL : thm := BPolyRings.POLY_CONST_MUL
def RING_OF_NUM_POWSER_RING : thm := BPolyRings.RING_OF_NUM_POWSER_RING
def RING_OF_NUM_POLY_RING : thm := BPolyRings.RING_OF_NUM_POLY_RING
def POLY_CONST_OF_NUM : thm := BPolyRings.POLY_CONST_OF_NUM
def POLY_CONST_EQ : thm := BPolyRings.POLY_CONST_EQ
def POLY_CONST_EQ_0 : thm := BPolyRings.POLY_CONST_EQ_0
def POLY_CONST_EQ_1 : thm := BPolyRings.POLY_CONST_EQ_1
def POWSER_VAR_MUL_EQ_0 : thm := BPolyRings.POWSER_VAR_MUL_EQ_0
def POWSER_VARPOW_MUL_EQ_0 : thm := BPolyRings.POWSER_VARPOW_MUL_EQ_0
def RING_HOMOMORPHISM_POLY_CONST : thm := BPolyRings.RING_HOMOMORPHISM_POLY_CONST
def RING_MONOMORPHISM_POLY_CONST : thm := BPolyRings.RING_MONOMORPHISM_POLY_CONST
def RING_HOMOMORPHISM_POWSER_CONST : thm := BPolyRings.RING_HOMOMORPHISM_POWSER_CONST
def RING_MONOMORPHISM_POWSER_CONST : thm := BPolyRings.RING_MONOMORPHISM_POWSER_CONST
def RING_HOMOMORPHISM_MONOMIAL_1 : thm := BPolyRings.RING_HOMOMORPHISM_MONOMIAL_1
def POWSER_SUM : thm := BPolyRings.POWSER_SUM
def POLY_SUM : thm := BPolyRings.POLY_SUM
def POLY_RING_VAR_POW : thm := BPolyRings.POLY_RING_VAR_POW
def POLY_RING_PRODUCT_VAR_POW : thm := BPolyRings.POLY_RING_PRODUCT_VAR_POW
def POLY_RING_PRODUCT_VAR : thm := BPolyRings.POLY_RING_PRODUCT_VAR
def POLY_RING_EXPAND : thm := BPolyRings.POLY_RING_EXPAND
def POLY_RING_INDUCT : thm := BPolyRings.POLY_RING_INDUCT
def POLY_RING_INDUCT_STRONG : thm := BPolyRings.POLY_RING_INDUCT_STRONG
def POLY_RING_HOMOMORPHISM_UNIQUE : thm := BPolyRings.POLY_RING_HOMOMORPHISM_UNIQUE
def TRIVIAL_POWSER_RING : thm := BPolyRings.TRIVIAL_POWSER_RING
def TRIVIAL_POLY_RING : thm := BPolyRings.TRIVIAL_POLY_RING
def TRIVIAL_RING_POWSER_0 : thm := BPolyRings.TRIVIAL_RING_POWSER_0
def TRIVIAL_RING_POLY_0 : thm := BPolyRings.TRIVIAL_RING_POLY_0
def RING_CARRIER_POWSER_RING : thm := BPolyRings.RING_CARRIER_POWSER_RING
def POWSER_MONOMIALS : thm := BPolyRings.POWSER_MONOMIALS
def RING_CARRIER_POLY_RING : thm := BPolyRings.RING_CARRIER_POLY_RING
def POLY_SUBRING_GENERATED_MUL : thm := BPolyRings.POLY_SUBRING_GENERATED_MUL
def POLY_MONOMIALS : thm := BPolyRings.POLY_MONOMIALS
def POLY_MONOMIALS_ALT : thm := BPolyRings.POLY_MONOMIALS_ALT
def POWSER_RING_EQ : thm := BPolyRings.POWSER_RING_EQ
def POWSER_RING_EQ_IMP : thm := BPolyRings.POWSER_RING_EQ_IMP
def POLY_RING_EQ : thm := BPolyRings.POLY_RING_EQ
def POLY_RING_EQ_IMP : thm := BPolyRings.POLY_RING_EQ_IMP

-- HomExtend
def poly_extend : thm := BHomExtend.poly_extend
def POLY_EXTEND_FROM_SUBRING_GENERATED : thm := BHomExtend.POLY_EXTEND_FROM_SUBRING_GENERATED
def POLY_EXTEND : thm := BHomExtend.POLY_EXTEND
def POLY_EXTEND_SUPERSET : thm := BHomExtend.POLY_EXTEND_SUPERSET
def POLY_EXTEND_POLYNOMIAL : thm := BHomExtend.POLY_EXTEND_POLYNOMIAL
def POLY_EXTEND_CONST : thm := BHomExtend.POLY_EXTEND_CONST
def POLY_EXTEND_0 : thm := BHomExtend.POLY_EXTEND_0
def POLY_EXTEND_1 : thm := BHomExtend.POLY_EXTEND_1
def POLY_EXTEND_VAR : thm := BHomExtend.POLY_EXTEND_VAR
def POLY_EXTEND_NEG : thm := BHomExtend.POLY_EXTEND_NEG
def POLY_EXTEND_ADD : thm := BHomExtend.POLY_EXTEND_ADD
def POLY_EXTEND_SUB : thm := BHomExtend.POLY_EXTEND_SUB
def POLY_EXTEND_MUL : thm := BHomExtend.POLY_EXTEND_MUL
def POLY_EXTEND_POW : thm := BHomExtend.POLY_EXTEND_POW
def POLY_EXTEND_VARPOW : thm := BHomExtend.POLY_EXTEND_VARPOW
def POLY_EXTEND_CONST_VARPOW : thm := BHomExtend.POLY_EXTEND_CONST_VARPOW
def RING_HOMOMORPHISM_POLY_EXTEND : thm := BHomExtend.RING_HOMOMORPHISM_POLY_EXTEND
def POLY_EXTEND_RING_SUM : thm := BHomExtend.POLY_EXTEND_RING_SUM
def POLY_EXTEND_RING_PRODUCT : thm := BHomExtend.POLY_EXTEND_RING_PRODUCT
def POLY_EXTEND_UNIQUE : thm := BHomExtend.POLY_EXTEND_UNIQUE
def POLY_EXTEND_EQ : thm := BHomExtend.POLY_EXTEND_EQ
def POLY_EXTEND_ID : thm := BHomExtend.POLY_EXTEND_ID
def POLY_EXTEND_COMPOSE : thm := BHomExtend.POLY_EXTEND_COMPOSE
def POLY_EXTEND_COMPOSE_COEFFS : thm := BHomExtend.POLY_EXTEND_COMPOSE_COEFFS
def POLY_EXTEND_HOMOMORPHIC_IMAGE : thm := BHomExtend.POLY_EXTEND_HOMOMORPHIC_IMAGE
def POWSER_EXTEND_AT_0 : thm := BHomExtend.POWSER_EXTEND_AT_0
def POLY_EXTEND_AT_0 : thm := BHomExtend.POLY_EXTEND_AT_0
def RING_HOMOMORPHISM_POWSER_EXTEND_AT_0 : thm := BHomExtend.RING_HOMOMORPHISM_POWSER_EXTEND_AT_0
def POLY_SUBRING_GENERATED : thm := BHomExtend.POLY_SUBRING_GENERATED
def RING_HOMOMORPHISMS_EQ_FROM_POLY_RING : thm := BHomExtend.RING_HOMOMORPHISMS_EQ_FROM_POLY_RING
def POLY_SUBRING_GENERATED_1 : thm := BHomExtend.POLY_SUBRING_GENERATED_1
def IMAGE_POLY_EXTEND : thm := BHomExtend.IMAGE_POLY_EXTEND
def IMAGE_POLY_EXTEND_1 : thm := BHomExtend.IMAGE_POLY_EXTEND_1
def POLY_EXTEND_INTO_SUBRING_GENERATED : thm := BHomExtend.POLY_EXTEND_INTO_SUBRING_GENERATED

-- NatIso
def RING_ISOMORPHISM_POWSER_RING_TRIVIAL : thm := BNatIso.RING_ISOMORPHISM_POWSER_RING_TRIVIAL
def RING_ISOMORPHISM_POLY_RING_TRIVIAL : thm := BNatIso.RING_ISOMORPHISM_POLY_RING_TRIVIAL
def ISOMORPHIC_POWSER_RING_TRIVIAL : thm := BNatIso.ISOMORPHIC_POWSER_RING_TRIVIAL
def ISOMORPHIC_POLY_RING_TRIVIAL : thm := BNatIso.ISOMORPHIC_POLY_RING_TRIVIAL
def RING_ISOMORPHISMS_POWSER_RINGS : thm := BNatIso.RING_ISOMORPHISMS_POWSER_RINGS
def ISOMORPHIC_POWSER_RINGS : thm := BNatIso.ISOMORPHIC_POWSER_RINGS
def RING_ISOMORPHISMS_POLY_RINGS : thm := BNatIso.RING_ISOMORPHISMS_POLY_RINGS
def ISOMORPHIC_POLY_RINGS : thm := BNatIso.ISOMORPHIC_POLY_RINGS
def RING_ISOMORPHISMS_POWSER_POWSER_RING : thm := BNatIso.RING_ISOMORPHISMS_POWSER_POWSER_RING
def ISOMORPHIC_RING_POWSER_POWSER : thm := BNatIso.ISOMORPHIC_RING_POWSER_POWSER
def ISOMORPHIC_RING_POWSER_POWSER_GEN : thm := BNatIso.ISOMORPHIC_RING_POWSER_POWSER_GEN
def RING_CARRIER_POWSER_SUBRING_GENERATED : thm := BNatIso.RING_CARRIER_POWSER_SUBRING_GENERATED
def RING_CARRIER_POLY_SUBRING_GENERATED : thm := BNatIso.RING_CARRIER_POLY_SUBRING_GENERATED
def RING_CARRIER_POWSER_SUBRING_GENERATED_MONO : thm := BNatIso.RING_CARRIER_POWSER_SUBRING_GENERATED_MONO
def RING_CARRIER_POLY_SUBRING_GENERATED_MONO : thm := BNatIso.RING_CARRIER_POLY_SUBRING_GENERATED_MONO
def RING_CARRIER_POWSER_SUBRING_GENERATED_SUBSET : thm := BNatIso.RING_CARRIER_POWSER_SUBRING_GENERATED_SUBSET
def RING_CARRIER_POLY_SUBRING_GENERATED_SUBSET : thm := BNatIso.RING_CARRIER_POLY_SUBRING_GENERATED_SUBSET
def SUBRING_POWSER_INTO_SUBRING : thm := BNatIso.SUBRING_POWSER_INTO_SUBRING
def SUBRING_POLY_INTO_SUBRING : thm := BNatIso.SUBRING_POLY_INTO_SUBRING
def RING_ISOMORPHISMS_POWSER_SUBRING_GENERATED : thm := BNatIso.RING_ISOMORPHISMS_POWSER_SUBRING_GENERATED
def ISOMORPHIC_RINGS_POWSER_SUBRING_GENERATED : thm := BNatIso.ISOMORPHIC_RINGS_POWSER_SUBRING_GENERATED
def RING_ISOMORPHISMS_POLY_SUBRING_GENERATED : thm := BNatIso.RING_ISOMORPHISMS_POLY_SUBRING_GENERATED
def ISOMORPHIC_RINGS_POLY_SUBRING_GENERATED : thm := BNatIso.ISOMORPHIC_RINGS_POLY_SUBRING_GENERATED
def RING_ISOMORPHISMS_POLY_POLY_RING : thm := BNatIso.RING_ISOMORPHISMS_POLY_POLY_RING
def ISOMORPHIC_RING_POLY_POLY : thm := BNatIso.ISOMORPHIC_RING_POLY_POLY
def ISOMORPHIC_RING_POLY_POLY_GEN : thm := BNatIso.ISOMORPHIC_RING_POLY_POLY_GEN
def POLY_EXTEND_EXTEND : thm := BNatIso.POLY_EXTEND_EXTEND

-- Renaming
def poly_reindex : thm := BRenaming.poly_reindex
def RING_ISOMORPHISMS_POWSER_REINDEX : thm := BRenaming.RING_ISOMORPHISMS_POWSER_REINDEX
def RING_ISOMORPHISM_POWSER_REINDEX : thm := BRenaming.RING_ISOMORPHISM_POWSER_REINDEX
def RING_ISOMORPHISMS_POLY_REINDEX : thm := BRenaming.RING_ISOMORPHISMS_POLY_REINDEX
def POLY_VARS_REINDEX : thm := BRenaming.POLY_VARS_REINDEX
def RING_ISOMORPHISM_POLY_REINDEX : thm := BRenaming.RING_ISOMORPHISM_POLY_REINDEX
def POLY_REINDEX_CONST : thm := BRenaming.POLY_REINDEX_CONST
def POLY_REINDEX_VAR : thm := BRenaming.POLY_REINDEX_VAR
def MONOMIALS_POLY_REINDEX : thm := BRenaming.MONOMIALS_POLY_REINDEX
def POLY_EXTEND_REINDEX : thm := BRenaming.POLY_EXTEND_REINDEX
def RING_POWERSERIES_REINDEX : thm := BRenaming.RING_POWERSERIES_REINDEX
def POLY_RING_HOMOMORPHISM_I : thm := BRenaming.POLY_RING_HOMOMORPHISM_I
def POLY_CONST_DIVIDES_COEFFS : thm := BRenaming.POLY_CONST_DIVIDES_COEFFS
def POLY_CONST_DIVIDES_COEFFS_REV : thm := BRenaming.POLY_CONST_DIVIDES_COEFFS_REV
def POLY_CONST_DIVIDES_COEFFS_EQ : thm := BRenaming.POLY_CONST_DIVIDES_COEFFS_EQ
def POLY_CONST_DIVIDES_CONST : thm := BRenaming.POLY_CONST_DIVIDES_CONST

-- MonomialOrders
def POSET_MONOMIAL_DIVIDES : thm := BMonomialOrders.POSET_MONOMIAL_DIVIDES
def FLD_MONOMIAL_DIVIDES : thm := BMonomialOrders.FLD_MONOMIAL_DIVIDES
def COMPATIBLE_MONOMIAL_ORDER : thm := BMonomialOrders.COMPATIBLE_MONOMIAL_ORDER
def WQOSET_COMPATIBLE_MONOMIAL_ORDER : thm := BMonomialOrders.WQOSET_COMPATIBLE_MONOMIAL_ORDER
def WF_COMPATIBLE_MONOMIAL_ORDER : thm := BMonomialOrders.WF_COMPATIBLE_MONOMIAL_ORDER
def WOSET_COMPATIBLE_MONOMIAL_ORDER : thm := BMonomialOrders.WOSET_COMPATIBLE_MONOMIAL_ORDER
def monomial_le : thm := BMonomialOrders.monomial_le
def monomial_lt : thm := BMonomialOrders.monomial_lt
def PROPERLY_MONOMIAL_LE : thm := BMonomialOrders.PROPERLY_MONOMIAL_LE
def MONOMIAL_LE_MONO : thm := BMonomialOrders.MONOMIAL_LE_MONO
def MONOMIAL_LT_MONO : thm := BMonomialOrders.MONOMIAL_LT_MONO
def MONOMIAL_LE_PROPERLY : thm := BMonomialOrders.MONOMIAL_LE_PROPERLY
def MONOMIAL_LT_PROPERLY : thm := BMonomialOrders.MONOMIAL_LT_PROPERLY
def MONOMIAL_LE_IMPROPERLY : thm := BMonomialOrders.MONOMIAL_LE_IMPROPERLY
def MONOMIAL_LT_IMPROPERLY : thm := BMonomialOrders.MONOMIAL_LT_IMPROPERLY
def MONOMIAL_LE_REFL : thm := BMonomialOrders.MONOMIAL_LE_REFL
def MONOMIAL_LT_REFL : thm := BMonomialOrders.MONOMIAL_LT_REFL
def MONOMIAL_LT_IMP_LE : thm := BMonomialOrders.MONOMIAL_LT_IMP_LE
def MONOMIAL_LE_LT : thm := BMonomialOrders.MONOMIAL_LE_LT
def MONOMIAL_LE_TRANS : thm := BMonomialOrders.MONOMIAL_LE_TRANS
def QOSET_MONOMIAL_LE : thm := BMonomialOrders.QOSET_MONOMIAL_LE
def FLD_MONOMIAL_LE : thm := BMonomialOrders.FLD_MONOMIAL_LE
def MONOMIAL_LE_LMUL : thm := BMonomialOrders.MONOMIAL_LE_LMUL
def MONOMIAL_LE_RMUL : thm := BMonomialOrders.MONOMIAL_LE_RMUL
def MONOMIAL_LT_LMUL : thm := BMonomialOrders.MONOMIAL_LT_LMUL
def MONOMIAL_LT_RMUL : thm := BMonomialOrders.MONOMIAL_LT_RMUL
def MONOMIAL_LE_MUL2 : thm := BMonomialOrders.MONOMIAL_LE_MUL2
def MONOMIAL_LE_DIVISOR : thm := BMonomialOrders.MONOMIAL_LE_DIVISOR
def MONOMIAL_GE_1 : thm := BMonomialOrders.MONOMIAL_GE_1
def MONOMIAL_LE_VARS : thm := BMonomialOrders.MONOMIAL_LE_VARS
def MONOMIAL_LT_VARS : thm := BMonomialOrders.MONOMIAL_LT_VARS
def MONOMIAL_LE_POSET : thm := BMonomialOrders.MONOMIAL_LE_POSET
def MONOMIAL_LE_ANTISYM : thm := BMonomialOrders.MONOMIAL_LE_ANTISYM
def MONOMIAL_LET_ANTISYM : thm := BMonomialOrders.MONOMIAL_LET_ANTISYM
def MONOMIAL_LTE_ANTISYM : thm := BMonomialOrders.MONOMIAL_LTE_ANTISYM
def MONOMIAL_LT_ANTISYM : thm := BMonomialOrders.MONOMIAL_LT_ANTISYM
def MONOMIAL_LET_TRANS : thm := BMonomialOrders.MONOMIAL_LET_TRANS
def MONOMIAL_LTE_TRANS : thm := BMonomialOrders.MONOMIAL_LTE_TRANS
def MONOMIAL_LT_TRANS : thm := BMonomialOrders.MONOMIAL_LT_TRANS
def MONOMIAL_LET_MUL2 : thm := BMonomialOrders.MONOMIAL_LET_MUL2
def MONOMIAL_LTE_MUL2 : thm := BMonomialOrders.MONOMIAL_LTE_MUL2
def MONOMIAL_LT_MUL2 : thm := BMonomialOrders.MONOMIAL_LT_MUL2
def POSET_MONOMIAL_LE : thm := BMonomialOrders.POSET_MONOMIAL_LE
def MONOMIAL_LE_VARS_EQ : thm := BMonomialOrders.MONOMIAL_LE_VARS_EQ
def MONOMIAL_LT_VARS_EQ : thm := BMonomialOrders.MONOMIAL_LT_VARS_EQ
def MONOMIAL_LT_TOSET : thm := BMonomialOrders.MONOMIAL_LT_TOSET
def MONOMIAL_LE_TOSET : thm := BMonomialOrders.MONOMIAL_LE_TOSET
def TOSET_MONOMIAL_LE : thm := BMonomialOrders.TOSET_MONOMIAL_LE
def WF_MONOMIAL_LT : thm := BMonomialOrders.WF_MONOMIAL_LT
def WOSET_MONOMIAL_LE : thm := BMonomialOrders.WOSET_MONOMIAL_LE

-- OneCoeff
def EXISTS_FUN_FROM_1 : thm := BOneCoeff.EXISTS_FUN_FROM_1
def FORALL_FUN_FROM_1 : thm := BOneCoeff.FORALL_FUN_FROM_1
def LAMBDA_1_EQ : thm := BOneCoeff.LAMBDA_1_EQ
def FUN_ONE_NUM_EQ : thm := BOneCoeff.FUN_ONE_NUM_EQ
def FUN_ONE_EQ_ONE : thm := BOneCoeff.FUN_ONE_EQ_ONE
def FINITE_FUN_FROM_1 : thm := BOneCoeff.FINITE_FUN_FROM_1
def MONOMIAL_DIVISORS_1 : thm := BOneCoeff.MONOMIAL_DIVISORS_1
def coeff : thm := BOneCoeff.coeff
def COEFF : thm := BOneCoeff.COEFF
def COEFF_0 : thm := BOneCoeff.COEFF_0
def FUN_EQ_COEFF : thm := BOneCoeff.FUN_EQ_COEFF
def RING_POLYNOMIAL_POWERSERIES_COEFF : thm := BOneCoeff.RING_POLYNOMIAL_POWERSERIES_COEFF
def RING_POWERSERIES_COEFF : thm := BOneCoeff.RING_POWERSERIES_COEFF
def COEFF_IN_CARRIER : thm := BOneCoeff.COEFF_IN_CARRIER
def COEFF_IN_CARRIER_ALT : thm := BOneCoeff.COEFF_IN_CARRIER_ALT
def RING_POLYNOMIAL_COEFF : thm := BOneCoeff.RING_POLYNOMIAL_COEFF
def COEFF_COMPOSE : thm := BOneCoeff.COEFF_COMPOSE
def COEFF_POLY_CONST : thm := BOneCoeff.COEFF_POLY_CONST
def COEFF_POLY_0 : thm := BOneCoeff.COEFF_POLY_0
def COEFF_POLY_1 : thm := BOneCoeff.COEFF_POLY_1
def COEFF_POLY_VAR : thm := BOneCoeff.COEFF_POLY_VAR
def COEFF_POLY_NEG : thm := BOneCoeff.COEFF_POLY_NEG
def COEFF_POLY_ADD : thm := BOneCoeff.COEFF_POLY_ADD
def COEFF_POLY_SUB : thm := BOneCoeff.COEFF_POLY_SUB
def COEFF_POLY_MUL_ALT : thm := BOneCoeff.COEFF_POLY_MUL_ALT
def COEFF_POLY_MUL : thm := BOneCoeff.COEFF_POLY_MUL
def COEFF_POLY_VARPOW : thm := BOneCoeff.COEFF_POLY_VARPOW
def COEFF_POLY_LMUL : thm := BOneCoeff.COEFF_POLY_LMUL
def COEFF_POLY_CONST_MUL_VAR_POW : thm := BOneCoeff.COEFF_POLY_CONST_MUL_VAR_POW
def COEFF_POLY_RMUL : thm := BOneCoeff.COEFF_POLY_RMUL
def COEFF_POLY_VAR_MUL : thm := BOneCoeff.COEFF_POLY_VAR_MUL
def COEFF_POLY_CONST_MUL_VAR_MUL : thm := BOneCoeff.COEFF_POLY_CONST_MUL_VAR_MUL
def COEFF_POLY_MUL_VAR : thm := BOneCoeff.COEFF_POLY_MUL_VAR
def COEFF_POLY_VARPOW_MUL : thm := BOneCoeff.COEFF_POLY_VARPOW_MUL
def COEFF_POLY_MUL_VARPOW : thm := BOneCoeff.COEFF_POLY_MUL_VARPOW
def POLY_MUL_UNIVARIATE : thm := BOneCoeff.POLY_MUL_UNIVARIATE
def RING_POLYNOMIAL_SUBRING_COEFF : thm := BOneCoeff.RING_POLYNOMIAL_SUBRING_COEFF
def FINITE_COEFF_SUPPORT : thm := BOneCoeff.FINITE_COEFF_SUPPORT
def RING_POLYNOMIAL_COEFF_BOUND : thm := BOneCoeff.RING_POLYNOMIAL_COEFF_BOUND
def RING_POLYNOMIAL_COEFF_ZERO_FROM : thm := BOneCoeff.RING_POLYNOMIAL_COEFF_ZERO_FROM

-- Degree
def poly_deg : thm := BDegree.poly_deg
def POLY_DEG_SUBRING_GENERATED : thm := BDegree.POLY_DEG_SUBRING_GENERATED
def POLY_DEG_CONST : thm := BDegree.POLY_DEG_CONST
def POLY_DEG_0 : thm := BDegree.POLY_DEG_0
def POLY_NONCONSTANT_IMP_NZ : thm := BDegree.POLY_NONCONSTANT_IMP_NZ
def POLY_DEG_1 : thm := BDegree.POLY_DEG_1
def POLY_DEG_LE_EQ : thm := BDegree.POLY_DEG_LE_EQ
def POLY_DEG_LE : thm := BDegree.POLY_DEG_LE
def MONOMIAL_DEG_LE_POLY_DEG : thm := BDegree.MONOMIAL_DEG_LE_POLY_DEG
def POLY_DEG_GE_EQ : thm := BDegree.POLY_DEG_GE_EQ
def POLY_DEG_GE : thm := BDegree.POLY_DEG_GE
def COEFF_ABOVE_DEG : thm := BDegree.COEFF_ABOVE_DEG
def FINITE_POLY_DEG_LE : thm := BDegree.FINITE_POLY_DEG_LE
def POLY_DEG_MONOMIAL_EXISTS : thm := BDegree.POLY_DEG_MONOMIAL_EXISTS
def POLY_TOP_MONOMIAL_LE : thm := BDegree.POLY_TOP_MONOMIAL_LE
def POLY_TOP_MONOMIAL_LT : thm := BDegree.POLY_TOP_MONOMIAL_LT
def POLY_DEG_EQ_0_ALT : thm := BDegree.POLY_DEG_EQ_0_ALT
def POLY_DEG_EQ_0 : thm := BDegree.POLY_DEG_EQ_0
def POLY_DEG_EQ : thm := BDegree.POLY_DEG_EQ
def POLY_DEG_UNIQUE : thm := BDegree.POLY_DEG_UNIQUE
def POLY_DEG_VAR : thm := BDegree.POLY_DEG_VAR
def COEFF_NONZERO_LE_DEG : thm := BDegree.COEFF_NONZERO_LE_DEG
def COEFF_NONZERO_LE : thm := BDegree.COEFF_NONZERO_LE
def POLY_DEG_LE_COEFF_EQ : thm := BDegree.POLY_DEG_LE_COEFF_EQ
def POLY_DEG_LE_COEFF : thm := BDegree.POLY_DEG_LE_COEFF
def POLY_DEG_GE_COEFF_EQ : thm := BDegree.POLY_DEG_GE_COEFF_EQ
def POLY_DEG_GE_COEFF : thm := BDegree.POLY_DEG_GE_COEFF
def POLY_DEG_EQ_COEFF_EQ : thm := BDegree.POLY_DEG_EQ_COEFF_EQ
def POLY_DEG_EQ_COEFF : thm := BDegree.POLY_DEG_EQ_COEFF
def POLY_DEG_EQ_FROM_LE : thm := BDegree.POLY_DEG_EQ_FROM_LE
def COEFF_POWSER_SUM : thm := BDegree.COEFF_POWSER_SUM
def COEFF_POLY_SUM : thm := BDegree.COEFF_POLY_SUM
def COEFF_RING_SUM_MONOMIALS : thm := BDegree.COEFF_RING_SUM_MONOMIALS
def POLY_DEG_NEG : thm := BDegree.POLY_DEG_NEG
def POLY_DEG_ADD_LE : thm := BDegree.POLY_DEG_ADD_LE
def POLY_DEG_SUB_LE : thm := BDegree.POLY_DEG_SUB_LE
def POLY_DEG_ADD : thm := BDegree.POLY_DEG_ADD
def POLY_DEG_SUB : thm := BDegree.POLY_DEG_SUB
def POLY_DEG_ADD_CONST : thm := BDegree.POLY_DEG_ADD_CONST
def POLY_DEG_SUB_CONST : thm := BDegree.POLY_DEG_SUB_CONST
def POLY_DEG_MUL_LE : thm := BDegree.POLY_DEG_MUL_LE
def POLY_DEG_POW_LE : thm := BDegree.POLY_DEG_POW_LE
def POLY_DEG_MUL : thm := BDegree.POLY_DEG_MUL
def POLY_DEG_CMUL : thm := BDegree.POLY_DEG_CMUL
def POLY_DEG_CMUL_LE : thm := BDegree.POLY_DEG_CMUL_LE
def POLY_MUL_LEADING_COEFF : thm := BDegree.POLY_MUL_LEADING_COEFF
def POLY_DEG_MUL_UNIVARIATE : thm := BDegree.POLY_DEG_MUL_UNIVARIATE
def POLY_DEG_VAR_MUL : thm := BDegree.POLY_DEG_VAR_MUL
def POLY_DEG_MUL_VAR : thm := BDegree.POLY_DEG_MUL_VAR
def POLY_DEG_VARPOW_MUL : thm := BDegree.POLY_DEG_VARPOW_MUL
def POLY_DEG_MUL_VARPOW : thm := BDegree.POLY_DEG_MUL_VARPOW
def INTEGRAL_DOMAIN_POLY_RING : thm := BDegree.INTEGRAL_DOMAIN_POLY_RING
def POLY_DEG_POW : thm := BDegree.POLY_DEG_POW
def POLY_DEG_DIVIDES_LE : thm := BDegree.POLY_DEG_DIVIDES_LE
def POLY_DEG_ASSOCIATES : thm := BDegree.POLY_DEG_ASSOCIATES
def POLY_DEG_RING_ADD_LE : thm := BDegree.POLY_DEG_RING_ADD_LE
def POLY_DEG_RING_SUB_LE : thm := BDegree.POLY_DEG_RING_SUB_LE
def POLY_DEG_RING_SUM_LE : thm := BDegree.POLY_DEG_RING_SUM_LE
def POLY_DEG_VAR_POW : thm := BDegree.POLY_DEG_VAR_POW
def POLY_DEG_CONST_VARPOW_LE : thm := BDegree.POLY_DEG_CONST_VARPOW_LE
def POLY_VAR_POW_SUB_CONST : thm := BDegree.POLY_VAR_POW_SUB_CONST
def POLY_POLY_DEG_EQ_0 : thm := BDegree.POLY_POLY_DEG_EQ_0
def POLY_VARS_MUL_EQ : thm := BDegree.POLY_VARS_MUL_EQ
def POLY_VARS_POW_EQ : thm := BDegree.POLY_VARS_POW_EQ

-- Cardinalities
def CARD_EQ_MONOMIALS_FINITE : thm := BCardinalities.CARD_EQ_MONOMIALS_FINITE
def FINITE_MONOMIALS_DEG_LT : thm := BCardinalities.FINITE_MONOMIALS_DEG_LT
def CARD_EQ_MONOMIALS_INFINITE : thm := BCardinalities.CARD_EQ_MONOMIALS_INFINITE
def CARD_EQ_MONOMIALS_COUNTABLE : thm := BCardinalities.CARD_EQ_MONOMIALS_COUNTABLE
def CARD_EQ_POWSER_RING_COUNTABLE : thm := BCardinalities.CARD_EQ_POWSER_RING_COUNTABLE
def CARD_EQ_POWSER_RING_FINITE : thm := BCardinalities.CARD_EQ_POWSER_RING_FINITE
def CARD_EQ_POWSER_RING_INFINITE : thm := BCardinalities.CARD_EQ_POWSER_RING_INFINITE
def CARD_EQ_POLY_RING_COUNTABLE : thm := BCardinalities.CARD_EQ_POLY_RING_COUNTABLE
def CARD_EQ_POLY_RING_FINITE : thm := BCardinalities.CARD_EQ_POLY_RING_FINITE
def CARD_EQ_POLY_RING_INFINITE : thm := BCardinalities.CARD_EQ_POLY_RING_INFINITE

-- Evaluation
def poly_evaluate : thm := BEvaluation.poly_evaluate
def POLY_EVALUATE : thm := BEvaluation.POLY_EVALUATE
def POLY_EVALUATE_0 : thm := BEvaluation.POLY_EVALUATE_0
def POLY_EVALUATE_1 : thm := BEvaluation.POLY_EVALUATE_1
def POLY_EVALUATE_VAR : thm := BEvaluation.POLY_EVALUATE_VAR
def POLY_EVALUATE_CONST : thm := BEvaluation.POLY_EVALUATE_CONST
def POLY_EVALUATE_ADD : thm := BEvaluation.POLY_EVALUATE_ADD
def POLY_EVALUATE_SUB : thm := BEvaluation.POLY_EVALUATE_SUB
def POLY_EVALUATE_MUL : thm := BEvaluation.POLY_EVALUATE_MUL
def POLY_SUB_EVALUATE_IN_IDEAL_GENERATED : thm := BEvaluation.POLY_SUB_EVALUATE_IN_IDEAL_GENERATED
def IDEAL_GENERATED_POLY_POINT : thm := BEvaluation.IDEAL_GENERATED_POLY_POINT
def MAXIMAL_IDEAL_POLY_POINT : thm := BEvaluation.MAXIMAL_IDEAL_POLY_POINT
def POLY_EVALUATE_POW : thm := BEvaluation.POLY_EVALUATE_POW
def POLY_EVALUATE_RING_SUM : thm := BEvaluation.POLY_EVALUATE_RING_SUM
def POLY_EVALUATE_RING_PRODUCT : thm := BEvaluation.POLY_EVALUATE_RING_PRODUCT
def RING_HOMOMORPHISM_POLY_EVALUATE : thm := BEvaluation.RING_HOMOMORPHISM_POLY_EVALUATE
def RING_EPIMORPHISM_POLY_EVALUATE : thm := BEvaluation.RING_EPIMORPHISM_POLY_EVALUATE
def POLY_EVALUATE_HOMOMORPHIC_IMAGE : thm := BEvaluation.POLY_EVALUATE_HOMOMORPHIC_IMAGE
def POLY_EXTEND_EVALUATE : thm := BEvaluation.POLY_EXTEND_EVALUATE
def POLY_EVALUATE_EQ : thm := BEvaluation.POLY_EVALUATE_EQ
def POWSER_EVALUATE_AT_0 : thm := BEvaluation.POWSER_EVALUATE_AT_0
def POLY_EVALUATE_AT_0 : thm := BEvaluation.POLY_EVALUATE_AT_0
def RING_HOMOMORPHISM_POWSER_EVALUATE_AT_0 : thm := BEvaluation.RING_HOMOMORPHISM_POWSER_EVALUATE_AT_0
def RING_EPIMORPHISM_POWSER_EVALUATE_AT_0 : thm := BEvaluation.RING_EPIMORPHISM_POWSER_EVALUATE_AT_0
def POLY_EVALUATE_REINDEX : thm := BEvaluation.POLY_EVALUATE_REINDEX
def poly_eval : thm := BEvaluation.poly_eval
def POLY_EVAL : thm := BEvaluation.POLY_EVAL
def POLY_EVAL_0 : thm := BEvaluation.POLY_EVAL_0
def POLY_EVAL_1 : thm := BEvaluation.POLY_EVAL_1
def POLY_EVAL_VAR : thm := BEvaluation.POLY_EVAL_VAR
def POLY_EVAL_CONST : thm := BEvaluation.POLY_EVAL_CONST
def POLY_EVAL_ADD : thm := BEvaluation.POLY_EVAL_ADD
def POLY_EVAL_SUB : thm := BEvaluation.POLY_EVAL_SUB
def POLY_EVAL_MUL : thm := BEvaluation.POLY_EVAL_MUL
def POLY_EVAL_POW : thm := BEvaluation.POLY_EVAL_POW
def POLY_EVAL_VAR_POW_SUB_CONST : thm := BEvaluation.POLY_EVAL_VAR_POW_SUB_CONST
def POLY_EVAL_RING_SUM : thm := BEvaluation.POLY_EVAL_RING_SUM
def POLY_EVAL_RING_PRODUCT : thm := BEvaluation.POLY_EVAL_RING_PRODUCT
def RING_HOMOMORPHISM_POLY_EVAL : thm := BEvaluation.RING_HOMOMORPHISM_POLY_EVAL
def RING_EPIMORPHISM_POLY_EVAL : thm := BEvaluation.RING_EPIMORPHISM_POLY_EVAL
def POLY_EVAL_HOMOMORPHIC_IMAGE : thm := BEvaluation.POLY_EVAL_HOMOMORPHIC_IMAGE
def POLY_EVAL_SUBRING_GENERATED : thm := BEvaluation.POLY_EVAL_SUBRING_GENERATED
def POLY_EXTEND_UNIVARIATE : thm := BEvaluation.POLY_EXTEND_UNIVARIATE
def POLY_EVAL_EXPAND : thm := BEvaluation.POLY_EVAL_EXPAND
def POLY_EXPAND : thm := BEvaluation.POLY_EXPAND
def COEFF_RING_SUM_VARPOW_REV : thm := BEvaluation.COEFF_RING_SUM_VARPOW_REV
def POLY_EXPAND_REV : thm := BEvaluation.POLY_EXPAND_REV
def IN_IDEAL_GENERATED_POLY_CONST : thm := BEvaluation.IN_IDEAL_GENERATED_POLY_CONST
def POLY_DEG_RING_SUM_VARPOW_REV : thm := BEvaluation.POLY_DEG_RING_SUM_VARPOW_REV
def POWSER_EVAL_AT_0 : thm := BEvaluation.POWSER_EVAL_AT_0
def POLY_EVAL_AT_0 : thm := BEvaluation.POLY_EVAL_AT_0
def RING_HOMOMORPHISM_POWSER_EVAL_AT_0 : thm := BEvaluation.RING_HOMOMORPHISM_POWSER_EVAL_AT_0
def RING_EPIMORPHISM_POWSER_EVAL_AT_0 : thm := BEvaluation.RING_EPIMORPHISM_POWSER_EVAL_AT_0
def POWSER_RING_HOMOMORPHISM_COEFF_0 : thm := BEvaluation.POWSER_RING_HOMOMORPHISM_COEFF_0
def POLY_RING_HOMOMORPHISM_COEFF_0 : thm := BEvaluation.POLY_RING_HOMOMORPHISM_COEFF_0
def POWSER_RING_EPIMORPHISM_COEFF_0 : thm := BEvaluation.POWSER_RING_EPIMORPHISM_COEFF_0
def POLY_RING_EPIMORPHISM_COEFF_0 : thm := BEvaluation.POLY_RING_EPIMORPHISM_COEFF_0
def POLY_EVAL_COEFF : thm := BEvaluation.POLY_EVAL_COEFF
def IMAGE_POLY_EVAL : thm := BEvaluation.IMAGE_POLY_EVAL
def POLY_VAR_DIVIDES_UNIVARIATE : thm := BEvaluation.POLY_VAR_DIVIDES_UNIVARIATE

-- Composing
def RING_POWERSERIES_COMPOSE : thm := BComposing.RING_POWERSERIES_COMPOSE
def IN_RING_POWERSERIES_CARRIER_COMPOSE : thm := BComposing.IN_RING_POWERSERIES_CARRIER_COMPOSE
def RING_POLYNOMIAL_COMPOSE : thm := BComposing.RING_POLYNOMIAL_COMPOSE
def IN_RING_POLYNOMIAL_CARRIER_COMPOSE : thm := BComposing.IN_RING_POLYNOMIAL_CARRIER_COMPOSE
def POLY_DEG_HOMOMORPHIC_IMAGE : thm := BComposing.POLY_DEG_HOMOMORPHIC_IMAGE
def POLY_DEG_MONOMORPHIC_IMAGE : thm := BComposing.POLY_DEG_MONOMORPHIC_IMAGE
def POLY_EQ_0_MONOMORPHIC_IMAGE : thm := BComposing.POLY_EQ_0_MONOMORPHIC_IMAGE
def RING_HOMOMORPHISM_POWSER_RINGS : thm := BComposing.RING_HOMOMORPHISM_POWSER_RINGS
def POLY_EVAL_RING_PRODUCT_EQ_0 : thm := BComposing.POLY_EVAL_RING_PRODUCT_EQ_0
def RING_HOMOMORPHISM_POLY_RINGS : thm := BComposing.RING_HOMOMORPHISM_POLY_RINGS
def RING_MONOMORPHISM_POWSER_RINGS : thm := BComposing.RING_MONOMORPHISM_POWSER_RINGS
def POLY_RING_MONOMORPHIC_PREIMAGE : thm := BComposing.POLY_RING_MONOMORPHIC_PREIMAGE
def RING_MONOMORPHISM_POLY_RINGS : thm := BComposing.RING_MONOMORPHISM_POLY_RINGS
def RING_EPIMORPHISM_POWSER_RINGS : thm := BComposing.RING_EPIMORPHISM_POWSER_RINGS
def RING_EPIMORPHISM_POLY_RINGS : thm := BComposing.RING_EPIMORPHISM_POLY_RINGS
def RING_ISOMORPHISM_POWSER_RINGS : thm := BComposing.RING_ISOMORPHISM_POWSER_RINGS
def RING_ISOMORPHISM_POLY_RINGS : thm := BComposing.RING_ISOMORPHISM_POLY_RINGS
def RING_SUM_POWSER_SUBRING_GENERATED : thm := BComposing.RING_SUM_POWSER_SUBRING_GENERATED
def RING_PRODUCT_POWSER_SUBRING_GENERATED : thm := BComposing.RING_PRODUCT_POWSER_SUBRING_GENERATED
def RING_SUM_POLY_SUBRING_GENERATED : thm := BComposing.RING_SUM_POLY_SUBRING_GENERATED
def RING_PRODUCT_POLY_SUBRING_GENERATED : thm := BComposing.RING_PRODUCT_POLY_SUBRING_GENERATED
def POLY_COMPOSE_HOMOMORPHISM_VAR : thm := BComposing.POLY_COMPOSE_HOMOMORPHISM_VAR
def POLY_COMPOSE_HOMOMORPHISM_CONST : thm := BComposing.POLY_COMPOSE_HOMOMORPHISM_CONST
def POLY_COMPOSE_HOMOMORPHISM_NEG : thm := BComposing.POLY_COMPOSE_HOMOMORPHISM_NEG
def POLY_COMPOSE_HOMOMORPHISM_MUL : thm := BComposing.POLY_COMPOSE_HOMOMORPHISM_MUL
def POLY_COMPOSE_HOMOMORPHISM_SUB : thm := BComposing.POLY_COMPOSE_HOMOMORPHISM_SUB
def POLY_COMPOSE_HOMOMORPHISM_ADD : thm := BComposing.POLY_COMPOSE_HOMOMORPHISM_ADD
def POLY_COMPOSE_HOMOMORPHISM_POW : thm := BComposing.POLY_COMPOSE_HOMOMORPHISM_POW
def POLY_COMPOSE_HOMOMORPHISM_X_MINUS_POW : thm := BComposing.POLY_COMPOSE_HOMOMORPHISM_X_MINUS_POW

-- Zerodivisors
def INTEGRAL_DOMAIN_POWSER_RING : thm := BZerodivisors.INTEGRAL_DOMAIN_POWSER_RING
def RING_UNIT_POLY_CONST : thm := BZerodivisors.RING_UNIT_POLY_CONST
def RING_UNIT_POLY_DOMAIN : thm := BZerodivisors.RING_UNIT_POLY_DOMAIN
def RING_NILPOTENT_POLY_RING : thm := BZerodivisors.RING_NILPOTENT_POLY_RING
def RING_UNIT_POLY_RING : thm := BZerodivisors.RING_UNIT_POLY_RING
def RING_UNIT_POLY_RING_1 : thm := BZerodivisors.RING_UNIT_POLY_RING_1
def RING_UNIT_POLY_VAR : thm := BZerodivisors.RING_UNIT_POLY_VAR
def FIELD_POLY_RING : thm := BZerodivisors.FIELD_POLY_RING
def POLY_DEG_UNIT : thm := BZerodivisors.POLY_DEG_UNIT
def POLY_DEG_EQ_0_UNIT : thm := BZerodivisors.POLY_DEG_EQ_0_UNIT
def FIELD_POLY_DEG_EQ_0 : thm := BZerodivisors.FIELD_POLY_DEG_EQ_0
def IRREDUCIBLE_IMP_POLY_DEG_NZ : thm := BZerodivisors.IRREDUCIBLE_IMP_POLY_DEG_NZ
def POLY_DEG_1_IMP_IRREDUCIBLE : thm := BZerodivisors.POLY_DEG_1_IMP_IRREDUCIBLE
def RING_UNIT_POWSER_RING : thm := BZerodivisors.RING_UNIT_POWSER_RING
def LOCAL_POWSER_RING : thm := BZerodivisors.LOCAL_POWSER_RING
def RING_PRIME_POLY_VAR_UNIVARIATE : thm := BZerodivisors.RING_PRIME_POLY_VAR_UNIVARIATE
def RING_PRIME_POLY_VAR : thm := BZerodivisors.RING_PRIME_POLY_VAR
def RING_IRREDUCIBLE_POLY_VAR : thm := BZerodivisors.RING_IRREDUCIBLE_POLY_VAR
def RING_PRIME_POLY_CONST : thm := BZerodivisors.RING_PRIME_POLY_CONST
def RING_IRREDUCIBLE_POLY_CONST : thm := BZerodivisors.RING_IRREDUCIBLE_POLY_CONST
def RING_ISOMORPHISMS_POLY_TRANSLATE : thm := BZerodivisors.RING_ISOMORPHISMS_POLY_TRANSLATE
def RING_PRIME_VAR_MINUS_A : thm := BZerodivisors.RING_PRIME_VAR_MINUS_A
def RING_PRIME_X_MINUS_A : thm := BZerodivisors.RING_PRIME_X_MINUS_A
def RING_IRREDUCIBLE_VAR_MINUS_A : thm := BZerodivisors.RING_IRREDUCIBLE_VAR_MINUS_A
def RING_IRREDUCIBLE_X_MINUS_A : thm := BZerodivisors.RING_IRREDUCIBLE_X_MINUS_A
def RING_UNIT_VAR_MINUS_A : thm := BZerodivisors.RING_UNIT_VAR_MINUS_A
def RING_UNIT_X_MINUS_A : thm := BZerodivisors.RING_UNIT_X_MINUS_A
def POLY_DEG_VAR_MINUS_A : thm := BZerodivisors.POLY_DEG_VAR_MINUS_A

-- XMinusA
def POLY_DEG_X_MINUS_A : thm := BXMinusA.POLY_DEG_X_MINUS_A
def POLY_X_MINUS_A_NONZERO : thm := BXMinusA.POLY_X_MINUS_A_NONZERO
def POLY_X_MINUS_A_IN_CARRIER : thm := BXMinusA.POLY_X_MINUS_A_IN_CARRIER
def RING_POLYNOMIAL_X_MINUS_A : thm := BXMinusA.RING_POLYNOMIAL_X_MINUS_A
def POLY_DIVIDES_X_MINUS_A : thm := BXMinusA.POLY_DIVIDES_X_MINUS_A
def POLY_DIVIDES_X_MINUS_ROOT : thm := BXMinusA.POLY_DIVIDES_X_MINUS_ROOT
def POLY_DIVIDES_X_MINUS_ROOT_EQ : thm := BXMinusA.POLY_DIVIDES_X_MINUS_ROOT_EQ
def POLY_ROOT_BOUND : thm := BXMinusA.POLY_ROOT_BOUND
def INFINITE_INTEGRAL_DOMAIN_POLY_EVAL_ALL_ZERO : thm := BXMinusA.INFINITE_INTEGRAL_DOMAIN_POLY_EVAL_ALL_ZERO
def POLY_EQSET_BOUND : thm := BXMinusA.POLY_EQSET_BOUND
def POLY_LEVELSET_BOUND : thm := BXMinusA.POLY_LEVELSET_BOUND
def ROOTS_OF_UNITY_BOUND : thm := BXMinusA.ROOTS_OF_UNITY_BOUND
def IRREDUCIBLE_ROOT_IMP_DEG_EQ_1 : thm := BXMinusA.IRREDUCIBLE_ROOT_IMP_DEG_EQ_1

-- Division
def POLY_TOP_NONZERO : thm := BDivision.POLY_TOP_NONZERO
def POLY_TOP_TAIL : thm := BDivision.POLY_TOP_TAIL
def POLY_TOP_EQ_0 : thm := BDivision.POLY_TOP_EQ_0
def POLY_DEG_LT_FROM_LE : thm := BDivision.POLY_DEG_LT_FROM_LE
def POLY_DEG_DIVIDES_LE_UNIVARIATE : thm := BDivision.POLY_DEG_DIVIDES_LE_UNIVARIATE
def POLY_DIVISION_GEN : thm := BDivision.POLY_DIVISION_GEN
def POLY_DIVISION : thm := BDivision.POLY_DIVISION
def EUCLIDEAN_POLY_RING : thm := BDivision.EUCLIDEAN_POLY_RING
def PID_POLY_RING : thm := BDivision.PID_POLY_RING
def POLY_DEG_1_ROOT : thm := BDivision.POLY_DEG_1_ROOT
def POLY_DEG_2_IRREDUCIBLE : thm := BDivision.POLY_DEG_2_IRREDUCIBLE
def poly_div : thm := BDivision.poly_div
def poly_rem : thm := BDivision.poly_rem
def POLY_DIV_REM : thm := BDivision.POLY_DIV_REM
def POLY_DIV : thm := BDivision.POLY_DIV
def RING_POLYNOMIAL_DIV : thm := BDivision.RING_POLYNOMIAL_DIV
def POLY_REM : thm := BDivision.POLY_REM
def RING_POLYNOMIAL_REM : thm := BDivision.RING_POLYNOMIAL_REM
def POLY_DIV_REM_SIMP : thm := BDivision.POLY_DIV_REM_SIMP
def POLY_DEG_REM : thm := BDivision.POLY_DEG_REM
def POLY_DEG_REM_ALT : thm := BDivision.POLY_DEG_REM_ALT
def POLY_DIVIDES_REM : thm := BDivision.POLY_DIVIDES_REM
def POLY_REM_UNIQUE : thm := BDivision.POLY_REM_UNIQUE
def HAS_SIZE_POLY_DEG_LT : thm := BDivision.HAS_SIZE_POLY_DEG_LT
def QUOTIENT_POLY_RING_HAS_SIZE : thm := BDivision.QUOTIENT_POLY_RING_HAS_SIZE
def MAXIMAL_IDEAL_POLY_RING_EPIMORPHISM : thm := BDivision.MAXIMAL_IDEAL_POLY_RING_EPIMORPHISM

-- Hilbert
def NOETHERIAN_POLY_RING_1 : thm := BHilbert.NOETHERIAN_POLY_RING_1
def NOETHERIAN_POLY_RING : thm := BHilbert.NOETHERIAN_POLY_RING
def KAPLANSKY_LEMMA : thm := BHilbert.KAPLANSKY_LEMMA
def NOETHERIAN_POWSER_RING_1 : thm := BHilbert.NOETHERIAN_POWSER_RING_1
def NOETHERIAN_POWSER_RING : thm := BHilbert.NOETHERIAN_POWSER_RING

-- Monic
def monic : thm := BMonic.monic
def MONIC_POLY_1 : thm := BMonic.MONIC_POLY_1
def MONIC_POLY_0 : thm := BMonic.MONIC_POLY_0
def MONIC_IMP_NONZERO : thm := BMonic.MONIC_IMP_NONZERO
def MONIC_IN_TRIVIAL_RING : thm := BMonic.MONIC_IN_TRIVIAL_RING
def MONIC_POLY_CONST : thm := BMonic.MONIC_POLY_CONST
def MONIC_DEG_0 : thm := BMonic.MONIC_DEG_0
def MONIC_UNIT_EQ_DEG_0 : thm := BMonic.MONIC_UNIT_EQ_DEG_0
def MONIC_POLY_VAR : thm := BMonic.MONIC_POLY_VAR
def MONIC_X_MINUS_A : thm := BMonic.MONIC_X_MINUS_A
def MONIC_EQ_X_MINUS_A : thm := BMonic.MONIC_EQ_X_MINUS_A
def MONIC_SUBRING_GENERATED : thm := BMonic.MONIC_SUBRING_GENERATED
def MONIC_HOMOMORPHIC_IMAGE : thm := BMonic.MONIC_HOMOMORPHIC_IMAGE
def MONIC_EPIMORPHIC_PREIMAGE : thm := BMonic.MONIC_EPIMORPHIC_PREIMAGE
def POLY_DEG_MUL_MONIC : thm := BMonic.POLY_DEG_MUL_MONIC
def POLY_DEG_LMUL_MONIC : thm := BMonic.POLY_DEG_LMUL_MONIC
def POLY_DEG_RMUL_MONIC : thm := BMonic.POLY_DEG_RMUL_MONIC
def POLY_DEG_MUL_X_MINUS_A : thm := BMonic.POLY_DEG_MUL_X_MINUS_A
def POLY_DEG_CMUL_MONIC : thm := BMonic.POLY_DEG_CMUL_MONIC
def MONIC_POLY_MUL : thm := BMonic.MONIC_POLY_MUL
def MONIC_POLY_POW : thm := BMonic.MONIC_POLY_POW
def POLY_DEG_POW_MONIC : thm := BMonic.POLY_DEG_POW_MONIC
def MONIC_POLY_PRODUCT : thm := BMonic.MONIC_POLY_PRODUCT
def MONIC_POLY_ADD_LOWER : thm := BMonic.MONIC_POLY_ADD_LOWER
def RING_UNIT_LEADING_COEFF_VARPOW_ADD : thm := BMonic.RING_UNIT_LEADING_COEFF_VARPOW_ADD
def POLY_DEG_PRODUCT_MONIC : thm := BMonic.POLY_DEG_PRODUCT_MONIC
def POLY_DEG_PRODUCT_POW_MONIC : thm := BMonic.POLY_DEG_PRODUCT_POW_MONIC
def MONIC_POLY_EXTEND_WEIGHT : thm := BMonic.MONIC_POLY_EXTEND_WEIGHT
def COEFF_POLY_MUL_MONIC_SUBLEADING : thm := BMonic.COEFF_POLY_MUL_MONIC_SUBLEADING
def COEFF_RING_PRODUCT_MONIC_SUBLEADING : thm := BMonic.COEFF_RING_PRODUCT_MONIC_SUBLEADING
def COEFF_POLY_POW_X_MINUS_A_SUBLEADING : thm := BMonic.COEFF_POLY_POW_X_MINUS_A_SUBLEADING
def MONIC_POLY_SPLIT : thm := BMonic.MONIC_POLY_SPLIT
def MONIC_ASSOCIATES_EQ : thm := BMonic.MONIC_ASSOCIATES_EQ
def RING_ASSOCIATES_X_MINUS_A : thm := BMonic.RING_ASSOCIATES_X_MINUS_A
def MONIC_CMUL : thm := BMonic.MONIC_CMUL
def MONIC_ASSOCIATE_EXISTS : thm := BMonic.MONIC_ASSOCIATE_EXISTS
def LINEAR_POLY_ASSOCIATE_X_MINUS_A : thm := BMonic.LINEAR_POLY_ASSOCIATE_X_MINUS_A
def FIELD_MONIC_ASSOCIATE : thm := BMonic.FIELD_MONIC_ASSOCIATE
def FIELD_MONIC_IRREDUCIBLE_ASSOCIATE : thm := BMonic.FIELD_MONIC_IRREDUCIBLE_ASSOCIATE
def RING_COPRIME_DISTINCT_MONIC_IRREDUCIBLES : thm := BMonic.RING_COPRIME_DISTINCT_MONIC_IRREDUCIBLES
def POLY_DEG_DIVIDES_LE_MONIC : thm := BMonic.POLY_DEG_DIVIDES_LE_MONIC
def MONIC_DIVIDES_EQ : thm := BMonic.MONIC_DIVIDES_EQ
def MONIC_FACTOR_COEFFS_PRIME_IDEAL : thm := BMonic.MONIC_FACTOR_COEFFS_PRIME_IDEAL
def POLY_ROOT_DECOMPOSE : thm := BMonic.POLY_ROOT_DECOMPOSE
def poly_splits : thm := BSplits.poly_splits
def POLY_SPLITS_IN_CARRIER : thm := BSplits.POLY_SPLITS_IN_CARRIER
def POLY_SPLITS_CONST : thm := BSplits.POLY_SPLITS_CONST
def POLY_SPLITS_0 : thm := BSplits.POLY_SPLITS_0
def POLY_SPLITS_1 : thm := BSplits.POLY_SPLITS_1
def POLY_DEG_0_IMP_SPLITS : thm := BSplits.POLY_DEG_0_IMP_SPLITS
def POLY_SPLITS_UNIT : thm := BSplits.POLY_SPLITS_UNIT
def POLY_SPLITS_OVER_TRIVIAL_RING : thm := BSplits.POLY_SPLITS_OVER_TRIVIAL_RING
def POLY_SPLITS_X_MINUS_A : thm := BSplits.POLY_SPLITS_X_MINUS_A
def POLY_SPLITS_VAR : thm := BSplits.POLY_SPLITS_VAR
def POLY_DEG_SPLIT : thm := BSplits.POLY_DEG_SPLIT
def POLY_DEG_SPLIT_MONIC : thm := BSplits.POLY_DEG_SPLIT_MONIC
def POLY_TOP_SPLIT : thm := BSplits.POLY_TOP_SPLIT
def POLY_EVAL_SPLIT : thm := BSplits.POLY_EVAL_SPLIT
def POLY_SPLITS : thm := BSplits.POLY_SPLITS
def POLY_SPLITS_CASES : thm := BSplits.POLY_SPLITS_CASES
def POLY_SPLITS_CASES_ALT : thm := BSplits.POLY_SPLITS_CASES_ALT
def POLY_SPLITS_MUL : thm := BSplits.POLY_SPLITS_MUL
def POLY_SPLITS_PRODUCT : thm := BSplits.POLY_SPLITS_PRODUCT
def POLY_PRODUCT_HOMOMORPHIC_IMAGE : thm := BSplits.POLY_PRODUCT_HOMOMORPHIC_IMAGE
def POLY_SPLITS_IN_SUBRING : thm := BSplits.POLY_SPLITS_IN_SUBRING
def POLY_SPLITS_IN_SUBRING_MONIC : thm := BSplits.POLY_SPLITS_IN_SUBRING_MONIC
def POLY_SPLITS_HOMOMORPHIC_IMAGE : thm := BSplits.POLY_SPLITS_HOMOMORPHIC_IMAGE
def POLY_SPLITS_MONOMORPHIC_PREIMAGE : thm := BSplits.POLY_SPLITS_MONOMORPHIC_PREIMAGE
def POLY_DEG_1_IMP_SPLITS_MONIC : thm := BSplits.POLY_DEG_1_IMP_SPLITS_MONIC
def POLY_DEG_1_IMP_SPLITS : thm := BSplits.POLY_DEG_1_IMP_SPLITS
def POLY_SPLITS_EQ_IRREDUCIBLES : thm := BSplits.POLY_SPLITS_EQ_IRREDUCIBLES
def POLY_SPLITS_DIVISOR : thm := BSplits.POLY_SPLITS_DIVISOR
def POLY_ROOTS_SPLIT : thm := BSplits.POLY_ROOTS_SPLIT
def RING_PRODUCT_X_MINUS_A : thm := BSplits.RING_PRODUCT_X_MINUS_A
def POLY_SPLITS_HAS_ROOT : thm := BSplits.POLY_SPLITS_HAS_ROOT
def POLY_ROOTS_MONOMORPHIC_IMAGE : thm := BSplits.POLY_ROOTS_MONOMORPHIC_IMAGE
def POLY_SPLITS_SQUAREFREE_ROOT_COUNT_EXPLICIT : thm := BSplits.POLY_SPLITS_SQUAREFREE_ROOT_COUNT_EXPLICIT
def POLY_SPLITS_SQUAREFREE_ROOT_COUNT : thm := BSplits.POLY_SPLITS_SQUAREFREE_ROOT_COUNT
def POLY_ROOT_COUNT_IMP_SPLITS : thm := BSplits.POLY_ROOT_COUNT_IMP_SPLITS
def POLY_ROOT_COUNT_IMP_PRODUCT : thm := BSplits.POLY_ROOT_COUNT_IMP_PRODUCT
def MONIC_POLY_EQ_ROOTS_PRODUCT : thm := BSplits.MONIC_POLY_EQ_ROOTS_PRODUCT

-- Reciprocal
def poly_recip : thm := BReciprocal.poly_recip
def COEFF_POLY_RECIP : thm := BReciprocal.COEFF_POLY_RECIP
def RING_POWERSERIES_RECIP : thm := BReciprocal.RING_POWERSERIES_RECIP
def RING_POLYNOMIAL_RECIP : thm := BReciprocal.RING_POLYNOMIAL_RECIP
def POLY_RECIP_IN_CARRIER : thm := BReciprocal.POLY_RECIP_IN_CARRIER
def COEFF_0_POLY_RECIP_EQ_0 : thm := BReciprocal.COEFF_0_POLY_RECIP_EQ_0
def POLY_DEG_RECIP_LE : thm := BReciprocal.POLY_DEG_RECIP_LE
def POLY_DEG_RECIP : thm := BReciprocal.POLY_DEG_RECIP
def POLY_RECIP_RECIP : thm := BReciprocal.POLY_RECIP_RECIP
def POLY_VARPOW_RECIP_RECIP : thm := BReciprocal.POLY_VARPOW_RECIP_RECIP
def POLY_DIVIDES_RECIP_RECIP : thm := BReciprocal.POLY_DIVIDES_RECIP_RECIP
def POLY_RECIP_CONST : thm := BReciprocal.POLY_RECIP_CONST
def RING_UNIT_POLY_RECIP : thm := BReciprocal.RING_UNIT_POLY_RECIP
def RING_UNIT_POLY_RECIP_EQ : thm := BReciprocal.RING_UNIT_POLY_RECIP_EQ
def POLY_RECIP_0 : thm := BReciprocal.POLY_RECIP_0
def POLY_RECIP_EQ_0 : thm := BReciprocal.POLY_RECIP_EQ_0
def POLY_RECIP_RECIP_EQ : thm := BReciprocal.POLY_RECIP_RECIP_EQ
def POLY_RECIP_1 : thm := BReciprocal.POLY_RECIP_1
def POLY_RECIP_NEG : thm := BReciprocal.POLY_RECIP_NEG
def POLY_RECIP_MUL_GEN : thm := BReciprocal.POLY_RECIP_MUL_GEN
def POLY_RECIP_MUL : thm := BReciprocal.POLY_RECIP_MUL
def POLY_DIVIDES_RECIP : thm := BReciprocal.POLY_DIVIDES_RECIP
def POLY_DIVIDES_RECIP_GALOIS : thm := BReciprocal.POLY_DIVIDES_RECIP_GALOIS
def POLY_DIVIDES_RECIP_EQ : thm := BReciprocal.POLY_DIVIDES_RECIP_EQ
def RING_PRIME_POLY_RECIP : thm := BReciprocal.RING_PRIME_POLY_RECIP
def RING_PRIME_POLY_RECIP_EQ : thm := BReciprocal.RING_PRIME_POLY_RECIP_EQ
def RING_IRREDUCIBLE_POLY_RECIP : thm := BReciprocal.RING_IRREDUCIBLE_POLY_RECIP
def RING_IRREDUCIBLE_POLY_RECIP_EQ : thm := BReciprocal.RING_IRREDUCIBLE_POLY_RECIP_EQ
def POLY_EVAL_RECIP : thm := BReciprocal.POLY_EVAL_RECIP

-- Derivative
def poly_deriv : thm := BDerivative.poly_deriv
def POLY_DERIV_SUBRING_GENERATED : thm := BDerivative.POLY_DERIV_SUBRING_GENERATED
def COEFF_POLY_DERIV : thm := BDerivative.COEFF_POLY_DERIV
def RING_POWERSERIES_POLY_DERIV : thm := BDerivative.RING_POWERSERIES_POLY_DERIV
def POWSER_DERIV_IN_CARRIER : thm := BDerivative.POWSER_DERIV_IN_CARRIER
def RING_POLYNOMIAL_POLY_DERIV : thm := BDerivative.RING_POLYNOMIAL_POLY_DERIV
def POLY_DERIV_IN_CARRIER : thm := BDerivative.POLY_DERIV_IN_CARRIER
def POLY_DEG_DERIV_LE : thm := BDerivative.POLY_DEG_DERIV_LE
def POLY_DEG_DERIV : thm := BDerivative.POLY_DEG_DERIV
def POLY_DERIV_NONZERO_CHAR0 : thm := BDerivative.POLY_DERIV_NONZERO_CHAR0
def POLY_DERIV_CONST : thm := BDerivative.POLY_DERIV_CONST
def POLY_DERIV_0 : thm := BDerivative.POLY_DERIV_0
def POLY_DERIV_1 : thm := BDerivative.POLY_DERIV_1
def POLY_DERIV_VAR : thm := BDerivative.POLY_DERIV_VAR
def POLY_DERIV_ADD : thm := BDerivative.POLY_DERIV_ADD
def POLY_DERIV_NEG : thm := BDerivative.POLY_DERIV_NEG
def POLY_DERIV_SUB : thm := BDerivative.POLY_DERIV_SUB
def POLY_DERIV_CMUL : thm := BDerivative.POLY_DERIV_CMUL
def POLY_DERIV_HOMOMORPHIC_IMAGE : thm := BDerivative.POLY_DERIV_HOMOMORPHIC_IMAGE
def POLY_DERIV_MUL : thm := BDerivative.POLY_DERIV_MUL
def POLY_EVALUATE_TAYLOR : thm := BDerivative.POLY_EVALUATE_TAYLOR
def POLY_EVALUATE_SUB_IN_IDEAL : thm := BDerivative.POLY_EVALUATE_SUB_IN_IDEAL
def POLY_DERIV_SUM : thm := BDerivative.POLY_DERIV_SUM
def POLY_DERIV_PRODUCT : thm := BDerivative.POLY_DERIV_PRODUCT
def POLY_DERIV_POW : thm := BDerivative.POLY_DERIV_POW
def POLY_DERIV_VAR_POW : thm := BDerivative.POLY_DERIV_VAR_POW
def POLY_DERIV_VAR_POW_ZERO : thm := BDerivative.POLY_DERIV_VAR_POW_ZERO
def POLY_DERIV_EQ_0_COEFF : thm := BDerivative.POLY_DERIV_EQ_0_COEFF
def POLY_DERIV_EQ_0_EXPLICIT : thm := BDerivative.POLY_DERIV_EQ_0_EXPLICIT
def POLY_IRREDUCIBLE_DIVIDES_DERIV_EQ : thm := BDerivative.POLY_IRREDUCIBLE_DIVIDES_DERIV_EQ

-- Separable
def poly_separable : thm := BSeparable.poly_separable
def POLY_NONCONSTANT_IRREDUCIBLE_IMP_SEPARABLE : thm := BSeparable.POLY_NONCONSTANT_IRREDUCIBLE_IMP_SEPARABLE
def POLY_IRREDUCIBLE_IMP_SEPARABLE : thm := BSeparable.POLY_IRREDUCIBLE_IMP_SEPARABLE
def POLY_SQUARE_DIVIDES_DERIV : thm := BSeparable.POLY_SQUARE_DIVIDES_DERIV
def REPEATED_ROOT_POLY_DERIV_ZERO : thm := BSeparable.REPEATED_ROOT_POLY_DERIV_ZERO
def POLY_SEPARABLE_IMP_SQUAREFREE : thm := BSeparable.POLY_SEPARABLE_IMP_SQUAREFREE
def POLY_SQUARE_DIVIDES_DERIV_EQ : thm := BSeparable.POLY_SQUARE_DIVIDES_DERIV_EQ
def POLY_SQUAREFREE_IMP_SEPARABLE : thm := BSeparable.POLY_SQUAREFREE_IMP_SEPARABLE
def POLY_SEPARABLE_EQ_SQUAREFREE : thm := BSeparable.POLY_SEPARABLE_EQ_SQUAREFREE
def POLY_SEPARABLE_MONOMORPHIC_IMAGE : thm := BSeparable.POLY_SEPARABLE_MONOMORPHIC_IMAGE
def POLY_SEPARABLE_FROM_MONOMORPHIC_IMAGE : thm := BSeparable.POLY_SEPARABLE_FROM_MONOMORPHIC_IMAGE
def POLY_SEPARABLE_DIVISOR : thm := BSeparable.POLY_SEPARABLE_DIVISOR
def POLY_SEPARABLE_X_MINUS_A : thm := BSeparable.POLY_SEPARABLE_X_MINUS_A
def POLY_ROOT_COUNT_IMP_SQUAREFREE : thm := BSeparable.POLY_ROOT_COUNT_IMP_SQUAREFREE
def POLY_SEPARABLE_EQ_DERIV_NONZERO : thm := BSeparable.POLY_SEPARABLE_EQ_DERIV_NONZERO

-- GaussA
def POLY_PRIMITIVE_CONST_CANCEL : thm := BGaussA.POLY_PRIMITIVE_CONST_CANCEL
def MAKE_PRIMITIVE_IN_IDEAL : thm := BGaussA.MAKE_PRIMITIVE_IN_IDEAL
def POLY_MAKE_PRIMITIVE : thm := BGaussA.POLY_MAKE_PRIMITIVE
def RING_PRIME_POLY_RING_MONO : thm := BGaussA.RING_PRIME_POLY_RING_MONO

-- GaussB
def UFD_POLY_RING : thm := BGaussB.UFD_POLY_RING

-- GaussC
def POLY_CLEAR_DENOMINATORS : thm := BGaussC.POLY_CLEAR_DENOMINATORS

-- GaussD
def IRREDUCIBLE_PRIMITIVE_POLY_FRACTION_RING : thm := BGaussD.IRREDUCIBLE_PRIMITIVE_POLY_FRACTION_RING

-- Eisenstein
def EISENSTEIN_IRREDUCIBILITY_GEN : thm := BEisenstein.EISENSTEIN_IRREDUCIBILITY_GEN
def EISENSTEIN_IRREDUCIBILITY : thm := BEisenstein.EISENSTEIN_IRREDUCIBILITY
def EISENSTEIN_IRREDUCIBILITY_FRACTION_RING : thm := BEisenstein.EISENSTEIN_IRREDUCIBILITY_FRACTION_RING

-- RingOrder
def RING_ORDER_DIVIDES : thm := BRingOrder.RING_ORDER_DIVIDES
def RING_POW_EQ_1 : thm := BRingOrder.RING_POW_EQ_1
def RING_POW_EQ : thm := BRingOrder.RING_POW_EQ
def RING_ORDER_EQ_0 : thm := BRingOrder.RING_ORDER_EQ_0
def RING_ORDER_EQ_1 : thm := BRingOrder.RING_ORDER_EQ_1
def RING_ORDER_UNIQUE : thm := BRingOrder.RING_ORDER_UNIQUE
def RING_ORDER_EQ_LEAST : thm := BRingOrder.RING_ORDER_EQ_LEAST
def RING_POW_RING_ORDER : thm := BRingOrder.RING_POW_RING_ORDER
def RING_ORDER_1 : thm := BRingOrder.RING_ORDER_1
def RING_ORDER_SUBRING_GENERATED : thm := BRingOrder.RING_ORDER_SUBRING_GENERATED
def RING_POW_GCD_EQ_1 : thm := BRingOrder.RING_POW_GCD_EQ_1
def RING_POW_COPRIME_EQ_1 : thm := BRingOrder.RING_POW_COPRIME_EQ_1
def RING_ORDER_MUL_DIVIDES_GEN : thm := BRingOrder.RING_ORDER_MUL_DIVIDES_GEN
def RING_ORDER_MUL_DIVIDES : thm := BRingOrder.RING_ORDER_MUL_DIVIDES
def RING_ORDER_MUL_DIVIDES_LCM : thm := BRingOrder.RING_ORDER_MUL_DIVIDES_LCM
def RING_POW_MOD_ORDER_GEN : thm := BRingOrder.RING_POW_MOD_ORDER_GEN
def RING_POW_MOD_ORDER : thm := BRingOrder.RING_POW_MOD_ORDER
def RING_POW_EQ_GEN : thm := BRingOrder.RING_POW_EQ_GEN
def RING_POW_EQ_LT : thm := BRingOrder.RING_POW_EQ_LT
def RING_POW_EQ_LT_EQ : thm := BRingOrder.RING_POW_EQ_LT_EQ
def RING_ORDER_POW : thm := BRingOrder.RING_ORDER_POW
def RING_ORDER_POW_GEN : thm := BRingOrder.RING_ORDER_POW_GEN
def RING_ORDER_POW_DIVIDES : thm := BRingOrder.RING_ORDER_POW_DIVIDES
def RING_ORDER_UNIQUE_PRIME : thm := BRingOrder.RING_ORDER_UNIQUE_PRIME
def RING_ORDER_MUL : thm := BRingOrder.RING_ORDER_MUL
def RING_ORDER_0 : thm := BRingOrder.RING_ORDER_0
def RING_ORDER_NONZERO_MULTSYS : thm := BRingOrder.RING_ORDER_NONZERO_MULTSYS
def RING_ORDER_NONZERO : thm := BRingOrder.RING_ORDER_NONZERO
def INTEGRAL_DOMAIN_ORDER_NONZERO : thm := BRingOrder.INTEGRAL_DOMAIN_ORDER_NONZERO
def FINITE_RING_REGULAR : thm := BRingOrder.FINITE_RING_REGULAR
def FINITE_INTEGRAL_DOMAIN_UNIT : thm := BRingOrder.FINITE_INTEGRAL_DOMAIN_UNIT
def RING_ORDER_LCM_EXISTS_MULTSYS : thm := BRingOrder.RING_ORDER_LCM_EXISTS_MULTSYS
def RING_ORDER_LCM_EXISTS : thm := BRingOrder.RING_ORDER_LCM_EXISTS
def RING_ORDER_DIVIDES_MAXIMAL_MULTSYS_GEN : thm := BRingOrder.RING_ORDER_DIVIDES_MAXIMAL_MULTSYS_GEN
def RING_ORDER_DIVIDES_MAXIMAL_MULTSYS : thm := BRingOrder.RING_ORDER_DIVIDES_MAXIMAL_MULTSYS
def RING_ORDER_DIVIDES_MAXIMAL : thm := BRingOrder.RING_ORDER_DIVIDES_MAXIMAL
def RING_ORDER_DIVIDES_MAXIMAL_UNIT : thm := BRingOrder.RING_ORDER_DIVIDES_MAXIMAL_UNIT
def INTEGRAL_DOMAIN_ORDER_DIVIDES_MAXIMAL : thm := BRingOrder.INTEGRAL_DOMAIN_ORDER_DIVIDES_MAXIMAL
def FINITE_RING_MULTSYS_CYCLIC : thm := BRingOrder.FINITE_RING_MULTSYS_CYCLIC
def FINITE_INTEGRAL_DOMAIN_CYCLIC : thm := BRingOrder.FINITE_INTEGRAL_DOMAIN_CYCLIC
def FIELD_NONZERO_NONINVOLUTION : thm := BRingOrder.FIELD_NONZERO_NONINVOLUTION
def FINITE_FIELD_CARD_ROOTS_OF_UNITY : thm := BRingOrder.FINITE_FIELD_CARD_ROOTS_OF_UNITY
def INTEGRAL_DOMAIN_ROOTS_OF_UNITY_CYCLIC : thm := BRingOrder.INTEGRAL_DOMAIN_ROOTS_OF_UNITY_CYCLIC
def ROOTS_OF_UNITY_RING_ORDER : thm := BRingOrder.ROOTS_OF_UNITY_RING_ORDER
def ROOTS_OF_UNITY_RING_ORDER_DIVISOR : thm := BRingOrder.ROOTS_OF_UNITY_RING_ORDER_DIVISOR
def RING_ENDOMORPHISM_ROOT_OF_UNITY : thm := BRingOrder.RING_ENDOMORPHISM_ROOT_OF_UNITY
def ROOTS_OF_UNITY_HAS_SIZE_NONZERO : thm := BRingOrder.ROOTS_OF_UNITY_HAS_SIZE_NONZERO
def ROOTS_OF_UNITY_HAS_SIZE_PRIMITIVE : thm := BRingOrder.ROOTS_OF_UNITY_HAS_SIZE_PRIMITIVE
def RING_ORDER_MONOMORPHIC_IMAGE : thm := BRingOrder.RING_ORDER_MONOMORPHIC_IMAGE
def ROOTS_OF_UNITY_HAS_SIZE_DIVISOR : thm := BRingOrder.ROOTS_OF_UNITY_HAS_SIZE_DIVISOR
def ROOTS_OF_UNITY_EQ_MOD_IDEAL : thm := BRingOrder.ROOTS_OF_UNITY_EQ_MOD_IDEAL
def PRIMITIVE_ROOT_OF_UNITY_EXISTS : thm := BRingOrder.PRIMITIVE_ROOT_OF_UNITY_EXISTS

-- Frobenius
def RING_ENDOMORPHISM_FROBENIUS : thm := BFrobenius.RING_ENDOMORPHISM_FROBENIUS
def RING_MONOMORPHISM_FROBENIUS_GEN : thm := BFrobenius.RING_MONOMORPHISM_FROBENIUS_GEN
def RING_MONOMORPHISM_FROBENIUS : thm := BFrobenius.RING_MONOMORPHISM_FROBENIUS
def ROOTS_OF_UNITY_HAS_SIZE_IMP_CHAR : thm := BFrobenius.ROOTS_OF_UNITY_HAS_SIZE_IMP_CHAR
def RING_AUTOMORPHISM_FROBENIUS : thm := BFrobenius.RING_AUTOMORPHISM_FROBENIUS
def FROBENIUS_FIXED : thm := BFrobenius.FROBENIUS_FIXED
def RING_CHAR_POWSER_RING : thm := BFrobenius.RING_CHAR_POWSER_RING
def RING_CHAR_POLY_RING : thm := BFrobenius.RING_CHAR_POLY_RING
def RING_ENDOMORPHISM_FROBENIUS_ITERATE : thm := BFrobenius.RING_ENDOMORPHISM_FROBENIUS_ITERATE
def RING_MONOMORPHISM_FROBENIUS_ITERATE : thm := BFrobenius.RING_MONOMORPHISM_FROBENIUS_ITERATE
def FROBENIUS_ADD_POWER : thm := BFrobenius.FROBENIUS_ADD_POWER
def FROBENIUS_SUM_POWER : thm := BFrobenius.FROBENIUS_SUM_POWER

-- IntegralDomainRule
def INTEGRAL_DOMAIN_RULE : term → IO (Except String thm) := fun t => (BIntegralDomainRule.INTEGRAL_DOMAIN_RULE t).run
def FIELD_TAC : HolCore.Tactics.tactic := fun g => BIntegralDomainRule.FIELD_TAC g
def FIELD_INV_EQ_0 : thm := BIntegralDomainRule.FIELD_INV_EQ_0
def FIELD_DIV_EQ_0 : thm := BIntegralDomainRule.FIELD_DIV_EQ_0

-- RingPullDiv
def RING_PULL_DIV : thm := BRingPullDiv.RING_PULL_DIV
def RING_PULL_DIV_CONV := BRingPullDiv.RING_PULL_DIV_CONV
def RING_PULL_DIV_TAC : HolCore.Tactics.tactic := fun g => BRingPullDiv.RING_PULL_DIV_TAC g











































































/-- `needs "Library/ringtheory.ml"`: already done by importing this module. -/
def ensureRingTheory : IO Unit := pure ()

end SessionLibrary.RingTheory
