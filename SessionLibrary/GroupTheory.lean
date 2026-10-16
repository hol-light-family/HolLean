/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/grouptheory.ml.                       -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/GroupTheory.lean

  The `unsafe` half of the grouptheory.ml translation: it supplies HolLibrary.GroupTheory's
  dependencies from Session and SessionLibrary.Frag, SessionLibrary.Card, SessionLibrary.Prime, builds the bundles once, in order,
  and exports every name under its HOL Light name.  `ensureGroupTheory` is
  `needs "Library/grouptheory.ml"` (which first does `needs "Library/frag.ml"`, `needs "Library/card.ml"`, `needs "Library/prime.ml"`).

  The blocks between `@@CORE` and `@@EXPORTS` markers are generated from
  HolLibrary/GroupTheory.lean by tools/grouptheorydiff/gen_session.py and scope.py
  (bookkeeping only: field-by-field copies and accessors).
-/

import Session
import HolLibrary.GroupTheory
import SessionLibrary.Frag
import SessionLibrary.Card
import SessionLibrary.Prime

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.GroupTheory

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨Session.sessionB, Session.sessionC, Session.sessionT⟩

-- @@CORE BEGIN
/-- The core theorems grouptheory.ml uses. -/
unsafe def core1 (_ : Unit) : HolLibrary.GroupTheory.CoreThms1 where
  ADD1 := Session.ADD1
  ADD_CLAUSES := Session.ADD_CLAUSES
  ADD_SYM := Session.ADD_SYM
  ALL := Session.listDefs.ALL
  ALL_MEM := Session.listThms1.ALL_MEM
  AND_FORALL_THM := Session.AND_FORALL_THM
  ARITH := Session.ARITH
  ARITH_EQ := Session.ARITH_EQ
  BETA_THM := Session.BETA_THM
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARD_CROSS := Session.CARD_CROSS
  CARD_DELETE := Session.CARD_DELETE
  CARD_EQ_0 := Session.CARD_EQ_0
  CARD_EQ_BIJECTION := Session.CARD_EQ_BIJECTION
  CARD_EQ_BIJECTIONS := Session.CARD_EQ_BIJECTIONS
  CARD_EQ_BIJECTIONS_SPECIAL := Session.CARD_EQ_BIJECTIONS_SPECIAL
  CARD_EQ_CARD := SessionLibrary.Card.«CARD_EQ_CARD»
  CARD_EQ_CARD_IMP := SessionLibrary.Card.«CARD_EQ_CARD_IMP»
  CARD_EQ_CONG := SessionLibrary.Card.«CARD_EQ_CONG»
  CARD_EQ_FINITE_SUBSETS := SessionLibrary.Card.«CARD_EQ_FINITE_SUBSETS»
  CARD_EQ_IMAGE := SessionLibrary.Card.«CARD_EQ_IMAGE»
  CARD_EQ_IMAGES := SessionLibrary.Card.«CARD_EQ_IMAGES»
  CARD_EQ_IMAGE_MUL_FIBRES := SessionLibrary.Card.«CARD_EQ_IMAGE_MUL_FIBRES»
  CARD_EQ_IMP_LE := SessionLibrary.Card.«CARD_EQ_IMP_LE»
  CARD_EQ_LIST_GEN := SessionLibrary.Card.«CARD_EQ_LIST_GEN»
  CARD_EQ_REFL := SessionLibrary.Card.«CARD_EQ_REFL»
  CARD_EQ_REFL_IMP := SessionLibrary.Card.«CARD_EQ_REFL_IMP»
  CARD_EQ_SYM := SessionLibrary.Card.«CARD_EQ_SYM»
  CARD_EQ_TRANS := SessionLibrary.Card.«CARD_EQ_TRANS»
  CARD_EXP_C := SessionLibrary.Card.«CARD_EXP_C»
  CARD_EXP_FINITE_EQ := SessionLibrary.Card.«CARD_EXP_FINITE_EQ»
  CARD_FINITE_CONG := SessionLibrary.Card.«CARD_FINITE_CONG»
  CARD_HAS_SIZE_CONG := SessionLibrary.Card.«CARD_HAS_SIZE_CONG»
  CARD_IMAGE_INJ := Session.CARD_IMAGE_INJ
  CARD_IMAGE_LE := Session.CARD_IMAGE_LE
  CARD_LE_ANTISYM := SessionLibrary.Card.«CARD_LE_ANTISYM»
  CARD_LE_COUNTABLE_INFINITE := SessionLibrary.Card.«CARD_LE_COUNTABLE_INFINITE»
  CARD_LE_EQ_SUBSET_UNIV := SessionLibrary.Card.«CARD_LE_EQ_SUBSET_UNIV»
  CARD_LE_FINITE := SessionLibrary.Card.«CARD_LE_FINITE»
  CARD_LE_FINITE_INFINITE := SessionLibrary.Card.«CARD_LE_FINITE_INFINITE»
  CARD_LE_IMAGE := SessionLibrary.Card.«CARD_LE_IMAGE»
  CARD_LE_RESTRICTED_FUNSPACE := SessionLibrary.Card.«CARD_LE_RESTRICTED_FUNSPACE»
  CARD_LE_SUBSET := SessionLibrary.Card.«CARD_LE_SUBSET»
  CARD_LE_TRANS := SessionLibrary.Card.«CARD_LE_TRANS»
  CARD_LE_UNIV := SessionLibrary.Card.«CARD_LE_UNIV»
  CARD_MUL_ABSORB := SessionLibrary.Card.«CARD_MUL_ABSORB»
  CARD_MUL_C := SessionLibrary.Card.«CARD_MUL_C»
  CARD_MUL_CONG := SessionLibrary.Card.«CARD_MUL_CONG»
  CARD_MUL_FINITE := SessionLibrary.Card.«CARD_MUL_FINITE»
  CARD_MUL_FINITE_EQ := SessionLibrary.Card.«CARD_MUL_FINITE_EQ»
  CARD_MUL_SYM := SessionLibrary.Card.«CARD_MUL_SYM»
  CARD_NUMSEG_1 := Session.CARD_NUMSEG_1
  CARD_NUMSEG_LT := Session.CARD_NUMSEG_LT
  CARD_PSUBSET := Session.CARD_PSUBSET
  CARD_SING := Session.CARD_SING
  CARD_SUBSET := Session.CARD_SUBSET
  CARD_SUBSET_EQ := Session.CARD_SUBSET_EQ
  CARD_SUBSET_LE := Session.CARD_SUBSET_LE
  CARD_UNIONS := Session.CARD_UNIONS
  CARTESIAN_PRODUCT_AS_RESTRICTIONS := Session.CARTESIAN_PRODUCT_AS_RESTRICTIONS
  CARTESIAN_PRODUCT_EQ := Session.CARTESIAN_PRODUCT_EQ
  CARTESIAN_PRODUCT_EQ_EMPTY := Session.CARTESIAN_PRODUCT_EQ_EMPTY
  CARTESIAN_PRODUCT_SINGS_GEN := Session.CARTESIAN_PRODUCT_SINGS_GEN
  COND_CLAUSES := Session.COND_CLAUSES
  COND_ID := Session.COND_ID
  COND_RAND := Session.COND_RAND
  COND_RATOR := Session.COND_RATOR
  COND_SWAP := Session.COND_SWAP
  CONG_NSUM := Session.CONG_NSUM
  CONJ_ASSOC := Session.CONJ_ASSOC
/-- The core theorems grouptheory.ml uses. -/
unsafe def core10 (_ : Unit) : HolLibrary.GroupTheory.CoreThms10 where
/-- The core theorems grouptheory.ml uses. -/
unsafe def core11 (_ : Unit) : HolLibrary.GroupTheory.CoreThms11 where
/-- The core theorems grouptheory.ml uses. -/
unsafe def core12 (_ : Unit) : HolLibrary.GroupTheory.CoreThms12 where
/-- The core theorems grouptheory.ml uses. -/
unsafe def core13 (_ : Unit) : HolLibrary.GroupTheory.CoreThms13 where
/-- The core theorems grouptheory.ml uses. -/
unsafe def core14 (_ : Unit) : HolLibrary.GroupTheory.CoreThms14 where
/-- The core theorems grouptheory.ml uses. -/
unsafe def core15 (_ : Unit) : HolLibrary.GroupTheory.CoreThms15 where
/-- The core theorems grouptheory.ml uses. -/
unsafe def core16 (_ : Unit) : HolLibrary.GroupTheory.CoreThms16 where
/-- The core theorems grouptheory.ml uses. -/
unsafe def core2 (_ : Unit) : HolLibrary.GroupTheory.CoreThms2 where
  CONJ_SYM := Session.CONJ_SYM
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  COPRIME_GCD := SessionLibrary.Prime.«COPRIME_GCD»
  COPRIME_LEXP := SessionLibrary.Prime.«COPRIME_LEXP»
  COPRIME_PRIME_EQ := SessionLibrary.Prime.«COPRIME_PRIME_EQ»
  COUNTABLE := Session.COUNTABLE
  COUNTABLE_CARTESIAN_PRODUCT := SessionLibrary.Card.«COUNTABLE_CARTESIAN_PRODUCT»
  COUNTABLE_IMAGE := SessionLibrary.Card.«COUNTABLE_IMAGE»
  COUNTABLE_SUBSET := SessionLibrary.Card.«COUNTABLE_SUBSET»
  CROSS := Session.CROSS
  CROSS_EMPTY := Session.CROSS_EMPTY
  CROSS_EQ := Session.CROSS_EQ
  CROSS_SING := Session.CROSS_SING
  DELETE_SUBSET := Session.DELETE_SUBSET
  DEST_FRAG_ADD := SessionLibrary.Frag.«DEST_FRAG_ADD»
  DEST_FRAG_OF := SessionLibrary.Frag.«DEST_FRAG_OF»
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DIFF_EQ_EMPTY := Session.DIFF_EQ_EMPTY
  DIFF_UNIONS_PAIRWISE_DISJOINT := Session.DIFF_UNIONS_PAIRWISE_DISJOINT
  DISJOINT := Session.DISJOINT
  DISJOINT_EMPTY_REFL := Session.DISJOINT_EMPTY_REFL
  DISJOINT_SING := Session.DISJOINT_SING
  DIVIDES_0 := SessionLibrary.Prime.«DIVIDES_0»
  DIVIDES_ANTISYM := Session.DIVIDES_ANTISYM
  DIVIDES_DIVIDES_DIV := Session.DIVIDES_DIVIDES_DIV
  DIVIDES_DIV_MULT := Session.DIVIDES_DIV_MULT
  DIVIDES_GCD_RIGHT := SessionLibrary.Prime.«DIVIDES_GCD_RIGHT»
  DIVIDES_INDEX := SessionLibrary.Prime.«DIVIDES_INDEX»
  DIVIDES_LCM_LEFT := SessionLibrary.Prime.«DIVIDES_LCM_LEFT»
  DIVIDES_LE := Session.DIVIDES_LE
  DIVIDES_MOD := Session.DIVIDES_MOD
  DIVIDES_NSUM := SessionLibrary.Prime.«DIVIDES_NSUM»
  DIVIDES_ONE := Session.DIVIDES_ONE
  DIVIDES_PRIMEPOW := SessionLibrary.Prime.«DIVIDES_PRIMEPOW»
  DIVIDES_PRIME_PRIME := SessionLibrary.Prime.«DIVIDES_PRIME_PRIME»
  DIVIDES_REFL := SessionLibrary.Prime.«DIVIDES_REFL»
  DIVIDES_SUB_1 := SessionLibrary.Prime.«DIVIDES_SUB_1»
  DIVIDES_TRANS := SessionLibrary.Prime.«DIVIDES_TRANS»
  DIVIDES_ZERO := SessionLibrary.Prime.«DIVIDES_ZERO»
  DIVISION := Session.DIVISION
  DIV_1 := Session.DIV_1
  DIV_EQ_0 := Session.DIV_EQ_0
  DIV_MULT := Session.DIV_MULT
  DIV_REFL := Session.DIV_REFL
  DIV_UNIQ := Session.DIV_UNIQ
  EMPTY_GSPEC := Session.EMPTY_GSPEC
  EMPTY_NUMSEG := Session.EMPTY_NUMSEG
  EMPTY_SUBSET := Session.EMPTY_SUBSET
  EMPTY_UNIONS := Session.EMPTY_UNIONS
  EQ_C_BIJECTIONS := SessionLibrary.Card.«EQ_C_BIJECTIONS»
  EQ_C_INVOLUTION := SessionLibrary.Card.«EQ_C_INVOLUTION»
  EQ_EXP := Session.EQ_EXP
  EQ_IMP := Session.EQ_IMP
  EQ_SYM_EQ := Session.EQ_SYM_EQ
  EQ_TRANS := Session.EQ_TRANS
  ETA_AX := Session.ETA_AX
  EXISTS_IN_GSPEC := Session.EXISTS_IN_GSPEC
  EXISTS_IN_IMAGE := Session.EXISTS_IN_IMAGE
  EXISTS_PAIR_THM := Session.EXISTS_PAIR_THM
  EXISTS_REFL := Session.EXISTS_REFL
  EXISTS_UNIQUE := Session.EXISTS_UNIQUE
  EXISTS_UNIQUE_DEF := Session.EXISTS_UNIQUE_DEF
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXISTS_UNPAIR_THM := Session.EXISTS_UNPAIR_THM
  EXP := Session.EXP
  EXP_1 := Session.EXP_1
  EXP_ADD := Session.EXP_ADD
  EXP_C := SessionLibrary.Card.«EXP_C»
  EXP_EQ_0 := Session.EXP_EQ_0
  EXP_EQ_1 := Session.EXP_EQ_1
/-- The core theorems grouptheory.ml uses. -/
unsafe def core3 (_ : Unit) : HolLibrary.GroupTheory.CoreThms3 where
  EXTENSION := Session.EXTENSION
  EXTENSIONAL := Session.EXTENSIONAL
  EXTENSIONAL_UNIV := Session.EXTENSIONAL_UNIV
  FINITE_BOOL := Session.FINITE_BOOL
  FINITE_CARTESIAN_PRODUCT := SessionLibrary.Card.«FINITE_CARTESIAN_PRODUCT»
  FINITE_CROSS := Session.FINITE_CROSS
  FINITE_CROSS_EQ := Session.FINITE_CROSS_EQ
  FINITE_DELETE := Session.FINITE_DELETE
  FINITE_DIFF := Session.FINITE_DIFF
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_FRAG_SUPPORT := SessionLibrary.Frag.«FINITE_FRAG_SUPPORT»
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_IMAGE_EQ := Session.FINITE_IMAGE_EQ
  FINITE_IMAGE_GEN := Session.FINITE_IMAGE_GEN
  FINITE_IMAGE_INJ_EQ := Session.FINITE_IMAGE_INJ_EQ
  FINITE_IMP_COUNTABLE := SessionLibrary.Card.«FINITE_IMP_COUNTABLE»
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_INTER := Session.FINITE_INTER
  FINITE_INT_SEG := Session.FINITE_INT_SEG
  FINITE_NUMSEG := Session.FINITE_NUMSEG
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_POWERSET := Session.FINITE_POWERSET
  FINITE_POWERSET_EQ := Session.FINITE_POWERSET_EQ
  FINITE_PRODUCT_DEPENDENT := Session.FINITE_PRODUCT_DEPENDENT
  FINITE_RESTRICT := Session.FINITE_RESTRICT
  FINITE_RESTRICTED_SUBSETS := Session.FINITE_RESTRICTED_SUBSETS
  FINITE_SING := Session.FINITE_SING
  FINITE_SPECIAL_DIVISORS := SessionLibrary.Prime.«FINITE_SPECIAL_DIVISORS»
  FINITE_SUBSET := Session.FINITE_SUBSET
  FINITE_SUBSET_UNIONS_DIRECTED_EQ := Session.FINITE_SUBSET_UNIONS_DIRECTED_EQ
  FINITE_UNION := Session.FINITE_UNION
  FINITE_UNIONS := Session.FINITE_UNIONS
  FLD_num := SessionLibrary.Wo.«FLD_num»
  FORALL_AND_THM := Session.FORALL_AND_THM
  FORALL_CARTESIAN_PRODUCT_ELEMENTS := Session.FORALL_CARTESIAN_PRODUCT_ELEMENTS
  FORALL_CARTESIAN_PRODUCT_ELEMENTS_EQ := Session.FORALL_CARTESIAN_PRODUCT_ELEMENTS_EQ
  FORALL_INT_CASES := Session.FORALL_INT_CASES
  FORALL_IN_CROSS := Session.FORALL_IN_CROSS
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_IN_IMAGE_2 := Session.FORALL_IN_IMAGE_2
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  FORALL_IN_UNION := Session.FORALL_IN_UNION
  FORALL_IN_UNIONS := Session.FORALL_IN_UNIONS
  FORALL_PAIR_FUN_THM := Session.FORALL_PAIR_FUN_THM
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  FORALL_SMALL_SUBSET_IMAGE := Session.FORALL_SMALL_SUBSET_IMAGE
  FORALL_UNWIND_THM1 := Session.FORALL_UNWIND_THM1
  FORALL_UNWIND_THM2 := Session.FORALL_UNWIND_THM2
  FRAG_EQ := SessionLibrary.Frag.«FRAG_EQ»
  FRAG_INDUCTION := SessionLibrary.Frag.«FRAG_INDUCTION»
  FRAG_OF_EQ := SessionLibrary.Frag.«FRAG_OF_EQ»
  FRAG_OF_NONZERO := SessionLibrary.Frag.«FRAG_OF_NONZERO»
  FRAG_SUPPORT_0 := SessionLibrary.Frag.«FRAG_SUPPORT_0»
  FRAG_SUPPORT_ADD := SessionLibrary.Frag.«FRAG_SUPPORT_ADD»
  FRAG_SUPPORT_CMUL := SessionLibrary.Frag.«FRAG_SUPPORT_CMUL»
  FRAG_SUPPORT_EQ_EMPTY := SessionLibrary.Frag.«FRAG_SUPPORT_EQ_EMPTY»
  FRAG_SUPPORT_NEG := SessionLibrary.Frag.«FRAG_SUPPORT_NEG»
  FRAG_SUPPORT_OF := SessionLibrary.Frag.«FRAG_SUPPORT_OF»
  FRAG_SUPPORT_SUB := SessionLibrary.Frag.«FRAG_SUPPORT_SUB»
  FRAG_SUPPORT_SUM := SessionLibrary.Frag.«FRAG_SUPPORT_SUM»
  FUNCTION_FACTORS_LEFT_GEN := Session.FUNCTION_FACTORS_LEFT_GEN
  FUN_EQ_THM := Session.FUN_EQ_THM
  FUN_IN_IMAGE := Session.FUN_IN_IMAGE
  GCD := Session.GCD
  GCD_0 := SessionLibrary.Prime.«GCD_0»
  GCD_1 := SessionLibrary.Prime.«GCD_1»
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_0 := Session.HAS_SIZE_0
/-- The core theorems grouptheory.ml uses. -/
unsafe def core4 (_ : Unit) : HolLibrary.GroupTheory.CoreThms4 where
  HAS_SIZE_IMAGE_INJ := Session.HAS_SIZE_IMAGE_INJ
  IMAGE := Session.IMAGE
  IMAGE_CLAUSES := Session.IMAGE_CLAUSES
  IMAGE_EQ := Session.IMAGE_EQ
  IMAGE_EQ_EMPTY := Session.IMAGE_EQ_EMPTY
  IMAGE_FST_CROSS := Session.IMAGE_FST_CROSS
  IMAGE_I := Session.IMAGE_I
  IMAGE_ID := Session.IMAGE_ID
  IMAGE_PAIRED_CROSS := Session.IMAGE_PAIRED_CROSS
  IMAGE_PROJECTION_CARTESIAN_PRODUCT := Session.IMAGE_PROJECTION_CARTESIAN_PRODUCT
  IMAGE_SND_CROSS := Session.IMAGE_SND_CROSS
  IMAGE_SUBSET := Session.IMAGE_SUBSET
  IMAGE_o := Session.IMAGE_o
  IMP_CONJ := Session.IMP_CONJ
  IMP_CONJ_ALT := Session.IMP_CONJ_ALT
  IMP_IMP := Session.IMP_IMP
  IN := Session.IN
  INDEX_DECOMPOSITION := SessionLibrary.Prime.«INDEX_DECOMPOSITION»
  INFINITE := Session.INFINITE
  INFINITE_IMAGE := Session.INFINITE_IMAGE
  INFINITE_IMAGE_INJ := Session.INFINITE_IMAGE_INJ
  INFINITE_NONEMPTY := Session.INFINITE_NONEMPTY
  INFINITE_SUPERSET := Session.INFINITE_SUPERSET
  INJECTIVE_ON_ALT := Session.INJECTIVE_ON_ALT
  INJECTIVE_ON_LEFT_INVERSE := Session.INJECTIVE_ON_LEFT_INVERSE
  INSERT_SUBSET := Session.INSERT_SUBSET
  INTERS_2 := Session.INTERS_2
  INTERS_ANTIMONO_GEN := Session.INTERS_ANTIMONO_GEN
  INTERS_GSPEC := Session.INTERS_GSPEC
  INTERS_SUBSET_STRONG := Session.INTERS_SUBSET_STRONG
  INTER_COMM := Session.INTER_COMM
  INTER_CROSS := Session.INTER_CROSS
  INTER_EMPTY := Session.INTER_EMPTY
  INTER_SUBSET := Session.INTER_SUBSET
  INT_ABS := Session.INT_ABS
  INT_ABS_NEG := Session.INT_ABS_NEG
  INT_ABS_NUM := Session.INT_ABS_NUM
  INT_ABS_NZ := Session.INT_ABS_NZ
  INT_ABS_POS := Session.INT_ABS_POS
  INT_ABS_ZERO := Session.INT_ABS_ZERO
  INT_ADD_ASSOC := Session.INT_ADD_ASSOC
  INT_ADD_LID := Session.INT_ADD_LID
  INT_ADD_LINV := Session.INT_ADD_LINV
  INT_ADD_RDISTRIB := Session.INT_ADD_RDISTRIB
  INT_ADD_REM := Session.INT_ADD_REM
  INT_ADD_RID := Session.INT_ADD_RID
  INT_ADD_RINV := Session.INT_ADD_RINV
  INT_ADD_SYM := Session.INT_ADD_SYM
  INT_CONG_LREM := Session.INT_CONG_LREM
  INT_COUNTABLE := SessionLibrary.Card.«INT_COUNTABLE»
  INT_DIVISION := Session.INT_DIVISION
  INT_DIVISION_SIMP := Session.INT_DIVISION_SIMP
  INT_ENTIRE := Session.INT_ENTIRE
  INT_EXISTS_POS := Session.INT_EXISTS_POS
  INT_FORALL_POS := Session.INT_FORALL_POS
  INT_IMAGE := Session.INT_IMAGE
  INT_LE_REFL := Session.INT_LE_REFL
  INT_LT_IMP_LE := Session.INT_LT_IMP_LE
  INT_LT_REM := Session.INT_LT_REM
  INT_LT_REM_EQ := Session.INT_LT_REM_EQ
  INT_MUL_ASSOC := Session.INT_MUL_ASSOC
  INT_MUL_DIV_EQ := Session.INT_MUL_DIV_EQ
  INT_MUL_LID := Session.INT_MUL_LID
  INT_MUL_LNEG := Session.INT_MUL_LNEG
  INT_MUL_LZERO := Session.INT_MUL_LZERO
  INT_MUL_RID := Session.INT_MUL_RID
  INT_MUL_RNEG := Session.INT_MUL_RNEG
  INT_MUL_RZERO := Session.INT_MUL_RZERO
  INT_MUL_SYM := Session.INT_MUL_SYM
  INT_NEG_0 := Session.INT_NEG_0
/-- The core theorems grouptheory.ml uses. -/
unsafe def core5 (_ : Unit) : HolLibrary.GroupTheory.CoreThms5 where
  INT_NEG_ADD := Session.INT_NEG_ADD
  INT_NEG_EQ_0 := Session.INT_NEG_EQ_0
  INT_NEG_NEG := Session.INT_NEG_NEG
  INT_OF_NUM_ADD := Session.INT_OF_NUM_ADD
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_LE := Session.INT_OF_NUM_LE
  INT_OF_NUM_LT := Session.INT_OF_NUM_LT
  INT_OF_NUM_MUL := Session.INT_OF_NUM_MUL
  INT_OF_NUM_OF_INT := Session.INT_OF_NUM_OF_INT
  INT_OF_NUM_REM := Session.INT_OF_NUM_REM
  INT_OF_NUM_SUB := Session.INT_OF_NUM_SUB
  INT_OF_NUM_SUC := Session.INT_OF_NUM_SUC
  INT_POS := Session.INT_POS
  INT_REM_0 := Session.INT_REM_0
  INT_REM_1 := Session.INT_REM_1
  INT_REM_DIV := Session.INT_REM_DIV
  INT_REM_EQ := Session.INT_REM_EQ
  INT_REM_EQ_0 := Session.INT_REM_EQ_0
  INT_REM_EQ_SELF := Session.INT_REM_EQ_SELF
  INT_REM_LT := Session.INT_REM_LT
  INT_REM_MOD_SELF := Session.INT_REM_MOD_SELF
  INT_REM_POS_EQ := Session.INT_REM_POS_EQ
  INT_REM_REM := Session.INT_REM_REM
  INT_REM_REM_MUL := Session.INT_REM_REM_MUL
  INT_REM_ZERO := Session.INT_REM_ZERO
  INT_SUB := Session.INT_SUB
  INT_SUB_0 := Session.INT_SUB_0
  INT_SUB_LT := Session.INT_SUB_LT
  INT_WLOG_LT := Session.INT_WLOG_LT
  IN_CARTESIAN_PRODUCT := Session.IN_CARTESIAN_PRODUCT
  IN_CROSS := Session.IN_CROSS
  IN_DELETE := Session.IN_DELETE
  IN_DIFF := Session.IN_DIFF
  IN_ELIM_PAIR_THM := Session.IN_ELIM_PAIR_THM
  IN_ELIM_THM := Session.IN_ELIM_THM
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
  ITERATE_CLAUSES_GEN := Session.ITERATE_CLAUSES_GEN
  ITERATE_CLOSED := Session.ITERATE_CLOSED
  ITERATE_EQ := Session.ITERATE_EQ
  ITERATE_EXPAND_CASES := Session.ITERATE_EXPAND_CASES
  ITERATE_LCM_DIVIDES_GEN := SessionLibrary.Prime.«ITERATE_LCM_DIVIDES_GEN»
  ITERATE_LCM_EQ_0_GEN := SessionLibrary.Prime.«ITERATE_LCM_EQ_0_GEN»
  ITERATE_OP_GEN := Session.ITERATE_OP_GEN
  ITERATE_SING := Session.ITERATE_SING
  ITERATE_SUPERSET := Session.ITERATE_SUPERSET
  ITERATO_CLAUSES := Session.ITERATO_CLAUSES
  ITERATO_CLAUSES_EXISTS := Session.ITERATO_CLAUSES_EXISTS
  ITERATO_CLOSED := Session.ITERATO_CLOSED
  ITERATO_EQ := Session.ITERATO_EQ
  ITERATO_EXPAND_CASES := Session.ITERATO_EXPAND_CASES
  ITERATO_SUPPORT := Session.ITERATO_SUPPORT
  I_DEF := Session.I_DEF
  LAMBDA_PAIR := Session.LAMBDA_PAIR
  LAMBDA_PAIR_THM := Session.LAMBDA_PAIR_THM
  LCM := SessionLibrary.Prime.«LCM»
  LCM_0 := SessionLibrary.Prime.«LCM_0»
  LCM_COPRIME_DECOMP := SessionLibrary.Prime.«LCM_COPRIME_DECOMP»
  LCM_DIVIDES := SessionLibrary.Prime.«LCM_DIVIDES»
  LCM_DIVIDES_MUL := SessionLibrary.Prime.«LCM_DIVIDES_MUL»
  LCM_ZERO := SessionLibrary.Prime.«LCM_ZERO»
/-- The core theorems grouptheory.ml uses. -/
unsafe def core6 (_ : Unit) : HolLibrary.GroupTheory.CoreThms6 where
  LE := Session.LE
  LEFT_AND_EXISTS_THM := Session.LEFT_AND_EXISTS_THM
  LEFT_EXISTS_AND_THM := Session.LEFT_EXISTS_AND_THM
  LEFT_FORALL_IMP_THM := Session.LEFT_FORALL_IMP_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LET_TRANS := Session.LET_TRANS
  LE_0 := Session.LE_0
  LE_1 := Session.LE_1
  LE_ANTISYM := Session.LE_ANTISYM
  LE_C := Session.LE_C
  LE_INDEX := SessionLibrary.Prime.«LE_INDEX»
  LE_LT := Session.LE_LT
  LE_REFL := Session.LE_REFL
  LE_TRANS := Session.LE_TRANS
  LT := Session.LT
  LTE_TRANS := Session.LTE_TRANS
  LT_EXISTS := Session.LT_EXISTS
  LT_IMP_LE := Session.LT_IMP_LE
  LT_NZ := Session.LT_NZ
  LT_REFL := Session.LT_REFL
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MONOIDAL_FRAG_ADD := SessionLibrary.Frag.«MONOIDAL_FRAG_ADD»
  MONO_AND := Session.MONO_AND
  MONO_EXISTS := Session.MONO_EXISTS
  MONO_FORALL := Session.MONO_FORALL
  MONO_OR := Session.MONO_OR
  MULT_ASSOC := Session.MULT_ASSOC
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_EQ_0 := Session.MULT_EQ_0
  MULT_SYM := Session.MULT_SYM
  NEUTRAL_FRAG_ADD := SessionLibrary.Frag.«NEUTRAL_FRAG_ADD»
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NOT_INSERT_EMPTY := Session.NOT_INSERT_EMPTY
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NOT_LE := Session.NOT_LE
  NOT_LT := Session.NOT_LT
  NOT_SUC := Session.NOT_SUC
  NSUM_CONST := Session.NSUM_CONST
  NSUM_RESTRICT_SET := Session.NSUM_RESTRICT_SET
  NUMSEG_CLAUSES := Session.NUMSEG_CLAUSES
  NUMSEG_LREC := Session.NUMSEG_LREC
  NUMSEG_RREC := Session.NUMSEG_RREC
  NUMSEG_SING := Session.NUMSEG_SING
  NUM_GCD := Session.NUM_GCD
  NUM_OF_INT_OF_NUM := Session.NUM_OF_INT_OF_NUM
  ONE_OR_PRIME := Session.ONE_OR_PRIME
  ONE_OR_PRIME_DIVIDES_OR_COPRIME := Session.ONE_OR_PRIME_DIVIDES_OR_COPRIME
  PAIR := Session.PAIR
  PAIRWISE_IMAGE := Session.PAIRWISE_IMAGE
  PAIRWISE_IMP := Session.PAIRWISE_IMP
  PAIRWISE_MONO := Session.PAIRWISE_MONO
  PAIR_EQ := Session.PAIR_EQ
  PRIMEPOW_DIVIDES_INDEX := SessionLibrary.Prime.«PRIMEPOW_DIVIDES_INDEX»
  PRIMES_INFINITE := SessionLibrary.Prime.«PRIMES_INFINITE»
  PRIME_0 := SessionLibrary.Prime.«PRIME_0»
  PRIME_1 := SessionLibrary.Prime.«PRIME_1»
  PRIME_COPRIME_EQ := SessionLibrary.Prime.«PRIME_COPRIME_EQ»
  PRIME_DIVEXP_EQ := SessionLibrary.Prime.«PRIME_DIVEXP_EQ»
  PRIME_DIVIDES_ITERATE_LCM_GEN := SessionLibrary.Prime.«PRIME_DIVIDES_ITERATE_LCM_GEN»
  PRIME_DIVIDES_LCM := SessionLibrary.Prime.«PRIME_DIVIDES_LCM»
  PRIME_DIVPROD := SessionLibrary.Prime.«PRIME_DIVPROD»
  PRIME_DIVPROD_EQ := SessionLibrary.Prime.«PRIME_DIVPROD_EQ»
  PRIME_FACTOR := SessionLibrary.Prime.«PRIME_FACTOR»
  PRIME_IMP_NZ := SessionLibrary.Prime.«PRIME_IMP_NZ»
  PRIME_POWER_EXISTS := SessionLibrary.Prime.«PRIME_POWER_EXISTS»
  PSUBSET := Session.PSUBSET
  RESTRICTION := Session.RESTRICTION
  RESTRICTION_EXTENSION := Session.RESTRICTION_EXTENSION
/-- The core theorems grouptheory.ml uses. -/
unsafe def core7 (_ : Unit) : HolLibrary.GroupTheory.CoreThms7 where
  RESTRICTION_IN_CARTESIAN_PRODUCT := Session.RESTRICTION_IN_CARTESIAN_PRODUCT
  RESTRICTION_IN_EXTENSIONAL := Session.RESTRICTION_IN_EXTENSIONAL
  RESTRICTION_THM := Session.RESTRICTION_THM
  RESTRICTION_UNIQUE := Session.RESTRICTION_UNIQUE
  RESTRICTION_UNIQUE_ALT := Session.RESTRICTION_UNIQUE_ALT
  RIGHT_AND_EXISTS_THM := Session.RIGHT_AND_EXISTS_THM
  RIGHT_EXISTS_AND_THM := Session.RIGHT_EXISTS_AND_THM
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RIGHT_IMP_EXISTS_THM := Session.RIGHT_IMP_EXISTS_THM
  RIGHT_IMP_FORALL_THM := Session.RIGHT_IMP_FORALL_THM
  SELECT_UNIQUE := Session.SELECT_UNIQUE
  SIMPLE_IMAGE := Session.SIMPLE_IMAGE
  SIMPLE_IMAGE_GEN := Session.SIMPLE_IMAGE_GEN
  SING_GSPEC := Session.SING_GSPEC
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUBSET_ANTISYM_EQ := Session.SUBSET_ANTISYM_EQ
  SUBSET_CARD_EQ := Session.SUBSET_CARD_EQ
  SUBSET_CARTESIAN_PRODUCT := Session.SUBSET_CARTESIAN_PRODUCT
  SUBSET_CROSS := Session.SUBSET_CROSS
  SUBSET_IMAGE := Session.SUBSET_IMAGE
  SUBSET_INTER := Session.SUBSET_INTER
  SUBSET_INTERS := Session.SUBSET_INTERS
  SUBSET_REFL := Session.SUBSET_REFL
  SUBSET_RESTRICT := Session.SUBSET_RESTRICT
  SUBSET_TRANS := Session.SUBSET_TRANS
  SUBSET_UNION := Session.SUBSET_UNION
  SUBSET_UNIONS := Session.SUBSET_UNIONS
  SUBSET_UNIV := Session.SUBSET_UNIV
  SUB_0 := Session.SUB_0
  SUB_ADD := Session.SUB_ADD
  SUB_REFL := Session.SUB_REFL
  SUC_SUB1 := Session.SUC_SUB1
  SURJECTIVE_IFF_INJECTIVE := Session.SURJECTIVE_IFF_INJECTIVE
  SURJECTIVE_IFF_INJECTIVE_GEN := Session.SURJECTIVE_IFF_INJECTIVE_GEN
  SURJECTIVE_ON_RIGHT_INVERSE := Session.SURJECTIVE_ON_RIGHT_INVERSE
  SWAP_EXISTS_THM := Session.SWAP_EXISTS_THM
  SWAP_FORALL_THM := Session.SWAP_FORALL_THM
  UNIONS_0 := Session.UNIONS_0
  UNIONS_GSPEC := Session.UNIONS_GSPEC
  UNIONS_IMAGE := Session.UNIONS_IMAGE
  UNIONS_INSERT := Session.UNIONS_INSERT
  UNIONS_SINGS := Session.UNIONS_SINGS
  UNIONS_SUBSET := Session.UNIONS_SUBSET
  UNION_COMM := Session.UNION_COMM
  UNION_EMPTY := Session.UNION_EMPTY
  UNION_OVER_INTER := Session.UNION_OVER_INTER
  UNION_SUBSET := Session.UNION_SUBSET
  UNIV_NOT_EMPTY := Session.UNIV_NOT_EMPTY
  UNWIND_THM1 := Session.UNWIND_THM1
  UNWIND_THM2 := Session.UNWIND_THM2
  WF := Session.WF
  WF_FINITE := Session.WF_FINITE
  WLOG_LE := Session.WLOG_LE
  WLOG_LT := Session.WLOG_LT
  WO := SessionLibrary.Wo.«WO»
  WOSET_num := SessionLibrary.Wo.«WOSET_num»
  ZL_SUBSETS_UNIONS_NONEMPTY := SessionLibrary.Wo.«ZL_SUBSETS_UNIONS_NONEMPTY»
  cartesian_product := Session.cartesian_product
  divides := Session.divides
  eq_c := Session.eq_c
  frag_support := SessionLibrary.Frag.«frag_support»
  ge_c := Session.ge_c
  int_INFINITE := SessionLibrary.Card.«int_INFINITE»
  int_divides := Session.int_divides
  le_c := Session.le_c
  monoidal := Session.monoidal
  mul_c := SessionLibrary.Card.«mul_c»
/-- The core theorems grouptheory.ml uses. -/
unsafe def core8 (_ : Unit) : HolLibrary.GroupTheory.CoreThms8 where
  neutral := Session.neutral
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
  o_ASSOC := Session.o_ASSOC
  o_DEF := Session.o_DEF
  o_THM := Session.o_THM
  pairwise := Session.pairwise
  prime := Session.prime
  support := Session.support
  woset := SessionLibrary.Wo.«woset»
/-- The core theorems grouptheory.ml uses. -/
unsafe def core9 (_ : Unit) : HolLibrary.GroupTheory.CoreThms9 where
-- @@CORE END

/-- What grouptheory.ml uses from Session. -/
unsafe def deps (_ : Unit) : HolLibrary.GroupTheory.GroupTheoryDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  new_type_definition ty names th :=
    ExceptT.mk (Session.new_type_definition ty names.1 names.2 th)
  new_recursive_definition ax s := do
    ExceptT.mk (Session.new_recursive_definition ax (← HolLight.q s))
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  INT_ARITH t := ExceptT.mk (Session.INT_ARITH t)
  INT_ARITH_TAC := Session.INT_ARITH_TAC
  INTEGER_RULE t := ExceptT.mk (Session.INTEGER_RULE t)
  INTEGER_TAC := Session.INTEGER_TAC
  NUMBER_RULE t := ExceptT.mk (Session.NUMBER_RULE t)
  NUMBER_TAC := Session.NUMBER_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  num_CONV := Session.num_CONV
  HAS_SIZE_CONV := Session.HAS_SIZE_CONV
  extend_basic_congs := Session.extend_basic_congs
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  INT_REDUCE_CONV := Session.INT_REDUCE_CONV
  SELECT_CONV t := pure (Session.SELECT_CONV t)
  parse_as_infix := Session.parse_as_infix
  prove_general_recursive_function_exists := Session.prove_general_recursive_function_exists
  TAUT t := ExceptT.mk (Session.TAUT t)
  basic_ss := Session.basic_ss
  let_CONV := Session.let_CONV
  NUM_RING := Session.NUM_RING
  METIS_TAC := Session.METIS_TAC
  INT_REM_DOWN_CONV := Session.INT_REM_DOWN_CONV
  FRAG_MODULE t := ExceptT.mk (SessionLibrary.Frag.FRAG_MODULE t)
  ETA_CONV t := pure (Session.ETA_CONV t)
  core1 := core1 ()
  core2 := core2 ()
  core3 := core3 ()
  core4 := core4 ()
  core5 := core5 ()
  core6 := core6 ()
  core7 := core7 ()
  core8 := core8 ()
  core9 := core9 ()
  core10 := core10 ()
  core11 := core11 ()
  core12 := core12 ()
  core13 := core13 ()
  core14 := core14 ()
  core15 := core15 ()
  core16 := core16 ()

/-- Build a bundle once.  `setup` is a thunk, so that `deps` is not built
    before the bundle is needed.  The whole core library is built first
    (`Session.ensureDefine`, and MATCH_CONV's basic conversions, which HOL
    Light adds loading ind_types.ml), then frag.ml, card.ml, prime.ml, which grouptheory.ml needs. -/
private unsafe def cached {α : Type} [Inhabited α] (r : IO.Ref (Option α)) (name : String)
    (setup : Unit → IO (Except String α)) : α :=
  match unsafeIO (do
    match ← r.get with
    | some d => pure d
    | none => do
      Session.ensureDefine
      let _ ← Session.MATCH_CONV (HolCore.Kernel.mk_var "p" HolCore.Kernel.bool_ty)
      SessionLibrary.Frag.ensureFrag
      SessionLibrary.Card.ensureCard
      SessionLibrary.Prime.ensurePrime
      match ← setup () with
      | .ok d => do r.set (some d); pure d
      | .error e => panic! s!"{name} failed: {e}") with
  | .ok d => d | _ => panic! s!"SessionLibrary.GroupTheory: {name}"

/- The bundles, in file order; each forces the one before it. -/

-- @@BUNDLES BEGIN
initialize theBasics : IO.Ref (Option HolLibrary.GroupTheory.Basics) ← IO.mkRef none
unsafe def BBasics : HolLibrary.GroupTheory.Basics :=
  cached theBasics "setupBasics" fun _ => do
    (HolLibrary.GroupTheory.setupBasics (deps ())).run

initialize theDerived : IO.Ref (Option HolLibrary.GroupTheory.Derived) ← IO.mkRef none
unsafe def BDerived : HolLibrary.GroupTheory.Derived :=
  cached theDerived "setupDerived" fun _ => do
    let _ ← IO.mkRef BBasics.group_tybij
    (HolLibrary.GroupTheory.setupDerived (deps ()) BBasics).run

initialize thePow : IO.Ref (Option HolLibrary.GroupTheory.Pow) ← IO.mkRef none
unsafe def BPow : HolLibrary.GroupTheory.Pow :=
  cached thePow "setupPow" fun _ => do
    let _ ← IO.mkRef BDerived.group_div
    (HolLibrary.GroupTheory.setupPow (deps ()) BBasics BDerived).run

initialize theAbelian : IO.Ref (Option HolLibrary.GroupTheory.Abelian) ← IO.mkRef none
unsafe def BAbelian : HolLibrary.GroupTheory.Abelian :=
  cached theAbelian "setupAbelian" fun _ => do
    let _ ← IO.mkRef BPow.GROUP_COMMUTES_POW
    (HolLibrary.GroupTheory.setupAbelian (deps ()) BBasics BDerived BPow).run

initialize theTotalized : IO.Ref (Option HolLibrary.GroupTheory.Totalized) ← IO.mkRef none
unsafe def BTotalized : HolLibrary.GroupTheory.Totalized :=
  cached theTotalized "setupTotalized" fun _ => do
    let _ ← IO.mkRef BAbelian.abelian_group
    (HolLibrary.GroupTheory.setupTotalized (deps ()) BBasics BDerived BAbelian).run

initialize theGroupRule : IO.Ref (Option HolLibrary.GroupTheory.GroupRule) ← IO.mkRef none
unsafe def BGroupRule : HolLibrary.GroupTheory.GroupRule :=
  cached theGroupRule "setupGroupRule" fun _ => do
    let _ ← IO.mkRef BTotalized.group_neg
    (HolLibrary.GroupTheory.setupGroupRule (deps ()) BBasics BDerived BPow BTotalized).run

initialize theGroupProduct : IO.Ref (Option HolLibrary.GroupTheory.GroupProduct) ← IO.mkRef none
unsafe def BGroupProduct : HolLibrary.GroupTheory.GroupProduct :=
  cached theGroupProduct "setupGroupProduct" fun _ => do
    let _ ← IO.mkRef BGroupRule.GROUP_RULE
    (HolLibrary.GroupTheory.setupGroupProduct (deps ()) BBasics BDerived).run

initialize theGroupProductClauses : IO.Ref (Option HolLibrary.GroupTheory.GroupProductClauses) ← IO.mkRef none
unsafe def BGroupProductClauses : HolLibrary.GroupTheory.GroupProductClauses :=
  cached theGroupProductClauses "setupGroupProductClauses" fun _ => do
    let _ ← IO.mkRef BGroupProduct.group_product
    (HolLibrary.GroupTheory.setupGroupProductClauses (deps ()) BBasics BAbelian BGroupProduct).run

initialize theGroupProductMul : IO.Ref (Option HolLibrary.GroupTheory.GroupProductMul) ← IO.mkRef none
unsafe def BGroupProductMul : HolLibrary.GroupTheory.GroupProductMul :=
  cached theGroupProductMul "setupGroupProductMul" fun _ => do
    let _ ← IO.mkRef BGroupProductClauses.GROUP_PRODUCT_UNION
    (HolLibrary.GroupTheory.setupGroupProductMul (deps ()) BBasics BDerived BPow BAbelian BTotalized BGroupProduct BGroupProductClauses).run

initialize theConjugation : IO.Ref (Option HolLibrary.GroupTheory.Conjugation) ← IO.mkRef none
unsafe def BConjugation : HolLibrary.GroupTheory.Conjugation :=
  cached theConjugation "setupConjugation" fun _ => do
    let _ ← IO.mkRef BGroupProductMul.GROUP_PRODUCT_MUL
    (HolLibrary.GroupTheory.setupConjugation (deps ()) BBasics BGroupRule).run

initialize theSubgroups : IO.Ref (Option HolLibrary.GroupTheory.Subgroups) ← IO.mkRef none
unsafe def BSubgroups : HolLibrary.GroupTheory.Subgroups :=
  cached theSubgroups "setupSubgroups" fun _ => do
    let _ ← IO.mkRef BConjugation.group_conjugation
    (HolLibrary.GroupTheory.setupSubgroups (deps ()) BBasics BDerived BPow BGroupProduct BConjugation).run

initialize theSubgroupGenerated : IO.Ref (Option HolLibrary.GroupTheory.SubgroupGenerated) ← IO.mkRef none
unsafe def BSubgroupGenerated : HolLibrary.GroupTheory.SubgroupGenerated :=
  cached theSubgroupGenerated "setupSubgroupGenerated" fun _ => do
    let _ ← IO.mkRef BSubgroups.subgroup_of
    (HolLibrary.GroupTheory.setupSubgroupGenerated (deps ()) BBasics BDerived BPow BAbelian BConjugation BSubgroups).run

initialize theSubgroupGen1 : IO.Ref (Option HolLibrary.GroupTheory.SubgroupGen1) ← IO.mkRef none
unsafe def BSubgroupGen1 : HolLibrary.GroupTheory.SubgroupGen1 :=
  cached theSubgroupGen1 "setupSubgroupGen1" fun _ => do
    let _ ← IO.mkRef BSubgroupGenerated.subgroup_generated
    (HolLibrary.GroupTheory.setupSubgroupGen1 (deps ()) BBasics BSubgroups BSubgroupGenerated).run

initialize theSubgroupGen2 : IO.Ref (Option HolLibrary.GroupTheory.SubgroupGen2) ← IO.mkRef none
unsafe def BSubgroupGen2 : HolLibrary.GroupTheory.SubgroupGen2 :=
  cached theSubgroupGen2 "setupSubgroupGen2" fun _ => do
    let _ ← IO.mkRef BSubgroupGen1.FINITE_SUBGROUP_GENERATED
    (HolLibrary.GroupTheory.setupSubgroupGen2 (deps ()) BBasics BDerived BAbelian BSubgroups BSubgroupGenerated BSubgroupGen1).run

initialize theProdGroup : IO.Ref (Option HolLibrary.GroupTheory.ProdGroup) ← IO.mkRef none
unsafe def BProdGroup : HolLibrary.GroupTheory.ProdGroup :=
  cached theProdGroup "setupProdGroup" fun _ => do
    let _ ← IO.mkRef BSubgroupGen2.SUBGROUP_GENERATED_INSERT_ID
    (HolLibrary.GroupTheory.setupProdGroup (deps ()) BBasics BDerived BPow BAbelian BSubgroups BSubgroupGenerated BSubgroupGen1).run

initialize theProductGroup : IO.Ref (Option HolLibrary.GroupTheory.ProductGroup) ← IO.mkRef none
unsafe def BProductGroup : HolLibrary.GroupTheory.ProductGroup :=
  cached theProductGroup "setupProductGroup" fun _ => do
    let _ ← IO.mkRef BProdGroup.prod_group
    (HolLibrary.GroupTheory.setupProductGroup (deps ()) BBasics BDerived BPow BAbelian BSubgroups BSubgroupGenerated BSubgroupGen1 BProdGroup).run

initialize theSumGroup : IO.Ref (Option HolLibrary.GroupTheory.SumGroup) ← IO.mkRef none
unsafe def BSumGroup : HolLibrary.GroupTheory.SumGroup :=
  cached theSumGroup "setupSumGroup" fun _ => do
    let _ ← IO.mkRef BProductGroup.PRODUCT_GROUP
    (HolLibrary.GroupTheory.setupSumGroup (deps ()) BBasics BDerived BAbelian BSubgroups BSubgroupGenerated BSubgroupGen1 BProductGroup).run

initialize theHomomorphisms : IO.Ref (Option HolLibrary.GroupTheory.Homomorphisms) ← IO.mkRef none
unsafe def BHomomorphisms : HolLibrary.GroupTheory.Homomorphisms :=
  cached theHomomorphisms "setupHomomorphisms" fun _ => do
    let _ ← IO.mkRef BSumGroup.sum_group
    (HolLibrary.GroupTheory.setupHomomorphisms (deps ()) BBasics BDerived BSubgroupGenerated).run

initialize theHomomorphisms1 : IO.Ref (Option HolLibrary.GroupTheory.Homomorphisms1) ← IO.mkRef none
unsafe def BHomomorphisms1 : HolLibrary.GroupTheory.Homomorphisms1 :=
  cached theHomomorphisms1 "setupHomomorphisms1" fun _ => do
    let _ ← IO.mkRef BHomomorphisms.group_homomorphism
    (HolLibrary.GroupTheory.setupHomomorphisms1 (deps ()) BBasics BDerived BPow BSubgroupGenerated BSubgroupGen1 BHomomorphisms).run

initialize theHomomorphisms2 : IO.Ref (Option HolLibrary.GroupTheory.Homomorphisms2) ← IO.mkRef none
unsafe def BHomomorphisms2 : HolLibrary.GroupTheory.Homomorphisms2 :=
  cached theHomomorphisms2 "setupHomomorphisms2" fun _ => do
    let _ ← IO.mkRef BHomomorphisms1.GROUP_HOMOMORPHISM_INV
    (HolLibrary.GroupTheory.setupHomomorphisms2 (deps ()) BBasics BGroupRule BConjugation BSubgroups BSubgroupGenerated BSubgroupGen1 BHomomorphisms BHomomorphisms1).run

initialize theHomomorphisms3 : IO.Ref (Option HolLibrary.GroupTheory.Homomorphisms3) ← IO.mkRef none
unsafe def BHomomorphisms3 : HolLibrary.GroupTheory.Homomorphisms3 :=
  cached theHomomorphisms3 "setupHomomorphisms3" fun _ => do
    let _ ← IO.mkRef BHomomorphisms2.SUBGROUP_GENERATED_BY_HOMOMORPHIC_IMAGE
    (HolLibrary.GroupTheory.setupHomomorphisms3 (deps ()) BBasics BDerived BSubgroupGenerated BProdGroup BHomomorphisms BHomomorphisms1 BHomomorphisms2).run

initialize theHomomorphisms4 : IO.Ref (Option HolLibrary.GroupTheory.Homomorphisms4) ← IO.mkRef none
unsafe def BHomomorphisms4 : HolLibrary.GroupTheory.Homomorphisms4 :=
  cached theHomomorphisms4 "setupHomomorphisms4" fun _ => do
    let _ ← IO.mkRef BHomomorphisms3.CARD_EQ_GROUP_ISOMORPHIC_IMAGE
    (HolLibrary.GroupTheory.setupHomomorphisms4 (deps ()) BBasics BDerived BPow BAbelian BProductGroup BSumGroup BHomomorphisms BHomomorphisms1 BHomomorphisms2).run

initialize theIso1 : IO.Ref (Option HolLibrary.GroupTheory.Iso1) ← IO.mkRef none
unsafe def BIso1 : HolLibrary.GroupTheory.Iso1 :=
  cached theIso1 "setupIso1" fun _ => do
    let _ ← IO.mkRef BHomomorphisms4.GROUP_HOMOMORPHISM_COMPONENTWISE
    (HolLibrary.GroupTheory.setupIso1 (deps ()) BBasics BProductGroup BSumGroup BHomomorphisms BHomomorphisms1 BHomomorphisms2 BHomomorphisms3 BHomomorphisms4).run

initialize theIso2 : IO.Ref (Option HolLibrary.GroupTheory.Iso2) ← IO.mkRef none
unsafe def BIso2 : HolLibrary.GroupTheory.Iso2 :=
  cached theIso2 "setupIso2" fun _ => do
    let _ ← IO.mkRef BIso1.isomorphic_group
    (HolLibrary.GroupTheory.setupIso2 (deps ()) BBasics BSubgroupGenerated BProdGroup BProductGroup BSumGroup BHomomorphisms BHomomorphisms1 BHomomorphisms2 BHomomorphisms3 BHomomorphisms4 BIso1).run

initialize theDirectLimit : IO.Ref (Option HolLibrary.GroupTheory.DirectLimit) ← IO.mkRef none
unsafe def BDirectLimit : HolLibrary.GroupTheory.DirectLimit :=
  cached theDirectLimit "setupDirectLimit" fun _ => do
    let _ ← IO.mkRef BIso2.ISOMORPHIC_PRODUCT_GROUP_BIJECTIONS
    (HolLibrary.GroupTheory.setupDirectLimit (deps ()) BBasics BHomomorphisms).run

initialize theSetwise1 : IO.Ref (Option HolLibrary.GroupTheory.Setwise1) ← IO.mkRef none
unsafe def BSetwise1 : HolLibrary.GroupTheory.Setwise1 :=
  cached theSetwise1 "setupSetwise1" fun _ => do
    let _ ← IO.mkRef BDirectLimit.GROUP_DIRECT_LIMIT
    (HolLibrary.GroupTheory.setupSetwise1 (deps ()) BBasics BDerived BAbelian BSubgroups).run

initialize theSetwise2 : IO.Ref (Option HolLibrary.GroupTheory.Setwise2) ← IO.mkRef none
unsafe def BSetwise2 : HolLibrary.GroupTheory.Setwise2 :=
  cached theSetwise2 "setupSetwise2" fun _ => do
    let _ ← IO.mkRef BSetwise1.group_setinv
    (HolLibrary.GroupTheory.setupSetwise2 (deps ()) BBasics BDerived BConjugation BSubgroups BSubgroupGenerated BSubgroupGen1 BSetwise1).run

initialize theGroupActions : IO.Ref (Option HolLibrary.GroupTheory.GroupActions) ← IO.mkRef none
unsafe def BGroupActions : HolLibrary.GroupTheory.GroupActions :=
  cached theGroupActions "setupGroupActions" fun _ => do
    let _ ← IO.mkRef BSetwise2.GROUP_SETMUL_RSUBSET_EQ
    (HolLibrary.GroupTheory.setupGroupActions (deps ()) BBasics BDerived BSubgroups BSubgroupGenerated BSubgroupGen1).run

initialize theGroupOrbits : IO.Ref (Option HolLibrary.GroupTheory.GroupOrbits) ← IO.mkRef none
unsafe def BGroupOrbits : HolLibrary.GroupTheory.GroupOrbits :=
  cached theGroupOrbits "setupGroupOrbits" fun _ => do
    let _ ← IO.mkRef BGroupActions.group_action
    (HolLibrary.GroupTheory.setupGroupOrbits (deps ()) BBasics BGroupActions).run

initialize theOrbitStabilizer : IO.Ref (Option HolLibrary.GroupTheory.OrbitStabilizer) ← IO.mkRef none
unsafe def BOrbitStabilizer : HolLibrary.GroupTheory.OrbitStabilizer :=
  cached theOrbitStabilizer "setupOrbitStabilizer" fun _ => do
    let _ ← IO.mkRef BGroupOrbits.group_orbit
    (HolLibrary.GroupTheory.setupOrbitStabilizer (deps ()) BBasics BDerived BGroupRule BConjugation BSubgroups BSubgroupGenerated BSubgroupGen1 BProdGroup BSetwise1 BGroupActions BGroupOrbits).run

initialize theCosets : IO.Ref (Option HolLibrary.GroupTheory.Cosets) ← IO.mkRef none
unsafe def BCosets : HolLibrary.GroupTheory.Cosets :=
  cached theCosets "setupCosets" fun _ => do
    let _ ← IO.mkRef BOrbitStabilizer.ORBIT_STABILIZER_MUL_GEN
    (HolLibrary.GroupTheory.setupCosets (deps ()) BBasics BDerived BSubgroups BSetwise1 BSetwise2).run

initialize theCosets1 : IO.Ref (Option HolLibrary.GroupTheory.Cosets1) ← IO.mkRef none
unsafe def BCosets1 : HolLibrary.GroupTheory.Cosets1 :=
  cached theCosets1 "setupCosets1" fun _ => do
    let _ ← IO.mkRef BCosets.right_coset
    (HolLibrary.GroupTheory.setupCosets1 (deps ()) BBasics BDerived BSubgroups BSetwise1 BCosets).run

initialize theCosets2 : IO.Ref (Option HolLibrary.GroupTheory.Cosets2) ← IO.mkRef none
unsafe def BCosets2 : HolLibrary.GroupTheory.Cosets2 :=
  cached theCosets2 "setupCosets2" fun _ => do
    let _ ← IO.mkRef BCosets1.IN_LEFT_COSET_SELF
    (HolLibrary.GroupTheory.setupCosets2 (deps ()) BBasics BDerived BGroupRule BConjugation BSubgroups BSubgroupGen1 BProdGroup BProductGroup BSetwise1 BGroupActions BGroupOrbits BOrbitStabilizer BCosets).run

initialize theCosetProducts : IO.Ref (Option HolLibrary.GroupTheory.CosetProducts) ← IO.mkRef none
unsafe def BCosetProducts : HolLibrary.GroupTheory.CosetProducts :=
  cached theCosetProducts "setupCosetProducts" fun _ => do
    let _ ← IO.mkRef BCosets2.GROUP_ORBIT_SUBGROUP_TRANSLATION
    (HolLibrary.GroupTheory.setupCosetProducts (deps ()) BBasics BGroupRule BSubgroups BSubgroupGenerated BSubgroupGen1 BProductGroup BSetwise1 BCosets BCosets1 BCosets2).run

initialize theNormalSubgroups : IO.Ref (Option HolLibrary.GroupTheory.NormalSubgroups) ← IO.mkRef none
unsafe def BNormalSubgroups : HolLibrary.GroupTheory.NormalSubgroups :=
  cached theNormalSubgroups "setupNormalSubgroups" fun _ => do
    let _ ← IO.mkRef BCosetProducts.RIGHT_COSET_PRODUCT_GROUP
    (HolLibrary.GroupTheory.setupNormalSubgroups (deps ()) BBasics BDerived BAbelian BConjugation BSubgroups BSetwise1 BSetwise2 BGroupActions BCosets BCosets1).run

initialize theNormalSubgroups2 : IO.Ref (Option HolLibrary.GroupTheory.NormalSubgroups2) ← IO.mkRef none
unsafe def BNormalSubgroups2 : HolLibrary.GroupTheory.NormalSubgroups2 :=
  cached theNormalSubgroups2 "setupNormalSubgroups2" fun _ => do
    let _ ← IO.mkRef BNormalSubgroups.normal_subgroup_of
    (HolLibrary.GroupTheory.setupNormalSubgroups2 (deps ()) BBasics BSubgroups BSubgroupGenerated BSubgroupGen1 BProdGroup BSetwise1 BSetwise2 BCosets BCosets2 BCosetProducts BNormalSubgroups).run

initialize theConjugate : IO.Ref (Option HolLibrary.GroupTheory.Conjugate) ← IO.mkRef none
unsafe def BConjugate : HolLibrary.GroupTheory.Conjugate :=
  cached theConjugate "setupConjugate" fun _ => do
    let _ ← IO.mkRef BNormalSubgroups2.GROUP_SETMUL_RIGHT_COSET
    (HolLibrary.GroupTheory.setupConjugate (deps ()) BBasics BDerived BConjugation BSubgroupGenerated BHomomorphisms2 BHomomorphisms3 BIso1 BGroupActions BGroupOrbits BOrbitStabilizer).run

initialize theCentralizerNormalizer : IO.Ref (Option HolLibrary.GroupTheory.CentralizerNormalizer) ← IO.mkRef none
unsafe def BCentralizerNormalizer : HolLibrary.GroupTheory.CentralizerNormalizer :=
  cached theCentralizerNormalizer "setupCentralizerNormalizer" fun _ => do
    let _ ← IO.mkRef BConjugate.group_conjugate
    (HolLibrary.GroupTheory.setupCentralizerNormalizer (deps ()) BBasics BDerived BAbelian BConjugation BSubgroups BSubgroupGenerated BSubgroupGen1 BSetwise1 BSetwise2 BCosetProducts BNormalSubgroups).run

initialize theCentralizerNormalizer2 : IO.Ref (Option HolLibrary.GroupTheory.CentralizerNormalizer2) ← IO.mkRef none
unsafe def BCentralizerNormalizer2 : HolLibrary.GroupTheory.CentralizerNormalizer2 :=
  cached theCentralizerNormalizer2 "setupCentralizerNormalizer2" fun _ => do
    let _ ← IO.mkRef BCentralizerNormalizer.group_centralizer
    (HolLibrary.GroupTheory.setupCentralizerNormalizer2 (deps ()) BBasics BConjugation BSubgroups BSubgroupGenerated BSubgroupGen1 BHomomorphisms2 BSetwise1 BGroupActions BGroupOrbits BOrbitStabilizer BNormalSubgroups BConjugate BCentralizerNormalizer).run

initialize theQuotientGroups : IO.Ref (Option HolLibrary.GroupTheory.QuotientGroups) ← IO.mkRef none
unsafe def BQuotientGroups : HolLibrary.GroupTheory.QuotientGroups :=
  cached theQuotientGroups "setupQuotientGroups" fun _ => do
    let _ ← IO.mkRef BCentralizerNormalizer2.GROUP_CENTRALIZER_ALT
    (HolLibrary.GroupTheory.setupQuotientGroups (deps ()) BBasics BDerived BPow BAbelian BSubgroups BSubgroupGenerated BSubgroupGen1 BProdGroup BProductGroup BHomomorphisms BHomomorphisms2 BIso1 BSetwise1 BSetwise2 BCosets BCosets2 BCosetProducts BNormalSubgroups BNormalSubgroups2).run

initialize theKernelsImages1 : IO.Ref (Option HolLibrary.GroupTheory.KernelsImages1) ← IO.mkRef none
unsafe def BKernelsImages1 : HolLibrary.GroupTheory.KernelsImages1 :=
  cached theKernelsImages1 "setupKernelsImages1" fun _ => do
    let _ ← IO.mkRef BQuotientGroups.quotient_group
    (HolLibrary.GroupTheory.setupKernelsImages1 (deps ()) BBasics BDerived BSubgroups BSubgroupGenerated BSubgroupGen1 BHomomorphisms BHomomorphisms1 BHomomorphisms2 BHomomorphisms3 BSetwise1 BCosets BCosets2 BNormalSubgroups BQuotientGroups).run

initialize theKernelsImages2 : IO.Ref (Option HolLibrary.GroupTheory.KernelsImages2) ← IO.mkRef none
unsafe def BKernelsImages2 : HolLibrary.GroupTheory.KernelsImages2 :=
  cached theKernelsImages2 "setupKernelsImages2" fun _ => do
    let _ ← IO.mkRef BKernelsImages1.group_kernel
    (HolLibrary.GroupTheory.setupKernelsImages2 (deps ()) BBasics BDerived BTotalized BSubgroups BSubgroupGen1 BHomomorphisms BHomomorphisms1 BHomomorphisms2 BIso1 BSetwise1 BSetwise2 BCosets BNormalSubgroups BNormalSubgroups2 BQuotientGroups BKernelsImages1).run

initialize theSubgroupCorrespondence : IO.Ref (Option HolLibrary.GroupTheory.SubgroupCorrespondence) ← IO.mkRef none
unsafe def BSubgroupCorrespondence : HolLibrary.GroupTheory.SubgroupCorrespondence :=
  cached theSubgroupCorrespondence "setupSubgroupCorrespondence" fun _ => do
    let _ ← IO.mkRef BKernelsImages2.QUOTIENT_GROUP_UNIVERSAL_EXPLICIT
    (HolLibrary.GroupTheory.setupSubgroupCorrespondence (deps ()) BBasics BDerived BConjugation BSubgroups BHomomorphisms BHomomorphisms1 BHomomorphisms2 BSetwise1 BCosets BNormalSubgroups BConjugate BQuotientGroups BKernelsImages1 BKernelsImages2).run

initialize theTrivialHomomorphisms : IO.Ref (Option HolLibrary.GroupTheory.TrivialHomomorphisms) ← IO.mkRef none
unsafe def BTrivialHomomorphisms : HolLibrary.GroupTheory.TrivialHomomorphisms :=
  cached theTrivialHomomorphisms "setupTrivialHomomorphisms" fun _ => do
    let _ ← IO.mkRef BSubgroupCorrespondence.GROUP_EPIMORPHISM_SUBGROUP_CORRESPONDENCE_ALT
    (HolLibrary.GroupTheory.setupTrivialHomomorphisms (deps ()) BBasics BHomomorphisms BHomomorphisms1 BHomomorphisms2 BKernelsImages1).run

initialize theGroupElementOrder : IO.Ref (Option HolLibrary.GroupTheory.GroupElementOrder) ← IO.mkRef none
unsafe def BGroupElementOrder : HolLibrary.GroupTheory.GroupElementOrder :=
  cached theGroupElementOrder "setupGroupElementOrder" fun _ => do
    let _ ← IO.mkRef BTrivialHomomorphisms.trivial_homomorphism
    (HolLibrary.GroupTheory.setupGroupElementOrder (deps ()) BBasics BDerived BPow).run

initialize theGroupElementOrder2 : IO.Ref (Option HolLibrary.GroupTheory.GroupElementOrder2) ← IO.mkRef none
unsafe def BGroupElementOrder2 : HolLibrary.GroupTheory.GroupElementOrder2 :=
  cached theGroupElementOrder2 "setupGroupElementOrder2" fun _ => do
    let _ ← IO.mkRef BGroupElementOrder.group_element_order
    (HolLibrary.GroupTheory.setupGroupElementOrder2 (deps ()) BBasics BDerived BPow BAbelian BGroupRule BHomomorphisms BHomomorphisms1 BHomomorphisms2 BIso1 BKernelsImages1 BGroupElementOrder).run

initialize theOrderDecomp : IO.Ref (Option HolLibrary.GroupTheory.OrderDecomp) ← IO.mkRef none
unsafe def BOrderDecomp : HolLibrary.GroupTheory.OrderDecomp :=
  cached theOrderDecomp "setupOrderDecomp" fun _ => do
    let _ ← IO.mkRef BGroupElementOrder2.GROUP_ELEMENT_ORDER_POW_GEN
    (HolLibrary.GroupTheory.setupOrderDecomp (deps ()) BBasics BDerived BPow BAbelian BGroupRule BSubgroupGenerated BProdGroup BSumGroup BGroupElementOrder BGroupElementOrder2).run

initialize theTorsionSubgroups : IO.Ref (Option HolLibrary.GroupTheory.TorsionSubgroups) ← IO.mkRef none
unsafe def BTorsionSubgroups : HolLibrary.GroupTheory.TorsionSubgroups :=
  cached theTorsionSubgroups "setupTorsionSubgroups" fun _ => do
    let _ ← IO.mkRef BOrderDecomp.GROUP_ELEMENT_ORDER_LCM_EXISTS
    (HolLibrary.GroupTheory.setupTorsionSubgroups (deps ()) BBasics BDerived BConjugation BSubgroups BCosets BNormalSubgroups BQuotientGroups BGroupElementOrder BGroupElementOrder2).run

initialize theCyclicGroups1 : IO.Ref (Option HolLibrary.GroupTheory.CyclicGroups1) ← IO.mkRef none
unsafe def BCyclicGroups1 : HolLibrary.GroupTheory.CyclicGroups1 :=
  cached theCyclicGroups1 "setupCyclicGroups1" fun _ => do
    let _ ← IO.mkRef BTorsionSubgroups.SUBGROUP_OF_TORSION_GENERAL
    (HolLibrary.GroupTheory.setupCyclicGroups1 (deps ()) BBasics BDerived BPow BAbelian BSubgroups BSubgroupGenerated BSubgroupGen1 BSubgroupGen2 BHomomorphisms BHomomorphisms1 BHomomorphisms2 BIso1 BNormalSubgroups BQuotientGroups).run

initialize theCyclicGroups2 : IO.Ref (Option HolLibrary.GroupTheory.CyclicGroups2) ← IO.mkRef none
unsafe def BCyclicGroups2 : HolLibrary.GroupTheory.CyclicGroups2 :=
  cached theCyclicGroups2 "setupCyclicGroups2" fun _ => do
    let _ ← IO.mkRef BCyclicGroups1.SUBGROUP_OF_POWERS
    (HolLibrary.GroupTheory.setupCyclicGroups2 (deps ()) BBasics BDerived BPow BSubgroups BSubgroupGenerated BSubgroupGen1 BCosets2 BGroupElementOrder BCyclicGroups1).run

initialize theCyclicGroups3 : IO.Ref (Option HolLibrary.GroupTheory.CyclicGroups3) ← IO.mkRef none
unsafe def BCyclicGroups3 : HolLibrary.GroupTheory.CyclicGroups3 :=
  cached theCyclicGroups3 "setupCyclicGroups3" fun _ => do
    let _ ← IO.mkRef BCyclicGroups2.FINITE_CYCLIC_SUBGROUP
    (HolLibrary.GroupTheory.setupCyclicGroups3 (deps ()) BBasics BDerived BPow BSubgroups BSubgroupGenerated BSubgroupGen1 BCosets2 BNormalSubgroups BQuotientGroups BSubgroupCorrespondence BGroupElementOrder BGroupElementOrder2 BCyclicGroups1 BCyclicGroups2).run

initialize theFinitelyGenerated : IO.Ref (Option HolLibrary.GroupTheory.FinitelyGenerated) ← IO.mkRef none
unsafe def BFinitelyGenerated : HolLibrary.GroupTheory.FinitelyGenerated :=
  cached theFinitelyGenerated "setupFinitelyGenerated" fun _ => do
    let _ ← IO.mkRef BCyclicGroups3.ABELIAN_SIMPLE_GROUP
    (HolLibrary.GroupTheory.setupFinitelyGenerated (deps ()) BBasics BDerived BSubgroups BSubgroupGenerated BSubgroupGen1 BProdGroup BProductGroup BSumGroup BHomomorphisms BHomomorphisms1 BHomomorphisms2 BHomomorphisms3 BIso1 BIso2 BGroupActions BQuotientGroups BCyclicGroups1).run

initialize theFinitelyGeneratedSubgroups : IO.Ref (Option HolLibrary.GroupTheory.FinitelyGeneratedSubgroups) ← IO.mkRef none
unsafe def BFinitelyGeneratedSubgroups : HolLibrary.GroupTheory.FinitelyGeneratedSubgroups :=
  cached theFinitelyGeneratedSubgroups "setupFinitelyGeneratedSubgroups" fun _ => do
    let _ ← IO.mkRef BFinitelyGenerated.finitely_generated_group
    (HolLibrary.GroupTheory.setupFinitelyGeneratedSubgroups (deps ()) BBasics BDerived BGroupRule BConjugation BSubgroups BSubgroupGenerated BSubgroupGen1 BSubgroupGen2 BHomomorphisms BHomomorphisms1 BHomomorphisms2 BIso1 BIso2 BSetwise1 BGroupActions BCosets BCosets1 BCosets2 BCosetProducts BNormalSubgroups BNormalSubgroups2 BQuotientGroups BKernelsImages1 BKernelsImages2 BCyclicGroups1 BFinitelyGenerated).run

initialize theFinitelyGeneratedMaximal : IO.Ref (Option HolLibrary.GroupTheory.FinitelyGeneratedMaximal) ← IO.mkRef none
unsafe def BFinitelyGeneratedMaximal : HolLibrary.GroupTheory.FinitelyGeneratedMaximal :=
  cached theFinitelyGeneratedMaximal "setupFinitelyGeneratedMaximal" fun _ => do
    let _ ← IO.mkRef BFinitelyGeneratedSubgroups.FINITELY_GENERATED_FIXED_INDEX_SUBGROUPS
    (HolLibrary.GroupTheory.setupFinitelyGeneratedMaximal (deps ()) BBasics BSubgroups BSubgroupGenerated BSubgroupGen2 BNormalSubgroups BFinitelyGenerated BFinitelyGeneratedSubgroups).run

initialize theIntegerGroup : IO.Ref (Option HolLibrary.GroupTheory.IntegerGroup) ← IO.mkRef none
unsafe def BIntegerGroup : HolLibrary.GroupTheory.IntegerGroup :=
  cached theIntegerGroup "setupIntegerGroup" fun _ => do
    let _ ← IO.mkRef BFinitelyGeneratedMaximal.FINITELY_GENERATED_ABELIAN_SUBGROUP
    (HolLibrary.GroupTheory.setupIntegerGroup (deps ()) BBasics BDerived BPow BAbelian BSubgroupGen1 BHomomorphisms BHomomorphisms1 BHomomorphisms2 BIso1 BGroupElementOrder BCyclicGroups1 BCyclicGroups2).run

initialize theIntegerModGroup : IO.Ref (Option HolLibrary.GroupTheory.IntegerModGroup) ← IO.mkRef none
unsafe def BIntegerModGroup : HolLibrary.GroupTheory.IntegerModGroup :=
  cached theIntegerModGroup "setupIntegerModGroup" fun _ => do
    let _ ← IO.mkRef BIntegerGroup.integer_group
    (HolLibrary.GroupTheory.setupIntegerModGroup (deps ()) BBasics BDerived BPow BAbelian BSubgroupGenerated BSubgroupGen1 BProdGroup BHomomorphisms BGroupElementOrder BGroupElementOrder2 BCyclicGroups1 BIntegerGroup).run

initialize theCyclicInteger : IO.Ref (Option HolLibrary.GroupTheory.CyclicInteger) ← IO.mkRef none
unsafe def BCyclicInteger : HolLibrary.GroupTheory.CyclicInteger :=
  cached theCyclicInteger "setupCyclicInteger" fun _ => do
    let _ ← IO.mkRef BIntegerModGroup.integer_mod_group
    (HolLibrary.GroupTheory.setupCyclicInteger (deps ()) BBasics BPow BSubgroupGenerated BIso1 BIso2 BKernelsImages1 BGroupElementOrder BCyclicGroups1 BCyclicGroups2 BIntegerGroup BIntegerModGroup).run

initialize theCyclicProd : IO.Ref (Option HolLibrary.GroupTheory.CyclicProd) ← IO.mkRef none
unsafe def BCyclicProd : HolLibrary.GroupTheory.CyclicProd :=
  cached theCyclicProd "setupCyclicProd" fun _ => do
    let _ ← IO.mkRef BCyclicInteger.CYCLIC_INTEGER_GROUP
    (HolLibrary.GroupTheory.setupCyclicProd (deps ()) BBasics BDerived BPow BSubgroupGenerated BSubgroupGen1 BProdGroup BHomomorphisms2 BHomomorphisms3 BIso1 BIso2 BGroupElementOrder BCyclicGroups1 BCyclicGroups2 BCyclicGroups3 BIntegerModGroup BCyclicInteger).run

initialize thePgroup : IO.Ref (Option HolLibrary.GroupTheory.Pgroup) ← IO.mkRef none
unsafe def BPgroup : HolLibrary.GroupTheory.Pgroup :=
  cached thePgroup "setupPgroup" fun _ => do
    let _ ← IO.mkRef BCyclicProd.CYCLIC_PROD_INTEGER_MOD_GROUP
    (HolLibrary.GroupTheory.setupPgroup (deps ()) BBasics BProdGroup BSumGroup BHomomorphisms BHomomorphisms1 BHomomorphisms3 BHomomorphisms4 BQuotientGroups BGroupElementOrder BGroupElementOrder2 BOrderDecomp).run

initialize theSylowCount : IO.Ref (Option HolLibrary.GroupTheory.SylowCount) ← IO.mkRef none
unsafe def BSylowCount : HolLibrary.GroupTheory.SylowCount :=
  cached theSylowCount "setupSylowCount" fun _ => do
    let _ ← IO.mkRef BPgroup.pgroup
    (HolLibrary.GroupTheory.setupSylowCount (deps ()) BBasics BGroupRule BSubgroups BSubgroupGen1 BSetwise1 BGroupActions BGroupOrbits BOrbitStabilizer BCosets BCosets1 BCosets2 BCyclicGroups3 BIntegerModGroup BCyclicInteger).run

initialize theSylow : IO.Ref (Option HolLibrary.GroupTheory.Sylow) ← IO.mkRef none
unsafe def BSylow : HolLibrary.GroupTheory.Sylow :=
  cached theSylow "setupSylow" fun _ => do
    let _ ← IO.mkRef BSylowCount.SYLOW_THEOREM_COUNT_MOD
    (HolLibrary.GroupTheory.setupSylow (deps ()) BBasics BDerived BPow BSubgroups BSubgroupGenerated BSubgroupGen1 BGroupElementOrder BOrderDecomp BCyclicGroups3 BPgroup BSylowCount).run

initialize thePowering : IO.Ref (Option HolLibrary.GroupTheory.Powering) ← IO.mkRef none
unsafe def BPowering : HolLibrary.GroupTheory.Powering :=
  cached thePowering "setupPowering" fun _ => do
    let _ ← IO.mkRef BSylow.SYLOW_THEOREM
    (HolLibrary.GroupTheory.setupPowering (deps ()) BHomomorphisms BHomomorphisms2 BHomomorphisms4 BGroupOrbits BOrbitStabilizer BSylow).run

initialize theSylow2 : IO.Ref (Option HolLibrary.GroupTheory.Sylow2) ← IO.mkRef none
unsafe def BSylow2 : HolLibrary.GroupTheory.Sylow2 :=
  cached theSylow2 "setupSylow2" fun _ => do
    let _ ← IO.mkRef BPowering.ABELIAN_GROUP_MONOMORPHISM_POWERING_EQ
    (HolLibrary.GroupTheory.setupSylow2 (deps ()) BBasics BGroupRule BConjugation BSubgroups BSubgroupGen1 BHomomorphisms2 BGroupActions BCosets BCosets2 BNormalSubgroups BConjugate BCentralizerNormalizer BCentralizerNormalizer2 BSubgroupCorrespondence BSylow BPowering).run

initialize thePGroupCentre : IO.Ref (Option HolLibrary.GroupTheory.PGroupCentre) ← IO.mkRef none
unsafe def BPGroupCentre : HolLibrary.GroupTheory.PGroupCentre :=
  cached thePGroupCentre "setupPGroupCentre" fun _ => do
    let _ ← IO.mkRef BSylow2.SYLOW_THEOREM_CONJUGATE_GEN
    (HolLibrary.GroupTheory.setupPGroupCentre (deps ()) BBasics BDerived BConjugation BSubgroups BSubgroupGen1 BGroupActions BOrbitStabilizer BCosets BCosets2 BCosetProducts BNormalSubgroups BCentralizerNormalizer BSylow BPowering).run

initialize thePgroupNormalizer : IO.Ref (Option HolLibrary.GroupTheory.PgroupNormalizer) ← IO.mkRef none
unsafe def BPgroupNormalizer : HolLibrary.GroupTheory.PgroupNormalizer :=
  cached thePgroupNormalizer "setupPgroupNormalizer" fun _ => do
    let _ ← IO.mkRef BPGroupCentre.PGROUP_NONTRIVIAL_CENTRE_GEN
    (HolLibrary.GroupTheory.setupPgroupNormalizer (deps ()) BBasics BDerived BConjugation BSubgroups BSubgroupGenerated BSubgroupGen1 BHomomorphisms2 BSetwise1 BSetwise2 BCosets2 BCosetProducts BNormalSubgroups BConjugate BCentralizerNormalizer BSylow BSylow2 BPGroupCentre).run

initialize theGroupDisjointSum : IO.Ref (Option HolLibrary.GroupTheory.GroupDisjointSum) ← IO.mkRef none
unsafe def BGroupDisjointSum : HolLibrary.GroupTheory.GroupDisjointSum :=
  cached theGroupDisjointSum "setupGroupDisjointSum" fun _ => do
    let _ ← IO.mkRef BPgroupNormalizer.PGROUP_SUBGROUP_PSUBSET_NORMALIZER
    (HolLibrary.GroupTheory.setupGroupDisjointSum (deps ()) BBasics BDerived BGroupRule BSubgroups BSetwise1 BCosets BNormalSubgroups).run

initialize theGroupMulMorphism : IO.Ref (Option HolLibrary.GroupTheory.GroupMulMorphism) ← IO.mkRef none
unsafe def BGroupMulMorphism : HolLibrary.GroupTheory.GroupMulMorphism :=
  cached theGroupMulMorphism "setupGroupMulMorphism" fun _ => do
    let _ ← IO.mkRef BGroupDisjointSum.GROUP_DISJOINT_SUM_ALT
    (HolLibrary.GroupTheory.setupGroupMulMorphism (deps ()) BBasics BAbelian BGroupRule BSubgroups BSubgroupGenerated BSubgroupGen1 BSubgroupGen2 BProdGroup BHomomorphisms BHomomorphisms1 BHomomorphisms2 BSetwise1 BNormalSubgroups BGroupDisjointSum).run

initialize theGroupSumImKer : IO.Ref (Option HolLibrary.GroupTheory.GroupSumImKer) ← IO.mkRef none
unsafe def BGroupSumImKer : HolLibrary.GroupTheory.GroupSumImKer :=
  cached theGroupSumImKer "setupGroupSumImKer" fun _ => do
    let _ ← IO.mkRef BGroupMulMorphism.GROUP_HOMOMORPHISM_GROUP_MUL_GEN
    (HolLibrary.GroupTheory.setupGroupSumImKer (deps ()) BBasics BSubgroups BSubgroupGenerated BSubgroupGen1 BSubgroupGen2 BHomomorphisms BHomomorphisms2 BIso1 BSetwise1 BCosetProducts BNormalSubgroups BNormalSubgroups2 BKernelsImages1 BGroupDisjointSum BGroupMulMorphism).run

initialize theGroupSumHomomorphism : IO.Ref (Option HolLibrary.GroupTheory.GroupSumHomomorphism) ← IO.mkRef none
unsafe def BGroupSumHomomorphism : HolLibrary.GroupTheory.GroupSumHomomorphism :=
  cached theGroupSumHomomorphism "setupGroupSumHomomorphism" fun _ => do
    let _ ← IO.mkRef BGroupSumImKer.ISOMORPHIC_PROD_GROUP_SUBGROUP_GENERATED
    (HolLibrary.GroupTheory.setupGroupSumHomomorphism (deps ()) BBasics BDerived BAbelian BGroupRule BGroupProduct BGroupProductMul BSubgroups BSubgroupGenerated BSubgroupGen1 BSubgroupGen2 BSumGroup BHomomorphisms BHomomorphisms1 BHomomorphisms4).run

initialize theGroupSumEpimorphism : IO.Ref (Option HolLibrary.GroupTheory.GroupSumEpimorphism) ← IO.mkRef none
unsafe def BGroupSumEpimorphism : HolLibrary.GroupTheory.GroupSumEpimorphism :=
  cached theGroupSumEpimorphism "setupGroupSumEpimorphism" fun _ => do
    let _ ← IO.mkRef BGroupSumHomomorphism.GROUP_HOMOMORPHISM_GROUP_SUM_GEN
    (HolLibrary.GroupTheory.setupGroupSumEpimorphism (deps ()) BAbelian BGroupProduct BSubgroups BSubgroupGenerated BSubgroupGen1 BSumGroup BHomomorphisms BHomomorphisms2 BGroupSumHomomorphism).run

initialize theGroupSumMonomorphism : IO.Ref (Option HolLibrary.GroupTheory.GroupSumMonomorphism) ← IO.mkRef none
unsafe def BGroupSumMonomorphism : HolLibrary.GroupTheory.GroupSumMonomorphism :=
  cached theGroupSumMonomorphism "setupGroupSumMonomorphism" fun _ => do
    let _ ← IO.mkRef BGroupSumEpimorphism.SUBGROUP_EPIMORPHISM_GROUP_SUM_GEN
    (HolLibrary.GroupTheory.setupGroupSumMonomorphism (deps ()) BBasics BDerived BAbelian BGroupRule BGroupProduct BGroupProductClauses BSubgroups BSubgroupGenerated BSubgroupGen1 BSubgroupGen2 BSumGroup BHomomorphisms BHomomorphisms2 BKernelsImages1 BGroupDisjointSum BGroupSumHomomorphism BGroupSumEpimorphism).run

initialize theSumGroupIsomorphism : IO.Ref (Option HolLibrary.GroupTheory.SumGroupIsomorphism) ← IO.mkRef none
unsafe def BSumGroupIsomorphism : HolLibrary.GroupTheory.SumGroupIsomorphism :=
  cached theSumGroupIsomorphism "setupSumGroupIsomorphism" fun _ => do
    let _ ← IO.mkRef BGroupSumMonomorphism.GROUP_MONOMORPHISM_GROUP_SUM_GEN
    (HolLibrary.GroupTheory.setupSumGroupIsomorphism (deps ()) BAbelian BSubgroups BSubgroupGenerated BSubgroupGen1 BHomomorphisms2 BIso1 BNormalSubgroups BGroupDisjointSum BGroupSumEpimorphism BGroupSumMonomorphism).run

initialize theCarrierSubgroupGeneratedUnions : IO.Ref (Option HolLibrary.GroupTheory.CarrierSubgroupGeneratedUnions) ← IO.mkRef none
unsafe def BCarrierSubgroupGeneratedUnions : HolLibrary.GroupTheory.CarrierSubgroupGeneratedUnions :=
  cached theCarrierSubgroupGeneratedUnions "setupCarrierSubgroupGeneratedUnions" fun _ => do
    let _ ← IO.mkRef BSumGroupIsomorphism.SUBGROUP_ISOMORPHISM_GROUP_SUM_EQ
    (HolLibrary.GroupTheory.setupCarrierSubgroupGeneratedUnions (deps ()) BDerived BPow BAbelian BGroupProduct BGroupProductMul BSubgroups BSubgroupGenerated BSubgroupGen1 BSumGroup BHomomorphisms BGroupSumEpimorphism).run

initialize thePrimeTorsion : IO.Ref (Option HolLibrary.GroupTheory.PrimeTorsion) ← IO.mkRef none
unsafe def BPrimeTorsion : HolLibrary.GroupTheory.PrimeTorsion :=
  cached thePrimeTorsion "setupPrimeTorsion" fun _ => do
    let _ ← IO.mkRef BCarrierSubgroupGeneratedUnions.CARRIER_SUBGROUP_GENERATED_UNIONS
    (HolLibrary.GroupTheory.setupPrimeTorsion (deps ()) BBasics BSubgroups BSubgroupGenerated BSubgroupGen1 BSubgroupGen2 BGroupElementOrder BGroupElementOrder2 BOrderDecomp).run

initialize theTorsionStructure : IO.Ref (Option HolLibrary.GroupTheory.TorsionStructure) ← IO.mkRef none
unsafe def BTorsionStructure : HolLibrary.GroupTheory.TorsionStructure :=
  cached theTorsionStructure "setupTorsionStructure" fun _ => do
    let _ ← IO.mkRef BPrimeTorsion.SUBGROUP_GENERATED_UNIONS_PRIME_TORSION_FINITE
    (HolLibrary.GroupTheory.setupTorsionStructure (deps ()) BBasics BSubgroups BSubgroupGenerated BSubgroupGen1 BSumGroup BHomomorphisms BHomomorphisms2 BIso1 BGroupElementOrder BGroupElementOrder2 BOrderDecomp BTorsionSubgroups BCyclicGroups3 BPgroup BGroupDisjointSum BSumGroupIsomorphism BPrimeTorsion).run

initialize theFinitelyGeneratedAbelian : IO.Ref (Option HolLibrary.GroupTheory.FinitelyGeneratedAbelian) ← IO.mkRef none
unsafe def BFinitelyGeneratedAbelian : HolLibrary.GroupTheory.FinitelyGeneratedAbelian :=
  cached theFinitelyGeneratedAbelian "setupFinitelyGeneratedAbelian" fun _ => do
    let _ ← IO.mkRef BTorsionStructure.SUBGROUP_GENERATED_UNIONS_PRIME_TORSION_FULL
    (HolLibrary.GroupTheory.setupFinitelyGeneratedAbelian (deps ()) BBasics BPow BAbelian BGroupRule BGroupProduct BGroupProductClauses BGroupProductMul BSubgroups BSubgroupGenerated BSubgroupGen1 BSubgroupGen2 BProdGroup BProductGroup BSumGroup BHomomorphisms BHomomorphisms2 BHomomorphisms3 BHomomorphisms4 BIso2 BSetwise1 BSetwise2 BKernelsImages1 BGroupElementOrder BCyclicGroups1 BGroupSumEpimorphism BCarrierSubgroupGeneratedUnions).run

initialize theFinGenAbelianStructure : IO.Ref (Option HolLibrary.GroupTheory.FinGenAbelianStructure) ← IO.mkRef none
unsafe def BFinGenAbelianStructure : HolLibrary.GroupTheory.FinGenAbelianStructure :=
  cached theFinGenAbelianStructure "setupFinGenAbelianStructure" fun _ => do
    let _ ← IO.mkRef BFinitelyGeneratedAbelian.FINITELY_GENERATED_ABELIAN_SUBGROUP_STRUCTURE_ISOMORPHISM
    (HolLibrary.GroupTheory.setupFinGenAbelianStructure (deps ()) BSumGroup BIso1 BIso2 BGroupElementOrder2 BOrderDecomp BTorsionSubgroups BCyclicGroups1 BFinitelyGenerated BIntegerGroup BIntegerModGroup BCyclicInteger BFinitelyGeneratedAbelian).run

initialize theFreeAbelianGroup : IO.Ref (Option HolLibrary.GroupTheory.FreeAbelianGroup) ← IO.mkRef none
unsafe def BFreeAbelianGroup : HolLibrary.GroupTheory.FreeAbelianGroup :=
  cached theFreeAbelianGroup "setupFreeAbelianGroup" fun _ => do
    let _ ← IO.mkRef BFinGenAbelianStructure.FINITELY_GENERATED_ABELIAN_SUBGROUP_STRUCTURE_ISOMORPHISM_ALT
    (HolLibrary.GroupTheory.setupFreeAbelianGroup (deps ()) BBasics BDerived BPow BAbelian BTotalized BSubgroups BSumGroup BHomomorphisms BHomomorphisms2 BIso1 BKernelsImages1 BIntegerGroup).run

initialize theFreeAbelianExtra : IO.Ref (Option HolLibrary.GroupTheory.FreeAbelianExtra) ← IO.mkRef none
unsafe def BFreeAbelianExtra : HolLibrary.GroupTheory.FreeAbelianExtra :=
  cached theFreeAbelianExtra "setupFreeAbelianExtra" fun _ => do
    let _ ← IO.mkRef BFreeAbelianGroup.free_abelian_group
    (HolLibrary.GroupTheory.setupFreeAbelianExtra (deps ()) BBasics BDerived BHomomorphisms BHomomorphisms1 BIso1 BIso2 BIntegerModGroup BFreeAbelianGroup).run

initialize theSolvableGroup : IO.Ref (Option HolLibrary.GroupTheory.SolvableGroup) ← IO.mkRef none
unsafe def BSolvableGroup : HolLibrary.GroupTheory.SolvableGroup :=
  cached theSolvableGroup "setupSolvableGroup" fun _ => do
    let _ ← IO.mkRef BFreeAbelianExtra.ISOMORPHIC_FREE_ABELIAN_GROUP_UNIONS
    (HolLibrary.GroupTheory.setupSolvableGroup (deps ()) BBasics BDerived BAbelian BSubgroups BSubgroupGenerated BSubgroupGen1 BSubgroupGen2 BCosets BNormalSubgroups BQuotientGroups).run

initialize theSolvableImage : IO.Ref (Option HolLibrary.GroupTheory.SolvableImage) ← IO.mkRef none
unsafe def BSolvableImage : HolLibrary.GroupTheory.SolvableImage :=
  cached theSolvableImage "setupSolvableImage" fun _ => do
    let _ ← IO.mkRef BSolvableGroup.solvable_group
    (HolLibrary.GroupTheory.setupSolvableImage (deps ()) BBasics BDerived BAbelian BSubgroupGenerated BHomomorphisms BHomomorphisms1 BHomomorphisms2 BHomomorphisms4 BIso1 BCosets BNormalSubgroups BNormalSubgroups2 BQuotientGroups BKernelsImages1 BKernelsImages2 BSubgroupCorrespondence BSolvableGroup).run

initialize theSolvableSubgroup : IO.Ref (Option HolLibrary.GroupTheory.SolvableSubgroup) ← IO.mkRef none
unsafe def BSolvableSubgroup : HolLibrary.GroupTheory.SolvableSubgroup :=
  cached theSolvableSubgroup "setupSolvableSubgroup" fun _ => do
    let _ ← IO.mkRef BSolvableImage.ABELIAN_QUOTIENT_EPIMORPHIC_IMAGE
    (HolLibrary.GroupTheory.setupSolvableSubgroup (deps ()) BConjugation BSubgroups BSubgroupGenerated BSubgroupGen1 BSubgroupGen2 BHomomorphisms BIso1 BNormalSubgroups BKernelsImages1 BSolvableGroup BSolvableImage).run

initialize theSolvableQuotient : IO.Ref (Option HolLibrary.GroupTheory.SolvableQuotient) ← IO.mkRef none
unsafe def BSolvableQuotient : HolLibrary.GroupTheory.SolvableQuotient :=
  cached theSolvableQuotient "setupSolvableQuotient" fun _ => do
    let _ ← IO.mkRef BSolvableSubgroup.SOLVABLE_GROUP_SUBGROUP
    (HolLibrary.GroupTheory.setupSolvableQuotient (deps ()) BSubgroups BSubgroupGenerated BSubgroupGen1 BSubgroupGen2 BHomomorphisms BHomomorphisms2 BIso2 BNormalSubgroups BQuotientGroups BKernelsImages1 BSubgroupCorrespondence BSolvableGroup).run

initialize theExactSequences : IO.Ref (Option HolLibrary.GroupTheory.ExactSequences) ← IO.mkRef none
unsafe def BExactSequences : HolLibrary.GroupTheory.ExactSequences :=
  cached theExactSequences "setupExactSequences" fun _ => do
    let _ ← IO.mkRef BSolvableQuotient.SOLVABLE_GROUP_SOLVABLE_QUOTIENT
    (HolLibrary.GroupTheory.setupExactSequences (deps ()) BBasics BSubgroupGen1 BProdGroup BHomomorphisms BHomomorphisms1 BHomomorphisms2 BHomomorphisms3 BNormalSubgroups BQuotientGroups BKernelsImages1 BKernelsImages2 BTrivialHomomorphisms).run

initialize theExactSeq : IO.Ref (Option HolLibrary.GroupTheory.ExactSeq) ← IO.mkRef none
unsafe def BExactSeq : HolLibrary.GroupTheory.ExactSeq :=
  cached theExactSeq "setupExactSeq" fun _ => do
    let _ ← IO.mkRef BExactSequences.group_exactness
    (HolLibrary.GroupTheory.setupExactSeq (deps ()) BBasics BDerived BAbelian BSubgroups BSubgroupGenerated BSubgroupGen1 BProdGroup BHomomorphisms BHomomorphisms1 BHomomorphisms2 BHomomorphisms3 BHomomorphisms4 BIso1 BSetwise1 BNormalSubgroups BKernelsImages1 BKernelsImages2 BGroupDisjointSum BGroupMulMorphism BGroupSumImKer BExactSequences).run

initialize theFiveLemma : IO.Ref (Option HolLibrary.GroupTheory.FiveLemma) ← IO.mkRef none
unsafe def BFiveLemma : HolLibrary.GroupTheory.FiveLemma :=
  cached theFiveLemma "setupFiveLemma" fun _ => do
    let _ ← IO.mkRef BExactSeq.EXACT_SEQUENCE_SUM_LEMMA
    (HolLibrary.GroupTheory.setupFiveLemma (deps ()) BBasics BDerived BHomomorphisms BHomomorphisms1 BHomomorphisms2 BIso1 BKernelsImages1 BFreeAbelianGroup BExactSequences BExactSeq).run

initialize theShortFiveLemma : IO.Ref (Option HolLibrary.GroupTheory.ShortFiveLemma) ← IO.mkRef none
unsafe def BShortFiveLemma : HolLibrary.GroupTheory.ShortFiveLemma :=
  cached theShortFiveLemma "setupShortFiveLemma" fun _ => do
    let _ ← IO.mkRef BFiveLemma.SPLITTING_LEMMA_FREE_ABELIAN_GROUP
    (HolLibrary.GroupTheory.setupShortFiveLemma (deps ()) BBasics BGroupRule BProdGroup BHomomorphisms BHomomorphisms1 BHomomorphisms2 BHomomorphisms3 BKernelsImages1 BExactSequences BExactSeq BFiveLemma).run

-- @@BUNDLES END

-- @@EXPORTS BEGIN
-- Basics
unsafe def group_tybij : thm := BBasics.group_tybij
unsafe def group_carrier : thm := BBasics.group_carrier
unsafe def group_id : thm := BBasics.group_id
unsafe def group_inv : thm := BBasics.group_inv
unsafe def group_mul : thm := BBasics.group_mul
unsafe def GROUP_PROPERTIES := BBasics.GROUP_PROPERTIES
unsafe def GROUP_ID : thm := BBasics.GROUP_ID
unsafe def GROUP_INV : thm := BBasics.GROUP_INV
unsafe def GROUP_MUL : thm := BBasics.GROUP_MUL
unsafe def GROUP_MUL_ASSOC : thm := BBasics.GROUP_MUL_ASSOC
unsafe def GROUP_MUL_LID : thm := BBasics.GROUP_MUL_LID
unsafe def GROUP_MUL_RID : thm := BBasics.GROUP_MUL_RID
unsafe def GROUP_MUL_LINV : thm := BBasics.GROUP_MUL_LINV
unsafe def GROUP_MUL_RINV : thm := BBasics.GROUP_MUL_RINV
unsafe def GROUPS_EQ : thm := BBasics.GROUPS_EQ
unsafe def GROUP_CARRIER_NONEMPTY : thm := BBasics.GROUP_CARRIER_NONEMPTY
unsafe def singleton_group : thm := BBasics.singleton_group
unsafe def SINGLETON_GROUP : thm := BBasics.SINGLETON_GROUP
unsafe def trivial_group : thm := BBasics.trivial_group
unsafe def TRIVIAL_IMP_FINITE_GROUP : thm := BBasics.TRIVIAL_IMP_FINITE_GROUP
unsafe def TRIVIAL_GROUP_SINGLETON_GROUP : thm := BBasics.TRIVIAL_GROUP_SINGLETON_GROUP
unsafe def FINITE_SINGLETON_GROUP : thm := BBasics.FINITE_SINGLETON_GROUP
unsafe def TRIVIAL_GROUP_SUBSET : thm := BBasics.TRIVIAL_GROUP_SUBSET
unsafe def TRIVIAL_GROUP : thm := BBasics.TRIVIAL_GROUP
unsafe def TRIVIAL_GROUP_ALT : thm := BBasics.TRIVIAL_GROUP_ALT
unsafe def TRIVIAL_GROUP_HAS_SIZE_1 : thm := BBasics.TRIVIAL_GROUP_HAS_SIZE_1
unsafe def GROUP_CARRIER_HAS_SIZE_1 : thm := BBasics.GROUP_CARRIER_HAS_SIZE_1
unsafe def opposite_group : thm := BBasics.opposite_group
unsafe def OPPOSITE_GROUP : thm := BBasics.OPPOSITE_GROUP
unsafe def OPPOSITE_OPPOSITE_GROUP : thm := BBasics.OPPOSITE_OPPOSITE_GROUP
unsafe def OPPOSITE_GROUP_INV : thm := BBasics.OPPOSITE_GROUP_INV
unsafe def OPPOSITE_GROUP_MUL : thm := BBasics.OPPOSITE_GROUP_MUL
unsafe def OPPOSITE_SINGLETON_GROUP : thm := BBasics.OPPOSITE_SINGLETON_GROUP
unsafe def TRIVIAL_OPPOSITE_GROUP : thm := BBasics.TRIVIAL_OPPOSITE_GROUP
unsafe def FINITE_OPPOSITE_GROUP : thm := BBasics.FINITE_OPPOSITE_GROUP

-- Derived
unsafe def group_div : thm := BDerived.group_div
unsafe def GROUP_DIV : thm := BDerived.GROUP_DIV
unsafe def GROUP_MUL_LCANCEL : thm := BDerived.GROUP_MUL_LCANCEL
unsafe def GROUP_MUL_LCANCEL_IMP : thm := BDerived.GROUP_MUL_LCANCEL_IMP
unsafe def GROUP_MUL_RCANCEL : thm := BDerived.GROUP_MUL_RCANCEL
unsafe def GROUP_MUL_RCANCEL_IMP : thm := BDerived.GROUP_MUL_RCANCEL_IMP
unsafe def GROUP_LID_UNIQUE : thm := BDerived.GROUP_LID_UNIQUE
unsafe def GROUP_RID_UNIQUE : thm := BDerived.GROUP_RID_UNIQUE
unsafe def GROUP_LID_EQ : thm := BDerived.GROUP_LID_EQ
unsafe def GROUP_RID_EQ : thm := BDerived.GROUP_RID_EQ
unsafe def GROUP_LINV_UNIQUE : thm := BDerived.GROUP_LINV_UNIQUE
unsafe def GROUP_RINV_UNIQUE : thm := BDerived.GROUP_RINV_UNIQUE
unsafe def GROUP_LINV_EQ : thm := BDerived.GROUP_LINV_EQ
unsafe def GROUP_RINV_EQ : thm := BDerived.GROUP_RINV_EQ
unsafe def GROUP_MUL_EQ_ID : thm := BDerived.GROUP_MUL_EQ_ID
unsafe def GROUP_INV_INV : thm := BDerived.GROUP_INV_INV
unsafe def GROUP_INV_ID : thm := BDerived.GROUP_INV_ID
unsafe def GROUP_INV_EQ_ID : thm := BDerived.GROUP_INV_EQ_ID
unsafe def GROUP_INV_MUL : thm := BDerived.GROUP_INV_MUL
unsafe def GROUP_INV_EQ : thm := BDerived.GROUP_INV_EQ
unsafe def GROUP_DIV_REFL : thm := BDerived.GROUP_DIV_REFL
unsafe def GROUP_DIV_EQ_ID : thm := BDerived.GROUP_DIV_EQ_ID
unsafe def GROUP_COMMUTES_INV : thm := BDerived.GROUP_COMMUTES_INV
unsafe def GROUP_COMMUTES_INV_EQ : thm := BDerived.GROUP_COMMUTES_INV_EQ
unsafe def GROUP_COMMUTES_MUL : thm := BDerived.GROUP_COMMUTES_MUL
unsafe def FORALL_IN_GROUP_CARRIER_INV : thm := BDerived.FORALL_IN_GROUP_CARRIER_INV
unsafe def EXISTS_IN_GROUP_CARRIER_INV : thm := BDerived.EXISTS_IN_GROUP_CARRIER_INV
unsafe def group_pow : thm := BDerived.group_pow
unsafe def GROUP_POW : thm := BDerived.GROUP_POW
unsafe def GROUP_POW_0 : thm := BDerived.GROUP_POW_0
unsafe def GROUP_POW_1 : thm := BDerived.GROUP_POW_1
unsafe def GROUP_POW_2 : thm := BDerived.GROUP_POW_2
unsafe def GROUP_POW_ID : thm := BDerived.GROUP_POW_ID
unsafe def GROUP_POW_ADD : thm := BDerived.GROUP_POW_ADD
unsafe def GROUP_POW_SUB : thm := BDerived.GROUP_POW_SUB
unsafe def GROUP_POW_SUB_ALT : thm := BDerived.GROUP_POW_SUB_ALT
unsafe def GROUP_INV_POW : thm := BDerived.GROUP_INV_POW
unsafe def GROUP_POW_MUL : thm := BDerived.GROUP_POW_MUL
unsafe def GROUP_POW_POW : thm := BDerived.GROUP_POW_POW

-- Pow
unsafe def GROUP_COMMUTES_POW : thm := BPow.GROUP_COMMUTES_POW
unsafe def GROUP_MUL_POW : thm := BPow.GROUP_MUL_POW
unsafe def group_zpow : thm := BPow.group_zpow
unsafe def GROUP_ZPOW : thm := BPow.GROUP_ZPOW
unsafe def GROUP_NPOW : thm := BPow.GROUP_NPOW
unsafe def GROUP_ZPOW_0 : thm := BPow.GROUP_ZPOW_0
unsafe def GROUP_ZPOW_1 : thm := BPow.GROUP_ZPOW_1
unsafe def GROUP_ZPOW_2 : thm := BPow.GROUP_ZPOW_2
unsafe def GROUP_ZPOW_ID : thm := BPow.GROUP_ZPOW_ID
unsafe def GROUP_ZPOW_NEG : thm := BPow.GROUP_ZPOW_NEG
unsafe def GROUP_ZPOW_MINUS1 : thm := BPow.GROUP_ZPOW_MINUS1
unsafe def GROUP_ZPOW_POW : thm := BPow.GROUP_ZPOW_POW
unsafe def GROUP_ZPOW_ABS_EQ_ID : thm := BPow.GROUP_ZPOW_ABS_EQ_ID
unsafe def GROUP_ZPOW_ADD : thm := BPow.GROUP_ZPOW_ADD
unsafe def GROUP_ZPOW_SUB : thm := BPow.GROUP_ZPOW_SUB
unsafe def GROUP_ZPOW_SUB_ALT : thm := BPow.GROUP_ZPOW_SUB_ALT
unsafe def GROUP_INV_ZPOW : thm := BPow.GROUP_INV_ZPOW
unsafe def GROUP_ZPOW_INV : thm := BPow.GROUP_ZPOW_INV
unsafe def GROUP_ZPOW_MUL : thm := BPow.GROUP_ZPOW_MUL
unsafe def GROUP_COMMUTES_ZPOW : thm := BPow.GROUP_COMMUTES_ZPOW
unsafe def GROUP_MUL_ZPOW : thm := BPow.GROUP_MUL_ZPOW

-- Abelian
unsafe def abelian_group : thm := BAbelian.abelian_group
unsafe def TRIVIAL_IMP_ABELIAN_GROUP : thm := BAbelian.TRIVIAL_IMP_ABELIAN_GROUP
unsafe def ABELIAN_SINGLETON_GROUP : thm := BAbelian.ABELIAN_SINGLETON_GROUP
unsafe def ABELIAN_OPPOSITE_GROUP : thm := BAbelian.ABELIAN_OPPOSITE_GROUP
unsafe def ABELIAN_GROUP_MUL_POW : thm := BAbelian.ABELIAN_GROUP_MUL_POW
unsafe def ABELIAN_GROUP_MUL_ZPOW : thm := BAbelian.ABELIAN_GROUP_MUL_ZPOW
unsafe def ABELIAN_GROUP_DIV_ZPOW : thm := BAbelian.ABELIAN_GROUP_DIV_ZPOW
unsafe def ABELIAN_GROUP_MUL_AC : thm := BAbelian.ABELIAN_GROUP_MUL_AC

-- Totalized
unsafe def group_neg : thm := BTotalized.group_neg
unsafe def group_add : thm := BTotalized.group_add
unsafe def group_nmul : thm := BTotalized.group_nmul
unsafe def GROUP_NEG : thm := BTotalized.GROUP_NEG
unsafe def GROUP_ADD : thm := BTotalized.GROUP_ADD
unsafe def GROUP_NEG_EQ_INV : thm := BTotalized.GROUP_NEG_EQ_INV
unsafe def GROUP_ADD_EQ_MUL : thm := BTotalized.GROUP_ADD_EQ_MUL
unsafe def GROUP_ADD_LID : thm := BTotalized.GROUP_ADD_LID
unsafe def GROUP_ADD_RID : thm := BTotalized.GROUP_ADD_RID
unsafe def GROUP_ADD_ASSOC : thm := BTotalized.GROUP_ADD_ASSOC
unsafe def GROUP_NEG_ADD : thm := BTotalized.GROUP_NEG_ADD
unsafe def GROUP_NEG_NEG : thm := BTotalized.GROUP_NEG_NEG
unsafe def GROUP_NEG_ID : thm := BTotalized.GROUP_NEG_ID
unsafe def GROUP_ADD_EQ_ID : thm := BTotalized.GROUP_ADD_EQ_ID
unsafe def GROUP_NEG_EQ_ID : thm := BTotalized.GROUP_NEG_EQ_ID
unsafe def GROUP_NMUL_EQ_POW : thm := BTotalized.GROUP_NMUL_EQ_POW
unsafe def GROUP_NMUL_ADD : thm := BTotalized.GROUP_NMUL_ADD
unsafe def GROUP_NMUL_MUL : thm := BTotalized.GROUP_NMUL_MUL
unsafe def GROUP_NMUL_1 : thm := BTotalized.GROUP_NMUL_1
unsafe def GROUP_NEG_NMUL : thm := BTotalized.GROUP_NEG_NMUL
unsafe def GROUP_ADD_SYM : thm := BTotalized.GROUP_ADD_SYM
unsafe def GROUP_ADD_SYM_EQ : thm := BTotalized.GROUP_ADD_SYM_EQ
unsafe def GROUP_ADD_NMUL : thm := BTotalized.GROUP_ADD_NMUL
unsafe def NEUTRAL_GROUP_ADD : thm := BTotalized.NEUTRAL_GROUP_ADD
unsafe def MONOIDAL_GROUP_ADD : thm := BTotalized.MONOIDAL_GROUP_ADD

-- GroupRule
unsafe def GROUP_RULE : term → IO (Except String thm) := fun t => (BGroupRule.GROUP_RULE t).run
unsafe def GROUP_TAC : HolCore.Tactics.tactic := fun g => BGroupRule.GROUP_TAC g

-- GroupProduct
unsafe def group_product : thm := BGroupProduct.group_product
unsafe def group_sum : thm := BGroupProduct.group_sum
unsafe def GROUP_PRODUCT_EQ : thm := BGroupProduct.GROUP_PRODUCT_EQ
unsafe def GROUP_SUM_EQ : thm := BGroupProduct.GROUP_SUM_EQ
unsafe def GROUP_PRODUCT_CLOSED : thm := BGroupProduct.GROUP_PRODUCT_CLOSED
unsafe def GROUP_SUM_CLOSED : thm := BGroupProduct.GROUP_SUM_CLOSED
unsafe def GROUP_PRODUCT : thm := BGroupProduct.GROUP_PRODUCT
unsafe def GROUP_SUM : thm := BGroupProduct.GROUP_SUM
unsafe def GROUP_PRODUCT_SUPPORT : thm := BGroupProduct.GROUP_PRODUCT_SUPPORT
unsafe def GROUP_SUM_SUPPORT : thm := BGroupProduct.GROUP_SUM_SUPPORT
unsafe def GROUP_PRODUCT_RESTRICT : thm := BGroupProduct.GROUP_PRODUCT_RESTRICT
unsafe def GROUP_SUM_RESTRICT : thm := BGroupProduct.GROUP_SUM_RESTRICT
unsafe def GROUP_PRODUCT_EXPAND_CASES : thm := BGroupProduct.GROUP_PRODUCT_EXPAND_CASES
unsafe def GROUP_SUM_EXPAND_CASES : thm := BGroupProduct.GROUP_SUM_EXPAND_CASES
unsafe def GROUP_PRODUCT_RESTRICT_SET : thm := BGroupProduct.GROUP_PRODUCT_RESTRICT_SET
unsafe def GROUP_SUM_RESTRICT_SET : thm := BGroupProduct.GROUP_SUM_RESTRICT_SET
unsafe def GROUP_PRODUCT_SUPERSET : thm := BGroupProduct.GROUP_PRODUCT_SUPERSET
unsafe def GROUP_SUM_SUPERSET : thm := BGroupProduct.GROUP_SUM_SUPERSET
unsafe def GROUP_PRODUCT_CLAUSES : thm := BGroupProduct.GROUP_PRODUCT_CLAUSES
unsafe def GROUP_PRODUCT_CLAUSES_EXISTS : thm := BGroupProduct.GROUP_PRODUCT_CLAUSES_EXISTS
unsafe def GROUP_SUM_CLAUSES_EXISTS : thm := BGroupProduct.GROUP_SUM_CLAUSES_EXISTS
unsafe def GROUP_PRODUCT_EQ_ID : thm := BGroupProduct.GROUP_PRODUCT_EQ_ID
unsafe def GROUP_SUM_EQ_ID : thm := BGroupProduct.GROUP_SUM_EQ_ID
unsafe def GROUP_PRODUCT_ID : thm := BGroupProduct.GROUP_PRODUCT_ID
unsafe def GROUP_SUM_ID : thm := BGroupProduct.GROUP_SUM_ID
unsafe def GROUP_COMMUTES_PRODUCT : thm := BGroupProduct.GROUP_COMMUTES_PRODUCT
unsafe def GROUP_COMMUTES_SUM : thm := BGroupProduct.GROUP_COMMUTES_SUM
unsafe def GROUP_PRODUCT_SING : thm := BGroupProduct.GROUP_PRODUCT_SING
unsafe def GROUP_SUM_SING : thm := BGroupProduct.GROUP_SUM_SING

-- GroupProductClauses
unsafe def GROUP_PRODUCT_UNION : thm := BGroupProductClauses.GROUP_PRODUCT_UNION
unsafe def GROUP_PRODUCT_CLAUSES_LEFT : thm := BGroupProductClauses.GROUP_PRODUCT_CLAUSES_LEFT
unsafe def GROUP_PRODUCT_CLAUSES_RIGHT : thm := BGroupProductClauses.GROUP_PRODUCT_CLAUSES_RIGHT
unsafe def GROUP_PRODUCT_CLAUSES_NUMSEG : thm := BGroupProductClauses.GROUP_PRODUCT_CLAUSES_NUMSEG
unsafe def GROUP_PRODUCT_CLAUSES_COMMUTING : thm := BGroupProductClauses.GROUP_PRODUCT_CLAUSES_COMMUTING
unsafe def ABELIAN_GROUP_PRODUCT_CLAUSES : thm := BGroupProductClauses.ABELIAN_GROUP_PRODUCT_CLAUSES
unsafe def GROUP_SUM_CLAUSES_COMMUTING : thm := BGroupProductClauses.GROUP_SUM_CLAUSES_COMMUTING
unsafe def ABELIAN_GROUP_SUM_CLAUSES : thm := BGroupProductClauses.ABELIAN_GROUP_SUM_CLAUSES

-- GroupProductMul
unsafe def GROUP_PRODUCT_MUL : thm := BGroupProductMul.GROUP_PRODUCT_MUL
unsafe def GROUP_SUM_MUL : thm := BGroupProductMul.GROUP_SUM_MUL
unsafe def ABELIAN_GROUP_SUM_MUL : thm := BGroupProductMul.ABELIAN_GROUP_SUM_MUL
unsafe def GROUP_SUM_INV : thm := BGroupProductMul.GROUP_SUM_INV
unsafe def ABELIAN_GROUP_SUM_INV : thm := BGroupProductMul.ABELIAN_GROUP_SUM_INV
unsafe def GROUP_SUM_POW : thm := BGroupProductMul.GROUP_SUM_POW
unsafe def ABELIAN_GROUP_SUM_POW : thm := BGroupProductMul.ABELIAN_GROUP_SUM_POW
unsafe def GROUP_SUM_ZPOW : thm := BGroupProductMul.GROUP_SUM_ZPOW
unsafe def ABELIAN_GROUP_SUM_ZPOW : thm := BGroupProductMul.ABELIAN_GROUP_SUM_ZPOW
unsafe def GROUP_SUM_IMAGE : thm := BGroupProductMul.GROUP_SUM_IMAGE
unsafe def ABELIAN_GROUP_PRODUCT_ITERATE : thm := BGroupProductMul.ABELIAN_GROUP_PRODUCT_ITERATE
unsafe def ABELIAN_GROUP_SUM_ITERATE : thm := BGroupProductMul.ABELIAN_GROUP_SUM_ITERATE
unsafe def ABELIAN_GROUP_ITERATE : thm := BGroupProductMul.ABELIAN_GROUP_ITERATE

-- Conjugation
unsafe def group_conjugation : thm := BConjugation.group_conjugation
unsafe def GROUP_CONJUGATION : thm := BConjugation.GROUP_CONJUGATION
unsafe def GROUP_CONJUGATION_CONJUGATION : thm := BConjugation.GROUP_CONJUGATION_CONJUGATION
unsafe def GROUP_CONJUGATION_EQ : thm := BConjugation.GROUP_CONJUGATION_EQ
unsafe def GROUP_CONJUGATION_EQ_SELF : thm := BConjugation.GROUP_CONJUGATION_EQ_SELF
unsafe def GROUP_CONJUGATION_EQ_ID : thm := BConjugation.GROUP_CONJUGATION_EQ_ID
unsafe def GROUP_CONJUGATION_BY_ID : thm := BConjugation.GROUP_CONJUGATION_BY_ID
unsafe def GROUP_CONJUGATION_LINV : thm := BConjugation.GROUP_CONJUGATION_LINV
unsafe def GROUP_CONJUGATION_RINV : thm := BConjugation.GROUP_CONJUGATION_RINV
unsafe def IN_IMAGE_GROUP_CONJUGATION : thm := BConjugation.IN_IMAGE_GROUP_CONJUGATION
unsafe def IMAGE_GROUP_CONJUGATION_SUBSET : thm := BConjugation.IMAGE_GROUP_CONJUGATION_SUBSET
unsafe def IMAGE_GROUP_CONJUGATION_BY_ID : thm := BConjugation.IMAGE_GROUP_CONJUGATION_BY_ID
unsafe def IMAGE_GROUP_CONJUGATION_BY_MUL : thm := BConjugation.IMAGE_GROUP_CONJUGATION_BY_MUL
unsafe def IMAGE_GROUP_CONJUGATION_BY_INV : thm := BConjugation.IMAGE_GROUP_CONJUGATION_BY_INV
unsafe def IMAGE_GROUP_CONJUGATION_EQ_SWAP : thm := BConjugation.IMAGE_GROUP_CONJUGATION_EQ_SWAP
unsafe def IMAGE_GROUP_CONJUGATION_EQ_PREIMAGE : thm := BConjugation.IMAGE_GROUP_CONJUGATION_EQ_PREIMAGE

-- Subgroups
unsafe def subgroup_of : thm := BSubgroups.subgroup_of
unsafe def IN_SUBGROUP_ID : thm := BSubgroups.IN_SUBGROUP_ID
unsafe def IN_SUBGROUP_INV : thm := BSubgroups.IN_SUBGROUP_INV
unsafe def IN_SUBGROUP_MUL : thm := BSubgroups.IN_SUBGROUP_MUL
unsafe def IN_SUBGROUP_DIV : thm := BSubgroups.IN_SUBGROUP_DIV
unsafe def IN_SUBGROUP_POW : thm := BSubgroups.IN_SUBGROUP_POW
unsafe def IN_SUBGROUP_ZPOW : thm := BSubgroups.IN_SUBGROUP_ZPOW
unsafe def IN_SUBGROUP_CONJUGATION : thm := BSubgroups.IN_SUBGROUP_CONJUGATION
unsafe def IN_SUBGROUP_PRODUCT : thm := BSubgroups.IN_SUBGROUP_PRODUCT
unsafe def IN_SUBGROUP_SUM : thm := BSubgroups.IN_SUBGROUP_SUM
unsafe def IMAGE_GROUP_CONJUGATION_SUBGROUP : thm := BSubgroups.IMAGE_GROUP_CONJUGATION_SUBGROUP
unsafe def SUBGROUP_OF_INTERS : thm := BSubgroups.SUBGROUP_OF_INTERS
unsafe def SUBGROUP_OF_INTER : thm := BSubgroups.SUBGROUP_OF_INTER
unsafe def SUBGROUP_OF_UNIONS : thm := BSubgroups.SUBGROUP_OF_UNIONS
unsafe def SUBGROUP_OF_OPPOSITE_GROUP : thm := BSubgroups.SUBGROUP_OF_OPPOSITE_GROUP
unsafe def SUBGROUP_OF_IMP_SUBSET : thm := BSubgroups.SUBGROUP_OF_IMP_SUBSET
unsafe def SUBGROUP_OF_IMP_NONEMPTY : thm := BSubgroups.SUBGROUP_OF_IMP_NONEMPTY
unsafe def TRIVIAL_SUBGROUP_OF : thm := BSubgroups.TRIVIAL_SUBGROUP_OF
unsafe def CARRIER_SUBGROUP_OF : thm := BSubgroups.CARRIER_SUBGROUP_OF
unsafe def FINITE_SUBGROUPS : thm := BSubgroups.FINITE_SUBGROUPS
unsafe def FINITE_RESTRICTED_SUBGROUPS : thm := BSubgroups.FINITE_RESTRICTED_SUBGROUPS

-- SubgroupGenerated
unsafe def subgroup_generated : thm := BSubgroupGenerated.subgroup_generated
unsafe def SUBGROUP_GENERATED : thm := BSubgroupGenerated.SUBGROUP_GENERATED
unsafe def SUBGROUP_GENERATED_EQ : thm := BSubgroupGenerated.SUBGROUP_GENERATED_EQ
unsafe def GROUP_ID_SUBGROUP : thm := BSubgroupGenerated.GROUP_ID_SUBGROUP
unsafe def GROUP_INV_SUBGROUP : thm := BSubgroupGenerated.GROUP_INV_SUBGROUP
unsafe def GROUP_MUL_SUBGROUP : thm := BSubgroupGenerated.GROUP_MUL_SUBGROUP
unsafe def ABELIAN_SUBGROUP_GENERATED : thm := BSubgroupGenerated.ABELIAN_SUBGROUP_GENERATED
unsafe def GROUP_DIV_SUBGROUP_GENERATED : thm := BSubgroupGenerated.GROUP_DIV_SUBGROUP_GENERATED
unsafe def GROUP_POW_SUBGROUP_GENERATED : thm := BSubgroupGenerated.GROUP_POW_SUBGROUP_GENERATED
unsafe def GROUP_ZPOW_SUBGROUP_GENERATED : thm := BSubgroupGenerated.GROUP_ZPOW_SUBGROUP_GENERATED
unsafe def GROUP_CONJUGATION_SUBGROUP_GENERATED : thm := BSubgroupGenerated.GROUP_CONJUGATION_SUBGROUP_GENERATED
unsafe def SUBGROUP_GENERATED_RESTRICT : thm := BSubgroupGenerated.SUBGROUP_GENERATED_RESTRICT
unsafe def SUBGROUP_SUBGROUP_GENERATED : thm := BSubgroupGenerated.SUBGROUP_SUBGROUP_GENERATED
unsafe def SUBGROUP_GENERATED_MONO : thm := BSubgroupGenerated.SUBGROUP_GENERATED_MONO
unsafe def SUBGROUP_GENERATED_MINIMAL : thm := BSubgroupGenerated.SUBGROUP_GENERATED_MINIMAL
unsafe def SUBGROUPS_GENERATED_EQ : thm := BSubgroupGenerated.SUBGROUPS_GENERATED_EQ
unsafe def SUBGROUP_GENERATED_INDUCT : thm := BSubgroupGenerated.SUBGROUP_GENERATED_INDUCT
unsafe def GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET : thm := BSubgroupGenerated.GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET
unsafe def SUBGROUP_GENERATED_SUPERSET : thm := BSubgroupGenerated.SUBGROUP_GENERATED_SUPERSET
unsafe def SUBGROUP_OF_SUBGROUP_GENERATED_EQ : thm := BSubgroupGenerated.SUBGROUP_OF_SUBGROUP_GENERATED_EQ
unsafe def SUBGROUP_GENERATED_INDUCT_STRONG : thm := BSubgroupGenerated.SUBGROUP_GENERATED_INDUCT_STRONG
unsafe def SUBGROUP_GENERATED_INDUCT_ALT : thm := BSubgroupGenerated.SUBGROUP_GENERATED_INDUCT_ALT
unsafe def SUBGROUP_GENERATED_INDUCT_LEFT : thm := BSubgroupGenerated.SUBGROUP_GENERATED_INDUCT_LEFT

-- SubgroupGen1
unsafe def FINITE_SUBGROUP_GENERATED : thm := BSubgroupGen1.FINITE_SUBGROUP_GENERATED
unsafe def CARD_LE_SUBGROUP_GENERATED : thm := BSubgroupGen1.CARD_LE_SUBGROUP_GENERATED
unsafe def COUNTABLE_SUBGROUP_GENERATED : thm := BSubgroupGen1.COUNTABLE_SUBGROUP_GENERATED
unsafe def SUBGROUP_GENERATED_SUBSET_CARRIER : thm := BSubgroupGen1.SUBGROUP_GENERATED_SUBSET_CARRIER
unsafe def SUBSET_CARRIER_SUBGROUP_GENERATED : thm := BSubgroupGen1.SUBSET_CARRIER_SUBGROUP_GENERATED
unsafe def SUBGROUP_GENERATED_MINIMAL_EQ : thm := BSubgroupGen1.SUBGROUP_GENERATED_MINIMAL_EQ
unsafe def CARRIER_SUBGROUP_GENERATED_SUBGROUP : thm := BSubgroupGen1.CARRIER_SUBGROUP_GENERATED_SUBGROUP
unsafe def SUBGROUP_OF_SUBGROUP_GENERATED_SUBGROUP_EQ : thm := BSubgroupGen1.SUBGROUP_OF_SUBGROUP_GENERATED_SUBGROUP_EQ
unsafe def SUBGROUP_GENERATED_GROUP_CARRIER : thm := BSubgroupGen1.SUBGROUP_GENERATED_GROUP_CARRIER
unsafe def SUBGROUP_OF_SUBGROUP_GENERATED : thm := BSubgroupGen1.SUBGROUP_OF_SUBGROUP_GENERATED
unsafe def SUBGROUP_GENERATED_SUBSET_CARRIER_SUBSET : thm := BSubgroupGen1.SUBGROUP_GENERATED_SUBSET_CARRIER_SUBSET
unsafe def SUBGROUP_GENERATED_REFL : thm := BSubgroupGen1.SUBGROUP_GENERATED_REFL
unsafe def SUBGROUP_GENERATED_INC : thm := BSubgroupGen1.SUBGROUP_GENERATED_INC
unsafe def SUBGROUP_GENERATED_INC_GEN : thm := BSubgroupGen1.SUBGROUP_GENERATED_INC_GEN
unsafe def SUBGROUP_OF_SUBGROUP_GENERATED_REV : thm := BSubgroupGen1.SUBGROUP_OF_SUBGROUP_GENERATED_REV
unsafe def TRIVIAL_GROUP_SUBGROUP_GENERATED : thm := BSubgroupGen1.TRIVIAL_GROUP_SUBGROUP_GENERATED
unsafe def TRIVIAL_GROUP_SUBGROUP_GENERATED_TRIVIAL : thm := BSubgroupGen1.TRIVIAL_GROUP_SUBGROUP_GENERATED_TRIVIAL
unsafe def TRIVIAL_GROUP_SUBGROUP_GENERATED_EQ : thm := BSubgroupGen1.TRIVIAL_GROUP_SUBGROUP_GENERATED_EQ
unsafe def TRIVIAL_GROUP_GENERATED_BY_ANYTHING : thm := BSubgroupGen1.TRIVIAL_GROUP_GENERATED_BY_ANYTHING
unsafe def SUBGROUP_GENERATED_BY_SUBGROUP_GENERATED : thm := BSubgroupGen1.SUBGROUP_GENERATED_BY_SUBGROUP_GENERATED

-- SubgroupGen2
unsafe def SUBGROUP_GENERATED_INSERT_ID : thm := BSubgroupGen2.SUBGROUP_GENERATED_INSERT_ID
unsafe def GROUP_CARRIER_SUBGROUP_GENERATED_MONO : thm := BSubgroupGen2.GROUP_CARRIER_SUBGROUP_GENERATED_MONO
unsafe def SUBGROUP_GENERATED_IDEMPOT_GEN : thm := BSubgroupGen2.SUBGROUP_GENERATED_IDEMPOT_GEN
unsafe def SUBGROUP_GENERATED_IDEMPOT : thm := BSubgroupGen2.SUBGROUP_GENERATED_IDEMPOT
unsafe def SUBGROUP_GENERATED_BY_SUBGROUP_GENERATED_IDEMPOT : thm := BSubgroupGen2.SUBGROUP_GENERATED_BY_SUBGROUP_GENERATED_IDEMPOT
unsafe def SUBGROUP_GENERATED_UNION_LEFT : thm := BSubgroupGen2.SUBGROUP_GENERATED_UNION_LEFT
unsafe def SUBGROUP_GENERATED_UNION_RIGHT : thm := BSubgroupGen2.SUBGROUP_GENERATED_UNION_RIGHT
unsafe def SUBGROUP_GENERATED_UNION : thm := BSubgroupGen2.SUBGROUP_GENERATED_UNION
unsafe def TRIVIAL_GROUP_SUBGROUP_GENERATED_EMPTY : thm := BSubgroupGen2.TRIVIAL_GROUP_SUBGROUP_GENERATED_EMPTY
unsafe def SUBGROUP_OF_COMMUTING_ELEMENTS : thm := BSubgroupGen2.SUBGROUP_OF_COMMUTING_ELEMENTS
unsafe def GROUP_COMMUTES_SUBGROUP_GENERATED_EQ : thm := BSubgroupGen2.GROUP_COMMUTES_SUBGROUP_GENERATED_EQ
unsafe def GROUP_COMMUTES_SUBGROUP_GENERATED : thm := BSubgroupGen2.GROUP_COMMUTES_SUBGROUP_GENERATED
unsafe def GROUP_COMMUTES_SUBGROUPS_GENERATED_EQ : thm := BSubgroupGen2.GROUP_COMMUTES_SUBGROUPS_GENERATED_EQ
unsafe def ABELIAN_GROUP_SUBGROUP_GENERATED_GEN : thm := BSubgroupGen2.ABELIAN_GROUP_SUBGROUP_GENERATED_GEN

-- ProdGroup
unsafe def prod_group : thm := BProdGroup.prod_group
unsafe def PROD_GROUP : thm := BProdGroup.PROD_GROUP
unsafe def GROUP_POW_PROD_GROUP : thm := BProdGroup.GROUP_POW_PROD_GROUP
unsafe def GROUP_ZPOW_PROD_GROUP : thm := BProdGroup.GROUP_ZPOW_PROD_GROUP
unsafe def OPPOSITE_PROD_GROUP : thm := BProdGroup.OPPOSITE_PROD_GROUP
unsafe def TRIVIAL_PROD_GROUP : thm := BProdGroup.TRIVIAL_PROD_GROUP
unsafe def FINITE_PROD_GROUP : thm := BProdGroup.FINITE_PROD_GROUP
unsafe def ABELIAN_PROD_GROUP : thm := BProdGroup.ABELIAN_PROD_GROUP
unsafe def CROSS_SUBGROUP_OF_PROD_GROUP : thm := BProdGroup.CROSS_SUBGROUP_OF_PROD_GROUP
unsafe def PROD_GROUP_SUBGROUP_GENERATED : thm := BProdGroup.PROD_GROUP_SUBGROUP_GENERATED
unsafe def product_group : thm := BProdGroup.product_group

-- ProductGroup
unsafe def PRODUCT_GROUP : thm := BProductGroup.PRODUCT_GROUP
unsafe def GROUP_POW_PRODUCT_GROUP : thm := BProductGroup.GROUP_POW_PRODUCT_GROUP
unsafe def GROUP_ZPOW_PRODUCT_GROUP : thm := BProductGroup.GROUP_ZPOW_PRODUCT_GROUP
unsafe def OPPOSITE_PRODUCT_GROUP : thm := BProductGroup.OPPOSITE_PRODUCT_GROUP
unsafe def GROUP_PRODUCT_INJECTION : thm := BProductGroup.GROUP_PRODUCT_INJECTION
unsafe def TRIVIAL_PRODUCT_GROUP : thm := BProductGroup.TRIVIAL_PRODUCT_GROUP
unsafe def CARTESIAN_PRODUCT_SUBGROUP_OF_PRODUCT_GROUP : thm := BProductGroup.CARTESIAN_PRODUCT_SUBGROUP_OF_PRODUCT_GROUP
unsafe def PRODUCT_GROUP_SUBGROUP_GENERATED : thm := BProductGroup.PRODUCT_GROUP_SUBGROUP_GENERATED
unsafe def FINITE_PRODUCT_GROUP : thm := BProductGroup.FINITE_PRODUCT_GROUP
unsafe def ABELIAN_PRODUCT_GROUP : thm := BProductGroup.ABELIAN_PRODUCT_GROUP

-- SumGroup
unsafe def sum_group : thm := BSumGroup.sum_group
unsafe def SUM_GROUP_ALT : thm := BSumGroup.SUM_GROUP_ALT
unsafe def SUM_GROUP_EQ_PRODUCT_GROUP : thm := BSumGroup.SUM_GROUP_EQ_PRODUCT_GROUP
unsafe def SUBGROUP_SUM_GROUP : thm := BSumGroup.SUBGROUP_SUM_GROUP
unsafe def SUM_GROUP_CLAUSES : thm := BSumGroup.SUM_GROUP_CLAUSES
unsafe def GROUP_POW_SUM_GROUP : thm := BSumGroup.GROUP_POW_SUM_GROUP
unsafe def GROUP_ZPOW_SUM_GROUP : thm := BSumGroup.GROUP_ZPOW_SUM_GROUP
unsafe def GROUP_SUM_INJECTION : thm := BSumGroup.GROUP_SUM_INJECTION
unsafe def TRIVIAL_SUM_GROUP : thm := BSumGroup.TRIVIAL_SUM_GROUP
unsafe def CARTESIAN_PRODUCT_SUBGROUP_OF_SUM_GROUP : thm := BSumGroup.CARTESIAN_PRODUCT_SUBGROUP_OF_SUM_GROUP
unsafe def SUM_GROUP_SUBGROUP_GENERATED : thm := BSumGroup.SUM_GROUP_SUBGROUP_GENERATED
unsafe def ABELIAN_SUM_GROUP : thm := BSumGroup.ABELIAN_SUM_GROUP

-- Homomorphisms
unsafe def group_homomorphism : thm := BHomomorphisms.group_homomorphism
unsafe def group_monomorphism : thm := BHomomorphisms.group_monomorphism
unsafe def group_epimorphism : thm := BHomomorphisms.group_epimorphism
unsafe def group_endomorphism : thm := BHomomorphisms.group_endomorphism
unsafe def group_isomorphisms : thm := BHomomorphisms.group_isomorphisms
unsafe def group_isomorphism : thm := BHomomorphisms.group_isomorphism
unsafe def group_automorphism : thm := BHomomorphisms.group_automorphism
unsafe def GROUP_HOMOMORPHISM_EQ : thm := BHomomorphisms.GROUP_HOMOMORPHISM_EQ
unsafe def GROUP_MONOMORPHISM_EQ : thm := BHomomorphisms.GROUP_MONOMORPHISM_EQ
unsafe def GROUP_EPIMORPHISM_EQ : thm := BHomomorphisms.GROUP_EPIMORPHISM_EQ
unsafe def GROUP_ENDOMORPHISM_EQ : thm := BHomomorphisms.GROUP_ENDOMORPHISM_EQ
unsafe def GROUP_ISOMORPHISMS_EQ : thm := BHomomorphisms.GROUP_ISOMORPHISMS_EQ
unsafe def GROUP_ISOMORPHISM_EQ : thm := BHomomorphisms.GROUP_ISOMORPHISM_EQ
unsafe def GROUP_AUTOMORPHISM_EQ : thm := BHomomorphisms.GROUP_AUTOMORPHISM_EQ
unsafe def GROUP_HOMOMORPHISMS_EQ_ON_GENERATORS : thm := BHomomorphisms.GROUP_HOMOMORPHISMS_EQ_ON_GENERATORS
unsafe def GROUP_ISOMORPHISMS_SYM : thm := BHomomorphisms.GROUP_ISOMORPHISMS_SYM
unsafe def GROUP_ISOMORPHISMS_IMP_ISOMORPHISM : thm := BHomomorphisms.GROUP_ISOMORPHISMS_IMP_ISOMORPHISM
unsafe def GROUP_ISOMORPHISMS_IMP_ISOMORPHISM_ALT : thm := BHomomorphisms.GROUP_ISOMORPHISMS_IMP_ISOMORPHISM_ALT
unsafe def GROUP_HOMOMORPHISM : thm := BHomomorphisms.GROUP_HOMOMORPHISM
unsafe def GROUP_EPIMORPHISM_SUBSET : thm := BHomomorphisms.GROUP_EPIMORPHISM_SUBSET
unsafe def GROUP_ISOMORPHISMS : thm := BHomomorphisms.GROUP_ISOMORPHISMS
unsafe def GROUP_HOMOMORPHISM_OF_ID : thm := BHomomorphisms.GROUP_HOMOMORPHISM_OF_ID

-- Homomorphisms1
unsafe def GROUP_HOMOMORPHISM_INV : thm := BHomomorphisms1.GROUP_HOMOMORPHISM_INV
unsafe def GROUP_HOMOMORPHISM_MUL : thm := BHomomorphisms1.GROUP_HOMOMORPHISM_MUL
unsafe def GROUP_HOMOMORPHISM_DIV : thm := BHomomorphisms1.GROUP_HOMOMORPHISM_DIV
unsafe def GROUP_HOMOMORPHISM_POW : thm := BHomomorphisms1.GROUP_HOMOMORPHISM_POW
unsafe def GROUP_HOMOMORPHISM_ZPOW : thm := BHomomorphisms1.GROUP_HOMOMORPHISM_ZPOW
unsafe def GROUP_HOMOMORPHISM_TRIVIAL : thm := BHomomorphisms1.GROUP_HOMOMORPHISM_TRIVIAL
unsafe def GROUP_HOMOMORPHISM_ID : thm := BHomomorphisms1.GROUP_HOMOMORPHISM_ID
unsafe def GROUP_MONOMORPHISM_ID : thm := BHomomorphisms1.GROUP_MONOMORPHISM_ID
unsafe def GROUP_EPIMORPHISM_ID : thm := BHomomorphisms1.GROUP_EPIMORPHISM_ID
unsafe def GROUP_ISOMORPHISMS_ID : thm := BHomomorphisms1.GROUP_ISOMORPHISMS_ID
unsafe def GROUP_ISOMORPHISM_ID : thm := BHomomorphisms1.GROUP_ISOMORPHISM_ID
unsafe def GROUP_HOMOMORPHISM_COMPOSE : thm := BHomomorphisms1.GROUP_HOMOMORPHISM_COMPOSE
unsafe def GROUP_MONOMORPHISM_COMPOSE : thm := BHomomorphisms1.GROUP_MONOMORPHISM_COMPOSE
unsafe def GROUP_MONOMORPHISM_COMPOSE_REV : thm := BHomomorphisms1.GROUP_MONOMORPHISM_COMPOSE_REV
unsafe def GROUP_EPIMORPHISM_COMPOSE : thm := BHomomorphisms1.GROUP_EPIMORPHISM_COMPOSE
unsafe def GROUP_EPIMORPHISM_COMPOSE_REV : thm := BHomomorphisms1.GROUP_EPIMORPHISM_COMPOSE_REV
unsafe def GROUP_MONOMORPHISM_LEFT_INVERTIBLE : thm := BHomomorphisms1.GROUP_MONOMORPHISM_LEFT_INVERTIBLE
unsafe def GROUP_EPIMORPHISM_RIGHT_INVERTIBLE : thm := BHomomorphisms1.GROUP_EPIMORPHISM_RIGHT_INVERTIBLE
unsafe def GROUP_HOMOMORPHISM_INTO_SUBGROUP : thm := BHomomorphisms1.GROUP_HOMOMORPHISM_INTO_SUBGROUP
unsafe def GROUP_HOMOMORPHISM_INTO_SUBGROUP_EQ_GEN : thm := BHomomorphisms1.GROUP_HOMOMORPHISM_INTO_SUBGROUP_EQ_GEN
unsafe def GROUP_HOMOMORPHISM_INTO_SUBGROUP_EQ : thm := BHomomorphisms1.GROUP_HOMOMORPHISM_INTO_SUBGROUP_EQ
unsafe def GROUP_HOMOMORPHISM_FROM_SUBGROUP_GENERATED : thm := BHomomorphisms1.GROUP_HOMOMORPHISM_FROM_SUBGROUP_GENERATED
unsafe def GROUP_HOMOMORPHISM_BETWEEN_SUBGROUPS : thm := BHomomorphisms1.GROUP_HOMOMORPHISM_BETWEEN_SUBGROUPS
unsafe def GROUP_HOMOMORPHISM_BETWEEN_SUBGROUPS_ALT : thm := BHomomorphisms1.GROUP_HOMOMORPHISM_BETWEEN_SUBGROUPS_ALT
unsafe def GROUP_MONOMORPHISM_FROM_SUBGROUP_GENERATED : thm := BHomomorphisms1.GROUP_MONOMORPHISM_FROM_SUBGROUP_GENERATED
unsafe def GROUP_MONOMORPHISM_BETWEEN_SUBGROUPS : thm := BHomomorphisms1.GROUP_MONOMORPHISM_BETWEEN_SUBGROUPS
unsafe def GROUP_MONOMORPHISM_INTO_SUPERGROUP : thm := BHomomorphisms1.GROUP_MONOMORPHISM_INTO_SUPERGROUP
unsafe def GROUP_HOMOMORPHISM_INCLUSION : thm := BHomomorphisms1.GROUP_HOMOMORPHISM_INCLUSION
unsafe def GROUP_MONOMORPHISM_INCLUSION : thm := BHomomorphisms1.GROUP_MONOMORPHISM_INCLUSION

-- Homomorphisms2
unsafe def SUBGROUP_GENERATED_BY_HOMOMORPHIC_IMAGE : thm := BHomomorphisms2.SUBGROUP_GENERATED_BY_HOMOMORPHIC_IMAGE
unsafe def SUBGROUP_GENERATED_BY_HOMOMORPHIC_IMAGE_EQ : thm := BHomomorphisms2.SUBGROUP_GENERATED_BY_HOMOMORPHIC_IMAGE_EQ
unsafe def SUBGROUP_GENERATED_BY_EPIMORPHIC_IMAGE : thm := BHomomorphisms2.SUBGROUP_GENERATED_BY_EPIMORPHIC_IMAGE
unsafe def GROUP_EPIMORPHISM_BETWEEN_SUBGROUPS : thm := BHomomorphisms2.GROUP_EPIMORPHISM_BETWEEN_SUBGROUPS
unsafe def GROUP_EPIMORPHISM_INTO_SUBGROUP_EQ_GEN : thm := BHomomorphisms2.GROUP_EPIMORPHISM_INTO_SUBGROUP_EQ_GEN
unsafe def GROUP_EPIMORPHISM_INTO_SUBGROUP_EQ : thm := BHomomorphisms2.GROUP_EPIMORPHISM_INTO_SUBGROUP_EQ
unsafe def GROUP_ISOMORPHISM : thm := BHomomorphisms2.GROUP_ISOMORPHISM
unsafe def GROUP_ISOMORPHISM_SUBSET : thm := BHomomorphisms2.GROUP_ISOMORPHISM_SUBSET
unsafe def SUBGROUP_OF_HOMOMORPHIC_IMAGE : thm := BHomomorphisms2.SUBGROUP_OF_HOMOMORPHIC_IMAGE
unsafe def SUBGROUP_OF_HOMOMORPHIC_PREIMAGE : thm := BHomomorphisms2.SUBGROUP_OF_HOMOMORPHIC_PREIMAGE
unsafe def SUBGROUP_OF_EPIMORPHIC_PREIMAGE : thm := BHomomorphisms2.SUBGROUP_OF_EPIMORPHIC_PREIMAGE
unsafe def GROUP_MONOMORPHISM_EPIMORPHISM : thm := BHomomorphisms2.GROUP_MONOMORPHISM_EPIMORPHISM
unsafe def GROUP_ISOMORPHISM_EPIMORPHISM : thm := BHomomorphisms2.GROUP_ISOMORPHISM_EPIMORPHISM
unsafe def SUBGROUP_MONOMORPHISM_EPIMORPHISM : thm := BHomomorphisms2.SUBGROUP_MONOMORPHISM_EPIMORPHISM
unsafe def GROUP_ISOMORPHISM_IMP_MONOMORPHISM : thm := BHomomorphisms2.GROUP_ISOMORPHISM_IMP_MONOMORPHISM
unsafe def GROUP_ISOMORPHISM_IMP_EPIMORPHISM : thm := BHomomorphisms2.GROUP_ISOMORPHISM_IMP_EPIMORPHISM
unsafe def GROUP_MONOMORPHISM_IMP_HOMOMORPHISM : thm := BHomomorphisms2.GROUP_MONOMORPHISM_IMP_HOMOMORPHISM
unsafe def GROUP_EPIMORPHISM_IMP_HOMOMORPHISM : thm := BHomomorphisms2.GROUP_EPIMORPHISM_IMP_HOMOMORPHISM
unsafe def GROUP_ISOMORPHISM_IMP_HOMOMORPHISM : thm := BHomomorphisms2.GROUP_ISOMORPHISM_IMP_HOMOMORPHISM
unsafe def GROUP_AUTOMORPHISM_IMP_ENDOMORPHISM : thm := BHomomorphisms2.GROUP_AUTOMORPHISM_IMP_ENDOMORPHISM
unsafe def GROUP_ISOMORPHISM_EQ_MONOMORPHISM_FINITE : thm := BHomomorphisms2.GROUP_ISOMORPHISM_EQ_MONOMORPHISM_FINITE
unsafe def GROUP_ISOMORPHISM_EQ_EPIMORPHISM_FINITE : thm := BHomomorphisms2.GROUP_ISOMORPHISM_EQ_EPIMORPHISM_FINITE
unsafe def GROUP_ISOMORPHISMS_CONJUGATION : thm := BHomomorphisms2.GROUP_ISOMORPHISMS_CONJUGATION
unsafe def GROUP_AUTOMORPHISM_CONJUGATION : thm := BHomomorphisms2.GROUP_AUTOMORPHISM_CONJUGATION
unsafe def GROUP_ISOMORPHISM_CONJUGATION : thm := BHomomorphisms2.GROUP_ISOMORPHISM_CONJUGATION
unsafe def GROUP_HOMOMORPHISM_CONJUGATION : thm := BHomomorphisms2.GROUP_HOMOMORPHISM_CONJUGATION
unsafe def CARD_LE_GROUP_MONOMORPHIC_IMAGE : thm := BHomomorphisms2.CARD_LE_GROUP_MONOMORPHIC_IMAGE
unsafe def CARD_LE_GROUP_EPIMORPHIC_IMAGE : thm := BHomomorphisms2.CARD_LE_GROUP_EPIMORPHIC_IMAGE

-- Homomorphisms3
unsafe def CARD_EQ_GROUP_ISOMORPHIC_IMAGE : thm := BHomomorphisms3.CARD_EQ_GROUP_ISOMORPHIC_IMAGE
unsafe def FINITE_GROUP_MONOMORPHIC_PREIMAGE : thm := BHomomorphisms3.FINITE_GROUP_MONOMORPHIC_PREIMAGE
unsafe def FINITE_GROUP_EPIMORPHIC_IMAGE : thm := BHomomorphisms3.FINITE_GROUP_EPIMORPHIC_IMAGE
unsafe def CARD_EQ_GROUP_MONOMORPHIC_IMAGE : thm := BHomomorphisms3.CARD_EQ_GROUP_MONOMORPHIC_IMAGE
unsafe def GROUP_ISOMORPHISMS_BETWEEN_SUBGROUPS : thm := BHomomorphisms3.GROUP_ISOMORPHISMS_BETWEEN_SUBGROUPS
unsafe def GROUP_ISOMORPHISMS_BETWEEN_SUBGROUPS_ALT : thm := BHomomorphisms3.GROUP_ISOMORPHISMS_BETWEEN_SUBGROUPS_ALT
unsafe def GROUP_ISOMORPHISM_BETWEEN_SUBGROUPS : thm := BHomomorphisms3.GROUP_ISOMORPHISM_BETWEEN_SUBGROUPS
unsafe def GROUP_ISOMORPHISMS_COMPOSE : thm := BHomomorphisms3.GROUP_ISOMORPHISMS_COMPOSE
unsafe def GROUP_ISOMORPHISM_COMPOSE : thm := BHomomorphisms3.GROUP_ISOMORPHISM_COMPOSE
unsafe def GROUP_ISOMORPHISM_COMPOSE_REV : thm := BHomomorphisms3.GROUP_ISOMORPHISM_COMPOSE_REV
unsafe def GROUP_EPIMORPHISM_ISOMORPHISM_COMPOSE_REV : thm := BHomomorphisms3.GROUP_EPIMORPHISM_ISOMORPHISM_COMPOSE_REV
unsafe def GROUP_MONOMORPHISM_ISOMORPHISM_COMPOSE_REV : thm := BHomomorphisms3.GROUP_MONOMORPHISM_ISOMORPHISM_COMPOSE_REV
unsafe def GROUP_ISOMORPHISM_INVERSE : thm := BHomomorphisms3.GROUP_ISOMORPHISM_INVERSE
unsafe def GROUP_ISOMORPHISMS_OPPOSITE_GROUP : thm := BHomomorphisms3.GROUP_ISOMORPHISMS_OPPOSITE_GROUP
unsafe def GROUP_ISOMORPHISM_OPPOSITE_GROUP : thm := BHomomorphisms3.GROUP_ISOMORPHISM_OPPOSITE_GROUP
unsafe def GROUP_HOMOMORPHISM_FROM_TRIVIAL_GROUP : thm := BHomomorphisms3.GROUP_HOMOMORPHISM_FROM_TRIVIAL_GROUP
unsafe def GROUP_MONOMORPHISM_FROM_TRIVIAL_GROUP : thm := BHomomorphisms3.GROUP_MONOMORPHISM_FROM_TRIVIAL_GROUP
unsafe def GROUP_MONOMORPHISM_TO_TRIVIAL_GROUP : thm := BHomomorphisms3.GROUP_MONOMORPHISM_TO_TRIVIAL_GROUP
unsafe def GROUP_EPIMORPHISM_FROM_TRIVIAL_GROUP : thm := BHomomorphisms3.GROUP_EPIMORPHISM_FROM_TRIVIAL_GROUP
unsafe def GROUP_EPIMORPHISM_TO_TRIVIAL_GROUP : thm := BHomomorphisms3.GROUP_EPIMORPHISM_TO_TRIVIAL_GROUP
unsafe def GROUP_HOMOMORPHISM_PAIRWISE : thm := BHomomorphisms3.GROUP_HOMOMORPHISM_PAIRWISE
unsafe def GROUP_HOMOMORPHISM_PAIRED : thm := BHomomorphisms3.GROUP_HOMOMORPHISM_PAIRED
unsafe def GROUP_HOMOMORPHISM_PAIRED2 : thm := BHomomorphisms3.GROUP_HOMOMORPHISM_PAIRED2
unsafe def GROUP_ISOMORPHISMS_PAIRED2 : thm := BHomomorphisms3.GROUP_ISOMORPHISMS_PAIRED2
unsafe def GROUP_ISOMORPHISM_PAIRED2 : thm := BHomomorphisms3.GROUP_ISOMORPHISM_PAIRED2
unsafe def GROUP_HOMOMORPHISM_OF_FST : thm := BHomomorphisms3.GROUP_HOMOMORPHISM_OF_FST
unsafe def GROUP_HOMOMORPHISM_OF_SND : thm := BHomomorphisms3.GROUP_HOMOMORPHISM_OF_SND
unsafe def GROUP_EPIMORPHISM_OF_FST : thm := BHomomorphisms3.GROUP_EPIMORPHISM_OF_FST
unsafe def GROUP_EPIMORPHISM_OF_SND : thm := BHomomorphisms3.GROUP_EPIMORPHISM_OF_SND
unsafe def GROUP_HOMOMORPHISM_FST : thm := BHomomorphisms3.GROUP_HOMOMORPHISM_FST
unsafe def GROUP_HOMOMORPHISM_SND : thm := BHomomorphisms3.GROUP_HOMOMORPHISM_SND
unsafe def GROUP_EPIMORPHISM_FST : thm := BHomomorphisms3.GROUP_EPIMORPHISM_FST
unsafe def GROUP_EPIMORPHISM_SND : thm := BHomomorphisms3.GROUP_EPIMORPHISM_SND
unsafe def GROUP_ISOMORPHISM_FST : thm := BHomomorphisms3.GROUP_ISOMORPHISM_FST
unsafe def GROUP_ISOMORPHISM_SND : thm := BHomomorphisms3.GROUP_ISOMORPHISM_SND
unsafe def GROUP_ISOMORPHISMS_PROD_GROUP_SWAP : thm := BHomomorphisms3.GROUP_ISOMORPHISMS_PROD_GROUP_SWAP

-- Homomorphisms4
unsafe def GROUP_HOMOMORPHISM_COMPONENTWISE : thm := BHomomorphisms4.GROUP_HOMOMORPHISM_COMPONENTWISE
unsafe def GROUP_HOMOMORPHISM_COMPONENTWISE_UNIV : thm := BHomomorphisms4.GROUP_HOMOMORPHISM_COMPONENTWISE_UNIV
unsafe def GROUP_HOMOMORPHISM_PRODUCT_PROJECTION : thm := BHomomorphisms4.GROUP_HOMOMORPHISM_PRODUCT_PROJECTION
unsafe def GROUP_HOMOMORPHISM_SUM_PROJECTION : thm := BHomomorphisms4.GROUP_HOMOMORPHISM_SUM_PROJECTION
unsafe def GROUP_HOMOMORPHISM_PRODUCT_INJECTION : thm := BHomomorphisms4.GROUP_HOMOMORPHISM_PRODUCT_INJECTION
unsafe def GROUP_HOMOMORPHISM_SUM_INJECTION : thm := BHomomorphisms4.GROUP_HOMOMORPHISM_SUM_INJECTION
unsafe def GROUP_HOMOMORPHISM_PRODUCT : thm := BHomomorphisms4.GROUP_HOMOMORPHISM_PRODUCT
unsafe def GROUP_HOMOMORPHISM_SUM : thm := BHomomorphisms4.GROUP_HOMOMORPHISM_SUM
unsafe def GROUP_EPIMORPHISM_PRODUCT_PROJECTION : thm := BHomomorphisms4.GROUP_EPIMORPHISM_PRODUCT_PROJECTION
unsafe def GROUP_ISOMORPHISM_PRODUCT_PROJECTION : thm := BHomomorphisms4.GROUP_ISOMORPHISM_PRODUCT_PROJECTION
unsafe def GROUP_EPIMORPHISM_SUM_PROJECTION : thm := BHomomorphisms4.GROUP_EPIMORPHISM_SUM_PROJECTION
unsafe def GROUP_ISOMORPHISM_SUM_PROJECTION : thm := BHomomorphisms4.GROUP_ISOMORPHISM_SUM_PROJECTION
unsafe def ABELIAN_GROUP_EPIMORPHIC_IMAGE : thm := BHomomorphisms4.ABELIAN_GROUP_EPIMORPHIC_IMAGE
unsafe def ABELIAN_GROUP_HOMOMORPHISM_GROUP_MUL : thm := BHomomorphisms4.ABELIAN_GROUP_HOMOMORPHISM_GROUP_MUL
unsafe def ABELIAN_GROUP_HOMOMORPHISM_INVERSION : thm := BHomomorphisms4.ABELIAN_GROUP_HOMOMORPHISM_INVERSION
unsafe def ABELIAN_GROUP_ISOMORPHISMS_INVERSION : thm := BHomomorphisms4.ABELIAN_GROUP_ISOMORPHISMS_INVERSION
unsafe def ABELIAN_GROUP_ISOMORPHISM_INVERSION : thm := BHomomorphisms4.ABELIAN_GROUP_ISOMORPHISM_INVERSION
unsafe def ABELIAN_GROUP_MONOMORPHISM_INVERSION : thm := BHomomorphisms4.ABELIAN_GROUP_MONOMORPHISM_INVERSION
unsafe def ABELIAN_GROUP_EPIMORPHISM_INVERSION : thm := BHomomorphisms4.ABELIAN_GROUP_EPIMORPHISM_INVERSION
unsafe def ABELIAN_GROUP_HOMOMORPHISM_POWERING : thm := BHomomorphisms4.ABELIAN_GROUP_HOMOMORPHISM_POWERING
unsafe def ABELIAN_GROUP_HOMOMORPHISM_ZPOWERING : thm := BHomomorphisms4.ABELIAN_GROUP_HOMOMORPHISM_ZPOWERING

-- Iso1
unsafe def isomorphic_group : thm := BIso1.isomorphic_group
unsafe def GROUP_ISOMORPHISM_IMP_ISOMORPHIC : thm := BIso1.GROUP_ISOMORPHISM_IMP_ISOMORPHIC
unsafe def ISOMORPHIC_PRODUCT_GROUP_SING : thm := BIso1.ISOMORPHIC_PRODUCT_GROUP_SING
unsafe def ISOMORPHIC_SUM_GROUP_SING : thm := BIso1.ISOMORPHIC_SUM_GROUP_SING
unsafe def ISOMORPHIC_GROUP_REFL : thm := BIso1.ISOMORPHIC_GROUP_REFL
unsafe def ISOMORPHIC_GROUP_SYM : thm := BIso1.ISOMORPHIC_GROUP_SYM
unsafe def ISOMORPHIC_GROUP_TRANS : thm := BIso1.ISOMORPHIC_GROUP_TRANS
unsafe def ISOMORPHIC_GROUP_OPPOSITE_GROUP : thm := BIso1.ISOMORPHIC_GROUP_OPPOSITE_GROUP
unsafe def ISOMORPHIC_GROUP_TRIVIALITY : thm := BIso1.ISOMORPHIC_GROUP_TRIVIALITY
unsafe def ISOMORPHIC_TO_TRIVIAL_GROUP : thm := BIso1.ISOMORPHIC_TO_TRIVIAL_GROUP
unsafe def ISOMORPHIC_TRIVIAL_GROUPS : thm := BIso1.ISOMORPHIC_TRIVIAL_GROUPS
unsafe def ISOMORPHIC_GROUP_SINGLETON_GROUP : thm := BIso1.ISOMORPHIC_GROUP_SINGLETON_GROUP
unsafe def ISOMORPHIC_GROUP_PROD_GROUPS : thm := BIso1.ISOMORPHIC_GROUP_PROD_GROUPS
unsafe def ISOMORPHIC_GROUP_PROD_GROUP_SYM : thm := BIso1.ISOMORPHIC_GROUP_PROD_GROUP_SYM
unsafe def ISOMORPHIC_GROUP_PROD_GROUP_SWAP_LEFT : thm := BIso1.ISOMORPHIC_GROUP_PROD_GROUP_SWAP_LEFT
unsafe def ISOMORPHIC_GROUP_PROD_GROUP_SWAP_RIGHT : thm := BIso1.ISOMORPHIC_GROUP_PROD_GROUP_SWAP_RIGHT
unsafe def ISOMORPHIC_PROD_TRIVIAL_GROUP : thm := BIso1.ISOMORPHIC_PROD_TRIVIAL_GROUP
unsafe def ISOMORPHIC_PRODUCT_GROUP_SUPPORT : thm := BIso1.ISOMORPHIC_PRODUCT_GROUP_SUPPORT
unsafe def ISOMORPHIC_PRODUCT_GROUP_SYMDIFF : thm := BIso1.ISOMORPHIC_PRODUCT_GROUP_SYMDIFF
unsafe def ISOMORPHIC_SUM_GROUP_SUPPORT : thm := BIso1.ISOMORPHIC_SUM_GROUP_SUPPORT
unsafe def ISOMORPHIC_SUM_GROUP_SYMDIFF : thm := BIso1.ISOMORPHIC_SUM_GROUP_SYMDIFF

-- Iso2
unsafe def ISOMORPHIC_PRODUCT_GROUP_BIJECTIONS : thm := BIso2.ISOMORPHIC_PRODUCT_GROUP_BIJECTIONS
unsafe def ISOMORPHIC_SUM_GROUP_BIJECTIONS : thm := BIso2.ISOMORPHIC_SUM_GROUP_BIJECTIONS
unsafe def ISOMORPHIC_GROUP_PRODUCT_GROUP : thm := BIso2.ISOMORPHIC_GROUP_PRODUCT_GROUP
unsafe def ISOMORPHIC_GROUP_SUM_GROUP : thm := BIso2.ISOMORPHIC_GROUP_SUM_GROUP
unsafe def GROUP_ISOMORPHISMS_PRODUCT_GROUP_DISJOINT_UNION : thm := BIso2.GROUP_ISOMORPHISMS_PRODUCT_GROUP_DISJOINT_UNION
unsafe def GROUP_ISOMORPHISMS_SUM_GROUP_DISJOINT_UNION : thm := BIso2.GROUP_ISOMORPHISMS_SUM_GROUP_DISJOINT_UNION
unsafe def GROUP_ISOMORPHISM_PRODUCT_GROUP_DISJOINT_UNION : thm := BIso2.GROUP_ISOMORPHISM_PRODUCT_GROUP_DISJOINT_UNION
unsafe def GROUP_ISOMORPHISM_SUM_GROUP_DISJOINT_UNION : thm := BIso2.GROUP_ISOMORPHISM_SUM_GROUP_DISJOINT_UNION
unsafe def ISOMORPHIC_PRODUCT_GROUP_DISJOINT_UNION : thm := BIso2.ISOMORPHIC_PRODUCT_GROUP_DISJOINT_UNION
unsafe def ISOMORPHIC_SUM_GROUP_DISJOINT_UNION : thm := BIso2.ISOMORPHIC_SUM_GROUP_DISJOINT_UNION
unsafe def ISOMORPHIC_PRODUCT_GROUP_INSERT : thm := BIso2.ISOMORPHIC_PRODUCT_GROUP_INSERT
unsafe def ISOMORPHIC_SUM_GROUP_INSERT : thm := BIso2.ISOMORPHIC_SUM_GROUP_INSERT
unsafe def ISOMORPHIC_GROUP_CARD_EQ : thm := BIso2.ISOMORPHIC_GROUP_CARD_EQ
unsafe def ISOMORPHIC_GROUP_FINITENESS : thm := BIso2.ISOMORPHIC_GROUP_FINITENESS
unsafe def ISOMORPHIC_GROUP_INFINITENESS : thm := BIso2.ISOMORPHIC_GROUP_INFINITENESS
unsafe def ISOMORPHIC_GROUP_HAS_ORDER : thm := BIso2.ISOMORPHIC_GROUP_HAS_ORDER
unsafe def ISOMORPHIC_GROUP_ORDER : thm := BIso2.ISOMORPHIC_GROUP_ORDER
unsafe def ISOMORPHIC_GROUP_ABELIANNESS : thm := BIso2.ISOMORPHIC_GROUP_ABELIANNESS
unsafe def CREATE_ISOMORPHIC_COPY_OF_GROUP : thm := BIso2.CREATE_ISOMORPHIC_COPY_OF_GROUP
unsafe def ISOMORPHIC_COPY_OF_GROUP : thm := BIso2.ISOMORPHIC_COPY_OF_GROUP

-- DirectLimit
unsafe def GROUP_DIRECT_LIMIT : thm := BDirectLimit.GROUP_DIRECT_LIMIT

-- Setwise1
unsafe def group_setinv : thm := BSetwise1.group_setinv
unsafe def group_setmul : thm := BSetwise1.group_setmul
unsafe def GROUP_SETINV_AS_IMAGE : thm := BSetwise1.GROUP_SETINV_AS_IMAGE
unsafe def SUBGROUP_OF_SETWISE : thm := BSetwise1.SUBGROUP_OF_SETWISE
unsafe def FINITE_SUBGROUP_OF_SETWISE : thm := BSetwise1.FINITE_SUBGROUP_OF_SETWISE
unsafe def OPPOSITE_GROUP_SETINV : thm := BSetwise1.OPPOSITE_GROUP_SETINV
unsafe def OPPOSITE_GROUP_SETMUL : thm := BSetwise1.OPPOSITE_GROUP_SETMUL
unsafe def GROUP_SETINV_EQ_EMPTY : thm := BSetwise1.GROUP_SETINV_EQ_EMPTY
unsafe def GROUP_SETMUL_EQ_EMPTY : thm := BSetwise1.GROUP_SETMUL_EQ_EMPTY
unsafe def GROUP_SETMUL_EMPTY : thm := BSetwise1.GROUP_SETMUL_EMPTY
unsafe def GROUP_SETINV_MONO : thm := BSetwise1.GROUP_SETINV_MONO
unsafe def GROUP_SETMUL_MONO : thm := BSetwise1.GROUP_SETMUL_MONO
unsafe def GROUP_SETMUL_INC_GEN : thm := BSetwise1.GROUP_SETMUL_INC_GEN
unsafe def GROUP_SETMUL_INC : thm := BSetwise1.GROUP_SETMUL_INC
unsafe def FINITE_GROUP_SETMUL : thm := BSetwise1.FINITE_GROUP_SETMUL
unsafe def GROUP_SETMUL_SYM_ELEMENTWISE : thm := BSetwise1.GROUP_SETMUL_SYM_ELEMENTWISE
unsafe def GROUP_SETINV_SING : thm := BSetwise1.GROUP_SETINV_SING
unsafe def GROUP_SETMUL_SING : thm := BSetwise1.GROUP_SETMUL_SING
unsafe def GROUP_SETINV : thm := BSetwise1.GROUP_SETINV
unsafe def GROUP_SETMUL : thm := BSetwise1.GROUP_SETMUL
unsafe def GROUP_SETMUL_LID : thm := BSetwise1.GROUP_SETMUL_LID
unsafe def GROUP_SETMUL_RID : thm := BSetwise1.GROUP_SETMUL_RID
unsafe def GROUP_SETMUL_ASSOC : thm := BSetwise1.GROUP_SETMUL_ASSOC
unsafe def GROUP_SETMUL_SYM : thm := BSetwise1.GROUP_SETMUL_SYM
unsafe def GROUP_SETINV_SUBGROUP : thm := BSetwise1.GROUP_SETINV_SUBGROUP
unsafe def GROUP_SETMUL_LSUBSET : thm := BSetwise1.GROUP_SETMUL_LSUBSET
unsafe def GROUP_SETMUL_RSUBSET : thm := BSetwise1.GROUP_SETMUL_RSUBSET
unsafe def GROUP_SETMUL_LSUBSET_EQ : thm := BSetwise1.GROUP_SETMUL_LSUBSET_EQ

-- Setwise2
unsafe def GROUP_SETMUL_RSUBSET_EQ : thm := BSetwise2.GROUP_SETMUL_RSUBSET_EQ
unsafe def IMAGE_GROUP_CONJUGATION : thm := BSetwise2.IMAGE_GROUP_CONJUGATION
unsafe def IMAGE_GROUP_CONJUGATION_EQ : thm := BSetwise2.IMAGE_GROUP_CONJUGATION_EQ
unsafe def GROUP_SETMUL_SUBGROUP : thm := BSetwise2.GROUP_SETMUL_SUBGROUP
unsafe def GROUP_SETMUL_LCANCEL : thm := BSetwise2.GROUP_SETMUL_LCANCEL
unsafe def GROUP_SETMUL_RCANCEL : thm := BSetwise2.GROUP_SETMUL_RCANCEL
unsafe def GROUP_SETMUL_LCANCEL_SET : thm := BSetwise2.GROUP_SETMUL_LCANCEL_SET
unsafe def GROUP_SETMUL_RCANCEL_SET : thm := BSetwise2.GROUP_SETMUL_RCANCEL_SET
unsafe def SUBGROUP_SETMUL_EQ : thm := BSetwise2.SUBGROUP_SETMUL_EQ
unsafe def SUBGROUP_SETMUL : thm := BSetwise2.SUBGROUP_SETMUL
unsafe def SUBGROUP_GENERATED_SETMUL : thm := BSetwise2.SUBGROUP_GENERATED_SETMUL
unsafe def CARRIER_SUBGROUP_GENERATED_UNION : thm := BSetwise2.CARRIER_SUBGROUP_GENERATED_UNION

-- GroupActions
unsafe def group_action : thm := BGroupActions.group_action
unsafe def GROUP_ACTION_ALT : thm := BGroupActions.GROUP_ACTION_ALT
unsafe def GROUP_ACTION_MUL : thm := BGroupActions.GROUP_ACTION_MUL
unsafe def GROUP_ACTION_LINV : thm := BGroupActions.GROUP_ACTION_LINV
unsafe def GROUP_ACTION_RINV : thm := BGroupActions.GROUP_ACTION_RINV
unsafe def GROUP_ACTION_BIJECTIVE : thm := BGroupActions.GROUP_ACTION_BIJECTIVE
unsafe def GROUP_ACTION_SURJECTIVE : thm := BGroupActions.GROUP_ACTION_SURJECTIVE
unsafe def GROUP_ACTION_INJECTIVE : thm := BGroupActions.GROUP_ACTION_INJECTIVE
unsafe def GROUP_ACTION_ON_SUBSET : thm := BGroupActions.GROUP_ACTION_ON_SUBSET
unsafe def GROUP_ACTION_FROM_SUBGROUP : thm := BGroupActions.GROUP_ACTION_FROM_SUBGROUP
unsafe def GROUP_ACTIONS_EQ_ON_GENERATORS : thm := BGroupActions.GROUP_ACTIONS_EQ_ON_GENERATORS
unsafe def GROUP_ACTION_IMAGE : thm := BGroupActions.GROUP_ACTION_IMAGE
unsafe def GROUP_ACTION_IMAGE_SIZED : thm := BGroupActions.GROUP_ACTION_IMAGE_SIZED
unsafe def group_stabilizer : thm := BGroupActions.group_stabilizer
unsafe def GROUP_STABILIZER_SUBSET_CARRIER : thm := BGroupActions.GROUP_STABILIZER_SUBSET_CARRIER
unsafe def FINITE_GROUP_STABILIZER : thm := BGroupActions.FINITE_GROUP_STABILIZER
unsafe def SUBGROUP_OF_GROUP_STABILIZER : thm := BGroupActions.SUBGROUP_OF_GROUP_STABILIZER
unsafe def GROUP_STABILIZER_NONEMPTY : thm := BGroupActions.GROUP_STABILIZER_NONEMPTY
unsafe def GROUP_STABILIZER_SUBGROUP_GENERATED : thm := BGroupActions.GROUP_STABILIZER_SUBGROUP_GENERATED
unsafe def GROUP_STABILIZER_ON_SUBGROUP : thm := BGroupActions.GROUP_STABILIZER_ON_SUBGROUP
unsafe def GROUP_ACTION_KERNEL_POINTWISE : thm := BGroupActions.GROUP_ACTION_KERNEL_POINTWISE
unsafe def GROUP_ACTION_EQ : thm := BGroupActions.GROUP_ACTION_EQ
unsafe def GROUP_ACTION_FIBRES : thm := BGroupActions.GROUP_ACTION_FIBRES

-- GroupOrbits
unsafe def group_orbit : thm := BGroupOrbits.group_orbit
unsafe def GROUP_ORBIT_IN_SET : thm := BGroupOrbits.GROUP_ORBIT_IN_SET
unsafe def IN_GROUP_ORBIT : thm := BGroupOrbits.IN_GROUP_ORBIT
unsafe def GROUP_ORBIT : thm := BGroupOrbits.GROUP_ORBIT
unsafe def GROUP_ORBIT_SUBSET : thm := BGroupOrbits.GROUP_ORBIT_SUBSET
unsafe def GROUP_ORBIT_ON_SUBSET : thm := BGroupOrbits.GROUP_ORBIT_ON_SUBSET
unsafe def FINITE_GROUP_ORBIT : thm := BGroupOrbits.FINITE_GROUP_ORBIT
unsafe def GROUP_ORBIT_REFL_EQ : thm := BGroupOrbits.GROUP_ORBIT_REFL_EQ
unsafe def GROUP_ORBIT_REFL : thm := BGroupOrbits.GROUP_ORBIT_REFL
unsafe def IN_GROUP_ORBIT_SELF : thm := BGroupOrbits.IN_GROUP_ORBIT_SELF
unsafe def GROUP_ORBIT_EMPTY : thm := BGroupOrbits.GROUP_ORBIT_EMPTY
unsafe def GROUP_ORBIT_EQ_EMPTY : thm := BGroupOrbits.GROUP_ORBIT_EQ_EMPTY
unsafe def GROUP_ORBIT_SYM_EQ : thm := BGroupOrbits.GROUP_ORBIT_SYM_EQ
unsafe def GROUP_ORBIT_SYM : thm := BGroupOrbits.GROUP_ORBIT_SYM
unsafe def GROUP_ORBIT_TRANS : thm := BGroupOrbits.GROUP_ORBIT_TRANS
unsafe def GROUP_ORBIT_EQ : thm := BGroupOrbits.GROUP_ORBIT_EQ
unsafe def CLOSED_GROUP_ORBIT : thm := BGroupOrbits.CLOSED_GROUP_ORBIT
unsafe def GROUP_ORBIT_EQ_SING : thm := BGroupOrbits.GROUP_ORBIT_EQ_SING
unsafe def GROUP_ORBIT_EQ_SING_SELF : thm := BGroupOrbits.GROUP_ORBIT_EQ_SING_SELF
unsafe def GROUP_ORBIT_HAS_SIZE_1 : thm := BGroupOrbits.GROUP_ORBIT_HAS_SIZE_1
unsafe def GROUP_ACTION_INVARIANT_SUBSET : thm := BGroupOrbits.GROUP_ACTION_INVARIANT_SUBSET
unsafe def GROUP_ACTION_CLOSED : thm := BGroupOrbits.GROUP_ACTION_CLOSED
unsafe def GROUP_ACTION_INVARIANT : thm := BGroupOrbits.GROUP_ACTION_INVARIANT
unsafe def INVARIANT_GROUP_ORBIT : thm := BGroupOrbits.INVARIANT_GROUP_ORBIT
unsafe def SUBSET_GROUP_ORBIT_CLOSED : thm := BGroupOrbits.SUBSET_GROUP_ORBIT_CLOSED
unsafe def SUBSET_GROUP_ORBIT_INVARIANT : thm := BGroupOrbits.SUBSET_GROUP_ORBIT_INVARIANT
unsafe def GROUP_ORBITS_EQ : thm := BGroupOrbits.GROUP_ORBITS_EQ
unsafe def DISJOINT_GROUP_ORBITS : thm := BGroupOrbits.DISJOINT_GROUP_ORBITS
unsafe def PAIRWISE_DISJOINT_GROUP_ORBITS : thm := BGroupOrbits.PAIRWISE_DISJOINT_GROUP_ORBITS
unsafe def UNIONS_GROUP_ORBITS_CLOSED : thm := BGroupOrbits.UNIONS_GROUP_ORBITS_CLOSED
unsafe def UNIONS_GROUP_ORBITS_INVARIANT : thm := BGroupOrbits.UNIONS_GROUP_ORBITS_INVARIANT
unsafe def UNIONS_GROUP_ORBITS : thm := BGroupOrbits.UNIONS_GROUP_ORBITS
unsafe def NSUM_CARD_GROUP_ORBITS : thm := BGroupOrbits.NSUM_CARD_GROUP_ORBITS

-- OrbitStabilizer
unsafe def ORBIT_STABILIZER_MUL_GEN : thm := BOrbitStabilizer.ORBIT_STABILIZER_MUL_GEN
unsafe def ORBIT_STABILIZER_MUL : thm := BOrbitStabilizer.ORBIT_STABILIZER_MUL
unsafe def CARD_GROUP_ORBIT_DIVIDES : thm := BOrbitStabilizer.CARD_GROUP_ORBIT_DIVIDES
unsafe def CARD_GROUP_STABILIZER_DIVIDES : thm := BOrbitStabilizer.CARD_GROUP_STABILIZER_DIVIDES
unsafe def GROUP_STABILIZER_OF_ACTION : thm := BOrbitStabilizer.GROUP_STABILIZER_OF_ACTION
unsafe def GROUP_ACTION_SUBGROUP_TRANSLATION : thm := BOrbitStabilizer.GROUP_ACTION_SUBGROUP_TRANSLATION
unsafe def GROUP_STABILIZER_SUBGROUP_TRANSLATION : thm := BOrbitStabilizer.GROUP_STABILIZER_SUBGROUP_TRANSLATION
unsafe def GROUP_ACTION_GROUP_TRANSLATION : thm := BOrbitStabilizer.GROUP_ACTION_GROUP_TRANSLATION
unsafe def GROUP_STABILIZER_GROUP_TRANSLATION : thm := BOrbitStabilizer.GROUP_STABILIZER_GROUP_TRANSLATION
unsafe def GROUP_ACTION_SUBSET_TRANSLATION : thm := BOrbitStabilizer.GROUP_ACTION_SUBSET_TRANSLATION
unsafe def GROUP_ACTION_CONJUGATION : thm := BOrbitStabilizer.GROUP_ACTION_CONJUGATION
unsafe def CARD_GROUP_SETMUL_GEN : thm := BOrbitStabilizer.CARD_GROUP_SETMUL_GEN
unsafe def CARD_GROUP_SETMUL_MUL : thm := BOrbitStabilizer.CARD_GROUP_SETMUL_MUL
unsafe def CARD_GROUP_SETMUL : thm := BOrbitStabilizer.CARD_GROUP_SETMUL
unsafe def CARD_GROUP_SETMUL_DIVIDES : thm := BOrbitStabilizer.CARD_GROUP_SETMUL_DIVIDES
unsafe def GROUP_ORBIT_COMMON_DIVISOR : thm := BOrbitStabilizer.GROUP_ORBIT_COMMON_DIVISOR
unsafe def GROUP_ORBIT_COMMON_INDEX : thm := BOrbitStabilizer.GROUP_ORBIT_COMMON_INDEX

-- Cosets
unsafe def right_coset : thm := BCosets.right_coset
unsafe def left_coset : thm := BCosets.left_coset
unsafe def LEFT_COSET_AS_IMAGE : thm := BCosets.LEFT_COSET_AS_IMAGE
unsafe def RIGHT_COSET : thm := BCosets.RIGHT_COSET
unsafe def LEFT_COSET : thm := BCosets.LEFT_COSET
unsafe def IN_RIGHT_COSET : thm := BCosets.IN_RIGHT_COSET
unsafe def IN_LEFT_COSET : thm := BCosets.IN_LEFT_COSET
unsafe def IN_RIGHT_COSET_INV : thm := BCosets.IN_RIGHT_COSET_INV
unsafe def IN_LEFT_COSET_INV : thm := BCosets.IN_LEFT_COSET_INV
unsafe def GROUP_SETINV_LEFT_COSET_GEN : thm := BCosets.GROUP_SETINV_LEFT_COSET_GEN
unsafe def GROUP_SETINV_RIGHT_COSET_GEN : thm := BCosets.GROUP_SETINV_RIGHT_COSET_GEN
unsafe def RIGHT_COSET_OPPOSITE_GROUP : thm := BCosets.RIGHT_COSET_OPPOSITE_GROUP
unsafe def LEFT_COSET_OPPOSITE_GROUP : thm := BCosets.LEFT_COSET_OPPOSITE_GROUP
unsafe def GROUP_CONJUGATION_RIGHT_COSET : thm := BCosets.GROUP_CONJUGATION_RIGHT_COSET
unsafe def RIGHT_COSET_GROUP_CONJUGATION : thm := BCosets.RIGHT_COSET_GROUP_CONJUGATION
unsafe def LEFT_COSET_LEFT_COSET : thm := BCosets.LEFT_COSET_LEFT_COSET
unsafe def RIGHT_COSET_RIGHT_COSET : thm := BCosets.RIGHT_COSET_RIGHT_COSET
unsafe def RIGHT_COSET_ID : thm := BCosets.RIGHT_COSET_ID
unsafe def LEFT_COSET_ID : thm := BCosets.LEFT_COSET_ID
unsafe def LEFT_COSET_TRIVIAL : thm := BCosets.LEFT_COSET_TRIVIAL
unsafe def RIGHT_COSET_TRIVIAL : thm := BCosets.RIGHT_COSET_TRIVIAL
unsafe def LEFT_COSET_CARRIER : thm := BCosets.LEFT_COSET_CARRIER
unsafe def RIGHT_COSET_CARRIER : thm := BCosets.RIGHT_COSET_CARRIER
unsafe def RIGHT_COSET_EQ : thm := BCosets.RIGHT_COSET_EQ
unsafe def LEFT_COSET_EQ : thm := BCosets.LEFT_COSET_EQ
unsafe def RIGHT_COSET_EQ_SUBGROUP : thm := BCosets.RIGHT_COSET_EQ_SUBGROUP
unsafe def LEFT_COSET_EQ_SUBGROUP : thm := BCosets.LEFT_COSET_EQ_SUBGROUP
unsafe def RIGHT_COSET_EQ_EMPTY : thm := BCosets.RIGHT_COSET_EQ_EMPTY
unsafe def LEFT_COSET_EQ_EMPTY : thm := BCosets.LEFT_COSET_EQ_EMPTY
unsafe def RIGHT_COSET_NONEMPTY : thm := BCosets.RIGHT_COSET_NONEMPTY
unsafe def LEFT_COSET_NONEMPTY : thm := BCosets.LEFT_COSET_NONEMPTY
unsafe def IN_RIGHT_COSET_SELF : thm := BCosets.IN_RIGHT_COSET_SELF

-- Cosets1
unsafe def IN_LEFT_COSET_SELF : thm := BCosets1.IN_LEFT_COSET_SELF
unsafe def UNIONS_RIGHT_COSETS : thm := BCosets1.UNIONS_RIGHT_COSETS
unsafe def UNIONS_LEFT_COSETS : thm := BCosets1.UNIONS_LEFT_COSETS
unsafe def RIGHT_COSETS_EQ : thm := BCosets1.RIGHT_COSETS_EQ
unsafe def LEFT_COSETS_EQ : thm := BCosets1.LEFT_COSETS_EQ
unsafe def DISJOINT_RIGHT_COSETS : thm := BCosets1.DISJOINT_RIGHT_COSETS
unsafe def DISJOINT_LEFT_COSETS : thm := BCosets1.DISJOINT_LEFT_COSETS
unsafe def PAIRWISE_DISJOINT_RIGHT_COSETS : thm := BCosets1.PAIRWISE_DISJOINT_RIGHT_COSETS
unsafe def PAIRWISE_DISJOINT_LEFT_COSETS : thm := BCosets1.PAIRWISE_DISJOINT_LEFT_COSETS
unsafe def IMAGE_RIGHT_COSET_SWITCH : thm := BCosets1.IMAGE_RIGHT_COSET_SWITCH
unsafe def IMAGE_LEFT_COSET_SWITCH : thm := BCosets1.IMAGE_LEFT_COSET_SWITCH
unsafe def CARD_EQ_LEFT_RIGHT_COSETS : thm := BCosets1.CARD_EQ_LEFT_RIGHT_COSETS
unsafe def HAS_SIZE_LEFT_RIGHT_COSETS : thm := BCosets1.HAS_SIZE_LEFT_RIGHT_COSETS
unsafe def CARD_EQ_RIGHT_COSETS : thm := BCosets1.CARD_EQ_RIGHT_COSETS
unsafe def GROUP_ID_IN_LEFT_COSET_GEN : thm := BCosets1.GROUP_ID_IN_LEFT_COSET_GEN
unsafe def GROUP_ID_IN_LEFT_COSET : thm := BCosets1.GROUP_ID_IN_LEFT_COSET
unsafe def SUBGROUP_OF_LEFT_COSET : thm := BCosets1.SUBGROUP_OF_LEFT_COSET
unsafe def GROUP_ID_IN_RIGHT_COSET_GEN : thm := BCosets1.GROUP_ID_IN_RIGHT_COSET_GEN
unsafe def GROUP_ID_IN_RIGHT_COSET : thm := BCosets1.GROUP_ID_IN_RIGHT_COSET
unsafe def SUBGROUP_OF_RIGHT_COSET : thm := BCosets1.SUBGROUP_OF_RIGHT_COSET
unsafe def CARD_EQ_LEFT_COSETS : thm := BCosets1.CARD_EQ_LEFT_COSETS
unsafe def CARD_EQ_RIGHT_COSET_SUBGROUP : thm := BCosets1.CARD_EQ_RIGHT_COSET_SUBGROUP
unsafe def CARD_EQ_LEFT_COSET_SUBGROUP : thm := BCosets1.CARD_EQ_LEFT_COSET_SUBGROUP

-- Cosets2
unsafe def GROUP_ORBIT_SUBGROUP_TRANSLATION : thm := BCosets2.GROUP_ORBIT_SUBGROUP_TRANSLATION
unsafe def GROUP_ORBIT_GROUP_TRANSLATION : thm := BCosets2.GROUP_ORBIT_GROUP_TRANSLATION
unsafe def ORBIT_STABILIZER_GEN : thm := BCosets2.ORBIT_STABILIZER_GEN
unsafe def ORBIT_STABILIZER : thm := BCosets2.ORBIT_STABILIZER
unsafe def GROUP_ACTION_LEFT_COSET_MULTIPLICATION : thm := BCosets2.GROUP_ACTION_LEFT_COSET_MULTIPLICATION
unsafe def GROUP_ORBIT_LEFT_COSET_MULTIPLICATION : thm := BCosets2.GROUP_ORBIT_LEFT_COSET_MULTIPLICATION
unsafe def GROUP_STABILIZER_LEFT_COSET_MULTIPLICATION : thm := BCosets2.GROUP_STABILIZER_LEFT_COSET_MULTIPLICATION
unsafe def GROUP_ORBIT_LEFT_COSET_MULTIPLICATION_ID : thm := BCosets2.GROUP_ORBIT_LEFT_COSET_MULTIPLICATION_ID
unsafe def GROUP_STABILIZER_LEFT_COSET_MULTIPLICATION_ID : thm := BCosets2.GROUP_STABILIZER_LEFT_COSET_MULTIPLICATION_ID
unsafe def LAGRANGE_THEOREM_LEFT_GEN : thm := BCosets2.LAGRANGE_THEOREM_LEFT_GEN
unsafe def LAGRANGE_THEOREM_RIGHT_GEN : thm := BCosets2.LAGRANGE_THEOREM_RIGHT_GEN
unsafe def LAGRANGE_THEOREM_LEFT : thm := BCosets2.LAGRANGE_THEOREM_LEFT
unsafe def LAGRANGE_THEOREM_RIGHT : thm := BCosets2.LAGRANGE_THEOREM_RIGHT
unsafe def LAGRANGE_THEOREM : thm := BCosets2.LAGRANGE_THEOREM
unsafe def CARD_LEFT_COSETS_DIVIDES : thm := BCosets2.CARD_LEFT_COSETS_DIVIDES
unsafe def CARD_RIGHT_COSETS_DIVIDES : thm := BCosets2.CARD_RIGHT_COSETS_DIVIDES
unsafe def LAGRANGE_THEOREM_LEFT_DIV : thm := BCosets2.LAGRANGE_THEOREM_LEFT_DIV
unsafe def LAGRANGE_THEOREM_RIGHT_DIV : thm := BCosets2.LAGRANGE_THEOREM_RIGHT_DIV
unsafe def GROUP_SETMUL_PROD_GROUP : thm := BCosets2.GROUP_SETMUL_PROD_GROUP
unsafe def RIGHT_COSET_PROD_GROUP : thm := BCosets2.RIGHT_COSET_PROD_GROUP
unsafe def LEFT_COSET_PROD_GROUP : thm := BCosets2.LEFT_COSET_PROD_GROUP
unsafe def GROUP_SETMUL_PRODUCT_GROUP : thm := BCosets2.GROUP_SETMUL_PRODUCT_GROUP

-- CosetProducts
unsafe def RIGHT_COSET_PRODUCT_GROUP : thm := BCosetProducts.RIGHT_COSET_PRODUCT_GROUP
unsafe def LEFT_COSET_PRODUCT_GROUP : thm := BCosetProducts.LEFT_COSET_PRODUCT_GROUP
unsafe def GROUP_SETINV_SUBGROUP_GENERATED : thm := BCosetProducts.GROUP_SETINV_SUBGROUP_GENERATED
unsafe def GROUP_SETMUL_SUBGROUP_GENERATED : thm := BCosetProducts.GROUP_SETMUL_SUBGROUP_GENERATED
unsafe def RIGHT_COSET_SUBGROUP_GENERATED : thm := BCosetProducts.RIGHT_COSET_SUBGROUP_GENERATED
unsafe def LEFT_COSET_SUBGROUP_GENERATED : thm := BCosetProducts.LEFT_COSET_SUBGROUP_GENERATED
unsafe def SCHREIER_TRANSVERSAL_LEMMA : thm := BCosetProducts.SCHREIER_TRANSVERSAL_LEMMA

-- NormalSubgroups
unsafe def normal_subgroup_of : thm := BNormalSubgroups.normal_subgroup_of
unsafe def NORMAL_SUBGROUP_IMP_SUBGROUP : thm := BNormalSubgroups.NORMAL_SUBGROUP_IMP_SUBGROUP
unsafe def NORMAL_SUBGROUP_OF_IMP_SUBSET : thm := BNormalSubgroups.NORMAL_SUBGROUP_OF_IMP_SUBSET
unsafe def NORMAL_SUBGROUP_OF_OPPOSITE_GROUP : thm := BNormalSubgroups.NORMAL_SUBGROUP_OF_OPPOSITE_GROUP
unsafe def ABELIAN_GROUP_NORMAL_SUBGROUP : thm := BNormalSubgroups.ABELIAN_GROUP_NORMAL_SUBGROUP
unsafe def NORMAL_SUBGROUP_CONJUGATE_ALT : thm := BNormalSubgroups.NORMAL_SUBGROUP_CONJUGATE_ALT
unsafe def NORMAL_SUBGROUP_CONJUGATE_INV : thm := BNormalSubgroups.NORMAL_SUBGROUP_CONJUGATE_INV
unsafe def NORMAL_SUBGROUP_CONJUGATION_EQ : thm := BNormalSubgroups.NORMAL_SUBGROUP_CONJUGATION_EQ
unsafe def NORMAL_SUBGROUP_CONJUGATION : thm := BNormalSubgroups.NORMAL_SUBGROUP_CONJUGATION
unsafe def NORMAL_SUBGROUP_CONJUGATION_SUPERSET : thm := BNormalSubgroups.NORMAL_SUBGROUP_CONJUGATION_SUPERSET
unsafe def ABELIAN_GROUP_CONJUGATION : thm := BNormalSubgroups.ABELIAN_GROUP_CONJUGATION
unsafe def NORMAL_SUBGROUP_OF_INTERS : thm := BNormalSubgroups.NORMAL_SUBGROUP_OF_INTERS
unsafe def NORMAL_SUBGROUP_OF_INTER : thm := BNormalSubgroups.NORMAL_SUBGROUP_OF_INTER
unsafe def NORMAL_SUBGROUP_OF_UNIONS : thm := BNormalSubgroups.NORMAL_SUBGROUP_OF_UNIONS
unsafe def NORMAL_SUBGROUP_ACTION_KERNEL : thm := BNormalSubgroups.NORMAL_SUBGROUP_ACTION_KERNEL
unsafe def NORMAL_SUBGROUP_LEFT_EQ_RIGHT_COSETS : thm := BNormalSubgroups.NORMAL_SUBGROUP_LEFT_EQ_RIGHT_COSETS
unsafe def NORMAL_SUBGROUP_LEFT_SUBSET_RIGHT_COSETS : thm := BNormalSubgroups.NORMAL_SUBGROUP_LEFT_SUBSET_RIGHT_COSETS
unsafe def NORMAL_SUBGROUP_RIGHT_SUBSET_LEFT_COSETS : thm := BNormalSubgroups.NORMAL_SUBGROUP_RIGHT_SUBSET_LEFT_COSETS
unsafe def NORMAL_SUBGROUP_MUL_SYM : thm := BNormalSubgroups.NORMAL_SUBGROUP_MUL_SYM
unsafe def TRIVIAL_NORMAL_SUBGROUP_OF : thm := BNormalSubgroups.TRIVIAL_NORMAL_SUBGROUP_OF
unsafe def CARRIER_NORMAL_SUBGROUP_OF : thm := BNormalSubgroups.CARRIER_NORMAL_SUBGROUP_OF
unsafe def GROUP_SETINV_RIGHT_COSET : thm := BNormalSubgroups.GROUP_SETINV_RIGHT_COSET
unsafe def GROUP_SETINV_LEFT_COSET : thm := BNormalSubgroups.GROUP_SETINV_LEFT_COSET

-- NormalSubgroups2
unsafe def GROUP_SETMUL_RIGHT_COSET : thm := BNormalSubgroups2.GROUP_SETMUL_RIGHT_COSET
unsafe def GROUP_SETMUL_LEFT_COSET : thm := BNormalSubgroups2.GROUP_SETMUL_LEFT_COSET
unsafe def CROSS_NORMAL_SUBGROUP_OF_PROD_GROUP : thm := BNormalSubgroups2.CROSS_NORMAL_SUBGROUP_OF_PROD_GROUP
unsafe def NORMAL_SUBGROUP_OF_SUBGROUP_GENERATED_GEN : thm := BNormalSubgroups2.NORMAL_SUBGROUP_OF_SUBGROUP_GENERATED_GEN
unsafe def NORMAL_SUBGROUP_OF_SUBGROUP_GENERATED : thm := BNormalSubgroups2.NORMAL_SUBGROUP_OF_SUBGROUP_GENERATED
unsafe def GROUP_SETMUL_NORMAL_SUBGROUP_LEFT : thm := BNormalSubgroups2.GROUP_SETMUL_NORMAL_SUBGROUP_LEFT
unsafe def GROUP_SETMUL_NORMAL_SUBGROUP_RIGHT : thm := BNormalSubgroups2.GROUP_SETMUL_NORMAL_SUBGROUP_RIGHT
unsafe def GROUP_SETMUL_NORMAL_SUBGROUP : thm := BNormalSubgroups2.GROUP_SETMUL_NORMAL_SUBGROUP
unsafe def CARRIER_SUBGROUP_GENERATED_UNION_LEFT : thm := BNormalSubgroups2.CARRIER_SUBGROUP_GENERATED_UNION_LEFT
unsafe def CARRIER_SUBGROUP_GENERATED_UNION_RIGHT : thm := BNormalSubgroups2.CARRIER_SUBGROUP_GENERATED_UNION_RIGHT

-- Conjugate
unsafe def group_conjugate : thm := BConjugate.group_conjugate
unsafe def GROUP_CONJUGATE_REFL : thm := BConjugate.GROUP_CONJUGATE_REFL
unsafe def GROUP_CONJUGATE_SYM : thm := BConjugate.GROUP_CONJUGATE_SYM
unsafe def GROUP_CONJUGATE_TRANS : thm := BConjugate.GROUP_CONJUGATE_TRANS
unsafe def GROUP_CONJUGATE_SUBGROUPS_GENERATED : thm := BConjugate.GROUP_CONJUGATE_SUBGROUPS_GENERATED
unsafe def GROUP_CONJUGATE_IMP_ISOMORPHIC : thm := BConjugate.GROUP_CONJUGATE_IMP_ISOMORPHIC
unsafe def GROUP_CONJUGATE_IMP_CARD_EQ : thm := BConjugate.GROUP_CONJUGATE_IMP_CARD_EQ
unsafe def GROUP_ORBIT_CONJUGATE_STABILIZERS : thm := BConjugate.GROUP_ORBIT_CONJUGATE_STABILIZERS
unsafe def CARD_EQ_GROUP_ORBIT_STABILIZERS : thm := BConjugate.CARD_EQ_GROUP_ORBIT_STABILIZERS

-- CentralizerNormalizer
unsafe def group_centralizer : thm := BCentralizerNormalizer.group_centralizer
unsafe def group_normalizer : thm := BCentralizerNormalizer.group_normalizer
unsafe def GROUP_CENTRALIZER : thm := BCentralizerNormalizer.GROUP_CENTRALIZER
unsafe def GROUP_NORMALIZER : thm := BCentralizerNormalizer.GROUP_NORMALIZER
unsafe def GROUP_NORMALIZER_CONJUGATION_EQ : thm := BCentralizerNormalizer.GROUP_NORMALIZER_CONJUGATION_EQ
unsafe def GROUP_NORMALIZER_CONJUGATION : thm := BCentralizerNormalizer.GROUP_NORMALIZER_CONJUGATION
unsafe def GROUP_NORMALIZER_FINITE : thm := BCentralizerNormalizer.GROUP_NORMALIZER_FINITE
unsafe def GROUP_CENTRALIZER_RESTRICT : thm := BCentralizerNormalizer.GROUP_CENTRALIZER_RESTRICT
unsafe def GROUP_NORMALIZER_RESTRICT : thm := BCentralizerNormalizer.GROUP_NORMALIZER_RESTRICT
unsafe def GROUP_CENTRALIZER_SUBSET_CARRIER : thm := BCentralizerNormalizer.GROUP_CENTRALIZER_SUBSET_CARRIER
unsafe def GROUP_NORMALIZER_SUBSET_CARRIER : thm := BCentralizerNormalizer.GROUP_NORMALIZER_SUBSET_CARRIER
unsafe def FINITE_GROUP_CENTRALIZER : thm := BCentralizerNormalizer.FINITE_GROUP_CENTRALIZER
unsafe def FINITE_GROUP_NORMALIZER : thm := BCentralizerNormalizer.FINITE_GROUP_NORMALIZER
unsafe def GROUP_CENTRALIZER_SUBSET_NORMALIZER : thm := BCentralizerNormalizer.GROUP_CENTRALIZER_SUBSET_NORMALIZER
unsafe def SUBGROUP_GROUP_CENTRALIZER : thm := BCentralizerNormalizer.SUBGROUP_GROUP_CENTRALIZER
unsafe def SUBGROUP_GROUP_NORMALIZER : thm := BCentralizerNormalizer.SUBGROUP_GROUP_NORMALIZER
unsafe def GROUP_CENTRALIZER_SUBGROUP_GENERATED : thm := BCentralizerNormalizer.GROUP_CENTRALIZER_SUBGROUP_GENERATED
unsafe def GROUP_NORMALIZER_SUBGROUP_GENERATED : thm := BCentralizerNormalizer.GROUP_NORMALIZER_SUBGROUP_GENERATED
unsafe def IN_GROUP_CENTRALIZER_ID : thm := BCentralizerNormalizer.IN_GROUP_CENTRALIZER_ID
unsafe def IN_GROUP_NORMALIZER_ID : thm := BCentralizerNormalizer.IN_GROUP_NORMALIZER_ID
unsafe def GROUP_CENTRALIZER_NONEMPTY : thm := BCentralizerNormalizer.GROUP_CENTRALIZER_NONEMPTY
unsafe def GROUP_NORMALIZER_NONEMPTY : thm := BCentralizerNormalizer.GROUP_NORMALIZER_NONEMPTY
unsafe def GROUP_CENTRALIZER_SUBSET : thm := BCentralizerNormalizer.GROUP_CENTRALIZER_SUBSET
unsafe def GROUP_CENTRALIZER_SUBSET_EQ : thm := BCentralizerNormalizer.GROUP_CENTRALIZER_SUBSET_EQ
unsafe def GROUP_CENTRE_EQ_CARRIER : thm := BCentralizerNormalizer.GROUP_CENTRE_EQ_CARRIER
unsafe def GROUP_CENTRALIZER_CENTRALIZER_SUBSET : thm := BCentralizerNormalizer.GROUP_CENTRALIZER_CENTRALIZER_SUBSET
unsafe def GROUP_NORMALIZER_MAXIMAL_GEN : thm := BCentralizerNormalizer.GROUP_NORMALIZER_MAXIMAL_GEN
unsafe def GROUP_NORMALIZER_MAXIMAL : thm := BCentralizerNormalizer.GROUP_NORMALIZER_MAXIMAL
unsafe def NORMAL_SUBGROUP_NORMALIZER_CONTAINS_CARRIER : thm := BCentralizerNormalizer.NORMAL_SUBGROUP_NORMALIZER_CONTAINS_CARRIER
unsafe def NORMAL_SUBGROUP_NORMALIZER_EQ_CARRIER : thm := BCentralizerNormalizer.NORMAL_SUBGROUP_NORMALIZER_EQ_CARRIER
unsafe def GROUP_NORMALIZER_SUBSET : thm := BCentralizerNormalizer.GROUP_NORMALIZER_SUBSET
unsafe def NORMAL_SUBGROUP_OF_NORMALIZER : thm := BCentralizerNormalizer.NORMAL_SUBGROUP_OF_NORMALIZER
unsafe def GROUP_CENTRALIZER_POINTWISE : thm := BCentralizerNormalizer.GROUP_CENTRALIZER_POINTWISE

-- CentralizerNormalizer2
unsafe def GROUP_CENTRALIZER_ALT : thm := BCentralizerNormalizer2.GROUP_CENTRALIZER_ALT
unsafe def NORMAL_SUBGROUP_CENTRALIZER_NORMALIZER : thm := BCentralizerNormalizer2.NORMAL_SUBGROUP_CENTRALIZER_NORMALIZER
unsafe def NORMAL_SUBGROUP_CENTRALIZER : thm := BCentralizerNormalizer2.NORMAL_SUBGROUP_CENTRALIZER
unsafe def GROUP_NORMALIZER_SING : thm := BCentralizerNormalizer2.GROUP_NORMALIZER_SING
unsafe def GROUP_CENTRALIZER_GALOIS_EQ : thm := BCentralizerNormalizer2.GROUP_CENTRALIZER_GALOIS_EQ
unsafe def GROUP_CENTRALIZER_GALOIS : thm := BCentralizerNormalizer2.GROUP_CENTRALIZER_GALOIS
unsafe def GROUP_CENTRALIZER_MONO : thm := BCentralizerNormalizer2.GROUP_CENTRALIZER_MONO
unsafe def GROUP_ACTION_CONJUGATION_NORMAL_SUBGROUP : thm := BCentralizerNormalizer2.GROUP_ACTION_CONJUGATION_NORMAL_SUBGROUP
unsafe def GROUP_STABILIZER_CONJUGATION : thm := BCentralizerNormalizer2.GROUP_STABILIZER_CONJUGATION
unsafe def GROUP_ORBIT_CONJUGATION_GEN : thm := BCentralizerNormalizer2.GROUP_ORBIT_CONJUGATION_GEN
unsafe def GROUP_ORBIT_CONJUGATION : thm := BCentralizerNormalizer2.GROUP_ORBIT_CONJUGATION
unsafe def GROUP_ACTION_IMAGE_CONJUGATION : thm := BCentralizerNormalizer2.GROUP_ACTION_IMAGE_CONJUGATION
unsafe def GROUP_STABILIZER_IMAGE_CONJUGATION : thm := BCentralizerNormalizer2.GROUP_STABILIZER_IMAGE_CONJUGATION
unsafe def GROUP_ACTION_IMAGE_CONJUGATION_CARRIER : thm := BCentralizerNormalizer2.GROUP_ACTION_IMAGE_CONJUGATION_CARRIER
unsafe def GROUP_ACTION_IMAGE_CONJUGATION_SUBGROUPS : thm := BCentralizerNormalizer2.GROUP_ACTION_IMAGE_CONJUGATION_SUBGROUPS
unsafe def GROUP_ORBIT_IMAGE_CONJUGATION : thm := BCentralizerNormalizer2.GROUP_ORBIT_IMAGE_CONJUGATION
unsafe def GROUP_ORBIT_IMAGE_CONJUGATION_GEN : thm := BCentralizerNormalizer2.GROUP_ORBIT_IMAGE_CONJUGATION_GEN
unsafe def CARD_CONJUGATE_SUBSETS_MUL_GEN : thm := BCentralizerNormalizer2.CARD_CONJUGATE_SUBSETS_MUL_GEN
unsafe def CARD_CONJUGATE_SUBSETS_MUL : thm := BCentralizerNormalizer2.CARD_CONJUGATE_SUBSETS_MUL
unsafe def CARD_CONJUGATE_SUBSETS : thm := BCentralizerNormalizer2.CARD_CONJUGATE_SUBSETS

-- QuotientGroups
unsafe def quotient_group : thm := BQuotientGroups.quotient_group
unsafe def QUOTIENT_GROUP : thm := BQuotientGroups.QUOTIENT_GROUP
unsafe def ABELIAN_QUOTIENT_GROUP : thm := BQuotientGroups.ABELIAN_QUOTIENT_GROUP
unsafe def FINITE_QUOTIENT_GROUP : thm := BQuotientGroups.FINITE_QUOTIENT_GROUP
unsafe def TRIVIAL_QUOTIENT_GROUP : thm := BQuotientGroups.TRIVIAL_QUOTIENT_GROUP
unsafe def QUOTIENT_GROUP_ID : thm := BQuotientGroups.QUOTIENT_GROUP_ID
unsafe def QUOTIENT_GROUP_INV : thm := BQuotientGroups.QUOTIENT_GROUP_INV
unsafe def QUOTIENT_GROUP_MUL : thm := BQuotientGroups.QUOTIENT_GROUP_MUL
unsafe def QUOTIENT_GROUP_DIV : thm := BQuotientGroups.QUOTIENT_GROUP_DIV
unsafe def QUOTIENT_GROUP_POW : thm := BQuotientGroups.QUOTIENT_GROUP_POW
unsafe def QUOTIENT_GROUP_ZPOW : thm := BQuotientGroups.QUOTIENT_GROUP_ZPOW
unsafe def GROUP_HOMOMORPHISM_RIGHT_COSET : thm := BQuotientGroups.GROUP_HOMOMORPHISM_RIGHT_COSET
unsafe def GROUP_EPIMORPHISM_RIGHT_COSET : thm := BQuotientGroups.GROUP_EPIMORPHISM_RIGHT_COSET
unsafe def CARD_LE_QUOTIENT_GROUP : thm := BQuotientGroups.CARD_LE_QUOTIENT_GROUP
unsafe def CARD_QUOTIENT_GROUP_DIVIDES : thm := BQuotientGroups.CARD_QUOTIENT_GROUP_DIVIDES
unsafe def TRIVIAL_QUOTIENT_GROUP_EQ : thm := BQuotientGroups.TRIVIAL_QUOTIENT_GROUP_EQ
unsafe def TRIVIAL_QUOTIENT_GROUP_SELF : thm := BQuotientGroups.TRIVIAL_QUOTIENT_GROUP_SELF
unsafe def QUOTIENT_GROUP_TRIVIAL : thm := BQuotientGroups.QUOTIENT_GROUP_TRIVIAL
unsafe def GROUP_ISOMORPHISM_PROD_QUOTIENT_GROUP : thm := BQuotientGroups.GROUP_ISOMORPHISM_PROD_QUOTIENT_GROUP
unsafe def ISOMORPHIC_QUOTIENT_PROD_GROUP : thm := BQuotientGroups.ISOMORPHIC_QUOTIENT_PROD_GROUP
unsafe def CARTESIAN_PRODUCT_NORMAL_SUBGROUP_OF_PRODUCT_GROUP : thm := BQuotientGroups.CARTESIAN_PRODUCT_NORMAL_SUBGROUP_OF_PRODUCT_GROUP
unsafe def GROUP_ISOMORPHISM_PRODUCT_QUOTIENT_GROUP : thm := BQuotientGroups.GROUP_ISOMORPHISM_PRODUCT_QUOTIENT_GROUP
unsafe def ISOMORPHIC_QUOTIENT_PRODUCT_GROUP : thm := BQuotientGroups.ISOMORPHIC_QUOTIENT_PRODUCT_GROUP
unsafe def SUBGROUP_OF_QUOTIENT_GROUP : thm := BQuotientGroups.SUBGROUP_OF_QUOTIENT_GROUP
unsafe def SUBGROUP_OF_QUOTIENT_GROUP_ALT : thm := BQuotientGroups.SUBGROUP_OF_QUOTIENT_GROUP_ALT
unsafe def SUBGROUP_OF_QUOTIENT_GROUP_GENERATED_BY : thm := BQuotientGroups.SUBGROUP_OF_QUOTIENT_GROUP_GENERATED_BY
unsafe def QUOTIENT_GROUP_SUBGROUP_GENERATED : thm := BQuotientGroups.QUOTIENT_GROUP_SUBGROUP_GENERATED

-- KernelsImages1
unsafe def group_kernel : thm := BKernelsImages1.group_kernel
unsafe def group_image : thm := BKernelsImages1.group_image
unsafe def GROUP_KERNEL_ID : thm := BKernelsImages1.GROUP_KERNEL_ID
unsafe def GROUP_KERNEL_NONEMPTY : thm := BKernelsImages1.GROUP_KERNEL_NONEMPTY
unsafe def GROUP_KERNEL_SUBSET_CARRIER : thm := BKernelsImages1.GROUP_KERNEL_SUBSET_CARRIER
unsafe def GROUP_MONOMORPHISM : thm := BKernelsImages1.GROUP_MONOMORPHISM
unsafe def GROUP_MONOMORPHISM_ALT : thm := BKernelsImages1.GROUP_MONOMORPHISM_ALT
unsafe def GROUP_MONOMORPHISM_ALT_EQ : thm := BKernelsImages1.GROUP_MONOMORPHISM_ALT_EQ
unsafe def GROUP_EPIMORPHISM : thm := BKernelsImages1.GROUP_EPIMORPHISM
unsafe def GROUP_EPIMORPHISM_ALT : thm := BKernelsImages1.GROUP_EPIMORPHISM_ALT
unsafe def GROUP_ISOMORPHISM_EPIMORPHISM_ALT : thm := BKernelsImages1.GROUP_ISOMORPHISM_EPIMORPHISM_ALT
unsafe def GROUP_ISOMORPHISM_GROUP_KERNEL_GROUP_IMAGE : thm := BKernelsImages1.GROUP_ISOMORPHISM_GROUP_KERNEL_GROUP_IMAGE
unsafe def GROUP_ISOMORPHISM_ALT : thm := BKernelsImages1.GROUP_ISOMORPHISM_ALT
unsafe def SUBGROUP_GROUP_KERNEL : thm := BKernelsImages1.SUBGROUP_GROUP_KERNEL
unsafe def SUBGROUP_GROUP_IMAGE : thm := BKernelsImages1.SUBGROUP_GROUP_IMAGE
unsafe def GROUP_KERNEL_TO_SUBGROUP_GENERATED : thm := BKernelsImages1.GROUP_KERNEL_TO_SUBGROUP_GENERATED
unsafe def GROUP_IMAGE_TO_SUBGROUP_GENERATED : thm := BKernelsImages1.GROUP_IMAGE_TO_SUBGROUP_GENERATED
unsafe def GROUP_KERNEL_FROM_SUBGROUP_GENERATED : thm := BKernelsImages1.GROUP_KERNEL_FROM_SUBGROUP_GENERATED
unsafe def GROUP_IMAGE_FROM_SUBGROUP_GENERATED : thm := BKernelsImages1.GROUP_IMAGE_FROM_SUBGROUP_GENERATED
unsafe def GROUP_ISOMORPHISM_ONTO_IMAGE : thm := BKernelsImages1.GROUP_ISOMORPHISM_ONTO_IMAGE
unsafe def NORMAL_SUBGROUP_GROUP_KERNEL : thm := BKernelsImages1.NORMAL_SUBGROUP_GROUP_KERNEL
unsafe def GROUP_KERNEL_RIGHT_COSET : thm := BKernelsImages1.GROUP_KERNEL_RIGHT_COSET
unsafe def CARD_EQ_GROUP_IMAGE_KERNEL : thm := BKernelsImages1.CARD_EQ_GROUP_IMAGE_KERNEL
unsafe def CARD_DIVIDES_GROUP_MONOMORPHIC_IMAGE : thm := BKernelsImages1.CARD_DIVIDES_GROUP_MONOMORPHIC_IMAGE
unsafe def CARD_DIVIDES_GROUP_EPIMORPHIC_IMAGE : thm := BKernelsImages1.CARD_DIVIDES_GROUP_EPIMORPHIC_IMAGE

-- KernelsImages2
unsafe def QUOTIENT_GROUP_UNIVERSAL_EXPLICIT : thm := BKernelsImages2.QUOTIENT_GROUP_UNIVERSAL_EXPLICIT
unsafe def QUOTIENT_GROUP_UNIVERSAL : thm := BKernelsImages2.QUOTIENT_GROUP_UNIVERSAL
unsafe def QUOTIENT_GROUP_UNIVERSAL_EPIMORPHISM : thm := BKernelsImages2.QUOTIENT_GROUP_UNIVERSAL_EPIMORPHISM
unsafe def GROUP_KERNEL_FROM_TRIVIAL_GROUP : thm := BKernelsImages2.GROUP_KERNEL_FROM_TRIVIAL_GROUP
unsafe def GROUP_IMAGE_FROM_TRIVIAL_GROUP : thm := BKernelsImages2.GROUP_IMAGE_FROM_TRIVIAL_GROUP
unsafe def GROUP_KERNEL_TO_TRIVIAL_GROUP : thm := BKernelsImages2.GROUP_KERNEL_TO_TRIVIAL_GROUP
unsafe def GROUP_IMAGE_TO_TRIVIAL_GROUP : thm := BKernelsImages2.GROUP_IMAGE_TO_TRIVIAL_GROUP
unsafe def FIRST_GROUP_ISOMORPHISM_THEOREM : thm := BKernelsImages2.FIRST_GROUP_ISOMORPHISM_THEOREM
unsafe def FIRST_GROUP_EPIMORPHISM_THEOREM : thm := BKernelsImages2.FIRST_GROUP_EPIMORPHISM_THEOREM
unsafe def GROUP_HOMOMORPHISM_PREIMAGE_IMAGE_RIGHT : thm := BKernelsImages2.GROUP_HOMOMORPHISM_PREIMAGE_IMAGE_RIGHT
unsafe def GROUP_HOMOMORPHISM_PREIMAGE_IMAGE_LEFT : thm := BKernelsImages2.GROUP_HOMOMORPHISM_PREIMAGE_IMAGE_LEFT
unsafe def GROUP_HOMOMORPHISM_IMAGE_PREIMAGE : thm := BKernelsImages2.GROUP_HOMOMORPHISM_IMAGE_PREIMAGE
unsafe def GROUP_HOMOMORPHISM_PREIMAGE_IMAGE : thm := BKernelsImages2.GROUP_HOMOMORPHISM_PREIMAGE_IMAGE
unsafe def GROUP_HOMOMORPHISM_IMAGE_PREIMAGE_EQ : thm := BKernelsImages2.GROUP_HOMOMORPHISM_IMAGE_PREIMAGE_EQ
unsafe def GROUP_EPIMORPHISM_SUBGROUP_CORRESPONDENCE : thm := BKernelsImages2.GROUP_EPIMORPHISM_SUBGROUP_CORRESPONDENCE

-- SubgroupCorrespondence
unsafe def GROUP_EPIMORPHISM_SUBGROUP_CORRESPONDENCE_ALT : thm := BSubgroupCorrespondence.GROUP_EPIMORPHISM_SUBGROUP_CORRESPONDENCE_ALT
unsafe def NORMAL_SUBGROUP_OF_HOMOMORPHIC_PREIMAGE : thm := BSubgroupCorrespondence.NORMAL_SUBGROUP_OF_HOMOMORPHIC_PREIMAGE
unsafe def NORMAL_SUBGROUP_OF_EPIMORPHIC_IMAGE : thm := BSubgroupCorrespondence.NORMAL_SUBGROUP_OF_EPIMORPHIC_IMAGE
unsafe def NORMAL_SUBGROUP_OF_EPIMORPHIC_PREIMAGE_EQ : thm := BSubgroupCorrespondence.NORMAL_SUBGROUP_OF_EPIMORPHIC_PREIMAGE_EQ
unsafe def GROUP_EPIMORPHISM_NORMAL_SUBGROUP_CORRESPONDENCE : thm := BSubgroupCorrespondence.GROUP_EPIMORPHISM_NORMAL_SUBGROUP_CORRESPONDENCE
unsafe def GROUP_EPIMORPHISM_NORMAL_SUBGROUP_CORRESPONDENCE_ALT : thm := BSubgroupCorrespondence.GROUP_EPIMORPHISM_NORMAL_SUBGROUP_CORRESPONDENCE_ALT
unsafe def SUBGROUP_OF_ISOMORPHIC_IMAGE_EQ : thm := BSubgroupCorrespondence.SUBGROUP_OF_ISOMORPHIC_IMAGE_EQ
unsafe def NORMAL_SUBGROUP_OF_ISOMORPHIC_IMAGE_EQ : thm := BSubgroupCorrespondence.NORMAL_SUBGROUP_OF_ISOMORPHIC_IMAGE_EQ
unsafe def GROUP_CONJUGATE_SUBGROUP_OF : thm := BSubgroupCorrespondence.GROUP_CONJUGATE_SUBGROUP_OF
unsafe def GROUP_CONJUGATE_NORMAL_SUBGROUP_OF : thm := BSubgroupCorrespondence.GROUP_CONJUGATE_NORMAL_SUBGROUP_OF
unsafe def NORMAL_SUBGROUP_CONJUGATE : thm := BSubgroupCorrespondence.NORMAL_SUBGROUP_CONJUGATE
unsafe def NORMAL_SUBGROUP_CONJUGATE_EQ : thm := BSubgroupCorrespondence.NORMAL_SUBGROUP_CONJUGATE_EQ
unsafe def QUOTIENT_SUBGROUP_CORRESPONDENCE : thm := BSubgroupCorrespondence.QUOTIENT_SUBGROUP_CORRESPONDENCE
unsafe def QUOTIENT_NORMAL_SUBGROUP_CORRESPONDENCE : thm := BSubgroupCorrespondence.QUOTIENT_NORMAL_SUBGROUP_CORRESPONDENCE
unsafe def FIRST_GROUP_ISOMORPHISM_THEOREM_GEN : thm := BSubgroupCorrespondence.FIRST_GROUP_ISOMORPHISM_THEOREM_GEN
unsafe def FIRST_GROUP_ISOMORPHISM_THEOREM_GEN_ALT : thm := BSubgroupCorrespondence.FIRST_GROUP_ISOMORPHISM_THEOREM_GEN_ALT
unsafe def SIMPLE_GROUP_EPIMORPHIC_IMAGE_EQ : thm := BSubgroupCorrespondence.SIMPLE_GROUP_EPIMORPHIC_IMAGE_EQ
unsafe def NO_PROPER_SUBGROUP_EPIMORPHIC_IMAGE_EQ : thm := BSubgroupCorrespondence.NO_PROPER_SUBGROUP_EPIMORPHIC_IMAGE_EQ
unsafe def MAXIMAL_SUBGROUP : thm := BSubgroupCorrespondence.MAXIMAL_SUBGROUP
unsafe def MAXIMAL_NORMAL_SUBGROUP : thm := BSubgroupCorrespondence.MAXIMAL_NORMAL_SUBGROUP

-- TrivialHomomorphisms
unsafe def trivial_homomorphism : thm := BTrivialHomomorphisms.trivial_homomorphism
unsafe def GROUP_KERNEL_IMAGE_TRIVIAL : thm := BTrivialHomomorphisms.GROUP_KERNEL_IMAGE_TRIVIAL
unsafe def TRIVIAL_HOMOMORPHISM_GROUP_KERNEL : thm := BTrivialHomomorphisms.TRIVIAL_HOMOMORPHISM_GROUP_KERNEL
unsafe def TRIVIAL_HOMOMORPHISM_GROUP_IMAGE : thm := BTrivialHomomorphisms.TRIVIAL_HOMOMORPHISM_GROUP_IMAGE
unsafe def TRIVIAL_HOMOMORPHISM_TRIVIAL : thm := BTrivialHomomorphisms.TRIVIAL_HOMOMORPHISM_TRIVIAL
unsafe def GROUP_MONOMORPHISM_TRIVIAL : thm := BTrivialHomomorphisms.GROUP_MONOMORPHISM_TRIVIAL
unsafe def GROUP_EPIMORPHISM_TRIVIAL : thm := BTrivialHomomorphisms.GROUP_EPIMORPHISM_TRIVIAL
unsafe def GROUP_ISOMORPHISM_TRIVIAL : thm := BTrivialHomomorphisms.GROUP_ISOMORPHISM_TRIVIAL

-- GroupElementOrder
unsafe def group_element_order : thm := BGroupElementOrder.group_element_order
unsafe def GROUP_POW_EQ_ID : thm := BGroupElementOrder.GROUP_POW_EQ_ID
unsafe def GROUP_POW_EQ_ID_DIVISOR : thm := BGroupElementOrder.GROUP_POW_EQ_ID_DIVISOR
unsafe def GROUP_POW_ELEMENT_ORDER : thm := BGroupElementOrder.GROUP_POW_ELEMENT_ORDER
unsafe def GROUP_ZPOW_EQ_ID : thm := BGroupElementOrder.GROUP_ZPOW_EQ_ID
unsafe def GROUP_ZPOW_EQ_ID_DIVISOR : thm := BGroupElementOrder.GROUP_ZPOW_EQ_ID_DIVISOR
unsafe def GROUP_ZPOW_EQ_ALT : thm := BGroupElementOrder.GROUP_ZPOW_EQ_ALT
unsafe def GROUP_ZPOW_EQ : thm := BGroupElementOrder.GROUP_ZPOW_EQ
unsafe def GROUP_POW_EQ : thm := BGroupElementOrder.GROUP_POW_EQ
unsafe def GROUP_ZPOW_REM_ELEMENT_ORDER : thm := BGroupElementOrder.GROUP_ZPOW_REM_ELEMENT_ORDER
unsafe def GROUP_POW_MOD_ELEMENT_ORDER : thm := BGroupElementOrder.GROUP_POW_MOD_ELEMENT_ORDER
unsafe def GROUP_ELEMENT_ORDER_EQ_0 : thm := BGroupElementOrder.GROUP_ELEMENT_ORDER_EQ_0
unsafe def GROUP_ELEMENT_ORDER_UNIQUE : thm := BGroupElementOrder.GROUP_ELEMENT_ORDER_UNIQUE
unsafe def GROUP_ELEMENT_ORDER_EQ_1 : thm := BGroupElementOrder.GROUP_ELEMENT_ORDER_EQ_1
unsafe def GROUP_ELEMENT_ORDER_UNIQUE_PRIME : thm := BGroupElementOrder.GROUP_ELEMENT_ORDER_UNIQUE_PRIME
unsafe def GROUP_ELEMENT_ORDER_ID : thm := BGroupElementOrder.GROUP_ELEMENT_ORDER_ID
unsafe def GROUP_ELEMENT_ORDER_INV : thm := BGroupElementOrder.GROUP_ELEMENT_ORDER_INV
unsafe def GROUP_POW_GCD_EQ_ID : thm := BGroupElementOrder.GROUP_POW_GCD_EQ_ID
unsafe def GROUP_POW_COPRIME_EQ_ID : thm := BGroupElementOrder.GROUP_POW_COPRIME_EQ_ID
unsafe def FINITE_GROUP_ELEMENT_ORDER_NONZERO : thm := BGroupElementOrder.FINITE_GROUP_ELEMENT_ORDER_NONZERO
unsafe def GROUP_ELEMENT_ORDER_POW : thm := BGroupElementOrder.GROUP_ELEMENT_ORDER_POW

-- GroupElementOrder2
unsafe def GROUP_ELEMENT_ORDER_POW_GEN : thm := BGroupElementOrder2.GROUP_ELEMENT_ORDER_POW_GEN
unsafe def GROUP_ELEMENT_ORDER_MUL_DIVIDES_GEN : thm := BGroupElementOrder2.GROUP_ELEMENT_ORDER_MUL_DIVIDES_GEN
unsafe def ABELIAN_GROUP_ELEMENT_ORDER_MUL_DIVIDES_GEN : thm := BGroupElementOrder2.ABELIAN_GROUP_ELEMENT_ORDER_MUL_DIVIDES_GEN
unsafe def GROUP_ELEMENT_ORDER_MUL_DIVIDES_LCM : thm := BGroupElementOrder2.GROUP_ELEMENT_ORDER_MUL_DIVIDES_LCM
unsafe def ABELIAN_GROUP_ELEMENT_ORDER_MUL_DIVIDES_LCM : thm := BGroupElementOrder2.ABELIAN_GROUP_ELEMENT_ORDER_MUL_DIVIDES_LCM
unsafe def GROUP_ELEMENT_ORDER_HOMOMORPHIC_IMAGE : thm := BGroupElementOrder2.GROUP_ELEMENT_ORDER_HOMOMORPHIC_IMAGE
unsafe def GROUP_ELEMENT_ORDER_MONOMORPHIC_IMAGE : thm := BGroupElementOrder2.GROUP_ELEMENT_ORDER_MONOMORPHIC_IMAGE
unsafe def ISOMORPHIC_GROUP_TORSION : thm := BGroupElementOrder2.ISOMORPHIC_GROUP_TORSION
unsafe def GROUP_ELEMENT_ORDER_CONJUGATION : thm := BGroupElementOrder2.GROUP_ELEMENT_ORDER_CONJUGATION
unsafe def GROUP_ELEMENT_ORDER_MUL_DIVIDES : thm := BGroupElementOrder2.GROUP_ELEMENT_ORDER_MUL_DIVIDES
unsafe def ABELIAN_GROUP_ELEMENT_ORDER_MUL_DIVIDES : thm := BGroupElementOrder2.ABELIAN_GROUP_ELEMENT_ORDER_MUL_DIVIDES
unsafe def GROUP_POW_MUL_EQ_ID_SYM : thm := BGroupElementOrder2.GROUP_POW_MUL_EQ_ID_SYM
unsafe def GROUP_ELEMENT_ORDER_MUL_SYM : thm := BGroupElementOrder2.GROUP_ELEMENT_ORDER_MUL_SYM
unsafe def GROUP_ELEMENT_ORDER_UNIQUE_ALT : thm := BGroupElementOrder2.GROUP_ELEMENT_ORDER_UNIQUE_ALT
unsafe def GROUP_ELEMENT_ORDER_EQ_2 : thm := BGroupElementOrder2.GROUP_ELEMENT_ORDER_EQ_2
unsafe def GROUP_ELEMENT_ORDER_EQ_2_ALT : thm := BGroupElementOrder2.GROUP_ELEMENT_ORDER_EQ_2_ALT
unsafe def GROUP_ELEMENT_ORDER_POW_DIVIDES : thm := BGroupElementOrder2.GROUP_ELEMENT_ORDER_POW_DIVIDES
unsafe def GROUP_ELEMENT_ORDER_MUL_EQ : thm := BGroupElementOrder2.GROUP_ELEMENT_ORDER_MUL_EQ
unsafe def GROUP_ELEMENT_ORDER_EQ_MUL_GEN : thm := BGroupElementOrder2.GROUP_ELEMENT_ORDER_EQ_MUL_GEN
unsafe def GROUP_ELEMENT_ORDER_EQ_MUL : thm := BGroupElementOrder2.GROUP_ELEMENT_ORDER_EQ_MUL
unsafe def ABELIAN_GROUP_ELEMENT_ORDER_MUL_EQ : thm := BGroupElementOrder2.ABELIAN_GROUP_ELEMENT_ORDER_MUL_EQ

-- OrderDecomp
unsafe def GROUP_ELEMENT_ORDER_LCM_EXISTS : thm := BOrderDecomp.GROUP_ELEMENT_ORDER_LCM_EXISTS
unsafe def ABELIAN_GROUP_ELEMENT_ORDER_LCM_EXISTS : thm := BOrderDecomp.ABELIAN_GROUP_ELEMENT_ORDER_LCM_EXISTS
unsafe def ABELIAN_GROUP_ORDER_DIVIDES_MAXIMAL : thm := BOrderDecomp.ABELIAN_GROUP_ORDER_DIVIDES_MAXIMAL
unsafe def ABELIAN_GROUP_ELEMENT_ORDER_DIVIDES_MAXIMAL_ALT : thm := BOrderDecomp.ABELIAN_GROUP_ELEMENT_ORDER_DIVIDES_MAXIMAL_ALT
unsafe def GROUP_ELEMENT_ORDER_SUBGROUP_GENERATED : thm := BOrderDecomp.GROUP_ELEMENT_ORDER_SUBGROUP_GENERATED
unsafe def GROUP_ELEMENT_ORDER_PROD_GROUP : thm := BOrderDecomp.GROUP_ELEMENT_ORDER_PROD_GROUP
unsafe def GROUP_ELEMENT_ORDER_PROD_GROUP_ALT : thm := BOrderDecomp.GROUP_ELEMENT_ORDER_PROD_GROUP_ALT
unsafe def GROUP_ELEMENT_ORDER_SUM_GROUP : thm := BOrderDecomp.GROUP_ELEMENT_ORDER_SUM_GROUP
unsafe def GROUP_ELEMENT_ORDER_SUM_GROUP_EQ_0 : thm := BOrderDecomp.GROUP_ELEMENT_ORDER_SUM_GROUP_EQ_0
unsafe def GROUP_ELEMENT_ORDER_COPRIME_DECOMP_EXPLICIT : thm := BOrderDecomp.GROUP_ELEMENT_ORDER_COPRIME_DECOMP_EXPLICIT
unsafe def GROUP_ELEMENT_ORDER_COPRIME_DECOMP_UNIQUE : thm := BOrderDecomp.GROUP_ELEMENT_ORDER_COPRIME_DECOMP_UNIQUE
unsafe def GROUP_ELEMENT_ORDER_COPRIME_DECOMP : thm := BOrderDecomp.GROUP_ELEMENT_ORDER_COPRIME_DECOMP
unsafe def GROUP_ELEMENT_ORDER_COPRIME_DECOMP_DIVIDES : thm := BOrderDecomp.GROUP_ELEMENT_ORDER_COPRIME_DECOMP_DIVIDES
unsafe def GROUP_POW_EQ_ID_DECOMP : thm := BOrderDecomp.GROUP_POW_EQ_ID_DECOMP
unsafe def GROUP_ELEMENT_ORDER_PRIMEPOW_DECOMP : thm := BOrderDecomp.GROUP_ELEMENT_ORDER_PRIMEPOW_DECOMP

-- TorsionSubgroups
unsafe def SUBGROUP_OF_TORSION_GENERAL : thm := BTorsionSubgroups.SUBGROUP_OF_TORSION_GENERAL
unsafe def SUBGROUP_OF_TORSION_GEN : thm := BTorsionSubgroups.SUBGROUP_OF_TORSION_GEN
unsafe def SUBGROUP_OF_TORSION : thm := BTorsionSubgroups.SUBGROUP_OF_TORSION
unsafe def SUBGROUP_OF_PRIMES_TORSION : thm := BTorsionSubgroups.SUBGROUP_OF_PRIMES_TORSION
unsafe def SUBGROUP_OF_PRIME_TORSION : thm := BTorsionSubgroups.SUBGROUP_OF_PRIME_TORSION
unsafe def SUBGROUP_OF_LOWER_ORDER : thm := BTorsionSubgroups.SUBGROUP_OF_LOWER_ORDER
unsafe def SUBGROUP_OF_LOWER_ORDER_ALT : thm := BTorsionSubgroups.SUBGROUP_OF_LOWER_ORDER_ALT
unsafe def SUBGROUP_OF_NONDIVISIBLE_ORDER : thm := BTorsionSubgroups.SUBGROUP_OF_NONDIVISIBLE_ORDER
unsafe def SUBGROUP_OF_COPRIME_ORDER : thm := BTorsionSubgroups.SUBGROUP_OF_COPRIME_ORDER
unsafe def TORSION_FREE_GROUP : thm := BTorsionSubgroups.TORSION_FREE_GROUP
unsafe def TORSION_FREE_GROUP_ALT : thm := BTorsionSubgroups.TORSION_FREE_GROUP_ALT
unsafe def QUOTIENT_GROUP_POW_EQ_ID : thm := BTorsionSubgroups.QUOTIENT_GROUP_POW_EQ_ID
unsafe def TORSION_FREE_QUOTIENT_GROUP : thm := BTorsionSubgroups.TORSION_FREE_QUOTIENT_GROUP
unsafe def IMAGE_GROUP_CONJUGATION_TORSION_GEN : thm := BTorsionSubgroups.IMAGE_GROUP_CONJUGATION_TORSION_GEN
unsafe def NORMAL_SUBGROUP_OF_TORSION_GEN : thm := BTorsionSubgroups.NORMAL_SUBGROUP_OF_TORSION_GEN
unsafe def NORMAL_SUBGROUP_OF_TORSION : thm := BTorsionSubgroups.NORMAL_SUBGROUP_OF_TORSION

-- CyclicGroups1
unsafe def SUBGROUP_OF_POWERS : thm := BCyclicGroups1.SUBGROUP_OF_POWERS
unsafe def CARRIER_SUBGROUP_GENERATED_BY_SING : thm := BCyclicGroups1.CARRIER_SUBGROUP_GENERATED_BY_SING
unsafe def cyclic_group : thm := BCyclicGroups1.cyclic_group
unsafe def CYCLIC_GROUP : thm := BCyclicGroups1.CYCLIC_GROUP
unsafe def CYCLIC_IMP_ABELIAN_GROUP : thm := BCyclicGroups1.CYCLIC_IMP_ABELIAN_GROUP
unsafe def TRIVIAL_IMP_CYCLIC_GROUP : thm := BCyclicGroups1.TRIVIAL_IMP_CYCLIC_GROUP
unsafe def CYCLIC_GROUP_ALT : thm := BCyclicGroups1.CYCLIC_GROUP_ALT
unsafe def CYCLIC_GROUP_GENERATED : thm := BCyclicGroups1.CYCLIC_GROUP_GENERATED
unsafe def CYCLIC_GROUP_EPIMORPHIC_IMAGE : thm := BCyclicGroups1.CYCLIC_GROUP_EPIMORPHIC_IMAGE
unsafe def ISOMORPHIC_GROUP_CYCLICITY : thm := BCyclicGroups1.ISOMORPHIC_GROUP_CYCLICITY
unsafe def SUBGROUP_OF_CYCLIC_GROUP_EXPLICIT : thm := BCyclicGroups1.SUBGROUP_OF_CYCLIC_GROUP_EXPLICIT
unsafe def SUBGROUP_OF_CYCLIC_GROUP : thm := BCyclicGroups1.SUBGROUP_OF_CYCLIC_GROUP
unsafe def CYCLIC_GROUP_QUOTIENT_GROUP : thm := BCyclicGroups1.CYCLIC_GROUP_QUOTIENT_GROUP
unsafe def NO_PROPER_SUBGROUPS_IMP_CYCLIC : thm := BCyclicGroups1.NO_PROPER_SUBGROUPS_IMP_CYCLIC

-- CyclicGroups2
unsafe def FINITE_CYCLIC_SUBGROUP : thm := BCyclicGroups2.FINITE_CYCLIC_SUBGROUP
unsafe def INFINITE_CYCLIC_SUBGROUP : thm := BCyclicGroups2.INFINITE_CYCLIC_SUBGROUP
unsafe def FINITE_CYCLIC_SUBGROUP_ALT : thm := BCyclicGroups2.FINITE_CYCLIC_SUBGROUP_ALT
unsafe def INFINITE_CYCLIC_SUBGROUP_ALT : thm := BCyclicGroups2.INFINITE_CYCLIC_SUBGROUP_ALT
unsafe def FINITE_CYCLIC_SUBGROUP_ORDER : thm := BCyclicGroups2.FINITE_CYCLIC_SUBGROUP_ORDER
unsafe def INFINITE_CYCLIC_SUBGROUP_ORDER : thm := BCyclicGroups2.INFINITE_CYCLIC_SUBGROUP_ORDER
unsafe def FINITE_CYCLIC_SUBGROUP_EXPLICIT : thm := BCyclicGroups2.FINITE_CYCLIC_SUBGROUP_EXPLICIT
unsafe def FINITE_SUBGROUPS_EQ : thm := BCyclicGroups2.FINITE_SUBGROUPS_EQ
unsafe def CARD_CYCLIC_SUBGROUP_ORDER : thm := BCyclicGroups2.CARD_CYCLIC_SUBGROUP_ORDER
unsafe def PRIME_ORDER_IMP_NO_PROPER_SUBGROUPS : thm := BCyclicGroups2.PRIME_ORDER_IMP_NO_PROPER_SUBGROUPS
unsafe def PRIME_ORDER_EQ_NO_PROPER_SUBGROUPS : thm := BCyclicGroups2.PRIME_ORDER_EQ_NO_PROPER_SUBGROUPS
unsafe def NO_PROPER_SUBGROUPS_EQ_CYCLIC_PRIME_ORDER : thm := BCyclicGroups2.NO_PROPER_SUBGROUPS_EQ_CYCLIC_PRIME_ORDER

-- CyclicGroups3
unsafe def ABELIAN_SIMPLE_GROUP : thm := BCyclicGroups3.ABELIAN_SIMPLE_GROUP
unsafe def PRIME_ORDER_IMP_CYCLIC_GROUP : thm := BCyclicGroups3.PRIME_ORDER_IMP_CYCLIC_GROUP
unsafe def GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER : thm := BCyclicGroups3.GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER
unsafe def GROUP_POW_GROUP_ORDER : thm := BCyclicGroups3.GROUP_POW_GROUP_ORDER
unsafe def GROUP_ZPOW_REM_ORDER : thm := BCyclicGroups3.GROUP_ZPOW_REM_ORDER
unsafe def GROUP_POW_MOD_ORDER : thm := BCyclicGroups3.GROUP_POW_MOD_ORDER
unsafe def SUBGROUP_OF_FINITE_CYCLIC_GROUP : thm := BCyclicGroups3.SUBGROUP_OF_FINITE_CYCLIC_GROUP
unsafe def COUNT_FINITE_CYCLIC_GROUP_SUBGROUPS : thm := BCyclicGroups3.COUNT_FINITE_CYCLIC_GROUP_SUBGROUPS
unsafe def COUNT_FINITE_CYCLIC_GROUP_SUBGROUPS_ALL : thm := BCyclicGroups3.COUNT_FINITE_CYCLIC_GROUP_SUBGROUPS_ALL
unsafe def MAXIMAL_SUBGROUP_PRIME_INDEX : thm := BCyclicGroups3.MAXIMAL_SUBGROUP_PRIME_INDEX
unsafe def PRIME_INDEX_MAXIMAL_PROPER_SUBGROUP : thm := BCyclicGroups3.PRIME_INDEX_MAXIMAL_PROPER_SUBGROUP
unsafe def MAXIMAL_PROPER_SUBGROUP_PRIME_INDEX : thm := BCyclicGroups3.MAXIMAL_PROPER_SUBGROUP_PRIME_INDEX
unsafe def GROUP_ZPOW_CANCEL : thm := BCyclicGroups3.GROUP_ZPOW_CANCEL
unsafe def GROUP_POW_CANCEL : thm := BCyclicGroups3.GROUP_POW_CANCEL

-- FinitelyGenerated
unsafe def finitely_generated_group : thm := BFinitelyGenerated.finitely_generated_group
unsafe def FINITELY_GENERATED_GROUP : thm := BFinitelyGenerated.FINITELY_GENERATED_GROUP
unsafe def CYCLIC_IMP_FINITELY_GENERATED_GROUP : thm := BFinitelyGenerated.CYCLIC_IMP_FINITELY_GENERATED_GROUP
unsafe def FINITE_IMP_FINITELY_GENERATED_GROUP : thm := BFinitelyGenerated.FINITE_IMP_FINITELY_GENERATED_GROUP
unsafe def TRIVIAL_IMP_FINITELY_GENERATED_GROUP : thm := BFinitelyGenerated.TRIVIAL_IMP_FINITELY_GENERATED_GROUP
unsafe def FINITELY_GENERATED_GROUP_EPIMORPHIC_IMAGE : thm := BFinitelyGenerated.FINITELY_GENERATED_GROUP_EPIMORPHIC_IMAGE
unsafe def ISOMORPHIC_GROUP_FINITE_GENERATION : thm := BFinitelyGenerated.ISOMORPHIC_GROUP_FINITE_GENERATION
unsafe def FINITELY_GENERATED_GROUP_QUOTIENT_GROUP : thm := BFinitelyGenerated.FINITELY_GENERATED_GROUP_QUOTIENT_GROUP
unsafe def FINITELY_GENERATED_IMP_COUNTABLE_GROUP : thm := BFinitelyGenerated.FINITELY_GENERATED_IMP_COUNTABLE_GROUP
unsafe def FINITELY_GENERATED_PROD_GROUP : thm := BFinitelyGenerated.FINITELY_GENERATED_PROD_GROUP
unsafe def FINITELY_GENERATED_PRODUCT_GROUP : thm := BFinitelyGenerated.FINITELY_GENERATED_PRODUCT_GROUP
unsafe def FINITELY_GENERATED_SUM_GROUP : thm := BFinitelyGenerated.FINITELY_GENERATED_SUM_GROUP
unsafe def FINITE_GROUP_ACTIONS : thm := BFinitelyGenerated.FINITE_GROUP_ACTIONS

-- FinitelyGeneratedSubgroups
unsafe def FINITELY_GENERATED_FIXED_INDEX_SUBGROUPS : thm := BFinitelyGeneratedSubgroups.FINITELY_GENERATED_FIXED_INDEX_SUBGROUPS
unsafe def FINITELY_GENERATED_FINITE_INDEX_SUBGROUP : thm := BFinitelyGeneratedSubgroups.FINITELY_GENERATED_FINITE_INDEX_SUBGROUP
unsafe def FINITELY_GENERATED_ABELIAN_SUBGROUP_EXPLICIT : thm := BFinitelyGeneratedSubgroups.FINITELY_GENERATED_ABELIAN_SUBGROUP_EXPLICIT

-- FinitelyGeneratedMaximal
unsafe def FINITELY_GENERATED_ABELIAN_SUBGROUP : thm := BFinitelyGeneratedMaximal.FINITELY_GENERATED_ABELIAN_SUBGROUP
unsafe def MAXIMAL_SUBGROUP_EXISTS : thm := BFinitelyGeneratedMaximal.MAXIMAL_SUBGROUP_EXISTS
unsafe def MAXIMAL_NORMAL_SUBGROUP_EXISTS : thm := BFinitelyGeneratedMaximal.MAXIMAL_NORMAL_SUBGROUP_EXISTS

-- IntegerGroup
unsafe def integer_group : thm := BIntegerGroup.integer_group
unsafe def INTEGER_GROUP : thm := BIntegerGroup.INTEGER_GROUP
unsafe def ABELIAN_INTEGER_GROUP : thm := BIntegerGroup.ABELIAN_INTEGER_GROUP
unsafe def INFINITE_INTEGER_GROUP : thm := BIntegerGroup.INFINITE_INTEGER_GROUP
unsafe def GROUP_POW_INTEGER_GROUP : thm := BIntegerGroup.GROUP_POW_INTEGER_GROUP
unsafe def GROUP_ZPOW_INTEGER_GROUP : thm := BIntegerGroup.GROUP_ZPOW_INTEGER_GROUP
unsafe def GROUP_ELEMENT_ORDER_INTEGER_GROUP : thm := BIntegerGroup.GROUP_ELEMENT_ORDER_INTEGER_GROUP
unsafe def GROUP_ENDOMORPHISM_INTEGER_GROUP_MUL : thm := BIntegerGroup.GROUP_ENDOMORPHISM_INTEGER_GROUP_MUL
unsafe def GROUP_ENDOMORPHISM_INTEGER_GROUP_EXPLICIT : thm := BIntegerGroup.GROUP_ENDOMORPHISM_INTEGER_GROUP_EXPLICIT
unsafe def GROUP_ENDOMORPHISM_INTEGER_GROUP_EQ : thm := BIntegerGroup.GROUP_ENDOMORPHISM_INTEGER_GROUP_EQ
unsafe def GROUP_ENDOMORPHISM_INTEGER_GROUP_EQ_ALT : thm := BIntegerGroup.GROUP_ENDOMORPHISM_INTEGER_GROUP_EQ_ALT
unsafe def GROUP_HOMOMORPHISM_GROUP_ZPOW : thm := BIntegerGroup.GROUP_HOMOMORPHISM_GROUP_ZPOW
unsafe def GROUP_EPIMORPHISM_GROUP_ZPOW : thm := BIntegerGroup.GROUP_EPIMORPHISM_GROUP_ZPOW
unsafe def GROUP_ISOMORPHISM_GROUP_ZPOW : thm := BIntegerGroup.GROUP_ISOMORPHISM_GROUP_ZPOW
unsafe def ISOMORPHIC_GROUP_INFINITE_CYCLIC_INTEGER : thm := BIntegerGroup.ISOMORPHIC_GROUP_INFINITE_CYCLIC_INTEGER
unsafe def ISOMORPHIC_INFINITE_CYCLIC_GROUPS : thm := BIntegerGroup.ISOMORPHIC_INFINITE_CYCLIC_GROUPS

-- IntegerModGroup
unsafe def integer_mod_group : thm := BIntegerModGroup.integer_mod_group
unsafe def INTEGER_MOD_GROUP : thm := BIntegerModGroup.INTEGER_MOD_GROUP
unsafe def INTEGER_MOD_GROUP_TRIVIAL : thm := BIntegerModGroup.INTEGER_MOD_GROUP_TRIVIAL
unsafe def GROUP_CARRIER_INTEGER_MOD_GROUP : thm := BIntegerModGroup.GROUP_CARRIER_INTEGER_MOD_GROUP
unsafe def GROUP_POW_INTEGER_MOD_GROUP : thm := BIntegerModGroup.GROUP_POW_INTEGER_MOD_GROUP
unsafe def GROUP_ZPOW_INTEGER_MOD_GROUP : thm := BIntegerModGroup.GROUP_ZPOW_INTEGER_MOD_GROUP
unsafe def ABELIAN_INTEGER_MOD_GROUP : thm := BIntegerModGroup.ABELIAN_INTEGER_MOD_GROUP
unsafe def INTEGER_MOD_GROUP_0 : thm := BIntegerModGroup.INTEGER_MOD_GROUP_0
unsafe def INTEGER_MOD_GROUP_1R : thm := BIntegerModGroup.INTEGER_MOD_GROUP_1R
unsafe def INTEGER_MOD_GROUP_1 : thm := BIntegerModGroup.INTEGER_MOD_GROUP_1
unsafe def GROUP_HOMOMORPHISM_PROD_INTEGER_MOD_GROUP : thm := BIntegerModGroup.GROUP_HOMOMORPHISM_PROD_INTEGER_MOD_GROUP
unsafe def TRIVIAL_INTEGER_MOD_GROUP : thm := BIntegerModGroup.TRIVIAL_INTEGER_MOD_GROUP
unsafe def NON_TRIVIAL_INTEGER_GROUP : thm := BIntegerModGroup.NON_TRIVIAL_INTEGER_GROUP
unsafe def GROUP_ELEMENT_ORDER_INTEGER_MOD_GROUP_1 : thm := BIntegerModGroup.GROUP_ELEMENT_ORDER_INTEGER_MOD_GROUP_1
unsafe def GROUP_ELEMENT_ORDER_INTEGER_MOD_GROUP_1R : thm := BIntegerModGroup.GROUP_ELEMENT_ORDER_INTEGER_MOD_GROUP_1R
unsafe def GROUP_ELEMENT_ORDER_INTEGER_MOD_GROUP : thm := BIntegerModGroup.GROUP_ELEMENT_ORDER_INTEGER_MOD_GROUP
unsafe def INTEGER_MOD_SUBGROUP_GENERATED_BY_1R : thm := BIntegerModGroup.INTEGER_MOD_SUBGROUP_GENERATED_BY_1R
unsafe def INTEGER_MOD_SUBGROUP_GENERATED_BY_1 : thm := BIntegerModGroup.INTEGER_MOD_SUBGROUP_GENERATED_BY_1
unsafe def CYCLIC_GROUP_INTEGER_MOD_GROUP : thm := BIntegerModGroup.CYCLIC_GROUP_INTEGER_MOD_GROUP

-- CyclicInteger
unsafe def CYCLIC_INTEGER_GROUP : thm := BCyclicInteger.CYCLIC_INTEGER_GROUP
unsafe def FINITE_INTEGER_MOD_GROUP : thm := BCyclicInteger.FINITE_INTEGER_MOD_GROUP
unsafe def GROUP_EPIMORPHISM_INTEGER_MOD_GROUP_ZPOW : thm := BCyclicInteger.GROUP_EPIMORPHISM_INTEGER_MOD_GROUP_ZPOW
unsafe def GROUP_ISOMORPHISM_GROUP_ZPOW_GEN : thm := BCyclicInteger.GROUP_ISOMORPHISM_GROUP_ZPOW_GEN
unsafe def ISOMORPHIC_GROUP_CYCLIC_INTEGER : thm := BCyclicInteger.ISOMORPHIC_GROUP_CYCLIC_INTEGER
unsafe def ORDER_INTEGER_MOD_GROUP : thm := BCyclicInteger.ORDER_INTEGER_MOD_GROUP
unsafe def ISOMORPHIC_FINITE_CYCLIC_INTEGER_MOD_GROUP : thm := BCyclicInteger.ISOMORPHIC_FINITE_CYCLIC_INTEGER_MOD_GROUP
unsafe def ISOMORPHIC_GROUP_INTEGER_MOD_GROUP : thm := BCyclicInteger.ISOMORPHIC_GROUP_INTEGER_MOD_GROUP
unsafe def ISOMORPHIC_INTEGER_MOD_GROUPS : thm := BCyclicInteger.ISOMORPHIC_INTEGER_MOD_GROUPS
unsafe def ISOMORPHIC_FINITE_CYCLIC_GROUPS : thm := BCyclicInteger.ISOMORPHIC_FINITE_CYCLIC_GROUPS
unsafe def CYCLIC_IMP_COUNTABLE_GROUP : thm := BCyclicInteger.CYCLIC_IMP_COUNTABLE_GROUP
unsafe def SUBGROUP_GENERATED_ELEMENT_ORDER : thm := BCyclicInteger.SUBGROUP_GENERATED_ELEMENT_ORDER
unsafe def CYCLIC_GROUP_ELEMENT_ORDER : thm := BCyclicInteger.CYCLIC_GROUP_ELEMENT_ORDER

-- CyclicProd
unsafe def CYCLIC_PROD_INTEGER_MOD_GROUP : thm := BCyclicProd.CYCLIC_PROD_INTEGER_MOD_GROUP
unsafe def ISOMORPHIC_PROD_INTEGER_MOD_GROUP : thm := BCyclicProd.ISOMORPHIC_PROD_INTEGER_MOD_GROUP
unsafe def GROUP_ISOMORPHISM_PROD_INTEGER_MOD_GROUP : thm := BCyclicProd.GROUP_ISOMORPHISM_PROD_INTEGER_MOD_GROUP
unsafe def CYCLIC_PROD_GROUP : thm := BCyclicProd.CYCLIC_PROD_GROUP
unsafe def CYCLIC_PRIME_ORDER_GROUP : thm := BCyclicProd.CYCLIC_PRIME_ORDER_GROUP
unsafe def GROUP_ELEMENT_ORDER_PRIME : thm := BCyclicProd.GROUP_ELEMENT_ORDER_PRIME
unsafe def GENERATOR_INTEGER_MOD_GROUP : thm := BCyclicProd.GENERATOR_INTEGER_MOD_GROUP
unsafe def CYCLIC_GROUP_PRIME_ORDER_EQ : thm := BCyclicProd.CYCLIC_GROUP_PRIME_ORDER_EQ

-- Pgroup
unsafe def pgroup : thm := BPgroup.pgroup
unsafe def PGROUP_MONOMORPHIC_PREIMAGE : thm := BPgroup.PGROUP_MONOMORPHIC_PREIMAGE
unsafe def PGROUP_EPIMORPHIC_IMAGE : thm := BPgroup.PGROUP_EPIMORPHIC_IMAGE
unsafe def PGROUP_QUOTIENT_GROUP : thm := BPgroup.PGROUP_QUOTIENT_GROUP
unsafe def PGROUP_SUBGROUP_GENERATED : thm := BPgroup.PGROUP_SUBGROUP_GENERATED
unsafe def PGROUP_PROD_GROUP : thm := BPgroup.PGROUP_PROD_GROUP
unsafe def PGROUP_EMPTY : thm := BPgroup.PGROUP_EMPTY
unsafe def PGROUP_MONO : thm := BPgroup.PGROUP_MONO
unsafe def PGROUP_SUM_GROUP : thm := BPgroup.PGROUP_SUM_GROUP
unsafe def PGROUP_SING : thm := BPgroup.PGROUP_SING

-- SylowCount
unsafe def SYLOW_THEOREM_COUNT_MOD : thm := BSylowCount.SYLOW_THEOREM_COUNT_MOD

-- Sylow
unsafe def SYLOW_THEOREM : thm := BSylow.SYLOW_THEOREM
unsafe def CAUCHY_GROUP_THEOREM : thm := BSylow.CAUCHY_GROUP_THEOREM
unsafe def PRIME_DIVIDES_GROUP_ORDER : thm := BSylow.PRIME_DIVIDES_GROUP_ORDER
unsafe def COPRIME_GROUP_ORDER : thm := BSylow.COPRIME_GROUP_ORDER
unsafe def FINITE_PGROUP : thm := BSylow.FINITE_PGROUP
unsafe def FINITE_PGROUP_SING : thm := BSylow.FINITE_PGROUP_SING
unsafe def FINITE_AND_PGROUP_SING : thm := BSylow.FINITE_AND_PGROUP_SING
unsafe def FINITE_GROUP_POW_INJECTIVE_EQ : thm := BSylow.FINITE_GROUP_POW_INJECTIVE_EQ
unsafe def FINITE_GROUP_ZPOW_INJECTIVE_EQ : thm := BSylow.FINITE_GROUP_ZPOW_INJECTIVE_EQ
unsafe def FINITE_GROUP_POW_SURJECTIVE_EQ : thm := BSylow.FINITE_GROUP_POW_SURJECTIVE_EQ
unsafe def FINITE_GROUP_ZPOW_SURJECTIVE_EQ : thm := BSylow.FINITE_GROUP_ZPOW_SURJECTIVE_EQ
unsafe def FINITE_GROUP_ZROOT_EXISTS : thm := BSylow.FINITE_GROUP_ZROOT_EXISTS
unsafe def FINITE_GROUP_ROOT_EXISTS : thm := BSylow.FINITE_GROUP_ROOT_EXISTS

-- Powering
unsafe def ABELIAN_GROUP_MONOMORPHISM_POWERING_EQ : thm := BPowering.ABELIAN_GROUP_MONOMORPHISM_POWERING_EQ
unsafe def ABELIAN_GROUP_MONOMORPHISM_POWERING : thm := BPowering.ABELIAN_GROUP_MONOMORPHISM_POWERING
unsafe def ABELIAN_GROUP_ISOMORPHISM_POWERING_EQ : thm := BPowering.ABELIAN_GROUP_ISOMORPHISM_POWERING_EQ
unsafe def ABELIAN_GROUP_ISOMORPHISM_POWERING : thm := BPowering.ABELIAN_GROUP_ISOMORPHISM_POWERING
unsafe def ABELIAN_GROUP_EPIMORPHISM_POWERING_EQ : thm := BPowering.ABELIAN_GROUP_EPIMORPHISM_POWERING_EQ
unsafe def ABELIAN_GROUP_EPIMORPHISM_POWERING : thm := BPowering.ABELIAN_GROUP_EPIMORPHISM_POWERING
unsafe def PGROUP_ACTION_FIXPOINTS : thm := BPowering.PGROUP_ACTION_FIXPOINTS
unsafe def PGROUP_ACTION_FIXPOINT : thm := BPowering.PGROUP_ACTION_FIXPOINT

-- Sylow2
unsafe def SYLOW_THEOREM_CONJUGATE_GEN : thm := BSylow2.SYLOW_THEOREM_CONJUGATE_GEN
unsafe def SYLOW_THEOREM_CONJUGATE_SUBSET : thm := BSylow2.SYLOW_THEOREM_CONJUGATE_SUBSET
unsafe def SYLOW_THEOREM_CONJUGATE_ALT : thm := BSylow2.SYLOW_THEOREM_CONJUGATE_ALT
unsafe def SYLOW_THEOREM_CONJUGATE : thm := BSylow2.SYLOW_THEOREM_CONJUGATE
unsafe def SYLOW_THEOREM_CONJUGATE_EQ : thm := BSylow2.SYLOW_THEOREM_CONJUGATE_EQ
unsafe def SYLOW_THEOREM_PGROUP_SUPERSET : thm := BSylow2.SYLOW_THEOREM_PGROUP_SUPERSET
unsafe def SYLOW_THEOREM_NORMAL_UNIQUE : thm := BSylow2.SYLOW_THEOREM_NORMAL_UNIQUE
unsafe def SYLOW_THEOREM_COUNT_NORMALIZER : thm := BSylow2.SYLOW_THEOREM_COUNT_NORMALIZER
unsafe def SYLOW_THEOREM_COUNT_NORMALIZER_MUL : thm := BSylow2.SYLOW_THEOREM_COUNT_NORMALIZER_MUL
unsafe def SYLOW_THEOREM_NORMAL_UNIQUE_EQ : thm := BSylow2.SYLOW_THEOREM_NORMAL_UNIQUE_EQ
unsafe def SYLOW_THEOREM_UNIQUE : thm := BSylow2.SYLOW_THEOREM_UNIQUE
unsafe def SYLOW_THEOREM_COUNT_DIVISOR : thm := BSylow2.SYLOW_THEOREM_COUNT_DIVISOR

-- PGroupCentre
unsafe def PGROUP_NONTRIVIAL_CENTRE_GEN : thm := BPGroupCentre.PGROUP_NONTRIVIAL_CENTRE_GEN
unsafe def PGROUP_NONTRIVIAL_CENTRE : thm := BPGroupCentre.PGROUP_NONTRIVIAL_CENTRE
unsafe def PGROUP_DIVIDES_NORMALIZER_QUOTIENT : thm := BPGroupCentre.PGROUP_DIVIDES_NORMALIZER_QUOTIENT

-- PgroupNormalizer
unsafe def PGROUP_SUBGROUP_PSUBSET_NORMALIZER : thm := BPgroupNormalizer.PGROUP_SUBGROUP_PSUBSET_NORMALIZER
unsafe def PGROUP_MAXIMAL_NORMAL_SUBGROUP_OF : thm := BPgroupNormalizer.PGROUP_MAXIMAL_NORMAL_SUBGROUP_OF
unsafe def PGROUP_FRATTINI : thm := BPgroupNormalizer.PGROUP_FRATTINI
unsafe def PGROUP_SELF_NORMALIZER : thm := BPgroupNormalizer.PGROUP_SELF_NORMALIZER
unsafe def PGROUP_NORMALIZER_NORMALIZER : thm := BPgroupNormalizer.PGROUP_NORMALIZER_NORMALIZER

-- GroupDisjointSum
unsafe def GROUP_DISJOINT_SUM_ALT : thm := BGroupDisjointSum.GROUP_DISJOINT_SUM_ALT
unsafe def GROUP_DISJOINT_SUM_ID : thm := BGroupDisjointSum.GROUP_DISJOINT_SUM_ID
unsafe def GROUP_DISJOINT_SUM_CANCEL : thm := BGroupDisjointSum.GROUP_DISJOINT_SUM_CANCEL
unsafe def GROUP_SUM_COMMUTING_IMP_NORMAL : thm := BGroupDisjointSum.GROUP_SUM_COMMUTING_IMP_NORMAL
unsafe def GROUP_SUM_NORMAL_IMP_COMMUTING : thm := BGroupDisjointSum.GROUP_SUM_NORMAL_IMP_COMMUTING
unsafe def GROUP_SUM_NORMAL_EQ_COMMUTING : thm := BGroupDisjointSum.GROUP_SUM_NORMAL_EQ_COMMUTING

-- GroupMulMorphism
unsafe def GROUP_HOMOMORPHISM_GROUP_MUL_GEN : thm := BGroupMulMorphism.GROUP_HOMOMORPHISM_GROUP_MUL_GEN
unsafe def GROUP_HOMOMORPHISM_GROUP_MUL_EQ : thm := BGroupMulMorphism.GROUP_HOMOMORPHISM_GROUP_MUL_EQ
unsafe def GROUP_HOMOMORPHISM_GROUP_MUL : thm := BGroupMulMorphism.GROUP_HOMOMORPHISM_GROUP_MUL
unsafe def GROUP_EPIMORPHISM_GROUP_MUL_EQ : thm := BGroupMulMorphism.GROUP_EPIMORPHISM_GROUP_MUL_EQ
unsafe def GROUP_MONOMORPHISM_GROUP_MUL_EQ : thm := BGroupMulMorphism.GROUP_MONOMORPHISM_GROUP_MUL_EQ
unsafe def GROUP_ISOMORPHISM_GROUP_MUL_ALT : thm := BGroupMulMorphism.GROUP_ISOMORPHISM_GROUP_MUL_ALT
unsafe def GROUP_ISOMORPHISM_GROUP_MUL_EQ : thm := BGroupMulMorphism.GROUP_ISOMORPHISM_GROUP_MUL_EQ
unsafe def GROUP_ISOMORPHISM_GROUP_MUL_GEN : thm := BGroupMulMorphism.GROUP_ISOMORPHISM_GROUP_MUL_GEN
unsafe def GROUP_ISOMORPHISM_GROUP_MUL : thm := BGroupMulMorphism.GROUP_ISOMORPHISM_GROUP_MUL

-- GroupSumImKer
unsafe def ISOMORPHIC_PROD_GROUP_SUBGROUP_GENERATED : thm := BGroupSumImKer.ISOMORPHIC_PROD_GROUP_SUBGROUP_GENERATED
unsafe def GROUP_INTER_IM_KER : thm := BGroupSumImKer.GROUP_INTER_IM_KER
unsafe def GROUP_SUM_IM_KER : thm := BGroupSumImKer.GROUP_SUM_IM_KER
unsafe def GROUP_SUM_KER_IM : thm := BGroupSumImKer.GROUP_SUM_KER_IM
unsafe def GROUP_SEMIDIRECT_SUM_IM_KER : thm := BGroupSumImKer.GROUP_SEMIDIRECT_SUM_IM_KER
unsafe def GROUP_SEMIDIRECT_SUM_KER_IM : thm := BGroupSumImKer.GROUP_SEMIDIRECT_SUM_KER_IM
unsafe def GROUP_ISOMORPHISM_GROUP_MUL_IM_KER : thm := BGroupSumImKer.GROUP_ISOMORPHISM_GROUP_MUL_IM_KER
unsafe def GROUP_ISOMORPHISM_GROUP_MUL_KER_IM : thm := BGroupSumImKer.GROUP_ISOMORPHISM_GROUP_MUL_KER_IM

-- GroupSumHomomorphism
unsafe def GROUP_HOMOMORPHISM_GROUP_SUM_GEN : thm := BGroupSumHomomorphism.GROUP_HOMOMORPHISM_GROUP_SUM_GEN
unsafe def GROUP_HOMOMORPHISM_GROUP_SUM_EQ : thm := BGroupSumHomomorphism.GROUP_HOMOMORPHISM_GROUP_SUM_EQ
unsafe def GROUP_HOMOMORPHISM_GROUP_SUM : thm := BGroupSumHomomorphism.GROUP_HOMOMORPHISM_GROUP_SUM
unsafe def GROUP_HOMOMORPHISM_ABELIAN_GROUP_SUM : thm := BGroupSumHomomorphism.GROUP_HOMOMORPHISM_ABELIAN_GROUP_SUM
unsafe def ABELIAN_GROUP_HOMOMORPHISM_GROUP_SUM : thm := BGroupSumHomomorphism.ABELIAN_GROUP_HOMOMORPHISM_GROUP_SUM

-- GroupSumEpimorphism
unsafe def SUBGROUP_EPIMORPHISM_GROUP_SUM_GEN : thm := BGroupSumEpimorphism.SUBGROUP_EPIMORPHISM_GROUP_SUM_GEN
unsafe def SUBGROUP_EPIMORPHISM_GROUP_SUM_EQ : thm := BGroupSumEpimorphism.SUBGROUP_EPIMORPHISM_GROUP_SUM_EQ
unsafe def SUBGROUP_EPIMORPHISM_GROUP_SUM : thm := BGroupSumEpimorphism.SUBGROUP_EPIMORPHISM_GROUP_SUM
unsafe def SUBGROUP_EPIMORPHISM_ABELIAN_GROUP_SUM : thm := BGroupSumEpimorphism.SUBGROUP_EPIMORPHISM_ABELIAN_GROUP_SUM
unsafe def GROUP_EPIMORPHISM_GROUP_SUM_GEN : thm := BGroupSumEpimorphism.GROUP_EPIMORPHISM_GROUP_SUM_GEN
unsafe def GROUP_EPIMORPHISM_GROUP_SUM_EQ : thm := BGroupSumEpimorphism.GROUP_EPIMORPHISM_GROUP_SUM_EQ
unsafe def GROUP_EPIMORPHISM_GROUP_SUM : thm := BGroupSumEpimorphism.GROUP_EPIMORPHISM_GROUP_SUM
unsafe def GROUP_EPIMORPHISM_ABELIAN_GROUP_SUM : thm := BGroupSumEpimorphism.GROUP_EPIMORPHISM_ABELIAN_GROUP_SUM

-- GroupSumMonomorphism
unsafe def GROUP_MONOMORPHISM_GROUP_SUM_GEN : thm := BGroupSumMonomorphism.GROUP_MONOMORPHISM_GROUP_SUM_GEN
unsafe def GROUP_MONOMORPHISM_GROUP_SUM_EQ : thm := BGroupSumMonomorphism.GROUP_MONOMORPHISM_GROUP_SUM_EQ
unsafe def GROUP_MONOMORPHISM_GROUP_SUM : thm := BGroupSumMonomorphism.GROUP_MONOMORPHISM_GROUP_SUM
unsafe def GROUP_MONOMORPHISM_ABELIAN_GROUP_SUM : thm := BGroupSumMonomorphism.GROUP_MONOMORPHISM_ABELIAN_GROUP_SUM
unsafe def SUBGROUP_ISOMORPHISM_GROUP_SUM_GEN : thm := BGroupSumMonomorphism.SUBGROUP_ISOMORPHISM_GROUP_SUM_GEN

-- SumGroupIsomorphism
unsafe def SUBGROUP_ISOMORPHISM_GROUP_SUM_EQ : thm := BSumGroupIsomorphism.SUBGROUP_ISOMORPHISM_GROUP_SUM_EQ
unsafe def SUBGROUP_ISOMORPHISM_GROUP_SUM : thm := BSumGroupIsomorphism.SUBGROUP_ISOMORPHISM_GROUP_SUM
unsafe def SUBGROUP_ISOMORPHISM_ABELIAN_GROUP_SUM : thm := BSumGroupIsomorphism.SUBGROUP_ISOMORPHISM_ABELIAN_GROUP_SUM
unsafe def GROUP_ISOMORPHISM_GROUP_SUM_GEN : thm := BSumGroupIsomorphism.GROUP_ISOMORPHISM_GROUP_SUM_GEN
unsafe def GROUP_ISOMORPHISM_GROUP_SUM_EQ : thm := BSumGroupIsomorphism.GROUP_ISOMORPHISM_GROUP_SUM_EQ
unsafe def GROUP_ISOMORPHISM_GROUP_SUM : thm := BSumGroupIsomorphism.GROUP_ISOMORPHISM_GROUP_SUM
unsafe def GROUP_ISOMORPHISM_ABELIAN_GROUP_SUM : thm := BSumGroupIsomorphism.GROUP_ISOMORPHISM_ABELIAN_GROUP_SUM
unsafe def ISOMORPHIC_SUM_GROUP_GEN : thm := BSumGroupIsomorphism.ISOMORPHIC_SUM_GROUP_GEN
unsafe def ISOMORPHIC_SUM_GROUP : thm := BSumGroupIsomorphism.ISOMORPHIC_SUM_GROUP
unsafe def ISOMORPHIC_ABELIAN_SUM_GROUP : thm := BSumGroupIsomorphism.ISOMORPHIC_ABELIAN_SUM_GROUP
unsafe def ISOMORPHIC_NORMAL_SUM_GROUP : thm := BSumGroupIsomorphism.ISOMORPHIC_NORMAL_SUM_GROUP

-- CarrierSubgroupGeneratedUnions
unsafe def CARRIER_SUBGROUP_GENERATED_UNIONS : thm := BCarrierSubgroupGeneratedUnions.CARRIER_SUBGROUP_GENERATED_UNIONS
unsafe def CARRIER_SUBGROUP_GENERATED_UNIONS_ALT : thm := BCarrierSubgroupGeneratedUnions.CARRIER_SUBGROUP_GENERATED_UNIONS_ALT
unsafe def CARRIER_SUBGROUP_GENERATED_UNIONS_FINITE : thm := BCarrierSubgroupGeneratedUnions.CARRIER_SUBGROUP_GENERATED_UNIONS_FINITE
unsafe def CARRIER_SUBGROUP_GENERATED_UNIONS_EXPLICIT : thm := BCarrierSubgroupGeneratedUnions.CARRIER_SUBGROUP_GENERATED_UNIONS_EXPLICIT
unsafe def CARRIER_SUBGROUP_GENERATED_ALT : thm := BCarrierSubgroupGeneratedUnions.CARRIER_SUBGROUP_GENERATED_ALT
unsafe def CARRIER_SUBGROUP_GENERATED_FINITE : thm := BCarrierSubgroupGeneratedUnions.CARRIER_SUBGROUP_GENERATED_FINITE
unsafe def CARRIER_SUBGROUP_GENERATED_EXPLICIT : thm := BCarrierSubgroupGeneratedUnions.CARRIER_SUBGROUP_GENERATED_EXPLICIT

-- PrimeTorsion
unsafe def SUBGROUP_GENERATED_UNIONS_PRIME_TORSION_FINITE : thm := BPrimeTorsion.SUBGROUP_GENERATED_UNIONS_PRIME_TORSION_FINITE
unsafe def SUBGROUP_GENERATED_UNIONS_PRIME_TORSION : thm := BPrimeTorsion.SUBGROUP_GENERATED_UNIONS_PRIME_TORSION

-- TorsionStructure
unsafe def SUBGROUP_GENERATED_UNIONS_PRIME_TORSION_FULL : thm := BTorsionStructure.SUBGROUP_GENERATED_UNIONS_PRIME_TORSION_FULL
unsafe def PGROUP_PRIME_TORSION : thm := BTorsionStructure.PGROUP_PRIME_TORSION
unsafe def PGROUP_SUBSET_PRIME_TORSION : thm := BTorsionStructure.PGROUP_SUBSET_PRIME_TORSION
unsafe def ABELIAN_GROUP_TORSION_ISOMORPHISM : thm := BTorsionStructure.ABELIAN_GROUP_TORSION_ISOMORPHISM
unsafe def ABELIAN_GROUP_TORSION_STRUCTURE : thm := BTorsionStructure.ABELIAN_GROUP_TORSION_STRUCTURE
unsafe def TORSION_ABELIAN_GROUP_ISOMORPHISM : thm := BTorsionStructure.TORSION_ABELIAN_GROUP_ISOMORPHISM
unsafe def TORSION_ABELIAN_GROUP_STRUCTURE : thm := BTorsionStructure.TORSION_ABELIAN_GROUP_STRUCTURE
unsafe def FINITE_ABELIAN_GROUP_STRUCTURE : thm := BTorsionStructure.FINITE_ABELIAN_GROUP_STRUCTURE
unsafe def FINITE_ABELIAN_GROUP_STRUCTURE_ALT : thm := BTorsionStructure.FINITE_ABELIAN_GROUP_STRUCTURE_ALT
unsafe def TORSION_ABELIAN_GROUP_AS_SUM_OF_PGROUPS : thm := BTorsionStructure.TORSION_ABELIAN_GROUP_AS_SUM_OF_PGROUPS

-- FinitelyGeneratedAbelian
unsafe def FINITELY_GENERATED_ABELIAN_SUBGROUP_STRUCTURE_ISOMORPHISM : thm := BFinitelyGeneratedAbelian.FINITELY_GENERATED_ABELIAN_SUBGROUP_STRUCTURE_ISOMORPHISM

-- FinGenAbelianStructure
unsafe def FINITELY_GENERATED_ABELIAN_SUBGROUP_STRUCTURE_ISOMORPHISM_ALT : thm := BFinGenAbelianStructure.FINITELY_GENERATED_ABELIAN_SUBGROUP_STRUCTURE_ISOMORPHISM_ALT
unsafe def FINITELY_GENERATED_ABELIAN_SUBGROUP_STRUCTURE_EXPLICIT : thm := BFinGenAbelianStructure.FINITELY_GENERATED_ABELIAN_SUBGROUP_STRUCTURE_EXPLICIT
unsafe def FINITELY_GENERATED_ABELIAN_SUBGROUP_STRUCTURE_EXPLICIT_ALT : thm := BFinGenAbelianStructure.FINITELY_GENERATED_ABELIAN_SUBGROUP_STRUCTURE_EXPLICIT_ALT
unsafe def FINITELY_GENERATED_ABELIAN_GROUP_STRUCTURE_EXPLICIT : thm := BFinGenAbelianStructure.FINITELY_GENERATED_ABELIAN_GROUP_STRUCTURE_EXPLICIT
unsafe def FINITELY_GENERATED_ABELIAN_GROUP_STRUCTURE_EXPLICIT_ALT : thm := BFinGenAbelianStructure.FINITELY_GENERATED_ABELIAN_GROUP_STRUCTURE_EXPLICIT_ALT
unsafe def FINITELY_GENERATED_ABELIAN_GROUP_AS_SUM_OF_CYCLIC_GROUPS : thm := BFinGenAbelianStructure.FINITELY_GENERATED_ABELIAN_GROUP_AS_SUM_OF_CYCLIC_GROUPS
unsafe def FINITELY_GENERATED_ABELIAN_GROUP_AS_PRODUCT_OF_CYCLIC_GROUPS : thm := BFinGenAbelianStructure.FINITELY_GENERATED_ABELIAN_GROUP_AS_PRODUCT_OF_CYCLIC_GROUPS
unsafe def FINITELY_GENERATED_ABELIAN_GROUP_AS_SUM_OF_INTEGER_MOD_GROUPS : thm := BFinGenAbelianStructure.FINITELY_GENERATED_ABELIAN_GROUP_AS_SUM_OF_INTEGER_MOD_GROUPS
unsafe def FINITELY_GENERATED_ABELIAN_GROUP_AS_PRODUCT_OF_INTEGER_MOD_GROUPS : thm := BFinGenAbelianStructure.FINITELY_GENERATED_ABELIAN_GROUP_AS_PRODUCT_OF_INTEGER_MOD_GROUPS
unsafe def FINITELY_GENERATED_ABELIAN_GROUP_AS_SUM_OF_INTEGER_GROUPS : thm := BFinGenAbelianStructure.FINITELY_GENERATED_ABELIAN_GROUP_AS_SUM_OF_INTEGER_GROUPS
unsafe def FINITELY_GENERATED_ABELIAN_GROUP_AS_PRODUCT_OF_INTEGER_GROUPS : thm := BFinGenAbelianStructure.FINITELY_GENERATED_ABELIAN_GROUP_AS_PRODUCT_OF_INTEGER_GROUPS

-- FreeAbelianGroup
unsafe def free_abelian_group : thm := BFreeAbelianGroup.free_abelian_group
unsafe def FREE_ABELIAN_GROUP : thm := BFreeAbelianGroup.FREE_ABELIAN_GROUP
unsafe def ABELIAN_FREE_ABELIAN_GROUP : thm := BFreeAbelianGroup.ABELIAN_FREE_ABELIAN_GROUP
unsafe def FREE_ABELIAN_GROUP_POW : thm := BFreeAbelianGroup.FREE_ABELIAN_GROUP_POW
unsafe def FREE_ABELIAN_GROUP_ZPOW : thm := BFreeAbelianGroup.FREE_ABELIAN_GROUP_ZPOW
unsafe def FRAG_OF_IN_FREE_ABELIAN_GROUP : thm := BFreeAbelianGroup.FRAG_OF_IN_FREE_ABELIAN_GROUP
unsafe def FREE_ABELIAN_GROUP_INDUCT : thm := BFreeAbelianGroup.FREE_ABELIAN_GROUP_INDUCT
unsafe def FREE_ABELIAN_GROUP_UNIVERSAL : thm := BFreeAbelianGroup.FREE_ABELIAN_GROUP_UNIVERSAL
unsafe def ISOMORPHIC_GROUP_INTEGER_FREE_ABELIAN_GROUP_SING : thm := BFreeAbelianGroup.ISOMORPHIC_GROUP_INTEGER_FREE_ABELIAN_GROUP_SING
unsafe def GROUP_HOMOMORPHISM_FREE_ABELIAN_GROUPS_ID : thm := BFreeAbelianGroup.GROUP_HOMOMORPHISM_FREE_ABELIAN_GROUPS_ID
unsafe def GROUP_ISOMORPHISM_FREE_ABELIAN_GROUP_SUM : thm := BFreeAbelianGroup.GROUP_ISOMORPHISM_FREE_ABELIAN_GROUP_SUM

-- FreeAbelianExtra
unsafe def ISOMORPHIC_FREE_ABELIAN_GROUP_UNIONS : thm := BFreeAbelianExtra.ISOMORPHIC_FREE_ABELIAN_GROUP_UNIONS
unsafe def ISOMORPHIC_SUM_INTEGER_GROUP : thm := BFreeAbelianExtra.ISOMORPHIC_SUM_INTEGER_GROUP
unsafe def CARD_EQ_FREE_ABELIAN_GROUP_INFINITE : thm := BFreeAbelianExtra.CARD_EQ_FREE_ABELIAN_GROUP_INFINITE
unsafe def CARD_EQ_HOMOMORPHISMS_FROM_FREE_ABELIAN_GROUP : thm := BFreeAbelianExtra.CARD_EQ_HOMOMORPHISMS_FROM_FREE_ABELIAN_GROUP
unsafe def ISOMORPHIC_FREE_ABELIAN_GROUPS : thm := BFreeAbelianExtra.ISOMORPHIC_FREE_ABELIAN_GROUPS

-- SolvableGroup
unsafe def solvable_group : thm := BSolvableGroup.solvable_group
unsafe def SOLVABLE_GROUP_ALT : thm := BSolvableGroup.SOLVABLE_GROUP_ALT
unsafe def ABELIAN_QUOTIENT_COMMUTATOR : thm := BSolvableGroup.ABELIAN_QUOTIENT_COMMUTATOR
unsafe def TRIVIAL_IMP_SOLVABLE_GROUP : thm := BSolvableGroup.TRIVIAL_IMP_SOLVABLE_GROUP
unsafe def ABELIAN_IMP_SOLVABLE_GROUP : thm := BSolvableGroup.ABELIAN_IMP_SOLVABLE_GROUP
unsafe def SOLVABLE_GROUP_NORMAL_EXTENSION : thm := BSolvableGroup.SOLVABLE_GROUP_NORMAL_EXTENSION

-- SolvableImage
unsafe def ABELIAN_QUOTIENT_EPIMORPHIC_IMAGE : thm := BSolvableImage.ABELIAN_QUOTIENT_EPIMORPHIC_IMAGE
unsafe def SOLVABLE_GROUP_EPIMORPHIC_IMAGE : thm := BSolvableImage.SOLVABLE_GROUP_EPIMORPHIC_IMAGE
unsafe def SOLVABLE_GROUP_QUOTIENT : thm := BSolvableImage.SOLVABLE_GROUP_QUOTIENT
unsafe def ISOMORPHIC_GROUP_SOLVABILITY : thm := BSolvableImage.ISOMORPHIC_GROUP_SOLVABILITY
unsafe def COMMUTATOR_IMP_ABELIAN_QUOTIENT : thm := BSolvableImage.COMMUTATOR_IMP_ABELIAN_QUOTIENT
unsafe def ABELIAN_QUOTIENT_GROUP_DIV : thm := BSolvableImage.ABELIAN_QUOTIENT_GROUP_DIV

-- SolvableSubgroup
unsafe def SOLVABLE_GROUP_SUBGROUP : thm := BSolvableSubgroup.SOLVABLE_GROUP_SUBGROUP
unsafe def SOLVABLE_GROUP_MONOMORPHIC_PREIMAGE : thm := BSolvableSubgroup.SOLVABLE_GROUP_MONOMORPHIC_PREIMAGE

-- SolvableQuotient
unsafe def SOLVABLE_GROUP_SOLVABLE_QUOTIENT : thm := BSolvableQuotient.SOLVABLE_GROUP_SOLVABLE_QUOTIENT

-- ExactSequences
unsafe def group_exactness : thm := BExactSequences.group_exactness
unsafe def short_exact_sequence : thm := BExactSequences.short_exact_sequence
unsafe def SHORT_EXACT_SEQUENCE : thm := BExactSequences.SHORT_EXACT_SEQUENCE
unsafe def GROUP_EXACTNESS_MONOMORPHISM : thm := BExactSequences.GROUP_EXACTNESS_MONOMORPHISM
unsafe def GROUP_EXACTNESS_EPIMORPHISM : thm := BExactSequences.GROUP_EXACTNESS_EPIMORPHISM
unsafe def EXTREMELY_SHORT_EXACT_SEQUENCE : thm := BExactSequences.EXTREMELY_SHORT_EXACT_SEQUENCE
unsafe def GROUP_EXACTNESS_EPIMORPHISM_EQ_TRIVIALITY : thm := BExactSequences.GROUP_EXACTNESS_EPIMORPHISM_EQ_TRIVIALITY
unsafe def GROUP_EXACTNESS_MONOMORPHISM_EQ_TRIVIALITY : thm := BExactSequences.GROUP_EXACTNESS_MONOMORPHISM_EQ_TRIVIALITY
unsafe def VERY_SHORT_EXACT_SEQUENCE : thm := BExactSequences.VERY_SHORT_EXACT_SEQUENCE
unsafe def GROUP_EXACTNESS_EQ_TRIVIALITY : thm := BExactSequences.GROUP_EXACTNESS_EQ_TRIVIALITY
unsafe def GROUP_EXACTNESS_IMP_TRIVIALITY : thm := BExactSequences.GROUP_EXACTNESS_IMP_TRIVIALITY
unsafe def GROUP_EXACTNESS_ISOMORPHISM_EQ_TRIVIALITY : thm := BExactSequences.GROUP_EXACTNESS_ISOMORPHISM_EQ_TRIVIALITY
unsafe def GROUP_EXACTNESS_ISOMORPHISM_EQ_MONO_EPI : thm := BExactSequences.GROUP_EXACTNESS_ISOMORPHISM_EQ_MONO_EPI
unsafe def SHORT_EXACT_SEQUENCE_NORMAL_SUBGROUP : thm := BExactSequences.SHORT_EXACT_SEQUENCE_NORMAL_SUBGROUP
unsafe def SHORT_EXACT_SEQUENCE_PROD_GROUP : thm := BExactSequences.SHORT_EXACT_SEQUENCE_PROD_GROUP
unsafe def SHORT_EXACT_SEQUENCE_PROD_GROUP_ALT : thm := BExactSequences.SHORT_EXACT_SEQUENCE_PROD_GROUP_ALT

-- ExactSeq
unsafe def EXACT_SEQUENCE_SUM_LEMMA : thm := BExactSeq.EXACT_SEQUENCE_SUM_LEMMA
unsafe def SHORT_EXACT_SEQUENCE_QUOTIENT : thm := BExactSeq.SHORT_EXACT_SEQUENCE_QUOTIENT
unsafe def TRIVIAL_GROUPS_IMP_SHORT_EXACT_SEQUENCE : thm := BExactSeq.TRIVIAL_GROUPS_IMP_SHORT_EXACT_SEQUENCE
unsafe def SHORT_EXACT_SEQUENCE_TRIVIAL_GROUPS : thm := BExactSeq.SHORT_EXACT_SEQUENCE_TRIVIAL_GROUPS
unsafe def SPLITTING_SUBLEMMA_GEN : thm := BExactSeq.SPLITTING_SUBLEMMA_GEN
unsafe def SPLITTING_SUBLEMMA : thm := BExactSeq.SPLITTING_SUBLEMMA
unsafe def SPLITTING_LEMMA_LEFT_GEN : thm := BExactSeq.SPLITTING_LEMMA_LEFT_GEN
unsafe def SPLITTING_LEMMA_LEFT : thm := BExactSeq.SPLITTING_LEMMA_LEFT
unsafe def SPLITTING_LEMMA_LEFT_PROD_GROUP : thm := BExactSeq.SPLITTING_LEMMA_LEFT_PROD_GROUP
unsafe def SPLITTING_LEMMA_RIGHT_GEN : thm := BExactSeq.SPLITTING_LEMMA_RIGHT_GEN
unsafe def SPLITTING_LEMMA_RIGHT : thm := BExactSeq.SPLITTING_LEMMA_RIGHT
unsafe def SPLITTING_LEMMA_RIGHT_PROD_GROUP : thm := BExactSeq.SPLITTING_LEMMA_RIGHT_PROD_GROUP

-- FiveLemma
unsafe def SPLITTING_LEMMA_FREE_ABELIAN_GROUP : thm := BFiveLemma.SPLITTING_LEMMA_FREE_ABELIAN_GROUP
unsafe def FOUR_LEMMA_MONO : thm := BFiveLemma.FOUR_LEMMA_MONO
unsafe def FOUR_LEMMA_EPI : thm := BFiveLemma.FOUR_LEMMA_EPI
unsafe def FIVE_LEMMA : thm := BFiveLemma.FIVE_LEMMA

-- ShortFiveLemma
unsafe def SHORT_FIVE_LEMMA_MONO : thm := BShortFiveLemma.SHORT_FIVE_LEMMA_MONO
unsafe def SHORT_FIVE_LEMMA_EPI : thm := BShortFiveLemma.SHORT_FIVE_LEMMA_EPI
unsafe def SHORT_FIVE_LEMMA : thm := BShortFiveLemma.SHORT_FIVE_LEMMA
unsafe def EXACT_SEQUENCE_HEXAGON_LEMMA : thm := BShortFiveLemma.EXACT_SEQUENCE_HEXAGON_LEMMA
-- @@EXPORTS END

/-- `needs "Library/grouptheory.ml"`: build the bundles, in order. -/
unsafe def ensureGroupTheory : IO Unit := do
  -- @@ENSURE BEGIN
  let _ ← IO.mkRef BBasics.group_tybij
  let _ ← IO.mkRef BDerived.group_div
  let _ ← IO.mkRef BPow.GROUP_COMMUTES_POW
  let _ ← IO.mkRef BAbelian.abelian_group
  let _ ← IO.mkRef BTotalized.group_neg
  let _ ← IO.mkRef BGroupRule.GROUP_RULE
  let _ ← IO.mkRef BGroupProduct.group_product
  let _ ← IO.mkRef BGroupProductClauses.GROUP_PRODUCT_UNION
  let _ ← IO.mkRef BGroupProductMul.GROUP_PRODUCT_MUL
  let _ ← IO.mkRef BConjugation.group_conjugation
  let _ ← IO.mkRef BSubgroups.subgroup_of
  let _ ← IO.mkRef BSubgroupGenerated.subgroup_generated
  let _ ← IO.mkRef BSubgroupGen1.FINITE_SUBGROUP_GENERATED
  let _ ← IO.mkRef BSubgroupGen2.SUBGROUP_GENERATED_INSERT_ID
  let _ ← IO.mkRef BProdGroup.prod_group
  let _ ← IO.mkRef BProductGroup.PRODUCT_GROUP
  let _ ← IO.mkRef BSumGroup.sum_group
  let _ ← IO.mkRef BHomomorphisms.group_homomorphism
  let _ ← IO.mkRef BHomomorphisms1.GROUP_HOMOMORPHISM_INV
  let _ ← IO.mkRef BHomomorphisms2.SUBGROUP_GENERATED_BY_HOMOMORPHIC_IMAGE
  let _ ← IO.mkRef BHomomorphisms3.CARD_EQ_GROUP_ISOMORPHIC_IMAGE
  let _ ← IO.mkRef BHomomorphisms4.GROUP_HOMOMORPHISM_COMPONENTWISE
  let _ ← IO.mkRef BIso1.isomorphic_group
  let _ ← IO.mkRef BIso2.ISOMORPHIC_PRODUCT_GROUP_BIJECTIONS
  let _ ← IO.mkRef BDirectLimit.GROUP_DIRECT_LIMIT
  let _ ← IO.mkRef BSetwise1.group_setinv
  let _ ← IO.mkRef BSetwise2.GROUP_SETMUL_RSUBSET_EQ
  let _ ← IO.mkRef BGroupActions.group_action
  let _ ← IO.mkRef BGroupOrbits.group_orbit
  let _ ← IO.mkRef BOrbitStabilizer.ORBIT_STABILIZER_MUL_GEN
  let _ ← IO.mkRef BCosets.right_coset
  let _ ← IO.mkRef BCosets1.IN_LEFT_COSET_SELF
  let _ ← IO.mkRef BCosets2.GROUP_ORBIT_SUBGROUP_TRANSLATION
  let _ ← IO.mkRef BCosetProducts.RIGHT_COSET_PRODUCT_GROUP
  let _ ← IO.mkRef BNormalSubgroups.normal_subgroup_of
  let _ ← IO.mkRef BNormalSubgroups2.GROUP_SETMUL_RIGHT_COSET
  let _ ← IO.mkRef BConjugate.group_conjugate
  let _ ← IO.mkRef BCentralizerNormalizer.group_centralizer
  let _ ← IO.mkRef BCentralizerNormalizer2.GROUP_CENTRALIZER_ALT
  let _ ← IO.mkRef BQuotientGroups.quotient_group
  let _ ← IO.mkRef BKernelsImages1.group_kernel
  let _ ← IO.mkRef BKernelsImages2.QUOTIENT_GROUP_UNIVERSAL_EXPLICIT
  let _ ← IO.mkRef BSubgroupCorrespondence.GROUP_EPIMORPHISM_SUBGROUP_CORRESPONDENCE_ALT
  let _ ← IO.mkRef BTrivialHomomorphisms.trivial_homomorphism
  let _ ← IO.mkRef BGroupElementOrder.group_element_order
  let _ ← IO.mkRef BGroupElementOrder2.GROUP_ELEMENT_ORDER_POW_GEN
  let _ ← IO.mkRef BOrderDecomp.GROUP_ELEMENT_ORDER_LCM_EXISTS
  let _ ← IO.mkRef BTorsionSubgroups.SUBGROUP_OF_TORSION_GENERAL
  let _ ← IO.mkRef BCyclicGroups1.SUBGROUP_OF_POWERS
  let _ ← IO.mkRef BCyclicGroups2.FINITE_CYCLIC_SUBGROUP
  let _ ← IO.mkRef BCyclicGroups3.ABELIAN_SIMPLE_GROUP
  let _ ← IO.mkRef BFinitelyGenerated.finitely_generated_group
  let _ ← IO.mkRef BFinitelyGeneratedSubgroups.FINITELY_GENERATED_FIXED_INDEX_SUBGROUPS
  let _ ← IO.mkRef BFinitelyGeneratedMaximal.FINITELY_GENERATED_ABELIAN_SUBGROUP
  let _ ← IO.mkRef BIntegerGroup.integer_group
  let _ ← IO.mkRef BIntegerModGroup.integer_mod_group
  let _ ← IO.mkRef BCyclicInteger.CYCLIC_INTEGER_GROUP
  let _ ← IO.mkRef BCyclicProd.CYCLIC_PROD_INTEGER_MOD_GROUP
  let _ ← IO.mkRef BPgroup.pgroup
  let _ ← IO.mkRef BSylowCount.SYLOW_THEOREM_COUNT_MOD
  let _ ← IO.mkRef BSylow.SYLOW_THEOREM
  let _ ← IO.mkRef BPowering.ABELIAN_GROUP_MONOMORPHISM_POWERING_EQ
  let _ ← IO.mkRef BSylow2.SYLOW_THEOREM_CONJUGATE_GEN
  let _ ← IO.mkRef BPGroupCentre.PGROUP_NONTRIVIAL_CENTRE_GEN
  let _ ← IO.mkRef BPgroupNormalizer.PGROUP_SUBGROUP_PSUBSET_NORMALIZER
  let _ ← IO.mkRef BGroupDisjointSum.GROUP_DISJOINT_SUM_ALT
  let _ ← IO.mkRef BGroupMulMorphism.GROUP_HOMOMORPHISM_GROUP_MUL_GEN
  let _ ← IO.mkRef BGroupSumImKer.ISOMORPHIC_PROD_GROUP_SUBGROUP_GENERATED
  let _ ← IO.mkRef BGroupSumHomomorphism.GROUP_HOMOMORPHISM_GROUP_SUM_GEN
  let _ ← IO.mkRef BGroupSumEpimorphism.SUBGROUP_EPIMORPHISM_GROUP_SUM_GEN
  let _ ← IO.mkRef BGroupSumMonomorphism.GROUP_MONOMORPHISM_GROUP_SUM_GEN
  let _ ← IO.mkRef BSumGroupIsomorphism.SUBGROUP_ISOMORPHISM_GROUP_SUM_EQ
  let _ ← IO.mkRef BCarrierSubgroupGeneratedUnions.CARRIER_SUBGROUP_GENERATED_UNIONS
  let _ ← IO.mkRef BPrimeTorsion.SUBGROUP_GENERATED_UNIONS_PRIME_TORSION_FINITE
  let _ ← IO.mkRef BTorsionStructure.SUBGROUP_GENERATED_UNIONS_PRIME_TORSION_FULL
  let _ ← IO.mkRef BFinitelyGeneratedAbelian.FINITELY_GENERATED_ABELIAN_SUBGROUP_STRUCTURE_ISOMORPHISM
  let _ ← IO.mkRef BFinGenAbelianStructure.FINITELY_GENERATED_ABELIAN_SUBGROUP_STRUCTURE_ISOMORPHISM_ALT
  let _ ← IO.mkRef BFreeAbelianGroup.free_abelian_group
  let _ ← IO.mkRef BFreeAbelianExtra.ISOMORPHIC_FREE_ABELIAN_GROUP_UNIONS
  let _ ← IO.mkRef BSolvableGroup.solvable_group
  let _ ← IO.mkRef BSolvableImage.ABELIAN_QUOTIENT_EPIMORPHIC_IMAGE
  let _ ← IO.mkRef BSolvableSubgroup.SOLVABLE_GROUP_SUBGROUP
  let _ ← IO.mkRef BSolvableQuotient.SOLVABLE_GROUP_SOLVABLE_QUOTIENT
  let _ ← IO.mkRef BExactSequences.group_exactness
  let _ ← IO.mkRef BExactSeq.EXACT_SEQUENCE_SUM_LEMMA
  let _ ← IO.mkRef BFiveLemma.SPLITTING_LEMMA_FREE_ABELIAN_GROUP
  let _ ← IO.mkRef BShortFiveLemma.SHORT_FIVE_LEMMA_MONO
  -- @@ENSURE END
  pure ()

end SessionLibrary.GroupTheory
