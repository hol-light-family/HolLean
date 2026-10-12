/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/ringtheory.ml.                            -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/RingTheory.lean

  The `unsafe` half of the ringtheory.ml translation: it supplies
  HolLibrary.RingTheory's dependencies from Session and the parent
  libraries, builds each bundle once, in file order, and
  exports every name under its HOL Light name.  `ensureRingTheory` is
  `needs "Library/ringtheory.ml"` (which first does `needs
  "Library/binomial.ml"`, `needs "Library/pocklington.ml"` and `needs
  "Library/card.ml"`).

  The blocks between `@@CORE` and `@@EXPORTS` markers are generated from
  HolLibrary/RingTheory.lean by tools/ringtheorydiff/gen_session.py and
  scope.py (bookkeeping only: field-by-field copies and accessors).  The
  parents' theorems are filled from their SessionLibrary modules, the
  last-loaded first, as OCaml's shadowing.
-/

import Session
import HolLibrary.RingTheory
import SessionLibrary.Binomial
import SessionLibrary.Pocklington
import SessionLibrary.Card

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.RingTheory

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨Session.sessionB, Session.sessionC, Session.sessionT⟩

-- @@CORE BEGIN
/-- The core theorems ringtheory.ml uses. -/
unsafe def core1 (_ : Unit) : HolLibrary.RingTheory.CoreThms1 where
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
  CARD_IMAGE_INJ := Session.CARD_IMAGE_INJ
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
unsafe def core2 (_ : Unit) : HolLibrary.RingTheory.CoreThms2 where
  COND_RAND := Session.COND_RAND
  COND_RATOR := Session.COND_RATOR
  COND_SWAP := Session.COND_SWAP
  CONG := Session.CONG
  CONG_IMP_EQ := SessionLibrary.Pocklington.«CONG_IMP_EQ»
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
  DIVIDES_ANTISYM := Session.DIVIDES_ANTISYM
  DIVIDES_EXP_LE_IMP := SessionLibrary.Prime.«DIVIDES_EXP_LE_IMP»
  DIVIDES_LCM_GCD := SessionLibrary.Prime.«DIVIDES_LCM_GCD»
  DIVIDES_LE := Session.DIVIDES_LE
  DIVIDES_ONE := Session.DIVIDES_ONE
  DIVIDES_PRIME_BINOM := SessionLibrary.Binomial.«DIVIDES_PRIME_BINOM»
  DIVIDES_REFL := SessionLibrary.Prime.«DIVIDES_REFL»
  DIVIDES_ZERO := SessionLibrary.Prime.«DIVIDES_ZERO»
  DIVISION_SIMP := Session.DIVISION_SIMP
  DIV_MULT := Session.DIV_MULT
  EMPTY_GSPEC := Session.EMPTY_GSPEC
  EMPTY_NUMSEG := Session.EMPTY_NUMSEG
  EMPTY_SUBSET := Session.EMPTY_SUBSET
  EMPTY_UNIONS := Session.EMPTY_UNIONS
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
  EXISTS_UNIQUE_UNIONS_INTERS := Session.EXISTS_UNIQUE_UNIONS_INTERS
  EXISTS_UNPAIR_THM := Session.EXISTS_UNPAIR_THM
  EXP := Session.EXP
  EXTENSION := Session.EXTENSION
  EXTENSIONAL := Session.EXTENSIONAL
/-- The core theorems ringtheory.ml uses. -/
unsafe def core3 (_ : Unit) : HolLibrary.RingTheory.CoreThms3 where
  EXTENSIONAL_UNIV := Session.EXTENSIONAL_UNIV
  FINITE_1 := Session.FINITE_1
  FINITE_BOOL := Session.FINITE_BOOL
  FINITE_CARTESIAN_PRODUCT := SessionLibrary.Card.«FINITE_CARTESIAN_PRODUCT»
  FINITE_CROSS := Session.FINITE_CROSS
  FINITE_CROSS_EQ := Session.FINITE_CROSS_EQ
  FINITE_DELETE := Session.FINITE_DELETE
  FINITE_DIFF := Session.FINITE_DIFF
  FINITE_EMPTY := Session.FINITE_EMPTY
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
  HAS_SIZE_1 := Session.HAS_SIZE_1
  HAS_SIZE_BOOL := Session.HAS_SIZE_BOOL
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
unsafe def core4 (_ : Unit) : HolLibrary.RingTheory.CoreThms4 where
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
  INSERT_RESTRICT := Session.INSERT_RESTRICT
  INSERT_SUBSET := Session.INSERT_SUBSET
  INTERS_ANTIMONO_GEN := Session.INTERS_ANTIMONO_GEN
  INTERS_GSPEC := Session.INTERS_GSPEC
  INTER_ASSOC := Session.INTER_ASSOC
  INTER_COMM := Session.INTER_COMM
  INTER_CROSS := Session.INTER_CROSS
  INTER_RESTRICT := Session.INTER_RESTRICT
  INTER_SUBSET := Session.INTER_SUBSET
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
unsafe def core5 (_ : Unit) : HolLibrary.RingTheory.CoreThms5 where
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
  LE_REFL := Session.LE_REFL
  LE_SUC := Session.LE_SUC
  LE_TRANS := Session.LE_TRANS
  LT := Session.LT
  LT_ANTISYM := Session.LT_ANTISYM
  LT_IMP_LE := Session.LT_IMP_LE
/-- The core theorems ringtheory.ml uses. -/
unsafe def core6 (_ : Unit) : HolLibrary.RingTheory.CoreThms6 where
  LT_IMP_NE := Session.LT_IMP_NE
  LT_REFL := Session.LT_REFL
  LT_SUC_LE := Session.LT_SUC_LE
  LT_TRANS := Session.LT_TRANS
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MINIMAL := Session.MINIMAL
  MINIMAL_LE := Session.MINIMAL_LE
  MINIMAL_UNIQUE := Session.MINIMAL_UNIQUE
  MOD_LT := Session.MOD_LT
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
  NSUM_DELTA := Session.NSUM_DELTA
  NSUM_EQ := Session.NSUM_EQ
  NSUM_EQ_0_IFF := Session.NSUM_EQ_0_IFF
  NSUM_SING := Session.NSUM_SING
  NSUM_SUPERSET := Session.NSUM_SUPERSET
  NUMSEG_ADD_SPLIT := Session.NUMSEG_ADD_SPLIT
  NUMSEG_CLAUSES := Session.NUMSEG_CLAUSES
  NUMSEG_CLAUSES_LT := Session.NUMSEG_CLAUSES_LT
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
  PRIME_IMP_NZ := SessionLibrary.Prime.«PRIME_IMP_NZ»
  PROPERLY_PROPERLY := SessionLibrary.Wo.«PROPERLY_PROPERLY»
  PSUBSET := Session.PSUBSET
  PSUBSET_ALT := Session.PSUBSET_ALT
  QOSET_FLD := SessionLibrary.Wo.«QOSET_FLD»
  REAL_ENTIRE := Session.REAL_ENTIRE
  REAL_INV_0 := Session.REAL_INV_0
  REAL_MUL_RINV := Session.REAL_MUL_RINV
  REAL_OF_NUM_EQ := Session.REAL_OF_NUM_EQ
  REAL_OF_NUM_SUC := Session.REAL_OF_NUM_SUC
/-- The core theorems ringtheory.ml uses. -/
unsafe def core7 (_ : Unit) : HolLibrary.RingTheory.CoreThms7 where
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
unsafe def core8 (_ : Unit) : HolLibrary.RingTheory.CoreThms8 where
  WF_IND := Session.WF_IND
  WF_LEX := Session.WF_LEX
  WF_MEASURE_GEN := Session.WF_MEASURE_GEN
  WF_REC_EXISTS := Session.WF_REC_EXISTS
  WF_SUBSET := Session.WF_SUBSET
  WF_num := Session.WF_num
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
  properly := SessionLibrary.Wo.«properly»
  qoset := SessionLibrary.Wo.«qoset»
  real_pow := Session.real_pow
  strictly := SessionLibrary.Wo.«strictly»
  sum_DISTINCT := SessionLibrary.Card.«sum_DISTINCT»
  sum_INJECTIVE := SessionLibrary.Card.«sum_INJECTIVE»
  support := Session.support
  toset := SessionLibrary.Wo.«toset»-- @@CORE END

/-- What ringtheory.ml uses from Session. -/
unsafe def deps (_ : Unit) : HolLibrary.RingTheory.RingTheoryDeps where
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
  core1 := core1 ()
  core2 := core2 ()
  core3 := core3 ()
  core4 := core4 ()
  core5 := core5 ()
  core6 := core6 ()
  core7 := core7 ()
  core8 := core8 ()

/-- Build a bundle once.  `setup` is a thunk, so that `deps` is not built
    before the bundle is needed.  The whole core library is built first
    (`Session.ensureDefine`, and MATCH_CONV's basic conversions, which HOL
    Light adds loading ind_types.ml), then binomial.ml, pocklington.ml and
    card.ml, which ringtheory.ml needs. -/
private unsafe def cached {α : Type} [Inhabited α] (r : IO.Ref (Option α)) (name : String)
    (setup : Unit → IO (Except String α)) : α :=
  match unsafeIO (do
    match ← r.get with
    | some d => pure d
    | none => do
      Session.ensureDefine
      let _ ← Session.MATCH_CONV (HolCore.Kernel.mk_var "p" HolCore.Kernel.bool_ty)
      SessionLibrary.Binomial.ensureBinomial
      SessionLibrary.Pocklington.ensurePocklington
      SessionLibrary.Card.ensureCard
      match ← setup () with
      | .ok d => do r.set (some d); pure d
      | .error e => panic! s!"{name} failed: {e}") with
  | .ok d => d | _ => panic! s!"SessionLibrary.RingTheory: {name}"

/- The single bundle. -/

-- @@BUNDLES BEGIN
initialize theBasics : IO.Ref (Option HolLibrary.RingTheory.Basics) ← IO.mkRef none
unsafe def BBasics : HolLibrary.RingTheory.Basics :=
  cached theBasics "setupBasics" fun _ => do
    (HolLibrary.RingTheory.setupBasics (deps ())).run

initialize theNumbers : IO.Ref (Option HolLibrary.RingTheory.Numbers) ← IO.mkRef none
unsafe def BNumbers : HolLibrary.RingTheory.Numbers :=
  cached theNumbers "setupNumbers" fun _ => do
    let _ ← IO.mkRef BBasics.ring_tybij
    (HolLibrary.RingTheory.setupNumbers (deps ()) BBasics).run

initialize theSums : IO.Ref (Option HolLibrary.RingTheory.Sums) ← IO.mkRef none
unsafe def BSums : HolLibrary.RingTheory.Sums :=
  cached theSums "setupSums" fun _ => do
    let _ ← IO.mkRef BNumbers.ring_of_num
    (HolLibrary.RingTheory.setupSums (deps ()) BBasics BNumbers).run

initialize theProducts : IO.Ref (Option HolLibrary.RingTheory.Products) ← IO.mkRef none
unsafe def BProducts : HolLibrary.RingTheory.Products :=
  cached theProducts "setupProducts" fun _ => do
    let _ ← IO.mkRef BSums.ring_sum
    (HolLibrary.RingTheory.setupProducts (deps ()) BBasics BNumbers).run

initialize theDivides : IO.Ref (Option HolLibrary.RingTheory.Divides) ← IO.mkRef none
unsafe def BDivides : HolLibrary.RingTheory.Divides :=
  cached theDivides "setupDivides" fun _ => do
    let _ ← IO.mkRef BProducts.ring_product
    (HolLibrary.RingTheory.setupDivides (deps ()) BBasics BNumbers BSums BProducts).run

initialize theSubrings : IO.Ref (Option HolLibrary.RingTheory.Subrings) ← IO.mkRef none
unsafe def BSubrings : HolLibrary.RingTheory.Subrings :=
  cached theSubrings "setupSubrings" fun _ => do
    let _ ← IO.mkRef BDivides.ring_divides
    (HolLibrary.RingTheory.setupSubrings (deps ()) BBasics BNumbers BSums BProducts).run

initialize theIdeals : IO.Ref (Option HolLibrary.RingTheory.Ideals) ← IO.mkRef none
unsafe def BIdeals : HolLibrary.RingTheory.Ideals :=
  cached theIdeals "setupIdeals" fun _ => do
    let _ ← IO.mkRef BSubrings.subring_of
    (HolLibrary.RingTheory.setupIdeals (deps ()) BBasics BNumbers BSums BDivides BSubrings).run

initialize theDomains : IO.Ref (Option HolLibrary.RingTheory.Domains) ← IO.mkRef none
unsafe def BDomains : HolLibrary.RingTheory.Domains :=
  cached theDomains "setupDomains" fun _ => do
    let _ ← IO.mkRef BIdeals.ring_ideal
    (HolLibrary.RingTheory.setupDomains (deps ()) BBasics BNumbers BProducts BDivides BSubrings).run

initialize theRules : IO.Ref (Option HolLibrary.RingTheory.Rules) ← IO.mkRef none
unsafe def BRules : HolLibrary.RingTheory.Rules :=
  cached theRules "setupRules" fun _ => do
    let _ ← IO.mkRef BDomains.integral_domain
    (HolLibrary.RingTheory.setupRules (deps ()) BBasics BNumbers BDivides BDomains).run

initialize theHoms : IO.Ref (Option HolLibrary.RingTheory.Homs) ← IO.mkRef none
unsafe def BHoms : HolLibrary.RingTheory.Homs :=
  cached theHoms "setupHoms" fun _ => do
    let _ ← IO.mkRef BRules.RING_CARRIER_RULE
    (HolLibrary.RingTheory.setupHoms (deps ()) BBasics BNumbers BSums BProducts BDivides BSubrings BIdeals BDomains).run

initialize theIso : IO.Ref (Option HolLibrary.RingTheory.Iso) ← IO.mkRef none
unsafe def BIso : HolLibrary.RingTheory.Iso :=
  cached theIso "setupIso" fun _ => do
    let _ ← IO.mkRef BHoms.ring_homomorphism
    (HolLibrary.RingTheory.setupIso (deps ()) BBasics BHoms).run

initialize theKernels : IO.Ref (Option HolLibrary.RingTheory.Kernels) ← IO.mkRef none
unsafe def BKernels : HolLibrary.RingTheory.Kernels :=
  cached theKernels "setupKernels" fun _ => do
    let _ ← IO.mkRef BIso.isomorphic_ring
    (HolLibrary.RingTheory.setupKernels (deps ()) BBasics BDivides BSubrings BIdeals BDomains BHoms BIso).run

initialize theProdRings : IO.Ref (Option HolLibrary.RingTheory.ProdRings) ← IO.mkRef none
unsafe def BProdRings : HolLibrary.RingTheory.ProdRings :=
  cached theProdRings "setupProdRings" fun _ => do
    let _ ← IO.mkRef BKernels.ring_kernel
    (HolLibrary.RingTheory.setupProdRings (deps ()) BBasics BNumbers BSums BDivides BSubrings BIdeals BHoms BIso).run

initialize theLimits : IO.Ref (Option HolLibrary.RingTheory.Limits) ← IO.mkRef none
unsafe def BLimits : HolLibrary.RingTheory.Limits :=
  cached theLimits "setupLimits" fun _ => do
    let _ ← IO.mkRef BProdRings.prod_ring
    (HolLibrary.RingTheory.setupLimits (deps ()) BBasics BNumbers BHoms).run

initialize theRingRule : IO.Ref (Option HolLibrary.RingTheory.RingRule) ← IO.mkRef none
unsafe def BRingRule : HolLibrary.RingTheory.RingRule :=
  cached theRingRule "setupRingRule" fun _ => do
    let _ ← IO.mkRef BLimits.RING_DIRECT_LIMIT
    (HolLibrary.RingTheory.setupRingRule (deps ()) BBasics BNumbers BRules BHoms BIso BProdRings BLimits).run

initialize theCosets : IO.Ref (Option HolLibrary.RingTheory.Cosets) ← IO.mkRef none
unsafe def BCosets : HolLibrary.RingTheory.Cosets :=
  cached theCosets "setupCosets" fun _ => do
    let _ ← IO.mkRef BRingRule.RING_RULE
    (HolLibrary.RingTheory.setupCosets (deps ()) BBasics BNumbers BDivides BSubrings BIdeals BHoms BIso BKernels BProdRings BRingRule).run

initialize theQuotients : IO.Ref (Option HolLibrary.RingTheory.Quotients) ← IO.mkRef none
unsafe def BQuotients : HolLibrary.RingTheory.Quotients :=
  cached theQuotients "setupQuotients" fun _ => do
    let _ ← IO.mkRef BCosets.ring_coset
    (HolLibrary.RingTheory.setupQuotients (deps ()) BBasics BSubrings BIdeals BHoms BIso BKernels BCosets).run

initialize thePrimes : IO.Ref (Option HolLibrary.RingTheory.Primes) ← IO.mkRef none
unsafe def BPrimes : HolLibrary.RingTheory.Primes :=
  cached thePrimes "setupPrimes" fun _ => do
    let _ ← IO.mkRef BQuotients.quotient_ring
    (HolLibrary.RingTheory.setupPrimes (deps ()) BBasics BNumbers BProducts BDivides BDomains BHoms BKernels).run

initialize theFactorizations : IO.Ref (Option HolLibrary.RingTheory.Factorizations) ← IO.mkRef none
unsafe def BFactorizations : HolLibrary.RingTheory.Factorizations :=
  cached theFactorizations "setupFactorizations" fun _ => do
    let _ ← IO.mkRef BPrimes.ring_prime
    (HolLibrary.RingTheory.setupFactorizations (deps ()) BBasics BProducts BDivides BDomains BPrimes).run

initialize theSquarefree : IO.Ref (Option HolLibrary.RingTheory.Squarefree) ← IO.mkRef none
unsafe def BSquarefree : HolLibrary.RingTheory.Squarefree :=
  cached theSquarefree "setupSquarefree" fun _ => do
    let _ ← IO.mkRef BFactorizations.RING_DIVIDES_PRIMEFACTS_INJECTION
    (HolLibrary.RingTheory.setupSquarefree (deps ()) BBasics BNumbers BDivides BDomains BPrimes).run

initialize theLocalization : IO.Ref (Option HolLibrary.RingTheory.Localization) ← IO.mkRef none
unsafe def BLocalization : HolLibrary.RingTheory.Localization :=
  cached theLocalization "setupLocalization" fun _ => do
    let _ ← IO.mkRef BSquarefree.ring_squarefree
    (HolLibrary.RingTheory.setupLocalization (deps ()) BBasics BDivides BIdeals BDomains BHoms BIso BKernels BRingRule BSquarefree).run

initialize theSpecialIdeals : IO.Ref (Option HolLibrary.RingTheory.SpecialIdeals) ← IO.mkRef none
unsafe def BSpecialIdeals : HolLibrary.RingTheory.SpecialIdeals :=
  cached theSpecialIdeals "setupSpecialIdeals" fun _ => do
    let _ ← IO.mkRef BLocalization.ring_localequiv
    (HolLibrary.RingTheory.setupSpecialIdeals (deps ()) BBasics BNumbers BDivides BIdeals BDomains BHoms BIso BKernels BRingRule BCosets BQuotients BPrimes BSquarefree BLocalization).run

initialize theRadical : IO.Ref (Option HolLibrary.RingTheory.Radical) ← IO.mkRef none
unsafe def BRadical : HolLibrary.RingTheory.Radical :=
  cached theRadical "setupRadical" fun _ => do
    let _ ← IO.mkRef BSpecialIdeals.proper_ideal
    (HolLibrary.RingTheory.setupRadical (deps ()) BBasics BNumbers BSums BDivides BIdeals BDomains BRingRule BSquarefree BSpecialIdeals).run

initialize theUFDs : IO.Ref (Option HolLibrary.RingTheory.UFDs) ← IO.mkRef none
unsafe def BUFDs : HolLibrary.RingTheory.UFDs :=
  cached theUFDs "setupUFDs" fun _ => do
    let _ ← IO.mkRef BRadical.radical
    (HolLibrary.RingTheory.setupUFDs (deps ()) BBasics BProducts BDivides BIdeals BDomains BHoms BIso BKernels BRingRule BPrimes BFactorizations BSquarefree BLocalization BSpecialIdeals).run

initialize theEuclidean : IO.Ref (Option HolLibrary.RingTheory.Euclidean) ← IO.mkRef none
unsafe def BEuclidean : HolLibrary.RingTheory.Euclidean :=
  cached theEuclidean "setupEuclidean" fun _ => do
    let _ ← IO.mkRef BUFDs.UFD
    (HolLibrary.RingTheory.setupEuclidean (deps ()) BBasics BDivides BIdeals BDomains BHoms BIso BQuotients BSpecialIdeals).run

initialize theNoetherian : IO.Ref (Option HolLibrary.RingTheory.Noetherian) ← IO.mkRef none
unsafe def BNoetherian : HolLibrary.RingTheory.Noetherian :=
  cached theNoetherian "setupNoetherian" fun _ => do
    let _ ← IO.mkRef BEuclidean.euclidean_ring
    (HolLibrary.RingTheory.setupNoetherian (deps ()) BBasics BIdeals BHoms BIso BKernels BProdRings BQuotients BSpecialIdeals BUFDs).run

initialize theACCP : IO.Ref (Option HolLibrary.RingTheory.ACCP) ← IO.mkRef none
unsafe def BACCP : HolLibrary.RingTheory.ACCP :=
  cached theACCP "setupACCP" fun _ => do
    let _ ← IO.mkRef BNoetherian.NOETHERIAN_RING
    (HolLibrary.RingTheory.setupACCP (deps ()) BBasics BProducts BDivides BIdeals BDomains BPrimes BFactorizations BSpecialIdeals BUFDs BNoetherian).run

initialize theRingGcd : IO.Ref (Option HolLibrary.RingTheory.RingGcd) ← IO.mkRef none
unsafe def BRingGcd : HolLibrary.RingTheory.RingGcd :=
  cached theRingGcd "setupRingGcd" fun _ => do
    let _ ← IO.mkRef BACCP.RING_ACCP
    (HolLibrary.RingTheory.setupRingGcd (deps ()) BBasics BNumbers BDivides BDomains BUFDs).run

initialize theBezout : IO.Ref (Option HolLibrary.RingTheory.Bezout) ← IO.mkRef none
unsafe def BBezout : HolLibrary.RingTheory.Bezout :=
  cached theBezout "setupBezout" fun _ => do
    let _ ← IO.mkRef BRingGcd.ring_gcd
    (HolLibrary.RingTheory.setupBezout (deps ()) BBasics BDivides BIdeals BHoms BIso BRingRule BQuotients BPrimes BSquarefree BLocalization BSpecialIdeals BUFDs BNoetherian BACCP BRingGcd).run

initialize theGcdDomain : IO.Ref (Option HolLibrary.RingTheory.GcdDomain) ← IO.mkRef none
unsafe def BGcdDomain : HolLibrary.RingTheory.GcdDomain :=
  cached theGcdDomain "setupGcdDomain" fun _ => do
    let _ ← IO.mkRef BBezout.bezout_ring
    (HolLibrary.RingTheory.setupGcdDomain (deps ()) BBasics BNumbers BProducts BDivides BDomains BUFDs BRingGcd BBezout).run

initialize theSquarefreeUFD : IO.Ref (Option HolLibrary.RingTheory.SquarefreeUFD) ← IO.mkRef none
unsafe def BSquarefreeUFD : HolLibrary.RingTheory.SquarefreeUFD :=
  cached theSquarefreeUFD "setupSquarefreeUFD" fun _ => do
    let _ ← IO.mkRef BGcdDomain.RING_GCD_LMUL
    (HolLibrary.RingTheory.setupSquarefreeUFD (deps ()) BBasics BNumbers BProducts BDivides BDomains BRingRule BPrimes BSquarefree BUFDs BRingGcd BGcdDomain).run

initialize theBooleanRings : IO.Ref (Option HolLibrary.RingTheory.BooleanRings) ← IO.mkRef none
unsafe def BBooleanRings : HolLibrary.RingTheory.BooleanRings :=
  cached theBooleanRings "setupBooleanRings" fun _ => do
    let _ ← IO.mkRef BSquarefreeUFD.RING_SQUAREFREE_GCD
    (HolLibrary.RingTheory.setupBooleanRings (deps ()) BBasics BNumbers BDivides BSubrings BIdeals BDomains BHoms BIso BKernels BProdRings BRingRule BQuotients BPrimes BSquarefree BSpecialIdeals BRadical BBezout).run

initialize theLocalRings : IO.Ref (Option HolLibrary.RingTheory.LocalRings) ← IO.mkRef none
unsafe def BLocalRings : HolLibrary.RingTheory.LocalRings :=
  cached theLocalRings "setupLocalRings" fun _ => do
    let _ ← IO.mkRef BBooleanRings.boolean_ring
    (HolLibrary.RingTheory.setupLocalRings (deps ()) BBasics BIdeals BHoms BIso BQuotients BSquarefree BLocalization BSpecialIdeals BNoetherian).run

initialize theVonNeumann : IO.Ref (Option HolLibrary.RingTheory.VonNeumann) ← IO.mkRef none
unsafe def BVonNeumann : HolLibrary.RingTheory.VonNeumann :=
  cached theVonNeumann "setupVonNeumann" fun _ => do
    let _ ← IO.mkRef BLocalRings.local_ring
    (HolLibrary.RingTheory.setupVonNeumann (deps ()) BBasics BNumbers BDivides BIdeals BDomains BHoms BIso BProdRings BRingRule BQuotients BSquarefree BLocalization BSpecialIdeals BUFDs BBezout BBooleanRings).run

initialize theBoolRing : IO.Ref (Option HolLibrary.RingTheory.BoolRing) ← IO.mkRef none
unsafe def BBoolRing : HolLibrary.RingTheory.BoolRing :=
  cached theBoolRing "setupBoolRing" fun _ => do
    let _ ← IO.mkRef BVonNeumann.vnregular_ring
    (HolLibrary.RingTheory.setupBoolRing (deps ()) BBasics BDomains BHoms BIso BRingRule BBooleanRings).run

initialize theIntegerRing : IO.Ref (Option HolLibrary.RingTheory.IntegerRing) ← IO.mkRef none
unsafe def BIntegerRing : HolLibrary.RingTheory.IntegerRing :=
  cached theIntegerRing "setupIntegerRing" fun _ => do
    let _ ← IO.mkRef BBoolRing.bool_ring
    (HolLibrary.RingTheory.setupIntegerRing (deps ()) BBasics BNumbers BDivides BIdeals BDomains BHoms BKernels BCosets BUFDs BEuclidean BRingGcd BBezout).run

initialize theIntegerModRing : IO.Ref (Option HolLibrary.RingTheory.IntegerModRing) ← IO.mkRef none
unsafe def BIntegerModRing : HolLibrary.RingTheory.IntegerModRing :=
  cached theIntegerModRing "setupIntegerModRing" fun _ => do
    let _ ← IO.mkRef BIntegerRing.integer_ring
    (HolLibrary.RingTheory.setupIntegerModRing (deps ()) BBasics BNumbers BDivides BIdeals BDomains BHoms BIso BKernels BProdRings BCosets BQuotients BVonNeumann BIntegerRing).run

initialize theIntegerModConv : IO.Ref (Option HolLibrary.RingTheory.IntegerModConv) ← IO.mkRef none
unsafe def BIntegerModConv : HolLibrary.RingTheory.IntegerModConv :=
  cached theIntegerModConv "setupIntegerModConv" fun _ => do
    let _ ← IO.mkRef BIntegerModRing.integer_mod_ring
    (HolLibrary.RingTheory.setupIntegerModConv (deps ()) BBasics BDivides BIntegerModRing).run

initialize theRealRing : IO.Ref (Option HolLibrary.RingTheory.RealRing) ← IO.mkRef none
unsafe def BRealRing : HolLibrary.RingTheory.RealRing :=
  cached theRealRing "setupRealRing" fun _ => do
    let _ ← IO.mkRef BIntegerModConv.RING_INV_INTEGER_MOD_RING
    (HolLibrary.RingTheory.setupRealRing (deps ()) BBasics BNumbers BDivides BDomains).run

initialize theMonomials : IO.Ref (Option HolLibrary.RingTheory.Monomials) ← IO.mkRef none
unsafe def BMonomials : HolLibrary.RingTheory.Monomials :=
  cached theMonomials "setupMonomials" fun _ => do
    let _ ← IO.mkRef BRealRing.real_ring
    (HolLibrary.RingTheory.setupMonomials (deps ())).run

initialize thePowerSeries : IO.Ref (Option HolLibrary.RingTheory.PowerSeries) ← IO.mkRef none
unsafe def BPowerSeries : HolLibrary.RingTheory.PowerSeries :=
  cached thePowerSeries "setupPowerSeries" fun _ => do
    let _ ← IO.mkRef BMonomials.monomial_1
    (HolLibrary.RingTheory.setupPowerSeries (deps ()) BBasics BSums BRingRule BMonomials).run

initialize thePolyRings : IO.Ref (Option HolLibrary.RingTheory.PolyRings) ← IO.mkRef none
unsafe def BPolyRings : HolLibrary.RingTheory.PolyRings :=
  cached thePolyRings "setupPolyRings" fun _ => do
    let _ ← IO.mkRef BPowerSeries.ring_powerseries
    (HolLibrary.RingTheory.setupPolyRings (deps ()) BBasics BNumbers BSums BProducts BSubrings BHoms BMonomials BPowerSeries).run

initialize theHomExtend : IO.Ref (Option HolLibrary.RingTheory.HomExtend) ← IO.mkRef none
unsafe def BHomExtend : HolLibrary.RingTheory.HomExtend :=
  cached theHomExtend "setupHomExtend" fun _ => do
    let _ ← IO.mkRef BPolyRings.powser_ring
    (HolLibrary.RingTheory.setupHomExtend (deps ()) BBasics BNumbers BSums BProducts BSubrings BHoms BRingRule BMonomials BPowerSeries BPolyRings).run

initialize theNatIso : IO.Ref (Option HolLibrary.RingTheory.NatIso) ← IO.mkRef none
unsafe def BNatIso : HolLibrary.RingTheory.NatIso :=
  cached theNatIso "setupNatIso" fun _ => do
    let _ ← IO.mkRef BHomExtend.poly_extend
    (HolLibrary.RingTheory.setupNatIso (deps ()) BBasics BSums BProducts BSubrings BHoms BIso BRingRule BMonomials BPowerSeries BPolyRings BHomExtend).run

initialize theRenaming : IO.Ref (Option HolLibrary.RingTheory.Renaming) ← IO.mkRef none
unsafe def BRenaming : HolLibrary.RingTheory.Renaming :=
  cached theRenaming "setupRenaming" fun _ => do
    let _ ← IO.mkRef BNatIso.RING_ISOMORPHISM_POWSER_RING_TRIVIAL
    (HolLibrary.RingTheory.setupRenaming (deps ()) BBasics BSums BProducts BDivides BHoms BMonomials BPowerSeries BPolyRings BHomExtend BNatIso).run

initialize theMonomialOrders : IO.Ref (Option HolLibrary.RingTheory.MonomialOrders) ← IO.mkRef none
unsafe def BMonomialOrders : HolLibrary.RingTheory.MonomialOrders :=
  cached theMonomialOrders "setupMonomialOrders" fun _ => do
    let _ ← IO.mkRef BRenaming.poly_reindex
    (HolLibrary.RingTheory.setupMonomialOrders (deps ()) BMonomials).run

initialize theOneCoeff : IO.Ref (Option HolLibrary.RingTheory.OneCoeff) ← IO.mkRef none
unsafe def BOneCoeff : HolLibrary.RingTheory.OneCoeff :=
  cached theOneCoeff "setupOneCoeff" fun _ => do
    let _ ← IO.mkRef BMonomialOrders.POSET_MONOMIAL_DIVIDES
    (HolLibrary.RingTheory.setupOneCoeff (deps ()) BBasics BSums BSubrings BMonomials BPowerSeries BPolyRings).run

initialize theDegree : IO.Ref (Option HolLibrary.RingTheory.Degree) ← IO.mkRef none
unsafe def BDegree : HolLibrary.RingTheory.Degree :=
  cached theDegree "setupDegree" fun _ => do
    let _ ← IO.mkRef BOneCoeff.EXISTS_FUN_FROM_1
    (HolLibrary.RingTheory.setupDegree (deps ()) BBasics BSums BDivides BSubrings BDomains BHoms BKernels BRingRule BMonomials BPowerSeries BPolyRings BNatIso BMonomialOrders BOneCoeff).run

initialize theCardinalities : IO.Ref (Option HolLibrary.RingTheory.Cardinalities) ← IO.mkRef none
unsafe def BCardinalities : HolLibrary.RingTheory.Cardinalities :=
  cached theCardinalities "setupCardinalities" fun _ => do
    let _ ← IO.mkRef BDegree.poly_deg
    (HolLibrary.RingTheory.setupCardinalities (deps ()) BBasics BMonomials BPolyRings).run

initialize theEvaluation : IO.Ref (Option HolLibrary.RingTheory.Evaluation) ← IO.mkRef none
unsafe def BEvaluation : HolLibrary.RingTheory.Evaluation :=
  cached theEvaluation "setupEvaluation" fun _ => do
    let _ ← IO.mkRef BCardinalities.CARD_EQ_MONOMIALS_FINITE
    (HolLibrary.RingTheory.setupEvaluation (deps ()) BBasics BNumbers BSums BProducts BDivides BSubrings BHoms BKernels BMonomials BPowerSeries BPolyRings BHomExtend BRenaming BOneCoeff BDegree).run

initialize theComposing : IO.Ref (Option HolLibrary.RingTheory.Composing) ← IO.mkRef none
unsafe def BComposing : HolLibrary.RingTheory.Composing :=
  cached theComposing "setupComposing" fun _ => do
    let _ ← IO.mkRef BEvaluation.poly_evaluate
    (HolLibrary.RingTheory.setupComposing (deps ()) BBasics BSums BHoms BKernels BMonomials BPowerSeries BPolyRings BDegree).run

initialize theZerodivisors : IO.Ref (Option HolLibrary.RingTheory.Zerodivisors) ← IO.mkRef none
unsafe def BZerodivisors : HolLibrary.RingTheory.Zerodivisors :=
  cached theZerodivisors "setupZerodivisors" fun _ => do
    let _ ← IO.mkRef BComposing.RING_POWERSERIES_COMPOSE
    (HolLibrary.RingTheory.setupZerodivisors (deps ()) BBasics BSums BProducts BDivides BIdeals BDomains BHoms BIso BKernels BRingRule BCosets BQuotients BPrimes BSpecialIdeals BRadical BLocalRings BMonomials BPowerSeries BPolyRings BHomExtend BNatIso BRenaming BMonomialOrders BOneCoeff BDegree BEvaluation BComposing).run

initialize theXMinusA : IO.Ref (Option HolLibrary.RingTheory.XMinusA) ← IO.mkRef none
unsafe def BXMinusA : HolLibrary.RingTheory.XMinusA :=
  cached theXMinusA "setupXMinusA" fun _ => do
    let _ ← IO.mkRef BZerodivisors.INTEGRAL_DOMAIN_POWSER_RING
    (HolLibrary.RingTheory.setupXMinusA (deps ()) BBasics BDivides BDomains BRingRule BPowerSeries BPolyRings BDegree BEvaluation).run

initialize theDivision : IO.Ref (Option HolLibrary.RingTheory.Division) ← IO.mkRef none
unsafe def BDivision : HolLibrary.RingTheory.Division :=
  cached theDivision "setupDivision" fun _ => do
    let _ ← IO.mkRef BXMinusA.POLY_DEG_X_MINUS_A
    (HolLibrary.RingTheory.setupDivision (deps ()) BBasics BNumbers BSums BDivides BDomains BRules BRingRule BEuclidean BMonomials BPowerSeries BPolyRings BOneCoeff BDegree BEvaluation).run

initialize theHilbert : IO.Ref (Option HolLibrary.RingTheory.Hilbert) ← IO.mkRef none
unsafe def BHilbert : HolLibrary.RingTheory.Hilbert :=
  cached theHilbert "setupHilbert" fun _ => do
    let _ ← IO.mkRef BDivision.POLY_TOP_NONZERO
    (HolLibrary.RingTheory.setupHilbert (deps ()) BBasics BNumbers BSums BIdeals BRules BHoms BIso BRingRule BSpecialIdeals BNoetherian BMonomials BPowerSeries BPolyRings BNatIso BOneCoeff BDegree BEvaluation BDivision).run

initialize theMonic : IO.Ref (Option HolLibrary.RingTheory.Monic) ← IO.mkRef none
unsafe def BMonic : HolLibrary.RingTheory.Monic :=
  cached theMonic "setupMonic" fun _ => do
    let _ ← IO.mkRef BHilbert.NOETHERIAN_POLY_RING_1
    (HolLibrary.RingTheory.setupMonic (deps ()) BBasics BProducts BDivides BSubrings BDomains BPrimes BPowerSeries BPolyRings BOneCoeff BDegree BZerodivisors BDivision).run

initialize theReciprocal : IO.Ref (Option HolLibrary.RingTheory.Reciprocal) ← IO.mkRef none
unsafe def BReciprocal : HolLibrary.RingTheory.Reciprocal :=
  cached theReciprocal "setupReciprocal" fun _ => do
    let _ ← IO.mkRef BMonic.monic
    (HolLibrary.RingTheory.setupReciprocal (deps ()) BBasics BNumbers BSums BDivides BDomains BRingRule BPrimes BPowerSeries BPolyRings BOneCoeff BDegree BEvaluation BZerodivisors BDivision).run

initialize theDerivative : IO.Ref (Option HolLibrary.RingTheory.Derivative) ← IO.mkRef none
unsafe def BDerivative : HolLibrary.RingTheory.Derivative :=
  cached theDerivative "setupDerivative" fun _ => do
    let _ ← IO.mkRef BReciprocal.poly_recip
    (HolLibrary.RingTheory.setupDerivative (deps ()) BBasics BNumbers BSums BProducts BSubrings BDomains BHoms BRingRule BPowerSeries BPolyRings BOneCoeff BDegree BDivision).run

initialize theSeparable : IO.Ref (Option HolLibrary.RingTheory.Separable) ← IO.mkRef none
unsafe def BSeparable : HolLibrary.RingTheory.Separable :=
  cached theSeparable "setupSeparable" fun _ => do
    let _ ← IO.mkRef BDerivative.poly_deriv
    (HolLibrary.RingTheory.setupSeparable (deps ()) BBasics BNumbers BDivides BDomains BRingRule BPrimes BSquarefree BUFDs BACCP BGcdDomain BPowerSeries BPolyRings BDegree BEvaluation BZerodivisors BXMinusA BDivision BDerivative).run

initialize theGaussA : IO.Ref (Option HolLibrary.RingTheory.GaussA) ← IO.mkRef none
unsafe def BGaussA : HolLibrary.RingTheory.GaussA :=
  cached theGaussA "setupGaussA" fun _ => do
    let _ ← IO.mkRef BSeparable.POLY_NONCONSTANT_IRREDUCIBLE_IMP_SEPARABLE
    (HolLibrary.RingTheory.setupGaussA (deps ()) BBasics BDivides BDomains BHoms BPrimes BSpecialIdeals BUFDs BACCP BMonomials BPowerSeries BPolyRings BNatIso BOneCoeff BDegree BZerodivisors BDivision).run

initialize theGaussB : IO.Ref (Option HolLibrary.RingTheory.GaussB) ← IO.mkRef none
unsafe def BGaussB : HolLibrary.RingTheory.GaussB :=
  cached theGaussB "setupGaussB" fun _ => do
    let _ ← IO.mkRef BGaussA.POLY_PRIMITIVE_CONST_CANCEL
    (HolLibrary.RingTheory.setupGaussB (deps ()) BBasics BNumbers BDivides BIdeals BDomains BIso BRingRule BSpecialIdeals BUFDs BPowerSeries BPolyRings BNatIso BRenaming BOneCoeff BDegree BZerodivisors BDivision BGaussA).run

initialize theGaussC : IO.Ref (Option HolLibrary.RingTheory.GaussC) ← IO.mkRef none
unsafe def BGaussC : HolLibrary.RingTheory.GaussC :=
  cached theGaussC "setupGaussC" fun _ => do
    let _ ← IO.mkRef BGaussB.UFD_POLY_RING
    (HolLibrary.RingTheory.setupGaussC (deps ()) BBasics BDomains BHoms BRingRule BSquarefree BLocalization BPowerSeries BPolyRings BComposing).run

initialize theGaussD : IO.Ref (Option HolLibrary.RingTheory.GaussD) ← IO.mkRef none
unsafe def BGaussD : HolLibrary.RingTheory.GaussD :=
  cached theGaussD "setupGaussD" fun _ => do
    let _ ← IO.mkRef BGaussC.POLY_CLEAR_DENOMINATORS
    (HolLibrary.RingTheory.setupGaussD (deps ()) BBasics BDivides BDomains BHoms BKernels BRingRule BPrimes BLocalization BUFDs BPowerSeries BPolyRings BRenaming BDegree BComposing BZerodivisors BGaussB BGaussC).run

initialize theEisenstein : IO.Ref (Option HolLibrary.RingTheory.Eisenstein) ← IO.mkRef none
unsafe def BEisenstein : HolLibrary.RingTheory.Eisenstein :=
  cached theEisenstein "setupEisenstein" fun _ => do
    let _ ← IO.mkRef BGaussD.IRREDUCIBLE_PRIMITIVE_POLY_FRACTION_RING
    (HolLibrary.RingTheory.setupEisenstein (deps ()) BBasics BNumbers BDivides BIdeals BDomains BHoms BKernels BCosets BQuotients BPrimes BLocalization BSpecialIdeals BUFDs BMonomials BPowerSeries BPolyRings BOneCoeff BDegree BEvaluation BComposing BZerodivisors BDivision BGaussA BGaussD).run

initialize theRingOrder : IO.Ref (Option HolLibrary.RingTheory.RingOrder) ← IO.mkRef none
unsafe def BRingOrder : HolLibrary.RingTheory.RingOrder :=
  cached theRingOrder "setupRingOrder" fun _ => do
    let _ ← IO.mkRef BEisenstein.EISENSTEIN_IRREDUCIBILITY_GEN
    (HolLibrary.RingTheory.setupRingOrder (deps ()) BBasics BNumbers).run

initialize theFrobenius : IO.Ref (Option HolLibrary.RingTheory.Frobenius) ← IO.mkRef none
unsafe def BFrobenius : HolLibrary.RingTheory.Frobenius :=
  cached theFrobenius "setupFrobenius" fun _ => do
    let _ ← IO.mkRef BRingOrder.RING_ORDER_DIVIDES
    (HolLibrary.RingTheory.setupFrobenius (deps ()) BBasics BNumbers BSums BDivides BSubrings BDomains BHoms BKernels BCosets BPowerSeries BPolyRings BDegree BEvaluation BXMinusA).run

initialize theIntegralDomainRule : IO.Ref (Option HolLibrary.RingTheory.IntegralDomainRule) ← IO.mkRef none
unsafe def BIntegralDomainRule : HolLibrary.RingTheory.IntegralDomainRule :=
  cached theIntegralDomainRule "setupIntegralDomainRule" fun _ => do
    let _ ← IO.mkRef BFrobenius.RING_ENDOMORPHISM_FROBENIUS
    (HolLibrary.RingTheory.setupIntegralDomainRule (deps ()) BBasics BDivides BDomains BRules BHoms BIso BKernels BLimits BPolyRings BDegree BCardinalities).run

initialize theRingPullDiv : IO.Ref (Option HolLibrary.RingTheory.RingPullDiv) ← IO.mkRef none
unsafe def BRingPullDiv : HolLibrary.RingTheory.RingPullDiv :=
  cached theRingPullDiv "setupRingPullDiv" fun _ => do
    let _ ← IO.mkRef BIntegralDomainRule.INTEGRAL_DOMAIN_RULE
    (HolLibrary.RingTheory.setupRingPullDiv (deps ()) BNumbers BDivides BDomains BRules BIntegralDomainRule).run

-- @@BUNDLES END

-- @@EXPORTS BEGIN
-- Basics
unsafe def ring_tybij : thm := BBasics.ring_tybij
unsafe def ring_carrier : thm := BBasics.ring_carrier
unsafe def ring_0 : thm := BBasics.ring_0
unsafe def ring_1 : thm := BBasics.ring_1
unsafe def ring_neg : thm := BBasics.ring_neg
unsafe def ring_add : thm := BBasics.ring_add
unsafe def ring_mul : thm := BBasics.ring_mul
unsafe def ring_sub : thm := BBasics.ring_sub
unsafe def RINGS_EQ : thm := BBasics.RINGS_EQ
unsafe def RING_PROPERTIES : thm := BBasics.RING_PROPERTIES
unsafe def RING_0 : thm := BBasics.RING_0
unsafe def RING_1 : thm := BBasics.RING_1
unsafe def RING_NEG : thm := BBasics.RING_NEG
unsafe def RING_ADD : thm := BBasics.RING_ADD
unsafe def RING_SUB : thm := BBasics.RING_SUB
unsafe def RING_MUL : thm := BBasics.RING_MUL
unsafe def RING_ADD_SYM : thm := BBasics.RING_ADD_SYM
unsafe def RING_MUL_SYM : thm := BBasics.RING_MUL_SYM
unsafe def RING_ADD_ASSOC : thm := BBasics.RING_ADD_ASSOC
unsafe def RING_MUL_ASSOC : thm := BBasics.RING_MUL_ASSOC
unsafe def RING_ADD_LDISTRIB : thm := BBasics.RING_ADD_LDISTRIB
unsafe def RING_ADD_RDISTRIB : thm := BBasics.RING_ADD_RDISTRIB
unsafe def RING_ADD_LZERO : thm := BBasics.RING_ADD_LZERO
unsafe def RING_ADD_RZERO : thm := BBasics.RING_ADD_RZERO
unsafe def RING_MUL_LID : thm := BBasics.RING_MUL_LID
unsafe def RING_MUL_RID : thm := BBasics.RING_MUL_RID
unsafe def RING_ADD_LNEG : thm := BBasics.RING_ADD_LNEG
unsafe def RING_ADD_RNEG : thm := BBasics.RING_ADD_RNEG
unsafe def RING_ADD_AC : thm := BBasics.RING_ADD_AC
unsafe def RING_MUL_AC : thm := BBasics.RING_MUL_AC
unsafe def RING_ADD_LCANCEL : thm := BBasics.RING_ADD_LCANCEL
unsafe def RING_ADD_RCANCEL : thm := BBasics.RING_ADD_RCANCEL
unsafe def RING_ADD_LCANCEL_IMP : thm := BBasics.RING_ADD_LCANCEL_IMP
unsafe def RING_ADD_RCANCEL_IMP : thm := BBasics.RING_ADD_RCANCEL_IMP
unsafe def RING_ADD_EQ_RIGHT : thm := BBasics.RING_ADD_EQ_RIGHT
unsafe def RING_ADD_EQ_LEFT : thm := BBasics.RING_ADD_EQ_LEFT
unsafe def RING_LZERO_UNIQUE : thm := BBasics.RING_LZERO_UNIQUE
unsafe def RING_RZERO_UNIQUE : thm := BBasics.RING_RZERO_UNIQUE
unsafe def RING_ADD_EQ_0 : thm := BBasics.RING_ADD_EQ_0
unsafe def RING_LNEG_UNIQUE : thm := BBasics.RING_LNEG_UNIQUE
unsafe def RING_RNEG_UNIQUE : thm := BBasics.RING_RNEG_UNIQUE
unsafe def RING_NEG_NEG : thm := BBasics.RING_NEG_NEG
unsafe def RING_NEG_EQ_SWAP : thm := BBasics.RING_NEG_EQ_SWAP
unsafe def RING_NEG_EQ : thm := BBasics.RING_NEG_EQ
unsafe def RING_NEG_0 : thm := BBasics.RING_NEG_0
unsafe def RING_NEG_EQ_0 : thm := BBasics.RING_NEG_EQ_0
unsafe def RING_MUL_LZERO : thm := BBasics.RING_MUL_LZERO
unsafe def RING_MUL_RZERO : thm := BBasics.RING_MUL_RZERO
unsafe def RING_MUL_LNEG : thm := BBasics.RING_MUL_LNEG
unsafe def RING_MUL_RNEG : thm := BBasics.RING_MUL_RNEG
unsafe def RING_NEG_ADD : thm := BBasics.RING_NEG_ADD
unsafe def RING_SUB_REFL : thm := BBasics.RING_SUB_REFL
unsafe def RING_SUB_LZERO : thm := BBasics.RING_SUB_LZERO
unsafe def RING_SUB_RZERO : thm := BBasics.RING_SUB_RZERO
unsafe def RING_SUB_EQ_0 : thm := BBasics.RING_SUB_EQ_0
unsafe def RING_SUB_LDISTRIB : thm := BBasics.RING_SUB_LDISTRIB
unsafe def RING_SUB_RDISTRIB : thm := BBasics.RING_SUB_RDISTRIB
unsafe def RING_EQ_SUB_LADD : thm := BBasics.RING_EQ_SUB_LADD
unsafe def RING_EQ_SUB_RADD : thm := BBasics.RING_EQ_SUB_RADD
unsafe def RING_SUB_TELESCOPE : thm := BBasics.RING_SUB_TELESCOPE
unsafe def RING_NEG_SUB : thm := BBasics.RING_NEG_SUB
unsafe def RING_CARRIER_NONEMPTY : thm := BBasics.RING_CARRIER_NONEMPTY
unsafe def trivial_ring : thm := BBasics.trivial_ring
unsafe def TRIVIAL_IMP_FINITE_RING : thm := BBasics.TRIVIAL_IMP_FINITE_RING
unsafe def TRIVIAL_RING_SUBSET : thm := BBasics.TRIVIAL_RING_SUBSET
unsafe def TRIVIAL_RING : thm := BBasics.TRIVIAL_RING
unsafe def TRIVIAL_RING_ALT : thm := BBasics.TRIVIAL_RING_ALT
unsafe def TRIVIAL_RING_10 : thm := BBasics.TRIVIAL_RING_10
unsafe def RING_CARRIER_HAS_SIZE_1 : thm := BBasics.RING_CARRIER_HAS_SIZE_1
unsafe def TRIVIAL_RING_HAS_SIZE_1 : thm := BBasics.TRIVIAL_RING_HAS_SIZE_1
unsafe def RING_CARRIER_HAS_SIZE_2 : thm := BBasics.RING_CARRIER_HAS_SIZE_2
unsafe def singleton_ring : thm := BBasics.singleton_ring
unsafe def SINGLETON_RING : thm := BBasics.SINGLETON_RING
unsafe def TRIVIAL_RING_SINGLETON_RING : thm := BBasics.TRIVIAL_RING_SINGLETON_RING
unsafe def FINITE_SINGLETON_RING : thm := BBasics.FINITE_SINGLETON_RING

-- Numbers
unsafe def ring_of_num : thm := BNumbers.ring_of_num
unsafe def ring_of_int : thm := BNumbers.ring_of_int
unsafe def RING_OF_NUM : thm := BNumbers.RING_OF_NUM
unsafe def RING_OF_INT : thm := BNumbers.RING_OF_INT
unsafe def RING_OF_INT_OF_NUM : thm := BNumbers.RING_OF_INT_OF_NUM
unsafe def RING_OF_NUM_0 : thm := BNumbers.RING_OF_NUM_0
unsafe def RING_OF_NUM_1 : thm := BNumbers.RING_OF_NUM_1
unsafe def RING_OF_NUM_ADD : thm := BNumbers.RING_OF_NUM_ADD
unsafe def RING_OF_NUM_MUL : thm := BNumbers.RING_OF_NUM_MUL
unsafe def RING_OF_INT_0 : thm := BNumbers.RING_OF_INT_0
unsafe def RING_OF_INT_1 : thm := BNumbers.RING_OF_INT_1
unsafe def RING_OF_INT_CASES : thm := BNumbers.RING_OF_INT_CASES
unsafe def RING_OF_INT_NEG : thm := BNumbers.RING_OF_INT_NEG
unsafe def RING_OF_INT_ADD : thm := BNumbers.RING_OF_INT_ADD
unsafe def RING_OF_INT_MUL : thm := BNumbers.RING_OF_INT_MUL
unsafe def RING_OF_INT_SUB : thm := BNumbers.RING_OF_INT_SUB
unsafe def RING_OF_NUM_EQ_0 : thm := BNumbers.RING_OF_NUM_EQ_0
unsafe def RING_CHAR_EQ_0 : thm := BNumbers.RING_CHAR_EQ_0
unsafe def RING_CHAR_EQ_1 : thm := BNumbers.RING_CHAR_EQ_1
unsafe def RING_OF_INT_EQ_0 : thm := BNumbers.RING_OF_INT_EQ_0
unsafe def RING_OF_INT_EQ : thm := BNumbers.RING_OF_INT_EQ
unsafe def RING_OF_NUM_EQ : thm := BNumbers.RING_OF_NUM_EQ
unsafe def RING_OF_INT_REM : thm := BNumbers.RING_OF_INT_REM
unsafe def RING_OF_NUM_MOD : thm := BNumbers.RING_OF_NUM_MOD
unsafe def RING_OF_NUM_CHAR : thm := BNumbers.RING_OF_NUM_CHAR
unsafe def RING_CHAR_INFINITE : thm := BNumbers.RING_CHAR_INFINITE
unsafe def RING_CHAR_FINITE : thm := BNumbers.RING_CHAR_FINITE
unsafe def RING_CHAR_UNIQUE : thm := BNumbers.RING_CHAR_UNIQUE
unsafe def ring_pow : thm := BNumbers.ring_pow
unsafe def RING_POW : thm := BNumbers.RING_POW
unsafe def RING_POW_ZERO : thm := BNumbers.RING_POW_ZERO
unsafe def RING_POW_0 : thm := BNumbers.RING_POW_0
unsafe def RING_POW_1 : thm := BNumbers.RING_POW_1
unsafe def RING_POW_2 : thm := BNumbers.RING_POW_2
unsafe def RING_POW_ONE : thm := BNumbers.RING_POW_ONE
unsafe def RING_POW_ADD : thm := BNumbers.RING_POW_ADD
unsafe def RING_POW_MUL : thm := BNumbers.RING_POW_MUL
unsafe def RING_POW_POW : thm := BNumbers.RING_POW_POW
unsafe def RING_MUL_POW : thm := BNumbers.RING_MUL_POW
unsafe def RING_OF_NUM_EXP : thm := BNumbers.RING_OF_NUM_EXP
unsafe def RING_OF_INT_POW : thm := BNumbers.RING_OF_INT_POW
unsafe def RING_POW_NEG : thm := BNumbers.RING_POW_NEG
unsafe def RING_POW_IDEMPOTENT : thm := BNumbers.RING_POW_IDEMPOTENT
unsafe def RING_OF_NUM_CLAUSES : thm := BNumbers.RING_OF_NUM_CLAUSES
unsafe def RING_OF_INT_CLAUSES : thm := BNumbers.RING_OF_INT_CLAUSES

-- Sums
unsafe def ring_sum : thm := BSums.ring_sum
unsafe def NEUTRAL_RING_ADD : thm := BSums.NEUTRAL_RING_ADD
unsafe def MONOIDAL_RING_ADD : thm := BSums.MONOIDAL_RING_ADD
unsafe def RING_SUM : thm := BSums.RING_SUM
unsafe def RING_SUM_RESTRICT : thm := BSums.RING_SUM_RESTRICT
unsafe def RING_SUM_SUPPORT : thm := BSums.RING_SUM_SUPPORT
unsafe def RING_SUM_TRIVIAL : thm := BSums.RING_SUM_TRIVIAL
unsafe def RING_SUM_CLAUSES : thm := BSums.RING_SUM_CLAUSES
unsafe def RING_SUM_SING : thm := BSums.RING_SUM_SING
unsafe def RING_SUM_CLAUSES_NUMSEG_ALT : thm := BSums.RING_SUM_CLAUSES_NUMSEG_ALT
unsafe def RING_SUM_CLAUSES_NUMSEG : thm := BSums.RING_SUM_CLAUSES_NUMSEG
unsafe def RING_SUM_CLAUSES_LEFT : thm := BSums.RING_SUM_CLAUSES_LEFT
unsafe def RING_SUM_CLAUSES_RIGHT : thm := BSums.RING_SUM_CLAUSES_RIGHT
unsafe def RING_SUM_UNION : thm := BSums.RING_SUM_UNION
unsafe def RING_SUM_DIFF : thm := BSums.RING_SUM_DIFF
unsafe def RING_SUM_INCL_EXCL : thm := BSums.RING_SUM_INCL_EXCL
unsafe def RING_SUM_CLOSED : thm := BSums.RING_SUM_CLOSED
unsafe def RING_SUM_RELATED : thm := BSums.RING_SUM_RELATED
unsafe def RING_SUM_EQ_0 : thm := BSums.RING_SUM_EQ_0
unsafe def RING_SUM_0 : thm := BSums.RING_SUM_0
unsafe def RING_SUM_DELETE : thm := BSums.RING_SUM_DELETE
unsafe def RING_SUM_NEG : thm := BSums.RING_SUM_NEG
unsafe def RING_SUM_ADD : thm := BSums.RING_SUM_ADD
unsafe def RING_SUM_SUB : thm := BSums.RING_SUM_SUB
unsafe def RING_SUM_EQ : thm := BSums.RING_SUM_EQ
unsafe def RING_SUM_DELTA : thm := BSums.RING_SUM_DELTA
unsafe def RING_SUM_LMUL : thm := BSums.RING_SUM_LMUL
unsafe def RING_SUM_RMUL : thm := BSums.RING_SUM_RMUL
unsafe def RING_SUM_SWAP : thm := BSums.RING_SUM_SWAP
unsafe def RING_SUM_REFLECT : thm := BSums.RING_SUM_REFLECT
unsafe def RING_SUM_SUM_PRODUCT : thm := BSums.RING_SUM_SUM_PRODUCT
unsafe def RING_SUM_SUPERSET : thm := BSums.RING_SUM_SUPERSET
unsafe def RING_SUM_RESTRICT_SET : thm := BSums.RING_SUM_RESTRICT_SET
unsafe def RING_SUM_CASES : thm := BSums.RING_SUM_CASES
unsafe def RING_SUM_IMAGE : thm := BSums.RING_SUM_IMAGE
unsafe def RING_SUM_EQ_GENERAL_INVERSES : thm := BSums.RING_SUM_EQ_GENERAL_INVERSES
unsafe def RING_SUM_OFFSET : thm := BSums.RING_SUM_OFFSET
unsafe def RING_SUM_CONST : thm := BSums.RING_SUM_CONST
unsafe def RING_SUM_IMAGE_GEN : thm := BSums.RING_SUM_IMAGE_GEN
unsafe def RING_BINOMIAL_THEOREM : thm := BSums.RING_BINOMIAL_THEOREM
unsafe def RING_BINOMIAL_FRESHMAN : thm := BSums.RING_BINOMIAL_FRESHMAN
unsafe def RING_SUM_DIFFS : thm := BSums.RING_SUM_DIFFS
unsafe def RING_SUM_DIFFS_ALT : thm := BSums.RING_SUM_DIFFS_ALT
unsafe def RING_GEOM_SERIES_GEN : thm := BSums.RING_GEOM_SERIES_GEN
unsafe def RING_GEOM_SERIES : thm := BSums.RING_GEOM_SERIES

-- Products
unsafe def ring_product : thm := BProducts.ring_product
unsafe def NEUTRAL_RING_MUL : thm := BProducts.NEUTRAL_RING_MUL
unsafe def MONOIDAL_RING_MUL : thm := BProducts.MONOIDAL_RING_MUL
unsafe def RING_PRODUCT : thm := BProducts.RING_PRODUCT
unsafe def RING_PRODUCT_RESTRICT : thm := BProducts.RING_PRODUCT_RESTRICT
unsafe def RING_PRODUCT_SUPPORT : thm := BProducts.RING_PRODUCT_SUPPORT
unsafe def RING_PRODUCT_TRIVIAL : thm := BProducts.RING_PRODUCT_TRIVIAL
unsafe def RING_PRODUCT_CLAUSES : thm := BProducts.RING_PRODUCT_CLAUSES
unsafe def RING_PRODUCT_SING : thm := BProducts.RING_PRODUCT_SING
unsafe def RING_PRODUCT_CLAUSES_NUMSEG_ALT : thm := BProducts.RING_PRODUCT_CLAUSES_NUMSEG_ALT
unsafe def RING_PRODUCT_CLAUSES_NUMSEG : thm := BProducts.RING_PRODUCT_CLAUSES_NUMSEG
unsafe def RING_PRODUCT_CLAUSES_LEFT : thm := BProducts.RING_PRODUCT_CLAUSES_LEFT
unsafe def RING_PRODUCT_UNION : thm := BProducts.RING_PRODUCT_UNION
unsafe def RING_PRODUCT_INCL_EXCL : thm := BProducts.RING_PRODUCT_INCL_EXCL
unsafe def RING_PRODUCT_CLOSED : thm := BProducts.RING_PRODUCT_CLOSED
unsafe def RING_PRODUCT_RELATED : thm := BProducts.RING_PRODUCT_RELATED
unsafe def RING_PRODUCT_EQ_1 : thm := BProducts.RING_PRODUCT_EQ_1
unsafe def RING_PRODUCT_1 : thm := BProducts.RING_PRODUCT_1
unsafe def RING_PRODUCT_0 : thm := BProducts.RING_PRODUCT_0
unsafe def RING_PRODUCT_MUL : thm := BProducts.RING_PRODUCT_MUL
unsafe def RING_PRODUCT_EQ : thm := BProducts.RING_PRODUCT_EQ
unsafe def RING_PRODUCT_DELTA : thm := BProducts.RING_PRODUCT_DELTA
unsafe def RING_PRODUCT_CONST : thm := BProducts.RING_PRODUCT_CONST
unsafe def RING_PRODUCT_LMUL : thm := BProducts.RING_PRODUCT_LMUL
unsafe def RING_PRODUCT_SWAP : thm := BProducts.RING_PRODUCT_SWAP
unsafe def RING_PRODUCT_REFLECT : thm := BProducts.RING_PRODUCT_REFLECT
unsafe def RING_PRODUCT_SUPERSET : thm := BProducts.RING_PRODUCT_SUPERSET
unsafe def RING_PRODUCT_RESTRICT_SET : thm := BProducts.RING_PRODUCT_RESTRICT_SET
unsafe def RING_PRODUCT_CASES : thm := BProducts.RING_PRODUCT_CASES
unsafe def RING_PRODUCT_IMAGE : thm := BProducts.RING_PRODUCT_IMAGE
unsafe def RING_PRODUCT_EQ_GENERAL_INVERSES : thm := BProducts.RING_PRODUCT_EQ_GENERAL_INVERSES
unsafe def RING_PRODUCT_OFFSET : thm := BProducts.RING_PRODUCT_OFFSET
unsafe def RING_PRODUCT_IMAGE_GEN : thm := BProducts.RING_PRODUCT_IMAGE_GEN
unsafe def RING_PRODUCT_NSUM : thm := BProducts.RING_PRODUCT_NSUM

-- Divides
unsafe def ring_divides : thm := BDivides.ring_divides
unsafe def ring_zerodivisor : thm := BDivides.ring_zerodivisor
unsafe def ring_regular : thm := BDivides.ring_regular
unsafe def ring_nilpotent : thm := BDivides.ring_nilpotent
unsafe def ring_unit : thm := BDivides.ring_unit
unsafe def ring_associates : thm := BDivides.ring_associates
unsafe def ring_coprime : thm := BDivides.ring_coprime
unsafe def ring_inv : thm := BDivides.ring_inv
unsafe def ring_div : thm := BDivides.ring_div
unsafe def RING_DIVIDES_ALT : thm := BDivides.RING_DIVIDES_ALT
unsafe def RING_DIVIDES_IN_CARRIER : thm := BDivides.RING_DIVIDES_IN_CARRIER
unsafe def RING_ZERODIVISOR_IN_CARRIER : thm := BDivides.RING_ZERODIVISOR_IN_CARRIER
unsafe def RING_REGULAR_IN_CARRIER : thm := BDivides.RING_REGULAR_IN_CARRIER
unsafe def RING_NILPOTENT_IN_CARRIER : thm := BDivides.RING_NILPOTENT_IN_CARRIER
unsafe def RING_UNIT_IN_CARRIER : thm := BDivides.RING_UNIT_IN_CARRIER
unsafe def RING_ASSOCIATES_IN_CARRIER : thm := BDivides.RING_ASSOCIATES_IN_CARRIER
unsafe def RING_COPRIME_IN_CARRIER : thm := BDivides.RING_COPRIME_IN_CARRIER
unsafe def RING_INV : thm := BDivides.RING_INV
unsafe def RING_MUL_RINV : thm := BDivides.RING_MUL_RINV
unsafe def RING_MUL_LINV : thm := BDivides.RING_MUL_LINV
unsafe def RING_DIV : thm := BDivides.RING_DIV
unsafe def RING_CLAUSES : thm := BDivides.RING_CLAUSES
unsafe def RING_RINV_UNIQUE : thm := BDivides.RING_RINV_UNIQUE
unsafe def RING_LINV_UNIQUE : thm := BDivides.RING_LINV_UNIQUE
unsafe def RING_INV_1 : thm := BDivides.RING_INV_1
unsafe def RING_DIV_1 : thm := BDivides.RING_DIV_1
unsafe def RING_1_DIV : thm := BDivides.RING_1_DIV
unsafe def RING_INV_ZERO : thm := BDivides.RING_INV_ZERO
unsafe def RING_INV_MUL : thm := BDivides.RING_INV_MUL
unsafe def RING_INV_POW : thm := BDivides.RING_INV_POW
unsafe def RING_POW_INV : thm := BDivides.RING_POW_INV
unsafe def RING_INV_INV : thm := BDivides.RING_INV_INV
unsafe def RING_MUL_RINV_EQ : thm := BDivides.RING_MUL_RINV_EQ
unsafe def RING_MUL_LINV_EQ : thm := BDivides.RING_MUL_LINV_EQ
unsafe def RING_UNIT_DIVIDES : thm := BDivides.RING_UNIT_DIVIDES
unsafe def RING_UNIT_0 : thm := BDivides.RING_UNIT_0
unsafe def RING_INV_0 : thm := BDivides.RING_INV_0
unsafe def RING_UNIT_1 : thm := BDivides.RING_UNIT_1
unsafe def RING_UNIT_NEG : thm := BDivides.RING_UNIT_NEG
unsafe def RING_UNIT_NEG_EQ : thm := BDivides.RING_UNIT_NEG_EQ
unsafe def RING_UNIT_INV : thm := BDivides.RING_UNIT_INV
unsafe def RING_UNIT_MUL : thm := BDivides.RING_UNIT_MUL
unsafe def RING_UNIT_DIV : thm := BDivides.RING_UNIT_DIV
unsafe def RING_MUL_IMP_UNITS : thm := BDivides.RING_MUL_IMP_UNITS
unsafe def RING_UNIT_MUL_EQ : thm := BDivides.RING_UNIT_MUL_EQ
unsafe def RING_UNIT_POW : thm := BDivides.RING_UNIT_POW
unsafe def RING_UNIT_POW_EQ : thm := BDivides.RING_UNIT_POW_EQ
unsafe def RING_UNIT_DIVIDES_ANY : thm := BDivides.RING_UNIT_DIVIDES_ANY
unsafe def RING_UNIT_DIVISOR : thm := BDivides.RING_UNIT_DIVISOR
unsafe def RING_UNIT_PRODUCT : thm := BDivides.RING_UNIT_PRODUCT
unsafe def RING_MUL_LCANCEL : thm := BDivides.RING_MUL_LCANCEL
unsafe def RING_MUL_RCANCEL : thm := BDivides.RING_MUL_RCANCEL
unsafe def RING_DIVIDES_REFL : thm := BDivides.RING_DIVIDES_REFL
unsafe def RING_DIVIDES_TRANS : thm := BDivides.RING_DIVIDES_TRANS
unsafe def RING_DIVIDES_MORE_DIVISORS : thm := BDivides.RING_DIVIDES_MORE_DIVISORS
unsafe def RING_DIVIDES_ANTISYM : thm := BDivides.RING_DIVIDES_ANTISYM
unsafe def RING_DIVIDES_ASSOCIATES : thm := BDivides.RING_DIVIDES_ASSOCIATES
unsafe def RING_DIVIDES_0 : thm := BDivides.RING_DIVIDES_0
unsafe def RING_DIVIDES_ZERO : thm := BDivides.RING_DIVIDES_ZERO
unsafe def RING_DIVIDES_1 : thm := BDivides.RING_DIVIDES_1
unsafe def RING_DIVIDES_ONE : thm := BDivides.RING_DIVIDES_ONE
unsafe def RING_UNIT_DIVIDES_ALL : thm := BDivides.RING_UNIT_DIVIDES_ALL
unsafe def RING_DIVIDES_ADD : thm := BDivides.RING_DIVIDES_ADD
unsafe def RING_DIVIDES_SUB : thm := BDivides.RING_DIVIDES_SUB
unsafe def RING_DIVIDES_LNEG : thm := BDivides.RING_DIVIDES_LNEG
unsafe def RING_DIVIDES_NEG : thm := BDivides.RING_DIVIDES_NEG
unsafe def RING_DIVIDES_NEG_EQ : thm := BDivides.RING_DIVIDES_NEG_EQ
unsafe def RING_DIVIDES_RMUL : thm := BDivides.RING_DIVIDES_RMUL
unsafe def RING_DIVIDES_LMUL : thm := BDivides.RING_DIVIDES_LMUL
unsafe def RING_DIVIDES_LMUL_REV : thm := BDivides.RING_DIVIDES_LMUL_REV
unsafe def RING_DIVIDES_RMUL_REV : thm := BDivides.RING_DIVIDES_RMUL_REV
unsafe def RING_DIVIDES_MUL2 : thm := BDivides.RING_DIVIDES_MUL2
unsafe def RING_DIVIDES_LMUL2 : thm := BDivides.RING_DIVIDES_LMUL2
unsafe def RING_DIVIDES_RMUL2 : thm := BDivides.RING_DIVIDES_RMUL2
unsafe def RING_DIVIDES_SUB_POW : thm := BDivides.RING_DIVIDES_SUB_POW
unsafe def RING_DIVIDES_PRODUCTS : thm := BDivides.RING_DIVIDES_PRODUCTS
unsafe def RING_DIVIDES_PRODUCT_SUBSET : thm := BDivides.RING_DIVIDES_PRODUCT_SUBSET
unsafe def RING_ASSOCIATES_REFL : thm := BDivides.RING_ASSOCIATES_REFL
unsafe def RING_ASSOCIATES_SYM : thm := BDivides.RING_ASSOCIATES_SYM
unsafe def RING_ASSOCIATES_TRANS : thm := BDivides.RING_ASSOCIATES_TRANS
unsafe def RING_ASSOCIATES_SAME_DIVISORS : thm := BDivides.RING_ASSOCIATES_SAME_DIVISORS
unsafe def RING_ASSOCIATES_0 : thm := BDivides.RING_ASSOCIATES_0
unsafe def RING_ASSOCIATES_1 : thm := BDivides.RING_ASSOCIATES_1
unsafe def RING_ASSOCIATES_LNEG : thm := BDivides.RING_ASSOCIATES_LNEG
unsafe def RING_ASSOCIATES_NEG : thm := BDivides.RING_ASSOCIATES_NEG
unsafe def RING_ASSOCIATES_NEG_EQ : thm := BDivides.RING_ASSOCIATES_NEG_EQ
unsafe def RING_ASSOCIATES_MUL : thm := BDivides.RING_ASSOCIATES_MUL
unsafe def RING_ASSOCIATES_POW : thm := BDivides.RING_ASSOCIATES_POW
unsafe def RING_ASSOCIATES_PRODUCT : thm := BDivides.RING_ASSOCIATES_PRODUCT
unsafe def RING_ZERODIVISOR_0 : thm := BDivides.RING_ZERODIVISOR_0
unsafe def RING_REGULAR_0 : thm := BDivides.RING_REGULAR_0
unsafe def RING_ZERODIVISOR_1 : thm := BDivides.RING_ZERODIVISOR_1
unsafe def RING_REGULAR_1 : thm := BDivides.RING_REGULAR_1
unsafe def RING_ZERODIVISOR_LMUL : thm := BDivides.RING_ZERODIVISOR_LMUL
unsafe def RING_ZERODIVISOR_RMUL : thm := BDivides.RING_ZERODIVISOR_RMUL
unsafe def RING_ZERODIVISOR_MUL : thm := BDivides.RING_ZERODIVISOR_MUL
unsafe def RING_ZERODIVISOR_POW : thm := BDivides.RING_ZERODIVISOR_POW
unsafe def RING_REGULAR_MUL_EQ : thm := BDivides.RING_REGULAR_MUL_EQ
unsafe def RING_REGULAR_POW : thm := BDivides.RING_REGULAR_POW
unsafe def RING_REGULAR_MUL : thm := BDivides.RING_REGULAR_MUL
unsafe def RING_ZERODIVISOR_NEG : thm := BDivides.RING_ZERODIVISOR_NEG
unsafe def RING_ZERODIVISOR_NEG_EQ : thm := BDivides.RING_ZERODIVISOR_NEG_EQ
unsafe def RING_REGULAR_NEG : thm := BDivides.RING_REGULAR_NEG
unsafe def RING_REGULAR_NEG_EQ : thm := BDivides.RING_REGULAR_NEG_EQ
unsafe def RING_ZERODIVISOR_IMP_NONUNIT : thm := BDivides.RING_ZERODIVISOR_IMP_NONUNIT
unsafe def RING_UNIT_IMP_REGULAR : thm := BDivides.RING_UNIT_IMP_REGULAR
unsafe def RING_DIVIDES_UNIT : thm := BDivides.RING_DIVIDES_UNIT
unsafe def RING_COPRIME_REFL : thm := BDivides.RING_COPRIME_REFL
unsafe def RING_COPRIME_SYM : thm := BDivides.RING_COPRIME_SYM
unsafe def RING_COPRIME_0 : thm := BDivides.RING_COPRIME_0
unsafe def RING_COPRIME_00 : thm := BDivides.RING_COPRIME_00
unsafe def RING_COPRIME_DIVISORS : thm := BDivides.RING_COPRIME_DIVISORS
unsafe def RING_COPRIME_UNIT : thm := BDivides.RING_COPRIME_UNIT
unsafe def RING_ASSOCIATES_RMUL : thm := BDivides.RING_ASSOCIATES_RMUL
unsafe def RING_ASSOCIATES_LMUL : thm := BDivides.RING_ASSOCIATES_LMUL
unsafe def RING_ASSOCIATES_DIVIDES : thm := BDivides.RING_ASSOCIATES_DIVIDES
unsafe def RING_ASSOCIATES_ASSOCIATES : thm := BDivides.RING_ASSOCIATES_ASSOCIATES
unsafe def RING_ASSOCIATES_UNIT : thm := BDivides.RING_ASSOCIATES_UNIT
unsafe def RING_ASSOCIATES_EQ_0 : thm := BDivides.RING_ASSOCIATES_EQ_0
unsafe def RING_ASSOCIATES_COPRIME : thm := BDivides.RING_ASSOCIATES_COPRIME
unsafe def RING_ASSOCIATES_ZERODIVISOR : thm := BDivides.RING_ASSOCIATES_ZERODIVISOR
unsafe def RING_ASSOCIATES_REGULAR : thm := BDivides.RING_ASSOCIATES_REGULAR
unsafe def RING_ASSOCIATES_NILPOTENT : thm := BDivides.RING_ASSOCIATES_NILPOTENT
unsafe def RING_NILPOTENT_0 : thm := BDivides.RING_NILPOTENT_0
unsafe def RING_NILPOTENT_1 : thm := BDivides.RING_NILPOTENT_1
unsafe def RING_NILPOTENT : thm := BDivides.RING_NILPOTENT
unsafe def RING_NILPOTENT_POW : thm := BDivides.RING_NILPOTENT_POW
unsafe def RING_NILPOTENT_IMP_ZERODIVISOR : thm := BDivides.RING_NILPOTENT_IMP_ZERODIVISOR
unsafe def RING_NILPOTENT_NEG : thm := BDivides.RING_NILPOTENT_NEG
unsafe def RING_NILPOTENT_NEG_EQ : thm := BDivides.RING_NILPOTENT_NEG_EQ
unsafe def RING_UNIT_IDEMPOTENT_EQ_1 : thm := BDivides.RING_UNIT_IDEMPOTENT_EQ_1

-- Subrings
unsafe def subring_of : thm := BSubrings.subring_of
unsafe def subring_generated : thm := BSubrings.subring_generated
unsafe def IN_SUBRING_0 : thm := BSubrings.IN_SUBRING_0
unsafe def IN_SUBRING_1 : thm := BSubrings.IN_SUBRING_1
unsafe def IN_SUBRING_NEG : thm := BSubrings.IN_SUBRING_NEG
unsafe def IN_SUBRING_ADD : thm := BSubrings.IN_SUBRING_ADD
unsafe def IN_SUBRING_MUL : thm := BSubrings.IN_SUBRING_MUL
unsafe def IN_SUBRING_SUB : thm := BSubrings.IN_SUBRING_SUB
unsafe def IN_SUBRING_POW : thm := BSubrings.IN_SUBRING_POW
unsafe def IN_SUBRING_NUM : thm := BSubrings.IN_SUBRING_NUM
unsafe def IN_SUBRING_INT : thm := BSubrings.IN_SUBRING_INT
unsafe def IN_SUBRING_SUM : thm := BSubrings.IN_SUBRING_SUM
unsafe def IN_SUBRING_PRODUCT : thm := BSubrings.IN_SUBRING_PRODUCT
unsafe def SUBRING_OF_INTERS : thm := BSubrings.SUBRING_OF_INTERS
unsafe def SUBRING_OF_INTER : thm := BSubrings.SUBRING_OF_INTER
unsafe def SUBRING_OF_UNIONS : thm := BSubrings.SUBRING_OF_UNIONS
unsafe def SUBRING_OF_IMP_SUBSET : thm := BSubrings.SUBRING_OF_IMP_SUBSET
unsafe def SUBRING_OF_IMP_NONEMPTY : thm := BSubrings.SUBRING_OF_IMP_NONEMPTY
unsafe def CARRIER_SUBRING_OF : thm := BSubrings.CARRIER_SUBRING_OF
unsafe def PRIME_SUBRING : thm := BSubrings.PRIME_SUBRING
unsafe def PRIME_SUBRING_MINIMAL : thm := BSubrings.PRIME_SUBRING_MINIMAL
unsafe def SUBRING_GENERATED : thm := BSubrings.SUBRING_GENERATED
unsafe def SUBRING_GENERATED_EQ : thm := BSubrings.SUBRING_GENERATED_EQ
unsafe def RING_SUB_SUBRING_GENERATED : thm := BSubrings.RING_SUB_SUBRING_GENERATED
unsafe def RING_POW_SUBRING_GENERATED : thm := BSubrings.RING_POW_SUBRING_GENERATED
unsafe def RING_OF_NUM_SUBRING_GENERATED : thm := BSubrings.RING_OF_NUM_SUBRING_GENERATED
unsafe def RING_OF_INT_SUBRING_GENERATED : thm := BSubrings.RING_OF_INT_SUBRING_GENERATED
unsafe def RING_0_IN_SUBRING_GENERATED : thm := BSubrings.RING_0_IN_SUBRING_GENERATED
unsafe def RING_1_IN_SUBRING_GENERATED : thm := BSubrings.RING_1_IN_SUBRING_GENERATED
unsafe def RING_NEG_IN_SUBRING_GENERATED : thm := BSubrings.RING_NEG_IN_SUBRING_GENERATED
unsafe def RING_ADD_IN_SUBRING_GENERATED : thm := BSubrings.RING_ADD_IN_SUBRING_GENERATED
unsafe def RING_MUL_IN_SUBRING_GENERATED : thm := BSubrings.RING_MUL_IN_SUBRING_GENERATED
unsafe def RING_POW_IN_SUBRING_GENERATED : thm := BSubrings.RING_POW_IN_SUBRING_GENERATED
unsafe def SUBRING_GENERATED_RESTRICT : thm := BSubrings.SUBRING_GENERATED_RESTRICT
unsafe def SUBRING_SUBRING_GENERATED : thm := BSubrings.SUBRING_SUBRING_GENERATED
unsafe def SUBRING_GENERATED_MONO : thm := BSubrings.SUBRING_GENERATED_MONO
unsafe def SUBRING_GENERATED_MINIMAL : thm := BSubrings.SUBRING_GENERATED_MINIMAL
unsafe def SUBRINGS_GENERATED_EQ : thm := BSubrings.SUBRINGS_GENERATED_EQ
unsafe def SUBRING_GENERATED_INDUCT : thm := BSubrings.SUBRING_GENERATED_INDUCT
unsafe def SUBRING_GENERATED_INDUCT_STRONG : thm := BSubrings.SUBRING_GENERATED_INDUCT_STRONG
unsafe def RING_CARRIER_SUBRING_GENERATED_SUBSET : thm := BSubrings.RING_CARRIER_SUBRING_GENERATED_SUBSET
unsafe def SUBRING_OF_SUBRING_GENERATED_EQ : thm := BSubrings.SUBRING_OF_SUBRING_GENERATED_EQ
unsafe def SUBRING_GENERATED_SUPERSET : thm := BSubrings.SUBRING_GENERATED_SUPERSET
unsafe def FINITE_SUBRING_GENERATED : thm := BSubrings.FINITE_SUBRING_GENERATED
unsafe def SUBRING_GENERATED_SUBSET_CARRIER : thm := BSubrings.SUBRING_GENERATED_SUBSET_CARRIER
unsafe def SUBSET_CARRIER_SUBRING_GENERATED : thm := BSubrings.SUBSET_CARRIER_SUBRING_GENERATED
unsafe def CARRIER_SUBRING_GENERATED_SUBRING : thm := BSubrings.CARRIER_SUBRING_GENERATED_SUBRING
unsafe def SUBRING_GENERATED_MINIMAL_EQ : thm := BSubrings.SUBRING_GENERATED_MINIMAL_EQ
unsafe def SUBRING_OF_SUBRING_GENERATED_SUBRING_EQ : thm := BSubrings.SUBRING_OF_SUBRING_GENERATED_SUBRING_EQ
unsafe def SUBRING_GENERATED_RING_CARRIER : thm := BSubrings.SUBRING_GENERATED_RING_CARRIER
unsafe def SUBRING_OF_SUBRING_GENERATED : thm := BSubrings.SUBRING_OF_SUBRING_GENERATED
unsafe def SUBRING_GENERATED_SUBSET_CARRIER_SUBSET : thm := BSubrings.SUBRING_GENERATED_SUBSET_CARRIER_SUBSET
unsafe def SUBRING_GENERATED_REFL : thm := BSubrings.SUBRING_GENERATED_REFL
unsafe def SUBRING_GENERATED_INC : thm := BSubrings.SUBRING_GENERATED_INC
unsafe def SUBRING_GENERATED_INC_GEN : thm := BSubrings.SUBRING_GENERATED_INC_GEN
unsafe def SUBRING_OF_SUBRING_GENERATED_REV : thm := BSubrings.SUBRING_OF_SUBRING_GENERATED_REV
unsafe def TRIVIAL_RING_SUBRING_GENERATED : thm := BSubrings.TRIVIAL_RING_SUBRING_GENERATED
unsafe def SUBRING_GENERATED_BY_SUBRING_GENERATED : thm := BSubrings.SUBRING_GENERATED_BY_SUBRING_GENERATED
unsafe def SUBRING_GENERATED_INSERT_ZERO : thm := BSubrings.SUBRING_GENERATED_INSERT_ZERO
unsafe def RING_CARRIER_SUBRING_GENERATED_MONO : thm := BSubrings.RING_CARRIER_SUBRING_GENERATED_MONO
unsafe def SUBRING_GENERATED_IDEMPOT_GEN : thm := BSubrings.SUBRING_GENERATED_IDEMPOT_GEN
unsafe def SUBRING_GENERATED_IDEMPOT : thm := BSubrings.SUBRING_GENERATED_IDEMPOT
unsafe def SUBRING_GENERATED_SUBRING_GENERATED : thm := BSubrings.SUBRING_GENERATED_SUBRING_GENERATED
unsafe def SUBRING_GENERATED_BY_SUBRING_GENERATED_IDEMPOT : thm := BSubrings.SUBRING_GENERATED_BY_SUBRING_GENERATED_IDEMPOT
unsafe def SUBRING_GENERATED_UNION_LEFT : thm := BSubrings.SUBRING_GENERATED_UNION_LEFT
unsafe def SUBRING_GENERATED_UNION_RIGHT : thm := BSubrings.SUBRING_GENERATED_UNION_RIGHT
unsafe def SUBRING_GENERATED_UNION : thm := BSubrings.SUBRING_GENERATED_UNION
unsafe def RING_CHAR_SUBRING_GENERATED : thm := BSubrings.RING_CHAR_SUBRING_GENERATED
unsafe def IN_SUBRING_GENERATED_FINITARY : thm := BSubrings.IN_SUBRING_GENERATED_FINITARY
unsafe def SUBRING_GENERATED_FINITARY : thm := BSubrings.SUBRING_GENERATED_FINITARY
unsafe def SUBSET_SUBRING_GENERATED_FINITARY : thm := BSubrings.SUBSET_SUBRING_GENERATED_FINITARY
unsafe def SUBRING_GENERATED_PRIME_SUBRING : thm := BSubrings.SUBRING_GENERATED_PRIME_SUBRING
unsafe def RING_CARRIER_SUBRING_GENERATED_0 : thm := BSubrings.RING_CARRIER_SUBRING_GENERATED_0

-- Ideals
unsafe def ring_ideal : thm := BIdeals.ring_ideal
unsafe def RING_IDEAL : thm := BIdeals.RING_IDEAL
unsafe def RING_IDEAL_IMP_SUBSET : thm := BIdeals.RING_IDEAL_IMP_SUBSET
unsafe def RING_IDEAL_IMP_NONEMPTY : thm := BIdeals.RING_IDEAL_IMP_NONEMPTY
unsafe def RING_IDEAL_0 : thm := BIdeals.RING_IDEAL_0
unsafe def IN_RING_IDEAL_0 : thm := BIdeals.IN_RING_IDEAL_0
unsafe def IN_RING_IDEAL_NEG : thm := BIdeals.IN_RING_IDEAL_NEG
unsafe def IN_RING_IDEAL_ADD : thm := BIdeals.IN_RING_IDEAL_ADD
unsafe def IN_RING_IDEAL_SUB : thm := BIdeals.IN_RING_IDEAL_SUB
unsafe def IN_RING_IDEAL_MUL : thm := BIdeals.IN_RING_IDEAL_MUL
unsafe def IN_RING_IDEAL_LMUL : thm := BIdeals.IN_RING_IDEAL_LMUL
unsafe def IN_RING_IDEAL_RMUL : thm := BIdeals.IN_RING_IDEAL_RMUL
unsafe def RING_MULTIPLE_IN_IDEAL : thm := BIdeals.RING_MULTIPLE_IN_IDEAL
unsafe def RING_POW_IN_IDEAL : thm := BIdeals.RING_POW_IN_IDEAL
unsafe def IN_RING_IDEAL_SUM : thm := BIdeals.IN_RING_IDEAL_SUM
unsafe def RING_ASSOCIATES_IN_IDEAL : thm := BIdeals.RING_ASSOCIATES_IN_IDEAL
unsafe def RING_IDEAL_INTERS : thm := BIdeals.RING_IDEAL_INTERS
unsafe def RING_IDEAL_INTER : thm := BIdeals.RING_IDEAL_INTER
unsafe def RING_IDEAL_UNIONS : thm := BIdeals.RING_IDEAL_UNIONS
unsafe def RING_IDEAL_EQ_CARRIER : thm := BIdeals.RING_IDEAL_EQ_CARRIER
unsafe def RING_IDEAL_EQ_CARRIER_UNIT : thm := BIdeals.RING_IDEAL_EQ_CARRIER_UNIT
unsafe def TRIVIAL_RING_IDEAL : thm := BIdeals.TRIVIAL_RING_IDEAL
unsafe def RING_IDEAL_CARRIER : thm := BIdeals.RING_IDEAL_CARRIER
unsafe def RING_IDEAL_SUBRING_GENERATED_EQ : thm := BIdeals.RING_IDEAL_SUBRING_GENERATED_EQ
unsafe def RING_IDEAL_SUBRING_GENERATED : thm := BIdeals.RING_IDEAL_SUBRING_GENERATED
unsafe def RING_SUBRING_INTER_IDEAL : thm := BIdeals.RING_SUBRING_INTER_IDEAL
unsafe def RING_IDEAL_INTER_SUBRING : thm := BIdeals.RING_IDEAL_INTER_SUBRING
unsafe def ring_setneg : thm := BIdeals.ring_setneg
unsafe def ring_setadd : thm := BIdeals.ring_setadd
unsafe def ring_setmul : thm := BIdeals.ring_setmul
unsafe def RING_NEG_IN_SETNEG : thm := BIdeals.RING_NEG_IN_SETNEG
unsafe def RING_ADD_IN_SETADD : thm := BIdeals.RING_ADD_IN_SETADD
unsafe def RING_MUL_IN_SETMUL : thm := BIdeals.RING_MUL_IN_SETMUL
unsafe def RING_SETNEG_MONO : thm := BIdeals.RING_SETNEG_MONO
unsafe def RING_SETADD_MONO : thm := BIdeals.RING_SETADD_MONO
unsafe def RING_SETMUL_MONO : thm := BIdeals.RING_SETMUL_MONO
unsafe def SUBRING_OF_SETWISE : thm := BIdeals.SUBRING_OF_SETWISE
unsafe def RING_IDEAL_SETWISE : thm := BIdeals.RING_IDEAL_SETWISE
unsafe def RING_SETNEG_EQ_EMPTY : thm := BIdeals.RING_SETNEG_EQ_EMPTY
unsafe def RING_SETADD_EQ_EMPTY : thm := BIdeals.RING_SETADD_EQ_EMPTY
unsafe def RING_SETMUL_EQ_EMPTY : thm := BIdeals.RING_SETMUL_EQ_EMPTY
unsafe def RING_SETNEG_SING : thm := BIdeals.RING_SETNEG_SING
unsafe def RING_SETADD_SING : thm := BIdeals.RING_SETADD_SING
unsafe def RING_SETMUL_SING : thm := BIdeals.RING_SETMUL_SING
unsafe def RING_SETNEG : thm := BIdeals.RING_SETNEG
unsafe def RING_SETADD : thm := BIdeals.RING_SETADD
unsafe def RING_SETMUL : thm := BIdeals.RING_SETMUL
unsafe def RING_SETADD_SYM : thm := BIdeals.RING_SETADD_SYM
unsafe def RING_SETMUL_SYM : thm := BIdeals.RING_SETMUL_SYM
unsafe def RING_SETADD_LZERO : thm := BIdeals.RING_SETADD_LZERO
unsafe def RING_SETADD_RZERO : thm := BIdeals.RING_SETADD_RZERO
unsafe def RING_SETMUL_LID : thm := BIdeals.RING_SETMUL_LID
unsafe def RING_SETMUL_RID : thm := BIdeals.RING_SETMUL_RID
unsafe def RING_SETADD_ASSOC : thm := BIdeals.RING_SETADD_ASSOC
unsafe def RING_SETMUL_ASSOC : thm := BIdeals.RING_SETMUL_ASSOC
unsafe def RING_SETADD_AC : thm := BIdeals.RING_SETADD_AC
unsafe def RING_SETMUL_AC : thm := BIdeals.RING_SETMUL_AC
unsafe def RING_SETADD_SUPERSET_LEFT : thm := BIdeals.RING_SETADD_SUPERSET_LEFT
unsafe def RING_SETADD_SUPERSET_RIGHT : thm := BIdeals.RING_SETADD_SUPERSET_RIGHT
unsafe def RING_SETNEG_SETADD : thm := BIdeals.RING_SETNEG_SETADD
unsafe def RING_SETADD_LDISTRIB : thm := BIdeals.RING_SETADD_LDISTRIB
unsafe def RING_SETADD_RDISTRIB : thm := BIdeals.RING_SETADD_RDISTRIB
unsafe def RING_SETNEG_IDEAL : thm := BIdeals.RING_SETNEG_IDEAL
unsafe def RING_SETNEG_SUBRING : thm := BIdeals.RING_SETNEG_SUBRING
unsafe def RING_SETADD_LSUBSET : thm := BIdeals.RING_SETADD_LSUBSET
unsafe def RING_SETADD_RSUBSET : thm := BIdeals.RING_SETADD_RSUBSET
unsafe def RING_SETADD_LSUBSET_EQ : thm := BIdeals.RING_SETADD_LSUBSET_EQ
unsafe def RING_SETADD_RSUBSET_EQ : thm := BIdeals.RING_SETADD_RSUBSET_EQ
unsafe def RING_SETADD_SUBRING : thm := BIdeals.RING_SETADD_SUBRING
unsafe def RING_SETMUL_SUBRING : thm := BIdeals.RING_SETMUL_SUBRING
unsafe def RING_SETADD_SUBSET_IDEAL : thm := BIdeals.RING_SETADD_SUBSET_IDEAL
unsafe def RING_SETADD_IDEAL_LEFT : thm := BIdeals.RING_SETADD_IDEAL_LEFT
unsafe def RING_SETADD_IDEAL_RIGHT : thm := BIdeals.RING_SETADD_IDEAL_RIGHT
unsafe def RING_SETMUL_IDEAL_LEFT : thm := BIdeals.RING_SETMUL_IDEAL_LEFT
unsafe def RING_SETMUL_IDEAL_RIGHT : thm := BIdeals.RING_SETMUL_IDEAL_RIGHT
unsafe def RING_SETMUL_SUBSET_IDEAL : thm := BIdeals.RING_SETMUL_SUBSET_IDEAL
unsafe def RING_SETADD_LCANCEL : thm := BIdeals.RING_SETADD_LCANCEL
unsafe def RING_SETADD_RCANCEL : thm := BIdeals.RING_SETADD_RCANCEL
unsafe def RING_SETADD_LCANCEL_SET : thm := BIdeals.RING_SETADD_LCANCEL_SET
unsafe def RING_SETADD_RCANCEL_SET : thm := BIdeals.RING_SETADD_RCANCEL_SET
unsafe def RING_IDEAL_SETADD : thm := BIdeals.RING_IDEAL_SETADD
unsafe def SUBRING_SETADD_LEFT : thm := BIdeals.SUBRING_SETADD_LEFT
unsafe def SUBRING_SETADD_RIGHT : thm := BIdeals.SUBRING_SETADD_RIGHT
unsafe def RING_IDEAL_QUOTIENT : thm := BIdeals.RING_IDEAL_QUOTIENT
unsafe def RING_IDEAL_QUOTIENT_RMUL : thm := BIdeals.RING_IDEAL_QUOTIENT_RMUL
unsafe def RING_IDEAL_QUOTIENT_LMUL : thm := BIdeals.RING_IDEAL_QUOTIENT_LMUL
unsafe def RING_COMAXIMAL : thm := BIdeals.RING_COMAXIMAL
unsafe def ideal_generated : thm := BIdeals.ideal_generated
unsafe def IDEAL_GENERATED_RESTRICT : thm := BIdeals.IDEAL_GENERATED_RESTRICT
unsafe def RING_IDEAL_IDEAL_GENERATED : thm := BIdeals.RING_IDEAL_IDEAL_GENERATED
unsafe def IDEAL_GENERATED_NONEMPTY : thm := BIdeals.IDEAL_GENERATED_NONEMPTY
unsafe def IDEAL_GENERATED_MONO : thm := BIdeals.IDEAL_GENERATED_MONO
unsafe def IDEAL_GENERATED_MINIMAL : thm := BIdeals.IDEAL_GENERATED_MINIMAL
unsafe def IDEAL_GENERATED_INDUCT : thm := BIdeals.IDEAL_GENERATED_INDUCT
unsafe def IDEAL_GENERATED_INDUCT_STRONG : thm := BIdeals.IDEAL_GENERATED_INDUCT_STRONG
unsafe def IDEAL_GENERATED_SUBSET : thm := BIdeals.IDEAL_GENERATED_SUBSET
unsafe def FINITE_IDEAL_GENERATED : thm := BIdeals.FINITE_IDEAL_GENERATED
unsafe def IDEAL_GENERATED_SUBSET_CARRIER : thm := BIdeals.IDEAL_GENERATED_SUBSET_CARRIER
unsafe def IDEAL_GENERATED_MINIMAL_EQ : thm := BIdeals.IDEAL_GENERATED_MINIMAL_EQ
unsafe def IDEALS_GENERATED_SUBSET : thm := BIdeals.IDEALS_GENERATED_SUBSET
unsafe def IDEAL_GENERATED_RING_IDEAL : thm := BIdeals.IDEAL_GENERATED_RING_IDEAL
unsafe def IDEAL_GENERATED_RING_IDEAL_EQ : thm := BIdeals.IDEAL_GENERATED_RING_IDEAL_EQ
unsafe def IDEAL_GENERATED_RING_CARRIER : thm := BIdeals.IDEAL_GENERATED_RING_CARRIER
unsafe def IDEAL_GENERATED_SUBSET_CARRIER_SUBSET : thm := BIdeals.IDEAL_GENERATED_SUBSET_CARRIER_SUBSET
unsafe def IDEAL_GENERATED_REFL : thm := BIdeals.IDEAL_GENERATED_REFL
unsafe def IDEAL_GENERATED_INC : thm := BIdeals.IDEAL_GENERATED_INC
unsafe def IDEAL_GENERATED_INC_GEN : thm := BIdeals.IDEAL_GENERATED_INC_GEN
unsafe def IDEAL_GENERATED_BY_IDEAL_GENERATED : thm := BIdeals.IDEAL_GENERATED_BY_IDEAL_GENERATED
unsafe def IDEAL_GENERATED_INSERT_ZERO : thm := BIdeals.IDEAL_GENERATED_INSERT_ZERO
unsafe def IDEAL_GENERATED_0 : thm := BIdeals.IDEAL_GENERATED_0
unsafe def IDEAL_GENERATED_EMPTY : thm := BIdeals.IDEAL_GENERATED_EMPTY
unsafe def IDEAL_GENERATED_SING : thm := BIdeals.IDEAL_GENERATED_SING
unsafe def IDEAL_GENERATED_SING_ALT : thm := BIdeals.IDEAL_GENERATED_SING_ALT
unsafe def IN_IDEAL_GENERATED_SING_EQ : thm := BIdeals.IN_IDEAL_GENERATED_SING_EQ
unsafe def IN_IDEAL_GENERATED_SING : thm := BIdeals.IN_IDEAL_GENERATED_SING
unsafe def IN_IDEAL_GENERATED_SELF : thm := BIdeals.IN_IDEAL_GENERATED_SELF
unsafe def IDEAL_GENERATED_SING_EQ_CARRIER : thm := BIdeals.IDEAL_GENERATED_SING_EQ_CARRIER
unsafe def SUBSET_IDEALS_GENERATED_SING : thm := BIdeals.SUBSET_IDEALS_GENERATED_SING
unsafe def IDEALS_GENERATED_SING_EQ : thm := BIdeals.IDEALS_GENERATED_SING_EQ
unsafe def PSUBSET_IDEALS_GENERATED_SING : thm := BIdeals.PSUBSET_IDEALS_GENERATED_SING
unsafe def IDEAL_GENERATED_EQ_0 : thm := BIdeals.IDEAL_GENERATED_EQ_0
unsafe def IDEAL_GENERATED_SING_SETMUL_RIGHT : thm := BIdeals.IDEAL_GENERATED_SING_SETMUL_RIGHT
unsafe def IDEAL_GENERATED_SING_SETMUL_LEFT : thm := BIdeals.IDEAL_GENERATED_SING_SETMUL_LEFT
unsafe def RING_SETMUL_IDEAL_GENERATED_SING : thm := BIdeals.RING_SETMUL_IDEAL_GENERATED_SING
unsafe def IDEAL_GENERATED_UNION : thm := BIdeals.IDEAL_GENERATED_UNION
unsafe def IDEAL_GENERATED_INSERT : thm := BIdeals.IDEAL_GENERATED_INSERT
unsafe def IDEAL_GENERATED_2 : thm := BIdeals.IDEAL_GENERATED_2
unsafe def IDEAL_GENERATED_SETADD_SUBSET : thm := BIdeals.IDEAL_GENERATED_SETADD_SUBSET
unsafe def RING_SCALE_SETMUL : thm := BIdeals.RING_SCALE_SETMUL
unsafe def RING_IDEAL_SCALE : thm := BIdeals.RING_IDEAL_SCALE
unsafe def IDEAL_GENERATED_SCALE : thm := BIdeals.IDEAL_GENERATED_SCALE
unsafe def IDEAL_GENERATED_FINITARY : thm := BIdeals.IDEAL_GENERATED_FINITARY
unsafe def IDEAL_GENERATED_FINITARY_ALT : thm := BIdeals.IDEAL_GENERATED_FINITARY_ALT
unsafe def IDEAL_GENERATED_FINITE_IMAGE : thm := BIdeals.IDEAL_GENERATED_FINITE_IMAGE
unsafe def IDEAL_GENERATED_FINITE : thm := BIdeals.IDEAL_GENERATED_FINITE
unsafe def IDEAL_GENERATED_EXPLICIT : thm := BIdeals.IDEAL_GENERATED_EXPLICIT

-- Domains
unsafe def integral_domain : thm := BDomains.integral_domain
unsafe def field : thm := BDomains.field
unsafe def INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING : thm := BDomains.INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING
unsafe def FIELD_IMP_NONTRIVIAL_RING : thm := BDomains.FIELD_IMP_NONTRIVIAL_RING
unsafe def INTEGRAL_DOMAIN_NONTRIVIAL : thm := BDomains.INTEGRAL_DOMAIN_NONTRIVIAL
unsafe def FIELD_NONTRIVIAL : thm := BDomains.FIELD_NONTRIVIAL
unsafe def INTEGRAL_DOMAIN_EQ_NO_ZERODIVISORS : thm := BDomains.INTEGRAL_DOMAIN_EQ_NO_ZERODIVISORS
unsafe def INTEGRAL_DOMAIN_EQ_ALL_REGULAR : thm := BDomains.INTEGRAL_DOMAIN_EQ_ALL_REGULAR
unsafe def INTEGRAL_DOMAIN_ZERODIVISOR : thm := BDomains.INTEGRAL_DOMAIN_ZERODIVISOR
unsafe def INTEGRAL_DOMAIN_REGULAR : thm := BDomains.INTEGRAL_DOMAIN_REGULAR
unsafe def INTEGRAL_DOMAIN_MUL_EQ_0 : thm := BDomains.INTEGRAL_DOMAIN_MUL_EQ_0
unsafe def INTEGRAL_DOMAIN_POW_EQ_0 : thm := BDomains.INTEGRAL_DOMAIN_POW_EQ_0
unsafe def INTEGRAL_DOMAIN_NILPOTENT : thm := BDomains.INTEGRAL_DOMAIN_NILPOTENT
unsafe def INTEGRAL_DOMAIN_PRODUCT_EQ_0 : thm := BDomains.INTEGRAL_DOMAIN_PRODUCT_EQ_0
unsafe def INTEGRAL_DOMAIN_MUL_LCANCEL : thm := BDomains.INTEGRAL_DOMAIN_MUL_LCANCEL
unsafe def INTEGRAL_DOMAIN_MUL_LCANCEL_EQ : thm := BDomains.INTEGRAL_DOMAIN_MUL_LCANCEL_EQ
unsafe def INTEGRAL_DOMAIN_MUL_RCANCEL : thm := BDomains.INTEGRAL_DOMAIN_MUL_RCANCEL
unsafe def INTEGRAL_DOMAIN_MUL_RCANCEL_EQ : thm := BDomains.INTEGRAL_DOMAIN_MUL_RCANCEL_EQ
unsafe def INTEGRAL_DOMAIN_DIVIDES_LMUL2 : thm := BDomains.INTEGRAL_DOMAIN_DIVIDES_LMUL2
unsafe def INTEGRAL_DOMAIN_DIVIDES_RMUL2 : thm := BDomains.INTEGRAL_DOMAIN_DIVIDES_RMUL2
unsafe def INTEGRAL_DOMAIN_ASSOCIATES_LMUL2 : thm := BDomains.INTEGRAL_DOMAIN_ASSOCIATES_LMUL2
unsafe def INTEGRAL_DOMAIN_ASSOCIATES_RMUL2 : thm := BDomains.INTEGRAL_DOMAIN_ASSOCIATES_RMUL2
unsafe def INTEGRAL_DOMAIN_MUL_EQ_SELF : thm := BDomains.INTEGRAL_DOMAIN_MUL_EQ_SELF
unsafe def INTEGRAL_DOMAIN_DIVIDES_MUL_SELF : thm := BDomains.INTEGRAL_DOMAIN_DIVIDES_MUL_SELF
unsafe def INTEGRAL_DOMAIN_DIVIDES_ASSOCIATES_MUL_SELF : thm := BDomains.INTEGRAL_DOMAIN_DIVIDES_ASSOCIATES_MUL_SELF
unsafe def FIELD_EQ_ALL_UNITS : thm := BDomains.FIELD_EQ_ALL_UNITS
unsafe def FIELD_EQ_ALL_DIVIDE_1 : thm := BDomains.FIELD_EQ_ALL_DIVIDE_1
unsafe def FIELD_UNIT : thm := BDomains.FIELD_UNIT
unsafe def FIELD_MUL_LINV : thm := BDomains.FIELD_MUL_LINV
unsafe def FIELD_MUL_RINV : thm := BDomains.FIELD_MUL_RINV
unsafe def FIELD_DIVIDES : thm := BDomains.FIELD_DIVIDES
unsafe def FIELD_ASSOCIATES : thm := BDomains.FIELD_ASSOCIATES
unsafe def FIELD_COPRIME : thm := BDomains.FIELD_COPRIME
unsafe def FIELD_IMP_INTEGRAL_DOMAIN : thm := BDomains.FIELD_IMP_INTEGRAL_DOMAIN
unsafe def FIELD_ZERODIVISOR : thm := BDomains.FIELD_ZERODIVISOR
unsafe def FIELD_REGULAR : thm := BDomains.FIELD_REGULAR
unsafe def FIELD_NILPOTENT : thm := BDomains.FIELD_NILPOTENT
unsafe def FIELD_MUL_EQ_0 : thm := BDomains.FIELD_MUL_EQ_0
unsafe def FIELD_POW_EQ_0 : thm := BDomains.FIELD_POW_EQ_0
unsafe def FIELD_PRODUCT_EQ_0 : thm := BDomains.FIELD_PRODUCT_EQ_0
unsafe def FINITE_INTEGRAL_DOMAIN_IMP_FIELD : thm := BDomains.FINITE_INTEGRAL_DOMAIN_IMP_FIELD
unsafe def FINITE_INTEGRAL_DOMAIN_EQ_FIELD : thm := BDomains.FINITE_INTEGRAL_DOMAIN_EQ_FIELD
unsafe def INTEGRAL_DOMAIN_CHAR : thm := BDomains.INTEGRAL_DOMAIN_CHAR
unsafe def RING_CHAR_DIVIDES_MUL : thm := BDomains.RING_CHAR_DIVIDES_MUL
unsafe def RING_CHAR_DIVIDES_PRIME : thm := BDomains.RING_CHAR_DIVIDES_PRIME
unsafe def FINITE_INTEGRAL_DOMAIN_CHAR : thm := BDomains.FINITE_INTEGRAL_DOMAIN_CHAR
unsafe def INTEGRAL_DOMAIN_SUBRING_GENERATED : thm := BDomains.INTEGRAL_DOMAIN_SUBRING_GENERATED
unsafe def INTEGRAL_DOMAIN_ASSOCIATES : thm := BDomains.INTEGRAL_DOMAIN_ASSOCIATES
unsafe def INTEGRAL_DOMAIN_10 : thm := BDomains.INTEGRAL_DOMAIN_10
unsafe def FIELD_10 : thm := BDomains.FIELD_10

-- Rules
unsafe def RING_CARRIER_RULE := BRules.RING_CARRIER_RULE
unsafe def RING_CARRIER_TAC : HolCore.Tactics.tactic := fun g => BRules.RING_CARRIER_TAC g
unsafe def RING_POLY_UNIVERSAL_CONV : HolCore.Equal.ioconv := fun t => BRules.RING_POLY_UNIVERSAL_CONV t
unsafe def RING_INTEGRAL_DOMAIN_UNIVERSAL := BRules.RING_INTEGRAL_DOMAIN_UNIVERSAL
unsafe def ring_ring_cofactors_universal := BRules.ring_ring_cofactors_universal

-- Homs
unsafe def ring_homomorphism : thm := BHoms.ring_homomorphism
unsafe def ring_monomorphism : thm := BHoms.ring_monomorphism
unsafe def ring_epimorphism : thm := BHoms.ring_epimorphism
unsafe def ring_endomorphism : thm := BHoms.ring_endomorphism
unsafe def ring_isomorphisms : thm := BHoms.ring_isomorphisms
unsafe def ring_isomorphism : thm := BHoms.ring_isomorphism
unsafe def ring_automorphism : thm := BHoms.ring_automorphism
unsafe def RING_HOMOMORPHISM_EQ : thm := BHoms.RING_HOMOMORPHISM_EQ
unsafe def RING_MONOMORPHISM_EQ : thm := BHoms.RING_MONOMORPHISM_EQ
unsafe def RING_EPIMORPHISM_EQ : thm := BHoms.RING_EPIMORPHISM_EQ
unsafe def RING_ENDOMORPHISM_EQ : thm := BHoms.RING_ENDOMORPHISM_EQ
unsafe def RING_ISOMORPHISMS_EQ : thm := BHoms.RING_ISOMORPHISMS_EQ
unsafe def RING_ISOMORPHISM_EQ : thm := BHoms.RING_ISOMORPHISM_EQ
unsafe def RING_AUTOMORPHISM_EQ : thm := BHoms.RING_AUTOMORPHISM_EQ
unsafe def RING_ISOMORPHISMS_SYM : thm := BHoms.RING_ISOMORPHISMS_SYM
unsafe def RING_ISOMORPHISMS_IMP_ISOMORPHISM : thm := BHoms.RING_ISOMORPHISMS_IMP_ISOMORPHISM
unsafe def RING_ISOMORPHISMS_IMP_ISOMORPHISM_ALT : thm := BHoms.RING_ISOMORPHISMS_IMP_ISOMORPHISM_ALT
unsafe def RING_HOMOMORPHISM : thm := BHoms.RING_HOMOMORPHISM
unsafe def RING_ISOMORPHISMS : thm := BHoms.RING_ISOMORPHISMS
unsafe def RING_HOMOMORPHISM_IN_CARRIER : thm := BHoms.RING_HOMOMORPHISM_IN_CARRIER
unsafe def RING_HOMOMORPHISM_0 : thm := BHoms.RING_HOMOMORPHISM_0
unsafe def RING_HOMOMORPHISM_1 : thm := BHoms.RING_HOMOMORPHISM_1
unsafe def RING_HOMOMORPHISM_NEG : thm := BHoms.RING_HOMOMORPHISM_NEG
unsafe def RING_HOMOMORPHISM_ADD : thm := BHoms.RING_HOMOMORPHISM_ADD
unsafe def RING_HOMOMORPHISM_MUL : thm := BHoms.RING_HOMOMORPHISM_MUL
unsafe def RING_HOMOMORPHISM_SUB : thm := BHoms.RING_HOMOMORPHISM_SUB
unsafe def RING_HOMOMORPHISM_POW : thm := BHoms.RING_HOMOMORPHISM_POW
unsafe def RING_HOMOMORPHISM_INV : thm := BHoms.RING_HOMOMORPHISM_INV
unsafe def FIELD_HOMOMORPHISM_INV : thm := BHoms.FIELD_HOMOMORPHISM_INV
unsafe def FIELD_HOMOMORPHISM_DIV : thm := BHoms.FIELD_HOMOMORPHISM_DIV
unsafe def RING_HOMOMORPHISM_RING_OF_NUM : thm := BHoms.RING_HOMOMORPHISM_RING_OF_NUM
unsafe def RING_HOMOMORPHISM_RING_OF_INT : thm := BHoms.RING_HOMOMORPHISM_RING_OF_INT
unsafe def RING_CHAR_HOMOMORPHIC_IMAGE : thm := BHoms.RING_CHAR_HOMOMORPHIC_IMAGE
unsafe def RING_HOMOMORPHISM_SUM : thm := BHoms.RING_HOMOMORPHISM_SUM
unsafe def RING_HOMOMORPHISM_PRODUCT : thm := BHoms.RING_HOMOMORPHISM_PRODUCT
unsafe def RING_MONOMORPHISM_SUM : thm := BHoms.RING_MONOMORPHISM_SUM
unsafe def RING_MONOMORPHISM_PRODUCT : thm := BHoms.RING_MONOMORPHISM_PRODUCT
unsafe def RING_MONOMORPHISM_SUM_GEN : thm := BHoms.RING_MONOMORPHISM_SUM_GEN
unsafe def RING_MONOMORPHISM_PRODUCT_GEN : thm := BHoms.RING_MONOMORPHISM_PRODUCT_GEN
unsafe def RING_HOMOMORPHISMS_EQ_FROM_SUBRING_GENERATED : thm := BHoms.RING_HOMOMORPHISMS_EQ_FROM_SUBRING_GENERATED
unsafe def RING_MONOMORPHISM_IMP_HOMOMORPHISM : thm := BHoms.RING_MONOMORPHISM_IMP_HOMOMORPHISM
unsafe def RING_EPIMORPHISM_IMP_HOMOMORPHISM : thm := BHoms.RING_EPIMORPHISM_IMP_HOMOMORPHISM
unsafe def RING_MONOMORPHISM_INJECTIVE_EQ : thm := BHoms.RING_MONOMORPHISM_INJECTIVE_EQ
unsafe def RING_MONOMORPHISM_EQ_0 : thm := BHoms.RING_MONOMORPHISM_EQ_0
unsafe def RING_HOMOMORPHISM_ID : thm := BHoms.RING_HOMOMORPHISM_ID
unsafe def RING_HOMOMORPHISM_I : thm := BHoms.RING_HOMOMORPHISM_I
unsafe def RING_MONOMORPHISM_ID : thm := BHoms.RING_MONOMORPHISM_ID
unsafe def RING_MONOMORPHISM_I : thm := BHoms.RING_MONOMORPHISM_I
unsafe def RING_EPIMORPHISM_ID : thm := BHoms.RING_EPIMORPHISM_ID
unsafe def RING_EPIMORPHISM_I : thm := BHoms.RING_EPIMORPHISM_I
unsafe def RING_ISOMORPHISMS_ID : thm := BHoms.RING_ISOMORPHISMS_ID
unsafe def RING_ISOMORPHISMS_I : thm := BHoms.RING_ISOMORPHISMS_I
unsafe def RING_ISOMORPHISM_ID : thm := BHoms.RING_ISOMORPHISM_ID
unsafe def RING_ISOMORPHISM_I : thm := BHoms.RING_ISOMORPHISM_I
unsafe def RING_AUTOMORPHISM_ID : thm := BHoms.RING_AUTOMORPHISM_ID
unsafe def RING_AUTOMORPHISM_I : thm := BHoms.RING_AUTOMORPHISM_I
unsafe def RING_HOMOMORPHISM_COMPOSE : thm := BHoms.RING_HOMOMORPHISM_COMPOSE
unsafe def RING_MONOMORPHISM_COMPOSE : thm := BHoms.RING_MONOMORPHISM_COMPOSE
unsafe def RING_MONOMORPHISM_COMPOSE_REV : thm := BHoms.RING_MONOMORPHISM_COMPOSE_REV
unsafe def RING_EPIMORPHISM_COMPOSE : thm := BHoms.RING_EPIMORPHISM_COMPOSE
unsafe def RING_EPIMORPHISM_COMPOSE_REV : thm := BHoms.RING_EPIMORPHISM_COMPOSE_REV
unsafe def RING_MONOMORPHISM_LEFT_INVERTIBLE : thm := BHoms.RING_MONOMORPHISM_LEFT_INVERTIBLE
unsafe def RING_EPIMORPHISM_RIGHT_INVERTIBLE : thm := BHoms.RING_EPIMORPHISM_RIGHT_INVERTIBLE
unsafe def RING_HOMOMORPHISM_INTO_SUBRING : thm := BHoms.RING_HOMOMORPHISM_INTO_SUBRING
unsafe def RING_HOMOMORPHISM_INTO_SUBRING_EQ_GEN : thm := BHoms.RING_HOMOMORPHISM_INTO_SUBRING_EQ_GEN
unsafe def RING_HOMOMORPHISM_INTO_SUBRING_EQ : thm := BHoms.RING_HOMOMORPHISM_INTO_SUBRING_EQ
unsafe def RING_HOMOMORPHISM_FROM_SUBRING_GENERATED : thm := BHoms.RING_HOMOMORPHISM_FROM_SUBRING_GENERATED
unsafe def RING_MONOMORPHISM_FROM_SUBRING_GENERATED : thm := BHoms.RING_MONOMORPHISM_FROM_SUBRING_GENERATED
unsafe def RING_HOMOMORPHISM_INCLUSION : thm := BHoms.RING_HOMOMORPHISM_INCLUSION
unsafe def RING_MONOMORPHISM_INCLUSION : thm := BHoms.RING_MONOMORPHISM_INCLUSION
unsafe def RING_HOMOMORPHISM_BETWEEN_SUBRINGS : thm := BHoms.RING_HOMOMORPHISM_BETWEEN_SUBRINGS
unsafe def RING_HOMOMORPHISM_BETWEEN_SUBRINGS_ALT : thm := BHoms.RING_HOMOMORPHISM_BETWEEN_SUBRINGS_ALT
unsafe def RING_MONOMORPHISM_INTO_SUBRING : thm := BHoms.RING_MONOMORPHISM_INTO_SUBRING
unsafe def RING_MONOMORPHISM_BETWEEN_SUBRINGS : thm := BHoms.RING_MONOMORPHISM_BETWEEN_SUBRINGS
unsafe def RING_MONOMORPHISM_INTO_SUPERRING : thm := BHoms.RING_MONOMORPHISM_INTO_SUPERRING
unsafe def RING_SUM_SUBRING_GENERATED_GEN : thm := BHoms.RING_SUM_SUBRING_GENERATED_GEN
unsafe def RING_SUM_SUBRING_GENERATED : thm := BHoms.RING_SUM_SUBRING_GENERATED
unsafe def RING_PRODUCT_SUBRING_GENERATED_GEN : thm := BHoms.RING_PRODUCT_SUBRING_GENERATED_GEN
unsafe def RING_PRODUCT_SUBRING_GENERATED : thm := BHoms.RING_PRODUCT_SUBRING_GENERATED
unsafe def SUBRING_GENERATED_BY_HOMOMORPHIC_IMAGE : thm := BHoms.SUBRING_GENERATED_BY_HOMOMORPHIC_IMAGE
unsafe def RING_EPIMORPHISM_BETWEEN_SUBRINGS : thm := BHoms.RING_EPIMORPHISM_BETWEEN_SUBRINGS
unsafe def RING_ISOMORPHISM : thm := BHoms.RING_ISOMORPHISM
unsafe def RING_ISOMORPHISM_SUBSET : thm := BHoms.RING_ISOMORPHISM_SUBSET
unsafe def SUBRING_OF_HOMOMORPHIC_IMAGE : thm := BHoms.SUBRING_OF_HOMOMORPHIC_IMAGE
unsafe def RING_IDEAL_EPIMORPHIC_IMAGE : thm := BHoms.RING_IDEAL_EPIMORPHIC_IMAGE
unsafe def SUBRING_OF_HOMOMORPHIC_PREIMAGE : thm := BHoms.SUBRING_OF_HOMOMORPHIC_PREIMAGE
unsafe def SUBRING_OF_EPIMORPHIC_PREIMAGE : thm := BHoms.SUBRING_OF_EPIMORPHIC_PREIMAGE
unsafe def SUBRING_OF_HOMOMORPHIC_EQUALITIES : thm := BHoms.SUBRING_OF_HOMOMORPHIC_EQUALITIES
unsafe def SUBRING_OF_FIXPOINTS : thm := BHoms.SUBRING_OF_FIXPOINTS
unsafe def RING_IDEAL_HOMOMORPHIC_PREIMAGE : thm := BHoms.RING_IDEAL_HOMOMORPHIC_PREIMAGE
unsafe def IDEAL_GENERATED_BY_HOMOMORPHIC_IMAGE : thm := BHoms.IDEAL_GENERATED_BY_HOMOMORPHIC_IMAGE
unsafe def IDEAL_GENERATED_BY_EPIMORPHIC_IMAGE : thm := BHoms.IDEAL_GENERATED_BY_EPIMORPHIC_IMAGE
unsafe def RING_MONOMORPHISM_EPIMORPHISM : thm := BHoms.RING_MONOMORPHISM_EPIMORPHISM
unsafe def SUBRING_MONOMORPHISM_EPIMORPHISM : thm := BHoms.SUBRING_MONOMORPHISM_EPIMORPHISM
unsafe def RING_ISOMORPHISM_EPIMORPHISM : thm := BHoms.RING_ISOMORPHISM_EPIMORPHISM
unsafe def RING_ISOMORPHISM_MONOMORPHISM : thm := BHoms.RING_ISOMORPHISM_MONOMORPHISM
unsafe def RING_ISOMORPHISM_MONOMORPHISM_ALT : thm := BHoms.RING_ISOMORPHISM_MONOMORPHISM_ALT
unsafe def RING_ISOMORPHISM_IMP_MONOMORPHISM : thm := BHoms.RING_ISOMORPHISM_IMP_MONOMORPHISM
unsafe def RING_ISOMORPHISM_IMP_EPIMORPHISM : thm := BHoms.RING_ISOMORPHISM_IMP_EPIMORPHISM
unsafe def RING_ISOMORPHISM_IMP_HOMOMORPHISM : thm := BHoms.RING_ISOMORPHISM_IMP_HOMOMORPHISM
unsafe def RING_AUTOMORPHISM_IMP_ENDOMORPHISM : thm := BHoms.RING_AUTOMORPHISM_IMP_ENDOMORPHISM
unsafe def RING_ISOMORPHISMS_ISOMORPHISM : thm := BHoms.RING_ISOMORPHISMS_ISOMORPHISM
unsafe def RING_ISOMORPHISM_EQ_MONOMORPHISM_FINITE : thm := BHoms.RING_ISOMORPHISM_EQ_MONOMORPHISM_FINITE
unsafe def RING_ISOMORPHISM_EQ_EPIMORPHISM_FINITE : thm := BHoms.RING_ISOMORPHISM_EQ_EPIMORPHISM_FINITE
unsafe def RING_ISOMORPHISMS_BETWEEN_SUBRINGS : thm := BHoms.RING_ISOMORPHISMS_BETWEEN_SUBRINGS
unsafe def RING_ISOMORPHISMS_BETWEEN_SUBRINGS_ALT : thm := BHoms.RING_ISOMORPHISMS_BETWEEN_SUBRINGS_ALT
unsafe def RING_ISOMORPHISM_BETWEEN_SUBRINGS : thm := BHoms.RING_ISOMORPHISM_BETWEEN_SUBRINGS
unsafe def RING_ISOMORPHISMS_COMPOSE : thm := BHoms.RING_ISOMORPHISMS_COMPOSE
unsafe def RING_ISOMORPHISM_COMPOSE : thm := BHoms.RING_ISOMORPHISM_COMPOSE
unsafe def RING_ISOMORPHISM_COMPOSE_REV : thm := BHoms.RING_ISOMORPHISM_COMPOSE_REV
unsafe def RING_EPIMORPHISM_ISOMORPHISM_COMPOSE_REV : thm := BHoms.RING_EPIMORPHISM_ISOMORPHISM_COMPOSE_REV
unsafe def RING_MONOMORPHISM_ISOMORPHISM_COMPOSE_REV : thm := BHoms.RING_MONOMORPHISM_ISOMORPHISM_COMPOSE_REV
unsafe def RING_ISOMORPHISM_INVERSE : thm := BHoms.RING_ISOMORPHISM_INVERSE
unsafe def RING_HOMOMORPHISM_FROM_TRIVIAL_RING : thm := BHoms.RING_HOMOMORPHISM_FROM_TRIVIAL_RING
unsafe def RING_MONOMORPHISM_FROM_TRIVIAL_RING : thm := BHoms.RING_MONOMORPHISM_FROM_TRIVIAL_RING
unsafe def RING_MONOMORPHISM_TO_TRIVIAL_RING : thm := BHoms.RING_MONOMORPHISM_TO_TRIVIAL_RING
unsafe def RING_EPIMORPHISM_FROM_TRIVIAL_RING : thm := BHoms.RING_EPIMORPHISM_FROM_TRIVIAL_RING
unsafe def RING_EPIMORPHISM_TO_TRIVIAL_RING : thm := BHoms.RING_EPIMORPHISM_TO_TRIVIAL_RING
unsafe def TRIVIAL_RING_MONOMORPHIC_PREIMAGE : thm := BHoms.TRIVIAL_RING_MONOMORPHIC_PREIMAGE
unsafe def TRIVIAL_RING_HOMOMORPHIC_IMAGE : thm := BHoms.TRIVIAL_RING_HOMOMORPHIC_IMAGE
unsafe def TRIVIAL_RING_MONOMORPHIC_IMAGE_EQ : thm := BHoms.TRIVIAL_RING_MONOMORPHIC_IMAGE_EQ
unsafe def RING_NILPOTENT_HOMOMORPHIC_IMAGE : thm := BHoms.RING_NILPOTENT_HOMOMORPHIC_IMAGE
unsafe def RING_NILPOTENT_MONOMORPHIC_IMAGE_EQ : thm := BHoms.RING_NILPOTENT_MONOMORPHIC_IMAGE_EQ
unsafe def RING_CHAR_MONOMORPHIC_IMAGE : thm := BHoms.RING_CHAR_MONOMORPHIC_IMAGE

-- Iso
unsafe def isomorphic_ring : thm := BIso.isomorphic_ring
unsafe def RING_ISOMORPHISM_IMP_ISOMORPHIC : thm := BIso.RING_ISOMORPHISM_IMP_ISOMORPHIC
unsafe def ISOMORPHIC_RING_REFL : thm := BIso.ISOMORPHIC_RING_REFL
unsafe def ISOMORPHIC_RING_EQ : thm := BIso.ISOMORPHIC_RING_EQ
unsafe def ISOMORPHIC_RING_SYM : thm := BIso.ISOMORPHIC_RING_SYM
unsafe def ISOMORPHIC_RING_TRANS : thm := BIso.ISOMORPHIC_RING_TRANS
unsafe def ISOMORPHIC_RING_TRIVIALITY : thm := BIso.ISOMORPHIC_RING_TRIVIALITY
unsafe def ISOMORPHIC_TO_TRIVIAL_RING : thm := BIso.ISOMORPHIC_TO_TRIVIAL_RING
unsafe def ISOMORPHIC_TRIVIAL_RINGS : thm := BIso.ISOMORPHIC_TRIVIAL_RINGS
unsafe def ISOMORPHIC_RING_SINGLETON_RING : thm := BIso.ISOMORPHIC_RING_SINGLETON_RING
unsafe def CARD_LE_RING_MONOMORPHIC_IMAGE : thm := BIso.CARD_LE_RING_MONOMORPHIC_IMAGE
unsafe def CARD_LE_RING_EPIMORPHIC_IMAGE : thm := BIso.CARD_LE_RING_EPIMORPHIC_IMAGE
unsafe def CARD_EQ_RING_ISOMORPHIC_IMAGE : thm := BIso.CARD_EQ_RING_ISOMORPHIC_IMAGE
unsafe def ISOMORPHIC_RING_CARD_EQ : thm := BIso.ISOMORPHIC_RING_CARD_EQ
unsafe def ISOMORPHIC_RING_FINITENESS : thm := BIso.ISOMORPHIC_RING_FINITENESS
unsafe def ISOMORPHIC_RING_INFINITENESS : thm := BIso.ISOMORPHIC_RING_INFINITENESS
unsafe def FINITE_RING_MONOMORPHIC_PREIMAGE : thm := BIso.FINITE_RING_MONOMORPHIC_PREIMAGE
unsafe def FINITE_RING_EPIMORPHIC_IMAGE : thm := BIso.FINITE_RING_EPIMORPHIC_IMAGE
unsafe def CARD_EQ_RING_MONOMORPHIC_IMAGE : thm := BIso.CARD_EQ_RING_MONOMORPHIC_IMAGE
unsafe def ISOMORPHIC_RING_SIZE : thm := BIso.ISOMORPHIC_RING_SIZE
unsafe def ISOMORPHIC_RING_CARD : thm := BIso.ISOMORPHIC_RING_CARD
unsafe def ISOMORPHIC_RING_CHAR : thm := BIso.ISOMORPHIC_RING_CHAR
unsafe def ISOMORPHIC_TRANSPORT_OF_RING : thm := BIso.ISOMORPHIC_TRANSPORT_OF_RING
unsafe def ISOMORPHIC_COPY_OF_RING : thm := BIso.ISOMORPHIC_COPY_OF_RING
unsafe def ISOMORPHIC_SUBCOPY_OF_RING : thm := BIso.ISOMORPHIC_SUBCOPY_OF_RING

-- Kernels
unsafe def ring_kernel : thm := BKernels.ring_kernel
unsafe def ring_image : thm := BKernels.ring_image
unsafe def RING_KERNEL_0 : thm := BKernels.RING_KERNEL_0
unsafe def RING_KERNEL_NONEMPTY : thm := BKernels.RING_KERNEL_NONEMPTY
unsafe def RING_KERNEL_SUBSET_CARRIER : thm := BKernels.RING_KERNEL_SUBSET_CARRIER
unsafe def RING_MONOMORPHISM : thm := BKernels.RING_MONOMORPHISM
unsafe def RING_MONOMORPHISM_ALT : thm := BKernels.RING_MONOMORPHISM_ALT
unsafe def RING_MONOMORPHISM_ALT_EQ : thm := BKernels.RING_MONOMORPHISM_ALT_EQ
unsafe def RING_EPIMORPHISM : thm := BKernels.RING_EPIMORPHISM
unsafe def RING_EPIMORPHISM_ALT : thm := BKernels.RING_EPIMORPHISM_ALT
unsafe def RING_ISOMORPHISM_RING_KERNEL_RING_IMAGE : thm := BKernels.RING_ISOMORPHISM_RING_KERNEL_RING_IMAGE
unsafe def RING_ISOMORPHISM_ALT : thm := BKernels.RING_ISOMORPHISM_ALT
unsafe def CARD_EQ_RING_IMAGE_KERNEL : thm := BKernels.CARD_EQ_RING_IMAGE_KERNEL
unsafe def RING_IDEAL_RING_KERNEL : thm := BKernels.RING_IDEAL_RING_KERNEL
unsafe def SUBRING_RING_IMAGE : thm := BKernels.SUBRING_RING_IMAGE
unsafe def RING_KERNEL_TO_SUBRING_GENERATED : thm := BKernels.RING_KERNEL_TO_SUBRING_GENERATED
unsafe def RING_IMAGE_TO_SUBRING_GENERATED : thm := BKernels.RING_IMAGE_TO_SUBRING_GENERATED
unsafe def RING_KERNEL_FROM_SUBRING_GENERATED : thm := BKernels.RING_KERNEL_FROM_SUBRING_GENERATED
unsafe def RING_IMAGE_FROM_SUBRING_GENERATED : thm := BKernels.RING_IMAGE_FROM_SUBRING_GENERATED
unsafe def RING_ISOMORPHISM_ONTO_IMAGE : thm := BKernels.RING_ISOMORPHISM_ONTO_IMAGE
unsafe def SUBRING_IMP_MONOMORPHIC_PROPERTY : thm := BKernels.SUBRING_IMP_MONOMORPHIC_PROPERTY
unsafe def RING_KERNEL_FROM_TRIVIAL_RING : thm := BKernels.RING_KERNEL_FROM_TRIVIAL_RING
unsafe def RING_IMAGE_FROM_TRIVIAL_RING : thm := BKernels.RING_IMAGE_FROM_TRIVIAL_RING
unsafe def RING_KERNEL_TO_TRIVIAL_RING : thm := BKernels.RING_KERNEL_TO_TRIVIAL_RING
unsafe def RING_IMAGE_TO_TRIVIAL_RING : thm := BKernels.RING_IMAGE_TO_TRIVIAL_RING
unsafe def RING_HOMOMORPHISM_PREIMAGE_IMAGE_GEN : thm := BKernels.RING_HOMOMORPHISM_PREIMAGE_IMAGE_GEN
unsafe def RING_HOMOMORPHISM_IMAGE_PREIMAGE : thm := BKernels.RING_HOMOMORPHISM_IMAGE_PREIMAGE
unsafe def RING_HOMOMORPHISM_PREIMAGE_IMAGE : thm := BKernels.RING_HOMOMORPHISM_PREIMAGE_IMAGE
unsafe def RING_HOMOMORPHISM_IMAGE_PREIMAGE_EQ : thm := BKernels.RING_HOMOMORPHISM_IMAGE_PREIMAGE_EQ
unsafe def RING_EPIMORPHISM_IDEAL_CORRESPONDENCE : thm := BKernels.RING_EPIMORPHISM_IDEAL_CORRESPONDENCE
unsafe def RING_EPIMORPHISM_SUBRING_CORRESPONDENCE : thm := BKernels.RING_EPIMORPHISM_SUBRING_CORRESPONDENCE
unsafe def RING_EPIMORPHISM_IDEAL_CORRESPONDENCE_ALT : thm := BKernels.RING_EPIMORPHISM_IDEAL_CORRESPONDENCE_ALT
unsafe def RING_EPIMORPHISM_SUBRING_CORRESPONDENCE_ALT : thm := BKernels.RING_EPIMORPHISM_SUBRING_CORRESPONDENCE_ALT
unsafe def RING_IDEAL_ISOMORPHIC_IMAGE_EQ : thm := BKernels.RING_IDEAL_ISOMORPHIC_IMAGE_EQ
unsafe def RING_DIVIDES_HOMOMORPHIC_IMAGE : thm := BKernels.RING_DIVIDES_HOMOMORPHIC_IMAGE
unsafe def RING_ASSOCIATES_HOMOMORPHIC_IMAGE : thm := BKernels.RING_ASSOCIATES_HOMOMORPHIC_IMAGE
unsafe def RING_UNIT_HOMOMORPHIC_IMAGE : thm := BKernels.RING_UNIT_HOMOMORPHIC_IMAGE
unsafe def RING_DIVIDES_ISOMORPHIC_IMAGE_EQ : thm := BKernels.RING_DIVIDES_ISOMORPHIC_IMAGE_EQ
unsafe def RING_ASSOCIATES_ISOMORPHIC_IMAGE_EQ : thm := BKernels.RING_ASSOCIATES_ISOMORPHIC_IMAGE_EQ
unsafe def RING_UNIT_ISOMORPHIC_IMAGE_EQ : thm := BKernels.RING_UNIT_ISOMORPHIC_IMAGE_EQ
unsafe def RING_ZERODIVISOR_MONOMORPHIC_IMAGE : thm := BKernels.RING_ZERODIVISOR_MONOMORPHIC_IMAGE
unsafe def RING_ZERODIVISOR_ISOMORPHIC_IMAGE_EQ : thm := BKernels.RING_ZERODIVISOR_ISOMORPHIC_IMAGE_EQ
unsafe def RING_REGULAR_ISOMORPHIC_IMAGE_EQ : thm := BKernels.RING_REGULAR_ISOMORPHIC_IMAGE_EQ
unsafe def ISOMORPHIC_RING_INTEGRAL_DOMAINNESS : thm := BKernels.ISOMORPHIC_RING_INTEGRAL_DOMAINNESS
unsafe def INTEGRAL_DOMAIN_MONOMORPHIC_PREIMAGE : thm := BKernels.INTEGRAL_DOMAIN_MONOMORPHIC_PREIMAGE
unsafe def FIELD_EPIMORPHIC_IMAGE : thm := BKernels.FIELD_EPIMORPHIC_IMAGE
unsafe def ISOMORPHIC_RING_FIELDNESS : thm := BKernels.ISOMORPHIC_RING_FIELDNESS
unsafe def RING_HOMOMORPHISM_EPIMORPHISM_FACTOR : thm := BKernels.RING_HOMOMORPHISM_EPIMORPHISM_FACTOR

-- ProdRings
unsafe def prod_ring : thm := BProdRings.prod_ring
unsafe def PROD_RING : thm := BProdRings.PROD_RING
unsafe def RING_HOMOMORPHISM_PAIRWISE : thm := BProdRings.RING_HOMOMORPHISM_PAIRWISE
unsafe def RING_HOMOMORPHISM_PAIRED : thm := BProdRings.RING_HOMOMORPHISM_PAIRED
unsafe def RING_HOMOMORPHISM_DIAG : thm := BProdRings.RING_HOMOMORPHISM_DIAG
unsafe def RING_MONOMORPHISM_DIAG : thm := BProdRings.RING_MONOMORPHISM_DIAG
unsafe def RING_HOMOMORPHISM_PAIRED2 : thm := BProdRings.RING_HOMOMORPHISM_PAIRED2
unsafe def RING_ISOMORPHISMS_PAIRED2 : thm := BProdRings.RING_ISOMORPHISMS_PAIRED2
unsafe def RING_ISOMORPHISM_PAIRED2 : thm := BProdRings.RING_ISOMORPHISM_PAIRED2
unsafe def ISOMORPHIC_RING_PROD_RINGS : thm := BProdRings.ISOMORPHIC_RING_PROD_RINGS
unsafe def RING_HOMOMORPHISM_OF_FST : thm := BProdRings.RING_HOMOMORPHISM_OF_FST
unsafe def RING_HOMOMORPHISM_OF_SND : thm := BProdRings.RING_HOMOMORPHISM_OF_SND
unsafe def RING_EPIMORPHISM_OF_FST : thm := BProdRings.RING_EPIMORPHISM_OF_FST
unsafe def RING_EPIMORPHISM_OF_SND : thm := BProdRings.RING_EPIMORPHISM_OF_SND
unsafe def RING_HOMOMORPHISM_FST : thm := BProdRings.RING_HOMOMORPHISM_FST
unsafe def RING_HOMOMORPHISM_SND : thm := BProdRings.RING_HOMOMORPHISM_SND
unsafe def RING_EPIMORPHISM_FST : thm := BProdRings.RING_EPIMORPHISM_FST
unsafe def RING_EPIMORPHISM_SND : thm := BProdRings.RING_EPIMORPHISM_SND
unsafe def RING_ISOMORPHISM_FST : thm := BProdRings.RING_ISOMORPHISM_FST
unsafe def RING_ISOMORPHISM_SND : thm := BProdRings.RING_ISOMORPHISM_SND
unsafe def RING_ISOMORPHISMS_PROD_RING_SWAP : thm := BProdRings.RING_ISOMORPHISMS_PROD_RING_SWAP
unsafe def ISOMORPHIC_RING_PROD_RING_SYM : thm := BProdRings.ISOMORPHIC_RING_PROD_RING_SYM
unsafe def ISOMORPHIC_RING_PROD_RING_SWAP_LEFT : thm := BProdRings.ISOMORPHIC_RING_PROD_RING_SWAP_LEFT
unsafe def ISOMORPHIC_RING_PROD_RING_SWAP_RIGHT : thm := BProdRings.ISOMORPHIC_RING_PROD_RING_SWAP_RIGHT
unsafe def ISOMORPHIC_PROD_TRIVIAL_RING : thm := BProdRings.ISOMORPHIC_PROD_TRIVIAL_RING
unsafe def TRIVIAL_PROD_RING : thm := BProdRings.TRIVIAL_PROD_RING
unsafe def FINITE_PROD_RING : thm := BProdRings.FINITE_PROD_RING
unsafe def CROSS_SUBRING_OF_PROD_RING : thm := BProdRings.CROSS_SUBRING_OF_PROD_RING
unsafe def PROD_RING_SUBRING_GENERATED : thm := BProdRings.PROD_RING_SUBRING_GENERATED
unsafe def RING_IDEAL_CROSS : thm := BProdRings.RING_IDEAL_CROSS
unsafe def RING_IDEAL_PROD_RING : thm := BProdRings.RING_IDEAL_PROD_RING
unsafe def IDEAL_GENERATED_PAIRWISE : thm := BProdRings.IDEAL_GENERATED_PAIRWISE
unsafe def IDEAL_GENERATED_CROSS : thm := BProdRings.IDEAL_GENERATED_CROSS
unsafe def RING_POW_PROD_RING : thm := BProdRings.RING_POW_PROD_RING
unsafe def RING_DIVIDES_PROD_RING : thm := BProdRings.RING_DIVIDES_PROD_RING
unsafe def RING_OF_NUM_PROD_RING : thm := BProdRings.RING_OF_NUM_PROD_RING
unsafe def RING_OF_INT_PROD_RING : thm := BProdRings.RING_OF_INT_PROD_RING
unsafe def RING_ASSOCIATES_PROD_RING : thm := BProdRings.RING_ASSOCIATES_PROD_RING
unsafe def RING_ZERODIVISOR_PROD_RING : thm := BProdRings.RING_ZERODIVISOR_PROD_RING
unsafe def RING_REGULAR_PROD_RING : thm := BProdRings.RING_REGULAR_PROD_RING
unsafe def RING_NILPOTENT_PROD_RING : thm := BProdRings.RING_NILPOTENT_PROD_RING
unsafe def product_ring : thm := BProdRings.product_ring
unsafe def PRODUCT_RING : thm := BProdRings.PRODUCT_RING
unsafe def TRIVIAL_PRODUCT_RING : thm := BProdRings.TRIVIAL_PRODUCT_RING
unsafe def ISOMORPHIC_RING_PRODUCT_RING : thm := BProdRings.ISOMORPHIC_RING_PRODUCT_RING
unsafe def RING_HOMOMORPHISM_COMPONENTWISE : thm := BProdRings.RING_HOMOMORPHISM_COMPONENTWISE
unsafe def RING_HOMOMORPHISM_COMPONENTWISE_UNIV : thm := BProdRings.RING_HOMOMORPHISM_COMPONENTWISE_UNIV
unsafe def RING_PRODUCT_INJECTION : thm := BProdRings.RING_PRODUCT_INJECTION
unsafe def RING_HOMOMORPHISM_DIAGONAL : thm := BProdRings.RING_HOMOMORPHISM_DIAGONAL
unsafe def RING_HOMOMORPHISM_DIAGONAL_UNIV : thm := BProdRings.RING_HOMOMORPHISM_DIAGONAL_UNIV
unsafe def RING_MONOMORPHISM_DIAGONAL : thm := BProdRings.RING_MONOMORPHISM_DIAGONAL
unsafe def RING_MONOMORPHISM_DIAGONAL_UNIV : thm := BProdRings.RING_MONOMORPHISM_DIAGONAL_UNIV
unsafe def RING_HOMOMORPHISM_PRODUCT_PROJECTION : thm := BProdRings.RING_HOMOMORPHISM_PRODUCT_PROJECTION
unsafe def RING_EPIMORPHISM_PRODUCT_PROJECTION : thm := BProdRings.RING_EPIMORPHISM_PRODUCT_PROJECTION
unsafe def RING_ISOMORPHISM_PRODUCT_PROJECTION : thm := BProdRings.RING_ISOMORPHISM_PRODUCT_PROJECTION
unsafe def CARTESIAN_PRODUCT_SUBRING_OF_PRODUCT_RING : thm := BProdRings.CARTESIAN_PRODUCT_SUBRING_OF_PRODUCT_RING
unsafe def PRODUCT_RING_SUBRING_GENERATED : thm := BProdRings.PRODUCT_RING_SUBRING_GENERATED
unsafe def FINITE_PRODUCT_RING : thm := BProdRings.FINITE_PRODUCT_RING
unsafe def RING_IDEAL_CARTESIAN_PRODUCT : thm := BProdRings.RING_IDEAL_CARTESIAN_PRODUCT
unsafe def RING_SUM_PRODUCT_RING : thm := BProdRings.RING_SUM_PRODUCT_RING
unsafe def RING_IDEAL_PRODUCT_RING : thm := BProdRings.RING_IDEAL_PRODUCT_RING
unsafe def IDEAL_GENERATED_COMPONENTWISE : thm := BProdRings.IDEAL_GENERATED_COMPONENTWISE
unsafe def IDEAL_GENERATED_CARTESIAN_PRODUCT : thm := BProdRings.IDEAL_GENERATED_CARTESIAN_PRODUCT
unsafe def RING_POW_PRODUCT_RING : thm := BProdRings.RING_POW_PRODUCT_RING
unsafe def RING_DIVIDES_PRODUCT_RING : thm := BProdRings.RING_DIVIDES_PRODUCT_RING
unsafe def RING_ASSOCIATES_PRODUCT_RING : thm := BProdRings.RING_ASSOCIATES_PRODUCT_RING
unsafe def RING_ZERODIVISOR_PRODUCT_RING : thm := BProdRings.RING_ZERODIVISOR_PRODUCT_RING
unsafe def RING_REGULAR_PRODUCT_RING : thm := BProdRings.RING_REGULAR_PRODUCT_RING
unsafe def RING_NILPOTENT_PRODUCT_RING_GEN : thm := BProdRings.RING_NILPOTENT_PRODUCT_RING_GEN
unsafe def RING_NILPOTENT_PRODUCT_RING : thm := BProdRings.RING_NILPOTENT_PRODUCT_RING
unsafe def ISOMORPHIC_PRODUCT_RING_DISJOINT_UNION : thm := BProdRings.ISOMORPHIC_PRODUCT_RING_DISJOINT_UNION
unsafe def ISOMORPHIC_PRODUCT_RING_SING : thm := BProdRings.ISOMORPHIC_PRODUCT_RING_SING
unsafe def ISOMORPHIC_PRODUCT_RING_SUPPORT : thm := BProdRings.ISOMORPHIC_PRODUCT_RING_SUPPORT
unsafe def ISOMORPHIC_PRODUCT_RING_SYMDIFF : thm := BProdRings.ISOMORPHIC_PRODUCT_RING_SYMDIFF
unsafe def ISOMORPHIC_PRODUCT_RING_BIJECTIONS : thm := BProdRings.ISOMORPHIC_PRODUCT_RING_BIJECTIONS
unsafe def RING_ISOMORPHISMS_PRODUCT_RING_DISJOINT_UNION : thm := BProdRings.RING_ISOMORPHISMS_PRODUCT_RING_DISJOINT_UNION
unsafe def RING_ISOMORPHISM_PRODUCT_RING_DISJOINT_UNION : thm := BProdRings.RING_ISOMORPHISM_PRODUCT_RING_DISJOINT_UNION
unsafe def ISOMORPHIC_PRODUCT_RING_INSERT : thm := BProdRings.ISOMORPHIC_PRODUCT_RING_INSERT

-- Limits
unsafe def RING_DIRECT_LIMIT : thm := BLimits.RING_DIRECT_LIMIT
unsafe def RING_MONOMORPHIC_IMAGE_RULE := BLimits.RING_MONOMORPHIC_IMAGE_RULE

-- RingRule
unsafe def RING_RULE : term → IO (Except String thm) := fun t => (BRingRule.RING_RULE t).run
unsafe def RING_TAC : HolCore.Tactics.tactic := fun g => BRingRule.RING_TAC g

-- Cosets
unsafe def ring_coset : thm := BCosets.ring_coset
unsafe def RING_COSET_SETADD : thm := BCosets.RING_COSET_SETADD
unsafe def RING_COSET : thm := BCosets.RING_COSET
unsafe def RING_COSET_0 : thm := BCosets.RING_COSET_0
unsafe def RING_COSET_TRIVIAL : thm := BCosets.RING_COSET_TRIVIAL
unsafe def RING_COSET_CARRIER : thm := BCosets.RING_COSET_CARRIER
unsafe def RING_COSET_EQ : thm := BCosets.RING_COSET_EQ
unsafe def RING_COSET_EQ_IDEAL : thm := BCosets.RING_COSET_EQ_IDEAL
unsafe def RING_COSET_EQ_EMPTY : thm := BCosets.RING_COSET_EQ_EMPTY
unsafe def RING_COSET_NONEMPTY : thm := BCosets.RING_COSET_NONEMPTY
unsafe def IN_RING_COSET_SELF : thm := BCosets.IN_RING_COSET_SELF
unsafe def UNIONS_RING_COSETS : thm := BCosets.UNIONS_RING_COSETS
unsafe def RING_COSETS_EQ : thm := BCosets.RING_COSETS_EQ
unsafe def IN_RING_COSET : thm := BCosets.IN_RING_COSET
unsafe def RING_COSET_RELATIONAL : thm := BCosets.RING_COSET_RELATIONAL
unsafe def DISJOINT_RING_COSETS : thm := BCosets.DISJOINT_RING_COSETS
unsafe def PAIRWISE_DISJOINT_RING_COSETS : thm := BCosets.PAIRWISE_DISJOINT_RING_COSETS
unsafe def IMAGE_RING_COSET_SWITCH : thm := BCosets.IMAGE_RING_COSET_SWITCH
unsafe def CARD_EQ_RING_COSETS : thm := BCosets.CARD_EQ_RING_COSETS
unsafe def CARD_EQ_RING_COSET_IDEAL : thm := BCosets.CARD_EQ_RING_COSET_IDEAL
unsafe def LAGRANGE_THEOREM_RING_EXPLICIT : thm := BCosets.LAGRANGE_THEOREM_RING_EXPLICIT
unsafe def LAGRANGE_THEOREM_RING : thm := BCosets.LAGRANGE_THEOREM_RING
unsafe def PRIME_SUBRING_FINITE : thm := BCosets.PRIME_SUBRING_FINITE
unsafe def HAS_SIZE_PRIME_SUBRING : thm := BCosets.HAS_SIZE_PRIME_SUBRING
unsafe def CARD_PRIME_SUBRING : thm := BCosets.CARD_PRIME_SUBRING
unsafe def FINITE_PRIME_SUBRING : thm := BCosets.FINITE_PRIME_SUBRING
unsafe def RING_CHAR_DIVIDES_ORDER : thm := BCosets.RING_CHAR_DIVIDES_ORDER
unsafe def CARD_DIVIDES_RING_MONOMORPHIC_IMAGE : thm := BCosets.CARD_DIVIDES_RING_MONOMORPHIC_IMAGE
unsafe def CARD_DIVIDES_RING_EPIMORPHIC_IMAGE : thm := BCosets.CARD_DIVIDES_RING_EPIMORPHIC_IMAGE
unsafe def CARD_RING_COSETS_DIVIDES : thm := BCosets.CARD_RING_COSETS_DIVIDES
unsafe def RING_SETADD_PROD_RING : thm := BCosets.RING_SETADD_PROD_RING
unsafe def RING_COSET_PROD_RING : thm := BCosets.RING_COSET_PROD_RING
unsafe def RING_SETADD_PRODUCT_RING : thm := BCosets.RING_SETADD_PRODUCT_RING
unsafe def RING_COSET_PRODUCT_RING : thm := BCosets.RING_COSET_PRODUCT_RING
unsafe def RING_SETNEG_SUBRING_GENERATED : thm := BCosets.RING_SETNEG_SUBRING_GENERATED
unsafe def RING_SETADD_SUBRING_GENERATED : thm := BCosets.RING_SETADD_SUBRING_GENERATED
unsafe def RING_SETNEG_COSET : thm := BCosets.RING_SETNEG_COSET
unsafe def RING_SETADD_COSETS : thm := BCosets.RING_SETADD_COSETS
unsafe def RING_SETMUL_COSETS : thm := BCosets.RING_SETMUL_COSETS
unsafe def RING_COSET_IDEAL_GENERATED_SING : thm := BCosets.RING_COSET_IDEAL_GENERATED_SING
unsafe def RING_COSET_IDEAL_GENERATED_SING_EQ : thm := BCosets.RING_COSET_IDEAL_GENERATED_SING_EQ

-- Quotients
unsafe def quotient_ring : thm := BQuotients.quotient_ring
unsafe def RING_HOMOMORPHISM_RING_COSET : thm := BQuotients.RING_HOMOMORPHISM_RING_COSET
unsafe def QUOTIENT_RING : thm := BQuotients.QUOTIENT_RING
unsafe def RING_EPIMORPHISM_RING_COSET : thm := BQuotients.RING_EPIMORPHISM_RING_COSET
unsafe def QUOTIENT_RING_CARRIER : thm := BQuotients.QUOTIENT_RING_CARRIER
unsafe def QUOTIENT_RING_0 : thm := BQuotients.QUOTIENT_RING_0
unsafe def QUOTIENT_RING_1 : thm := BQuotients.QUOTIENT_RING_1
unsafe def QUOTIENT_RING_NEG : thm := BQuotients.QUOTIENT_RING_NEG
unsafe def QUOTIENT_RING_ADD : thm := BQuotients.QUOTIENT_RING_ADD
unsafe def QUOTIENT_RING_MUL : thm := BQuotients.QUOTIENT_RING_MUL
unsafe def RING_KERNEL_RING_COSET : thm := BQuotients.RING_KERNEL_RING_COSET
unsafe def CARD_LE_QUOTIENT_RING : thm := BQuotients.CARD_LE_QUOTIENT_RING
unsafe def CARD_QUOTIENT_RING_DIVIDES : thm := BQuotients.CARD_QUOTIENT_RING_DIVIDES
unsafe def QUOTIENT_RING_UNIVERSAL_EXPLICIT : thm := BQuotients.QUOTIENT_RING_UNIVERSAL_EXPLICIT
unsafe def QUOTIENT_RING_UNIVERSAL : thm := BQuotients.QUOTIENT_RING_UNIVERSAL
unsafe def QUOTIENT_RING_UNIVERSAL_EPIMORPHISM : thm := BQuotients.QUOTIENT_RING_UNIVERSAL_EPIMORPHISM
unsafe def FIRST_RING_ISOMORPHISM_THEOREM : thm := BQuotients.FIRST_RING_ISOMORPHISM_THEOREM
unsafe def FIRST_RING_EPIMORPHISM_THEOREM : thm := BQuotients.FIRST_RING_EPIMORPHISM_THEOREM
unsafe def SECOND_RING_ISOMORPHISM_THEOREM : thm := BQuotients.SECOND_RING_ISOMORPHISM_THEOREM
unsafe def THIRD_RING_ISOMORPHISM_THEOREM : thm := BQuotients.THIRD_RING_ISOMORPHISM_THEOREM
unsafe def QUOTIENT_RING_SUBRING_CORRESPONDENCE : thm := BQuotients.QUOTIENT_RING_SUBRING_CORRESPONDENCE
unsafe def QUOTIENT_RING_IDEAL_CORRESPONDENCE : thm := BQuotients.QUOTIENT_RING_IDEAL_CORRESPONDENCE
unsafe def FIRST_RING_ISOMORPHISM_THEOREM_GEN : thm := BQuotients.FIRST_RING_ISOMORPHISM_THEOREM_GEN
unsafe def FIRST_RING_ISOMORPHISM_THEOREM_GEN_ALT : thm := BQuotients.FIRST_RING_ISOMORPHISM_THEOREM_GEN_ALT

-- Primes
unsafe def ring_prime : thm := BPrimes.ring_prime
unsafe def ring_irreducible : thm := BPrimes.ring_irreducible
unsafe def RING_PRIME_IN_CARRIER : thm := BPrimes.RING_PRIME_IN_CARRIER
unsafe def RING_IRREDUCIBLE_IN_CARRIER : thm := BPrimes.RING_IRREDUCIBLE_IN_CARRIER
unsafe def RING_PRIME_NEG : thm := BPrimes.RING_PRIME_NEG
unsafe def RING_IRREDUCIBLE_NEG : thm := BPrimes.RING_IRREDUCIBLE_NEG
unsafe def RING_PRIME_IMP_NONTRIVIAL_RING : thm := BPrimes.RING_PRIME_IMP_NONTRIVIAL_RING
unsafe def RING_IRREDUCIBLE_IMP_NONTRIVIAL_RING : thm := BPrimes.RING_IRREDUCIBLE_IMP_NONTRIVIAL_RING
unsafe def FIELD_PRIME : thm := BPrimes.FIELD_PRIME
unsafe def FIELD_IRREDUCIBLE : thm := BPrimes.FIELD_IRREDUCIBLE
unsafe def RING_ASSOCIATES_PRIME : thm := BPrimes.RING_ASSOCIATES_PRIME
unsafe def RING_NONUNIT_DIVIDES_IRREDUCIBLE : thm := BPrimes.RING_NONUNIT_DIVIDES_IRREDUCIBLE
unsafe def RING_PRIME_DIVIDES_IRREDUCIBLE : thm := BPrimes.RING_PRIME_DIVIDES_IRREDUCIBLE
unsafe def RING_PRIME_DIVIDES_MUL : thm := BPrimes.RING_PRIME_DIVIDES_MUL
unsafe def RING_PRIME_DIVIDES_POW : thm := BPrimes.RING_PRIME_DIVIDES_POW
unsafe def RING_PRIME_DIVIDES_PRODUCT : thm := BPrimes.RING_PRIME_DIVIDES_PRODUCT
unsafe def INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE : thm := BPrimes.INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE
unsafe def INTEGRAL_DOMAIN_IRREDUCIBLE : thm := BPrimes.INTEGRAL_DOMAIN_IRREDUCIBLE
unsafe def INTEGRAL_DOMAIN_IRREDUCIBLE_ALT : thm := BPrimes.INTEGRAL_DOMAIN_IRREDUCIBLE_ALT
unsafe def INTEGRAL_DOMAIN_IRREDUCIBLE_DIVISORS : thm := BPrimes.INTEGRAL_DOMAIN_IRREDUCIBLE_DIVISORS
unsafe def RING_ASSOCIATES_IRREDUCIBLE : thm := BPrimes.RING_ASSOCIATES_IRREDUCIBLE
unsafe def INTEGRAL_DOMAIN_DIVIDES_PRIME_LMUL : thm := BPrimes.INTEGRAL_DOMAIN_DIVIDES_PRIME_LMUL
unsafe def INTEGRAL_DOMAIN_DIVIDES_PRIME_RMUL : thm := BPrimes.INTEGRAL_DOMAIN_DIVIDES_PRIME_RMUL
unsafe def RING_IRREDUCIBLE_DIVIDES_OR_COPRIME : thm := BPrimes.RING_IRREDUCIBLE_DIVIDES_OR_COPRIME
unsafe def RING_IRREDUCIBLE_COPRIME_EQ : thm := BPrimes.RING_IRREDUCIBLE_COPRIME_EQ
unsafe def RING_IRREDUCIBLES_COPRIME_OR_ASSOCIATES : thm := BPrimes.RING_IRREDUCIBLES_COPRIME_OR_ASSOCIATES
unsafe def INTEGRAL_DOMAIN_PRIME_DIVIDES_OR_COPRIME : thm := BPrimes.INTEGRAL_DOMAIN_PRIME_DIVIDES_OR_COPRIME
unsafe def INTEGRAL_DOMAIN_PRIME_COPRIME_EQ : thm := BPrimes.INTEGRAL_DOMAIN_PRIME_COPRIME_EQ
unsafe def INTEGRAL_DOMAIN_PRIMES_COPRIME_OR_ASSOCIATES : thm := BPrimes.INTEGRAL_DOMAIN_PRIMES_COPRIME_OR_ASSOCIATES
unsafe def INTEGRAL_DOMAIN_PRIMES_DIVIDES_EQ_ASSOCIATES : thm := BPrimes.INTEGRAL_DOMAIN_PRIMES_DIVIDES_EQ_ASSOCIATES
unsafe def RING_PRIME_ISOMORPHIC_IMAGE_EQ : thm := BPrimes.RING_PRIME_ISOMORPHIC_IMAGE_EQ
unsafe def RING_IRREDUCIBLE_ISOMORPHIC_IMAGE_EQ : thm := BPrimes.RING_IRREDUCIBLE_ISOMORPHIC_IMAGE_EQ
unsafe def RING_PRIME_MUL_DIVIDES : thm := BPrimes.RING_PRIME_MUL_DIVIDES
unsafe def RING_PRIME_MUL_DIVIDES_EQ : thm := BPrimes.RING_PRIME_MUL_DIVIDES_EQ
unsafe def RING_PRIME_PRODUCT_DIVIDES : thm := BPrimes.RING_PRIME_PRODUCT_DIVIDES
unsafe def INTEGRAL_DOMAIN_PRIME_PRODUCT_DIVIDES : thm := BPrimes.INTEGRAL_DOMAIN_PRIME_PRODUCT_DIVIDES

-- Factorizations
unsafe def RING_DIVIDES_PRIMEFACTS_INJECTION : thm := BFactorizations.RING_DIVIDES_PRIMEFACTS_INJECTION
unsafe def RING_DIVIDES_PRIMEFACTS_INJECTION_EQ : thm := BFactorizations.RING_DIVIDES_PRIMEFACTS_INJECTION_EQ
unsafe def RING_DIVIDES_PRIMEFACTS_LE : thm := BFactorizations.RING_DIVIDES_PRIMEFACTS_LE
unsafe def RING_ASSOCIATES_PRIMEFACTS_BIJECTION : thm := BFactorizations.RING_ASSOCIATES_PRIMEFACTS_BIJECTION
unsafe def RING_ASSOCIATES_PRIMEFACTS_BIJECTIONS : thm := BFactorizations.RING_ASSOCIATES_PRIMEFACTS_BIJECTIONS
unsafe def RING_ASSOCIATES_PRIMEFACTS_BIJECTIONS_EQ : thm := BFactorizations.RING_ASSOCIATES_PRIMEFACTS_BIJECTIONS_EQ
unsafe def RING_ASSOCIATES_PRIMEFACTS_BIJECTION_EQ : thm := BFactorizations.RING_ASSOCIATES_PRIMEFACTS_BIJECTION_EQ
unsafe def RING_ASSOCIATES_PRIMEFACTS_EQ : thm := BFactorizations.RING_ASSOCIATES_PRIMEFACTS_EQ
unsafe def RING_DIVIDES_PRIMEFACTS_LT : thm := BFactorizations.RING_DIVIDES_PRIMEFACTS_LT

-- Squarefree
unsafe def ring_squarefree : thm := BSquarefree.ring_squarefree
unsafe def RING_SQUAREFREE_IN_CARRIER : thm := BSquarefree.RING_SQUAREFREE_IN_CARRIER
unsafe def RING_UNIT_IMP_SQUAREFREE : thm := BSquarefree.RING_UNIT_IMP_SQUAREFREE
unsafe def RING_SQUAREFREE_1 : thm := BSquarefree.RING_SQUAREFREE_1
unsafe def RING_SQUAREFREE_DIVISOR : thm := BSquarefree.RING_SQUAREFREE_DIVISOR
unsafe def RING_SQUAREFREE_ASSOCIATES : thm := BSquarefree.RING_SQUAREFREE_ASSOCIATES
unsafe def RING_SQUAREFREE_0 : thm := BSquarefree.RING_SQUAREFREE_0
unsafe def RING_SQUAREFREE_IMP_NONZERO : thm := BSquarefree.RING_SQUAREFREE_IMP_NONZERO
unsafe def RING_IRREDUCIBLE_IMP_SQUAREFREE : thm := BSquarefree.RING_IRREDUCIBLE_IMP_SQUAREFREE
unsafe def RING_PRIME_IMP_SQUAREFREE : thm := BSquarefree.RING_PRIME_IMP_SQUAREFREE
unsafe def RING_SQUAREFREE_IMP_NO_PRIME_SQUARE : thm := BSquarefree.RING_SQUAREFREE_IMP_NO_PRIME_SQUARE
unsafe def RING_SQUAREFREE_COPRIME : thm := BSquarefree.RING_SQUAREFREE_COPRIME
unsafe def RING_SQUAREFREE_COPRIME_DIVISORS : thm := BSquarefree.RING_SQUAREFREE_COPRIME_DIVISORS
unsafe def RING_SQUAREFREE_MUL_IMP : thm := BSquarefree.RING_SQUAREFREE_MUL_IMP
unsafe def RING_SQUAREFREE_POW : thm := BSquarefree.RING_SQUAREFREE_POW
unsafe def ring_multsys : thm := BSquarefree.ring_multsys
unsafe def RING_MULTSYS : thm := BSquarefree.RING_MULTSYS
unsafe def RING_MULTSYS_IMP_SUBSET : thm := BSquarefree.RING_MULTSYS_IMP_SUBSET
unsafe def RING_MULTSYS_IMP_NONEMPTY : thm := BSquarefree.RING_MULTSYS_IMP_NONEMPTY
unsafe def RING_MULYSYS_1 : thm := BSquarefree.RING_MULYSYS_1
unsafe def RING_MULYSYS_CARRIER : thm := BSquarefree.RING_MULYSYS_CARRIER
unsafe def RING_MULTSYS_REGULAR : thm := BSquarefree.RING_MULTSYS_REGULAR
unsafe def RING_MULTSYS_NONZERO : thm := BSquarefree.RING_MULTSYS_NONZERO
unsafe def RING_MULTSYS_POWERS : thm := BSquarefree.RING_MULTSYS_POWERS
unsafe def RING_MULTSYS_UNITS : thm := BSquarefree.RING_MULTSYS_UNITS
unsafe def RING_MULTSYS_IDEMPOT : thm := BSquarefree.RING_MULTSYS_IDEMPOT
unsafe def RING_MULTSYS_INTERS : thm := BSquarefree.RING_MULTSYS_INTERS
unsafe def RING_MULTSYS_INTER : thm := BSquarefree.RING_MULTSYS_INTER
unsafe def RING_POW_IN_MULTSYS : thm := BSquarefree.RING_POW_IN_MULTSYS
unsafe def RING_MULTSYS_NILPOTENT_EXISTS : thm := BSquarefree.RING_MULTSYS_NILPOTENT_EXISTS

-- Localization
unsafe def ring_localequiv : thm := BLocalization.ring_localequiv
unsafe def RING_LOCALEQUIV : thm := BLocalization.RING_LOCALEQUIV
unsafe def RING_LOCALEQUIV_REFL : thm := BLocalization.RING_LOCALEQUIV_REFL
unsafe def RING_LOCALEQUIV_SYM : thm := BLocalization.RING_LOCALEQUIV_SYM
unsafe def RING_LOCALEQUIV_TRANS : thm := BLocalization.RING_LOCALEQUIV_TRANS
unsafe def RING_LOCALEQUIV_EQUIV : thm := BLocalization.RING_LOCALEQUIV_EQUIV
unsafe def RING_LOCALEQUIV_NEG : thm := BLocalization.RING_LOCALEQUIV_NEG
unsafe def RING_LOCALEQUIV_ADD : thm := BLocalization.RING_LOCALEQUIV_ADD
unsafe def RING_LOCALEQUIV_MUL : thm := BLocalization.RING_LOCALEQUIV_MUL
unsafe def ring_localization : thm := BLocalization.ring_localization
unsafe def RING_LOCALIZATION : thm := BLocalization.RING_LOCALIZATION
unsafe def RING_LOCALIZATION_NEG : thm := BLocalization.RING_LOCALIZATION_NEG
unsafe def RING_LOCALIZATION_ADD : thm := BLocalization.RING_LOCALIZATION_ADD
unsafe def RING_LOCALIZATION_MUL : thm := BLocalization.RING_LOCALIZATION_MUL
unsafe def RING_LOCALIZATION_CARRIER : thm := BLocalization.RING_LOCALIZATION_CARRIER
unsafe def RING_LOCALIZATION_0 : thm := BLocalization.RING_LOCALIZATION_0
unsafe def RING_LOCALIZATION_1 : thm := BLocalization.RING_LOCALIZATION_1
unsafe def TRIVIAL_RING_LOCALIZATION : thm := BLocalization.TRIVIAL_RING_LOCALIZATION
unsafe def RING_LOCALEQUIV_IN_CARRIER : thm := BLocalization.RING_LOCALEQUIV_IN_CARRIER
unsafe def RING_UNIT_LOCALEQUIV : thm := BLocalization.RING_UNIT_LOCALEQUIV
unsafe def RING_UNIT_LOCALEQUIV_EQ : thm := BLocalization.RING_UNIT_LOCALEQUIV_EQ
unsafe def RING_UNIT_LOCALIZATION : thm := BLocalization.RING_UNIT_LOCALIZATION
unsafe def RING_LOCALEQUIV_EQ_0_GEN : thm := BLocalization.RING_LOCALEQUIV_EQ_0_GEN
unsafe def RING_IDEAL_LOCALIZATION : thm := BLocalization.RING_IDEAL_LOCALIZATION
unsafe def ring_fractionate : thm := BLocalization.ring_fractionate
unsafe def RING_FRACTIONATE_IN_CARRIER : thm := BLocalization.RING_FRACTIONATE_IN_CARRIER
unsafe def RING_UNIT_FRACTIONATE : thm := BLocalization.RING_UNIT_FRACTIONATE
unsafe def RING_FRACTIONATE_EQ_0_GEN : thm := BLocalization.RING_FRACTIONATE_EQ_0_GEN
unsafe def RING_HOMOMORPHISM_FRACTIONATE : thm := BLocalization.RING_HOMOMORPHISM_FRACTIONATE
unsafe def RING_MONOMORPHISM_FRACTIONATE_GEN : thm := BLocalization.RING_MONOMORPHISM_FRACTIONATE_GEN
unsafe def RING_ISOMORPHISM_FRACTIONATE_GEN : thm := BLocalization.RING_ISOMORPHISM_FRACTIONATE_GEN
unsafe def RING_LOCALIZATION_UNCHANGED : thm := BLocalization.RING_LOCALIZATION_UNCHANGED
unsafe def RING_LOCALIZATION_UNIVERSAL : thm := BLocalization.RING_LOCALIZATION_UNIVERSAL
unsafe def RING_LOCALEQUIV_SPLIT_EXPLICIT : thm := BLocalization.RING_LOCALEQUIV_SPLIT_EXPLICIT
unsafe def RING_LOCALEQUIV_SPLIT : thm := BLocalization.RING_LOCALEQUIV_SPLIT
unsafe def LOCALEQUIV_MUL_RCANCEL : thm := BLocalization.LOCALEQUIV_MUL_RCANCEL
unsafe def LOCALEQUIV_MUL_LCANCEL : thm := BLocalization.LOCALEQUIV_MUL_LCANCEL
unsafe def RING_LOCALIZATION_HOMOMORPHISM_UNIQUE : thm := BLocalization.RING_LOCALIZATION_HOMOMORPHISM_UNIQUE
unsafe def RING_LOCALIZATION_UNIQUE : thm := BLocalization.RING_LOCALIZATION_UNIQUE
unsafe def IDEAL_LOCALIZATION_CONTRACTION : thm := BLocalization.IDEAL_LOCALIZATION_CONTRACTION
unsafe def IDEAL_GENERATED_RING_LOCALIZATION : thm := BLocalization.IDEAL_GENERATED_RING_LOCALIZATION
unsafe def fraction_ring : thm := BLocalization.fraction_ring
unsafe def RING_LOCALEQUIV_EQ_0 : thm := BLocalization.RING_LOCALEQUIV_EQ_0
unsafe def RING_FRACTIONATE_EQ_0 : thm := BLocalization.RING_FRACTIONATE_EQ_0
unsafe def RING_MONOMORPHISM_FRACTIONATE : thm := BLocalization.RING_MONOMORPHISM_FRACTIONATE
unsafe def FRACTION_RING_UNIVERSAL : thm := BLocalization.FRACTION_RING_UNIVERSAL
unsafe def RING_UNIT_FRACTION_RING : thm := BLocalization.RING_UNIT_FRACTION_RING
unsafe def RING_ZERODIVISOR_FRACTION_RING : thm := BLocalization.RING_ZERODIVISOR_FRACTION_RING
unsafe def FRACTION_RING_UNIT_EQ_REGULAR : thm := BLocalization.FRACTION_RING_UNIT_EQ_REGULAR
unsafe def FRACTION_RING_UNIT_OR_ZERODIVISOR : thm := BLocalization.FRACTION_RING_UNIT_OR_ZERODIVISOR
unsafe def TRIVIAL_FRACTION_RING : thm := BLocalization.TRIVIAL_FRACTION_RING
unsafe def FRACTION_FIELD : thm := BLocalization.FRACTION_FIELD
unsafe def FRACTION_DOMAIN : thm := BLocalization.FRACTION_DOMAIN
unsafe def INTEGRAL_DOMAIN_LOCALIZATION : thm := BLocalization.INTEGRAL_DOMAIN_LOCALIZATION

-- SpecialIdeals
unsafe def proper_ideal : thm := BSpecialIdeals.proper_ideal
unsafe def principal_ideal : thm := BSpecialIdeals.principal_ideal
unsafe def finitely_generated_ideal : thm := BSpecialIdeals.finitely_generated_ideal
unsafe def prime_ideal : thm := BSpecialIdeals.prime_ideal
unsafe def maximal_ideal : thm := BSpecialIdeals.maximal_ideal
unsafe def PID : thm := BSpecialIdeals.PID
unsafe def noetherian_ring : thm := BSpecialIdeals.noetherian_ring
unsafe def PROPER_IMP_RING_IDEAL : thm := BSpecialIdeals.PROPER_IMP_RING_IDEAL
unsafe def PROPER_IDEAL_IMP_SUBSET : thm := BSpecialIdeals.PROPER_IDEAL_IMP_SUBSET
unsafe def PROPER_IDEAL_IMP_PSUBSET : thm := BSpecialIdeals.PROPER_IDEAL_IMP_PSUBSET
unsafe def PRINCIPAL_IMP_RING_IDEAL : thm := BSpecialIdeals.PRINCIPAL_IMP_RING_IDEAL
unsafe def PRINCIPAL_IDEAL_IMP_SUBSET : thm := BSpecialIdeals.PRINCIPAL_IDEAL_IMP_SUBSET
unsafe def FINITELY_GENERATED_IMP_RING_IDEAL : thm := BSpecialIdeals.FINITELY_GENERATED_IMP_RING_IDEAL
unsafe def FINITELY_GENERATED_IDEAL_IMP_SUBSET : thm := BSpecialIdeals.FINITELY_GENERATED_IDEAL_IMP_SUBSET
unsafe def FINITELY_GENERATED_IDEAL_SUBSET : thm := BSpecialIdeals.FINITELY_GENERATED_IDEAL_SUBSET
unsafe def PRIME_IMP_PROPER_IDEAL : thm := BSpecialIdeals.PRIME_IMP_PROPER_IDEAL
unsafe def PRIME_IMP_RING_IDEAL : thm := BSpecialIdeals.PRIME_IMP_RING_IDEAL
unsafe def PRIME_IDEAL_IMP_SUBSET : thm := BSpecialIdeals.PRIME_IDEAL_IMP_SUBSET
unsafe def PRIME_IDEAL_IMP_PSUBSET : thm := BSpecialIdeals.PRIME_IDEAL_IMP_PSUBSET
unsafe def MAXIMAL_IMP_PROPER_IDEAL : thm := BSpecialIdeals.MAXIMAL_IMP_PROPER_IDEAL
unsafe def MAXIMAL_IMP_RING_IDEAL : thm := BSpecialIdeals.MAXIMAL_IMP_RING_IDEAL
unsafe def MAXIMAL_IDEAL_IMP_SUBSET : thm := BSpecialIdeals.MAXIMAL_IDEAL_IMP_SUBSET
unsafe def MAXIMAL_IDEAL_IMP_PSUBSET : thm := BSpecialIdeals.MAXIMAL_IDEAL_IMP_PSUBSET
unsafe def PROPER_IDEAL_0 : thm := BSpecialIdeals.PROPER_IDEAL_0
unsafe def PRINCIPAL_IMP_FINITELY_GENERATED_IDEAL : thm := BSpecialIdeals.PRINCIPAL_IMP_FINITELY_GENERATED_IDEAL
unsafe def PID_IMP_INTEGRAL_DOMAIN : thm := BSpecialIdeals.PID_IMP_INTEGRAL_DOMAIN
unsafe def PID_IMP_NOETHERIAN_RING : thm := BSpecialIdeals.PID_IMP_NOETHERIAN_RING
unsafe def PRINCIPAL_IDEAL_ALT : thm := BSpecialIdeals.PRINCIPAL_IDEAL_ALT
unsafe def PRINCIPAL_IDEAL_IDEAL_GENERATED_SING : thm := BSpecialIdeals.PRINCIPAL_IDEAL_IDEAL_GENERATED_SING
unsafe def PRINCIPAL_IDEAL_0 : thm := BSpecialIdeals.PRINCIPAL_IDEAL_0
unsafe def FINITELY_GENERATED_IDEAL_0 : thm := BSpecialIdeals.FINITELY_GENERATED_IDEAL_0
unsafe def PRINCIPAL_IDEAL_CARRIER : thm := BSpecialIdeals.PRINCIPAL_IDEAL_CARRIER
unsafe def FINITELY_GENERATED_IDEAL_CARRIER : thm := BSpecialIdeals.FINITELY_GENERATED_IDEAL_CARRIER
unsafe def PROPER_IDEAL_ALT : thm := BSpecialIdeals.PROPER_IDEAL_ALT
unsafe def NONPRINCIPAL_IMP_PROPER_IDEAL : thm := BSpecialIdeals.NONPRINCIPAL_IMP_PROPER_IDEAL
unsafe def NONFINITELY_GENERATED_IMP_PROPER_IDEAL : thm := BSpecialIdeals.NONFINITELY_GENERATED_IMP_PROPER_IDEAL
unsafe def FINITELY_GENERATED_IDEAL_ALT : thm := BSpecialIdeals.FINITELY_GENERATED_IDEAL_ALT
unsafe def FINITELY_GENERATED_IDEAL_GENERATED : thm := BSpecialIdeals.FINITELY_GENERATED_IDEAL_GENERATED
unsafe def FINITELY_GENERATED_IDEAL_SETADD : thm := BSpecialIdeals.FINITELY_GENERATED_IDEAL_SETADD
unsafe def PROPER_IDEAL : thm := BSpecialIdeals.PROPER_IDEAL
unsafe def PROPER_IDEAL_UNIT : thm := BSpecialIdeals.PROPER_IDEAL_UNIT
unsafe def PROPER_IDEAL_SUBSET_NONUNITS : thm := BSpecialIdeals.PROPER_IDEAL_SUBSET_NONUNITS
unsafe def PROPER_IDEAL_UNIONS : thm := BSpecialIdeals.PROPER_IDEAL_UNIONS
unsafe def PROPER_IDEAL_EXISTS : thm := BSpecialIdeals.PROPER_IDEAL_EXISTS
unsafe def FINITELY_GENERATED_IDEAL_EPIMORPHIC_IMAGE : thm := BSpecialIdeals.FINITELY_GENERATED_IDEAL_EPIMORPHIC_IMAGE
unsafe def PRINCIPAL_IDEAL_EPIMORPHIC_IMAGE : thm := BSpecialIdeals.PRINCIPAL_IDEAL_EPIMORPHIC_IMAGE
unsafe def FINITELY_GENERATED_IDEAL_LOCALIZATION : thm := BSpecialIdeals.FINITELY_GENERATED_IDEAL_LOCALIZATION
unsafe def PRINCIPAL_IDEAL_LOCALIZATION : thm := BSpecialIdeals.PRINCIPAL_IDEAL_LOCALIZATION
unsafe def PROPER_IDEAL_HOMOMORPHIC_PREIMAGE : thm := BSpecialIdeals.PROPER_IDEAL_HOMOMORPHIC_PREIMAGE
unsafe def PROPER_IDEAL_CORRESPONDENCE : thm := BSpecialIdeals.PROPER_IDEAL_CORRESPONDENCE
unsafe def PROPER_IDEAL_ISOMORPHIC_IMAGE_EQ : thm := BSpecialIdeals.PROPER_IDEAL_ISOMORPHIC_IMAGE_EQ
unsafe def PRIME_IDEAL_HOMOMORPHIC_PREIMAGE : thm := BSpecialIdeals.PRIME_IDEAL_HOMOMORPHIC_PREIMAGE
unsafe def RING_1_NOT_IN_PRIME_IDEAL : thm := BSpecialIdeals.RING_1_NOT_IN_PRIME_IDEAL
unsafe def RING_UNIT_NOT_IN_PRIME_IDEAL : thm := BSpecialIdeals.RING_UNIT_NOT_IN_PRIME_IDEAL
unsafe def RING_MUL_IN_PRIME_IDEAL : thm := BSpecialIdeals.RING_MUL_IN_PRIME_IDEAL
unsafe def RING_POW_IN_PRIME_IDEAL : thm := BSpecialIdeals.RING_POW_IN_PRIME_IDEAL
unsafe def MAXIMAL_SUPERIDEAL_EXISTS : thm := BSpecialIdeals.MAXIMAL_SUPERIDEAL_EXISTS
unsafe def MAXIMAL_IDEAL_EXISTS : thm := BSpecialIdeals.MAXIMAL_IDEAL_EXISTS
unsafe def RING_MULTSYS_NONPRIME : thm := BSpecialIdeals.RING_MULTSYS_NONPRIME
unsafe def RING_MULTSYS_NONPRIME_EQ : thm := BSpecialIdeals.RING_MULTSYS_NONPRIME_EQ
unsafe def RING_SATURATED_MULTSYS_NONPRIME : thm := BSpecialIdeals.RING_SATURATED_MULTSYS_NONPRIME
unsafe def MAXIMAL_EXCLUDING_IMP_PRIME_IDEAL : thm := BSpecialIdeals.MAXIMAL_EXCLUDING_IMP_PRIME_IDEAL
unsafe def MAXIMAL_IMP_PRIME_IDEAL : thm := BSpecialIdeals.MAXIMAL_IMP_PRIME_IDEAL
unsafe def MAXIMAL_AMONG_PRIME_IDEALS : thm := BSpecialIdeals.MAXIMAL_AMONG_PRIME_IDEALS
unsafe def PRIME_IDEAL_0 : thm := BSpecialIdeals.PRIME_IDEAL_0
unsafe def MAXIMAL_IDEAL_0 : thm := BSpecialIdeals.MAXIMAL_IDEAL_0
unsafe def PRIME_SUPERIDEAL_EXISTS : thm := BSpecialIdeals.PRIME_SUPERIDEAL_EXISTS
unsafe def PRIME_IDEAL_EXISTS : thm := BSpecialIdeals.PRIME_IDEAL_EXISTS
unsafe def PRIME_SUPERIDEAL_EXCLUDING_EXISTS : thm := BSpecialIdeals.PRIME_SUPERIDEAL_EXCLUDING_EXISTS
unsafe def PRIME_IDEAL_EXCLUDING_EXISTS : thm := BSpecialIdeals.PRIME_IDEAL_EXCLUDING_EXISTS
unsafe def MAXIMAL_NONFG_IMP_PRIME_IDEAL : thm := BSpecialIdeals.MAXIMAL_NONFG_IMP_PRIME_IDEAL
unsafe def PRIME_IDEAL_SING : thm := BSpecialIdeals.PRIME_IDEAL_SING
unsafe def RING_PRIME_IDEAL : thm := BSpecialIdeals.RING_PRIME_IDEAL
unsafe def PROPER_IDEAL_IDEAL_GENERATED_SING : thm := BSpecialIdeals.PROPER_IDEAL_IDEAL_GENERATED_SING
unsafe def MAXIMAL_CONTAINING_IDEAL_EXISTS : thm := BSpecialIdeals.MAXIMAL_CONTAINING_IDEAL_EXISTS
unsafe def UNIONS_MAXIMAL_IDEALS : thm := BSpecialIdeals.UNIONS_MAXIMAL_IDEALS
unsafe def UNIONS_PROPER_IDEALS : thm := BSpecialIdeals.UNIONS_PROPER_IDEALS
unsafe def UNIONS_PRIME_IDEALS : thm := BSpecialIdeals.UNIONS_PRIME_IDEALS
unsafe def PROPER_IDEAL_NONUNITS : thm := BSpecialIdeals.PROPER_IDEAL_NONUNITS
unsafe def MAXIMAL_IDEAL_NONUNITS : thm := BSpecialIdeals.MAXIMAL_IDEAL_NONUNITS
unsafe def PRIME_IDEAL_NONUNITS : thm := BSpecialIdeals.PRIME_IDEAL_NONUNITS
unsafe def RING_IDEAL_NONUNITS : thm := BSpecialIdeals.RING_IDEAL_NONUNITS
unsafe def RING_IRREDUCIBLE_IMP_MAXIMAL_PRINCIPAL_IDEAL : thm := BSpecialIdeals.RING_IRREDUCIBLE_IMP_MAXIMAL_PRINCIPAL_IDEAL
unsafe def RING_IRREDUCIBLE_EQ_MAXIMAL_PRINCIPAL_IDEAL : thm := BSpecialIdeals.RING_IRREDUCIBLE_EQ_MAXIMAL_PRINCIPAL_IDEAL
unsafe def MAXIMAL_IDEAL_SING_IMP_IRREDUCIBLE : thm := BSpecialIdeals.MAXIMAL_IDEAL_SING_IMP_IRREDUCIBLE
unsafe def RING_IRREDUCIBLE_EQ_MAXIMAL_IDEAL : thm := BSpecialIdeals.RING_IRREDUCIBLE_EQ_MAXIMAL_IDEAL
unsafe def MAXIMAL_IDEAL_SING : thm := BSpecialIdeals.MAXIMAL_IDEAL_SING
unsafe def PID_IRREDUCIBLE_EQ_PRIME : thm := BSpecialIdeals.PID_IRREDUCIBLE_EQ_PRIME
unsafe def FIELD_EQ_TRIVIAL_IDEALS : thm := BSpecialIdeals.FIELD_EQ_TRIVIAL_IDEALS
unsafe def FIELD_EQ_TRIVIAL_IDEALS_EQ : thm := BSpecialIdeals.FIELD_EQ_TRIVIAL_IDEALS_EQ
unsafe def FIELD_EQ_NO_PROPER_IDEALS : thm := BSpecialIdeals.FIELD_EQ_NO_PROPER_IDEALS
unsafe def FIELD_EQ_NO_PROPER_IDEALS_EQ : thm := BSpecialIdeals.FIELD_EQ_NO_PROPER_IDEALS_EQ
unsafe def FIELD_EQ_PROPER_IMP_MAXIMAL_IDEAL : thm := BSpecialIdeals.FIELD_EQ_PROPER_IMP_MAXIMAL_IDEAL
unsafe def FIELD_EQ_PROPER_IMP_PRIME_IDEAL : thm := BSpecialIdeals.FIELD_EQ_PROPER_IMP_PRIME_IDEAL
unsafe def FIELD_IMP_PID : thm := BSpecialIdeals.FIELD_IMP_PID
unsafe def FIELD_IMP_NOETHERIAN_RING : thm := BSpecialIdeals.FIELD_IMP_NOETHERIAN_RING
unsafe def PID_MAXIMAL_EQ_PRIME_IDEAL : thm := BSpecialIdeals.PID_MAXIMAL_EQ_PRIME_IDEAL
unsafe def PID_EQ_INTEGRAL_DOMAIN_PRIME_PRINCIPAL : thm := BSpecialIdeals.PID_EQ_INTEGRAL_DOMAIN_PRIME_PRINCIPAL
unsafe def TRIVIAL_QUOTIENT_RING : thm := BSpecialIdeals.TRIVIAL_QUOTIENT_RING
unsafe def INTEGRAL_DOMAIN_QUOTIENT_RING : thm := BSpecialIdeals.INTEGRAL_DOMAIN_QUOTIENT_RING
unsafe def FIELD_QUOTIENT_RING : thm := BSpecialIdeals.FIELD_QUOTIENT_RING
unsafe def PRIME_IDEAL_CORRESPONDENCE : thm := BSpecialIdeals.PRIME_IDEAL_CORRESPONDENCE
unsafe def PRIME_IDEAL_ISOMORPHIC_IMAGE_EQ : thm := BSpecialIdeals.PRIME_IDEAL_ISOMORPHIC_IMAGE_EQ
unsafe def MAXIMAL_IDEAL_CORRESPONDENCE : thm := BSpecialIdeals.MAXIMAL_IDEAL_CORRESPONDENCE
unsafe def MAXIMAL_IDEAL_EPIMORPHIC_PREIMAGE : thm := BSpecialIdeals.MAXIMAL_IDEAL_EPIMORPHIC_PREIMAGE
unsafe def MAXIMAL_IDEAL_ISOMORPHIC_IMAGE_EQ : thm := BSpecialIdeals.MAXIMAL_IDEAL_ISOMORPHIC_IMAGE_EQ
unsafe def ISOMORPHIC_RING_PIDNESS : thm := BSpecialIdeals.ISOMORPHIC_RING_PIDNESS
unsafe def FIELD_HOMOMORPHISM_IMP_MONOMORPHISM : thm := BSpecialIdeals.FIELD_HOMOMORPHISM_IMP_MONOMORPHISM
unsafe def FIELD_EPIMORPHISM_IMP_ISOMORPHISM : thm := BSpecialIdeals.FIELD_EPIMORPHISM_IMP_ISOMORPHISM
unsafe def RING_EPIMORPHISM_ONTO_FIELD_EXISTS : thm := BSpecialIdeals.RING_EPIMORPHISM_ONTO_FIELD_EXISTS
unsafe def FIELD_RING_HOMOMORPHISM_MONOMORPHISM : thm := BSpecialIdeals.FIELD_RING_HOMOMORPHISM_MONOMORPHISM

-- Radical
unsafe def radical : thm := BRadical.radical
unsafe def RADICAL_SUBSET : thm := BRadical.RADICAL_SUBSET
unsafe def RADICAL_MONO : thm := BRadical.RADICAL_MONO
unsafe def RING_IDEAL_RADICAL : thm := BRadical.RING_IDEAL_RADICAL
unsafe def RADICAL_0 : thm := BRadical.RADICAL_0
unsafe def RADICAL_RING_CARRIER : thm := BRadical.RADICAL_RING_CARRIER
unsafe def RADICAL_ALT : thm := BRadical.RADICAL_ALT
unsafe def RING_POW_IN_RADICAL : thm := BRadical.RING_POW_IN_RADICAL
unsafe def INTEGRAL_DOMAIN_NILRADICAL : thm := BRadical.INTEGRAL_DOMAIN_NILRADICAL
unsafe def FIELD_NILRADICAL : thm := BRadical.FIELD_NILRADICAL
unsafe def RADICAL : thm := BRadical.RADICAL
unsafe def RING_NILRADICAL : thm := BRadical.RING_NILRADICAL
unsafe def INTERS_PRIME_IDEALS : thm := BRadical.INTERS_PRIME_IDEALS
unsafe def RADICAL_RADICAL : thm := BRadical.RADICAL_RADICAL
unsafe def RADICAL_EQ_CARRIER : thm := BRadical.RADICAL_EQ_CARRIER
unsafe def PROPER_RADICAL : thm := BRadical.PROPER_RADICAL
unsafe def RADICAL_UNIONS : thm := BRadical.RADICAL_UNIONS
unsafe def RADICAL_UNION : thm := BRadical.RADICAL_UNION
unsafe def RADICAL_INTER : thm := BRadical.RADICAL_INTER
unsafe def RADICAL_SETADD : thm := BRadical.RADICAL_SETADD
unsafe def COMAXIMAL_RADICALS : thm := BRadical.COMAXIMAL_RADICALS
unsafe def RADICAL_PRIME_IDEAL : thm := BRadical.RADICAL_PRIME_IDEAL
unsafe def RADICAL_SUBSET_PRIME_IDEAL_EQ : thm := BRadical.RADICAL_SUBSET_PRIME_IDEAL_EQ
unsafe def RADICAL_IDEAL_PRIME_IDEAL_EQ : thm := BRadical.RADICAL_IDEAL_PRIME_IDEAL_EQ
unsafe def PRIME_IDEAL_CONTAINS_NILPOTENTS : thm := BRadical.PRIME_IDEAL_CONTAINS_NILPOTENTS
unsafe def RING_NILPOTENT_ADD : thm := BRadical.RING_NILPOTENT_ADD
unsafe def RING_NILPOTENT_LMUL : thm := BRadical.RING_NILPOTENT_LMUL
unsafe def RING_NILPOTENT_RMUL : thm := BRadical.RING_NILPOTENT_RMUL
unsafe def RING_NILPOTENT_SUB : thm := BRadical.RING_NILPOTENT_SUB
unsafe def RING_NILPOTENT_SUM : thm := BRadical.RING_NILPOTENT_SUM
unsafe def RING_ZERODIVISOR_NILPOTENT_CLAUSES : thm := BRadical.RING_ZERODIVISOR_NILPOTENT_CLAUSES
unsafe def RING_REGULAR_NILPOTENT_CLAUSES : thm := BRadical.RING_REGULAR_NILPOTENT_CLAUSES
unsafe def RING_UNIT_NILPOTENT_CLAUSES_1 : thm := BRadical.RING_UNIT_NILPOTENT_CLAUSES_1
unsafe def RING_UNIT_NILPOTENT_CLAUSES : thm := BRadical.RING_UNIT_NILPOTENT_CLAUSES
unsafe def RING_NILPOTENT_UNIT : thm := BRadical.RING_NILPOTENT_UNIT
unsafe def UNIQUE_PRIME_IDEAL : thm := BRadical.UNIQUE_PRIME_IDEAL

-- UFDs
unsafe def UFD : thm := BUFDs.UFD
unsafe def UFD_IMP_INTEGRAL_DOMAIN : thm := BUFDs.UFD_IMP_INTEGRAL_DOMAIN
unsafe def PID_IMP_UFD : thm := BUFDs.PID_IMP_UFD
unsafe def FIELD_IMP_UFD : thm := BUFDs.FIELD_IMP_UFD
unsafe def ISOMORPHIC_RING_UFDNESS : thm := BUFDs.ISOMORPHIC_RING_UFDNESS
unsafe def UFD_EQ_PRIMEFACT : thm := BUFDs.UFD_EQ_PRIMEFACT
unsafe def UFD_EQ_PRIMEFACT_NONUNIT : thm := BUFDs.UFD_EQ_PRIMEFACT_NONUNIT
unsafe def UFD_PRIME_FACTOR_EXISTS : thm := BUFDs.UFD_PRIME_FACTOR_EXISTS
unsafe def UFD_IRREDUCIBLE_EQ_PRIME : thm := BUFDs.UFD_IRREDUCIBLE_EQ_PRIME
unsafe def UFD_EQ_ATOMIC : thm := BUFDs.UFD_EQ_ATOMIC
unsafe def UFD_EQ_ATOMIC_NONUNIT : thm := BUFDs.UFD_EQ_ATOMIC_NONUNIT
unsafe def UFD_EQ_UNIQUE_FACTORIZATION : thm := BUFDs.UFD_EQ_UNIQUE_FACTORIZATION
unsafe def UFD_COPRIME : thm := BUFDs.UFD_COPRIME
unsafe def UFD_PRIME_FACTOR_INDUCT : thm := BUFDs.UFD_PRIME_FACTOR_INDUCT
unsafe def UFD_IMP_GCD_EXISTS : thm := BUFDs.UFD_IMP_GCD_EXISTS
unsafe def PID_EQ_UFD_PRIME_MAXIMAL : thm := BUFDs.PID_EQ_UFD_PRIME_MAXIMAL
unsafe def RING_DIVIDES_LOCALEQUIV : thm := BUFDs.RING_DIVIDES_LOCALEQUIV
unsafe def UFD_LOCALIZATION : thm := BUFDs.UFD_LOCALIZATION
unsafe def PROPER_IDEAL_LOCALIZATION : thm := BUFDs.PROPER_IDEAL_LOCALIZATION
unsafe def RING_LOCALEQUIV_IN_LOCALIZED_IDEAL : thm := BUFDs.RING_LOCALEQUIV_IN_LOCALIZED_IDEAL
unsafe def PRIME_IDEAL_LOCALIZATION_CONTRACTION : thm := BUFDs.PRIME_IDEAL_LOCALIZATION_CONTRACTION
unsafe def PRIME_IDEAL_LOCALIZATION : thm := BUFDs.PRIME_IDEAL_LOCALIZATION
unsafe def PRIME_IDEAL_LOCALIZATION_EXISTS : thm := BUFDs.PRIME_IDEAL_LOCALIZATION_EXISTS
unsafe def RING_LOCALIZATION_PRIME_IDEAL_CORRESPONDENCE : thm := BUFDs.RING_LOCALIZATION_PRIME_IDEAL_CORRESPONDENCE

-- Euclidean
unsafe def euclidean_ring : thm := BEuclidean.euclidean_ring
unsafe def EUCLIDEAN_RING : thm := BEuclidean.EUCLIDEAN_RING
unsafe def EUCLIDEAN_RING_ALT : thm := BEuclidean.EUCLIDEAN_RING_ALT
unsafe def EUCLIDEAN_IMP_PRINCIPAL_IDEAL_RING : thm := BEuclidean.EUCLIDEAN_IMP_PRINCIPAL_IDEAL_RING
unsafe def EUCLIDEAN_DOMAIN_IMP_PID : thm := BEuclidean.EUCLIDEAN_DOMAIN_IMP_PID
unsafe def EUCLIDEAN_RING_UNIVERSAL_SIDE_DIVISOR : thm := BEuclidean.EUCLIDEAN_RING_UNIVERSAL_SIDE_DIVISOR
unsafe def EUCLIDEAN_RING_EPIMORPHIC_IMAGE : thm := BEuclidean.EUCLIDEAN_RING_EPIMORPHIC_IMAGE
unsafe def EUCLIDEAN_QUOTIENT_RING : thm := BEuclidean.EUCLIDEAN_QUOTIENT_RING
unsafe def ISOMORPHIC_RING_EUCLIDEANNESS : thm := BEuclidean.ISOMORPHIC_RING_EUCLIDEANNESS

-- Noetherian
unsafe def NOETHERIAN_RING : thm := BNoetherian.NOETHERIAN_RING
unsafe def NOETHERIAN_RING_EQ_ACC : thm := BNoetherian.NOETHERIAN_RING_EQ_ACC
unsafe def NOETHERIAN_RING_EQ_MAXIMAL : thm := BNoetherian.NOETHERIAN_RING_EQ_MAXIMAL
unsafe def NOETHERIAN_RING_EPIMORPHIC_IMAGE : thm := BNoetherian.NOETHERIAN_RING_EPIMORPHIC_IMAGE
unsafe def NOETHERIAN_QUOTIENT_RING : thm := BNoetherian.NOETHERIAN_QUOTIENT_RING
unsafe def ISOMORPHIC_RING_NOETHERIANNESS : thm := BNoetherian.ISOMORPHIC_RING_NOETHERIANNESS
unsafe def NOETHERIAN_PROD_RING : thm := BNoetherian.NOETHERIAN_PROD_RING
unsafe def NOETHERIAN_PRODUCT_RING : thm := BNoetherian.NOETHERIAN_PRODUCT_RING
unsafe def NOETHERIAN_RING_EQ_FG_PRIME_IDEALS : thm := BNoetherian.NOETHERIAN_RING_EQ_FG_PRIME_IDEALS
unsafe def NOETHERIAN_RING_LOCALIZATION : thm := BNoetherian.NOETHERIAN_RING_LOCALIZATION

-- ACCP
unsafe def RING_ACCP : thm := BACCP.RING_ACCP
unsafe def RING_DIVIDES_WF : thm := BACCP.RING_DIVIDES_WF
unsafe def RING_PRINCIPAL_IDEALS_WF : thm := BACCP.RING_PRINCIPAL_IDEALS_WF
unsafe def ACCP_RING_PROPER_DIVISOR_INDUCT : thm := BACCP.ACCP_RING_PROPER_DIVISOR_INDUCT
unsafe def RING_PROPER_DIVISOR_INDUCT : thm := BACCP.RING_PROPER_DIVISOR_INDUCT
unsafe def ACCP_DOMAIN_ATOMIC : thm := BACCP.ACCP_DOMAIN_ATOMIC
unsafe def ACCP_DOMAIN_IRREDUCIBLE_FACTOR_EXISTS : thm := BACCP.ACCP_DOMAIN_IRREDUCIBLE_FACTOR_EXISTS
unsafe def NOETHERIAN_DOMAIN_ATOMIC : thm := BACCP.NOETHERIAN_DOMAIN_ATOMIC
unsafe def NOETHERIAN_DOMAIN_IRREDUCIBLE_FACTOR_EXISTS : thm := BACCP.NOETHERIAN_DOMAIN_IRREDUCIBLE_FACTOR_EXISTS
unsafe def UFD_EQ_ACCP : thm := BACCP.UFD_EQ_ACCP

-- RingGcd
unsafe def ring_gcd : thm := BRingGcd.ring_gcd
unsafe def RING_GCD_WORKS : thm := BRingGcd.RING_GCD_WORKS
unsafe def RING_GCD_UNIQUE : thm := BRingGcd.RING_GCD_UNIQUE
unsafe def RING_GCD_REFL : thm := BRingGcd.RING_GCD_REFL
unsafe def RING_GCD : thm := BRingGcd.RING_GCD
unsafe def RING_GCD_EQ : thm := BRingGcd.RING_GCD_EQ
unsafe def RING_GCD_SYM : thm := BRingGcd.RING_GCD_SYM
unsafe def RING_GCD_DIVIDES : thm := BRingGcd.RING_GCD_DIVIDES
unsafe def RING_UNIT_GCD : thm := BRingGcd.RING_UNIT_GCD
unsafe def RING_GCD_EQ_1 : thm := BRingGcd.RING_GCD_EQ_1
unsafe def UFD_DIVIDES_GCD : thm := BRingGcd.UFD_DIVIDES_GCD
unsafe def UFD_DIVIDES_GCD_EQ : thm := BRingGcd.UFD_DIVIDES_GCD_EQ
unsafe def RING_GCD_00 : thm := BRingGcd.RING_GCD_00
unsafe def FIELD_GCD : thm := BRingGcd.FIELD_GCD

-- Bezout
unsafe def bezout_ring : thm := BBezout.bezout_ring
unsafe def BEZOUT_RING_FINITELY_GENERATED_EQ_PRINCIPAL_IDEAL : thm := BBezout.BEZOUT_RING_FINITELY_GENERATED_EQ_PRINCIPAL_IDEAL
unsafe def PID_IMP_BEZOUT_RING : thm := BBezout.PID_IMP_BEZOUT_RING
unsafe def FIELD_IMP_BEZOUT_RING : thm := BBezout.FIELD_IMP_BEZOUT_RING
unsafe def BEZOUT_RING_2 : thm := BBezout.BEZOUT_RING_2
unsafe def BEZOUT_RING_SETADD : thm := BBezout.BEZOUT_RING_SETADD
unsafe def PID_EQ_NOETHERIAN_BEZOUT_DOMAIN : thm := BBezout.PID_EQ_NOETHERIAN_BEZOUT_DOMAIN
unsafe def BEZOUT_RING_IMP_BEZOUT : thm := BBezout.BEZOUT_RING_IMP_BEZOUT
unsafe def RING_IMP_GCD_EXISTS : thm := BBezout.RING_IMP_GCD_EXISTS
unsafe def BEZOUT_RING_IMP_GCD : thm := BBezout.BEZOUT_RING_IMP_GCD
unsafe def BEZOUT_RING : thm := BBezout.BEZOUT_RING
unsafe def BEZOUT_RING_COPRIME : thm := BBezout.BEZOUT_RING_COPRIME
unsafe def BEZOUT_RING_COPRIME_COMAXIMAL : thm := BBezout.BEZOUT_RING_COPRIME_COMAXIMAL
unsafe def BEZOUT_RING_COMAXIMAL_COPRIME : thm := BBezout.BEZOUT_RING_COMAXIMAL_COPRIME
unsafe def RING_DIVIDES_GCD : thm := BBezout.RING_DIVIDES_GCD
unsafe def RING_DIVIDES_GCD_EQ : thm := BBezout.RING_DIVIDES_GCD_EQ
unsafe def BEZOUT_RING_IRREDUCIBLE_IMP_PRIME : thm := BBezout.BEZOUT_RING_IRREDUCIBLE_IMP_PRIME
unsafe def BEZOUT_DOMAIN_IRREDUCIBLE_EQ_PRIME : thm := BBezout.BEZOUT_DOMAIN_IRREDUCIBLE_EQ_PRIME
unsafe def PID_EQ_ACCP_BEZOUT_DOMAIN : thm := BBezout.PID_EQ_ACCP_BEZOUT_DOMAIN
unsafe def PID_EQ_UFD_BEZOUT_RING : thm := BBezout.PID_EQ_UFD_BEZOUT_RING
unsafe def PID_EQ_BEZOUT_ATOMIC : thm := BBezout.PID_EQ_BEZOUT_ATOMIC
unsafe def BEZOUT_RING_EPIMORPHIC_IMAGE : thm := BBezout.BEZOUT_RING_EPIMORPHIC_IMAGE
unsafe def BEZOUT_QUOTIENT_RING : thm := BBezout.BEZOUT_QUOTIENT_RING
unsafe def ISOMORPHIC_RING_BEZOUTNESS : thm := BBezout.ISOMORPHIC_RING_BEZOUTNESS
unsafe def RING_COPRIME_HOMOMORPHIC_IMAGE : thm := BBezout.RING_COPRIME_HOMOMORPHIC_IMAGE
unsafe def BEZOUT_RING_LOCALIZATION : thm := BBezout.BEZOUT_RING_LOCALIZATION
unsafe def PID_RING_LOCALIZATION : thm := BBezout.PID_RING_LOCALIZATION

-- GcdDomain
unsafe def RING_GCD_LMUL : thm := BGcdDomain.RING_GCD_LMUL
unsafe def RING_GCD_RMUL : thm := BGcdDomain.RING_GCD_RMUL
unsafe def RING_COPRIME_DIVPROD_LEFT : thm := BGcdDomain.RING_COPRIME_DIVPROD_LEFT
unsafe def RING_COPRIME_DIVPROD_RIGHT : thm := BGcdDomain.RING_COPRIME_DIVPROD_RIGHT
unsafe def RING_DIVIDES_MUL : thm := BGcdDomain.RING_DIVIDES_MUL
unsafe def RING_DIVIDES_MUL_EQ : thm := BGcdDomain.RING_DIVIDES_MUL_EQ
unsafe def RING_COPRIME_LMUL : thm := BGcdDomain.RING_COPRIME_LMUL
unsafe def RING_COPRIME_RMUL : thm := BGcdDomain.RING_COPRIME_RMUL
unsafe def RING_COPRIME_PRODUCT_EQ : thm := BGcdDomain.RING_COPRIME_PRODUCT_EQ
unsafe def RING_COPRIME_PRODUCT : thm := BGcdDomain.RING_COPRIME_PRODUCT
unsafe def RING_COPRIME_RPOW : thm := BGcdDomain.RING_COPRIME_RPOW
unsafe def RING_COPRIME_LPOW : thm := BGcdDomain.RING_COPRIME_LPOW
unsafe def RING_COPRIME_PRODUCT_DIVIDES_ALT : thm := BGcdDomain.RING_COPRIME_PRODUCT_DIVIDES_ALT
unsafe def RING_COPRIME_PRODUCT_DIVIDES : thm := BGcdDomain.RING_COPRIME_PRODUCT_DIVIDES

-- SquarefreeUFD
unsafe def RING_SQUAREFREE_GCD : thm := BSquarefreeUFD.RING_SQUAREFREE_GCD
unsafe def RING_SQUAREFREE_PRIME_EQ : thm := BSquarefreeUFD.RING_SQUAREFREE_PRIME_EQ
unsafe def RING_SQUAREFREE_PRIME_DIVISOR_EQ : thm := BSquarefreeUFD.RING_SQUAREFREE_PRIME_DIVISOR_EQ
unsafe def RING_SQUAREFREE_DIVIDES : thm := BSquarefreeUFD.RING_SQUAREFREE_DIVIDES
unsafe def RING_SQUAREFREE_DIVPOW : thm := BSquarefreeUFD.RING_SQUAREFREE_DIVPOW
unsafe def RING_SQUAREFREE_DIVPOW_EQ : thm := BSquarefreeUFD.RING_SQUAREFREE_DIVPOW_EQ
unsafe def RING_SQUAREFREE_DIVIDES_SQUARE : thm := BSquarefreeUFD.RING_SQUAREFREE_DIVIDES_SQUARE
unsafe def RING_SQUAREFREE_MUL_EQ : thm := BSquarefreeUFD.RING_SQUAREFREE_MUL_EQ
unsafe def RING_SQUAREFREE_PRODUCT : thm := BSquarefreeUFD.RING_SQUAREFREE_PRODUCT
unsafe def RING_SQUAREFREE_ALT : thm := BSquarefreeUFD.RING_SQUAREFREE_ALT
unsafe def RING_SQUAREFREE : thm := BSquarefreeUFD.RING_SQUAREFREE
unsafe def RING_SQUAREFREE_DECOMPOSITION : thm := BSquarefreeUFD.RING_SQUAREFREE_DECOMPOSITION

-- BooleanRings
unsafe def boolean_ring : thm := BBooleanRings.boolean_ring
unsafe def BOOLEAN_RING_SQUARE : thm := BBooleanRings.BOOLEAN_RING_SQUARE
unsafe def BOOLEAN_RING_DOUBLE : thm := BBooleanRings.BOOLEAN_RING_DOUBLE
unsafe def BOOLEAN_RING_NEG : thm := BBooleanRings.BOOLEAN_RING_NEG
unsafe def BOOLEAN_RING_POW : thm := BBooleanRings.BOOLEAN_RING_POW
unsafe def BOOLEAN_RING_OF_NUM : thm := BBooleanRings.BOOLEAN_RING_OF_NUM
unsafe def BOOLEAN_RING_CHAR : thm := BBooleanRings.BOOLEAN_RING_CHAR
unsafe def BOOLEAN_RING_UNIT : thm := BBooleanRings.BOOLEAN_RING_UNIT
unsafe def BOOLEAN_RING_ZERODIVISOR : thm := BBooleanRings.BOOLEAN_RING_ZERODIVISOR
unsafe def BOOLEAN_RING_REGULAR : thm := BBooleanRings.BOOLEAN_RING_REGULAR
unsafe def BOOLEAN_RING_IRREDUCIBLE : thm := BBooleanRings.BOOLEAN_RING_IRREDUCIBLE
unsafe def BOOLEAN_RING_DIVIDES : thm := BBooleanRings.BOOLEAN_RING_DIVIDES
unsafe def BOOLEAN_RING_NILPOTENT : thm := BBooleanRings.BOOLEAN_RING_NILPOTENT
unsafe def BOOLEAN_RING_RADICAL : thm := BBooleanRings.BOOLEAN_RING_RADICAL
unsafe def TRIVIAL_IMP_BOOLEAN_RING : thm := BBooleanRings.TRIVIAL_IMP_BOOLEAN_RING
unsafe def BOOLEAN_RING_10 : thm := BBooleanRings.BOOLEAN_RING_10
unsafe def BOOLEAN_RING_2 : thm := BBooleanRings.BOOLEAN_RING_2
unsafe def ISOMORPHIC_RING_BOOLEANNESS : thm := BBooleanRings.ISOMORPHIC_RING_BOOLEANNESS
unsafe def BOOLEAN_RING_EPIMORPHIC_IMAGE : thm := BBooleanRings.BOOLEAN_RING_EPIMORPHIC_IMAGE
unsafe def BOOLEAN_QUOTIENT_RING : thm := BBooleanRings.BOOLEAN_QUOTIENT_RING
unsafe def BOOLEAN_RING_SUBRING_GENERATED : thm := BBooleanRings.BOOLEAN_RING_SUBRING_GENERATED
unsafe def BOOLEAN_RING_MONOMORPHIC_PREIMAGE : thm := BBooleanRings.BOOLEAN_RING_MONOMORPHIC_PREIMAGE
unsafe def BOOLEAN_PROD_RING : thm := BBooleanRings.BOOLEAN_PROD_RING
unsafe def BOOLEAN_PRODUCT_RING : thm := BBooleanRings.BOOLEAN_PRODUCT_RING
unsafe def BOOLEAN_IMP_BEZOUT_RING : thm := BBooleanRings.BOOLEAN_IMP_BEZOUT_RING
unsafe def BOOLEAN_RING_MAXIMAL_EQ_PRIME_IDEAL : thm := BBooleanRings.BOOLEAN_RING_MAXIMAL_EQ_PRIME_IDEAL
unsafe def BOOLEAN_RING_MULTSYS : thm := BBooleanRings.BOOLEAN_RING_MULTSYS
unsafe def BOOLEAN_PROPER_IDEAL_COMPLEMENT : thm := BBooleanRings.BOOLEAN_PROPER_IDEAL_COMPLEMENT
unsafe def BOOLEAN_INTEGRAL_DOMAIN : thm := BBooleanRings.BOOLEAN_INTEGRAL_DOMAIN

-- LocalRings
unsafe def local_ring : thm := BLocalRings.local_ring
unsafe def LOCAL_IMP_NONTRIVIAL_RING : thm := BLocalRings.LOCAL_IMP_NONTRIVIAL_RING
unsafe def LOCAL_RING_IDEAL_NONUNITS : thm := BLocalRings.LOCAL_RING_IDEAL_NONUNITS
unsafe def FIELD_IMP_LOCAL_RING : thm := BLocalRings.FIELD_IMP_LOCAL_RING
unsafe def UNIQUE_PRIME_IDEAL_IMP_LOCAL_RING : thm := BLocalRings.UNIQUE_PRIME_IDEAL_IMP_LOCAL_RING
unsafe def LOCAL_RING_EPIMORPHIC_IMAGE : thm := BLocalRings.LOCAL_RING_EPIMORPHIC_IMAGE
unsafe def LOCAL_QUOTIENT_RING : thm := BLocalRings.LOCAL_QUOTIENT_RING
unsafe def ISOMORPHIC_RING_LOCALITY : thm := BLocalRings.ISOMORPHIC_RING_LOCALITY
unsafe def LOCAL_RING_LOCALIZATION : thm := BLocalRings.LOCAL_RING_LOCALIZATION
unsafe def NOETHERIAN_LOCAL_RING_LOCALIZATION : thm := BLocalRings.NOETHERIAN_LOCAL_RING_LOCALIZATION

-- VonNeumann
unsafe def vnregular_ring : thm := BVonNeumann.vnregular_ring
unsafe def FIELD_IMP_VNREGULAR_RING : thm := BVonNeumann.FIELD_IMP_VNREGULAR_RING
unsafe def BOOLEAN_IMP_VNREGULAR_RING : thm := BVonNeumann.BOOLEAN_IMP_VNREGULAR_RING
unsafe def VNREGULAR_RING_EPIMORPHIC_IMAGE : thm := BVonNeumann.VNREGULAR_RING_EPIMORPHIC_IMAGE
unsafe def VNREGULAR_QUOTIENT_RING : thm := BVonNeumann.VNREGULAR_QUOTIENT_RING
unsafe def ISOMORPHIC_RING_VNREGULARITY : thm := BVonNeumann.ISOMORPHIC_RING_VNREGULARITY
unsafe def VNREGULAR_PROD_RING : thm := BVonNeumann.VNREGULAR_PROD_RING
unsafe def VNREGULAR_PRODUCT_RING : thm := BVonNeumann.VNREGULAR_PRODUCT_RING
unsafe def VNREGULAR_IMP_REDUCED_RING : thm := BVonNeumann.VNREGULAR_IMP_REDUCED_RING
unsafe def VNREGULAR_RING_NILPOTENT : thm := BVonNeumann.VNREGULAR_RING_NILPOTENT
unsafe def VNREGULAR_RING_REGULAR : thm := BVonNeumann.VNREGULAR_RING_REGULAR
unsafe def VNREGULAR_DOMAIN : thm := BVonNeumann.VNREGULAR_DOMAIN
unsafe def VNREGULAR_RING_PRINCIPAL_IDEALS : thm := BVonNeumann.VNREGULAR_RING_PRINCIPAL_IDEALS
unsafe def VNREGULAR_IMP_BEZOUT_RING : thm := BVonNeumann.VNREGULAR_IMP_BEZOUT_RING
unsafe def VNREGULAR_RING_FINITELY_GENERATED_IDEALS : thm := BVonNeumann.VNREGULAR_RING_FINITELY_GENERATED_IDEALS
unsafe def VNREGULAR_RING_IDEAL_IDEMPOT : thm := BVonNeumann.VNREGULAR_RING_IDEAL_IDEMPOT
unsafe def VNREGULAR_RING : thm := BVonNeumann.VNREGULAR_RING
unsafe def VNREGULAR_RING_ALT : thm := BVonNeumann.VNREGULAR_RING_ALT
unsafe def VNREGULAR_RING_LOCALIZATION : thm := BVonNeumann.VNREGULAR_RING_LOCALIZATION
unsafe def VNREGULAR_FRACTION_RING : thm := BVonNeumann.VNREGULAR_FRACTION_RING

-- BoolRing
unsafe def bool_ring : thm := BBoolRing.bool_ring
unsafe def BOOL_RING : thm := BBoolRing.BOOL_RING
unsafe def FIELD_BOOL_RING : thm := BBoolRing.FIELD_BOOL_RING
unsafe def NOT_TRIVIAL_BOOL_RING : thm := BBoolRing.NOT_TRIVIAL_BOOL_RING
unsafe def BOOLEAN_RING_BOOL_RING : thm := BBoolRing.BOOLEAN_RING_BOOL_RING
unsafe def INTEGRAL_DOMAIN_BOOL_RING : thm := BBoolRing.INTEGRAL_DOMAIN_BOOL_RING
unsafe def BOOL_RING_CARRIER_HAS_SIZE_2 : thm := BBoolRing.BOOL_RING_CARRIER_HAS_SIZE_2
unsafe def ISOMORPHIC_RING_BOOL_RING : thm := BBoolRing.ISOMORPHIC_RING_BOOL_RING

-- IntegerRing
unsafe def integer_ring : thm := BIntegerRing.integer_ring
unsafe def INTEGER_RING : thm := BIntegerRing.INTEGER_RING
unsafe def INTEGER_RING_POW : thm := BIntegerRing.INTEGER_RING_POW
unsafe def INTEGER_RING_UNIT : thm := BIntegerRing.INTEGER_RING_UNIT
unsafe def INTEGER_RING_DIVIDES : thm := BIntegerRing.INTEGER_RING_DIVIDES
unsafe def NOT_TRIVIAL_INTEGER_RING : thm := BIntegerRing.NOT_TRIVIAL_INTEGER_RING
unsafe def NOT_FIELD_INTEGER_RING : thm := BIntegerRing.NOT_FIELD_INTEGER_RING
unsafe def RING_HOMOMORPHISM_INTEGER_RING_OF_INT : thm := BIntegerRing.RING_HOMOMORPHISM_INTEGER_RING_OF_INT
unsafe def RING_MONOMORPHISM_INTEGER_RING_OF_INT : thm := BIntegerRing.RING_MONOMORPHISM_INTEGER_RING_OF_INT
unsafe def INTEGRAL_DOMAIN_INTEGER_RING : thm := BIntegerRing.INTEGRAL_DOMAIN_INTEGER_RING
unsafe def EUCLIDEAN_INTEGER_RING : thm := BIntegerRing.EUCLIDEAN_INTEGER_RING
unsafe def PID_INTEGER_RING : thm := BIntegerRing.PID_INTEGER_RING
unsafe def UFD_INTEGER_RING : thm := BIntegerRing.UFD_INTEGER_RING
unsafe def BEZOUT_INTEGER_RING : thm := BIntegerRing.BEZOUT_INTEGER_RING
unsafe def INTEGER_RING_OF_NUM : thm := BIntegerRing.INTEGER_RING_OF_NUM
unsafe def INTEGER_RING_OF_INT : thm := BIntegerRing.INTEGER_RING_OF_INT
unsafe def INTEGER_RING_CHAR : thm := BIntegerRing.INTEGER_RING_CHAR
unsafe def INTEGER_RING_COPRIME : thm := BIntegerRing.INTEGER_RING_COPRIME
unsafe def INTEGER_RING_ASSOCIATES : thm := BIntegerRing.INTEGER_RING_ASSOCIATES
unsafe def INTEGER_RING_GCD : thm := BIntegerRing.INTEGER_RING_GCD
unsafe def INTEGER_RING_IDEAL_GENERATED_SING : thm := BIntegerRing.INTEGER_RING_IDEAL_GENERATED_SING
unsafe def INTEGER_RING_COSET_IDEAL_GENERATED_SING : thm := BIntegerRing.INTEGER_RING_COSET_IDEAL_GENERATED_SING

-- IntegerModRing
unsafe def integer_mod_ring : thm := BIntegerModRing.integer_mod_ring
unsafe def INTEGER_MOD_RING : thm := BIntegerModRing.INTEGER_MOD_RING
unsafe def IN_INTEGER_MOD_RING_CARRIER : thm := BIntegerModRing.IN_INTEGER_MOD_RING_CARRIER
unsafe def RING_CARRIER_INTEGER_MOD_RING : thm := BIntegerModRing.RING_CARRIER_INTEGER_MOD_RING
unsafe def INTEGER_MOD_RING_CARRIER_REM : thm := BIntegerModRing.INTEGER_MOD_RING_CARRIER_REM
unsafe def INTEGER_MOD_RING_TRIVIAL : thm := BIntegerModRing.INTEGER_MOD_RING_TRIVIAL
unsafe def INTEGER_MOD_RING_SUB : thm := BIntegerModRing.INTEGER_MOD_RING_SUB
unsafe def INTEGER_MOD_RING_POW : thm := BIntegerModRing.INTEGER_MOD_RING_POW
unsafe def INTEGER_MOD_RING_OF_NUM : thm := BIntegerModRing.INTEGER_MOD_RING_OF_NUM
unsafe def INTEGER_MOD_RING_OF_INT : thm := BIntegerModRing.INTEGER_MOD_RING_OF_INT
unsafe def INTEGER_MOD_RING_CLAUSES : thm := BIntegerModRing.INTEGER_MOD_RING_CLAUSES
unsafe def INTEGER_MOD_RING_CHAR : thm := BIntegerModRing.INTEGER_MOD_RING_CHAR
unsafe def INTEGER_MOD_RING_DIVIDES : thm := BIntegerModRing.INTEGER_MOD_RING_DIVIDES
unsafe def INTEGER_MOD_RING_ASSOCIATES : thm := BIntegerModRing.INTEGER_MOD_RING_ASSOCIATES
unsafe def INTEGER_MOD_RING_UNIT : thm := BIntegerModRing.INTEGER_MOD_RING_UNIT
unsafe def TRIVIAL_INTEGER_MOD_RING : thm := BIntegerModRing.TRIVIAL_INTEGER_MOD_RING
unsafe def FINITE_INTEGER_MOD_RING : thm := BIntegerModRing.FINITE_INTEGER_MOD_RING
unsafe def CARD_INTEGER_MOD_RING : thm := BIntegerModRing.CARD_INTEGER_MOD_RING
unsafe def FIELD_INTEGER_MOD_RING : thm := BIntegerModRing.FIELD_INTEGER_MOD_RING
unsafe def INTEGRAL_DOMAIN_INTEGER_MOD_RING : thm := BIntegerModRing.INTEGRAL_DOMAIN_INTEGER_MOD_RING
unsafe def RING_HOMOMORPHISM_INTEGER_MOD_RING_OF_INT : thm := BIntegerModRing.RING_HOMOMORPHISM_INTEGER_MOD_RING_OF_INT
unsafe def RING_MONOMORPHISM_INTEGER_MOD_RING_OF_INT : thm := BIntegerModRing.RING_MONOMORPHISM_INTEGER_MOD_RING_OF_INT
unsafe def RING_HOMOMORPHISM_FROM_INTEGER_MOD_RING : thm := BIntegerModRing.RING_HOMOMORPHISM_FROM_INTEGER_MOD_RING
unsafe def RING_MONOMORPHISM_FROM_INTEGER_MOD_RING : thm := BIntegerModRing.RING_MONOMORPHISM_FROM_INTEGER_MOD_RING
unsafe def RING_HOMOMORPHISM_INTEGER_MOD_RINGS : thm := BIntegerModRing.RING_HOMOMORPHISM_INTEGER_MOD_RINGS
unsafe def RING_HOMOMORPHISM_INTEGER_MOD_RINGS_POW : thm := BIntegerModRing.RING_HOMOMORPHISM_INTEGER_MOD_RINGS_POW
unsafe def RING_HOMOMORPHISM_PROD_INTEGER_MOD_RING : thm := BIntegerModRing.RING_HOMOMORPHISM_PROD_INTEGER_MOD_RING
unsafe def RING_ISOMORPHISM_PROD_INTEGER_MOD_RING : thm := BIntegerModRing.RING_ISOMORPHISM_PROD_INTEGER_MOD_RING
unsafe def ISOMORPHIC_PROD_INTEGER_MOD_RING : thm := BIntegerModRing.ISOMORPHIC_PROD_INTEGER_MOD_RING
unsafe def VNREGULAR_INTEGER_MOD_RING : thm := BIntegerModRing.VNREGULAR_INTEGER_MOD_RING
unsafe def INTEGER_QUOTIENT_RING_ISOMORPHIC_MOD : thm := BIntegerModRing.INTEGER_QUOTIENT_RING_ISOMORPHIC_MOD
unsafe def RING_ISOMORPHISM_PRIME_SUBRING : thm := BIntegerModRing.RING_ISOMORPHISM_PRIME_SUBRING
unsafe def ISOMORPHIC_PRIME_SUBRING : thm := BIntegerModRing.ISOMORPHIC_PRIME_SUBRING
unsafe def FIELD_PRIME_SUBRING : thm := BIntegerModRing.FIELD_PRIME_SUBRING

-- IntegerModConv
unsafe def RING_INV_INTEGER_MOD_RING : thm := BIntegerModConv.RING_INV_INTEGER_MOD_RING
unsafe def INTEGER_MOD_RING_RED_CONV : HolCore.Equal.ioconv := fun t => BIntegerModConv.INTEGER_MOD_RING_RED_CONV t

-- RealRing
unsafe def real_ring : thm := BRealRing.real_ring
unsafe def REAL_RING_CLAUSES : thm := BRealRing.REAL_RING_CLAUSES
unsafe def FIELD_REAL_RING : thm := BRealRing.FIELD_REAL_RING
unsafe def INTEGRAL_DOMAIN_REAL_RING : thm := BRealRing.INTEGRAL_DOMAIN_REAL_RING
unsafe def REAL_RING_OF_NUM : thm := BRealRing.REAL_RING_OF_NUM
unsafe def REAL_RING_OF_INT : thm := BRealRing.REAL_RING_OF_INT
unsafe def REAL_RING_CHAR : thm := BRealRing.REAL_RING_CHAR
unsafe def REAL_RING_SUB : thm := BRealRing.REAL_RING_SUB
unsafe def REAL_RING_INV : thm := BRealRing.REAL_RING_INV
unsafe def REAL_RING_DIV : thm := BRealRing.REAL_RING_DIV
unsafe def REAL_RING_POW : thm := BRealRing.REAL_RING_POW
unsafe def REAL_FIELD_CLAUSES : thm := BRealRing.REAL_FIELD_CLAUSES

-- Monomials
unsafe def monomial_1 : thm := BMonomials.monomial_1
unsafe def monomial_mul : thm := BMonomials.monomial_mul
unsafe def monomial_div : thm := BMonomials.monomial_div
unsafe def monomial_restrict : thm := BMonomials.monomial_restrict
unsafe def monomial_divides : thm := BMonomials.monomial_divides
unsafe def monomial_var : thm := BMonomials.monomial_var
unsafe def monomial_vars : thm := BMonomials.monomial_vars
unsafe def monomial_deg : thm := BMonomials.monomial_deg
unsafe def monomial : thm := BMonomials.monomial
unsafe def MONOMIAL_POINTWISE_TAC : HolCore.Tactics.tactic := fun g => BMonomials.MONOMIAL_POINTWISE_TAC g
unsafe def MONOMIAL_TAC : HolCore.Tactics.tactic := fun g => BMonomials.MONOMIAL_TAC g
unsafe def MONOMIAL_RULE : term → IO (Except String thm) := fun t => (BMonomials.MONOMIAL_RULE t).run
unsafe def FINITE_MONOMIAL_VARS : thm := BMonomials.FINITE_MONOMIAL_VARS
unsafe def FINITE_MONOMIAL_VARS_1 : thm := BMonomials.FINITE_MONOMIAL_VARS_1
unsafe def MONOMIAL_DEG : thm := BMonomials.MONOMIAL_DEG
unsafe def MONOMIAL_VAR_1 : thm := BMonomials.MONOMIAL_VAR_1
unsafe def MONOMIAL_VARS_1 : thm := BMonomials.MONOMIAL_VARS_1
unsafe def MONOMIAL_VARS_EQ_EMPTY : thm := BMonomials.MONOMIAL_VARS_EQ_EMPTY
unsafe def MONOMIAL_VARS_MUL : thm := BMonomials.MONOMIAL_VARS_MUL
unsafe def MONOMIAL_VARS_VAR : thm := BMonomials.MONOMIAL_VARS_VAR
unsafe def MONOMIAL_VARS_RESTRICT : thm := BMonomials.MONOMIAL_VARS_RESTRICT
unsafe def MONOMIAL_RESTRICT_EQ : thm := BMonomials.MONOMIAL_RESTRICT_EQ
unsafe def MONOMIAL_RESTRICT_REFL : thm := BMonomials.MONOMIAL_RESTRICT_REFL
unsafe def MONOMIAL_MONO : thm := BMonomials.MONOMIAL_MONO
unsafe def MONOMIAL_UNIV : thm := BMonomials.MONOMIAL_UNIV
unsafe def MONOMIAL_1 : thm := BMonomials.MONOMIAL_1
unsafe def MONOMIAL_MUL : thm := BMonomials.MONOMIAL_MUL
unsafe def MONOMIAL_RESTRICT_MUL : thm := BMonomials.MONOMIAL_RESTRICT_MUL
unsafe def MONOMIAL_MUL_RESTRICT : thm := BMonomials.MONOMIAL_MUL_RESTRICT
unsafe def MONOMIAL_DIVISOR : thm := BMonomials.MONOMIAL_DIVISOR
unsafe def MONOMIAL_VAR : thm := BMonomials.MONOMIAL_VAR
unsafe def MONOMIAL_RESTRICT : thm := BMonomials.MONOMIAL_RESTRICT
unsafe def MONOMIAL : thm := BMonomials.MONOMIAL
unsafe def MONOMIAL_UNIV_1 : thm := BMonomials.MONOMIAL_UNIV_1
unsafe def MONOMIAL_DEG_1 : thm := BMonomials.MONOMIAL_DEG_1
unsafe def MONOMIAL_DEG_VAR : thm := BMonomials.MONOMIAL_DEG_VAR
unsafe def MONOMIAL_DEG_EQ_0_ALT : thm := BMonomials.MONOMIAL_DEG_EQ_0_ALT
unsafe def MONOMIAL_DEG_EQ_0 : thm := BMonomials.MONOMIAL_DEG_EQ_0
unsafe def MONOMIAL_DIV_DIVIDES : thm := BMonomials.MONOMIAL_DIV_DIVIDES
unsafe def MONOMIAL_DIV : thm := BMonomials.MONOMIAL_DIV
unsafe def MONOMIAL_DIVIDES_1 : thm := BMonomials.MONOMIAL_DIVIDES_1
unsafe def MONOMIAL_DIVIDES_EXISTS : thm := BMonomials.MONOMIAL_DIVIDES_EXISTS
unsafe def MONOMIAL_VAR_DIVIDES_MUL : thm := BMonomials.MONOMIAL_VAR_DIVIDES_MUL
unsafe def MONOMIAL_MUL_EQ_VAR : thm := BMonomials.MONOMIAL_MUL_EQ_VAR
unsafe def MONOMIAL_DEG_MUL : thm := BMonomials.MONOMIAL_DEG_MUL
unsafe def MONOMIAL_DEG_LE : thm := BMonomials.MONOMIAL_DEG_LE
unsafe def MONOMIAL_VAR_EQ : thm := BMonomials.MONOMIAL_VAR_EQ
unsafe def MONOMIAL_MUL_LID : thm := BMonomials.MONOMIAL_MUL_LID
unsafe def MONOMIAL_MUL_RID : thm := BMonomials.MONOMIAL_MUL_RID
unsafe def MONOMIAL_MUL_SYM : thm := BMonomials.MONOMIAL_MUL_SYM
unsafe def MONOMIAL_MUL_ASSOC : thm := BMonomials.MONOMIAL_MUL_ASSOC
unsafe def MONOMIAL_MUL_AC : thm := BMonomials.MONOMIAL_MUL_AC
unsafe def MONOMIAL_MUL_EQ_1 : thm := BMonomials.MONOMIAL_MUL_EQ_1
unsafe def MONOMIAL_MUL_LCANCEL : thm := BMonomials.MONOMIAL_MUL_LCANCEL
unsafe def MONOMIAL_MUL_RCANCEL : thm := BMonomials.MONOMIAL_MUL_RCANCEL
unsafe def MONOMIAL_DIVIDES_REFL : thm := BMonomials.MONOMIAL_DIVIDES_REFL
unsafe def MONOMIAL_DIVIDES_TRANS : thm := BMonomials.MONOMIAL_DIVIDES_TRANS
unsafe def MONOMIAL_DIVIDES_ANTISYM : thm := BMonomials.MONOMIAL_DIVIDES_ANTISYM
unsafe def MONOMIAL_DIVIDES_LMUL : thm := BMonomials.MONOMIAL_DIVIDES_LMUL
unsafe def MONOMIAL_DIVIDES_RMUL : thm := BMonomials.MONOMIAL_DIVIDES_RMUL
unsafe def MONOMIAL_DIV_LMUL_EQ : thm := BMonomials.MONOMIAL_DIV_LMUL_EQ
unsafe def MONOMIAL_DIV_LMUL : thm := BMonomials.MONOMIAL_DIV_LMUL
unsafe def MONOMIAL_DIV_RMUL_EQ : thm := BMonomials.MONOMIAL_DIV_RMUL_EQ
unsafe def MONOMIAL_DIV_RMUL : thm := BMonomials.MONOMIAL_DIV_RMUL
unsafe def MONOMIAL_VAR_DIVIDES : thm := BMonomials.MONOMIAL_VAR_DIVIDES
unsafe def MONOMIAL_VARS_DIVISOR : thm := BMonomials.MONOMIAL_VARS_DIVISOR
unsafe def MONOMIAL_FINITE_DIVISORS : thm := BMonomials.MONOMIAL_FINITE_DIVISORS
unsafe def MONOMIAL_FINITE_DIVISORPAIRS : thm := BMonomials.MONOMIAL_FINITE_DIVISORPAIRS
unsafe def MONOMIAL_INDUCT : thm := BMonomials.MONOMIAL_INDUCT
unsafe def MONOMIAL_VARS_UNIVARIATE : thm := BMonomials.MONOMIAL_VARS_UNIVARIATE
unsafe def MONOMIAL_DEG_UNIVARIATE : thm := BMonomials.MONOMIAL_DEG_UNIVARIATE
unsafe def MONOMIAL_MUL_VAR_ONE : thm := BMonomials.MONOMIAL_MUL_VAR_ONE
unsafe def MONOMIAL_DEG_ONE : thm := BMonomials.MONOMIAL_DEG_ONE

-- PowerSeries
unsafe def ring_powerseries : thm := BPowerSeries.ring_powerseries
unsafe def ring_polynomial : thm := BPowerSeries.ring_polynomial
unsafe def RING_POLYNOMIAL_IMP_POWERSERIES : thm := BPowerSeries.RING_POLYNOMIAL_IMP_POWERSERIES
unsafe def poly_vars : thm := BPowerSeries.poly_vars
unsafe def poly_const : thm := BPowerSeries.poly_const
unsafe def poly_0 : thm := BPowerSeries.poly_0
unsafe def poly_1 : thm := BPowerSeries.poly_1
unsafe def poly_neg : thm := BPowerSeries.poly_neg
unsafe def poly_add : thm := BPowerSeries.poly_add
unsafe def poly_sub : thm := BPowerSeries.poly_sub
unsafe def poly_mul : thm := BPowerSeries.poly_mul
unsafe def poly_var : thm := BPowerSeries.poly_var
unsafe def POLY_SUB : thm := BPowerSeries.POLY_SUB
unsafe def RING_POWERSERIES_MONOMIAL : thm := BPowerSeries.RING_POWERSERIES_MONOMIAL
unsafe def RING_POLYNOMIAL_MONOMIAL : thm := BPowerSeries.RING_POLYNOMIAL_MONOMIAL
unsafe def POLY_0 : thm := BPowerSeries.POLY_0
unsafe def POLY_CONST_0 : thm := BPowerSeries.POLY_CONST_0
unsafe def POLY_CONST_1 : thm := BPowerSeries.POLY_CONST_1
unsafe def RING_POWERSERIES_CONST : thm := BPowerSeries.RING_POWERSERIES_CONST
unsafe def RING_POWERSERIES_VAR : thm := BPowerSeries.RING_POWERSERIES_VAR
unsafe def RING_POWERSERIES_0 : thm := BPowerSeries.RING_POWERSERIES_0
unsafe def RING_POWERSERIES_1 : thm := BPowerSeries.RING_POWERSERIES_1
unsafe def POLY_VAR_MONOMIAL_1 : thm := BPowerSeries.POLY_VAR_MONOMIAL_1
unsafe def RING_POWERSERIES_NEG : thm := BPowerSeries.RING_POWERSERIES_NEG
unsafe def RING_POWERSERIES_ADD : thm := BPowerSeries.RING_POWERSERIES_ADD
unsafe def RING_POWERSERIES_SUB : thm := BPowerSeries.RING_POWERSERIES_SUB
unsafe def RING_POWERSERIES_MUL : thm := BPowerSeries.RING_POWERSERIES_MUL
unsafe def RING_POLYNOMIAL_CONST : thm := BPowerSeries.RING_POLYNOMIAL_CONST
unsafe def RING_POLYNOMIAL_VAR : thm := BPowerSeries.RING_POLYNOMIAL_VAR
unsafe def POLY_VAR_EQ_CONST : thm := BPowerSeries.POLY_VAR_EQ_CONST
unsafe def RING_POLYNOMIAL_0 : thm := BPowerSeries.RING_POLYNOMIAL_0
unsafe def RING_POLYNOMIAL_1 : thm := BPowerSeries.RING_POLYNOMIAL_1
unsafe def RING_POLYNOMIAL_NEG : thm := BPowerSeries.RING_POLYNOMIAL_NEG
unsafe def RING_POLYNOMIAL_ADD : thm := BPowerSeries.RING_POLYNOMIAL_ADD
unsafe def RING_POLYNOMIAL_SUB : thm := BPowerSeries.RING_POLYNOMIAL_SUB
unsafe def RING_POLYNOMIAL_MUL : thm := BPowerSeries.RING_POLYNOMIAL_MUL
unsafe def POLY_ADD_SYM : thm := BPowerSeries.POLY_ADD_SYM
unsafe def POLY_ADD_ASSOC : thm := BPowerSeries.POLY_ADD_ASSOC
unsafe def POLY_ADD_LZERO : thm := BPowerSeries.POLY_ADD_LZERO
unsafe def POLY_ADD_RZERO : thm := BPowerSeries.POLY_ADD_RZERO
unsafe def POLY_ADD_LNEG : thm := BPowerSeries.POLY_ADD_LNEG
unsafe def POLY_MUL_SYM : thm := BPowerSeries.POLY_MUL_SYM
unsafe def POLY_ADD_LDISTRIB : thm := BPowerSeries.POLY_ADD_LDISTRIB
unsafe def POLY_MUL_LID : thm := BPowerSeries.POLY_MUL_LID
unsafe def POLY_MUL_RID : thm := BPowerSeries.POLY_MUL_RID
unsafe def POLY_MUL_ASSOC : thm := BPowerSeries.POLY_MUL_ASSOC
unsafe def POWSER_MUL_0 : thm := BPowerSeries.POWSER_MUL_0
unsafe def POLY_MUL_0 : thm := BPowerSeries.POLY_MUL_0
unsafe def POWSER_MUL_MONOMIAL_1 : thm := BPowerSeries.POWSER_MUL_MONOMIAL_1
unsafe def POLY_MUL_MONOMIAL_1 : thm := BPowerSeries.POLY_MUL_MONOMIAL_1
unsafe def POWSER_MUL_CONST : thm := BPowerSeries.POWSER_MUL_CONST
unsafe def POLY_MUL_CONST : thm := BPowerSeries.POLY_MUL_CONST
unsafe def POWSER_VAR_MUL : thm := BPowerSeries.POWSER_VAR_MUL
unsafe def POWSER_MUL_VAR : thm := BPowerSeries.POWSER_MUL_VAR
unsafe def POLY_VAR_MUL : thm := BPowerSeries.POLY_VAR_MUL
unsafe def POLY_MUL_VAR : thm := BPowerSeries.POLY_MUL_VAR
unsafe def POLY_VARS_CONST : thm := BPowerSeries.POLY_VARS_CONST
unsafe def POLY_VARS_0 : thm := BPowerSeries.POLY_VARS_0
unsafe def POLY_VARS_1 : thm := BPowerSeries.POLY_VARS_1
unsafe def POLY_VARS_VAR : thm := BPowerSeries.POLY_VARS_VAR
unsafe def POLY_VARS_NEG : thm := BPowerSeries.POLY_VARS_NEG
unsafe def POLY_VARS_ADD : thm := BPowerSeries.POLY_VARS_ADD
unsafe def POLY_VARS_MUL : thm := BPowerSeries.POLY_VARS_MUL
unsafe def FINITE_POLYNOMIAL_VARS : thm := BPowerSeries.FINITE_POLYNOMIAL_VARS

-- PolyRings
unsafe def powser_ring : thm := BPolyRings.powser_ring
unsafe def poly_ring : thm := BPolyRings.poly_ring
unsafe def POWSER_RING : thm := BPolyRings.POWSER_RING
unsafe def POLY_RING_SUBRING_OF_POWSER_RING : thm := BPolyRings.POLY_RING_SUBRING_OF_POWSER_RING
unsafe def POLY_RING_AS_SUBRING : thm := BPolyRings.POLY_RING_AS_SUBRING
unsafe def POLY_RING_AS_SUBRING_ALT : thm := BPolyRings.POLY_RING_AS_SUBRING_ALT
unsafe def POLY_RING_AS_SUBRING_FINITE : thm := BPolyRings.POLY_RING_AS_SUBRING_FINITE
unsafe def POLY_CARRIER_SUBRING_OF_POWSER_RING : thm := BPolyRings.POLY_CARRIER_SUBRING_OF_POWSER_RING
unsafe def RING_MONOMORPHISM_POLY_POWSER : thm := BPolyRings.RING_MONOMORPHISM_POLY_POWSER
unsafe def POLY_RING : thm := BPolyRings.POLY_RING
unsafe def POLY_IN_POWSER_RING : thm := BPolyRings.POLY_IN_POWSER_RING
unsafe def poly_pow : thm := BPolyRings.poly_pow
unsafe def POLY_POW : thm := BPolyRings.POLY_POW
unsafe def POLY_POW_ALT : thm := BPolyRings.POLY_POW_ALT
unsafe def RING_POWERSERIES_POW : thm := BPolyRings.RING_POWERSERIES_POW
unsafe def RING_POLYNOMIAL_POW : thm := BPolyRings.RING_POLYNOMIAL_POW
unsafe def POLY_POW_1 : thm := BPolyRings.POLY_POW_1
unsafe def POLY_POW_0 : thm := BPolyRings.POLY_POW_0
unsafe def POLY_VARS_POW : thm := BPolyRings.POLY_VARS_POW
unsafe def POWSER_RING_CLAUSES : thm := BPolyRings.POWSER_RING_CLAUSES
unsafe def POWSER_CLAUSES : thm := BPolyRings.POWSER_CLAUSES
unsafe def POLY_RING_CLAUSES : thm := BPolyRings.POLY_RING_CLAUSES
unsafe def POLY_CLAUSES : thm := BPolyRings.POLY_CLAUSES
unsafe def POLY_SUBRING_GENERATED_CLAUSES : thm := BPolyRings.POLY_SUBRING_GENERATED_CLAUSES
unsafe def POLY_CONST_SUBRING_GENERATED : thm := BPolyRings.POLY_CONST_SUBRING_GENERATED
unsafe def POWSER_MONOMIAL_IN_CARRIER : thm := BPolyRings.POWSER_MONOMIAL_IN_CARRIER
unsafe def POLY_MONOMIAL_IN_CARRIER : thm := BPolyRings.POLY_MONOMIAL_IN_CARRIER
unsafe def RING_POLYNOMIAL : thm := BPolyRings.RING_POLYNOMIAL
unsafe def RING_POWERSERIES : thm := BPolyRings.RING_POWERSERIES
unsafe def IN_POLY_RING_CARRIER : thm := BPolyRings.IN_POLY_RING_CARRIER
unsafe def RING_POLYNOMIAL_CARRIER_GEN : thm := BPolyRings.RING_POLYNOMIAL_CARRIER_GEN
unsafe def RING_POLYNOMIAL_CARRIER : thm := BPolyRings.RING_POLYNOMIAL_CARRIER
unsafe def POLY_MONOMIALS_FINITE : thm := BPolyRings.POLY_MONOMIALS_FINITE
unsafe def FINITE_POLY_VARS : thm := BPolyRings.FINITE_POLY_VARS
unsafe def RING_CARRIER_POLY_RING_FINITE : thm := BPolyRings.RING_CARRIER_POLY_RING_FINITE
unsafe def POWSER_RING_MONO : thm := BPolyRings.POWSER_RING_MONO
unsafe def POLY_RING_MONO : thm := BPolyRings.POLY_RING_MONO
unsafe def POLY_RING_POLY_VARS : thm := BPolyRings.POLY_RING_POLY_VARS
unsafe def POLY_RING_IN_POLY_VARS : thm := BPolyRings.POLY_RING_IN_POLY_VARS
unsafe def POLY_RING_IN_FINITE_VARIABLES : thm := BPolyRings.POLY_RING_IN_FINITE_VARIABLES
unsafe def IN_POLY_RING_SUBRING_GENERATED_FINITARY : thm := BPolyRings.IN_POLY_RING_SUBRING_GENERATED_FINITARY
unsafe def POLY_VAR : thm := BPolyRings.POLY_VAR
unsafe def POLY_VAR_UNIV : thm := BPolyRings.POLY_VAR_UNIV
unsafe def POLY_CONST : thm := BPolyRings.POLY_CONST
unsafe def POWSER_VAR : thm := BPolyRings.POWSER_VAR
unsafe def POWSER_VAR_UNIV : thm := BPolyRings.POWSER_VAR_UNIV
unsafe def POWSER_CONST : thm := BPolyRings.POWSER_CONST
unsafe def POLY_CONST_NEG : thm := BPolyRings.POLY_CONST_NEG
unsafe def POLY_CONST_ADD : thm := BPolyRings.POLY_CONST_ADD
unsafe def POLY_CONST_MUL : thm := BPolyRings.POLY_CONST_MUL
unsafe def RING_OF_NUM_POWSER_RING : thm := BPolyRings.RING_OF_NUM_POWSER_RING
unsafe def RING_OF_NUM_POLY_RING : thm := BPolyRings.RING_OF_NUM_POLY_RING
unsafe def POLY_CONST_OF_NUM : thm := BPolyRings.POLY_CONST_OF_NUM
unsafe def POLY_CONST_EQ : thm := BPolyRings.POLY_CONST_EQ
unsafe def POLY_CONST_EQ_0 : thm := BPolyRings.POLY_CONST_EQ_0
unsafe def POLY_CONST_EQ_1 : thm := BPolyRings.POLY_CONST_EQ_1
unsafe def POWSER_VAR_MUL_EQ_0 : thm := BPolyRings.POWSER_VAR_MUL_EQ_0
unsafe def POWSER_VARPOW_MUL_EQ_0 : thm := BPolyRings.POWSER_VARPOW_MUL_EQ_0
unsafe def RING_HOMOMORPHISM_POLY_CONST : thm := BPolyRings.RING_HOMOMORPHISM_POLY_CONST
unsafe def RING_MONOMORPHISM_POLY_CONST : thm := BPolyRings.RING_MONOMORPHISM_POLY_CONST
unsafe def RING_HOMOMORPHISM_POWSER_CONST : thm := BPolyRings.RING_HOMOMORPHISM_POWSER_CONST
unsafe def RING_MONOMORPHISM_POWSER_CONST : thm := BPolyRings.RING_MONOMORPHISM_POWSER_CONST
unsafe def RING_HOMOMORPHISM_MONOMIAL_1 : thm := BPolyRings.RING_HOMOMORPHISM_MONOMIAL_1
unsafe def POWSER_SUM : thm := BPolyRings.POWSER_SUM
unsafe def POLY_SUM : thm := BPolyRings.POLY_SUM
unsafe def POLY_RING_VAR_POW : thm := BPolyRings.POLY_RING_VAR_POW
unsafe def POLY_RING_PRODUCT_VAR_POW : thm := BPolyRings.POLY_RING_PRODUCT_VAR_POW
unsafe def POLY_RING_PRODUCT_VAR : thm := BPolyRings.POLY_RING_PRODUCT_VAR
unsafe def POLY_RING_EXPAND : thm := BPolyRings.POLY_RING_EXPAND
unsafe def POLY_RING_INDUCT : thm := BPolyRings.POLY_RING_INDUCT
unsafe def POLY_RING_INDUCT_STRONG : thm := BPolyRings.POLY_RING_INDUCT_STRONG
unsafe def POLY_RING_HOMOMORPHISM_UNIQUE : thm := BPolyRings.POLY_RING_HOMOMORPHISM_UNIQUE
unsafe def TRIVIAL_POWSER_RING : thm := BPolyRings.TRIVIAL_POWSER_RING
unsafe def TRIVIAL_POLY_RING : thm := BPolyRings.TRIVIAL_POLY_RING
unsafe def TRIVIAL_RING_POWSER_0 : thm := BPolyRings.TRIVIAL_RING_POWSER_0
unsafe def TRIVIAL_RING_POLY_0 : thm := BPolyRings.TRIVIAL_RING_POLY_0
unsafe def RING_CARRIER_POWSER_RING : thm := BPolyRings.RING_CARRIER_POWSER_RING
unsafe def POWSER_MONOMIALS : thm := BPolyRings.POWSER_MONOMIALS
unsafe def RING_CARRIER_POLY_RING : thm := BPolyRings.RING_CARRIER_POLY_RING
unsafe def POLY_MONOMIALS : thm := BPolyRings.POLY_MONOMIALS
unsafe def POLY_MONOMIALS_ALT : thm := BPolyRings.POLY_MONOMIALS_ALT
unsafe def POWSER_RING_EQ : thm := BPolyRings.POWSER_RING_EQ
unsafe def POWSER_RING_EQ_IMP : thm := BPolyRings.POWSER_RING_EQ_IMP
unsafe def POLY_RING_EQ : thm := BPolyRings.POLY_RING_EQ
unsafe def POLY_RING_EQ_IMP : thm := BPolyRings.POLY_RING_EQ_IMP

-- HomExtend
unsafe def poly_extend : thm := BHomExtend.poly_extend
unsafe def POLY_EXTEND_FROM_SUBRING_GENERATED : thm := BHomExtend.POLY_EXTEND_FROM_SUBRING_GENERATED
unsafe def POLY_EXTEND : thm := BHomExtend.POLY_EXTEND
unsafe def POLY_EXTEND_SUPERSET : thm := BHomExtend.POLY_EXTEND_SUPERSET
unsafe def POLY_EXTEND_POLYNOMIAL : thm := BHomExtend.POLY_EXTEND_POLYNOMIAL
unsafe def POLY_EXTEND_CONST : thm := BHomExtend.POLY_EXTEND_CONST
unsafe def POLY_EXTEND_0 : thm := BHomExtend.POLY_EXTEND_0
unsafe def POLY_EXTEND_1 : thm := BHomExtend.POLY_EXTEND_1
unsafe def POLY_EXTEND_VAR : thm := BHomExtend.POLY_EXTEND_VAR
unsafe def POLY_EXTEND_NEG : thm := BHomExtend.POLY_EXTEND_NEG
unsafe def POLY_EXTEND_ADD : thm := BHomExtend.POLY_EXTEND_ADD
unsafe def POLY_EXTEND_SUB : thm := BHomExtend.POLY_EXTEND_SUB
unsafe def POLY_EXTEND_MUL : thm := BHomExtend.POLY_EXTEND_MUL
unsafe def POLY_EXTEND_POW : thm := BHomExtend.POLY_EXTEND_POW
unsafe def RING_HOMOMORPHISM_POLY_EXTEND : thm := BHomExtend.RING_HOMOMORPHISM_POLY_EXTEND
unsafe def POLY_EXTEND_RING_SUM : thm := BHomExtend.POLY_EXTEND_RING_SUM
unsafe def POLY_EXTEND_RING_PRODUCT : thm := BHomExtend.POLY_EXTEND_RING_PRODUCT
unsafe def POLY_EXTEND_UNIQUE : thm := BHomExtend.POLY_EXTEND_UNIQUE
unsafe def POLY_EXTEND_EQ : thm := BHomExtend.POLY_EXTEND_EQ
unsafe def POLY_EXTEND_ID : thm := BHomExtend.POLY_EXTEND_ID
unsafe def POLY_EXTEND_COMPOSE : thm := BHomExtend.POLY_EXTEND_COMPOSE
unsafe def POLY_EXTEND_HOMOMORPHIC_IMAGE : thm := BHomExtend.POLY_EXTEND_HOMOMORPHIC_IMAGE
unsafe def POWSER_EXTEND_AT_0 : thm := BHomExtend.POWSER_EXTEND_AT_0
unsafe def POLY_EXTEND_AT_0 : thm := BHomExtend.POLY_EXTEND_AT_0
unsafe def RING_HOMOMORPHISM_POWSER_EXTEND_AT_0 : thm := BHomExtend.RING_HOMOMORPHISM_POWSER_EXTEND_AT_0
unsafe def POLY_SUBRING_GENERATED : thm := BHomExtend.POLY_SUBRING_GENERATED
unsafe def RING_HOMOMORPHISMS_EQ_FROM_POLY_RING : thm := BHomExtend.RING_HOMOMORPHISMS_EQ_FROM_POLY_RING
unsafe def POLY_SUBRING_GENERATED_1 : thm := BHomExtend.POLY_SUBRING_GENERATED_1
unsafe def IMAGE_POLY_EXTEND : thm := BHomExtend.IMAGE_POLY_EXTEND
unsafe def IMAGE_POLY_EXTEND_1 : thm := BHomExtend.IMAGE_POLY_EXTEND_1
unsafe def POLY_EXTEND_INTO_SUBRING_GENERATED : thm := BHomExtend.POLY_EXTEND_INTO_SUBRING_GENERATED

-- NatIso
unsafe def RING_ISOMORPHISM_POWSER_RING_TRIVIAL : thm := BNatIso.RING_ISOMORPHISM_POWSER_RING_TRIVIAL
unsafe def RING_ISOMORPHISM_POLY_RING_TRIVIAL : thm := BNatIso.RING_ISOMORPHISM_POLY_RING_TRIVIAL
unsafe def ISOMORPHIC_POWSER_RING_TRIVIAL : thm := BNatIso.ISOMORPHIC_POWSER_RING_TRIVIAL
unsafe def ISOMORPHIC_POLY_RING_TRIVIAL : thm := BNatIso.ISOMORPHIC_POLY_RING_TRIVIAL
unsafe def RING_ISOMORPHISMS_POWSER_RINGS : thm := BNatIso.RING_ISOMORPHISMS_POWSER_RINGS
unsafe def ISOMORPHIC_POWSER_RINGS : thm := BNatIso.ISOMORPHIC_POWSER_RINGS
unsafe def RING_ISOMORPHISMS_POLY_RINGS : thm := BNatIso.RING_ISOMORPHISMS_POLY_RINGS
unsafe def ISOMORPHIC_POLY_RINGS : thm := BNatIso.ISOMORPHIC_POLY_RINGS
unsafe def RING_ISOMORPHISMS_POWSER_POWSER_RING : thm := BNatIso.RING_ISOMORPHISMS_POWSER_POWSER_RING
unsafe def ISOMORPHIC_RING_POWSER_POWSER : thm := BNatIso.ISOMORPHIC_RING_POWSER_POWSER
unsafe def ISOMORPHIC_RING_POWSER_POWSER_GEN : thm := BNatIso.ISOMORPHIC_RING_POWSER_POWSER_GEN
unsafe def RING_CARRIER_POWSER_SUBRING_GENERATED : thm := BNatIso.RING_CARRIER_POWSER_SUBRING_GENERATED
unsafe def RING_CARRIER_POLY_SUBRING_GENERATED : thm := BNatIso.RING_CARRIER_POLY_SUBRING_GENERATED
unsafe def RING_CARRIER_POWSER_SUBRING_GENERATED_MONO : thm := BNatIso.RING_CARRIER_POWSER_SUBRING_GENERATED_MONO
unsafe def RING_CARRIER_POLY_SUBRING_GENERATED_MONO : thm := BNatIso.RING_CARRIER_POLY_SUBRING_GENERATED_MONO
unsafe def RING_CARRIER_POWSER_SUBRING_GENERATED_SUBSET : thm := BNatIso.RING_CARRIER_POWSER_SUBRING_GENERATED_SUBSET
unsafe def RING_CARRIER_POLY_SUBRING_GENERATED_SUBSET : thm := BNatIso.RING_CARRIER_POLY_SUBRING_GENERATED_SUBSET
unsafe def SUBRING_POWSER_INTO_SUBRING : thm := BNatIso.SUBRING_POWSER_INTO_SUBRING
unsafe def SUBRING_POLY_INTO_SUBRING : thm := BNatIso.SUBRING_POLY_INTO_SUBRING
unsafe def RING_ISOMORPHISMS_POWSER_SUBRING_GENERATED : thm := BNatIso.RING_ISOMORPHISMS_POWSER_SUBRING_GENERATED
unsafe def ISOMORPHIC_RINGS_POWSER_SUBRING_GENERATED : thm := BNatIso.ISOMORPHIC_RINGS_POWSER_SUBRING_GENERATED
unsafe def RING_ISOMORPHISMS_POLY_SUBRING_GENERATED : thm := BNatIso.RING_ISOMORPHISMS_POLY_SUBRING_GENERATED
unsafe def ISOMORPHIC_RINGS_POLY_SUBRING_GENERATED : thm := BNatIso.ISOMORPHIC_RINGS_POLY_SUBRING_GENERATED
unsafe def RING_ISOMORPHISMS_POLY_POLY_RING : thm := BNatIso.RING_ISOMORPHISMS_POLY_POLY_RING
unsafe def ISOMORPHIC_RING_POLY_POLY : thm := BNatIso.ISOMORPHIC_RING_POLY_POLY
unsafe def ISOMORPHIC_RING_POLY_POLY_GEN : thm := BNatIso.ISOMORPHIC_RING_POLY_POLY_GEN
unsafe def POLY_EXTEND_EXTEND : thm := BNatIso.POLY_EXTEND_EXTEND

-- Renaming
unsafe def poly_reindex : thm := BRenaming.poly_reindex
unsafe def RING_ISOMORPHISMS_POWSER_REINDEX : thm := BRenaming.RING_ISOMORPHISMS_POWSER_REINDEX
unsafe def RING_ISOMORPHISM_POWSER_REINDEX : thm := BRenaming.RING_ISOMORPHISM_POWSER_REINDEX
unsafe def RING_ISOMORPHISMS_POLY_REINDEX : thm := BRenaming.RING_ISOMORPHISMS_POLY_REINDEX
unsafe def POLY_VARS_REINDEX : thm := BRenaming.POLY_VARS_REINDEX
unsafe def RING_ISOMORPHISM_POLY_REINDEX : thm := BRenaming.RING_ISOMORPHISM_POLY_REINDEX
unsafe def POLY_REINDEX_CONST : thm := BRenaming.POLY_REINDEX_CONST
unsafe def POLY_REINDEX_VAR : thm := BRenaming.POLY_REINDEX_VAR
unsafe def MONOMIALS_POLY_REINDEX : thm := BRenaming.MONOMIALS_POLY_REINDEX
unsafe def POLY_EXTEND_REINDEX : thm := BRenaming.POLY_EXTEND_REINDEX
unsafe def RING_POWERSERIES_REINDEX : thm := BRenaming.RING_POWERSERIES_REINDEX
unsafe def POLY_RING_HOMOMORPHISM_I : thm := BRenaming.POLY_RING_HOMOMORPHISM_I
unsafe def POLY_CONST_DIVIDES_COEFFS : thm := BRenaming.POLY_CONST_DIVIDES_COEFFS
unsafe def POLY_CONST_DIVIDES_COEFFS_REV : thm := BRenaming.POLY_CONST_DIVIDES_COEFFS_REV
unsafe def POLY_CONST_DIVIDES_COEFFS_EQ : thm := BRenaming.POLY_CONST_DIVIDES_COEFFS_EQ
unsafe def POLY_CONST_DIVIDES_CONST : thm := BRenaming.POLY_CONST_DIVIDES_CONST

-- MonomialOrders
unsafe def POSET_MONOMIAL_DIVIDES : thm := BMonomialOrders.POSET_MONOMIAL_DIVIDES
unsafe def FLD_MONOMIAL_DIVIDES : thm := BMonomialOrders.FLD_MONOMIAL_DIVIDES
unsafe def COMPATIBLE_MONOMIAL_ORDER : thm := BMonomialOrders.COMPATIBLE_MONOMIAL_ORDER
unsafe def WQOSET_COMPATIBLE_MONOMIAL_ORDER : thm := BMonomialOrders.WQOSET_COMPATIBLE_MONOMIAL_ORDER
unsafe def WF_COMPATIBLE_MONOMIAL_ORDER : thm := BMonomialOrders.WF_COMPATIBLE_MONOMIAL_ORDER
unsafe def WOSET_COMPATIBLE_MONOMIAL_ORDER : thm := BMonomialOrders.WOSET_COMPATIBLE_MONOMIAL_ORDER
unsafe def monomial_le : thm := BMonomialOrders.monomial_le
unsafe def monomial_lt : thm := BMonomialOrders.monomial_lt
unsafe def PROPERLY_MONOMIAL_LE : thm := BMonomialOrders.PROPERLY_MONOMIAL_LE
unsafe def MONOMIAL_LE_MONO : thm := BMonomialOrders.MONOMIAL_LE_MONO
unsafe def MONOMIAL_LT_MONO : thm := BMonomialOrders.MONOMIAL_LT_MONO
unsafe def MONOMIAL_LE_PROPERLY : thm := BMonomialOrders.MONOMIAL_LE_PROPERLY
unsafe def MONOMIAL_LT_PROPERLY : thm := BMonomialOrders.MONOMIAL_LT_PROPERLY
unsafe def MONOMIAL_LE_IMPROPERLY : thm := BMonomialOrders.MONOMIAL_LE_IMPROPERLY
unsafe def MONOMIAL_LT_IMPROPERLY : thm := BMonomialOrders.MONOMIAL_LT_IMPROPERLY
unsafe def MONOMIAL_LE_REFL : thm := BMonomialOrders.MONOMIAL_LE_REFL
unsafe def MONOMIAL_LT_REFL : thm := BMonomialOrders.MONOMIAL_LT_REFL
unsafe def MONOMIAL_LT_IMP_LE : thm := BMonomialOrders.MONOMIAL_LT_IMP_LE
unsafe def MONOMIAL_LE_LT : thm := BMonomialOrders.MONOMIAL_LE_LT
unsafe def MONOMIAL_LE_TRANS : thm := BMonomialOrders.MONOMIAL_LE_TRANS
unsafe def QOSET_MONOMIAL_LE : thm := BMonomialOrders.QOSET_MONOMIAL_LE
unsafe def FLD_MONOMIAL_LE : thm := BMonomialOrders.FLD_MONOMIAL_LE
unsafe def MONOMIAL_LE_LMUL : thm := BMonomialOrders.MONOMIAL_LE_LMUL
unsafe def MONOMIAL_LE_RMUL : thm := BMonomialOrders.MONOMIAL_LE_RMUL
unsafe def MONOMIAL_LT_LMUL : thm := BMonomialOrders.MONOMIAL_LT_LMUL
unsafe def MONOMIAL_LT_RMUL : thm := BMonomialOrders.MONOMIAL_LT_RMUL
unsafe def MONOMIAL_LE_MUL2 : thm := BMonomialOrders.MONOMIAL_LE_MUL2
unsafe def MONOMIAL_LE_DIVISOR : thm := BMonomialOrders.MONOMIAL_LE_DIVISOR
unsafe def MONOMIAL_GE_1 : thm := BMonomialOrders.MONOMIAL_GE_1
unsafe def MONOMIAL_LE_VARS : thm := BMonomialOrders.MONOMIAL_LE_VARS
unsafe def MONOMIAL_LT_VARS : thm := BMonomialOrders.MONOMIAL_LT_VARS
unsafe def MONOMIAL_LE_POSET : thm := BMonomialOrders.MONOMIAL_LE_POSET
unsafe def MONOMIAL_LE_ANTISYM : thm := BMonomialOrders.MONOMIAL_LE_ANTISYM
unsafe def MONOMIAL_LET_ANTISYM : thm := BMonomialOrders.MONOMIAL_LET_ANTISYM
unsafe def MONOMIAL_LTE_ANTISYM : thm := BMonomialOrders.MONOMIAL_LTE_ANTISYM
unsafe def MONOMIAL_LT_ANTISYM : thm := BMonomialOrders.MONOMIAL_LT_ANTISYM
unsafe def MONOMIAL_LET_TRANS : thm := BMonomialOrders.MONOMIAL_LET_TRANS
unsafe def MONOMIAL_LTE_TRANS : thm := BMonomialOrders.MONOMIAL_LTE_TRANS
unsafe def MONOMIAL_LT_TRANS : thm := BMonomialOrders.MONOMIAL_LT_TRANS
unsafe def MONOMIAL_LET_MUL2 : thm := BMonomialOrders.MONOMIAL_LET_MUL2
unsafe def MONOMIAL_LTE_MUL2 : thm := BMonomialOrders.MONOMIAL_LTE_MUL2
unsafe def MONOMIAL_LT_MUL2 : thm := BMonomialOrders.MONOMIAL_LT_MUL2
unsafe def POSET_MONOMIAL_LE : thm := BMonomialOrders.POSET_MONOMIAL_LE
unsafe def MONOMIAL_LE_VARS_EQ : thm := BMonomialOrders.MONOMIAL_LE_VARS_EQ
unsafe def MONOMIAL_LT_VARS_EQ : thm := BMonomialOrders.MONOMIAL_LT_VARS_EQ
unsafe def MONOMIAL_LT_TOSET : thm := BMonomialOrders.MONOMIAL_LT_TOSET
unsafe def MONOMIAL_LE_TOSET : thm := BMonomialOrders.MONOMIAL_LE_TOSET
unsafe def TOSET_MONOMIAL_LE : thm := BMonomialOrders.TOSET_MONOMIAL_LE
unsafe def WF_MONOMIAL_LT : thm := BMonomialOrders.WF_MONOMIAL_LT
unsafe def WOSET_MONOMIAL_LE : thm := BMonomialOrders.WOSET_MONOMIAL_LE

-- OneCoeff
unsafe def EXISTS_FUN_FROM_1 : thm := BOneCoeff.EXISTS_FUN_FROM_1
unsafe def FORALL_FUN_FROM_1 : thm := BOneCoeff.FORALL_FUN_FROM_1
unsafe def LAMBDA_1_EQ : thm := BOneCoeff.LAMBDA_1_EQ
unsafe def FUN_ONE_NUM_EQ : thm := BOneCoeff.FUN_ONE_NUM_EQ
unsafe def FUN_ONE_EQ_ONE : thm := BOneCoeff.FUN_ONE_EQ_ONE
unsafe def FINITE_FUN_FROM_1 : thm := BOneCoeff.FINITE_FUN_FROM_1
unsafe def MONOMIAL_DIVISORS_1 : thm := BOneCoeff.MONOMIAL_DIVISORS_1
unsafe def coeff : thm := BOneCoeff.coeff
unsafe def COEFF : thm := BOneCoeff.COEFF
unsafe def COEFF_0 : thm := BOneCoeff.COEFF_0
unsafe def FUN_EQ_COEFF : thm := BOneCoeff.FUN_EQ_COEFF
unsafe def RING_POLYNOMIAL_POWERSERIES_COEFF : thm := BOneCoeff.RING_POLYNOMIAL_POWERSERIES_COEFF
unsafe def RING_POWERSERIES_COEFF : thm := BOneCoeff.RING_POWERSERIES_COEFF
unsafe def COEFF_IN_CARRIER : thm := BOneCoeff.COEFF_IN_CARRIER
unsafe def COEFF_IN_CARRIER_ALT : thm := BOneCoeff.COEFF_IN_CARRIER_ALT
unsafe def RING_POLYNOMIAL_COEFF : thm := BOneCoeff.RING_POLYNOMIAL_COEFF
unsafe def COEFF_COMPOSE : thm := BOneCoeff.COEFF_COMPOSE
unsafe def COEFF_POLY_CONST : thm := BOneCoeff.COEFF_POLY_CONST
unsafe def COEFF_POLY_0 : thm := BOneCoeff.COEFF_POLY_0
unsafe def COEFF_POLY_1 : thm := BOneCoeff.COEFF_POLY_1
unsafe def COEFF_POLY_VAR : thm := BOneCoeff.COEFF_POLY_VAR
unsafe def COEFF_POLY_NEG : thm := BOneCoeff.COEFF_POLY_NEG
unsafe def COEFF_POLY_ADD : thm := BOneCoeff.COEFF_POLY_ADD
unsafe def COEFF_POLY_SUB : thm := BOneCoeff.COEFF_POLY_SUB
unsafe def COEFF_POLY_MUL_ALT : thm := BOneCoeff.COEFF_POLY_MUL_ALT
unsafe def COEFF_POLY_MUL : thm := BOneCoeff.COEFF_POLY_MUL
unsafe def COEFF_POLY_VARPOW : thm := BOneCoeff.COEFF_POLY_VARPOW
unsafe def COEFF_POLY_LMUL : thm := BOneCoeff.COEFF_POLY_LMUL
unsafe def COEFF_POLY_RMUL : thm := BOneCoeff.COEFF_POLY_RMUL
unsafe def COEFF_POLY_VAR_MUL : thm := BOneCoeff.COEFF_POLY_VAR_MUL
unsafe def COEFF_POLY_MUL_VAR : thm := BOneCoeff.COEFF_POLY_MUL_VAR
unsafe def COEFF_POLY_VARPOW_MUL : thm := BOneCoeff.COEFF_POLY_VARPOW_MUL
unsafe def COEFF_POLY_MUL_VARPOW : thm := BOneCoeff.COEFF_POLY_MUL_VARPOW
unsafe def POLY_MUL_UNIVARIATE : thm := BOneCoeff.POLY_MUL_UNIVARIATE
unsafe def RING_POLYNOMIAL_SUBRING_COEFF : thm := BOneCoeff.RING_POLYNOMIAL_SUBRING_COEFF
unsafe def FINITE_COEFF_SUPPORT : thm := BOneCoeff.FINITE_COEFF_SUPPORT
unsafe def RING_POLYNOMIAL_COEFF_BOUND : thm := BOneCoeff.RING_POLYNOMIAL_COEFF_BOUND
unsafe def RING_POLYNOMIAL_COEFF_ZERO_FROM : thm := BOneCoeff.RING_POLYNOMIAL_COEFF_ZERO_FROM

-- Degree
unsafe def poly_deg : thm := BDegree.poly_deg
unsafe def POLY_DEG_SUBRING_GENERATED : thm := BDegree.POLY_DEG_SUBRING_GENERATED
unsafe def POLY_DEG_CONST : thm := BDegree.POLY_DEG_CONST
unsafe def POLY_DEG_0 : thm := BDegree.POLY_DEG_0
unsafe def POLY_DEG_1 : thm := BDegree.POLY_DEG_1
unsafe def POLY_DEG_LE_EQ : thm := BDegree.POLY_DEG_LE_EQ
unsafe def POLY_DEG_LE : thm := BDegree.POLY_DEG_LE
unsafe def MONOMIAL_DEG_LE_POLY_DEG : thm := BDegree.MONOMIAL_DEG_LE_POLY_DEG
unsafe def POLY_DEG_GE_EQ : thm := BDegree.POLY_DEG_GE_EQ
unsafe def POLY_DEG_GE : thm := BDegree.POLY_DEG_GE
unsafe def COEFF_ABOVE_DEG : thm := BDegree.COEFF_ABOVE_DEG
unsafe def POLY_DEG_MONOMIAL_EXISTS : thm := BDegree.POLY_DEG_MONOMIAL_EXISTS
unsafe def POLY_TOP_MONOMIAL_LE : thm := BDegree.POLY_TOP_MONOMIAL_LE
unsafe def POLY_TOP_MONOMIAL_LT : thm := BDegree.POLY_TOP_MONOMIAL_LT
unsafe def POLY_DEG_EQ_0_ALT : thm := BDegree.POLY_DEG_EQ_0_ALT
unsafe def POLY_DEG_EQ_0 : thm := BDegree.POLY_DEG_EQ_0
unsafe def POLY_DEG_EQ : thm := BDegree.POLY_DEG_EQ
unsafe def POLY_DEG_UNIQUE : thm := BDegree.POLY_DEG_UNIQUE
unsafe def POLY_DEG_VAR : thm := BDegree.POLY_DEG_VAR
unsafe def COEFF_NONZERO_LE_DEG : thm := BDegree.COEFF_NONZERO_LE_DEG
unsafe def COEFF_NONZERO_LE : thm := BDegree.COEFF_NONZERO_LE
unsafe def POLY_DEG_LE_COEFF_EQ : thm := BDegree.POLY_DEG_LE_COEFF_EQ
unsafe def POLY_DEG_LE_COEFF : thm := BDegree.POLY_DEG_LE_COEFF
unsafe def POLY_DEG_GE_COEFF_EQ : thm := BDegree.POLY_DEG_GE_COEFF_EQ
unsafe def POLY_DEG_GE_COEFF : thm := BDegree.POLY_DEG_GE_COEFF
unsafe def POLY_DEG_EQ_COEFF_EQ : thm := BDegree.POLY_DEG_EQ_COEFF_EQ
unsafe def POLY_DEG_EQ_COEFF : thm := BDegree.POLY_DEG_EQ_COEFF
unsafe def POLY_DEG_EQ_FROM_LE : thm := BDegree.POLY_DEG_EQ_FROM_LE
unsafe def COEFF_POWSER_SUM : thm := BDegree.COEFF_POWSER_SUM
unsafe def COEFF_POLY_SUM : thm := BDegree.COEFF_POLY_SUM
unsafe def POLY_DEG_NEG : thm := BDegree.POLY_DEG_NEG
unsafe def POLY_DEG_ADD_LE : thm := BDegree.POLY_DEG_ADD_LE
unsafe def POLY_DEG_SUB_LE : thm := BDegree.POLY_DEG_SUB_LE
unsafe def POLY_DEG_ADD : thm := BDegree.POLY_DEG_ADD
unsafe def POLY_DEG_SUB : thm := BDegree.POLY_DEG_SUB
unsafe def POLY_DEG_MUL_LE : thm := BDegree.POLY_DEG_MUL_LE
unsafe def POLY_DEG_POW_LE : thm := BDegree.POLY_DEG_POW_LE
unsafe def POLY_DEG_MUL : thm := BDegree.POLY_DEG_MUL
unsafe def POLY_DEG_CMUL : thm := BDegree.POLY_DEG_CMUL
unsafe def POLY_MUL_LEADING_COEFF : thm := BDegree.POLY_MUL_LEADING_COEFF
unsafe def POLY_DEG_MUL_UNIVARIATE : thm := BDegree.POLY_DEG_MUL_UNIVARIATE
unsafe def POLY_DEG_VAR_MUL : thm := BDegree.POLY_DEG_VAR_MUL
unsafe def POLY_DEG_MUL_VAR : thm := BDegree.POLY_DEG_MUL_VAR
unsafe def POLY_DEG_VARPOW_MUL : thm := BDegree.POLY_DEG_VARPOW_MUL
unsafe def POLY_DEG_MUL_VARPOW : thm := BDegree.POLY_DEG_MUL_VARPOW
unsafe def INTEGRAL_DOMAIN_POLY_RING : thm := BDegree.INTEGRAL_DOMAIN_POLY_RING
unsafe def POLY_DEG_POW : thm := BDegree.POLY_DEG_POW
unsafe def POLY_DEG_DIVIDES_LE : thm := BDegree.POLY_DEG_DIVIDES_LE
unsafe def POLY_DEG_RING_ADD_LE : thm := BDegree.POLY_DEG_RING_ADD_LE
unsafe def POLY_DEG_RING_SUB_LE : thm := BDegree.POLY_DEG_RING_SUB_LE
unsafe def POLY_DEG_RING_SUM_LE : thm := BDegree.POLY_DEG_RING_SUM_LE
unsafe def POLY_DEG_VAR_POW : thm := BDegree.POLY_DEG_VAR_POW
unsafe def POLY_POLY_DEG_EQ_0 : thm := BDegree.POLY_POLY_DEG_EQ_0
unsafe def POLY_VARS_MUL_EQ : thm := BDegree.POLY_VARS_MUL_EQ
unsafe def POLY_VARS_POW_EQ : thm := BDegree.POLY_VARS_POW_EQ

-- Cardinalities
unsafe def CARD_EQ_MONOMIALS_FINITE : thm := BCardinalities.CARD_EQ_MONOMIALS_FINITE
unsafe def CARD_EQ_MONOMIALS_INFINITE : thm := BCardinalities.CARD_EQ_MONOMIALS_INFINITE
unsafe def CARD_EQ_MONOMIALS_COUNTABLE : thm := BCardinalities.CARD_EQ_MONOMIALS_COUNTABLE
unsafe def CARD_EQ_POWSER_RING_COUNTABLE : thm := BCardinalities.CARD_EQ_POWSER_RING_COUNTABLE
unsafe def CARD_EQ_POWSER_RING_FINITE : thm := BCardinalities.CARD_EQ_POWSER_RING_FINITE
unsafe def CARD_EQ_POWSER_RING_INFINITE : thm := BCardinalities.CARD_EQ_POWSER_RING_INFINITE
unsafe def CARD_EQ_POLY_RING_COUNTABLE : thm := BCardinalities.CARD_EQ_POLY_RING_COUNTABLE
unsafe def CARD_EQ_POLY_RING_FINITE : thm := BCardinalities.CARD_EQ_POLY_RING_FINITE
unsafe def CARD_EQ_POLY_RING_INFINITE : thm := BCardinalities.CARD_EQ_POLY_RING_INFINITE

-- Evaluation
unsafe def poly_evaluate : thm := BEvaluation.poly_evaluate
unsafe def POLY_EVALUATE : thm := BEvaluation.POLY_EVALUATE
unsafe def POLY_EVALUATE_0 : thm := BEvaluation.POLY_EVALUATE_0
unsafe def POLY_EVALUATE_1 : thm := BEvaluation.POLY_EVALUATE_1
unsafe def POLY_EVALUATE_VAR : thm := BEvaluation.POLY_EVALUATE_VAR
unsafe def POLY_EVALUATE_CONST : thm := BEvaluation.POLY_EVALUATE_CONST
unsafe def POLY_EVALUATE_ADD : thm := BEvaluation.POLY_EVALUATE_ADD
unsafe def POLY_EVALUATE_SUB : thm := BEvaluation.POLY_EVALUATE_SUB
unsafe def POLY_EVALUATE_MUL : thm := BEvaluation.POLY_EVALUATE_MUL
unsafe def POLY_EVALUATE_POW : thm := BEvaluation.POLY_EVALUATE_POW
unsafe def POLY_EVALUATE_RING_SUM : thm := BEvaluation.POLY_EVALUATE_RING_SUM
unsafe def POLY_EVALUATE_RING_PRODUCT : thm := BEvaluation.POLY_EVALUATE_RING_PRODUCT
unsafe def RING_HOMOMORPHISM_POLY_EVALUATE : thm := BEvaluation.RING_HOMOMORPHISM_POLY_EVALUATE
unsafe def RING_EPIMORPHISM_POLY_EVALUATE : thm := BEvaluation.RING_EPIMORPHISM_POLY_EVALUATE
unsafe def POLY_EVALUATE_HOMOMORPHIC_IMAGE : thm := BEvaluation.POLY_EVALUATE_HOMOMORPHIC_IMAGE
unsafe def POLY_EXTEND_EVALUATE : thm := BEvaluation.POLY_EXTEND_EVALUATE
unsafe def POLY_EVALUATE_EQ : thm := BEvaluation.POLY_EVALUATE_EQ
unsafe def POWSER_EVALUATE_AT_0 : thm := BEvaluation.POWSER_EVALUATE_AT_0
unsafe def POLY_EVALUATE_AT_0 : thm := BEvaluation.POLY_EVALUATE_AT_0
unsafe def RING_HOMOMORPHISM_POWSER_EVALUATE_AT_0 : thm := BEvaluation.RING_HOMOMORPHISM_POWSER_EVALUATE_AT_0
unsafe def RING_EPIMORPHISM_POWSER_EVALUATE_AT_0 : thm := BEvaluation.RING_EPIMORPHISM_POWSER_EVALUATE_AT_0
unsafe def POLY_EVALUATE_REINDEX : thm := BEvaluation.POLY_EVALUATE_REINDEX
unsafe def poly_eval : thm := BEvaluation.poly_eval
unsafe def POLY_EVAL : thm := BEvaluation.POLY_EVAL
unsafe def POLY_EVAL_0 : thm := BEvaluation.POLY_EVAL_0
unsafe def POLY_EVAL_1 : thm := BEvaluation.POLY_EVAL_1
unsafe def POLY_EVAL_VAR : thm := BEvaluation.POLY_EVAL_VAR
unsafe def POLY_EVAL_CONST : thm := BEvaluation.POLY_EVAL_CONST
unsafe def POLY_EVAL_ADD : thm := BEvaluation.POLY_EVAL_ADD
unsafe def POLY_EVAL_SUB : thm := BEvaluation.POLY_EVAL_SUB
unsafe def POLY_EVAL_MUL : thm := BEvaluation.POLY_EVAL_MUL
unsafe def POLY_EVAL_POW : thm := BEvaluation.POLY_EVAL_POW
unsafe def POLY_EVAL_RING_SUM : thm := BEvaluation.POLY_EVAL_RING_SUM
unsafe def POLY_EVAL_RING_PRODUCT : thm := BEvaluation.POLY_EVAL_RING_PRODUCT
unsafe def RING_HOMOMORPHISM_POLY_EVAL : thm := BEvaluation.RING_HOMOMORPHISM_POLY_EVAL
unsafe def RING_EPIMORPHISM_POLY_EVAL : thm := BEvaluation.RING_EPIMORPHISM_POLY_EVAL
unsafe def POLY_EVAL_HOMOMORPHIC_IMAGE : thm := BEvaluation.POLY_EVAL_HOMOMORPHIC_IMAGE
unsafe def POLY_EXTEND_UNIVARIATE : thm := BEvaluation.POLY_EXTEND_UNIVARIATE
unsafe def POLY_EVAL_EXPAND : thm := BEvaluation.POLY_EVAL_EXPAND
unsafe def POLY_EXPAND : thm := BEvaluation.POLY_EXPAND
unsafe def POWSER_EVAL_AT_0 : thm := BEvaluation.POWSER_EVAL_AT_0
unsafe def POLY_EVAL_AT_0 : thm := BEvaluation.POLY_EVAL_AT_0
unsafe def RING_HOMOMORPHISM_POWSER_EVAL_AT_0 : thm := BEvaluation.RING_HOMOMORPHISM_POWSER_EVAL_AT_0
unsafe def RING_EPIMORPHISM_POWSER_EVAL_AT_0 : thm := BEvaluation.RING_EPIMORPHISM_POWSER_EVAL_AT_0
unsafe def POWSER_RING_HOMOMORPHISM_COEFF_0 : thm := BEvaluation.POWSER_RING_HOMOMORPHISM_COEFF_0
unsafe def POLY_RING_HOMOMORPHISM_COEFF_0 : thm := BEvaluation.POLY_RING_HOMOMORPHISM_COEFF_0
unsafe def POWSER_RING_EPIMORPHISM_COEFF_0 : thm := BEvaluation.POWSER_RING_EPIMORPHISM_COEFF_0
unsafe def POLY_RING_EPIMORPHISM_COEFF_0 : thm := BEvaluation.POLY_RING_EPIMORPHISM_COEFF_0
unsafe def POLY_EVAL_COEFF : thm := BEvaluation.POLY_EVAL_COEFF
unsafe def IMAGE_POLY_EVAL : thm := BEvaluation.IMAGE_POLY_EVAL
unsafe def POLY_VAR_DIVIDES_UNIVARIATE : thm := BEvaluation.POLY_VAR_DIVIDES_UNIVARIATE

-- Composing
unsafe def RING_POWERSERIES_COMPOSE : thm := BComposing.RING_POWERSERIES_COMPOSE
unsafe def IN_RING_POWERSERIES_CARRIER_COMPOSE : thm := BComposing.IN_RING_POWERSERIES_CARRIER_COMPOSE
unsafe def RING_POLYNOMIAL_COMPOSE : thm := BComposing.RING_POLYNOMIAL_COMPOSE
unsafe def IN_RING_POLYNOMIAL_CARRIER_COMPOSE : thm := BComposing.IN_RING_POLYNOMIAL_CARRIER_COMPOSE
unsafe def POLY_DEG_HOMOMORPHIC_IMAGE : thm := BComposing.POLY_DEG_HOMOMORPHIC_IMAGE
unsafe def POLY_DEG_MONOMORPHIC_IMAGE : thm := BComposing.POLY_DEG_MONOMORPHIC_IMAGE
unsafe def POLY_EQ_0_MONOMORPHIC_IMAGE : thm := BComposing.POLY_EQ_0_MONOMORPHIC_IMAGE
unsafe def RING_HOMOMORPHISM_POWSER_RINGS : thm := BComposing.RING_HOMOMORPHISM_POWSER_RINGS
unsafe def RING_HOMOMORPHISM_POLY_RINGS : thm := BComposing.RING_HOMOMORPHISM_POLY_RINGS
unsafe def RING_MONOMORPHISM_POWSER_RINGS : thm := BComposing.RING_MONOMORPHISM_POWSER_RINGS
unsafe def RING_MONOMORPHISM_POLY_RINGS : thm := BComposing.RING_MONOMORPHISM_POLY_RINGS
unsafe def RING_EPIMORPHISM_POWSER_RINGS : thm := BComposing.RING_EPIMORPHISM_POWSER_RINGS
unsafe def RING_EPIMORPHISM_POLY_RINGS : thm := BComposing.RING_EPIMORPHISM_POLY_RINGS
unsafe def RING_ISOMORPHISM_POWSER_RINGS : thm := BComposing.RING_ISOMORPHISM_POWSER_RINGS
unsafe def RING_ISOMORPHISM_POLY_RINGS : thm := BComposing.RING_ISOMORPHISM_POLY_RINGS
unsafe def POLY_COMPOSE_HOMOMORPHISM_VAR : thm := BComposing.POLY_COMPOSE_HOMOMORPHISM_VAR
unsafe def POLY_COMPOSE_HOMOMORPHISM_CONST : thm := BComposing.POLY_COMPOSE_HOMOMORPHISM_CONST
unsafe def POLY_COMPOSE_HOMOMORPHISM_NEG : thm := BComposing.POLY_COMPOSE_HOMOMORPHISM_NEG
unsafe def POLY_COMPOSE_HOMOMORPHISM_MUL : thm := BComposing.POLY_COMPOSE_HOMOMORPHISM_MUL
unsafe def POLY_COMPOSE_HOMOMORPHISM_SUB : thm := BComposing.POLY_COMPOSE_HOMOMORPHISM_SUB
unsafe def POLY_COMPOSE_HOMOMORPHISM_ADD : thm := BComposing.POLY_COMPOSE_HOMOMORPHISM_ADD
unsafe def POLY_COMPOSE_HOMOMORPHISM_POW : thm := BComposing.POLY_COMPOSE_HOMOMORPHISM_POW

-- Zerodivisors
unsafe def INTEGRAL_DOMAIN_POWSER_RING : thm := BZerodivisors.INTEGRAL_DOMAIN_POWSER_RING
unsafe def RING_UNIT_POLY_CONST : thm := BZerodivisors.RING_UNIT_POLY_CONST
unsafe def RING_UNIT_POLY_DOMAIN : thm := BZerodivisors.RING_UNIT_POLY_DOMAIN
unsafe def RING_NILPOTENT_POLY_RING : thm := BZerodivisors.RING_NILPOTENT_POLY_RING
unsafe def RING_UNIT_POLY_RING : thm := BZerodivisors.RING_UNIT_POLY_RING
unsafe def RING_UNIT_POLY_RING_1 : thm := BZerodivisors.RING_UNIT_POLY_RING_1
unsafe def RING_UNIT_POLY_VAR : thm := BZerodivisors.RING_UNIT_POLY_VAR
unsafe def FIELD_POLY_RING : thm := BZerodivisors.FIELD_POLY_RING
unsafe def POLY_DEG_UNIT : thm := BZerodivisors.POLY_DEG_UNIT
unsafe def POLY_DEG_EQ_0_UNIT : thm := BZerodivisors.POLY_DEG_EQ_0_UNIT
unsafe def IRREDUCIBLE_IMP_POLY_DEG_NZ : thm := BZerodivisors.IRREDUCIBLE_IMP_POLY_DEG_NZ
unsafe def POLY_DEG_1_IMP_IRREDUCIBLE : thm := BZerodivisors.POLY_DEG_1_IMP_IRREDUCIBLE
unsafe def RING_UNIT_POWSER_RING : thm := BZerodivisors.RING_UNIT_POWSER_RING
unsafe def LOCAL_POWSER_RING : thm := BZerodivisors.LOCAL_POWSER_RING
unsafe def RING_PRIME_POLY_VAR_UNIVARIATE : thm := BZerodivisors.RING_PRIME_POLY_VAR_UNIVARIATE
unsafe def RING_PRIME_POLY_VAR : thm := BZerodivisors.RING_PRIME_POLY_VAR
unsafe def RING_IRREDUCIBLE_POLY_VAR : thm := BZerodivisors.RING_IRREDUCIBLE_POLY_VAR
unsafe def RING_PRIME_POLY_CONST : thm := BZerodivisors.RING_PRIME_POLY_CONST
unsafe def RING_IRREDUCIBLE_POLY_CONST : thm := BZerodivisors.RING_IRREDUCIBLE_POLY_CONST

-- XMinusA
unsafe def POLY_DEG_X_MINUS_A : thm := BXMinusA.POLY_DEG_X_MINUS_A
unsafe def POLY_X_MINUS_A_NONZERO : thm := BXMinusA.POLY_X_MINUS_A_NONZERO
unsafe def POLY_X_MINUS_A_IN_CARRIER : thm := BXMinusA.POLY_X_MINUS_A_IN_CARRIER
unsafe def POLY_DIVIDES_X_MINUS_A : thm := BXMinusA.POLY_DIVIDES_X_MINUS_A
unsafe def POLY_DIVIDES_X_MINUS_ROOT : thm := BXMinusA.POLY_DIVIDES_X_MINUS_ROOT
unsafe def POLY_DIVIDES_X_MINUS_ROOT_EQ : thm := BXMinusA.POLY_DIVIDES_X_MINUS_ROOT_EQ
unsafe def POLY_DEG_MUL_X_MINUS_A : thm := BXMinusA.POLY_DEG_MUL_X_MINUS_A
unsafe def POLY_ROOT_BOUND : thm := BXMinusA.POLY_ROOT_BOUND
unsafe def INFINITE_INTEGRAL_DOMAIN_POLY_EVAL_ALL_ZERO : thm := BXMinusA.INFINITE_INTEGRAL_DOMAIN_POLY_EVAL_ALL_ZERO

-- Division
unsafe def POLY_TOP_NONZERO : thm := BDivision.POLY_TOP_NONZERO
unsafe def POLY_TOP_TAIL : thm := BDivision.POLY_TOP_TAIL
unsafe def POLY_TOP_EQ_0 : thm := BDivision.POLY_TOP_EQ_0
unsafe def POLY_DEG_LT_FROM_LE : thm := BDivision.POLY_DEG_LT_FROM_LE
unsafe def POLY_DEG_DIVIDES_LE_UNIVARIATE : thm := BDivision.POLY_DEG_DIVIDES_LE_UNIVARIATE
unsafe def POLY_DIVISION_GEN : thm := BDivision.POLY_DIVISION_GEN
unsafe def POLY_DIVISION : thm := BDivision.POLY_DIVISION
unsafe def EUCLIDEAN_POLY_RING : thm := BDivision.EUCLIDEAN_POLY_RING
unsafe def PID_POLY_RING : thm := BDivision.PID_POLY_RING
unsafe def POLY_DEG_1_ROOT : thm := BDivision.POLY_DEG_1_ROOT
unsafe def poly_div : thm := BDivision.poly_div
unsafe def poly_rem : thm := BDivision.poly_rem
unsafe def POLY_DIV_REM : thm := BDivision.POLY_DIV_REM
unsafe def POLY_DIV : thm := BDivision.POLY_DIV
unsafe def RING_POLYNOMIAL_DIV : thm := BDivision.RING_POLYNOMIAL_DIV
unsafe def POLY_REM : thm := BDivision.POLY_REM
unsafe def RING_POLYNOMIAL_REM : thm := BDivision.RING_POLYNOMIAL_REM
unsafe def POLY_DIV_REM_SIMP : thm := BDivision.POLY_DIV_REM_SIMP
unsafe def POLY_DEG_REM : thm := BDivision.POLY_DEG_REM
unsafe def POLY_DEG_REM_ALT : thm := BDivision.POLY_DEG_REM_ALT
unsafe def POLY_DIVIDES_REM : thm := BDivision.POLY_DIVIDES_REM
unsafe def POLY_REM_UNIQUE : thm := BDivision.POLY_REM_UNIQUE

-- Hilbert
unsafe def NOETHERIAN_POLY_RING_1 : thm := BHilbert.NOETHERIAN_POLY_RING_1
unsafe def NOETHERIAN_POLY_RING : thm := BHilbert.NOETHERIAN_POLY_RING
unsafe def KAPLANSKY_LEMMA : thm := BHilbert.KAPLANSKY_LEMMA
unsafe def NOETHERIAN_POWSER_RING_1 : thm := BHilbert.NOETHERIAN_POWSER_RING_1
unsafe def NOETHERIAN_POWSER_RING : thm := BHilbert.NOETHERIAN_POWSER_RING

-- Monic
unsafe def monic : thm := BMonic.monic
unsafe def MONIC_POLY_1 : thm := BMonic.MONIC_POLY_1
unsafe def MONIC_POLY_0 : thm := BMonic.MONIC_POLY_0
unsafe def MONIC_IMP_NONZERO : thm := BMonic.MONIC_IMP_NONZERO
unsafe def MONIC_IN_TRIVIAL_RING : thm := BMonic.MONIC_IN_TRIVIAL_RING
unsafe def MONIC_POLY_CONST : thm := BMonic.MONIC_POLY_CONST
unsafe def MONIC_DEG_0 : thm := BMonic.MONIC_DEG_0
unsafe def MONIC_POLY_VAR : thm := BMonic.MONIC_POLY_VAR
unsafe def MONIC_SUBRING_GENERATED : thm := BMonic.MONIC_SUBRING_GENERATED
unsafe def POLY_DEG_MUL_MONIC : thm := BMonic.POLY_DEG_MUL_MONIC
unsafe def MONIC_POLY_MUL : thm := BMonic.MONIC_POLY_MUL
unsafe def MONIC_POLY_POW : thm := BMonic.MONIC_POLY_POW
unsafe def MONIC_POLY_PRODUCT : thm := BMonic.MONIC_POLY_PRODUCT
unsafe def MONIC_ASSOCIATES_EQ : thm := BMonic.MONIC_ASSOCIATES_EQ
unsafe def MONIC_CMUL : thm := BMonic.MONIC_CMUL
unsafe def FIELD_MONIC_ASSOCIATE : thm := BMonic.FIELD_MONIC_ASSOCIATE
unsafe def FIELD_MONIC_IRREDUCIBLE_ASSOCIATE : thm := BMonic.FIELD_MONIC_IRREDUCIBLE_ASSOCIATE
unsafe def RING_COPRIME_DISTINCT_MONIC_IRREDUCIBLES : thm := BMonic.RING_COPRIME_DISTINCT_MONIC_IRREDUCIBLES
unsafe def POLY_DEG_DIVIDES_LE_MONIC : thm := BMonic.POLY_DEG_DIVIDES_LE_MONIC

-- Reciprocal
unsafe def poly_recip : thm := BReciprocal.poly_recip
unsafe def COEFF_POLY_RECIP : thm := BReciprocal.COEFF_POLY_RECIP
unsafe def RING_POWERSERIES_RECIP : thm := BReciprocal.RING_POWERSERIES_RECIP
unsafe def RING_POLYNOMIAL_RECIP : thm := BReciprocal.RING_POLYNOMIAL_RECIP
unsafe def POLY_RECIP_IN_CARRIER : thm := BReciprocal.POLY_RECIP_IN_CARRIER
unsafe def COEFF_0_POLY_RECIP_EQ_0 : thm := BReciprocal.COEFF_0_POLY_RECIP_EQ_0
unsafe def POLY_DEG_RECIP_LE : thm := BReciprocal.POLY_DEG_RECIP_LE
unsafe def POLY_DEG_RECIP : thm := BReciprocal.POLY_DEG_RECIP
unsafe def POLY_RECIP_RECIP : thm := BReciprocal.POLY_RECIP_RECIP
unsafe def POLY_VARPOW_RECIP_RECIP : thm := BReciprocal.POLY_VARPOW_RECIP_RECIP
unsafe def POLY_DIVIDES_RECIP_RECIP : thm := BReciprocal.POLY_DIVIDES_RECIP_RECIP
unsafe def POLY_RECIP_CONST : thm := BReciprocal.POLY_RECIP_CONST
unsafe def RING_UNIT_POLY_RECIP : thm := BReciprocal.RING_UNIT_POLY_RECIP
unsafe def RING_UNIT_POLY_RECIP_EQ : thm := BReciprocal.RING_UNIT_POLY_RECIP_EQ
unsafe def POLY_RECIP_0 : thm := BReciprocal.POLY_RECIP_0
unsafe def POLY_RECIP_EQ_0 : thm := BReciprocal.POLY_RECIP_EQ_0
unsafe def POLY_RECIP_RECIP_EQ : thm := BReciprocal.POLY_RECIP_RECIP_EQ
unsafe def POLY_RECIP_1 : thm := BReciprocal.POLY_RECIP_1
unsafe def POLY_RECIP_NEG : thm := BReciprocal.POLY_RECIP_NEG
unsafe def POLY_RECIP_MUL_GEN : thm := BReciprocal.POLY_RECIP_MUL_GEN
unsafe def POLY_RECIP_MUL : thm := BReciprocal.POLY_RECIP_MUL
unsafe def POLY_DIVIDES_RECIP : thm := BReciprocal.POLY_DIVIDES_RECIP
unsafe def POLY_DIVIDES_RECIP_GALOIS : thm := BReciprocal.POLY_DIVIDES_RECIP_GALOIS
unsafe def POLY_DIVIDES_RECIP_EQ : thm := BReciprocal.POLY_DIVIDES_RECIP_EQ
unsafe def RING_PRIME_POLY_RECIP : thm := BReciprocal.RING_PRIME_POLY_RECIP
unsafe def RING_PRIME_POLY_RECIP_EQ : thm := BReciprocal.RING_PRIME_POLY_RECIP_EQ
unsafe def RING_IRREDUCIBLE_POLY_RECIP : thm := BReciprocal.RING_IRREDUCIBLE_POLY_RECIP
unsafe def RING_IRREDUCIBLE_POLY_RECIP_EQ : thm := BReciprocal.RING_IRREDUCIBLE_POLY_RECIP_EQ
unsafe def POLY_EVAL_RECIP : thm := BReciprocal.POLY_EVAL_RECIP

-- Derivative
unsafe def poly_deriv : thm := BDerivative.poly_deriv
unsafe def POLY_DERIV_SUBRING_GENERATED : thm := BDerivative.POLY_DERIV_SUBRING_GENERATED
unsafe def COEFF_POLY_DERIV : thm := BDerivative.COEFF_POLY_DERIV
unsafe def RING_POWERSERIES_POLY_DERIV : thm := BDerivative.RING_POWERSERIES_POLY_DERIV
unsafe def POWSER_DERIV_IN_CARRIER : thm := BDerivative.POWSER_DERIV_IN_CARRIER
unsafe def RING_POLYNOMIAL_POLY_DERIV : thm := BDerivative.RING_POLYNOMIAL_POLY_DERIV
unsafe def POLY_DERIV_IN_CARRIER : thm := BDerivative.POLY_DERIV_IN_CARRIER
unsafe def POLY_DEG_DERIV_LE : thm := BDerivative.POLY_DEG_DERIV_LE
unsafe def POLY_DEG_DERIV : thm := BDerivative.POLY_DEG_DERIV
unsafe def POLY_DERIV_NONZERO_CHAR0 : thm := BDerivative.POLY_DERIV_NONZERO_CHAR0
unsafe def POLY_DERIV_CONST : thm := BDerivative.POLY_DERIV_CONST
unsafe def POLY_DERIV_0 : thm := BDerivative.POLY_DERIV_0
unsafe def POLY_DERIV_1 : thm := BDerivative.POLY_DERIV_1
unsafe def POLY_DERIV_VAR : thm := BDerivative.POLY_DERIV_VAR
unsafe def POLY_DERIV_ADD : thm := BDerivative.POLY_DERIV_ADD
unsafe def POLY_DERIV_NEG : thm := BDerivative.POLY_DERIV_NEG
unsafe def POLY_DERIV_SUB : thm := BDerivative.POLY_DERIV_SUB
unsafe def POLY_DERIV_CMUL : thm := BDerivative.POLY_DERIV_CMUL
unsafe def POLY_DERIV_HOMOMORPHIC_IMAGE : thm := BDerivative.POLY_DERIV_HOMOMORPHIC_IMAGE
unsafe def POLY_DERIV_MUL : thm := BDerivative.POLY_DERIV_MUL
unsafe def POLY_DERIV_SUM : thm := BDerivative.POLY_DERIV_SUM
unsafe def POLY_DERIV_PRODUCT : thm := BDerivative.POLY_DERIV_PRODUCT
unsafe def POLY_DERIV_POW : thm := BDerivative.POLY_DERIV_POW
unsafe def POLY_DERIV_VAR_POW : thm := BDerivative.POLY_DERIV_VAR_POW

-- Separable
unsafe def POLY_NONCONSTANT_IRREDUCIBLE_IMP_SEPARABLE : thm := BSeparable.POLY_NONCONSTANT_IRREDUCIBLE_IMP_SEPARABLE
unsafe def POLY_IRREDUCIBLE_IMP_SEPARABLE : thm := BSeparable.POLY_IRREDUCIBLE_IMP_SEPARABLE
unsafe def POLY_SQUARE_DIVIDES_DERIV : thm := BSeparable.POLY_SQUARE_DIVIDES_DERIV
unsafe def REPEATED_ROOT_POLY_DERIV_ZERO : thm := BSeparable.REPEATED_ROOT_POLY_DERIV_ZERO
unsafe def POLY_SEPARABLE_IMP_SQUAREFREE : thm := BSeparable.POLY_SEPARABLE_IMP_SQUAREFREE
unsafe def POLY_SQUARE_DIVIDES_DERIV_EQ : thm := BSeparable.POLY_SQUARE_DIVIDES_DERIV_EQ
unsafe def POLY_SQUAREFREE_IMP_SEPARABLE : thm := BSeparable.POLY_SQUAREFREE_IMP_SEPARABLE
unsafe def POLY_SEPARABLE_EQ_SQUAREFREE : thm := BSeparable.POLY_SEPARABLE_EQ_SQUAREFREE
unsafe def POLY_ROOT_COUNT_IMP_SQUAREFREE : thm := BSeparable.POLY_ROOT_COUNT_IMP_SQUAREFREE

-- GaussA
unsafe def POLY_PRIMITIVE_CONST_CANCEL : thm := BGaussA.POLY_PRIMITIVE_CONST_CANCEL
unsafe def MAKE_PRIMITIVE_IN_IDEAL : thm := BGaussA.MAKE_PRIMITIVE_IN_IDEAL
unsafe def POLY_MAKE_PRIMITIVE : thm := BGaussA.POLY_MAKE_PRIMITIVE
unsafe def RING_PRIME_POLY_RING_MONO : thm := BGaussA.RING_PRIME_POLY_RING_MONO

-- GaussB
unsafe def UFD_POLY_RING : thm := BGaussB.UFD_POLY_RING

-- GaussC
unsafe def POLY_CLEAR_DENOMINATORS : thm := BGaussC.POLY_CLEAR_DENOMINATORS

-- GaussD
unsafe def IRREDUCIBLE_PRIMITIVE_POLY_FRACTION_RING : thm := BGaussD.IRREDUCIBLE_PRIMITIVE_POLY_FRACTION_RING

-- Eisenstein
unsafe def EISENSTEIN_IRREDUCIBILITY_GEN : thm := BEisenstein.EISENSTEIN_IRREDUCIBILITY_GEN
unsafe def EISENSTEIN_IRREDUCIBILITY : thm := BEisenstein.EISENSTEIN_IRREDUCIBILITY
unsafe def EISENSTEIN_IRREDUCIBILITY_FRACTION_RING : thm := BEisenstein.EISENSTEIN_IRREDUCIBILITY_FRACTION_RING

-- RingOrder
unsafe def RING_ORDER_DIVIDES : thm := BRingOrder.RING_ORDER_DIVIDES
unsafe def RING_POW_EQ_1 : thm := BRingOrder.RING_POW_EQ_1
unsafe def RING_ORDER_EQ_0 : thm := BRingOrder.RING_ORDER_EQ_0
unsafe def RING_ORDER_EQ_1 : thm := BRingOrder.RING_ORDER_EQ_1
unsafe def RING_ORDER_UNIQUE : thm := BRingOrder.RING_ORDER_UNIQUE
unsafe def RING_POW_RING_ORDER : thm := BRingOrder.RING_POW_RING_ORDER
unsafe def RING_ORDER_1 : thm := BRingOrder.RING_ORDER_1
unsafe def RING_POW_GCD_EQ_1 : thm := BRingOrder.RING_POW_GCD_EQ_1
unsafe def RING_POW_COPRIME_EQ_1 : thm := BRingOrder.RING_POW_COPRIME_EQ_1
unsafe def RING_ORDER_MUL_DIVIDES_GEN : thm := BRingOrder.RING_ORDER_MUL_DIVIDES_GEN
unsafe def RING_ORDER_MUL_DIVIDES : thm := BRingOrder.RING_ORDER_MUL_DIVIDES
unsafe def RING_ORDER_MUL_DIVIDES_LCM : thm := BRingOrder.RING_ORDER_MUL_DIVIDES_LCM
unsafe def RING_POW_MOD_ORDER_GEN : thm := BRingOrder.RING_POW_MOD_ORDER_GEN
unsafe def RING_POW_MOD_ORDER : thm := BRingOrder.RING_POW_MOD_ORDER
unsafe def RING_ORDER_POW : thm := BRingOrder.RING_ORDER_POW
unsafe def RING_ORDER_POW_GEN : thm := BRingOrder.RING_ORDER_POW_GEN
unsafe def RING_ORDER_POW_DIVIDES : thm := BRingOrder.RING_ORDER_POW_DIVIDES
unsafe def RING_ORDER_UNIQUE_PRIME : thm := BRingOrder.RING_ORDER_UNIQUE_PRIME
unsafe def RING_ORDER_MUL : thm := BRingOrder.RING_ORDER_MUL

-- Frobenius
unsafe def RING_ENDOMORPHISM_FROBENIUS : thm := BFrobenius.RING_ENDOMORPHISM_FROBENIUS
unsafe def RING_MONOMORPHISM_FROBENIUS_GEN : thm := BFrobenius.RING_MONOMORPHISM_FROBENIUS_GEN
unsafe def RING_MONOMORPHISM_FROBENIUS : thm := BFrobenius.RING_MONOMORPHISM_FROBENIUS
unsafe def RING_AUTOMORPHISM_FROBENIUS : thm := BFrobenius.RING_AUTOMORPHISM_FROBENIUS
unsafe def FROBENIUS_FIXED : thm := BFrobenius.FROBENIUS_FIXED

-- IntegralDomainRule
unsafe def INTEGRAL_DOMAIN_RULE : term → IO (Except String thm) := fun t => (BIntegralDomainRule.INTEGRAL_DOMAIN_RULE t).run
unsafe def FIELD_TAC : HolCore.Tactics.tactic := fun g => BIntegralDomainRule.FIELD_TAC g
unsafe def FIELD_INV_EQ_0 : thm := BIntegralDomainRule.FIELD_INV_EQ_0
unsafe def FIELD_DIV_EQ_0 : thm := BIntegralDomainRule.FIELD_DIV_EQ_0

-- RingPullDiv
unsafe def RING_PULL_DIV : thm := BRingPullDiv.RING_PULL_DIV
unsafe def RING_PULL_DIV_CONV := BRingPullDiv.RING_PULL_DIV_CONV
unsafe def RING_PULL_DIV_TAC : HolCore.Tactics.tactic := fun g => BRingPullDiv.RING_PULL_DIV_TAC g











































































-- @@EXPORTS END

/-- `needs "Library/ringtheory.ml"`: build the bundle. -/
unsafe def ensureRingTheory : IO Unit := do
  -- @@ENSURE BEGIN
  let _ ← IO.mkRef BBasics.ring_tybij
  let _ ← IO.mkRef BNumbers.ring_of_num
  let _ ← IO.mkRef BSums.ring_sum
  let _ ← IO.mkRef BProducts.ring_product
  let _ ← IO.mkRef BDivides.ring_divides
  let _ ← IO.mkRef BSubrings.subring_of
  let _ ← IO.mkRef BIdeals.ring_ideal
  let _ ← IO.mkRef BDomains.integral_domain
  let _ ← IO.mkRef BRules.RING_CARRIER_RULE
  let _ ← IO.mkRef BHoms.ring_homomorphism
  let _ ← IO.mkRef BIso.isomorphic_ring
  let _ ← IO.mkRef BKernels.ring_kernel
  let _ ← IO.mkRef BProdRings.prod_ring
  let _ ← IO.mkRef BLimits.RING_DIRECT_LIMIT
  let _ ← IO.mkRef BRingRule.RING_RULE
  let _ ← IO.mkRef BCosets.ring_coset
  let _ ← IO.mkRef BQuotients.quotient_ring
  let _ ← IO.mkRef BPrimes.ring_prime
  let _ ← IO.mkRef BFactorizations.RING_DIVIDES_PRIMEFACTS_INJECTION
  let _ ← IO.mkRef BSquarefree.ring_squarefree
  let _ ← IO.mkRef BLocalization.ring_localequiv
  let _ ← IO.mkRef BSpecialIdeals.proper_ideal
  let _ ← IO.mkRef BRadical.radical
  let _ ← IO.mkRef BUFDs.UFD
  let _ ← IO.mkRef BEuclidean.euclidean_ring
  let _ ← IO.mkRef BNoetherian.NOETHERIAN_RING
  let _ ← IO.mkRef BACCP.RING_ACCP
  let _ ← IO.mkRef BRingGcd.ring_gcd
  let _ ← IO.mkRef BBezout.bezout_ring
  let _ ← IO.mkRef BGcdDomain.RING_GCD_LMUL
  let _ ← IO.mkRef BSquarefreeUFD.RING_SQUAREFREE_GCD
  let _ ← IO.mkRef BBooleanRings.boolean_ring
  let _ ← IO.mkRef BLocalRings.local_ring
  let _ ← IO.mkRef BVonNeumann.vnregular_ring
  let _ ← IO.mkRef BBoolRing.bool_ring
  let _ ← IO.mkRef BIntegerRing.integer_ring
  let _ ← IO.mkRef BIntegerModRing.integer_mod_ring
  let _ ← IO.mkRef BIntegerModConv.RING_INV_INTEGER_MOD_RING
  let _ ← IO.mkRef BRealRing.real_ring
  let _ ← IO.mkRef BMonomials.monomial_1
  let _ ← IO.mkRef BPowerSeries.ring_powerseries
  let _ ← IO.mkRef BPolyRings.powser_ring
  let _ ← IO.mkRef BHomExtend.poly_extend
  let _ ← IO.mkRef BNatIso.RING_ISOMORPHISM_POWSER_RING_TRIVIAL
  let _ ← IO.mkRef BRenaming.poly_reindex
  let _ ← IO.mkRef BMonomialOrders.POSET_MONOMIAL_DIVIDES
  let _ ← IO.mkRef BOneCoeff.EXISTS_FUN_FROM_1
  let _ ← IO.mkRef BDegree.poly_deg
  let _ ← IO.mkRef BCardinalities.CARD_EQ_MONOMIALS_FINITE
  let _ ← IO.mkRef BEvaluation.poly_evaluate
  let _ ← IO.mkRef BComposing.RING_POWERSERIES_COMPOSE
  let _ ← IO.mkRef BZerodivisors.INTEGRAL_DOMAIN_POWSER_RING
  let _ ← IO.mkRef BXMinusA.POLY_DEG_X_MINUS_A
  let _ ← IO.mkRef BDivision.POLY_TOP_NONZERO
  let _ ← IO.mkRef BHilbert.NOETHERIAN_POLY_RING_1
  let _ ← IO.mkRef BMonic.monic
  let _ ← IO.mkRef BReciprocal.poly_recip
  let _ ← IO.mkRef BDerivative.poly_deriv
  let _ ← IO.mkRef BSeparable.POLY_NONCONSTANT_IRREDUCIBLE_IMP_SEPARABLE
  let _ ← IO.mkRef BGaussA.POLY_PRIMITIVE_CONST_CANCEL
  let _ ← IO.mkRef BGaussB.UFD_POLY_RING
  let _ ← IO.mkRef BGaussC.POLY_CLEAR_DENOMINATORS
  let _ ← IO.mkRef BGaussD.IRREDUCIBLE_PRIMITIVE_POLY_FRACTION_RING
  let _ ← IO.mkRef BEisenstein.EISENSTEIN_IRREDUCIBILITY_GEN
  let _ ← IO.mkRef BRingOrder.RING_ORDER_DIVIDES
  let _ ← IO.mkRef BFrobenius.RING_ENDOMORPHISM_FROBENIUS
  let _ ← IO.mkRef BIntegralDomainRule.FIELD_INV_EQ_0
  let _ ← IO.mkRef BRingPullDiv.RING_PULL_DIV-- @@ENSURE END
  pure ()

end SessionLibrary.RingTheory
