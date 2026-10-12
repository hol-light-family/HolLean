/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/words.ml.                                   -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Words.lean

  The `unsafe` half of the words.ml translation: it holds words.ml's refs,
  supplies HolLibrary.Words' dependencies from Session, builds each bundle
  once, in file order, and exports every name.  `ensureWords` is `needs
  "Library/words.ml"`, which first does `needs "Library/bdd.ml"`.

  The blocks between `@@CORE` and `@@EXPORTS` markers are generated from
  HolLibrary/Words.lean by tools/wordsdiff/gen_session.py (bookkeeping
  only: field-by-field copies and accessors).
-/

import Session
import HolLibrary.Words
import SessionLibrary.BDD

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)
open Session

namespace SessionLibrary.Words

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨sessionB, sessionC, sessionT⟩

/- words.ml's refs (words.ml 65-69). -/
initialize word_sizes : IO.Ref (List thm) ← IO.mkRef []
initialize word_pow2sizes : IO.Ref (List thm) ← IO.mkRef []
initialize word_SIZE_CONV : IO.Ref ioconv ← IO.mkRef (fun t => pure (HolCore.Equal.NO_CONV t))
initialize word_POW2SIZE_CONV : IO.Ref ioconv ← IO.mkRef (fun t => pure (HolCore.Equal.NO_CONV t))

-- @@CORE BEGIN
/-- The core theorems words.ml uses, A-E. -/
unsafe def core1 (_ : Unit) : HolLibrary.Words.CoreThms1 where
  ADD := Session.«ADD»
  ADD1 := Session.«ADD1»
  ADD_AC := Session.«ADD_AC»
  ADD_ASSOC := Session.«ADD_ASSOC»
  ADD_CLAUSES := Session.«ADD_CLAUSES»
  ADD_EQ_0 := Session.«ADD_EQ_0»
  ADD_SUB := Session.«ADD_SUB»
  ADD_SUB2 := Session.«ADD_SUB2»
  ADD_SYM := Session.«ADD_SYM»
  AND_CLAUSES := Session.«AND_CLAUSES»
  AND_FORALL_THM := Session.«AND_FORALL_THM»
  ARITH := Session.«ARITH»
  ARITH_EQ := Session.«ARITH_EQ»
  ARITH_ODD := Session.«ARITH_ODD»
  ARITH_SUC := Session.«ARITH_SUC»
  ARITH_ZERO := Session.«ARITH_ZERO»
  BINARY_INDUCT := Session.«BINARY_INDUCT»
  BIT0 := Session.«BIT0»
  BIT1 := Session.«BIT1»
  CARD_CLAUSES := Session.«CARD_CLAUSES»
  CARD_EQ_0 := Session.«CARD_EQ_0»
  CARD_IMAGE_INJ := Session.«CARD_IMAGE_INJ»
  CARD_IMAGE_LE := Session.«CARD_IMAGE_LE»
  CARD_NUMSEG_LT := Session.«CARD_NUMSEG_LT»
  CARD_SING := Session.«CARD_SING»
  CARD_SUBSET := Session.«CARD_SUBSET»
  CARD_UNION := Session.«CARD_UNION»
  CARD_UNION_EQ := Session.«CARD_UNION_EQ»
  CARD_UNION_GEN := Session.«CARD_UNION_GEN»
  CARD_UNION_LE := Session.«CARD_UNION_LE»
  CART_EQ := Session.«CART_EQ»
  COND_CLAUSES := Session.«COND_CLAUSES»
  COND_ID := Session.«COND_ID»
  COND_RAND := Session.«COND_RAND»
  COND_SWAP := Session.«COND_SWAP»
  CONG := Session.«CONG»
  CONG_DIV2 := Session.«CONG_DIV2»
  CONG_LMOD := Session.«CONG_LMOD»
  CONG_NSUM := Session.«CONG_NSUM»
  CONG_RMOD := Session.«CONG_RMOD»
  CONJ_ASSOC := Session.«CONJ_ASSOC»
  CONJ_SYM := Session.«CONJ_SYM»
  CONTRAPOS_THM := Session.«CONTRAPOS_THM»
  DE_MORGAN_THM := Session.«DE_MORGAN_THM»
  DIMINDEX_1 := Session.«DIMINDEX_1»
  DIMINDEX_2 := Session.«DIMINDEX_2»
  DIMINDEX_3 := Session.«DIMINDEX_3»
  DIMINDEX_4 := Session.«DIMINDEX_4»
  DIMINDEX_FINITE_SUM := Session.«DIMINDEX_FINITE_SUM»
  DIMINDEX_GE_1 := Session.«DIMINDEX_GE_1»
  DIMINDEX_NONZERO := Session.«DIMINDEX_NONZERO»
  DIMINDEX_TYBIT0 := Session.«DIMINDEX_TYBIT0»
  DIMINDEX_UNIQUE := Session.«DIMINDEX_UNIQUE»
  DISJOINT_EMPTY := Session.«DISJOINT_EMPTY»
  DISJOINT_SYM := Session.«DISJOINT_SYM»
  DISJ_SYM := Session.«DISJ_SYM»
  DIVIDES_DIV_MULT := Session.«DIVIDES_DIV_MULT»
  DIVIDES_LE := Session.«DIVIDES_LE»
  DIVIDES_MOD := Session.«DIVIDES_MOD»
  DIVISION := Session.«DIVISION»
  DIVISION_SIMP := Session.«DIVISION_SIMP»
  DIVMOD_UNIQ := Session.«DIVMOD_UNIQ»
  DIV_0 := Session.«DIV_0»
  DIV_1 := Session.«DIV_1»
  DIV_ADD_EQ := Session.«DIV_ADD_EQ»
  DIV_DIV := Session.«DIV_DIV»
  DIV_EQ_0 := Session.«DIV_EQ_0»
  DIV_EXP := Session.«DIV_EXP»
  DIV_LE := Session.«DIV_LE»
  DIV_LT := Session.«DIV_LT»
  DIV_MOD := Session.«DIV_MOD»
  DIV_MULT := Session.«DIV_MULT»
  DIV_MULT2 := Session.«DIV_MULT2»
  DIV_MULT_ADD := Session.«DIV_MULT_ADD»
  DIV_UNIQ := Session.«DIV_UNIQ»
  DIV_ZERO := Session.«DIV_ZERO»
  EMPTY_GSPEC := Session.«EMPTY_GSPEC»
  EQ_ADD_LCANCEL := Session.«EQ_ADD_LCANCEL»
  EQ_ADD_RCANCEL := Session.«EQ_ADD_RCANCEL»
  EQ_IMP := Session.«EQ_IMP»
  EQ_SYM_EQ := Session.«EQ_SYM_EQ»
  EQ_TRANS := Session.«EQ_TRANS»
  EVEN := Session.«EVEN»
  EVEN_ADD := Session.«EVEN_ADD»
  EVEN_EXISTS := Session.«EVEN_EXISTS»
  EVEN_EXP := Session.«EVEN_EXP»
  EVEN_MOD := Session.«EVEN_MOD»
  EVEN_MULT := Session.«EVEN_MULT»
  EXISTS_BOOL_THM := Session.«EXISTS_BOOL_THM»
  EXISTS_OR_THM := Session.«EXISTS_OR_THM»
  EXP := Session.«EXP»
  EXP_1 := Session.«EXP_1»
  EXP_2_NE_0 := Session.«EXP_2_NE_0»
  EXP_ADD := Session.«EXP_ADD»
  EXP_EQ_0 := Session.«EXP_EQ_0»
  EXP_EXP := Session.«EXP_EXP»
  EXP_LT_0 := Session.«EXP_LT_0»
  EXP_MULT := Session.«EXP_MULT»
  EXP_ONE := Session.«EXP_ONE»
  EXP_ZERO := Session.«EXP_ZERO»
  EXTENSION := Session.«EXTENSION»
/-- The core theorems words.ml uses, F-I. -/
unsafe def core2 (_ : Unit) : HolLibrary.Words.CoreThms2 where
  FINITE_EMPTY := Session.«FINITE_EMPTY»
  FINITE_IMAGE := Session.«FINITE_IMAGE»
  FINITE_INSERT := Session.«FINITE_INSERT»
  FINITE_NUMSEG := Session.«FINITE_NUMSEG»
  FINITE_NUMSEG_LT := Session.«FINITE_NUMSEG_LT»
  FINITE_RESTRICT := Session.«FINITE_RESTRICT»
  FINITE_SING := Session.«FINITE_SING»
  FINITE_SUBSET := Session.«FINITE_SUBSET»
  FINITE_UNION := Session.«FINITE_UNION»
  FORALL_AND_THM := Session.«FORALL_AND_THM»
  FORALL_BOOL_THM := Session.«FORALL_BOOL_THM»
  FORALL_IN_GSPEC := Session.«FORALL_IN_GSPEC»
  FORALL_IN_IMAGE := Session.«FORALL_IN_IMAGE»
  FUN_EQ_THM := Session.«FUN_EQ_THM»
  GE := Session.«GE»
  GT := Session.«GT»
  HAS_SIZE := Session.«HAS_SIZE»
  IMP_CONJ := Session.«IMP_CONJ»
  IMP_CONJ_ALT := Session.«IMP_CONJ_ALT»
  INSERT_UNION_EQ := Session.«INSERT_UNION_EQ»
  INTER_COMM := Session.«INTER_COMM»
  INTER_SUBSET := Session.«INTER_SUBSET»
  INT_ABS_MUL := Session.«INT_ABS_MUL»
  INT_ABS_NUM := Session.«INT_ABS_NUM»
  INT_ABS_POS := Session.«INT_ABS_POS»
  INT_ABS_POW := Session.«INT_ABS_POW»
  INT_ADD_RID := Session.«INT_ADD_RID»
  INT_CONG_DIV2 := Session.«INT_CONG_DIV2»
  INT_CONG_IMP_EQ := Session.«INT_CONG_IMP_EQ»
  INT_DIVISION := Session.«INT_DIVISION»
  INT_DIV_1 := Session.«INT_DIV_1»
  INT_DIV_DIV := Session.«INT_DIV_DIV»
  INT_DIV_EQ_0 := Session.«INT_DIV_EQ_0»
  INT_DIV_LT_EQ := Session.«INT_DIV_LT_EQ»
  INT_DIV_MUL := Session.«INT_DIV_MUL»
  INT_DIV_MUL_ADD := Session.«INT_DIV_MUL_ADD»
  INT_DIV_REM := Session.«INT_DIV_REM»
  INT_DIV_ZERO := Session.«INT_DIV_ZERO»
  INT_EQ_MUL_LCANCEL := Session.«INT_EQ_MUL_LCANCEL»
  INT_EQ_SUB_RADD := Session.«INT_EQ_SUB_RADD»
  INT_FORALL_POS := Session.«INT_FORALL_POS»
  INT_GE := Session.«INT_GE»
  INT_GT := Session.«INT_GT»
  INT_LE_DIV_EQ := Session.«INT_LE_DIV_EQ»
  INT_LE_LMUL_EQ := Session.«INT_LE_LMUL_EQ»
  INT_LE_MUL2 := Session.«INT_LE_MUL2»
  INT_LE_POW2 := Session.«INT_LE_POW2»
  INT_LE_REFL := Session.«INT_LE_REFL»
  INT_LE_RMUL := Session.«INT_LE_RMUL»
  INT_LE_TRANS := Session.«INT_LE_TRANS»
  INT_LT_IMP_LE := Session.«INT_LT_IMP_LE»
  INT_LT_IMP_NE := Session.«INT_LT_IMP_NE»
  INT_LT_LMUL_EQ := Session.«INT_LT_LMUL_EQ»
  INT_LT_POW2 := Session.«INT_LT_POW2»
  INT_MAX := Session.«INT_MAX»
  INT_MIN := Session.«INT_MIN»
  INT_MUL_ASSOC := Session.«INT_MUL_ASSOC»
  INT_MUL_RID := Session.«INT_MUL_RID»
  INT_MUL_RNEG := Session.«INT_MUL_RNEG»
  INT_MUL_RZERO := Session.«INT_MUL_RZERO»
  INT_MUL_SYM := Session.«INT_MUL_SYM»
  INT_NEG_LT0 := Session.«INT_NEG_LT0»
  INT_NOT_LE := Session.«INT_NOT_LE»
  INT_NOT_LT := Session.«INT_NOT_LT»
  INT_OF_NUM_ADD := Session.«INT_OF_NUM_ADD»
  INT_OF_NUM_CLAUSES := Session.«INT_OF_NUM_CLAUSES»
  INT_OF_NUM_DIV := Session.«INT_OF_NUM_DIV»
  INT_OF_NUM_EQ := Session.«INT_OF_NUM_EQ»
  INT_OF_NUM_LE := Session.«INT_OF_NUM_LE»
  INT_OF_NUM_LT := Session.«INT_OF_NUM_LT»
  INT_OF_NUM_MUL := Session.«INT_OF_NUM_MUL»
  INT_OF_NUM_OF_INT := Session.«INT_OF_NUM_OF_INT»
  INT_OF_NUM_POW := Session.«INT_OF_NUM_POW»
  INT_OF_NUM_REM := Session.«INT_OF_NUM_REM»
  INT_OF_NUM_SUB := Session.«INT_OF_NUM_SUB»
  INT_POS := Session.«INT_POS»
  INT_POW := Session.«INT_POW»
  INT_POW_ADD := Session.«INT_POW_ADD»
  INT_POW_EQ_0 := Session.«INT_POW_EQ_0»
  INT_POW_LE := Session.«INT_POW_LE»
  INT_POW_MONO := Session.«INT_POW_MONO»
  INT_REM_EQ := Session.«INT_REM_EQ»
  INT_REM_EQ_0 := Session.«INT_REM_EQ_0»
  INT_REM_MOD_SELF := Session.«INT_REM_MOD_SELF»
  INT_REM_REM := Session.«INT_REM_REM»
  INT_REM_REM_POW_MIN := Session.«INT_REM_REM_POW_MIN»
  INT_REM_UNIQUE := Session.«INT_REM_UNIQUE»
  INT_SUB_0 := Session.«INT_SUB_0»
  INT_SUB_LZERO := Session.«INT_SUB_LZERO»
  IN_ELIM_PAIR_THM := Session.«IN_ELIM_PAIR_THM»
  IN_ELIM_THM := Session.«IN_ELIM_THM»
  IN_IMAGE := Session.«IN_IMAGE»
  IN_INSERT := Session.«IN_INSERT»
  IN_INTER := Session.«IN_INTER»
  IN_NUMSEG := Session.«IN_NUMSEG»
  IN_SING := Session.«IN_SING»
  IN_UNION := Session.«IN_UNION»
  IN_UNIV := Session.«IN_UNIV»
/-- The core theorems words.ml uses, J-Q. -/
unsafe def core3 (_ : Unit) : HolLibrary.Words.CoreThms3 where
  LAMBDA_BETA := Session.«LAMBDA_BETA»
  LDIV_LT_EQ := Session.«LDIV_LT_EQ»
  LE := Session.«LE»
  LEFT_ADD_DISTRIB := Session.«LEFT_ADD_DISTRIB»
  LEFT_IMP_EXISTS_THM := Session.«LEFT_IMP_EXISTS_THM»
  LEFT_SUB_DISTRIB := Session.«LEFT_SUB_DISTRIB»
  LET_ADD2 := Session.«LET_ADD2»
  LET_TRANS := Session.«LET_TRANS»
  LE_0 := Session.«LE_0»
  LE_1 := Session.«LE_1»
  LE_ADD := Session.«LE_ADD»
  LE_ADD2 := Session.«LE_ADD2»
  LE_ADD_LCANCEL := Session.«LE_ADD_LCANCEL»
  LE_ANTISYM := Session.«LE_ANTISYM»
  LE_CASES := Session.«LE_CASES»
  LE_EXISTS := Session.«LE_EXISTS»
  LE_EXP := Session.«LE_EXP»
  LE_LT := Session.«LE_LT»
  LE_MINIMAL := Session.«LE_MINIMAL»
  LE_MULT_LCANCEL := Session.«LE_MULT_LCANCEL»
  LE_MULT_RCANCEL := Session.«LE_MULT_RCANCEL»
  LE_REFL := Session.«LE_REFL»
  LE_SUC_LT := Session.«LE_SUC_LT»
  LE_TRANS := Session.«LE_TRANS»
  LT := Session.«LT»
  LTE_TRANS := Session.«LTE_TRANS»
  LT_ADD2 := Session.«LT_ADD2»
  LT_ADD_LCANCEL := Session.«LT_ADD_LCANCEL»
  LT_EXISTS := Session.«LT_EXISTS»
  LT_EXP := Session.«LT_EXP»
  LT_IMP_LE := Session.«LT_IMP_LE»
  LT_LE := Session.«LT_LE»
  LT_MULT2 := Session.«LT_MULT2»
  LT_MULT_LCANCEL := Session.«LT_MULT_LCANCEL»
  LT_POW2_REFL := Session.«LT_POW2_REFL»
  LT_REFL := Session.«LT_REFL»
  LT_TRANS := Session.«LT_TRANS»
  MAX := Session.«MAX»
  MIN := Session.«MIN»
  MINIMAL := Session.«MINIMAL»
  MINIMAL_LE := Session.«MINIMAL_LE»
  MINIMAL_UBOUND := Session.«MINIMAL_UBOUND»
  MINIMAL_UNIQUE := Session.«MINIMAL_UNIQUE»
  MOD_0 := Session.«MOD_0»
  MOD_1 := Session.«MOD_1»
  MOD_2_CASES := Session.«MOD_2_CASES»
  MOD_ADD_CASES := Session.«MOD_ADD_CASES»
  MOD_ADD_MOD := Session.«MOD_ADD_MOD»
  MOD_CASES := Session.«MOD_CASES»
  MOD_EQ_0 := Session.«MOD_EQ_0»
  MOD_EQ_SELF := Session.«MOD_EQ_SELF»
  MOD_LE := Session.«MOD_LE»
  MOD_LT := Session.«MOD_LT»
  MOD_LT_EQ := Session.«MOD_LT_EQ»
  MOD_LT_EQ_LT := Session.«MOD_LT_EQ_LT»
  MOD_MOD := Session.«MOD_MOD»
  MOD_MOD_EXP_MIN := Session.«MOD_MOD_EXP_MIN»
  MOD_MOD_REFL := Session.«MOD_MOD_REFL»
  MOD_MULT := Session.«MOD_MULT»
  MOD_MULT2 := Session.«MOD_MULT2»
  MOD_MULT_ADD := Session.«MOD_MULT_ADD»
  MOD_MULT_MOD := Session.«MOD_MULT_MOD»
  MOD_NSUM_MOD_NUMSEG := Session.«MOD_NSUM_MOD_NUMSEG»
  MOD_REFL := Session.«MOD_REFL»
  MOD_UNIQ := Session.«MOD_UNIQ»
  MOD_ZERO := Session.«MOD_ZERO»
  MONO_EXISTS := Session.«MONO_EXISTS»
  MONO_FORALL := Session.«MONO_FORALL»
  MULT_2 := Session.«MULT_2»
  MULT_AC := Session.«MULT_AC»
  MULT_ASSOC := Session.«MULT_ASSOC»
  MULT_CLAUSES := Session.«MULT_CLAUSES»
  MULT_EQ_0 := Session.«MULT_EQ_0»
  MULT_SYM := Session.«MULT_SYM»
  NOT_EVEN := Session.«NOT_EVEN»
  NOT_FORALL_THM := Session.«NOT_FORALL_THM»
  NOT_IMP := Session.«NOT_IMP»
  NOT_IN_EMPTY := Session.«NOT_IN_EMPTY»
  NOT_LE := Session.«NOT_LE»
  NOT_LT := Session.«NOT_LT»
  NOT_ODD := Session.«NOT_ODD»
  NOT_SUC := Session.«NOT_SUC»
  NSUM_ADD := Session.«NSUM_ADD»
  NSUM_ADD_NUMSEG := Session.«NSUM_ADD_NUMSEG»
  NSUM_CLAUSES := Session.«NSUM_CLAUSES»
  NSUM_CLAUSES_LEFT := Session.«NSUM_CLAUSES_LEFT»
  NSUM_CLAUSES_NUMSEG := Session.«NSUM_CLAUSES_NUMSEG»
  NSUM_CLAUSES_NUMSEG_LT := Session.«NSUM_CLAUSES_NUMSEG_LT»
  NSUM_CLOSED := Session.«NSUM_CLOSED»
  NSUM_CONST := Session.«NSUM_CONST»
  NSUM_DELTA := Session.«NSUM_DELTA»
  NSUM_EQ := Session.«NSUM_EQ»
  NSUM_EQ_0_IFF := Session.«NSUM_EQ_0_IFF»
  NSUM_EQ_GENERAL_INVERSES := Session.«NSUM_EQ_GENERAL_INVERSES»
  NSUM_GROUP := Session.«NSUM_GROUP»
  NSUM_IMAGE := Session.«NSUM_IMAGE»
  NSUM_LE := Session.«NSUM_LE»
  NSUM_LMUL := Session.«NSUM_LMUL»
  NSUM_NSUM_PRODUCT := Session.«NSUM_NSUM_PRODUCT»
  NSUM_OFFSET := Session.«NSUM_OFFSET»
  NSUM_REFLECT := Session.«NSUM_REFLECT»
  NSUM_RESTRICT_SET := Session.«NSUM_RESTRICT_SET»
  NSUM_RMUL := Session.«NSUM_RMUL»
  NSUM_SING := Session.«NSUM_SING»
  NSUM_SUPERSET := Session.«NSUM_SUPERSET»
  NSUM_UNION := Session.«NSUM_UNION»
  NSUM_UNION_EQ := Session.«NSUM_UNION_EQ»
  NUMERAL := Session.«NUMERAL»
  NUMSEG_CLAUSES_LT := Session.«NUMSEG_CLAUSES_LT»
  NUMSEG_LT := Session.«NUMSEG_LT»
  NUMSEG_LT_DIMINDEX := Session.«NUMSEG_LT_DIMINDEX»
  NUM_OF_INT_OF_NUM := Session.«NUM_OF_INT_OF_NUM»
  ODD := Session.«ODD»
  ODD_ADD := Session.«ODD_ADD»
  ODD_EXP := Session.«ODD_EXP»
  ODD_MOD := Session.«ODD_MOD»
  ODD_MOD_EVEN := Session.«ODD_MOD_EVEN»
  ODD_MULT := Session.«ODD_MULT»
  ODD_SUB := Session.«ODD_SUB»
  OR_CLAUSES := Session.«OR_CLAUSES»
  PAIR_EQ := Session.«PAIR_EQ»
/-- The core theorems words.ml uses, R-Z and lower case. -/
unsafe def core4 (_ : Unit) : HolLibrary.Words.CoreThms4 where
  RDIV_LT_EQ := Session.«RDIV_LT_EQ»
  REAL_OF_INT_CLAUSES := Session.«REAL_OF_INT_CLAUSES»
  REAL_OF_NUM_ADD := Session.«REAL_OF_NUM_ADD»
  REAL_OF_NUM_CLAUSES := Session.«REAL_OF_NUM_CLAUSES»
  REAL_OF_NUM_EQ := Session.«REAL_OF_NUM_EQ»
  REAL_OF_NUM_LE := Session.«REAL_OF_NUM_LE»
  REAL_OF_NUM_POW := Session.«REAL_OF_NUM_POW»
  REAL_OF_NUM_SUB := Session.«REAL_OF_NUM_SUB»
  REAL_OF_NUM_SUM := Session.«REAL_OF_NUM_SUM»
  REAL_OF_NUM_SUM_NUMSEG := Session.«REAL_OF_NUM_SUM_NUMSEG»
  REAL_SUB_0 := Session.«REAL_SUB_0»
  REAL_SUB_LE := Session.«REAL_SUB_LE»
  REAL_SUB_RZERO := Session.«REAL_SUB_RZERO»
  RIGHT_ADD_DISTRIB := Session.«RIGHT_ADD_DISTRIB»
  RIGHT_OR_DISTRIB := Session.«RIGHT_OR_DISTRIB»
  SING_GSPEC := Session.«SING_GSPEC»
  SUBSET := Session.«SUBSET»
  SUBSET_INTER_ABSORPTION := Session.«SUBSET_INTER_ABSORPTION»
  SUB_0 := Session.«SUB_0»
  SUB_ADD := Session.«SUB_ADD»
  SUB_EQ_0 := Session.«SUB_EQ_0»
  SUB_REFL := Session.«SUB_REFL»
  SUC_INJ := Session.«SUC_INJ»
  SUC_SUB1 := Session.«SUC_SUB1»
  SUM_ADD := Session.«SUM_ADD»
  SUM_ADD_NUMSEG := Session.«SUM_ADD_NUMSEG»
  SUM_DIFFS_ALT := Session.«SUM_DIFFS_ALT»
  SUM_EQ_0_NUMSEG := Session.«SUM_EQ_0_NUMSEG»
  SUM_LMUL := Session.«SUM_LMUL»
  SUM_NEG := Session.«SUM_NEG»
  SUM_RMUL := Session.«SUM_RMUL»
  SUM_SUB := Session.«SUM_SUB»
  SUM_SUB_NUMSEG := Session.«SUM_SUB_NUMSEG»
  UNION_EMPTY := Session.«UNION_EMPTY»
  UNWIND_THM2 := Session.«UNWIND_THM2»
  bool_INDUCT := Session.«bool_INDUCT»
  divides := Session.«divides»
  int_divides := Session.«int_divides»
  int_of_num := Session.«int_of_num»
  num_CASES := Session.«num_CASES»
  num_INDUCTION := Session.«num_INDUCTION»
  num_congruent := Session.«num_congruent»
  num_divides := Session.«num_divides»
  numseg := Session.«numseg»
  o_DEF := Session.«o_DEF»-- @@CORE END

/-- What words.ml uses from Session. -/
unsafe def deps (_ : Unit) : HolLibrary.Words.WordsDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  new_type_definition ty names th :=
    ExceptT.mk (Session.new_type_definition ty names.1 names.2 th)
  new_type_abbrev := Session.new_type_abbrev
  define s := do ExceptT.mk (Session.define (← HolLight.q s))
  word_sizes := word_sizes
  word_pow2sizes := word_pow2sizes
  word_SIZE_CONV := word_SIZE_CONV
  word_POW2SIZE_CONV := word_POW2SIZE_CONV
  ARITH_RULE t := ExceptT.mk (ARITH_RULE t)
  ARITH_TAC := ARITH_TAC
  ASM_ARITH_TAC := ASM_ARITH_TAC
  ASM_INT_ARITH_TAC := ASM_INT_ARITH_TAC
  ASM_MESON_TAC := ASM_MESON_TAC
  HAS_SIZE_DIMINDEX_RULE ty := ExceptT.mk (HAS_SIZE_DIMINDEX_RULE ty)
  INDUCT_TAC := INDUCT_TAC
  INTEGER_RULE t := ExceptT.mk (INTEGER_RULE t)
  INT_ARITH t := ExceptT.mk (INT_ARITH t)
  INT_ARITH_TAC := INT_ARITH_TAC
  INT_RING t := ExceptT.mk (INT_RING t)
  MESON ths t := ExceptT.mk (MESON ths t)
  MESON_TAC := MESON_TAC
  NUMBER_RULE t := ExceptT.mk (NUMBER_RULE t)
  REAL_ARITH t := ExceptT.mk (REAL_ARITH3 t)
  REAL_ARITH_TAC := REAL_ARITH_TAC2
  SET_RULE t := ExceptT.mk (SET_RULE t)
  SET_TAC := SET_TAC
  mk_small_numeral := mk_small_numeral
  mk_intconst := Session.mk_intconst
  BITS_ELIM_CONV t := do
    match ← Session.BITS_ELIM_CONV with
    | .ok c => pure (c t)
    | .error e => pure (.error e)
  DIMINDEX_CONV t := pure (Session.DIMINDEX_CONV t)
  EXPAND_CASES_CONV := EXPAND_CASES_CONV
  EXPAND_NSUM_CONV := EXPAND_NSUM_CONV
  INT_ABS_CONV := INT_ABS_CONV
  INT_DIV_CONV := INT_DIV_CONV
  INT_GE_CONV := INT_GE_CONV
  INT_GT_CONV := INT_GT_CONV
  INT_LE_CONV := INT_LE_CONV
  INT_LT_CONV := INT_LT_CONV
  INT_MUL_CONV := INT_MUL_CONV
  INT_POLY_CONV := INT_POLY_CONV
  INT_POW_CONV := INT_POW_CONV
  INT_REDUCE_CONV := INT_REDUCE_CONV
  INT_RED_CONV := INT_RED_CONV
  INT_REM_CONV := INT_REM_CONV
  INT_REM_DOWN_CONV := INT_REM_DOWN_CONV
  INT_SGN_CONV := INT_SGN_CONV
  INT_SUB_CONV := INT_SUB_CONV
  MOD_DOWN_CONV := MOD_DOWN_CONV
  NUM_ADD_CONV := NUM_ADD_CONV
  NUM_DIV_CONV := NUM_DIV_CONV
  NUM_EQ_CONV := NUM_EQ_CONV
  NUM_EVEN_CONV := NUM_EVEN_CONV
  NUM_EXP_CONV := NUM_EXP_CONV
  NUM_GE_CONV := NUM_GE_CONV
  NUM_GT_CONV := NUM_GT_CONV
  NUM_LE_CONV := NUM_LE_CONV
  NUM_LT_CONV := NUM_LT_CONV
  NUM_MAX_CONV := NUM_MAX_CONV
  NUM_MIN_CONV := NUM_MIN_CONV
  NUM_MOD_CONV := NUM_MOD_CONV
  NUM_MULT_CONV := NUM_MULT_CONV
  NUM_ODD_CONV := NUM_ODD_CONV
  NUM_REDUCE_CONV := NUM_REDUCE_CONV
  NUM_RED_CONV := NUM_RED_CONV
  NUM_SUB_CONV := NUM_SUB_CONV
  NUM_SUC_CONV := NUM_SUC_CONV
  num_CONV := Session.num_CONV
  prove_general_recursive_function_exists := Session.prove_general_recursive_function_exists
  bool_compset := Session.bool_compset
  set_skip := Session.set_skip
  add_conv := Session.add_conv
  WEAK_CBV_CONV := Session.WEAK_CBV_CONV
  let_CONV := Session.let_CONV
  BDD_DEFTAUT := SessionLibrary.BDD.BDD_DEFTAUT
  REAL_POLY_CONV := REAL_POLY_CONV
  core1 := core1 ()
  core2 := core2 ()
  core3 := core3 ()
  core4 := core4 ()

/-- words.ml's `needs "Library/bdd.ml"` (words.ml 39), once, before the
    first bundle. -/
initialize theWordsPrelude : IO.Ref Bool ← IO.mkRef false

unsafe def ensureWordsPrelude : IO Unit := do
  unless (← theWordsPrelude.get) do
    theWordsPrelude.set true
    SessionLibrary.BDD.ensureBDD

/-- Build a bundle once, after the prelude.  `setup` is a thunk, so that
    `deps` is not built before the prelude has run. -/
private unsafe def cached {α : Type} [Inhabited α] (r : IO.Ref (Option α)) (name : String)
    (setup : Unit → IO (Except String α)) : α :=
  match unsafeIO (do
    match ← r.get with
    | some d => pure d
    | none => do
      ensureWordsPrelude
      match ← setup () with
      | .ok d => do r.set (some d); pure d
      | .error e => panic! s!"{name} failed: {e}") with
  | .ok d => d | _ => panic! s!"SessionLibrary.Words: {name}"

/- The bundles, in words.ml order.  Each forces the one before it, so that
   any bundle builds every earlier one first, as HOL Light's load does. -/

-- @@BUNDLES BEGIN
initialize theWordSizes : IO.Ref (Option HolLibrary.Words.WordSizes) ← IO.mkRef none
unsafe def BWordSizes : HolLibrary.Words.WordSizes :=
  cached theWordSizes "setupWordSizes" fun _ => do
    (HolLibrary.Words.setupWordSizes (deps ())).run

initialize theDigitsum : IO.Ref (Option HolLibrary.Words.Digitsum) ← IO.mkRef none
unsafe def BDigitsum : HolLibrary.Words.Digitsum :=
  cached theDigitsum "setupDigitsum" fun _ => do
    let _ ← IO.mkRef BWordSizes.HAS_SIZE_8
    (HolLibrary.Words.setupDigitsum (deps ())).run

initialize theBitval : IO.Ref (Option HolLibrary.Words.Bitval) ← IO.mkRef none
unsafe def BBitval : HolLibrary.Words.Bitval :=
  cached theBitval "setupBitval" fun _ => do
    let _ ← IO.mkRef BDigitsum.DIGITSUM_WORKS_GEN
    (HolLibrary.Words.setupBitval (deps ())).run

initialize theBinary : IO.Ref (Option HolLibrary.Words.Binary) ← IO.mkRef none
unsafe def BBinary : HolLibrary.Words.Binary :=
  cached theBinary "setupBinary" fun _ => do
    let _ ← IO.mkRef BBitval.bitval
    (HolLibrary.Words.setupBinary (deps ()) BDigitsum BBitval).run

initialize theWordType : IO.Ref (Option HolLibrary.Words.WordType) ← IO.mkRef none
unsafe def BWordType : HolLibrary.Words.WordType :=
  cached theWordType "setupWordType" fun _ => do
    let _ ← IO.mkRef BBinary.ODD_MOD_POW2
    (HolLibrary.Words.setupWordType (deps ())).run

initialize theBitsOfWord : IO.Ref (Option HolLibrary.Words.BitsOfWord) ← IO.mkRef none
unsafe def BBitsOfWord : HolLibrary.Words.BitsOfWord :=
  cached theBitsOfWord "setupBitsOfWord" fun _ => do
    let _ ← IO.mkRef BWordType.word_tybij
    (HolLibrary.Words.setupBitsOfWord (deps ()) BWordType).run

initialize theVal : IO.Ref (Option HolLibrary.Words.Val) ← IO.mkRef none
unsafe def BVal : HolLibrary.Words.Val :=
  cached theVal "setupVal" fun _ => do
    let _ ← IO.mkRef BBitsOfWord.bits_of_word
    (HolLibrary.Words.setupVal (deps ()) BBinary BBitval BWordType BBitsOfWord).run

initialize theIval : IO.Ref (Option HolLibrary.Words.Ival) ← IO.mkRef none
unsafe def BIval : HolLibrary.Words.Ival :=
  cached theIval "setupIval" fun _ => do
    let _ ← IO.mkRef BVal.val_def
    (HolLibrary.Words.setupIval (deps ()) BBitval BVal).run

initialize theNumBits : IO.Ref (Option HolLibrary.Words.NumBits) ← IO.mkRef none
unsafe def BNumBits : HolLibrary.Words.NumBits :=
  cached theNumBits "setupNumBits" fun _ => do
    let _ ← IO.mkRef BIval.ival
    (HolLibrary.Words.setupNumBits (deps ()) BDigitsum BBitsOfWord BVal).run

initialize theNumShiftAdd : IO.Ref (Option HolLibrary.Words.NumShiftAdd) ← IO.mkRef none
unsafe def BNumShiftAdd : HolLibrary.Words.NumShiftAdd :=
  cached theNumShiftAdd "setupNumShiftAdd" fun _ => do
    let _ ← IO.mkRef BNumBits.numbit
    (HolLibrary.Words.setupNumShiftAdd (deps ()) BNumBits).run

initialize theLimits : IO.Ref (Option HolLibrary.Words.Limits) ← IO.mkRef none
unsafe def BLimits : HolLibrary.Words.Limits :=
  cached theLimits "setupLimits" fun _ => do
    let _ ← IO.mkRef BNumShiftAdd.num_shift_add
    (HolLibrary.Words.setupLimits (deps ()) BBitval BVal BIval).run

initialize thePopcount : IO.Ref (Option HolLibrary.Words.Popcount) ← IO.mkRef none
unsafe def BPopcount : HolLibrary.Words.Popcount :=
  cached thePopcount "setupPopcount" fun _ => do
    let _ ← IO.mkRef BLimits.word_UINT_MAX
    (HolLibrary.Words.setupPopcount (deps ()) BBitval BWordType BBitsOfWord BVal).run

initialize theGeneralOps : IO.Ref (Option HolLibrary.Words.GeneralOps) ← IO.mkRef none
unsafe def BGeneralOps : HolLibrary.Words.GeneralOps :=
  cached theGeneralOps "setupGeneralOps" fun _ => do
    let _ ← IO.mkRef BPopcount.word_popcount
    (HolLibrary.Words.setupGeneralOps (deps ()) BWordType BVal BIval).run

initialize theWordOps1 : IO.Ref (Option HolLibrary.Words.WordOps1) ← IO.mkRef none
unsafe def BWordOps1 : HolLibrary.Words.WordOps1 :=
  cached theWordOps1 "setupWordOps1" fun _ => do
    let _ ← IO.mkRef BGeneralOps.modular
    (HolLibrary.Words.setupWordOps1 (deps ()) BBitval BWordType BBitsOfWord BVal BIval BPopcount BGeneralOps).run

initialize theWordOps2 : IO.Ref (Option HolLibrary.Words.WordOps2) ← IO.mkRef none
unsafe def BWordOps2 : HolLibrary.Words.WordOps2 :=
  cached theWordOps2 "setupWordOps2" fun _ => do
    let _ ← IO.mkRef BWordOps1.word_not
    (HolLibrary.Words.setupWordOps2 (deps ()) BBitval BBinary BWordType BBitsOfWord BVal BIval BGeneralOps BWordOps1).run

initialize theWordOps3 : IO.Ref (Option HolLibrary.Words.WordOps3) ← IO.mkRef none
unsafe def BWordOps3 : HolLibrary.Words.WordOps3 :=
  cached theWordOps3 "setupWordOps3" fun _ => do
    let _ ← IO.mkRef BWordOps2.WORD_NOT_AS_SUB
    (HolLibrary.Words.setupWordOps3 (deps ()) BWordType BBitsOfWord BVal BIval BPopcount BGeneralOps BWordOps1 BWordOps2).run

initialize theWordRule : IO.Ref (Option HolLibrary.Words.WordRule) ← IO.mkRef none
unsafe def BWordRule : HolLibrary.Words.WordRule :=
  cached theWordRule "setupWordRule" fun _ => do
    let _ ← IO.mkRef BWordOps3.WORD_SHL_WORD
    (HolLibrary.Words.setupWordRule (deps ()) BBitval BVal BIval BWordOps1 BWordOps2).run

initialize theWordBitwise : IO.Ref (Option HolLibrary.Words.WordBitwise) ← IO.mkRef none
unsafe def BWordBitwise : HolLibrary.Words.WordBitwise :=
  cached theWordBitwise "setupWordBitwise" fun _ => do
    let _ ← IO.mkRef BWordRule.WORD_VAL_CONG_CONV
    (HolLibrary.Words.setupWordBitwise (deps ()) BWordType BBitsOfWord BVal BWordOps1).run

initialize theWordArith : IO.Ref (Option HolLibrary.Words.WordArith) ← IO.mkRef none
unsafe def BWordArith : HolLibrary.Words.WordArith :=
  cached theWordArith "setupWordArith" fun _ => do
    let _ ← IO.mkRef BWordBitwise.WORD_BITWISE_RULE
    (HolLibrary.Words.setupWordArith (deps ()) BVal BIval BLimits BGeneralOps BWordOps1 BWordOps2 BWordOps3 BWordRule).run

initialize theValExpand : IO.Ref (Option HolLibrary.Words.ValExpand) ← IO.mkRef none
unsafe def BValExpand : HolLibrary.Words.ValExpand :=
  cached theValExpand "setupValExpand" fun _ => do
    let _ ← IO.mkRef BWordArith.WORD_ARITH
    (HolLibrary.Words.setupValExpand (deps ()) BVal).run

initialize theZxSx : IO.Ref (Option HolLibrary.Words.ZxSx) ← IO.mkRef none
unsafe def BZxSx : HolLibrary.Words.ZxSx :=
  cached theZxSx "setupZxSx" fun _ => do
    let _ ← IO.mkRef BValExpand.EMPOWER_CONV
    (HolLibrary.Words.setupZxSx (deps ()) BBitval BBinary BWordType BVal BIval BWordOps1 BWordOps2 BWordOps3 BWordRule).run

initialize theJoinSubword : IO.Ref (Option HolLibrary.Words.JoinSubword) ← IO.mkRef none
unsafe def BJoinSubword : HolLibrary.Words.JoinSubword :=
  cached theJoinSubword "setupJoinSubword" fun _ => do
    let _ ← IO.mkRef BZxSx.word_zx
    (HolLibrary.Words.setupJoinSubword (deps ()) BDigitsum BBinary BWordType BVal BIval BWordOps1 BWordOps2 BWordOps3 BZxSx).run

initialize theInsertDup : IO.Ref (Option HolLibrary.Words.InsertDup) ← IO.mkRef none
unsafe def BInsertDup : HolLibrary.Words.InsertDup :=
  cached theInsertDup "setupInsertDup" fun _ => do
    let _ ← IO.mkRef BJoinSubword.word_join
    (HolLibrary.Words.setupInsertDup (deps ()) BBinary BWordType BBitsOfWord BVal BZxSx BJoinSubword).run

initialize theBitRec : IO.Ref (Option HolLibrary.Words.BitRec) ← IO.mkRef none
unsafe def BBitRec : HolLibrary.Words.BitRec :=
  cached theBitRec "setupBitRec" fun _ => do
    let _ ← IO.mkRef BInsertDup.word_insert
    (HolLibrary.Words.setupBitRec (deps ()) BBitval BWordType BVal BWordOps1 BWordRule).run

initialize theMisc1 : IO.Ref (Option HolLibrary.Words.Misc1) ← IO.mkRef none
unsafe def BMisc1 : HolLibrary.Words.Misc1 :=
  cached theMisc1 "setupMisc1" fun _ => do
    let _ ← IO.mkRef BBitRec.BIT_WORD_ADD
    (HolLibrary.Words.setupMisc1 (deps ()) BBitval BWordType BBitsOfWord BVal BIval BLimits BPopcount BWordOps1 BWordOps2 BWordOps3 BWordRule BWordBitwise BZxSx BJoinSubword BBitRec).run

initialize theMasks : IO.Ref (Option HolLibrary.Words.Masks) ← IO.mkRef none
unsafe def BMasks : HolLibrary.Words.Masks :=
  cached theMasks "setupMasks" fun _ => do
    let _ ← IO.mkRef BMisc1.WORD_ADD_0
    (HolLibrary.Words.setupMasks (deps ()) BBitval BBinary BWordType BBitsOfWord BVal BIval BWordOps1 BWordOps2 BWordOps3 BWordRule BWordBitwise BZxSx BMisc1).run

initialize theClzCtz : IO.Ref (Option HolLibrary.Words.ClzCtz) ← IO.mkRef none
unsafe def BClzCtz : HolLibrary.Words.ClzCtz :=
  cached theClzCtz "setupClzCtz" fun _ => do
    let _ ← IO.mkRef BMasks.WORD_MASK_ALT
    (HolLibrary.Words.setupClzCtz (deps ()) BBitval BWordType BBitsOfWord BVal BPopcount BWordOps1 BWordOps3 BWordRule BMisc1 BMasks).run

initialize theReverse : IO.Ref (Option HolLibrary.Words.Reverse) ← IO.mkRef none
unsafe def BReverse : HolLibrary.Words.Reverse :=
  cached theReverse "setupReverse" fun _ => do
    let _ ← IO.mkRef BClzCtz.word_ctz
    (HolLibrary.Words.setupReverse (deps ()) BBitval BWordType BBitsOfWord BVal BWordOps1 BWordOps2 BWordOps3 BZxSx BClzCtz).run

initialize theAlign : IO.Ref (Option HolLibrary.Words.Align) ← IO.mkRef none
unsafe def BAlign : HolLibrary.Words.Align :=
  cached theAlign "setupAlign" fun _ => do
    let _ ← IO.mkRef BReverse.word_reversefields
    (HolLibrary.Words.setupAlign (deps ()) BVal BIval BWordOps1 BWordOps2 BWordOps3 BWordRule BWordBitwise BMisc1).run

initialize theTopflip : IO.Ref (Option HolLibrary.Words.Topflip) ← IO.mkRef none
unsafe def BTopflip : HolLibrary.Words.Topflip :=
  cached theTopflip "setupTopflip" fun _ => do
    let _ ← IO.mkRef BAlign.aligned
    (HolLibrary.Words.setupTopflip (deps ()) BVal BIval BLimits BGeneralOps BWordOps1 BWordOps3 BWordBitwise BWordArith BMisc1 BAlign).run

initialize theBitWordConv : IO.Ref (Option HolLibrary.Words.BitWordConv) ← IO.mkRef none
unsafe def BBitWordConv : HolLibrary.Words.BitWordConv :=
  cached theBitWordConv "setupBitWordConv" fun _ => do
    let _ ← IO.mkRef BTopflip.WORD_WORD_OPERATION_CONV
    (HolLibrary.Words.setupBitWordConv (deps ()) BWordType BVal BWordOps1 BWordOps2 BWordOps3 BZxSx BJoinSubword BInsertDup BBitRec BMasks BReverse).run

initialize theBlast : IO.Ref (Option HolLibrary.Words.Blast) ← IO.mkRef none
unsafe def BBlast : HolLibrary.Words.Blast :=
  cached theBlast "setupBlast" fun _ => do
    let _ ← IO.mkRef BBitWordConv.BIT_WORD_CONV
    (HolLibrary.Words.setupBlast (deps ()) BBitval BVal BPopcount BWordOps1 BWordOps3 BWordRule BValExpand BZxSx BBitRec BMisc1 BMasks BBitWordConv).run

initialize theReduce1 : IO.Ref (Option HolLibrary.Words.Reduce1) ← IO.mkRef none
unsafe def BReduce1 : HolLibrary.Words.Reduce1 :=
  cached theReduce1 "setupReduce1" fun _ => do
    let _ ← IO.mkRef BBlast.WORD_BLAST
    (HolLibrary.Words.setupReduce1 (deps ()) BBitval BVal BIval BLimits BGeneralOps BWordOps1 BWordOps2 BWordOps3 BReverse).run

initialize theReduce2 : IO.Ref (Option HolLibrary.Words.Reduce2) ← IO.mkRef none
unsafe def BReduce2 : HolLibrary.Words.Reduce2 :=
  cached theReduce2 "setupReduce2" fun _ => do
    let _ ← IO.mkRef BReduce1.WORD_WORD_CONV
    (HolLibrary.Words.setupReduce2 (deps ()) BWordType BBitsOfWord BVal BPopcount BWordOps1 BWordOps3 BZxSx BJoinSubword BInsertDup BReduce1).run

initialize theReduce3 : IO.Ref (Option HolLibrary.Words.Reduce3) ← IO.mkRef none
unsafe def BReduce3 : HolLibrary.Words.Reduce3 :=
  cached theReduce3 "setupReduce3" fun _ => do
    let _ ← IO.mkRef BReduce2.WORD_AND_CONV
    (HolLibrary.Words.setupReduce3 (deps ()) BDigitsum BBitval BWordType BVal BPopcount BGeneralOps BClzCtz BReverse BAlign BBitWordConv BReduce1 BReduce2).run

initialize theWordify : IO.Ref (Option HolLibrary.Words.Wordify) ← IO.mkRef none
unsafe def BWordify : HolLibrary.Words.Wordify :=
  cached theWordify "setupWordify" fun _ => do
    let _ ← IO.mkRef BReduce3.WORD_EVENPARITY_CONV
    (HolLibrary.Words.setupWordify (deps ()) BBitval BWordType BVal BIval BWordOps1 BWordOps2 BWordArith BZxSx BMisc1 BReduce1 BReduce3).run

initialize theBitblast : IO.Ref (Option HolLibrary.Words.Bitblast) ← IO.mkRef none
unsafe def BBitblast : HolLibrary.Words.Bitblast :=
  cached theBitblast "setupBitblast" fun _ => do
    let _ ← IO.mkRef BWordify.WORD_TO_IWORD_CONV
    (HolLibrary.Words.setupBitblast (deps ()) BBitval BWordType BVal BLimits BPopcount BGeneralOps BWordOps1 BWordOps3 BValExpand BMisc1 BMasks BClzCtz BReverse BBitWordConv BBlast BReduce3 BWordify).run

initialize theSimd : IO.Ref (Option HolLibrary.Words.Simd) ← IO.mkRef none
unsafe def BSimd : HolLibrary.Words.Simd :=
  cached theSimd "setupSimd" fun _ => do
    let _ ← IO.mkRef BBitblast.WORD_MUL_EXPAND_CONV
    (HolLibrary.Words.setupSimd (deps ()) BWordType BJoinSubword).run

-- @@BUNDLES END

-- @@EXPORTS BEGIN
-- WordSizes
unsafe def HAS_SIZE_8 : thm := BWordSizes.HAS_SIZE_8
unsafe def HAS_SIZE_16 : thm := BWordSizes.HAS_SIZE_16
unsafe def HAS_SIZE_32 : thm := BWordSizes.HAS_SIZE_32
unsafe def HAS_SIZE_64 : thm := BWordSizes.HAS_SIZE_64
unsafe def HAS_SIZE_128 : thm := BWordSizes.HAS_SIZE_128
unsafe def HAS_SIZE_256 : thm := BWordSizes.HAS_SIZE_256
unsafe def HAS_SIZE_512 : thm := BWordSizes.HAS_SIZE_512
unsafe def DIMINDEX_8 : thm := BWordSizes.DIMINDEX_8
unsafe def DIMINDEX_16 : thm := BWordSizes.DIMINDEX_16
unsafe def DIMINDEX_32 : thm := BWordSizes.DIMINDEX_32
unsafe def DIMINDEX_64 : thm := BWordSizes.DIMINDEX_64
unsafe def DIMINDEX_128 : thm := BWordSizes.DIMINDEX_128
unsafe def DIMINDEX_256 : thm := BWordSizes.DIMINDEX_256
unsafe def DIMINDEX_512 : thm := BWordSizes.DIMINDEX_512
unsafe def add_word_sizes := BWordSizes.add_word_sizes

-- Digitsum
unsafe def DIGITSUM_WORKS_GEN : thm := BDigitsum.DIGITSUM_WORKS_GEN
unsafe def DIGITSUM_WORKS : thm := BDigitsum.DIGITSUM_WORKS
unsafe def DIGITSUM_BOUND : thm := BDigitsum.DIGITSUM_BOUND
unsafe def DIGITSUM_SPLIT : thm := BDigitsum.DIGITSUM_SPLIT
unsafe def DIGITSUM_DIV : thm := BDigitsum.DIGITSUM_DIV
unsafe def DIGITSUM_MOD : thm := BDigitsum.DIGITSUM_MOD
unsafe def DIGITSUM_MOD_NUMSEG : thm := BDigitsum.DIGITSUM_MOD_NUMSEG
unsafe def DIGITSUM_DIV_NUMSEG : thm := BDigitsum.DIGITSUM_DIV_NUMSEG
unsafe def DIGITSUM_DIV_MOD : thm := BDigitsum.DIGITSUM_DIV_MOD
unsafe def DIGITSUM_UNIQUE : thm := BDigitsum.DIGITSUM_UNIQUE

-- Bitval
unsafe def bitval : thm := BBitval.bitval
unsafe def BITVAL_CLAUSES : thm := BBitval.BITVAL_CLAUSES
unsafe def BITVAL_BOUND : thm := BBitval.BITVAL_BOUND
unsafe def BITVAL_BOUND_ALT : thm := BBitval.BITVAL_BOUND_ALT
unsafe def ODD_BITVAL : thm := BBitval.ODD_BITVAL
unsafe def EVEN_BITVAL : thm := BBitval.EVEN_BITVAL
unsafe def NUM_AS_BITVAL : thm := BBitval.NUM_AS_BITVAL
unsafe def NUM_AS_BITVAL_ALT : thm := BBitval.NUM_AS_BITVAL_ALT
unsafe def BITVAL_EQ_0 : thm := BBitval.BITVAL_EQ_0
unsafe def BITVAL_EQ_1 : thm := BBitval.BITVAL_EQ_1
unsafe def BITVAL_POS : thm := BBitval.BITVAL_POS
unsafe def BITVAL_NOT : thm := BBitval.BITVAL_NOT
unsafe def BITVAL_AND : thm := BBitval.BITVAL_AND
unsafe def BITVAL_OR : thm := BBitval.BITVAL_OR
unsafe def BITVAL_IFF : thm := BBitval.BITVAL_IFF
unsafe def BITVAL_XOR : thm := BBitval.BITVAL_XOR
unsafe def BITVAL_EXP : thm := BBitval.BITVAL_EXP
unsafe def INT_BITVAL_NOT : thm := BBitval.INT_BITVAL_NOT
unsafe def INT_BITVAL_AND : thm := BBitval.INT_BITVAL_AND
unsafe def INT_BITVAL_OR : thm := BBitval.INT_BITVAL_OR
unsafe def INT_BITVAL_IMP : thm := BBitval.INT_BITVAL_IMP
unsafe def INT_BITVAL_IFF : thm := BBitval.INT_BITVAL_IFF
unsafe def INT_BITVAL_POW : thm := BBitval.INT_BITVAL_POW
unsafe def REAL_BITVAL_NOT : thm := BBitval.REAL_BITVAL_NOT
unsafe def BITVAL_ODD : thm := BBitval.BITVAL_ODD
unsafe def LE_BITVAL : thm := BBitval.LE_BITVAL
unsafe def INT_LE_BITVAL : thm := BBitval.INT_LE_BITVAL
unsafe def REAL_LE_BITVAL : thm := BBitval.REAL_LE_BITVAL
unsafe def EQ_BITVAL : thm := BBitval.EQ_BITVAL
unsafe def INT_EQ_BITVAL : thm := BBitval.INT_EQ_BITVAL
unsafe def REAL_EQ_BITVAL : thm := BBitval.REAL_EQ_BITVAL
unsafe def BINT_POLY_CONV : HolCore.Equal.ioconv := fun t => BBitval.BINT_POLY_CONV t

-- Binary
unsafe def ODD_MOD_POW2 : thm := BBinary.ODD_MOD_POW2
unsafe def BINARY_DIGITSUM_BOUND : thm := BBinary.BINARY_DIGITSUM_BOUND
unsafe def BINARY_DIGITSUM_SPLIT : thm := BBinary.BINARY_DIGITSUM_SPLIT
unsafe def BINARY_DIGITSUM_DIV : thm := BBinary.BINARY_DIGITSUM_DIV
unsafe def BINARY_DIGITSUM_MOD : thm := BBinary.BINARY_DIGITSUM_MOD

-- WordType
unsafe def word_tybij : thm := BWordType.word_tybij
unsafe def WORD_EQ_BITVECTOR : thm := BWordType.WORD_EQ_BITVECTOR
unsafe def bit : thm := BWordType.bit
unsafe def WORD_EQ_BITS_ALT : thm := BWordType.WORD_EQ_BITS_ALT
unsafe def WORD_EQ_BITS : thm := BWordType.WORD_EQ_BITS
unsafe def BIT_TRIVIAL : thm := BWordType.BIT_TRIVIAL
unsafe def BIT_GUARD : thm := BWordType.BIT_GUARD

-- BitsOfWord
unsafe def bits_of_word : thm := BBitsOfWord.bits_of_word
unsafe def word_of_bits : thm := BBitsOfWord.word_of_bits
unsafe def IN_BITS_OF_WORD : thm := BBitsOfWord.IN_BITS_OF_WORD
unsafe def BIT_WORD_OF_BITS : thm := BBitsOfWord.BIT_WORD_OF_BITS
unsafe def WORD_OF_BITS_EQ : thm := BBitsOfWord.WORD_OF_BITS_EQ
unsafe def WORD_OF_BITS_OF_WORD : thm := BBitsOfWord.WORD_OF_BITS_OF_WORD
unsafe def BITS_OF_WORD_OF_BITS : thm := BBitsOfWord.BITS_OF_WORD_OF_BITS
unsafe def BITS_OF_WORD_EQ : thm := BBitsOfWord.BITS_OF_WORD_EQ
unsafe def WORD_OF_BITS : thm := BBitsOfWord.WORD_OF_BITS
unsafe def WORD_OF_BITS_ALT : thm := BBitsOfWord.WORD_OF_BITS_ALT
unsafe def FINITE_BITS_OF_WORD : thm := BBitsOfWord.FINITE_BITS_OF_WORD
unsafe def BITS_OF_WORD_SUBSET : thm := BBitsOfWord.BITS_OF_WORD_SUBSET
unsafe def BITS_OF_WORD_SUBSET_ALT : thm := BBitsOfWord.BITS_OF_WORD_SUBSET_ALT
unsafe def BITS_OF_WORD_SUBSET_NUMSEG : thm := BBitsOfWord.BITS_OF_WORD_SUBSET_NUMSEG

-- Val
unsafe def val_def : thm := BVal.val_def
unsafe def VAL : thm := BVal.VAL
unsafe def word : thm := BVal.word
unsafe def BIT_WORD : thm := BVal.BIT_WORD
unsafe def BIT_LSB_WORD : thm := BVal.BIT_LSB_WORD
unsafe def BIT_WORD_0 : thm := BVal.BIT_WORD_0
unsafe def BITS_OF_WORD_0 : thm := BVal.BITS_OF_WORD_0
unsafe def BITS_OF_WORD_EQ_EMPTY : thm := BVal.BITS_OF_WORD_EQ_EMPTY
unsafe def WORD_OF_BITS_EMPTY : thm := BVal.WORD_OF_BITS_EMPTY
unsafe def BITVAL_BIT_WORD : thm := BVal.BITVAL_BIT_WORD
unsafe def WORD_VAL : thm := BVal.WORD_VAL
unsafe def VAL_WORD : thm := BVal.VAL_WORD
unsafe def MOD_VAL_WORD : thm := BVal.MOD_VAL_WORD
unsafe def DIVIDES_VAL_WORD : thm := BVal.DIVIDES_VAL_WORD
unsafe def VAL_WORD_LE : thm := BVal.VAL_WORD_LE
unsafe def VAL_WORD_LT : thm := BVal.VAL_WORD_LT
unsafe def FORALL_WORD : thm := BVal.FORALL_WORD
unsafe def EXISTS_WORD : thm := BVal.EXISTS_WORD
unsafe def VAL_WORD_0 : thm := BVal.VAL_WORD_0
unsafe def VAL_WORD_1 : thm := BVal.VAL_WORD_1
unsafe def WORD_BITVAL : thm := BVal.WORD_BITVAL
unsafe def VAL_WORD_BITVAL : thm := BVal.VAL_WORD_BITVAL
unsafe def VAL_WORD_EQ : thm := BVal.VAL_WORD_EQ
unsafe def VAL_EQ : thm := BVal.VAL_EQ
unsafe def VAL_EQ_0 : thm := BVal.VAL_EQ_0
unsafe def VAL_EQ_1 : thm := BVal.VAL_EQ_1
unsafe def VAL_EQ_BITVAL : thm := BVal.VAL_EQ_BITVAL
unsafe def WORD_BITVAL_EQ_0 : thm := BVal.WORD_BITVAL_EQ_0
unsafe def WORD_BITVAL_EQ_1 : thm := BVal.WORD_BITVAL_EQ_1
unsafe def WORD_NE_10 : thm := BVal.WORD_NE_10
unsafe def WORD_EQ : thm := BVal.WORD_EQ
unsafe def WORD_EQ_IMP : thm := BVal.WORD_EQ_IMP
unsafe def WORD_EQ_0 : thm := BVal.WORD_EQ_0
unsafe def VAL_BOUND : thm := BVal.VAL_BOUND
unsafe def INT_VAL_BOUND : thm := BVal.INT_VAL_BOUND
unsafe def VAL_MOD_REFL : thm := BVal.VAL_MOD_REFL
unsafe def VAL_WORD_EQ_EQ : thm := BVal.VAL_WORD_EQ_EQ
unsafe def FORALL_VAL_GEN : thm := BVal.FORALL_VAL_GEN
unsafe def FORALL_VAL : thm := BVal.FORALL_VAL
unsafe def VAL_CONG : thm := BVal.VAL_CONG
unsafe def WORD_MOD_SIZE : thm := BVal.WORD_MOD_SIZE
unsafe def VAL_WORD_CONG : thm := BVal.VAL_WORD_CONG
unsafe def VAL_WORD_GALOIS : thm := BVal.VAL_WORD_GALOIS
unsafe def WORD_VAL_GALOIS : thm := BVal.WORD_VAL_GALOIS
unsafe def DIVIDES_VAL_WORD_EQ : thm := BVal.DIVIDES_VAL_WORD_EQ
unsafe def BIT_VAL : thm := BVal.BIT_VAL
unsafe def BIT_VAL_MOD : thm := BVal.BIT_VAL_MOD
unsafe def BIT_LSB : thm := BVal.BIT_LSB
unsafe def TWICE_MSB : thm := BVal.TWICE_MSB
unsafe def MSB_VAL : thm := BVal.MSB_VAL
unsafe def MSB_INT_VAL : thm := BVal.MSB_INT_VAL
unsafe def BITVAL_MSB : thm := BVal.BITVAL_MSB
unsafe def BLOCK_BITS_ZERO_ALT : thm := BVal.BLOCK_BITS_ZERO_ALT
unsafe def BLOCK_BITS_ZERO : thm := BVal.BLOCK_BITS_ZERO
unsafe def LOWER_BITS_ZERO : thm := BVal.LOWER_BITS_ZERO
unsafe def UPPER_BITS_ZERO : thm := BVal.UPPER_BITS_ZERO
unsafe def UPPER_BITS_ZERO_ALT : thm := BVal.UPPER_BITS_ZERO_ALT
unsafe def VAL_WORD_OF_BITS : thm := BVal.VAL_WORD_OF_BITS
unsafe def WORD_OF_BITS_AS_WORD : thm := BVal.WORD_OF_BITS_AS_WORD
unsafe def WORD_OF_BITS_AS_WORD_FINITE : thm := BVal.WORD_OF_BITS_AS_WORD_FINITE
unsafe def WORD_OF_BITS_SING_AS_WORD : thm := BVal.WORD_OF_BITS_SING_AS_WORD
unsafe def VAL_WORD_OF_BITS_SING : thm := BVal.VAL_WORD_OF_BITS_SING
unsafe def WORD_OF_BITS_MASK : thm := BVal.WORD_OF_BITS_MASK
unsafe def BIT_MASK_WORD : thm := BVal.BIT_MASK_WORD
unsafe def BIT_WORD_POW2 : thm := BVal.BIT_WORD_POW2
unsafe def BIT_WORD_1 : thm := BVal.BIT_WORD_1
unsafe def BIT_WORD_BITVAL : thm := BVal.BIT_WORD_BITVAL
unsafe def WORD_OF_BITS_SING_AS_WORD_1 : thm := BVal.WORD_OF_BITS_SING_AS_WORD_1
unsafe def BITS_OF_WORD_1 : thm := BVal.BITS_OF_WORD_1
unsafe def BIT_WORD_OF_BITS_SING : thm := BVal.BIT_WORD_OF_BITS_SING
unsafe def VAL_MOD : thm := BVal.VAL_MOD
unsafe def VAL_MOD_2 : thm := BVal.VAL_MOD_2
unsafe def VAL_MOD_STEP : thm := BVal.VAL_MOD_STEP
unsafe def VAL_DIV : thm := BVal.VAL_DIV
unsafe def VAL_DIV_ALT : thm := BVal.VAL_DIV_ALT
unsafe def VAL_LE_BITS : thm := BVal.VAL_LE_BITS
unsafe def VAL_LE_SUBSET : thm := BVal.VAL_LE_SUBSET

-- Ival
unsafe def ival : thm := BIval.ival
unsafe def iword : thm := BIval.iword
unsafe def word_sgn : thm := BIval.word_sgn
unsafe def INT_IVAL : thm := BIval.INT_IVAL
unsafe def WORD_IWORD : thm := BIval.WORD_IWORD
unsafe def IVAL_VAL : thm := BIval.IVAL_VAL
unsafe def VAL_IVAL : thm := BIval.VAL_IVAL
unsafe def IVAL_EQ_VAL : thm := BIval.IVAL_EQ_VAL
unsafe def INT_VAL_IWORD : thm := BIval.INT_VAL_IWORD
unsafe def INT_VAL_IWORD_EQ : thm := BIval.INT_VAL_IWORD_EQ
unsafe def MSB_IVAL : thm := BIval.MSB_IVAL
unsafe def IVAL_BOUND : thm := BIval.IVAL_BOUND
unsafe def IVAL_WORD_0 : thm := BIval.IVAL_WORD_0
unsafe def IVAL_WORD_1 : thm := BIval.IVAL_WORD_1
unsafe def IVAL_VAL_CONG : thm := BIval.IVAL_VAL_CONG
unsafe def IVAL_CONG : thm := BIval.IVAL_CONG
unsafe def IVAL_EQ : thm := BIval.IVAL_EQ
unsafe def IVAL_EQ_0 : thm := BIval.IVAL_EQ_0
unsafe def IVAL_EQ_1 : thm := BIval.IVAL_EQ_1
unsafe def IWORD_EQ : thm := BIval.IWORD_EQ
unsafe def IWORD_REM_SIZE : thm := BIval.IWORD_REM_SIZE
unsafe def IVAL_IWORD_CONG : thm := BIval.IVAL_IWORD_CONG
unsafe def VAL_IWORD_CONG : thm := BIval.VAL_IWORD_CONG
unsafe def IVAL_WORD_CONG : thm := BIval.IVAL_WORD_CONG
unsafe def IVAL_IWORD : thm := BIval.IVAL_IWORD
unsafe def IWORD_IVAL : thm := BIval.IWORD_IVAL
unsafe def IVAL_IWORD_GALOIS : thm := BIval.IVAL_IWORD_GALOIS
unsafe def BIT_IVAL : thm := BIval.BIT_IVAL
unsafe def BIT_IWORD : thm := BIval.BIT_IWORD
unsafe def INT_REM_IVAL : thm := BIval.INT_REM_IVAL
unsafe def VAL_IVAL_REM : thm := BIval.VAL_IVAL_REM
unsafe def INT_REM_IVAL_IWORD : thm := BIval.INT_REM_IVAL_IWORD
unsafe def INT_DIVIDES_IVAL_IWORD : thm := BIval.INT_DIVIDES_IVAL_IWORD
unsafe def FORALL_IVAL_GEN : thm := BIval.FORALL_IVAL_GEN
unsafe def FORALL_IVAL : thm := BIval.FORALL_IVAL
unsafe def FORALL_IWORD : thm := BIval.FORALL_IWORD
unsafe def EXISTS_IWORD : thm := BIval.EXISTS_IWORD
unsafe def IVAL_REM_2 : thm := BIval.IVAL_REM_2
unsafe def BIT_LSB_IWORD : thm := BIval.BIT_LSB_IWORD
unsafe def TWOS_COMPLEMENT_GEN : thm := BIval.TWOS_COMPLEMENT_GEN
unsafe def TWOS_COMPLEMENT : thm := BIval.TWOS_COMPLEMENT

-- NumBits
unsafe def numbit : thm := BNumBits.numbit
unsafe def NUMBIT_VAL : thm := BNumBits.NUMBIT_VAL
unsafe def numbitCtx := BNumBits.numbitCtx
unsafe def bits_of_num : thm := BNumBits.bits_of_num
unsafe def IN_BITS_OF_NUM : thm := BNumBits.IN_BITS_OF_NUM
unsafe def BITS_OF_NUM_SUBSET_NUMSEG_LT : thm := BNumBits.BITS_OF_NUM_SUBSET_NUMSEG_LT
unsafe def FINITE_BITS_OF_NUM : thm := BNumBits.FINITE_BITS_OF_NUM
unsafe def NSUM_BITS_OF_NUM : thm := BNumBits.NSUM_BITS_OF_NUM
unsafe def BITS_OF_NUM_NSUM : thm := BNumBits.BITS_OF_NUM_NSUM
unsafe def BITS_OF_NUM_EQ : thm := BNumBits.BITS_OF_NUM_EQ
unsafe def BITS_OF_NUM_GALOIS : thm := BNumBits.BITS_OF_NUM_GALOIS
unsafe def NSUM_BITS_DIV : thm := BNumBits.NSUM_BITS_DIV
unsafe def NSUM_BITS_MOD : thm := BNumBits.NSUM_BITS_MOD
unsafe def NSUM_BITS_EQ : thm := BNumBits.NSUM_BITS_EQ
unsafe def BITSUM_BOUND : thm := BNumBits.BITSUM_BOUND
unsafe def BITS_OF_NUM_SUBSET_NUMSEG_EQ : thm := BNumBits.BITS_OF_NUM_SUBSET_NUMSEG_EQ
unsafe def BITSUM_DIVIDES : thm := BNumBits.BITSUM_DIVIDES
unsafe def BITS_OF_NUM_DISJOINT_NUMSEG_EQ : thm := BNumBits.BITS_OF_NUM_DISJOINT_NUMSEG_EQ
unsafe def BITS_OF_NUM_0 : thm := BNumBits.BITS_OF_NUM_0
unsafe def BITS_OF_NUM_POW2 : thm := BNumBits.BITS_OF_NUM_POW2
unsafe def BITS_OF_NUM_1 : thm := BNumBits.BITS_OF_NUM_1
unsafe def BITS_OF_NUM_DIV : thm := BNumBits.BITS_OF_NUM_DIV
unsafe def BITS_OF_NUM_MOD : thm := BNumBits.BITS_OF_NUM_MOD
unsafe def BITS_OF_NUM_MUL_ALT : thm := BNumBits.BITS_OF_NUM_MUL_ALT
unsafe def BITS_OF_NUM_MUL : thm := BNumBits.BITS_OF_NUM_MUL
unsafe def BITS_OF_NUM_ADD : thm := BNumBits.BITS_OF_NUM_ADD
unsafe def DISJOINT_BITS_HILO : thm := BNumBits.DISJOINT_BITS_HILO
unsafe def DISJOINT_BITS_CLAUSES : thm := BNumBits.DISJOINT_BITS_CLAUSES
unsafe def DIV_MOD_DISJOINT_BITS : thm := BNumBits.DIV_MOD_DISJOINT_BITS
unsafe def BITS_OF_WORD_WORD : thm := BNumBits.BITS_OF_WORD_WORD
unsafe def BITS_OF_NUM_VAL : thm := BNumBits.BITS_OF_NUM_VAL

-- NumShiftAdd
unsafe def num_shift_add : thm := BNumShiftAdd.num_shift_add
unsafe def num_shift_add_0 : thm := BNumShiftAdd.num_shift_add_0
unsafe def EXP_2_MOD_LT : thm := BNumShiftAdd.EXP_2_MOD_LT
unsafe def num_shift_add_SUC : thm := BNumShiftAdd.num_shift_add_SUC
unsafe def num_shift_add_lt : thm := BNumShiftAdd.num_shift_add_lt
unsafe def num_shift_add_mod : thm := BNumShiftAdd.num_shift_add_mod
unsafe def nsaCtx := BNumShiftAdd.nsaCtx

-- Limits
unsafe def word_UINT_MAX : thm := BLimits.word_UINT_MAX
unsafe def word_INT_MIN : thm := BLimits.word_INT_MIN
unsafe def word_INT_MAX : thm := BLimits.word_INT_MAX
unsafe def WORD_INT_MIN : thm := BLimits.WORD_INT_MIN
unsafe def WORD_INT_MAX : thm := BLimits.WORD_INT_MAX
unsafe def VAL_WORD_UINT_MAX : thm := BLimits.VAL_WORD_UINT_MAX
unsafe def IVAL_WORD_INT_MIN : thm := BLimits.IVAL_WORD_INT_MIN
unsafe def IVAL_WORD_INT_MAX : thm := BLimits.IVAL_WORD_INT_MAX
unsafe def VAL_BOUND_ALT : thm := BLimits.VAL_BOUND_ALT
unsafe def IVAL_BOUND_ALT : thm := BLimits.IVAL_BOUND_ALT
unsafe def VAL_WORD_INT_MIN : thm := BLimits.VAL_WORD_INT_MIN
unsafe def INT_VAL_WORD_INT_MIN : thm := BLimits.INT_VAL_WORD_INT_MIN
unsafe def WORD_INT_MIN_ALT : thm := BLimits.WORD_INT_MIN_ALT
unsafe def BIT_WORD_INT_MIN : thm := BLimits.BIT_WORD_INT_MIN
unsafe def word_saturate : thm := BLimits.word_saturate
unsafe def iword_saturate : thm := BLimits.iword_saturate

-- Popcount
unsafe def word_popcount : thm := BPopcount.word_popcount
unsafe def HAS_SIZE_BITS_OF_WORD_POPCOUNT : thm := BPopcount.HAS_SIZE_BITS_OF_WORD_POPCOUNT
unsafe def WORD_POPCOUNT_BOUND : thm := BPopcount.WORD_POPCOUNT_BOUND
unsafe def WORD_POPCOUNT_BOUND_SIZE : thm := BPopcount.WORD_POPCOUNT_BOUND_SIZE
unsafe def WORD_POPCOUNT_EQ_0 : thm := BPopcount.WORD_POPCOUNT_EQ_0
unsafe def WORD_POPCOUNT_0 : thm := BPopcount.WORD_POPCOUNT_0
unsafe def WORD_POPCOUNT_1 : thm := BPopcount.WORD_POPCOUNT_1
unsafe def WORD_POPCOUNT_BITVAL : thm := BPopcount.WORD_POPCOUNT_BITVAL
unsafe def WORD_POPCOUNT_NSUM : thm := BPopcount.WORD_POPCOUNT_NSUM
unsafe def WORD_POPCOUNT_LE_BITS : thm := BPopcount.WORD_POPCOUNT_LE_BITS
unsafe def WORD_POPCOUNT_WORD_OF_BITS_GEN : thm := BPopcount.WORD_POPCOUNT_WORD_OF_BITS_GEN
unsafe def WORD_POPCOUNT_WORD_OF_BITS : thm := BPopcount.WORD_POPCOUNT_WORD_OF_BITS
unsafe def word_evenparity : thm := BPopcount.word_evenparity
unsafe def word_oddparity : thm := BPopcount.word_oddparity
unsafe def NOT_WORD_EVENPARITY : thm := BPopcount.NOT_WORD_EVENPARITY
unsafe def NOT_WORD_ODDPARITY : thm := BPopcount.NOT_WORD_ODDPARITY
unsafe def WORD_EVENPARITY_0 : thm := BPopcount.WORD_EVENPARITY_0
unsafe def WORD_ODDPARITY_0 : thm := BPopcount.WORD_ODDPARITY_0
unsafe def WORD_EVENPARITY_1 : thm := BPopcount.WORD_EVENPARITY_1
unsafe def WORD_ODDPARITY_1 : thm := BPopcount.WORD_ODDPARITY_1

-- GeneralOps
unsafe def modular : thm := BGeneralOps.modular
unsafe def VAL_MODULAR : thm := BGeneralOps.VAL_MODULAR
unsafe def CONG_MODULAR : thm := BGeneralOps.CONG_MODULAR
unsafe def imodular : thm := BGeneralOps.imodular
unsafe def CONG_IMODULAR : thm := BGeneralOps.CONG_IMODULAR
unsafe def relational2 : thm := BGeneralOps.relational2
unsafe def irelational2 : thm := BGeneralOps.irelational2
unsafe def bitwise1 : thm := BGeneralOps.bitwise1
unsafe def bitwise2 : thm := BGeneralOps.bitwise2
unsafe def BIT_BITWISE1 : thm := BGeneralOps.BIT_BITWISE1
unsafe def BIT_BITWISE2 : thm := BGeneralOps.BIT_BITWISE2

-- WordOps1
unsafe def word_not : thm := BWordOps1.word_not
unsafe def BIT_WORD_NOT : thm := BWordOps1.BIT_WORD_NOT
unsafe def BITS_OF_WORD_NOT : thm := BWordOps1.BITS_OF_WORD_NOT
unsafe def WORD_OF_BITS_DIFF : thm := BWordOps1.WORD_OF_BITS_DIFF
unsafe def VAL_WORD_NOT : thm := BWordOps1.VAL_WORD_NOT
unsafe def INT_VAL_WORD_NOT : thm := BWordOps1.INT_VAL_WORD_NOT
unsafe def REAL_VAL_WORD_NOT : thm := BWordOps1.REAL_VAL_WORD_NOT
unsafe def WORD_POPCOUNT_NOT : thm := BWordOps1.WORD_POPCOUNT_NOT
unsafe def word_and : thm := BWordOps1.word_and
unsafe def BIT_WORD_AND : thm := BWordOps1.BIT_WORD_AND
unsafe def BIT_WORD_AND_ALT : thm := BWordOps1.BIT_WORD_AND_ALT
unsafe def BITS_OF_WORD_AND : thm := BWordOps1.BITS_OF_WORD_AND
unsafe def WORD_AND_EQ_0 : thm := BWordOps1.WORD_AND_EQ_0
unsafe def WORD_OF_BITS_INTER : thm := BWordOps1.WORD_OF_BITS_INTER
unsafe def WORD_AND_WORD_OF_BITS_SING : thm := BWordOps1.WORD_AND_WORD_OF_BITS_SING
unsafe def WORD_OF_BITS_SING_AND_WORD : thm := BWordOps1.WORD_OF_BITS_SING_AND_WORD
unsafe def WORD_AND_POW2 : thm := BWordOps1.WORD_AND_POW2
unsafe def VAL_WORD_AND_POW2 : thm := BWordOps1.VAL_WORD_AND_POW2
unsafe def WORD_AND_POW2_BITVAL : thm := BWordOps1.WORD_AND_POW2_BITVAL
unsafe def VAL_WORD_AND_POW2_BITVAL : thm := BWordOps1.VAL_WORD_AND_POW2_BITVAL
unsafe def VAL_WORD_AND_LE : thm := BWordOps1.VAL_WORD_AND_LE
unsafe def VAL_WORD_AND_LE_MIN : thm := BWordOps1.VAL_WORD_AND_LE_MIN
unsafe def VAL_WORD_AND_WORD_LE : thm := BWordOps1.VAL_WORD_AND_WORD_LE
unsafe def WORD_POPCOUNT_AND : thm := BWordOps1.WORD_POPCOUNT_AND
unsafe def word_or : thm := BWordOps1.word_or
unsafe def BIT_WORD_OR : thm := BWordOps1.BIT_WORD_OR
unsafe def BIT_WORD_OR_ALT : thm := BWordOps1.BIT_WORD_OR_ALT
unsafe def BITS_OF_WORD_OR : thm := BWordOps1.BITS_OF_WORD_OR
unsafe def WORD_OF_BITS_UNION : thm := BWordOps1.WORD_OF_BITS_UNION
unsafe def VAL_WORD_OR_LE : thm := BWordOps1.VAL_WORD_OR_LE
unsafe def VAL_WORD_OR_LE_MAX : thm := BWordOps1.VAL_WORD_OR_LE_MAX
unsafe def WORD_POPCOUNT_OR : thm := BWordOps1.WORD_POPCOUNT_OR
unsafe def WORD_POPCOUNT_OR_DISJOINT : thm := BWordOps1.WORD_POPCOUNT_OR_DISJOINT
unsafe def word_xor : thm := BWordOps1.word_xor
unsafe def BIT_WORD_XOR : thm := BWordOps1.BIT_WORD_XOR
unsafe def BIT_WORD_XOR_ALT : thm := BWordOps1.BIT_WORD_XOR_ALT
unsafe def VAL_WORD_ADD_AND_XOR : thm := BWordOps1.VAL_WORD_ADD_AND_XOR
unsafe def VAL_WORD_ADD_AND_OR : thm := BWordOps1.VAL_WORD_ADD_AND_OR
unsafe def VAL_WORD_OR_DISJOINT : thm := BWordOps1.VAL_WORD_OR_DISJOINT
unsafe def VAL_WORD_OR_AND_XOR : thm := BWordOps1.VAL_WORD_OR_AND_XOR
unsafe def REAL_VAL_WORD_XOR : thm := BWordOps1.REAL_VAL_WORD_XOR
unsafe def word_add : thm := BWordOps1.word_add
unsafe def VAL_WORD_ADD : thm := BWordOps1.VAL_WORD_ADD
unsafe def VAL_WORD_ADD_CASES : thm := BWordOps1.VAL_WORD_ADD_CASES
unsafe def VAL_WORD_ADC_CASES : thm := BWordOps1.VAL_WORD_ADC_CASES
unsafe def INT_VAL_WORD_ADD_CASES : thm := BWordOps1.INT_VAL_WORD_ADD_CASES
unsafe def CONG_WORD_ADD : thm := BWordOps1.CONG_WORD_ADD
unsafe def INT_CONG_WORD_ADD : thm := BWordOps1.INT_CONG_WORD_ADD
unsafe def WORD_ADD : thm := BWordOps1.WORD_ADD
unsafe def ICONG_WORD_ADD : thm := BWordOps1.ICONG_WORD_ADD
unsafe def IWORD_INT_ADD : thm := BWordOps1.IWORD_INT_ADD
unsafe def WORD_ADD_IMODULAR : thm := BWordOps1.WORD_ADD_IMODULAR
unsafe def ODD_VAL_WORD : thm := BWordOps1.ODD_VAL_WORD
unsafe def EVEN_VAL_WORD : thm := BWordOps1.EVEN_VAL_WORD
unsafe def ODD_VAL_WORD_ADD : thm := BWordOps1.ODD_VAL_WORD_ADD
unsafe def EVEN_VAL_WORD_ADD : thm := BWordOps1.EVEN_VAL_WORD_ADD
unsafe def word_sub : thm := BWordOps1.word_sub
unsafe def VAL_WORD_SUB : thm := BWordOps1.VAL_WORD_SUB
unsafe def VAL_WORD_SUB_CASES : thm := BWordOps1.VAL_WORD_SUB_CASES
unsafe def INT_VAL_WORD_SUB_CASES : thm := BWordOps1.INT_VAL_WORD_SUB_CASES
unsafe def CONG_WORD_SUB : thm := BWordOps1.CONG_WORD_SUB
unsafe def INT_CONG_WORD_SUB : thm := BWordOps1.INT_CONG_WORD_SUB
unsafe def INT_VAL_WORD_SUB : thm := BWordOps1.INT_VAL_WORD_SUB
unsafe def ICONG_WORD_SUB : thm := BWordOps1.ICONG_WORD_SUB
unsafe def IWORD_INT_SUB : thm := BWordOps1.IWORD_INT_SUB
unsafe def WORD_SUB_IMODULAR : thm := BWordOps1.WORD_SUB_IMODULAR
unsafe def WORD_SUB : thm := BWordOps1.WORD_SUB
unsafe def word_neg : thm := BWordOps1.word_neg
unsafe def ODD_VAL_WORD_SUB : thm := BWordOps1.ODD_VAL_WORD_SUB
unsafe def EVEN_VAL_WORD_SUB : thm := BWordOps1.EVEN_VAL_WORD_SUB
unsafe def VAL_WORD_NEG : thm := BWordOps1.VAL_WORD_NEG
unsafe def VAL_WORD_NEG_CASES : thm := BWordOps1.VAL_WORD_NEG_CASES
unsafe def INT_VAL_WORD_NEG_CASES : thm := BWordOps1.INT_VAL_WORD_NEG_CASES
unsafe def REAL_VAL_WORD_NEG_CASES : thm := BWordOps1.REAL_VAL_WORD_NEG_CASES
unsafe def INT_VAL_WORD_NEG : thm := BWordOps1.INT_VAL_WORD_NEG
unsafe def REAL_VAL_WORD_NEG : thm := BWordOps1.REAL_VAL_WORD_NEG
unsafe def CONG_WORD_NEG : thm := BWordOps1.CONG_WORD_NEG
unsafe def INT_CONG_WORD_NEG : thm := BWordOps1.INT_CONG_WORD_NEG
unsafe def ICONG_WORD_NEG : thm := BWordOps1.ICONG_WORD_NEG
unsafe def IWORD_INT_NEG : thm := BWordOps1.IWORD_INT_NEG
unsafe def WORD_NEG_AS_ADD : thm := BWordOps1.WORD_NEG_AS_ADD

-- WordOps2
unsafe def WORD_NOT_AS_SUB : thm := BWordOps2.WORD_NOT_AS_SUB
unsafe def VAL_WORD_NEG_1 : thm := BWordOps2.VAL_WORD_NEG_1
unsafe def IVAL_WORD_NEG_1 : thm := BWordOps2.IVAL_WORD_NEG_1
unsafe def IVAL_EQ_MINUS1 : thm := BWordOps2.IVAL_EQ_MINUS1
unsafe def WORD_NEG_1 : thm := BWordOps2.WORD_NEG_1
unsafe def ODD_VAL_WORD_NEG : thm := BWordOps2.ODD_VAL_WORD_NEG
unsafe def EVEN_VAL_WORD_NEG : thm := BWordOps2.EVEN_VAL_WORD_NEG
unsafe def word_mul : thm := BWordOps2.word_mul
unsafe def VAL_WORD_MUL : thm := BWordOps2.VAL_WORD_MUL
unsafe def CONG_WORD_MUL : thm := BWordOps2.CONG_WORD_MUL
unsafe def INT_CONG_WORD_MUL : thm := BWordOps2.INT_CONG_WORD_MUL
unsafe def WORD_MUL : thm := BWordOps2.WORD_MUL
unsafe def ICONG_WORD_MUL : thm := BWordOps2.ICONG_WORD_MUL
unsafe def IWORD_INT_MUL : thm := BWordOps2.IWORD_INT_MUL
unsafe def WORD_MUL_IMODULAR : thm := BWordOps2.WORD_MUL_IMODULAR
unsafe def ODD_VAL_WORD_MUL : thm := BWordOps2.ODD_VAL_WORD_MUL
unsafe def EVEN_VAL_WORD_MUL : thm := BWordOps2.EVEN_VAL_WORD_MUL
unsafe def word_udiv : thm := BWordOps2.word_udiv
unsafe def VAL_WORD_UDIV : thm := BWordOps2.VAL_WORD_UDIV
unsafe def word_umod : thm := BWordOps2.word_umod
unsafe def VAL_WORD_UMOD : thm := BWordOps2.VAL_WORD_UMOD
unsafe def word_umax : thm := BWordOps2.word_umax
unsafe def word_imax : thm := BWordOps2.word_imax
unsafe def VAL_WORD_UMAX : thm := BWordOps2.VAL_WORD_UMAX
unsafe def WORD_UMAX : thm := BWordOps2.WORD_UMAX
unsafe def WORD_UMAX_SYM : thm := BWordOps2.WORD_UMAX_SYM
unsafe def WORD_UMAX_ASSOC : thm := BWordOps2.WORD_UMAX_ASSOC
unsafe def IVAL_WORD_IMAX : thm := BWordOps2.IVAL_WORD_IMAX
unsafe def word_umin : thm := BWordOps2.word_umin
unsafe def word_imin : thm := BWordOps2.word_imin
unsafe def VAL_WORD_UMIN : thm := BWordOps2.VAL_WORD_UMIN
unsafe def WORD_UMIN : thm := BWordOps2.WORD_UMIN
unsafe def WORD_UMIN_SYM : thm := BWordOps2.WORD_UMIN_SYM
unsafe def WORD_UMIN_ASSOC : thm := BWordOps2.WORD_UMIN_ASSOC
unsafe def IVAL_WORD_IMIN : thm := BWordOps2.IVAL_WORD_IMIN
unsafe def word_shl : thm := BWordOps2.word_shl
unsafe def VAL_WORD_SHL : thm := BWordOps2.VAL_WORD_SHL
unsafe def CONG_WORD_SHL : thm := BWordOps2.CONG_WORD_SHL
unsafe def ICONG_WORD_SHL : thm := BWordOps2.ICONG_WORD_SHL
unsafe def BIT_WORD_SHL : thm := BWordOps2.BIT_WORD_SHL
unsafe def WORD_SHL_WORD_OF_BITS : thm := BWordOps2.WORD_SHL_WORD_OF_BITS
unsafe def WORD_SHL_0 : thm := BWordOps2.WORD_SHL_0
unsafe def WORD_SHL_ZERO : thm := BWordOps2.WORD_SHL_ZERO
unsafe def WORD_SHL_TRIVIAL : thm := BWordOps2.WORD_SHL_TRIVIAL
unsafe def WORD_SHL_COMPOSE : thm := BWordOps2.WORD_SHL_COMPOSE
unsafe def WORD_SHL_LSB_ALT : thm := BWordOps2.WORD_SHL_LSB_ALT
unsafe def WORD_SHL_LSB : thm := BWordOps2.WORD_SHL_LSB

-- WordOps3
unsafe def WORD_SHL_WORD : thm := BWordOps3.WORD_SHL_WORD
unsafe def WORD_SHL_AS_IWORD : thm := BWordOps3.WORD_SHL_AS_IWORD
unsafe def WORD_SHL_IWORD : thm := BWordOps3.WORD_SHL_IWORD
unsafe def WORD_MUL_EXPAND : thm := BWordOps3.WORD_MUL_EXPAND
unsafe def word_ushr : thm := BWordOps3.word_ushr
unsafe def VAL_WORD_USHR : thm := BWordOps3.VAL_WORD_USHR
unsafe def WORD_USHR_EQ_0 : thm := BWordOps3.WORD_USHR_EQ_0
unsafe def BIT_WORD_USHR : thm := BWordOps3.BIT_WORD_USHR
unsafe def WORD_USHR_WORD_OF_BITS : thm := BWordOps3.WORD_USHR_WORD_OF_BITS
unsafe def WORD_USHR_0 : thm := BWordOps3.WORD_USHR_0
unsafe def WORD_USHR_ZERO : thm := BWordOps3.WORD_USHR_ZERO
unsafe def WORD_USHR_COMPOSE : thm := BWordOps3.WORD_USHR_COMPOSE
unsafe def WORD_USHR_MSB_ALT : thm := BWordOps3.WORD_USHR_MSB_ALT
unsafe def WORD_USHR_MSB : thm := BWordOps3.WORD_USHR_MSB
unsafe def WORD_USHR_MSB_EQ : thm := BWordOps3.WORD_USHR_MSB_EQ
unsafe def WORD_POPCOUNT_SHL : thm := BWordOps3.WORD_POPCOUNT_SHL
unsafe def WORD_POPCOUNT_USHR : thm := BWordOps3.WORD_POPCOUNT_USHR
unsafe def word_ishr : thm := BWordOps3.word_ishr
unsafe def IVAL_WORD_ISHR : thm := BWordOps3.IVAL_WORD_ISHR
unsafe def WORD_ISHR_EQ_0 : thm := BWordOps3.WORD_ISHR_EQ_0
unsafe def BIT_WORD_ISHR : thm := BWordOps3.BIT_WORD_ISHR
unsafe def WORD_ISHR_WORD_OF_BITS : thm := BWordOps3.WORD_ISHR_WORD_OF_BITS
unsafe def WORD_ISHR_0 : thm := BWordOps3.WORD_ISHR_0
unsafe def WORD_ISHR_ZERO : thm := BWordOps3.WORD_ISHR_ZERO
unsafe def WORD_ISHR_COMPOSE : thm := BWordOps3.WORD_ISHR_COMPOSE
unsafe def WORD_ISHR_UNIQUE : thm := BWordOps3.WORD_ISHR_UNIQUE
unsafe def IVAL_WORD_ISHR_SHL_UNIQUE : thm := BWordOps3.IVAL_WORD_ISHR_SHL_UNIQUE
unsafe def word_ror : thm := BWordOps3.word_ror
unsafe def word_rol : thm := BWordOps3.word_rol
unsafe def WORD_ROR_ROL_GEN : thm := BWordOps3.WORD_ROR_ROL_GEN
unsafe def WORD_ROL_ROR_GEN : thm := BWordOps3.WORD_ROL_ROR_GEN
unsafe def WORD_ROR_PERIODIC : thm := BWordOps3.WORD_ROR_PERIODIC
unsafe def WORD_ROR_MOD : thm := BWordOps3.WORD_ROR_MOD
unsafe def WORD_ROR_EQ_SELF : thm := BWordOps3.WORD_ROR_EQ_SELF
unsafe def WORD_ROR_ZERO : thm := BWordOps3.WORD_ROR_ZERO
unsafe def WORD_ROL_PERIODIC : thm := BWordOps3.WORD_ROL_PERIODIC
unsafe def WORD_ROL_MOD : thm := BWordOps3.WORD_ROL_MOD
unsafe def WORD_ROL_EQ_SELF : thm := BWordOps3.WORD_ROL_EQ_SELF
unsafe def WORD_ROL_ZERO : thm := BWordOps3.WORD_ROL_ZERO
unsafe def WORD_ROR_ROL : thm := BWordOps3.WORD_ROR_ROL
unsafe def WORD_ROL_ROR : thm := BWordOps3.WORD_ROL_ROR
unsafe def WORD_ROR_SHIFTS : thm := BWordOps3.WORD_ROR_SHIFTS
unsafe def WORD_ROL_SHIFTS : thm := BWordOps3.WORD_ROL_SHIFTS
unsafe def BIT_WORD_ROR : thm := BWordOps3.BIT_WORD_ROR
unsafe def BIT_WORD_ROL : thm := BWordOps3.BIT_WORD_ROL
unsafe def WORD_ROR_COMPOSE : thm := BWordOps3.WORD_ROR_COMPOSE
unsafe def WORD_ROL_COMPOSE : thm := BWordOps3.WORD_ROL_COMPOSE
unsafe def VAL_WORD_ROR : thm := BWordOps3.VAL_WORD_ROR
unsafe def VAL_WORD_ROL : thm := BWordOps3.VAL_WORD_ROL
unsafe def word_ule : thm := BWordOps3.word_ule
unsafe def word_uge : thm := BWordOps3.word_uge
unsafe def word_ult : thm := BWordOps3.word_ult
unsafe def word_ugt : thm := BWordOps3.word_ugt
unsafe def word_ile : thm := BWordOps3.word_ile
unsafe def word_ige : thm := BWordOps3.word_ige
unsafe def word_ilt : thm := BWordOps3.word_ilt
unsafe def word_igt : thm := BWordOps3.word_igt
unsafe def WORD_ULT : thm := BWordOps3.WORD_ULT
unsafe def WORD_ULE : thm := BWordOps3.WORD_ULE
unsafe def WORD_UGT : thm := BWordOps3.WORD_UGT
unsafe def WORD_UGE : thm := BWordOps3.WORD_UGE
unsafe def WORD_ILT : thm := BWordOps3.WORD_ILT
unsafe def WORD_ILE : thm := BWordOps3.WORD_ILE
unsafe def WORD_IGT : thm := BWordOps3.WORD_IGT
unsafe def WORD_IGE : thm := BWordOps3.WORD_IGE

-- WordRule
unsafe def WORD_VAL_CONG_CONV : HolCore.Equal.ioconv := fun t => BWordRule.WORD_VAL_CONG_CONV t
unsafe def WORD_RULE : term → IO (Except String thm) := fun t => (BWordRule.WORD_RULE t).run

-- WordBitwise
unsafe def WORD_BITWISE_RULE : term → IO (Except String thm) := fun t => (BWordBitwise.WORD_BITWISE_RULE t).run
unsafe def WORD_BITWISE_TAC : HolCore.Tactics.tactic := fun g => BWordBitwise.WORD_BITWISE_TAC g

-- WordArith
unsafe def WORD_ARITH : term → IO (Except String thm) := fun t => (BWordArith.WORD_ARITH t).run
unsafe def WORD_ARITH_TAC : HolCore.Tactics.tactic := fun g => BWordArith.WORD_ARITH_TAC g

-- ValExpand
unsafe def EMPOWER_CONV : HolCore.Equal.ioconv := fun t => BValExpand.EMPOWER_CONV t
unsafe def VAL_EXPAND_CONV : HolCore.Equal.ioconv := fun t => BValExpand.VAL_EXPAND_CONV t

-- ZxSx
unsafe def word_zx : thm := BZxSx.word_zx
unsafe def VAL_WORD_ZX_GEN : thm := BZxSx.VAL_WORD_ZX_GEN
unsafe def VAL_WORD_ZX : thm := BZxSx.VAL_WORD_ZX
unsafe def WORD_ZX_ZX : thm := BZxSx.WORD_ZX_ZX
unsafe def WORD_ZX_0 : thm := BZxSx.WORD_ZX_0
unsafe def WORD_ZX_TRIVIAL : thm := BZxSx.WORD_ZX_TRIVIAL
unsafe def WORD_ZX_WORD : thm := BZxSx.WORD_ZX_WORD
unsafe def WORD_ZX_WORD_SIMPLE : thm := BZxSx.WORD_ZX_WORD_SIMPLE
unsafe def WORD_ZX_1 : thm := BZxSx.WORD_ZX_1
unsafe def WORD_ZX_BITVAL : thm := BZxSx.WORD_ZX_BITVAL
unsafe def BIT_WORD_ZX : thm := BZxSx.BIT_WORD_ZX
unsafe def WORD_ZX_AND : thm := BZxSx.WORD_ZX_AND
unsafe def WORD_ZX_OR : thm := BZxSx.WORD_ZX_OR
unsafe def WORD_ZX_XOR : thm := BZxSx.WORD_ZX_XOR
unsafe def WORD_ZX_NOT : thm := BZxSx.WORD_ZX_NOT
unsafe def WORD_ZX_ADD : thm := BZxSx.WORD_ZX_ADD
unsafe def WORD_ZX_MUL : thm := BZxSx.WORD_ZX_MUL
unsafe def WORD_ZX_NEG : thm := BZxSx.WORD_ZX_NEG
unsafe def WORD_ZX_SUB : thm := BZxSx.WORD_ZX_SUB
unsafe def WORD_ZX_SHL : thm := BZxSx.WORD_ZX_SHL
unsafe def word_sx : thm := BZxSx.word_sx
unsafe def IVAL_WORD_SX : thm := BZxSx.IVAL_WORD_SX
unsafe def WORD_SX_SX : thm := BZxSx.WORD_SX_SX
unsafe def WORD_SX_0 : thm := BZxSx.WORD_SX_0
unsafe def WORD_SX_TRIVIAL : thm := BZxSx.WORD_SX_TRIVIAL
unsafe def WORD_SX_ZX : thm := BZxSx.WORD_SX_ZX
unsafe def word_sxfrom : thm := BZxSx.word_sxfrom
unsafe def BIT_WORD_SXFROM : thm := BZxSx.BIT_WORD_SXFROM
unsafe def IVAL_WORD_SXFROM_UNIQUE : thm := BZxSx.IVAL_WORD_SXFROM_UNIQUE
unsafe def word_cand : thm := BZxSx.word_cand
unsafe def word_cor : thm := BZxSx.word_cor
unsafe def WORD_CAND : thm := BZxSx.WORD_CAND
unsafe def WORD_COR : thm := BZxSx.WORD_COR
unsafe def WORD_CAND_NE_0 : thm := BZxSx.WORD_CAND_NE_0
unsafe def WORD_COR_NE_0 : thm := BZxSx.WORD_COR_NE_0
unsafe def WORD_CAND_EQ_0 : thm := BZxSx.WORD_CAND_EQ_0
unsafe def WORD_COR_EQ_0 : thm := BZxSx.WORD_COR_EQ_0
unsafe def VAL_WORD_CAND : thm := BZxSx.VAL_WORD_CAND
unsafe def VAL_WORD_COR : thm := BZxSx.VAL_WORD_COR
unsafe def BIT_WORD_CAND : thm := BZxSx.BIT_WORD_CAND
unsafe def BIT_WORD_COR : thm := BZxSx.BIT_WORD_COR

-- JoinSubword
unsafe def word_join : thm := BJoinSubword.word_join
unsafe def VAL_WORD_JOIN : thm := BJoinSubword.VAL_WORD_JOIN
unsafe def BIT_WORD_JOIN_GEN : thm := BJoinSubword.BIT_WORD_JOIN_GEN
unsafe def BIT_WORD_JOIN : thm := BJoinSubword.BIT_WORD_JOIN
unsafe def VAL_WORD_JOIN_SIMPLE : thm := BJoinSubword.VAL_WORD_JOIN_SIMPLE
unsafe def WORD_JOIN_NOT : thm := BJoinSubword.WORD_JOIN_NOT
unsafe def word_subword : thm := BJoinSubword.word_subword
unsafe def VAL_WORD_SUBWORD : thm := BJoinSubword.VAL_WORD_SUBWORD
unsafe def VAL_WORD_SUBWORD_DIMINDEX : thm := BJoinSubword.VAL_WORD_SUBWORD_DIMINDEX
unsafe def VAL_WORD_SUBWORD_SIMPLE : thm := BJoinSubword.VAL_WORD_SUBWORD_SIMPLE
unsafe def WORD_SUBWORD_WORD : thm := BJoinSubword.WORD_SUBWORD_WORD
unsafe def BIT_WORD_SUBWORD : thm := BJoinSubword.BIT_WORD_SUBWORD
unsafe def WORD_SUBWORD_0 : thm := BJoinSubword.WORD_SUBWORD_0
unsafe def WORD_SUBWORD_JOIN_SELF : thm := BJoinSubword.WORD_SUBWORD_JOIN_SELF
unsafe def VAL_WORD_SUBWORD_JOIN : thm := BJoinSubword.VAL_WORD_SUBWORD_JOIN
unsafe def WORD_SUBWORD_JOIN_LOWER : thm := BJoinSubword.WORD_SUBWORD_JOIN_LOWER
unsafe def WORD_SUBWORD_JOIN_UPPER : thm := BJoinSubword.WORD_SUBWORD_JOIN_UPPER
unsafe def WORD_SUBWORD_SUBWORD : thm := BJoinSubword.WORD_SUBWORD_SUBWORD
unsafe def WORD_SUBWORD_TRIVIAL : thm := BJoinSubword.WORD_SUBWORD_TRIVIAL
unsafe def WORD_SUBWORD_DIMINDEX : thm := BJoinSubword.WORD_SUBWORD_DIMINDEX
unsafe def WORD_ZX_SUBWORD : thm := BJoinSubword.WORD_ZX_SUBWORD
unsafe def VAL_WORD_SUBWORD_JOIN_FULL : thm := BJoinSubword.VAL_WORD_SUBWORD_JOIN_FULL
unsafe def WORD_SUBWORD_JOIN_AS_USHR : thm := BJoinSubword.WORD_SUBWORD_JOIN_AS_USHR
unsafe def WORD_SUBWORD_JOIN_AS_SHL : thm := BJoinSubword.WORD_SUBWORD_JOIN_AS_SHL
unsafe def WORD_SUBWORD_AS_USHR : thm := BJoinSubword.WORD_SUBWORD_AS_USHR
unsafe def WORD_USHR_AS_SUBWORD : thm := BJoinSubword.WORD_USHR_AS_SUBWORD
unsafe def WORD_SHL_SUBWORD : thm := BJoinSubword.WORD_SHL_SUBWORD
unsafe def WORD_SUBWORD_AND : thm := BJoinSubword.WORD_SUBWORD_AND
unsafe def WORD_SUBWORD_OR : thm := BJoinSubword.WORD_SUBWORD_OR
unsafe def WORD_SUBWORD_XOR : thm := BJoinSubword.WORD_SUBWORD_XOR
unsafe def WORD_SUBWORD_NOT : thm := BJoinSubword.WORD_SUBWORD_NOT
unsafe def WORD_SUBWORD_ADD : thm := BJoinSubword.WORD_SUBWORD_ADD
unsafe def WORD_SUBWORD_AS_IWORD : thm := BJoinSubword.WORD_SUBWORD_AS_IWORD
unsafe def WORD_SUBWORD_IWORD : thm := BJoinSubword.WORD_SUBWORD_IWORD
unsafe def WORD_SUBWORD_AS_USHR_SHL : thm := BJoinSubword.WORD_SUBWORD_AS_USHR_SHL
unsafe def WORD_SXFROM_SUBWORD_AS_ISHR_SHL : thm := BJoinSubword.WORD_SXFROM_SUBWORD_AS_ISHR_SHL
unsafe def VAL_EXPAND_SUBWORDS : thm := BJoinSubword.VAL_EXPAND_SUBWORDS
unsafe def VAL_SUBWORDS_EQ : thm := BJoinSubword.VAL_SUBWORDS_EQ
unsafe def WORD_SUBWORDS_EQ : thm := BJoinSubword.WORD_SUBWORDS_EQ

-- InsertDup
unsafe def word_insert : thm := BInsertDup.word_insert
unsafe def BIT_WORD_INSERT : thm := BInsertDup.BIT_WORD_INSERT
unsafe def WORD_SUBWORD_INSERT_OUTER : thm := BInsertDup.WORD_SUBWORD_INSERT_OUTER
unsafe def WORD_SUBWORD_INSERT_INNER : thm := BInsertDup.WORD_SUBWORD_INSERT_INNER
unsafe def word_duplicate : thm := BInsertDup.word_duplicate
unsafe def BIT_WORD_DUPLICATE : thm := BInsertDup.BIT_WORD_DUPLICATE
unsafe def WORD_DUPLICATE_REFL : thm := BInsertDup.WORD_DUPLICATE_REFL
unsafe def WORD_DUPLICATE_DOUBLE : thm := BInsertDup.WORD_DUPLICATE_DOUBLE
unsafe def WORD_SUBWORD_DUPLICATE : thm := BInsertDup.WORD_SUBWORD_DUPLICATE
unsafe def WORD_SUBWORD_DUPLICATE_DUPLICATE : thm := BInsertDup.WORD_SUBWORD_DUPLICATE_DUPLICATE
unsafe def VAL_WORD_DUPLICATE : thm := BInsertDup.VAL_WORD_DUPLICATE
unsafe def WORD_DUPLICATE : thm := BInsertDup.WORD_DUPLICATE
unsafe def WORD_SUBWORD_ZX : thm := BInsertDup.WORD_SUBWORD_ZX
unsafe def WORD_SUBWORD_ZX_TRIVIAL : thm := BInsertDup.WORD_SUBWORD_ZX_TRIVIAL
unsafe def WORD_SIMPLE_SUBWORD_CONV : HolCore.Equal.ioconv := fun t => BInsertDup.WORD_SIMPLE_SUBWORD_CONV t

-- BitRec
unsafe def BIT_WORD_ADD : thm := BBitRec.BIT_WORD_ADD
unsafe def BIT_WORD_SUB : thm := BBitRec.BIT_WORD_SUB
unsafe def BIT_WORD_NEG : thm := BBitRec.BIT_WORD_NEG
unsafe def BIT_WORD_ADD_CLAUSES : thm := BBitRec.BIT_WORD_ADD_CLAUSES
unsafe def BIT_WORD_SUB_CLAUSES : thm := BBitRec.BIT_WORD_SUB_CLAUSES
unsafe def BIT_WORD_NEG_CLAUSES : thm := BBitRec.BIT_WORD_NEG_CLAUSES
unsafe def LE_VAL_MOD_STEP : thm := BBitRec.LE_VAL_MOD_STEP
unsafe def LT_VAL_MOD_STEP : thm := BBitRec.LT_VAL_MOD_STEP

-- Misc1
unsafe def WORD_ADD_0 : thm := BMisc1.WORD_ADD_0
unsafe def WORD_ADD_SYM : thm := BMisc1.WORD_ADD_SYM
unsafe def WORD_ADD_ASSOC : thm := BMisc1.WORD_ADD_ASSOC
unsafe def WORD_ADD_AC : thm := BMisc1.WORD_ADD_AC
unsafe def WORD_MUL_0 : thm := BMisc1.WORD_MUL_0
unsafe def WORD_MUL_SYM : thm := BMisc1.WORD_MUL_SYM
unsafe def WORD_MUL_ASSOC : thm := BMisc1.WORD_MUL_ASSOC
unsafe def WORD_MUL_AC : thm := BMisc1.WORD_MUL_AC
unsafe def WORD_SUB_0 : thm := BMisc1.WORD_SUB_0
unsafe def WORD_SUB_LZERO : thm := BMisc1.WORD_SUB_LZERO
unsafe def WORD_SUB_EQ_0 : thm := BMisc1.WORD_SUB_EQ_0
unsafe def WORD_SUB_REFL : thm := BMisc1.WORD_SUB_REFL
unsafe def WORD_NEG_NEG : thm := BMisc1.WORD_NEG_NEG
unsafe def WORD_NEG_0 : thm := BMisc1.WORD_NEG_0
unsafe def WORD_NEG_SUB : thm := BMisc1.WORD_NEG_SUB
unsafe def WORD_NEG_EQ_0 : thm := BMisc1.WORD_NEG_EQ_0
unsafe def WORD_NOT_NOT : thm := BMisc1.WORD_NOT_NOT
unsafe def WORD_AND_REFL : thm := BMisc1.WORD_AND_REFL
unsafe def WORD_AND_0 : thm := BMisc1.WORD_AND_0
unsafe def WORD_AND_NOT0 : thm := BMisc1.WORD_AND_NOT0
unsafe def WORD_AND_SYM : thm := BMisc1.WORD_AND_SYM
unsafe def WORD_AND_ASSOC : thm := BMisc1.WORD_AND_ASSOC
unsafe def WORD_OR_REFL : thm := BMisc1.WORD_OR_REFL
unsafe def WORD_OR_0 : thm := BMisc1.WORD_OR_0
unsafe def WORD_OR_NOT0 : thm := BMisc1.WORD_OR_NOT0
unsafe def WORD_OR_SYM : thm := BMisc1.WORD_OR_SYM
unsafe def WORD_OR_ASSOC : thm := BMisc1.WORD_OR_ASSOC
unsafe def WORD_OR_EQ_0 : thm := BMisc1.WORD_OR_EQ_0
unsafe def WORD_NOT_AND : thm := BMisc1.WORD_NOT_AND
unsafe def WORD_NOT_OR : thm := BMisc1.WORD_NOT_OR
unsafe def WORD_XOR_EQ_0 : thm := BMisc1.WORD_XOR_EQ_0
unsafe def WORD_XOR_0 : thm := BMisc1.WORD_XOR_0
unsafe def WORD_XOR_NOT : thm := BMisc1.WORD_XOR_NOT
unsafe def WORD_XOR_NOT0 : thm := BMisc1.WORD_XOR_NOT0
unsafe def WORD_XOR_REFL : thm := BMisc1.WORD_XOR_REFL
unsafe def WORD_XOR_SYM : thm := BMisc1.WORD_XOR_SYM
unsafe def WORD_XOR_ASSOC : thm := BMisc1.WORD_XOR_ASSOC
unsafe def WORD_AND_1 : thm := BMisc1.WORD_AND_1
unsafe def WORD_AND_1_BITVAL : thm := BMisc1.WORD_AND_1_BITVAL
unsafe def WORD_NOT_NEG : thm := BMisc1.WORD_NOT_NEG
unsafe def WORD_NOT_SUB : thm := BMisc1.WORD_NOT_SUB
unsafe def WORD_NOT_ADD : thm := BMisc1.WORD_NOT_ADD
unsafe def VAL_WORD_SUB_EQ_0 : thm := BMisc1.VAL_WORD_SUB_EQ_0
unsafe def VAL_EQ_MAX_ALT : thm := BMisc1.VAL_EQ_MAX_ALT
unsafe def VAL_EQ_MAX : thm := BMisc1.VAL_EQ_MAX
unsafe def VAL_EQ_MAX_MASK : thm := BMisc1.VAL_EQ_MAX_MASK
unsafe def VAL_WORD_OR_EQ_0 : thm := BMisc1.VAL_WORD_OR_EQ_0
unsafe def VAL_WORD_AND_EQ_MAX : thm := BMisc1.VAL_WORD_AND_EQ_MAX
unsafe def WORD_SHL_AND : thm := BMisc1.WORD_SHL_AND
unsafe def WORD_USHR_AND : thm := BMisc1.WORD_USHR_AND
unsafe def WORD_SHL_OR : thm := BMisc1.WORD_SHL_OR
unsafe def WORD_USHR_OR : thm := BMisc1.WORD_USHR_OR
unsafe def WORD_SHL_XOR : thm := BMisc1.WORD_SHL_XOR
unsafe def WORD_USHR_XOR : thm := BMisc1.WORD_USHR_XOR
unsafe def WORD_ADD_XOR_GEN : thm := BMisc1.WORD_ADD_XOR_GEN
unsafe def WORD_ADD_OR_GEN : thm := BMisc1.WORD_ADD_OR_GEN
unsafe def WORD_OR_XOR_GEN : thm := BMisc1.WORD_OR_XOR_GEN
unsafe def WORD_ADD_OR_EQ : thm := BMisc1.WORD_ADD_OR_EQ
unsafe def WORD_OR_XOR_EQ : thm := BMisc1.WORD_OR_XOR_EQ
unsafe def WORD_ADD_OR : thm := BMisc1.WORD_ADD_OR
unsafe def WORD_OR_XOR : thm := BMisc1.WORD_OR_XOR
unsafe def WORD_ADD_XOR : thm := BMisc1.WORD_ADD_XOR
unsafe def WORD_POPCOUNT_ADD_DISJOINT : thm := BMisc1.WORD_POPCOUNT_ADD_DISJOINT
unsafe def WORD_POPCOUNT_XOR_AND : thm := BMisc1.WORD_POPCOUNT_XOR_AND
unsafe def WORD_POPCOUNT_OR_AND : thm := BMisc1.WORD_POPCOUNT_OR_AND
unsafe def WORD_POPCOUNT_XOR_AND2 : thm := BMisc1.WORD_POPCOUNT_XOR_AND2
unsafe def WORD_POPCOUNT_XOR : thm := BMisc1.WORD_POPCOUNT_XOR
unsafe def WORD_SUB_XOR : thm := BMisc1.WORD_SUB_XOR
unsafe def WORD_XOR_SUB : thm := BMisc1.WORD_XOR_SUB
unsafe def WORD_SUB_MASK_WORD : thm := BMisc1.WORD_SUB_MASK_WORD
unsafe def WORD_XOR_MASK_WORD : thm := BMisc1.WORD_XOR_MASK_WORD
unsafe def WORD_XOR_INT_MIN : thm := BMisc1.WORD_XOR_INT_MIN
unsafe def WORD_BITVAL_NOT : thm := BMisc1.WORD_BITVAL_NOT
unsafe def IVAL_WORD_NOT : thm := BMisc1.IVAL_WORD_NOT
unsafe def BIT_WORD_NEG_CASES : thm := BMisc1.BIT_WORD_NEG_CASES
unsafe def BIT_WORD_ADD_1_CASES : thm := BMisc1.BIT_WORD_ADD_1_CASES
unsafe def BIT_WORD_SUB_1_CASES : thm := BMisc1.BIT_WORD_SUB_1_CASES
unsafe def BIT_WORD_AND_NEG : thm := BMisc1.BIT_WORD_AND_NEG
unsafe def BIT_WORD_OR_NEG : thm := BMisc1.BIT_WORD_OR_NEG
unsafe def BIT_WORD_XOR_NEG : thm := BMisc1.BIT_WORD_XOR_NEG
unsafe def BIT_WORD_AND_ADD_1 : thm := BMisc1.BIT_WORD_AND_ADD_1
unsafe def BIT_WORD_AND_SUB_1 : thm := BMisc1.BIT_WORD_AND_SUB_1
unsafe def BIT_WORD_OR_ADD_1 : thm := BMisc1.BIT_WORD_OR_ADD_1
unsafe def BIT_WORD_OR_SUB_1 : thm := BMisc1.BIT_WORD_OR_SUB_1
unsafe def BIT_WORD_XOR_ADD_1 : thm := BMisc1.BIT_WORD_XOR_ADD_1
unsafe def BIT_WORD_XOR_SUB_1 : thm := BMisc1.BIT_WORD_XOR_SUB_1
unsafe def BIT_WORD_AND_NOT_SUB_1 : thm := BMisc1.BIT_WORD_AND_NOT_SUB_1
unsafe def BIT_WORD_AND_NOT_ADD_1 : thm := BMisc1.BIT_WORD_AND_NOT_ADD_1
unsafe def WORD_OR_SHL_USHR : thm := BMisc1.WORD_OR_SHL_USHR
unsafe def WORD_OR_USHR_SHL : thm := BMisc1.WORD_OR_USHR_SHL
unsafe def WORD_ADD_SHL_USHR : thm := BMisc1.WORD_ADD_SHL_USHR
unsafe def WORD_ADD_USHR_SHL : thm := BMisc1.WORD_ADD_USHR_SHL

-- Masks
unsafe def WORD_MASK_ALT : thm := BMasks.WORD_MASK_ALT
unsafe def WORD_MASK : thm := BMasks.WORD_MASK
unsafe def BIT_WORD_MASK : thm := BMasks.BIT_WORD_MASK
unsafe def WORD_ISHR_MSB : thm := BMasks.WORD_ISHR_MSB
unsafe def WORD_NOT_MASK : thm := BMasks.WORD_NOT_MASK
unsafe def WORD_AND_MASK : thm := BMasks.WORD_AND_MASK
unsafe def WORD_OR_MASK : thm := BMasks.WORD_OR_MASK
unsafe def WORD_XOR_MASK : thm := BMasks.WORD_XOR_MASK
unsafe def WORD_NEG_AND_MASK : thm := BMasks.WORD_NEG_AND_MASK
unsafe def WORD_AND_MASKS : thm := BMasks.WORD_AND_MASKS
unsafe def WORD_OR_MASKS : thm := BMasks.WORD_OR_MASKS
unsafe def WORD_XOR_MASKS : thm := BMasks.WORD_XOR_MASKS
unsafe def WORD_AND_CONDITIONS : thm := BMasks.WORD_AND_CONDITIONS
unsafe def WORD_OR_CONDITIONS : thm := BMasks.WORD_OR_CONDITIONS
unsafe def WORD_XOR_CONDITIONS : thm := BMasks.WORD_XOR_CONDITIONS
unsafe def VAL_WORD_MASK : thm := BMasks.VAL_WORD_MASK
unsafe def IVAL_WORD_MASK : thm := BMasks.IVAL_WORD_MASK
unsafe def INT_VAL_WORD_MASK : thm := BMasks.INT_VAL_WORD_MASK
unsafe def REAL_VAL_WORD_MASK : thm := BMasks.REAL_VAL_WORD_MASK
unsafe def WORD_MUL_EXPAND_ALT : thm := BMasks.WORD_MUL_EXPAND_ALT
unsafe def WORD_SX_ZX_GEN : thm := BMasks.WORD_SX_ZX_GEN
unsafe def BIT_WORD_SX : thm := BMasks.BIT_WORD_SX
unsafe def VAL_WORD_AND_MASK : thm := BMasks.VAL_WORD_AND_MASK
unsafe def IVAL_WORD_AND_MASK : thm := BMasks.IVAL_WORD_AND_MASK
unsafe def VAL_WORD_AND_MASK_WORD : thm := BMasks.VAL_WORD_AND_MASK_WORD
unsafe def WORD_AND_MASK_WORD : thm := BMasks.WORD_AND_MASK_WORD
unsafe def VAL_WORD_AND_NOT_MASK_WORD : thm := BMasks.VAL_WORD_AND_NOT_MASK_WORD
unsafe def WORD_AND_NOT_MASK_WORD : thm := BMasks.WORD_AND_NOT_MASK_WORD
unsafe def WORD_BITMASK : thm := BMasks.WORD_BITMASK
unsafe def MASK_WORD_SUB : thm := BMasks.MASK_WORD_SUB
unsafe def WORD_AND_MASK_WORDS : thm := BMasks.WORD_AND_MASK_WORDS
unsafe def WORD_OR_MASK_WORDS : thm := BMasks.WORD_OR_MASK_WORDS
unsafe def WORD_USHR_MASK_WORD : thm := BMasks.WORD_USHR_MASK_WORD

-- ClzCtz
unsafe def word_ctz : thm := BClzCtz.word_ctz
unsafe def word_clz : thm := BClzCtz.word_clz
unsafe def WORD_CLZ : thm := BClzCtz.WORD_CLZ
unsafe def WORD_CTZ_0 : thm := BClzCtz.WORD_CTZ_0
unsafe def WORD_LE_CTZ : thm := BClzCtz.WORD_LE_CTZ
unsafe def WORD_CTZ_LE : thm := BClzCtz.WORD_CTZ_LE
unsafe def WORD_CTZ_LE_DIMINDEX : thm := BClzCtz.WORD_CTZ_LE_DIMINDEX
unsafe def WORD_CTZ_LBOUND : thm := BClzCtz.WORD_CTZ_LBOUND
unsafe def WORD_CTZ_EQ_DIMINDEX : thm := BClzCtz.WORD_CTZ_EQ_DIMINDEX
unsafe def WORD_CTZ_LT_DIMINDEX : thm := BClzCtz.WORD_CTZ_LT_DIMINDEX
unsafe def WORD_CTZ_EQ_0 : thm := BClzCtz.WORD_CTZ_EQ_0
unsafe def WORD_CTZ_UNIQUE_GEN : thm := BClzCtz.WORD_CTZ_UNIQUE_GEN
unsafe def WORD_CTZ_UNIQUE : thm := BClzCtz.WORD_CTZ_UNIQUE
unsafe def WORD_LE_CTZ_VAL_MOD : thm := BClzCtz.WORD_LE_CTZ_VAL_MOD
unsafe def WORD_LE_CTZ_VAL : thm := BClzCtz.WORD_LE_CTZ_VAL
unsafe def WORD_CTZ_UNIQUE_VAL : thm := BClzCtz.WORD_CTZ_UNIQUE_VAL
unsafe def WORD_CLZ_0 : thm := BClzCtz.WORD_CLZ_0
unsafe def WORD_SIZE_SUB_CLZ : thm := BClzCtz.WORD_SIZE_SUB_CLZ
unsafe def WORD_CLZ_LE_DIMINDEX : thm := BClzCtz.WORD_CLZ_LE_DIMINDEX
unsafe def WORD_LE_CLZ : thm := BClzCtz.WORD_LE_CLZ
unsafe def WORD_CLZ_LE : thm := BClzCtz.WORD_CLZ_LE
unsafe def WORD_CLZ_LBOUND_ALT : thm := BClzCtz.WORD_CLZ_LBOUND_ALT
unsafe def WORD_CLZ_LBOUND : thm := BClzCtz.WORD_CLZ_LBOUND
unsafe def WORD_CLZ_EQ_DIMINDEX : thm := BClzCtz.WORD_CLZ_EQ_DIMINDEX
unsafe def WORD_CLZ_LT_DIMINDEX : thm := BClzCtz.WORD_CLZ_LT_DIMINDEX
unsafe def WORD_CLZ_EQ_0 : thm := BClzCtz.WORD_CLZ_EQ_0
unsafe def WORD_CLZ_DECOMP : thm := BClzCtz.WORD_CLZ_DECOMP
unsafe def WORD_CLZ_UNIQUE_GEN : thm := BClzCtz.WORD_CLZ_UNIQUE_GEN
unsafe def WORD_CLZ_UNIQUE : thm := BClzCtz.WORD_CLZ_UNIQUE
unsafe def WORD_LE_CLZ_VAL : thm := BClzCtz.WORD_LE_CLZ_VAL
unsafe def WORD_LE_CLZ_VAL_MULT : thm := BClzCtz.WORD_LE_CLZ_VAL_MULT
unsafe def WORD_LE_CLZ_VAL_DIV : thm := BClzCtz.WORD_LE_CLZ_VAL_DIV
unsafe def VAL_BOUND_CLZ : thm := BClzCtz.VAL_BOUND_CLZ
unsafe def WORD_CLZ_UNIQUE_VAL : thm := BClzCtz.WORD_CLZ_UNIQUE_VAL
unsafe def WORD_CTZ_BIT : thm := BClzCtz.WORD_CTZ_BIT
unsafe def WORD_CLZ_BIT : thm := BClzCtz.WORD_CLZ_BIT
unsafe def WORD_CTZ_MASK_WORD : thm := BClzCtz.WORD_CTZ_MASK_WORD
unsafe def WORD_CLZ_MASK_WORD : thm := BClzCtz.WORD_CLZ_MASK_WORD
unsafe def WORD_AND_NEG_CTZ : thm := BClzCtz.WORD_AND_NEG_CTZ
unsafe def WORD_XOR_SUB_1_CTZ : thm := BClzCtz.WORD_XOR_SUB_1_CTZ
unsafe def WORD_AND_NOT_SUB_1_CTZ : thm := BClzCtz.WORD_AND_NOT_SUB_1_CTZ
unsafe def WORD_CTZ_EMULATION_REV : thm := BClzCtz.WORD_CTZ_EMULATION_REV
unsafe def WORD_CTZ_EMULATION_AND_NEG_REV : thm := BClzCtz.WORD_CTZ_EMULATION_AND_NEG_REV
unsafe def WORD_CTZ_EMULATION_XOR_SUB_1_REV : thm := BClzCtz.WORD_CTZ_EMULATION_XOR_SUB_1_REV
unsafe def WORD_CTZ_EMULATION : thm := BClzCtz.WORD_CTZ_EMULATION
unsafe def WORD_CTZ_EMULATION_AND_NEG : thm := BClzCtz.WORD_CTZ_EMULATION_AND_NEG
unsafe def WORD_CTZ_EMULATION_XOR_SUB_1 : thm := BClzCtz.WORD_CTZ_EMULATION_XOR_SUB_1
unsafe def WORD_CLZ_IMP : thm := BClzCtz.WORD_CLZ_IMP
unsafe def WORD_CLZ_OR : thm := BClzCtz.WORD_CLZ_OR
unsafe def WORD_CTZ_IMP : thm := BClzCtz.WORD_CTZ_IMP
unsafe def WORD_CTZ_OR : thm := BClzCtz.WORD_CTZ_OR
unsafe def WORD_CLZ_MONO : thm := BClzCtz.WORD_CLZ_MONO
unsafe def WORD_CTZ_EMULATION_POPCOUNT : thm := BClzCtz.WORD_CTZ_EMULATION_POPCOUNT

-- Reverse
unsafe def word_reversefields : thm := BReverse.word_reversefields
unsafe def BIT_WORD_REVERSEFIELDS : thm := BReverse.BIT_WORD_REVERSEFIELDS
unsafe def WORD_REVERSEFIELDS_REVERSEFIELDS : thm := BReverse.WORD_REVERSEFIELDS_REVERSEFIELDS
unsafe def BIT_REVERSEFIELDS_1 : thm := BReverse.BIT_REVERSEFIELDS_1
unsafe def WORD_CTZ_REVERSEFIELDS : thm := BReverse.WORD_CTZ_REVERSEFIELDS
unsafe def WORD_CLZ_REVERSEFIELDS : thm := BReverse.WORD_CLZ_REVERSEFIELDS
unsafe def WORD_CLZ_USHR : thm := BReverse.WORD_CLZ_USHR
unsafe def WORD_SHL_AS_USHR : thm := BReverse.WORD_SHL_AS_USHR
unsafe def WORD_USHR_AS_SHL : thm := BReverse.WORD_USHR_AS_SHL
unsafe def WORD_CTZ_SHL : thm := BReverse.WORD_CTZ_SHL
unsafe def word_bytereverse : thm := BReverse.word_bytereverse
unsafe def BIT_WORD_BYTEREVERSE : thm := BReverse.BIT_WORD_BYTEREVERSE
unsafe def WORD_BYTEREVERSE_BYTEREVERSE : thm := BReverse.WORD_BYTEREVERSE_BYTEREVERSE
unsafe def WORD_BYTEREVERSE_REVERSEFIELDS : thm := BReverse.WORD_BYTEREVERSE_REVERSEFIELDS
unsafe def word_pmul : thm := BReverse.word_pmul
unsafe def BIT_WORD_PMUL_ALT : thm := BReverse.BIT_WORD_PMUL_ALT
unsafe def BIT_WORD_PMUL : thm := BReverse.BIT_WORD_PMUL
unsafe def BITVAL_BIT_WORD_PMUL : thm := BReverse.BITVAL_BIT_WORD_PMUL
unsafe def WORD_PMUL_0 : thm := BReverse.WORD_PMUL_0
unsafe def WORD_PMUL_XOR : thm := BReverse.WORD_PMUL_XOR
unsafe def WORD_PMUL_ZX : thm := BReverse.WORD_PMUL_ZX
unsafe def WORD_PMUL_STEP : thm := BReverse.WORD_PMUL_STEP
unsafe def WORD_PMUL_SYM : thm := BReverse.WORD_PMUL_SYM
unsafe def WORD_PMUL_POW2 : thm := BReverse.WORD_PMUL_POW2

-- Align
unsafe def aligned : thm := BAlign.aligned
unsafe def ALIGNED : thm := BAlign.ALIGNED
unsafe def ALIGNED_WORD : thm := BAlign.ALIGNED_WORD
unsafe def ALIGNED_IWORD : thm := BAlign.ALIGNED_IWORD
unsafe def ALIGNED_WORD_0 : thm := BAlign.ALIGNED_WORD_0
unsafe def ALIGNED_WORD_NEG : thm := BAlign.ALIGNED_WORD_NEG
unsafe def ALIGNED_WORD_ADD : thm := BAlign.ALIGNED_WORD_ADD
unsafe def ALIGNED_WORD_MUL : thm := BAlign.ALIGNED_WORD_MUL
unsafe def ALIGNED_WORD_SUB : thm := BAlign.ALIGNED_WORD_SUB
unsafe def ALIGNED_WORD_ADD_EQ : thm := BAlign.ALIGNED_WORD_ADD_EQ
unsafe def ALIGNED_WORD_SUB_EQ : thm := BAlign.ALIGNED_WORD_SUB_EQ
unsafe def word_jshl : thm := BAlign.word_jshl
unsafe def word_jshr : thm := BAlign.word_jshr
unsafe def word_jushr : thm := BAlign.word_jushr
unsafe def word_jdiv : thm := BAlign.word_jdiv
unsafe def word_jrem : thm := BAlign.word_jrem
unsafe def word_jror : thm := BAlign.word_jror
unsafe def word_jrol : thm := BAlign.word_jrol
unsafe def VAL_WORD_NEG_MOD_DIMINDEX : thm := BAlign.VAL_WORD_NEG_MOD_DIMINDEX
unsafe def WORD_JROL_JROR : thm := BAlign.WORD_JROL_JROR
unsafe def WORD_JROR_JROL : thm := BAlign.WORD_JROR_JROL
unsafe def WORD_JROR : thm := BAlign.WORD_JROR
unsafe def WORD_JROL : thm := BAlign.WORD_JROL
unsafe def WORD_JUSHR_NEG : thm := BAlign.WORD_JUSHR_NEG
unsafe def WORD_JSHL_NEG : thm := BAlign.WORD_JSHL_NEG

-- Topflip
unsafe def WORD_WORD_OPERATION_CONV : HolCore.Equal.ioconv := fun t => BTopflip.WORD_WORD_OPERATION_CONV t
unsafe def IVAL_TOPFLIP_VAL : thm := BTopflip.IVAL_TOPFLIP_VAL
unsafe def WORD_ULE_TOPFLIP : thm := BTopflip.WORD_ULE_TOPFLIP
unsafe def WORD_ULT_TOPFLIP : thm := BTopflip.WORD_ULT_TOPFLIP
unsafe def WORD_UGE_TOPFLIP : thm := BTopflip.WORD_UGE_TOPFLIP
unsafe def WORD_UGT_TOPFLIP : thm := BTopflip.WORD_UGT_TOPFLIP
unsafe def WORD_ILT_TOPFLIP : thm := BTopflip.WORD_ILT_TOPFLIP
unsafe def WORD_ILE_TOPFLIP : thm := BTopflip.WORD_ILE_TOPFLIP
unsafe def WORD_IGT_TOPFLIP : thm := BTopflip.WORD_IGT_TOPFLIP
unsafe def WORD_IGE_TOPFLIP : thm := BTopflip.WORD_IGE_TOPFLIP
unsafe def WORD_LE_ADD_EXACT : thm := BTopflip.WORD_LE_ADD_EXACT
unsafe def WORD_ADD_LT_EXACT : thm := BTopflip.WORD_ADD_LT_EXACT
unsafe def WORD_ADD_LT_INEXACT : thm := BTopflip.WORD_ADD_LT_INEXACT
unsafe def WORD_LT_ADC_EXACT : thm := BTopflip.WORD_LT_ADC_EXACT
unsafe def WORD_ADC_LE_EXACT : thm := BTopflip.WORD_ADC_LE_EXACT
unsafe def WORD_ADC_LE_INEXACT : thm := BTopflip.WORD_ADC_LE_INEXACT

-- BitWordConv
unsafe def BIT_WORD_CONV : HolCore.Equal.ioconv := fun t => BBitWordConv.BIT_WORD_CONV t

-- Blast
unsafe def WORD_BLAST : term → IO (Except String thm) := fun t => (BBlast.WORD_BLAST t).run
unsafe def WORD_POPCOUNT_ADD_OR : thm := BBlast.WORD_POPCOUNT_ADD_OR
unsafe def WORD_POPCOUNT_ADD : thm := BBlast.WORD_POPCOUNT_ADD
unsafe def WORD_POPCOUNT_MUL : thm := BBlast.WORD_POPCOUNT_MUL
unsafe def WORD_ODDPARITY_POPCOUNT : thm := BBlast.WORD_ODDPARITY_POPCOUNT
unsafe def WORD_EVENPARITY_POPCOUNT : thm := BBlast.WORD_EVENPARITY_POPCOUNT

-- Reduce1
unsafe def WORD_WORD_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_WORD_CONV t
unsafe def WORD_IWORD_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_IWORD_CONV t
unsafe def WORD_SATURATE_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_SATURATE_CONV t
unsafe def IWORD_SATURATE_CONV : HolCore.Equal.ioconv := fun t => BReduce1.IWORD_SATURATE_CONV t
unsafe def WORD_VAL_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_VAL_CONV t
unsafe def WORD_IVAL_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_IVAL_CONV t
unsafe def WORD_BIT_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_BIT_CONV t
unsafe def BIT_WORD_PMUL_CONV : HolCore.Equal.ioconv := fun t => BReduce1.BIT_WORD_PMUL_CONV t
unsafe def WORD_EQ_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_EQ_CONV t
unsafe def WORD_ULT_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_ULT_CONV t
unsafe def WORD_ULE_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_ULE_CONV t
unsafe def WORD_UGT_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_UGT_CONV t
unsafe def WORD_UGE_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_UGE_CONV t
unsafe def WORD_ILT_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_ILT_CONV t
unsafe def WORD_ILE_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_ILE_CONV t
unsafe def WORD_IGT_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_IGT_CONV t
unsafe def WORD_IGE_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_IGE_CONV t
unsafe def WORD_ADD_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_ADD_CONV t
unsafe def WORD_MUL_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_MUL_CONV t
unsafe def WORD_SUB_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_SUB_CONV t
unsafe def WORD_NEG_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_NEG_CONV t
unsafe def WORD_UDIV_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_UDIV_CONV t
unsafe def WORD_UMOD_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_UMOD_CONV t
unsafe def WORD_UMAX_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_UMAX_CONV t
unsafe def WORD_UMIN_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_UMIN_CONV t
unsafe def WORD_IMAX_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_IMAX_CONV t
unsafe def WORD_IMIN_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_IMIN_CONV t
unsafe def WORD_SHL_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_SHL_CONV t
unsafe def WORD_USHR_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_USHR_CONV t
unsafe def WORD_ISHR_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_ISHR_CONV t
unsafe def WORD_NOT_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_NOT_CONV t

-- Reduce2
unsafe def WORD_AND_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_AND_CONV t
unsafe def WORD_OR_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_OR_CONV t
unsafe def WORD_XOR_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_XOR_CONV t
unsafe def WORD_ROL_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_ROL_CONV t
unsafe def WORD_ROR_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_ROR_CONV t
unsafe def WORD_ZX_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_ZX_CONV t
unsafe def WORD_SX_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_SX_CONV t
unsafe def WORD_SXFROM_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_SXFROM_CONV t
unsafe def WORD_CAND_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_CAND_CONV t
unsafe def WORD_COR_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_COR_CONV t
unsafe def WORD_JOIN_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_JOIN_CONV t
unsafe def WORD_SUBWORD_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_SUBWORD_CONV t
unsafe def WORD_INSERT_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_INSERT_CONV t
unsafe def WORD_DUPLICATE_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_DUPLICATE_CONV t
unsafe def WORD_BITS_OF_WORD_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_BITS_OF_WORD_CONV t
unsafe def WORD_POPCOUNT_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_POPCOUNT_CONV t

-- Reduce3
unsafe def WORD_EVENPARITY_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_EVENPARITY_CONV t
unsafe def WORD_ODDPARITY_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_ODDPARITY_CONV t
unsafe def WORD_CTZ_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_CTZ_CONV t
unsafe def WORD_CLZ_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_CLZ_CONV t
unsafe def WORD_BYTEREVERSE_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_BYTEREVERSE_CONV t
unsafe def WORD_REVERSEFIELDS_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_REVERSEFIELDS_CONV t
unsafe def WORD_PMUL_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_PMUL_CONV t
unsafe def WORD_JSHL_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_JSHL_CONV t
unsafe def WORD_JSHR_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_JSHR_CONV t
unsafe def WORD_JUSHR_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_JUSHR_CONV t
unsafe def WORD_JROL_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_JROL_CONV t
unsafe def WORD_JROR_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_JROR_CONV t
unsafe def WORD_JDIV_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_JDIV_CONV t
unsafe def WORD_JREM_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_JREM_CONV t
unsafe def word_red_conv_list := BReduce3.word_red_conv_list
unsafe def WORD_RED_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_RED_CONV t
unsafe def WORD_REDUCE_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_REDUCE_CONV t
unsafe def word_compute_add_convs := BReduce3.word_compute_add_convs
unsafe def WORD_COMPUTE_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_COMPUTE_CONV t

-- Wordify
unsafe def WORD_TO_IWORD_CONV : HolCore.Equal.ioconv := fun t => BWordify.WORD_TO_IWORD_CONV t
unsafe def WORD_IREDUCE_CONV : HolCore.Equal.ioconv := fun t => BWordify.WORD_IREDUCE_CONV t
unsafe def EXPAND_NSUM_BALANCE_CONV : HolCore.Equal.ioconv := fun t => BWordify.EXPAND_NSUM_BALANCE_CONV t
unsafe def WORD_COMPARISON_ULT : thm := BWordify.WORD_COMPARISON_ULT
unsafe def WORD_COMPARISON_ULE : thm := BWordify.WORD_COMPARISON_ULE
unsafe def WORD_COMPARISON_ILT : thm := BWordify.WORD_COMPARISON_ILT
unsafe def WORD_COMPARISON_ILE : thm := BWordify.WORD_COMPARISON_ILE
unsafe def WORD_COMPARISON_NE : thm := BWordify.WORD_COMPARISON_NE
unsafe def WORD_COMPARISON_EQ : thm := BWordify.WORD_COMPARISON_EQ
unsafe def WORDIFY_CONV : HolCore.Equal.ioconv := fun t => BWordify.WORDIFY_CONV t
unsafe def VAL_WORD_ADJUST_CONV := BWordify.VAL_WORD_ADJUST_CONV
unsafe def VAL_WORD_ADJUST_BINOP_CONV : HolCore.Equal.ioconv := fun t => BWordify.VAL_WORD_ADJUST_BINOP_CONV t
unsafe def WORDIFY_ATOM_CONV : HolCore.Equal.ioconv := fun t => BWordify.WORDIFY_ATOM_CONV t
unsafe def IWORDIFY_CONV : HolCore.Equal.ioconv := fun t => BWordify.IWORDIFY_CONV t
unsafe def IVAL_WORD_ADJUST_CONV := BWordify.IVAL_WORD_ADJUST_CONV
unsafe def IVAL_WORD_ADJUST_BINOP_CONV : HolCore.Equal.ioconv := fun t => BWordify.IVAL_WORD_ADJUST_BINOP_CONV t
unsafe def IWORDIFY_ATOM_CONV : HolCore.Equal.ioconv := fun t => BWordify.IWORDIFY_ATOM_CONV t
unsafe def WORDIFY_WORD_CONV : HolCore.Equal.ioconv := fun t => BWordify.WORDIFY_WORD_CONV t

-- Bitblast
unsafe def WORD_MUL_EXPAND_CONV : HolCore.Equal.ioconv := fun t => BBitblast.WORD_MUL_EXPAND_CONV t
unsafe def WORD_POPCOUNT_EXPAND_CONV : HolCore.Equal.ioconv := fun t => BBitblast.WORD_POPCOUNT_EXPAND_CONV t
unsafe def WORD_INEQ_RELATION_EXPAND_CONV : HolCore.Equal.ioconv := fun t => BBitblast.WORD_INEQ_RELATION_EXPAND_CONV t
unsafe def VAL_MOD_OR_DIV_CONV : HolCore.Equal.ioconv := fun t => BBitblast.VAL_MOD_OR_DIV_CONV t
unsafe def BITBLAST_THEN := BBitblast.BITBLAST_THEN
unsafe def BITBLAST_TAC : HolCore.Tactics.tactic := fun g => BBitblast.BITBLAST_TAC g
unsafe def BITBLAST_RULE : term → IO (Except String thm) := fun t => (BBitblast.BITBLAST_RULE t).run

-- Simd
unsafe def usimd2 : thm := BSimd.usimd2
unsafe def simd2 : thm := BSimd.simd2
unsafe def usimd4 : thm := BSimd.usimd4
unsafe def simd4 : thm := BSimd.simd4
unsafe def usimd8 : thm := BSimd.usimd8
unsafe def simd8 : thm := BSimd.simd8
unsafe def usimd16 : thm := BSimd.usimd16
unsafe def simd16 : thm := BSimd.simd16
unsafe def USIMD2 : thm := BSimd.USIMD2
unsafe def SIMD2 : thm := BSimd.SIMD2


































-- @@EXPORTS END

/- The procedures (by hand, not generated). -/
/-- `BIT_PRED` (words.ml 1337). -/
unsafe def BIT_PRED (t : term) : Except String (Option term × thm) := BNumBits.BIT_PRED t
/-- `NUMBIT_CONV` (words.ml 1337). -/
unsafe def NUMBIT_CONV : HolCore.Equal.ioconv := fun t => BNumBits.NUMBIT_CONV t
/-- `NUM_SHIFT_ADD_CORE` (words.ml 1628). -/
unsafe def NUM_SHIFT_ADD_CORE (a b i : term) : Except String thm :=
  BNumShiftAdd.NUM_SHIFT_ADD_CORE a b i
/-- `NUM_SHIFT_ADD_CONV` (words.ml 1628). -/
unsafe def NUM_SHIFT_ADD_CONV : HolCore.Equal.ioconv := fun t => BNumShiftAdd.NUM_SHIFT_ADD_CONV t

/-- `needs "Library/words.ml"`: build every bundle, in file order. -/
unsafe def ensureWords : IO Unit := do
  -- @@ENSURE BEGIN
  let _ ← IO.mkRef BWordSizes.HAS_SIZE_8
  let _ ← IO.mkRef BDigitsum.DIGITSUM_WORKS_GEN
  let _ ← IO.mkRef BBitval.bitval
  let _ ← IO.mkRef BBinary.ODD_MOD_POW2
  let _ ← IO.mkRef BWordType.word_tybij
  let _ ← IO.mkRef BBitsOfWord.bits_of_word
  let _ ← IO.mkRef BVal.val_def
  let _ ← IO.mkRef BIval.ival
  let _ ← IO.mkRef BNumBits.numbit
  let _ ← IO.mkRef BNumShiftAdd.num_shift_add
  let _ ← IO.mkRef BLimits.word_UINT_MAX
  let _ ← IO.mkRef BPopcount.word_popcount
  let _ ← IO.mkRef BGeneralOps.modular
  let _ ← IO.mkRef BWordOps1.word_not
  let _ ← IO.mkRef BWordOps2.WORD_NOT_AS_SUB
  let _ ← IO.mkRef BWordOps3.WORD_SHL_WORD
  let _ ← IO.mkRef BWordRule.WORD_VAL_CONG_CONV
  let _ ← IO.mkRef BWordBitwise.WORD_BITWISE_RULE
  let _ ← IO.mkRef BWordArith.WORD_ARITH
  let _ ← IO.mkRef BValExpand.EMPOWER_CONV
  let _ ← IO.mkRef BZxSx.word_zx
  let _ ← IO.mkRef BJoinSubword.word_join
  let _ ← IO.mkRef BInsertDup.word_insert
  let _ ← IO.mkRef BBitRec.BIT_WORD_ADD
  let _ ← IO.mkRef BMisc1.WORD_ADD_0
  let _ ← IO.mkRef BMasks.WORD_MASK_ALT
  let _ ← IO.mkRef BClzCtz.word_ctz
  let _ ← IO.mkRef BReverse.word_reversefields
  let _ ← IO.mkRef BAlign.aligned
  let _ ← IO.mkRef BTopflip.IVAL_TOPFLIP_VAL
  let _ ← IO.mkRef BBitWordConv.BIT_WORD_CONV
  let _ ← IO.mkRef BBlast.WORD_POPCOUNT_ADD_OR
  let _ ← IO.mkRef BReduce1.WORD_WORD_CONV
  let _ ← IO.mkRef BReduce2.WORD_AND_CONV
  let _ ← IO.mkRef BReduce3.WORD_EVENPARITY_CONV
  let _ ← IO.mkRef BWordify.WORD_COMPARISON_ULT
  let _ ← IO.mkRef BBitblast.WORD_MUL_EXPAND_CONV
  let _ ← IO.mkRef BSimd.usimd2  -- @@ENSURE END
  pure ()

end SessionLibrary.Words
