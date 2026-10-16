/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/primitive.ml.                         -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Primitive.lean

  The `unsafe` half of the primitive.ml translation: it supplies HolLibrary.Primitive's
  dependencies from Session and SessionLibrary.Integer, SessionLibrary.Isum, SessionLibrary.Binomial, SessionLibrary.Pocklington, SessionLibrary.Multiplicative, builds the bundles once, in order,
  and exports every name under its HOL Light name.  `ensurePrimitive` is
  `needs "Library/primitive.ml"` (which first does `needs "Library/integer.ml"`, `needs "Library/isum.ml"`, `needs "Library/binomial.ml"`, `needs "Library/pocklington.ml"`, `needs "Library/multiplicative.ml"`).

  The blocks between `@@CORE` and `@@EXPORTS` markers are generated from
  HolLibrary/Primitive.lean by tools/primitivediff/gen_session.py and scope.py
  (bookkeeping only: field-by-field copies and accessors).
-/

import Session
import HolLibrary.Primitive
import SessionLibrary.Integer
import SessionLibrary.Isum
import SessionLibrary.Binomial
import SessionLibrary.Pocklington
import SessionLibrary.Multiplicative

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Primitive

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨Session.sessionB, Session.sessionC, Session.sessionT⟩

-- @@CORE BEGIN
/-- The core theorems primitive.ml uses. -/
unsafe def core1 (_ : Unit) : HolLibrary.Primitive.CoreThms1 where
  ADD1 := Session.ADD1
  ADD_CLAUSES := Session.ADD_CLAUSES
  ADD_EQ_0 := Session.ADD_EQ_0
  ADD_SUB := Session.ADD_SUB
  ARITH := Session.ARITH
  ARITH_EQ := Session.ARITH_EQ
  BINOMIAL_THEOREM := SessionLibrary.Binomial.«BINOMIAL_THEOREM»
  BINOM_1 := SessionLibrary.Binomial.«BINOM_1»
  BINOM_PENULT := SessionLibrary.Binomial.«BINOM_PENULT»
  BINOM_REFL := SessionLibrary.Binomial.«BINOM_REFL»
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARD_EQ_NSUM := Session.CARD_EQ_NSUM
  CARD_IMAGE_INJ := Session.CARD_IMAGE_INJ
  CARD_NUMSEG_LT := Session.CARD_NUMSEG_LT
  CARD_PSUBSET_IMP := Session.CARD_PSUBSET_IMP
  CARD_SUBSET_IMAGE := Session.CARD_SUBSET_IMAGE
  CARD_SUBSET_LE := Session.CARD_SUBSET_LE
  CHINESE_REMAINDER_COUNT := SessionLibrary.Pocklington.«CHINESE_REMAINDER_COUNT»
  CHINESE_REMAINDER_UNIQUE := SessionLibrary.Pocklington.«CHINESE_REMAINDER_UNIQUE»
  CHINESE_REMAINDER_USUAL := SessionLibrary.Pocklington.«CHINESE_REMAINDER_USUAL»
  COND_ID := Session.COND_ID
  CONG := Session.CONG
  CONG_CHINESE_EQ := SessionLibrary.Pocklington.«CONG_CHINESE_EQ»
  CONG_COPRIME := SessionLibrary.Pocklington.«CONG_COPRIME»
  CONG_EXP := SessionLibrary.Pocklington.«CONG_EXP»
  CONG_IMP_EQ := SessionLibrary.Pocklington.«CONG_IMP_EQ»
  CONG_MINUS1_SQUARED := SessionLibrary.Pocklington.«CONG_MINUS1_SQUARED»
  CONG_MOD := SessionLibrary.Pocklington.«CONG_MOD»
  CONG_MOD_0 := SessionLibrary.Pocklington.«CONG_MOD_0»
  CONG_MOD_1 := SessionLibrary.Pocklington.«CONG_MOD_1»
  CONG_REFL := SessionLibrary.Pocklington.«CONG_REFL»
  CONG_SYM := SessionLibrary.Pocklington.«CONG_SYM»
  CONG_TO_1 := SessionLibrary.Pocklington.«CONG_TO_1»
  CONG_TRANS := SessionLibrary.Pocklington.«CONG_TRANS»
  CONJ_ACI := Session.CONJ_ACI
  CONJ_ASSOC := Session.CONJ_ASSOC
  CONJ_SYM := Session.CONJ_SYM
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  COPRIME_0 := SessionLibrary.Prime.«COPRIME_0»
  COPRIME_1 := SessionLibrary.Prime.«COPRIME_1»
  COPRIME_2 := SessionLibrary.Prime.«COPRIME_2»
  COPRIME_EXP_DIVPROD := SessionLibrary.Prime.«COPRIME_EXP_DIVPROD»
  COPRIME_GCD := SessionLibrary.Prime.«COPRIME_GCD»
  COPRIME_LEXP := SessionLibrary.Prime.«COPRIME_LEXP»
  COPRIME_LMUL := SessionLibrary.Prime.«COPRIME_LMUL»
  COPRIME_PRIME := SessionLibrary.Prime.«COPRIME_PRIME»
  COPRIME_PRIME_EQ := SessionLibrary.Prime.«COPRIME_PRIME_EQ»
  COPRIME_REFL := SessionLibrary.Prime.«COPRIME_REFL»
  COPRIME_REXP := SessionLibrary.Prime.«COPRIME_REXP»
  COPRIME_RMOD := Session.COPRIME_RMOD
  COPRIME_RMUL := SessionLibrary.Prime.«COPRIME_RMUL»
  COPRIME_SYM := SessionLibrary.Prime.«COPRIME_SYM»
  COUNT_CONG_SOLVE := SessionLibrary.Pocklington.«COUNT_CONG_SOLVE»
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DIVIDES_0 := SessionLibrary.Prime.«DIVIDES_0»
  DIVIDES_1 := SessionLibrary.Prime.«DIVIDES_1»
  DIVIDES_2 := SessionLibrary.Prime.«DIVIDES_2»
  DIVIDES_ADD := SessionLibrary.Prime.«DIVIDES_ADD»
  DIVIDES_DIVIDES_DIV := Session.DIVIDES_DIVIDES_DIV
  DIVIDES_DIV_SELF := Session.DIVIDES_DIV_SELF
  DIVIDES_EXP_LE := SessionLibrary.Prime.«DIVIDES_EXP_LE»
  DIVIDES_EXP_LE_IMP := SessionLibrary.Prime.«DIVIDES_EXP_LE_IMP»
  DIVIDES_GCD_LEFT := SessionLibrary.Prime.«DIVIDES_GCD_LEFT»
  DIVIDES_LE := Session.DIVIDES_LE
  DIVIDES_LMUL := SessionLibrary.Prime.«DIVIDES_LMUL»
  DIVIDES_MOD := Session.DIVIDES_MOD
  DIVIDES_MUL2 := SessionLibrary.Prime.«DIVIDES_MUL2»
  DIVIDES_ONE := Session.DIVIDES_ONE
  DIVIDES_PRIMEPOW := SessionLibrary.Prime.«DIVIDES_PRIMEPOW»
  DIVIDES_PRIME_BINOM := SessionLibrary.Binomial.«DIVIDES_PRIME_BINOM»
/-- The core theorems primitive.ml uses. -/
unsafe def core2 (_ : Unit) : HolLibrary.Primitive.CoreThms2 where
  DIVIDES_PRIME_PRIME := SessionLibrary.Prime.«DIVIDES_PRIME_PRIME»
  DIVIDES_REFL := SessionLibrary.Prime.«DIVIDES_REFL»
  DIVIDES_REXP := SessionLibrary.Prime.«DIVIDES_REXP»
  DIVIDES_RMUL := SessionLibrary.Prime.«DIVIDES_RMUL»
  DIVIDES_RMUL2_EQ := SessionLibrary.Prime.«DIVIDES_RMUL2_EQ»
  DIVIDES_ZERO := SessionLibrary.Prime.«DIVIDES_ZERO»
  DIVISION := Session.DIVISION
  DIV_0 := Session.DIV_0
  DIV_1 := Session.DIV_1
  DIV_BY_DIV := Session.DIV_BY_DIV
  DIV_EQ_0 := Session.DIV_EQ_0
  DIV_MULT := Session.DIV_MULT
  DIV_REFL := Session.DIV_REFL
  EMPTY_GSPEC := Session.EMPTY_GSPEC
  EQ_ADD_LCANCEL_0 := Session.EQ_ADD_LCANCEL_0
  EQ_ADD_RCANCEL_0 := Session.EQ_ADD_RCANCEL_0
  EQ_IMP := Session.EQ_IMP
  EQ_IMP_LE := Session.EQ_IMP_LE
  EQ_MULT_LCANCEL := Session.EQ_MULT_LCANCEL
  EQ_TRANS := Session.EQ_TRANS
  ETA_AX := Session.ETA_AX
  EVEN_ADD := Session.EVEN_ADD
  EVEN_EXISTS := Session.EVEN_EXISTS
  EVEN_EXP := Session.EVEN_EXP
  EVEN_MULT := Session.EVEN_MULT
  EVEN_OR_ODD := Session.EVEN_OR_ODD
  EVEN_PHI := SessionLibrary.Pocklington.«EVEN_PHI»
  EVEN_PHI_EQ := SessionLibrary.Pocklington.«EVEN_PHI_EQ»
  EVEN_SUB := Session.EVEN_SUB
  EXISTS_INT_CASES := Session.EXISTS_INT_CASES
  EXISTS_LT_MOD_THM := Session.EXISTS_LT_MOD_THM
  EXISTS_REFL := Session.EXISTS_REFL
  EXP := Session.EXP
  EXP_1 := Session.EXP_1
  EXP_ADD := Session.EXP_ADD
  EXP_EQ_0 := Session.EXP_EQ_0
  EXP_EQ_1 := Session.EXP_EQ_1
  EXP_EXP := Session.EXP_EXP
  EXP_MONO_LE := Session.EXP_MONO_LE
  EXP_MULT := Session.EXP_MULT
  EXP_ONE := Session.EXP_ONE
  EXTENSION := Session.EXTENSION
  FERMAT_LITTLE := SessionLibrary.Pocklington.«FERMAT_LITTLE»
  FINITE_DIVISORS := SessionLibrary.Prime.«FINITE_DIVISORS»
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_INT_SEG := Session.FINITE_INT_SEG
  FINITE_NUMSEG := Session.FINITE_NUMSEG
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_RESTRICT := Session.FINITE_RESTRICT
  FINITE_SPECIAL_DIVISORS := SessionLibrary.Prime.«FINITE_SPECIAL_DIVISORS»
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_AND_THM := Session.FORALL_AND_THM
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_LT_MOD_THM := Session.FORALL_LT_MOD_THM
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  FORALL_UNWIND_THM2 := Session.FORALL_UNWIND_THM2
  FUN_EQ_THM := Session.FUN_EQ_THM
  GCD := Session.GCD
  GCD_0 := SessionLibrary.Prime.«GCD_0»
  GCD_1 := SessionLibrary.Prime.«GCD_1»
  GCD_2_CASES := SessionLibrary.Prime.«GCD_2_CASES»
  GCD_LE := SessionLibrary.Prime.«GCD_LE»
  GCD_ONE := SessionLibrary.Prime.«GCD_ONE»
  GCD_ZERO := SessionLibrary.Prime.«GCD_ZERO»
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_0 := Session.HAS_SIZE_0
  HAS_SIZE_IMAGE_INJ_RESTRICT := Session.HAS_SIZE_IMAGE_INJ_RESTRICT
  HAS_SIZE_NUMSEG_LT := Session.HAS_SIZE_NUMSEG_LT
  IMP_CONJ := Session.IMP_CONJ
/-- The core theorems primitive.ml uses. -/
unsafe def core3 (_ : Unit) : HolLibrary.Primitive.CoreThms3 where
  IMP_CONJ_ALT := Session.IMP_CONJ_ALT
  IMP_IMP := Session.IMP_IMP
  INDEX_EQ_0 := SessionLibrary.Prime.«INDEX_EQ_0»
  INDEX_EXP := SessionLibrary.Prime.«INDEX_EXP»
  INDEX_MUL := SessionLibrary.Prime.«INDEX_MUL»
  INDEX_REFL := SessionLibrary.Prime.«INDEX_REFL»
  INDUCT_COPRIME_ALT := SessionLibrary.Prime.«INDUCT_COPRIME_ALT»
  INDUCT_COPRIME_STRONG := SessionLibrary.Prime.«INDUCT_COPRIME_STRONG»
  INJECTIVE_EXP_MODULO := SessionLibrary.Pocklington.«INJECTIVE_EXP_MODULO»
  INT_2_DIVIDES_ADD := Session.INT_2_DIVIDES_ADD
  INT_2_DIVIDES_MUL := Session.INT_2_DIVIDES_MUL
  INT_2_DIVIDES_POW := Session.INT_2_DIVIDES_POW
  INT_ABS_NUM := Session.INT_ABS_NUM
  INT_ADD_RID := Session.INT_ADD_RID
  INT_CONG := SessionLibrary.Integer.«INT_CONG»
  INT_CONG_0_DIVIDES := SessionLibrary.Integer.«INT_CONG_0_DIVIDES»
  INT_CONG_MOD_0 := SessionLibrary.Integer.«INT_CONG_MOD_0»
  INT_CONG_NUM_EXISTS := Session.INT_CONG_NUM_EXISTS
  INT_CONG_POW := SessionLibrary.Integer.«INT_CONG_POW»
  INT_CONG_SOLVE := SessionLibrary.Integer.«INT_CONG_SOLVE»
  INT_CONG_SOLVE_POS := SessionLibrary.Integer.«INT_CONG_SOLVE_POS»
  INT_CONG_SYM := SessionLibrary.Integer.«INT_CONG_SYM»
  INT_CONG_TRANS := SessionLibrary.Integer.«INT_CONG_TRANS»
  INT_COPRIME_LMUL := SessionLibrary.Integer.«INT_COPRIME_LMUL»
  INT_COPRIME_LPOW := SessionLibrary.Integer.«INT_COPRIME_LPOW»
  INT_DIVIDES_0 := SessionLibrary.Integer.«INT_DIVIDES_0»
  INT_DIVIDES_ADD := SessionLibrary.Integer.«INT_DIVIDES_ADD»
  INT_DIVIDES_LABS := Session.INT_DIVIDES_LABS
  INT_DIVIDES_LE := SessionLibrary.Integer.«INT_DIVIDES_LE»
  INT_DIVIDES_LMUL := SessionLibrary.Integer.«INT_DIVIDES_LMUL»
  INT_DIVIDES_POW_LE_IMP := SessionLibrary.Integer.«INT_DIVIDES_POW_LE_IMP»
  INT_DIVIDES_REFL := SessionLibrary.Integer.«INT_DIVIDES_REFL»
  INT_EXISTS_POS := Session.INT_EXISTS_POS
  INT_FORALL_ABS := Session.INT_FORALL_ABS
  INT_LT_SUB_RADD := Session.INT_LT_SUB_RADD
  INT_MUL_LZERO := Session.INT_MUL_LZERO
  INT_MUL_RID := Session.INT_MUL_RID
  INT_OF_NUM_ADD := Session.INT_OF_NUM_ADD
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_GT := Session.INT_OF_NUM_GT
  INT_OF_NUM_LE := Session.INT_OF_NUM_LE
  INT_OF_NUM_LT := Session.INT_OF_NUM_LT
  INT_OF_NUM_MUL := Session.INT_OF_NUM_MUL
  INT_OF_NUM_POW := Session.INT_OF_NUM_POW
  INT_OF_NUM_SUB := Session.INT_OF_NUM_SUB
  INT_POW := Session.INT_POW
  INT_POW_1 := Session.INT_POW_1
  INT_POW_ADD := Session.INT_POW_ADD
  INT_POW_MUL := Session.INT_POW_MUL
  INT_POW_NEG := Session.INT_POW_NEG
  INT_POW_POW := Session.INT_POW_POW
  INT_PRIME_DIVPROD_EQ := SessionLibrary.Integer.«INT_PRIME_DIVPROD_EQ»
  INT_SUB_REFL := Session.INT_SUB_REFL
  IN_ELIM_PAIR_THM := Session.IN_ELIM_PAIR_THM
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_NUMSEG := Session.IN_NUMSEG
  ISUM_0 := SessionLibrary.Isum.«ISUM_0»
  ISUM_CASES := SessionLibrary.Isum.«ISUM_CASES»
  ISUM_CLAUSES_NUMSEG := SessionLibrary.Isum.«ISUM_CLAUSES_NUMSEG»
  ISUM_CLAUSES_RIGHT := SessionLibrary.Isum.«ISUM_CLAUSES_RIGHT»
  ISUM_SING := SessionLibrary.Isum.«ISUM_SING»
  ISUM_SING_NUMSEG := SessionLibrary.Isum.«ISUM_SING_NUMSEG»
  ITERATE_CLAUSES := Session.ITERATE_CLAUSES
  ITERATE_EQ := Session.ITERATE_EQ
  ITERATE_SING := Session.ITERATE_SING
  ITERATE_UNION := Session.ITERATE_UNION
  LCM_1 := SessionLibrary.Prime.«LCM_1»
  LCM_SYM := SessionLibrary.Prime.«LCM_SYM»
  LE := Session.LE
/-- The core theorems primitive.ml uses. -/
unsafe def core4 (_ : Unit) : HolLibrary.Primitive.CoreThms4 where
  LEFT_FORALL_IMP_THM := Session.LEFT_FORALL_IMP_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LEFT_OR_DISTRIB := Session.LEFT_OR_DISTRIB
  LE_0 := Session.LE_0
  LE_1 := Session.LE_1
  LE_ANTISYM := Session.LE_ANTISYM
  LE_EXP := Session.LE_EXP
  LE_MULT2 := Session.LE_MULT2
  LE_MULT_LCANCEL := Session.LE_MULT_LCANCEL
  LE_MULT_RCANCEL := Session.LE_MULT_RCANCEL
  LE_REFL := Session.LE_REFL
  LE_TRANS := Session.LE_TRANS
  LT := Session.LT
  LT_IMP_NE := Session.LT_IMP_NE
  LT_LE := Session.LT_LE
  LT_REFL := Session.LT_REFL
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MOD_EXP_MOD := Session.MOD_EXP_MOD
  MOD_LT_EQ := Session.MOD_LT_EQ
  MONOIDAL_MUL := Session.MONOIDAL_MUL
  MONO_EXISTS := Session.MONO_EXISTS
  MULT_AC := Session.MULT_AC
  MULT_ASSOC := Session.MULT_ASSOC
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_EQ_0 := Session.MULT_EQ_0
  MULT_EQ_1 := Session.MULT_EQ_1
  MULT_EXP := Session.MULT_EXP
  MULT_SYM := Session.MULT_SYM
  NEUTRAL_MUL := Session.NEUTRAL_MUL
  NOT_EVEN := Session.NOT_EVEN
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NOT_LE := Session.NOT_LE
  NOT_LT := Session.NOT_LT
  NOT_ODD := Session.NOT_ODD
  NOT_SUC := Session.NOT_SUC
  NSUM_CLAUSES_LEFT := Session.NSUM_CLAUSES_LEFT
  NSUM_CLAUSES_RIGHT := Session.NSUM_CLAUSES_RIGHT
  NSUM_CLOSED := Session.NSUM_CLOSED
  NSUM_CONST_NUMSEG := Session.NSUM_CONST_NUMSEG
  NSUM_EQ := Session.NSUM_EQ
  NSUM_GROUP := Session.NSUM_GROUP
  NSUM_LE := Session.NSUM_LE
  NSUM_LMUL := Session.NSUM_LMUL
  NSUM_LT := Session.NSUM_LT
  NUM_OF_INT_OF_NUM := Session.NUM_OF_INT_OF_NUM
  ODD := Session.ODD
  ODD_ADD := Session.ODD_ADD
  ODD_EXISTS := Session.ODD_EXISTS
  ODD_EXP := Session.ODD_EXP
  ODD_MOD_2 := SessionLibrary.Pocklington.«ODD_MOD_2»
  ODD_MOD_EVEN := Session.ODD_MOD_EVEN
  ODD_MULT := Session.ODD_MULT
  ODD_PRIME := SessionLibrary.Prime.«ODD_PRIME»
  ORDER := SessionLibrary.Pocklington.«ORDER»
  ORDER_1 := SessionLibrary.Pocklington.«ORDER_1»
  ORDER_CONG := SessionLibrary.Pocklington.«ORDER_CONG»
  ORDER_DIVIDES := SessionLibrary.Pocklington.«ORDER_DIVIDES»
  ORDER_DIVIDES_EXPDIFF := SessionLibrary.Pocklington.«ORDER_DIVIDES_EXPDIFF»
  ORDER_DIVIDES_PHI := SessionLibrary.Pocklington.«ORDER_DIVIDES_PHI»
  ORDER_EQ_0 := SessionLibrary.Pocklington.«ORDER_EQ_0»
  ORDER_EQ_1 := SessionLibrary.Pocklington.«ORDER_EQ_1»
  ORDER_EXP := SessionLibrary.Pocklington.«ORDER_EXP»
  ORDER_EXP_GEN := SessionLibrary.Pocklington.«ORDER_EXP_GEN»
  ORDER_MOD := SessionLibrary.Pocklington.«ORDER_MOD»
  ORDER_MUL_LCM := SessionLibrary.Pocklington.«ORDER_MUL_LCM»
  ORDER_UNIQUE := SessionLibrary.Pocklington.«ORDER_UNIQUE»
  ORDER_UNIQUE_PRIME := SessionLibrary.Pocklington.«ORDER_UNIQUE_PRIME»
/-- The core theorems primitive.ml uses. -/
unsafe def core5 (_ : Unit) : HolLibrary.Primitive.CoreThms5 where
  ORDER_WORKS := SessionLibrary.Pocklington.«ORDER_WORKS»
  PHI_0 := SessionLibrary.Pocklington.«PHI_0»
  PHI_1 := SessionLibrary.Pocklington.«PHI_1»
  PHI_2 := SessionLibrary.Pocklington.«PHI_2»
  PHI_ALT := SessionLibrary.Pocklington.«PHI_ALT»
  PHI_DIVISORSUM := SessionLibrary.Multiplicative.«PHI_DIVISORSUM»
  PHI_EQ_0 := SessionLibrary.Pocklington.«PHI_EQ_0»
  PHI_FINITE_LEMMA := SessionLibrary.Pocklington.«PHI_FINITE_LEMMA»
  PHI_LOWERBOUND_1_STRONG := SessionLibrary.Pocklington.«PHI_LOWERBOUND_1_STRONG»
  PHI_LOWERBOUND_2 := SessionLibrary.Pocklington.«PHI_LOWERBOUND_2»
  PHI_MULTIPLICATIVE := SessionLibrary.Pocklington.«PHI_MULTIPLICATIVE»
  PHI_PRIME := SessionLibrary.Pocklington.«PHI_PRIME»
  PHI_PRIMEPOW := SessionLibrary.Pocklington.«PHI_PRIMEPOW»
  PHI_PRIMEPOW_ALT := SessionLibrary.Pocklington.«PHI_PRIMEPOW_ALT»
  PRIMEPOW_FACTOR := SessionLibrary.Prime.«PRIMEPOW_FACTOR»
  PRIME_0 := SessionLibrary.Prime.«PRIME_0»
  PRIME_1 := SessionLibrary.Prime.«PRIME_1»
  PRIME_2 := SessionLibrary.Prime.«PRIME_2»
  PRIME_COPRIME_EQ := SessionLibrary.Prime.«PRIME_COPRIME_EQ»
  PRIME_COPRIME_LT := SessionLibrary.Prime.«PRIME_COPRIME_LT»
  PRIME_DIVEXP := SessionLibrary.Prime.«PRIME_DIVEXP»
  PRIME_DIVEXP_EQ := SessionLibrary.Prime.«PRIME_DIVEXP_EQ»
  PRIME_DIVPROD_EQ := SessionLibrary.Prime.«PRIME_DIVPROD_EQ»
  PRIME_GE_2 := SessionLibrary.Prime.«PRIME_GE_2»
  PRIME_IMP_NZ := SessionLibrary.Prime.«PRIME_IMP_NZ»
  PRIME_ODD := SessionLibrary.Prime.«PRIME_ODD»
  REAL_ADD_LID := Session.REAL_ADD_LID
  REAL_MUL_AC := Session.REAL_MUL_AC
  REAL_MUL_RZERO := Session.REAL_MUL_RZERO
  REAL_SUB_LDISTRIB := Session.REAL_SUB_LDISTRIB
  REAL_SUB_POW := Session.REAL_SUB_POW
  REAL_SUB_REFL := Session.REAL_SUB_REFL
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RIGHT_IMP_FORALL_THM := Session.RIGHT_IMP_FORALL_THM
  RIGHT_SUB_DISTRIB := Session.RIGHT_SUB_DISTRIB
  SING_GSPEC := Session.SING_GSPEC
  SUBSET := Session.SUBSET
  SUB_ADD := Session.SUB_ADD
  SUB_REFL := Session.SUB_REFL
  SUC_SUB1 := Session.SUC_SUB1
  SUM_CLAUSES_LEFT := Session.SUM_CLAUSES_LEFT
  SUM_EQ_GENERAL_INVERSES := Session.SUM_EQ_GENERAL_INVERSES
  SUM_LMUL := Session.SUM_LMUL
  SUM_RMUL := Session.SUM_RMUL
  SUM_SUB_NUMSEG := Session.SUM_SUB_NUMSEG
  SUM_SUM_PRODUCT := Session.SUM_SUM_PRODUCT
  SURJECTIVE_IFF_INJECTIVE := Session.SURJECTIVE_IFF_INJECTIVE
  SURJECTIVE_IFF_INJECTIVE_GEN := Session.SURJECTIVE_IFF_INJECTIVE_GEN
  SWAP_FORALL_THM := Session.SWAP_FORALL_THM
  UNWIND_THM2 := Session.UNWIND_THM2
  WLOG_LT := Session.WLOG_LT
  binom := SessionLibrary.Binomial.«binom»
  coprime := Session.coprime
  divides := Session.divides
  int_congruent := Session.int_congruent
  int_prime := SessionLibrary.Integer.«int_prime»
  nproduct := Session.nproduct
  num_INDUCTION := Session.num_INDUCTION
  num_WF := Session.num_WF
  num_congruent := Session.num_congruent
  num_coprime := Session.num_coprime
  num_divides := Session.num_divides
  prime := Session.prime
  real_pow := Session.real_pow
/-- The core theorems primitive.ml uses. -/
unsafe def core6 (_ : Unit) : HolLibrary.Primitive.CoreThms6 where
/-- The core theorems primitive.ml uses. -/
unsafe def core7 (_ : Unit) : HolLibrary.Primitive.CoreThms7 where
/-- The core theorems primitive.ml uses. -/
unsafe def core8 (_ : Unit) : HolLibrary.Primitive.CoreThms8 where
-- @@CORE END

/-- What primitive.ml uses from Session. -/
unsafe def deps (_ : Unit) : HolLibrary.Primitive.PrimitiveDeps where
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  INT_ARITH t := ExceptT.mk (Session.INT_ARITH t)
  ASM_INT_ARITH_TAC := Session.ASM_INT_ARITH_TAC
  INTEGER_RULE t := ExceptT.mk (Session.INTEGER_RULE t)
  NUMBER_RULE t := ExceptT.mk (Session.NUMBER_RULE t)
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  REAL_ARITH t := ExceptT.mk (Session.REAL_ARITH3 t)
  INDUCT_TAC := Session.INDUCT_TAC
  INT_OF_REAL_THM th := ExceptT.mk (SessionLibrary.Isum.INT_OF_REAL_THM th)
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  CONG_CONV := SessionLibrary.Pocklington.CONG_CONV
  MOD_DOWN_CONV := Session.MOD_DOWN_CONV
  NUM_RING := Session.NUM_RING
  PRIME_CONV t := ExceptT.mk (SessionLibrary.Pocklington.PRIME_CONV t)
  EXPAND_CASES_CONV := Session.EXPAND_CASES_CONV
  COPRIME_CONV := SessionLibrary.Prime.COPRIME_CONV
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
    Light adds loading ind_types.ml), then integer.ml, isum.ml, binomial.ml, pocklington.ml, multiplicative.ml, which primitive.ml needs. -/
private unsafe def cached {α : Type} [Inhabited α] (r : IO.Ref (Option α)) (name : String)
    (setup : Unit → IO (Except String α)) : α :=
  match unsafeIO (do
    match ← r.get with
    | some d => pure d
    | none => do
      Session.ensureDefine
      let _ ← Session.MATCH_CONV (HolCore.Kernel.mk_var "p" HolCore.Kernel.bool_ty)
      SessionLibrary.Integer.ensureInteger
      SessionLibrary.Isum.ensureIsum
      SessionLibrary.Binomial.ensureBinomial
      SessionLibrary.Pocklington.ensurePocklington
      SessionLibrary.Multiplicative.ensureMultiplicative
      match ← setup () with
      | .ok d => do r.set (some d); pure d
      | .error e => panic! s!"{name} failed: {e}") with
  | .ok d => d | _ => panic! s!"SessionLibrary.Primitive: {name}"

/- The bundles, in file order; each forces the one before it. -/

-- @@BUNDLES BEGIN
initialize theLemma : IO.Ref (Option HolLibrary.Primitive.Lemma) ← IO.mkRef none
unsafe def BLemma : HolLibrary.Primitive.Lemma :=
  cached theLemma "setupLemma" fun _ => do
    (HolLibrary.Primitive.setupLemma (deps ())).run

initialize thePolyDiff : IO.Ref (Option HolLibrary.Primitive.PolyDiff) ← IO.mkRef none
unsafe def BPolyDiff : HolLibrary.Primitive.PolyDiff :=
  cached thePolyDiff "setupPolyDiff" fun _ => do
    let _ ← IO.mkRef BLemma.INT_PRIME
    (HolLibrary.Primitive.setupPolyDiff (deps ())).run

initialize theLagrange : IO.Ref (Option HolLibrary.Primitive.Lagrange) ← IO.mkRef none
unsafe def BLagrange : HolLibrary.Primitive.Lagrange :=
  cached theLagrange "setupLagrange" fun _ => do
    let _ ← IO.mkRef BPolyDiff.REAL_POLY_DIFF_EXPLICIT
    (HolLibrary.Primitive.setupLagrange (deps ()) BPolyDiff).run

initialize theNumLagrange : IO.Ref (Option HolLibrary.Primitive.NumLagrange) ← IO.mkRef none
unsafe def BNumLagrange : HolLibrary.Primitive.NumLagrange :=
  cached theNumLagrange "setupNumLagrange" fun _ => do
    let _ ← IO.mkRef BLagrange.FINITE_INTSEG_RESTRICT
    (HolLibrary.Primitive.setupNumLagrange (deps ()) BLemma BLagrange).run

initialize theCountOrders : IO.Ref (Option HolLibrary.Primitive.CountOrders) ← IO.mkRef none
unsafe def BCountOrders : HolLibrary.Primitive.CountOrders :=
  cached theCountOrders "setupCountOrders" fun _ => do
    let _ ← IO.mkRef BNumLagrange.NUM_LAGRANGE_LEMMA
    (HolLibrary.Primitive.setupCountOrders (deps ()) BNumLagrange).run

initialize thePrimitiveRoots : IO.Ref (Option HolLibrary.Primitive.PrimitiveRoots) ← IO.mkRef none
unsafe def BPrimitiveRoots : HolLibrary.Primitive.PrimitiveRoots :=
  cached thePrimitiveRoots "setupPrimitiveRoots" fun _ => do
    let _ ← IO.mkRef BCountOrders.COUNT_ORDERS_MODULO_PRIME
    (HolLibrary.Primitive.setupPrimitiveRoots (deps ()) BCountOrders).run

initialize thePrimePows1 : IO.Ref (Option HolLibrary.Primitive.PrimePows1) ← IO.mkRef none
unsafe def BPrimePows1 : HolLibrary.Primitive.PrimePows1 :=
  cached thePrimePows1 "setupPrimePows1" fun _ => do
    let _ ← IO.mkRef BPrimitiveRoots.PRIMITIVE_ROOTS_MODULO_PRIME
    (HolLibrary.Primitive.setupPrimePows1 (deps ()) BPrimitiveRoots).run

initialize thePrimePows2 : IO.Ref (Option HolLibrary.Primitive.PrimePows2) ← IO.mkRef none
unsafe def BPrimePows2 : HolLibrary.Primitive.PrimePows2 :=
  cached thePrimePows2 "setupPrimePows2" fun _ => do
    let _ ← IO.mkRef BPrimePows1.COPRIME_1_PLUS_POWER_STEP
    (HolLibrary.Primitive.setupPrimePows2 (deps ()) BPrimePows1).run

initialize theDouble : IO.Ref (Option HolLibrary.Primitive.Double) ← IO.mkRef none
unsafe def BDouble : HolLibrary.Primitive.Double :=
  cached theDouble "setupDouble" fun _ => do
    let _ ← IO.mkRef BPrimePows2.PRIMITIVE_ROOT_MODULO_PRIMEPOW
    (HolLibrary.Primitive.setupDouble (deps ()) BPrimePows2).run

initialize theDegenerate : IO.Ref (Option HolLibrary.Primitive.Degenerate) ← IO.mkRef none
unsafe def BDegenerate : HolLibrary.Primitive.Degenerate :=
  cached theDegenerate "setupDegenerate" fun _ => do
    let _ ← IO.mkRef BDouble.PRIMITIVE_ROOT_MODULO_2
    (HolLibrary.Primitive.setupDegenerate (deps ())).run

initialize theNegative : IO.Ref (Option HolLibrary.Primitive.Negative) ← IO.mkRef none
unsafe def BNegative : HolLibrary.Primitive.Negative :=
  cached theNegative "setupNegative" fun _ => do
    let _ ← IO.mkRef BDegenerate.PRIMITIVE_ROOT_MODULO_0
    (HolLibrary.Primitive.setupNegative (deps ())).run

initialize theEquivalences : IO.Ref (Option HolLibrary.Primitive.Equivalences) ← IO.mkRef none
unsafe def BEquivalences : HolLibrary.Primitive.Equivalences :=
  cached theEquivalences "setupEquivalences" fun _ => do
    let _ ← IO.mkRef BNegative.CONG_TO_1_POW2
    (HolLibrary.Primitive.setupEquivalences (deps ()) BPrimePows2 BDouble BDegenerate BNegative).run

initialize theCountPrimitiveRoots : IO.Ref (Option HolLibrary.Primitive.CountPrimitiveRoots) ← IO.mkRef none
unsafe def BCountPrimitiveRoots : HolLibrary.Primitive.CountPrimitiveRoots :=
  cached theCountPrimitiveRoots "setupCountPrimitiveRoots" fun _ => do
    let _ ← IO.mkRef BEquivalences.PRIMITIVE_ROOT_EXISTS
    (HolLibrary.Primitive.setupCountPrimitiveRoots (deps ()) BEquivalences).run

initialize theCountRoots : IO.Ref (Option HolLibrary.Primitive.CountRoots) ← IO.mkRef none
unsafe def BCountRoots : HolLibrary.Primitive.CountRoots :=
  cached theCountRoots "setupCountRoots" fun _ => do
    let _ ← IO.mkRef BCountPrimitiveRoots.COUNT_PRIMITIVE_ROOTS_ALT
    (HolLibrary.Primitive.setupCountRoots (deps ()) BPrimitiveRoots).run

initialize theQuadraticResidues : IO.Ref (Option HolLibrary.Primitive.QuadraticResidues) ← IO.mkRef none
unsafe def BQuadraticResidues : HolLibrary.Primitive.QuadraticResidues :=
  cached theQuadraticResidues "setupQuadraticResidues" fun _ => do
    let _ ← IO.mkRef BCountRoots.COUNT_ROOTS_MODULO_PRIMITIVE_GEN_ALT
    (HolLibrary.Primitive.setupQuadraticResidues (deps ())).run

initialize theEulerCriterion : IO.Ref (Option HolLibrary.Primitive.EulerCriterion) ← IO.mkRef none
unsafe def BEulerCriterion : HolLibrary.Primitive.EulerCriterion :=
  cached theEulerCriterion "setupEulerCriterion" fun _ => do
    let _ ← IO.mkRef BQuadraticResidues.INT_OF_NUM_POWER_RESIDUE
    (HolLibrary.Primitive.setupEulerCriterion (deps ()) BEquivalences BCountRoots).run

initialize theCountRootsOdd : IO.Ref (Option HolLibrary.Primitive.CountRootsOdd) ← IO.mkRef none
unsafe def BCountRootsOdd : HolLibrary.Primitive.CountRootsOdd :=
  cached theCountRootsOdd "setupCountRootsOdd" fun _ => do
    let _ ← IO.mkRef BEulerCriterion.GENERALIZED_EULER_CRITERION
    (HolLibrary.Primitive.setupCountRootsOdd (deps ()) BEquivalences BCountRoots).run

initialize theCountRootsPrimitive : IO.Ref (Option HolLibrary.Primitive.CountRootsPrimitive) ← IO.mkRef none
unsafe def BCountRootsPrimitive : HolLibrary.Primitive.CountRootsPrimitive :=
  cached theCountRootsPrimitive "setupCountRootsPrimitive" fun _ => do
    let _ ← IO.mkRef BCountRootsOdd.COUNT_ROOTS_MODULO_ODD_GEN
    (HolLibrary.Primitive.setupCountRootsPrimitive (deps ()) BCountRoots BCountRootsOdd).run

initialize theQuadraticNonresidue : IO.Ref (Option HolLibrary.Primitive.QuadraticNonresidue) ← IO.mkRef none
unsafe def BQuadraticNonresidue : HolLibrary.Primitive.QuadraticNonresidue :=
  cached theQuadraticNonresidue "setupQuadraticNonresidue" fun _ => do
    let _ ← IO.mkRef BCountRootsPrimitive.COUNT_ROOTS_MODULO_PRIMITIVE_ALT
    (HolLibrary.Primitive.setupQuadraticNonresidue (deps ()) BEquivalences BCountRoots BQuadraticResidues).run

-- @@BUNDLES END

-- @@EXPORTS BEGIN
-- Lemma
unsafe def INT_PRIME : thm := BLemma.INT_PRIME

-- PolyDiff
unsafe def REAL_POLY_DIFF_EXPLICIT : thm := BPolyDiff.REAL_POLY_DIFF_EXPLICIT
unsafe def INT_POLY_DIFF_EXPLICIT : thm := BPolyDiff.INT_POLY_DIFF_EXPLICIT

-- Lagrange
unsafe def FINITE_INTSEG_RESTRICT : thm := BLagrange.FINITE_INTSEG_RESTRICT
unsafe def INT_POLY_LAGRANGE : thm := BLagrange.INT_POLY_LAGRANGE

-- NumLagrange
unsafe def NUM_LAGRANGE_LEMMA : thm := BNumLagrange.NUM_LAGRANGE_LEMMA

-- CountOrders
unsafe def COUNT_ORDERS_MODULO_PRIME : thm := BCountOrders.COUNT_ORDERS_MODULO_PRIME

-- PrimitiveRoots
unsafe def PRIMITIVE_ROOTS_MODULO_PRIME : thm := BPrimitiveRoots.PRIMITIVE_ROOTS_MODULO_PRIME
unsafe def PRIMITIVE_ROOT_MODULO_PRIME : thm := BPrimitiveRoots.PRIMITIVE_ROOT_MODULO_PRIME

-- PrimePows1
unsafe def COPRIME_1_PLUS_POWER_STEP : thm := BPrimePows1.COPRIME_1_PLUS_POWER_STEP
unsafe def COPRIME_1_PLUS_POWER : thm := BPrimePows1.COPRIME_1_PLUS_POWER
unsafe def PRIMITIVE_ROOT_MODULO_PRIMEPOWS : thm := BPrimePows1.PRIMITIVE_ROOT_MODULO_PRIMEPOWS

-- PrimePows2
unsafe def PRIMITIVE_ROOT_MODULO_PRIMEPOW : thm := BPrimePows2.PRIMITIVE_ROOT_MODULO_PRIMEPOW
unsafe def PRIME_DIVISOR_ORDER_EXISTS : thm := BPrimePows2.PRIME_DIVISOR_ORDER_EXISTS
unsafe def INJECTIVE_EXP_MODULO_EQ : thm := BPrimePows2.INJECTIVE_EXP_MODULO_EQ
unsafe def POWER_RESIDUE_MODULO_EQ_ALT : thm := BPrimePows2.POWER_RESIDUE_MODULO_EQ_ALT
unsafe def POWER_RESIDUE_MODULO_EQ : thm := BPrimePows2.POWER_RESIDUE_MODULO_EQ

-- Double
unsafe def PRIMITIVE_ROOT_MODULO_2 : thm := BDouble.PRIMITIVE_ROOT_MODULO_2
unsafe def PRIMITIVE_ROOT_MODULO_4 : thm := BDouble.PRIMITIVE_ROOT_MODULO_4
unsafe def PRIMITIVE_ROOT_DOUBLE_LEMMA : thm := BDouble.PRIMITIVE_ROOT_DOUBLE_LEMMA
unsafe def PRIMITIVE_ROOT_MODULO_DOUBLE_PRIMEPOW : thm := BDouble.PRIMITIVE_ROOT_MODULO_DOUBLE_PRIMEPOW

-- Degenerate
unsafe def PRIMITIVE_ROOT_MODULO_0 : thm := BDegenerate.PRIMITIVE_ROOT_MODULO_0
unsafe def PRIMITIVE_ROOT_MODULO_1 : thm := BDegenerate.PRIMITIVE_ROOT_MODULO_1

-- Negative
unsafe def CONG_TO_1_POW2 : thm := BNegative.CONG_TO_1_POW2
unsafe def NO_PRIMITIVE_ROOT_MODULO_POW2 : thm := BNegative.NO_PRIMITIVE_ROOT_MODULO_POW2
unsafe def NO_PRIMITIVE_ROOT_MODULO_COMPOSITE : thm := BNegative.NO_PRIMITIVE_ROOT_MODULO_COMPOSITE

-- Equivalences
unsafe def PRIMITIVE_ROOT_EXISTS : thm := BEquivalences.PRIMITIVE_ROOT_EXISTS
unsafe def PRIMITIVE_ROOT_EXISTS_NONTRIVIAL : thm := BEquivalences.PRIMITIVE_ROOT_EXISTS_NONTRIVIAL

-- CountPrimitiveRoots
unsafe def COUNT_PRIMITIVE_ROOTS_ALT : thm := BCountPrimitiveRoots.COUNT_PRIMITIVE_ROOTS_ALT
unsafe def COUNT_PRIMITIVE_ROOTS : thm := BCountPrimitiveRoots.COUNT_PRIMITIVE_ROOTS

-- CountRoots
unsafe def COUNT_ROOTS_MODULO_PRIMITIVE_GEN_ALT : thm := BCountRoots.COUNT_ROOTS_MODULO_PRIMITIVE_GEN_ALT
unsafe def COUNT_ROOTS_MODULO_PRIMITIVE_GEN : thm := BCountRoots.COUNT_ROOTS_MODULO_PRIMITIVE_GEN
unsafe def POWER_RESIDUE_MODULO_PRIMITIVE : thm := BCountRoots.POWER_RESIDUE_MODULO_PRIMITIVE
unsafe def POWER_RESIDUE_MODULO_PRIME_EQ : thm := BCountRoots.POWER_RESIDUE_MODULO_PRIME_EQ
unsafe def POWER_RESIDUE_MODULO_PRIMITIVE_ORDER_ALT : thm := BCountRoots.POWER_RESIDUE_MODULO_PRIMITIVE_ORDER_ALT
unsafe def POWER_RESIDUE_MODULO_PRIMITIVE_ORDER : thm := BCountRoots.POWER_RESIDUE_MODULO_PRIMITIVE_ORDER
unsafe def QUADRATIC_RESIDUE_MODULO_PRIMITIVE_ORDER : thm := BCountRoots.QUADRATIC_RESIDUE_MODULO_PRIMITIVE_ORDER
unsafe def POWER_RESIDUE_MODULO_PRIMITIVE_POWER : thm := BCountRoots.POWER_RESIDUE_MODULO_PRIMITIVE_POWER
unsafe def QUADRATIC_RESIDUE_MODULO_PRIMITIVE_POWER : thm := BCountRoots.QUADRATIC_RESIDUE_MODULO_PRIMITIVE_POWER
unsafe def COUNT_POWER_RESIDUES_MODULO_PRIMITIVE : thm := BCountRoots.COUNT_POWER_RESIDUES_MODULO_PRIMITIVE
unsafe def COUNT_QUADRATIC_RESIDUES_MODULO_PRIMITIVE : thm := BCountRoots.COUNT_QUADRATIC_RESIDUES_MODULO_PRIMITIVE

-- QuadraticResidues
unsafe def INT_OF_NUM_POWER_RESIDUE : thm := BQuadraticResidues.INT_OF_NUM_POWER_RESIDUE
unsafe def QUADRATIC_RESIDUE_MODULO_ODD_POWER : thm := BQuadraticResidues.QUADRATIC_RESIDUE_MODULO_ODD_POWER
unsafe def QUADRATIC_RESIDUE_MODULO_POWER_2_STABLE : thm := BQuadraticResidues.QUADRATIC_RESIDUE_MODULO_POWER_2_STABLE
unsafe def QUADRATIC_RESIDUE_MODULO_POWER_2 : thm := BQuadraticResidues.QUADRATIC_RESIDUE_MODULO_POWER_2

-- EulerCriterion
unsafe def GENERALIZED_EULER_CRITERION : thm := BEulerCriterion.GENERALIZED_EULER_CRITERION
unsafe def GENERALIZED_EULER_CRITERION_PRIME : thm := BEulerCriterion.GENERALIZED_EULER_CRITERION_PRIME
unsafe def EULER_CRITERION : thm := BEulerCriterion.EULER_CRITERION

-- CountRootsOdd
unsafe def COUNT_ROOTS_MODULO_ODD_GEN : thm := BCountRootsOdd.COUNT_ROOTS_MODULO_ODD_GEN
unsafe def COUNT_ROOTS_MODULO_ODD_ALT_GEN : thm := BCountRootsOdd.COUNT_ROOTS_MODULO_ODD_ALT_GEN
unsafe def POWER_RESIDUE_MODULO_ODD : thm := BCountRootsOdd.POWER_RESIDUE_MODULO_ODD

-- CountRootsPrimitive
unsafe def COUNT_ROOTS_MODULO_PRIMITIVE_ALT : thm := BCountRootsPrimitive.COUNT_ROOTS_MODULO_PRIMITIVE_ALT
unsafe def COUNT_ROOTS_MODULO_PRIMITIVE : thm := BCountRootsPrimitive.COUNT_ROOTS_MODULO_PRIMITIVE
unsafe def COUNT_ROOTS_MODULO_ODD_ALT : thm := BCountRootsPrimitive.COUNT_ROOTS_MODULO_ODD_ALT
unsafe def COUNT_ROOTS_MODULO_ODD : thm := BCountRootsPrimitive.COUNT_ROOTS_MODULO_ODD
unsafe def POWER_RESIDUE_EXISTS : thm := BCountRootsPrimitive.POWER_RESIDUE_EXISTS

-- QuadraticNonresidue
unsafe def QUADRATIC_NONRESIDUE_EXISTS : thm := BQuadraticNonresidue.QUADRATIC_NONRESIDUE_EXISTS
-- @@EXPORTS END

/-- `needs "Library/primitive.ml"`: build the bundles, in order. -/
unsafe def ensurePrimitive : IO Unit := do
  -- @@ENSURE BEGIN
  let _ ← IO.mkRef BLemma.INT_PRIME
  let _ ← IO.mkRef BPolyDiff.REAL_POLY_DIFF_EXPLICIT
  let _ ← IO.mkRef BLagrange.FINITE_INTSEG_RESTRICT
  let _ ← IO.mkRef BNumLagrange.NUM_LAGRANGE_LEMMA
  let _ ← IO.mkRef BCountOrders.COUNT_ORDERS_MODULO_PRIME
  let _ ← IO.mkRef BPrimitiveRoots.PRIMITIVE_ROOTS_MODULO_PRIME
  let _ ← IO.mkRef BPrimePows1.COPRIME_1_PLUS_POWER_STEP
  let _ ← IO.mkRef BPrimePows2.PRIMITIVE_ROOT_MODULO_PRIMEPOW
  let _ ← IO.mkRef BDouble.PRIMITIVE_ROOT_MODULO_2
  let _ ← IO.mkRef BDegenerate.PRIMITIVE_ROOT_MODULO_0
  let _ ← IO.mkRef BNegative.CONG_TO_1_POW2
  let _ ← IO.mkRef BEquivalences.PRIMITIVE_ROOT_EXISTS
  let _ ← IO.mkRef BCountPrimitiveRoots.COUNT_PRIMITIVE_ROOTS_ALT
  let _ ← IO.mkRef BCountRoots.COUNT_ROOTS_MODULO_PRIMITIVE_GEN_ALT
  let _ ← IO.mkRef BQuadraticResidues.INT_OF_NUM_POWER_RESIDUE
  let _ ← IO.mkRef BEulerCriterion.GENERALIZED_EULER_CRITERION
  let _ ← IO.mkRef BCountRootsOdd.COUNT_ROOTS_MODULO_ODD_GEN
  let _ ← IO.mkRef BCountRootsPrimitive.COUNT_ROOTS_MODULO_PRIMITIVE_ALT
  let _ ← IO.mkRef BQuadraticNonresidue.QUADRATIC_NONRESIDUE_EXISTS  -- @@ENSURE END
  pure ()

end SessionLibrary.Primitive
