/- File: SessionLibrary/Words.lean
The session half of the words.ml translation: it supplies HolLibrary.Words'
dependencies from Session and exports every name under its own name.
Importing this module is `needs "Library/words.ml"`: each bundle is built by
`initialize` when the module is loaded, in words.ml file order.  words.ml's
`needs "Library/bdd.ml"` (words.ml 39) is satisfied by importing
SessionLibrary.BDD; its four refs (65-69) are `IO.Ref`s.

Where the old Session exported a dependency bare, `deps` and `core1`..`core4`
take it from a Session bundle:
  AND_CLAUSES, DISJ_SYM, EQ_IMP, EQ_SYM_EQ, EXISTS_OR_THM, FORALL_AND_THM,
  OR_CLAUSES, RIGHT_OR_DISTRIB      -> T.*
  COND_CLAUSES, EXISTS_BOOL_THM, FORALL_BOOL_THM, bool_INDUCT -> C.*
  NOT_SUC, NUMERAL, SUC_INJ, num_CASES                        -> Nm.*
In `deps`: `mk_small_numeral` -> `HolMath.Nums.mk_small_numeral Nm.numK`;
`REAL_ARITH` -> `REAL_ARITH3`; `REAL_ARITH_TAC` -> `REAL_ARITH_TAC2`;
`BDD_DEFTAUT` -> `SessionLibrary.BDD.BDD_DEFTAUT`.
-/

import Session
import SessionLibrary.BDD
import HolLibrary.Words

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Words

/- words.ml's refs (words.ml 65-69). -/
initialize word_sizes : IO.Ref (List thm) ← IO.mkRef []
initialize word_pow2sizes : IO.Ref (List thm) ← IO.mkRef []
initialize word_SIZE_CONV : IO.Ref ioconv ← IO.mkRef (fun t => pure (HolCore.Equal.NO_CONV t))
initialize word_POW2SIZE_CONV : IO.Ref ioconv ← IO.mkRef (fun t => pure (HolCore.Equal.NO_CONV t))

/-- The core theorems words.ml uses, A-E. -/
def core1 : HolLibrary.Words.CoreThms1 where
  ADD := Session.ADD
  ADD1 := Session.ADD1
  ADD_AC := Session.ADD_AC
  ADD_ASSOC := Session.ADD_ASSOC
  ADD_CLAUSES := Session.ADD_CLAUSES
  ADD_EQ_0 := Session.ADD_EQ_0
  ADD_SUB := Session.ADD_SUB
  ADD_SUB2 := Session.ADD_SUB2
  ADD_SYM := Session.ADD_SYM
  AND_CLAUSES := Session.T.AND_CLAUSES
  AND_FORALL_THM := Session.AND_FORALL_THM
  ARITH := Session.ARITH
  ARITH_EQ := Session.ARITH_EQ
  ARITH_ODD := Session.ARITH_ODD
  ARITH_SUC := Session.ARITH_SUC
  ARITH_ZERO := Session.ARITH_ZERO
  BINARY_INDUCT := Session.BINARY_INDUCT
  BIT0 := Session.BIT0
  BIT1 := Session.BIT1
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARD_EQ_0 := Session.CARD_EQ_0
  CARD_IMAGE_INJ := Session.CARD_IMAGE_INJ
  CARD_IMAGE_LE := Session.CARD_IMAGE_LE
  CARD_NUMSEG_LT := Session.CARD_NUMSEG_LT
  CARD_SING := Session.CARD_SING
  CARD_SUBSET := Session.CARD_SUBSET
  CARD_UNION := Session.CARD_UNION
  CARD_UNION_EQ := Session.CARD_UNION_EQ
  CARD_UNION_GEN := Session.CARD_UNION_GEN
  CARD_UNION_LE := Session.CARD_UNION_LE
  CART_EQ := Session.CART_EQ
  COND_CLAUSES := Session.C.COND_CLAUSES
  COND_ID := Session.COND_ID
  COND_RAND := Session.COND_RAND
  COND_SWAP := Session.COND_SWAP
  CONG := Session.CONG
  CONG_DIV2 := Session.CONG_DIV2
  CONG_LMOD := Session.CONG_LMOD
  CONG_NSUM := Session.CONG_NSUM
  CONG_RMOD := Session.CONG_RMOD
  CONJ_ASSOC := Session.CONJ_ASSOC
  CONJ_SYM := Session.CONJ_SYM
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DIMINDEX_1 := Session.DIMINDEX_1
  DIMINDEX_2 := Session.DIMINDEX_2
  DIMINDEX_3 := Session.DIMINDEX_3
  DIMINDEX_4 := Session.DIMINDEX_4
  DIMINDEX_FINITE_SUM := Session.DIMINDEX_FINITE_SUM
  DIMINDEX_GE_1 := Session.DIMINDEX_GE_1
  DIMINDEX_NONZERO := Session.DIMINDEX_NONZERO
  DIMINDEX_TYBIT0 := Session.DIMINDEX_TYBIT0
  DIMINDEX_UNIQUE := Session.DIMINDEX_UNIQUE
  DISJOINT_EMPTY := Session.DISJOINT_EMPTY
  DISJOINT_SYM := Session.DISJOINT_SYM
  DISJ_SYM := Session.T.DISJ_SYM
  DIVIDES_DIV_MULT := Session.DIVIDES_DIV_MULT
  DIVIDES_LE := Session.DIVIDES_LE
  DIVIDES_MOD := Session.DIVIDES_MOD
  DIVISION := Session.DIVISION
  DIVISION_SIMP := Session.DIVISION_SIMP
  DIVMOD_UNIQ := Session.DIVMOD_UNIQ
  DIV_0 := Session.DIV_0
  DIV_1 := Session.DIV_1
  DIV_ADD_EQ := Session.DIV_ADD_EQ
  DIV_DIV := Session.DIV_DIV
  DIV_EQ_0 := Session.DIV_EQ_0
  DIV_EXP := Session.DIV_EXP
  DIV_LE := Session.DIV_LE
  DIV_LT := Session.DIV_LT
  DIV_MOD := Session.DIV_MOD
  DIV_MULT := Session.DIV_MULT
  DIV_MULT2 := Session.DIV_MULT2
  DIV_MULT_ADD := Session.DIV_MULT_ADD
  DIV_UNIQ := Session.DIV_UNIQ
  DIV_ZERO := Session.DIV_ZERO
  EMPTY_GSPEC := Session.EMPTY_GSPEC
  EQ_ADD_LCANCEL := Session.EQ_ADD_LCANCEL
  EQ_ADD_RCANCEL := Session.EQ_ADD_RCANCEL
  EQ_IMP := Session.T.EQ_IMP
  EQ_SYM_EQ := Session.T.EQ_SYM_EQ
  EQ_TRANS := Session.EQ_TRANS
  EVEN := Session.EVEN
  EVEN_ADD := Session.EVEN_ADD
  EVEN_EXISTS := Session.EVEN_EXISTS
  EVEN_EXP := Session.EVEN_EXP
  EVEN_MOD := Session.EVEN_MOD
  EVEN_MULT := Session.EVEN_MULT
  EXISTS_BOOL_THM := Session.C.EXISTS_BOOL_THM
  EXISTS_OR_THM := Session.T.EXISTS_OR_THM
  EXP := Session.EXP
  EXP_1 := Session.EXP_1
  EXP_2_NE_0 := Session.EXP_2_NE_0
  EXP_ADD := Session.EXP_ADD
  EXP_EQ_0 := Session.EXP_EQ_0
  EXP_EXP := Session.EXP_EXP
  EXP_LT_0 := Session.EXP_LT_0
  EXP_MULT := Session.EXP_MULT
  EXP_ONE := Session.EXP_ONE
  EXP_ZERO := Session.EXP_ZERO
  EXTENSION := Session.EXTENSION

/-- The core theorems words.ml uses, F-I. -/
def core2 : HolLibrary.Words.CoreThms2 where
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_NUMSEG := Session.FINITE_NUMSEG
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_RESTRICT := Session.FINITE_RESTRICT
  FINITE_SING := Session.FINITE_SING
  FINITE_SUBSET := Session.FINITE_SUBSET
  FINITE_UNION := Session.FINITE_UNION
  FORALL_AND_THM := Session.T.FORALL_AND_THM
  FORALL_BOOL_THM := Session.C.FORALL_BOOL_THM
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FUN_EQ_THM := Session.FUN_EQ_THM
  GE := Session.GE
  GT := Session.GT
  HAS_SIZE := Session.HAS_SIZE
  IMP_CONJ := Session.IMP_CONJ
  IMP_CONJ_ALT := Session.IMP_CONJ_ALT
  INSERT_UNION_EQ := Session.INSERT_UNION_EQ
  INTER_COMM := Session.INTER_COMM
  INTER_SUBSET := Session.INTER_SUBSET
  INT_ABS_MUL := Session.INT_ABS_MUL
  INT_ABS_NUM := Session.INT_ABS_NUM
  INT_ABS_POS := Session.INT_ABS_POS
  INT_ABS_POW := Session.INT_ABS_POW
  INT_ADD_RID := Session.INT_ADD_RID
  INT_CONG_DIV2 := Session.INT_CONG_DIV2
  INT_CONG_IMP_EQ := Session.INT_CONG_IMP_EQ
  INT_DIVISION := Session.INT_DIVISION
  INT_DIV_1 := Session.INT_DIV_1
  INT_DIV_DIV := Session.INT_DIV_DIV
  INT_DIV_EQ_0 := Session.INT_DIV_EQ_0
  INT_DIV_LT_EQ := Session.INT_DIV_LT_EQ
  INT_DIV_MUL := Session.INT_DIV_MUL
  INT_DIV_MUL_ADD := Session.INT_DIV_MUL_ADD
  INT_DIV_REM := Session.INT_DIV_REM
  INT_DIV_ZERO := Session.INT_DIV_ZERO
  INT_EQ_MUL_LCANCEL := Session.INT_EQ_MUL_LCANCEL
  INT_EQ_SUB_RADD := Session.INT_EQ_SUB_RADD
  INT_FORALL_POS := Session.INT_FORALL_POS
  INT_GE := Session.INT_GE
  INT_GT := Session.INT_GT
  INT_LE_DIV_EQ := Session.INT_LE_DIV_EQ
  INT_LE_LMUL_EQ := Session.INT_LE_LMUL_EQ
  INT_LE_MUL2 := Session.INT_LE_MUL2
  INT_LE_POW2 := Session.INT_LE_POW2
  INT_LE_REFL := Session.INT_LE_REFL
  INT_LE_RMUL := Session.INT_LE_RMUL
  INT_LE_TRANS := Session.INT_LE_TRANS
  INT_LT_IMP_LE := Session.INT_LT_IMP_LE
  INT_LT_IMP_NE := Session.INT_LT_IMP_NE
  INT_LT_LMUL_EQ := Session.INT_LT_LMUL_EQ
  INT_LT_POW2 := Session.INT_LT_POW2
  INT_MAX := Session.INT_MAX
  INT_MIN := Session.INT_MIN
  INT_MUL_ASSOC := Session.INT_MUL_ASSOC
  INT_MUL_RID := Session.INT_MUL_RID
  INT_MUL_RNEG := Session.INT_MUL_RNEG
  INT_MUL_RZERO := Session.INT_MUL_RZERO
  INT_MUL_SYM := Session.INT_MUL_SYM
  INT_NEG_LT0 := Session.INT_NEG_LT0
  INT_NOT_LE := Session.INT_NOT_LE
  INT_NOT_LT := Session.INT_NOT_LT
  INT_OF_NUM_ADD := Session.INT_OF_NUM_ADD
  INT_OF_NUM_CLAUSES := Session.INT_OF_NUM_CLAUSES
  INT_OF_NUM_DIV := Session.INT_OF_NUM_DIV
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_LE := Session.INT_OF_NUM_LE
  INT_OF_NUM_LT := Session.INT_OF_NUM_LT
  INT_OF_NUM_MUL := Session.INT_OF_NUM_MUL
  INT_OF_NUM_OF_INT := Session.INT_OF_NUM_OF_INT
  INT_OF_NUM_POW := Session.INT_OF_NUM_POW
  INT_OF_NUM_REM := Session.INT_OF_NUM_REM
  INT_OF_NUM_SUB := Session.INT_OF_NUM_SUB
  INT_POS := Session.INT_POS
  INT_POW := Session.INT_POW
  INT_POW_ADD := Session.INT_POW_ADD
  INT_POW_EQ_0 := Session.INT_POW_EQ_0
  INT_POW_LE := Session.INT_POW_LE
  INT_POW_MONO := Session.INT_POW_MONO
  INT_REM_EQ := Session.INT_REM_EQ
  INT_REM_EQ_0 := Session.INT_REM_EQ_0
  INT_REM_MOD_SELF := Session.INT_REM_MOD_SELF
  INT_REM_REM := Session.INT_REM_REM
  INT_REM_REM_POW_MIN := Session.INT_REM_REM_POW_MIN
  INT_REM_UNIQUE := Session.INT_REM_UNIQUE
  INT_SUB_0 := Session.INT_SUB_0
  INT_SUB_LZERO := Session.INT_SUB_LZERO
  IN_ELIM_PAIR_THM := Session.IN_ELIM_PAIR_THM
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_INTER := Session.IN_INTER
  IN_NUMSEG := Session.IN_NUMSEG
  IN_SING := Session.IN_SING
  IN_UNION := Session.IN_UNION
  IN_UNIV := Session.IN_UNIV

/-- The core theorems words.ml uses, J-Q. -/
def core3 : HolLibrary.Words.CoreThms3 where
  LAMBDA_BETA := Session.LAMBDA_BETA
  LDIV_LT_EQ := Session.LDIV_LT_EQ
  LE := Session.LE
  LEFT_ADD_DISTRIB := Session.LEFT_ADD_DISTRIB
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LEFT_SUB_DISTRIB := Session.LEFT_SUB_DISTRIB
  LET_ADD2 := Session.LET_ADD2
  LET_TRANS := Session.LET_TRANS
  LE_0 := Session.LE_0
  LE_1 := Session.LE_1
  LE_ADD := Session.LE_ADD
  LE_ADD2 := Session.LE_ADD2
  LE_ADD_LCANCEL := Session.LE_ADD_LCANCEL
  LE_ANTISYM := Session.LE_ANTISYM
  LE_CASES := Session.LE_CASES
  LE_EXISTS := Session.LE_EXISTS
  LE_EXP := Session.LE_EXP
  LE_LT := Session.LE_LT
  LE_MINIMAL := Session.LE_MINIMAL
  LE_MULT_LCANCEL := Session.LE_MULT_LCANCEL
  LE_MULT_RCANCEL := Session.LE_MULT_RCANCEL
  LE_REFL := Session.LE_REFL
  LE_SUC_LT := Session.LE_SUC_LT
  LE_TRANS := Session.LE_TRANS
  LT := Session.LT
  LTE_TRANS := Session.LTE_TRANS
  LT_ADD2 := Session.LT_ADD2
  LT_ADD_LCANCEL := Session.LT_ADD_LCANCEL
  LT_EXISTS := Session.LT_EXISTS
  LT_EXP := Session.LT_EXP
  LT_IMP_LE := Session.LT_IMP_LE
  LT_LE := Session.LT_LE
  LT_MULT2 := Session.LT_MULT2
  LT_MULT_LCANCEL := Session.LT_MULT_LCANCEL
  LT_POW2_REFL := Session.LT_POW2_REFL
  LT_REFL := Session.LT_REFL
  LT_TRANS := Session.LT_TRANS
  MAX := Session.MAX
  MIN := Session.MIN
  MINIMAL := Session.MINIMAL
  MINIMAL_LE := Session.MINIMAL_LE
  MINIMAL_UBOUND := Session.MINIMAL_UBOUND
  MINIMAL_UNIQUE := Session.MINIMAL_UNIQUE
  MOD_0 := Session.MOD_0
  MOD_1 := Session.MOD_1
  MOD_2_CASES := Session.MOD_2_CASES
  MOD_ADD_CASES := Session.MOD_ADD_CASES
  MOD_ADD_MOD := Session.MOD_ADD_MOD
  MOD_CASES := Session.MOD_CASES
  MOD_EQ_0 := Session.MOD_EQ_0
  MOD_EQ_SELF := Session.MOD_EQ_SELF
  MOD_LE := Session.MOD_LE
  MOD_LT := Session.MOD_LT
  MOD_LT_EQ := Session.MOD_LT_EQ
  MOD_LT_EQ_LT := Session.MOD_LT_EQ_LT
  MOD_MOD := Session.MOD_MOD
  MOD_MOD_EXP_MIN := Session.MOD_MOD_EXP_MIN
  MOD_MOD_REFL := Session.MOD_MOD_REFL
  MOD_MULT := Session.MOD_MULT
  MOD_MULT2 := Session.MOD_MULT2
  MOD_MULT_ADD := Session.MOD_MULT_ADD
  MOD_MULT_MOD := Session.MOD_MULT_MOD
  MOD_NSUM_MOD_NUMSEG := Session.MOD_NSUM_MOD_NUMSEG
  MOD_REFL := Session.MOD_REFL
  MOD_UNIQ := Session.MOD_UNIQ
  MOD_ZERO := Session.MOD_ZERO
  MONO_EXISTS := Session.MONO_EXISTS
  MONO_FORALL := Session.MONO_FORALL
  MULT_2 := Session.MULT_2
  MULT_AC := Session.MULT_AC
  MULT_ASSOC := Session.MULT_ASSOC
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_EQ_0 := Session.MULT_EQ_0
  MULT_SYM := Session.MULT_SYM
  NOT_EVEN := Session.NOT_EVEN
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NOT_LE := Session.NOT_LE
  NOT_LT := Session.NOT_LT
  NOT_ODD := Session.NOT_ODD
  NOT_SUC := Session.Nm.NOT_SUC
  NSUM_ADD := Session.NSUM_ADD
  NSUM_ADD_NUMSEG := Session.NSUM_ADD_NUMSEG
  NSUM_CLAUSES := Session.NSUM_CLAUSES
  NSUM_CLAUSES_LEFT := Session.NSUM_CLAUSES_LEFT
  NSUM_CLAUSES_NUMSEG := Session.NSUM_CLAUSES_NUMSEG
  NSUM_CLAUSES_NUMSEG_LT := Session.NSUM_CLAUSES_NUMSEG_LT
  NSUM_CLOSED := Session.NSUM_CLOSED
  NSUM_CONST := Session.NSUM_CONST
  NSUM_DELTA := Session.NSUM_DELTA
  NSUM_EQ := Session.NSUM_EQ
  NSUM_EQ_0_IFF := Session.NSUM_EQ_0_IFF
  NSUM_EQ_GENERAL_INVERSES := Session.NSUM_EQ_GENERAL_INVERSES
  NSUM_GROUP := Session.NSUM_GROUP
  NSUM_IMAGE := Session.NSUM_IMAGE
  NSUM_LE := Session.NSUM_LE
  NSUM_LMUL := Session.NSUM_LMUL
  NSUM_NSUM_PRODUCT := Session.NSUM_NSUM_PRODUCT
  NSUM_OFFSET := Session.NSUM_OFFSET
  NSUM_REFLECT := Session.NSUM_REFLECT
  NSUM_RESTRICT_SET := Session.NSUM_RESTRICT_SET
  NSUM_RMUL := Session.NSUM_RMUL
  NSUM_SING := Session.NSUM_SING
  NSUM_SUPERSET := Session.NSUM_SUPERSET
  NSUM_UNION := Session.NSUM_UNION
  NSUM_UNION_EQ := Session.NSUM_UNION_EQ
  NUMERAL := Session.Nm.NUMERAL
  NUMSEG_CLAUSES_LT := Session.NUMSEG_CLAUSES_LT
  NUMSEG_LT := Session.NUMSEG_LT
  NUMSEG_LT_DIMINDEX := Session.NUMSEG_LT_DIMINDEX
  NUM_OF_INT_OF_NUM := Session.NUM_OF_INT_OF_NUM
  ODD := Session.ODD
  ODD_ADD := Session.ODD_ADD
  ODD_EXP := Session.ODD_EXP
  ODD_MOD := Session.ODD_MOD
  ODD_MOD_EVEN := Session.ODD_MOD_EVEN
  ODD_MULT := Session.ODD_MULT
  ODD_SUB := Session.ODD_SUB
  OR_CLAUSES := Session.T.OR_CLAUSES
  PAIR_EQ := Session.PAIR_EQ

/-- The core theorems words.ml uses, R-Z and lower case. -/
def core4 : HolLibrary.Words.CoreThms4 where
  RDIV_LT_EQ := Session.RDIV_LT_EQ
  REAL_OF_INT_CLAUSES := Session.REAL_OF_INT_CLAUSES
  REAL_OF_NUM_ADD := Session.REAL_OF_NUM_ADD
  REAL_OF_NUM_CLAUSES := Session.REAL_OF_NUM_CLAUSES
  REAL_OF_NUM_EQ := Session.REAL_OF_NUM_EQ
  REAL_OF_NUM_LE := Session.REAL_OF_NUM_LE
  REAL_OF_NUM_POW := Session.REAL_OF_NUM_POW
  REAL_OF_NUM_SUB := Session.REAL_OF_NUM_SUB
  REAL_OF_NUM_SUM := Session.REAL_OF_NUM_SUM
  REAL_OF_NUM_SUM_NUMSEG := Session.REAL_OF_NUM_SUM_NUMSEG
  REAL_SUB_0 := Session.REAL_SUB_0
  REAL_SUB_LE := Session.REAL_SUB_LE
  REAL_SUB_RZERO := Session.REAL_SUB_RZERO
  RIGHT_ADD_DISTRIB := Session.RIGHT_ADD_DISTRIB
  RIGHT_OR_DISTRIB := Session.T.RIGHT_OR_DISTRIB
  SING_GSPEC := Session.SING_GSPEC
  SUBSET := Session.SUBSET
  SUBSET_INTER_ABSORPTION := Session.SUBSET_INTER_ABSORPTION
  SUB_0 := Session.SUB_0
  SUB_ADD := Session.SUB_ADD
  SUB_EQ_0 := Session.SUB_EQ_0
  SUB_REFL := Session.SUB_REFL
  SUC_INJ := Session.Nm.SUC_INJ
  SUC_SUB1 := Session.SUC_SUB1
  SUM_ADD := Session.SUM_ADD
  SUM_ADD_NUMSEG := Session.SUM_ADD_NUMSEG
  SUM_DIFFS_ALT := Session.SUM_DIFFS_ALT
  SUM_EQ_0_NUMSEG := Session.SUM_EQ_0_NUMSEG
  SUM_LMUL := Session.SUM_LMUL
  SUM_NEG := Session.SUM_NEG
  SUM_RMUL := Session.SUM_RMUL
  SUM_SUB := Session.SUM_SUB
  SUM_SUB_NUMSEG := Session.SUM_SUB_NUMSEG
  UNION_EMPTY := Session.UNION_EMPTY
  UNWIND_THM2 := Session.UNWIND_THM2
  bool_INDUCT := Session.C.bool_INDUCT
  divides := Session.divides
  int_divides := Session.int_divides
  int_of_num := Session.int_of_num
  num_CASES := Session.Nm.num_CASES
  num_INDUCTION := Session.num_INDUCTION
  num_congruent := Session.num_congruent
  num_divides := Session.num_divides
  numseg := Session.numseg
  o_DEF := Session.o_DEF

/-- What words.ml uses from Session. -/
def deps : HolLibrary.Words.WordsDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  new_type_definition ty names th :=
    ExceptT.mk (Session.new_type_definition ty names.1 names.2 th)
  new_type_abbrev := Session.new_type_abbrev
  define s := do ExceptT.mk (Session.define (← HolLight.q s))
  word_sizes := word_sizes
  word_pow2sizes := word_pow2sizes
  word_SIZE_CONV := word_SIZE_CONV
  word_POW2SIZE_CONV := word_POW2SIZE_CONV
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  ASM_INT_ARITH_TAC := Session.ASM_INT_ARITH_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  HAS_SIZE_DIMINDEX_RULE ty := ExceptT.mk (Session.HAS_SIZE_DIMINDEX_RULE ty)
  INDUCT_TAC := Session.INDUCT_TAC
  INTEGER_RULE t := ExceptT.mk (Session.INTEGER_RULE t)
  INT_ARITH t := ExceptT.mk (Session.INT_ARITH t)
  INT_ARITH_TAC := Session.INT_ARITH_TAC
  INT_RING t := ExceptT.mk (Session.INT_RING t)
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  NUMBER_RULE t := ExceptT.mk (Session.NUMBER_RULE t)
  REAL_ARITH t := ExceptT.mk (Session.REAL_ARITH3 t)
  REAL_ARITH_TAC := Session.REAL_ARITH_TAC2
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  mk_small_numeral := HolMath.Nums.mk_small_numeral Session.Nm.numK
  mk_intconst := Session.mk_intconst
  BITS_ELIM_CONV t := do
    match ← Session.BITS_ELIM_CONV with
    | .ok c => pure (c t)
    | .error e => pure (.error e)
  DIMINDEX_CONV t := pure (Session.DIMINDEX_CONV t)
  EXPAND_CASES_CONV := Session.EXPAND_CASES_CONV
  EXPAND_NSUM_CONV := Session.EXPAND_NSUM_CONV
  INT_ABS_CONV := Session.INT_ABS_CONV
  INT_DIV_CONV := Session.INT_DIV_CONV
  INT_GE_CONV := Session.INT_GE_CONV
  INT_GT_CONV := Session.INT_GT_CONV
  INT_LE_CONV := Session.INT_LE_CONV
  INT_LT_CONV := Session.INT_LT_CONV
  INT_MUL_CONV := Session.INT_MUL_CONV
  INT_POLY_CONV := Session.INT_POLY_CONV
  INT_POW_CONV := Session.INT_POW_CONV
  INT_REDUCE_CONV := Session.INT_REDUCE_CONV
  INT_RED_CONV := Session.INT_RED_CONV
  INT_REM_CONV := Session.INT_REM_CONV
  INT_REM_DOWN_CONV := Session.INT_REM_DOWN_CONV
  INT_SGN_CONV := Session.INT_SGN_CONV
  INT_SUB_CONV := Session.INT_SUB_CONV
  MOD_DOWN_CONV := Session.MOD_DOWN_CONV
  NUM_ADD_CONV := Session.NUM_ADD_CONV
  NUM_DIV_CONV := Session.NUM_DIV_CONV
  NUM_EQ_CONV := Session.NUM_EQ_CONV
  NUM_EVEN_CONV := Session.NUM_EVEN_CONV
  NUM_EXP_CONV := Session.NUM_EXP_CONV
  NUM_GE_CONV := Session.NUM_GE_CONV
  NUM_GT_CONV := Session.NUM_GT_CONV
  NUM_LE_CONV := Session.NUM_LE_CONV
  NUM_LT_CONV := Session.NUM_LT_CONV
  NUM_MAX_CONV := Session.NUM_MAX_CONV
  NUM_MIN_CONV := Session.NUM_MIN_CONV
  NUM_MOD_CONV := Session.NUM_MOD_CONV
  NUM_MULT_CONV := Session.NUM_MULT_CONV
  NUM_ODD_CONV := Session.NUM_ODD_CONV
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  NUM_RED_CONV := Session.NUM_RED_CONV
  NUM_SUB_CONV := Session.NUM_SUB_CONV
  NUM_SUC_CONV := Session.NUM_SUC_CONV
  num_CONV := Session.num_CONV
  prove_general_recursive_function_exists := Session.prove_general_recursive_function_exists
  bool_compset := Session.bool_compset
  set_skip := Session.set_skip
  add_conv := Session.add_conv
  WEAK_CBV_CONV := Session.WEAK_CBV_CONV
  let_CONV := Session.let_CONV
  BDD_DEFTAUT := SessionLibrary.BDD.BDD_DEFTAUT
  REAL_POLY_CONV := Session.REAL_POLY_CONV
  core1 := core1
  core2 := core2
  core3 := core3
  core4 := core4

/-- Build a bundle once, eagerly (a failed setup throws, as Session panics). -/
private def ioW {α : Type} [Inhabited α] (what : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← x with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"{what} failed: {e}")

/- The bundles, in words.ml order.  `initialize` declaration order IS the
   forcing order (so each builds every earlier bundle first, as HOL Light's
   load does); Session's `let _ ← IO.mkRef <prev field>` force-lines are
   therefore redundant and dropped.  `needs "Library/bdd.ml"` already ran via
   the Session.BDD import. -/

initialize BWordSizes : HolLibrary.Words.WordSizes ←
  ioW "setupWordSizes" (HolLibrary.Words.setupWordSizes deps).run

initialize BDigitsum : HolLibrary.Words.Digitsum ←
  ioW "setupDigitsum" (HolLibrary.Words.setupDigitsum deps).run

initialize BBitval : HolLibrary.Words.Bitval ←
  ioW "setupBitval" (HolLibrary.Words.setupBitval deps).run

initialize BBinary : HolLibrary.Words.Binary ←
  ioW "setupBinary" (HolLibrary.Words.setupBinary deps BDigitsum BBitval).run

initialize BWordType : HolLibrary.Words.WordType ←
  ioW "setupWordType" (HolLibrary.Words.setupWordType deps).run

initialize BBitsOfWord : HolLibrary.Words.BitsOfWord ←
  ioW "setupBitsOfWord" (HolLibrary.Words.setupBitsOfWord deps BWordType).run

initialize BVal : HolLibrary.Words.Val ←
  ioW "setupVal" (HolLibrary.Words.setupVal deps BBinary BBitval BWordType BBitsOfWord).run

initialize BIval : HolLibrary.Words.Ival ←
  ioW "setupIval" (HolLibrary.Words.setupIval deps BBitval BVal).run

initialize BNumBits : HolLibrary.Words.NumBits ←
  ioW "setupNumBits" (HolLibrary.Words.setupNumBits deps BDigitsum BBitsOfWord BVal).run

initialize BNumShiftAdd : HolLibrary.Words.NumShiftAdd ←
  ioW "setupNumShiftAdd" (HolLibrary.Words.setupNumShiftAdd deps BNumBits).run

initialize BLimits : HolLibrary.Words.Limits ←
  ioW "setupLimits" (HolLibrary.Words.setupLimits deps BBitval BVal BIval).run

initialize BPopcount : HolLibrary.Words.Popcount ←
  ioW "setupPopcount" (HolLibrary.Words.setupPopcount deps BBitval BWordType BBitsOfWord BVal).run

initialize BGeneralOps : HolLibrary.Words.GeneralOps ←
  ioW "setupGeneralOps" (HolLibrary.Words.setupGeneralOps deps BWordType BVal BIval).run

initialize BWordOps1 : HolLibrary.Words.WordOps1 ←
  ioW "setupWordOps1" (HolLibrary.Words.setupWordOps1 deps BBitval BWordType BBitsOfWord BVal BIval BPopcount BGeneralOps).run

initialize BWordOps2 : HolLibrary.Words.WordOps2 ←
  ioW "setupWordOps2" (HolLibrary.Words.setupWordOps2 deps BBitval BBinary BWordType BBitsOfWord BVal BIval BGeneralOps BWordOps1).run

initialize BWordOps3 : HolLibrary.Words.WordOps3 ←
  ioW "setupWordOps3" (HolLibrary.Words.setupWordOps3 deps BWordType BBitsOfWord BVal BIval BPopcount BGeneralOps BWordOps1 BWordOps2).run

initialize BWordRule : HolLibrary.Words.WordRule ←
  ioW "setupWordRule" (HolLibrary.Words.setupWordRule deps BBitval BVal BIval BWordOps1 BWordOps2).run

initialize BWordBitwise : HolLibrary.Words.WordBitwise ←
  ioW "setupWordBitwise" (HolLibrary.Words.setupWordBitwise deps BWordType BBitsOfWord BVal BWordOps1).run

initialize BWordArith : HolLibrary.Words.WordArith ←
  ioW "setupWordArith" (HolLibrary.Words.setupWordArith deps BVal BIval BLimits BGeneralOps BWordOps1 BWordOps2 BWordOps3 BWordRule).run

initialize BValExpand : HolLibrary.Words.ValExpand ←
  ioW "setupValExpand" (HolLibrary.Words.setupValExpand deps BVal).run

initialize BZxSx : HolLibrary.Words.ZxSx ←
  ioW "setupZxSx" (HolLibrary.Words.setupZxSx deps BBitval BBinary BWordType BVal BIval BWordOps1 BWordOps2 BWordOps3 BWordRule).run

initialize BJoinSubword : HolLibrary.Words.JoinSubword ←
  ioW "setupJoinSubword" (HolLibrary.Words.setupJoinSubword deps BDigitsum BBinary BWordType BVal BIval BWordOps1 BWordOps2 BWordOps3 BZxSx).run

initialize BInsertDup : HolLibrary.Words.InsertDup ←
  ioW "setupInsertDup" (HolLibrary.Words.setupInsertDup deps BBinary BWordType BBitsOfWord BVal BZxSx BJoinSubword).run

initialize BBitRec : HolLibrary.Words.BitRec ←
  ioW "setupBitRec" (HolLibrary.Words.setupBitRec deps BBitval BWordType BVal BWordOps1 BWordRule).run

initialize BMisc1 : HolLibrary.Words.Misc1 ←
  ioW "setupMisc1" (HolLibrary.Words.setupMisc1 deps BBitval BWordType BBitsOfWord BVal BIval BLimits BPopcount BWordOps1 BWordOps2 BWordOps3 BWordRule BWordBitwise BZxSx BJoinSubword BBitRec).run

initialize BMasks : HolLibrary.Words.Masks ←
  ioW "setupMasks" (HolLibrary.Words.setupMasks deps BBitval BBinary BWordType BBitsOfWord BVal BIval BWordOps1 BWordOps2 BWordOps3 BWordRule BWordBitwise BZxSx BMisc1).run

initialize BClzCtz : HolLibrary.Words.ClzCtz ←
  ioW "setupClzCtz" (HolLibrary.Words.setupClzCtz deps BBitval BWordType BBitsOfWord BVal BPopcount BWordOps1 BWordOps3 BWordRule BMisc1 BMasks).run

initialize BReverse : HolLibrary.Words.Reverse ←
  ioW "setupReverse" (HolLibrary.Words.setupReverse deps BBitval BWordType BBitsOfWord BVal BWordOps1 BWordOps2 BWordOps3 BZxSx BClzCtz).run

initialize BAlign : HolLibrary.Words.Align ←
  ioW "setupAlign" (HolLibrary.Words.setupAlign deps BVal BIval BWordOps1 BWordOps2 BWordOps3 BWordRule BWordBitwise BMisc1).run

initialize BTopflip : HolLibrary.Words.Topflip ←
  ioW "setupTopflip" (HolLibrary.Words.setupTopflip deps BVal BIval BLimits BGeneralOps BWordOps1 BWordOps3 BWordBitwise BWordArith BMisc1 BAlign).run

initialize BBitWordConv : HolLibrary.Words.BitWordConv ←
  ioW "setupBitWordConv" (HolLibrary.Words.setupBitWordConv deps BWordType BVal BWordOps1 BWordOps2 BWordOps3 BZxSx BJoinSubword BInsertDup BBitRec BMasks BReverse).run

initialize BBlast : HolLibrary.Words.Blast ←
  ioW "setupBlast" (HolLibrary.Words.setupBlast deps BBitval BVal BPopcount BWordOps1 BWordOps3 BWordRule BValExpand BZxSx BBitRec BMisc1 BMasks BBitWordConv).run

initialize BReduce1 : HolLibrary.Words.Reduce1 ←
  ioW "setupReduce1" (HolLibrary.Words.setupReduce1 deps BBitval BVal BIval BLimits BGeneralOps BWordOps1 BWordOps2 BWordOps3 BReverse).run

initialize BReduce2 : HolLibrary.Words.Reduce2 ←
  ioW "setupReduce2" (HolLibrary.Words.setupReduce2 deps BWordType BBitsOfWord BVal BPopcount BWordOps1 BWordOps3 BZxSx BJoinSubword BInsertDup BReduce1).run

initialize BReduce3 : HolLibrary.Words.Reduce3 ←
  ioW "setupReduce3" (HolLibrary.Words.setupReduce3 deps BDigitsum BBitval BWordType BVal BPopcount BGeneralOps BClzCtz BReverse BAlign BBitWordConv BReduce1 BReduce2).run

initialize BWordify : HolLibrary.Words.Wordify ←
  ioW "setupWordify" (HolLibrary.Words.setupWordify deps BBitval BWordType BVal BIval BWordOps1 BWordOps2 BWordArith BZxSx BMisc1 BReduce1 BReduce3).run

initialize BBitblast : HolLibrary.Words.Bitblast ←
  ioW "setupBitblast" (HolLibrary.Words.setupBitblast deps BBitval BWordType BVal BLimits BPopcount BGeneralOps BWordOps1 BWordOps3 BValExpand BMisc1 BMasks BClzCtz BReverse BBitWordConv BBlast BReduce3 BWordify).run

initialize BSimd : HolLibrary.Words.Simd ←
  ioW "setupSimd" (HolLibrary.Words.setupSimd deps BWordType BJoinSubword).run

/- ---------------------------------------------------------------------- -/
/- words.ml bare re-exports (plain `def`s, same names/order as Session).   -/
/- ---------------------------------------------------------------------- -/
-- WordSizes
def HAS_SIZE_8 : thm := BWordSizes.HAS_SIZE_8
def HAS_SIZE_16 : thm := BWordSizes.HAS_SIZE_16
def HAS_SIZE_32 : thm := BWordSizes.HAS_SIZE_32
def HAS_SIZE_64 : thm := BWordSizes.HAS_SIZE_64
def HAS_SIZE_128 : thm := BWordSizes.HAS_SIZE_128
def HAS_SIZE_256 : thm := BWordSizes.HAS_SIZE_256
def HAS_SIZE_512 : thm := BWordSizes.HAS_SIZE_512
def DIMINDEX_8 : thm := BWordSizes.DIMINDEX_8
def DIMINDEX_16 : thm := BWordSizes.DIMINDEX_16
def DIMINDEX_32 : thm := BWordSizes.DIMINDEX_32
def DIMINDEX_64 : thm := BWordSizes.DIMINDEX_64
def DIMINDEX_128 : thm := BWordSizes.DIMINDEX_128
def DIMINDEX_256 : thm := BWordSizes.DIMINDEX_256
def DIMINDEX_512 : thm := BWordSizes.DIMINDEX_512
def add_word_sizes := BWordSizes.add_word_sizes

-- Digitsum
def DIGITSUM_WORKS_GEN : thm := BDigitsum.DIGITSUM_WORKS_GEN
def DIGITSUM_WORKS : thm := BDigitsum.DIGITSUM_WORKS
def DIGITSUM_BOUND : thm := BDigitsum.DIGITSUM_BOUND
def DIGITSUM_SPLIT : thm := BDigitsum.DIGITSUM_SPLIT
def DIGITSUM_DIV : thm := BDigitsum.DIGITSUM_DIV
def DIGITSUM_MOD : thm := BDigitsum.DIGITSUM_MOD
def DIGITSUM_MOD_NUMSEG : thm := BDigitsum.DIGITSUM_MOD_NUMSEG
def DIGITSUM_DIV_NUMSEG : thm := BDigitsum.DIGITSUM_DIV_NUMSEG
def DIGITSUM_DIV_MOD : thm := BDigitsum.DIGITSUM_DIV_MOD
def DIGITSUM_UNIQUE : thm := BDigitsum.DIGITSUM_UNIQUE

-- Bitval
def bitval : thm := BBitval.bitval
def BITVAL_CLAUSES : thm := BBitval.BITVAL_CLAUSES
def BITVAL_BOUND : thm := BBitval.BITVAL_BOUND
def BITVAL_BOUND_ALT : thm := BBitval.BITVAL_BOUND_ALT
def ODD_BITVAL : thm := BBitval.ODD_BITVAL
def EVEN_BITVAL : thm := BBitval.EVEN_BITVAL
def NUM_AS_BITVAL : thm := BBitval.NUM_AS_BITVAL
def NUM_AS_BITVAL_ALT : thm := BBitval.NUM_AS_BITVAL_ALT
def BITVAL_EQ_0 : thm := BBitval.BITVAL_EQ_0
def BITVAL_EQ_1 : thm := BBitval.BITVAL_EQ_1
def BITVAL_POS : thm := BBitval.BITVAL_POS
def BITVAL_NOT : thm := BBitval.BITVAL_NOT
def BITVAL_AND : thm := BBitval.BITVAL_AND
def BITVAL_OR : thm := BBitval.BITVAL_OR
def BITVAL_IFF : thm := BBitval.BITVAL_IFF
def BITVAL_XOR : thm := BBitval.BITVAL_XOR
def BITVAL_EXP : thm := BBitval.BITVAL_EXP
def INT_BITVAL_NOT : thm := BBitval.INT_BITVAL_NOT
def INT_BITVAL_AND : thm := BBitval.INT_BITVAL_AND
def INT_BITVAL_OR : thm := BBitval.INT_BITVAL_OR
def INT_BITVAL_IMP : thm := BBitval.INT_BITVAL_IMP
def INT_BITVAL_IFF : thm := BBitval.INT_BITVAL_IFF
def INT_BITVAL_POW : thm := BBitval.INT_BITVAL_POW
def REAL_BITVAL_NOT : thm := BBitval.REAL_BITVAL_NOT
def BITVAL_ODD : thm := BBitval.BITVAL_ODD
def LE_BITVAL : thm := BBitval.LE_BITVAL
def INT_LE_BITVAL : thm := BBitval.INT_LE_BITVAL
def REAL_LE_BITVAL : thm := BBitval.REAL_LE_BITVAL
def EQ_BITVAL : thm := BBitval.EQ_BITVAL
def INT_EQ_BITVAL : thm := BBitval.INT_EQ_BITVAL
def REAL_EQ_BITVAL : thm := BBitval.REAL_EQ_BITVAL
def BINT_POLY_CONV : HolCore.Equal.ioconv := fun t => BBitval.BINT_POLY_CONV t

-- Binary
def ODD_MOD_POW2 : thm := BBinary.ODD_MOD_POW2
def BINARY_DIGITSUM_BOUND : thm := BBinary.BINARY_DIGITSUM_BOUND
def BINARY_DIGITSUM_SPLIT : thm := BBinary.BINARY_DIGITSUM_SPLIT
def BINARY_DIGITSUM_DIV : thm := BBinary.BINARY_DIGITSUM_DIV
def BINARY_DIGITSUM_MOD : thm := BBinary.BINARY_DIGITSUM_MOD

-- WordType
def word_tybij : thm := BWordType.word_tybij
def WORD_EQ_BITVECTOR : thm := BWordType.WORD_EQ_BITVECTOR
def bit : thm := BWordType.bit
def WORD_EQ_BITS_ALT : thm := BWordType.WORD_EQ_BITS_ALT
def WORD_EQ_BITS : thm := BWordType.WORD_EQ_BITS
def BIT_TRIVIAL : thm := BWordType.BIT_TRIVIAL
def BIT_GUARD : thm := BWordType.BIT_GUARD

-- BitsOfWord
def bits_of_word : thm := BBitsOfWord.bits_of_word
def word_of_bits : thm := BBitsOfWord.word_of_bits
def IN_BITS_OF_WORD : thm := BBitsOfWord.IN_BITS_OF_WORD
def BIT_WORD_OF_BITS : thm := BBitsOfWord.BIT_WORD_OF_BITS
def WORD_OF_BITS_EQ : thm := BBitsOfWord.WORD_OF_BITS_EQ
def WORD_OF_BITS_OF_WORD : thm := BBitsOfWord.WORD_OF_BITS_OF_WORD
def BITS_OF_WORD_OF_BITS : thm := BBitsOfWord.BITS_OF_WORD_OF_BITS
def BITS_OF_WORD_EQ : thm := BBitsOfWord.BITS_OF_WORD_EQ
def WORD_OF_BITS : thm := BBitsOfWord.WORD_OF_BITS
def WORD_OF_BITS_ALT : thm := BBitsOfWord.WORD_OF_BITS_ALT
def FINITE_BITS_OF_WORD : thm := BBitsOfWord.FINITE_BITS_OF_WORD
def BITS_OF_WORD_SUBSET : thm := BBitsOfWord.BITS_OF_WORD_SUBSET
def BITS_OF_WORD_SUBSET_ALT : thm := BBitsOfWord.BITS_OF_WORD_SUBSET_ALT
def BITS_OF_WORD_SUBSET_NUMSEG : thm := BBitsOfWord.BITS_OF_WORD_SUBSET_NUMSEG

-- Val
def val_def : thm := BVal.val_def
def VAL : thm := BVal.VAL
def word : thm := BVal.word
def BIT_WORD : thm := BVal.BIT_WORD
def BIT_LSB_WORD : thm := BVal.BIT_LSB_WORD
def BIT_WORD_0 : thm := BVal.BIT_WORD_0
def BITS_OF_WORD_0 : thm := BVal.BITS_OF_WORD_0
def BITS_OF_WORD_EQ_EMPTY : thm := BVal.BITS_OF_WORD_EQ_EMPTY
def WORD_OF_BITS_EMPTY : thm := BVal.WORD_OF_BITS_EMPTY
def BITVAL_BIT_WORD : thm := BVal.BITVAL_BIT_WORD
def WORD_VAL : thm := BVal.WORD_VAL
def VAL_WORD : thm := BVal.VAL_WORD
def MOD_VAL_WORD : thm := BVal.MOD_VAL_WORD
def DIVIDES_VAL_WORD : thm := BVal.DIVIDES_VAL_WORD
def VAL_WORD_LE : thm := BVal.VAL_WORD_LE
def VAL_WORD_LT : thm := BVal.VAL_WORD_LT
def FORALL_WORD : thm := BVal.FORALL_WORD
def EXISTS_WORD : thm := BVal.EXISTS_WORD
def VAL_WORD_0 : thm := BVal.VAL_WORD_0
def VAL_WORD_1 : thm := BVal.VAL_WORD_1
def WORD_BITVAL : thm := BVal.WORD_BITVAL
def VAL_WORD_BITVAL : thm := BVal.VAL_WORD_BITVAL
def VAL_WORD_EQ : thm := BVal.VAL_WORD_EQ
def VAL_EQ : thm := BVal.VAL_EQ
def VAL_EQ_0 : thm := BVal.VAL_EQ_0
def VAL_EQ_1 : thm := BVal.VAL_EQ_1
def VAL_EQ_BITVAL : thm := BVal.VAL_EQ_BITVAL
def WORD_BITVAL_EQ_0 : thm := BVal.WORD_BITVAL_EQ_0
def WORD_BITVAL_EQ_1 : thm := BVal.WORD_BITVAL_EQ_1
def WORD_NE_10 : thm := BVal.WORD_NE_10
def WORD_EQ : thm := BVal.WORD_EQ
def WORD_EQ_IMP : thm := BVal.WORD_EQ_IMP
def WORD_EQ_0 : thm := BVal.WORD_EQ_0
def VAL_BOUND : thm := BVal.VAL_BOUND
def INT_VAL_BOUND : thm := BVal.INT_VAL_BOUND
def VAL_MOD_REFL : thm := BVal.VAL_MOD_REFL
def VAL_WORD_EQ_EQ : thm := BVal.VAL_WORD_EQ_EQ
def FORALL_VAL_GEN : thm := BVal.FORALL_VAL_GEN
def FORALL_VAL : thm := BVal.FORALL_VAL
def VAL_CONG : thm := BVal.VAL_CONG
def WORD_MOD_SIZE : thm := BVal.WORD_MOD_SIZE
def VAL_WORD_CONG : thm := BVal.VAL_WORD_CONG
def VAL_WORD_GALOIS : thm := BVal.VAL_WORD_GALOIS
def WORD_VAL_GALOIS : thm := BVal.WORD_VAL_GALOIS
def DIVIDES_VAL_WORD_EQ : thm := BVal.DIVIDES_VAL_WORD_EQ
def BIT_VAL : thm := BVal.BIT_VAL
def BIT_VAL_MOD : thm := BVal.BIT_VAL_MOD
def BIT_LSB : thm := BVal.BIT_LSB
def TWICE_MSB : thm := BVal.TWICE_MSB
def MSB_VAL : thm := BVal.MSB_VAL
def MSB_INT_VAL : thm := BVal.MSB_INT_VAL
def BITVAL_MSB : thm := BVal.BITVAL_MSB
def BLOCK_BITS_ZERO_ALT : thm := BVal.BLOCK_BITS_ZERO_ALT
def BLOCK_BITS_ZERO : thm := BVal.BLOCK_BITS_ZERO
def LOWER_BITS_ZERO : thm := BVal.LOWER_BITS_ZERO
def UPPER_BITS_ZERO : thm := BVal.UPPER_BITS_ZERO
def UPPER_BITS_ZERO_ALT : thm := BVal.UPPER_BITS_ZERO_ALT
def VAL_WORD_OF_BITS : thm := BVal.VAL_WORD_OF_BITS
def WORD_OF_BITS_AS_WORD : thm := BVal.WORD_OF_BITS_AS_WORD
def WORD_OF_BITS_AS_WORD_FINITE : thm := BVal.WORD_OF_BITS_AS_WORD_FINITE
def WORD_OF_BITS_SING_AS_WORD : thm := BVal.WORD_OF_BITS_SING_AS_WORD
def VAL_WORD_OF_BITS_SING : thm := BVal.VAL_WORD_OF_BITS_SING
def WORD_OF_BITS_MASK : thm := BVal.WORD_OF_BITS_MASK
def BIT_MASK_WORD : thm := BVal.BIT_MASK_WORD
def BIT_WORD_POW2 : thm := BVal.BIT_WORD_POW2
def BIT_WORD_1 : thm := BVal.BIT_WORD_1
def BIT_WORD_BITVAL : thm := BVal.BIT_WORD_BITVAL
def WORD_OF_BITS_SING_AS_WORD_1 : thm := BVal.WORD_OF_BITS_SING_AS_WORD_1
def BITS_OF_WORD_1 : thm := BVal.BITS_OF_WORD_1
def BIT_WORD_OF_BITS_SING : thm := BVal.BIT_WORD_OF_BITS_SING
def VAL_MOD : thm := BVal.VAL_MOD
def VAL_MOD_2 : thm := BVal.VAL_MOD_2
def VAL_MOD_STEP : thm := BVal.VAL_MOD_STEP
def VAL_DIV : thm := BVal.VAL_DIV
def VAL_DIV_ALT : thm := BVal.VAL_DIV_ALT
def VAL_LE_BITS : thm := BVal.VAL_LE_BITS
def VAL_LE_SUBSET : thm := BVal.VAL_LE_SUBSET

-- Ival
def ival : thm := BIval.ival
def iword : thm := BIval.iword
def word_sgn : thm := BIval.word_sgn
def INT_IVAL : thm := BIval.INT_IVAL
def WORD_IWORD : thm := BIval.WORD_IWORD
def IVAL_VAL : thm := BIval.IVAL_VAL
def VAL_IVAL : thm := BIval.VAL_IVAL
def IVAL_EQ_VAL : thm := BIval.IVAL_EQ_VAL
def INT_VAL_IWORD : thm := BIval.INT_VAL_IWORD
def INT_VAL_IWORD_EQ : thm := BIval.INT_VAL_IWORD_EQ
def MSB_IVAL : thm := BIval.MSB_IVAL
def IVAL_BOUND : thm := BIval.IVAL_BOUND
def IVAL_WORD_0 : thm := BIval.IVAL_WORD_0
def IVAL_WORD_1 : thm := BIval.IVAL_WORD_1
def IVAL_VAL_CONG : thm := BIval.IVAL_VAL_CONG
def IVAL_CONG : thm := BIval.IVAL_CONG
def IVAL_EQ : thm := BIval.IVAL_EQ
def IVAL_EQ_0 : thm := BIval.IVAL_EQ_0
def IVAL_EQ_1 : thm := BIval.IVAL_EQ_1
def IWORD_EQ : thm := BIval.IWORD_EQ
def IWORD_REM_SIZE : thm := BIval.IWORD_REM_SIZE
def IVAL_IWORD_CONG : thm := BIval.IVAL_IWORD_CONG
def VAL_IWORD_CONG : thm := BIval.VAL_IWORD_CONG
def IVAL_WORD_CONG : thm := BIval.IVAL_WORD_CONG
def IVAL_IWORD : thm := BIval.IVAL_IWORD
def IWORD_IVAL : thm := BIval.IWORD_IVAL
def IVAL_IWORD_GALOIS : thm := BIval.IVAL_IWORD_GALOIS
def BIT_IVAL : thm := BIval.BIT_IVAL
def BIT_IWORD : thm := BIval.BIT_IWORD
def INT_REM_IVAL : thm := BIval.INT_REM_IVAL
def VAL_IVAL_REM : thm := BIval.VAL_IVAL_REM
def INT_REM_IVAL_IWORD : thm := BIval.INT_REM_IVAL_IWORD
def INT_DIVIDES_IVAL_IWORD : thm := BIval.INT_DIVIDES_IVAL_IWORD
def FORALL_IVAL_GEN : thm := BIval.FORALL_IVAL_GEN
def FORALL_IVAL : thm := BIval.FORALL_IVAL
def FORALL_IWORD : thm := BIval.FORALL_IWORD
def EXISTS_IWORD : thm := BIval.EXISTS_IWORD
def IVAL_REM_2 : thm := BIval.IVAL_REM_2
def BIT_LSB_IWORD : thm := BIval.BIT_LSB_IWORD
def TWOS_COMPLEMENT_GEN : thm := BIval.TWOS_COMPLEMENT_GEN
def TWOS_COMPLEMENT : thm := BIval.TWOS_COMPLEMENT

-- NumBits
def numbit : thm := BNumBits.numbit
def NUMBIT_VAL : thm := BNumBits.NUMBIT_VAL
def numbitCtx := BNumBits.numbitCtx
def bits_of_num : thm := BNumBits.bits_of_num
def IN_BITS_OF_NUM : thm := BNumBits.IN_BITS_OF_NUM
def BITS_OF_NUM_SUBSET_NUMSEG_LT : thm := BNumBits.BITS_OF_NUM_SUBSET_NUMSEG_LT
def FINITE_BITS_OF_NUM : thm := BNumBits.FINITE_BITS_OF_NUM
def NSUM_BITS_OF_NUM : thm := BNumBits.NSUM_BITS_OF_NUM
def BITS_OF_NUM_NSUM : thm := BNumBits.BITS_OF_NUM_NSUM
def BITS_OF_NUM_EQ : thm := BNumBits.BITS_OF_NUM_EQ
def BITS_OF_NUM_GALOIS : thm := BNumBits.BITS_OF_NUM_GALOIS
def NSUM_BITS_DIV : thm := BNumBits.NSUM_BITS_DIV
def NSUM_BITS_MOD : thm := BNumBits.NSUM_BITS_MOD
def NSUM_BITS_EQ : thm := BNumBits.NSUM_BITS_EQ
def BITSUM_BOUND : thm := BNumBits.BITSUM_BOUND
def BITS_OF_NUM_SUBSET_NUMSEG_EQ : thm := BNumBits.BITS_OF_NUM_SUBSET_NUMSEG_EQ
def BITSUM_DIVIDES : thm := BNumBits.BITSUM_DIVIDES
def BITS_OF_NUM_DISJOINT_NUMSEG_EQ : thm := BNumBits.BITS_OF_NUM_DISJOINT_NUMSEG_EQ
def BITS_OF_NUM_0 : thm := BNumBits.BITS_OF_NUM_0
def BITS_OF_NUM_POW2 : thm := BNumBits.BITS_OF_NUM_POW2
def BITS_OF_NUM_1 : thm := BNumBits.BITS_OF_NUM_1
def BITS_OF_NUM_DIV : thm := BNumBits.BITS_OF_NUM_DIV
def BITS_OF_NUM_MOD : thm := BNumBits.BITS_OF_NUM_MOD
def BITS_OF_NUM_MUL_ALT : thm := BNumBits.BITS_OF_NUM_MUL_ALT
def BITS_OF_NUM_MUL : thm := BNumBits.BITS_OF_NUM_MUL
def BITS_OF_NUM_ADD : thm := BNumBits.BITS_OF_NUM_ADD
def DISJOINT_BITS_HILO : thm := BNumBits.DISJOINT_BITS_HILO
def DISJOINT_BITS_CLAUSES : thm := BNumBits.DISJOINT_BITS_CLAUSES
def DIV_MOD_DISJOINT_BITS : thm := BNumBits.DIV_MOD_DISJOINT_BITS
def BITS_OF_WORD_WORD : thm := BNumBits.BITS_OF_WORD_WORD
def BITS_OF_NUM_VAL : thm := BNumBits.BITS_OF_NUM_VAL

-- NumShiftAdd
def num_shift_add : thm := BNumShiftAdd.num_shift_add
def num_shift_add_0 : thm := BNumShiftAdd.num_shift_add_0
def EXP_2_MOD_LT : thm := BNumShiftAdd.EXP_2_MOD_LT
def num_shift_add_SUC : thm := BNumShiftAdd.num_shift_add_SUC
def num_shift_add_lt : thm := BNumShiftAdd.num_shift_add_lt
def num_shift_add_mod : thm := BNumShiftAdd.num_shift_add_mod
def nsaCtx := BNumShiftAdd.nsaCtx

-- Limits
def word_UINT_MAX : thm := BLimits.word_UINT_MAX
def word_INT_MIN : thm := BLimits.word_INT_MIN
def word_INT_MAX : thm := BLimits.word_INT_MAX
def WORD_INT_MIN : thm := BLimits.WORD_INT_MIN
def WORD_INT_MAX : thm := BLimits.WORD_INT_MAX
def VAL_WORD_UINT_MAX : thm := BLimits.VAL_WORD_UINT_MAX
def IVAL_WORD_INT_MIN : thm := BLimits.IVAL_WORD_INT_MIN
def IVAL_WORD_INT_MAX : thm := BLimits.IVAL_WORD_INT_MAX
def VAL_BOUND_ALT : thm := BLimits.VAL_BOUND_ALT
def IVAL_BOUND_ALT : thm := BLimits.IVAL_BOUND_ALT
def VAL_WORD_INT_MIN : thm := BLimits.VAL_WORD_INT_MIN
def INT_VAL_WORD_INT_MIN : thm := BLimits.INT_VAL_WORD_INT_MIN
def WORD_INT_MIN_ALT : thm := BLimits.WORD_INT_MIN_ALT
def BIT_WORD_INT_MIN : thm := BLimits.BIT_WORD_INT_MIN
def word_saturate : thm := BLimits.word_saturate
def iword_saturate : thm := BLimits.iword_saturate

-- Popcount
def word_popcount : thm := BPopcount.word_popcount
def HAS_SIZE_BITS_OF_WORD_POPCOUNT : thm := BPopcount.HAS_SIZE_BITS_OF_WORD_POPCOUNT
def WORD_POPCOUNT_BOUND : thm := BPopcount.WORD_POPCOUNT_BOUND
def WORD_POPCOUNT_BOUND_SIZE : thm := BPopcount.WORD_POPCOUNT_BOUND_SIZE
def WORD_POPCOUNT_EQ_0 : thm := BPopcount.WORD_POPCOUNT_EQ_0
def WORD_POPCOUNT_0 : thm := BPopcount.WORD_POPCOUNT_0
def WORD_POPCOUNT_1 : thm := BPopcount.WORD_POPCOUNT_1
def WORD_POPCOUNT_BITVAL : thm := BPopcount.WORD_POPCOUNT_BITVAL
def WORD_POPCOUNT_NSUM : thm := BPopcount.WORD_POPCOUNT_NSUM
def WORD_POPCOUNT_LE_BITS : thm := BPopcount.WORD_POPCOUNT_LE_BITS
def WORD_POPCOUNT_WORD_OF_BITS_GEN : thm := BPopcount.WORD_POPCOUNT_WORD_OF_BITS_GEN
def WORD_POPCOUNT_WORD_OF_BITS : thm := BPopcount.WORD_POPCOUNT_WORD_OF_BITS
def word_evenparity : thm := BPopcount.word_evenparity
def word_oddparity : thm := BPopcount.word_oddparity
def NOT_WORD_EVENPARITY : thm := BPopcount.NOT_WORD_EVENPARITY
def NOT_WORD_ODDPARITY : thm := BPopcount.NOT_WORD_ODDPARITY
def WORD_EVENPARITY_0 : thm := BPopcount.WORD_EVENPARITY_0
def WORD_ODDPARITY_0 : thm := BPopcount.WORD_ODDPARITY_0
def WORD_EVENPARITY_1 : thm := BPopcount.WORD_EVENPARITY_1
def WORD_ODDPARITY_1 : thm := BPopcount.WORD_ODDPARITY_1

-- GeneralOps
def modular : thm := BGeneralOps.modular
def VAL_MODULAR : thm := BGeneralOps.VAL_MODULAR
def CONG_MODULAR : thm := BGeneralOps.CONG_MODULAR
def imodular : thm := BGeneralOps.imodular
def CONG_IMODULAR : thm := BGeneralOps.CONG_IMODULAR
def relational2 : thm := BGeneralOps.relational2
def irelational2 : thm := BGeneralOps.irelational2
def bitwise1 : thm := BGeneralOps.bitwise1
def bitwise2 : thm := BGeneralOps.bitwise2
def BIT_BITWISE1 : thm := BGeneralOps.BIT_BITWISE1
def BIT_BITWISE2 : thm := BGeneralOps.BIT_BITWISE2

-- WordOps1
def word_not : thm := BWordOps1.word_not
def BIT_WORD_NOT : thm := BWordOps1.BIT_WORD_NOT
def BITS_OF_WORD_NOT : thm := BWordOps1.BITS_OF_WORD_NOT
def WORD_OF_BITS_DIFF : thm := BWordOps1.WORD_OF_BITS_DIFF
def VAL_WORD_NOT : thm := BWordOps1.VAL_WORD_NOT
def INT_VAL_WORD_NOT : thm := BWordOps1.INT_VAL_WORD_NOT
def REAL_VAL_WORD_NOT : thm := BWordOps1.REAL_VAL_WORD_NOT
def WORD_POPCOUNT_NOT : thm := BWordOps1.WORD_POPCOUNT_NOT
def word_and : thm := BWordOps1.word_and
def BIT_WORD_AND : thm := BWordOps1.BIT_WORD_AND
def BIT_WORD_AND_ALT : thm := BWordOps1.BIT_WORD_AND_ALT
def BITS_OF_WORD_AND : thm := BWordOps1.BITS_OF_WORD_AND
def WORD_AND_EQ_0 : thm := BWordOps1.WORD_AND_EQ_0
def WORD_OF_BITS_INTER : thm := BWordOps1.WORD_OF_BITS_INTER
def WORD_AND_WORD_OF_BITS_SING : thm := BWordOps1.WORD_AND_WORD_OF_BITS_SING
def WORD_OF_BITS_SING_AND_WORD : thm := BWordOps1.WORD_OF_BITS_SING_AND_WORD
def WORD_AND_POW2 : thm := BWordOps1.WORD_AND_POW2
def VAL_WORD_AND_POW2 : thm := BWordOps1.VAL_WORD_AND_POW2
def WORD_AND_POW2_BITVAL : thm := BWordOps1.WORD_AND_POW2_BITVAL
def VAL_WORD_AND_POW2_BITVAL : thm := BWordOps1.VAL_WORD_AND_POW2_BITVAL
def VAL_WORD_AND_LE : thm := BWordOps1.VAL_WORD_AND_LE
def VAL_WORD_AND_LE_MIN : thm := BWordOps1.VAL_WORD_AND_LE_MIN
def VAL_WORD_AND_WORD_LE : thm := BWordOps1.VAL_WORD_AND_WORD_LE
def WORD_POPCOUNT_AND : thm := BWordOps1.WORD_POPCOUNT_AND
def word_or : thm := BWordOps1.word_or
def BIT_WORD_OR : thm := BWordOps1.BIT_WORD_OR
def BIT_WORD_OR_ALT : thm := BWordOps1.BIT_WORD_OR_ALT
def BITS_OF_WORD_OR : thm := BWordOps1.BITS_OF_WORD_OR
def WORD_OF_BITS_UNION : thm := BWordOps1.WORD_OF_BITS_UNION
def VAL_WORD_OR_LE : thm := BWordOps1.VAL_WORD_OR_LE
def VAL_WORD_OR_LE_MAX : thm := BWordOps1.VAL_WORD_OR_LE_MAX
def WORD_POPCOUNT_OR : thm := BWordOps1.WORD_POPCOUNT_OR
def WORD_POPCOUNT_OR_DISJOINT : thm := BWordOps1.WORD_POPCOUNT_OR_DISJOINT
def word_xor : thm := BWordOps1.word_xor
def BIT_WORD_XOR : thm := BWordOps1.BIT_WORD_XOR
def BIT_WORD_XOR_ALT : thm := BWordOps1.BIT_WORD_XOR_ALT
def VAL_WORD_ADD_AND_XOR : thm := BWordOps1.VAL_WORD_ADD_AND_XOR
def VAL_WORD_ADD_AND_OR : thm := BWordOps1.VAL_WORD_ADD_AND_OR
def VAL_WORD_OR_DISJOINT : thm := BWordOps1.VAL_WORD_OR_DISJOINT
def VAL_WORD_OR_AND_XOR : thm := BWordOps1.VAL_WORD_OR_AND_XOR
def REAL_VAL_WORD_XOR : thm := BWordOps1.REAL_VAL_WORD_XOR
def word_add : thm := BWordOps1.word_add
def VAL_WORD_ADD : thm := BWordOps1.VAL_WORD_ADD
def VAL_WORD_ADD_CASES : thm := BWordOps1.VAL_WORD_ADD_CASES
def VAL_WORD_ADC_CASES : thm := BWordOps1.VAL_WORD_ADC_CASES
def INT_VAL_WORD_ADD_CASES : thm := BWordOps1.INT_VAL_WORD_ADD_CASES
def CONG_WORD_ADD : thm := BWordOps1.CONG_WORD_ADD
def INT_CONG_WORD_ADD : thm := BWordOps1.INT_CONG_WORD_ADD
def WORD_ADD : thm := BWordOps1.WORD_ADD
def ICONG_WORD_ADD : thm := BWordOps1.ICONG_WORD_ADD
def IWORD_INT_ADD : thm := BWordOps1.IWORD_INT_ADD
def WORD_ADD_IMODULAR : thm := BWordOps1.WORD_ADD_IMODULAR
def ODD_VAL_WORD : thm := BWordOps1.ODD_VAL_WORD
def EVEN_VAL_WORD : thm := BWordOps1.EVEN_VAL_WORD
def ODD_VAL_WORD_ADD : thm := BWordOps1.ODD_VAL_WORD_ADD
def EVEN_VAL_WORD_ADD : thm := BWordOps1.EVEN_VAL_WORD_ADD
def word_sub : thm := BWordOps1.word_sub
def VAL_WORD_SUB : thm := BWordOps1.VAL_WORD_SUB
def VAL_WORD_SUB_CASES : thm := BWordOps1.VAL_WORD_SUB_CASES
def INT_VAL_WORD_SUB_CASES : thm := BWordOps1.INT_VAL_WORD_SUB_CASES
def CONG_WORD_SUB : thm := BWordOps1.CONG_WORD_SUB
def INT_CONG_WORD_SUB : thm := BWordOps1.INT_CONG_WORD_SUB
def INT_VAL_WORD_SUB : thm := BWordOps1.INT_VAL_WORD_SUB
def ICONG_WORD_SUB : thm := BWordOps1.ICONG_WORD_SUB
def IWORD_INT_SUB : thm := BWordOps1.IWORD_INT_SUB
def WORD_SUB_IMODULAR : thm := BWordOps1.WORD_SUB_IMODULAR
def WORD_SUB : thm := BWordOps1.WORD_SUB
def word_neg : thm := BWordOps1.word_neg
def ODD_VAL_WORD_SUB : thm := BWordOps1.ODD_VAL_WORD_SUB
def EVEN_VAL_WORD_SUB : thm := BWordOps1.EVEN_VAL_WORD_SUB
def VAL_WORD_NEG : thm := BWordOps1.VAL_WORD_NEG
def VAL_WORD_NEG_CASES : thm := BWordOps1.VAL_WORD_NEG_CASES
def INT_VAL_WORD_NEG_CASES : thm := BWordOps1.INT_VAL_WORD_NEG_CASES
def REAL_VAL_WORD_NEG_CASES : thm := BWordOps1.REAL_VAL_WORD_NEG_CASES
def INT_VAL_WORD_NEG : thm := BWordOps1.INT_VAL_WORD_NEG
def REAL_VAL_WORD_NEG : thm := BWordOps1.REAL_VAL_WORD_NEG
def CONG_WORD_NEG : thm := BWordOps1.CONG_WORD_NEG
def INT_CONG_WORD_NEG : thm := BWordOps1.INT_CONG_WORD_NEG
def ICONG_WORD_NEG : thm := BWordOps1.ICONG_WORD_NEG
def IWORD_INT_NEG : thm := BWordOps1.IWORD_INT_NEG
def WORD_NEG_AS_ADD : thm := BWordOps1.WORD_NEG_AS_ADD

-- WordOps2
def WORD_NOT_AS_SUB : thm := BWordOps2.WORD_NOT_AS_SUB
def VAL_WORD_NEG_1 : thm := BWordOps2.VAL_WORD_NEG_1
def IVAL_WORD_NEG_1 : thm := BWordOps2.IVAL_WORD_NEG_1
def IVAL_EQ_MINUS1 : thm := BWordOps2.IVAL_EQ_MINUS1
def WORD_NEG_1 : thm := BWordOps2.WORD_NEG_1
def ODD_VAL_WORD_NEG : thm := BWordOps2.ODD_VAL_WORD_NEG
def EVEN_VAL_WORD_NEG : thm := BWordOps2.EVEN_VAL_WORD_NEG
def word_mul : thm := BWordOps2.word_mul
def VAL_WORD_MUL : thm := BWordOps2.VAL_WORD_MUL
def CONG_WORD_MUL : thm := BWordOps2.CONG_WORD_MUL
def INT_CONG_WORD_MUL : thm := BWordOps2.INT_CONG_WORD_MUL
def WORD_MUL : thm := BWordOps2.WORD_MUL
def ICONG_WORD_MUL : thm := BWordOps2.ICONG_WORD_MUL
def IWORD_INT_MUL : thm := BWordOps2.IWORD_INT_MUL
def WORD_MUL_IMODULAR : thm := BWordOps2.WORD_MUL_IMODULAR
def ODD_VAL_WORD_MUL : thm := BWordOps2.ODD_VAL_WORD_MUL
def EVEN_VAL_WORD_MUL : thm := BWordOps2.EVEN_VAL_WORD_MUL
def word_udiv : thm := BWordOps2.word_udiv
def VAL_WORD_UDIV : thm := BWordOps2.VAL_WORD_UDIV
def word_umod : thm := BWordOps2.word_umod
def VAL_WORD_UMOD : thm := BWordOps2.VAL_WORD_UMOD
def word_umax : thm := BWordOps2.word_umax
def word_imax : thm := BWordOps2.word_imax
def VAL_WORD_UMAX : thm := BWordOps2.VAL_WORD_UMAX
def WORD_UMAX : thm := BWordOps2.WORD_UMAX
def WORD_UMAX_SYM : thm := BWordOps2.WORD_UMAX_SYM
def WORD_UMAX_ASSOC : thm := BWordOps2.WORD_UMAX_ASSOC
def IVAL_WORD_IMAX : thm := BWordOps2.IVAL_WORD_IMAX
def word_umin : thm := BWordOps2.word_umin
def word_imin : thm := BWordOps2.word_imin
def VAL_WORD_UMIN : thm := BWordOps2.VAL_WORD_UMIN
def WORD_UMIN : thm := BWordOps2.WORD_UMIN
def WORD_UMIN_SYM : thm := BWordOps2.WORD_UMIN_SYM
def WORD_UMIN_ASSOC : thm := BWordOps2.WORD_UMIN_ASSOC
def IVAL_WORD_IMIN : thm := BWordOps2.IVAL_WORD_IMIN
def word_shl : thm := BWordOps2.word_shl
def VAL_WORD_SHL : thm := BWordOps2.VAL_WORD_SHL
def CONG_WORD_SHL : thm := BWordOps2.CONG_WORD_SHL
def ICONG_WORD_SHL : thm := BWordOps2.ICONG_WORD_SHL
def BIT_WORD_SHL : thm := BWordOps2.BIT_WORD_SHL
def WORD_SHL_WORD_OF_BITS : thm := BWordOps2.WORD_SHL_WORD_OF_BITS
def WORD_SHL_0 : thm := BWordOps2.WORD_SHL_0
def WORD_SHL_ZERO : thm := BWordOps2.WORD_SHL_ZERO
def WORD_SHL_TRIVIAL : thm := BWordOps2.WORD_SHL_TRIVIAL
def WORD_SHL_COMPOSE : thm := BWordOps2.WORD_SHL_COMPOSE
def WORD_SHL_LSB_ALT : thm := BWordOps2.WORD_SHL_LSB_ALT
def WORD_SHL_LSB : thm := BWordOps2.WORD_SHL_LSB

-- WordOps3
def WORD_SHL_WORD : thm := BWordOps3.WORD_SHL_WORD
def WORD_SHL_AS_IWORD : thm := BWordOps3.WORD_SHL_AS_IWORD
def WORD_SHL_IWORD : thm := BWordOps3.WORD_SHL_IWORD
def WORD_MUL_EXPAND : thm := BWordOps3.WORD_MUL_EXPAND
def word_ushr : thm := BWordOps3.word_ushr
def VAL_WORD_USHR : thm := BWordOps3.VAL_WORD_USHR
def WORD_USHR_EQ_0 : thm := BWordOps3.WORD_USHR_EQ_0
def BIT_WORD_USHR : thm := BWordOps3.BIT_WORD_USHR
def WORD_USHR_WORD_OF_BITS : thm := BWordOps3.WORD_USHR_WORD_OF_BITS
def WORD_USHR_0 : thm := BWordOps3.WORD_USHR_0
def WORD_USHR_ZERO : thm := BWordOps3.WORD_USHR_ZERO
def WORD_USHR_COMPOSE : thm := BWordOps3.WORD_USHR_COMPOSE
def WORD_USHR_MSB_ALT : thm := BWordOps3.WORD_USHR_MSB_ALT
def WORD_USHR_MSB : thm := BWordOps3.WORD_USHR_MSB
def WORD_USHR_MSB_EQ : thm := BWordOps3.WORD_USHR_MSB_EQ
def WORD_POPCOUNT_SHL : thm := BWordOps3.WORD_POPCOUNT_SHL
def WORD_POPCOUNT_USHR : thm := BWordOps3.WORD_POPCOUNT_USHR
def word_ishr : thm := BWordOps3.word_ishr
def IVAL_WORD_ISHR : thm := BWordOps3.IVAL_WORD_ISHR
def WORD_ISHR_EQ_0 : thm := BWordOps3.WORD_ISHR_EQ_0
def BIT_WORD_ISHR : thm := BWordOps3.BIT_WORD_ISHR
def WORD_ISHR_WORD_OF_BITS : thm := BWordOps3.WORD_ISHR_WORD_OF_BITS
def WORD_ISHR_0 : thm := BWordOps3.WORD_ISHR_0
def WORD_ISHR_ZERO : thm := BWordOps3.WORD_ISHR_ZERO
def WORD_ISHR_COMPOSE : thm := BWordOps3.WORD_ISHR_COMPOSE
def WORD_ISHR_UNIQUE : thm := BWordOps3.WORD_ISHR_UNIQUE
def IVAL_WORD_ISHR_SHL_UNIQUE : thm := BWordOps3.IVAL_WORD_ISHR_SHL_UNIQUE
def word_ror : thm := BWordOps3.word_ror
def word_rol : thm := BWordOps3.word_rol
def WORD_ROR_ROL_GEN : thm := BWordOps3.WORD_ROR_ROL_GEN
def WORD_ROL_ROR_GEN : thm := BWordOps3.WORD_ROL_ROR_GEN
def WORD_ROR_PERIODIC : thm := BWordOps3.WORD_ROR_PERIODIC
def WORD_ROR_MOD : thm := BWordOps3.WORD_ROR_MOD
def WORD_ROR_EQ_SELF : thm := BWordOps3.WORD_ROR_EQ_SELF
def WORD_ROR_ZERO : thm := BWordOps3.WORD_ROR_ZERO
def WORD_ROL_PERIODIC : thm := BWordOps3.WORD_ROL_PERIODIC
def WORD_ROL_MOD : thm := BWordOps3.WORD_ROL_MOD
def WORD_ROL_EQ_SELF : thm := BWordOps3.WORD_ROL_EQ_SELF
def WORD_ROL_ZERO : thm := BWordOps3.WORD_ROL_ZERO
def WORD_ROR_ROL : thm := BWordOps3.WORD_ROR_ROL
def WORD_ROL_ROR : thm := BWordOps3.WORD_ROL_ROR
def WORD_ROR_SHIFTS : thm := BWordOps3.WORD_ROR_SHIFTS
def WORD_ROL_SHIFTS : thm := BWordOps3.WORD_ROL_SHIFTS
def BIT_WORD_ROR : thm := BWordOps3.BIT_WORD_ROR
def BIT_WORD_ROL : thm := BWordOps3.BIT_WORD_ROL
def WORD_ROR_COMPOSE : thm := BWordOps3.WORD_ROR_COMPOSE
def WORD_ROL_COMPOSE : thm := BWordOps3.WORD_ROL_COMPOSE
def VAL_WORD_ROR : thm := BWordOps3.VAL_WORD_ROR
def VAL_WORD_ROL : thm := BWordOps3.VAL_WORD_ROL
def word_ule : thm := BWordOps3.word_ule
def word_uge : thm := BWordOps3.word_uge
def word_ult : thm := BWordOps3.word_ult
def word_ugt : thm := BWordOps3.word_ugt
def word_ile : thm := BWordOps3.word_ile
def word_ige : thm := BWordOps3.word_ige
def word_ilt : thm := BWordOps3.word_ilt
def word_igt : thm := BWordOps3.word_igt
def WORD_ULT : thm := BWordOps3.WORD_ULT
def WORD_ULE : thm := BWordOps3.WORD_ULE
def WORD_UGT : thm := BWordOps3.WORD_UGT
def WORD_UGE : thm := BWordOps3.WORD_UGE
def WORD_ILT : thm := BWordOps3.WORD_ILT
def WORD_ILE : thm := BWordOps3.WORD_ILE
def WORD_IGT : thm := BWordOps3.WORD_IGT
def WORD_IGE : thm := BWordOps3.WORD_IGE

-- WordRule
def WORD_VAL_CONG_CONV : HolCore.Equal.ioconv := fun t => BWordRule.WORD_VAL_CONG_CONV t
def WORD_RULE : term → IO (Except String thm) := fun t => (BWordRule.WORD_RULE t).run

-- WordBitwise
def WORD_BITWISE_RULE : term → IO (Except String thm) := fun t => (BWordBitwise.WORD_BITWISE_RULE t).run
def WORD_BITWISE_TAC : HolCore.Tactics.tactic := fun g => BWordBitwise.WORD_BITWISE_TAC g

-- WordArith
def WORD_ARITH : term → IO (Except String thm) := fun t => (BWordArith.WORD_ARITH t).run
def WORD_ARITH_TAC : HolCore.Tactics.tactic := fun g => BWordArith.WORD_ARITH_TAC g

-- ValExpand
def EMPOWER_CONV : HolCore.Equal.ioconv := fun t => BValExpand.EMPOWER_CONV t
def VAL_EXPAND_CONV : HolCore.Equal.ioconv := fun t => BValExpand.VAL_EXPAND_CONV t

-- ZxSx
def word_zx : thm := BZxSx.word_zx
def VAL_WORD_ZX_GEN : thm := BZxSx.VAL_WORD_ZX_GEN
def VAL_WORD_ZX : thm := BZxSx.VAL_WORD_ZX
def WORD_ZX_ZX : thm := BZxSx.WORD_ZX_ZX
def WORD_ZX_0 : thm := BZxSx.WORD_ZX_0
def WORD_ZX_TRIVIAL : thm := BZxSx.WORD_ZX_TRIVIAL
def WORD_ZX_WORD : thm := BZxSx.WORD_ZX_WORD
def WORD_ZX_WORD_SIMPLE : thm := BZxSx.WORD_ZX_WORD_SIMPLE
def WORD_ZX_1 : thm := BZxSx.WORD_ZX_1
def WORD_ZX_BITVAL : thm := BZxSx.WORD_ZX_BITVAL
def BIT_WORD_ZX : thm := BZxSx.BIT_WORD_ZX
def WORD_ZX_AND : thm := BZxSx.WORD_ZX_AND
def WORD_ZX_OR : thm := BZxSx.WORD_ZX_OR
def WORD_ZX_XOR : thm := BZxSx.WORD_ZX_XOR
def WORD_ZX_NOT : thm := BZxSx.WORD_ZX_NOT
def WORD_ZX_ADD : thm := BZxSx.WORD_ZX_ADD
def WORD_ZX_MUL : thm := BZxSx.WORD_ZX_MUL
def WORD_ZX_NEG : thm := BZxSx.WORD_ZX_NEG
def WORD_ZX_SUB : thm := BZxSx.WORD_ZX_SUB
def WORD_ZX_SHL : thm := BZxSx.WORD_ZX_SHL
def word_sx : thm := BZxSx.word_sx
def IVAL_WORD_SX : thm := BZxSx.IVAL_WORD_SX
def WORD_SX_SX : thm := BZxSx.WORD_SX_SX
def WORD_SX_0 : thm := BZxSx.WORD_SX_0
def WORD_SX_TRIVIAL : thm := BZxSx.WORD_SX_TRIVIAL
def WORD_SX_ZX : thm := BZxSx.WORD_SX_ZX
def word_sxfrom : thm := BZxSx.word_sxfrom
def BIT_WORD_SXFROM : thm := BZxSx.BIT_WORD_SXFROM
def IVAL_WORD_SXFROM_UNIQUE : thm := BZxSx.IVAL_WORD_SXFROM_UNIQUE
def word_cand : thm := BZxSx.word_cand
def word_cor : thm := BZxSx.word_cor
def WORD_CAND : thm := BZxSx.WORD_CAND
def WORD_COR : thm := BZxSx.WORD_COR
def WORD_CAND_NE_0 : thm := BZxSx.WORD_CAND_NE_0
def WORD_COR_NE_0 : thm := BZxSx.WORD_COR_NE_0
def WORD_CAND_EQ_0 : thm := BZxSx.WORD_CAND_EQ_0
def WORD_COR_EQ_0 : thm := BZxSx.WORD_COR_EQ_0
def VAL_WORD_CAND : thm := BZxSx.VAL_WORD_CAND
def VAL_WORD_COR : thm := BZxSx.VAL_WORD_COR
def BIT_WORD_CAND : thm := BZxSx.BIT_WORD_CAND
def BIT_WORD_COR : thm := BZxSx.BIT_WORD_COR

-- JoinSubword
def word_join : thm := BJoinSubword.word_join
def VAL_WORD_JOIN : thm := BJoinSubword.VAL_WORD_JOIN
def BIT_WORD_JOIN_GEN : thm := BJoinSubword.BIT_WORD_JOIN_GEN
def BIT_WORD_JOIN : thm := BJoinSubword.BIT_WORD_JOIN
def VAL_WORD_JOIN_SIMPLE : thm := BJoinSubword.VAL_WORD_JOIN_SIMPLE
def WORD_JOIN_NOT : thm := BJoinSubword.WORD_JOIN_NOT
def word_subword : thm := BJoinSubword.word_subword
def VAL_WORD_SUBWORD : thm := BJoinSubword.VAL_WORD_SUBWORD
def VAL_WORD_SUBWORD_DIMINDEX : thm := BJoinSubword.VAL_WORD_SUBWORD_DIMINDEX
def VAL_WORD_SUBWORD_SIMPLE : thm := BJoinSubword.VAL_WORD_SUBWORD_SIMPLE
def WORD_SUBWORD_WORD : thm := BJoinSubword.WORD_SUBWORD_WORD
def BIT_WORD_SUBWORD : thm := BJoinSubword.BIT_WORD_SUBWORD
def WORD_SUBWORD_0 : thm := BJoinSubword.WORD_SUBWORD_0
def WORD_SUBWORD_JOIN_SELF : thm := BJoinSubword.WORD_SUBWORD_JOIN_SELF
def VAL_WORD_SUBWORD_JOIN : thm := BJoinSubword.VAL_WORD_SUBWORD_JOIN
def WORD_SUBWORD_JOIN_LOWER : thm := BJoinSubword.WORD_SUBWORD_JOIN_LOWER
def WORD_SUBWORD_JOIN_UPPER : thm := BJoinSubword.WORD_SUBWORD_JOIN_UPPER
def WORD_SUBWORD_SUBWORD : thm := BJoinSubword.WORD_SUBWORD_SUBWORD
def WORD_SUBWORD_TRIVIAL : thm := BJoinSubword.WORD_SUBWORD_TRIVIAL
def WORD_SUBWORD_DIMINDEX : thm := BJoinSubword.WORD_SUBWORD_DIMINDEX
def WORD_ZX_SUBWORD : thm := BJoinSubword.WORD_ZX_SUBWORD
def VAL_WORD_SUBWORD_JOIN_FULL : thm := BJoinSubword.VAL_WORD_SUBWORD_JOIN_FULL
def WORD_SUBWORD_JOIN_AS_USHR : thm := BJoinSubword.WORD_SUBWORD_JOIN_AS_USHR
def WORD_SUBWORD_JOIN_AS_SHL : thm := BJoinSubword.WORD_SUBWORD_JOIN_AS_SHL
def WORD_SUBWORD_AS_USHR : thm := BJoinSubword.WORD_SUBWORD_AS_USHR
def WORD_USHR_AS_SUBWORD : thm := BJoinSubword.WORD_USHR_AS_SUBWORD
def WORD_SHL_SUBWORD : thm := BJoinSubword.WORD_SHL_SUBWORD
def WORD_SUBWORD_AND : thm := BJoinSubword.WORD_SUBWORD_AND
def WORD_SUBWORD_OR : thm := BJoinSubword.WORD_SUBWORD_OR
def WORD_SUBWORD_XOR : thm := BJoinSubword.WORD_SUBWORD_XOR
def WORD_SUBWORD_NOT : thm := BJoinSubword.WORD_SUBWORD_NOT
def WORD_SUBWORD_ADD : thm := BJoinSubword.WORD_SUBWORD_ADD
def WORD_SUBWORD_AS_IWORD : thm := BJoinSubword.WORD_SUBWORD_AS_IWORD
def WORD_SUBWORD_IWORD : thm := BJoinSubword.WORD_SUBWORD_IWORD
def WORD_SUBWORD_AS_USHR_SHL : thm := BJoinSubword.WORD_SUBWORD_AS_USHR_SHL
def WORD_SXFROM_SUBWORD_AS_ISHR_SHL : thm := BJoinSubword.WORD_SXFROM_SUBWORD_AS_ISHR_SHL
def VAL_EXPAND_SUBWORDS : thm := BJoinSubword.VAL_EXPAND_SUBWORDS
def VAL_SUBWORDS_EQ : thm := BJoinSubword.VAL_SUBWORDS_EQ
def WORD_SUBWORDS_EQ : thm := BJoinSubword.WORD_SUBWORDS_EQ

-- InsertDup
def word_insert : thm := BInsertDup.word_insert
def BIT_WORD_INSERT : thm := BInsertDup.BIT_WORD_INSERT
def WORD_SUBWORD_INSERT_OUTER : thm := BInsertDup.WORD_SUBWORD_INSERT_OUTER
def WORD_SUBWORD_INSERT_INNER : thm := BInsertDup.WORD_SUBWORD_INSERT_INNER
def word_duplicate : thm := BInsertDup.word_duplicate
def BIT_WORD_DUPLICATE : thm := BInsertDup.BIT_WORD_DUPLICATE
def WORD_DUPLICATE_REFL : thm := BInsertDup.WORD_DUPLICATE_REFL
def WORD_DUPLICATE_DOUBLE : thm := BInsertDup.WORD_DUPLICATE_DOUBLE
def WORD_SUBWORD_DUPLICATE : thm := BInsertDup.WORD_SUBWORD_DUPLICATE
def WORD_SUBWORD_DUPLICATE_DUPLICATE : thm := BInsertDup.WORD_SUBWORD_DUPLICATE_DUPLICATE
def VAL_WORD_DUPLICATE : thm := BInsertDup.VAL_WORD_DUPLICATE
def WORD_DUPLICATE : thm := BInsertDup.WORD_DUPLICATE
def WORD_SUBWORD_ZX : thm := BInsertDup.WORD_SUBWORD_ZX
def WORD_SUBWORD_ZX_TRIVIAL : thm := BInsertDup.WORD_SUBWORD_ZX_TRIVIAL
def WORD_SIMPLE_SUBWORD_CONV : HolCore.Equal.ioconv := fun t => BInsertDup.WORD_SIMPLE_SUBWORD_CONV t

-- BitRec
def BIT_WORD_ADD : thm := BBitRec.BIT_WORD_ADD
def BIT_WORD_SUB : thm := BBitRec.BIT_WORD_SUB
def BIT_WORD_NEG : thm := BBitRec.BIT_WORD_NEG
def BIT_WORD_ADD_CLAUSES : thm := BBitRec.BIT_WORD_ADD_CLAUSES
def BIT_WORD_SUB_CLAUSES : thm := BBitRec.BIT_WORD_SUB_CLAUSES
def BIT_WORD_NEG_CLAUSES : thm := BBitRec.BIT_WORD_NEG_CLAUSES
def LE_VAL_MOD_STEP : thm := BBitRec.LE_VAL_MOD_STEP
def LT_VAL_MOD_STEP : thm := BBitRec.LT_VAL_MOD_STEP

-- Misc1
def WORD_ADD_0 : thm := BMisc1.WORD_ADD_0
def WORD_ADD_SYM : thm := BMisc1.WORD_ADD_SYM
def WORD_ADD_ASSOC : thm := BMisc1.WORD_ADD_ASSOC
def WORD_ADD_AC : thm := BMisc1.WORD_ADD_AC
def WORD_MUL_0 : thm := BMisc1.WORD_MUL_0
def WORD_MUL_SYM : thm := BMisc1.WORD_MUL_SYM
def WORD_MUL_ASSOC : thm := BMisc1.WORD_MUL_ASSOC
def WORD_MUL_AC : thm := BMisc1.WORD_MUL_AC
def WORD_SUB_0 : thm := BMisc1.WORD_SUB_0
def WORD_SUB_LZERO : thm := BMisc1.WORD_SUB_LZERO
def WORD_SUB_EQ_0 : thm := BMisc1.WORD_SUB_EQ_0
def WORD_SUB_REFL : thm := BMisc1.WORD_SUB_REFL
def WORD_NEG_NEG : thm := BMisc1.WORD_NEG_NEG
def WORD_NEG_0 : thm := BMisc1.WORD_NEG_0
def WORD_NEG_SUB : thm := BMisc1.WORD_NEG_SUB
def WORD_NEG_EQ_0 : thm := BMisc1.WORD_NEG_EQ_0
def WORD_NOT_NOT : thm := BMisc1.WORD_NOT_NOT
def WORD_AND_REFL : thm := BMisc1.WORD_AND_REFL
def WORD_AND_0 : thm := BMisc1.WORD_AND_0
def WORD_AND_NOT0 : thm := BMisc1.WORD_AND_NOT0
def WORD_AND_SYM : thm := BMisc1.WORD_AND_SYM
def WORD_AND_ASSOC : thm := BMisc1.WORD_AND_ASSOC
def WORD_OR_REFL : thm := BMisc1.WORD_OR_REFL
def WORD_OR_0 : thm := BMisc1.WORD_OR_0
def WORD_OR_NOT0 : thm := BMisc1.WORD_OR_NOT0
def WORD_OR_SYM : thm := BMisc1.WORD_OR_SYM
def WORD_OR_ASSOC : thm := BMisc1.WORD_OR_ASSOC
def WORD_OR_EQ_0 : thm := BMisc1.WORD_OR_EQ_0
def WORD_NOT_AND : thm := BMisc1.WORD_NOT_AND
def WORD_NOT_OR : thm := BMisc1.WORD_NOT_OR
def WORD_XOR_EQ_0 : thm := BMisc1.WORD_XOR_EQ_0
def WORD_XOR_0 : thm := BMisc1.WORD_XOR_0
def WORD_XOR_NOT : thm := BMisc1.WORD_XOR_NOT
def WORD_XOR_NOT0 : thm := BMisc1.WORD_XOR_NOT0
def WORD_XOR_REFL : thm := BMisc1.WORD_XOR_REFL
def WORD_XOR_SYM : thm := BMisc1.WORD_XOR_SYM
def WORD_XOR_ASSOC : thm := BMisc1.WORD_XOR_ASSOC
def WORD_AND_1 : thm := BMisc1.WORD_AND_1
def WORD_AND_1_BITVAL : thm := BMisc1.WORD_AND_1_BITVAL
def WORD_NOT_NEG : thm := BMisc1.WORD_NOT_NEG
def WORD_NOT_SUB : thm := BMisc1.WORD_NOT_SUB
def WORD_NOT_ADD : thm := BMisc1.WORD_NOT_ADD
def VAL_WORD_SUB_EQ_0 : thm := BMisc1.VAL_WORD_SUB_EQ_0
def VAL_EQ_MAX_ALT : thm := BMisc1.VAL_EQ_MAX_ALT
def VAL_EQ_MAX : thm := BMisc1.VAL_EQ_MAX
def VAL_EQ_MAX_MASK : thm := BMisc1.VAL_EQ_MAX_MASK
def VAL_WORD_OR_EQ_0 : thm := BMisc1.VAL_WORD_OR_EQ_0
def VAL_WORD_AND_EQ_MAX : thm := BMisc1.VAL_WORD_AND_EQ_MAX
def WORD_SHL_AND : thm := BMisc1.WORD_SHL_AND
def WORD_USHR_AND : thm := BMisc1.WORD_USHR_AND
def WORD_SHL_OR : thm := BMisc1.WORD_SHL_OR
def WORD_USHR_OR : thm := BMisc1.WORD_USHR_OR
def WORD_SHL_XOR : thm := BMisc1.WORD_SHL_XOR
def WORD_USHR_XOR : thm := BMisc1.WORD_USHR_XOR
def WORD_ADD_XOR_GEN : thm := BMisc1.WORD_ADD_XOR_GEN
def WORD_ADD_OR_GEN : thm := BMisc1.WORD_ADD_OR_GEN
def WORD_OR_XOR_GEN : thm := BMisc1.WORD_OR_XOR_GEN
def WORD_ADD_OR_EQ : thm := BMisc1.WORD_ADD_OR_EQ
def WORD_OR_XOR_EQ : thm := BMisc1.WORD_OR_XOR_EQ
def WORD_ADD_OR : thm := BMisc1.WORD_ADD_OR
def WORD_OR_XOR : thm := BMisc1.WORD_OR_XOR
def WORD_ADD_XOR : thm := BMisc1.WORD_ADD_XOR
def WORD_POPCOUNT_ADD_DISJOINT : thm := BMisc1.WORD_POPCOUNT_ADD_DISJOINT
def WORD_POPCOUNT_XOR_AND : thm := BMisc1.WORD_POPCOUNT_XOR_AND
def WORD_POPCOUNT_OR_AND : thm := BMisc1.WORD_POPCOUNT_OR_AND
def WORD_POPCOUNT_XOR_AND2 : thm := BMisc1.WORD_POPCOUNT_XOR_AND2
def WORD_POPCOUNT_XOR : thm := BMisc1.WORD_POPCOUNT_XOR
def WORD_SUB_XOR : thm := BMisc1.WORD_SUB_XOR
def WORD_XOR_SUB : thm := BMisc1.WORD_XOR_SUB
def WORD_SUB_MASK_WORD : thm := BMisc1.WORD_SUB_MASK_WORD
def WORD_XOR_MASK_WORD : thm := BMisc1.WORD_XOR_MASK_WORD
def WORD_XOR_INT_MIN : thm := BMisc1.WORD_XOR_INT_MIN
def WORD_BITVAL_NOT : thm := BMisc1.WORD_BITVAL_NOT
def IVAL_WORD_NOT : thm := BMisc1.IVAL_WORD_NOT
def BIT_WORD_NEG_CASES : thm := BMisc1.BIT_WORD_NEG_CASES
def BIT_WORD_ADD_1_CASES : thm := BMisc1.BIT_WORD_ADD_1_CASES
def BIT_WORD_SUB_1_CASES : thm := BMisc1.BIT_WORD_SUB_1_CASES
def BIT_WORD_AND_NEG : thm := BMisc1.BIT_WORD_AND_NEG
def BIT_WORD_OR_NEG : thm := BMisc1.BIT_WORD_OR_NEG
def BIT_WORD_XOR_NEG : thm := BMisc1.BIT_WORD_XOR_NEG
def BIT_WORD_AND_ADD_1 : thm := BMisc1.BIT_WORD_AND_ADD_1
def BIT_WORD_AND_SUB_1 : thm := BMisc1.BIT_WORD_AND_SUB_1
def BIT_WORD_OR_ADD_1 : thm := BMisc1.BIT_WORD_OR_ADD_1
def BIT_WORD_OR_SUB_1 : thm := BMisc1.BIT_WORD_OR_SUB_1
def BIT_WORD_XOR_ADD_1 : thm := BMisc1.BIT_WORD_XOR_ADD_1
def BIT_WORD_XOR_SUB_1 : thm := BMisc1.BIT_WORD_XOR_SUB_1
def BIT_WORD_AND_NOT_SUB_1 : thm := BMisc1.BIT_WORD_AND_NOT_SUB_1
def BIT_WORD_AND_NOT_ADD_1 : thm := BMisc1.BIT_WORD_AND_NOT_ADD_1
def WORD_OR_SHL_USHR : thm := BMisc1.WORD_OR_SHL_USHR
def WORD_OR_USHR_SHL : thm := BMisc1.WORD_OR_USHR_SHL
def WORD_ADD_SHL_USHR : thm := BMisc1.WORD_ADD_SHL_USHR
def WORD_ADD_USHR_SHL : thm := BMisc1.WORD_ADD_USHR_SHL

-- Masks
def WORD_MASK_ALT : thm := BMasks.WORD_MASK_ALT
def WORD_MASK : thm := BMasks.WORD_MASK
def BIT_WORD_MASK : thm := BMasks.BIT_WORD_MASK
def WORD_ISHR_MSB : thm := BMasks.WORD_ISHR_MSB
def WORD_NOT_MASK : thm := BMasks.WORD_NOT_MASK
def WORD_AND_MASK : thm := BMasks.WORD_AND_MASK
def WORD_OR_MASK : thm := BMasks.WORD_OR_MASK
def WORD_XOR_MASK : thm := BMasks.WORD_XOR_MASK
def WORD_NEG_AND_MASK : thm := BMasks.WORD_NEG_AND_MASK
def WORD_AND_MASKS : thm := BMasks.WORD_AND_MASKS
def WORD_OR_MASKS : thm := BMasks.WORD_OR_MASKS
def WORD_XOR_MASKS : thm := BMasks.WORD_XOR_MASKS
def WORD_AND_CONDITIONS : thm := BMasks.WORD_AND_CONDITIONS
def WORD_OR_CONDITIONS : thm := BMasks.WORD_OR_CONDITIONS
def WORD_XOR_CONDITIONS : thm := BMasks.WORD_XOR_CONDITIONS
def VAL_WORD_MASK : thm := BMasks.VAL_WORD_MASK
def IVAL_WORD_MASK : thm := BMasks.IVAL_WORD_MASK
def INT_VAL_WORD_MASK : thm := BMasks.INT_VAL_WORD_MASK
def REAL_VAL_WORD_MASK : thm := BMasks.REAL_VAL_WORD_MASK
def WORD_MUL_EXPAND_ALT : thm := BMasks.WORD_MUL_EXPAND_ALT
def WORD_SX_ZX_GEN : thm := BMasks.WORD_SX_ZX_GEN
def BIT_WORD_SX : thm := BMasks.BIT_WORD_SX
def VAL_WORD_AND_MASK : thm := BMasks.VAL_WORD_AND_MASK
def IVAL_WORD_AND_MASK : thm := BMasks.IVAL_WORD_AND_MASK
def VAL_WORD_AND_MASK_WORD : thm := BMasks.VAL_WORD_AND_MASK_WORD
def WORD_AND_MASK_WORD : thm := BMasks.WORD_AND_MASK_WORD
def VAL_WORD_AND_NOT_MASK_WORD : thm := BMasks.VAL_WORD_AND_NOT_MASK_WORD
def WORD_AND_NOT_MASK_WORD : thm := BMasks.WORD_AND_NOT_MASK_WORD
def WORD_BITMASK : thm := BMasks.WORD_BITMASK
def MASK_WORD_SUB : thm := BMasks.MASK_WORD_SUB
def WORD_AND_MASK_WORDS : thm := BMasks.WORD_AND_MASK_WORDS
def WORD_OR_MASK_WORDS : thm := BMasks.WORD_OR_MASK_WORDS
def WORD_USHR_MASK_WORD : thm := BMasks.WORD_USHR_MASK_WORD

-- ClzCtz
def word_ctz : thm := BClzCtz.word_ctz
def word_clz : thm := BClzCtz.word_clz
def WORD_CLZ : thm := BClzCtz.WORD_CLZ
def WORD_CTZ_0 : thm := BClzCtz.WORD_CTZ_0
def WORD_LE_CTZ : thm := BClzCtz.WORD_LE_CTZ
def WORD_CTZ_LE : thm := BClzCtz.WORD_CTZ_LE
def WORD_CTZ_LE_DIMINDEX : thm := BClzCtz.WORD_CTZ_LE_DIMINDEX
def WORD_CTZ_LBOUND : thm := BClzCtz.WORD_CTZ_LBOUND
def WORD_CTZ_EQ_DIMINDEX : thm := BClzCtz.WORD_CTZ_EQ_DIMINDEX
def WORD_CTZ_LT_DIMINDEX : thm := BClzCtz.WORD_CTZ_LT_DIMINDEX
def WORD_CTZ_EQ_0 : thm := BClzCtz.WORD_CTZ_EQ_0
def WORD_CTZ_UNIQUE_GEN : thm := BClzCtz.WORD_CTZ_UNIQUE_GEN
def WORD_CTZ_UNIQUE : thm := BClzCtz.WORD_CTZ_UNIQUE
def WORD_LE_CTZ_VAL_MOD : thm := BClzCtz.WORD_LE_CTZ_VAL_MOD
def WORD_LE_CTZ_VAL : thm := BClzCtz.WORD_LE_CTZ_VAL
def WORD_CTZ_UNIQUE_VAL : thm := BClzCtz.WORD_CTZ_UNIQUE_VAL
def WORD_CLZ_0 : thm := BClzCtz.WORD_CLZ_0
def WORD_SIZE_SUB_CLZ : thm := BClzCtz.WORD_SIZE_SUB_CLZ
def WORD_CLZ_LE_DIMINDEX : thm := BClzCtz.WORD_CLZ_LE_DIMINDEX
def WORD_LE_CLZ : thm := BClzCtz.WORD_LE_CLZ
def WORD_CLZ_LE : thm := BClzCtz.WORD_CLZ_LE
def WORD_CLZ_LBOUND_ALT : thm := BClzCtz.WORD_CLZ_LBOUND_ALT
def WORD_CLZ_LBOUND : thm := BClzCtz.WORD_CLZ_LBOUND
def WORD_CLZ_EQ_DIMINDEX : thm := BClzCtz.WORD_CLZ_EQ_DIMINDEX
def WORD_CLZ_LT_DIMINDEX : thm := BClzCtz.WORD_CLZ_LT_DIMINDEX
def WORD_CLZ_EQ_0 : thm := BClzCtz.WORD_CLZ_EQ_0
def WORD_CLZ_DECOMP : thm := BClzCtz.WORD_CLZ_DECOMP
def WORD_CLZ_UNIQUE_GEN : thm := BClzCtz.WORD_CLZ_UNIQUE_GEN
def WORD_CLZ_UNIQUE : thm := BClzCtz.WORD_CLZ_UNIQUE
def WORD_LE_CLZ_VAL : thm := BClzCtz.WORD_LE_CLZ_VAL
def WORD_LE_CLZ_VAL_MULT : thm := BClzCtz.WORD_LE_CLZ_VAL_MULT
def WORD_LE_CLZ_VAL_DIV : thm := BClzCtz.WORD_LE_CLZ_VAL_DIV
def VAL_BOUND_CLZ : thm := BClzCtz.VAL_BOUND_CLZ
def WORD_CLZ_UNIQUE_VAL : thm := BClzCtz.WORD_CLZ_UNIQUE_VAL
def WORD_CTZ_BIT : thm := BClzCtz.WORD_CTZ_BIT
def WORD_CLZ_BIT : thm := BClzCtz.WORD_CLZ_BIT
def WORD_CTZ_MASK_WORD : thm := BClzCtz.WORD_CTZ_MASK_WORD
def WORD_CLZ_MASK_WORD : thm := BClzCtz.WORD_CLZ_MASK_WORD
def WORD_AND_NEG_CTZ : thm := BClzCtz.WORD_AND_NEG_CTZ
def WORD_XOR_SUB_1_CTZ : thm := BClzCtz.WORD_XOR_SUB_1_CTZ
def WORD_AND_NOT_SUB_1_CTZ : thm := BClzCtz.WORD_AND_NOT_SUB_1_CTZ
def WORD_CTZ_EMULATION_REV : thm := BClzCtz.WORD_CTZ_EMULATION_REV
def WORD_CTZ_EMULATION_AND_NEG_REV : thm := BClzCtz.WORD_CTZ_EMULATION_AND_NEG_REV
def WORD_CTZ_EMULATION_XOR_SUB_1_REV : thm := BClzCtz.WORD_CTZ_EMULATION_XOR_SUB_1_REV
def WORD_CTZ_EMULATION : thm := BClzCtz.WORD_CTZ_EMULATION
def WORD_CTZ_EMULATION_AND_NEG : thm := BClzCtz.WORD_CTZ_EMULATION_AND_NEG
def WORD_CTZ_EMULATION_XOR_SUB_1 : thm := BClzCtz.WORD_CTZ_EMULATION_XOR_SUB_1
def WORD_CLZ_IMP : thm := BClzCtz.WORD_CLZ_IMP
def WORD_CLZ_OR : thm := BClzCtz.WORD_CLZ_OR
def WORD_CTZ_IMP : thm := BClzCtz.WORD_CTZ_IMP
def WORD_CTZ_OR : thm := BClzCtz.WORD_CTZ_OR
def WORD_CLZ_MONO : thm := BClzCtz.WORD_CLZ_MONO
def WORD_CTZ_EMULATION_POPCOUNT : thm := BClzCtz.WORD_CTZ_EMULATION_POPCOUNT

-- Reverse
def word_reversefields : thm := BReverse.word_reversefields
def BIT_WORD_REVERSEFIELDS : thm := BReverse.BIT_WORD_REVERSEFIELDS
def WORD_REVERSEFIELDS_REVERSEFIELDS : thm := BReverse.WORD_REVERSEFIELDS_REVERSEFIELDS
def BIT_REVERSEFIELDS_1 : thm := BReverse.BIT_REVERSEFIELDS_1
def WORD_CTZ_REVERSEFIELDS : thm := BReverse.WORD_CTZ_REVERSEFIELDS
def WORD_CLZ_REVERSEFIELDS : thm := BReverse.WORD_CLZ_REVERSEFIELDS
def WORD_CLZ_USHR : thm := BReverse.WORD_CLZ_USHR
def WORD_SHL_AS_USHR : thm := BReverse.WORD_SHL_AS_USHR
def WORD_USHR_AS_SHL : thm := BReverse.WORD_USHR_AS_SHL
def WORD_CTZ_SHL : thm := BReverse.WORD_CTZ_SHL
def word_bytereverse : thm := BReverse.word_bytereverse
def BIT_WORD_BYTEREVERSE : thm := BReverse.BIT_WORD_BYTEREVERSE
def WORD_BYTEREVERSE_BYTEREVERSE : thm := BReverse.WORD_BYTEREVERSE_BYTEREVERSE
def WORD_BYTEREVERSE_REVERSEFIELDS : thm := BReverse.WORD_BYTEREVERSE_REVERSEFIELDS
def word_pmul : thm := BReverse.word_pmul
def BIT_WORD_PMUL_ALT : thm := BReverse.BIT_WORD_PMUL_ALT
def BIT_WORD_PMUL : thm := BReverse.BIT_WORD_PMUL
def BITVAL_BIT_WORD_PMUL : thm := BReverse.BITVAL_BIT_WORD_PMUL
def WORD_PMUL_0 : thm := BReverse.WORD_PMUL_0
def WORD_PMUL_XOR : thm := BReverse.WORD_PMUL_XOR
def WORD_PMUL_ZX : thm := BReverse.WORD_PMUL_ZX
def WORD_PMUL_STEP : thm := BReverse.WORD_PMUL_STEP
def WORD_PMUL_SYM : thm := BReverse.WORD_PMUL_SYM
def WORD_PMUL_POW2 : thm := BReverse.WORD_PMUL_POW2

-- Align
def aligned : thm := BAlign.aligned
def ALIGNED : thm := BAlign.ALIGNED
def ALIGNED_WORD : thm := BAlign.ALIGNED_WORD
def ALIGNED_IWORD : thm := BAlign.ALIGNED_IWORD
def ALIGNED_WORD_0 : thm := BAlign.ALIGNED_WORD_0
def ALIGNED_WORD_NEG : thm := BAlign.ALIGNED_WORD_NEG
def ALIGNED_WORD_ADD : thm := BAlign.ALIGNED_WORD_ADD
def ALIGNED_WORD_MUL : thm := BAlign.ALIGNED_WORD_MUL
def ALIGNED_WORD_SUB : thm := BAlign.ALIGNED_WORD_SUB
def ALIGNED_WORD_ADD_EQ : thm := BAlign.ALIGNED_WORD_ADD_EQ
def ALIGNED_WORD_SUB_EQ : thm := BAlign.ALIGNED_WORD_SUB_EQ
def word_jshl : thm := BAlign.word_jshl
def word_jshr : thm := BAlign.word_jshr
def word_jushr : thm := BAlign.word_jushr
def word_jdiv : thm := BAlign.word_jdiv
def word_jrem : thm := BAlign.word_jrem
def word_jror : thm := BAlign.word_jror
def word_jrol : thm := BAlign.word_jrol
def VAL_WORD_NEG_MOD_DIMINDEX : thm := BAlign.VAL_WORD_NEG_MOD_DIMINDEX
def WORD_JROL_JROR : thm := BAlign.WORD_JROL_JROR
def WORD_JROR_JROL : thm := BAlign.WORD_JROR_JROL
def WORD_JROR : thm := BAlign.WORD_JROR
def WORD_JROL : thm := BAlign.WORD_JROL
def WORD_JUSHR_NEG : thm := BAlign.WORD_JUSHR_NEG
def WORD_JSHL_NEG : thm := BAlign.WORD_JSHL_NEG

-- Topflip
def WORD_WORD_OPERATION_CONV : HolCore.Equal.ioconv := fun t => BTopflip.WORD_WORD_OPERATION_CONV t
def IVAL_TOPFLIP_VAL : thm := BTopflip.IVAL_TOPFLIP_VAL
def WORD_ULE_TOPFLIP : thm := BTopflip.WORD_ULE_TOPFLIP
def WORD_ULT_TOPFLIP : thm := BTopflip.WORD_ULT_TOPFLIP
def WORD_UGE_TOPFLIP : thm := BTopflip.WORD_UGE_TOPFLIP
def WORD_UGT_TOPFLIP : thm := BTopflip.WORD_UGT_TOPFLIP
def WORD_ILT_TOPFLIP : thm := BTopflip.WORD_ILT_TOPFLIP
def WORD_ILE_TOPFLIP : thm := BTopflip.WORD_ILE_TOPFLIP
def WORD_IGT_TOPFLIP : thm := BTopflip.WORD_IGT_TOPFLIP
def WORD_IGE_TOPFLIP : thm := BTopflip.WORD_IGE_TOPFLIP
def WORD_LE_ADD_EXACT : thm := BTopflip.WORD_LE_ADD_EXACT
def WORD_ADD_LT_EXACT : thm := BTopflip.WORD_ADD_LT_EXACT
def WORD_ADD_LT_INEXACT : thm := BTopflip.WORD_ADD_LT_INEXACT
def WORD_LT_ADC_EXACT : thm := BTopflip.WORD_LT_ADC_EXACT
def WORD_ADC_LE_EXACT : thm := BTopflip.WORD_ADC_LE_EXACT
def WORD_ADC_LE_INEXACT : thm := BTopflip.WORD_ADC_LE_INEXACT

-- BitWordConv
def BIT_WORD_CONV : HolCore.Equal.ioconv := fun t => BBitWordConv.BIT_WORD_CONV t

-- Blast
def WORD_BLAST : term → IO (Except String thm) := fun t => (BBlast.WORD_BLAST t).run
def WORD_POPCOUNT_ADD_OR : thm := BBlast.WORD_POPCOUNT_ADD_OR
def WORD_POPCOUNT_ADD : thm := BBlast.WORD_POPCOUNT_ADD
def WORD_POPCOUNT_MUL : thm := BBlast.WORD_POPCOUNT_MUL
def WORD_ODDPARITY_POPCOUNT : thm := BBlast.WORD_ODDPARITY_POPCOUNT
def WORD_EVENPARITY_POPCOUNT : thm := BBlast.WORD_EVENPARITY_POPCOUNT

-- Reduce1
def WORD_WORD_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_WORD_CONV t
def WORD_IWORD_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_IWORD_CONV t
def WORD_SATURATE_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_SATURATE_CONV t
def IWORD_SATURATE_CONV : HolCore.Equal.ioconv := fun t => BReduce1.IWORD_SATURATE_CONV t
def WORD_VAL_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_VAL_CONV t
def WORD_IVAL_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_IVAL_CONV t
def WORD_BIT_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_BIT_CONV t
def BIT_WORD_PMUL_CONV : HolCore.Equal.ioconv := fun t => BReduce1.BIT_WORD_PMUL_CONV t
def WORD_EQ_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_EQ_CONV t
def WORD_ULT_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_ULT_CONV t
def WORD_ULE_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_ULE_CONV t
def WORD_UGT_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_UGT_CONV t
def WORD_UGE_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_UGE_CONV t
def WORD_ILT_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_ILT_CONV t
def WORD_ILE_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_ILE_CONV t
def WORD_IGT_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_IGT_CONV t
def WORD_IGE_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_IGE_CONV t
def WORD_ADD_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_ADD_CONV t
def WORD_MUL_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_MUL_CONV t
def WORD_SUB_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_SUB_CONV t
def WORD_NEG_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_NEG_CONV t
def WORD_UDIV_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_UDIV_CONV t
def WORD_UMOD_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_UMOD_CONV t
def WORD_UMAX_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_UMAX_CONV t
def WORD_UMIN_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_UMIN_CONV t
def WORD_IMAX_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_IMAX_CONV t
def WORD_IMIN_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_IMIN_CONV t
def WORD_SHL_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_SHL_CONV t
def WORD_USHR_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_USHR_CONV t
def WORD_ISHR_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_ISHR_CONV t
def WORD_NOT_CONV : HolCore.Equal.ioconv := fun t => BReduce1.WORD_NOT_CONV t

-- Reduce2
def WORD_AND_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_AND_CONV t
def WORD_OR_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_OR_CONV t
def WORD_XOR_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_XOR_CONV t
def WORD_ROL_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_ROL_CONV t
def WORD_ROR_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_ROR_CONV t
def WORD_ZX_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_ZX_CONV t
def WORD_SX_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_SX_CONV t
def WORD_SXFROM_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_SXFROM_CONV t
def WORD_CAND_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_CAND_CONV t
def WORD_COR_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_COR_CONV t
def WORD_JOIN_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_JOIN_CONV t
def WORD_SUBWORD_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_SUBWORD_CONV t
def WORD_INSERT_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_INSERT_CONV t
def WORD_DUPLICATE_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_DUPLICATE_CONV t
def WORD_BITS_OF_WORD_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_BITS_OF_WORD_CONV t
def WORD_POPCOUNT_CONV : HolCore.Equal.ioconv := fun t => BReduce2.WORD_POPCOUNT_CONV t

-- Reduce3
def WORD_EVENPARITY_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_EVENPARITY_CONV t
def WORD_ODDPARITY_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_ODDPARITY_CONV t
def WORD_CTZ_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_CTZ_CONV t
def WORD_CLZ_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_CLZ_CONV t
def WORD_BYTEREVERSE_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_BYTEREVERSE_CONV t
def WORD_REVERSEFIELDS_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_REVERSEFIELDS_CONV t
def WORD_PMUL_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_PMUL_CONV t
def WORD_JSHL_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_JSHL_CONV t
def WORD_JSHR_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_JSHR_CONV t
def WORD_JUSHR_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_JUSHR_CONV t
def WORD_JROL_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_JROL_CONV t
def WORD_JROR_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_JROR_CONV t
def WORD_JDIV_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_JDIV_CONV t
def WORD_JREM_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_JREM_CONV t
def word_red_conv_list := BReduce3.word_red_conv_list
def WORD_RED_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_RED_CONV t
def WORD_REDUCE_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_REDUCE_CONV t
def word_compute_add_convs := BReduce3.word_compute_add_convs
def WORD_COMPUTE_CONV : HolCore.Equal.ioconv := fun t => BReduce3.WORD_COMPUTE_CONV t

-- Wordify
def WORD_TO_IWORD_CONV : HolCore.Equal.ioconv := fun t => BWordify.WORD_TO_IWORD_CONV t
def WORD_IREDUCE_CONV : HolCore.Equal.ioconv := fun t => BWordify.WORD_IREDUCE_CONV t
def EXPAND_NSUM_BALANCE_CONV : HolCore.Equal.ioconv := fun t => BWordify.EXPAND_NSUM_BALANCE_CONV t
def WORD_COMPARISON_ULT : thm := BWordify.WORD_COMPARISON_ULT
def WORD_COMPARISON_ULE : thm := BWordify.WORD_COMPARISON_ULE
def WORD_COMPARISON_ILT : thm := BWordify.WORD_COMPARISON_ILT
def WORD_COMPARISON_ILE : thm := BWordify.WORD_COMPARISON_ILE
def WORD_COMPARISON_NE : thm := BWordify.WORD_COMPARISON_NE
def WORD_COMPARISON_EQ : thm := BWordify.WORD_COMPARISON_EQ
def WORDIFY_CONV : HolCore.Equal.ioconv := fun t => BWordify.WORDIFY_CONV t
def VAL_WORD_ADJUST_CONV := BWordify.VAL_WORD_ADJUST_CONV
def VAL_WORD_ADJUST_BINOP_CONV : HolCore.Equal.ioconv := fun t => BWordify.VAL_WORD_ADJUST_BINOP_CONV t
def WORDIFY_ATOM_CONV : HolCore.Equal.ioconv := fun t => BWordify.WORDIFY_ATOM_CONV t
def IWORDIFY_CONV : HolCore.Equal.ioconv := fun t => BWordify.IWORDIFY_CONV t
def IVAL_WORD_ADJUST_CONV := BWordify.IVAL_WORD_ADJUST_CONV
def IVAL_WORD_ADJUST_BINOP_CONV : HolCore.Equal.ioconv := fun t => BWordify.IVAL_WORD_ADJUST_BINOP_CONV t
def IWORDIFY_ATOM_CONV : HolCore.Equal.ioconv := fun t => BWordify.IWORDIFY_ATOM_CONV t
def WORDIFY_WORD_CONV : HolCore.Equal.ioconv := fun t => BWordify.WORDIFY_WORD_CONV t

-- Bitblast
def WORD_MUL_EXPAND_CONV : HolCore.Equal.ioconv := fun t => BBitblast.WORD_MUL_EXPAND_CONV t
def WORD_POPCOUNT_EXPAND_CONV : HolCore.Equal.ioconv := fun t => BBitblast.WORD_POPCOUNT_EXPAND_CONV t
def WORD_INEQ_RELATION_EXPAND_CONV : HolCore.Equal.ioconv := fun t => BBitblast.WORD_INEQ_RELATION_EXPAND_CONV t
def VAL_MOD_OR_DIV_CONV : HolCore.Equal.ioconv := fun t => BBitblast.VAL_MOD_OR_DIV_CONV t
def BITBLAST_THEN := BBitblast.BITBLAST_THEN
def BITBLAST_TAC : HolCore.Tactics.tactic := fun g => BBitblast.BITBLAST_TAC g
def BITBLAST_RULE : term → IO (Except String thm) := fun t => (BBitblast.BITBLAST_RULE t).run

-- Simd
def usimd2 : thm := BSimd.usimd2
def simd2 : thm := BSimd.simd2
def usimd4 : thm := BSimd.usimd4
def simd4 : thm := BSimd.simd4
def usimd8 : thm := BSimd.usimd8
def simd8 : thm := BSimd.simd8
def usimd16 : thm := BSimd.usimd16
def simd16 : thm := BSimd.simd16
def USIMD2 : thm := BSimd.USIMD2
def SIMD2 : thm := BSimd.SIMD2

/- The procedures (by hand, not generated). -/
/-- `BIT_PRED` (words.ml 1337). -/
def BIT_PRED (t : term) : Except String (Option term × thm) := BNumBits.BIT_PRED t
/-- `NUMBIT_CONV` (words.ml 1337). -/
def NUMBIT_CONV : HolCore.Equal.ioconv := fun t => BNumBits.NUMBIT_CONV t
/-- `NUM_SHIFT_ADD_CORE` (words.ml 1628). -/
def NUM_SHIFT_ADD_CORE (a b i : term) : Except String thm :=
  BNumShiftAdd.NUM_SHIFT_ADD_CORE a b i
/-- `NUM_SHIFT_ADD_CONV` (words.ml 1628). -/
def NUM_SHIFT_ADD_CONV : HolCore.Equal.ioconv := fun t => BNumShiftAdd.NUM_SHIFT_ADD_CONV t

/-- A no-op: importing this module has loaded words.ml.  Kept for callers of
    the old `ensureWords`. -/
def ensureWords : IO Unit := pure ()

end SessionLibrary.Words
