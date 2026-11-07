/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/pocklington.ml.                            -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Pocklington.lean

  The session half of the pocklington.ml translation: it supplies
  HolLibrary.Pocklington's dependencies from Session, SessionLibrary.Iter
  and SessionLibrary.Prime, and exports every name under its HOL Light name.
  Importing this module is `needs "Library/pocklington.ml"`; its
  `needs "Library/iter.ml"` and `needs "Library/prime.ml"` are the imports
  of SessionLibrary.Iter and SessionLibrary.Prime.  Each bundle is built by
  `initialize` when the module is loaded, in file order.
-/

import Session
import HolLibrary.Pocklington
import SessionLibrary.Iter
import SessionLibrary.Prime

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Pocklington

/-- The core theorems pocklington.ml uses. -/
def core1 : HolLibrary.Pocklington.CoreThms1 where
  ADD1 := Session.ADD1
  ADD_AC := Session.ADD_AC
  ADD_ASSOC := Session.ADD_ASSOC
  ADD_CLAUSES := Session.ADD_CLAUSES
  ADD_EQ_0 := Session.ADD_EQ_0
  ADD_SUB := Session.ADD_SUB
  ADD_SYM := Session.ADD_SYM
  ALL := Session.listDefs.ALL
  AND_FORALL_THM := Session.AND_FORALL_THM
  ARITH := Session.ARITH
  ARITH_EQ := Session.ARITH_EQ
  BETA_THM := Session.BETA_THM
  BEZOUT_GCD_STRONG := SessionLibrary.Prime.«BEZOUT_GCD_STRONG»
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARD_DIFF := Session.CARD_DIFF
  CARD_IMAGE_INJ := Session.CARD_IMAGE_INJ
  CARD_IMAGE_INJ_EQ := Session.CARD_IMAGE_INJ_EQ
  CARD_NUMSEG_LE := Session.CARD_NUMSEG_LE
  CARD_NUMSEG_LT := Session.CARD_NUMSEG_LT
  CARD_PRODUCT := Session.CARD_PRODUCT
  CARD_SUBSET := Session.CARD_SUBSET
  CARD_SUBSET_EQ := Session.CARD_SUBSET_EQ
  CHINESE_REMAINDER := SessionLibrary.Prime.«CHINESE_REMAINDER»
  COMPLETE_FACTOR_INDUCT := SessionLibrary.Prime.«COMPLETE_FACTOR_INDUCT»
  COND_CLAUSES := Session.COND_CLAUSES
  COND_ID := Session.COND_ID
  CONG := Session.CONG
  CONG_DIV2 := Session.CONG_DIV2
  CONG_LMOD := Session.CONG_LMOD
  CONG_RMOD := Session.CONG_RMOD
  CONJ_ASSOC := Session.CONJ_ASSOC
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  COPRIME_0 := SessionLibrary.Prime.«COPRIME_0»
  COPRIME_1 := SessionLibrary.Prime.«COPRIME_1»
  COPRIME_EXP := SessionLibrary.Prime.«COPRIME_EXP»
  COPRIME_GCD := SessionLibrary.Prime.«COPRIME_GCD»
  COPRIME_LEXP := SessionLibrary.Prime.«COPRIME_LEXP»
  COPRIME_LMOD := Session.COPRIME_LMOD
  COPRIME_LMUL := SessionLibrary.Prime.«COPRIME_LMUL»
  COPRIME_LMUL2 := SessionLibrary.Prime.«COPRIME_LMUL2»
  COPRIME_MUL := SessionLibrary.Prime.«COPRIME_MUL»
  COPRIME_NPRODUCT := SessionLibrary.Prime.«COPRIME_NPRODUCT»
  COPRIME_NPRODUCT_EQ := SessionLibrary.Prime.«COPRIME_NPRODUCT_EQ»
  COPRIME_PRIMEPOW := SessionLibrary.Prime.«COPRIME_PRIMEPOW»
  COPRIME_PRIME_PRIME := SessionLibrary.Prime.«COPRIME_PRIME_PRIME»
  COPRIME_REFL := SessionLibrary.Prime.«COPRIME_REFL»
  COPRIME_REXP := SessionLibrary.Prime.«COPRIME_REXP»
  COPRIME_RMOD := Session.COPRIME_RMOD
  COPRIME_RMUL := SessionLibrary.Prime.«COPRIME_RMUL»
  COPRIME_RMUL2 := SessionLibrary.Prime.«COPRIME_RMUL2»
  COPRIME_SYM := SessionLibrary.Prime.«COPRIME_SYM»
  CROSS_EMPTY := Session.CROSS_EMPTY
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DIVIDES_0 := SessionLibrary.Prime.«DIVIDES_0»
  DIVIDES_1 := SessionLibrary.Prime.«DIVIDES_1»
  DIVIDES_ADD := SessionLibrary.Prime.«DIVIDES_ADD»
  DIVIDES_ADD_REVL := SessionLibrary.Prime.«DIVIDES_ADD_REVL»
  DIVIDES_ADD_REVR := SessionLibrary.Prime.«DIVIDES_ADD_REVR»
  DIVIDES_ANTISYM := Session.DIVIDES_ANTISYM
  DIVIDES_DIV_MULT := Session.DIVIDES_DIV_MULT
  DIVIDES_EXP_LE := SessionLibrary.Prime.«DIVIDES_EXP_LE»
  DIVIDES_EXP_LE_IMP := SessionLibrary.Prime.«DIVIDES_EXP_LE_IMP»
  DIVIDES_GCD := SessionLibrary.Prime.«DIVIDES_GCD»
  DIVIDES_GCD_RIGHT := SessionLibrary.Prime.«DIVIDES_GCD_RIGHT»
  DIVIDES_INDEX := SessionLibrary.Prime.«DIVIDES_INDEX»
  DIVIDES_LCM_RIGHT := SessionLibrary.Prime.«DIVIDES_LCM_RIGHT»
  DIVIDES_LE := Session.DIVIDES_LE
  DIVIDES_LE_IMP := Session.DIVIDES_LE_IMP
  DIVIDES_LE_STRONG := Session.DIVIDES_LE_STRONG
  DIVIDES_LMUL := SessionLibrary.Prime.«DIVIDES_LMUL»
  DIVIDES_LMUL2_EQ := SessionLibrary.Prime.«DIVIDES_LMUL2_EQ»
  DIVIDES_MOD := Session.DIVIDES_MOD
  DIVIDES_MUL := SessionLibrary.Prime.«DIVIDES_MUL»
/-- The core theorems pocklington.ml uses. -/
def core2 : HolLibrary.Pocklington.CoreThms2 where
  DIVIDES_MUL2 := SessionLibrary.Prime.«DIVIDES_MUL2»
  DIVIDES_ONE := Session.DIVIDES_ONE
  DIVIDES_PRIME_PRIME := SessionLibrary.Prime.«DIVIDES_PRIME_PRIME»
  DIVIDES_REFL := SessionLibrary.Prime.«DIVIDES_REFL»
  DIVIDES_REXP := SessionLibrary.Prime.«DIVIDES_REXP»
  DIVIDES_RMUL := SessionLibrary.Prime.«DIVIDES_RMUL»
  DIVIDES_RMUL2_EQ := SessionLibrary.Prime.«DIVIDES_RMUL2_EQ»
  DIVIDES_SUB := SessionLibrary.Prime.«DIVIDES_SUB»
  DIVIDES_TRANS := SessionLibrary.Prime.«DIVIDES_TRANS»
  DIVIDES_ZERO := SessionLibrary.Prime.«DIVIDES_ZERO»
  DIVISION := Session.DIVISION
  DIVISION_0 := Session.DIVISION_0
  DIVISION_SIMP := Session.DIVISION_SIMP
  DIV_0 := Session.DIV_0
  DIV_EQ_0 := Session.DIV_EQ_0
  DIV_MONO := Session.DIV_MONO
  DIV_MULT := Session.DIV_MULT
  DIV_UNIQ := Session.DIV_UNIQ
  EMPTY_GSPEC := Session.EMPTY_GSPEC
  EQ_ADD_RCANCEL := Session.EQ_ADD_RCANCEL
  EQ_IMP := Session.EQ_IMP
  EQ_MULT_LCANCEL := Session.EQ_MULT_LCANCEL
  EQ_MULT_RCANCEL := Session.EQ_MULT_RCANCEL
  EQ_TRANS := Session.EQ_TRANS
  EVEN := Session.EVEN
  EVEN_EXISTS := Session.EVEN_EXISTS
  EVEN_EXP := Session.EVEN_EXP
  EVEN_MULT := Session.EVEN_MULT
  EVEN_SUB := Session.EVEN_SUB
  EXISTS_IN_IMAGE := Session.EXISTS_IN_IMAGE
  EXISTS_PAIR_THM := Session.EXISTS_PAIR_THM
  EXISTS_REFL := Session.EXISTS_REFL
  EXISTS_UNIQUE := Session.EXISTS_UNIQUE
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXP := Session.EXP
  EXP_1 := Session.EXP_1
  EXP_2 := Session.EXP_2
  EXP_ADD := Session.EXP_ADD
  EXP_EQ_0 := Session.EXP_EQ_0
  EXP_EQ_1 := Session.EXP_EQ_1
  EXP_EXP := Session.EXP_EXP
  EXP_MONO_LE := Session.EXP_MONO_LE
  EXP_MULT := Session.EXP_MULT
  EXP_ONE := Session.EXP_ONE
  EXTENSION := Session.EXTENSION
  FINITE_DIVISORS := SessionLibrary.Prime.«FINITE_DIVISORS»
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_NUMSEG := Session.FINITE_NUMSEG
  FINITE_NUMSEG_LE := Session.FINITE_NUMSEG_LE
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_RULES := Session.FINITE_RULES
  FINITE_SPECIAL_DIVISORS := SessionLibrary.Prime.«FINITE_SPECIAL_DIVISORS»
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_AND_THM := Session.FORALL_AND_THM
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  FORALL_UNWIND_THM1 := Session.FORALL_UNWIND_THM1
  FUN_EQ_THM := Session.FUN_EQ_THM
  GCD := Session.GCD
  GCD_0 := SessionLibrary.Prime.«GCD_0»
  GCD_SYM := SessionLibrary.Prime.«GCD_SYM»
  GCD_ZERO := SessionLibrary.Prime.«GCD_ZERO»
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_0 := Session.HAS_SIZE_0
  HAS_SIZE_CROSS := Session.HAS_SIZE_CROSS
  HAS_SIZE_IMAGE_INJ := Session.HAS_SIZE_IMAGE_INJ
  HAS_SIZE_IMAGE_INJ_EQ := Session.HAS_SIZE_IMAGE_INJ_EQ
  HAS_SIZE_NUMSEG_LT := Session.HAS_SIZE_NUMSEG_LT
  IMAGE_CLAUSES := Session.IMAGE_CLAUSES
  IMAGE_EQ_EMPTY := Session.IMAGE_EQ_EMPTY
/-- The core theorems pocklington.ml uses. -/
def core3 : HolLibrary.Pocklington.CoreThms3 where
  IMP_CONJ := Session.IMP_CONJ
  IMP_IMP := Session.IMP_IMP
  IN := Session.IN
  INDEX_EQ_0 := SessionLibrary.Prime.«INDEX_EQ_0»
  INDEX_EXP := SessionLibrary.Prime.«INDEX_EXP»
  INDEX_GCD := SessionLibrary.Prime.«INDEX_GCD»
  INDEX_PRIME := SessionLibrary.Prime.«INDEX_PRIME»
  INDUCT_COPRIME_ALT := SessionLibrary.Prime.«INDUCT_COPRIME_ALT»
  INDUCT_COPRIME_STRONG := SessionLibrary.Prime.«INDUCT_COPRIME_STRONG»
  INT_IMAGE := Session.INT_IMAGE
  INT_MUL_RZERO := Session.INT_MUL_RZERO
  INT_OF_NUM_ADD := Session.INT_OF_NUM_ADD
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_LT := Session.INT_OF_NUM_LT
  INT_OF_NUM_MUL := Session.INT_OF_NUM_MUL
  INT_OF_NUM_POW := Session.INT_OF_NUM_POW
  INT_OF_NUM_SUB := Session.INT_OF_NUM_SUB
  IN_CROSS := Session.IN_CROSS
  IN_ELIM_PAIR_THM := Session.IN_ELIM_PAIR_THM
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_NUMSEG := Session.IN_NUMSEG
  IN_SING := Session.IN_SING
  ITER := SessionLibrary.Iter.«ITER»
  ITERATE_CLAUSES := Session.ITERATE_CLAUSES
  ITERATE_EQ := Session.ITERATE_EQ
  ITERATE_EQ_GENERAL_INVERSES := Session.ITERATE_EQ_GENERAL_INVERSES
  ITERATE_ITERATE_PRODUCT := Session.ITERATE_ITERATE_PRODUCT
  ITERATE_RELATED := Session.ITERATE_RELATED
  ITLIST := Session.listDefs.ITLIST
  LCM_0 := SessionLibrary.Prime.«LCM_0»
  LCM_COPRIME_DECOMP := SessionLibrary.Prime.«LCM_COPRIME_DECOMP»
  LCM_DIVIDES := SessionLibrary.Prime.«LCM_DIVIDES»
  LE := Session.LE
  LEFT_ADD_DISTRIB := Session.LEFT_ADD_DISTRIB
  LEFT_AND_EXISTS_THM := Session.LEFT_AND_EXISTS_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LEFT_SUB_DISTRIB := Session.LEFT_SUB_DISTRIB
  LE_0 := Session.LE_0
  LE_1 := Session.LE_1
  LE_ANTISYM := Session.LE_ANTISYM
  LE_CASES := Session.LE_CASES
  LE_EXISTS := Session.LE_EXISTS
  LE_EXP := Session.LE_EXP
  LE_LCM := SessionLibrary.Prime.«LE_LCM»
  LE_LT := Session.LE_LT
  LE_MULT2 := Session.LE_MULT2
  LE_MULT_LCANCEL := Session.LE_MULT_LCANCEL
  LE_MULT_RCANCEL := Session.LE_MULT_RCANCEL
  LE_RDIV_EQ := Session.LE_RDIV_EQ
  LE_REFL := Session.LE_REFL
  LE_TRANS := Session.LE_TRANS
  LT := Session.LT
  LT_LE := Session.LT_LE
  LT_MULT_LCANCEL := Session.LT_MULT_LCANCEL
  LT_NZ := Session.LT_NZ
  LT_REFL := Session.LT_REFL
  LT_TRANS := Session.LT_TRANS
  MEM := Session.listDefs.MEM
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MOD_2_CASES := Session.MOD_2_CASES
  MOD_EQ_0 := Session.MOD_EQ_0
  MOD_EQ_SELF := Session.MOD_EQ_SELF
  MOD_EXP_MOD := Session.MOD_EXP_MOD
  MOD_LT := Session.MOD_LT
  MOD_LT_EQ := Session.MOD_LT_EQ
  MOD_MOD_REFL := Session.MOD_MOD_REFL
  MOD_UNIQ := Session.MOD_UNIQ
  MOD_ZERO := Session.MOD_ZERO
  MONOIDAL_MUL := Session.MONOIDAL_MUL
  MONO_AND := Session.MONO_AND
  MONO_EXISTS := Session.MONO_EXISTS
/-- The core theorems pocklington.ml uses. -/
def core4 : HolLibrary.Pocklington.CoreThms4 where
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
  NOT_LT := Session.NOT_LT
  NOT_ODD := Session.NOT_ODD
  NOT_SUC := Session.NOT_SUC
  NPRODUCT_CLAUSES := Session.NPRODUCT_CLAUSES
  ODD_EXISTS := Session.ODD_EXISTS
  ORDER_EXISTENCE_ITER := SessionLibrary.Iter.«ORDER_EXISTENCE_ITER»
  OR_EXISTS_THM := Session.OR_EXISTS_THM
  PAIRWISE_EMPTY := Session.PAIRWISE_EMPTY
  PAIRWISE_INSERT := Session.PAIRWISE_INSERT
  PAIR_EQ := Session.PAIR_EQ
  PRIME := SessionLibrary.Prime.«PRIME»
  PRIMEPOW_DIVIDES_INDEX := SessionLibrary.Prime.«PRIMEPOW_DIVIDES_INDEX»
  PRIME_0 := SessionLibrary.Prime.«PRIME_0»
  PRIME_1 := SessionLibrary.Prime.«PRIME_1»
  PRIME_2 := SessionLibrary.Prime.«PRIME_2»
  PRIME_COPRIME := SessionLibrary.Prime.«PRIME_COPRIME»
  PRIME_COPRIME_EQ := SessionLibrary.Prime.«PRIME_COPRIME_EQ»
  PRIME_DIVEXP_EQ := SessionLibrary.Prime.«PRIME_DIVEXP_EQ»
  PRIME_DIVPROD_POW_EQ := SessionLibrary.Prime.«PRIME_DIVPROD_POW_EQ»
  PRIME_DIVPROD_POW_GEN_EQ := SessionLibrary.Prime.«PRIME_DIVPROD_POW_GEN_EQ»
  PRIME_EXP := SessionLibrary.Prime.«PRIME_EXP»
  PRIME_FACTOR := SessionLibrary.Prime.«PRIME_FACTOR»
  PRIME_FACTORIZATION := SessionLibrary.Prime.«PRIME_FACTORIZATION»
  PRIME_GE_2 := SessionLibrary.Prime.«PRIME_GE_2»
  PRIME_IMP_NZ := SessionLibrary.Prime.«PRIME_IMP_NZ»
  PRIME_ODD := SessionLibrary.Prime.«PRIME_ODD»
  RDIV_LT_EQ := Session.RDIV_LT_EQ
  RIGHT_AND_EXISTS_THM := Session.RIGHT_AND_EXISTS_THM
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RIGHT_IMP_FORALL_THM := Session.RIGHT_IMP_FORALL_THM
  RIGHT_SUB_DISTRIB := Session.RIGHT_SUB_DISTRIB
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUBSET_ANTISYM_EQ := Session.SUBSET_ANTISYM_EQ
  SUB_0 := Session.SUB_0
  SUB_ADD := Session.SUB_ADD
  SUB_REFL := Session.SUB_REFL
  SURJECTIVE_IFF_INJECTIVE_GEN := Session.SURJECTIVE_IFF_INJECTIVE_GEN
  SWAP_EXISTS_THM := Session.SWAP_EXISTS_THM
  SWAP_FORALL_THM := Session.SWAP_FORALL_THM
  UNIQUE_SKOLEM_THM := Session.UNIQUE_SKOLEM_THM
  UNWIND_THM2 := Session.UNWIND_THM2
  cong := Session.cong
  coprime := Session.coprime
  divides := Session.divides
  index_def := SessionLibrary.Prime.«index_def»
  int_congruent := Session.int_congruent
  int_of_num := Session.int_of_num
  nproduct := Session.nproduct
  num_FINITE := Session.num_FINITE
  num_INDUCTION := Session.num_INDUCTION
  num_MAX := Session.num_MAX
  num_WOP := Session.num_WOP
  num_congruent := Session.num_congruent
  num_divides := Session.num_divides
  pairwise := Session.pairwise
  prime := Session.prime
  MOD_LE := Session.MOD_LE
  MOD_MULT := Session.MOD_MULT
  PRIME_DIVPROD := SessionLibrary.Prime.«PRIME_DIVPROD»
  ALL_IMP := Session.listThms1.ALL_IMP
  ALL_MEM := Session.listThms1.ALL_MEM
  num_WF := Session.num_WF
  LT_MULT_RCANCEL := Session.LT_MULT_RCANCEL

/-- What pocklington.ml uses from Session. -/
def deps : HolLibrary.Pocklington.PocklingtonDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  prioritize_num := do
    match ← HolCore.Kernel.mk_type "num" [] with
    | .ok ty => Session.prioritize_overload ty
    | .error e => throw (IO.userError e)
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  INTEGER_RULE t := ExceptT.mk (Session.INTEGER_RULE t)
  INT_ARITH t := ExceptT.mk (Session.INT_ARITH t)
  INT_ARITH_TAC := Session.INT_ARITH_TAC
  LIST_INDUCT_TAC := Session.LIST_INDUCT_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  NUMBER_RULE t := ExceptT.mk (Session.NUMBER_RULE t)
  NUMBER_TAC := Session.NUMBER_TAC
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  DIVIDES_CONV := SessionLibrary.Prime.DIVIDES_CONV
  COPRIME_CONV := SessionLibrary.Prime.COPRIME_CONV
  EXP_MOD_CONV := Session.EXP_MOD_CONV
  NUM_DIV_CONV := Session.NUM_DIV_CONV
  NUM_EQ_CONV := Session.NUM_EQ_CONV
  NUM_LE_CONV := Session.NUM_LE_CONV
  NUM_MULT_CONV := Session.NUM_MULT_CONV
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  NUM_SUB_CONV := Session.NUM_SUB_CONV
  SELECT_CONV t := pure (Session.SELECT_CONV t)
  num_CONV := Session.num_CONV
  mk_numeral := Session.mk_numeral
  mk_small_numeral := Session.mk_small_numeral
  mk_flist := Session.mk_flist
  core1 := core1
  core2 := core2
  core3 := core3
  core4 := core4

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in pocklington.ml order. -/
initialize BBasics : HolLibrary.Pocklington.Basics ←
  ioB "setupBasics" (HolLibrary.Pocklington.setupBasics deps).run
initialize BSolve : HolLibrary.Pocklington.Solve ←
  ioB "setupSolve" (HolLibrary.Pocklington.setupSolve deps BBasics).run
initialize BSquarefree : HolLibrary.Pocklington.Squarefree ←
  ioB "setupSquarefree" (HolLibrary.Pocklington.setupSquarefree deps BBasics).run
initialize BPhi : HolLibrary.Pocklington.Phi ←
  ioB "setupPhi" (HolLibrary.Pocklington.setupPhi deps BBasics BSolve).run
initialize BOrder : HolLibrary.Pocklington.Order ←
  ioB "setupOrder" (HolLibrary.Pocklington.setupOrder deps BBasics BSolve BPhi).run
initialize BPock : HolLibrary.Pocklington.Pock ←
  ioB "setupPock" (HolLibrary.Pocklington.setupPock deps BBasics BPhi BOrder).run
initialize BCertify : HolLibrary.Pocklington.Certify ←
  ioB "setupCertify" (HolLibrary.Pocklington.setupCertify deps BPock).run

-- Basics
def nat_mod_lemma : thm := BBasics.nat_mod_lemma
def nat_mod : thm := BBasics.nat_mod
def FINITE_NUMBER_SEGMENT : thm := BBasics.FINITE_NUMBER_SEGMENT
def CONG_MOD_0 : thm := BBasics.CONG_MOD_0
def CONG_MOD_1 : thm := BBasics.CONG_MOD_1
def CONG_MOD_2 : thm := BBasics.CONG_MOD_2
def CONG_MOD_2_ALT : thm := BBasics.CONG_MOD_2_ALT
def CONG_0 : thm := BBasics.CONG_0
def CONG_SUB_CASES : thm := BBasics.CONG_SUB_CASES
def CONG_MINUS1 : thm := BBasics.CONG_MINUS1
def CONG_MINUS1_SQUARED : thm := BBasics.CONG_MINUS1_SQUARED
def CONG_CASES : thm := BBasics.CONG_CASES
def CONG_CASE : thm := BBasics.CONG_CASE
def CONG_MULT_LCANCEL : thm := BBasics.CONG_MULT_LCANCEL
def CONG_MULT_RCANCEL : thm := BBasics.CONG_MULT_RCANCEL
def CONG_REFL : thm := BBasics.CONG_REFL
def EQ_IMP_CONG : thm := BBasics.EQ_IMP_CONG
def CONG_SYM : thm := BBasics.CONG_SYM
def CONG_TRANS : thm := BBasics.CONG_TRANS
def CONG_ADD : thm := BBasics.CONG_ADD
def CONG_MULT : thm := BBasics.CONG_MULT
def CONG_MULT_1 : thm := BBasics.CONG_MULT_1
def CONG_EXP : thm := BBasics.CONG_EXP
def CONG_EXP_1 : thm := BBasics.CONG_EXP_1
def CONG_SUB : thm := BBasics.CONG_SUB
def CONG_MULT_LCANCEL_EQ : thm := BBasics.CONG_MULT_LCANCEL_EQ
def CONG_MULT_RCANCEL_EQ : thm := BBasics.CONG_MULT_RCANCEL_EQ
def CONG_ADD_LCANCEL_EQ : thm := BBasics.CONG_ADD_LCANCEL_EQ
def CONG_ADD_RCANCEL_EQ : thm := BBasics.CONG_ADD_RCANCEL_EQ
def CONG_ADD_RCANCEL : thm := BBasics.CONG_ADD_RCANCEL
def CONG_ADD_LCANCEL : thm := BBasics.CONG_ADD_LCANCEL
def CONG_ADD_LCANCEL_EQ_0 : thm := BBasics.CONG_ADD_LCANCEL_EQ_0
def CONG_ADD_RCANCEL_EQ_0 : thm := BBasics.CONG_ADD_RCANCEL_EQ_0
def CONG_MULT_LCANCEL_ALL : thm := BBasics.CONG_MULT_LCANCEL_ALL
def CONG_LMUL : thm := BBasics.CONG_LMUL
def CONG_RMUL : thm := BBasics.CONG_RMUL
def CONG_IMP_EQ : thm := BBasics.CONG_IMP_EQ
def CONG_DIVIDES_MODULUS : thm := BBasics.CONG_DIVIDES_MODULUS
def CONG_0_DIVIDES : thm := BBasics.CONG_0_DIVIDES
def CONG_1_DIVIDES : thm := BBasics.CONG_1_DIVIDES
def CONG_1_DIVIDES_EQ : thm := BBasics.CONG_1_DIVIDES_EQ
def CONG_DIVIDES : thm := BBasics.CONG_DIVIDES
def CONG_COPRIME : thm := BBasics.CONG_COPRIME
def CONG_GCD_RIGHT : thm := BBasics.CONG_GCD_RIGHT
def CONG_GCD_LEFT : thm := BBasics.CONG_GCD_LEFT
def CONG_MOD : thm := BBasics.CONG_MOD
def MOD_MULT_CONG : thm := BBasics.MOD_MULT_CONG
def CONG_MOD_LT : thm := BBasics.CONG_MOD_LT
def MOD_UNIQUE : thm := BBasics.MOD_UNIQUE
def CONG_DIV : thm := BBasics.CONG_DIV
def CONG_DIV_COPRIME : thm := BBasics.CONG_DIV_COPRIME
def CONG_SQUARE_1_PRIME_POWER : thm := BBasics.CONG_SQUARE_1_PRIME_POWER
def CONG_LT : thm := BBasics.CONG_LT
def CONG_LE : thm := BBasics.CONG_LE
def CONG_TO_1 : thm := BBasics.CONG_TO_1
def EVEN_MOD_2 : thm := BBasics.EVEN_MOD_2
def ODD_MOD_2 : thm := BBasics.ODD_MOD_2
def CONG_CONV : term → IO (Except String thm) := fun t => (BBasics.CONG_CONV t).run

-- Solve
def CONG_SOLVE_EQ : thm := BSolve.CONG_SOLVE_EQ
def CONG_SOLVE_LT_EQ : thm := BSolve.CONG_SOLVE_LT_EQ
def CONG_SOLVE : thm := BSolve.CONG_SOLVE
def CONG_SOLVE_UNIQUE : thm := BSolve.CONG_SOLVE_UNIQUE
def CONG_SOLVE_UNIQUE_NONTRIVIAL : thm := BSolve.CONG_SOLVE_UNIQUE_NONTRIVIAL
def CONG_UNIQUE_INVERSE_PRIME : thm := BSolve.CONG_UNIQUE_INVERSE_PRIME
def COUNT_CONG_SOLVE_SIMPLE : thm := BSolve.COUNT_CONG_SOLVE_SIMPLE
def COUNT_CONG_SOLVE_GEN : thm := BSolve.COUNT_CONG_SOLVE_GEN
def COUNT_CONG_SOLVE : thm := BSolve.COUNT_CONG_SOLVE
def CONG_CHINESE : thm := BSolve.CONG_CHINESE
def CHINESE_REMAINDER_UNIQUE : thm := BSolve.CHINESE_REMAINDER_UNIQUE
def CHINESE_REMAINDER_COPRIME_UNIQUE : thm := BSolve.CHINESE_REMAINDER_COPRIME_UNIQUE
def CHINESE_REMAINDER_USUAL : thm := BSolve.CHINESE_REMAINDER_USUAL
def CONG_CHINESE_EQ : thm := BSolve.CONG_CHINESE_EQ
def CHINESE_REMAINDER_COUNT : thm := BSolve.CHINESE_REMAINDER_COUNT
def CHINESE_REMAINDER_COPRIME_COUNT : thm := BSolve.CHINESE_REMAINDER_COPRIME_COUNT
def COUNT_ROOTS_MODULO_COPRIME : thm := BSolve.COUNT_ROOTS_MODULO_COPRIME
def inverse_mod : thm := BSolve.inverse_mod
def INVERSE_MOD_BOUND : thm := BSolve.INVERSE_MOD_BOUND
def INVERSE_MOD_RMUL_GEN : thm := BSolve.INVERSE_MOD_RMUL_GEN
def INVERSE_MOD_LMUL_GEN : thm := BSolve.INVERSE_MOD_LMUL_GEN
def INVERSE_MOD_RMUL_EQ : thm := BSolve.INVERSE_MOD_RMUL_EQ
def INVERSE_MOD_LMUL_EQ : thm := BSolve.INVERSE_MOD_LMUL_EQ
def INVERSE_MOD_LMUL : thm := BSolve.INVERSE_MOD_LMUL
def INVERSE_MOD_RMUL : thm := BSolve.INVERSE_MOD_RMUL
def INVERSE_MOD_UNIQUE : thm := BSolve.INVERSE_MOD_UNIQUE
def INVERSE_MOD_1 : thm := BSolve.INVERSE_MOD_1
def INVERSE_MOD_CONG : thm := BSolve.INVERSE_MOD_CONG
def INVERSE_MOD_INVERSE_MOD_CONG : thm := BSolve.INVERSE_MOD_INVERSE_MOD_CONG
def INVERSE_MOD_INVERSE_MOD : thm := BSolve.INVERSE_MOD_INVERSE_MOD
def INVERSE_MOD_NONZERO_ALT : thm := BSolve.INVERSE_MOD_NONZERO_ALT
def INVERSE_MOD_NONZERO : thm := BSolve.INVERSE_MOD_NONZERO
def INVERSE_MOD_BOUND_LE : thm := BSolve.INVERSE_MOD_BOUND_LE
def INVERSE_MOD_INVERSION : thm := BSolve.INVERSE_MOD_INVERSION
def INVERSE_MOD_CONV : term → IO (Except String thm) := fun t => (BSolve.INVERSE_MOD_CONV t).run

-- Squarefree
def squarefree : thm := BSquarefree.squarefree
def SQUAREFREE_0 : thm := BSquarefree.SQUAREFREE_0
def SQUAREFREE_1 : thm := BSquarefree.SQUAREFREE_1
def SQUAREFREE_IMP_NZ : thm := BSquarefree.SQUAREFREE_IMP_NZ
def SQUAREFREE_PRIME : thm := BSquarefree.SQUAREFREE_PRIME
def SQUAREFREE_PRIME_DIVISOR : thm := BSquarefree.SQUAREFREE_PRIME_DIVISOR
def SQUAREFREE_INDEX : thm := BSquarefree.SQUAREFREE_INDEX
def SQUAREFREE_PRIME_INDEX : thm := BSquarefree.SQUAREFREE_PRIME_INDEX
def SQUAREFREE_COPRIME : thm := BSquarefree.SQUAREFREE_COPRIME
def SQUAREFREE_COPRIME_DIVISORS : thm := BSquarefree.SQUAREFREE_COPRIME_DIVISORS
def SQUAREFREE_DIVISOR : thm := BSquarefree.SQUAREFREE_DIVISOR
def PRIME_IMP_SQUAREFREE : thm := BSquarefree.PRIME_IMP_SQUAREFREE
def SQUAREFREE_MUL : thm := BSquarefree.SQUAREFREE_MUL
def SQUAREFREE_EXP : thm := BSquarefree.SQUAREFREE_EXP
def SQUAREFREE_DIVIDES : thm := BSquarefree.SQUAREFREE_DIVIDES
def SQUAREFREE_DIVEXP : thm := BSquarefree.SQUAREFREE_DIVEXP
def SQUAREFREE_DIVEXP_EQ : thm := BSquarefree.SQUAREFREE_DIVEXP_EQ
def SQUAREFREE : thm := BSquarefree.SQUAREFREE
def SQUAREFREE_ALT : thm := BSquarefree.SQUAREFREE_ALT
def SQUAREFREE_GCD : thm := BSquarefree.SQUAREFREE_GCD
def SQUAREFREE_GCD_SQUARE : thm := BSquarefree.SQUAREFREE_GCD_SQUARE
def SQUAREFREE_NPRODUCT : thm := BSquarefree.SQUAREFREE_NPRODUCT
def SQUAREFREE_EXPAND : thm := BSquarefree.SQUAREFREE_EXPAND
def SQUAREFREE_EXPAND_EQ : thm := BSquarefree.SQUAREFREE_EXPAND_EQ
def SQUAREFREE_DECOMPOSITION : thm := BSquarefree.SQUAREFREE_DECOMPOSITION
def CONG_MOD_SQUAREFREE : thm := BSquarefree.CONG_MOD_SQUAREFREE
def CONG_MOD_SQUAREFREE_EQ : thm := BSquarefree.CONG_MOD_SQUAREFREE_EQ

-- Phi
def phi : thm := BPhi.phi
def PHI_ALT : thm := BPhi.PHI_ALT
def PHI_FINITE_LEMMA : thm := BPhi.PHI_FINITE_LEMMA
def PHI_ANOTHER : thm := BPhi.PHI_ANOTHER
def PHI_LIMIT : thm := BPhi.PHI_LIMIT
def PHI_LIMIT_STRONG : thm := BPhi.PHI_LIMIT_STRONG
def PHI_0 : thm := BPhi.PHI_0
def PHI_1 : thm := BPhi.PHI_1
def PHI_LOWERBOUND_1_STRONG : thm := BPhi.PHI_LOWERBOUND_1_STRONG
def PHI_LOWERBOUND_1 : thm := BPhi.PHI_LOWERBOUND_1
def PHI_LOWERBOUND_2 : thm := BPhi.PHI_LOWERBOUND_2
def PHI_EQ_0 : thm := BPhi.PHI_EQ_0
def PHI_PRIME_EQ : thm := BPhi.PHI_PRIME_EQ
def PHI_PRIME : thm := BPhi.PHI_PRIME
def PHI_PRIMEPOW_SUC : thm := BPhi.PHI_PRIMEPOW_SUC
def PHI_PRIMEPOW : thm := BPhi.PHI_PRIMEPOW
def PHI_PRIMEPOW_ALT : thm := BPhi.PHI_PRIMEPOW_ALT
def PHI_2 : thm := BPhi.PHI_2
def PHI_MULTIPLICATIVE : thm := BPhi.PHI_MULTIPLICATIVE
def EVEN_PHI : thm := BPhi.EVEN_PHI
def EVEN_PHI_EQ : thm := BPhi.EVEN_PHI_EQ
def ODD_PHI_EQ : thm := BPhi.ODD_PHI_EQ
def PHI_EQ_PRIME : thm := BPhi.PHI_EQ_PRIME
def PHI_LIMIT_COMPOSITE : thm := BPhi.PHI_LIMIT_COMPOSITE
def NPRODUCT_MOD : thm := BPhi.NPRODUCT_MOD
def NPRODUCT_CMUL : thm := BPhi.NPRODUCT_CMUL
def ITERATE_OVER_COPRIME : thm := BPhi.ITERATE_OVER_COPRIME
def ITERATE_ITERATE_DIVISORS : thm := BPhi.ITERATE_ITERATE_DIVISORS
def FERMAT_LITTLE : thm := BPhi.FERMAT_LITTLE
def FERMAT_LITTLE_PRIME : thm := BPhi.FERMAT_LITTLE_PRIME

-- Order
def LUCAS_COPRIME_LEMMA : thm := BOrder.LUCAS_COPRIME_LEMMA
def LUCAS_WEAK : thm := BOrder.LUCAS_WEAK
def LUCAS : thm := BOrder.LUCAS
def order : thm := BOrder.order
def EXP_ITER : thm := BOrder.EXP_ITER
def ORDER_DIVIDES : thm := BOrder.ORDER_DIVIDES
def ORDER : thm := BOrder.ORDER
def ORDER_UNIQUE_ALT : thm := BOrder.ORDER_UNIQUE_ALT
def ORDER_MINIMAL : thm := BOrder.ORDER_MINIMAL
def ORDER_WORKS : thm := BOrder.ORDER_WORKS
def ORDER_1 : thm := BOrder.ORDER_1
def ORDER_EQ_0 : thm := BOrder.ORDER_EQ_0
def ORDER_EQ_1 : thm := BOrder.ORDER_EQ_1
def ORDER_UNIQUE_PRIME : thm := BOrder.ORDER_UNIQUE_PRIME
def ORDER_CONG : thm := BOrder.ORDER_CONG
def ORDER_MOD : thm := BOrder.ORDER_MOD
def COPRIME_ORDER : thm := BOrder.COPRIME_ORDER
def ORDER_DIVIDES_PHI : thm := BOrder.ORDER_DIVIDES_PHI
def ORDER_LE_PHI : thm := BOrder.ORDER_LE_PHI
def ORDER_DIVIDES_EXPDIFF : thm := BOrder.ORDER_DIVIDES_EXPDIFF
def ORDER_UNIQUE : thm := BOrder.ORDER_UNIQUE
def ORDER_MUL_LCM : thm := BOrder.ORDER_MUL_LCM
def ORDER_EXP_GEN : thm := BOrder.ORDER_EXP_GEN
def ORDER_EXP : thm := BOrder.ORDER_EXP
def ORDER_INVERSE_MOD : thm := BOrder.ORDER_INVERSE_MOD
def ORDER_MUL_DIVIDES : thm := BOrder.ORDER_MUL_DIVIDES
def ORDER_MUL_EQ : thm := BOrder.ORDER_MUL_EQ
def ORDER_LCM_EXISTS : thm := BOrder.ORDER_LCM_EXISTS
def ORDER_DIVIDES_MAXIMAL : thm := BOrder.ORDER_DIVIDES_MAXIMAL
def POWER_RESIDUE_MODULO_COPRIME : thm := BOrder.POWER_RESIDUE_MODULO_COPRIME
def POWER_RESIDUE_MODULO_PRIME : thm := BOrder.POWER_RESIDUE_MODULO_PRIME
def INJECTIVE_EXP_MODULO : thm := BOrder.INJECTIVE_EXP_MODULO
def PRIMITIVE_ROOT_IMP_COPRIME : thm := BOrder.PRIMITIVE_ROOT_IMP_COPRIME
def PRIMITIVE_ROOT_IMP_PRIME : thm := BOrder.PRIMITIVE_ROOT_IMP_PRIME
def PRIMITIVE_ROOT_IMAGE : thm := BOrder.PRIMITIVE_ROOT_IMAGE
def PRIMITIVE_ROOT_IMAGE_PRIME : thm := BOrder.PRIMITIVE_ROOT_IMAGE_PRIME
def PRIMITIVE_ROOT_SURJECTIVE : thm := BOrder.PRIMITIVE_ROOT_SURJECTIVE
def PRIMITIVE_ROOT_SURJECTIVE_ALT : thm := BOrder.PRIMITIVE_ROOT_SURJECTIVE_ALT
def PRIMITIVE_ROOT_SURJECTIVE_PRIME : thm := BOrder.PRIMITIVE_ROOT_SURJECTIVE_PRIME
def PRIMITIVE_ROOT_SURJECTIVE_PRIME_ALT : thm := BOrder.PRIMITIVE_ROOT_SURJECTIVE_PRIME_ALT
def PRIME_DIVISOR_SQRT : thm := BOrder.PRIME_DIVISOR_SQRT
def PRIME_PRIME_FACTOR_SQRT : thm := BOrder.PRIME_PRIME_FACTOR_SQRT

-- Pock
def POCKLINGTON_LEMMA : thm := BPock.POCKLINGTON_LEMMA
def POCKLINGTON : thm := BPock.POCKLINGTON
def POCKLINGTON_ALT : thm := BPock.POCKLINGTON_ALT
def primefact : thm := BPock.primefact
def PRIMEFACT : thm := BPock.PRIMEFACT
def PRIMAFACT_CONTAINS : thm := BPock.PRIMAFACT_CONTAINS
def PRIMEFACT_VARIANT : thm := BPock.PRIMEFACT_VARIANT
def LUCAS_PRIMEFACT : thm := BPock.LUCAS_PRIMEFACT
def POCKLINGTON_PRIMEFACT : thm := BPock.POCKLINGTON_PRIMEFACT

-- Certify
def prime_theorem_cache := BCertify.prime_theorem_cache
def check_certificate := BCertify.check_certificate
def PROVE_PRIME := BCertify.PROVE_PRIME
def PROVE_PRIMEFACT := BCertify.PROVE_PRIMEFACT
def PRIME_TEST : term → IO (Except String thm) := fun t => (BCertify.PRIME_TEST t).run
def PRIME_CONV : term → IO (Except String thm) := fun t => (BCertify.PRIME_CONV t).run
def GUIDED_PROVE_PRIME := BCertify.GUIDED_PROVE_PRIME
def PRIME_RULE := BCertify.PRIME_RULE










/- pocklington.ml's names that HolLibrary.Pocklington defines at top level
   (they need no bundle). -/
export HolLibrary.Pocklington (num_0 num_1 num_2 even_num odd_num log2 powermod factor
  PARI_THRESHOLD multifactor certificate find_primitive_root uniq_num setify_num
  certify_prime lookup_under_num split_factors extract_primes_from_certificate
  guided_certify_prime)

/-- `needs "Library/pocklington.ml"`: already done by importing this module. -/
def ensurePocklington : IO Unit := pure ()

end SessionLibrary.Pocklington
