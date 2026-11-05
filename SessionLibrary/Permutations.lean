/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/permutations.ml.                      -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Permutations.lean

  The session half of the permutations.ml translation: it supplies
  HolLibrary.Permutations's dependencies from Session and exports every name
  under its HOL Light name.  Importing this module is
  `needs "Library/permutations.ml"` (permutations.ml has no `needs`): the
  bundles are built by `initialize` when the module is loaded, in file
  order.
-/

import Session
import HolLibrary.Permutations

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Permutations

/-- The core theorems permutations.ml uses. -/
def core1 : HolLibrary.Permutations.CoreThms1 where
  ADD1 := Session.ADD1
  ADD_CLAUSES := Session.ADD_CLAUSES
  ARITH := Session.ARITH
  ARITH_EQ := Session.ARITH_EQ
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARD_DELETE := Session.CARD_DELETE
  CARD_EQ_0 := Session.CARD_EQ_0
  CARD_IMAGE_INJ := Session.CARD_IMAGE_INJ
  CARD_SUBSET := Session.CARD_SUBSET
  CARD_UNION := Session.CARD_UNION
  CHOOSE_SUBSET_STRONG := Session.CHOOSE_SUBSET_STRONG
  COND_ID := Session.COND_ID
  COND_RAND := Session.COND_RAND
  COND_RATOR := Session.COND_RATOR
  CONJ_ASSOC := Session.CONJ_ASSOC
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DIV_0 := Session.DIV_0
  EMPTY_GSPEC := Session.EMPTY_GSPEC
  EQ_SYM := Session.EQ_SYM
  EVEN := Session.EVEN
  EVEN_ADD := Session.EVEN_ADD
  EVEN_MULT := Session.EVEN_MULT
  EVEN_SUB := Session.EVEN_SUB
  EXISTS_PAIR_THM := Session.EXISTS_PAIR_THM
  EXISTS_UNIQUE := Session.EXISTS_UNIQUE
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXTENSION := Session.EXTENSION
  FACT := Session.FACT
  FINITE_CROSS_EQ := Session.FINITE_CROSS_EQ
  FINITE_DELETE := Session.FINITE_DELETE
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_NUMSEG := Session.FINITE_NUMSEG
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_RESTRICT := Session.FINITE_RESTRICT
  FINITE_RULES := Session.FINITE_RULES
  FINITE_SING := Session.FINITE_SING
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  FORALL_UNWIND_THM2 := Session.FORALL_UNWIND_THM2
  FUN_EQ_THM := Session.FUN_EQ_THM
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_IMAGE_INJ := Session.HAS_SIZE_IMAGE_INJ
  HAS_SIZE_PRODUCT := Session.HAS_SIZE_PRODUCT
  IMAGE_CLAUSES := Session.IMAGE_CLAUSES
  IMP_CONJ := Session.IMP_CONJ
  IMP_CONJ_ALT := Session.IMP_CONJ_ALT
  IMP_IMP := Session.IMP_IMP
  INJECTIVE_ON_LEFT_INVERSE := Session.INJECTIVE_ON_LEFT_INVERSE
  INSERT_AC := Session.INSERT_AC
  IN_CROSS := Session.IN_CROSS
  IN_DELETE := Session.IN_DELETE
  IN_DIFF := Session.IN_DIFF
  IN_ELIM_PAIR_THM := Session.IN_ELIM_PAIR_THM
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_NUMSEG := Session.IN_NUMSEG
  IN_SING := Session.IN_SING
  IN_UNIV := Session.IN_UNIV
  ITERATE_BIJECTION := Session.ITERATE_BIJECTION
  I_DEF := Session.I_DEF
  I_O_ID := Session.I_O_ID
  I_THM := Session.I_THM
  LAMBDA_PAIR_THM := Session.LAMBDA_PAIR_THM
  LEFT_AND_EXISTS_THM := Session.LEFT_AND_EXISTS_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_ANTISYM := Session.LE_ANTISYM
  LE_REFL := Session.LE_REFL
/-- The core theorems permutations.ml uses. -/
def core2 : HolLibrary.Permutations.CoreThms2 where
  LE_TRANS := Session.LE_TRANS
  LT := Session.LT
  LT_REFL := Session.LT_REFL
  MOD_ADD_MOD := Session.MOD_ADD_MOD
  MOD_CASES := Session.MOD_CASES
  MOD_LT := Session.MOD_LT
  MOD_LT_EQ := Session.MOD_LT_EQ
  MOD_MOD_REFL := Session.MOD_MOD_REFL
  MONOIDAL_ADD := Session.MONOIDAL_ADD
  MONOIDAL_REAL_ADD := Session.MONOIDAL_REAL_ADD
  MONO_EXISTS := Session.MONO_EXISTS
  NOT_EVEN := Session.NOT_EVEN
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NOT_LT := Session.NOT_LT
  NOT_SUC := Session.NOT_SUC
  NUMSEG_LREC := Session.NUMSEG_LREC
  ODD := Session.ODD
  PAIR_EQ := Session.PAIR_EQ
  REAL_POW_NEG := Session.REAL_POW_NEG
  REAL_POW_ONE := Session.REAL_POW_ONE
  REAL_SGN_EQ := Session.REAL_SGN_EQ
  RIGHT_AND_EXISTS_THM := Session.RIGHT_AND_EXISTS_THM
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  SELECT_UNIQUE := Session.SELECT_UNIQUE
  SUBSET := Session.SUBSET
  SUC_INJ := Session.SUC_INJ
  SUC_SUB1 := Session.SUC_SUB1
  SUM_IMAGE := Session.SUM_IMAGE
  SUM_SUM_PRODUCT := Session.SUM_SUM_PRODUCT
  SURJECTIVE_IFF_INJECTIVE := Session.SURJECTIVE_IFF_INJECTIVE
  SURJECTIVE_RIGHT_INVERSE := Session.SURJECTIVE_RIGHT_INVERSE
  SWAP_FORALL_THM := Session.SWAP_FORALL_THM
  nsum := Session.nsum
  num_WF := Session.num_WF
  o_ASSOC := Session.o_ASSOC
  o_DEF := Session.o_DEF
  o_THM := Session.o_THM
  real_pow := Session.real_pow
  sum := Session.sum
/-- The core theorems permutations.ml uses. -/
def core3 : HolLibrary.Permutations.CoreThms3 where
/-- The core theorems permutations.ml uses. -/
def core4 : HolLibrary.Permutations.CoreThms4 where

/-- What permutations.ml uses from Session. -/
def deps : HolLibrary.Permutations.PermutationsDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  parse_as_infix := Session.parse_as_infix
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  METIS_TAC := Session.METIS_TAC
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  REAL_ARITH_TAC := Session.REAL_ARITH_TAC2
  INDUCT_TAC := Session.INDUCT_TAC
  GEN_BETA_CONV := Session.GEN_BETA_CONV
  HAS_SIZE_CONV := Session.HAS_SIZE_CONV
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  new_inductive_definition s := do
    ExceptT.mk (Session.new_inductive_definition (← HolLight.q s))
  num_CONV := Session.num_CONV
  NUM_RED_CONV := Session.NUM_RED_CONV
  REAL_RAT_REDUCE_CONV := Session.REAL_RAT_REDUCE_CONV
  WF_INDUCT_TAC := Session.WF_INDUCT_TAC
  REAL_RING t := ExceptT.mk (Session.REAL_RING t)
  core1 := core1
  core2 := core2
  core3 := core3
  core4 := core4

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in permutations.ml order. -/
initialize BPermutes : HolLibrary.Permutations.Permutes ←
  ioB "setupPermutes" (HolLibrary.Permutations.setupPermutes deps).run
initialize BBasicCons : HolLibrary.Permutations.BasicCons ←
  ioB "setupBasicCons" (HolLibrary.Permutations.setupBasicCons deps BPermutes).run
initialize BGroups : HolLibrary.Permutations.Groups ←
  ioB "setupGroups" (HolLibrary.Permutations.setupGroups deps BPermutes BBasicCons).run
initialize BNumPerms : HolLibrary.Permutations.NumPerms ←
  ioB "setupNumPerms"
    (HolLibrary.Permutations.setupNumPerms deps BPermutes BBasicCons BGroups).run
initialize BAltChar : HolLibrary.Permutations.AltChar ←
  ioB "setupAltChar" (HolLibrary.Permutations.setupAltChar deps BPermutes).run
initialize BRestrict : HolLibrary.Permutations.Restrict ←
  ioB "setupRestrict"
    (HolLibrary.Permutations.setupRestrict deps BPermutes BBasicCons BAltChar).run
initialize BIterSwap : HolLibrary.Permutations.IterSwap ←
  ioB "setupIterSwap" (HolLibrary.Permutations.setupIterSwap deps BPermutes).run
initialize BThreeCycle : HolLibrary.Permutations.ThreeCycle ←
  ioB "setupThreeCycle" (HolLibrary.Permutations.setupThreeCycle deps BPermutes).run
initialize BSwapseq : HolLibrary.Permutations.Swapseq ←
  ioB "setupSwapseq" (HolLibrary.Permutations.setupSwapseq deps BPermutes BIterSwap).run
initialize BEvenperm : HolLibrary.Permutations.Evenperm ←
  ioB "setupEvenperm" (HolLibrary.Permutations.setupEvenperm deps BPermutes BSwapseq).run
initialize BSign : HolLibrary.Permutations.Sign ←
  ioB "setupSign" (HolLibrary.Permutations.setupSign deps BPermutes BBasicCons BGroups
    BNumPerms BSwapseq BEvenperm).run
initialize BSignTransfer : HolLibrary.Permutations.SignTransfer ←
  ioB "setupSignTransfer" (HolLibrary.Permutations.setupSignTransfer deps BPermutes
    BBasicCons BGroups BNumPerms BSwapseq BEvenperm BSign).run
initialize BInvolution : HolLibrary.Permutations.Involution ←
  ioB "setupInvolution" (HolLibrary.Permutations.setupInvolution deps BPermutes
    BBasicCons BGroups BAltChar BSwapseq BEvenperm BSign).run
initialize BPermset : HolLibrary.Permutations.Permset ←
  ioB "setupPermset"
    (HolLibrary.Permutations.setupPermset deps BPermutes BBasicCons BNumPerms).run
initialize BSumOver : HolLibrary.Permutations.SumOver ←
  ioB "setupSumOver" (HolLibrary.Permutations.setupSumOver deps BPermutes BNumPerms).run

-- Permutes
def permutes : thm := BPermutes.permutes
def inverse : thm := BPermutes.inverse
def SURJECTIVE_INVERSE : thm := BPermutes.SURJECTIVE_INVERSE
def SURJECTIVE_INVERSE_o : thm := BPermutes.SURJECTIVE_INVERSE_o
def INJECTIVE_INVERSE : thm := BPermutes.INJECTIVE_INVERSE
def INJECTIVE_INVERSE_o : thm := BPermutes.INJECTIVE_INVERSE_o
def INVERSE_UNIQUE_o : thm := BPermutes.INVERSE_UNIQUE_o
def INVERSE_I : thm := BPermutes.INVERSE_I
def INVERSE_UNIQUE_ALT : thm := BPermutes.INVERSE_UNIQUE_ALT
def swap : thm := BPermutes.swap
def SWAP_REFL : thm := BPermutes.SWAP_REFL
def SWAP_SYM : thm := BPermutes.SWAP_SYM
def SWAP_IDEMPOTENT : thm := BPermutes.SWAP_IDEMPOTENT
def INVERSE_SWAP : thm := BPermutes.INVERSE_SWAP
def SWAP_GALOIS : thm := BPermutes.SWAP_GALOIS
def SWAP_LEFT : thm := BPermutes.SWAP_LEFT
def SWAP_RIGHT : thm := BPermutes.SWAP_RIGHT
def SWAP_OTHER : thm := BPermutes.SWAP_OTHER
def SWAP_TRIPLE : thm := BPermutes.SWAP_TRIPLE
def SWAP_TRIPLE_ALT : thm := BPermutes.SWAP_TRIPLE_ALT
def INVOLUTION_SIZE_2_IS_SWAP : thm := BPermutes.INVOLUTION_SIZE_2_IS_SWAP
def INVOLUTION_MOVES_2_IS_SWAP : thm := BPermutes.INVOLUTION_MOVES_2_IS_SWAP

-- BasicCons
def PERMUTES_IN_IMAGE : thm := BBasicCons.PERMUTES_IN_IMAGE
def PERMUTES_IMAGE : thm := BBasicCons.PERMUTES_IMAGE
def PERMUTES_INJECTIVE : thm := BBasicCons.PERMUTES_INJECTIVE
def PERMUTES_SURJECTIVE : thm := BBasicCons.PERMUTES_SURJECTIVE
def PERMUTES_EQ : thm := BBasicCons.PERMUTES_EQ
def PERMUTES_INVERSES_o : thm := BBasicCons.PERMUTES_INVERSES_o
def PERMUTES_INVERSES : thm := BBasicCons.PERMUTES_INVERSES
def PERMUTES_SUBSET : thm := BBasicCons.PERMUTES_SUBSET
def PERMUTES_EMPTY : thm := BBasicCons.PERMUTES_EMPTY
def PERMUTES_SING : thm := BBasicCons.PERMUTES_SING
def PERMUTES_UNIV : thm := BBasicCons.PERMUTES_UNIV
def PERMUTES_INVERSE_EQ : thm := BBasicCons.PERMUTES_INVERSE_EQ
def PERMUTES_SWAP : thm := BBasicCons.PERMUTES_SWAP
def PERMUTES_SUPERSET : thm := BBasicCons.PERMUTES_SUPERSET
def PERMUTES_BIJECTIONS : thm := BBasicCons.PERMUTES_BIJECTIONS
def PERMUTES_INVERSE_FUNCTION : thm := BBasicCons.PERMUTES_INVERSE_FUNCTION
def PERMUTES_ALT : thm := BBasicCons.PERMUTES_ALT
def PERMUTES : thm := BBasicCons.PERMUTES
def PERMUTES_RESTRICT_SET : thm := BBasicCons.PERMUTES_RESTRICT_SET
def PERMUTES_RESTRICT : thm := BBasicCons.PERMUTES_RESTRICT
def PERMUTES_CARTESIAN_PRODUCT : thm := BBasicCons.PERMUTES_CARTESIAN_PRODUCT
def PERMUTES_TRANSFER_BIJECTIONS : thm := BBasicCons.PERMUTES_TRANSFER_BIJECTIONS
def PERMUTES_TRANSFER : thm := BBasicCons.PERMUTES_TRANSFER

-- Groups
def SWAP_CONJUGATE : thm := BGroups.SWAP_CONJUGATE
def PERMUTES_ID : thm := BGroups.PERMUTES_ID
def PERMUTES_I : thm := BGroups.PERMUTES_I
def PERMUTES_DOUBLETON : thm := BGroups.PERMUTES_DOUBLETON
def PERMUTES_COMPOSE : thm := BGroups.PERMUTES_COMPOSE
def PERMUTES_INVERSE : thm := BGroups.PERMUTES_INVERSE
def PERMUTES_INVERSE_INVERSE : thm := BGroups.PERMUTES_INVERSE_INVERSE

-- NumPerms
def PERMUTES_INSERT_LEMMA : thm := BNumPerms.PERMUTES_INSERT_LEMMA
def PERMUTES_INSERT : thm := BNumPerms.PERMUTES_INSERT
def HAS_SIZE_PERMUTATIONS : thm := BNumPerms.HAS_SIZE_PERMUTATIONS
def FINITE_PERMUTATIONS : thm := BNumPerms.FINITE_PERMUTATIONS
def CARD_PERMUTATIONS : thm := BNumPerms.CARD_PERMUTATIONS

-- AltChar
def PERMUTES_FINITE_INJECTIVE : thm := BAltChar.PERMUTES_FINITE_INJECTIVE
def PERMUTES_FINITE_SURJECTIVE : thm := BAltChar.PERMUTES_FINITE_SURJECTIVE

-- Restrict
def RESTRICT_PERMUTES_EQ : thm := BRestrict.RESTRICT_PERMUTES_EQ
def RESTRICT_PERMUTES_SUBSET : thm := BRestrict.RESTRICT_PERMUTES_SUBSET
def RESTRICT_I : thm := BRestrict.RESTRICT_I
def RESTRICT_COMPOSE : thm := BRestrict.RESTRICT_COMPOSE
def RESTRICT_INVERSE : thm := BRestrict.RESTRICT_INVERSE
def RESTRICT_SWAP : thm := BRestrict.RESTRICT_SWAP

-- IterSwap
def ITERATE_PERMUTE : thm := BIterSwap.ITERATE_PERMUTE
def NSUM_PERMUTE : thm := BIterSwap.NSUM_PERMUTE
def NSUM_PERMUTE_NUMSEG : thm := BIterSwap.NSUM_PERMUTE_NUMSEG
def SUM_PERMUTE : thm := BIterSwap.SUM_PERMUTE
def SUM_PERMUTE_NUMSEG : thm := BIterSwap.SUM_PERMUTE_NUMSEG
def SWAP_COMMON : thm := BIterSwap.SWAP_COMMON
def SWAP_COMMON' : thm := BIterSwap.SWAP_COMMON'
def SWAP_INDEPENDENT : thm := BIterSwap.SWAP_INDEPENDENT

-- ThreeCycle
def three_cycle : thm := BThreeCycle.three_cycle
def PERMUTES_THREE_CYCLE : thm := BThreeCycle.PERMUTES_THREE_CYCLE
def THREE_CYCLE_COMPOSE_REVERSE : thm := BThreeCycle.THREE_CYCLE_COMPOSE_REVERSE
def THREE_CYCLE_INVERSE : thm := BThreeCycle.THREE_CYCLE_INVERSE
def THREE_CYCLE_AS_COMMUTATOR : thm := BThreeCycle.THREE_CYCLE_AS_COMMUTATOR
def THREE_CYCLE_COMMUTATOR : thm := BThreeCycle.THREE_CYCLE_COMMUTATOR
def THREE_CYCLE_NOT_I : thm := BThreeCycle.THREE_CYCLE_NOT_I

-- Swapseq
def swapseq_RULES : thm := BSwapseq.swapseq_RULES
def swapseq_INDUCT : thm := BSwapseq.swapseq_INDUCT
def swapseq_CASES : thm := BSwapseq.swapseq_CASES
def permutation : thm := BSwapseq.permutation
def SWAPSEQ_I : thm := BSwapseq.SWAPSEQ_I
def PERMUTATION_I : thm := BSwapseq.PERMUTATION_I
def SWAPSEQ_SWAP : thm := BSwapseq.SWAPSEQ_SWAP
def PERMUTATION_SWAP : thm := BSwapseq.PERMUTATION_SWAP
def SWAPSEQ_COMPOSE : thm := BSwapseq.SWAPSEQ_COMPOSE
def PERMUTATION_COMPOSE : thm := BSwapseq.PERMUTATION_COMPOSE
def SWAPSEQ_ENDSWAP : thm := BSwapseq.SWAPSEQ_ENDSWAP
def SWAPSEQ_INVERSE_EXISTS : thm := BSwapseq.SWAPSEQ_INVERSE_EXISTS
def SWAPSEQ_INVERSE : thm := BSwapseq.SWAPSEQ_INVERSE
def PERMUTATION_INVERSE : thm := BSwapseq.PERMUTATION_INVERSE
def SYMMETRY_LEMMA : thm := BSwapseq.SYMMETRY_LEMMA
def SWAP_GENERAL : thm := BSwapseq.SWAP_GENERAL
def FIXING_SWAPSEQ_DECREASE : thm := BSwapseq.FIXING_SWAPSEQ_DECREASE
def SWAPSEQ_IDENTITY_EVEN : thm := BSwapseq.SWAPSEQ_IDENTITY_EVEN

-- Evenperm
def evenperm : thm := BEvenperm.evenperm
def SWAPSEQ_EVEN_EVEN : thm := BEvenperm.SWAPSEQ_EVEN_EVEN
def EVENPERM_UNIQUE : thm := BEvenperm.EVENPERM_UNIQUE
def EVENPERM_I : thm := BEvenperm.EVENPERM_I
def EVENPERM_ID : thm := BEvenperm.EVENPERM_ID
def EVENPERM_SWAP : thm := BEvenperm.EVENPERM_SWAP
def EVENPERM_COMPOSE : thm := BEvenperm.EVENPERM_COMPOSE
def EVENPERM_INVERSE : thm := BEvenperm.EVENPERM_INVERSE
def PERMUTATION_BIJECTIVE : thm := BEvenperm.PERMUTATION_BIJECTIVE
def PERMUTATION_FINITE_SUPPORT : thm := BEvenperm.PERMUTATION_FINITE_SUPPORT
def PERMUTATION_LEMMA : thm := BEvenperm.PERMUTATION_LEMMA
def PERMUTATION : thm := BEvenperm.PERMUTATION
def PERMUTATION_INVERSE_WORKS : thm := BEvenperm.PERMUTATION_INVERSE_WORKS
def PERMUTATION_INVERSE_COMPOSE : thm := BEvenperm.PERMUTATION_INVERSE_COMPOSE
def PERMUTATION_COMPOSE_EQ : thm := BEvenperm.PERMUTATION_COMPOSE_EQ
def PERMUTATION_COMPOSE_SWAP : thm := BEvenperm.PERMUTATION_COMPOSE_SWAP

-- Sign
def PERMUTATION_PERMUTES : thm := BSign.PERMUTATION_PERMUTES
def PERMUTATION_RESTRICT : thm := BSign.PERMUTATION_RESTRICT
def PERMUTES_INDUCT : thm := BSign.PERMUTES_INDUCT
def PERMUTES_INDUCT_STRONG : thm := BSign.PERMUTES_INDUCT_STRONG
def sign : thm := BSign.sign
def SIGN_NZ : thm := BSign.SIGN_NZ
def SIGN_I : thm := BSign.SIGN_I
def SIGN_ID : thm := BSign.SIGN_ID
def SIGN_INVERSE : thm := BSign.SIGN_INVERSE
def SIGN_COMPOSE : thm := BSign.SIGN_COMPOSE
def SIGN_SWAP : thm := BSign.SIGN_SWAP
def SIGN_IDEMPOTENT : thm := BSign.SIGN_IDEMPOTENT
def REAL_ABS_SIGN_PERMUTATION : thm := BSign.REAL_ABS_SIGN_PERMUTATION
def REAL_SGN_SIGN : thm := BSign.REAL_SGN_SIGN
def EVENPERM_TRANSFER : thm := BSign.EVENPERM_TRANSFER

-- SignTransfer
def SIGN_TRANSFER : thm := BSignTransfer.SIGN_TRANSFER
def SIGN_CARTESIAN_PRODUCT : thm := BSignTransfer.SIGN_CARTESIAN_PRODUCT
def PERMUTES_NUMSET_LE : thm := BSignTransfer.PERMUTES_NUMSET_LE
def PERMUTES_NUMSET_GE : thm := BSignTransfer.PERMUTES_NUMSET_GE
def IMAGE_INVERSE_PERMUTATIONS : thm := BSignTransfer.IMAGE_INVERSE_PERMUTATIONS
def IMAGE_COMPOSE_PERMUTATIONS_L : thm := BSignTransfer.IMAGE_COMPOSE_PERMUTATIONS_L
def IMAGE_COMPOSE_PERMUTATIONS_R : thm := BSignTransfer.IMAGE_COMPOSE_PERMUTATIONS_R
def PERMUTES_IN_NUMSEG : thm := BSignTransfer.PERMUTES_IN_NUMSEG
def SUM_PERMUTATIONS_INVERSE : thm := BSignTransfer.SUM_PERMUTATIONS_INVERSE
def SUM_PERMUTATIONS_COMPOSE_L : thm := BSignTransfer.SUM_PERMUTATIONS_COMPOSE_L
def SUM_PERMUTATIONS_COMPOSE_R : thm := BSignTransfer.SUM_PERMUTATIONS_COMPOSE_R
def CARD_EVEN_PERMUTATIONS : thm := BSignTransfer.CARD_EVEN_PERMUTATIONS

-- Involution
def PERMUTES_INVOLUTION : thm := BInvolution.PERMUTES_INVOLUTION
def SIGN_INVOLUTION : thm := BInvolution.SIGN_INVOLUTION
def PERMUTES_CYCLIC : thm := BInvolution.PERMUTES_CYCLIC
def PERMUTES_CYCLIC_N : thm := BInvolution.PERMUTES_CYCLIC_N
def PERMUTATION_CYCLIC : thm := BInvolution.PERMUTATION_CYCLIC
def PERMUTATION_CYCLIC_N : thm := BInvolution.PERMUTATION_CYCLIC_N
def EVENPERM_CYCLIC : thm := BInvolution.EVENPERM_CYCLIC
def EVENPERM_CYCLIC_N : thm := BInvolution.EVENPERM_CYCLIC_N
def SIGN_CYCLIC : thm := BInvolution.SIGN_CYCLIC
def SIGN_CYCLIC_N : thm := BInvolution.SIGN_CYCLIC_N

-- Permset
def PERMSET_CONV : term → IO (Except String thm) := fun t => (BPermset.PERMSET_CONV t).run

-- SumOver
def SUM_OVER_PERMUTATIONS_INSERT : thm := BSumOver.SUM_OVER_PERMUTATIONS_INSERT
def SUM_OVER_PERMUTATIONS_NUMSEG : thm := BSumOver.SUM_OVER_PERMUTATIONS_NUMSEG
/-- `needs "Library/permutations.ml"`: already done by importing this module. -/
def ensurePermutations : IO Unit := pure ()

end SessionLibrary.Permutations
