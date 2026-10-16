/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/permutations.ml.                      -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Permutations.lean

  The `unsafe` half of the permutations.ml translation: it supplies HolLibrary.Permutations's
  dependencies from Session, builds the bundles once, in order,
  and exports every name under its HOL Light name.  `ensurePermutations` is
  `needs "Library/permutations.ml"` (which first does nothing (no `needs`)).

  The blocks between `@@CORE` and `@@EXPORTS` markers are generated from
  HolLibrary/Permutations.lean by tools/permutationsdiff/gen_session.py and scope.py
  (bookkeeping only: field-by-field copies and accessors).
-/

import Session
import HolLibrary.Permutations

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Permutations

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨Session.sessionB, Session.sessionC, Session.sessionT⟩

-- @@CORE BEGIN
/-- The core theorems permutations.ml uses. -/
unsafe def core1 (_ : Unit) : HolLibrary.Permutations.CoreThms1 where
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
unsafe def core2 (_ : Unit) : HolLibrary.Permutations.CoreThms2 where
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
unsafe def core3 (_ : Unit) : HolLibrary.Permutations.CoreThms3 where
/-- The core theorems permutations.ml uses. -/
unsafe def core4 (_ : Unit) : HolLibrary.Permutations.CoreThms4 where
-- @@CORE END

/-- What permutations.ml uses from Session. -/
unsafe def deps (_ : Unit) : HolLibrary.Permutations.PermutationsDeps where
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
  core1 := core1 ()
  core2 := core2 ()
  core3 := core3 ()
  core4 := core4 ()

/-- Build a bundle once.  `setup` is a thunk, so that `deps` is not built
    before the bundle is needed.  The whole core library is built first
    (`Session.ensureDefine`, and MATCH_CONV's basic conversions, which HOL
    Light adds loading ind_types.ml). -/
private unsafe def cached {α : Type} [Inhabited α] (r : IO.Ref (Option α)) (name : String)
    (setup : Unit → IO (Except String α)) : α :=
  match unsafeIO (do
    match ← r.get with
    | some d => pure d
    | none => do
      Session.ensureDefine
      let _ ← Session.MATCH_CONV (HolCore.Kernel.mk_var "p" HolCore.Kernel.bool_ty)
      match ← setup () with
      | .ok d => do r.set (some d); pure d
      | .error e => panic! s!"{name} failed: {e}") with
  | .ok d => d | _ => panic! s!"SessionLibrary.Permutations: {name}"

/- The bundles, in file order; each forces the one before it. -/

-- @@BUNDLES BEGIN
initialize thePermutes : IO.Ref (Option HolLibrary.Permutations.Permutes) ← IO.mkRef none
unsafe def BPermutes : HolLibrary.Permutations.Permutes :=
  cached thePermutes "setupPermutes" fun _ => do
    (HolLibrary.Permutations.setupPermutes (deps ())).run

initialize theBasicCons : IO.Ref (Option HolLibrary.Permutations.BasicCons) ← IO.mkRef none
unsafe def BBasicCons : HolLibrary.Permutations.BasicCons :=
  cached theBasicCons "setupBasicCons" fun _ => do
    let _ ← IO.mkRef BPermutes.permutes
    (HolLibrary.Permutations.setupBasicCons (deps ()) BPermutes).run

initialize theGroups : IO.Ref (Option HolLibrary.Permutations.Groups) ← IO.mkRef none
unsafe def BGroups : HolLibrary.Permutations.Groups :=
  cached theGroups "setupGroups" fun _ => do
    let _ ← IO.mkRef BBasicCons.PERMUTES_IN_IMAGE
    (HolLibrary.Permutations.setupGroups (deps ()) BPermutes BBasicCons).run

initialize theNumPerms : IO.Ref (Option HolLibrary.Permutations.NumPerms) ← IO.mkRef none
unsafe def BNumPerms : HolLibrary.Permutations.NumPerms :=
  cached theNumPerms "setupNumPerms" fun _ => do
    let _ ← IO.mkRef BGroups.SWAP_CONJUGATE
    (HolLibrary.Permutations.setupNumPerms (deps ()) BPermutes BBasicCons BGroups).run

initialize theAltChar : IO.Ref (Option HolLibrary.Permutations.AltChar) ← IO.mkRef none
unsafe def BAltChar : HolLibrary.Permutations.AltChar :=
  cached theAltChar "setupAltChar" fun _ => do
    let _ ← IO.mkRef BNumPerms.PERMUTES_INSERT_LEMMA
    (HolLibrary.Permutations.setupAltChar (deps ()) BPermutes).run

initialize theRestrict : IO.Ref (Option HolLibrary.Permutations.Restrict) ← IO.mkRef none
unsafe def BRestrict : HolLibrary.Permutations.Restrict :=
  cached theRestrict "setupRestrict" fun _ => do
    let _ ← IO.mkRef BAltChar.PERMUTES_FINITE_INJECTIVE
    (HolLibrary.Permutations.setupRestrict (deps ()) BPermutes BBasicCons BAltChar).run

initialize theIterSwap : IO.Ref (Option HolLibrary.Permutations.IterSwap) ← IO.mkRef none
unsafe def BIterSwap : HolLibrary.Permutations.IterSwap :=
  cached theIterSwap "setupIterSwap" fun _ => do
    let _ ← IO.mkRef BRestrict.RESTRICT_PERMUTES_SUBSET
    (HolLibrary.Permutations.setupIterSwap (deps ()) BPermutes).run

initialize theThreeCycle : IO.Ref (Option HolLibrary.Permutations.ThreeCycle) ← IO.mkRef none
unsafe def BThreeCycle : HolLibrary.Permutations.ThreeCycle :=
  cached theThreeCycle "setupThreeCycle" fun _ => do
    let _ ← IO.mkRef BIterSwap.ITERATE_PERMUTE
    (HolLibrary.Permutations.setupThreeCycle (deps ()) BPermutes).run

initialize theSwapseq : IO.Ref (Option HolLibrary.Permutations.Swapseq) ← IO.mkRef none
unsafe def BSwapseq : HolLibrary.Permutations.Swapseq :=
  cached theSwapseq "setupSwapseq" fun _ => do
    let _ ← IO.mkRef BThreeCycle.three_cycle
    (HolLibrary.Permutations.setupSwapseq (deps ()) BPermutes BIterSwap).run

initialize theEvenperm : IO.Ref (Option HolLibrary.Permutations.Evenperm) ← IO.mkRef none
unsafe def BEvenperm : HolLibrary.Permutations.Evenperm :=
  cached theEvenperm "setupEvenperm" fun _ => do
    let _ ← IO.mkRef BSwapseq.swapseq_RULES
    (HolLibrary.Permutations.setupEvenperm (deps ()) BPermutes BSwapseq).run

initialize theSign : IO.Ref (Option HolLibrary.Permutations.Sign) ← IO.mkRef none
unsafe def BSign : HolLibrary.Permutations.Sign :=
  cached theSign "setupSign" fun _ => do
    let _ ← IO.mkRef BEvenperm.evenperm
    (HolLibrary.Permutations.setupSign (deps ()) BPermutes BBasicCons BGroups BNumPerms BSwapseq BEvenperm).run

initialize theSignTransfer : IO.Ref (Option HolLibrary.Permutations.SignTransfer) ← IO.mkRef none
unsafe def BSignTransfer : HolLibrary.Permutations.SignTransfer :=
  cached theSignTransfer "setupSignTransfer" fun _ => do
    let _ ← IO.mkRef BSign.PERMUTATION_PERMUTES
    (HolLibrary.Permutations.setupSignTransfer (deps ()) BPermutes BBasicCons BGroups BNumPerms BSwapseq BEvenperm BSign).run

initialize theInvolution : IO.Ref (Option HolLibrary.Permutations.Involution) ← IO.mkRef none
unsafe def BInvolution : HolLibrary.Permutations.Involution :=
  cached theInvolution "setupInvolution" fun _ => do
    let _ ← IO.mkRef BSignTransfer.SIGN_TRANSFER
    (HolLibrary.Permutations.setupInvolution (deps ()) BPermutes BBasicCons BGroups BAltChar BSwapseq BEvenperm BSign).run

initialize thePermset : IO.Ref (Option HolLibrary.Permutations.Permset) ← IO.mkRef none
unsafe def BPermset : HolLibrary.Permutations.Permset :=
  cached thePermset "setupPermset" fun _ => do
    let _ ← IO.mkRef BInvolution.PERMUTES_INVOLUTION
    (HolLibrary.Permutations.setupPermset (deps ()) BPermutes BBasicCons BNumPerms).run

initialize theSumOver : IO.Ref (Option HolLibrary.Permutations.SumOver) ← IO.mkRef none
unsafe def BSumOver : HolLibrary.Permutations.SumOver :=
  cached theSumOver "setupSumOver" fun _ => do
    let _ ← IO.mkRef BPermset.PERMSET_CONV
    (HolLibrary.Permutations.setupSumOver (deps ()) BPermutes BNumPerms).run

-- @@BUNDLES END

-- @@EXPORTS BEGIN
-- Permutes
unsafe def permutes : thm := BPermutes.permutes
unsafe def inverse : thm := BPermutes.inverse
unsafe def SURJECTIVE_INVERSE : thm := BPermutes.SURJECTIVE_INVERSE
unsafe def SURJECTIVE_INVERSE_o : thm := BPermutes.SURJECTIVE_INVERSE_o
unsafe def INJECTIVE_INVERSE : thm := BPermutes.INJECTIVE_INVERSE
unsafe def INJECTIVE_INVERSE_o : thm := BPermutes.INJECTIVE_INVERSE_o
unsafe def INVERSE_UNIQUE_o : thm := BPermutes.INVERSE_UNIQUE_o
unsafe def INVERSE_I : thm := BPermutes.INVERSE_I
unsafe def INVERSE_UNIQUE_ALT : thm := BPermutes.INVERSE_UNIQUE_ALT
unsafe def swap : thm := BPermutes.swap
unsafe def SWAP_REFL : thm := BPermutes.SWAP_REFL
unsafe def SWAP_SYM : thm := BPermutes.SWAP_SYM
unsafe def SWAP_IDEMPOTENT : thm := BPermutes.SWAP_IDEMPOTENT
unsafe def INVERSE_SWAP : thm := BPermutes.INVERSE_SWAP
unsafe def SWAP_GALOIS : thm := BPermutes.SWAP_GALOIS
unsafe def SWAP_LEFT : thm := BPermutes.SWAP_LEFT
unsafe def SWAP_RIGHT : thm := BPermutes.SWAP_RIGHT
unsafe def SWAP_OTHER : thm := BPermutes.SWAP_OTHER
unsafe def SWAP_TRIPLE : thm := BPermutes.SWAP_TRIPLE
unsafe def SWAP_TRIPLE_ALT : thm := BPermutes.SWAP_TRIPLE_ALT
unsafe def INVOLUTION_SIZE_2_IS_SWAP : thm := BPermutes.INVOLUTION_SIZE_2_IS_SWAP
unsafe def INVOLUTION_MOVES_2_IS_SWAP : thm := BPermutes.INVOLUTION_MOVES_2_IS_SWAP

-- BasicCons
unsafe def PERMUTES_IN_IMAGE : thm := BBasicCons.PERMUTES_IN_IMAGE
unsafe def PERMUTES_IMAGE : thm := BBasicCons.PERMUTES_IMAGE
unsafe def PERMUTES_INJECTIVE : thm := BBasicCons.PERMUTES_INJECTIVE
unsafe def PERMUTES_SURJECTIVE : thm := BBasicCons.PERMUTES_SURJECTIVE
unsafe def PERMUTES_INVERSES_o : thm := BBasicCons.PERMUTES_INVERSES_o
unsafe def PERMUTES_INVERSES : thm := BBasicCons.PERMUTES_INVERSES
unsafe def PERMUTES_SUBSET : thm := BBasicCons.PERMUTES_SUBSET
unsafe def PERMUTES_EMPTY : thm := BBasicCons.PERMUTES_EMPTY
unsafe def PERMUTES_SING : thm := BBasicCons.PERMUTES_SING
unsafe def PERMUTES_UNIV : thm := BBasicCons.PERMUTES_UNIV
unsafe def PERMUTES_INVERSE_EQ : thm := BBasicCons.PERMUTES_INVERSE_EQ
unsafe def PERMUTES_SWAP : thm := BBasicCons.PERMUTES_SWAP
unsafe def PERMUTES_SUPERSET : thm := BBasicCons.PERMUTES_SUPERSET
unsafe def PERMUTES_BIJECTIONS : thm := BBasicCons.PERMUTES_BIJECTIONS
unsafe def PERMUTES_INVERSE_FUNCTION : thm := BBasicCons.PERMUTES_INVERSE_FUNCTION
unsafe def PERMUTES_ALT : thm := BBasicCons.PERMUTES_ALT
unsafe def PERMUTES_RESTRICT_SET : thm := BBasicCons.PERMUTES_RESTRICT_SET
unsafe def PERMUTES_RESTRICT : thm := BBasicCons.PERMUTES_RESTRICT
unsafe def PERMUTES_CARTESIAN_PRODUCT : thm := BBasicCons.PERMUTES_CARTESIAN_PRODUCT
unsafe def PERMUTES_TRANSFER_BIJECTIONS : thm := BBasicCons.PERMUTES_TRANSFER_BIJECTIONS
unsafe def PERMUTES_TRANSFER : thm := BBasicCons.PERMUTES_TRANSFER

-- Groups
unsafe def SWAP_CONJUGATE : thm := BGroups.SWAP_CONJUGATE
unsafe def PERMUTES_ID : thm := BGroups.PERMUTES_ID
unsafe def PERMUTES_I : thm := BGroups.PERMUTES_I
unsafe def PERMUTES_COMPOSE : thm := BGroups.PERMUTES_COMPOSE
unsafe def PERMUTES_INVERSE : thm := BGroups.PERMUTES_INVERSE
unsafe def PERMUTES_INVERSE_INVERSE : thm := BGroups.PERMUTES_INVERSE_INVERSE

-- NumPerms
unsafe def PERMUTES_INSERT_LEMMA : thm := BNumPerms.PERMUTES_INSERT_LEMMA
unsafe def PERMUTES_INSERT : thm := BNumPerms.PERMUTES_INSERT
unsafe def HAS_SIZE_PERMUTATIONS : thm := BNumPerms.HAS_SIZE_PERMUTATIONS
unsafe def FINITE_PERMUTATIONS : thm := BNumPerms.FINITE_PERMUTATIONS
unsafe def CARD_PERMUTATIONS : thm := BNumPerms.CARD_PERMUTATIONS

-- AltChar
unsafe def PERMUTES_FINITE_INJECTIVE : thm := BAltChar.PERMUTES_FINITE_INJECTIVE
unsafe def PERMUTES_FINITE_SURJECTIVE : thm := BAltChar.PERMUTES_FINITE_SURJECTIVE

-- Restrict
unsafe def RESTRICT_PERMUTES_SUBSET : thm := BRestrict.RESTRICT_PERMUTES_SUBSET
unsafe def RESTRICT_I : thm := BRestrict.RESTRICT_I
unsafe def RESTRICT_COMPOSE : thm := BRestrict.RESTRICT_COMPOSE
unsafe def RESTRICT_INVERSE : thm := BRestrict.RESTRICT_INVERSE
unsafe def RESTRICT_SWAP : thm := BRestrict.RESTRICT_SWAP

-- IterSwap
unsafe def ITERATE_PERMUTE : thm := BIterSwap.ITERATE_PERMUTE
unsafe def NSUM_PERMUTE : thm := BIterSwap.NSUM_PERMUTE
unsafe def NSUM_PERMUTE_NUMSEG : thm := BIterSwap.NSUM_PERMUTE_NUMSEG
unsafe def SUM_PERMUTE : thm := BIterSwap.SUM_PERMUTE
unsafe def SUM_PERMUTE_NUMSEG : thm := BIterSwap.SUM_PERMUTE_NUMSEG
unsafe def SWAP_COMMON : thm := BIterSwap.SWAP_COMMON
unsafe def SWAP_COMMON' : thm := BIterSwap.SWAP_COMMON'
unsafe def SWAP_INDEPENDENT : thm := BIterSwap.SWAP_INDEPENDENT

-- ThreeCycle
unsafe def three_cycle : thm := BThreeCycle.three_cycle
unsafe def PERMUTES_THREE_CYCLE : thm := BThreeCycle.PERMUTES_THREE_CYCLE
unsafe def THREE_CYCLE_COMPOSE_REVERSE : thm := BThreeCycle.THREE_CYCLE_COMPOSE_REVERSE
unsafe def THREE_CYCLE_INVERSE : thm := BThreeCycle.THREE_CYCLE_INVERSE
unsafe def THREE_CYCLE_AS_COMMUTATOR : thm := BThreeCycle.THREE_CYCLE_AS_COMMUTATOR
unsafe def THREE_CYCLE_COMMUTATOR : thm := BThreeCycle.THREE_CYCLE_COMMUTATOR
unsafe def THREE_CYCLE_NOT_I : thm := BThreeCycle.THREE_CYCLE_NOT_I

-- Swapseq
unsafe def swapseq_RULES : thm := BSwapseq.swapseq_RULES
unsafe def swapseq_INDUCT : thm := BSwapseq.swapseq_INDUCT
unsafe def swapseq_CASES : thm := BSwapseq.swapseq_CASES
unsafe def permutation : thm := BSwapseq.permutation
unsafe def SWAPSEQ_I : thm := BSwapseq.SWAPSEQ_I
unsafe def PERMUTATION_I : thm := BSwapseq.PERMUTATION_I
unsafe def SWAPSEQ_SWAP : thm := BSwapseq.SWAPSEQ_SWAP
unsafe def PERMUTATION_SWAP : thm := BSwapseq.PERMUTATION_SWAP
unsafe def SWAPSEQ_COMPOSE : thm := BSwapseq.SWAPSEQ_COMPOSE
unsafe def PERMUTATION_COMPOSE : thm := BSwapseq.PERMUTATION_COMPOSE
unsafe def SWAPSEQ_ENDSWAP : thm := BSwapseq.SWAPSEQ_ENDSWAP
unsafe def SWAPSEQ_INVERSE_EXISTS : thm := BSwapseq.SWAPSEQ_INVERSE_EXISTS
unsafe def SWAPSEQ_INVERSE : thm := BSwapseq.SWAPSEQ_INVERSE
unsafe def PERMUTATION_INVERSE : thm := BSwapseq.PERMUTATION_INVERSE
unsafe def SYMMETRY_LEMMA : thm := BSwapseq.SYMMETRY_LEMMA
unsafe def SWAP_GENERAL : thm := BSwapseq.SWAP_GENERAL
unsafe def FIXING_SWAPSEQ_DECREASE : thm := BSwapseq.FIXING_SWAPSEQ_DECREASE
unsafe def SWAPSEQ_IDENTITY_EVEN : thm := BSwapseq.SWAPSEQ_IDENTITY_EVEN

-- Evenperm
unsafe def evenperm : thm := BEvenperm.evenperm
unsafe def SWAPSEQ_EVEN_EVEN : thm := BEvenperm.SWAPSEQ_EVEN_EVEN
unsafe def EVENPERM_UNIQUE : thm := BEvenperm.EVENPERM_UNIQUE
unsafe def EVENPERM_I : thm := BEvenperm.EVENPERM_I
unsafe def EVENPERM_ID : thm := BEvenperm.EVENPERM_ID
unsafe def EVENPERM_SWAP : thm := BEvenperm.EVENPERM_SWAP
unsafe def EVENPERM_COMPOSE : thm := BEvenperm.EVENPERM_COMPOSE
unsafe def EVENPERM_INVERSE : thm := BEvenperm.EVENPERM_INVERSE
unsafe def PERMUTATION_BIJECTIVE : thm := BEvenperm.PERMUTATION_BIJECTIVE
unsafe def PERMUTATION_FINITE_SUPPORT : thm := BEvenperm.PERMUTATION_FINITE_SUPPORT
unsafe def PERMUTATION_LEMMA : thm := BEvenperm.PERMUTATION_LEMMA
unsafe def PERMUTATION : thm := BEvenperm.PERMUTATION
unsafe def PERMUTATION_INVERSE_WORKS : thm := BEvenperm.PERMUTATION_INVERSE_WORKS
unsafe def PERMUTATION_INVERSE_COMPOSE : thm := BEvenperm.PERMUTATION_INVERSE_COMPOSE
unsafe def PERMUTATION_COMPOSE_EQ : thm := BEvenperm.PERMUTATION_COMPOSE_EQ
unsafe def PERMUTATION_COMPOSE_SWAP : thm := BEvenperm.PERMUTATION_COMPOSE_SWAP

-- Sign
unsafe def PERMUTATION_PERMUTES : thm := BSign.PERMUTATION_PERMUTES
unsafe def PERMUTATION_RESTRICT : thm := BSign.PERMUTATION_RESTRICT
unsafe def PERMUTES_INDUCT : thm := BSign.PERMUTES_INDUCT
unsafe def PERMUTES_INDUCT_STRONG : thm := BSign.PERMUTES_INDUCT_STRONG
unsafe def sign : thm := BSign.sign
unsafe def SIGN_NZ : thm := BSign.SIGN_NZ
unsafe def SIGN_I : thm := BSign.SIGN_I
unsafe def SIGN_ID : thm := BSign.SIGN_ID
unsafe def SIGN_INVERSE : thm := BSign.SIGN_INVERSE
unsafe def SIGN_COMPOSE : thm := BSign.SIGN_COMPOSE
unsafe def SIGN_SWAP : thm := BSign.SIGN_SWAP
unsafe def SIGN_IDEMPOTENT : thm := BSign.SIGN_IDEMPOTENT
unsafe def REAL_ABS_SIGN : thm := BSign.REAL_ABS_SIGN
unsafe def REAL_SGN_SIGN : thm := BSign.REAL_SGN_SIGN
unsafe def EVENPERM_TRANSFER : thm := BSign.EVENPERM_TRANSFER

-- SignTransfer
unsafe def SIGN_TRANSFER : thm := BSignTransfer.SIGN_TRANSFER
unsafe def SIGN_CARTESIAN_PRODUCT : thm := BSignTransfer.SIGN_CARTESIAN_PRODUCT
unsafe def PERMUTES_NUMSET_LE : thm := BSignTransfer.PERMUTES_NUMSET_LE
unsafe def PERMUTES_NUMSET_GE : thm := BSignTransfer.PERMUTES_NUMSET_GE
unsafe def IMAGE_INVERSE_PERMUTATIONS : thm := BSignTransfer.IMAGE_INVERSE_PERMUTATIONS
unsafe def IMAGE_COMPOSE_PERMUTATIONS_L : thm := BSignTransfer.IMAGE_COMPOSE_PERMUTATIONS_L
unsafe def IMAGE_COMPOSE_PERMUTATIONS_R : thm := BSignTransfer.IMAGE_COMPOSE_PERMUTATIONS_R
unsafe def PERMUTES_IN_NUMSEG : thm := BSignTransfer.PERMUTES_IN_NUMSEG
unsafe def SUM_PERMUTATIONS_INVERSE : thm := BSignTransfer.SUM_PERMUTATIONS_INVERSE
unsafe def SUM_PERMUTATIONS_COMPOSE_L : thm := BSignTransfer.SUM_PERMUTATIONS_COMPOSE_L
unsafe def SUM_PERMUTATIONS_COMPOSE_R : thm := BSignTransfer.SUM_PERMUTATIONS_COMPOSE_R
unsafe def CARD_EVEN_PERMUTATIONS : thm := BSignTransfer.CARD_EVEN_PERMUTATIONS

-- Involution
unsafe def PERMUTES_INVOLUTION : thm := BInvolution.PERMUTES_INVOLUTION
unsafe def SIGN_INVOLUTION : thm := BInvolution.SIGN_INVOLUTION
unsafe def PERMUTES_CYCLIC : thm := BInvolution.PERMUTES_CYCLIC
unsafe def PERMUTES_CYCLIC_N : thm := BInvolution.PERMUTES_CYCLIC_N
unsafe def PERMUTATION_CYCLIC : thm := BInvolution.PERMUTATION_CYCLIC
unsafe def PERMUTATION_CYCLIC_N : thm := BInvolution.PERMUTATION_CYCLIC_N
unsafe def EVENPERM_CYCLIC : thm := BInvolution.EVENPERM_CYCLIC
unsafe def EVENPERM_CYCLIC_N : thm := BInvolution.EVENPERM_CYCLIC_N
unsafe def SIGN_CYCLIC : thm := BInvolution.SIGN_CYCLIC
unsafe def SIGN_CYCLIC_N : thm := BInvolution.SIGN_CYCLIC_N

-- Permset
unsafe def PERMSET_CONV : term → IO (Except String thm) := fun t => (BPermset.PERMSET_CONV t).run

-- SumOver
unsafe def SUM_OVER_PERMUTATIONS_INSERT : thm := BSumOver.SUM_OVER_PERMUTATIONS_INSERT
unsafe def SUM_OVER_PERMUTATIONS_NUMSEG : thm := BSumOver.SUM_OVER_PERMUTATIONS_NUMSEG
-- @@EXPORTS END

/-- `needs "Library/permutations.ml"`: build the bundles, in order. -/
unsafe def ensurePermutations : IO Unit := do
  -- @@ENSURE BEGIN
  let _ ← IO.mkRef BPermutes.permutes
  let _ ← IO.mkRef BBasicCons.PERMUTES_IN_IMAGE
  let _ ← IO.mkRef BGroups.SWAP_CONJUGATE
  let _ ← IO.mkRef BNumPerms.PERMUTES_INSERT_LEMMA
  let _ ← IO.mkRef BAltChar.PERMUTES_FINITE_INJECTIVE
  let _ ← IO.mkRef BRestrict.RESTRICT_PERMUTES_SUBSET
  let _ ← IO.mkRef BIterSwap.ITERATE_PERMUTE
  let _ ← IO.mkRef BThreeCycle.three_cycle
  let _ ← IO.mkRef BSwapseq.swapseq_RULES
  let _ ← IO.mkRef BEvenperm.evenperm
  let _ ← IO.mkRef BSign.PERMUTATION_PERMUTES
  let _ ← IO.mkRef BSignTransfer.SIGN_TRANSFER
  let _ ← IO.mkRef BInvolution.PERMUTES_INVOLUTION
  let _ ← IO.mkRef BPermset.PERMSET_CONV
  let _ ← IO.mkRef BSumOver.SUM_OVER_PERMUTATIONS_INSERT
  -- @@ENSURE END
  pure ()

end SessionLibrary.Permutations
