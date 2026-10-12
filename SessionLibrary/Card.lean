/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/card.ml.                                    -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Card.lean

  The `unsafe` half of the card.ml translation: it supplies HolLibrary.Card's
  dependencies from Session, builds each bundle once, in file order, and
  exports every name under its HOL Light name.  `ensureCard` is `needs
  "Library/card.ml"` (which first does `needs "Library/wo.ml"`).

  The blocks between `@@CORE` and `@@EXPORTS` markers are generated from
  HolLibrary/Card.lean by tools/carddiff/gen_session.py and scope.py
  (bookkeeping only: field-by-field copies and accessors).
-/

import Session
import HolLibrary.Card
import SessionLibrary.Wo

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Card

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨Session.sessionB, Session.sessionC, Session.sessionT⟩

-- @@CORE BEGIN
/-- The core theorems card.ml uses. -/
unsafe def core1 (_ : Unit) : HolLibrary.Card.CoreThms1 where
  ADD1 := Session.ADD1
  AND_FORALL_THM := Session.AND_FORALL_THM
  ARB := Session.ARB
  ARITH := Session.ARITH
  CARD_BOOL := Session.CARD_BOOL
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARD_CROSS := Session.CARD_CROSS
  CARD_DIFF := Session.CARD_DIFF
  CARD_IMAGE_INJ := Session.CARD_IMAGE_INJ
  CARD_LE_1 := Session.CARD_LE_1
  CARD_NUMSEG_1 := Session.CARD_NUMSEG_1
  CARD_SING := Session.CARD_SING
  CARD_SUBSET := Session.CARD_SUBSET
  CARD_SUBSET_EQ := Session.CARD_SUBSET_EQ
  CARD_UNION := Session.CARD_UNION
  CARTESIAN_PRODUCT_EQ_EMPTY := Session.CARTESIAN_PRODUCT_EQ_EMPTY
  CARTESIAN_PRODUCT_EQ_MEMBERS := Session.CARTESIAN_PRODUCT_EQ_MEMBERS
  CART_EQ := Session.CART_EQ
  COMPL_COMPL := Session.COMPL_COMPL
  COND_RAND := Session.COND_RAND
  COND_RATOR := Session.COND_RATOR
  CONJ_ACI := Session.CONJ_ACI
  CONJ_ASSOC := Session.CONJ_ASSOC
  CONJ_SYM := Session.CONJ_SYM
  CONS_11 := Session.listThms1.CONS_11
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  COUNTABLE := Session.COUNTABLE
  CROSS := Session.CROSS
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DIFF_EMPTY := Session.DIFF_EMPTY
  DIMINDEX_GE_1 := Session.DIMINDEX_GE_1
  DISJOINT := Session.DISJOINT
  DISJOINT_SING := Session.DISJOINT_SING
  EL := Session.listDefs.EL
  EMPTY_GSPEC := Session.EMPTY_GSPEC
  EMPTY_SUBSET := Session.EMPTY_SUBSET
  EQ_IMP := Session.EQ_IMP
  EQ_SYM_EQ := Session.EQ_SYM_EQ
  EQ_TRANS := Session.EQ_TRANS
  ETA_AX := Session.ETA_AX
  EXISTS_IN_GSPEC := Session.EXISTS_IN_GSPEC
  EXISTS_IN_IMAGE := Session.EXISTS_IN_IMAGE
  EXISTS_PAIR_THM := Session.EXISTS_PAIR_THM
  EXISTS_REFL := Session.EXISTS_REFL
  EXISTS_SUBSET_IMAGE_INJ := Session.EXISTS_SUBSET_IMAGE_INJ
  EXISTS_UNIQUE_ALT := Session.EXISTS_UNIQUE_ALT
  EXISTS_UNIQUE_DEF := Session.EXISTS_UNIQUE_DEF
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXP := Session.EXP
  EXTENSION := Session.EXTENSION
  EXTENSIONAL := Session.EXTENSIONAL
  FINITE_BOOL := Session.FINITE_BOOL
  FINITE_CROSS := Session.FINITE_CROSS
  FINITE_CROSS_EQ := Session.FINITE_CROSS_EQ
  FINITE_DIFF := Session.FINITE_DIFF
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_INDEX_NUMBERS := Session.FINITE_INDEX_NUMBERS
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_INTER := Session.FINITE_INTER
  FINITE_NUMSEG := Session.FINITE_NUMSEG
  FINITE_POWERSET := Session.FINITE_POWERSET
  FINITE_PRODUCT := Session.FINITE_PRODUCT
  FINITE_RESTRICTED_FUNSPACE := Session.FINITE_RESTRICTED_FUNSPACE
  FINITE_RULES := Session.FINITE_RULES
  FINITE_SING := Session.FINITE_SING
  FINITE_SUBSET := Session.FINITE_SUBSET
  FINITE_UNION := Session.FINITE_UNION
  FINITE_UNIONS := Session.FINITE_UNIONS
  FORALL_AND_THM := Session.FORALL_AND_THM
  FORALL_CURRY := Session.FORALL_CURRY
  FORALL_INT_CASES := Session.FORALL_INT_CASES
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  FORALL_IN_PCROSS := Session.FORALL_IN_PCROSS
  FORALL_IN_UNION := Session.FORALL_IN_UNION
  FORALL_IN_UNIONS := Session.FORALL_IN_UNIONS
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  FSTCART_PASTECART := Session.FSTCART_PASTECART
  FUNCTION_FACTORS_LEFT_GEN := Session.FUNCTION_FACTORS_LEFT_GEN
  FUN_EQ_THM := Session.FUN_EQ_THM
  HAS_SIZE := Session.HAS_SIZE
  HD := Session.listDefs.HD
  IMAGE_CLAUSES := Session.IMAGE_CLAUSES
  IMAGE_ID := Session.IMAGE_ID
  IMAGE_SUBSET := Session.IMAGE_SUBSET
  IMAGE_UNION := Session.IMAGE_UNION
  IMAGE_o := Session.IMAGE_o
  IMP_CONJ := Session.IMP_CONJ
  IMP_CONJ_ALT := Session.IMP_CONJ_ALT
  IMP_IMP := Session.IMP_IMP
  IN := Session.IN
/-- The core theorems card.ml uses. -/
unsafe def core2 (_ : Unit) : HolLibrary.Card.CoreThms2 where
  INFINITE := Session.INFINITE
  INFINITE_CROSS_EQ := Session.INFINITE_CROSS_EQ
  INFINITE_ENUMERATE_SUBSET := Session.INFINITE_ENUMERATE_SUBSET
  INJECTIVE_LEFT_INVERSE := Session.INJECTIVE_LEFT_INVERSE
  INJECTIVE_ON_ALT := Session.INJECTIVE_ON_ALT
  INJECTIVE_ON_LEFT_INVERSE := Session.INJECTIVE_ON_LEFT_INVERSE
  INTER := Session.INTER
  INTERSECTION_OF := Session.INTERSECTION_OF
  INTERSECTION_OF_EMPTY := Session.INTERSECTION_OF_EMPTY
  INTERSECTION_OF_INC := Session.INTERSECTION_OF_INC
  INTERS_0 := Session.INTERS_0
  INTERS_1 := Session.INTERS_1
  INTERS_2 := Session.INTERS_2
  INTERS_GSPEC := Session.INTERS_GSPEC
  INTERS_IMAGE := Session.INTERS_IMAGE
  INTERS_INSERT := Session.INTERS_INSERT
  INTERS_UNIONS := Session.INTERS_UNIONS
  INTER_COMM := Session.INTER_COMM
  INTER_SUBSET := Session.INTER_SUBSET
  INTER_UNIONS := Session.INTER_UNIONS
  INTER_UNIV := Session.INTER_UNIV
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  IN_CARTESIAN_PRODUCT := Session.IN_CARTESIAN_PRODUCT
  IN_CROSS := Session.IN_CROSS
  IN_DIFF := Session.IN_DIFF
  IN_ELIM_PAIR_THM := Session.IN_ELIM_PAIR_THM
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_GSPEC := Session.IN_GSPEC
  IN_IMAGE := Session.IN_IMAGE
  IN_INTER := Session.IN_INTER
  IN_INTERS := Session.IN_INTERS
  IN_NUMSEG := Session.IN_NUMSEG
  IN_SING := Session.IN_SING
  IN_UNION := Session.IN_UNION
  IN_UNIONS := Session.IN_UNIONS
  IN_UNIV := Session.IN_UNIV
  ITLIST := Session.listDefs.ITLIST
  I_THM := Session.I_THM
  LAMBDA_BETA := Session.LAMBDA_BETA
  LE := Session.LE
  LEFT_AND_EXISTS_THM := Session.LEFT_AND_EXISTS_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LEFT_IMP_FORALL_THM := Session.LEFT_IMP_FORALL_THM
  LENGTH := Session.listDefs.LENGTH
  LENGTH_EQ_NIL := Session.listThms1.LENGTH_EQ_NIL
  LET_ANTISYM := Session.LET_ANTISYM
  LE_0 := Session.LE_0
  LE_1 := Session.LE_1
  LE_ADD_LCANCEL := Session.LE_ADD_LCANCEL
  LE_ANTISYM := Session.LE_ANTISYM
  LE_C := Session.LE_C
  LE_REFL := Session.LE_REFL
  LE_TRANS := Session.LE_TRANS
  LT := Session.LT
  LT_LE := Session.LT_LE
  LT_SUC := Session.LT_SUC
  MAP := Session.listDefs.MAP
  MAP_EQ_NIL := Session.listThms2.MAP_EQ_NIL
  MEM := Session.listDefs.MEM
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MEM_LIST_OF_SET := Session.MEM_LIST_OF_SET
  MEM_MAP := Session.listThms1.MEM_MAP
  MONO_AND := Session.MONO_AND
  MONO_EXISTS := Session.MONO_EXISTS
  MONO_FORALL := Session.MONO_FORALL
  NOT_CONS_NIL := Session.listThms1.NOT_CONS_NIL
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NOT_INSERT_EMPTY := Session.NOT_INSERT_EMPTY
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NOT_LE := Session.NOT_LE
  NOT_SUC := Session.NOT_SUC
  NUMPAIR_INJ := Session.NUMPAIR_INJ
  NUMSEG_CLAUSES := Session.NUMSEG_CLAUSES
  NUMSEG_EMPTY := Session.NUMSEG_EMPTY
  NUMSEG_SING := Session.NUMSEG_SING
  OR_EXISTS_THM := Session.OR_EXISTS_THM
  PAIR := Session.PAIR
  PAIRWISE_IMAGE := Session.PAIRWISE_IMAGE
  PAIRWISE_SING := Session.PAIRWISE_SING
  PAIR_EQ := Session.PAIR_EQ
  PASTECART_FST_SND := Session.PASTECART_FST_SND
  PASTECART_IN_PCROSS := Session.PASTECART_IN_PCROSS
  REAL_ADD_RID := Session.REAL_ADD_RID
  REAL_ARCH := Session.REAL_ARCH
  REAL_ARCH_LT := Session.REAL_ARCH_LT
  REAL_BOUNDS_LT := Session.REAL_BOUNDS_LT
  REAL_EQ_ADD_LCANCEL := Session.REAL_EQ_ADD_LCANCEL
  REAL_EQ_MUL_LCANCEL := Session.REAL_EQ_MUL_LCANCEL
  REAL_INV_MUL := Session.REAL_INV_MUL
  REAL_LET_TRANS := Session.REAL_LET_TRANS
  REAL_LE_DIV := Session.REAL_LE_DIV
  REAL_LE_INV_EQ := Session.REAL_LE_INV_EQ
/-- The core theorems card.ml uses. -/
unsafe def core3 (_ : Unit) : HolLibrary.Card.CoreThms3 where
  REAL_LE_MUL := Session.REAL_LE_MUL
  REAL_LT_DIV := Session.REAL_LT_DIV
  REAL_LT_IMP_LE := Session.REAL_LT_IMP_LE
  REAL_LT_INV_EQ := Session.REAL_LT_INV_EQ
  REAL_LT_LMUL_EQ := Session.REAL_LT_LMUL_EQ
  REAL_MUL_ASSOC := Session.REAL_MUL_ASSOC
  REAL_OF_NUM_LT := Session.REAL_OF_NUM_LT
  REAL_OF_NUM_SUC := Session.REAL_OF_NUM_SUC
  REAL_POS := Session.REAL_POS
  REAL_POW_1 := Session.REAL_POW_1
  REAL_POW_ADD := Session.REAL_POW_ADD
  REAL_POW_LE := Session.REAL_POW_LE
  REAL_POW_LT := Session.REAL_POW_LT
  REAL_SHRINK_EQ := Session.REAL_SHRINK_EQ
  REAL_SHRINK_RANGE := Session.REAL_SHRINK_RANGE
  REAL_SUB_LT := Session.REAL_SUB_LT
  REAL_SUP_LE := Session.REAL_SUP_LE
  REAL_WLOG_LT := Session.REAL_WLOG_LT
  RESTRICTION := Session.RESTRICTION
  RESTRICTION_IN_CARTESIAN_PRODUCT := Session.RESTRICTION_IN_CARTESIAN_PRODUCT
  RESTRICTION_UNIQUE := Session.RESTRICTION_UNIQUE
  RIGHT_AND_EXISTS_THM := Session.RIGHT_AND_EXISTS_THM
  RIGHT_EXISTS_AND_THM := Session.RIGHT_EXISTS_AND_THM
  RIGHT_EXISTS_IMP_THM := Session.RIGHT_EXISTS_IMP_THM
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RIGHT_IMP_EXISTS_THM := Session.RIGHT_IMP_EXISTS_THM
  RIGHT_IMP_FORALL_THM := Session.RIGHT_IMP_FORALL_THM
  SET_OF_LIST_OF_SET := Session.SET_OF_LIST_OF_SET
  SIMPLE_IMAGE := Session.SIMPLE_IMAGE
  SING_GSPEC := Session.SING_GSPEC
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SNDCART_PASTECART := Session.SNDCART_PASTECART
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUBSET_DIFF := Session.SUBSET_DIFF
  SUBSET_IMAGE_INJ := Session.SUBSET_IMAGE_INJ
  SUBSET_NUMSEG := Session.SUBSET_NUMSEG
  SUBSET_REFL := Session.SUBSET_REFL
  SUBSET_RESTRICT := Session.SUBSET_RESTRICT
  SUBSET_TRANS := Session.SUBSET_TRANS
  SUBSET_UNION := Session.SUBSET_UNION
  SUBSET_UNIV := Session.SUBSET_UNIV
  SUC_INJ := Session.SUC_INJ
  SUM_CLAUSES := Session.SUM_CLAUSES
  SUM_CLAUSES_LEFT := Session.SUM_CLAUSES_LEFT
  SUM_CLAUSES_RIGHT := Session.SUM_CLAUSES_RIGHT
  SUM_COMBINE_R := Session.SUM_COMBINE_R
  SUM_EQ_NUMSEG := Session.SUM_EQ_NUMSEG
  SUM_RESTRICT_SET := Session.SUM_RESTRICT_SET
  SUM_SING := Session.SUM_SING
  SUM_SUBSET_SIMPLE := Session.SUM_SUBSET_SIMPLE
  SUP := Session.SUP
  SURJECTIVE_ON_RIGHT_INVERSE := Session.SURJECTIVE_ON_RIGHT_INVERSE
  SURJECTIVE_RIGHT_INVERSE := Session.SURJECTIVE_RIGHT_INVERSE
  SWAP_EXISTS_THM := Session.SWAP_EXISTS_THM
  SWAP_FORALL_THM := Session.SWAP_FORALL_THM
  TL := Session.listDefs.TL
  UNIONS := Session.UNIONS
  UNIONS_0 := Session.UNIONS_0
  UNIONS_1 := Session.UNIONS_1
  UNIONS_2 := Session.UNIONS_2
  UNIONS_GSPEC := Session.UNIONS_GSPEC
  UNIONS_IMAGE := Session.UNIONS_IMAGE
  UNIONS_INSERT := Session.UNIONS_INSERT
  UNIONS_INTERS := Session.UNIONS_INTERS
  UNIONS_UNION := Session.UNIONS_UNION
  UNION_COMM := Session.UNION_COMM
  UNION_EMPTY := Session.UNION_EMPTY
  UNION_OF := Session.UNION_OF
  UNION_OF_EMPTY := Session.UNION_OF_EMPTY
  UNION_OF_INC := Session.UNION_OF_INC
  UNIV_NOT_EMPTY := Session.UNIV_NOT_EMPTY
  UNWIND_THM1 := Session.UNWIND_THM1
  UNWIND_THM2 := Session.UNWIND_THM2
  WF_MEASURE_GEN := Session.WF_MEASURE_GEN
  WF_SUBSET := Session.WF_SUBSET
  cartesian_product := Session.cartesian_product
  eq_c := Session.eq_c
  ge_c := Session.ge_c
  le_c := Session.le_c
  lt_c := Session.lt_c
  num_INDUCTION := Session.num_INDUCTION
  num_INFINITE := Session.num_INFINITE
  num_WOP := Session.num_WOP
  o_DEF := Session.o_DEF
  o_THM := Session.o_THM
  pair_RECURSION := Session.pair_RECURSION
  pairwise := Session.pairwise
  real_INFINITE := Session.real_INFINITE
  real_div := Session.real_div
  real_pow := Session.real_pow
  sum_INDUCT := Session.sum_INDUCT
  sum_RECURSION := Session.sum_RECURSION-- @@CORE END

/-- What card.ml uses from Session. -/
unsafe def deps (_ : Unit) : HolLibrary.Card.CardDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  parse_as_infix := Session.parse_as_infix
  distinctness s := ExceptT.mk (pure (Session.distinctness s))
  injectivity s := ExceptT.mk (pure (Session.injectivity s))
  prove_cases_thm th := ExceptT.mk (Session.prove_cases_thm th)
  prove_recursive_functions_exist ax t := ExceptT.mk (Session.prove_recursive_functions_exist ax t)
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  ASM_METIS_TAC := Session.ASM_METIS_TAC
  ASM_REAL_ARITH_TAC := Session.ASM_REAL_ARITH_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  LIST_INDUCT_TAC := Session.LIST_INDUCT_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  METIS_TAC := Session.METIS_TAC
  REAL_ARITH t := ExceptT.mk (Session.REAL_ARITH3 t)
  REAL_ARITH_TAC := Session.REAL_ARITH_TAC2
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  WF_INDUCT_TAC := Session.WF_INDUCT_TAC
  GEN_BETA_CONV := Session.GEN_BETA_CONV
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  REAL_RAT_REDUCE_CONV := Session.REAL_RAT_REDUCE_CONV
  SELECT_CONV t := pure (Session.SELECT_CONV t)
  core1 := core1 ()
  core2 := core2 ()
  core3 := core3 ()

/-- Build a bundle once.  `setup` is a thunk, so that `deps` is not built
    before the bundle is needed.  The whole core library is built first
    (`Session.ensureDefine`), as HOL Light has loaded all of hol_lib.ml
    before `needs "Library/card.ml"`, and then wo.ml, which card.ml needs. -/
private unsafe def cached {α : Type} [Inhabited α] (r : IO.Ref (Option α)) (name : String)
    (setup : Unit → IO (Except String α)) : α :=
  match unsafeIO (do
    match ← r.get with
    | some d => pure d
    | none => do
      Session.ensureDefine
      -- HOL Light adds MATCH_CONV to the basic conversions loading
      -- ind_types.ml; Session builds that layer on first use, and card.ml's
      -- rewrites need it (`function` terms, UNION_LE_ADD_C).
      let _ ← Session.MATCH_CONV (HolCore.Kernel.mk_var "p" HolCore.Kernel.bool_ty)
      SessionLibrary.Wo.ensureWo
      match ← setup () with
      | .ok d => do r.set (some d); pure d
      | .error e => panic! s!"{name} failed: {e}") with
  | .ok d => d | _ => panic! s!"SessionLibrary.Card: {name}"

/- The bundles, in card.ml order.  Each forces the one before it, so that
   any bundle builds every earlier one first, as HOL Light's load does. -/

-- @@BUNDLES BEGIN
initialize theBasics : IO.Ref (Option HolLibrary.Card.Basics) ← IO.mkRef none
unsafe def BBasics : HolLibrary.Card.Basics :=
  cached theBasics "setupBasics" fun _ => do
    (HolLibrary.Card.setupBasics (deps ())).run

initialize theOrder : IO.Ref (Option HolLibrary.Card.Order) ← IO.mkRef none
unsafe def BOrder : HolLibrary.Card.Order :=
  cached theOrder "setupOrder" fun _ => do
    let _ ← IO.mkRef BBasics.TRANS_CHAIN_TAC
    (HolLibrary.Card.setupOrder (deps ()) BBasics SessionLibrary.Wo.BDefs SessionLibrary.Wo.BOrders SessionLibrary.Wo.BSegs SessionLibrary.Wo.BInseg SessionLibrary.Wo.BWellOrder SessionLibrary.Wo.BZorn).run

initialize theArith : IO.Ref (Option HolLibrary.Card.Arith) ← IO.mkRef none
unsafe def BArith : HolLibrary.Card.Arith :=
  cached theArith "setupArith" fun _ => do
    let _ ← IO.mkRef BOrder.CARD_LE_ANTISYM
    (HolLibrary.Card.setupArith (deps ()) BBasics BOrder).run

initialize theSquare : IO.Ref (Option HolLibrary.Card.Square) ← IO.mkRef none
unsafe def BSquare : HolLibrary.Card.Square :=
  cached theSquare "setupSquare" fun _ => do
    let _ ← IO.mkRef BArith.add_c
    (HolLibrary.Card.setupSquare (deps ()) BBasics BOrder BArith SessionLibrary.Wo.BZorn).run

initialize theCancel : IO.Ref (Option HolLibrary.Card.Cancel) ← IO.mkRef none
unsafe def BCancel : HolLibrary.Card.Cancel :=
  cached theCancel "setupCancel" fun _ => do
    let _ ← IO.mkRef BSquare.CARD_SQUARE_INFINITE
    (HolLibrary.Card.setupCancel (deps ()) BBasics BOrder BArith BSquare).run

initialize theCountable : IO.Ref (Option HolLibrary.Card.Countable) ← IO.mkRef none
unsafe def BCountable : HolLibrary.Card.Countable :=
  cached theCountable "setupCountable" fun _ => do
    let _ ← IO.mkRef BCancel.CARD_LT_ADD
    (HolLibrary.Card.setupCountable (deps ()) BBasics BOrder BArith BSquare BCancel).run

initialize theUnionOf : IO.Ref (Option HolLibrary.Card.UnionOf) ← IO.mkRef none
unsafe def BUnionOf : HolLibrary.Card.UnionOf :=
  cached theUnionOf "setupUnionOf" fun _ => do
    let _ ← IO.mkRef BCountable.CANTOR_THM
    (HolLibrary.Card.setupUnionOf (deps ()) BCountable SessionLibrary.Wo.BDefs).run

initialize theReals : IO.Ref (Option HolLibrary.Card.Reals) ← IO.mkRef none
unsafe def BReals : HolLibrary.Card.Reals :=
  cached theReals "setupReals" fun _ => do
    let _ ← IO.mkRef BUnionOf.COUNTABLE_CART
    (HolLibrary.Card.setupReals (deps ()) BBasics BOrder BArith BSquare BCountable BUnionOf).run

initialize theExp : IO.Ref (Option HolLibrary.Card.Exp) ← IO.mkRef none
unsafe def BExp : HolLibrary.Card.Exp :=
  cached theExp "setupExp" fun _ => do
    let _ ← IO.mkRef BReals.COUNTABLE_UNION_OF_INTERS_NONEMPTY
    (HolLibrary.Card.setupExp (deps ()) BBasics BOrder BArith BSquare BCountable BReals).run

initialize thePowerset : IO.Ref (Option HolLibrary.Card.Powerset) ← IO.mkRef none
unsafe def BPowerset : HolLibrary.Card.Powerset :=
  cached thePowerset "setupPowerset" fun _ => do
    let _ ← IO.mkRef BExp.exp_c
    (HolLibrary.Card.setupPowerset (deps ()) BBasics BOrder BArith BSquare BCountable BReals BExp).run

initialize theCartesian : IO.Ref (Option HolLibrary.Card.Cartesian) ← IO.mkRef none
unsafe def BCartesian : HolLibrary.Card.Cartesian :=
  cached theCartesian "setupCartesian" fun _ => do
    let _ ← IO.mkRef BPowerset.CARD_EQ_RESTRICTED_POWERSET
    (HolLibrary.Card.setupCartesian (deps ()) BBasics BOrder BArith BSquare BCountable BReals BExp BPowerset).run

-- @@BUNDLES END

-- @@EXPORTS BEGIN
-- Basics
unsafe def TRANS_CHAIN_TAC := BBasics.TRANS_CHAIN_TAC
unsafe def sum_DISTINCT : thm := BBasics.sum_DISTINCT
unsafe def sum_INJECTIVE : thm := BBasics.sum_INJECTIVE
unsafe def sum_CASES : thm := BBasics.sum_CASES
unsafe def FORALL_SUM_THM : thm := BBasics.FORALL_SUM_THM
unsafe def EXISTS_SUM_THM : thm := BBasics.EXISTS_SUM_THM
unsafe def FLATTEN_LEMMA : thm := BBasics.FLATTEN_LEMMA
unsafe def TARSKI_SET : thm := BBasics.TARSKI_SET
unsafe def INJECTIVE_LEFT_INVERSE_NONEMPTY : thm := BBasics.INJECTIVE_LEFT_INVERSE_NONEMPTY
unsafe def BIJECTIVE_INJECTIVE_SURJECTIVE : thm := BBasics.BIJECTIVE_INJECTIVE_SURJECTIVE
unsafe def BIJECTIVE_INVERSES : thm := BBasics.BIJECTIVE_INVERSES
unsafe def EQ_C_BIJECTIONS : thm := BBasics.EQ_C_BIJECTIONS
unsafe def EQ_C : thm := BBasics.EQ_C
unsafe def EQ_C_ALT : thm := BBasics.EQ_C_ALT
unsafe def CARD_LE_REFL : thm := BBasics.CARD_LE_REFL
unsafe def CARD_EMPTY_LE : thm := BBasics.CARD_EMPTY_LE
unsafe def CARD_LE_TRANS : thm := BBasics.CARD_LE_TRANS
unsafe def CARD_LT_REFL : thm := BBasics.CARD_LT_REFL
unsafe def CARD_LET_TRANS : thm := BBasics.CARD_LET_TRANS
unsafe def CARD_LTE_TRANS : thm := BBasics.CARD_LTE_TRANS
unsafe def CARD_LT_TRANS : thm := BBasics.CARD_LT_TRANS
unsafe def CARD_EQ_REFL : thm := BBasics.CARD_EQ_REFL
unsafe def CARD_EQ_REFL_IMP : thm := BBasics.CARD_EQ_REFL_IMP
unsafe def CARD_EQ_SYM : thm := BBasics.CARD_EQ_SYM
unsafe def CARD_EQ_IMP_LE : thm := BBasics.CARD_EQ_IMP_LE
unsafe def CARD_LT_IMP_LE : thm := BBasics.CARD_LT_IMP_LE
unsafe def CARD_LE_RELATIONAL : thm := BBasics.CARD_LE_RELATIONAL
unsafe def CARD_LE_RELATIONAL_FULL : thm := BBasics.CARD_LE_RELATIONAL_FULL
unsafe def CARD_LE_EMPTY : thm := BBasics.CARD_LE_EMPTY
unsafe def CARD_EQ_EMPTY : thm := BBasics.CARD_EQ_EMPTY

-- Order
unsafe def CARD_LE_ANTISYM : thm := BOrder.CARD_LE_ANTISYM
unsafe def CARD_LE_TOTAL : thm := BOrder.CARD_LE_TOTAL
unsafe def CARD_LET_TOTAL : thm := BOrder.CARD_LET_TOTAL
unsafe def CARD_LTE_TOTAL : thm := BOrder.CARD_LTE_TOTAL
unsafe def CARD_LT_TOTAL : thm := BOrder.CARD_LT_TOTAL
unsafe def CARD_NOT_LE : thm := BOrder.CARD_NOT_LE
unsafe def CARD_NOT_LT : thm := BOrder.CARD_NOT_LT
unsafe def CARD_LT_LE : thm := BOrder.CARD_LT_LE
unsafe def CARD_LE_LT : thm := BOrder.CARD_LE_LT
unsafe def CARD_LE_CONG : thm := BOrder.CARD_LE_CONG
unsafe def CARD_LT_CONG : thm := BOrder.CARD_LT_CONG
unsafe def CARD_EQ_TRANS : thm := BOrder.CARD_EQ_TRANS
unsafe def CARD_EQ_CONG : thm := BOrder.CARD_EQ_CONG
unsafe def INFINITE_CARD_LE : thm := BOrder.INFINITE_CARD_LE
unsafe def FINITE_CARD_LT : thm := BOrder.FINITE_CARD_LT
unsafe def CARD_LE_SUBSET : thm := BOrder.CARD_LE_SUBSET
unsafe def CARD_LE_UNIV : thm := BOrder.CARD_LE_UNIV
unsafe def CARD_LE_EQ_SUBSET : thm := BOrder.CARD_LE_EQ_SUBSET
unsafe def CARD_LE_EQ_SUBSET_UNIV : thm := BOrder.CARD_LE_EQ_SUBSET_UNIV
unsafe def CARD_INFINITE_CONG : thm := BOrder.CARD_INFINITE_CONG
unsafe def CARD_FINITE_CONG : thm := BOrder.CARD_FINITE_CONG
unsafe def CARD_LE_FINITE : thm := BOrder.CARD_LE_FINITE
unsafe def CARD_EQ_FINITE : thm := BOrder.CARD_EQ_FINITE
unsafe def CARD_EQ_INFINITE : thm := BOrder.CARD_EQ_INFINITE
unsafe def CARD_LE_INFINITE : thm := BOrder.CARD_LE_INFINITE
unsafe def CARD_LT_FINITE_INFINITE : thm := BOrder.CARD_LT_FINITE_INFINITE
unsafe def CARD_LE_FINITE_INFINITE : thm := BOrder.CARD_LE_FINITE_INFINITE
unsafe def CARD_LE_CARD_IMP : thm := BOrder.CARD_LE_CARD_IMP
unsafe def CARD_EQ_CARD_IMP : thm := BOrder.CARD_EQ_CARD_IMP
unsafe def CARD_LE_CARD : thm := BOrder.CARD_LE_CARD
unsafe def CARD_EQ_CARD : thm := BOrder.CARD_EQ_CARD
unsafe def CARD_LT_CARD : thm := BOrder.CARD_LT_CARD
unsafe def CARD_HAS_SIZE_CONG : thm := BOrder.CARD_HAS_SIZE_CONG
unsafe def NUMSEG_CARD_LE : thm := BOrder.NUMSEG_CARD_LE
unsafe def CARD_LE_IMAGE : thm := BOrder.CARD_LE_IMAGE
unsafe def CARD_LE_IMAGE_GEN : thm := BOrder.CARD_LE_IMAGE_GEN
unsafe def CARD_EQ_IMAGE : thm := BOrder.CARD_EQ_IMAGE
unsafe def CARD_GE_PREIMAGE : thm := BOrder.CARD_GE_PREIMAGE
unsafe def CARD_LE_PREIMAGE : thm := BOrder.CARD_LE_PREIMAGE
unsafe def CARD_EQ_PREIMAGE : thm := BOrder.CARD_EQ_PREIMAGE
unsafe def CARD_LE_IMAGES : thm := BOrder.CARD_LE_IMAGES
unsafe def CARD_EQ_IMAGES : thm := BOrder.CARD_EQ_IMAGES
unsafe def LE_C_IMAGE : thm := BOrder.LE_C_IMAGE
unsafe def LE_C_IMAGE_SUBSET : thm := BOrder.LE_C_IMAGE_SUBSET
unsafe def CARD_LE_SING : thm := BOrder.CARD_LE_SING
unsafe def CARD_SING_LE : thm := BOrder.CARD_SING_LE
unsafe def CARD_EQ_ORDINAL_EXISTS : thm := BOrder.CARD_EQ_ORDINAL_EXISTS
unsafe def WF_CARD_LT : thm := BOrder.WF_CARD_LT

-- Arith
unsafe def add_c : thm := BArith.add_c
unsafe def mul_c : thm := BArith.mul_c
unsafe def CARD_LE_ADD : thm := BArith.CARD_LE_ADD
unsafe def CARD_LE_MUL : thm := BArith.CARD_LE_MUL
unsafe def CARD_FUNSPACE_LE : thm := BArith.CARD_FUNSPACE_LE
unsafe def CARD_ADD_CONG : thm := BArith.CARD_ADD_CONG
unsafe def CARD_MUL_CONG : thm := BArith.CARD_MUL_CONG
unsafe def CARD_FUNSPACE_CONG : thm := BArith.CARD_FUNSPACE_CONG
unsafe def MUL_C_UNIV : thm := BArith.MUL_C_UNIV
unsafe def CARD_FUNSPACE_CURRY : thm := BArith.CARD_FUNSPACE_CURRY
unsafe def IN_CARD_ADD : thm := BArith.IN_CARD_ADD
unsafe def IN_CARD_MUL : thm := BArith.IN_CARD_MUL
unsafe def CARD_LE_SQUARE : thm := BArith.CARD_LE_SQUARE
unsafe def CARD_SQUARE_NUM : thm := BArith.CARD_SQUARE_NUM
unsafe def UNION_LE_ADD_C : thm := BArith.UNION_LE_ADD_C
unsafe def CARD_ADD_C : thm := BArith.CARD_ADD_C
unsafe def CARD_MUL_C : thm := BArith.CARD_MUL_C
unsafe def CARD_ADD_SYM : thm := BArith.CARD_ADD_SYM
unsafe def CARD_ADD_ASSOC : thm := BArith.CARD_ADD_ASSOC
unsafe def CARD_MUL_SYM : thm := BArith.CARD_MUL_SYM
unsafe def CARD_MUL_ASSOC : thm := BArith.CARD_MUL_ASSOC
unsafe def CARD_LDISTRIB : thm := BArith.CARD_LDISTRIB
unsafe def CARD_RDISTRIB : thm := BArith.CARD_RDISTRIB
unsafe def CARD_LE_ADDR : thm := BArith.CARD_LE_ADDR
unsafe def CARD_LE_ADDL : thm := BArith.CARD_LE_ADDL
unsafe def CARD_MUL_LID : thm := BArith.CARD_MUL_LID
unsafe def CARD_MUL_RID : thm := BArith.CARD_MUL_RID
unsafe def CARD_ADD_LE_MUL_INFINITE : thm := BArith.CARD_ADD_LE_MUL_INFINITE
unsafe def CARD_DISJOINT_UNION : thm := BArith.CARD_DISJOINT_UNION
unsafe def CARD_LE_EXISTS : thm := BArith.CARD_LE_EXISTS
unsafe def CARD_LT_IMP_SUC_LE : thm := BArith.CARD_LT_IMP_SUC_LE

-- Square
unsafe def CARD_SQUARE_INFINITE : thm := BSquare.CARD_SQUARE_INFINITE
unsafe def CARD_ADD_FINITE : thm := BSquare.CARD_ADD_FINITE
unsafe def CARD_ADD_FINITE_EQ : thm := BSquare.CARD_ADD_FINITE_EQ
unsafe def CARD_MUL_FINITE : thm := BSquare.CARD_MUL_FINITE
unsafe def CARD_MUL_FINITE_EQ : thm := BSquare.CARD_MUL_FINITE_EQ
unsafe def CARD_MUL_ABSORB_LE : thm := BSquare.CARD_MUL_ABSORB_LE
unsafe def CARD_MUL2_ABSORB_LE : thm := BSquare.CARD_MUL2_ABSORB_LE
unsafe def CARD_MUL2_ABSORB_LE_ALT : thm := BSquare.CARD_MUL2_ABSORB_LE_ALT
unsafe def CARD_ADD_ABSORB_LE : thm := BSquare.CARD_ADD_ABSORB_LE
unsafe def CARD_ADD2_ABSORB_LE : thm := BSquare.CARD_ADD2_ABSORB_LE
unsafe def CARD_MUL_ABSORB : thm := BSquare.CARD_MUL_ABSORB
unsafe def CARD_ADD_ABSORB_LEFT : thm := BSquare.CARD_ADD_ABSORB_LEFT
unsafe def CARD_ADD_ABSORB_RIGHT : thm := BSquare.CARD_ADD_ABSORB_RIGHT
unsafe def CARD_UNION_ABSORB_LEFT : thm := BSquare.CARD_UNION_ABSORB_LEFT
unsafe def CARD_UNION_ABSORB_RIGHT : thm := BSquare.CARD_UNION_ABSORB_RIGHT
unsafe def CARD_ADD2_ABSORB_LT : thm := BSquare.CARD_ADD2_ABSORB_LT
unsafe def CARD_DIFF_ABSORB : thm := BSquare.CARD_DIFF_ABSORB

-- Cancel
unsafe def CARD_LT_ADD : thm := BCancel.CARD_LT_ADD
unsafe def CARD_LE_ADD_LCANCEL : thm := BCancel.CARD_LE_ADD_LCANCEL
unsafe def CARD_LE_ADD_LCANCEL_EQ : thm := BCancel.CARD_LE_ADD_LCANCEL_EQ
unsafe def CARD_LE_ADD_RCANCEL : thm := BCancel.CARD_LE_ADD_RCANCEL
unsafe def CARD_LE_ADD_RCANCEL_EQ : thm := BCancel.CARD_LE_ADD_RCANCEL_EQ
unsafe def CARD_EQ_ADD_LCANCEL : thm := BCancel.CARD_EQ_ADD_LCANCEL
unsafe def CARD_EQ_ADD_LCANCEL_EQ : thm := BCancel.CARD_EQ_ADD_LCANCEL_EQ
unsafe def CARD_EQ_ADD_RCANCEL : thm := BCancel.CARD_EQ_ADD_RCANCEL
unsafe def CARD_EQ_ADD_RCANCEL_EQ : thm := BCancel.CARD_EQ_ADD_RCANCEL_EQ
unsafe def CARD_LE_UNIONS2 : thm := BCancel.CARD_LE_UNIONS2
unsafe def CARD_LE_UNIONS : thm := BCancel.CARD_LE_UNIONS
unsafe def CARD_LE_DISJOINT_UNIONS : thm := BCancel.CARD_LE_DISJOINT_UNIONS
unsafe def CARD_EQ_DISJOINT_UNIONS : thm := BCancel.CARD_EQ_DISJOINT_UNIONS
unsafe def CARD_EQ_IMAGE_MUL_FIBRES : thm := BCancel.CARD_EQ_IMAGE_MUL_FIBRES
unsafe def CARD_DIFF_CONG : thm := BCancel.CARD_DIFF_CONG
unsafe def EQ_C_BIJECTIONS_DISJOINT : thm := BCancel.EQ_C_BIJECTIONS_DISJOINT
unsafe def EQ_C_BIJECTIONS_SUBSETS : thm := BCancel.EQ_C_BIJECTIONS_SUBSETS
unsafe def EQ_C_BIJECTIONS_SUBSETS_LT : thm := BCancel.EQ_C_BIJECTIONS_SUBSETS_LT
unsafe def EQ_C_BIJECTIONS_EXTEND : thm := BCancel.EQ_C_BIJECTIONS_EXTEND
unsafe def EQ_C_INVOLUTION : thm := BCancel.EQ_C_INVOLUTION
unsafe def CARD_MUL_LT_LEMMA : thm := BCancel.CARD_MUL_LT_LEMMA
unsafe def CARD_MUL_LT_INFINITE : thm := BCancel.CARD_MUL_LT_INFINITE

-- Countable
unsafe def CANTOR_THM : thm := BCountable.CANTOR_THM
unsafe def CANTOR_THM_UNIV : thm := BCountable.CANTOR_THM_UNIV
unsafe def NUM_COUNTABLE : thm := BCountable.NUM_COUNTABLE
unsafe def COUNTABLE_ALT : thm := BCountable.COUNTABLE_ALT
unsafe def COUNTABLE_CASES : thm := BCountable.COUNTABLE_CASES
unsafe def CARD_LE_COUNTABLE : thm := BCountable.CARD_LE_COUNTABLE
unsafe def CARD_EQ_COUNTABLE : thm := BCountable.CARD_EQ_COUNTABLE
unsafe def CARD_COUNTABLE_CONG : thm := BCountable.CARD_COUNTABLE_CONG
unsafe def COUNTABLE_SUBSET : thm := BCountable.COUNTABLE_SUBSET
unsafe def COUNTABLE_RESTRICT : thm := BCountable.COUNTABLE_RESTRICT
unsafe def COUNTABLE_SUBSET_NUM : thm := BCountable.COUNTABLE_SUBSET_NUM
unsafe def FINITE_IMP_COUNTABLE : thm := BCountable.FINITE_IMP_COUNTABLE
unsafe def CARD_LE_COUNTABLE_INFINITE : thm := BCountable.CARD_LE_COUNTABLE_INFINITE
unsafe def CARD_LT_COUNTABLE_UNCOUNTABLE : thm := BCountable.CARD_LT_COUNTABLE_UNCOUNTABLE
unsafe def COUNTABLE_IMAGE : thm := BCountable.COUNTABLE_IMAGE
unsafe def COUNTABLE_IMAGE_INJ_GENERAL : thm := BCountable.COUNTABLE_IMAGE_INJ_GENERAL
unsafe def COUNTABLE_IMAGE_INJ_EQ : thm := BCountable.COUNTABLE_IMAGE_INJ_EQ
unsafe def COUNTABLE_IMAGE_INJ : thm := BCountable.COUNTABLE_IMAGE_INJ
unsafe def COUNTABLE_EMPTY : thm := BCountable.COUNTABLE_EMPTY
unsafe def COUNTABLE_INTER : thm := BCountable.COUNTABLE_INTER
unsafe def COUNTABLE_UNION_IMP : thm := BCountable.COUNTABLE_UNION_IMP
unsafe def COUNTABLE_UNION : thm := BCountable.COUNTABLE_UNION
unsafe def COUNTABLE_SING : thm := BCountable.COUNTABLE_SING
unsafe def COUNTABLE_INSERT : thm := BCountable.COUNTABLE_INSERT
unsafe def COUNTABLE_DELETE : thm := BCountable.COUNTABLE_DELETE
unsafe def COUNTABLE_DIFF_FINITE : thm := BCountable.COUNTABLE_DIFF_FINITE
unsafe def COUNTABLE_DIFF : thm := BCountable.COUNTABLE_DIFF
unsafe def COUNTABLE_CROSS : thm := BCountable.COUNTABLE_CROSS
unsafe def COUNTABLE_AS_IMAGE_SUBSET : thm := BCountable.COUNTABLE_AS_IMAGE_SUBSET
unsafe def COUNTABLE_AS_IMAGE_SUBSET_EQ : thm := BCountable.COUNTABLE_AS_IMAGE_SUBSET_EQ
unsafe def COUNTABLE_AS_IMAGE : thm := BCountable.COUNTABLE_AS_IMAGE
unsafe def FORALL_COUNTABLE_AS_IMAGE : thm := BCountable.FORALL_COUNTABLE_AS_IMAGE
unsafe def COUNTABLE_AS_INJECTIVE_IMAGE : thm := BCountable.COUNTABLE_AS_INJECTIVE_IMAGE
unsafe def COUNTABLE_AS_IMAGE_NUM_SUBSET : thm := BCountable.COUNTABLE_AS_IMAGE_NUM_SUBSET
unsafe def COUNTABLE_AS_INJECTIVE_IMAGE_SUBSET : thm := BCountable.COUNTABLE_AS_INJECTIVE_IMAGE_SUBSET
unsafe def COUNTABLE_UNIONS : thm := BCountable.COUNTABLE_UNIONS
unsafe def COUNTABLE_PRODUCT_DEPENDENT : thm := BCountable.COUNTABLE_PRODUCT_DEPENDENT
unsafe def COUNTABLE_CARD_ADD : thm := BCountable.COUNTABLE_CARD_ADD
unsafe def COUNTABLE_CARD_ADD_EQ : thm := BCountable.COUNTABLE_CARD_ADD_EQ
unsafe def COUNTABLE_CARD_MUL : thm := BCountable.COUNTABLE_CARD_MUL
unsafe def COUNTABLE_CARD_MUL_EQ : thm := BCountable.COUNTABLE_CARD_MUL_EQ
unsafe def CARD_EQ_PCROSS : thm := BCountable.CARD_EQ_PCROSS
unsafe def COUNTABLE_PCROSS_EQ : thm := BCountable.COUNTABLE_PCROSS_EQ
unsafe def COUNTABLE_PCROSS : thm := BCountable.COUNTABLE_PCROSS
unsafe def INT_COUNTABLE : thm := BCountable.INT_COUNTABLE
unsafe def CARD_EQ_INT_NUM : thm := BCountable.CARD_EQ_INT_NUM
unsafe def int_INFINITE : thm := BCountable.int_INFINITE

-- UnionOf
unsafe def COUNTABLE_CART : thm := BUnionOf.COUNTABLE_CART
unsafe def EXISTS_COUNTABLE_SUBSET_IMAGE_INJ : thm := BUnionOf.EXISTS_COUNTABLE_SUBSET_IMAGE_INJ
unsafe def FORALL_COUNTABLE_SUBSET_IMAGE_INJ : thm := BUnionOf.FORALL_COUNTABLE_SUBSET_IMAGE_INJ
unsafe def EXISTS_COUNTABLE_SUBSET_IMAGE : thm := BUnionOf.EXISTS_COUNTABLE_SUBSET_IMAGE
unsafe def FORALL_COUNTABLE_SUBSET_IMAGE : thm := BUnionOf.FORALL_COUNTABLE_SUBSET_IMAGE
unsafe def COUNTABLE_SUBSET_IMAGE : thm := BUnionOf.COUNTABLE_SUBSET_IMAGE
unsafe def COUNTABLE_IMAGE_EQ : thm := BUnionOf.COUNTABLE_IMAGE_EQ
unsafe def COUNTABLE_IMAGE_EQ_INJ : thm := BUnionOf.COUNTABLE_IMAGE_EQ_INJ
unsafe def COUNTABLE_FLD : thm := BUnionOf.COUNTABLE_FLD
unsafe def COUNTABLE_UNION_OF_EMPTY : thm := BUnionOf.COUNTABLE_UNION_OF_EMPTY
unsafe def COUNTABLE_INTERSECTION_OF_EMPTY : thm := BUnionOf.COUNTABLE_INTERSECTION_OF_EMPTY
unsafe def COUNTABLE_UNION_OF_INC : thm := BUnionOf.COUNTABLE_UNION_OF_INC
unsafe def COUNTABLE_INTERSECTION_OF_INC : thm := BUnionOf.COUNTABLE_INTERSECTION_OF_INC
unsafe def COUNTABLE_UNION_OF_COMPLEMENT : thm := BUnionOf.COUNTABLE_UNION_OF_COMPLEMENT
unsafe def COUNTABLE_INTERSECTION_OF_COMPLEMENT : thm := BUnionOf.COUNTABLE_INTERSECTION_OF_COMPLEMENT
unsafe def COUNTABLE_UNION_OF_EXPLICIT : thm := BUnionOf.COUNTABLE_UNION_OF_EXPLICIT
unsafe def COUNTABLE_UNION_OF_ASCENDING : thm := BUnionOf.COUNTABLE_UNION_OF_ASCENDING
unsafe def COUNTABLE_UNION_OF_IDEMPOT : thm := BUnionOf.COUNTABLE_UNION_OF_IDEMPOT
unsafe def COUNTABLE_INTERSECTION_OF_IDEMPOT : thm := BUnionOf.COUNTABLE_INTERSECTION_OF_IDEMPOT
unsafe def COUNTABLE_UNION_OF_UNIONS : thm := BUnionOf.COUNTABLE_UNION_OF_UNIONS
unsafe def COUNTABLE_UNION_OF_UNION : thm := BUnionOf.COUNTABLE_UNION_OF_UNION
unsafe def COUNTABLE_INTERSECTION_OF_INTERS : thm := BUnionOf.COUNTABLE_INTERSECTION_OF_INTERS
unsafe def COUNTABLE_INTERSECTION_OF_INTER : thm := BUnionOf.COUNTABLE_INTERSECTION_OF_INTER
unsafe def COUNTABLE_UNION_OF_INTER_EQ : thm := BUnionOf.COUNTABLE_UNION_OF_INTER_EQ
unsafe def COUNTABLE_UNION_OF_INTER : thm := BUnionOf.COUNTABLE_UNION_OF_INTER
unsafe def COUNTABLE_INTERSECTION_OF_UNION_EQ : thm := BUnionOf.COUNTABLE_INTERSECTION_OF_UNION_EQ
unsafe def COUNTABLE_INTERSECTION_OF_UNION : thm := BUnionOf.COUNTABLE_INTERSECTION_OF_UNION
unsafe def COUNTABLE_INTERSECTION_OF_UNIONS_NONEMPTY : thm := BUnionOf.COUNTABLE_INTERSECTION_OF_UNIONS_NONEMPTY
unsafe def COUNTABLE_INTERSECTION_OF_UNIONS : thm := BUnionOf.COUNTABLE_INTERSECTION_OF_UNIONS

-- Reals
unsafe def COUNTABLE_UNION_OF_INTERS_NONEMPTY : thm := BReals.COUNTABLE_UNION_OF_INTERS_NONEMPTY
unsafe def COUNTABLE_UNION_OF_INTERS : thm := BReals.COUNTABLE_UNION_OF_INTERS
unsafe def COUNTABLE_DISJOINT_UNION_OF_IDEMPOT : thm := BReals.COUNTABLE_DISJOINT_UNION_OF_IDEMPOT
unsafe def COUNTABLE_ASCENDING_CHAIN : thm := BReals.COUNTABLE_ASCENDING_CHAIN
unsafe def COUNTABLE_DESCENDING_CHAIN : thm := BReals.COUNTABLE_DESCENDING_CHAIN
unsafe def CARD_EQ_LIST_GEN : thm := BReals.CARD_EQ_LIST_GEN
unsafe def CARD_EQ_LIST : thm := BReals.CARD_EQ_LIST
unsafe def CARD_EQ_CART : thm := BReals.CARD_EQ_CART
unsafe def CARD_EQ_REAL : thm := BReals.CARD_EQ_REAL
unsafe def UNCOUNTABLE_REAL : thm := BReals.UNCOUNTABLE_REAL
unsafe def CARD_EQ_REAL_IMP_UNCOUNTABLE : thm := BReals.CARD_EQ_REAL_IMP_UNCOUNTABLE
unsafe def COUNTABLE_IMP_CARD_LT_REAL : thm := BReals.COUNTABLE_IMP_CARD_LT_REAL
unsafe def CARD_LT_NUM_REAL : thm := BReals.CARD_LT_NUM_REAL
unsafe def CARD_EQ_REAL_SUBSET : thm := BReals.CARD_EQ_REAL_SUBSET

-- Exp
unsafe def exp_c : thm := BExp.exp_c
unsafe def EXP_C : thm := BExp.EXP_C
unsafe def CARD_EXP_UNIV : thm := BExp.CARD_EXP_UNIV
unsafe def CARD_EXP_GRAPH : thm := BExp.CARD_EXP_GRAPH
unsafe def CARD_EXP_GRAPH_PAIRED : thm := BExp.CARD_EXP_GRAPH_PAIRED
unsafe def CARD_EXP_0 : thm := BExp.CARD_EXP_0
unsafe def CARD_EXP_ZERO : thm := BExp.CARD_EXP_ZERO
unsafe def CARD_EXP_ADD : thm := BExp.CARD_EXP_ADD
unsafe def CARD_EXP_MUL : thm := BExp.CARD_EXP_MUL
unsafe def CARD_MUL_EXP : thm := BExp.CARD_MUL_EXP
unsafe def CARD_EXP_SING : thm := BExp.CARD_EXP_SING
unsafe def CARD_LE_EXP_LEFT : thm := BExp.CARD_LE_EXP_LEFT
unsafe def CARD_LE_EXP_RIGHT : thm := BExp.CARD_LE_EXP_RIGHT
unsafe def CARD_LE_EXP : thm := BExp.CARD_LE_EXP
unsafe def CARD_EXP_CONG : thm := BExp.CARD_EXP_CONG
unsafe def CARD_EXP_FINITE : thm := BExp.CARD_EXP_FINITE
unsafe def CARD_EXP_C : thm := BExp.CARD_EXP_C
unsafe def CARD_EXP_POWERSET : thm := BExp.CARD_EXP_POWERSET
unsafe def CARD_EXP_CANTOR : thm := BExp.CARD_EXP_CANTOR
unsafe def CARD_EXP_ABSORB : thm := BExp.CARD_EXP_ABSORB
unsafe def CARD_EXP_LE_REAL : thm := BExp.CARD_EXP_LE_REAL
unsafe def CARD_EXP_EQ_REAL : thm := BExp.CARD_EXP_EQ_REAL

-- Powerset
unsafe def CARD_EQ_RESTRICTED_POWERSET : thm := BPowerset.CARD_EQ_RESTRICTED_POWERSET
unsafe def CARD_EQ_LIMITED_POWERSET : thm := BPowerset.CARD_EQ_LIMITED_POWERSET
unsafe def CARD_EQ_FULLSIZE_POWERSET : thm := BPowerset.CARD_EQ_FULLSIZE_POWERSET
unsafe def CARD_EQ_EXP_INFINITE_FINITE : thm := BPowerset.CARD_EQ_EXP_INFINITE_FINITE
unsafe def CARD_EQ_FINITE_SUBSETS : thm := BPowerset.CARD_EQ_FINITE_SUBSETS
unsafe def CARD_LE_LIST : thm := BPowerset.CARD_LE_LIST
unsafe def CARD_LE_SUBPOWERSET : thm := BPowerset.CARD_LE_SUBPOWERSET
unsafe def CARD_LE_FINITE_SUBSETS : thm := BPowerset.CARD_LE_FINITE_SUBSETS
unsafe def CARD_LE_COUNTABLE_SUBSETS : thm := BPowerset.CARD_LE_COUNTABLE_SUBSETS
unsafe def CARD_LE_POWERSET : thm := BPowerset.CARD_LE_POWERSET
unsafe def CARD_POWERSET_CONG : thm := BPowerset.CARD_POWERSET_CONG
unsafe def COUNTABLE_LIST_GEN : thm := BPowerset.COUNTABLE_LIST_GEN
unsafe def COUNTABLE_LIST : thm := BPowerset.COUNTABLE_LIST
unsafe def COUNTABLE_FINITE_SUBSETS : thm := BPowerset.COUNTABLE_FINITE_SUBSETS
unsafe def CARD_EQ_REAL_SEQUENCES : thm := BPowerset.CARD_EQ_REAL_SEQUENCES
unsafe def CARD_EQ_COUNTABLE_SUBSETS_SUBREAL : thm := BPowerset.CARD_EQ_COUNTABLE_SUBSETS_SUBREAL
unsafe def CARD_EQ_COUNTABLE_SUBSETS_REAL : thm := BPowerset.CARD_EQ_COUNTABLE_SUBSETS_REAL
unsafe def CARD_LE_RESTRICTED_FUNSPACE : thm := BPowerset.CARD_LE_RESTRICTED_FUNSPACE
unsafe def COUNTABLE_RESTRICTED_FUNSPACE : thm := BPowerset.COUNTABLE_RESTRICTED_FUNSPACE
unsafe def CARD_LE_RESTRICTED_FUNSPACE_INFINITE : thm := BPowerset.CARD_LE_RESTRICTED_FUNSPACE_INFINITE
unsafe def CARD_EQ_RESTRICTED_FUNSPACE_INFINITE : thm := BPowerset.CARD_EQ_RESTRICTED_FUNSPACE_INFINITE
unsafe def CARD_EQ_FUNSPACE : thm := BPowerset.CARD_EQ_FUNSPACE

-- Cartesian
unsafe def CARTESIAN_PRODUCT_CONST : thm := BCartesian.CARTESIAN_PRODUCT_CONST
unsafe def CARD_LE_CARTESIAN_PRODUCT : thm := BCartesian.CARD_LE_CARTESIAN_PRODUCT
unsafe def CARD_EQ_CARTESIAN_PRODUCT : thm := BCartesian.CARD_EQ_CARTESIAN_PRODUCT
unsafe def CARD_LE_CARTESIAN_PRODUCT_SUBINDEX : thm := BCartesian.CARD_LE_CARTESIAN_PRODUCT_SUBINDEX
unsafe def FINITE_CARTESIAN_PRODUCT : thm := BCartesian.FINITE_CARTESIAN_PRODUCT
unsafe def COUNTABLE_CARTESIAN_PRODUCT : thm := BCartesian.COUNTABLE_CARTESIAN_PRODUCT
unsafe def CARD_EXP_FINITE_EQ : thm := BCartesian.CARD_EXP_FINITE_EQ
unsafe def CARD_EQ_CARTESIAN_PRODUCT_DISJOINT_UNION : thm := BCartesian.CARD_EQ_CARTESIAN_PRODUCT_DISJOINT_UNION






























-- @@EXPORTS END

/-- `needs "Library/card.ml"`: build every bundle, in file order. -/
unsafe def ensureCard : IO Unit := do
  -- @@ENSURE BEGIN
  let _ ← IO.mkRef BBasics.sum_DISTINCT
  let _ ← IO.mkRef BOrder.CARD_LE_ANTISYM
  let _ ← IO.mkRef BArith.add_c
  let _ ← IO.mkRef BSquare.CARD_SQUARE_INFINITE
  let _ ← IO.mkRef BCancel.CARD_LT_ADD
  let _ ← IO.mkRef BCountable.CANTOR_THM
  let _ ← IO.mkRef BUnionOf.COUNTABLE_CART
  let _ ← IO.mkRef BReals.COUNTABLE_UNION_OF_INTERS_NONEMPTY
  let _ ← IO.mkRef BExp.exp_c
  let _ ← IO.mkRef BPowerset.CARD_EQ_RESTRICTED_POWERSET
  let _ ← IO.mkRef BCartesian.CARTESIAN_PRODUCT_CONST  -- @@ENSURE END
  pure ()

end SessionLibrary.Card
