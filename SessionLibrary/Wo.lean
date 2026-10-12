/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/wo.ml.                                      -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Wo.lean

  The `unsafe` half of the wo.ml translation: it supplies HolLibrary.Wo's
  dependencies from Session, builds each bundle once, in file order, and
  exports every name under its HOL Light name.  `ensureWo` is `needs
  "Library/wo.ml"`.

  The blocks between `@@CORE` and `@@EXPORTS` markers are generated from
  HolLibrary/Wo.lean by tools/wodiff/gen_session.py (bookkeeping only:
  field-by-field copies and accessors).
-/

import Session
import HolLibrary.Wo

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Wo

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨Session.sessionB, Session.sessionC, Session.sessionT⟩

-- @@CORE BEGIN
/-- The core theorems wo.ml uses. -/
unsafe def core1 (_ : Unit) : HolLibrary.Wo.CoreThms1 where
  AND_FORALL_THM := Session.«AND_FORALL_THM»
  COND_ID := Session.«COND_ID»
  CONJ_ASSOC := Session.«CONJ_ASSOC»
  CONTRAPOS_THM := Session.«CONTRAPOS_THM»
  DEPENDENT_CHOICE := Session.«DEPENDENT_CHOICE»
  DISJ_SYM := Session.«DISJ_SYM»
  EQ_IMP := Session.«EQ_IMP»
  ETA_AX := Session.«ETA_AX»
  EXISTS_FINITE_SUBSET_IMAGE := Session.«EXISTS_FINITE_SUBSET_IMAGE»
  EXISTS_IN_IMAGE := Session.«EXISTS_IN_IMAGE»
  EXISTS_IN_INSERT := Session.«EXISTS_IN_INSERT»
  EXISTS_PAIR_THM := Session.«EXISTS_PAIR_THM»
  EXTENSION := Session.«EXTENSION»
  FINITE_CROSS := Session.«FINITE_CROSS»
  FINITE_EMPTY := Session.«FINITE_EMPTY»
  FINITE_IMAGE := Session.«FINITE_IMAGE»
  FINITE_INDUCT_STRONG := Session.«FINITE_INDUCT_STRONG»
  FINITE_NUMSEG_LT := Session.«FINITE_NUMSEG_LT»
  FINITE_SING := Session.«FINITE_SING»
  FINITE_SUBSET := Session.«FINITE_SUBSET»
  FINITE_UNION := Session.«FINITE_UNION»
  FORALL_AND_THM := Session.«FORALL_AND_THM»
  FORALL_IN_IMAGE := Session.«FORALL_IN_IMAGE»
  FORALL_IN_INSERT := Session.«FORALL_IN_INSERT»
  FORALL_PAIR_THM := Session.«FORALL_PAIR_THM»
  FORALL_UNWIND_THM2 := Session.«FORALL_UNWIND_THM2»
  FUN_EQ_THM := Session.«FUN_EQ_THM»
  IMP_CONJ := Session.«IMP_CONJ»
  IMP_CONJ_ALT := Session.«IMP_CONJ_ALT»
  IMP_IMP := Session.«IMP_IMP»
  IN := Session.«IN»
  INFINITE := Session.«INFINITE»
  INFINITE_ENUMERATE_EQ := Session.«INFINITE_ENUMERATE_EQ»
  INFINITE_ENUMERATE_SUBSET := Session.«INFINITE_ENUMERATE_SUBSET»
  INFINITE_IMAGE := Session.«INFINITE_IMAGE»
  INJECTIVE_ALT := Session.«INJECTIVE_ALT»
  INJECTIVE_LEFT_INVERSE := Session.«INJECTIVE_LEFT_INVERSE»
  INSERT_SUBSET := Session.«INSERT_SUBSET»
  IN_CROSS := Session.«IN_CROSS»
  IN_DIFF := Session.«IN_DIFF»
  IN_ELIM_PAIR_THM := Session.«IN_ELIM_PAIR_THM»
  IN_ELIM_THM := Session.«IN_ELIM_THM»
  IN_IMAGE := Session.«IN_IMAGE»
  IN_UNION := Session.«IN_UNION»
  IN_UNIONS := Session.«IN_UNIONS»
  IN_UNIV := Session.«IN_UNIV»
  LEFT_AND_EXISTS_THM := Session.«LEFT_AND_EXISTS_THM»
  LEFT_IMP_EXISTS_THM := Session.«LEFT_IMP_EXISTS_THM»
  LE_CASES := Session.«LE_CASES»
  LE_LT := Session.«LE_LT»
  LT_ADD_RCANCEL := Session.«LT_ADD_RCANCEL»
  LT_CASES := Session.«LT_CASES»
  LT_IMP_LE := Session.«LT_IMP_LE»
  LT_IMP_NE := Session.«LT_IMP_NE»
  LT_LE := Session.«LT_LE»
  LT_SUC_LE := Session.«LT_SUC_LE»
  LT_TRANS := Session.«LT_TRANS»
  MEMBER_NOT_EMPTY := Session.«MEMBER_NOT_EMPTY»
  MONO_AND := Session.«MONO_AND»
  MONO_EXISTS := Session.«MONO_EXISTS»
  MONO_FORALL := Session.«MONO_FORALL»
  MONO_IMP := Session.«MONO_IMP»
  NOT_EXISTS_THM := Session.«NOT_EXISTS_THM»
  NOT_FORALL_THM := Session.«NOT_FORALL_THM»
  NOT_IMP := Session.«NOT_IMP»
  NOT_INSERT_EMPTY := Session.«NOT_INSERT_EMPTY»
  NOT_IN_EMPTY := Session.«NOT_IN_EMPTY»
  OR_EXISTS_THM := Session.«OR_EXISTS_THM»
  PAIRWISE_IMAGE := Session.«PAIRWISE_IMAGE»
  PAIR_EQ := Session.«PAIR_EQ»
  RIGHT_FORALL_IMP_THM := Session.«RIGHT_FORALL_IMP_THM»
  RIGHT_IMP_EXISTS_THM := Session.«RIGHT_IMP_EXISTS_THM»
  SKOLEM_THM := Session.«SKOLEM_THM»
  SUBSET := Session.«SUBSET»
  SUBSET_ANTISYM := Session.«SUBSET_ANTISYM»
  SUBSET_EMPTY := Session.«SUBSET_EMPTY»
  SUBSET_REFL := Session.«SUBSET_REFL»
  SUBSET_TRANS := Session.«SUBSET_TRANS»
  SUBSET_UNIV := Session.«SUBSET_UNIV»
  SWAP_EXISTS_THM := Session.«SWAP_EXISTS_THM»
  SWAP_FORALL_THM := Session.«SWAP_FORALL_THM»
  TRANSITIVE_STEPWISE_LE := Session.«TRANSITIVE_STEPWISE_LE»
  TRANSITIVE_STEPWISE_LT := Session.«TRANSITIVE_STEPWISE_LT»
  UNIONS := Session.«UNIONS»
  UNIONS_GSPEC := Session.«UNIONS_GSPEC»
  UNIV := Session.«UNIV»
  UNWIND_THM2 := Session.«UNWIND_THM2»
  WF := Session.«WF»
  WF_ANTISYM := Session.«WF_ANTISYM»
  WF_DCHAIN := Session.«WF_DCHAIN»
  WF_FINITE := Session.«WF_FINITE»
  WF_IND := Session.«WF_IND»
  WF_REC := Session.«WF_REC»
  WF_REC_EXISTS := Session.«WF_REC_EXISTS»
  WF_SUBSET := Session.«WF_SUBSET»
  WF_num := Session.«WF_num»
  WLOG_LT := Session.«WLOG_LT»
  num_FINITE := Session.«num_FINITE»
  num_INFINITE := Session.«num_INFINITE»
  o_THM := Session.«o_THM»
  pairwise := Session.«pairwise»-- @@CORE END

/-- What wo.ml uses from Session. -/
unsafe def deps (_ : Unit) : HolLibrary.Wo.WoDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  parse_as_infix := Session.parse_as_infix
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  METIS_TAC := Session.METIS_TAC
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  GEN_BETA_CONV := Session.GEN_BETA_CONV
  SELECT_CONV t := pure (Session.SELECT_CONV t)
  core1 := core1 ()

/-- Build a bundle once.  `setup` is a thunk, so that `deps` is not built
    before the bundle is needed.  The whole core library is built first
    (`Session.ensureDefine`): HOL Light has loaded all of hol_lib.ml before
    `needs "Library/wo.ml"`, and Session would otherwise build some core
    layers later, on first use, after wo.ml's `parse_as_infix`. -/
private unsafe def cached {α : Type} [Inhabited α] (r : IO.Ref (Option α)) (name : String)
    (setup : Unit → IO (Except String α)) : α :=
  match unsafeIO (do
    match ← r.get with
    | some d => pure d
    | none => do
      Session.ensureDefine
      match ← setup () with
      | .ok d => do r.set (some d); pure d
      | .error e => panic! s!"{name} failed: {e}") with
  | .ok d => d | _ => panic! s!"SessionLibrary.Wo: {name}"

/- The bundles, in wo.ml order.  Each forces the one before it, so that
   any bundle builds every earlier one first, as HOL Light's load does. -/

-- @@BUNDLES BEGIN
initialize theDefs : IO.Ref (Option HolLibrary.Wo.Defs) ← IO.mkRef none
unsafe def BDefs : HolLibrary.Wo.Defs :=
  cached theDefs "setupDefs" fun _ => do
    (HolLibrary.Wo.setupDefs (deps ())).run

initialize theOrders : IO.Ref (Option HolLibrary.Wo.Orders) ← IO.mkRef none
unsafe def BOrders : HolLibrary.Wo.Orders :=
  cached theOrders "setupOrders" fun _ => do
    let _ ← IO.mkRef BDefs.PBETA_TAC
    (HolLibrary.Wo.setupOrders (deps ()) BDefs).run

initialize theSegs : IO.Ref (Option HolLibrary.Wo.Segs) ← IO.mkRef none
unsafe def BSegs : HolLibrary.Wo.Segs :=
  cached theSegs "setupSegs" fun _ => do
    let _ ← IO.mkRef BOrders.strictly
    (HolLibrary.Wo.setupSegs (deps ()) BDefs BOrders).run

initialize theInseg : IO.Ref (Option HolLibrary.Wo.Inseg) ← IO.mkRef none
unsafe def BInseg : HolLibrary.Wo.Inseg :=
  cached theInseg "setupInseg" fun _ => do
    let _ ← IO.mkRef BSegs.FLD_TRIVIAL
    (HolLibrary.Wo.setupInseg (deps ()) BDefs BOrders BSegs).run

initialize theWellOrder : IO.Ref (Option HolLibrary.Wo.WellOrder) ← IO.mkRef none
unsafe def BWellOrder : HolLibrary.Wo.WellOrder :=
  cached theWellOrder "setupWellOrder" fun _ => do
    let _ ← IO.mkRef BInseg.WOSET_TRANS_LE
    (HolLibrary.Wo.setupWellOrder (deps ()) BDefs BOrders BSegs BInseg).run

initialize theZorn : IO.Ref (Option HolLibrary.Wo.Zorn) ← IO.mkRef none
unsafe def BZorn : HolLibrary.Wo.Zorn :=
  cached theZorn "setupZorn" fun _ => do
    let _ ← IO.mkRef BWellOrder.ORDINAL_UNION
    (HolLibrary.Wo.setupZorn (deps ()) BDefs BOrders BSegs BInseg BWellOrder).run

initialize theTukey : IO.Ref (Option HolLibrary.Wo.Tukey) ← IO.mkRef none
unsafe def BTukey : HolLibrary.Wo.Tukey :=
  cached theTukey "setupTukey" fun _ => do
    let _ ← IO.mkRef BZorn.HP
    (HolLibrary.Wo.setupTukey (deps ()) BDefs BOrders BSegs BInseg BWellOrder BZorn).run

-- @@BUNDLES END

-- @@EXPORTS BEGIN
-- Defs
unsafe def PBETA_TAC : HolCore.Tactics.tactic := fun g => BDefs.PBETA_TAC g
unsafe def SUBSET_PRED : thm := BDefs.SUBSET_PRED
unsafe def UNIONS_PRED : thm := BDefs.UNIONS_PRED
unsafe def fld : thm := BDefs.fld
unsafe def IN_FLD : thm := BDefs.IN_FLD
unsafe def FLD_EQ_EMPTY : thm := BDefs.FLD_EQ_EMPTY
unsafe def FLD_SUBSET : thm := BDefs.FLD_SUBSET
unsafe def FINITE_FLD : thm := BDefs.FINITE_FLD
unsafe def qoset : thm := BDefs.qoset
unsafe def poset : thm := BDefs.poset
unsafe def toset : thm := BDefs.toset
unsafe def woset : thm := BDefs.woset
unsafe def wqoset : thm := BDefs.wqoset
unsafe def chain : thm := BDefs.chain
unsafe def antichain : thm := BDefs.antichain
unsafe def CHAIN : thm := BDefs.CHAIN
unsafe def ANTICHAIN : thm := BDefs.ANTICHAIN
unsafe def CHAIN_SUBSET : thm := BDefs.CHAIN_SUBSET
unsafe def ANTICHAIN_SUBSET : thm := BDefs.ANTICHAIN_SUBSET
unsafe def QOSET_REFL : thm := BDefs.QOSET_REFL
unsafe def QOSET_TRANS : thm := BDefs.QOSET_TRANS
unsafe def QOSET_REFL_EQ : thm := BDefs.QOSET_REFL_EQ
unsafe def QOSET_FLDEQ : thm := BDefs.QOSET_FLDEQ
unsafe def QOSET_FLD : thm := BDefs.QOSET_FLD
unsafe def WOSET_IMP_TOSET : thm := BDefs.WOSET_IMP_TOSET
unsafe def WOSET_IMP_POSET : thm := BDefs.WOSET_IMP_POSET
unsafe def WOSET_IMP_QOSET : thm := BDefs.WOSET_IMP_QOSET
unsafe def TOSET_IMP_POSET : thm := BDefs.TOSET_IMP_POSET
unsafe def TOSET_IMP_QOSET : thm := BDefs.TOSET_IMP_QOSET
unsafe def POSET_IMP_QOSET : thm := BDefs.POSET_IMP_QOSET
unsafe def WQOSET_IMP_QOSET : thm := BDefs.WQOSET_IMP_QOSET

-- Orders
unsafe def strictly : thm := BOrders.strictly
unsafe def properly : thm := BOrders.properly
unsafe def PROPERLY_EQ_STRICTLY : thm := BOrders.PROPERLY_EQ_STRICTLY
unsafe def STRICTLY_EQ_PROPERLY : thm := BOrders.STRICTLY_EQ_PROPERLY
unsafe def STRICTLY_IMP_PROPERLY : thm := BOrders.STRICTLY_IMP_PROPERLY
unsafe def STRICTLY_STRICTLY : thm := BOrders.STRICTLY_STRICTLY
unsafe def PROPERLY_PROPERLY : thm := BOrders.PROPERLY_PROPERLY
unsafe def STRICTLY_PROPERLY : thm := BOrders.STRICTLY_PROPERLY
unsafe def PROPERLY_STRICTLY : thm := BOrders.PROPERLY_STRICTLY
unsafe def PROPERLY_MONO : thm := BOrders.PROPERLY_MONO
unsafe def POSET_QOSET : thm := BOrders.POSET_QOSET
unsafe def TOSET : thm := BOrders.TOSET
unsafe def TOSET_POSET : thm := BOrders.TOSET_POSET
unsafe def WOSET_TOSET : thm := BOrders.WOSET_TOSET
unsafe def WQOSET : thm := BOrders.WQOSET
unsafe def WQOSET_QOSET : thm := BOrders.WQOSET_QOSET
unsafe def WOSET_POSET : thm := BOrders.WOSET_POSET
unsafe def WOSET : thm := BOrders.WOSET
unsafe def WOSET_WF : thm := BOrders.WOSET_WF
unsafe def WOSET_IMP_WQOSET : thm := BOrders.WOSET_IMP_WQOSET
unsafe def WQOSET_SUPERSET : thm := BOrders.WQOSET_SUPERSET
unsafe def WQOSET_NOBAD : thm := BOrders.WQOSET_NOBAD
unsafe def WQOSET_NOBAD_SUBSEQ : thm := BOrders.WQOSET_NOBAD_SUBSEQ
unsafe def WQOSET_ANTICHAIN : thm := BOrders.WQOSET_ANTICHAIN
unsafe def WQOSET_IMP_WF : thm := BOrders.WQOSET_IMP_WF
unsafe def WQOSET_WF_SUPERSET : thm := BOrders.WQOSET_WF_SUPERSET
unsafe def WQOSET_WF_SUPERSET_EQ : thm := BOrders.WQOSET_WF_SUPERSET_EQ
unsafe def WOSET_WQOSET : thm := BOrders.WOSET_WQOSET
unsafe def FLD_RESTRICT_QOSET : thm := BOrders.FLD_RESTRICT_QOSET
unsafe def FLD_RESTRICT_POSET : thm := BOrders.FLD_RESTRICT_POSET
unsafe def FLD_RESTRICT_TOSET : thm := BOrders.FLD_RESTRICT_TOSET
unsafe def FLD_RESTRICT_WOSET : thm := BOrders.FLD_RESTRICT_WOSET
unsafe def FLD_RESTRICT_WQOSET : thm := BOrders.FLD_RESTRICT_WQOSET
unsafe def QOSET_RESTRICT : thm := BOrders.QOSET_RESTRICT
unsafe def POSET_RESTRICT : thm := BOrders.POSET_RESTRICT
unsafe def TOSET_RESTRICT : thm := BOrders.TOSET_RESTRICT
unsafe def WOSET_RESTRICT : thm := BOrders.WOSET_RESTRICT
unsafe def WQOSET_RESTRICT : thm := BOrders.WQOSET_RESTRICT
unsafe def QOSET_MIN : thm := BOrders.QOSET_MIN
unsafe def QOSET_MAX : thm := BOrders.QOSET_MAX
unsafe def POSET_MIN : thm := BOrders.POSET_MIN
unsafe def POSET_MAX : thm := BOrders.POSET_MAX
unsafe def TOSET_MIN : thm := BOrders.TOSET_MIN
unsafe def TOSET_MAX : thm := BOrders.TOSET_MAX

-- Segs
unsafe def FLD_TRIVIAL : thm := BSegs.FLD_TRIVIAL
unsafe def WOSET_TRIVIAL : thm := BSegs.WOSET_TRIVIAL
unsafe def WQOSET_TRIVIAL : thm := BSegs.WQOSET_TRIVIAL
unsafe def TOSET_TRIVIAL : thm := BSegs.TOSET_TRIVIAL
unsafe def POSET_TRIVIAL : thm := BSegs.POSET_TRIVIAL
unsafe def QOSET_TRIVIAL : thm := BSegs.QOSET_TRIVIAL
unsafe def FLD_num : thm := BSegs.FLD_num
unsafe def WOSET_num : thm := BSegs.WOSET_num
unsafe def WQOSET_num : thm := BSegs.WQOSET_num
unsafe def TOSET_num : thm := BSegs.TOSET_num
unsafe def POSET_num : thm := BSegs.POSET_num
unsafe def QOSET_num : thm := BSegs.QOSET_num
unsafe def QOSET_POINTWISE : thm := BSegs.QOSET_POINTWISE
unsafe def FLD_POINTWISE : thm := BSegs.FLD_POINTWISE
unsafe def WQOSET_POINTWISE : thm := BSegs.WQOSET_POINTWISE
unsafe def DICKSON : thm := BSegs.DICKSON
unsafe def inseg : thm := BSegs.inseg
unsafe def INSEG_ANTISYM : thm := BSegs.INSEG_ANTISYM
unsafe def INSEG_REFL : thm := BSegs.INSEG_REFL
unsafe def INSEG_TRANS : thm := BSegs.INSEG_TRANS
unsafe def linseg : thm := BSegs.linseg
unsafe def ordinal : thm := BSegs.ordinal
unsafe def POSET_REFL : thm := BSegs.POSET_REFL
unsafe def POSET_TRANS : thm := BSegs.POSET_TRANS
unsafe def POSET_ANTISYM : thm := BSegs.POSET_ANTISYM
unsafe def POSET_FLDEQ : thm := BSegs.POSET_FLDEQ
unsafe def WOSET_REFL : thm := BSegs.WOSET_REFL
unsafe def WOSET_TRANS : thm := BSegs.WOSET_TRANS
unsafe def WOSET_ANTISYM : thm := BSegs.WOSET_ANTISYM
unsafe def WOSET_TOTAL : thm := BSegs.WOSET_TOTAL
unsafe def WOSET_WELL : thm := BSegs.WOSET_WELL
unsafe def WOSET_FLDEQ : thm := BSegs.WOSET_FLDEQ
unsafe def WOSET_TRANS_LESS : thm := BSegs.WOSET_TRANS_LESS
unsafe def PAIRED_EXT : thm := BSegs.PAIRED_EXT

-- Inseg
unsafe def WOSET_TRANS_LE : thm := BInseg.WOSET_TRANS_LE
unsafe def WOSET_WELL_CONTRAPOS : thm := BInseg.WOSET_WELL_CONTRAPOS
unsafe def WOSET_TOTAL_LE : thm := BInseg.WOSET_TOTAL_LE
unsafe def WOSET_TOTAL_LT : thm := BInseg.WOSET_TOTAL_LT
unsafe def ORDINAL_IMP_WOSET : thm := BInseg.ORDINAL_IMP_WOSET
unsafe def WOSET_FINITE_TOSET : thm := BInseg.WOSET_FINITE_TOSET
unsafe def UNION_FLD : thm := BInseg.UNION_FLD
unsafe def UNION_INSEG : thm := BInseg.UNION_INSEG
unsafe def INSEG_SUBSET : thm := BInseg.INSEG_SUBSET
unsafe def INSEG_SUBSET_FLD : thm := BInseg.INSEG_SUBSET_FLD
unsafe def INSEG_FLD_SUBSET : thm := BInseg.INSEG_FLD_SUBSET
unsafe def INSEG_WOSET : thm := BInseg.INSEG_WOSET
unsafe def INSEG_ORDINAL : thm := BInseg.INSEG_ORDINAL
unsafe def LINSEG_INSEG : thm := BInseg.LINSEG_INSEG
unsafe def LINSEG_WOSET : thm := BInseg.LINSEG_WOSET
unsafe def LINSEG_FLD : thm := BInseg.LINSEG_FLD
unsafe def INSEG_PROPER_SUBSET : thm := BInseg.INSEG_PROPER_SUBSET
unsafe def INSEG_PROPER_SUBSET_FLD : thm := BInseg.INSEG_PROPER_SUBSET_FLD
unsafe def INSEG_LINSEG : thm := BInseg.INSEG_LINSEG
unsafe def EXTEND_FLD : thm := BInseg.EXTEND_FLD
unsafe def EXTEND_INSEG : thm := BInseg.EXTEND_INSEG
unsafe def EXTEND_LINSEG : thm := BInseg.EXTEND_LINSEG
unsafe def ORDINAL_CHAINED_LEMMA : thm := BInseg.ORDINAL_CHAINED_LEMMA
unsafe def ORDINAL_CHAINED : thm := BInseg.ORDINAL_CHAINED
unsafe def ORDINAL_FLD_UNIQUE : thm := BInseg.ORDINAL_FLD_UNIQUE
unsafe def ORDINAL_FLD_SUBSET : thm := BInseg.ORDINAL_FLD_SUBSET
unsafe def ORDINAL_FLD_SUBSET_EQ : thm := BInseg.ORDINAL_FLD_SUBSET_EQ
unsafe def FLD_SUC : thm := BInseg.FLD_SUC
unsafe def ORDINAL_SUC : thm := BInseg.ORDINAL_SUC

-- WellOrder
unsafe def ORDINAL_UNION : thm := BWellOrder.ORDINAL_UNION
unsafe def ORDINAL_UNION_LEMMA : thm := BWellOrder.ORDINAL_UNION_LEMMA
unsafe def ORDINAL_UP : thm := BWellOrder.ORDINAL_UP
unsafe def WO_ORDINAL : thm := BWellOrder.WO_ORDINAL
unsafe def FLD_RESTRICT : thm := BWellOrder.FLD_RESTRICT
unsafe def WO : thm := BWellOrder.WO
unsafe def WF_INSEG_WOSET : thm := BWellOrder.WF_INSEG_WOSET
unsafe def WOSET_INSEG_ORDINAL : thm := BWellOrder.WOSET_INSEG_ORDINAL
unsafe def SUBWOSET_ISO_INSEG : thm := BWellOrder.SUBWOSET_ISO_INSEG

-- Zorn
unsafe def HP : thm := BZorn.HP
unsafe def ZL_STRONG : thm := BZorn.ZL_STRONG
unsafe def ZL : thm := BZorn.ZL
unsafe def KL_POSET_LEMMA : thm := BZorn.KL_POSET_LEMMA
unsafe def KL : thm := BZorn.KL
unsafe def POSET_RESTRICTED_SUBSET : thm := BZorn.POSET_RESTRICTED_SUBSET
unsafe def FLD_RESTRICTED_SUBSET : thm := BZorn.FLD_RESTRICTED_SUBSET
unsafe def ZL_SUBSETS : thm := BZorn.ZL_SUBSETS
unsafe def ZL_SUBSETS_UNIONS : thm := BZorn.ZL_SUBSETS_UNIONS
unsafe def ZL_SUBSETS_UNIONS_NONEMPTY : thm := BZorn.ZL_SUBSETS_UNIONS_NONEMPTY

-- Tukey
unsafe def TUKEY : thm := BTukey.TUKEY
unsafe def OEP : thm := BTukey.OEP
unsafe def TOSET_COFINAL_WOSET : thm := BTukey.TOSET_COFINAL_WOSET
















-- @@EXPORTS END

/-- `needs "Library/wo.ml"`: build every bundle, in file order. -/
unsafe def ensureWo : IO Unit := do
  -- @@ENSURE BEGIN
  let _ ← IO.mkRef BDefs.SUBSET_PRED
  let _ ← IO.mkRef BOrders.strictly
  let _ ← IO.mkRef BSegs.FLD_TRIVIAL
  let _ ← IO.mkRef BInseg.WOSET_TRANS_LE
  let _ ← IO.mkRef BWellOrder.ORDINAL_UNION
  let _ ← IO.mkRef BZorn.HP
  let _ ← IO.mkRef BTukey.TUKEY  -- @@ENSURE END
  pure ()

end SessionLibrary.Wo
