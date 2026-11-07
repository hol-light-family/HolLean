/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/wo.ml.                                      -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Wo.lean

  The session half of the wo.ml translation: it supplies HolLibrary.Wo's
  dependencies from Session and exports every name under its HOL Light name.
  Importing this module is `needs "Library/wo.ml"`: each bundle is built by
  `initialize` when the module is loaded, in file order, after the whole of
  Session (as HOL Light has loaded all of hol_lib.ml before wo.ml's
  `parse_as_infix`).
-/

import Session
import HolLibrary.Wo

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Wo

/-- The core theorems wo.ml uses. -/
def core1 : HolLibrary.Wo.CoreThms1 where
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
  FORALL_IN_IMAGE_2 := Session.FORALL_IN_IMAGE_2
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
  pairwise := Session.«pairwise»

/-- What wo.ml uses from Session. -/
def deps : HolLibrary.Wo.WoDeps where
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
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in wo.ml order. -/
initialize BDefs : HolLibrary.Wo.Defs ←
  ioB "setupDefs" (HolLibrary.Wo.setupDefs deps).run
initialize BOrders : HolLibrary.Wo.Orders ←
  ioB "setupOrders" (HolLibrary.Wo.setupOrders deps BDefs).run
initialize BSegs : HolLibrary.Wo.Segs ←
  ioB "setupSegs" (HolLibrary.Wo.setupSegs deps BDefs BOrders).run
initialize BInseg : HolLibrary.Wo.Inseg ←
  ioB "setupInseg" (HolLibrary.Wo.setupInseg deps BDefs BOrders BSegs).run
initialize BWellOrder : HolLibrary.Wo.WellOrder ←
  ioB "setupWellOrder" (HolLibrary.Wo.setupWellOrder deps BDefs BOrders BSegs BInseg).run
initialize BZorn : HolLibrary.Wo.Zorn ←
  ioB "setupZorn" (HolLibrary.Wo.setupZorn deps BDefs BOrders BSegs BInseg BWellOrder).run
initialize BTukey : HolLibrary.Wo.Tukey ←
  ioB "setupTukey" (HolLibrary.Wo.setupTukey deps BDefs BOrders BSegs BInseg BWellOrder BZorn).run

-- Defs
def PBETA_TAC : HolCore.Tactics.tactic := fun g => BDefs.PBETA_TAC g
def SUBSET_PRED : thm := BDefs.SUBSET_PRED
def UNIONS_PRED : thm := BDefs.UNIONS_PRED
def fld : thm := BDefs.fld
def IN_FLD : thm := BDefs.IN_FLD
def FLD_EQ_EMPTY : thm := BDefs.FLD_EQ_EMPTY
def FLD_SUBSET : thm := BDefs.FLD_SUBSET
def FINITE_FLD : thm := BDefs.FINITE_FLD
def qoset : thm := BDefs.qoset
def poset : thm := BDefs.poset
def toset : thm := BDefs.toset
def woset : thm := BDefs.woset
def wqoset : thm := BDefs.wqoset
def chain : thm := BDefs.chain
def antichain : thm := BDefs.antichain
def CHAIN : thm := BDefs.CHAIN
def ANTICHAIN : thm := BDefs.ANTICHAIN
def CHAIN_SUBSET : thm := BDefs.CHAIN_SUBSET
def ANTICHAIN_SUBSET : thm := BDefs.ANTICHAIN_SUBSET
def QOSET_REFL : thm := BDefs.QOSET_REFL
def QOSET_TRANS : thm := BDefs.QOSET_TRANS
def QOSET_REFL_EQ : thm := BDefs.QOSET_REFL_EQ
def QOSET_FLDEQ : thm := BDefs.QOSET_FLDEQ
def QOSET_FLD : thm := BDefs.QOSET_FLD
def WOSET_IMP_TOSET : thm := BDefs.WOSET_IMP_TOSET
def WOSET_IMP_POSET : thm := BDefs.WOSET_IMP_POSET
def WOSET_IMP_QOSET : thm := BDefs.WOSET_IMP_QOSET
def TOSET_IMP_POSET : thm := BDefs.TOSET_IMP_POSET
def TOSET_IMP_QOSET : thm := BDefs.TOSET_IMP_QOSET
def POSET_IMP_QOSET : thm := BDefs.POSET_IMP_QOSET
def WQOSET_IMP_QOSET : thm := BDefs.WQOSET_IMP_QOSET

-- Orders
def strictly : thm := BOrders.strictly
def properly : thm := BOrders.properly
def PROPERLY_EQ_STRICTLY : thm := BOrders.PROPERLY_EQ_STRICTLY
def STRICTLY_EQ_PROPERLY : thm := BOrders.STRICTLY_EQ_PROPERLY
def STRICTLY_IMP_PROPERLY : thm := BOrders.STRICTLY_IMP_PROPERLY
def STRICTLY_STRICTLY : thm := BOrders.STRICTLY_STRICTLY
def PROPERLY_PROPERLY : thm := BOrders.PROPERLY_PROPERLY
def STRICTLY_PROPERLY : thm := BOrders.STRICTLY_PROPERLY
def PROPERLY_STRICTLY : thm := BOrders.PROPERLY_STRICTLY
def PROPERLY_MONO : thm := BOrders.PROPERLY_MONO
def POSET_QOSET : thm := BOrders.POSET_QOSET
def TOSET : thm := BOrders.TOSET
def TOSET_POSET : thm := BOrders.TOSET_POSET
def WOSET_TOSET : thm := BOrders.WOSET_TOSET
def WQOSET : thm := BOrders.WQOSET
def WQOSET_QOSET : thm := BOrders.WQOSET_QOSET
def WOSET_POSET : thm := BOrders.WOSET_POSET
def WOSET : thm := BOrders.WOSET
def WOSET_WF : thm := BOrders.WOSET_WF
def WOSET_IMP_WQOSET : thm := BOrders.WOSET_IMP_WQOSET
def WQOSET_SUPERSET : thm := BOrders.WQOSET_SUPERSET
def WQOSET_NOBAD : thm := BOrders.WQOSET_NOBAD
def WQOSET_NOBAD_SUBSEQ : thm := BOrders.WQOSET_NOBAD_SUBSEQ
def WQOSET_ANTICHAIN : thm := BOrders.WQOSET_ANTICHAIN
def WQOSET_IMP_WF : thm := BOrders.WQOSET_IMP_WF
def WQOSET_WF_SUPERSET : thm := BOrders.WQOSET_WF_SUPERSET
def WQOSET_WF_SUPERSET_EQ : thm := BOrders.WQOSET_WF_SUPERSET_EQ
def WOSET_WQOSET : thm := BOrders.WOSET_WQOSET
def FLD_RESTRICT_QOSET : thm := BOrders.FLD_RESTRICT_QOSET
def FLD_RESTRICT_POSET : thm := BOrders.FLD_RESTRICT_POSET
def FLD_RESTRICT_TOSET : thm := BOrders.FLD_RESTRICT_TOSET
def FLD_RESTRICT_WOSET : thm := BOrders.FLD_RESTRICT_WOSET
def FLD_RESTRICT_WQOSET : thm := BOrders.FLD_RESTRICT_WQOSET
def QOSET_RESTRICT : thm := BOrders.QOSET_RESTRICT
def POSET_RESTRICT : thm := BOrders.POSET_RESTRICT
def TOSET_RESTRICT : thm := BOrders.TOSET_RESTRICT
def WOSET_RESTRICT : thm := BOrders.WOSET_RESTRICT
def WQOSET_RESTRICT : thm := BOrders.WQOSET_RESTRICT
def QOSET_MIN : thm := BOrders.QOSET_MIN
def QOSET_MAX : thm := BOrders.QOSET_MAX
def POSET_MIN : thm := BOrders.POSET_MIN
def POSET_MAX : thm := BOrders.POSET_MAX
def TOSET_MIN : thm := BOrders.TOSET_MIN
def TOSET_MAX : thm := BOrders.TOSET_MAX

-- Segs
def FLD_TRIVIAL : thm := BSegs.FLD_TRIVIAL
def WOSET_TRIVIAL : thm := BSegs.WOSET_TRIVIAL
def WQOSET_TRIVIAL : thm := BSegs.WQOSET_TRIVIAL
def TOSET_TRIVIAL : thm := BSegs.TOSET_TRIVIAL
def POSET_TRIVIAL : thm := BSegs.POSET_TRIVIAL
def QOSET_TRIVIAL : thm := BSegs.QOSET_TRIVIAL
def FLD_num : thm := BSegs.FLD_num
def WOSET_num : thm := BSegs.WOSET_num
def WQOSET_num : thm := BSegs.WQOSET_num
def TOSET_num : thm := BSegs.TOSET_num
def POSET_num : thm := BSegs.POSET_num
def QOSET_num : thm := BSegs.QOSET_num
def QOSET_POINTWISE : thm := BSegs.QOSET_POINTWISE
def FLD_POINTWISE : thm := BSegs.FLD_POINTWISE
def WQOSET_POINTWISE : thm := BSegs.WQOSET_POINTWISE
def DICKSON : thm := BSegs.DICKSON
def inseg : thm := BSegs.inseg
def INSEG_ANTISYM : thm := BSegs.INSEG_ANTISYM
def INSEG_REFL : thm := BSegs.INSEG_REFL
def INSEG_TRANS : thm := BSegs.INSEG_TRANS
def linseg : thm := BSegs.linseg
def ordinal : thm := BSegs.ordinal
def POSET_REFL : thm := BSegs.POSET_REFL
def POSET_TRANS : thm := BSegs.POSET_TRANS
def POSET_ANTISYM : thm := BSegs.POSET_ANTISYM
def POSET_FLDEQ : thm := BSegs.POSET_FLDEQ
def WOSET_REFL : thm := BSegs.WOSET_REFL
def WOSET_TRANS : thm := BSegs.WOSET_TRANS
def WOSET_ANTISYM : thm := BSegs.WOSET_ANTISYM
def WOSET_TOTAL : thm := BSegs.WOSET_TOTAL
def WOSET_WELL : thm := BSegs.WOSET_WELL
def WOSET_FLDEQ : thm := BSegs.WOSET_FLDEQ
def WOSET_TRANS_LESS : thm := BSegs.WOSET_TRANS_LESS
def PAIRED_EXT : thm := BSegs.PAIRED_EXT

-- Inseg
def WOSET_TRANS_LE : thm := BInseg.WOSET_TRANS_LE
def WOSET_WELL_CONTRAPOS : thm := BInseg.WOSET_WELL_CONTRAPOS
def WOSET_TOTAL_LE : thm := BInseg.WOSET_TOTAL_LE
def WOSET_TOTAL_LT : thm := BInseg.WOSET_TOTAL_LT
def ORDINAL_IMP_WOSET : thm := BInseg.ORDINAL_IMP_WOSET
def WOSET_FINITE_TOSET : thm := BInseg.WOSET_FINITE_TOSET
def UNION_FLD : thm := BInseg.UNION_FLD
def UNION_INSEG : thm := BInseg.UNION_INSEG
def INSEG_SUBSET : thm := BInseg.INSEG_SUBSET
def INSEG_SUBSET_FLD : thm := BInseg.INSEG_SUBSET_FLD
def INSEG_FLD_SUBSET : thm := BInseg.INSEG_FLD_SUBSET
def INSEG_WOSET : thm := BInseg.INSEG_WOSET
def INSEG_ORDINAL : thm := BInseg.INSEG_ORDINAL
def LINSEG_INSEG : thm := BInseg.LINSEG_INSEG
def LINSEG_WOSET : thm := BInseg.LINSEG_WOSET
def LINSEG_FLD : thm := BInseg.LINSEG_FLD
def INSEG_PROPER_SUBSET : thm := BInseg.INSEG_PROPER_SUBSET
def INSEG_PROPER_SUBSET_FLD : thm := BInseg.INSEG_PROPER_SUBSET_FLD
def INSEG_LINSEG : thm := BInseg.INSEG_LINSEG
def EXTEND_FLD : thm := BInseg.EXTEND_FLD
def EXTEND_INSEG : thm := BInseg.EXTEND_INSEG
def EXTEND_LINSEG : thm := BInseg.EXTEND_LINSEG
def ORDINAL_CHAINED_LEMMA : thm := BInseg.ORDINAL_CHAINED_LEMMA
def ORDINAL_CHAINED : thm := BInseg.ORDINAL_CHAINED
def ORDINAL_FLD_UNIQUE : thm := BInseg.ORDINAL_FLD_UNIQUE
def ORDINAL_FLD_SUBSET : thm := BInseg.ORDINAL_FLD_SUBSET
def ORDINAL_FLD_SUBSET_EQ : thm := BInseg.ORDINAL_FLD_SUBSET_EQ
def FLD_SUC : thm := BInseg.FLD_SUC
def ORDINAL_SUC : thm := BInseg.ORDINAL_SUC

-- WellOrder
def ORDINAL_UNION : thm := BWellOrder.ORDINAL_UNION
def ORDINAL_UNION_LEMMA : thm := BWellOrder.ORDINAL_UNION_LEMMA
def ORDINAL_UP : thm := BWellOrder.ORDINAL_UP
def WO_ORDINAL : thm := BWellOrder.WO_ORDINAL
def FLD_RESTRICT : thm := BWellOrder.FLD_RESTRICT
def WO : thm := BWellOrder.WO
def WF_INSEG_WOSET : thm := BWellOrder.WF_INSEG_WOSET
def WOSET_INSEG_ORDINAL : thm := BWellOrder.WOSET_INSEG_ORDINAL
def SUBWOSET_ISO_INSEG : thm := BWellOrder.SUBWOSET_ISO_INSEG

-- Zorn
def HP : thm := BZorn.HP
def ZL_STRONG : thm := BZorn.ZL_STRONG
def ZL : thm := BZorn.ZL
def KL_POSET_LEMMA : thm := BZorn.KL_POSET_LEMMA
def KL : thm := BZorn.KL
def POSET_RESTRICTED_SUBSET : thm := BZorn.POSET_RESTRICTED_SUBSET
def FLD_RESTRICTED_SUBSET : thm := BZorn.FLD_RESTRICTED_SUBSET
def ZL_SUBSETS : thm := BZorn.ZL_SUBSETS
def ZL_SUBSETS_UNIONS : thm := BZorn.ZL_SUBSETS_UNIONS
def ZL_SUBSETS_UNIONS_NONEMPTY : thm := BZorn.ZL_SUBSETS_UNIONS_NONEMPTY
def ZL_SUBSETS_INTERS_NONEMPTY : thm := BZorn.ZL_SUBSETS_INTERS_NONEMPTY

-- Tukey
def TUKEY : thm := BTukey.TUKEY
def OEP : thm := BTukey.OEP
def TOSET_COFINAL_WOSET : thm := BTukey.TOSET_COFINAL_WOSET
















/-- `needs "Library/wo.ml"`: already done by importing this module. -/
def ensureWo : IO Unit := pure ()

end SessionLibrary.Wo
