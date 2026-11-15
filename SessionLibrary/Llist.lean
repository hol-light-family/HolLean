/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/llist.ml.                                   -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Llist.lean

  The session half of the llist.ml translation: it supplies
  HolLibrary.Llist's dependencies from Session and SessionLibrary.Iter, and
  exports every name under its HOL Light name.  Importing this module is
  `needs "Library/llist.ml"`.  The bundles are built by `initialize` when
  the module is loaded.
-/

import Session
import HolLibrary.Llist
import SessionLibrary.Iter

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Llist

/-- The core theorems llist.ml uses. -/
def core1 : HolLibrary.Llist.CoreThms1 where
  ADD_CLAUSES := Session.ADD_CLAUSES
  ALL2 := Session.listDefs.ALL2
  APPEND := Session.listDefs.APPEND
  APPEND_NIL := Session.listThms1.APPEND_NIL
  CONS_11 := Session.listThms1.CONS_11
  EL := Session.listDefs.EL
  EL_APPEND := Session.listThms2.EL_APPEND
  EL_LIST_OF_SEQ := Session.listThms2.EL_LIST_OF_SEQ
  EL_MAP := Session.listThms2.EL_MAP
  EQ_IMP := Session.EQ_IMP
  ETA_AX := Session.ETA_AX
  EXISTS_IN_IMAGE := Session.EXISTS_IN_IMAGE
  EXISTS_IN_INSERT := Session.EXISTS_IN_INSERT
  EXTENSION := Session.EXTENSION
  FILTER := Session.listDefs.FILTER
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  FST := Session.FST
  FUN_EQ_THM := Session.FUN_EQ_THM
  HD := Session.listDefs.HD
  IMP_CONJ := Session.IMP_CONJ
  INSERT_UNION_EQ := Session.INSERT_UNION_EQ
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_UNIV := Session.IN_UNIV
  ITER := SessionLibrary.Iter.«ITER»
  ITER_ALT := SessionLibrary.Iter.«ITER_ALT»
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LENGTH := Session.listDefs.LENGTH
  LENGTH_APPEND := Session.listThms1.LENGTH_APPEND
  LENGTH_LIST_OF_SEQ := Session.listThms2.LENGTH_LIST_OF_SEQ
  LENGTH_MAP := Session.listThms1.LENGTH_MAP
  LE_ANTISYM := Session.LE_ANTISYM
  LE_REFL := Session.LE_REFL
  LIST_EQ := Session.listThms1.LIST_EQ
  LIST_OF_SEQ := Session.listThms2.LIST_OF_SEQ
  LT := Session.LT
  LT_0 := Session.LT_0
  LT_NZ := Session.LT_NZ
  LT_REFL := Session.LT_REFL
  LT_SUC := Session.LT_SUC
  MAP := Session.listDefs.MAP
  MAP_ID := Session.listThms2.MAP_ID
  MAP_o := Session.listThms1.MAP_o
  MINIMAL := Session.MINIMAL
  NOT_CONS_NIL := Session.listThms1.NOT_CONS_NIL
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NOT_LT := Session.NOT_LT
  NOT_SUC := Session.NOT_SUC
  PAIR_EQ := Session.PAIR_EQ
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  SELECT_UNIQUE := Session.SELECT_UNIQUE
  SND := Session.SND
  SUBSET := Session.SUBSET
  SUBSET_REFL := Session.SUBSET_REFL
  SUB_0 := Session.SUB_0
  SUB_SUC := Session.SUB_SUC
  SUC_INJ := Session.SUC_INJ
  SUC_SUB1 := Session.SUC_SUB1
  SWAP_FORALL_THM := Session.SWAP_FORALL_THM
  TL := Session.listDefs.TL
  UNION_EMPTY := Session.UNION_EMPTY
  list_CASES := Session.listThms1.list_CASES
  list_of_seq := Session.listDefs.list_of_seq
  num_CASES := Session.num_CASES
  o_ASSOC := Session.o_ASSOC
  o_DEF := Session.o_DEF
  o_THM := Session.o_THM
  option_DISTINCT := Session.indTypesBoot.option_DISTINCT
  option_INDUCT := Session.option_INDUCT
  option_INJ := Session.indTypesBoot.option_INJ
  option_RECURSION := Session.option_RECURSION
  set_of_list := Session.set_of_list

/-- What llist.ml uses from Session. -/
def deps : HolLibrary.Llist.LlistDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  define s := do ExceptT.mk (Session.define (← HolLight.q s))
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  new_recursive_definition ax s := do
    ExceptT.mk (Session.new_recursive_definition ax (← HolLight.q s))
  LIST_INDUCT_TAC := Session.LIST_INDUCT_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  METIS_TAC := Session.METIS_TAC
  ASM_METIS_TAC := Session.ASM_METIS_TAC
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  TAUT t := ExceptT.mk (Session.TAUT t)
  ITAUT t := ExceptT.mk (Session.ITAUT t)
  REAL_ARITH t := ExceptT.mk (Session.REAL_ARITH t)
  REAL_FIELD t := ExceptT.mk (Session.REAL_FIELD t)
  REAL_ARITH_TAC := Session.REAL_ARITH_TAC
  ASM_REAL_ARITH_TAC := Session.ASM_REAL_ARITH_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  INT_ARITH t := ExceptT.mk (Session.INT_ARITH t)
  INT_ARITH_TAC := Session.INT_ARITH_TAC
  ASM_INT_ARITH_TAC := Session.ASM_INT_ARITH_TAC
  INTEGER_RULE t := ExceptT.mk (Session.INTEGER_RULE t)
  INTEGER_TAC := Session.INTEGER_TAC
  NUMBER_RULE := Session.NUMBER_RULE
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  INT_REDUCE_CONV := Session.INT_REDUCE_CONV
  INT_RED_CONV := Session.INT_RED_CONV
  INT_REM_DOWN_CONV := Session.INT_REM_DOWN_CONV
  HAS_SIZE_CONV := Session.HAS_SIZE_CONV
  let_CONV := Session.let_CONV
  num_CONV := Session.num_CONV
  mk_numeral := Session.mk_numeral
  LET_TAC := Session.LET_TAC
  basic_ss := Session.basic_ss
  NUM_SUB_CONV := Session.NUM_SUB_CONV
  REAL_RAT_REDUCE_CONV := Session.REAL_RAT_REDUCE_CONV
  NUM_EQ_CONV := Session.NUM_EQ_CONV
  NUM_DIV_CONV := Session.NUM_DIV_CONV
  EXP_MOD_CONV := Session.EXP_MOD_CONV
  EXPAND_CASES_CONV := Session.EXPAND_CASES_CONV
  define_type s := ExceptT.mk (Session.define_type s)
  new_inductive_definition s := do
    ExceptT.mk (Session.new_inductive_definition (← HolLight.q s))
  get_monotonicity_theorems := Session.get_monotonicity_theorems
  set_monotonicity_theorems := Session.set_monotonicity_theorems
  GEN_BETA_CONV := Session.GEN_BETA_CONV
  SELECT_CONV t := pure (Session.SELECT_CONV t)
  cases s := ExceptT.mk (Session.cases s)
  distinctness s := ExceptT.mk (Session.distinctness s)
  injectivity s := ExceptT.mk (Session.injectivity s)
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in llist.ml order. -/
initialize BLlist01 : HolLibrary.Llist.Llist01 ←
  ioB "setupLlist01" (HolLibrary.Llist.setupLlist01 deps).run
initialize BLlist02 : HolLibrary.Llist.Llist02 ←
  ioB "setupLlist02" (HolLibrary.Llist.setupLlist02 deps BLlist01).run

-- Llist01
def THE : thm := BLlist01.THE
def OPTION_MAP : thm := BLlist01.OPTION_MAP
def option_CASES : thm := BLlist01.option_CASES
def OPTION_MAP_EQ_NONE : thm := BLlist01.OPTION_MAP_EQ_NONE
def OPTION_MAP_EQ_SOME : thm := BLlist01.OPTION_MAP_EQ_SOME
def OPTION_MAP_ID : thm := BLlist01.OPTION_MAP_ID
def OPTION_MAP_o : thm := BLlist01.OPTION_MAP_o
def llist_INDUCT : thm := BLlist01.llist_INDUCT
def llist_RECURSION : thm := BLlist01.llist_RECURSION
def LLIST_OF_LIST_11 : thm := BLlist01.LLIST_OF_LIST_11
def LLIST_OF_SEQ_11 : thm := BLlist01.LLIST_OF_SEQ_11
def LLIST_OF_LIST_NEQ_SEQ : thm := BLlist01.LLIST_OF_LIST_NEQ_SEQ
def LLIST_LIST_OR_SEQ : thm := BLlist01.LLIST_LIST_OR_SEQ
def LLIST_REP_EQ : thm := BLlist01.LLIST_REP_EQ
def LLIST_REP_CASES_TAC : term → HolCore.Tactics.tactic := BLlist01.LLIST_REP_CASES_TAC
def LNIL_DEF : thm := BLlist01.LNIL_DEF
def LCONS_DEF : thm := BLlist01.LCONS_DEF
def LLIST_OF_LIST : thm := BLlist01.LLIST_OF_LIST
def LNTH_DEF : thm := BLlist01.LNTH_DEF
def LNTH : thm := BLlist01.LNTH
def LLIST_EQ : thm := BLlist01.LLIST_EQ
def LLIST_OF_SEQ : thm := BLlist01.LLIST_OF_SEQ
def LLIST_CASES : thm := BLlist01.LLIST_CASES
def NOT_LCONS_LNIL : thm := BLlist01.NOT_LCONS_LNIL
def LCONS_11 : thm := BLlist01.LCONS_11
def LHD_DEF : thm := BLlist01.LHD_DEF
def LHD : thm := BLlist01.LHD
def LTL_DEF : thm := BLlist01.LTL_DEF
def LTL : thm := BLlist01.LTL
def LCONS_LHD_LTL : thm := BLlist01.LCONS_LHD_LTL
def LNTH_NONE_MONO : thm := BLlist01.LNTH_NONE_MONO
def LAPPEND_DEF : thm := BLlist01.LAPPEND_DEF
def LAPPEND : thm := BLlist01.LAPPEND
def LCOREC_DEF : thm := BLlist01.LCOREC_DEF
def LCOREC : thm := BLlist01.LCOREC
def LCOREC_UNIQUE : thm := BLlist01.LCOREC_UNIQUE
def LUNFOLD_DEF : thm := BLlist01.LUNFOLD_DEF
def LUNFOLD : thm := BLlist01.LUNFOLD
def LUNFOLD_UNIQUE : thm := BLlist01.LUNFOLD_UNIQUE
def LLIST_COINDUCT : thm := BLlist01.LLIST_COINDUCT
def LLIST_STRONG_COINDUCT : thm := BLlist01.LLIST_STRONG_COINDUCT
def LLIST_CASES_TAC : term → HolCore.Tactics.tactic := BLlist01.LLIST_CASES_TAC
def LLIST_COINDUCT_UNFOLD_TAC : List thm → HolCore.Tactics.tactic := BLlist01.LLIST_COINDUCT_UNFOLD_TAC
def LLIST_COINDUCT_TAC : HolCore.Tactics.tactic := BLlist01.LLIST_COINDUCT_TAC
def LLIST_BISIM_REFL : thm := BLlist01.LLIST_BISIM_REFL
def LLIST_BISIM_LCONS : thm := BLlist01.LLIST_BISIM_LCONS
def LLIST_BISIM_TAC : HolCore.Tactics.tactic := BLlist01.LLIST_BISIM_TAC
def LNTH_LLIST_OF_LIST : thm := BLlist01.LNTH_LLIST_OF_LIST
def LNTH_LLIST_OF_SEQ : thm := BLlist01.LNTH_LLIST_OF_SEQ
def list_of_llist : thm := BLlist01.list_of_llist
def LFINITE_DEF : thm := BLlist01.LFINITE_DEF
def LFINITE_LCONS : thm := BLlist01.LFINITE_LCONS
def LFINITE_RULES : thm := BLlist01.LFINITE_RULES
def LFINITE_INDUCT : thm := BLlist01.LFINITE_INDUCT
def LFINITE_CASES : thm := BLlist01.LFINITE_CASES
def LFINITE_LTL : thm := BLlist01.LFINITE_LTL
def LFINITE_LLIST_OF_LIST : thm := BLlist01.LFINITE_LLIST_OF_LIST
def NOT_LFINITE_LLIST_OF_SEQ : thm := BLlist01.NOT_LFINITE_LLIST_OF_SEQ
def LFINITE_LNTH : thm := BLlist01.LFINITE_LNTH
def LLIST_OF_LIST_OF_LLIST : thm := BLlist01.LLIST_OF_LIST_OF_LLIST
def NOT_LFINITE_COINDUCT : thm := BLlist01.NOT_LFINITE_COINDUCT
def LLENGTH_DEF : thm := BLlist01.LLENGTH_DEF
def LLENGTH : thm := BLlist01.LLENGTH
def LLENGTH_EQ_NONE : thm := BLlist01.LLENGTH_EQ_NONE
def LLENGTH_LLIST_OF_LIST : thm := BLlist01.LLENGTH_LLIST_OF_LIST
def LMAP_DEF : thm := BLlist01.LMAP_DEF
def LMAP : thm := BLlist01.LMAP
def LMAP_LLIST_OF_LIST : thm := BLlist01.LMAP_LLIST_OF_LIST
def LMAP_LLIST_OF_SEQ : thm := BLlist01.LMAP_LLIST_OF_SEQ
def LMAP_ID : thm := BLlist01.LMAP_ID
def LMAP_o : thm := BLlist01.LMAP_o
def LMAP_EQ_LNIL : thm := BLlist01.LMAP_EQ_LNIL
def LNTH_LMAP : thm := BLlist01.LNTH_LMAP
def LFINITE_LMAP : thm := BLlist01.LFINITE_LMAP
def LLENGTH_LMAP : thm := BLlist01.LLENGTH_LMAP
def LAPPEND_LLIST_OF_LIST : thm := BLlist01.LAPPEND_LLIST_OF_LIST
def LAPPEND_LNIL : thm := BLlist01.LAPPEND_LNIL
def LAPPEND_ASSOC : thm := BLlist01.LAPPEND_ASSOC
def LAPPEND_INFINITE : thm := BLlist01.LAPPEND_INFINITE
def LFINITE_LAPPEND : thm := BLlist01.LFINITE_LAPPEND
def LMAP_LAPPEND : thm := BLlist01.LMAP_LAPPEND
def LNTH_LAPPEND : thm := BLlist01.LNTH_LAPPEND
def LAPPEND_EQ_LNIL : thm := BLlist01.LAPPEND_EQ_LNIL
def LTAKE_DEF : thm := BLlist01.LTAKE_DEF
def LTAKE : thm := BLlist01.LTAKE
def LDROP_DEF : thm := BLlist01.LDROP_DEF
def LDROP_LNIL : thm := BLlist01.LDROP_LNIL
def LDROP : thm := BLlist01.LDROP
def LTAKE_LDROP : thm := BLlist01.LTAKE_LDROP
def LNTH_LDROP : thm := BLlist01.LNTH_LDROP
def LDROP_ADD : thm := BLlist01.LDROP_ADD
def LNTH_LTAKE : thm := BLlist01.LNTH_LTAKE
def LLIST_EQ_LTAKE : thm := BLlist01.LLIST_EQ_LTAKE
def LTAKE_LLIST_OF_SEQ : thm := BLlist01.LTAKE_LLIST_OF_SEQ
def LDROP_LLIST_OF_SEQ : thm := BLlist01.LDROP_LLIST_OF_SEQ
def set_of_llist : thm := BLlist01.set_of_llist
def IN_SET_OF_LLIST : thm := BLlist01.IN_SET_OF_LLIST
def LNTH_LCONS_EXISTS : thm := BLlist01.LNTH_LCONS_EXISTS
def SET_OF_LLIST : thm := BLlist01.SET_OF_LLIST
def SET_OF_LLIST_LLIST_OF_LIST : thm := BLlist01.SET_OF_LLIST_LLIST_OF_LIST
def SET_OF_LLIST_LLIST_OF_SEQ : thm := BLlist01.SET_OF_LLIST_LLIST_OF_SEQ
def SET_OF_LLIST_LMAP : thm := BLlist01.SET_OF_LLIST_LMAP
def SET_OF_LLIST_LAPPEND : thm := BLlist01.SET_OF_LLIST_LAPPEND
def LALL_DEF : thm := BLlist01.LALL_DEF
def LEXISTS_DEF : thm := BLlist01.LEXISTS_DEF
def LALL_SET_OF_LLIST : thm := BLlist01.LALL_SET_OF_LLIST
def LEXISTS_SET_OF_LLIST : thm := BLlist01.LEXISTS_SET_OF_LLIST
def LALL : thm := BLlist01.LALL
def LEXISTS : thm := BLlist01.LEXISTS
def LEXISTS_LALL : thm := BLlist01.LEXISTS_LALL
def LALL_LMAP : thm := BLlist01.LALL_LMAP
def LEXISTS_LMAP : thm := BLlist01.LEXISTS_LMAP
def LALL_COINDUCT : thm := BLlist01.LALL_COINDUCT
def LEXISTS_INDUCT : thm := BLlist01.LEXISTS_INDUCT
def MONO_LALL : thm := BLlist01.MONO_LALL
def MONO_LEXISTS : thm := BLlist01.MONO_LEXISTS
def LFIRST_RULES : thm := BLlist01.LFIRST_RULES
def LFIRST_INDUCT : thm := BLlist01.LFIRST_INDUCT
def LFIRST_CASES : thm := BLlist01.LFIRST_CASES
def LFIRST_UNIQUE : thm := BLlist01.LFIRST_UNIQUE
def LFIRST_EXISTS : thm := BLlist01.LFIRST_EXISTS
def LFIRST_LCONS : thm := BLlist01.LFIRST_LCONS
def LFIRST_SUBSET : thm := BLlist01.LFIRST_SUBSET
def LFIRST_LEXISTS : thm := BLlist01.LFIRST_LEXISTS
def lfirst : thm := BLlist01.lfirst
def LFIRST_LFIRST : thm := BLlist01.LFIRST_LFIRST
def LFIRST_EQ : thm := BLlist01.LFIRST_EQ
def LFIRST_LCONS_P : thm := BLlist01.LFIRST_LCONS_P
def LFIRST_LCONS_NOTP : thm := BLlist01.LFIRST_LCONS_NOTP
def LFILTER_DEF : thm := BLlist01.LFILTER_DEF
def LFILTER_UNFOLD : thm := BLlist01.LFILTER_UNFOLD
def LFILTER : thm := BLlist01.LFILTER
def LFILTER_EQ_LNIL : thm := BLlist01.LFILTER_EQ_LNIL
def LFILTER_LAPPEND : thm := BLlist01.LFILTER_LAPPEND

-- Llist02
def LFILTER_LLIST_OF_LIST : thm := BLlist02.LFILTER_LLIST_OF_LIST
def SET_OF_LLIST_LFILTER : thm := BLlist02.SET_OF_LLIST_LFILTER
def LALL_LFILTER : thm := BLlist02.LALL_LFILTER
def LFILTER_LFILTER : thm := BLlist02.LFILTER_LFILTER
def LFLATTEN_DEF : thm := BLlist02.LFLATTEN_DEF
def LFLATTEN_UNFOLD : thm := BLlist02.LFLATTEN_UNFOLD
def LFLATTEN : thm := BLlist02.LFLATTEN
def LFLATTEN_EQ_LNIL : thm := BLlist02.LFLATTEN_EQ_LNIL
def LFLATTEN_INFINITE : thm := BLlist02.LFLATTEN_INFINITE
def LFLATTEN_LCONS : thm := BLlist02.LFLATTEN_LCONS
def LMAP_LFLATTEN : thm := BLlist02.LMAP_LFLATTEN
def LZIP_DEF : thm := BLlist02.LZIP_DEF
def LZIP : thm := BLlist02.LZIP
def LNTH_LZIP : thm := BLlist02.LNTH_LZIP
def LZIP_LMAP : thm := BLlist02.LZIP_LMAP
def LALL2_DEF : thm := BLlist02.LALL2_DEF
def LALL2 : thm := BLlist02.LALL2
def LALL2_EQ : thm := BLlist02.LALL2_EQ
def LALL2_LNTH : thm := BLlist02.LALL2_LNTH
def LLENGTH_EQ : thm := BLlist02.LLENGTH_EQ
def LALL2_COINDUCT : thm := BLlist02.LALL2_COINDUCT
def MONO_LALL2 : thm := BLlist02.MONO_LALL2
def LPREFIX_DEF : thm := BLlist02.LPREFIX_DEF
def LPREFIX : thm := BLlist02.LPREFIX
def LPREFIX_LAPPEND : thm := BLlist02.LPREFIX_LAPPEND
def LPREFIX_REFL : thm := BLlist02.LPREFIX_REFL
def LPREFIX_TRANS : thm := BLlist02.LPREFIX_TRANS
def LPREFIX_LTAKE : thm := BLlist02.LPREFIX_LTAKE
def LPREFIX_LNTH : thm := BLlist02.LPREFIX_LNTH
def LPREFIX_ANTISYM : thm := BLlist02.LPREFIX_ANTISYM
def LPREFIX_COINDUCT : thm := BLlist02.LPREFIX_COINDUCT
def LLIST_OF_LNTH : thm := BLlist02.LLIST_OF_LNTH
def LPREFIX_CHAIN_LUB : thm := BLlist02.LPREFIX_CHAIN_LUB
def LPREFIX_LTAKE_LUB : thm := BLlist02.LPREFIX_LTAKE_LUB
def LITERATE_DEF : thm := BLlist02.LITERATE_DEF
def LITERATE : thm := BLlist02.LITERATE
def LFINITE_LITERATE : thm := BLlist02.LFINITE_LITERATE
def LMAP_LITERATE : thm := BLlist02.LMAP_LITERATE

/-- `needs "Library/llist.ml"`: already done by importing this module. -/
def ensureLlist : IO Unit := pure ()

end SessionLibrary.Llist
