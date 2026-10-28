/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/frag.ml.                                    -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Frag.lean

  The session half of the frag.ml translation: it supplies
  HolLibrary.Frag's dependencies from Session and exports every name under
  its HOL Light name.  Importing this module is `needs "Library/frag.ml"`:
  the bundle is built by `initialize` when the module is loaded.
-/

import Session
import HolLibrary.Frag

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Frag

/-- The core theorems frag.ml uses. -/
def core1 : HolLibrary.Frag.CoreThms1 where
  AND_FORALL_THM := Session.AND_FORALL_THM
  BETA_THM := Session.BETA_THM
  COND_RAND := Session.COND_RAND
  COND_RATOR := Session.COND_RATOR
  CONJ_ASSOC := Session.CONJ_ASSOC
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  EMPTY_GSPEC := Session.EMPTY_GSPEC
  EMPTY_SUBSET := Session.EMPTY_SUBSET
  ETA_AX := Session.ETA_AX
  EXTENSION := Session.EXTENSION
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_SING := Session.FINITE_SING
  FINITE_SUBSET := Session.FINITE_SUBSET
  FINITE_UNION := Session.FINITE_UNION
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FUN_EQ_THM := Session.FUN_EQ_THM
  IMAGE_CLAUSES := Session.IMAGE_CLAUSES
  IMAGE_SUBSET := Session.IMAGE_SUBSET
  IMP_CONJ := Session.IMP_CONJ
  IMP_CONJ_ALT := Session.IMP_CONJ_ALT
  INSERT_SUBSET := Session.INSERT_SUBSET
  INT_ADD_LID := Session.INT_ADD_LID
  INT_ENTIRE := Session.INT_ENTIRE
  INT_FORALL_POS := Session.INT_FORALL_POS
  INT_MUL_LZERO := Session.INT_MUL_LZERO
  INT_MUL_RZERO := Session.INT_MUL_RZERO
  INT_NEG_EQ_0 := Session.INT_NEG_EQ_0
  INT_OF_NUM_SUC := Session.INT_OF_NUM_SUC
  INT_SUB_RZERO := Session.INT_SUB_RZERO
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_INSERT := Session.IN_INSERT
  IN_UNION := Session.IN_UNION
  IN_UNIV := Session.IN_UNIV
/-- The core theorems frag.ml uses. -/
def core2 : HolLibrary.Frag.CoreThms2 where
  ITERATE_CLAUSES := Session.ITERATE_CLAUSES
  ITERATE_EQ := Session.ITERATE_EQ
  ITERATE_EQ_NEUTRAL := Session.ITERATE_EQ_NEUTRAL
  ITERATE_EXPAND_CASES := Session.ITERATE_EXPAND_CASES
  ITERATE_OP_GEN := Session.ITERATE_OP_GEN
  ITERATE_UNIV := Session.ITERATE_UNIV
  I_THM := Session.I_THM
  LEFT_OR_FORALL_THM := Session.LEFT_OR_FORALL_THM
  MONO_FORALL := Session.MONO_FORALL
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RIGHT_OR_FORALL_THM := Session.RIGHT_OR_FORALL_THM
  SIMPLE_IMAGE := Session.SIMPLE_IMAGE
  SING_GSPEC := Session.SING_GSPEC
  SUBSET := Session.SUBSET
  SUBSET_TRANS := Session.SUBSET_TRANS
  SUBSET_UNIONS := Session.SUBSET_UNIONS
  SUBSET_UNIV := Session.SUBSET_UNIV
  SUPPORT_SUBSET := Session.SUPPORT_SUBSET
  SWAP_FORALL_THM := Session.SWAP_FORALL_THM
  UNIONS_MONO_IMAGE := Session.UNIONS_MONO_IMAGE
  UNIONS_SUBSET := Session.UNIONS_SUBSET
  monoidal := Session.monoidal
  neutral := Session.neutral
  o_THM := Session.o_THM
  support := Session.support

/-- What frag.ml uses from Session. -/
def deps : HolLibrary.Frag.FragDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  new_type_definition ty names th :=
    ExceptT.mk (Session.new_type_definition ty names.1 names.2 th)
  INT_ARITH t := ExceptT.mk (Session.INT_ARITH t)
  INT_ARITH_TAC := Session.INT_ARITH_TAC
  INT_RING t := ExceptT.mk (Session.INT_RING t)
  INT_REDUCE_CONV := Session.INT_REDUCE_CONV
  INDUCT_TAC := Session.INDUCT_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  core1 := core1
  core2 := core2

/-- frag.ml, run when this module is loaded. -/
initialize BFrag : HolLibrary.Frag.Frag ← do
  match ← (HolLibrary.Frag.setupFrag deps).run with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"setupFrag failed: {e}")

-- Frag
def frag_tybij : thm := BFrag.frag_tybij
def frag_support : thm := BFrag.frag_support
def frag_0 : thm := BFrag.frag_0
def frag_of : thm := BFrag.frag_of
def frag_neg : thm := BFrag.frag_neg
def frag_cmul : thm := BFrag.frag_cmul
def frag_add : thm := BFrag.frag_add
def frag_sub : thm := BFrag.frag_sub
def FRAG_EQ : thm := BFrag.FRAG_EQ
def DEST_FRAG_0 : thm := BFrag.DEST_FRAG_0
def DEST_FRAG_OF : thm := BFrag.DEST_FRAG_OF
def DEST_FRAG_NEG : thm := BFrag.DEST_FRAG_NEG
def DEST_FRAG_CMUL : thm := BFrag.DEST_FRAG_CMUL
def DEST_FRAG_ADD : thm := BFrag.DEST_FRAG_ADD
def DEST_FRAG_SUB : thm := BFrag.DEST_FRAG_SUB
def FRAG_OF_NONZERO : thm := BFrag.FRAG_OF_NONZERO
def FRAG_MODULE : term → IO (Except String thm) := fun t => (BFrag.FRAG_MODULE t).run
def FINITE_FRAG_SUPPORT : thm := BFrag.FINITE_FRAG_SUPPORT
def FRAG_SUPPORT_0 : thm := BFrag.FRAG_SUPPORT_0
def FRAG_SUPPORT_OF : thm := BFrag.FRAG_SUPPORT_OF
def FRAG_SUPPORT_NEG : thm := BFrag.FRAG_SUPPORT_NEG
def FRAG_SUPPORT_CMUL : thm := BFrag.FRAG_SUPPORT_CMUL
def FRAG_SUPPORT_ADD : thm := BFrag.FRAG_SUPPORT_ADD
def FRAG_SUPPORT_SUB : thm := BFrag.FRAG_SUPPORT_SUB
def FRAG_SUPPORT_EQ_EMPTY : thm := BFrag.FRAG_SUPPORT_EQ_EMPTY
def FRAG_OF_EQ : thm := BFrag.FRAG_OF_EQ
def FRAG_ADD_EQ_0 : thm := BFrag.FRAG_ADD_EQ_0
def NEUTRAL_FRAG_ADD : thm := BFrag.NEUTRAL_FRAG_ADD
def MONOIDAL_FRAG_ADD : thm := BFrag.MONOIDAL_FRAG_ADD
def FRAG_CMUL_SUM : thm := BFrag.FRAG_CMUL_SUM
def FRAG_SUPPORT_SUM : thm := BFrag.FRAG_SUPPORT_SUM
def frag_extend : thm := BFrag.frag_extend
def FRAG_EXTEND : thm := BFrag.FRAG_EXTEND
def FRAG_EXTEND_0 : thm := BFrag.FRAG_EXTEND_0
def FRAG_EXTEND_OF : thm := BFrag.FRAG_EXTEND_OF
def FRAG_EXTEND_CMUL : thm := BFrag.FRAG_EXTEND_CMUL
def FRAG_EXTEND_NEG : thm := BFrag.FRAG_EXTEND_NEG
def FRAG_EXTEND_ADD : thm := BFrag.FRAG_EXTEND_ADD
def FRAG_EXTEND_SUB : thm := BFrag.FRAG_EXTEND_SUB
def FRAG_EXTEND_SUM : thm := BFrag.FRAG_EXTEND_SUM
def FRAG_EXTEND_EQ : thm := BFrag.FRAG_EXTEND_EQ
def FRAG_EXTEND_EQ_0 : thm := BFrag.FRAG_EXTEND_EQ_0
def FRAG_SUPPORT_FRAG_EXTEND : thm := BFrag.FRAG_SUPPORT_FRAG_EXTEND
def FRAG_EXPANSION : thm := BFrag.FRAG_EXPANSION
def FRAG_CLOSURE_SUB_CMUL : thm := BFrag.FRAG_CLOSURE_SUB_CMUL
def FRAG_INDUCTION : thm := BFrag.FRAG_INDUCTION
def FRAG_EXTEND_COMPOSE : thm := BFrag.FRAG_EXTEND_COMPOSE
def FRAG_SPLIT : thm := BFrag.FRAG_SPLIT





/-- `needs "Library/frag.ml"`: already done by importing this module. -/
def ensureFrag : IO Unit := pure ()

end SessionLibrary.Frag
