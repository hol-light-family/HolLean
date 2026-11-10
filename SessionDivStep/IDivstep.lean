/- ---------------------------------------------------------------------- -/
/- Session wiring for Divstep/idivstep.ml                                   . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionDivStep/IDivstep.lean

  The session half of the idivstep.ml translation: it supplies HolDivStep.IDivstep's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "Divstep/idivstep.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolDivStep.IDivstep
import SessionLibrary.Iter
import SessionLibrary.Integer
import SessionDivStep.Divstep

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionDivStep.IDivstep

/-- The core theorems idivstep.ml uses. -/
def core1 : HolDivStep.IDivstep.CoreThms1 where
  ADD_CLAUSES := Session.ADD_CLAUSES
  AND_FORALL_THM := Session.AND_FORALL_THM
  ARITH := Session.ARITH
  CART_EQ := Session.CART_EQ
  DIMINDEX_2 := Session.DIMINDEX_2
  EL := Session.listDefs.EL
  FINITE_RULES := Session.FINITE_RULES
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  FUN_EQ_THM := Session.FUN_EQ_THM
  HD := Session.listDefs.HD
  IMP_CONJ := Session.IMP_CONJ
  INT_2_DIVIDES_ADD := Session.INT_2_DIVIDES_ADD
  INT_2_DIVIDES_MUL := Session.INT_2_DIVIDES_MUL
  INT_2_DIVIDES_SUB := Session.INT_2_DIVIDES_SUB
  INT_ADD_LDISTRIB := Session.INT_ADD_LDISTRIB
  INT_ADD_REM := Session.INT_ADD_REM
  INT_ADD_RID := Session.INT_ADD_RID
  INT_CONG_DIV2 := Session.INT_CONG_DIV2
  INT_CONG_LREM := Session.INT_CONG_LREM
  INT_CONG_REFL := SessionLibrary.Integer.«INT_CONG_REFL»
  INT_DIVIDES_POW_LE_IMP := SessionLibrary.Integer.«INT_DIVIDES_POW_LE_IMP»
  INT_DIVISION_SIMP := Session.INT_DIVISION_SIMP
  INT_DIV_LNEG := Session.INT_DIV_LNEG
  INT_DIV_LT_EQ := Session.INT_DIV_LT_EQ
  INT_GCD_EQ := SessionLibrary.Integer.«INT_GCD_EQ»
  INT_LE_DIV_EQ := Session.INT_LE_DIV_EQ
  INT_LT_DIV_EQ := Session.INT_LT_DIV_EQ
  INT_MUL_ASSOC := Session.INT_MUL_ASSOC
  INT_MUL_DIV_EQ := Session.INT_MUL_DIV_EQ
  INT_MUL_LID := Session.INT_MUL_LID
  INT_MUL_LZERO := Session.INT_MUL_LZERO
  INT_OF_NUM_SUC := Session.INT_OF_NUM_SUC
  INT_POW := Session.INT_POW
  INT_REM_2_CASES := Session.INT_REM_2_CASES
  INT_REM_2_DIVIDES := Session.INT_REM_2_DIVIDES
  INT_REM_2_NEG := Session.INT_REM_2_NEG
  INT_REM_EQ := Session.INT_REM_EQ
  INT_REM_EQ_0 := Session.INT_REM_EQ_0
  INT_REM_REM := Session.INT_REM_REM
  INT_SUB_LDISTRIB := Session.INT_SUB_LDISTRIB
  INT_SUB_REM := Session.INT_SUB_REM
  IN_SING := Session.IN_SING
  ISUM_CLAUSES := Session.ISUM_CLAUSES
  ITER := SessionLibrary.Iter.«ITER»
  ITER_ADD := SessionLibrary.Iter.«ITER_ADD»
  I_THM := Session.I_THM
  LAMBDA_BETA := Session.LAMBDA_BETA
  LENGTH := Session.listDefs.LENGTH
  LE_REFL := Session.LE_REFL
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NUMSEG_CLAUSES := Session.NUMSEG_CLAUSES
  NUMSEG_SING := Session.NUMSEG_SING
  PAIR_EQ := Session.PAIR_EQ
  REAL_OF_INT_CLAUSES := Session.REAL_OF_INT_CLAUSES
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  SUB_0 := Session.SUB_0
  SWAP_FORALL_THM := Session.SWAP_FORALL_THM
  TL := Session.listDefs.TL
  divstep := SessionDivStep.Divstep.«divstep»
  int_gt := Session.int_gt
  int_of_num_th := Session.int_of_num_th
  o_THM := Session.o_THM
  vector := Session.vector

/-- What idivstep.ml uses from Session. -/
def deps : HolDivStep.IDivstep.IDivstepDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  define s := do ExceptT.mk (Session.define (← HolLight.q s))
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
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
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in idivstep.ml order. -/
initialize BIDivstepDefs : HolDivStep.IDivstep.IDivstepDefs ←
  ioB "setupIDivstepDefs" (HolDivStep.IDivstep.setupIDivstepDefs deps).run
initialize BIDivstepBounds : HolDivStep.IDivstep.IDivstepBounds ←
  ioB "setupIDivstepBounds" (HolDivStep.IDivstep.setupIDivstepBounds deps BIDivstepDefs).run
initialize BIDivstepMat : HolDivStep.IDivstep.IDivstepMat ←
  ioB "setupIDivstepMat" (HolDivStep.IDivstep.setupIDivstepMat deps BIDivstepDefs BIDivstepBounds).run

-- IDivstepDefs
def FORALL_2 : thm := BIDivstepDefs.FORALL_2
def VECTOR_2 : thm := BIDivstepDefs.VECTOR_2
def ISUM_2 : thm := BIDivstepDefs.ISUM_2
def imat_I : thm := BIDivstepDefs.imat_I
def imat_mul : thm := BIDivstepDefs.imat_mul
def imat_vmul : thm := BIDivstepDefs.imat_vmul
def IMAT_I : thm := BIDivstepDefs.IMAT_I
def IMAT_MUL : thm := BIDivstepDefs.IMAT_MUL
def IMAT_MUL_LID : thm := BIDivstepDefs.IMAT_MUL_LID
def IMAT_MUL_ASSOC : thm := BIDivstepDefs.IMAT_MUL_ASSOC
def idivstep : thm := BIDivstepDefs.idivstep
def IDIVSTEP_STAYS_ODD : thm := BIDivstepDefs.IDIVSTEP_STAYS_ODD
def IDIVSTEP_STAYS_ZERO : thm := BIDivstepDefs.IDIVSTEP_STAYS_ZERO
def divstep_d : thm := BIDivstepDefs.divstep_d
def divstep_f : thm := BIDivstepDefs.divstep_f
def divstep_g : thm := BIDivstepDefs.divstep_g
def DIVSTEP_DFG : thm := BIDivstepDefs.DIVSTEP_DFG
def DIVSTEP_D : thm := BIDivstepDefs.DIVSTEP_D
def DIVSTEP_F : thm := BIDivstepDefs.DIVSTEP_F
def DIVSTEP_G : thm := BIDivstepDefs.DIVSTEP_G
def DIVSTEP_DFG_ADD : thm := BIDivstepDefs.DIVSTEP_DFG_ADD

-- IDivstepBounds
def DIVSTEP_D_PARITY : thm := BIDivstepBounds.DIVSTEP_D_PARITY
def DIVSTEP_D_BOUND : thm := BIDivstepBounds.DIVSTEP_D_BOUND
def DIVSTEP_F_ODD : thm := BIDivstepBounds.DIVSTEP_F_ODD
def DIVSTEP_G_ZERO : thm := BIDivstepBounds.DIVSTEP_G_ZERO
def DIVSTEP_FG_GCD : thm := BIDivstepBounds.DIVSTEP_FG_GCD
def DIVSTEP_F_BOUNDS : thm := BIDivstepBounds.DIVSTEP_F_BOUNDS
def DIVSTEP_G_BOUNDS : thm := BIDivstepBounds.DIVSTEP_G_BOUNDS
def DIVSTEP_F_BOUNDS_LT : thm := BIDivstepBounds.DIVSTEP_F_BOUNDS_LT
def DIVSTEP_G_BOUNDS_LT : thm := BIDivstepBounds.DIVSTEP_G_BOUNDS_LT
def ITER_DIVSTEP_INTEGER : thm := BIDivstepBounds.ITER_DIVSTEP_INTEGER

-- IDivstepMat
def divstep_mat : thm := BIDivstepMat.divstep_mat
def DIVSTEP_MAT : thm := BIDivstepMat.DIVSTEP_MAT
def DIVSTEP_MAT_BOUNDS : thm := BIDivstepMat.DIVSTEP_MAT_BOUNDS
def DIVSTEP_MAT_ABS_BOUNDS : thm := BIDivstepMat.DIVSTEP_MAT_ABS_BOUNDS
def DIVSTEP_MAT_ADD : thm := BIDivstepMat.DIVSTEP_MAT_ADD
def DIVSTEP_MAT_DIAGONAL : thm := BIDivstepMat.DIVSTEP_MAT_DIAGONAL
def DIVSTEP_MAT_DIAGONAL_1 : thm := BIDivstepMat.DIVSTEP_MAT_DIAGONAL_1
def DIVSTEP_MAT_DIAGONAL_2 : thm := BIDivstepMat.DIVSTEP_MAT_DIAGONAL_2
def DIVSTEP_CONGRUENCE : thm := BIDivstepMat.DIVSTEP_CONGRUENCE
def DIVSTEP_D_CONGRUENCE : thm := BIDivstepMat.DIVSTEP_D_CONGRUENCE
def DIVSTEP_D_CONGRUENCE_GEN : thm := BIDivstepMat.DIVSTEP_D_CONGRUENCE_GEN
def DIVSTEP_MAT_CONGRUENCE : thm := BIDivstepMat.DIVSTEP_MAT_CONGRUENCE
def DIVSTEP_MAT_CONGRUENCE_GEN : thm := BIDivstepMat.DIVSTEP_MAT_CONGRUENCE_GEN
def DIVSTEP_D_MOD : thm := BIDivstepMat.DIVSTEP_D_MOD
def DIVSTEP_MAT_MOD : thm := BIDivstepMat.DIVSTEP_MAT_MOD
def DIVSTEP_D_NEG : thm := BIDivstepMat.DIVSTEP_D_NEG
def DIVSTEP_MAT_NEG : thm := BIDivstepMat.DIVSTEP_MAT_NEG
def DIVSTEP_F_NEG : thm := BIDivstepMat.DIVSTEP_F_NEG
def DIVSTEP_G_NEG : thm := BIDivstepMat.DIVSTEP_G_NEG
def DIVSTEP_CONGRUENCE_NEG : thm := BIDivstepMat.DIVSTEP_CONGRUENCE_NEG
def hdivstep : thm := BIDivstepMat.hdivstep
def HDIVSTEP_DIVSTEP : thm := BIDivstepMat.HDIVSTEP_DIVSTEP
def HDIVSTEP_IDIVSTEP : thm := BIDivstepMat.HDIVSTEP_IDIVSTEP

/-- `needs "Divstep/idivstep.ml"`: already done by importing this module. -/
def ensureIDivstep : IO Unit := pure ()

end SessionDivStep.IDivstep
