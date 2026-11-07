/- ---------------------------------------------------------------------- -/
/- Session wiring for Multivariate/msum.ml.                               -/
/- ---------------------------------------------------------------------- -/
/- File: SessionMultiLib/MSum.lean

  The session half of the msum.ml translation: it supplies HolMultiLib.MSum's
  dependencies from Session, SessionMultiLib.Vectors and SessionMultiLib.Misc,
  and exports every theorem by name.  Importing this module is
  `needs "Multivariate/msum.ml"`: its own `needs "Multivariate/vectors.ml"` is
  the import below, and each bundle is built by `initialize` when the module
  is loaded, in file order.
-/

import Session
import SessionMultiLib.Vectors
import HolMultiLib.MSum

open HolCore HolCore.Kernel

namespace SessionMultiLib.MSum

open Session in
/-- The core theorems msum.ml uses. -/
def core : HolMultiLib.MSum.CoreThms :=
  { ADD1, ADD_0, ADD_CLAUSES, ADD_SUB, ADD_SUC, ARITH, CARD_NUMSEG, CART_EQ, CART_EQ_FULL,
    CONTRAPOS_THM, DELETE, DE_MORGAN_THM, DIMINDEX_FINITE_PROD, ETA_AX, FINITE_DELETE,
    FINITE_IMAGE, FINITE_INDEX_INRANGE, FINITE_INDUCT_STRONG, FINITE_NUMSEG, FINITE_RULES,
    FINITE_SUBSET, FINITE_UNIONS, FORALL_PAIR_THM, FUN_EQ_THM, IMAGE_CLAUSES, IMP_CONJ,
    IMP_CONJ_ALT, IN_DELETE, IN_ELIM_THM, IN_IMAGE, IN_INSERT, IN_INTER, IN_NUMSEG, IN_UNIONS,
    ITERATE_CLAUSES, ITERATE_REFLECT, LAMBDA_BETA, LE, LT_REFL, MONO_AND, NOT_IN_EMPTY, NOT_LE,
    NOT_LT, NUMSEG_CLAUSES, NUMSEG_EMPTY, NUMSEG_OFFSET_IMAGE, NUMSEG_SING, ONE, REAL_ADD_ASSOC,
    REAL_LE_TRANS, SELECT_UNIQUE, SUBSET, SUC_INJ, SUC_SUB1, SUM_ADD, SUM_ADD_GEN, SUM_ADD_SPLIT,
    SUM_CASES, SUM_CLAUSES, SUM_CLAUSES_LEFT, SUM_COMBINE_L, SUM_COMBINE_R, SUM_CONST,
    SUM_DELETE, SUM_DELTA, SUM_DIFF, SUM_EQ, SUM_EQ_0, SUM_EQ_GENERAL, SUM_EQ_GENERAL_INVERSES,
    SUM_GROUP, SUM_GROUP_RELATION, SUM_IMAGE, SUM_IMAGE_GEN, SUM_INCL_EXCL, SUM_INJECTION,
    SUM_LE, SUM_LMUL, SUM_NEG, SUM_OFFSET, SUM_OFFSET_0, SUM_PAIR, SUM_RESTRICT_SET, SUM_RMUL,
    SUM_SUB, SUM_SUM_PRODUCT, SUM_SUPERSET, SUM_SWAP, SUM_UNION, SUM_UNION_NONZERO, UNIONS_0,
    UNIONS_INSERT, monoidal, neutral, o_DEF, o_THM, support }

open SessionMultiLib.Vectors SessionMultiLib.Misc in
/-- The theorems msum.ml uses from Multivariate/vectors.ml and misc.ml. -/
def vec : HolMultiLib.MSum.VecThms :=
  { COND_COMPONENT, MATRIX_ADD_AC, MATRIX_ADD_ASSOC, MATRIX_ADD_COMPONENT,
    MATRIX_ADD_LDISTRIB, MATRIX_ADD_LID, MATRIX_ADD_RDISTRIB, MATRIX_ADD_RID,
    MATRIX_CMUL_COMPONENT, MATRIX_MUL_LZERO, MATRIX_MUL_RZERO, MATRIX_NEG_0,
    MATRIX_NEG_COMPONENT, MATRIX_NEG_SUB, MATRIX_SUB_COMPONENT, MAT_0_COMPONENT,
    VEC_COMPONENT, VSUM_COMPONENT, VSUM_NORM, VECTORIZE_COMPONENT }

/-- What msum.ml uses from hol.ml's library and from vectors.ml. -/
def deps : HolMultiLib.MSum.MsumDeps where
  new_definition s := do
    let t ← ExceptT.mk (HolCore.Parser.parse_term s)
    ExceptT.mk (Session.new_definition t)
  overload_interface s t := ExceptT.mk (Session.overload_interface s t)
  prioritize_real := Session.prioritize_real
  prioritize_vector := SessionMultiLib.Vectors.prioritize_vector
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  MATRIX_ARITH t := ExceptT.mk (SessionMultiLib.Vectors.MATRIX_ARITH t)
  MATRIX_ARITH_TAC := SessionMultiLib.Vectors.MATRIX_ARITH_TAC
  MESON_TAC := Session.MESON_TAC
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  num_CONV := Session.num_CONV
  core := core
  vec := vec

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in msum.ml order. -/
initialize BMsum1 : HolMultiLib.MSum.Msum1 ←
  ioB "setupMsum1" (HolMultiLib.MSum.setupMsum1 deps).run
initialize BMsum2 : HolMultiLib.MSum.Msum2 ←
  ioB "setupMsum2" (HolMultiLib.MSum.setupMsum2 deps BMsum1).run

-- Msum1 (msum.ml 9-245)
def matrix_norm : thm := BMsum1.matrix_norm
def NEUTRAL_MATRIX_ADD : thm := BMsum1.NEUTRAL_MATRIX_ADD
def MONOIDAL_MATRIX_ADD : thm := BMsum1.MONOIDAL_MATRIX_ADD
def msum : thm := BMsum1.msum
def MSUM_COMPONENT : thm := BMsum1.MSUM_COMPONENT
def MSUM_ROW : thm := BMsum1.MSUM_ROW
def MSUM_CLAUSES : thm := BMsum1.MSUM_CLAUSES
def MSUM : thm := BMsum1.MSUM
def MSUM_EQ_0 : thm := BMsum1.MSUM_EQ_0
def MSUM_0 : thm := BMsum1.MSUM_0
def MSUM_LMUL : thm := BMsum1.MSUM_LMUL
def MSUM_RMUL : thm := BMsum1.MSUM_RMUL
def MSUM_ADD : thm := BMsum1.MSUM_ADD
def MSUM_SUB : thm := BMsum1.MSUM_SUB
def MSUM_CONST : thm := BMsum1.MSUM_CONST
def MSUM_MATRIX_RMUL : thm := BMsum1.MSUM_MATRIX_RMUL
def MSUM_MATRIX_LMUL : thm := BMsum1.MSUM_MATRIX_LMUL
def MSUM_IMAGE : thm := BMsum1.MSUM_IMAGE
def MSUM_UNION : thm := BMsum1.MSUM_UNION
def MSUM_DIFF : thm := BMsum1.MSUM_DIFF
def MSUM_DELETE : thm := BMsum1.MSUM_DELETE
def MSUM_INCL_EXCL : thm := BMsum1.MSUM_INCL_EXCL
def MSUM_NEG : thm := BMsum1.MSUM_NEG
def MSUM_EQ : thm := BMsum1.MSUM_EQ
def MSUM_SUPERSET : thm := BMsum1.MSUM_SUPERSET
def MSUM_SUPPORT_EXPLICIT : thm := BMsum1.MSUM_SUPPORT_EXPLICIT
def MSUM_SUPPORT : thm := BMsum1.MSUM_SUPPORT
def MSUM_UNIV : thm := BMsum1.MSUM_UNIV
def MSUM_EQ_SUPERSET : thm := BMsum1.MSUM_EQ_SUPERSET
def MSUM_UNION_RZERO : thm := BMsum1.MSUM_UNION_RZERO
def MSUM_UNION_LZERO : thm := BMsum1.MSUM_UNION_LZERO
def MSUM_RESTRICT : thm := BMsum1.MSUM_RESTRICT
def MSUM_RESTRICT_SET : thm := BMsum1.MSUM_RESTRICT_SET
def MSUM_CASES : thm := BMsum1.MSUM_CASES
def MSUM_SING : thm := BMsum1.MSUM_SING
def VECTORIZE_MSUM : thm := BMsum1.VECTORIZE_MSUM
def MSUM_NORM : thm := BMsum1.MSUM_NORM
def MSUM_NORM_LE : thm := BMsum1.MSUM_NORM_LE
def MSUM_NORM_TRIANGLE : thm := BMsum1.MSUM_NORM_TRIANGLE
def MSUM_NORM_BOUND : thm := BMsum1.MSUM_NORM_BOUND
-- Msum2 (msum.ml 248-581)
def MSUM_CLAUSES_NUMSEG : thm := BMsum2.MSUM_CLAUSES_NUMSEG
def MSUM_CLAUSES_RIGHT : thm := BMsum2.MSUM_CLAUSES_RIGHT
def MSUM_CMUL_NUMSEG : thm := BMsum2.MSUM_CMUL_NUMSEG
def MSUM_EQ_NUMSEG : thm := BMsum2.MSUM_EQ_NUMSEG
def MSUM_IMAGE_GEN : thm := BMsum2.MSUM_IMAGE_GEN
def MSUM_GROUP : thm := BMsum2.MSUM_GROUP
def MSUM_GROUP_RELATION : thm := BMsum2.MSUM_GROUP_RELATION
def MSUM_VMUL : thm := BMsum2.MSUM_VMUL
def MSUM_DELTA : thm := BMsum2.MSUM_DELTA
def MSUM_ADD_NUMSEG : thm := BMsum2.MSUM_ADD_NUMSEG
def MSUM_SUB_NUMSEG : thm := BMsum2.MSUM_SUB_NUMSEG
def MSUM_ADD_SPLIT : thm := BMsum2.MSUM_ADD_SPLIT
def MSUM_MSUM_PRODUCT : thm := BMsum2.MSUM_MSUM_PRODUCT
def MSUM_IMAGE_NONZERO : thm := BMsum2.MSUM_IMAGE_NONZERO
def MSUM_UNION_NONZERO : thm := BMsum2.MSUM_UNION_NONZERO
def MSUM_UNIONS_NONZERO : thm := BMsum2.MSUM_UNIONS_NONZERO
def MSUM_CLAUSES_LEFT : thm := BMsum2.MSUM_CLAUSES_LEFT
def MSUM_DIFFS : thm := BMsum2.MSUM_DIFFS
def MSUM_DIFFS_ALT : thm := BMsum2.MSUM_DIFFS_ALT
def MSUM_DELETE_CASES : thm := BMsum2.MSUM_DELETE_CASES
def MSUM_EQ_GENERAL : thm := BMsum2.MSUM_EQ_GENERAL
def MSUM_EQ_GENERAL_INVERSES : thm := BMsum2.MSUM_EQ_GENERAL_INVERSES
def MSUM_OFFSET : thm := BMsum2.MSUM_OFFSET
def MSUM_OFFSET_0 : thm := BMsum2.MSUM_OFFSET_0
def MSUM_TRIV_NUMSEG : thm := BMsum2.MSUM_TRIV_NUMSEG
def MSUM_CONST_NUMSEG : thm := BMsum2.MSUM_CONST_NUMSEG
def MSUM_SUC : thm := BMsum2.MSUM_SUC
def MSUM_BIJECTION : thm := BMsum2.MSUM_BIJECTION
def MSUM_PARTIAL_SUC : thm := BMsum2.MSUM_PARTIAL_SUC
def MSUM_PARTIAL_PRE : thm := BMsum2.MSUM_PARTIAL_PRE
def MSUM_COMBINE_L : thm := BMsum2.MSUM_COMBINE_L
def MSUM_COMBINE_R : thm := BMsum2.MSUM_COMBINE_R
def MSUM_INJECTION : thm := BMsum2.MSUM_INJECTION
def MSUM_SWAP : thm := BMsum2.MSUM_SWAP
def MSUM_SWAP_NUMSEG : thm := BMsum2.MSUM_SWAP_NUMSEG
def MSUM_ADD_GEN : thm := BMsum2.MSUM_ADD_GEN
def MSUM_CASES_1 : thm := BMsum2.MSUM_CASES_1
def MSUM_SING_NUMSEG : thm := BMsum2.MSUM_SING_NUMSEG
def MSUM_1 : thm := BMsum2.MSUM_1
def MSUM_2 : thm := BMsum2.MSUM_2
def MSUM_3 : thm := BMsum2.MSUM_3
def MSUM_4 : thm := BMsum2.MSUM_4
def MSUM_PAIR : thm := BMsum2.MSUM_PAIR
def MSUM_PAIR_0 : thm := BMsum2.MSUM_PAIR_0
def MSUM_REFLECT : thm := BMsum2.MSUM_REFLECT

/-- `needs "Multivariate/msum.ml"`: already done by importing this module. -/
def ensureMsum : IO Unit := pure ()

end SessionMultiLib.MSum
