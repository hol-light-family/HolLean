/- ---------------------------------------------------------------------- -/
/- Session wiring for Multivariate/complexes.ml.                          -/
/- ---------------------------------------------------------------------- -/
/- File: SessionMultiLib/Complexes.lean

  The session half of the complexes.ml translation: it supplies
  HolMultiLib.Complexes's dependencies (convex.ml's `ConvexDeps`, the extra
  theorems from Session and SessionMultiLib, and the procedures), and
  exports every theorem and procedure by name.  Importing this module is
  `needs "Multivariate/complexes.ml"`: its own `needs` is the import of
  SessionMultiLib.Convex, and each bundle is built by `initialize` when the
  module is loaded, in file order.
-/

import SessionMultiLib.Convex
import HolMultiLib.Complexes

open HolCore HolCore.Kernel

namespace SessionMultiLib.Complexes

open Session SessionMultiLib.Vectors SessionMultiLib.Determinants
  SessionMultiLib.Topology in
/-- The theorems complexes.ml uses that convex.ml's deps do not carry. -/
def cpx : HolMultiLib.Complexes.CpxThms :=
  { ADD_CLAUSES, EQ_ADD_RCANCEL, EVEN, INFINITE, ITERATE_CLAUSES, ITERATE_EQ,
    ITERATE_EQ_NEUTRAL, ITERATE_IMAGE, ITERATE_PAIR, ITERATE_REFLECT, ITERATE_SUPERSET,
    ITERATE_UNION, LE_0, NOT_SUC, NUMSEG_LREC, NUMSEG_RREC, POW_2_SQRT_ABS, PRODUCT_CLAUSES,
    REAL_ABS_ZERO, REAL_ADD_SUB, REAL_DIFFSQ, REAL_LE_LCANCEL_IMP, REAL_LE_SQUARE,
    REAL_LE_SUB_RADD, REAL_LT_RMUL_EQ, REAL_MUL_RINV_UNIQ, REAL_POW_1, REAL_POW_ADD,
    REAL_POW_EQ_1, REAL_POW_MONO, REAL_SGN_DIV, REAL_SOS_EQ_0, REAL_SUB_LZERO, SELECT_UNIQUE,
    SQRT_MONO_LE, SQRT_MONO_LT, SQRT_POS_LT, SUB_0, SUB_ADD, SUB_REFL, SUC_SUB1, SUM_SUBSET,
    monoidal, neutral, num_WF, real_sgn, real_sub,
    DET_2, ORTHOGONAL_MATRIX_2, EVENTUALLY_AT_INFINITY,
    EUCLIDEAN_SPACE_INFINITE, FORALL_2, L1_LE_NORM, MATRIX_COMPONENT, MATRIX_VECTOR_MUL,
    MATRIX_VECTOR_MUL_COMPONENT, SUM_2, VECTOR_2, VSUM_CLAUSES_LEFT, VSUM_COMPONENT,
    VSUM_CONST_NUMSEG, VSUM_DIFFS_ALT, VSUM_EQ_GENERAL_INVERSES, VSUM_EQ_NUMSEG, VSUM_NORM,
    VSUM_OFFSET_0, VSUM_SUB_NUMSEG, VSUM_TRIV_NUMSEG, VSUM_VSUM_PRODUCT, matrix, vector_norm,
    convex := SessionMultiLib.Convex.convex }

def deps : HolMultiLib.Complexes.ComplexesDeps where
  cvx := SessionMultiLib.Convex.deps
  define s := do
    let t ← ExceptT.mk (HolCore.Parser.parse_term s)
    ExceptT.mk (Session.define t)
  new_type_abbrev := Session.new_type_abbrev
  overload_interface s t := ExceptT.mk (Session.overload_interface s t)
  extend_basic_congs := Session.extend_basic_congs
  REAL_RAT_ADD_CONV := Session.REAL_RAT_ADD_CONV
  REAL_RAT_EQ_CONV := Session.REAL_RAT_EQ_CONV
  REAL_RAT_INV_CONV := Session.REAL_RAT_INV_CONV
  REAL_RAT_MUL_CONV := Session.REAL_RAT_MUL_CONV
  NNF_CONV := Session.NNF_CONV
  NNFC_CONV := Session.NNFC_CONV
  PRENEX_CONV := Session.PRENEX_CONV
  WEAK_CNF_CONV := Session.WEAK_CNF_CONV
  CONJ_CANON_CONV := Session.CONJ_CANON_CONV
  CONDS_CELIM_CONV := Session.CONDS_CELIM_CONV
  ratSyntax := Session.RSyn
  SEMIRING_NORMALIZERS_CONV sth rth isc addc mulc powc ord := do
    let sctx ← HolMath.Normalizer.setupSemiringCtx Session.TRUTH Session.NmzP.2 sth rth isc
      addc mulc powc ord
    pure (HolMath.Normalizer.SEMIRING_NORMALIZERS_CONV sctx Session.NUM_ADD_CONV
      Session.NUM_SUC_CONV Session.NUM_MULT_CONV Session.num_CONV)
  RING_AND_IDEAL_CONV K := do
    let R ← HolMath.Grobner.setupRingCtx Session.GrG Session.Nm.numK (concl Session.TRUTH)
      Session.PRESIMP_CONV Session.CONDS_ELIM_CONV Session.NNF_CONV Session.WEAK_DNF_CONV
      Session.T.AND_FORALL_THM Session.T.LEFT_AND_FORALL_THM Session.T.RIGHT_AND_FORALL_THM
      Session.C.LEFT_OR_FORALL_THM Session.C.RIGHT_OR_FORALL_THM Session.T.OR_EXISTS_THM
      Session.T.LEFT_OR_EXISTS_THM Session.T.RIGHT_OR_EXISTS_THM
      Session.T.LEFT_AND_EXISTS_THM Session.T.RIGHT_AND_EXISTS_THM K
    pure (HolMath.Grobner.RING' R, HolMath.Grobner.ideal_cofactors R)
  cpx := cpx

private def ioB {α : Type} (name : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in complexes.ml order. -/

initialize BCXA : HolMultiLib.Complexes.CXA ←
  ioB "setupCXA" (HolMultiLib.Complexes.setupCXA deps).run

-- CXA (complexes.ml 10-139)
/-- `prioritize_complex()` (complexes.ml 12). -/
def prioritize_complex : ExceptT String IO Unit := BCXA.prioritize_complex
def RE_DEF : thm := BCXA.RE_DEF
def IM_DEF : thm := BCXA.IM_DEF
def complex : thm := BCXA.complex
def CX_DEF : thm := BCXA.CX_DEF
def ii : thm := BCXA.ii
def complex_mul : thm := BCXA.complex_mul
def complex_inv : thm := BCXA.complex_inv
def complex_div : thm := BCXA.complex_div
def complex_pow : thm := BCXA.complex_pow
def RE : thm := BCXA.RE
def IM : thm := BCXA.IM
def COMPLEX_EQ : thm := BCXA.COMPLEX_EQ
def COMPLEX : thm := BCXA.COMPLEX
def COMPLEX_EQ_0 : thm := BCXA.COMPLEX_EQ_0
def FORALL_COMPLEX : thm := BCXA.FORALL_COMPLEX
def EXISTS_COMPLEX : thm := BCXA.EXISTS_COMPLEX
def complex_neg : thm := BCXA.complex_neg
def complex_add : thm := BCXA.complex_add
def complex_sub : thm := BCXA.complex_sub
def complex_norm : thm := BCXA.complex_norm
def COMPLEX_SQNORM : thm := BCXA.COMPLEX_SQNORM
/-- `SIMPLE_COMPLEX_ARITH_TAC` (complexes.ml 132). -/
def SIMPLE_COMPLEX_ARITH_TAC : HolCore.Tactics.tactic := fun g => BCXA.SIMPLE_COMPLEX_ARITH_TAC g
/-- `SIMPLE_COMPLEX_ARITH tm` (complexes.ml 138). -/
def SIMPLE_COMPLEX_ARITH : term → IO (Except String thm) := fun t =>
  (BCXA.SIMPLE_COMPLEX_ARITH t).run

initialize BCXB : HolMultiLib.Complexes.CXB ←
  ioB "setupCXB" (HolMultiLib.Complexes.setupCXB BCXA).run

-- CXB (complexes.ml 141-367)
def COMPLEX_ADD_SYM : thm := BCXB.COMPLEX_ADD_SYM
def COMPLEX_ADD_ASSOC : thm := BCXB.COMPLEX_ADD_ASSOC
def COMPLEX_ADD_LID : thm := BCXB.COMPLEX_ADD_LID
def COMPLEX_ADD_LINV : thm := BCXB.COMPLEX_ADD_LINV
def COMPLEX_MUL_SYM : thm := BCXB.COMPLEX_MUL_SYM
def COMPLEX_MUL_ASSOC : thm := BCXB.COMPLEX_MUL_ASSOC
def COMPLEX_MUL_LID : thm := BCXB.COMPLEX_MUL_LID
def COMPLEX_ADD_LDISTRIB : thm := BCXB.COMPLEX_ADD_LDISTRIB
def COMPLEX_ADD_AC : thm := BCXB.COMPLEX_ADD_AC
def COMPLEX_MUL_AC : thm := BCXB.COMPLEX_MUL_AC
def COMPLEX_ADD_RID : thm := BCXB.COMPLEX_ADD_RID
def COMPLEX_MUL_RID : thm := BCXB.COMPLEX_MUL_RID
def COMPLEX_ADD_RINV : thm := BCXB.COMPLEX_ADD_RINV
def COMPLEX_ADD_RDISTRIB : thm := BCXB.COMPLEX_ADD_RDISTRIB
def COMPLEX_EQ_ADD_LCANCEL : thm := BCXB.COMPLEX_EQ_ADD_LCANCEL
def COMPLEX_EQ_ADD_RCANCEL : thm := BCXB.COMPLEX_EQ_ADD_RCANCEL
def COMPLEX_MUL_RZERO : thm := BCXB.COMPLEX_MUL_RZERO
def COMPLEX_MUL_LZERO : thm := BCXB.COMPLEX_MUL_LZERO
def COMPLEX_NEG_NEG : thm := BCXB.COMPLEX_NEG_NEG
def COMPLEX_MUL_RNEG : thm := BCXB.COMPLEX_MUL_RNEG
def COMPLEX_MUL_LNEG : thm := BCXB.COMPLEX_MUL_LNEG
def COMPLEX_NEG_ADD : thm := BCXB.COMPLEX_NEG_ADD
def COMPLEX_NEG_0 : thm := BCXB.COMPLEX_NEG_0
def COMPLEX_EQ_ADD_LCANCEL_0 : thm := BCXB.COMPLEX_EQ_ADD_LCANCEL_0
def COMPLEX_EQ_ADD_RCANCEL_0 : thm := BCXB.COMPLEX_EQ_ADD_RCANCEL_0
def COMPLEX_LNEG_UNIQ : thm := BCXB.COMPLEX_LNEG_UNIQ
def COMPLEX_RNEG_UNIQ : thm := BCXB.COMPLEX_RNEG_UNIQ
def COMPLEX_NEG_LMUL : thm := BCXB.COMPLEX_NEG_LMUL
def COMPLEX_NEG_RMUL : thm := BCXB.COMPLEX_NEG_RMUL
def COMPLEX_NEG_MUL2 : thm := BCXB.COMPLEX_NEG_MUL2
def COMPLEX_SUB_ADD : thm := BCXB.COMPLEX_SUB_ADD
def COMPLEX_SUB_ADD2 : thm := BCXB.COMPLEX_SUB_ADD2
def COMPLEX_SUB_REFL : thm := BCXB.COMPLEX_SUB_REFL
def COMPLEX_SUB_0 : thm := BCXB.COMPLEX_SUB_0
def COMPLEX_NEG_EQ_0 : thm := BCXB.COMPLEX_NEG_EQ_0
def COMPLEX_NEG_SUB : thm := BCXB.COMPLEX_NEG_SUB
def COMPLEX_ADD_SUB : thm := BCXB.COMPLEX_ADD_SUB
def COMPLEX_NEG_EQ : thm := BCXB.COMPLEX_NEG_EQ
def COMPLEX_NEG_MINUS1 : thm := BCXB.COMPLEX_NEG_MINUS1
def COMPLEX_SUB_SUB : thm := BCXB.COMPLEX_SUB_SUB
def COMPLEX_ADD2_SUB2 : thm := BCXB.COMPLEX_ADD2_SUB2
def COMPLEX_SUB_LZERO : thm := BCXB.COMPLEX_SUB_LZERO
def COMPLEX_SUB_RZERO : thm := BCXB.COMPLEX_SUB_RZERO
def COMPLEX_SUB_LNEG : thm := BCXB.COMPLEX_SUB_LNEG
def COMPLEX_SUB_RNEG : thm := BCXB.COMPLEX_SUB_RNEG
def COMPLEX_SUB_NEG2 : thm := BCXB.COMPLEX_SUB_NEG2
def COMPLEX_SUB_TRIANGLE : thm := BCXB.COMPLEX_SUB_TRIANGLE
def COMPLEX_EQ_SUB_LADD : thm := BCXB.COMPLEX_EQ_SUB_LADD
def COMPLEX_EQ_SUB_RADD : thm := BCXB.COMPLEX_EQ_SUB_RADD
def COMPLEX_SUB_SUB2 : thm := BCXB.COMPLEX_SUB_SUB2
def COMPLEX_ADD_SUB2 : thm := BCXB.COMPLEX_ADD_SUB2
def COMPLEX_DIFFSQ : thm := BCXB.COMPLEX_DIFFSQ
def COMPLEX_EQ_NEG2 : thm := BCXB.COMPLEX_EQ_NEG2
def COMPLEX_SUB_LDISTRIB : thm := BCXB.COMPLEX_SUB_LDISTRIB
def COMPLEX_SUB_RDISTRIB : thm := BCXB.COMPLEX_SUB_RDISTRIB
def COMPLEX_MUL_2 : thm := BCXB.COMPLEX_MUL_2

initialize BCXC : HolMultiLib.Complexes.CXC ←
  ioB "setupCXC" (HolMultiLib.Complexes.setupCXC deps BCXA BCXB).run

-- CXC (complexes.ml 369-613)
def II_NZ : thm := BCXC.II_NZ
def COMPLEX_MUL_LINV : thm := BCXC.COMPLEX_MUL_LINV
def COMPLEX_ENTIRE : thm := BCXC.COMPLEX_ENTIRE
def COMPLEX_MUL_RINV : thm := BCXC.COMPLEX_MUL_RINV
def COMPLEX_DIV_REFL : thm := BCXC.COMPLEX_DIV_REFL
def COMPLEX_VEC_0 : thm := BCXC.COMPLEX_VEC_0
def COMPLEX_CMUL : thm := BCXC.COMPLEX_CMUL
def COMPLEX_POW_ADD : thm := BCXC.COMPLEX_POW_ADD
def COMPLEX_POW_POW : thm := BCXC.COMPLEX_POW_POW
def COMPLEX_POW_1 : thm := BCXC.COMPLEX_POW_1
def COMPLEX_POW_2 : thm := BCXC.COMPLEX_POW_2
def COMPLEX_POW_NEG : thm := BCXC.COMPLEX_POW_NEG
def COMPLEX_POW_ONE : thm := BCXC.COMPLEX_POW_ONE
def COMPLEX_POW_MUL : thm := BCXC.COMPLEX_POW_MUL
def COMPLEX_POW_II_2 : thm := BCXC.COMPLEX_POW_II_2
def COMPLEX_POW_EQ_0 : thm := BCXC.COMPLEX_POW_EQ_0
def COMPLEX_POW_ZERO : thm := BCXC.COMPLEX_POW_ZERO
def CX_INJ : thm := BCXC.CX_INJ
def CX_NEG : thm := BCXC.CX_NEG
def CX_ADD : thm := BCXC.CX_ADD
def CX_SUB : thm := BCXC.CX_SUB
def CX_INV : thm := BCXC.CX_INV
def CX_MUL : thm := BCXC.CX_MUL
def CX_POW : thm := BCXC.CX_POW
def CX_DIV : thm := BCXC.CX_DIV
def CX_ABS : thm := BCXC.CX_ABS
def COMPLEX_NORM_CX : thm := BCXC.COMPLEX_NORM_CX
def DIST_CX : thm := BCXC.DIST_CX
def RE_CX : thm := BCXC.RE_CX
def RE_NEG : thm := BCXC.RE_NEG
def RE_ADD : thm := BCXC.RE_ADD
def RE_SUB : thm := BCXC.RE_SUB
def IM_CX : thm := BCXC.IM_CX
def IM_NEG : thm := BCXC.IM_NEG
def IM_ADD : thm := BCXC.IM_ADD
def IM_SUB : thm := BCXC.IM_SUB
def COMPLEX_EXPAND : thm := BCXC.COMPLEX_EXPAND
def COMPLEX_TRAD : thm := BCXC.COMPLEX_TRAD
def RE_II : thm := BCXC.RE_II
def IM_II : thm := BCXC.IM_II
def RE_MUL_II : thm := BCXC.RE_MUL_II
def IM_MUL_II : thm := BCXC.IM_MUL_II
def COMPLEX_NORM_II : thm := BCXC.COMPLEX_NORM_II
def RE_CMUL : thm := BCXC.RE_CMUL
def IM_CMUL : thm := BCXC.IM_CMUL
def RE_MUL_CX : thm := BCXC.RE_MUL_CX
def IM_MUL_CX : thm := BCXC.IM_MUL_CX
def RE_DIV_CX : thm := BCXC.RE_DIV_CX
def IM_DIV_CX : thm := BCXC.IM_DIV_CX

initialize BCXD : HolMultiLib.Complexes.CXD ←
  ioB "setupCXD" (HolMultiLib.Complexes.setupCXD deps BCXA BCXB BCXC).run

-- CXD (complexes.ml 616-769)
/-- `is_complex_const` (complexes.ml 619). -/
def is_complex_const : term → Bool := fun t => BCXD.is_complex_const t
/-- `dest_complex_const` (complexes.ml 625). -/
def dest_complex_const : term → Except String Rat := fun t => BCXD.dest_complex_const t
/-- `mk_complex_const` (complexes.ml 632). -/
def mk_complex_const : Rat → Except String term := fun r => BCXD.mk_complex_const r
/-- `COMPLEX_RAT_EQ_CONV` (complexes.ml 641). -/
def COMPLEX_RAT_EQ_CONV : term → IO (Except String thm) := fun t => BCXD.COMPLEX_RAT_EQ_CONV t
/-- `COMPLEX_RAT_MUL_CONV` (complexes.ml 644). -/
def COMPLEX_RAT_MUL_CONV : term → IO (Except String thm) := fun t =>
  BCXD.COMPLEX_RAT_MUL_CONV t
/-- `COMPLEX_RAT_ADD_CONV` (complexes.ml 647). -/
def COMPLEX_RAT_ADD_CONV : term → IO (Except String thm) := fun t =>
  BCXD.COMPLEX_RAT_ADD_CONV t
/-- `COMPLEX_RAT_POW_CONV` (complexes.ml 650). -/
def COMPLEX_RAT_POW_CONV : term → IO (Except String thm) := fun t =>
  BCXD.COMPLEX_RAT_POW_CONV t
def COMPLEX_POLY_CLAUSES : thm := BCXD.COMPLEX_POLY_CLAUSES
def COMPLEX_POLY_NEG_CLAUSES : thm := BCXD.COMPLEX_POLY_NEG_CLAUSES
/-- `COMPLEX_POLY_NEG_CONV` (complexes.ml 684). -/
def COMPLEX_POLY_NEG_CONV : term → IO (Except String thm) := fun t =>
  BCXD.COMPLEX_POLY_NEG_CONV t
/-- `COMPLEX_POLY_ADD_CONV` (complexes.ml 684). -/
def COMPLEX_POLY_ADD_CONV : term → IO (Except String thm) := fun t =>
  BCXD.COMPLEX_POLY_ADD_CONV t
/-- `COMPLEX_POLY_SUB_CONV` (complexes.ml 684). -/
def COMPLEX_POLY_SUB_CONV : term → IO (Except String thm) := fun t =>
  BCXD.COMPLEX_POLY_SUB_CONV t
/-- `COMPLEX_POLY_MUL_CONV` (complexes.ml 685). -/
def COMPLEX_POLY_MUL_CONV : term → IO (Except String thm) := fun t =>
  BCXD.COMPLEX_POLY_MUL_CONV t
/-- `COMPLEX_POLY_POW_CONV` (complexes.ml 685). -/
def COMPLEX_POLY_POW_CONV : term → IO (Except String thm) := fun t =>
  BCXD.COMPLEX_POLY_POW_CONV t
/-- `COMPLEX_RAT_INV_CONV` (complexes.ml 695). -/
def COMPLEX_RAT_INV_CONV : term → IO (Except String thm) := fun t =>
  BCXD.COMPLEX_RAT_INV_CONV t
/-- `COMPLEX_POLY_CONV` (complexes.ml 698, the redefinition). -/
def COMPLEX_POLY_CONV : term → IO (Except String thm) := fun t => BCXD.COMPLEX_POLY_CONV t
/-- `COMPLEX_RING` (complexes.ml 738). -/
def COMPLEX_RING : term → IO (Except String thm) := fun t => BCXD.COMPLEX_RING t
/-- `complex_ideal_cofactors` (complexes.ml 738). -/
def complex_ideal_cofactors : List term → term → IO (Except String (List term)) :=
  fun ts t => BCXD.complex_ideal_cofactors ts t

initialize BCXE : HolMultiLib.Complexes.CXE ←
  ioB "setupCXE" (HolMultiLib.Complexes.setupCXE deps BCXA BCXB BCXC BCXD).run

-- CXE (complexes.ml 772-894)
def COMPLEX_INV_0 : thm := BCXE.COMPLEX_INV_0
def COMPLEX_INV_1 : thm := BCXE.COMPLEX_INV_1
def COMPLEX_INV_MUL : thm := BCXE.COMPLEX_INV_MUL
def COMPLEX_POW_INV : thm := BCXE.COMPLEX_POW_INV
def COMPLEX_INV_INV : thm := BCXE.COMPLEX_INV_INV
def COMPLEX_INV_DIV : thm := BCXE.COMPLEX_INV_DIV
def COMPLEX_EQ_INV2 : thm := BCXE.COMPLEX_EQ_INV2
def SGN_RE_COMPLEX_INV : thm := BCXE.SGN_RE_COMPLEX_INV
def RE_COMPLEX_INV_GT_0 : thm := BCXE.RE_COMPLEX_INV_GT_0
def RE_COMPLEX_INV_GE_0 : thm := BCXE.RE_COMPLEX_INV_GE_0
def COMPLEX_EQ_MUL_LCANCEL : thm := BCXE.COMPLEX_EQ_MUL_LCANCEL
def COMPLEX_EQ_MUL_RCANCEL : thm := BCXE.COMPLEX_EQ_MUL_RCANCEL
/-- `COMPLEX_FIELD` (complexes.ml 847). -/
def COMPLEX_FIELD : term → IO (Except String thm) := fun t => BCXE.COMPLEX_FIELD t

initialize BCXF : HolMultiLib.Complexes.CXF ←
  ioB "setupCXF" (HolMultiLib.Complexes.setupCXF deps BCXA BCXB BCXC BCXE).run

-- CXF (complexes.ml 896-1037)
def COMPLEX_DIV_1 : thm := BCXF.COMPLEX_DIV_1
def COMPLEX_DIV_LMUL : thm := BCXF.COMPLEX_DIV_LMUL
def COMPLEX_DIV_RMUL : thm := BCXF.COMPLEX_DIV_RMUL
def COMPLEX_INV_II : thm := BCXF.COMPLEX_INV_II
def COMPLEX_INV_EQ_0 : thm := BCXF.COMPLEX_INV_EQ_0
def COMPLEX_INV_NEG : thm := BCXF.COMPLEX_INV_NEG
def COMPLEX_NEG_INV : thm := BCXF.COMPLEX_NEG_INV
def COMPLEX_INV_EQ_1 : thm := BCXF.COMPLEX_INV_EQ_1
def COMPLEX_DIV_EQ_0 : thm := BCXF.COMPLEX_DIV_EQ_0
def COMPLEX_POW_DIV : thm := BCXF.COMPLEX_POW_DIV
def COMPLEX_DIV_POW : thm := BCXF.COMPLEX_DIV_POW
def COMPLEX_DIV_POW2 : thm := BCXF.COMPLEX_DIV_POW2
def COMPLEX_NORM_ZERO : thm := BCXF.COMPLEX_NORM_ZERO
def COMPLEX_NORM_NUM : thm := BCXF.COMPLEX_NORM_NUM
def COMPLEX_NORM_0 : thm := BCXF.COMPLEX_NORM_0
def COMPLEX_NORM_NZ : thm := BCXF.COMPLEX_NORM_NZ
def COMPLEX_NORM_MUL : thm := BCXF.COMPLEX_NORM_MUL
def COMPLEX_NORM_POW : thm := BCXF.COMPLEX_NORM_POW
def COMPLEX_NORM_INV : thm := BCXF.COMPLEX_NORM_INV
def COMPLEX_NORM_DIV : thm := BCXF.COMPLEX_NORM_DIV
def COMPLEX_NORM_TRIANGLE_SUB : thm := BCXF.COMPLEX_NORM_TRIANGLE_SUB
def COMPLEX_NORM_ABS_NORM : thm := BCXF.COMPLEX_NORM_ABS_NORM
def COMPLEX_POW_EQ_1 : thm := BCXF.COMPLEX_POW_EQ_1

initialize BCXG : HolMultiLib.Complexes.CXG ←
  ioB "setupCXG" (HolMultiLib.Complexes.setupCXG deps BCXA BCXB BCXC BCXE BCXF).run

-- CXG (complexes.ml 1039-1302)
def cnj : thm := BCXG.cnj
def CNJ_INJ : thm := BCXG.CNJ_INJ
def CNJ_CNJ : thm := BCXG.CNJ_CNJ
def CNJ_CX : thm := BCXG.CNJ_CX
def COMPLEX_NORM_CNJ : thm := BCXG.COMPLEX_NORM_CNJ
def CNJ_NEG : thm := BCXG.CNJ_NEG
def CNJ_INV : thm := BCXG.CNJ_INV
def CNJ_ADD : thm := BCXG.CNJ_ADD
def CNJ_SUB : thm := BCXG.CNJ_SUB
def CNJ_MUL : thm := BCXG.CNJ_MUL
def CNJ_DIV : thm := BCXG.CNJ_DIV
def CNJ_POW : thm := BCXG.CNJ_POW
def RE_CNJ : thm := BCXG.RE_CNJ
def IM_CNJ : thm := BCXG.IM_CNJ
def CNJ_EQ_CX : thm := BCXG.CNJ_EQ_CX
def CNJ_EQ_0 : thm := BCXG.CNJ_EQ_0
def COMPLEX_ADD_CNJ : thm := BCXG.COMPLEX_ADD_CNJ
def CNJ_II : thm := BCXG.CNJ_II
def CX_RE_CNJ : thm := BCXG.CX_RE_CNJ
def CX_IM_CNJ : thm := BCXG.CX_IM_CNJ
def FORALL_CNJ : thm := BCXG.FORALL_CNJ
def EXISTS_CNJ : thm := BCXG.EXISTS_CNJ
def COMPLEX_NORM_POW_2 : thm := BCXG.COMPLEX_NORM_POW_2
def COMPLEX_MUL_CNJ : thm := BCXG.COMPLEX_MUL_CNJ
def COMPLEX_INV_CNJ : thm := BCXG.COMPLEX_INV_CNJ
def COMPLEX_DIV_CNJ : thm := BCXG.COMPLEX_DIV_CNJ
def RE_COMPLEX_DIV_EQ_0 : thm := BCXG.RE_COMPLEX_DIV_EQ_0
def IM_COMPLEX_DIV_EQ_0 : thm := BCXG.IM_COMPLEX_DIV_EQ_0
def RE_COMPLEX_DIV_GT_0 : thm := BCXG.RE_COMPLEX_DIV_GT_0
def IM_COMPLEX_DIV_GT_0 : thm := BCXG.IM_COMPLEX_DIV_GT_0
def RE_COMPLEX_DIV_GE_0 : thm := BCXG.RE_COMPLEX_DIV_GE_0
def IM_COMPLEX_DIV_GE_0 : thm := BCXG.IM_COMPLEX_DIV_GE_0
def RE_COMPLEX_DIV_LE_0 : thm := BCXG.RE_COMPLEX_DIV_LE_0
def IM_COMPLEX_DIV_LE_0 : thm := BCXG.IM_COMPLEX_DIV_LE_0
def RE_COMPLEX_DIV_LT_0 : thm := BCXG.RE_COMPLEX_DIV_LT_0
def IM_COMPLEX_DIV_LT_0 : thm := BCXG.IM_COMPLEX_DIV_LT_0
def IM_COMPLEX_INV_GE_0 : thm := BCXG.IM_COMPLEX_INV_GE_0
def IM_COMPLEX_INV_LE_0 : thm := BCXG.IM_COMPLEX_INV_LE_0
def IM_COMPLEX_INV_GT_0 : thm := BCXG.IM_COMPLEX_INV_GT_0
def IM_COMPLEX_INV_LT_0 : thm := BCXG.IM_COMPLEX_INV_LT_0
def IM_COMPLEX_INV_EQ_0 : thm := BCXG.IM_COMPLEX_INV_EQ_0
def REAL_SGN_RE_COMPLEX_DIV : thm := BCXG.REAL_SGN_RE_COMPLEX_DIV
def REAL_SGN_IM_COMPLEX_DIV : thm := BCXG.REAL_SGN_IM_COMPLEX_DIV
def COMPLEX_NORM_GE_RE_IM : thm := BCXG.COMPLEX_NORM_GE_RE_IM
def COMPLEX_NORM_LE_RE_IM : thm := BCXG.COMPLEX_NORM_LE_RE_IM
def COMPLEX_L1_LE_NORM : thm := BCXG.COMPLEX_L1_LE_NORM

initialize BCXH : HolMultiLib.Complexes.CXH ←
  ioB "setupCXH" (HolMultiLib.Complexes.setupCXH deps BCXA BCXB BCXC BCXD BCXF BCXG).run

-- CXH (complexes.ml 1304-1567)
def csqrt : thm := BCXH.csqrt
def CSQRT : thm := BCXH.CSQRT
def CX_SQRT : thm := BCXH.CX_SQRT
def CSQRT_CX : thm := BCXH.CSQRT_CX
def CSQRT_0 : thm := BCXH.CSQRT_0
def CSQRT_1 : thm := BCXH.CSQRT_1
def CSQRT_PRINCIPAL : thm := BCXH.CSQRT_PRINCIPAL
def RE_CSQRT : thm := BCXH.RE_CSQRT
def CSQRT_UNIQUE : thm := BCXH.CSQRT_UNIQUE
def POW_2_CSQRT : thm := BCXH.POW_2_CSQRT
def CSQRT_EQ_0 : thm := BCXH.CSQRT_EQ_0
def DOT_COMPLEX_MUL_CNJ : thm := BCXH.DOT_COMPLEX_MUL_CNJ
def DOT_CNJ : thm := BCXH.DOT_CNJ
def LINEAR_COMPLEX_MUL : thm := BCXH.LINEAR_COMPLEX_MUL
def BILINEAR_COMPLEX_MUL : thm := BCXH.BILINEAR_COMPLEX_MUL
def LINEAR_CNJ : thm := BCXH.LINEAR_CNJ
def ORTHOGONAL_TRANSFORMATION_CNJ : thm := BCXH.ORTHOGONAL_TRANSFORMATION_CNJ
def LINEAR_COMPLEX_LMUL : thm := BCXH.LINEAR_COMPLEX_LMUL
def LINEAR_COMPLEX_RMUL : thm := BCXH.LINEAR_COMPLEX_RMUL
def COMPLEX_CAUCHY_SCHWARZ_EQ : thm := BCXH.COMPLEX_CAUCHY_SCHWARZ_EQ
def COMPLEX_BASIS : thm := BCXH.COMPLEX_BASIS
def COMPLEX_LINEAR : thm := BCXH.COMPLEX_LINEAR
def COMPLEX_LINEAR_ALT : thm := BCXH.COMPLEX_LINEAR_ALT
def ORTHOGONAL_TRANSFORMATION_COMPLEX_MUL : thm := BCXH.ORTHOGONAL_TRANSFORMATION_COMPLEX_MUL
def COMPLEX_ORTHOGONAL_ROTATION : thm := BCXH.COMPLEX_ORTHOGONAL_ROTATION
def COMPLEX_ORTHOGONAL_ROTOINVERSION : thm := BCXH.COMPLEX_ORTHOGONAL_ROTOINVERSION
def COMPLEX_ORTHOGONAL_TRANSFORMATION : thm := BCXH.COMPLEX_ORTHOGONAL_TRANSFORMATION

initialize BCXI : HolMultiLib.Complexes.CXI ←
  ioB "setupCXI" (HolMultiLib.Complexes.setupCXI deps BCXA BCXB BCXC BCXD BCXE BCXG).run

-- CXI (complexes.ml 1569-1794)
def RE_VSUM : thm := BCXI.RE_VSUM
def IM_VSUM : thm := BCXI.IM_VSUM
def VSUM_COMPLEX_LMUL : thm := BCXI.VSUM_COMPLEX_LMUL
def VSUM_COMPLEX_RMUL : thm := BCXI.VSUM_COMPLEX_RMUL
def VSUM_CX : thm := BCXI.VSUM_CX
def CNJ_VSUM : thm := BCXI.CNJ_VSUM
def VSUM_CX_NUMSEG : thm := BCXI.VSUM_CX_NUMSEG
def COMPLEX_SUB_POW : thm := BCXI.COMPLEX_SUB_POW
def COMPLEX_SUB_POW_R1 : thm := BCXI.COMPLEX_SUB_POW_R1
def COMPLEX_SUB_POW_L1 : thm := BCXI.COMPLEX_SUB_POW_L1
def real : thm := BCXI.real
def REAL : thm := BCXI.REAL
def REAL_CNJ : thm := BCXI.REAL_CNJ
def REAL_IMP_CNJ : thm := BCXI.REAL_IMP_CNJ
def REAL_EXISTS : thm := BCXI.REAL_EXISTS
def FORALL_REAL : thm := BCXI.FORALL_REAL
def EXISTS_REAL : thm := BCXI.EXISTS_REAL
def REAL_CX : thm := BCXI.REAL_CX
def REAL_MUL_CX : thm := BCXI.REAL_MUL_CX
def REAL_ADD : thm := BCXI.REAL_ADD
def REAL_NEG : thm := BCXI.REAL_NEG
def REAL_SUB : thm := BCXI.REAL_SUB
def REAL_MUL : thm := BCXI.REAL_MUL
def REAL_POW : thm := BCXI.REAL_POW
def REAL_INV : thm := BCXI.REAL_INV
def REAL_INV_EQ : thm := BCXI.REAL_INV_EQ
def REAL_DIV : thm := BCXI.REAL_DIV
def REAL_VSUM : thm := BCXI.REAL_VSUM
def REAL_MUL_CNJ : thm := BCXI.REAL_MUL_CNJ
def REAL_SEGMENT : thm := BCXI.REAL_SEGMENT
def IN_SEGMENT_CX : thm := BCXI.IN_SEGMENT_CX
def IN_SEGMENT_CX_GEN : thm := BCXI.IN_SEGMENT_CX_GEN
def RE_POS_SEGMENT : thm := BCXI.RE_POS_SEGMENT
def CONVEX_REAL : thm := BCXI.CONVEX_REAL
def IMAGE_CX : thm := BCXI.IMAGE_CX
def SUBSPACE_REAL : thm := BCXI.SUBSPACE_REAL
def DIM_REAL : thm := BCXI.DIM_REAL
def INTERIOR_REAL : thm := BCXI.INTERIOR_REAL

initialize BCXJ : HolMultiLib.Complexes.CXJ ←
  ioB "setupCXJ" (HolMultiLib.Complexes.setupCXJ deps BCXA BCXB BCXC BCXD BCXE BCXF
    BCXI).run

-- CXJ (complexes.ml 1796-2090)
def REAL_NORM : thm := BCXJ.REAL_NORM
def REAL_NORM_POS : thm := BCXJ.REAL_NORM_POS
def COMPLEX_NORM_VSUM_SUM_RE : thm := BCXJ.COMPLEX_NORM_VSUM_SUM_RE
def COMPLEX_NORM_VSUM_BOUND : thm := BCXJ.COMPLEX_NORM_VSUM_BOUND
def COMPLEX_NORM_VSUM_BOUND_SUBSET : thm := BCXJ.COMPLEX_NORM_VSUM_BOUND_SUBSET
def VSUM_GP_BASIC : thm := BCXJ.VSUM_GP_BASIC
def VSUM_GP_MULTIPLIED : thm := BCXJ.VSUM_GP_MULTIPLIED
def VSUM_GP : thm := BCXJ.VSUM_GP
def VSUM_GP_OFFSET : thm := BCXJ.VSUM_GP_OFFSET
def COMPLEX_SUB_POLYFUN : thm := BCXJ.COMPLEX_SUB_POLYFUN
def COMPLEX_SUB_POLYFUN_ALT : thm := BCXJ.COMPLEX_SUB_POLYFUN_ALT
def COMPLEX_POLYFUN_LINEAR_FACTOR : thm := BCXJ.COMPLEX_POLYFUN_LINEAR_FACTOR
def COMPLEX_POLYFUN_LINEAR_FACTOR_ROOT : thm := BCXJ.COMPLEX_POLYFUN_LINEAR_FACTOR_ROOT
def COMPLEX_POLYFUN_EXTREMAL_LEMMA : thm := BCXJ.COMPLEX_POLYFUN_EXTREMAL_LEMMA
def COMPLEX_POLYFUN_EXTREMAL : thm := BCXJ.COMPLEX_POLYFUN_EXTREMAL
def COMPLEX_POLYFUN_ROOTBOUND : thm := BCXJ.COMPLEX_POLYFUN_ROOTBOUND
def COMPLEX_POLYFUN_FINITE_ROOTS : thm := BCXJ.COMPLEX_POLYFUN_FINITE_ROOTS
def COMPLEX_POLYFUN_EQ_0 : thm := BCXJ.COMPLEX_POLYFUN_EQ_0
def COMPLEX_POLYFUN_EQ_CONST : thm := BCXJ.COMPLEX_POLYFUN_EQ_CONST

initialize BCXK : HolMultiLib.Complexes.CXK ←
  ioB "setupCXK" (HolMultiLib.Complexes.setupCXK deps BCXA BCXB BCXC BCXE BCXF BCXG).run

-- CXK (complexes.ml 2092-2250)
def cproduct : thm := BCXK.cproduct
def NEUTRAL_COMPLEX_MUL : thm := BCXK.NEUTRAL_COMPLEX_MUL
def MONOIDAL_COMPLEX_MUL : thm := BCXK.MONOIDAL_COMPLEX_MUL
def CPRODUCT_CLAUSES : thm := BCXK.CPRODUCT_CLAUSES
def CPRODUCT_EQ_0 : thm := BCXK.CPRODUCT_EQ_0
def CPRODUCT_INV : thm := BCXK.CPRODUCT_INV
def CPRODUCT_MUL : thm := BCXK.CPRODUCT_MUL
def CPRODUCT_EQ_1 : thm := BCXK.CPRODUCT_EQ_1
def CPRODUCT_1 : thm := BCXK.CPRODUCT_1
def CPRODUCT_POW : thm := BCXK.CPRODUCT_POW
def NORM_CPRODUCT : thm := BCXK.NORM_CPRODUCT
def CPRODUCT_EQ : thm := BCXK.CPRODUCT_EQ
def CPRODUCT_SING : thm := BCXK.CPRODUCT_SING
def CPRODUCT_CLAUSES_NUMSEG : thm := BCXK.CPRODUCT_CLAUSES_NUMSEG
def CPRODUCT_CLAUSES_RIGHT : thm := BCXK.CPRODUCT_CLAUSES_RIGHT
def CPRODUCT_CLAUSES_LEFT : thm := BCXK.CPRODUCT_CLAUSES_LEFT
def CPRODUCT_IMAGE : thm := BCXK.CPRODUCT_IMAGE
def CPRODUCT_OFFSET : thm := BCXK.CPRODUCT_OFFSET
def CPRODUCT_CONST : thm := BCXK.CPRODUCT_CONST
def CPRODUCT_CONST_NUMSEG : thm := BCXK.CPRODUCT_CONST_NUMSEG
def CPRODUCT_PAIR : thm := BCXK.CPRODUCT_PAIR
def CPRODUCT_REFLECT : thm := BCXK.CPRODUCT_REFLECT
def CNJ_CPRODUCT : thm := BCXK.CNJ_CPRODUCT
def CX_PRODUCT : thm := BCXK.CX_PRODUCT
def CPRODUCT_SUPERSET : thm := BCXK.CPRODUCT_SUPERSET
def CPRODUCT_UNION : thm := BCXK.CPRODUCT_UNION

/-- `needs "Multivariate/complexes.ml"`: importing this module has built
    every bundle; this is a no-op kept for symmetry with the other wiring files. -/
def ensureComplexes : IO Unit := pure ()

end SessionMultiLib.Complexes
