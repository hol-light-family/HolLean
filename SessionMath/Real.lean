/- File: SessionMath/Real.lean
real.ml: the theory of the real numbers, built by `initialize` when this
module is imported.  Several of its proofs (RealThms5/9/11) end in
REAL_ARITH_TAC goals that are provable only while `:real` is the default
type for overloaded operators; that holds here, as in HOL Light, because
int.ml's overloads and its closing `prioritize_num` come later.
-/
import SessionMath.RealArith
import HolMath.Real

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Simp HolCore.Theorems HolCore.Classic

namespace Session

private def ioOk' {α : Type} (what : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"{what}: {e}")




/- ---------------------------------------------------------------------- -/
/- real.ml: the theory of the real numbers.                                -/
/-                                                                        -/
/- Twelve setups wired in dependency order.  `REAL_ARITH` throughout       -/
/- means `REAL_ARITH2` (realarith.ml's second REAL_ARITH), which is what    -/
/- real.ml's `REAL_ARITH` denotes at this point in the load order.  Each    -/
/- setup is an `initialize` constant; PUBLIC accessors below expose each    -/
/- bundle with its real.ml line range. -/
/- ---------------------------------------------------------------------- -/

/-- `RealThms1` (real.ml 14-102): `REAL_OF_NUM_*` bridges, `REAL_MUL_AC`,
    distributivity and the two strict-order lemmas. -/
initialize realThms1Layer : HolMath.Real.RealThms1 ←
  ioOk' "setupRealThms1" (HolMath.Real.setupRealThms1 arith1 arith2 arith3 arith4 arith5 CiT Rl RaL
    MESON_TAC ASM_MESON_TAC).run

def RT1 : HolMath.Real.RealThms1 := realThms1Layer

/-- `RealThms2` (real.ml 109-255): the thirty-six linear theorems. -/
initialize realThms2Layer : HolMath.Real.RealThms2 ←
  ioOk' "setupRealThms2" (HolMath.Real.setupRealThms2 REAL_ARITH2 Rl CiT).run

def RT2 : HolMath.Real.RealThms2 := realThms2Layer

/-- `RealThms3` (real.ml 256-400): further linear/subtraction theorems. -/
initialize realThms3Layer : HolMath.Real.RealThms3 ←
  ioOk' "setupRealThms3" (HolMath.Real.setupRealThms3 REAL_ARITH2).run

def RT3 : HolMath.Real.RealThms3 := realThms3Layer

/-- `RealThms4` (real.ml 401-510): the absolute-value theorems. -/
initialize realThms4Layer : HolMath.Real.RealThms4 ←
  ioOk' "setupRealThms4" (HolMath.Real.setupRealThms4 REAL_ARITH2).run

def RT4 : HolMath.Real.RealThms4 := realThms4Layer

/-- `RealThms5` (real.ml 511-594): the min/max theorems.  Built here while
    `:real` is still the schematic default (see the header note). -/
initialize realThms5Layer : HolMath.Real.RealThms5 ←
  ioOk' "setupRealThms5" (HolMath.Real.setupRealThms5 REAL_ARITH2).run

def RT5 : HolMath.Real.RealThms5 := realThms5Layer

/-- `RealBackchain` (real.ml 595-606): the two backchaining `pth`s. -/
initialize realBackchainLayer : HolMath.Real.RealBackchain ←
  ioOk' "setupRealBackchain" (HolMath.Real.setupRealBackchain T.IMP_CONJ Rl.REAL_LE_TRANS
    RaL.REAL_LET_TRANS).run

def RBc : HolMath.Real.RealBackchain := realBackchainLayer

/-- `RealThms6` (real.ml 607-855): multiplication/inverse/division/power. -/
initialize realThms6Layer : HolMath.Real.RealThms6 ←
  ioOk' "setupRealThms6" (HolMath.Real.setupRealThms6 Nm arith1 arith4 arith5 CnA Rl CiT RaL
    RT1 RT2 RT3 RT4 REAL_ARITH2 MESON_TAC ASM_MESON_TAC).run

def RT6 : HolMath.Real.RealThms6 := realThms6Layer

/-- `RealThms7` (real.ml 856-1114): cancellation and division/inverse
    ordering theorems. -/
initialize realThms7Layer : HolMath.Real.RealThms7 ←
  ioOk' "setupRealThms7" (HolMath.Real.setupRealThms7 Nm Rl CiT RaL
    RT1 RT2 RT3 RT6 num_CONV REAL_ARITH2 MESON_TAC).run

def RT7 : HolMath.Real.RealThms7 := realThms7Layer

/-- `RealThms8` (real.ml 1115-1389): power monotonicity and squares. -/
initialize realThms8Layer : HolMath.Real.RealThms8 ←
  ioOk' "setupRealThms8" (HolMath.Real.setupRealThms8 Nm arith1 arith2 arith3 arith4 arith5 arith7
    CnA Rl CiT RaL RT1 RT2 RT3 RT4 RT6 RT7 NUM_EQ_CONV REAL_ARITH2 MESON_TAC ASM_MESON_TAC).run

def RT8 : HolMath.Real.RealThms8 := realThms8Layer

/-- `RealThms9` (real.ml 1390-1517): convex bounds and the Archimedean
    theorems.  Built here while `:real` is still the schematic default. -/
initialize realThms9Layer : HolMath.Real.RealThms9 ←
  ioOk' "setupRealThms9" (HolMath.Real.setupRealThms9 Nm CnA Rl CiT RaL
    RT1 RT2 RT3 RT6 RT7 REAL_ARITH2 MESON_TAC ASM_MESON_TAC).run

def RT9 : HolMath.Real.RealThms9 := realThms9Layer

/-- `RealThms10` (real.ml 1518-1656): the `real_sgn` definition and its
    theorems, plus the WLOG rules.  `real_sgn` is a new definition here, so
    this setup is NOT idempotent — the `initialize` runs it at most once. -/
initialize realThms10Layer : HolMath.Real.RealThms10 ←
  ioOk' "setupRealThms10" (HolMath.Real.setupRealThms10 Nm CnA Rl CiT RaL
    RT2 RT4 RT6 RT7 RT8 new_definition REAL_ARITH2 MESON_TAC).run

def RT10 : HolMath.Real.RealThms10 := realThms10Layer

/-- `RealThms11` (real.ml 1657-1993): the `sqrt` definition and its theory.
    `sqrt` is a new definition here, so this setup is NOT idempotent.  Built
    here while `:real` is still the schematic default. -/
initialize realThms11Layer : HolMath.Real.RealThms11 ←
  ioOk' "setupRealThms11" (HolMath.Real.setupRealThms11 arith2 arith5 arith7 CnA Rl CiT RaL
    RT2 RT3 RT4 RT5 RT6 RT7 RT8 RT10
    SELECT_CONV NUM_REDUCE_CONV new_definition REAL_ARITH2 MESON_TAC ASM_MESON_TAC).run

def RT11 : HolMath.Real.RealThms11 := realThms11Layer

/- Public accessors for the real.ml bundles. -/

/-- The `real.ml` first block (14-102). -/
def realThms1 : HolMath.Real.RealThms1 := RT1
/-- The `real.ml` second block (109-255). -/
def realThms2 : HolMath.Real.RealThms2 := RT2
/-- The `real.ml` third block (256-400). -/
def realThms3 : HolMath.Real.RealThms3 := RT3
/-- The `real.ml` fourth block (401-510). -/
def realThms4 : HolMath.Real.RealThms4 := RT4
/-- The `real.ml` fifth block (511-594). -/
def realThms5 : HolMath.Real.RealThms5 := RT5
/-- The `real.ml` backchaining rules' context (595-606). -/
def realBackchain : HolMath.Real.RealBackchain := RBc
/-- The `real.ml` sixth block (607-855). -/
def realThms6 : HolMath.Real.RealThms6 := RT6
/-- The `real.ml` seventh block (856-1114). -/
def realThms7 : HolMath.Real.RealThms7 := RT7
/-- The `real.ml` eighth block (1115-1389). -/
def realThms8 : HolMath.Real.RealThms8 := RT8
/-- The `real.ml` ninth block (1390-1517). -/
def realThms9 : HolMath.Real.RealThms9 := RT9
/-- The `real.ml` tenth block (1518-1656). -/
def realThms10 : HolMath.Real.RealThms10 := RT10
/-- The `real.ml` eleventh block (1657-1993). -/
def realThms11 : HolMath.Real.RealThms11 := RT11

/-- `REAL_ARITH_TAC` (real.ml 106): `CONV_TAC REAL_ARITH`, with `REAL_ARITH2`
    pre-supplied.  NOTE: `ASM_REAL_ARITH_TAC` is NOT defined in real.ml — it
    arrives with calc_rat.ml — so it is not exposed here. -/
def REAL_ARITH_TAC : tactic := HolMath.Real.REAL_ARITH_TAC REAL_ARITH2

/-- `REAL_LE_IMP` (real.ml 597-599): a RULE, given `th` returns `GEN_ALL
    (MATCH_MP le_pth (SPEC_ALL th))`. -/
def REAL_LE_IMP (th : thm) : IO (Except String thm) :=
  HolMath.Real.REAL_LE_IMP RBc th
/-- `REAL_LET_IMP` (real.ml 601-603): a RULE, given `th` returns `GEN_ALL
    (MATCH_MP let_pth (SPEC_ALL th))`. -/
def REAL_LET_IMP (th : thm) : IO (Except String thm) :=
  HolMath.Real.REAL_LET_IMP RBc th

/- The real.ml theorems as bare names, as HOL Light has them. -/
def REAL_OF_NUM_LT        : thm := realThms1.REAL_OF_NUM_LT
def REAL_OF_NUM_GE        : thm := realThms1.REAL_OF_NUM_GE
def REAL_OF_NUM_GT        : thm := realThms1.REAL_OF_NUM_GT
def REAL_OF_NUM_MAX       : thm := realThms1.REAL_OF_NUM_MAX
def REAL_OF_NUM_MIN       : thm := realThms1.REAL_OF_NUM_MIN
def REAL_OF_NUM_SUC       : thm := realThms1.REAL_OF_NUM_SUC
def REAL_OF_NUM_SUB       : thm := realThms1.REAL_OF_NUM_SUB
def REAL_OF_NUM_SUB_CASES : thm := realThms1.REAL_OF_NUM_SUB_CASES
def REAL_OF_NUM_CLAUSES   : thm := realThms1.REAL_OF_NUM_CLAUSES
def REAL_MUL_AC           : thm := realThms1.REAL_MUL_AC
def REAL_ADD_RDISTRIB     : thm := realThms1.REAL_ADD_RDISTRIB
def REAL_LT_LADD_IMP      : thm := realThms1.REAL_LT_LADD_IMP
def REAL_LT_MUL           : thm := realThms1.REAL_LT_MUL
def REAL_EQ_ADD_LCANCEL_0 : thm := realThms2.REAL_EQ_ADD_LCANCEL_0
def REAL_EQ_ADD_RCANCEL_0 : thm := realThms2.REAL_EQ_ADD_RCANCEL_0
def REAL_LNEG_UNIQ        : thm := realThms2.REAL_LNEG_UNIQ
def REAL_RNEG_UNIQ        : thm := realThms2.REAL_RNEG_UNIQ
def REAL_NEG_LMUL         : thm := realThms2.REAL_NEG_LMUL
def REAL_NEG_RMUL         : thm := realThms2.REAL_NEG_RMUL
def REAL_NEG_MUL2         : thm := realThms2.REAL_NEG_MUL2
def REAL_LT_LADD          : thm := realThms2.REAL_LT_LADD
def REAL_LT_RADD          : thm := realThms2.REAL_LT_RADD
def REAL_LT_ANTISYM       : thm := realThms2.REAL_LT_ANTISYM
def REAL_LT_GT            : thm := realThms2.REAL_LT_GT
def REAL_NOT_EQ           : thm := realThms2.REAL_NOT_EQ
def REAL_NOT_LE           : thm := realThms2.REAL_NOT_LE
def REAL_LET_ANTISYM      : thm := realThms2.REAL_LET_ANTISYM
def REAL_NEG_LT0          : thm := realThms2.REAL_NEG_LT0
def REAL_NEG_GT0          : thm := realThms2.REAL_NEG_GT0
def REAL_NEG_LE0          : thm := realThms2.REAL_NEG_LE0
def REAL_NEG_GE0          : thm := realThms2.REAL_NEG_GE0
def REAL_LT_TOTAL         : thm := realThms2.REAL_LT_TOTAL
def REAL_LT_NEGTOTAL      : thm := realThms2.REAL_LT_NEGTOTAL
def REAL_LE_01            : thm := realThms2.REAL_LE_01
def REAL_LT_01            : thm := realThms2.REAL_LT_01
def REAL_LE_LADD          : thm := realThms2.REAL_LE_LADD
def REAL_LE_RADD          : thm := realThms2.REAL_LE_RADD
def REAL_LT_ADD2          : thm := realThms2.REAL_LT_ADD2
def REAL_LE_ADD2          : thm := realThms2.REAL_LE_ADD2
def REAL_LT_LNEG          : thm := realThms2.REAL_LT_LNEG
def REAL_LT_RNEG          : thm := realThms2.REAL_LT_RNEG
def REAL_LT_ADDNEG        : thm := realThms2.REAL_LT_ADDNEG
def REAL_LT_ADDNEG2       : thm := realThms2.REAL_LT_ADDNEG2
def REAL_LT_ADD1          : thm := realThms2.REAL_LT_ADD1
def REAL_SUB_ADD          : thm := realThms2.REAL_SUB_ADD
def REAL_SUB_ADD2         : thm := realThms2.REAL_SUB_ADD2
def REAL_SUB_REFL         : thm := realThms2.REAL_SUB_REFL
def REAL_LE_DOUBLE        : thm := realThms2.REAL_LE_DOUBLE
def REAL_LE_NEGL          : thm := realThms2.REAL_LE_NEGL
def REAL_LE_NEGR          : thm := realThms3.REAL_LE_NEGR
def REAL_NEG_EQ_0         : thm := realThms3.REAL_NEG_EQ_0
def REAL_ADD_SUB          : thm := realThms3.REAL_ADD_SUB
def REAL_NEG_EQ           : thm := realThms3.REAL_NEG_EQ
def REAL_NEG_MINUS1       : thm := realThms3.REAL_NEG_MINUS1
def REAL_LT_IMP_NE        : thm := realThms3.REAL_LT_IMP_NE
def REAL_LE_ADDR          : thm := realThms3.REAL_LE_ADDR
def REAL_LE_ADDL          : thm := realThms3.REAL_LE_ADDL
def REAL_LT_ADDR          : thm := realThms3.REAL_LT_ADDR
def REAL_LT_ADDL          : thm := realThms3.REAL_LT_ADDL
def REAL_SUB_SUB          : thm := realThms3.REAL_SUB_SUB
def REAL_LT_ADD_SUB       : thm := realThms3.REAL_LT_ADD_SUB
def REAL_LT_SUB_RADD      : thm := realThms3.REAL_LT_SUB_RADD
def REAL_LT_SUB_LADD      : thm := realThms3.REAL_LT_SUB_LADD
def REAL_LE_SUB_LADD      : thm := realThms3.REAL_LE_SUB_LADD
def REAL_LE_SUB_RADD      : thm := realThms3.REAL_LE_SUB_RADD
def REAL_ADD2_SUB2        : thm := realThms3.REAL_ADD2_SUB2
def REAL_SUB_LZERO        : thm := realThms3.REAL_SUB_LZERO
def REAL_SUB_RZERO        : thm := realThms3.REAL_SUB_RZERO
def REAL_LET_ADD2         : thm := realThms3.REAL_LET_ADD2
def REAL_LTE_ADD2         : thm := realThms3.REAL_LTE_ADD2
def REAL_SUB_LNEG         : thm := realThms3.REAL_SUB_LNEG
def REAL_SUB_RNEG         : thm := realThms3.REAL_SUB_RNEG
def REAL_SUB_NEG2         : thm := realThms3.REAL_SUB_NEG2
def REAL_SUB_TRIANGLE     : thm := realThms3.REAL_SUB_TRIANGLE
def REAL_EQ_SUB_LADD      : thm := realThms3.REAL_EQ_SUB_LADD
def REAL_EQ_SUB_RADD      : thm := realThms3.REAL_EQ_SUB_RADD
def REAL_SUB_SUB2         : thm := realThms3.REAL_SUB_SUB2
def REAL_ADD_SUB2         : thm := realThms3.REAL_ADD_SUB2
def REAL_EQ_IMP_LE        : thm := realThms3.REAL_EQ_IMP_LE
def REAL_LT_IMP_NZ        : thm := realThms3.REAL_LT_IMP_NZ
def REAL_DIFFSQ           : thm := realThms3.REAL_DIFFSQ
def REAL_EQ_NEG2          : thm := realThms3.REAL_EQ_NEG2
def REAL_LT_NEG2          : thm := realThms3.REAL_LT_NEG2
def REAL_SUB_LDISTRIB     : thm := realThms3.REAL_SUB_LDISTRIB
def REAL_SUB_RDISTRIB     : thm := realThms3.REAL_SUB_RDISTRIB
def REAL_ABS_ZERO         : thm := realThms4.REAL_ABS_ZERO
def REAL_ABS_0            : thm := realThms4.REAL_ABS_0
def REAL_ABS_1            : thm := realThms4.REAL_ABS_1
def REAL_ABS_TRIANGLE     : thm := realThms4.REAL_ABS_TRIANGLE
def REAL_ABS_TRIANGLE_LE  : thm := realThms4.REAL_ABS_TRIANGLE_LE
def REAL_ABS_TRIANGLE_LT  : thm := realThms4.REAL_ABS_TRIANGLE_LT
def REAL_ABS_POS          : thm := realThms4.REAL_ABS_POS
def REAL_ABS_SUB          : thm := realThms4.REAL_ABS_SUB
def REAL_ABS_NZ           : thm := realThms4.REAL_ABS_NZ
def REAL_ABS_ABS          : thm := realThms4.REAL_ABS_ABS
def REAL_ABS_LE           : thm := realThms4.REAL_ABS_LE
def REAL_ABS_REFL         : thm := realThms4.REAL_ABS_REFL
def REAL_ABS_BETWEEN      : thm := realThms4.REAL_ABS_BETWEEN
def REAL_ABS_BOUND        : thm := realThms4.REAL_ABS_BOUND
def REAL_ABS_STILLNZ      : thm := realThms4.REAL_ABS_STILLNZ
def REAL_ABS_CASES        : thm := realThms4.REAL_ABS_CASES
def REAL_ABS_BETWEEN1     : thm := realThms4.REAL_ABS_BETWEEN1
def REAL_ABS_SIGN         : thm := realThms4.REAL_ABS_SIGN
def REAL_ABS_SIGN2        : thm := realThms4.REAL_ABS_SIGN2
def REAL_ABS_CIRCLE       : thm := realThms4.REAL_ABS_CIRCLE
def REAL_SUB_ABS          : thm := realThms4.REAL_SUB_ABS
def REAL_ABS_SUB_ABS      : thm := realThms4.REAL_ABS_SUB_ABS
def REAL_ABS_BETWEEN2     : thm := realThms4.REAL_ABS_BETWEEN2
def REAL_ABS_BOUNDS       : thm := realThms4.REAL_ABS_BOUNDS
def REAL_BOUNDS_LE        : thm := realThms4.REAL_BOUNDS_LE
def REAL_BOUNDS_LT        : thm := realThms4.REAL_BOUNDS_LT
def REAL_MIN_MAX          : thm := realThms5.REAL_MIN_MAX
def REAL_MAX_MIN          : thm := realThms5.REAL_MAX_MIN
def REAL_MAX_MAX          : thm := realThms5.REAL_MAX_MAX
def REAL_MIN_MIN          : thm := realThms5.REAL_MIN_MIN
def REAL_MAX_SYM          : thm := realThms5.REAL_MAX_SYM
def REAL_MIN_SYM          : thm := realThms5.REAL_MIN_SYM
def REAL_LE_MAX           : thm := realThms5.REAL_LE_MAX
def REAL_LE_MIN           : thm := realThms5.REAL_LE_MIN
def REAL_LT_MAX           : thm := realThms5.REAL_LT_MAX
def REAL_LT_MIN           : thm := realThms5.REAL_LT_MIN
def REAL_MAX_LE           : thm := realThms5.REAL_MAX_LE
def REAL_MIN_LE           : thm := realThms5.REAL_MIN_LE
def REAL_MAX_LT           : thm := realThms5.REAL_MAX_LT
def REAL_MIN_LT           : thm := realThms5.REAL_MIN_LT
def REAL_MAX_ASSOC        : thm := realThms5.REAL_MAX_ASSOC
def REAL_MIN_ASSOC        : thm := realThms5.REAL_MIN_ASSOC
def REAL_MAX_ACI          : thm := realThms5.REAL_MAX_ACI
def REAL_MIN_ACI          : thm := realThms5.REAL_MIN_ACI
def REAL_ABS_MUL          : thm := realThms6.REAL_ABS_MUL
def REAL_POW_LE           : thm := realThms6.REAL_POW_LE
def REAL_POW_LT           : thm := realThms6.REAL_POW_LT
def REAL_ABS_POW          : thm := realThms6.REAL_ABS_POW
def REAL_LE_LMUL          : thm := realThms6.REAL_LE_LMUL
def REAL_LE_RMUL          : thm := realThms6.REAL_LE_RMUL
def REAL_LT_LMUL          : thm := realThms6.REAL_LT_LMUL
def REAL_LT_RMUL          : thm := realThms6.REAL_LT_RMUL
def REAL_EQ_MUL_LCANCEL   : thm := realThms6.REAL_EQ_MUL_LCANCEL
def REAL_EQ_MUL_RCANCEL   : thm := realThms6.REAL_EQ_MUL_RCANCEL
def REAL_MUL_LINV_UNIQ    : thm := realThms6.REAL_MUL_LINV_UNIQ
def REAL_MUL_RINV_UNIQ    : thm := realThms6.REAL_MUL_RINV_UNIQ
def REAL_INV_INV          : thm := realThms6.REAL_INV_INV
def REAL_EQ_INV2          : thm := realThms6.REAL_EQ_INV2
def REAL_INV_EQ_0         : thm := realThms6.REAL_INV_EQ_0
def REAL_LT_INV           : thm := realThms6.REAL_LT_INV
def REAL_LT_INV_EQ        : thm := realThms6.REAL_LT_INV_EQ
def REAL_INV_NEG          : thm := realThms6.REAL_INV_NEG
def REAL_LE_INV_EQ        : thm := realThms6.REAL_LE_INV_EQ
def REAL_LE_INV           : thm := realThms6.REAL_LE_INV
def REAL_MUL_RINV         : thm := realThms6.REAL_MUL_RINV
def REAL_INV_1            : thm := realThms6.REAL_INV_1
def REAL_INV_EQ_1         : thm := realThms6.REAL_INV_EQ_1
def REAL_DIV_1            : thm := realThms6.REAL_DIV_1
def REAL_DIV_REFL         : thm := realThms6.REAL_DIV_REFL
def REAL_DIV_RMUL         : thm := realThms6.REAL_DIV_RMUL
def REAL_DIV_LMUL         : thm := realThms6.REAL_DIV_LMUL
def REAL_DIV_EQ_1         : thm := realThms6.REAL_DIV_EQ_1
def REAL_ABS_INV          : thm := realThms6.REAL_ABS_INV
def REAL_ABS_DIV          : thm := realThms6.REAL_ABS_DIV
def REAL_INV_MUL          : thm := realThms6.REAL_INV_MUL
def REAL_INV_DIV          : thm := realThms6.REAL_INV_DIV
def REAL_POW_MUL          : thm := realThms6.REAL_POW_MUL
def REAL_POW_INV          : thm := realThms6.REAL_POW_INV
def REAL_INV_POW          : thm := realThms6.REAL_INV_POW
def REAL_POW_DIV          : thm := realThms6.REAL_POW_DIV
def REAL_DIV_EQ_0         : thm := realThms6.REAL_DIV_EQ_0
def REAL_POW_ADD          : thm := realThms6.REAL_POW_ADD
def REAL_POW_NZ           : thm := realThms6.REAL_POW_NZ
def REAL_POW_SUB          : thm := realThms6.REAL_POW_SUB
def REAL_LT_LCANCEL_IMP   : thm := realThms7.REAL_LT_LCANCEL_IMP
def REAL_LT_RCANCEL_IMP   : thm := realThms7.REAL_LT_RCANCEL_IMP
def REAL_LE_LCANCEL_IMP   : thm := realThms7.REAL_LE_LCANCEL_IMP
def REAL_LE_RCANCEL_IMP   : thm := realThms7.REAL_LE_RCANCEL_IMP
def REAL_LE_RMUL_EQ       : thm := realThms7.REAL_LE_RMUL_EQ
def REAL_LE_LMUL_EQ       : thm := realThms7.REAL_LE_LMUL_EQ
def REAL_LT_RMUL_EQ       : thm := realThms7.REAL_LT_RMUL_EQ
def REAL_LT_LMUL_EQ       : thm := realThms7.REAL_LT_LMUL_EQ
def REAL_LE_MUL_EQ        : thm := realThms7.REAL_LE_MUL_EQ
def REAL_LT_MUL_EQ        : thm := realThms7.REAL_LT_MUL_EQ
def REAL_MUL_POS_LT       : thm := realThms7.REAL_MUL_POS_LT
def REAL_MUL_POS_LE       : thm := realThms7.REAL_MUL_POS_LE
def REAL_LE_RDIV_EQ       : thm := realThms7.REAL_LE_RDIV_EQ
def REAL_LE_LDIV_EQ       : thm := realThms7.REAL_LE_LDIV_EQ
def REAL_LT_RDIV_EQ       : thm := realThms7.REAL_LT_RDIV_EQ
def REAL_LT_LDIV_EQ       : thm := realThms7.REAL_LT_LDIV_EQ
def REAL_EQ_RDIV_EQ       : thm := realThms7.REAL_EQ_RDIV_EQ
def REAL_EQ_LDIV_EQ       : thm := realThms7.REAL_EQ_LDIV_EQ
def REAL_LT_DIV2_EQ       : thm := realThms7.REAL_LT_DIV2_EQ
def REAL_LE_DIV2_EQ       : thm := realThms7.REAL_LE_DIV2_EQ
def REAL_MUL_2            : thm := realThms7.REAL_MUL_2
def REAL_POW_EQ_0         : thm := realThms7.REAL_POW_EQ_0
def REAL_LE_MUL2          : thm := realThms7.REAL_LE_MUL2
def REAL_LT_MUL2          : thm := realThms7.REAL_LT_MUL2
def REAL_LT_SQUARE        : thm := realThms7.REAL_LT_SQUARE
def REAL_POW_1            : thm := realThms7.REAL_POW_1
def REAL_POW_ONE          : thm := realThms7.REAL_POW_ONE
def REAL_LT_INV2          : thm := realThms7.REAL_LT_INV2
def REAL_LE_INV2          : thm := realThms7.REAL_LE_INV2
def REAL_LT_LINV          : thm := realThms7.REAL_LT_LINV
def REAL_LT_RINV          : thm := realThms7.REAL_LT_RINV
def REAL_LE_LINV          : thm := realThms7.REAL_LE_LINV
def REAL_LE_RINV          : thm := realThms7.REAL_LE_RINV
def REAL_INV_LE_1         : thm := realThms7.REAL_INV_LE_1
def REAL_INV_1_LE         : thm := realThms7.REAL_INV_1_LE
def REAL_INV_LT_1         : thm := realThms7.REAL_INV_LT_1
def REAL_INV_1_LT         : thm := realThms7.REAL_INV_1_LT
def REAL_SUB_INV          : thm := realThms7.REAL_SUB_INV
def REAL_DOWN             : thm := realThms7.REAL_DOWN
def REAL_DOWN2            : thm := realThms7.REAL_DOWN2
def REAL_POW_LE2          : thm := realThms7.REAL_POW_LE2
def REAL_POW_LE_1         : thm := realThms8.REAL_POW_LE_1
def REAL_POW_1_LE         : thm := realThms8.REAL_POW_1_LE
def REAL_POW_MONO         : thm := realThms8.REAL_POW_MONO
def REAL_POW_LT2          : thm := realThms8.REAL_POW_LT2
def REAL_POW_LT_1         : thm := realThms8.REAL_POW_LT_1
def REAL_POW_1_LT         : thm := realThms8.REAL_POW_1_LT
def REAL_POW_MONO_LT      : thm := realThms8.REAL_POW_MONO_LT
def REAL_POW_POW          : thm := realThms8.REAL_POW_POW
def REAL_EQ_RCANCEL_IMP   : thm := realThms8.REAL_EQ_RCANCEL_IMP
def REAL_EQ_LCANCEL_IMP   : thm := realThms8.REAL_EQ_LCANCEL_IMP
def REAL_LT_DIV           : thm := realThms8.REAL_LT_DIV
def REAL_LE_DIV           : thm := realThms8.REAL_LE_DIV
def REAL_DIV_POW2         : thm := realThms8.REAL_DIV_POW2
def REAL_DIV_POW2_ALT     : thm := realThms8.REAL_DIV_POW2_ALT
def REAL_LT_POW2          : thm := realThms8.REAL_LT_POW2
def REAL_LE_POW2          : thm := realThms8.REAL_LE_POW2
def REAL_POW2_ABS         : thm := realThms8.REAL_POW2_ABS
def REAL_LE_SQUARE_ABS    : thm := realThms8.REAL_LE_SQUARE_ABS
def REAL_LT_SQUARE_ABS    : thm := realThms8.REAL_LT_SQUARE_ABS
def REAL_EQ_SQUARE_ABS    : thm := realThms8.REAL_EQ_SQUARE_ABS
def REAL_LE_POW_2         : thm := realThms8.REAL_LE_POW_2
def REAL_LT_POW_2         : thm := realThms8.REAL_LT_POW_2
def REAL_SOS_EQ_0         : thm := realThms8.REAL_SOS_EQ_0
def REAL_POW_ZERO         : thm := realThms8.REAL_POW_ZERO
def REAL_POW_MONO_INV     : thm := realThms8.REAL_POW_MONO_INV
def REAL_POW_LE2_REV      : thm := realThms8.REAL_POW_LE2_REV
def REAL_POW_LT2_REV      : thm := realThms8.REAL_POW_LT2_REV
def REAL_POW_EQ           : thm := realThms8.REAL_POW_EQ
def REAL_POW_EQ_ABS       : thm := realThms8.REAL_POW_EQ_ABS
def REAL_POW_EQ_1_IMP     : thm := realThms8.REAL_POW_EQ_1_IMP
def REAL_POW_EQ_1         : thm := realThms8.REAL_POW_EQ_1
def REAL_POW_LT2_ODD      : thm := realThms8.REAL_POW_LT2_ODD
def REAL_POW_LE2_ODD      : thm := realThms8.REAL_POW_LE2_ODD
def REAL_POW_LT2_ODD_EQ   : thm := realThms8.REAL_POW_LT2_ODD_EQ
def REAL_POW_LE2_ODD_EQ   : thm := realThms8.REAL_POW_LE2_ODD_EQ
def REAL_POW_EQ_ODD_EQ    : thm := realThms8.REAL_POW_EQ_ODD_EQ
def REAL_POW_EQ_ODD       : thm := realThms8.REAL_POW_EQ_ODD
def REAL_POW_EQ_EQ        : thm := realThms8.REAL_POW_EQ_EQ
def REAL_EVENPOW_ABS      : thm := realThms8.REAL_EVENPOW_ABS
def REAL_OF_NUM_MOD       : thm := realThms8.REAL_OF_NUM_MOD
def REAL_OF_NUM_DIV       : thm := realThms8.REAL_OF_NUM_DIV
def REAL_CONVEX_BOUND2_LT : thm := realThms9.REAL_CONVEX_BOUND2_LT
def REAL_CONVEX_BOUND2_LE : thm := realThms9.REAL_CONVEX_BOUND2_LE
def REAL_CONVEX_BOUND_LT  : thm := realThms9.REAL_CONVEX_BOUND_LT
def REAL_CONVEX_BOUND_LE  : thm := realThms9.REAL_CONVEX_BOUND_LE
def REAL_CONVEX_BOUND_GT  : thm := realThms9.REAL_CONVEX_BOUND_GT
def REAL_CONVEX_BOUND_GE  : thm := realThms9.REAL_CONVEX_BOUND_GE
def REAL_CONVEX_BOUNDS_LE : thm := realThms9.REAL_CONVEX_BOUNDS_LE
def REAL_CONVEX_BOUNDS_LT : thm := realThms9.REAL_CONVEX_BOUNDS_LT
def REAL_ARCH_SIMPLE      : thm := realThms9.REAL_ARCH_SIMPLE
def REAL_ARCH_LT          : thm := realThms9.REAL_ARCH_LT
def REAL_ARCH             : thm := realThms9.REAL_ARCH
def REAL_ARCH_INV         : thm := realThms9.REAL_ARCH_INV
def REAL_POW_LBOUND       : thm := realThms9.REAL_POW_LBOUND
def REAL_ARCH_POW         : thm := realThms9.REAL_ARCH_POW
def REAL_ARCH_POW2        : thm := realThms9.REAL_ARCH_POW2
def REAL_ARCH_POW_INV     : thm := realThms9.REAL_ARCH_POW_INV
def real_sgn              : thm := realThms10.real_sgn
def REAL_SGN_0            : thm := realThms10.REAL_SGN_0
def REAL_SGN_NEG          : thm := realThms10.REAL_SGN_NEG
def REAL_SGN_ABS          : thm := realThms10.REAL_SGN_ABS
def REAL_SGN_ABS_ALT      : thm := realThms10.REAL_SGN_ABS_ALT
def REAL_EQ_SGN_ABS       : thm := realThms10.REAL_EQ_SGN_ABS
def REAL_ABS_SGN          : thm := realThms10.REAL_ABS_SGN
def REAL_SGN              : thm := realThms10.REAL_SGN
def REAL_SGN_MUL          : thm := realThms10.REAL_SGN_MUL
def REAL_SGN_INV          : thm := realThms10.REAL_SGN_INV
def REAL_SGN_DIV          : thm := realThms10.REAL_SGN_DIV
def REAL_SGN_EQ           : thm := realThms10.REAL_SGN_EQ
def REAL_SGN_CASES        : thm := realThms10.REAL_SGN_CASES
def REAL_SGN_INEQS        : thm := realThms10.REAL_SGN_INEQS
def REAL_SGN_POW          : thm := realThms10.REAL_SGN_POW
def REAL_SGN_POW_2        : thm := realThms10.REAL_SGN_POW_2
def REAL_SGN_REAL_SGN     : thm := realThms10.REAL_SGN_REAL_SGN
def REAL_INV_SGN          : thm := realThms10.REAL_INV_SGN
def REAL_SGN_EQ_INEQ      : thm := realThms10.REAL_SGN_EQ_INEQ
def REAL_SGNS_EQ          : thm := realThms10.REAL_SGNS_EQ
def REAL_SGNS_EQ_ALT      : thm := realThms10.REAL_SGNS_EQ_ALT
def REAL_WLOG_LE          : thm := realThms10.REAL_WLOG_LE
def REAL_WLOG_LT          : thm := realThms10.REAL_WLOG_LT
def REAL_WLOG_LE_3        : thm := realThms10.REAL_WLOG_LE_3
def sqrt                  : thm := realThms11.sqrt
def SQRT_UNIQUE           : thm := realThms11.SQRT_UNIQUE
def POW_2_SQRT            : thm := realThms11.POW_2_SQRT
def SQRT_0                : thm := realThms11.SQRT_0
def SQRT_1                : thm := realThms11.SQRT_1
def POW_2_SQRT_ABS        : thm := realThms11.POW_2_SQRT_ABS
def SQRT_WORKS_GEN        : thm := realThms11.SQRT_WORKS_GEN
def SQRT_UNIQUE_GEN       : thm := realThms11.SQRT_UNIQUE_GEN
def SQRT_NEG              : thm := realThms11.SQRT_NEG
def REAL_SGN_SQRT         : thm := realThms11.REAL_SGN_SQRT
def SQRT_WORKS            : thm := realThms11.SQRT_WORKS
def REAL_POS_EQ_SQUARE    : thm := realThms11.REAL_POS_EQ_SQUARE
def SQRT_POS_LE           : thm := realThms11.SQRT_POS_LE
def SQRT_POW_2            : thm := realThms11.SQRT_POW_2
def SQRT_POW2             : thm := realThms11.SQRT_POW2
def SQRT_MUL              : thm := realThms11.SQRT_MUL
def SQRT_INV              : thm := realThms11.SQRT_INV
def SQRT_DIV              : thm := realThms11.SQRT_DIV
def SQRT_LT_0             : thm := realThms11.SQRT_LT_0
def SQRT_EQ_0             : thm := realThms11.SQRT_EQ_0
def SQRT_LE_0             : thm := realThms11.SQRT_LE_0
def REAL_ABS_SQRT         : thm := realThms11.REAL_ABS_SQRT
def SQRT_MONO_LT          : thm := realThms11.SQRT_MONO_LT
def SQRT_MONO_LE          : thm := realThms11.SQRT_MONO_LE
def SQRT_MONO_LT_EQ       : thm := realThms11.SQRT_MONO_LT_EQ
def SQRT_MONO_LE_EQ       : thm := realThms11.SQRT_MONO_LE_EQ
def SQRT_INJ              : thm := realThms11.SQRT_INJ
def SQRT_EQ_1             : thm := realThms11.SQRT_EQ_1
def SQRT_POS_LT           : thm := realThms11.SQRT_POS_LT
def REAL_LE_LSQRT         : thm := realThms11.REAL_LE_LSQRT
def REAL_LE_RSQRT         : thm := realThms11.REAL_LE_RSQRT
def REAL_LT_LSQRT         : thm := realThms11.REAL_LT_LSQRT
def REAL_LT_RSQRT         : thm := realThms11.REAL_LT_RSQRT
def SQRT_EVEN_POW2        : thm := realThms11.SQRT_EVEN_POW2
def REAL_DIV_SQRT         : thm := realThms11.REAL_DIV_SQRT
def REAL_RSQRT_LE         : thm := realThms11.REAL_RSQRT_LE
def REAL_LSQRT_LE         : thm := realThms11.REAL_LSQRT_LE
def REAL_SQRT_POW_2       : thm := realThms11.REAL_SQRT_POW_2
def REAL_ABS_LE_SQRT_POS  : thm := realThms11.REAL_ABS_LE_SQRT_POS
def REAL_ABS_LE_SQRT      : thm := realThms11.REAL_ABS_LE_SQRT

/- ---------------------------------------------------------------------- -/

end Session
