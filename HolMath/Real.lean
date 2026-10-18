/- File: Real.lean
More basic properties of the reals.
Original       John Harrison, University of Cambridge Computer Laboratory
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Original (c) Copyright, Valentina Bruno 2010
Lean4 translation by Chris Walton 2026

Basic properties of the reals.  The theorems are grouped into eleven bundles
(`RealThms1..11`) in `HolMath.Real`, so they do not collide with
`HolMath.RealAx.RealThms`.  `REAL_ARITH` throughout is realarith.ml's
(Session's `REAL_ARITH2`); `ASM_REAL_ARITH_TAC` is not here, it arrives with
`calc_rat.ml`. -/

import HolMath.RealArith
import HolMath.Base

namespace HolMath.Real

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax

/- ---------------------------------------------------------------------- -/
/- Additional commutativity properties of the inclusion map.              -/
/- ---------------------------------------------------------------------- -/

/-- real.ml 14-102. -/
structure RealThms1 where
  REAL_OF_NUM_LT        : thm
  REAL_OF_NUM_GE        : thm
  REAL_OF_NUM_GT        : thm
  REAL_OF_NUM_MAX       : thm
  REAL_OF_NUM_MIN       : thm
  REAL_OF_NUM_SUC       : thm
  REAL_OF_NUM_SUB       : thm
  REAL_OF_NUM_SUB_CASES : thm
  REAL_OF_NUM_CLAUSES   : thm
  REAL_MUL_AC           : thm
  REAL_ADD_RDISTRIB     : thm
  REAL_LT_LADD_IMP      : thm
  REAL_LT_MUL           : thm
  deriving Inhabited

/-- `K` supplies `REAL_OF_NUM_POW`, which calc_int.ml proves. -/
@[nospecialize]
def setupRealThms1 [HolBase]
    (A1 : HolMath.Arith.ArithThms1) (A2 : HolMath.Arith.ArithThms2)
    (A3 : HolMath.Arith.ArithThms3) (A4 : HolMath.Arith.ArithThms4)
    (A5 : HolMath.Arith.ArithThms5)
    (K : HolMath.CalcInt.CalcIntThms)
    (R : HolMath.RealAx.RealThms)
    (L : HolMath.RealArith.RealArithLemmas)
    (MESON_TAC : List thm → tactic)
    (ASM_MESON_TAC : List thm → tactic) :
    ExceptT String IO RealThms1 := do
  let C := HolBase.C
  let CONTRAPOS_CONV : ioconv := fun t => pure (HolCore.Classic.CONTRAPOS_CONV
    C.contraposConvPth (mk_var "a" bool_ty) (mk_var "b" bool_ty) t)
  let { ADD1, .. } := A1
  let { GE, GT, MAX, MIN, .. } := A2
  let { LE_CASES, NOT_LE, .. } := A3
  let { LE_EXISTS, .. } := A4
  let { ADD_SUB2, .. } := A5
  let { REAL_OF_NUM_POW, .. } := K
  let { REAL_ADD_SYM, REAL_ADD_ASSOC, REAL_ADD_LID, REAL_ADD_LINV,
        REAL_MUL_SYM, REAL_MUL_ASSOC, REAL_ADD_LDISTRIB, REAL_LE_LADD_IMP,
        REAL_LE_MUL, REAL_OF_NUM_EQ, REAL_OF_NUM_LE, REAL_OF_NUM_ADD,
        REAL_OF_NUM_MUL, real_sub, real_lt, real_ge, real_gt, real_max,
        real_min, .. } := R
  let { REAL_NEG_SUB, REAL_LT_LE, REAL_ENTIRE, .. } := L
  let { COND_RAND, .. } := C

  let REAL_OF_NUM_LT ← prove
   r"!m n. &m < &n <=> m < n"
   (REWRITE_TAC [real_lt, ← GSYM NOT_LE, REAL_OF_NUM_LE])

  let REAL_OF_NUM_GE ← prove
   r"!m n. &m >= &n <=> m >= n"
   (REWRITE_TAC [GE, real_ge, REAL_OF_NUM_LE])

  let REAL_OF_NUM_GT ← prove
   r"!m n. &m > &n <=> m > n"
   (REWRITE_TAC [GT, real_gt, REAL_OF_NUM_LT])

  let REAL_OF_NUM_MAX ← prove
   r"!m n. max (&m) (&n) = &(MAX m n)"
   (REWRITE_TAC [REAL_OF_NUM_LE, MAX, real_max, ← GSYM COND_RAND])

  let REAL_OF_NUM_MIN ← prove
   r"!m n. min (&m) (&n) = &(MIN m n)"
   (REWRITE_TAC [REAL_OF_NUM_LE, MIN, real_min, ← GSYM COND_RAND])

  let REAL_OF_NUM_SUC ← prove
   r"!n. &n + &1 = &(SUC n)"
   (REWRITE_TAC [ADD1, REAL_OF_NUM_ADD])

  let REAL_OF_NUM_SUB ← prove
   r"!m n. m <= n ==> (&n - &m = &(n - m))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [LE_EXISTS] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [ADD_SUB2] THEN
    REWRITE_TAC [← GSYM REAL_OF_NUM_ADD] THEN
    ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
    REWRITE_TAC [real_sub, ← GSYM REAL_ADD_ASSOC] THEN
    MESON_TAC [REAL_ADD_LINV, REAL_ADD_SYM, REAL_ADD_LID])

  let REAL_OF_NUM_SUB_CASES ← prove
   r"!m n. &m - &n = if n <= m then &(m - n) else -- &(n - m)"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [REAL_OF_NUM_SUB] THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_NEG_SUB] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC REAL_OF_NUM_SUB THEN ASM_MESON_TAC [LE_CASES])

  let REAL_OF_NUM_CLAUSES ← prove
   r"(!m n. &m:real = &n <=> m = n) /\
   (!m n. &m:real >= &n <=> m >= n) /\
   (!m n. &m:real > &n <=> m > n) /\
   (!m n. &m:real <= &n <=> m <= n) /\
   (!m n. &m:real < &n <=> m < n) /\
   (!m n. max (&m) (&n):real = &(MAX m n)) /\
   (!m n. min (&m) (&n):real = &(MIN m n)) /\
   (!m n. &m + &n:real = &(m + n)) /\
   (!m n. &m * &n:real = &(m * n)) /\
   (!x n. (&x:real) pow n = &(x EXP n))"
   (REWRITE_TAC [REAL_OF_NUM_EQ, REAL_OF_NUM_GE, REAL_OF_NUM_GT,
                 REAL_OF_NUM_LE, REAL_OF_NUM_LT, REAL_OF_NUM_MAX,
                 REAL_OF_NUM_MIN, REAL_OF_NUM_ADD, REAL_OF_NUM_MUL,
                 REAL_OF_NUM_POW])

  /- ---------------------------------------------------------------------- -/
  /- A few theorems we need to prove explicitly for later.                  -/
  /- ---------------------------------------------------------------------- -/

  let REAL_MUL_AC ← prove
   r"(m * n = n * m) /\
   ((m * n) * p = m * (n * p)) /\
   (m * (n * p) = n * (m * p))"
   (REWRITE_TAC [REAL_MUL_ASSOC, ← EQT_INTRO (← SPEC_ALL REAL_MUL_SYM)] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_MUL_SYM)

  let REAL_ADD_RDISTRIB ← prove
   r"!x y z. (x + y) * z = x * z + y * z"
   (MESON_TAC [REAL_MUL_SYM, REAL_ADD_LDISTRIB])

  let REAL_LT_LADD_IMP ← prove
   r"!x y z. y < z ==> x + y < x + z"
   (REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
    REWRITE_TAC [real_lt] THEN
    DISCH_THEN (MP_TAC o MATCH_MP REAL_LE_LADD_IMP) THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"--x")) THEN
    REWRITE_TAC [REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_LID])

  let REAL_LT_MUL ← prove
   r"!x y. &0 < x /\ &0 < y ==> &0 < x * y"
   (REPEAT GEN_TAC THEN REWRITE_TAC [REAL_LT_LE] THEN
    CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [REAL_ENTIRE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC [])

  return {
    REAL_OF_NUM_LT, REAL_OF_NUM_GE, REAL_OF_NUM_GT, REAL_OF_NUM_MAX,
    REAL_OF_NUM_MIN, REAL_OF_NUM_SUC, REAL_OF_NUM_SUB, REAL_OF_NUM_SUB_CASES,
    REAL_OF_NUM_CLAUSES, REAL_MUL_AC, REAL_ADD_RDISTRIB, REAL_LT_LADD_IMP,
    REAL_LT_MUL }

/- ---------------------------------------------------------------------- -/
/- Tactic version of REAL_ARITH.                                          -/
/- ---------------------------------------------------------------------- -/

/-- `let REAL_ARITH_TAC = CONV_TAC REAL_ARITH` (real.ml 106).  `REAL_ARITH`
    is realarith.ml's (Session's `REAL_ARITH2`). -/
def REAL_ARITH_TAC [HolBase]
    (REAL_ARITH : term → IO (Except String thm)) : tactic :=
  CONV_TAC REAL_ARITH

/- ---------------------------------------------------------------------- -/
/- Prove all the linear theorems we can blow away automatically.          -/
/- ---------------------------------------------------------------------- -/

/-- real.ml 109-255. -/
structure RealThms2 where
  REAL_EQ_ADD_LCANCEL_0 : thm
  REAL_EQ_ADD_RCANCEL_0 : thm
  REAL_LNEG_UNIQ        : thm
  REAL_RNEG_UNIQ        : thm
  REAL_NEG_LMUL         : thm
  REAL_NEG_RMUL         : thm
  REAL_NEG_MUL2         : thm
  REAL_LT_LADD          : thm
  REAL_LT_RADD          : thm
  REAL_LT_ANTISYM       : thm
  REAL_LT_GT            : thm
  REAL_NOT_EQ           : thm
  REAL_NOT_LE           : thm
  REAL_LET_ANTISYM      : thm
  REAL_NEG_LT0          : thm
  REAL_NEG_GT0          : thm
  REAL_NEG_LE0          : thm
  REAL_NEG_GE0          : thm
  REAL_LT_TOTAL         : thm
  REAL_LT_NEGTOTAL      : thm
  REAL_LE_01            : thm
  REAL_LT_01            : thm
  REAL_LE_LADD          : thm
  REAL_LE_RADD          : thm
  REAL_LT_ADD2          : thm
  REAL_LE_ADD2          : thm
  REAL_LT_LNEG          : thm
  REAL_LT_RNEG          : thm
  REAL_LT_ADDNEG        : thm
  REAL_LT_ADDNEG2       : thm
  REAL_LT_ADD1          : thm
  REAL_SUB_ADD          : thm
  REAL_SUB_ADD2         : thm
  REAL_SUB_REFL         : thm
  REAL_LE_DOUBLE        : thm
  REAL_LE_NEGL          : thm
  deriving Inhabited

@[nospecialize]
def setupRealThms2 [HolBase]
    (REAL_ARITH : term → IO (Except String thm))
    (R : HolMath.RealAx.RealThms)
    (K : HolMath.CalcInt.CalcIntThms) :
    ExceptT String IO RealThms2 := do
  let REAL_ARITH_TAC := REAL_ARITH_TAC REAL_ARITH
  let { real_lt, .. } := R
  let { REAL_ADD_AC, REAL_LE_LNEG, REAL_LE_RNEG, .. } := K

  let REAL_EQ_ADD_LCANCEL_0 ← prove
   r"!x y. (x + y = x) <=> (y = &0)"
   REAL_ARITH_TAC

  let REAL_EQ_ADD_RCANCEL_0 ← prove
   r"!x y. (x + y = y) <=> (x = &0)"
   REAL_ARITH_TAC

  let REAL_LNEG_UNIQ ← prove
   r"!x y. (x + y = &0) <=> (x = --y)"
   REAL_ARITH_TAC

  let REAL_RNEG_UNIQ ← prove
   r"!x y. (x + y = &0) <=> (y = --x)"
   REAL_ARITH_TAC

  let REAL_NEG_LMUL ← prove
   r"!x y. --(x * y) = (--x) * y"
   REAL_ARITH_TAC

  let REAL_NEG_RMUL ← prove
   r"!x y. --(x * y) = x * (--y)"
   REAL_ARITH_TAC

  let REAL_NEG_MUL2 ← prove
   r"!x y. (--x) * (--y) = x * y"
   REAL_ARITH_TAC

  let REAL_LT_LADD ← prove
   r"!x y z. (x + y) < (x + z) <=> y < z"
   REAL_ARITH_TAC

  let REAL_LT_RADD ← prove
   r"!x y z. (x + z) < (y + z) <=> x < y"
   REAL_ARITH_TAC

  let REAL_LT_ANTISYM ← prove
   r"!x y. ~(x < y /\ y < x)"
   REAL_ARITH_TAC

  let REAL_LT_GT ← prove
   r"!x y. x < y ==> ~(y < x)"
   REAL_ARITH_TAC

  let REAL_NOT_EQ ← prove
   r"!x y. ~(x = y) <=> x < y \/ y < x"
   REAL_ARITH_TAC

  let REAL_NOT_LE ← prove
   r"!x y. ~(x <= y) <=> y < x"
   REAL_ARITH_TAC

  let REAL_LET_ANTISYM ← prove
   r"!x y. ~(x <= y /\ y < x)"
   REAL_ARITH_TAC

  let REAL_NEG_LT0 ← prove
   r"!x. (--x) < &0 <=> &0 < x"
   REAL_ARITH_TAC

  let REAL_NEG_GT0 ← prove
   r"!x. &0 < (--x) <=> x < &0"
   REAL_ARITH_TAC

  let REAL_NEG_LE0 ← prove
   r"!x. (--x) <= &0 <=> &0 <= x"
   REAL_ARITH_TAC

  let REAL_NEG_GE0 ← prove
   r"!x. &0 <= (--x) <=> x <= &0"
   REAL_ARITH_TAC

  let REAL_LT_TOTAL ← prove
   r"!x y. (x = y) \/ x < y \/ y < x"
   REAL_ARITH_TAC

  let REAL_LT_NEGTOTAL ← prove
   r"!x. (x = &0) \/ (&0 < x) \/ (&0 < --x)"
   REAL_ARITH_TAC

  let REAL_LE_01 ← prove
   r"&0 <= &1"
   REAL_ARITH_TAC

  let REAL_LT_01 ← prove
   r"&0 < &1"
   REAL_ARITH_TAC

  let REAL_LE_LADD ← prove
   r"!x y z. (x + y) <= (x + z) <=> y <= z"
   REAL_ARITH_TAC

  let REAL_LE_RADD ← prove
   r"!x y z. (x + z) <= (y + z) <=> x <= y"
   REAL_ARITH_TAC

  let REAL_LT_ADD2 ← prove
   r"!w x y z. w < x /\ y < z ==> (w + y) < (x + z)"
   REAL_ARITH_TAC

  let REAL_LE_ADD2 ← prove
   r"!w x y z. w <= x /\ y <= z ==> (w + y) <= (x + z)"
   REAL_ARITH_TAC

  let REAL_LT_LNEG ← prove
   r"!x y. --x < y <=> &0 < x + y"
   (REWRITE_TAC [real_lt, REAL_LE_RNEG, REAL_ADD_AC])

  let REAL_LT_RNEG ← prove
   r"!x y. x < --y <=> x + y < &0"
   (REWRITE_TAC [real_lt, REAL_LE_LNEG, REAL_ADD_AC])

  let REAL_LT_ADDNEG ← prove
   r"!x y z. y < (x + (--z)) <=> (y + z) < x"
   REAL_ARITH_TAC

  let REAL_LT_ADDNEG2 ← prove
   r"!x y z. (x + (--y)) < z <=> x < (z + y)"
   REAL_ARITH_TAC

  let REAL_LT_ADD1 ← prove
   r"!x y. x <= y ==> x < (y + &1)"
   REAL_ARITH_TAC

  let REAL_SUB_ADD ← prove
   r"!x y. (x - y) + y = x"
   REAL_ARITH_TAC

  let REAL_SUB_ADD2 ← prove
   r"!x y. y + (x - y) = x"
   REAL_ARITH_TAC

  let REAL_SUB_REFL ← prove
   r"!x. x - x = &0"
   REAL_ARITH_TAC

  let REAL_LE_DOUBLE ← prove
   r"!x. &0 <= x + x <=> &0 <= x"
   REAL_ARITH_TAC

  let REAL_LE_NEGL ← prove
   r"!x. (--x <= x) <=> (&0 <= x)"
   REAL_ARITH_TAC

  return { REAL_EQ_ADD_LCANCEL_0, REAL_EQ_ADD_RCANCEL_0, REAL_LNEG_UNIQ,
           REAL_RNEG_UNIQ, REAL_NEG_LMUL, REAL_NEG_RMUL, REAL_NEG_MUL2,
           REAL_LT_LADD, REAL_LT_RADD, REAL_LT_ANTISYM, REAL_LT_GT,
           REAL_NOT_EQ, REAL_NOT_LE, REAL_LET_ANTISYM, REAL_NEG_LT0,
           REAL_NEG_GT0, REAL_NEG_LE0, REAL_NEG_GE0, REAL_LT_TOTAL,
           REAL_LT_NEGTOTAL, REAL_LE_01, REAL_LT_01, REAL_LE_LADD,
           REAL_LE_RADD, REAL_LT_ADD2, REAL_LE_ADD2, REAL_LT_LNEG,
           REAL_LT_RNEG, REAL_LT_ADDNEG, REAL_LT_ADDNEG2, REAL_LT_ADD1,
           REAL_SUB_ADD, REAL_SUB_ADD2, REAL_SUB_REFL, REAL_LE_DOUBLE,
           REAL_LE_NEGL }

/-- real.ml 256-400. -/
structure RealThms3 where
  REAL_LE_NEGR      : thm
  REAL_NEG_EQ_0     : thm
  REAL_ADD_SUB      : thm
  REAL_NEG_EQ       : thm
  REAL_NEG_MINUS1   : thm
  REAL_LT_IMP_NE    : thm
  REAL_LE_ADDR      : thm
  REAL_LE_ADDL      : thm
  REAL_LT_ADDR      : thm
  REAL_LT_ADDL      : thm
  REAL_SUB_SUB      : thm
  REAL_LT_ADD_SUB   : thm
  REAL_LT_SUB_RADD  : thm
  REAL_LT_SUB_LADD  : thm
  REAL_LE_SUB_LADD  : thm
  REAL_LE_SUB_RADD  : thm
  REAL_ADD2_SUB2    : thm
  REAL_SUB_LZERO    : thm
  REAL_SUB_RZERO    : thm
  REAL_LET_ADD2     : thm
  REAL_LTE_ADD2     : thm
  REAL_SUB_LNEG     : thm
  REAL_SUB_RNEG     : thm
  REAL_SUB_NEG2     : thm
  REAL_SUB_TRIANGLE : thm
  REAL_EQ_SUB_LADD  : thm
  REAL_EQ_SUB_RADD  : thm
  REAL_SUB_SUB2     : thm
  REAL_ADD_SUB2     : thm
  REAL_EQ_IMP_LE    : thm
  REAL_LT_IMP_NZ    : thm
  REAL_DIFFSQ       : thm
  REAL_EQ_NEG2      : thm
  REAL_LT_NEG2      : thm
  REAL_SUB_LDISTRIB : thm
  REAL_SUB_RDISTRIB : thm
  deriving Inhabited

@[nospecialize]
def setupRealThms3 [HolBase]
    (REAL_ARITH : term → IO (Except String thm)) :
    ExceptT String IO RealThms3 := do
  let REAL_ARITH_TAC := REAL_ARITH_TAC REAL_ARITH

  let REAL_LE_NEGR ← prove
   r"!x. (x <= --x) <=> (x <= &0)"
   REAL_ARITH_TAC

  let REAL_NEG_EQ_0 ← prove
   r"!x. (--x = &0) <=> (x = &0)"
   REAL_ARITH_TAC

  let REAL_ADD_SUB ← prove
   r"!x y. (x + y) - x = y"
   REAL_ARITH_TAC

  let REAL_NEG_EQ ← prove
   r"!x y. (--x = y) <=> (x = --y)"
   REAL_ARITH_TAC

  let REAL_NEG_MINUS1 ← prove
   r"!x. --x = (--(&1)) * x"
   REAL_ARITH_TAC

  let REAL_LT_IMP_NE ← prove
   r"!x y. x < y ==> ~(x = y)"
   REAL_ARITH_TAC

  let REAL_LE_ADDR ← prove
   r"!x y. x <= x + y <=> &0 <= y"
   REAL_ARITH_TAC

  let REAL_LE_ADDL ← prove
   r"!x y. y <= x + y <=> &0 <= x"
   REAL_ARITH_TAC

  let REAL_LT_ADDR ← prove
   r"!x y. x < x + y <=> &0 < y"
   REAL_ARITH_TAC

  let REAL_LT_ADDL ← prove
   r"!x y. y < x + y <=> &0 < x"
   REAL_ARITH_TAC

  let REAL_SUB_SUB ← prove
   r"!x y. (x - y) - x = --y"
   REAL_ARITH_TAC

  let REAL_LT_ADD_SUB ← prove
   r"!x y z. (x + y) < z <=> x < (z - y)"
   REAL_ARITH_TAC

  let REAL_LT_SUB_RADD ← prove
   r"!x y z. (x - y) < z <=> x < z + y"
   REAL_ARITH_TAC

  let REAL_LT_SUB_LADD ← prove
   r"!x y z. x < (y - z) <=> (x + z) < y"
   REAL_ARITH_TAC

  let REAL_LE_SUB_LADD ← prove
   r"!x y z. x <= (y - z) <=> (x + z) <= y"
   REAL_ARITH_TAC

  let REAL_LE_SUB_RADD ← prove
   r"!x y z. (x - y) <= z <=> x <= z + y"
   REAL_ARITH_TAC

  let REAL_ADD2_SUB2 ← prove
   r"!a b c d. (a + b) - (c + d) = (a - c) + (b - d)"
   REAL_ARITH_TAC

  let REAL_SUB_LZERO ← prove
   r"!x. &0 - x = --x"
   REAL_ARITH_TAC

  let REAL_SUB_RZERO ← prove
   r"!x. x - &0 = x"
   REAL_ARITH_TAC

  let REAL_LET_ADD2 ← prove
   r"!w x y z. w <= x /\ y < z ==> (w + y) < (x + z)"
   REAL_ARITH_TAC

  let REAL_LTE_ADD2 ← prove
   r"!w x y z. w < x /\ y <= z ==> w + y < x + z"
   REAL_ARITH_TAC

  let REAL_SUB_LNEG ← prove
   r"!x y. (--x) - y = --(x + y)"
   REAL_ARITH_TAC

  let REAL_SUB_RNEG ← prove
   r"!x y. x - (--y) = x + y"
   REAL_ARITH_TAC

  let REAL_SUB_NEG2 ← prove
   r"!x y. (--x) - (--y) = y - x"
   REAL_ARITH_TAC

  let REAL_SUB_TRIANGLE ← prove
   r"!a b c. (a - b) + (b - c) = a - c"
   REAL_ARITH_TAC

  let REAL_EQ_SUB_LADD ← prove
   r"!x y z. (x = y - z) <=> (x + z = y)"
   REAL_ARITH_TAC

  let REAL_EQ_SUB_RADD ← prove
   r"!x y z. (x - y = z) <=> (x = z + y)"
   REAL_ARITH_TAC

  let REAL_SUB_SUB2 ← prove
   r"!x y. x - (x - y) = y"
   REAL_ARITH_TAC

  let REAL_ADD_SUB2 ← prove
   r"!x y. x - (x + y) = --y"
   REAL_ARITH_TAC

  let REAL_EQ_IMP_LE ← prove
   r"!x y. (x = y) ==> x <= y"
   REAL_ARITH_TAC

  let REAL_LT_IMP_NZ ← prove
   r"!x. &0 < x ==> ~(x = &0)"
   REAL_ARITH_TAC

  let REAL_DIFFSQ ← prove
   r"!x y. (x + y) * (x - y) = (x * x) - (y * y)"
   REAL_ARITH_TAC

  let REAL_EQ_NEG2 ← prove
   r"!x y. (--x = --y) <=> (x = y)"
   REAL_ARITH_TAC

  let REAL_LT_NEG2 ← prove
   r"!x y. --x < --y <=> y < x"
   REAL_ARITH_TAC

  let REAL_SUB_LDISTRIB ← prove
   r"!x y z. x * (y - z) = x * y - x * z"
   REAL_ARITH_TAC

  let REAL_SUB_RDISTRIB ← prove
   r"!x y z. (x - y) * z = x * z - y * z"
   REAL_ARITH_TAC

  return { REAL_LE_NEGR, REAL_NEG_EQ_0, REAL_ADD_SUB, REAL_NEG_EQ,
           REAL_NEG_MINUS1, REAL_LT_IMP_NE, REAL_LE_ADDR, REAL_LE_ADDL,
           REAL_LT_ADDR, REAL_LT_ADDL, REAL_SUB_SUB, REAL_LT_ADD_SUB,
           REAL_LT_SUB_RADD, REAL_LT_SUB_LADD, REAL_LE_SUB_LADD,
           REAL_LE_SUB_RADD, REAL_ADD2_SUB2, REAL_SUB_LZERO, REAL_SUB_RZERO,
           REAL_LET_ADD2, REAL_LTE_ADD2, REAL_SUB_LNEG, REAL_SUB_RNEG,
           REAL_SUB_NEG2, REAL_SUB_TRIANGLE, REAL_EQ_SUB_LADD,
           REAL_EQ_SUB_RADD, REAL_SUB_SUB2, REAL_ADD_SUB2, REAL_EQ_IMP_LE,
           REAL_LT_IMP_NZ, REAL_DIFFSQ, REAL_EQ_NEG2, REAL_LT_NEG2,
           REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB }

/- ---------------------------------------------------------------------- -/
/- Theorems about "abs".                                                  -/
/- ---------------------------------------------------------------------- -/

/-- real.ml 401-510. -/
structure RealThms4 where
  REAL_ABS_ZERO     : thm
  REAL_ABS_0        : thm
  REAL_ABS_1        : thm
  REAL_ABS_TRIANGLE : thm
  REAL_ABS_TRIANGLE_LE : thm
  REAL_ABS_TRIANGLE_LT : thm
  REAL_ABS_POS      : thm
  REAL_ABS_SUB      : thm
  REAL_ABS_NZ       : thm
  REAL_ABS_ABS      : thm
  REAL_ABS_LE       : thm
  REAL_ABS_REFL     : thm
  REAL_ABS_BETWEEN  : thm
  REAL_ABS_BOUND    : thm
  REAL_ABS_STILLNZ  : thm
  REAL_ABS_CASES    : thm
  REAL_ABS_BETWEEN1 : thm
  REAL_ABS_SIGN     : thm
  REAL_ABS_SIGN2    : thm
  REAL_ABS_CIRCLE   : thm
  REAL_SUB_ABS      : thm
  REAL_ABS_SUB_ABS  : thm
  REAL_ABS_BETWEEN2 : thm
  REAL_ABS_BOUNDS   : thm
  REAL_BOUNDS_LE    : thm
  REAL_BOUNDS_LT    : thm
  deriving Inhabited

@[nospecialize]
def setupRealThms4 [HolBase]
    (REAL_ARITH : term → IO (Except String thm)) :
    ExceptT String IO RealThms4 := do
  let REAL_ARITH_TAC := REAL_ARITH_TAC REAL_ARITH

  let REAL_ABS_ZERO ← prove
   r"!x. (abs(x) = &0) <=> (x = &0)"
   REAL_ARITH_TAC

  let REAL_ABS_0 ← prove
   r"abs(&0) = &0"
   REAL_ARITH_TAC

  let REAL_ABS_1 ← prove
   r"abs(&1) = &1"
   REAL_ARITH_TAC

  let REAL_ABS_TRIANGLE ← prove
   r"!x y. abs(x + y) <= abs(x) + abs(y)"
   REAL_ARITH_TAC

  let REAL_ABS_TRIANGLE_LE ← prove
   r"!x y z.abs(x) + abs(y - x) <= z ==> abs(y) <= z"
   REAL_ARITH_TAC

  let REAL_ABS_TRIANGLE_LT ← prove
   r"!x y z.abs(x) + abs(y - x) < z ==> abs(y) < z"
   REAL_ARITH_TAC

  let REAL_ABS_POS ← prove
   r"!x. &0 <= abs(x)"
   REAL_ARITH_TAC

  let REAL_ABS_SUB ← prove
   r"!x y. abs(x - y) = abs(y - x)"
   REAL_ARITH_TAC

  let REAL_ABS_NZ ← prove
   r"!x. ~(x = &0) <=> &0 < abs(x)"
   REAL_ARITH_TAC

  let REAL_ABS_ABS ← prove
   r"!x. abs(abs(x)) = abs(x)"
   REAL_ARITH_TAC

  let REAL_ABS_LE ← prove
   r"!x. x <= abs(x)"
   REAL_ARITH_TAC

  let REAL_ABS_REFL ← prove
   r"!x. (abs(x) = x) <=> &0 <= x"
   REAL_ARITH_TAC

  let REAL_ABS_BETWEEN ← prove
   r"!x y d. &0 < d /\ ((x - d) < y) /\ (y < (x + d)) <=> abs(y - x) < d"
   REAL_ARITH_TAC

  let REAL_ABS_BOUND ← prove
   r"!x y d. abs(x - y) < d ==> y < (x + d)"
   REAL_ARITH_TAC

  let REAL_ABS_STILLNZ ← prove
   r"!x y. abs(x - y) < abs(y) ==> ~(x = &0)"
   REAL_ARITH_TAC

  let REAL_ABS_CASES ← prove
   r"!x. (x = &0) \/ &0 < abs(x)"
   REAL_ARITH_TAC

  let REAL_ABS_BETWEEN1 ← prove
   r"!x y z. x < z /\ (abs(y - x)) < (z - x) ==> y < z"
   REAL_ARITH_TAC

  let REAL_ABS_SIGN ← prove
   r"!x y. abs(x - y) < y ==> &0 < x"
   REAL_ARITH_TAC

  let REAL_ABS_SIGN2 ← prove
   r"!x y. abs(x - y) < --y ==> x < &0"
   REAL_ARITH_TAC

  let REAL_ABS_CIRCLE ← prove
   r"!x y h. abs(h) < (abs(y) - abs(x)) ==> abs(x + h) < abs(y)"
   REAL_ARITH_TAC

  let REAL_SUB_ABS ← prove
   r"!x y. (abs(x) - abs(y)) <= abs(x - y)"
   REAL_ARITH_TAC

  let REAL_ABS_SUB_ABS ← prove
   r"!x y. abs(abs(x) - abs(y)) <= abs(x - y)"
   REAL_ARITH_TAC

  let REAL_ABS_BETWEEN2 ← prove
   r"!x0 x y0 y. x0 < y0 /\ &2 * abs(x - x0) < (y0 - x0) /\
                          &2 * abs(y - y0) < (y0 - x0)
        ==> x < y"
   REAL_ARITH_TAC

  let REAL_ABS_BOUNDS ← prove
   r"!x k. abs(x) <= k <=> --k <= x /\ x <= k"
   REAL_ARITH_TAC

  let REAL_BOUNDS_LE ← prove
   r"!x k. --k <= x /\ x <= k <=> abs(x) <= k"
   REAL_ARITH_TAC

  let REAL_BOUNDS_LT ← prove
   r"!x k. --k < x /\ x < k <=> abs(x) < k"
   REAL_ARITH_TAC

  return { REAL_ABS_ZERO, REAL_ABS_0, REAL_ABS_1, REAL_ABS_TRIANGLE,
           REAL_ABS_TRIANGLE_LE, REAL_ABS_TRIANGLE_LT, REAL_ABS_POS,
           REAL_ABS_SUB, REAL_ABS_NZ, REAL_ABS_ABS, REAL_ABS_LE, REAL_ABS_REFL,
           REAL_ABS_BETWEEN, REAL_ABS_BOUND, REAL_ABS_STILLNZ, REAL_ABS_CASES,
           REAL_ABS_BETWEEN1, REAL_ABS_SIGN, REAL_ABS_SIGN2, REAL_ABS_CIRCLE,
           REAL_SUB_ABS, REAL_ABS_SUB_ABS, REAL_ABS_BETWEEN2, REAL_ABS_BOUNDS,
           REAL_BOUNDS_LE, REAL_BOUNDS_LT }

/- ---------------------------------------------------------------------- -/
/- Theorems about max and min.                                            -/
/- ---------------------------------------------------------------------- -/

/-- real.ml 511-594. -/
structure RealThms5 where
  REAL_MIN_MAX   : thm
  REAL_MAX_MIN   : thm
  REAL_MAX_MAX   : thm
  REAL_MIN_MIN   : thm
  REAL_MAX_SYM   : thm
  REAL_MIN_SYM   : thm
  REAL_LE_MAX    : thm
  REAL_LE_MIN    : thm
  REAL_LT_MAX    : thm
  REAL_LT_MIN    : thm
  REAL_MAX_LE    : thm
  REAL_MIN_LE    : thm
  REAL_MAX_LT    : thm
  REAL_MIN_LT    : thm
  REAL_MAX_ASSOC : thm
  REAL_MIN_ASSOC : thm
  REAL_MAX_ACI   : thm
  REAL_MIN_ACI   : thm
  deriving Inhabited

@[nospecialize]
def setupRealThms5 [HolBase]
    (REAL_ARITH : term → IO (Except String thm)) :
    ExceptT String IO RealThms5 := do
  let REAL_ARITH_TAC := REAL_ARITH_TAC REAL_ARITH

  let REAL_MIN_MAX ← prove
   r"!x y. min x y = --(max (--x) (--y))"
   REAL_ARITH_TAC

  let REAL_MAX_MIN ← prove
   r"!x y. max x y = --(min (--x) (--y))"
   REAL_ARITH_TAC

  let REAL_MAX_MAX ← prove
   r"!x y. x <= max x y /\ y <= max x y"
   REAL_ARITH_TAC

  let REAL_MIN_MIN ← prove
   r"!x y. min x y <= x /\ min x y <= y"
   REAL_ARITH_TAC

  let REAL_MAX_SYM ← prove
   r"!x y. max x y = max y x"
   REAL_ARITH_TAC

  let REAL_MIN_SYM ← prove
   r"!x y. min x y = min y x"
   REAL_ARITH_TAC

  let REAL_LE_MAX ← prove
   r"!x y z. z <= max x y <=> z <= x \/ z <= y"
   REAL_ARITH_TAC

  let REAL_LE_MIN ← prove
   r"!x y z. z <= min x y <=> z <= x /\ z <= y"
   REAL_ARITH_TAC

  let REAL_LT_MAX ← prove
   r"!x y z. z < max x y <=> z < x \/ z < y"
   REAL_ARITH_TAC

  let REAL_LT_MIN ← prove
   r"!x y z. z < min x y <=> z < x /\ z < y"
   REAL_ARITH_TAC

  let REAL_MAX_LE ← prove
   r"!x y z. max x y <= z <=> x <= z /\ y <= z"
   REAL_ARITH_TAC

  let REAL_MIN_LE ← prove
   r"!x y z. min x y <= z <=> x <= z \/ y <= z"
   REAL_ARITH_TAC

  let REAL_MAX_LT ← prove
   r"!x y z. max x y < z <=> x < z /\ y < z"
   REAL_ARITH_TAC

  let REAL_MIN_LT ← prove
   r"!x y z. min x y < z <=> x < z \/ y < z"
   REAL_ARITH_TAC

  let REAL_MAX_ASSOC ← prove
   r"!x y z. max x (max y z) = max (max x y) z"
   REAL_ARITH_TAC

  let REAL_MIN_ASSOC ← prove
   r"!x y z. min x (min y z) = min (min x y) z"
   REAL_ARITH_TAC

  let REAL_MAX_ACI ← prove
   r"(max x y = max y x) /\
   (max (max x y) z = max x (max y z)) /\
   (max x (max y z) = max y (max x z)) /\
   (max x x = x) /\
   (max x (max x y) = max x y)"
   REAL_ARITH_TAC

  let REAL_MIN_ACI ← prove
   r"(min x y = min y x) /\
   (min (min x y) z = min x (min y z)) /\
   (min x (min y z) = min y (min x z)) /\
   (min x x = x) /\
   (min x (min x y) = min x y)"
   REAL_ARITH_TAC

  return { REAL_MIN_MAX, REAL_MAX_MIN, REAL_MAX_MAX, REAL_MIN_MIN,
           REAL_MAX_SYM, REAL_MIN_SYM, REAL_LE_MAX, REAL_LE_MIN, REAL_LT_MAX,
           REAL_LT_MIN, REAL_MAX_LE, REAL_MIN_LE, REAL_MAX_LT, REAL_MIN_LT,
           REAL_MAX_ASSOC, REAL_MIN_ASSOC, REAL_MAX_ACI, REAL_MIN_ACI }

/- ---------------------------------------------------------------------- -/
/- To simplify backchaining, just as in the natural number case.          -/
/- ---------------------------------------------------------------------- -/

/-- The `pth`s that `REAL_LE_IMP` and `REAL_LET_IMP` close over. -/
structure RealBackchain where
  le_pth  : thm
  let_pth : thm
  deriving Inhabited

@[nospecialize]
def setupRealBackchain [HolBase] (IMP_CONJ REAL_LE_TRANS REAL_LET_TRANS : thm) :
    ExceptT String IO RealBackchain := do
  let le_pth ← PURE_ONCE_REWRITE_RULE [IMP_CONJ] REAL_LE_TRANS
  let let_pth ← PURE_ONCE_REWRITE_RULE [IMP_CONJ] REAL_LET_TRANS
  return { le_pth, let_pth }

/-- `REAL_LE_IMP` (real.ml 597): `fun th -> GEN_ALL(MATCH_MP pth (SPEC_ALL th))`. -/
def REAL_LE_IMP [HolBase] (bc : RealBackchain) (th : thm) : IO (Except String thm) :=
  (do GEN_ALL (← MATCH_MP bc.le_pth (← SPEC_ALL th))).run

/-- `REAL_LET_IMP` (real.ml 601). -/
def REAL_LET_IMP [HolBase] (bc : RealBackchain) (th : thm) : IO (Except String thm) :=
  (do GEN_ALL (← MATCH_MP bc.let_pth (← SPEC_ALL th))).run

/- ---------------------------------------------------------------------- -/
/- Now a bit of nonlinear stuff.                                          -/
/- ---------------------------------------------------------------------- -/

/-- real.ml 607-855. -/
structure RealThms6 where
  REAL_ABS_MUL        : thm
  REAL_POW_LE         : thm
  REAL_POW_LT         : thm
  REAL_ABS_POW        : thm
  REAL_LE_LMUL        : thm
  REAL_LE_RMUL        : thm
  REAL_LT_LMUL        : thm
  REAL_LT_RMUL        : thm
  REAL_EQ_MUL_LCANCEL : thm
  REAL_EQ_MUL_RCANCEL : thm
  REAL_MUL_LINV_UNIQ  : thm
  REAL_MUL_RINV_UNIQ  : thm
  REAL_INV_INV        : thm
  REAL_EQ_INV2        : thm
  REAL_INV_EQ_0       : thm
  REAL_LT_INV         : thm
  REAL_LT_INV_EQ      : thm
  REAL_INV_NEG        : thm
  REAL_LE_INV_EQ      : thm
  REAL_LE_INV         : thm
  REAL_MUL_RINV       : thm
  REAL_INV_1          : thm
  REAL_INV_EQ_1       : thm
  REAL_DIV_1          : thm
  REAL_DIV_REFL       : thm
  REAL_DIV_RMUL       : thm
  REAL_DIV_LMUL       : thm
  REAL_DIV_EQ_1       : thm
  REAL_ABS_INV        : thm
  REAL_ABS_DIV        : thm
  REAL_INV_MUL        : thm
  REAL_INV_DIV        : thm
  REAL_POW_MUL        : thm
  REAL_POW_INV        : thm
  REAL_INV_POW        : thm
  REAL_POW_DIV        : thm
  REAL_DIV_EQ_0       : thm
  REAL_POW_ADD        : thm
  REAL_POW_NZ         : thm
  REAL_POW_SUB        : thm
  deriving Inhabited

/-- `REAL_ARITH` is realarith.ml's (Session's `REAL_ARITH2`). -/
@[nospecialize]
def setupRealThms6 [HolBase]
    (N : HolMath.Nums.NumsThms)
    (A1 : HolMath.Arith.ArithThms1) (A4 : HolMath.Arith.ArithThms4)
    (A5 : HolMath.Arith.ArithThms5)
    (CnA : HolMath.CalcNum.ArithRewrites)
    (R : HolMath.RealAx.RealThms)
    (K : HolMath.CalcInt.CalcIntThms)
    (L : HolMath.RealArith.RealArithLemmas)
    (T1 : RealThms1) (T2 : RealThms2) (T3 : RealThms3) (T4 : RealThms4)
    (REAL_ARITH' : term → IO (Except String thm))
    (MESON_TAC : List thm → tactic)
    (ASM_MESON_TAC : List thm → tactic) :
    ExceptT String IO RealThms6 := do
  let REAL_ARITH (t : term) : ExceptT String IO thm := REAL_ARITH' t
  let REAL_ARITH_TAC := REAL_ARITH_TAC REAL_ARITH'
  let INDUCT_TAC := HolMath.Nums.INDUCT_TAC N.num_INDUCTION
  let { REAL_OF_NUM_LT, REAL_MUL_AC, REAL_LT_MUL, .. } := T1
  let { REAL_LT_NEGTOTAL, REAL_LT_01, REAL_LT_RNEG, .. } := T2
  let { REAL_SUB_RZERO, REAL_SUB_LDISTRIB, .. } := T3
  let { REAL_ABS_0, REAL_ABS_1, .. } := T4
  let { REAL_ADD_LID, REAL_MUL_SYM, REAL_MUL_ASSOC, REAL_MUL_LID, REAL_LE_MUL, REAL_INV_0, REAL_MUL_LINV, REAL_OF_NUM_EQ,
        real_abs, real_pow, real_div, .. } := R
  let { REAL_MUL_RZERO, REAL_MUL_LZERO, REAL_NEG_NEG, REAL_MUL_RNEG,
        REAL_MUL_LNEG, REAL_NEG_0, REAL_ABS_NUM, REAL_ABS_NEG, .. } := K
  let { REAL_LE_LT, REAL_ENTIRE, REAL_LE_NEGTOTAL,
        REAL_MUL_RID, REAL_POS, .. } := L
  let { ADD_CLAUSES, .. } := A1
  let { LE_EXISTS, .. } := A4
  let { ADD_SUB2, .. } := A5
  let { ARITH_EQ, ARITH, .. } := CnA

  let REAL_ABS_MUL ← prove
   r"!x y. abs(x * y) = abs(x) * abs(y)"
   (REPEAT GEN_TAC THEN
    DISJ_CASES_TAC (← SPEC (← q r"x:real") REAL_LE_NEGTOTAL) THENL
     [ALL_TAC,
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [← GSYM REAL_ABS_NEG]] THEN
    (DISJ_CASES_TAC (← SPEC (← q r"y:real") REAL_LE_NEGTOTAL) THENL
      [ALL_TAC,
       GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [← GSYM REAL_ABS_NEG]]) THEN
    ASSUM_LIST (MP_TAC o MATCH_MP REAL_LE_MUL o end_itlist CONJ o rev) THEN
    REWRITE_TAC [REAL_MUL_LNEG, REAL_MUL_RNEG, REAL_NEG_NEG] THEN DISCH_TAC THENL
     [ALL_TAC,
      GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_ABS_NEG],
      GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_ABS_NEG],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [real_abs, REAL_MUL_LNEG, REAL_MUL_RNEG, REAL_NEG_NEG])

  let REAL_POW_LE ← prove
   r"!x n. &0 <= x ==> &0 <= x pow n"
   (REPEAT STRIP_TAC THEN SPEC_TAC ((← q r"n:num"), (← q r"n:num")) THEN
    INDUCT_TAC THEN REWRITE_TAC [real_pow, REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC [])

  let REAL_POW_LT ← prove
   r"!x n. &0 < x ==> &0 < x pow n"
   (REPEAT STRIP_TAC THEN SPEC_TAC ((← q r"n:num"), (← q r"n:num")) THEN
    INDUCT_TAC THEN REWRITE_TAC [real_pow, REAL_LT_01] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC [])

  let REAL_ABS_POW ← prove
   r"!x n. abs(x pow n) = abs(x) pow n"
   (GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [real_pow, REAL_ABS_NUM, REAL_ABS_MUL])

  let REAL_LE_LMUL ← prove
   r"!x y z. &0 <= x /\ y <= z ==> x * y <= x * z"
   (ONCE_REWRITE_TAC [← REAL_ARITH (← q r"x <= y <=> &0 <= y - x")] THEN
    REWRITE_TAC [← GSYM REAL_SUB_LDISTRIB, REAL_SUB_RZERO, REAL_LE_MUL])

  let REAL_LE_RMUL ← prove
   r"!x y z. x <= y /\ &0 <= z ==> x * z <= y * z"
   (MESON_TAC [REAL_MUL_SYM, REAL_LE_LMUL])

  let REAL_LT_LMUL ← prove
   r"!x y z. &0 < x /\ y < z ==> x * y < x * z"
   (ONCE_REWRITE_TAC [← REAL_ARITH (← q r"x < y <=> &0 < y - x")] THEN
    REWRITE_TAC [← GSYM REAL_SUB_LDISTRIB, REAL_SUB_RZERO, REAL_LT_MUL])

  let REAL_LT_RMUL ← prove
   r"!x y z. x < y /\ &0 < z ==> x * z < y * z"
   (MESON_TAC [REAL_MUL_SYM, REAL_LT_LMUL])

  let REAL_EQ_MUL_LCANCEL ← prove
   r"!x y z. (x * y = x * z) <=> (x = &0) \/ (y = z)"
   (REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"(x = y) <=> (x - y = &0)")] THEN
    REWRITE_TAC [← GSYM REAL_SUB_LDISTRIB, REAL_ENTIRE, REAL_SUB_RZERO])

  let REAL_EQ_MUL_RCANCEL ← prove
   r"!x y z. (x * z = y * z) <=> (x = y) \/ (z = &0)"
   (ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    REWRITE_TAC [REAL_EQ_MUL_LCANCEL] THEN
    MESON_TAC [])

  let REAL_MUL_LINV_UNIQ ← prove
   r"!x y. (x * y = &1) ==> (inv(y) = x)"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"y = &0") THEN
    ASM_REWRITE_TAC [REAL_MUL_RZERO, REAL_OF_NUM_EQ, ARITH_EQ] THEN
    FIRST_ASSUM (SUBST1_TAC o SYM o MATCH_MP REAL_MUL_LINV) THEN
    ASM_REWRITE_TAC [REAL_EQ_MUL_RCANCEL] THEN
    DISCH_THEN (ACCEPT_TAC o SYM))

  let REAL_MUL_RINV_UNIQ ← prove
   r"!x y. (x * y = &1) ==> (inv(x) = y)"
   (ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    MATCH_ACCEPT_TAC REAL_MUL_LINV_UNIQ)

  let REAL_INV_INV ← prove
   r"!x. inv(inv x) = x"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"x = &0") THEN
    ASM_REWRITE_TAC [REAL_INV_0] THEN
    MATCH_MP_TAC REAL_MUL_RINV_UNIQ THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN
    ASM_REWRITE_TAC [])

  let REAL_EQ_INV2 ← prove
   r"!x y. inv(x) = inv(y) <=> x = y"
   (MESON_TAC [REAL_INV_INV])

  let REAL_INV_EQ_0 ← prove
   r"!x. inv(x) = &0 <=> x = &0"
   (GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [REAL_INV_0] THEN
    ONCE_REWRITE_TAC [← GSYM REAL_INV_INV] THEN ASM_REWRITE_TAC [REAL_INV_0])

  let REAL_LT_INV ← prove
   r"!x. &0 < x ==> &0 < inv(x)"
   (GEN_TAC THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (← SPEC (← q r"inv(x)") REAL_LT_NEGTOTAL) THEN
    ASM_REWRITE_TAC [] THENL
     [RULE_ASSUM_TAC (REWRITE_RULE [REAL_INV_EQ_0]) THEN ASM_REWRITE_TAC [],
      DISCH_TAC THEN SUBGOAL_THEN (← q r"&0 < --(inv x) * x") MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC [],
        REWRITE_TAC [REAL_MUL_LNEG]]] THEN
    SUBGOAL_THEN (← q r"inv(x) * x = &1") SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_MUL_LINV THEN
      UNDISCH_TAC (← q r"&0 < x") THEN REAL_ARITH_TAC,
      REWRITE_TAC [REAL_LT_RNEG, REAL_ADD_LID, REAL_OF_NUM_LT, ARITH]])

  let REAL_LT_INV_EQ ← prove
   r"!x. &0 < inv x <=> &0 < x"
   (GEN_TAC THEN EQ_TAC THEN REWRITE_TAC [REAL_LT_INV] THEN
    GEN_REWRITE_TAC (funpow 2 RAND_CONV) [← GSYM REAL_INV_INV] THEN
    REWRITE_TAC [REAL_LT_INV])

  let REAL_INV_NEG ← prove
   r"!x. inv(--x) = --(inv x)"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"x = &0") THEN
    ASM_REWRITE_TAC [REAL_NEG_0, REAL_INV_0] THEN
    MATCH_MP_TAC REAL_MUL_LINV_UNIQ THEN
    REWRITE_TAC [REAL_MUL_LNEG, REAL_MUL_RNEG, REAL_NEG_NEG] THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC [])

  let REAL_LE_INV_EQ ← prove
   r"!x. &0 <= inv x <=> &0 <= x"
   (REWRITE_TAC [REAL_LE_LT, REAL_LT_INV_EQ, REAL_INV_EQ_0] THEN
    MESON_TAC [REAL_INV_EQ_0])

  let REAL_LE_INV ← prove
   r"!x. &0 <= x ==> &0 <= inv(x)"
   (REWRITE_TAC [REAL_LE_INV_EQ])

  let REAL_MUL_RINV ← prove
   r"!x. ~(x = &0) ==> (x * inv(x) = &1)"
   (ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    REWRITE_TAC [REAL_MUL_LINV])

  let REAL_INV_1 ← prove
   r"inv(&1) = &1"
   (MATCH_MP_TAC REAL_MUL_RINV_UNIQ THEN
    REWRITE_TAC [REAL_MUL_LID])

  let REAL_INV_EQ_1 ← prove
   r"!x. inv(x) = &1 <=> x = &1"
   (MESON_TAC [REAL_INV_INV, REAL_INV_1])

  let REAL_DIV_1 ← prove
   r"!x. x / &1 = x"
   (REWRITE_TAC [real_div, REAL_INV_1, REAL_MUL_RID])

  let REAL_DIV_REFL ← prove
   r"!x. ~(x = &0) ==> (x / x = &1)"
   (GEN_TAC THEN REWRITE_TAC [real_div, REAL_MUL_RINV])

  let REAL_DIV_RMUL ← prove
   r"!x y. ~(y = &0) ==> ((x / y) * y = x)"
   (SIMP_TAC [real_div, ← GSYM REAL_MUL_ASSOC, REAL_MUL_LINV, REAL_MUL_RID])

  let REAL_DIV_LMUL ← prove
   r"!x y. ~(y = &0) ==> (y * (x / y) = x)"
   (ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN REWRITE_TAC [REAL_DIV_RMUL])

  let REAL_DIV_EQ_1 ← prove
   r"!x y:real. x / y = &1 <=> x = y /\ ~(x = &0) /\ ~(y = &0)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [real_div] THEN
    ASM_CASES_TAC (← q r"x = &0") THEN ASM_REWRITE_TAC [REAL_MUL_LZERO] THEN
    ASM_CASES_TAC (← q r"y = &0") THEN ASM_REWRITE_TAC [REAL_INV_0, REAL_MUL_RZERO] THEN
    REWRITE_TAC [REAL_OF_NUM_EQ, ARITH] THEN
    EQ_TAC THEN ASM_SIMP_TAC [← GSYM real_div, REAL_DIV_REFL] THEN
    DISCH_THEN (MP_TAC o AP_TERM (← q r"( * ) (y:real)")) THEN
    ASM_SIMP_TAC [REAL_DIV_LMUL, REAL_MUL_RID])

  let REAL_ABS_INV ← prove
   r"!x. abs(inv x) = inv(abs x)"
   (GEN_TAC THEN CONV_TAC SYM_CONV THEN
    ASM_CASES_TAC (← q r"x = &0") THEN ASM_REWRITE_TAC [REAL_INV_0, REAL_ABS_0] THEN
    MATCH_MP_TAC REAL_MUL_RINV_UNIQ THEN
    REWRITE_TAC [← GSYM REAL_ABS_MUL] THEN
    POP_ASSUM (SUBST1_TAC o MATCH_MP REAL_MUL_RINV) THEN
    REWRITE_TAC [REAL_ABS_1])

  let REAL_ABS_DIV ← prove
   r"!x y. abs(x / y) = abs(x) / abs(y)"
   (REWRITE_TAC [real_div, REAL_ABS_INV, REAL_ABS_MUL])

  let REAL_INV_MUL ← prove
   r"!x y. inv(x * y) = inv(x) * inv(y)"
   (REPEAT GEN_TAC THEN
    MAP_EVERY ASM_CASES_TAC [← q r"x = &0", ← q r"y = &0"] THEN
    ASM_REWRITE_TAC [REAL_INV_0, REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
    MATCH_MP_TAC REAL_MUL_LINV_UNIQ THEN
    ONCE_REWRITE_TAC [← AC REAL_MUL_AC (← q r"(a * b) * (c * d) = (a * c) * (b * d)")] THEN
    EVERY_ASSUM (SUBST1_TAC o MATCH_MP REAL_MUL_LINV) THEN
    REWRITE_TAC [REAL_MUL_LID])

  let REAL_INV_DIV ← prove
   r"!x y. inv(x / y) = y / x"
   (REWRITE_TAC [real_div, REAL_INV_INV, REAL_INV_MUL] THEN
    MATCH_ACCEPT_TAC REAL_MUL_SYM)

  let REAL_POW_MUL ← prove
   r"!x y n. (x * y) pow n = (x pow n) * (y pow n)"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [real_pow, REAL_MUL_LID, REAL_MUL_AC])

  let REAL_POW_INV ← prove
   r"!x n. (inv x) pow n = inv(x pow n)"
   (GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [real_pow, REAL_INV_1, REAL_INV_MUL])

  let REAL_INV_POW ← prove
   r"!x n. inv(x pow n) = (inv x) pow n"
   (REWRITE_TAC [REAL_POW_INV])

  let REAL_POW_DIV ← prove
   r"!x y n. (x / y) pow n = (x pow n) / (y pow n)"
   (REWRITE_TAC [real_div, REAL_POW_MUL, REAL_POW_INV])

  let REAL_DIV_EQ_0 ← prove
   r"!x y. x / y = &0 <=> x = &0 \/ y = &0"
   (REWRITE_TAC [real_div, REAL_INV_EQ_0, REAL_ENTIRE])

  let REAL_POW_ADD ← prove
   r"!x m n. x pow (m + n) = x pow m * x pow n"
   (GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [ADD_CLAUSES, real_pow, REAL_MUL_LID, REAL_MUL_ASSOC])

  let REAL_POW_NZ ← prove
   r"!x n. ~(x = &0) ==> ~(x pow n = &0)"
   (GEN_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC [real_pow, REAL_OF_NUM_EQ, ARITH] THEN
    ASM_MESON_TAC [REAL_ENTIRE])

  let REAL_POW_SUB ← prove
   r"!x m n. ~(x = &0) /\ m <= n ==> (x pow (n - m) = x pow n / x pow m)"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC [LE_EXISTS] THEN
    DISCH_THEN (CHOOSE_THEN SUBST1_TAC) THEN
    REWRITE_TAC [ADD_SUB2] THEN REWRITE_TAC [REAL_POW_ADD] THEN
    REWRITE_TAC [real_div] THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_MUL_LID] THEN
    REWRITE_TAC [REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_MUL_LINV THEN
    MATCH_MP_TAC REAL_POW_NZ THEN ASM_REWRITE_TAC [])

  return {
    REAL_ABS_MUL, REAL_POW_LE, REAL_POW_LT, REAL_ABS_POW, REAL_LE_LMUL,
    REAL_LE_RMUL, REAL_LT_LMUL, REAL_LT_RMUL, REAL_EQ_MUL_LCANCEL,
    REAL_EQ_MUL_RCANCEL, REAL_MUL_LINV_UNIQ, REAL_MUL_RINV_UNIQ, REAL_INV_INV,
    REAL_EQ_INV2, REAL_INV_EQ_0, REAL_LT_INV, REAL_LT_INV_EQ, REAL_INV_NEG,
    REAL_LE_INV_EQ, REAL_LE_INV, REAL_MUL_RINV, REAL_INV_1, REAL_INV_EQ_1,
    REAL_DIV_1, REAL_DIV_REFL, REAL_DIV_RMUL, REAL_DIV_LMUL, REAL_DIV_EQ_1,
    REAL_ABS_INV, REAL_ABS_DIV, REAL_INV_MUL, REAL_INV_DIV, REAL_POW_MUL,
    REAL_POW_INV, REAL_INV_POW, REAL_POW_DIV, REAL_DIV_EQ_0, REAL_POW_ADD,
    REAL_POW_NZ, REAL_POW_SUB }

/-- real.ml 856-1114. -/
structure RealThms7 where
  REAL_LT_LCANCEL_IMP : thm
  REAL_LT_RCANCEL_IMP : thm
  REAL_LE_LCANCEL_IMP : thm
  REAL_LE_RCANCEL_IMP : thm
  REAL_LE_RMUL_EQ     : thm
  REAL_LE_LMUL_EQ     : thm
  REAL_LT_RMUL_EQ     : thm
  REAL_LT_LMUL_EQ     : thm
  REAL_LE_MUL_EQ      : thm
  REAL_LT_MUL_EQ      : thm
  REAL_MUL_POS_LT     : thm
  REAL_MUL_POS_LE     : thm
  REAL_LE_RDIV_EQ     : thm
  REAL_LE_LDIV_EQ     : thm
  REAL_LT_RDIV_EQ     : thm
  REAL_LT_LDIV_EQ     : thm
  REAL_EQ_RDIV_EQ     : thm
  REAL_EQ_LDIV_EQ     : thm
  REAL_LT_DIV2_EQ     : thm
  REAL_LE_DIV2_EQ     : thm
  REAL_MUL_2          : thm
  REAL_POW_EQ_0       : thm
  REAL_LE_MUL2        : thm
  REAL_LT_MUL2        : thm
  REAL_LT_SQUARE      : thm
  REAL_POW_1          : thm
  REAL_POW_ONE        : thm
  REAL_LT_INV2        : thm
  REAL_LE_INV2        : thm
  REAL_LT_LINV        : thm
  REAL_LT_RINV        : thm
  REAL_LE_LINV        : thm
  REAL_LE_RINV        : thm
  REAL_INV_LE_1       : thm
  REAL_INV_1_LE       : thm
  REAL_INV_LT_1       : thm
  REAL_INV_1_LT       : thm
  REAL_SUB_INV        : thm
  REAL_DOWN           : thm
  REAL_DOWN2          : thm
  REAL_POW_LE2        : thm
  deriving Inhabited

@[nospecialize]
def setupRealThms7 [HolBase]
    (N : HolMath.Nums.NumsThms)
    (R : HolMath.RealAx.RealThms)
    (K : HolMath.CalcInt.CalcIntThms)
    (L : HolMath.RealArith.RealArithLemmas)
    (T1 : RealThms1) (T2 : RealThms2) (T3 : RealThms3) (T6 : RealThms6)
    (num_CONV' : term → IO (Except String thm))
    (REAL_ARITH' : term → IO (Except String thm))
    (MESON_TAC : List thm → tactic) :
    ExceptT String IO RealThms7 := do
  let num_CONV (t : term) : ExceptT String IO thm := num_CONV' t
  let REAL_ARITH (t : term) : ExceptT String IO thm := REAL_ARITH' t
  let REAL_ARITH_TAC := REAL_ARITH_TAC REAL_ARITH'
  let INDUCT_TAC := HolMath.Nums.INDUCT_TAC N.num_INDUCTION
  let { REAL_LT_MUL, .. } := T1
  let { REAL_NOT_LE, REAL_LT_NEGTOTAL, REAL_LT_01, .. } := T2
  let { REAL_LT_IMP_NZ, REAL_SUB_RDISTRIB, .. } := T3
  let { REAL_POW_LE, REAL_LE_LMUL, REAL_LE_RMUL, REAL_LT_LMUL, REAL_LT_RMUL,
        REAL_EQ_MUL_LCANCEL, REAL_INV_INV, REAL_LT_INV, REAL_LT_INV_EQ,
        REAL_MUL_RINV, REAL_INV_1, REAL_DIV_LMUL, REAL_INV_MUL, .. } := T6
  let { REAL_MUL_SYM, REAL_MUL_ASSOC, REAL_MUL_LID, REAL_LE_REFL,
        REAL_LE_ANTISYM, REAL_LE_TRANS, REAL_LE_TOTAL, REAL_MUL_LINV, real_pow,
        real_div, .. } := R
  let { REAL_MUL_RZERO, REAL_MUL_LZERO, .. } := K
  let { REAL_LT_IMP_LE, REAL_LET_TRANS, REAL_LE_LT, REAL_LT_LE, REAL_LT_REFL,
        REAL_ENTIRE, REAL_LE_SQUARE, REAL_MUL_RID, .. } := L
  let { NOT_SUC, .. } := N
  let { EQ_SYM_EQ, .. } := HolBase.T

  let REAL_LT_LCANCEL_IMP ← prove
   r"!x y z. &0 < x /\ x * y < x * z ==> y < z"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (fun th => tactic_of do pure (
      ASSUME_TAC (← CONJUNCT1 th) THEN MP_TAC th)) THEN DISCH_THEN
     (MP_TAC o uncurry CONJ o (F_F (MATCH_MP REAL_LT_INV) (pure : thm → ExceptT String IO thm)) o CONJ_PAIR) THEN
    DISCH_THEN (MP_TAC o MATCH_MP REAL_LT_LMUL) THEN
    POP_ASSUM (ASSUME_TAC o MATCH_MP REAL_MUL_LINV o MATCH_MP REAL_LT_IMP_NZ) THEN
    ASM_REWRITE_TAC [REAL_MUL_ASSOC, REAL_MUL_LID])

  let REAL_LT_RCANCEL_IMP ← prove
   r"!x y z. &0 < z /\ x * z < y * z ==> x < y"
   (ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN REWRITE_TAC [REAL_LT_LCANCEL_IMP])

  let REAL_LE_LCANCEL_IMP ← prove
   r"!x y z. &0 < x /\ x * y <= x * z ==> y <= z"
   (REPEAT GEN_TAC THEN REWRITE_TAC [REAL_LE_LT, REAL_EQ_MUL_LCANCEL] THEN
    ASM_CASES_TAC (← q r"x = &0") THEN ASM_REWRITE_TAC [REAL_LT_REFL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN DISJ1_TAC THEN
    MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN
    EXISTS_TAC (← q r"x:real") THEN ASM_REWRITE_TAC [])

  let REAL_LE_RCANCEL_IMP ← prove
   r"!x y z. &0 < z /\ x * z <= y * z ==> x <= y"
   (ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN REWRITE_TAC [REAL_LE_LCANCEL_IMP])

  let REAL_LE_RMUL_EQ ← prove
   r"!x y z. &0 < z ==> (x * z <= y * z <=> x <= y)"
   (MESON_TAC [REAL_LE_RMUL, REAL_LE_RCANCEL_IMP, REAL_LT_IMP_LE])

  let REAL_LE_LMUL_EQ ← prove
   r"!x y z. &0 < z ==> (z * x <= z * y <=> x <= y)"
   (MESON_TAC [REAL_LE_RMUL_EQ, REAL_MUL_SYM])

  let REAL_LT_RMUL_EQ ← prove
   r"!x y z. &0 < z ==> (x * z < y * z <=> x < y)"
   (SIMP_TAC [← GSYM REAL_NOT_LE, REAL_LE_RMUL_EQ])

  let REAL_LT_LMUL_EQ ← prove
   r"!x y z. &0 < z ==> (z * x < z * y <=> x < y)"
   (SIMP_TAC [← GSYM REAL_NOT_LE, REAL_LE_LMUL_EQ])

  let REAL_LE_MUL_EQ ← prove
   r"(!x y. &0 < x ==> (&0 <= x * y <=> &0 <= y)) /\
   (!x y. &0 < y ==> (&0 <= x * y <=> &0 <= x))"
   (MESON_TAC [REAL_LE_LMUL_EQ, REAL_LE_RMUL_EQ, REAL_MUL_LZERO, REAL_MUL_RZERO])

  let REAL_LT_MUL_EQ ← prove
   r"(!x y. &0 < x ==> (&0 < x * y <=> &0 < y)) /\
   (!x y. &0 < y ==> (&0 < x * y <=> &0 < x))"
   (MESON_TAC [REAL_LT_LMUL_EQ, REAL_LT_RMUL_EQ, REAL_MUL_LZERO, REAL_MUL_RZERO])

  let REAL_MUL_POS_LT ← prove
   r"!x y. &0 < x * y <=> &0 < x /\ &0 < y \/ x < &0 /\ y < &0"
   (REPEAT STRIP_TAC THEN
    STRIP_ASSUME_TAC (← SPEC (← q r"x:real") REAL_LT_NEGTOTAL) THEN
    STRIP_ASSUME_TAC (← SPEC (← q r"y:real") REAL_LT_NEGTOTAL) THEN
    ASM_REWRITE_TAC [REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_LT_REFL] THEN
    ASSUM_LIST (MP_TAC o MATCH_MP REAL_LT_MUL o end_itlist CONJ) THEN
    REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC)

  let REAL_MUL_POS_LE ← prove
   r"!x y. &0 <= x * y <=>
         x = &0 \/ y = &0 \/ &0 < x /\ &0 < y \/ x < &0 /\ y < &0"
   (REWRITE_TAC [← REAL_ARITH (← q r"&0 <= x <=> x = &0 \/ &0 < x")] THEN
    REWRITE_TAC [REAL_MUL_POS_LT, REAL_ENTIRE] THEN REAL_ARITH_TAC)

  let REAL_LE_RDIV_EQ ← prove
   r"!x y z. &0 < z ==> (x <= y / z <=> x * z <= y)"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do pure (
      GEN_REWRITE_TAC LAND_CONV [← GSYM (← MATCH_MP REAL_LE_RMUL_EQ th)])) THEN
    ASM_SIMP_TAC [real_div, ← GSYM REAL_MUL_ASSOC, REAL_MUL_LINV,
                  REAL_MUL_RID, REAL_LT_IMP_NZ])

  let REAL_LE_LDIV_EQ ← prove
   r"!x y z. &0 < z ==> (x / z <= y <=> x <= y * z)"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do pure (
      GEN_REWRITE_TAC LAND_CONV [← GSYM (← MATCH_MP REAL_LE_RMUL_EQ th)])) THEN
    ASM_SIMP_TAC [real_div, ← GSYM REAL_MUL_ASSOC, REAL_MUL_LINV,
                  REAL_MUL_RID, REAL_LT_IMP_NZ])

  let REAL_LT_RDIV_EQ ← prove
   r"!x y z. &0 < z ==> (x < y / z <=> x * z < y)"
   (SIMP_TAC [← GSYM REAL_NOT_LE, REAL_LE_LDIV_EQ])

  let REAL_LT_LDIV_EQ ← prove
   r"!x y z. &0 < z ==> (x / z < y <=> x < y * z)"
   (SIMP_TAC [← GSYM REAL_NOT_LE, REAL_LE_RDIV_EQ])

  let REAL_EQ_RDIV_EQ ← prove
   r"!x y z. &0 < z ==> ((x = y / z) <=> (x * z = y))"
   (REWRITE_TAC [← GSYM REAL_LE_ANTISYM] THEN
    SIMP_TAC [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ])

  let REAL_EQ_LDIV_EQ ← prove
   r"!x y z. &0 < z ==> ((x / z = y) <=> (x = y * z))"
   (REWRITE_TAC [← GSYM REAL_LE_ANTISYM] THEN
    SIMP_TAC [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ])

  let REAL_LT_DIV2_EQ ← prove
   r"!x y z. &0 < z ==> (x / z < y / z <=> x < y)"
   (SIMP_TAC [real_div, REAL_LT_RMUL_EQ, REAL_LT_INV_EQ])

  let REAL_LE_DIV2_EQ ← prove
   r"!x y z. &0 < z ==> (x / z <= y / z <=> x <= y)"
   (SIMP_TAC [real_div, REAL_LE_RMUL_EQ, REAL_LT_INV_EQ])

  let REAL_MUL_2 ← prove
   r"!x. &2 * x = x + x"
   REAL_ARITH_TAC

  let REAL_POW_EQ_0 ← prove
   r"!x n. (x pow n = &0) <=> (x = &0) /\ ~(n = 0)"
   (GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [NOT_SUC, real_pow, REAL_ENTIRE] THENL
     [REAL_ARITH_TAC,
      CONV_TAC TAUT])

  let REAL_LE_MUL2 ← prove
   r"!w x y z. &0 <= w /\ w <= x /\ &0 <= y /\ y <= z
             ==> w * y <= x * z"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"w * z") THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL, MATCH_MP_TAC REAL_LE_RMUL] THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"y:real") THEN
    ASM_REWRITE_TAC [])

  let REAL_LT_MUL2 ← prove
   r"!w x y z. &0 <= w /\ w < x /\ &0 <= y /\ y < z
             ==> w * y < x * z"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC (← q r"w * z") THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL, MATCH_MP_TAC REAL_LT_RMUL] THEN
    ASM_REWRITE_TAC [] THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC [],
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q r"y:real") THEN
      ASM_REWRITE_TAC []])

  let REAL_LT_SQUARE ← prove
   r"!x. (&0 < x * x) <=> ~(x = &0)"
   (GEN_TAC THEN REWRITE_TAC [REAL_LT_LE, REAL_LE_SQUARE] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [EQ_SYM_EQ] THEN
    REWRITE_TAC [REAL_ENTIRE])

  let REAL_POW_1 ← prove
   r"!x. x pow 1 = x"
   (REWRITE_TAC [← num_CONV (← q r"1")] THEN
    REWRITE_TAC [real_pow, REAL_MUL_RID])

  let REAL_POW_ONE ← prove
   r"!n. &1 pow n = &1"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [real_pow, REAL_MUL_LID])

  let REAL_LT_INV2 ← prove
   r"!x y. &0 < x /\ x < y ==> inv(y) < inv(x)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN
    EXISTS_TAC (← q r"x * y") THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN
      POP_ASSUM_LIST (MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC,
      SUBGOAL_THEN (← q r"(inv x * x = &1) /\ (inv y * y = &1)") ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_MUL_LINV THEN
        POP_ASSUM_LIST (MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC,
        ASM_REWRITE_TAC [REAL_MUL_ASSOC, REAL_MUL_LID] THEN
        GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
        ASM_REWRITE_TAC [← GSYM REAL_MUL_ASSOC, REAL_MUL_RID]]])

  let REAL_LE_INV2 ← prove
   r"!x y. &0 < x /\ x <= y ==> inv(y) <= inv(x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [REAL_LE_LT] THEN
    ASM_CASES_TAC (← q r"x:real = y") THEN ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN DISJ1_TAC THEN MATCH_MP_TAC REAL_LT_INV2 THEN
    ASM_REWRITE_TAC [])

  let REAL_LT_LINV ← prove
   r"!x y. &0 < y /\ inv y < x ==> inv x < y"
   (REPEAT STRIP_TAC THEN MP_TAC (← SPEC (← q r"y:real") REAL_LT_INV) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    MP_TAC (← SPECL [← q r"(inv y:real)", ← q r"x:real"] REAL_LT_INV2) THEN
    ASM_REWRITE_TAC [REAL_INV_INV])

  let REAL_LT_RINV ← prove
   r"!x y. &0 < x /\ x < inv y ==> y < inv x"
   (REPEAT STRIP_TAC THEN MP_TAC (← SPEC (← q r"x:real") REAL_LT_INV) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    MP_TAC (← SPECL [← q r"x:real", ← q r"inv y:real"] REAL_LT_INV2) THEN
    ASM_REWRITE_TAC [REAL_INV_INV])

  let REAL_LE_LINV ← prove
   r"!x y. &0 < y /\ inv y <= x ==> inv x <= y"
   (REPEAT STRIP_TAC THEN MP_TAC (← SPEC (← q r"y:real") REAL_LT_INV) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    MP_TAC (← SPECL [← q r"(inv y:real)", ← q r"x:real"] REAL_LE_INV2) THEN
    ASM_REWRITE_TAC [REAL_INV_INV])

  let REAL_LE_RINV ← prove
   r"!x y. &0 < x /\ x <= inv y ==> y <= inv x"
   (REPEAT STRIP_TAC THEN MP_TAC (← SPEC (← q r"x:real") REAL_LT_INV) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    MP_TAC (← SPECL [← q r"x:real", ← q r"inv y:real"] REAL_LE_INV2) THEN
    ASM_REWRITE_TAC [REAL_INV_INV])

  let REAL_INV_LE_1 ← prove
   r"!x. &1 <= x ==> inv(x) <= &1"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_INV_1] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC [REAL_LT_01])

  let REAL_INV_1_LE ← prove
   r"!x. &0 < x /\ x <= &1 ==> &1 <= inv(x)"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_INV_1] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC [REAL_LT_01])

  let REAL_INV_LT_1 ← prove
   r"!x. &1 < x ==> inv(x) < &1"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_INV_1] THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC [REAL_LT_01])

  let REAL_INV_1_LT ← prove
   r"!x. &0 < x /\ x < &1 ==> &1 < inv(x)"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_INV_1] THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC [REAL_LT_01])

  let REAL_SUB_INV ← prove
   r"!x y. ~(x = &0) /\ ~(y = &0) ==> (inv(x) - inv(y) = (y - x) / (x * y))"
   (REWRITE_TAC [real_div, REAL_SUB_RDISTRIB, REAL_INV_MUL] THEN
    SIMP_TAC [REAL_MUL_ASSOC, REAL_MUL_RINV, REAL_MUL_LID] THEN
    REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN REWRITE_TAC [← GSYM real_div] THEN
    SIMP_TAC [REAL_DIV_LMUL])

  let REAL_DOWN ← prove
   r"!d. &0 < d ==> ?e. &0 < e /\ e < d"
   (GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC (← q r"d / &2") THEN
    ASSUME_TAC (← REAL_ARITH (← q r"&0 < &2")) THEN
    ASSUME_TAC (← MATCH_MP REAL_MUL_LINV (← REAL_ARITH (← q r"~(&2 = &0)"))) THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN EXISTS_TAC (← q r"&2") THEN
    ASM_REWRITE_TAC [real_div, ← GSYM REAL_MUL_ASSOC, REAL_MUL_RID] THEN
    UNDISCH_TAC (← q r"&0 < d") THEN REAL_ARITH_TAC)

  let REAL_DOWN2 ← prove
   r"!d1 d2. &0 < d1 /\ &0 < d2 ==> ?e. &0 < e /\ e < d1 /\ e < d2"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    DISJ_CASES_TAC (← SPECL [← q r"d1:real", ← q r"d2:real"] REAL_LE_TOTAL) THENL
     [MP_TAC (← SPEC (← q r"d1:real") REAL_DOWN),
      MP_TAC (← SPEC (← q r"d2:real") REAL_DOWN)] THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"e:real") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"e:real") THEN
    POP_ASSUM_LIST (MP_TAC o end_itlist CONJ) THEN
    REAL_ARITH_TAC)

  let REAL_POW_LE2 ← prove
   r"!n x y. &0 <= x /\ x <= y ==> x pow n <= y pow n"
   (INDUCT_TAC THEN REWRITE_TAC [real_pow, REAL_LE_REFL] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC [],
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []])

  return {
    REAL_LT_LCANCEL_IMP, REAL_LT_RCANCEL_IMP, REAL_LE_LCANCEL_IMP,
    REAL_LE_RCANCEL_IMP, REAL_LE_RMUL_EQ, REAL_LE_LMUL_EQ, REAL_LT_RMUL_EQ,
    REAL_LT_LMUL_EQ, REAL_LE_MUL_EQ, REAL_LT_MUL_EQ, REAL_MUL_POS_LT,
    REAL_MUL_POS_LE, REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ, REAL_LT_RDIV_EQ,
    REAL_LT_LDIV_EQ, REAL_EQ_RDIV_EQ, REAL_EQ_LDIV_EQ, REAL_LT_DIV2_EQ,
    REAL_LE_DIV2_EQ, REAL_MUL_2, REAL_POW_EQ_0, REAL_LE_MUL2, REAL_LT_MUL2,
    REAL_LT_SQUARE, REAL_POW_1, REAL_POW_ONE, REAL_LT_INV2, REAL_LE_INV2,
    REAL_LT_LINV, REAL_LT_RINV, REAL_LE_LINV, REAL_LE_RINV, REAL_INV_LE_1,
    REAL_INV_1_LE, REAL_INV_LT_1, REAL_INV_1_LT, REAL_SUB_INV, REAL_DOWN,
    REAL_DOWN2, REAL_POW_LE2 }

/-- real.ml 1115-1389. -/
structure RealThms8 where
  REAL_POW_LE_1       : thm
  REAL_POW_1_LE       : thm
  REAL_POW_MONO       : thm
  REAL_POW_LT2        : thm
  REAL_POW_LT_1       : thm
  REAL_POW_1_LT       : thm
  REAL_POW_MONO_LT    : thm
  REAL_POW_POW        : thm
  REAL_EQ_RCANCEL_IMP : thm
  REAL_EQ_LCANCEL_IMP : thm
  REAL_LT_DIV         : thm
  REAL_LE_DIV         : thm
  REAL_DIV_POW2       : thm
  REAL_DIV_POW2_ALT   : thm
  REAL_LT_POW2        : thm
  REAL_LE_POW2        : thm
  REAL_POW2_ABS       : thm
  REAL_LE_SQUARE_ABS  : thm
  REAL_LT_SQUARE_ABS  : thm
  REAL_EQ_SQUARE_ABS  : thm
  REAL_LE_POW_2       : thm
  REAL_LT_POW_2       : thm
  REAL_SOS_EQ_0       : thm
  REAL_POW_ZERO       : thm
  REAL_POW_MONO_INV   : thm
  REAL_POW_LE2_REV    : thm
  REAL_POW_LT2_REV    : thm
  REAL_POW_EQ         : thm
  REAL_POW_EQ_ABS     : thm
  REAL_POW_EQ_1_IMP   : thm
  REAL_POW_EQ_1       : thm
  REAL_POW_LT2_ODD    : thm
  REAL_POW_LE2_ODD    : thm
  REAL_POW_LT2_ODD_EQ : thm
  REAL_POW_LE2_ODD_EQ : thm
  REAL_POW_EQ_ODD_EQ  : thm
  REAL_POW_EQ_ODD     : thm
  REAL_POW_EQ_EQ      : thm
  REAL_EVENPOW_ABS    : thm
  REAL_OF_NUM_MOD     : thm
  REAL_OF_NUM_DIV     : thm
  deriving Inhabited

@[nospecialize]
def setupRealThms8 [HolBase]
    (N : HolMath.Nums.NumsThms)
    (A1 : HolMath.Arith.ArithThms1) (A2 : HolMath.Arith.ArithThms2)
    (A3 : HolMath.Arith.ArithThms3) (A4 : HolMath.Arith.ArithThms4)
    (A5 : HolMath.Arith.ArithThms5) (A7 : HolMath.Arith.ArithThms7)
    (CnA : HolMath.CalcNum.ArithRewrites)
    (R : HolMath.RealAx.RealThms)
    (K : HolMath.CalcInt.CalcIntThms)
    (L : HolMath.RealArith.RealArithLemmas)
    (T1 : RealThms1) (T2 : RealThms2) (T3 : RealThms3) (T4 : RealThms4)
    (T6 : RealThms6) (T7 : RealThms7)
    (NUM_EQ_CONV' : term → IO (Except String thm))
    (REAL_ARITH' : term → IO (Except String thm))
    (MESON_TAC : List thm → tactic)
    (ASM_MESON_TAC : List thm → tactic) :
    ExceptT String IO RealThms8 := do
  let NUM_EQ_CONV (t : term) : ExceptT String IO thm := NUM_EQ_CONV' t
  let REAL_ARITH (t : term) : ExceptT String IO thm := REAL_ARITH' t
  let REAL_ARITH_TAC := REAL_ARITH_TAC REAL_ARITH'
  let INDUCT_TAC := HolMath.Nums.INDUCT_TAC N.num_INDUCTION
  let { REAL_OF_NUM_LT, REAL_OF_NUM_CLAUSES, REAL_LT_MUL, .. } := T1
  let { REAL_NOT_LE, REAL_SUB_REFL, .. } := T2
  let { REAL_SUB_RZERO, REAL_EQ_SUB_LADD, REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB, .. } := T3
  let { REAL_ABS_POS, REAL_ABS_ABS, .. } := T4
  let { REAL_POW_LE, REAL_POW_LT, REAL_ABS_POW, REAL_LE_LMUL, REAL_LT_LMUL,
        REAL_INV_INV, REAL_LT_INV_EQ, REAL_LE_INV_EQ, REAL_DIV_LMUL,
        REAL_INV_DIV, REAL_POW_INV, REAL_POW_ADD, REAL_POW_SUB, .. } := T6
  let { REAL_POW_EQ_0, REAL_LT_MUL2, REAL_POW_ONE, REAL_LE_INV2, REAL_INV_1_LE,
        REAL_POW_LE2, .. } := T7
  let { REAL_ADD_LID, REAL_MUL_SYM, REAL_MUL_LID, REAL_LE_REFL,
        REAL_LE_ANTISYM, REAL_LE_TRANS, REAL_LE_MUL, REAL_INV_0,
        REAL_OF_NUM_EQ, REAL_OF_NUM_LE, real_abs, real_pow, real_div, .. } := R
  let { REAL_MUL_RZERO, REAL_MUL_LZERO, REAL_POW_NEG, REAL_ABS_NUM, .. } := K
  let { REAL_LT_TRANS, REAL_LE_LT, REAL_SUB_0, REAL_LT_LE, REAL_ENTIRE,
        REAL_LE_NEGTOTAL, REAL_LE_SQUARE, REAL_MUL_RID, REAL_POW_2, REAL_POS, .. } := L
  let { NOT_SUC, .. } := N
  let { ADD_SYM, .. } := A1
  let { MULT_CLAUSES, LE, LE_0, .. } := A2
  let { NOT_LE, LT_IMP_LE, .. } := A3
  let { LE_EXISTS, LT_EXISTS, .. } := A4
  let { NOT_EVEN, NOT_ODD, EVEN_EXISTS, .. } := A5
  let { DIV_ZERO, DIVISION_SIMP, .. } := A7
  let { ARITH_EVEN, ARITH, .. } := CnA

  let REAL_POW_LE_1 ← prove
   r"!n x. &1 <= x ==> &1 <= x pow n"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"n:num", ← q r"&1", ← q r"x:real"] REAL_POW_LE2) THEN
    ASM_REWRITE_TAC [REAL_POW_ONE, REAL_POS])

  let REAL_POW_1_LE ← prove
   r"!n x. &0 <= x /\ x <= &1 ==> x pow n <= &1"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"n:num", ← q r"x:real", ← q r"&1"] REAL_POW_LE2) THEN
    ASM_REWRITE_TAC [REAL_POW_ONE])

  let REAL_POW_MONO ← prove
   r"!m n x. &1 <= x /\ m <= n ==> x pow m <= x pow n"
   (REPEAT GEN_TAC THEN REWRITE_TAC [LE_EXISTS] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"d:num") SUBST1_TAC) THEN
    REWRITE_TAC [REAL_POW_ADD] THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"&1") THEN
      REWRITE_TAC [REAL_OF_NUM_LE, ARITH] THEN
      MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC [],
      MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC []])

  let REAL_POW_LT2 ← prove
   r"!n x y. ~(n = 0) /\ &0 <= x /\ x < y ==> x pow n < y pow n"
   (INDUCT_TAC THEN REWRITE_TAC [NOT_SUC, real_pow] THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [real_pow, REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC [],
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []])

  let REAL_POW_LT_1 ← prove
   r"!n x. ~(n = 0) /\ &1 < x ==> &1 < x pow n"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"n:num", ← q r"&1", ← q r"x:real"] REAL_POW_LT2) THEN
    ASM_REWRITE_TAC [REAL_POW_ONE, REAL_POS])

  let REAL_POW_1_LT ← prove
   r"!n x. ~(n = 0) /\ &0 <= x /\ x < &1 ==> x pow n < &1"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"n:num", ← q r"x:real", ← q r"&1"] REAL_POW_LT2) THEN
    ASM_REWRITE_TAC [REAL_POW_ONE])

  let REAL_POW_MONO_LT ← prove
   r"!m n x. &1 < x /\ m < n ==> x pow m < x pow n"
   (REPEAT GEN_TAC THEN REWRITE_TAC [LT_EXISTS] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (CHOOSE_THEN SUBST_ALL_TAC) THEN
    REWRITE_TAC [REAL_POW_ADD] THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN
      MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (← q r"&1") THEN
      ASM_REWRITE_TAC [REAL_OF_NUM_LT, ARITH],
      SPEC_TAC ((← q r"d:num"), (← q r"d:num")) THEN
      INDUCT_TAC THEN ONCE_REWRITE_TAC [real_pow] THENL
       [ASM_REWRITE_TAC [real_pow, REAL_MUL_RID], ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LT_MUL2 THEN
      ASM_REWRITE_TAC [REAL_OF_NUM_LE, ARITH]])

  let REAL_POW_POW ← prove
   r"!x m n. (x pow m) pow n = x pow (m * n)"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [real_pow, MULT_CLAUSES, REAL_POW_ADD])

  let REAL_EQ_RCANCEL_IMP ← prove
   r"!x y z. ~(z = &0) /\ (x * z = y * z) ==> (x = y)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_SUB_0] THEN
    REWRITE_TAC [REAL_SUB_RZERO, ← GSYM REAL_SUB_RDISTRIB, REAL_ENTIRE] THEN
    CONV_TAC TAUT)

  let REAL_EQ_LCANCEL_IMP ← prove
   r"!x y z. ~(z = &0) /\ (z * x = z * y) ==> (x = y)"
   (ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN MATCH_ACCEPT_TAC REAL_EQ_RCANCEL_IMP)

  let REAL_LT_DIV ← prove
   r"!x y. &0 < x /\ &0 < y ==> &0 < x / y"
   (SIMP_TAC [REAL_LT_MUL, REAL_LT_INV_EQ, real_div])

  let REAL_LE_DIV ← prove
   r"!x y. &0 <= x /\ &0 <= y ==> &0 <= x / y"
   (SIMP_TAC [REAL_LE_MUL, REAL_LE_INV_EQ, real_div])

  let REAL_DIV_POW2 ← prove
   r"!x m n. ~(x = &0)
           ==> (x pow m / x pow n = if n <= m then x pow (m - n)
                                    else inv(x pow (n - m)))"
   (REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_SIMP_TAC [REAL_POW_SUB] THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_INV_INV] THEN
    AP_TERM_TAC THEN REWRITE_TAC [REAL_INV_DIV] THEN
    UNDISCH_TAC (← q r"~(n:num <= m)") THEN REWRITE_TAC [NOT_LE] THEN
    DISCH_THEN (MP_TAC o MATCH_MP LT_IMP_LE) THEN
    ASM_SIMP_TAC [REAL_POW_SUB])

  let REAL_DIV_POW2_ALT ← prove
   r"!x m n. ~(x = &0)
           ==> (x pow m / x pow n = if n < m then x pow (m - n)
                                    else inv(x pow (n - m)))"
   (REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_INV_INV] THEN
    ONCE_REWRITE_TAC [REAL_INV_DIV] THEN
    ASM_SIMP_TAC [← GSYM NOT_LE, REAL_DIV_POW2] THEN
    ASM_CASES_TAC (← q r"m <= n:num") THEN
    ASM_REWRITE_TAC [REAL_INV_INV])

  let REAL_LT_POW2 ← prove
   r"!n. &0 < &2 pow n"
   (SIMP_TAC [REAL_POW_LT, REAL_OF_NUM_LT, ARITH])

  let REAL_LE_POW2 ← prove
   r"!n. &1 <= &2 pow n"
   (GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"&2 pow 0") THEN
    SIMP_TAC [REAL_POW_MONO, LE_0, REAL_OF_NUM_LE, ARITH] THEN
    REWRITE_TAC [real_pow, REAL_LE_REFL])

  let REAL_POW2_ABS ← prove
   r"!x. abs(x) pow 2 = x pow 2"
   (GEN_TAC THEN REWRITE_TAC [real_abs] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_POW_NEG, ARITH_EVEN])

  let REAL_LE_SQUARE_ABS ← prove
   r"!x y. abs(x) <= abs(y) <=> x pow 2 <= y pow 2"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_POW2_ABS] THEN
    MESON_TAC [REAL_POW_LE2, REAL_ABS_POS, ← NUM_EQ_CONV (← q r"2 = 0"),
               REAL_POW_LT2, REAL_NOT_LE])

  let REAL_LT_SQUARE_ABS ← prove
   r"!x y. abs(x) < abs(y) <=> x pow 2 < y pow 2"
   (REWRITE_TAC [← GSYM REAL_NOT_LE, REAL_LE_SQUARE_ABS])

  let REAL_EQ_SQUARE_ABS ← prove
   r"!x y. abs x = abs y <=> x pow 2 = y pow 2"
   (REWRITE_TAC [← GSYM REAL_LE_ANTISYM, REAL_LE_SQUARE_ABS])

  let REAL_LE_POW_2 ← prove
   r"!x. &0 <= x pow 2"
   (REWRITE_TAC [REAL_POW_2, REAL_LE_SQUARE])

  let REAL_LT_POW_2 ← prove
   r"!x. &0 < x pow 2 <=> ~(x = &0)"
   (REWRITE_TAC [REAL_LE_POW_2, ← REAL_ARITH (← q r"&0 < x <=> &0 <= x /\ ~(x = &0)")] THEN
    REWRITE_TAC [REAL_POW_EQ_0, ARITH])

  let REAL_SOS_EQ_0 ← prove
   r"!x y. x pow 2 + y pow 2 = &0 <=> x = &0 /\ y = &0"
   (REPEAT GEN_TAC THEN EQ_TAC THEN
    SIMP_TAC [REAL_POW_2, REAL_MUL_LZERO, REAL_ADD_LID] THEN
    DISCH_THEN (MP_TAC o MATCH_MP (← REAL_ARITH
     (← q r"x + y = &0 ==> &0 <= x /\ &0 <= y ==> x = &0 /\ y = &0"))) THEN
    REWRITE_TAC [REAL_LE_SQUARE, REAL_ENTIRE])

  let REAL_POW_ZERO ← prove
   r"!n. &0 pow n = if n = 0 then &1 else &0"
   (INDUCT_TAC THEN REWRITE_TAC [real_pow, NOT_SUC, REAL_MUL_LZERO])

  let REAL_POW_MONO_INV ← prove
   r"!m n x. &0 <= x /\ x <= &1 /\ n <= m ==> x pow m <= x pow n"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"x = &0") THENL
     [ASM_REWRITE_TAC [REAL_POW_ZERO] THEN
      REPEAT (COND_CASES_TAC THEN REWRITE_TAC [REAL_POS, REAL_LE_REFL]) THEN
      UNDISCH_TAC (← q r"n:num <= m") THEN ASM_REWRITE_TAC [LE],
      GEN_REWRITE_TAC BINOP_CONV [← GSYM REAL_INV_INV] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC [← GSYM REAL_POW_INV] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC [REAL_LT_INV_EQ],
        MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC REAL_INV_1_LE] THEN
      ASM_REWRITE_TAC [REAL_LT_LE]])

  let REAL_POW_LE2_REV ← prove
   r"!n x y. ~(n = 0) /\ &0 <= y /\ x pow n <= y pow n ==> x <= y"
   (MESON_TAC [REAL_POW_LT2, REAL_NOT_LE])

  let REAL_POW_LT2_REV ← prove
   r"!n x y. &0 <= y /\ x pow n < y pow n ==> x < y"
   (MESON_TAC [REAL_POW_LE2, REAL_NOT_LE])

  let REAL_POW_EQ ← prove
   r"!n x y. ~(n = 0) /\ &0 <= x /\ &0 <= y /\ x pow n = y pow n ==> x = y"
   (REWRITE_TAC [← GSYM REAL_LE_ANTISYM] THEN MESON_TAC [REAL_POW_LE2_REV])

  let REAL_POW_EQ_ABS ← prove
   r"!n x y. ~(n = 0) /\ x pow n = y pow n ==> abs x = abs y"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_EQ THEN EXISTS_TAC (← q r"n:num") THEN
    ASM_REWRITE_TAC [REAL_ABS_POS, ← GSYM REAL_ABS_POW])

  let REAL_POW_EQ_1_IMP ← prove
   r"!x n. ~(n = 0) /\ x pow n = &1 ==> abs(x) = &1"
   (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_POW_EQ_ABS THEN EXISTS_TAC (← q r"n:num") THEN
    ASM_REWRITE_TAC [REAL_POW_ONE])

  let REAL_POW_EQ_1 ← prove
   r"!x n. x pow n = &1 <=> abs(x) = &1 /\ (x < &0 ==> EVEN(n)) \/ n = 0"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [real_pow] THEN
    ASM_CASES_TAC (← q r"abs(x) = &1") THENL
     [ALL_TAC, ASM_MESON_TAC [REAL_POW_EQ_1_IMP]] THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (DISJ_CASES_THEN SUBST1_TAC o MATCH_MP (← REAL_ARITH
     (← q r"abs x = a ==> x = a \/ x = --a"))) THEN
    ASM_REWRITE_TAC [REAL_POW_NEG, REAL_POW_ONE] THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC)

  let REAL_POW_LT2_ODD ← prove
   r"!n x y. x < y /\ ODD n ==> x pow n < y pow n"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_REWRITE_TAC [ARITH] THEN STRIP_TAC THEN
    DISJ_CASES_TAC (← SPEC (← q r"y:real") REAL_LE_NEGTOTAL) THENL
     [DISJ_CASES_TAC (← REAL_ARITH (← q r"&0 <= x \/ &0 < --x")) THEN
      ASM_SIMP_TAC [REAL_POW_LT2] THEN
      SUBGOAL_THEN (← q r"&0 < --x pow n /\ &0 <= y pow n") MP_TAC THENL
       [ASM_SIMP_TAC [REAL_POW_LE, REAL_POW_LT],
        ASM_REWRITE_TAC [REAL_POW_NEG, ← GSYM NOT_ODD] THEN REAL_ARITH_TAC],
      SUBGOAL_THEN (← q r"--y pow n < --x pow n") MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC [],
        ASM_REWRITE_TAC [REAL_POW_NEG, ← GSYM NOT_ODD]] THEN
      REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC])

  let REAL_POW_LE2_ODD ← prove
   r"!n x y. x <= y /\ ODD n ==> x pow n <= y pow n"
   (REWRITE_TAC [REAL_LE_LT] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [REAL_POW_LT2_ODD])

  let REAL_POW_LT2_ODD_EQ ← prove
   r"!n x y. ODD n ==> (x pow n < y pow n <=> x < y)"
   (MESON_TAC [REAL_POW_LT2_ODD, REAL_POW_LE2_ODD, REAL_NOT_LE])

  let REAL_POW_LE2_ODD_EQ ← prove
   r"!n x y. ODD n ==> (x pow n <= y pow n <=> x <= y)"
   (MESON_TAC [REAL_POW_LT2_ODD, REAL_POW_LE2_ODD, REAL_NOT_LE])

  let REAL_POW_EQ_ODD_EQ ← prove
   r"!n x y. ODD n ==> (x pow n = y pow n <=> x = y)"
   (SIMP_TAC [← GSYM REAL_LE_ANTISYM, REAL_POW_LE2_ODD_EQ])

  let REAL_POW_EQ_ODD ← prove
   r"!n x y. ODD n /\ x pow n = y pow n ==> x = y"
   (MESON_TAC [REAL_POW_EQ_ODD_EQ])

  let REAL_POW_EQ_EQ ← prove
   r"!n x y. x pow n = y pow n <=>
           if EVEN n then n = 0 \/ abs x = abs y else x = y"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_REWRITE_TAC [real_pow, ARITH] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [REAL_POW_EQ_ODD_EQ, ← GSYM NOT_EVEN] THEN
    EQ_TAC THENL [ASM_MESON_TAC [REAL_POW_EQ_ABS], ALL_TAC] THEN
    REWRITE_TAC [REAL_EQ_SQUARE_ABS] THEN DISCH_TAC THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"m:num") SUBST1_TAC o
      REWRITE_RULE [EVEN_EXISTS]) THEN ASM_REWRITE_TAC [← GSYM REAL_POW_POW])

  let REAL_EVENPOW_ABS ← prove
   r"!x n. EVEN n ==> abs x pow n = x pow n"
   (SIMP_TAC [REAL_POW_EQ_EQ, REAL_ABS_ABS])

  let REAL_OF_NUM_MOD ← prove
   r"!m n. &(m MOD n):real = &m - &(m DIV n) * &n"
   (REPEAT GEN_TAC THEN REWRITE_TAC [REAL_EQ_SUB_LADD] THEN
    REWRITE_TAC [REAL_OF_NUM_CLAUSES] THEN
    MESON_TAC [DIVISION_SIMP, ADD_SYM])

  let REAL_OF_NUM_DIV ← prove
   r"!m n. &(m DIV n):real = &m / &n - &(m MOD n) / &n"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n = 0") THENL
     [ASM_REWRITE_TAC [DIV_ZERO, real_div, REAL_INV_0, REAL_MUL_RZERO,
                       REAL_SUB_REFL],
      MATCH_MP_TAC REAL_EQ_LCANCEL_IMP THEN EXISTS_TAC (← q r"&n:real") THEN
      ASM_SIMP_TAC [REAL_SUB_LDISTRIB, REAL_DIV_LMUL, REAL_OF_NUM_EQ] THEN
      REWRITE_TAC [REAL_OF_NUM_MOD] THEN REAL_ARITH_TAC])

  return {
    REAL_POW_LE_1, REAL_POW_1_LE, REAL_POW_MONO, REAL_POW_LT2, REAL_POW_LT_1,
    REAL_POW_1_LT, REAL_POW_MONO_LT, REAL_POW_POW, REAL_EQ_RCANCEL_IMP,
    REAL_EQ_LCANCEL_IMP, REAL_LT_DIV, REAL_LE_DIV, REAL_DIV_POW2,
    REAL_DIV_POW2_ALT, REAL_LT_POW2, REAL_LE_POW2, REAL_POW2_ABS,
    REAL_LE_SQUARE_ABS, REAL_LT_SQUARE_ABS, REAL_EQ_SQUARE_ABS, REAL_LE_POW_2,
    REAL_LT_POW_2, REAL_SOS_EQ_0, REAL_POW_ZERO, REAL_POW_MONO_INV,
    REAL_POW_LE2_REV, REAL_POW_LT2_REV, REAL_POW_EQ, REAL_POW_EQ_ABS,
    REAL_POW_EQ_1_IMP, REAL_POW_EQ_1, REAL_POW_LT2_ODD, REAL_POW_LE2_ODD,
    REAL_POW_LT2_ODD_EQ, REAL_POW_LE2_ODD_EQ, REAL_POW_EQ_ODD_EQ,
    REAL_POW_EQ_ODD, REAL_POW_EQ_EQ, REAL_EVENPOW_ABS, REAL_OF_NUM_MOD,
    REAL_OF_NUM_DIV }

/- ---------------------------------------------------------------------- -/
/- Bounds on convex combinations.                                         -/
/- ---------------------------------------------------------------------- -/

/-- real.ml 1390-1517. -/
structure RealThms9 where
  REAL_CONVEX_BOUND2_LT : thm
  REAL_CONVEX_BOUND2_LE : thm
  REAL_CONVEX_BOUND_LT  : thm
  REAL_CONVEX_BOUND_LE  : thm
  REAL_CONVEX_BOUND_GT  : thm
  REAL_CONVEX_BOUND_GE  : thm
  REAL_CONVEX_BOUNDS_LE : thm
  REAL_CONVEX_BOUNDS_LT : thm
  REAL_ARCH_SIMPLE      : thm
  REAL_ARCH_LT          : thm
  REAL_ARCH             : thm
  REAL_ARCH_INV         : thm
  REAL_POW_LBOUND       : thm
  REAL_ARCH_POW         : thm
  REAL_ARCH_POW2        : thm
  REAL_ARCH_POW_INV     : thm
  deriving Inhabited

@[nospecialize]
def setupRealThms9 [HolBase]
    (N : HolMath.Nums.NumsThms)
    (CnA : HolMath.CalcNum.ArithRewrites)
    (R : HolMath.RealAx.RealThms)
    (K : HolMath.CalcInt.CalcIntThms)
    (L : HolMath.RealArith.RealArithLemmas)
    (T1 : RealThms1) (T2 : RealThms2) (T3 : RealThms3)
    (T6 : RealThms6) (T7 : RealThms7)
    (REAL_ARITH' : term → IO (Except String thm))
    (MESON_TAC : List thm → tactic)
    (ASM_MESON_TAC : List thm → tactic) :
    ExceptT String IO RealThms9 := do
  let REAL_ARITH (t : term) : ExceptT String IO thm := REAL_ARITH' t
  let REAL_ARITH_TAC := REAL_ARITH_TAC REAL_ARITH'
  let INDUCT_TAC := HolMath.Nums.INDUCT_TAC N.num_INDUCTION
  -- meson.ml: `let MESON ths tm = prove(tm,MESON_TAC ths)`
  let MESON (ths : List thm) (tm : term) : ExceptT String IO thm :=
    HolCore.Tactics.prove HolBase.B tm (MESON_TAC ths)
  let { REAL_OF_NUM_LT, REAL_OF_NUM_SUC, REAL_ADD_RDISTRIB, .. } := T1
  let { REAL_LT_ANTISYM, REAL_LE_ADD2, REAL_SUB_ADD2, .. } := T2
  let { REAL_LE_SUB_LADD, REAL_LTE_ADD2, .. } := T3
  let { REAL_LE_LMUL, REAL_LT_LMUL, REAL_INV_INV, REAL_LT_INV, REAL_LT_INV_EQ,
        REAL_INV_1, REAL_POW_INV, .. } := T6
  let { REAL_LT_LDIV_EQ, REAL_POW_1, REAL_LT_INV2, .. } := T7
  let { REAL_ADD_LID, REAL_MUL_LID, REAL_LE_REFL, REAL_LE_TRANS, REAL_LE_TOTAL,
        REAL_LE_MUL, REAL_OF_NUM_ADD, real_pow, REAL_COMPLETE, .. } := R
  let { REAL_MUL_LZERO, REAL_ADD_RID, .. } := K
  let { REAL_LT_IMP_LE, REAL_LTE_TRANS, REAL_LET_TRANS, REAL_LT_TRANS,
        REAL_SUB_LT, REAL_NOT_LT, REAL_POS, .. } := L
  let { ARITH, .. } := CnA
  let { RIGHT_FORALL_IMP_THM, MONO_EXISTS, .. } := HolBase.T

  let REAL_CONVEX_BOUND2_LT ← prove
   r"!x y a u v. x < a /\ y < b /\ &0 <= u /\ &0 <= v /\ u + v = &1
               ==> u * x + v * y < u * a + v * b"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"u = &0") THENL
     [ASM_REWRITE_TAC [REAL_MUL_LZERO, REAL_ADD_LID] THEN REPEAT STRIP_TAC,
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LTE_ADD2 THEN
      ASM_SIMP_TAC [REAL_LE_LMUL, REAL_LT_IMP_LE]] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN
    REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC)

  let REAL_CONVEX_BOUND2_LE ← prove
   r"!x y a u v. x <= a /\ y <= b /\ &0 <= u /\ &0 <= v /\ u + v = &1
               ==> u * x + v * y <= u * a + v * b"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC)

  let REAL_CONVEX_BOUND_LT ← prove
   r"!x y a u v. x < a /\ y < a /\ &0 <= u /\ &0 <= v /\ (u + v = &1)
               ==> u * x + v * y < a"
   (MESON_TAC [REAL_CONVEX_BOUND2_LT, ← MESON [REAL_MUL_LID, REAL_ADD_RDISTRIB]
     (← q r"u + v = &1 ==> u * a + v * a = a")])

  let REAL_CONVEX_BOUND_LE ← prove
   r"!x y a u v. x <= a /\ y <= a /\ &0 <= u /\ &0 <= v /\ (u + v = &1)
               ==> u * x + v * y <= a"
   (MESON_TAC [REAL_CONVEX_BOUND2_LE, ← MESON [REAL_MUL_LID, REAL_ADD_RDISTRIB]
     (← q r"u + v = &1 ==> u * a + v * a = a")])

  let REAL_CONVEX_BOUND_GT ← prove
   r"!x y a u v.
        a < x /\ a < y /\ &0 <= u /\ &0 <= v /\ u + v = &1
        ==> a < u * x + v * y"
   (MESON_TAC [REAL_CONVEX_BOUND2_LT, ← MESON [REAL_MUL_LID, REAL_ADD_RDISTRIB]
     (← q r"u + v = &1 ==> u * a + v * a = a")])

  let REAL_CONVEX_BOUND_GE ← prove
   r"!x y a u v.
        a <= x /\ a <= y /\ &0 <= u /\ &0 <= v /\ u + v = &1
        ==> a <= u * x + v * y"
   (MESON_TAC [REAL_CONVEX_BOUND2_LE, ← MESON [REAL_MUL_LID, REAL_ADD_RDISTRIB]
     (← q r"u + v = &1 ==> u * a + v * a = a")])

  let REAL_CONVEX_BOUNDS_LE ← prove
   r"!x y a b u v.
        a <= x /\ x <= b /\ a <= y /\ y <= b /\
        &0 <= u /\ &0 <= v /\ u + v = &1
        ==> a <= u * x + v * y /\ u * x + v * y <= b"
   (MESON_TAC [REAL_CONVEX_BOUND2_LE, ← MESON [REAL_MUL_LID, REAL_ADD_RDISTRIB]
     (← q r"u + v = &1 ==> u * a + v * a = a")])

  let REAL_CONVEX_BOUNDS_LT ← prove
   r"!x y a b u v.
        a < x /\ x < b /\ a < y /\ y < b /\
        &0 <= u /\ &0 <= v /\ u + v = &1
        ==> a < u * x + v * y /\ u * x + v * y < b"
   (MESON_TAC [REAL_CONVEX_BOUND2_LT, ← MESON [REAL_MUL_LID, REAL_ADD_RDISTRIB]
     (← q r"u + v = &1 ==> u * a + v * a = a")])

  /- ---------------------------------------------------------------------- -/
  /- Some basic forms of the Archimedian property.                          -/
  /- ---------------------------------------------------------------------- -/

  let REAL_ARCH_SIMPLE ← prove
   r"!x. ?n. x <= &n"
   (← do
    let lemma ← prove r"(!x. (?n. x = &n) ==> P x) <=> !n. P(&n)" (MESON_TAC [])
    pure
     (MP_TAC (← SPEC (← q r"\y. ?n. y = &n") REAL_COMPLETE) THEN REWRITE_TAC [lemma] THEN
      MESON_TAC [REAL_LE_SUB_LADD, REAL_OF_NUM_ADD, REAL_LE_TOTAL,
                 ← REAL_ARITH (← q r"~(M <= M - &1)")]))

  let REAL_ARCH_LT ← prove
   r"!x. ?n. x < &n"
   (MESON_TAC [REAL_ARCH_SIMPLE, REAL_OF_NUM_ADD,
               ← REAL_ARITH (← q r"x <= n ==> x < n + &1")])

  let REAL_ARCH ← prove
   r"!x. &0 < x ==> !y. ?n. y < &n * x"
   (MESON_TAC [REAL_ARCH_LT, REAL_LT_LDIV_EQ])

  let REAL_ARCH_INV ← prove
   r"!e. &0 < e <=> ?n. ~(n = 0) /\ &0 < inv(&n) /\ inv(&n) < e"
   (GEN_TAC THEN EQ_TAC THENL [ALL_TAC, MESON_TAC [REAL_LT_TRANS]] THEN
    DISCH_TAC THEN MP_TAC (← SPEC (← q r"inv(e)") REAL_ARCH_LT) THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    ASM_MESON_TAC [REAL_LT_INV2, REAL_INV_INV, REAL_LT_INV_EQ, REAL_LT_TRANS,
                   REAL_LT_ANTISYM])

  let REAL_POW_LBOUND ← prove
   r"!x n. &0 <= x ==> &1 + &n * x <= (&1 + x) pow n"
   (GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
    INDUCT_TAC THEN
    REWRITE_TAC [real_pow, REAL_MUL_LZERO, REAL_ADD_RID, REAL_LE_REFL] THEN
    REWRITE_TAC [← GSYM REAL_OF_NUM_SUC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"(&1 + x) * (&1 + &n * x)") THEN
    ASM_SIMP_TAC [REAL_LE_LMUL, ← REAL_ARITH (← q r"&0 <= x ==> &0 <= &1 + x")] THEN
    ASM_SIMP_TAC [REAL_LE_MUL, REAL_POS, ← REAL_ARITH
     (← q r"&1 + (n + &1) * x <= (&1 + x) * (&1 + n * x) <=> &0 <= n * x * x")])

  let REAL_ARCH_POW ← prove
   r"!x y. &1 < x ==> ?n. y < x pow n"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPEC (← q r"x - &1") REAL_ARCH) THEN ASM_REWRITE_TAC [REAL_SUB_LT] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"y:real")) THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC (← q r"n:num") THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC (← q r"&1 + &n * (x - &1)") THEN
    ASM_SIMP_TAC [← REAL_ARITH (← q r"x < y ==> x < &1 + y")] THEN
    ASM_MESON_TAC [REAL_POW_LBOUND, REAL_SUB_ADD2, ← REAL_ARITH
      (← q r"&1 < x ==> &0 <= x - &1")])

  let REAL_ARCH_POW2 ← prove
   r"!x. ?n. x < &2 pow n"
   (SIMP_TAC [REAL_ARCH_POW, REAL_OF_NUM_LT, ARITH])

  let REAL_ARCH_POW_INV ← prove
   r"!x y. &0 < y /\ x < &1 ==> ?n. x pow n < y"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"&0 < x") THENL
     [ALL_TAC, ASM_MESON_TAC [REAL_POW_1, REAL_LET_TRANS, REAL_NOT_LT]] THEN
    SUBGOAL_THEN (← q r"inv(&1) < inv(x)") MP_TAC THENL
     [ASM_SIMP_TAC [REAL_LT_INV2], REWRITE_TAC [REAL_INV_1]] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"inv(y)") o MATCH_MP REAL_ARCH_POW) THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
    GEN_REWRITE_TAC BINOP_CONV [← GSYM REAL_INV_INV] THEN
    ASM_SIMP_TAC [← GSYM REAL_POW_INV, REAL_LT_INV, REAL_LT_INV2])

  return {
    REAL_CONVEX_BOUND2_LT, REAL_CONVEX_BOUND2_LE, REAL_CONVEX_BOUND_LT,
    REAL_CONVEX_BOUND_LE, REAL_CONVEX_BOUND_GT, REAL_CONVEX_BOUND_GE,
    REAL_CONVEX_BOUNDS_LE, REAL_CONVEX_BOUNDS_LT, REAL_ARCH_SIMPLE,
    REAL_ARCH_LT, REAL_ARCH, REAL_ARCH_INV, REAL_POW_LBOUND, REAL_ARCH_POW,
    REAL_ARCH_POW2, REAL_ARCH_POW_INV }

/- ---------------------------------------------------------------------- -/
/- The sign of a real number, as a real number.                           -/
/- ---------------------------------------------------------------------- -/

/-- real.ml 1518-1656. -/
structure RealThms10 where
  real_sgn          : thm
  REAL_SGN_0        : thm
  REAL_SGN_NEG      : thm
  REAL_SGN_ABS      : thm
  REAL_SGN_ABS_ALT  : thm
  REAL_EQ_SGN_ABS   : thm
  REAL_ABS_SGN      : thm
  REAL_SGN          : thm
  REAL_SGN_MUL      : thm
  REAL_SGN_INV      : thm
  REAL_SGN_DIV      : thm
  REAL_SGN_EQ       : thm
  REAL_SGN_CASES    : thm
  REAL_SGN_INEQS    : thm
  REAL_SGN_POW      : thm
  REAL_SGN_POW_2    : thm
  REAL_SGN_REAL_SGN : thm
  REAL_INV_SGN      : thm
  REAL_SGN_EQ_INEQ  : thm
  REAL_SGNS_EQ      : thm
  REAL_SGNS_EQ_ALT  : thm
  REAL_WLOG_LE      : thm
  REAL_WLOG_LT      : thm
  REAL_WLOG_LE_3    : thm
  deriving Inhabited

/-- `real_sgn` is a `new_definition`, so Session runs this once. -/
@[nospecialize]
def setupRealThms10 [HolBase]
    (N : HolMath.Nums.NumsThms)
    (CnA : HolMath.CalcNum.ArithRewrites)
    (R : HolMath.RealAx.RealThms)
    (K : HolMath.CalcInt.CalcIntThms)
    (L : HolMath.RealArith.RealArithLemmas)
    (T2 : RealThms2) (T4 : RealThms4) (T6 : RealThms6)
    (T7 : RealThms7) (T8 : RealThms8)
    (new_definition' : term → IO (Except String thm))
    (REAL_ARITH' : term → IO (Except String thm))
    (MESON_TAC : List thm → tactic) :
    ExceptT String IO RealThms10 := do
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let REAL_ARITH (t : term) : ExceptT String IO thm := REAL_ARITH' t
  let REAL_ARITH_TAC := REAL_ARITH_TAC REAL_ARITH'
  let INDUCT_TAC := HolMath.Nums.INDUCT_TAC N.num_INDUCTION
  let { REAL_NOT_LE, REAL_LT_TOTAL, REAL_LT_01, .. } := T2
  let { REAL_ABS_ZERO, REAL_ABS_POS, .. } := T4
  let { REAL_ABS_MUL, REAL_INV_INV, REAL_LT_INV_EQ, REAL_INV_NEG,
        REAL_MUL_RINV, REAL_INV_1, REAL_ABS_DIV, REAL_INV_MUL, .. } := T6
  let { REAL_POW_EQ_0, .. } := T7
  let { REAL_LE_POW_2, .. } := T8
  let { REAL_MUL_ASSOC, REAL_LE_TOTAL, REAL_INV_0, real_pow, real_div, .. } := R
  let { REAL_MUL_LZERO, .. } := K
  let { REAL_MUL_RID, .. } := L
  let { ARITH, .. } := CnA

  let real_sgn ← new_definition
   r"(real_sgn:real->real) x =
        if &0 < x then &1 else if x < &0 then -- &1 else &0"

  let REAL_SGN_0 ← prove
   r"real_sgn(&0) = &0"
   (REWRITE_TAC [real_sgn] THEN REAL_ARITH_TAC)

  let REAL_SGN_NEG ← prove
   r"!x. real_sgn(--x) = --(real_sgn x)"
   (REWRITE_TAC [real_sgn] THEN REAL_ARITH_TAC)

  let REAL_SGN_ABS ← prove
   r"!x. real_sgn(x) * abs(x) = x"
   (REWRITE_TAC [real_sgn] THEN REAL_ARITH_TAC)

  let REAL_SGN_ABS_ALT ← prove
   r"!x. real_sgn x * x = abs x"
   (GEN_TAC THEN REWRITE_TAC [real_sgn] THEN REAL_ARITH_TAC)

  let REAL_EQ_SGN_ABS ← prove
   r"!x y:real. x = y <=> real_sgn x = real_sgn y /\ abs x = abs y"
   (MESON_TAC [REAL_SGN_ABS])

  let REAL_ABS_SGN ← prove
   r"!x. abs(real_sgn x) = real_sgn(abs x)"
   (REWRITE_TAC [real_sgn] THEN REAL_ARITH_TAC)

  let REAL_SGN ← prove
   r"!x. real_sgn x = x / abs x"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"x = &0") THENL
     [ASM_REWRITE_TAC [real_div, REAL_MUL_LZERO, REAL_SGN_0],
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [← GSYM REAL_SGN_ABS] THEN
      ASM_SIMP_TAC [real_div, ← GSYM REAL_MUL_ASSOC, REAL_ABS_ZERO,
                    REAL_MUL_RINV, REAL_MUL_RID]])

  let REAL_SGN_MUL ← prove
   r"!x y. real_sgn(x * y) = real_sgn(x) * real_sgn(y)"
   (REWRITE_TAC [REAL_SGN, REAL_ABS_MUL, real_div, REAL_INV_MUL] THEN
    REAL_ARITH_TAC)

  let REAL_SGN_INV ← prove
   r"!x. real_sgn(inv x) = real_sgn x"
   (REWRITE_TAC [real_sgn, REAL_LT_INV_EQ, ← GSYM REAL_INV_NEG,
                 ← REAL_ARITH (← q r"x < &0 <=> &0 < --x")])

  let REAL_SGN_DIV ← prove
   r"!x y. real_sgn(x / y) = real_sgn(x) / real_sgn(y)"
   (REWRITE_TAC [REAL_SGN, REAL_ABS_DIV] THEN
    REWRITE_TAC [real_div, REAL_INV_MUL, REAL_INV_INV] THEN
    REAL_ARITH_TAC)

  let REAL_SGN_EQ ← prove
   r"(!x. real_sgn x = &0 <=> x = &0) /\
   (!x. real_sgn x = &1 <=> x > &0) /\
   (!x. real_sgn x = -- &1 <=> x < &0)"
   (REWRITE_TAC [real_sgn] THEN REAL_ARITH_TAC)

  let REAL_SGN_CASES ← prove
   r"!x. real_sgn x = &0 \/ real_sgn x = &1 \/ real_sgn x = -- &1"
   (REWRITE_TAC [real_sgn] THEN MESON_TAC [])

  let REAL_SGN_INEQS ← prove
   r"(!x. &0 <= real_sgn x <=> &0 <= x) /\
   (!x. &0 < real_sgn x <=> &0 < x) /\
   (!x. &0 >= real_sgn x <=> &0 >= x) /\
   (!x. &0 > real_sgn x <=> &0 > x) /\
   (!x. &0 = real_sgn x <=> &0 = x) /\
   (!x. real_sgn x <= &0 <=> x <= &0) /\
   (!x. real_sgn x < &0 <=> x < &0) /\
   (!x. real_sgn x >= &0 <=> x >= &0) /\
   (!x. real_sgn x > &0 <=> x > &0) /\
   (!x. real_sgn x = &0 <=> x = &0)"
   (REWRITE_TAC [real_sgn] THEN REAL_ARITH_TAC)

  let REAL_SGN_POW ← prove
   r"!x n. real_sgn(x pow n) = real_sgn(x) pow n"
   (GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [REAL_SGN_MUL, real_pow] THEN
    REWRITE_TAC [real_sgn, REAL_LT_01])

  let REAL_SGN_POW_2 ← prove
   r"!x. real_sgn(x pow 2) = real_sgn(abs x)"
   (REWRITE_TAC [real_sgn] THEN
    SIMP_TAC [← GSYM REAL_NOT_LE, REAL_ABS_POS, REAL_LE_POW_2,
              ← REAL_ARITH (← q r"&0 <= x ==> (x <= &0 <=> x = &0)")] THEN
    REWRITE_TAC [REAL_POW_EQ_0, REAL_ABS_ZERO, ARITH])

  let REAL_SGN_REAL_SGN ← prove
   r"!x. real_sgn(real_sgn x) = real_sgn x"
   (REWRITE_TAC [real_sgn] THEN REAL_ARITH_TAC)

  let REAL_INV_SGN ← prove
   r"!x. real_inv(real_sgn x) = real_sgn x"
   (GEN_TAC THEN REWRITE_TAC [real_sgn] THEN
    REPEAT COND_CASES_TAC THEN
    REWRITE_TAC [REAL_INV_0, REAL_INV_1, REAL_INV_NEG])

  let REAL_SGN_EQ_INEQ ← prove
   r"!x y. real_sgn x = real_sgn y <=>
         x = y \/ abs(x - y) < max (abs x) (abs y)"
   (REWRITE_TAC [real_sgn] THEN REAL_ARITH_TAC)

  let REAL_SGNS_EQ ← prove
   r"!x y. real_sgn x = real_sgn y <=>
         (x = &0 <=> y = &0) /\
         (x > &0 <=> y > &0) /\
         (x < &0 <=> y < &0)"
   (REWRITE_TAC [real_sgn] THEN REAL_ARITH_TAC)

  let REAL_SGNS_EQ_ALT ← prove
   r"!x y. real_sgn x = real_sgn y <=>
         (x = &0 ==> y = &0) /\
         (x > &0 ==> y > &0) /\
         (x < &0 ==> y < &0)"
   (REWRITE_TAC [real_sgn] THEN REAL_ARITH_TAC)

  /- ---------------------------------------------------------------------- -/
  /- Useful "without loss of generality" lemmas.                            -/
  /- ---------------------------------------------------------------------- -/

  let REAL_WLOG_LE ← prove
   r"(!x y. P x y <=> P y x) /\ (!x y. x <= y ==> P x y) ==> !x y. P x y"
   (MESON_TAC [REAL_LE_TOTAL])

  let REAL_WLOG_LT ← prove
   r"(!x. P x x) /\ (!x y. P x y <=> P y x) /\ (!x y. x < y ==> P x y)
   ==> !x y. P x y"
   (MESON_TAC [REAL_LT_TOTAL])

  let REAL_WLOG_LE_3 ← prove
   r"!P. (!x y z. P x y z ==> P y x z /\ P x z y) /\
       (!x y z:real. x <= y /\ y <= z ==> P x y z)
       ==> !x y z. P x y z"
   (MESON_TAC [REAL_LE_TOTAL])

  return {
    real_sgn, REAL_SGN_0, REAL_SGN_NEG, REAL_SGN_ABS, REAL_SGN_ABS_ALT,
    REAL_EQ_SGN_ABS, REAL_ABS_SGN, REAL_SGN, REAL_SGN_MUL, REAL_SGN_INV,
    REAL_SGN_DIV, REAL_SGN_EQ, REAL_SGN_CASES, REAL_SGN_INEQS, REAL_SGN_POW,
    REAL_SGN_POW_2, REAL_SGN_REAL_SGN, REAL_INV_SGN, REAL_SGN_EQ_INEQ,
    REAL_SGNS_EQ, REAL_SGNS_EQ_ALT, REAL_WLOG_LE, REAL_WLOG_LT,
    REAL_WLOG_LE_3 }

/- ---------------------------------------------------------------------- -/
/- Square roots. The existence derivation is laborious but independent of -/
/- any analytic or topological machinery, just using completeness directly.-/
/- We totalize by making sqrt(-x) = -sqrt(x), which looks rather unnatural-/
/- but allows many convenient properties to be used without sideconditions.-/
/- ---------------------------------------------------------------------- -/

/-- real.ml 1657-1993. -/
structure RealThms11 where
  sqrt                 : thm
  SQRT_UNIQUE          : thm
  POW_2_SQRT           : thm
  SQRT_0               : thm
  SQRT_1               : thm
  POW_2_SQRT_ABS       : thm
  SQRT_WORKS_GEN       : thm
  SQRT_UNIQUE_GEN      : thm
  SQRT_NEG             : thm
  REAL_SGN_SQRT        : thm
  SQRT_WORKS           : thm
  REAL_POS_EQ_SQUARE   : thm
  SQRT_POS_LE          : thm
  SQRT_POW_2           : thm
  SQRT_POW2            : thm
  SQRT_MUL             : thm
  SQRT_INV             : thm
  SQRT_DIV             : thm
  SQRT_LT_0            : thm
  SQRT_EQ_0            : thm
  SQRT_LE_0            : thm
  REAL_ABS_SQRT        : thm
  SQRT_MONO_LT         : thm
  SQRT_MONO_LE         : thm
  SQRT_MONO_LT_EQ      : thm
  SQRT_MONO_LE_EQ      : thm
  SQRT_INJ             : thm
  SQRT_EQ_1            : thm
  SQRT_POS_LT          : thm
  REAL_LE_LSQRT        : thm
  REAL_LE_RSQRT        : thm
  REAL_LT_LSQRT        : thm
  REAL_LT_RSQRT        : thm
  SQRT_EVEN_POW2       : thm
  REAL_DIV_SQRT        : thm
  REAL_RSQRT_LE        : thm
  REAL_LSQRT_LE        : thm
  REAL_SQRT_POW_2      : thm
  REAL_ABS_LE_SQRT_POS : thm
  REAL_ABS_LE_SQRT     : thm
  deriving Inhabited

/-- `sqrt` is a `new_definition`, so Session runs this once. -/
@[nospecialize]
def setupRealThms11 [HolBase]
    (A2 : HolMath.Arith.ArithThms2) (A5 : HolMath.Arith.ArithThms5)
    (A7 : HolMath.Arith.ArithThms7)
    (CnA : HolMath.CalcNum.ArithRewrites)
    (R : HolMath.RealAx.RealThms)
    (CiT : HolMath.CalcInt.CalcIntThms)
    (L : HolMath.RealArith.RealArithLemmas)
    (T2 : RealThms2) (T3 : RealThms3) (T4 : RealThms4) (T5 : RealThms5)
    (T6 : RealThms6) (T7 : RealThms7) (T8 : RealThms8) (T10 : RealThms10)
    (SELECT_CONV' : term → Except String thm)
    (NUM_REDUCE_CONV : ioconv)
    (new_definition' : term → IO (Except String thm))
    (REAL_ARITH' : term → IO (Except String thm))
    (MESON_TAC : List thm → tactic)
    (ASM_MESON_TAC : List thm → tactic) :
    ExceptT String IO RealThms11 := do
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let SELECT_CONV : ioconv := fun t => pure (SELECT_CONV' t)
  let REAL_ARITH (t : term) : ExceptT String IO thm := REAL_ARITH' t
  let REAL_ARITH_TAC := REAL_ARITH_TAC REAL_ARITH'
  let { REAL_NOT_LE, REAL_LE_LADD, .. } := T2
  let { REAL_LT_SUB_LADD, REAL_LT_IMP_NZ, .. } := T3
  let { REAL_ABS_POS, REAL_ABS_SUB, REAL_ABS_NZ, .. } := T4
  let { REAL_LE_MIN, REAL_MIN_LE, .. } := T5
  let { REAL_ABS_MUL, REAL_POW_LE, REAL_POW_LT, REAL_ABS_POW, REAL_LE_LMUL,
        REAL_INV_INV, REAL_LT_INV_EQ, REAL_ABS_INV, REAL_POW_MUL, REAL_POW_INV, .. } := T6
  let { REAL_LT_LMUL_EQ, REAL_LT_LDIV_EQ, REAL_EQ_LDIV_EQ, REAL_LE_MUL2,
        REAL_LT_INV2, REAL_POW_LE2, .. } := T7
  let { REAL_POW_POW, REAL_LT_DIV, REAL_POW2_ABS, REAL_LE_SQUARE_ABS,
        REAL_LT_SQUARE_ABS, REAL_LE_POW_2, REAL_LT_POW_2, REAL_POW_ZERO,
        REAL_POW_LT2_REV, .. } := T8
  let { real_sgn, REAL_SGN_0, REAL_SGN_NEG, REAL_SGN_MUL, REAL_SGN_INV,
        REAL_SGN_EQ, REAL_SGN_POW, REAL_SGN_POW_2, REAL_SGN_REAL_SGN,
        REAL_WLOG_LE, .. } := T10
  let { REAL_MUL_LID, REAL_LE_REFL, REAL_LE_ANTISYM, REAL_LE_TRANS,
        REAL_LE_TOTAL, REAL_LE_MUL, real_gt, real_abs, real_div, REAL_COMPLETE, .. } := R
  let { REAL_MUL_LZERO, REAL_NEG_0, REAL_POW_NEG, REAL_ABS_NUM, REAL_ABS_NEG, .. } := CiT
  let { REAL_LT_IMP_LE, REAL_LTE_TRANS, REAL_LET_TRANS, REAL_LE_ADD,
        REAL_LE_LT, REAL_SUB_LT, REAL_NOT_LT, REAL_SUB_0, REAL_LT_LE,
        REAL_ENTIRE, REAL_LE_SQUARE, REAL_MUL_RID, REAL_POW_2, REAL_POS, .. } := L
  let { MULT_SYM, .. } := A2
  let { EVEN_EXISTS, .. } := A5
  let { DIV_MULT, .. } := A7
  let { ARITH_EQ, ARITH, .. } := CnA
  let { SELECT_UNIQUE, NOT_IMP, CONTRAPOS_THM, .. } := HolBase.C
  let { IMP_CONJ_ALT, UNWIND_THM2, LEFT_IMP_EXISTS_THM, MONO_EXISTS, .. } := HolBase.T

  let sqrt ← new_definition
   r"sqrt(x) = @y. real_sgn y = real_sgn x /\ y pow 2 = abs x"

  let SQRT_UNIQUE ← prove
   r"!x y. &0 <= y /\ y pow 2 = x ==> sqrt(x) = y"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [sqrt] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [REAL_SGN_POW_2, REAL_ABS_POW] THEN
    X_GEN_TAC (← q r"z:real") THEN ASM_REWRITE_TAC [real_abs] THEN
    REWRITE_TAC [REAL_ENTIRE, REAL_SUB_0, ← REAL_ARITH
      (← q r"x pow 2 = y pow 2 <=> (x - y) * (x - --y) = &0")] THEN
    REWRITE_TAC [real_sgn] THEN REPEAT (POP_ASSUM MP_TAC) THEN
    REAL_ARITH_TAC)

  let POW_2_SQRT ← prove
   r"!x. &0 <= x ==> sqrt(x pow 2) = x"
   (MESON_TAC [SQRT_UNIQUE])

  let SQRT_0 ← prove
   r"sqrt(&0) = &0"
   (MESON_TAC [SQRT_UNIQUE, REAL_POW_2, REAL_MUL_LZERO, REAL_POS])

  let SQRT_1 ← prove
   r"sqrt(&1) = &1"
   (MESON_TAC [SQRT_UNIQUE, REAL_POW_2, REAL_MUL_LID, REAL_POS])

  let POW_2_SQRT_ABS ← prove
   r"!x. sqrt(x pow 2) = abs(x)"
   (GEN_TAC THEN MATCH_MP_TAC SQRT_UNIQUE THEN
    REWRITE_TAC [REAL_ABS_POS, REAL_POW_2, ← GSYM REAL_ABS_MUL] THEN
    REWRITE_TAC [real_abs, REAL_LE_SQUARE])

  let SQRT_WORKS_GEN ← prove
   r"!x. real_sgn(sqrt x) = real_sgn x /\ sqrt(x) pow 2 = abs x"
   (← do
    let lemma ← prove
     r"!x y. x pow 2 < y ==> ?x'. x < x' /\ x' pow 2 < y"
      (REPEAT STRIP_TAC THEN
       EXISTS_TAC (← q r"abs x + min (&1) ((y - x pow 2) / (&2 * abs x + &2))") THEN
       ASSUME_TAC (← REAL_ARITH (← q r"&0 < &2 * abs x + &1 /\ &0 < &2 * abs x + &2")) THEN
       ASM_SIMP_TAC [REAL_LT_DIV, REAL_SUB_LT, ← REAL_ARITH
         (← q r"&0 < y ==> x < abs x + min (&1) y")] THEN
       REWRITE_TAC [← REAL_ARITH (← q r"(x + e) pow 2 = e * (&2 * x + e) + x pow 2")] THEN
       REWRITE_TAC [REAL_POW2_ABS, ← GSYM REAL_LT_SUB_LADD] THEN
       TRANS_TAC REAL_LET_TRANS
         (← q r"(y - x pow 2) / (&2 * abs x + &2) * (&2 * abs x + &1)") THEN
       CONJ_TAC THENL
        [MATCH_MP_TAC REAL_LE_MUL2 THEN
         REWRITE_TAC [REAL_LE_MIN, REAL_POS, REAL_MIN_LE, REAL_LE_REFL] THEN
         ASM_SIMP_TAC [REAL_LE_ADD, REAL_POS, REAL_LE_MUL, REAL_ABS_POS,
                       REAL_LT_IMP_LE, REAL_LT_DIV, REAL_SUB_LT, REAL_LE_MIN] THEN
         REWRITE_TAC [REAL_LE_LADD, REAL_MIN_LE, REAL_LE_REFL],
         SIMP_TAC [real_div, ← REAL_ARITH (← q r"(a * inv b) * c = (a * c) * inv b")] THEN
         REWRITE_TAC [← GSYM real_div] THEN
         ASM_SIMP_TAC [REAL_LT_LDIV_EQ, REAL_LT_LMUL_EQ, REAL_SUB_LT] THEN
         REAL_ARITH_TAC])
    let lemma' ← prove
     r"!x y. &0 < x /\ &0 < y /\ y < x pow 2
           ==> ?x'. x' < x /\ &0 < x' /\ y < x' pow 2"
      (REPEAT STRIP_TAC THEN
       MP_TAC (← ISPECL [← q r"inv(abs x):real", ← q r"inv y:real"] lemma) THEN
       ASM_SIMP_TAC [REAL_POW_INV, REAL_POW2_ABS, REAL_LT_INV2] THEN
       REWRITE_TAC [← GSYM REAL_ABS_INV] THEN
       DISCH_THEN (X_CHOOSE_THEN (← q r"x':real") STRIP_ASSUME_TAC) THEN
       EXISTS_TAC (← q r"inv x':real") THEN REWRITE_TAC [REAL_POW_INV] THEN
       REWRITE_TAC [REAL_LT_INV_EQ] THEN CONJ_TAC THENL
        [GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_INV_INV],
         CONJ_TAC THENL [REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC,
         ALL_TAC] THEN
         GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_INV_INV]] THEN
       MATCH_MP_TAC REAL_LT_INV2 THEN
       (CONJ_TAC THENL
         [ALL_TAC, REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC]) THEN
       ASM_REWRITE_TAC [REAL_LT_INV_EQ, REAL_LT_POW_2] THEN
       REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC)
    let main_lemma ← prove
     r"!y. &0 < y ==> ?x. x pow 2 = y"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o MATCH_MP REAL_LT_IMP_NZ) THEN
       MP_TAC (← ISPEC (← q r"\x. &0 <= x /\ x pow 2 <= y") REAL_COMPLETE) THEN
       REWRITE_TAC [] THEN ANTS_TAC THENL
        [CONJ_TAC THENL
          [EXISTS_TAC (← q r"&0") THEN REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC,
           ALL_TAC] THEN
         EXISTS_TAC (← q r"y + &1") THEN X_GEN_TAC (← q r"x:real") THEN
         DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
         GEN_REWRITE_TAC I [← GSYM CONTRAPOS_THM] THEN
         REWRITE_TAC [REAL_NOT_LE] THEN DISCH_TAC THEN
         TRANS_TAC REAL_LET_TRANS (← q r"(y + &1) pow 2") THEN
         ASM_SIMP_TAC [← GSYM REAL_LT_SQUARE_ABS, REAL_POW_LT, ← REAL_ARITH
          (← q r"&0 < y /\ &0 < y pow 2 ==> y <= (y + &1) pow 2")] THEN
         REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC,
         MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"s:real") THEN STRIP_TAC] THEN
       REWRITE_TAC [← GSYM REAL_LE_ANTISYM, ← GSYM REAL_NOT_LT] THEN
       REPEAT STRIP_TAC THENL
        [MP_TAC (← ISPECL [← q r"s:real", ← q r"y:real"] lemma') THEN
         ASM_REWRITE_TAC [NOT_IMP] THEN CONJ_TAC THENL
          [UNDISCH_TAC (← q r"y:real < s pow 2") THEN
           ASM_CASES_TAC (← q r"s = &0") THEN ASM_REWRITE_TAC [REAL_LT_LE] THEN
           REWRITE_TAC [REAL_POW_ZERO] THEN CONV_TAC NUM_REDUCE_CONV THEN
           ASM_REWRITE_TAC [REAL_NOT_LE] THEN
           STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
           UNDISCH_TAC (← q r"&0 < y") THEN REAL_ARITH_TAC,
           DISCH_THEN (X_CHOOSE_THEN (← q r"z:real")
            (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
           REWRITE_TAC [REAL_NOT_LT] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
           X_GEN_TAC (← q r"x:real") THEN
           DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
           GEN_REWRITE_TAC I [← GSYM CONTRAPOS_THM] THEN
           REWRITE_TAC [REAL_NOT_LE] THEN DISCH_TAC THEN
           TRANS_TAC REAL_LTE_TRANS (← q r"(z:real) pow 2") THEN
           ASM_REWRITE_TAC [← GSYM REAL_LE_SQUARE_ABS] THEN
           REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC],
         MP_TAC (← ISPECL [← q r"s:real", ← q r"y:real"] lemma) THEN ASM_REWRITE_TAC [] THEN
         DISCH_THEN (X_CHOOSE_THEN (← q r"z:real")
          (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
         MATCH_MP_TAC (← REAL_ARITH (← q r"abs z <= s ==> s < z ==> F")) THEN
         FIRST_X_ASSUM MATCH_MP_TAC THEN
         ASM_SIMP_TAC [REAL_ABS_POS, REAL_POW2_ABS, REAL_LT_IMP_LE]])
    pure
     (GEN_TAC THEN REWRITE_TAC [sqrt] THEN CONV_TAC SELECT_CONV THEN
      SUBGOAL_THEN (← q r"!x. &0 < x ==> ?y. &0 < y /\ y pow 2 = x") ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN MP_TAC (← SPEC (← q r"x:real") main_lemma) THEN
        ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"y:real") THEN
        STRIP_TAC THEN EXISTS_TAC (← q r"abs y:real") THEN
        ASM_REWRITE_TAC [REAL_POW2_ABS, ← GSYM REAL_ABS_NZ] THEN
        DISCH_THEN SUBST_ALL_TAC THEN
        REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC,
        ASM_CASES_TAC (← q r"x = &0") THEN
        ASM_REWRITE_TAC [REAL_SGN_0, REAL_SGN_EQ, UNWIND_THM2] THEN
        REWRITE_TAC [REAL_ABS_NUM, REAL_POW_ZERO, ARITH] THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"abs x")) THEN
        ASM_REWRITE_TAC [← GSYM REAL_ABS_NZ] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"y:real") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q r"real_sgn x * y") THEN
        ASM_REWRITE_TAC [REAL_POW_MUL, ← GSYM REAL_SGN_POW, REAL_SGN_POW_2] THEN
        REWRITE_TAC [REAL_SGN_MUL, REAL_SGN_REAL_SGN] THEN
        ASM_SIMP_TAC [real_sgn, ← REAL_ARITH (← q r"&0 < abs x <=> ~(x = &0)")] THEN
        REWRITE_TAC [REAL_MUL_LID, REAL_MUL_RID]]))

  let SQRT_UNIQUE_GEN ← prove
   r"!x y. real_sgn y = real_sgn x /\ y pow 2 = abs x ==> sqrt x = y"
   (REPEAT GEN_TAC THEN
    MP_TAC (← GSYM (← SPEC (← q r"x:real") SQRT_WORKS_GEN)) THEN
    SIMP_TAC [REAL_ENTIRE, REAL_SUB_0, ← REAL_ARITH
      (← q r"x pow 2 = y pow 2 <=> (x:real - y) * (x - --y) = &0")] THEN
    DISCH_THEN (K ALL_TAC) THEN REWRITE_TAC [IMP_CONJ_ALT] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [REAL_SGN_NEG] THEN
    SIMP_TAC [← REAL_ARITH (← q r"--x = x <=> x = &0"), REAL_SGN_EQ, REAL_NEG_0, SQRT_0])

  let SQRT_NEG ← prove
   r"!x. sqrt(--x) = --sqrt(x)"
   (GEN_TAC THEN MATCH_MP_TAC SQRT_UNIQUE_GEN THEN
    REWRITE_TAC [REAL_SGN_NEG, REAL_POW_NEG, REAL_ABS_NEG, ARITH] THEN
    REWRITE_TAC [SQRT_WORKS_GEN])

  let REAL_SGN_SQRT ← prove
   r"!x. real_sgn(sqrt x) = real_sgn x"
   (REWRITE_TAC [SQRT_WORKS_GEN])

  let SQRT_WORKS ← prove
   r"!x. &0 <= x ==> &0 <= sqrt(x) /\ sqrt(x) pow 2 = x"
   (REPEAT STRIP_TAC THEN MP_TAC (← SPEC (← q r"x:real") SQRT_WORKS_GEN) THEN
    REWRITE_TAC [real_sgn] THEN REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC)

  let REAL_POS_EQ_SQUARE ← prove
   r"!x. &0 <= x <=> ?y. y pow 2 = x"
   (MESON_TAC [REAL_LE_POW_2, SQRT_WORKS])

  let SQRT_POS_LE ← prove
   r"!x. &0 <= x ==> &0 <= sqrt(x)"
   (MESON_TAC [SQRT_WORKS])

  let SQRT_POW_2 ← prove
   r"!x. &0 <= x ==> sqrt(x) pow 2 = x"
   (MESON_TAC [SQRT_WORKS])

  let SQRT_POW2 ← prove
   r"!x. sqrt(x) pow 2 = x <=> &0 <= x"
   (MESON_TAC [REAL_POW_2, REAL_LE_SQUARE, SQRT_POW_2])

  let SQRT_MUL ← prove
   r"!x y. sqrt(x * y) = sqrt x * sqrt y"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC SQRT_UNIQUE_GEN THEN
    REWRITE_TAC [REAL_SGN_MUL, REAL_POW_MUL, SQRT_WORKS_GEN, REAL_ABS_MUL])

  let SQRT_INV ← prove
   r"!x. sqrt (inv x) = inv(sqrt x)"
   (GEN_TAC THEN MATCH_MP_TAC SQRT_UNIQUE_GEN THEN
    REWRITE_TAC [REAL_SGN_INV, REAL_POW_INV, REAL_ABS_INV, SQRT_WORKS_GEN])

  let SQRT_DIV ← prove
   r"!x y. sqrt (x / y) = sqrt x / sqrt y"
   (REWRITE_TAC [real_div, SQRT_MUL, SQRT_INV])

  let SQRT_LT_0 ← prove
   r"!x. &0 < sqrt x <=> &0 < x"
   (REWRITE_TAC [← GSYM real_gt, ← GSYM REAL_SGN_EQ, REAL_SGN_SQRT])

  let SQRT_EQ_0 ← prove
   r"!x. sqrt x = &0 <=> x = &0"
   (ONCE_REWRITE_TAC [← GSYM REAL_SGN_EQ] THEN REWRITE_TAC [REAL_SGN_SQRT])

  let SQRT_LE_0 ← prove
   r"!x. &0 <= sqrt x <=> &0 <= x"
   (REWRITE_TAC [← REAL_ARITH (← q r"&0 <= x <=> &0 < x \/ x = &0")] THEN
    REWRITE_TAC [SQRT_LT_0, SQRT_EQ_0])

  let REAL_ABS_SQRT ← prove
   r"!x. abs(sqrt x) = sqrt(abs x)"
   (GEN_TAC THEN REWRITE_TAC [real_abs, SQRT_LE_0] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [SQRT_NEG])

  let SQRT_MONO_LT ← prove
   r"!x y. x < y ==> sqrt(x) < sqrt(y)"
   (SUBGOAL_THEN (← q r"!x y. &0 <= x /\ x < y ==> sqrt x < sqrt y") ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LT2_REV THEN
      EXISTS_TAC (← q r"2") THEN ASM_REWRITE_TAC [SQRT_WORKS_GEN, SQRT_LE_0] THEN
      REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC,
      REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"&0 <= x") THEN ASM_SIMP_TAC [] THEN
      ASM_CASES_TAC (← q r"&0 <= y") THENL
       [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q r"&0") THEN
        ASM_REWRITE_TAC [← GSYM REAL_NOT_LE, SQRT_LE_0],
        FIRST_X_ASSUM (MP_TAC o SPECL [← q r"--y:real", ← q r"--x:real"]) THEN
        REWRITE_TAC [SQRT_NEG] THEN REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC]])

  let SQRT_MONO_LE ← prove
   r"!x y. x <= y ==> sqrt(x) <= sqrt(y)"
   (MESON_TAC [REAL_LE_LT, SQRT_MONO_LT])

  let SQRT_MONO_LT_EQ ← prove
   r"!x y. sqrt(x) < sqrt(y) <=> x < y"
   (MESON_TAC [REAL_NOT_LT, SQRT_MONO_LT, SQRT_MONO_LE])

  let SQRT_MONO_LE_EQ ← prove
   r"!x y. sqrt(x) <= sqrt(y) <=> x <= y"
   (MESON_TAC [REAL_NOT_LT, SQRT_MONO_LT, SQRT_MONO_LE])

  let SQRT_INJ ← prove
   r"!x y. sqrt(x) = sqrt(y) <=> x = y"
   (SIMP_TAC [← GSYM REAL_LE_ANTISYM, SQRT_MONO_LE_EQ])

  let SQRT_EQ_1 ← prove
   r"!x. sqrt x = &1 <=> x = &1"
   (MESON_TAC [SQRT_INJ, SQRT_1])

  let SQRT_POS_LT ← prove
   r"!x. &0 < x ==> &0 < sqrt(x)"
   (MESON_TAC [REAL_LT_LE, SQRT_POS_LE, SQRT_EQ_0])

  let REAL_LE_LSQRT ← prove
   r"!x y. &0 <= y /\ x <= y pow 2 ==> sqrt(x) <= y"
   (MESON_TAC [SQRT_MONO_LE, REAL_POW_LE, POW_2_SQRT])

  let REAL_LE_RSQRT ← prove
   r"!x y. x pow 2 <= y ==> x <= sqrt(y)"
   (MESON_TAC [REAL_LE_TOTAL, SQRT_MONO_LE, SQRT_POS_LE, REAL_POW_2,
               REAL_LE_SQUARE, REAL_LE_TRANS, POW_2_SQRT])

  let REAL_LT_LSQRT ← prove
   r"!x y. &0 <= y /\ x < y pow 2 ==> sqrt x < y"
   (MESON_TAC [SQRT_MONO_LT, REAL_POW_LE, POW_2_SQRT])

  let REAL_LT_RSQRT ← prove
   r"!x y. x pow 2 < y ==> x < sqrt(y)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC (← REAL_ARITH (← q r"abs x < a ==> x < a")) THEN
    REWRITE_TAC [← GSYM POW_2_SQRT_ABS] THEN MATCH_MP_TAC SQRT_MONO_LT THEN
    ASM_REWRITE_TAC [REAL_POW_2, REAL_LE_SQUARE])

  let SQRT_EVEN_POW2 ← prove
   r"!n. EVEN n ==> (sqrt(&2 pow n) = &2 pow (n DIV 2))"
   (SIMP_TAC [EVEN_EXISTS, LEFT_IMP_EXISTS_THM, DIV_MULT, ARITH_EQ] THEN
    MESON_TAC [SQRT_UNIQUE, REAL_POW_POW, MULT_SYM, REAL_POW_LE, REAL_POS])

  let REAL_DIV_SQRT ← prove
   r"!x. &0 <= x ==> x / sqrt(x) = sqrt(x)"
   (REWRITE_TAC [REAL_LE_LT] THEN REPEAT STRIP_TAC THENL
     [ALL_TAC, ASM_MESON_TAC [SQRT_0, real_div, REAL_MUL_LZERO]] THEN
    ASM_SIMP_TAC [REAL_EQ_LDIV_EQ, SQRT_POS_LT, ← GSYM REAL_POW_2] THEN
    ASM_SIMP_TAC [SQRT_POW_2, REAL_LT_IMP_LE])

  let REAL_RSQRT_LE ← prove
   r"!x y. &0 <= x /\ &0 <= y /\ x <= sqrt y ==> x pow 2 <= y"
   (MESON_TAC [REAL_POW_LE2, SQRT_POW_2])

  let REAL_LSQRT_LE ← prove
   r"!x y. &0 <= x /\ sqrt x <= y ==> x <= y pow 2"
   (MESON_TAC [REAL_POW_LE2, SQRT_POS_LE, REAL_LE_TRANS, SQRT_POW_2])

  let REAL_SQRT_POW_2 ← prove
   r"!x. sqrt x pow 2 = abs x"
   (REWRITE_TAC [SQRT_WORKS_GEN])

  let REAL_ABS_LE_SQRT_POS ← prove
   r"!x y. &0 <= x /\ &0 <= y ==> abs(sqrt x - sqrt y) <= sqrt(abs(x - y))"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RSQRT THEN
    REWRITE_TAC [REAL_POW_2] THEN
    TRANS_TAC REAL_LE_TRANS (← q r"abs(sqrt x - sqrt y) * abs(sqrt x + sqrt y)") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [REAL_ABS_POS] THEN
      MATCH_MP_TAC (← REAL_ARITH
       (← q r"&0 <= x /\ &0 <= y ==> abs(x - y) <= abs(x + y)")) THEN
      ASM_SIMP_TAC [SQRT_POS_LE],
      REWRITE_TAC [← GSYM REAL_ABS_MUL, ← REAL_ARITH
       (← q r"(x - y:real) * (x + y) = x pow 2 - y pow 2")] THEN
      ASM_SIMP_TAC [SQRT_POW_2, REAL_LE_REFL]])

  let REAL_ABS_LE_SQRT ← prove
   r"!x y. abs(sqrt x - sqrt y) <= sqrt(&2 * abs(x - y))"
   (MATCH_MP_TAC REAL_WLOG_LE THEN
    CONJ_TAC THENL [REWRITE_TAC [REAL_ABS_SUB], ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:real", ← q r"y:real"] THEN DISCH_TAC THEN
    ASM_CASES_TAC (← q r"&0 <= x") THENL
     [TRANS_TAC REAL_LE_TRANS (← q r"sqrt(abs(x - y))") THEN
      REWRITE_TAC [SQRT_MONO_LE_EQ, ← REAL_ARITH (← q r"abs x <= &2 * abs x")] THEN
      MATCH_MP_TAC REAL_ABS_LE_SQRT_POS THEN
      REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC,
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"&0 <= y") THENL
     [ALL_TAC,
      ONCE_REWRITE_TAC [← REAL_ARITH (← q r"abs(x - y) = abs(--x - --y)")] THEN
      REWRITE_TAC [← GSYM SQRT_NEG] THEN
      TRANS_TAC REAL_LE_TRANS (← q r"sqrt(abs(--x - --y))") THEN
      REWRITE_TAC [SQRT_MONO_LE_EQ, ← REAL_ARITH (← q r"abs x <= &2 * abs x")] THEN
      MATCH_MP_TAC REAL_ABS_LE_SQRT_POS THEN
      REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC] THEN
    ASM_SIMP_TAC [SQRT_LE_0, ← REAL_ARITH
     (← q r"~(&0 <= x) /\ &0 <= y ==> abs(x - y) = y - x")] THEN
    MATCH_MP_TAC REAL_LE_RSQRT THEN
    MP_TAC (← SPEC (← q r"sqrt(--x) - sqrt y") REAL_LE_POW_2) THEN
    REWRITE_TAC [← REAL_ARITH
     (← q r"(x - y:real) pow 2 = (x pow 2 + y pow 2) - &2 * x * y")] THEN
    REWRITE_TAC [REAL_SQRT_POW_2] THEN REWRITE_TAC [SQRT_NEG, REAL_ABS_NEG] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC)

  return {
    sqrt, SQRT_UNIQUE, POW_2_SQRT, SQRT_0, SQRT_1, POW_2_SQRT_ABS,
    SQRT_WORKS_GEN, SQRT_UNIQUE_GEN, SQRT_NEG, REAL_SGN_SQRT, SQRT_WORKS,
    REAL_POS_EQ_SQUARE, SQRT_POS_LE, SQRT_POW_2, SQRT_POW2, SQRT_MUL,
    SQRT_INV, SQRT_DIV, SQRT_LT_0, SQRT_EQ_0, SQRT_LE_0, REAL_ABS_SQRT,
    SQRT_MONO_LT, SQRT_MONO_LE, SQRT_MONO_LT_EQ, SQRT_MONO_LE_EQ, SQRT_INJ,
    SQRT_EQ_1, SQRT_POS_LT, REAL_LE_LSQRT, REAL_LE_RSQRT, REAL_LT_LSQRT,
    REAL_LT_RSQRT, SQRT_EVEN_POW2, REAL_DIV_SQRT, REAL_RSQRT_LE,
    REAL_LSQRT_LE, REAL_SQRT_POW_2, REAL_ABS_LE_SQRT_POS, REAL_ABS_LE_SQRT }


end HolMath.Real
