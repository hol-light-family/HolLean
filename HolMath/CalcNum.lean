/- File: CalcNum.lean
Calculation with naturals.
John Harrison, University of Cambridge Computer Laboratory
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Original (c) Copyright, Mario Carneiro 2020
Lean4 translation by Chris Walton 2026 -/

import HolCore.Bool
import HolCore.Equal
import HolCore.Drule
import HolCore.Tactics
import HolCore.Itab
import HolCore.Simp
import HolCore.Parser
import HolCore.Printer
import HolCore.Nets
import HolCore.Theorems
import HolCore.IndDefs
import HolCore.Classic
import HolCore.Canon
import HolCore.Meson
import HolMath.Pair
import HolMath.Nums
import HolMath.Recursion
import HolMath.Arith
import HolMath.Wf
import HolMath.Compute
import HolMath.Base

namespace HolMath.CalcNum

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms DSLThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax

/- Simple rule to get rid of NUMERAL constant. -/

/-- `DENUMERAL = GEN_REWRITE_RULE DEPTH_CONV [NUMERAL]` (calc_num.ml 17). -/
def DENUMERAL [HolBase] (NUMERAL : thm) : thm → ExceptT String IO thm :=
  GEN_REWRITE_RULE DEPTH_CONV [NUMERAL]

/-- The `ARITH_*` rewrite collection of `calc_num.ml`, plus the combined
    `ARITH` and `EXP_2_NE_0`. -/
structure ArithRewrites where
  ARITH_ZERO  : thm
  BIT0_0      : thm
  BIT1_0      : thm
  ARITH_SUC   : thm
  ARITH_PRE   : thm
  ARITH_ADD   : thm
  ARITH_MULT  : thm
  ARITH_EXP   : thm
  ARITH_EVEN  : thm
  ARITH_ODD   : thm
  ARITH_LE    : thm
  ARITH_LT    : thm
  ARITH_GE    : thm
  ARITH_GT    : thm
  ARITH_EQ    : thm
  ARITH_SUB   : thm
  ARITH       : thm
  EXP_2_NE_0  : thm
  deriving Inhabited

/-- Big collection of rewrites to do trivial arithmetic (calc_num.ml 19-205).
    Note that we have none for DIV and MOD, and that PRE and SUB are a bit
    inefficient; log(n)^2 instead of log(n). -/
@[nospecialize]
def setupArithRewrites [HolBase] (N : HolMath.Nums.NumsThms)
    (A1 : HolMath.Arith.ArithThms1) (A2 : HolMath.Arith.ArithThms2)
    (A3 : HolMath.Arith.ArithThms3) (A4 : HolMath.Arith.ArithThms4)
    (A5 : HolMath.Arith.ArithThms5) :
    ExceptT String IO ArithRewrites := do
  let INDUCT_TAC := HolMath.Nums.INDUCT_TAC N.num_INDUCTION
  let { NUMERAL, NOT_SUC, SUC_INJ, .. } := N
  let DENUMERAL := DENUMERAL NUMERAL
  let { DISJ_SYM, .. } := HolBase.T
  let { PRE, ADD_CLAUSES, ADD_ASSOC, ADD_AC, BIT0, BIT1, ADD1, .. } := A1
  let { MULT_CLAUSES, LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_EQ_0,
        EQ_MULT_LCANCEL, MULT_2, EXP, EXP_EQ_0, EXP_ADD, LE, GE, GT, LE_SUC_LT,
        LE_0, .. } := A2
  let { LE_ANTISYM, LET_ANTISYM, LTE_ANTISYM, LE_LT, NOT_LE, .. } := A3
  let { LE_EXISTS, LE_MULT_LCANCEL, LT_MULT_LCANCEL, .. } := A4
  let { EVEN, ODD, EVEN_ADD, EVEN_MULT, ODD_ADD, SUB, SUB_0, SUB_SUC, ADD_SUB2,
        SUB_EQ_0, LEFT_SUB_DISTRIB, .. } := A5

  let ARITH_ZERO ← prove
   r"(NUMERAL 0 = 0) /\
   (BIT0 _0 = _0)"
   (REWRITE_TAC [NUMERAL, BIT0, ← DENUMERAL ADD_CLAUSES])

  let BIT0_0 ← prove
   r"BIT0 0 = 0"
   (REWRITE_TAC [NUMERAL, ARITH_ZERO])

  let BIT1_0 ← prove
   r"BIT1 0 = 1"
   (REWRITE_TAC [NUMERAL])

  let ARITH_SUC ← prove
   r"(!n. SUC(NUMERAL n) = NUMERAL(SUC n)) /\
   (SUC _0 = BIT1 _0) /\
   (!n. SUC (BIT0 n) = BIT1 n) /\
   (!n. SUC (BIT1 n) = BIT0 (SUC n))"
   (REWRITE_TAC [NUMERAL, BIT0, BIT1, ← DENUMERAL ADD_CLAUSES])

  let ARITH_PRE ← prove
   r"(!n. PRE(NUMERAL n) = NUMERAL(PRE n)) /\
   (PRE _0 = _0) /\
   (!n. PRE(BIT0 n) = if n = _0 then _0 else BIT1 (PRE n)) /\
   (!n. PRE(BIT1 n) = BIT0 n)"
   (REWRITE_TAC [NUMERAL, BIT1, BIT0, ← DENUMERAL PRE] THEN INDUCT_TAC THEN
    REWRITE_TAC [NUMERAL, ← DENUMERAL PRE, ← DENUMERAL ADD_CLAUSES, ← DENUMERAL NOT_SUC,
                 ARITH_ZERO])

  let ARITH_ADD ← prove
   r"(!m n. NUMERAL(m) + NUMERAL(n) = NUMERAL(m + n)) /\
   (_0 + _0 = _0) /\
   (!n. _0 + BIT0 n = BIT0 n) /\
   (!n.        _0 + BIT1 n = BIT1 n) /\
   (!n.   BIT0 n + _0 = BIT0 n) /\
   (!n.   BIT1 n + _0 = BIT1 n) /\
   (!m n. BIT0 m + BIT0 n = BIT0 (m + n)) /\
   (!m n. BIT0 m + BIT1 n = BIT1 (m + n)) /\
   (!m n. BIT1 m + BIT0 n = BIT1 (m + n)) /\
   (!m n. BIT1 m + BIT1 n = BIT0 (SUC(m + n)))"
   (PURE_REWRITE_TAC [NUMERAL, BIT0, BIT1, ← DENUMERAL ADD_CLAUSES, SUC_INJ] THEN
    REWRITE_TAC [ADD_AC])

  let ARITH_MULT ← prove
   r"(!m n. NUMERAL(m) * NUMERAL(n) = NUMERAL(m * n)) /\
   (_0 * _0 = _0) /\
   (!n. _0 * BIT0 n = _0) /\
   (!n. _0 * BIT1 n = _0) /\
   (!n. BIT0 n * _0 = _0) /\
   (!n. BIT1 n * _0 = _0) /\
   (!m n. BIT0 m * BIT0 n = BIT0 (BIT0 (m * n))) /\
   (!m n. BIT0 m * BIT1 n = BIT0 m + BIT0 (BIT0 (m * n))) /\
   (!m n. BIT1 m * BIT0 n = BIT0 n + BIT0 (BIT0 (m * n))) /\
   (!m n. BIT1 m * BIT1 n = BIT1 m + BIT0 n + BIT0 (BIT0 (m * n)))"
   (PURE_REWRITE_TAC [NUMERAL, BIT0, BIT1, ← DENUMERAL MULT_CLAUSES,
                      ← DENUMERAL ADD_CLAUSES, SUC_INJ] THEN
    REWRITE_TAC [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, ADD_AC])

  let ARITH_EXP ← prove
   r"(!m n. (NUMERAL m) EXP (NUMERAL n) = NUMERAL(m EXP n)) /\
   (_0 EXP _0 = BIT1 _0) /\
   (!m. (BIT0 m) EXP _0 = BIT1 _0) /\
   (!m. (BIT1 m) EXP _0 = BIT1 _0) /\
   (!n. _0 EXP (BIT0 n) = (_0 EXP n) * (_0 EXP n)) /\
   (!m n. (BIT0 m) EXP (BIT0 n) = ((BIT0 m) EXP n) * ((BIT0 m) EXP n)) /\
   (!m n. (BIT1 m) EXP (BIT0 n) = ((BIT1 m) EXP n) * ((BIT1 m) EXP n)) /\
   (!n. _0 EXP (BIT1 n) = _0) /\
   (!m n. (BIT0 m) EXP (BIT1 n) =
        BIT0 m * ((BIT0 m) EXP n) * ((BIT0 m) EXP n)) /\
   (!m n. (BIT1 m) EXP (BIT1 n) =
        BIT1 m * ((BIT1 m) EXP n) * ((BIT1 m) EXP n))"
   (REWRITE_TAC [NUMERAL] THEN REPEAT STRIP_TAC THEN
    TRY (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [BIT0, BIT1]) THEN
    REWRITE_TAC [← DENUMERAL EXP, ← DENUMERAL MULT_CLAUSES, EXP_ADD])

  let ARITH_EVEN ← prove
   r"(!n. EVEN(NUMERAL n) <=> EVEN n) /\
   (EVEN _0 <=> T) /\
   (!n. EVEN(BIT0 n) <=> T) /\
   (!n. EVEN(BIT1 n) <=> F)"
   (REWRITE_TAC [NUMERAL, BIT1, BIT0, ← DENUMERAL EVEN, EVEN_ADD])

  let ARITH_ODD ← prove
   r"(!n. ODD(NUMERAL n) <=> ODD n) /\
   (ODD _0 <=> F) /\
   (!n. ODD(BIT0 n) <=> F) /\
   (!n. ODD(BIT1 n) <=> T)"
   (REWRITE_TAC [NUMERAL, BIT1, BIT0, ← DENUMERAL ODD, ODD_ADD])

  let ARITH_LE ← prove
   r"(!m n. NUMERAL m <= NUMERAL n <=> m <= n) /\
   ((_0 <= _0) <=> T) /\
   (!n. (BIT0 n <= _0) <=> n <= _0) /\
   (!n. (BIT1 n <= _0) <=> F) /\
   (!n. (_0 <= BIT0 n) <=> T) /\
   (!n. (_0 <= BIT1 n) <=> T) /\
   (!m n. (BIT0 m <= BIT0 n) <=> m <= n) /\
   (!m n. (BIT0 m <= BIT1 n) <=> m <= n) /\
   (!m n. (BIT1 m <= BIT0 n) <=> m < n) /\
   (!m n. (BIT1 m <= BIT1 n) <=> m <= n)"
   (REWRITE_TAC [NUMERAL, BIT1, BIT0, ← DENUMERAL NOT_SUC,
        ← DENUMERAL (← GSYM NOT_SUC), SUC_INJ] THEN
    REWRITE_TAC [← DENUMERAL LE_0] THEN REWRITE_TAC [← DENUMERAL LE, ← GSYM MULT_2] THEN
    REWRITE_TAC [LE_MULT_LCANCEL, SUC_INJ,
                 ← DENUMERAL MULT_EQ_0, ← DENUMERAL NOT_SUC] THEN
    REWRITE_TAC [← DENUMERAL NOT_SUC] THEN REWRITE_TAC [LE_SUC_LT] THEN
    REWRITE_TAC [LT_MULT_LCANCEL] THEN
    SUBGOAL_THEN (← q r"2 = SUC 1") (fun th => REWRITE_TAC [th]) THENL
     [REWRITE_TAC [NUMERAL, BIT0, BIT1, ← DENUMERAL ADD_CLAUSES],
      REWRITE_TAC [← DENUMERAL NOT_SUC, NOT_SUC, EQ_MULT_LCANCEL] THEN
      REWRITE_TAC [← ONCE_REWRITE_RULE [DISJ_SYM] LE_LT] THEN
      MAP_EVERY X_GEN_TAC [← q r"m:num", ← q r"n:num"] THEN
      SUBGOAL_THEN (← q r"~(SUC 1 * m = SUC (SUC 1 * n))")
        (fun th => REWRITE_TAC [th]) THEN
      DISCH_THEN (MP_TAC o AP_TERM (← q r"EVEN")) THEN
      REWRITE_TAC [EVEN_MULT, EVEN_ADD, NUMERAL, BIT1, EVEN]])

  let ARITH_LT ← prove
   r"(!m n. NUMERAL m < NUMERAL n <=> m < n) /\
   ((_0 < _0) <=> F) /\
   (!n. (BIT0 n < _0) <=> F) /\
   (!n. (BIT1 n < _0) <=> F) /\
   (!n. (_0 < BIT0 n) <=> _0 < n) /\
   (!n. (_0 < BIT1 n) <=> T) /\
   (!m n. (BIT0 m < BIT0 n) <=> m < n) /\
   (!m n. (BIT0 m < BIT1 n) <=> m <= n) /\
   (!m n. (BIT1 m < BIT0 n) <=> m < n) /\
   (!m n. (BIT1 m < BIT1 n) <=> m < n)"
   (REWRITE_TAC [NUMERAL, ← GSYM NOT_LE, ARITH_LE] THEN
    REWRITE_TAC [← DENUMERAL LE])

  let ARITH_GE ← REWRITE_RULE [← GSYM GE, ← GSYM GT] ARITH_LE

  let ARITH_GT ← REWRITE_RULE [← GSYM GE, ← GSYM GT] ARITH_LT

  let ARITH_EQ ← prove
   r"(!m n. (NUMERAL m = NUMERAL n) <=> (m = n)) /\
   ((_0 = _0) <=> T) /\
   (!n. (BIT0 n = _0) <=> (n = _0)) /\
   (!n. (BIT1 n = _0) <=> F) /\
   (!n. (_0 = BIT0 n) <=> (_0 = n)) /\
   (!n. (_0 = BIT1 n) <=> F) /\
   (!m n. (BIT0 m = BIT0 n) <=> (m = n)) /\
   (!m n. (BIT0 m = BIT1 n) <=> F) /\
   (!m n. (BIT1 m = BIT0 n) <=> F) /\
   (!m n. (BIT1 m = BIT1 n) <=> (m = n))"
   (REWRITE_TAC [NUMERAL, ← GSYM LE_ANTISYM, ARITH_LE] THEN
    REWRITE_TAC [LET_ANTISYM, LTE_ANTISYM, ← DENUMERAL LE_0])

  let ARITH_SUB ← prove
   r"(!m n. NUMERAL m - NUMERAL n = NUMERAL(m - n)) /\
   (_0 - _0 = _0) /\
   (!n. _0 - BIT0 n = _0) /\
   (!n. _0 - BIT1 n = _0) /\
   (!n. BIT0 n - _0 = BIT0 n) /\
   (!n. BIT1 n - _0 = BIT1 n) /\
   (!m n. BIT0 m - BIT0 n = BIT0 (m - n)) /\
   (!m n. BIT0 m - BIT1 n = PRE(BIT0 (m - n))) /\
   (!m n. BIT1 m - BIT0 n = if n <= m then BIT1 (m - n) else _0) /\
   (!m n. BIT1 m - BIT1 n = BIT0 (m - n))"
   (REWRITE_TAC [NUMERAL, ← DENUMERAL SUB_0] THEN PURE_REWRITE_TAC [BIT0, BIT1] THEN
    REWRITE_TAC [← GSYM MULT_2, SUB_SUC, LEFT_SUB_DISTRIB] THEN
    REWRITE_TAC [SUB] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC [← DENUMERAL SUB_EQ_0] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [NOT_LE]) THEN
    ASM_REWRITE_TAC [LE_SUC_LT, LT_MULT_LCANCEL, ARITH_EQ] THEN
    POP_ASSUM (CHOOSE_THEN SUBST1_TAC o REWRITE_RULE [LE_EXISTS]) THEN
    REWRITE_TAC [ADD1, LEFT_ADD_DISTRIB] THEN
    REWRITE_TAC [ADD_SUB2, ← GSYM ADD_ASSOC])

  let ARITH ← end_itlist CONJ
    [ARITH_ZERO, ARITH_SUC, ARITH_PRE,
     ARITH_ADD, ARITH_MULT, ARITH_EXP,
     ARITH_EVEN, ARITH_ODD,
     ARITH_EQ, ARITH_LE, ARITH_LT, ARITH_GE, ARITH_GT,
     ARITH_SUB]

  let EXP_2_NE_0 ← prove
   r"!n. ~(2 EXP n = 0)"
   (REWRITE_TAC [EXP_EQ_0, ARITH_EQ])

  return {
    ARITH_ZERO, BIT0_0, BIT1_0, ARITH_SUC, ARITH_PRE, ARITH_ADD, ARITH_MULT,
    ARITH_EXP, ARITH_EVEN, ARITH_ODD, ARITH_LE, ARITH_LT, ARITH_GE, ARITH_GT,
    ARITH_EQ, ARITH_SUB, ARITH, EXP_2_NE_0 }

end


section Numerals

open HolCore HolCore.Kernel HolCore.Basics HolCore.Lib HolCore.Bool HolCore.Equal
     HolCore.Drule HolCore.Tactics HolCore.Itab HolCore.Simp HolCore.Parser
     HolCore.Theorems HolCore.IndDefs HolCore.Classic HolCore.Canon

/- ---------------------------------------------------------------------- -/
/- Preamble of the big NUM_*_CONV closure: the shared term constants,     -/
/- variable terms and pure numeral helpers (calc_num.ml lines 221-347).   -/
/- ---------------------------------------------------------------------- -/

/-- The term constants and proforma variables shared by every `calc_num.ml`
    numeral conversion (calc_num.ml lines 221-238).  `num_ty` is the type of
    naturals; the `*_tm` fields are the raw combinators and operators; the
    single-letter `*_tm` fields are the proforma variables `a..p:num`. -/
structure CalcNumConsts where
  num_ty     : hol_type
  NUMERAL_tm : term
  BIT0_tm    : term
  BIT1_tm    : term
  zero_tm    : term
  suc_tm     : term
  one_tm     : term
  add_tm     : term
  mul_tm     : term
  exp_tm     : term
  eq_tm      : term
  /- `dtm`/`mtm` of calc_num.ml line 1378 (`(DIV)`/`(MOD)`).  Recovered from
     `DIVISION` by theorem-destructuring rather than from the quotations, so
     `dest_binop` works whether or not the session has declared `DIV`/`MOD`
     yet.  See `NUM_DIV_CONV`. -/
  div_tm     : term
  mod_tm     : term
  /- `(-)` and `(<=)`, likewise recovered from theorems rather than quotations:
     an undeclared constant parses as a free variable, which would make
     `dest_binop` silently never match. -/
  sub_tm     : term
  le_tm      : term
  a_tm       : term
  b_tm       : term
  c_tm       : term
  d_tm       : term
  e_tm       : term
  h_tm       : term
  l_tm       : term
  m_tm       : term
  n_tm       : term
  p_tm       : term
  deriving Inhabited

/-- Build `CalcNumConsts` from the session theorems (calc_num.ml lines 221-238).
    The `rator`/`rand` extractions yield `NUMERAL`, `BIT0`, `BIT1`, `_0`, `SUC`,
    `(+)`, `(*)`, `EXP`, `(=)`. -/
def setupCalcNumConsts (ZERO_DEF TWO ADD_0 EXP_2 DIVISION SUB_0 LE_0 : thm)
    (mk_small_numeral : Int → Except String term) :
    ExceptT String IO CalcNumConsts := do
  -- `num_ty = type_of(lhand(concl ZERO_DEF))`.
  let num_ty := type_of (← liftExcept (HolCore.Equal.lhand (concl ZERO_DEF)))
  -- `Comb(NUMERAL_tm,Comb(BIT0_tm,Comb(BIT1_tm,zero_tm))) = mk_small_numeral 2`.
  let two_num ← liftExcept (mk_small_numeral 2)
  let (NUMERAL_tm, BIT0_tm, BIT1_tm, zero_tm) ←
    (match two_num with
     | .Comb num (.Comb b0 (.Comb b1 z)) => pure (num, b0, b1, z)
     | _ => throw "setupCalcNumConsts: mk_small_numeral 2 not in expected form")
  -- `suc_tm = rator(rand(concl TWO))`.
  let suc_tm ← liftExcept (rator (← rand (concl TWO)))
  -- `one_tm = rand(mk_small_numeral 1)`.
  let one_tm ← liftExcept (rand (← mk_small_numeral 1))
  -- `add_tm = rator(rator(lhand(snd(strip_forall(concl ADD_0)))))`.
  let add_tm ← liftExcept
    (rator (← rator (← HolCore.Equal.lhand (strip_forall (concl ADD_0)).2)))
  -- `mul_tm = rator(rator(rand(snd(strip_forall(concl EXP_2)))))`.
  let mul_tm ← liftExcept
    (rator (← rator (← rand (strip_forall (concl EXP_2)).2)))
  -- `exp_tm = rator(rator(lhand(snd(strip_forall(concl EXP_2)))))`.
  let exp_tm ← liftExcept
    (rator (← rator (← HolCore.Equal.lhand (strip_forall (concl EXP_2)).2)))
  -- `eq_tm = rator(rator(concl TWO))`.
  let eq_tm ← liftExcept (rator (← rator (concl TWO)))
  -- calc_num.ml line 1378 writes `dtm = `(DIV)`` and `mtm = `(MOD)``.  We instead
  -- recover both from `DIVISION`, whose statement is
  --   `|- !m n. ~(n = 0) ==> m = m DIV n * n + m MOD n /\ m MOD n < n`
  -- following the same idiom as `add_tm`/`mul_tm`/`exp_tm` above.  This yields the
  -- genuine constants at `num->num->num`, so the OCaml's own `dest_binop` applies.
  let (div_tm, mod_tm) ← liftExcept (do
    let (c1, c2) ← Basics.dest_conj (← rand (strip_forall (concl DIVISION)).2)
    -- `lhand(lhand(rand c1))` is `m DIV n`; `lhand c2` is `m MOD n`.
    let div_tm ← rator (← rator
      (← HolCore.Equal.lhand (← HolCore.Equal.lhand (← rand c1))))
    let mod_tm ← rator (← rator (← HolCore.Equal.lhand c2))
    return (div_tm, mod_tm))
  -- `sub_tm` from `SUB_0 = |- !m. 0 - m = 0 /\ m - 0 = m`: `lhand` of the first
  -- conjunct is `0 - m`.  `le_tm` from `LE_0 = |- !n. 0 <= n` directly.
  let sub_tm ← liftExcept (do
    let (c1, _) ← Basics.dest_conj (strip_forall (concl SUB_0)).2
    rator (← rator (← HolCore.Equal.lhand c1)))
  let le_tm ← liftExcept (rator (← rator (strip_forall (concl LE_0)).2))
  -- The proforma variables `a..p:num`.
  let a_tm := mk_var "a" num_ty
  let b_tm := mk_var "b" num_ty
  let c_tm := mk_var "c" num_ty
  let d_tm := mk_var "d" num_ty
  let e_tm := mk_var "e" num_ty
  let h_tm := mk_var "h" num_ty
  let l_tm := mk_var "l" num_ty
  let m_tm := mk_var "m" num_ty
  let n_tm := mk_var "n" num_ty
  let p_tm := mk_var "p" num_ty
  return {
    num_ty, NUMERAL_tm, BIT0_tm, BIT1_tm, zero_tm, suc_tm, one_tm,
    add_tm, mul_tm, exp_tm, eq_tm, div_tm, mod_tm, sub_tm, le_tm,
    a_tm, b_tm, c_tm, d_tm, e_tm, h_tm, l_tm, m_tm, n_tm, p_tm }

/-- `STANDARDIZE` (calc_num.ml lines 239-253): replace every atom of a theorem's
    conclusion by the canonical term constant of the same name/appearance, then
    re-establish the theorem by `EQ_MP (REFL tm') th`.  This shares the physical
    term nodes so later structural `==` comparisons succeed.  Rendered as an
    explicit application (OCaml's `fun th -> ...`) since `o` is reserved. -/
def STANDARDIZE (K : CalcNumConsts) (th : thm) : Except String thm := do
  let ilist : List (term × term) :=
    [(K.BIT0_tm, K.BIT0_tm), (K.BIT1_tm, K.BIT1_tm), (K.zero_tm, K.zero_tm),
     (K.suc_tm, K.suc_tm), (K.add_tm, K.add_tm), (K.mul_tm, K.mul_tm),
     (K.exp_tm, K.exp_tm), (K.eq_tm, K.eq_tm), (K.NUMERAL_tm, K.NUMERAL_tm),
     (K.a_tm, K.a_tm), (K.b_tm, K.b_tm), (K.c_tm, K.c_tm), (K.d_tm, K.d_tm),
     (K.e_tm, K.e_tm), (K.h_tm, K.h_tm), (K.l_tm, K.l_tm), (K.m_tm, K.m_tm),
     (K.n_tm, K.n_tm), (K.p_tm, K.p_tm)]
  let rec replace (tm : term) : Except String term :=
    match tm with
    | .Var _ _ => .ok (rev_assocd tm ilist tm)
    | .Const _ _ => .ok (rev_assocd tm ilist tm)
    | .Comb s t => do mk_comb (← replace s) (← replace t)
    | .Abs _ _ => failwith "replace"
  let tm' ← replace (concl th)
  EQ_MP (REFL tm') th

/-- `dest_raw_numeral` (calc_num.ml lines 259-263): the value of a raw
    `BIT0`/`BIT1`/`_0` numeral, as a rational (matching OCaml's `num`). -/
partial def dest_raw_numeral : term → Except String Rat
  | .Comb (.Const "BIT1" _) t => do return 2 * (← dest_raw_numeral t) + 1
  | .Comb (.Const "BIT0" _) t => do return 2 * (← dest_raw_numeral t)
  | .Const "_0" _ => .ok 0
  | _ => failwith "dest_raw_numeral"

/-- `bitcounts` (calc_num.ml lines 264-271): the number of `BIT1`s (`w`) and
    `BIT0`s (`z`) in a raw numeral. -/
partial def bitcounts (tm : term) : Except String (Nat × Nat) :=
  let rec bctr (w z : Nat) (tm : term) : Except String (Nat × Nat) :=
    match tm with
    | .Const "_0" _ => .ok (w, z)
    | .Comb (.Const "BIT0" _) t => bctr w (z + 1) t
    | .Comb (.Const "BIT1" _) t => bctr (w + 1) z t
    | _ => failwith "malformed numeral"
  bctr 0 0 tm

/-- `wellformed` (calc_num.ml lines 272-276): is `tm` a well-formed raw
    numeral? -/
partial def wellformed : term → Bool
  | .Const "_0" _ => true
  | .Comb (.Const "BIT0" _) t => wellformed t
  | .Comb (.Const "BIT1" _) t => wellformed t
  | _ => false

/-- `orderrelation` (calc_num.ml lines 277-292): three-way comparison of two raw
    numerals returning `-1`/`0`/`1`; fails on malformed input. -/
partial def orderrelation (mtm ntm : term) : Except String Int :=
  if mtm == ntm then
    if wellformed mtm then .ok 0 else failwith "orderrelation"
  else
    match mtm, ntm with
    | .Const "_0" _, .Const "_0" _ => .ok 0
    | .Const "_0" _, _ =>
        if wellformed ntm then .ok (-1) else failwith "orderrelation"
    | _, .Const "_0" _ =>
        if wellformed ntm then .ok 1 else failwith "orderrelation"
    | .Comb (.Const "BIT0" _) mt, .Comb (.Const "BIT0" _) nt =>
        orderrelation mt nt
    | .Comb (.Const "BIT1" _) mt, .Comb (.Const "BIT1" _) nt =>
        orderrelation mt nt
    | .Comb (.Const "BIT0" _) mt, .Comb (.Const "BIT1" _) nt => do
        if (← orderrelation mt nt) > 0 then .ok 1 else .ok (-1)
    | .Comb (.Const "BIT1" _) mt, .Comb (.Const "BIT0" _) nt => do
        if (← orderrelation mt nt) < 0 then .ok (-1) else .ok 1
    | _, _ => failwith "orderrelation"

/-- `doublebn` (calc_num.ml line 293): double a raw numeral, keeping `_0`
    normalized. -/
def doublebn (K : CalcNumConsts) (tm : term) : Except String term :=
  if tm == K.zero_tm then .ok tm else mk_comb K.BIT0_tm tm

mutual
/-- `subbn`/`sbcbn` (calc_num.ml lines 294-320): subtraction and
    subtract-with-borrow on raw numerals, assuming the order relation holds. -/
partial def subbn (K : CalcNumConsts) (mtm ntm : term) : Except String term := do
  match mtm, ntm with
  | _, .Const "_0" _ => .ok mtm
  | .Comb (.Const "BIT0" _) mt, .Comb (.Const "BIT0" _) nt =>
      doublebn K (← subbn K mt nt)
  | .Comb (.Const "BIT1" _) mt, .Comb (.Const "BIT1" _) nt =>
      doublebn K (← subbn K mt nt)
  | .Comb (.Const "BIT1" _) mt, .Comb (.Const "BIT0" _) nt =>
      mk_comb K.BIT1_tm (← subbn K mt nt)
  | .Comb (.Const "BIT0" _) mt, .Comb (.Const "BIT1" _) nt =>
      mk_comb K.BIT1_tm (← sbcbn K mt nt)
  | _, _ => failwith "malformed numeral or wrong relation"
partial def sbcbn (K : CalcNumConsts) (mtm ntm : term) : Except String term := do
  match mtm, ntm with
  | .Comb (.Const "BIT0" _) mt, .Const "_0" _ =>
      mk_comb K.BIT1_tm (← sbcbn K mt ntm)
  | .Comb (.Const "BIT1" _) mt, .Const "_0" _ =>
      doublebn K mt
  | .Comb (.Const "BIT0" _) mt, .Comb (.Const "BIT0" _) nt =>
      mk_comb K.BIT1_tm (← sbcbn K mt nt)
  | .Comb (.Const "BIT1" _) mt, .Comb (.Const "BIT1" _) nt =>
      mk_comb K.BIT1_tm (← sbcbn K mt nt)
  | .Comb (.Const "BIT1" _) mt, .Comb (.Const "BIT0" _) nt =>
      doublebn K (← subbn K mt nt)
  | .Comb (.Const "BIT0" _) mt, .Comb (.Const "BIT1" _) nt =>
      doublebn K (← sbcbn K mt nt)
  | _, _ => failwith "malformed numeral or wrong relation"
end

/-- `topsplit` (calc_num.ml lines 321-347): peel the low 4 bits off a raw
    numeral, returning `(low, rest)` where `low` is a small integer 0-15 and
    `rest` is either `_0` (the numeral fit in <= 4 bits) or the remaining raw
    numeral above the 4 (or fewer) low bits. -/
def topsplit (K : CalcNumConsts) (tm : term) : Except String (Int × term) :=
  match tm with
  | .Const "_0" _ => .ok (0, K.zero_tm)
  | .Comb (.Const "BIT1" _) (.Const "_0" _) => .ok (1, K.zero_tm)
  | .Comb (.Const "BIT0" _) (.Comb (.Const "BIT1" _) (.Const "_0" _)) =>
      .ok (2, K.zero_tm)
  | .Comb (.Const "BIT1" _) (.Comb (.Const "BIT1" _) (.Const "_0" _)) =>
      .ok (3, K.zero_tm)
  | .Comb (.Const "BIT0" _) (.Comb (.Const "BIT0" _)
      (.Comb (.Const "BIT1" _) (.Const "_0" _))) => .ok (4, K.zero_tm)
  | .Comb (.Const "BIT1" _) (.Comb (.Const "BIT0" _)
      (.Comb (.Const "BIT1" _) (.Const "_0" _))) => .ok (5, K.zero_tm)
  | .Comb (.Const "BIT0" _) (.Comb (.Const "BIT1" _)
      (.Comb (.Const "BIT1" _) (.Const "_0" _))) => .ok (6, K.zero_tm)
  | .Comb (.Const "BIT1" _) (.Comb (.Const "BIT1" _)
      (.Comb (.Const "BIT1" _) (.Const "_0" _))) => .ok (7, K.zero_tm)
  | .Comb (.Const "BIT0" _) (.Comb (.Const "BIT0" _)
      (.Comb (.Const "BIT0" _) (.Comb (.Const "BIT0" _) n))) => .ok (0, n)
  | .Comb (.Const "BIT1" _) (.Comb (.Const "BIT0" _)
      (.Comb (.Const "BIT0" _) (.Comb (.Const "BIT0" _) n))) => .ok (1, n)
  | .Comb (.Const "BIT0" _) (.Comb (.Const "BIT1" _)
      (.Comb (.Const "BIT0" _) (.Comb (.Const "BIT0" _) n))) => .ok (2, n)
  | .Comb (.Const "BIT1" _) (.Comb (.Const "BIT1" _)
      (.Comb (.Const "BIT0" _) (.Comb (.Const "BIT0" _) n))) => .ok (3, n)
  | .Comb (.Const "BIT0" _) (.Comb (.Const "BIT0" _)
      (.Comb (.Const "BIT1" _) (.Comb (.Const "BIT0" _) n))) => .ok (4, n)
  | .Comb (.Const "BIT1" _) (.Comb (.Const "BIT0" _)
      (.Comb (.Const "BIT1" _) (.Comb (.Const "BIT0" _) n))) => .ok (5, n)
  | .Comb (.Const "BIT0" _) (.Comb (.Const "BIT1" _)
      (.Comb (.Const "BIT1" _) (.Comb (.Const "BIT0" _) n))) => .ok (6, n)
  | .Comb (.Const "BIT1" _) (.Comb (.Const "BIT1" _)
      (.Comb (.Const "BIT1" _) (.Comb (.Const "BIT0" _) n))) => .ok (7, n)
  | .Comb (.Const "BIT0" _) (.Comb (.Const "BIT0" _)
      (.Comb (.Const "BIT0" _) (.Comb (.Const "BIT1" _) n))) => .ok (8, n)
  | .Comb (.Const "BIT1" _) (.Comb (.Const "BIT0" _)
      (.Comb (.Const "BIT0" _) (.Comb (.Const "BIT1" _) n))) => .ok (9, n)
  | .Comb (.Const "BIT0" _) (.Comb (.Const "BIT1" _)
      (.Comb (.Const "BIT0" _) (.Comb (.Const "BIT1" _) n))) => .ok (10, n)
  | .Comb (.Const "BIT1" _) (.Comb (.Const "BIT1" _)
      (.Comb (.Const "BIT0" _) (.Comb (.Const "BIT1" _) n))) => .ok (11, n)
  | .Comb (.Const "BIT0" _) (.Comb (.Const "BIT0" _)
      (.Comb (.Const "BIT1" _) (.Comb (.Const "BIT1" _) n))) => .ok (12, n)
  | .Comb (.Const "BIT1" _) (.Comb (.Const "BIT0" _)
      (.Comb (.Const "BIT1" _) (.Comb (.Const "BIT1" _) n))) => .ok (13, n)
  | .Comb (.Const "BIT0" _) (.Comb (.Const "BIT1" _)
      (.Comb (.Const "BIT1" _) (.Comb (.Const "BIT1" _) n))) => .ok (14, n)
  | .Comb (.Const "BIT1" _) (.Comb (.Const "BIT1" _)
      (.Comb (.Const "BIT1" _) (.Comb (.Const "BIT1" _) n))) => .ok (15, n)
  | _ => failwith "malformed numeral"

/- ---------------------------------------------------------------------- -/
/- Proformas for the delicate numeral conversions (calc_num.ml 348-603).  -/
/- ---------------------------------------------------------------------- -/

/-- `mk_compnumeral k base` (calc_num.ml 350-354): build the raw numeral for the
    small integer `k` with `base` at the top.  `partial` because the recursion
    is on `k / 2`. -/
partial def mkCompNumeral (K : CalcNumConsts) (k : Int) (base : term) :
    Except String term :=
  if k == 0 then .ok base else do
    let t ← mkCompNumeral K (k / 2) base
    if k % 2 == 1 then mk_comb K.BIT1_tm t else mk_comb K.BIT0_tm t

/-- Every `pth_*` theorem and theorem-array proved in calc_num.ml lines
    348-603, together with the flag arrays computed alongside the add/adc
    clause arrays.

    Field meanings:
    * `BITS_INJ`, `ARITH_0`: `NUM_ADD_RULE`/`NUM_ADC_RULE` helper lemmas.
    * `REFL_bit0`, `REFL_bit1`: standardized `REFL` of `BIT0`/`BIT1`.
    * `add_clauses`/`add_flags`, `adc_clauses`/`adc_flags`: the 32*32 dispatch
      tables for `NUM_ADD_RULE`/`NUM_ADC_RULE`.
    * `shift_pth_0`..`shift_pth_triv`, `shift_pths_1`, `shift_pths_0`:
      `NUM_SHIFT_CONV`'s proformas. -/
structure CalcNumProformas where
  BITS_INJ      : thm
  ARITH_0       : thm
  REFL_bit0     : thm
  REFL_bit1     : thm
  add_clauses   : Array thm
  add_flags     : Array Int
  adc_clauses   : Array thm
  adc_flags     : Array Int
  shift_pth_0   : thm
  shift_pth_z   : thm
  shift_pth_1   : thm
  shift_pth_base : thm
  shift_pth_triv : thm
  shift_pths_1  : Array thm
  shift_pths_0  : Array thm
  -- NUM_UNSHIFT_CONV proformas (calc_num.ml 605-693).
  unshift_pth_triv : thm
  unshift_pth_base : thm
  unshift_pth_0    : thm
  unshift_pth_1    : thm
  unshift_pth_z    : thm
  unshift_puths_1  : Array thm
  unshift_puths_2  : Array thm
  -- NUM_SQUARE_RULE proformas (calc_num.ml 695-830).
  sq_pth_0     : thm
  sq_pth_1     : thm
  sq_pth_even  : thm
  sq_pth_odd   : thm
  sq_pth_qstep : thm
  sq_pth_rec   : thm
  sq_pth_toom3 : thm
  sq_pth_even3 : thm
  -- NUM_MUL_RULE proformas (calc_num.ml 921-970).
  mul_pth_0l    : thm
  mul_pth_0r    : thm
  mul_pth_1l    : thm
  mul_pth_1r    : thm
  mul_pth_evenl : thm
  mul_pth_evenr : thm
  mul_pth_oddl  : thm
  mul_pth_oddr  : thm
  mul_pth_oo1   : thm
  mul_pth_oo2   : thm
  mul_pth_recodel : thm
  mul_pth_recoder : thm
  -- NUM_MULT_CONV' proforma (calc_num.ml 1124).
  mulc_pth_refl : thm
  -- NUM_SUC_CONV proforma (calc_num.ml 1137).
  suc_pth : thm
  -- NUM_ADD_CONV proforma (calc_num.ml 1149).
  add_topthm : thm
  -- NUM_MULT_CONV proformas (calc_num.ml 1166-1168).
  mult_topthm   : thm
  mult_pth_refl : thm
  -- NUM_EXP_CONV proformas (calc_num.ml 1185-1206).
  exp_pth0 : thm
  exp_pth1 : thm
  exp_pth  : thm
  exp_tth  : thm
  exp_fth  : thm
  -- NUM_LT_CONV proformas (calc_num.ml 1234-1245).
  lt_pth : thm
  lt_qth : thm
  lt_rth : thm
  -- NUM_LE_CONV proformas (calc_num.ml 1265-1276).
  le_pth : thm
  le_qth : thm
  le_rth : thm
  -- NUM_EQ_CONV proformas (calc_num.ml 1296-1307).
  eq_pth : thm
  eq_qth : thm
  eq_rth : thm
  -- NUM_PRE_CONV proformas (calc_num.ml 1323-1341).
  pre_tth : thm
  pre_pth : thm
  -- NUM_SUB_CONV proformas (calc_num.ml 1343-1370).
  sub_pth0 : thm
  sub_pth1 : thm
  -- NUM_DIV_CONV / NUM_MOD_CONV proformas (calc_num.ml 1372-1397).
  divmod_pth  : thm
  divmod_pth0 : thm
  -- NUM_FACT_CONV proformas (calc_num.ml 1398-1425).
  fact_pth_0   : thm
  fact_pth_suc : thm
  -- EXPAND_CASES_CONV proformas (calc_num.ml 1508-1526).
  expand_pth_base : thm
  expand_pth_step : thm
  -- EXP_MOD_CONV proformas (calc_num.ml 1527-1560).
  expmod_pth_0    : thm
  expmod_pth_even : thm
  expmod_pth_odd  : thm
  deriving Inhabited

/-- `AP_BIT0 th = MK_COMB(REFL_bit0,th)` (calc_num.ml line 256). -/
def AP_BIT0 (P : CalcNumProformas) (th : thm) : Except String thm :=
  Kernel.MK_COMB P.REFL_bit0 th

/-- `AP_BIT1 th = MK_COMB(REFL_bit1,th)` (calc_num.ml line 257). -/
def AP_BIT1 (P : CalcNumProformas) (th : thm) : Except String thm :=
  Kernel.MK_COMB P.REFL_bit1 th

/-- `QUICK_PROVE_HYP ath bth = EQ_MP (DEDUCT_ANTISYM_RULE ath bth) ath`
    (calc_num.ml line 258). -/
def QUICK_PROVE_HYP (ath bth : thm) : Except String thm :=
  EQ_MP (Kernel.DEDUCT_ANTISYM_RULE ath bth) ath

end Numerals

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv conv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolLight HolLight.Syntax

/-- The delicate-conversion proformas of calc_num.ml, in file order:
    NUM_ADD_RULE (348-425), NUM_SHIFT_CONV (426-603), NUM_UNSHIFT_CONV
    (605-693), NUM_SQUARE_RULE (695-830), NUM_MUL_RULE (921-970) and the
    exported conversions (1124-1560).  Where one tactic contains several
    rules that print (MESON), they are bound last one first, as OCaml
    evaluates the tactic expression right to left. -/
@[nospecialize]
def setupCalcNumProformas [HolBase] (K : CalcNumConsts) (A : ArithRewrites)
    (NUMERAL BIT0 BIT1 ADD_CLAUSES MULT_CLAUSES SUC_INJ EQ_MULT_LCANCEL MULT_2
     MULT_ASSOC LEFT_ADD_DISTRIB ADD_EQ_0 MULT_EQ_0 : thm)
    (RIGHT_ADD_DISTRIB EXP_2 MULT_AC ADD_AC EQ_ADD_LCANCEL EQ_ADD_RCANCEL
     ADD_SYM ADD1 ADD_ASSOC NOT_SUC MULT_SYM EXP EXP_ADD
     LT_EXISTS LE_ADD NOT_LT NOT_LE LE_ANTISYM LT_REFL LE_REFL : thm)
    (PRE SUB_EQ_0 ADD_SUB DIVMOD_UNIQ DIV_ZERO MOD_ZERO FACT LT : thm)
    (MESON_TAC : List thm → tactic)
    (MOD_DOWN_CONV : ioconv)
    (NUM_CANCEL_CONV : ioconv)
    (mk_small_numeral : Int → Except String term) :
    ExceptT String IO CalcNumProformas := do
  let { IMP_CONJ, .. } := HolBase.T
  let { DE_MORGAN_THM, .. } := HolBase.C
  let STANDARDIZE (th : thm) : ExceptT String IO thm := liftExcept (HolMath.CalcNum.STANDARDIZE K th)
  let MESON (ths : List thm) (s : String) : ExceptT String IO thm := prove s (MESON_TAC ths)

  let REFL_bit0 ← STANDARDIZE (REFL K.BIT0_tm)
  let REFL_bit1 ← STANDARDIZE (REFL K.BIT1_tm)

  /- NUM_ADD_RULE, NUM_ADC_RULE (calc_num.ml 348-425). -/

  let bases (v : term) : ExceptT String IO (List term) := do
    let part2 ← liftExcept ((upto 8 15).mapM (fun k => mkCompNumeral K k v))
    let sub ← ExceptT.mk (subst [(← liftExcept (mk_comb K.BIT0_tm v), ← liftExcept (mk_comb K.BIT1_tm v))])
    let part1 ← part2.mapM (fun t => ExceptT.mk (sub t))
    let part0 ← liftExcept ((upto 0 15).mapM (fun k => mkCompNumeral K k K.zero_tm))
    return part0 ++ part1 ++ part2
  let starts ← liftExcept ((allpairs (fun mtm ntm => do
      mk_comb (← mk_comb K.add_tm mtm) ntm) (← bases K.m_tm) (← bases K.n_tm)).mapM id)
  let BITS_INJ ← STANDARDIZE (← prove
   r"(BIT0 m = BIT0 n <=> m = n) /\
     (BIT1 m = BIT1 n <=> m = n)"
   (REWRITE_TAC [BIT0, BIT1] THEN
    REWRITE_TAC [← GSYM MULT_2] THEN
    REWRITE_TAC [SUC_INJ, EQ_MULT_LCANCEL, A.ARITH_EQ]))
  let ARITH_0 ← STANDARDIZE (← MESON [NUMERAL, ADD_CLAUSES]
    r"m + _0 = m /\ _0 + n = n")
  let patadj ← ExceptT.mk (subst [(← q r"SUC(m + _0)", ← q r"SUC m"),
                                  (← q r"SUC(_0 + n)", ← q r"SUC n")])
  let mkclauses (sucflag : Bool) (t : term) : ExceptT String IO (thm × Int) := do
    let tm ← liftExcept (if sucflag then mk_comb K.suc_tm t else .ok t)
    let th1 ← ExceptT.mk (PURE_REWRITE_CONV [A.ARITH_ADD, A.ARITH_SUC, ARITH_0] tm)
    let tm1 ← ExceptT.mk (patadj (← liftExcept (rand (concl th1))))
    if !(free_in K.add_tm tm1) then
      return (th1, if free_in K.m_tm tm1 then 0 else 1)
    let ptm ← liftExcept (do rand (← rand (← rand (← rand tm1))))
    let sub ← ExceptT.mk (subst [(K.p_tm, ptm)])
    let tmc := safe_mk_eq (safe_mk_eq ptm K.p_tm) (safe_mk_eq tm (← ExceptT.mk (sub tm1)))
    return (← EQT_ELIM (← ExceptT.mk (REWRITE_CONV [A.ARITH_ADD, A.ARITH_SUC, ARITH_0, BITS_INJ] tmc)),
            if free_in K.suc_tm tm1 then 3 else 2)
  let (add_clauses, add_flags) ← do
    let (l1, l2) := (← starts.mapM (mkclauses false)).unzip
    pure ((← l1.mapM STANDARDIZE).toArray, l2.toArray)
  let (adc_clauses, adc_flags) ← do
    let (l1, l2) := (← starts.mapM (mkclauses true)).unzip
    pure ((← l1.mapM STANDARDIZE).toArray, l2.toArray)

  /- NUM_SHIFT_CONV (calc_num.ml 426-603). -/

  let shift_pth_0 ← STANDARDIZE (← prove
   r"(n = a + p * b <=> BIT0 n = BIT0 a + BIT0 p * b)"
   (REWRITE_TAC [BIT0, BIT1] THEN
    REWRITE_TAC [← GSYM MULT_2, ← GSYM MULT_ASSOC, ← GSYM LEFT_ADD_DISTRIB] THEN
    REWRITE_TAC [EQ_MULT_LCANCEL, A.ARITH_EQ]))
  let shift_pth_z ← STANDARDIZE (← prove
   r"n = _0 + p * b <=> BIT0 n = _0 + BIT0 p * b"
   (SUBST1_TAC (← SYM (← SPEC (← q r"_0") NUMERAL)) THEN
    REWRITE_TAC [BIT1, BIT0] THEN
    REWRITE_TAC [ADD_CLAUSES, ← GSYM MULT_2] THEN
    REWRITE_TAC [← GSYM MULT_ASSOC, EQ_MULT_LCANCEL, A.ARITH_EQ]))
  let shift_pth_1 ← STANDARDIZE (← prove
   r"(n = a + p * b <=> BIT1 n = BIT1 a + BIT0 p * b)"
   (REWRITE_TAC [BIT0, BIT1] THEN
    REWRITE_TAC [← GSYM MULT_2, ← GSYM MULT_ASSOC, ← GSYM LEFT_ADD_DISTRIB,
                 ADD_CLAUSES, SUC_INJ] THEN
    REWRITE_TAC [EQ_MULT_LCANCEL, A.ARITH_EQ]))
  let shift_pth_base ← STANDARDIZE (← prove
   r"n = _0 + BIT1 _0 * n"
   (MESON_TAC [ADD_CLAUSES, MULT_CLAUSES, NUMERAL]))
  let shift_pth_triv ← STANDARDIZE (← prove
   r"_0 = a + p * b <=> _0 = a + BIT0 p * b"
   (CONV_TAC (BINOP_CONV SYM_CONV) THEN
    SUBST1_TAC (← SYM (← SPEC (← q r"_0") NUMERAL)) THEN
    REWRITE_TAC [ADD_EQ_0, MULT_EQ_0, BIT0]))
  let shift_pths_1 := (CONJUNCTS (← STANDARDIZE (← prove
   r"(n = a + p * b <=>
        BIT0(BIT0(BIT0(BIT0 n))) =
        BIT0(BIT0(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = a + p * b <=>
        BIT1(BIT0(BIT0(BIT0 n))) =
        BIT1(BIT0(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = a + p * b <=>
        BIT0(BIT1(BIT0(BIT0 n))) =
        BIT0(BIT1(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = a + p * b <=>
        BIT1(BIT1(BIT0(BIT0 n))) =
        BIT1(BIT1(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = a + p * b <=>
        BIT0(BIT0(BIT1(BIT0 n))) =
        BIT0(BIT0(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = a + p * b <=>
        BIT1(BIT0(BIT1(BIT0 n))) =
        BIT1(BIT0(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = a + p * b <=>
        BIT0(BIT1(BIT1(BIT0 n))) =
        BIT0(BIT1(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = a + p * b <=>
        BIT1(BIT1(BIT1(BIT0 n))) =
        BIT1(BIT1(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = a + p * b <=>
        BIT0(BIT0(BIT0(BIT1 n))) =
        BIT0(BIT0(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = a + p * b <=>
        BIT1(BIT0(BIT0(BIT1 n))) =
        BIT1(BIT0(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = a + p * b <=>
        BIT0(BIT1(BIT0(BIT1 n))) =
        BIT0(BIT1(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = a + p * b <=>
        BIT1(BIT1(BIT0(BIT1 n))) =
        BIT1(BIT1(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = a + p * b <=>
        BIT0(BIT0(BIT1(BIT1 n))) =
        BIT0(BIT0(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = a + p * b <=>
        BIT1(BIT0(BIT1(BIT1 n))) =
        BIT1(BIT0(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = a + p * b <=>
        BIT0(BIT1(BIT1(BIT1 n))) =
        BIT0(BIT1(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = a + p * b <=>
        BIT1(BIT1(BIT1(BIT1 n))) =
        BIT1(BIT1(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b)"
   (MP_TAC (← REWRITE_RULE [← GSYM MULT_2] BIT0) THEN
    MP_TAC (← REWRITE_RULE [← GSYM MULT_2] BIT1) THEN
    ABBREV_TAC (← q r"two = 2") THEN
    DISCH_THEN (fun th => REWRITE_TAC [th]) THEN
    DISCH_THEN (fun th => REWRITE_TAC [th]) THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [ADD_CLAUSES, SUC_INJ, EQ_MULT_LCANCEL, A.ARITH_EQ,
                 ← GSYM LEFT_ADD_DISTRIB, ← GSYM MULT_ASSOC])))).toArray
  let shift_pths_0 := (CONJUNCTS (← STANDARDIZE (← prove
   r"(n = _0 + p * b <=>
        BIT0(BIT0(BIT0(BIT0 n))) =
        _0 + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = _0 + p * b <=>
        BIT1(BIT0(BIT0(BIT0 n))) =
        BIT1 _0 + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = _0 + p * b <=>
        BIT0(BIT1(BIT0(BIT0 n))) =
        BIT0(BIT1 _0) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = _0 + p * b <=>
        BIT1(BIT1(BIT0(BIT0 n))) =
        BIT1(BIT1 _0) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = _0 + p * b <=>
        BIT0(BIT0(BIT1(BIT0 n))) =
        BIT0(BIT0(BIT1 _0)) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = _0 + p * b <=>
        BIT1(BIT0(BIT1(BIT0 n))) =
        BIT1(BIT0(BIT1 _0)) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = _0 + p * b <=>
        BIT0(BIT1(BIT1(BIT0 n))) =
        BIT0(BIT1(BIT1 _0)) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = _0 + p * b <=>
        BIT1(BIT1(BIT1(BIT0 n))) =
        BIT1(BIT1(BIT1 _0)) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = _0 + p * b <=>
        BIT0(BIT0(BIT0(BIT1 n))) =
        BIT0(BIT0(BIT0(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = _0 + p * b <=>
        BIT1(BIT0(BIT0(BIT1 n))) =
        BIT1(BIT0(BIT0(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = _0 + p * b <=>
        BIT0(BIT1(BIT0(BIT1 n))) =
        BIT0(BIT1(BIT0(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = _0 + p * b <=>
        BIT1(BIT1(BIT0(BIT1 n))) =
        BIT1(BIT1(BIT0(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = _0 + p * b <=>
        BIT0(BIT0(BIT1(BIT1 n))) =
        BIT0(BIT0(BIT1(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = _0 + p * b <=>
        BIT1(BIT0(BIT1(BIT1 n))) =
        BIT1(BIT0(BIT1(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = _0 + p * b <=>
        BIT0(BIT1(BIT1(BIT1 n))) =
        BIT0(BIT1(BIT1(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
       (n = _0 + p * b <=>
        BIT1(BIT1(BIT1(BIT1 n))) =
        BIT1(BIT1(BIT1(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b)"
   (SUBST1_TAC (← MESON [NUMERAL] r"_0 = 0") THEN
    MP_TAC (← REWRITE_RULE [← GSYM MULT_2] BIT0) THEN
    MP_TAC (← REWRITE_RULE [← GSYM MULT_2] BIT1) THEN
    ABBREV_TAC (← q r"two = 2") THEN
    DISCH_THEN (fun th => REWRITE_TAC [th]) THEN
    DISCH_THEN (fun th => REWRITE_TAC [th]) THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [ADD_CLAUSES, SUC_INJ, EQ_MULT_LCANCEL, A.ARITH_EQ,
                 ← GSYM LEFT_ADD_DISTRIB, ← GSYM MULT_ASSOC])))).toArray

  /- NUM_UNSHIFT_CONV (calc_num.ml 605-693). -/

  let unshift_pth_triv ← STANDARDIZE (← prove
   r"a + p * _0 = a"
   (SUBST1_TAC (← SYM (← SPEC (← q r"_0") NUMERAL)) THEN
    REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES]))
  let unshift_pth_base ← STANDARDIZE (← prove
   r"a + BIT1 _0 * b = a + b"
   (SUBST1_TAC (← SYM (← SPEC (← q r"BIT1 _0") NUMERAL)) THEN
    REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES]))
  let unshift_pth_0 ← STANDARDIZE (← prove
   r"BIT0 a + BIT0 p * b = BIT0(a + p * b)"
   (REWRITE_TAC [BIT0] THEN REWRITE_TAC [← GSYM MULT_2] THEN
    REWRITE_TAC [← GSYM MULT_ASSOC, ← GSYM LEFT_ADD_DISTRIB]))
  let unshift_pth_1 ← STANDARDIZE (← prove
   r"BIT1 a + BIT0 p * b = BIT1(a + p * b)"
   (REWRITE_TAC [BIT0, BIT1] THEN REWRITE_TAC [← GSYM MULT_2] THEN
    REWRITE_TAC [ADD_CLAUSES, SUC_INJ] THEN
    REWRITE_TAC [← GSYM MULT_ASSOC, ← GSYM LEFT_ADD_DISTRIB] THEN
    REWRITE_TAC [EQ_MULT_LCANCEL, A.ARITH_EQ]))
  let unshift_pth_z ← STANDARDIZE (← prove
   r"_0 + BIT0 p * b = BIT0(_0 + p * b)"
   (SUBST1_TAC (← SYM (← SPEC (← q r"_0") NUMERAL)) THEN
    REWRITE_TAC [BIT1, BIT0] THEN REWRITE_TAC [ADD_CLAUSES] THEN
    REWRITE_TAC [RIGHT_ADD_DISTRIB]))
  let unshift_puths_1 := (CONJUNCTS (← STANDARDIZE (← prove
   r"(a + p * b = n <=>
          BIT0(BIT0(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT0(BIT0(BIT0(BIT0 n)))) /\
         (a + p * b = n <=>
          BIT1(BIT0(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT1(BIT0(BIT0(BIT0 n)))) /\
         (a + p * b = n <=>
          BIT0(BIT1(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT0(BIT1(BIT0(BIT0 n)))) /\
         (a + p * b = n <=>
          BIT1(BIT1(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT1(BIT1(BIT0(BIT0 n)))) /\
         (a + p * b = n <=>
          BIT0(BIT0(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT0(BIT0(BIT1(BIT0 n)))) /\
         (a + p * b = n <=>
          BIT1(BIT0(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT1(BIT0(BIT1(BIT0 n)))) /\
         (a + p * b = n <=>
          BIT0(BIT1(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT0(BIT1(BIT1(BIT0 n)))) /\
         (a + p * b = n <=>
          BIT1(BIT1(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT1(BIT1(BIT1(BIT0 n)))) /\
         (a + p * b = n <=>
          BIT0(BIT0(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT0(BIT0(BIT0(BIT1 n)))) /\
         (a + p * b = n <=>
          BIT1(BIT0(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT1(BIT0(BIT0(BIT1 n)))) /\
         (a + p * b = n <=>
          BIT0(BIT1(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT0(BIT1(BIT0(BIT1 n)))) /\
         (a + p * b = n <=>
          BIT1(BIT1(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT1(BIT1(BIT0(BIT1 n)))) /\
         (a + p * b = n <=>
          BIT0(BIT0(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT0(BIT0(BIT1(BIT1 n)))) /\
         (a + p * b = n <=>
          BIT1(BIT0(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT1(BIT0(BIT1(BIT1 n)))) /\
         (a + p * b = n <=>
          BIT0(BIT1(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT0(BIT1(BIT1(BIT1 n)))) /\
         (a + p * b = n <=>
          BIT1(BIT1(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
          BIT1(BIT1(BIT1(BIT1 n))))"
   (SUBST1_TAC (← MESON [NUMERAL] r"_0 = 0") THEN
    MP_TAC (← REWRITE_RULE [← GSYM MULT_2] BIT0) THEN
    MP_TAC (← REWRITE_RULE [← GSYM MULT_2] BIT1) THEN
    ABBREV_TAC (← q r"two = 2") THEN
    DISCH_THEN (fun th => REWRITE_TAC [th]) THEN
    DISCH_THEN (fun th => REWRITE_TAC [th]) THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [ADD_CLAUSES, SUC_INJ, EQ_MULT_LCANCEL, A.ARITH_EQ,
                 ← GSYM LEFT_ADD_DISTRIB, ← GSYM MULT_ASSOC])))).toArray
  let unshift_puths_2 := (← (upto 0 255).mapM (fun i => do
    let th1 := unshift_puths_1[(i % 16).toNat]!
    let th2 := unshift_puths_1[(i / 16).toNat]!
    let th3 ← GEN_REWRITE_RULE RAND_CONV [th1] th2
    STANDARDIZE th3)).toArray

  /- NUM_SQUARE_RULE (calc_num.ml 695-830). -/

  let sq_pth_0 ← STANDARDIZE (← prove
   r"_0 EXP 2 = _0"
   (MESON_TAC [NUMERAL, ← ExceptT.mk (REWRITE_CONV [A.ARITH] (← q r"0 EXP 2"))]))
  let sq_pth_1 ← STANDARDIZE (← prove
   r"(BIT1 _0) EXP 2 = BIT1 _0"
   (MESON_TAC [NUMERAL, ← ExceptT.mk (REWRITE_CONV [A.ARITH] (← q r"1 EXP 2"))]))
  let sq_pth_even ← STANDARDIZE (← prove
   r"m EXP 2 = n <=> (BIT0 m) EXP 2 = BIT0(BIT0 n)"
   (ABBREV_TAC (← q r"two = 2") THEN
    REWRITE_TAC [BIT0] THEN EXPAND_TAC "two" THEN
    REWRITE_TAC [← GSYM MULT_2] THEN REWRITE_TAC [EXP_2] THEN
    REWRITE_TAC [← AC MULT_AC (← q r"(2 * m) * (2 * n) = 2 * 2 * m * n")] THEN
    REWRITE_TAC [EQ_MULT_LCANCEL, A.ARITH_EQ]))
  let sq_pth_odd ← STANDARDIZE (← prove
   r"m EXP 2 = n <=> (BIT1 m) EXP 2 = BIT1(BIT0(m + n))"
   (ABBREV_TAC (← q r"two = 2") THEN
    REWRITE_TAC [NUMERAL, BIT0, BIT1] THEN
    EXPAND_TAC "two" THEN REWRITE_TAC [← GSYM MULT_2] THEN
    REWRITE_TAC [EXP_2, MULT_CLAUSES, ADD_CLAUSES] THEN
    REWRITE_TAC [SUC_INJ, ← GSYM MULT_ASSOC, ← GSYM LEFT_ADD_DISTRIB] THEN
    REWRITE_TAC [← AC ADD_AC (← q r"(m + m * 2 * m) + m = m * 2 * m + m + m")] THEN
    REWRITE_TAC [← GSYM MULT_2, ← AC MULT_AC (← q r"m * 2 * m = 2 * m * m")] THEN
    REWRITE_TAC [← GSYM MULT_ASSOC, ← GSYM LEFT_ADD_DISTRIB] THEN
    REWRITE_TAC [EQ_MULT_LCANCEL, A.ARITH_EQ] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [ADD_SYM] THEN
    REWRITE_TAC [EQ_ADD_RCANCEL]))
  let sq_pth_qstep ← do
    let cancel ← MESON [EQ_ADD_LCANCEL] r"!m:num. m + n = m + p ==> n = p"
    let zero ← MESON [NUMERAL] r"_0 = 0"
    UNDISCH (← STANDARDIZE (← prove
     r"n + BIT1 _0 = m /\
       m EXP 2 = p /\
       m + a = BIT0(BIT0 p)
       ==> (BIT1(BIT1(BIT1 n))) EXP 2 = BIT1(BIT0(BIT0(BIT0 a)))"
     (ABBREV_TAC (← q r"two = 2") THEN
      SUBST1_TAC zero THEN
      REWRITE_TAC [BIT1, BIT0] THEN EXPAND_TAC "two" THEN
      REWRITE_TAC [← GSYM MULT_2] THEN
      REWRITE_TAC [ADD1, LEFT_ADD_DISTRIB, ← GSYM ADD_ASSOC] THEN
      REWRITE_TAC [MULT_ASSOC] THEN REWRITE_TAC [A.ARITH] THEN
      REWRITE_TAC [IMP_CONJ] THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN DISCH_TAC THEN
      MATCH_MP_TAC cancel THEN
      EXISTS_TAC (← q r"16 * (n + 1)") THEN
      ASM_REWRITE_TAC [ADD_ASSOC, ← GSYM LEFT_ADD_DISTRIB] THEN
      EXPAND_TAC "two" THEN REWRITE_TAC [EXP_2] THEN
      REWRITE_TAC [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB] THEN
      REWRITE_TAC [MULT_CLAUSES, MULT_ASSOC] THEN
      REWRITE_TAC [← AC MULT_AC (← q r"(8 * n) * NUMERAL p = (8 * NUMERAL p) * n")] THEN
      REWRITE_TAC [A.ARITH] THEN
      REWRITE_TAC [← AC ADD_AC
         (← q r"(n + 16) + p + q + 49 = (n + p + q) + (16 + 49)")] THEN
      REWRITE_TAC [← GSYM ADD_ASSOC] THEN REWRITE_TAC [A.ARITH] THEN
      REWRITE_TAC [ADD_ASSOC, EQ_ADD_RCANCEL] THEN
      REWRITE_TAC [← GSYM ADD_ASSOC, ← GSYM MULT_2, MULT_ASSOC] THEN
      ONCE_REWRITE_TAC [← AC ADD_AC (← q r"a + b + c:num = b + a + c")] THEN
      REWRITE_TAC [← GSYM RIGHT_ADD_DISTRIB] THEN
      REWRITE_TAC [A.ARITH])))
  let sq_pth_rec ← UNDISCH (← STANDARDIZE (← prove
   r"n = l + p * h /\
       h + l = m /\
       h EXP 2 = a /\
       l EXP 2 = c /\
       m EXP 2 = d /\
       a + c = e /\
       e + b = d
       ==> n EXP 2 = c + p * (b + p * a)"
   (REWRITE_TAC [IMP_CONJ] THEN
    DISCH_THEN SUBST1_TAC THEN
    REPLICATE_TAC 5 (DISCH_THEN (SUBST1_TAC o SYM)) THEN
    REWRITE_TAC [EXP_2, LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB] THEN
    REWRITE_TAC [MULT_AC] THEN CONV_TAC (BINOP_CONV NUM_CANCEL_CONV) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [RIGHT_ADD_DISTRIB] THEN
    REWRITE_TAC [MULT_AC] THEN REWRITE_TAC [ADD_AC])))
  let sq_pth_toom3 ← do
    let sucSyms (n : Int) : ExceptT String IO (List thm) :=
      (upto 1 n).mapM (fun k => do
        SYM (← ExceptT.mk (REWRITE_CONV [A.ARITH_SUC]
          (← liftExcept (mk_comb K.suc_tm (← liftExcept (mk_small_numeral (k - 1))))))))
    let lem2 ← MESON []
     r"b = b' /\ c = c' /\ d = d'
        ==> b + d':num = b' + d /\ 4 * b + d' = 4 * b' + d"
    let lem1 ← MESON []
     r"b = b' /\ c = c' /\ d = d'
        ==> 5 * b + c' + d' = 5 * b' + c + d"
    let zero ← MESON [NUMERAL] r"_0 = 0"
    STANDARDIZE (← prove
     r"h EXP 2 = e /\
       l EXP 2 = a /\
       (l + BIT1 _0 * (m + BIT1 _0 * h)) EXP 2 =
       a +  BIT1 _0 * (b +  BIT1 _0 * (c +  BIT1 _0 * (d +  BIT1 _0 * e))) /\
       (l + BIT0(BIT1 _0) * (m + BIT0(BIT1 _0) * h)) EXP 2 =
       a + BIT0(BIT1 _0) * (b + BIT0(BIT1 _0) *
       (c + BIT0(BIT1 _0) * (d + BIT0(BIT1 _0) * e))) /\
       (h + BIT0(BIT1 _0) * (m + BIT0(BIT1 _0) * l)) EXP 2 =
       e + BIT0(BIT1 _0) * (d + BIT0(BIT1 _0) *
       (c + BIT0(BIT1 _0) * (b + BIT0(BIT1 _0) * a)))
       ==> (l + p * (m + p * h)) EXP 2 =
           a + p * (b + p * (c + p * (d + p * e)))"
     (ABBREV_TAC (← q r"two = 2") THEN
      SUBST1_TAC zero THEN
      REWRITE_TAC [BIT1, BIT0] THEN
      EXPAND_TAC "two" THEN REWRITE_TAC [← GSYM MULT_2] THEN
      REWRITE_TAC [A.ARITH] THEN
      SUBGOAL_THEN
       (← q r"!p x y z. (x + p * (y + p * z)) EXP 2 =
                  x * x + p * (2 * x * y + p * ((2 * x * z + y * y) +
                            p * (2 * y * z + p * z * z)))")
       (fun th => REWRITE_TAC [th])
      THENL
       [REWRITE_TAC [EXP_2, MULT_2, LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB] THEN
        REWRITE_TAC [MULT_AC] THEN REWRITE_TAC [ADD_AC],
        REWRITE_TAC [EXP_2]] THEN
      MAP_EVERY ABBREV_TAC
       [← q r"a':num = l * l", ← q r"b' = 2 * l * m", ← q r"c' = 2 * l * h + m * m",
        ← q r"d' = 2 * m * h", ← q r"e':num = h * h"] THEN
      SUBST1_TAC (← AC MULT_AC (← q r"2 * m * l = 2 * l * m")) THEN
      SUBST1_TAC (← AC MULT_AC (← q r"2 * h * l = 2 * l * h")) THEN
      SUBST1_TAC (← AC MULT_AC (← q r"2 * h * m = 2 * m * h")) THEN
      ASM_REWRITE_TAC [] THEN EXPAND_TAC "two" THEN
      POP_ASSUM_LIST (fun _ => ALL_TAC) THEN
      ASM_CASES_TAC (← q r"a':num = a") THEN ASM_REWRITE_TAC [] THEN
      ASM_CASES_TAC (← q r"e':num = e") THEN ASM_REWRITE_TAC [] THEN
      POP_ASSUM_LIST (fun _ => ALL_TAC) THEN
      REWRITE_TAC [EQ_ADD_LCANCEL, EQ_MULT_LCANCEL] THEN
      REWRITE_TAC [LEFT_ADD_DISTRIB, MULT_ASSOC] THEN
      REWRITE_TAC [A.ARITH] THEN
      REWRITE_TAC [MULT_CLAUSES, EQ_ADD_LCANCEL] THEN
      REWRITE_TAC [ADD_ASSOC, EQ_ADD_RCANCEL] THEN
      REWRITE_TAC [← GSYM ADD_ASSOC] THEN DISCH_TAC THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP lem1) THEN
      REWRITE_TAC [LEFT_ADD_DISTRIB, MULT_ASSOC] THEN
      REWRITE_TAC (← sucSyms 5) THEN
      REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES] THEN
      CONV_TAC (LAND_CONV NUM_CANCEL_CONV) THEN DISCH_THEN SUBST_ALL_TAC THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP lem2) THEN
      REWRITE_TAC [LEFT_ADD_DISTRIB, MULT_ASSOC] THEN
      REWRITE_TAC (← sucSyms 4) THEN
      REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES] THEN
      CONV_TAC (LAND_CONV (BINOP_CONV NUM_CANCEL_CONV)) THEN
      REWRITE_TAC [← GSYM MULT_2] THEN ONCE_REWRITE_TAC [ADD_SYM] THEN
      REWRITE_TAC [← GSYM (← el 4 (CONJUNCTS MULT_CLAUSES))] THEN
      SIMP_TAC [EQ_MULT_LCANCEL, NOT_SUC]))
  let sq_pth_even3 ← STANDARDIZE (← prove
   r"m EXP 2 = n <=>
       (BIT0(BIT0(BIT0 m))) EXP 2 = BIT0(BIT0(BIT0(BIT0(BIT0(BIT0 n)))))"
   (ABBREV_TAC (← q r"two = 2") THEN
    REWRITE_TAC [BIT0] THEN REWRITE_TAC [← GSYM MULT_2] THEN
    EXPAND_TAC "two" THEN REWRITE_TAC [EXP_2] THEN
    REWRITE_TAC [← AC MULT_AC
     (← q r"(2 * 2 * 2 * m) * 2 * 2 * 2 * m = 2 * 2 * 2 * 2 * 2 * 2 * m * m")] THEN
    REWRITE_TAC [EQ_MULT_LCANCEL, A.ARITH_EQ]))

  /- NUM_MUL_RULE (calc_num.ml 921-970). -/

  let (mul_pth_0l, mul_pth_0r) ← CONJ_PAIR (← STANDARDIZE (← prove
   r"_0 * n = _0 /\ m * _0 = _0"
   (MESON_TAC [NUMERAL, MULT_CLAUSES])))
  let (mul_pth_1l, mul_pth_1r) ← CONJ_PAIR (← STANDARDIZE (← prove
   r"(BIT1 _0) * n = n /\ m * (BIT1 _0) = m"
   (MESON_TAC [NUMERAL, MULT_CLAUSES])))
  let (mul_pth_evenl, mul_pth_evenr) ← CONJ_PAIR (← STANDARDIZE (← prove
   r"(m * n = p <=> (BIT0 m) * n = BIT0 p) /\
       (m * n = p <=> m * BIT0 n = BIT0 p)"
   (REWRITE_TAC [BIT0] THEN REWRITE_TAC [← GSYM MULT_2] THEN
    REWRITE_TAC [← AC MULT_AC (← q r"m * 2 * n = 2 * m * n")] THEN
    REWRITE_TAC [← GSYM MULT_ASSOC, EQ_MULT_LCANCEL, A.ARITH_EQ])))
  let (mul_pth_oddl, mul_pth_oddr) ← CONJ_PAIR (← STANDARDIZE (← prove
   r"(m * n = p <=> BIT1 m * n = BIT0 p + n) /\
       (m * n = p <=> m * BIT1 n = BIT0 p + m)"
   (REWRITE_TAC [BIT0, BIT1] THEN REWRITE_TAC [← GSYM MULT_2] THEN
    REWRITE_TAC [MULT_CLAUSES] THEN
    REWRITE_TAC [← MESON [MULT_AC, ADD_SYM] r"m + m * 2 * n = 2 * m * n + m"] THEN
    REWRITE_TAC [← GSYM MULT_ASSOC, EQ_MULT_LCANCEL, EQ_ADD_RCANCEL] THEN
    REWRITE_TAC [A.ARITH_EQ])))
  let mul_pth_oo1 ← UNDISCH_ALL (← STANDARDIZE (← prove
   r"n + p = m /\ SUC(m + n) = a /\ p EXP 2 = b /\ a EXP 2 = c /\ b + d = c
        ==> ((BIT1 m) * (BIT1 n) = d)"
   (ABBREV_TAC (← q r"two = 2") THEN REWRITE_TAC [BIT1, IMP_CONJ] THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [EXP_2, ← GSYM MULT_2] THEN
    REPLICATE_TAC 4 (DISCH_THEN (SUBST1_TAC o SYM)) THEN
    REWRITE_TAC [ADD1, ← AC ADD_AC (← q r"((n + p) + n) + 1 = (p + (n + n)) + 1")] THEN
    REWRITE_TAC [← GSYM MULT_2] THEN
    REWRITE_TAC [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB] THEN
    REWRITE_TAC [← GSYM ADD_ASSOC, MULT_CLAUSES, EQ_ADD_LCANCEL] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [MULT_2, LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB] THEN
    REWRITE_TAC [MULT_AC] THEN REWRITE_TAC [ADD_AC])))
  let mul_pth_oo2 ← PURE_ONCE_REWRITE_RULE [MULT_SYM]
    (← INST [(K.n_tm, K.m_tm), (K.m_tm, K.n_tm)] mul_pth_oo1)
  let mul_pth_recodel ← UNDISCH_ALL (← STANDARDIZE (← prove
   r"SUC(_0 + m) = p ==> (p * n = a + n <=> m * n = a)"
   (SUBST1_TAC (← MESON [NUMERAL] r"_0 = 0") THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [ADD_CLAUSES, MULT_CLAUSES, EQ_ADD_RCANCEL])))
  let mul_pth_recoder ← UNDISCH_ALL (← STANDARDIZE (← prove
   r"SUC(_0 + n) = p ==> (m * p = a + m <=> m * n = a)"
   (ONCE_REWRITE_TAC [MULT_SYM] THEN
    SUBST1_TAC (← MESON [NUMERAL] r"_0 = 0") THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [ADD_CLAUSES, MULT_CLAUSES, EQ_ADD_RCANCEL])))

  /- NUM_MULT_CONV' (calc_num.ml 1124). -/

  let mulc_pth_refl ← STANDARDIZE (← MESON [EXP_2] r"m EXP 2 = p <=> m * m = p")

  /- The exported conversions (calc_num.ml 1128-1307). -/

  let suc_pth ← STANDARDIZE (← prove
   r"SUC(_0 + m) = n <=> SUC(NUMERAL m) = NUMERAL n"
   (BINOP_TAC THEN MESON_TAC [NUMERAL, ADD_CLAUSES]))
  let add_topthm ← STANDARDIZE (← prove
   r"m + n = p <=> NUMERAL m + NUMERAL n = NUMERAL p"
   (MESON_TAC [NUMERAL]))
  let mult_topthm ← STANDARDIZE (← prove
   r"m * n = p <=> NUMERAL m * NUMERAL n = NUMERAL p"
   (MESON_TAC [NUMERAL]))
  let mult_pth_refl ← STANDARDIZE (← prove
   r"m EXP 2 = p <=> NUMERAL m * NUMERAL m = NUMERAL p"
   (MESON_TAC [NUMERAL, EXP_2]))
  let exp_pth0 ← STANDARDIZE (← prove
   r"(m EXP n = p) ==> (p * p = a) ==> (m EXP (BIT0 n) = a)"
   (REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN
    REWRITE_TAC [BIT0, EXP_ADD]))
  let exp_pth1 ← STANDARDIZE (← prove
   r"(m EXP n = p) ==> (p * p = b) ==> (m * b = a) ==> (m EXP (BIT1 n) = a)"
   (REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN
    REWRITE_TAC [BIT1, EXP_ADD, EXP]))
  let exp_pth ← STANDARDIZE (← prove
   r"m EXP _0 = BIT1 _0"
   (MP_TAC (← CONJUNCT1 EXP) THEN REWRITE_TAC [NUMERAL, BIT1] THEN
    DISCH_THEN MATCH_ACCEPT_TAC))
  let exp_tth ← STANDARDIZE (← prove
   r"(NUMERAL m) EXP (NUMERAL n) = m EXP n"
   (REWRITE_TAC [NUMERAL]))
  let exp_fth ← STANDARDIZE (← prove
   r"m = NUMERAL m"
   (REWRITE_TAC [NUMERAL]))
  let lt_pth ← UNDISCH (← STANDARDIZE (← prove
   r"SUC(m + n) = p ==> ((NUMERAL n < NUMERAL p) <=> T)"
   (REWRITE_TAC [NUMERAL, LT_EXISTS, ADD_CLAUSES] THEN
    MESON_TAC [ADD_SYM])))
  let lt_qth ← UNDISCH (← STANDARDIZE (← prove
   r"m + p = n ==> (NUMERAL n < NUMERAL p <=> F)"
   (DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [NOT_LT, NUMERAL] THEN
    MESON_TAC [LE_ADD, ADD_SYM])))
  let lt_rth ← STANDARDIZE (← prove
   r"NUMERAL n < NUMERAL n <=> F"
   (MESON_TAC [LT_REFL]))
  let le_pth ← UNDISCH (← STANDARDIZE (← prove
   r"m + n = p ==> ((NUMERAL n <= NUMERAL p) <=> T)"
   (DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [NUMERAL] THEN
    MESON_TAC [LE_ADD, ADD_SYM])))
  let le_qth ← UNDISCH (← STANDARDIZE (← prove
   r"SUC(m + p) = n ==> (NUMERAL n <= NUMERAL p <=> F)"
   (DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [NUMERAL, NOT_LE, ADD_CLAUSES, LT_EXISTS] THEN
    MESON_TAC [ADD_SYM])))
  let le_rth ← STANDARDIZE (← prove
   r"NUMERAL n <= NUMERAL n <=> T"
   (REWRITE_TAC [LE_REFL]))
  let eq_pth ← UNDISCH (← STANDARDIZE (← prove
   r"SUC(m + n) = p ==> ((NUMERAL n = NUMERAL p) <=> F)"
   (DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [NUMERAL, ← GSYM LE_ANTISYM, DE_MORGAN_THM] THEN
    REWRITE_TAC [NOT_LE, LT_EXISTS, ADD_CLAUSES] THEN
    MESON_TAC [ADD_SYM])))
  let eq_qth ← UNDISCH (← STANDARDIZE (← prove
   r"SUC(m + p) = n ==> ((NUMERAL n = NUMERAL p) <=> F)"
   (DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [NUMERAL, ← GSYM LE_ANTISYM, DE_MORGAN_THM] THEN
    REWRITE_TAC [NOT_LE, LT_EXISTS, ADD_CLAUSES] THEN
    MESON_TAC [ADD_SYM])))
  let eq_rth ← STANDARDIZE (← prove
   r"(NUMERAL n = NUMERAL n) <=> T"
   (REWRITE_TAC []))

  /- NUM_PRE_CONV (calc_num.ml 1323-1341). -/

  let pre_tth ← prove
   r"PRE 0 = 0"
   (REWRITE_TAC [PRE])
  let pre_pth ← prove
   r"(SUC m = n) ==> (PRE n = m)"
   (DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [PRE])
  -- The conversions' own quotations (`m`, `n`, `SUC`, ... below) are parsed
  -- here, where calc_num.ml parses them; the Lean code uses the equal terms
  -- of `CalcNumConsts`.
  let quotes (l : List String) : ExceptT String IO Unit := do
    for s in l do let _ ← q s
  quotes [r"m:num", r"n:num", r"SUC"]

  /- NUM_SUB_CONV (calc_num.ml 1343-1370). -/

  let sub_pth0 ← prove
   r"p <= n ==> (p - n = 0)"
   (REWRITE_TAC [SUB_EQ_0])
  let sub_pth1 ← prove
   r"(m + n = p) ==> (p - n = m)"
   (DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [ADD_SUB])
  quotes [r"m:num", r"n:num", r"p:num", r"(-)", r"(+)", r"(<=)"]

  /- NUM_DIV_CONV, NUM_MOD_CONV (calc_num.ml 1372-1397). -/

  let divmod_pth ← prove
   r"q * n + r = m ==> r < n ==> m DIV n = q /\ m MOD n = r"
   (MESON_TAC [DIVMOD_UNIQ])
  let divmod_pth0 ← prove
   r"!m. m DIV 0 = 0 /\ m MOD 0 = m"
   (REWRITE_TAC [DIV_ZERO, MOD_ZERO])
  quotes [r"m:num", r"n:num", r"q:num", r"r:num", r"(DIV)", r"(MOD)"]

  /- NUM_FACT_CONV (calc_num.ml 1398-1425). -/

  quotes [r"SUC", r"(*)"]
  let fact_pth_0 ← prove
   r"FACT 0 = 1"
   (REWRITE_TAC [FACT])
  let fact_pth_suc ← prove
   r"(SUC x = y) ==> (FACT x = w) ==> (y * w = z) ==> (FACT y = z)"
   (REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN
    REWRITE_TAC [FACT])
  quotes [r"w:num", r"x:num", r"y:num", r"z:num"]

  -- num_CONV's `SUC_tm = `SUC`` (calc_num.ml 1500).
  quotes [r"SUC"]

  /- EXPAND_CASES_CONV (calc_num.ml 1508-1526). -/

  let expand_pth_base ← prove
   r"(!n. n < 0 ==> P n) <=> T"
   (REWRITE_TAC [LT])
  let expand_pth_step ← prove
   r"(!n. n < SUC k ==> P n) <=> (!n. n < k ==> P n) /\ P k"
   (REWRITE_TAC [LT] THEN MESON_TAC [])

  /- EXP_MOD_CONV (calc_num.ml 1527-1560). -/

  let (expmod_pth_0, expmod_pth_even, expmod_pth_odd) ← do
    match CONJUNCTS (← prove
     r"(a EXP 0) MOD n = 1 MOD n /\
         (a EXP (NUMERAL(BIT0 k))) MOD n =
         ((a EXP (NUMERAL k) MOD n) EXP 2) MOD n /\
         (a EXP (NUMERAL(BIT1 k))) MOD n =
         (a * ((a EXP (NUMERAL k) MOD n) EXP 2) MOD n) MOD n"
     (REWRITE_TAC [EXP, EXP_2] THEN REWRITE_TAC [BIT0, BIT1, NUMERAL] THEN
      REWRITE_TAC [EXP, EXP_ADD] THEN CONV_TAC MOD_DOWN_CONV THEN
      REWRITE_TAC [])) with
    | [p0, peven, podd] => pure (p0, peven, podd)
    | _ => throw "EXP_MOD_CONV: expected 3 conjuncts"

  return {
    BITS_INJ, ARITH_0, REFL_bit0, REFL_bit1,
    add_clauses, add_flags, adc_clauses, adc_flags,
    shift_pth_0, shift_pth_z, shift_pth_1, shift_pth_base, shift_pth_triv,
    shift_pths_1, shift_pths_0,
    unshift_pth_triv, unshift_pth_base, unshift_pth_0, unshift_pth_1,
    unshift_pth_z, unshift_puths_1, unshift_puths_2,
    sq_pth_0, sq_pth_1, sq_pth_even, sq_pth_odd, sq_pth_qstep, sq_pth_rec,
    sq_pth_toom3, sq_pth_even3,
    mul_pth_0l, mul_pth_0r, mul_pth_1l, mul_pth_1r, mul_pth_evenl, mul_pth_evenr,
    mul_pth_oddl, mul_pth_oddr, mul_pth_oo1, mul_pth_oo2, mul_pth_recodel,
    mul_pth_recoder,
    mulc_pth_refl, suc_pth, add_topthm, mult_topthm, mult_pth_refl,
    exp_pth0, exp_pth1, exp_pth, exp_tth, exp_fth,
    lt_pth, lt_qth, lt_rth, le_pth, le_qth, le_rth, eq_pth, eq_qth, eq_rth,
    pre_tth, pre_pth, sub_pth0, sub_pth1, divmod_pth, divmod_pth0,
    fact_pth_0, fact_pth_suc, expand_pth_base, expand_pth_step,
    expmod_pth_0, expmod_pth_even, expmod_pth_odd }

end

section Numerals

open HolCore HolCore.Kernel HolCore.Basics HolCore.Lib HolCore.Bool HolCore.Equal
     HolCore.Drule HolCore.Tactics HolCore.Itab HolCore.Simp HolCore.Parser
     HolCore.Theorems HolCore.IndDefs HolCore.Classic HolCore.Canon

/- ---------------------------------------------------------------------- -/
/- NUM_ADD_RULE / NUM_ADC_RULE (calc_num.ml lines 375-424).               -/
/- ---------------------------------------------------------------------- -/

/-- Shared dispatch of `NUM_ADD_RULE`/`NUM_ADC_RULE` at a leaf clause with flag
    `fl`.  `recAdd`/`recAdc` are the two mutually-recursive rules threaded in. -/
private def numAddDispatch (K : CalcNumConsts)
    (recAdd recAdc : term → term → IO (Except String thm))
    (m_hi n_hi : term) (th1 : thm) (fl : Int) : IO (Except String thm) := do
  match fl with
  | 0 => (pure (Kernel.INST [(m_hi, K.m_tm)] th1) : IO (Except String thm))
  | 1 => (pure (Kernel.INST [(n_hi, K.n_tm)] th1) : IO (Except String thm))
  | 2 =>
    match ← recAdd m_hi n_hi with
    | .error e => return .error e
    | .ok th2 =>
      match concl th2 with
      | .Comb _ ptm =>
        match Kernel.INST [(m_hi, K.m_tm), (n_hi, K.n_tm), (ptm, K.p_tm)] th1 with
        | .error e => return .error e
        | .ok th3 => (pure (EQ_MP th3 th2) : IO (Except String thm))
      | _ => return .error "NUM_ADD_RULE: unexpected conclusion"
  | _ =>
    match ← recAdc m_hi n_hi with
    | .error e => return .error e
    | .ok th2 =>
      match concl th2 with
      | .Comb _ ptm =>
        match Kernel.INST [(m_hi, K.m_tm), (n_hi, K.n_tm), (ptm, K.p_tm)] th1 with
        | .error e => return .error e
        | .ok th3 => (pure (EQ_MP th3 th2) : IO (Except String thm))
      | _ => return .error "NUM_ADC_RULE: unexpected conclusion"

mutual
/-- `NUM_ADD_RULE`/`NUM_ADC_RULE` (calc_num.ml 375-424): add two raw numerals,
    with (`adc`) or without (`add`) a carry-in, dispatching through the 32*32
    clause/flag arrays.  Rendered as one mutually-recursive pair. -/
partial def NUM_ADD_RULE (K : CalcNumConsts) (P : CalcNumProformas)
    (mtm ntm : term) : IO (Except String thm) := do
  match (do
      let (m_lo, m_hi) ← topsplit K mtm
      let (n_lo, n_hi) ← topsplit K ntm
      let m_ind := if m_hi == K.zero_tm then m_lo else m_lo + 16
      let n_ind := if n_hi == K.zero_tm then n_lo else n_lo + 16
      let ind := 32 * m_ind + n_ind
      pure (m_hi, n_hi, ind) : Except String (term × term × Int)) with
  | .error e => return .error e
  | .ok (m_hi, n_hi, ind) =>
    let th1 := P.add_clauses[ind.toNat]!
    let fl := P.add_flags[ind.toNat]!
    numAddDispatch K (NUM_ADD_RULE K P) (NUM_ADC_RULE K P) m_hi n_hi th1 fl
partial def NUM_ADC_RULE (K : CalcNumConsts) (P : CalcNumProformas)
    (mtm ntm : term) : IO (Except String thm) := do
  match (do
      let (m_lo, m_hi) ← topsplit K mtm
      let (n_lo, n_hi) ← topsplit K ntm
      let m_ind := if m_hi == K.zero_tm then m_lo else m_lo + 16
      let n_ind := if n_hi == K.zero_tm then n_lo else n_lo + 16
      let ind := 32 * m_ind + n_ind
      pure (m_hi, n_hi, ind) : Except String (term × term × Int)) with
  | .error e => return .error e
  | .ok (m_hi, n_hi, ind) =>
    let th1 := P.adc_clauses[ind.toNat]!
    let fl := P.adc_flags[ind.toNat]!
    numAddDispatch K (NUM_ADD_RULE K P) (NUM_ADC_RULE K P) m_hi n_hi th1 fl
end

/- ---------------------------------------------------------------------- -/
/- NUM_SHIFT_CONV (calc_num.ml lines 579-603).                            -/
/- ---------------------------------------------------------------------- -/

/-- `NUM_SHIFT_CONV k tm` (calc_num.ml 579-603): rewrite a numeral into the
    form `a + p * b`, shifting `k` low bits into `a`.  `partial` because the
    recursion is on the (numeric) `k` and the numeral structure, not
    structural. -/
partial def NUM_SHIFT_CONV (K : CalcNumConsts) (P : CalcNumProformas)
    (k : Int) (tm : term) : IO (Except String thm) := do
  if k ≤ 0 then
    (pure (Kernel.INST [(tm, K.n_tm)] P.shift_pth_base) : IO (Except String thm))
  else
    match tm with
    | .Comb _ (.Comb _ (.Comb _ (.Comb _ _))) =>
      if k ≥ 4 then
        match (topsplit K tm : Except String (Int × term)) with
        | .error e => return .error e
        | .ok (i, ntm) =>
          match ← NUM_SHIFT_CONV K P (k - 4) ntm with
          | .error e => return .error e
          | .ok th1 =>
            match concl th1 with
            | .Comb _ (.Comb (.Comb _ (.Const "_0" _)) (.Comb (.Comb _ ptm) btm)) =>
              let th2 := P.shift_pths_0[i.toNat]!
              match Kernel.INST [(ntm, K.n_tm), (btm, K.b_tm), (ptm, K.p_tm)] th2 with
              | .error e => return .error e
              | .ok th3 => (pure (EQ_MP th3 th1) : IO (Except String thm))
            | .Comb _ (.Comb (.Comb _ atm) (.Comb (.Comb _ ptm) btm)) =>
              let th2 := P.shift_pths_1[i.toNat]!
              match Kernel.INST [(ntm, K.n_tm), (atm, K.a_tm), (btm, K.b_tm),
                                 (ptm, K.p_tm)] th2 with
              | .error e => return .error e
              | .ok th3 => (pure (EQ_MP th3 th1) : IO (Except String thm))
            | _ => return .error "NUM_SHIFT_CONV: malformed intermediate"
      else
        numShiftBit K P k tm
    | _ => numShiftBit K P k tm
where
  /-- The `BIT0`/`BIT1`/`_0` branches (calc_num.ml 588-602). -/
  numShiftBit (K : CalcNumConsts) (P : CalcNumProformas) (k : Int) (tm : term) :
      IO (Except String thm) := do
    match tm with
    | .Comb (.Const "BIT0" _) ntm =>
      match ← NUM_SHIFT_CONV K P (k - 1) ntm with
      | .error e => return .error e
      | .ok th1 =>
        match concl th1 with
        | .Comb _ (.Comb (.Comb _ (.Const "_0" _)) (.Comb (.Comb _ ptm) btm)) =>
          match Kernel.INST [(ntm, K.n_tm), (btm, K.b_tm), (ptm, K.p_tm)] P.shift_pth_z with
          | .error e => return .error e
          | .ok ith => (pure (EQ_MP ith th1) : IO (Except String thm))
        | .Comb _ (.Comb (.Comb _ atm) (.Comb (.Comb _ ptm) btm)) =>
          match Kernel.INST [(ntm, K.n_tm), (atm, K.a_tm), (btm, K.b_tm),
                             (ptm, K.p_tm)] P.shift_pth_0 with
          | .error e => return .error e
          | .ok ith => (pure (EQ_MP ith th1) : IO (Except String thm))
        | _ => return .error "NUM_SHIFT_CONV: malformed intermediate (BIT0)"
    | .Comb (.Const "BIT1" _) ntm =>
      match ← NUM_SHIFT_CONV K P (k - 1) ntm with
      | .error e => return .error e
      | .ok th1 =>
        match concl th1 with
        | .Comb _ (.Comb (.Comb _ atm) (.Comb (.Comb _ ptm) btm)) =>
          match Kernel.INST [(ntm, K.n_tm), (atm, K.a_tm), (btm, K.b_tm),
                             (ptm, K.p_tm)] P.shift_pth_1 with
          | .error e => return .error e
          | .ok ith => (pure (EQ_MP ith th1) : IO (Except String thm))
        | _ => return .error "NUM_SHIFT_CONV: malformed intermediate (BIT1)"
    | .Const "_0" _ =>
      match ← NUM_SHIFT_CONV K P (k - 1) tm with
      | .error e => return .error e
      | .ok th1 =>
        match concl th1 with
        | .Comb _ (.Comb (.Comb _ atm) (.Comb (.Comb _ ptm) btm)) =>
          match Kernel.INST [(atm, K.a_tm), (btm, K.b_tm), (ptm, K.p_tm)] P.shift_pth_triv with
          | .error e => return .error e
          | .ok ith => (pure (EQ_MP ith th1) : IO (Except String thm))
        | _ => return .error "NUM_SHIFT_CONV: malformed intermediate (_0)"
    | _ => return .error "NUM_SHIFT_CONV: malformed numeral"

/- ---------------------------------------------------------------------- -/
/- NUM_UNSHIFT_CONV (calc_num.ml lines 605-693).                          -/
/- ---------------------------------------------------------------------- -/

mutual
/-- `NUM_UNSHIFT_CONV tm` (calc_num.ml 654-693): the inverse of
    `NUM_SHIFT_CONV` — collapse a term of the form `a + p * b` back into a
    single raw numeral.  Recursive via the `puths_1`/`puths_2` dispatch
    tables. -/
partial def NUM_UNSHIFT_CONV (K : CalcNumConsts) (P : CalcNumProformas)
    (tm : term) : IO (Except String thm) := do
  match tm with
  | .Comb (.Comb (.Const "+" _) atm) (.Comb (.Comb (.Const "*" _) ptm) btm) =>
    match atm, ptm, btm with
    | _, _, .Const "_0" _ =>
        (pure (Kernel.INST [(atm, K.a_tm), (ptm, K.p_tm)] P.unshift_pth_triv)
          : IO (Except String thm))
    | _, .Comb (.Const "BIT1" _) (.Const "_0" _), _ =>
        match Kernel.INST [(atm, K.a_tm), (btm, K.b_tm)] P.unshift_pth_base with
        | .error e => return .error e
        | .ok th1 =>
          match concl th1 with
          | .Comb _ (.Comb (.Comb _ mtm) ntm) =>
            match ← NUM_ADD_RULE K P mtm ntm with
            | .error e => return .error e
            | .ok ath => (pure (TRANS th1 ath) : IO (Except String thm))
          | _ => return .error "NUM_UNSHIFT_CONV: unexpected pth_base concl"
    | .Comb _ (.Comb _ (.Comb _ (.Comb _ atm'))),
      .Comb _ (.Comb _ (.Comb _ (.Comb _ (.Comb pc pd)))), _ =>
      -- ptm is 4 bits deep with a `Comb` residual `ptm' = Comb pc pd`.
      let ptm' := term.Comb pc pd
      match (topsplit K atm : Except String (Int × term)) with
      | .error e => return .error e
      | .ok (i, _) =>
        match atm', ptm' with
        | .Comb _ (.Comb _ (.Comb _ (.Comb _ atm''))),
          .Comb _ (.Comb _ (.Comb _ (.Comb _ (.Comb pc2 pd2)))) =>
          let ptm'' := term.Comb pc2 pd2
          match (topsplit K atm' : Except String (Int × term)) with
          | .error e => return .error e
          | .ok (j, _) =>
            match (do
                let inner ← mk_comb (← mk_comb K.mul_tm ptm'') btm
                mk_comb (← mk_comb K.add_tm atm'') inner
                : Except String term) with
            | .error e => return .error e
            | .ok tm' =>
              match ← NUM_UNSHIFT_CONV K P tm' with
              | .error e => return .error e
              | .ok th1 =>
                match rand (concl th1) with
                | .error e => return .error e
                | .ok ntm =>
                  let th := P.unshift_puths_2[(16 * j + i).toNat]!
                  match Kernel.INST [(atm'', K.a_tm), (ptm'', K.p_tm),
                                     (btm, K.b_tm), (ntm, K.n_tm)] th with
                  | .error e => return .error e
                  | .ok th2 => (pure (EQ_MP th2 th1) : IO (Except String thm))
        | _, _ => unshiftPuths1 K P atm' ptm' btm i
    | _, _, _ => unshiftLeaf K P atm ptm btm
  | _ => return .error "NUM_UNSHIFT_CONV: malformed numeral"

/-- The `puths_1` dispatch of `NUM_UNSHIFT_CONV` (single 4-bit chunk). -/
partial def unshiftPuths1 (K : CalcNumConsts) (P : CalcNumProformas)
    (atm' ptm' btm : term) (i : Int) : IO (Except String thm) := do
  match (do
      let inner ← mk_comb (← mk_comb K.mul_tm ptm') btm
      mk_comb (← mk_comb K.add_tm atm') inner : Except String term) with
  | .error e => return .error e
  | .ok tm' =>
    match ← NUM_UNSHIFT_CONV K P tm' with
    | .error e => return .error e
    | .ok th1 =>
      match rand (concl th1) with
      | .error e => return .error e
      | .ok ntm =>
        let th := P.unshift_puths_1[i.toNat]!
        match Kernel.INST [(atm', K.a_tm), (ptm', K.p_tm),
                           (btm, K.b_tm), (ntm, K.n_tm)] th with
        | .error e => return .error e
        | .ok th2 => (pure (EQ_MP th2 th1) : IO (Except String thm))

/-- The per-bit leaf dispatch of `NUM_UNSHIFT_CONV` (calc_num.ml 685-692). -/
partial def unshiftLeaf (K : CalcNumConsts) (P : CalcNumProformas)
    (atm ptm btm : term) : IO (Except String thm) := do
  let rec2 := Simp.convRuleIO (Simp.randConvIO (Simp.randConvIO (NUM_UNSHIFT_CONV K P)))
  match atm, ptm with
  | .Const "_0" _, .Comb (.Const "BIT0" _) qtm =>
      match Kernel.INST [(btm, K.b_tm), (qtm, K.p_tm)] P.unshift_pth_z with
      | .error e => return .error e
      | .ok th1 => (rec2 th1 : IO (Except String thm))
  | .Comb (.Const "BIT0" _) ctm, .Comb (.Const "BIT0" _) qtm =>
      match Kernel.INST [(ctm, K.a_tm), (btm, K.b_tm), (qtm, K.p_tm)] P.unshift_pth_0 with
      | .error e => return .error e
      | .ok th1 => (rec2 th1 : IO (Except String thm))
  | .Comb (.Const "BIT1" _) ctm, .Comb (.Const "BIT0" _) qtm =>
      match Kernel.INST [(ctm, K.a_tm), (btm, K.b_tm), (qtm, K.p_tm)] P.unshift_pth_1 with
      | .error e => return .error e
      | .ok th1 => (rec2 th1 : IO (Except String thm))
  | _, _ => return .error "NUM_UNSHIFT_CONV: malformed numeral"
end

/-- `NUM_UNSHIFT2_CONV = RAND_CONV(RAND_CONV NUM_UNSHIFT_CONV) THENC NUM_UNSHIFT_CONV`. -/
def NUM_UNSHIFT2_CONV (K : CalcNumConsts) (P : CalcNumProformas) : ioconv :=
  Simp.thencIO (Simp.randConvIO (Simp.randConvIO (NUM_UNSHIFT_CONV K P)))
    (NUM_UNSHIFT_CONV K P)

/-- `NUM_UNSHIFT3_CONV = RAND_CONV(RAND_CONV NUM_UNSHIFT2_CONV) THENC NUM_UNSHIFT_CONV`. -/
def NUM_UNSHIFT3_CONV (K : CalcNumConsts) (P : CalcNumProformas) : ioconv :=
  Simp.thencIO (Simp.randConvIO (Simp.randConvIO (NUM_UNSHIFT2_CONV K P)))
    (NUM_UNSHIFT_CONV K P)

/-- `NUM_UNSHIFT4_CONV = RAND_CONV(RAND_CONV NUM_UNSHIFT3_CONV) THENC NUM_UNSHIFT_CONV`. -/
def NUM_UNSHIFT4_CONV (K : CalcNumConsts) (P : CalcNumProformas) : ioconv :=
  Simp.thencIO (Simp.randConvIO (Simp.randConvIO (NUM_UNSHIFT3_CONV K P)))
    (NUM_UNSHIFT_CONV K P)

/-- `BINOP2_CONV conv1 conv2 = COMB2_CONV (RAND_CONV conv1) conv2` (IO form,
    calc_num.ml 707). -/
def binop2ConvIO (conv1 conv2 : ioconv) : ioconv :=
  Simp.comb2ConvIO (Simp.randConvIO conv1) conv2

/- ---------------------------------------------------------------------- -/
/- Toom-3 multiplication (calc_num.ml lines 707-892).                     -/
/- ---------------------------------------------------------------------- -/

/-- `TOOM3_CONV = BINOP2_CONV (LAND_CONV NUM_UNSHIFT2_CONV) NUM_UNSHIFT4_CONV`. -/
def TOOM3_CONV (K : CalcNumConsts) (P : CalcNumProformas) : ioconv :=
  binop2ConvIO (Simp.landConvIO (NUM_UNSHIFT2_CONV K P)) (NUM_UNSHIFT4_CONV K P)

/-- `NUM_SUC_CONV` (calc_num.ml 1136-1147): the exported successor conversion. -/
def NUM_SUC_CONV (K : CalcNumConsts) (P : CalcNumProformas) (tm : term) :
    IO (Except String thm) := do
  match tm with
  | .Comb (.Const "SUC" _) (.Comb (.Const "NUMERAL" _) mtm) =>
    if wellformed mtm then
      match ← NUM_ADC_RULE K P K.zero_tm mtm with
      | .error e => return .error e
      | .ok th1 =>
        match rand (concl th1) with
        | .error e => return .error e
        | .ok ntm =>
          match Kernel.INST [(mtm, K.m_tm), (ntm, K.n_tm)] P.suc_pth with
          | .error e => return .error e
          | .ok ith => (pure (EQ_MP ith th1) : IO (Except String thm))
    else return .error "NUM_SUC_CONV"
  | _ => return .error "NUM_SUC_CONV"

/-- `NUM_ADD_CONV` (calc_num.ml 1148-1160): the exported addition conversion. -/
def NUM_ADD_CONV (K : CalcNumConsts) (P : CalcNumProformas) (tm : term) :
    IO (Except String thm) := do
  match tm with
  | .Comb (.Comb (.Const "+" _) (.Comb (.Const "NUMERAL" _) mtm))
      (.Comb (.Const "NUMERAL" _) ntm) =>
    if wellformed mtm && wellformed ntm then
      match ← NUM_ADD_RULE K P mtm ntm with
      | .error e => return .error e
      | .ok th1 =>
        match rand (concl th1) with
        | .error e => return .error e
        | .ok ptm =>
          match Kernel.INST [(mtm, K.m_tm), (ntm, K.n_tm), (ptm, K.p_tm)] P.add_topthm with
          | .error e => return .error e
          | .ok th2 => (pure (EQ_MP th2 th1) : IO (Except String thm))
    else return .error "NUM_ADD_CONV"
  | _ => return .error "NUM_ADD_CONV"

/-- `NUM_LT_CONV` (calc_num.ml 1230-1259). -/
def NUM_LT_CONV (K : CalcNumConsts) (P : CalcNumProformas) (tm : term) :
    IO (Except String thm) := do
  match tm with
  | .Comb (.Comb (.Const "<" _) (.Comb (.Const "NUMERAL" _) mtm))
      (.Comb (.Const "NUMERAL" _) ntm) =>
    match (orderrelation mtm ntm : Except String Int) with
    | .error e => return .error e
    | .ok rel =>
      if rel == 0 then
        (pure (Kernel.INST [(ntm, K.n_tm)] P.lt_rth) : IO (Except String thm))
      else if rel < 0 then
        match (sbcbn K ntm mtm : Except String term) with
        | .error e => return .error e
        | .ok dtm =>
          match ← NUM_ADC_RULE K P dtm mtm with
          | .error e => return .error e
          | .ok th =>
            match Kernel.INST [(dtm, K.m_tm), (mtm, K.n_tm), (ntm, K.p_tm)] P.lt_pth with
            | .error e => return .error e
            | .ok ith => (pure (QUICK_PROVE_HYP th ith) : IO (Except String thm))
      else
        match (subbn K mtm ntm : Except String term) with
        | .error e => return .error e
        | .ok dtm =>
          match ← NUM_ADD_RULE K P dtm ntm with
          | .error e => return .error e
          | .ok th =>
            match Kernel.INST [(dtm, K.m_tm), (mtm, K.n_tm), (ntm, K.p_tm)] P.lt_qth with
            | .error e => return .error e
            | .ok ith => (pure (QUICK_PROVE_HYP th ith) : IO (Except String thm))
  | _ => return .error "NUM_LT_CONV"

/-- `NUM_LE_CONV` (calc_num.ml 1260-1289). -/
def NUM_LE_CONV (K : CalcNumConsts) (P : CalcNumProformas) (tm : term) :
    IO (Except String thm) := do
  match tm with
  | .Comb (.Comb (.Const "<=" _) (.Comb (.Const "NUMERAL" _) mtm))
      (.Comb (.Const "NUMERAL" _) ntm) =>
    match (orderrelation mtm ntm : Except String Int) with
    | .error e => return .error e
    | .ok rel =>
      if rel == 0 then
        (pure (Kernel.INST [(ntm, K.n_tm)] P.le_rth) : IO (Except String thm))
      else if rel < 0 then
        match (subbn K ntm mtm : Except String term) with
        | .error e => return .error e
        | .ok dtm =>
          match ← NUM_ADD_RULE K P dtm mtm with
          | .error e => return .error e
          | .ok th =>
            match Kernel.INST [(dtm, K.m_tm), (mtm, K.n_tm), (ntm, K.p_tm)] P.le_pth with
            | .error e => return .error e
            | .ok ith => (pure (QUICK_PROVE_HYP th ith) : IO (Except String thm))
      else
        match (sbcbn K mtm ntm : Except String term) with
        | .error e => return .error e
        | .ok dtm =>
          match ← NUM_ADC_RULE K P dtm ntm with
          | .error e => return .error e
          | .ok th =>
            match Kernel.INST [(dtm, K.m_tm), (mtm, K.n_tm), (ntm, K.p_tm)] P.le_qth with
            | .error e => return .error e
            | .ok ith => (pure (QUICK_PROVE_HYP th ith) : IO (Except String thm))
  | _ => return .error "NUM_LE_CONV"

/-- `NUM_EQ_CONV` (calc_num.ml 1290-1310). -/
def NUM_EQ_CONV (K : CalcNumConsts) (P : CalcNumProformas) (tm : term) :
    IO (Except String thm) := do
  match tm with
  | .Comb (.Comb (.Const "=" _) (.Comb (.Const "NUMERAL" _) mtm))
      (.Comb (.Const "NUMERAL" _) ntm) =>
    match (orderrelation mtm ntm : Except String Int) with
    | .error e => return .error e
    | .ok rel =>
      if rel == 0 then
        (pure (Kernel.INST [(ntm, K.n_tm)] P.eq_rth) : IO (Except String thm))
      else if rel < 0 then
        match (sbcbn K ntm mtm : Except String term) with
        | .error e => return .error e
        | .ok dtm =>
          match ← NUM_ADC_RULE K P dtm mtm with
          | .error e => return .error e
          | .ok th =>
            match Kernel.INST [(dtm, K.m_tm), (mtm, K.n_tm), (ntm, K.p_tm)] P.eq_pth with
            | .error e => return .error e
            | .ok ith => (pure (QUICK_PROVE_HYP th ith) : IO (Except String thm))
      else
        match (sbcbn K mtm ntm : Except String term) with
        | .error e => return .error e
        | .ok dtm =>
          match ← NUM_ADC_RULE K P dtm ntm with
          | .error e => return .error e
          | .ok th =>
            match Kernel.INST [(dtm, K.m_tm), (mtm, K.n_tm), (ntm, K.p_tm)] P.eq_qth with
            | .error e => return .error e
            | .ok ith => (pure (QUICK_PROVE_HYP th ith) : IO (Except String thm))
  | _ => return .error "NUM_EQ_CONV"

/- ---------------------------------------------------------------------- -/
/- Final hack-together (calc_num.ml lines 1440-1495).                     -/
/- ---------------------------------------------------------------------- -/

/-- Fold `net_of_conv` over a list of `(pattern, conv)` pairs onto `sofar`
    (`itlist (uncurry net_of_conv) l sofar`, right-to-left as in OCaml). -/
def netOfConvs (l : List (term × ioconv)) (sofar : HolCore.Nets.net gconv) :
    IO (Except String (HolCore.Nets.net gconv)) := do
  let mut acc := sofar
  -- `itlist` folds from the right; order does not affect the final net set.
  for (tm, conv) in l.reverse do
    match ← (Simp.net_of_conv tm conv acc
              : IO (Except String (HolCore.Nets.net gconv))) with
    | .error e => return .error e
    | .ok n => acc := n
  return .ok acc

/-- `NUM_REL_CONV` (calc_num.ml 1444-1453): the relational reductions
    (`<`, `<=`, `>`, `>=`, `=`) as a net conversion over `basic_net ()`. -/
def NUM_REL_CONV (numLtConv numLeConv numGtConv numGeConv numEqConv : ioconv) :
    IO (Except String ioconv) := do
  match ← (do
      let ltP ← HolLight.q "NUMERAL m < NUMERAL n"
      let leP ← HolLight.q "NUMERAL m <= NUMERAL n"
      let gtP ← HolLight.q "NUMERAL m > NUMERAL n"
      let geP ← HolLight.q "NUMERAL m >= NUMERAL n"
      let eqP ← HolLight.q "NUMERAL m = NUMERAL n"
      pure (ltP, leP, gtP, geP, eqP)
      : ExceptT String IO (term × term × term × term × term)).run with
  | .error e => return .error e
  | .ok (ltP, leP, gtP, geP, eqP) =>
    let bnet ← (Simp.basic_net : IO (HolCore.Nets.net gconv))
    match ← netOfConvs
        [(ltP, numLtConv), (leP, numLeConv), (gtP, numGtConv),
         (geP, numGeConv), (eqP, numEqConv)] bnet with
    | .error e => return .error e
    | .ok gconv_net => return .ok (Simp.REWRITES_CONV gconv_net)

/-- `num_red_conv_list` (calc_num.ml 1455-1474): the 18-entry pattern/conversion
    dispatch table.  All conversions are passed pre-built. -/
def num_red_conv_list
    (numSucConv numPreConv numFactConv numLtConv numLeConv numGtConv numGeConv
     numEqConv numEvenConv numOddConv numAddConv numSubConv numMultConv
     numExpConv numDivConv numModConv numMaxConv numMinConv : ioconv) :
    IO (Except String (List (term × ioconv))) := do
  match ← (do
      let sucP ← HolLight.q "SUC(NUMERAL n)"
      let preP ← HolLight.q "PRE(NUMERAL n)"
      let factP ← HolLight.q "FACT(NUMERAL n)"
      let ltP ← HolLight.q "NUMERAL m < NUMERAL n"
      let leP ← HolLight.q "NUMERAL m <= NUMERAL n"
      let gtP ← HolLight.q "NUMERAL m > NUMERAL n"
      let geP ← HolLight.q "NUMERAL m >= NUMERAL n"
      let eqP ← HolLight.q "NUMERAL m = NUMERAL n"
      let evenP ← HolLight.q "EVEN(NUMERAL n)"
      let oddP ← HolLight.q "ODD(NUMERAL n)"
      let addP ← HolLight.q "NUMERAL m + NUMERAL n"
      let subP ← HolLight.q "NUMERAL m - NUMERAL n"
      let mulP ← HolLight.q "NUMERAL m * NUMERAL n"
      let expP ← HolLight.q "(NUMERAL m) EXP (NUMERAL n)"
      let divP ← HolLight.q "(NUMERAL m) DIV (NUMERAL n)"
      let modP ← HolLight.q "(NUMERAL m) MOD (NUMERAL n)"
      let maxP ← HolLight.q "MAX (NUMERAL m) (NUMERAL n)"
      let minP ← HolLight.q "MIN (NUMERAL m) (NUMERAL n)"
      pure [(sucP, numSucConv), (preP, numPreConv), (factP, numFactConv),
            (ltP, numLtConv), (leP, numLeConv), (gtP, numGtConv),
            (geP, numGeConv), (eqP, numEqConv), (evenP, numEvenConv),
            (oddP, numOddConv), (addP, numAddConv), (subP, numSubConv),
            (mulP, numMultConv), (expP, numExpConv), (divP, numDivConv),
            (modP, numModConv), (maxP, numMaxConv), (minP, numMinConv)]
      : ExceptT String IO (List (term × ioconv))).run with
  | .error e => return .error e
  | .ok l => return .ok l

/-- `NUM_RED_CONV` (calc_num.ml 1476-1479): the full single-step numeral
    reduction as a net conversion over `basic_net ()`. -/
def NUM_RED_CONV (redList : List (term × ioconv)) : IO (Except String ioconv) := do
  let bnet ← (Simp.basic_net : IO (HolCore.Nets.net gconv))
  match ← netOfConvs redList bnet with
  | .error e => return .error e
  | .ok gconv_net => return .ok (Simp.REWRITES_CONV gconv_net)

/-- `NUM_REDUCE_CONV = DEPTH_CONV NUM_RED_CONV` (calc_num.ml 1481). -/
def NUM_REDUCE_CONV (numRedConv : ioconv) : ioconv := Simp.depthConvIO numRedConv

/-- `num_compute_add_convs` (calc_num.ml 1483-1487): add every `num_red_conv_list`
    entry to a compset as a conversion attached to its head constant at the
    pattern's argument count. -/
def num_compute_add_convs (redList : List (term × ioconv))
    (add_conv : term → Int → ioconv → HolMath.Compute.compset → IO (Except String Unit))
    (cs : HolMath.Compute.compset) : IO (Except String Unit) := do
  for (pat, the_conv) in redList do
    let (c, args) := strip_comb pat
    match ← add_conv c (Int.ofNat args.length) the_conv cs with
    | .error e => return .error e
    | .ok _ => pure ()
  return .ok ()

/-- `NUM_COMPUTE_CONV` (calc_num.ml 1489-1493): call-by-value evaluation of a
    numeral term via a `bool_compset ()` extended with the reduction
    conversions.  `bool_compset`, `set_skip`, `add_conv` and `WEAK_CBV_CONV`
    are injected because the pure library cannot reach the session state. -/
def NUM_COMPUTE_CONV (redList : List (term × ioconv))
    (bool_compset : IO (Except String HolMath.Compute.compset))
    (set_skip : HolMath.Compute.compset → term → Option Int → IO (Except String Unit))
    (add_conv : term → Int → ioconv → HolMath.Compute.compset → IO (Except String Unit))
    (WEAK_CBV_CONV : HolMath.Compute.compset → ioconv)
    (condTm : term) : IO (Except String ioconv) := do
  match ← bool_compset with
  | .error e => return .error e
  | .ok cs =>
    match ← set_skip cs condTm (some 1) with
    | .error e => return .error e
    | .ok _ =>
      match ← num_compute_add_convs redList add_conv cs with
      | .error e => return .error e
      | .ok _ => return .ok (WEAK_CBV_CONV cs)

/- ---------------------------------------------------------------------- -/
/- I do like this after all...                                            -/
/- ---------------------------------------------------------------------- -/

/-- `num_CONV tm` (calc_num.ml 1500-1507): `|- NUMERAL n = SUC (NUMERAL (n-1))`
    for a positive numeral `tm`. -/
def num_CONV (K : CalcNumConsts) (P : CalcNumProformas)
    (mk_numeral : Rat → Except String term) (tm : term) :
    IO (Except String thm) := do
  -- `let SUC_tm = `SUC` in fun tm -> ...`: the constant is fixed when
  -- num_CONV is defined, so hiding or overloading `SUC` later has no effect.
  let SUC_tm := K.suc_tm
  ExceptT.run do
    let n := (← liftExcept (dest_numeral tm : Except String Rat)) - num_1
    if n < num_0 then throw "num_CONV"
    let tm' ← liftExcept (mk_numeral n)
    let th ← ExceptT.mk (NUM_SUC_CONV K P (← liftExcept (mk_comb SUC_tm tm')))
    liftExcept (Equal.SYM th)

end Numerals

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv conv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolLight HolLight.Syntax

/- ---------------------------------------------------------------------- -/
/- NUM_SQUARE_RULE (calc_num.ml 823-892).                                 -/
/- ---------------------------------------------------------------------- -/

mutual
/-- `GEN_NUM_SQUARE_RULE w z tm` (calc_num.ml 825-890): square a raw numeral
    with `w` `BIT1`s and `z` `BIT0`s. -/
partial def GEN_NUM_SQUARE_RULE [HolBase] (K : CalcNumConsts)
    (P : CalcNumProformas) (mk_numeral : Rat → Except String term)
    (w z : Nat) (tm : term) : IO (Except String thm) := ExceptT.run do
  match tm with
  | .Const "_0" _ => return P.sq_pth_0
  | .Comb (.Const "BIT0" _) mtm =>
    match mtm with
    | .Comb (.Const "BIT0" _) (.Comb (.Const "BIT0" _) ptm) =>
      let th1 ← ExceptT.mk (GEN_NUM_SQUARE_RULE K P mk_numeral w (z - 3) ptm)
      let ntm ← liftExcept (rand (concl th1))
      EQ_MP (← INST [(ptm, K.m_tm), (ntm, K.n_tm)] P.sq_pth_even3) th1
    | _ =>
      let th1 ← ExceptT.mk (GEN_NUM_SQUARE_RULE K P mk_numeral w (z - 1) mtm)
      let ntm ← liftExcept (rand (concl th1))
      EQ_MP (← INST [(mtm, K.m_tm), (ntm, K.n_tm)] P.sq_pth_even) th1
  | .Comb (.Const "BIT1" _) mtm =>
    if mtm == K.zero_tm then return P.sq_pth_1
    if (w < 100 || z < 20) && w + z < 150 then
      match mtm with
      | .Comb (.Const "BIT1" _) (.Comb (.Const "BIT1" _) ntm) =>
        let th1 ← ExceptT.mk (NUM_ADD_RULE K P ntm K.one_tm)
        let mtm ← liftExcept (rand (concl th1))
        let th2 ← ExceptT.mk (NUM_SQUARE_RULE K P mk_numeral mtm)
        let ptm ← liftExcept (rand (concl th2))
        let atm ← liftExcept (do subbn K (← mk_comb K.BIT0_tm (← mk_comb K.BIT0_tm ptm)) mtm)
        let th3 ← ExceptT.mk (NUM_ADD_RULE K P mtm atm)
        let th4 ← INST [(atm, K.a_tm), (mtm, K.m_tm), (ntm, K.n_tm), (ptm, K.p_tm)] P.sq_pth_qstep
        liftExcept (QUICK_PROVE_HYP (← CONJ th1 (← CONJ th2 th3)) th4)
      | _ =>
        let th1 ← ExceptT.mk (GEN_NUM_SQUARE_RULE K P mk_numeral (w - 1) z mtm)
        let ntm ← liftExcept (rand (concl th1))
        let th2 ← EQ_MP (← INST [(mtm, K.m_tm), (ntm, K.n_tm)] P.sq_pth_odd) th1
        match concl th2 with
        | .Comb _ (.Comb _ (.Comb _ (.Comb (.Comb _ ptm) qtm))) =>
          let th3 ← ExceptT.mk (NUM_ADD_RULE K P ptm qtm)
          TRANS th2 (← liftExcept (do AP_BIT1 P (← AP_BIT0 P th3)))
        | _ => throw "GEN_NUM_SQUARE_RULE"
    else if w + z < 800 then
      let k2 : Int := (w + z) / 2
      let th1 ← ExceptT.mk (NUM_SHIFT_CONV K P k2 tm)
      match ← liftExcept (rand (concl th1)) with
      | .Comb (.Comb _ ltm) (.Comb (.Comb _ ptm) htm) =>
        let th2 ← ExceptT.mk (NUM_ADD_RULE K P htm ltm)
        let mtm ← liftExcept (rand (concl th2))
        let th3 ← ExceptT.mk (NUM_SQUARE_RULE K P mk_numeral htm)
        let th4 ← ExceptT.mk (NUM_SQUARE_RULE K P mk_numeral ltm)
        let th5 ← ExceptT.mk (NUM_SQUARE_RULE K P mk_numeral mtm)
        let atm ← liftExcept (rand (concl th3))
        let ctm ← liftExcept (rand (concl th4))
        let dtm ← liftExcept (rand (concl th5))
        let th6 ← ExceptT.mk (NUM_ADD_RULE K P atm ctm)
        let etm ← liftExcept (rand (concl th6))
        let btm ← liftExcept (subbn K dtm etm)
        let th7 ← ExceptT.mk (NUM_ADD_RULE K P etm btm)
        let dtm ← liftExcept (rand (concl th7))
        let th8 ← INST [(atm, K.a_tm), (btm, K.b_tm), (ctm, K.c_tm), (dtm, K.d_tm),
                        (etm, K.e_tm), (htm, K.h_tm), (ltm, K.l_tm), (mtm, K.m_tm),
                        (tm, K.n_tm), (ptm, K.p_tm)] P.sq_pth_rec
        let th9 ← liftExcept (QUICK_PROVE_HYP
          (← end_itlist CONJ [th1, th2, th3, th4, th5, th6, th7]) th8)
        CONV_RULE (RAND_CONV (thenc_ (RAND_CONV (RAND_CONV (NUM_UNSHIFT_CONV K P)))
                                     (NUM_UNSHIFT_CONV K P))) th9
      | _ => throw "GEN_NUM_SQUARE_RULE"
    else
      let k3 : Int := (w + z) / 3
      let th0 ← ExceptT.mk ((thenc_ (NUM_SHIFT_CONV K P k3)
                   (RAND_CONV (RAND_CONV (NUM_SHIFT_CONV K P k3)))) tm)
      match ← liftExcept (rand (concl th0)) with
      | .Comb (.Comb _ ltm) (.Comb (.Comb _ ptm) (.Comb (.Comb _ mtm) (.Comb (.Comb _ _) htm))) =>
        let th1 ← ExceptT.mk (NUM_SQUARE_RULE K P mk_numeral htm)
        let th2 ← ExceptT.mk (NUM_SQUARE_RULE K P mk_numeral ltm)
        let atm ← liftExcept (rand (concl th2))
        let etm ← liftExcept (rand (concl th1))
        let lnum ← liftExcept (dest_raw_numeral ltm)
        let mnum ← liftExcept (dest_raw_numeral mtm)
        let hnum ← liftExcept (dest_raw_numeral htm)
        let btm ← liftExcept (do rand (← mk_numeral (2 * lnum * mnum)))
        let ctm ← liftExcept (do rand (← mk_numeral (mnum * mnum + 2 * lnum * hnum)))
        let dtm ← liftExcept (do rand (← mk_numeral (2 * hnum * mnum)))
        let th ← INST [(atm, K.a_tm), (btm, K.b_tm), (ctm, K.c_tm), (dtm, K.d_tm),
                       (etm, K.e_tm), (htm, K.h_tm), (mtm, K.m_tm), (ltm, K.l_tm),
                       (ptm, K.p_tm)] P.sq_pth_toom3
        let TOOM3 := TOOM3_CONV K P
        let th' ← CONV_RULE
          (binop2ConvIO
            (RAND_CONV (RAND_CONV (binop2ConvIO TOOM3 (binop2ConvIO TOOM3 TOOM3))))
            TOOM3) th
        match conjuncts (← liftExcept (do rand (← rand (← lhand (concl th'))))) with
        | [tm3, tm4, tm5] =>
          let th3 ← ExceptT.mk (NUM_SQUARE_RULE K P mk_numeral (← liftExcept (do lhand (← lhand tm3))))
          let th4 ← ExceptT.mk (NUM_SQUARE_RULE K P mk_numeral (← liftExcept (do lhand (← lhand tm4))))
          let th5 ← ExceptT.mk (NUM_SQUARE_RULE K P mk_numeral (← liftExcept (do lhand (← lhand tm5))))
          MP th' (← end_itlist CONJ [th1, th2, th3, th4, th5])
        | _ => throw "GEN_NUM_SQUARE_RULE"
      | _ => throw "GEN_NUM_SQUARE_RULE"
  | _ => throw "GEN_NUM_SQUARE_RULE: malformed numeral"

/-- `NUM_SQUARE_RULE tm` (calc_num.ml 891). -/
partial def NUM_SQUARE_RULE [HolBase] (K : CalcNumConsts)
    (P : CalcNumProformas) (mk_numeral : Rat → Except String term)
    (tm : term) : IO (Except String thm) := ExceptT.run do
  let (w, z) ← liftExcept (bitcounts tm)
  ExceptT.mk (GEN_NUM_SQUARE_RULE K P mk_numeral w z tm)
end

/- ---------------------------------------------------------------------- -/
/- NUM_MUL_RULE (calc_num.ml 894-1010).                                   -/
/- ---------------------------------------------------------------------- -/

/-- `NUM_MUL_RULE k l tm tm'` (calc_num.ml 971-1010): multiply raw numerals
    with `k` and `l` bits. -/
partial def NUM_MUL_RULE [HolBase] (K : CalcNumConsts)
    (P : CalcNumProformas) (mk_numeral : Rat → Except String term)
    (k l : Int) (tm tm' : term) : IO (Except String thm) := ExceptT.run do
  match tm, tm' with
  | .Const "_0" _, _ => INST [(tm', K.n_tm)] P.mul_pth_0l
  | _, .Const "_0" _ => INST [(tm, K.m_tm)] P.mul_pth_0r
  | .Comb (.Const "BIT1" _) (.Const "_0" _), _ => INST [(tm', K.n_tm)] P.mul_pth_1l
  | _, .Comb (.Const "BIT1" _) (.Const "_0" _) => INST [(tm, K.m_tm)] P.mul_pth_1r
  | .Comb (.Const "BIT0" _) mtm, _ =>
    let th0 ← ExceptT.mk (NUM_MUL_RULE K P mk_numeral (k - 1) l mtm tm')
    let th1 ← INST [(mtm, K.m_tm), (tm', K.n_tm), (← liftExcept (rand (concl th0)), K.p_tm)]
                P.mul_pth_evenl
    EQ_MP th1 th0
  | _, .Comb (.Const "BIT0" _) ntm =>
    let th0 ← ExceptT.mk (NUM_MUL_RULE K P mk_numeral k (l - 1) tm ntm)
    let th1 ← INST [(tm, K.m_tm), (ntm, K.n_tm), (← liftExcept (rand (concl th0)), K.p_tm)]
                P.mul_pth_evenr
    EQ_MP th1 th0
  | .Comb (.Const "BIT1" _) mtm, .Comb (.Const "BIT1" _) ntm =>
    if k ≤ 50 || l ≤ 50 || k * k ≤ l || l * l ≤ k then
      match mtm, ntm with
      | .Comb (.Const "BIT1" _) (.Comb (.Const "BIT1" _) _), _ =>
        let th1 ← ExceptT.mk (NUM_ADC_RULE K P K.zero_tm tm)
        let ptm ← liftExcept (rand (concl th1))
        let th2 ← ExceptT.mk (NUM_MUL_RULE K P mk_numeral k l ptm tm')
        let atm ← liftExcept (do subbn K (← rand (concl th2)) tm')
        let th3 ← INST [(tm, K.m_tm), (tm', K.n_tm), (ptm, K.p_tm), (atm, K.a_tm)]
                    P.mul_pth_recodel
        let th4 ← PROVE_HYP th1 th3
        EQ_MP th4 (← TRANS th2 (← SYM (← ExceptT.mk (NUM_ADD_RULE K P atm tm'))))
      | _, .Comb (.Const "BIT1" _) (.Comb (.Const "BIT1" _) _) =>
        let th1 ← ExceptT.mk (NUM_ADC_RULE K P K.zero_tm tm')
        let ptm ← liftExcept (rand (concl th1))
        let th2 ← ExceptT.mk (NUM_MUL_RULE K P mk_numeral k l tm ptm)
        let atm ← liftExcept (do subbn K (← rand (concl th2)) tm)
        let th3 ← INST [(tm, K.m_tm), (tm', K.n_tm), (ptm, K.p_tm), (atm, K.a_tm)]
                    P.mul_pth_recoder
        let th4 ← PROVE_HYP th1 th3
        EQ_MP th4 (← TRANS th2 (← SYM (← ExceptT.mk (NUM_ADD_RULE K P atm tm))))
      | _, _ =>
        if k ≤ l then
          let th0 ← ExceptT.mk (NUM_MUL_RULE K P mk_numeral (k - 1) l mtm tm')
          let ptm ← liftExcept (rand (concl th0))
          let th1 ← EQ_MP (← INST [(mtm, K.m_tm), (tm', K.n_tm), (ptm, K.p_tm)] P.mul_pth_oddl) th0
          let tm1 ← liftExcept (do lhand (← rand (concl th1)))
          TRANS th1 (← ExceptT.mk (NUM_ADD_RULE K P tm1 tm'))
        else
          let th0 ← ExceptT.mk (NUM_MUL_RULE K P mk_numeral k (l - 1) tm ntm)
          let ptm ← liftExcept (rand (concl th0))
          let th1 ← EQ_MP (← INST [(tm, K.m_tm), (ntm, K.n_tm), (ptm, K.p_tm)] P.mul_pth_oddr) th0
          let tm1 ← liftExcept (do lhand (← rand (concl th1)))
          TRANS th1 (← ExceptT.mk (NUM_ADD_RULE K P tm1 tm))
    else
      let mval ← liftExcept (dest_raw_numeral mtm)
      let nval ← liftExcept (dest_raw_numeral ntm)
      if nval ≤ mval then
        let ptm ← liftExcept (do rand (← mk_numeral (mval - nval)))
        let th2 ← ExceptT.mk (NUM_ADD_RULE K P ntm ptm)
        let th3 ← ExceptT.mk (NUM_ADC_RULE K P mtm ntm)
        let atm ← liftExcept (rand (concl th3))
        let th4 ← ExceptT.mk (NUM_SQUARE_RULE K P mk_numeral ptm)
        let btm ← liftExcept (rand (concl th4))
        let th5 ← ExceptT.mk (NUM_SQUARE_RULE K P mk_numeral atm)
        let ctm ← liftExcept (rand (concl th5))
        let dtm ← liftExcept (subbn K ctm btm)
        let th6 ← ExceptT.mk (NUM_ADD_RULE K P btm dtm)
        let th1 ← INST [(atm, K.a_tm), (btm, K.b_tm), (ctm, K.c_tm), (dtm, K.d_tm),
                        (mtm, K.m_tm), (ntm, K.n_tm), (ptm, K.p_tm)] P.mul_pth_oo1
        liftExcept (QUICK_PROVE_HYP (← end_itlist CONJ [th2, th3, th4, th5, th6]) th1)
      else
        let ptm ← liftExcept (do rand (← mk_numeral (nval - mval)))
        let th2 ← ExceptT.mk (NUM_ADD_RULE K P mtm ptm)
        let th3 ← ExceptT.mk (NUM_ADC_RULE K P ntm mtm)
        let atm ← liftExcept (rand (concl th3))
        let th4 ← ExceptT.mk (NUM_SQUARE_RULE K P mk_numeral ptm)
        let btm ← liftExcept (rand (concl th4))
        let th5 ← ExceptT.mk (NUM_SQUARE_RULE K P mk_numeral atm)
        let ctm ← liftExcept (rand (concl th5))
        let dtm ← liftExcept (subbn K ctm btm)
        let th6 ← ExceptT.mk (NUM_ADD_RULE K P btm dtm)
        let th1 ← INST [(atm, K.a_tm), (btm, K.b_tm), (ctm, K.c_tm), (dtm, K.d_tm),
                        (mtm, K.m_tm), (ntm, K.n_tm), (ptm, K.p_tm)] P.mul_pth_oo2
        liftExcept (QUICK_PROVE_HYP (← end_itlist CONJ [th2, th3, th4, th5, th6]) th1)
  | _, _ => throw "NUM_MUL_RULE"

/- ---------------------------------------------------------------------- -/
/- The exported numeral conversions (calc_num.ml 1124-1229).              -/
/- ---------------------------------------------------------------------- -/

/-- `NUM_MULT_CONV'` (calc_num.ml 1124-1135). -/
partial def NUM_MULT_CONV' [HolBase] (K : CalcNumConsts)
    (P : CalcNumProformas) (mk_numeral : Rat → Except String term) : ioconv :=
  fun tm => ExceptT.run do
  match tm with
  | .Comb (.Comb (.Const "*" _) mtm) ntm =>
    if mtm == ntm then
      let th1 ← ExceptT.mk (NUM_SQUARE_RULE K P mk_numeral mtm)
      let ptm ← liftExcept (rand (concl th1))
      EQ_MP (← INST [(mtm, K.m_tm), (ptm, K.p_tm)] P.mulc_pth_refl) th1
    else
      let (w1, z1) ← liftExcept (bitcounts mtm)
      let (w2, z2) ← liftExcept (bitcounts ntm)
      ExceptT.mk (NUM_MUL_RULE K P mk_numeral (Int.ofNat (w1 + z1)) (Int.ofNat (w2 + z2)) mtm ntm)
  | _ => throw "NUM_MULT_CONV'"

/-- `NUM_MULT_CONV` (calc_num.ml 1161-1179). -/
partial def NUM_MULT_CONV [HolBase] (K : CalcNumConsts)
    (P : CalcNumProformas) (mk_numeral : Rat → Except String term) : ioconv :=
  fun tm => ExceptT.run do
  match tm with
  | .Comb (.Comb (.Const "*" _) (.Comb (.Const "NUMERAL" _) mtm)) (.Comb (.Const "NUMERAL" _) ntm) =>
    if mtm == ntm then
      let th1 ← ExceptT.mk (NUM_SQUARE_RULE K P mk_numeral mtm)
      let ptm ← liftExcept (rand (concl th1))
      EQ_MP (← INST [(mtm, K.m_tm), (ptm, K.p_tm)] P.mult_pth_refl) th1
    else
      let (w1, z1) ← liftExcept (bitcounts mtm)
      let (w2, z2) ← liftExcept (bitcounts ntm)
      let th1 ← ExceptT.mk (NUM_MUL_RULE K P mk_numeral (Int.ofNat (w1 + z1)) (Int.ofNat (w2 + z2)) mtm ntm)
      let ptm ← liftExcept (rand (concl th1))
      EQ_MP (← INST [(mtm, K.m_tm), (ntm, K.n_tm), (ptm, K.p_tm)] P.mult_topthm) th1
  | _ => throw "NUM_MULT_CONV"

/-- `NUM_EXP_CONV` (calc_num.ml 1183-1229).  `tconv` is
    `GEN_REWRITE_CONV I [tth]`, built once in `CalcNumNets`. -/
partial def NUM_EXP_CONV [HolBase] (K : CalcNumConsts)
    (P : CalcNumProformas) (mk_numeral : Rat → Except String term) (tconv : ioconv) : ioconv :=
  let NUM_MULT_CONV' := NUM_MULT_CONV' K P mk_numeral
  let rec NUM_EXP_CONV (l r : term) : IO (Except String thm) := ExceptT.run do
    if r == K.zero_tm then return ← INST [(l, K.m_tm)] P.exp_pth
    let (b, r') ← liftExcept (dest_comb r)
    if b == K.BIT0_tm then
      let th1 ← ExceptT.mk (NUM_EXP_CONV l r')
      let tm1 ← liftExcept (rand (concl th1))
      let th2 ← ExceptT.mk (NUM_MULT_CONV' (← liftExcept (do (← mk_binop K.mul_tm tm1) tm1)))
      let tm2 ← liftExcept (rand (concl th2))
      MP (← MP (← INST [(l, K.m_tm), (r', K.n_tm), (tm1, K.p_tm), (tm2, K.a_tm)] P.exp_pth0) th1) th2
    else
      let th1 ← ExceptT.mk (NUM_EXP_CONV l r')
      let tm1 ← liftExcept (rand (concl th1))
      let th2 ← ExceptT.mk (NUM_MULT_CONV' (← liftExcept (do (← mk_binop K.mul_tm tm1) tm1)))
      let tm2 ← liftExcept (rand (concl th2))
      let th3 ← ExceptT.mk (NUM_MULT_CONV' (← liftExcept (do (← mk_binop K.mul_tm l) tm2)))
      let tm3 ← liftExcept (rand (concl th3))
      MP (← MP (← MP (← INST [(l, K.m_tm), (r', K.n_tm), (tm1, K.p_tm), (tm2, K.b_tm),
                               (tm3, K.a_tm)] P.exp_pth1) th1) th2) th3
  fun tm => ExceptT.run do
    try
      let th ← ExceptT.mk (tconv tm)
      let (lop, r) ← liftExcept (dest_comb (← liftExcept (rand (concl th))))
      let (_, l) ← liftExcept (dest_comb lop)
      if !(wellformed l && wellformed r) then throw ""
      let th' ← ExceptT.mk (NUM_EXP_CONV l r)
      let tm' ← liftExcept (rand (concl th'))
      TRANS (← TRANS th th') (← INST [(tm', K.m_tm)] P.exp_fth)
    catch _ => throw "NUM_EXP_CONV"
/- ---------------------------------------------------------------------- -/
/- Now more delicate conversions for situations where efficiency matters. -/
/- ---------------------------------------------------------------------- -/

/- ---------------------------------------------------------------------- -/
/- NUM_EVEN_CONV, NUM_ODD_CONV (calc_num.ml 211-217).                     -/
/- ---------------------------------------------------------------------- -/

/-- `NUM_EVEN_CONV = let tth,rths = CONJ_PAIR ARITH_EVEN in
    GEN_REWRITE_CONV I [tth] THENC GEN_REWRITE_CONV I [rths]`. -/
def NUM_EVEN_CONV [HolBase] (ARITH_EVEN : thm) : ExceptT String IO ioconv := do
  let (tth, rths) ← CONJ_PAIR ARITH_EVEN
  let c2 ← GEN_REWRITE_CONV_NET id [rths]
  let c1 ← GEN_REWRITE_CONV_NET id [tth]
  return thenc_ c1 c2

/-- `NUM_ODD_CONV`, likewise with `ARITH_ODD`. -/
def NUM_ODD_CONV [HolBase] (ARITH_ODD : thm) : ExceptT String IO ioconv := do
  let (tth, rths) ← CONJ_PAIR ARITH_ODD
  let c2 ← GEN_REWRITE_CONV_NET id [rths]
  let c1 ← GEN_REWRITE_CONV_NET id [tth]
  return thenc_ c1 c2

/- ---------------------------------------------------------------------- -/
/- What the remaining conversions build before their `fun tm ->`.        -/
/- ---------------------------------------------------------------------- -/

/-- The nets, conversions and terms that calc_num.ml's later conversions
    build once, in the `let ... in` before their `fun tm ->`. -/
structure CalcNumNets where
  /-- NUM_EVEN_CONV, NUM_ODD_CONV (calc_num.ml 211-217). -/
  even_conv : ioconv
  odd_conv : ioconv
  /-- NUM_EXP_CONV's `tconv = GEN_REWRITE_CONV I [tth]` (1206). -/
  exp_tconv : ioconv
  /-- `GEN_REWRITE_CONV I [GT]`, `GEN_REWRITE_CONV I [GE]` (1314-1316). -/
  gt_conv : ioconv
  ge_conv : ioconv
  /-- NUM_PRE_CONV's `pre = `PRE`` (1330). -/
  pre_tm : term
  /-- NUM_DIV_CONV's `q`, `r` and NUM_FACT_CONV's `w`, `x`, `y`, `z`. -/
  q_tm : term
  r_tm : term
  w_tm : term
  x_tm : term
  y_tm : term
  z_tm : term
  /-- NUM_MAX_CONV / NUM_MIN_CONV's `GEN_REWRITE_CONV I [COND_CLAUSES]`. -/
  max_cond_conv : ioconv
  min_cond_conv : ioconv
  /-- EXPAND_CASES_CONV's `base_CONV`, the `GEN_REWRITE_CONV I [pth_step]` of
      `step_CONV`, and `REWRITE_CONV[GSYM CONJ_ASSOC]`. -/
  expand_base : ioconv
  expand_step : ioconv
  expand_assoc : ioconv
  /-- EXP_MOD_CONV's `conv_zero`, `conv_0`, `conv_even`, `conv_odd`. -/
  expmod_zero : ioconv
  expmod_0 : ioconv
  expmod_even : ioconv
  expmod_odd : ioconv
  deriving Inhabited

/-- Build `CalcNumNets`, in calc_num.ml's order.  `REWRITE_CONV[GSYM
    CONJ_ASSOC]` uses the basic rewrites current when this runs, so Session
    runs it at calc_num.ml's position in the load. -/
@[nospecialize]
def setupCalcNumNets [HolBase] (A : ArithRewrites) (K : CalcNumConsts) (P : CalcNumProformas)
    (GT GE COND_CLAUSES CONJ_ASSOC MOD_ZERO : thm) : ExceptT String IO CalcNumNets := do
  let even_conv ← NUM_EVEN_CONV A.ARITH_EVEN
  let odd_conv ← NUM_ODD_CONV A.ARITH_ODD
  let exp_tconv ← GEN_REWRITE_CONV_NET id [P.exp_tth]
  let gt_conv ← GEN_REWRITE_CONV_NET id [GT]
  let ge_conv ← GEN_REWRITE_CONV_NET id [GE]
  let pre_tm ← q r"PRE"
  let q_tm := mk_var "q" K.num_ty
  let r_tm := mk_var "r" K.num_ty
  let w_tm := mk_var "w" K.num_ty
  let x_tm := mk_var "x" K.num_ty
  let y_tm := mk_var "y" K.num_ty
  let z_tm := mk_var "z" K.num_ty
  let max_cond_conv ← GEN_REWRITE_CONV_NET id [COND_CLAUSES]
  let min_cond_conv ← GEN_REWRITE_CONV_NET id [COND_CLAUSES]
  let expand_base ← GEN_REWRITE_CONV_NET id [P.expand_pth_base]
  let expand_step ← GEN_REWRITE_CONV_NET id [P.expand_pth_step]
  let expand_assoc ← REWRITE_CONV_NET [← GSYM CONJ_ASSOC]
  let expmod_zero ← GEN_REWRITE_CONV_NET id [MOD_ZERO]
  let expmod_0 ← GEN_REWRITE_CONV_NET id [P.expmod_pth_0]
  let expmod_even ← GEN_REWRITE_CONV_NET id [P.expmod_pth_even]
  let expmod_odd ← GEN_REWRITE_CONV_NET id [P.expmod_pth_odd]
  return { even_conv, odd_conv, exp_tconv, gt_conv, ge_conv, pre_tm,
           q_tm, r_tm, w_tm, x_tm, y_tm, z_tm, max_cond_conv, min_cond_conv,
           expand_base, expand_step, expand_assoc,
           expmod_zero, expmod_0, expmod_even, expmod_odd }

/- ---------------------------------------------------------------------- -/
/- NUM_GT_CONV, NUM_GE_CONV, NUM_PRE_CONV (calc_num.ml 1314-1341).        -/
/- ---------------------------------------------------------------------- -/

/-- `NUM_GT_CONV = GEN_REWRITE_CONV I [GT] THENC NUM_LT_CONV`. -/
def NUM_GT_CONV (N : CalcNumNets) (K : CalcNumConsts) (P : CalcNumProformas) : ioconv :=
  thenc_ N.gt_conv (NUM_LT_CONV K P)

/-- `NUM_GE_CONV = GEN_REWRITE_CONV I [GE] THENC NUM_LE_CONV`. -/
def NUM_GE_CONV (N : CalcNumNets) (K : CalcNumConsts) (P : CalcNumProformas) : ioconv :=
  thenc_ N.ge_conv (NUM_LE_CONV K P)

/-- `NUM_PRE_CONV` (calc_num.ml 1319-1341). -/
def NUM_PRE_CONV [HolBase] (N : CalcNumNets) (K : CalcNumConsts) (P : CalcNumProformas)
    (mk_numeral : Rat → Except String term) : ioconv := fun tm => ExceptT.run do
  try
    let (l, r) ← liftExcept (dest_comb tm)
    if !(l == N.pre_tm) then throw ""
    let x ← liftExcept (dest_numeral r)
    if x == num_0 then return P.pre_tth
    let tm' ← liftExcept (mk_numeral (x - num_1))
    let th1 ← ExceptT.mk (NUM_SUC_CONV K P (← liftExcept (mk_comb K.suc_tm tm')))
    MP (← INST [(tm', K.m_tm), (r, K.n_tm)] P.pre_pth) th1
  catch _ => throw "NUM_PRE_CONV"

/- ---------------------------------------------------------------------- -/
/- NUM_SUB_CONV (calc_num.ml 1343-1370).                                  -/
/- ---------------------------------------------------------------------- -/

/-- `NUM_SUB_CONV`.  `(-)`, `(+)`, `(<=)` are `CalcNumConsts`' constants: a
    quotation here would give a free variable when the symbol is not
    declared in the ambient session. -/
def NUM_SUB_CONV [HolBase] (K : CalcNumConsts) (P : CalcNumProformas)
    (mk_numeral : Rat → Except String term) : ioconv := fun tm => ExceptT.run do
  try
    let (l, r) ← liftExcept (dest_binop K.sub_tm tm)
    let ln ← liftExcept (dest_numeral l)
    let rn ← liftExcept (dest_numeral r)
    if ln ≤ rn then
      let th0 ← EQT_ELIM (← ExceptT.mk (NUM_LE_CONV K P (← liftExcept (do (← mk_binop K.le_tm l) r))))
      let pth ← INST [(l, K.p_tm), (r, K.n_tm)] P.sub_pth0
      MP pth th0
    else
      let k ← liftExcept (mk_numeral (ln - rn))
      let th0 ← ExceptT.mk (NUM_ADD_CONV K P (← liftExcept (do (← mk_binop K.add_tm k) r)))
      let pth ← INST [(k, K.m_tm), (l, K.p_tm), (r, K.n_tm)] P.sub_pth1
      MP pth th0
  catch _ => throw "NUM_SUB_CONV"

/- ---------------------------------------------------------------------- -/
/- NUM_DIV_CONV, NUM_MOD_CONV (calc_num.ml 1372-1397).                    -/
/- ---------------------------------------------------------------------- -/

/-- `NUM_DIVMOD_CONV x y` (calc_num.ml 1381-1392). -/
def NUM_DIVMOD_CONV [HolBase] (N : CalcNumNets) (K : CalcNumConsts) (P : CalcNumProformas)
    (mk_numeral : Rat → Except String term) (x y : Rat) : ExceptT String IO thm := do
  if y == num_0 then return ← SPEC (← liftExcept (mk_numeral x)) P.divmod_pth0
  let k := quo_num x y
  let l := mod_num x y
  let th0 ← INST [(← liftExcept (mk_numeral x), K.m_tm), (← liftExcept (mk_numeral y), K.n_tm),
                  (← liftExcept (mk_numeral k), N.q_tm), (← liftExcept (mk_numeral l), N.r_tm)]
              P.divmod_pth
  let tm0 ← liftExcept (do lhand (← lhand (concl th0)))
  let th1 ← ExceptT.mk ((thenc_ (LAND_CONV (NUM_MULT_CONV K P mk_numeral)) (NUM_ADD_CONV K P)) tm0)
  let th2 ← MP th0 th1
  let tm2 ← liftExcept (lhand (concl th2))
  MP th2 (← EQT_ELIM (← ExceptT.mk (NUM_LT_CONV K P tm2)))

/-- `NUM_DIV_CONV` (calc_num.ml 1393-1395).  `(DIV)` is `CalcNumConsts.div_tm`
    (recovered from `DIVISION`) rather than a quotation; see `NUM_SUB_CONV`. -/
def NUM_DIV_CONV [HolBase] (N : CalcNumNets) (K : CalcNumConsts) (P : CalcNumProformas)
    (mk_numeral : Rat → Except String term) : ioconv := fun tm => ExceptT.run do
  try
    let (xt, yt) ← liftExcept (dest_binop K.div_tm tm)
    CONJUNCT1 (← NUM_DIVMOD_CONV N K P mk_numeral (← liftExcept (dest_numeral xt))
                 (← liftExcept (dest_numeral yt)))
  catch _ => throw "NUM_DIV_CONV"

/-- `NUM_MOD_CONV` (calc_num.ml 1396-1397). -/
def NUM_MOD_CONV [HolBase] (N : CalcNumNets) (K : CalcNumConsts) (P : CalcNumProformas)
    (mk_numeral : Rat → Except String term) : ioconv := fun tm => ExceptT.run do
  try
    let (xt, yt) ← liftExcept (dest_binop K.mod_tm tm)
    CONJUNCT2 (← NUM_DIVMOD_CONV N K P mk_numeral (← liftExcept (dest_numeral xt))
                 (← liftExcept (dest_numeral yt)))
  catch _ => throw "NUM_MOD_CONV"

/- ---------------------------------------------------------------------- -/
/- NUM_FACT_CONV (calc_num.ml 1398-1425).                                 -/
/- ---------------------------------------------------------------------- -/

/-- `NUM_FACT_CONV` (calc_num.ml 1398-1425).  `SUC` and `(*)` are
    `CalcNumConsts`' constants. -/
partial def NUM_FACT_CONV [HolBase] (N : CalcNumNets) (K : CalcNumConsts) (P : CalcNumProformas)
    (mk_numeral : Rat → Except String term) : ioconv :=
  let mksuc (n : Rat) : ExceptT String IO thm := do
    let n' := n - num_1
    ExceptT.mk (NUM_SUC_CONV K P (← liftExcept (do mk_comb K.suc_tm (← mk_numeral n'))))
  let rec NUM_FACT_CONV (n : Rat) : ExceptT String IO thm := do
    if n == num_0 then return P.fact_pth_0
    let th0 ← mksuc n
    let tmx ← liftExcept (do rand (← lhand (concl th0)))
    let tm0 ← liftExcept (rand (concl th0))
    let th1 ← NUM_FACT_CONV (n - num_1)
    let tm1 ← liftExcept (rand (concl th1))
    let th2 ← ExceptT.mk (NUM_MULT_CONV K P mk_numeral (← liftExcept (do (← mk_binop K.mul_tm tm0) tm1)))
    let tm2 ← liftExcept (rand (concl th2))
    let pth ← INST [(tmx, N.x_tm), (tm0, N.y_tm), (tm1, N.w_tm), (tm2, N.z_tm)] P.fact_pth_suc
    MP (← MP (← MP pth th0) th1) th2
  fun tm => ExceptT.run do
    try
      let (l, r) ← liftExcept (dest_comb tm)
      if (← liftExcept (dest_const l)).1 == "FACT"
      then NUM_FACT_CONV (← liftExcept (dest_numeral r))
      else throw ""
    catch _ => throw "NUM_FACT_CONV"

/- ---------------------------------------------------------------------- -/
/- NUM_MAX_CONV, NUM_MIN_CONV (calc_num.ml 1427-1435).                    -/
/- ---------------------------------------------------------------------- -/

/-- `NUM_MAX_CONV = REWR_CONV MAX THENC
    RATOR_CONV(RATOR_CONV(RAND_CONV NUM_LE_CONV)) THENC
    GEN_REWRITE_CONV I [COND_CLAUSES]`. -/
def NUM_MAX_CONV [HolBase] (N : CalcNumNets) (MAX : thm) (K : CalcNumConsts)
    (P : CalcNumProformas) : ioconv :=
  REWR_CONV MAX THENC
  RATOR_CONV (RATOR_CONV (RAND_CONV (NUM_LE_CONV K P))) THENC
  N.max_cond_conv

/-- `NUM_MIN_CONV`, likewise with `MIN`. -/
def NUM_MIN_CONV [HolBase] (N : CalcNumNets) (MIN : thm) (K : CalcNumConsts)
    (P : CalcNumProformas) : ioconv :=
  REWR_CONV MIN THENC
  RATOR_CONV (RATOR_CONV (RAND_CONV (NUM_LE_CONV K P))) THENC
  N.min_cond_conv

/-- `NUM_REDUCE_TAC = CONV_TAC NUM_REDUCE_CONV` (calc_num.ml 1495). -/
def NUM_REDUCE_TAC [HolBase] (NUM_REDUCE_CONV : ioconv) : tactic :=
  CONV_TAC NUM_REDUCE_CONV

/- ---------------------------------------------------------------------- -/
/- Expands "!n. n < numeral-constant ==> P(n)" into all the cases.        -/
/- ---------------------------------------------------------------------- -/

/-- `EXPAND_CASES_CONV` (calc_num.ml 1512-1526). -/
partial def EXPAND_CASES_CONV (N : CalcNumNets) (K : CalcNumConsts)
    (P : CalcNumProformas) (mk_numeral : Rat → Except String term) : ioconv :=
  let base_CONV := N.expand_base
  let step_CONV :=
    BINDER_CONV (LAND_CONV (RAND_CONV (num_CONV K P mk_numeral))) THENC N.expand_step
  let rec conv : ioconv := fun tm =>
    (base_CONV ORELSEC (step_CONV THENC LAND_CONV conv)) tm
  conv THENC N.expand_assoc

/- ---------------------------------------------------------------------- -/
/- Computation of (a EXP k) MOD n keeping intermediates reduced           -/
/- ---------------------------------------------------------------------- -/

/-- `EXP_MOD_CONV` (calc_num.ml 1531-1560). -/
partial def EXP_MOD_CONV (N : CalcNumNets)
    (NUM_EXP_CONV NUM_MULT_CONV NUM_MOD_CONV : ioconv) : ioconv :=
  let rec conv : ioconv := fun tm =>
    ((N.expmod_0 THENC NUM_MOD_CONV) ORELSEC
     (N.expmod_even THENC
      LAND_CONV (LAND_CONV conv THENC NUM_EXP_CONV) THENC
      NUM_MOD_CONV) ORELSEC
     (N.expmod_odd THENC
      LAND_CONV (RAND_CONV (LAND_CONV (LAND_CONV conv THENC NUM_EXP_CONV) THENC
                            NUM_MOD_CONV) THENC
                 NUM_MULT_CONV) THENC
      NUM_MOD_CONV)) tm
  let fullconv := (N.expmod_zero THENC NUM_EXP_CONV) ORELSEC conv
  fun tm =>
    match tm with
    | .Comb (.Comb (.Const "MOD" _) (.Comb (.Comb (.Const "EXP" _) m) k)) n =>
      if HolMath.Nums.is_numeral m && HolMath.Nums.is_numeral k &&
         HolMath.Nums.is_numeral n then fullconv tm
      else pure (failwith "EXP_MOD_CONV")
    | _ => pure (failwith "EXP_MOD_CONV")

end

end HolMath.CalcNum
