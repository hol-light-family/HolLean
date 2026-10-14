/- File: CalcRat.lean
Calculation with rational-valued reals.
Original       John Harrison, University of Cambridge Computer Laboratory
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Lean4 translation by Chris Walton 2026

Makes HOL Light's real arithmetic work over the rationals.  This file defines
`GEN_REAL_ARITH`, `REAL_ARITH` and `REAL_ARITH_TAC` for the last time (the
semiring normaliser is now instantiated with `is_ratconst` rather than
`is_realintconst`), and introduces `ASM_REAL_ARITH_TAC`.  Because OCaml shadows
and Lean cannot, these are the `3`-numbered versions (`GEN_REAL_ARITH3`,
`REAL_ARITH3`, `REAL_ARITH_TAC2`); `REAL_POLY_CONV` is likewise defined twice,
the second extending the first to `inv` and division. -/

import HolMath.Real
import HolMath.Base

namespace HolMath.CalcRat

set_option maxRecDepth 8000

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

/-- `DECIMAL` (calc_rat.ml 16-17). -/
@[nospecialize]
def setupDecimal [HolBase] (new_definition : term → IO (Except String thm)) :
    ExceptT String IO thm := do
  ExceptT.mk (new_definition (← q r"DECIMAL x y = &x / &y"))

end

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

/-- The five handy lemmas of calc_rat.ml 20-80 that every later rational
    conversion is built on, in OCaml source order. -/
structure RatLemmas where
  /-- `RAT_LEMMA1` (calc_rat.ml 23). -/
  RAT_LEMMA1 : thm
  /-- `RAT_LEMMA2` (calc_rat.ml 35). -/
  RAT_LEMMA2 : thm
  /-- `RAT_LEMMA3` (calc_rat.ml 43). -/
  RAT_LEMMA3 : thm
  /-- `RAT_LEMMA4` (calc_rat.ml 50). -/
  RAT_LEMMA4 : thm
  /-- `RAT_LEMMA5` (calc_rat.ml 74). -/
  RAT_LEMMA5 : thm
  deriving Inhabited

/-- calc_rat.ml 19-78: various handy lemmas.  `REAL_ARITH` is the version
    current at this point of the load (real.ml's). -/
@[nospecialize]
def setupRatLemmas [HolBase]
    (R : HolMath.RealAx.RealThms)
    (Ci : HolMath.CalcInt.CalcIntThms)
    (L : HolMath.RealArith.RealArithLemmas)
    (T1 : HolMath.Real.RealThms1)
    (T6 : HolMath.Real.RealThms6)
    (REAL_ARITH' : term → IO (Except String thm)) :
    ExceptT String IO RatLemmas := do
  let REAL_ARITH (t : term) : ExceptT String IO thm := REAL_ARITH' t
  let REAL_ARITH_TAC : tactic := CONV_TAC REAL_ARITH'
  let { REAL_MUL_ASSOC, REAL_LE_ANTISYM, REAL_LE_MUL, real_sub, real_div, .. } := R
  let { REAL_MUL_LNEG, .. } := Ci
  let { REAL_LT_IMP_LE, REAL_LT_REFL, REAL_MUL_RID, .. } := L
  let { REAL_MUL_AC, REAL_ADD_RDISTRIB, .. } := T1
  let { REAL_EQ_MUL_LCANCEL, REAL_LT_INV, REAL_LE_INV, REAL_MUL_RINV, .. } := T6
  let { EQ_TRANS, CONJ_SYM, .. } := HolBase.T
  let { DE_MORGAN_THM, CONTRAPOS_THM, .. } := HolBase.C

  /- Various handy lemmas. -/

  let RAT_LEMMA1 ← prove
   r"~(y1 = &0) /\ ~(y2 = &0) ==>
      ((x1 / y1) + (x2 / y2) = (x1 * y2 + x2 * y1) * inv(y1) * inv(y2))"
   (STRIP_TAC THEN REWRITE_TAC [real_div, REAL_ADD_RDISTRIB] THEN BINOP_TAC THENL
     [REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN ONCE_REWRITE_TAC
       [← AC REAL_MUL_AC (← q r"a * b * c = (b * a) * c")],
      REWRITE_TAC [REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_MUL_RID] THEN
    REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN REWRITE_TAC [REAL_EQ_MUL_LCANCEL] THEN
    DISJ2_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_MUL_RINV THEN
    ASM_REWRITE_TAC [])

  let RAT_LEMMA2 ← prove
   r"&0 < y1 /\ &0 < y2 ==>
      ((x1 / y1) + (x2 / y2) = (x1 * y2 + x2 * y1) * inv(y1) * inv(y2))"
   (DISCH_TAC THEN MATCH_MP_TAC RAT_LEMMA1 THEN POP_ASSUM MP_TAC THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC [DE_MORGAN_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [REAL_LT_REFL])

  let RAT_LEMMA3 ← prove
   r"&0 < y1 /\ &0 < y2 ==>
      ((x1 / y1) - (x2 / y2) = (x1 * y2 - x2 * y1) * inv(y1) * inv(y2))"
   (DISCH_THEN (fun th => tactic_of do
      pure (MP_TAC (← GEN_ALL (← MATCH_MP RAT_LEMMA2 th)))) THEN
    REWRITE_TAC [real_div] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC [real_sub, ← GSYM REAL_MUL_LNEG])

  let RAT_LEMMA4 ← do
    let lemma ← prove
     r"&0 < y ==> (&0 <= x * y <=> &0 <= x)"
     (DISCH_TAC THEN EQ_TAC THEN DISCH_TAC THENL
       [SUBGOAL_THEN (← q r"&0 <= x * (y * inv y)") MP_TAC THENL
         [REWRITE_TAC [REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL THEN
          ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LE_INV THEN
          MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC [],
          SUBGOAL_THEN (← q r"y * inv y = &1") (fun th =>
            REWRITE_TAC [th, REAL_MUL_RID]) THEN
          MATCH_MP_TAC REAL_MUL_RINV THEN
          UNDISCH_TAC (← q r"&0 < y") THEN REAL_ARITH_TAC],
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC []])
    prove
     r"&0 < y1 /\ &0 < y2 ==> (x1 / y1 <= x2 / y2 <=> x1 * y2 <= x2 * y1)"
     (ONCE_REWRITE_TAC [CONJ_SYM] THEN DISCH_TAC THEN
      ONCE_REWRITE_TAC [← REAL_ARITH (← q r"a <= b <=> &0 <= b - a")] THEN
      FIRST_ASSUM (fun th => tactic_of do
        pure (REWRITE_TAC [← MATCH_MP RAT_LEMMA3 th])) THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC (← q r"&0 <= (x2 * y1 - x1 * y2) * inv y2") THEN
      REWRITE_TAC [REAL_MUL_ASSOC] THEN CONJ_TAC THEN
      MATCH_MP_TAC lemma THEN MATCH_MP_TAC REAL_LT_INV THEN
      ASM_REWRITE_TAC [])

  let RAT_LEMMA5 ← prove
   r"&0 < y1 /\ &0 < y2 ==> ((x1 / y1 = x2 / y2) <=> (x1 * y2 = x2 * y1))"
   (REPEAT DISCH_TAC THEN REWRITE_TAC [← GSYM REAL_LE_ANTISYM] THEN
    MATCH_MP_TAC (← TAUT (← q r"(a <=> a') /\ (b <=> b') ==> (a /\ b <=> a' /\ b')")) THEN
    CONJ_TAC THEN MATCH_MP_TAC RAT_LEMMA4 THEN ASM_REWRITE_TAC [])

  return {
    RAT_LEMMA1, RAT_LEMMA2, RAT_LEMMA3, RAT_LEMMA4, RAT_LEMMA5 }

end

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

/-- `REAL_INT_RAT_CONV` (calc_rat.ml 84-92). -/
@[nospecialize]
def setupRealIntRatConv [HolBase] (DECIMAL : thm) (R : HolMath.RealAx.RealThms)
    (K : HolMath.CalcInt.CalcIntThms) (T6 : HolMath.Real.RealThms6) : ExceptT String IO ioconv := do
  let pth ← prove
   r"(&x = &x / &1) /\
     (--(&x) = --(&x) / &1) /\
     (DECIMAL x y = &x / &y) /\
     (--(DECIMAL x y) = --(&x) / &y)"
   (REWRITE_TAC [T6.REAL_DIV_1, DECIMAL] THEN
    REWRITE_TAC [R.real_div, K.REAL_MUL_LNEG])
  return TRY_CONV (← GEN_REWRITE_CONV_NET id [pth])

/-- `REAL_INT_RAT_CONV` and the relational conversions (calc_rat.ml 84-171). -/
structure RealRatRelConvs where
  REAL_INT_RAT_CONV : ioconv
  REAL_RAT_LE_CONV  : ioconv
  REAL_RAT_LT_CONV  : ioconv
  REAL_RAT_GE_CONV  : ioconv
  REAL_RAT_GT_CONV  : ioconv
  REAL_RAT_EQ_CONV  : ioconv
  REAL_RAT_SGN_CONV : ioconv
  deriving Inhabited

/- ---------------------------------------------------------------------- -/
/- Relational operations.                                                 -/
/- ---------------------------------------------------------------------- -/

/-- Build the relational conversions (calc_rat.ml 84-171). -/
@[nospecialize]
def setupRealRatRelConvs [HolBase] (Lm : RatLemmas) (DECIMAL : thm)
    (V : HolMath.CalcInt.RealIntCompareConvs) (W : HolMath.CalcInt.RealIntArithConvs)
    (R : HolMath.RealAx.RealThms) (K : HolMath.CalcInt.CalcIntThms)
    (T2 : HolMath.Real.RealThms2) (T6 : HolMath.Real.RealThms6)
    (T10 : HolMath.Real.RealThms10) : ExceptT String IO RealRatRelConvs := do
  let { IMP_IMP, .. } := HolBase.T
  let { COND_CLAUSES, .. } := HolBase.C
  let REAL_INT_RAT_CONV ← setupRealIntRatConv DECIMAL R K T6
  -- Each of LE, LT and EQ parses its own `x1`, `x2`, `y1`, `y2`, relation
  -- and `(/)` (calc_rat.ml 101-104, 122-125, 147-150), after its theorem.
  let vars (rel : String) : ExceptT String IO
      (term × term × term × term × (term → Except String (term × term)) ×
       (term → Except String (term × term))) := do
    let x1 ← q r"x1:real"
    let x2 ← q r"x2:real"
    let y1 ← q r"y1:real"
    let y2 ← q r"y2:real"
    let dest_rel := dest_binop (← q rel)
    let dest_div := dest_binop (← q r"(/)")
    return (x1, x2, y1, y2, dest_rel, dest_div)
  -- The RAW conversion shared by LE, LT and EQ (calc_rat.ml 103-112).
  let raw (v : term × term × term × term × (term → Except String (term × term)) ×
        (term → Except String (term × term))) (pth : thm) (FINAL : ioconv) :
      ioconv := fun tm => ExceptT.run do
    let (x1, x2, y1, y2, dest_rel, dest_div) := v
    let (l, r) ← liftExcept (dest_rel tm)
    let (lx, ly) ← liftExcept (dest_div l)
    let (rx, ry) ← liftExcept (dest_div r)
    let th0 ← INST [(lx, x1), (ly, y1), (rx, x2), (ry, y2)] pth
    let th1 ← MP_CONV V.REAL_INT_LT_CONV (← MP_CONV V.REAL_INT_LT_CONV th0)
    let th2 ← ExceptT.mk ((BINOP_CONV W.REAL_INT_MUL_CONV THENC FINAL)
      (← liftExcept (rand (concl th1))))
    TRANS th1 th2
  let le_pth ← prove
   r"&0 < y1 ==> &0 < y2 ==> (x1 / y1 <= x2 / y2 <=> x1 * y2 <= x2 * y1)"
   (REWRITE_TAC [IMP_IMP, Lm.RAT_LEMMA4])
  let REAL_RAT_LE_CONV := BINOP_CONV REAL_INT_RAT_CONV THENC
    raw (← vars r"(<=)") le_pth V.REAL_INT_LE_CONV
  let lt_pth ← prove
   r"&0 < y1 ==> &0 < y2 ==> (x1 / y1 < x2 / y2 <=> x1 * y2 < x2 * y1)"
   (REWRITE_TAC [IMP_IMP] THEN
    GEN_REWRITE_TAC (fun c => RAND_CONV (ONCE_DEPTH_CONV c)) [← GSYM T2.REAL_NOT_LE] THEN
    SIMP_TAC [← TAUT (← q r"(~a <=> ~b) <=> (a <=> b)"), Lm.RAT_LEMMA4])
  let REAL_RAT_LT_CONV := BINOP_CONV REAL_INT_RAT_CONV THENC
    raw (← vars r"(<)") lt_pth V.REAL_INT_LT_CONV
  let REAL_RAT_GE_CONV := (← GEN_REWRITE_CONV_NET id [R.real_ge]) THENC REAL_RAT_LE_CONV
  let REAL_RAT_GT_CONV := (← GEN_REWRITE_CONV_NET id [R.real_gt]) THENC REAL_RAT_LT_CONV
  let eq_pth ← prove
   r"&0 < y1 ==> &0 < y2 ==> ((x1 / y1 = x2 / y2) <=> (x1 * y2 = x2 * y1))"
   (REWRITE_TAC [IMP_IMP, Lm.RAT_LEMMA5])
  let REAL_RAT_EQ_CONV := BINOP_CONV REAL_INT_RAT_CONV THENC
    raw (← vars r"(=) :real->real->bool") eq_pth V.REAL_INT_EQ_CONV
  let condAll ← SPEC_ALL COND_CLAUSES
  let REAL_RAT_SGN_CONV :=
    (← GEN_REWRITE_CONV_NET id [T10.real_sgn]) THENC
    RATOR_CONV (LAND_CONV REAL_RAT_LT_CONV) THENC
    ((← GEN_REWRITE_CONV_NET id [← CONJUNCT1 condAll]) ORELSEC
     ((← GEN_REWRITE_CONV_NET id [← CONJUNCT2 condAll]) THENC
      RATOR_CONV (LAND_CONV REAL_RAT_LT_CONV) THENC
      (← GEN_REWRITE_CONV_NET id [COND_CLAUSES])))
  return { REAL_INT_RAT_CONV, REAL_RAT_LE_CONV, REAL_RAT_LT_CONV, REAL_RAT_GE_CONV,
           REAL_RAT_GT_CONV, REAL_RAT_EQ_CONV, REAL_RAT_SGN_CONV }

/-- `REAL_RAT_NEG_CONV`, `REAL_RAT_ABS_CONV`, `REAL_RAT_INV_CONV`
    (calc_rat.ml 175-229). -/
structure RealRatUnaryConvs where
  REAL_RAT_NEG_CONV : ioconv
  REAL_RAT_ABS_CONV : ioconv
  REAL_RAT_INV_CONV : ioconv
  deriving Inhabited

/-- Build the unary conversions (calc_rat.ml 175-229). -/
@[nospecialize]
def setupRealRatUnaryConvs [HolBase] (DECIMAL : thm) (R : HolMath.RealAx.RealThms)
    (K : HolMath.CalcInt.CalcIntThms) (L : HolMath.RealArith.RealArithLemmas)
    (T1 : HolMath.Real.RealThms1) (T6 : HolMath.Real.RealThms6) :
    ExceptT String IO RealRatUnaryConvs := do
  let pth ← prove
   r"(--(&0) = &0) /\
     (--(--(&n)) = &n) /\
     (--(&m / &n) = --(&m) / &n) /\
     (--(--(&m) / &n) = &m / &n) /\
     (--(DECIMAL m n) = --(&m) / &n)"
   (REWRITE_TAC [R.real_div, T6.REAL_INV_NEG, K.REAL_MUL_LNEG, K.REAL_NEG_NEG,
     K.REAL_NEG_0, DECIMAL])
  let ptm ← q r"(--)"
  let conv1 ← GEN_REWRITE_CONV_NET id [pth]
  let REAL_RAT_NEG_CONV : ioconv := fun tm => ExceptT.run do
    tryWith (ExceptT.mk (conv1 tm)) <|
    tryWith (do
        let (l, r) ← liftExcept (dest_comb tm)
        if l == ptm && HolMath.CalcInt.is_realintconst r then
          if (← liftExcept (HolMath.CalcInt.dest_realintconst r)) > num_0
          then return REFL tm
          else throw ""
        else throw "")
      (throw "REAL_RAT_NEG_CONV")
  let pth ← prove
   r"(abs(&n) = &n) /\
     (abs(--(&n)) = &n) /\
     (abs(&m / &n) = &m / &n) /\
     (abs(--(&m) / &n) = &m / &n) /\
     (abs(DECIMAL m n) = &m / &n) /\
     (abs(--(DECIMAL m n)) = &m / &n)"
   (REWRITE_TAC [DECIMAL, T6.REAL_ABS_DIV, K.REAL_ABS_NEG, K.REAL_ABS_NUM])
  let REAL_RAT_ABS_CONV ← GEN_REWRITE_CONV_NET id [pth]
  let pth1 ← prove
   r"(inv(&0) = &0) /\
     (inv(&1) = &1) /\
     (inv(-- &1) = --(&1)) /\
     (inv(&1 / &n) = &n) /\
     (inv(-- &1 / &n) = -- &n)"
   (REWRITE_TAC [R.REAL_INV_0, T6.REAL_INV_1, T6.REAL_INV_NEG,
                 T6.REAL_INV_DIV, T6.REAL_DIV_1] THEN
    REWRITE_TAC [R.real_div, T6.REAL_INV_NEG, K.REAL_MUL_RNEG, T6.REAL_INV_1,
                 L.REAL_MUL_RID])
  let pth2 ← prove
   r"(inv(&n) = &1 / &n) /\
     (inv(--(&n)) = --(&1) / &n) /\
     (inv(&m / &n) = &n / &m) /\
     (inv(--(&m) / &n) = --(&n) / &m) /\
     (inv(DECIMAL m n) = &n / &m) /\
     (inv(--(DECIMAL m n)) = --(&n) / &m)"
   (REWRITE_TAC [DECIMAL, T6.REAL_INV_DIV] THEN
    REWRITE_TAC [T6.REAL_INV_NEG, R.real_div, K.REAL_MUL_RNEG, T1.REAL_MUL_AC,
      R.REAL_MUL_LID, K.REAL_MUL_LNEG, T6.REAL_INV_MUL, T6.REAL_INV_INV])
  let REAL_RAT_INV_CONV := (← GEN_REWRITE_CONV_NET id [pth1]) ORELSEC
                           (← GEN_REWRITE_CONV_NET id [pth2])
  return { REAL_RAT_NEG_CONV, REAL_RAT_ABS_CONV, REAL_RAT_INV_CONV }

/-- `REAL_RAT_ADD_CONV`, `REAL_RAT_SUB_CONV`, `REAL_RAT_MUL_CONV`,
    `REAL_RAT_DIV_CONV` (calc_rat.ml 233-358). -/
structure RealRatArithConvs where
  REAL_RAT_ADD_CONV : ioconv
  REAL_RAT_SUB_CONV : ioconv
  REAL_RAT_MUL_CONV : ioconv
  REAL_RAT_DIV_CONV : ioconv
  deriving Inhabited

/-- Build the arithmetic conversions (calc_rat.ml 233-358).  `REAL_INT_REDUCE_CONV`
    is calc_int.ml's. -/
@[nospecialize]
def setupRealRatArithConvs [HolBase] (Lm : RatLemmas) (Rl : RealRatRelConvs)
    (U : RealRatUnaryConvs) (V : HolMath.CalcInt.RealIntCompareConvs)
    (W : HolMath.CalcInt.RealIntArithConvs) (S : HolMath.CalcInt.RatSyntax)
    (R : HolMath.RealAx.RealThms) (L : HolMath.RealArith.RealArithLemmas)
    (T1 : HolMath.Real.RealThms1) (T6 : HolMath.Real.RealThms6)
    (REAL_INT_REDUCE_CONV : ioconv) : ExceptT String IO RealRatArithConvs := do
  let mkI (x : Rat) : ExceptT String IO term := liftExcept (HolMath.CalcInt.mk_realintconst S x)
  let dI (t : term) : ExceptT String IO Rat := liftExcept (HolMath.CalcInt.dest_realintconst t)
  let divOne ← GEN_REWRITE_CONV_NET id [T6.REAL_DIV_1]
  -- REAL_RAT_ADD_CONV (calc_rat.ml 233-277).
  let pth ← prove
   r"&0 < y1 ==> &0 < y2 ==> &0 < y3 ==>
     ((x1 * y2 + x2 * y1) * y3 = x3 * y1 * y2)
     ==> (x1 / y1 + x2 / y2 = x3 / y3)"
   (REPEAT DISCH_TAC THEN
    MP_TAC Lm.RAT_LEMMA2 THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [← GSYM T6.REAL_INV_MUL, ← GSYM R.real_div] THEN
    SUBGOAL_THEN (← q r"&0 < y1 * y2 /\ &0 < y3") MP_TAC THENL
     [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC T1.REAL_LT_MUL THEN
      ASM_REWRITE_TAC [],
      DISCH_THEN (fun th => tactic_of do
        pure (ASM_REWRITE_TAC [← MATCH_MP Lm.RAT_LEMMA5 th]))])
  let dest_divop := dest_binop (← q r"(/)")
  let dest_addop := dest_binop (← q r"(+)")
  let x1 ← q r"x1:real"
  let x2 ← q r"x2:real"
  let x3 ← q r"x3:real"
  let y1 ← q r"y1:real"
  let y2 ← q r"y2:real"
  let y3 ← q r"y3:real"
  -- Addition.
  let RAW_REAL_RAT_ADD_CONV : ioconv := fun tm => ExceptT.run do
    let (r1, r2) ← liftExcept (dest_addop tm)
    let (x1', y1') ← liftExcept (dest_divop r1)
    let (x2', y2') ← liftExcept (dest_divop r2)
    let x1n ← dI x1'
    let y1n ← dI y1'
    let x2n ← dI x2'
    let y2n ← dI y2'
    let x3n := x1n * y2n + x2n * y1n
    let y3n := y1n * y2n
    let d := gcd_num x3n y3n
    let x3n' := quo_num x3n d
    let y3n' := quo_num y3n d
    let (x3n'', y3n'') := if y3n' > num_0 then (x3n', y3n') else (-x3n', -y3n')
    let x3' ← mkI x3n''
    let y3' ← mkI y3n''
    let th0 ← INST [(x1', x1), (y1', y1), (x2', x2), (y2', y2), (x3', x3), (y3', y3)] pth
    let th1 ← MP_CONV V.REAL_INT_LT_CONV (← MP_CONV V.REAL_INT_LT_CONV
      (← MP_CONV V.REAL_INT_LT_CONV th0))
    let (tm2, tm3) ← liftExcept (do dest_eq (← dest_imp (concl th1)).1)
    let th2 ← ExceptT.mk ((LAND_CONV (BINOP_CONV W.REAL_INT_MUL_CONV THENC W.REAL_INT_ADD_CONV)
      THENC W.REAL_INT_MUL_CONV) tm2)
    let th3 ← ExceptT.mk ((RAND_CONV W.REAL_INT_MUL_CONV THENC W.REAL_INT_MUL_CONV) tm3)
    MP th1 (← TRANS th2 (← SYM th3))
  let REAL_RAT_ADD_CONV := BINOP_CONV Rl.REAL_INT_RAT_CONV THENC
    RAW_REAL_RAT_ADD_CONV THENC TRY_CONV divOne
  -- Subtraction.
  let pth ← prove r"x - y = x + --y" (REWRITE_TAC [R.real_sub])
  let REAL_RAT_SUB_CONV := (← GEN_REWRITE_CONV_NET id [pth]) THENC
    RAND_CONV U.REAL_RAT_NEG_CONV THENC REAL_RAT_ADD_CONV
  -- REAL_RAT_MUL_CONV (calc_rat.ml 290-349).
  let pth_nocancel ← prove
   r"(x1 / y1) * (x2 / y2) = (x1 * x2) / (y1 * y2)"
   (REWRITE_TAC [R.real_div, T6.REAL_INV_MUL, T1.REAL_MUL_AC])
  let pth_cancel ← prove
   r"~(d1 = &0) /\ ~(d2 = &0) /\
     (d1 * u1 = x1) /\ (d2 * u2 = x2) /\
     (d2 * v1 = y1) /\ (d1 * v2 = y2)
     ==> ((x1 / y1) * (x2 / y2) = (u1 * u2) / (v1 * v2))"
   (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
    ASM_REWRITE_TAC [R.real_div, T6.REAL_INV_MUL] THEN
    ONCE_REWRITE_TAC [← AC T1.REAL_MUL_AC
     (← q r"((d1 * u1) * (id2 * iv1)) * ((d2 * u2) * id1 * iv2) =
      (u1 * u2) * (iv1 * iv2) * (id2 * d2) * (id1 * d1)")] THEN
    ASM_SIMP_TAC [R.REAL_MUL_LINV, L.REAL_MUL_RID])
  -- calc_rat.ml 307-312: the MUL conversion parses its own `(/)`, `x1`,
  -- `x2`, `y1`, `y2` (equal to the ADD conversion's).
  let dest_divop := dest_binop (← q r"(/)")
  let dest_mulop := dest_binop (← q r"(*)")
  let x1 ← q r"x1:real"
  let x2 ← q r"x2:real"
  let y1 ← q r"y1:real"
  let y2 ← q r"y2:real"
  let u1 ← q r"u1:real"
  let u2 ← q r"u2:real"
  let v1 ← q r"v1:real"
  let v2 ← q r"v2:real"
  let d1 ← q r"d1:real"
  let d2 ← q r"d2:real"
  -- Multiplication.
  let RAW_REAL_RAT_MUL_CONV : ioconv := fun tm => ExceptT.run do
    let (r1, r2) ← liftExcept (dest_mulop tm)
    let (x1', y1') ← liftExcept (dest_divop r1)
    let (x2', y2') ← liftExcept (dest_divop r2)
    let x1n ← dI x1'
    let y1n ← dI y1'
    let x2n ← dI x2'
    let y2n ← dI y2'
    let d1n := gcd_num x1n y2n
    let d2n := gcd_num x2n y1n
    if d1n == num_1 && d2n == num_1 then
      let th0 ← INST [(x1', x1), (y1', y1), (x2', x2), (y2', y2)] pth_nocancel
      let th1 ← ExceptT.mk (BINOP_CONV W.REAL_INT_MUL_CONV (← liftExcept (rand (concl th0))))
      TRANS th0 th1
    else
      let u1' ← mkI (quo_num x1n d1n)
      let u2' ← mkI (quo_num x2n d2n)
      let v1' ← mkI (quo_num y1n d2n)
      let v2' ← mkI (quo_num y2n d1n)
      let d1' ← mkI d1n
      let d2' ← mkI d2n
      let th0 ← INST [(x1', x1), (y1', y1), (x2', x2), (y2', y2),
                      (u1', u1), (v1', v1), (u2', u2), (v2', v2), (d1', d1), (d2', d2)] pth_cancel
      let th1 ← EQT_ELIM (← ExceptT.mk (REAL_INT_REDUCE_CONV (← liftExcept (lhand (concl th0)))))
      let th2 ← MP th0 th1
      let th3 ← ExceptT.mk (BINOP_CONV W.REAL_INT_MUL_CONV (← liftExcept (rand (concl th2))))
      TRANS th2 th3
  let REAL_RAT_MUL_CONV := BINOP_CONV Rl.REAL_INT_RAT_CONV THENC
    RAW_REAL_RAT_MUL_CONV THENC TRY_CONV divOne
  -- REAL_RAT_DIV_CONV (calc_rat.ml 351-356).
  let pth ← prove r"x / y = x * inv(y)" (REWRITE_TAC [R.real_div])
  let REAL_RAT_DIV_CONV := (← GEN_REWRITE_CONV_NET id [pth]) THENC
    RAND_CONV U.REAL_RAT_INV_CONV THENC REAL_RAT_MUL_CONV
  return { REAL_RAT_ADD_CONV, REAL_RAT_SUB_CONV, REAL_RAT_MUL_CONV, REAL_RAT_DIV_CONV }

/-- `REAL_RAT_POW_CONV`, `REAL_RAT_MAX_CONV`, `REAL_RAT_MIN_CONV`
    (calc_rat.ml 362-385). -/
structure RealRatPowMaxMinConvs where
  REAL_RAT_POW_CONV : ioconv
  REAL_RAT_MAX_CONV : ioconv
  REAL_RAT_MIN_CONV : ioconv
  deriving Inhabited

/- ---------------------------------------------------------------------- -/
/- Powers.                                                                -/
/- ---------------------------------------------------------------------- -/

/-- Build the power, max and min conversions (calc_rat.ml 362-385). -/
@[nospecialize]
def setupRealRatPowMaxMinConvs [HolBase] (Rl : RealRatRelConvs)
    (W : HolMath.CalcInt.RealIntArithConvs) (R : HolMath.RealAx.RealThms)
    (T6 : HolMath.Real.RealThms6) : ExceptT String IO RealRatPowMaxMinConvs := do
  let { COND_CLAUSES, .. } := HolBase.C
  let pth ← prove r"(x / y) pow n = (x pow n) / (y pow n)" (REWRITE_TAC [T6.REAL_POW_DIV])
  let REAL_RAT_POW_CONV := W.REAL_INT_POW_CONV ORELSEC
    (LAND_CONV Rl.REAL_INT_RAT_CONV THENC
     (← GEN_REWRITE_CONV_NET id [pth]) THENC
     BINOP_CONV W.REAL_INT_POW_CONV)
  let condConv ← GEN_REWRITE_CONV_NET id [COND_CLAUSES]
  let REAL_RAT_MAX_CONV := REWR_CONV R.real_max THENC
    RATOR_CONV (RATOR_CONV (RAND_CONV Rl.REAL_RAT_LE_CONV)) THENC condConv
  let condConv ← GEN_REWRITE_CONV_NET id [COND_CLAUSES]
  let REAL_RAT_MIN_CONV := REWR_CONV R.real_min THENC
    RATOR_CONV (RATOR_CONV (RAND_CONV Rl.REAL_RAT_LE_CONV)) THENC condConv
  return { REAL_RAT_POW_CONV, REAL_RAT_MAX_CONV, REAL_RAT_MIN_CONV }

/- ---------------------------------------------------------------------- -/
/- Everything.                                                            -/
/- ---------------------------------------------------------------------- -/

/-- `real_rat_red_conv_list` (calc_rat.ml 389-405).  OCaml evaluates the list
    literal last element first, so the patterns are parsed in that order. -/
def real_rat_red_conv_list [HolBase] (Rl : RealRatRelConvs) (U : RealRatUnaryConvs)
    (A : RealRatArithConvs) (P : RealRatPowMaxMinConvs) :
    ExceptT String IO (List (term × ioconv)) := do
  let mn ← q r"min x y"
  let mx ← q r"max x y"
  let pw ← q r"x pow n"
  let dv ← q r"x / y"
  let ml ← q r"x * y"
  let sb ← q r"x - y"
  let ad ← q r"x + y"
  let iv ← q r"inv(x)"
  let ab ← q r"abs(x)"
  let sg ← q r"real_sgn(x)"
  let ng ← q r"--x"
  let eq ← q r"x:real = y"
  let gt ← q r"x > y"
  let ge ← q r"x >= y"
  let lt ← q r"x < y"
  let le ← q r"x <= y"
  return [(le, Rl.REAL_RAT_LE_CONV),
          (lt, Rl.REAL_RAT_LT_CONV),
          (ge, Rl.REAL_RAT_GE_CONV),
          (gt, Rl.REAL_RAT_GT_CONV),
          (eq, Rl.REAL_RAT_EQ_CONV),
          (ng, CHANGED_CONV U.REAL_RAT_NEG_CONV),
          (sg, Rl.REAL_RAT_SGN_CONV),
          (ab, U.REAL_RAT_ABS_CONV),
          (iv, U.REAL_RAT_INV_CONV),
          (ad, A.REAL_RAT_ADD_CONV),
          (sb, A.REAL_RAT_SUB_CONV),
          (ml, A.REAL_RAT_MUL_CONV),
          (dv, CHANGED_CONV A.REAL_RAT_DIV_CONV),
          (pw, P.REAL_RAT_POW_CONV),
          (mx, P.REAL_RAT_MAX_CONV),
          (mn, P.REAL_RAT_MIN_CONV)]

/-- `REAL_RAT_RED_CONV` (calc_rat.ml 407-410): the net is built from
    `basic_net()` as it is now. -/
def REAL_RAT_RED_CONV (cl : List (term × ioconv)) : ExceptT String IO ioconv :=
  HolMath.CalcInt.REAL_INT_RED_CONV cl

/-- `real_rat_compute_add_convs` (calc_rat.ml 414-419). -/
def real_rat_compute_add_convs (cl : List (term × ioconv)) (cs : HolMath.Compute.compset) :
    ExceptT String IO Unit :=
  HolMath.CalcInt.real_int_compute_add_convs cl cs

/-- `REAL_RAT_COMPUTE_CONV` (calc_rat.ml 421-425). -/
def REAL_RAT_COMPUTE_CONV [HolBase] (cl : List (term × ioconv))
    (bool_compset : IO (Except String HolMath.Compute.compset))
    (WEAK_CBV_CONV : HolMath.Compute.compset → ioconv) : ExceptT String IO ioconv :=
  HolMath.CalcInt.REAL_INT_COMPUTE_CONV cl bool_compset WEAK_CBV_CONV

/-- The first rational normaliser's six conversions (calc_rat.ml 431-438).
    Only `REAL_POLY_CONV` is redefined afterwards (calc_rat.ml 443). -/
structure RealPolyConvs1 where
  polys : HolMath.Normalizer.PolynomialConvs

/-- Build `RealPolyConvs1` (calc_rat.ml 431-438). -/
@[nospecialize]
def setupRealPolyConvs1 [HolBase] (L : HolMath.RealArith.RealArithLemmas)
    (A : RealRatArithConvs) (P : RealRatPowMaxMinConvs)
    (TRUTH SEMIRING_PTHS : thm) (num_CONV : term → IO (Except String thm))
    (NUM_ADD_CONV NUM_SUC_CONV NUM_MULT_CONV : ioconv) : ExceptT String IO RealPolyConvs1 := do
  let sctx ← HolMath.Normalizer.setupSemiringCtx TRUTH SEMIRING_PTHS
    L.REAL_POLY_CLAUSES L.REAL_POLY_NEG_CLAUSES HolMath.CalcInt.is_ratconst
    A.REAL_RAT_ADD_CONV A.REAL_RAT_MUL_CONV P.REAL_RAT_POW_CONV HolMath.RealArith.term_lt
  let polys := HolMath.Normalizer.SEMIRING_NORMALIZERS_CONV sctx
    NUM_ADD_CONV NUM_SUC_CONV NUM_MULT_CONV num_CONV
  return { polys }

/-- What the redefined `REAL_POLY_CONV` binds before its `let rec`
    (calc_rat.ml 444-454), with the conversions it calls. -/
structure RealPolyConv2Env where
  neg_tm : term
  inv_tm : term
  add_tm : term
  sub_tm : term
  mul_tm : term
  div_tm : term
  pow_tm : term
  abs_tm : term
  max_tm : term
  min_tm : term
  div_conv : ioconv
  P : HolMath.Normalizer.PolynomialConvs
  REAL_RAT_INV_CONV : ioconv

/-- The `let rec REAL_POLY_CONV tm` of calc_rat.ml 455-485. -/
partial def REAL_POLY_CONV2_rec [HolBase] (E : RealPolyConv2Env) : ioconv := fun tm => ExceptT.run do
  let REAL_POLY_CONV := REAL_POLY_CONV2_rec E
  let P := E.P
  if !(is_comb tm) || HolMath.CalcInt.is_ratconst tm then return REFL tm
  let (lop, r) ← liftExcept (dest_comb tm)
  if lop == E.neg_tm then
    let th1 ← AP_TERM lop (← ExceptT.mk (REAL_POLY_CONV r))
    TRANS th1 (← ExceptT.mk (P.POLYNOMIAL_NEG_CONV (← liftExcept (rand (concl th1)))))
  else if lop == E.inv_tm then
    let th1 ← AP_TERM lop (← ExceptT.mk (REAL_POLY_CONV r))
    TRANS th1 (← ExceptT.mk (TRY_CONV E.REAL_RAT_INV_CONV (← liftExcept (rand (concl th1)))))
  else if lop == E.abs_tm then
    AP_TERM lop (← ExceptT.mk (REAL_POLY_CONV r))
  else if !(is_comb lop) then return REFL tm
  else
  let (op, l) ← liftExcept (dest_comb lop)
  if op == E.pow_tm then
    let th1 ← AP_THM (← AP_TERM op (← ExceptT.mk (REAL_POLY_CONV l))) r
    TRANS th1 (← ExceptT.mk (TRY_CONV P.POLYNOMIAL_POW_CONV (← liftExcept (rand (concl th1)))))
  else if op == E.add_tm || op == E.mul_tm || op == E.sub_tm then
    let thr ← ExceptT.mk (REAL_POLY_CONV r)
    let th1 ← MK_COMB (← AP_TERM op (← ExceptT.mk (REAL_POLY_CONV l)), thr)
    let fn := if op == E.add_tm then P.POLYNOMIAL_ADD_CONV
              else if op == E.mul_tm then P.POLYNOMIAL_MUL_CONV
              else P.POLYNOMIAL_SUB_CONV
    TRANS th1 (← ExceptT.mk (fn (← liftExcept (rand (concl th1)))))
  else if op == E.div_tm then
    let th1 ← ExceptT.mk (E.div_conv tm)
    TRANS th1 (← ExceptT.mk (REAL_POLY_CONV (← liftExcept (rand (concl th1)))))
  else if op == E.min_tm || op == E.max_tm then
    let thr ← ExceptT.mk (REAL_POLY_CONV r)
    MK_COMB (← AP_TERM op (← ExceptT.mk (REAL_POLY_CONV l)), thr)
  else return REFL tm

/-- The redefined `REAL_POLY_CONV` (calc_rat.ml 443-486). -/
@[nospecialize]
def setupRealPolyConv2 [HolBase] (R : HolMath.RealAx.RealThms) (U : RealRatUnaryConvs)
    (Q1 : RealPolyConvs1) : ExceptT String IO ioconv := do
  let neg_tm ← q r"(--):real->real"
  let inv_tm ← q r"inv:real->real"
  let add_tm ← q r"(+):real->real->real"
  let sub_tm ← q r"(-):real->real->real"
  let mul_tm ← q r"(*):real->real->real"
  let div_tm ← q r"(/):real->real->real"
  let pow_tm ← q r"(pow):real->num->real"
  let abs_tm ← q r"abs:real->real"
  let max_tm ← q r"max:real->real->real"
  let min_tm ← q r"min:real->real->real"
  let div_conv := REWR_CONV R.real_div
  let P := Q1.polys
  let REAL_RAT_INV_CONV := U.REAL_RAT_INV_CONV
  let E : RealPolyConv2Env :=
    { neg_tm := neg_tm, inv_tm := inv_tm, add_tm := add_tm, sub_tm := sub_tm,
      mul_tm := mul_tm, div_tm := div_tm, pow_tm := pow_tm, abs_tm := abs_tm,
      max_tm := max_tm, min_tm := min_tm, div_conv := div_conv, P := P,
      REAL_RAT_INV_CONV := REAL_RAT_INV_CONV }
  return REAL_POLY_CONV2_rec E

/-- `REAL_RING`, `real_ideal_cofactors` (calc_rat.ml 490-518) and
    `REAL_IDEAL_CONV` (calc_rat.ml 524-531). -/
structure RealRingConvs where
  /-- `REAL_INTEGRAL` (calc_rat.ml 491). -/
  REAL_INTEGRAL : thm
  /-- `REAL_RABINOWITSCH` (calc_rat.ml 500). -/
  REAL_RABINOWITSCH : thm
  REAL_RING : term → IO (Except String thm)
  real_ideal_cofactors : List term → term → IO (Except String (List term))
  REAL_IDEAL_CONV : List term → term → IO (Except String thm)

/-- Build `RealRingConvs` (calc_rat.ml 490-531).  `REAL_ARITH` is
    realarith.ml's second `REAL_ARITH`, the one in scope here. -/
@[nospecialize]
def setupRealRing [HolBase] (S : HolMath.CalcInt.RatSyntax) (Rl : RealRatRelConvs)
    (REAL_POLY_CONV : ioconv) (DECIMAL : thm) (Nm : HolMath.Nums.NumeralConsts)
    (MULT_CLAUSES EQ_ADD_LCANCEL REAL_OF_NUM_EQ REAL_OF_NUM_ADD REAL_OF_NUM_MUL
     REAL_SUB_0 REAL_ENTIRE REAL_MUL_RINV REAL_MUL_LZERO : thm)
    (REAL_ARITH : ioconv) (MESON_TAC : List thm → tactic)
    (PRESIMP_CONV CONDS_ELIM_CONV NNF_CONV WEAK_DNF_CONV : ioconv)
    (AND_FORALL_THM LEFT_AND_FORALL_THM RIGHT_AND_FORALL_THM
     LEFT_OR_FORALL_THM RIGHT_OR_FORALL_THM OR_EXISTS_THM
     LEFT_OR_EXISTS_THM RIGHT_OR_EXISTS_THM LEFT_AND_EXISTS_THM
     RIGHT_AND_EXISTS_THM : thm)
    (G : HolMath.Grobner.GrobnerGlobals) (TRUTH : thm) : ExceptT String IO RealRingConvs := do
  let REAL_ARITH_TAC := CONV_TAC REAL_ARITH
  let REAL_INTEGRAL ← prove
   r"(!x. &0 * x = &0) /\
     (!x y z. (x + y = x + z) <=> (y = z)) /\
     (!w x y z. (w * y + x * z = w * z + x * y) <=> (w = x) \/ (y = z))"
   (REWRITE_TAC [MULT_CLAUSES, EQ_ADD_LCANCEL] THEN
    REWRITE_TAC [← GSYM REAL_OF_NUM_EQ,
                 ← GSYM REAL_OF_NUM_ADD, ← GSYM REAL_OF_NUM_MUL] THEN
    ONCE_REWRITE_TAC [← GSYM REAL_SUB_0] THEN
    REWRITE_TAC [← GSYM REAL_ENTIRE] THEN REAL_ARITH_TAC)
  let REAL_RABINOWITSCH ← prove
   r"!x y:real. ~(x = y) <=> ?z. (x - y) * z = &1"
   (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (fun c => LAND_CONV (RAND_CONV c)) [← GSYM REAL_SUB_0] THEN
    MESON_TAC [REAL_MUL_RINV, REAL_MUL_LZERO,
               ← ExceptT.mk (REAL_ARITH (← q r"~(&1 = &0)"))])
  let init ← GEN_REWRITE_CONV_NET ONCE_DEPTH_CONV [DECIMAL]
  let real_ty ← qty r"real"
  let neg_tm ← q r"(--):real->real"
  let add_tm ← q r"(+):real->real->real"
  let sub_tm ← q r"(-):real->real->real"
  let inv_tm ← q r"(inv):real->real"
  let mul_tm ← q r"(*):real->real->real"
  let div_tm ← q r"(/):real->real->real"
  let pow_tm ← q r"(pow):real->num->real"
  let K : HolMath.Grobner.RingParms :=
    { ring_dest_const     := HolMath.CalcInt.rat_of_term
      ring_mk_const       := HolMath.CalcInt.term_of_rat S
      RING_EQ_CONV        := Rl.REAL_RAT_EQ_CONV
      ring_neg_tm         := neg_tm
      ring_add_tm         := add_tm
      ring_sub_tm         := sub_tm
      ring_inv_tm         := inv_tm
      ring_mul_tm         := mul_tm
      ring_div_tm         := div_tm
      ring_pow_tm         := pow_tm
      RING_INTEGRAL       := REAL_INTEGRAL
      RABINOWITSCH_THM    := REAL_RABINOWITSCH
      RING_NORMALIZE_CONV := REAL_POLY_CONV }
  let R ← HolMath.Grobner.setupRingCtx G Nm (concl TRUTH)
    PRESIMP_CONV CONDS_ELIM_CONV NNF_CONV WEAK_DNF_CONV
    AND_FORALL_THM LEFT_AND_FORALL_THM RIGHT_AND_FORALL_THM
    LEFT_OR_FORALL_THM RIGHT_OR_FORALL_THM OR_EXISTS_THM
    LEFT_OR_EXISTS_THM RIGHT_OR_EXISTS_THM LEFT_AND_EXISTS_THM RIGHT_AND_EXISTS_THM K
  let pure_ := HolMath.Grobner.RING' R
  let REAL_RING : ioconv := fun tm => ExceptT.run do
    let th ← ExceptT.mk (init tm)
    EQ_MP (← SYM th) (← ExceptT.mk (pure_ (← liftExcept (rand (concl th)))))
  let real_ideal_cofactors (tms : List term) (tm : term) : IO (Except String (List term)) :=
    if (tm :: tms).all (fun t => type_of t == real_ty) then HolMath.Grobner.ideal_cofactors R tms tm
    else pure (.error "real_ideal_cofactors: not all terms have type :real")
  -- REAL_IDEAL_CONV (calc_rat.ml 524-531).
  let mk_add := mk_binop (← q r"( + ):real->real->real")
  let mk_mul := mk_binop (← q r"( * ):real->real->real")
  let REAL_IDEAL_CONV (tms : List term) (tm : term) : IO (Except String thm) := ExceptT.run do
    let cfs ← ExceptT.mk (real_ideal_cofactors tms tm)
    let tm' ← liftExcept (do
      let prods ← (← map2 (fun c t => (c, t)) cfs tms).mapM (fun (c, t) => do (← mk_mul c) t)
      end_itlistM (fun a b => do (← mk_add a) b) prods)
    let th ← ExceptT.mk (REAL_POLY_CONV tm)
    let th' ← ExceptT.mk (REAL_POLY_CONV tm')
    TRANS th (← SYM th')
  return { REAL_INTEGRAL, REAL_RABINOWITSCH, REAL_RING, real_ideal_cofactors, REAL_IDEAL_CONV }

/-- `GEN_REAL_ARITH`, `REAL_ARITH`, `REAL_ARITH_TAC` and `ASM_REAL_ARITH_TAC`,
    the final versions (calc_rat.ml 537-559). -/
structure FinalRealArith where
  GEN_REAL_ARITH3 : HolMath.RealArith.PsProver → term → IO (Except String thm)
  REAL_ARITH3 : term → IO (Except String thm)
  REAL_ARITH_TAC2 : tactic
  ASM_REAL_ARITH_TAC : tactic

/-- Build `FinalRealArith` (calc_rat.ml 537-559).  `GEN_REAL_ARITH PROVER`
    builds the procedure each time it is applied, as in OCaml;
    `REAL_ARITH`'s `pure` is built once. -/
@[nospecialize]
def setupFinalRealArith [HolBase] (P : HolCore.Canon.NNFPths)
    (G : HolMath.RealArith.GenRealArith1Ctx) (G2 : HolMath.RealArith.GenRealArith2Ctx)
    (PRESIMP_CONV NNF_CONV CONDS_ELIM_CONV SKOLEM_CONV PRENEX_CONV WEAK_DNF_CONV : ioconv)
    (S : HolMath.CalcInt.RatSyntax) (Rl : RealRatRelConvs) (Q1 : RealPolyConvs1)
    (REAL_POLY_CONV : ioconv) (DECIMAL : thm) (REAL_LINEAR_PROVER : HolMath.RealArith.PsProver) :
    ExceptT String IO FinalRealArith := do
  let GEN_REAL_ARITH (PROVER : HolMath.RealArith.PsProver) : ExceptT String IO ioconv :=
    HolMath.RealArith.GEN_REAL_ARITH2 P G G2
      PRESIMP_CONV NNF_CONV CONDS_ELIM_CONV SKOLEM_CONV PRENEX_CONV WEAK_DNF_CONV
      (HolMath.CalcInt.term_of_rat S) Rl.REAL_RAT_EQ_CONV Rl.REAL_RAT_GE_CONV Rl.REAL_RAT_GT_CONV
      REAL_POLY_CONV Q1.polys.POLYNOMIAL_NEG_CONV Q1.polys.POLYNOMIAL_ADD_CONV
      Q1.polys.POLYNOMIAL_MUL_CONV PROVER
  let GEN_REAL_ARITH3 (PROVER : HolMath.RealArith.PsProver) (tm : term) : IO (Except String thm) :=
    ExceptT.run do ExceptT.mk ((← GEN_REAL_ARITH PROVER) tm)
  let pure_ ← GEN_REAL_ARITH REAL_LINEAR_PROVER
  let init ← GEN_REWRITE_CONV_NET ONCE_DEPTH_CONV [DECIMAL]
  let REAL_ARITH3 : ioconv := fun tm => do
    match ← (do
        let th ← ExceptT.mk (init tm)
        EQ_MP (← SYM th) (← ExceptT.mk (pure_ (← liftExcept (rand (concl th)))))
        : ExceptT String IO thm).run with
    | .ok th => return .ok th
    | .error m =>
      return .error ("REAL_ARITH `" ++ (← HolCore.Printer.string_of_term tm) ++ "`: " ++ m)
  let REAL_ARITH_TAC2 := CONV_TAC REAL_ARITH3
  let ASM_REAL_ARITH_TAC :=
    REPEAT (FIRST_X_ASSUM (fun th =>
      if !(is_forall (concl th)) then MP_TAC th else fun _ => pure (.error "check"))) THEN
    REAL_ARITH_TAC2
  return { GEN_REAL_ARITH3, REAL_ARITH3, REAL_ARITH_TAC2, ASM_REAL_ARITH_TAC }

end

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

/-- The three equivalential forms of transitivity of calc_rat.ml 563-577 -
    `REAL_LE_TRANS_LE` (563), `REAL_LE_TRANS_LTE` (567) and `REAL_LE_TRANS_LT`
    (572).  Each recasts `x <= y` as a universally-quantified transitivity
    statement; the second and third share an identical proof script (only the
    conclusion's inner relation differs, `<=` vs `<`).  All three are consumed
    later in the development, not within calc_rat.ml itself. -/
structure RealFieldTrans where
  /-- `REAL_LE_TRANS_LE` (calc_rat.ml 563): `x <= y <=> (!z. y <= z ==> x <= z)`. -/
  REAL_LE_TRANS_LE  : thm
  /-- `REAL_LE_TRANS_LTE` (calc_rat.ml 567): `x <= y <=> (!z. y < z ==> x <= z)`. -/
  REAL_LE_TRANS_LTE : thm
  /-- `REAL_LE_TRANS_LT` (calc_rat.ml 572): `x <= y <=> (!z. y < z ==> x < z)`. -/
  REAL_LE_TRANS_LT  : thm
  deriving Inhabited

/-- calc_rat.ml 559-576: a few handy equivalential forms of transitivity.
    `REAL_ARITH` is calc_rat.ml's final one. -/
@[nospecialize]
def setupRealFieldTrans [HolBase]
    (R : HolMath.RealAx.RealThms)
    (MESON_TAC : List thm → tactic)
    (REAL_ARITH' : term → IO (Except String thm)) :
    ExceptT String IO RealFieldTrans := do
  let REAL_ARITH_TAC : tactic := CONV_TAC REAL_ARITH'
  let { REAL_LE_REFL, REAL_LE_TRANS, .. } := R

  /- A few handy equivalential forms of transitivity. -/

  let REAL_LE_TRANS_LE ← prove
   r"!x y:real. x <= y <=> (!z. y <= z ==> x <= z)"
   (MESON_TAC [REAL_LE_TRANS, REAL_LE_REFL])

  let REAL_LE_TRANS_LTE ← prove
   r"!x y:real. x <= y <=> (!z. y < z ==> x <= z)"
   (REPEAT GEN_TAC THEN EQ_TAC THENL [REAL_ARITH_TAC, ALL_TAC] THEN
    DISCH_THEN (fun th => tactic_of do
      pure (MP_TAC (← SPEC (← q r"y + (x - y) / &2") th))) THEN REAL_ARITH_TAC)

  let REAL_LE_TRANS_LT ← prove
   r"!x y:real. x <= y <=> (!z. y < z ==> x < z)"
   (REPEAT GEN_TAC THEN EQ_TAC THENL [REAL_ARITH_TAC, ALL_TAC] THEN
    DISCH_THEN (fun th => tactic_of do
      pure (MP_TAC (← SPEC (← q r"y + (x - y) / &2") th))) THEN REAL_ARITH_TAC)

  return {
    REAL_LE_TRANS_LE, REAL_LE_TRANS_LTE, REAL_LE_TRANS_LT }

end

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

/-- `REAL_FIELD` (calc_rat.ml 581-630): builds the nets and conversions once
    and returns the procedure.  `REAL_ARITH` is calc_rat.ml's final one. -/
@[nospecialize]
def setupRealField [HolBase] (R : HolMath.RealAx.RealThms) (T6 : HolMath.Real.RealThms6)
    (T7 : HolMath.Real.RealThms7)
    (NNF_CONV NNFC_CONV WEAK_CNF_CONV CONJ_CANON_CONV PRENEX_CONV
     CONDS_CELIM_CONV NUM_REDUCE_CONV REAL_RAT_REDUCE_CONV : ioconv)
    (REAL_RING REAL_ARITH : ioconv) (MESON : List thm → term → IO (Except String thm)) :
    ExceptT String IO ioconv := do
  let { FORALL_SIMP, EXISTS_SIMP, .. } := HolBase.T
  -- `norm_net` (calc_rat.ml 582-588).
  let gsymPowInv ← GSYM T6.REAL_POW_INV
  let powInvConv : ioconv := fun tm =>
    let ok := match (do rand (← rand tm) : Except String term) with
      | .ok r => HolMath.Nums.is_numeral r
      | .error _ => false
    if ok then REWR_CONV gsymPowInv tm else pure (.error "check")
  let seed ← ExceptT.mk (Simp.net_of_conv (← q r"inv((x:real) pow n)") powInvConv
    HolCore.Nets.empty_net)
  let norm_net ← [FORALL_SIMP, EXISTS_SIMP, R.real_div, T6.REAL_INV_INV, T6.REAL_INV_MUL,
      T6.REAL_POW_ADD].foldrM
    (fun th acc => do ExceptT.mk (Simp.net_of_thm HolBase.B false (← SPEC_ALL th) acc)) seed
  -- `easy_nz_conv` (calc_rat.ml 589-596).
  let easy_nz_conv :=
    LAND_CONV (← GEN_REWRITE_CONV_NET TRY_CONV
      [← ExceptT.mk (MESON [T7.REAL_POW_EQ_0, R.REAL_OF_NUM_EQ] (← q
        r"~(x pow n = &0) <=>
          ~((x:real) = &0) \/ (&n = &0) \/ ~(x pow n = &0)"))]) THENC
    TRY_CONV (LAND_CONV REAL_RAT_REDUCE_CONV THENC
              (← GEN_REWRITE_CONV_NET id [← TAUT (← q r"(T ==> p) <=> p")]))
  -- `prenex_conv`, `setup_conv`, `core_rule`, `is_inv` (calc_rat.ml 597-611).
  let prenex_conv :=
    TOP_DEPTH_CONV BETA_CONV THENC
    NUM_REDUCE_CONV THENC
    TOP_DEPTH_CONV (REWRITES_CONV norm_net) THENC
    NNFC_CONV THENC DEPTH_BINOP_CONV (← q r"(/\)") CONDS_CELIM_CONV THENC
    PRENEX_CONV THENC
    (← ExceptT.mk (Simp.ONCE_REWRITE_CONV HolBase.B
      [← ExceptT.mk (REAL_ARITH (← q r"x < y <=> x < y /\ ~(x = y)"))]))
  let setup_conv := NNF_CONV THENC WEAK_CNF_CONV THENC CONJ_CANON_CONV
  let core_rule (t : term) : ExceptT String IO thm :=
    tryWith (ExceptT.mk (REAL_RING t)) (ExceptT.mk (REAL_ARITH t))
  let inv_tm ← q r"inv:real->real"
  let is_div := is_binop (← q r"(/):real->real->real")
  let is_inv (tm : term) : Bool :=
    (is_div tm || (is_comb tm && (match rator tm with | .ok r => r == inv_tm | .error _ => false)))
    && (match rand tm with | .ok r => !(HolMath.CalcInt.is_ratconst r) | .error _ => false)
  -- `BASIC_REAL_FIELD` (calc_rat.ml 612-624).
  let BASIC_REAL_FIELD (tm : term) : ExceptT String IO thm := do
    let is_freeinv (t : term) : Bool := is_inv t && free_in t tm
    let itms := setify (← liftExcept ((find_terms is_freeinv tm).mapM rand))
    let hyps ← itms.mapM (fun t => do CONV_RULE easy_nz_conv (← SPEC t T6.REAL_MUL_RINV))
    let tm' ← liftExcept (hyps.foldrM (fun th t => mk_imp (concl th) t) tm)
    let th1 ← ExceptT.mk (setup_conv tm')
    let ths ← (conjuncts (← liftExcept (rand (concl th1)))).mapM core_rule
    let th2 ← EQ_MP (← SYM th1) (← end_itlist CONJ ths)
    hyps.foldlM (fun th h => MP th h) th2
  return fun tm => ExceptT.run do
    let th0 ← ExceptT.mk (prenex_conv tm)
    let tm0 ← liftExcept (rand (concl th0))
    let (avs, bod) := strip_forall tm0
    let th1 ← ExceptT.mk (setup_conv bod)
    let ths ← (conjuncts (← liftExcept (rand (concl th1)))).mapM BASIC_REAL_FIELD
    EQ_MP (← SYM th0) (← GENL avs (← EQ_MP (← SYM th1) (← end_itlist CONJ ths)))

end

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

/-- The eight monotone-mapping theorems of calc_rat.ml 634-685, relating the
    reals to the open interval `(-1,1)` via the shrink map `x / (&1 + abs x)`
    and its inverse grow map `y / (&1 - abs y)`.  In OCaml source order:
    `REAL_SHRINK_RANGE` (634), `REAL_SHRINK_LT` (641), `REAL_SHRINK_LE` (657),
    `REAL_SHRINK_EQ` (661), `REAL_SHRINK_GALOIS` (665), `REAL_GROW_SHRINK`
    (677), `REAL_SHRINK_GROW_EQ` (681) and `REAL_SHRINK_GROW` (685).

    None of the eight scripts contains a `THENL`; every one is a plain
    left-associative `THEN` chain (verified against the OCaml), so there are no
    branch-count subtleties in this section. -/
structure RealShrink where
  /-- `REAL_SHRINK_RANGE` (calc_rat.ml 634):
      `!x. abs(x / (&1 + abs x)) < &1`. -/
  REAL_SHRINK_RANGE   : thm
  /-- `REAL_SHRINK_LT` (calc_rat.ml 641):
      `!x y. x / (&1 + abs x) < y / (&1 + abs y) <=> x < y`. -/
  REAL_SHRINK_LT      : thm
  /-- `REAL_SHRINK_LE` (calc_rat.ml 657):
      `!x y. x / (&1 + abs x) <= y / (&1 + abs y) <=> x <= y`. -/
  REAL_SHRINK_LE      : thm
  /-- `REAL_SHRINK_EQ` (calc_rat.ml 661):
      `!x y. x / (&1 + abs x) = y / (&1 + abs y) <=> x = y`. -/
  REAL_SHRINK_EQ      : thm
  /-- `REAL_SHRINK_GALOIS` (calc_rat.ml 665):
      `!x y. x / (&1 + abs x) = y <=> abs y < &1 /\ y / (&1 - abs y) = x`. -/
  REAL_SHRINK_GALOIS  : thm
  /-- `REAL_GROW_SHRINK` (calc_rat.ml 677):
      `!x. x / (&1 + abs x) / (&1 - abs(x / (&1 + abs x))) = x`. -/
  REAL_GROW_SHRINK    : thm
  /-- `REAL_SHRINK_GROW_EQ` (calc_rat.ml 681):
      `!x. x / (&1 - abs x) / (&1 + abs(x / (&1 - abs x))) = x <=> abs x < &1`. -/
  REAL_SHRINK_GROW_EQ : thm
  /-- `REAL_SHRINK_GROW` (calc_rat.ml 685):
      `!x. abs x < &1
           ==> x / (&1 - abs x) / (&1 + abs(x / (&1 - abs x))) = x`. -/
  REAL_SHRINK_GROW    : thm
  deriving Inhabited

/-- calc_rat.ml 640-688: useful monotone mappings between R and (-1,1). -/
@[nospecialize]
def setupRealShrink [HolBase]
    (R : HolMath.RealAx.RealThms)
    (Ci : HolMath.CalcInt.CalcIntThms)
    (L : HolMath.RealArith.RealArithLemmas)
    (T6 : HolMath.Real.RealThms6)
    (T7 : HolMath.Real.RealThms7)
    (REAL_ARITH' : term → IO (Except String thm))
    (REAL_FIELD' : term → IO (Except String thm))
    (MESON' : List thm → term → IO (Except String thm))
    (MESON_TAC : List thm → tactic) :
    ExceptT String IO RealShrink := do
  let REAL_ARITH (t : term) : ExceptT String IO thm := REAL_ARITH' t
  let REAL_FIELD (t : term) : ExceptT String IO thm := REAL_FIELD' t
  let MESON (ths : List thm) (t : term) : ExceptT String IO thm := MESON' ths t
  let REAL_ARITH_TAC : tactic := CONV_TAC REAL_ARITH'
  let { REAL_LE_ANTISYM, .. } := R
  let { REAL_MUL_LZERO, .. } := Ci
  let { REAL_NOT_LT, .. } := L
  let { REAL_ABS_DIV, .. } := T6
  let { REAL_LT_RDIV_EQ, REAL_LT_LDIV_EQ, .. } := T7

  /- Useful monotone mappings between R and (-1,1) -/

  let REAL_SHRINK_RANGE ← prove
   r"!x. abs(x / (&1 + abs x)) < &1"
   (GEN_TAC THEN
    REWRITE_TAC [REAL_ABS_DIV, ← REAL_ARITH (← q r"abs(&1 + abs x) = &1 + abs x")] THEN
    SIMP_TAC [REAL_LT_LDIV_EQ, ← REAL_ARITH (← q r"&0 < &1 + abs x")] THEN
    REAL_ARITH_TAC)

  let REAL_SHRINK_LT ← prove
   r"!x y. x / (&1 + abs x) < y / (&1 + abs y) <=> x < y"
   (← do
    let r6 ← REAL_ARITH (← q r"&0 < &1 + abs x")
    let r5 ← REAL_ARITH (← q r"a / b * c:real = (a * c) / b")
    let r4 ← REAL_ARITH (← q r"&0 < &1 + abs x")
    let r3 ← REAL_ARITH (← q r"abs(&1 + abs x) = &1 + abs x")
    let m1 ← MESON [] (← q r"(!x y. P x y /\ P y x) <=> (!x y. P x y)")
    let r2 ← REAL_ARITH (← q r"&0 < &1 + abs x")
    let r1 ← REAL_ARITH
     (← q r"(&0 < x' <=> &0 < x) /\ (&0 < y' <=> &0 < y) /\
      (abs x' < abs y' <=> abs x < abs y) /\ (abs y' < abs x' <=> abs y < abs x)
      ==> (x' < y' <=> x < y)")
    pure
     (REPEAT GEN_TAC THEN MATCH_MP_TAC r1 THEN
      SIMP_TAC [REAL_LT_RDIV_EQ, r2, REAL_MUL_LZERO] THEN
      MAP_EVERY (fun t => SPEC_TAC (t, t)) [← q r"y:real", ← q r"x:real"] THEN
      REWRITE_TAC [m1] THEN
      REPEAT GEN_TAC THEN
      REWRITE_TAC [REAL_ABS_DIV, r3] THEN
      SIMP_TAC [REAL_LT_RDIV_EQ, r4] THEN
      ONCE_REWRITE_TAC [r5] THEN
      SIMP_TAC [REAL_LT_LDIV_EQ, r6] THEN
      REAL_ARITH_TAC))

  let REAL_SHRINK_LE ← prove
   r"!x y. x / (&1 + abs x) <= y / (&1 + abs y) <=> x <= y"
   (REWRITE_TAC [← GSYM REAL_NOT_LT, REAL_SHRINK_LT])

  let REAL_SHRINK_EQ ← prove
   r"!x y. x / (&1 + abs x) = y / (&1 + abs y) <=> x = y"
   (REWRITE_TAC [← GSYM REAL_LE_ANTISYM, REAL_SHRINK_LE])

  let REAL_SHRINK_GALOIS ← prove
   r"!x y. x / (&1 + abs x) = y <=> abs y < &1 /\ y / (&1 - abs y) = x"
   (← do
    let f1 ← REAL_FIELD (← q r"x * y = &1 ==> inv x * inv y = &1")
    let r3 ← REAL_ARITH (← q r"x * inv y * inv z = x * &1 ==> x / y / z = x")
    let r2 ← REAL_ARITH (← q r"abs y < &1 ==> abs(&1 - abs y) = &1 - abs y")
    let r1 ← REAL_ARITH (← q r"abs(&1 + abs x) = &1 + abs x")
    pure
     (REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
      FIRST_X_ASSUM (fun th => tactic_of do pure (SUBST1_TAC (← SYM th))) THEN
      ASM_REWRITE_TAC [REAL_SHRINK_RANGE] THEN
      ASM_SIMP_TAC [REAL_ABS_DIV, r1, r2] THEN
      MATCH_MP_TAC r3 THEN
      AP_TERM_TAC THEN
      MATCH_MP_TAC f1 THEN
      REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD'))

  let REAL_GROW_SHRINK ← prove
   r"!x. x / (&1 + abs x) / (&1 - abs(x / (&1 + abs x))) = x"
   (MESON_TAC [REAL_SHRINK_GALOIS, REAL_SHRINK_RANGE])

  let REAL_SHRINK_GROW_EQ ← prove
   r"!x. x / (&1 - abs x) / (&1 + abs(x / (&1 - abs x))) = x <=> abs x < &1"
   (MESON_TAC [REAL_SHRINK_GALOIS, REAL_SHRINK_RANGE])

  let REAL_SHRINK_GROW ← prove
   r"!x. abs x < &1
       ==> x / (&1 - abs x) / (&1 + abs(x / (&1 - abs x))) = x"
   (REWRITE_TAC [REAL_SHRINK_GROW_EQ])

  return {
    REAL_SHRINK_RANGE, REAL_SHRINK_LT, REAL_SHRINK_LE, REAL_SHRINK_EQ,
    REAL_SHRINK_GALOIS, REAL_GROW_SHRINK, REAL_SHRINK_GROW_EQ,
    REAL_SHRINK_GROW }

end

end HolMath.CalcRat
