/- File: CalcInt.lean
Calculation with integer-valued reals.
Original       John Harrison, University of Cambridge Computer Laboratory
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Lean4 translation by Chris Walton 2026

Calculation with reals that are integers or rationals.  The rational layer in
HolCore/Lib.lean maps OCaml's `num`/`ratio` operators onto Lean's `Rat`:
`=/`→`==`, `<>/`→`!=`, `//`→`Lib.divide_num`, `minus_num`→negation,
`gcd_num`→`Lib.gcd_num`, `numdom x`→`(Lib.numerator x, Lib.denominator x)`. -/

import HolMath.RealAx
import HolMath.Base

namespace HolMath.CalcInt

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

/-- `is_realintconst` (calc_int.ml 16-21). -/
def is_realintconst (tm : term) : Bool :=
  match tm with
  | .Comb (.Const "real_of_num" _) n => HolMath.Nums.is_numeral n
  | .Comb (.Const "real_neg" _) (.Comb (.Const "real_of_num" _) n) =>
      HolMath.Nums.is_numeral n &&
        (match dest_numeral n with | .ok v => v != num_0 | .error _ => false)
  | _ => false

/-- `dest_realintconst` (calc_int.ml 23-30). -/
def dest_realintconst (tm : term) : Except String Rat :=
  match tm with
  | .Comb (.Const "real_of_num" _) n => dest_numeral n
  | .Comb (.Const "real_neg" _) (.Comb (.Const "real_of_num" _) n) => do
      let nn ← dest_numeral n
      if nn != num_0 then return -(← dest_numeral n) else failwith "dest_realintconst"
  | _ => failwith "dest_realintconst"

/-- The quotations `mk_realintconst` and `term_of_rat` bind before
    `fun x -> ...` (calc_int.ml 32-33, 55), and the numeral constructor. -/
structure RatSyntax where
  cast_tm : term
  neg_tm : term
  div_tm : term
  mk_numeral : Rat → Except String term
  deriving Inhabited

/-- Build the `RatSyntax` (calc_int.ml 33, 55). -/
@[nospecialize]
def setupRatSyntax [HolBase] (mk_numeral : Rat → Except String term) :
    ExceptT String IO RatSyntax := do
  let cast_tm ← q r"real_of_num"
  let neg_tm ← q r"(--)"
  let div_tm ← q r"(/)"
  return { cast_tm, neg_tm, div_tm, mk_numeral }

/-- The `mk_numconst` of `mk_realintconst` (calc_int.ml 34). -/
private def mk_numconst (R : RatSyntax) (n : Rat) : Except String term := do
  mk_comb R.cast_tm (← R.mk_numeral n)

/-- `mk_realintconst` (calc_int.ml 32-36). -/
def mk_realintconst (R : RatSyntax) (x : Rat) : Except String term :=
  if x < num_0 then do mk_comb R.neg_tm (← mk_numconst R (-x)) else mk_numconst R x

/-- `is_ratconst` (calc_int.ml 38-44). -/
def is_ratconst (tm : term) : Bool :=
  match tm with
  | .Comb (.Comb (.Const "real_div" _) p) q =>
      is_realintconst p && is_realintconst q &&
      (match dest_realintconst p, dest_realintconst q with
       | .ok m, .ok n => n > num_1 && gcd_num m n == num_1
       | _, _ => false)
  | _ => is_realintconst tm

/-- `rat_of_term` (calc_int.ml 46-52). -/
def rat_of_term (tm : term) : Except String Rat :=
  match tm with
  | .Comb (.Comb (.Const "real_div" _) p) q => do
      let m ← dest_realintconst p
      let n ← dest_realintconst q
      if n > num_1 && gcd_num m n == num_1 then return divide_num m n
      else failwith "rat_of_term"
  | _ => dest_realintconst tm

/-- `term_of_rat` (calc_int.ml 54-60). -/
def term_of_rat (R : RatSyntax) (x : Rat) : Except String term := do
  let p : Rat := Rat.ofInt (numerator x)
  let q : Rat := Rat.ofInt (denominator x)
  let ptm ← mk_realintconst R p
  if q == num_1 then return ptm
  mk_comb (← mk_comb R.div_tm ptm) (← mk_realintconst R q)

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

/-- The nineteen elementary real theorems of `calc_int.ml` 66-171 - the
    consequences of the `realax.ml` axioms needed to justify the integer
    constant conversions.  Fields in OCaml order. -/
structure CalcIntThms where
  /-- `REAL_ADD_AC` (calc_int.ml 66): the AC-suite for real addition. -/
  REAL_ADD_AC        : thm
  /-- `REAL_ADD_RINV` (calc_int.ml 72). -/
  REAL_ADD_RINV      : thm
  /-- `REAL_EQ_ADD_LCANCEL` (calc_int.ml 76). -/
  REAL_EQ_ADD_LCANCEL : thm
  /-- `REAL_EQ_ADD_RCANCEL` (calc_int.ml 82). -/
  REAL_EQ_ADD_RCANCEL : thm
  /-- `REAL_MUL_RZERO` (calc_int.ml 86). -/
  REAL_MUL_RZERO     : thm
  /-- `REAL_MUL_LZERO` (calc_int.ml 90). -/
  REAL_MUL_LZERO     : thm
  /-- `REAL_NEG_NEG` (calc_int.ml 94). -/
  REAL_NEG_NEG       : thm
  /-- `REAL_MUL_RNEG` (calc_int.ml 99). -/
  REAL_MUL_RNEG      : thm
  /-- `REAL_MUL_LNEG` (calc_int.ml 104). -/
  REAL_MUL_LNEG      : thm
  /-- `REAL_NEG_ADD` (calc_int.ml 108). -/
  REAL_NEG_ADD       : thm
  /-- `REAL_ADD_RID` (calc_int.ml 116). -/
  REAL_ADD_RID       : thm
  /-- `REAL_NEG_0` (calc_int.ml 120). -/
  REAL_NEG_0         : thm
  /-- `REAL_LE_LNEG` (calc_int.ml 124). -/
  REAL_LE_LNEG       : thm
  /-- `REAL_LE_NEG2` (calc_int.ml 134). -/
  REAL_LE_NEG2       : thm
  /-- `REAL_LE_RNEG` (calc_int.ml 141). -/
  REAL_LE_RNEG       : thm
  /-- `REAL_OF_NUM_POW` (calc_int.ml 152). -/
  REAL_OF_NUM_POW    : thm
  /-- `REAL_POW_NEG` (calc_int.ml 157). -/
  REAL_POW_NEG       : thm
  /-- `REAL_ABS_NUM` (calc_int.ml 164). -/
  REAL_ABS_NUM       : thm
  /-- `REAL_ABS_NEG` (calc_int.ml 168). -/
  REAL_ABS_NEG       : thm
  deriving Inhabited

/-- calc_int.ml 62-171: some elementary "bootstrapping" lemmas. -/
@[nospecialize]
def setupCalcInt [HolBase]
    (A2 : HolMath.Arith.ArithThms2) (A5 : HolMath.Arith.ArithThms5)
    (N : HolMath.Nums.NumsThms)
    (R : HolMath.RealAx.RealThms)
    (MESON_TAC : List thm → tactic) :
    ExceptT String IO CalcIntThms := do
  let INDUCT_TAC := HolMath.Nums.INDUCT_TAC N.num_INDUCTION
  let { EXP, LE_0, .. } := A2
  let { EVEN, .. } := A5
  let { REAL_ADD_SYM, REAL_ADD_ASSOC, REAL_ADD_LID, REAL_ADD_LINV,
        REAL_MUL_SYM, REAL_ADD_LDISTRIB, REAL_LE_ANTISYM, REAL_LE_TOTAL,
        REAL_LE_LADD_IMP, REAL_OF_NUM_LE, REAL_OF_NUM_MUL, real_abs, real_pow, .. } := R

  /- Some elementary "bootstrapping" lemmas we need below. -/

  let REAL_ADD_AC ← prove
   r"(m + n = n + m) /\
   ((m + n) + p = m + (n + p)) /\
   (m + (n + p) = n + (m + p))"
   (MESON_TAC [REAL_ADD_ASSOC, REAL_ADD_SYM])

  let REAL_ADD_RINV ← prove
   r"!x. x + --x = &0"
   (MESON_TAC [REAL_ADD_SYM, REAL_ADD_LINV])

  let REAL_EQ_ADD_LCANCEL ← prove
   r"!x y z. (x + y = x + z) <=> (y = z)"
   (REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    POP_ASSUM (fun th => tactic_of do pure (MP_TAC (← AP_TERM (← q r"(+) (--x)") th))) THEN
    REWRITE_TAC [REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_LID])

  let REAL_EQ_ADD_RCANCEL ← prove
   r"!x y z. (x + z = y + z) <=> (x = y)"
   (MESON_TAC [REAL_ADD_SYM, REAL_EQ_ADD_LCANCEL])

  let REAL_MUL_RZERO ← prove
   r"!x. x * &0 = &0"
   (MESON_TAC [REAL_EQ_ADD_RCANCEL, REAL_ADD_LDISTRIB, REAL_ADD_LID])

  let REAL_MUL_LZERO ← prove
   r"!x. &0 * x = &0"
   (MESON_TAC [REAL_MUL_SYM, REAL_MUL_RZERO])

  let REAL_NEG_NEG ← prove
   r"!x. --(--x) = x"
   (MESON_TAC
     [REAL_EQ_ADD_RCANCEL, REAL_ADD_LINV, REAL_ADD_SYM, REAL_ADD_LINV])

  let REAL_MUL_RNEG ← prove
   r"!x y. x * (--y) = -- (x * y)"
   (MESON_TAC [REAL_EQ_ADD_RCANCEL, REAL_ADD_LDISTRIB, REAL_ADD_LINV,
               REAL_MUL_RZERO])

  let REAL_MUL_LNEG ← prove
   r"!x y. (--x) * y = -- (x * y)"
   (MESON_TAC [REAL_MUL_SYM, REAL_MUL_RNEG])

  let REAL_NEG_ADD ← prove
   r"!x y. --(x + y) = --x + --y"
   (REPEAT GEN_TAC THEN
    MATCH_MP_TAC (← GEN_ALL (← EQ_IMP_RULE (← SPEC_ALL REAL_EQ_ADD_RCANCEL)).1) THEN
    EXISTS_TAC (← q r"x + y") THEN REWRITE_TAC [REAL_ADD_LINV] THEN
    ONCE_REWRITE_TAC [← AC REAL_ADD_AC (← q r"(a + b) + (c + d) = (a + c) + (b + d)")] THEN
    REWRITE_TAC [REAL_ADD_LINV, REAL_ADD_LID])

  let REAL_ADD_RID ← prove
   r"!x. x + &0 = x"
   (MESON_TAC [REAL_ADD_SYM, REAL_ADD_LID])

  let REAL_NEG_0 ← prove
   r"--(&0) = &0"
   (MESON_TAC [REAL_ADD_LINV, REAL_ADD_RID])

  let REAL_LE_LNEG ← prove
   r"!x y. --x <= y <=> &0 <= x + y"
   (REPEAT GEN_TAC THEN EQ_TAC THEN
    DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← MATCH_MP REAL_LE_LADD_IMP th))) THENL
     [DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"x:real") th))) THEN
      REWRITE_TAC [← ONCE_REWRITE_RULE [REAL_ADD_SYM] REAL_ADD_LINV],
      DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"--x") th))) THEN
      REWRITE_TAC [REAL_ADD_LINV, REAL_ADD_ASSOC, REAL_ADD_LID,
          ← ONCE_REWRITE_RULE [REAL_ADD_SYM] REAL_ADD_LID]])

  let REAL_LE_NEG2 ← prove
   r"!x y. --x <= --y <=> y <= x"
   (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [← GSYM REAL_NEG_NEG] THEN
    REWRITE_TAC [REAL_LE_LNEG] THEN
    AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_ADD_SYM)

  let REAL_LE_RNEG ← prove
   r"!x y. x <= --y <=> x + y <= &0"
   (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [← GSYM REAL_NEG_NEG] THEN
    REWRITE_TAC [REAL_LE_LNEG, ← GSYM REAL_NEG_ADD] THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_LE_NEG2] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [← GSYM REAL_ADD_LINV] THEN
    REWRITE_TAC [REAL_NEG_ADD, REAL_NEG_NEG] THEN
    MATCH_ACCEPT_TAC REAL_ADD_SYM)

  let REAL_OF_NUM_POW ← prove
   r"!x n. (&x) pow n = &(x EXP n)"
   (GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [real_pow, EXP, REAL_OF_NUM_MUL])

  let REAL_POW_NEG ← prove
   r"!x n. (--x) pow n = if EVEN n then x pow n else --(x pow n)"
   (GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [real_pow, EVEN] THEN
    ASM_CASES_TAC (← q r"EVEN n") THEN
    ASM_REWRITE_TAC [REAL_MUL_RNEG, REAL_MUL_LNEG, REAL_NEG_NEG])

  let REAL_ABS_NUM ← prove
   r"!n. abs(&n) = &n"
   (REWRITE_TAC [real_abs, REAL_OF_NUM_LE, LE_0])

  let REAL_ABS_NEG ← prove
   r"!x. abs(--x) = abs x"
   (REWRITE_TAC [real_abs, REAL_LE_RNEG, REAL_NEG_NEG, REAL_ADD_LID] THEN
    MESON_TAC [REAL_LE_TOTAL, REAL_LE_ANTISYM, REAL_NEG_0])

  return {
    REAL_ADD_AC, REAL_ADD_RINV, REAL_EQ_ADD_LCANCEL, REAL_EQ_ADD_RCANCEL,
    REAL_MUL_RZERO, REAL_MUL_LZERO, REAL_NEG_NEG, REAL_MUL_RNEG, REAL_MUL_LNEG,
    REAL_NEG_ADD, REAL_ADD_RID, REAL_NEG_0, REAL_LE_LNEG, REAL_LE_NEG2,
    REAL_LE_RNEG, REAL_OF_NUM_POW, REAL_POW_NEG, REAL_ABS_NUM, REAL_ABS_NEG }

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

/-- `REAL_INT_LE_CONV,REAL_INT_LT_CONV,REAL_INT_GE_CONV,REAL_INT_GT_CONV,
    REAL_INT_EQ_CONV` (calc_int.ml 177-246). -/
structure RealIntCompareConvs where
  REAL_INT_LE_CONV : ioconv
  REAL_INT_LT_CONV : ioconv
  REAL_INT_GE_CONV : ioconv
  REAL_INT_GT_CONV : ioconv
  REAL_INT_EQ_CONV : ioconv
  deriving Inhabited

/-- Build the five comparison conversions (calc_int.ml 177-246); every
    rewrite net is built here, once. -/
@[nospecialize]
def setupRealIntCompareConvs [HolBase] (NUM_EQ_CONV NUM_LE_CONV NUM_LT_CONV : ioconv)
    (K : CalcIntThms) (R : HolMath.RealAx.RealThms) (A1 : HolMath.Arith.ArithThms1)
    (A2 : HolMath.Arith.ArithThms2) (A3 : HolMath.Arith.ArithThms3) :
    ExceptT String IO RealIntCompareConvs := do
  let TAUT_CONV : ioconv := fun t => (TAUT t).run
  let tth ← TAUT (← q r"(F /\ F <=> F) /\ (F /\ T <=> F) /\
          (T /\ F <=> F) /\ (T /\ T <=> T)")
  let nth ← TAUT (← q r"(~T <=> F) /\ (~F <=> T)")
  let NUM2_EQ_CONV := BINOP_CONV NUM_EQ_CONV THENC (← GEN_REWRITE_CONV_NET id [tth])
  let NUM2_NE_CONV := RAND_CONV NUM2_EQ_CONV THENC (← GEN_REWRITE_CONV_NET id [nth])
  let [pth_le1, pth_le2a, pth_le2b, pth_le3] := CONJUNCTS (← prove
   r"(--(&m) <= &n <=> T) /\
     (&m <= &n <=> m <= n) /\
     (--(&m) <= --(&n) <=> n <= m) /\
     (&m <= --(&n) <=> (m = 0) /\ (n = 0))"
   (REWRITE_TAC [K.REAL_LE_NEG2] THEN
    REWRITE_TAC [K.REAL_LE_LNEG, K.REAL_LE_RNEG] THEN
    REWRITE_TAC [R.REAL_OF_NUM_ADD, R.REAL_OF_NUM_LE, A2.LE_0] THEN
    REWRITE_TAC [A2.LE, A1.ADD_EQ_0])) | throw "REAL_INT_LE_CONV"
  let REAL_INT_LE_CONV := FIRST_CONV
   [← GEN_REWRITE_CONV_NET id [pth_le1],
    (← GEN_REWRITE_CONV_NET id [pth_le2a, pth_le2b]) THENC NUM_LE_CONV,
    (← GEN_REWRITE_CONV_NET id [pth_le3]) THENC NUM2_EQ_CONV]
  let [pth_lt1, pth_lt2a, pth_lt2b, pth_lt3] := CONJUNCTS (← prove
   r"(&m < --(&n) <=> F) /\
     (&m < &n <=> m < n) /\
     (--(&m) < --(&n) <=> n < m) /\
     (--(&m) < &n <=> ~((m = 0) /\ (n = 0)))"
   (REWRITE_TAC [pth_le1, pth_le2a, pth_le2b, pth_le3,
                 ← GSYM A3.NOT_LE, R.real_lt] THEN
    CONV_TAC TAUT_CONV)) | throw "REAL_INT_LT_CONV"
  let REAL_INT_LT_CONV := FIRST_CONV
   [← GEN_REWRITE_CONV_NET id [pth_lt1],
    (← GEN_REWRITE_CONV_NET id [pth_lt2a, pth_lt2b]) THENC NUM_LT_CONV,
    (← GEN_REWRITE_CONV_NET id [pth_lt3]) THENC NUM2_NE_CONV]
  let [pth_ge1, pth_ge2a, pth_ge2b, pth_ge3] := CONJUNCTS (← prove
   r"(&m >= --(&n) <=> T) /\
     (&m >= &n <=> n <= m) /\
     (--(&m) >= --(&n) <=> m <= n) /\
     (--(&m) >= &n <=> (m = 0) /\ (n = 0))"
   (REWRITE_TAC [pth_le1, pth_le2a, pth_le2b, pth_le3, R.real_ge] THEN
    CONV_TAC TAUT_CONV)) | throw "REAL_INT_GE_CONV"
  let REAL_INT_GE_CONV := FIRST_CONV
   [← GEN_REWRITE_CONV_NET id [pth_ge1],
    (← GEN_REWRITE_CONV_NET id [pth_ge2a, pth_ge2b]) THENC NUM_LE_CONV,
    (← GEN_REWRITE_CONV_NET id [pth_ge3]) THENC NUM2_EQ_CONV]
  let [pth_gt1, pth_gt2a, pth_gt2b, pth_gt3] := CONJUNCTS (← prove
   r"(--(&m) > &n <=> F) /\
     (&m > &n <=> n < m) /\
     (--(&m) > --(&n) <=> m < n) /\
     (&m > --(&n) <=> ~((m = 0) /\ (n = 0)))"
   (REWRITE_TAC [pth_lt1, pth_lt2a, pth_lt2b, pth_lt3, R.real_gt] THEN
    CONV_TAC TAUT_CONV)) | throw "REAL_INT_GT_CONV"
  let REAL_INT_GT_CONV := FIRST_CONV
   [← GEN_REWRITE_CONV_NET id [pth_gt1],
    (← GEN_REWRITE_CONV_NET id [pth_gt2a, pth_gt2b]) THENC NUM_LT_CONV,
    (← GEN_REWRITE_CONV_NET id [pth_gt3]) THENC NUM2_NE_CONV]
  let [pth_eq1a, pth_eq1b, pth_eq2a, pth_eq2b] := CONJUNCTS (← prove
   r"((&m = &n) <=> (m = n)) /\
     ((--(&m) = --(&n)) <=> (m = n)) /\
     ((--(&m) = &n) <=> (m = 0) /\ (n = 0)) /\
     ((&m = --(&n)) <=> (m = 0) /\ (n = 0))"
   (REWRITE_TAC [← GSYM R.REAL_LE_ANTISYM, ← GSYM A3.LE_ANTISYM] THEN
    REWRITE_TAC [pth_le1, pth_le2a, pth_le2b, pth_le3, A2.LE, A2.LE_0] THEN
    CONV_TAC TAUT_CONV)) | throw "REAL_INT_EQ_CONV"
  let REAL_INT_EQ_CONV := FIRST_CONV
   [(← GEN_REWRITE_CONV_NET id [pth_eq1a, pth_eq1b]) THENC NUM_EQ_CONV,
    (← GEN_REWRITE_CONV_NET id [pth_eq2a, pth_eq2b]) THENC NUM2_EQ_CONV]
  return { REAL_INT_LE_CONV, REAL_INT_LT_CONV, REAL_INT_GE_CONV,
           REAL_INT_GT_CONV, REAL_INT_EQ_CONV }

/-- `REAL_INT_NEG_CONV`, `REAL_INT_MUL_CONV`, `REAL_INT_ADD_CONV`,
    `REAL_INT_SUB_CONV`, `REAL_INT_POW_CONV`, `REAL_INT_ABS_CONV`
    (calc_int.ml 248-374). -/
structure RealIntArithConvs where
  REAL_INT_NEG_CONV : ioconv
  REAL_INT_MUL_CONV : ioconv
  REAL_INT_ADD_CONV : ioconv
  REAL_INT_SUB_CONV : ioconv
  REAL_INT_POW_CONV : ioconv
  REAL_INT_ABS_CONV : ioconv
  deriving Inhabited

/-- Build the six arithmetic conversions (calc_int.ml 248-374); every
    rewrite net and quotation is made here, once. -/
@[nospecialize]
def setupRealIntArithConvs [HolBase]
    (NUM_MULT_CONV NUM_ADD_CONV NUM_EXP_CONV NUM_EVEN_CONV : ioconv)
    (mk_numeral : Rat → Except String term)
    (K : CalcIntThms) (R : HolMath.RealAx.RealThms) : ExceptT String IO RealIntArithConvs := do
  -- REAL_INT_NEG_CONV (calc_int.ml 248-253).
  let pth ← prove
   r"(--(&0) = &0) /\
     (--(--(&x)) = &x)"
   (REWRITE_TAC [K.REAL_NEG_NEG, K.REAL_NEG_0])
  let REAL_INT_NEG_CONV ← GEN_REWRITE_CONV_NET id [pth]

  -- REAL_INT_MUL_CONV (calc_int.ml 255-272).
  let pth0 ← prove
   r"(&0 * &x = &0) /\
     (&0 * --(&x) = &0) /\
     (&x * &0 = &0) /\
     (--(&x) * &0 = &0)"
   (REWRITE_TAC [K.REAL_MUL_LZERO, K.REAL_MUL_RZERO])
  let (pth1, pth2) ← CONJ_PAIR (← prove
   r"((&m * &n = &(m * n)) /\
      (--(&m) * --(&n) = &(m * n))) /\
     ((--(&m) * &n = --(&(m * n))) /\
      (&m * --(&n) = --(&(m * n))))"
   (REWRITE_TAC [K.REAL_MUL_LNEG, K.REAL_MUL_RNEG, K.REAL_NEG_NEG] THEN
    REWRITE_TAC [R.REAL_OF_NUM_MUL]))
  let REAL_INT_MUL_CONV := FIRST_CONV
   [← GEN_REWRITE_CONV_NET id [pth0],
    (← GEN_REWRITE_CONV_NET id [pth1]) THENC RAND_CONV NUM_MULT_CONV,
    (← GEN_REWRITE_CONV_NET id [pth2]) THENC RAND_CONV (RAND_CONV NUM_MULT_CONV)]

  -- REAL_INT_ADD_CONV (calc_int.ml 274-345).
  let neg_tm ← q r"(--)"
  let amp_tm ← q r"&"
  let add_tm ← q r"(+)"
  let dest := dest_binop (← q r"(+)")
  let m_tm ← q r"m:num"
  let n_tm ← q r"n:num"
  let pth0 ← prove
   r"(--(&m) + &m = &0) /\
     (&m + --(&m) = &0)"
   (REWRITE_TAC [R.REAL_ADD_LINV, K.REAL_ADD_RINV])
  let [pth1, pth2, pth3, pth4, pth5, pth6] := CONJUNCTS (← prove
   r"(--(&m) + --(&n) = --(&(m + n))) /\
     (--(&m) + &(m + n) = &n) /\
     (--(&(m + n)) + &m = --(&n)) /\
     (&(m + n) + --(&m) = &n) /\
     (&m + --(&(m + n)) = --(&n)) /\
     (&m + &n = &(m + n))"
   (REWRITE_TAC [← GSYM R.REAL_OF_NUM_ADD, K.REAL_NEG_ADD] THEN
    REWRITE_TAC [R.REAL_ADD_ASSOC, R.REAL_ADD_LINV, R.REAL_ADD_LID] THEN
    REWRITE_TAC [K.REAL_ADD_RINV, R.REAL_ADD_LID] THEN
    ONCE_REWRITE_TAC [R.REAL_ADD_SYM] THEN
    REWRITE_TAC [R.REAL_ADD_ASSOC, R.REAL_ADD_LINV, R.REAL_ADD_LID] THEN
    REWRITE_TAC [K.REAL_ADD_RINV, R.REAL_ADD_LID])) | throw "REAL_INT_ADD_CONV"
  let NUM_ADD (t : term) : ExceptT String IO thm := ExceptT.mk (NUM_ADD_CONV t)
  let rd (t : term) : ExceptT String IO term := liftExcept (rand t)
  let addConv : ioconv := fun tm => ExceptT.run do
    tryWith (do
        let (l, r) ← liftExcept (dest tm)
        if !(is_realintconst l) || !(is_realintconst r) then throw ""
        if (← liftExcept (rator l)) == neg_tm then
          if (← liftExcept (rator r)) == neg_tm then
            let th1 ← INST [(← rd (← rd l), m_tm), (← rd (← rd r), n_tm)] pth1
            let tm1 ← rd (← rd (← rd (concl th1)))
            let th2 ← AP_TERM neg_tm (← AP_TERM amp_tm (← NUM_ADD tm1))
            TRANS th1 th2
          else
            let m ← rd (← rd l)
            let n ← rd r
            let m' ← liftExcept (dest_numeral m)
            let n' ← liftExcept (dest_numeral n)
            if m' <= n' then
              let p ← liftExcept (mk_numeral (n' - m'))
              let th1 ← INST [(m, m_tm), (p, n_tm)] pth2
              let th2 ← NUM_ADD (← rd (← rd (← liftExcept (lhand (concl th1)))))
              let th3 ← AP_TERM (← liftExcept (rator tm)) (← AP_TERM amp_tm (← SYM th2))
              TRANS th3 th1
            else
              let p ← liftExcept (mk_numeral (m' - n'))
              let th1 ← INST [(n, m_tm), (p, n_tm)] pth3
              let th2 ← NUM_ADD (← rd (← rd (← liftExcept (do lhand (← lhand (concl th1))))))
              let th3 ← AP_TERM neg_tm (← AP_TERM amp_tm (← SYM th2))
              let th4 ← AP_THM (← AP_TERM add_tm th3) (← rd tm)
              TRANS th4 th1
        else
          if (← liftExcept (rator r)) == neg_tm then
            let m ← rd l
            let n ← rd (← rd r)
            let m' ← liftExcept (dest_numeral m)
            let n' ← liftExcept (dest_numeral n)
            if n' <= m' then
              let p ← liftExcept (mk_numeral (m' - n'))
              let th1 ← INST [(n, m_tm), (p, n_tm)] pth4
              let th2 ← NUM_ADD (← rd (← liftExcept (do lhand (← lhand (concl th1)))))
              let th3 ← AP_TERM add_tm (← AP_TERM amp_tm (← SYM th2))
              let th4 ← AP_THM th3 (← rd tm)
              TRANS th4 th1
            else
              let p ← liftExcept (mk_numeral (n' - m'))
              let th1 ← INST [(m, m_tm), (p, n_tm)] pth5
              let th2 ← NUM_ADD (← rd (← rd (← rd (← liftExcept (lhand (concl th1))))))
              let th3 ← AP_TERM neg_tm (← AP_TERM amp_tm (← SYM th2))
              let th4 ← AP_TERM (← liftExcept (rator tm)) th3
              TRANS th4 th1
          else
            let th1 ← INST [(← rd l, m_tm), (← rd r, n_tm)] pth6
            let tm1 ← rd (← rd (concl th1))
            let th2 ← AP_TERM amp_tm (← NUM_ADD tm1)
            TRANS th1 th2)
      (throw "REAL_INT_ADD_CONV")
  let REAL_INT_ADD_CONV := (← GEN_REWRITE_CONV_NET id [pth0]) ORELSEC addConv

  -- REAL_INT_SUB_CONV (calc_int.ml 347-350).
  let REAL_INT_SUB_CONV :=
    (← GEN_REWRITE_CONV_NET id [R.real_sub]) THENC
    TRY_CONV (RAND_CONV REAL_INT_NEG_CONV) THENC
    REAL_INT_ADD_CONV

  -- REAL_INT_POW_CONV (calc_int.ml 352-367).
  let (pth1, pth2) ← CONJ_PAIR (← prove
   r"(&x pow n = &(x EXP n)) /\
     ((--(&x)) pow n = if EVEN n then &(x EXP n) else --(&(x EXP n)))"
   (REWRITE_TAC [K.REAL_OF_NUM_POW, K.REAL_POW_NEG]))
  let tth ← prove
   r"((if T then x:real else y) = x) /\ ((if F then x:real else y) = y)"
   (REWRITE_TAC [])
  let neg_tm ← q r"(--)"
  let REAL_INT_POW_CONV :=
    ((← GEN_REWRITE_CONV_NET id [pth1]) THENC RAND_CONV NUM_EXP_CONV) ORELSEC
    ((← GEN_REWRITE_CONV_NET id [pth2]) THENC
     RATOR_CONV (RATOR_CONV (RAND_CONV NUM_EVEN_CONV)) THENC
     (← GEN_REWRITE_CONV_NET id [tth]) THENC
     (fun tm => match rator tm with
       | .ok rt => if rt == neg_tm then RAND_CONV (RAND_CONV NUM_EXP_CONV) tm
                   else RAND_CONV NUM_EXP_CONV tm
       | .error e => pure (.error e)))

  -- REAL_INT_ABS_CONV (calc_int.ml 369-374).
  let pth ← prove
   r"(abs(--(&x)) = &x) /\
     (abs(&x) = &x)"
   (REWRITE_TAC [K.REAL_ABS_NEG, K.REAL_ABS_NUM])
  let REAL_INT_ABS_CONV ← GEN_REWRITE_CONV_NET id [pth]

  return { REAL_INT_NEG_CONV, REAL_INT_MUL_CONV, REAL_INT_ADD_CONV,
           REAL_INT_SUB_CONV, REAL_INT_POW_CONV, REAL_INT_ABS_CONV }

/-- `real_int_red_conv_list` (calc_int.ml 376-387).  OCaml evaluates the list
    literal last element first, so the patterns are parsed in that order. -/
def real_int_red_conv_list [HolBase] (V : RealIntCompareConvs) (W : RealIntArithConvs) :
    ExceptT String IO (List (term × ioconv)) := do
  let pw ← q r"x pow n"
  let ml ← q r"x * y"
  let sb ← q r"x - y"
  let ad ← q r"x + y"
  let ab ← q r"abs(x)"
  let ng ← q r"--x"
  let eq ← q r"x:real = y"
  let gt ← q r"x > y"
  let ge ← q r"x >= y"
  let lt ← q r"x < y"
  let le ← q r"x <= y"
  return [(le, V.REAL_INT_LE_CONV),
          (lt, V.REAL_INT_LT_CONV),
          (ge, V.REAL_INT_GE_CONV),
          (gt, V.REAL_INT_GT_CONV),
          (eq, V.REAL_INT_EQ_CONV),
          (ng, CHANGED_CONV W.REAL_INT_NEG_CONV),
          (ab, W.REAL_INT_ABS_CONV),
          (ad, W.REAL_INT_ADD_CONV),
          (sb, W.REAL_INT_SUB_CONV),
          (ml, W.REAL_INT_MUL_CONV),
          (pw, W.REAL_INT_POW_CONV)]

/-- `REAL_INT_RED_CONV` (calc_int.ml 389-392): the net is built from
    `basic_net()` as it is now. -/
def REAL_INT_RED_CONV (cl : List (term × ioconv)) : ExceptT String IO ioconv := do
  let net ← cl.foldrM (fun (pat, cnv) acc => ExceptT.mk (Simp.net_of_conv pat cnv acc))
    (← liftM (Simp.basic_net : IO (HolCore.Nets.net Simp.gconv)))
  return Simp.REWRITES_CONV net

/-- `real_int_compute_add_convs` (calc_int.ml 396-401). -/
def real_int_compute_add_convs (cl : List (term × ioconv)) (cs : HolMath.Compute.compset) :
    ExceptT String IO Unit := do
  let convlist := cl.map (fun (pat, the_conv) =>
    let (c, args) := strip_comb pat
    (c, args.length, the_conv))
  convlist.foldrM (fun (c, n, cnv) () =>
    ExceptT.mk (HolMath.Compute.add_conv c (Int.ofNat n) cnv cs)) ()

/-- `REAL_INT_COMPUTE_CONV` (calc_int.ml 403-407). -/
def REAL_INT_COMPUTE_CONV [HolBase] (cl : List (term × ioconv))
    (bool_compset : IO (Except String HolMath.Compute.compset))
    (WEAK_CBV_CONV : HolMath.Compute.compset → ioconv) : ExceptT String IO ioconv := do
  let cs ← ExceptT.mk bool_compset
  ExceptT.mk (HolMath.Compute.set_skip cs (← q r"COND: bool -> A -> A -> A") (some 1))
  real_int_compute_add_convs cl cs
  return WEAK_CBV_CONV cs

end

end HolMath.CalcInt
