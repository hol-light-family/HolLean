/- File: RealArith.lean
Framework for universal real decision procedures, and a simple instance.
Original       John Harrison, University of Cambridge Computer Laboratory
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Lean4 translation by Chris Walton 2026

HOL Light's linear real decision procedure.  OCaml defines `GEN_REAL_ARITH`
and `REAL_ARITH` twice each by shadowing; Lean cannot shadow, so the two
versions are numbered: `GEN_REAL_ARITH1`/`REAL_ARITH1` (the bootstrapping
versions, with explicit abs-elimination conversion slots) and
`GEN_REAL_ARITH2`/`REAL_ARITH2` (with abs/max/min elimination hardwired in).
A third version arrives in `calc_rat.ml`. -/

import HolMath.CalcInt
import HolMath.Base

namespace HolMath.RealArith

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
open HolCore.Canon (NNFPths dconv)




/- ---------------------------------------------------------------------- -/
/- Data structure for Positivstellensatz refutations.                     -/
/- (realarith.ml 162-177)                                                 -/
/-                                                                        -/
/- The OCaml is a variant type; `num` is the rational type (Lean's         -/
/- `Rat`) and `int` is a machine integer.  `Eqmul`, `Sum` and `Product`    -/
/- are recursive, so this is an ordinary Lean `inductive`.                 -/
/- ---------------------------------------------------------------------- -/

/-- `positivstellensatz` (realarith.ml 166-177): a refutation certificate.
    The `Axiom_*` constructors cite an input hypothesis by index; the
    `Rational_*` constructors supply a numeric witness; `Square` records that a
    term's square is non-negative; and `Eqmul`/`Sum`/`Product` combine
    certificates. -/
inductive positivstellensatz where
  | Axiom_eq    : Int → positivstellensatz
  | Axiom_le    : Int → positivstellensatz
  | Axiom_lt    : Int → positivstellensatz
  | Rational_eq : Rat → positivstellensatz
  | Rational_le : Rat → positivstellensatz
  | Rational_lt : Rat → positivstellensatz
  | Square      : term → positivstellensatz
  | Eqmul       : term → positivstellensatz → positivstellensatz
  | Sum         : positivstellensatz → positivstellensatz → positivstellensatz
  | Product     : positivstellensatz → positivstellensatz → positivstellensatz
  deriving Inhabited, Repr

/-- The variable ordering both `REAL_ARITH` definitions pass to
    `SEMIRING_NORMALIZERS_CONV` is OCaml's POLYMORPHIC `(<)` on terms, not
    HOL Light's `term_order`.  `term` derives `Ord`, so this is the faithful
    analogue - the same device `ImpConv.thm_lt` uses for theorems. -/
def term_lt (x y : term) : Bool := compare x y == Ordering.lt

/- ---------------------------------------------------------------------- -/
/- Some lemmas needed now just to drive the decision procedure.           -/
/- (realarith.ml 12-14)                                                   -/
/- ---------------------------------------------------------------------- -/


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

/-- The twenty-nine driving lemmas (realarith.ml 16-160): consequences of the
    `realax.ml` axioms that only exist to make the decision procedure below go
    through.  Two of them, `REAL_POLY_CLAUSES` (a ten-conjunct semiring bundle)
    and `REAL_POLY_NEG_CLAUSES` (a two-conjunct ring bundle), are fed by both
    `REAL_ARITH` definitions to `SEMIRING_NORMALIZERS_CONV`, so their conjunct
    order is load-bearing. -/
structure RealArithLemmas where
  /-- `REAL_LTE_TOTAL` (realarith.ml 16). -/
  REAL_LTE_TOTAL     : thm
  /-- `REAL_LET_TOTAL` (realarith.ml 20). -/
  REAL_LET_TOTAL     : thm
  /-- `REAL_LT_IMP_LE` (realarith.ml 24). -/
  REAL_LT_IMP_LE     : thm
  /-- `REAL_LTE_TRANS` (realarith.ml 28). -/
  REAL_LTE_TRANS     : thm
  /-- `REAL_LET_TRANS` (realarith.ml 32). -/
  REAL_LET_TRANS     : thm
  /-- `REAL_LT_TRANS` (realarith.ml 36). -/
  REAL_LT_TRANS      : thm
  /-- `REAL_LE_ADD` (realarith.ml 40). -/
  REAL_LE_ADD        : thm
  /-- `REAL_LTE_ANTISYM` (realarith.ml 44). -/
  REAL_LTE_ANTISYM   : thm
  /-- `REAL_SUB_LE` (realarith.ml 48). -/
  REAL_SUB_LE        : thm
  /-- `REAL_NEG_SUB` (realarith.ml 52). -/
  REAL_NEG_SUB       : thm
  /-- `REAL_LE_LT` (realarith.ml 57). -/
  REAL_LE_LT         : thm
  /-- `REAL_SUB_LT` (realarith.ml 61). -/
  REAL_SUB_LT        : thm
  /-- `REAL_NOT_LT` (realarith.ml 66). -/
  REAL_NOT_LT        : thm
  /-- `REAL_SUB_0` (realarith.ml 70). -/
  REAL_SUB_0         : thm
  /-- `REAL_LT_LE` (realarith.ml 76). -/
  REAL_LT_LE         : thm
  /-- `REAL_LT_REFL` (realarith.ml 80). -/
  REAL_LT_REFL       : thm
  /-- `REAL_LTE_ADD` (realarith.ml 84). -/
  REAL_LTE_ADD       : thm
  /-- `REAL_LET_ADD` (realarith.ml 88). -/
  REAL_LET_ADD       : thm
  /-- `REAL_LT_ADD` (realarith.ml 92). -/
  REAL_LT_ADD        : thm
  /-- `REAL_ENTIRE` (realarith.ml 96). -/
  REAL_ENTIRE        : thm
  /-- `REAL_LE_NEGTOTAL` (realarith.ml 106). -/
  REAL_LE_NEGTOTAL   : thm
  /-- `REAL_LE_SQUARE` (realarith.ml 110). -/
  REAL_LE_SQUARE     : thm
  /-- `REAL_MUL_RID` (realarith.ml 116). -/
  REAL_MUL_RID       : thm
  /-- `REAL_POW_2` (realarith.ml 120). -/
  REAL_POW_2         : thm
  /-- `REAL_POLY_CLAUSES` (realarith.ml 125): the ten-conjunct semiring
      bundle. -/
  REAL_POLY_CLAUSES  : thm
  /-- `REAL_POLY_NEG_CLAUSES` (realarith.ml 140): the two-conjunct ring
      bundle. -/
  REAL_POLY_NEG_CLAUSES : thm
  /-- `REAL_POS` (realarith.ml 145). -/
  REAL_POS           : thm
  /-- `REAL_LT_NZ` (realarith.ml 149). -/
  REAL_LT_NZ         : thm
  /-- `REAL_POS_LT` (realarith.ml 156). -/
  REAL_POS_LT        : thm
  deriving Inhabited

/-- realarith.ml 12-160: some lemmas needed now just to drive the decision
    procedure. -/
@[nospecialize]
def setupRealArithLemmas [HolBase]
    (A2 : HolMath.Arith.ArithThms2) (A3 : HolMath.Arith.ArithThms3)
    (Ci : HolMath.CalcInt.CalcIntThms)
    (R : HolMath.RealAx.RealThms)
    (MESON_TAC : List thm → tactic)
    (num_CONV : ioconv) :
    ExceptT String IO RealArithLemmas := do
  let { LE_0, LT_0, .. } := A2
  let { LT_NZ, .. } := A3
  let { REAL_ADD_AC, REAL_MUL_RZERO, REAL_MUL_LZERO, REAL_NEG_NEG,
        REAL_MUL_RNEG, REAL_MUL_LNEG, REAL_NEG_ADD, REAL_ADD_RID, REAL_LE_LNEG,
        REAL_LE_NEG2, REAL_LE_RNEG, .. } := Ci
  let { REAL_ADD_SYM, REAL_ADD_LID, REAL_MUL_SYM, REAL_MUL_ASSOC, REAL_MUL_LID,
        REAL_ADD_LDISTRIB, REAL_LE_REFL, REAL_LE_ANTISYM, REAL_LE_TRANS,
        REAL_LE_TOTAL, REAL_LE_LADD_IMP, REAL_LE_MUL, REAL_MUL_LINV,
        REAL_OF_NUM_EQ, REAL_OF_NUM_LE, real_sub, real_lt, real_pow, .. } := R

  /- Some lemmas needed now just to drive the decision procedure. -/

  let REAL_LTE_TOTAL ← prove
   r"!x y. x < y \/ y <= x"
   (REWRITE_TAC [real_lt] THEN CONV_TAC (fun t => (TAUT t).run))

  let REAL_LET_TOTAL ← prove
   r"!x y. x <= y \/ y < x"
   (REWRITE_TAC [real_lt] THEN CONV_TAC (fun t => (TAUT t).run))

  let REAL_LT_IMP_LE ← prove
   r"!x y. x < y ==> x <= y"
   (MESON_TAC [real_lt, REAL_LE_TOTAL])

  let REAL_LTE_TRANS ← prove
   r"!x y z. x < y /\ y <= z ==> x < z"
   (MESON_TAC [real_lt, REAL_LE_TRANS])

  let REAL_LET_TRANS ← prove
   r"!x y z. x <= y /\ y < z ==> x < z"
   (MESON_TAC [real_lt, REAL_LE_TRANS])

  let REAL_LT_TRANS ← prove
   r"!x y z. x < y /\ y < z ==> x < z"
   (MESON_TAC [REAL_LTE_TRANS, REAL_LT_IMP_LE])

  let REAL_LE_ADD ← prove
   r"!x y. &0 <= x /\ &0 <= y ==> &0 <= x + y"
   (MESON_TAC [REAL_LE_LADD_IMP, REAL_ADD_RID, REAL_LE_TRANS])

  let REAL_LTE_ANTISYM ← prove
   r"!x y. ~(x < y /\ y <= x)"
   (MESON_TAC [real_lt])

  let REAL_SUB_LE ← prove
   r"!x y. &0 <= (x - y) <=> y <= x"
   (REWRITE_TAC [real_sub, ← GSYM REAL_LE_LNEG, REAL_LE_NEG2])

  let REAL_NEG_SUB ← prove
   r"!x y. --(x - y) = y - x"
   (REWRITE_TAC [real_sub, REAL_NEG_ADD, REAL_NEG_NEG] THEN
    REWRITE_TAC [REAL_ADD_AC])

  let REAL_LE_LT ← prove
   r"!x y. x <= y <=> x < y \/ (x = y)"
   (REWRITE_TAC [real_lt] THEN MESON_TAC [REAL_LE_ANTISYM, REAL_LE_TOTAL])

  let REAL_SUB_LT ← prove
   r"!x y. &0 < (x - y) <=> y < x"
   (REWRITE_TAC [real_lt] THEN ONCE_REWRITE_TAC [← GSYM REAL_NEG_SUB] THEN
    REWRITE_TAC [REAL_LE_LNEG, REAL_ADD_RID, REAL_SUB_LE])

  let REAL_NOT_LT ← prove
   r"!x y. ~(x < y) <=> y <= x"
   (REWRITE_TAC [real_lt])

  let REAL_SUB_0 ← prove
   r"!x y. (x - y = &0) <=> (x = y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM REAL_LE_ANTISYM] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [← GSYM REAL_NOT_LT] THEN
    REWRITE_TAC [REAL_SUB_LE, REAL_SUB_LT] THEN REWRITE_TAC [REAL_NOT_LT])

  let REAL_LT_LE ← prove
   r"!x y. x < y <=> x <= y /\ ~(x = y)"
   (MESON_TAC [real_lt, REAL_LE_TOTAL, REAL_LE_ANTISYM])

  let REAL_LT_REFL ← prove
   r"!x. ~(x < x)"
   (REWRITE_TAC [real_lt, REAL_LE_REFL])

  let REAL_LTE_ADD ← prove
   r"!x y. &0 < x /\ &0 <= y ==> &0 < x + y"
   (MESON_TAC [REAL_LE_LADD_IMP, REAL_ADD_RID, REAL_LTE_TRANS])

  let REAL_LET_ADD ← prove
   r"!x y. &0 <= x /\ &0 < y ==> &0 < x + y"
   (MESON_TAC [REAL_LTE_ADD, REAL_ADD_SYM])

  let REAL_LT_ADD ← prove
   r"!x y. &0 < x /\ &0 < y ==> &0 < x + y"
   (MESON_TAC [REAL_LT_IMP_LE, REAL_LTE_ADD])

  let REAL_ENTIRE ← prove
   r"!x y. (x * y = &0) <=> (x = &0) \/ (y = &0)"
   (REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
    ASM_CASES_TAC (← q r"x = &0") THEN ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (MP_TAC (← AP_TERM (← q r"(*) (inv x)") th))) THEN
    REWRITE_TAC [REAL_MUL_ASSOC] THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (REWRITE_TAC [← MATCH_MP REAL_MUL_LINV th])) THEN
    REWRITE_TAC [REAL_MUL_LID, REAL_MUL_RZERO])

  let REAL_LE_NEGTOTAL ← prove
   r"!x. &0 <= x \/ &0 <= --x"
   (REWRITE_TAC [REAL_LE_RNEG, REAL_ADD_LID, REAL_LE_TOTAL])

  let REAL_LE_SQUARE ← prove
   r"!x. &0 <= x * x"
   (GEN_TAC THEN DISJ_CASES_TAC (← SPEC (← q r"x:real") REAL_LE_NEGTOTAL) THEN
    POP_ASSUM (fun th => tactic_of do
      pure (MP_TAC (← MATCH_MP REAL_LE_MUL (← CONJ th th)))) THEN
    REWRITE_TAC [REAL_MUL_LNEG, REAL_MUL_RNEG, REAL_NEG_NEG])

  let REAL_MUL_RID ← prove
   r"!x. x * &1 = x"
   (MESON_TAC [REAL_MUL_LID, REAL_MUL_SYM])

  let REAL_POW_2 ← prove
   r"!x. x pow 2 = x * x"
   (← do
     let n1 ← ExceptT.mk (num_CONV (← q r"1"))
     let n2 ← ExceptT.mk (num_CONV (← q r"2"))
     pure (REWRITE_TAC [n2, n1] THEN
           REWRITE_TAC [real_pow, REAL_MUL_RID]))

  let REAL_POLY_CLAUSES ← prove
   r"(!x y z. x + (y + z) = (x + y) + z) /\
   (!x y. x + y = y + x) /\
   (!x. &0 + x = x) /\
   (!x y z. x * (y * z) = (x * y) * z) /\
   (!x y. x * y = y * x) /\
   (!x. &1 * x = x) /\
   (!x. &0 * x = &0) /\
   (!x y z. x * (y + z) = x * y + x * z) /\
   (!x. x pow 0 = &1) /\
   (!x n. x pow (SUC n) = x * x pow n)"
   (REWRITE_TAC [real_pow, REAL_ADD_LDISTRIB, REAL_MUL_LZERO] THEN
    REWRITE_TAC [REAL_MUL_ASSOC, REAL_ADD_LID, REAL_MUL_LID] THEN
    REWRITE_TAC [REAL_ADD_AC] THEN REWRITE_TAC [REAL_MUL_SYM])

  let REAL_POLY_NEG_CLAUSES ← prove
   r"(!x. --x = --(&1) * x) /\
   (!x y. x - y = x + --(&1) * y)"
   (REWRITE_TAC [REAL_MUL_LNEG, real_sub, REAL_MUL_LID])

  let REAL_POS ← prove
   r"!n. &0 <= &n"
   (REWRITE_TAC [REAL_OF_NUM_LE, LE_0])

  let REAL_LT_NZ ← prove
   r"!n. ~(&n = &0) <=> (&0 < &n)"
   (GEN_TAC THEN REWRITE_TAC [REAL_LT_LE] THEN
    CONV_TAC (RAND_CONV (ONCE_DEPTH_CONV SYM_CONV)) THEN
    ASM_CASES_TAC (← q r"&n = &0") THEN
    ASM_REWRITE_TAC [REAL_LE_REFL, REAL_POS])

  let REAL_POS_LT ← prove
   r"!n. &0 < &(SUC n)"
   (GEN_TAC THEN REWRITE_TAC [← SPEC (← q r"SUC n") (← GSYM REAL_LT_NZ),
                              REAL_OF_NUM_EQ] THEN
    REWRITE_TAC [← GSYM LT_NZ, LT_0])

  return {
    REAL_LTE_TOTAL, REAL_LET_TOTAL, REAL_LT_IMP_LE, REAL_LTE_TRANS,
    REAL_LET_TRANS, REAL_LT_TRANS, REAL_LE_ADD, REAL_LTE_ANTISYM, REAL_SUB_LE,
    REAL_NEG_SUB, REAL_LE_LT, REAL_SUB_LT, REAL_NOT_LT, REAL_SUB_0, REAL_LT_LE,
    REAL_LT_REFL, REAL_LTE_ADD, REAL_LET_ADD, REAL_LT_ADD, REAL_ENTIRE,
    REAL_LE_NEGTOTAL, REAL_LE_SQUARE, REAL_MUL_RID, REAL_POW_2,
    REAL_POLY_CLAUSES, REAL_POLY_NEG_CLAUSES, REAL_POS, REAL_LT_NZ,
    REAL_POS_LT }

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
open HolCore.Canon (NNFPths dconv)

/-- What `GEN_REAL_ARITH` binds before `fun (mk_numeric,...) ->`
    (realarith.ml 185-256): `pth`, `pth_final`, `pth_add`, `pth_mul`,
    `pth_emul`, `pth_square` and the quotations. -/
structure GenRealArith1Ctx where
  pth       : thm
  pth_final : thm
  pth_add   : thm
  pth_mul   : thm
  pth_emul  : thm
  pth_square : thm
  x_tm      : term
  y_tm      : term
  neg_tm    : term
  gt_tm     : term
  ge_tm     : term
  eq_tm     : term
  p_tm      : term
  or_tm     : term
  false_tm  : term
  z_tm      : term
  xy_lt     : term
  xy_nlt    : term
  xy_le     : term
  xy_nle    : term
  xy_gt     : term
  xy_ngt    : term
  xy_ge     : term
  xy_nge    : term
  xy_eq     : term
  xy_ne     : term
  deriving Inhabited

/-- Build `GenRealArith1Ctx` (realarith.ml 185-256). -/
@[nospecialize]
def setupGenRealArith1Ctx [HolBase] (K : HolMath.CalcInt.CalcIntThms)
    (R : HolMath.RealAx.RealThms) (L : RealArithLemmas)
    (MESON_TAC : List thm → tactic) : ExceptT String IO GenRealArith1Ctx := do
  let pth ← prove
   r"(x < y <=> y - x > &0) /\
     (x <= y <=> y - x >= &0) /\
     (x > y <=> x - y > &0) /\
     (x >= y <=> x - y >= &0) /\
     ((x = y) <=> (x - y = &0)) /\
     (~(x < y) <=> x - y >= &0) /\
     (~(x <= y) <=> x - y > &0) /\
     (~(x > y) <=> y - x >= &0) /\
     (~(x >= y) <=> y - x > &0) /\
     (~(x = y) <=> x - y > &0 \/ --(x - y) > &0)"
   (REWRITE_TAC [R.real_gt, R.real_ge, L.REAL_SUB_LT, L.REAL_SUB_LE, L.REAL_NEG_SUB] THEN
    REWRITE_TAC [L.REAL_SUB_0, R.real_lt] THEN MESON_TAC [R.REAL_LE_ANTISYM])
  let pth_final ← TAUT (← q r"(~p ==> F) ==> p")
  let pth_add ← prove
   r"((x = &0) /\ (y = &0) ==> (x + y = &0)) /\
     ((x = &0) /\ y >= &0 ==> x + y >= &0) /\
     ((x = &0) /\ y > &0 ==> x + y > &0) /\
     (x >= &0 /\ (y = &0) ==> x + y >= &0) /\
     (x >= &0 /\ y >= &0 ==> x + y >= &0) /\
     (x >= &0 /\ y > &0 ==> x + y > &0) /\
     (x > &0 /\ (y = &0) ==> x + y > &0) /\
     (x > &0 /\ y >= &0 ==> x + y > &0) /\
     (x > &0 /\ y > &0 ==> x + y > &0)"
   (SIMP_TAC [R.REAL_ADD_LID, K.REAL_ADD_RID, R.real_ge, R.real_gt] THEN
    REWRITE_TAC [L.REAL_LE_LT] THEN
    MESON_TAC [R.REAL_ADD_LID, K.REAL_ADD_RID, L.REAL_LT_ADD])
  let pth_mul ← prove
   r"((x = &0) /\ (y = &0) ==> (x * y = &0)) /\
     ((x = &0) /\ y >= &0 ==> (x * y = &0)) /\
     ((x = &0) /\ y > &0 ==> (x * y = &0)) /\
     (x >= &0 /\ (y = &0) ==> (x * y = &0)) /\
     (x >= &0 /\ y >= &0 ==> x * y >= &0) /\
     (x >= &0 /\ y > &0 ==> x * y >= &0) /\
     (x > &0 /\ (y = &0) ==> (x * y = &0)) /\
     (x > &0 /\ y >= &0 ==> x * y >= &0) /\
     (x > &0 /\ y > &0 ==> x * y > &0)"
   (SIMP_TAC [K.REAL_MUL_LZERO, K.REAL_MUL_RZERO, R.real_ge, R.real_gt] THEN
    SIMP_TAC [L.REAL_LT_LE, R.REAL_LE_MUL] THEN MESON_TAC [L.REAL_ENTIRE])
  let pth_emul ← prove
   r"(y = &0) ==> !x. x * y = &0"
   (SIMP_TAC [K.REAL_MUL_RZERO])
  let pth_square ← prove
   r"!x. x * x >= &0"
   (REWRITE_TAC [R.real_ge, L.REAL_POW_2, L.REAL_LE_SQUARE])
  let x_tm ← q r"x:real"
  let y_tm ← q r"y:real"
  let neg_tm ← q r"(--):real->real"
  let gt_tm ← q r"(>):real->real->bool"
  let ge_tm ← q r"(>=):real->real->bool"
  let eq_tm ← q r"(=):real->real->bool"
  let p_tm ← q r"p:bool"
  let or_tm ← q r"(\/)"
  let false_tm ← q r"F"
  let z_tm ← q r"&0 :real"
  let xy_lt ← q r"(x:real) < y"
  let xy_nlt ← q r"~((x:real) < y)"
  let xy_le ← q r"(x:real) <= y"
  let xy_nle ← q r"~((x:real) <= y)"
  let xy_gt ← q r"(x:real) > y"
  let xy_ngt ← q r"~((x:real) > y)"
  let xy_ge ← q r"(x:real) >= y"
  let xy_nge ← q r"~((x:real) >= y)"
  let xy_eq ← q r"x:real = y"
  let xy_ne ← q r"~(x:real = y)"
  return {
    pth, pth_final, pth_add, pth_mul, pth_emul, pth_square,
    x_tm, y_tm, neg_tm, gt_tm, ge_tm, eq_tm, p_tm, or_tm, false_tm, z_tm,
    xy_lt, xy_nlt, xy_le, xy_nle, xy_gt, xy_ngt, xy_ge, xy_nge, xy_eq, xy_ne }

/-- `is_ge = is_binop ge_tm` (realarith.ml 257). -/
def GenRealArith1Ctx.is_ge (G : GenRealArith1Ctx) (tm : term) : Bool := is_binop G.ge_tm tm

/-- `is_gt = is_binop gt_tm` (realarith.ml 258). -/
def GenRealArith1Ctx.is_gt (G : GenRealArith1Ctx) (tm : term) : Bool := is_binop G.gt_tm tm

/-- `is_req = is_binop eq_tm` (realarith.ml 259). -/
def GenRealArith1Ctx.is_req (G : GenRealArith1Ctx) (tm : term) : Bool := is_binop G.eq_tm tm

/-- `MATCH_MP_RULE th` (realarith.ml 243-246): builds the net once and
    returns the rule. -/
def MATCH_MP_RULE [HolBase] (th : thm) : ExceptT String IO (thm → ExceptT String IO thm) := do
  let net ← (CONJUNCTS th).foldrM (fun th acc => do
      ExceptT.mk (Simp.net_of_conv (← liftExcept (lhand (concl th)))
        (fun t => (PART_MATCH lhand th t).run) acc))
    HolCore.Nets.empty_net
  return fun th => do MP (← ExceptT.mk (Simp.REWRITES_CONV net (concl th))) th

/-- The translator `hol_of_positivstellensatz` hands the prover. -/
abbrev PsTranslator :=
  (List thm × List thm × List thm) → positivstellensatz → IO (Except String thm)

/-- The `prover` argument of `GEN_REAL_ARITH`. -/
abbrev PsProver := PsTranslator → (List thm × List thm × List thm) → IO (Except String thm)

/-- `GEN_REAL_ARITH (mk_numeric, ..., prover)` (realarith.ml 259-379): builds
    the conversions, nets and rules once and returns `fun tm -> ...`.  The
    `init_conv` conversions are passed in. -/
partial def GEN_REAL_ARITH1 [HolBase] (P : NNFPths) (G : GenRealArith1Ctx)
    (PRESIMP_CONV NNF_CONV CONDS_ELIM_CONV SKOLEM_CONV PRENEX_CONV WEAK_DNF_CONV : ioconv)
    (mk_numeric : Rat → Except String term)
    (NUMERIC_EQ_CONV NUMERIC_GE_CONV NUMERIC_GT_CONV : ioconv)
    (POLY_CONV POLY_NEG_CONV POLY_ADD_CONV POLY_MUL_CONV : ioconv)
    (absconv1 absconv2 : ioconv) (prover : PsProver) : ExceptT String IO ioconv := do
  let REAL_INEQ_CONV (pth : thm) : ioconv := fun tm => ExceptT.run do
    let (lop, r) ← liftExcept (dest_comb tm)
    let th ← INST [(← liftExcept (rand lop), G.x_tm), (r, G.y_tm)] pth
    TRANS th (← ExceptT.mk (LAND_CONV POLY_CONV (← liftExcept (rand (concl th)))))
  let [REAL_LT_CONV, REAL_LE_CONV, REAL_GT_CONV, REAL_GE_CONV, REAL_EQ_CONV,
       REAL_NOT_LT_CONV, REAL_NOT_LE_CONV, REAL_NOT_GT_CONV, REAL_NOT_GE_CONV, _] :=
       (CONJUNCTS G.pth).map REAL_INEQ_CONV | throw "GEN_REAL_ARITH"
  let REAL_NOT_EQ_CONV : ioconv ← do
    let pth ← liftExcept (last (CONJUNCTS G.pth))
    pure fun tm => ExceptT.run do
      let (l, r) ← liftExcept (dest_eq tm)
      let th ← INST [(l, G.x_tm), (r, G.y_tm)] pth
      let th_p ← ExceptT.mk (POLY_CONV (← liftExcept (do lhand (← lhand (← rand (concl th))))))
      let th_x ← AP_TERM G.neg_tm th_p
      let th_n ← CONV_RULE (RAND_CONV POLY_NEG_CONV) th_x
      let th' ← liftExcept (Drule.MK_DISJ (← AP_THM (← AP_TERM G.gt_tm th_p) G.z_tm)
                                          (← AP_THM (← AP_TERM G.gt_tm th_n) G.z_tm))
      TRANS th th'
  let onRand (c : ioconv) : ioconv := fun t => match rand t with
    | .ok r => c r
    | .error e => pure (.error e)
  let net_single ← [(G.xy_lt, REAL_LT_CONV),
     (G.xy_nlt, onRand REAL_NOT_LT_CONV),
     (G.xy_le, REAL_LE_CONV),
     (G.xy_nle, onRand REAL_NOT_LE_CONV),
     (G.xy_gt, REAL_GT_CONV),
     (G.xy_ngt, onRand REAL_NOT_GT_CONV),
     (G.xy_ge, REAL_GE_CONV),
     (G.xy_nge, onRand REAL_NOT_GE_CONV),
     (G.xy_eq, REAL_EQ_CONV),
     (G.xy_ne, onRand REAL_NOT_EQ_CONV)].foldrM
    (fun (pat, cv) acc => ExceptT.mk (Simp.net_of_conv pat cv acc)) HolCore.Nets.empty_net
  let both (c1 c2 : ioconv) : dconv := fun t => ExceptT.run do
    return (← ExceptT.mk (c1 t), ← ExceptT.mk (c2 t))
  let net_double ← [(G.xy_lt, both REAL_LT_CONV REAL_NOT_LT_CONV),
     (G.xy_le, both REAL_LE_CONV REAL_NOT_LE_CONV),
     (G.xy_gt, both REAL_GT_CONV REAL_NOT_GT_CONV),
     (G.xy_ge, both REAL_GE_CONV REAL_NOT_GE_CONV),
     (G.xy_eq, both REAL_EQ_CONV REAL_NOT_EQ_CONV)].foldrM
    (fun (pat, cv) acc => ExceptT.mk (HolCore.Nets.enter' [] (pat, cv) acc))
    (HolCore.Nets.empty_net : HolCore.Nets.net dconv)
  let REAL_INEQ_NORM_CONV : ioconv := Simp.REWRITES_CONV net_single
  let REAL_INEQ_NORM_DCONV : dconv := fun t => do
    match ← tryfindM (fun (cv : dconv) => cv t) (HolCore.Nets.lookup t net_double) with
    | .ok r => return .ok r
    | .error _ => return .error "REWRITES_CONV"
  let NNF_NORM_CONV :=
    HolCore.Canon.GEN_NNF_CONV HolBase.B P false REAL_INEQ_NORM_CONV REAL_INEQ_NORM_DCONV
  let mulRules ← MATCH_MP_RULE G.pth_mul
  let MUL_RULE (th : thm) : ExceptT String IO thm := do
    CONV_RULE (LAND_CONV POLY_MUL_CONV) (← mulRules th)
  let addRules ← MATCH_MP_RULE G.pth_add
  let ADD_RULE (th : thm) : ExceptT String IO thm := do
    CONV_RULE (LAND_CONV POLY_ADD_CONV) (← addRules th)
  let EMUL_RULE (tm : term) (th : thm) : ExceptT String IO thm := do
    CONV_RULE (LAND_CONV POLY_MUL_CONV) (← SPEC tm (← MATCH_MP G.pth_emul th))
  let SQUARE_RULE (t : term) : ExceptT String IO thm := do
    CONV_RULE (LAND_CONV POLY_MUL_CONV) (← SPEC t G.pth_square)
  let numericThm (c : ioconv) (rel : term) (x : Rat) : ExceptT String IO thm := do
    EQT_ELIM (← ExceptT.mk (c (← liftExcept (do mk_comb (← mk_comb rel (← mk_numeric x)) G.z_tm))))
  let hol_of_positivstellensatz : PsTranslator := fun (eqs, les, lts) prf0 => ExceptT.run do
    -- OCaml evaluates `CONJ (translate p1) (translate p2)` right to left.
    let rec translate (prf : positivstellensatz) : ExceptT String IO thm := do
      match prf with
      | .Axiom_eq n => liftExcept (el n.toNat eqs)
      | .Axiom_le n => liftExcept (el n.toNat les)
      | .Axiom_lt n => liftExcept (el n.toNat lts)
      | .Rational_eq x => numericThm NUMERIC_EQ_CONV G.eq_tm x
      | .Rational_le x => numericThm NUMERIC_GE_CONV G.ge_tm x
      | .Rational_lt x => numericThm NUMERIC_GT_CONV G.gt_tm x
      | .Square t => SQUARE_RULE t
      | .Eqmul t p => EMUL_RULE t (← translate p)
      | .Sum p1 p2 => do
          let t2 ← translate p2
          ADD_RULE (← CONJ (← translate p1) t2)
      | .Product p1 p2 => do
          let t2 ← translate p2
          MUL_RULE (← CONJ (← translate p1) t2)
    CONV_RULE (FIRST_CONV [NUMERIC_GE_CONV, NUMERIC_GT_CONV, NUMERIC_EQ_CONV]) (← translate prf0)
  let init_conv :=
    TOP_DEPTH_CONV BETA_CONV THENC
    PRESIMP_CONV THENC
    NNF_CONV THENC DEPTH_BINOP_CONV G.or_tm CONDS_ELIM_CONV THENC
    NNF_NORM_CONV THENC
    SKOLEM_CONV THENC
    PRENEX_CONV THENC
    WEAK_DNF_CONV
  let rec overall (dun ths : List thm) : ExceptT String IO thm := do
    match ths with
    | [] =>
      let (eq, ne) := partition (fun th => G.is_req (concl th)) dun
      let (le, nl) := partition (fun th => G.is_ge (concl th)) ne
      let lt := filter (fun th => G.is_gt (concl th)) nl
      ExceptT.mk (prover hol_of_positivstellensatz (eq, le, lt))
    | th :: oths =>
      let tm := concl th
      if is_conj tm then
        let (th1, th2) ← CONJ_PAIR th
        overall dun (th1 :: th2 :: oths)
      else if is_disj tm then
        let th1 ← overall dun ((← ASSUME (← liftExcept (lhand tm))) :: oths)
        let th2 ← overall dun ((← ASSUME (← liftExcept (rand tm))) :: oths)
        DISJ_CASES th th1 th2
      else overall (th :: dun) oths
  return fun tm => ExceptT.run do
    -- NNF_NORM_CONV' with its CACHE_CONV is made afresh for each `tm`.
    let cacheNet ← liftM (IO.mkRef (HolCore.Nets.empty_net : HolCore.Nets.net thm))
    let cachedNormConv : ioconv := fun t => do
      let ALPHA_HACK (th : thm) (q : term) : Except String thm := do
        let q' ← lhand (concl th)
        if q' == q then .ok th else Kernel.TRANS (← Equal.ALPHA q q') th
      match tryfind (fun th => ALPHA_HACK th t) (HolCore.Nets.lookup t (← cacheNet.get)) with
      | .ok th => return .ok th
      | .error _ =>
        match ← REAL_INEQ_NORM_CONV t with
        | .error e => return .error e
        | .ok th =>
          match ← HolCore.Nets.enter [] (t, th) (← cacheNet.get) with
          | .ok net' => cacheNet.set net'; return .ok th
          | .error e => return .error e
    let NNF_NORM_CONV' :=
      HolCore.Canon.GEN_NNF_CONV HolBase.B P false cachedNormConv (fun _ => pure (.error ""))
    let rec absremover : ioconv := fun t =>
      (TOP_DEPTH_CONV (absconv1 THENC BINOP_CONV (LAND_CONV POLY_CONV)) THENC
       TRY_CONV (absconv2 THENC NNF_NORM_CONV' THENC BINOP_CONV absremover)) t
    let th0 ← ExceptT.mk (init_conv (← liftExcept (mk_neg tm)))
    let tm0 ← liftExcept (rand (concl th0))
    let th ←
      if tm0 == G.false_tm then pure (← EQ_IMP_RULE th0).1
      else do
        let (evs, bod) := strip_exists tm0
        let (avs, ibod) := strip_forall bod
        let th1 ← avs.foldrM MK_FORALL (← ExceptT.mk (DEPTH_BINOP_CONV G.or_tm absremover ibod))
        let th2 ← overall [] [← SPECL avs (← ASSUME (← liftExcept (rand (concl th1))))]
        let th3 ← evs.foldrM SIMPLE_CHOOSE (← PROVE_HYP (← EQ_MP th1 (← ASSUME bod)) th2)
        DISCH_ALL (← PROVE_HYP (← EQ_MP th0 (← ASSUME (← liftExcept (mk_neg tm)))) th3)
    MP (← INST [(tm, G.p_tm)] G.pth_final) th

/- ---------------------------------------------------------------------- -/
/- Linear prover. This works over the rationals in general, but is         -/
/- designed to be OK on integers provided the input contains only          -/
/- integers.  REAL_LINEAR_PROVER (realarith.ml 385-489): a Fourier-Motzkin  -/
/- style refutation search producing `positivstellensatz` certificates.     -/
/- This is the `prover` argument both `REAL_ARITH` definitions pass to      -/
/- `GEN_REAL_ARITH`.                                                        -/
/-                                                                        -/
/- The OCaml is `let REAL_LINEAR_PROVER = <helpers> in fun translator       -/
/- (eq,le,lt) -> ...`.  The `<helpers>` that close over nothing tricky      -/
/- (`linear_add`, `linear_cmul`, `contradictory`, `linear_ineqs`,           -/
/- `linear_eqs`, `linear_prover`, `lin_of_hol`, the alien predicates) are   -/
/- top-level defs here; the alien lemmas `pth`/`pth_suc` need proofs, so    -/
/- they are threaded in via the caller.  The final entry point takes the    -/
/- translator, the alien lemmas, a `RatSyntax` (for `term_of_rat`) and the  -/
/- triple.  OCaml `num` is Lean's `Rat`.                                    -/
/- ---------------------------------------------------------------------- -/

/-- A tagged linear form: a finite partial function from terms to rational
    coefficients, paired with the `positivstellensatz` certificate that
    justifies it.  This is the `(e,p)` pair the OCaml `linear_ineqs`/
    `linear_eqs` thread around. -/
abbrev linForm := HolCore.Lib.Func term Rat × positivstellensatz

/-- `HolCore.Lib.Func` derives no `Inhabited` (its `deriving` clause is
    commented out), but its `.Empty` constructor makes it trivially nonempty.
    A local instance so the `partial` linear-prover defs below - whose return
    types mention `Func term Rat` - can be compiled. -/
instance : Inhabited (HolCore.Lib.Func term Rat) := ⟨.Empty⟩

/-- `linear_add` (realarith.ml 386): add two linear forms, dropping any
    coefficient that becomes zero.  `combine (+/) (fun z -> z =/ num_0)`. -/
def linear_add (f g : HolCore.Lib.Func term Rat) : HolCore.Lib.Func term Rat :=
  HolCore.Lib.combine (· + ·) (fun z => z == num_0) f g

/-- `linear_cmul` (realarith.ml 387): scale every coefficient by `c`.
    `mapf (fun x -> c */ x)`. -/
def linear_cmul (c : Rat) (f : HolCore.Lib.Func term Rat) :
    HolCore.Lib.Func term Rat :=
  HolCore.Lib.mapf (fun x => c * x) f

/-- `contradictory p (e,_)` (realarith.ml 389-391): true when `e` is undefined
    and `p num_0` fails, or when `dom e = [one_tm]` and `p(apply e one_tm)`
    fails.  `one_tm` is `&1`.  The `apply` result is `Except`; where it fails
    (it cannot, given the `dom` guard) we treat the clause as false. -/
def contradictory (one_tm : term) (p : Rat → Bool)
    (ep : linForm) : Bool :=
  let e := ep.1
  (HolCore.Lib.is_undefined e && !(p num_0)) ||
  (HolCore.Lib.dom e == [one_tm] &&
    (match HolCore.Lib.apply e one_tm with
     | .ok v => !(p v)
     | .error _ => false))

/-- `linear_ineqs vars (les,lts)` (realarith.ml 392-425): the recursive
    Fourier-Motzkin elimination over the inequalities.  Returns the
    contradictory `(e,p)` pair whose certificate refutes the system.

    The OCaml `try find ... with Failure _ ->` fallbacks become pattern matches
    on the `Except` result of `find` (`.ok` short-circuits, `.error` falls
    through) - a control-flow fallback, not error propagation.  The nested
    `itlist` folds are all right folds (see the inline comments); `one_tm` is
    `&1`. -/
partial def linear_ineqs (one_tm : term) (vars : List term)
    (les lts : List linForm) : Except String linForm :=
  match HolCore.Lib.find (contradictory one_tm (fun x => x > num_0)) lts with
  | .ok r => .ok r
  | .error _ =>
  match HolCore.Lib.find (contradictory one_tm (fun x => x ≥ num_0)) les with
  | .ok r => .ok r
  | .error _ =>
  if vars == ([] : List term) then
    .error "linear_ineqs: no contradiction"
  else
    let ineqs := les ++ lts
    let blowup (v : term) : Nat :=
      (HolCore.Lib.filter
        (fun (ep : linForm) => HolCore.Lib.tryapplyd ep.1 v num_0 > num_0)
        ineqs).length *
      (HolCore.Lib.filter
        (fun (ep : linForm) => HolCore.Lib.tryapplyd ep.1 v num_0 < num_0)
        ineqs).length
    -- v = fst(hd(sort (fun (_,i) (_,j) -> i < j) (map (fun v -> v,blowup v) vars)))
    let scored : List (term × Nat) :=
      vars.map (fun v => (v, blowup v))
    let sorted := HolCore.Lib.sort
      (fun (a : term × Nat) (b : term × Nat) => a.2 < b.2) scored
    match HolCore.Lib.hd sorted with
    | .error e => .error e
    | .ok vpair =>
    let v := vpair.1
    -- addup (e1,p1) (e2,p2) acc
    let addup (ep1 ep2 : linForm) (acc : List linForm) : List linForm :=
      let c1 := HolCore.Lib.tryapplyd ep1.1 v num_0
      let c2 := HolCore.Lib.tryapplyd ep2.1 v num_0
      if c1 * c2 ≥ num_0 then acc
      else
        let e1' := linear_cmul (abs_num c2) ep1.1
        let e2' := linear_cmul (abs_num c1) ep2.1
        let p1' := positivstellensatz.Product (.Rational_lt (abs_num c2)) ep1.2
        let p2' := positivstellensatz.Product (.Rational_lt (abs_num c1)) ep2.2
        (linear_add e1' e2', positivstellensatz.Sum p1' p2') :: acc
    let (les0, les1) := HolCore.Lib.partition
      (fun (ep : linForm) => HolCore.Lib.tryapplyd ep.1 v num_0 == num_0) les
    let (lts0, lts1) := HolCore.Lib.partition
      (fun (ep : linForm) => HolCore.Lib.tryapplyd ep.1 v num_0 == num_0) lts
    let (lesp, lesn) := HolCore.Lib.partition
      (fun (ep : linForm) => HolCore.Lib.tryapplyd ep.1 v num_0 > num_0) les1
    let (ltsp, ltsn) := HolCore.Lib.partition
      (fun (ep : linForm) => HolCore.Lib.tryapplyd ep.1 v num_0 > num_0) lts1
    -- les' = itlist (fun ep1 -> itlist (addup ep1) lesp) lesn les0   (RIGHT fold)
    let les' := HolCore.Lib.itlist
      (fun ep1 acc => HolCore.Lib.itlist (addup ep1) lesp acc) lesn les0
    -- lts' : nested right folds.
    let ltsSeed := HolCore.Lib.itlist
      (fun ep1 acc => HolCore.Lib.itlist (addup ep1) (lesn ++ ltsn) acc) ltsp lts0
    let lts' := HolCore.Lib.itlist
      (fun ep1 acc => HolCore.Lib.itlist (addup ep1) (lesp ++ ltsp) acc) ltsn ltsSeed
    linear_ineqs one_tm (HolCore.Lib.subtract vars [v]) les' lts'

/-- `linear_eqs (eqs,les,lts)` (realarith.ml 426-441): eliminate the equalities
    one at a time, then hand off to `linear_ineqs`.  The `find` on `eqs` is a
    control-flow fallback as in `linear_ineqs`.

    In `xform`, `k = minus_num d */ abs_num c // c`: OCaml's `*/` and `//` are
    left-associative and of equal precedence, so this is `((-d) * abs_num c) / c`.
    `term_of_rat` needs the `RatSyntax` record, threaded in as `RS`. -/
partial def linear_eqs (RS : HolMath.CalcInt.RatSyntax) (one_tm : term)
    (eqs les lts : List linForm) : Except String linForm :=
  match HolCore.Lib.find (contradictory one_tm (fun x => x == num_0)) eqs with
  | .ok r => .ok r
  | .error _ =>
  match eqs with
  | [] =>
      -- vars = subtract (itlist (union o dom o fst) (les@lts) []) [one_tm]
      let vars := HolCore.Lib.subtract
        (HolCore.Lib.itlist
          (fun (ep : linForm) acc => HolCore.Lib.union (HolCore.Lib.dom ep.1) acc)
          (les ++ lts) [])
        [one_tm]
      linear_ineqs one_tm vars les lts
  | (e, p) :: es =>
      if HolCore.Lib.is_undefined e then linear_eqs RS one_tm es les lts
      else
        match HolCore.Lib.choose (HolCore.Lib.undefine one_tm e) with
        | .error err => .error err
        | .ok (x, c) =>
          -- xform (t,q) : uses term_of_rat, so it is Except-valued.
          let xform (tq : linForm) : Except String linForm :=
            let t := tq.1
            let q := tq.2
            let d := HolCore.Lib.tryapplyd t x num_0
            if d == num_0 then .ok tq
            else do
              let k := ((-d) * abs_num c) / c
              let e' := linear_cmul k e
              let t' := linear_cmul (abs_num c) t
              let ktm ← HolMath.CalcInt.term_of_rat RS k
              let p' := positivstellensatz.Eqmul ktm p
              let q' := positivstellensatz.Product (.Rational_lt (abs_num c)) q
              pure (linear_add e' t', positivstellensatz.Sum p' q')
          do
            let es' ← es.mapM xform
            let les' ← les.mapM xform
            let lts' ← lts.mapM xform
            linear_eqs RS one_tm es' les' lts'

/-- `linear_prover (eq,le,lt)` (realarith.ml 442-448): tag each input linear
    form with its `Axiom_*` index and run `linear_eqs`.  `0--n` is
    `HolCore.Lib.upto 0 n`; the indices START AT 0 and `el` is 0-indexed, so
    they line up with `GEN_REAL_ARITH1`'s `Axiom_eq n -> el n eqs` with NO
    offset. -/
def linear_prover (RS : HolMath.CalcInt.RatSyntax) (one_tm : term)
    (eq le lt : List (HolCore.Lib.Func term Rat)) : Except String linForm := do
  let mkTag (ctor : Int → positivstellensatz)
      (ps : List (HolCore.Lib.Func term Rat)) :
      Except String (List linForm) :=
    HolCore.Lib.map2 (fun p n => (p, ctor n)) ps
      (HolCore.Lib.upto 0 (Int.ofNat ps.length - 1))
  let eqs ← mkTag positivstellensatz.Axiom_eq eq
  let les ← mkTag positivstellensatz.Axiom_le le
  let lts ← mkTag positivstellensatz.Axiom_lt lt
  linear_eqs RS one_tm eqs les lts

/-- `lin_of_hol` (realarith.ml 449-464): read a HOL real term into a linear
    form.  RECURSIVE, and it REBINDS `one_tm`/`zero_tm`/`add_tm`/`mul_tm`
    locally and SHADOWS its own name in the OCaml - here the constants are
    parsed once and passed in, and the recursion is a local `rec`.  Uses
    `is_ratconst`/`rat_of_term`.  A term maps to `tm |=> num 1` when it is a
    variable (not a comb) or an unrecognised application. -/
partial def lin_of_hol (one_tm zero_tm add_tm mul_tm : term) (tm : term) :
    HolCore.Lib.Func term Rat :=
  if tm == zero_tm then HolCore.Lib.undefined
  else if !(is_comb tm) then (tm |=> (num_1 : Rat))
  else if HolMath.CalcInt.is_ratconst tm then
    (match HolMath.CalcInt.rat_of_term tm with
     | .ok r => (one_tm |=> r)
     | .error _ => (tm |=> (num_1 : Rat)))
  else
    match dest_comb tm with
    | .error _ => (tm |=> (num_1 : Rat))
    | .ok (lop, r) =>
      if !(is_comb lop) then (tm |=> (num_1 : Rat))
      else
        match dest_comb lop with
        | .error _ => (tm |=> (num_1 : Rat))
        | .ok (op, l) =>
          if op == add_tm then
            linear_add (lin_of_hol one_tm zero_tm add_tm mul_tm l)
                       (lin_of_hol one_tm zero_tm add_tm mul_tm r)
          else if op == mul_tm && HolMath.CalcInt.is_ratconst l then
            (match HolMath.CalcInt.rat_of_term l with
             | .ok rv => (r |=> rv)
             | .error _ => (tm |=> (num_1 : Rat)))
          else (tm |=> (num_1 : Rat))

/-- `is_alien` (realarith.ml 465-468): `real_of_num n` with `n` not a numeral -
    a DIRECT term pattern match. -/
def is_alien (tm : term) : Bool :=
  match tm with
  | .Comb (.Const "real_of_num" _) n => !(HolMath.Nums.is_numeral n)
  | _ => false

/-- `is_suc_alien` (realarith.ml 469-472): `real_of_num (SUC _)`. -/
def is_suc_alien (tm : term) : Bool :=
  match tm with
  | .Comb (.Const "real_of_num" _) (.Comb (.Const "SUC" _) _) => true
  | _ => false

/-- `dest_suc_alien` (realarith.ml 473-476): the `n` inside `real_of_num (SUC
    n)`; ends `| _ -> failwith ""`. -/
def dest_suc_alien (tm : term) : Except String term :=
  match tm with
  | .Comb (.Const "real_of_num" _) (.Comb (.Const "SUC" _) n) => .ok n
  | _ => failwith ""

/-- The alien-handling lemmas (realarith.ml 478-479):
      `pth     = REWRITE_RULE[GSYM real_ge] (SPEC n_tm REAL_POS)`
      `pth_suc = REWRITE_RULE[GSYM real_gt] (SPEC n_tm REAL_POS_LT)`.
    `REAL_POS` and `REAL_POS_LT` are fields 27 and 29 of `RealArithLemmas`.
    Bundled into a small record built once and threaded into the entry point. -/
structure LinearProverAliens where
  /-- `n:num`, the variable both lemmas are specialised at. -/
  n_tm    : term
  /-- `REWRITE_RULE[GSYM real_ge] (SPEC n_tm REAL_POS)`. -/
  pth     : thm
  /-- `REWRITE_RULE[GSYM real_gt] (SPEC n_tm REAL_POS_LT)`. -/
  pth_suc : thm
  deriving Inhabited

/-- Build `LinearProverAliens` (realarith.ml 477-479).  Takes `R`
    (`RealAx.RealThms`) for `real_ge`/`real_gt` and the `RealArithLemmas`
    bundle `L` for `REAL_POS`/`REAL_POS_LT`. -/
@[nospecialize]
def setupLinearProverAliens [HolBase] (R : HolMath.RealAx.RealThms) (L : RealArithLemmas) :
    ExceptT String IO LinearProverAliens := do
  let n_tm ← q r"n:num"
  let pth ← REWRITE_RULE [← GSYM R.real_ge] (← SPEC n_tm L.REAL_POS)
  let pth_suc ← REWRITE_RULE [← GSYM R.real_gt] (← SPEC n_tm L.REAL_POS_LT)
  return { n_tm, pth, pth_suc }

/-- `REAL_LINEAR_PROVER` (realarith.ml 385-489): the `prover` slot of
    `GEN_REAL_ARITH1`.  Reads the hypotheses into linear forms, handles the
    `real_of_num n` "aliens" (non-numeral casts), runs `linear_prover`, and
    calls the translator on the alien-extended triple.

    The `translator` (`hol_of_positivstellensatz`) is passed UNAPPLIED so this
    function can apply it to its own alien-extended triple rather than the one
    the framework started from.  The term constants `lin_of_hol` needs, the
    `RatSyntax`, and the alien lemmas `A` are threaded in.  `partial` because
    `linear_ineqs`/`linear_eqs`/`lin_of_hol` are mutually recursive. -/
partial def REAL_LINEAR_PROVER (RS : HolMath.CalcInt.RatSyntax)
    (A : LinearProverAliens)
    (one_tm zero_tm add_tm mul_tm : term)
    (translator : (List thm × List thm × List thm) →
                  positivstellensatz → IO (Except String thm))
    (tris : List thm × List thm × List thm) : IO (Except String thm) :=
  ExceptT.run do
    let (eq, le, lt) := tris
    -- eq_pols = map (lin_of_hol o lhand o concl) eq   (o -> explicit lambda)
    let polOf (th : thm) : Except String (HolCore.Lib.Func term Rat) := do
      let l ← HolCore.Equal.lhand (concl th)
      pure (lin_of_hol one_tm zero_tm add_tm mul_tm l)
    let eq_pols ← liftExcept (eq.mapM polOf)
    let le_pols ← liftExcept (le.mapM polOf)
    let lt_pols ← liftExcept (lt.mapM polOf)
    -- all_aliens = filter is_alien (itlist (union o dom) (eq_pols@le_pols@lt_pols) [])
    let all_aliens := HolCore.Lib.filter is_alien
      (HolCore.Lib.itlist
        (fun (f : HolCore.Lib.Func term Rat) acc =>
          HolCore.Lib.union (HolCore.Lib.dom f) acc)
        (eq_pols ++ le_pols ++ lt_pols) [])
    let (suc_aliens, aliens) := HolCore.Lib.partition is_suc_alien all_aliens
    -- le_pols' = le_pols @ map (fun v -> v |=> num 1) aliens
    let le_pols' := le_pols ++
      aliens.map (fun v => (v |=> (num_1 : Rat)))
    let lt_pols' := lt_pols ++
      suc_aliens.map (fun v => (v |=> (num_1 : Rat)))
    -- let _,proof = linear_prover(eq_pols,le_pols',lt_pols')
    let (_, proof) ← liftExcept (linear_prover RS one_tm eq_pols le_pols' lt_pols')
    -- le' = le @ map (fun a -> INST [rand a,n_tm] pth) aliens
    let le' ← liftExcept (do
      let extra ← aliens.mapM (fun a => do
        Kernel.INST [(← rand a, A.n_tm)] A.pth)
      pure (le ++ extra))
    -- lt' = lt @ map (fun a -> INST [dest_suc_alien a,n_tm] pth_suc) suc_aliens
    let lt' ← liftExcept (do
      let extra ← suc_aliens.mapM (fun a => do
        Kernel.INST [(← dest_suc_alien a, A.n_tm)] A.pth_suc)
      pure (lt ++ extra))
    -- `translator (eq,le',lt') proof` (realarith.ml 488).  The translator is
    -- `hol_of_positivstellensatz` UNAPPLIED, and it is applied here to the
    -- ALIEN-EXTENDED triple, so that the `Axiom_le`/`Axiom_lt` indices the
    -- search emitted for the appended alien point-functions resolve against
    -- `le'`/`lt'` rather than the shorter `le`/`lt`.
    ExceptT.mk (translator (eq, le', lt') proof)


/-- The two polynomial normaliser setups of `REAL_ARITH` #1 and #2
    (realarith.ml 495-500, 652-657) are the same; this builds them. -/
def realPolyConvs [HolBase] (L : RealArithLemmas)
    (TRUTH SEMIRING_PTHS : thm) (num_CONV : term → IO (Except String thm))
    (is_realintconst : term → Bool)
    (REAL_INT_ADD_CONV REAL_INT_MUL_CONV REAL_INT_POW_CONV : ioconv)
    (NUM_ADD_CONV NUM_SUC_CONV NUM_MULT_CONV : ioconv) :
    ExceptT String IO HolMath.Normalizer.PolynomialConvs := do
  let sctx ← HolMath.Normalizer.setupSemiringCtx TRUTH SEMIRING_PTHS
    L.REAL_POLY_CLAUSES L.REAL_POLY_NEG_CLAUSES is_realintconst
    REAL_INT_ADD_CONV REAL_INT_MUL_CONV REAL_INT_POW_CONV term_lt
  return HolMath.Normalizer.SEMIRING_NORMALIZERS_CONV sctx NUM_ADD_CONV NUM_SUC_CONV NUM_MULT_CONV
    num_CONV

/-- The values `REAL_ARITH` #1 builds before `fun tm ->` (realarith.ml
    495-509), other than `rule`: the polynomial conversions and
    `deabs_conv`. -/
structure RealArith1Ctx where
  polys : HolMath.Normalizer.PolynomialConvs
  deabs_conv : ioconv

/-- Build `RealArith1Ctx` (realarith.ml 495-500, 509). -/
@[nospecialize]
def setupRealArith1Ctx [HolBase] (R : HolMath.RealAx.RealThms) (L : RealArithLemmas)
    (TRUTH SEMIRING_PTHS : thm) (num_CONV : term → IO (Except String thm))
    (is_realintconst : term → Bool)
    (REAL_INT_ADD_CONV REAL_INT_MUL_CONV REAL_INT_POW_CONV : ioconv)
    (NUM_ADD_CONV NUM_SUC_CONV NUM_MULT_CONV : ioconv) : ExceptT String IO RealArith1Ctx := do
  let polys ← realPolyConvs L TRUTH SEMIRING_PTHS num_CONV
    is_realintconst REAL_INT_ADD_CONV REAL_INT_MUL_CONV REAL_INT_POW_CONV
    NUM_ADD_CONV NUM_SUC_CONV NUM_MULT_CONV
  let deabs_conv ← REWRITE_CONV_NET [R.real_abs, R.real_max, R.real_min]
  return { polys, deabs_conv }

/-- `REAL_ARITH` #1 (realarith.ml 494-511): builds `rule` once and returns
    `fun tm -> ...`. -/
def REAL_ARITH1 [HolBase] (P : NNFPths) (G : GenRealArith1Ctx) (RA : RealArith1Ctx)
    (PRESIMP_CONV NNF_CONV CONDS_ELIM_CONV SKOLEM_CONV PRENEX_CONV WEAK_DNF_CONV : ioconv)
    (mk_realintconst : Rat → Except String term)
    (REAL_INT_EQ_CONV REAL_INT_GE_CONV REAL_INT_GT_CONV : ioconv)
    (REAL_LINEAR_PROVER : PsProver) : ExceptT String IO ioconv := do
  let NO_CONV : ioconv := fun t => pure (Equal.NO_CONV t)
  let rule ← GEN_REAL_ARITH1 P G PRESIMP_CONV NNF_CONV CONDS_ELIM_CONV SKOLEM_CONV PRENEX_CONV
    WEAK_DNF_CONV mk_realintconst REAL_INT_EQ_CONV REAL_INT_GE_CONV REAL_INT_GT_CONV
    RA.polys.POLYNOMIAL_CONV RA.polys.POLYNOMIAL_NEG_CONV RA.polys.POLYNOMIAL_ADD_CONV
    RA.polys.POLYNOMIAL_MUL_CONV NO_CONV NO_CONV REAL_LINEAR_PROVER
  return fun tm => ExceptT.run do
    let th1 ← ExceptT.mk (RA.deabs_conv tm)
    EQ_MP (← SYM th1) (← ExceptT.mk (rule (← liftExcept (rand (concl th1)))))

/- ---------------------------------------------------------------------- -/
/- Slightly less parametrized GEN_REAL_ARITH with more intelligent        -/
/- elimination of abs, max and min hardwired in.                          -/
/- ---------------------------------------------------------------------- -/

/-- What the second `GEN_REAL_ARITH` binds before `fun (mkconst,...) ->`
    (realarith.ml 518-644): `ABSMAXMIN_ELIM_CONV1`, `ABSMAXMIN_ELIM_CONV2`,
    and `pth_abs`, `pth_max`, `pth_min`. -/
structure GenRealArith2Ctx where
  absconv1 : ioconv
  absconv2 : ioconv
  pth_abs  : thm
  pth_max  : thm
  pth_min  : thm
  deriving Inhabited

/-- Build `GenRealArith2Ctx` (realarith.ml 518-644).  `REAL_ARITH` is the
    first `REAL_ARITH`. -/
@[nospecialize]
def setupGenRealArith2Ctx [HolBase] (R : HolMath.RealAx.RealThms) (REAL_ARITH : ioconv) :
    ExceptT String IO GenRealArith2Ctx := do
  let absconv1 ← GEN_REWRITE_CONV_NET id [← ExceptT.mk (REAL_ARITH (← q
    r"(--(&1) * abs(x) >= r <=>
       --(&1) * x >= r /\ &1 * x >= r) /\
      (--(&1) * abs(x) + a >= r <=>
       a + --(&1) * x >= r /\ a + &1 * x >= r) /\
      (a + --(&1) * abs(x) >= r <=>
       a + --(&1) * x >= r /\ a + &1 * x >= r) /\
      (a + --(&1) * abs(x) + b >= r <=>
       a + --(&1) * x + b >= r /\ a + &1 * x + b >= r) /\
      (a + b + --(&1) * abs(x) >= r <=>
       a + b + --(&1) * x >= r /\ a + b + &1 * x >= r) /\
      (a + b + --(&1) * abs(x) + c >= r <=>
       a + b + --(&1) * x + c >= r /\ a + b + &1 * x + c >= r) /\
      (--(&1) * max x y >= r <=>
       --(&1) * x >= r /\ --(&1) * y >= r) /\
      (--(&1) * max x y + a >= r <=>
       a + --(&1) * x >= r /\ a + --(&1) * y >= r) /\
      (a + --(&1) * max x y >= r <=>
       a + --(&1) * x >= r /\ a + --(&1) * y >= r) /\
      (a + --(&1) * max x y + b >= r <=>
       a + --(&1) * x + b >= r /\ a + --(&1) * y  + b >= r) /\
      (a + b + --(&1) * max x y >= r <=>
       a + b + --(&1) * x >= r /\ a + b + --(&1) * y >= r) /\
      (a + b + --(&1) * max x y + c >= r <=>
       a + b + --(&1) * x + c >= r /\ a + b + --(&1) * y  + c >= r) /\
      (&1 * min x y >= r <=>
       &1 * x >= r /\ &1 * y >= r) /\
      (&1 * min x y + a >= r <=>
       a + &1 * x >= r /\ a + &1 * y >= r) /\
      (a + &1 * min x y >= r <=>
       a + &1 * x >= r /\ a + &1 * y >= r) /\
      (a + &1 * min x y + b >= r <=>
       a + &1 * x + b >= r /\ a + &1 * y  + b >= r) /\
      (a + b + &1 * min x y >= r <=>
       a + b + &1 * x >= r /\ a + b + &1 * y >= r) /\
      (a + b + &1 * min x y + c >= r <=>
       a + b + &1 * x + c >= r /\ a + b + &1 * y  + c >= r) /\
      (min x y >= r <=>
        x >= r /\  y >= r) /\
      (min x y + a >= r <=>
       a + x >= r /\ a + y >= r) /\
      (a + min x y >= r <=>
       a + x >= r /\ a + y >= r) /\
      (a + min x y + b >= r <=>
       a + x + b >= r /\ a + y  + b >= r) /\
      (a + b + min x y >= r <=>
       a + b + x >= r /\ a + b + y >= r) /\
      (a + b + min x y + c >= r <=>
       a + b + x + c >= r /\ a + b + y + c >= r) /\
      (--(&1) * abs(x) > r <=>
       --(&1) * x > r /\ &1 * x > r) /\
      (--(&1) * abs(x) + a > r <=>
       a + --(&1) * x > r /\ a + &1 * x > r) /\
      (a + --(&1) * abs(x) > r <=>
       a + --(&1) * x > r /\ a + &1 * x > r) /\
      (a + --(&1) * abs(x) + b > r <=>
       a + --(&1) * x + b > r /\ a + &1 * x + b > r) /\
      (a + b + --(&1) * abs(x) > r <=>
       a + b + --(&1) * x > r /\ a + b + &1 * x > r) /\
      (a + b + --(&1) * abs(x) + c > r <=>
       a + b + --(&1) * x + c > r /\ a + b + &1 * x + c > r) /\
      (--(&1) * max x y > r <=>
       --(&1) * x > r /\ --(&1) * y > r) /\
      (--(&1) * max x y + a > r <=>
       a + --(&1) * x > r /\ a + --(&1) * y > r) /\
      (a + --(&1) * max x y > r <=>
       a + --(&1) * x > r /\ a + --(&1) * y > r) /\
      (a + --(&1) * max x y + b > r <=>
       a + --(&1) * x + b > r /\ a + --(&1) * y  + b > r) /\
      (a + b + --(&1) * max x y > r <=>
       a + b + --(&1) * x > r /\ a + b + --(&1) * y > r) /\
      (a + b + --(&1) * max x y + c > r <=>
       a + b + --(&1) * x + c > r /\ a + b + --(&1) * y  + c > r) /\
      (min x y > r <=>
        x > r /\  y > r) /\
      (min x y + a > r <=>
       a + x > r /\ a + y > r) /\
      (a + min x y > r <=>
       a + x > r /\ a + y > r) /\
      (a + min x y + b > r <=>
       a + x + b > r /\ a + y  + b > r) /\
      (a + b + min x y > r <=>
       a + b + x > r /\ a + b + y > r) /\
      (a + b + min x y + c > r <=>
       a + b + x + c > r /\ a + b + y + c > r)"))]
  let pth_abs ← prove
   r"P(abs x) <=> (x >= &0 /\ P x) \/ (&0 > x /\ P (--x))"
   (REWRITE_TAC [R.real_abs, R.real_gt, R.real_ge] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [R.real_lt])
  let pth_max ← prove
   r"P(max x y) <=> (y >= x /\ P y) \/ (x > y /\ P x)"
   (REWRITE_TAC [R.real_max, R.real_gt, R.real_ge] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [R.real_lt])
  let pth_min ← prove
   r"P(min x y) <=> (y >= x /\ P x) \/ (x > y /\ P y)"
   (REWRITE_TAC [R.real_min, R.real_gt, R.real_ge] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [R.real_lt])
  let abs_tm ← q r"real_abs"
  let p_tm ← q r"P:real->bool"
  let x_tm ← q r"x:real"
  let y_tm ← q r"y:real"
  let is_max := is_binop (← q r"real_max")
  let is_min := is_binop (← q r"real_min")
  let is_abs (t : term) : Bool := is_comb t && (match rator t with
    | .ok r => r == abs_tm
    | .error _ => false)
  let eliminate_construct (p : term → Bool) (c : term → term → ExceptT String IO thm) : ioconv :=
    fun tm => ExceptT.run do
      let t ← liftExcept (find_term (fun t => p t && free_in t tm) tm)
      let v ← liftM (genvar (type_of t) : IO term)
      let stm ← ExceptT.mk ((← ExceptT.mk (subst [(v, t)])) tm)
      let th0 ← SYM (← liftExcept (do Equal.BETA_CONV (← mk_comb (← mk_abs v stm) t)))
      let (p, ax) ← liftExcept (do dest_comb (← rand (concl th0)))
      CONV_RULE (RAND_CONV (BINOP_CONV (RAND_CONV BETA_CONV))) (← TRANS th0 (← c p ax))
  let elim_abs := eliminate_construct is_abs
    (fun p ax => do INST [(p, p_tm), (← liftExcept (rand ax), x_tm)] pth_abs)
  let elim_max := eliminate_construct is_max
    (fun p ax => do
      let (ax, y) ← liftExcept (dest_comb ax)
      INST [(p, p_tm), (← liftExcept (rand ax), x_tm), (y, y_tm)] pth_max)
  let elim_min := eliminate_construct is_min
    (fun p ax => do
      let (ax, y) ← liftExcept (dest_comb ax)
      INST [(p, p_tm), (← liftExcept (rand ax), x_tm), (y, y_tm)] pth_min)
  let absconv2 := FIRST_CONV [elim_abs, elim_max, elim_min]
  return { absconv1, absconv2, pth_abs, pth_max, pth_min }

/-- The second `GEN_REAL_ARITH (mkconst,...,PROVER)` (realarith.ml 645-646). -/
def GEN_REAL_ARITH2 [HolBase] (P : NNFPths) (G : GenRealArith1Ctx) (G2 : GenRealArith2Ctx)
    (PRESIMP_CONV NNF_CONV CONDS_ELIM_CONV SKOLEM_CONV PRENEX_CONV WEAK_DNF_CONV : ioconv)
    (mkconst : Rat → Except String term) (EQ GE GT : ioconv) (NORM NEG ADD MUL : ioconv)
    (PROVER : PsProver) : ExceptT String IO ioconv :=
  GEN_REAL_ARITH1 P G PRESIMP_CONV NNF_CONV CONDS_ELIM_CONV SKOLEM_CONV PRENEX_CONV WEAK_DNF_CONV
    mkconst EQ GE GT NORM NEG ADD MUL G2.absconv1 G2.absconv2 PROVER

/-- The polynomial conversions `REAL_ARITH` #2 builds (realarith.ml
    652-657). -/
structure RealArith2Ctx where
  polys : HolMath.Normalizer.PolynomialConvs

/- ---------------------------------------------------------------------- -/
/- Incorporate that. This gets overwritten again in "calc_rat.ml".        -/
/- ---------------------------------------------------------------------- -/

/-- Build `RealArith2Ctx` (realarith.ml 652-657). -/
@[nospecialize]
def setupRealArith2Ctx [HolBase] (L : RealArithLemmas)
    (TRUTH SEMIRING_PTHS : thm) (num_CONV : term → IO (Except String thm))
    (is_realintconst : term → Bool)
    (REAL_INT_ADD_CONV REAL_INT_MUL_CONV REAL_INT_POW_CONV : ioconv)
    (NUM_ADD_CONV NUM_SUC_CONV NUM_MULT_CONV : ioconv) : ExceptT String IO RealArith2Ctx := do
  let polys ← realPolyConvs L TRUTH SEMIRING_PTHS
    num_CONV is_realintconst REAL_INT_ADD_CONV REAL_INT_MUL_CONV REAL_INT_POW_CONV
    NUM_ADD_CONV NUM_SUC_CONV NUM_MULT_CONV
  return { polys }

/-- `REAL_ARITH` #2 (realarith.ml 651-662). -/
def REAL_ARITH2 [HolBase] (P : NNFPths) (G : GenRealArith1Ctx) (G2 : GenRealArith2Ctx)
    (RA : RealArith2Ctx)
    (PRESIMP_CONV NNF_CONV CONDS_ELIM_CONV SKOLEM_CONV PRENEX_CONV WEAK_DNF_CONV : ioconv)
    (mk_realintconst : Rat → Except String term)
    (REAL_INT_EQ_CONV REAL_INT_GE_CONV REAL_INT_GT_CONV : ioconv)
    (REAL_LINEAR_PROVER : PsProver) : ExceptT String IO ioconv :=
  GEN_REAL_ARITH2 P G G2 PRESIMP_CONV NNF_CONV CONDS_ELIM_CONV SKOLEM_CONV PRENEX_CONV WEAK_DNF_CONV
    mk_realintconst REAL_INT_EQ_CONV REAL_INT_GE_CONV REAL_INT_GT_CONV
    RA.polys.POLYNOMIAL_CONV RA.polys.POLYNOMIAL_NEG_CONV RA.polys.POLYNOMIAL_ADD_CONV
    RA.polys.POLYNOMIAL_MUL_CONV REAL_LINEAR_PROVER

end

end HolMath.RealArith
