/- File: RealAx.lean
Theory of real numbers.
Original       John Harrison, University of Cambridge Computer Laboratory
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Lean4 translation by Chris Walton 2026

CONSTRUCTION OVERVIEW.  The reals are built in three layered stages, each
introducing a type:

  1. `nadd` (realax.ml 253-263) - a BASIC type definition carving out the
     "nearly-multiplicative" functions `num->num` satisfying `is_nadd`.
  2. `hreal` (realax.ml 1257-1258) - a QUOTIENT of `nadd` by the equivalence
     `(===)`, giving the non-negative reals.
  3. `real` (realax.ml 1712-1713) - a QUOTIENT of `hreal#hreal` by `treal_eq`,
     giving the signed reals: the reals at last.

Stages 2 and 3 go through `define_quotient_type` / `lift_function` /
`lift_theorem` from quot.ml. -/

import HolCore.Bool
import HolCore.Equal
import HolCore.Drule
import HolCore.Tactics
import HolCore.Itab
import HolCore.Simp
import HolCore.Parser
import HolCore.Preterm
import HolCore.Printer
import HolCore.Nets
import HolCore.Theorems
import HolCore.IndDefs
import HolCore.Classic
import HolCore.Canon
import HolCore.Meson
import HolCore.Trivia
import HolCore.Quot
import HolMath.Pair
import HolMath.Nums
import HolMath.Recursion
import HolMath.Arith
import HolMath.Wf
import HolMath.CalcNum
import HolMath.Normalizer
import HolMath.Grobner
import HolMath.IndTypes
import HolMath.Lists
import HolMath.Base

namespace HolMath.RealAx

set_option maxRecDepth 8000

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolLight

/- ---------------------------------------------------------------------- -/
/- The main infix overloaded operations                                   -/
/- ---------------------------------------------------------------------- -/

/-- realax.ml 17-46: the working infixes of the construction, the
    overloadable symbols, and their `num` interface.  This changes parser
    state: afterwards `+`, `-`, `*`, `<`, `<=`, `>`, `>=` are overloaded
    symbols mapped to the `num` constants.  realax.ml 48 only defines
    `prioritize_num`; nothing here calls it. -/
def setupRealAxOverloads
    (parse_as_infix : String × (Int × String) → IO Unit)
    (make_overloadable' : String → hol_type → IO (Except String Unit))
    (overload_interface' : String → term → IO (Except String Unit)) :
    ExceptT String IO Unit := do
  let make_overloadable (s : String) (ty : String) : ExceptT String IO Unit := do
    make_overloadable' s (← qty ty)
  let overload_interface (p : String × String) : ExceptT String IO Unit := do
    overload_interface' p.1 (← q p.2)

  parse_as_infix ("++", (16, "right"))
  parse_as_infix ("**", (20, "right"))
  parse_as_infix ("<<=", (12, "right"))
  parse_as_infix ("===", (10, "right"))

  parse_as_infix ("treal_mul", (20, "right"))
  parse_as_infix ("treal_add", (16, "right"))
  parse_as_infix ("treal_le", (12, "right"))
  parse_as_infix ("treal_eq", (10, "right"))

  make_overloadable "+" r"A->A->A"
  make_overloadable "-" r"A->A->A"
  make_overloadable "*" r"A->A->A"
  make_overloadable "/" r"A->A->A"
  make_overloadable "<" r"A->A->bool"
  make_overloadable "<=" r"A->A->bool"
  make_overloadable ">" r"A->A->bool"
  make_overloadable ">=" r"A->A->bool"
  make_overloadable "--" r"A->A"
  make_overloadable "pow" r"A->num->A"
  make_overloadable "inv" r"A->A"
  make_overloadable "abs" r"A->A"
  make_overloadable "max" r"A->A->A"
  make_overloadable "min" r"A->A->A"
  make_overloadable "&" r"num->A"

  for p in [("+", r"(+):num->num->num"), ("-", r"(-):num->num->num"),
            ("*", r"(*):num->num->num"), ("<", r"(<):num->num->bool"),
            ("<=", r"(<=):num->num->bool"), (">", r"(>):num->num->bool"),
            (">=", r"(>=):num->num->bool")] do
    overload_interface p

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

/-- `dist` and the theorems about it (realax.ml 54-171), plus the bounds
    lemmas of 173-247.  Field names match the OCaml identifiers exactly, in
    OCaml order.

    Note realax.ml 125 proves FIVE theorems in a single `let` tuple:
    `DIST_LE_CASES, DIST_ADDBOUND, DIST_TRIANGLE, DIST_ADD2, DIST_ADD2_REV`. -/
structure DistThms where
  /- Absolute distance function on the naturals (54). -/
  dist              : thm
  /- Some easy theorems (61-105). -/
  DIST_REFL         : thm
  DIST_LZERO        : thm
  DIST_RZERO        : thm
  DIST_SYM          : thm
  DIST_LADD         : thm
  DIST_RADD         : thm
  DIST_LADD_0       : thm
  DIST_RADD_0       : thm
  DIST_LMUL         : thm
  DIST_RMUL         : thm
  DIST_EQ_0         : thm
  /- Simplifying theorem about the distance operation (109). -/
  DIST_ELIM_THM     : thm
  /- Now some more theorems (125-171) - the five-way tuple at 125. -/
  DIST_LE_CASES     : thm
  DIST_ADDBOUND     : thm
  DIST_TRIANGLE     : thm
  DIST_ADD2         : thm
  DIST_ADD2_REV     : thm
  DIST_TRIANGLE_LE  : thm
  DIST_TRIANGLES_LE : thm
  /- Useful lemmas about bounds (176-247). -/
  BOUNDS_LINEAR     : thm
  BOUNDS_LINEAR_0   : thm
  BOUNDS_DIVIDED    : thm
  BOUNDS_NOTZERO    : thm
  BOUNDS_IGNORE     : thm
  deriving Inhabited

/-- realax.ml 54-247.  `dist(m,n) = ...` has a paired left-hand side, so
    `new_definition` here is the pair-aware one. -/
@[nospecialize]
def setupDist [HolBase] (N : HolMath.Nums.NumsThms)
    (A1 : HolMath.Arith.ArithThms1) (A2 : HolMath.Arith.ArithThms2)
    (A3 : HolMath.Arith.ArithThms3) (A4 : HolMath.Arith.ArithThms4)
    (A5 : HolMath.Arith.ArithThms5)
    (SUB_ELIM_THM : thm)
    (HIGHER_REWRITE_CONV : List thm → Bool → ioconv)
    (NUM_CANCEL_CONV : ioconv)
    (new_definition' : term → IO (Except String thm)) :
    ExceptT String IO DistThms := do
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let INDUCT_TAC := HolMath.Nums.INDUCT_TAC N.num_INDUCTION
  let { NOT_SUC, .. } := N
  let { COND_ELIM_THM, .. } := HolBase.C
  let { EQ_SYM_EQ, .. } := HolBase.T
  let { ADD_CLAUSES, ADD_SYM, ADD_ASSOC, ADD_EQ_0, EQ_ADD_LCANCEL,
        EQ_ADD_LCANCEL_0, .. } := A1
  let { MULT_CLAUSES, MULT_SYM, LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, LE, LT,
        LT_SUC_LE, LE_0, .. } := A2
  let { LE_ANTISYM, LE_TRANS, LE_CASES, NOT_LE, NOT_LT, .. } := A3
  let { LE_EXISTS, LT_EXISTS, LE_ADD, LE_ADDR, LE_ADD_LCANCEL, LE_ADD2,
        LE_MULT_LCANCEL, .. } := A4
  let { SUB_0, SUB_REFL, ADD_SUB, ADD_SUB2, SUB_EQ_0, ADD_SUBR2, ADD_SUBR,
        SUB_ADD_LCANCEL, SUB_ADD_RCANCEL, LEFT_SUB_DISTRIB, RIGHT_SUB_DISTRIB, .. } := A5

  /- Absolute distance function on the naturals. -/

  let dist ← new_definition
   r"dist(m,n) = (m - n) + (n - m)"

  /- Some easy theorems. -/

  let DIST_REFL ← prove
   r"!n. dist(n,n) = 0"
   (REWRITE_TAC [dist, SUB_REFL, ADD_CLAUSES])

  let DIST_LZERO ← prove
   r"!n. dist(0,n) = n"
   (REWRITE_TAC [dist, SUB_0, ADD_CLAUSES])

  let DIST_RZERO ← prove
   r"!n. dist(n,0) = n"
   (REWRITE_TAC [dist, SUB_0, ADD_CLAUSES])

  let DIST_SYM ← prove
   r"!m n. dist(m,n) = dist(n,m)"
   (REWRITE_TAC [dist] THEN MATCH_ACCEPT_TAC ADD_SYM)

  let DIST_LADD ← prove
   r"!m p n. dist(m + n,m + p) = dist(n,p)"
   (REWRITE_TAC [dist, SUB_ADD_LCANCEL])

  let DIST_RADD ← prove
   r"!m p n. dist(m + p,n + p) = dist(m,n)"
   (REWRITE_TAC [dist, SUB_ADD_RCANCEL])

  let DIST_LADD_0 ← prove
   r"!m n. dist(m + n,m) = n"
   (REWRITE_TAC [dist, ADD_SUB2, ADD_SUBR2, ADD_CLAUSES])

  let DIST_RADD_0 ← prove
   r"!m n. dist(m,m + n) = n"
   (ONCE_REWRITE_TAC [DIST_SYM] THEN MATCH_ACCEPT_TAC DIST_LADD_0)

  let DIST_LMUL ← prove
   r"!m n p. m * dist(n,p) = dist(m * n,m * p)"
   (REWRITE_TAC [dist, LEFT_ADD_DISTRIB, LEFT_SUB_DISTRIB])

  let DIST_RMUL ← prove
   r"!m n p. dist(m,n) * p = dist(m * p,n * p)"
   (REWRITE_TAC [dist, RIGHT_ADD_DISTRIB, RIGHT_SUB_DISTRIB])

  let DIST_EQ_0 ← prove
   r"!m n. (dist(m,n) = 0) <=> (m = n)"
   (REWRITE_TAC [dist, ADD_EQ_0, SUB_EQ_0, LE_ANTISYM])

  /- Simplifying theorem about the distance operation. -/

  let DIST_ELIM_THM ← prove
   r"P(dist(x,y)) <=> !d. ((x = y + d) ==> P(d)) /\ ((y = x + d) ==> P(d))"
   (DISJ_CASES_TAC (← SPECL [← q r"x:num", ← q r"y:num"] LE_CASES) THEN
    POP_ASSUM (fun th => tactic_of do
      pure ((X_CHOOSE_THEN (← q r"e:num") SUBST1_TAC) (← REWRITE_RULE [LE_EXISTS] th))) THEN
    REWRITE_TAC [dist, ADD_SUB, ADD_SUB2, ADD_SUBR, ADD_SUBR2] THEN
    REWRITE_TAC [ADD_CLAUSES, EQ_ADD_LCANCEL] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    REWRITE_TAC [← GSYM ADD_ASSOC, EQ_ADD_LCANCEL_0, ADD_EQ_0] THEN
    ASM_CASES_TAC (← q r"e = 0") THEN ASM_REWRITE_TAC [] THEN
    EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [])

  /- Now some more theorems. -/

  let DIST_ELIM_TAC : tactic :=
    let conv :=
      HIGHER_REWRITE_CONV [SUB_ELIM_THM, COND_ELIM_THM, DIST_ELIM_THM] false
    CONV_TAC conv THEN TRY GEN_TAC THEN CONJ_TAC THEN
    DISCH_THEN (fun th => SUBST_ALL_TAC th THEN
                          (match dest_eq (concl th) with
                           | .ok (l, r) =>
                               if is_var l && not (vfree_in l r) then ALL_TAC
                               else ASSUME_TAC th
                           | .error e => fun _ => pure (.error e)))
  let DIST_ELIM_TAC' : tactic :=
    REPEAT STRIP_TAC THEN REPEAT DIST_ELIM_TAC THEN
    tactic_of (do pure (REWRITE_TAC [← GSYM NOT_LT, LT_EXISTS])) THEN
    DISCH_THEN (CHOOSE_THEN SUBST_ALL_TAC) THEN POP_ASSUM MP_TAC THEN
    CONV_TAC (LAND_CONV NUM_CANCEL_CONV) THEN
    REWRITE_TAC [ADD_CLAUSES, NOT_SUC]
  let DIST_LE_CASES ← prove
   r"!m n p. dist(m,n) <= p <=> (m <= n + p) /\ (n <= m + p)"
   (REPEAT GEN_TAC THEN REPEAT DIST_ELIM_TAC THEN
    REWRITE_TAC [← GSYM ADD_ASSOC, LE_ADD, LE_ADD_LCANCEL])
  let DIST_ADDBOUND ← prove
   r"!m n. dist(m,n) <= m + n"
   (REPEAT GEN_TAC THEN DIST_ELIM_TAC THENL
     [ONCE_REWRITE_TAC [ADD_SYM], ALL_TAC] THEN
    REWRITE_TAC [ADD_ASSOC, LE_ADDR])
  let (DIST_TRIANGLE, DIST_ADD2, DIST_ADD2_REV) ← do
    match CONJUNCTS (← prove
     r"(!m n p. dist(m,p) <= dist(m,n) + dist(n,p)) /\
       (!m n p q. dist(m + n,p + q) <= dist(m,p) + dist(n,q)) /\
       (!m n p q. dist(m,p) <= dist(m + n,p + q) + dist(n,q))"
      DIST_ELIM_TAC') with
    | [a, b, c] => pure (a, b, c)
    | _ => throw "DIST_TRIANGLE: expected three conjuncts"

  let DIST_TRIANGLE_LE ← prove
   r"!m n p q. dist(m,n) + dist(n,p) <= q ==> dist(m,p) <= q"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC (← q r"dist(m,n) + dist(n,p)") THEN ASM_REWRITE_TAC [DIST_TRIANGLE])

  let DIST_TRIANGLES_LE ← prove
   r"!m n p q r s.
        dist(m,n) <= r /\ dist(p,q) <= s ==> dist(m,p) <= dist(n,q) + r + s"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC DIST_TRIANGLE_LE THEN
    EXISTS_TAC (← q r"n:num") THEN GEN_REWRITE_TAC RAND_CONV [ADD_SYM] THEN
    REWRITE_TAC [← GSYM ADD_ASSOC] THEN MATCH_MP_TAC LE_ADD2 THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC DIST_TRIANGLE_LE THEN
    EXISTS_TAC (← q r"q:num") THEN GEN_REWRITE_TAC RAND_CONV [ADD_SYM] THEN
    REWRITE_TAC [LE_ADD_LCANCEL] THEN ONCE_REWRITE_TAC [DIST_SYM] THEN
    ASM_REWRITE_TAC [])

  /- Useful lemmas about bounds. -/

  let BOUNDS_LINEAR ← prove
   r"!A B C. (!n. A * n <= B * n + C) <=> A <= B"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC [NOT_LE] THEN
      DISCH_THEN (fun th => tactic_of do
        pure ((CHOOSE_THEN SUBST1_TAC) (← REWRITE_RULE [LT_EXISTS] th))) THEN
      REWRITE_TAC [RIGHT_ADD_DISTRIB, LE_ADD_LCANCEL] THEN
      DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"SUC C") th))) THEN
      REWRITE_TAC [NOT_LE, MULT_CLAUSES, ADD_CLAUSES, LT_SUC_LE] THEN
      REWRITE_TAC [ADD_ASSOC, LE_ADDR],
      DISCH_THEN (fun th => tactic_of do
        pure ((CHOOSE_THEN SUBST1_TAC) (← REWRITE_RULE [LE_EXISTS] th))) THEN
      REWRITE_TAC [RIGHT_ADD_DISTRIB, ← GSYM ADD_ASSOC, LE_ADD]])

  let BOUNDS_LINEAR_0 ← prove
   r"!A B. (!n. A * n <= B) <=> (A = 0)"
   (REPEAT GEN_TAC THEN
    MP_TAC (← SPECL [← q r"A:num", ← q r"0", ← q r"B:num"] BOUNDS_LINEAR) THEN
    REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES, LE])

  let BOUNDS_DIVIDED ← prove
   r"!P. (?B. !n. P(n) <= B) <=>
       (?A B. !n. n * P(n) <= A * n + B)"
   (GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [← q r"B:num", ← q r"0"] THEN
      GEN_TAC THEN REWRITE_TAC [ADD_CLAUSES] THEN
      GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN
      ASM_REWRITE_TAC [LE_MULT_LCANCEL],
      EXISTS_TAC (← q r"P(0) + A + B") THEN GEN_TAC THEN
      MP_TAC (← SPECL [← q r"n:num", ← q r"(P:num->num) n", ← q r"P(0) + A + B"]
       LE_MULT_LCANCEL) THEN
      ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [LE_ADD] THEN
      DISCH_THEN (fun th => tactic_of do pure (SUBST1_TAC (← SYM th))) THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"A * n + B") THEN
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [LEFT_ADD_DISTRIB] THEN
      GEN_REWRITE_TAC RAND_CONV [ADD_SYM] THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
      REWRITE_TAC [← GSYM ADD_ASSOC, LE_ADD_LCANCEL] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"B * n") THEN
      REWRITE_TAC [LE_ADD] THEN UNDISCH_TAC (← q r"~(n = 0)") THEN
      SPEC_TAC (← q r"n:num", ← q r"n:num") THEN INDUCT_TAC THEN
      ASM_REWRITE_TAC [MULT_CLAUSES, LE_ADD]])

  let BOUNDS_NOTZERO ← prove
   r"!P A B. (P 0 0 = 0) /\ (!m n. P m n <= A * (m + n) + B) ==>
       (?B. !m n. P m n <= B * (m + n))"
   (REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"A + B") THEN
    REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"m + n = 0") THENL
     [RULE_ASSUM_TAC (REWRITE_RULE [ADD_EQ_0]) THEN ASM_REWRITE_TAC [LE_0],
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"A * (m + n) + B") THEN
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [RIGHT_ADD_DISTRIB, LE_ADD_LCANCEL] THEN
      UNDISCH_TAC (← q r"~(m + n = 0)") THEN SPEC_TAC (← q r"m + n", ← q r"p:num") THEN
      INDUCT_TAC THEN REWRITE_TAC [MULT_CLAUSES, LE_ADD]])

  let BOUNDS_IGNORE ← prove
   r"!P Q. (?B. !i. P(i) <= Q(i) + B) <=>
         (?B N. !i. N <= i ==> P(i) <= Q(i) + B)"
   (REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
     [EXISTS_TAC (← q r"B:num") THEN ASM_REWRITE_TAC [],
      POP_ASSUM MP_TAC THEN SPEC_TAC (← q r"B:num", ← q r"B:num") THEN
      SPEC_TAC (← q r"N:num", ← q r"N:num") THEN INDUCT_TAC THENL
       [REWRITE_TAC [LE_0] THEN GEN_TAC THEN DISCH_TAC THEN
        EXISTS_TAC (← q r"B:num") THEN ASM_REWRITE_TAC [],
        GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
        EXISTS_TAC (← q r"B + P(N:num)") THEN X_GEN_TAC (← q r"i:num") THEN
        DISCH_TAC THEN ASM_CASES_TAC (← q r"SUC N <= i") THENL
         [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"Q(i:num) + B") THEN
          REWRITE_TAC [LE_ADD, ADD_ASSOC] THEN FIRST_ASSUM MATCH_MP_TAC THEN
          ASM_REWRITE_TAC [],
          UNDISCH_TAC (← q r"~(SUC N <= i)") THEN REWRITE_TAC [NOT_LE, LT] THEN
          ASM_REWRITE_TAC [← GSYM NOT_LE] THEN DISCH_THEN SUBST1_TAC THEN
          REWRITE_TAC [ADD_ASSOC] THEN ONCE_REWRITE_TAC [ADD_SYM] THEN
          REWRITE_TAC [LE_ADD]]]])

  return {
    dist, DIST_REFL, DIST_LZERO, DIST_RZERO, DIST_SYM, DIST_LADD, DIST_RADD,
    DIST_LADD_0, DIST_RADD_0, DIST_LMUL, DIST_RMUL, DIST_EQ_0, DIST_ELIM_THM,
    DIST_LE_CASES, DIST_ADDBOUND, DIST_TRIANGLE, DIST_ADD2, DIST_ADD2_REV,
    DIST_TRIANGLE_LE, DIST_TRIANGLES_LE, BOUNDS_LINEAR, BOUNDS_LINEAR_0,
    BOUNDS_DIVIDED, BOUNDS_NOTZERO, BOUNDS_IGNORE }

/-- The `nadd` type construction and the eight properties of
    nearly-multiplicative / nearly-additive functions (realax.ml 253-363).

    Field names match the OCaml identifiers exactly, in OCaml order.
    `nadd_abs`/`nadd_rep` are the two theorems returned by
    `new_basic_type_definition "nadd" ("mk_nadd","dest_nadd") is_nadd_0`. -/
structure NaddThms where
  /- Define type of nearly-multiplicative functions. This is equivalent to
     being nearly-additive, hence the name, but it is easier to work with this
     formulation rather than actually derive it from nearly-additivity.
     `is_nadd` (253). -/
  is_nadd            : thm
  /- The zero function is near-multiplicative (257). -/
  is_nadd_0          : thm
  /- `new_basic_type_definition "nadd" (...) is_nadd_0` (260). -/
  nadd_abs           : thm
  nadd_rep           : thm
  /- Properties of nearly-multiplicative / -additive functions (269-363). -/
  NADD_CAUCHY        : thm
  NADD_BOUND         : thm
  NADD_MULTIPLICATIVE : thm
  NADD_ADDITIVE      : thm
  NADD_SUC           : thm
  NADD_DIST_LEMMA    : thm
  NADD_DIST          : thm
  NADD_ALTMUL        : thm
  deriving Inhabited

/-- realax.ml 248-371: the type of nearly-multiplicative functions. -/
@[nospecialize]
def setupNadd [HolBase] (N : HolMath.Nums.NumsThms)
    (A1 : HolMath.Arith.ArithThms1) (A2 : HolMath.Arith.ArithThms2)
    (A3 : HolMath.Arith.ArithThms3) (A4 : HolMath.Arith.ArithThms4)
    (D : DistThms) (ETA_AX : thm)
    (NUM_CANCEL_CONV : ioconv) (ARITH : thm)
    (LE_IMP' : thm → IO (Except String thm))
    (new_definition' : term → IO (Except String thm))
    (new_basic_type_definition' : String → String → String → thm →
      IO (Except String (thm × thm)))
    (override_interface' : String → term → IO (Except String Unit)) :
    ExceptT String IO NaddThms := do
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let new_basic_type_definition (ty : String) (names : String × String) (th : thm) :
      ExceptT String IO (thm × thm) :=
    new_basic_type_definition' ty names.1 names.2 th
  let override_interface (p : String × String) : ExceptT String IO Unit := do
    override_interface' p.1 (← q p.2)
  let INDUCT_TAC := HolMath.Nums.INDUCT_TAC N.num_INDUCTION
  let LE_IMP (th : thm) : ExceptT String IO thm := LE_IMP' th
  let { ADD_CLAUSES, ADD_SYM, ADD_ASSOC, ADD_AC, ADD_EQ_0, ADD1, .. } := A1
  let { MULT_CLAUSES, MULT_SYM, LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB,
        MULT_ASSOC, MULT_AC, LE_0, .. } := A2
  let { LE_REFL, LE_TRANS, LE_CASES, .. } := A3
  let { LE_EXISTS, LE_ADD, LE_ADDR, LE_ADD_LCANCEL, LE_ADD2, LE_MULT_LCANCEL, .. } := A4
  let { DIST_REFL, DIST_SYM, DIST_LADD_0, DIST_LMUL, DIST_LE_CASES,
        DIST_ADDBOUND, DIST_TRIANGLE, DIST_ADD2, .. } := D
  let { EXISTS_REFL, .. } := HolBase.T

  /- Define type of nearly-multiplicative functions. This is equivalent to
     being nearly-additive, hence the name, but it is easier to work with this
     formulation rather than actually derive it from nearly-additivity. -/

  let is_nadd ← new_definition
   r"is_nadd x <=> (?B. !m n. dist(m * x(n),n * x(m)) <= B * (m + n))"

  let is_nadd_0 ← prove
   r"is_nadd (\n. 0)"
   (REWRITE_TAC [is_nadd, MULT_CLAUSES, DIST_REFL, LE_0])

  let (nadd_abs, nadd_rep) ←
    new_basic_type_definition "nadd" ("mk_nadd", "dest_nadd") is_nadd_0

  override_interface ("fn", r"dest_nadd")
  override_interface ("afn", r"mk_nadd")

  /- Properties of nearly-multiplicative / nearly-additive functions. -/

  let NADD_CAUCHY ← prove
   r"!x. ?B. !m n. dist(m * fn x n,n * fn x m) <= B * (m + n)"
   (REWRITE_TAC [← GSYM is_nadd, nadd_rep, nadd_abs, ETA_AX])

  let NADD_BOUND ← prove
   r"!x. ?A B. !n. fn x n <= A * n + B"
   (GEN_TAC THEN X_CHOOSE_TAC (← q r"B:num") (← SPEC (← q r"x:nadd") NADD_CAUCHY) THEN
    MAP_EVERY EXISTS_TAC [← q r"B + fn x 1", ← q r"B:num"] THEN GEN_TAC THEN
    POP_ASSUM (fun th => tactic_of do
      pure (MP_TAC (← SPECL [← q r"n:num", ← q r"1"] th))) THEN
    REWRITE_TAC [DIST_LE_CASES, MULT_CLAUSES] THEN
    DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← CONJUNCT2 th))) THEN
    REWRITE_TAC [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_CLAUSES] THEN
    REWRITE_TAC [ADD_AC, MULT_AC])

  let NADD_MULTIPLICATIVE ← prove
   r"!x. ?B. !m n. dist(fn x (m * n),m * fn x n) <= B * m + B"
   (GEN_TAC THEN X_CHOOSE_TAC (← q r"B:num") (← SPEC (← q r"x:nadd") NADD_CAUCHY) THEN
    EXISTS_TAC (← q r"B + fn x 0") THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"n = 0") THENL
     [MATCH_MP_TAC (← LE_IMP DIST_ADDBOUND) THEN
      ASM_REWRITE_TAC [MULT_CLAUSES, RIGHT_ADD_DISTRIB, MULT_AC] THEN
      REWRITE_TAC [LE_EXISTS] THEN CONV_TAC (ONCE_DEPTH_CONV NUM_CANCEL_CONV) THEN
      REWRITE_TAC [← GSYM EXISTS_REFL], UNDISCH_TAC (← q r"~(n = 0)")] THEN
    REWRITE_TAC [← TAUT (← q r"(~a ==> b) <=> a \/ b"), ← GSYM LE_MULT_LCANCEL,
                 DIST_LMUL] THEN
    REWRITE_TAC [MULT_ASSOC] THEN GEN_REWRITE_TAC
     (LAND_CONV o RAND_CONV o RAND_CONV o LAND_CONV) [MULT_SYM] THEN
    POP_ASSUM (fun th => tactic_of do pure (MATCH_MP_TAC (← LE_IMP th))) THEN
    REWRITE_TAC [LE_EXISTS, RIGHT_ADD_DISTRIB, LEFT_ADD_DISTRIB, MULT_AC] THEN
    CONV_TAC (ONCE_DEPTH_CONV NUM_CANCEL_CONV) THEN
    REWRITE_TAC [← GSYM EXISTS_REFL])

  let NADD_ADDITIVE ← prove
   r"!x. ?B. !m n. dist(fn x (m + n),fn x m + fn x n) <= B"
   (GEN_TAC THEN X_CHOOSE_TAC (← q r"B:num") (← SPEC (← q r"x:nadd") NADD_CAUCHY) THEN
    EXISTS_TAC (← q r"3 * B + fn x 0") THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"m + n = 0") THENL
     [RULE_ASSUM_TAC (REWRITE_RULE [ADD_EQ_0]) THEN ONCE_REWRITE_TAC [DIST_SYM] THEN
      ASM_REWRITE_TAC [ADD_CLAUSES, DIST_LADD_0, LE_ADDR],
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"3 * B") THEN
      REWRITE_TAC [LE_ADD] THEN UNDISCH_TAC (← q r"~(m + n = 0)")] THEN
    REWRITE_TAC [← TAUT (← q r"(~a ==> b) <=> a \/ b"), ← GSYM LE_MULT_LCANCEL] THEN
    REWRITE_TAC [DIST_LMUL, LEFT_ADD_DISTRIB] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [RIGHT_ADD_DISTRIB] THEN
    MATCH_MP_TAC (← LE_IMP DIST_ADD2) THEN
    SUBGOAL_THEN (← q r"(m + n) * 3 * B = B * (m + m + n) + B * (n + m + n)")
    SUBST1_TAC THENL
     [REWRITE_TAC [← SYM (← REWRITE_CONV [ARITH] (← q r"1 + 1 + 1"))] THEN
      REWRITE_TAC [RIGHT_ADD_DISTRIB, LEFT_ADD_DISTRIB, MULT_CLAUSES] THEN
      REWRITE_TAC [MULT_AC] THEN CONV_TAC NUM_CANCEL_CONV THEN REFL_TAC,
      MATCH_MP_TAC LE_ADD2 THEN ASM_REWRITE_TAC []])

  let NADD_SUC ← prove
   r"!x. ?B. !n. dist(fn x (SUC n),fn x n) <= B"
   (GEN_TAC THEN X_CHOOSE_TAC (← q r"B:num") (← SPEC (← q r"x:nadd") NADD_ADDITIVE) THEN
    EXISTS_TAC (← q r"B + fn x 1") THEN GEN_TAC THEN
    MATCH_MP_TAC (← LE_IMP DIST_TRIANGLE) THEN
    EXISTS_TAC (← q r"fn x n + fn x 1") THEN
    ASM_REWRITE_TAC [ADD1] THEN MATCH_MP_TAC LE_ADD2 THEN
    ASM_REWRITE_TAC [DIST_LADD_0, LE_REFL])

  let NADD_DIST_LEMMA ← prove
   r"!x. ?B. !m n. dist(fn x (m + n),fn x m) <= B * n"
   (GEN_TAC THEN X_CHOOSE_TAC (← q r"B:num") (← SPEC (← q r"x:nadd") NADD_SUC) THEN
    EXISTS_TAC (← q r"B:num") THEN GEN_TAC THEN
    INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES, DIST_REFL, LE_0] THEN
    MATCH_MP_TAC (← LE_IMP DIST_TRIANGLE) THEN
    EXISTS_TAC (← q r"fn x (m + n)") THEN
    REWRITE_TAC [ADD1, LEFT_ADD_DISTRIB] THEN
    GEN_REWRITE_TAC RAND_CONV [ADD_SYM] THEN
    MATCH_MP_TAC LE_ADD2 THEN ASM_REWRITE_TAC [← GSYM ADD1, MULT_CLAUSES])

  let NADD_DIST ← prove
   r"!x. ?B. !m n. dist(fn x m,fn x n) <= B * dist(m,n)"
   (GEN_TAC THEN X_CHOOSE_TAC (← q r"B:num") (← SPEC (← q r"x:nadd") NADD_DIST_LEMMA) THEN
    EXISTS_TAC (← q r"B:num") THEN REPEAT GEN_TAC THEN
    DISJ_CASES_THEN MP_TAC (← SPECL [← q r"m:num", ← q r"n:num"] LE_CASES) THEN
    DISCH_THEN (fun th => tactic_of do
      pure ((CHOOSE_THEN SUBST1_TAC) (← ONCE_REWRITE_RULE [LE_EXISTS] th))) THENL
     [ONCE_REWRITE_TAC [DIST_SYM], ALL_TAC] THEN
    ASM_REWRITE_TAC [DIST_LADD_0])

  let NADD_ALTMUL ← prove
   r"!x y. ?A B. !n. dist(n * fn x (fn y n),fn x n * fn y n) <= A * n + B"
   (REPEAT GEN_TAC THEN X_CHOOSE_TAC (← q r"B:num") (← SPEC (← q r"x:nadd") NADD_CAUCHY) THEN
    MP_TAC (← SPEC (← q r"y:nadd") NADD_BOUND) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"M:num") (X_CHOOSE_TAC (← q r"L:num"))) THEN
    MAP_EVERY EXISTS_TAC [← q r"B * (1 + M)", ← q r"B * L"] THEN GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [MULT_SYM] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"B * (n + fn y n)") THEN
    ASM_REWRITE_TAC [] THEN REWRITE_TAC [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB] THEN
    REWRITE_TAC [MULT_CLAUSES, ← GSYM ADD_ASSOC, LE_ADD_LCANCEL] THEN
    ASM_REWRITE_TAC [← GSYM LEFT_ADD_DISTRIB, ← GSYM MULT_ASSOC, LE_MULT_LCANCEL])

  return {
    is_nadd, is_nadd_0, nadd_abs, nadd_rep, NADD_CAUCHY, NADD_BOUND,
    NADD_MULTIPLICATIVE, NADD_ADDITIVE, NADD_SUC, NADD_DIST_LEMMA, NADD_DIST,
    NADD_ALTMUL }

/-- The equivalence relation `===` (realax.ml 366-388), the injection of the
    naturals `&` (393-415) and the (reflexive) ordering `<<=` (418-511).
    Field names match the OCaml identifiers exactly, in OCaml order.

    THREE `override_interface` calls are LOAD-BEARING and each MUST run before
    any quotation mentioning its symbol is parsed: `===` (366) before
    `nadd_eq` and every `x === y`; `&` (393) before `nadd_of_num` and every
    `&k`; `<<=` (418) before `nadd_le` and every `x <<= y`.  If an override
    had not run, the symbol would parse as a free VARIABLE and the theorem
    would be about something else.  The setup is sequenced so each override
    happens before its dependents.  The infix declarations for `===` and
    `<<=` live in the file head and are reproduced by
    `setupRealAxOverloads`, so they are NOT repeated here. -/
structure NaddOrderThms where
  /- Equivalence relation and proof it is one (366-388). -/
  nadd_eq            : thm
  NADD_EQ_REFL       : thm
  NADD_EQ_SYM        : thm
  NADD_EQ_TRANS      : thm
  /- Injection of the natural numbers (393-415). -/
  nadd_of_num        : thm
  NADD_OF_NUM        : thm
  NADD_OF_NUM_WELLDEF : thm
  NADD_OF_NUM_EQ     : thm
  /- (Reflexive) ordering and the only special property needed (418-511). -/
  nadd_le            : thm
  NADD_LE_WELLDEF_LEMMA : thm
  NADD_LE_WELLDEF    : thm
  NADD_LE_REFL       : thm
  NADD_LE_TRANS      : thm
  NADD_LE_ANTISYM    : thm
  NADD_LE_TOTAL_LEMMA : thm
  NADD_LE_TOTAL      : thm
  NADD_ARCH          : thm
  NADD_OF_NUM_LE     : thm
  deriving Inhabited

/-- realax.ml 373-497: the equivalence relation, the injection of the
    naturals, and the ordering. -/
@[nospecialize]
def setupNaddOrder [HolBase]
    (A1 : HolMath.Arith.ArithThms1) (A2 : HolMath.Arith.ArithThms2)
    (A3 : HolMath.Arith.ArithThms3) (A4 : HolMath.Arith.ArithThms4)
    (D : DistThms) (Na : NaddThms)
    (LE_IMP' : thm → IO (Except String thm))
    (new_definition' : term → IO (Except String thm))
    (override_interface' : String → term → IO (Except String Unit)) :
    ExceptT String IO NaddOrderThms := do
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let override_interface (p : String × String) : ExceptT String IO Unit := do
    override_interface' p.1 (← q p.2)
  let LE_IMP (th : thm) : ExceptT String IO thm := LE_IMP' th
  let { ADD_ASSOC, ADD_AC, .. } := A1
  let { MULT_SYM, LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_AC, LE_0, .. } := A2
  let { NOT_LE, NOT_LT, .. } := A3
  let { LE_ADD, LE_ADDR, LE_ADD_RCANCEL, LE_ADD2, LT_ADD2, LE_MULT_LCANCEL, .. } := A4
  let { DIST_REFL, DIST_SYM, DIST_RMUL, DIST_EQ_0, DIST_LE_CASES,
        DIST_TRIANGLE, BOUNDS_LINEAR, BOUNDS_LINEAR_0, .. } := D
  let { is_nadd, nadd_rep, NADD_CAUCHY, NADD_BOUND, .. } := Na
  let { FORALL_AND_THM, AND_FORALL_THM, LEFT_AND_EXISTS_THM,
        RIGHT_AND_EXISTS_THM, .. } := HolBase.T
  let { DE_MORGAN_THM, NOT_EXISTS_THM, NOT_FORALL_THM, .. } := HolBase.C

  /- Definition of the equivalence relation and proof that it *is* one. -/

  override_interface ("===", r"(nadd_eq):nadd->nadd->bool")

  let nadd_eq ← new_definition
   r"x === y <=> ?B. !n. dist(fn x n,fn y n) <= B"

  let NADD_EQ_REFL ← prove
   r"!x. x === x"
   (GEN_TAC THEN REWRITE_TAC [nadd_eq, DIST_REFL, LE_0])

  let NADD_EQ_SYM ← prove
   r"!x y. x === y <=> y === x"
   (REPEAT GEN_TAC THEN REWRITE_TAC [nadd_eq] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [DIST_SYM] THEN REFL_TAC)

  let NADD_EQ_TRANS ← prove
   r"!x y z. x === y /\ y === z ==> x === z"
   (REPEAT GEN_TAC THEN REWRITE_TAC [nadd_eq] THEN
    DISCH_THEN (CONJUNCTS_THEN2
      (X_CHOOSE_TAC (← q r"B1:num")) (X_CHOOSE_TAC (← q r"B2:num"))) THEN
    EXISTS_TAC (← q r"B1 + B2") THEN X_GEN_TAC (← q r"n:num") THEN
    MATCH_MP_TAC (← LE_IMP DIST_TRIANGLE) THEN EXISTS_TAC (← q r"fn y n") THEN
    MATCH_MP_TAC LE_ADD2 THEN ASM_REWRITE_TAC [])

  /- Injection of the natural numbers. -/

  override_interface ("&", r"nadd_of_num:num->nadd")

  let nadd_of_num ← new_definition
   r"&k = afn(\n. k * n)"

  let NADD_OF_NUM ← prove
   r"!k. fn(&k) = \n. k * n"
   (REWRITE_TAC [nadd_of_num, ← GSYM nadd_rep, is_nadd] THEN
    REWRITE_TAC [DIST_REFL, LE_0, MULT_AC])

  let NADD_OF_NUM_WELLDEF ← prove
   r"!m n. (m = n) ==> &m === &n"
   (REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_ACCEPT_TAC NADD_EQ_REFL)

  let NADD_OF_NUM_EQ ← prove
   r"!m n. (&m === &n) <=> (m = n)"
   (REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC [NADD_OF_NUM_WELLDEF] THEN
    REWRITE_TAC [nadd_eq, NADD_OF_NUM] THEN
    REWRITE_TAC [← GSYM DIST_RMUL, BOUNDS_LINEAR_0, DIST_EQ_0])

  /- Definition of (reflexive) ordering and the only special property needed. -/

  override_interface ("<<=", r"nadd_le:nadd->nadd->bool")

  let nadd_le ← new_definition
   r"x <<= y <=> ?B. !n. fn x n <= fn y n + B"

  let NADD_LE_WELLDEF_LEMMA ← prove
   r"!x x' y y'. x === x' /\ y === y' /\ x <<= y ==> x' <<= y'"
   (REPEAT GEN_TAC THEN REWRITE_TAC [nadd_eq, nadd_le] THEN
    REWRITE_TAC [DIST_LE_CASES, FORALL_AND_THM] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q r"B1:num")) MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q r"B2:num")) MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"B:num")) THEN
    EXISTS_TAC (← q r"(B2 + B) + B1") THEN X_GEN_TAC (← q r"n:num") THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (MATCH_MP_TAC (← LE_IMP (← CONJUNCT2 th)))) THEN
    REWRITE_TAC [ADD_ASSOC, LE_ADD_RCANCEL] THEN
    FIRST_ASSUM (fun th => tactic_of do pure (MATCH_MP_TAC (← LE_IMP th))) THEN
    ASM_REWRITE_TAC [LE_ADD_RCANCEL])

  let NADD_LE_WELLDEF ← prove
   r"!x x' y y'. x === x' /\ y === y' ==> (x <<= y <=> x' <<= y')"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC NADD_LE_WELLDEF_LEMMA THEN ASM_REWRITE_TAC [] THENL
     [MAP_EVERY EXISTS_TAC [← q r"x:nadd", ← q r"y:nadd"],
      MAP_EVERY EXISTS_TAC [← q r"x':nadd", ← q r"y':nadd"] THEN
      ONCE_REWRITE_TAC [NADD_EQ_SYM]] THEN
    ASM_REWRITE_TAC [])

  let NADD_LE_REFL ← prove
   r"!x. x <<= x"
   (REWRITE_TAC [nadd_le, LE_ADD])

  let NADD_LE_TRANS ← prove
   r"!x y z. x <<= y /\ y <<= z ==> x <<= z"
   (REPEAT GEN_TAC THEN REWRITE_TAC [nadd_le] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q r"B1:num")) MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"B2:num")) THEN
    EXISTS_TAC (← q r"B2 + B1") THEN GEN_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do pure (MATCH_MP_TAC (← LE_IMP th))) THEN
    ASM_REWRITE_TAC [ADD_ASSOC, LE_ADD_RCANCEL])

  let NADD_LE_ANTISYM ← prove
   r"!x y. x <<= y /\ y <<= x <=> (x === y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [nadd_le, nadd_eq, DIST_LE_CASES] THEN
    EQ_TAC THENL
     [DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q r"B1:num"))
        (X_CHOOSE_TAC (← q r"B2:num"))) THEN
      EXISTS_TAC (← q r"B1 + B2") THEN GEN_TAC THEN CONJ_TAC THEN
      FIRST_ASSUM (fun th => tactic_of do pure (MATCH_MP_TAC (← LE_IMP th))) THEN
      ASM_REWRITE_TAC [ADD_ASSOC, LE_ADD_RCANCEL, LE_ADD, LE_ADDR],
      DISCH_THEN (X_CHOOSE_TAC (← q r"B:num")) THEN
      CONJ_TAC THEN EXISTS_TAC (← q r"B:num") THEN ASM_REWRITE_TAC []])

  let NADD_LE_TOTAL_LEMMA ← prove
   r"!x y. ~(x <<= y) ==> !B. ?n. ~(n = 0) /\ fn y n + B < fn x n"
   (REPEAT GEN_TAC THEN REWRITE_TAC [nadd_le, NOT_FORALL_THM, NOT_EXISTS_THM] THEN
    REWRITE_TAC [NOT_LE] THEN DISCH_TAC THEN GEN_TAC THEN
    POP_ASSUM (fun th => tactic_of do
      pure ((X_CHOOSE_TAC (← q r"n:num")) (← SPEC (← q r"B + fn x 0") th))) THEN
    EXISTS_TAC (← q r"n:num") THEN POP_ASSUM MP_TAC THEN
    ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [NOT_LT, ADD_ASSOC, LE_ADDR] THEN
    CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC [NOT_LT] THEN
    DISCH_THEN (fun th => tactic_of do pure (MATCH_MP_TAC (← LE_IMP th))) THEN
    REWRITE_TAC [ADD_ASSOC, LE_ADD])

  let NADD_LE_TOTAL ← prove
   r"!x y. x <<= y \/ y <<= x"
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [← TAUT (← q r"a <=> ~ ~ a")] THEN
    X_CHOOSE_TAC (← q r"B1:num") (← SPEC (← q r"x:nadd") NADD_CAUCHY) THEN
    X_CHOOSE_TAC (← q r"B2:num") (← SPEC (← q r"y:nadd") NADD_CAUCHY) THEN
    PURE_ONCE_REWRITE_TAC [DE_MORGAN_THM] THEN
    DISCH_THEN (fun th => tactic_of do
      pure (MP_TAC (← end_itlist CONJ
        (← (CONJUNCTS th).mapM (MATCH_MP NADD_LE_TOTAL_LEMMA))))) THEN
    REWRITE_TAC [AND_FORALL_THM] THEN
    DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"B1 + B2") th))) THEN
    REWRITE_TAC [RIGHT_AND_EXISTS_THM] THEN REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"m:num") (X_CHOOSE_THEN (← q r"n:num") MP_TAC)) THEN
    (← do
      let it ← ITAUT (← q r"(~a /\ b) /\ (~c /\ d) ==> ~(c \/ ~b) /\ ~(a \/ ~d)")
      pure (DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← MATCH_MP it th))))) THEN
    REWRITE_TAC [NOT_LT, ← GSYM LE_MULT_LCANCEL] THEN REWRITE_TAC [NOT_LE] THEN
    DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← MATCH_MP LT_ADD2 th))) THEN
    REWRITE_TAC [NOT_LT] THEN
    REWRITE_TAC [LEFT_ADD_DISTRIB] THEN
    ONCE_REWRITE_TAC [← AC ADD_AC
      (← q r"(a + b + c) + (d + e + f) = (d + b + e) + (a + c + f)")] THEN
    MATCH_MP_TAC LE_ADD2 THEN REWRITE_TAC [← GSYM RIGHT_ADD_DISTRIB] THEN
    CONJ_TAC THEN GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [MULT_SYM] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [DIST_LE_CASES]) THEN ASM_REWRITE_TAC [])

  let NADD_ARCH ← prove
   r"!x. ?n. x <<= &n"
   (REWRITE_TAC [nadd_le, NADD_OF_NUM, NADD_BOUND])

  let NADD_OF_NUM_LE ← prove
   r"!m n. (&m <<= &n) <=> m <= n"
   (REPEAT GEN_TAC THEN REWRITE_TAC [nadd_le, NADD_OF_NUM] THEN
    REWRITE_TAC [BOUNDS_LINEAR])

  return {
    nadd_eq, NADD_EQ_REFL, NADD_EQ_SYM, NADD_EQ_TRANS, nadd_of_num,
    NADD_OF_NUM, NADD_OF_NUM_WELLDEF, NADD_OF_NUM_EQ, nadd_le,
    NADD_LE_WELLDEF_LEMMA, NADD_LE_WELLDEF, NADD_LE_REFL, NADD_LE_TRANS,
    NADD_LE_ANTISYM, NADD_LE_TOTAL_LEMMA, NADD_LE_TOTAL, NADD_ARCH,
    NADD_OF_NUM_LE }

/-- Addition on `nadd` (realax.ml 514-597), multiplication (606-611) and the
    properties of multiplication (640-694).  Field names match the OCaml
    identifiers exactly, in OCaml order.

    TWO `override_interface` calls are LOAD-BEARING: `++` (514) before
    `nadd_add` and every `x ++ y`; `**` (606) before `nadd_mul` and every
    `x ** y`.  If an override had not run the symbol would parse as a free
    VARIABLE and the theorem would be about something else.  The setup is
    sequenced so each override runs before its dependents' quotations are
    parsed.  The infix declarations for `++` and `**` live in the file head
    and are reproduced by `setupRealAxOverloads`, so they are NOT repeated
    here; this setup REQUIRES `setupRealAxOverloads` to have run first. -/
structure NaddArithThms where
  /- Addition (514-530). -/
  nadd_add           : thm
  NADD_ADD           : thm
  NADD_ADD_WELLDEF   : thm
  /- Basic properties of addition (542-597). -/
  NADD_ADD_SYM       : thm
  NADD_ADD_ASSOC     : thm
  NADD_ADD_LID       : thm
  NADD_ADD_LCANCEL   : thm
  NADD_LE_ADD        : thm
  NADD_LE_EXISTS     : thm
  NADD_OF_NUM_ADD    : thm
  /- Multiplication (606-611). -/
  nadd_mul           : thm
  NADD_MUL           : thm
  /- Properties of multiplication (640-694). -/
  NADD_MUL_SYM       : thm
  NADD_MUL_ASSOC     : thm
  NADD_MUL_LID       : thm
  NADD_LDISTRIB      : thm
  NADD_MUL_WELLDEF_LEMMA : thm
  NADD_MUL_WELLDEF   : thm
  NADD_OF_NUM_MUL    : thm
  deriving Inhabited

/-- realax.ml 512-699: addition and multiplication of nadds. -/
@[nospecialize]
def setupNaddArith [HolBase]
    (A1 : HolMath.Arith.ArithThms1) (A2 : HolMath.Arith.ArithThms2)
    (A3 : HolMath.Arith.ArithThms3) (A4 : HolMath.Arith.ArithThms4)
    (D : DistThms) (Na : NaddThms) (O : NaddOrderThms) (ETA_AX : thm)
    (LE_IMP' : thm → IO (Except String thm))
    (new_definition' : term → IO (Except String thm))
    (override_interface' : String → term → IO (Except String Unit)) :
    ExceptT String IO NaddArithThms := do
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let override_interface (p : String × String) : ExceptT String IO Unit := do
    override_interface' p.1 (← q p.2)
  let LE_IMP (th : thm) : ExceptT String IO thm := LE_IMP' th
  let { ADD_CLAUSES, ADD_SYM, ADD_ASSOC, ADD_AC, .. } := A1
  let { MULT_CLAUSES, MULT_SYM, LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB,
        MULT_ASSOC, LE_0, .. } := A2
  let { LE_REFL, LE_TRANS, EQ_IMP_LE, .. } := A3
  let { LE_EXISTS, LE_ADD, LE_ADD2, LE_MULT_LCANCEL, .. } := A4
  let { DIST_REFL, DIST_SYM, DIST_LADD, DIST_RADD_0, DIST_LMUL, DIST_ADDBOUND,
        DIST_TRIANGLE, DIST_ADD2, DIST_ADD2_REV, BOUNDS_DIVIDED,
        BOUNDS_NOTZERO, .. } := D
  let { is_nadd, nadd_abs, nadd_rep, NADD_CAUCHY, NADD_MULTIPLICATIVE,
        NADD_ADDITIVE, NADD_DIST, NADD_ALTMUL, .. } := Na
  let { nadd_eq, NADD_EQ_REFL, NADD_EQ_TRANS, NADD_OF_NUM, nadd_le, .. } := O
  let { SKOLEM_THM, .. } := HolBase.C

  /- Addition. -/

  override_interface ("++", r"nadd_add:nadd->nadd->nadd")

  let nadd_add ← new_definition
   r"x ++ y = afn(\n. fn x n + fn y n)"

  let NADD_ADD ← prove
   r"!x y. fn(x ++ y) = \n. fn x n + fn y n"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [nadd_add, ← GSYM nadd_rep, is_nadd] THEN
    X_CHOOSE_TAC (← q r"B1:num") (← SPEC (← q r"x:nadd") NADD_CAUCHY) THEN
    X_CHOOSE_TAC (← q r"B2:num") (← SPEC (← q r"y:nadd") NADD_CAUCHY) THEN
    EXISTS_TAC (← q r"B1 + B2") THEN MAP_EVERY X_GEN_TAC [← q r"m:num", ← q r"n:num"] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [LEFT_ADD_DISTRIB] THEN
    MATCH_MP_TAC (← LE_IMP DIST_ADD2) THEN REWRITE_TAC [RIGHT_ADD_DISTRIB] THEN
    MATCH_MP_TAC LE_ADD2 THEN ASM_REWRITE_TAC [])

  let NADD_ADD_WELLDEF ← prove
   r"!x x' y y'. x === x' /\ y === y' ==> (x ++ y === x' ++ y')"
   (REPEAT GEN_TAC THEN REWRITE_TAC [nadd_eq, NADD_ADD] THEN
    DISCH_THEN (CONJUNCTS_THEN2
      (X_CHOOSE_TAC (← q r"B1:num")) (X_CHOOSE_TAC (← q r"B2:num"))) THEN
    EXISTS_TAC (← q r"B1 + B2") THEN X_GEN_TAC (← q r"n:num") THEN
    MATCH_MP_TAC (← LE_IMP DIST_ADD2) THEN
    MATCH_MP_TAC LE_ADD2 THEN ASM_REWRITE_TAC [])

  /- Basic properties of addition. -/

  let NADD_ADD_SYM ← prove
   r"!x y. (x ++ y) === (y ++ x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [nadd_add] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ADD_SYM] THEN
    REWRITE_TAC [NADD_EQ_REFL])

  let NADD_ADD_ASSOC ← prove
   r"!x y z. (x ++ (y ++ z)) === ((x ++ y) ++ z)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [nadd_add] THEN
    REWRITE_TAC [NADD_ADD, ADD_ASSOC, NADD_EQ_REFL])

  let NADD_ADD_LID ← prove
   r"!x. (&0 ++ x) === x"
   (GEN_TAC THEN REWRITE_TAC [nadd_eq, NADD_ADD, NADD_OF_NUM] THEN
    REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES, DIST_REFL, LE_0])

  let NADD_ADD_LCANCEL ← prove
   r"!x y z. (x ++ y) === (x ++ z) ==> y === z"
   (REPEAT GEN_TAC THEN REWRITE_TAC [nadd_eq, NADD_ADD, DIST_LADD])

  let NADD_LE_ADD ← prove
   r"!x y. x <<= (x ++ y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [nadd_le, NADD_ADD] THEN
    EXISTS_TAC (← q r"0") THEN REWRITE_TAC [ADD_CLAUSES, LE_ADD])

  let NADD_LE_EXISTS ← prove
   r"!x y. x <<= y ==> ?d. y === x ++ d"
   (REPEAT GEN_TAC THEN REWRITE_TAC [nadd_le] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"B:num") MP_TAC) THEN
    REWRITE_TAC [LE_EXISTS, SKOLEM_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"d:num->num")
      (fun th => tactic_of do pure (ASSUME_TAC (← GSYM th)))) THEN
    EXISTS_TAC (← q r"afn d") THEN REWRITE_TAC [nadd_eq, NADD_ADD] THEN
    EXISTS_TAC (← q r"B:num") THEN X_GEN_TAC (← q r"n:num") THEN
    SUBGOAL_THEN (← q r"fn(afn d) = d") SUBST1_TAC THENL
     [REWRITE_TAC [← GSYM nadd_rep, is_nadd] THEN
      X_CHOOSE_TAC (← q r"B1:num") (← SPEC (← q r"x:nadd") NADD_CAUCHY) THEN
      X_CHOOSE_TAC (← q r"B2:num") (← SPEC (← q r"y:nadd") NADD_CAUCHY) THEN
      EXISTS_TAC (← q r"B1 + (B2 + B)") THEN REPEAT GEN_TAC THEN
      MATCH_MP_TAC (← LE_IMP DIST_ADD2_REV) THEN
      MAP_EVERY EXISTS_TAC [← q r"m * fn x n", ← q r"n * fn x m"] THEN
      ONCE_REWRITE_TAC [RIGHT_ADD_DISTRIB] THEN
      GEN_REWRITE_TAC RAND_CONV [ADD_SYM] THEN
      MATCH_MP_TAC LE_ADD2 THEN ASM_REWRITE_TAC [] THEN
      ONCE_REWRITE_TAC [ADD_SYM] THEN
      ASM_REWRITE_TAC [← GSYM LEFT_ADD_DISTRIB] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [LEFT_ADD_DISTRIB] THEN
      MATCH_MP_TAC (← LE_IMP DIST_ADD2) THEN REWRITE_TAC [RIGHT_ADD_DISTRIB] THEN
      GEN_REWRITE_TAC RAND_CONV [ADD_SYM] THEN MATCH_MP_TAC LE_ADD2 THEN
      ONCE_REWRITE_TAC [ADD_SYM] THEN ASM_REWRITE_TAC [] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
      REWRITE_TAC [← GSYM DIST_LMUL, DIST_ADDBOUND, LE_MULT_LCANCEL],
      ASM_REWRITE_TAC [DIST_RADD_0, LE_REFL]])

  let NADD_OF_NUM_ADD ← prove
   r"!m n. &m ++ &n === &(m + n)"
   (REWRITE_TAC [nadd_eq, NADD_OF_NUM, NADD_ADD] THEN
    REWRITE_TAC [RIGHT_ADD_DISTRIB, DIST_REFL, LE_0])

  /- Multiplication. -/

  override_interface ("**", r"nadd_mul:nadd->nadd->nadd")

  let nadd_mul ← new_definition
   r"x ** y = afn(\n. fn x (fn y n))"

  let NADD_MUL ← prove
   r"!x y. fn(x ** y) = \n. fn x (fn y n)"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [nadd_mul, ← GSYM nadd_rep, is_nadd] THEN
    X_CHOOSE_TAC (← q r"B:num") (← SPEC (← q r"y:nadd") NADD_CAUCHY) THEN
    X_CHOOSE_TAC (← q r"C:num") (← SPEC (← q r"x:nadd") NADD_DIST) THEN
    X_CHOOSE_TAC (← q r"D:num") (← SPEC (← q r"x:nadd") NADD_MULTIPLICATIVE) THEN
    MATCH_MP_TAC BOUNDS_NOTZERO THEN
    REWRITE_TAC [MULT_CLAUSES, DIST_REFL] THEN
    MAP_EVERY EXISTS_TAC [← q r"D + C * B", ← q r"D + D"] THEN
    REPEAT GEN_TAC THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC (← q r"(D * m + D) + (D * n + D) + C * B * (m + n)") THEN CONJ_TAC THENL
     [MATCH_MP_TAC (← LE_IMP DIST_TRIANGLE) THEN
      EXISTS_TAC (← q r"fn x (m * fn y n)") THEN
      MATCH_MP_TAC LE_ADD2 THEN
      ONCE_REWRITE_TAC [DIST_SYM] THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC (← LE_IMP DIST_TRIANGLE) THEN
      EXISTS_TAC (← q r"fn x (n * fn y m)") THEN
      MATCH_MP_TAC LE_ADD2 THEN
      ONCE_REWRITE_TAC [DIST_SYM] THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC (← q r"C * dist(m * fn y n,n * fn y m)") THEN
      ASM_REWRITE_TAC [LE_MULT_LCANCEL],
      MATCH_MP_TAC EQ_IMP_LE THEN
      REWRITE_TAC [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_ASSOC, ADD_AC]])

  /- Properties of multiplication. -/

  let NADD_MUL_SYM ← prove
   r"!x y. (x ** y) === (y ** x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [nadd_eq, NADD_MUL] THEN
    X_CHOOSE_THEN (← q r"A1:num") MP_TAC
      (← SPECL [← q r"x:nadd", ← q r"y:nadd"] NADD_ALTMUL) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"B1:num")) THEN
    X_CHOOSE_THEN (← q r"A2:num") MP_TAC
      (← SPECL [← q r"y:nadd", ← q r"x:nadd"] NADD_ALTMUL) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"B2:num")) THEN REWRITE_TAC [BOUNDS_DIVIDED] THEN
    REWRITE_TAC [DIST_LMUL] THEN MAP_EVERY EXISTS_TAC [← q r"A1 + A2", ← q r"B1 + B2"] THEN
    GEN_TAC THEN REWRITE_TAC [RIGHT_ADD_DISTRIB] THEN
    ONCE_REWRITE_TAC [← AC ADD_AC (← q r"(a + b) + (c + d) = (a + c) + (b + d)")] THEN
    MATCH_MP_TAC (← LE_IMP DIST_TRIANGLE) THEN
    EXISTS_TAC (← q r"fn x n * fn y n") THEN
    MATCH_MP_TAC LE_ADD2 THEN ASM_REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [DIST_SYM] THEN
    GEN_REWRITE_TAC (LAND_CONV o funpow 2 RAND_CONV) [MULT_SYM] THEN
    ASM_REWRITE_TAC [])

  let NADD_MUL_ASSOC ← prove
   r"!x y z. (x ** (y ** z)) === ((x ** y) ** z)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [nadd_mul] THEN
    REWRITE_TAC [NADD_MUL, NADD_EQ_REFL])

  let NADD_MUL_LID ← prove
   r"!x. (&1 ** x) === x"
   (REWRITE_TAC [NADD_OF_NUM, nadd_mul, MULT_CLAUSES] THEN
    REWRITE_TAC [nadd_abs, NADD_EQ_REFL, ETA_AX])

  let NADD_LDISTRIB ← prove
   r"!x y z. x ** (y ++ z) === (x ** y) ++ (x ** z)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [nadd_eq] THEN
    REWRITE_TAC [NADD_ADD, NADD_MUL] THEN
    X_CHOOSE_TAC (← q r"B:num") (← SPEC (← q r"x:nadd") NADD_ADDITIVE) THEN
    EXISTS_TAC (← q r"B:num") THEN ASM_REWRITE_TAC [])

  let NADD_MUL_WELLDEF_LEMMA ← prove
   r"!x y y'. y === y' ==> (x ** y) === (x ** y')"
   (REPEAT GEN_TAC THEN REWRITE_TAC [nadd_eq, NADD_MUL] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"B1:num")) THEN
    X_CHOOSE_TAC (← q r"B2:num") (← SPEC (← q r"x:nadd") NADD_DIST) THEN
    EXISTS_TAC (← q r"B2 * B1") THEN X_GEN_TAC (← q r"n:num") THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC (← q r"B2 * dist(fn y n,fn y' n)") THEN
    ASM_REWRITE_TAC [LE_MULT_LCANCEL])

  let NADD_MUL_WELLDEF ← prove
   r"!x x' y y'. x === x' /\ y === y'
               ==> (x ** y) === (x' ** y')"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC NADD_EQ_TRANS THEN
    EXISTS_TAC (← q r"x' ** y") THEN CONJ_TAC THENL
     [MATCH_MP_TAC NADD_EQ_TRANS THEN EXISTS_TAC (← q r"y ** x'") THEN
      REWRITE_TAC [NADD_MUL_SYM] THEN MATCH_MP_TAC NADD_EQ_TRANS THEN
      EXISTS_TAC (← q r"y ** x") THEN REWRITE_TAC [NADD_MUL_SYM], ALL_TAC] THEN
    MATCH_MP_TAC NADD_MUL_WELLDEF_LEMMA THEN ASM_REWRITE_TAC [])

  let NADD_OF_NUM_MUL ← prove
   r"!m n. &m ** &n === &(m * n)"
   (REWRITE_TAC [nadd_eq, NADD_OF_NUM, NADD_MUL] THEN
    REWRITE_TAC [MULT_ASSOC, DIST_REFL, LE_0])

  return {
    nadd_add, NADD_ADD, NADD_ADD_WELLDEF, NADD_ADD_SYM, NADD_ADD_ASSOC,
    NADD_ADD_LID, NADD_ADD_LCANCEL, NADD_LE_ADD, NADD_LE_EXISTS,
    NADD_OF_NUM_ADD, nadd_mul, NADD_MUL, NADD_MUL_SYM, NADD_MUL_ASSOC,
    NADD_MUL_LID, NADD_LDISTRIB, NADD_MUL_WELLDEF_LEMMA, NADD_MUL_WELLDEF,
    NADD_OF_NUM_MUL }

/-- The handy lemmas (realax.ml 703-746), the Archimedean property in a more
    useful form (754-802) and completeness (823-929).  Field names match the
    OCaml identifiers exactly, in OCaml order.

    NADD_COMPLETE (823) is a ~105-line proof, the hardest single item in the
    file. -/
structure NaddCompleteThms where
  /- A few handy lemmas (703-746). -/
  NADD_LE_0        : thm
  NADD_EQ_IMP_LE   : thm
  NADD_LE_LMUL     : thm
  NADD_LE_RMUL     : thm
  NADD_LE_RADD     : thm
  NADD_LE_LADD     : thm
  NADD_RDISTRIB    : thm
  /- The Archimedean property in a more useful form (754-802). -/
  NADD_ARCH_MULT   : thm
  NADD_ARCH_ZERO   : thm
  NADD_ARCH_LEMMA  : thm
  /- Completeness (823-929). -/
  NADD_COMPLETE    : thm
  deriving Inhabited

/-- realax.ml 700-926: a few handy lemmas, the Archimedean property, and
    completeness. -/
@[nospecialize]
def setupNaddComplete [HolBase]
    (A1 : HolMath.Arith.ArithThms1) (A2 : HolMath.Arith.ArithThms2)
    (A3 : HolMath.Arith.ArithThms3) (A4 : HolMath.Arith.ArithThms4)
    (D : DistThms) (Na : NaddThms) (O : NaddOrderThms) (M : NaddArithThms)
    (MESON_TAC ASM_MESON_TAC : List thm → tactic) :
    ExceptT String IO NaddCompleteThms := do
  let { ADD_CLAUSES, ADD_SYM, ADD_ASSOC, ADD1, .. } := A1
  let { MULT_SUC, MULT_CLAUSES, MULT_SYM, LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB,
        MULT_2, LE_SUC_LT, LE_0, .. } := A2
  let { LT_REFL, LE_TRANS, NOT_LE, LT_IMP_LE, .. } := A3
  let { LE_ADD, LE_ADD_LCANCEL, LE_ADD_RCANCEL, LE_MULT_RCANCEL, num_MAX, .. } := A4
  let { DIST_RZERO, DIST_LE_CASES, BOUNDS_IGNORE, .. } := D
  let { is_nadd, nadd_rep, NADD_CAUCHY, .. } := Na
  let { nadd_eq, NADD_EQ_REFL, NADD_EQ_SYM, NADD_EQ_TRANS, NADD_OF_NUM,
        nadd_le, NADD_LE_WELLDEF, NADD_LE_TRANS, NADD_LE_ANTISYM,
        NADD_LE_TOTAL, NADD_ARCH, NADD_OF_NUM_LE, .. } := O
  let { NADD_ADD, NADD_ADD_WELLDEF, NADD_ADD_SYM, NADD_ADD_LID, NADD_LE_ADD,
        NADD_LE_EXISTS, NADD_OF_NUM_ADD, NADD_MUL, NADD_MUL_SYM,
        NADD_MUL_ASSOC, NADD_MUL_LID, NADD_LDISTRIB, NADD_MUL_WELLDEF,
        NADD_OF_NUM_MUL, .. } := M
  let { SWAP_FORALL_THM, FORALL_AND_THM, .. } := HolBase.T
  let { NOT_EXISTS_THM, NOT_FORALL_THM, SKOLEM_THM, .. } := HolBase.C

  /- A few handy lemmas. -/

  let NADD_LE_0 ← prove
   r"!x. &0 <<= x"
   (GEN_TAC THEN
    REWRITE_TAC [nadd_le, NADD_OF_NUM, MULT_CLAUSES, LE_0])

  let NADD_EQ_IMP_LE ← prove
   r"!x y. x === y ==> x <<= y"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [nadd_eq, nadd_le, DIST_LE_CASES] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"B:num")) THEN EXISTS_TAC (← q r"B:num") THEN
    ASM_REWRITE_TAC [])

  let NADD_LE_LMUL ← prove
   r"!x y z. y <<= z ==> (x ** y) <<= (x ** z)"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (fun th => tactic_of do
      pure ((X_CHOOSE_TAC (← q r"d:nadd")) (← MATCH_MP NADD_LE_EXISTS th))) THEN
    MATCH_MP_TAC NADD_LE_TRANS THEN
    EXISTS_TAC (← q r"x ** y ++ x ** d") THEN REWRITE_TAC [NADD_LE_ADD] THEN
    MATCH_MP_TAC NADD_EQ_IMP_LE THEN
    MATCH_MP_TAC NADD_EQ_TRANS THEN
    EXISTS_TAC (← q r"x ** (y ++ d)") THEN
    ONCE_REWRITE_TAC [NADD_EQ_SYM] THEN
    REWRITE_TAC [NADD_LDISTRIB] THEN
    MATCH_MP_TAC NADD_MUL_WELLDEF THEN
    ASM_REWRITE_TAC [NADD_EQ_REFL])

  let NADD_LE_RMUL ← prove
   r"!x y z. x <<= y ==> (x ** z) <<= (y ** z)"
   (MESON_TAC [NADD_LE_LMUL, NADD_LE_WELLDEF, NADD_MUL_SYM])

  let NADD_LE_RADD ← prove
   r"!x y z. x ++ z <<= y ++ z <=> x <<= y"
   (REPEAT GEN_TAC THEN REWRITE_TAC [nadd_le, NADD_ADD] THEN
    GEN_REWRITE_TAC (LAND_CONV o funpow 2 BINDER_CONV o RAND_CONV)
      [ADD_SYM] THEN
    REWRITE_TAC [ADD_ASSOC, LE_ADD_RCANCEL] THEN
    GEN_REWRITE_TAC (LAND_CONV o funpow 2 BINDER_CONV o RAND_CONV)
      [ADD_SYM] THEN REFL_TAC)

  let NADD_LE_LADD ← prove
   r"!x y z. x ++ y <<= x ++ z <=> y <<= z"
   (MESON_TAC [NADD_LE_RADD, NADD_ADD_SYM, NADD_LE_WELLDEF])

  let NADD_RDISTRIB ← prove
   r"!x y z. (x ++ y) ** z === x ** z ++ y ** z"
   (MESON_TAC [NADD_LDISTRIB, NADD_MUL_SYM, NADD_ADD_WELLDEF,
      NADD_EQ_TRANS, NADD_EQ_REFL, NADD_EQ_SYM])

  /- The Archimedean property in a more useful form. -/

  let NADD_ARCH_MULT ← prove
   r"!x k. ~(x === &0) ==> ?N. &k <<= &N ** x"
   (REPEAT GEN_TAC THEN REWRITE_TAC [nadd_eq, nadd_le, NOT_EXISTS_THM] THEN
    X_CHOOSE_TAC (← q r"B:num") (← SPEC (← q r"x:nadd") NADD_CAUCHY) THEN
    DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"B + k") th))) THEN
    REWRITE_TAC [NOT_FORALL_THM, NADD_OF_NUM] THEN
    REWRITE_TAC [MULT_CLAUSES, DIST_RZERO, NOT_LE] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"N:num")) THEN
    MAP_EVERY EXISTS_TAC [← q r"N:num", ← q r"B * N"] THEN X_GEN_TAC (← q r"i:num") THEN
    REWRITE_TAC [NADD_MUL, NADD_OF_NUM] THEN
    MATCH_MP_TAC (← GEN_ALL (← EQ_IMP_RULE (← SPEC_ALL LE_ADD_RCANCEL)).1) THEN
    EXISTS_TAC (← q r"B * i") THEN
    REWRITE_TAC [← GSYM ADD_ASSOC, ← GSYM LEFT_ADD_DISTRIB] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"i * fn x N") THEN
    RULE_ASSUM_TAC (REWRITE_RULE [DIST_LE_CASES]) THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [← GSYM RIGHT_ADD_DISTRIB] THEN
    GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN
    REWRITE_TAC [LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
    MATCH_MP_TAC LT_IMP_LE THEN ONCE_REWRITE_TAC [ADD_SYM] THEN
    FIRST_ASSUM ACCEPT_TAC)

  let NADD_ARCH_ZERO ← prove
   r"!x k. (!n. &n ** x <<= k) ==> (x === &0)"
   (REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN DISCH_TAC THEN
    REWRITE_TAC [NOT_FORALL_THM] THEN
    X_CHOOSE_TAC (← q r"p:num") (← SPEC (← q r"k:nadd") NADD_ARCH) THEN
    FIRST_ASSUM (fun th => tactic_of do pure (MP_TAC (← MATCH_MP NADD_ARCH_MULT th))) THEN
    DISCH_THEN (fun th => tactic_of do
      pure ((X_CHOOSE_TAC (← q r"N:num")) (← SPEC (← q r"p:num") th))) THEN
    EXISTS_TAC (← q r"N + 1") THEN DISCH_TAC THEN UNDISCH_TAC (← q r"~(x === &0)") THEN
    REWRITE_TAC [← GSYM NADD_LE_ANTISYM, NADD_LE_0] THEN
    MATCH_MP_TAC (← GEN_ALL (← EQ_IMP_RULE (← SPEC_ALL NADD_LE_RADD)).1) THEN
    EXISTS_TAC (← q r"&N ** x") THEN MATCH_MP_TAC NADD_LE_TRANS THEN
    EXISTS_TAC (← q r"k:nadd") THEN CONJ_TAC THENL
     [SUBGOAL_THEN (← q r"&(N + 1) ** x === x ++ &N ** x") MP_TAC THENL
       [ONCE_REWRITE_TAC [ADD_SYM] THEN
        MATCH_MP_TAC NADD_EQ_TRANS THEN
        EXISTS_TAC (← q r"&1 ** x ++ &N ** x") THEN CONJ_TAC THENL
         [MATCH_MP_TAC NADD_EQ_TRANS THEN
          EXISTS_TAC (← q r"(&1 ++ &N) ** x") THEN CONJ_TAC THENL
           [MESON_TAC [NADD_OF_NUM_ADD, NADD_MUL_WELLDEF, NADD_EQ_REFL,
              NADD_EQ_SYM],
            MESON_TAC [NADD_RDISTRIB, NADD_MUL_SYM, NADD_EQ_SYM, NADD_EQ_TRANS]],
          MESON_TAC [NADD_ADD_WELLDEF, NADD_EQ_REFL, NADD_MUL_LID]],
        ASM_MESON_TAC [NADD_LE_WELLDEF, NADD_EQ_REFL]],
      ASM_MESON_TAC [NADD_LE_TRANS, NADD_LE_WELLDEF, NADD_EQ_REFL,
        NADD_ADD_LID]])

  let NADD_ARCH_LEMMA ← prove
   r"!x y z. (!n. &n ** x <<= &n ** y ++ z) ==> x <<= y"
   (REPEAT STRIP_TAC THEN
    DISJ_CASES_TAC (← SPECL [← q r"x:nadd", ← q r"y:nadd"] NADD_LE_TOTAL) THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure ((X_CHOOSE_TAC (← q r"d:nadd")) (← MATCH_MP NADD_LE_EXISTS th))) THEN
    MATCH_MP_TAC NADD_EQ_IMP_LE THEN
    MATCH_MP_TAC NADD_EQ_TRANS THEN EXISTS_TAC (← q r"y ++ d") THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC NADD_EQ_TRANS THEN EXISTS_TAC (← q r"y ++ &0") THEN CONJ_TAC THENL
     [MATCH_MP_TAC NADD_ADD_WELLDEF THEN REWRITE_TAC [NADD_EQ_REFL] THEN
      MATCH_MP_TAC NADD_ARCH_ZERO THEN EXISTS_TAC (← q r"z:nadd") THEN
      ASM_MESON_TAC [NADD_MUL_WELLDEF, NADD_LE_WELLDEF, NADD_LDISTRIB,
        NADD_LE_LADD, NADD_EQ_REFL],
      ASM_MESON_TAC [NADD_ADD_LID, NADD_ADD_WELLDEF, NADD_EQ_TRANS,
        NADD_ADD_SYM]])

  /- Completeness. -/

  let NADD_COMPLETE ← prove
   r"!P. (?x. P x) /\ (?M. !x. P x ==> x <<= M) ==>
       ?M. (!x. P x ==> x <<= M) /\
           !M'. (!x. P x ==> x <<= M') ==> M <<= M'"
   (GEN_TAC THEN DISCH_THEN
      (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q r"a:nadd")) (X_CHOOSE_TAC (← q r"m:nadd"))) THEN
    SUBGOAL_THEN
      (← q r"!n. ?r. (?x. P x /\ &r <<= &n ** x) /\
             !r'. (?x. P x /\ &r' <<= &n ** x) ==> r' <= r") MP_TAC THENL
     [GEN_TAC THEN REWRITE_TAC [← GSYM num_MAX] THEN CONJ_TAC THENL
       [MAP_EVERY EXISTS_TAC [← q r"0", ← q r"a:nadd"] THEN ASM_REWRITE_TAC [NADD_LE_0],
        X_CHOOSE_TAC (← q r"N:num") (← SPEC (← q r"m:nadd") NADD_ARCH) THEN
        EXISTS_TAC (← q r"n * N") THEN X_GEN_TAC (← q r"p:num") THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"w:nadd") STRIP_ASSUME_TAC) THEN
        ONCE_REWRITE_TAC [← GSYM NADD_OF_NUM_LE] THEN
        MATCH_MP_TAC NADD_LE_TRANS THEN EXISTS_TAC (← q r"&n ** w") THEN
        ASM_REWRITE_TAC [] THEN MATCH_MP_TAC NADD_LE_TRANS THEN
        EXISTS_TAC (← q r"&n ** &N") THEN CONJ_TAC THENL
         [MATCH_MP_TAC NADD_LE_LMUL THEN MATCH_MP_TAC NADD_LE_TRANS THEN
          EXISTS_TAC (← q r"m:nadd") THEN ASM_REWRITE_TAC [] THEN
          FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
          MATCH_MP_TAC NADD_EQ_IMP_LE THEN
          MATCH_ACCEPT_TAC NADD_OF_NUM_MUL]],
      ONCE_REWRITE_TAC [SKOLEM_THM] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"r:num->num")
       (fun th => tactic_of do
          let (th1, th2) ← CONJ_PAIR (← SPEC (← q r"n:num") th)
          pure (MAP_EVERY (fun t => tactic_of do
            pure (MP_TAC (← GEN (← q r"n:num") t))) [th1, th2]))) THEN
      DISCH_THEN (fun th => tactic_of do
        pure (MP_TAC (← GEN (← q r"n:num")
          (← SPECL [← q r"n:num", ← q r"SUC(r(n:num))"] th)))) THEN
      REWRITE_TAC [LE_SUC_LT, LT_REFL, NOT_EXISTS_THM] THEN
      (← do
        let it ← ITAUT (← q r"(a \/ b) /\ ~(c /\ b) ==> c ==> a")
        let tot ← SPECL [← q r"&n ** x", ← q r"&(SUC(r(n:num)))"] NADD_LE_TOTAL
        pure (DISCH_THEN (fun th => tactic_of do
          pure (ASSUME_TAC (← GENL [← q r"n:num", ← q r"x:nadd"]
            (← MATCH_MP it (← CONJ tot (← SPEC_ALL th)))))))) THEN
      DISCH_TAC] THEN
    SUBGOAL_THEN (← q r"!n i. i * r(n) <= n * r(i) + n") ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN
      FIRST_ASSUM (fun th => tactic_of do
        pure (X_CHOOSE_THEN (← q r"x:nadd") STRIP_ASSUME_TAC
          (← SPEC (← q r"n:num") th))) THEN
      ONCE_REWRITE_TAC [← GSYM NADD_OF_NUM_LE] THEN
      MATCH_MP_TAC NADD_LE_TRANS THEN
      EXISTS_TAC (← q r"&i ** &n ** x") THEN CONJ_TAC THENL
       [MATCH_MP_TAC NADD_LE_TRANS THEN
        EXISTS_TAC (← q r"&i ** &(r(n:num))") THEN CONJ_TAC THENL
         [MATCH_MP_TAC NADD_EQ_IMP_LE THEN
          ONCE_REWRITE_TAC [NADD_EQ_SYM] THEN MATCH_ACCEPT_TAC NADD_OF_NUM_MUL,
          MATCH_MP_TAC NADD_LE_LMUL THEN ASM_REWRITE_TAC []],
        MATCH_MP_TAC NADD_LE_TRANS THEN
        EXISTS_TAC (← q r"&n ** &(SUC(r(i:num)))") THEN CONJ_TAC THENL
         [MATCH_MP_TAC NADD_LE_TRANS THEN EXISTS_TAC (← q r"&n ** &i ** x") THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC NADD_EQ_IMP_LE THEN
            MATCH_MP_TAC NADD_EQ_TRANS THEN
            EXISTS_TAC (← q r"(&i ** &n) ** x") THEN
            REWRITE_TAC [NADD_MUL_ASSOC] THEN
            MATCH_MP_TAC NADD_EQ_TRANS THEN
            EXISTS_TAC (← q r"(&n ** &i) ** x") THEN
            REWRITE_TAC [← ONCE_REWRITE_RULE [NADD_EQ_SYM] NADD_MUL_ASSOC] THEN
            MATCH_MP_TAC NADD_MUL_WELLDEF THEN
            REWRITE_TAC [NADD_MUL_SYM, NADD_EQ_REFL],
            MATCH_MP_TAC NADD_LE_LMUL THEN
            FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []],
          ONCE_REWRITE_TAC [ADD_SYM] THEN REWRITE_TAC [← GSYM MULT_SUC] THEN
          MATCH_MP_TAC NADD_EQ_IMP_LE THEN
          REWRITE_TAC [NADD_OF_NUM_MUL]]], ALL_TAC] THEN
    EXISTS_TAC (← q r"afn r") THEN SUBGOAL_THEN (← q r"fn(afn r) = r") ASSUME_TAC THENL
     [REWRITE_TAC [← GSYM nadd_rep] THEN REWRITE_TAC [is_nadd, DIST_LE_CASES] THEN
      EXISTS_TAC (← q r"1") THEN REWRITE_TAC [MULT_CLAUSES] THEN
      REWRITE_TAC [FORALL_AND_THM] THEN
      GEN_REWRITE_TAC RAND_CONV [SWAP_FORALL_THM] THEN
      GEN_REWRITE_TAC (LAND_CONV o funpow 2 BINDER_CONV o
        funpow 2 RAND_CONV) [ADD_SYM] THEN
      REWRITE_TAC [] THEN MAP_EVERY X_GEN_TAC [← q r"i:num", ← q r"n:num"] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"n * r(i:num) + n") THEN
      ASM_REWRITE_TAC [ADD_ASSOC, LE_ADD], ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC (← q r"x:nadd") THEN DISCH_TAC THEN
      MATCH_MP_TAC NADD_ARCH_LEMMA THEN
      EXISTS_TAC (← q r"&2") THEN X_GEN_TAC (← q r"n:num") THEN
      MATCH_MP_TAC NADD_LE_TRANS THEN
      EXISTS_TAC (← q r"&(SUC(r(n:num)))") THEN CONJ_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
        ASM_REWRITE_TAC [nadd_le, NADD_ADD, NADD_MUL, NADD_OF_NUM] THEN
        ONCE_REWRITE_TAC [ADD_SYM] THEN
        REWRITE_TAC [ADD1, RIGHT_ADD_DISTRIB] THEN
        REWRITE_TAC [MULT_2, MULT_CLAUSES, ADD_ASSOC, LE_ADD_RCANCEL] THEN
        REWRITE_TAC [← GSYM ADD_ASSOC] THEN ONCE_REWRITE_TAC [ADD_SYM] THEN
        ONCE_REWRITE_TAC [BOUNDS_IGNORE] THEN
        MAP_EVERY EXISTS_TAC [← q r"0", ← q r"n:num"] THEN
        X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN
        GEN_REWRITE_TAC LAND_CONV [MULT_SYM] THEN
        MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"n * r(i:num) + n") THEN
        ASM_REWRITE_TAC [LE_ADD_LCANCEL, ADD_CLAUSES]],
      X_GEN_TAC (← q r"z:nadd") THEN DISCH_TAC THEN
      MATCH_MP_TAC NADD_ARCH_LEMMA THEN EXISTS_TAC (← q r"&1") THEN
      X_GEN_TAC (← q r"n:num") THEN MATCH_MP_TAC NADD_LE_TRANS THEN
      EXISTS_TAC (← q r"&(r(n:num)) ++ &1") THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC [nadd_le, NADD_ADD, NADD_MUL, NADD_OF_NUM] THEN
        EXISTS_TAC (← q r"0") THEN REWRITE_TAC [ADD_CLAUSES, MULT_CLAUSES] THEN
        GEN_TAC THEN GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [MULT_SYM] THEN
        ASM_REWRITE_TAC [],
        REWRITE_TAC [NADD_LE_RADD] THEN
        FIRST_ASSUM (fun th => tactic_of do
          pure (X_CHOOSE_THEN (← q r"x:nadd") MP_TAC (← SPEC (← q r"n:num") th))) THEN
        DISCH_THEN STRIP_ASSUME_TAC THEN
        MATCH_MP_TAC NADD_LE_TRANS THEN EXISTS_TAC (← q r"&n ** x") THEN
        ASM_REWRITE_TAC [] THEN MATCH_MP_TAC NADD_LE_LMUL THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []]])

  return {
    NADD_LE_0, NADD_EQ_IMP_LE, NADD_LE_LMUL, NADD_LE_RMUL, NADD_LE_RADD,
    NADD_LE_LADD, NADD_RDISTRIB, NADD_ARCH_MULT, NADD_ARCH_ZERO,
    NADD_ARCH_LEMMA, NADD_COMPLETE }

/-- A bit more on nearly-multiplicative functions (realax.ml 932-972) and
    the auxiliary function for the multiplicative inverse (975-1179).
    Field names match the OCaml identifiers exactly, in OCaml order.

    `nadd_rinv` (975) has a SIMPLE variable LHS, so the plain `new_definition`
    is right.  The two `el 3 (CONJUNCTS MULT_CLAUSES)` idioms (941,968) select
    the FOURTH conjunct `!m. m * 1 = m` (0-indexed `el 3`) then `GSYM` it. -/
structure NaddInvAuxThms where
  /- A bit more on nearly-multiplicative functions (932-972). -/
  NADD_UBOUND          : thm
  NADD_NONZERO         : thm
  NADD_LBOUND          : thm
  /- Auxiliary function for the multiplicative inverse (975-1179). -/
  nadd_rinv            : thm
  NADD_MUL_LINV_LEMMA0 : thm
  NADD_MUL_LINV_LEMMA1 : thm
  NADD_MUL_LINV_LEMMA2 : thm
  NADD_MUL_LINV_LEMMA3 : thm
  NADD_MUL_LINV_LEMMA4 : thm
  NADD_MUL_LINV_LEMMA5 : thm
  NADD_MUL_LINV_LEMMA6 : thm
  NADD_MUL_LINV_LEMMA7 : thm
  NADD_MUL_LINV_LEMMA7a : thm
  NADD_MUL_LINV_LEMMA8 : thm
  deriving Inhabited

/-- realax.ml 928-1178: more on nearly-multiplicative functions and the
    auxiliary function for the multiplicative inverse. -/
@[nospecialize]
def setupNaddInvAux [HolBase] (N : HolMath.Nums.NumsThms)
    (A1 : HolMath.Arith.ArithThms1) (A2 : HolMath.Arith.ArithThms2)
    (A3 : HolMath.Arith.ArithThms3) (A4 : HolMath.Arith.ArithThms4)
    (DIVISION : thm)
    (D : DistThms) (Na : NaddThms) (O : NaddOrderThms) (M : NaddArithThms)
    (Cm : NaddCompleteThms) (ARITH ARITH_SUC : thm)
    (new_definition' : term → IO (Except String thm)) :
    ExceptT String IO NaddInvAuxThms := do
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let INDUCT_TAC := HolMath.Nums.INDUCT_TAC N.num_INDUCTION
  let { NOT_SUC, .. } := N
  let { ADD_CLAUSES, ADD_SYM, ADD_ASSOC, ADD_AC, ADD1, .. } := A1
  let { MULT_CLAUSES, MULT_SYM, LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB,
        MULT_ASSOC, MULT_AC, LE, LT, LE_SUC_LT, LE_0, .. } := A2
  let { LE_REFL, LE_TRANS, LE_CASES, NOT_LE, NOT_LT, LT_IMP_LE, .. } := A3
  let { LE_ADD, LE_ADDR, LE_ADD_LCANCEL, LE_ADD_RCANCEL, LE_ADD2, LE_MULT2,
        LE_MULT_LCANCEL, LE_MULT_RCANCEL, .. } := A4
  let { DIST_REFL, DIST_LZERO, DIST_SYM, DIST_RADD_0, DIST_LMUL, DIST_ADDBOUND,
        DIST_TRIANGLES_LE, BOUNDS_NOTZERO, BOUNDS_IGNORE, .. } := D
  let { NADD_CAUCHY, NADD_BOUND, .. } := Na
  let { NADD_OF_NUM, nadd_le, .. } := O
  let { NADD_MUL, .. } := M
  let { NADD_ARCH_MULT, .. } := Cm
  let { EQ_IMP, .. } := HolBase.T
  let { NOT_FORALL_THM, .. } := HolBase.C

  /- A bit more on nearly-multiplicative functions. -/

  let NADD_UBOUND ← prove
   r"!x. ?B N. !n. N <= n ==> fn x n <= B * n"
   (GEN_TAC THEN X_CHOOSE_THEN (← q r"A1:num")
      (X_CHOOSE_TAC (← q r"A2:num")) (← SPEC (← q r"x:nadd") NADD_BOUND) THEN
    EXISTS_TAC (← q r"A1 + A2") THEN EXISTS_TAC (← q r"1") THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC (← q r"A1 * n + A2") THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [RIGHT_ADD_DISTRIB, LE_ADD_LCANCEL] THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM (← el 3 (CONJUNCTS MULT_CLAUSES))] THEN
    ASM_REWRITE_TAC [LE_MULT_LCANCEL])

  let NADD_NONZERO ← prove
   r"!x. ~(x === &0) ==> ?N. !n. N <= n ==> ~(fn x n = 0)"
   (GEN_TAC THEN
    DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← MATCH_MP NADD_ARCH_MULT th))) THEN
    DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"1") th))) THEN
    REWRITE_TAC [nadd_le, NADD_MUL, NADD_OF_NUM, MULT_CLAUSES] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"A1:num") (X_CHOOSE_TAC (← q r"A2:num"))) THEN
    EXISTS_TAC (← q r"A2 + 1") THEN X_GEN_TAC (← q r"n:num") THEN REPEAT DISCH_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (UNDISCH_TAC (← check is_forall (concl th)))) THEN
    REWRITE_TAC [NOT_FORALL_THM, NOT_LE, ← GSYM LE_SUC_LT, ADD1] THEN
    EXISTS_TAC (← q r"n:num") THEN ASM_REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES])

  let NADD_LBOUND ← prove
   r"!x. ~(x === &0) ==> ?A N. !n. N <= n ==> n <= A * fn x n"
   (GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure ((X_CHOOSE_TAC (← q r"N:num")) (← MATCH_MP NADD_NONZERO th))) THEN
    FIRST_ASSUM (fun th => tactic_of do pure (MP_TAC (← MATCH_MP NADD_ARCH_MULT th))) THEN
    DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"1") th))) THEN
    REWRITE_TAC [nadd_le, NADD_MUL, NADD_OF_NUM, MULT_CLAUSES] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"A1:num") (X_CHOOSE_TAC (← q r"A2:num"))) THEN
    EXISTS_TAC (← q r"A1 + A2") THEN EXISTS_TAC (← q r"N:num") THEN GEN_TAC THEN
    DISCH_THEN (ANTE_RES_THEN ASSUME_TAC) THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"A1 * fn x n + A2") THEN
    ASM_REWRITE_TAC [RIGHT_ADD_DISTRIB, LE_ADD_LCANCEL] THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM (← el 3 (CONJUNCTS MULT_CLAUSES))] THEN
    REWRITE_TAC [LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    REWRITE_TAC [← GSYM (← REWRITE_CONV [ARITH_SUC] (← q r"SUC 0"))] THEN
    ASM_REWRITE_TAC [← GSYM NOT_LT, LT])

  /- Auxiliary function for the multiplicative inverse. -/

  let nadd_rinv ← new_definition
   r"nadd_rinv(x) = \n. (n * n) DIV (fn x n)"

  let NADD_MUL_LINV_LEMMA0 ← prove
   r"!x. ~(x === &0) ==> ?A B. !n. nadd_rinv x n <= A * n + B"
   (GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC [BOUNDS_IGNORE] THEN
    FIRST_ASSUM (fun th => tactic_of do pure (MP_TAC (← MATCH_MP NADD_LBOUND th))) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"A:num") (X_CHOOSE_TAC (← q r"N:num"))) THEN
    MAP_EVERY EXISTS_TAC [← q r"A:num", ← q r"0", ← q r"SUC N"] THEN
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [ADD_CLAUSES] THEN
    MP_TAC (← SPECL [← q r"nadd_rinv x n", ← q r"A * n", ← q r"n:num"] LE_MULT_RCANCEL) THEN
    UNDISCH_TAC (← q r"SUC N <= n") THEN ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_REWRITE_TAC [LE, NOT_SUC] THEN DISCH_TAC THEN
    DISCH_THEN (fun th => tactic_of do pure (SUBST1_TAC (← SYM th))) THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"nadd_rinv x n * A * fn x n") THEN
    ASM_REWRITE_TAC [LE_MULT_LCANCEL] THEN CONJ_TAC THENL
     [DISJ2_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC (← q r"SUC N") THEN ASM_REWRITE_TAC [LE, LE_REFL],
      GEN_REWRITE_TAC LAND_CONV [MULT_SYM] THEN
      REWRITE_TAC [← GSYM MULT_ASSOC, LE_MULT_LCANCEL] THEN
      DISJ2_TAC THEN ASM_CASES_TAC (← q r"fn x n = 0") THEN
      ASM_REWRITE_TAC [MULT_CLAUSES, LE_0, nadd_rinv] THEN
      FIRST_ASSUM (fun th => tactic_of do pure (MP_TAC (← MATCH_MP DIVISION th))) THEN
      DISCH_THEN (fun t => tactic_of do
        pure (GEN_REWRITE_TAC RAND_CONV [← CONJUNCT1 (← SPEC_ALL t)])) THEN
      GEN_REWRITE_TAC LAND_CONV [MULT_SYM] THEN REWRITE_TAC [LE_ADD]])

  let NADD_MUL_LINV_LEMMA1 ← prove
   r"!x n. ~(fn x n = 0) ==> dist(fn x n * nadd_rinv(x) n, n * n) <= fn x n"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← MATCH_MP DIVISION th))) THEN
    DISCH_THEN (fun th => tactic_of do
      pure ((CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) (← SPEC (← q r"n * n") th))) THEN
    REWRITE_TAC [nadd_rinv] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [MULT_SYM] THEN
    REWRITE_TAC [DIST_RADD_0] THEN MATCH_MP_TAC LT_IMP_LE THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC)

  let NADD_MUL_LINV_LEMMA2 ← prove
   r"!x. ~(x === &0) ==> ?N. !n. N <= n ==>
         dist(fn x n * nadd_rinv(x) n, n * n) <= fn x n"
   (GEN_TAC THEN
    DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← MATCH_MP NADD_NONZERO th))) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"N:num")) THEN EXISTS_TAC (← q r"N:num") THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC NADD_MUL_LINV_LEMMA1 THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [])

  let NADD_MUL_LINV_LEMMA3 ← prove
   r"!x. ~(x === &0) ==> ?N. !m n. N <= n ==>
        dist(m * fn x m * fn x n * nadd_rinv(x) n,
             m * fn x m * n * n) <= m * fn x m * fn x n"
   (GEN_TAC THEN
    DISCH_THEN (fun th => tactic_of do
      pure (MP_TAC (← MATCH_MP NADD_MUL_LINV_LEMMA2 th))) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"N:num")) THEN EXISTS_TAC (← q r"N:num") THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM DIST_LMUL, MULT_ASSOC] THEN
    REWRITE_TAC [LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [])

  let NADD_MUL_LINV_LEMMA4 ← prove
   r"!x. ~(x === &0) ==> ?N. !m n. N <= m /\ N <= n ==>
        (fn x m * fn x n) * dist(m * nadd_rinv(x) n,n * nadd_rinv(x) m) <=
          (m * n) * dist(m * fn x n,n * fn x m) + (fn x m * fn x n) * (m + n)"
   (GEN_TAC THEN
    DISCH_THEN (fun th => tactic_of do
      pure (MP_TAC (← MATCH_MP NADD_MUL_LINV_LEMMA3 th))) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"N:num")) THEN EXISTS_TAC (← q r"N:num") THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [DIST_LMUL, LEFT_ADD_DISTRIB] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [DIST_SYM] THEN
    MATCH_MP_TAC DIST_TRIANGLES_LE THEN CONJ_TAC THENL
     [ANTE_RES_THEN (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"m:num") th)))
        (← ASSUME (← q r"N <= n")),
      ANTE_RES_THEN (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"n:num") th)))
        (← ASSUME (← q r"N <= m"))] THEN
    MATCH_MP_TAC EQ_IMP THEN REWRITE_TAC [MULT_AC])

  let NADD_MUL_LINV_LEMMA5 ← prove
   r"!x. ~(x === &0) ==> ?B N. !m n. N <= m /\ N <= n ==>
        (fn x m * fn x n) * dist(m * nadd_rinv(x) n,n * nadd_rinv(x) m) <=
        B * (m * n) * (m + n)"
   (GEN_TAC THEN
    DISCH_THEN (fun th => tactic_of do
      pure (MP_TAC (← MATCH_MP NADD_MUL_LINV_LEMMA4 th))) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"N1:num")) THEN
    X_CHOOSE_TAC (← q r"B1:num") (← SPEC (← q r"x:nadd") NADD_CAUCHY) THEN
    X_CHOOSE_THEN (← q r"B2:num") (X_CHOOSE_TAC (← q r"N2:num"))
      (← SPEC (← q r"x:nadd") NADD_UBOUND) THEN
    EXISTS_TAC (← q r"B1 + B2 * B2") THEN EXISTS_TAC (← q r"N1 + N2") THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC (← q r"(m * n) * dist(m * fn x n,n * fn x m) +
              (fn x m * fn x n) * (m + n)") THEN
    CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"N1 + N2") THEN
      ASM_REWRITE_TAC [LE_ADD, LE_ADDR],
      REWRITE_TAC [RIGHT_ADD_DISTRIB] THEN MATCH_MP_TAC LE_ADD2] THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN
      GEN_REWRITE_TAC RAND_CONV [← GSYM MULT_ASSOC] THEN
      GEN_REWRITE_TAC (funpow 2 RAND_CONV) [MULT_SYM] THEN
      ASM_REWRITE_TAC [LE_MULT_LCANCEL],
      ONCE_REWRITE_TAC [← AC MULT_AC
        (← q r"(a * b) * (c * d) * e = ((a * c) * (b * d)) * e")] THEN
      REWRITE_TAC [LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
      MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"N1 + N2") THEN
      ASM_REWRITE_TAC [LE_ADD, LE_ADDR]])

  let NADD_MUL_LINV_LEMMA6 ← prove
   r"!x. ~(x === &0) ==> ?B N. !m n. N <= m /\ N <= n ==>
        (m * n) * dist(m * nadd_rinv(x) n,n * nadd_rinv(x) m) <=
        B * (m * n) * (m + n)"
   (GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (MP_TAC (← MATCH_MP NADD_MUL_LINV_LEMMA5 th))) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"B1:num") (X_CHOOSE_TAC (← q r"N1:num"))) THEN
    FIRST_ASSUM (fun th => tactic_of do pure (MP_TAC (← MATCH_MP NADD_LBOUND th))) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"B2:num") (X_CHOOSE_TAC (← q r"N2:num"))) THEN
    EXISTS_TAC (← q r"B1 * B2 * B2") THEN EXISTS_TAC (← q r"N1 + N2") THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC (← q r"(B2 * B2) * (fn x m * fn x n) *
              dist (m * nadd_rinv x n,n * nadd_rinv x m)") THEN
    CONJ_TAC THENL
     [REWRITE_TAC [MULT_ASSOC, LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
      ONCE_REWRITE_TAC [← AC MULT_AC (← q r"((a * b) * c) * d = (a * c) * (b * d)")] THEN
      MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC,
      ONCE_REWRITE_TAC [← AC MULT_AC
        (← q r"(a * b * c) * (d * e) * f = (b * c) * (a * (d * e) * f)")] THEN
      REWRITE_TAC [LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"N1 + N2") THEN
    ASM_REWRITE_TAC [LE_ADD, LE_ADDR])

  let NADD_MUL_LINV_LEMMA7 ← prove
   r"!x. ~(x === &0) ==> ?B N. !m n. N <= m /\ N <= n ==>
        dist(m * nadd_rinv(x) n,n * nadd_rinv(x) m) <= B * (m + n)"
   (GEN_TAC THEN
    DISCH_THEN (fun th => tactic_of do
      pure (MP_TAC (← MATCH_MP NADD_MUL_LINV_LEMMA6 th))) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"B:num") (X_CHOOSE_TAC (← q r"N:num"))) THEN
    MAP_EVERY EXISTS_TAC [← q r"B:num", ← q r"N + 1"] THEN
    MAP_EVERY X_GEN_TAC [← q r"m:num", ← q r"n:num"] THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"N <= m /\ N <= n") MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"N + 1") THEN
      ASM_REWRITE_TAC [LE_ADD],
      DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN
      ONCE_REWRITE_TAC [← AC MULT_AC (← q r"a * b * c = b * a * c")] THEN
      REWRITE_TAC [LE_MULT_LCANCEL] THEN
      DISCH_THEN (DISJ_CASES_THEN2 MP_TAC ACCEPT_TAC) THEN
      CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN (K ALL_TAC : thm → tactic) THEN
      ONCE_REWRITE_TAC [← GSYM (← CONJUNCT1 LE)] THEN
      REWRITE_TAC [NOT_LE, ← GSYM LE_SUC_LT] THEN
      REWRITE_TAC [← EQT_ELIM (← REWRITE_CONV [ARITH] (← q r"SUC 0 = 1 * 1"))] THEN
      MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"N + 1") THEN
      ASM_REWRITE_TAC [LE_ADDR]])

  let NADD_MUL_LINV_LEMMA7a ← prove
   r"!x. ~(x === &0) ==> !N. ?A B. !m n. m <= N ==>
        dist(m * nadd_rinv(x) n,n * nadd_rinv(x) m) <= A * n + B"
   (GEN_TAC THEN
    DISCH_THEN (fun th => tactic_of do
      pure (MP_TAC (← MATCH_MP NADD_MUL_LINV_LEMMA0 th))) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"A0:num") (X_CHOOSE_TAC (← q r"B0:num"))) THEN
    INDUCT_TAC THENL
     [MAP_EVERY EXISTS_TAC [← q r"nadd_rinv x 0", ← q r"0"] THEN
      REPEAT GEN_TAC THEN REWRITE_TAC [LE] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC [MULT_CLAUSES, DIST_LZERO, ADD_CLAUSES] THEN
      GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN MATCH_ACCEPT_TAC LE_REFL,
      FIRST_ASSUM (X_CHOOSE_THEN (← q r"A:num") (X_CHOOSE_TAC (← q r"B:num"))) THEN
      EXISTS_TAC (← q r"A + (nadd_rinv(x)(SUC N) + SUC N * A0)") THEN
      EXISTS_TAC (← q r"SUC N * B0 + B") THEN
      REPEAT GEN_TAC THEN REWRITE_TAC [LE] THEN
      DISCH_THEN (DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC) THENL
       [MATCH_MP_TAC LE_TRANS THEN
        EXISTS_TAC (← q r"SUC N * nadd_rinv x n + n * nadd_rinv x (SUC N)") THEN
        REWRITE_TAC [DIST_ADDBOUND] THEN REWRITE_TAC [RIGHT_ADD_DISTRIB] THEN
        ONCE_REWRITE_TAC [← AC ADD_AC
          (← q r"(a + b + c) + d + e = (c + d) + (b + a + e)")] THEN
        MATCH_MP_TAC LE_ADD2 THEN CONJ_TAC THENL
         [REWRITE_TAC [← GSYM MULT_ASSOC, ← GSYM LEFT_ADD_DISTRIB] THEN
          ASM_REWRITE_TAC [LE_MULT_LCANCEL],
          GEN_REWRITE_TAC LAND_CONV [MULT_SYM] THEN
          MATCH_ACCEPT_TAC LE_ADD],
        MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"A * n + B") THEN CONJ_TAC THENL
         [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
          REWRITE_TAC [ADD_ASSOC, LE_ADD_RCANCEL] THEN
          REWRITE_TAC [RIGHT_ADD_DISTRIB, ← GSYM ADD_ASSOC, LE_ADD]]]])

  let NADD_MUL_LINV_LEMMA8 ← prove
   r"!x. ~(x === &0) ==>
        ?B. !m n. dist(m * nadd_rinv(x) n,n * nadd_rinv(x) m) <= B * (m + n)"
   (GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (MP_TAC (← MATCH_MP NADD_MUL_LINV_LEMMA7 th))) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"B0:num") (X_CHOOSE_TAC (← q r"N:num"))) THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (MP_TAC (← SPEC (← q r"N:num") (← MATCH_MP NADD_MUL_LINV_LEMMA7a th)))) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"A:num") (X_CHOOSE_TAC (← q r"B:num"))) THEN
    MATCH_MP_TAC BOUNDS_NOTZERO THEN REWRITE_TAC [DIST_REFL] THEN
    EXISTS_TAC (← q r"A + B0") THEN EXISTS_TAC (← q r"B:num") THEN REPEAT GEN_TAC THEN
    DISJ_CASES_THEN2 ASSUME_TAC MP_TAC (← SPECL [← q r"N:num", ← q r"m:num"] LE_CASES) THENL
     [DISJ_CASES_THEN2 ASSUME_TAC MP_TAC (← SPECL [← q r"N:num", ← q r"n:num"] LE_CASES)
      THENL
       [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"B0 * (m + n)") THEN CONJ_TAC THENL
         [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
          GEN_REWRITE_TAC (RAND_CONV o funpow 2 LAND_CONV) [ADD_SYM] THEN
          REWRITE_TAC [RIGHT_ADD_DISTRIB, ← GSYM ADD_ASSOC, LE_ADD]],
        DISCH_THEN (ANTE_RES_THEN ASSUME_TAC) THEN
        MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"A * m + B") THEN
        ONCE_REWRITE_TAC [DIST_SYM] THEN
        ASM_REWRITE_TAC [LE_ADD_RCANCEL] THEN
        REWRITE_TAC [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, ← GSYM ADD_ASSOC,
          LE_ADD]],
      DISCH_THEN (ANTE_RES_THEN ASSUME_TAC) THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"A * n + B") THEN
      ASM_REWRITE_TAC [LE_ADD_RCANCEL] THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [ADD_SYM] THEN
      REWRITE_TAC [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, ← GSYM ADD_ASSOC,
        LE_ADD]])

  return {
    NADD_UBOUND, NADD_NONZERO, NADD_LBOUND, nadd_rinv, NADD_MUL_LINV_LEMMA0,
    NADD_MUL_LINV_LEMMA1, NADD_MUL_LINV_LEMMA2, NADD_MUL_LINV_LEMMA3,
    NADD_MUL_LINV_LEMMA4, NADD_MUL_LINV_LEMMA5, NADD_MUL_LINV_LEMMA6,
    NADD_MUL_LINV_LEMMA7, NADD_MUL_LINV_LEMMA7a, NADD_MUL_LINV_LEMMA8 }

/-- The multiplicative inverse on `nadd` (realax.ml 1182-1252), the SECOND
    type construction `hreal` as a QUOTIENT of `nadd` by `(===)` (1256-1287),
    completeness in lifted form and the 21 lifted first-order theorems
    (1289-1310), and the consequential `hreal` theorems (1316-1381).  Field
    names match the OCaml identifiers exactly, in OCaml order.

    `nadd_inv(x) = if x === &0 then &0 else afn(nadd_rinv x)` (1183) is a
    CONDITIONAL definition with a SIMPLE variable LHS, so the plain
    `new_definition` is right.

    `hreal_tybij` (1257) is stored as the PAIR `(hreal_tybij1, hreal_tybij2)`
    returned by `define_quotient_type`.  The five `lift_function` calls each
    return a PAIR `(hreal_X, hreal_X_th)`; both halves are kept because the
    `_th` halves are the `trths` argument to `lift_theorem`. -/
structure HrealThms where
  /- The multiplicative inverse proper (1182-1252). -/
  nadd_inv           : thm
  NADD_INV           : thm
  NADD_MUL_LINV      : thm
  NADD_INV_0         : thm
  NADD_INV_WELLDEF   : thm
  /- Definition of the new type `hreal` (1256-1287). -/
  hreal_tybij1       : thm
  hreal_tybij2       : thm
  hreal_of_num       : thm
  hreal_of_num_th    : thm
  hreal_add          : thm
  hreal_add_th       : thm
  hreal_mul          : thm
  hreal_mul_th       : thm
  hreal_le           : thm
  hreal_le_th        : thm
  hreal_inv          : thm
  hreal_inv_th       : thm
  /- Completeness in lifted form (1289-1296). -/
  HREAL_COMPLETE     : thm
  /- The 21 lifted first-order theorems (1298-1310). -/
  HREAL_OF_NUM_EQ    : thm
  HREAL_OF_NUM_LE    : thm
  HREAL_OF_NUM_ADD   : thm
  HREAL_OF_NUM_MUL   : thm
  HREAL_LE_REFL      : thm
  HREAL_LE_TRANS     : thm
  HREAL_LE_ANTISYM   : thm
  HREAL_LE_TOTAL     : thm
  HREAL_LE_ADD       : thm
  HREAL_LE_EXISTS    : thm
  HREAL_ARCH         : thm
  HREAL_ADD_SYM      : thm
  HREAL_ADD_ASSOC    : thm
  HREAL_ADD_LID      : thm
  HREAL_ADD_LCANCEL  : thm
  HREAL_MUL_SYM      : thm
  HREAL_MUL_ASSOC    : thm
  HREAL_MUL_LID      : thm
  HREAL_ADD_LDISTRIB : thm
  HREAL_MUL_LINV     : thm
  HREAL_INV_0        : thm
  /- Consequential theorems needed later (1316-1381). -/
  HREAL_LE_EXISTS_DEF     : thm
  HREAL_EQ_ADD_LCANCEL    : thm
  HREAL_EQ_ADD_RCANCEL    : thm
  HREAL_LE_ADD_LCANCEL    : thm
  HREAL_LE_ADD_RCANCEL    : thm
  HREAL_ADD_RID           : thm
  HREAL_ADD_RDISTRIB      : thm
  HREAL_MUL_LZERO         : thm
  HREAL_MUL_RZERO         : thm
  HREAL_ADD_AC            : thm
  HREAL_LE_ADD2           : thm
  HREAL_LE_MUL_RCANCEL_IMP : thm
  deriving Inhabited

/-- realax.ml 1179-1381: the multiplicative inverse, the quotient type
    `hreal`, and the lifted theorems. -/
@[nospecialize]
def setupHreal [HolBase]
    (A1 : HolMath.Arith.ArithThms1) (A2 : HolMath.Arith.ArithThms2)
    (A3 : HolMath.Arith.ArithThms3) (A4 : HolMath.Arith.ArithThms4)
    (D : DistThms) (Na : NaddThms) (O : NaddOrderThms) (M : NaddArithThms)
    (Cm : NaddCompleteThms) (Iv : NaddInvAuxThms)
    (ASM_MESON_TAC : List thm → tactic)
    (new_definition' : term → IO (Except String thm))
    (define_quotient_type' :
      String → String × String → term → IO (Except String (thm × thm)))
    (lift_function' :
      thm → thm × thm → String → thm → IO (Except String (thm × thm)))
    (lift_theorem' :
      thm × thm → thm × thm × thm → List thm → thm → IO (Except String thm))
    (override_interface' : String → term → IO (Except String Unit))
    (overload_interface' : String → term → IO (Except String Unit)) :
    ExceptT String IO HrealThms := do
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let define_quotient_type (ty : String) (names : String × String) (s : String) :
      ExceptT String IO (thm × thm) := do
    define_quotient_type' ty names (← q s)
  let lift_function (tybij : thm) (refl_trans : thm × thm) (name : String) (wth : thm) :
      ExceptT String IO (thm × thm) :=
    lift_function' tybij refl_trans name wth
  let lift_theorem (tybij : thm × thm) (eqvs : thm × thm × thm) (trths : List thm)
      (th : thm) : ExceptT String IO thm :=
    lift_theorem' tybij eqvs trths th
  let override_interface (p : String × String) : ExceptT String IO Unit := do
    override_interface' p.1 (← q p.2)
  let overload_interface (p : String × String) : ExceptT String IO Unit := do
    overload_interface' p.1 (← q p.2)
  let { ADD_AC, .. } := A1
  let { MULT_CLAUSES, MULT_SYM, RIGHT_ADD_DISTRIB, .. } := A2
  let { LE_TRANS, .. } := A3
  let { LE_ADD2, .. } := A4
  let { DIST_LMUL, DIST_TRIANGLE_LE, BOUNDS_DIVIDED, BOUNDS_IGNORE, .. } := D
  let { is_nadd, nadd_rep, NADD_BOUND, NADD_ALTMUL, .. } := Na
  let { nadd_eq, NADD_EQ_REFL, NADD_EQ_SYM, NADD_EQ_TRANS, NADD_OF_NUM,
        NADD_OF_NUM_WELLDEF, NADD_OF_NUM_EQ, NADD_LE_WELLDEF, NADD_LE_REFL,
        NADD_LE_TRANS, NADD_LE_ANTISYM, NADD_LE_TOTAL, NADD_ARCH,
        NADD_OF_NUM_LE, .. } := O
  let { NADD_ADD_WELLDEF, NADD_ADD_SYM, NADD_ADD_ASSOC, NADD_ADD_LID,
        NADD_ADD_LCANCEL, NADD_LE_ADD, NADD_LE_EXISTS, NADD_OF_NUM_ADD,
        NADD_MUL, NADD_MUL_SYM, NADD_MUL_ASSOC, NADD_MUL_LID, NADD_LDISTRIB,
        NADD_MUL_WELLDEF, NADD_OF_NUM_MUL, .. } := M
  let { NADD_COMPLETE, .. } := Cm
  let { NADD_MUL_LINV_LEMMA2, NADD_MUL_LINV_LEMMA8, .. } := Iv

  /- Now the multiplicative inverse proper. -/

  let nadd_inv ← new_definition
   r"nadd_inv(x) = if x === &0 then &0 else afn(nadd_rinv x)"

  override_interface ("inv", r"nadd_inv:nadd->nadd")

  let NADD_INV ← prove
   r"!x. fn(nadd_inv x) = if x === &0 then (\n. 0) else nadd_rinv x"
   (GEN_TAC THEN REWRITE_TAC [nadd_inv] THEN
    ASM_CASES_TAC (← q r"x === &0") THEN ASM_REWRITE_TAC [NADD_OF_NUM, MULT_CLAUSES] THEN
    REWRITE_TAC [← GSYM nadd_rep, is_nadd] THEN
    MATCH_MP_TAC NADD_MUL_LINV_LEMMA8 THEN POP_ASSUM ACCEPT_TAC)

  let NADD_MUL_LINV ← prove
   r"!x. ~(x === &0) ==> inv(x) ** x === &1"
   (GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [nadd_eq, NADD_MUL] THEN
    ONCE_REWRITE_TAC [BOUNDS_DIVIDED] THEN
    X_CHOOSE_THEN (← q r"A1:num") (X_CHOOSE_TAC (← q r"B1:num"))
     (← SPECL [← q r"inv(x)", ← q r"x:nadd"] NADD_ALTMUL) THEN
    REWRITE_TAC [DIST_LMUL, NADD_OF_NUM, MULT_CLAUSES] THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure ((X_CHOOSE_TAC (← q r"N:num")) (← MATCH_MP NADD_MUL_LINV_LEMMA2 th))) THEN
    X_CHOOSE_THEN (← q r"A':num") (X_CHOOSE_TAC (← q r"B':num"))
      (← SPEC (← q r"x:nadd") NADD_BOUND) THEN
    SUBGOAL_THEN (← q r"?A2 B2. !n. dist(fn x n * nadd_rinv x n,n * n) <= A2 * n + B2")
    STRIP_ASSUME_TAC THENL
     [EXISTS_TAC (← q r"A':num") THEN ONCE_REWRITE_TAC [BOUNDS_IGNORE] THEN
      MAP_EVERY EXISTS_TAC [← q r"B':num", ← q r"N:num"] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"fn x n") THEN ASM_REWRITE_TAC [] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
      MAP_EVERY EXISTS_TAC [← q r"A1 + A2", ← q r"B1 + B2"] THEN
      GEN_TAC THEN MATCH_MP_TAC DIST_TRIANGLE_LE THEN
      EXISTS_TAC (← q r"fn (inv x) n * fn x n") THEN
      REWRITE_TAC [RIGHT_ADD_DISTRIB] THEN
      ONCE_REWRITE_TAC [← AC ADD_AC (← q r"(a + b) + c + d = (a + c) + (b + d)")] THEN
      MATCH_MP_TAC LE_ADD2 THEN ASM_REWRITE_TAC [] THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [MULT_SYM] THEN
      ASM_REWRITE_TAC [NADD_INV]])

  let NADD_INV_0 ← prove
   r"inv(&0) === &0"
   (REWRITE_TAC [nadd_inv, NADD_EQ_REFL])

  /- Welldefinedness follows from already established principles because if
     x = y then y' = y' 1 = y' (x' x) = y' (x' y) = (y' y) x' = 1 x' = x' -/

  let NADD_INV_WELLDEF ← do
    let TAC (tm : term) (ths : List thm) : tactic :=
      MATCH_MP_TAC NADD_EQ_TRANS THEN EXISTS_TAC tm THEN
      CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC ths]
    prove
     r"!x y. x === y ==> inv(x) === inv(y)"
     (REPEAT STRIP_TAC THEN
      ASM_CASES_TAC (← q r"x === &0") THENL
       [SUBGOAL_THEN (← q r"y === &0") ASSUME_TAC THENL
         [ASM_MESON_TAC [NADD_EQ_TRANS, NADD_EQ_SYM],
          ASM_REWRITE_TAC [nadd_inv, NADD_EQ_REFL]],
        SUBGOAL_THEN (← q r"~(y === &0)") ASSUME_TAC THENL
         [ASM_MESON_TAC [NADD_EQ_TRANS, NADD_EQ_SYM], ALL_TAC]] THEN
      TAC (← q r"inv(y) ** &1")
          [NADD_MUL_SYM, NADD_MUL_LID, NADD_EQ_TRANS] THEN
      TAC (← q r"inv(y) ** (inv(x) ** x)")
          [NADD_MUL_LINV, NADD_MUL_WELLDEF, NADD_EQ_REFL] THEN
      TAC (← q r"inv(y) ** (inv(x) ** y)")
          [NADD_MUL_WELLDEF, NADD_EQ_REFL, NADD_EQ_SYM] THEN
      TAC (← q r"(inv(y) ** y) ** inv(x)")
          [NADD_MUL_ASSOC, NADD_MUL_SYM, NADD_EQ_TRANS,
           NADD_MUL_WELLDEF, NADD_EQ_REFL] THEN
      ASM_MESON_TAC [NADD_MUL_LINV, NADD_MUL_WELLDEF, NADD_EQ_REFL,
        NADD_MUL_LID, NADD_EQ_TRANS, NADD_EQ_SYM])

  /- Definition of the new type. -/

  let (hreal_tybij1, hreal_tybij2) ←
    define_quotient_type "hreal" ("mk_hreal", "dest_hreal") r"(===)"
  let hreal_tybij := (hreal_tybij1, hreal_tybij2)

  for p in [("+", r"hreal_add:hreal->hreal->hreal"),
            ("*", r"hreal_mul:hreal->hreal->hreal"),
            ("<=", r"hreal_le:hreal->hreal->bool")] do
    overload_interface p

  for p in [("&", r"hreal_of_num:num->hreal"),
            ("inv", r"hreal_inv:hreal->hreal")] do
    override_interface p

  let (hreal_of_num, hreal_of_num_th) ←
    lift_function hreal_tybij.2 (NADD_EQ_REFL, NADD_EQ_TRANS)
    "hreal_of_num" NADD_OF_NUM_WELLDEF

  let (hreal_add, hreal_add_th) ←
    lift_function hreal_tybij.2 (NADD_EQ_REFL, NADD_EQ_TRANS)
    "hreal_add" NADD_ADD_WELLDEF

  let (hreal_mul, hreal_mul_th) ←
    lift_function hreal_tybij.2 (NADD_EQ_REFL, NADD_EQ_TRANS)
    "hreal_mul" NADD_MUL_WELLDEF

  let (hreal_le, hreal_le_th) ←
    lift_function hreal_tybij.2 (NADD_EQ_REFL, NADD_EQ_TRANS)
    "hreal_le" NADD_LE_WELLDEF

  let (hreal_inv, hreal_inv_th) ←
    lift_function hreal_tybij.2 (NADD_EQ_REFL, NADD_EQ_TRANS)
    "hreal_inv" NADD_INV_WELLDEF

  let HREAL_COMPLETE ← do
    let th1 ← ASSUME (← q r"(P:nadd->bool) = (\x. Q(mk_hreal((===) x)))")
    let th2 ← BETA_RULE (← AP_THM th1 (← q r"x:nadd"))
    let th3 ← lift_theorem hreal_tybij
                (NADD_EQ_REFL, NADD_EQ_SYM, NADD_EQ_TRANS)
                [hreal_of_num_th, hreal_add_th, hreal_mul_th, hreal_le_th, th2]
                (← SPEC_ALL NADD_COMPLETE)
    let th4 ← MATCH_MP (← DISCH_ALL th3) (REFL (← q r"\x. Q(mk_hreal((===) x)):bool"))
    let P ← q r"P:hreal->bool"
    CONV_RULE (fun t => pure (HolCore.Equal.GEN_ALPHA_CONV P t)) (← GEN_ALL th4)

  let lifted ←
    [NADD_OF_NUM_EQ, NADD_OF_NUM_LE, NADD_OF_NUM_ADD, NADD_OF_NUM_MUL,
     NADD_LE_REFL, NADD_LE_TRANS, NADD_LE_ANTISYM, NADD_LE_TOTAL, NADD_LE_ADD,
     NADD_LE_EXISTS, NADD_ARCH, NADD_ADD_SYM, NADD_ADD_ASSOC, NADD_ADD_LID,
     NADD_ADD_LCANCEL, NADD_MUL_SYM, NADD_MUL_ASSOC, NADD_MUL_LID, NADD_LDISTRIB,
     NADD_MUL_LINV, NADD_INV_0].mapM
      (lift_theorem hreal_tybij
         (NADD_EQ_REFL, NADD_EQ_SYM, NADD_EQ_TRANS)
             [hreal_of_num_th, hreal_add_th, hreal_mul_th,
              hreal_le_th, hreal_inv_th])
  let (HREAL_OF_NUM_EQ, HREAL_OF_NUM_LE, HREAL_OF_NUM_ADD, HREAL_OF_NUM_MUL,
       HREAL_LE_REFL, HREAL_LE_TRANS, HREAL_LE_ANTISYM, HREAL_LE_TOTAL,
       HREAL_LE_ADD, HREAL_LE_EXISTS, HREAL_ARCH, HREAL_ADD_SYM, HREAL_ADD_ASSOC,
       HREAL_ADD_LID, HREAL_ADD_LCANCEL, HREAL_MUL_SYM, HREAL_MUL_ASSOC,
       HREAL_MUL_LID, HREAL_ADD_LDISTRIB, HREAL_MUL_LINV, HREAL_INV_0) ←
    match lifted with
    | [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16,
       a17, a18, a19, a20, a21] =>
      pure (a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16,
            a17, a18, a19, a20, a21)
    | _ => throw "HREAL lifted theorems: expected 21"

  /- Consequential theorems needed later. -/

  let HREAL_LE_EXISTS_DEF ← prove
   r"!m n. m <= n <=> ?d. n = m + d"
   (REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC [HREAL_LE_EXISTS] THEN
    DISCH_THEN (CHOOSE_THEN SUBST1_TAC) THEN REWRITE_TAC [HREAL_LE_ADD])

  let HREAL_EQ_ADD_LCANCEL ← prove
   r"!m n p. (m + n = m + p) <=> (n = p)"
   (REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC [HREAL_ADD_LCANCEL] THEN
    DISCH_THEN SUBST1_TAC THEN REFL_TAC)

  let HREAL_EQ_ADD_RCANCEL ← prove
   r"!m n p. (m + p = n + p) <=> (m = n)"
   (ONCE_REWRITE_TAC [HREAL_ADD_SYM] THEN REWRITE_TAC [HREAL_EQ_ADD_LCANCEL])

  let HREAL_LE_ADD_LCANCEL ← prove
   r"!m n p. (m + n <= m + p) <=> (n <= p)"
   (REWRITE_TAC [HREAL_LE_EXISTS_DEF, ← GSYM HREAL_ADD_ASSOC,
      HREAL_EQ_ADD_LCANCEL])

  let HREAL_LE_ADD_RCANCEL ← prove
   r"!m n p. (m + p <= n + p) <=> (m <= n)"
   (ONCE_REWRITE_TAC [HREAL_ADD_SYM] THEN MATCH_ACCEPT_TAC HREAL_LE_ADD_LCANCEL)

  let HREAL_ADD_RID ← prove
   r"!n. n + &0 = n"
   (ONCE_REWRITE_TAC [HREAL_ADD_SYM] THEN MATCH_ACCEPT_TAC HREAL_ADD_LID)

  let HREAL_ADD_RDISTRIB ← prove
   r"!m n p. (m + n) * p = m * p + n * p"
   (ONCE_REWRITE_TAC [HREAL_MUL_SYM] THEN MATCH_ACCEPT_TAC HREAL_ADD_LDISTRIB)

  let HREAL_MUL_LZERO ← prove
   r"!m. &0 * m = &0"
   (GEN_TAC THEN MP_TAC (← SPECL [← q r"&0", ← q r"&1", ← q r"m:hreal"] HREAL_ADD_RDISTRIB) THEN
    REWRITE_TAC [HREAL_ADD_LID] THEN
    GEN_REWRITE_TAC (funpow 2 LAND_CONV) [← GSYM HREAL_ADD_LID] THEN
    REWRITE_TAC [HREAL_EQ_ADD_RCANCEL] THEN
    DISCH_THEN (fun th => tactic_of do pure (ACCEPT_TAC (← SYM th))))

  let HREAL_MUL_RZERO ← prove
   r"!m. m * &0 = &0"
   (ONCE_REWRITE_TAC [HREAL_MUL_SYM] THEN MATCH_ACCEPT_TAC HREAL_MUL_LZERO)

  let HREAL_ADD_AC ← prove
   r"(m + n = n + m) /\
   ((m + n) + p = m + (n + p)) /\
   (m + (n + p) = n + (m + p))"
   (REWRITE_TAC [HREAL_ADD_ASSOC, ← EQT_INTRO (← SPEC_ALL HREAL_ADD_SYM)] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC HREAL_ADD_SYM)

  let HREAL_LE_ADD2 ← prove
   r"!a b c d. a <= b /\ c <= d ==> a + c <= b + d"
   (REPEAT GEN_TAC THEN REWRITE_TAC [HREAL_LE_EXISTS_DEF] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q r"d1:hreal"))
      (X_CHOOSE_TAC (← q r"d2:hreal"))) THEN
    EXISTS_TAC (← q r"d1 + d2") THEN ASM_REWRITE_TAC [HREAL_ADD_AC])

  let HREAL_LE_MUL_RCANCEL_IMP ← prove
   r"!a b c. a <= b ==> a * c <= b * c"
   (REPEAT GEN_TAC THEN REWRITE_TAC [HREAL_LE_EXISTS_DEF] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"d:hreal") SUBST1_TAC) THEN
    EXISTS_TAC (← q r"d * c") THEN REWRITE_TAC [HREAL_ADD_RDISTRIB])

  return {
    nadd_inv, NADD_INV, NADD_MUL_LINV, NADD_INV_0, NADD_INV_WELLDEF,
    hreal_tybij1, hreal_tybij2, hreal_of_num, hreal_of_num_th, hreal_add,
    hreal_add_th, hreal_mul, hreal_mul_th, hreal_le, hreal_le_th, hreal_inv,
    hreal_inv_th, HREAL_COMPLETE, HREAL_OF_NUM_EQ, HREAL_OF_NUM_LE,
    HREAL_OF_NUM_ADD, HREAL_OF_NUM_MUL, HREAL_LE_REFL, HREAL_LE_TRANS,
    HREAL_LE_ANTISYM, HREAL_LE_TOTAL, HREAL_LE_ADD, HREAL_LE_EXISTS,
    HREAL_ARCH, HREAL_ADD_SYM, HREAL_ADD_ASSOC, HREAL_ADD_LID,
    HREAL_ADD_LCANCEL, HREAL_MUL_SYM, HREAL_MUL_ASSOC, HREAL_MUL_LID,
    HREAL_ADD_LDISTRIB, HREAL_MUL_LINV, HREAL_INV_0, HREAL_LE_EXISTS_DEF,
    HREAL_EQ_ADD_LCANCEL, HREAL_EQ_ADD_RCANCEL, HREAL_LE_ADD_LCANCEL,
    HREAL_LE_ADD_RCANCEL, HREAL_ADD_RID, HREAL_ADD_RDISTRIB, HREAL_MUL_LZERO,
    HREAL_MUL_RZERO, HREAL_ADD_AC, HREAL_LE_ADD2, HREAL_LE_MUL_RCANCEL_IMP }

/-- The signed-real representatives: operations on PAIRS of `hreal` standing
    for differences, where `(x,y)` represents `x - y` (realax.ml 1385-1588).
    Field names match the OCaml identifiers exactly, in OCaml order.

    ALL SIX operation definitions (1385-1402) have PAIRED / TUPLED left-hand
    sides, so each uses `new_definition_pair`, NOT the plain `new_definition`
    (which rejects a paired LHS with "Non-variable in LHS pattern").
    `treal_eq` (1409) is likewise paired.  `treal_add`/`treal_mul`/`treal_le`/
    `treal_eq` are INFIX; their `parse_as_infix` declarations already ran in
    `setupRealAxOverloads`, so they are not repeated here.

    `treal_inv` (1400) is a NESTED CONDITIONAL with SELECT terms.  A LATER
    stage adds the welldefinedness theorems (1594-1708) and the `real`
    quotient. -/
structure TrealThms where
  /- Operations on representatives (1385-1402). -/
  treal_of_num       : thm
  treal_neg          : thm
  treal_add          : thm
  treal_mul          : thm
  treal_le           : thm
  treal_inv          : thm
  /- The equivalence relation and proof it is one (1409-1426). -/
  treal_eq           : thm
  TREAL_EQ_REFL      : thm
  TREAL_EQ_SYM       : thm
  TREAL_EQ_TRANS     : thm
  /- Useful to avoid unnecessary use of the equivalence relation (1433). -/
  TREAL_EQ_AP        : thm
  /- Commutativity properties for injector (1441-1455). -/
  TREAL_OF_NUM_EQ    : thm
  TREAL_OF_NUM_LE    : thm
  TREAL_OF_NUM_ADD   : thm
  TREAL_OF_NUM_MUL   : thm
  /- Strong forms of equality for welldefinedness proofs (1466-1470). -/
  TREAL_ADD_SYM_EQ   : thm
  TREAL_MUL_SYM_EQ   : thm
  /- Properties of operations on representatives (1478-1588). -/
  TREAL_ADD_SYM      : thm
  TREAL_ADD_ASSOC    : thm
  TREAL_ADD_LID      : thm
  TREAL_ADD_LINV     : thm
  TREAL_MUL_SYM      : thm
  TREAL_MUL_ASSOC    : thm
  TREAL_MUL_LID      : thm
  TREAL_ADD_LDISTRIB : thm
  TREAL_LE_REFL      : thm
  TREAL_LE_ANTISYM   : thm
  TREAL_LE_TRANS     : thm
  TREAL_LE_TOTAL     : thm
  TREAL_LE_LADD_IMP  : thm
  TREAL_LE_MUL       : thm
  TREAL_INV_0        : thm
  TREAL_MUL_LINV     : thm
  /- Show that the operations respect the equivalence relation (1594-1708). -/
  TREAL_OF_NUM_WELLDEF : thm
  TREAL_NEG_WELLDEF    : thm
  TREAL_ADD_WELLDEFR   : thm
  TREAL_ADD_WELLDEF    : thm
  TREAL_MUL_WELLDEFR   : thm
  TREAL_MUL_WELLDEF    : thm
  TREAL_EQ_IMP_LE      : thm
  TREAL_LE_WELLDEF     : thm
  TREAL_INV_WELLDEF    : thm
  deriving Inhabited

/-- realax.ml 1383-1708: operations on representatives of signed reals.
    The definitions have paired left-hand sides, so `new_definition` here is
    the pair-aware one. -/
@[nospecialize]
def setupTreal [HolBase] (Pr : HolMath.Pair.PairThms)
    (A1 : HolMath.Arith.ArithThms1) (A2 : HolMath.Arith.ArithThms2)
    (H : HrealThms)
    (new_definition' : term → IO (Except String thm)) :
    ExceptT String IO TrealThms := do
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let { ADD_CLAUSES, .. } := A1
  let { MULT_CLAUSES, .. } := A2
  let { PAIR_EQ, FORALL_PAIR_THM, .. } := Pr
  let { HREAL_OF_NUM_EQ, HREAL_OF_NUM_LE, HREAL_OF_NUM_ADD, HREAL_OF_NUM_MUL,
        HREAL_LE_REFL, HREAL_LE_ANTISYM, HREAL_LE_TOTAL, HREAL_LE_ADD,
        HREAL_LE_EXISTS, HREAL_ADD_SYM, HREAL_ADD_ASSOC, HREAL_ADD_LID,
        HREAL_MUL_SYM, HREAL_MUL_ASSOC, HREAL_MUL_LID, HREAL_ADD_LDISTRIB,
        HREAL_MUL_LINV, HREAL_INV_0, HREAL_EQ_ADD_LCANCEL,
        HREAL_EQ_ADD_RCANCEL, HREAL_LE_ADD_LCANCEL, HREAL_LE_ADD_RCANCEL,
        HREAL_ADD_RID, HREAL_ADD_RDISTRIB, HREAL_MUL_LZERO, HREAL_MUL_RZERO,
        HREAL_ADD_AC, HREAL_LE_ADD2, HREAL_LE_MUL_RCANCEL_IMP, .. } := H
  let { EQ_SYM_EQ, .. } := HolBase.T
  let { SELECT_UNIQUE, COND_CLAUSES, .. } := HolBase.C

  /- Define operations on representatives of signed reals. -/

  let treal_of_num ← new_definition
   r"treal_of_num n = (&n, &0)"

  let treal_neg ← new_definition
   r"treal_neg ((x:hreal),(y:hreal)) = (y,x)"

  let treal_add ← new_definition
   r"(x1,y1) treal_add (x2,y2) = (x1 + x2, y1 + y2)"

  let treal_mul ← new_definition
   r"(x1,y1) treal_mul (x2,y2) = ((x1 * x2) + (y1 * y2),(x1 * y2) + (y1 * x2))"

  let treal_le ← new_definition
   r"(x1,y1) treal_le (x2,y2) <=> x1 + y2 <= x2 + y1"

  let treal_inv ← new_definition
   r"treal_inv(x,y) = if x = y then (&0, &0)
                    else if y <= x then (inv(@d. x = y + d), &0)
                    else (&0, inv(@d. y = x + d))"

  /- Define the equivalence relation and prove it *is* one. -/

  let treal_eq ← new_definition
   r"(x1,y1) treal_eq (x2,y2) <=> (x1 + y2 = x2 + y1)"

  let TREAL_EQ_REFL ← prove
   r"!x. x treal_eq x"
   (REWRITE_TAC [FORALL_PAIR_THM, treal_eq])

  let TREAL_EQ_SYM ← prove
   r"!x y. x treal_eq y <=> y treal_eq x"
   (REWRITE_TAC [FORALL_PAIR_THM, treal_eq, EQ_SYM_EQ])

  let TREAL_EQ_TRANS ← prove
   r"!x y z. x treal_eq y /\ y treal_eq z ==> x treal_eq z"
   (REWRITE_TAC [FORALL_PAIR_THM, treal_eq] THEN REPEAT GEN_TAC THEN
    DISCH_THEN (fun th => tactic_of do
      pure (MP_TAC (← MK_COMB (← F_F (AP_TERM (← q r"(+)")) pure (← CONJ_PAIR th))))) THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [HREAL_ADD_SYM] THEN
    REWRITE_TAC [← GSYM HREAL_ADD_ASSOC, HREAL_EQ_ADD_LCANCEL] THEN
    REWRITE_TAC [HREAL_ADD_ASSOC, HREAL_EQ_ADD_RCANCEL] THEN
    DISCH_THEN (fun th => tactic_of do
      pure (MATCH_ACCEPT_TAC (← ONCE_REWRITE_RULE [HREAL_ADD_SYM] th))))

  /- Useful to avoid unnecessary use of the equivalence relation. -/

  let TREAL_EQ_AP ← prove
   r"!x y. (x = y) ==> x treal_eq y"
   (SIMP_TAC [TREAL_EQ_REFL])

  /- Commutativity properties for injector. -/

  let TREAL_OF_NUM_EQ ← prove
   r"!m n. (treal_of_num m treal_eq treal_of_num n) <=> (m = n)"
   (REWRITE_TAC [treal_of_num, treal_eq, HREAL_OF_NUM_EQ, HREAL_ADD_RID])

  let TREAL_OF_NUM_LE ← prove
   r"!m n. (treal_of_num m treal_le treal_of_num n) <=> m <= n"
   (REWRITE_TAC [treal_of_num, treal_le, HREAL_OF_NUM_LE, HREAL_ADD_RID])

  let TREAL_OF_NUM_ADD ← prove
   r"!m n. (treal_of_num m treal_add treal_of_num n) treal_eq
         (treal_of_num(m + n))"
   (REWRITE_TAC [treal_of_num, treal_eq, treal_add,
     HREAL_OF_NUM_ADD, HREAL_ADD_RID, ADD_CLAUSES])

  let TREAL_OF_NUM_MUL ← prove
   r"!m n. (treal_of_num m treal_mul treal_of_num n) treal_eq
         (treal_of_num(m * n))"
   (REWRITE_TAC [treal_of_num, treal_eq, treal_mul,
     HREAL_OF_NUM_MUL, HREAL_MUL_RZERO, HREAL_MUL_LZERO, HREAL_ADD_RID,
     HREAL_ADD_LID, HREAL_ADD_RID, MULT_CLAUSES])

  /- Strong forms of equality are useful to simplify welldefinedness proofs. -/

  let TREAL_ADD_SYM_EQ ← prove
   r"!x y. x treal_add y = y treal_add x"
   (REWRITE_TAC [FORALL_PAIR_THM, treal_add, PAIR_EQ, HREAL_ADD_SYM])

  let TREAL_MUL_SYM_EQ ← prove
   r"!x y. x treal_mul y = y treal_mul x"
   (REWRITE_TAC [FORALL_PAIR_THM, treal_mul, HREAL_MUL_SYM, HREAL_ADD_SYM])

  /- Prove the properties of operations on representatives. -/

  let TREAL_ADD_SYM ← prove
   r"!x y. (x treal_add y) treal_eq (y treal_add x)"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC TREAL_EQ_AP THEN
    MATCH_ACCEPT_TAC TREAL_ADD_SYM_EQ)

  let TREAL_ADD_ASSOC ← prove
   r"!x y z. (x treal_add (y treal_add z)) treal_eq
           ((x treal_add y) treal_add z)"
   (SIMP_TAC [FORALL_PAIR_THM, TREAL_EQ_AP, treal_add, HREAL_ADD_ASSOC])

  let TREAL_ADD_LID ← prove
   r"!x. ((treal_of_num 0) treal_add x) treal_eq x"
   (REWRITE_TAC [FORALL_PAIR_THM, treal_of_num, treal_add, treal_eq,
                 HREAL_ADD_LID])

  let TREAL_ADD_LINV ← prove
   r"!x. ((treal_neg x) treal_add x) treal_eq (treal_of_num 0)"
   (REWRITE_TAC [FORALL_PAIR_THM, treal_neg, treal_add, treal_eq, treal_of_num,
                 HREAL_ADD_LID, HREAL_ADD_RID, HREAL_ADD_SYM])

  let TREAL_MUL_SYM ← prove
   r"!x y. (x treal_mul y) treal_eq (y treal_mul x)"
   (SIMP_TAC [TREAL_EQ_AP, TREAL_MUL_SYM_EQ])

  let TREAL_MUL_ASSOC ← prove
   r"!x y z. (x treal_mul (y treal_mul z)) treal_eq
           ((x treal_mul y) treal_mul z)"
   (SIMP_TAC [FORALL_PAIR_THM, TREAL_EQ_AP, treal_mul, HREAL_ADD_LDISTRIB,
              HREAL_ADD_RDISTRIB, ← GSYM HREAL_MUL_ASSOC, HREAL_ADD_AC])

  let TREAL_MUL_LID ← prove
   r"!x. ((treal_of_num 1) treal_mul x) treal_eq x"
   (SIMP_TAC [FORALL_PAIR_THM, treal_of_num, treal_mul, treal_eq] THEN
    REWRITE_TAC [HREAL_MUL_LZERO, HREAL_MUL_LID, HREAL_ADD_LID, HREAL_ADD_RID])

  let TREAL_ADD_LDISTRIB ← prove
   r"!x y z. (x treal_mul (y treal_add z)) treal_eq
           ((x treal_mul y) treal_add (x treal_mul z))"
   (SIMP_TAC [FORALL_PAIR_THM, TREAL_EQ_AP, treal_mul, treal_add,
              HREAL_ADD_LDISTRIB, PAIR_EQ, HREAL_ADD_AC])

  let TREAL_LE_REFL ← prove
   r"!x. x treal_le x"
   (REWRITE_TAC [FORALL_PAIR_THM, treal_le, HREAL_LE_REFL])

  let TREAL_LE_ANTISYM ← prove
   r"!x y. x treal_le y /\ y treal_le x <=> (x treal_eq y)"
   (REWRITE_TAC [FORALL_PAIR_THM, treal_le, treal_eq, HREAL_LE_ANTISYM])

  let TREAL_LE_TRANS ← prove
   r"!x y z. x treal_le y /\ y treal_le z ==> x treal_le z"
   (REWRITE_TAC [FORALL_PAIR_THM, treal_le] THEN REPEAT GEN_TAC THEN
    DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← MATCH_MP HREAL_LE_ADD2 th))) THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [HREAL_ADD_SYM] THEN
    REWRITE_TAC [← GSYM HREAL_ADD_ASSOC, HREAL_LE_ADD_LCANCEL] THEN
    REWRITE_TAC [HREAL_ADD_ASSOC, HREAL_LE_ADD_RCANCEL] THEN
    DISCH_THEN (fun th => tactic_of do
      pure (MATCH_ACCEPT_TAC (← ONCE_REWRITE_RULE [HREAL_ADD_SYM] th))))

  let TREAL_LE_TOTAL ← prove
   r"!x y. x treal_le y \/ y treal_le x"
   (REWRITE_TAC [FORALL_PAIR_THM, treal_le, HREAL_LE_TOTAL])

  let TREAL_LE_LADD_IMP ← prove
   r"!x y z. (y treal_le z) ==> (x treal_add y) treal_le (x treal_add z)"
   (REWRITE_TAC [FORALL_PAIR_THM, treal_le, treal_add] THEN
    REWRITE_TAC [← GSYM HREAL_ADD_ASSOC, HREAL_LE_ADD_LCANCEL] THEN
    ONCE_REWRITE_TAC [HREAL_ADD_SYM] THEN
    REWRITE_TAC [← GSYM HREAL_ADD_ASSOC, HREAL_LE_ADD_LCANCEL])

  let TREAL_LE_MUL ← prove
   r"!x y. (treal_of_num 0) treal_le x /\ (treal_of_num 0) treal_le y
         ==> (treal_of_num 0) treal_le (x treal_mul y)"
   (REWRITE_TAC [FORALL_PAIR_THM, treal_of_num, treal_le, treal_mul] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [HREAL_ADD_LID, HREAL_ADD_RID] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (fun th => tactic_of do
      pure ((CHOOSE_THEN SUBST1_TAC) (← MATCH_MP HREAL_LE_EXISTS th))) THEN
    REWRITE_TAC [HREAL_ADD_LDISTRIB, HREAL_LE_ADD_LCANCEL,
      ← GSYM HREAL_ADD_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV [HREAL_ADD_SYM] THEN
    ASM_REWRITE_TAC [HREAL_LE_ADD_LCANCEL] THEN
    MATCH_MP_TAC HREAL_LE_MUL_RCANCEL_IMP THEN ASM_REWRITE_TAC [])

  let TREAL_INV_0 ← prove
   r"treal_inv (treal_of_num 0) treal_eq (treal_of_num 0)"
   (REWRITE_TAC [treal_inv, treal_eq, treal_of_num])

  let TREAL_MUL_LINV ← prove
   r"!x. ~(x treal_eq treal_of_num 0) ==>
        (treal_inv(x) treal_mul x) treal_eq (treal_of_num 1)"
   (REWRITE_TAC [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:hreal", ← q r"y:hreal"] THEN
    PURE_REWRITE_TAC [treal_eq, treal_of_num, treal_mul, treal_inv] THEN
    PURE_REWRITE_TAC [HREAL_ADD_LID, HREAL_ADD_RID] THEN DISCH_TAC THEN
    PURE_ASM_REWRITE_TAC [COND_CLAUSES] THEN COND_CASES_TAC THEN
    PURE_REWRITE_TAC [treal_mul, treal_eq] THEN
    REWRITE_TAC [HREAL_ADD_LID, HREAL_ADD_RID,
                 HREAL_MUL_LZERO, HREAL_MUL_RZERO] THENL
     [ALL_TAC,
      DISJ_CASES_THEN MP_TAC (← SPECL [← q r"x:hreal", ← q r"y:hreal"] HREAL_LE_TOTAL) THEN
      ASM_REWRITE_TAC [] THEN DISCH_TAC] THEN
    FIRST_ASSUM (fun th => tactic_of do pure (MP_TAC (← MATCH_MP HREAL_LE_EXISTS th))) THEN
    DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← SELECT_RULE th))) THEN
    DISCH_THEN (fun th => tactic_of do
      pure (ASSUME_TAC (← SYM th) THEN
            GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th])) THEN
    REWRITE_TAC [HREAL_ADD_LDISTRIB] THEN
    GEN_REWRITE_TAC RAND_CONV [HREAL_ADD_SYM] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC HREAL_MUL_LINV THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (UNDISCH_TAC (← check is_eq (concl th)))) THEN
    ASM_REWRITE_TAC [HREAL_ADD_RID] THEN
    PURE_ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN ASM_REWRITE_TAC [])

  /- Show that the operations respect the equivalence relation. -/

  let TREAL_OF_NUM_WELLDEF ← prove
   r"!m n. (m = n) ==> (treal_of_num m) treal_eq (treal_of_num n)"
   (REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_ACCEPT_TAC TREAL_EQ_REFL)

  let TREAL_NEG_WELLDEF ← prove
   r"!x1 x2. x1 treal_eq x2 ==> (treal_neg x1) treal_eq (treal_neg x2)"
   (REWRITE_TAC [FORALL_PAIR_THM, treal_neg, treal_eq] THEN REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [HREAL_ADD_SYM] THEN ASM_REWRITE_TAC [])

  let TREAL_ADD_WELLDEFR ← prove
   r"!x1 x2 y. x1 treal_eq x2 ==> (x1 treal_add y) treal_eq (x2 treal_add y)"
   (REWRITE_TAC [FORALL_PAIR_THM, treal_add, treal_eq] THEN
    REWRITE_TAC [HREAL_EQ_ADD_RCANCEL, HREAL_ADD_ASSOC] THEN
    ONCE_REWRITE_TAC [HREAL_ADD_SYM] THEN
    REWRITE_TAC [HREAL_EQ_ADD_RCANCEL, HREAL_ADD_ASSOC])

  let TREAL_ADD_WELLDEF ← prove
   r"!x1 x2 y1 y2. x1 treal_eq x2 /\ y1 treal_eq y2 ==>
     (x1 treal_add y1) treal_eq (x2 treal_add y2)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC TREAL_EQ_TRANS THEN EXISTS_TAC (← q r"x1 treal_add y2") THEN
    CONJ_TAC THENL [ONCE_REWRITE_TAC [TREAL_ADD_SYM_EQ], ALL_TAC] THEN
    MATCH_MP_TAC TREAL_ADD_WELLDEFR THEN ASM_REWRITE_TAC [])

  let TREAL_MUL_WELLDEFR ← prove
   r"!x1 x2 y. x1 treal_eq x2 ==> (x1 treal_mul y) treal_eq (x2 treal_mul y)"
   (REWRITE_TAC [FORALL_PAIR_THM, treal_mul, treal_eq] THEN REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC [← AC HREAL_ADD_AC
      (← q r"(a + b) + (c + d) = (a + d) + (b + c)")] THEN
    REWRITE_TAC [← GSYM HREAL_ADD_RDISTRIB] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC [] THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC [HREAL_ADD_SYM] THEN POP_ASSUM SUBST1_TAC THEN REFL_TAC)

  let TREAL_MUL_WELLDEF ← prove
   r"!x1 x2 y1 y2. x1 treal_eq x2 /\ y1 treal_eq y2 ==>
     (x1 treal_mul y1) treal_eq (x2 treal_mul y2)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC TREAL_EQ_TRANS THEN EXISTS_TAC (← q r"x1 treal_mul y2") THEN
    CONJ_TAC THENL [ONCE_REWRITE_TAC [TREAL_MUL_SYM_EQ], ALL_TAC] THEN
    MATCH_MP_TAC TREAL_MUL_WELLDEFR THEN ASM_REWRITE_TAC [])

  let TREAL_EQ_IMP_LE ← prove
   r"!x y. x treal_eq y ==> x treal_le y"
   (SIMP_TAC [FORALL_PAIR_THM, treal_eq, treal_le, HREAL_LE_REFL])

  let TREAL_LE_WELLDEF ← prove
   r"!x1 x2 y1 y2. x1 treal_eq x2 /\ y1 treal_eq y2 ==>
     (x1 treal_le y1 <=> x2 treal_le y2)"
   (REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [MATCH_MP_TAC TREAL_LE_TRANS THEN EXISTS_TAC (← q r"y1:hreal#hreal") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC TREAL_LE_TRANS THEN EXISTS_TAC (← q r"x1:hreal#hreal") THEN
        ASM_REWRITE_TAC [] THEN MATCH_MP_TAC TREAL_EQ_IMP_LE THEN
        ONCE_REWRITE_TAC [TREAL_EQ_SYM],
        MATCH_MP_TAC TREAL_EQ_IMP_LE],
      MATCH_MP_TAC TREAL_LE_TRANS THEN EXISTS_TAC (← q r"y2:hreal#hreal") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC TREAL_LE_TRANS THEN EXISTS_TAC (← q r"x2:hreal#hreal") THEN
        ASM_REWRITE_TAC [] THEN MATCH_MP_TAC TREAL_EQ_IMP_LE,
        MATCH_MP_TAC TREAL_EQ_IMP_LE THEN ONCE_REWRITE_TAC [TREAL_EQ_SYM]]] THEN
    ASM_REWRITE_TAC [])

  let TREAL_INV_WELLDEF ← do
    let lemma ← prove
     r"(@d. x = x + d) = &0"
     (MATCH_MP_TAC SELECT_UNIQUE THEN BETA_TAC THEN
      GEN_TAC THEN GEN_REWRITE_TAC (funpow 2 LAND_CONV) [← GSYM HREAL_ADD_RID] THEN
      REWRITE_TAC [HREAL_EQ_ADD_LCANCEL] THEN
      MATCH_ACCEPT_TAC EQ_SYM_EQ)
    prove
     r"!x y. x treal_eq y ==> (treal_inv x) treal_eq (treal_inv y)"
     (REWRITE_TAC [FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"x1:hreal", ← q r"x2:hreal", ← q r"y1:hreal", ← q r"y2:hreal"] THEN
      PURE_REWRITE_TAC [treal_eq, treal_inv] THEN
      ASM_CASES_TAC (← q r"x1 :hreal = x2") THEN
      ASM_CASES_TAC (← q r"y1 :hreal = y2") THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [TREAL_EQ_REFL] THEN
      DISCH_THEN (fun th => tactic_of do
        pure (MP_TAC (← GEN_REWRITE_RULE RAND_CONV [HREAL_ADD_SYM] th))) THEN
      REWRITE_TAC [HREAL_EQ_ADD_LCANCEL, HREAL_EQ_ADD_RCANCEL] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC [HREAL_LE_REFL, lemma, HREAL_INV_0, TREAL_EQ_REFL] THEN
      ASM_CASES_TAC (← q r"x2 <= x1") THEN ASM_REWRITE_TAC [] THENL
       [FIRST_ASSUM (fun th => tactic_of do
          pure (ASSUME_TAC (← SYM (← SELECT_RULE (← MATCH_MP HREAL_LE_EXISTS th))))) THEN
        UNDISCH_TAC (← q r"x1 + y2 = x2 + y1") THEN
        FIRST_ASSUM (fun th => tactic_of do pure (SUBST1_TAC (← SYM th))) THEN
        REWRITE_TAC [HREAL_EQ_ADD_LCANCEL, ← GSYM HREAL_ADD_ASSOC] THEN
        DISCH_THEN (fun th => tactic_of do pure (SUBST1_TAC (← SYM th))) THEN
        REWRITE_TAC [← ONCE_REWRITE_RULE [HREAL_ADD_SYM] HREAL_LE_ADD] THEN
        GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV o BINDER_CONV o
          LAND_CONV) [HREAL_ADD_SYM] THEN
        REWRITE_TAC [HREAL_EQ_ADD_LCANCEL, TREAL_EQ_REFL],
        DISJ_CASES_THEN MP_TAC
          (← SPECL [← q r"x1:hreal", ← q r"x2:hreal"] HREAL_LE_TOTAL) THEN
        ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
        FIRST_ASSUM (fun th => tactic_of do
          pure (ASSUME_TAC (← SYM (← SELECT_RULE (← MATCH_MP HREAL_LE_EXISTS th))))) THEN
        UNDISCH_TAC (← q r"x1 + y2 = x2 + y1") THEN
        FIRST_ASSUM (fun th => tactic_of do pure (SUBST1_TAC (← SYM th))) THEN
        REWRITE_TAC [HREAL_EQ_ADD_LCANCEL, ← GSYM HREAL_ADD_ASSOC] THEN
        DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC [← ONCE_REWRITE_RULE [HREAL_ADD_SYM] HREAL_LE_ADD] THEN
        COND_CASES_TAC THENL
         [UNDISCH_TAC (← q r"(@d. x2 = x1 + d) + y1 <= y1:hreal") THEN
          GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← GSYM HREAL_ADD_LID] THEN
          REWRITE_TAC [← ONCE_REWRITE_RULE [HREAL_ADD_SYM] HREAL_LE_ADD_LCANCEL] THEN
          DISCH_TAC THEN SUBGOAL_THEN (← q r"(@d. x2 = x1 + d) = &0") MP_TAC THENL
           [ASM_REWRITE_TAC [← GSYM HREAL_LE_ANTISYM] THEN
            GEN_REWRITE_TAC RAND_CONV [← GSYM HREAL_ADD_LID] THEN
            REWRITE_TAC [HREAL_LE_ADD],
            DISCH_THEN SUBST_ALL_TAC THEN
            UNDISCH_TAC (← q r"x1 + &0 = x2") THEN
            ASM_REWRITE_TAC [HREAL_ADD_RID]],
          GEN_REWRITE_TAC (funpow 3 RAND_CONV o BINDER_CONV o LAND_CONV)
            [HREAL_ADD_SYM] THEN
          REWRITE_TAC [HREAL_EQ_ADD_LCANCEL, TREAL_EQ_REFL]]])

  return {
    treal_of_num, treal_neg, treal_add, treal_mul, treal_le, treal_inv,
    treal_eq, TREAL_EQ_REFL, TREAL_EQ_SYM, TREAL_EQ_TRANS, TREAL_EQ_AP,
    TREAL_OF_NUM_EQ, TREAL_OF_NUM_LE, TREAL_OF_NUM_ADD, TREAL_OF_NUM_MUL,
    TREAL_ADD_SYM_EQ, TREAL_MUL_SYM_EQ, TREAL_ADD_SYM, TREAL_ADD_ASSOC,
    TREAL_ADD_LID, TREAL_ADD_LINV, TREAL_MUL_SYM, TREAL_MUL_ASSOC,
    TREAL_MUL_LID, TREAL_ADD_LDISTRIB, TREAL_LE_REFL, TREAL_LE_ANTISYM,
    TREAL_LE_TRANS, TREAL_LE_TOTAL, TREAL_LE_LADD_IMP, TREAL_LE_MUL,
    TREAL_INV_0, TREAL_MUL_LINV, TREAL_OF_NUM_WELLDEF, TREAL_NEG_WELLDEF,
    TREAL_ADD_WELLDEFR, TREAL_ADD_WELLDEF, TREAL_MUL_WELLDEFR,
    TREAL_MUL_WELLDEF, TREAL_EQ_IMP_LE, TREAL_LE_WELLDEF, TREAL_INV_WELLDEF }

/-- The THIRD and final type construction: `real` as a QUOTIENT of
    `hreal#hreal` by `treal_eq` (realax.ml 1711-1973).  Field names match the
    OCaml identifiers exactly, in OCaml order.

    `real_tybij` (1712) is stored as the PAIR `(real_tybij1, real_tybij2)`
    returned by `define_quotient_type`.  The SIX `lift_function` calls each
    return a PAIR `(real_X, real_X_th)`; both halves are kept because the
    `_th` halves are the `trths` argument to `lift_theorem`.  NOTE `real_neg`
    is new at this layer (there was no `nadd_neg`/`hreal_neg`), so there are
    SIX lift_functions, not five.

    `real_pow` (1799) is the ONLY recursive definition in this file, built
    with `new_recursive_definition num_RECURSION`.  The other eight additional
    definitions have SIMPLE LHS so use the plain `new_definition`. -/
structure RealThms where
  /- Definition of the quotient type (1712-1757). -/
  real_tybij1        : thm
  real_tybij2        : thm
  real_of_num        : thm
  real_of_num_th     : thm
  real_neg           : thm
  real_neg_th        : thm
  real_add           : thm
  real_add_th        : thm
  real_mul           : thm
  real_mul_th        : thm
  real_le            : thm
  real_le_th         : thm
  real_inv           : thm
  real_inv_th        : thm
  /- The 20 lifted first-order theorems (1738-1757). -/
  REAL_ADD_SYM       : thm
  REAL_ADD_ASSOC     : thm
  REAL_ADD_LID       : thm
  REAL_ADD_LINV      : thm
  REAL_MUL_SYM       : thm
  REAL_MUL_ASSOC     : thm
  REAL_MUL_LID       : thm
  REAL_ADD_LDISTRIB  : thm
  REAL_LE_REFL       : thm
  REAL_LE_ANTISYM    : thm
  REAL_LE_TRANS      : thm
  REAL_LE_TOTAL      : thm
  REAL_LE_LADD_IMP   : thm
  REAL_LE_MUL        : thm
  REAL_INV_0         : thm
  REAL_MUL_LINV      : thm
  REAL_OF_NUM_EQ     : thm
  REAL_OF_NUM_LE     : thm
  REAL_OF_NUM_ADD    : thm
  REAL_OF_NUM_MUL    : thm
  /- Additional definitions (1786-1807). -/
  real_sub           : thm
  real_lt            : thm
  real_ge            : thm
  real_gt            : thm
  real_abs           : thm
  real_pow           : thm
  real_div           : thm
  real_max           : thm
  real_min           : thm
  /- The supremum property (1813-1951). -/
  REAL_HREAL_LEMMA1      : thm
  REAL_HREAL_LEMMA2      : thm
  REAL_COMPLETE_SOMEPOS  : thm
  REAL_COMPLETE          : thm
  deriving Inhabited

/-- realax.ml 1709-1973: the quotient type `real`, its interface, the
    additional definitions, and completeness. -/
@[nospecialize]
def setupReal [HolBase] (Pr : HolMath.Pair.PairThms) (H : HrealThms)
    (Tr : TrealThms) (num_RECURSION : thm)
    (new_definition' : term → IO (Except String thm))
    (new_recursive_definition' : thm → term → IO (Except String thm))
    (define_quotient_type' :
      String → String × String → term → IO (Except String (thm × thm)))
    (lift_function' :
      thm → thm × thm → String → thm → IO (Except String (thm × thm)))
    (lift_theorem' :
      thm × thm → thm × thm × thm → List thm → thm → IO (Except String thm))
    (overload_interface' : String → term → IO (Except String Unit))
    (parse_as_prefix : String → IO Unit)
    (parse_as_infix : String × (Int × String) → IO Unit)
    (prioritize_overload : hol_type → IO Unit)
    (reduce_interface' : String → term → IO (Except String Unit))
    (remove_interface : String → IO Unit) :
    ExceptT String IO RealThms := do
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let new_recursive_definition (ax : thm) (s : String) : ExceptT String IO thm := do
    new_recursive_definition' ax (← q s)
  let define_quotient_type (ty : String) (names : String × String) (s : String) :
      ExceptT String IO (thm × thm) := do
    define_quotient_type' ty names (← q s)
  let lift_function (tybij : thm) (refl_trans : thm × thm) (name : String) (wth : thm) :
      ExceptT String IO (thm × thm) :=
    lift_function' tybij refl_trans name wth
  let lift_theorem (tybij : thm × thm) (eqvs : thm × thm × thm) (trths : List thm)
      (th : thm) : ExceptT String IO thm :=
    lift_theorem' tybij eqvs trths th
  let overload_interface (p : String × String) : ExceptT String IO Unit := do
    overload_interface' p.1 (← q p.2)
  let reduce_interface (p : String × String) : ExceptT String IO Unit := do
    reduce_interface' p.1 (← q p.2)
  let { PAIR, .. } := Pr
  let { HREAL_COMPLETE, HREAL_LE_ANTISYM, HREAL_LE_ADD, HREAL_LE_EXISTS,
        HREAL_ADD_SYM, HREAL_ADD_ASSOC, HREAL_ADD_LID, HREAL_EQ_ADD_LCANCEL,
        HREAL_ADD_RID, .. } := H
  let { treal_of_num, treal_le, treal_eq, TREAL_EQ_REFL, TREAL_EQ_SYM,
        TREAL_EQ_TRANS, TREAL_OF_NUM_EQ, TREAL_OF_NUM_LE, TREAL_OF_NUM_ADD,
        TREAL_OF_NUM_MUL, TREAL_ADD_SYM, TREAL_ADD_ASSOC, TREAL_ADD_LID,
        TREAL_ADD_LINV, TREAL_MUL_SYM, TREAL_MUL_ASSOC, TREAL_MUL_LID,
        TREAL_ADD_LDISTRIB, TREAL_LE_REFL, TREAL_LE_ANTISYM, TREAL_LE_TRANS,
        TREAL_LE_TOTAL, TREAL_LE_LADD_IMP, TREAL_LE_MUL, TREAL_INV_0,
        TREAL_MUL_LINV, TREAL_OF_NUM_WELLDEF, TREAL_NEG_WELLDEF,
        TREAL_ADD_WELLDEF, TREAL_MUL_WELLDEF, TREAL_LE_WELLDEF,
        TREAL_INV_WELLDEF, .. } := Tr
  let { EQ_SYM_EQ, BETA_THM, EQ_IMP, EXISTS_REFL, .. } := HolBase.T
  let { FUN_EQ_THM, SELECT_REFL, .. } := HolBase.C

  /- Now define the quotient type -- the reals at last! -/

  let (real_tybij1, real_tybij2) ←
    define_quotient_type "real" ("mk_real", "dest_real") r"(treal_eq)"
  let real_tybij := (real_tybij1, real_tybij2)

  let (real_of_num, real_of_num_th) ←
    lift_function real_tybij.2 (TREAL_EQ_REFL, TREAL_EQ_TRANS)
    "real_of_num" TREAL_OF_NUM_WELLDEF

  let (real_neg, real_neg_th) ←
    lift_function real_tybij.2 (TREAL_EQ_REFL, TREAL_EQ_TRANS)
    "real_neg" TREAL_NEG_WELLDEF

  let (real_add, real_add_th) ←
    lift_function real_tybij.2 (TREAL_EQ_REFL, TREAL_EQ_TRANS)
    "real_add" TREAL_ADD_WELLDEF

  let (real_mul, real_mul_th) ←
    lift_function real_tybij.2 (TREAL_EQ_REFL, TREAL_EQ_TRANS)
    "real_mul" TREAL_MUL_WELLDEF

  let (real_le, real_le_th) ←
    lift_function real_tybij.2 (TREAL_EQ_REFL, TREAL_EQ_TRANS)
    "real_le" TREAL_LE_WELLDEF

  let (real_inv, real_inv_th) ←
    lift_function real_tybij.2 (TREAL_EQ_REFL, TREAL_EQ_TRANS)
    "real_inv" TREAL_INV_WELLDEF

  let lifted ←
    [TREAL_ADD_SYM, TREAL_ADD_ASSOC, TREAL_ADD_LID, TREAL_ADD_LINV,
     TREAL_MUL_SYM, TREAL_MUL_ASSOC, TREAL_MUL_LID,
     TREAL_ADD_LDISTRIB,
     TREAL_LE_REFL, TREAL_LE_ANTISYM, TREAL_LE_TRANS, TREAL_LE_TOTAL,
     TREAL_LE_LADD_IMP, TREAL_LE_MUL,
     TREAL_INV_0, TREAL_MUL_LINV,
     TREAL_OF_NUM_EQ, TREAL_OF_NUM_LE, TREAL_OF_NUM_ADD, TREAL_OF_NUM_MUL].mapM
      (lift_theorem real_tybij (TREAL_EQ_REFL, TREAL_EQ_SYM, TREAL_EQ_TRANS)
        [real_of_num_th, real_neg_th, real_add_th,
         real_mul_th, real_le_th, real_inv_th])
  let (REAL_ADD_SYM, REAL_ADD_ASSOC, REAL_ADD_LID, REAL_ADD_LINV,
       REAL_MUL_SYM, REAL_MUL_ASSOC, REAL_MUL_LID,
       REAL_ADD_LDISTRIB,
       REAL_LE_REFL, REAL_LE_ANTISYM, REAL_LE_TRANS, REAL_LE_TOTAL,
       REAL_LE_LADD_IMP, REAL_LE_MUL,
       REAL_INV_0, REAL_MUL_LINV,
       REAL_OF_NUM_EQ, REAL_OF_NUM_LE, REAL_OF_NUM_ADD, REAL_OF_NUM_MUL) ←
    match lifted with
    | [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16,
       a17, a18, a19, a20] =>
      pure (a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16,
            a17, a18, a19, a20)
    | _ => throw "REAL lifted theorems: expected 20"

  /- Set up a friendly interface. -/

  parse_as_prefix "--"
  parse_as_infix ("/", (22, "left"))
  parse_as_infix ("pow", (24, "left"))

  for p in [("+", r"real_add:real->real->real"), ("-", r"real_sub:real->real->real"),
            ("*", r"real_mul:real->real->real"), ("/", r"real_div:real->real->real"),
            ("<", r"real_lt:real->real->bool"), ("<=", r"real_le:real->real->bool"),
            (">", r"real_gt:real->real->bool"), (">=", r"real_ge:real->real->bool"),
            ("--", r"real_neg:real->real"), ("pow", r"real_pow:real->num->real"),
            ("inv", r"real_inv:real->real"), ("abs", r"real_abs:real->real"),
            ("max", r"real_max:real->real->real"), ("min", r"real_min:real->real->real"),
            ("&", r"real_of_num:num->real")] do
    overload_interface p

  let prioritize_real (_ : Unit) : IO Unit := prioritize_overload (hol_type.Tyapp "real" [])
  prioritize_real ()

  /- Additional definitions. -/

  let real_sub ← new_definition
   r"x - y = x + --y"

  let real_lt ← new_definition
   r"x < y <=> ~(y <= x)"

  let real_ge ← new_definition
   r"x >= y <=> y <= x"

  let real_gt ← new_definition
   r"x > y <=> y < x"

  let real_abs ← new_definition
   r"abs(x) = if &0 <= x then x else --x"

  let real_pow ← new_recursive_definition num_RECURSION
   r"(x pow 0 = &1) /\
   (!n. x pow (SUC n) = x * (x pow n))"

  let real_div ← new_definition
   r"x / y = x * inv(y)"

  let real_max ← new_definition
   r"real_max m n = if m <= n then n else m"

  let real_min ← new_definition
   r"real_min m n = if m <= n then m else n"

  /- Derive the supremum property for an arbitrary bounded nonempty set -/

  let REAL_HREAL_LEMMA1 ← prove
   r"?r:hreal->real.
       (!x. &0 <= x <=> ?y. x = r y) /\
       (!y z. y <= z <=> r y <= r z)"
   (EXISTS_TAC (← q r"\y. mk_real((treal_eq)(y,hreal_of_num 0))") THEN
    REWRITE_TAC [← GSYM real_le_th] THEN
    REWRITE_TAC [treal_le, HREAL_ADD_LID, HREAL_ADD_RID] THEN
    GEN_TAC THEN EQ_TAC THENL
     [MP_TAC (← INST [(← q r"dest_real x", ← q r"r:hreal#hreal->bool")] real_tybij.2) THEN
      REWRITE_TAC [real_tybij.1] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"p:hreal#hreal") MP_TAC) THEN
      DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← AP_TERM (← q r"mk_real") th))) THEN
      REWRITE_TAC [real_tybij.1] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC [← GSYM real_of_num_th, ← GSYM real_le_th] THEN
      SUBST1_TAC (← GSYM (← ISPEC (← q r"p:hreal#hreal") PAIR)) THEN
      PURE_REWRITE_TAC [treal_of_num, treal_le] THEN
      PURE_REWRITE_TAC [HREAL_ADD_LID, HREAL_ADD_RID] THEN
      DISCH_THEN (fun th => tactic_of do
        pure ((X_CHOOSE_THEN (← q r"d:hreal") SUBST1_TAC) (← MATCH_MP HREAL_LE_EXISTS th))) THEN
      EXISTS_TAC (← q r"d:hreal") THEN AP_TERM_TAC THEN
      ONCE_REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"q:hreal#hreal") THEN
      SUBST1_TAC (← GSYM (← ISPEC (← q r"q:hreal#hreal") PAIR)) THEN
      PURE_REWRITE_TAC [treal_eq] THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [HREAL_ADD_SYM] THEN
      REWRITE_TAC [← GSYM HREAL_ADD_ASSOC, HREAL_EQ_ADD_LCANCEL] THEN
      REWRITE_TAC [HREAL_ADD_RID],
      DISCH_THEN (CHOOSE_THEN SUBST1_TAC) THEN
      REWRITE_TAC [← GSYM real_of_num_th, ← GSYM real_le_th] THEN
      REWRITE_TAC [treal_of_num, treal_le] THEN
      REWRITE_TAC [HREAL_ADD_LID, HREAL_ADD_RID] THEN
      GEN_REWRITE_TAC RAND_CONV [← GSYM HREAL_ADD_LID] THEN
      REWRITE_TAC [HREAL_LE_ADD]])

  let REAL_HREAL_LEMMA2 ← prove
   r"?h r. (!x:hreal. h(r x) = x) /\
         (!x. &0 <= x ==> (r(h x) = x)) /\
         (!x:hreal. &0 <= r x) /\
         (!x y. x <= y <=> r x <= r y)"
   (STRIP_ASSUME_TAC REAL_HREAL_LEMMA1 THEN
    EXISTS_TAC (← q r"\x:real. @y:hreal. x = r y") THEN
    EXISTS_TAC (← q r"r:hreal->real") THEN
    ASM_REWRITE_TAC [BETA_THM] THEN
    SUBGOAL_THEN (← q r"!y z. ((r:hreal->real) y = r z) <=> (y = z)") ASSUME_TAC THENL
     [ASM_REWRITE_TAC [← GSYM REAL_LE_ANTISYM, ← GSYM HREAL_LE_ANTISYM], ALL_TAC] THEN
    ASM_REWRITE_TAC [← GEN_REWRITE_RULE (LAND_CONV o BINDER_CONV) [EQ_SYM_EQ]
      (← SPEC_ALL SELECT_REFL), ← GSYM EXISTS_REFL] THEN
    GEN_TAC THEN
    DISCH_THEN (fun th => tactic_of do pure (ACCEPT_TAC (← SYM (← SELECT_RULE th)))))

  let REAL_COMPLETE_SOMEPOS ← prove
   r"!P. (?x. P x /\ &0 <= x) /\
       (?M. !x. P x ==> x <= M)
       ==> ?M. (!x. P x ==> x <= M) /\
               !M'. (!x. P x ==> x <= M') ==> M <= M'"
   (REPEAT STRIP_TAC THEN STRIP_ASSUME_TAC REAL_HREAL_LEMMA2 THEN
    MP_TAC (← SPEC (← q r"\y:hreal. (P:real->bool)(r y)") HREAL_COMPLETE) THEN
    BETA_TAC THEN
    W (fun g => tactic_of do
      pure (C SUBGOAL_THEN MP_TAC
        (← funpowM 2 (fun t => Prod.fst <$> dest_imp t) (snd g)))) THENL
     [CONJ_TAC THENL
       [EXISTS_TAC (← q r"(h:real->hreal) x") THEN
        UNDISCH_TAC (← q r"(P:real->bool) x") THEN
        MATCH_MP_TAC (← TAUT (← q r"(b <=> a) ==> a ==> b")) THEN
        AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
        EXISTS_TAC (← q r"(h:real->hreal) M") THEN
        X_GEN_TAC (← q r"y:hreal") THEN DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN
        ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC (← TAUT (← q r"(b <=> a) ==> a ==> b")) THEN
        AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"x:real") THEN
        ASM_REWRITE_TAC [] THEN FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC []],
      MATCH_MP_TAC (← TAUT (← q r"(b ==> c) ==> a ==> (a ==> b) ==> c")) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"B:hreal") STRIP_ASSUME_TAC)] THEN
    EXISTS_TAC (← q r"(r:hreal->real) B") THEN CONJ_TAC THENL
     [X_GEN_TAC (← q r"z:real") THEN DISCH_TAC THEN
      DISJ_CASES_TAC (← SPECL [← q r"&0", ← q r"z:real"] REAL_LE_TOTAL) THENL
       [ANTE_RES_THEN (fun th => tactic_of do pure (SUBST1_TAC (← SYM th)))
          (← ASSUME (← q r"&0 <= z")) THEN
        FIRST_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC I [← GSYM th])) THEN
        FIRST_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC (← q r"(P:real->bool) z") THEN
        MATCH_MP_TAC (← TAUT (← q r"(b <=> a) ==> a ==> b")) THEN
        AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC [],
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"&0") THEN
        ASM_REWRITE_TAC []],
      X_GEN_TAC (← q r"C:real") THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"B:hreal <= (h(C:real))") MP_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
        SUBGOAL_THEN (← q r"(r:hreal->real)(h C) = C") (fun th => ASM_REWRITE_TAC [th]),
        ASM_REWRITE_TAC [] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"x:real") THEN
      ASM_REWRITE_TAC [] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC []])

  let REAL_COMPLETE ← do
    let lemma ← prove
     r"y = (y - x) + x"
     (REWRITE_TAC [real_sub, ← GSYM REAL_ADD_ASSOC, REAL_ADD_LINV] THEN
      ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN REWRITE_TAC [REAL_ADD_LID])
    prove
     r"!P. (?x. P x) /\
       (?M. !x. P x ==> x <= M)
       ==> ?M. (!x. P x ==> x <= M) /\
               !M'. (!x. P x ==> x <= M') ==> M <= M'"
     (REPEAT STRIP_TAC THEN
      DISJ_CASES_TAC (← SPECL [← q r"&0", ← q r"x:real"] REAL_LE_TOTAL) THENL
       [MATCH_MP_TAC REAL_COMPLETE_SOMEPOS THEN CONJ_TAC THENL
         [EXISTS_TAC (← q r"x:real"), EXISTS_TAC (← q r"M:real")] THEN
        ASM_REWRITE_TAC [],
        FIRST_ASSUM (fun th => tactic_of do pure (MP_TAC (← MATCH_MP REAL_LE_LADD_IMP th))) THEN
        DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"--x") th))) THEN
        REWRITE_TAC [REAL_ADD_LINV] THEN
        ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN REWRITE_TAC [REAL_ADD_LID] THEN
        DISCH_TAC THEN
        MP_TAC (← SPEC (← q r"\y. P(y + x) :bool") REAL_COMPLETE_SOMEPOS) THEN
        BETA_TAC THEN
        W (fun g => tactic_of do
          pure (C SUBGOAL_THEN MP_TAC
            (← funpowM 2 (fun t => Prod.fst <$> dest_imp t) (snd g)))) THENL
         [CONJ_TAC THENL
           [EXISTS_TAC (← q r"&0") THEN ASM_REWRITE_TAC [REAL_LE_REFL, REAL_ADD_LID],
            EXISTS_TAC (← q r"M + --x") THEN GEN_TAC THEN
            DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN
            DISCH_THEN (fun th => tactic_of do
              pure (MP_TAC (← SPEC (← q r"--x") (← MATCH_MP REAL_LE_LADD_IMP th)))) THEN
            DISCH_THEN (fun th => tactic_of do
              pure (MP_TAC (← ONCE_REWRITE_RULE [REAL_ADD_SYM] th))) THEN
            REWRITE_TAC [← GSYM REAL_ADD_ASSOC] THEN
            REWRITE_TAC [← ONCE_REWRITE_RULE [REAL_ADD_SYM] REAL_ADD_LINV] THEN
            REWRITE_TAC [← ONCE_REWRITE_RULE [REAL_ADD_SYM] REAL_ADD_LID]],
          MATCH_MP_TAC (← TAUT (← q r"(b ==> c) ==> a ==> (a ==> b) ==> c")) THEN
          DISCH_THEN (X_CHOOSE_THEN (← q r"B:real") STRIP_ASSUME_TAC)] THEN
        EXISTS_TAC (← q r"B + x") THEN CONJ_TAC THENL
         [GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [lemma] THEN
          DISCH_THEN (ANTE_RES_THEN
            (fun th => tactic_of do
              pure (MP_TAC (← SPEC (← q r"x:real") (← MATCH_MP REAL_LE_LADD_IMP th))))) THEN
          ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
          REWRITE_TAC [real_sub, ← GSYM REAL_ADD_ASSOC, REAL_ADD_LINV] THEN
          REWRITE_TAC [← ONCE_REWRITE_RULE [REAL_ADD_SYM] REAL_ADD_LID] THEN
          REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
          ASM_REWRITE_TAC [],
          REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"B <= M' - x") MP_TAC THENL
           [FIRST_ASSUM MATCH_MP_TAC THEN X_GEN_TAC (← q r"z:real") THEN DISCH_TAC THEN
            SUBGOAL_THEN (← q r"z + x <= M'") MP_TAC THENL
             [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
              DISCH_THEN (fun th => tactic_of do
                pure (MP_TAC (← SPEC (← q r"--x") (← MATCH_MP REAL_LE_LADD_IMP th)))) THEN
              ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
              REWRITE_TAC [real_sub] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
              AP_TERM_TAC THEN REWRITE_TAC [← GSYM REAL_ADD_ASSOC] THEN
              REWRITE_TAC [← ONCE_REWRITE_RULE [REAL_ADD_SYM] REAL_ADD_LINV] THEN
              REWRITE_TAC [← ONCE_REWRITE_RULE [REAL_ADD_SYM] REAL_ADD_LID]],
           DISCH_THEN (fun th => tactic_of do
             pure (MP_TAC (← SPEC (← q r"x:real") (← MATCH_MP REAL_LE_LADD_IMP th)))) THEN
           MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
            [MATCH_ACCEPT_TAC REAL_ADD_SYM,
             ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN REWRITE_TAC [real_sub] THEN
             REWRITE_TAC [← GSYM REAL_ADD_ASSOC, REAL_ADD_LINV] THEN
             REWRITE_TAC [← ONCE_REWRITE_RULE [REAL_ADD_SYM] REAL_ADD_LID]]]]])

  for p in [("+", r"hreal_add:hreal->hreal->hreal"),
            ("*", r"hreal_mul:hreal->hreal->hreal"),
            ("<=", r"hreal_le:hreal->hreal->bool"),
            ("inv", r"hreal_inv:hreal->hreal")] do
    reduce_interface p

  for s in ["**", "++", "<<=", "===", "fn", "afn"] do
    remove_interface s

  return {
    real_tybij1, real_tybij2, real_of_num, real_of_num_th, real_neg,
    real_neg_th, real_add, real_add_th, real_mul, real_mul_th, real_le,
    real_le_th, real_inv, real_inv_th, REAL_ADD_SYM, REAL_ADD_ASSOC,
    REAL_ADD_LID, REAL_ADD_LINV, REAL_MUL_SYM, REAL_MUL_ASSOC, REAL_MUL_LID,
    REAL_ADD_LDISTRIB, REAL_LE_REFL, REAL_LE_ANTISYM, REAL_LE_TRANS,
    REAL_LE_TOTAL, REAL_LE_LADD_IMP, REAL_LE_MUL, REAL_INV_0, REAL_MUL_LINV,
    REAL_OF_NUM_EQ, REAL_OF_NUM_LE, REAL_OF_NUM_ADD, REAL_OF_NUM_MUL, real_sub,
    real_lt, real_ge, real_gt, real_abs, real_pow, real_div, real_max,
    real_min, REAL_HREAL_LEMMA1, REAL_HREAL_LEMMA2, REAL_COMPLETE_SOMEPOS,
    REAL_COMPLETE }

end

end HolMath.RealAx
