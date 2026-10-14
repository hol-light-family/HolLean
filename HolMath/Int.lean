/- File: Int.lean
Theory of integers.

The integers are carved out of the real numbers; hence all the
universal theorems can be derived trivially from the real analog.

Original       John Harrison, University of Cambridge Computer Laboratory
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Lean4 translation by Chris Walton 2026

`int` is carved out of `real` by `new_type_definition` against `integer`, so
most integer theorems are lifted from their real analogues by `INT_OF_REAL_THM`
rather than proved.  OCaml shadows `INT_ARITH`, `INT_ARITH_TAC`, `INTEGER_TAC`,
`INTEGER_RULE` and `ASM_INT_ARITH_TAC`, defining each twice; Lean cannot shadow,
so the two versions are numbered 1 and 2 (the second handles `div` and `rem`).
Many top-level entries mutate global parser state (overloads, infixes,
`prioritize_num`) and so must run exactly once and in order. -/

import HolMath.CalcRat
import HolMath.Base

namespace HolMath.Int

set_option maxRecDepth 8000

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax


/- ---------------------------------------------------------------------- -/
/- Representing predicate. The "is_int" variant is useful for backwards   -/
/- compatibility with former definition of "is_int" constant, now removed.-/
/- ---------------------------------------------------------------------- -/

/-- `integer` (int.ml 20).  Creates a constant, so Session runs it once. -/
def setupInteger (new_definition : term → IO (Except String thm)) :
    ExceptT String IO thm := do
  ExceptT.mk (new_definition (← q r"integer(x) <=> ?n. abs(x) = &n"))

/-- `is_int` (int.ml 23) and the theorem `?x. integer x` that int.ml 32 passes
    to `new_type_definition`. -/
structure IntExistence where
  /-- `is_int` (int.ml 23). -/
  is_int : thm
  /-- `?x. integer x` (int.ml 32), the existence theorem fed to
      `new_type_definition`. -/
  int_exists : thm
  deriving Inhabited

/-- int.ml 23-34.  `REAL_ARITH` is calc_rat.ml's final one (Session's
    `REAL_ARITH3`), so `REAL_ARITH_TAC` is `CONV_TAC REAL_ARITH3`. -/
@[nospecialize]
def setupIntExistence [HolBase]
    (R : HolMath.RealAx.RealThms)
    (integer : thm)
    (REAL_ARITH : term → IO (Except String thm)) :
    ExceptT String IO IntExistence := do
  let { EXISTS_OR_THM, EXISTS_REFL, .. } := HolBase.T
  let { REAL_OF_NUM_EQ, .. } := R
  let REAL_ARITH_TAC : tactic := CONV_TAC REAL_ARITH

  let is_int ← prove
   r"integer(x) <=> ?n. x = &n \/ x = -- &n"
   (REWRITE_TAC [integer] THEN AP_TERM_TAC THEN ABS_TAC THEN REAL_ARITH_TAC)

  -- The argument of `new_type_definition "int" ...` (int.ml 32).
  let int_exists ← prove
   r"?x. integer x"
   (EXISTS_TAC (← q r"&0") THEN
    REWRITE_TAC [is_int, REAL_OF_NUM_EQ, EXISTS_OR_THM, ← GSYM EXISTS_REFL])

  return { is_int, int_exists }

/- ---------------------------------------------------------------------- -/
/- Type of integers.                                                      -/
/- ---------------------------------------------------------------------- -/

/-- int.ml 31-52.  `int_tybij` itself (the `new_type_definition` call, which
    creates the type) is made by Session and passed in. -/
structure IntTybij where
  /-- `int_tybij` (int.ml 31): the conjoined bijection
      `(!a. int_of_real(real_of_int a) = a) /\
       (!r. integer r <=> real_of_int(int_of_real r) = r)`. -/
  int_tybij : thm
  /-- `int_abstr` (int.ml 36) = `SPEC_ALL(CONJUNCT1 int_tybij)`. -/
  int_abstr : thm
  /-- `int_rep` (int.ml 36) = `SPEC_ALL(CONJUNCT2 int_tybij)`. -/
  int_rep : thm
  /-- `dest_int_rep` (int.ml 39):
      `!i. ?n. (real_of_int i = &n) \/ (real_of_int i = --(&n))`. -/
  dest_int_rep : thm
  /-- `INTEGER_REAL_OF_INT` (int.ml 43): `!x. integer(real_of_int x)`. -/
  INTEGER_REAL_OF_INT : thm
  /-- `int_eq` (int.ml 52): `!x y. (x = y) <=> (real_of_int x = real_of_int y)`. -/
  int_eq : thm
  deriving Inhabited

@[nospecialize]
def setupIntTybij [HolBase]
    (is_int : thm)
    (int_tybij : thm)
    (MESON_TAC : List thm → tactic) :
    ExceptT String IO IntTybij := do
  let (int_abstr, int_rep) :=
    (← SPEC_ALL (← CONJUNCT1 int_tybij), ← SPEC_ALL (← CONJUNCT2 int_tybij))

  let dest_int_rep ← prove
   r"!i. ?n. (real_of_int i = &n) \/ (real_of_int i = --(&n))"
   (REWRITE_TAC [← GSYM is_int, int_rep, int_abstr])

  let INTEGER_REAL_OF_INT ← prove
   r"!x. integer(real_of_int x)"
   (MESON_TAC [int_tybij])

  /- We want the following too. -/

  let int_eq ← prove
   r"!x y. (x = y) <=> (real_of_int x = real_of_int y)"
   (REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    POP_ASSUM (MP_TAC o AP_TERM (← q r"int_of_real")) THEN
    REWRITE_TAC [int_abstr])

  return { int_tybij, int_abstr, int_rep, dest_int_rep,
           INTEGER_REAL_OF_INT, int_eq }

/- ---------------------------------------------------------------------- -/
/- Set up interface map.                                                  -/
/- ---------------------------------------------------------------------- -/

/-- int.ml 61-70: `do_list overload_interface [...]` and `prioritize_int()`.
    Global parser state; Session runs it once, before the definitions below. -/
def setupIntInterface
    (overload_interface : String → term → IO (Except String Unit))
    (prioritize_overload : hol_type → IO Unit) :
    ExceptT String IO Unit := do
  for (s, c) in
      [("+", "int_add:int->int->int"), ("-", "int_sub:int->int->int"),
       ("*", "int_mul:int->int->int"), ("<", "int_lt:int->int->bool"),
       ("<=", "int_le:int->int->bool"), (">", "int_gt:int->int->bool"),
       (">=", "int_ge:int->int->bool"), ("--", "int_neg:int->int"),
       ("pow", "int_pow:int->num->int"), ("abs", "int_abs:int->int"),
       ("max", "int_max:int->int->int"), ("min", "int_min:int->int->int"),
       ("&", "int_of_num:num->int")] do
    ExceptT.mk (overload_interface s (← q c))
  -- `let prioritize_int() = prioritize_overload(mk_type("int",[]))`
  liftM (prioritize_overload (← (mk_type "int" [] : ExceptT String IO hol_type)))

/- ---------------------------------------------------------------------- -/
/- Definitions and closure derivations of all operations but "inv" and "/".-/
/- ---------------------------------------------------------------------- -/

/-- int.ml 76-257: the operations, their `_th` theorems, REAL_OF_INT_CLAUSES
    and a few theorems about the type.  The comparisons have no `_th`. -/
structure IntOps where
  /-- `int_le` (int.ml 76): `x <= y <=> real_of_int x <= real_of_int y`. -/
  int_le : thm
  /-- `int_lt` (int.ml 79): `x < y <=> real_of_int x < real_of_int y`. -/
  int_lt : thm
  /-- `int_ge` (int.ml 82): `x >= y <=> real_of_int x >= real_of_int y`. -/
  int_ge : thm
  /-- `int_gt` (int.ml 85): `x > y <=> real_of_int x > real_of_int y`. -/
  int_gt : thm
  /-- `int_of_num` (int.ml 88): `&n = int_of_real(real_of_num n)`. -/
  int_of_num : thm
  /-- `int_of_num_th` (int.ml 91):
      `!n. real_of_int(int_of_num n) = real_of_num n`. -/
  int_of_num_th : thm
  /-- `int_neg` (int.ml 96): `--i = int_of_real(--(real_of_int i))`. -/
  int_neg : thm
  /-- `int_neg_th` (int.ml 99):
      `!x. real_of_int(int_neg x) = --(real_of_int x)`. -/
  int_neg_th : thm
  /-- `int_add` (int.ml 106):
      `x + y = int_of_real(real_of_int x + real_of_int y)`. -/
  int_add : thm
  /-- `int_add_th` (int.ml 109):
      `!x y. real_of_int(x + y) = real_of_int x + real_of_int y`. -/
  int_add_th : thm
  /-- `int_sub` (int.ml 123):
      `x - y = int_of_real(real_of_int x - real_of_int y)`. -/
  int_sub : thm
  /-- `int_sub_th` (int.ml 126):
      `!x y. real_of_int(x - y) = real_of_int x - real_of_int y`. -/
  int_sub_th : thm
  /-- `int_mul` (int.ml 131):
      `x * y = int_of_real(real_of_int x * real_of_int y)`. -/
  int_mul : thm
  /-- `int_mul_th` (int.ml 134):
      `!x y. real_of_int(x * y) = real_of_int x * real_of_int y`. -/
  int_mul_th : thm
  /-- `int_abs` (int.ml 143): `abs x = int_of_real(abs(real_of_int x))`. -/
  int_abs : thm
  /-- `int_abs_th` (int.ml 146):
      `!x. real_of_int(abs x) = abs(real_of_int x)`. -/
  int_abs_th : thm
  /-- `int_sgn` (int.ml 151):
      `int_sgn x = int_of_real(real_sgn(real_of_int x))`. -/
  int_sgn : thm
  /-- `int_sgn_th` (int.ml 154):
      `!x. real_of_int(int_sgn x) = real_sgn(real_of_int x)`. -/
  int_sgn_th : thm
  /-- `int_max` (int.ml 160):
      `int_max x y = int_of_real(max (real_of_int x) (real_of_int y))`. -/
  int_max : thm
  /-- `int_max_th` (int.ml 163):
      `!x y. real_of_int(max x y) = max (real_of_int x) (real_of_int y)`. -/
  int_max_th : thm
  /-- `int_min` (int.ml 168):
      `int_min x y = int_of_real(min (real_of_int x) (real_of_int y))`. -/
  int_min : thm
  /-- `int_min_th` (int.ml 171):
      `!x y. real_of_int(min x y) = min (real_of_int x) (real_of_int y)`. -/
  int_min_th : thm
  /-- `int_pow` (int.ml 176): `x pow n = int_of_real((real_of_int x) pow n)`. -/
  int_pow : thm
  /-- `int_pow_th` (int.ml 179):
      `!x n. real_of_int(x pow n) = (real_of_int x) pow n`. -/
  int_pow_th : thm
  /-- `REAL_OF_INT_CLAUSES` (int.ml 191): the seventeen-clause conjunction
      collecting every bridge into one rewrite. -/
  REAL_OF_INT_CLAUSES : thm
  /-- `INT_IMAGE` (int.ml 217):
      `!x. (?n. x = &n) \/ (?n. x = --(&n))`. -/
  INT_IMAGE : thm
  /-- `FORALL_INT_CASES` (int.ml 227):
      `!P. (!x. P x) <=> (!n. P(&n)) /\ (!n. P(-- &n))`. -/
  FORALL_INT_CASES : thm
  /-- `EXISTS_INT_CASES` (int.ml 231):
      `!P. (?x. P x) <=> (?n. P(&n)) \/ (?n. P(-- &n))`. -/
  EXISTS_INT_CASES : thm
  /-- `INT_LT_DISCRETE` (int.ml 235): `!x y. x < y <=> (x + &1) <= y`. -/
  INT_LT_DISCRETE : thm
  /-- `INT_GT_DISCRETE` (int.ml 254): `!x y. x > y <=> x >= (y + &1)`. -/
  INT_GT_DISCRETE : thm
  deriving Inhabited

/-- int.ml 76-257.  The definitions create constants, so Session runs this
    once, after `setupIntInterface`.  `REAL_ARITH` is Session's `REAL_ARITH3`. -/
@[nospecialize]
def setupIntOps [HolBase] (N : HolMath.Nums.NumsThms)
    (R : HolMath.RealAx.RealThms)
    (CiT : HolMath.CalcInt.CalcIntThms)
    (RT1 : HolMath.Real.RealThms1)
    (RT2 : HolMath.Real.RealThms2)
    (RT3 : HolMath.Real.RealThms3)
    (RT10 : HolMath.Real.RealThms10)
    (A1 : HolMath.Arith.ArithThms1)
    (A2 : HolMath.Arith.ArithThms2)
    (A3 : HolMath.Arith.ArithThms3)
    (A4 : HolMath.Arith.ArithThms4)
    (AR : HolMath.CalcNum.ArithRewrites)
    (int_rep int_abstr is_int dest_int_rep int_eq : thm)
    (MESON_TAC : List thm → tactic)
    (REWRITE_CONV' : List thm → term → IO (Except String thm))
    (REAL_ARITH : term → IO (Except String thm))
    (new_definition' : term → IO (Except String thm)) :
    ExceptT String IO IntOps := do
  let new_definition (s : String) : ExceptT String IO thm := do
    ExceptT.mk (new_definition' (← q s))
  let REWRITE_CONV (ths : List thm) (t : term) : ExceptT String IO thm :=
    ExceptT.mk (REWRITE_CONV' ths t)
  let INDUCT_TAC := HolMath.Nums.INDUCT_TAC N.num_INDUCTION
  let REAL_ARITH_TAC : tactic := HolMath.Real.REAL_ARITH_TAC REAL_ARITH
  let { EXISTS_OR_THM, EXISTS_REFL, OR_EXISTS_THM, .. } := HolBase.T
  let { REAL_OF_NUM_EQ, REAL_OF_NUM_LE, REAL_OF_NUM_ADD, REAL_OF_NUM_MUL,
        REAL_ADD_SYM, REAL_ADD_ASSOC, real_sub, real_abs, real_max, real_min,
        real_pow, real_ge, real_gt, .. } := R
  let { REAL_NEG_NEG, REAL_MUL_LNEG, REAL_MUL_RNEG, REAL_NEG_ADD, REAL_LE_NEG2,
        REAL_LE_LNEG, REAL_LE_RNEG, .. } := CiT
  let { REAL_OF_NUM_LT, .. } := RT1
  let { REAL_LT_LNEG, REAL_LT_RNEG, .. } := RT2
  let { REAL_LE_SUB_RADD, REAL_EQ_NEG2, REAL_LT_NEG2, .. } := RT3
  let { real_sgn, .. } := RT10
  let { ADD_CLAUSES, ADD_SYM, ADD1, .. } := A1
  let { LE_SUC_LT, LT_SUC_LE, .. } := A2
  let { LE_CASES, .. } := A3
  let { LE_EXISTS, .. } := A4
  let { ARITH_SUC, .. } := AR

  let int_le ← new_definition
    r"x <= y <=> (real_of_int x) <= (real_of_int y)"

  let int_lt ← new_definition
    r"x < y <=> (real_of_int x) < (real_of_int y)"

  let int_ge ← new_definition
    r"x >= y <=> (real_of_int x) >= (real_of_int y)"

  let int_gt ← new_definition
    r"x > y <=> (real_of_int x) > (real_of_int y)"

  let int_of_num ← new_definition
    r"&n = int_of_real(real_of_num n)"

  let int_of_num_th ← prove
   r"!n. real_of_int(int_of_num n) = real_of_num n"
   (REWRITE_TAC [int_of_num, ← GSYM int_rep, is_int] THEN
    REWRITE_TAC [REAL_OF_NUM_EQ, EXISTS_OR_THM, ← GSYM EXISTS_REFL])

  let int_neg ← new_definition
    r"--i = int_of_real(--(real_of_int i))"

  let int_neg_th ← prove
   r"!x. real_of_int(int_neg x) = --(real_of_int x)"
   (REWRITE_TAC [int_neg, ← GSYM int_rep, is_int] THEN
    GEN_TAC THEN STRIP_ASSUME_TAC (← SPEC (← q r"x:int") dest_int_rep) THEN
    ASM_REWRITE_TAC [REAL_NEG_NEG, EXISTS_OR_THM, REAL_EQ_NEG2,
      REAL_OF_NUM_EQ, ← GSYM EXISTS_REFL])

  let int_add ← new_definition
    r"x + y = int_of_real((real_of_int x) + (real_of_int y))"

  let int_add_th ← prove
   r"!x y. real_of_int(x + y) = (real_of_int x) + (real_of_int y)"
   (REWRITE_TAC [int_add, ← GSYM int_rep, is_int] THEN REPEAT GEN_TAC THEN
    X_CHOOSE_THEN (← q r"m:num") DISJ_CASES_TAC (← SPEC (← q r"x:int") dest_int_rep) THEN
    X_CHOOSE_THEN (← q r"n:num") DISJ_CASES_TAC (← SPEC (← q r"y:int") dest_int_rep) THEN
    ASM_REWRITE_TAC [REAL_OF_NUM_ADD, REAL_OF_NUM_EQ, EXISTS_OR_THM] THEN
    REWRITE_TAC [← GSYM EXISTS_REFL] THEN
    DISJ_CASES_THEN MP_TAC (← SPECL [← q r"m:num", ← q r"n:num"] LE_CASES) THEN
    REWRITE_TAC [LE_EXISTS] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"d:num") SUBST1_TAC) THEN
    REWRITE_TAC [← GSYM REAL_OF_NUM_ADD, OR_EXISTS_THM, REAL_NEG_ADD] THEN
    TRY (EXISTS_TAC (← q r"d:num") THEN REAL_ARITH_TAC) THEN
    REWRITE_TAC [EXISTS_OR_THM, ← GSYM REAL_NEG_ADD, REAL_EQ_NEG2,
      REAL_OF_NUM_ADD, REAL_OF_NUM_EQ, ← GSYM EXISTS_REFL])

  let int_sub ← new_definition
    r"x - y = int_of_real(real_of_int x - real_of_int y)"

  let int_sub_th ← prove
   r"!x y. real_of_int(x - y) = (real_of_int x) - (real_of_int y)"
   (REWRITE_TAC [int_sub, real_sub, ← GSYM int_neg_th, ← GSYM int_add_th] THEN
    REWRITE_TAC [int_abstr])

  let int_mul ← new_definition
    r"x * y = int_of_real ((real_of_int x) * (real_of_int y))"

  let int_mul_th ← prove
   r"!x y. real_of_int(x * y) = (real_of_int x) * (real_of_int y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [int_mul, ← GSYM int_rep, is_int] THEN
    X_CHOOSE_THEN (← q r"m:num") DISJ_CASES_TAC (← SPEC (← q r"x:int") dest_int_rep) THEN
    X_CHOOSE_THEN (← q r"n:num") DISJ_CASES_TAC (← SPEC (← q r"y:int") dest_int_rep) THEN
    ASM_REWRITE_TAC [REAL_OF_NUM_ADD, REAL_OF_NUM_EQ, EXISTS_OR_THM] THEN
    REWRITE_TAC [REAL_MUL_LNEG, REAL_MUL_RNEG, REAL_NEG_NEG, REAL_OF_NUM_MUL] THEN
    REWRITE_TAC [REAL_EQ_NEG2, REAL_OF_NUM_EQ, ← GSYM EXISTS_REFL])

  let int_abs ← new_definition
    r"abs x = int_of_real(abs(real_of_int x))"

  let int_abs_th ← prove
   r"!x. real_of_int(abs x) = abs(real_of_int x)"
   (GEN_TAC THEN REWRITE_TAC [int_abs, real_abs] THEN COND_CASES_TAC THEN
    REWRITE_TAC [← GSYM int_neg, int_neg_th, int_abstr])

  let int_sgn ← new_definition
    r"int_sgn x = int_of_real(real_sgn(real_of_int x))"

  let int_sgn_th ← prove
   r"!x. real_of_int(int_sgn x) = real_sgn(real_of_int x)"
   (GEN_TAC THEN REWRITE_TAC [int_sgn, real_sgn, ← GSYM int_rep] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    MESON_TAC [is_int])

  let int_max ← new_definition
    r"int_max x y = int_of_real(max (real_of_int x) (real_of_int y))"

  let int_max_th ← prove
   r"!x y. real_of_int(max x y) = max (real_of_int x) (real_of_int y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [int_max, real_max] THEN
    COND_CASES_TAC THEN REWRITE_TAC [int_abstr])

  let int_min ← new_definition
    r"int_min x y = int_of_real(min (real_of_int x) (real_of_int y))"

  let int_min_th ← prove
   r"!x y. real_of_int(min x y) = min (real_of_int x) (real_of_int y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [int_min, real_min] THEN
    COND_CASES_TAC THEN REWRITE_TAC [int_abstr])

  let int_pow ← new_definition
    r"x pow n = int_of_real((real_of_int x) pow n)"

  let int_pow_th ← prove
   r"!x n. real_of_int(x pow n) = (real_of_int x) pow n"
   (GEN_TAC THEN REWRITE_TAC [int_pow] THEN INDUCT_TAC THEN
    REWRITE_TAC [real_pow] THENL
     [REWRITE_TAC [← GSYM int_of_num, int_of_num_th],
      POP_ASSUM (SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC [← GSYM int_mul, int_mul_th]])

  /- ---------------------------------------------------------------------- -/
  /- All collected into a single rewrite                                    -/
  /- ---------------------------------------------------------------------- -/

  let REAL_OF_INT_CLAUSES ← prove
   r"(!x y. real_of_int x = real_of_int y <=> x = y) /\
   (!x y. real_of_int x >= real_of_int y <=> x >= y) /\
   (!x y. real_of_int x > real_of_int y <=> x > y) /\
   (!x y. real_of_int x <= real_of_int y <=> x <= y) /\
   (!x y. real_of_int x < real_of_int y <=> x < y) /\
   (!x y. max (real_of_int x) (real_of_int y) = real_of_int(max x y)) /\
   (!x y. min (real_of_int x) (real_of_int y) = real_of_int(min x y)) /\
   (!n. &n = real_of_int(&n)) /\
   (!x. --real_of_int x = real_of_int(--x)) /\
   (!x. abs(real_of_int x) = real_of_int(abs x)) /\
   (!x y. max (real_of_int x) (real_of_int y) = real_of_int(max x y)) /\
   (!x y. min (real_of_int x) (real_of_int y) = real_of_int(min x y)) /\
   (!x. real_sgn (real_of_int x) = real_of_int(int_sgn x)) /\
   (!x y. real_of_int x + real_of_int y = real_of_int(x + y)) /\
   (!x y. real_of_int x - real_of_int y = real_of_int(x - y)) /\
   (!x y. real_of_int x * real_of_int y = real_of_int(x * y)) /\
   (!x n. real_of_int x pow n = real_of_int(x pow n))"
   (REWRITE_TAC [int_eq, int_ge, int_gt, int_le, int_lt, int_max_th, int_min_th,
                 int_of_num_th, int_neg_th, int_abs_th, int_max_th, int_min_th,
                 int_sgn_th, int_add_th, int_sub_th, int_mul_th, int_pow_th])

  /- ---------------------------------------------------------------------- -/
  /- A few convenient theorems about the integer type.                      -/
  /- ---------------------------------------------------------------------- -/

  let INT_IMAGE ← prove
   r"!x. (?n. x = &n) \/ (?n. x = --(&n))"
   (GEN_TAC THEN
    X_CHOOSE_THEN (← q r"n:num") DISJ_CASES_TAC (← SPEC (← q r"x:int") dest_int_rep) THEN
    POP_ASSUM (MP_TAC o AP_TERM (← q r"int_of_real")) THEN REWRITE_TAC [int_abstr] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [int_of_num, int_neg] THENL
     [DISJ1_TAC, DISJ2_TAC] THEN
    EXISTS_TAC (← q r"n:num") THEN REWRITE_TAC [int_abstr] THEN
    REWRITE_TAC [← GSYM int_of_num, int_of_num_th])

  let FORALL_INT_CASES ← prove
   r"!P:int->bool. (!x. P x) <=> (!n. P(&n)) /\ (!n. P(-- &n))"
   (MESON_TAC [INT_IMAGE])

  let EXISTS_INT_CASES ← prove
   r"!P:int->bool. (?x. P x) <=> (?n. P(&n)) \/ (?n. P(-- &n))"
   (MESON_TAC [INT_IMAGE])

  let INT_LT_DISCRETE ← prove
   r"!x y. x < y <=> (x + &1) <= y"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [int_le, int_lt, int_add_th] THEN
    DISJ_CASES_THEN (X_CHOOSE_THEN (← q r"m:num") SUBST1_TAC)
     (← SPEC (← q r"x:int") INT_IMAGE) THEN
    DISJ_CASES_THEN (X_CHOOSE_THEN (← q r"n:num") SUBST1_TAC)
     (← SPEC (← q r"y:int") INT_IMAGE) THEN
    REWRITE_TAC [int_neg_th, int_of_num_th] THEN
    REWRITE_TAC [REAL_LE_NEG2, REAL_LT_NEG2] THEN
    REWRITE_TAC [REAL_LE_LNEG, REAL_LT_LNEG, REAL_LE_RNEG, REAL_LT_RNEG] THEN
    REWRITE_TAC [← GSYM REAL_ADD_ASSOC] THEN
    ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
    REWRITE_TAC [← GSYM real_sub, REAL_LE_SUB_RADD] THEN
    REWRITE_TAC [REAL_OF_NUM_LE, REAL_OF_NUM_LT, REAL_OF_NUM_ADD] THEN
    REWRITE_TAC [← GSYM ADD1, ← ONCE_REWRITE_RULE [ADD_SYM] (← GSYM ADD1)] THEN
    REWRITE_TAC [← SYM (← REWRITE_CONV [ARITH_SUC] (← q r"SUC 0"))] THEN
    REWRITE_TAC [ADD_CLAUSES, LE_SUC_LT, LT_SUC_LE])

  let INT_GT_DISCRETE ← prove
   r"!x y. x > y <=> x >= (y + &1)"
   (REWRITE_TAC [int_gt, int_ge, real_ge, real_gt, ← GSYM int_le, ← GSYM int_lt] THEN
    MATCH_ACCEPT_TAC INT_LT_DISCRETE)

  return { int_le, int_lt, int_ge, int_gt, int_of_num, int_of_num_th,
           int_neg, int_neg_th, int_add, int_add_th, int_sub, int_sub_th,
           int_mul, int_mul_th, int_abs, int_abs_th, int_sgn, int_sgn_th,
           int_max, int_max_th, int_min, int_min_th, int_pow, int_pow_th,
           REAL_OF_INT_CLAUSES, INT_IMAGE, FORALL_INT_CASES, EXISTS_INT_CASES,
           INT_LT_DISCRETE, INT_GT_DISCRETE }


/- ---------------------------------------------------------------------- -/
/- Conversions of integer constants to and from OCaml numbers.            -/
/- ---------------------------------------------------------------------- -/

/-- `is_intconst` (int.ml 262).  `--(&0)` is not an integer constant. -/
def is_intconst (tm : term) : Bool :=
  match tm with
  | .Comb (.Const "int_of_num" _) n => HolMath.Nums.is_numeral n
  | .Comb (.Const "int_neg" _) (.Comb (.Const "int_of_num" _) n) =>
      HolMath.Nums.is_numeral n && (match dest_numeral n with
                       | .ok v => !(v == num_0)
                       | .error _ => false)
  | _ => false

/-- `dest_intconst` (int.ml 269). -/
def dest_intconst (tm : term) : Except String Rat :=
  match tm with
  | .Comb (.Const "int_of_num" _) n => dest_numeral n
  | .Comb (.Const "int_neg" _) (.Comb (.Const "int_of_num" _) n) => do
      let nn ← dest_numeral n
      if nn != num_0 then pure (-(← dest_numeral n))
      else .error "dest_intconst"
  | _ => .error "dest_intconst"

/-- The terms `mk_intconst` closes over (int.ml 279-280:
    `let cast_tm = `int_of_num` and neg_tm = `int_neg` in ...`), parsed once
    by `setupIntConstSyntax`. -/
structure IntConstSyntax where
  cast_tm : term
  neg_tm : term
  mk_numeral : Rat → Except String term
  deriving Inhabited

def setupIntConstSyntax (mk_numeral : Rat → Except String term) :
    ExceptT String IO IntConstSyntax := do
  let cast_tm ← q r"int_of_num"
  let neg_tm ← q r"int_neg"
  return { cast_tm, neg_tm, mk_numeral }

/-- `mk_numconst` (int.ml 281). -/
private def mk_intnumconst (I : IntConstSyntax) (n : Rat) :
    Except String term := do
  mk_comb I.cast_tm (← I.mk_numeral n)

/-- `mk_intconst` (int.ml 279). -/
def mk_intconst (I : IntConstSyntax) (x : Rat) : Except String term :=
  if x < num_0 then do mk_comb I.neg_tm (← mk_intnumconst I (-x))
  else mk_intnumconst I x

/- ---------------------------------------------------------------------- -/
/- A simple procedure to lift most universal real theorems to integers.   -/
/- For a more complete procedure, give required term to INT_ARITH (below).-/
/- ---------------------------------------------------------------------- -/

/-- `let rec INT_OF_REAL_THM th = if is_conj(concl th) then CONJ ... else
    INT_OF_REAL_THM1 th` (int.ml 316). -/
private partial def intOfRealThmRec [HolBase]
    (INT_OF_REAL_THM1 : thm → ExceptT String IO thm) (th : thm) :
    ExceptT String IO thm :=
  if is_conj (concl th) then do
    CONJ (← intOfRealThmRec INT_OF_REAL_THM1 (← CONJUNCT1 th))
         (← intOfRealThmRec INT_OF_REAL_THM1 (← CONJUNCT2 th))
  else INT_OF_REAL_THM1 th

/-- `INT_OF_REAL_THM` (int.ml 290).  The rewrite list is in the OCaml's order
    (`int_sgn_th` before `int_sub_th`), which the DEPTH_CONV result depends
    on. -/
@[nospecialize]
def setupIntOfRealThm [HolBase] (int_eq : thm) (O : IntOps) :
    ExceptT String IO (thm → IO (Except String thm)) := do
  let { int_le, int_lt, int_ge, int_gt, int_of_num_th, int_neg_th, int_add_th,
        int_mul_th, int_sgn_th, int_sub_th, int_abs_th, int_max_th, int_min_th,
        int_pow_th, .. } := O
  let dest ← q r"real_of_int"
  let real_ty ← qty r"real"
  let int_ty ← qty r"int"
  let cond_th ← prove
   r"real_of_int(if b then x else y) =
       if b then real_of_int x else real_of_int y"
   (COND_CASES_TAC THEN REWRITE_TAC [])
  let thlist ← [int_eq, int_le, int_lt, int_ge, int_gt,
    int_of_num_th, int_neg_th, int_add_th, int_mul_th, int_sgn_th,
    int_sub_th, int_abs_th, int_max_th, int_min_th, int_pow_th, cond_th].mapM GSYM
  let REW_RULE := GEN_REWRITE_RULE DEPTH_CONV thlist
  let int_tm_of_real_var (v : term) : ExceptT String IO term := do
    let (s, ty) ← liftExcept (dest_var v)
    if ty == real_ty then liftExcept (mk_comb dest (mk_var s int_ty)) else pure v
  let int_of_real_var (v : term) : ExceptT String IO term := do
    let (s, ty) ← liftExcept (dest_var v)
    if ty == real_ty then pure (mk_var s int_ty) else pure v
  let INT_OF_REAL_THM1 (th : thm) : ExceptT String IO thm := do
    let newavs := subtract (frees (concl th)) (freesl (hyp th))
    let (avs, _bod) := strip_forall (concl th)
    let allavs := newavs ++ avs
    let avs' ← allavs.mapM int_tm_of_real_var
    let avs'' ← avs.mapM int_of_real_var
    GENL avs'' (← REW_RULE (← SPECL avs' (← GENL newavs th)))
  pure (fun th => (intOfRealThmRec INT_OF_REAL_THM1 th).run)

/- ---------------------------------------------------------------------- -/
/- Collect together all the theorems derived automatically.               -/
/- (int.ml 325-601; split into ten bundles of at most 28.)                -/
/- ---------------------------------------------------------------------- -/

/-- int.ml 326-353. -/
structure IntThms1 where
  INT_ABS_0 : thm
  INT_ABS_1 : thm
  INT_ABS_ABS : thm
  INT_ABS_BETWEEN : thm
  INT_ABS_BETWEEN1 : thm
  INT_ABS_BETWEEN2 : thm
  INT_ABS_BOUND : thm
  INT_ABS_BOUNDS : thm
  INT_ABS_CASES : thm
  INT_ABS_CIRCLE : thm
  INT_ABS_LE : thm
  INT_ABS_MUL : thm
  INT_ABS_NEG : thm
  INT_ABS_NUM : thm
  INT_ABS_NZ : thm
  INT_ABS_POS : thm
  INT_ABS_POW : thm
  INT_ABS_REFL : thm
  INT_ABS_SGN : thm
  INT_ABS_SIGN : thm
  INT_ABS_SIGN2 : thm
  INT_ABS_STILLNZ : thm
  INT_ABS_SUB : thm
  INT_ABS_SUB_ABS : thm
  INT_ABS_TRIANGLE : thm
  INT_ABS_ZERO : thm
  INT_ADD2_SUB2 : thm
  INT_ADD_AC : thm
  deriving Inhabited

def setupIntThms1 (INT_OF_REAL_THM' : thm → IO (Except String thm))
    (REAL_ABS_0 REAL_ABS_1 REAL_ABS_ABS REAL_ABS_BETWEEN REAL_ABS_BETWEEN1
     REAL_ABS_BETWEEN2 REAL_ABS_BOUND REAL_ABS_BOUNDS REAL_ABS_CASES
     REAL_ABS_CIRCLE REAL_ABS_LE REAL_ABS_MUL REAL_ABS_NEG REAL_ABS_NUM
     REAL_ABS_NZ REAL_ABS_POS REAL_ABS_POW REAL_ABS_REFL REAL_ABS_SGN
     REAL_ABS_SIGN REAL_ABS_SIGN2 REAL_ABS_STILLNZ REAL_ABS_SUB
     REAL_ABS_SUB_ABS REAL_ABS_TRIANGLE REAL_ABS_ZERO REAL_ADD2_SUB2
     REAL_ADD_AC : thm) :
    ExceptT String IO IntThms1 := do
  let INT_OF_REAL_THM th := ExceptT.mk (INT_OF_REAL_THM' th)
  let INT_ABS_0 ← INT_OF_REAL_THM REAL_ABS_0
  let INT_ABS_1 ← INT_OF_REAL_THM REAL_ABS_1
  let INT_ABS_ABS ← INT_OF_REAL_THM REAL_ABS_ABS
  let INT_ABS_BETWEEN ← INT_OF_REAL_THM REAL_ABS_BETWEEN
  let INT_ABS_BETWEEN1 ← INT_OF_REAL_THM REAL_ABS_BETWEEN1
  let INT_ABS_BETWEEN2 ← INT_OF_REAL_THM REAL_ABS_BETWEEN2
  let INT_ABS_BOUND ← INT_OF_REAL_THM REAL_ABS_BOUND
  let INT_ABS_BOUNDS ← INT_OF_REAL_THM REAL_ABS_BOUNDS
  let INT_ABS_CASES ← INT_OF_REAL_THM REAL_ABS_CASES
  let INT_ABS_CIRCLE ← INT_OF_REAL_THM REAL_ABS_CIRCLE
  let INT_ABS_LE ← INT_OF_REAL_THM REAL_ABS_LE
  let INT_ABS_MUL ← INT_OF_REAL_THM REAL_ABS_MUL
  let INT_ABS_NEG ← INT_OF_REAL_THM REAL_ABS_NEG
  let INT_ABS_NUM ← INT_OF_REAL_THM REAL_ABS_NUM
  let INT_ABS_NZ ← INT_OF_REAL_THM REAL_ABS_NZ
  let INT_ABS_POS ← INT_OF_REAL_THM REAL_ABS_POS
  let INT_ABS_POW ← INT_OF_REAL_THM REAL_ABS_POW
  let INT_ABS_REFL ← INT_OF_REAL_THM REAL_ABS_REFL
  let INT_ABS_SGN ← INT_OF_REAL_THM REAL_ABS_SGN
  let INT_ABS_SIGN ← INT_OF_REAL_THM REAL_ABS_SIGN
  let INT_ABS_SIGN2 ← INT_OF_REAL_THM REAL_ABS_SIGN2
  let INT_ABS_STILLNZ ← INT_OF_REAL_THM REAL_ABS_STILLNZ
  let INT_ABS_SUB ← INT_OF_REAL_THM REAL_ABS_SUB
  let INT_ABS_SUB_ABS ← INT_OF_REAL_THM REAL_ABS_SUB_ABS
  let INT_ABS_TRIANGLE ← INT_OF_REAL_THM REAL_ABS_TRIANGLE
  let INT_ABS_ZERO ← INT_OF_REAL_THM REAL_ABS_ZERO
  let INT_ADD2_SUB2 ← INT_OF_REAL_THM REAL_ADD2_SUB2
  let INT_ADD_AC ← INT_OF_REAL_THM REAL_ADD_AC
  return { INT_ABS_0, INT_ABS_1, INT_ABS_ABS, INT_ABS_BETWEEN, INT_ABS_BETWEEN1,
           INT_ABS_BETWEEN2, INT_ABS_BOUND, INT_ABS_BOUNDS, INT_ABS_CASES,
           INT_ABS_CIRCLE, INT_ABS_LE, INT_ABS_MUL, INT_ABS_NEG, INT_ABS_NUM,
           INT_ABS_NZ, INT_ABS_POS, INT_ABS_POW, INT_ABS_REFL, INT_ABS_SGN,
           INT_ABS_SIGN, INT_ABS_SIGN2, INT_ABS_STILLNZ, INT_ABS_SUB,
           INT_ABS_SUB_ABS, INT_ABS_TRIANGLE, INT_ABS_ZERO, INT_ADD2_SUB2,
           INT_ADD_AC }

/-- int.ml 354-381. -/
structure IntThms2 where
  INT_ADD_ASSOC : thm
  INT_ADD_LDISTRIB : thm
  INT_ADD_LID : thm
  INT_ADD_LINV : thm
  INT_ADD_RDISTRIB : thm
  INT_ADD_RID : thm
  INT_ADD_RINV : thm
  INT_ADD_SUB : thm
  INT_ADD_SUB2 : thm
  INT_ADD_SYM : thm
  INT_BOUNDS_LE : thm
  INT_BOUNDS_LT : thm
  INT_DIFFSQ : thm
  INT_ENTIRE : thm
  INT_EQ_ADD_LCANCEL : thm
  INT_EQ_ADD_LCANCEL_0 : thm
  INT_EQ_ADD_RCANCEL : thm
  INT_EQ_ADD_RCANCEL_0 : thm
  INT_EQ_IMP_LE : thm
  INT_EQ_LCANCEL_IMP : thm
  INT_EQ_MUL_LCANCEL : thm
  INT_EQ_MUL_RCANCEL : thm
  INT_EQ_NEG2 : thm
  INT_EQ_RCANCEL_IMP : thm
  INT_EQ_SGN_ABS : thm
  INT_EQ_SQUARE_ABS : thm
  INT_EQ_SUB_LADD : thm
  INT_EQ_SUB_RADD : thm
  deriving Inhabited

def setupIntThms2 (INT_OF_REAL_THM' : thm → IO (Except String thm))
    (REAL_ADD_ASSOC REAL_ADD_LDISTRIB REAL_ADD_LID REAL_ADD_LINV
     REAL_ADD_RDISTRIB REAL_ADD_RID REAL_ADD_RINV REAL_ADD_SUB REAL_ADD_SUB2
     REAL_ADD_SYM REAL_BOUNDS_LE REAL_BOUNDS_LT REAL_DIFFSQ REAL_ENTIRE
     REAL_EQ_ADD_LCANCEL REAL_EQ_ADD_LCANCEL_0 REAL_EQ_ADD_RCANCEL
     REAL_EQ_ADD_RCANCEL_0 REAL_EQ_IMP_LE REAL_EQ_LCANCEL_IMP
     REAL_EQ_MUL_LCANCEL REAL_EQ_MUL_RCANCEL REAL_EQ_NEG2 REAL_EQ_RCANCEL_IMP
     REAL_EQ_SGN_ABS REAL_EQ_SQUARE_ABS REAL_EQ_SUB_LADD REAL_EQ_SUB_RADD : thm) :
    ExceptT String IO IntThms2 := do
  let INT_OF_REAL_THM th := ExceptT.mk (INT_OF_REAL_THM' th)
  let INT_ADD_ASSOC ← INT_OF_REAL_THM REAL_ADD_ASSOC
  let INT_ADD_LDISTRIB ← INT_OF_REAL_THM REAL_ADD_LDISTRIB
  let INT_ADD_LID ← INT_OF_REAL_THM REAL_ADD_LID
  let INT_ADD_LINV ← INT_OF_REAL_THM REAL_ADD_LINV
  let INT_ADD_RDISTRIB ← INT_OF_REAL_THM REAL_ADD_RDISTRIB
  let INT_ADD_RID ← INT_OF_REAL_THM REAL_ADD_RID
  let INT_ADD_RINV ← INT_OF_REAL_THM REAL_ADD_RINV
  let INT_ADD_SUB ← INT_OF_REAL_THM REAL_ADD_SUB
  let INT_ADD_SUB2 ← INT_OF_REAL_THM REAL_ADD_SUB2
  let INT_ADD_SYM ← INT_OF_REAL_THM REAL_ADD_SYM
  let INT_BOUNDS_LE ← INT_OF_REAL_THM REAL_BOUNDS_LE
  let INT_BOUNDS_LT ← INT_OF_REAL_THM REAL_BOUNDS_LT
  let INT_DIFFSQ ← INT_OF_REAL_THM REAL_DIFFSQ
  let INT_ENTIRE ← INT_OF_REAL_THM REAL_ENTIRE
  let INT_EQ_ADD_LCANCEL ← INT_OF_REAL_THM REAL_EQ_ADD_LCANCEL
  let INT_EQ_ADD_LCANCEL_0 ← INT_OF_REAL_THM REAL_EQ_ADD_LCANCEL_0
  let INT_EQ_ADD_RCANCEL ← INT_OF_REAL_THM REAL_EQ_ADD_RCANCEL
  let INT_EQ_ADD_RCANCEL_0 ← INT_OF_REAL_THM REAL_EQ_ADD_RCANCEL_0
  let INT_EQ_IMP_LE ← INT_OF_REAL_THM REAL_EQ_IMP_LE
  let INT_EQ_LCANCEL_IMP ← INT_OF_REAL_THM REAL_EQ_LCANCEL_IMP
  let INT_EQ_MUL_LCANCEL ← INT_OF_REAL_THM REAL_EQ_MUL_LCANCEL
  let INT_EQ_MUL_RCANCEL ← INT_OF_REAL_THM REAL_EQ_MUL_RCANCEL
  let INT_EQ_NEG2 ← INT_OF_REAL_THM REAL_EQ_NEG2
  let INT_EQ_RCANCEL_IMP ← INT_OF_REAL_THM REAL_EQ_RCANCEL_IMP
  let INT_EQ_SGN_ABS ← INT_OF_REAL_THM REAL_EQ_SGN_ABS
  let INT_EQ_SQUARE_ABS ← INT_OF_REAL_THM REAL_EQ_SQUARE_ABS
  let INT_EQ_SUB_LADD ← INT_OF_REAL_THM REAL_EQ_SUB_LADD
  let INT_EQ_SUB_RADD ← INT_OF_REAL_THM REAL_EQ_SUB_RADD
  return { INT_ADD_ASSOC, INT_ADD_LDISTRIB, INT_ADD_LID, INT_ADD_LINV,
           INT_ADD_RDISTRIB, INT_ADD_RID, INT_ADD_RINV, INT_ADD_SUB, INT_ADD_SUB2,
           INT_ADD_SYM, INT_BOUNDS_LE, INT_BOUNDS_LT, INT_DIFFSQ, INT_ENTIRE,
           INT_EQ_ADD_LCANCEL, INT_EQ_ADD_LCANCEL_0, INT_EQ_ADD_RCANCEL,
           INT_EQ_ADD_RCANCEL_0, INT_EQ_IMP_LE, INT_EQ_LCANCEL_IMP,
           INT_EQ_MUL_LCANCEL, INT_EQ_MUL_RCANCEL, INT_EQ_NEG2, INT_EQ_RCANCEL_IMP,
           INT_EQ_SGN_ABS, INT_EQ_SQUARE_ABS, INT_EQ_SUB_LADD, INT_EQ_SUB_RADD }

/-- int.ml 382-409. -/
structure IntThms3 where
  INT_EVENPOW_ABS : thm
  INT_LET_ADD : thm
  INT_LET_ADD2 : thm
  INT_LET_ANTISYM : thm
  INT_LET_TOTAL : thm
  INT_LET_TRANS : thm
  INT_LE_01 : thm
  INT_LE_ADD : thm
  INT_LE_ADD2 : thm
  INT_LE_ADDL : thm
  INT_LE_ADDR : thm
  INT_LE_ANTISYM : thm
  INT_LE_DOUBLE : thm
  INT_LE_LADD : thm
  INT_LE_LADD_IMP : thm
  INT_LE_LCANCEL_IMP : thm
  INT_LE_LMUL : thm
  INT_LE_LMUL_EQ : thm
  INT_LE_LNEG : thm
  INT_LE_LT : thm
  INT_LE_MAX : thm
  INT_LE_MIN : thm
  INT_LE_MUL : thm
  INT_LE_MUL2 : thm
  INT_LE_MUL_EQ : thm
  INT_LE_NEG2 : thm
  INT_LE_NEGL : thm
  INT_LE_NEGR : thm
  deriving Inhabited

def setupIntThms3 (INT_OF_REAL_THM' : thm → IO (Except String thm))
    (REAL_EVENPOW_ABS REAL_LET_ADD REAL_LET_ADD2 REAL_LET_ANTISYM
     REAL_LET_TOTAL REAL_LET_TRANS REAL_LE_01 REAL_LE_ADD REAL_LE_ADD2
     REAL_LE_ADDL REAL_LE_ADDR REAL_LE_ANTISYM REAL_LE_DOUBLE REAL_LE_LADD
     REAL_LE_LADD_IMP REAL_LE_LCANCEL_IMP REAL_LE_LMUL REAL_LE_LMUL_EQ
     REAL_LE_LNEG REAL_LE_LT REAL_LE_MAX REAL_LE_MIN REAL_LE_MUL REAL_LE_MUL2
     REAL_LE_MUL_EQ REAL_LE_NEG2 REAL_LE_NEGL REAL_LE_NEGR : thm) :
    ExceptT String IO IntThms3 := do
  let INT_OF_REAL_THM th := ExceptT.mk (INT_OF_REAL_THM' th)
  let INT_EVENPOW_ABS ← INT_OF_REAL_THM REAL_EVENPOW_ABS
  let INT_LET_ADD ← INT_OF_REAL_THM REAL_LET_ADD
  let INT_LET_ADD2 ← INT_OF_REAL_THM REAL_LET_ADD2
  let INT_LET_ANTISYM ← INT_OF_REAL_THM REAL_LET_ANTISYM
  let INT_LET_TOTAL ← INT_OF_REAL_THM REAL_LET_TOTAL
  let INT_LET_TRANS ← INT_OF_REAL_THM REAL_LET_TRANS
  let INT_LE_01 ← INT_OF_REAL_THM REAL_LE_01
  let INT_LE_ADD ← INT_OF_REAL_THM REAL_LE_ADD
  let INT_LE_ADD2 ← INT_OF_REAL_THM REAL_LE_ADD2
  let INT_LE_ADDL ← INT_OF_REAL_THM REAL_LE_ADDL
  let INT_LE_ADDR ← INT_OF_REAL_THM REAL_LE_ADDR
  let INT_LE_ANTISYM ← INT_OF_REAL_THM REAL_LE_ANTISYM
  let INT_LE_DOUBLE ← INT_OF_REAL_THM REAL_LE_DOUBLE
  let INT_LE_LADD ← INT_OF_REAL_THM REAL_LE_LADD
  let INT_LE_LADD_IMP ← INT_OF_REAL_THM REAL_LE_LADD_IMP
  let INT_LE_LCANCEL_IMP ← INT_OF_REAL_THM REAL_LE_LCANCEL_IMP
  let INT_LE_LMUL ← INT_OF_REAL_THM REAL_LE_LMUL
  let INT_LE_LMUL_EQ ← INT_OF_REAL_THM REAL_LE_LMUL_EQ
  let INT_LE_LNEG ← INT_OF_REAL_THM REAL_LE_LNEG
  let INT_LE_LT ← INT_OF_REAL_THM REAL_LE_LT
  let INT_LE_MAX ← INT_OF_REAL_THM REAL_LE_MAX
  let INT_LE_MIN ← INT_OF_REAL_THM REAL_LE_MIN
  let INT_LE_MUL ← INT_OF_REAL_THM REAL_LE_MUL
  let INT_LE_MUL2 ← INT_OF_REAL_THM REAL_LE_MUL2
  let INT_LE_MUL_EQ ← INT_OF_REAL_THM REAL_LE_MUL_EQ
  let INT_LE_NEG2 ← INT_OF_REAL_THM REAL_LE_NEG2
  let INT_LE_NEGL ← INT_OF_REAL_THM REAL_LE_NEGL
  let INT_LE_NEGR ← INT_OF_REAL_THM REAL_LE_NEGR
  return { INT_EVENPOW_ABS, INT_LET_ADD, INT_LET_ADD2, INT_LET_ANTISYM,
           INT_LET_TOTAL, INT_LET_TRANS, INT_LE_01, INT_LE_ADD, INT_LE_ADD2,
           INT_LE_ADDL, INT_LE_ADDR, INT_LE_ANTISYM, INT_LE_DOUBLE, INT_LE_LADD,
           INT_LE_LADD_IMP, INT_LE_LCANCEL_IMP, INT_LE_LMUL, INT_LE_LMUL_EQ,
           INT_LE_LNEG, INT_LE_LT, INT_LE_MAX, INT_LE_MIN, INT_LE_MUL, INT_LE_MUL2,
           INT_LE_MUL_EQ, INT_LE_NEG2, INT_LE_NEGL, INT_LE_NEGR }

/-- int.ml 410-437. -/
structure IntThms4 where
  INT_LE_NEGTOTAL : thm
  INT_LE_POW2 : thm
  INT_LE_POW_2 : thm
  INT_LE_RADD : thm
  INT_LE_RCANCEL_IMP : thm
  INT_LE_REFL : thm
  INT_LE_RMUL : thm
  INT_LE_RMUL_EQ : thm
  INT_LE_RNEG : thm
  INT_LE_SQUARE : thm
  INT_LE_SQUARE_ABS : thm
  INT_LE_SUB_LADD : thm
  INT_LE_SUB_RADD : thm
  INT_LE_TOTAL : thm
  INT_LE_TRANS : thm
  INT_LNEG_UNIQ : thm
  INT_LTE_ADD : thm
  INT_LTE_ADD2 : thm
  INT_LTE_ANTISYM : thm
  INT_LTE_TOTAL : thm
  INT_LTE_TRANS : thm
  INT_LT_01 : thm
  INT_LT_ADD : thm
  INT_LT_ADD1 : thm
  INT_LT_ADD2 : thm
  INT_LT_ADDL : thm
  INT_LT_ADDNEG : thm
  INT_LT_ADDNEG2 : thm
  deriving Inhabited

def setupIntThms4 (INT_OF_REAL_THM' : thm → IO (Except String thm))
    (REAL_LE_NEGTOTAL REAL_LE_POW2 REAL_LE_POW_2 REAL_LE_RADD
     REAL_LE_RCANCEL_IMP REAL_LE_REFL REAL_LE_RMUL REAL_LE_RMUL_EQ REAL_LE_RNEG
     REAL_LE_SQUARE REAL_LE_SQUARE_ABS REAL_LE_SUB_LADD REAL_LE_SUB_RADD
     REAL_LE_TOTAL REAL_LE_TRANS REAL_LNEG_UNIQ REAL_LTE_ADD REAL_LTE_ADD2
     REAL_LTE_ANTISYM REAL_LTE_TOTAL REAL_LTE_TRANS REAL_LT_01 REAL_LT_ADD
     REAL_LT_ADD1 REAL_LT_ADD2 REAL_LT_ADDL REAL_LT_ADDNEG REAL_LT_ADDNEG2 : thm) :
    ExceptT String IO IntThms4 := do
  let INT_OF_REAL_THM th := ExceptT.mk (INT_OF_REAL_THM' th)
  let INT_LE_NEGTOTAL ← INT_OF_REAL_THM REAL_LE_NEGTOTAL
  let INT_LE_POW2 ← INT_OF_REAL_THM REAL_LE_POW2
  let INT_LE_POW_2 ← INT_OF_REAL_THM REAL_LE_POW_2
  let INT_LE_RADD ← INT_OF_REAL_THM REAL_LE_RADD
  let INT_LE_RCANCEL_IMP ← INT_OF_REAL_THM REAL_LE_RCANCEL_IMP
  let INT_LE_REFL ← INT_OF_REAL_THM REAL_LE_REFL
  let INT_LE_RMUL ← INT_OF_REAL_THM REAL_LE_RMUL
  let INT_LE_RMUL_EQ ← INT_OF_REAL_THM REAL_LE_RMUL_EQ
  let INT_LE_RNEG ← INT_OF_REAL_THM REAL_LE_RNEG
  let INT_LE_SQUARE ← INT_OF_REAL_THM REAL_LE_SQUARE
  let INT_LE_SQUARE_ABS ← INT_OF_REAL_THM REAL_LE_SQUARE_ABS
  let INT_LE_SUB_LADD ← INT_OF_REAL_THM REAL_LE_SUB_LADD
  let INT_LE_SUB_RADD ← INT_OF_REAL_THM REAL_LE_SUB_RADD
  let INT_LE_TOTAL ← INT_OF_REAL_THM REAL_LE_TOTAL
  let INT_LE_TRANS ← INT_OF_REAL_THM REAL_LE_TRANS
  let INT_LNEG_UNIQ ← INT_OF_REAL_THM REAL_LNEG_UNIQ
  let INT_LTE_ADD ← INT_OF_REAL_THM REAL_LTE_ADD
  let INT_LTE_ADD2 ← INT_OF_REAL_THM REAL_LTE_ADD2
  let INT_LTE_ANTISYM ← INT_OF_REAL_THM REAL_LTE_ANTISYM
  let INT_LTE_TOTAL ← INT_OF_REAL_THM REAL_LTE_TOTAL
  let INT_LTE_TRANS ← INT_OF_REAL_THM REAL_LTE_TRANS
  let INT_LT_01 ← INT_OF_REAL_THM REAL_LT_01
  let INT_LT_ADD ← INT_OF_REAL_THM REAL_LT_ADD
  let INT_LT_ADD1 ← INT_OF_REAL_THM REAL_LT_ADD1
  let INT_LT_ADD2 ← INT_OF_REAL_THM REAL_LT_ADD2
  let INT_LT_ADDL ← INT_OF_REAL_THM REAL_LT_ADDL
  let INT_LT_ADDNEG ← INT_OF_REAL_THM REAL_LT_ADDNEG
  let INT_LT_ADDNEG2 ← INT_OF_REAL_THM REAL_LT_ADDNEG2
  return { INT_LE_NEGTOTAL, INT_LE_POW2, INT_LE_POW_2, INT_LE_RADD,
           INT_LE_RCANCEL_IMP, INT_LE_REFL, INT_LE_RMUL, INT_LE_RMUL_EQ,
           INT_LE_RNEG, INT_LE_SQUARE, INT_LE_SQUARE_ABS, INT_LE_SUB_LADD,
           INT_LE_SUB_RADD, INT_LE_TOTAL, INT_LE_TRANS, INT_LNEG_UNIQ, INT_LTE_ADD,
           INT_LTE_ADD2, INT_LTE_ANTISYM, INT_LTE_TOTAL, INT_LTE_TRANS, INT_LT_01,
           INT_LT_ADD, INT_LT_ADD1, INT_LT_ADD2, INT_LT_ADDL, INT_LT_ADDNEG,
           INT_LT_ADDNEG2 }

/-- int.ml 438-465. -/
structure IntThms5 where
  INT_LT_ADDR : thm
  INT_LT_ADD_SUB : thm
  INT_LT_ANTISYM : thm
  INT_LT_GT : thm
  INT_LT_IMP_LE : thm
  INT_LT_IMP_NE : thm
  INT_LT_LADD : thm
  INT_LT_LADD_IMP : thm
  INT_LT_LCANCEL_IMP : thm
  INT_LT_LE : thm
  INT_LT_LMUL : thm
  INT_LT_LMUL_EQ : thm
  INT_LT_LNEG : thm
  INT_LT_MAX : thm
  INT_LT_MIN : thm
  INT_LT_MUL : thm
  INT_LT_MUL2 : thm
  INT_LT_MUL_EQ : thm
  INT_LT_NEG2 : thm
  INT_LT_NEGTOTAL : thm
  INT_LT_POW2 : thm
  INT_LT_POW_2 : thm
  INT_LT_RADD : thm
  INT_LT_RCANCEL_IMP : thm
  INT_LT_REFL : thm
  INT_LT_RMUL : thm
  INT_LT_RMUL_EQ : thm
  INT_LT_RNEG : thm
  deriving Inhabited

def setupIntThms5 (INT_OF_REAL_THM' : thm → IO (Except String thm))
    (REAL_LT_ADDR REAL_LT_ADD_SUB REAL_LT_ANTISYM REAL_LT_GT REAL_LT_IMP_LE
     REAL_LT_IMP_NE REAL_LT_LADD REAL_LT_LADD_IMP REAL_LT_LCANCEL_IMP
     REAL_LT_LE REAL_LT_LMUL REAL_LT_LMUL_EQ REAL_LT_LNEG REAL_LT_MAX
     REAL_LT_MIN REAL_LT_MUL REAL_LT_MUL2 REAL_LT_MUL_EQ REAL_LT_NEG2
     REAL_LT_NEGTOTAL REAL_LT_POW2 REAL_LT_POW_2 REAL_LT_RADD
     REAL_LT_RCANCEL_IMP REAL_LT_REFL REAL_LT_RMUL REAL_LT_RMUL_EQ REAL_LT_RNEG : thm) :
    ExceptT String IO IntThms5 := do
  let INT_OF_REAL_THM th := ExceptT.mk (INT_OF_REAL_THM' th)
  let INT_LT_ADDR ← INT_OF_REAL_THM REAL_LT_ADDR
  let INT_LT_ADD_SUB ← INT_OF_REAL_THM REAL_LT_ADD_SUB
  let INT_LT_ANTISYM ← INT_OF_REAL_THM REAL_LT_ANTISYM
  let INT_LT_GT ← INT_OF_REAL_THM REAL_LT_GT
  let INT_LT_IMP_LE ← INT_OF_REAL_THM REAL_LT_IMP_LE
  let INT_LT_IMP_NE ← INT_OF_REAL_THM REAL_LT_IMP_NE
  let INT_LT_LADD ← INT_OF_REAL_THM REAL_LT_LADD
  let INT_LT_LADD_IMP ← INT_OF_REAL_THM REAL_LT_LADD_IMP
  let INT_LT_LCANCEL_IMP ← INT_OF_REAL_THM REAL_LT_LCANCEL_IMP
  let INT_LT_LE ← INT_OF_REAL_THM REAL_LT_LE
  let INT_LT_LMUL ← INT_OF_REAL_THM REAL_LT_LMUL
  let INT_LT_LMUL_EQ ← INT_OF_REAL_THM REAL_LT_LMUL_EQ
  let INT_LT_LNEG ← INT_OF_REAL_THM REAL_LT_LNEG
  let INT_LT_MAX ← INT_OF_REAL_THM REAL_LT_MAX
  let INT_LT_MIN ← INT_OF_REAL_THM REAL_LT_MIN
  let INT_LT_MUL ← INT_OF_REAL_THM REAL_LT_MUL
  let INT_LT_MUL2 ← INT_OF_REAL_THM REAL_LT_MUL2
  let INT_LT_MUL_EQ ← INT_OF_REAL_THM REAL_LT_MUL_EQ
  let INT_LT_NEG2 ← INT_OF_REAL_THM REAL_LT_NEG2
  let INT_LT_NEGTOTAL ← INT_OF_REAL_THM REAL_LT_NEGTOTAL
  let INT_LT_POW2 ← INT_OF_REAL_THM REAL_LT_POW2
  let INT_LT_POW_2 ← INT_OF_REAL_THM REAL_LT_POW_2
  let INT_LT_RADD ← INT_OF_REAL_THM REAL_LT_RADD
  let INT_LT_RCANCEL_IMP ← INT_OF_REAL_THM REAL_LT_RCANCEL_IMP
  let INT_LT_REFL ← INT_OF_REAL_THM REAL_LT_REFL
  let INT_LT_RMUL ← INT_OF_REAL_THM REAL_LT_RMUL
  let INT_LT_RMUL_EQ ← INT_OF_REAL_THM REAL_LT_RMUL_EQ
  let INT_LT_RNEG ← INT_OF_REAL_THM REAL_LT_RNEG
  return { INT_LT_ADDR, INT_LT_ADD_SUB, INT_LT_ANTISYM, INT_LT_GT, INT_LT_IMP_LE,
           INT_LT_IMP_NE, INT_LT_LADD, INT_LT_LADD_IMP, INT_LT_LCANCEL_IMP,
           INT_LT_LE, INT_LT_LMUL, INT_LT_LMUL_EQ, INT_LT_LNEG, INT_LT_MAX,
           INT_LT_MIN, INT_LT_MUL, INT_LT_MUL2, INT_LT_MUL_EQ, INT_LT_NEG2,
           INT_LT_NEGTOTAL, INT_LT_POW2, INT_LT_POW_2, INT_LT_RADD,
           INT_LT_RCANCEL_IMP, INT_LT_REFL, INT_LT_RMUL, INT_LT_RMUL_EQ,
           INT_LT_RNEG }

/-- int.ml 466-493. -/
structure IntThms6 where
  INT_LT_SQUARE : thm
  INT_LT_SQUARE_ABS : thm
  INT_LT_SUB_LADD : thm
  INT_LT_SUB_RADD : thm
  INT_LT_TOTAL : thm
  INT_LT_TRANS : thm
  INT_MAX_ACI : thm
  INT_MAX_ASSOC : thm
  INT_MAX_LE : thm
  INT_MAX_LT : thm
  INT_MAX_MAX : thm
  INT_MAX_MIN : thm
  INT_MAX_SYM : thm
  INT_MIN_ACI : thm
  INT_MIN_ASSOC : thm
  INT_MIN_LE : thm
  INT_MIN_LT : thm
  INT_MIN_MAX : thm
  INT_MIN_MIN : thm
  INT_MIN_SYM : thm
  INT_MUL_2 : thm
  INT_MUL_AC : thm
  INT_MUL_ASSOC : thm
  INT_MUL_LID : thm
  INT_MUL_LNEG : thm
  INT_MUL_LZERO : thm
  INT_MUL_POS_LE : thm
  INT_MUL_POS_LT : thm
  deriving Inhabited

def setupIntThms6 (INT_OF_REAL_THM' : thm → IO (Except String thm))
    (REAL_LT_SQUARE REAL_LT_SQUARE_ABS REAL_LT_SUB_LADD REAL_LT_SUB_RADD
     REAL_LT_TOTAL REAL_LT_TRANS REAL_MAX_ACI REAL_MAX_ASSOC REAL_MAX_LE
     REAL_MAX_LT REAL_MAX_MAX REAL_MAX_MIN REAL_MAX_SYM REAL_MIN_ACI
     REAL_MIN_ASSOC REAL_MIN_LE REAL_MIN_LT REAL_MIN_MAX REAL_MIN_MIN
     REAL_MIN_SYM REAL_MUL_2 REAL_MUL_AC REAL_MUL_ASSOC REAL_MUL_LID
     REAL_MUL_LNEG REAL_MUL_LZERO REAL_MUL_POS_LE REAL_MUL_POS_LT : thm) :
    ExceptT String IO IntThms6 := do
  let INT_OF_REAL_THM th := ExceptT.mk (INT_OF_REAL_THM' th)
  let INT_LT_SQUARE ← INT_OF_REAL_THM REAL_LT_SQUARE
  let INT_LT_SQUARE_ABS ← INT_OF_REAL_THM REAL_LT_SQUARE_ABS
  let INT_LT_SUB_LADD ← INT_OF_REAL_THM REAL_LT_SUB_LADD
  let INT_LT_SUB_RADD ← INT_OF_REAL_THM REAL_LT_SUB_RADD
  let INT_LT_TOTAL ← INT_OF_REAL_THM REAL_LT_TOTAL
  let INT_LT_TRANS ← INT_OF_REAL_THM REAL_LT_TRANS
  let INT_MAX_ACI ← INT_OF_REAL_THM REAL_MAX_ACI
  let INT_MAX_ASSOC ← INT_OF_REAL_THM REAL_MAX_ASSOC
  let INT_MAX_LE ← INT_OF_REAL_THM REAL_MAX_LE
  let INT_MAX_LT ← INT_OF_REAL_THM REAL_MAX_LT
  let INT_MAX_MAX ← INT_OF_REAL_THM REAL_MAX_MAX
  let INT_MAX_MIN ← INT_OF_REAL_THM REAL_MAX_MIN
  let INT_MAX_SYM ← INT_OF_REAL_THM REAL_MAX_SYM
  let INT_MIN_ACI ← INT_OF_REAL_THM REAL_MIN_ACI
  let INT_MIN_ASSOC ← INT_OF_REAL_THM REAL_MIN_ASSOC
  let INT_MIN_LE ← INT_OF_REAL_THM REAL_MIN_LE
  let INT_MIN_LT ← INT_OF_REAL_THM REAL_MIN_LT
  let INT_MIN_MAX ← INT_OF_REAL_THM REAL_MIN_MAX
  let INT_MIN_MIN ← INT_OF_REAL_THM REAL_MIN_MIN
  let INT_MIN_SYM ← INT_OF_REAL_THM REAL_MIN_SYM
  let INT_MUL_2 ← INT_OF_REAL_THM REAL_MUL_2
  let INT_MUL_AC ← INT_OF_REAL_THM REAL_MUL_AC
  let INT_MUL_ASSOC ← INT_OF_REAL_THM REAL_MUL_ASSOC
  let INT_MUL_LID ← INT_OF_REAL_THM REAL_MUL_LID
  let INT_MUL_LNEG ← INT_OF_REAL_THM REAL_MUL_LNEG
  let INT_MUL_LZERO ← INT_OF_REAL_THM REAL_MUL_LZERO
  let INT_MUL_POS_LE ← INT_OF_REAL_THM REAL_MUL_POS_LE
  let INT_MUL_POS_LT ← INT_OF_REAL_THM REAL_MUL_POS_LT
  return { INT_LT_SQUARE, INT_LT_SQUARE_ABS, INT_LT_SUB_LADD, INT_LT_SUB_RADD,
           INT_LT_TOTAL, INT_LT_TRANS, INT_MAX_ACI, INT_MAX_ASSOC, INT_MAX_LE,
           INT_MAX_LT, INT_MAX_MAX, INT_MAX_MIN, INT_MAX_SYM, INT_MIN_ACI,
           INT_MIN_ASSOC, INT_MIN_LE, INT_MIN_LT, INT_MIN_MAX, INT_MIN_MIN,
           INT_MIN_SYM, INT_MUL_2, INT_MUL_AC, INT_MUL_ASSOC, INT_MUL_LID,
           INT_MUL_LNEG, INT_MUL_LZERO, INT_MUL_POS_LE, INT_MUL_POS_LT }

/-- int.ml 494-521. -/
structure IntThms7 where
  INT_MUL_RID : thm
  INT_MUL_RNEG : thm
  INT_MUL_RZERO : thm
  INT_MUL_SYM : thm
  INT_NEG_0 : thm
  INT_NEG_ADD : thm
  INT_NEG_EQ : thm
  INT_NEG_EQ_0 : thm
  INT_NEG_GE0 : thm
  INT_NEG_GT0 : thm
  INT_NEG_LE0 : thm
  INT_NEG_LMUL : thm
  INT_NEG_LT0 : thm
  INT_NEG_MINUS1 : thm
  INT_NEG_MUL2 : thm
  INT_NEG_NEG : thm
  INT_NEG_RMUL : thm
  INT_NEG_SUB : thm
  INT_NOT_EQ : thm
  INT_NOT_LE : thm
  INT_NOT_LT : thm
  INT_OF_NUM_ADD : thm
  INT_OF_NUM_CLAUSES : thm
  INT_OF_NUM_EQ : thm
  INT_OF_NUM_GE : thm
  INT_OF_NUM_GT : thm
  INT_OF_NUM_LE : thm
  INT_OF_NUM_LT : thm
  deriving Inhabited

def setupIntThms7 (INT_OF_REAL_THM' : thm → IO (Except String thm))
    (REAL_MUL_RID REAL_MUL_RNEG REAL_MUL_RZERO REAL_MUL_SYM REAL_NEG_0
     REAL_NEG_ADD REAL_NEG_EQ REAL_NEG_EQ_0 REAL_NEG_GE0 REAL_NEG_GT0
     REAL_NEG_LE0 REAL_NEG_LMUL REAL_NEG_LT0 REAL_NEG_MINUS1 REAL_NEG_MUL2
     REAL_NEG_NEG REAL_NEG_RMUL REAL_NEG_SUB REAL_NOT_EQ REAL_NOT_LE
     REAL_NOT_LT REAL_OF_NUM_ADD REAL_OF_NUM_CLAUSES REAL_OF_NUM_EQ
     REAL_OF_NUM_GE REAL_OF_NUM_GT REAL_OF_NUM_LE REAL_OF_NUM_LT : thm) :
    ExceptT String IO IntThms7 := do
  let INT_OF_REAL_THM th := ExceptT.mk (INT_OF_REAL_THM' th)
  let INT_MUL_RID ← INT_OF_REAL_THM REAL_MUL_RID
  let INT_MUL_RNEG ← INT_OF_REAL_THM REAL_MUL_RNEG
  let INT_MUL_RZERO ← INT_OF_REAL_THM REAL_MUL_RZERO
  let INT_MUL_SYM ← INT_OF_REAL_THM REAL_MUL_SYM
  let INT_NEG_0 ← INT_OF_REAL_THM REAL_NEG_0
  let INT_NEG_ADD ← INT_OF_REAL_THM REAL_NEG_ADD
  let INT_NEG_EQ ← INT_OF_REAL_THM REAL_NEG_EQ
  let INT_NEG_EQ_0 ← INT_OF_REAL_THM REAL_NEG_EQ_0
  let INT_NEG_GE0 ← INT_OF_REAL_THM REAL_NEG_GE0
  let INT_NEG_GT0 ← INT_OF_REAL_THM REAL_NEG_GT0
  let INT_NEG_LE0 ← INT_OF_REAL_THM REAL_NEG_LE0
  let INT_NEG_LMUL ← INT_OF_REAL_THM REAL_NEG_LMUL
  let INT_NEG_LT0 ← INT_OF_REAL_THM REAL_NEG_LT0
  let INT_NEG_MINUS1 ← INT_OF_REAL_THM REAL_NEG_MINUS1
  let INT_NEG_MUL2 ← INT_OF_REAL_THM REAL_NEG_MUL2
  let INT_NEG_NEG ← INT_OF_REAL_THM REAL_NEG_NEG
  let INT_NEG_RMUL ← INT_OF_REAL_THM REAL_NEG_RMUL
  let INT_NEG_SUB ← INT_OF_REAL_THM REAL_NEG_SUB
  let INT_NOT_EQ ← INT_OF_REAL_THM REAL_NOT_EQ
  let INT_NOT_LE ← INT_OF_REAL_THM REAL_NOT_LE
  let INT_NOT_LT ← INT_OF_REAL_THM REAL_NOT_LT
  let INT_OF_NUM_ADD ← INT_OF_REAL_THM REAL_OF_NUM_ADD
  let INT_OF_NUM_CLAUSES ← INT_OF_REAL_THM REAL_OF_NUM_CLAUSES
  let INT_OF_NUM_EQ ← INT_OF_REAL_THM REAL_OF_NUM_EQ
  let INT_OF_NUM_GE ← INT_OF_REAL_THM REAL_OF_NUM_GE
  let INT_OF_NUM_GT ← INT_OF_REAL_THM REAL_OF_NUM_GT
  let INT_OF_NUM_LE ← INT_OF_REAL_THM REAL_OF_NUM_LE
  let INT_OF_NUM_LT ← INT_OF_REAL_THM REAL_OF_NUM_LT
  return { INT_MUL_RID, INT_MUL_RNEG, INT_MUL_RZERO, INT_MUL_SYM, INT_NEG_0,
           INT_NEG_ADD, INT_NEG_EQ, INT_NEG_EQ_0, INT_NEG_GE0, INT_NEG_GT0,
           INT_NEG_LE0, INT_NEG_LMUL, INT_NEG_LT0, INT_NEG_MINUS1, INT_NEG_MUL2,
           INT_NEG_NEG, INT_NEG_RMUL, INT_NEG_SUB, INT_NOT_EQ, INT_NOT_LE,
           INT_NOT_LT, INT_OF_NUM_ADD, INT_OF_NUM_CLAUSES, INT_OF_NUM_EQ,
           INT_OF_NUM_GE, INT_OF_NUM_GT, INT_OF_NUM_LE, INT_OF_NUM_LT }

/-- int.ml 522-549. -/
structure IntThms8 where
  INT_OF_NUM_MAX : thm
  INT_OF_NUM_MIN : thm
  INT_OF_NUM_MOD : thm
  INT_OF_NUM_MUL : thm
  INT_OF_NUM_POW : thm
  INT_OF_NUM_SUB : thm
  INT_OF_NUM_SUB_CASES : thm
  INT_OF_NUM_SUC : thm
  INT_POS : thm
  INT_POS_EQ_SQUARE : thm
  INT_POS_NZ : thm
  INT_POW2_ABS : thm
  INT_POW_1 : thm
  INT_POW_1_LE : thm
  INT_POW_1_LT : thm
  INT_POW_2 : thm
  INT_POW_ADD : thm
  INT_POW_EQ : thm
  INT_POW_EQ_0 : thm
  INT_POW_EQ_1 : thm
  INT_POW_EQ_1_IMP : thm
  INT_POW_EQ_ABS : thm
  INT_POW_EQ_EQ : thm
  INT_POW_EQ_ODD : thm
  INT_POW_EQ_ODD_EQ : thm
  INT_POW_LBOUND : thm
  INT_POW_LE : thm
  INT_POW_LE2 : thm
  deriving Inhabited

def setupIntThms8 (INT_OF_REAL_THM' : thm → IO (Except String thm))
    (REAL_OF_NUM_MAX REAL_OF_NUM_MIN REAL_OF_NUM_MOD REAL_OF_NUM_MUL
     REAL_OF_NUM_POW REAL_OF_NUM_SUB REAL_OF_NUM_SUB_CASES REAL_OF_NUM_SUC
     REAL_POS REAL_POS_EQ_SQUARE REAL_LT_IMP_NZ REAL_POW2_ABS REAL_POW_1
     REAL_POW_1_LE REAL_POW_1_LT REAL_POW_2 REAL_POW_ADD REAL_POW_EQ
     REAL_POW_EQ_0 REAL_POW_EQ_1 REAL_POW_EQ_1_IMP REAL_POW_EQ_ABS
     REAL_POW_EQ_EQ REAL_POW_EQ_ODD REAL_POW_EQ_ODD_EQ REAL_POW_LBOUND
     REAL_POW_LE REAL_POW_LE2 : thm) :
    ExceptT String IO IntThms8 := do
  let INT_OF_REAL_THM th := ExceptT.mk (INT_OF_REAL_THM' th)
  let INT_OF_NUM_MAX ← INT_OF_REAL_THM REAL_OF_NUM_MAX
  let INT_OF_NUM_MIN ← INT_OF_REAL_THM REAL_OF_NUM_MIN
  let INT_OF_NUM_MOD ← INT_OF_REAL_THM REAL_OF_NUM_MOD
  let INT_OF_NUM_MUL ← INT_OF_REAL_THM REAL_OF_NUM_MUL
  let INT_OF_NUM_POW ← INT_OF_REAL_THM REAL_OF_NUM_POW
  let INT_OF_NUM_SUB ← INT_OF_REAL_THM REAL_OF_NUM_SUB
  let INT_OF_NUM_SUB_CASES ← INT_OF_REAL_THM REAL_OF_NUM_SUB_CASES
  let INT_OF_NUM_SUC ← INT_OF_REAL_THM REAL_OF_NUM_SUC
  let INT_POS ← INT_OF_REAL_THM REAL_POS
  let INT_POS_EQ_SQUARE ← INT_OF_REAL_THM REAL_POS_EQ_SQUARE
  let INT_POS_NZ ← INT_OF_REAL_THM REAL_LT_IMP_NZ
  let INT_POW2_ABS ← INT_OF_REAL_THM REAL_POW2_ABS
  let INT_POW_1 ← INT_OF_REAL_THM REAL_POW_1
  let INT_POW_1_LE ← INT_OF_REAL_THM REAL_POW_1_LE
  let INT_POW_1_LT ← INT_OF_REAL_THM REAL_POW_1_LT
  let INT_POW_2 ← INT_OF_REAL_THM REAL_POW_2
  let INT_POW_ADD ← INT_OF_REAL_THM REAL_POW_ADD
  let INT_POW_EQ ← INT_OF_REAL_THM REAL_POW_EQ
  let INT_POW_EQ_0 ← INT_OF_REAL_THM REAL_POW_EQ_0
  let INT_POW_EQ_1 ← INT_OF_REAL_THM REAL_POW_EQ_1
  let INT_POW_EQ_1_IMP ← INT_OF_REAL_THM REAL_POW_EQ_1_IMP
  let INT_POW_EQ_ABS ← INT_OF_REAL_THM REAL_POW_EQ_ABS
  let INT_POW_EQ_EQ ← INT_OF_REAL_THM REAL_POW_EQ_EQ
  let INT_POW_EQ_ODD ← INT_OF_REAL_THM REAL_POW_EQ_ODD
  let INT_POW_EQ_ODD_EQ ← INT_OF_REAL_THM REAL_POW_EQ_ODD_EQ
  let INT_POW_LBOUND ← INT_OF_REAL_THM REAL_POW_LBOUND
  let INT_POW_LE ← INT_OF_REAL_THM REAL_POW_LE
  let INT_POW_LE2 ← INT_OF_REAL_THM REAL_POW_LE2
  return { INT_OF_NUM_MAX, INT_OF_NUM_MIN, INT_OF_NUM_MOD, INT_OF_NUM_MUL,
           INT_OF_NUM_POW, INT_OF_NUM_SUB, INT_OF_NUM_SUB_CASES, INT_OF_NUM_SUC,
           INT_POS, INT_POS_EQ_SQUARE, INT_POS_NZ, INT_POW2_ABS, INT_POW_1,
           INT_POW_1_LE, INT_POW_1_LT, INT_POW_2, INT_POW_ADD, INT_POW_EQ,
           INT_POW_EQ_0, INT_POW_EQ_1, INT_POW_EQ_1_IMP, INT_POW_EQ_ABS,
           INT_POW_EQ_EQ, INT_POW_EQ_ODD, INT_POW_EQ_ODD_EQ, INT_POW_LBOUND,
           INT_POW_LE, INT_POW_LE2 }

/-- int.ml 550-575. -/
structure IntThms9 where
  INT_POW_LE2_ODD : thm
  INT_POW_LE2_ODD_EQ : thm
  INT_POW_LE2_REV : thm
  INT_POW_LE_1 : thm
  INT_POW_LT : thm
  INT_POW_LT2 : thm
  INT_POW_LT2_ODD : thm
  INT_POW_LT2_ODD_EQ : thm
  INT_POW_LT2_REV : thm
  INT_POW_LT_1 : thm
  INT_POW_MONO : thm
  INT_POW_MONO_LT : thm
  INT_POW_MUL : thm
  INT_POW_NEG : thm
  INT_POW_NZ : thm
  INT_POW_ONE : thm
  INT_POW_POW : thm
  INT_POW_ZERO : thm
  INT_RNEG_UNIQ : thm
  INT_SGN : thm
  INT_SGNS_EQ : thm
  INT_SGNS_EQ_ALT : thm
  INT_SGN_0 : thm
  INT_SGN_ABS : thm
  INT_SGN_ABS_ALT : thm
  INT_SGN_CASES : thm
  deriving Inhabited

def setupIntThms9 (INT_OF_REAL_THM' : thm → IO (Except String thm))
    (REAL_POW_LE2_ODD REAL_POW_LE2_ODD_EQ REAL_POW_LE2_REV REAL_POW_LE_1
     REAL_POW_LT REAL_POW_LT2 REAL_POW_LT2_ODD REAL_POW_LT2_ODD_EQ
     REAL_POW_LT2_REV REAL_POW_LT_1 REAL_POW_MONO REAL_POW_MONO_LT REAL_POW_MUL
     REAL_POW_NEG REAL_POW_NZ REAL_POW_ONE REAL_POW_POW REAL_POW_ZERO
     REAL_RNEG_UNIQ real_sgn REAL_SGNS_EQ REAL_SGNS_EQ_ALT REAL_SGN_0
     REAL_SGN_ABS REAL_SGN_ABS_ALT REAL_SGN_CASES : thm) :
    ExceptT String IO IntThms9 := do
  let INT_OF_REAL_THM th := ExceptT.mk (INT_OF_REAL_THM' th)
  let INT_POW_LE2_ODD ← INT_OF_REAL_THM REAL_POW_LE2_ODD
  let INT_POW_LE2_ODD_EQ ← INT_OF_REAL_THM REAL_POW_LE2_ODD_EQ
  let INT_POW_LE2_REV ← INT_OF_REAL_THM REAL_POW_LE2_REV
  let INT_POW_LE_1 ← INT_OF_REAL_THM REAL_POW_LE_1
  let INT_POW_LT ← INT_OF_REAL_THM REAL_POW_LT
  let INT_POW_LT2 ← INT_OF_REAL_THM REAL_POW_LT2
  let INT_POW_LT2_ODD ← INT_OF_REAL_THM REAL_POW_LT2_ODD
  let INT_POW_LT2_ODD_EQ ← INT_OF_REAL_THM REAL_POW_LT2_ODD_EQ
  let INT_POW_LT2_REV ← INT_OF_REAL_THM REAL_POW_LT2_REV
  let INT_POW_LT_1 ← INT_OF_REAL_THM REAL_POW_LT_1
  let INT_POW_MONO ← INT_OF_REAL_THM REAL_POW_MONO
  let INT_POW_MONO_LT ← INT_OF_REAL_THM REAL_POW_MONO_LT
  let INT_POW_MUL ← INT_OF_REAL_THM REAL_POW_MUL
  let INT_POW_NEG ← INT_OF_REAL_THM REAL_POW_NEG
  let INT_POW_NZ ← INT_OF_REAL_THM REAL_POW_NZ
  let INT_POW_ONE ← INT_OF_REAL_THM REAL_POW_ONE
  let INT_POW_POW ← INT_OF_REAL_THM REAL_POW_POW
  let INT_POW_ZERO ← INT_OF_REAL_THM REAL_POW_ZERO
  let INT_RNEG_UNIQ ← INT_OF_REAL_THM REAL_RNEG_UNIQ
  let INT_SGN ← INT_OF_REAL_THM real_sgn
  let INT_SGNS_EQ ← INT_OF_REAL_THM REAL_SGNS_EQ
  let INT_SGNS_EQ_ALT ← INT_OF_REAL_THM REAL_SGNS_EQ_ALT
  let INT_SGN_0 ← INT_OF_REAL_THM REAL_SGN_0
  let INT_SGN_ABS ← INT_OF_REAL_THM REAL_SGN_ABS
  let INT_SGN_ABS_ALT ← INT_OF_REAL_THM REAL_SGN_ABS_ALT
  let INT_SGN_CASES ← INT_OF_REAL_THM REAL_SGN_CASES
  return { INT_POW_LE2_ODD, INT_POW_LE2_ODD_EQ, INT_POW_LE2_REV, INT_POW_LE_1,
           INT_POW_LT, INT_POW_LT2, INT_POW_LT2_ODD, INT_POW_LT2_ODD_EQ,
           INT_POW_LT2_REV, INT_POW_LT_1, INT_POW_MONO, INT_POW_MONO_LT,
           INT_POW_MUL, INT_POW_NEG, INT_POW_NZ, INT_POW_ONE, INT_POW_POW,
           INT_POW_ZERO, INT_RNEG_UNIQ, INT_SGN, INT_SGNS_EQ, INT_SGNS_EQ_ALT,
           INT_SGN_0, INT_SGN_ABS, INT_SGN_ABS_ALT, INT_SGN_CASES }

/-- int.ml 576-601. -/
structure IntThms10 where
  INT_SGN_EQ : thm
  INT_SGN_EQ_INEQ : thm
  INT_SGN_INEQS : thm
  INT_SGN_INT_SGN : thm
  INT_SGN_MUL : thm
  INT_SGN_NEG : thm
  INT_SGN_POW : thm
  INT_SGN_POW_2 : thm
  INT_SOS_EQ_0 : thm
  INT_SUB_0 : thm
  INT_SUB_ABS : thm
  INT_SUB_ADD : thm
  INT_SUB_ADD2 : thm
  INT_SUB_LDISTRIB : thm
  INT_SUB_LE : thm
  INT_SUB_LNEG : thm
  INT_SUB_LT : thm
  INT_SUB_LZERO : thm
  INT_SUB_NEG2 : thm
  INT_SUB_RDISTRIB : thm
  INT_SUB_REFL : thm
  INT_SUB_RNEG : thm
  INT_SUB_RZERO : thm
  INT_SUB_SUB : thm
  INT_SUB_SUB2 : thm
  INT_SUB_TRIANGLE : thm
  deriving Inhabited

def setupIntThms10 (INT_OF_REAL_THM' : thm → IO (Except String thm))
    (REAL_SGN_EQ REAL_SGN_EQ_INEQ REAL_SGN_INEQS REAL_SGN_REAL_SGN REAL_SGN_MUL
     REAL_SGN_NEG REAL_SGN_POW REAL_SGN_POW_2 REAL_SOS_EQ_0 REAL_SUB_0
     REAL_SUB_ABS REAL_SUB_ADD REAL_SUB_ADD2 REAL_SUB_LDISTRIB REAL_SUB_LE
     REAL_SUB_LNEG REAL_SUB_LT REAL_SUB_LZERO REAL_SUB_NEG2 REAL_SUB_RDISTRIB
     REAL_SUB_REFL REAL_SUB_RNEG REAL_SUB_RZERO REAL_SUB_SUB REAL_SUB_SUB2
     REAL_SUB_TRIANGLE : thm) :
    ExceptT String IO IntThms10 := do
  let INT_OF_REAL_THM th := ExceptT.mk (INT_OF_REAL_THM' th)
  let INT_SGN_EQ ← INT_OF_REAL_THM REAL_SGN_EQ
  let INT_SGN_EQ_INEQ ← INT_OF_REAL_THM REAL_SGN_EQ_INEQ
  let INT_SGN_INEQS ← INT_OF_REAL_THM REAL_SGN_INEQS
  let INT_SGN_INT_SGN ← INT_OF_REAL_THM REAL_SGN_REAL_SGN
  let INT_SGN_MUL ← INT_OF_REAL_THM REAL_SGN_MUL
  let INT_SGN_NEG ← INT_OF_REAL_THM REAL_SGN_NEG
  let INT_SGN_POW ← INT_OF_REAL_THM REAL_SGN_POW
  let INT_SGN_POW_2 ← INT_OF_REAL_THM REAL_SGN_POW_2
  let INT_SOS_EQ_0 ← INT_OF_REAL_THM REAL_SOS_EQ_0
  let INT_SUB_0 ← INT_OF_REAL_THM REAL_SUB_0
  let INT_SUB_ABS ← INT_OF_REAL_THM REAL_SUB_ABS
  let INT_SUB_ADD ← INT_OF_REAL_THM REAL_SUB_ADD
  let INT_SUB_ADD2 ← INT_OF_REAL_THM REAL_SUB_ADD2
  let INT_SUB_LDISTRIB ← INT_OF_REAL_THM REAL_SUB_LDISTRIB
  let INT_SUB_LE ← INT_OF_REAL_THM REAL_SUB_LE
  let INT_SUB_LNEG ← INT_OF_REAL_THM REAL_SUB_LNEG
  let INT_SUB_LT ← INT_OF_REAL_THM REAL_SUB_LT
  let INT_SUB_LZERO ← INT_OF_REAL_THM REAL_SUB_LZERO
  let INT_SUB_NEG2 ← INT_OF_REAL_THM REAL_SUB_NEG2
  let INT_SUB_RDISTRIB ← INT_OF_REAL_THM REAL_SUB_RDISTRIB
  let INT_SUB_REFL ← INT_OF_REAL_THM REAL_SUB_REFL
  let INT_SUB_RNEG ← INT_OF_REAL_THM REAL_SUB_RNEG
  let INT_SUB_RZERO ← INT_OF_REAL_THM REAL_SUB_RZERO
  let INT_SUB_SUB ← INT_OF_REAL_THM REAL_SUB_SUB
  let INT_SUB_SUB2 ← INT_OF_REAL_THM REAL_SUB_SUB2
  let INT_SUB_TRIANGLE ← INT_OF_REAL_THM REAL_SUB_TRIANGLE
  return { INT_SGN_EQ, INT_SGN_EQ_INEQ, INT_SGN_INEQS, INT_SGN_INT_SGN,
           INT_SGN_MUL, INT_SGN_NEG, INT_SGN_POW, INT_SGN_POW_2, INT_SOS_EQ_0,
           INT_SUB_0, INT_SUB_ABS, INT_SUB_ADD, INT_SUB_ADD2, INT_SUB_LDISTRIB,
           INT_SUB_LE, INT_SUB_LNEG, INT_SUB_LT, INT_SUB_LZERO, INT_SUB_NEG2,
           INT_SUB_RDISTRIB, INT_SUB_REFL, INT_SUB_RNEG, INT_SUB_RZERO,
           INT_SUB_SUB, INT_SUB_SUB2, INT_SUB_TRIANGLE }

structure IntWlog where
  INT_WLOG_LE   : thm
  INT_WLOG_LT   : thm
  INT_WLOG_LE_3 : thm
  deriving Inhabited

/-- int.ml 603-616. -/
@[nospecialize]
def setupIntWlog [HolBase]
    (INT_LE_TOTAL : thm) (INT_LT_TOTAL : thm)
    (MESON_TAC : List thm → tactic) :
    ExceptT String IO IntWlog := do
  let INT_WLOG_LE ← prove
   r"(!x y:int. P x y <=> P y x) /\ (!x y. x <= y ==> P x y) ==> !x y. P x y"
   (MESON_TAC [INT_LE_TOTAL])

  let INT_WLOG_LT ← prove
   r"(!x:int. P x x) /\ (!x y. P x y <=> P y x) /\ (!x y. x < y ==> P x y)
   ==> !x y. P x y"
   (MESON_TAC [INT_LT_TOTAL])

  let INT_WLOG_LE_3 ← prove
   r"!P. (!x y z. P x y z ==> P y x z /\ P x z y) /\
       (!x y z:int. x <= y /\ y <= z ==> P x y z)
       ==> !x y z. P x y z"
   (MESON_TAC [INT_LE_TOTAL])

  return { INT_WLOG_LE, INT_WLOG_LT, INT_WLOG_LE_3 }

/-- int.ml 619-709.  `INT_ARITH`, `INT_ARITH_TAC` and `ASM_INT_ARITH_TAC` are
    defined again at int.ml 2193-2319 ("enhanced later"); these first
    versions are numbered 1. -/
structure IntArith1 where
  /-- `INT_FORALL_POS` (int.ml 622):
      `!P. (!n. P(&n)) <=> (!i:int. &0 <= i ==> P(i))`. -/
  INT_FORALL_POS : thm
  /-- `INT_EXISTS_POS` (int.ml 630):
      `!P. (?n. P(&n)) <=> (?i:int. &0 <= i /\ P(i))`. -/
  INT_EXISTS_POS : thm
  /-- `INT_FORALL_ABS` (int.ml 635):
      `!P. (!n. P(&n)) <=> (!x:int. P(abs x))`. -/
  INT_FORALL_ABS : thm
  /-- `INT_EXISTS_ABS` (int.ml 639):
      `!P. (?n. P(&n)) <=> (?x:int. P(abs x))`. -/
  INT_EXISTS_ABS : thm
  INT_POW : thm
  INT_ABS : thm
  INT_GE : thm
  INT_GT : thm
  INT_LT : thm
  /-- `INT_ARITH` (int.ml 674), the first of two. -/
  INT_ARITH1 : term → IO (Except String thm)
  /-- `INT_ARITH_TAC` (int.ml 705). -/
  INT_ARITH_TAC1 : tactic
  /-- `ASM_INT_ARITH_TAC` (int.ml 707). -/
  ASM_INT_ARITH_TAC1 : tactic
  deriving Inhabited

/-- `REAL_ARITH` is calc_rat.ml's final one (Session's `REAL_ARITH3`). -/
@[nospecialize]
def setupIntArith1 [HolBase] (P : HolCore.Canon.NNFPths)
    (O : IntOps) (int_eq : thm)
    (INT_OF_REAL_THM' : thm → IO (Except String thm))
    (R : HolMath.RealAx.RealThms)
    (A2 : HolMath.Arith.ArithThms2)
    (INT_ADD_LID INT_LE_RNEG : thm)
    (INT_OF_NUM_LE INT_NEG_0 INT_NOT_LE INT_NOT_LT INT_NOT_EQ : thm)
    (INT_ABS_POS INT_ABS_REFL : thm)
    (PRESIMP_CONV NNF_CONV CONDS_ELIM_CONV : ioconv)
    (REAL_ARITH : term → IO (Except String thm))
    (MESON_TAC : List thm → tactic) :
    ExceptT String IO IntArith1 := do
  let INT_OF_REAL_THM (th : thm) : ExceptT String IO thm := INT_OF_REAL_THM' th
  let { int_le, int_lt, int_ge, int_gt, int_of_num_th, int_neg_th, int_add_th,
        int_mul_th, int_sub_th, int_pow_th, int_abs_th, int_max_th, int_min_th,
        INT_IMAGE, INT_LT_DISCRETE, .. } := O
  let { real_pow, real_abs, real_ge, real_gt, real_lt, .. } := R
  let { LE, LE_0, .. } := A2
  let { NOT_EXISTS_THM, .. } := HolBase.C

  /- ---------------------------------------------------------------------- -/
  /- More useful "image" theorems.                                          -/
  /- ---------------------------------------------------------------------- -/

  let INT_FORALL_POS ← prove
   r"!P. (!n. P(&n)) <=> (!i:int. &0 <= i ==> P(i))"
   (GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN GEN_TAC THENL
     [DISJ_CASES_THEN (CHOOSE_THEN SUBST1_TAC) (← SPEC (← q r"i:int") INT_IMAGE) THEN
      ASM_REWRITE_TAC [INT_LE_RNEG, INT_ADD_LID, INT_OF_NUM_LE, LE] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [INT_NEG_0],
      FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [INT_OF_NUM_LE, LE_0]])

  let INT_EXISTS_POS ← prove
   r"!P. (?n. P(&n)) <=> (?i:int. &0 <= i /\ P(i))"
   (GEN_TAC THEN GEN_REWRITE_TAC I [← TAUT (← q r"(p <=> q) <=> (~p <=> ~q)")] THEN
    REWRITE_TAC [NOT_EXISTS_THM, INT_FORALL_POS] THEN MESON_TAC [])

  let INT_FORALL_ABS ← prove
   r"!P. (!n. P(&n)) <=> (!x:int. P(abs x))"
   (REWRITE_TAC [INT_FORALL_POS] THEN MESON_TAC [INT_ABS_POS, INT_ABS_REFL])

  let INT_EXISTS_ABS ← prove
   r"!P. (?n. P(&n)) <=> (?x:int. P(abs x))"
   (GEN_TAC THEN GEN_REWRITE_TAC I [← TAUT (← q r"(p <=> q) <=> (~p <=> ~q)")] THEN
    REWRITE_TAC [NOT_EXISTS_THM, INT_FORALL_ABS] THEN MESON_TAC [])

  /- ---------------------------------------------------------------------- -/
  /- A few "pseudo definitions".                                            -/
  /- ---------------------------------------------------------------------- -/

  let INT_POW ← prove
   r"(x pow 0 = &1) /\
   (!n. x pow (SUC n) = x * x pow n)"
   (REWRITE_TAC (← (CONJUNCTS real_pow).mapM INT_OF_REAL_THM))

  let INT_ABS ← prove
   r"!x. abs(x) = if &0 <= x then x else --x"
   (GEN_TAC THEN MP_TAC (← INT_OF_REAL_THM (← SPEC (← q r"x:real") real_abs)) THEN
    COND_CASES_TAC THEN REWRITE_TAC [int_eq])

  let INT_GE ← prove
   r"!x y. x >= y <=> y <= x"
   (REWRITE_TAC [int_ge, int_le, real_ge])

  let INT_GT ← prove
   r"!x y. x > y <=> y < x"
   (REWRITE_TAC [int_gt, int_lt, real_gt])

  let INT_LT ← prove
   r"!x y. x < y <=> ~(y <= x)"
   (REWRITE_TAC [int_lt, int_le, real_lt])

  /- ---------------------------------------------------------------------- -/
  /- An initial bootstrapping procedure for the integers, enhanced later.   -/
  /- ---------------------------------------------------------------------- -/

  -- let INT_ARITH =
  let atom_CONV ←
    GEN_REWRITE_CONV_NET I [← prove
      r"(~(x:int <= y) <=> y + &1 <= x) /\
        (~(x < y) <=> y <= x) /\
        (~(x = y) <=> x + &1 <= y \/ y + &1 <= x) /\
        (x < y <=> x + &1 <= y)"
      (REWRITE_TAC [INT_NOT_LE, INT_NOT_LT, INT_NOT_EQ, INT_LT_DISCRETE])]
  let bub_CONV ← GEN_REWRITE_CONV_NET TOP_SWEEP_CONV
   [int_eq, int_le, int_lt, int_ge, int_gt,
    int_of_num_th, int_neg_th, int_add_th, int_mul_th,
    int_sub_th, int_pow_th, int_abs_th, int_max_th, int_min_th]
  let base_CONV := TRY_CONV atom_CONV THENC bub_CONV
  let NNF_NORM_CONV := HolCore.Canon.GEN_NNF_CONV HolBase.B P false
   base_CONV (fun t => ExceptT.run do
     let n ← (base_CONV (← mk_neg t) : ExceptT String IO thm)
     pure ((← (base_CONV t : ExceptT String IO thm)), n))
  let init_CONV :=
    TOP_DEPTH_CONV BETA_CONV THENC
    PRESIMP_CONV THENC
    (← GEN_REWRITE_CONV_NET DEPTH_CONV [INT_GT, INT_GE]) THENC
    NNF_CONV THENC DEPTH_BINOP_CONV (← q r"(\/)") CONDS_ELIM_CONV THENC
    NNF_NORM_CONV
  let p_tm ← q r"p:bool"
  let not_tm ← q r"(~)"
  let pth ← TAUT (safe_mk_eq (← mk_neg (← mk_neg p_tm)) p_tm)
  let INT_ARITH1 (tm : term) : ExceptT String IO thm := do
    let th0 ← INST [(tm, p_tm)] pth
    let th1 ← (init_CONV (← mk_neg tm) : ExceptT String IO thm)
    let th2 ← (REAL_ARITH (← mk_neg (← rand (concl th1))) : ExceptT String IO thm)
    HolLight.EQ_MP th0 (← HolLight.EQ_MP (← AP_TERM not_tm (← SYM th1)) th2)

  let INT_ARITH_TAC1 := CONV_TAC (EQT_INTRO o INT_ARITH1)

  let ASM_INT_ARITH_TAC1 :=
    REPEAT (FIRST_X_ASSUM (MP_TAC o check (not o is_forall o concl))) THEN
    INT_ARITH_TAC1

  return { INT_FORALL_POS, INT_EXISTS_POS, INT_FORALL_ABS, INT_EXISTS_ABS,
           INT_POW, INT_ABS, INT_GE, INT_GT, INT_LT,
           INT_ARITH1 := fun t => (INT_ARITH1 t).run, INT_ARITH_TAC1, ASM_INT_ARITH_TAC1 }

/-- int.ml 714-866: pseudo-definitions, lemmas, the Archimedian property and
    Euclidean `div` and `rem`. -/
structure IntDivMod where
  /-- `INT_SUB` (int.ml 715): `!x y. x - y = x + --y`. -/
  INT_SUB : thm
  /-- `INT_MAX` (int.ml 717): `!x y. max x y = if x <= y then y else x`. -/
  INT_MAX : thm
  /-- `INT_MIN` (int.ml 719): `!x y. min x y = if x <= y then x else y`. -/
  INT_MIN : thm
  /-- `INT_OF_NUM_EXISTS` (int.ml 725):
      `!x:int. (?n. x = &n) <=> &0 <= x`. -/
  INT_OF_NUM_EXISTS : thm
  /-- `INT_LE_DISCRETE` (int.ml 732): `!x y:int. x <= y <=> x < y + &1`. -/
  INT_LE_DISCRETE : thm
  /-- `INT_LE_TRANS_LE` (int.ml 734):
      `!x y:int. x <= y <=> (!z. y <= z ==> x <= z)`. -/
  INT_LE_TRANS_LE : thm
  /-- `INT_LE_TRANS_LT` (int.ml 738):
      `!x y:int. x <= y <=> (!z. y < z ==> x < z)`. -/
  INT_LE_TRANS_LT : thm
  /-- `INT_MUL_EQ_1` (int.ml 743):
      `!x y:int. x * y = &1 <=> x = &1 /\ y = &1 \/ x = --(&1) /\ y = --(&1)`. -/
  INT_MUL_EQ_1 : thm
  /-- `INT_ABS_MUL_1` (int.ml 754):
      `!x y. abs(x * y) = &1 <=> abs(x) = &1 /\ abs(y) = &1`. -/
  INT_ABS_MUL_1 : thm
  /-- `INT_WOP` (int.ml 761): well-ordering of the non-negative integers. -/
  INT_WOP : thm
  /-- `INT_ARCH` (int.ml 773): `!x d. ~(d = &0) ==> ?c. x < c * d`. -/
  INT_ARCH : thm
  /-- `INT_DIVMOD_EXIST_0` (int.ml 796): the existence property from which
      `div`/`rem` are specified. -/
  INT_DIVMOD_EXIST_0 : thm
  /-- `INT_DIVISION_0` (int.ml 819): `new_specification ["div"; "rem"]`.  This
      is the raw specifying theorem for the two new constants. -/
  INT_DIVISION_0 : thm
  /-- `INT_DIVISION` (int.ml 822): the defining property of `div`/`rem`:
      `!m n. ~(n = &0) ==> m = m div n * n + m rem n /\
             &0 <= m rem n /\ m rem n < abs n`. -/
  INT_DIVISION : thm
  /-- `INT_DIVISION_SIMP` (int.ml 827): `!m n. m div n * n + m rem n = m`. -/
  INT_DIVISION_SIMP : thm
  /-- `INT_REM_POS` (int.ml 832): `!a b. ~(b = &0) ==> &0 <= a rem b`. -/
  INT_REM_POS : thm
  /-- `INT_DIV_0` (int.ml 836): `!m. m div &0 = &0`. -/
  INT_DIV_0 : thm
  /-- `INT_REM_0` (int.ml 840): `!m. m rem &0 = m`. -/
  INT_REM_0 : thm
  /-- `INT_REM_POS_EQ` (int.ml 844): `!m n. &0 <= m rem n <=> n = &0 ==> &0 <= m`. -/
  INT_REM_POS_EQ : thm
  /-- `INT_REM_DIV` (int.ml 849): `!m n. m rem n = m - m div n * n`. -/
  INT_REM_DIV : thm
  /-- `INT_LT_REM` (int.ml 854): `!x n. &0 < n ==> x rem n < n`. -/
  INT_LT_REM : thm
  /-- `INT_LT_REM_EQ` (int.ml 858):
      `!m n. m rem n < n <=> &0 < n \/ n = &0 /\ m < &0`. -/
  INT_LT_REM_EQ : thm
  deriving Inhabited

/-- Register the `int.ml` infix operators `div` and `rem` (int.ml 816-817),
    precedence 22 left-associative.  Mutates global parser state, so it must
    run once and before `setupIntDivMod`, which parses terms using `div`/`rem`. -/
def setupIntDivRemInfixes : IO Unit := do
  HolCore.Printer.parse_as_infix ("div", (22, "left"))
  HolCore.Printer.parse_as_infix ("rem", (22, "left"))

/-- int.ml 714-866.  Session runs `setupIntDivRemInfixes` first, so that `div`
    and `rem` parse as infixes.  `INT_ARITH` etc. are the first versions. -/
@[nospecialize]
def setupIntDivMod [HolBase] (A1 : IntArith1) (O : IntOps)
    (INT_POS INT_OF_NUM_MUL : thm)
    (INT_LE_TRANS INT_LE_REFL INT_LE_TOTAL : thm)
    (INT_MUL_LNEG : thm)
    (INT_MUL_RNEG INT_NEG_NEG INT_OF_NUM_EQ INT_NEG_EQ INT_OF_NUM_LE : thm)
    (INT_ABS_POS INT_ABS_MUL : thm)
    (INT_ADD_LID : thm)
    (INT_LE_LMUL INT_LET_TRANS : thm)
    (INT_LT_REFL : thm)
    (MULT_EQ_1 LE_REFL NOT_LE num_WOP : thm)
    (new_specification' : List String → thm → IO (Except String thm))
    (MESON' : List thm → term → IO (Except String thm))
    (MESON_TAC : List thm → tactic) (ASM_MESON_TAC : List thm → tactic) :
    ExceptT String IO IntDivMod := do
  let new_specification (l : List String) (th : thm) : ExceptT String IO thm :=
    new_specification' l th
  let MESON (ths : List thm) (t : term) : ExceptT String IO thm := MESON' ths t
  let INT_ARITH (t : term) : ExceptT String IO thm := A1.INT_ARITH1 t
  let INT_ARITH_TAC := A1.INT_ARITH_TAC1
  let ASM_INT_ARITH_TAC := A1.ASM_INT_ARITH_TAC1
  let { INT_FORALL_POS, .. } := A1
  let { INT_IMAGE, INT_LT_DISCRETE, .. } := O
  let { CONTRAPOS_THM, NOT_FORALL_THM, SKOLEM_THM, .. } := HolBase.C
  let { EXISTS_REFL, IMP_CONJ, LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM,
        MONO_EXISTS, MONO_FORALL, OR_EXISTS_THM, RIGHT_AND_EXISTS_THM,
        RIGHT_EXISTS_AND_THM, SWAP_EXISTS_THM, .. } := HolBase.T

  /- ---------------------------------------------------------------------- -/
  /- Some pseudo-definitions.                                               -/
  /- ---------------------------------------------------------------------- -/

  let INT_SUB ← INT_ARITH (← q r"!x y. x - y = x + --y")

  let INT_MAX ← INT_ARITH (← q r"!x y. max x y = if x <= y then y else x")

  let INT_MIN ← INT_ARITH (← q r"!x y. min x y = if x <= y then x else y")

  /- ---------------------------------------------------------------------- -/
  /- Additional useful lemmas.                                              -/
  /- ---------------------------------------------------------------------- -/

  let INT_OF_NUM_EXISTS ← prove
   r"!x:int. (?n. x = &n) <=> &0 <= x"
   (GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [INT_POS] THEN
    MP_TAC (← ISPEC (← q r"x:int") INT_IMAGE) THEN
    REWRITE_TAC [OR_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    ASM_INT_ARITH_TAC)

  let INT_LE_DISCRETE ← INT_ARITH (← q r"!x y:int. x <= y <=> x < y + &1")

  let INT_LE_TRANS_LE ← prove
   r"!x y:int. x <= y <=> (!z. y <= z ==> x <= z)"
   (MESON_TAC [INT_LE_TRANS, INT_LE_REFL])

  let INT_LE_TRANS_LT ← prove
   r"!x y:int. x <= y <=> (!z. y < z ==> x < z)"
   (REPEAT GEN_TAC THEN EQ_TAC THENL [INT_ARITH_TAC, ALL_TAC] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"y + &1:int")) THEN INT_ARITH_TAC)

  let INT_MUL_EQ_1 ← prove
   r"!x y:int. x * y = &1 <=> x = &1 /\ y = &1 \/ x = --(&1) /\ y = --(&1)"
   (REPEAT GEN_TAC THEN
    MP_TAC (← ISPEC (← q r"x:int") INT_IMAGE) THEN
    MP_TAC (← ISPEC (← q r"y:int") INT_IMAGE) THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [INT_MUL_LNEG, INT_MUL_RNEG, INT_NEG_NEG,
       ← INT_ARITH (← q r"~(--(&n:int) = &1)"), INT_OF_NUM_MUL,
       ← INT_ARITH (← q r"~(&n:int = -- &1)"), INT_OF_NUM_EQ, INT_NEG_EQ] THEN
    REWRITE_TAC [MULT_EQ_1])

  let INT_ABS_MUL_1 ← prove
   r"!x y. abs(x * y) = &1 <=> abs(x) = &1 /\ abs(y) = &1"
   (REPEAT GEN_TAC THEN REWRITE_TAC [INT_ABS_MUL] THEN
    MP_TAC (← SPEC (← q r"y:int") INT_ABS_POS) THEN SPEC_TAC ((← q r"abs(y)"), (← q r"b:int")) THEN
    MP_TAC (← SPEC (← q r"x:int") INT_ABS_POS) THEN SPEC_TAC ((← q r"abs(x)"), (← q r"a:int")) THEN
    REWRITE_TAC [← GSYM INT_FORALL_POS, INT_OF_NUM_MUL, INT_OF_NUM_EQ, MULT_EQ_1])

  let INT_WOP ← prove
   r"(?x. &0 <= x /\ P x) <=>
   (?x. &0 <= x /\ P x /\ !y. &0 <= y /\ P y ==> x <= y)"
   (ONCE_REWRITE_TAC [← MESON [] (← q r"(?x. P x /\ Q x) <=> ~(!x. P x ==> ~Q x)")] THEN
    REWRITE_TAC [IMP_CONJ, ← GSYM INT_FORALL_POS, INT_OF_NUM_LE] THEN
    REWRITE_TAC [NOT_FORALL_THM] THEN GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
    REWRITE_TAC [← GSYM NOT_LE, CONTRAPOS_THM])

  /- ---------------------------------------------------------------------- -/
  /- Archimedian property for the integers.                                 -/
  /- ---------------------------------------------------------------------- -/

  let INT_ARCH ← prove
   r"!x d. ~(d = &0) ==> ?c. x < c * d"
   (SUBGOAL_THEN (← q r"!x. &0 <= x ==> ?n. x <= &n") ASSUME_TAC THENL
     [REWRITE_TAC [← GSYM INT_FORALL_POS, INT_OF_NUM_LE] THEN MESON_TAC [LE_REFL],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!x. ?n. x <= &n") ASSUME_TAC THENL
     [ASM_MESON_TAC [INT_LE_TOTAL], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!x d. &0 < d ==> ?c. x < c * d") ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC [INT_LT_DISCRETE, INT_ADD_LID] THEN
      ASM_MESON_TAC [INT_POS, INT_LE_LMUL, ← INT_ARITH
          (← q r"x + &1 <= &n /\ &n * &1 <= &n * d ==> x + &1 <= &n * d")],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!x d. ~(d = &0) ==> ?c. x < c * d") ASSUME_TAC THENL
     [ASM_MESON_TAC [← INT_ARITH (← q r"--x * y = x * --y"),
                     ← INT_ARITH (← q r"~(d = &0) ==> &0 < d \/ &0 < --d")],
      ALL_TAC] THEN
    ASM_MESON_TAC [← INT_ARITH (← q r"--x * y = x * --y"),
                   ← INT_ARITH (← q r"~(d = &0) ==> &0 < d \/ &0 < --d")])

  /- ---------------------------------------------------------------------- -/
  /- Definitions of ("Euclidean") integer division and remainder.           -/
  /- ---------------------------------------------------------------------- -/

  let INT_DIVMOD_EXIST_0 ← prove
   r"!m n:int. ?q r. if n = &0 then q = &0 /\ r = m
                   else &0 <= r /\ r < abs(n) /\ m = q * n + r"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n = &0") THEN
    ASM_REWRITE_TAC [RIGHT_EXISTS_AND_THM, EXISTS_REFL] THEN
    GEN_REWRITE_TAC I [SWAP_EXISTS_THM] THEN
    SUBGOAL_THEN (← q r"?r. &0 <= r /\ ?q:int. m = n * q + r") MP_TAC THENL
     [FIRST_ASSUM (MP_TAC o SPEC (← q r"--m:int") o MATCH_MP INT_ARCH) THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"s:int")) THEN
      EXISTS_TAC (← q r"m + s * n:int") THEN CONJ_TAC THENL
       [ASM_INT_ARITH_TAC, EXISTS_TAC (← q r"--s:int") THEN INT_ARITH_TAC],
      GEN_REWRITE_TAC LAND_CONV [INT_WOP] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"r:int") THEN
      REWRITE_TAC [LEFT_AND_EXISTS_THM, RIGHT_AND_EXISTS_THM] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"q:int") THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MP_TAC o SPEC (← q r"r - abs n")) THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"if &0 <= n then q + &1 else q - &1")) THEN
      ASM_INT_ARITH_TAC])

  -- (parse_as_infix("div",(22,"left")) and "rem": setupIntDivRemInfixes.)

  let INT_DIVISION_0 ← new_specification ["div", "rem"]
    (← REWRITE_RULE [SKOLEM_THM] INT_DIVMOD_EXIST_0)

  let INT_DIVISION ← prove
   r"!m n. ~(n = &0)
         ==> m = m div n * n + m rem n /\ &0 <= m rem n /\ m rem n < abs n"
   (MESON_TAC [INT_DIVISION_0])

  let INT_DIVISION_SIMP ← prove
   r"!m n. m div n * n + m rem n = m"
   (MP_TAC INT_DIVISION_0 THEN REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [] THEN CONV_TAC A1.INT_ARITH1)

  let INT_REM_POS ← prove
   r"!a b. ~(b = &0) ==> &0 <= a rem b"
   (MESON_TAC [INT_DIVISION])

  let INT_DIV_0 ← prove
   r"!m. m div &0 = &0"
   (MESON_TAC [INT_DIVISION_0])

  let INT_REM_0 ← prove
   r"!m. m rem &0 = m"
   (MESON_TAC [INT_DIVISION_0])

  let INT_REM_POS_EQ ← prove
   r"!m n. &0 <= m rem n <=> n = &0 ==> &0 <= m"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n:int = &0") THEN
    ASM_SIMP_TAC [INT_REM_0, INT_REM_POS])

  let INT_REM_DIV ← prove
   r"!m n. m rem n = m - m div n * n"
   (REWRITE_TAC [← INT_ARITH (← q r"a:int = b - c <=> c + a = b")] THEN
    REWRITE_TAC [INT_DIVISION_SIMP])

  let INT_LT_REM ← prove
   r"!x n. &0 < n ==> x rem n < n"
   (MESON_TAC [INT_DIVISION, INT_LT_REFL, ← INT_ARITH (← q r"&0:int < n ==> abs n = n")])

  let INT_LT_REM_EQ ← prove
   r"!m n. m rem n < n <=> &0 < n \/ n = &0 /\ m < &0"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n:int = &0") THEN
    ASM_SIMP_TAC [INT_REM_0, INT_LT_REFL] THEN
    EQ_TAC THEN REWRITE_TAC [INT_LT_REM] THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] INT_LET_TRANS) THEN
    ASM_SIMP_TAC [INT_REM_POS])

  return { INT_SUB, INT_MAX, INT_MIN, INT_OF_NUM_EXISTS, INT_LE_DISCRETE,
           INT_LE_TRANS_LE, INT_LE_TRANS_LT, INT_MUL_EQ_1, INT_ABS_MUL_1,
           INT_WOP, INT_ARCH, INT_DIVMOD_EXIST_0, INT_DIVISION_0,
           INT_DIVISION, INT_DIVISION_SIMP, INT_REM_POS, INT_DIV_0, INT_REM_0,
           INT_REM_POS_EQ, INT_REM_DIV, INT_LT_REM, INT_LT_REM_EQ }

/- ---------------------------------------------------------------------- -/
/- Arithmetic operations on integers. Essentially a clone of stuff for    -/
/- reals in the file "calc_int.ml", except for div and rem, which are more -/
/- like N.                                                                -/
/- ---------------------------------------------------------------------- -/

structure IntCompareConvs where
  INT_LE_CONV : ioconv
  INT_LT_CONV : ioconv
  INT_GE_CONV : ioconv
  INT_GT_CONV : ioconv
  INT_EQ_CONV : ioconv
  deriving Inhabited

/-- `let INT_LE_CONV,INT_LT_CONV,INT_GE_CONV,INT_GT_CONV,INT_EQ_CONV = ...`
    (int.ml 871-940). -/
@[nospecialize]
def setupIntCompareConvs [HolBase]
    (NUM_EQ_CONV NUM_LE_CONV NUM_LT_CONV : ioconv)
    (A1 : IntArith1)
    (INT_LE_NEG2 INT_LE_LNEG INT_LE_RNEG : thm)
    (INT_OF_NUM_ADD INT_OF_NUM_LE : thm)
    (INT_LE_ANTISYM : thm)
    (LE LE_0 ADD_EQ_0 NOT_LE LE_ANTISYM : thm) :
    ExceptT String IO IntCompareConvs := do
  let { INT_LT, INT_GE, INT_GT, .. } := A1
  let tth ← TAUT (← q r"(F /\ F <=> F) /\ (F /\ T <=> F) /\
          (T /\ F <=> F) /\ (T /\ T <=> T)")
  let nth ← TAUT (← q r"(~T <=> F) /\ (~F <=> T)")
  let NUM2_EQ_CONV := BINOP_CONV NUM_EQ_CONV THENC (← GEN_REWRITE_CONV_NET I [tth])
  let NUM2_NE_CONV :=
    RAND_CONV NUM2_EQ_CONV THENC
    (← GEN_REWRITE_CONV_NET I [nth])
  let [pth_le1, pth_le2a, pth_le2b, pth_le3] := CONJUNCTS (← prove
   r"(--(&m) <= &n <=> T) /\
     (&m <= &n <=> m <= n) /\
     (--(&m) <= --(&n) <=> n <= m) /\
     (&m <= --(&n) <=> (m = 0) /\ (n = 0))"
    (REWRITE_TAC [INT_LE_NEG2] THEN
     REWRITE_TAC [INT_LE_LNEG, INT_LE_RNEG] THEN
     REWRITE_TAC [INT_OF_NUM_ADD, INT_OF_NUM_LE, LE_0] THEN
     REWRITE_TAC [LE, ADD_EQ_0])) | throw "pth_le"
  let INT_LE_CONV := FIRST_CONV
   [(← GEN_REWRITE_CONV_NET I [pth_le1]),
    (← GEN_REWRITE_CONV_NET I [pth_le2a, pth_le2b]) THENC NUM_LE_CONV,
    (← GEN_REWRITE_CONV_NET I [pth_le3]) THENC NUM2_EQ_CONV]
  let [pth_lt1, pth_lt2a, pth_lt2b, pth_lt3] := CONJUNCTS (← prove
   r"(&m < --(&n) <=> F) /\
     (&m < &n <=> m < n) /\
     (--(&m) < --(&n) <=> n < m) /\
     (--(&m) < &n <=> ~((m = 0) /\ (n = 0)))"
    (REWRITE_TAC [pth_le1, pth_le2a, pth_le2b, pth_le3,
                  ← GSYM NOT_LE, INT_LT] THEN
     CONV_TAC TAUT)) | throw "pth_lt"
  let INT_LT_CONV := FIRST_CONV
   [(← GEN_REWRITE_CONV_NET I [pth_lt1]),
    (← GEN_REWRITE_CONV_NET I [pth_lt2a, pth_lt2b]) THENC NUM_LT_CONV,
    (← GEN_REWRITE_CONV_NET I [pth_lt3]) THENC NUM2_NE_CONV]
  let [pth_ge1, pth_ge2a, pth_ge2b, pth_ge3] := CONJUNCTS (← prove
   r"(&m >= --(&n) <=> T) /\
     (&m >= &n <=> n <= m) /\
     (--(&m) >= --(&n) <=> m <= n) /\
     (--(&m) >= &n <=> (m = 0) /\ (n = 0))"
    (REWRITE_TAC [pth_le1, pth_le2a, pth_le2b, pth_le3, INT_GE] THEN
     CONV_TAC TAUT)) | throw "pth_ge"
  let INT_GE_CONV := FIRST_CONV
   [(← GEN_REWRITE_CONV_NET I [pth_ge1]),
    (← GEN_REWRITE_CONV_NET I [pth_ge2a, pth_ge2b]) THENC NUM_LE_CONV,
    (← GEN_REWRITE_CONV_NET I [pth_ge3]) THENC NUM2_EQ_CONV]
  let [pth_gt1, pth_gt2a, pth_gt2b, pth_gt3] := CONJUNCTS (← prove
   r"(--(&m) > &n <=> F) /\
     (&m > &n <=> n < m) /\
     (--(&m) > --(&n) <=> m < n) /\
     (&m > --(&n) <=> ~((m = 0) /\ (n = 0)))"
    (REWRITE_TAC [pth_lt1, pth_lt2a, pth_lt2b, pth_lt3, INT_GT] THEN
     CONV_TAC TAUT)) | throw "pth_gt"
  let INT_GT_CONV := FIRST_CONV
   [(← GEN_REWRITE_CONV_NET I [pth_gt1]),
    (← GEN_REWRITE_CONV_NET I [pth_gt2a, pth_gt2b]) THENC NUM_LT_CONV,
    (← GEN_REWRITE_CONV_NET I [pth_gt3]) THENC NUM2_NE_CONV]
  let [pth_eq1a, pth_eq1b, pth_eq2a, pth_eq2b] := CONJUNCTS (← prove
   r"((&m = &n) <=> (m = n)) /\
     ((--(&m) = --(&n)) <=> (m = n)) /\
     ((--(&m) = &n) <=> (m = 0) /\ (n = 0)) /\
     ((&m = --(&n)) <=> (m = 0) /\ (n = 0))"
    (REWRITE_TAC [← GSYM INT_LE_ANTISYM, ← GSYM LE_ANTISYM] THEN
     REWRITE_TAC [pth_le1, pth_le2a, pth_le2b, pth_le3, LE, LE_0] THEN
     CONV_TAC TAUT)) | throw "pth_eq"
  let INT_EQ_CONV := FIRST_CONV
   [(← GEN_REWRITE_CONV_NET I [pth_eq1a, pth_eq1b]) THENC NUM_EQ_CONV,
    (← GEN_REWRITE_CONV_NET I [pth_eq2a, pth_eq2b]) THENC NUM2_EQ_CONV]
  return { INT_LE_CONV, INT_LT_CONV, INT_GE_CONV, INT_GT_CONV, INT_EQ_CONV }

structure IntArithConvs where
  INT_NEG_CONV : ioconv
  INT_MUL_CONV : ioconv
  INT_ADD_CONV : ioconv
  INT_SUB_CONV : ioconv
  INT_POW_CONV : ioconv
  INT_ABS_CONV : ioconv
  INT_MAX_CONV : ioconv
  INT_MIN_CONV : ioconv
  INT_SGN_CONV : ioconv
  deriving Inhabited

/-- int.ml 941-1087, `INT_NEG_CONV` to `INT_SGN_CONV`. -/
@[nospecialize]
def setupIntArithConvs [HolBase]
    (V : IntCompareConvs)
    (NUM_MULT_CONV NUM_ADD_CONV NUM_EXP_CONV NUM_EVEN_CONV : ioconv)
    (mk_numeral : Rat → Except String term)
    (INT_NEG_NEG INT_NEG_0 : thm)
    (INT_MUL_LZERO INT_MUL_RZERO INT_MUL_LNEG INT_MUL_RNEG : thm)
    (INT_ADD_LINV INT_ADD_RINV INT_NEG_ADD INT_ADD_LID : thm)
    (INT_ADD_ASSOC INT_ADD_SYM : thm)
    (INT_OF_NUM_MUL INT_OF_NUM_ADD INT_OF_NUM_POW INT_POW_NEG : thm)
    (INT_ABS_NEG INT_ABS_NUM : thm)
    (INT_SUB INT_MAX INT_MIN INT_SGN : thm) :
    ExceptT String IO IntArithConvs := do
  let { INT_LE_CONV, INT_LT_CONV, .. } := V
  let { COND_CLAUSES, .. } := HolBase.C

  let INT_NEG_CONV ← GEN_REWRITE_CONV_NET I [← prove
   r"(--(&0) = &0) /\
     (--(--(&x)) = &x)"
    (REWRITE_TAC [INT_NEG_NEG, INT_NEG_0])]

  let INT_MUL_CONV ← do
    let pth0 ← prove
     r"(&0 * &x = &0) /\
       (&0 * --(&x) = &0) /\
       (&x * &0 = &0) /\
       (--(&x) * &0 = &0)"
      (REWRITE_TAC [INT_MUL_LZERO, INT_MUL_RZERO])
    let (pth1, pth2) ← CONJ_PAIR (← prove
     r"((&m * &n = &(m * n)) /\
        (--(&m) * --(&n) = &(m * n))) /\
       ((--(&m) * &n = --(&(m * n))) /\
        (&m * --(&n) = --(&(m * n))))"
      (REWRITE_TAC [INT_MUL_LNEG, INT_MUL_RNEG, INT_NEG_NEG] THEN
       REWRITE_TAC [INT_OF_NUM_MUL]))
    pure (FIRST_CONV
     [(← GEN_REWRITE_CONV_NET I [pth0]),
      (← GEN_REWRITE_CONV_NET I [pth1]) THENC RAND_CONV NUM_MULT_CONV,
      (← GEN_REWRITE_CONV_NET I [pth2]) THENC RAND_CONV (RAND_CONV NUM_MULT_CONV)])

  let INT_ADD_CONV ← do
    let neg_tm ← q r"(--)"
    let amp_tm ← q r"(&)"
    let add_tm ← q r"(+)"
    let dest := dest_binop add_tm
    let m_tm ← q r"m:num"
    let n_tm ← q r"n:num"
    let pth0 ← prove
     r"(--(&m) + &m = &0) /\
       (&m + --(&m) = &0)"
      (REWRITE_TAC [INT_ADD_LINV, INT_ADD_RINV])
    let [pth1, pth2, pth3, pth4, pth5, pth6] := CONJUNCTS (← prove
     r"(--(&m) + --(&n) = --(&(m + n))) /\
       (--(&m) + &(m + n) = &n) /\
       (--(&(m + n)) + &m = --(&n)) /\
       (&(m + n) + --(&m) = &n) /\
       (&m + --(&(m + n)) = --(&n)) /\
       (&m + &n = &(m + n))"
      (REWRITE_TAC [← GSYM INT_OF_NUM_ADD, INT_NEG_ADD] THEN
       REWRITE_TAC [INT_ADD_ASSOC, INT_ADD_LINV, INT_ADD_LID] THEN
       REWRITE_TAC [INT_ADD_RINV, INT_ADD_LID] THEN
       ONCE_REWRITE_TAC [INT_ADD_SYM] THEN
       REWRITE_TAC [INT_ADD_ASSOC, INT_ADD_LINV, INT_ADD_LID] THEN
       REWRITE_TAC [INT_ADD_RINV, INT_ADD_LID])) | throw "pth_add"
    let conv (tm : term) : ExceptT String IO thm := do
      let (l, r) ← dest tm
      if !(is_intconst l) || !(is_intconst r) then throw ""
      else if (← rator l) == neg_tm then
        if (← rator r) == neg_tm then
          let th1 ← INST [(← rand (← rand l), m_tm), (← rand (← rand r), n_tm)] pth1
          let tm1 ← rand (← rand (← rand (concl th1)))
          let th2 ← AP_TERM neg_tm (← AP_TERM amp_tm (← NUM_ADD_CONV tm1))
          TRANS th1 th2
        else
          let m ← rand (← rand l)
          let n ← rand r
          let m' ← dest_numeral m
          let n' ← dest_numeral n
          if m' <= n' then
            let p ← mk_numeral (n' - m')
            let th1 ← INST [(m, m_tm), (p, n_tm)] pth2
            let th2 ← NUM_ADD_CONV (← rand (← rand (← lhand (concl th1))))
            let th3 ← AP_TERM (← rator tm) (← AP_TERM amp_tm (← SYM th2))
            TRANS th3 th1
          else
            let p ← mk_numeral (m' - n')
            let th1 ← INST [(n, m_tm), (p, n_tm)] pth3
            let th2 ← NUM_ADD_CONV (← rand (← rand (← lhand (← lhand (concl th1)))))
            let th3 ← AP_TERM neg_tm (← AP_TERM amp_tm (← SYM th2))
            let th4 ← AP_THM (← AP_TERM add_tm th3) (← rand tm)
            TRANS th4 th1
      else
        if (← rator r) == neg_tm then
          let m ← rand l
          let n ← rand (← rand r)
          let m' ← dest_numeral m
          let n' ← dest_numeral n
          if n' <= m' then
            let p ← mk_numeral (m' - n')
            let th1 ← INST [(n, m_tm), (p, n_tm)] pth4
            let th2 ← NUM_ADD_CONV (← rand (← lhand (← lhand (concl th1))))
            let th3 ← AP_TERM add_tm (← AP_TERM amp_tm (← SYM th2))
            let th4 ← AP_THM th3 (← rand tm)
            TRANS th4 th1
          else
            let p ← mk_numeral (n' - m')
            let th1 ← INST [(m, m_tm), (p, n_tm)] pth5
            let th2 ← NUM_ADD_CONV (← rand (← rand (← rand (← lhand (concl th1)))))
            let th3 ← AP_TERM neg_tm (← AP_TERM amp_tm (← SYM th2))
            let th4 ← AP_TERM (← rator tm) th3
            TRANS th4 th1
        else
          let th1 ← INST [(← rand l, m_tm), (← rand r, n_tm)] pth6
          let tm1 ← rand (← rand (concl th1))
          let th2 ← AP_TERM amp_tm (← NUM_ADD_CONV tm1)
          TRANS th1 th2
    pure ((← GEN_REWRITE_CONV_NET I [pth0]) ORELSEC
      (fun tm => (tryCatch (conv tm) (fun _ => throw "INT_ADD_CONV") : ExceptT String IO thm)))

  let INT_SUB_CONV :=
    (← GEN_REWRITE_CONV_NET I [INT_SUB]) THENC
    TRY_CONV (RAND_CONV INT_NEG_CONV) THENC
    INT_ADD_CONV

  let INT_POW_CONV ← do
    let (pth1, pth2) ← CONJ_PAIR (← prove
     r"(&x pow n = &(x EXP n)) /\
       ((--(&x)) pow n = if EVEN n then &(x EXP n) else --(&(x EXP n)))"
      (REWRITE_TAC [INT_OF_NUM_POW, INT_POW_NEG]))
    let tth ← prove
     r"((if T then x:int else y) = x) /\ ((if F then x:int else y) = y)"
      (REWRITE_TAC [])
    let neg_tm ← q r"(--)"
    pure (((← GEN_REWRITE_CONV_NET I [pth1]) THENC RAND_CONV NUM_EXP_CONV) ORELSEC
      ((← GEN_REWRITE_CONV_NET I [pth2]) THENC
       RATOR_CONV (RATOR_CONV (RAND_CONV NUM_EVEN_CONV)) THENC
       (← GEN_REWRITE_CONV_NET I [tth]) THENC
       (fun tm => ExceptT.run do
          if (← rator tm) == neg_tm then RAND_CONV (RAND_CONV NUM_EXP_CONV) tm
          else RAND_CONV NUM_EXP_CONV tm)))

  let INT_ABS_CONV ← GEN_REWRITE_CONV_NET I [← prove
   r"(abs(--(&x)) = &x) /\
     (abs(&x) = &x)"
    (REWRITE_TAC [INT_ABS_NEG, INT_ABS_NUM])]

  let INT_MAX_CONV :=
    REWR_CONV INT_MAX THENC
    RATOR_CONV (RATOR_CONV (RAND_CONV INT_LE_CONV)) THENC
    (← GEN_REWRITE_CONV_NET I [COND_CLAUSES])

  let INT_MIN_CONV :=
    REWR_CONV INT_MIN THENC
    RATOR_CONV (RATOR_CONV (RAND_CONV INT_LE_CONV)) THENC
    (← GEN_REWRITE_CONV_NET I [COND_CLAUSES])

  let INT_SGN_CONV :=
    (← GEN_REWRITE_CONV_NET I [INT_SGN]) THENC
    RATOR_CONV (LAND_CONV INT_LT_CONV) THENC
    ((← GEN_REWRITE_CONV_NET I [← CONJUNCT1 (← SPEC_ALL COND_CLAUSES)]) ORELSEC
     ((← GEN_REWRITE_CONV_NET I [← CONJUNCT2 (← SPEC_ALL COND_CLAUSES)]) THENC
      RATOR_CONV (LAND_CONV INT_LT_CONV) THENC
      (← GEN_REWRITE_CONV_NET I [COND_CLAUSES])))

  return { INT_NEG_CONV, INT_MUL_CONV, INT_ADD_CONV, INT_SUB_CONV,
           INT_POW_CONV, INT_ABS_CONV, INT_MAX_CONV, INT_MIN_CONV,
           INT_SGN_CONV }

/- ---------------------------------------------------------------------- -/
/- Instantiate the normalizer.                                            -/
/- ---------------------------------------------------------------------- -/

structure IntPolyConvs where
  INT_POLY_CONV : ioconv
  deriving Inhabited

/-- `INT_POLY_CONV` (int.ml 1090-1119).  `INT_POW` and `INT_ARITH_TAC` are the
    first versions; OCaml's polymorphic `(<)` is `RealArith.term_lt`.
    `setupSemiringCtx` takes the natural-number pieces that
    `SEMIRING_NORMALIZERS_CONV` uses internally. -/
@[nospecialize]
def setupIntPolyConvs [HolBase]
    (A1 : IntArith1)
    (Ar : IntArithConvs)
    (TRUTH SEMIRING_PTHS : thm)
    (num_CONV : term → IO (Except String thm))
    (NUM_ADD_CONV NUM_SUC_CONV NUM_MULT_CONV : ioconv) :
    ExceptT String IO IntPolyConvs := do
  let { INT_POW, INT_ARITH_TAC1 := INT_ARITH_TAC, .. } := A1
  let sth ← prove
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
    (REWRITE_TAC [INT_POW] THEN INT_ARITH_TAC)
  let rth ← prove
   r"(!x. --x = --(&1) * x) /\
     (!x y. x - y = x + --(&1) * y)"
    INT_ARITH_TAC
  let is_semiring_constant := is_intconst
  let SEMIRING_ADD_CONV := Ar.INT_ADD_CONV
  let SEMIRING_MUL_CONV := Ar.INT_MUL_CONV
  let SEMIRING_POW_CONV := Ar.INT_POW_CONV
  let sctx ← HolMath.Normalizer.setupSemiringCtx TRUTH SEMIRING_PTHS
               sth rth
               is_semiring_constant
               SEMIRING_ADD_CONV SEMIRING_MUL_CONV SEMIRING_POW_CONV
               HolMath.RealArith.term_lt
  -- `let _,_,_,_,_,INT_POLY_CONV = SEMIRING_NORMALIZERS_CONV ...`
  let INT_POLY_CONV := (HolMath.Normalizer.SEMIRING_NORMALIZERS_CONV sctx
                 NUM_ADD_CONV NUM_SUC_CONV NUM_MULT_CONV num_CONV).POLYNOMIAL_CONV
  return { INT_POLY_CONV }

/- ---------------------------------------------------------------------- -/
/- Instantiate the ring and ideal procedures.                             -/
/- ---------------------------------------------------------------------- -/

structure IntRingConvs where
  /-- `INT_RING` (int.ml 1134). -/
  INT_RING : term → IO (Except String thm)
  /-- `int_ideal_cofactors` (int.ml 1141). -/
  int_ideal_cofactors : List term → term → IO (Except String (List term))
  /-- `INT_INTEGRAL` (int.ml 1123), kept for later sections. -/
  INT_INTEGRAL : thm

/-- `let INT_RING,int_ideal_cofactors = ...` (int.ml 1122-1147).  The port
    has no `RING_AND_IDEAL_CONV`: its two halves are `Grobner.RING'` and
    `Grobner.ideal_cofactors` over one `RingParms`, and the pieces
    RING_AND_IDEAL_CONV builds internally (INITIAL_CONV, REFUTE, FINAL_RULE)
    are built here.  The integers have no inverse or division, hence the two
    `genvar bool_ty` dummies, and `TRUTH` in the Rabinowitsch slot. -/
@[nospecialize]
def setupIntRing [HolBase]
    (Ics : IntConstSyntax)
    (V : IntCompareConvs)
    (A1 : IntArith1)
    (Pc : IntPolyConvs)
    (Nm : HolMath.Nums.NumeralConsts)
    (MULT_CLAUSES EQ_ADD_LCANCEL
     INT_OF_NUM_EQ INT_OF_NUM_ADD INT_OF_NUM_MUL
     INT_SUB_0 INT_ENTIRE : thm)
    (PRESIMP_CONV CONDS_ELIM_CONV NNF_CONV WEAK_DNF_CONV : ioconv)
    (AND_FORALL_THM LEFT_AND_FORALL_THM RIGHT_AND_FORALL_THM
     LEFT_OR_FORALL_THM RIGHT_OR_FORALL_THM OR_EXISTS_THM
     LEFT_OR_EXISTS_THM RIGHT_OR_EXISTS_THM LEFT_AND_EXISTS_THM
     RIGHT_AND_EXISTS_THM : thm)
    (G : HolMath.Grobner.GrobnerGlobals) (TRUTH : thm) :
    ExceptT String IO IntRingConvs := do
  let INT_INTEGRAL ← prove
   r"(!x. &0 * x = &0) /\
     (!x y z. (x + y = x + z) <=> (y = z)) /\
     (!w x y z. (w * y + x * z = w * z + x * y) <=> (w = x) \/ (y = z))"
    (REWRITE_TAC [MULT_CLAUSES, EQ_ADD_LCANCEL] THEN
     REWRITE_TAC [← GSYM INT_OF_NUM_EQ,
                  ← GSYM INT_OF_NUM_ADD, ← GSYM INT_OF_NUM_MUL] THEN
     ONCE_REWRITE_TAC [← GSYM INT_SUB_0] THEN
     REWRITE_TAC [← GSYM INT_ENTIRE] THEN A1.INT_ARITH_TAC1)
  let int_ty ← qty r"int"
  -- The tuple's components, right to left as OCaml evaluates them.
  let pow_tm ← q r"(pow):int->num->int"
  let div_dummy ← liftM (genvar bool_ty : IO term)
  let mul_tm ← q r"(*):int->int->int"
  let inv_dummy ← liftM (genvar bool_ty : IO term)
  let sub_tm ← q r"(-):int->int->int"
  let add_tm ← q r"(+):int->int->int"
  let neg_tm ← q r"(--):int->int"
  let K : HolMath.Grobner.RingParms :=
    { ring_dest_const     := dest_intconst
      ring_mk_const       := mk_intconst Ics
      RING_EQ_CONV        := V.INT_EQ_CONV
      ring_neg_tm         := neg_tm
      ring_add_tm         := add_tm
      ring_sub_tm         := sub_tm
      ring_inv_tm         := inv_dummy
      ring_mul_tm         := mul_tm
      ring_div_tm         := div_dummy
      ring_pow_tm         := pow_tm
      RING_INTEGRAL       := INT_INTEGRAL
      RABINOWITSCH_THM    := TRUTH
      RING_NORMALIZE_CONV := Pc.INT_POLY_CONV }
  -- What RING_AND_IDEAL_CONV builds from the parameters (grobner.ml 336-617).
  let R ← HolMath.Grobner.setupRingCtx G Nm (concl TRUTH)
            PRESIMP_CONV CONDS_ELIM_CONV NNF_CONV WEAK_DNF_CONV
            AND_FORALL_THM LEFT_AND_FORALL_THM RIGHT_AND_FORALL_THM
            LEFT_OR_FORALL_THM RIGHT_OR_FORALL_THM OR_EXISTS_THM
            LEFT_OR_EXISTS_THM RIGHT_OR_EXISTS_THM
            LEFT_AND_EXISTS_THM RIGHT_AND_EXISTS_THM K
  -- `let pure,ideal = RING_AND_IDEAL_CONV (...)`
  let pure_ := HolMath.Grobner.RING' R
  let ideal := HolMath.Grobner.ideal_cofactors R
  return { INT_RING := pure_,
           int_ideal_cofactors := fun tms tm =>
             if (tm :: tms).all (fun t => type_of t == int_ty)
             then ideal tms tm
             else pure (.error "int_ideal_cofactors: not all terms have type :int"),
           INT_INTEGRAL }

/- ---------------------------------------------------------------------- -/
/- Set up overloading so we can use same symbols for N, Z and even R.     -/
/- ---------------------------------------------------------------------- -/

/-- int.ml 1148-1219.  Parser changes and definitions, interleaved in
    int.ml's order: each `overload_interface` runs before the definition
    whose statement uses the symbol. -/
structure IntDivisibility where
  /-- `cong` (int.ml 1163): `(x == y) (rel:A->A->bool) <=> rel x y`. -/
  cong : thm
  /-- `real_mod` (int.ml 1170): `real_mod n (x:real) y = ?q. integer q /\ x - y = q * n`. -/
  real_mod : thm
  /-- `int_divides` (int.ml 1182): `a divides b <=> ?x:int. b = a * x`. -/
  int_divides : thm
  /-- `INT_DIVIDES_LE` (int.ml 1185). -/
  INT_DIVIDES_LE : thm
  /-- `int_mod` (int.ml 1199): `(mod n) x y = n divides (x - y)`. -/
  int_mod : thm
  /-- `int_congruent` (int.ml 1202). -/
  int_congruent : thm
  /-- `INT_CONG_IMP_EQ` (int.ml 1206). -/
  INT_CONG_IMP_EQ : thm
  /-- `int_coprime` (int.ml 1218): `coprime(a,b) <=> ?x y. a * x + b * y = &1`. -/
  int_coprime : thm

@[nospecialize]
def setupIntDivisibility [HolBase]
    (A1 : IntArith1)
    (INT_ABS_MUL INT_ENTIRE INT_LE_MUL : thm)
    (make_overloadable' : String → hol_type → IO (Except String Unit))
    (overload_interface' : String → term → IO (Except String Unit))
    (parse_as_infix : String × (Int × String) → IO Unit)
    (parse_as_prefix : String → IO Unit)
    (new_definition' : term → IO (Except String thm)) :
    ExceptT String IO IntDivisibility := do
  let make_overloadable (s : String) (ty : hol_type) : ExceptT String IO Unit :=
    make_overloadable' s ty
  let overload_interface (s : String) (t : term) : ExceptT String IO Unit :=
    overload_interface' s t
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let INT_ARITH (t : term) : ExceptT String IO thm := A1.INT_ARITH1 t
  let ASM_INT_ARITH_TAC := A1.ASM_INT_ARITH_TAC1
  let { LEFT_IMP_EXISTS_THM, .. } := HolBase.T

  make_overloadable "divides" (← qty r"A->A->bool")
  make_overloadable "mod" (← qty r"A->A->A->bool")
  make_overloadable "coprime" (← qty r"A#A->bool")
  make_overloadable "gcd" (← qty r"A#A->A")
  make_overloadable "lcm" (← qty r"A#A->A")

  /- ---------------------------------------------------------------------- -/
  /- The general notion of congruence: just syntax for equivalence relation.-/
  /- ---------------------------------------------------------------------- -/

  parse_as_infix ("==", (10, "right"))

  let cong ← new_definition
    r"(x == y) (rel:A->A->bool) <=> rel x y"

  /- ---------------------------------------------------------------------- -/
  /- Get real moduli defined and out of the way first.                      -/
  /- ---------------------------------------------------------------------- -/

  let real_mod ← new_definition
    r"real_mod n (x:real) y = ?q. integer q /\ x - y = q * n"

  overload_interface "mod" (← q r"real_mod")

  /- ---------------------------------------------------------------------- -/
  /- Integer divisibility.                                                  -/
  /- ---------------------------------------------------------------------- -/

  parse_as_infix ("divides", (12, "right"))
  overload_interface "divides" (← q r"int_divides:int->int->bool")

  let int_divides ← new_definition
    r"a divides b <=> ?x:int. b = a * x"

  let INT_DIVIDES_LE ← prove
   r"!x y:int. x divides y ==> abs(x) <= abs(y) \/ y = &0"
   (← do
    let i1 ← INT_ARITH (← q r"x:int <= x * y <=> &0 <= x * (y - &1)")
    let t1 ← TAUT (← q r"p \/ q \/ r <=> ~q /\ ~r ==> p")
    pure
     (SIMP_TAC [int_divides, LEFT_IMP_EXISTS_THM, INT_ABS_MUL, INT_ENTIRE] THEN
      REWRITE_TAC [t1] THEN
      REWRITE_TAC [i1] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_LE_MUL THEN ASM_INT_ARITH_TAC))

  /- ---------------------------------------------------------------------- -/
  /- Integer congruences.                                                   -/
  /- ---------------------------------------------------------------------- -/

  parse_as_prefix "mod"
  overload_interface "mod" (← q r"int_mod:int->int->int->bool")

  let int_mod ← new_definition
    r"(mod n) x y = n divides (x - y)"

  let int_congruent ← prove
   r"!x y n. (x == y) (mod n) <=> ?d. x - y = n * d"
   (REWRITE_TAC [int_mod, cong, int_divides])

  let INT_CONG_IMP_EQ ← prove
   r"!x y n:int. abs(x - y) < n /\ (x == y) (mod n) ==> x = y"
   (REWRITE_TAC [int_congruent, ← GSYM int_divides] THEN
    REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN
    ASM_INT_ARITH_TAC)

  /- ---------------------------------------------------------------------- -/
  /- Integer coprimality.                                                   -/
  /- ---------------------------------------------------------------------- -/

  overload_interface "coprime" (← q r"int_coprime:int#int->bool")

  let int_coprime ← new_definition
    r"!a b. coprime(a,b) <=> ?x y. a * x + b * y = &1"

  return { cong, real_mod, int_divides, INT_DIVIDES_LE, int_mod,
           int_congruent, INT_CONG_IMP_EQ, int_coprime }

/- ---------------------------------------------------------------------- -/
/- A tactic for simple divisibility/congruence/coprimality goals.         -/
/- ---------------------------------------------------------------------- -/

/-- `let rec GENVAR_EXISTS_CONV tm = ...` inside INTEGER_TAC (int.ml 1301). -/
private partial def genvarExistsConv : ioconv := fun tm => ExceptT.run do
  if !(is_exists tm) then pure (REFL tm) else
  let (ev, _bod) ← dest_exists tm
  let gv ← liftM (genvar (type_of ev) : IO term)
  ((fun t => pure (HolCore.Equal.GEN_ALPHA_CONV gv t)) THENC
   BINDER_CONV genvarExistsConv) tm

/-- `let rec solve_idealism evs ps eqs = ...` inside INTEGER_TAC (int.ml 1294),
    over its closures `isolate_variables` and `subst_in_poly`. -/
private partial def solveIdealism
    (isolate_variables : List term → List term → term →
      ExceptT String IO (term × List (term × term)))
    (subst_in_poly : List (term × term) → term → ExceptT String IO term)
    (evs ps eqs : List term) : ExceptT String IO (List (term × term)) := do
  if evs.isEmpty then pure [] else
  let (eq, cfs) ← (tryfindM (isolate_variables evs ps) eqs : ExceptT String IO _)
  let evs' := subtract evs (cfs.map Prod.snd)
  let eqs' ← (subtract eqs [eq]).mapM (subst_in_poly cfs)
  pure (cfs ++ (← solveIdealism isolate_variables subst_in_poly evs' ps eqs'))

/-- `INTEGER_TAC` and `INTEGER_RULE` (int.ml 1224-1327), the first versions:
    int.ml 2045 and 2064 define them again, to eliminate gcd and lcm. -/
structure IntTac1 where
  /-- `INTEGER_TAC` (int.ml 1224), first of two. -/
  INTEGER_TAC1 : tactic
  /-- `INTEGER_RULE` (int.ml 1327), first of two. -/
  INTEGER_RULE1 : term → IO (Except String thm)
  deriving Inhabited

@[nospecialize]
def setupIntTac1 [HolBase]
    (A1 : IntArith1)
    (Pc : IntPolyConvs)
    (Rg : IntRingConvs)
    (Dv : IntDivisibility)
    (INT_SUB_0 INT_ENTIRE : thm)
    (MESON' : List thm → term → IO (Except String thm)) :
    ExceptT String IO IntTac1 := do
  let B := HolBase.B
  let MESON (ths : List thm) (t : term) : ExceptT String IO thm := MESON' ths t
  let INT_ARITH (t : term) : ExceptT String IO thm := A1.INT_ARITH1 t
  let { INT_POLY_CONV, .. } := Pc
  let { INT_RING, int_ideal_cofactors, .. } := Rg
  let { int_coprime, int_congruent, int_divides, .. } := Dv
  let { LEFT_AND_EXISTS_THM, RIGHT_AND_EXISTS_THM, LEFT_OR_EXISTS_THM,
        RIGHT_OR_EXISTS_THM, UNWIND_THM2, .. } := HolBase.T

  -- let INTEGER_TAC =
  let int_ty ← qty r"int"
  let INT_POLYEQ_CONV :=
    (← GEN_REWRITE_CONV_NET I [← GSYM INT_SUB_0]) THENC LAND_CONV INT_POLY_CONV
  let ISOLATE_VARIABLE ← do
    let pth ← INT_ARITH (← q r"!a x. a = &0 <=> x = x + a")
    let is_defined (v t : term) : Bool :=
      let mons := striplist (dest_binary "int_add") t
      mem v mons && forall' (fun m => v == m || !(free_in v m)) mons
    pure fun (vars : List term) (tm : term) => (do
      let th ← (INT_POLYEQ_CONV tm : ExceptT String IO thm)
      let th' ← ((SYM_CONV THENC INT_POLYEQ_CONV) tm : ExceptT String IO thm)
      let (v, th1) ←
        tryCatch (do let t ← lhand (← rand (concl th)); pure (← find (fun v => is_defined v t) vars, th'))
          (fun _ => do let t ← lhand (← rand (concl th')); pure (← find (fun v => is_defined v t) vars, th))
      let th2 ← TRANS th1 (← SPECL [← lhs (← rand (concl th1)), v] pth)
      CONV_RULE (RAND_CONV (RAND_CONV INT_POLY_CONV)) th2 : ExceptT String IO thm)
  let UNWIND_POLYS_CONV (tm : term) : ExceptT String IO thm := do
    let (vars, bod) := strip_exists tm
    let cjs := conjuncts bod
    let th1 ← (tryfindM (ISOLATE_VARIABLE vars) cjs : ExceptT String IO thm)
    let eq ← lhand (concl th1)
    let bod' ← list_mk_conj (eq :: subtract cjs [eq])
    let th2 ← HolCore.Canon.CONJ_ACI_RULE B (safe_mk_eq bod bod')
    let th3 ← TRANS th2 (← HolCore.Drule.MK_CONJ th1 (REFL (← rand (← rand (concl th2)))))
    let v ← lhs (← lhand (← rand (concl th3)))
    let vars' := subtract vars [v] ++ [v]
    let th4 ← CONV_RULE (RAND_CONV (REWR_CONV UNWIND_THM2))
                (← (HolCore.Drule.MK_EXISTS v th3 : ExceptT String IO thm))
    let IMP_RULE (v v' : List term) : ExceptT String IO thm := do
      DISCH_ALL (← v.foldrM (fun x th => liftExcept (B.SIMPLE_CHOOSE x th))
                   (← v'.foldrM (fun x th => liftExcept (B.SIMPLE_EXISTS x th)) (← ASSUME bod)))
    let th5 ← B.IMP_ANTISYM_RULE (← IMP_RULE vars vars') (← IMP_RULE vars' vars)
    TRANS th5 (← (subtract vars [v]).foldrM
                   (fun x th => (HolCore.Drule.MK_EXISTS x th : ExceptT String IO thm)) th4)
  let zero_tm ← q r"&0"
  let one_tm ← q r"&1"
  let isolate_monomials ← do
    let mul_tm ← q r"(int_mul)"
    let add_tm ← q r"(int_add)"
    let neg_tm ← q r"(int_neg)"
    let dest_mul := dest_binop mul_tm
    let dest_add := dest_binop add_tm
    let mk_mul (a b : term) : Except String term := do (← mk_binop mul_tm a) b
    let mk_add (a b : term) : Except String term := do (← mk_binop add_tm a) b
    let scrub_var (v m : term) : Except String term := do
      let ps := striplist dest_mul m
      let ps' := subtract ps [v]
      if ps' == [] then pure one_tm else end_itlistM mk_mul ps'
    let find_multipliers (v : term) (mons : List term) : Except String term := do
      let mons1 := mons.filter (fun m => free_in v m)
      let mons2 ← mons1.mapM (scrub_var v)
      if mons2 == [] then pure zero_tm else end_itlistM mk_add mons2
    pure fun (vars : List term) (tm : term) => (do
      let (cmons, vmons) :=
        partition (fun m => intersect (frees m) vars == []) (striplist dest_add tm)
      let cofactors ← vars.mapM (fun v => find_multipliers v vmons)
      let cnc ← if cmons == [] then pure zero_tm
                else mk_comb neg_tm (← end_itlistM mk_add cmons)
      pure (cofactors, cnc) : Except String (List term × term))
  let isolate_variables (evs ps : List term) (eq : term) :
      ExceptT String IO (term × List (term × term)) := do
    let vars := evs.filter (fun v => vfree_in v eq)
    let (qs, p) ← isolate_monomials vars eq
    let rs := (qs ++ ps).filter (fun t => type_of t == int_ty)
    let rs ← (int_ideal_cofactors rs p : ExceptT String IO (List term))
    pure (eq, ← zip (← chop_list qs.length rs).1 vars)
  let subst_in_poly (i : List (term × term)) (p : term) : ExceptT String IO term := do
    rhs (concl (← (INT_POLY_CONV ((← vsubst i) p) : ExceptT String IO thm)))
  let solve_idealism := solveIdealism isolate_variables subst_in_poly
  let EXISTS_POLY_TAC : tactic := fun gl => ExceptT.run do
    let (asl, w) := gl
    let (evs, bod) := strip_exists w
    let ps := mapfilter (check (fun t => type_of t == int_ty) o lhs o concl o (Prod.snd : String × thm → thm)) asl
    let cfs ← solve_idealism evs ps (← ((conjuncts bod).mapM lhs : Except String _))
    ((MAP_EVERY EXISTS_TAC (evs.map (fun v => rev_assocd v cfs zero_tm)) THEN
      REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC INT_RING) gl : ExceptT String IO _)
  let SCRUB_NEQ_TAC := MATCH_MP_TAC o MATCH_MP (← MESON []
    (← q r"~(x = y) ==> x = y \/ p ==> p"))
  let INTEGER_TAC1 :=
    REWRITE_TAC [int_coprime, int_congruent, int_divides] THEN
    REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
    REWRITE_TAC [LEFT_AND_EXISTS_THM, RIGHT_AND_EXISTS_THM,
                 LEFT_OR_EXISTS_THM, RIGHT_OR_EXISTS_THM] THEN
    CONV_TAC (REPEATC UNWIND_POLYS_CONV) THEN
    REPEAT (FIRST_X_ASSUM SCRUB_NEQ_TAC) THEN
    REWRITE_TAC [LEFT_AND_EXISTS_THM, RIGHT_AND_EXISTS_THM,
                 LEFT_OR_EXISTS_THM, RIGHT_OR_EXISTS_THM] THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o SYM)) THEN
    CONV_TAC (ONCE_DEPTH_CONV INT_POLYEQ_CONV) THEN
    REWRITE_TAC [← GSYM INT_ENTIRE,
                 ← TAUT (← q r"a \/ (b /\ c) <=> (a \/ b) /\ (a \/ c)")] THEN
    POP_ASSUM_LIST (K ALL_TAC) THEN
    REPEAT DISCH_TAC THEN CONV_TAC genvarExistsConv THEN
    CONV_TAC (ONCE_DEPTH_CONV INT_POLYEQ_CONV) THEN EXISTS_POLY_TAC

  let INTEGER_RULE1 (tm : term) : IO (Except String thm) :=
    HolCore.Tactics.prove B tm INTEGER_TAC1

  return { INTEGER_TAC1, INTEGER_RULE1 }

/- ---------------------------------------------------------------------- -/
/- More div and rem properties.                                           -/
/- ---------------------------------------------------------------------- -/

/-- int.ml 1329-1763. -/
structure IntDivRem1 where
  INT_DIVMOD_UNIQ : thm
  INT_DIV_UNIQ : thm
  INT_REM_UNIQ : thm
  INT_DIV_LT : thm
  INT_REM_LT : thm
  INT_DIV_RNEG : thm
  INT_REM_RNEG : thm
  INT_REM_RABS : thm
  INT_REM_REM : thm
  INT_REM_EQ : thm
  INT_DIV_ZERO : thm
  INT_REM_ZERO : thm
  INT_REM_EQ_0 : thm
  INT_MUL_DIV_EQ : thm
  INT_CONG_LREM : thm
  INT_CONG_RREM : thm
  INT_REM_MOD_SELF : thm
  INT_REM_REM_MUL : thm
  INT_CONG_SOLVE_BOUNDS : thm
  INT_NEG_REM : thm
  INT_ADD_REM : thm
  INT_SUB_REM : thm
  INT_MUL_REM : thm
  INT_POW_REM : thm
  INT_OF_NUM_DIV : thm
  INT_OF_NUM_REM : thm
  INT_DIV_REFL : thm
  INT_REM_REFL : thm
  INT_DIV_LNEG : thm
  INT_REM_LNEG : thm
  INT_DIV_NEG2 : thm
  INT_REM_NEG2 : thm
  INT_DIV_1 : thm
  INT_REM_1 : thm
  INT_DIV_MUL : thm
  INT_REM_MUL : thm
  INT_DIV_LT_EQ : thm
  INT_LE_DIV_EQ : thm
  INT_DIV_LE_EQ : thm
  INT_LT_DIV_EQ : thm
  INT_DIV_LE : thm
  INT_DIV_DIV : thm
  INT_REM_MUL_REM : thm
  INT_DIV_EQ_0 : thm
  INT_REM_EQ_SELF : thm
  INT_REM_UNIQUE : thm
  INT_DIV_REM : thm
  INT_REM_REM_LE : thm
  INT_LE_DIV : thm
  INT_LT_DIV : thm
  INT_REM_LE_EQ : thm
  INT_REM_LE : thm
  INT_REM_MUL_ADD : thm
  INT_DIV_MUL_ADD : thm
  INT_CONG_DIV2 : thm
  INT_REM_2_CASES : thm
  NOT_INT_REM_2 : thm
  INT_REM_2_DIVIDES : thm
  INT_REM_2_EXPAND : thm
  INT_REM_2_NEG : thm
  INT_DIVIDES_DIV_SELF : thm
  INT_DIV_BY_DIV : thm
  INT_DIVIDES_DIV_DIVIDES : thm
  INT_DIVIDES_DIVIDES_DIV : thm
  INT_DIVIDES_DIVIDES_DIV_EQ : thm
  deriving Inhabited

@[nospecialize]
def setupIntDivRem1 [HolBase]
    (N : HolMath.Nums.NumsThms)
    (O : IntOps) (A1 : IntArith1) (Dm : IntDivMod) (Rg : IntRingConvs)
    (Dv : IntDivisibility) (Tc : IntTac1)
    (IT1 : IntThms1) (IT2 : IntThms2) (IT3 : IntThms3) (IT4 : IntThms4)
    (IT5 : IntThms5) (IT6 : IntThms6) (IT7 : IntThms7) (IT8 : IntThms8)
    (IT9 : IntThms9) (IT10 : IntThms10)
    (DIVISION DIV_ZERO MOD_ZERO MOD_LE LE_1 RDIV_LT_EQ : thm)
    (MESON_TAC : List thm → tactic) (ASM_MESON_TAC : List thm → tactic) :
    ExceptT String IO IntDivRem1 := do
  let INDUCT_TAC := HolMath.Nums.INDUCT_TAC N.num_INDUCTION
  let INT_ARITH (t : term) : ExceptT String IO thm := A1.INT_ARITH1 t
  let INT_ARITH_TAC := A1.INT_ARITH_TAC1
  let ASM_INT_ARITH_TAC := A1.ASM_INT_ARITH_TAC1
  let INTEGER_TAC := Tc.INTEGER_TAC1
  let INTEGER_RULE (t : term) : ExceptT String IO thm := Tc.INTEGER_RULE1 t
  let INT_RING (t : term) : ExceptT String IO thm := Rg.INT_RING t
  let { INT_ABS_0, INT_ABS_MUL, INT_ABS_NEG, INT_ABS_NUM, INT_ABS_POS,
        INT_ADD_AC, .. } := IT1
  let { INT_ADD_LID, INT_ADD_RID, INT_ENTIRE, INT_EQ_SUB_RADD, .. } := IT2
  let { INT_LET_ADD2, INT_LET_ANTISYM, INT_LE_ADD, INT_LE_ANTISYM, INT_LE_LMUL,
        INT_LE_LMUL_EQ, INT_LE_LT, INT_LE_MUL, .. } := IT3
  let { INT_LE_REFL, INT_LE_RMUL, INT_LE_SUB_LADD, INT_LE_TRANS, INT_LTE_TRANS, .. } := IT4
  let { INT_LT_IMP_LE, INT_LT_LMUL_EQ, .. } := IT5
  let { INT_LT_SUB_RADD, INT_MUL_AC, INT_MUL_LNEG, INT_MUL_LZERO, .. } := IT6
  let { INT_MUL_RID, INT_MUL_RNEG, INT_MUL_RZERO, INT_MUL_SYM, INT_NEG_0,
        INT_NEG_EQ_0, INT_NOT_LE, INT_NOT_LT, INT_OF_NUM_ADD,
        INT_OF_NUM_CLAUSES, INT_OF_NUM_EQ, INT_OF_NUM_LE, INT_OF_NUM_LT, .. } := IT7
  let { INT_OF_NUM_MUL, INT_POS, .. } := IT8
  let { INT_SGN, INT_SGN_0, INT_SGN_ABS_ALT, .. } := IT9
  let { INT_SGN_NEG, .. } := IT10
  let { FORALL_INT_CASES, INT_LT_DISCRETE, .. } := O
  let { INT_FORALL_POS, INT_FORALL_ABS, INT_POW, .. } := A1
  let { INT_LE_DISCRETE, INT_DIVISION, INT_DIVISION_SIMP, INT_REM_POS,
        INT_DIV_0, INT_REM_0, INT_REM_POS_EQ, INT_REM_DIV, INT_LT_REM, .. } := Dm
  let { int_divides, int_congruent, .. } := Dv
  let { EQ_SYM_EQ, CONJ_SYM, IMP_CONJ, SWAP_FORALL_THM, AND_FORALL_THM,
        RIGHT_FORALL_IMP_THM, LEFT_IMP_EXISTS_THM, MONO_FORALL, .. } := HolBase.T

  let INT_DIVMOD_UNIQ ← prove
   r"!m n q r. m = q * n + r /\ &0 <= r /\ r < abs n
             ==> m div n = q /\ m rem n = r"
   (← do
    let i1 ← INT_ARITH
     (← q r"&1 * abs n <= abs(q - m div n) * abs n /\
      abs(m rem n - r) = abs((q - m div n) * n)
      ==> ~(abs(m rem n - r) < abs n)")
    let t1 ← TAUT (← q r"~p ==> p ==> q")
    pure
     (REPEAT GEN_TAC THEN STRIP_TAC THEN
      SUBGOAL_THEN (← q r"~(n = &0)") MP_TAC THENL [ASM_INT_ARITH_TAC, ALL_TAC] THEN
      DISCH_THEN (STRIP_ASSUME_TAC o SPEC (← q r"m:int") o MATCH_MP INT_DIVISION) THEN
      ASM_CASES_TAC (← q r"m div n = q") THENL
       [REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC INT_RING, ALL_TAC] THEN
      SUBGOAL_THEN (← q r"abs(m rem n - r) < abs n") MP_TAC THENL
       [ASM_INT_ARITH_TAC, MATCH_MP_TAC t1] THEN
      MATCH_MP_TAC i1 THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC INT_LE_RMUL THEN ASM_INT_ARITH_TAC,
        AP_TERM_TAC THEN REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC INT_RING]))

  let INT_DIV_UNIQ ← prove
   r"!m n q r. m = q * n + r /\ &0 <= r /\ r < abs n
             ==> m div n = q"
   (MESON_TAC [INT_DIVMOD_UNIQ])

  let INT_REM_UNIQ ← prove
   r"!m n q r. m = q * n + r /\ &0 <= r /\ r < abs n
             ==> m rem n = r"
   (MESON_TAC [INT_DIVMOD_UNIQ])

  let (INT_DIV_LT, INT_REM_LT) ← CONJ_PAIR (← prove
   r"(!m n. (~(n = &0) ==> &0 <= m) /\ m < n ==> m div n = &0) /\
   (!m n. (~(n = &0) ==> &0 <= m) /\ m < n ==> m rem n = m)"
   (REWRITE_TAC [AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"n:int = &0") THEN ASM_REWRITE_TAC [INT_DIV_0, INT_REM_0] THEN
    REWRITE_TAC [← TAUT (← q r"(p ==> q) /\ (p ==> r) <=> p ==> q /\ r")] THEN
    STRIP_TAC THEN MATCH_MP_TAC INT_DIVMOD_UNIQ THEN ASM_INT_ARITH_TAC))

  let (INT_DIV_RNEG, INT_REM_RNEG) ← CONJ_PAIR (← prove
   r"(!m n. m div (--n) = --(m div n)) /\
   (!m n. m rem (--n) = m rem n)"
   (REWRITE_TAC [AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"n:int = &0") THEN
    ASM_REWRITE_TAC [INT_DIV_0, INT_REM_0, INT_NEG_0] THEN
    MATCH_MP_TAC INT_DIVMOD_UNIQ THEN
    MP_TAC (← SPECL [← q r"m:int", ← q r"n:int"] INT_DIVISION) THEN
    ASM_INT_ARITH_TAC))

  let INT_REM_RABS ← prove
   r"!x y. x rem (abs y) = x rem y"
   (REWRITE_TAC [FORALL_INT_CASES, INT_ABS_NEG, INT_REM_RNEG, INT_ABS_NUM])

  let INT_REM_REM ← prove
   r"!m n. (m rem n) rem n = m rem n"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"n:int = &0") THEN ASM_REWRITE_TAC [INT_REM_0] THEN
    MATCH_MP_TAC INT_REM_UNIQ THEN EXISTS_TAC (← q r"&0:int") THEN
    REWRITE_TAC [INT_MUL_LZERO, INT_ADD_LID] THEN
    ASM_MESON_TAC [INT_DIVISION])

  let INT_REM_EQ ← prove
   r"!m n p. m rem p = n rem p <=> (m == n) (mod p)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [int_congruent] THEN
    EQ_TAC THENL
     [DISCH_TAC THEN EXISTS_TAC (← q r"m div p - n div p") THEN
      MP_TAC (← SPECL [← q r"m:int", ← q r"p:int"] INT_DIVISION_SIMP) THEN
      MP_TAC (← SPECL [← q r"n:int", ← q r"p:int"] INT_DIVISION_SIMP) THEN
      ASM_REWRITE_TAC [] THEN CONV_TAC INT_RING,
      REWRITE_TAC [LEFT_IMP_EXISTS_THM, INT_EQ_SUB_RADD] THEN
      X_GEN_TAC (← q r"d:int") THEN DISCH_THEN SUBST1_TAC THEN
      ASM_CASES_TAC (← q r"p:int = &0") THEN
      ASM_REWRITE_TAC [INT_REM_0, INT_MUL_LZERO, INT_ADD_LID] THEN
      MATCH_MP_TAC INT_REM_UNIQ THEN EXISTS_TAC (← q r"n div p + d") THEN
      MP_TAC (← SPECL [← q r"n:int", ← q r"p:int"] INT_DIVISION) THEN
      ASM_SIMP_TAC [] THEN CONV_TAC INT_RING])

  let (INT_DIV_ZERO, INT_REM_ZERO) ← CONJ_PAIR (← prove
   r"(!n. &0 div n = &0) /\ (!n. &0 rem n = &0)"
   (REWRITE_TAC [AND_FORALL_THM] THEN GEN_TAC THEN
    ASM_CASES_TAC (← q r"n:int = &0") THEN ASM_REWRITE_TAC [INT_DIV_0, INT_REM_0] THEN
    MATCH_MP_TAC INT_DIVMOD_UNIQ THEN
    ASM_INT_ARITH_TAC))

  let INT_REM_EQ_0 ← prove
   r"!m n. m rem n = &0 <=> n divides m"
   (REPEAT GEN_TAC THEN
    SUBST1_TAC (← SYM (← SPEC (← q r"n:int") INT_REM_ZERO)) THEN
    REWRITE_TAC [INT_REM_EQ] THEN CONV_TAC INTEGER_RULE)

  let INT_MUL_DIV_EQ ← prove
   r"(!m n. n * m div n = m <=> n divides m) /\
   (!m n. m div n * n = m <=> n divides m)"
   (REWRITE_TAC [AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
    MP_TAC (← SPECL [← q r"m:int", ← q r"n:int"] INT_DIVISION_SIMP) THEN
    REWRITE_TAC [← GSYM INT_REM_EQ_0] THEN CONV_TAC INT_RING)

  let INT_CONG_LREM ← prove
   r"!x y n. (x rem n == y) (mod n) <=> (x == y) (mod n)"
   (REWRITE_TAC [← GSYM INT_REM_EQ, INT_REM_REM])

  let INT_CONG_RREM ← prove
   r"!x y n. (x == y rem n) (mod n) <=> (x == y) (mod n)"
   (REWRITE_TAC [← GSYM INT_REM_EQ, INT_REM_REM])

  let INT_REM_MOD_SELF ← prove
   r"!m n. (m rem n == m) (mod n)"
   (REWRITE_TAC [INT_CONG_LREM] THEN CONV_TAC INTEGER_RULE)

  let INT_REM_REM_MUL ← prove
   r"(!m n p. m rem (n * p) rem n = m rem n) /\
   (!m n p. m rem (n * p) rem p = m rem p)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [INT_REM_EQ] THENL
     [MP_TAC (← ISPECL [← q r"m:int", ← q r"n * p:int"] INT_REM_MOD_SELF),
      MP_TAC (← ISPECL [← q r"m:int", ← q r"n * p:int"] INT_REM_MOD_SELF)] THEN
    CONV_TAC INTEGER_RULE)

  let INT_CONG_SOLVE_BOUNDS ← prove
   r"!a n:int. ~(n = &0) ==> ?x. &0 <= x /\ x < abs n /\ (x == a) (mod n)"
   (MESON_TAC [INT_DIVISION, INT_REM_MOD_SELF])

  let INT_NEG_REM ← prove
   r"!n p. --(n rem p) rem p = --n rem p"
   (REPEAT GEN_TAC THEN REWRITE_TAC [INT_REM_EQ] THEN
    MATCH_MP_TAC (← INTEGER_RULE
     (← q r"(a:int == b) (mod n) ==> (--a == --b) (mod n)")) THEN
    REWRITE_TAC [INT_REM_MOD_SELF])

  let INT_ADD_REM ← prove
   r"!m n p. (m rem p + n rem p) rem p = (m + n) rem p"
   (REPEAT GEN_TAC THEN REWRITE_TAC [INT_REM_EQ] THEN MATCH_MP_TAC (← INTEGER_RULE
     (← q r"(x:int == x') (mod n) /\ (y == y') (mod n)
      ==> (x + y == x' + y') (mod n)")) THEN
    REWRITE_TAC [INT_REM_MOD_SELF])

  let INT_SUB_REM ← prove
   r"!m n p. (m rem p - n rem p) rem p = (m - n) rem p"
   (REPEAT GEN_TAC THEN REWRITE_TAC [INT_REM_EQ] THEN MATCH_MP_TAC (← INTEGER_RULE
     (← q r"(x:int == x') (mod n) /\ (y == y') (mod n)
      ==> (x - y == x' - y') (mod n)")) THEN
    REWRITE_TAC [INT_REM_MOD_SELF])

  let INT_MUL_REM ← prove
   r"!m n p. (m rem p * n rem p) rem p = (m * n) rem p"
   (REPEAT GEN_TAC THEN REWRITE_TAC [INT_REM_EQ] THEN MATCH_MP_TAC (← INTEGER_RULE
     (← q r"(x:int == x') (mod n) /\ (y == y') (mod n)
      ==> (x * y == x' * y') (mod n)")) THEN
    REWRITE_TAC [INT_REM_MOD_SELF])

  let INT_POW_REM ← prove
   r"!m n p. ((m rem p) pow n) rem p = (m pow n) rem p"
   (GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC [INT_POW] THEN
    GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [← GSYM INT_MUL_REM] THEN
    ASM_REWRITE_TAC [] THEN REWRITE_TAC [INT_REM_REM] THEN
    REWRITE_TAC [INT_MUL_REM])

  let (INT_OF_NUM_DIV, INT_OF_NUM_REM) ← CONJ_PAIR (← prove
   r"(!m n. &m div &n = &(m DIV n)) /\
   (!m n. &m rem &n = &(m MOD n))"
   (REWRITE_TAC [AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_REWRITE_TAC [INT_DIV_0, INT_REM_0, DIV_ZERO, MOD_ZERO] THEN
    MATCH_MP_TAC INT_DIVMOD_UNIQ THEN
    REWRITE_TAC [INT_OF_NUM_MUL, INT_OF_NUM_ADD, INT_ABS_NUM] THEN
    REWRITE_TAC [INT_POS, INT_OF_NUM_EQ, INT_OF_NUM_LT] THEN
    MATCH_MP_TAC DIVISION THEN ASM_REWRITE_TAC []))

  let (INT_DIV_REFL, INT_REM_REFL) ← CONJ_PAIR (← prove
   r"(!n. n div n = if n = &0 then &0 else &1) /\
   (!n. n rem n = &0)"
   (REWRITE_TAC [AND_FORALL_THM] THEN X_GEN_TAC (← q r"n:int") THEN
    COND_CASES_TAC THENL [ASM_MESON_TAC [INT_DIV_0, INT_REM_0], ALL_TAC] THEN
    MATCH_MP_TAC INT_DIVMOD_UNIQ THEN ASM_INT_ARITH_TAC))

  let (INT_DIV_LNEG, INT_REM_LNEG) ← CONJ_PAIR (← prove
   r"(!m n. --m div n =
          if m rem n = &0 then --(m div n) else --(m div n) - int_sgn n) /\
   (!m n. --m rem n =
          if m rem n = &0 then &0 else abs n - m rem n)"
   (REWRITE_TAC [AND_FORALL_THM] THEN MAP_EVERY X_GEN_TAC [← q r"m:int", ← q r"n:int"] THEN
    ASM_CASES_TAC (← q r"n:int = &0") THENL
     [ASM_REWRITE_TAC [INT_DIV_0, INT_REM_0, INT_SGN_0] THEN INT_ARITH_TAC,
      ALL_TAC] THEN
    MATCH_MP_TAC INT_DIVMOD_UNIQ THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q r"m:int") o MATCH_MP INT_DIVISION) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [INT_SGN_ABS_ALT, ← INT_ARITH
     (← q r"--m:int = (--x - y) * z + w <=> m = x * z + y * z - w")] THEN
    ASM_REWRITE_TAC [] THEN ASM_INT_ARITH_TAC))

  let INT_DIV_NEG2 ← prove
   r"!m n. --m div --n = if m rem n = &0 then m div n else m div n + int_sgn n"
   (REWRITE_TAC [INT_DIV_RNEG, INT_DIV_LNEG, INT_SGN_NEG, INT_REM_RNEG] THEN
    INT_ARITH_TAC)

  let INT_REM_NEG2 ← prove
   r"!m n. --m rem --n = if m rem n = &0 then &0 else abs n - m rem n"
   (REWRITE_TAC [INT_REM_LNEG, INT_REM_RNEG] THEN INT_ARITH_TAC)

  let (INT_DIV_1, INT_REM_1) ← CONJ_PAIR (← prove
   r"(!n. n div &1 = n) /\
   (!n. n rem &1 = &0)"
   (REWRITE_TAC [AND_FORALL_THM] THEN GEN_TAC THEN
    MATCH_MP_TAC INT_DIVMOD_UNIQ THEN INT_ARITH_TAC))

  let (INT_DIV_MUL, INT_REM_MUL) ← CONJ_PAIR (← prove
   r"((!m n. ~(n = &0) ==> (m * n) div n = m) /\
    (!m n. ~(m = &0) ==> (m * n) div m = n)) /\
   ((!m n. (m * n) rem n = &0) /\
    (!m n. (m * n) rem m = &0))"
   (MATCH_MP_TAC (← TAUT
     (← q r"((p ==> p') /\ (q ==> q')) /\ p /\ q ==> (p /\ p') /\ (q /\ q')")) THEN
    CONJ_TAC THENL [MESON_TAC [INT_MUL_SYM], REWRITE_TAC [AND_FORALL_THM]] THEN
    REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n:int = &0") THEN
    ASM_REWRITE_TAC [INT_REM_0, INT_MUL_RZERO] THEN
    MATCH_MP_TAC INT_DIVMOD_UNIQ THEN ASM_INT_ARITH_TAC))

  let INT_DIV_LT_EQ ← prove
   r"!a b c. &0 < a ==> (b div a < c <=> b < a * c)"
   (← do
    let i5 ← INT_ARITH
     (← q r"(~(m:int < n * --c) <=> --m < n * c) <=> ~(m = n * --c)")
    let i4 ← INT_ARITH (← q r"--a:int <= b <=> ~(a < --b)")
    let i3 ← INT_ARITH (← q r"--(q * &n + &0:int) = &n * --q")
    let i2 ← INT_ARITH (← q r"~(&m:int < -- &n)")
    let t1 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    let i1 ← INT_ARITH (← q r"~(&0:int < -- &n)")
    pure
     (GEN_REWRITE_TAC I [FORALL_INT_CASES] THEN
      REWRITE_TAC [i1] THEN X_GEN_TAC (← q r"n:num") THEN
      REWRITE_TAC [RIGHT_FORALL_IMP_THM, INT_OF_NUM_LT] THEN DISCH_TAC THEN
      GEN_REWRITE_TAC I [FORALL_INT_CASES] THEN
      MATCH_MP_TAC t1 THEN CONJ_TAC THENL
       [REWRITE_TAC [INT_OF_NUM_DIV, FORALL_INT_CASES] THEN
        REWRITE_TAC [INT_MUL_RNEG, INT_OF_NUM_MUL] THEN
        REWRITE_TAC [INT_OF_NUM_LT, i2] THEN
        ASM_SIMP_TAC [RDIV_LT_EQ, LE_1],
        DISCH_TAC] THEN
      X_GEN_TAC (← q r"m:num") THEN
      REWRITE_TAC [INT_DIV_LNEG] THEN COND_CASES_TAC THENL
       [MP_TAC (← SPECL [← q r"&m:int", ← q r"&n:int"] INT_DIVISION) THEN
        MAP_EVERY ABBREV_TAC [← q r"q = &m div &n", ← q r"r = &m rem &n"] THEN
        ASM_SIMP_TAC [INT_OF_NUM_EQ, LE_1] THEN DISCH_TAC THEN
        REWRITE_TAC [i3] THEN
        ASM_SIMP_TAC [INT_LT_LMUL_EQ, INT_OF_NUM_LT],
        ALL_TAC] THEN
      ASM_SIMP_TAC [INT_SGN, INT_OF_NUM_LT, LE_1] THEN
      REWRITE_TAC [INT_LT_SUB_RADD, ← GSYM INT_LE_DISCRETE] THEN
      ASM_REWRITE_TAC [i4] THEN
      REWRITE_TAC [i5] THEN
      ASM_MESON_TAC [INT_REM_MUL]))

  let INT_LE_DIV_EQ ← prove
   r"!a b c. &0 < a ==> (c <= b div a <=> a * c <= b)"
   (SIMP_TAC [← GSYM INT_NOT_LT, INT_DIV_LT_EQ])

  let INT_DIV_LE_EQ ← prove
   r"!a b c. &0 < a ==> (b div a <= c <=> b < a * (c + &1))"
   (SIMP_TAC [INT_LE_DISCRETE, INT_DIV_LT_EQ])

  let INT_LT_DIV_EQ ← prove
   r"!a b c. &0 < a ==> (c < b div a <=> a * (c + &1) <= b)"
   (SIMP_TAC [← GSYM INT_NOT_LE, INT_DIV_LE_EQ])

  let INT_DIV_LE ← prove
   r"!m n. abs(m div n) <= abs m"
   (GEN_REWRITE_TAC BINDER_CONV [FORALL_INT_CASES] THEN
    REWRITE_TAC [INT_DIV_RNEG, INT_ABS_NEG] THEN
    GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN X_GEN_TAC (← q r"n:num") THEN
    ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_REWRITE_TAC [INT_DIV_0, INT_ABS_NUM, INT_ABS_POS] THEN
    REWRITE_TAC [← INT_ARITH (← q r"abs(x:int) <= a <=> --a <= x /\ x <= a")] THEN
    ASM_SIMP_TAC [INT_LE_DIV_EQ, INT_DIV_LE_EQ, INT_OF_NUM_LT, LE_1] THEN
    X_GEN_TAC (← q r"m:int") THEN MATCH_MP_TAC (← INT_ARITH
     (← q r"&0:int < n /\ abs m * &1 <= abs m * n
      ==> n * --abs m <= m /\ m < n * (abs m + &1)")) THEN
    ASM_SIMP_TAC [INT_OF_NUM_LT, LE_1] THEN
    MATCH_MP_TAC INT_LE_LMUL THEN REWRITE_TAC [INT_ABS_POS] THEN
    ASM_SIMP_TAC [INT_OF_NUM_LE, LE_1])

  let (INT_DIV_DIV, INT_REM_MUL_REM) ← CONJ_PAIR (← prove
   r"(!m n p. &0 <= n ==> (m div n) div p = m div (n * p)) /\
   (!m n p. &0 <= n ==> m rem (n * p) = n * (m div n) rem p + m rem n)"
   (REWRITE_TAC [AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"n:int = &0") THEN
    ASM_REWRITE_TAC [INT_MUL_LZERO, INT_DIV_0, INT_REM_0,
                     INT_DIV_ZERO, INT_ADD_LID, INT_LE_LT] THEN
    ASM_CASES_TAC (← q r"&0:int < n") THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q r"p:int = &0") THEN
    ASM_REWRITE_TAC [INT_MUL_RZERO, INT_DIV_0, INT_REM_0] THENL
     [REWRITE_TAC [INT_REM_DIV] THEN INT_ARITH_TAC, ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [EQ_SYM_EQ] THEN
    MATCH_MP_TAC INT_DIVMOD_UNIQ THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC [INT_REM_DIV] THEN INT_ARITH_TAC,
      ASM_SIMP_TAC [INT_LE_ADD, INT_LE_MUL, INT_LT_IMP_LE, INT_DIVISION],
      TRANS_TAC INT_LTE_TRANS (← q r"n * (abs p - &1) + n:int") THEN CONJ_TAC THENL
       [MATCH_MP_TAC INT_LET_ADD2 THEN ASM_SIMP_TAC [INT_LT_REM] THEN
        ASM_SIMP_TAC [INT_LE_LMUL_EQ, INT_LE_SUB_LADD, ← GSYM INT_LT_DISCRETE] THEN
        ASM_SIMP_TAC [INT_DIVISION],
        REWRITE_TAC [← INT_ARITH (← q r"n * (p - &1) + n:int = n * p"), INT_ABS_MUL] THEN
        MATCH_MP_TAC INT_LE_RMUL THEN INT_ARITH_TAC]]))

  let INT_DIV_EQ_0 ← prove
   r"!m n. m div n = &0 <=> n = &0 \/ &0 <= m /\ m < abs n"
   (GEN_REWRITE_TAC BINDER_CONV [FORALL_INT_CASES] THEN
    REWRITE_TAC [INT_DIV_RNEG, INT_NEG_EQ_0, INT_ABS_NEG] THEN
    MAP_EVERY X_GEN_TAC [← q r"m:int", ← q r"n:num"] THEN ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_REWRITE_TAC [INT_DIV_0, INT_OF_NUM_EQ, INT_ABS_NUM] THEN
    ASM_SIMP_TAC [← GSYM INT_LE_ANTISYM, INT_DIV_LE_EQ, INT_LE_DIV_EQ, CONJ_SYM,
                  INT_OF_NUM_LT, LE_1, INT_ADD_LID, INT_MUL_RZERO, INT_MUL_RID])

  let INT_REM_EQ_SELF ← prove
   r"!m n. m rem n = m <=> n = &0 \/ &0 <= m /\ m < abs n"
   (REWRITE_TAC [INT_REM_DIV, ← INT_ARITH (← q r"m - x:int = m <=> x = &0")] THEN
    REWRITE_TAC [INT_DIV_EQ_0, INT_ENTIRE] THEN INT_ARITH_TAC)

  let INT_REM_UNIQUE ← prove
   r"!m n p. m rem n = p <=>
           (n = &0 /\ m = p \/ &0 <= p /\ p < abs n) /\ (m == p) (mod n)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n:int = &0") THENL
     [ASM_REWRITE_TAC [INT_REM_0, INT_ABS_0, INT_LET_ANTISYM] THEN
      CONV_TAC INTEGER_RULE,
      EQ_TAC THENL
       [DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [INT_DIVISION] THEN
        REWRITE_TAC [← GSYM INT_REM_EQ, INT_REM_REM],
        ASM_SIMP_TAC [← GSYM INT_REM_EQ, INT_REM_EQ_SELF]]])

  let INT_DIV_REM ← prove
   r"!m n p. &0 <= n ==> (m div n) rem p = (m rem (n * p)) div n"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n:int = &0") THEN
    ASM_REWRITE_TAC [INT_LE_LT, INT_DIV_0, INT_REM_ZERO] THEN DISCH_TAC THEN
    ASM_SIMP_TAC [INT_REM_MUL_REM, INT_LT_IMP_LE] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_DIV_UNIQ THEN
    EXISTS_TAC (← q r"m rem n") THEN ASM_SIMP_TAC [INT_DIVISION] THEN
    REWRITE_TAC [INT_ADD_AC, INT_MUL_AC])

  let INT_REM_REM_LE ← prove
   r"!m n p. ~(n = &0) /\ abs n <= abs p ==> m rem n rem p = m rem n"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [INT_REM_EQ_SELF] THEN
    ASM_CASES_TAC (← q r"p:int = &0") THEN ASM_REWRITE_TAC [INT_REM_POS_EQ] THEN
    TRANS_TAC INT_LTE_TRANS (← q r"abs n:int") THEN ASM_MESON_TAC [INT_DIVISION])

  let INT_LE_DIV ← prove
   r"!m n. &0 <= m /\ &0 <= n ==> &0 <= m div n"
   (REWRITE_TAC [← GSYM INT_FORALL_POS, IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC [INT_OF_NUM_DIV, INT_POS])

  let INT_LT_DIV ← prove
   r"!m n. &0 < n /\ n <= m ==> &0 < m div n"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [← INT_ARITH (← q r"&0:int < x <=> &0 <= x /\ ~(x = &0)")] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INT_LE_DIV THEN ASM_INT_ARITH_TAC,
      REWRITE_TAC [INT_DIV_EQ_0] THEN ASM_INT_ARITH_TAC])

  let INT_REM_LE_EQ ← prove
   r"!m n. m rem n <= m <=> n = &0 \/ &0 <= m"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n:int = &0") THEN
    ASM_SIMP_TAC [INT_REM_0, INT_LE_REFL] THEN
    EQ_TAC THENL [ASM_MESON_TAC [INT_REM_POS, INT_LE_TRANS], ALL_TAC] THEN
    ONCE_REWRITE_TAC [← GSYM INT_REM_RABS] THEN
    MAP_EVERY (fun t => SPEC_TAC (t, t)) [← q r"m:int", ← q r"n:int"] THEN
    REWRITE_TAC [← GSYM INT_FORALL_POS, ← GSYM INT_FORALL_ABS] THEN
    REWRITE_TAC [INT_OF_NUM_CLAUSES, INT_OF_NUM_REM, MOD_LE])

  let INT_REM_LE ← prove
   r"!m n p. (n = &0 \/ &0 <= m) /\ m <= p ==> m rem n <= p"
   (MESON_TAC [INT_REM_LE_EQ, INT_LE_TRANS])

  let INT_REM_MUL_ADD ← prove
   r"(!m n p. (m * n + p) rem n = p rem n) /\
   (!m n p. (n * m + p) rem n = p rem n) /\
   (!m n p. (p + m * n) rem n = p rem n) /\
   (!m n p. (p + n * m) rem n = p rem n)"
   (ONCE_REWRITE_TAC [← GSYM INT_ADD_REM] THEN
    REWRITE_TAC [INT_REM_MUL, INT_ADD_LID, INT_ADD_RID, INT_REM_REM])

  let INT_DIV_MUL_ADD ← prove
   r"(!m n p. ~(n = &0) ==> (m * n + p) div n = m + p div n) /\
   (!m n p. ~(n = &0) ==> (n * m + p) div n = m + p div n) /\
   (!m n p. ~(n = &0) ==> (p + m * n) div n = p div n + m) /\
   (!m n p. ~(n = &0) ==> (p + n * m) div n = p div n + m)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_DIV_UNIQ THEN
    EXISTS_TAC (← q r"p rem n") THEN
    MP_TAC (← SPECL [← q r"p:int", ← q r"n:int"] INT_DIVISION) THEN
    ASM_REWRITE_TAC [] THEN ASM_INT_ARITH_TAC)

  -- OCaml evaluates the list right to left, so the second INTEGER_RULE runs
  -- (and prints) first.
  let INT_CONG_DIV2 ← prove
   r"!a b m n.
      (a == b) (mod (m * n)) ==> (a div m == b div m) (mod n)"
   (← do
    let ir2 ← INTEGER_RULE (← q r"(a:int == b) (mod(--n)) <=> (a == b) (mod n)")
    let ir1 ← INTEGER_RULE (← q r"(--a:int == --b) (mod n) <=> (a == b) (mod n)")
    pure
     (GEN_REWRITE_TAC (funpow 2 BINDER_CONV) [FORALL_INT_CASES] THEN
      REWRITE_TAC [INT_DIV_RNEG, INT_MUL_LNEG, ir1, ir2] THEN
      SIMP_TAC [← GSYM INT_REM_EQ, INT_DIV_REM, INT_POS]))

  let INT_REM_2_CASES ← prove
   r"!n. n rem &2 = &0 \/ n rem &2 = &1"
   (GEN_TAC THEN MP_TAC (← SPECL [← q r"n:int", ← q r"&2:int"] INT_DIVISION) THEN
    INT_ARITH_TAC)

  let NOT_INT_REM_2 ← prove
   r"(!n. ~(n rem &2 = &0) <=> n rem &2 = &1) /\
   (!n. ~(n rem &2 = &1) <=> n rem &2 = &0)"
   (REWRITE_TAC [AND_FORALL_THM] THEN MP_TAC INT_REM_2_CASES THEN
    MATCH_MP_TAC MONO_FORALL THEN INT_ARITH_TAC)

  let INT_REM_2_DIVIDES ← prove
   r"(!n. n rem &2 = &0 <=> &2 divides n) /\
   (!n. n rem &2 = &1 <=> ~(&2 divides n))"
   (REWRITE_TAC [← GSYM (← CONJUNCT1 NOT_INT_REM_2)] THEN
    REWRITE_TAC [INT_REM_EQ_0])

  let INT_REM_2_EXPAND ← prove
   r"!x. x rem &2 = if &2 divides x then &0 else &1"
   (MESON_TAC [INT_REM_2_DIVIDES])

  let INT_REM_2_NEG ← prove
   r"!x. --x rem &2 = x rem &2"
   (GEN_TAC THEN REWRITE_TAC [INT_REM_2_EXPAND] THEN
    REWRITE_TAC [← INTEGER_RULE (← q r"(a:int) divides --x <=> a divides x")])

  let INT_DIVIDES_DIV_SELF ← prove
   r"!n d. d divides n ==> n div d divides n"
   (MESON_TAC [INT_MUL_DIV_EQ, int_divides])

  let INT_DIV_BY_DIV ← prove
   r"!m n:int. ~(n = &0) /\ m divides n ==> n div (n div m) = m"
   (MESON_TAC [INT_DIVIDES_DIV_SELF, INT_MUL_DIV_EQ, ← INT_RING
     (← q r"a * x:int = n /\ a * y = n /\ ~(n = &0) ==> x = y")])

  let INT_DIVIDES_DIV_DIVIDES ← prove
   r"!n d e. d divides n /\ (n = &0 ==> e = &0)
           ==> (n div d divides e <=> n divides d * e)"
   (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [← GSYM (← CONJUNCT1 INT_MUL_DIV_EQ)] THEN
    ASM_CASES_TAC (← q r"e:int = &0") THEN ASM_REWRITE_TAC [] THEN INTEGER_TAC)

  let INT_DIVIDES_DIVIDES_DIV ← prove
   r"!n d e. d divides n ==> (e divides (n div d) <=> (d * e) divides n)"
   (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM (← CONJUNCT1 INT_MUL_DIV_EQ)] THEN
    ASM_CASES_TAC (← q r"d:int = &0") THEN ASM_REWRITE_TAC [INT_DIV_ZERO, INT_DIV_0] THEN
    INTEGER_TAC)

  let INT_DIVIDES_DIVIDES_DIV_EQ ← prove
   r"!n d e. d divides n /\ e divides (n div d) <=> (d * e) divides n"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC (← TAUT
     (← q r"(r ==> p) /\ (p ==> (q <=> r)) ==> (p /\ q <=> r)")) THEN
    REWRITE_TAC [INT_DIVIDES_DIVIDES_DIV] THEN INTEGER_TAC)

  return {
    INT_DIVMOD_UNIQ, INT_DIV_UNIQ, INT_REM_UNIQ, INT_DIV_LT, INT_REM_LT,
    INT_DIV_RNEG, INT_REM_RNEG, INT_REM_RABS, INT_REM_REM, INT_REM_EQ,
    INT_DIV_ZERO, INT_REM_ZERO, INT_REM_EQ_0, INT_MUL_DIV_EQ, INT_CONG_LREM,
    INT_CONG_RREM, INT_REM_MOD_SELF, INT_REM_REM_MUL, INT_CONG_SOLVE_BOUNDS,
    INT_NEG_REM,
    INT_ADD_REM, INT_SUB_REM, INT_MUL_REM, INT_POW_REM, INT_OF_NUM_DIV,
    INT_OF_NUM_REM, INT_DIV_REFL, INT_REM_REFL, INT_DIV_LNEG, INT_REM_LNEG,
    INT_DIV_NEG2, INT_REM_NEG2, INT_DIV_1, INT_REM_1, INT_DIV_MUL, INT_REM_MUL,
    INT_DIV_LT_EQ, INT_LE_DIV_EQ, INT_DIV_LE_EQ, INT_LT_DIV_EQ, INT_DIV_LE,
    INT_DIV_DIV, INT_REM_MUL_REM,
    INT_DIV_EQ_0, INT_REM_EQ_SELF, INT_REM_UNIQUE, INT_DIV_REM, INT_REM_REM_LE,
    INT_LE_DIV, INT_LT_DIV, INT_REM_LE_EQ, INT_REM_LE, INT_REM_MUL_ADD,
    INT_DIV_MUL_ADD, INT_CONG_DIV2, INT_REM_2_CASES, NOT_INT_REM_2,
    INT_REM_2_DIVIDES, INT_REM_2_EXPAND, INT_REM_2_NEG, INT_DIVIDES_DIV_SELF,
    INT_DIV_BY_DIV, INT_DIVIDES_DIV_DIVIDES, INT_DIVIDES_DIVIDES_DIV,
    INT_DIVIDES_DIVIDES_DIV_EQ }

/- ---------------------------------------------------------------------- -/
/- Arithmetic operations also on div and rem, hence the whole lot.        -/
/- ---------------------------------------------------------------------- -/

structure IntDivRemConvs where
  INT_DIV_CONV : ioconv
  INT_REM_CONV : ioconv
  deriving Inhabited

/-- `let INT_DIV_CONV,INT_REM_CONV = ...` (int.ml 1772-1801). -/
@[nospecialize]
def setupIntDivRemConvs [HolBase]
    (I : IntConstSyntax)
    (Cc : IntCompareConvs)
    (Ar : IntArithConvs)
    (Dr : IntDivRem1)
    (MESON_TAC : List thm → tactic) :
    ExceptT String IO IntDivRemConvs := do
  let { INT_LE_CONV, INT_LT_CONV, .. } := Cc
  let { INT_MUL_CONV, INT_ADD_CONV, INT_ABS_CONV, .. } := Ar
  let mk_intconst := mk_intconst I
  let pth ← prove
   r"q * n + r = m ==> &0 <= r ==> r < abs n ==> m div n = q /\ m rem n = r"
    (MESON_TAC [Dr.INT_DIVMOD_UNIQ])
  let m ← q r"m:int"
  let n ← q r"n:int"
  let q_ ← q r"q:int"
  let r ← q r"r:int"
  let dtm ← q r"(div)"
  let mtm ← q r"(rem)"
  let emod_num (x y : Rat) : Rat :=
    let r := mod_num x y
    if r < 0 then r + abs_num y else r
  let equo_num (x y : Rat) : Rat := quo_num (x - emod_num x y) y
  let INT_DIVMOD_CONV (x y : Rat) : ExceptT String IO thm := do
    let k := equo_num x y
    let l := emod_num x y
    let th0 ← INST [(← mk_intconst x, m), (← mk_intconst y, n),
                    (← mk_intconst k, q_), (← mk_intconst l, r)] pth
    let tm0 ← lhand (← lhand (concl th0))
    let th1 ← ((LAND_CONV INT_MUL_CONV THENC INT_ADD_CONV) tm0 : ExceptT String IO thm)
    let th2 ← MP th0 th1
    let tm2 ← lhand (concl th2)
    let th3 ← MP th2 (← EQT_ELIM (← INT_LE_CONV tm2))
    let tm3 ← lhand (concl th3)
    MP th3 (← EQT_ELIM (← (RAND_CONV INT_ABS_CONV THENC INT_LT_CONV) tm3))
  let INT_DIV_CONV (tm : term) : ExceptT String IO thm :=
    tryCatch (do
      let (l, r) ← dest_binop dtm tm
      CONJUNCT1 (← INT_DIVMOD_CONV (← dest_intconst l) (← dest_intconst r)))
     (fun _ => throw "INT_DIV_CONV")
  let INT_REM_CONV (tm : term) : ExceptT String IO thm :=
    tryCatch (do
      let (l, r) ← dest_binop mtm tm
      CONJUNCT2 (← INT_DIVMOD_CONV (← dest_intconst l) (← dest_intconst r)))
     (fun _ => throw "INT_MOD_CONV")
  return { INT_DIV_CONV := fun t => INT_DIV_CONV t, INT_REM_CONV := fun t => INT_REM_CONV t }

/-- `int_red_conv_list` (int.ml 1803). -/
def int_red_conv_list (Cc : IntCompareConvs) (Ar : IntArithConvs)
    (Dc : IntDivRemConvs) :
    ExceptT String IO (List (term × ioconv)) := do
  let { INT_LE_CONV, INT_LT_CONV, INT_GE_CONV, INT_GT_CONV, INT_EQ_CONV } := Cc
  let { INT_NEG_CONV, INT_SGN_CONV, INT_ABS_CONV, INT_ADD_CONV, INT_SUB_CONV,
        INT_MUL_CONV, INT_POW_CONV, INT_MAX_CONV, INT_MIN_CONV } := Ar
  let { INT_DIV_CONV, INT_REM_CONV } := Dc
  pure
    [(← q r"x <= y", INT_LE_CONV),
     (← q r"x < y", INT_LT_CONV),
     (← q r"x >= y", INT_GE_CONV),
     (← q r"x > y", INT_GT_CONV),
     (← q r"x:int = y", INT_EQ_CONV),
     (← q r"--x", CHANGED_CONV INT_NEG_CONV),
     (← q r"int_sgn(x)", INT_SGN_CONV),
     (← q r"abs(x)", INT_ABS_CONV),
     (← q r"x + y", INT_ADD_CONV),
     (← q r"x - y", INT_SUB_CONV),
     (← q r"x * y", INT_MUL_CONV),
     (← q r"x div y", INT_DIV_CONV),
     (← q r"x rem y", INT_REM_CONV),
     (← q r"x pow n", INT_POW_CONV),
     (← q r"max x y", INT_MAX_CONV),
     (← q r"min x y", INT_MIN_CONV)]

/-- `INT_RED_CONV` (int.ml 1821).  `basic_net()` is read once, here; Session
    builds this once. -/
def INT_RED_CONV (int_red_conv_list : List (term × ioconv)) :
    ExceptT String IO ioconv := do
  -- `itlist (uncurry net_of_conv) int_red_conv_list (basic_net())`
  let gconv_net ← int_red_conv_list.foldrM
    (fun (pat, cnv) net => (Simp.net_of_conv pat cnv net : ExceptT String IO _))
    (← (Simp.basic_net : IO (HolCore.Nets.net Simp.gconv)))
  return (Simp.REWRITES_CONV gconv_net)

/-- `INT_REDUCE_CONV` (int.ml 1826). -/
def INT_REDUCE_CONV (int_red_conv_list : List (term × ioconv)) :
    ExceptT String IO ioconv := do
  return (Simp.depthConvIO (← INT_RED_CONV int_red_conv_list))

/-- `int_compute_add_convs` (int.ml 1828). -/
def int_compute_add_convs (int_red_conv_list : List (term × ioconv))
    (cs : HolMath.Compute.compset) : ExceptT String IO Unit := do
  let convlist := int_red_conv_list.map fun (pat, the_conv) =>
    let (c, args) := strip_comb pat
    (c, args.length, the_conv)
  -- `itlist (fun newc () -> Compute.add_conv newc compset) convlist ()`
  convlist.foldrM (fun (c, n, cnv) () =>
    (HolMath.Compute.add_conv c (Int.ofNat n) cnv cs : ExceptT String IO Unit)) ()

/-- `INT_COMPUTE_CONV` (int.ml 1835).  Session builds this once. -/
def INT_COMPUTE_CONV (int_red_conv_list : List (term × ioconv))
    (bool_compset : IO (Except String HolMath.Compute.compset))
    (WEAK_CBV_CONV : HolMath.Compute.compset → ioconv) :
    ExceptT String IO ioconv := do
  let cs ← (bool_compset : ExceptT String IO _)
  (HolMath.Compute.set_skip cs (← q r"COND: bool -> A -> A -> A") (some 1)
    : ExceptT String IO Unit)
  int_compute_add_convs int_red_conv_list cs
  return (WEAK_CBV_CONV cs)

/- ---------------------------------------------------------------------- -/
/- Integer analogs of the usual even/odd combining theorems EVEN_ADD etc. -/
/- ---------------------------------------------------------------------- -/

structure IntEvenOdd where
  INT_2_DIVIDES_ADD : thm
  INT_2_DIVIDES_SUB : thm
  INT_2_DIVIDES_MUL : thm
  INT_2_DIVIDES_POW : thm
  deriving Inhabited

/-- int.ml 1844-1877. -/
@[nospecialize]
def setupIntEvenOdd [HolBase]
    (N : HolMath.Nums.NumsThms)
    (INT_REDUCE_CONV : ioconv)
    (Dr : IntDivRem1)
    (INT_POW NOT_SUC : thm) :
    ExceptT String IO IntEvenOdd := do
  let INDUCT_TAC := HolMath.Nums.INDUCT_TAC N.num_INDUCTION
  let { INT_REM_2_DIVIDES, INT_ADD_REM, INT_SUB_REM, INT_MUL_REM,
        INT_REM_2_CASES, .. } := Dr

  let INT_2_DIVIDES_ADD ← prove
   r"!m n:int. &2 divides (m + n) <=> (&2 divides m <=> &2 divides n)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM INT_REM_2_DIVIDES] THEN
    ONCE_REWRITE_TAC [← GSYM INT_ADD_REM] THEN
    DISJ_CASES_TAC (← SPEC (← q r"m:int") INT_REM_2_CASES) THEN
    DISJ_CASES_TAC (← SPEC (← q r"n:int") INT_REM_2_CASES) THEN
    ASM_REWRITE_TAC [] THEN CONV_TAC INT_REDUCE_CONV)

  let INT_2_DIVIDES_SUB ← prove
   r"!m n:int. &2 divides (m - n) <=> (&2 divides m <=> &2 divides n)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM INT_REM_2_DIVIDES] THEN
    ONCE_REWRITE_TAC [← GSYM INT_SUB_REM] THEN
    DISJ_CASES_TAC (← SPEC (← q r"m:int") INT_REM_2_CASES) THEN
    DISJ_CASES_TAC (← SPEC (← q r"n:int") INT_REM_2_CASES) THEN
    ASM_REWRITE_TAC [] THEN CONV_TAC INT_REDUCE_CONV)

  let INT_2_DIVIDES_MUL ← prove
   r"!m n:int. &2 divides (m * n) <=> &2 divides m \/ &2 divides n"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM INT_REM_2_DIVIDES] THEN
    ONCE_REWRITE_TAC [← GSYM INT_MUL_REM] THEN
    DISJ_CASES_TAC (← SPEC (← q r"m:int") INT_REM_2_CASES) THEN
    DISJ_CASES_TAC (← SPEC (← q r"n:int") INT_REM_2_CASES) THEN
    ASM_REWRITE_TAC [] THEN CONV_TAC INT_REDUCE_CONV)

  let INT_2_DIVIDES_POW ← prove
   r"!n k. &2 divides (n pow k) <=> &2 divides n /\ ~(k = 0)"
   (GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC [INT_POW] THENL
     [REWRITE_TAC [← GSYM (← CONJUNCT2 INT_REM_2_DIVIDES)] THEN
      CONV_TAC INT_REDUCE_CONV,
      ASM_REWRITE_TAC [INT_2_DIVIDES_MUL, NOT_SUC] THEN
      CONV_TAC TAUT])

  return { INT_2_DIVIDES_ADD, INT_2_DIVIDES_SUB, INT_2_DIVIDES_MUL,
           INT_2_DIVIDES_POW }

/- ---------------------------------------------------------------------- -/
/- Pushing and pulling to combine nested rem terms into a single rem.     -/
/- ---------------------------------------------------------------------- -/

/-- `let rec downconv tm = ...` inside INT_REM_DOWN_CONV (int.ml 1888). -/
partial def intRemDownConv (addmul_conv mod_conv : ioconv) : ioconv := fun tm =>
  let downconv := intRemDownConv addmul_conv mod_conv
  ((addmul_conv THENC LAND_CONV downconv) ORELSEC
   (mod_conv THENC downconv) ORELSEC
   SUB_CONV downconv) tm

structure IntRemConvs where
  INT_REM_DOWN_CONV : ioconv
  INT_POW_REM_CONV : ioconv
  deriving Inhabited

/-- int.ml 1880-1928. -/
@[nospecialize]
def setupIntRemConvs [HolBase]
    (Dr : IntDivRem1)
    (Dc : IntDivRemConvs)
    (Ar : IntArithConvs)
    (INT_POW_NEG INT_OF_NUM_CLAUSES COND_CLAUSES : thm)
    (NUM_EVEN_CONV : ioconv)
    (EXP_MOD_CONV : ioconv) :
    ExceptT String IO IntRemConvs := do
  let { INT_NEG_REM, INT_ADD_REM, INT_SUB_REM, INT_MUL_REM, INT_POW_REM,
        INT_REM_REM, INT_REM_RNEG, INT_OF_NUM_REM, .. } := Dr
  let { INT_REM_CONV, .. } := Dc
  let { INT_NEG_CONV, .. } := Ar

  let INT_REM_DOWN_CONV ← do
    let addmul_conv ← GEN_REWRITE_CONV_NET I
      [← GSYM INT_NEG_REM, ← GSYM INT_ADD_REM, ← GSYM INT_SUB_REM,
       ← GSYM INT_MUL_REM, ← GSYM INT_POW_REM]
    let mod_conv ← GEN_REWRITE_CONV_NET I [INT_REM_REM]
    let downconv := intRemDownConv addmul_conv mod_conv
    let upconv ←
      GEN_REWRITE_CONV_NET DEPTH_CONV
       [INT_NEG_REM, INT_ADD_REM, INT_SUB_REM, INT_MUL_REM,
        INT_POW_REM, INT_REM_REM]
    pure (downconv THENC upconv)

  /- Reduction of (a pow k) rem n keeping intermediates reduced. -/

  let INT_POW_REM_CONV ← do
    let (pth_0, pth_1) ← CONJ_PAIR (← prove
     r"((&m pow k) rem &n = &(m EXP k MOD n) /\
        (&m pow k) rem (-- &n) = &(m EXP k MOD n)) /\
       ((-- &m pow k) rem &n =
        if EVEN k then &(m EXP k MOD n) else (-- &(m EXP k MOD n)) rem &n) /\
       ((-- &m pow k) rem (-- &n) =
        if EVEN k then &(m EXP k MOD n) else (-- &(m EXP k MOD n)) rem &n)"
      (REWRITE_TAC [INT_REM_RNEG, INT_POW_NEG] THEN
       COND_CASES_TAC THEN
       ASM_REWRITE_TAC [← GSYM INT_OF_NUM_CLAUSES, ← GSYM INT_OF_NUM_REM] THEN
       CONV_TAC INT_REM_DOWN_CONV THEN REFL_TAC))
    let conv :=
      ((← GEN_REWRITE_CONV_NET I [pth_0]) THENC RAND_CONV EXP_MOD_CONV) ORELSEC
      ((← GEN_REWRITE_CONV_NET I [pth_1]) THENC
       RATOR_CONV (LAND_CONV NUM_EVEN_CONV) THENC
       (← GEN_REWRITE_CONV_NET I [COND_CLAUSES]) THENC
       (RAND_CONV EXP_MOD_CONV ORELSEC
        (LAND_CONV
         (RAND_CONV (RAND_CONV EXP_MOD_CONV THENC TRY_CONV INT_NEG_CONV)) THENC
          INT_REM_CONV)))
    pure fun (tm : term) =>
      match tm with
      | .Comb (.Comb (.Const "rem" _)
                (.Comb (.Comb (.Const "int_pow" _) m) k)) n =>
          if is_intconst m && HolMath.Nums.is_numeral k && is_intconst n then conv tm
          else pure (.error "INT_POW_REM_CONV")
      | _ => pure (.error "INT_POW_REM_CONV")

  return { INT_REM_DOWN_CONV, INT_POW_REM_CONV }

/- ---------------------------------------------------------------------- -/
/- Existence of integer gcd, and the Bezout identity.                     -/
/- ---------------------------------------------------------------------- -/

/-- int.ml 1929-2064.  `int_gcd` comes from `new_specification`, `int_lcm`
    from `new_definition`; the `overload_interface` calls for gcd and lcm run
    before them.  `INTEGER_TAC` and `INTEGER_RULE` are defined a second time
    here, eliminating gcd and lcm before the first version's procedure. -/
structure IntGcdLcm where
  /-- `WF_INT_MEASURE` (int.ml 1932). -/
  WF_INT_MEASURE : thm
  /-- `WF_INT_MEASURE_2` (int.ml 1939). -/
  WF_INT_MEASURE_2 : thm
  /-- `INT_GCD_EXISTS` (int.ml 1945): the Bezout identity. -/
  INT_GCD_EXISTS : thm
  /-- `INT_GCD_EXISTS_POS` (int.ml 1960): Bezout with a nonnegative gcd. -/
  INT_GCD_EXISTS_POS : thm
  /-- `int_gcd` (int.ml 1976), via `new_specification`. -/
  int_gcd : thm
  /-- `int_lcm` (int.ml 1979), via `new_definition`. -/
  int_lcm : thm
  INT_DIVIDES_LABS : thm
  INT_DIVIDES_RABS : thm
  INT_DIVIDES_ABS : thm
  INT_LCM_POS : thm
  INT_MUL_GCD_LCM : thm
  INT_MUL_LCM_GCD : thm
  INT_DIVIDES_LCM_GCD : thm
  INT_LCM_DIVIDES : thm
  INT_LCM : thm
  /-- `INTEGER_TAC` (int.ml 2045), the second version. -/
  INTEGER_TAC2 : tactic
  /-- `INTEGER_RULE` (int.ml 2064), the second version. -/
  INTEGER_RULE2 : term → IO (Except String thm)
  deriving Inhabited

@[nospecialize]
def setupIntGcdLcm [HolBase]
    (FORALL_PAIR_THM FORALL_UNCURRY : thm)
    (A1 : IntArith1)
    (Tc : IntTac1)
    (Dr : IntDivRem1)
    (num_WF : thm)
    (INT_OF_NUM_LT INT_FORALL_POS : thm)
    (INT_MUL_LZERO INT_ADD_LID INT_ADD_RID INT_MUL_RID : thm)
    (INT_LE_NEGTOTAL : thm)
    (INT_ABS INT_POS INT_ABS_POS INT_ABS_NUM INT_ABS_ZERO : thm)
    (INT_MUL_RZERO INT_MUL_SYM : thm)
    (EXISTS_UNCURRY SKOLEM_THM : thm)
    (MESON_TAC ASM_MESON_TAC : List thm → tactic)
    (overload_interface' : String → term → IO (Except String Unit))
    (new_specification' : List String → thm → IO (Except String thm))
    (new_definition' : term → IO (Except String thm)) :
    ExceptT String IO IntGcdLcm := do
  let overload_interface (s : String) (t : term) : ExceptT String IO Unit :=
    overload_interface' s t
  let new_specification (l : List String) (th : thm) : ExceptT String IO thm :=
    new_specification' l th
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let INT_ARITH (t : term) : ExceptT String IO thm := A1.INT_ARITH1 t
  let INT_ARITH_TAC := A1.INT_ARITH_TAC1
  let INTEGER_TAC := Tc.INTEGER_TAC1
  let INTEGER_RULE (t : term) : ExceptT String IO thm := Tc.INTEGER_RULE1 t
  let { INT_LE_DIV, INT_MUL_DIV_EQ, INT_DIVIDES_DIVIDES_DIV, INT_DIVIDES_DIV_DIVIDES,
        .. } := Dr
  let { MONO_EXISTS, .. } := HolBase.T

  let WF_INT_MEASURE ← prove
   r"!P m. (!x. &0 <= m(x)) /\ (!x. (!y. m(y) < m(x) ==> P(y)) ==> P(x))
         ==> !x:A. P(x)"
   (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"!n x:A. m(x) = &n ==> P(x)") MP_TAC THENL
     [MATCH_MP_TAC num_WF, ALL_TAC] THEN
    REWRITE_TAC [← GSYM INT_OF_NUM_LT, INT_FORALL_POS] THEN ASM_MESON_TAC [])

  let WF_INT_MEASURE_2 ← prove
   r"!P m. (!x y. &0 <= m x y) /\
         (!x y. (!x' y'. m x' y' < m x y ==> P x' y') ==> P x y)
         ==> !x:A y:B. P x y"
   (REWRITE_TAC [FORALL_UNCURRY, ← GSYM FORALL_PAIR_THM, WF_INT_MEASURE])

  -- The tactic's INTEGER_RULEs run (and print) right to left, as in OCaml.
  let INT_GCD_EXISTS ← prove
   r"!a b. ?d. d divides a /\ d divides b /\ ?x y. d = a * x + b * y"
   (← do
    let INT_GCD_EXISTS_CASES ← INT_ARITH
     (← q r"(a = &0 \/ b = &0) \/
      abs(a - b) + abs b < abs a + abs b \/ abs(a + b) + abs b < abs a + abs b \/
      abs a + abs(b - a) < abs a + abs b \/ abs a + abs(b + a) < abs a + abs b")
    let d_divides_d ← INTEGER_RULE (← q r"d divides d")
    let d_divides_0 ← INTEGER_RULE (← q r"d divides &0")
    pure
     (MATCH_MP_TAC WF_INT_MEASURE_2 THEN EXISTS_TAC (← q r"\x y. abs(x) + abs(y)") THEN
      REWRITE_TAC [] THEN REPEAT STRIP_TAC THENL [INT_ARITH_TAC, ALL_TAC] THEN
      DISJ_CASES_THEN MP_TAC INT_GCD_EXISTS_CASES THENL
       [STRIP_TAC THEN ASM_REWRITE_TAC [d_divides_0] THEN
        REWRITE_TAC [INT_MUL_LZERO, INT_ADD_LID, INT_ADD_RID] THEN
        MESON_TAC [d_divides_d, INT_MUL_RID],
        DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN (ANTE_RES_THEN MP_TAC)) THEN
        MATCH_MP_TAC MONO_EXISTS THEN INTEGER_TAC]))

  let INT_GCD_EXISTS_POS ← prove
   r"!a b. ?d. &0 <= d /\ d divides a /\ d divides b /\ ?x y. d = a * x + b * y"
   (← do
    let i1 ← INT_ARITH (← q r"a * --x + b * --y = --(a * x + b * y)")
    let n1 ← INTEGER_RULE (← q r"(--d) divides x <=> d divides x")
    pure
     (REPEAT GEN_TAC THEN
      X_CHOOSE_TAC (← q r"d:int") (← SPECL [← q r"a:int", ← q r"b:int"] INT_GCD_EXISTS) THEN
      DISJ_CASES_TAC (← SPEC (← q r"d:int") INT_LE_NEGTOTAL) THEN
      ASM_MESON_TAC [n1, i1]))

  /- ---------------------------------------------------------------------- -/
  /- Hence define (positive) integer gcd and lcm operations, with a few     -/
  /- basic properties of the latter; most analogous gcd ones get automated. -/
  /- ---------------------------------------------------------------------- -/

  overload_interface "gcd" (← q r"int_gcd:int#int->int")
  overload_interface "lcm" (← q r"int_lcm:int#int->int")

  let int_gcd ← new_specification ["int_gcd"]
    (← REWRITE_RULE [EXISTS_UNCURRY, SKOLEM_THM] INT_GCD_EXISTS_POS)

  let int_lcm ← new_definition
    r"int_lcm(m,n) = if m * n = &0 then &0 else abs(m * n) div gcd(m,n)"

  let INT_DIVIDES_LABS ← prove
   r"!d n. abs(d) divides n <=> d divides n"
   (REPEAT GEN_TAC THEN SIMP_TAC [INT_ABS] THEN COND_CASES_TAC THEN INTEGER_TAC)

  let INT_DIVIDES_RABS ← prove
   r"!d n. d divides (abs n) <=> d divides n"
   (REPEAT GEN_TAC THEN SIMP_TAC [INT_ABS] THEN COND_CASES_TAC THEN INTEGER_TAC)

  let INT_DIVIDES_ABS ← prove
   r"(!d n. abs(d) divides n <=> d divides n) /\
   (!d n. d divides (abs n) <=> d divides n)"
   (REWRITE_TAC [INT_DIVIDES_LABS, INT_DIVIDES_RABS])

  let INT_LCM_POS ← prove
   r"!m n. &0 <= lcm(m,n)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [int_lcm] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [INT_POS, INT_ABS_POS, INT_LE_DIV, int_gcd])

  let INT_MUL_GCD_LCM ← prove
   r"!m n:int. gcd(m,n) * lcm(m,n) = abs(m * n)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [int_lcm] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [INT_MUL_RZERO, INT_ABS_NUM] THEN
    REWRITE_TAC [INT_MUL_DIV_EQ] THEN REWRITE_TAC [INT_ABS] THEN
    ASM_MESON_TAC [int_gcd, ← INTEGER_RULE
     (← q r"d divides m ==> d divides (m * n:int) /\ d divides --(m * n)")])

  let INT_MUL_LCM_GCD ← prove
   r"!m n:int. lcm(m,n) * gcd(m,n) = abs(m * n)"
   (MESON_TAC [INT_MUL_SYM, INT_MUL_GCD_LCM])

  let INT_DIVIDES_LCM_GCD ← prove
   r"!m n d:int. d divides lcm(m,n) <=> d * gcd(m,n) divides m * n"
   (REPEAT GEN_TAC THEN REWRITE_TAC [int_lcm] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THENL [INTEGER_TAC, ALL_TAC] THEN
    W (MP_TAC o PART_MATCH (lhand o rand)
      INT_DIVIDES_DIVIDES_DIV o lhand o snd) THEN
    ASM_REWRITE_TAC [INT_ABS_ZERO, INT_DIVIDES_ABS] THEN ANTS_TAC THENL
     [MESON_TAC [int_gcd, ← INTEGER_RULE (← q r"d divides m ==> d divides (m * n:int)")],
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [INT_MUL_SYM]])

  let INT_LCM_DIVIDES ← prove
   r"!m n d:int. lcm(m,n) divides d <=> m divides d /\ n divides d"
   (REPEAT GEN_TAC THEN REWRITE_TAC [int_lcm] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THENL [INTEGER_TAC, ALL_TAC] THEN
    W (MP_TAC o PART_MATCH (lhand o rand)
      INT_DIVIDES_DIV_DIVIDES o lhand o snd) THEN
    ASM_REWRITE_TAC [INT_ABS_ZERO, INT_DIVIDES_ABS] THEN ANTS_TAC THENL
     [MESON_TAC [int_gcd, ← INTEGER_RULE (← q r"d divides m ==> d divides (m * n:int)")],
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC (← SPECL [← q r"m:int", ← q r"n:int"] int_gcd) THEN INTEGER_TAC)

  let INT_LCM ← prove
   r"!m n. m divides lcm(m,n) /\
         n divides lcm(m,n) /\
         (!d. m divides d /\ n divides d ==> lcm(m,n) divides d)"
   (REWRITE_TAC [INT_LCM_DIVIDES, INT_DIVIDES_LCM_GCD] THEN
    REPEAT GEN_TAC THEN MP_TAC (← SPECL [← q r"m:int", ← q r"n:int"] int_gcd) THEN
    INTEGER_TAC)

  /- ---------------------------------------------------------------------- -/
  /- Add their elimination to INTEGER_TAC (better for gcd at the moment).   -/
  /- ---------------------------------------------------------------------- -/

  let GCD_ELIM_TAC ← do
    let gcd_tm ← q r"gcd:int#int->int"
    let dest_gcd (tm : term) : Except String (term × term) := do
      let (l, r) ← dest_comb tm
      if l == gcd_tm then HolMath.Pair.dest_pair r else throw "dest_gcd"
    pure
     (REPEAT GEN_TAC THEN
      W (fun (_asl, w) => tactic_of do
            let gts := find_terms (can dest_gcd) w
            let ths ← gts.mapM (fun tm => do
              let (a, b) ← dest_gcd tm
              SPECL [a, b] int_gcd)
            pure
             (MAP_EVERY MP_TAC ths THEN
              MAP_EVERY SPEC_TAC (← zip gts (← gts.mapM (fun t =>
                liftM (genvar (type_of t) : IO term)))))))
  let pth ← prove
   r"!d a b:int. d divides gcd(a,b) <=> d divides a /\ d divides b"
    (GCD_ELIM_TAC THEN INTEGER_TAC)
  let INTEGER_TAC2 :=
    GEN_REWRITE_TAC TOP_DEPTH_CONV
     [pth, INT_DIVIDES_ABS, INT_DIVIDES_LCM_GCD, INT_LCM_DIVIDES] THEN
    REPEAT (GEN_TAC ORELSE CONJ_TAC) THEN GCD_ELIM_TAC THEN INTEGER_TAC

  let INTEGER_RULE2 (tm : term) : IO (Except String thm) :=
    HolCore.Tactics.prove HolBase.B tm INTEGER_TAC2

  return {
    WF_INT_MEASURE, WF_INT_MEASURE_2, INT_GCD_EXISTS, INT_GCD_EXISTS_POS,
    int_gcd, int_lcm, INT_DIVIDES_LABS, INT_DIVIDES_RABS, INT_DIVIDES_ABS,
    INT_LCM_POS, INT_MUL_GCD_LCM, INT_MUL_LCM_GCD, INT_DIVIDES_LCM_GCD,
    INT_LCM_DIVIDES, INT_LCM, INTEGER_TAC2, INTEGER_RULE2 }

/- ---------------------------------------------------------------------- -/
/- Mapping from nonnegative integers back to natural numbers.             -/
/- ---------------------------------------------------------------------- -/

structure IntNumOfInt where
  /-- `num_of_int` (int.ml 2071): `num_of_int x = @n. &n = x`. -/
  num_of_int : thm
  NUM_OF_INT_OF_NUM : thm
  INT_OF_NUM_OF_INT : thm
  NUM_OF_INT : thm
  NUM_OF_INT_ADD : thm
  NUM_OF_INT_MUL : thm
  NUM_OF_INT_POW : thm
  deriving Inhabited

/-- int.ml 2070-2104. -/
@[nospecialize]
def setupIntNumOfInt [HolBase]
    (INT_OF_NUM_EQ INT_OF_NUM_ADD INT_OF_NUM_MUL INT_OF_NUM_POW : thm)
    (INT_FORALL_POS INT_POS : thm)
    (RIGHT_FORALL_IMP_THM IMP_CONJ SWAP_FORALL_THM : thm)
    (SELECT_CONV' : term → Except String thm)
    (MESON_TAC : List thm → tactic)
    (new_definition' : term → IO (Except String thm)) :
    ExceptT String IO IntNumOfInt := do
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let SELECT_CONV : ioconv := fun t => pure (SELECT_CONV' t)
  let { SELECT_UNIQUE, .. } := HolBase.C

  let num_of_int ← new_definition
    r"num_of_int x = @n. &n = x"

  let NUM_OF_INT_OF_NUM ← prove
   r"!n. num_of_int(&n) = n"
   (REWRITE_TAC [num_of_int, INT_OF_NUM_EQ, SELECT_UNIQUE])

  let INT_OF_NUM_OF_INT ← prove
   r"!x. &0 <= x ==> &(num_of_int x) = x"
   (REWRITE_TAC [← GSYM INT_FORALL_POS, num_of_int] THEN
    GEN_TAC THEN CONV_TAC SELECT_CONV THEN MESON_TAC [])

  let NUM_OF_INT ← prove
   r"!x. &0 <= x <=> (&(num_of_int x) = x)"
   (MESON_TAC [INT_OF_NUM_OF_INT, INT_POS])

  let NUM_OF_INT_ADD ← prove
   r"!x y. &0 <= x /\ &0 <= y
         ==> num_of_int(x + y) = num_of_int x + num_of_int y"
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM, IMP_CONJ] THEN
    REWRITE_TAC [← GSYM INT_FORALL_POS, INT_OF_NUM_ADD, NUM_OF_INT_OF_NUM])

  let NUM_OF_INT_MUL ← prove
   r"!x y. &0 <= x /\ &0 <= y
         ==> num_of_int(x * y) = num_of_int x * num_of_int y"
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM, IMP_CONJ] THEN
    REWRITE_TAC [← GSYM INT_FORALL_POS, INT_OF_NUM_MUL, NUM_OF_INT_OF_NUM])

  let NUM_OF_INT_POW ← prove
   r"!x n. &0 <= x ==> num_of_int(x pow n) = num_of_int x EXP n"
   (GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN
    REWRITE_TAC [← GSYM INT_FORALL_POS, INT_OF_NUM_POW, NUM_OF_INT_OF_NUM])

  return { num_of_int, NUM_OF_INT_OF_NUM, INT_OF_NUM_OF_INT, NUM_OF_INT,
           NUM_OF_INT_ADD, NUM_OF_INT_MUL, NUM_OF_INT_POW }

/- ---------------------------------------------------------------------- -/
/- Now define similar notions over the natural numbers.                   -/
/- ---------------------------------------------------------------------- -/

/-- int.ml 2107-2149.  The `overload_interface` calls run before the
    definitions, so that their statements parse the symbols as constants. -/
structure IntNumNotions where
  /-- `num_divides` (int.ml 2114): `a divides b <=> &a divides &b`. -/
  num_divides : thm
  /-- `num_mod` (int.ml 2117): `(mod n) x y <=> (mod &n) (&x) (&y)`. -/
  num_mod : thm
  /-- `num_congruent` (int.ml 2120): `(x == y) (mod n) <=> (&x == &y) (mod &n)`.-/
  num_congruent : thm
  /-- `num_coprime` (int.ml 2124): `coprime(a,b) <=> coprime(&a,&b)`. -/
  num_coprime : thm
  /-- `num_gcd` (int.ml 2127): `gcd(a,b) = num_of_int(gcd(&a,&b))`. -/
  num_gcd : thm
  /-- `num_lcm` (int.ml 2130): `lcm(a,b) = num_of_int(lcm(&a,&b))`. -/
  num_lcm : thm
  /-- `NUM_TO_INT_CONV` (int.ml 2138). -/
  NUM_TO_INT_CONV : ioconv
  deriving Inhabited

@[nospecialize]
def setupIntNumNotions [HolBase]
    (cong : thm)
    (INT_EXISTS_POS INT_FORALL_POS : thm)
    (INT_OF_NUM_EQ INT_OF_NUM_LE INT_OF_NUM_LT INT_OF_NUM_GE INT_OF_NUM_GT : thm)
    (INT_OF_NUM_SUC INT_OF_NUM_ADD INT_OF_NUM_MUL INT_OF_NUM_POW : thm)
    (NUM_SIMPLIFY_CONV : ioconv)
    (MESON_TAC : List thm → tactic)
    (overload_interface' : String → term → IO (Except String Unit))
    (new_definition' : term → IO (Except String thm)) :
    ExceptT String IO IntNumNotions := do
  let overload_interface (s : String) (t : term) : ExceptT String IO Unit :=
    overload_interface' s t
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)

  overload_interface "divides" (← q r"num_divides:num->num->bool")
  overload_interface "mod" (← q r"num_mod:num->num->num->bool")
  overload_interface "coprime" (← q r"num_coprime:num#num->bool")
  overload_interface "gcd" (← q r"num_gcd:num#num->num")
  overload_interface "lcm" (← q r"num_lcm:num#num->num")

  let num_divides ← new_definition
   r"a divides b <=> &a divides &b"

  let num_mod ← new_definition
    r"(mod n) x y <=> (mod &n) (&x) (&y)"

  let num_congruent ← prove
   r"!x y n. (x == y) (mod n) <=> (&x == &y) (mod &n)"
   (REWRITE_TAC [cong, num_mod])

  let num_coprime ← new_definition
   r"coprime(a,b) <=> coprime(&a,&b)"

  let num_gcd ← new_definition
   r"gcd(a,b) = num_of_int(gcd(&a,&b))"

  let num_lcm ← new_definition
   r"lcm(a,b) = num_of_int(lcm(&a,&b))"

  /- ---------------------------------------------------------------------- -/
  /- Map an assertion over N to an integer equivalent.                      -/
  /- To make this work nicely, all variables of type num should be          -/
  /- quantified.                                                            -/
  /- ---------------------------------------------------------------------- -/

  let NUM_TO_INT_CONV ← do
    let pth_relativize ← prove
     r"((!n. P(&n)) <=> (!i. ~(&0 <= i) \/ P i)) /\
       ((?n. P(&n)) <=> (?i. &0 <= i /\ P i))"
      (REWRITE_TAC [INT_EXISTS_POS, INT_FORALL_POS] THEN MESON_TAC [])
    let relation_conv ← GEN_REWRITE_CONV_NET TOP_SWEEP_CONV (← [INT_OF_NUM_EQ, INT_OF_NUM_LE,
      INT_OF_NUM_LT, INT_OF_NUM_GE, INT_OF_NUM_GT, INT_OF_NUM_SUC, INT_OF_NUM_ADD,
      INT_OF_NUM_MUL, INT_OF_NUM_POW].mapM GSYM)
    let quantifier_conv ← GEN_REWRITE_CONV_NET DEPTH_CONV [pth_relativize]
    pure (NUM_SIMPLIFY_CONV THENC relation_conv THENC quantifier_conv)

  return { num_divides, num_mod, num_congruent, num_coprime, num_gcd, num_lcm,
           NUM_TO_INT_CONV }

/- ---------------------------------------------------------------------- -/
/- Linear decision procedure for the naturals at last!                    -/
/- ---------------------------------------------------------------------- -/

/-- int.ml 2153-2189.  `INT_ARITH` here is still the first version. -/
structure IntArithRule where
  /-- `ARITH_RULE` (int.ml 2153). -/
  ARITH_RULE : term → IO (Except String thm)
  /-- `ARITH_TAC` (int.ml 2183). -/
  ARITH_TAC : tactic
  /-- `ASM_ARITH_TAC` (int.ml 2185). -/
  ASM_ARITH_TAC : tactic
  deriving Inhabited

@[nospecialize]
def setupIntArithRule [HolBase]
    (INT_ARITH' : term → IO (Except String thm))
    (INT_POS : thm)
    (INT_OF_NUM_EQ INT_OF_NUM_LE INT_OF_NUM_LT INT_OF_NUM_GE INT_OF_NUM_GT : thm)
    (INT_OF_NUM_ADD INT_OF_NUM_MUL INT_OF_NUM_MAX INT_OF_NUM_MIN : thm)
    (ADD1 : thm)
    (NUM_SIMPLIFY_CONV NUM_NORMALIZE_CONV : ioconv)
    (PRENEX_CONV : term → IO (Except String thm)) :
    ExceptT String IO IntArithRule := do
  let INT_ARITH (t : term) : ExceptT String IO thm := INT_ARITH' t
  let init_conv :=
    NUM_SIMPLIFY_CONV THENC
    (← GEN_REWRITE_CONV_NET DEPTH_CONV [ADD1]) THENC
    HolCore.Canon.PROP_ATOM_CONV (BINOP_CONV NUM_NORMALIZE_CONV) THENC
    PRENEX_CONV THENC
    (← GEN_REWRITE_CONV_NET TOP_SWEEP_CONV (← [INT_OF_NUM_EQ, INT_OF_NUM_LE, INT_OF_NUM_LT,
      INT_OF_NUM_GE, INT_OF_NUM_GT, INT_OF_NUM_ADD,
      ← SPEC (← q r"NUMERAL k") INT_OF_NUM_MUL,
      INT_OF_NUM_MAX, INT_OF_NUM_MIN].mapM GSYM))
  let is_numimage (t : term) : Bool :=
    match t with
    | .Comb (.Const "int_of_num" _) n => !(HolMath.Nums.is_numeral n)
    | _ => false
  let ARITH_RULE (tm : term) : ExceptT String IO thm :=
    tryCatch (do
      let th1 ← (init_conv tm : ExceptT String IO thm)
      let tm1 ← rand (concl th1)
      let (avs, bod) := strip_forall tm1
      let nim := setify (find_terms is_numimage bod)
      let gvs ← nim.mapM (fun v => liftM (genvar (type_of v) : IO term))
      let pths ← nim.mapM (fun v => do SPEC (← rand v) INT_POS)
      let ibod ← (pths.foldrM (fun th b => mk_imp (concl th) b) bod : Except String term)
      let gbod ← (← (subst (← zip gvs nim) : ExceptT String IO (term → IO (Except String term)))) ibod
      let th2 ← INST (← zip nim gvs) (← INT_ARITH gbod)
      let th3 ← GENL avs (← pths.foldlM (fun th p => MP th p) th2)
      EQ_MP (← SYM th1) th3)
    (fun msg => do
      throw ("ARITH_RULE `" ++ (← liftM (HolCore.Printer.string_of_term tm)) ++ "`: " ++ msg))

  let ARITH_TAC := CONV_TAC (EQT_INTRO o ARITH_RULE)

  let ASM_ARITH_TAC :=
    REPEAT (FIRST_X_ASSUM (MP_TAC o check (not o is_forall o concl))) THEN
    ARITH_TAC

  return { ARITH_RULE := fun t => ARITH_RULE t, ARITH_TAC, ASM_ARITH_TAC }

/- ---------------------------------------------------------------------- -/
/- Enhanced integer procedures eliminating div and rem (replacing first   -/
/- one).                                                                  -/
/- ---------------------------------------------------------------------- -/

/-- `let rec rule tm = ...` inside INT_POS_RULE (int.ml 2215). -/
private partial def intPosRule [HolBase]
    (pth_pos pth_add pth_mul pth_pow : thm) (x_tm y_tm n_tm : term)
    (tm : term) : Except String thm := do
  let rule := intPosRule pth_pos pth_add pth_mul pth_pow x_tm y_tm n_tm
  let B := HolBase.B
  match tm with
  | .Comb (.Const "int_of_num" _) rtm => HolCore.Kernel.INST [(rtm, n_tm)] pth_pos
  | .Comb (.Comb (.Const "int_add" _) ltm) rtm =>
      let lth ← rule ltm
      let rth ← rule rtm
      B.MP (← HolCore.Kernel.INST [(ltm, x_tm), (rtm, y_tm)] pth_add) (← B.CONJ lth rth)
  | .Comb (.Comb (.Const "int_mul" _) ltm) rtm =>
      let lth ← rule ltm
      let rth ← rule rtm
      B.MP (← HolCore.Kernel.INST [(ltm, x_tm), (rtm, y_tm)] pth_mul) (← B.CONJ lth rth)
  | .Comb (.Comb (.Const "int_pow" _) ltm) rtm =>
      let lth ← rule ltm
      B.MP (← HolCore.Kernel.INST [(ltm, x_tm), (rtm, n_tm)] pth_pow) lth
  | _ => throw "INT_POS_RULE"

/-- The closed-over values of INT_DIVREM_ELIM_CONV's `conv` (int.ml 2251-2266). -/
private structure DivremElim where
  INT_POS_RULE : term → Except String thm
  DIVREM_ELIM_THM_POS : thm
  DIVREM_ELIM_THM : thm
  BETA2_CONV : ioconv
  INT_REDUCE_CONV : ioconv
  div_tm : term
  rem_tm : term
  p_tm : term
  m_tm : term
  n_tm : term
  is_divrem : term → Bool

/-- `let rec conv tm = ...` inside INT_DIVREM_ELIM_CONV (int.ml 2267). -/
private partial def divremElimConv [HolBase] (E : DivremElim) (tm : term) :
    IO (Except String thm) := ExceptT.run do
  let { INT_POS_RULE, DIVREM_ELIM_THM_POS, DIVREM_ELIM_THM, BETA2_CONV,
        INT_REDUCE_CONV, div_tm, rem_tm, p_tm, m_tm, n_tm, is_divrem } := E
  let conv := divremElimConv E
  tryCatch (do
    let t ← hd (sort free_in
         (find_terms (fun t => is_divrem t && free_in t tm) tm))
    let x ← lhand t
    let y ← rand t
    let dtm ← mk_comb (← mk_comb div_tm x) y
    let rtm ← mk_comb (← mk_comb rem_tm x) y
    let vd ← liftM (genvar (type_of dtm) : IO term)
    let vr ← liftM (genvar (type_of rtm) : IO term)
    let p ← list_mk_abs [vd, vr]
              (← (← (subst [(vd, dtm), (vr, rtm)]
                    : ExceptT String IO (term → IO (Except String term)))) tm)
    let th0 ← INST [(p, p_tm), (x, m_tm), (y, n_tm)] DIVREM_ELIM_THM_POS
    let th1 ← tryCatch (do
        let (ltm, rtm) ← dest_conj (← lhand (concl th0))
        MP th0 (← CONJ (← INT_POS_RULE (← rand ltm)) (← INT_POS_RULE (← rand rtm))))
      (fun _ => do INST [(p, p_tm), (x, m_tm), (y, n_tm)] DIVREM_ELIM_THM)
    let th2 ← CONV_RULE (COMB2_CONV (RAND_CONV BETA2_CONV)
         (funpow 2 BINDER_CONV (RAND_CONV BETA2_CONV))) th1
    let th3 ← CONV_RULE (RAND_CONV
               (funpow 2 BINDER_CONV INT_REDUCE_CONV)) th2
    CONV_RULE (RAND_CONV (BINDER_CONV (BINDER_CONV (RAND_CONV conv)))) th3)
   (fun _ => pure (REFL tm))

/-- `let rec topconv tm = ...` inside INT_DIVREM_ELIM_CONV (int.ml 2292). -/
private partial def divremElimTopConv [HolBase] (E : DivremElim) : ioconv := fun tm =>
  if is_forall tm || is_exists tm then BINDER_CONV (divremElimTopConv E) tm
  else divremElimConv E tm

/-- `INT_ARITH`, `INT_ARITH_TAC` and `ASM_INT_ARITH_TAC` (int.ml 2193-2321),
    the second versions: `init_CONV` also reduces constants and eliminates
    `div` and `rem`, and failures are reported with the term. -/
structure IntArith2 where
  INT_ARITH2 : term → IO (Except String thm)
  INT_ARITH_TAC2 : tactic
  ASM_INT_ARITH_TAC2 : tactic
  deriving Inhabited

/-- `REAL_ARITH` is calc_rat.ml's final one (Session's `REAL_ARITH3`). -/
@[nospecialize]
def setupIntArith2 [HolBase] (P : HolCore.Canon.NNFPths)
    (A1 : IntArith1)
    (O : IntOps) (int_eq : thm)
    (INT_NOT_LE INT_NOT_LT INT_NOT_EQ : thm)
    (INT_POS INT_LE_ADD INT_LE_MUL INT_POW_LE : thm)
    (INT_ABS_NUM INT_LET_ANTISYM INT_DIV_0 INT_REM_0 : thm)
    (INT_DIVISION INT_LE_DIV INT_DIVMOD_UNIQ : thm)
    (PRESIMP_CONV NNF_CONV CONDS_ELIM_CONV INT_REDUCE_CONV : ioconv)
    (REAL_ARITH : term → IO (Except String thm))
    (ASM_METIS_TAC : List thm → tactic) :
    ExceptT String IO IntArith2 := do
  let { int_le, int_lt, int_ge, int_gt, int_of_num_th, int_neg_th, int_add_th,
        int_mul_th, int_sub_th, int_pow_th, int_abs_th, int_max_th, int_min_th,
        INT_LT_DISCRETE, .. } := O
  let { INT_GT, INT_GE, INT_ABS, .. } := A1
  let { UNWIND_THM2, CONJ_ASSOC, RIGHT_EXISTS_AND_THM, .. } := HolBase.T

  -- let INT_ARITH =
  let atom_CONV ←
    GEN_REWRITE_CONV_NET I [← prove
      r"(~(x:int <= y) <=> y + &1 <= x) /\
        (~(x < y) <=> y <= x) /\
        (~(x = y) <=> x + &1 <= y \/ y + &1 <= x) /\
        (x < y <=> x + &1 <= y)"
      (REWRITE_TAC [INT_NOT_LE, INT_NOT_LT, INT_NOT_EQ, INT_LT_DISCRETE])]
  let bub_CONV ← GEN_REWRITE_CONV_NET TOP_SWEEP_CONV
   [int_eq, int_le, int_lt, int_ge, int_gt,
    int_of_num_th, int_neg_th, int_add_th, int_mul_th,
    int_sub_th, int_pow_th, int_abs_th, int_max_th, int_min_th]
  let base_CONV := TRY_CONV atom_CONV THENC bub_CONV
  let NNF_NORM_CONV := HolCore.Canon.GEN_NNF_CONV HolBase.B P false
   base_CONV (fun t => ExceptT.run do
     let n ← (base_CONV (← mk_neg t) : ExceptT String IO thm)
     pure ((← (base_CONV t : ExceptT String IO thm)), n))
  let INT_POS_RULE ← do
    let x_tm ← q r"x:int"
    let y_tm ← q r"y:int"
    let n_tm ← q r"n:num"
    let pth_pos ← SPEC n_tm INT_POS
    let pth_add ← SPECL [x_tm, y_tm] INT_LE_ADD
    let pth_mul ← SPECL [x_tm, y_tm] INT_LE_MUL
    let pth_pow ← SPECL [x_tm, n_tm] INT_POW_LE
    pure (intPosRule pth_pos pth_add pth_mul pth_pow x_tm y_tm n_tm)
  let INT_DIVREM_ELIM_CONV ← do
    let tac :=
      REWRITE_TAC [← GSYM INT_LT_DISCRETE] THEN
      ASM_CASES_TAC (← q r"n:int = &0") THEN ASM_REWRITE_TAC [] THENL
       [ASM_REWRITE_TAC [INT_ABS_NUM, INT_LET_ANTISYM] THEN
        REWRITE_TAC [UNWIND_THM2, ← GSYM CONJ_ASSOC, RIGHT_EXISTS_AND_THM] THEN
        REWRITE_TAC [INT_DIV_0, INT_REM_0],
        EQ_TAC THEN STRIP_TAC THENL
         [MAP_EVERY EXISTS_TAC [← q r"m div n", ← q r"m rem n"] THEN
          ASM_SIMP_TAC [INT_DIVISION, INT_LE_DIV],
          ASM_METIS_TAC [INT_DIVMOD_UNIQ]]]
    let DIVREM_ELIM_THM ← prove
     r"P (m div n) (m rem n) <=>
       ?q r. (n = &0 /\ q = &0 /\ r = m \/
              m = q * n + r /\
              &0 <= r /\ r + &1 <= abs n) /\
             P q r"
      tac
    let DIVREM_ELIM_THM' ← prove
     r"P (m div n) (m rem n) <=>
       ?q r. (n = &0 /\ q = &0 /\ r = m \/
              m = q * n + r /\
              (&0 <= m /\ &0 <= n ==> &0 <= q) /\
              &0 <= r /\ r + &1 <= abs n) /\
             P q r"
      tac
    let DIVREM_ELIM_THM_POS ← prove
     r"&0 <= m /\ &0 <= n
       ==> (P (m div n) (m rem n) <=>
            ?q r. (n = &0 /\ q = &0 /\ r = m \/
                   m = q * n + r /\
                   &0 <= q /\
                   &0 <= r /\ r + &1 <= n) /\
                  P q r)"
      (SIMP_TAC [DIVREM_ELIM_THM', INT_ABS])
    let BETA2_CONV := RATOR_CONV BETA_CONV THENC BETA_CONV
    let div_tm ← q r"(div):int->int->int"
    let rem_tm ← q r"(rem):int->int->int"
    let p_tm ← q r"P:int->int->bool"
    let m_tm ← q r"m:int"
    let n_tm ← q r"n:int"
    let is_divrem :=
      let is_div := is_binop div_tm
      let is_rem := is_binop rem_tm
      fun tm => is_div tm || is_rem tm
    pure (divremElimTopConv
      { INT_POS_RULE := INT_POS_RULE, DIVREM_ELIM_THM_POS := DIVREM_ELIM_THM_POS,
        DIVREM_ELIM_THM := DIVREM_ELIM_THM, BETA2_CONV := BETA2_CONV,
        INT_REDUCE_CONV := INT_REDUCE_CONV, div_tm := div_tm, rem_tm := rem_tm,
        p_tm := p_tm, m_tm := m_tm, n_tm := n_tm, is_divrem := is_divrem })
  let init_CONV :=
    TOP_DEPTH_CONV BETA_CONV THENC
    PRESIMP_CONV THENC
    (← GEN_REWRITE_CONV_NET DEPTH_CONV [INT_GT, INT_GE]) THENC
    NNF_CONV THENC DEPTH_BINOP_CONV (← q r"(\/)") CONDS_ELIM_CONV THENC
    INT_REDUCE_CONV THENC INT_DIVREM_ELIM_CONV THENC
    NNF_NORM_CONV
  let p_tm ← q r"p:bool"
  let not_tm ← q r"(~)"
  let pth ← TAUT (safe_mk_eq (← mk_neg (← mk_neg p_tm)) p_tm)
  let INT_ARITH2 (tm : term) : ExceptT String IO thm :=
    tryCatch (do
      let th0 ← INST [(tm, p_tm)] pth
      let th1 ← (init_CONV (← mk_neg tm) : ExceptT String IO thm)
      let th2 ← (REAL_ARITH (← mk_neg (← rand (concl th1))) : ExceptT String IO thm)
      EQ_MP th0 (← EQ_MP (← AP_TERM not_tm (← SYM th1)) th2))
    (fun m => do
      throw ("INT_ARITH `" ++ (← liftM (HolCore.Printer.string_of_term tm)) ++ "`: " ++ m))

  let INT_ARITH_TAC2 := CONV_TAC (EQT_INTRO o INT_ARITH2)

  let ASM_INT_ARITH_TAC2 :=
    REPEAT (FIRST_X_ASSUM (MP_TAC o check (not o is_forall o concl))) THEN
    INT_ARITH_TAC2

  return { INT_ARITH2 := fun t => INT_ARITH2 t, INT_ARITH_TAC2, ASM_INT_ARITH_TAC2 }

/- ---------------------------------------------------------------------- -/
/- A few miscellaneous natural number lemmas.                             -/
/- ---------------------------------------------------------------------- -/

structure IntMiscNat where
  BINARY_INDUCT : thm
  NUM_CASES_BINARY : thm
  num_WF_DOWN : thm
  INT_REM_REM_POW_MIN : thm
  deriving Inhabited

/-- int.ml 2326-2375.  `ASM_INT_ARITH_TAC` is the second version. -/
@[nospecialize]
def setupIntMiscNat [HolBase]
    (Ar : IntArithRule) (A2 : IntArith2)
    (num_WF LE_0 LE_EXISTS NOT_LE LT_IMP_LE : thm)
    (INT_REM_ZERO INT_POW_ZERO INT_REM_0 INT_REM_1 : thm)
    (INT_POW_ADD INT_REM_REM_MUL INT_REM_REM_LE : thm)
    (INT_POW_EQ_0 INT_ABS_POW INT_POW_MONO : thm)
    (MESON_TAC ASM_MESON_TAC : List thm → tactic) :
    ExceptT String IO IntMiscNat := do
  let ARITH_RULE (t : term) : ExceptT String IO thm := Ar.ARITH_RULE t
  let ASM_ARITH_TAC := Ar.ASM_ARITH_TAC
  let ASM_INT_ARITH_TAC := A2.ASM_INT_ARITH_TAC2

  let BINARY_INDUCT ← prove
   r"!P. P 0 /\ (!n. P n ==> P(2 * n) /\ P(2 * n + 1)) ==> !n. P n"
   (GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC num_WF THEN GEN_TAC THEN
    STRIP_ASSUME_TAC (← ARITH_RULE
     (← q r"n = 0 \/ n DIV 2 < n /\ (n = 2 * n DIV 2 \/ n = 2 * n DIV 2 + 1)")) THEN
    ASM_MESON_TAC [])

  let NUM_CASES_BINARY ← prove
   r"!P. (!n. P n) <=> (!n. P(2 * n)) /\ (!n. P(2 * n + 1))"
   (MESON_TAC [← ARITH_RULE (← q r"n = 2 * n DIV 2 \/ n = 2 * n DIV 2 + 1")])

  let num_WF_DOWN ← prove
   r"!P m:num.
        (!n. m <= n ==> P n) /\
        (!n. n < m /\ (!p. n < p ==> P p) ==> P n)
        ==> (!n. P n)"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_CASES_TAC (← q r"m = 0") THENL [ASM_MESON_TAC [LE_0], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!i. P(m - 1 - i)") MP_TAC THENL
     [MATCH_MP_TAC num_WF THEN GEN_TAC THEN
      DISCH_THEN (fun th => FIRST_X_ASSUM MATCH_MP_TAC THEN ASSUME_TAC th) THEN
      CONJ_TAC THENL [ASM_ARITH_TAC, X_GEN_TAC (← q r"p:num")] THEN
      ASM_CASES_TAC (← q r"m:num <= p") THEN ASM_SIMP_TAC [] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"m - 1 - p")) THEN
      ASM_SIMP_TAC [← ARITH_RULE
       (← q r"~(m <= p) ==> m - 1 - (m - 1 - p) = p")] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC,
      ASM_MESON_TAC [← ARITH_RULE (← q r"~(m <= n) ==> n = m - 1 - (m - 1 - n)")]])

  let INT_REM_REM_POW_MIN ← prove
   r"!x p m n. x rem (p pow m) rem (p pow n) = x rem (p pow MIN m n)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"x:int = &0") THEN
    ASM_REWRITE_TAC [INT_REM_ZERO] THEN ASM_CASES_TAC (← q r"p:int = &0") THENL
     [ASM_REWRITE_TAC [INT_POW_ZERO, ← ARITH_RULE
       (← q r"MIN a b = 0 <=> a = 0 \/ b = 0")] THEN
      MAP_EVERY ASM_CASES_TAC [← q r"m = 0", ← q r"n = 0"] THEN
      ASM_REWRITE_TAC [INT_REM_0, INT_REM_1],
      REWRITE_TAC [← ARITH_RULE (← q r"MIN m n = if n <= m then n else m")]] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THENL
     [FIRST_X_ASSUM (CHOOSE_THEN SUBST1_TAC o GEN_REWRITE_RULE I [LE_EXISTS]) THEN
      REWRITE_TAC [INT_POW_ADD, INT_REM_REM_MUL],
      RULE_ASSUM_TAC (REWRITE_RULE [NOT_LE])] THEN
    MATCH_MP_TAC INT_REM_REM_LE THEN
    ASM_REWRITE_TAC [INT_POW_EQ_0, INT_ABS_POW] THEN
    MATCH_MP_TAC INT_POW_MONO THEN ASM_SIMP_TAC [LT_IMP_LE] THEN
    ASM_INT_ARITH_TAC)

  return { BINARY_INDUCT, NUM_CASES_BINARY, num_WF_DOWN, INT_REM_REM_POW_MIN }

/- ---------------------------------------------------------------------- -/
/- Also a similar divisibility procedure for natural numbers.             -/
/- ---------------------------------------------------------------------- -/

/-- `let rec antisym_conv tm = ...` inside NUMBER_TAC (int.ml 2505). -/
private partial def numberAntisymConv [HolBase] (conva : ioconv) : ioconv := fun tm =>
  let antisym_conv := numberAntisymConv conva
  if is_forall tm || is_exists tm then BINDER_CONV antisym_conv tm
  else if is_conj tm || is_disj tm then BINOP_CONV antisym_conv tm
  else if is_imp tm then RAND_CONV antisym_conv tm
  else conva tm

/-- int.ml 2378-2566. -/
structure IntNumber where
  NUM_GCD : thm
  NUM_LCM : thm
  CONG : thm
  CONG_LMOD : thm
  CONG_RMOD : thm
  CONG_DIV2 : thm
  divides : thm
  DIVIDES_LE : thm
  DIVIDES_LE_STRONG : thm
  DIVIDES_LE_IMP : thm
  PROPERLY_DIVIDES_LE_IMP : thm
  DIVIDES_ANTISYM : thm
  DIVIDES_ONE : thm
  DIV_ADD : thm
  DIVIDES_MOD : thm
  DIVIDES_DIV_MULT : thm
  DIV_BY_DIV : thm
  DIVIDES_DIV_DIVIDES : thm
  DIVIDES_DIV_SELF : thm
  DIVIDES_DIVIDES_DIV : thm
  DIVIDES_DIVIDES_DIV_EQ : thm
  DIVIDES_DIVIDES_DIV_IMP : thm
  MULT_DIV : thm
  /-- `NUMBER_TAC` (int.ml 2503). -/
  NUMBER_TAC : tactic
  /-- `NUMBER_RULE` (int.ml 2528). -/
  NUMBER_RULE : term → IO (Except String thm)
  COPRIME_LMOD : thm
  COPRIME_RMOD : thm
  INT_CONG_NUM_EXISTS : thm
  GCD : thm
  coprime : thm
  deriving Inhabited

/-- `INT_ARITH`, `INTEGER_TAC` etc. are the second versions here. -/
@[nospecialize]
def setupIntNumber [HolBase]
    (A1 : IntArith1) (A2 : IntArith2) (G : IntGcdLcm) (Ar : IntArithRule)
    (Nn : IntNumNotions) (NoI : IntNumOfInt)
    (int_divides : thm)
    (INT_OF_NUM_EQ INT_OF_NUM_LE INT_OF_NUM_LT INT_OF_NUM_GE INT_OF_NUM_GT : thm)
    (INT_OF_NUM_SUC INT_OF_NUM_ADD INT_OF_NUM_MUL INT_OF_NUM_POW : thm)
    (INT_OF_NUM_DIV INT_REM_EQ INT_OF_NUM_REM : thm)
    (INT_ABS_POS INT_ABS_ABS INT_ABS_MUL INT_ABS INT_LE_LMUL : thm)
    (INT_MUL_DIV_EQ INT_DIV_BY_DIV : thm)
    (INT_DIVIDES_DIV_DIVIDES INT_DIVIDES_DIV_SELF : thm)
    (INT_DIVIDES_DIVIDES_DIV INT_DIVIDES_DIVIDES_DIV_EQ : thm)
    (DIV_MOD MOD_MOD_REFL MOD_EQ_0 DIV_ZERO DIV_MULT_ADD DIV_MULT DIV_0 : thm)
    (ADD_CLAUSES MULT_CLAUSES MULT_EQ_1 MULT_EQ_0 LE_MULT_LCANCEL : thm)
    (MULT_SYM MULT_ASSOC LE_1 LE_0 LE_REFL : thm)
    (NUM_RING' : term → IO (Except String thm))
    (MESON_TAC : List thm → tactic) :
    ExceptT String IO IntNumber := do
  let NUM_RING (t : term) : ExceptT String IO thm := NUM_RING' t
  let ARITH_RULE (t : term) : ExceptT String IO thm := Ar.ARITH_RULE t
  let ARITH_TAC := Ar.ARITH_TAC
  let ASM_ARITH_TAC := Ar.ASM_ARITH_TAC
  let INT_ARITH (t : term) : ExceptT String IO thm := A2.INT_ARITH2 t
  let ASM_INT_ARITH_TAC := A2.ASM_INT_ARITH_TAC2
  let INTEGER_TAC := G.INTEGER_TAC2
  let INTEGER_RULE (t : term) : ExceptT String IO thm := G.INTEGER_RULE2 t
  let { INT_FORALL_POS, .. } := A1
  let { int_gcd, INT_LCM_POS, .. } := G
  let { num_divides, num_congruent, num_coprime, num_gcd, num_lcm, .. } := Nn
  let { NUM_OF_INT, INT_OF_NUM_OF_INT, .. } := NoI
  let { NOT_EXISTS_THM, .. } := HolBase.C
  let { IMP_CONJ, LEFT_IMP_EXISTS_THM, RIGHT_IMP_FORALL_THM, .. } := HolBase.T

  let NUM_GCD ← prove
   r"!a b. &(gcd(a,b)) = gcd(&a,&b)"
   (REWRITE_TAC [num_gcd, ← GSYM NUM_OF_INT, int_gcd])

  let NUM_LCM ← prove
   r"!a b. &(lcm(a,b)) = lcm(&a,&b)"
   (REWRITE_TAC [num_lcm, ← GSYM NUM_OF_INT, INT_LCM_POS])

  let CONG ← prove
   r"!x y n. (x == y) (mod n) <=> x MOD n = y MOD n"
   (REWRITE_TAC [num_congruent, ← GSYM INT_REM_EQ, INT_OF_NUM_REM, INT_OF_NUM_EQ])

  let CONG_LMOD ← prove
   r"!x y n. (x MOD n == y) (mod n) <=> (x == y) (mod n)"
   (REWRITE_TAC [CONG, MOD_MOD_REFL])

  let CONG_RMOD ← prove
   r"!x y n. (x == y MOD n) (mod n) <=> (x == y) (mod n)"
   (REWRITE_TAC [CONG, MOD_MOD_REFL])

  let CONG_DIV2 ← prove
   r"!a b m n. (a == b) (mod (m * n)) ==> (a DIV m == b DIV m) (mod n)"
   (SIMP_TAC [CONG, DIV_MOD])

  let divides ← prove
   r"a divides b <=> ?x:num. b = a * x"
   (REWRITE_TAC [num_divides, int_divides] THEN
    EQ_TAC THENL [ALL_TAC, MESON_TAC [INT_OF_NUM_MUL, INT_OF_NUM_EQ]] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"x:int")) THEN EXISTS_TAC (← q r"num_of_int(abs x)") THEN
    SIMP_TAC [← GSYM INT_OF_NUM_EQ,
              ← INT_ARITH (← q r"&m:int = &n <=> abs(&m :int) = abs(&n)")] THEN
    ASM_REWRITE_TAC [← GSYM INT_OF_NUM_MUL, INT_ABS_MUL] THEN
    SIMP_TAC [INT_OF_NUM_OF_INT, INT_ABS_POS, INT_ABS_ABS])

  let DIVIDES_LE ← prove
   r"!m n. m divides n ==> m <= n \/ n = 0"
   (SUBGOAL_THEN (← q r"!m n. m <= m * n \/ m * n = 0")
      (fun th => MESON_TAC [divides, th]) THEN
    REWRITE_TAC [LE_MULT_LCANCEL, MULT_EQ_0, ← ARITH_RULE
     (← q r"m <= m * n <=> m * 1 <= m * n")] THEN
    ASM_ARITH_TAC)

  let DIVIDES_LE_STRONG ← prove
   r"!m n. m divides n ==> 1 <= m /\ m <= n \/ n = 0"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"m = 0") THEN
    ASM_SIMP_TAC [DIVIDES_LE, LE_1, LE_0] THEN
    REWRITE_TAC [divides] THEN MESON_TAC [MULT_CLAUSES])

  let DIVIDES_LE_IMP ← prove
   r"!m n. m divides n /\ (n = 0 ==> m = 0) ==> m <= n"
   (MESON_TAC [DIVIDES_LE, LE_REFL])

  let PROPERLY_DIVIDES_LE_IMP ← prove
   r"!m n. m divides n /\ ~(n = 0) /\ ~(m = n) ==> 2 * m <= n"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [MULT_SYM] THEN
    SIMP_TAC [IMP_CONJ, divides, LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [← NUM_RING (← q r"~(m = m * d) <=> ~(m = 0) /\ ~(d = 1)")] THEN
    SIMP_TAC [LE_MULT_LCANCEL, MULT_EQ_0] THEN ARITH_TAC)

  let DIVIDES_ANTISYM ← prove
   r"!m n. m divides n /\ n divides m <=> m = n"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [ALL_TAC, REWRITE_TAC [divides] THEN MESON_TAC [MULT_CLAUSES]] THEN
    DISCH_THEN (CONJUNCTS_THEN (MP_TAC o MATCH_MP DIVIDES_LE_STRONG)) THEN
    ARITH_TAC)

  let DIVIDES_ONE ← prove
   r"!n. n divides 1 <=> n = 1"
   (REWRITE_TAC [divides] THEN MESON_TAC [MULT_EQ_1, MULT_CLAUSES])

  let DIV_ADD ← prove
   r"!d a b. d divides a \/ d divides b
           ==> (a + b) DIV d = a DIV d + b DIV d"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"d = 0") THEN
    ASM_SIMP_TAC [DIV_ZERO, ADD_CLAUSES] THEN
    REWRITE_TAC [divides] THEN STRIP_TAC THEN
    ASM_SIMP_TAC [DIV_MULT_ADD, DIV_MULT])

  let DIVIDES_MOD ← prove
   r"!m n. m divides n <=> n MOD m = 0"
   (REWRITE_TAC [divides, MOD_EQ_0] THEN MESON_TAC [MULT_SYM])

  let DIVIDES_DIV_MULT ← prove
   r"!m n. m divides n <=> ((n DIV m) * m = n)"
   (REWRITE_TAC [← GSYM INT_OF_NUM_EQ, ← GSYM INT_OF_NUM_MUL, ← GSYM INT_OF_NUM_DIV,
                 INT_MUL_DIV_EQ, ← GSYM num_divides])

  let DIV_BY_DIV ← prove
   r"!m n. ~(n = 0) /\ m divides n ==> n DIV (n DIV m) = m"
   (REWRITE_TAC [← GSYM INT_OF_NUM_EQ, ← GSYM INT_OF_NUM_DIV, num_divides,
                 INT_DIV_BY_DIV])

  let DIVIDES_DIV_DIVIDES ← prove
   r"!n d e. d divides n /\ (n = 0 ==> e = 0)
           ==> (n DIV d divides e <=> n divides d * e)"
   (REWRITE_TAC [← GSYM INT_OF_NUM_EQ, ← GSYM INT_OF_NUM_DIV, num_divides,
                 ← GSYM INT_OF_NUM_MUL, INT_DIVIDES_DIV_DIVIDES])

  let DIVIDES_DIV_SELF ← prove
   r"!n d. d divides n ==> n DIV d divides n"
   (REWRITE_TAC [num_divides, ← GSYM INT_OF_NUM_DIV, INT_DIVIDES_DIV_SELF])

  let DIVIDES_DIVIDES_DIV ← prove
   r"!n d e. d divides n ==> (e divides (n DIV d) <=> (d * e) divides n)"
   (REWRITE_TAC [← GSYM INT_OF_NUM_EQ, ← GSYM INT_OF_NUM_DIV, num_divides,
                 ← GSYM INT_OF_NUM_MUL, INT_DIVIDES_DIVIDES_DIV])

  let DIVIDES_DIVIDES_DIV_EQ ← prove
   r"!n d e:num. d divides n /\ e divides n DIV d <=> d * e divides n"
   (REWRITE_TAC [num_divides, ← GSYM INT_OF_NUM_DIV, ← GSYM INT_OF_NUM_MUL] THEN
    REWRITE_TAC [INT_DIVIDES_DIVIDES_DIV_EQ])

  let DIVIDES_DIVIDES_DIV_IMP ← prove
   r"!n d e. d * e divides n ==> e divides n DIV d"
   (MESON_TAC [DIVIDES_DIVIDES_DIV_EQ])

  let MULT_DIV ← prove
   r"(!m n p. p divides m ==> (m * n) DIV p = m DIV p * n) /\
   (!m n p. p divides n ==> (m * n) DIV p = m * n DIV p)"
   (MATCH_MP_TAC (← TAUT (← q r"(a ==> b) /\ a ==> a /\ b")) THEN CONJ_TAC THENL
     [MESON_TAC [MULT_SYM], SIMP_TAC [divides, LEFT_IMP_EXISTS_THM]] THEN
    REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"p = 0") THEN
    ASM_SIMP_TAC [MULT_CLAUSES, DIV_0, ← GSYM MULT_ASSOC, DIV_MULT])

  let NUMBER_TAC ← do
    let conva ← GEN_REWRITE_CONV_NET TRY_CONV [← GSYM DIVIDES_ANTISYM]
    let antisym_conv := numberAntisymConv conva
    let pth_relativize ← prove
     r"((!n. P(&n)) <=> (!i:int. &0 <= i ==> P i)) /\
       ((?n. P(&n)) <=> (?i:int. &0 <= i /\ P i))"
      (GEN_REWRITE_TAC RAND_CONV [← TAUT (← q r"(a <=> b) <=> (~a <=> ~b)")] THEN
       REWRITE_TAC [NOT_EXISTS_THM, INT_FORALL_POS] THEN MESON_TAC [])
    let relation_conv ←
     GEN_REWRITE_CONV_NET TOP_SWEEP_CONV
      (num_divides :: num_congruent :: num_coprime :: NUM_GCD :: NUM_LCM :: (← [
       INT_OF_NUM_EQ, INT_OF_NUM_LE, INT_OF_NUM_LT, INT_OF_NUM_GE, INT_OF_NUM_GT,
       INT_OF_NUM_SUC, INT_OF_NUM_ADD, INT_OF_NUM_MUL, INT_OF_NUM_POW].mapM GSYM))
    let quantifier_conv ← GEN_REWRITE_CONV_NET DEPTH_CONV [pth_relativize]
    pure
     (REPEAT (CONJ_TAC ORELSE GEN_TAC ORELSE EQ_TAC) THEN CONV_TAC antisym_conv THEN
      W (fun (_, w) => MAP_EVERY (fun v => SPEC_TAC (v, v)) (frees w)) THEN
      CONV_TAC (relation_conv THENC quantifier_conv) THEN
      REWRITE_TAC [RIGHT_IMP_FORALL_THM] THEN REPEAT GEN_TAC THEN
      INTEGER_TAC)

  let NUMBER_RULE (tm : term) : ExceptT String IO thm :=
    HolCore.Tactics.prove HolBase.B tm NUMBER_TAC

  -- OCaml evaluates the list right to left: the second NUMBER_RULE first.
  let COPRIME_LMOD ← prove
   r"!a n. coprime(a MOD n,n) <=> coprime(a,n)"
   (← do
    let r2 ← NUMBER_RULE (← q r"(a:num == b) (mod n) /\ coprime(a,n) ==> coprime(b,n)")
    let r1 ← NUMBER_RULE (← q r"(x:num == x) (mod n)")
    pure (MESON_TAC [CONG_LMOD, r1, r2]))

  let COPRIME_RMOD ← prove
   r"!a n. coprime(n,a MOD n) <=> coprime(n,a)"
   (ONCE_REWRITE_TAC [← NUMBER_RULE (← q r"coprime(a:num,b) <=> coprime(b,a)")] THEN
    REWRITE_TAC [COPRIME_LMOD])

  let INT_CONG_NUM_EXISTS ← prove
   r"!x y:int.
        (y = &0 ==> &0 <= x)
        ==> ?n. (&n == x) (mod y)"
   (← do
    let n1 ← INTEGER_RULE (← q r"(x + a:int == x) (mod n) <=> n divides a")
    let i1 ← INT_ARITH (← q r"abs(x) * &1:int <= y ==> &0 <= x + y")
    pure
     (REPEAT STRIP_TAC THEN
      EXISTS_TAC (← q r"num_of_int(x + abs(x * y))") THEN
      W (MP_TAC o PART_MATCH (lhand o rand) INT_OF_NUM_OF_INT o
            lhand o rator o snd) THEN
      ANTS_TAC THENL
       [POP_ASSUM MP_TAC THEN ASM_CASES_TAC (← q r"y:int = &0") THEN
        ASM_REWRITE_TAC [] THENL [ASM_ARITH_TAC, ALL_TAC] THEN
        MATCH_MP_TAC i1 THEN
        REWRITE_TAC [INT_ABS_MUL] THEN MATCH_MP_TAC INT_LE_LMUL THEN
        ASM_INT_ARITH_TAC,
        DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC [n1] THEN
        REWRITE_TAC [INT_ABS] THEN COND_CASES_TAC THEN CONV_TAC INTEGER_RULE]))

  let GCD ← prove
   r"!a b. (gcd(a,b) divides a /\ gcd(a,b) divides b) /\
         (!e. e divides a /\ e divides b ==> e divides gcd(a,b))"
   NUMBER_TAC

  let coprime ← prove
   r"coprime(a,b) <=> !d. d divides a /\ d divides b ==> d = 1"
   (EQ_TAC THENL [CONV_TAC NUMBER_RULE, ALL_TAC] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"gcd(a,b)")) THEN REWRITE_TAC [GCD] THEN
    NUMBER_TAC)

  return { NUM_GCD, NUM_LCM, CONG, CONG_LMOD, CONG_RMOD, CONG_DIV2, divides,
           DIVIDES_LE, DIVIDES_LE_STRONG, DIVIDES_LE_IMP, PROPERLY_DIVIDES_LE_IMP,
           DIVIDES_ANTISYM, DIVIDES_ONE, DIV_ADD, DIVIDES_MOD, DIVIDES_DIV_MULT,
           DIV_BY_DIV, DIVIDES_DIV_DIVIDES, DIVIDES_DIV_SELF, DIVIDES_DIVIDES_DIV,
           DIVIDES_DIVIDES_DIV_EQ, DIVIDES_DIVIDES_DIV_IMP, MULT_DIV, NUMBER_TAC,
           NUMBER_RULE := fun t => NUMBER_RULE t, COPRIME_LMOD, COPRIME_RMOD,
           INT_CONG_NUM_EXISTS, GCD, coprime }

/- ---------------------------------------------------------------------- -/
/- Definition (and not much more) of primality.                           -/
/- ---------------------------------------------------------------------- -/

structure IntPrime where
  prime : thm
  ONE_OR_PRIME : thm
  ONE_OR_PRIME_DIVIDES_OR_COPRIME : thm
  PRIME_COPRIME_EQ_NONDIVISIBLE : thm
  ZERO_ONE_OR_PRIME_DIVPROD : thm
  ZERO_ONE_OR_PRIME : thm
  deriving Inhabited

/-- int.ml 2568-2630. -/
@[nospecialize]
def setupIntPrime [HolBase]
    (N : IntNumber)
    (MULT_EQ_0 MULT_EQ_1 MULT_CLAUSES LE_MULT_LCANCEL LE_MULT_RCANCEL : thm)
    (new_definition' : term → IO (Except String thm))
    (ARITH_RULE' : term → IO (Except String thm))
    (ASM_MESON_TAC : List thm → tactic) :
    ExceptT String IO IntPrime := do
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let ARITH_RULE (t : term) : ExceptT String IO thm := ARITH_RULE' t
  let NUMBER_RULE (t : term) : ExceptT String IO thm := N.NUMBER_RULE t
  let { DIVIDES_ONE, coprime, divides, DIVIDES_LE_STRONG, .. } := N
  let { CONTRAPOS_THM, DE_MORGAN_THM, .. } := HolBase.C
  let { MONO_OR, MONO_FORALL, DISJ_SYM, LEFT_IMP_EXISTS_THM, .. } := HolBase.T

  let prime ← new_definition
    r"prime(p) <=> ~(p = 1) /\ !x. x divides p ==> x = 1 \/ x = p"

  let ONE_OR_PRIME ← prove
   r"!p. p = 1 \/ prime p <=> !n. n divides p ==> n = 1 \/ n = p"
   (GEN_TAC THEN REWRITE_TAC [prime] THEN
    ASM_CASES_TAC (← q r"p = 1") THEN ASM_REWRITE_TAC [DIVIDES_ONE])

  let ONE_OR_PRIME_DIVIDES_OR_COPRIME ← prove
   r"!p. p = 1 \/ prime p <=> !n. p divides n \/ coprime(p,n)"
   (GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC [] THEN GEN_TAC THEN DISJ1_TAC THEN CONV_TAC NUMBER_RULE,
      ASM_MESON_TAC [prime, coprime],
      REWRITE_TAC [ONE_OR_PRIME] THEN
      X_GEN_TAC (← q r"n:num") THEN DISCH_TAC THEN ONCE_REWRITE_TAC [DISJ_SYM] THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"n:num")) THEN MATCH_MP_TAC MONO_OR THEN
      CONJ_TAC THEN POP_ASSUM MP_TAC THEN CONV_TAC NUMBER_RULE])

  let PRIME_COPRIME_EQ_NONDIVISIBLE ← prove
   r"!p. prime p <=> !n. coprime(p,n) <=> ~(p divides n)"
   (← do
    let t3 ← TAUT (← q r"~(p /\ q) ==> q \/ p ==> (p <=> ~q)")
    let t2 ← TAUT (← q r"p \/ ~p")
    let t1 ← TAUT (← q r"p /\ q ==> (p <=> ~q) ==> F")
    pure
     (X_GEN_TAC (← q r"p:num") THEN ASM_CASES_TAC (← q r"p = 1") THEN ASM_REWRITE_TAC [] THENL
       [ASM_REWRITE_TAC [prime] THEN DISCH_THEN (MP_TAC o SPEC (← q r"1")) THEN
        MATCH_MP_TAC t1 THEN CONV_TAC NUMBER_RULE,
        MP_TAC (← SPEC (← q r"p:num") ONE_OR_PRIME_DIVIDES_OR_COPRIME) THEN
        ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
        EQ_TAC THEN MATCH_MP_TAC MONO_FORALL THEN SIMP_TAC [t2] THEN
        GEN_TAC THEN MATCH_MP_TAC t3 THEN
        POP_ASSUM MP_TAC THEN REWRITE_TAC [CONTRAPOS_THM] THEN
        CONV_TAC NUMBER_RULE]))

  -- The tactic's NUMBER_RULEs run (and print) right to left, as in OCaml.
  let ZERO_ONE_OR_PRIME_DIVPROD ← prove
   r"!p a b.
        p = 0 \/ p = 1 \/ prime p
        ==> (p divides (a * b) <=> p divides a \/ p divides b)"
   (← do
    let cancel ← NUMBER_RULE
      (← q r"!d a b:num. d divides (a * b) /\ coprime(d,a) ==> d divides b")
    let zero_divides ← NUMBER_RULE (← q r"0 divides n <=> n = 0")
    let one_divides ← NUMBER_RULE (← q r"1 divides n")
    pure
     (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [one_divides] THEN
      ASM_REWRITE_TAC [zero_divides, MULT_EQ_0] THEN
      EQ_TAC THENL [ALL_TAC, CONV_TAC NUMBER_RULE] THEN
      ASM_MESON_TAC [prime, coprime, cancel]))

  let ZERO_ONE_OR_PRIME ← prove
   r"!p. p = 0 \/ p = 1 \/ prime p <=>
       !a b. p divides (a * b) ==> p divides a \/ p divides b"
   (← do
    let a3 ← ARITH_RULE (← q r"n <= 1 <=> n = 0 \/ n = 1")
    let a2 ← ARITH_RULE (← q r"a * b <= b <=> a * b <= 1 * b")
    let a1 ← ARITH_RULE (← q r"a * b <= a <=> a * b <= a * 1")
    let n1 ← NUMBER_RULE (← q r"(n:num) divides n")
    let t1 ← TAUT (← q r"p \/ q <=> ~p ==> q")
    pure
     (GEN_TAC THEN EQ_TAC THEN SIMP_TAC [ZERO_ONE_OR_PRIME_DIVPROD] THEN
      DISCH_TAC THEN REWRITE_TAC [t1] THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [prime, divides, LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"a:num", ← q r"b:num"] THEN DISCH_THEN (ASSUME_TAC o SYM) THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [← q r"a:num", ← q r"b:num"]) THEN
      FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN
      RULE_ASSUM_TAC (REWRITE_RULE [MULT_EQ_0, MULT_EQ_1, DE_MORGAN_THM]) THEN
      REWRITE_TAC [n1] THEN
      STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o MATCH_MP DIVIDES_LE_STRONG) THEN
      ONCE_REWRITE_TAC [a1, a2] THEN
      REWRITE_TAC [LE_MULT_LCANCEL, LE_MULT_RCANCEL] THEN
      ASM_SIMP_TAC [MULT_CLAUSES, a3]))

  return { prime, ONE_OR_PRIME, ONE_OR_PRIME_DIVIDES_OR_COPRIME,
           PRIME_COPRIME_EQ_NONDIVISIBLE, ZERO_ONE_OR_PRIME_DIVPROD,
           ZERO_ONE_OR_PRIME }

/- ---------------------------------------------------------------------- -/
/- Integer powers of real numbers.                                        -/
/- ---------------------------------------------------------------------- -/

structure RealZpow where
  real_zpow : thm
  REAL_POW_ZPOW : thm
  REAL_ZPOW_NUM : thm
  REAL_ZPOW_0 : thm
  REAL_ZPOW_1 : thm
  REAL_ZPOW_2 : thm
  REAL_ZPOW_ONE : thm
  REAL_ZPOW_NEG : thm
  REAL_ZPOW_MINUS1 : thm
  REAL_ZPOW_ZERO : thm
  REAL_ZPOW_POW : thm
  REAL_INV_ZPOW : thm
  REAL_ZPOW_INV : thm
  REAL_ZPOW_ZPOW : thm
  REAL_ZPOW_MUL : thm
  REAL_ZPOW_DIV : thm
  REAL_ZPOW_ADD : thm
  REAL_ZPOW_SUB : thm
  REAL_ZPOW_LE : thm
  REAL_ZPOW_LT : thm
  REAL_ZPOW_EQ_0 : thm
  REAL_ABS_ZPOW : thm
  REAL_SGN_ZPOW : thm
  deriving Inhabited

/-- int.ml 2634-2762.  `INT_ARITH` is the second version. -/
@[nospecialize]
def setupRealZpow [HolBase]
    (INT_POS NUM_OF_INT_OF_NUM FORALL_INT_CASES WLOG_LE : thm)
    (real_pow REAL_POW_1 REAL_POW_2 REAL_POW_ONE : thm)
    (REAL_INV_1 REAL_INV_INV REAL_INV_0 REAL_INV_MUL REAL_INV_POW : thm)
    (REAL_POW_ZERO REAL_POW_POW REAL_POW_MUL REAL_POW_ADD REAL_POW_EQ_0 : thm)
    (REAL_POW_LE REAL_POW_LT : thm)
    (REAL_LE_INV_EQ REAL_LT_INV_EQ REAL_INV_EQ_0 : thm)
    (REAL_EQ_INV2 REAL_MUL_LINV REAL_MUL_LID REAL_MUL_ASSOC : thm)
    (REAL_MUL_SYM REAL_MUL_AC real_div : thm)
    (REAL_ABS_INV REAL_ABS_POW REAL_SGN_POW REAL_SGN_INV REAL_INV_SGN : thm)
    (COND_ID COND_SWAP : thm)
    (INT_NEG_0 INT_NEG_NEG INT_NEG_EQ_0 INT_NEG_ADD : thm)
    (INT_OF_NUM_EQ INT_OF_NUM_ADD INT_OF_NUM_MUL : thm)
    (INT_MUL_LNEG INT_MUL_RNEG INT_ADD_SYM INT_SUB : thm)
    (SWAP_FORALL_THM RIGHT_FORALL_IMP_THM LEFT_IMP_EXISTS_THM LE_EXISTS : thm)
    (make_overloadable' : String → hol_type → IO (Except String Unit))
    (overload_interface' : String → term → IO (Except String Unit))
    (parse_as_infix : String × (Int × String) → IO Unit)
    (new_definition' : term → IO (Except String thm))
    (INT_ARITH' : term → IO (Except String thm))
    (ARITH_RULE' : term → IO (Except String thm))
    (MESON_TAC : List thm → tactic) :
    ExceptT String IO RealZpow := do
  let make_overloadable (s : String) (ty : hol_type) : ExceptT String IO Unit :=
    make_overloadable' s ty
  let overload_interface (s : String) (t : term) : ExceptT String IO Unit :=
    overload_interface' s t
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let INT_ARITH (t : term) : ExceptT String IO thm := INT_ARITH' t
  let ARITH_RULE (t : term) : ExceptT String IO thm := ARITH_RULE' t

  make_overloadable "zpow" (← qty r"A->int->A")
  parse_as_infix ("zpow", (24, "left"))
  overload_interface "zpow" (← q r"real_zpow:real->int->real")

  let real_zpow ← new_definition
   r"(z:real) zpow (i:int) = if &0 <= i then z pow (num_of_int i)
                          else inv(z pow (num_of_int(--i)))"

  let REAL_POW_ZPOW ← prove
   r"!x n. x pow n = x zpow (&n)"
   (REWRITE_TAC [real_zpow, INT_POS, NUM_OF_INT_OF_NUM])

  let REAL_ZPOW_NUM ← prove
   r"!x n. x zpow (&n) = x pow n"
   (REWRITE_TAC [real_zpow, INT_POS, NUM_OF_INT_OF_NUM])

  let REAL_ZPOW_0 ← prove
   r"!x:real. x zpow (&0) = &1"
   (REWRITE_TAC [REAL_ZPOW_NUM, real_pow])

  let REAL_ZPOW_1 ← prove
   r"!x:real. x zpow (&1) = x"
   (REWRITE_TAC [REAL_ZPOW_NUM, REAL_POW_1])

  let REAL_ZPOW_2 ← prove
   r"!x:real. x zpow (&2) = x * x"
   (REWRITE_TAC [REAL_ZPOW_NUM, REAL_POW_2])

  let REAL_ZPOW_ONE ← prove
   r"!n. &1 zpow n = &1"
   (REWRITE_TAC [real_zpow, REAL_POW_ONE, REAL_INV_1, COND_ID])

  let REAL_ZPOW_NEG ← prove
   r"!x n. x zpow (--n) = inv(x zpow n)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n:int = &0") THEN
    ASM_REWRITE_TAC [INT_NEG_0, REAL_ZPOW_0, REAL_INV_1] THEN
    ASM_SIMP_TAC [real_zpow, COND_SWAP, INT_NEG_NEG, ← INT_ARITH
     (← q r"~(n:int = &0) ==> (&0 <= --n <=> ~(&0 <= n))")] THEN
    MESON_TAC [REAL_INV_INV])

  let REAL_ZPOW_MINUS1 ← prove
   r"!x. x zpow --(&1) = inv x"
   (REWRITE_TAC [REAL_ZPOW_NEG, REAL_ZPOW_1])

  let REAL_ZPOW_ZERO ← prove
   r"!n. &0 zpow n = if n = &0 then &1 else &0"
   (REWRITE_TAC [FORALL_INT_CASES, REAL_ZPOW_NEG, REAL_ZPOW_NUM] THEN
    REWRITE_TAC [REAL_POW_ZERO, INT_NEG_EQ_0, INT_OF_NUM_EQ] THEN
    MESON_TAC [REAL_INV_0, REAL_INV_1])

  let REAL_ZPOW_POW ← prove
   r"(!(x:real) n. x zpow (&n) = x pow n) /\
   (!(x:real) n. x zpow (-- &n) = inv(x pow n))"
   (REWRITE_TAC [REAL_ZPOW_NEG, REAL_ZPOW_NUM])

  let REAL_INV_ZPOW ← prove
   r"!(x:real) n. inv(x zpow n) = inv(x) zpow n"
   (REWRITE_TAC [FORALL_INT_CASES, REAL_ZPOW_POW] THEN
    REWRITE_TAC [REAL_INV_POW, REAL_INV_INV])

  let REAL_ZPOW_INV ← prove
   r"!(x:real) n. inv x zpow n = inv(x zpow n)"
   (REWRITE_TAC [REAL_INV_ZPOW])

  let REAL_ZPOW_ZPOW ← prove
   r"!(x:real) m n. (x zpow m) zpow n = x zpow (m * n)"
   (REWRITE_TAC [FORALL_INT_CASES, INT_MUL_LNEG, INT_MUL_RNEG, INT_NEG_NEG] THEN
    REWRITE_TAC [REAL_ZPOW_POW, REAL_INV_POW, INT_OF_NUM_MUL, REAL_INV_INV] THEN
    REWRITE_TAC [REAL_POW_POW])

  let REAL_ZPOW_MUL ← prove
   r"!(x:real) (y:real) n. (x * y) zpow n = x zpow n * y zpow n"
   (REWRITE_TAC [FORALL_INT_CASES, REAL_ZPOW_POW, REAL_POW_MUL, REAL_INV_MUL])

  let REAL_ZPOW_DIV ← prove
   r"!(x:real) (y:real) n. (x / y) zpow n = x zpow n / y zpow n"
   (REWRITE_TAC [real_div, REAL_INV_ZPOW, REAL_ZPOW_MUL])

  let REAL_ZPOW_ADD ← prove
   r"!(x:real) m n.
        ~(x = &0) ==> x zpow (m + n) = x zpow m * x zpow n"
   (← do
    let a1 ← ARITH_RULE (← q r"--n + (n + m):int = m")
    let i1 ← INT_ARITH (← q r"--(--x + y):int = --y + x")
    pure
      (REWRITE_TAC [FORALL_INT_CASES, ← GSYM INT_NEG_ADD, INT_OF_NUM_ADD] THEN
       REWRITE_TAC [REAL_ZPOW_POW, REAL_POW_ADD, REAL_INV_MUL] THEN
       X_GEN_TAC (← q r"x:real") THEN GEN_REWRITE_TAC LAND_CONV [SWAP_FORALL_THM] THEN
       GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
         [REAL_MUL_SYM, INT_ADD_SYM] THEN
       REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
       MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL
        [REPEAT GEN_TAC THEN
         GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_EQ_INV2] THEN
         REWRITE_TAC [REAL_INV_MUL, REAL_INV_INV, ← GSYM REAL_ZPOW_NEG] THEN
         REWRITE_TAC [i1] THEN
         REWRITE_TAC [REAL_MUL_AC],
         MAP_EVERY X_GEN_TAC [← q r"n:num", ← q r"p:num"] THEN
         REWRITE_TAC [LE_EXISTS, LEFT_IMP_EXISTS_THM] THEN
         SIMP_TAC [← GSYM INT_OF_NUM_ADD, a1] THEN
         REWRITE_TAC [REAL_POW_ADD, REAL_ZPOW_NUM, REAL_MUL_ASSOC] THEN
         ASM_SIMP_TAC [REAL_MUL_LINV, REAL_POW_EQ_0, REAL_MUL_LID]]))

  let REAL_ZPOW_SUB ← prove
   r"!(x:real) m n.
        ~(x = &0) ==> x zpow (m - n) = x zpow m / x zpow n"
   (SIMP_TAC [INT_SUB, REAL_ZPOW_ADD, REAL_ZPOW_NEG, real_div])

  let REAL_ZPOW_LE ← prove
   r"!x n. &0 <= x ==> &0 <= x zpow n"
   (SIMP_TAC [FORALL_INT_CASES, REAL_ZPOW_POW, REAL_LE_INV_EQ, REAL_POW_LE])

  let REAL_ZPOW_LT ← prove
   r"!x n. &0 < x ==> &0 < x zpow n"
   (SIMP_TAC [FORALL_INT_CASES, REAL_ZPOW_POW, REAL_LT_INV_EQ, REAL_POW_LT])

  let REAL_ZPOW_EQ_0 ← prove
   r"!x n. x zpow n = &0 <=> x = &0 /\ ~(n = &0)"
   (REWRITE_TAC [FORALL_INT_CASES, REAL_ZPOW_POW, REAL_INV_EQ_0] THEN
    REWRITE_TAC [INT_NEG_EQ_0, REAL_POW_EQ_0, INT_OF_NUM_EQ])

  let REAL_ABS_ZPOW ← prove
   r"!x n. abs(x zpow n) = abs(x) zpow n"
   (REWRITE_TAC [FORALL_INT_CASES, REAL_ZPOW_POW, REAL_ABS_INV, REAL_ABS_POW])

  let REAL_SGN_ZPOW ← prove
   r"!x n. real_sgn(x zpow n) = real_sgn(x) zpow n"
   (REWRITE_TAC [FORALL_INT_CASES, REAL_ZPOW_POW] THEN
    REWRITE_TAC [← GSYM REAL_SGN_POW] THEN
    REWRITE_TAC [REAL_SGN_INV, REAL_INV_SGN])

  return { real_zpow, REAL_POW_ZPOW, REAL_ZPOW_NUM, REAL_ZPOW_0, REAL_ZPOW_1,
           REAL_ZPOW_2, REAL_ZPOW_ONE, REAL_ZPOW_NEG, REAL_ZPOW_MINUS1,
           REAL_ZPOW_ZERO, REAL_ZPOW_POW, REAL_INV_ZPOW, REAL_ZPOW_INV,
           REAL_ZPOW_ZPOW, REAL_ZPOW_MUL, REAL_ZPOW_DIV, REAL_ZPOW_ADD,
           REAL_ZPOW_SUB, REAL_ZPOW_LE, REAL_ZPOW_LT, REAL_ZPOW_EQ_0,
           REAL_ABS_ZPOW, REAL_SGN_ZPOW }

/- ---------------------------------------------------------------------- -/
/- Make sure we give priority to N.                                       -/
/- ---------------------------------------------------------------------- -/

/-- `prioritize_num()` (int.ml 2765).  Session runs it last. -/
def prioritize_num (prioritize_overload : hol_type → IO Unit) :
    ExceptT String IO Unit := do
  liftM (prioritize_overload (← (mk_type "num" [] : ExceptT String IO hol_type)))

end HolMath.Int
