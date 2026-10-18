/- ========================================================================= -/
/- The integer/rational-valued reals, and the "floor" and "frac" functions.  -/
/- ========================================================================= -/
/- File: HolLibrary/Floor.lean

  Original (c) Copyright, John Harrison 1998-2017
  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/floor.ml` (`needs "Library/floor.ml"`
  after the core library), in the style of HolLibrary/Prime.lean: pure, the
  proofs translated by hand, one `let` per OCaml `let`, in file order.  See
  HolLibrary/Prime.lean for the conventions and HolMath/Base.lean for the
  tactic surface.

  floor.ml 5 `prioritize_real()` is run by the wiring before the first
  bundle, and stays in force afterwards, as in HOL Light.  The definitions
  are `rational` (floor.ml 168, `new_definition`) and `floor`/`frac`
  (floor.ml 311, `new_specification`).
-/

import HolMath

open HolCore HolCore.Lib
open HolCore.Kernel hiding ASSUME INST
open HolCore.Equal (ioconv lhs lhand)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)
open HolLight HolLight.Syntax

namespace HolLibrary.Floor

set_option maxHeartbeats 1000000

/- ------------------------------------------------------------------------- -/
/- What floor.ml uses from the core library (supplied by Session).           -/
/- ------------------------------------------------------------------------- -/

/-- Theorems floor.ml uses from the core library, A-L.  (Two structures,
    split under 128 fields because Lean 4.33.1 crashed at 128 or more; that
    could not be reproduced on 4.34.1.  The runtime limit is 255 fields.) -/
structure CoreThms1 where
  (ADD_SUB ADD_SYM CONJ_ASSOC CONTRAPOS_THM DEPENDENT_CHOICE DIVISION
   EMPTY_GSPEC EXTENSION FINITE_IMAGE FINITE_NUMSEG FINITE_SUBSET
   FINITE_UNION FORALL_IN_IMAGE HAS_SIZE HAS_SIZE_0 HAS_SIZE_IMAGE_INJ
   HAS_SIZE_NUMSEG HAS_SIZE_NUMSEG_LE IMP_CONJ_ALT IMP_IMP IN INFINITE
   INFINITE_IMAGE INFINITE_IMAGE_INJ INFINITE_SUPERSET INTEGER_REAL_OF_INT
   INT_OF_NUM_OF_INT IN_ELIM_THM IN_IMAGE IN_NUMSEG IN_UNION IN_UNIV
   LEFT_AND_EXISTS_THM LEFT_IMP_EXISTS_THM LE_1 LE_ADD LE_CASES LE_EXISTS
   LE_REFL LT LT_CASES LT_NZ LT_SUC_LE : thm)

/-- Theorems floor.ml uses from the core library, M-Z and lower case. -/
structure CoreThms2 where
  (MONO_EXISTS MONO_FORALL MULT_EQ_1 NUM_OF_INT_OF_NUM OR_EXISTS_THM
   REAL_ABS_ABS REAL_ABS_DIV REAL_ABS_MUL REAL_ABS_NEG REAL_ABS_NUM
   REAL_ABS_POW REAL_ABS_ZERO REAL_ADD_LID REAL_ADD_SUB REAL_ADD_SYM
   REAL_ARCH_POW REAL_ARCH_SIMPLE REAL_EQ_ADD_LCANCEL REAL_EQ_NEG2 REAL_INV_0
   REAL_INV_INV REAL_LE_DIV REAL_LE_LDIV_EQ REAL_LE_LT REAL_LE_MUL
   REAL_LE_RDIV_EQ REAL_LE_REFL REAL_LE_TOTAL REAL_LE_TRANS REAL_LT_DIV
   REAL_LT_IMP_LE REAL_LT_INV_EQ REAL_LT_LDIV_EQ REAL_LT_LE REAL_LT_MIN
   REAL_LT_MUL REAL_LT_RDIV_EQ REAL_LT_REFL REAL_LT_TRANS REAL_MAX_LE
   REAL_MUL_LID REAL_MUL_LNEG REAL_MUL_LZERO REAL_MUL_RZERO REAL_MUL_SYM
   REAL_NEG_ADD REAL_NEG_NEG REAL_NEG_SUB REAL_NOT_LE REAL_NOT_LT
   REAL_OF_NUM_ADD REAL_OF_NUM_EQ REAL_OF_NUM_LE REAL_OF_NUM_LT
   REAL_OF_NUM_MUL REAL_OF_NUM_POW REAL_OF_NUM_SUB REAL_OF_NUM_SUC REAL_POS
   REAL_POW_LE REAL_POW_LT REAL_SUB_0 REAL_SUB_ADD REAL_SUB_LE REAL_SUB_LT
   REAL_SUB_REFL RIGHT_AND_EXISTS_THM SKOLEM_THM SUBSET SUM_CLOSED
   SURJECTIVE_IMAGE_EQ SWAP_EXISTS_THM TRANSITIVE_STEPWISE_LT UNWIND_THM1
   divides int_congruent int_eq int_le int_mul_th int_of_num int_of_num_th
   int_rep int_sub_th int_tybij integer is_int num_INFINITE num_WOP
   num_congruent real_abs real_div real_max real_min real_pow real_sub : thm)

/-- The decision procedures, rules, conversions and theorems floor.ml uses
    from hol.ml's library.  Rules that can fail are in `ExceptT`. -/
structure FloorDeps where
  -- definitions
  new_definition : String → ExceptT String IO thm
  new_specification : List String → thm → ExceptT String IO thm
  -- decision procedures and other Session tactics
  ARITH_TAC : tactic
  ASM_MESON_TAC : List thm → tactic
  ASM_REAL_ARITH_TAC : tactic
  INDUCT_TAC : tactic
  INTEGER_RULE : term → ExceptT String IO thm
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  NUMBER_RULE : term → ExceptT String IO thm
  REAL_ARITH : term → ExceptT String IO thm
  REAL_ARITH_TAC : tactic
  REAL_FIELD : term → ExceptT String IO thm
  REAL_POLY_CONV : ioconv
  SET_TAC : List thm → tactic
  -- theorems
  core1 : CoreThms1
  core2 : CoreThms2

/- ------------------------------------------------------------------------- -/
/- Closure theorems and other lemmas for the integer-valued reals (floor.ml 8-163) -/
/- ------------------------------------------------------------------------- -/

structure Integer where
  INTEGER_CASES : thm
  REAL_ABS_INTEGER_LEMMA : thm
  INTEGER_CLOSED : thm
  INTEGER_ADD : thm
  INTEGER_SUB : thm
  INTEGER_MUL : thm
  INTEGER_POW : thm
  REAL_LE_INTEGERS : thm
  REAL_LE_CASES_INTEGERS : thm
  REAL_LE_REVERSE_INTEGERS : thm
  REAL_LT_INTEGERS : thm
  REAL_EQ_INTEGERS : thm
  REAL_EQ_INTEGERS_IMP : thm
  INTEGER_NEG : thm
  INTEGER_ABS : thm
  INTEGER_POS : thm
  NONNEGATIVE_INTEGER : thm
  NONPOSITIVE_INTEGER : thm
  NONPOSITIVE_INTEGER_ALT : thm
  INTEGER_ADD_EQ : thm
  INTEGER_SUB_EQ : thm
  FORALL_INTEGER : thm
  INTEGER_SUM : thm
  INTEGER_ABS_MUL_EQ_1 : thm
  INTEGER_DIV : thm
  deriving Inhabited

@[nospecialize]
def setupInteger [HolBase] (D : FloorDeps) : ExceptT String IO Integer := do
  let { ARITH_TAC, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, REAL_FIELD, .. } := D
  let { ADD_SYM, LEFT_AND_EXISTS_THM, LE_CASES, LE_EXISTS, .. } := D.core1
  let { MULT_EQ_1, OR_EXISTS_THM, REAL_ABS_ABS, REAL_ABS_MUL, REAL_ABS_NEG, 
        REAL_ABS_NUM, REAL_ABS_POW, REAL_ADD_SUB, REAL_ADD_SYM, REAL_INV_0, 
        REAL_LE_DIV, REAL_MUL_RZERO, REAL_NEG_ADD, REAL_NEG_NEG, REAL_NEG_SUB, 
        REAL_NOT_LT, REAL_OF_NUM_ADD, REAL_OF_NUM_EQ, REAL_OF_NUM_LE, 
        REAL_OF_NUM_MUL, REAL_OF_NUM_POW, REAL_POS, REAL_SUB_ADD, SUM_CLOSED, 
        divides, integer, is_int, real_abs, real_div, real_max, real_min, 
        real_sub, .. } := D.core2

  let INTEGER_CASES ← prove
   r"integer x <=> (?n. x = &n) \/ (?n. x = -- &n)"
   (REWRITE_TAC [is_int, OR_EXISTS_THM])

  let REAL_ABS_INTEGER_LEMMA ← prove
   r"!x. integer(x) /\ ~(x = &0) ==> &1 <= abs(x)"
   (GEN_TAC THEN REWRITE_TAC [integer] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"(x = &0) <=> (abs(x) = &0)")] THEN
    POP_ASSUM (CHOOSE_THEN SUBST1_TAC) THEN
    REWRITE_TAC [REAL_OF_NUM_EQ, REAL_OF_NUM_LE] THEN ARITH_TAC)

  let INTEGER_CLOSED ← prove
   r"(!n. integer(&n)) /\
   (!x y. integer(x) /\ integer(y) ==> integer(x + y)) /\
   (!x y. integer(x) /\ integer(y) ==> integer(x - y)) /\
   (!x y. integer(x) /\ integer(y) ==> integer(x * y)) /\
   (!x r. integer(x) ==> integer(x pow r)) /\
   (!x. integer(x) ==> integer(--x)) /\
   (!x. integer(x) ==> integer(abs x)) /\
   (!x y. integer(x) /\ integer(y) ==> integer(max x y)) /\
   (!x y. integer(x) /\ integer(y) ==> integer(min x y))"
   (REWRITE_TAC [integer] THEN
    MATCH_MP_TAC (← TAUT
     (← q r"g /\ h /\ x /\ c /\ d /\ e /\ f /\ (a /\ e ==> b) /\ a
      ==> x /\ a /\ b /\ c /\ d /\ e /\ f /\ g /\ h")) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC [real_max] THEN MESON_TAC [],
      REWRITE_TAC [real_min] THEN MESON_TAC [],
      REWRITE_TAC [REAL_ABS_NUM] THEN MESON_TAC [],
      REWRITE_TAC [REAL_ABS_MUL] THEN MESON_TAC [REAL_OF_NUM_MUL],
      REWRITE_TAC [REAL_ABS_POW] THEN MESON_TAC [REAL_OF_NUM_POW],
      REWRITE_TAC [REAL_ABS_NEG], REWRITE_TAC [REAL_ABS_ABS],
      REWRITE_TAC [real_sub] THEN MESON_TAC [], ALL_TAC] THEN
    SIMP_TAC [← REAL_ARITH (← q r"&0 <= a ==> ((abs(x) = a) <=> (x = a) \/ (x = --a))"),
              REAL_POS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [← GSYM REAL_NEG_ADD, REAL_OF_NUM_ADD] THENL
     [MESON_TAC [], ALL_TAC, ALL_TAC, MESON_TAC []] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"(--a + b = c) <=> (a + c = b)"),
                 ← REAL_ARITH (← q r"(a + --b = c) <=> (b + c = a)")] THEN
    REWRITE_TAC [REAL_OF_NUM_ADD, REAL_OF_NUM_EQ] THEN
    MESON_TAC [LE_EXISTS, ADD_SYM, LE_CASES])

  let INTEGER_ADD ← prove
   r"!x y. integer(x) /\ integer(y) ==> integer(x + y)"
   (REWRITE_TAC [INTEGER_CLOSED])

  let INTEGER_SUB ← prove
   r"!x y. integer(x) /\ integer(y) ==> integer(x - y)"
   (REWRITE_TAC [INTEGER_CLOSED])

  let INTEGER_MUL ← prove
   r"!x y. integer(x) /\ integer(y) ==> integer(x * y)"
   (REWRITE_TAC [INTEGER_CLOSED])

  let INTEGER_POW ← prove
   r"!x n. integer(x) ==> integer(x pow n)"
   (REWRITE_TAC [INTEGER_CLOSED])

  let REAL_LE_INTEGERS ← prove
   r"!x y. integer(x) /\ integer(y) ==> (x <= y <=> (x = y) \/ x + &1 <= y)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPEC (← q r"y - x") REAL_ABS_INTEGER_LEMMA) THEN
    ASM_SIMP_TAC [INTEGER_CLOSED] THEN REAL_ARITH_TAC)

  let REAL_LE_CASES_INTEGERS ← prove
   r"!x y. integer(x) /\ integer(y) ==> x <= y \/ y + &1 <= x"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPEC (← q r"y - x") REAL_ABS_INTEGER_LEMMA) THEN
    ASM_SIMP_TAC [INTEGER_CLOSED] THEN REAL_ARITH_TAC)

  let REAL_LE_REVERSE_INTEGERS ← prove
   r"!x y. integer(x) /\ integer(y) /\ ~(y + &1 <= x) ==> x <= y"
   (MESON_TAC [REAL_LE_CASES_INTEGERS])

  let REAL_LT_INTEGERS ← prove
   r"!x y. integer(x) /\ integer(y) ==> (x < y <=> x + &1 <= y)"
   (MESON_TAC [REAL_NOT_LT, REAL_LE_CASES_INTEGERS,
               ← REAL_ARITH (← q r"x + &1 <= y ==> x < y")])

  let REAL_EQ_INTEGERS ← prove
   r"!x y. integer x /\ integer y ==> (x = y <=> abs(x - y) < &1)"
   (REWRITE_TAC [← REAL_ARITH (← q r"x = y <=> ~(x < y \/ y < x)")] THEN
    SIMP_TAC [REAL_LT_INTEGERS] THEN REAL_ARITH_TAC)

  let REAL_EQ_INTEGERS_IMP ← prove
   r"!x y. integer x /\ integer y /\ abs(x - y) < &1 ==> x = y"
   (SIMP_TAC [REAL_EQ_INTEGERS])

  let INTEGER_NEG ← prove
   r"!x. integer(--x) <=> integer(x)"
   (MESON_TAC [INTEGER_CLOSED, REAL_NEG_NEG])

  let INTEGER_ABS ← prove
   r"!x. integer(abs x) <=> integer(x)"
   (GEN_TAC THEN REWRITE_TAC [real_abs] THEN COND_CASES_TAC THEN
    REWRITE_TAC [INTEGER_NEG])

  let INTEGER_POS ← prove
   r"!x. &0 <= x ==> (integer(x) <=> ?n. x = &n)"
   (SIMP_TAC [integer, real_abs])

  let NONNEGATIVE_INTEGER ← prove
   r"!x. integer x /\ &0 <= x <=> ?n. x = &n"
   (MESON_TAC [INTEGER_POS, INTEGER_CLOSED, REAL_POS])

  let NONPOSITIVE_INTEGER ← prove
   r"!x. integer x /\ x <= &0 <=> ?n. x = -- &n"
   (GEN_TAC THEN REWRITE_TAC [is_int] THEN
    REWRITE_TAC [LEFT_AND_EXISTS_THM, ← REAL_ARITH (← q r"a + b = &0 <=> a = --b")] THEN
    AP_TERM_TAC THEN ABS_TAC THEN REAL_ARITH_TAC)

  let NONPOSITIVE_INTEGER_ALT ← prove
   r"!x. integer x /\ x <= &0 <=> ?n. x + &n = &0"
   (GEN_TAC THEN REWRITE_TAC [NONPOSITIVE_INTEGER] THEN
    AP_TERM_TAC THEN ABS_TAC THEN REAL_ARITH_TAC)

  let INTEGER_ADD_EQ ← prove
   r"(!x y. integer(x) ==> (integer(x + y) <=> integer(y))) /\
   (!x y. integer(y) ==> (integer(x + y) <=> integer(x)))"
   (MESON_TAC [REAL_ADD_SUB, REAL_ADD_SYM, INTEGER_CLOSED])

  let INTEGER_SUB_EQ ← prove
   r"(!x y. integer(x) ==> (integer(x - y) <=> integer(y))) /\
   (!x y. integer(y) ==> (integer(x - y) <=> integer(x)))"
   (MESON_TAC [REAL_SUB_ADD, REAL_NEG_SUB, INTEGER_CLOSED])

  let FORALL_INTEGER ← prove
   r"!P. (!n. P(&n)) /\ (!x. P x ==> P(--x)) ==> !x. integer x ==> P x"
   (MESON_TAC [INTEGER_CASES])

  let INTEGER_SUM ← prove
   r"!f:A->real s. (!x. x IN s ==> integer(f x)) ==> integer(sum s f)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_CLOSED THEN
    ASM_REWRITE_TAC [INTEGER_CLOSED])

  let INTEGER_ABS_MUL_EQ_1 ← prove
   r"!x y. integer x /\ integer y
         ==> (abs(x * y) = &1 <=> abs x = &1 /\ abs y = &1)"
   (REWRITE_TAC [integer] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [REAL_ABS_MUL] THEN
    REWRITE_TAC [REAL_OF_NUM_EQ, REAL_OF_NUM_MUL, MULT_EQ_1])

  let INTEGER_DIV ← prove
   r"!m n. integer(&m / &n) <=> n = 0 \/ n divides m"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n = 0") THENL
     [ASM_REWRITE_TAC [real_div, REAL_INV_0, REAL_MUL_RZERO, INTEGER_CLOSED],
      ASM_SIMP_TAC [INTEGER_POS, REAL_POS, REAL_LE_DIV, divides] THEN
      ASM_SIMP_TAC [REAL_OF_NUM_EQ, ← REAL_FIELD
       (← q r"~(n = &0) ==> (x / n = y <=> x = n * y)")] THEN
      REWRITE_TAC [REAL_OF_NUM_MUL, REAL_OF_NUM_EQ]])
  return { INTEGER_CASES, REAL_ABS_INTEGER_LEMMA, INTEGER_CLOSED, INTEGER_ADD, 
           INTEGER_SUB, INTEGER_MUL, INTEGER_POW, REAL_LE_INTEGERS, 
           REAL_LE_CASES_INTEGERS, REAL_LE_REVERSE_INTEGERS, REAL_LT_INTEGERS, 
           REAL_EQ_INTEGERS, REAL_EQ_INTEGERS_IMP, INTEGER_NEG, INTEGER_ABS, 
           INTEGER_POS, NONNEGATIVE_INTEGER, NONPOSITIVE_INTEGER, 
           NONPOSITIVE_INTEGER_ALT, INTEGER_ADD_EQ, INTEGER_SUB_EQ, 
           FORALL_INTEGER, INTEGER_SUM, INTEGER_ABS_MUL_EQ_1, INTEGER_DIV }

/- ------------------------------------------------------------------------- -/
/- Similar theorems for rational-valued reals (floor.ml 165-278)             -/
/- ------------------------------------------------------------------------- -/

structure Rational where
  rational : thm
  RATIONAL_INTEGER : thm
  RATIONAL_NUM : thm
  RATIONAL_NEG : thm
  RATIONAL_ABS : thm
  RATIONAL_INV : thm
  RATIONAL_ADD : thm
  RATIONAL_SUB : thm
  RATIONAL_MUL : thm
  RATIONAL_DIV : thm
  RATIONAL_POW : thm
  RATIONAL_CLOSED : thm
  RATIONAL_NEG_EQ : thm
  RATIONAL_ABS_EQ : thm
  RATIONAL_INV_EQ : thm
  RATIONAL_SUM : thm
  RATIONAL_ALT : thm
  deriving Inhabited

@[nospecialize]
def setupRational [HolBase] (D : FloorDeps) (PInteger : Integer) : ExceptT String IO Rational := do
  let { new_definition, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, REAL_ARITH, 
        REAL_FIELD, .. } := D
  let { LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM, .. } := D.core1
  let { REAL_ABS_DIV, REAL_ABS_ZERO, REAL_INV_0, REAL_INV_INV, REAL_MUL_LNEG, 
        REAL_NEG_NEG, REAL_OF_NUM_EQ, RIGHT_AND_EXISTS_THM, SUM_CLOSED, integer, 
        real_abs, real_div, real_pow, real_sub, .. } := D.core2
  let { INTEGER_CLOSED, .. } := PInteger

  let rational ← new_definition
   r"rational x <=> ?m n. integer m /\ integer n /\ ~(n = &0) /\ x = m / n"

  let RATIONAL_INTEGER ← prove
   r"!x. integer x ==> rational x"
   (GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [rational] THEN
    MAP_EVERY EXISTS_TAC [← q r"x:real", ← q r"&1"] THEN
    ASM_SIMP_TAC [INTEGER_CLOSED] THEN CONV_TAC REAL_FIELD)

  let RATIONAL_NUM ← prove
   r"!n. rational(&n)"
   (SIMP_TAC [RATIONAL_INTEGER, INTEGER_CLOSED])

  let RATIONAL_NEG ← prove
   r"!x. rational(x) ==> rational(--x)"
   (REWRITE_TAC [rational, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:real", ← q r"m:real", ← q r"n:real"] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [← q r"--m:real", ← q r"n:real"] THEN
    ASM_SIMP_TAC [INTEGER_CLOSED] THEN CONV_TAC REAL_FIELD)

  let RATIONAL_ABS ← prove
   r"!x. rational(x) ==> rational(abs x)"
   (REWRITE_TAC [real_abs] THEN MESON_TAC [RATIONAL_NEG])

  let RATIONAL_INV ← prove
   r"!x. rational(x) ==> rational(inv x)"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"x = &0") THEN
    ASM_SIMP_TAC [REAL_INV_0, RATIONAL_NUM] THEN
    REWRITE_TAC [rational, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"m:real", ← q r"n:real"] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [← q r"n:real", ← q r"m:real"] THEN
    ASM_SIMP_TAC [INTEGER_CLOSED] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD)

  let RATIONAL_ADD ← prove
   r"!x y. rational(x) /\ rational(y) ==> rational(x + y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [rational, LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC [RIGHT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"m1:real", ← q r"n1:real", ← q r"m2:real", ← q r"n2:real"] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [← q r"m1 * n2 + m2 * n1:real", ← q r"n1 * n2:real"] THEN
    ASM_SIMP_TAC [INTEGER_CLOSED] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD)

  let RATIONAL_SUB ← prove
   r"!x y. rational(x) /\ rational(y) ==> rational(x - y)"
   (SIMP_TAC [real_sub, RATIONAL_NEG, RATIONAL_ADD])

  let RATIONAL_MUL ← prove
   r"!x y. rational(x) /\ rational(y) ==> rational(x * y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [rational, LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC [RIGHT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"m1:real", ← q r"n1:real", ← q r"m2:real", ← q r"n2:real"] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [← q r"m1 * m2:real", ← q r"n1 * n2:real"] THEN
    ASM_SIMP_TAC [INTEGER_CLOSED] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD)

  let RATIONAL_DIV ← prove
   r"!x y. rational(x) /\ rational(y) ==> rational(x / y)"
   (SIMP_TAC [real_div, RATIONAL_INV, RATIONAL_MUL])

  let RATIONAL_POW ← prove
   r"!x n. rational(x) ==> rational(x pow n)"
   (GEN_TAC THEN INDUCT_TAC THEN
    ASM_SIMP_TAC [real_pow, RATIONAL_NUM, RATIONAL_MUL])

  let RATIONAL_CLOSED ← prove
   r"(!n. rational(&n)) /\
   (!x. integer x ==> rational x) /\
   (!x y. rational(x) /\ rational(y) ==> rational(x + y)) /\
   (!x y. rational(x) /\ rational(y) ==> rational(x - y)) /\
   (!x y. rational(x) /\ rational(y) ==> rational(x * y)) /\
   (!x y. rational(x) /\ rational(y) ==> rational(x / y)) /\
   (!x r. rational(x) ==> rational(x pow r)) /\
   (!x. rational(x) ==> rational(--x)) /\
   (!x. rational(x) ==> rational(inv x)) /\
   (!x. rational(x) ==> rational(abs x))"
   (SIMP_TAC [RATIONAL_NUM, RATIONAL_NEG, RATIONAL_ABS, RATIONAL_INV,
              RATIONAL_ADD, RATIONAL_SUB, RATIONAL_MUL, RATIONAL_DIV,
              RATIONAL_POW, RATIONAL_INTEGER])

  let RATIONAL_NEG_EQ ← prove
   r"!x. rational(--x) <=> rational x"
   (MESON_TAC [REAL_NEG_NEG, RATIONAL_NEG])

  let RATIONAL_ABS_EQ ← prove
   r"!x. rational(abs x) <=> rational x"
   (REWRITE_TAC [real_abs] THEN MESON_TAC [RATIONAL_NEG_EQ, RATIONAL_NUM])

  let RATIONAL_INV_EQ ← prove
   r"!x. rational(inv x) <=> rational x"
   (MESON_TAC [REAL_INV_INV, RATIONAL_INV])

  let RATIONAL_SUM ← prove
   r"!s x. (!i. i IN s ==> rational(x i)) ==> rational(sum s x)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_CLOSED THEN
    ASM_SIMP_TAC [RATIONAL_CLOSED])

  let RATIONAL_ALT ← prove
   r"!x. rational(x) <=> ?p q. ~(q = 0) /\ abs x = &p / &q"
   (GEN_TAC THEN REWRITE_TAC [rational] THEN EQ_TAC THENL
     [REWRITE_TAC [integer] THEN STRIP_TAC THEN ASM_REWRITE_TAC [REAL_ABS_DIV] THEN
      ASM_MESON_TAC [REAL_OF_NUM_EQ, REAL_ABS_ZERO],
      STRIP_TAC THEN FIRST_X_ASSUM (DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
       (← REAL_ARITH (← q r"abs(x:real) = a ==> x = a \/ x = --a"))) THEN
      ASM_REWRITE_TAC [real_div, ← GSYM REAL_MUL_LNEG] THEN
      REWRITE_TAC [← GSYM real_div] THEN
      ASM_MESON_TAC [INTEGER_CLOSED, REAL_OF_NUM_EQ]])
  return { rational, RATIONAL_INTEGER, RATIONAL_NUM, RATIONAL_NEG, RATIONAL_ABS, 
           RATIONAL_INV, RATIONAL_ADD, RATIONAL_SUB, RATIONAL_MUL, RATIONAL_DIV, 
           RATIONAL_POW, RATIONAL_CLOSED, RATIONAL_NEG_EQ, RATIONAL_ABS_EQ, 
           RATIONAL_INV_EQ, RATIONAL_SUM, RATIONAL_ALT }

/- ------------------------------------------------------------------------- -/
/- The floor and frac functions (floor.ml 280-314)                           -/
/- ------------------------------------------------------------------------- -/

structure FloorFrac where
  REAL_TRUNCATE_POS : thm
  REAL_TRUNCATE : thm
  FLOOR_FRAC : thm
  deriving Inhabited

@[nospecialize]
def setupFloorFrac [HolBase] (D : FloorDeps) (PInteger : Integer) : ExceptT String IO FloorFrac := do
  let { new_specification, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, INDUCT_TAC, 
        REAL_ARITH, .. } := D
  let { LEFT_IMP_EXISTS_THM, LE_REFL, LT, LT_SUC_LE, .. } := D.core1
  let { REAL_ADD_SUB, REAL_ARCH_SIMPLE, REAL_LE_LT, REAL_LE_TOTAL, REAL_NOT_LE, 
        REAL_OF_NUM_SUC, SKOLEM_THM, integer, num_WOP, .. } := D.core2
  let { INTEGER_CLOSED, .. } := PInteger

  let REAL_TRUNCATE_POS ← prove
   r"!x. &0 <= x ==> ?n r. &0 <= r /\ r < &1 /\ (x = &n + r)"
   (REPEAT STRIP_TAC THEN MP_TAC (← SPEC (← q r"x:real") REAL_ARCH_SIMPLE) THEN
    GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    INDUCT_TAC THEN REWRITE_TAC [LT_SUC_LE, ← CONJUNCT1 LT] THENL
     [DISCH_TAC THEN MAP_EVERY EXISTS_TAC [← q r"0", ← q r"&0"] THEN ASM_REAL_ARITH_TAC,
      POP_ASSUM_LIST (K ALL_TAC)] THEN
    REWRITE_TAC [← GSYM REAL_OF_NUM_SUC] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC (← q r"n:num"))) THEN
    REWRITE_TAC [LE_REFL, REAL_NOT_LE] THEN DISCH_TAC THEN
    FIRST_X_ASSUM (DISJ_CASES_THEN STRIP_ASSUME_TAC o REWRITE_RULE [REAL_LE_LT])
    THENL
     [MAP_EVERY EXISTS_TAC [← q r"n:num", ← q r"x - &n"] THEN ASM_REAL_ARITH_TAC,
      MAP_EVERY EXISTS_TAC [← q r"SUC n", ← q r"x - &(SUC n)"] THEN
      REWRITE_TAC [REAL_ADD_SUB, ← GSYM REAL_OF_NUM_SUC] THEN ASM_REAL_ARITH_TAC])

  let REAL_TRUNCATE ← prove
   r"!x. ?n r. integer(n) /\ &0 <= r /\ r < &1 /\ (x = n + r)"
   (GEN_TAC THEN DISJ_CASES_TAC (← SPECL [← q r"x:real", ← q r"&0"] REAL_LE_TOTAL) THENL
     [MP_TAC (← SPEC (← q r"--x") REAL_ARCH_SIMPLE) THEN
      REWRITE_TAC [← REAL_ARITH (← q r"--a <= b <=> &0 <= a + b")] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"n:num")
       (MP_TAC o MATCH_MP REAL_TRUNCATE_POS)) THEN
      REWRITE_TAC [← REAL_ARITH (← q r"(a + b = c + d) <=> (a = (c - b) + d)")],
      ALL_TAC] THEN
    ASM_MESON_TAC [integer, INTEGER_CLOSED, REAL_TRUNCATE_POS])

  let FLOOR_FRAC ←
      new_specification ["floor", "frac"]
         (← REWRITE_RULE [SKOLEM_THM] REAL_TRUNCATE)
  return { REAL_TRUNCATE_POS, REAL_TRUNCATE, FLOOR_FRAC }

/- ------------------------------------------------------------------------- -/
/- Useful lemmas about floor and frac (floor.ml 316-504)                     -/
/- ------------------------------------------------------------------------- -/

structure FloorLemmas where
  FLOOR_UNIQUE : thm
  FLOOR_EQ_0 : thm
  FLOOR : thm
  FLOOR_DOUBLE : thm
  FRAC_FLOOR : thm
  FLOOR_NUM : thm
  REAL_LE_FLOOR : thm
  REAL_FLOOR_LE : thm
  REAL_FLOOR_LT : thm
  REAL_LT_FLOOR : thm
  FLOOR_POS : thm
  FLOOR_DIV_DIV : thm
  FLOOR_MONO : thm
  REAL_FLOOR_EQ : thm
  REAL_FLOOR_LT_REFL : thm
  REAL_FRAC_EQ_0 : thm
  REAL_FRAC_POS_LT : thm
  FRAC_NUM : thm
  REAL_FLOOR_REFL : thm
  REAL_FRAC_ZERO : thm
  REAL_FLOOR_ADD : thm
  REAL_FLOOR_TRIANGLE : thm
  REAL_FLOOR_NEG : thm
  REAL_FRAC_ADD : thm
  FLOOR_POS_LE : thm
  FRAC_UNIQUE : thm
  REAL_FRAC_EQ : thm
  INTEGER_ROUND : thm
  FRAC_DIV_MOD : thm
  FRAC_NEG : thm
  REAL_FLOOR_FLOOR_DIV : thm
  deriving Inhabited

@[nospecialize]
def setupFloorLemmas [HolBase] (D : FloorDeps) (PInteger : Integer) (PFloorFrac : FloorFrac) : ExceptT String IO FloorLemmas := do
  let { ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON, MESON_TAC, 
        REAL_ARITH, REAL_ARITH_TAC, REAL_FIELD, .. } := D
  let { ADD_SUB, ADD_SYM, CONTRAPOS_THM, DIVISION, LE_1, LE_ADD, LT_NZ, .. } := D.core1
  let { MONO_FORALL, REAL_ADD_LID, REAL_INV_0, REAL_LE_DIV, REAL_LE_RDIV_EQ, 
        REAL_LE_REFL, REAL_LE_TRANS, REAL_LT_LDIV_EQ, REAL_LT_LE, REAL_MUL_LID, 
        REAL_MUL_RZERO, REAL_NOT_LE, REAL_NOT_LT, REAL_OF_NUM_ADD, 
        REAL_OF_NUM_EQ, REAL_OF_NUM_LE, REAL_OF_NUM_LT, REAL_OF_NUM_MUL, 
        REAL_OF_NUM_SUB, REAL_POS, REAL_SUB_0, REAL_SUB_LT, REAL_SUB_REFL, 
        integer, real_abs, real_div, .. } := D.core2
  let { REAL_ABS_INTEGER_LEMMA, INTEGER_CLOSED, REAL_LE_REVERSE_INTEGERS, 
        REAL_LT_INTEGERS, .. } := PInteger
  let { FLOOR_FRAC, .. } := PFloorFrac

  let FLOOR_UNIQUE ← prove
   r"!x a. integer(a) /\ a <= x /\ x < a + &1 <=> (floor x = a)"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [STRIP_TAC THEN STRIP_ASSUME_TAC (← SPEC (← q r"x:real") FLOOR_FRAC) THEN
      SUBGOAL_THEN (← q r"abs(floor x - a) < &1") MP_TAC THENL
       [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
      DISCH_TAC THEN REWRITE_TAC [REAL_NOT_LT] THEN
      MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN CONJ_TAC THENL
       [ASM_MESON_TAC [INTEGER_CLOSED], ASM_REAL_ARITH_TAC],
      DISCH_THEN (SUBST1_TAC o SYM) THEN
      MP_TAC (← SPEC (← q r"x:real") FLOOR_FRAC) THEN
      SIMP_TAC [] THEN REAL_ARITH_TAC])

  let FLOOR_EQ_0 ← prove
   r"!x. (floor x = &0) <=> &0 <= x /\ x < &1"
   (GEN_TAC THEN REWRITE_TAC [← GSYM FLOOR_UNIQUE] THEN
    REWRITE_TAC [INTEGER_CLOSED, REAL_ADD_LID])

  let FLOOR ← prove
   r"!x. integer(floor x) /\ floor(x) <= x /\ x < floor(x) + &1"
   (GEN_TAC THEN MP_TAC (← SPEC (← q r"x:real") FLOOR_FRAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC)

  let FLOOR_DOUBLE ← prove
   r"!u. &2 * floor(u) <= floor(&2 * u) /\ floor(&2 * u) <= &2 * floor(u) + &1"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_REVERSE_INTEGERS THEN
    SIMP_TAC [INTEGER_CLOSED, FLOOR] THEN
    MP_TAC (← SPEC (← q r"u:real") FLOOR) THEN MP_TAC (← SPEC (← q r"&2 * u") FLOOR) THEN
    REAL_ARITH_TAC)

  let FRAC_FLOOR ← prove
   r"!x. frac(x) = x - floor(x)"
   (MP_TAC FLOOR_FRAC THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC)

  let FLOOR_NUM ← prove
   r"!n. floor(&n) = &n"
   (REWRITE_TAC [← GSYM FLOOR_UNIQUE, INTEGER_CLOSED] THEN REAL_ARITH_TAC)

  let REAL_LE_FLOOR ← prove
   r"!x n. integer(n) ==> (n <= floor x <=> n <= x)"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [ASM_MESON_TAC [FLOOR, REAL_LE_TRANS], ALL_TAC] THEN
    REWRITE_TAC [← GSYM REAL_NOT_LT] THEN ASM_SIMP_TAC [REAL_LT_INTEGERS, FLOOR] THEN
    MP_TAC (← SPEC (← q r"x:real") FLOOR) THEN REAL_ARITH_TAC)

  let REAL_FLOOR_LE ← prove
   r"!x n. integer n ==> (floor x <= n <=> x - &1 < n)"
   (REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"x <= y <=> x + &1 <= y + &1")] THEN
    ASM_SIMP_TAC [← GSYM REAL_LT_INTEGERS, FLOOR, INTEGER_CLOSED] THEN
    ONCE_REWRITE_TAC [← TAUT (← q r"(p <=> q) <=> (~p <=> ~q)")] THEN
    ASM_SIMP_TAC [REAL_NOT_LT, REAL_LE_FLOOR, INTEGER_CLOSED] THEN
    REAL_ARITH_TAC)

  let REAL_FLOOR_LT ← prove
   r"!x n. integer n ==> (floor x < n <=> x < n)"
   (SIMP_TAC [← GSYM REAL_NOT_LE, REAL_LE_FLOOR])

  let REAL_LT_FLOOR ← prove
   r"!x n. integer n ==> (n < floor x <=> n <= x - &1)"
   (SIMP_TAC [← GSYM REAL_NOT_LE, REAL_FLOOR_LE])

  let FLOOR_POS ← prove
   r"!x. &0 <= x ==> ?n. floor(x) = &n"
   (REPEAT STRIP_TAC THEN MP_TAC (← CONJUNCT1 (← SPEC (← q r"x:real") FLOOR)) THEN
    REWRITE_TAC [integer] THEN
    ASM_SIMP_TAC [real_abs, REAL_LE_FLOOR, FLOOR, INTEGER_CLOSED])

  let FLOOR_DIV_DIV ← prove
   r"!m n. ~(m = 0) ==> floor(&n / &m) = &(n DIV m)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM FLOOR_UNIQUE, INTEGER_CLOSED] THEN
    ASM_SIMP_TAC [REAL_LE_RDIV_EQ, REAL_LT_LDIV_EQ, REAL_OF_NUM_LT,
                  REAL_OF_NUM_LE, REAL_OF_NUM_MUL, REAL_OF_NUM_ADD, LT_NZ] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"n:num") o MATCH_MP DIVISION) THEN ARITH_TAC)

  let FLOOR_MONO ← prove
   r"!x y. x <= y ==> floor x <= floor y"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_NOT_LT] THEN
    SIMP_TAC [FLOOR, REAL_LT_INTEGERS] THEN
    MAP_EVERY (MP_TAC o C SPEC FLOOR) [← q r"x:real", ← q r"y:real"] THEN REAL_ARITH_TAC)

  let REAL_FLOOR_EQ ← prove
   r"!x. floor x = x <=> integer x"
   (REWRITE_TAC [← GSYM FLOOR_UNIQUE, REAL_LE_REFL, ← REAL_ARITH (← q r"x < x + &1")])

  let REAL_FLOOR_LT_REFL ← prove
   r"!x. floor x < x <=> ~(integer x)"
   (MESON_TAC [REAL_LT_LE, REAL_FLOOR_EQ, FLOOR])

  let REAL_FRAC_EQ_0 ← prove
   r"!x. frac x = &0 <=> integer x"
   (REWRITE_TAC [FRAC_FLOOR, REAL_SUB_0] THEN MESON_TAC [REAL_FLOOR_EQ])

  let REAL_FRAC_POS_LT ← prove
   r"!x. &0 < frac x <=> ~(integer x)"
   (REWRITE_TAC [FRAC_FLOOR, REAL_SUB_LT, REAL_FLOOR_LT_REFL])

  let FRAC_NUM ← prove
   r"!n. frac(&n) = &0"
   (REWRITE_TAC [REAL_FRAC_EQ_0, INTEGER_CLOSED])

  let REAL_FLOOR_REFL ← prove
   r"!x. integer x ==> floor x = x"
   (REWRITE_TAC [REAL_FLOOR_EQ])

  let REAL_FRAC_ZERO ← prove
   r"!x. integer x ==> frac x = &0"
   (REWRITE_TAC [REAL_FRAC_EQ_0])

  let REAL_FLOOR_ADD ← prove
   r"!x y. floor(x + y) = if frac x + frac y < &1 then floor(x) + floor(y)
                        else (floor(x) + floor(y)) + &1"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM FLOOR_UNIQUE] THEN
    CONJ_TAC THENL [ASM_MESON_TAC [INTEGER_CLOSED, FLOOR], ALL_TAC] THEN
    MAP_EVERY (MP_TAC o C SPEC FLOOR_FRAC) [← q r"x:real", ← q r"y:real", ← q r"x + y:real"] THEN
    REAL_ARITH_TAC)

  let REAL_FLOOR_TRIANGLE ← prove
   r"!x y. floor(x) + floor(y) <= floor(x + y) /\
         floor(x + y) <= (floor x + floor y) + &1"
   (REPEAT GEN_TAC THEN REWRITE_TAC [REAL_FLOOR_ADD] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC)

  let REAL_FLOOR_NEG ← prove
   r"!x. floor(--x) = if integer x then --x else --(floor x + &1)"
   (GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [← GSYM FLOOR_UNIQUE] THEN
    MP_TAC (← SPEC (← q r"x:real") FLOOR) THEN
    MP_TAC (← SPEC (← q r"x:real") REAL_FLOOR_EQ) THEN
    ASM_SIMP_TAC [INTEGER_CLOSED] THEN REAL_ARITH_TAC)

  let REAL_FRAC_ADD ← prove
   r"!x y. frac(x + y) = if frac x + frac y < &1 then frac(x) + frac(y)
                       else (frac(x) + frac(y)) - &1"
   (REWRITE_TAC [FRAC_FLOOR, REAL_FLOOR_ADD] THEN REAL_ARITH_TAC)

  let FLOOR_POS_LE ← prove
   r"!x. &0 <= floor x <=> &0 <= x"
   (SIMP_TAC [REAL_LE_FLOOR, INTEGER_CLOSED])

  let FRAC_UNIQUE ← prove
   r"!x a. integer(x - a) /\ &0 <= a /\ a < &1 <=> frac x = a"
   (REWRITE_TAC [FRAC_FLOOR, ← REAL_ARITH (← q r"x - f:real = a <=> f = x - a")] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM FLOOR_UNIQUE] THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC)

  let REAL_FRAC_EQ ← prove
   r"!x. frac x = x <=> &0 <= x /\ x < &1"
   (REWRITE_TAC [← GSYM FRAC_UNIQUE, REAL_SUB_REFL, INTEGER_CLOSED])

  let INTEGER_ROUND ← prove
   r"!x. ?n. integer n /\ abs(x - n) <= &1 / &2"
   (GEN_TAC THEN MATCH_MP_TAC (← MESON [] (← q r"!a. P a \/ P(a + &1) ==> ?x. P x")) THEN
    EXISTS_TAC (← q r"floor x") THEN MP_TAC (← ISPEC (← q r"x:real") FLOOR) THEN
    SIMP_TAC [INTEGER_CLOSED] THEN REAL_ARITH_TAC)

  let FRAC_DIV_MOD ← prove
   r"!m n. ~(n = 0) ==> frac(&m / &n) = &(m MOD n) / &n"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM FRAC_UNIQUE] THEN
    ASM_SIMP_TAC [REAL_LE_DIV, REAL_POS, REAL_LT_LDIV_EQ, REAL_OF_NUM_LT, LE_1,
                  ← REAL_ARITH (← q r"x / a - y / a:real = (x - y) / a")] THEN
    MP_TAC (← SPECL [← q r"m:num", ← q r"n:num"] DIVISION) THEN
    ASM_SIMP_TAC [REAL_OF_NUM_LT, REAL_MUL_LID] THEN
    DISCH_THEN (fun th => tactic_of do pure (
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV o RAND_CONV)
                      [← CONJUNCT1 th])) THEN
    SIMP_TAC [REAL_OF_NUM_SUB, ← ONCE_REWRITE_RULE [ADD_SYM] LE_ADD, ADD_SUB] THEN
    ASM_SIMP_TAC [← GSYM REAL_OF_NUM_MUL, REAL_OF_NUM_EQ, INTEGER_CLOSED,
                  ← REAL_FIELD (← q r"~(n:real = &0) ==> (x * n) / n = x")])

  let FRAC_NEG ← prove
   r"!x. frac(--x) = if integer x then &0 else &1 - frac x"
   (GEN_TAC THEN REWRITE_TAC [FRAC_FLOOR, REAL_FLOOR_NEG] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC)

  let REAL_FLOOR_FLOOR_DIV ← prove
   r"!x n. floor(floor x / &n) = floor(x / &n)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_REWRITE_TAC [real_div, REAL_INV_0, REAL_MUL_RZERO] THEN
    REWRITE_TAC [← GSYM real_div, ← GSYM FLOOR_UNIQUE, FLOOR] THEN
    ASM_SIMP_TAC [REAL_LT_LDIV_EQ, REAL_LE_RDIV_EQ, REAL_OF_NUM_LT, LE_1] THEN
    SIMP_TAC [REAL_FLOOR_LT, REAL_LE_FLOOR, FLOOR, INTEGER_CLOSED] THEN
    ASM_SIMP_TAC [← GSYM REAL_LT_LDIV_EQ, ← GSYM REAL_LE_RDIV_EQ,
                  REAL_OF_NUM_LT, LE_1, FLOOR])
  return { FLOOR_UNIQUE, FLOOR_EQ_0, FLOOR, FLOOR_DOUBLE, FRAC_FLOOR, FLOOR_NUM, 
           REAL_LE_FLOOR, REAL_FLOOR_LE, REAL_FLOOR_LT, REAL_LT_FLOOR, FLOOR_POS, 
           FLOOR_DIV_DIV, FLOOR_MONO, REAL_FLOOR_EQ, REAL_FLOOR_LT_REFL, 
           REAL_FRAC_EQ_0, REAL_FRAC_POS_LT, FRAC_NUM, REAL_FLOOR_REFL, 
           REAL_FRAC_ZERO, REAL_FLOOR_ADD, REAL_FLOOR_TRIANGLE, REAL_FLOOR_NEG, 
           REAL_FRAC_ADD, FLOOR_POS_LE, FRAC_UNIQUE, REAL_FRAC_EQ, INTEGER_ROUND, 
           FRAC_DIV_MOD, FRAC_NEG, REAL_FLOOR_FLOOR_DIV }

/- ------------------------------------------------------------------------- -/
/- Assertions that there are integers between well-spaced reals (floor.ml 506-552) -/
/- ------------------------------------------------------------------------- -/

structure Between where
  INTEGER_EXISTS_BETWEEN_ALT : thm
  INTEGER_EXISTS_BETWEEN_LT : thm
  INTEGER_EXISTS_BETWEEN : thm
  INTEGER_EXISTS_BETWEEN_ABS : thm
  INTEGER_EXISTS_BETWEEN_ABS_LT : thm
  deriving Inhabited

@[nospecialize]
def setupBetween [HolBase] (D : FloorDeps) (PInteger : Integer) (PFloorLemmas : FloorLemmas) : ExceptT String IO Between := do
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, .. } := D
  let { MONO_EXISTS, REAL_LT_IMP_LE, REAL_LT_LE, real_abs, .. } := D.core2
  let { INTEGER_CLOSED, .. } := PInteger
  let { FLOOR, .. } := PFloorLemmas

  let INTEGER_EXISTS_BETWEEN_ALT ← prove
   r"!x y. x + &1 <= y ==> ?n. integer n /\ x < n /\ n <= y"
   (REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"floor y") THEN
    MP_TAC (← SPEC (← q r"y:real") FLOOR) THEN SIMP_TAC [] THEN ASM_REAL_ARITH_TAC)

  let INTEGER_EXISTS_BETWEEN_LT ← prove
   r"!x y. x + &1 < y ==> ?n. integer n /\ x < n /\ n < y"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"integer y") THENL
     [EXISTS_TAC (← q r"y - &1:real") THEN
      ASM_SIMP_TAC [INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC,
      FIRST_ASSUM (MP_TAC o MATCH_MP INTEGER_EXISTS_BETWEEN_ALT o
        MATCH_MP REAL_LT_IMP_LE) THEN
      MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [REAL_LT_LE] THEN ASM_MESON_TAC []])

  let INTEGER_EXISTS_BETWEEN ← prove
   r"!x y. x + &1 <= y ==> ?n. integer n /\ x <= n /\ n < y"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"integer y") THENL
     [EXISTS_TAC (← q r"y - &1:real") THEN
      ASM_SIMP_TAC [INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC,
      FIRST_ASSUM (MP_TAC o MATCH_MP INTEGER_EXISTS_BETWEEN_ALT) THEN
      MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [REAL_LT_LE] THENL [ASM_REAL_ARITH_TAC, ASM_MESON_TAC []]])

  let INTEGER_EXISTS_BETWEEN_ABS ← prove
   r"!x y. &1 <= abs(x - y)
         ==> ?n. integer n /\ (x <= n /\ n < y \/ y <= n /\ n < x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [real_abs] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THENL
     [MP_TAC (← ISPECL [← q r"y:real", ← q r"x:real"] INTEGER_EXISTS_BETWEEN),
      MP_TAC (← ISPECL [← q r"x:real", ← q r"y:real"] INTEGER_EXISTS_BETWEEN)] THEN
    (ANTS_TAC THENL [ASM_REAL_ARITH_TAC, MATCH_MP_TAC MONO_EXISTS]) THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [])

  let INTEGER_EXISTS_BETWEEN_ABS_LT ← prove
   r"!x y. &1 < abs(x - y)
         ==> ?n. integer n /\ (x < n /\ n < y \/ y < n /\ n < x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [real_abs] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THENL
     [MP_TAC (← ISPECL [← q r"y:real", ← q r"x:real"] INTEGER_EXISTS_BETWEEN_LT),
      MP_TAC (← ISPECL [← q r"x:real", ← q r"y:real"] INTEGER_EXISTS_BETWEEN_LT)] THEN
    (ANTS_TAC THENL [ASM_REAL_ARITH_TAC, MATCH_MP_TAC MONO_EXISTS]) THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [])
  return { INTEGER_EXISTS_BETWEEN_ALT, INTEGER_EXISTS_BETWEEN_LT, 
           INTEGER_EXISTS_BETWEEN, INTEGER_EXISTS_BETWEEN_ABS, 
           INTEGER_EXISTS_BETWEEN_ABS_LT }

/- ------------------------------------------------------------------------- -/
/- More trivial theorems about real_of_int (floor.ml 554-565)                -/
/- ------------------------------------------------------------------------- -/

structure RealOfInt where
  REAL_OF_INT_OF_REAL : thm
  IMAGE_REAL_OF_INT_UNIV : thm
  deriving Inhabited

@[nospecialize]
def setupRealOfInt [HolBase] (D : FloorDeps) : ExceptT String IO RealOfInt := do
  let { MESON_TAC, .. } := D
  let { EXTENSION, IN, IN_IMAGE, IN_UNIV, .. } := D.core1
  let { int_rep, int_tybij, .. } := D.core2

  let REAL_OF_INT_OF_REAL ← prove
   r"!x. integer(x) ==> real_of_int(int_of_real x) = x"
   (SIMP_TAC [int_rep])

  let IMAGE_REAL_OF_INT_UNIV ← prove
   r"IMAGE real_of_int (:int) = integer"
   (REWRITE_TAC [EXTENSION, IN_IMAGE, IN_UNIV] THEN
    REWRITE_TAC [IN] THEN MESON_TAC [int_tybij])
  return { REAL_OF_INT_OF_REAL, IMAGE_REAL_OF_INT_UNIV }

/- ------------------------------------------------------------------------- -/
/- Finiteness of bounded set of integers (floor.ml 567-652)                  -/
/- ------------------------------------------------------------------------- -/

structure Finite where
  HAS_SIZE_INTSEG_NUM : thm
  FINITE_INTSEG : thm
  HAS_SIZE_INTSEG_INT : thm
  CARD_INTSEG_INT : thm
  REAL_CARD_INTSEG_INT : thm
  deriving Inhabited

@[nospecialize]
def setupFinite [HolBase] (D : FloorDeps) (PInteger : Integer) (PRealOfInt : RealOfInt) : ExceptT String IO Finite := do
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, REAL_ARITH, REAL_ARITH_TAC, .. } := D
  let { EMPTY_GSPEC, EXTENSION, FINITE_IMAGE, FINITE_NUMSEG, FINITE_SUBSET, 
        FINITE_UNION, HAS_SIZE, HAS_SIZE_0, HAS_SIZE_IMAGE_INJ, HAS_SIZE_NUMSEG, 
        HAS_SIZE_NUMSEG_LE, INT_OF_NUM_OF_INT, IN_ELIM_THM, IN_IMAGE, IN_NUMSEG, 
        IN_UNION, LEFT_IMP_EXISTS_THM, .. } := D.core1
  let { NUM_OF_INT_OF_NUM, REAL_ARCH_SIMPLE, REAL_EQ_ADD_LCANCEL, REAL_EQ_NEG2, 
        REAL_MAX_LE, REAL_NOT_LT, REAL_OF_NUM_ADD, REAL_OF_NUM_EQ, 
        REAL_OF_NUM_LE, REAL_SUB_LE, SUBSET, SURJECTIVE_IMAGE_EQ, UNWIND_THM1, 
        int_le, int_of_num, int_of_num_th, .. } := D.core2
  let { INTEGER_CASES, INTEGER_CLOSED, INTEGER_POS, .. } := PInteger
  let { REAL_OF_INT_OF_REAL, .. } := PRealOfInt

  let HAS_SIZE_INTSEG_NUM ← prove
   r"!m n. {x | integer(x) /\ &m <= x /\ x <= &n} HAS_SIZE ((n + 1) - m)"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"{x | integer(x) /\ &m <= x /\ x <= &n} =
                  IMAGE real_of_num (m..n)")
    SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN
      X_GEN_TAC (← q r"x:real") THEN ASM_CASES_TAC (← q r"?k. x = &k") THENL
       [FIRST_X_ASSUM (CHOOSE_THEN SUBST_ALL_TAC) THEN
        REWRITE_TAC [REAL_OF_NUM_LE, INTEGER_CLOSED, REAL_OF_NUM_EQ] THEN
        REWRITE_TAC [UNWIND_THM1, IN_NUMSEG],
        ASM_MESON_TAC [INTEGER_POS, ← REAL_ARITH (← q r"&n <= x ==> &0 <= x")]],
      MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN REWRITE_TAC [HAS_SIZE_NUMSEG] THEN
      SIMP_TAC [REAL_OF_NUM_EQ]])

  let FINITE_INTSEG ← prove
   r"!a b. FINITE {x | integer(x) /\ a <= x /\ x <= b}"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPEC (← q r"max (abs a) (abs b)") REAL_ARCH_SIMPLE) THEN
    REWRITE_TAC [REAL_MAX_LE, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"n:num") THEN STRIP_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC (← q r"{x | integer(x) /\ abs(x) <= &n}") THEN CONJ_TAC THENL
     [ALL_TAC, SIMP_TAC [SUBSET, IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC (← q r"IMAGE (\x. &x) (0..n) UNION IMAGE (\x. --(&x)) (0..n)") THEN
    ASM_SIMP_TAC [FINITE_UNION, FINITE_IMAGE, FINITE_NUMSEG] THEN
    REWRITE_TAC [INTEGER_CASES, SUBSET, IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC [IN_UNION, IN_IMAGE, REAL_OF_NUM_EQ, REAL_EQ_NEG2] THEN
    REWRITE_TAC [UNWIND_THM1, IN_NUMSEG] THEN
    REWRITE_TAC [← GSYM REAL_OF_NUM_LE] THEN
    ASM_REAL_ARITH_TAC)

  let HAS_SIZE_INTSEG_INT ← prove
   r"!a b. integer a /\ integer b
         ==> {x | integer(x) /\ a <= x /\ x <= b} HAS_SIZE
             if b < a then 0 else num_of_int(int_of_real(b - a + &1))"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"{x | integer(x) /\ a <= x /\ x <= b} =
      IMAGE (\n. a + &n) {n | &n <= b - a}")
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
      ASM_SIMP_TAC [IN_ELIM_THM, INTEGER_CLOSED] THEN
      CONJ_TAC THENL [ALL_TAC, REAL_ARITH_TAC] THEN
      X_GEN_TAC (← q r"c:real") THEN STRIP_TAC THEN
      ONCE_REWRITE_TAC [← REAL_ARITH (← q r"a + x:real = y <=> y - a = x")] THEN
      ASM_SIMP_TAC [← GSYM INTEGER_POS, REAL_SUB_LE, INTEGER_CLOSED],
      MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN

      SIMP_TAC [REAL_EQ_ADD_LCANCEL, REAL_OF_NUM_EQ] THEN
      COND_CASES_TAC THENL
       [ASM_SIMP_TAC [← REAL_ARITH (← q r"b < a ==> ~(&n <= b - a)")] THEN
        REWRITE_TAC [HAS_SIZE_0, EMPTY_GSPEC],
        SUBGOAL_THEN (← q r"?m. b - a = &m") (CHOOSE_THEN SUBST1_TAC) THENL
         [ASM_MESON_TAC [INTEGER_POS, INTEGER_CLOSED, REAL_NOT_LT, REAL_SUB_LE],
          REWRITE_TAC [REAL_OF_NUM_ADD, REAL_OF_NUM_LE, ← GSYM int_of_num,
                       NUM_OF_INT_OF_NUM, HAS_SIZE_NUMSEG_LE]]]])

  let CARD_INTSEG_INT ← prove
   r"!a b. integer a /\ integer b
         ==> CARD {x | integer(x) /\ a <= x /\ x <= b} =
             if b < a then 0 else num_of_int(int_of_real(b - a + &1))"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (MP_TAC o MATCH_MP HAS_SIZE_INTSEG_INT) THEN
    SIMP_TAC [HAS_SIZE])

  let REAL_CARD_INTSEG_INT ← prove
   r"!a b. integer a /\ integer b
         ==> &(CARD {x | integer(x) /\ a <= x /\ x <= b}) =
             if b < a then &0 else b - a + &1"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [CARD_INTSEG_INT] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [REAL_OF_INT_OF_REAL] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [← GSYM int_of_num_th] THEN
    W (MP_TAC o PART_MATCH (lhs o rand) INT_OF_NUM_OF_INT o
      rand o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC [int_le, int_of_num_th, REAL_OF_INT_OF_REAL,
                    INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC,
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC REAL_OF_INT_OF_REAL THEN
      ASM_SIMP_TAC [INTEGER_CLOSED]])
  return { HAS_SIZE_INTSEG_NUM, FINITE_INTSEG, HAS_SIZE_INTSEG_INT, 
           CARD_INTSEG_INT, REAL_CARD_INTSEG_INT }

/- ------------------------------------------------------------------------- -/
/- Yet set of all integers or rationals is infinite (floor.ml 654-672)       -/
/- ------------------------------------------------------------------------- -/

structure Infinite where
  INFINITE_INTEGER : thm
  INFINITE_RATIONAL : thm
  deriving Inhabited

@[nospecialize]
def setupInfinite [HolBase] (D : FloorDeps) (PInteger : Integer) (PRational : Rational) : ExceptT String IO Infinite := do
  let { CONTRAPOS_THM, FINITE_SUBSET, FORALL_IN_IMAGE, IMP_CONJ_ALT, IN, 
        INFINITE, INFINITE_IMAGE_INJ, IN_UNIV, .. } := D.core1
  let { REAL_OF_NUM_EQ, SUBSET, num_INFINITE, .. } := D.core2
  let { INTEGER_CLOSED, .. } := PInteger
  let { RATIONAL_INTEGER, .. } := PRational

  let INFINITE_INTEGER ← prove
   r"INFINITE integer"
   (SUBGOAL_THEN (← q r"INFINITE(IMAGE real_of_num (:num))") MP_TAC THENL
     [SIMP_TAC [INFINITE_IMAGE_INJ, REAL_OF_NUM_EQ, num_INFINITE], ALL_TAC] THEN
    REWRITE_TAC [INFINITE, CONTRAPOS_THM] THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] FINITE_SUBSET) THEN
    REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_UNIV] THEN
    REWRITE_TAC [IN, INTEGER_CLOSED])

  let INFINITE_RATIONAL ← prove
   r"INFINITE rational"
   (MP_TAC INFINITE_INTEGER THEN
    REWRITE_TAC [INFINITE, CONTRAPOS_THM] THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] FINITE_SUBSET) THEN
    REWRITE_TAC [SUBSET, IN, RATIONAL_INTEGER])
  return { INFINITE_INTEGER, INFINITE_RATIONAL }

/- ------------------------------------------------------------------------- -/
/- Arbitrarily good rational approximations (floor.ml 674-812)               -/
/- ------------------------------------------------------------------------- -/

structure Approx where
  PADIC_RATIONAL_APPROXIMATION_STRADDLE : thm
  PADIC_RATIONAL_APPROXIMATION_STRADDLE_POS : thm
  PADIC_RATIONAL_APPROXIMATION_STRADDLE_POS_LE : thm
  RATIONAL_APPROXIMATION : thm
  RATIONAL_BETWEEN : thm
  RATIONAL_BETWEEN_EQ : thm
  RATIONAL_APPROXIMATION_STRADDLE : thm
  RATIONAL_APPROXIMATION_ABOVE : thm
  RATIONAL_APPROXIMATION_BELOW : thm
  INFINITE_RATIONAL_IN_RANGE : thm
  deriving Inhabited

@[nospecialize]
def setupApprox [HolBase] (D : FloorDeps) (PInteger : Integer) (PRational : Rational) (PFloorLemmas : FloorLemmas) : ExceptT String IO Approx := do
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, 
        SET_TAC, .. } := D
  let { CONJ_ASSOC, DEPENDENT_CHOICE, IMP_IMP, INFINITE_IMAGE, INFINITE_SUPERSET, 
        IN_UNIV, LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM, LT_CASES, .. } := D.core1
  let { MONO_EXISTS, REAL_ABS_DIV, REAL_ABS_NUM, REAL_ABS_POW, REAL_ARCH_POW, 
        REAL_LE_LDIV_EQ, REAL_LE_MUL, REAL_LE_RDIV_EQ, REAL_LT_DIV, 
        REAL_LT_IMP_LE, REAL_LT_INV_EQ, REAL_LT_LDIV_EQ, REAL_LT_MIN, 
        REAL_LT_MUL, REAL_LT_RDIV_EQ, REAL_LT_REFL, REAL_LT_TRANS, REAL_MUL_LNEG, 
        REAL_MUL_LZERO, REAL_MUL_SYM, REAL_POW_LE, REAL_POW_LT, 
        RIGHT_AND_EXISTS_THM, SWAP_EXISTS_THM, TRANSITIVE_STEPWISE_LT, integer, 
        num_INFINITE, real_div, .. } := D.core2
  let { INTEGER_CLOSED, .. } := PInteger
  let { RATIONAL_CLOSED, .. } := PRational
  let { FLOOR, .. } := PFloorLemmas

  let PADIC_RATIONAL_APPROXIMATION_STRADDLE ← prove
   r"!p x e. &0 < e /\ &1 < p
           ==> ?n q r. integer q /\ integer r /\
                       q / p pow n < x /\ x < r / p pow n /\
                       abs(q / p pow n - r / p pow n) < e"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"p:real", ← q r"&2 / e:real"] REAL_ARCH_POW) THEN
    ASM_SIMP_TAC [REAL_LT_LDIV_EQ] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC (← q r"n:num") THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
    ASM_SIMP_TAC [← GSYM REAL_LT_LDIV_EQ, REAL_POW_LT,
                  ← REAL_ARITH (← q r"&1 < p ==> &0 < p")] THEN
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC
     [← q r"floor(p pow n * x) - &1", ← q r"floor(p pow n * x) + &1"] THEN
    REWRITE_TAC [← REAL_ARITH
     (← q r"abs((x - &1) / p - (x + &1) / p) = abs(&2 / p)")] THEN
    ASM_SIMP_TAC [FLOOR, INTEGER_CLOSED, REAL_LT_LDIV_EQ, REAL_LT_RDIV_EQ,
                  REAL_POW_LT, ← REAL_ARITH (← q r"&1 < p ==> &0 < p")] THEN
    REWRITE_TAC [REAL_ABS_DIV, REAL_ABS_POW, REAL_ABS_NUM] THEN
    ASM_SIMP_TAC [← REAL_ARITH (← q r"&1 < p ==> abs p = p")] THEN
    MP_TAC (← ISPEC (← q r"p pow n * x:real") FLOOR) THEN REAL_ARITH_TAC)

  -- let PADIC_..._POS, PADIC_..._POS_LE = (CONJ_PAIR o prove) (`...`, tac)
  let (PADIC_RATIONAL_APPROXIMATION_STRADDLE_POS, PADIC_RATIONAL_APPROXIMATION_STRADDLE_POS_LE) ←
   CONJ_PAIR (← prove
   r"(!p x e. &0 < e /\ &1 < p /\ &0 < x
            ==> ?n q r. &q / p pow n < x /\ x < &r / p pow n /\
                        abs(&q / p pow n - &r / p pow n) < e) /\
   (!p x e. &0 < e /\ &1 < p /\ &0 <= x
           ==> ?n q r. &q / p pow n <= x /\ x < &r / p pow n /\
                       abs(&q / p pow n - &r / p pow n) < e)"
   (REPEAT STRIP_TAC THEN
    (SUBGOAL_THEN (← q r"&0 < p /\ &0 <= p") STRIP_ASSUME_TAC THENL
      [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
     MP_TAC (← ISPECL [← q r"p:real", ← q r"x:real", ← q r"e:real"]
       PADIC_RATIONAL_APPROXIMATION_STRADDLE) THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"n:num") THEN
     ASM_SIMP_TAC [REAL_LT_LDIV_EQ, REAL_LT_RDIV_EQ, REAL_POW_LT,
                   REAL_LE_LDIV_EQ, REAL_LE_RDIV_EQ, LEFT_IMP_EXISTS_THM] THEN
     REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
     MAP_EVERY X_GEN_TAC [← q r"q:real", ← q r"r:real"] THEN STRIP_TAC THEN
     MP_TAC (← ISPEC (← q r"r:real") integer) THEN
     MP_TAC (← ISPEC (← q r"max q (&0)") integer) THEN
     ASM_SIMP_TAC [INTEGER_CLOSED] THEN
     REWRITE_TAC [IMP_IMP, LEFT_AND_EXISTS_THM] THEN
     REWRITE_TAC [RIGHT_AND_EXISTS_THM] THEN
     MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"a:num") THEN
     MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"b:num") THEN
     REWRITE_TAC [← REAL_ARITH (← q r"abs(max q (&0)) = max q (&0)")] THEN
     SUBGOAL_THEN (← q r"&0 < r") ASSUME_TAC THENL
      [FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REAL_ARITH
        (← q r"a < r ==> &0 <= a ==> &0 < r"))) THEN
       MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN
       MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC,
       ASM_SIMP_TAC [← REAL_ARITH (← q r"&0 < r ==> abs r = r")]] THEN
     DISCH_THEN (CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
     REWRITE_TAC [← REAL_ARITH (← q r"max q (&0) = if &0 <= q then q else &0")] THEN
     COND_CASES_TAC THEN ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN
     ASM_SIMP_TAC [REAL_LE_MUL, REAL_LT_MUL, REAL_POW_LE, REAL_POW_LT] THEN
     FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REAL_ARITH
      (← q r"abs(q - r) < e ==> &0 < --q /\ z = &0 /\ &0 < r
       ==> abs(z - r) < e"))) THEN
     ASM_SIMP_TAC [REAL_LT_DIV, REAL_POW_LT] THEN
     REWRITE_TAC [real_div, REAL_MUL_LZERO, ← GSYM REAL_MUL_LNEG] THEN
     MATCH_MP_TAC REAL_LT_MUL THEN
     ASM_SIMP_TAC [REAL_LT_INV_EQ, REAL_POW_LT] THEN ASM_REAL_ARITH_TAC)))

  let RATIONAL_APPROXIMATION ← prove
   r"!x e. &0 < e ==> ?r. rational r /\ abs(r - x) < e"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"&2:real", ← q r"x:real", ← q r"e:real"]
      PADIC_RATIONAL_APPROXIMATION_STRADDLE) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC, REWRITE_TAC [LEFT_IMP_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC [← q r"n:num", ← q r"q:real", ← q r"r:real"] THEN
    STRIP_TAC THEN EXISTS_TAC (← q r"q / &2 pow n") THEN
    ASM_SIMP_TAC [RATIONAL_CLOSED] THEN ASM_REAL_ARITH_TAC)

  let RATIONAL_BETWEEN ← prove
   r"!a b. a < b ==> ?q. rational q /\ a < q /\ q < b"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"(a + b) / &2", ← q r"(b - a) / &4"] RATIONAL_APPROXIMATION) THEN
    ANTS_TAC THENL [ALL_TAC, MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC []] THEN
    ASM_REAL_ARITH_TAC)

  let RATIONAL_BETWEEN_EQ ← prove
   r"!a b. (?q. rational q /\ a < q /\ q < b) <=> a < b"
   (MESON_TAC [RATIONAL_BETWEEN, REAL_LT_TRANS])

  let RATIONAL_APPROXIMATION_STRADDLE ← prove
   r"!x e. &0 < e
         ==> ?a b. rational a /\ rational b /\
                   a < x /\ x < b /\ abs(b - a) < e"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"x - e / &4", ← q r"e / &4"] RATIONAL_APPROXIMATION) THEN
    ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC,
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC] THEN
    MP_TAC (← ISPECL [← q r"x + e / &4", ← q r"e / &4"] RATIONAL_APPROXIMATION) THEN
    ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC,
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC] THEN
    ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC)

  let RATIONAL_APPROXIMATION_ABOVE ← prove
   r"!x e. &0 < e ==> ?q. rational q /\ x < q /\ q < x + e"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"x:real", ← q r"e:real"] RATIONAL_APPROXIMATION_STRADDLE) THEN
    ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC)

  let RATIONAL_APPROXIMATION_BELOW ← prove
   r"!x e. &0 < e ==> ?q. rational q /\ x - e < q /\ q < x"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"x:real", ← q r"e:real"] RATIONAL_APPROXIMATION_STRADDLE) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC)

  let INFINITE_RATIONAL_IN_RANGE ← prove
   r"!a b. a < b ==> INFINITE {q | rational q /\ a < q /\ q < b}"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"?q. (!n. rational(q n) /\ a < q n /\ q n < b) /\ (!n. q(SUC n) < q n)")
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC DEPENDENT_CHOICE THEN
      REWRITE_TAC [← GSYM CONJ_ASSOC, ← GSYM REAL_LT_MIN] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC RATIONAL_BETWEEN THEN
      ASM_REWRITE_TAC [REAL_LT_MIN],
      MATCH_MP_TAC INFINITE_SUPERSET THEN
      EXISTS_TAC (← q r"IMAGE (q:num->real) (:num)") THEN
      CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
      MATCH_MP_TAC INFINITE_IMAGE THEN REWRITE_TAC [num_INFINITE, IN_UNIV] THEN
      SUBGOAL_THEN (← q r"!m n. m < n ==> (q:num->real) n < q m")
       (fun th => MESON_TAC [LT_CASES, th, REAL_LT_REFL]) THEN
      MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN
      ASM_MESON_TAC [REAL_LT_TRANS]])
  return { PADIC_RATIONAL_APPROXIMATION_STRADDLE, 
           PADIC_RATIONAL_APPROXIMATION_STRADDLE_POS, 
           PADIC_RATIONAL_APPROXIMATION_STRADDLE_POS_LE, RATIONAL_APPROXIMATION, 
           RATIONAL_BETWEEN, RATIONAL_BETWEEN_EQ, 
           RATIONAL_APPROXIMATION_STRADDLE, RATIONAL_APPROXIMATION_ABOVE, 
           RATIONAL_APPROXIMATION_BELOW, INFINITE_RATIONAL_IN_RANGE }

/- ------------------------------------------------------------------------- -/
/- Converting a congruence over N or Z into a real equivalent (floor.ml 814-845) -/
/- ------------------------------------------------------------------------- -/

structure Congruence where
  REAL_CONGRUENCE : thm
  REAL_INT_CONGRUENCE : thm
  deriving Inhabited

@[nospecialize]
def setupCongruence [HolBase] (D : FloorDeps) (PRealOfInt : RealOfInt) : ExceptT String IO Congruence := do
  let { INTEGER_RULE, MESON_TAC, NUMBER_RULE, REAL_FIELD, .. } := D
  let { IN, IN_IMAGE, IN_UNIV, .. } := D.core1
  let { REAL_OF_NUM_EQ, int_congruent, int_eq, int_mul_th, int_of_num_th, 
        int_sub_th, num_congruent, .. } := D.core2
  let { IMAGE_REAL_OF_INT_UNIV, .. } := PRealOfInt

  let REAL_CONGRUENCE ← prove
   r"!a b n. (a == b) (mod n) <=>
           if n = 0 then &a:real = &b
           else integer((&a - &b) / &n)"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_OF_NUM_EQ] THENL
     [CONV_TAC NUMBER_RULE, ALL_TAC] THEN
    REWRITE_TAC [← GSYM IMAGE_REAL_OF_INT_UNIV] THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM IN] THEN
    REWRITE_TAC [IN_IMAGE, IN_UNIV] THEN
    ASM_SIMP_TAC [REAL_OF_NUM_EQ, ← REAL_FIELD
     (← q r"~(n:real = &0) ==> (x / n = y <=> n * y = x)")] THEN
    REWRITE_TAC [← GSYM int_of_num_th] THEN
    REWRITE_TAC [← GSYM int_sub_th, ← GSYM int_mul_th, ← GSYM int_eq] THEN
    REWRITE_TAC [num_congruent, int_congruent] THEN MESON_TAC [])

  let REAL_INT_CONGRUENCE ← prove
   r"!a b n. (a == b) (mod n) <=>
           if n = &0 then real_of_int a = real_of_int b
           else integer((real_of_int a - real_of_int b) / real_of_int n)"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [← GSYM int_eq] THENL
     [CONV_TAC INTEGER_RULE, ALL_TAC] THEN
    REWRITE_TAC [← GSYM IMAGE_REAL_OF_INT_UNIV] THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM IN] THEN
    REWRITE_TAC [IN_IMAGE, IN_UNIV] THEN
    ASM_SIMP_TAC [← GSYM int_of_num_th, ← GSYM int_eq,  ← REAL_FIELD
     (← q r"~(n:real = &0) ==> (x / n = y <=> n * y = x)")] THEN
    REWRITE_TAC [← GSYM int_mul_th, ← GSYM int_sub_th, ← GSYM int_eq] THEN
    CONV_TAC INTEGER_RULE)
  return { REAL_CONGRUENCE, REAL_INT_CONGRUENCE }

/- ------------------------------------------------------------------------- -/
/- A simple tactic to try and prove that a real expression is integral (floor.ml 847-862) -/
/- ------------------------------------------------------------------------- -/

structure IntegerTac where
  REAL_INTEGER_TAC : tactic
  deriving Inhabited

@[nospecialize]
def setupIntegerTac [HolBase] (D : FloorDeps) (PInteger : Integer) : ExceptT String IO IntegerTac := do
  let { REAL_POLY_CONV, .. } := D
  let { INTEGER_REAL_OF_INT, .. } := D.core1
  let { INTEGER_CLOSED, .. } := PInteger

  -- field REAL_INTEGER_TAC : tactic
  -- let (REAL_INTEGER_TAC:tactic) = let base = ... and step = ... in ...
  let REAL_INTEGER_TAC ← (do
    let base := MATCH_ACCEPT_TAC (← CONJUNCT1 INTEGER_CLOSED) ORELSE
                MATCH_ACCEPT_TAC INTEGER_REAL_OF_INT
    let step :=
      MAP_FIRST MATCH_MP_TAC (CONJUNCTS (← CONJUNCT2 INTEGER_CLOSED)) THEN
      TRY CONJ_TAC
    let tac := REPEAT step THEN base
    pure (fun (asl, w) =>
     (match w with
       | .Comb (.Const "integer" _) _ =>
          (tac ORELSE
           (CONV_TAC (RAND_CONV REAL_POLY_CONV) THEN tac)) (asl, w)
       | _ => pure (.error "REAL_INTEGER_TAC: Goal not of expected form")) : tactic))
  return { REAL_INTEGER_TAC }

end HolLibrary.Floor
