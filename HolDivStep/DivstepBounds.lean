/- ========================================================================= -/
/- Termination bounds for the Bernstein-Yang divstep iteration.            -/
/- ========================================================================= -/
/- File: HolDivStep/DivstepBounds.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Divstep/divstep_bounds.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/iter.ml, Library/integer.ml, Library/floor.ml, Divstep/divstep.ml, Divstep/idivstep.ml, Divstep/hull_light.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionDivStep.DivstepBounds fills them).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, INT_ARITH, TAUT, SET_RULE, ...) they are
  bound first, in OCaml's order.
-/

import HolLibrary.Iter
import HolLibrary.Integer
import HolLibrary.Floor
import HolDivStep.Divstep
import HolDivStep.IDivstep
import HolDivStep.HullLight

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolDivStep.DivstepBounds

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD1 COND_SWAP CONJ_ASSOC DIVSTEP_FG_GCD FORALL_PAIR_THM IMP_IMP
   INTEGER_CLOSED INTEGER_REAL_OF_INT INT_2_DIVIDES_ADD INT_2_DIVIDES_SUB
   INT_ADD_RID INT_GCD_0 INT_MUL_DIV_EQ INT_MUL_LID INT_MUL_LZERO INT_OF_NUM_LT
   INT_REM_2_CASES INT_REM_2_DIVIDES ITER ITER_DIVSTEP_BOUND_ALT
   ITER_DIVSTEP_INTEGER ITER_DIVSTEP_ODD PAIR REAL_LT_INTEGERS
   REAL_OF_INT_CLAUSES REAL_OF_INT_OF_REAL REAL_SUB_0 REAL_SUB_REFL divstep
   divsteps_s endtoend_bits_simple int_eq int_of_num_th : thm)
  deriving Inhabited

/-- What divstep_bounds.ml uses from Session besides theorems. -/
structure DivstepBoundsDeps where
  new_definition : String → ExceptT String IO thm
  define : String → ExceptT String IO thm
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_ARITH_TAC : tactic
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  ASM_MESON_TAC : List thm → tactic
  METIS_TAC : List thm → tactic
  ASM_METIS_TAC : List thm → tactic
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  TAUT : term → ExceptT String IO thm
  ITAUT : term → ExceptT String IO thm
  REAL_ARITH : term → ExceptT String IO thm
  REAL_FIELD : term → ExceptT String IO thm
  REAL_ARITH_TAC : tactic
  ASM_REAL_ARITH_TAC : tactic
  INDUCT_TAC : tactic
  INT_ARITH : term → ExceptT String IO thm
  INT_ARITH_TAC : tactic
  ASM_INT_ARITH_TAC : tactic
  INTEGER_RULE : term → ExceptT String IO thm  -- ints.ml's INTEGER_RULE
  INTEGER_TAC : tactic
  NUMBER_RULE : ioconv  -- ints.ml's NUMBER_RULE
  NUM_REDUCE_CONV : ioconv
  INT_REDUCE_CONV : ioconv
  INT_RED_CONV : ioconv
  INT_REM_DOWN_CONV : ioconv
  HAS_SIZE_CONV : ioconv  -- card.ml's HAS_SIZE_CONV
  let_CONV : ioconv
  num_CONV : ioconv
  mk_numeral : Rat → Except String term
  LET_TAC : tactic
  basic_ss : List thm → IO (Except String HolCore.Simp.simpset)
  NUM_SUB_CONV : ioconv
  REAL_RAT_REDUCE_CONV : ioconv
  NUM_EQ_CONV : ioconv
  NUM_DIV_CONV : ioconv
  EXP_MOD_CONV : ioconv
  EXPAND_CASES_CONV : ioconv
  core1 : CoreThms1

/-- RingTheory's `wPart` (copied verbatim).  `W(MP_TAC o PART_MATCH f th o g
    o snd)`: match `th`'s part `f` against the part `g` of the goal, and
    MP_TAC the instance. -/
def wPart [HolBase] (g : term → Except String term) (f : term → Except String term)
    (th : thm) : tactic := fun gl =>
  ExceptT.run do
    let t ← liftExcept (g gl.2)
    ExceptT.mk (MP_TAC (← PART_MATCH f th t) gl)

/-- tactics.ml's NO_TAC. -/
def NO_TAC : tactic := HolCore.Tactics.NO_TAC



/- ------------------------------------------------------------------------- -/
/- Termination bounds for the Bernstein-Yang "divstep" iteration: lemmas     -/
/- about starting divstep with d = 1/2, the bounds theorem instantiated and  -/
/- tweaked, and the overall result for the integer-scaled version starting   -/
/- at 1.  (divstep_bounds.ml 1-94)                                           -/
/- ------------------------------------------------------------------------- -/

structure DivstepBoundsThms where
  -- @@FIELDS
  INTEGER_DIVSTEP_DELTA : thm
  ITER_DIVSTEP_ODD_ALT : thm
  DIVSTEP_ENDTOEND_BITS_SIMPLE : thm
  IDIVSTEP_ENDTOEND_BITS_SIMPLE : thm
  deriving Inhabited

@[nospecialize]
def setupDivstepBoundsThms [HolBase] (D : DivstepBoundsDeps) :
    ExceptT String IO DivstepBoundsThms := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, INDUCT_TAC, INT_REDUCE_CONV, MESON_TAC, REAL_ARITH,
        REAL_ARITH_TAC, REAL_RAT_REDUCE_CONV, TAUT, .. } := D
  let { ADD1, COND_SWAP, CONJ_ASSOC, DIVSTEP_FG_GCD, FORALL_PAIR_THM, IMP_IMP,
        INTEGER_CLOSED, INTEGER_REAL_OF_INT, INT_2_DIVIDES_ADD, INT_2_DIVIDES_SUB,
        INT_ADD_RID, INT_GCD_0, INT_MUL_DIV_EQ, INT_MUL_LID, INT_MUL_LZERO,
        INT_OF_NUM_LT, INT_REM_2_CASES, INT_REM_2_DIVIDES, ITER,
        ITER_DIVSTEP_BOUND_ALT, ITER_DIVSTEP_INTEGER, ITER_DIVSTEP_ODD, PAIR,
        REAL_LT_INTEGERS, REAL_OF_INT_CLAUSES, REAL_OF_INT_OF_REAL, REAL_SUB_0,
        REAL_SUB_REFL, divstep, divsteps_s, endtoend_bits_simple, int_eq,
        int_of_num_th, .. } := D.core1
  -- @@SCOPE END

  /- A couple of trivial lemmas about starting divstep with d = 1/2. -/

  let INTEGER_DIVSTEP_DELTA ← prove
   r"!f g n. integer(FST(ITER n divstep (&1 / &2,f,g)) - &1 / &2)"
   (← do
    -- right to left: the second REAL_ARITH, then the first
    let r2 ← REAL_ARITH (← q r"(&1 + x) - &1 / &2 = &1 + (x - &1 / &2)")
    let r1 ← REAL_ARITH (← q r"&1 - x - &1 / &2 = --(x - &1 / &2)")
    pure (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [ITER, REAL_SUB_REFL, INTEGER_CLOSED] THEN
    POP_ASSUM MP_TAC THEN
    SPEC_TAC (← q r"ITER n divstep (&1 / &2,f,g)", ← q r"t:real#int#int") THEN
    REWRITE_TAC [divstep, FORALL_PAIR_THM] THEN
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [r1] THEN
    REWRITE_TAC [r2] THEN
    MESON_TAC [INTEGER_CLOSED]))

  let ITER_DIVSTEP_ODD_ALT ← prove
   r"!f g n.
        f rem &2 = &1
        ==> FST(SND(ITER n divstep (&1 / &2,f,g))) rem &2 = &1"
   (← do
    pure (REPEAT STRIP_TAC THEN MATCH_MP_TAC ITER_DIVSTEP_ODD THEN
    ASM_MESON_TAC [PAIR]))

  /- Instantiate and tweak the bounds theorem. -/

  let DIVSTEP_ENDTOEND_BITS_SIMPLE ← prove
   r"!f g b n.
        &0 <= g /\ g <= f /\ f <= &2 pow b /\ f rem &2 = &1 /\
        9437 * b + 1 <= 4096 * n
        ==> SND(SND(ITER n divstep (&1 / &2,f,g))) = &0"
   (← do
    let r1 ← REAL_ARITH (← q r"x = y / &2 <=> &2 * x = y")
    pure (REWRITE_TAC [← GSYM divsteps_s] THEN REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC I [← GSYM ITER_DIVSTEP_BOUND_ALT] THEN
    MP_TAC (← ISPECL
     [← q r"\n. int_of_real(FST (ITER n divstep (&1 / &2,f,g)) - &1 / &2)",
      ← q r"\n. real_of_int(FST (SND(ITER n divstep (&1 / &2,f,g))))",
      ← q r"\n. real_of_int(SND (SND(ITER n divstep (&1 / &2,f,g))))",
      ← q r"b:num", ← q r"n:num"]
     endtoend_bits_simple) THEN
    REWRITE_TAC [← GSYM REAL_OF_INT_CLAUSES, IMP_IMP, ← GSYM CONJ_ASSOC] THEN
    SIMP_TAC [REAL_OF_INT_OF_REAL, INTEGER_DIVSTEP_DELTA] THEN
    REWRITE_TAC [INTEGER_REAL_OF_INT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [ITER, REAL_SUB_0] THEN REWRITE_TAC [REAL_OF_INT_CLAUSES] THEN
    REWRITE_TAC [int_of_num_th, ← GSYM int_eq] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC [INT_OF_NUM_LT] THEN
    X_GEN_TAC (← q r"m:num") THEN REWRITE_TAC [ITER, ← GSYM ADD1] THEN
    MP_TAC (← SPECL [← q r"f:int", ← q r"g:int", ← q r"m:num"] INTEGER_DIVSTEP_DELTA) THEN
    MP_TAC (← SPECL [← q r"f:int", ← q r"g:int", ← q r"m:num"] ITER_DIVSTEP_ODD_ALT) THEN
    SPEC_TAC (← q r"ITER m divstep (&1 / &2,f,g)", ← q r"t:real#int#int") THEN
    ASM_REWRITE_TAC [divstep, FORALL_PAIR_THM] THEN POP_ASSUM_LIST (fun _ => ALL_TAC) THEN
    MAP_EVERY X_GEN_TAC [← q r"delta:real", ← q r"f:int", ← q r"g:int"] THEN
    DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"delta - &1 / &2 < &0 <=> ~(delta > &0)") SUBST1_TAC THENL
     [EQ_TAC THENL [ASM_SIMP_TAC [REAL_LT_INTEGERS, INTEGER_CLOSED], ALL_TAC] THEN
      REAL_ARITH_TAC,
      ALL_TAC] THEN
    DISJ_CASES_TAC (← SPEC (← q r"g:int") INT_REM_2_CASES) THEN
    ASM_REWRITE_TAC [] THEN CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC [COND_SWAP] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [INT_MUL_LID, INT_MUL_LZERO, INT_ADD_RID] THENL
     [DISJ1_TAC, DISJ1_TAC, DISJ2_TAC, DISJ2_TAC] THEN
    (CONJ_TAC THENL [REAL_ARITH_TAC, ALL_TAC]) THEN
    REWRITE_TAC [r1] THEN
    REWRITE_TAC [REAL_OF_INT_CLAUSES] THEN
    REWRITE_TAC [INT_MUL_DIV_EQ, INT_2_DIVIDES_ADD, INT_2_DIVIDES_SUB] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [INT_REM_2_DIVIDES]) THEN
    ASM_REWRITE_TAC []))

  /- Overall result for the integer-scaled version starting at 1. -/

  let IDIVSTEP_ENDTOEND_BITS_SIMPLE ← prove
   r"!f g b n.
        &0 <= g /\ g <= f /\ f <= &2 pow b /\ f rem &2 = &1 /\
        9437 * b + 1 <= 4096 * n
        ==> divstep_g n (&1,f,g) = &0 /\
            abs(divstep_f n (&1,f,g)) = gcd(f,g)"
   (← do
    let t1 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    pure (REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC t1 THEN CONJ_TAC THENL
     [FIRST_ASSUM (MP_TAC o MATCH_MP DIVSTEP_ENDTOEND_BITS_SIMPLE) THEN
      REWRITE_TAC [ITER_DIVSTEP_INTEGER],
      ASM_MESON_TAC [DIVSTEP_FG_GCD, INT_GCD_0]]))

  -- @@RETURN BEGIN
  return { INTEGER_DIVSTEP_DELTA, ITER_DIVSTEP_ODD_ALT, DIVSTEP_ENDTOEND_BITS_SIMPLE,
           IDIVSTEP_ENDTOEND_BITS_SIMPLE }
  -- @@RETURN END

end HolDivStep.DivstepBounds
