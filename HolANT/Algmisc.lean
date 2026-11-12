/- ========================================================================= -/
/- ANT: Generic lemmas used by the algebraic number theory files ...       -/
/- ========================================================================= -/
/- File: HolANT/Algmisc.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/algmisc.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antalgmiscdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/products.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.Algmisc fills them).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left; where a proof applies rules that print or use
  counters (MESON, ARITH_RULE, ...) they are bound first, in OCaml's order.
-/

import HolANT.Prelude
import HolLibrary.Binomial
import HolLibrary.Iter
import HolLibrary.Prime
import HolLibrary.Pocklington
import HolLibrary.Wo
import HolLibrary.Card
import HolLibrary.RingTheory
import HolLibrary.Products

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude

namespace HolANT.Algmisc

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (EXP_1 EXP_ZERO EXTENSION FINITE_INDUCT_STRONG FORALL_IN_INSERT
   HAS_SIZE_IMAGE_INJ HAS_SIZE_NUMSEG_LT INT_ABS_POS INT_DIVIDES_ABS
   INT_OF_NUM_EQ INT_OF_NUM_LT INT_OF_NUM_OF_INT INT_OF_NUM_POW INT_POS
   INT_POW_LE IN_ELIM_THM IN_IMAGE LE_0 LE_EXP MONO_EXISTS NOT_IN_EMPTY num_MAX
   num_divides : thm)
  deriving Inhabited

/-- What algmisc.ml uses from Session besides theorems. -/
structure AlgmiscDeps where
  new_definition : String → ExceptT String IO thm
  define : String → ExceptT String IO thm
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  new_recursive_definition : thm → String → ExceptT String IO thm
  LIST_INDUCT_TAC : tactic
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
  PRIME_CONV : term → ExceptT String IO thm  -- pocklington.ml's PRIME_CONV
  PRIME_RULE : List String → term → ExceptT String IO thm  -- pocklington.ml's PRIME_RULE
  RING_RULE : term → ExceptT String IO thm  -- ringtheory.ml's RING_RULE
  INTEGRAL_DOMAIN_RULE : term → ExceptT String IO thm
  FIELD_TAC : tactic  -- ringtheory.ml's FIELD_TAC
  RING_CARRIER_TAC : tactic
  RING_TAC : tactic
  RING_PULL_DIV_TAC : tactic
  LET_TAC : tactic
  basic_ss : List thm → IO (Except String HolCore.Simp.simpset)
  INTEGER_MOD_RING_RED_CONV : ioconv
  NUM_SUB_CONV : ioconv
  REAL_RAT_REDUCE_CONV : ioconv
  NUM_EQ_CONV : ioconv
  NUM_DIV_CONV : ioconv
  EXP_MOD_CONV : ioconv
  EXPAND_CASES_CONV : ioconv
  DIVIDES_CONV : ioconv  -- prime.ml's DIVIDES_CONV
  COPRIME_CONV : ioconv
  core1 : CoreThms1

/-- RingTheory's `wPart` (copied verbatim).  `W(MP_TAC o PART_MATCH f th o g
    o snd)`: match `th`'s part `f` against the part `g` of the goal, and
    MP_TAC the instance. -/
def wPart [HolBase] (g : term → Except String term) (f : term → Except String term)
    (th : thm) : tactic := fun gl =>
  ExceptT.run do
    let t ← liftExcept (g gl.2)
    ExceptT.mk (MP_TAC (← PART_MATCH f th t) gl)



/- ---------------------------------------------------------------------- -/
/- algmisc.ml phrases from line 31 to 91                                  -/
/- ---------------------------------------------------------------------- -/

structure Algmisc where
  -- @@FIELDS
  UPPER_BOUND_FINITE_SET_INT : thm
  HAS_SIZE_INT_SEG_LT : thm
  NUM_ROOT_FLOOR : thm
  INT_DIVIDES_NUM_OF_INT_ABS : thm
  NUM_OF_INT_ABS_POW : thm
  FORALL_LT_2 : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupAlgmisc [HolBase] (D : AlgmiscDeps) :
    ExceptT String IO Algmisc := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, INT_ARITH_TAC, MESON_TAC, TAUT, .. } := D
  let { EXP_1, EXP_ZERO, EXTENSION, FINITE_INDUCT_STRONG, FORALL_IN_INSERT,
        HAS_SIZE_IMAGE_INJ, HAS_SIZE_NUMSEG_LT, INT_ABS_POS, INT_DIVIDES_ABS,
        INT_OF_NUM_EQ, INT_OF_NUM_LT, INT_OF_NUM_OF_INT, INT_OF_NUM_POW, INT_POS,
        INT_POW_LE, IN_ELIM_THM, IN_IMAGE, LE_0, LE_EXP, MONO_EXISTS, NOT_IN_EMPTY,
        num_MAX, num_divides, .. } := D.core1
  -- @@SCOPE END

  let UPPER_BOUND_FINITE_SET_INT ← prove
    r"!f:A->int s. FINITE s ==> ?a. !x. x IN s ==> f x <= a"
    (GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC [NOT_IN_EMPTY, FORALL_IN_INSERT] THEN MAP_EVERY X_GEN_TAC [(← q r"b:A"), (← q r"t:A->bool")] THEN DISCH_THEN ((X_CHOOSE_TAC (← q r"a:int")) o CONJUNCT1) THEN EXISTS_TAC (← q r"max ((f:A->int) b) a") THEN CONJ_TAC THENL [INT_ARITH_TAC, X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"x:A"))) THEN ASM_REWRITE_TAC [] THEN INT_ARITH_TAC])

  let HAS_SIZE_INT_SEG_LT ← prove
    r"!n. {k:int | &0 <= k /\ k < &n} HAS_SIZE n"
    (GEN_TAC THEN SUBGOAL_THEN (← q r"{k:int | &0 <= k /\ k < &n} = IMAGE int_of_num {m | m < n}") SUBST1_TAC THENL [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN X_GEN_TAC (← q r"k:int") THEN EQ_TAC THENL [STRIP_TAC THEN EXISTS_TAC (← q r"num_of_int k") THEN ASM_SIMP_TAC [INT_OF_NUM_OF_INT, (← GSYM INT_OF_NUM_LT)], STRIP_TAC THEN ASM_REWRITE_TAC [INT_POS, INT_OF_NUM_LT]], MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN REWRITE_TAC [HAS_SIZE_NUMSEG_LT, INT_OF_NUM_EQ] THEN MESON_TAC []])

  let NUM_ROOT_FLOOR ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"t:num <= u ==> u <= N ==> t <= N")
    let r2 ← TAUT (← q r"p /\ (q ==> r) ==> (p <=> q) ==> r")
    prove
      r"!n N. ~(n = 0) ==> ?t. t EXP n <= N /\ N < (t + 1) EXP n"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"\t. t EXP n <= N") num_MAX) THEN REWRITE_TAC [] THEN MATCH_MP_TAC r2 THEN CONJ_TAC THENL [CONJ_TAC THENL [EXISTS_TAC (← q r"0") THEN ASM_REWRITE_TAC [EXP_ZERO, LE_0], EXISTS_TAC (← q r"N:num") THEN X_GEN_TAC (← q r"t:num") THEN MATCH_MP_TAC r1 THEN MP_TAC (← SPECL [(← q r"t:num"), (← q r"1"), (← q r"n:num")] LE_EXP) THEN REWRITE_TAC [EXP_1] THEN DISCH_THEN SUBST1_TAC THEN COND_CASES_TAC THEN ASM_ARITH_TAC], MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"t:num") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o (SPEC (← q r"t + 1")))) THEN ASM_REWRITE_TAC [] THEN ARITH_TAC])

  let INT_DIVIDES_NUM_OF_INT_ABS ← prove
    r"!d n:int. d divides n <=> num_of_int(abs d) divides num_of_int(abs n)"
    (SIMP_TAC [num_divides, INT_OF_NUM_OF_INT, INT_ABS_POS, INT_DIVIDES_ABS])

  let NUM_OF_INT_ABS_POW ← prove
    r"!x:int n. num_of_int(abs x pow n) = num_of_int(abs x) EXP n"
    (SIMP_TAC [(← GSYM INT_OF_NUM_EQ), INT_OF_NUM_OF_INT, INT_ABS_POS, INT_POW_LE, (← GSYM INT_OF_NUM_POW)])

  let FORALL_LT_2 ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"0 < 2 /\ 1 < 2")
    let r2 ← ARITH_RULE (← q r"i < 2 <=> i = 0 \/ i = 1")
    prove
      r"!P. (!i. i < 2 ==> P i) <=> P 0 /\ P 1"
      (MESON_TAC [r2, r1])

  -- @@RETURN BEGIN
  return { UPPER_BOUND_FINITE_SET_INT, HAS_SIZE_INT_SEG_LT, NUM_ROOT_FLOOR,
           INT_DIVIDES_NUM_OF_INT_ABS, NUM_OF_INT_ABS_POW, FORALL_LT_2 }
  -- @@RETURN END

end HolANT.Algmisc
