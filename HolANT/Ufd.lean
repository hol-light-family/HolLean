/- ========================================================================= -/
/- ANT: Unique factorization domains                                       -/
/- ========================================================================= -/
/- File: HolANT/Ufd.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/ufd.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antufddiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.Ufd fills them).

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

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude

namespace HolANT.Ufd

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (INTEGRAL_DOMAIN_MUL_EQ_0 INTEGRAL_DOMAIN_MUL_LCANCEL INTEGRAL_DOMAIN_POW_EQ_0
   INTEGRAL_DOMAIN_PRIME_COPRIME_EQ MONO_EXISTS RING_0 RING_1
   RING_ASSOCIATES_LMUL RING_ASSOCIATES_SYM RING_COPRIME_0
   RING_COPRIME_DIVPROD_RIGHT RING_COPRIME_LMUL RING_COPRIME_RPOW
   RING_COPRIME_SYM RING_DIVIDES_REFL RING_DIVIDES_RMUL RING_MUL RING_MUL_ASSOC
   RING_MUL_LID RING_MUL_POW RING_MUL_RID RING_MUL_SYM RING_POW RING_POW_ONE
   RING_POW_ZERO RING_PRIME_DIVIDES_MUL RING_UNIT_1 RING_UNIT_IN_CARRIER
   RING_UNIT_MUL_EQ RING_UNIT_POW UFD_IMP_INTEGRAL_DOMAIN
   UFD_PRIME_FACTOR_INDUCT ring_coprime ring_divides ring_pow ring_prime
   ring_unit : thm)
  deriving Inhabited

/-- What ufd.ml uses from Session besides theorems. -/
structure UfdDeps where
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
/- ufd.ml phrases from line 17 to 133                                     -/
/- ---------------------------------------------------------------------- -/

structure Ufd where
  -- @@FIELDS
  UFD_COPRIME_MUL_POW : thm
  UFD_COPRIME_MUL_POW_ASSOCIATES : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupUfd [HolBase] (D : UfdDeps) :
    ExceptT String IO Ufd := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, INDUCT_TAC, RING_RULE, .. } := D
  let { INTEGRAL_DOMAIN_MUL_EQ_0, INTEGRAL_DOMAIN_MUL_LCANCEL,
        INTEGRAL_DOMAIN_POW_EQ_0, INTEGRAL_DOMAIN_PRIME_COPRIME_EQ, MONO_EXISTS,
        RING_0, RING_1, RING_ASSOCIATES_LMUL, RING_ASSOCIATES_SYM, RING_COPRIME_0,
        RING_COPRIME_DIVPROD_RIGHT, RING_COPRIME_LMUL, RING_COPRIME_RPOW,
        RING_COPRIME_SYM, RING_DIVIDES_REFL, RING_DIVIDES_RMUL, RING_MUL,
        RING_MUL_ASSOC, RING_MUL_LID, RING_MUL_POW, RING_MUL_RID, RING_MUL_SYM,
        RING_POW, RING_POW_ONE, RING_POW_ZERO, RING_PRIME_DIVIDES_MUL, RING_UNIT_1,
        RING_UNIT_IN_CARRIER, RING_UNIT_MUL_EQ, RING_UNIT_POW, UFD_IMP_INTEGRAL_DOMAIN,
        UFD_PRIME_FACTOR_INDUCT, ring_coprime, ring_divides, ring_pow, ring_prime,
        ring_unit, .. } := D.core1
  -- @@SCOPE END

  let UFD_COPRIME_MUL_POW ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"ring_pow r p k:A"
    let q2 ← q r"r:A ring"
    let q3 ← q r"ring_coprime r (ring_mul r (ring_pow r p k) v1,w:A)"
    let q4 ← q r"v1:A"
    let q5 ← q r"v1:A"
    let q6 ← q r"w:A"
    let q7 ← q r"ring_divides r (ring_pow r p k) (v:A)"
    let q8 ← q r"ring_coprime r (w:A,ring_pow r p k)"
    let q9 ← q r"(p:A) IN ring_carrier r /\ ~(p = ring_0 r) /\ ~ring_unit r p"
    let p10 ← prove r"!r p d v w:A k.
        UFD r /\ ring_prime r p /\ d IN ring_carrier r /\ ~(k = 0) /\
        v IN ring_carrier r /\ w IN ring_carrier r /\
        ring_coprime r (v,w) /\ ring_divides r p v /\
        ring_mul r v w = ring_mul r (ring_pow r p k) (ring_pow r d k)
        ==> ?v1. v1 IN ring_carrier r /\
                 v = ring_mul r (ring_pow r p k) v1 /\
                 ring_mul r v1 w = ring_pow r d k /\
                 ring_coprime r (v1,w)" (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP UFD_IMP_INTEGRAL_DOMAIN)) THEN SUBGOAL_THEN q9 STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [ring_prime], ALL_TAC] THEN SUBGOAL_THEN q8 ASSUME_TAC THENL [MATCH_MP_TAC RING_COPRIME_RPOW THEN ONCE_REWRITE_TAC [RING_COPRIME_SYM] THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_PRIME_COPRIME_EQ] THEN ASM_MESON_TAC [ring_coprime], ALL_TAC] THEN SUBGOAL_THEN q7 MP_TAC THENL [MATCH_MP_TAC RING_COPRIME_DIVPROD_RIGHT THEN EXISTS_TAC q6 THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC RING_DIVIDES_RMUL THEN ASM_SIMP_TAC [RING_DIVIDES_REFL, RING_POW], REWRITE_TAC [ring_divides] THEN DISCH_THEN ((X_CHOOSE_THEN q5 (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) o (CONJUNCT2 o CONJUNCT2))] THEN EXISTS_TAC q4 THEN UNDISCH_TAC q3 THEN ASM_SIMP_TAC [RING_COPRIME_LMUL, RING_POW] THEN DISCH_TAC THEN MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN MAP_EVERY EXISTS_TAC [q2, q1] THEN ASM_SIMP_TAC [RING_POW, RING_MUL, INTEGRAL_DOMAIN_POW_EQ_0, RING_MUL_ASSOC])
    let lemma := p10
    let q11 ← q r"y1:A"
    let q12 ← q r"y1:A"
    let q13 ← q r"k:num"
    let q14 ← q r"x:A"
    let q15 ← q r"y:A"
    let q16 ← q r"d:A"
    let q17 ← q r"p:A"
    let q18 ← q r"r:A ring"
    let v19 ← ISPECL [q18, q17, q16, q15, q14, q13] lemma
    let q20 ← q r"ring_mul r y x = ring_mul r x (y:A)"
    let q21 ← q r"ring_mul r z (ring_mul r u t) = ring_mul r u (ring_mul r z (t:A))"
    let r22 ← RING_RULE q21
    let q23 ← q r"ring_mul r p e:A"
    let q24 ← q r"e:A"
    let q25 ← q r"u:A"
    let q26 ← q r"y:A"
    let q27 ← q r"x1:A"
    let q28 ← q r"x1:A"
    let q29 ← q r"k:num"
    let q30 ← q r"y:A"
    let q31 ← q r"x:A"
    let q32 ← q r"d:A"
    let q33 ← q r"p:A"
    let q34 ← q r"r:A ring"
    let v35 ← ISPECL [q34, q33, q32, q31, q30, q29] lemma
    let q36 ← q r"k:num"
    let q37 ← q r"k:num"
    let q38 ← q r"~(k = 0)"
    let v39 ← GSYM RING_PRIME_DIVIDES_MUL
    let q40 ← q r"ring_divides r p (x:A) \/ ring_divides r p y"
    let q41 ← q r"y:A"
    let q42 ← q r"x:A"
    let q43 ← q r"(p:A) IN ring_carrier r /\ ~(p = ring_0 r) /\ ~ring_unit r p"
    let q44 ← q r"d:A"
    let q45 ← q r"p:A"
    let q46 ← q r"y:A"
    let q47 ← q r"x:A"
    let q48 ← q r"r:A ring"
    let v49 ← ISPECL [q48, q47, q46] RING_UNIT_MUL_EQ
    let q50 ← q r"y:A"
    let q51 ← q r"x:A"
    let q52 ← q r"w:A"
    let q53 ← q r"ring_0 r:A"
    let q54 ← q r"ring_1 r:A"
    let q55 ← q r"x:A = ring_0 r \/ y = ring_0 r"
    let q56 ← q r"y:A"
    let q57 ← q r"x:A"
    let q58 ← q r"!d:A. d IN ring_carrier r
            ==> !x y. x IN ring_carrier r /\ y IN ring_carrier r /\
                      ring_coprime r (x,y) /\ ring_mul r x y = ring_pow r d k
                      ==> ?u e. ring_unit r u /\ e IN ring_carrier r /\
                                x = ring_mul r u (ring_pow r e k)"
    let q59 ← q r"ring_1 r:A"
    let q60 ← q r"x:A"
    let q61 ← q r"!x:A. ring_unit r x
            ==> ?u e. ring_unit r u /\ e IN ring_carrier r /\
                      x = ring_mul r u (ring_pow r e k)"
    let q62 ← q r"ring_1 r:A"
    let q63 ← q r"a:A"
    let q64 ← q r"k = 0"
    prove
      r"!r a b c:A k.
            UFD r /\ a IN ring_carrier r /\ b IN ring_carrier r /\
            c IN ring_carrier r /\ ring_coprime r (a,b) /\
            ring_mul r a b = ring_pow r c k
            ==> ?u e. ring_unit r u /\ e IN ring_carrier r /\
                      a = ring_mul r u (ring_pow r e k)"
      (REPEAT GEN_TAC THEN ASM_CASES_TAC q64 THENL [ASM_REWRITE_TAC [ring_pow] THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC [q63, q62] THEN ASM_SIMP_TAC [RING_1, RING_MUL_RID] THEN REWRITE_TAC [ring_unit] THEN ASM_MESON_TAC [], STRIP_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP UFD_IMP_INTEGRAL_DOMAIN)) THEN SUBGOAL_THEN q61 (LABEL_TAC "unit") THENL [REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [q60, q59] THEN ASM_SIMP_TAC [RING_POW_ONE, RING_1, RING_MUL_RID, RING_UNIT_IN_CARRIER], ALL_TAC] THEN SUBGOAL_THEN q58 (fun th => ASM_MESON_TAC [th]) THEN MATCH_MP_TAC UFD_PRIME_FACTOR_INDUCT THEN ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL [ASM_REWRITE_TAC [RING_POW_ZERO] THEN MAP_EVERY X_GEN_TAC [q57, q56] THEN STRIP_TAC THEN SUBGOAL_THEN q55 STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [INTEGRAL_DOMAIN_MUL_EQ_0], MAP_EVERY EXISTS_TAC [q54, q53] THEN ASM_SIMP_TAC [RING_UNIT_1, RING_0, RING_POW_ZERO, RING_MUL_LID], REMOVE_THEN "unit" MATCH_MP_TAC THEN ASM_MESON_TAC [RING_COPRIME_0]], X_GEN_TAC q52 THEN DISCH_TAC THEN MAP_EVERY X_GEN_TAC [q51, q50] THEN STRIP_TAC THEN REMOVE_THEN "unit" MATCH_MP_TAC THEN MP_TAC v49 THEN ASM_SIMP_TAC [RING_UNIT_POW], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [q45, q44] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ih"))) THEN SUBGOAL_THEN q43 STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [ring_prime], ALL_TAC] THEN ASM_SIMP_TAC [RING_MUL_POW] THEN MAP_EVERY X_GEN_TAC [q42, q41] THEN STRIP_TAC THEN SUBGOAL_THEN q40 STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [v39] THEN MATCH_MP_TAC RING_DIVIDES_RMUL THEN ASM_SIMP_TAC [RING_POW] THEN UNDISCH_TAC q38 THEN SPEC_TAC (q37, q36) THEN INDUCT_TAC THEN REWRITE_TAC [ring_pow] THEN ASM_SIMP_TAC [RING_DIVIDES_RMUL, RING_DIVIDES_REFL, RING_POW], MP_TAC v35 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN q28 STRIP_ASSUME_TAC) THEN REMOVE_THEN "ih" (MP_TAC o (SPECL [q27, q26])) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC q25 THEN DISCH_THEN (X_CHOOSE_THEN q24 STRIP_ASSUME_TAC) THEN EXISTS_TAC q23 THEN ASM_SIMP_TAC [RING_MUL, RING_MUL_POW] THEN MATCH_MP_TAC r22 THEN ASM_SIMP_TAC [RING_POW, RING_UNIT_IN_CARRIER], SUBGOAL_THEN q20 ASSUME_TAC THENL [ASM_MESON_TAC [RING_MUL_SYM], ALL_TAC] THEN MP_TAC v19 THEN ANTS_TAC THENL [ONCE_REWRITE_TAC [RING_COPRIME_SYM] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN q12 STRIP_ASSUME_TAC) THEN REMOVE_THEN "ih" MATCH_MP_TAC THEN EXISTS_TAC q11 THEN ONCE_REWRITE_TAC [RING_COPRIME_SYM] THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [RING_MUL_SYM]])

  let UFD_COPRIME_MUL_POW_ASSOCIATES ← prove
    r"!r a b c:A k.
        UFD r /\ a IN ring_carrier r /\ b IN ring_carrier r /\
        c IN ring_carrier r /\ ring_coprime r (a,b) /\
        ring_mul r a b = ring_pow r c k
        ==> ?e. e IN ring_carrier r /\ ring_associates r a (ring_pow r e k)"
    (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o (MATCH_MP UFD_COPRIME_MUL_POW)) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"u:A") (X_CHOOSE_THEN (← q r"e:A") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)))) THEN EXISTS_TAC (← q r"e:A") THEN ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [RING_ASSOCIATES_SYM] THEN MATCH_MP_TAC RING_ASSOCIATES_LMUL THEN ASM_SIMP_TAC [RING_POW])

  -- @@RETURN BEGIN
  return { UFD_COPRIME_MUL_POW, UFD_COPRIME_MUL_POW_ASSOCIATES }
  -- @@RETURN END

end HolANT.Ufd
