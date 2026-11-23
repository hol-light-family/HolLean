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
  literals right to left.  The `do` macro of HolCore/OcamlOrder.lean
  (HolLight.Syntax) binds each statement's `(← ...)` actions in that order,
  so quotations and rules (MESON, ARITH_RULE, ...) run as in HOL Light;
  where a rule is bound by a `let` before the proof, it is bound in OCaml's
  order.
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
    let lemma := (← prove r"!r p d v w:A k.
        UFD r /\ ring_prime r p /\ d IN ring_carrier r /\ ~(k = 0) /\
        v IN ring_carrier r /\ w IN ring_carrier r /\
        ring_coprime r (v,w) /\ ring_divides r p v /\
        ring_mul r v w = ring_mul r (ring_pow r p k) (ring_pow r d k)
        ==> ?v1. v1 IN ring_carrier r /\
                 v = ring_mul r (ring_pow r p k) v1 /\
                 ring_mul r v1 w = ring_pow r d k /\
                 ring_coprime r (v1,w)" (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP UFD_IMP_INTEGRAL_DOMAIN)) THEN SUBGOAL_THEN (← q r"(p:A) IN ring_carrier r /\ ~(p = ring_0 r) /\ ~ring_unit r p") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [ring_prime], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_coprime r (w:A,ring_pow r p k)") ASSUME_TAC THENL [MATCH_MP_TAC RING_COPRIME_RPOW THEN ONCE_REWRITE_TAC [RING_COPRIME_SYM] THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_PRIME_COPRIME_EQ] THEN ASM_MESON_TAC [ring_coprime], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_divides r (ring_pow r p k) (v:A)") MP_TAC THENL [MATCH_MP_TAC RING_COPRIME_DIVPROD_RIGHT THEN EXISTS_TAC (← q r"w:A") THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC RING_DIVIDES_RMUL THEN ASM_SIMP_TAC [RING_DIVIDES_REFL, RING_POW], REWRITE_TAC [ring_divides] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"v1:A") (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) o (CONJUNCT2 o CONJUNCT2))] THEN EXISTS_TAC (← q r"v1:A") THEN UNDISCH_TAC (← q r"ring_coprime r (ring_mul r (ring_pow r p k) v1,w:A)") THEN ASM_SIMP_TAC [RING_COPRIME_LMUL, RING_POW] THEN DISCH_TAC THEN MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN MAP_EVERY EXISTS_TAC [(← q r"r:A ring"), (← q r"ring_pow r p k:A")] THEN ASM_SIMP_TAC [RING_POW, RING_MUL, INTEGRAL_DOMAIN_POW_EQ_0, RING_MUL_ASSOC]))
    prove
      r"!r a b c:A k.
            UFD r /\ a IN ring_carrier r /\ b IN ring_carrier r /\
            c IN ring_carrier r /\ ring_coprime r (a,b) /\
            ring_mul r a b = ring_pow r c k
            ==> ?u e. ring_unit r u /\ e IN ring_carrier r /\
                      a = ring_mul r u (ring_pow r e k)"
      (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"k = 0") THENL [ASM_REWRITE_TAC [ring_pow] THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"a:A"), (← q r"ring_1 r:A")] THEN ASM_SIMP_TAC [RING_1, RING_MUL_RID] THEN REWRITE_TAC [ring_unit] THEN ASM_MESON_TAC [], STRIP_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP UFD_IMP_INTEGRAL_DOMAIN)) THEN SUBGOAL_THEN (← q r"!x:A. ring_unit r x
            ==> ?u e. ring_unit r u /\ e IN ring_carrier r /\
                      x = ring_mul r u (ring_pow r e k)") (LABEL_TAC "unit") THENL [REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"x:A"), (← q r"ring_1 r:A")] THEN ASM_SIMP_TAC [RING_POW_ONE, RING_1, RING_MUL_RID, RING_UNIT_IN_CARRIER], ALL_TAC] THEN SUBGOAL_THEN (← q r"!d:A. d IN ring_carrier r
            ==> !x y. x IN ring_carrier r /\ y IN ring_carrier r /\
                      ring_coprime r (x,y) /\ ring_mul r x y = ring_pow r d k
                      ==> ?u e. ring_unit r u /\ e IN ring_carrier r /\
                                x = ring_mul r u (ring_pow r e k)") (fun th => ASM_MESON_TAC [th]) THEN MATCH_MP_TAC UFD_PRIME_FACTOR_INDUCT THEN ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL [ASM_REWRITE_TAC [RING_POW_ZERO] THEN MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"y:A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"x:A = ring_0 r \/ y = ring_0 r") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [INTEGRAL_DOMAIN_MUL_EQ_0], MAP_EVERY EXISTS_TAC [(← q r"ring_1 r:A"), (← q r"ring_0 r:A")] THEN ASM_SIMP_TAC [RING_UNIT_1, RING_0, RING_POW_ZERO, RING_MUL_LID], REMOVE_THEN "unit" MATCH_MP_TAC THEN ASM_MESON_TAC [RING_COPRIME_0]], X_GEN_TAC (← q r"w:A") THEN DISCH_TAC THEN MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"y:A")] THEN STRIP_TAC THEN REMOVE_THEN "unit" MATCH_MP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"x:A"), (← q r"y:A")] RING_UNIT_MUL_EQ) THEN ASM_SIMP_TAC [RING_UNIT_POW], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"p:A"), (← q r"d:A")] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ih"))) THEN SUBGOAL_THEN (← q r"(p:A) IN ring_carrier r /\ ~(p = ring_0 r) /\ ~ring_unit r p") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [ring_prime], ALL_TAC] THEN ASM_SIMP_TAC [RING_MUL_POW] THEN MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"y:A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_divides r p (x:A) \/ ring_divides r p y") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [(← GSYM RING_PRIME_DIVIDES_MUL)] THEN MATCH_MP_TAC RING_DIVIDES_RMUL THEN ASM_SIMP_TAC [RING_POW] THEN UNDISCH_TAC (← q r"~(k = 0)") THEN SPEC_TAC ((← q r"k:num"), (← q r"k:num")) THEN INDUCT_TAC THEN REWRITE_TAC [ring_pow] THEN ASM_SIMP_TAC [RING_DIVIDES_RMUL, RING_DIVIDES_REFL, RING_POW], MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A"), (← q r"d:A"), (← q r"x:A"), (← q r"y:A"), (← q r"k:num")] lemma) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"x1:A") STRIP_ASSUME_TAC) THEN REMOVE_THEN "ih" (MP_TAC o (SPECL [(← q r"x1:A"), (← q r"y:A")])) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"u:A") THEN DISCH_THEN (X_CHOOSE_THEN (← q r"e:A") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"ring_mul r p e:A") THEN ASM_SIMP_TAC [RING_MUL, RING_MUL_POW] THEN MATCH_MP_TAC (← RING_RULE (← q r"ring_mul r z (ring_mul r u t) = ring_mul r u (ring_mul r z (t:A))")) THEN ASM_SIMP_TAC [RING_POW, RING_UNIT_IN_CARRIER], SUBGOAL_THEN (← q r"ring_mul r y x = ring_mul r x (y:A)") ASSUME_TAC THENL [ASM_MESON_TAC [RING_MUL_SYM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A"), (← q r"d:A"), (← q r"y:A"), (← q r"x:A"), (← q r"k:num")] lemma) THEN ANTS_TAC THENL [ONCE_REWRITE_TAC [RING_COPRIME_SYM] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"y1:A") STRIP_ASSUME_TAC) THEN REMOVE_THEN "ih" MATCH_MP_TAC THEN EXISTS_TAC (← q r"y1:A") THEN ONCE_REWRITE_TAC [RING_COPRIME_SYM] THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [RING_MUL_SYM]])

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
