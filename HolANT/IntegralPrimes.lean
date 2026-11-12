/- ========================================================================= -/
/- ANT: Prime ideals in integral extensions                                -/
/- ========================================================================= -/
/- File: HolANT/IntegralPrimes.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/integral_primes.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antintegralprimesdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, ANT/integral.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.IntegralPrimes fills them).

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
import HolLibrary.Matroids
import HolLibrary.Permutations
import HolLibrary.RingDet
import HolLibrary.FieldTheory
import HolANT.Integral

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.Integral

namespace HolANT.IntegralPrimes

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (EMPTY_GSPEC EQ_TRANS EXTENSION FINITE_IMAGE FINITE_SUBSET_IMAGE
   FORALL_IN_IMAGE IDEAL_GENERATED_FINITARY IDEAL_GENERATED_FINITE_IMAGE
   IDEAL_GENERATED_INC IDEAL_GENERATED_SUBSET IMP_IMP INTEGRAL_ELEMENT_RELATION
   INTEGRAL_SPAN_FINITE_SET IN_DIFF IN_ELIM_THM IN_RING_IDEAL_0
   IN_RING_IDEAL_ADD IN_RING_IDEAL_LMUL IN_RING_IDEAL_NEG IN_RING_IDEAL_RMUL
   IN_RING_IDEAL_SUB IN_RING_IDEAL_SUM IN_SING LEFT_IMP_EXISTS_THM LT
   MAXIMAL_IMP_PRIME_IDEAL MAXIMAL_IMP_PROPER_IDEAL MAXIMAL_IMP_RING_IDEAL
   MAXIMAL_SUPERIDEAL_EXISTS MONO_EXISTS NOT_EXISTS_THM PRIME_IDEAL_0
   PRIME_IDEAL_HOMOMORPHIC_PREIMAGE PRIME_IMP_PROPER_IDEAL PRIME_IMP_RING_IDEAL
   PRIME_SUPERIDEAL_EXCLUDING_EXISTS PROPER_IDEAL_HOMOMORPHIC_PREIMAGE PSUBSET
   RIGHT_IMP_EXISTS_THM RIGHT_IMP_FORALL_THM RING_0 RING_1
   RING_1_NOT_IN_PRIME_IDEAL RING_ADD RING_ADD_RDISTRIB RING_ADD_RZERO RING_DET
   RING_DET_DEPENDENT_COLUMNS_MUL_IDEAL RING_DET_DIAGONAL_CONGRUENCE
   RING_DET_HOMOMORPHISM RING_HOMOMORPHISM_SUB RING_IDEAL_0
   RING_IDEAL_IDEAL_GENERATED RING_IDEAL_IMP_SUBSET RING_IDEAL_SETADD
   RING_MONIC_RELATION_FACTOR RING_MONOMORPHISM_EQ_0
   RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_MUL RING_MULTSYS_HOMOMORPHIC_IMAGE
   RING_MULTSYS_NONPRIME RING_MUL_ASSOC RING_MUL_IN_PRIME_IDEAL RING_MUL_LID
   RING_MUL_LZERO RING_POW RING_POW_IN_PRIME_IDEAL RING_SETADD_SUPERSET_LEFT
   RING_SETADD_SUPERSET_RIGHT RING_SPAN_FINITE RING_SPAN_INC RING_SUB
   RING_SUB_RDISTRIB RING_SUM RING_SUM_ADD RING_SUM_CLAUSES RING_SUM_CLOSED
   RING_SUM_DELTA RING_SUM_EQ RING_SUM_EQ_0 RING_SUM_LMUL RING_SUM_RMUL
   RING_SUM_SUB SING_SUBSET SKOLEM_THM SUBSET SUBSET_ANTISYM_EQ SUBSET_TRANS
   UNIONS_GSPEC maximal_ideal num_WOP ring_homomorphism ring_pow ring_setadd : thm)
  deriving Inhabited

/-- What integral_primes.ml uses from Session besides theorems. -/
structure IntegralPrimesDeps where
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
/- integral_primes.ml phrases from line 49 to 551                         -/
/- ---------------------------------------------------------------------- -/

structure IntegralPrimes where
  -- @@FIELDS
  INTEGRAL_DETERMINANT_TRICK_IDEAL : thm
  RING_SPAN_IDEAL_COMBINATION : thm
  INTEGRAL_EXTENSION_PRIME_ABOVE : thm
  INTEGRAL_EXTENSION_LYING_OVER : thm
  INTEGRAL_EXTENSION_GOING_UP : thm
  INTEGRAL_EXTENSION_INCOMPARABLE : thm
  INTEGRAL_EXTENSION_MAXIMAL_IDEAL : thm
  INTEGRAL_EXTENSION_PRIME_NONZERO : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupIntegralPrimes [HolBase] (D : IntegralPrimesDeps) :
    ExceptT String IO IntegralPrimes := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, ASM_MESON_TAC, MESON, MESON_TAC, RING_RULE, SET_RULE, SET_TAC,
        TAUT, .. } := D
  let { EMPTY_GSPEC, EQ_TRANS, EXTENSION, FINITE_IMAGE, FINITE_SUBSET_IMAGE,
        FORALL_IN_IMAGE, IDEAL_GENERATED_FINITARY, IDEAL_GENERATED_FINITE_IMAGE,
        IDEAL_GENERATED_INC, IDEAL_GENERATED_SUBSET, IMP_IMP,
        INTEGRAL_ELEMENT_RELATION, INTEGRAL_SPAN_FINITE_SET, IN_DIFF, IN_ELIM_THM,
        IN_RING_IDEAL_0, IN_RING_IDEAL_ADD, IN_RING_IDEAL_LMUL, IN_RING_IDEAL_NEG,
        IN_RING_IDEAL_RMUL, IN_RING_IDEAL_SUB, IN_RING_IDEAL_SUM, IN_SING,
        LEFT_IMP_EXISTS_THM, LT, MAXIMAL_IMP_PRIME_IDEAL, MAXIMAL_IMP_PROPER_IDEAL,
        MAXIMAL_IMP_RING_IDEAL, MAXIMAL_SUPERIDEAL_EXISTS, MONO_EXISTS, NOT_EXISTS_THM,
        PRIME_IDEAL_0, PRIME_IDEAL_HOMOMORPHIC_PREIMAGE, PRIME_IMP_PROPER_IDEAL,
        PRIME_IMP_RING_IDEAL, PRIME_SUPERIDEAL_EXCLUDING_EXISTS,
        PROPER_IDEAL_HOMOMORPHIC_PREIMAGE, PSUBSET, RIGHT_IMP_EXISTS_THM,
        RIGHT_IMP_FORALL_THM, RING_0, RING_1, RING_1_NOT_IN_PRIME_IDEAL, RING_ADD,
        RING_ADD_RDISTRIB, RING_ADD_RZERO, RING_DET,
        RING_DET_DEPENDENT_COLUMNS_MUL_IDEAL, RING_DET_DIAGONAL_CONGRUENCE,
        RING_DET_HOMOMORPHISM, RING_HOMOMORPHISM_SUB, RING_IDEAL_0,
        RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IMP_SUBSET, RING_IDEAL_SETADD,
        RING_MONIC_RELATION_FACTOR, RING_MONOMORPHISM_EQ_0,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL, RING_MULTSYS_HOMOMORPHIC_IMAGE,
        RING_MULTSYS_NONPRIME, RING_MUL_ASSOC, RING_MUL_IN_PRIME_IDEAL, RING_MUL_LID,
        RING_MUL_LZERO, RING_POW, RING_POW_IN_PRIME_IDEAL, RING_SETADD_SUPERSET_LEFT,
        RING_SETADD_SUPERSET_RIGHT, RING_SPAN_FINITE, RING_SPAN_INC, RING_SUB,
        RING_SUB_RDISTRIB, RING_SUM, RING_SUM_ADD, RING_SUM_CLAUSES, RING_SUM_CLOSED,
        RING_SUM_DELTA, RING_SUM_EQ, RING_SUM_EQ_0, RING_SUM_LMUL, RING_SUM_RMUL,
        RING_SUM_SUB, SING_SUBSET, SKOLEM_THM, SUBSET, SUBSET_ANTISYM_EQ, SUBSET_TRANS,
        UNIONS_GSPEC, maximal_ideal, num_WOP, ring_homomorphism, ring_pow, ring_setadd, .. } := D.core1
  -- @@SCOPE END

  let INTEGRAL_DETERMINANT_TRICK_IDEAL ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let v1 ← GSYM RING_MUL_ASSOC
    let q2 ← q r"(z:B) IN ring_carrier s"
    let q3 ← q r"z:B"
    let q8 ← q r"D = ring_mul s (ring_1 s) (D:B)"
    let q9 ← q r"c:B->A"
    let q10 ← q r"ring_1 s IN ring_span (r,s) (f:A->B) g"
    let q11 ← q r"y:B = x"
    let q12 ← q r"(if (x:B) = y then t else ring_0 r:A) IN ring_carrier r"
    let q13 ← q r"(y:B) IN ring_carrier s"
    let q14 ← q r"y:B"
    let q15 ← q r"y:B"
    let q16 ← q r"ring_sum s g
        (\y. ring_sub s (if y = x then ring_mul s ((f:A->B) t) x
                         else ring_0 s)
                        (ring_mul s (f((a:B->B->A) x y)) y))"
    let q17 ← q r"(x:B) = y ==> x IN j ==> y IN j"
    let r18 ← MESON [] q17
    let q26 ← q r"x:B"
    let q27 ← q r"(x:B) IN ring_carrier s"
    let q28 ← q r"x:B"
    let q29 ← q r"z:B"
    let q30 ← q r"\x:B. x"
    let q31 ← q r"\x y. (f:A->B)((m:B->B->A) x y)"
    let q32 ← q r"g:B->bool"
    let q33 ← q r"j:B->bool"
    let q34 ← q r"s:B ring"
    let v35 ← ISPECL [q34, q33, q32, q31, q30, q29] RING_DET_DEPENDENT_COLUMNS_MUL_IDEAL
    let v36 ← REWRITE_RULE [] v35
    let q37 ← q r"z:B"
    let q38 ← q r"!z:B. z IN g ==> ring_mul s z D IN j"
    let q39 ← q r"(D:B) IN ring_carrier s"
    let q40 ← q r"D = ring_det s (g:B->bool) (\x y. (f:A->B)((m:B->B->A) x y))"
    let q41 ← q r"m:B->B->A"
    let q42 ← q r"g:B->bool"
    let q43 ← q r"f:A->B"
    let q44 ← q r"s:B ring"
    let q45 ← q r"r:A ring"
    let v46 ← ISPECL [q45, q44, q43, q42, q41] RING_DET_HOMOMORPHISM
    let q47 ← q r"ring_sub r (ring_sub r c b) c = ring_neg r (b:A)"
    let r48 ← RING_RULE q47
    let v49 ← REWRITE_RULE [IMP_IMP] r48
    let q50 ← q r"ring_sub r (ring_sub r c ((a:B->B->A) x y)) c = ring_neg r (a x y)"
    let q51 ← q r"c:A"
    let q52 ← q r"if (x:B) = y then t else ring_0 r:A"
    let q53 ← q r"(if (x:B) = y then t else ring_0 r:A) IN ring_carrier r"
    let q54 ← q r"y:B"
    let q55 ← q r"x:B"
    let q56 ← q r"ring_det r g (m:B->B->A)"
    let q57 ← q r"!x y:B. x IN g /\ y IN g ==> (m:B->B->A) x y IN ring_carrier r"
    let q58 ← q r"m = \x y:B. ring_sub r (if x = y then t else ring_0 r)
                           ((a:B->B->A) x y)"
    let q59 ← q r"!x y:B. x IN g /\ y IN g ==> (a:B->B->A) x y IN ring_carrier r"
    prove
      r"!r s (f:A->B) j p (g:B->bool) (a:B->B->A) t.
          ring_homomorphism(r,s) f /\ ring_ideal s j /\ ring_ideal r p /\
          FINITE g /\ g SUBSET ring_carrier s /\
          ring_1 s IN ring_span (r,s) f g /\ t IN ring_carrier r /\
          (!x y. x IN g /\ y IN g ==> a x y IN p) /\
          (!x. x IN g
               ==> ring_sub s (ring_mul s (f t) x)
                     (ring_sum s g (\y. ring_mul s (f(a x y)) y)) IN j)
          ==> ?d. d IN ring_carrier r /\ f d IN j /\
                  ring_sub r d (ring_pow r t (CARD g)) IN p"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN q59 ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN ABBREV_TAC q58 THEN SUBGOAL_THEN q57 ASSUME_TAC THENL [EXPAND_TAC "m" THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [RING_SUB, RING_0], ALL_TAC] THEN EXISTS_TAC q56 THEN REWRITE_TAC [RING_DET] THEN CONJ_TAC THENL [ALL_TAC, MATCH_MP_TAC RING_DET_DIAGONAL_CONGRUENCE THEN ASM_REWRITE_TAC [] THEN MAP_EVERY X_GEN_TAC [q55, q54] THEN STRIP_TAC THEN EXPAND_TAC "m" THEN SUBGOAL_THEN q53 MP_TAC THENL [COND_CASES_TAC THEN ASM_SIMP_TAC [RING_0], ALL_TAC] THEN SPEC_TAC (q52, q51) THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN q50 SUBST1_TAC THENL [MATCH_MP_TAC v49 THEN ASM_SIMP_TAC [], MATCH_MP_TAC IN_RING_IDEAL_NEG THEN ASM_SIMP_TAC []]] THEN MP_TAC v46 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o ((REWRITE_RULE [SUBSET, FORALL_IN_IMAGE]) o (GEN_REWRITE_RULE id [ring_homomorphism]))) THEN ABBREV_TAC q40 THEN SUBGOAL_THEN q39 ASSUME_TAC THENL [EXPAND_TAC "D" THEN REWRITE_TAC [RING_DET], ALL_TAC] THEN SUBGOAL_THEN q38 ASSUME_TAC THENL [X_GEN_TAC q37 THEN DISCH_TAC THEN EXPAND_TAC "D" THEN MATCH_MP_TAC v36 THEN ASM_SIMP_TAC [] THEN CONJ_TAC THENL [ASM_MESON_TAC [SUBSET], ALL_TAC] THEN X_GEN_TAC q28 THEN DISCH_TAC THEN SUBGOAL_THEN q27 ASSUME_TAC THENL [ASM_MESON_TAC [SUBSET], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o ((SPEC q26) o (checkM (fun th => (do let z19 ← (do let z20 ← (pure th); pure (concl z20)); canM (fun z21 => (do let z22 ← (pure z21); find_termM (fun z23 => (do let z25 ← (pure z23); let z24 ← (q r"ring_sub s:B->B->B"); pure (z24 == z25))) z22)) z19))))) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r18 THEN TRANS_TAC EQ_TRANS q16 THEN CONJ_TAC THENL [wPart rand (lhand o rand) RING_SUM_SUB THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN X_GEN_TAC q15 THEN DISCH_TAC THEN CONJ_TAC THENL [COND_CASES_TAC, ALL_TAC] THEN ASM_MESON_TAC [RING_MUL, RING_0, SUBSET], DISCH_THEN SUBST1_TAC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC [RING_SUM_DELTA, RING_MUL], MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC q14 THEN DISCH_TAC THEN EXPAND_TAC "m" THEN REWRITE_TAC [] THEN SUBGOAL_THEN q13 ASSUME_TAC THENL [ASM_MESON_TAC [SUBSET], ALL_TAC] THEN SUBGOAL_THEN q12 ASSUME_TAC THENL [COND_CASES_TAC THEN ASM_SIMP_TAC [RING_0], ALL_TAC] THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_SUB th)])) THEN ASM_SIMP_TAC [RING_SUB_RDISTRIB] THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_CASES_TAC q11 THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [RING_MUL_LZERO]], ALL_TAC] THEN UNDISCH_TAC q10 THEN ASM_SIMP_TAC [RING_SPAN_FINITE, IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC q9 THEN STRIP_TAC THEN SUBGOAL_THEN q8 SUBST1_TAC THENL [ASM_SIMP_TAC [RING_MUL_LID], ALL_TAC] THEN FIRST_ASSUM (SUBST1_TAC o (checkM (fun th => (do let z7 ← (q r"ring_1 s:B"); let z6 ← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); liftExcept (lhand z4)); pure (z6 == z7))))) THEN wPart lhand (rand o rand) RING_SUM_RMUL THEN ANTS_TAC THENL [ASM_MESON_TAC [RING_MUL, SUBSET], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC IN_RING_IDEAL_SUM THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC q3 THEN DISCH_TAC THEN SUBGOAL_THEN q2 ASSUME_TAC THENL [ASM_MESON_TAC [SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [v1] THEN MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN ASM_SIMP_TAC [])

  let RING_SPAN_IDEAL_COMBINATION ← prove
    r"!r s (f:A->B) p g (k:K->bool) u y.
        ring_homomorphism(r,s) f /\ ring_ideal r p /\
        FINITE g /\ g SUBSET ring_carrier s /\
        (!i. i IN k ==> u i IN p /\ y i IN ring_span (r,s) f g)
        ==> ?a. (!e. e IN g ==> a e IN p) /\
                ring_sum s k (\i. ring_mul s (f(u i)) (y i)) =
                ring_sum s g (\e. ring_mul s (f(a e)) e)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o ((REWRITE_RULE [SUBSET, FORALL_IN_IMAGE]) o (GEN_REWRITE_RULE id [ring_homomorphism]))) THEN SUBGOAL_THEN (← q r"!e:B. e IN g ==> e IN ring_carrier s") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x:A. x IN p ==> x IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN MATCH_MP_TAC (← REWRITE_RULE [] (← ISPECL [(← q r"s:B ring"), (← q r"\z. ?a. (!e. e IN g ==> a e IN p) /\
             z = ring_sum s g (\e. ring_mul s ((f:A->B)(a e)) e)")] RING_SUM_CLOSED)) THEN REPEAT CONJ_TAC THENL [EXISTS_TAC (← q r"\e:B. ring_0 r:A") THEN ASM_SIMP_TAC [IN_RING_IDEAL_0] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_EQ_0 THEN ASM_SIMP_TAC [RING_MUL_LZERO], MAP_EVERY X_GEN_TAC [(← q r"x1:B"), (← q r"x2:B")] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"a1:B->A") STRIP_ASSUME_TAC) (X_CHOOSE_THEN (← q r"a2:B->A") STRIP_ASSUME_TAC)))) THEN EXISTS_TAC (← q r"\e:B. ring_add r ((a1:B->A) e) (a2 e)") THEN ASM_SIMP_TAC [IN_RING_IDEAL_ADD] THEN SUBGOAL_THEN (← q r"!e:B. e IN g
            ==> (a1:B->A) e IN ring_carrier r /\ (a2:B->A) e IN ring_carrier r") ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN wPart lhand (rand o rand) RING_SUM_ADD THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_MUL], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"e:B") THEN DISCH_TAC THEN ASM_SIMP_TAC [RING_ADD_RDISTRIB], X_GEN_TAC (← q r"i:K") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"i:K"))) THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [RING_SPAN_FINITE, IN_ELIM_THM] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"b:B->A") STRIP_ASSUME_TAC)) THEN EXISTS_TAC (← q r"\e:B. ring_mul r ((u:K->A) i) ((b:B->A) e)") THEN ASM_SIMP_TAC [IN_RING_IDEAL_RMUL] THEN SUBGOAL_THEN (← q r"(u:K->A) i IN ring_carrier r") ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN wPart lhand (rand o rand) RING_SUM_LMUL THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_MUL], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"e:B") THEN DISCH_TAC THEN ASM_SIMP_TAC [RING_MUL_ASSOC]])

  let INTEGRAL_EXTENSION_PRIME_ABOVE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r8 ← RING_RULE (← q r"y = ring_sub r d (ring_sub r d (y:A))")
    let r9 ← RING_RULE (← q r"ring_sub s (ring_mul s (ring_add s x w) e) (ring_mul s w e) =
          ring_mul s x (e:B)")
    let r25 ← RING_RULE (← q r"ring_mul s (ring_mul s c u) e =
        ring_mul s u (ring_mul s c (e:B))")
    let r26 ← SET_RULE (← q r"DISJOINT s (IMAGE (f:A->B) t) <=> !x. x IN t ==> ~(f x IN s)")
    prove
      r"!r s (f:A->B) p j.
          ring_homomorphism(r,s) f /\
          (!y. y IN ring_carrier s ==> integral_element (r,s) f y) /\
          prime_ideal r p /\ ring_ideal s j /\
          (!x. x IN ring_carrier r /\ f x IN j ==> x IN p)
          ==> ?q. prime_ideal s q /\ j SUBSET q /\
                  {x | x IN ring_carrier r /\ f x IN q} = p"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o ((REWRITE_RULE [SUBSET, FORALL_IN_IMAGE]) o (GEN_REWRITE_RULE id [ring_homomorphism]))) THEN SUBGOAL_THEN (← q r"!x:A. x IN p ==> x IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"IMAGE (f:A->B) p SUBSET ring_carrier s") ASSUME_TAC THENL [ASM_SIMP_TAC [SUBSET, FORALL_IN_IMAGE], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"IMAGE (f:A->B) (ring_carrier r DIFF p)"), (← q r"ring_setadd s j (ideal_generated s (IMAGE (f:A->B) p))")] PRIME_SUPERIDEAL_EXCLUDING_EXISTS) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_SETADD, RING_IDEAL_IDEAL_GENERATED] THEN CONJ_TAC THENL [MATCH_MP_TAC RING_MULTSYS_HOMOMORPHIC_IMAGE THEN EXISTS_TAC (← q r"r:A ring") THEN ASM_SIMP_TAC [RING_MULTSYS_NONPRIME], ALL_TAC] THEN REWRITE_TAC [r26] THEN X_GEN_TAC (← q r"t:A") THEN REWRITE_TAC [IN_DIFF] THEN STRIP_TAC THEN REWRITE_TAC [ring_setadd, IN_ELIM_THM, NOT_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"x:B"), (← q r"w:B")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"?k. FINITE k /\ k SUBSET p /\
            (w:B) IN ideal_generated s (IMAGE (f:A->B) k)") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"(w:B) IN ideal_generated s (IMAGE (f:A->B) p)") THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [IDEAL_GENERATED_FINITARY] THEN REWRITE_TAC [UNIONS_GSPEC, IN_ELIM_THM, FINITE_SUBSET_IMAGE] THEN MESON_TAC [], ALL_TAC] THEN UNDISCH_TAC (← q r"(w:B) IN ideal_generated s (IMAGE (f:A->B) k)") THEN MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"k:A->bool"), (← q r"f:A->B")] IDEAL_GENERATED_FINITE_IMAGE) THEN ANTS_TAC THENL [ASM SET_TAC [], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:A->B") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"!i:A. i IN k
              ==> i IN p /\ i IN ring_carrier r /\ (f:A->B) i IN ring_carrier s") ASSUME_TAC THENL [ASM_MESON_TAC [SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"f:A->B"), (← q r"IMAGE (c:A->B) k")] INTEGRAL_SPAN_FINITE_SET) THEN ASM_SIMP_TAC [FINITE_IMAGE, FORALL_IN_IMAGE] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"g:B->bool") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"!e:B. e IN g
              ==> ?a. (!y. y IN g ==> a y IN p) /\
                      ring_mul s w e =
                      ring_sum s g (\y. ring_mul s ((f:A->B)(a y)) y)") MP_TAC THENL [X_GEN_TAC (← q r"e:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(e:B) IN ring_carrier s") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"f:A->B"), (← q r"p:A->bool"), (← q r"g:B->bool"), (← q r"k:A->bool"), (← q r"\i:A. i"), (← q r"\i:A. ring_mul s ((c:A->B) i) e")] RING_SPAN_IDEAL_COMBINATION) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [X_GEN_TAC (← q r"i:A") THEN DISCH_TAC THEN CONJ_TAC THENL [ASM SET_TAC [], ASM_MESON_TAC [RING_SPAN_INC]], ALL_TAC] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"a:B->A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN wPart lhand (rand o rand) RING_SUM_RMUL THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_MUL], ALL_TAC] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"i:A") THEN DISCH_TAC THEN REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(f:A->B) i IN ring_carrier s /\ (c:A->B) i IN ring_carrier s") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN MATCH_MP_TAC (← REWRITE_RULE [IMP_IMP] r25) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN REWRITE_TAC [SKOLEM_THM] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"a:B->B->A")) THEN FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o (checkM (fun th => (do if ← (do let z19 ← (do let z20 ← (pure th); pure (concl z20)); pure (is_eq z19)) then (do let z24 ← (q r"w:B"); let z23 ← (do let z21 ← (do let z22 ← (pure th); pure (concl z22)); liftExcept (lhand z21)); pure (z23 == z24)) else pure false)))) THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier s /\ (w:B) IN ring_carrier s") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET, RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"f:A->B"), (← q r"j:B->bool"), (← q r"p:A->bool"), (← q r"g:B->bool"), (← q r"a:B->B->A"), (← q r"t:A")] INTEGRAL_DETERMINANT_TRICK_IDEAL) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN X_GEN_TAC (← q r"e:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(e:B) IN ring_carrier s") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"e:B")) o (checkM (fun th => (do if ← (do let z10 ← (do let z11 ← (pure th); pure (concl z11)); canM (fun z12 => (do let z13 ← (pure z12); find_termM (fun z14 => (do let z16 ← (pure z14); let z15 ← (q r"a:B->B->A"); pure (z15 == z16))) z13)) z10) then (do let z17 ← (do let z18 ← (pure th); pure (concl z18)); pure (is_forall z17)) else pure false))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o (SYM o CONJUNCT2)) THEN SUBGOAL_THEN (← q r"ring_sub s (ring_mul s (ring_add s x w) e) (ring_mul s w e) =
          ring_mul s x (e:B)") SUBST1_TAC THENL [MATCH_MP_TAC (← REWRITE_RULE [IMP_IMP] r9) THEN ASM_REWRITE_TAC [], MATCH_MP_TAC IN_RING_IDEAL_RMUL THEN ASM_REWRITE_TAC []], DISCH_THEN (X_CHOOSE_THEN (← q r"d:A") STRIP_ASSUME_TAC)] THEN SUBGOAL_THEN (← q r"(d:A) IN p") ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_pow r (t:A) (CARD(g:B->bool)) IN p") MP_TAC THENL [SUBGOAL_THEN (← q r"ring_pow r (t:A) (CARD(g:B->bool)) =
          ring_sub r d (ring_sub r d (ring_pow r t (CARD g)))") SUBST1_TAC THENL [MATCH_MP_TAC (← REWRITE_RULE [IMP_IMP] r8) THEN ASM_SIMP_TAC [RING_POW], MATCH_MP_TAC IN_RING_IDEAL_SUB THEN ASM_REWRITE_TAC []], ASM_SIMP_TAC [RING_POW_IN_PRIME_IDEAL]], MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"q:B->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [TRANS_TAC SUBSET_TRANS (← q r"ring_setadd s j (ideal_generated s (IMAGE (f:A->B) p))") THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC RING_SETADD_SUPERSET_LEFT THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, IN_RING_IDEAL_0, RING_IDEAL_IDEAL_GENERATED], GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"y:A") THEN REWRITE_TAC [IN_ELIM_THM] THEN EQ_TAC THENL [STRIP_TAC THEN ASM SET_TAC [], DISCH_TAC] THEN ASM_SIMP_TAC [] THEN FIRST_X_ASSUM (MATCH_MP_TAC o ((REWRITE_RULE [SUBSET]) o (checkM (fun th => (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); canM (fun z3 => (do let z4 ← (pure z3); find_termM (fun z5 => (do let z7 ← (pure z5); let z6 ← (q r"ring_setadd s:(B->bool)->(B->bool)->B->bool"); pure (z6 == z7))) z4)) z1))))) THEN MATCH_MP_TAC (← REWRITE_RULE [SUBSET, RIGHT_IMP_FORALL_THM, IMP_IMP] RING_SETADD_SUPERSET_RIGHT) THEN ASM_SIMP_TAC [IN_RING_IDEAL_0, RING_IDEAL_IDEAL_GENERATED] THEN CONJ_TAC THENL [MESON_TAC [IDEAL_GENERATED_SUBSET, SUBSET], MATCH_MP_TAC IDEAL_GENERATED_INC THEN ASM SET_TAC []]]])

  let INTEGRAL_EXTENSION_LYING_OVER ← prove
    r"!r s (f:A->B) p.
        ring_homomorphism(r,s) f /\
        (!y. y IN ring_carrier s ==> integral_element (r,s) f y) /\
        prime_ideal r p /\
        (!x. x IN ring_carrier r /\ f x = ring_0 s ==> x IN p)
        ==> ?q. prime_ideal s q /\ {x | x IN ring_carrier r /\ f x IN q} = p"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"f:A->B"), (← q r"p:A->bool"), (← q r"{ring_0 s:B}")] INTEGRAL_EXTENSION_PRIME_ABOVE) THEN ASM_REWRITE_TAC [RING_IDEAL_0, IN_SING] THEN MESON_TAC [])

  let INTEGRAL_EXTENSION_GOING_UP ← prove
    r"!r s (f:A->B) p p' q.
        ring_homomorphism(r,s) f /\
        (!y. y IN ring_carrier s ==> integral_element (r,s) f y) /\
        prime_ideal s q /\ {x | x IN ring_carrier r /\ f x IN q} = p /\
        prime_ideal r p' /\ p SUBSET p'
        ==> ?q'. prime_ideal s q' /\ q SUBSET q' /\
                 {x | x IN ring_carrier r /\ f x IN q'} = p'"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_EXTENSION_PRIME_ABOVE THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN ASM SET_TAC [])

  let INTEGRAL_EXTENSION_INCOMPARABLE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"b = ring_sub s (ring_add s a b) (a:B)")
    let r2 ← RING_RULE (← q r"a = ring_sub s (ring_add s a b) (b:B)")
    let r10 ← TAUT (← q r"p /\ ~q ==> (p <=> q) ==> F")
    let r11 ← TAUT (← q r"p <=> ~p ==> F")
    prove
      r"!r s (f:A->B) q q'.
          ring_homomorphism(r,s) f /\
          (!y. y IN ring_carrier s ==> integral_element (r,s) f y) /\
          prime_ideal s q /\ ring_ideal s q' /\ q SUBSET q' /\
          {x | x IN ring_carrier r /\ f x IN q'} =
          {x | x IN ring_carrier r /\ f x IN q}
          ==> q = q'"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o ((REWRITE_RULE [SUBSET, FORALL_IN_IMAGE]) o (GEN_REWRITE_RULE id [ring_homomorphism]))) THEN SUBGOAL_THEN (← q r"!z:B. z IN q ==> z IN q'") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN REWRITE_TAC [(← GSYM SUBSET_ANTISYM_EQ)] THEN ASM_REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(y:B) IN ring_carrier s") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN GEN_REWRITE_TAC id [r11] THEN DISCH_TAC THEN MP_TAC (← BETA_RULE (← ISPEC (← q r"\n. ?c. (!i. i < n ==> c i IN ring_carrier r) /\
              ring_add s (ring_pow s y n)
                (ring_sum s {i | i < n}
                   (\i. ring_mul s ((f:A->B)(c i)) (ring_pow s y i))) IN q") num_WOP)) THEN MATCH_MP_TAC r10 THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"f:A->B"), (← q r"y:B")] INTEGRAL_ELEMENT_RELATION) THEN ASM_SIMP_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"n:num") THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"c:num->A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [IN_RING_IDEAL_0], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"n:num") (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"c:num->A") STRIP_ASSUME_TAC) MP_TAC)) THEN ASM_CASES_TAC (← q r"n = 0") THENL [UNDISCH_TAC (← q r"ring_add s (ring_pow s y n)
          (ring_sum s {i | i < n}
             (\i. ring_mul s ((f:A->B)(c i)) (ring_pow s y i))) IN q") THEN ASM_REWRITE_TAC [ring_pow, LT, EMPTY_GSPEC, RING_SUM_CLAUSES] THEN ASM_SIMP_TAC [RING_ADD_RZERO, RING_1] THEN ASM_MESON_TAC [RING_1_NOT_IN_PRIME_IDEAL], ALL_TAC] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"n - 1"))) THEN ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [] THEN EXISTS_TAC (← q r"\i. (c:num->A)(i + 1)") THEN REWRITE_TAC [] THEN CONJ_TAC THENL [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"y:B"), (← q r"\i. (f:A->B)((c:num->A) i)"), (← q r"n:num")] RING_MONIC_RELATION_FACTOR) THEN ASM_SIMP_TAC [] THEN DISCH_THEN (fun th => tactic_of do pure (FIRST_X_ASSUM (MP_TAC o (checkM (fun th' => (do let z3 ← (do let z4 ← (pure th'); pure (concl z4)); canM (fun z5 => (do let z6 ← (pure z5); find_termM (fun z7 => (do let z9 ← (pure z7); let z8 ← (q r"ring_pow s (y:B) n"); pure (z8 == z9))) z6)) z3)))) THEN REWRITE_TAC [th])) THEN ABBREV_TAC (← q r"R = ring_add s (ring_pow s y (n - 1))
            (ring_sum s {i | i < n - 1}
               (\i. ring_mul s ((f:A->B)((c:num->A)(i + 1)))
                               (ring_pow s y i)))") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(R:B) IN ring_carrier s") ASSUME_TAC THENL [EXPAND_TAC "R" THEN ASM_SIMP_TAC [RING_ADD, RING_POW, RING_SUM], ALL_TAC] THEN SUBGOAL_THEN (← q r"(c:num->A) 0 IN ring_carrier r") ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"(f:A->B)((c:num->A) 0) IN q") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"(c:num->A) 0 IN {x | x IN ring_carrier r /\ (f:A->B) x IN q'}") MP_TAC THENL [REWRITE_TAC [IN_ELIM_THM] THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(f:A->B)((c:num->A) 0) =
          ring_sub s (ring_add s (f(c 0)) (ring_mul s y R)) (ring_mul s y R)") SUBST1_TAC THENL [MATCH_MP_TAC (← REWRITE_RULE [IMP_IMP] r2) THEN ASM_SIMP_TAC [RING_MUL], MATCH_MP_TAC IN_RING_IDEAL_SUB THEN ASM_SIMP_TAC [] THEN MATCH_MP_TAC IN_RING_IDEAL_RMUL THEN ASM_REWRITE_TAC []], ASM_REWRITE_TAC [] THEN SIMP_TAC [IN_ELIM_THM]], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul s y (R:B) IN q") MP_TAC THENL [SUBGOAL_THEN (← q r"ring_mul s y (R:B) =
        ring_sub s (ring_add s (f((c:num->A) 0)) (ring_mul s y R))
                   ((f:A->B)(c 0))") SUBST1_TAC THENL [MATCH_MP_TAC (← REWRITE_RULE [IMP_IMP] r1) THEN ASM_SIMP_TAC [RING_MUL], MATCH_MP_TAC IN_RING_IDEAL_SUB THEN ASM_REWRITE_TAC []], ASM_SIMP_TAC [RING_MUL_IN_PRIME_IDEAL]])

  let INTEGRAL_EXTENSION_MAXIMAL_IDEAL ← prove
    r"!r s (f:A->B) q.
        ring_homomorphism(r,s) f /\
        (!y. y IN ring_carrier s ==> integral_element (r,s) f y) /\
        prime_ideal s q
        ==> (maximal_ideal s q <=>
             maximal_ideal r {x | x IN ring_carrier r /\ f x IN q})"
    (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"p = {x | x IN ring_carrier r /\ (f:A->B) x IN q}") THEN SUBGOAL_THEN (← q r"prime_ideal r (p:A->bool)") ASSUME_TAC THENL [EXPAND_TAC "p" THEN MATCH_MP_TAC PRIME_IDEAL_HOMOMORPHIC_PREIMAGE THEN EXISTS_TAC (← q r"s:B ring") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN EQ_TAC THEN DISCH_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool")] MAXIMAL_SUPERIDEAL_EXISTS) THEN ASM_SIMP_TAC [PRIME_IMP_PROPER_IDEAL] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"m:A->bool") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"f:A->B"), (← q r"p:A->bool"), (← q r"m:A->bool"), (← q r"q:B->bool")] INTEGRAL_EXTENSION_GOING_UP) THEN ASM_SIMP_TAC [MAXIMAL_IMP_PRIME_IDEAL] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"q':B->bool") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"q':B->bool = q") SUBST_ALL_TAC THENL [FIRST_X_ASSUM (MP_TAC o (CONJUNCT2 o ((GEN_REWRITE_RULE id [maximal_ideal]) o (checkM (fun th => (do let z6 ← (q r"maximal_ideal s (q:B->bool)"); let z5 ← (do let z4 ← (pure th); pure (concl z4)); pure (z5 == z6))))))) THEN REWRITE_TAC [NOT_EXISTS_THM] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"q':B->bool"))) THEN ASM_SIMP_TAC [PRIME_IMP_PROPER_IDEAL, PSUBSET] THEN ASM SET_TAC [], ASM_MESON_TAC []], MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"q:B->bool")] MAXIMAL_SUPERIDEAL_EXISTS) THEN ASM_SIMP_TAC [PRIME_IMP_PROPER_IDEAL] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"m:B->bool") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"q:B->bool = m") (fun th => ASM_REWRITE_TAC [th]) THEN MATCH_MP_TAC INTEGRAL_EXTENSION_INCOMPARABLE THEN MAP_EVERY EXISTS_TAC [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"f:A->B")] THEN ASM_SIMP_TAC [MAXIMAL_IMP_RING_IDEAL] THEN SUBGOAL_THEN (← q r"proper_ideal r {x | x IN ring_carrier r /\ (f:A->B) x IN m}") MP_TAC THENL [MATCH_MP_TAC PROPER_IDEAL_HOMOMORPHIC_PREIMAGE THEN EXISTS_TAC (← q r"s:B ring") THEN ASM_SIMP_TAC [MAXIMAL_IMP_PROPER_IDEAL], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (CONJUNCT2 o ((GEN_REWRITE_RULE id [maximal_ideal]) o (checkM (fun th => (do let z3 ← (q r"maximal_ideal r (p:A->bool)"); let z2 ← (do let z1 ← (pure th); pure (concl z1)); pure (z2 == z3))))))) THEN REWRITE_TAC [NOT_EXISTS_THM] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"{x | x IN ring_carrier r /\ (f:A->B) x IN m}"))) THEN REWRITE_TAC [PSUBSET] THEN EXPAND_TAC "p" THEN ASM SET_TAC []])

  let INTEGRAL_EXTENSION_PRIME_NONZERO ← prove
    r"!r s (f:A->B) q.
        ring_monomorphism(r,s) f /\ integral_domain s /\
        (!y. y IN ring_carrier s ==> integral_element (r,s) f y) /\
        prime_ideal s q /\ ~(q = {ring_0 s})
        ==> ~({x | x IN ring_carrier r /\ f x IN q} = {ring_0 r})"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"f:A->B"), (← q r"{ring_0 s:B}"), (← q r"q:B->bool")] INTEGRAL_EXTENSION_INCOMPARABLE) THEN ASM_SIMP_TAC [PRIME_IDEAL_0, PRIME_IMP_RING_IDEAL, SING_SUBSET, IN_RING_IDEAL_0] THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"x:A") THEN REWRITE_TAC [IN_ELIM_THM, IN_SING] THEN ASM_CASES_TAC (← q r"(x:A) IN ring_carrier r") THEN ASM_REWRITE_TAC [] THENL [ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0], ASM_MESON_TAC [RING_0]])

  -- @@RETURN BEGIN
  return { INTEGRAL_DETERMINANT_TRICK_IDEAL, RING_SPAN_IDEAL_COMBINATION,
           INTEGRAL_EXTENSION_PRIME_ABOVE, INTEGRAL_EXTENSION_LYING_OVER,
           INTEGRAL_EXTENSION_GOING_UP, INTEGRAL_EXTENSION_INCOMPARABLE,
           INTEGRAL_EXTENSION_MAXIMAL_IDEAL, INTEGRAL_EXTENSION_PRIME_NONZERO }
  -- @@RETURN END

end HolANT.IntegralPrimes
