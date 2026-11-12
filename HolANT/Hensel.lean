/- ========================================================================= -/
/- ANT: Hensel lemma at finite level                                       -/
/- ========================================================================= -/
/- File: HolANT/Hensel.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/hensel.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/anthenseldiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/permutations.ml, Library/ring_det.ml, ANT/ideal_arith.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.Hensel fills them).

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
import HolLibrary.Permutations
import HolLibrary.RingDet
import HolANT.IdealArith

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.IdealArith

namespace HolANT.Hensel

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD_CLAUSES ADD_EQ_0 ADD_SYM ARITH_EQ COEFF_ABOVE_DEG COEFF_IN_CARRIER_ALT
   COEFF_POLY_0 COEFF_POLY_ADD COEFF_POLY_MUL COEFF_POLY_NEG COEFF_POLY_SUB
   CONTRAPOS_THM IDEAL_POW_0 IDEAL_POW_1 IDEAL_POW_ANTIMONO IDEAL_POW_PRINCIPAL
   IMP_IMP INTEGER_RING INTEGER_RING_IDEAL_GENERATED_SING INTEGER_RING_OF_NUM
   INTEGER_RING_POW INTEGER_RING_SUB INT_SUB_RZERO IN_ELIM_THM IN_RING_IDEAL_0
   IN_RING_IDEAL_ADD IN_RING_IDEAL_LMUL IN_RING_IDEAL_NEG IN_RING_IDEAL_RMUL
   IN_RING_IDEAL_SUB IN_RING_IDEAL_SUM IN_UNIV LEFT_IMP_EXISTS_THM LE_1 LE_ADD
   LE_ADDR LE_REFL LT_IMP_LE MONO_EXISTS NOT_LT ONE POLY_CLAUSES POLY_DEG_0
   POLY_DEG_EQ_FROM_LE POLY_DEG_LE_COEFF_EQ POLY_DERIV_CONST
   POLY_DERIV_IN_CARRIER POLY_DERIV_SUB POLY_DERIV_VAR_POW
   POLY_DIVISION_COEFF_IDEAL POLY_EVAL POLY_EVAL_0 POLY_EVAL_CONST POLY_EVAL_MUL
   POLY_EVAL_POW POLY_EVAL_SUB POLY_EVAL_SUB_IN_IDEAL POLY_EVAL_TAYLOR
   POLY_EVAL_VAR POLY_RING_CLAUSES POLY_TOP_EQ_0 RADICAL_IDEAL_POW RING_0 RING_1
   RING_ADD RING_ADD_RZERO RING_IDEAL_IDEAL_GENERATED RING_IDEAL_IDEAL_POW
   RING_IDEAL_IMP_SUBSET RING_IDEAL_POLY_COEFF RING_MUL RING_MUL_IN_IDEAL_POW
   RING_MUL_LID RING_MUL_RID RING_MUL_RZERO RING_NEG RING_OF_NUM RING_POLYNOMIAL
   RING_POLYNOMIAL_0 RING_POLYNOMIAL_CONST RING_POLYNOMIAL_IMP_POWERSERIES
   RING_POLYNOMIAL_MUL RING_POLYNOMIAL_POW RING_POLYNOMIAL_SUB
   RING_POLYNOMIAL_VAR RING_POW RING_POW_ONE RING_SUB RING_SUB_EQ_0
   RING_SUB_REFL RING_SUB_RZERO RING_UNIT_QUOTIENT_RING_COSET
   RING_UNIT_QUOTIENT_RING_COSET_EQ RING_UNIT_QUOTIENT_RING_COSET_MUL
   RING_UNIT_QUOTIENT_RING_COSET_POW RING_UNIT_QUOTIENT_RING_RADICAL SUBSET cong
   int_mod : thm)
  deriving Inhabited

/-- What hensel.ml uses from Session besides theorems. -/
structure HenselDeps where
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
/- hensel.ml phrases from line 63 to 641                                  -/
/- ---------------------------------------------------------------------- -/

structure Hensel01 where
  -- @@FIELDS
  RING_UNIT_QUOTIENT_RING_IDEAL_POW : thm
  HENSEL_NEWTON_STEP : thm
  HENSEL_LEMMA : thm
  HENSEL_NEWTON_STEP_SIMPLE : thm
  HENSEL_LEMMA_POW : thm
  HENSEL_LEMMA_UNIQUE : thm
  HENSEL_LEMMA_SIMPLE : thm
  HENSEL_LEMMA_NEWTON : thm
  HENSEL_ROOT_UNIQUE : thm
  POLY_EVAL_DERIV_VAR_POW_SUB_CONST : thm
  POWER_RESIDUE_MODULO_IDEAL_POW : thm
  INTEGER_RING_IDEAL_POW_SING : thm
  RING_UNIT_QUOTIENT_INTEGER_RING : thm
  HENSEL_LEMMA_INTEGER : thm
  INT_POWER_RESIDUE_MODULO_POWER : thm
  COEFF_POLY_MUL_IN_IDEAL_POW : thm
  HENSEL_FACTORIZATION_STEP : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupHensel01 [HolBase] (D : HenselDeps) :
    ExceptT String IO Hensel01 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, INTEGER_RULE,
        INTEGER_TAC, MESON_TAC, RING_CARRIER_TAC, RING_RULE, SET_TAC, .. } := D
  let { ADD_CLAUSES, ADD_SYM, ARITH_EQ, COEFF_ABOVE_DEG, COEFF_IN_CARRIER_ALT,
        COEFF_POLY_0, COEFF_POLY_ADD, COEFF_POLY_MUL, COEFF_POLY_NEG, COEFF_POLY_SUB,
        IDEAL_POW_0, IDEAL_POW_1, IDEAL_POW_ANTIMONO, IDEAL_POW_PRINCIPAL, IMP_IMP,
        INTEGER_RING, INTEGER_RING_IDEAL_GENERATED_SING, INTEGER_RING_OF_NUM,
        INTEGER_RING_POW, INTEGER_RING_SUB, INT_SUB_RZERO, IN_ELIM_THM,
        IN_RING_IDEAL_0, IN_RING_IDEAL_ADD, IN_RING_IDEAL_LMUL, IN_RING_IDEAL_NEG,
        IN_RING_IDEAL_RMUL, IN_RING_IDEAL_SUB, IN_RING_IDEAL_SUM, IN_UNIV,
        LEFT_IMP_EXISTS_THM, LE_1, LE_ADD, LE_ADDR, LE_REFL, ONE, POLY_CLAUSES,
        POLY_DERIV_CONST, POLY_DERIV_IN_CARRIER, POLY_DERIV_SUB, POLY_DERIV_VAR_POW,
        POLY_DIVISION_COEFF_IDEAL, POLY_EVAL, POLY_EVAL_0, POLY_EVAL_CONST,
        POLY_EVAL_MUL, POLY_EVAL_POW, POLY_EVAL_SUB, POLY_EVAL_SUB_IN_IDEAL,
        POLY_EVAL_TAYLOR, POLY_EVAL_VAR, POLY_RING_CLAUSES, RADICAL_IDEAL_POW, RING_0,
        RING_1, RING_ADD, RING_ADD_RZERO, RING_IDEAL_IDEAL_GENERATED,
        RING_IDEAL_IDEAL_POW, RING_IDEAL_IMP_SUBSET, RING_MUL, RING_MUL_IN_IDEAL_POW,
        RING_MUL_LID, RING_MUL_RID, RING_MUL_RZERO, RING_NEG, RING_OF_NUM,
        RING_POLYNOMIAL, RING_POLYNOMIAL_0, RING_POLYNOMIAL_CONST,
        RING_POLYNOMIAL_IMP_POWERSERIES, RING_POLYNOMIAL_MUL, RING_POLYNOMIAL_POW,
        RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_VAR, RING_POW, RING_POW_ONE, RING_SUB,
        RING_SUB_EQ_0, RING_SUB_REFL, RING_SUB_RZERO, RING_UNIT_QUOTIENT_RING_COSET,
        RING_UNIT_QUOTIENT_RING_COSET_EQ, RING_UNIT_QUOTIENT_RING_COSET_MUL,
        RING_UNIT_QUOTIENT_RING_COSET_POW, RING_UNIT_QUOTIENT_RING_RADICAL, SUBSET,
        cong, int_mod, .. } := D.core1
  -- @@SCOPE END

  let RING_UNIT_QUOTIENT_RING_IDEAL_POW ← prove
    r"!r j n x:A.
        ring_ideal r j /\ ~(n = 0) /\ x IN ring_carrier r
        ==> (ring_unit (quotient_ring r (ideal_pow r j n))
                       (ring_coset r (ideal_pow r j n) x) <=>
             ring_unit (quotient_ring r j) (ring_coset r j x))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_pow r j n:A->bool"), (← q r"x:A")] RING_UNIT_QUOTIENT_RING_RADICAL) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"x:A")] RING_UNIT_QUOTIENT_RING_RADICAL) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, RADICAL_IDEAL_POW] THEN MESON_TAC [])

  let HENSEL_NEWTON_STEP ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"2 * i = i + i")
    prove
      r"!r m f (b:A) d u s i.
          ring_ideal r m /\ f IN ring_carrier(poly_ring r (:1)) /\
          b IN ring_carrier r /\ d IN ring_carrier r /\ u IN ring_carrier r /\
          s IN ideal_pow r m i /\
          poly_eval r f b = ring_mul r (ring_pow r d 2) s /\
          poly_eval r (poly_deriv r f) b = ring_mul r d u /\
          ring_unit (quotient_ring r m) (ring_coset r m u)
          ==> ?t u' s'.
                  t IN ideal_pow r m i /\ u' IN ring_carrier r /\
                  ring_sub r u' u IN ideal_pow r m i /\
                  s' IN ideal_pow r m (2 * i) /\
                  poly_eval r f (ring_add r b (ring_mul r d t)) =
                  ring_mul r (ring_pow r d 2) s' /\
                  poly_eval r (poly_deriv r f) (ring_add r b (ring_mul r d t)) =
                  ring_mul r d u'"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(m:A->bool) SUBSET ring_carrier r") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"(s:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_POW, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"?v:A. v IN ring_carrier r /\
            ring_sub r (ring_mul r u v) (ring_1 r) IN ideal_pow r m i") STRIP_ASSUME_TAC THENL [ASM_CASES_TAC (← q r"i = 0") THENL [EXISTS_TAC (← q r"ring_1 r:A") THEN ASM_SIMP_TAC [IDEAL_POW_0, RING_SUB, RING_MUL, RING_1], ASM_MESON_TAC [RING_UNIT_QUOTIENT_RING_COSET, RING_UNIT_QUOTIENT_RING_IDEAL_POW, RING_IDEAL_IDEAL_POW]], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_neg r (ring_mul r s v) IN ideal_pow r m i /\
      ring_neg r (ring_mul r s v:A) IN ring_carrier r") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_NEG, RING_MUL] THEN ASM_SIMP_TAC [IN_RING_IDEAL_NEG, IN_RING_IDEAL_RMUL, RING_IDEAL_IDEAL_POW], ALL_TAC] THEN ABBREV_TAC (← q r"t0 = ring_neg r (ring_mul r s v):A") THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"f:(1->num)->A"), (← q r"b:A"), (← q r"ring_mul r d t0:A")] POLY_EVAL_TAYLOR) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"poly_deriv r f:(1->num)->A"), (← q r"b:A"), (← q r"ring_mul r d t0:A")] POLY_EVAL_TAYLOR) THEN ASM_SIMP_TAC [POLY_DERIV_IN_CARRIER, RING_MUL] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"g':A") STRIP_ASSUME_TAC) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"g:A") STRIP_ASSUME_TAC) THEN ABBREV_TAC (← q r"c = poly_eval r (poly_deriv r (poly_deriv r f)) (b:A)") THEN SUBGOAL_THEN (← q r"(c:A) IN ring_carrier r") ASSUME_TAC THENL [EXPAND_TAC "c" THEN REWRITE_TAC [POLY_EVAL], ALL_TAC] THEN MAP_EVERY EXISTS_TAC [(← q r"t0:A"), (← q r"ring_add r u (ring_add r (ring_mul r c t0)
                       (ring_mul r (ring_mul r d (ring_mul r t0 t0)) g')):A"), (← q r"ring_add r
        (ring_neg r (ring_mul r s (ring_sub r (ring_mul r u v) (ring_1 r))))
        (ring_mul r (ring_mul r t0 t0) g):A")] THEN ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL [RING_CARRIER_TAC, SUBGOAL_THEN (← q r"ring_sub r
         (ring_add r u (ring_add r (ring_mul r c t0)
                         (ring_mul r (ring_mul r d (ring_mul r t0 t0)) g')))
         u:A =
        ring_add r (ring_mul r c t0)
                   (ring_mul r (ring_mul r d (ring_mul r t0 t0)) g')") SUBST1_TAC THENL [W (fun (_, w) => tactic_of do pure (MP_TAC (← RING_RULE w))) THEN ASM_SIMP_TAC [RING_MUL], ALL_TAC] THEN MATCH_MP_TAC IN_RING_IDEAL_ADD THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN CONJ_TAC THENL [ASM_SIMP_TAC [IN_RING_IDEAL_LMUL, RING_IDEAL_IDEAL_POW], MATCH_MP_TAC IN_RING_IDEAL_RMUL THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, IN_RING_IDEAL_RMUL]], REWRITE_TAC [r1] THEN MATCH_MP_TAC IN_RING_IDEAL_ADD THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN CONJ_TAC THENL [MATCH_MP_TAC IN_RING_IDEAL_NEG THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN ASM_REWRITE_TAC [], MATCH_MP_TAC IN_RING_IDEAL_RMUL THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN ASM_REWRITE_TAC []], UNDISCH_TAC (← q r"ring_neg r (ring_mul r s v):A = t0") THEN W (fun (_, w) => tactic_of do pure (MP_TAC (← RING_RULE w))) THEN ASM_SIMP_TAC [RING_MUL], W (fun (_, w) => tactic_of do pure (MP_TAC (← RING_RULE w))) THEN ASM_SIMP_TAC [RING_MUL]])

  let HENSEL_LEMMA ← prove
    r"!r m f (a:A) d u s j k.
        ring_ideal r m /\ f IN ring_carrier(poly_ring r (:1)) /\
        a IN ring_carrier r /\ d IN ring_carrier r /\ u IN ring_carrier r /\
        ~(j = 0) /\ s IN ideal_pow r m j /\
        poly_eval r f a = ring_mul r (ring_pow r d 2) s /\
        poly_eval r (poly_deriv r f) a = ring_mul r d u /\
        ring_unit (quotient_ring r m) (ring_coset r m u)
        ==> ?t s'. t IN ideal_pow r m j /\ s' IN ideal_pow r m k /\
                   poly_eval r f (ring_add r a (ring_mul r d t)) =
                   ring_mul r (ring_pow r d 2) s'"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(m:A->bool) SUBSET ring_carrier r") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"!n. ?t u' s'.
        t IN ideal_pow r m j /\ u' IN ring_carrier r /\
        ring_unit (quotient_ring r m) (ring_coset r m u') /\
        s' IN ideal_pow r m (j + n) /\
        poly_eval r f (ring_add r a (ring_mul r d t)) =
        ring_mul r (ring_pow r d 2) s' /\
        poly_eval r (poly_deriv r f) (ring_add r a (ring_mul r d t)) =
        ring_mul r d (u':A)") MP_TAC THENL [ALL_TAC, DISCH_THEN (MP_TAC o (SPEC (← q r"k:num"))) THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"t:A"), (← q r"u':A"), (← q r"s':A")] THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"t:A"), (← q r"s':A")] THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"k:num"), (← q r"j + k:num")] IDEAL_POW_ANTIMONO) THEN ASM_REWRITE_TAC [LE_ADDR, SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC []] THEN INDUCT_TAC THENL [MAP_EVERY EXISTS_TAC [(← q r"ring_0 r:A"), (← q r"u:A"), (← q r"s:A")] THEN ASM_SIMP_TAC [ADD_CLAUSES, RING_MUL_RZERO, RING_ADD_RZERO, IN_RING_IDEAL_0, RING_IDEAL_IDEAL_POW], ALL_TAC] THEN FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"t:A") (X_CHOOSE_THEN (← q r"v:A") (X_CHOOSE_THEN (← q r"w:A") STRIP_ASSUME_TAC))) THEN SUBGOAL_THEN (← q r"(t:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_POW, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"f:(1->num)->A"), (← q r"ring_add r a (ring_mul r d t):A"), (← q r"d:A"), (← q r"v:A"), (← q r"w:A"), (← q r"j + n:num")] HENSEL_NEWTON_STEP) THEN ASM_SIMP_TAC [RING_ADD, RING_MUL] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"t':A"), (← q r"v':A"), (← q r"w':A")] THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"ring_add r t t':A"), (← q r"v':A"), (← q r"w':A")] THEN SUBGOAL_THEN (← q r"(t':A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_POW, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_add r a (ring_mul r d (ring_add r t t')):A =
    ring_add r (ring_add r a (ring_mul r d t)) (ring_mul r d t')") SUBST1_TAC THENL [W (fun (_, w) => tactic_of do pure (MP_TAC (← RING_RULE w))) THEN ASM_SIMP_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC IN_RING_IDEAL_ADD THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"j:num"), (← q r"j + n:num")] IDEAL_POW_ANTIMONO) THEN ASM_REWRITE_TAC [LE_ADD, SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [], MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"v':A"), (← q r"v:A")] RING_UNIT_QUOTIENT_RING_COSET_EQ) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"1"), (← q r"j + n:num")] IDEAL_POW_ANTIMONO) THEN ASM_SIMP_TAC [IDEAL_POW_1] THEN ANTS_TAC THENL [ASM_ARITH_TAC, REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC []], MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"j + SUC n"), (← q r"2 * (j + n)")] IDEAL_POW_ANTIMONO) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [ASM_ARITH_TAC, REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC []]])

  let HENSEL_NEWTON_STEP_SIMPLE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_sub r (ring_add r a t) a:A = t")
    prove
      r"!r m f (a:A) k.
          ring_ideal r m /\ f IN ring_carrier(poly_ring r (:1)) /\
          a IN ring_carrier r /\ poly_eval r f a IN ideal_pow r m k /\
          ring_unit (quotient_ring r m)
                    (ring_coset r m (poly_eval r (poly_deriv r f) a))
          ==> ?b. b IN ring_carrier r /\ ring_sub r b a IN ideal_pow r m k /\
                  poly_eval r f b IN ideal_pow r m (2 * k)"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"f:(1->num)->A"), (← q r"a:A"), (← q r"ring_1 r:A"), (← q r"poly_eval r (poly_deriv r f) (a:A)"), (← q r"poly_eval r f (a:A)"), (← q r"k:num")] HENSEL_NEWTON_STEP) THEN ASM_SIMP_TAC [RING_1, POLY_EVAL, RING_POW_ONE, RING_MUL_LID] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"t:A"), (← q r"u:A"), (← q r"s:A")] THEN STRIP_TAC THEN EXISTS_TAC (← q r"ring_add r a (ring_mul r (ring_1 r) t):A") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(t:A) IN ring_carrier r /\ (s:A) IN ring_carrier r") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_POW, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [RING_MUL_LID, RING_ADD, RING_1, r1])

  let HENSEL_LEMMA_POW ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_sub r (ring_add r a t) a:A = t")
    prove
      r"!r m f (a:A) j k.
          ring_ideal r m /\ f IN ring_carrier(poly_ring r (:1)) /\
          a IN ring_carrier r /\ ~(j = 0) /\
          poly_eval r f a IN ideal_pow r m j /\
          ring_unit (quotient_ring r m)
                    (ring_coset r m (poly_eval r (poly_deriv r f) a))
          ==> ?b. b IN ring_carrier r /\ ring_sub r b a IN ideal_pow r m j /\
                  poly_eval r f b IN ideal_pow r m k"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"f:(1->num)->A"), (← q r"a:A"), (← q r"ring_1 r:A"), (← q r"poly_eval r (poly_deriv r f) (a:A)"), (← q r"poly_eval r f (a:A)"), (← q r"j:num"), (← q r"k:num")] HENSEL_LEMMA) THEN ASM_SIMP_TAC [RING_1, POLY_EVAL, RING_POW_ONE, RING_MUL_LID] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"t:A"), (← q r"s:A")] THEN STRIP_TAC THEN EXISTS_TAC (← q r"ring_add r a (ring_mul r (ring_1 r) t):A") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(t:A) IN ring_carrier r /\ (s:A) IN ring_carrier r") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_POW, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [RING_MUL_LID, RING_ADD, RING_1, r1])

  let HENSEL_LEMMA_UNIQUE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"SUC i = 1 + i")
    let r10 ← RING_RULE (← q r"ring_add r b (ring_sub r c b):A = c")
    prove
      r"!r m f (b:A) c k.
          ring_ideal r m /\ f IN ring_carrier(poly_ring r (:1)) /\
          b IN ring_carrier r /\ c IN ring_carrier r /\
          ring_unit (quotient_ring r m)
                    (ring_coset r m (poly_eval r (poly_deriv r f) b)) /\
          ring_sub r b c IN m /\
          poly_eval r f b IN ideal_pow r m k /\
          poly_eval r f c IN ideal_pow r m k
          ==> ring_sub r b c IN ideal_pow r m k"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"(m:A->bool) SUBSET ring_carrier r") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"poly_eval r (poly_deriv r f) (b:A)")] RING_UNIT_QUOTIENT_RING_COSET) THEN ASM_REWRITE_TAC [POLY_EVAL] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"u:A") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"!i. i <= k ==> ring_sub r c (b:A) IN ideal_pow r m i") MP_TAC THENL [ALL_TAC, DISCH_THEN (MP_TAC o (SPEC (← q r"k:num"))) THEN REWRITE_TAC [LE_REFL] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_sub r b c = ring_neg r (ring_sub r c b):A") SUBST1_TAC THENL [W (fun (_, w) => tactic_of do pure (MP_TAC (← RING_RULE w))) THEN ASM_SIMP_TAC [], ASM_SIMP_TAC [IN_RING_IDEAL_NEG, RING_IDEAL_IDEAL_POW]]] THEN INDUCT_TAC THENL [ASM_SIMP_TAC [IDEAL_POW_0, RING_SUB], ALL_TAC] THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun z11 => (do let z12 ← (do let z13 ← (pure z11); pure (concl z13)); pure (is_imp z12))))) THEN ANTS_TAC THENL [ASM_ARITH_TAC, DISCH_TAC] THEN ASM_CASES_TAC (← q r"i = 0") THENL [ASM_SIMP_TAC [(← GSYM ONE), IDEAL_POW_1] THEN SUBGOAL_THEN (← q r"ring_sub r c b = ring_neg r (ring_sub r b c):A") SUBST1_TAC THENL [W (fun (_, w) => tactic_of do pure (MP_TAC (← RING_RULE w))) THEN ASM_SIMP_TAC [], ASM_SIMP_TAC [IN_RING_IDEAL_NEG]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"f:(1->num)->A"), (← q r"b:A"), (← q r"ring_sub r c b:A")] POLY_EVAL_TAYLOR) THEN ASM_SIMP_TAC [RING_SUB, r10] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"g:A") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"ideal_pow r m k SUBSET ideal_pow r m (SUC i) /\
      ideal_pow r m (i + i) SUBSET ideal_pow r (m:A->bool) (SUC i)") STRIP_ASSUME_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC IDEAL_POW_ANTIMONO THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sub r (ring_sub r (poly_eval r f c) (poly_eval r f b))
       (ring_mul r (ring_mul r (ring_sub r c b) (ring_sub r c b)) (g:A)) IN
      ideal_pow r m (SUC i)") ASSUME_TAC THENL [MATCH_MP_TAC IN_RING_IDEAL_SUB THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN CONJ_TAC THENL [MATCH_MP_TAC IN_RING_IDEAL_SUB THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN ASM SET_TAC [], MATCH_MP_TAC IN_RING_IDEAL_RMUL THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN FIRST_X_ASSUM (MATCH_MP_TAC o ((REWRITE_RULE [SUBSET]) o (checkM (fun th => (do if ← (do let z5 ← (q r"ideal_pow r m (SUC i):A->bool"); let z4 ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); liftExcept (rand z2)); pure (z4 == z5)) then (do let z9 ← (q r"ideal_pow r m (i + i):A->bool"); let z8 ← (do let z6 ← (do let z7 ← (pure th); pure (concl z7)); liftExcept (lhand z6)); pure (z8 == z9)) else pure false))))) THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sub r c b:A =
      ring_sub r
       (ring_mul r u
         (ring_sub r (ring_sub r (poly_eval r f c) (poly_eval r f b))
           (ring_mul r (ring_mul r (ring_sub r c b) (ring_sub r c b)) g)))
       (ring_mul r
         (ring_sub r (ring_mul r (poly_eval r (poly_deriv r f) b) u)
                     (ring_1 r))
         (ring_sub r c b))") SUBST1_TAC THENL [UNDISCH_TAC (← q r"poly_eval r f c =
        ring_add r
         (ring_add r (poly_eval r f b)
           (ring_mul r (poly_eval r (poly_deriv r f) b) (ring_sub r c b)))
         (ring_mul r (ring_mul r (ring_sub r c b) (ring_sub r c b)) (g:A))") THEN W (fun (_, w) => tactic_of do pure (MP_TAC (← RING_RULE w))) THEN ASM_SIMP_TAC [POLY_EVAL], ALL_TAC] THEN MATCH_MP_TAC IN_RING_IDEAL_SUB THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN CONJ_TAC THENL [ASM_SIMP_TAC [IN_RING_IDEAL_LMUL, RING_IDEAL_IDEAL_POW], REWRITE_TAC [r1] THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN ASM_SIMP_TAC [IDEAL_POW_1]])

  let HENSEL_LEMMA_SIMPLE ← prove
    r"!r m f (a:A) k.
        ring_ideal r m /\ f IN ring_carrier(poly_ring r (:1)) /\
        a IN ring_carrier r /\ poly_eval r f a IN m /\
        ring_unit (quotient_ring r m)
                  (ring_coset r m (poly_eval r (poly_deriv r f) a))
        ==> (?b. b IN ring_carrier r /\ ring_sub r b a IN m /\
                 poly_eval r f b IN ideal_pow r m k) /\
            (!b c. b IN ring_carrier r /\ c IN ring_carrier r /\
                   ring_sub r b a IN m /\ ring_sub r c a IN m /\
                   poly_eval r f b IN ideal_pow r m k /\
                   poly_eval r f c IN ideal_pow r m k
                   ==> ring_sub r b c IN ideal_pow r m k)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"f:(1->num)->A"), (← q r"a:A"), (← q r"1"), (← q r"k:num")] HENSEL_LEMMA_POW) THEN ASM_SIMP_TAC [IDEAL_POW_1, ARITH_EQ], REPEAT STRIP_TAC THEN MATCH_MP_TAC HENSEL_LEMMA_UNIQUE THEN EXISTS_TAC (← q r"f:(1->num)->A") THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"poly_eval r (poly_deriv r f) (b:A)"), (← q r"poly_eval r (poly_deriv r f) (a:A)")] RING_UNIT_QUOTIENT_RING_COSET_EQ) THEN ASM_REWRITE_TAC [POLY_EVAL] THEN DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC POLY_EVAL_SUB_IN_IDEAL THEN ASM_SIMP_TAC [POLY_DERIV_IN_CARRIER], SUBGOAL_THEN (← q r"ring_sub r b c = ring_sub r (ring_sub r b a) (ring_sub r c a):A") SUBST1_TAC THENL [W (fun (_, w) => tactic_of do pure (MP_TAC (← RING_RULE w))) THEN ASM_SIMP_TAC [], ASM_SIMP_TAC [IN_RING_IDEAL_SUB]]]])

  let HENSEL_LEMMA_NEWTON ← prove
    r"!r m f (a:A) s k.
        ring_ideal r m /\ f IN ring_carrier(poly_ring r (:1)) /\
        a IN ring_carrier r /\ s IN m /\
        poly_eval r f a =
        ring_mul r (ring_pow r (poly_eval r (poly_deriv r f) a) 2) s
        ==> ?t s'. t IN m /\ s' IN ideal_pow r m k /\
                   poly_eval r f
                    (ring_add r a
                      (ring_mul r (poly_eval r (poly_deriv r f) a) t)) =
                   ring_mul r (ring_pow r (poly_eval r (poly_deriv r f) a) 2)
                              s'"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"f:(1->num)->A"), (← q r"a:A"), (← q r"poly_eval r (poly_deriv r f) (a:A)"), (← q r"ring_1 r:A"), (← q r"s:A"), (← q r"1"), (← q r"k:num")] HENSEL_LEMMA) THEN ASM_SIMP_TAC [IDEAL_POW_1, ARITH_EQ, RING_1, POLY_EVAL, RING_MUL_RID] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_UNIT_QUOTIENT_RING_COSET, RING_1] THEN EXISTS_TAC (← q r"ring_1 r:A") THEN ASM_SIMP_TAC [RING_MUL_LID, RING_1, RING_SUB_REFL, IN_RING_IDEAL_0])

  let HENSEL_ROOT_UNIQUE ← prove
    r"!r m f (b:A) c.
        ring_ideal r m /\
        (!x. (!k. x IN ideal_pow r m k) ==> x = ring_0 r) /\
        f IN ring_carrier(poly_ring r (:1)) /\
        b IN ring_carrier r /\ c IN ring_carrier r /\
        ring_unit (quotient_ring r m)
                  (ring_coset r m (poly_eval r (poly_deriv r f) b)) /\
        ring_sub r b c IN m /\
        poly_eval r f b = ring_0 r /\ poly_eval r f c = ring_0 r
        ==> b = c"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"b:A"), (← q r"c:A")] RING_SUB_EQ_0) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN FIRST_X_ASSUM (MATCH_MP_TAC o (checkM (fun z1 => (do let z2 ← (do let z3 ← (pure z1); pure (concl z3)); pure (is_forall z2))))) THEN X_GEN_TAC (← q r"k:num") THEN MATCH_MP_TAC HENSEL_LEMMA_UNIQUE THEN EXISTS_TAC (← q r"f:(1->num)->A") THEN ASM_SIMP_TAC [IN_RING_IDEAL_0, RING_IDEAL_IDEAL_POW])

  let POLY_EVAL_DERIV_VAR_POW_SUB_CONST ← prove
    r"!r n c:A.
        c IN ring_carrier r
        ==> poly_sub r (poly_pow r (poly_var r one) n) (poly_const r c) IN
            ring_carrier(poly_ring r (:1)) /\
            !x. x IN ring_carrier r
                ==> poly_eval r (poly_sub r (poly_pow r (poly_var r one) n)
                                            (poly_const r c)) x =
                    ring_sub r (ring_pow r x n) c /\
                    poly_eval r (poly_deriv r
                                  (poly_sub r (poly_pow r (poly_var r one) n)
                                              (poly_const r c))) x =
                    ring_mul r (ring_of_num r n) (ring_pow r x (n - 1))"
    (REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [(← GSYM RING_POLYNOMIAL)] THEN CONJ_TAC THENL [ASM_SIMP_TAC [RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_POW, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_CONST], GEN_TAC THEN DISCH_TAC] THEN ASM_SIMP_TAC [RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_POW, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_CONST, POLY_EVAL_SUB, POLY_EVAL_POW, POLY_EVAL_VAR, POLY_EVAL_CONST] THEN ASM_SIMP_TAC [POLY_DERIV_SUB, RING_POLYNOMIAL_IMP_POWERSERIES, RING_POLYNOMIAL_POW, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_CONST, POLY_DERIV_VAR_POW, POLY_DERIV_CONST] THEN ASM_SIMP_TAC [POLY_EVAL_SUB, RING_POLYNOMIAL_MUL, RING_POLYNOMIAL_CONST, RING_POLYNOMIAL_POW, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_0, RING_OF_NUM, POLY_EVAL_MUL, POLY_EVAL_CONST, POLY_EVAL_POW, POLY_EVAL_VAR, POLY_EVAL_0, RING_SUB_RZERO, RING_MUL, RING_POW])

  let POWER_RESIDUE_MODULO_IDEAL_POW ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"n = 0 ==> n - 1 = 0")
    prove
      r"!r m n (a:A) k.
          ring_ideal r m /\ a IN ring_carrier r /\
          ring_unit (quotient_ring r m) (ring_coset r m (ring_of_num r n)) /\
          ring_unit (quotient_ring r m) (ring_coset r m a)
          ==> ((?x. x IN ring_carrier r /\
                    ring_sub r (ring_pow r x n) a IN ideal_pow r m k) <=>
               k = 0 \/
               (?x. x IN ring_carrier r /\ ring_sub r (ring_pow r x n) a IN m))"
      (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"k = 0") THENL [ASM_REWRITE_TAC [IDEAL_POW_0] THEN EXISTS_TAC (← q r"ring_0 r:A") THEN ASM_SIMP_TAC [RING_SUB, RING_POW, RING_0], ASM_REWRITE_TAC []] THEN EQ_TAC THEN DISCH_THEN (X_CHOOSE_THEN (← q r"x:A") STRIP_ASSUME_TAC) THENL [EXISTS_TAC (← q r"x:A") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"1"), (← q r"k:num")] IDEAL_POW_ANTIMONO) THEN ASM_SIMP_TAC [IDEAL_POW_1, RING_IDEAL_IMP_SUBSET, LE_1] THEN REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"poly_sub r (poly_pow r (poly_var r one) n) (poly_const r (a:A))"), (← q r"x:A"), (← q r"k:num")] HENSEL_LEMMA_SIMPLE) THEN ASM_SIMP_TAC [POLY_EVAL_DERIV_VAR_POW_SUB_CONST] THEN ANTS_TAC THENL [ALL_TAC, DISCH_THEN ((X_CHOOSE_THEN (← q r"y:A") STRIP_ASSUME_TAC) o CONJUNCT1) THEN EXISTS_TAC (← q r"y:A") THEN UNDISCH_TAC (← q r"poly_eval r (poly_sub r (poly_pow r (poly_var r one) n)
                               (poly_const r a)) (y:A) IN ideal_pow r m k") THEN ASM_SIMP_TAC [POLY_EVAL_DERIV_VAR_POW_SUB_CONST]] THEN ASM_SIMP_TAC [RING_UNIT_QUOTIENT_RING_COSET_MUL, RING_OF_NUM, RING_POW, RING_UNIT_QUOTIENT_RING_COSET_POW] THEN SUBGOAL_THEN (← q r"ring_unit (quotient_ring r m) (ring_coset r m (ring_pow r (x:A) n))") MP_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"ring_pow r x n:A"), (← q r"a:A")] RING_UNIT_QUOTIENT_RING_COSET_EQ) THEN ASM_SIMP_TAC [RING_POW], ASM_SIMP_TAC [RING_UNIT_QUOTIENT_RING_COSET_POW] THEN MESON_TAC [r1]])

  let INTEGER_RING_IDEAL_POW_SING ← prove
    r"!n k. ideal_pow integer_ring (ideal_generated integer_ring {n}) k =
         {x | n pow k divides x}"
    (SIMP_TAC [IDEAL_POW_PRINCIPAL, INTEGER_RING, IN_UNIV, INTEGER_RING_POW, INTEGER_RING_IDEAL_GENERATED_SING])

  let RING_UNIT_QUOTIENT_INTEGER_RING ← prove
    r"!n x. ring_unit
          (quotient_ring integer_ring (ideal_generated integer_ring {n}))
          (ring_coset integer_ring (ideal_generated integer_ring {n}) x) <=>
         coprime(x,n)"
    (SIMP_TAC [RING_UNIT_QUOTIENT_RING_COSET, RING_IDEAL_IDEAL_GENERATED, INTEGER_RING, IN_UNIV, INTEGER_RING_IDEAL_GENERATED_SING, IN_ELIM_THM, INTEGER_RING_SUB] THEN INTEGER_TAC)

  let HENSEL_LEMMA_INTEGER ← prove
    r"!f (n:int) a k.
        f IN ring_carrier(poly_ring integer_ring (:1)) /\
        (poly_eval integer_ring f a == &0) (mod n) /\
        coprime(poly_eval integer_ring (poly_deriv integer_ring f) a,n)
        ==> (?b. (b == a) (mod n) /\
                 (poly_eval integer_ring f b == &0) (mod (n pow k))) /\
            (!b c. (b == a) (mod n) /\ (c == a) (mod n) /\
                   (poly_eval integer_ring f b == &0) (mod (n pow k)) /\
                   (poly_eval integer_ring f c == &0) (mod (n pow k))
                   ==> (b == c) (mod (n pow k)))"
    (REPEAT GEN_TAC THEN REWRITE_TAC [cong, int_mod, INT_SUB_RZERO] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"ideal_generated integer_ring {n:int}"), (← q r"f:(1->num)->int"), (← q r"a:int"), (← q r"k:num")] HENSEL_LEMMA_SIMPLE) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, RING_UNIT_QUOTIENT_INTEGER_RING, INTEGER_RING_IDEAL_POW_SING, INTEGER_RING_IDEAL_GENERATED_SING, INTEGER_RING, IN_UNIV, IN_ELIM_THM, INTEGER_RING_SUB])

  let INT_POWER_RESIDUE_MODULO_POWER ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← INTEGER_RULE (← q r"!a b:int. coprime(a,b) <=> coprime(b,a)")
    prove
      r"!n:int d a k.
          coprime(&d,n) /\ coprime(n,a)
          ==> ((?x. (x pow d == a) (mod (n pow k))) <=>
               k = 0 \/ ?x. (x pow d == a) (mod n))"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"ideal_generated integer_ring {n:int}"), (← q r"d:num"), (← q r"a:int"), (← q r"k:num")] POWER_RESIDUE_MODULO_IDEAL_POW) THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, RING_UNIT_QUOTIENT_INTEGER_RING, INTEGER_RING_IDEAL_POW_SING, INTEGER_RING_IDEAL_GENERATED_SING, INTEGER_RING, IN_UNIV, IN_ELIM_THM, INTEGER_RING_SUB, INTEGER_RING_OF_NUM, INTEGER_RING_POW] THEN ANTS_TAC THENL [ASM_MESON_TAC [r1], REWRITE_TAC [cong, int_mod]])

  let COEFF_POLY_MUL_IN_IDEAL_POW ← prove
    r"!r m (p:(1->num)->A) q a b i.
        ring_ideal r m /\
        (!i. coeff i p IN ideal_pow r m a) /\
        (!i. coeff i q IN ideal_pow r m b)
        ==> coeff i (poly_mul r p q) IN ideal_pow r m (a + b)"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [COEFF_POLY_MUL] THEN MATCH_MP_TAC IN_RING_IDEAL_SUM THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET])

  let HENSEL_FACTORIZATION_STEP ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"k = k + 0")
    let r2 ← ARITH_RULE (← q r"k = 0 + k")
    let r3 ← ARITH_RULE (← q r"k = k + 0")
    let r4 ← RING_RULE (← q r"ring_sub R f (ring_mul R G H) = w /\
      ring_add R (ring_mul R q g) dl = ring_mul R t w
      ==> ring_sub R f (ring_mul R (ring_add R G dl)
            (ring_add R H (ring_add R (ring_mul R s w) (ring_mul R q H)))) =
          ring_sub R
           (ring_sub R
             (ring_neg R (ring_mul R
               (ring_sub R (ring_add R (ring_mul R s G) (ring_mul R t H))
                           (ring_1 R)) w))
             (ring_mul R (ring_mul R q H) (ring_sub R G g)))
           (ring_mul R dl (ring_add R (ring_mul R s w)
                                      (ring_mul R q (H:(1->num)->A))))")
    let r8 ← ARITH_RULE (← q r"k = k + 0")
    let r9 ← ARITH_RULE (← q r"k = 0 + k")
    let r10 ← RING_RULE (← q r"ring_sub R (ring_add R H (ring_add R x y)) H =
      ring_add R x (y:(1->num)->A)")
    let r11 ← RING_RULE (← q r"ring_sub R (ring_add R G dl) G = dl:(1->num)->A")
    prove
      r"!r m f g s t G H k.
          ring_ideal r m /\ ~(k = 0) /\
          f IN ring_carrier(poly_ring r (:1)) /\
          g IN ring_carrier(poly_ring r (:1)) /\
          s IN ring_carrier(poly_ring r (:1)) /\
          t IN ring_carrier(poly_ring r (:1)) /\
          G IN ring_carrier(poly_ring r (:1)) /\
          H IN ring_carrier(poly_ring r (:1)) /\
          ring_unit r (coeff (poly_deg r g) g) /\
          (!i. coeff i (ring_sub (poly_ring r (:1))
                         (ring_add (poly_ring r (:1))
                           (ring_mul (poly_ring r (:1)) s G)
                           (ring_mul (poly_ring r (:1)) t H))
                         (ring_1 (poly_ring r (:1)))) IN m) /\
          (!i. coeff i (ring_sub (poly_ring r (:1)) G g) IN m) /\
          (!i. coeff i (ring_sub (poly_ring r (:1)) f
                         (ring_mul (poly_ring r (:1)) G H)) IN ideal_pow r m k)
          ==> ?G' H'.
                G' IN ring_carrier(poly_ring r (:1)) /\
                H' IN ring_carrier(poly_ring r (:1)) /\
                (!i. coeff i (ring_sub (poly_ring r (:1)) G' G)
                     IN ideal_pow r m k) /\
                (!i. coeff i (ring_sub (poly_ring r (:1)) H' H)
                     IN ideal_pow r m k) /\
                (!i. poly_deg r g <= i ==> coeff i G' = coeff i G) /\
                (!i. coeff i (ring_sub (poly_ring r (:1)) f
                               (ring_mul (poly_ring r (:1)) G' H'))
                     IN ideal_pow r (m:A->bool) (k + 1))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_sub (poly_ring r (:1)) f (ring_mul (poly_ring r (:1)) G H)
      IN ring_carrier(poly_ring r (:1)):((1->num)->A)->bool") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_SUB, RING_MUL], ALL_TAC] THEN ABBREV_TAC (← q r"w = ring_sub (poly_ring r (:1)) f
           (ring_mul (poly_ring r (:1)) G H):(1->num)->A") THEN SUBGOAL_THEN (← q r"!p:(1->num)->A. p IN ring_carrier(poly_ring r (:1))
                      ==> !i. coeff i p IN ideal_pow r m 0") (LABEL_TAC "car") THENL [REWRITE_TAC [IDEAL_POW_0] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC COEFF_IN_CARRIER_ALT THEN ASM_REWRITE_TAC [RING_POLYNOMIAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"!p q:(1->num)->A a b i.
          (!j. coeff j p IN ideal_pow r m a) /\
          (!j. coeff j q IN ideal_pow r m b)
          ==> coeff i (ring_mul (poly_ring r (:1)) p q) IN
              ideal_pow r m (a + b)") (LABEL_TAC "mul") THENL [REWRITE_TAC [POLY_RING_CLAUSES] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC COEFF_POLY_MUL_IN_IDEAL_POW THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. coeff i (ring_mul (poly_ring r (:1)) t (w:(1->num)->A)) IN
          ideal_pow r m (0 + k)") MP_TAC THENL [GEN_TAC THEN USE_THEN "mul" MATCH_MP_TAC THEN ASM_SIMP_TAC [], REWRITE_TAC [ADD_CLAUSES] THEN DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_pow r m k:A->bool"), (← q r"ring_mul (poly_ring r (:1)) t w:(1->num)->A"), (← q r"g:(1->num)->A")] POLY_DIVISION_COEFF_IDEAL) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, RING_MUL] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"q:(1->num)->A"), (← q r"dl:(1->num)->A")] THEN DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN MAP_EVERY EXISTS_TAC [(← q r"ring_add (poly_ring r (:1)) G dl:(1->num)->A"), (← q r"ring_add (poly_ring r (:1)) H
        (ring_add (poly_ring r (:1)) (ring_mul (poly_ring r (:1)) s w)
                                     (ring_mul (poly_ring r (:1)) q H))
        :(1->num)->A")] THEN ASM_SIMP_TAC [RING_ADD, RING_MUL] THEN REPEAT CONJ_TAC THENL [ASM_SIMP_TAC [r11], ASM_SIMP_TAC [RING_MUL, r10] THEN REWRITE_TAC [POLY_RING_CLAUSES, COEFF_POLY_ADD] THEN GEN_TAC THEN MATCH_MP_TAC IN_RING_IDEAL_ADD THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN REWRITE_TAC [POLY_CLAUSES] THEN CONJ_TAC THENL [SUBST1_TAC r9, SUBST1_TAC r8] THEN USE_THEN "mul" MATCH_MP_TAC THEN ASM_SIMP_TAC [], X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN REWRITE_TAC [POLY_RING_CLAUSES, COEFF_POLY_ADD] THEN SUBGOAL_THEN (← q r"coeff i (dl:(1->num)->A) = ring_0 r") SUBST1_TAC THENL [FIRST_X_ASSUM (DISJ_CASES_TAC o (checkM (fun z5 => (do let z6 ← (do let z7 ← (pure z5); pure (concl z7)); pure (is_disj z6))))) THENL [MATCH_MP_TAC COEFF_ABOVE_DEG THEN ASM_REWRITE_TAC [RING_POLYNOMIAL] THEN ASM_ARITH_TAC, ASM_REWRITE_TAC [POLY_RING_CLAUSES, COEFF_POLY_0]], MATCH_MP_TAC RING_ADD_RZERO THEN MATCH_MP_TAC COEFF_IN_CARRIER_ALT THEN ASM_REWRITE_TAC [RING_POLYNOMIAL]], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sub (poly_ring r (:1)) (f:(1->num)->A)
       (ring_mul (poly_ring r (:1)) (ring_add (poly_ring r (:1)) G dl)
         (ring_add (poly_ring r (:1)) H
           (ring_add (poly_ring r (:1)) (ring_mul (poly_ring r (:1)) s w)
                                        (ring_mul (poly_ring r (:1)) q H)))) =
      ring_sub (poly_ring r (:1))
       (ring_sub (poly_ring r (:1))
         (ring_neg (poly_ring r (:1))
           (ring_mul (poly_ring r (:1))
             (ring_sub (poly_ring r (:1))
               (ring_add (poly_ring r (:1))
                 (ring_mul (poly_ring r (:1)) s G)
                 (ring_mul (poly_ring r (:1)) t H))
               (ring_1 (poly_ring r (:1)))) w))
         (ring_mul (poly_ring r (:1)) (ring_mul (poly_ring r (:1)) q H)
                   (ring_sub (poly_ring r (:1)) G g)))
       (ring_mul (poly_ring r (:1)) dl
         (ring_add (poly_ring r (:1)) (ring_mul (poly_ring r (:1)) s w)
                                      (ring_mul (poly_ring r (:1)) q H)))") SUBST1_TAC THENL [MATCH_MP_TAC (← REWRITE_RULE [IMP_IMP] r4) THEN ASM_SIMP_TAC [], ALL_TAC] THEN REWRITE_TAC [POLY_RING_CLAUSES, COEFF_POLY_SUB, COEFF_POLY_NEG] THEN REWRITE_TAC [POLY_CLAUSES] THEN GEN_TAC THEN MATCH_MP_TAC IN_RING_IDEAL_SUB THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN CONJ_TAC THENL [MATCH_MP_TAC IN_RING_IDEAL_SUB THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN CONJ_TAC THENL [MATCH_MP_TAC IN_RING_IDEAL_NEG THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN ONCE_REWRITE_TAC [ADD_SYM] THEN USE_THEN "mul" MATCH_MP_TAC THEN ASM_SIMP_TAC [IDEAL_POW_1], USE_THEN "mul" MATCH_MP_TAC THEN ASM_SIMP_TAC [IDEAL_POW_1] THEN SUBST1_TAC r3 THEN GEN_TAC THEN USE_THEN "mul" MATCH_MP_TAC THEN ASM_SIMP_TAC []], MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"k + 1:num"), (← q r"k + k:num")] IDEAL_POW_ANTIMONO) THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET] THEN ANTS_TAC THENL [ASM_ARITH_TAC, REWRITE_TAC [SUBSET]] THEN DISCH_THEN MATCH_MP_TAC THEN USE_THEN "mul" MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [POLY_RING_CLAUSES, COEFF_POLY_ADD] THEN GEN_TAC THEN MATCH_MP_TAC IN_RING_IDEAL_ADD THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN REWRITE_TAC [POLY_CLAUSES] THEN CONJ_TAC THENL [SUBST1_TAC r2, SUBST1_TAC r1] THEN USE_THEN "mul" MATCH_MP_TAC THEN ASM_SIMP_TAC []])

  -- @@RETURN BEGIN
  return { RING_UNIT_QUOTIENT_RING_IDEAL_POW, HENSEL_NEWTON_STEP, HENSEL_LEMMA,
           HENSEL_NEWTON_STEP_SIMPLE, HENSEL_LEMMA_POW, HENSEL_LEMMA_UNIQUE,
           HENSEL_LEMMA_SIMPLE, HENSEL_LEMMA_NEWTON, HENSEL_ROOT_UNIQUE,
           POLY_EVAL_DERIV_VAR_POW_SUB_CONST, POWER_RESIDUE_MODULO_IDEAL_POW,
           INTEGER_RING_IDEAL_POW_SING, RING_UNIT_QUOTIENT_INTEGER_RING,
           HENSEL_LEMMA_INTEGER, INT_POWER_RESIDUE_MODULO_POWER,
           COEFF_POLY_MUL_IN_IDEAL_POW, HENSEL_FACTORIZATION_STEP }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- hensel.ml phrases from line 803 to 803                                 -/
/- ---------------------------------------------------------------------- -/

structure Hensel02 where
  -- @@FIELDS
  HENSEL_LEMMA_FACTORIZATION : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupHensel02 [HolBase] (D : HenselDeps) (BHensel01 : Hensel01) :
    ExceptT String IO Hensel02 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, INDUCT_TAC, RING_RULE, .. } := D
  let { ADD_CLAUSES, ADD_EQ_0, ARITH_EQ, COEFF_ABOVE_DEG, COEFF_POLY_0, COEFF_POLY_ADD,
        COEFF_POLY_SUB, CONTRAPOS_THM, IDEAL_POW_1, IDEAL_POW_ANTIMONO, IN_ELIM_THM,
        IN_RING_IDEAL_0, IN_RING_IDEAL_ADD, IN_RING_IDEAL_LMUL, LEFT_IMP_EXISTS_THM,
        LE_REFL, LT_IMP_LE, MONO_EXISTS, NOT_LT, POLY_CLAUSES, POLY_DEG_0,
        POLY_DEG_EQ_FROM_LE, POLY_DEG_LE_COEFF_EQ, POLY_RING_CLAUSES, POLY_TOP_EQ_0,
        RING_1, RING_ADD, RING_IDEAL_IMP_SUBSET, RING_IDEAL_POLY_COEFF, RING_MUL,
        RING_POLYNOMIAL, RING_SUB, RING_SUB_REFL, SUBSET, .. } := D.core1
  let { HENSEL_FACTORIZATION_STEP, .. } := BHensel01
  -- @@SCOPE END

  let HENSEL_LEMMA_FACTORIZATION ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_sub R H' h =
          ring_add R (ring_sub R H' H) (ring_sub R H (h:(1->num)->A))")
    let r2 ← RING_RULE (← q r"ring_sub R G' g =
          ring_add R (ring_sub R G' G) (ring_sub R G (g:(1->num)->A))")
    let r3 ← ARITH_RULE (← q r"SUC n + 1 = (n + 1) + 1")
    let r4 ← RING_RULE (← q r"ring_sub R (ring_add R (ring_mul R s G) (ring_mul R t H))
                     (ring_1 R) =
          ring_add R
           (ring_sub R (ring_add R (ring_mul R s g) (ring_mul R t h))
                       (ring_1 R))
           (ring_add R (ring_mul R s (ring_sub R G g))
                       (ring_mul R t (ring_sub R H (h:(1->num)->A))))")
    prove
      r"!r m f g h s t k.
          ring_ideal r m /\
          f IN ring_carrier(poly_ring r (:1)) /\
          g IN ring_carrier(poly_ring r (:1)) /\
          h IN ring_carrier(poly_ring r (:1)) /\
          s IN ring_carrier(poly_ring r (:1)) /\
          t IN ring_carrier(poly_ring r (:1)) /\
          ring_unit r (coeff (poly_deg r g) g) /\
          (!i. ring_sub r (coeff i f) (coeff i (poly_mul r g h)) IN m) /\
          (!i. ring_sub r (coeff i (poly_add r (poly_mul r s g)
                                               (poly_mul r t h)))
                          (coeff i (poly_1 r)) IN m)
          ==> ?G H. G IN ring_carrier(poly_ring r (:1)) /\
                    H IN ring_carrier(poly_ring r (:1)) /\
                    poly_deg r G = poly_deg r g /\
                    (!i. poly_deg r g <= i ==> coeff i G = coeff i g) /\
                    (!i. ring_sub r (coeff i G) (coeff i g) IN m) /\
                    (!i. ring_sub r (coeff i H) (coeff i h) IN m) /\
                    (!i. ring_sub r (coeff i f) (coeff i (poly_mul r G H)) IN
                         ideal_pow r (m:A->bool) k)"
      (REPEAT GEN_TAC THEN REWRITE_TAC [(← GSYM COEFF_POLY_SUB), POLY_CLAUSES] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool")] RING_IDEAL_POLY_COEFF) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (LABEL_TAC "id") THEN SUBGOAL_THEN (← q r"!n p:(1->num)->A i.
          (!j. coeff j p IN ideal_pow r m (n + 1)) ==> coeff i p IN m") (LABEL_TAC "low") THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"1"), (← q r"n + 1:num")] IDEAL_POW_ANTIMONO) THEN ASM_SIMP_TAC [IDEAL_POW_1, RING_IDEAL_IMP_SUBSET] THEN ANTS_TAC THENL [ARITH_TAC, REWRITE_TAC [SUBSET]] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!n. ?G H:(1->num)->A.
                G IN ring_carrier(poly_ring r (:1)) /\
                H IN ring_carrier(poly_ring r (:1)) /\
                (!i. coeff i (ring_sub (poly_ring r (:1)) G g) IN m) /\
                (!i. coeff i (ring_sub (poly_ring r (:1)) H h) IN m) /\
                (!i. poly_deg r g <= i ==> coeff i G = coeff i g) /\
                (!i. coeff i (ring_sub (poly_ring r (:1)) f
                               (ring_mul (poly_ring r (:1)) G H)) IN
                     ideal_pow r m (n + 1))") MP_TAC THENL [INDUCT_TAC THENL [MAP_EVERY EXISTS_TAC [(← q r"g:(1->num)->A"), (← q r"h:(1->num)->A")] THEN ASM_SIMP_TAC [ADD_CLAUSES, IDEAL_POW_1, RING_SUB_REFL] THEN REWRITE_TAC [POLY_RING_CLAUSES, COEFF_POLY_0] THEN ASM_SIMP_TAC [IN_RING_IDEAL_0], ALL_TAC] THEN FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"G:(1->num)->A") (X_CHOOSE_THEN (← q r"H:(1->num)->A") STRIP_ASSUME_TAC)) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"f:(1->num)->A"), (← q r"g:(1->num)->A"), (← q r"s:(1->num)->A"), (← q r"t:(1->num)->A"), (← q r"G:(1->num)->A"), (← q r"H:(1->num)->A"), (← q r"n + 1:num")] HENSEL_FACTORIZATION_STEP) THEN ASM_REWRITE_TAC [ADD_EQ_0, ARITH_EQ] THEN ANTS_TAC THENL [SUBGOAL_THEN (← q r"ring_sub (poly_ring r (:1))
           (ring_add (poly_ring r (:1)) (ring_mul (poly_ring r (:1)) s G)
                                        (ring_mul (poly_ring r (:1)) t H))
           (ring_1 (poly_ring r (:1))) IN
          {p | p IN ring_carrier(poly_ring r (:1)) /\
               !i. coeff i p IN (m:A->bool)}") (fun th => MP_TAC th THEN SIMP_TAC [IN_ELIM_THM]) THEN SUBGOAL_THEN (← q r"ring_sub (poly_ring r (:1))
           (ring_add (poly_ring r (:1)) (ring_mul (poly_ring r (:1)) s G)
                                        (ring_mul (poly_ring r (:1)) t H))
           (ring_1 (poly_ring r (:1))) =
          ring_add (poly_ring r (:1))
           (ring_sub (poly_ring r (:1))
             (ring_add (poly_ring r (:1)) (ring_mul (poly_ring r (:1)) s g)
                                          (ring_mul (poly_ring r (:1)) t h))
             (ring_1 (poly_ring r (:1))))
           (ring_add (poly_ring r (:1))
             (ring_mul (poly_ring r (:1)) s (ring_sub (poly_ring r (:1)) G g))
             (ring_mul (poly_ring r (:1)) t
               (ring_sub (poly_ring r (:1)) H (h:(1->num)->A))))") SUBST1_TAC THENL [MATCH_MP_TAC r4 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MATCH_MP_TAC IN_RING_IDEAL_ADD THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [REWRITE_TAC [IN_ELIM_THM] THEN ASM_SIMP_TAC [RING_SUB, RING_ADD, RING_MUL, RING_1], MATCH_MP_TAC IN_RING_IDEAL_ADD THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THEN MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN ASM_SIMP_TAC [RING_SUB]], ALL_TAC] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"G':(1->num)->A"), (← q r"H':(1->num)->A")] THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"G':(1->num)->A"), (← q r"H':(1->num)->A")] THEN ASM_SIMP_TAC [r3] THEN CONJ_TAC THEN X_GEN_TAC (← q r"i:num") THENL [SUBGOAL_THEN (← q r"ring_sub (poly_ring r (:1)) G' g =
          ring_add (poly_ring r (:1)) (ring_sub (poly_ring r (:1)) G' G)
                   (ring_sub (poly_ring r (:1)) G (g:(1->num)->A))") SUBST1_TAC THENL [MATCH_MP_TAC r2 THEN ASM_REWRITE_TAC [], ALL_TAC], SUBGOAL_THEN (← q r"ring_sub (poly_ring r (:1)) H' h =
          ring_add (poly_ring r (:1)) (ring_sub (poly_ring r (:1)) H' H)
                   (ring_sub (poly_ring r (:1)) H (h:(1->num)->A))") SUBST1_TAC THENL [MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC [], ALL_TAC]] THEN REWRITE_TAC [POLY_RING_CLAUSES, COEFF_POLY_ADD] THEN REWRITE_TAC [POLY_CLAUSES] THEN MATCH_MP_TAC IN_RING_IDEAL_ADD THEN ASM_REWRITE_TAC [] THEN USE_THEN "low" MATCH_MP_TAC THEN EXISTS_TAC (← q r"n:num") THEN ASM_REWRITE_TAC [], DISCH_THEN (MP_TAC o (SPEC (← q r"k:num"))) THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"G:(1->num)->A") THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"H:(1->num)->A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ALL_TAC, GEN_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"k:num"), (← q r"k + 1:num")] IDEAL_POW_ANTIMONO) THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET] THEN ANTS_TAC THENL [ARITH_TAC, REWRITE_TAC [SUBSET]] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC []] THEN SUBGOAL_THEN (← q r"poly_deg r (G:(1->num)->A) <= poly_deg r (g:(1->num)->A)") ASSUME_TAC THENL [ASM_SIMP_TAC [POLY_DEG_LE_COEFF_EQ, RING_POLYNOMIAL] THEN X_GEN_TAC (← q r"d:num") THEN REWRITE_TAC [(← GSYM NOT_LT), CONTRAPOS_THM] THEN DISCH_TAC THEN ASM_SIMP_TAC [LT_IMP_LE] THEN MATCH_MP_TAC COEFF_ABOVE_DEG THEN ASM_REWRITE_TAC [RING_POLYNOMIAL], ALL_TAC] THEN ASM_CASES_TAC (← q r"coeff (poly_deg r g) (g:(1->num)->A) = ring_0 r") THENL [SUBGOAL_THEN (← q r"poly_deg r (g:(1->num)->A) = 0") MP_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"g:(1->num)->A")] POLY_TOP_EQ_0) THEN ASM_REWRITE_TAC [RING_POLYNOMIAL] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [POLY_DEG_0], ASM_ARITH_TAC], MATCH_MP_TAC POLY_DEG_EQ_FROM_LE THEN ASM_SIMP_TAC [RING_POLYNOMIAL, LE_REFL]]])

  -- @@RETURN BEGIN
  return { HENSEL_LEMMA_FACTORIZATION }
  -- @@RETURN END

end HolANT.Hensel
