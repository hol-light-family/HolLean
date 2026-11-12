/- ========================================================================= -/
/- ANT: Free algebras                                                      -/
/- ========================================================================= -/
/- File: HolANT/TraceForm.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/trace_form.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/anttraceformdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/products.ml, ANT/algmisc.ml, Library/isum.ml, ANT/integral.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/discriminant.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.TraceForm fills them).

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
import HolLibrary.Products
import HolANT.Algmisc
import HolLibrary.Isum
import HolANT.Integral
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolANT.IdealArith
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.IdealNorm
import HolANT.RingOfIntegers
import HolANT.NormIndex
import HolANT.Discriminant

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.Algmisc
open HolANT.Integral
open HolANT.Zlattice
open HolANT.Numfield
open HolANT.IdealArith
open HolANT.Dedekind
open HolANT.DedekindStruct
open HolANT.IdealNorm
open HolANT.RingOfIntegers
open HolANT.NormIndex
open HolANT.Discriminant

namespace HolANT.TraceForm

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD_SUB2 ALGEBRA_TRACE_FREE_BASIS ALGEBRA_TRACE_NORM_HOMOMORPHIC_IMAGE
   BASIS_COORDINATES BASIS_COORDINATES_EXPAND BASIS_COORDINATES_IN_CARRIER
   BASIS_COORDINATES_UNIQUE COND_RAND EQ_TRANS EXTENSION_DEGREE_ISOMORPHISM
   FINITE_EXTENSION_ISOMORPHISM FINITE_NUMSEG_LT FORALL_PAIR_THM
   FREE_BASIS_INDEPENDENT FREE_BASIS_IN_CARRIER FUN_EQ_THM IN_CROSS IN_ELIM_THM
   IN_IMAGE ISOMORPHIC_RING_FIELDNESS I_THM MULT_CLAUSES
   NUMBER_FIELD_DISCRIMINANT_BASIS NUMBER_FIELD_IMP_FIELD PAIR_EQ
   PRIME_SUBFIELD_TOWER_LAW PROD_RING RING_0 RING_ADD_LZERO RING_ADD_RZERO
   RING_DET_EQ RING_HOMOMORPHISM_0 RING_HOMOMORPHISM_COMPOSE RING_HOMOMORPHISM_I
   RING_HOMOMORPHISM_INTEGER_RING_OF_INT RING_HOMOMORPHISM_IN_CARRIER
   RING_HOMOMORPHISM_MUL RING_HOMOMORPHISM_PAIRED RING_HOMOMORPHISM_RING_OF_INT
   RING_HOMOMORPHISM_SUM_MUL RING_ISOMORPHISM RING_ISOMORPHISM_IMP_HOMOMORPHISM
   RING_ISOMORPHISM_RING_OF_INTEGERS RING_MUL RING_MUL_RZERO RING_OF_INTEGERS
   RING_OF_INTEGERS_FREE RING_SUM RING_SUM_EQ RING_SUM_EQ_0
   RING_SUM_NUMSEG_LT_ADD RING_SUM_PROD_RING basis_discriminant free_basis
   isomorphic_ring mul_matrix number_field o_DEF o_THM : thm)
  deriving Inhabited

/-- What trace_form.ml uses from Session besides theorems. -/
structure TraceFormDeps where
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
/- trace_form.ml phrases from line 46 to 313                              -/
/- ---------------------------------------------------------------------- -/

structure TraceForm where
  -- @@FIELDS
  EXTENSION_LINCOMB_PROD_RING : thm
  FREE_BASIS_PROD_RING : thm
  BASIS_COORDINATES_PROD_RING : thm
  ALGEBRA_TRACE_PROD_RING : thm
  FREE_BASIS_ISOMORPHIC_IMAGE : thm
  ALGEBRA_TRACE_ISOMORPHIC_IMAGE : thm
  NUMBER_FIELD_ISOMORPHIC_IMAGE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupTraceForm [HolBase] (D : TraceFormDeps) :
    ExceptT String IO TraceForm := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, MESON, .. } := D
  let { ADD_SUB2, ALGEBRA_TRACE_FREE_BASIS, ALGEBRA_TRACE_NORM_HOMOMORPHIC_IMAGE,
        BASIS_COORDINATES, BASIS_COORDINATES_EXPAND, BASIS_COORDINATES_IN_CARRIER,
        BASIS_COORDINATES_UNIQUE, COND_RAND, EQ_TRANS, EXTENSION_DEGREE_ISOMORPHISM,
        FINITE_EXTENSION_ISOMORPHISM, FINITE_NUMSEG_LT, FORALL_PAIR_THM,
        FREE_BASIS_INDEPENDENT, FREE_BASIS_IN_CARRIER, FUN_EQ_THM, IN_CROSS,
        IN_ELIM_THM, IN_IMAGE, ISOMORPHIC_RING_FIELDNESS, I_THM, MULT_CLAUSES,
        NUMBER_FIELD_DISCRIMINANT_BASIS, NUMBER_FIELD_IMP_FIELD, PAIR_EQ,
        PRIME_SUBFIELD_TOWER_LAW, PROD_RING, RING_0, RING_ADD_LZERO, RING_ADD_RZERO,
        RING_DET_EQ, RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_COMPOSE,
        RING_HOMOMORPHISM_I, RING_HOMOMORPHISM_INTEGER_RING_OF_INT,
        RING_HOMOMORPHISM_IN_CARRIER, RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_PAIRED,
        RING_HOMOMORPHISM_RING_OF_INT, RING_HOMOMORPHISM_SUM_MUL, RING_ISOMORPHISM,
        RING_ISOMORPHISM_IMP_HOMOMORPHISM, RING_ISOMORPHISM_RING_OF_INTEGERS, RING_MUL,
        RING_MUL_RZERO, RING_OF_INTEGERS, RING_OF_INTEGERS_FREE, RING_SUM, RING_SUM_EQ,
        RING_SUM_EQ_0, RING_SUM_NUMSEG_LT_ADD, RING_SUM_PROD_RING, basis_discriminant,
        free_basis, isomorphic_ring, mul_matrix, number_field, o_DEF, o_THM, .. } := D.core1
  -- @@SCOPE END

  let EXTENSION_LINCOMB_PROD_RING ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"i < n2 ==> n1 + i < n1 + n2:num"
    let r2 ← ARITH_RULE q1
    let q3 ← q r"i < n1 ==> i < n1 + n2:num"
    let r4 ← ARITH_RULE q3
    let q5 ← q r"ring_sum r t (f:num->C) = ring_0 r /\
      ring_sum r (s:num->bool) g = ring_sum r s h
      ==> ring_add r (ring_sum r t f) (ring_sum r s g) = ring_sum r s h"
    let r6 ← MESON [RING_ADD_LZERO, RING_SUM] q5
    let q7 ← q r"ring_sum r t (f:num->B) = ring_0 r /\
      ring_sum r (s:num->bool) g = ring_sum r s h
      ==> ring_add r (ring_sum r s g) (ring_sum r t f) = ring_sum r s h"
    let r8 ← MESON [RING_ADD_RZERO, RING_SUM] q7
    let q9 ← q r"~(n1 + i < n1:num)"
    let r10 ← ARITH_RULE q9
    let q11 ← q r"!i. i < n1 + n2
        ==> (h1:A->B)((c:num->A) i) IN ring_carrier l1 /\
            (h2:A->C)(c i) IN ring_carrier l2"
    prove
      r"!k:A ring l1:B ring l2:C ring h1 h2 n1 n2 g1 g2 c.
          ring_homomorphism(k,l1) h1 /\ ring_homomorphism(k,l2) h2 /\
          (!i. i < n1:num ==> g1 i IN ring_carrier l1) /\
          (!i. i < n2 ==> g2 i IN ring_carrier l2) /\
          (!i. i < n1 + n2 ==> c i IN ring_carrier k)
          ==> ring_sum (prod_ring l1 l2) {i | i < n1 + n2}
                (\i. ring_mul (prod_ring l1 l2) (h1(c i),h2(c i))
                       (if i < n1 then (g1 i,ring_0 l2)
                        else (ring_0 l1,g2(i - n1)))) =
              ring_sum l1 {i | i < n1} (\i. ring_mul l1 (h1(c i)) (g1 i)),
              ring_sum l2 {i | i < n2} (\i. ring_mul l2 (h2(c(n1 + i))) (g2 i))"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN q11 ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN wPart lhand (lhand o rand) RING_SUM_PROD_RING THEN ANTS_TAC THENL [REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL THEN ASM_SIMP_TAC [PROD_RING, IN_CROSS] THEN COND_CASES_TAC THEN ASM_SIMP_TAC [IN_CROSS, RING_0] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC, DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [PAIR_EQ, o_DEF, RING_SUM_NUMSEG_LT_ADD] THEN REWRITE_TAC [r10, ADD_SUB2] THEN REWRITE_TAC [PROD_RING, COND_RAND] THEN CONJ_TAC THENL [MATCH_MP_TAC r8, MATCH_MP_TAC r6] THEN CONJ_TAC THEN (MATCH_MP_TAC RING_SUM_EQ_0 ORELSE MATCH_MP_TAC RING_SUM_EQ) THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [RING_MUL_RZERO, r4, r2])

  let FREE_BASIS_PROD_RING ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"~(i:num < n1) ==> n1 + i - n1 = i")
    let r2 ← ARITH_RULE (← q r"~(i:num < n1) /\ i < n1 + n2 ==> i - n1 < n2")
    let r3 ← ARITH_RULE (← q r"i < n2 ==> n1 + i < n1 + n2:num")
    let r4 ← ARITH_RULE (← q r"i < n1 ==> i < n1 + n2:num")
    let r5 ← ARITH_RULE (← q r"~(n1 + i < n1:num)")
    prove
      r"!k:A ring l1:B ring l2:C ring h1 h2 n1 n2 g1 g2.
          ring_homomorphism(k,l1) h1 /\ ring_homomorphism(k,l2) h2 /\
          free_basis (k,l1) h1 n1 g1 /\ free_basis (k,l2) h2 n2 g2
          ==> free_basis (k,prod_ring l1 l2) (\a. h1 a,h2 a) (n1 + n2)
                (\i. if i < n1 then (g1 i,ring_0 l2)
                     else (ring_0 l1,g2(i - n1)))"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h1:A->B"), (← q r"k:A ring"), (← q r"l1:B ring"), (← q r"n1:num"), (← q r"g1:num->B")] FREE_BASIS_IN_CARRIER) THEN MP_TAC (← ISPECL [(← q r"h2:A->C"), (← q r"k:A ring"), (← q r"l2:C ring"), (← q r"n2:num"), (← q r"g2:num->C")] FREE_BASIS_IN_CARRIER) THEN ASM_REWRITE_TAC [] THEN REPEAT DISCH_TAC THEN REWRITE_TAC [free_basis, (← CONJUNCT1 PROD_RING), FORALL_PAIR_THM, IN_CROSS] THEN REPEAT CONJ_TAC THENL [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [IN_CROSS, RING_0] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC, MAP_EVERY X_GEN_TAC [(← q r"y1:B"), (← q r"y2:C")] THEN STRIP_TAC THEN EXISTS_TAC (← q r"\i. if i < n1 then basis_coordinates (k,l1) (h1:A->B) n1 g1 y1 i
            else basis_coordinates (k,l2) (h2:A->C) n2 g2 y2 (i - n1)") THEN SUBGOAL_THEN (← q r"!i. i < n1 + n2
            ==> (if i < n1 then basis_coordinates (k,l1) (h1:A->B) n1 g1 y1 i
                 else basis_coordinates (k,l2) (h2:A->C) n2 g2 y2 (i - n1)) IN
                ring_carrier k") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN MATCH_MP_TAC BASIS_COORDINATES_IN_CARRIER THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC, ASM_REWRITE_TAC []] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l1:B ring"), (← q r"l2:C ring"), (← q r"h1:A->B"), (← q r"h2:A->C"), (← q r"n1:num"), (← q r"n2:num"), (← q r"g1:num->B"), (← q r"g2:num->C"), (← q r"\i. if i < n1 then basis_coordinates (k,l1) (h1:A->B) n1 g1 y1 i
             else basis_coordinates (k,l2) (h2:A->C) n2 g2 y2 (i - n1)")] EXTENSION_LINCOMB_PROD_RING) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [r5, ADD_SUB2, PAIR_EQ] THEN CONJ_TAC THEN CONV_TAC SYM_CONV THENL [TRANS_TAC EQ_TRANS (← q r"ring_sum l1 {i | i < n1}
            (\i. ring_mul l1 ((h1:A->B)(basis_coordinates (k,l1) h1 n1 g1 y1 i))
                             ((g1:num->B) i))") THEN CONJ_TAC THENL [MATCH_MP_TAC RING_SUM_EQ THEN SIMP_TAC [IN_ELIM_THM], ALL_TAC], ALL_TAC] THEN MATCH_MP_TAC BASIS_COORDINATES_EXPAND THEN ASM_REWRITE_TAC [], X_GEN_TAC (← q r"c:num->A") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l1:B ring"), (← q r"l2:C ring"), (← q r"h1:A->B"), (← q r"h2:A->C"), (← q r"n1:num"), (← q r"n2:num"), (← q r"g1:num->B"), (← q r"g2:num->C"), (← q r"c:num->A")] EXTENSION_LINCOMB_PROD_RING) THEN ASM_REWRITE_TAC [PROD_RING, PAIR_EQ] THEN DISCH_THEN (CONJUNCTS_THEN (ASSUME_TAC o SYM)) THEN MP_TAC (← ISPECL [(← q r"h1:A->B"), (← q r"k:A ring"), (← q r"l1:B ring"), (← q r"n1:num"), (← q r"g1:num->B"), (← q r"c:num->A")] FREE_BASIS_INDEPENDENT) THEN MP_TAC (← ISPECL [(← q r"h2:A->C"), (← q r"k:A ring"), (← q r"l2:C ring"), (← q r"n2:num"), (← q r"g2:num->C"), (← q r"\i. (c:num->A)(n1 + i)")] FREE_BASIS_INDEPENDENT) THEN ASM_SIMP_TAC [r4, r3] THEN DISCH_THEN (LABEL_TAC "2") THEN DISCH_TAC THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"i:num < n1") THEN ASM_SIMP_TAC [] THEN REMOVE_THEN "2" (MP_TAC o (SPEC (← q r"i - n1:num"))) THEN ASM_SIMP_TAC [r2, r1]])

  let BASIS_COORDINATES_PROD_RING ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"~(i:num < n1) ==> n1 + i - n1 = i")
    let r2 ← ARITH_RULE (← q r"~(i:num < n1) /\ i < n1 + n2 ==> i - n1 < n2")
    let r3 ← ARITH_RULE (← q r"i < n2 ==> n1 + i < n1 + n2:num")
    let r4 ← ARITH_RULE (← q r"i < n1 ==> i < n1 + n2:num")
    prove
      r"!k:A ring l1:B ring l2:C ring h1 h2 n1 n2 g1 g2 y1 y2 i.
          ring_homomorphism(k,l1) h1 /\ ring_homomorphism(k,l2) h2 /\
          free_basis (k,l1) h1 n1 g1 /\ free_basis (k,l2) h2 n2 g2 /\
          y1 IN ring_carrier l1 /\ y2 IN ring_carrier l2 /\ i < n1 + n2
          ==> basis_coordinates (k,prod_ring l1 l2) (\a. h1 a,h2 a) (n1 + n2)
                (\i. if i < n1 then (g1 i,ring_0 l2)
                     else (ring_0 l1,g2(i - n1)))
                (y1,y2) i =
              if i < n1 then basis_coordinates (k,l1) h1 n1 g1 y1 i
              else basis_coordinates (k,l2) h2 n2 g2 y2 (i - n1)"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h1:A->B"), (← q r"k:A ring"), (← q r"l1:B ring"), (← q r"n1:num"), (← q r"g1:num->B")] FREE_BASIS_IN_CARRIER) THEN MP_TAC (← ISPECL [(← q r"h2:A->C"), (← q r"k:A ring"), (← q r"l2:C ring"), (← q r"n2:num"), (← q r"g2:num->C")] FREE_BASIS_IN_CARRIER) THEN ASM_REWRITE_TAC [] THEN REPEAT DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"\a. (h1:A->B) a,(h2:A->C) a"), (← q r"k:A ring"), (← q r"prod_ring (l1:B ring) (l2:C ring)"), (← q r"n1 + n2:num"), (← q r"\i. if i < n1 then ((g1:num->B) i,ring_0 l2)
           else (ring_0 l1,(g2:num->C)(i - n1))"), (← q r"(y1:B,y2:C)")] BASIS_COORDINATES) THEN ASM_SIMP_TAC [FREE_BASIS_PROD_RING, (← CONJUNCT1 PROD_RING), IN_CROSS] THEN ABBREV_TAC (← q r"c = basis_coordinates (k,prod_ring l1 l2) (\a. (h1:A->B) a,(h2:A->C) a)
            (n1 + n2) (\i. if i < n1 then ((g1:num->B) i,ring_0 l2)
                           else (ring_0 l1,(g2:num->C)(i - n1))) (y1,y2)") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l1:B ring"), (← q r"l2:C ring"), (← q r"h1:A->B"), (← q r"h2:A->C"), (← q r"n1:num"), (← q r"n2:num"), (← q r"g1:num->B"), (← q r"g2:num->C"), (← q r"c:num->A")] EXTENSION_LINCOMB_PROD_RING) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [PAIR_EQ] THEN STRIP_TAC THEN COND_CASES_TAC THENL [MP_TAC (← ISPECL [(← q r"h1:A->B"), (← q r"k:A ring"), (← q r"l1:B ring"), (← q r"n1:num"), (← q r"g1:num->B"), (← q r"y1:B"), (← q r"c:num->A")] BASIS_COORDINATES_UNIQUE) THEN ASM_SIMP_TAC [r4], MP_TAC (← ISPECL [(← q r"h2:A->C"), (← q r"k:A ring"), (← q r"l2:C ring"), (← q r"n2:num"), (← q r"g2:num->C"), (← q r"y2:C"), (← q r"\i. (c:num->A)(n1 + i)")] BASIS_COORDINATES_UNIQUE) THEN ASM_SIMP_TAC [r3] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"i - n1:num"))) THEN ASM_SIMP_TAC [r2, r1]])

  let ALGEBRA_TRACE_PROD_RING ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"~(n1 + i < n1:num)")
    let r2 ← ARITH_RULE (← q r"i < n2 ==> n1 + i < n1 + n2:num")
    let r3 ← ARITH_RULE (← q r"i < n1 ==> i < n1 + n2:num")
    let r4 ← ARITH_RULE (← q r"~(n1 + i < n1:num)")
    prove
      r"!k:A ring l1:B ring l2:C ring h1 h2 n1 n2 g1 g2 x1 x2.
          ring_homomorphism(k,l1) h1 /\ ring_homomorphism(k,l2) h2 /\
          free_basis (k,l1) h1 n1 g1 /\ free_basis (k,l2) h2 n2 g2 /\
          x1 IN ring_carrier l1 /\ x2 IN ring_carrier l2
          ==> algebra_trace (k,prod_ring l1 l2) (\a. h1 a,h2 a) (x1,x2) =
              ring_add k (algebra_trace (k,l1) h1 x1)
                         (algebra_trace (k,l2) h2 x2)"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h1:A->B"), (← q r"k:A ring"), (← q r"l1:B ring"), (← q r"n1:num"), (← q r"g1:num->B")] FREE_BASIS_IN_CARRIER) THEN MP_TAC (← ISPECL [(← q r"h2:A->C"), (← q r"k:A ring"), (← q r"l2:C ring"), (← q r"n2:num"), (← q r"g2:num->C")] FREE_BASIS_IN_CARRIER) THEN ASM_REWRITE_TAC [] THEN REPEAT DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l1:B ring"), (← q r"l2:C ring"), (← q r"h1:A->B"), (← q r"h2:A->C"), (← q r"n1:num"), (← q r"n2:num"), (← q r"g1:num->B"), (← q r"g2:num->C")] FREE_BASIS_PROD_RING) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"\a. (h1:A->B) a,(h2:A->C) a"), (← q r"k:A ring"), (← q r"prod_ring (l1:B ring) (l2:C ring)"), (← q r"n1 + n2:num"), (← q r"\i. if i < n1 then ((g1:num->B) i,ring_0 l2)
           else (ring_0 l1,(g2:num->C)(i - n1))"), (← q r"(x1:B,x2:C)")] ALGEBRA_TRACE_FREE_BASIS) THEN MP_TAC (← ISPECL [(← q r"h1:A->B"), (← q r"k:A ring"), (← q r"l1:B ring"), (← q r"n1:num"), (← q r"g1:num->B"), (← q r"x1:B")] ALGEBRA_TRACE_FREE_BASIS) THEN MP_TAC (← ISPECL [(← q r"h2:A->C"), (← q r"k:A ring"), (← q r"l2:C ring"), (← q r"n2:num"), (← q r"g2:num->C"), (← q r"x2:C")] ALGEBRA_TRACE_FREE_BASIS) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_PAIRED, (← CONJUNCT1 PROD_RING), IN_CROSS] THEN REPEAT (DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC [mul_matrix, RING_SUM_NUMSEG_LT_ADD, r4, ADD_SUB2] THEN BINOP_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN ASM_SIMP_TAC [PROD_RING, RING_MUL_RZERO] THEN wPart lhand (lhand o rand) BASIS_COORDINATES_PROD_RING THEN ASM_SIMP_TAC [RING_MUL, RING_0, r3, r2, r1, ADD_SUB2])

  let FREE_BASIS_ISOMORPHIC_IMAGE ← prove
    r"!k:A ring l:B ring l':C ring h f n g.
        ring_homomorphism(k,l) h /\ ring_isomorphism(l,l') f /\
        free_basis (k,l) h n g
        ==> free_basis (k,l') (f o h) n (f o g)"
    (REPEAT GEN_TAC THEN REWRITE_TAC [RING_ISOMORPHISM] THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FREE_BASIS_IN_CARRIER)) THEN SUBGOAL_THEN (← q r"!c. (!i. i < n ==> c i IN ring_carrier k)
        ==> (f:B->C)(ring_sum l {i | i < n}
                       (\i. ring_mul l ((h:A->B)(c i)) ((g:num->B) i))) =
            ring_sum l' {i | i < n} (\i. ring_mul l' (f(h(c i))) (f(g i)))") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC (← BETA_RULE (← ISPECL [(← q r"l:B ring"), (← q r"l':C ring"), (← q r"f:B->C"), (← q r"{i:num | i < n}"), (← q r"\i. (h:A->B)((c:num->A) i)"), (← q r"g:num->B")] RING_HOMOMORPHISM_SUM_MUL)) THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN EXISTS_TAC (← q r"k:A ring") THEN ASM_SIMP_TAC [], ALL_TAC] THEN REWRITE_TAC [free_basis, o_THM] THEN REPEAT CONJ_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN EXISTS_TAC (← q r"l:B ring") THEN ASM_SIMP_TAC [], X_GEN_TAC (← q r"y:C") THEN FIRST_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [(← SYM th)])) THEN REWRITE_TAC [IN_IMAGE] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"x:B") (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN EXISTS_TAC (← q r"basis_coordinates (k,l) (h:A->B) n g x") THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"basis_coordinates (k,l) (h:A->B) n g x"))) THEN ASM_SIMP_TAC [BASIS_COORDINATES_IN_CARRIER, BASIS_COORDINATES_EXPAND], X_GEN_TAC (← q r"c:num->A") THEN STRIP_TAC THEN MATCH_MP_TAC FREE_BASIS_INDEPENDENT THEN MAP_EVERY EXISTS_TAC [(← q r"h:A->B"), (← q r"l:B ring"), (← q r"g:num->B")] THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"!x y. x IN ring_carrier l /\ y IN ring_carrier l /\
                       (f:B->C) x = f y ==> x = y") THEN DISCH_THEN MATCH_MP_TAC THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"l':C ring"), (← q r"f:B->C")] RING_HOMOMORPHISM_0) THEN ASM_SIMP_TAC [RING_SUM, RING_0]])

  let ALGEBRA_TRACE_ISOMORPHIC_IMAGE ← prove
    r"!k:A ring l:B ring l':C ring h f n g x.
        ring_homomorphism(k,l) h /\ ring_isomorphism(l,l') f /\
        free_basis (k,l) h n g /\ x IN ring_carrier l
        ==> algebra_trace (k,l') (f o h) (f x) =
            algebra_trace (k,l) h x"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"l':C ring"), (← q r"h:A->B"), (← q r"f:B->C"), (← q r"n:num"), (← q r"g:num->B")] FREE_BASIS_ISOMORPHIC_IMAGE) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_ISOMORPHISM_IMP_HOMOMORPHISM)) THEN SUBGOAL_THEN (← q r"ring_homomorphism(k,l') ((f:B->C) o (h:A->B))") ASSUME_TAC THENL [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC (← q r"l:B ring") THEN ASM_REWRITE_TAC [], ASM_REWRITE_TAC [] THEN DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"(f:B->C) o (h:A->B)"), (← q r"I:A->A"), (← q r"f:B->C"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"k:A ring"), (← q r"l':C ring"), (← q r"n:num"), (← q r"g:num->B"), (← q r"x:B")] ALGEBRA_TRACE_NORM_HOMOMORPHIC_IMAGE) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_I, I_THM, o_THM])

  let NUMBER_FIELD_ISOMORPHIC_IMAGE ← prove
    r"!(k:A ring) (l:B ring) f.
        number_field k /\ ring_isomorphism(k,l) f
        ==> number_field l /\
            extension_degree(subfield_generated l {ring_0 l},l) I =
            extension_degree(subfield_generated k {ring_0 k},k) I /\
            number_field_discriminant l = number_field_discriminant k"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN (← q r"field(l:B ring)") ASSUME_TAC THENL [ASM_MESON_TAC [ISOMORPHIC_RING_FIELDNESS, isomorphic_ring], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_ISOMORPHISM_IMP_HOMOMORPHISM)) THEN MP_TAC (← ISPECL [(← q r"f:A->B"), (← q r"k:A ring"), (← q r"l:B ring")] PRIME_SUBFIELD_TOWER_LAW) THEN ASM_SIMP_TAC [FINITE_EXTENSION_ISOMORPHISM, EXTENSION_DEGREE_ISOMORPHISM] THEN REWRITE_TAC [MULT_CLAUSES] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"number_field(l:B ring)") ASSUME_TAC THENL [REWRITE_TAC [number_field] THEN ASM_MESON_TAC [number_field], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_FREE) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"n = extension_degree (subfield_generated k {ring_0 k},k) (I:A->A)") THEN DISCH_THEN (X_CHOOSE_TAC (← q r"w:num->A")) THEN SUBGOAL_THEN (← q r"ring_isomorphism(ring_of_integers k,ring_of_integers l) (f:A->B)") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_ISOMORPHISM_RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_homomorphism(integer_ring,ring_of_integers k) (ring_of_int k:int->A)") ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"(f:A->B) o ring_of_int k = ring_of_int l") ASSUME_TAC THENL [REWRITE_TAC [FUN_EQ_THM, o_THM] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_RING_OF_INT], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring"), (← q r"ring_of_int k:int->A"), (← q r"f:A->B"), (← q r"n:num"), (← q r"w:num->A")] FREE_BASIS_ISOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"n:num"), (← q r"(f:A->B) o (w:num->A)")] NUMBER_FIELD_DISCRIMINANT_BASIS) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A")] NUMBER_FIELD_DISCRIMINANT_BASIS) THEN ASM_REWRITE_TAC [] THEN REPEAT (DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC [basis_discriminant] THEN MATCH_MP_TAC RING_DET_EQ THEN MAP_EVERY X_GEN_TAC [(← q r"i:num"), (← q r"j:num")] THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(w:num->A) i IN ring_carrier(ring_of_integers k) /\
    w j IN ring_carrier(ring_of_integers k)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [FREE_BASIS_IN_CARRIER], ALL_TAC] THEN REWRITE_TAC [o_THM] THEN SUBGOAL_THEN (← q r"ring_mul (ring_of_integers l) ((f:A->B) (w i)) (f (w j)) =
    f (ring_mul (ring_of_integers k) ((w:num->A) i) (w j))") SUBST1_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring"), (← q r"f:A->B")] RING_HOMOMORPHISM_MUL) THEN ASM_SIMP_TAC [RING_ISOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring"), (← q r"ring_of_int k:int->A"), (← q r"f:A->B"), (← q r"n:num"), (← q r"w:num->A"), (← q r"ring_mul (ring_of_integers k) ((w:num->A) i) (w j)")] ALGEBRA_TRACE_ISOMORPHIC_IMAGE) THEN ASM_SIMP_TAC [RING_MUL])

  -- @@RETURN BEGIN
  return { EXTENSION_LINCOMB_PROD_RING, FREE_BASIS_PROD_RING,
           BASIS_COORDINATES_PROD_RING, ALGEBRA_TRACE_PROD_RING,
           FREE_BASIS_ISOMORPHIC_IMAGE, ALGEBRA_TRACE_ISOMORPHIC_IMAGE,
           NUMBER_FIELD_ISOMORPHIC_IMAGE }
  -- @@RETURN END

end HolANT.TraceForm
