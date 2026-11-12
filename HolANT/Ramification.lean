/- ========================================================================= -/
/- ANT: Ramification and the discriminant                                  -/
/- ========================================================================= -/
/- File: HolANT/Ramification.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/ramification.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antramificationdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/products.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/prime_split.ml, ANT/norm_index.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/finite_field_trace.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.Ramification fills them).

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
import HolANT.Integral
import HolANT.IdealArith
import HolANT.Dedekind
import HolLibrary.Isum
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolANT.DedekindStruct
import HolANT.IdealNorm
import HolANT.RingOfIntegers
import HolANT.PrimeSplit
import HolANT.NormIndex
import HolANT.Discriminant
import HolANT.TraceForm
import HolANT.FiniteFieldTrace

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.Algmisc
open HolANT.Integral
open HolANT.IdealArith
open HolANT.Dedekind
open HolANT.Zlattice
open HolANT.Numfield
open HolANT.DedekindStruct
open HolANT.IdealNorm
open HolANT.RingOfIntegers
open HolANT.PrimeSplit
open HolANT.NormIndex
open HolANT.Discriminant
open HolANT.TraceForm
open HolANT.FiniteFieldTrace

namespace HolANT.Ramification

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ALGEBRA_TRACE_NILPOTENT ALGEBRA_TRACE_NORM_HOMOMORPHIC_IMAGE
   ALGEBRA_TRACE_QUOTIENT_COMAXIMAL_NONZERO BASIS_COORDINATES_EXPAND
   BASIS_COORDINATES_LINCOMB BASIS_COORDINATES_LMUL
   BASIS_DISCRIMINANT_EQ_0_FINITE BASIS_DISCRIMINANT_HOMOMORPHIC_IMAGE
   DEDEKIND_QUOTIENT_RING_REDUCED DEDEKIND_RING_OF_INTEGERS DIVIDES_ZERO
   EXTENSION_LINCOMB_LMUL FIELD_IMP_INTEGRAL_DOMAIN FIELD_INTEGER_MOD_RING
   FINITE_INTEGER_MOD_RING FINITE_NUMSEG_LE FINITE_NUMSEG_LT FINITE_SUBSET
   FORALL_IN_GSPEC FREE_BASIS_IN_CARRIER IDEAL_GENERATED_EQ_0
   IDEAL_GENERATED_INC IDEAL_GENERATED_MINIMAL IDEAL_GENERATED_SING
   IDEAL_VALUATION_EQ_0 INTEGER_MOD_RING_CARRIER_REM INTEGER_MOD_RING_CLAUSES
   INTEGER_MOD_RING_OF_INT INTEGER_RING INT_ABS_NUM INT_ABS_POS INT_DIVIDES_LE
   INT_OF_NUM_LE INT_OF_NUM_OF_INT INT_REM_EQ_0 IN_ELIM_THM
   IN_INTEGER_MOD_RING_CARRIER IN_SING IN_UNIV MONO_EXISTS NOT_FORALL_THM
   NOT_IMP NOT_LE NUMBER_FIELD_DISCRIMINANT_BASIS
   NUMBER_FIELD_DISCRIMINANT_NONZERO PRIME_IMP_NZ PRIME_IMP_RING_IDEAL
   QUOTIENT_RING_0 QUOTIENT_RING_CARRIER RAMIFICATION_INDEX_PRIME
   RIGHT_IMP_EXISTS_THM RING_COSET_EQ_IDEAL
   RING_HOMOMORPHISM_INTEGER_MOD_RING_OF_INT
   RING_HOMOMORPHISM_INTEGER_RING_OF_INT RING_HOMOMORPHISM_IN_CARRIER
   RING_HOMOMORPHISM_POW RING_HOMOMORPHISM_RING_COSET
   RING_HOMOMORPHISM_RING_OF_INT RING_HOMOMORPHISM_RING_OF_NUM
   RING_HOMOMORPHISM_SUM_MUL RING_IDEAL_IDEAL_GENERATED RING_IDEAL_IMP_SUBSET
   RING_NILPOTENT RING_OF_INT RING_OF_INTEGERS RING_OF_INTEGERS_FREE
   RING_OF_INT_OF_NUM RING_OF_NUM RING_OF_NUM_EQ_0 RING_POW RING_SUM RING_SUM_EQ
   SING_SUBSET SKOLEM_THM SUBSET free_basis int_divides number_field o_DEF
   ring_divides : thm)
  deriving Inhabited

/-- What ramification.ml uses from Session besides theorems. -/
structure RamificationDeps where
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
/- ramification.ml phrases from line 55 to 418                            -/
/- ---------------------------------------------------------------------- -/

structure Ramification where
  -- @@FIELDS
  RING_HOMOMORPHISM_INTEGER_MOD_QUOTIENT_RING : thm
  FREE_BASIS_IDEAL_GENERATED_NUM : thm
  FREE_BASIS_QUOTIENT_RING_INTEGER_MOD : thm
  ALGEBRA_TRACE_QUOTIENT_RING_INTEGER_MOD : thm
  BASIS_DISCRIMINANT_QUOTIENT_RING_INTEGER_MOD : thm
  ALGEBRA_TRACE_NILPOTENT_INTEGER_MOD : thm
  ALGEBRA_TRACE_INTEGER_MOD_COMAXIMAL : thm
  NUMBER_FIELD_DISCRIMINANT_DIVIDES : thm
  NUMBER_FIELD_RAMIFIED_DISCRIMINANT : thm
  NUMBER_FIELD_FINITE_RAMIFIED_PRIMES : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupRamification [HolBase] (D : RamificationDeps) :
    ExceptT String IO Ramification := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_INT_ARITH_TAC, ASM_MESON_TAC, INTEGER_RULE, SET_RULE, TAUT, .. } := D
  let { ALGEBRA_TRACE_NILPOTENT, ALGEBRA_TRACE_NORM_HOMOMORPHIC_IMAGE,
        ALGEBRA_TRACE_QUOTIENT_COMAXIMAL_NONZERO, BASIS_COORDINATES_EXPAND,
        BASIS_COORDINATES_LINCOMB, BASIS_COORDINATES_LMUL,
        BASIS_DISCRIMINANT_EQ_0_FINITE, BASIS_DISCRIMINANT_HOMOMORPHIC_IMAGE,
        DEDEKIND_QUOTIENT_RING_REDUCED, DEDEKIND_RING_OF_INTEGERS, DIVIDES_ZERO,
        EXTENSION_LINCOMB_LMUL, FIELD_IMP_INTEGRAL_DOMAIN, FIELD_INTEGER_MOD_RING,
        FINITE_INTEGER_MOD_RING, FINITE_NUMSEG_LE, FINITE_NUMSEG_LT, FINITE_SUBSET,
        FORALL_IN_GSPEC, FREE_BASIS_IN_CARRIER, IDEAL_GENERATED_EQ_0,
        IDEAL_GENERATED_INC, IDEAL_GENERATED_MINIMAL, IDEAL_GENERATED_SING,
        IDEAL_VALUATION_EQ_0, INTEGER_MOD_RING_CARRIER_REM, INTEGER_MOD_RING_CLAUSES,
        INTEGER_MOD_RING_OF_INT, INTEGER_RING, INT_ABS_NUM, INT_ABS_POS,
        INT_DIVIDES_LE, INT_OF_NUM_LE, INT_OF_NUM_OF_INT, INT_REM_EQ_0, IN_ELIM_THM,
        IN_INTEGER_MOD_RING_CARRIER, IN_SING, IN_UNIV, MONO_EXISTS, NOT_FORALL_THM,
        NOT_IMP, NOT_LE, NUMBER_FIELD_DISCRIMINANT_BASIS,
        NUMBER_FIELD_DISCRIMINANT_NONZERO, PRIME_IMP_NZ, PRIME_IMP_RING_IDEAL,
        QUOTIENT_RING_0, QUOTIENT_RING_CARRIER, RAMIFICATION_INDEX_PRIME,
        RIGHT_IMP_EXISTS_THM, RING_COSET_EQ_IDEAL,
        RING_HOMOMORPHISM_INTEGER_MOD_RING_OF_INT,
        RING_HOMOMORPHISM_INTEGER_RING_OF_INT, RING_HOMOMORPHISM_IN_CARRIER,
        RING_HOMOMORPHISM_POW, RING_HOMOMORPHISM_RING_COSET,
        RING_HOMOMORPHISM_RING_OF_INT, RING_HOMOMORPHISM_RING_OF_NUM,
        RING_HOMOMORPHISM_SUM_MUL, RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IMP_SUBSET,
        RING_NILPOTENT, RING_OF_INT, RING_OF_INTEGERS, RING_OF_INTEGERS_FREE,
        RING_OF_INT_OF_NUM, RING_OF_NUM, RING_OF_NUM_EQ_0, RING_POW, RING_SUM,
        RING_SUM_EQ, SING_SUBSET, SKOLEM_THM, SUBSET, free_basis, int_divides,
        number_field, o_DEF, ring_divides, .. } := D.core1
  -- @@SCOPE END

  let RING_HOMOMORPHISM_INTEGER_MOD_QUOTIENT_RING ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!r:A ring m.
          ring_homomorphism
           (integer_mod_ring m,
            quotient_ring r (ideal_generated r {ring_of_num r m}))
           (ring_of_int(quotient_ring r (ideal_generated r {ring_of_num r m}))) /\
          !a. ring_coset r (ideal_generated r {ring_of_num r m})
                         (ring_of_int r a) =
              ring_of_int (quotient_ring r (ideal_generated r {ring_of_num r m}))
                          (a rem &m)"
      (REPEAT GEN_TAC THEN ABBREV_TAC (← q r"j = ideal_generated r {ring_of_num r m:A}") THEN SUBGOAL_THEN (← q r"ring_ideal r (j:A->bool)") ASSUME_TAC THENL [EXPAND_TAC "j" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_HOMOMORPHISM_RING_COSET)) THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_MOD_RING_OF_INT, (← GSYM RING_OF_NUM_EQ_0)] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM (← MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM th))])) THEN ASM_SIMP_TAC [QUOTIENT_RING_0, RING_COSET_EQ_IDEAL, RING_OF_NUM] THEN EXPAND_TAC "j" THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN REWRITE_TAC [SING_SUBSET, IN_SING, RING_OF_NUM], DISCH_THEN (ASSUME_TAC o (MATCH_MP RING_HOMOMORPHISM_RING_OF_INT)) THEN FIRST_X_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_RING_OF_INT th)])) THEN ASM_REWRITE_TAC [(← GSYM INTEGER_MOD_RING_OF_INT)]])

  let FREE_BASIS_IDEAL_GENERATED_NUM ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← INTEGER_RULE (← q r"!m d:int. m divides m * d")
    prove
      r"!r:A ring n w m x.
          free_basis (integer_ring,r) (ring_of_int r) n w /\ x IN ring_carrier r
          ==> (x IN ideal_generated r {ring_of_num r m} <=>
               !i. i < n
                   ==> &m divides
                       basis_coordinates (integer_ring,r) (ring_of_int r)
                                         n w x i)"
      (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [IDEAL_GENERATED_SING, RING_OF_NUM, IN_ELIM_THM, ring_divides, (← GSYM RING_OF_INT_OF_NUM)] THEN MP_TAC (← ISPEC (← q r"r:A ring") RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FREE_BASIS_IN_CARRIER)) THEN DISCH_TAC THEN EQ_TAC THENL [DISCH_THEN (X_CHOOSE_THEN (← q r"y:A") (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN ASM_SIMP_TAC [BASIS_COORDINATES_LMUL, INTEGER_RING, IN_UNIV, r1], REWRITE_TAC [int_divides] THEN DISCH_THEN ((X_CHOOSE_TAC (← q r"d:num->int")) o (REWRITE_RULE [RIGHT_IMP_EXISTS_THM, SKOLEM_THM])) THEN EXISTS_TAC (← q r"ring_sum r {i | i < n}
                    (\i. ring_mul r (ring_of_int r (d i)) ((w:num->A) i))") THEN REWRITE_TAC [RING_SUM] THEN MP_TAC (← ISPECL [(← q r"ring_of_int r:int->A"), (← q r"integer_ring"), (← q r"r:A ring"), (← q r"{i:num | i < n}"), (← q r"&m:int"), (← q r"d:num->int"), (← q r"w:num->A")] EXTENSION_LINCOMB_LMUL) THEN ASM_SIMP_TAC [INTEGER_RING, IN_UNIV, FINITE_NUMSEG_LT, IN_ELIM_THM] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"ring_of_int r:int->A"), (← q r"integer_ring"), (← q r"r:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"x:A")] BASIS_COORDINATES_EXPAND) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC LAND_CONV [(← SYM th)])) THEN MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC [IN_ELIM_THM]])

  let FREE_BASIS_QUOTIENT_RING_INTEGER_MOD ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"(&0:int) divides c <=> c = &0"
    let r2 ← INTEGER_RULE q1
    let q3 ← q r"&m:int = &0"
    let p4 ← prove r"!m c. c IN ring_carrier(integer_mod_ring m) /\ &m divides c ==> c = &0" (REWRITE_TAC [IN_INTEGER_MOD_RING_CARRIER] THEN REPEAT GEN_TAC THEN ASM_CASES_TAC q3 THEN ASM_REWRITE_TAC [r2] THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (MATCH_MP INT_DIVIDES_LE)) THEN ASM_INT_ARITH_TAC)
    let lemma := p4
    let q5 ← q r"ring_sum r {i | i < n}
      (\i. ring_mul r (ring_of_int r ((c:num->int) i)) ((w:num->A) i)) IN j"
    let q6 ← q r"c:num->int"
    let q7 ← q r"basis_coordinates (integer_ring,r) (ring_of_int r) n w (y:A)"
    let q8 ← q r"\i. basis_coordinates (integer_ring,r) (ring_of_int r) n w (y:A) i
          rem &m"
    let q9 ← q r"y:A"
    let q10 ← q r"r:A ring"
    let q11 ← q r"w:num->A"
    let q12 ← q r"\i. ring_of_int r ((c:num->int) i):A"
    let q13 ← q r"{i:num | i < n}"
    let q14 ← q r"ring_coset r (j:A->bool)"
    let q15 ← q r"quotient_ring r (j:A->bool)"
    let q16 ← q r"r:A ring"
    let v17 ← ISPECL [q16, q15, q14, q13, q12, q11] RING_HOMOMORPHISM_SUM_MUL
    let v18 ← BETA_RULE v17
    let q19 ← q r"!c. ring_coset r j
          (ring_sum r {i | i < n}
            (\i. ring_mul r (ring_of_int r (c i)) ((w:num->A) i))) =
        ring_sum (quotient_ring r j) {i | i < n}
          (\i. ring_mul (quotient_ring r j)
                 (ring_of_int (quotient_ring r j) (c i))
                 (ring_coset r j (w i)))"
    let q20 ← q r"ring_ideal r (j:A->bool)"
    let q21 ← q r"j = ideal_generated r {ring_of_num r m:A}"
    let q22 ← q r"m:num"
    let q23 ← q r"r:A ring"
    let v24 ← SPECL [q23, q22] RING_HOMOMORPHISM_INTEGER_MOD_QUOTIENT_RING
    prove
      r"!r:A ring n w m.
          free_basis (integer_ring,r) (ring_of_int r) n w
          ==> free_basis
               (integer_mod_ring m,
                quotient_ring r (ideal_generated r {ring_of_num r m}))
               (ring_of_int
                 (quotient_ring r (ideal_generated r {ring_of_num r m})))
               n (\i. ring_coset r (ideal_generated r {ring_of_num r m}) (w i))"
      (REPEAT STRIP_TAC THEN MP_TAC v24 THEN ABBREV_TAC q21 THEN DISCH_THEN (ASSUME_TAC o ((MATCH_MP RING_HOMOMORPHISM_RING_OF_INT) o CONJUNCT1)) THEN RULE_ASSUM_TAC (REWRITE_RULE [INTEGER_MOD_RING_OF_INT]) THEN SUBGOAL_THEN q20 ASSUME_TAC THENL [EXPAND_TAC "j" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_HOMOMORPHISM_RING_COSET)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FREE_BASIS_IN_CARRIER)) THEN SUBGOAL_THEN q19 (LABEL_TAC "lin") THENL [GEN_TAC THEN MP_TAC v18 THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, RING_OF_INT] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_RING_OF_INT th)])), ALL_TAC] THEN REWRITE_TAC [free_basis] THEN REPEAT CONJ_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN EXISTS_TAC q10 THEN ASM_SIMP_TAC [], ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, FORALL_IN_GSPEC] THEN X_GEN_TAC q9 THEN DISCH_TAC THEN EXISTS_TAC q8 THEN ASM_REWRITE_TAC [INTEGER_MOD_RING_CARRIER_REM] THEN REMOVE_THEN "lin" (SUBST1_TAC o (SYM o (SPEC q7))) THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC BASIS_COORDINATES_EXPAND THEN ASM_REWRITE_TAC [], ALL_TAC] THEN X_GEN_TAC q6 THEN STRIP_TAC THEN SUBGOAL_THEN q5 MP_TAC THENL [wPart Except.ok (rand o rand) RING_COSET_EQ_IDEAL THEN ASM_REWRITE_TAC [RING_SUM] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REMOVE_THEN "lin" (fun th => REWRITE_TAC [th]) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC QUOTIENT_RING_0 THEN ASM_REWRITE_TAC [], REMOVE_THEN "lin" (fun (_ : thm) => ALL_TAC)] THEN EXPAND_TAC "j" THEN ASM_SIMP_TAC [FREE_BASIS_IDEAL_GENERATED_NUM, RING_SUM, BASIS_COORDINATES_LINCOMB, RING_HOMOMORPHISM_INTEGER_RING_OF_INT, INTEGER_RING, IN_UNIV] THEN REWRITE_TAC [INTEGER_MOD_RING_CLAUSES] THEN ASM_MESON_TAC [lemma])

  let ALGEBRA_TRACE_QUOTIENT_RING_INTEGER_MOD ← prove
    r"!r:A ring n w m x.
        free_basis (integer_ring,r) (ring_of_int r) n w /\ x IN ring_carrier r
        ==> algebra_trace
              (integer_mod_ring m,
               quotient_ring r (ideal_generated r {ring_of_num r m}))
              (ring_of_int
                (quotient_ring r (ideal_generated r {ring_of_num r m})))
              (ring_coset r (ideal_generated r {ring_of_num r m}) x) =
            algebra_trace (integer_ring,r) (ring_of_int r) x rem &m"
    (REPEAT STRIP_TAC THEN MP_TAC (← SPECL [(← q r"r:A ring"), (← q r"m:num")] RING_HOMOMORPHISM_INTEGER_MOD_QUOTIENT_RING) THEN FIRST_ASSUM (MP_TAC o ((SPEC (← q r"m:num")) o (MATCH_MP FREE_BASIS_QUOTIENT_RING_INTEGER_MOD))) THEN ABBREV_TAC (← q r"j = ideal_generated r {ring_of_num r m:A}") THEN REWRITE_TAC [(← GSYM o_DEF), (← GSYM INTEGER_MOD_RING_OF_INT)] THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_ideal r (j:A->bool)") ASSUME_TAC THENL [EXPAND_TAC "j" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_int r:int->A"), (← q r"ring_of_int (quotient_ring r (j:A->bool))"), (← q r"ring_of_int (integer_mod_ring m)"), (← q r"ring_coset r (j:A->bool)"), (← q r"integer_ring"), (← q r"r:A ring"), (← q r"integer_mod_ring m"), (← q r"quotient_ring r (j:A->bool)"), (← q r"n:num"), (← q r"w:num->A"), (← q r"x:A")] ALGEBRA_TRACE_NORM_HOMOMORPHIC_IMAGE) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, RING_HOMOMORPHISM_RING_COSET])

  let BASIS_DISCRIMINANT_QUOTIENT_RING_INTEGER_MOD ← prove
    r"!r:A ring n w m.
        free_basis (integer_ring,r) (ring_of_int r) n w
        ==> basis_discriminant
              (integer_mod_ring m,
               quotient_ring r (ideal_generated r {ring_of_num r m}))
              (ring_of_int
                (quotient_ring r (ideal_generated r {ring_of_num r m})))
              n (\i. ring_coset r (ideal_generated r {ring_of_num r m}) (w i)) =
            basis_discriminant (integer_ring,r) (ring_of_int r) n w rem &m"
    (REPEAT STRIP_TAC THEN MP_TAC (← SPECL [(← q r"r:A ring"), (← q r"m:num")] RING_HOMOMORPHISM_INTEGER_MOD_QUOTIENT_RING) THEN FIRST_ASSUM (MP_TAC o ((SPEC (← q r"m:num")) o (MATCH_MP FREE_BASIS_QUOTIENT_RING_INTEGER_MOD))) THEN ABBREV_TAC (← q r"j = ideal_generated r {ring_of_num r m:A}") THEN REWRITE_TAC [(← GSYM o_DEF), (← GSYM INTEGER_MOD_RING_OF_INT)] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC BASIS_DISCRIMINANT_HOMOMORPHIC_IMAGE THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, INTEGER_MOD_RING_OF_INT] THEN MATCH_MP_TAC RING_HOMOMORPHISM_RING_COSET THEN EXPAND_TAC "j" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED])

  let ALGEBRA_TRACE_NILPOTENT_INTEGER_MOD ← prove
    r"!r:A ring n w p x m.
        free_basis (integer_ring,r) (ring_of_int r) n w /\ prime p /\
        x IN ring_carrier r /\ ~(m = 0) /\
        ring_pow r x m IN ideal_generated r {ring_of_num r p}
        ==> &p divides algebra_trace (integer_ring,r) (ring_of_int r) x"
    (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"j = ideal_generated r {ring_of_num r p:A}") THEN MP_TAC (← ISPECL [(← q r"ring_of_int(quotient_ring r (j:A->bool))"), (← q r"integer_mod_ring p"), (← q r"quotient_ring r (j:A->bool)"), (← q r"n:num"), (← q r"\i. ring_coset r j ((w:num->A) i)"), (← q r"ring_coset r j (x:A)")] ALGEBRA_TRACE_NILPOTENT) THEN EXPAND_TAC "j" THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"p:num"), (← q r"x:A")] ALGEBRA_TRACE_QUOTIENT_RING_INTEGER_MOD) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN ASM_SIMP_TAC [FREE_BASIS_QUOTIENT_RING_INTEGER_MOD, RING_HOMOMORPHISM_INTEGER_MOD_QUOTIENT_RING, FIELD_IMP_INTEGRAL_DOMAIN, FIELD_INTEGER_MOD_RING, INTEGER_MOD_RING_CLAUSES, INT_REM_EQ_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [RING_NILPOTENT] THEN SUBGOAL_THEN (← q r"ring_ideal r (j:A->bool)") ASSUME_TAC THENL [EXPAND_TAC "j" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_HOMOMORPHISM_RING_COSET)) THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], EXISTS_TAC (← q r"m:num")] THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← GSYM (← MATCH_MP RING_HOMOMORPHISM_POW th))])) THEN ASM_SIMP_TAC [QUOTIENT_RING_0, RING_COSET_EQ_IDEAL, RING_POW])

  let ALGEBRA_TRACE_INTEGER_MOD_COMAXIMAL ← prove
    r"!r:A ring n w p P Q.
        free_basis (integer_ring,r) (ring_of_int r) n w /\ prime p /\
        maximal_ideal r P /\ ring_ideal r Q /\
        ring_setadd r P Q = ring_carrier r /\
        P INTER Q = ideal_generated r {ring_of_num r p}
        ==> ?x. x IN Q /\
                ~(&p divides
                  algebra_trace (integer_ring,r) (ring_of_int r) x)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"integer_mod_ring p"), (← q r"r:A ring"), (← q r"ring_of_int(quotient_ring r (P INTER Q:A->bool))"), (← q r"n:num"), (← q r"\i. ring_coset r (P INTER Q:A->bool) ((w:num->A) i)"), (← q r"P:A->bool"), (← q r"Q:A->bool")] ALGEBRA_TRACE_QUOTIENT_COMAXIMAL_NONZERO) THEN ASM_SIMP_TAC [FIELD_INTEGER_MOD_RING, FINITE_INTEGER_MOD_RING, PRIME_IMP_NZ, RING_HOMOMORPHISM_INTEGER_MOD_QUOTIENT_RING, FREE_BASIS_QUOTIENT_RING_INTEGER_MOD] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"x:A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"p:num"), (← q r"x:A")] ALGEBRA_TRACE_QUOTIENT_RING_INTEGER_MOD) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST_ALL_TAC THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun z1 => (do let z2 ← (do let z3 ← (pure z1); pure (concl z3)); pure (is_neg z2))))) THEN REWRITE_TAC [INTEGER_MOD_RING_CLAUSES, INT_REM_EQ_0])

  let NUMBER_FIELD_DISCRIMINANT_DIVIDES ← prove
    r"!k:A ring p.
        number_field k /\ prime p
        ==> (&p divides number_field_discriminant k <=>
             ?x. ring_nilpotent
                   (quotient_ring (ring_of_integers k)
                      (ideal_generated (ring_of_integers k) {ring_of_num k p}))
                   x /\
                 ~(x = ring_0
                        (quotient_ring (ring_of_integers k)
                          (ideal_generated (ring_of_integers k)
                             {ring_of_num k p}))))"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP RING_OF_INTEGERS_FREE)) THEN ABBREV_TAC (← q r"n = extension_degree (subfield_generated k {ring_0 k},k:A ring) I") THEN DISCH_THEN (X_CHOOSE_TAC (← q r"w:num->A")) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A")] NUMBER_FIELD_DISCRIMINANT_BASIS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"p:num")] BASIS_DISCRIMINANT_QUOTIENT_RING_INTEGER_MOD) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"p:num")] FREE_BASIS_QUOTIENT_RING_INTEGER_MOD) THEN MP_TAC (← CONJUNCT1 (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:num")] RING_HOMOMORPHISM_INTEGER_MOD_QUOTIENT_RING)) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"j = ideal_generated (ring_of_integers k) {ring_of_num k p:A}") THEN REWRITE_TAC [(← GSYM INT_REM_EQ_0)] THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"integer_mod_ring p"), (← q r"quotient_ring (ring_of_integers k) (j:A->bool)"), (← q r"ring_of_int (quotient_ring (ring_of_integers k) (j:A->bool))"), (← q r"n:num"), (← q r"\i. ring_coset (ring_of_integers k) j ((w:num->A) i)")] BASIS_DISCRIMINANT_EQ_0_FINITE) THEN ASM_SIMP_TAC [FIELD_INTEGER_MOD_RING, FINITE_INTEGER_MOD_RING, PRIME_IMP_NZ, INTEGER_MOD_RING_CLAUSES])

  let NUMBER_FIELD_RAMIFIED_DISCRIMINANT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"x IN s ==> s SUBSET t ==> (x:A) IN t")
    prove
      r"!k:A ring p.
          number_field k /\ prime p
          ==> ((?P. prime_ideal (ring_of_integers k) P /\ ring_of_num k p IN P /\
                    1 < ramification_index (integer_ring,ring_of_integers k)
                          (ring_of_int k) P) <=>
               &p divides number_field_discriminant k)"
      (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_DISCRIMINANT_DIVIDES] THEN ABBREV_TAC (← q r"j = ideal_generated (ring_of_integers k) {ring_of_num k p:A}") THEN SUBGOAL_THEN (← q r"ring_of_num k p IN ring_carrier(ring_of_integers k) /\
      ~(ring_of_num k p = ring_0 (k:A ring))") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:num")] RING_OF_NUM) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN REWRITE_TAC [RING_OF_NUM_EQ_0] THEN RULE_ASSUM_TAC (REWRITE_RULE [number_field]) THEN ASM_SIMP_TAC [DIVIDES_ZERO, PRIME_IMP_NZ], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers k) (j:A->bool) /\ ~(j = {ring_0 k}) /\
      !P. prime_ideal (ring_of_integers k) P
          ==> (j SUBSET P <=> ring_of_num k p IN P)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "j" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_num k p:A")] IDEAL_GENERATED_EQ_0) THEN REWRITE_TAC [RING_OF_INTEGERS, (← ASSUME (← q r"ring_of_num k p IN ring_carrier(ring_of_integers (k:A ring))")), (← ASSUME (← q r"~(ring_of_num k p = ring_0 (k:A ring))"))] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN REPEAT STRIP_TAC THEN EQ_TAC THENL [MATCH_MP_TAC r1 THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN ASM_REWRITE_TAC [SING_SUBSET, IN_SING], DISCH_TAC THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, SING_SUBSET]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"j:A->bool")] DEDEKIND_QUOTIENT_RING_REDUCED) THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_OF_INTEGERS] THEN DISCH_THEN (MP_TAC o (AP_TERM (← q r"(~)"))) THEN REWRITE_TAC [NOT_FORALL_THM, NOT_IMP, NOT_LE] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN ASM_CASES_TAC (← q r"prime_ideal (ring_of_integers k) (P:A->bool)") THEN ASM_REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"ring_of_num k p IN (P:A->bool)") THEN ASM_REWRITE_TAC [] THENL [SUBGOAL_THEN (← q r"~(P = {ring_0 k:A})") (fun th => REWRITE_TAC [th]) THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"ring_of_num k p IN {ring_0 k:A}") THEN ASM_REWRITE_TAC [IN_SING], MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"p:num")] RAMIFICATION_INDEX_PRIME) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC []], ASM_CASES_TAC (← q r"P = {ring_0 k:A}") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"j:A->bool")] IDEAL_VALUATION_EQ_0) THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_OF_INTEGERS] THEN ARITH_TAC])

  let NUMBER_FIELD_FINITE_RAMIFIED_PRIMES ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"a /\ (b ==> c) ==> (a <=> b) ==> c")
    prove
      r"!k:A ring.
          number_field k
          ==> FINITE {p | prime p /\
                          ?P. prime_ideal (ring_of_integers k) P /\
                              ring_of_num k p IN P /\
                              1 < ramification_index
                                  (integer_ring,ring_of_integers k) (ring_of_int
                                      k) P}"
      (REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{p | p <= num_of_int(abs(number_field_discriminant (k:A ring)))}") THEN REWRITE_TAC [FINITE_NUMSEG_LE, SUBSET, IN_ELIM_THM] THEN X_GEN_TAC (← q r"p:num") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"p:num")] NUMBER_FIELD_RAMIFIED_DISCRIMINANT) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [EXISTS_TAC (← q r"P:A->bool") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (MP_TAC o (MATCH_MP INT_DIVIDES_LE)) THEN ASM_SIMP_TAC [NUMBER_FIELD_DISCRIMINANT_NONZERO, INT_ABS_NUM] THEN REWRITE_TAC [(← GSYM INT_OF_NUM_LE)] THEN SIMP_TAC [INT_OF_NUM_OF_INT, INT_ABS_POS])

  -- @@RETURN BEGIN
  return { RING_HOMOMORPHISM_INTEGER_MOD_QUOTIENT_RING, FREE_BASIS_IDEAL_GENERATED_NUM,
           FREE_BASIS_QUOTIENT_RING_INTEGER_MOD, ALGEBRA_TRACE_QUOTIENT_RING_INTEGER_MOD,
           BASIS_DISCRIMINANT_QUOTIENT_RING_INTEGER_MOD,
           ALGEBRA_TRACE_NILPOTENT_INTEGER_MOD, ALGEBRA_TRACE_INTEGER_MOD_COMAXIMAL,
           NUMBER_FIELD_DISCRIMINANT_DIVIDES, NUMBER_FIELD_RAMIFIED_DISCRIMINANT,
           NUMBER_FIELD_FINITE_RAMIFIED_PRIMES }
  -- @@RETURN END

end HolANT.Ramification
