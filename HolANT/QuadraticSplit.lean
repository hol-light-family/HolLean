/- ========================================================================= -/
/- ANT: The decomposition law in a quadratic field k = Q(x), x^2 = d ...   -/
/- ========================================================================= -/
/- File: HolANT/QuadraticSplit.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/quadratic_split.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antquadraticsplitdiff; the rest is by hand.  Its `needs` closure is
  Library/integer.ml, Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/products.ml, ANT/algmisc.ml, ANT/ideal_arith.ml, ANT/integral.ml, ANT/dedekind.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/prime_split.ml, ANT/norm_index.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/finite_field_trace.ml, ANT/ramification.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/classgroup.ml, ANT/relative_split.ml, ANT/relative_degree.ml, ANT/nf_valuation.ml, ANT/integrality.ml, ANT/dedekind_kummer.ml, ANT/quadratic.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.QuadraticSplit fills them).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left; where a proof applies rules that print or use
  counters (MESON, ARITH_RULE, ...) they are bound first, in OCaml's order.
-/

import HolANT.Prelude
import HolLibrary.Integer
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
import HolANT.IdealArith
import HolANT.Integral
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
import HolANT.Ramification
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.Classgroup
import HolANT.RelativeSplit
import HolANT.RelativeDegree
import HolANT.NfValuation
import HolANT.Integrality
import HolANT.DedekindKummer
import HolANT.Quadratic

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.Algmisc
open HolANT.IdealArith
open HolANT.Integral
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
open HolANT.Ramification
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.Classgroup
open HolANT.RelativeSplit
open HolANT.RelativeDegree
open HolANT.NfValuation
open HolANT.Integrality
open HolANT.DedekindKummer
open HolANT.Quadratic

namespace HolANT.QuadraticSplit

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ARITH_EQ COEFF_POLY_ADD COEFF_POLY_CONST COEFF_POLY_LMUL COEFF_POLY_SUB
   COEFF_POLY_VAR COEFF_POLY_VARPOW COPRIME_PRIME_PRIME
   DEDEKIND_KUMMER_LINEAR_IDEAL DEDEKIND_KUMMER_Q DEDEKIND_RING_OF_INTEGERS
   DIVIDES_ZERO EXP_1 EXTENSION FIELD_IMP_INTEGRAL_DOMAIN
   FIELD_IMP_NONTRIVIAL_RING FIELD_INTEGER_MOD_RING FIELD_MUL_RINV FINITE_DELETE
   FINITE_EMPTY FINITE_INSERT FINITE_SING FORALL_AND_THM FORALL_IN_INSERT
   FORALL_UNWIND_THM2 IDEAL_GENERATED_INC_GEN IDEAL_GENERATED_PAIR_EQ
   IDEAL_GENERATED_SING IDEAL_POW_1 IDEAL_POW_SUBSET_PRIME_IDEAL
   IDEAL_PRODUCT_INSERT IDEAL_PRODUCT_SING IDEAL_VALUATION_IDEAL_POW
   IDEAL_VALUATION_PRIME IMP_CONJ INTEGER_MOD_RING_CHAR INTEGER_MOD_RING_OF_INT
   INTEGER_RING INTEGRAL_DOMAIN_MUL_LCANCEL INTEGRAL_ELEMENT_QUADRATIC
   INT_ABS_NUM INT_ADD_LID INT_CONG_REFL INT_DIVIDES_ONE INT_DIVISION
   INT_DIV_MUL INT_MUL_LZERO INT_OF_NUM_EQ INT_POW_2 INT_REM_EQ INT_REM_EQ_0
   INT_REM_LT IN_DELETE IN_ELIM_THM IN_INSERT IN_INTEGER_MOD_RING_CARRIER
   IN_RING_IDEAL_0 IN_RING_IDEAL_NEG IN_SING IN_SUBRING_1 IN_SUBRING_ADD
   IN_SUBRING_INT IN_SUBRING_MUL IN_SUBRING_NEG IN_SUBRING_NUM IN_SUBRING_SUB
   IN_UNIV I_O_ID I_THM LEFT_IMP_EXISTS_THM LE_MULT2 MONIC_X_MINUS_A
   MULT_CLAUSES MULT_EQ_0 NOT_EXISTS_THM NOT_IN_EMPTY NOT_TRIVIAL_INTEGER_RING
   NSUM_DELETE NSUM_EQ_0_IFF NUMBER_FIELD_FUNDAMENTAL_IDENTITY_Q
   NUMBER_FIELD_IMP_FIELD NUMBER_FIELD_PRIME_FACTORIZATION_Q
   NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q NUMBER_FIELD_PRIME_IDEAL_PROD_EQ
   NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q NUMBER_FIELD_RAMIFIED_DISCRIMINANT
   NUMBER_FIELD_RING_OF_NUM_EQ_0 ODD_EXISTS POLY_COMPOSE_HOMOMORPHISM_CONST
   POLY_COMPOSE_HOMOMORPHISM_VAR POLY_CONST POLY_DEG_2_IRREDUCIBLE
   POLY_DEG_EQ_COEFF POLY_DEG_X_MINUS_A : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (POLY_EXTEND_CONST POLY_EXTEND_EVALUATE POLY_EXTEND_VAR POLY_RING_CLAUSES
   POLY_VAR_UNIV PRIME_2 PRIME_IDEAL_IMP_SUBSET PRIME_IMP_NZ
   PRIME_IMP_RING_IDEAL PRIME_ODD QUADRATIC_FIELD_INTEGRAL_BASIS
   RAMIFICATION_INDEX_PRIME RIGHT_FORALL_IMP_THM RING_0 RING_1 RING_ADD
   RING_ADD_LZERO RING_ADD_RZERO RING_HOMOMORPHISM_ADD RING_HOMOMORPHISM_I
   RING_HOMOMORPHISM_INTEGER_RING_OF_INT RING_HOMOMORPHISM_MUL
   RING_HOMOMORPHISM_NEG RING_HOMOMORPHISM_POLY_CONST
   RING_HOMOMORPHISM_POLY_EXTEND RING_HOMOMORPHISM_POLY_RINGS
   RING_HOMOMORPHISM_POW RING_HOMOMORPHISM_SUB RING_IDEAL_IDEAL_GENERATED
   RING_IDEAL_IDEAL_POW RING_IDEAL_IMP_SUBSET RING_INV
   RING_IRREDUCIBLE_X_MINUS_A RING_MUL RING_MUL_LZERO RING_MUL_RID
   RING_MUL_RZERO RING_NEG RING_NEG_0 RING_NEG_EQ RING_OF_INT RING_OF_INTEGERS
   RING_OF_INTEGERS_CARRIER RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q
   RING_OF_INTEGERS_SUBRING RING_OF_INTEGERS_SUBSET RING_OF_INT_0 RING_OF_INT_1
   RING_OF_INT_ADD RING_OF_INT_EQ_0 RING_OF_INT_IN_RING_OF_INTEGERS
   RING_OF_INT_MUL RING_OF_INT_NEG RING_OF_INT_OF_NUM RING_OF_INT_POW
   RING_OF_INT_SUB RING_OF_NUM RING_OF_NUM_1 RING_OF_NUM_ADD RING_OF_NUM_EQ_0
   RING_OF_NUM_MUL RING_POLYNOMIAL_IMP_POWERSERIES RING_POW RING_POWERSERIES_VAR
   RING_POW_1 RING_POW_2 RING_PRODUCT_CLAUSES RING_PRODUCT_SING RING_SETADD
   RING_SUB RING_SUB_EQ_0 RING_SUB_LZERO RING_SUB_RZERO RING_SUM_CLAUSES
   RING_SUM_SING SING_SUBSET SUBRING_GENERATED_INC_GEN SUBRING_GENERATED_MINIMAL
   SUBRING_SUBRING_GENERATED SUBSET SUBSET_ANTISYM SUBSET_REFL TRIVIAL_RING_10
   free_basis int_congruent int_divides monic num_coprime number_field poly_eval
   ring_div ring_divides ring_setadd ring_sub : thm)
  deriving Inhabited

/-- What quadratic_split.ml uses from Session besides theorems. -/
structure QuadraticSplitDeps where
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
  core2 : CoreThms2

/-- RingTheory's `wPart` (copied verbatim).  `W(MP_TAC o PART_MATCH f th o g
    o snd)`: match `th`'s part `f` against the part `g` of the goal, and
    MP_TAC the instance. -/
def wPart [HolBase] (g : term → Except String term) (f : term → Except String term)
    (th : thm) : tactic := fun gl =>
  ExceptT.run do
    let t ← liftExcept (g gl.2)
    ExceptT.mk (MP_TAC (← PART_MATCH f th t) gl)



/- ---------------------------------------------------------------------- -/
/- quadratic_split.ml phrases from line 62 to 679                         -/
/- ---------------------------------------------------------------------- -/

structure QuadraticSplit01 where
  -- @@FIELDS
  QUADRATIC_POLY_IN_CARRIER : thm
  QUADRATIC_POLY_DEG : thm
  QUADRATIC_POLY_EXTEND : thm
  QUADRATIC_POLY_HOMOMORPHIC_IMAGE : thm
  QUADRATIC_POLY_FACTOR : thm
  QUADRATIC_POLY_INTEGER_ROOT : thm
  QUADRATIC_DEDEKIND_KUMMER_SPLIT_PRIMES : thm
  QUADRATIC_DEDEKIND_KUMMER_RAMIFIED_PRIME : thm
  QUADRATIC_DEDEKIND_KUMMER_SPLIT : thm
  QUADRATIC_DEDEKIND_KUMMER_INERT : thm
  QUADRATIC_FIELD_RING_OF_INTEGERS : thm
  RING_OF_INTEGERS_SETADD_SUBRING_GENERATED : thm
  RING_OF_INTEGERS_SETADD_SUBRING_GENERATED_LINEAR : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupQuadraticSplit01 [HolBase] (D : QuadraticSplitDeps) :
    ExceptT String IO QuadraticSplit01 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, INTEGER_RULE, MESON, MESON_TAC,
        RING_RULE, TAUT, .. } := D
  let { ARITH_EQ, COEFF_POLY_ADD, COEFF_POLY_CONST, COEFF_POLY_LMUL, COEFF_POLY_SUB,
        COEFF_POLY_VAR, COEFF_POLY_VARPOW, DEDEKIND_KUMMER_LINEAR_IDEAL,
        DEDEKIND_KUMMER_Q, DIVIDES_ZERO, EXTENSION, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_IMP_NONTRIVIAL_RING, FIELD_INTEGER_MOD_RING, FIELD_MUL_RINV,
        FINITE_EMPTY, FINITE_INSERT, FINITE_SING, FORALL_AND_THM, FORALL_IN_INSERT,
        FORALL_UNWIND_THM2, IDEAL_POW_1, IDEAL_PRODUCT_INSERT, IDEAL_PRODUCT_SING,
        IMP_CONJ, INTEGER_MOD_RING_CHAR, INTEGER_MOD_RING_OF_INT, INTEGER_RING,
        INTEGRAL_ELEMENT_QUADRATIC, INT_OF_NUM_EQ, INT_REM_EQ, INT_REM_LT, IN_ELIM_THM,
        IN_INSERT, IN_INTEGER_MOD_RING_CARRIER, IN_RING_IDEAL_0, IN_SING,
        IN_SUBRING_ADD, IN_SUBRING_INT, IN_SUBRING_MUL, IN_UNIV, I_O_ID, I_THM,
        LEFT_IMP_EXISTS_THM, MONIC_X_MINUS_A, NOT_IN_EMPTY, NOT_TRIVIAL_INTEGER_RING,
        NUMBER_FIELD_IMP_FIELD, POLY_COMPOSE_HOMOMORPHISM_CONST,
        POLY_COMPOSE_HOMOMORPHISM_VAR, POLY_CONST, POLY_DEG_2_IRREDUCIBLE,
        POLY_DEG_EQ_COEFF, POLY_DEG_X_MINUS_A, .. } := D.core1
  let { POLY_EXTEND_CONST, POLY_EXTEND_EVALUATE, POLY_EXTEND_VAR, POLY_RING_CLAUSES,
        POLY_VAR_UNIV, PRIME_IMP_NZ, QUADRATIC_FIELD_INTEGRAL_BASIS,
        RIGHT_FORALL_IMP_THM, RING_0, RING_1, RING_ADD, RING_ADD_LZERO, RING_ADD_RZERO,
        RING_HOMOMORPHISM_ADD, RING_HOMOMORPHISM_I,
        RING_HOMOMORPHISM_INTEGER_RING_OF_INT, RING_HOMOMORPHISM_MUL,
        RING_HOMOMORPHISM_NEG, RING_HOMOMORPHISM_POLY_CONST,
        RING_HOMOMORPHISM_POLY_EXTEND, RING_HOMOMORPHISM_POLY_RINGS,
        RING_HOMOMORPHISM_POW, RING_HOMOMORPHISM_SUB, RING_IDEAL_IDEAL_GENERATED,
        RING_IDEAL_IDEAL_POW, RING_IDEAL_IMP_SUBSET, RING_INV,
        RING_IRREDUCIBLE_X_MINUS_A, RING_MUL, RING_MUL_RID, RING_MUL_RZERO, RING_NEG,
        RING_NEG_0, RING_NEG_EQ, RING_OF_INT, RING_OF_INTEGERS,
        RING_OF_INTEGERS_CARRIER, RING_OF_INTEGERS_SUBRING, RING_OF_INTEGERS_SUBSET,
        RING_OF_INT_ADD, RING_OF_INT_EQ_0, RING_OF_INT_IN_RING_OF_INTEGERS,
        RING_OF_INT_MUL, RING_OF_INT_NEG, RING_OF_INT_POW, RING_OF_INT_SUB,
        RING_OF_NUM, RING_OF_NUM_EQ_0, RING_POLYNOMIAL_IMP_POWERSERIES, RING_POW,
        RING_POWERSERIES_VAR, RING_POW_1, RING_POW_2, RING_PRODUCT_CLAUSES,
        RING_PRODUCT_SING, RING_SETADD, RING_SUB, RING_SUB_EQ_0, RING_SUB_LZERO,
        RING_SUB_RZERO, RING_SUM_CLAUSES, RING_SUM_SING, SING_SUBSET,
        SUBRING_GENERATED_INC_GEN, SUBRING_GENERATED_MINIMAL,
        SUBRING_SUBRING_GENERATED, SUBSET, SUBSET_ANTISYM, TRIVIAL_RING_10, free_basis,
        monic, number_field, poly_eval, ring_div, ring_setadd, ring_sub, .. } := D.core2
  -- @@SCOPE END

  let QUADRATIC_POLY_IN_CARRIER ← prove
    r"!r:A ring b c.
        b IN ring_carrier r /\ c IN ring_carrier r
        ==> ring_sub (poly_ring r (:1))
              (ring_pow (poly_ring r (:1)) (poly_var r one) 2)
              (ring_add (poly_ring r (:1))
                (ring_mul (poly_ring r (:1)) (poly_const r b) (poly_var r one))
                (poly_const r c)) IN ring_carrier(poly_ring r (:1))"
    (SIMP_TAC [RING_SUB, RING_POW, RING_ADD, RING_MUL, POLY_VAR_UNIV, POLY_CONST])

  let QUADRATIC_POLY_DEG ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"d = 0"
    let q2 ← q r"d = 1"
    let q3 ← q r"d = 2"
    let q4 ← q r"!d. coeff d (poly_sub r (poly_pow r (poly_var r one) 2)
                  (poly_add r (poly_mul r (poly_const r b) (poly_var r one))
                              (poly_const r c))) =
        if d = 2 then ring_1 r else if d = 1 then ring_neg r b
        else if d = 0 then ring_neg r c else ring_0 r:A"
    let q5 ← q r"c:A"
    let q6 ← q r"b:A"
    let q7 ← q r"r:A ring"
    let v8 ← ISPECL [q7, q6, q5] QUADRATIC_POLY_IN_CARRIER
    let q9 ← q r"poly_deg (r:A ring) p = 2 /\ coeff 2 p = ring_1 r
    ==> poly_deg r p = 2 /\ monic r p"
    let r10 ← MESON [monic] q9
    prove
      r"!r:A ring b c.
          ~trivial_ring r /\ b IN ring_carrier r /\ c IN ring_carrier r
          ==> poly_deg r
               (ring_sub (poly_ring r (:1))
                 (ring_pow (poly_ring r (:1)) (poly_var r one) 2)
                 (ring_add (poly_ring r (:1))
                   (ring_mul (poly_ring r (:1)) (poly_const r b)
                     (poly_var r one))
                   (poly_const r c))) = 2 /\
              monic r
               (ring_sub (poly_ring r (:1))
                 (ring_pow (poly_ring r (:1)) (poly_var r one) 2)
                 (ring_add (poly_ring r (:1))
                   (ring_mul (poly_ring r (:1)) (poly_const r b)
                     (poly_var r one))
                   (poly_const r c)))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC r10 THEN MP_TAC v8 THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [POLY_RING_CLAUSES, IN_ELIM_THM] THEN STRIP_TAC THEN SUBGOAL_THEN q4 ASSUME_TAC THENL [GEN_TAC THEN ASM_SIMP_TAC [COEFF_POLY_SUB, COEFF_POLY_ADD, COEFF_POLY_LMUL, COEFF_POLY_VAR, COEFF_POLY_VARPOW, COEFF_POLY_CONST, RING_POWERSERIES_VAR] THEN MAP_EVERY ASM_CASES_TAC [q3, q2, q1] THEN ASM_REWRITE_TAC [ARITH_EQ] THEN ASM_SIMP_TAC [RING_MUL_RZERO, RING_MUL_RID, RING_ADD_LZERO, RING_ADD_RZERO, RING_SUB_RZERO, RING_SUB_LZERO, RING_1, RING_0, RING_NEG, RING_NEG_0, ring_sub], ASM_REWRITE_TAC [ARITH_EQ] THEN MATCH_MP_TAC POLY_DEG_EQ_COEFF THEN ASM_SIMP_TAC [RING_POLYNOMIAL_IMP_POWERSERIES] THEN CONJ_TAC THENL [GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN ARITH_TAC, ASM_MESON_TAC [TRIVIAL_RING_10]]])

  let QUADRATIC_POLY_EXTEND ← prove
    r"!r:A ring t:B ring h z b c.
        ring_homomorphism(r,t) h /\ z IN ring_carrier t /\
        b IN ring_carrier r /\ c IN ring_carrier r
        ==> poly_extend (r,t) h (\v. z)
             (ring_sub (poly_ring r (:1))
               (ring_pow (poly_ring r (:1)) (poly_var r one) 2)
               (ring_add (poly_ring r (:1))
                 (ring_mul (poly_ring r (:1)) (poly_const r b)
                   (poly_var r one))
                 (poly_const r c))) =
            ring_sub t (ring_pow t z 2)
                       (ring_add t (ring_mul t (h b) z) (h c))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"t:B ring"), (← q r"(:1)"), (← q r"h:A->B"), (← q r"\v:1. (z:B)")] RING_HOMOMORPHISM_POLY_EXTEND) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_SUB th), (← MATCH_MP RING_HOMOMORPHISM_ADD th), (← MATCH_MP RING_HOMOMORPHISM_MUL th), (← MATCH_MP RING_HOMOMORPHISM_POW th), RING_POW, RING_ADD, RING_MUL, POLY_VAR_UNIV, POLY_CONST])) THEN ASM_SIMP_TAC [POLY_EXTEND_VAR, POLY_EXTEND_CONST])

  let QUADRATIC_POLY_HOMOMORPHIC_IMAGE ← prove
    r"!r:A ring s:B ring f b c.
        ring_homomorphism(r,s) f /\ b IN ring_carrier r /\ c IN ring_carrier r
        ==> f o ring_sub (poly_ring r (:1))
                  (ring_pow (poly_ring r (:1)) (poly_var r one) 2)
                  (ring_add (poly_ring r (:1))
                    (ring_mul (poly_ring r (:1)) (poly_const r b)
                      (poly_var r one))
                    (poly_const r c)) =
            ring_sub (poly_ring s (:1))
              (ring_pow (poly_ring s (:1)) (poly_var s one) 2)
              (ring_add (poly_ring s (:1))
                (ring_mul (poly_ring s (:1)) (poly_const s (f b))
                  (poly_var s one))
                (poly_const s (f c)))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"f:A->B"), (← q r"(:1)")] RING_HOMOMORPHISM_POLY_RINGS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← BETA_RULE (← MATCH_MP RING_HOMOMORPHISM_SUB th)) THEN MP_TAC (← BETA_RULE (← MATCH_MP RING_HOMOMORPHISM_ADD th)) THEN MP_TAC (← BETA_RULE (← MATCH_MP RING_HOMOMORPHISM_MUL th)) THEN MP_TAC (← BETA_RULE (← MATCH_MP RING_HOMOMORPHISM_POW th)))) THEN REPEAT DISCH_TAC THEN ASM_SIMP_TAC [RING_POW, RING_ADD, RING_MUL, POLY_VAR_UNIV, POLY_CONST] THEN ASM_SIMP_TAC [(← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"f:A->B")] POLY_COMPOSE_HOMOMORPHISM_VAR), (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"f:A->B")] POLY_COMPOSE_HOMOMORPHISM_CONST)])

  let QUADRATIC_POLY_FACTOR ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!R:B ring x a b.
        ring_sub R (ring_pow R x 2)
          (ring_add R (ring_mul R (ring_add R a b) x)
                      (ring_neg R (ring_mul R a b))) =
        ring_mul R (ring_sub R x a) (ring_sub R x b)")
    prove
      r"!r:A ring r1 r2.
          r1 IN ring_carrier r /\ r2 IN ring_carrier r
          ==> ring_sub (poly_ring r (:1))
                (ring_pow (poly_ring r (:1)) (poly_var r one) 2)
                (ring_add (poly_ring r (:1))
                  (ring_mul (poly_ring r (:1))
                    (poly_const r (ring_add r r1 r2)) (poly_var r one))
                  (poly_const r (ring_neg r (ring_mul r r1 r2)))) =
              ring_mul (poly_ring r (:1))
                (poly_sub r (poly_var r one) (poly_const r r1))
                (poly_sub r (poly_var r one) (poly_const r r2))"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"(:1)")] RING_HOMOMORPHISM_POLY_CONST) THEN DISCH_THEN (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_ADD th), (← MATCH_MP RING_HOMOMORPHISM_NEG th), (← MATCH_MP RING_HOMOMORPHISM_MUL th), RING_MUL])) THEN REWRITE_TAC [(← GSYM (← ISPECL [(← q r"r:A ring"), (← q r"(:1)")] (← (do let z2 ← (pure (CONJUNCTS POLY_RING_CLAUSES)); let z3 ← (pure 5); liftExcept (el z3 z2)))))] THEN MP_TAC (← ISPECL [(← q r"poly_ring (r:A ring) (:1)"), (← q r"poly_var r one:(1->num)->A"), (← q r"poly_const r r1:(1->num)->A"), (← q r"poly_const r r2:(1->num)->A")] r1) THEN ASM_SIMP_TAC [POLY_VAR_UNIV, POLY_CONST])

  let QUADRATIC_POLY_INTEGER_ROOT ← prove
    r"!k:A ring a b c p.
        a IN ring_carrier k /\
        ring_pow k a 2 =
        ring_add k (ring_mul k (ring_of_int k b) a) (ring_of_int k c)
        ==> ?m. m IN ring_carrier(poly_ring integer_ring (:1)) /\
                monic integer_ring m /\ poly_deg integer_ring m = 2 /\
                poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m =
                ring_0 k /\
                ring_of_int (integer_mod_ring p) o m =
                ring_sub (poly_ring (integer_mod_ring p) (:1))
                 (ring_pow (poly_ring (integer_mod_ring p) (:1))
                   (poly_var (integer_mod_ring p) one) 2)
                 (ring_add (poly_ring (integer_mod_ring p) (:1))
                   (ring_mul (poly_ring (integer_mod_ring p) (:1))
                     (poly_const (integer_mod_ring p)
                       (ring_of_int (integer_mod_ring p) b))
                     (poly_var (integer_mod_ring p) one))
                   (poly_const (integer_mod_ring p)
                     (ring_of_int (integer_mod_ring p) c)))"
    (REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"ring_sub (poly_ring integer_ring (:1))
     (ring_pow (poly_ring integer_ring (:1)) (poly_var integer_ring one) 2)
     (ring_add (poly_ring integer_ring (:1))
       (ring_mul (poly_ring integer_ring (:1)) (poly_const integer_ring b)
         (poly_var integer_ring one))
       (poly_const integer_ring c))") THEN SIMP_TAC [QUADRATIC_POLY_IN_CARRIER, QUADRATIC_POLY_DEG, QUADRATIC_POLY_EXTEND, INTEGER_RING, IN_UNIV, (← ISPECL [(← q r"integer_ring"), (← q r"integer_mod_ring p"), (← q r"ring_of_int (integer_mod_ring p)")] QUADRATIC_POLY_HOMOMORPHIC_IMAGE), RING_HOMOMORPHISM_INTEGER_RING_OF_INT, NOT_TRIVIAL_INTEGER_RING, (← ASSUME (← q r"(a:A) IN ring_carrier k"))] THEN SIMP_TAC [RING_SUB_EQ_0, RING_POW, RING_ADD, RING_MUL, RING_OF_INT, (← ASSUME (← q r"(a:A) IN ring_carrier k"))] THEN ASM_REWRITE_TAC [])

  let QUADRATIC_DEDEKIND_KUMMER_SPLIT_PRIMES ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r19 ← RING_RULE (← q r"!r a b c:A. a IN ring_carrier r /\ b IN ring_carrier r /\
                  c IN ring_carrier r
                  ==> ring_add r (ring_add r (ring_mul r b a) c)
                        (ring_add r (ring_mul r (ring_neg r b) a)
                                    (ring_neg r c)) = ring_0 r")
    prove
      r"!k:A ring a p b c y1 y2 P1 P2.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
          prime p /\ a IN ring_carrier k /\
          ring_pow k a 2 =
          ring_add k (ring_mul k (ring_of_int k b) a) (ring_of_int k c) /\
          ring_setadd (ring_of_integers k) (ring_carrier(subring_generated k {a}))
            (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
          ring_carrier(ring_of_integers k) /\
          ~((y1 == y2) (mod &p)) /\ (y1 + y2 == b) (mod &p) /\
          (y1 * y2 == --c) (mod &p) /\
          P1 = ideal_generated (ring_of_integers k)
                 {ring_of_num k p, ring_sub k a (ring_of_int k y1)} /\
          P2 = ideal_generated (ring_of_integers k)
                 {ring_of_num k p, ring_sub k a (ring_of_int k y2)}
          ==> prime_ideal (ring_of_integers k) P1 /\
              prime_ideal (ring_of_integers k) P2 /\ ~(P1 = P2) /\
              ideal_generated (ring_of_integers k) {ring_of_num k p} =
              ideal_prod (ring_of_integers k) P1 P2 /\
              residue_degree (integer_ring,ring_of_integers k)
                (ring_of_int k) P1 = 1 /\
              residue_degree (integer_ring,ring_of_integers k)
                (ring_of_int k) P2 = 1"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM] THEN MATCH_MP_TAC INTEGRAL_ELEMENT_QUADRATIC THEN MAP_EVERY EXISTS_TAC [(← q r"--b:int"), (← q r"--c:int")] THEN ASM_REWRITE_TAC [RING_OF_INT_NEG] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"ring_of_int k b:A"), (← q r"ring_of_int k c:A")] r19) THEN ASM_REWRITE_TAC [RING_OF_INT], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"b:int"), (← q r"c:int"), (← q r"p:num")] QUADRATIC_POLY_INTEGER_ROOT) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"m:(1->num)->int") THEN STRIP_TAC THEN ABBREV_TAC (← q r"r1 = ring_of_int (integer_mod_ring p) y1") THEN ABBREV_TAC (← q r"r2 = ring_of_int (integer_mod_ring p) y2") THEN SUBGOAL_THEN (← q r"r1 IN ring_carrier(integer_mod_ring p) /\
      r2 IN ring_carrier(integer_mod_ring p) /\ ~(r1 = r2) /\
      ring_add (integer_mod_ring p) r1 r2 =
      ring_of_int (integer_mod_ring p) b /\
      ring_neg (integer_mod_ring p) (ring_mul (integer_mod_ring p) r1 r2) =
      ring_of_int (integer_mod_ring p) c") STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["r1", "r2"] THEN REWRITE_TAC [RING_OF_INT, (← GSYM RING_OF_INT_ADD), (← GSYM RING_OF_INT_MUL), (← GSYM RING_OF_INT_NEG)] THEN REWRITE_TAC [INTEGER_MOD_RING_OF_INT, INT_REM_EQ] THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"((y1:int) * y2 == --c) (mod &p)") THEN CONV_TAC INTEGER_RULE, ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do if ← (do let z13 ← (do let z14 ← (pure th); pure (concl z14)); pure (is_eq z13)) then (do let z18 ← (q r"ring_of_int (integer_mod_ring p) o (m:(1->num)->int)"); let z17 ← (do let z15 ← (do let z16 ← (pure th); pure (concl z16)); liftExcept (lhand z15)); pure (z17 == z18)) else pure false)))) THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z12 ← (q r"ring_of_int (integer_mod_ring p) c"); let z11 ← (do let z9 ← (do let z10 ← (pure th); pure (concl z10)); liftExcept (rhs z9)); pure (z11 == z12)))))) THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z8 ← (q r"ring_of_int (integer_mod_ring p) b"); let z7 ← (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); liftExcept (rhs z5)); pure (z7 == z8)))))) THEN ASM_SIMP_TAC [QUADRATIC_POLY_FACTOR] THEN DISCH_TAC THEN ABBREV_TAC (← q r"g = \i. if i = 0
              then poly_sub (integer_mod_ring p)
                     (poly_var (integer_mod_ring p) one)
                     (poly_const (integer_mod_ring p) r1)
              else poly_sub (integer_mod_ring p)
                     (poly_var (integer_mod_ring p) one)
                     (poly_const (integer_mod_ring p) r2)") THEN SUBGOAL_THEN (← q r"(!i. i IN {0,1}
           ==> (g:num->(1->num)->int) i IN
               ring_carrier(poly_ring (integer_mod_ring p) (:1)) /\
               monic (integer_mod_ring p) (g i) /\
               ring_irreducible (poly_ring (integer_mod_ring p) (:1)) (g i) /\
               poly_deg (integer_mod_ring p) (g i) = 1) /\
      ~(g 0 = g 1)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "g" THEN REWRITE_TAC [FORALL_IN_INSERT, NOT_IN_EMPTY, ARITH_EQ] THEN ASM_SIMP_TAC [MONIC_X_MINUS_A, RING_IRREDUCIBLE_X_MINUS_A, FIELD_INTEGER_MOD_RING, FIELD_IMP_INTEGRAL_DOMAIN, FIELD_IMP_NONTRIVIAL_RING, POLY_DEG_X_MINUS_A] THEN REWRITE_TAC [(← GSYM (← ISPECL [(← q r"integer_mod_ring p"), (← q r"(:1)")] (← (do let z3 ← (pure (CONJUNCTS POLY_RING_CLAUSES)); let z4 ← (pure 5); liftExcept (el z4 z3)))))] THEN ASM_SIMP_TAC [RING_SUB, POLY_VAR_UNIV, POLY_CONST] THEN DISCH_THEN (MP_TAC o (AP_TERM (← q r"coeff 0:((1->num)->int)->int"))) THEN REWRITE_TAC [POLY_RING_CLAUSES, COEFF_POLY_SUB, COEFF_POLY_VAR, COEFF_POLY_CONST, ARITH_EQ] THEN ASM_SIMP_TAC [RING_SUB_LZERO, RING_NEG_EQ], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"p:num"), (← q r"m:(1->num)->int"), (← q r"{0,1}"), (← q r"g:num->(1->num)->int"), (← q r"\i:num. 1"), (← q r"\i:num. ideal_generated (ring_of_integers k)
                 {ring_of_num k p,
                  poly_extend (integer_ring,k) (ring_of_int k) (\v. a)
                    ((g:num->(1->num)->int) i):A}")] DEDEKIND_KUMMER_Q) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_INSERT, FINITE_EMPTY, ARITH_EQ] THEN REWRITE_TAC [FORALL_IN_INSERT, NOT_IN_EMPTY] THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_INSERT, NOT_IN_EMPTY] THEN ASM_REWRITE_TAC [ARITH_EQ] THEN EXPAND_TAC "g" THEN SIMP_TAC [RING_PRODUCT_CLAUSES, FINITE_INSERT, FINITE_EMPTY, IN_INSERT, NOT_IN_EMPTY, ARITH_EQ, RING_PRODUCT_SING] THEN REWRITE_TAC [(← GSYM (← ISPECL [(← q r"integer_mod_ring p"), (← q r"(:1)")] (← (do let z1 ← (pure (CONJUNCTS POLY_RING_CLAUSES)); let z2 ← (pure 5); liftExcept (el z2 z1)))))] THEN ASM_SIMP_TAC [RING_POW_1, RING_SUB, POLY_VAR_UNIV, POLY_CONST], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_generated (ring_of_integers k)
        {ring_of_num k p,
         poly_extend (integer_ring,k) (ring_of_int k) (\v. a)
           ((g:num->(1->num)->int) 0):A} =
      ideal_generated (ring_of_integers k)
        {ring_of_num k p, ring_sub k a (ring_of_int k y1)} /\
      ideal_generated (ring_of_integers k)
        {ring_of_num k p,
         poly_extend (integer_ring,k) (ring_of_int k) (\v. a)
           ((g:num->(1->num)->int) 1):A} =
      ideal_generated (ring_of_integers k)
        {ring_of_num k p, ring_sub k a (ring_of_int k y2)}") STRIP_ASSUME_TAC THENL [EXPAND_TAC "g" THEN MAP_EVERY EXPAND_TAC ["r1", "r2"] THEN REWRITE_TAC [ARITH_EQ] THEN CONJ_TAC THEN MATCH_MP_TAC DEDEKIND_KUMMER_LINEAR_IDEAL THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 SUBST1_TAC (MP_TAC o CONJUNCT2)) THEN REWRITE_TAC [FORALL_IN_INSERT, NOT_IN_EMPTY, IMP_CONJ, RIGHT_FORALL_IMP_THM, ARITH_EQ] THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_SIMP_TAC [IDEAL_PRODUCT_INSERT, FINITE_INSERT, FINITE_EMPTY, IN_INSERT, NOT_IN_EMPTY, ARITH_EQ, IDEAL_PRODUCT_SING, RING_IDEAL_IDEAL_POW, IDEAL_POW_1, RING_IDEAL_IDEAL_GENERATED])

  let QUADRATIC_DEDEKIND_KUMMER_RAMIFIED_PRIME ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r19 ← RING_RULE (← q r"!r a b c:A. a IN ring_carrier r /\ b IN ring_carrier r /\
                  c IN ring_carrier r
                  ==> ring_add r (ring_add r (ring_mul r b a) c)
                        (ring_add r (ring_mul r (ring_neg r b) a)
                                    (ring_neg r c)) = ring_0 r")
    prove
      r"!k:A ring a p b c y P.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
          prime p /\ a IN ring_carrier k /\
          ring_pow k a 2 =
          ring_add k (ring_mul k (ring_of_int k b) a) (ring_of_int k c) /\
          ring_setadd (ring_of_integers k) (ring_carrier(subring_generated k {a}))
            (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
          ring_carrier(ring_of_integers k) /\
          (y + y == b) (mod &p) /\ (y * y == --c) (mod &p) /\
          P = ideal_generated (ring_of_integers k)
                {ring_of_num k p, ring_sub k a (ring_of_int k y)}
          ==> prime_ideal (ring_of_integers k) P /\
              ideal_generated (ring_of_integers k) {ring_of_num k p} =
              ideal_pow (ring_of_integers k) P 2 /\
              residue_degree (integer_ring,ring_of_integers k)
                (ring_of_int k) P = 1"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM] THEN MATCH_MP_TAC INTEGRAL_ELEMENT_QUADRATIC THEN MAP_EVERY EXISTS_TAC [(← q r"--b:int"), (← q r"--c:int")] THEN ASM_REWRITE_TAC [RING_OF_INT_NEG] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"ring_of_int k b:A"), (← q r"ring_of_int k c:A")] r19) THEN ASM_REWRITE_TAC [RING_OF_INT], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"b:int"), (← q r"c:int"), (← q r"p:num")] QUADRATIC_POLY_INTEGER_ROOT) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"m:(1->num)->int") THEN STRIP_TAC THEN ABBREV_TAC (← q r"r = ring_of_int (integer_mod_ring p) y") THEN SUBGOAL_THEN (← q r"r IN ring_carrier(integer_mod_ring p) /\
      ring_add (integer_mod_ring p) r r =
      ring_of_int (integer_mod_ring p) b /\
      ring_neg (integer_mod_ring p) (ring_mul (integer_mod_ring p) r r) =
      ring_of_int (integer_mod_ring p) c") STRIP_ASSUME_TAC THENL [EXPAND_TAC "r" THEN REWRITE_TAC [RING_OF_INT, (← GSYM RING_OF_INT_ADD), (← GSYM RING_OF_INT_MUL), (← GSYM RING_OF_INT_NEG)] THEN REWRITE_TAC [INTEGER_MOD_RING_OF_INT, INT_REM_EQ] THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"((y:int) * y == --c) (mod &p)") THEN CONV_TAC INTEGER_RULE, ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do if ← (do let z13 ← (do let z14 ← (pure th); pure (concl z14)); pure (is_eq z13)) then (do let z18 ← (q r"ring_of_int (integer_mod_ring p) o (m:(1->num)->int)"); let z17 ← (do let z15 ← (do let z16 ← (pure th); pure (concl z16)); liftExcept (lhand z15)); pure (z17 == z18)) else pure false)))) THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z12 ← (q r"ring_of_int (integer_mod_ring p) c"); let z11 ← (do let z9 ← (do let z10 ← (pure th); pure (concl z10)); liftExcept (rhs z9)); pure (z11 == z12)))))) THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z8 ← (q r"ring_of_int (integer_mod_ring p) b"); let z7 ← (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); liftExcept (rhs z5)); pure (z7 == z8)))))) THEN ASM_SIMP_TAC [QUADRATIC_POLY_FACTOR] THEN DISCH_TAC THEN ABBREV_TAC (← q r"g = \i:num. poly_sub (integer_mod_ring p)
                    (poly_var (integer_mod_ring p) one)
                    (poly_const (integer_mod_ring p) r)") THEN SUBGOAL_THEN (← q r"(g:num->(1->num)->int) 0 IN
      ring_carrier(poly_ring (integer_mod_ring p) (:1)) /\
      monic (integer_mod_ring p) (g 0) /\
      ring_irreducible (poly_ring (integer_mod_ring p) (:1)) (g 0) /\
      poly_deg (integer_mod_ring p) (g 0) = 1") STRIP_ASSUME_TAC THENL [EXPAND_TAC "g" THEN ASM_SIMP_TAC [MONIC_X_MINUS_A, RING_IRREDUCIBLE_X_MINUS_A, FIELD_INTEGER_MOD_RING, FIELD_IMP_INTEGRAL_DOMAIN, FIELD_IMP_NONTRIVIAL_RING, POLY_DEG_X_MINUS_A] THEN REWRITE_TAC [(← GSYM (← ISPECL [(← q r"integer_mod_ring p"), (← q r"(:1)")] (← (do let z3 ← (pure (CONJUNCTS POLY_RING_CLAUSES)); let z4 ← (pure 5); liftExcept (el z4 z3)))))] THEN ASM_SIMP_TAC [RING_SUB, POLY_VAR_UNIV, POLY_CONST], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"p:num"), (← q r"m:(1->num)->int"), (← q r"{0}"), (← q r"g:num->(1->num)->int"), (← q r"\i:num. 2"), (← q r"\i:num. ideal_generated (ring_of_integers k)
                 {ring_of_num k p,
                  poly_extend (integer_ring,k) (ring_of_int k) (\v. a)
                    ((g:num->(1->num)->int) i):A}")] DEDEKIND_KUMMER_Q) THEN ASM_REWRITE_TAC [FINITE_SING, IN_SING, FORALL_UNWIND_THM2, ARITH_EQ] THEN ANTS_TAC THENL [REWRITE_TAC [RING_PRODUCT_SING] THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "g" THEN REWRITE_TAC [(← GSYM (← ISPECL [(← q r"integer_mod_ring p"), (← q r"(:1)")] (← (do let z1 ← (pure (CONJUNCTS POLY_RING_CLAUSES)); let z2 ← (pure 5); liftExcept (el z2 z1)))))] THEN ASM_SIMP_TAC [RING_POW, RING_SUB, POLY_VAR_UNIV, POLY_CONST, RING_POW_2], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_generated (ring_of_integers k)
        {ring_of_num k p,
         poly_extend (integer_ring,k) (ring_of_int k) (\v. a)
           ((g:num->(1->num)->int) 0):A} =
      ideal_generated (ring_of_integers k)
        {ring_of_num k p, ring_sub k a (ring_of_int k y)}") ASSUME_TAC THENL [EXPAND_TAC "g" THEN EXPAND_TAC "r" THEN MATCH_MP_TAC DEDEKIND_KUMMER_LINEAR_IDEAL THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [IDEAL_PRODUCT_SING, RING_IDEAL_IDEAL_POW])

  let QUADRATIC_DEDEKIND_KUMMER_SPLIT ← prove
    r"!k:A ring a p b c y1 y2.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        prime p /\ a IN ring_carrier k /\
        ring_pow k a 2 =
        ring_add k (ring_mul k (ring_of_int k b) a) (ring_of_int k c) /\
        ring_setadd (ring_of_integers k) (ring_carrier(subring_generated k {a}))
          (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
        ring_carrier(ring_of_integers k) /\
        ~((y1 == y2) (mod &p)) /\ (y1 + y2 == b) (mod &p) /\
        (y1 * y2 == --c) (mod &p)
        ==> ?P Q. prime_ideal (ring_of_integers k) P /\
                  prime_ideal (ring_of_integers k) Q /\ ~(P = Q) /\
                  ideal_generated (ring_of_integers k) {ring_of_num k p} =
                  ideal_prod (ring_of_integers k) P Q"
    (REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"ideal_generated (ring_of_integers k)
       {ring_of_num k p, ring_sub k a (ring_of_int k y1):A}"), (← q r"ideal_generated (ring_of_integers k)
       {ring_of_num k p, ring_sub k a (ring_of_int k y2):A}")] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"p:num"), (← q r"b:int"), (← q r"c:int"), (← q r"y1:int"), (← q r"y2:int"), (← q r"ideal_generated (ring_of_integers k)
       {ring_of_num k p, ring_sub k a (ring_of_int k y1):A}"), (← q r"ideal_generated (ring_of_integers k)
       {ring_of_num k p, ring_sub k a (ring_of_int k y2):A}")] QUADRATIC_DEDEKIND_KUMMER_SPLIT_PRIMES) THEN ASM_SIMP_TAC [])

  let QUADRATIC_DEDEKIND_KUMMER_INERT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r7 ← INTEGER_RULE (← q r"!x y n:int. (x == y) (mod n) <=> n divides (x - y)")
    prove
      r"!k:A ring a p b c.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
          prime p /\ a IN ring_carrier k /\
          ring_pow k a 2 =
          ring_add k (ring_mul k (ring_of_int k b) a) (ring_of_int k c) /\
          ring_setadd (ring_of_integers k) (ring_carrier(subring_generated k {a}))
            (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
          ring_carrier(ring_of_integers k) /\
          (!y. ~((y pow 2 == b * y + c) (mod &p)))
          ==> prime_ideal (ring_of_integers k)
                (ideal_generated (ring_of_integers k) {ring_of_num k p})"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"b:int"), (← q r"c:int"), (← q r"p:num")] QUADRATIC_POLY_INTEGER_ROOT) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"m:(1->num)->int") THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (GEN_REWRITE_RULE id [(← GSYM FIELD_INTEGER_MOD_RING)])) THEN SUBGOAL_THEN (← q r"ring_of_int (integer_mod_ring p) o m IN
      ring_carrier(poly_ring (integer_mod_ring p) (:1)) /\
      monic (integer_mod_ring p) (ring_of_int (integer_mod_ring p) o m) /\
      ring_irreducible (poly_ring (integer_mod_ring p) (:1))
        (ring_of_int (integer_mod_ring p) o m)") STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [QUADRATIC_POLY_IN_CARRIER, QUADRATIC_POLY_DEG, RING_OF_INT, FIELD_IMP_NONTRIVIAL_RING] THEN MATCH_MP_TAC POLY_DEG_2_IRREDUCIBLE THEN ASM_SIMP_TAC [QUADRATIC_POLY_IN_CARRIER, QUADRATIC_POLY_DEG, RING_OF_INT, FIELD_IMP_NONTRIVIAL_RING] THEN X_GEN_TAC (← q r"y:int") THEN DISCH_TAC THEN REWRITE_TAC [poly_eval] THEN REWRITE_TAC [(← GSYM (← REWRITE_RULE [RING_HOMOMORPHISM_I, I_O_ID] (← ISPECL [(← q r"integer_mod_ring p"), (← q r"integer_mod_ring p"), (← q r"I:int->int")] POLY_EXTEND_EVALUATE)))] THEN ASM_SIMP_TAC [QUADRATIC_POLY_EXTEND, RING_HOMOMORPHISM_I, RING_OF_INT, I_THM] THEN SUBGOAL_THEN (← q r"y = ring_of_int (integer_mod_ring p) y") SUBST1_TAC THENL [REWRITE_TAC [INTEGER_MOD_RING_OF_INT] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_LT THEN UNDISCH_TAC (← q r"y IN ring_carrier (integer_mod_ring p)") THEN ASM_SIMP_TAC [IN_INTEGER_MOD_RING_CARRIER, INT_OF_NUM_EQ, PRIME_IMP_NZ], ALL_TAC] THEN REWRITE_TAC [(← GSYM RING_OF_INT_POW), (← GSYM RING_OF_INT_MUL), (← GSYM RING_OF_INT_ADD), (← GSYM RING_OF_INT_SUB)] THEN REWRITE_TAC [RING_OF_INT_EQ_0, INTEGER_MOD_RING_CHAR] THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"y:int")) o (checkM (fun z8 => (do let z9 ← (do let z10 ← (pure z8); pure (concl z10)); pure (is_forall z9)))))) THEN REWRITE_TAC [r7], ALL_TAC] THEN FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_eq z1)) then (do let z6 ← (q r"ring_of_int (integer_mod_ring p) o (m:(1->num)->int)"); let z5 ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); liftExcept (lhand z3)); pure (z5 == z6)) else pure false)))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"p:num"), (← q r"m:(1->num)->int"), (← q r"{0}"), (← q r"\i:num. ring_of_int (integer_mod_ring p) o (m:(1->num)->int)"), (← q r"\i:num. 1"), (← q r"\i:num. ideal_generated (ring_of_integers k)
                 {ring_of_num k p,
                  poly_extend (integer_ring,k) (ring_of_int k) (\v. a)
                    (ring_of_int (integer_mod_ring p) o (m:(1->num)->int)):A}")] DEDEKIND_KUMMER_Q) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [FINITE_SING, IN_SING, ARITH_EQ, RING_PRODUCT_SING] THEN ASM_SIMP_TAC [RING_POW_1], DISCH_THEN (CONJUNCTS_THEN2 SUBST1_TAC (MP_TAC o (CONJUNCT2 o CONJUNCT2))) THEN REWRITE_TAC [IN_SING, FORALL_UNWIND_THM2] THEN SIMP_TAC [IDEAL_PRODUCT_SING, RING_IDEAL_IDEAL_POW, IDEAL_POW_1, RING_IDEAL_IDEAL_GENERATED]])

  let QUADRATIC_FIELD_RING_OF_INTEGERS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"(p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)")
    let r2 ← ARITH_RULE (← q r"i < 2 <=> i = 0 \/ i = 1")
    let r3 ← RING_RULE (← q r"!k:A ring y h.
           ring_mul k (ring_of_num k 2) h = ring_1 k
           ==> ring_mul k (ring_of_num k 2) (ring_mul k y h) = y")
    let r4 ← TAUT (← q r"r /\ p /\ q ==> p /\ q /\ r")
    prove
      r"!k:A ring x d w.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
          x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
          squarefree(num_of_int(abs d)) /\ ~(d = &1) /\
          w = (if (d == &1) (mod &4)
               then ring_div k (ring_add k (ring_1 k) x) (ring_of_num k 2) else x)
          ==> w IN ring_carrier(ring_of_integers k) /\
              (!z. z IN ring_carrier(ring_of_integers k)
                   ==> ?a b. z = ring_add k (ring_of_int k a)
                                            (ring_mul k (ring_of_int k b) w)) /\
              (if (d == &1) (mod &4)
               then ring_mul k (ring_of_num k 2) w = ring_add k (ring_1 k) x
               else w = x)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC r4 THEN CONJ_TAC THENL [FIRST_X_ASSUM SUBST1_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [ring_div] THEN FIRST_ASSUM (fun th => tactic_of do pure (ASSUME_TAC (← MATCH_MP NUMBER_FIELD_IMP_FIELD th) THEN STRIP_ASSUME_TAC (← REWRITE_RULE [number_field] th))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_of_num k 2:A")] FIELD_MUL_RINV) THEN ASM_SIMP_TAC [RING_OF_NUM, RING_OF_NUM_EQ_0, DIVIDES_ZERO, ARITH_EQ] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_add k (ring_1 k) x:A"), (← q r"ring_inv k (ring_of_num k 2):A")] r3) THEN ASM_SIMP_TAC [RING_ADD, RING_1, RING_INV, RING_OF_NUM], ALL_TAC] THEN MP_TAC (← SPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"d:int")] QUADRATIC_FIELD_INTEGRAL_BASIS) THEN ASM_REWRITE_TAC [free_basis, RING_OF_INTEGERS, INTEGER_RING, IN_UNIV] THEN SUBGOAL_THEN (← q r"{i:num | i < 2} = {0,1}") SUBST1_TAC THENL [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_INSERT, NOT_IN_EMPTY] THEN ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [r2, FORALL_AND_THM, r1, FORALL_UNWIND_THM2, ARITH_EQ] THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"z:A") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"z:A"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:num->int") SUBST1_TAC) THEN MAP_EVERY EXISTS_TAC [(← q r"(c:num->int) 0"), (← q r"(c:num->int) 1")] THEN MP_TAC (← ISPEC (← q r"k:A ring") (← CONJUNCT1 RING_OF_INTEGERS_SUBRING)) THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_mul (k:A ring) (ring_of_int k (c 0)) (ring_1 k) IN
      ring_carrier(ring_of_integers k) /\
      ring_mul k (ring_of_int k (c 1)) w IN ring_carrier(ring_of_integers k)") STRIP_ASSUME_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_REWRITE_TAC [RING_OF_INT_IN_RING_OF_INTEGERS], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN SIMP_TAC [RING_SUM_CLAUSES, FINITE_SING, IN_SING, ARITH_EQ, RING_SUM_SING] THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN SIMP_TAC [RING_MUL_RID, RING_OF_INT])

  let RING_OF_INTEGERS_SETADD_SUBRING_GENERATED ← prove
    r"!k:A ring a j.
        a IN ring_carrier(ring_of_integers k) /\
        ring_ideal (ring_of_integers k) j /\
        (!z. z IN ring_carrier(ring_of_integers k)
             ==> ?u v. u IN ring_carrier(subring_generated k {a}) /\
                       v IN j /\ z = ring_add k u v)
        ==> ring_setadd (ring_of_integers k)
              (ring_carrier(subring_generated k {a})) j =
            ring_carrier(ring_of_integers k)"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [MATCH_MP_TAC RING_SETADD THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET] THEN MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET, RING_OF_INTEGERS_SUBRING], REWRITE_TAC [SUBSET, ring_setadd, IN_ELIM_THM, RING_OF_INTEGERS] THEN ASM_MESON_TAC []])

  let RING_OF_INTEGERS_SETADD_SUBRING_GENERATED_LINEAR ← prove
    r"!k:A ring a j.
        a IN ring_carrier(ring_of_integers k) /\
        ring_ideal (ring_of_integers k) j /\
        (!z. z IN ring_carrier(ring_of_integers k)
             ==> ?m n. z = ring_add k (ring_of_int k m)
                                      (ring_mul k (ring_of_int k n) a))
        ==> ring_setadd (ring_of_integers k)
              (ring_carrier(subring_generated k {a})) j =
            ring_carrier(ring_of_integers k)"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_OF_INTEGERS_SETADD_SUBRING_GENERATED THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"z:A") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (← do let c := (← ASSUME (← q r"(z:A) IN ring_carrier(ring_of_integers k)")); pure (fun th => MATCH_MP th c))) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"m:int") (X_CHOOSE_THEN (← q r"n:int") SUBST1_TAC)) THEN MAP_EVERY EXISTS_TAC [(← q r"ring_add k (ring_of_int k m) (ring_mul k (ring_of_int k n) a):A"), (← q r"ring_0 k:A")] THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier k") ASSUME_TAC THENL [MATCH_MP_TAC (← REWRITE_RULE [SUBSET] (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_SUBSET)) THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN ASM_SIMP_TAC [RING_ADD_RZERO, RING_ADD, RING_MUL, RING_OF_INT] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{a:A}")] SUBRING_SUBRING_GENERATED) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{a:A}"), (← q r"a:A")] SUBRING_GENERATED_INC_GEN) THEN ASM_REWRITE_TAC [IN_SING] THEN MESON_TAC [IN_SUBRING_ADD, IN_SUBRING_MUL, IN_SUBRING_INT], MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"j:A->bool")] IN_RING_IDEAL_0) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS]])

  -- @@RETURN BEGIN
  return { QUADRATIC_POLY_IN_CARRIER, QUADRATIC_POLY_DEG, QUADRATIC_POLY_EXTEND,
           QUADRATIC_POLY_HOMOMORPHIC_IMAGE, QUADRATIC_POLY_FACTOR,
           QUADRATIC_POLY_INTEGER_ROOT, QUADRATIC_DEDEKIND_KUMMER_SPLIT_PRIMES,
           QUADRATIC_DEDEKIND_KUMMER_RAMIFIED_PRIME, QUADRATIC_DEDEKIND_KUMMER_SPLIT,
           QUADRATIC_DEDEKIND_KUMMER_INERT, QUADRATIC_FIELD_RING_OF_INTEGERS,
           RING_OF_INTEGERS_SETADD_SUBRING_GENERATED,
           RING_OF_INTEGERS_SETADD_SUBRING_GENERATED_LINEAR }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- quadratic_split.ml phrases from line 713 to 1292                       -/
/- ---------------------------------------------------------------------- -/

structure QuadraticSplit02 where
  -- @@FIELDS
  QUADRATIC_FIELD_SETADD_ODD : thm
  QUADRATIC_FIELD_RAMIFIED_PRIME : thm
  QUADRATIC_FIELD_RAMIFIED : thm
  QUADRATIC_FIELD_ODD_PRIME : thm
  QUADRATIC_FIELD_PRIME_TWO : thm
  QUADRATIC_FIELD_SPLIT_ODD_PRIME : thm
  QUADRATIC_FIELD_RAMIFIED_ODD_PRIME : thm
  QUADRATIC_FIELD_RAMIFIED_TWO : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupQuadraticSplit02 [HolBase] (D : QuadraticSplitDeps) (BQuadraticSplit01 : QuadraticSplit01) :
    ExceptT String IO QuadraticSplit02 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_INT_ARITH_TAC, ASM_MESON_TAC,
        INTEGER_RULE, INT_ARITH, INT_ARITH_TAC, INT_REDUCE_CONV, RING_RULE, SET_RULE,
        SET_TAC, TAUT, .. } := D
  let { ARITH_EQ, COPRIME_PRIME_PRIME, DEDEKIND_RING_OF_INTEGERS, DIVIDES_ZERO, EXP_1,
        EXTENSION, FIELD_IMP_INTEGRAL_DOMAIN, FINITE_DELETE, IDEAL_GENERATED_INC_GEN,
        IDEAL_GENERATED_SING, IDEAL_POW_SUBSET_PRIME_IDEAL, IDEAL_PRODUCT_SING,
        IDEAL_VALUATION_IDEAL_POW, IDEAL_VALUATION_PRIME, INTEGRAL_DOMAIN_MUL_LCANCEL,
        INT_ABS_NUM, INT_ADD_LID, INT_DIVISION, INT_MUL_LZERO, INT_OF_NUM_EQ,
        INT_POW_2, INT_REM_EQ, INT_REM_EQ_0, IN_DELETE, IN_ELIM_THM, IN_INSERT,
        IN_SING, IN_SUBRING_1, IN_SUBRING_ADD, IN_SUBRING_INT, IN_SUBRING_MUL,
        IN_SUBRING_NEG, IN_SUBRING_NUM, IN_SUBRING_SUB, LE_MULT2, MULT_CLAUSES,
        MULT_EQ_0, NOT_EXISTS_THM, NOT_IN_EMPTY, NSUM_DELETE, NSUM_EQ_0_IFF,
        NUMBER_FIELD_FUNDAMENTAL_IDENTITY_Q, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_PRIME_FACTORIZATION_Q, NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q,
        NUMBER_FIELD_PRIME_IDEAL_PROD_EQ, NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q,
        NUMBER_FIELD_RAMIFIED_DISCRIMINANT, ODD_EXISTS, .. } := D.core1
  let { PRIME_2, PRIME_IDEAL_IMP_SUBSET, PRIME_IMP_NZ, PRIME_IMP_RING_IDEAL, PRIME_ODD,
        RAMIFICATION_INDEX_PRIME, RING_1, RING_ADD, RING_ADD_LZERO,
        RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_POW, RING_MUL, RING_MUL_LZERO,
        RING_OF_INT, RING_OF_INTEGERS, RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q,
        RING_OF_INTEGERS_SUBRING, RING_OF_INTEGERS_SUBSET, RING_OF_INT_0,
        RING_OF_INT_1, RING_OF_INT_ADD, RING_OF_INT_IN_RING_OF_INTEGERS,
        RING_OF_INT_MUL, RING_OF_INT_NEG, RING_OF_INT_OF_NUM, RING_OF_NUM,
        RING_OF_NUM_1, RING_OF_NUM_ADD, RING_OF_NUM_EQ_0, RING_OF_NUM_MUL, RING_POW,
        RING_SUB_RZERO, SUBRING_GENERATED_INC_GEN, SUBRING_SUBRING_GENERATED, SUBSET,
        SUBSET_REFL, int_congruent, int_divides, num_coprime, number_field,
        ring_divides, .. } := D.core2
  let { QUADRATIC_DEDEKIND_KUMMER_INERT, QUADRATIC_DEDEKIND_KUMMER_RAMIFIED_PRIME,
        QUADRATIC_DEDEKIND_KUMMER_SPLIT, QUADRATIC_DEDEKIND_KUMMER_SPLIT_PRIMES,
        QUADRATIC_FIELD_RING_OF_INTEGERS, RING_OF_INTEGERS_SETADD_SUBRING_GENERATED,
        RING_OF_INTEGERS_SETADD_SUBRING_GENERATED_LINEAR, .. } := BQuadraticSplit01
  -- @@SCOPE END

  let QUADRATIC_FIELD_SETADD_ODD ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!k:A ring w a b h.
       ring_add k a (ring_mul k b w) =
       ring_add k (ring_add k (ring_add k a (ring_mul k b h))
          (ring_mul k (ring_mul k b h)
             (ring_sub k (ring_mul k (ring_of_num k 2) w) (ring_1 k))))
          (ring_mul k (ring_sub k (ring_mul k (ring_of_num k 2) h) (ring_1 k))
             (ring_mul k (ring_neg k b) w))")
    let r2 ← RING_RULE (← q r"ring_sub (r:A ring) (ring_add r a b) b = a")
    let r3 ← RING_RULE (← q r"ring_sub (r:A ring) (ring_add r (ring_1 r) x) (ring_1 r) = x")
    let r4 ← RING_RULE (← q r"ring_sub (r:A ring) (ring_add r (ring_1 r) x) (ring_1 r) = x")
    prove
      r"!k:A ring x d p.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
          x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
          squarefree(num_of_int(abs d)) /\ ~(d = &1) /\ ODD p
          ==> ring_setadd (ring_of_integers k)
                (ring_carrier(subring_generated k {x}))
                (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
              ring_carrier(ring_of_integers k)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← SPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"d:int"), (← q r"if ((d:int) == &1) (mod &4)
                   then ring_div k (ring_add k (ring_1 k) x) (ring_of_num k 2)
                   else x:A")] QUADRATIC_FIELD_RING_OF_INTEGERS) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"w = if ((d:int) == &1) (mod &4)
                    then ring_div k (ring_add k (ring_1 k) x) (ring_of_num k 2)
                    else x:A") THEN STRIP_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") (← CONJUNCT1 RING_OF_INTEGERS_SUBRING)) THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_carrier(subring_generated k {x:A}) subring_of k /\
      x IN ring_carrier(subring_generated k {x})") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [SUBRING_SUBRING_GENERATED, SUBRING_GENERATED_INC_GEN, IN_SING], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun z5 => (do let z6 ← (do let z7 ← (pure z5); pure (concl z7)); pure (HolCore.Classic.is_cond z6))))) THEN ASM_CASES_TAC (← q r"((d:int) == &1) (mod &4)") THEN ASM_REWRITE_TAC [] THENL [DISCH_TAC, DISCH_THEN SUBST_ALL_TAC THEN MATCH_MP_TAC RING_OF_INTEGERS_SETADD_SUBRING_GENERATED_LINEAR THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED]] THEN MATCH_MP_TAC RING_OF_INTEGERS_SETADD_SUBRING_GENERATED THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"x = ring_sub k (ring_mul k (ring_of_num k 2) w) (ring_1 k):A") SUBST1_TAC THENL [ASM_SIMP_TAC [RING_1, r4], ASM_SIMP_TAC [IN_SUBRING_SUB, IN_SUBRING_MUL, IN_SUBRING_NUM, IN_SUBRING_1]], ALL_TAC] THEN SUBGOAL_THEN (← q r"(w:A) IN ring_carrier k") ASSUME_TAC THENL [MATCH_MP_TAC (← REWRITE_RULE [SUBSET] (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_SUBSET)) THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"ODD p") THEN REWRITE_TAC [ODD_EXISTS] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"m:num")) THEN X_GEN_TAC (← q r"z:A") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (← do let c := (← ASSUME (← q r"(z:A) IN ring_carrier(ring_of_integers k)")); pure (fun th => MATCH_MP th c))) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:int") (X_CHOOSE_THEN (← q r"b:int") SUBST1_TAC)) THEN MAP_EVERY EXISTS_TAC [(← q r"ring_add k
        (ring_add k (ring_of_int k a)
                    (ring_mul k (ring_of_int k b) (ring_of_num k (m + 1))))
        (ring_mul k (ring_mul k (ring_of_int k b) (ring_of_num k (m + 1))) x):A"), (← q r"ring_mul k (ring_of_num k p)
         (ring_mul k (ring_neg k (ring_of_int k b)) w):A")] THEN REPEAT CONJ_TAC THENL [REPEAT (FIRST [CONJ_TAC, MATCH_MP_TAC IN_SUBRING_ADD, MATCH_MP_TAC IN_SUBRING_MUL]) THEN ASM_SIMP_TAC [IN_SUBRING_INT, IN_SUBRING_NUM], SIMP_TAC [IDEAL_GENERATED_SING, RING_OF_INTEGERS, RING_OF_NUM, (← GSYM RING_OF_INT_OF_NUM), RING_OF_INT_IN_RING_OF_INTEGERS] THEN REWRITE_TAC [IN_ELIM_THM, ring_divides, RING_OF_INTEGERS, (← GSYM RING_OF_INT_OF_NUM), RING_OF_INT_IN_RING_OF_INTEGERS] THEN SUBGOAL_THEN (← q r"ring_mul k (ring_neg k (ring_of_int k b)) w IN
        ring_carrier(ring_of_integers (k:A ring))") ASSUME_TAC THENL [ASM_SIMP_TAC [IN_SUBRING_MUL, IN_SUBRING_NEG, RING_OF_INT_IN_RING_OF_INTEGERS], ALL_TAC] THEN CONJ_TAC THENL [ASM_SIMP_TAC [IN_SUBRING_MUL, RING_OF_INT_IN_RING_OF_INTEGERS], EXISTS_TAC (← q r"ring_mul k (ring_neg k (ring_of_int k b)) w:A") THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"x = ring_sub k (ring_mul k (ring_of_num k 2) w) (ring_1 k) /\
      ring_of_num k p =
      ring_sub k (ring_mul k (ring_of_num k 2) (ring_of_num k (m + 1)))
                 (ring_1 k):A") (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_SIMP_TAC [RING_1, r3] THEN REWRITE_TAC [(← GSYM RING_OF_NUM_MUL), (← GSYM RING_OF_NUM_1)] THEN SUBGOAL_THEN (← q r"2 * (m + 1) = p + 1") SUBST1_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN SIMP_TAC [RING_OF_NUM_ADD, RING_OF_NUM, r2] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [RING_OF_INT, RING_OF_NUM])

  let QUADRATIC_FIELD_RAMIFIED_PRIME ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"f:num"
    let q2 ← q r"2"
    let q3 ← q r"e:num"
    let q4 ← q r"2"
    let v5 ← SPECL [q4, q3, q2, q1] LE_MULT2
    let q6 ← q r"f = 1"
    let p7 ← prove r"!e f. 1 < e /\ 1 <= f /\ e * f <= 2 ==> e = 2 /\ f = 1" (REPEAT GEN_TAC THEN ASM_CASES_TAC q6 THEN ASM_REWRITE_TAC [MULT_CLAUSES] THENL [ARITH_TAC, STRIP_TAC] THEN MP_TAC v5 THEN ASM_ARITH_TAC)
    let lemma := p7
    let q11 ← q r"Q:A->bool"
    let q15 ← q r"Q:A->bool"
    let q16 ← q r"Q:A->bool"
    let q17 ← q r"2 * 1 + n = 2 <=> n = 0"
    let r18 ← ARITH_RULE q17
    let q19 ← q r"P:A->bool"
    let q20 ← q r"S:(A->bool)->bool"
    let q21 ← q r"\Q. ramification_index (integer_ring,ring_of_integers k)
             (ring_of_int k) Q *
           residue_degree (integer_ring,ring_of_integers k)
             (ring_of_int k) (Q:A->bool)"
    let v22 ← ISPECL [q21, q20, q19] NSUM_DELETE
    let q23 ← q r"(a:A->bool) IN s /\ s DELETE a = {} ==> s = {a}"
    let r24 ← SET_RULE q23
    let q25 ← q r"S = {P:A->bool}"
    let q26 ← q r"ramification_index (integer_ring,ring_of_integers k)
      (ring_of_int k) (P:A->bool) = 2 /\
    residue_degree (integer_ring,ring_of_integers k) (ring_of_int k) P = 1"
    let q27 ← q r"(P:A->bool) IN S"
    let q28 ← q r"p:num"
    let q29 ← q r"Q:A->bool"
    let q30 ← q r"k:A ring"
    let v31 ← SPECL [q30, q29, q28] NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q
    let q32 ← q r"Q:A->bool"
    let q33 ← q r"!Q. Q IN S
        ==> 1 <= ramification_index (integer_ring,ring_of_integers k)
                   (ring_of_int k) Q /\
            1 <= residue_degree (integer_ring,ring_of_integers k)
                   (ring_of_int k) Q /\
            ramification_index (integer_ring,ring_of_integers k)
              (ring_of_int k) Q *
            residue_degree (integer_ring,ring_of_integers k)
              (ring_of_int k) (Q:A->bool) <= 2"
    let q34 ← q r"S = {P | prime_ideal (ring_of_integers k) P /\
                       ring_of_num k p IN (P:A->bool)}"
    let q35 ← q r"p:num"
    let q36 ← q r"k:A ring"
    let v37 ← SPECL [q36, q35] NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q
    let q38 ← q r"p:num"
    let q39 ← q r"k:A ring"
    let v40 ← SPECL [q39, q38] NUMBER_FIELD_FUNDAMENTAL_IDENTITY_Q
    let q41 ← q r"p:num"
    let q42 ← q r"k:A ring"
    let v43 ← SPECL [q42, q41] NUMBER_FIELD_PRIME_FACTORIZATION_Q
    prove
      r"!k:A ring p P.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
          prime p /\ prime_ideal (ring_of_integers k) P /\ ring_of_num k p IN P /\
          1 < ramification_index (integer_ring,ring_of_integers k)
                (ring_of_int k) P
          ==> ideal_generated (ring_of_integers k) {ring_of_num k p} =
              ideal_pow (ring_of_integers k) P 2"
      (REPEAT STRIP_TAC THEN MP_TAC v43 THEN MP_TAC v40 THEN MP_TAC v37 THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC q34 THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN q33 ASSUME_TAC THENL [EXPAND_TAC "S" THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC q32 THEN STRIP_TAC THEN MP_TAC v31 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN q27 ASSUME_TAC THENL [EXPAND_TAC "S" THEN ASM_REWRITE_TAC [IN_ELIM_THM], ALL_TAC] THEN SUBGOAL_THEN q26 STRIP_ASSUME_TAC THENL [MATCH_MP_TAC lemma THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN q25 SUBST_ALL_TAC THENL [MATCH_MP_TAC r24 THEN ASM_REWRITE_TAC [] THEN MP_TAC v22 THEN ASM_SIMP_TAC [r18, NSUM_EQ_0_IFF, FINITE_DELETE] THEN REWRITE_TAC [EXTENSION, IN_DELETE, NOT_IN_EMPTY, MULT_EQ_0] THEN DISCH_TAC THEN X_GEN_TAC q16 THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC q15) o (checkM (fun z12 => (do let z13 ← (do let z14 ← (pure z12); pure (concl z14)); pure (is_forall z13)))))) THEN FIRST_X_ASSUM (MP_TAC o ((SPEC q11) o (checkM (fun z8 => (do let z9 ← (do let z10 ← (pure z8); pure (concl z10)); pure (is_forall z9)))))) THEN ASM_REWRITE_TAC [] THEN ARITH_TAC, ALL_TAC] THEN ASM_REWRITE_TAC [] THEN SIMP_TAC [IDEAL_PRODUCT_SING, RING_IDEAL_IDEAL_POW] THEN ASM_REWRITE_TAC [])

  let QUADRATIC_FIELD_RAMIFIED ← prove
    r"!k:A ring x d p.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
        squarefree(num_of_int(abs d)) /\ ~(d = &1) /\ prime p
        ==> ((?P. prime_ideal (ring_of_integers k) P /\
                  ideal_generated (ring_of_integers k) {ring_of_num k p} =
                  ideal_pow (ring_of_integers k) P 2) <=>
             &p divides number_field_discriminant k)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← SPECL [(← q r"k:A ring"), (← q r"p:num")] NUMBER_FIELD_RAMIFIED_DISCRIMINANT) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN EQ_TAC THEN DISCH_THEN (X_CHOOSE_THEN (← q r"P:A->bool") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"P:A->bool") THEN ASM_SIMP_TAC [QUADRATIC_FIELD_RAMIFIED_PRIME] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_RING_OF_INTEGERS)) THEN SUBGOAL_THEN (← q r"ring_of_num k p IN
    ideal_generated (ring_of_integers k) {ring_of_num k p:A} /\
    ~(ring_of_num k p = ring_0 k)") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_INC_GEN THEN REWRITE_TAC [IN_SING, RING_OF_INTEGERS, (← GSYM RING_OF_INT_OF_NUM), RING_OF_INT_IN_RING_OF_INTEGERS], FIRST_ASSUM (MP_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN SIMP_TAC [RING_OF_NUM_EQ_0, DIVIDES_ZERO] THEN ASM_MESON_TAC [PRIME_IMP_NZ]], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_of_num k p IN (P:A->bool)") ASSUME_TAC THENL [UNDISCH_TAC (← q r"ring_of_num k p IN
      ideal_generated (ring_of_integers k) {ring_of_num k p:A}") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"P:A->bool"), (← q r"2")] IDEAL_POW_SUBSET_PRIME_IDEAL) THEN ASM_SIMP_TAC [PRIME_IDEAL_IMP_SUBSET, ARITH_EQ, SUBSET_REFL] THEN SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"p:num")] RAMIFICATION_INDEX_PRIME) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN SUBGOAL_THEN (← q r"~(P = {ring_0 k:A})") ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC (← q r"ring_of_num k p IN (P:A->bool)") THEN ASM_REWRITE_TAC [IN_SING], ALL_TAC] THEN ASM_SIMP_TAC [IDEAL_VALUATION_IDEAL_POW, IDEAL_VALUATION_PRIME, PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS] THEN ARITH_TAC)

  let QUADRATIC_FIELD_ODD_PRIME ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← INTEGER_RULE (← q r"!p y a:int. coprime(p,a) /\ p divides (a * y) ==> p divides y")
    let i3a := r1
    let r2 ← INTEGER_RULE (← q r"!p y d:int. p divides y /\ (y * y == d) (mod p) ==> p divides d")
    let i3b := r2
    let r3 ← INTEGER_RULE (← q r"!p y d:int. (y pow 2 == d) (mod p) ==> (y * --y == --d) (mod p)")
    let i6 := r3
    let r4 ← INTEGER_RULE (← q r"!p y:int. (y + --y == &0) (mod p)")
    let i7 := r4
    let r5 ← INT_ARITH (← q r"y - --y:int = &2 * y")
    let r6 ← INTEGER_RULE (← q r"!x y n:int. (x == y) (mod n) <=> n divides (x - y)")
    prove
      r"!k:A ring x d p.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
          x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
          squarefree(num_of_int(abs d)) /\ ~(d = &1) /\
          prime p /\ ~(p = 2) /\ ~(&p divides d)
          ==> ((?P Q. prime_ideal (ring_of_integers k) P /\
                      prime_ideal (ring_of_integers k) Q /\ ~(P = Q) /\
                      ideal_generated (ring_of_integers k) {ring_of_num k p} =
                      ideal_prod (ring_of_integers k) P Q) <=>
               ?y. (y pow 2 == d) (mod &p)) /\
              (prime_ideal (ring_of_integers k)
                 (ideal_generated (ring_of_integers k) {ring_of_num k p}) <=>
               ~(?y. (y pow 2 == d) (mod &p)))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← SPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"d:int"), (← q r"p:num")] QUADRATIC_FIELD_SETADD_ODD) THEN MP_TAC (← SPEC (← q r"p:num") PRIME_ODD) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"~((?P Q. prime_ideal (ring_of_integers k) P /\
               prime_ideal (ring_of_integers k) Q /\ ~(P = Q) /\
               ideal_generated (ring_of_integers k) {ring_of_num k p} =
               ideal_prod (ring_of_integers k) P (Q:A->bool)) /\
        prime_ideal (ring_of_integers k)
          (ideal_generated (ring_of_integers k) {ring_of_num k p:A}))") ASSUME_TAC THENL [STRIP_TAC THEN MP_TAC (← SPECL [(← q r"k:A ring"), (← q r"p:num"), (← q r"P:A->bool"), (← q r"Q:A->bool")] NUMBER_FIELD_PRIME_IDEAL_PROD_EQ) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"((?y. ((y:int) pow 2 == d) (mod &p)) ==>
       ?P Q. prime_ideal (ring_of_integers k) P /\
             prime_ideal (ring_of_integers k) Q /\ ~(P = Q) /\
             ideal_generated (ring_of_integers k) {ring_of_num k p} =
             ideal_prod (ring_of_integers k) P (Q:A->bool)) /\
      (~(?y. ((y:int) pow 2 == d) (mod &p)) ==>
       prime_ideal (ring_of_integers k)
         (ideal_generated (ring_of_integers k) {ring_of_num k p:A}))") MP_TAC THENL [CONJ_TAC THEN DISCH_TAC THENL [FIRST_X_ASSUM (X_CHOOSE_TAC (← q r"y:int")) THEN MATCH_MP_TAC QUADRATIC_DEDEKIND_KUMMER_SPLIT THEN MAP_EVERY EXISTS_TAC [(← q r"x:A"), (← q r"&0:int"), (← q r"d:int"), (← q r"y:int"), (← q r"--y:int")] THEN ASM_SIMP_TAC [RING_OF_INT_0, RING_MUL_LZERO, RING_ADD_LZERO, RING_OF_INT, i6, i7] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"~(&p divides (d:int))") THEN REWRITE_TAC [] THEN MATCH_MP_TAC i3b THEN EXISTS_TAC (← q r"y:int") THEN ASM_REWRITE_TAC [(← GSYM INT_POW_2)] THEN MATCH_MP_TAC i3a THEN EXISTS_TAC (← q r"&2:int") THEN CONJ_TAC THENL [REWRITE_TAC [(← GSYM num_coprime)] THEN MP_TAC (← SPECL [(← q r"p:num"), (← q r"2")] COPRIME_PRIME_PRIME) THEN ASM_REWRITE_TAC [PRIME_2], UNDISCH_TAC (← q r"((y:int) == --y) (mod &p)") THEN REWRITE_TAC [r6] THEN REWRITE_TAC [r5]], MATCH_MP_TAC QUADRATIC_DEDEKIND_KUMMER_INERT THEN MAP_EVERY EXISTS_TAC [(← q r"x:A"), (← q r"&0:int"), (← q r"d:int")] THEN ASM_SIMP_TAC [RING_OF_INT_0, RING_MUL_LZERO, RING_ADD_LZERO, RING_OF_INT, INT_MUL_LZERO, INT_ADD_LID] THEN ASM_REWRITE_TAC [(← GSYM NOT_EXISTS_THM)]], POP_ASSUM MP_TAC THEN CONV_TAC TAUT])

  let QUADRATIC_FIELD_PRIME_TWO ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"!a m n t:int. ~(m = &0)
        ==> ((a + m * t == a) (mod (m * n)) <=> n divides t)"
    let r2 ← INTEGER_RULE q1
    let q3 ← q r"t:int"
    let q4 ← q r"&2:int"
    let q5 ← q r"&4:int"
    let q6 ← q r"&1:int"
    let v7 ← SPECL [q6, q5, q4, q3] r2
    let p8 ← prove r"!t:int. (&1 + &4 * t == &1) (mod &8) <=> &2 divides t" (GEN_TAC THEN MP_TAC v7 THEN CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC [])
    let i1 := p8
    let q9 ← q r"!a m n t:int. ~(m = &0)
        ==> ((a + m * t == a + m) (mod (m * n)) <=> (t == &1) (mod n))"
    let r10 ← INTEGER_RULE q9
    let q11 ← q r"t:int"
    let q12 ← q r"&2:int"
    let q13 ← q r"&4:int"
    let q14 ← q r"&1:int"
    let v15 ← SPECL [q14, q13, q12, q11] r10
    let p16 ← prove r"!t:int. (&1 + &4 * t == &5) (mod &8) <=> (t == &1) (mod &2)" (GEN_TAC THEN MP_TAC v15 THEN CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC [])
    let i2 := p16
    let q17 ← q r"!n y2 y t:int. n divides (y2 - y) /\ (t == &1) (mod n) /\
                   (y2 == &1 * y + t) (mod n) ==> n divides &1"
    let r18 ← INTEGER_RULE q17
    let i4 := r18
    let q19 ← q r"!n t:int. n divides t ==> (&0 * &1 == --t) (mod n)"
    let r20 ← INTEGER_RULE q19
    let i5 := r20
    let q21 ← q r"&2 * q pow 2 + q:int"
    let q22 ← q r"&2 * q pow 2 - q:int"
    let q23 ← q r"r:int = &0 \/ r = &1"
    let q24 ← q r"q:int"
    let q25 ← q r"y div &2"
    let q26 ← q r"r:int"
    let q27 ← q r"y rem &2"
    let q28 ← q r"&2:int"
    let q29 ← q r"y:int"
    let v30 ← SPECL [q29, q28] INT_DIVISION
    let p31 ← prove r"!y:int. &2 divides (y pow 2 - y)" (GEN_TAC THEN MP_TAC v30 THEN REWRITE_TAC [INT_OF_NUM_EQ, ARITH_EQ, INT_ABS_NUM] THEN SPEC_TAC (q27, q26) THEN SPEC_TAC (q25, q24) THEN REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN SUBGOAL_THEN q23 (DISJ_CASES_THEN SUBST1_TAC) THENL [ASM_INT_ARITH_TAC, REWRITE_TAC [int_divides] THEN EXISTS_TAC q22 THEN INT_ARITH_TAC, REWRITE_TAC [int_divides] THEN EXISTS_TAC q21 THEN INT_ARITH_TAC])
    let par := p31
    let q32 ← q r"&2:int"
    let q33 ← q r"t:int"
    let v34 ← SPECL [q33, q32] INT_DIVISION
    let v35 ← GSYM INT_REM_EQ
    let v36 ← GSYM INT_REM_EQ_0
    let p37 ← prove r"!t:int. &2 divides t <=> ~((t == &1) (mod &2))" (GEN_TAC THEN REWRITE_TAC [v36, v35] THEN MP_TAC v34 THEN REWRITE_TAC [INT_OF_NUM_EQ, ARITH_EQ, INT_ABS_NUM] THEN CONV_TAC INT_REDUCE_CONV THEN INT_ARITH_TAC)
    let evodd := p37
    let q38 ← q r"t:int"
    let v39 ← SPEC q38 evodd
    let v40 ← GSYM INT_REM_EQ_0
    let q41 ← q r"t:int"
    let q42 ← q r"y:int"
    let q43 ← q r"(y:int) pow 2"
    let q44 ← q r"&2:int"
    let v45 ← SPECL [q44, q43, q42, q41] i4
    let q46 ← q r"y:int"
    let q47 ← q r"t:int"
    let q48 ← q r"&1:int"
    let q49 ← q r"w:A"
    let v50 ← GSYM INT_REM_EQ
    let q51 ← q r"&1:int"
    let q52 ← q r"&0:int"
    let q53 ← q r"t:int"
    let q54 ← q r"&1:int"
    let q55 ← q r"w:A"
    let q56 ← q r"(&2 divides (t:int)
     ==> ?P Q. prime_ideal (ring_of_integers k) P /\
               prime_ideal (ring_of_integers k) Q /\ ~(P = Q) /\
               ideal_generated (ring_of_integers k) {ring_of_num k 2} =
               ideal_prod (ring_of_integers k) P (Q:A->bool)) /\
    (((t:int) == &1) (mod &2)
     ==> prime_ideal (ring_of_integers k)
           (ideal_generated (ring_of_integers k) {ring_of_num k 2:A}))"
    let q57 ← q r"Q:A->bool"
    let q58 ← q r"P:A->bool"
    let q59 ← q r"2"
    let q60 ← q r"k:A ring"
    let v61 ← SPECL [q60, q59, q58, q57] NUMBER_FIELD_PRIME_IDEAL_PROD_EQ
    let q62 ← q r"~((?P Q. prime_ideal (ring_of_integers k) P /\
             prime_ideal (ring_of_integers k) Q /\ ~(P = Q) /\
             ideal_generated (ring_of_integers k) {ring_of_num k 2} =
             ideal_prod (ring_of_integers k) P (Q:A->bool)) /\
      prime_ideal (ring_of_integers k)
        (ideal_generated (ring_of_integers k) {ring_of_num k 2:A}))"
    let q63 ← q r"ring_setadd (ring_of_integers k) (ring_carrier(subring_generated k {w}))
      (ideal_generated (ring_of_integers k) {ring_of_num k 2}) =
    ring_carrier(ring_of_integers k:A ring)"
    let q64 ← q r"!k:A ring w x T.
           ring_mul k (ring_of_num k 2) w = ring_add k (ring_1 k) x
           ==> ring_pow k x 2 =
               ring_add k (ring_of_num k 1) (ring_mul k (ring_of_num k 4) T)
           ==> ring_mul k (ring_of_num k 4) (ring_pow k w 2) =
               ring_mul k (ring_of_num k 4)
                 (ring_add k (ring_mul k (ring_of_num k 1) w) T)"
    let r65 ← RING_RULE q64
    let q66 ← q r"ring_of_int k t:A"
    let q67 ← q r"x:A"
    let q68 ← q r"w:A"
    let q69 ← q r"k:A ring"
    let v70 ← ISPECL [q69, q68, q67, q66] r65
    let q71 ← q r"ring_pow k x 2 = ring_of_int k (&1 + &4 * t):A"
    let q72 ← q r"ring_of_num k 4:A"
    let q73 ← q r"k:A ring"
    let q74 ← q r"ring_pow k w 2 =
    ring_add k (ring_mul k (ring_of_int k (&1)) w) (ring_of_int k t):A"
    let q75 ← q r"(d:int) - &1 = &4 * t ==> d = &1 + &4 * t"
    let r76 ← INT_ARITH q75
    let q77 ← q r"t:int"
    let q78 ← q r"((d:int) == &1) (mod &4)"
    let v79 ← ASSUME q78
    let v80 ← REWRITE_RULE [int_congruent] v79
    let q81 ← q r"k:A ring"
    let v82 ← ISPEC q81 RING_OF_INTEGERS_SUBSET
    let v83 ← REWRITE_RULE [SUBSET] v82
    let q84 ← q r"(w:A) IN ring_carrier k"
    let q85 ← q r"w:A"
    let q86 ← q r"d:int"
    let q87 ← q r"x:A"
    let q88 ← q r"k:A ring"
    let v89 ← SPECL [q88, q87, q86, q85] QUADRATIC_FIELD_RING_OF_INTEGERS
    let q90 ← q r"w = ring_div k (ring_add k (ring_1 k) x) (ring_of_num k 2):A"
    prove
      r"!k:A ring x d.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
          x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
          squarefree(num_of_int(abs d)) /\ ~(d = &1) /\ (d == &1) (mod &4)
          ==> ((?P Q. prime_ideal (ring_of_integers k) P /\
                      prime_ideal (ring_of_integers k) Q /\ ~(P = Q) /\
                      ideal_generated (ring_of_integers k) {ring_of_num k 2} =
                      ideal_prod (ring_of_integers k) P Q) <=>
               (d == &1) (mod &8)) /\
              (prime_ideal (ring_of_integers k)
                 (ideal_generated (ring_of_integers k) {ring_of_num k 2}) <=>
               (d == &5) (mod &8))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN ABBREV_TAC q90 THEN MP_TAC v89 THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN FIRST_ASSUM (fun th => tactic_of do pure (ASSUME_TAC (← MATCH_MP NUMBER_FIELD_IMP_FIELD th) THEN STRIP_ASSUME_TAC (← REWRITE_RULE [number_field] th))) THEN SUBGOAL_THEN q84 ASSUME_TAC THENL [MATCH_MP_TAC v83 THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN MP_TAC v80 THEN DISCH_THEN (X_CHOOSE_THEN q77 (SUBST_ALL_TAC o (MATCH_MP r76))) THEN REWRITE_TAC [i1, i2] THEN SUBGOAL_THEN q74 ASSUME_TAC THENL [MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN MAP_EVERY EXISTS_TAC [q73, q72] THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, RING_OF_NUM, RING_OF_NUM_EQ_0, DIVIDES_ZERO, ARITH_EQ, RING_ADD, RING_POW, RING_MUL, RING_OF_INT] THEN UNDISCH_TAC q71 THEN REWRITE_TAC [RING_OF_INT_ADD, RING_OF_INT_MUL, RING_OF_INT_OF_NUM] THEN MP_TAC v70 THEN ASM_SIMP_TAC [RING_OF_INT], ALL_TAC] THEN SUBGOAL_THEN q63 ASSUME_TAC THENL [MATCH_MP_TAC RING_OF_INTEGERS_SETADD_SUBRING_GENERATED_LINEAR THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN SUBGOAL_THEN q62 ASSUME_TAC THENL [STRIP_TAC THEN MP_TAC v61 THEN ASM_REWRITE_TAC [PRIME_2], ALL_TAC] THEN SUBGOAL_THEN q56 MP_TAC THENL [CONJ_TAC THEN DISCH_TAC THENL [MATCH_MP_TAC QUADRATIC_DEDEKIND_KUMMER_SPLIT THEN MAP_EVERY EXISTS_TAC [q55, q54, q53, q52, q51] THEN ASM_SIMP_TAC [PRIME_2, i5] THEN REWRITE_TAC [v50] THEN CONV_TAC INT_REDUCE_CONV, MATCH_MP_TAC QUADRATIC_DEDEKIND_KUMMER_INERT THEN MAP_EVERY EXISTS_TAC [q49, q48, q47] THEN ASM_REWRITE_TAC [PRIME_2] THEN X_GEN_TAC q46 THEN DISCH_TAC THEN MP_TAC v45 THEN ASM_REWRITE_TAC [par, v40] THEN CONV_TAC INT_REDUCE_CONV], MP_TAC v39 THEN POP_ASSUM MP_TAC THEN CONV_TAC TAUT])

  let QUADRATIC_FIELD_SPLIT_ODD_PRIME ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← INTEGER_RULE (← q r"!p y a:int. coprime(p,a) /\ p divides (a * y) ==> p divides y")
    let i3a := r1
    let r2 ← INTEGER_RULE (← q r"!p y d:int. p divides y /\ (y * y == d) (mod p) ==> p divides d")
    let i3b := r2
    let r3 ← INTEGER_RULE (← q r"!p y d:int. (y pow 2 == d) (mod p) ==> (y * --y == --d) (mod p)")
    let i6 := r3
    let r4 ← INTEGER_RULE (← q r"!p y:int. (y + --y == &0) (mod p)")
    let i7 := r4
    let r5 ← INT_ARITH (← q r"y - --y:int = &2 * y")
    let r6 ← INTEGER_RULE (← q r"!x y n:int. (x == y) (mod n) <=> n divides (x - y)")
    let r7 ← RING_RULE (← q r"!r x y:A. x IN ring_carrier r /\ y IN ring_carrier r
                ==> ring_sub r x (ring_neg r y) = ring_add r x y")
    prove
      r"!k:A ring x d p y.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
          x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
          squarefree(num_of_int(abs d)) /\ ~(d = &1) /\
          prime p /\ ~(p = 2) /\ ~(&p divides d) /\ (y pow 2 == d) (mod &p)
          ==> prime_ideal (ring_of_integers k)
                (ideal_generated (ring_of_integers k)
                   {ring_of_num k p, ring_sub k x (ring_of_int k y)}) /\
              prime_ideal (ring_of_integers k)
                (ideal_generated (ring_of_integers k)
                   {ring_of_num k p, ring_add k x (ring_of_int k y)}) /\
              ~(ideal_generated (ring_of_integers k)
                  {ring_of_num k p, ring_sub k x (ring_of_int k y)} =
                ideal_generated (ring_of_integers k)
                  {ring_of_num k p, ring_add k x (ring_of_int k y)}) /\
              ideal_generated (ring_of_integers k) {ring_of_num k p} =
              ideal_prod (ring_of_integers k)
                (ideal_generated (ring_of_integers k)
                   {ring_of_num k p, ring_sub k x (ring_of_int k y)})
                (ideal_generated (ring_of_integers k)
                   {ring_of_num k p, ring_add k x (ring_of_int k y)}) /\
              ideal_norm (ring_of_integers k)
                (ideal_generated (ring_of_integers k)
                   {ring_of_num k p, ring_sub k x (ring_of_int k y)}) = p /\
              ideal_norm (ring_of_integers k)
                (ideal_generated (ring_of_integers k)
                   {ring_of_num k p, ring_add k x (ring_of_int k y)}) = p"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← SPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"d:int"), (← q r"p:num")] QUADRATIC_FIELD_SETADD_ODD) THEN MP_TAC (← SPEC (← q r"p:num") PRIME_ODD) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_sub k x (ring_of_int k (--y)) = ring_add k x (ring_of_int k y):A") (fun th => tactic_of do pure (SUBST1_TAC (← SYM th))) THENL [REWRITE_TAC [RING_OF_INT_NEG] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"ring_of_int k y:A")] r7) THEN ASM_REWRITE_TAC [RING_OF_INT], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"p:num"), (← q r"&0:int"), (← q r"d:int"), (← q r"y:int"), (← q r"--y:int"), (← q r"ideal_generated (ring_of_integers k)
                      {ring_of_num k p, ring_sub k x (ring_of_int k y):A}"), (← q r"ideal_generated (ring_of_integers k)
                      {ring_of_num k p, ring_sub k x (ring_of_int k (--y)):A}")] QUADRATIC_DEDEKIND_KUMMER_SPLIT_PRIMES) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_OF_INT_0, RING_MUL_LZERO, RING_ADD_LZERO, RING_OF_INT, i6, i7] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"~(&p divides (d:int))") THEN REWRITE_TAC [] THEN MATCH_MP_TAC i3b THEN EXISTS_TAC (← q r"y:int") THEN ASM_REWRITE_TAC [(← GSYM INT_POW_2)] THEN MATCH_MP_TAC i3a THEN EXISTS_TAC (← q r"&2:int") THEN CONJ_TAC THENL [REWRITE_TAC [(← GSYM num_coprime)] THEN MP_TAC (← SPECL [(← q r"p:num"), (← q r"2")] COPRIME_PRIME_PRIME) THEN ASM_REWRITE_TAC [PRIME_2], UNDISCH_TAC (← q r"((y:int) == --y) (mod &p)") THEN REWRITE_TAC [r6] THEN REWRITE_TAC [r5]], ALL_TAC] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"!z. ring_of_num k p IN
          ideal_generated (ring_of_integers k) {ring_of_num k p, z:A}") ASSUME_TAC THENL [GEN_TAC THEN MATCH_MP_TAC IDEAL_GENERATED_INC_GEN THEN REWRITE_TAC [IN_INSERT] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:num")] RING_OF_NUM) THEN REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ideal_generated (ring_of_integers k)
                        {ring_of_num k p, ring_sub k x (ring_of_int k y):A}"), (← q r"p:num")] RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q), MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ideal_generated (ring_of_integers k)
                        {ring_of_num k p,
                         ring_sub k x (ring_of_int k (--y)):A}"), (← q r"p:num")] RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q)] THEN ASM_REWRITE_TAC [EXP_1])

  let QUADRATIC_FIELD_RAMIFIED_ODD_PRIME ← prove
    r"!k:A ring x d p.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
        squarefree(num_of_int(abs d)) /\ ~(d = &1) /\
        prime p /\ ~(p = 2) /\ &p divides d
        ==> prime_ideal (ring_of_integers k)
              (ideal_generated (ring_of_integers k) {ring_of_num k p, x}) /\
            ideal_generated (ring_of_integers k) {ring_of_num k p} =
            ideal_pow (ring_of_integers k)
              (ideal_generated (ring_of_integers k) {ring_of_num k p, x}) 2 /\
            ideal_norm (ring_of_integers k)
              (ideal_generated (ring_of_integers k) {ring_of_num k p, x}) = p"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← SPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"d:int"), (← q r"p:num")] QUADRATIC_FIELD_SETADD_ODD) THEN MP_TAC (← SPEC (← q r"p:num") PRIME_ODD) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_sub k x (ring_of_int k (&0)) = x:A") (fun th => tactic_of do pure (SUBST1_TAC (← SYM th))) THENL [ASM_SIMP_TAC [RING_OF_INT_0, RING_SUB_RZERO], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"p:num"), (← q r"&0:int"), (← q r"d:int"), (← q r"&0:int"), (← q r"ideal_generated (ring_of_integers k)
                    {ring_of_num k p, ring_sub k x (ring_of_int k (&0)):A}")] QUADRATIC_DEDEKIND_KUMMER_RAMIFIED_PRIME) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_OF_INT_0, RING_MUL_LZERO, RING_ADD_LZERO, RING_OF_INT, INT_ADD_LID, INT_MUL_LZERO] THEN UNDISCH_TAC (← q r"&p divides (d:int)") THEN CONV_TAC INTEGER_RULE, ALL_TAC] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ideal_generated (ring_of_integers k)
                    {ring_of_num k p, ring_sub k x (ring_of_int k (&0)):A}"), (← q r"p:num")] RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q) THEN ASM_REWRITE_TAC [EXP_1] THEN DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC IDEAL_GENERATED_INC_GEN THEN REWRITE_TAC [IN_INSERT] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:num")] RING_OF_NUM) THEN REWRITE_TAC [RING_OF_INTEGERS])

  let QUADRATIC_FIELD_RAMIFIED_TWO ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← INTEGER_RULE (← q r"!x y n:int. (x == y) (mod n) <=> n divides (x - y)")
    let r2 ← INTEGER_RULE (← q r"!d n:int. n divides d
                  ==> (&0 + &0 == &0) (mod n) /\ (&0 * &0 == --d) (mod n)")
    let r3 ← RING_RULE (← q r"!r x:A. x IN ring_carrier r
              ==> ring_add r (ring_1 r) x =
                  ring_sub r x (ring_neg r (ring_1 r))")
    prove
      r"!k:A ring x d.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
          x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
          squarefree(num_of_int(abs d)) /\ ~(d = &1) /\ ~((d == &1) (mod &4))
          ==> prime_ideal (ring_of_integers k)
                (ideal_generated (ring_of_integers k)
                   {ring_of_num k 2,
                    if &2 divides d then x else ring_add k (ring_1 k) x}) /\
              ideal_generated (ring_of_integers k) {ring_of_num k 2} =
              ideal_pow (ring_of_integers k)
                (ideal_generated (ring_of_integers k)
                   {ring_of_num k 2,
                    if &2 divides d then x else ring_add k (ring_1 k) x}) 2 /\
              ideal_norm (ring_of_integers k)
                (ideal_generated (ring_of_integers k)
                   {ring_of_num k 2,
                    if &2 divides d then x else ring_add k (ring_1 k) x}) = 2"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"d:int"), (← q r"x:A")] QUADRATIC_FIELD_RING_OF_INTEGERS) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"ideal_generated (ring_of_integers k) {ring_of_num k 2:A}")] RING_OF_INTEGERS_SETADD_SUBRING_GENERATED_LINEAR) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN DISCH_TAC THEN ABBREV_TAC (← q r"u:int = if &2 divides d then &0 else --(&1)") THEN SUBGOAL_THEN (← q r"(if &2 divides d then x else ring_add k (ring_1 k) x) =
      ring_sub k x (ring_of_int k u:A)") SUBST1_TAC THENL [EXPAND_TAC "u" THEN COND_CASES_TAC THEN ASM_SIMP_TAC [RING_OF_INT_0, RING_SUB_RZERO, RING_OF_INT_NEG, RING_OF_INT_1] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A")] r3) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"2"), (← q r"&0:int"), (← q r"d:int"), (← q r"u:int"), (← q r"ideal_generated (ring_of_integers k)
                      {ring_of_num k 2, ring_sub k x (ring_of_int k u):A}")] QUADRATIC_DEDEKIND_KUMMER_RAMIFIED_PRIME) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_OF_INT_0, RING_MUL_LZERO, RING_ADD_LZERO, RING_OF_INT, PRIME_2] THEN EXPAND_TAC "u" THEN COND_CASES_TAC THENL [MATCH_MP_TAC r2 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN REWRITE_TAC [r1, int_divides] THEN MP_TAC (← SPECL [(← q r"d:int"), (← q r"&2:int")] INT_DIVISION) THEN UNDISCH_TAC (← q r"~(&2 divides (d:int))") THEN REWRITE_TAC [(← GSYM INT_REM_EQ_0)] THEN CONV_TAC INT_REDUCE_CONV THEN REPEAT STRIP_TAC THENL [EXISTS_TAC (← q r"--(&1):int") THEN INT_ARITH_TAC, EXISTS_TAC (← q r"d div &2 + &1:int") THEN ASM_INT_ARITH_TAC], ALL_TAC] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ideal_generated (ring_of_integers k)
                      {ring_of_num k 2, ring_sub k x (ring_of_int k u):A}"), (← q r"2")] RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q) THEN ASM_REWRITE_TAC [EXP_1, PRIME_2] THEN DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC IDEAL_GENERATED_INC_GEN THEN REWRITE_TAC [IN_INSERT] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"2")] RING_OF_NUM) THEN REWRITE_TAC [RING_OF_INTEGERS])

  -- @@RETURN BEGIN
  return { QUADRATIC_FIELD_SETADD_ODD, QUADRATIC_FIELD_RAMIFIED_PRIME,
           QUADRATIC_FIELD_RAMIFIED, QUADRATIC_FIELD_ODD_PRIME,
           QUADRATIC_FIELD_PRIME_TWO, QUADRATIC_FIELD_SPLIT_ODD_PRIME,
           QUADRATIC_FIELD_RAMIFIED_ODD_PRIME, QUADRATIC_FIELD_RAMIFIED_TWO }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- quadratic_split.ml phrases from line 1366 to 1366                      -/
/- ---------------------------------------------------------------------- -/

structure QuadraticSplit03 where
  -- @@FIELDS
  QUADRATIC_FIELD_SPLIT_TWO : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupQuadraticSplit03 [HolBase] (D : QuadraticSplitDeps) (BQuadraticSplit01 : QuadraticSplit01) :
    ExceptT String IO QuadraticSplit03 := do
  -- @@SCOPE BEGIN
  let { ASM_INT_ARITH_TAC, ASM_MESON_TAC, INTEGER_RULE, INT_ARITH, INT_REDUCE_CONV,
        RING_RULE, .. } := D
  let { ARITH_EQ, EXP_1, FIELD_IMP_INTEGRAL_DOMAIN, IDEAL_GENERATED_INC_GEN,
        IDEAL_GENERATED_PAIR_EQ, INTEGRAL_DOMAIN_MUL_LCANCEL, INT_CONG_REFL,
        INT_DIVIDES_ONE, INT_DIV_MUL, IN_INSERT, IN_RING_IDEAL_NEG,
        NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_RING_OF_NUM_EQ_0, .. } := D.core1
  let { PRIME_2, RING_1, RING_ADD, RING_IDEAL_IDEAL_GENERATED, RING_MUL, RING_OF_INT,
        RING_OF_INTEGERS, RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q, RING_OF_INTEGERS_SUBSET,
        RING_OF_INT_0, RING_OF_INT_1, RING_OF_INT_MUL, RING_OF_INT_OF_NUM,
        RING_OF_INT_SUB, RING_OF_NUM, RING_POW, RING_SUB, RING_SUB_RZERO, SUBSET,
        int_divides, .. } := D.core2
  let { QUADRATIC_DEDEKIND_KUMMER_SPLIT_PRIMES, QUADRATIC_FIELD_RING_OF_INTEGERS,
        RING_OF_INTEGERS_SETADD_SUBRING_GENERATED_LINEAR, .. } := BQuadraticSplit01
  -- @@SCOPE END

  let QUADRATIC_FIELD_SPLIT_TWO ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!r w:A. w IN ring_carrier r
              ==> ring_sub r (ring_1 r) w =
                  ring_neg r (ring_sub r w (ring_1 r)) /\
                  ring_sub r w (ring_1 r) =
                  ring_neg r (ring_sub r (ring_1 r) w)")
    let r2 ← INTEGER_RULE (← q r"!c n:int. n divides c ==> (&0 * &1 == --c) (mod n)")
    let r3 ← INTEGER_RULE (← q r"!x y n:int. (x == y) (mod n) <=> n divides (y - x)")
    let r4 ← RING_RULE (← q r"!r x w u e:A. x IN ring_carrier r /\ w IN ring_carrier r /\
                    u IN ring_carrier r /\ e IN ring_carrier r /\
                    ring_mul r (ring_of_num r 2) w = ring_add r (ring_1 r) x /\
                    ring_pow r x 2 = e /\
                    ring_mul r (ring_of_num r 4) u = ring_sub r e (ring_1 r)
                    ==> ring_mul r (ring_of_num r 4) (ring_pow r w 2) =
                        ring_mul r (ring_of_num r 4)
                          (ring_add r (ring_mul r (ring_1 r) w) u)")
    let r5 ← INT_ARITH (← q r"&8 * q:int = (&2 * q) * &4")
    let r10 ← INTEGER_RULE (← q r"!x y n:int. (x == y) (mod n) <=> n divides (x - y)")
    let r11 ← INTEGER_RULE (← q r"!x y n:int. (x == y) (mod n) <=> n divides (x - y)")
    prove
      r"!k:A ring x d w.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
          x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
          squarefree(num_of_int(abs d)) /\ ~(d = &1) /\ (d == &1) (mod &8) /\
          w = ring_div k (ring_add k (ring_1 k) x) (ring_of_num k 2)
          ==> prime_ideal (ring_of_integers k)
                (ideal_generated (ring_of_integers k) {ring_of_num k 2, w}) /\
              prime_ideal (ring_of_integers k)
                (ideal_generated (ring_of_integers k)
                   {ring_of_num k 2, ring_sub k (ring_1 k) w}) /\
              ~(ideal_generated (ring_of_integers k) {ring_of_num k 2, w} =
                ideal_generated (ring_of_integers k)
                  {ring_of_num k 2, ring_sub k (ring_1 k) w}) /\
              ideal_generated (ring_of_integers k) {ring_of_num k 2} =
              ideal_prod (ring_of_integers k)
                (ideal_generated (ring_of_integers k) {ring_of_num k 2, w})
                (ideal_generated (ring_of_integers k)
                   {ring_of_num k 2, ring_sub k (ring_1 k) w}) /\
              ideal_norm (ring_of_integers k)
                (ideal_generated (ring_of_integers k) {ring_of_num k 2, w}) = 2 /\
              ideal_norm (ring_of_integers k)
                (ideal_generated (ring_of_integers k)
                   {ring_of_num k 2, ring_sub k (ring_1 k) w}) = 2"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM (ASSUME_TAC o (SYM o (checkM (fun th => (do if ← (do let z12 ← (do let z13 ← (pure th); pure (concl z13)); pure (is_eq z12)) then (do let z17 ← (q r"w:A"); let z16 ← (do let z14 ← (do let z15 ← (pure th); pure (concl z15)); liftExcept (lhand z14)); pure (z16 == z17)) else pure false))))) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN)) THEN SUBGOAL_THEN (← q r"((d:int) == &1) (mod &4)") ASSUME_TAC THENL [UNDISCH_TAC (← q r"(d:int == &1) (mod &8)") THEN REWRITE_TAC [r11, int_divides] THEN STRIP_TAC THEN EXISTS_TAC (← q r"&2 * x':int") THEN ASM_INT_ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"d:int"), (← q r"w:A")] QUADRATIC_FIELD_RING_OF_INTEGERS) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"w:A"), (← q r"ideal_generated (ring_of_integers k) {ring_of_num k 2:A}")] RING_OF_INTEGERS_SETADD_SUBRING_GENERATED_LINEAR) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(w:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN ABBREV_TAC (← q r"c = (d - &1) div &4:int") THEN SUBGOAL_THEN (← q r"&4 * c:int = d - &1 /\ &2 divides c") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"(d:int == &1) (mod &8)") THEN REWRITE_TAC [r10, int_divides] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"q:int")) THEN SUBGOAL_THEN (← q r"c:int = &2 * q") (fun th => REWRITE_TAC [th]) THENL [EXPAND_TAC "c" THEN FIRST_X_ASSUM (SUBST1_TAC o (checkM (fun th => (do let z9 ← (q r"d - &1:int"); let z8 ← (do let z6 ← (do let z7 ← (pure th); pure (concl z7)); liftExcept (lhand z6)); pure (z8 == z9))))) THEN REWRITE_TAC [r5] THEN MATCH_MP_TAC (← CONJUNCT1 INT_DIV_MUL) THEN CONV_TAC INT_REDUCE_CONV, CONJ_TAC THENL [ASM_INT_ARITH_TAC, EXISTS_TAC (← q r"q:int") THEN REFL_TAC]], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_pow k w 2 =
      ring_add k (ring_mul k (ring_of_int k (&1)) w) (ring_of_int k c):A") ASSUME_TAC THENL [MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN MAP_EVERY EXISTS_TAC [(← q r"k:A ring"), (← q r"ring_of_num k 4:A")] THEN ASM_SIMP_TAC [RING_OF_NUM, RING_ADD, RING_MUL, RING_POW, RING_OF_INT, NUMBER_FIELD_RING_OF_NUM_EQ_0, ARITH_EQ] THEN SUBGOAL_THEN (← q r"ring_mul k (ring_of_num k 4) (ring_of_int k c) =
                    ring_sub k (ring_of_int k d) (ring_1 k):A") MP_TAC THENL [REWRITE_TAC [(← GSYM RING_OF_INT_OF_NUM), (← GSYM RING_OF_INT_MUL), (← GSYM RING_OF_INT_1), (← GSYM RING_OF_INT_SUB)] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_TAC THEN REWRITE_TAC [RING_OF_INT_1] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"w:A"), (← q r"ring_of_int k c:A"), (← q r"ring_of_int k d:A")] r4) THEN ASM_REWRITE_TAC [RING_OF_INT], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"w:A"), (← q r"2"), (← q r"&1:int"), (← q r"c:int"), (← q r"&0:int"), (← q r"&1:int"), (← q r"ideal_generated (ring_of_integers k)
                      {ring_of_num k 2, ring_sub k w (ring_of_int k (&0)):A}"), (← q r"ideal_generated (ring_of_integers k)
                      {ring_of_num k 2, ring_sub k w (ring_of_int k (&1)):A}")] QUADRATIC_DEDEKIND_KUMMER_SPLIT_PRIMES) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [PRIME_2] THEN REPEAT CONJ_TAC THENL [REWRITE_TAC [r3] THEN CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC [INT_DIVIDES_ONE] THEN CONV_TAC INT_REDUCE_CONV, CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC [INT_CONG_REFL], MATCH_MP_TAC r2 THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sub k w (ring_of_int k (&0)) = w /\
      ideal_generated (ring_of_integers k)
        {ring_of_num k 2, ring_sub k w (ring_of_int k (&1))} =
      ideal_generated (ring_of_integers k)
        {ring_of_num k 2, ring_sub k (ring_1 k) w:A}") (fun th => REWRITE_TAC [th]) THENL [ASM_SIMP_TAC [RING_OF_INT_0, RING_SUB_RZERO, RING_OF_INT_1] THEN MATCH_MP_TAC IDEAL_GENERATED_PAIR_EQ THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"2")] RING_OF_NUM) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"w:A"), (← q r"ring_1 k:A")] RING_SUB) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_1 k:A"), (← q r"w:A")] RING_SUB) THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_1) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN ASM_SIMP_TAC [] THEN REPEAT DISCH_TAC THEN X_GEN_TAC (← q r"j:A->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"w:A")] r1) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"j:A->bool")] IN_RING_IDEAL_NEG)) THEN ASM_MESON_TAC [], ALL_TAC] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"!z. ring_of_num k 2 IN
          ideal_generated (ring_of_integers k) {ring_of_num k 2, z:A}") ASSUME_TAC THENL [GEN_TAC THEN MATCH_MP_TAC IDEAL_GENERATED_INC_GEN THEN REWRITE_TAC [IN_INSERT] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"2")] RING_OF_NUM) THEN REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ideal_generated (ring_of_integers k)
                        {ring_of_num k 2, w:A}"), (← q r"2")] RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q), MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ideal_generated (ring_of_integers k)
                        {ring_of_num k 2, ring_sub k (ring_1 k) w:A}"), (← q r"2")] RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q)] THEN ASM_REWRITE_TAC [EXP_1, PRIME_2])

  -- @@RETURN BEGIN
  return { QUADRATIC_FIELD_SPLIT_TWO }
  -- @@RETURN END

end HolANT.QuadraticSplit
