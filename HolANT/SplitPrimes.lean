/- ========================================================================= -/
/- ANT: Infinitely many primes split completely in any finite ...          -/
/- ========================================================================= -/
/- File: HolANT/SplitPrimes.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/split_primes.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antsplitprimesdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/frag.ml, Library/grouptheory.ml, Library/symmetric_group.ml, Library/galois.ml, Library/integer.ml, Library/isum.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/prime_split.ml, ANT/norm_index.ml, ANT/discriminant.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/classgroup.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/relative_degree.ml, ANT/nf_valuation.ml, ANT/integrality.ml, ANT/dedekind_kummer.ml, ANT/finite_field_trace.ml, ANT/ramification.ml, ANT/splitting_types.ml, Library/ring_groups.ml, Library/finite_fields.ml, ANT/decomposition.ml, ANT/nf_decomposition.ml, ANT/decomposition_field.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.SplitPrimes fills them).

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
import HolLibrary.Frag
import HolLibrary.GroupTheory
import HolLibrary.SymmetricGroup
import HolLibrary.Galois
import HolLibrary.Integer
import HolLibrary.Isum
import HolLibrary.Products
import HolLibrary.Multiplicative
import HolLibrary.Primitive
import HolANT.Algmisc
import HolANT.Integral
import HolANT.IdealArith
import HolANT.Dedekind
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolANT.DedekindStruct
import HolANT.IdealNorm
import HolANT.RingOfIntegers
import HolANT.PrimeSplit
import HolANT.NormIndex
import HolANT.Discriminant
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.Classgroup
import HolANT.TraceForm
import HolANT.RelativeSplit
import HolANT.RelativeDegree
import HolANT.NfValuation
import HolANT.Integrality
import HolANT.DedekindKummer
import HolANT.FiniteFieldTrace
import HolANT.Ramification
import HolANT.SplittingTypes
import HolLibrary.RingGroups
import HolLibrary.FiniteFields
import HolANT.Decomposition
import HolANT.NfDecomposition
import HolANT.DecompositionField

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
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.Classgroup
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.RelativeDegree
open HolANT.NfValuation
open HolANT.Integrality
open HolANT.DedekindKummer
open HolANT.FiniteFieldTrace
open HolANT.Ramification
open HolANT.SplittingTypes
open HolANT.Decomposition
open HolANT.NfDecomposition
open HolANT.DecompositionField

namespace HolANT.SplitPrimes

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH DECOMPOSITION_GROUP
   DEDEKIND_IDEAL_FACTORIZATION DEDEKIND_RING_OF_INTEGERS DE_MORGAN_THM
   DIVIDES_ZERO EQ_IMP EQ_MULT_LCANCEL EXISTS_IN_GSPEC EXTENSION
   EXTENSION_DEGREE_EQ_IMAGE EXTENSION_DEGREE_SIMPLE
   FIELD_EXTENSION_FROM_SUBFIELD_GENERATED FIELD_EXTENSION_SUBFIELD_GENERATED
   FIELD_IMP_INTEGRAL_DOMAIN FIELD_IMP_NONTRIVIAL_RING
   FIELD_RING_HOMOMORPHISM_MONOMORPHISM FIELD_SUBFIELD_GENERATED
   FINITE_EXTENSION_EQ_IMAGE FINITE_EXTENSION_NORMAL_CLOSURE FINITE_GALOIS_GROUP
   FINITE_IMAGE FINITE_IMAGE_INJ FINITE_IMP_ALGEBRAIC_EXTENSION
   FINITE_IMP_FIELD_EXTENSION FINITE_RESTRICT FINITE_SUBSET FINITE_UNION
   FINITE_UNIONS FORALL_IN_GSPEC FORALL_IN_IMAGE FUN_EQ_THM FUN_IN_IMAGE
   GALOIS_EXTENSION_EQ_CARD GALOIS_EXTENSION_INTERMEDIATE GALOIS_GROUP_EQ_IMAGE
   GALOIS_GROUP_EQ_ON_GENERATORS GALOIS_GROUP_I GALOIS_GROUP_INVERSE
   GALOIS_GROUP_PERMUTES GALOIS_GROUP_PRIME_IDEAL_IMAGE
   GALOIS_GROUP_RING_HOMOMORPHISM GALOIS_GROUP_RING_OF_INTEGERS GROUP_ID
   IDEAL_GENERATED_INC IDEAL_GENERATED_MINIMAL IMAGE_I IMP_CONJ_ALT INFINITE
   INFINITE_DIFF_FINITE INFINITE_IMAGE INFINITE_NONEMPTY INFINITE_SUPERSET
   INTEGER_RING INTEGER_RING_DIVIDES INTEGRAL_DOMAIN_INTEGER_RING INT_ABS
   INT_ABS_POS INT_ABS_ZERO INT_DIVIDES_LABS INT_DIVIDES_LMUL INT_DIVIDES_ONE
   INT_DIVIDES_REFL INT_DIVIDES_SUB INT_ENTIRE INT_MUL_RID INT_MUL_RNEG
   INT_OF_NUM_EQ INT_OF_NUM_MUL INT_OF_NUM_OF_INT INT_PRIME INT_PRIME_1
   INT_PRIME_ABS INT_PRIME_FACTOR INT_PRIME_NEG INT_SUB_RZERO IN_DIFF
   IN_ELIM_THM IN_IDEAL_GENERATED_SING_EQ IN_IMAGE IN_RING_IDEAL_SUB
   IN_RING_POLYNOMIAL_CARRIER_COMPOSE IN_SING IN_UNION IN_UNIONS IN_UNIV I_O_ID
   I_THM LT_NZ MEMBER_NOT_EMPTY MONIC_HOMOMORPHIC_IMAGE
   MONIC_POLY_EQ_ROOTS_PRODUCT MONO_EXISTS MULT_EQ_1 : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (NOT_EXISTS_THM NPRODUCT_DELETE NPRODUCT_POS_LT NUMBER_FIELD_DEGREE_POS
   NUMBER_FIELD_GALOIS_SPLITTING_TYPES NUMBER_FIELD_HOMOMORPHIC_PREIMAGE
   NUMBER_FIELD_IMP_FIELD NUMBER_FIELD_INTEGRAL_PRIMITIVE_ELEMENT
   NUMBER_FIELD_PRIME_IDEALS_ABOVE NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q
   NUMBER_FIELD_PRIME_SUBFIELD NUMBER_FIELD_RAMIFICATION_INDEX_TOWER_Q
   NUMBER_FIELD_RESIDUE_DEGREE_TOWER_Q NUMBER_FIELD_TOWER_LAW
   PERFECT_FIELD_CHAR_0 PERFECT_FIELD_IMP_SEPARABLE_EXTENSION PERMUTES_INVERSES
   POLY_CONST POLY_DEG_CONST POLY_EVALUATE_SUB_IN_IDEAL POLY_EVAL_CONST
   POLY_EVAL_HOMOMORPHIC_IMAGE POLY_EVAL_RING_PRODUCT POLY_EVAL_SUB
   POLY_EVAL_VAR POLY_EXTEND_EVALUATE POLY_EXTEND_HOMOMORPHIC_IMAGE
   POLY_RING_CLAUSES POLY_ROOT_BOUND POLY_X_MINUS_A_IN_CARRIER PRIMES_INFINITE
   PRIME_0 PRIME_IDEAL_IMP_SUBSET PRIME_IMP_NZ PRIME_IMP_RING_IDEAL
   PRIME_SUBFIELD_MONOMORPHIC_IMAGE PRIME_SUBFIELD_SUBFIELD_GENERATED
   PRIME_SUBFIELD_TOWER_LAW RING_CARRIER_SUBFIELD_GENERATED_SUBSET
   RING_CHAR_SUBFIELD_GENERATED RING_HOMOMORPHISM_0 RING_HOMOMORPHISM_COMPOSE
   RING_HOMOMORPHISM_INTEGER_RING_OF_INT RING_HOMOMORPHISM_INTO_SUBRING
   RING_HOMOMORPHISM_IN_CARRIER RING_HOMOMORPHISM_RING_OF_INT
   RING_HOMOMORPHISM_RING_OF_INTEGERS RING_HOMOMORPHISM_RING_OF_NUM
   RING_HOMOMORPHISM_SUB RING_HOMOMORPHISM_SUBFIELD_INCLUSION
   RING_IDEAL_IDEAL_GENERATED RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_OF_INT
   RING_OF_INTEGERS RING_OF_INTEGERS_INTEGER_MINIMAL_POLYNOMIAL
   RING_OF_INTEGERS_PRIME_SUBFIELD_IDEAL RING_OF_INTEGERS_SUBRING
   RING_OF_INTEGERS_SUBSET RING_OF_INT_IN_PRIME_IDEAL
   RING_OF_INT_IN_RING_OF_INTEGERS RING_OF_NUM_EQ_0 RING_OF_NUM_IN_PRIME_IDEAL
   RING_POLYNOMIAL RING_POLYNOMIAL_CONST RING_POLYNOMIAL_VAR RING_PRODUCT_EQ
   RING_PRODUCT_IN_PRIME_IDEAL RING_PRODUCT_SUBRING_GENERATED_GEN RING_SUB
   RING_SUB_EQ_0 SIMPLE_IMAGE SING_SUBSET SPLITTING_TYPES_INTEGER_RING
   SPLITTING_TYPES_PRIME_SUBFIELD SUBFIELD_GENERATED SUBFIELD_GENERATED_EQ
   SUBRING_GENERATED_BY_SUBFIELD_GENERATED SUBRING_SUBSET_SUBFIELD_GENERATED
   SUBSET SUBSET_ANTISYM algebraic_extension divides field_extension
   finite_extension galois_extension int_divides num_INFINITE num_divides
   number_field o_THM poly_eval ring_homomorphism ring_sub totally_split : thm)
  deriving Inhabited

/-- What split_primes.ml uses from Session besides theorems. -/
structure SplitPrimesDeps where
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
  GROUP_RULE : term → ExceptT String IO thm  -- grouptheory.ml's GROUP_RULE
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
  INT_RING : term → ExceptT String IO thm
  SELECT_CONV : ioconv
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
/- split_primes.ml phrases from line 78 to 479                            -/
/- ---------------------------------------------------------------------- -/

structure SplitPrimes01 where
  -- @@FIELDS
  INTEGER_POLY_CONGRUENCE : thm
  INTEGER_POLY_FIBRE_FINITE : thm
  INTEGER_POLY_PRIME_DIVISORS_INFINITE : thm
  NUMBER_FIELD_GALOIS_CONJUGATES_POLY : thm
  NUMBER_FIELD_GALOIS_RATIONAL_TOTALLY_SPLIT : thm
  NUMBER_FIELD_RATIONAL_PRIMES_CONTAINING_FINITE : thm
  NUMBER_FIELD_GALOIS_TOTALLY_SPLIT_INFINITE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupSplitPrimes01 [HolBase] (D : SplitPrimesDeps) :
    ExceptT String IO SplitPrimes01 := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_MESON_TAC, INT_ARITH, INT_ARITH_TAC, INT_RING, MESON_TAC,
        RING_RULE, SET_RULE, SET_TAC, TAUT, .. } := D
  let { DECOMPOSITION_GROUP, DEDEKIND_IDEAL_FACTORIZATION, DEDEKIND_RING_OF_INTEGERS,
        DE_MORGAN_THM, EQ_IMP, EQ_MULT_LCANCEL, EXISTS_IN_GSPEC, EXTENSION,
        EXTENSION_DEGREE_SIMPLE, FIELD_IMP_INTEGRAL_DOMAIN, FIELD_IMP_NONTRIVIAL_RING,
        FIELD_SUBFIELD_GENERATED, FINITE_GALOIS_GROUP, FINITE_IMAGE, FINITE_IMAGE_INJ,
        FINITE_IMP_ALGEBRAIC_EXTENSION, FINITE_IMP_FIELD_EXTENSION, FINITE_RESTRICT,
        FINITE_SUBSET, FINITE_UNION, FINITE_UNIONS, FORALL_IN_GSPEC, FORALL_IN_IMAGE,
        FUN_EQ_THM, FUN_IN_IMAGE, GALOIS_EXTENSION_EQ_CARD,
        GALOIS_GROUP_EQ_ON_GENERATORS, GALOIS_GROUP_I, GALOIS_GROUP_INVERSE,
        GALOIS_GROUP_PERMUTES, GALOIS_GROUP_PRIME_IDEAL_IMAGE,
        GALOIS_GROUP_RING_HOMOMORPHISM, GALOIS_GROUP_RING_OF_INTEGERS, GROUP_ID,
        IDEAL_GENERATED_INC, IDEAL_GENERATED_MINIMAL, IMAGE_I, INFINITE,
        INFINITE_DIFF_FINITE, INFINITE_NONEMPTY, INFINITE_SUPERSET, INTEGER_RING,
        INTEGER_RING_DIVIDES, INTEGRAL_DOMAIN_INTEGER_RING, INT_ABS, INT_ABS_POS,
        INT_ABS_ZERO, INT_DIVIDES_LABS, INT_DIVIDES_LMUL, INT_DIVIDES_ONE,
        INT_DIVIDES_REFL, INT_DIVIDES_SUB, INT_ENTIRE, INT_MUL_RID, INT_MUL_RNEG,
        INT_OF_NUM_EQ, INT_OF_NUM_MUL, INT_OF_NUM_OF_INT, INT_PRIME, INT_PRIME_1,
        INT_PRIME_ABS, INT_PRIME_FACTOR, INT_PRIME_NEG, INT_SUB_RZERO, IN_DIFF,
        IN_ELIM_THM, IN_IDEAL_GENERATED_SING_EQ, IN_IMAGE, IN_RING_IDEAL_SUB,
        IN_RING_POLYNOMIAL_CARRIER_COMPOSE, IN_SING, IN_UNION, IN_UNIONS, IN_UNIV,
        I_THM, LT_NZ, MEMBER_NOT_EMPTY, MONIC_HOMOMORPHIC_IMAGE,
        MONIC_POLY_EQ_ROOTS_PRODUCT, .. } := D.core1
  let { NOT_EXISTS_THM, NPRODUCT_DELETE, NPRODUCT_POS_LT, NUMBER_FIELD_DEGREE_POS,
        NUMBER_FIELD_GALOIS_SPLITTING_TYPES, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_INTEGRAL_PRIMITIVE_ELEMENT, NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q,
        PERMUTES_INVERSES, POLY_CONST, POLY_DEG_CONST, POLY_EVALUATE_SUB_IN_IDEAL,
        POLY_EVAL_CONST, POLY_EVAL_HOMOMORPHIC_IMAGE, POLY_EVAL_RING_PRODUCT,
        POLY_EVAL_SUB, POLY_EVAL_VAR, POLY_EXTEND_EVALUATE,
        POLY_EXTEND_HOMOMORPHIC_IMAGE, POLY_RING_CLAUSES, POLY_ROOT_BOUND,
        POLY_X_MINUS_A_IN_CARRIER, PRIMES_INFINITE, PRIME_IDEAL_IMP_SUBSET,
        PRIME_IMP_NZ, PRIME_IMP_RING_IDEAL, RING_CARRIER_SUBFIELD_GENERATED_SUBSET,
        RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_INTEGER_RING_OF_INT,
        RING_HOMOMORPHISM_IN_CARRIER, RING_HOMOMORPHISM_RING_OF_INT,
        RING_HOMOMORPHISM_RING_OF_INTEGERS, RING_HOMOMORPHISM_RING_OF_NUM,
        RING_HOMOMORPHISM_SUB, RING_HOMOMORPHISM_SUBFIELD_INCLUSION,
        RING_IDEAL_IDEAL_GENERATED, RING_OF_INT, RING_OF_INTEGERS,
        RING_OF_INTEGERS_INTEGER_MINIMAL_POLYNOMIAL,
        RING_OF_INTEGERS_PRIME_SUBFIELD_IDEAL, RING_OF_INTEGERS_SUBRING,
        RING_OF_INTEGERS_SUBSET, RING_OF_INT_IN_PRIME_IDEAL,
        RING_OF_INT_IN_RING_OF_INTEGERS, RING_OF_NUM_IN_PRIME_IDEAL, RING_POLYNOMIAL,
        RING_POLYNOMIAL_CONST, RING_POLYNOMIAL_VAR, RING_PRODUCT_EQ,
        RING_PRODUCT_IN_PRIME_IDEAL, RING_PRODUCT_SUBRING_GENERATED_GEN, RING_SUB,
        RING_SUB_EQ_0, SIMPLE_IMAGE, SING_SUBSET, SPLITTING_TYPES_PRIME_SUBFIELD,
        SUBFIELD_GENERATED, SUBFIELD_GENERATED_EQ, SUBRING_SUBSET_SUBFIELD_GENERATED,
        SUBSET, SUBSET_ANTISYM, algebraic_extension, divides, field_extension,
        finite_extension, int_divides, num_INFINITE, num_divides, number_field, o_THM,
        poly_eval, ring_homomorphism, ring_sub, .. } := D.core2
  -- @@SCOPE END

  let INTEGER_POLY_CONGRUENCE ← prove
    r"!q m x y.
        q IN ring_carrier(poly_ring integer_ring (:1)) /\ m divides (x - y)
        ==> m divides (poly_eval integer_ring q x -
                       poly_eval integer_ring q y)"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"!a b. ring_sub integer_ring a b = a - b") ASSUME_TAC THENL [REWRITE_TAC [ring_sub, INTEGER_RING] THEN INT_ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"ideal_generated integer_ring {m:int}"), (← q r"q:(1->num)->int"), (← q r"y:int"), (← q r"x:int")] POLY_EVALUATE_SUB_IN_IDEAL) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, INTEGER_RING, IN_UNIV] THEN SIMP_TAC [IN_IDEAL_GENERATED_SING_EQ, INTEGER_RING, IN_UNIV, INTEGER_RING_DIVIDES, poly_eval] THEN ASM_REWRITE_TAC [])

  let INTEGER_POLY_FIBRE_FINITE ← prove
    r"!q v. q IN ring_carrier(poly_ring integer_ring (:1)) /\
         ~(poly_deg integer_ring q = 0)
         ==> FINITE {x | poly_eval integer_ring q x = v}"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"poly_sub integer_ring (q:(1->num)->int)
                    (poly_const integer_ring v)")] POLY_ROOT_BOUND) THEN SUBGOAL_THEN (← q r"(poly_const integer_ring v:(1->num)->int) IN
    ring_carrier(poly_ring integer_ring (:1))") ASSUME_TAC THENL [REWRITE_TAC [POLY_CONST, INTEGER_RING, IN_UNIV], ALL_TAC] THEN SUBGOAL_THEN (← q r"poly_sub integer_ring = ring_sub (poly_ring integer_ring (:1))") SUBST1_TAC THENL [REWRITE_TAC [POLY_RING_CLAUSES], ALL_TAC] THEN ANTS_TAC THENL [REWRITE_TAC [INTEGRAL_DOMAIN_INTEGER_RING] THEN CONJ_TAC THENL [MATCH_MP_TAC RING_SUB THEN ASM_REWRITE_TAC [], ASM_SIMP_TAC [RING_SUB_EQ_0] THEN DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~(poly_deg integer_ring (poly_const integer_ring v:(1->num)->int) =
          0)") THEN REWRITE_TAC [POLY_DEG_CONST]], DISCH_THEN (MP_TAC o CONJUNCT1)] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM, INTEGER_RING, IN_UNIV] THEN X_GEN_TAC (← q r"x:int") THEN REWRITE_TAC [POLY_RING_CLAUSES] THEN wPart (lhand o lhand) (lhand o rand) POLY_EVAL_SUB THEN ANTS_TAC THENL [REWRITE_TAC [RING_POLYNOMIAL] THEN ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN SIMP_TAC [POLY_EVAL_CONST, INTEGER_RING, IN_UNIV] THEN REWRITE_TAC [ring_sub, INTEGER_RING] THEN INT_ARITH_TAC)

  let INTEGER_POLY_PRIME_DIVISORS_INFINITE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← INT_ARITH (← q r"abs(z:int) = &1 <=> z = &1 \/ z = -- &1")
    prove
      r"!q. q IN ring_carrier(poly_ring integer_ring (:1)) /\
         ~(poly_deg integer_ring q = 0)
         ==> INFINITE {p | prime p /\
                           ?n. &p divides poly_eval integer_ring q (&n)}"
      (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"c = poly_eval integer_ring (q:(1->num)->int) (&0)") THEN REWRITE_TAC [INFINITE] THEN ABBREV_TAC (← q r"S = {p | prime p /\ ?n. &p divides poly_eval integer_ring q (&n)}") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"c:int = &0") THENL [UNDISCH_TAC (← q r"FINITE(S:num->bool)") THEN REWRITE_TAC [(← GSYM INFINITE)] THEN MATCH_MP_TAC INFINITE_SUPERSET THEN EXISTS_TAC (← q r"{p | prime p}") THEN REWRITE_TAC [PRIMES_INFINITE] THEN EXPAND_TAC "S" THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC (← q r"p:num") THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"p:num") THEN MP_TAC (← ISPECL [(← q r"q:(1->num)->int"), (← q r"&p:int"), (← q r"&p:int"), (← q r"&0:int")] INTEGER_POLY_CONGRUENCE) THEN ASM_REWRITE_TAC [INT_SUB_RZERO, INT_DIVIDES_REFL], ALL_TAC] THEN ABBREV_TAC (← q r"P = nproduct S (\p:num. p)") THEN SUBGOAL_THEN (← q r"!p:num. p IN S ==> p divides P") ASSUME_TAC THENL [X_GEN_TAC (← q r"p:num") THEN DISCH_TAC THEN EXPAND_TAC "P" THEN MP_TAC (← ISPECL [(← q r"\p:num. p"), (← q r"S:num->bool"), (← q r"p:num")] NPRODUCT_DELETE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [divides] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(P:num = 0)") ASSUME_TAC THENL [EXPAND_TAC "P" THEN REWRITE_TAC [(← GSYM LT_NZ)] THEN MATCH_MP_TAC NPRODUCT_POS_LT THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "S" THEN SIMP_TAC [IN_ELIM_THM, LT_NZ, PRIME_IMP_NZ], ALL_TAC] THEN ABBREV_TAC (← q r"M = num_of_int(abs c) * P") THEN SUBGOAL_THEN (← q r"&M:int = abs c * &P") ASSUME_TAC THENL [EXPAND_TAC "M" THEN SIMP_TAC [(← GSYM INT_OF_NUM_MUL), INT_OF_NUM_OF_INT, INT_ABS_POS], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(M:num = 0)") ASSUME_TAC THENL [REWRITE_TAC [(← GSYM INT_OF_NUM_EQ)] THEN ASM_REWRITE_TAC [INT_ENTIRE] THEN ASM_REWRITE_TAC [INT_ABS_ZERO, INT_OF_NUM_EQ], ALL_TAC] THEN SUBGOAL_THEN (← q r"?t. ~(poly_eval integer_ring q (&(M * t)) = c) /\
          ~(poly_eval integer_ring q (&(M * t)) = --c)") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"\t. &(M * t):int"), (← q r"{x | poly_eval integer_ring q x = c} UNION
                      {x | poly_eval integer_ring q x = --c}")] FINITE_IMAGE_INJ) THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_UNION, INTEGER_POLY_FIBRE_FINITE] THEN REWRITE_TAC [INT_OF_NUM_EQ, EQ_MULT_LCANCEL] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN REWRITE_TAC [IN_UNION, IN_ELIM_THM] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"(:num)"), (← q r"{t | poly_eval integer_ring q (&(M * t)) = c \/
              poly_eval integer_ring q (&(M * t)) = --c}")] INFINITE_DIFF_FINITE) THEN ASM_REWRITE_TAC [num_INFINITE] THEN DISCH_THEN (MP_TAC o (MATCH_MP INFINITE_NONEMPTY)) THEN REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY), IN_DIFF, IN_UNIV, IN_ELIM_THM, DE_MORGAN_THM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"q:(1->num)->int"), (← q r"&(M * t):int"), (← q r"&(M * t):int"), (← q r"&0:int")] INTEGER_POLY_CONGRUENCE) THEN ASM_REWRITE_TAC [INT_SUB_RZERO, INT_DIVIDES_REFL] THEN REWRITE_TAC [int_divides] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"u:int")) THEN SUBGOAL_THEN (← q r"poly_eval integer_ring q (&(M * t)) =
      c * (&1 + (if &0 <= c then &1 else -- &1) * &P * &t * u)") ASSUME_TAC THENL [UNDISCH_TAC (← q r"poly_eval integer_ring q (&(M * t)) - c = &(M * t) * u") THEN REWRITE_TAC [(← GSYM INT_OF_NUM_MUL)] THEN UNDISCH_TAC (← q r"&M:int = abs c * &P") THEN DISCH_THEN SUBST1_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [INT_ABS] THEN CONV_TAC INT_RING, ALL_TAC] THEN ABBREV_TAC (← q r"z:int = &1 + (if &0 <= (c:int) then &1 else -- &1) * &P * &t * u") THEN MP_TAC (← SPEC (← q r"z:int") INT_PRIME_FACTOR) THEN ANTS_TAC THENL [REWRITE_TAC [r1] THEN STRIP_TAC THEN UNDISCH_TAC (← q r"poly_eval integer_ring q (&(M * t)) = c * z") THEN ASM_REWRITE_TAC [INT_MUL_RID, INT_MUL_RNEG], DISCH_THEN (X_CHOOSE_THEN (← q r"r:int") STRIP_ASSUME_TAC)] THEN SUBGOAL_THEN (← q r"num_of_int(abs r) IN S") ASSUME_TAC THENL [EXPAND_TAC "S" THEN REWRITE_TAC [IN_ELIM_THM] THEN CONJ_TAC THENL [REWRITE_TAC [(← GSYM INT_PRIME)] THEN SIMP_TAC [INT_OF_NUM_OF_INT, INT_ABS_POS, INT_PRIME_ABS] THEN ASM_REWRITE_TAC [], EXISTS_TAC (← q r"M * t:num") THEN SIMP_TAC [INT_OF_NUM_OF_INT, INT_ABS_POS, INT_DIVIDES_LABS] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC INT_DIVIDES_LMUL THEN ASM_REWRITE_TAC []], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"num_of_int(abs r)"))) THEN ASM_REWRITE_TAC [num_divides] THEN SIMP_TAC [INT_OF_NUM_OF_INT, INT_ABS_POS, INT_DIVIDES_LABS] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(r:int) divides &1") MP_TAC THENL [SUBGOAL_THEN (← q r"&1:int = z - ((if &0 <= (c:int) then &1 else -- &1) * &t * u) * &P") SUBST1_TAC THENL [EXPAND_TAC "z" THEN CONV_TAC INT_RING, ALL_TAC] THEN MATCH_MP_TAC INT_DIVIDES_SUB THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC INT_DIVIDES_LMUL THEN ASM_REWRITE_TAC [], REWRITE_TAC [INT_DIVIDES_ONE] THEN STRIP_TAC THEN UNDISCH_TAC (← q r"int_prime r") THEN ASM_REWRITE_TAC [INT_PRIME_NEG, INT_PRIME_1]])

  let NUMBER_FIELD_GALOIS_CONJUGATES_POLY ← prove
    r"!l:B ring a.
        number_field l /\
        galois_extension(subfield_generated l {ring_0 l},l) I /\
        a IN ring_carrier(ring_of_integers l) /\
        subring_generated l
          (a INSERT ring_carrier(subfield_generated l {ring_0 l})) = l
        ==> ?q. q IN ring_carrier(poly_ring integer_ring (:1)) /\
                poly_deg integer_ring q =
                extension_degree(subfield_generated l {ring_0 l},l) I /\
                !n. ring_of_int l (poly_eval integer_ring q n) =
                    ring_product l
                      (group_carrier
                        (galois_group(subfield_generated l {ring_0 l},l) I))
                      (\f. ring_sub l (ring_of_int l n) (f a))"
    (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"Q = subfield_generated l {ring_0(l:B ring)}") THEN ABBREV_TAC (← q r"G = group_carrier(galois_group(Q,l) (I:B->B))") THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN (← q r"finite_extension(Q,l) (I:B->B) /\ field Q /\
                ring_homomorphism(Q,l) (I:B->B)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "Q" THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, RING_HOMOMORPHISM_SUBFIELD_INCLUSION] THEN ASM_MESON_TAC [number_field], ALL_TAC] THEN SUBGOAL_THEN (← q r"(a:B) IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"a:B")] RING_OF_INTEGERS_INTEGER_MINIMAL_POLYNOMIAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"q:(1->num)->int") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"q:(1->num)->int") THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"poly_deg integer_ring (q:(1->num)->int) = extension_degree(Q,l) (I:B->B)") ASSUME_TAC THENL [ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"I:B->B"), (← q r"Q:B ring"), (← q r"l:B ring"), (← q r"a:B")] EXTENSION_DEGREE_SIMPLE) THEN ASM_REWRITE_TAC [IMAGE_I] THEN ANTS_TAC THENL [CONJ_TAC THENL [ASM_MESON_TAC [finite_extension, field_extension, FINITE_IMP_FIELD_EXTENSION], MP_TAC (← ISPECL [(← q r"I:B->B"), (← q r"Q:B ring"), (← q r"l:B ring")] FINITE_IMP_ALGEBRAIC_EXTENSION) THEN ASM_SIMP_TAC [algebraic_extension]], DISCH_THEN (SUBST1_TAC o SYM) THEN REFL_TAC], ALL_TAC] THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"FINITE(G:(B->B)->bool) /\ CARD G = extension_degree(Q,l) (I:B->B)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "G" THEN ASM_SIMP_TAC [FINITE_GALOIS_GROUP] THEN ASM_MESON_TAC [GALOIS_EXTENSION_EQ_CARD], ALL_TAC] THEN ABBREV_TAC (← q r"qq = (ring_of_int l:int->B) o (q:(1->num)->int)") THEN SUBGOAL_THEN (← q r"qq IN ring_carrier(poly_ring (l:B ring) (:1)) /\ monic l qq /\
    poly_deg l qq = poly_deg integer_ring (q:(1->num)->int)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "qq" THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"l:B ring"), (← q r"ring_of_int l:int->B"), (← q r"q:(1->num)->int")] MONIC_HOMOMORPHIC_IMAGE) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, FIELD_IMP_NONTRIVIAL_RING], SIMP_TAC [] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC)] THEN MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN EXISTS_TAC (← q r"integer_ring") THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x. poly_eval (l:B ring) qq x =
        poly_extend (integer_ring,l) (ring_of_int l) (\v:1. x)
                    (q:(1->num)->int)") ASSUME_TAC THENL [EXPAND_TAC "qq" THEN SIMP_TAC [poly_eval, POLY_EXTEND_EVALUATE, RING_HOMOMORPHISM_INTEGER_RING_OF_INT], ALL_TAC] THEN SUBGOAL_THEN (← q r"qq = ring_product (poly_ring (l:B ring) (:1)) G
          (\f. poly_sub l (poly_var l one) (poly_const l ((f:B->B) a)))") ASSUME_TAC THENL [MATCH_MP_TAC MONIC_POLY_EQ_ROOTS_PRODUCT THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN] THEN REPEAT CONJ_TAC THENL [ASM_MESON_TAC [], X_GEN_TAC (← q r"f:B->B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_homomorphism(l,l) (f:B->B)") ASSUME_TAC THENL [ASM_MESON_TAC [GALOIS_GROUP_RING_HOMOMORPHISM], ALL_TAC] THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"l:B ring"), (← q r"l:B ring"), (← q r"ring_of_int l:int->B"), (← q r"(:1)"), (← q r"\v:1. (a:B)"), (← q r"f:B->B"), (← q r"q:(1->num)->int")] POLY_EXTEND_HOMOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(f:B->B) o ring_of_int (l:B ring) = ring_of_int l /\
                    (f:B->B) o (\v:1. a) = (\v. f a)") (fun th => REWRITE_TAC [th]) THENL [REWRITE_TAC [FUN_EQ_THM, o_THM] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_RING_OF_INT], ALL_TAC] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_MESON_TAC [RING_HOMOMORPHISM_0], MAP_EVERY X_GEN_TAC [(← q r"f:B->B"), (← q r"g:B->B")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"I:B->B"), (← q r"f:B->B"), (← q r"g:B->B"), (← q r"Q:B ring"), (← q r"l:B ring"), (← q r"{a:B}")] GALOIS_GROUP_EQ_ON_GENERATORS) THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [IN_SING] THEN CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN REWRITE_TAC [SUBFIELD_GENERATED_EQ, IMAGE_I] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [REWRITE_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET], ALL_TAC] THEN FIRST_ASSUM ((fun th => tactic_of do pure (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [(← SYM th)])) o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_eq z1)) then (do let z6 ← (q r"l:B ring"); let z5 ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); liftExcept (rand z3)); pure (z5 == z6)) else pure false)))) THEN SUBGOAL_THEN (← q r"ring_carrier Q UNION {a:B} = a INSERT ring_carrier Q") SUBST1_TAC THENL [SET_TAC [], ALL_TAC] THEN REWRITE_TAC [SUBRING_SUBSET_SUBFIELD_GENERATED]], ALL_TAC] THEN X_GEN_TAC (← q r"n:int") THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"l:B ring"), (← q r"n:int"), (← q r"ring_of_int l:int->B"), (← q r"q:(1->num)->int")] POLY_EVAL_HOMOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, INTEGER_RING, IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"!f. f IN G ==> (f:B->B) a IN ring_carrier l") ASSUME_TAC THENL [X_GEN_TAC (← q r"f:B->B") THEN DISCH_TAC THEN MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN EXISTS_TAC (← q r"l:B ring") THEN ASM_MESON_TAC [GALOIS_GROUP_RING_HOMOMORPHISM], ALL_TAC] THEN wPart lhand (lhand o rand) POLY_EVAL_RING_PRODUCT THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_OF_INT] THEN X_GEN_TAC (← q r"f:B->B") THEN DISCH_TAC THEN MATCH_MP_TAC POLY_X_MINUS_A_IN_CARRIER THEN ASM_SIMP_TAC [], DISCH_THEN SUBST1_TAC] THEN MATCH_MP_TAC RING_PRODUCT_EQ THEN X_GEN_TAC (← q r"f:B->B") THEN DISCH_TAC THEN REWRITE_TAC [] THEN wPart lhand (lhand o rand) POLY_EVAL_SUB THEN ASM_SIMP_TAC [RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_CONST] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [POLY_EVAL_VAR, POLY_EVAL_CONST, RING_OF_INT])

  let NUMBER_FIELD_GALOIS_RATIONAL_TOTALLY_SPLIT ← prove
    r"!l:B ring p P.
        number_field l /\
        galois_extension(subfield_generated l {ring_0 l},l) I /\
        prime p /\ prime_ideal (ring_of_integers l) P /\ ring_of_num l p IN P
        ==> (totally_split (integer_ring,ring_of_integers l) (ring_of_int l)
              (ideal_generated integer_ring {&p}) <=>
             group_carrier
              (decomposition_group(subfield_generated l {ring_0 l},l) I P) =
             {I})"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"p:num")] SPLITTING_TYPES_PRIME_SUBFIELD) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o (SYM o (CONJUNCT1 o CONJUNCT2))) THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"p:num")] RING_OF_INTEGERS_PRIME_SUBFIELD_IDEAL) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"Q = subfield_generated l {ring_0(l:B ring)}") THEN ABBREV_TAC (← q r"p0 = ideal_generated (ring_of_integers Q) {ring_of_num (l:B ring) p}") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o (SPEC (← q r"P:B->bool"))))) THEN ANTS_TAC THENL [ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], ALL_TAC] THEN DISCH_THEN (fun z1 => tactic_of do pure (MP_TAC (← (do pure (Prod.snd (← (do pure (← EQ_IMP_RULE z1)))))))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"I:B->B"), (← q r"Q:B ring"), (← q r"l:B ring"), (← q r"p0:B->bool"), (← q r"P:B->bool")] NUMBER_FIELD_GALOIS_SPLITTING_TYPES) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN EXPAND_TAC "Q" THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, (← CONJUNCT2 SUBFIELD_GENERATED), RING_HOMOMORPHISM_SUBFIELD_INCLUSION], SIMP_TAC []])

  let NUMBER_FIELD_RATIONAL_PRIMES_CONTAINING_FINITE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ ~q ==> ~(p <=> q)")
    prove
      r"!l:B ring Y.
          number_field l /\ FINITE Y /\
          Y SUBSET ring_carrier(ring_of_integers l) /\ ~(ring_0 l IN Y)
          ==> FINITE {p | prime p /\
                          ?P y. prime_ideal (ring_of_integers l) P /\
                                ring_of_num l p IN P /\ y IN Y /\ y IN P}"
      (REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"IMAGE (\P. ring_char(quotient_ring (ring_of_integers l) P))
            (UNIONS {{P | prime_ideal (ring_of_integers l) P /\
                          ~(P = {ring_0(ring_of_integers l)}) /\
                          ideal_generated (ring_of_integers l) {y} SUBSET P} |
                     (y:B) IN Y})") THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC [FINITE_UNIONS] THEN ASM_SIMP_TAC [SIMPLE_IMAGE, FINITE_IMAGE, FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"ideal_generated (ring_of_integers l) {y:B}")] DEDEKIND_IDEAL_FACTORIZATION) THEN ANTS_TAC THENL [ALL_TAC, SIMP_TAC []] THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED] THEN DISCH_THEN (MP_TAC o (AP_TERM (← q r"(IN) (y:B)"))) THEN REWRITE_TAC [IN_SING, RING_OF_INTEGERS] THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN ASM SET_TAC [], ALL_TAC] THEN GEN_REWRITE_TAC id [SUBSET] THEN REWRITE_TAC [IN_ELIM_THM, IN_IMAGE, IN_UNIONS, EXISTS_IN_GSPEC] THEN X_GEN_TAC (← q r"p:num") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"P:B->bool") (X_CHOOSE_THEN (← q r"y:B") STRIP_ASSUME_TAC))) THEN EXISTS_TAC (← q r"P:B->bool") THEN CONJ_TAC THENL [CONV_TAC SYM_CONV THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"P:B->bool"), (← q r"p:num")] RING_OF_NUM_IN_PRIME_IDEAL) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], EXISTS_TAC (← q r"y:B") THEN ASM_REWRITE_TAC [IN_ELIM_THM, RING_OF_INTEGERS] THEN CONJ_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN ASM SET_TAC [], MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, SING_SUBSET]]])

  let NUMBER_FIELD_GALOIS_TOTALLY_SPLIT_INFINITE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_sub r (ring_sub r n x) (ring_sub r n y) = ring_sub r y (x:B)")
    let r2 ← TAUT (← q r"(~p ==> F) ==> p")
    let r3 ← SET_RULE (← q r"(a:B->B) IN s /\ (!x. x IN s ==> x = a) ==> s = {a}")
    let r20 ← SET_RULE (← q r"{(g:(B->B)->B) x | x | x IN s /\ P x} = IMAGE g {x | x IN s /\ P x}")
    let r27 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!l:B ring.
          number_field l /\
          galois_extension(subfield_generated l {ring_0 l},l) I
          ==> INFINITE {p | prime p /\
                            totally_split (integer_ring,ring_of_integers l)
                              (ring_of_int l) (ideal_generated integer_ring
                                {&p})}"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN ABBREV_TAC (← q r"Q = subfield_generated l {ring_0(l:B ring)}") THEN ABBREV_TAC (← q r"G = group_carrier(galois_group(Q,l) (I:B->B))") THEN SUBGOAL_THEN (← q r"field Q /\ ring_homomorphism(Q,l) (I:B->B) /\
                  finite_extension(Q,l) (I:B->B) /\ FINITE(G:(B->B)->bool)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "Q" THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, RING_HOMOMORPHISM_SUBFIELD_INCLUSION] THEN MATCH_MP_TAC r27 THEN CONJ_TAC THENL [ASM_MESON_TAC [number_field], EXPAND_TAC "G" THEN EXPAND_TAC "Q" THEN SIMP_TAC [FINITE_GALOIS_GROUP]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"Q:B ring"), (← q r"l:B ring"), (← q r"I:B->B")] NUMBER_FIELD_INTEGRAL_PRIMITIVE_ELEMENT) THEN ASM_REWRITE_TAC [IMAGE_I] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:B") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(a:B) IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"a:B")] NUMBER_FIELD_GALOIS_CONJUGATES_POLY) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"q:(1->num)->int") STRIP_ASSUME_TAC) THEN MP_TAC (← SPEC (← q r"q:(1->num)->int") INTEGER_POLY_PRIME_DIVISORS_INFINITE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN MP_TAC (← ISPEC (← q r"l:B ring") NUMBER_FIELD_DEGREE_POS) THEN ASM_REWRITE_TAC [] THEN ARITH_TAC, DISCH_TAC] THEN SUBGOAL_THEN (← q r"!f. f IN G ==> ring_homomorphism(l,l) (f:B->B) /\
                     (f a) IN ring_carrier(ring_of_integers l) /\
                     (!n. f(ring_of_int l n) = ring_of_int l n)") (LABEL_TAC "Gprops") THENL [X_GEN_TAC (← q r"f:B->B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_homomorphism(l,l) (f:B->B)") ASSUME_TAC THENL [ASM_MESON_TAC [GALOIS_GROUP_RING_HOMOMORPHISM], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"l:B ring"), (← q r"f:B->B")] RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN ASM_REWRITE_TAC [ring_homomorphism] THEN ASM SET_TAC [], ASM_MESON_TAC [RING_HOMOMORPHISM_RING_OF_INT]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!f. f IN G /\ (f:B->B) a = a ==> f = I") ASSUME_TAC THENL [X_GEN_TAC (← q r"f:B->B") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"I:B->B"), (← q r"f:B->B"), (← q r"I:B->B"), (← q r"Q:B ring"), (← q r"l:B ring"), (← q r"{a:B}")] GALOIS_GROUP_EQ_ON_GENERATORS) THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [IN_SING, I_THM, GALOIS_GROUP_I] THEN CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN REWRITE_TAC [SUBFIELD_GENERATED_EQ, IMAGE_I] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET] THEN FIRST_ASSUM ((fun th => tactic_of do pure (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [(← SYM th)])) o (checkM (fun th => (do if ← (do let z21 ← (do let z22 ← (pure th); pure (concl z22)); pure (is_eq z21)) then (do let z26 ← (q r"l:B ring"); let z25 ← (do let z23 ← (do let z24 ← (pure th); pure (concl z24)); liftExcept (rand z23)); pure (z25 == z26)) else pure false)))) THEN SUBGOAL_THEN (← q r"ring_carrier Q UNION {a:B} = a INSERT ring_carrier Q") SUBST1_TAC THENL [SET_TAC [], ALL_TAC] THEN REWRITE_TAC [SUBRING_SUBSET_SUBFIELD_GENERATED], ALL_TAC] THEN ABBREV_TAC (← q r"E = {p | prime p /\
               ?P y. prime_ideal (ring_of_integers l) P /\
                     ring_of_num l p IN P /\
                     y IN {ring_sub l ((f:B->B) a) a | f | f IN G /\ ~(f = I)} /\
                     y IN P}") THEN SUBGOAL_THEN (← q r"FINITE(E:num->bool)") ASSUME_TAC THENL [EXPAND_TAC "E" THEN MATCH_MP_TAC NUMBER_FIELD_RATIONAL_PRIMES_CONTAINING_FINITE THEN ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL [ONCE_REWRITE_TAC [r20] THEN MATCH_MP_TAC FINITE_IMAGE THEN ASM_SIMP_TAC [FINITE_RESTRICT], REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN X_GEN_TAC (← q r"f:B->B") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"(f:B->B) a"), (← q r"a:B")] RING_SUB) THEN ASM_SIMP_TAC [RING_OF_INTEGERS], REWRITE_TAC [IN_ELIM_THM, NOT_EXISTS_THM] THEN X_GEN_TAC (← q r"f:B->B") THEN STRIP_TAC THEN UNDISCH_TAC (← q r"~(f:B->B = I)") THEN REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"(f:B->B) a"), (← q r"a:B")] RING_SUB_EQ_0) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_IN_CARRIER] THEN ANTS_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ASM_MESON_TAC []]], ALL_TAC] THEN MATCH_MP_TAC INFINITE_SUPERSET THEN EXISTS_TAC (← q r"{p | prime p /\ ?n. &p divides poly_eval integer_ring q (&n)} DIFF E") THEN ASM_SIMP_TAC [INFINITE_DIFF_FINITE] THEN REWRITE_TAC [SUBSET, IN_DIFF, IN_ELIM_THM] THEN X_GEN_TAC (← q r"p:num") THEN DISCH_THEN (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC (← q r"n:num"))) ASSUME_TAC) THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"p:num")] NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q) THEN ASM_REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY), IN_ELIM_THM] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"P0:B->bool") STRIP_ASSUME_TAC) o (CONJUNCT1 o CONJUNCT2)) THEN SUBGOAL_THEN (← q r"!g. g IN G
          ==> ring_sub l (ring_of_int l (&n)) ((g:B->B) a) IN
              ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"ring_of_int l (&n):B"), (← q r"(g:B->B) a")] RING_SUB) THEN ASM_SIMP_TAC [RING_OF_INTEGERS, RING_OF_INT_IN_RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"?f. f IN G /\ ring_sub l (ring_of_int l (&n)) ((f:B->B) a) IN P0") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"P0:B->bool"), (← q r"G:(B->B)->bool"), (← q r"\f. ring_sub l (ring_of_int l (&n)) ((f:B->B) a)")] RING_PRODUCT_IN_PRIME_IDEAL) THEN ASM_SIMP_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN SUBGOAL_THEN (← q r"ring_product (ring_of_integers l) G
          (\f. ring_sub l (ring_of_int l (&n)) ((f:B->B) a)) =
        ring_product l G (\f. ring_sub l (ring_of_int l (&n)) (f a))") SUBST1_TAC THENL [GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [(← GSYM (← CONJUNCT2 RING_OF_INTEGERS_SUBRING))] THEN REWRITE_TAC [RING_PRODUCT_SUBRING_GENERATED_GEN, (← CONJUNCT2 RING_OF_INTEGERS_SUBRING)] THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN FIRST_X_ASSUM ((fun th => tactic_of do pure (REWRITE_TAC [(← GSYM th)])) o (checkM (fun th => (do if ← (do let z10 ← (do let z11 ← (pure th); pure (concl z11)); pure (is_forall z10)) then (do let z12 ← (do let z13 ← (pure th); pure (concl z13)); canM (fun z14 => (do let z15 ← (pure z14); find_termM (fun t => (do if ← (do let z16 ← (pure t); pure (is_const z16)) then (do let z19 ← (pure "poly_eval"); let z18 ← (do pure (Prod.fst (← (do let z17 ← (pure t); liftExcept (dest_const z17))))); pure (z18 == z19)) else pure false)) z15)) z12) else pure false)))) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"P0:B->bool"), (← q r"p:num")] RING_OF_INT_IN_PRIME_IDEAL) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN FIRST_ASSUM (MP_TAC o ((MATCH_MP GALOIS_GROUP_PERMUTES) o ((checkM (fun th => (do let z9 ← (q r"(f:B->B) IN group_carrier(galois_group(Q,l) I)"); let z8 ← (do let z7 ← (pure th); pure (concl z7)); pure (z8 == z9)))) o ((REWRITE_RULE [(← SYM (← ASSUME (← q r"group_carrier(galois_group(Q,l) (I:B->B)) = G")))]) o (checkM (fun th => (do let z6 ← (q r"(f:B->B) IN G"); let z5 ← (do let z4 ← (pure th); pure (concl z4)); pure (z5 == z6)))))))) THEN DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP PERMUTES_INVERSES)) THEN SUBGOAL_THEN (← q r"inverse(f:B->B) IN G") ASSUME_TAC THENL [EXPAND_TAC "G" THEN MATCH_MP_TAC GALOIS_GROUP_INVERSE THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"P = IMAGE (inverse(f:B->B)) P0") THEN SUBGOAL_THEN (← q r"prime_ideal (ring_of_integers l) P /\ ring_of_num l p IN P /\
      ring_sub l (ring_of_int l (&n)) (a:B) IN P") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"I:B->B"), (← q r"Q:B ring"), (← q r"l:B ring"), (← q r"ring_of_integers l:B ring"), (← q r"inverse(f:B->B)"), (← q r"P0:B->bool")] GALOIS_GROUP_PRIME_IDEAL_IMAGE) THEN ANTS_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_SUBRING, GALOIS_GROUP_RING_OF_INTEGERS] THEN ASM_SIMP_TAC [PRIME_IDEAL_IMP_SUBSET] THEN UNDISCH_TAC (← q r"inverse(f:B->B) IN G") THEN EXPAND_TAC "G" THEN SIMP_TAC [], ALL_TAC] THEN EXPAND_TAC "P" THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN USE_THEN "Gprops" (MP_TAC o (SPEC (← q r"inverse(f:B->B)"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, STRIP_TAC] THEN REWRITE_TAC [IN_IMAGE] THEN CONJ_TAC THENL [EXISTS_TAC (← q r"ring_of_num l p:B") THEN ASM_REWRITE_TAC [] THEN CONV_TAC SYM_CONV THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"l:B ring"), (← q r"inverse(f:B->B)")] RING_HOMOMORPHISM_RING_OF_NUM) THEN ASM_SIMP_TAC [], EXISTS_TAC (← q r"ring_sub l (ring_of_int l (&n)) ((f:B->B) a)") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(f:B->B) a IN ring_carrier l") ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"l:B ring") RING_OF_INTEGERS_SUBSET) THEN REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN USE_THEN "Gprops" (MP_TAC o (SPEC (← q r"f:B->B"))) THEN ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"l:B ring"), (← q r"inverse(f:B->B)")] RING_HOMOMORPHISM_SUB) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (SPECL [(← q r"ring_of_int l (&n):B"), (← q r"(f:B->B) a")])) THEN ASM_REWRITE_TAC [RING_OF_INT] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC []], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"p:num"), (← q r"P:B->bool")] NUMBER_FIELD_GALOIS_RATIONAL_TOTALLY_SPLIT) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC r3 THEN CONJ_TAC THENL [MP_TAC (← ISPEC (← q r"decomposition_group(Q,l) (I:B->B) P") GROUP_ID) THEN REWRITE_TAC [DECOMPOSITION_GROUP], ALL_TAC] THEN REWRITE_TAC [DECOMPOSITION_GROUP, IN_ELIM_THM] THEN X_GEN_TAC (← q r"g:B->B") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(g:B->B) IN G") ASSUME_TAC THENL [EXPAND_TAC "G" THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN MATCH_MP_TAC r2 THEN DISCH_TAC THEN UNDISCH_TAC (← q r"~((p:num) IN E)") THEN REWRITE_TAC [] THEN EXPAND_TAC "E" THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_REWRITE_TAC [] THEN MAP_EVERY EXISTS_TAC [(← q r"P:B->bool"), (← q r"ring_sub l ((g:B->B) a) a")] THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [REWRITE_TAC [IN_ELIM_THM] THEN EXISTS_TAC (← q r"g:B->B") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN USE_THEN "Gprops" (MP_TAC o (SPEC (← q r"g:B->B"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, STRIP_TAC] THEN SUBGOAL_THEN (← q r"(g:B->B) a IN ring_carrier l") ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"l:B ring") RING_OF_INTEGERS_SUBSET) THEN REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sub l (ring_of_int l (&n)) ((g:B->B) a) IN P") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"ring_sub l (ring_of_int l (&n)) ((g:B->B) a) =
        g (ring_sub l (ring_of_int l (&n)) a)") SUBST1_TAC THENL [MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"l:B ring"), (← q r"g:B->B")] RING_HOMOMORPHISM_SUB) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (SPECL [(← q r"ring_of_int l (&n):B"), (← q r"a:B")])) THEN ASM_REWRITE_TAC [RING_OF_INT] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REFL_TAC, UNDISCH_TAC (← q r"IMAGE (g:B->B) P = P") THEN DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [(← SYM th)])) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"P:B->bool"), (← q r"ring_sub l (ring_of_int l (&n)) (a:B)"), (← q r"ring_sub l (ring_of_int l (&n)) ((g:B->B) a)")] IN_RING_IDEAL_SUB) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC [RING_OF_INT])

  -- @@RETURN BEGIN
  return { INTEGER_POLY_CONGRUENCE, INTEGER_POLY_FIBRE_FINITE,
           INTEGER_POLY_PRIME_DIVISORS_INFINITE, NUMBER_FIELD_GALOIS_CONJUGATES_POLY,
           NUMBER_FIELD_GALOIS_RATIONAL_TOTALLY_SPLIT,
           NUMBER_FIELD_RATIONAL_PRIMES_CONTAINING_FINITE,
           NUMBER_FIELD_GALOIS_TOTALLY_SPLIT_INFINITE }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- split_primes.ml phrases from line 733 to 1055                          -/
/- ---------------------------------------------------------------------- -/

structure SplitPrimes02 where
  -- @@FIELDS
  NUMBER_FIELD_GALOIS_CLOSURE_Q : thm
  NUMBER_FIELD_GALOIS_CLOSURE : thm
  NUMBER_FIELD_TOTALLY_SPLIT_HOMOMORPHIC_PREIMAGE : thm
  NUMBER_FIELD_TOTALLY_SPLIT_INFINITE_Q : thm
  NUMBER_FIELD_TOTALLY_SPLIT_INFINITE : thm
  NUMBER_FIELD_DEGREE_ONE_PRIMES_INFINITE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupSplitPrimes02 [HolBase] (D : SplitPrimesDeps) (BSplitPrimes01 : SplitPrimes01) :
    ExceptT String IO SplitPrimes02 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, MESON_TAC, SELECT_CONV, SET_TAC, .. } := D
  let { ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH, DIVIDES_ZERO, EXTENSION_DEGREE_EQ_IMAGE,
        FIELD_EXTENSION_FROM_SUBFIELD_GENERATED, FIELD_EXTENSION_SUBFIELD_GENERATED,
        FIELD_IMP_NONTRIVIAL_RING, FIELD_RING_HOMOMORPHISM_MONOMORPHISM,
        FIELD_SUBFIELD_GENERATED, FINITE_EXTENSION_EQ_IMAGE,
        FINITE_EXTENSION_NORMAL_CLOSURE, FINITE_IMP_ALGEBRAIC_EXTENSION,
        FINITE_IMP_FIELD_EXTENSION, FORALL_IN_IMAGE, GALOIS_EXTENSION_EQ_CARD,
        GALOIS_EXTENSION_INTERMEDIATE, GALOIS_GROUP_EQ_IMAGE, IMAGE_I, IMP_CONJ_ALT,
        INFINITE_IMAGE, INFINITE_SUPERSET, IN_ELIM_THM, IN_SING, I_O_ID, I_THM,
        MEMBER_NOT_EMPTY, MONO_EXISTS, MULT_EQ_1, .. } := D.core1
  let { NUMBER_FIELD_HOMOMORPHIC_PREIMAGE, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_PRIME_IDEALS_ABOVE, NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q,
        NUMBER_FIELD_PRIME_SUBFIELD, NUMBER_FIELD_RAMIFICATION_INDEX_TOWER_Q,
        NUMBER_FIELD_RESIDUE_DEGREE_TOWER_Q, NUMBER_FIELD_TOWER_LAW,
        PERFECT_FIELD_CHAR_0, PERFECT_FIELD_IMP_SEPARABLE_EXTENSION, PRIME_0,
        PRIME_SUBFIELD_MONOMORPHIC_IMAGE, PRIME_SUBFIELD_SUBFIELD_GENERATED,
        PRIME_SUBFIELD_TOWER_LAW, RING_CHAR_SUBFIELD_GENERATED,
        RING_HOMOMORPHISM_COMPOSE, RING_HOMOMORPHISM_INTO_SUBRING,
        RING_HOMOMORPHISM_RING_OF_NUM, RING_HOMOMORPHISM_SUBFIELD_INCLUSION,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_OF_INTEGERS, RING_OF_NUM_EQ_0,
        RING_OF_NUM_IN_PRIME_IDEAL, SPLITTING_TYPES_INTEGER_RING,
        SUBRING_GENERATED_BY_SUBFIELD_GENERATED, SUBSET, algebraic_extension,
        field_extension, finite_extension, galois_extension, number_field,
        totally_split, .. } := D.core2
  let { NUMBER_FIELD_GALOIS_TOTALLY_SPLIT_INFINITE, .. } := BSplitPrimes01
  -- @@SCOPE END

  let NUMBER_FIELD_GALOIS_CLOSURE_Q ← prove
    r"!l:B ring.
        number_field l
        ==> ?(m:(B#num)ring) j.
                number_field m /\ ring_homomorphism(l,m) j /\
                galois_extension(subfield_generated m {ring_0 m},m) I"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN (← q r"ring_char(l:B ring) = 0") ASSUME_TAC THENL [ASM_MESON_TAC [number_field], ALL_TAC] THEN ABBREV_TAC (← q r"Q = subfield_generated l {ring_0(l:B ring)}") THEN SUBGOAL_THEN (← q r"field Q /\ ring_homomorphism(Q,l) (I:B->B) /\
    finite_extension(Q,l) (I:B->B) /\ number_field Q /\
    subfield_generated Q {ring_0 Q} = Q") STRIP_ASSUME_TAC THENL [EXPAND_TAC "Q" THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, NUMBER_FIELD_PRIME_SUBFIELD, PRIME_SUBFIELD_SUBFIELD_GENERATED] THEN ASM_MESON_TAC [number_field], ALL_TAC] THEN MP_TAC (← ISPEC (← q r"l:B ring") ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:(B#num)ring") (X_CHOOSE_THEN (← q r"f:B->B#num") STRIP_ASSUME_TAC)) THEN SUBGOAL_THEN (← q r"field(c:(B#num)ring) /\ ring_monomorphism(l,c) (f:B->B#num) /\
    ring_homomorphism(l,c) f") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [algebraic_extension, field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"I:B->B"), (← q r"f:B->B#num"), (← q r"Q:B ring"), (← q r"l:B ring"), (← q r"c:(B#num)ring")] FINITE_EXTENSION_NORMAL_CLOSURE) THEN ASM_REWRITE_TAC [I_O_ID] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"s:(B#num)->bool") STRIP_ASSUME_TAC) THEN ABBREV_TAC (← q r"N = subfield_generated c (IMAGE (f:B->B#num) (ring_carrier Q) UNION s)") THEN EXISTS_TAC (← q r"N:(B#num)ring") THEN EXISTS_TAC (← q r"f:B->B#num") THEN SUBGOAL_THEN (← q r"IMAGE (f:B->B#num) (ring_carrier l) SUBSET ring_carrier N") ASSUME_TAC THENL [FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"f:B->B#num")) o (checkM (fun th => (do if ← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); pure (is_forall z4)) then (do let z6 ← (do let z7 ← (pure th); pure (concl z7)); canM (fun z8 => (do let z9 ← (pure z8); find_termM (fun t => (do if ← (do let z10 ← (pure t); pure (is_const z10)) then (do let z13 ← (pure "SUBSET"); let z12 ← (do pure (Prod.fst (← (do let z11 ← (pure t); liftExcept (dest_const z11))))); pure (z12 == z13)) else pure false)) z9)) z6) else pure false))))) THEN ASM_REWRITE_TAC [I_THM], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_homomorphism(l,N) (f:B->B#num)") ASSUME_TAC THENL [EXPAND_TAC "N" THEN ONCE_REWRITE_TAC [(← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED)] THEN MATCH_MP_TAC RING_HOMOMORPHISM_INTO_SUBRING THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "N" THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"field(N:(B#num)ring) /\ ring_char N = 0") STRIP_ASSUME_TAC THENL [EXPAND_TAC "N" THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, RING_CHAR_SUBFIELD_GENERATED] THEN MP_TAC (← ISPECL [(← q r"f:B->B#num"), (← q r"l:B ring"), (← q r"c:(B#num)ring")] PRIME_SUBFIELD_TOWER_LAW) THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_homomorphism(Q,N) ((f:B->B#num) o I)") ASSUME_TAC THENL [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC (← q r"l:B ring") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"number_field(N:(B#num)ring)") ASSUME_TAC THENL [REWRITE_TAC [number_field] THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"(f:B->B#num) o I"), (← q r"Q:B ring"), (← q r"N:(B#num)ring")] PRIME_SUBFIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [I_O_ID] THEN DISCH_THEN (SUBST1_TAC o (CONJUNCT1 o CONJUNCT2)) THEN ASM_MESON_TAC [number_field], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ring_homomorphism(Q,N) (f:B->B#num)") ASSUME_TAC THENL [FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do let z3 ← (q r"ring_homomorphism(Q,N) ((f:B->B#num) o I)"); let z2 ← (do let z1 ← (pure th); pure (concl z1)); pure (z2 == z3))))) THEN REWRITE_TAC [I_O_ID], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_char(Q:B ring) = 0") ASSUME_TAC THENL [ASM_MESON_TAC [number_field], ALL_TAC] THEN SUBGOAL_THEN (← q r"galois_extension(Q,N) (f:B->B#num)") ASSUME_TAC THENL [REWRITE_TAC [galois_extension] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC PERFECT_FIELD_IMP_SEPARABLE_EXTENSION THEN ASM_SIMP_TAC [PERFECT_FIELD_CHAR_0, FINITE_IMP_ALGEBRAIC_EXTENSION], ALL_TAC] THEN SUBGOAL_THEN (← q r"IMAGE (f:B->B#num) (ring_carrier Q) =
    IMAGE I (ring_carrier(subfield_generated N {ring_0 N}))") ASSUME_TAC THENL [REWRITE_TAC [IMAGE_I] THEN MP_TAC (← ISPECL [(← q r"Q:B ring"), (← q r"N:(B#num)ring"), (← q r"f:B->B#num")] PRIME_SUBFIELD_MONOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN ASM_SIMP_TAC [FIELD_IMP_NONTRIVIAL_RING], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"I:(B#num)->(B#num)"), (← q r"subfield_generated N {ring_0(N:(B#num)ring)}"), (← q r"N:(B#num)ring")] GALOIS_EXTENSION_EQ_CARD) THEN ANTS_TAC THENL [ASM_MESON_TAC [number_field], DISCH_THEN SUBST1_TAC] THEN MP_TAC (← ISPECL [(← q r"f:B->B#num"), (← q r"Q:B ring"), (← q r"N:(B#num)ring")] GALOIS_EXTENSION_EQ_CARD) THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"f:B->B#num"), (← q r"I:(B#num)->(B#num)"), (← q r"Q:B ring"), (← q r"subfield_generated N {ring_0(N:(B#num)ring)}"), (← q r"N:(B#num)ring")] GALOIS_GROUP_EQ_IMAGE) THEN MP_TAC (← ISPECL [(← q r"f:B->B#num"), (← q r"I:(B#num)->(B#num)"), (← q r"Q:B ring"), (← q r"subfield_generated N {ring_0(N:(B#num)ring)}"), (← q r"N:(B#num)ring")] EXTENSION_DEGREE_EQ_IMAGE) THEN ASM_REWRITE_TAC [] THEN REPEAT (DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC [])

  let NUMBER_FIELD_GALOIS_CLOSURE ← prove
    r"!k:A ring l:B ring h.
        field k /\ number_field l /\ ring_homomorphism(k,l) h
        ==> ?(m:(B#num)ring) j.
                number_field m /\ ring_homomorphism(l,m) j /\
                galois_extension(k,m) (j o h)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP NUMBER_FIELD_GALOIS_CLOSURE_Q)) THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"m:(B#num)ring") THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"j:B->B#num") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"g = (j:B->B#num) o (h:A->B)") THEN SUBGOAL_THEN (← q r"ring_homomorphism(k:A ring,m:(B#num)ring) g") ASSUME_TAC THENL [EXPAND_TAC "g" THEN ASM_MESON_TAC [RING_HOMOMORPHISM_COMPOSE], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"m:(B#num)ring"), (← q r"g:A->B#num")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITE_IMP_FIELD_EXTENSION)) THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"g:A->B#num"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"m:(B#num)ring")] GALOIS_EXTENSION_INTERMEDIATE) THEN ASM_REWRITE_TAC [I_O_ID, FIELD_EXTENSION_SUBFIELD_GENERATED] THEN DISCH_THEN MATCH_MP_TAC THEN SUBGOAL_THEN (← q r"IMAGE (g:A->B#num) (ring_carrier(subfield_generated k {ring_0 k})) =
    IMAGE I (ring_carrier(subfield_generated m {ring_0 m}))") ASSUME_TAC THENL [REWRITE_TAC [IMAGE_I] THEN MATCH_MP_TAC PRIME_SUBFIELD_MONOMORPHIC_IMAGE THEN ASM_MESON_TAC [field_extension], ALL_TAC] THEN SUBGOAL_THEN (← q r"field_extension(subfield_generated k {ring_0 k},m:(B#num)ring)
      (g:A->B#num) /\
    finite_extension(subfield_generated m {ring_0 m},m:(B#num)ring) I") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_EXTENSION_FROM_SUBFIELD_GENERATED] THEN ASM_MESON_TAC [number_field], ALL_TAC] THEN SUBGOAL_THEN (← q r"finite_extension(subfield_generated k {ring_0 k},m:(B#num)ring)
      (g:A->B#num)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"g:A->B#num"), (← q r"I:B#num->B#num"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"subfield_generated m {ring_0 m:B#num}"), (← q r"m:(B#num)ring")] FINITE_EXTENSION_EQ_IMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC [finite_extension], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"g:A->B#num"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"m:(B#num)ring")] GALOIS_EXTENSION_EQ_CARD) THEN MP_TAC (← ISPECL [(← q r"I:B#num->B#num"), (← q r"subfield_generated m {ring_0 m:B#num}"), (← q r"m:(B#num)ring")] GALOIS_EXTENSION_EQ_CARD) THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"g:A->B#num"), (← q r"I:B#num->B#num"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"subfield_generated m {ring_0 m:B#num}"), (← q r"m:(B#num)ring")] GALOIS_GROUP_EQ_IMAGE) THEN MP_TAC (← ISPECL [(← q r"g:A->B#num"), (← q r"I:B#num->B#num"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"subfield_generated m {ring_0 m:B#num}"), (← q r"m:(B#num)ring")] EXTENSION_DEGREE_EQ_IMAGE) THEN ASM_REWRITE_TAC [] THEN REPEAT (DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC [])

  let NUMBER_FIELD_TOTALLY_SPLIT_HOMOMORPHIC_PREIMAGE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"1 = n <=> n = 1")
    prove
      r"!(j:B->C) l m p.
          field l /\ number_field m /\ ring_homomorphism(l,m) j /\ prime p /\
          totally_split (integer_ring,ring_of_integers m) (ring_of_int m)
            (ideal_generated integer_ring {&p})
          ==> totally_split (integer_ring,ring_of_integers l) (ring_of_int l)
                (ideal_generated integer_ring {&p})"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN UNDISCH_TAC (← q r"totally_split (integer_ring,ring_of_integers (m:C ring)) (ring_of_int m)
        (ideal_generated integer_ring {&p:int}) :bool") THEN ASM_SIMP_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers m:C ring") SPLITTING_TYPES_INTEGER_RING)), (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") SPLITTING_TYPES_INTEGER_RING))] THEN DISCH_TAC THEN X_GEN_TAC (← q r"P:B->bool") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"number_field(l:B ring)") ASSUME_TAC THENL [ASM_MESON_TAC [NUMBER_FIELD_HOMOMORPHIC_PREIMAGE], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(P = {ring_0(l:B ring)})") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"ring_of_num l p IN {ring_0(l:B ring)}") THEN REWRITE_TAC [IN_SING, RING_OF_NUM_EQ_0] THEN FIRST_ASSUM (MP_TAC o (CONJUNCT1 o ((GEN_REWRITE_RULE id [number_field]) o (checkM (fun th => (do let z4 ← (q r"number_field(l:B ring)"); let z3 ← (do let z2 ← (pure th); pure (concl z2)); pure (z3 == z4))))))) THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [DIVIDES_ZERO] THEN ASM_MESON_TAC [PRIME_0], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"m:C ring"), (← q r"j:B->C"), (← q r"P:B->bool")] NUMBER_FIELD_PRIME_IDEALS_ABOVE) THEN ASM_REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY), IN_ELIM_THM] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"P':C->bool") STRIP_ASSUME_TAC) o CONJUNCT2) THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"P':C->bool"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ring_of_num m p = (j:B->C)(ring_of_num l p)") SUBST1_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_RING_OF_NUM], ASM SET_TAC []], STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"m:C ring"), (← q r"j:B->C"), (← q r"P:B->bool"), (← q r"P':C->bool")] NUMBER_FIELD_RAMIFICATION_INDEX_TOWER_Q) THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"m:C ring"), (← q r"j:B->C"), (← q r"P:B->bool"), (← q r"P':C->bool")] NUMBER_FIELD_RESIDUE_DEGREE_TOWER_Q) THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [r1, MULT_EQ_1] THEN SIMP_TAC [])

  let NUMBER_FIELD_TOTALLY_SPLIT_INFINITE_Q ← prove
    r"!l:B ring.
        number_field l
        ==> INFINITE {p | prime p /\
                          totally_split (integer_ring,ring_of_integers l)
                            (ring_of_int l) (ideal_generated integer_ring
                              {&p})}"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"l:B ring") NUMBER_FIELD_GALOIS_CLOSURE_Q) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"m:(B#num)ring") (X_CHOOSE_THEN (← q r"j:B->B#num") STRIP_ASSUME_TAC)) THEN MP_TAC (← ISPEC (← q r"m:(B#num)ring") NUMBER_FIELD_GALOIS_TOTALLY_SPLIT_INFINITE) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] INFINITE_SUPERSET) THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC (← q r"p:num") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"j:B->B#num"), (← q r"l:B ring"), (← q r"m:(B#num)ring"), (← q r"p:num")] NUMBER_FIELD_TOTALLY_SPLIT_HOMOMORPHIC_PREIMAGE) THEN ASM_SIMP_TAC [NUMBER_FIELD_IMP_FIELD])

  let NUMBER_FIELD_TOTALLY_SPLIT_INFINITE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"1 = n <=> n = 1")
    prove
      r"!(h:A->B) k l.
          field k /\ number_field l /\ ring_homomorphism(k,l) h
          ==> INFINITE {p | prime_ideal (ring_of_integers k) p /\
                            ~(p = {ring_0 k}) /\
                            totally_split (ring_of_integers k,ring_of_integers l)
                              h p}"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"number_field(k:A ring)") ASSUME_TAC THENL [ASM_MESON_TAC [NUMBER_FIELD_HOMOMORPHIC_PREIMAGE], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_char(k:A ring) = 0") ASSUME_TAC THENL [ASM_MESON_TAC [number_field], ALL_TAC] THEN MP_TAC (← ISPEC (← q r"l:B ring") NUMBER_FIELD_TOTALLY_SPLIT_INFINITE_Q) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"S = {q | prime q /\
               totally_split (integer_ring,ring_of_integers (l:B ring))
                 (ring_of_int l) (ideal_generated integer_ring {&q})}") THEN DISCH_TAC THEN ABBREV_TAC (← q r"pp = \q. @p. prime_ideal (ring_of_integers k) p /\
                   ring_of_num (k:A ring) q IN p") THEN SUBGOAL_THEN (← q r"!q. q IN S
          ==> prime q /\
              totally_split (integer_ring,ring_of_integers (l:B ring))
                (ring_of_int l) (ideal_generated integer_ring {&q}) /\
              prime_ideal (ring_of_integers k) (pp q) /\
              ring_of_num (k:A ring) q IN pp q") ASSUME_TAC THENL [X_GEN_TAC (← q r"q:num") THEN EXPAND_TAC "S" THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "pp" THEN CONV_TAC SELECT_CONV THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"q:num")] NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q) THEN ASM_REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY), IN_ELIM_THM] THEN SIMP_TAC [], ALL_TAC] THEN MATCH_MP_TAC INFINITE_SUPERSET THEN EXISTS_TAC (← q r"IMAGE (pp:num->A->bool) S") THEN CONJ_TAC THENL [MATCH_MP_TAC INFINITE_IMAGE THEN ASM_REWRITE_TAC [] THEN MAP_EVERY X_GEN_TAC [(← q r"q1:num"), (← q r"q2:num")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"(pp:num->A->bool) q2")] RING_OF_NUM_IN_PRIME_IDEAL) THEN DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"q1:num") th) THEN MP_TAC (← SPEC (← q r"q2:num") th))) THEN ASM_SIMP_TAC [RING_OF_INTEGERS] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z15 ← (q r"(pp:num->A->bool) q1 = pp q2"); let z14 ← (do let z13 ← (pure th); pure (concl z13)); pure (z14 == z15)))))) THEN ASM_SIMP_TAC [] THEN MESON_TAC [], ALL_TAC] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN X_GEN_TAC (← q r"q:num") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"q:num")) o (checkM (fun z10 => (do let z11 ← (do let z12 ← (pure z10); pure (concl z12)); pure (is_forall z11)))))) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"p = (pp:num->A->bool) q") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); canM (fun z4 => (do let z5 ← (pure z4); find_termM (fun t => (do if ← (do let z6 ← (pure t); pure (is_const z6)) then (do let z9 ← (pure "totally_split"); let z8 ← (do pure (Prod.fst (← (do let z7 ← (pure t); liftExcept (dest_const z7))))); pure (z8 == z9)) else pure false)) z5)) z2)))) THEN ASM_SIMP_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") SPLITTING_TYPES_INTEGER_RING))] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"~(p = {ring_0(k:A ring)})") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"ring_of_num k q IN {ring_0(k:A ring)}") THEN ASM_REWRITE_TAC [IN_SING, RING_OF_NUM_EQ_0, DIVIDES_ZERO] THEN ASM_MESON_TAC [PRIME_0], ASM_REWRITE_TAC [totally_split]] THEN X_GEN_TAC (← q r"P:B->bool") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"P:B->bool"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ring_of_num l q = (h:A->B)(ring_of_num k q)") SUBST1_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_RING_OF_NUM], ASM SET_TAC []], STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"P:B->bool")] NUMBER_FIELD_RAMIFICATION_INDEX_TOWER_Q) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"P:B->bool")] NUMBER_FIELD_RESIDUE_DEGREE_TOWER_Q) THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [r1, MULT_EQ_1] THEN SIMP_TAC [])

  let NUMBER_FIELD_DEGREE_ONE_PRIMES_INFINITE ← prove
    r"!l:B ring.
        number_field l
        ==> INFINITE {P | prime_ideal (ring_of_integers l) P /\
                          ~(P = {ring_0 l}) /\
                          residue_degree (integer_ring,ring_of_integers l)
                            (ring_of_int l) P = 1}"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_char(l:B ring) = 0") ASSUME_TAC THENL [ASM_MESON_TAC [number_field], ALL_TAC] THEN MP_TAC (← ISPEC (← q r"l:B ring") NUMBER_FIELD_TOTALLY_SPLIT_INFINITE_Q) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"S = {q | prime q /\
             totally_split (integer_ring,ring_of_integers (l:B ring))
               (ring_of_int l) (ideal_generated integer_ring {&q})}") THEN DISCH_TAC THEN ABBREV_TAC (← q r"pp = \q. @P. prime_ideal (ring_of_integers l) P /\
                 ring_of_num (l:B ring) q IN P") THEN SUBGOAL_THEN (← q r"!q. q IN S
        ==> prime q /\
            (!P. prime_ideal (ring_of_integers l) P /\
                 ring_of_num l q IN P
                 ==> ramification_index (integer_ring,ring_of_integers l)
                       (ring_of_int l) P = 1 /\
                     residue_degree (integer_ring,ring_of_integers l)
                       (ring_of_int l) P = 1) /\
            prime_ideal (ring_of_integers l) (pp q) /\
            ring_of_num (l:B ring) q IN pp q") ASSUME_TAC THENL [X_GEN_TAC (← q r"q:num") THEN EXPAND_TAC "S" THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"totally_split (integer_ring,ring_of_integers (l:B ring))
        (ring_of_int l) (ideal_generated integer_ring {&q})") THEN ASM_SIMP_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") SPLITTING_TYPES_INTEGER_RING))] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN EXPAND_TAC "pp" THEN CONV_TAC SELECT_CONV THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"q:num")] NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q) THEN ASM_REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY), IN_ELIM_THM] THEN SIMP_TAC [], ALL_TAC] THEN MATCH_MP_TAC INFINITE_SUPERSET THEN EXISTS_TAC (← q r"IMAGE (pp:num->B->bool) S") THEN CONJ_TAC THENL [MATCH_MP_TAC INFINITE_IMAGE THEN ASM_REWRITE_TAC [] THEN MAP_EVERY X_GEN_TAC [(← q r"q1:num"), (← q r"q2:num")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"(pp:num->B->bool) q2")] RING_OF_NUM_IN_PRIME_IDEAL) THEN DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"q1:num") th) THEN MP_TAC (← SPEC (← q r"q2:num") th))) THEN ASM_SIMP_TAC [RING_OF_INTEGERS] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z6 ← (q r"(pp:num->B->bool) q1 = pp q2"); let z5 ← (do let z4 ← (pure th); pure (concl z4)); pure (z5 == z6)))))) THEN ASM_SIMP_TAC [] THEN MESON_TAC [], ALL_TAC] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN X_GEN_TAC (← q r"q:num") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"q:num")) o (checkM (fun z1 => (do let z2 ← (do let z3 ← (pure z1); pure (concl z3)); pure (is_forall z2)))))) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"P = (pp:num->B->bool) q") THEN STRIP_TAC THEN ASM_SIMP_TAC [] THEN DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"ring_of_num l q IN {ring_0(l:B ring)}") THEN ASM_REWRITE_TAC [IN_SING, RING_OF_NUM_EQ_0, DIVIDES_ZERO] THEN ASM_MESON_TAC [PRIME_0])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_GALOIS_CLOSURE_Q, NUMBER_FIELD_GALOIS_CLOSURE,
           NUMBER_FIELD_TOTALLY_SPLIT_HOMOMORPHIC_PREIMAGE,
           NUMBER_FIELD_TOTALLY_SPLIT_INFINITE_Q, NUMBER_FIELD_TOTALLY_SPLIT_INFINITE,
           NUMBER_FIELD_DEGREE_ONE_PRIMES_INFINITE }
  -- @@RETURN END

end HolANT.SplitPrimes
