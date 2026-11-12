/- ========================================================================= -/
/- ANT: The decomposition law in the quadratic subfield of the ...         -/
/- ========================================================================= -/
/- File: HolANT/CyclotomicQuadraticSplit.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/cyclotomic_quadratic_split.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antcyclotomicquadraticsplitdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/integer.ml, Library/isum.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/jacobi.ml, Library/frag.ml, Library/grouptheory.ml, Library/symmetric_group.ml, Library/galois.ml, ANT/ideal_arith.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/dedekind.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/prime_split.ml, ANT/norm_index.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/finite_field_trace.ml, ANT/ramification.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/classgroup.ml, ANT/relative_split.ml, ANT/relative_degree.ml, ANT/splitting_types.ml, ANT/quadratic.ml, ANT/nf_valuation.ml, ANT/integrality.ml, ANT/dedekind_kummer.ml, ANT/quadratic_split.ml, Library/modmul_group.ml, Library/cyclotomic.ml, Library/ring_groups.ml, Library/finite_fields.ml, ANT/cyclotomic_poly.ml, ANT/power_basis.ml, ANT/cyclotomic_field.ml, ANT/cyclotomic_galois.ml, ANT/decomposition.ml, ANT/nf_decomposition.ml, ANT/decomposition_field.ml, ANT/cyclotomic_frobenius.ml, ANT/cyclotomic_subfield_split.ml, ANT/cyclotomic_integers.ml, ANT/cyclotomic_subfields.ml, ANT/gauss_sum.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.CyclotomicQuadraticSplit fills them).

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
import HolLibrary.Integer
import HolLibrary.Isum
import HolLibrary.Products
import HolLibrary.Multiplicative
import HolLibrary.Primitive
import HolLibrary.Jacobi
import HolLibrary.Frag
import HolLibrary.GroupTheory
import HolLibrary.SymmetricGroup
import HolLibrary.Galois
import HolANT.IdealArith
import HolANT.Algmisc
import HolANT.Integral
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
import HolANT.TraceForm
import HolANT.FiniteFieldTrace
import HolANT.Ramification
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.Classgroup
import HolANT.RelativeSplit
import HolANT.RelativeDegree
import HolANT.SplittingTypes
import HolANT.Quadratic
import HolANT.NfValuation
import HolANT.Integrality
import HolANT.DedekindKummer
import HolANT.QuadraticSplit
import HolLibrary.ModmulGroup
import HolLibrary.Cyclotomic
import HolLibrary.RingGroups
import HolLibrary.FiniteFields
import HolANT.CyclotomicPoly
import HolANT.PowerBasis
import HolANT.CyclotomicField
import HolANT.CyclotomicGalois
import HolANT.Decomposition
import HolANT.NfDecomposition
import HolANT.DecompositionField
import HolANT.CyclotomicFrobenius
import HolANT.CyclotomicSubfieldSplit
import HolANT.CyclotomicIntegers
import HolANT.CyclotomicSubfields
import HolANT.GaussSum

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.IdealArith
open HolANT.Algmisc
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
open HolANT.SplittingTypes
open HolANT.Quadratic
open HolANT.NfValuation
open HolANT.Integrality
open HolANT.DedekindKummer
open HolANT.QuadraticSplit
open HolANT.CyclotomicPoly
open HolANT.PowerBasis
open HolANT.CyclotomicField
open HolANT.CyclotomicGalois
open HolANT.Decomposition
open HolANT.NfDecomposition
open HolANT.DecompositionField
open HolANT.CyclotomicFrobenius
open HolANT.CyclotomicSubfieldSplit
open HolANT.CyclotomicIntegers
open HolANT.CyclotomicSubfields
open HolANT.GaussSum

namespace HolANT.CyclotomicQuadraticSplit

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ARITH_EQ CARD_CLAUSES COPRIME_SYM CYCLOTOMIC_FIELD_GALOIS_GROUP_EXISTS
   CYCLOTOMIC_FIELD_QUADRATIC_SUBFIELD CYCLOTOMIC_SUBFIELD_SPLITTING_TYPES
   DEDEKIND_IMP_INTEGRAL_DOMAIN DEDEKIND_KRULL_DIMENSION_ONE
   DEDEKIND_RING_OF_INTEGERS DIVIDES_PRIME_PRIME DIVIDES_ZERO EQ_TRANS EXTENSION
   FIELD_IMP_INTEGRAL_DOMAIN FINITE_EMPTY FINITE_INSERT FORALL_UNWIND_THM2
   GALOIS_GROUP IDEAL_GENERATED_EQ_0 IDEAL_GENERATED_MINIMAL IDEAL_PROD_EQ_ZERO
   IDEAL_PROD_SUBSET_LEFT IDEAL_PROD_SUBSET_PRIME_IDEAL IDEAL_PROD_SUBSET_RIGHT
   IMP_CONJ INTEGRAL_DOMAIN_MUL_EQ_0 INTEGRAL_DOMAIN_SQUARE_EQ INT_ABS_MUL
   INT_ABS_NEG INT_ABS_NUM INT_ABS_POW INT_DIVIDES_LNEG INT_DIVIDES_RNEG
   INT_DIVIDES_ZERO INT_ENTIRE INT_MUL_ASSOC INT_MUL_LID INT_MUL_LNEG
   INT_NEG_EQ_0 INT_OF_NUM_EQ INT_POW INT_POW_EQ_0 INT_POW_ONE IN_ELIM_THM
   IN_IDEAL_GENERATED_SELF IN_INSERT IN_SING JACOBI_PRIME NOT_IN_EMPTY
   NUMBER_FIELD_IMP_FIELD NUMBER_FIELD_SPLITTING_TYPES_EXCLUSIVE
   NUMBER_FIELD_SUBFIELD_GENERATED NUMBER_FIELD_TOTALLY_SPLIT_CARD
   NUM_OF_INT_OF_NUM PRIME_1 PRIME_COPRIME_EQ PRIME_IMP_NZ PRIME_IMP_RING_IDEAL
   PRIME_IMP_SQUAREFREE PRIME_SUBFIELD_SUBFIELD_GENERATED
   QUADRATIC_FIELD_ODD_PRIME QUADRATIC_GAUSS_SUM
   QUADRATIC_GAUSS_SUM_HOMOMORPHISM RIGHT_FORALL_IMP_THM RING_1
   RING_HOMOMORPHISM_NEG RING_IDEAL_IMP_SUBSET RING_ISOMORPHISM_IMP_HOMOMORPHISM
   RING_MUL_LID RING_MUL_LNEG RING_MUL_RNEG RING_OF_INT RING_OF_INTEGERS
   RING_OF_INT_1 RING_OF_INT_EQ_0 RING_OF_INT_NEG RING_OF_INT_SUBFIELD_GENERATED
   RING_OF_NUM RING_OF_NUM_EQ_0 RING_POW_SUBFIELD_GENERATED RING_POW_ZERO
   RING_SUB_REFL RING_SUM SING_SUBSET SPLITTING_TYPES_INTEGER_RING
   SUBFIELD_GENERATED_INC num_divides number_field ring_automorphism : thm)
  deriving Inhabited

/-- What cyclotomic_quadratic_split.ml uses from Session besides theorems. -/
structure CyclotomicQuadraticSplitDeps where
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
/- cyclotomic_quadratic_split.ml phrases from line 68 to 257              -/
/- ---------------------------------------------------------------------- -/

structure CyclotomicQuadraticSplit where
  -- @@FIELDS
  QUADRATIC_FIELD_TOTALLY_SPLIT_ODD_PRIME : thm
  CYCLOTOMIC_QUADRATIC_SUBFIELD_TOTALLY_SPLIT : thm
  CYCLOTOMIC_QUADRATIC_SUBFIELD_DECOMPOSITION : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupCyclotomicQuadraticSplit [HolBase] (D : CyclotomicQuadraticSplitDeps) :
    ExceptT String IO CyclotomicQuadraticSplit := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, NUM_REDUCE_CONV, RING_RULE,
        SET_RULE, SET_TAC, .. } := D
  let { ARITH_EQ, CARD_CLAUSES, COPRIME_SYM, CYCLOTOMIC_FIELD_GALOIS_GROUP_EXISTS,
        CYCLOTOMIC_FIELD_QUADRATIC_SUBFIELD, CYCLOTOMIC_SUBFIELD_SPLITTING_TYPES,
        DEDEKIND_IMP_INTEGRAL_DOMAIN, DEDEKIND_KRULL_DIMENSION_ONE,
        DEDEKIND_RING_OF_INTEGERS, DIVIDES_PRIME_PRIME, DIVIDES_ZERO, EQ_TRANS,
        EXTENSION, FIELD_IMP_INTEGRAL_DOMAIN, FINITE_EMPTY, FINITE_INSERT,
        FORALL_UNWIND_THM2, GALOIS_GROUP, IDEAL_GENERATED_EQ_0,
        IDEAL_GENERATED_MINIMAL, IDEAL_PROD_EQ_ZERO, IDEAL_PROD_SUBSET_LEFT,
        IDEAL_PROD_SUBSET_PRIME_IDEAL, IDEAL_PROD_SUBSET_RIGHT, IMP_CONJ,
        INTEGRAL_DOMAIN_MUL_EQ_0, INTEGRAL_DOMAIN_SQUARE_EQ, INT_ABS_MUL, INT_ABS_NEG,
        INT_ABS_NUM, INT_ABS_POW, INT_DIVIDES_LNEG, INT_DIVIDES_RNEG, INT_DIVIDES_ZERO,
        INT_ENTIRE, INT_MUL_ASSOC, INT_MUL_LID, INT_MUL_LNEG, INT_NEG_EQ_0,
        INT_OF_NUM_EQ, INT_POW, INT_POW_EQ_0, INT_POW_ONE, IN_ELIM_THM,
        IN_IDEAL_GENERATED_SELF, IN_INSERT, IN_SING, JACOBI_PRIME, NOT_IN_EMPTY,
        NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_SPLITTING_TYPES_EXCLUSIVE,
        NUMBER_FIELD_SUBFIELD_GENERATED, NUMBER_FIELD_TOTALLY_SPLIT_CARD,
        NUM_OF_INT_OF_NUM, PRIME_1, PRIME_COPRIME_EQ, PRIME_IMP_NZ,
        PRIME_IMP_RING_IDEAL, PRIME_IMP_SQUAREFREE, PRIME_SUBFIELD_SUBFIELD_GENERATED,
        QUADRATIC_FIELD_ODD_PRIME, QUADRATIC_GAUSS_SUM,
        QUADRATIC_GAUSS_SUM_HOMOMORPHISM, RIGHT_FORALL_IMP_THM, RING_1,
        RING_HOMOMORPHISM_NEG, RING_IDEAL_IMP_SUBSET,
        RING_ISOMORPHISM_IMP_HOMOMORPHISM, RING_MUL_LID, RING_MUL_LNEG, RING_MUL_RNEG,
        RING_OF_INT, RING_OF_INTEGERS, RING_OF_INT_1, RING_OF_INT_EQ_0,
        RING_OF_INT_NEG, RING_OF_INT_SUBFIELD_GENERATED, RING_OF_NUM, RING_OF_NUM_EQ_0,
        RING_POW_SUBFIELD_GENERATED, RING_POW_ZERO, RING_SUB_REFL, RING_SUM,
        SING_SUBSET, SPLITTING_TYPES_INTEGER_RING, SUBFIELD_GENERATED_INC, num_divides,
        number_field, ring_automorphism, .. } := D.core1
  -- @@SCOPE END

  let QUADRATIC_FIELD_TOTALLY_SPLIT_ODD_PRIME ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!j:A->bool. x IN j /\ j SUBSET R ==> x IN R")
    let r28 ← ARITH_RULE (← q r"1 < 2")
    prove
      r"!k:A ring x d p.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
          x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
          squarefree(num_of_int(abs d)) /\ ~(d = &1) /\
          prime p /\ ~(p = 2) /\ ~(&p divides d)
          ==> (totally_split (integer_ring,ring_of_integers k) (ring_of_int k)
                 (ideal_generated integer_ring {&p}) <=>
               ?y. (y pow 2 == d) (mod &p))"
      (REPEAT STRIP_TAC THEN MP_TAC (← SPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"d:int"), (← q r"p:num")] QUADRATIC_FIELD_ODD_PRIME) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"?y. ((y:int) pow 2 == d) (mod &p)") THEN ASM_REWRITE_TAC [] THENL [ALL_TAC, MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"p:num")] NUMBER_FIELD_SPLITTING_TYPES_EXCLUSIVE) THEN ASM_REWRITE_TAC [r28] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:num")] SPLITTING_TYPES_INTEGER_RING) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MESON_TAC []] THEN SUBGOAL_THEN (← q r"?P Q. prime_ideal (ring_of_integers k) P /\
            prime_ideal (ring_of_integers k) Q /\ ~(P = Q) /\
            ideal_generated (ring_of_integers k) {ring_of_num k p} =
            ideal_prod (ring_of_integers k) P (Q:A->bool)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [NUMBER_FIELD_TOTALLY_SPLIT_CARD] THEN SUBGOAL_THEN (← q r"dedekind_domain(ring_of_integers k:A ring)") ASSUME_TAC THENL [ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"(ring_of_num k p:A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [MESON_TAC [RING_OF_NUM, RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(P = {ring_0 k:A}) /\ ~(Q = {ring_0 k:A})") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"Q:A->bool")] IDEAL_PROD_EQ_ZERO) THEN ASM_SIMP_TAC [DEDEKIND_IMP_INTEGRAL_DOMAIN, PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do if ← (do let z15 ← (do let z16 ← (pure th); pure (concl z16)); pure (is_eq z15)) then (do let z17 ← (do let z18 ← (do let z19 ← (pure th); pure (concl z19)); liftExcept (rand z18)); pure (is_comb z17)) else pure false) then (do let z20 ← (do let z21 ← (do let z22 ← (pure th); pure (concl z22)); liftExcept (rand z21)); canM (fun z23 => (do let z24 ← (pure z23); find_termM (fun z25 => (do let z27 ← (pure z25); let z26 ← (q r"P:A->bool"); pure (z26 == z27))) z24)) z20) else pure false))))) THEN ASM_SIMP_TAC [IDEAL_GENERATED_EQ_0, DEDEKIND_IMP_INTEGRAL_DOMAIN] THEN REWRITE_TAC [RING_OF_INTEGERS, RING_OF_NUM_EQ_0] THEN UNDISCH_TAC (← q r"number_field(k:A ring)") THEN SIMP_TAC [number_field, DIVIDES_ZERO] THEN ASM_MESON_TAC [PRIME_IMP_NZ], ALL_TAC] THEN SUBGOAL_THEN (← q r"{R | prime_ideal (ring_of_integers k) R /\ ring_of_num k p IN R} =
      {P,Q:A->bool}") SUBST1_TAC THENL [GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"R:A->bool") THEN REWRITE_TAC [IN_ELIM_THM, IN_INSERT, NOT_IN_EMPTY] THEN EQ_TAC THENL [STRIP_TAC THEN SUBGOAL_THEN (← q r"ideal_prod (ring_of_integers k) P Q SUBSET (R:A->bool)") MP_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); pure (is_eq z2)) then (do let z4 ← (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); liftExcept (rand z5)); pure (is_comb z4)) else pure false) then (do let z7 ← (do let z8 ← (do let z9 ← (pure th); pure (concl z9)); liftExcept (rand z8)); canM (fun z10 => (do let z11 ← (pure z10); find_termM (fun z12 => (do let z14 ← (pure z12); let z13 ← (q r"P:A->bool"); pure (z13 == z14))) z11)) z7) else pure false))))) THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_SIMP_TAC [SING_SUBSET, PRIME_IMP_RING_IDEAL], ALL_TAC] THEN ASM_SIMP_TAC [IDEAL_PROD_SUBSET_PRIME_IDEAL, PRIME_IMP_RING_IDEAL, RING_IDEAL_IMP_SUBSET] THEN STRIP_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"R:A->bool"), (← q r"P:A->bool")] DEDEKIND_KRULL_DIMENSION_ONE), MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"R:A->bool"), (← q r"Q:A->bool")] DEDEKIND_KRULL_DIMENSION_ONE)] THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN MESON_TAC [], ALL_TAC] THEN DISCH_THEN (DISJ_CASES_THEN SUBST_ALL_TAC) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r1 THEN EXISTS_TAC (← q r"ideal_generated (ring_of_integers k) {ring_of_num k p:A}") THEN ASM_SIMP_TAC [IN_IDEAL_GENERATED_SELF] THEN ASM_SIMP_TAC [IDEAL_PROD_SUBSET_LEFT, IDEAL_PROD_SUBSET_RIGHT, PRIME_IMP_RING_IDEAL, RING_IDEAL_IMP_SUBSET], ASM_SIMP_TAC [CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY, IN_INSERT, NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV])

  let CYCLOTOMIC_QUADRATIC_SUBFIELD_TOTALLY_SPLIT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!k:A ring y. y IN ring_carrier k
                     ==> ring_mul k (ring_of_num k 2) y =
                         ring_sub k y (ring_neg k y)")
    prove
      r"!(k:A ring) z p y q.
          number_field k /\ z IN ring_carrier k /\ ring_order k z = p /\
          prime p /\ ~(p = 2) /\ subfield_generated k {z} = k /\
          y IN ring_carrier k /\
          ring_pow k y 2 = ring_of_int k (--(&1) pow ((p - 1) DIV 2) * &p) /\
          prime q /\ ~(q = p)
          ==> (totally_split
                (integer_ring,ring_of_integers(subfield_generated k {y}))
                (ring_of_int(subfield_generated k {y}))
                (ideal_generated integer_ring {&q}) <=>
               ?x. (x EXP 2 == q) (mod p))"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN)) THEN SUBGOAL_THEN (← q r"ring_char(k:A ring) = 0") ASSUME_TAC THENL [ASM_MESON_TAC [number_field], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(q divides (p:num)) /\ coprime(q,p) /\ ~(p divides q)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [PRIME_COPRIME_EQ, COPRIME_SYM, DIVIDES_PRIME_PRIME], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"p:num"), (← q r"{y:A}"), (← q r"q:num")] CYCLOTOMIC_SUBFIELD_SPLITTING_TYPES) THEN ASM_REWRITE_TAC [IN_SING] THEN DISCH_THEN (SUBST1_TAC o CONJUNCT2) THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_UNWIND_THM2] THEN ABBREV_TAC (← q r"w = ring_sum (k:A ring) {a | a < p}
            (\a. ring_mul k (ring_of_int k (jacobi(a,p))) (ring_pow k z a))") THEN SUBGOAL_THEN (← q r"(w:A) IN ring_carrier k") ASSUME_TAC THENL [EXPAND_TAC "w" THEN REWRITE_TAC [RING_SUM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"p:num")] QUADRATIC_GAUSS_SUM) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"y = w \/ y = ring_neg k (w:A)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"y:A"), (← q r"w:A")] INTEGRAL_DOMAIN_SQUARE_EQ) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(y:A = ring_0 k)") ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC (← q r"ring_pow k (y:A) 2 = ring_of_int k (--(&1) pow ((p - 1) DIV 2) * &p)") THEN ASM_REWRITE_TAC [RING_POW_ZERO, ARITH_EQ] THEN DISCH_THEN (MP_TAC o SYM) THEN ASM_REWRITE_TAC [RING_OF_INT_EQ_0, INT_DIVIDES_ZERO] THEN REWRITE_TAC [INT_ENTIRE, INT_POW_EQ_0, INT_NEG_EQ_0, INT_OF_NUM_EQ, ARITH_EQ] THEN ASM_SIMP_TAC [PRIME_IMP_NZ], ALL_TAC] THEN SUBGOAL_THEN (← q r"!g. g IN group_carrier(galois_group
                               (subfield_generated k {ring_0 k},k) I) /\
          g z = ring_pow k z q
          ==> g y = ring_mul k (ring_of_int k (jacobi(q,p))) (y:A)") ASSUME_TAC THENL [X_GEN_TAC (← q r"g:A->A") THEN REWRITE_TAC [GALOIS_GROUP, IN_ELIM_THM] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_homomorphism (k,k) (g:A->A)") ASSUME_TAC THENL [ASM_MESON_TAC [ring_automorphism, RING_ISOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"g:A->A"), (← q r"z:A"), (← q r"p:num"), (← q r"q:num")] QUADRATIC_GAUSS_SUM_HOMOMORPHISM) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN FIRST_X_ASSUM ((DISJ_CASES_THEN SUBST1_TAC) o (checkM (fun z2 => (do let z3 ← (do let z4 ← (pure z2); pure (concl z4)); pure (is_disj z3))))) THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_NEG th)])) THEN ASM_SIMP_TAC [RING_MUL_RNEG, RING_OF_INT], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"p:num"), (← q r"q:num")] CYCLOTOMIC_FIELD_GALOIS_GROUP_EXISTS) THEN ANTS_TAC THENL [ASM_MESON_TAC [PRIME_IMP_NZ], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"g0:A->A") STRIP_ASSUME_TAC) THEN TRANS_TAC EQ_TRANS (← q r"ring_mul k (ring_of_int k (jacobi(q,p))) (y:A) = y") THEN CONJ_TAC THENL [EQ_TAC THENL [DISCH_THEN (MP_TAC o (SPEC (← q r"g0:A->A"))) THEN ASM_SIMP_TAC [], REPEAT STRIP_TAC THEN ASM_SIMP_TAC []], ALL_TAC] THEN MP_TAC (← SPECL [(← q r"q:num"), (← q r"p:num")] JACOBI_PRIME) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [RING_OF_INT_1, RING_MUL_LID] THEN REWRITE_TAC [RING_OF_INT_NEG, RING_OF_INT_1] THEN ASM_SIMP_TAC [RING_MUL_LNEG, RING_MUL_LID, RING_1] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_mul k (ring_of_num k 2) (y:A) = ring_0 k") MP_TAC THENL [TRANS_TAC EQ_TRANS (← q r"ring_sub k y (ring_neg k (y:A))") THEN CONJ_TAC THENL [MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC [], ASM_SIMP_TAC [RING_SUB_REFL]], ASM_SIMP_TAC [INTEGRAL_DOMAIN_MUL_EQ_0, RING_OF_NUM, RING_OF_NUM_EQ_0, DIVIDES_ZERO] THEN CONV_TAC NUM_REDUCE_CONV])

  let CYCLOTOMIC_QUADRATIC_SUBFIELD_DECOMPOSITION ← prove
    r"!(k:A ring) z p y q.
        number_field k /\ z IN ring_carrier k /\ ring_order k z = p /\
        prime p /\ ~(p = 2) /\ subfield_generated k {z} = k /\
        y IN ring_carrier k /\
        ring_pow k y 2 = ring_of_int k (--(&1) pow ((p - 1) DIV 2) * &p) /\
        prime q /\ ~(q = 2) /\ ~(q = p)
        ==> (totally_split
              (integer_ring,ring_of_integers(subfield_generated k {y}))
              (ring_of_int(subfield_generated k {y}))
              (ideal_generated integer_ring {&q}) <=>
             ?x. (x EXP 2 == q) (mod p)) /\
            (totally_split
              (integer_ring,ring_of_integers(subfield_generated k {y}))
              (ring_of_int(subfield_generated k {y}))
              (ideal_generated integer_ring {&q}) <=>
             ?x:int. (x pow 2 == --(&1) pow ((p - 1) DIV 2) * &p) (mod &q))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL [MATCH_MP_TAC CYCLOTOMIC_QUADRATIC_SUBFIELD_TOTALLY_SPLIT THEN EXISTS_TAC (← q r"z:A") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {y:A}"), (← q r"y:A"), (← q r"--(&1) pow ((p - 1) DIV 2) * &p:int"), (← q r"q:num")] QUADRATIC_FIELD_TOTALLY_SPLIT_ODD_PRIME) THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_SUBFIELD_GENERATED, PRIME_SUBFIELD_SUBFIELD_GENERATED, RING_POW_SUBFIELD_GENERATED, RING_OF_INT_SUBFIELD_GENERATED] THEN REPEAT CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"p:num"), (← q r"y:A")] CYCLOTOMIC_FIELD_QUADRATIC_SUBFIELD) THEN ASM_SIMP_TAC [], MATCH_MP_TAC SUBFIELD_GENERATED_INC THEN ASM SET_TAC [], REWRITE_TAC [INT_ABS_MUL, INT_ABS_POW, INT_ABS_NEG, INT_ABS_NUM, INT_POW_ONE, INT_MUL_LID, NUM_OF_INT_OF_NUM] THEN ASM_SIMP_TAC [PRIME_IMP_SQUAREFREE], DISCH_THEN (MP_TAC o (AP_TERM (← q r"abs:int->int"))) THEN REWRITE_TAC [INT_ABS_MUL, INT_ABS_POW, INT_ABS_NEG, INT_ABS_NUM, INT_POW_ONE, INT_MUL_LID, INT_OF_NUM_EQ] THEN ASM_MESON_TAC [PRIME_1], DISCH_TAC THEN SUBGOAL_THEN (← q r"(q:num) divides p") MP_TAC THENL [REWRITE_TAC [num_divides] THEN UNDISCH_TAC (← q r"&q divides --(&1) pow ((p - 1) DIV 2) * &p") THEN SPEC_TAC ((← q r"(p - 1) DIV 2"), (← q r"n:num")) THEN INDUCT_TAC THEN REWRITE_TAC [INT_POW, INT_MUL_LID] THEN REWRITE_TAC [(← GSYM INT_MUL_ASSOC), INT_MUL_LNEG, INT_MUL_LID] THEN REWRITE_TAC [INT_DIVIDES_LNEG, INT_DIVIDES_RNEG] THEN ASM_REWRITE_TAC [], ASM_MESON_TAC [DIVIDES_PRIME_PRIME]]])

  -- @@RETURN BEGIN
  return { QUADRATIC_FIELD_TOTALLY_SPLIT_ODD_PRIME,
           CYCLOTOMIC_QUADRATIC_SUBFIELD_TOTALLY_SPLIT,
           CYCLOTOMIC_QUADRATIC_SUBFIELD_DECOMPOSITION }
  -- @@RETURN END

end HolANT.CyclotomicQuadraticSplit
