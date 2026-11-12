/- ========================================================================= -/
/- ANT: The Stickelberger theorem                                          -/
/- ========================================================================= -/
/- File: HolANT/Stickelberger.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/stickelberger.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antstickelbergerdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/products.ml, ANT/algmisc.ml, Library/isum.ml, ANT/integral.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/discriminant.ml, Library/frag.ml, Library/grouptheory.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/classgroup.ml, ANT/nf_valuation.ml, ANT/prime_split.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/integrality.ml, Library/ring_groups.ml, ANT/fingen_group.ml, Multivariate/misc.ml, Multivariate/metric.ml, Multivariate/homology.ml, Multivariate/vectors.ml, Multivariate/determinants.ml, Multivariate/topology.ml, Multivariate/convex.ml, Multivariate/paths.ml, Multivariate/polytope.ml, Multivariate/degree.ml, Multivariate/derivatives.ml, Multivariate/integration.ml, Multivariate/measure.ml, Multivariate/complex_algebra.ml, Multivariate/complexes.ml, Multivariate/canal.ml, Multivariate/transcendentals.ml, Multivariate/realanalysis.ml, Multivariate/moretop.ml, Multivariate/cauchy.ml, Multivariate/complex_ring.ml, Multivariate/complex_field.ml, ANT/complex_embeddings.ml, ANT/power_basis.ml, ANT/infinite_places.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.Stickelberger fills them).

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
import HolLibrary.Frag
import HolLibrary.GroupTheory
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.Classgroup
import HolANT.NfValuation
import HolANT.PrimeSplit
import HolANT.TraceForm
import HolANT.RelativeSplit
import HolANT.Integrality
import HolLibrary.RingGroups
import HolANT.FingenGroup
import HolMultiLib.Misc
import HolMultiLib.Metric
import HolMultiLib.Homology
import HolMultiLib.Vectors
import HolMultiLib.Determinants
import HolMultiLib.Topology
import HolMultiLib.Convex
import HolMultiLib.Paths
import HolMultiLib.Polytope
import HolMultiLib.Degree
import HolMultiLib.Derivatives
import HolMultiLib.Integration
import HolMultiLib.Measure
import HolMultiLib.ComplexAlgebra
import HolMultiLib.Complexes
import HolMultiLib.Canal
import HolMultiLib.Transcendentals
import HolMultiLib.RealAnalysis
import HolMultiLib.MoreTop
import HolMultiLib.Cauchy
import HolMultiLib.ComplexRing
import HolMultiLib.ComplexField
import HolANT.ComplexEmbeddings
import HolANT.PowerBasis
import HolANT.InfinitePlaces

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
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.Classgroup
open HolANT.NfValuation
open HolANT.PrimeSplit
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.Integrality
open HolANT.FingenGroup
open HolANT.ComplexEmbeddings
open HolANT.PowerBasis
open HolANT.InfinitePlaces

namespace HolANT.Stickelberger

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ARITH_EQ COMPLEX_EMBEDDINGS_HAS_SIZE COMPLEX_EMBEDDINGS_NONEMPTY
   COMPLEX_RING_CLAUSES COMPLEX_RING_OF_INT COMPLEX_RING_POW
   COMPLEX_RING_PRODUCT EXISTS_UNIQUE_THM EXTENSION FIELD_COMPLEX_RING
   FINITE_COMPLEX_EMBEDDINGS FINITE_IMAGE FINITE_IMAGE_INJ_EQ FINITE_NUMSEG_LT
   FINITE_PERMUTATIONS FINITE_SUBSET FUN_EQ_THM HAS_SIZE_INDEX INT_DIVISION_SIMP
   INT_OF_NUM_EQ INT_REM_2_CASES IN_ELIM_THM IN_IMAGE IN_INTER IN_SUBFIELD_LINV
   IN_SUBFIELD_MUL IN_SUBRING_0 IN_SUBRING_1 IN_SUBRING_INT IN_SUBRING_MUL
   IN_SUBRING_NEG IN_SUBRING_POW IN_SUBRING_PRODUCT IN_SUBRING_SUM IN_UNIV
   MEMBER_NOT_EMPTY NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS
   NUMBER_FIELD_NORM_COMPLEX_EMBEDDINGS NUMBER_FIELD_NORM_INTEGRAL_Q
   PERMUTES_IN_IMAGE PRIME_SUBRING RING_0 RING_1 RING_ADD_LZERO RING_ADD_RZERO
   RING_CHAR_COMPLEX_RING RING_HOMOMORPHISM_IN_CARRIER
   RING_HOMOMORPHISM_RING_OF_INT RING_HOMOMORPHISM_RING_OF_INTEGERS
   RING_HOMOMORPHISM_SUM RING_INV RING_MUL_LID RING_MUL_LNEG RING_OF_INT
   RING_OF_INTEGERS_FREE RING_OF_INTEGERS_PRIME_SUBFIELD
   RING_OF_INTEGERS_SUBRING RING_OF_INTEGERS_SUBSET RING_OF_INT_CLAUSES
   RING_OF_INT_EQ_0 RING_OF_INT_EQ_CHAR_0 RING_PRODUCT RING_PRODUCT_EQ
   RING_PRODUCT_IMAGE RING_SUB_LZERO RING_SUB_RZERO RING_SUM RING_SUM_ADD
   RING_SUM_EQ RING_SUM_PERMUTATIONS_RYSER RING_SUM_SUB SUBFIELD_IMP_SUBRING_OF
   SUBFIELD_SUBFIELD_GENERATED SUBSET complex_embeddings free_basis
   int_congruent lemma o_DEF ring_det ring_sign : thm)
  deriving Inhabited

/-- What stickelberger.ml uses from Session besides theorems. -/
structure StickelbergerDeps where
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
/- stickelberger.ml phrases from line 54 to 264                           -/
/- ---------------------------------------------------------------------- -/

structure Stickelberger where
  -- @@FIELDS
  RING_DET_PERMANENT_MOD_4 : thm
  NUMBER_FIELD_PERMANENT_INTEGRAL : thm
  NUMBER_FIELD_DISCRIMINANT_MOD_4 : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupStickelberger [HolBase] (D : StickelbergerDeps) :
    ExceptT String IO Stickelberger := do
  -- @@SCOPE BEGIN
  let { ASM_INT_ARITH_TAC, ASM_MESON_TAC, INTEGER_RULE, INTEGER_TAC, MESON_TAC,
        RING_RULE, SET_RULE, SET_TAC, .. } := D
  let { ARITH_EQ, COMPLEX_EMBEDDINGS_HAS_SIZE, COMPLEX_EMBEDDINGS_NONEMPTY,
        COMPLEX_RING_CLAUSES, COMPLEX_RING_OF_INT, COMPLEX_RING_POW,
        COMPLEX_RING_PRODUCT, EXISTS_UNIQUE_THM, EXTENSION, FIELD_COMPLEX_RING,
        FINITE_COMPLEX_EMBEDDINGS, FINITE_IMAGE, FINITE_IMAGE_INJ_EQ, FINITE_NUMSEG_LT,
        FINITE_PERMUTATIONS, FINITE_SUBSET, FUN_EQ_THM, HAS_SIZE_INDEX,
        INT_DIVISION_SIMP, INT_OF_NUM_EQ, INT_REM_2_CASES, IN_ELIM_THM, IN_IMAGE,
        IN_INTER, IN_SUBFIELD_LINV, IN_SUBFIELD_MUL, IN_SUBRING_0, IN_SUBRING_1,
        IN_SUBRING_INT, IN_SUBRING_MUL, IN_SUBRING_NEG, IN_SUBRING_POW,
        IN_SUBRING_PRODUCT, IN_SUBRING_SUM, IN_UNIV, MEMBER_NOT_EMPTY,
        NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS, NUMBER_FIELD_NORM_COMPLEX_EMBEDDINGS,
        NUMBER_FIELD_NORM_INTEGRAL_Q, PERMUTES_IN_IMAGE, PRIME_SUBRING, RING_0, RING_1,
        RING_ADD_LZERO, RING_ADD_RZERO, RING_CHAR_COMPLEX_RING,
        RING_HOMOMORPHISM_IN_CARRIER, RING_HOMOMORPHISM_RING_OF_INT,
        RING_HOMOMORPHISM_RING_OF_INTEGERS, RING_HOMOMORPHISM_SUM, RING_INV,
        RING_MUL_LID, RING_MUL_LNEG, RING_OF_INT, RING_OF_INTEGERS_FREE,
        RING_OF_INTEGERS_PRIME_SUBFIELD, RING_OF_INTEGERS_SUBRING,
        RING_OF_INTEGERS_SUBSET, RING_OF_INT_CLAUSES, RING_OF_INT_EQ_0,
        RING_OF_INT_EQ_CHAR_0, RING_PRODUCT, RING_PRODUCT_EQ, RING_PRODUCT_IMAGE,
        RING_SUB_LZERO, RING_SUB_RZERO, RING_SUM, RING_SUM_ADD, RING_SUM_EQ,
        RING_SUM_PERMUTATIONS_RYSER, RING_SUM_SUB, SUBFIELD_IMP_SUBRING_OF,
        SUBFIELD_SUBFIELD_GENERATED, SUBSET, complex_embeddings, free_basis,
        int_congruent, o_DEF, ring_det, ring_sign, .. } := D.core1
  -- @@SCOPE END

  let RING_DET_PERMANENT_MOD_4 ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q2 ← q r"ring_mul k (ring_of_int k c) z = ring_1 k:A"
    let q8 ← q r"x = ring_mul k z (ring_of_int k b):A"
    let q9 ← q r"z:A"
    let q10 ← q r"ring_inv k (ring_of_int k c):A"
    let q11 ← q r"ring_of_int k c:A"
    let q12 ← q r"k:A ring"
    let v13 ← ISPECL [q12, q11] RING_INV
    let q14 ← q r"!x:int. &0 divides x <=> x = &0"
    let r15 ← INTEGER_RULE q14
    let q16 ← q r"ring_of_int k c:A"
    let q17 ← q r"u:A->bool"
    let q18 ← q r"k:A ring"
    let v19 ← ISPECL [q18, q17, q16] IN_SUBFIELD_LINV
    let q20 ← q r"u:A->bool"
    let q21 ← q r"ring_carrier(subfield_generated k {ring_0 k:A})"
    let q22 ← q r"{ring_0 k:A}"
    let q23 ← q r"k:A ring"
    let v24 ← ISPECL [q23, q22] SUBFIELD_SUBFIELD_GENERATED
    let q25 ← q r"k:A ring"
    let v26 ← ISPEC q25 RING_OF_INTEGERS_PRIME_SUBFIELD
    let p27 ← prove r"!k x:A b c.
        field k /\ ring_char k = 0 /\
        x IN ring_carrier(ring_of_integers k) /\ ~(c = &0) /\
        ring_mul k (ring_of_int k c) x = ring_of_int k b
        ==> ?m. x = ring_of_int k m" (REPEAT STRIP_TAC THEN MP_TAC v26 THEN ASM_REWRITE_TAC [EXTENSION, IN_INTER, IN_ELIM_THM, IN_UNIV] THEN DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM th)])) THEN ASM_REWRITE_TAC [] THEN MP_TAC v24 THEN ASM_REWRITE_TAC [] THEN SPEC_TAC (q21, q20) THEN REPEAT STRIP_TAC THEN MP_TAC v19 THEN ASM_SIMP_TAC [IN_SUBRING_INT, SUBFIELD_IMP_SUBRING_OF, RING_OF_INT_EQ_0, r15] THEN MP_TAC v13 THEN REWRITE_TAC [RING_OF_INT] THEN SPEC_TAC (q10, q9) THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN q8 SUBST1_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun z3 => (do let z7 ← (do let z4 ← (do let z5 ← (pure z3); pure (concl z5)); liftExcept (rand z4)); let z6 ← (q r"ring_of_int k b:A"); pure (z6 == z7)))))) THEN UNDISCH_TAC q2 THEN W (fun z1 => tactic_of do pure (MP_TAC (← RING_RULE (← (do pure (Prod.snd (← (pure z1)))))))) THEN ANTS_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], REWRITE_TAC []], MATCH_MP_TAC IN_SUBFIELD_MUL THEN ASM_SIMP_TAC [IN_SUBRING_INT, SUBFIELD_IMP_SUBRING_OF]])
    let lemma := p27
    let q28 ← q r"--c:int"
    let q29 ← q r"ring_mul k (ring_of_int k (&4)) (ring_mul k x y) =
    ring_of_int k (a pow 2 - d):A"
    let q30 ← q r"c:int"
    let q31 ← q r"&4:int"
    let q32 ← q r"a pow 2 - d:int"
    let q33 ← q r"ring_mul k x y:A"
    let q34 ← q r"k:A ring"
    let v35 ← ISPECL [q34, q33, q32, q31] lemma
    let q37 ← q r"ring_sub k (x:A) y = ring_det k s (f:K->K->A)"
    let v38 ← ASSUME q37
    let v39 ← GSYM v38
    let q40 ← q r"ring_pow k (ring_det k s (f:K->K->A)) 2 =
                             ring_of_int k d"
    let v41 ← ASSUME q40
    let v42 ← GSYM v41
    let q43 ← q r"ring_add k (x:A) y = ring_of_int k a"
    let v44 ← ASSUME q43
    let v45 ← GSYM v44
    let v46 ← GSYM RING_OF_INT_CLAUSES
    let q47 ← q r"ring_mul k (ring_of_int k (&4)) (ring_mul k x y) =
    ring_of_int k (a pow 2 - d):A"
    let q48 ← q r"(x:A) IN ring_carrier k /\ y IN ring_carrier k"
    let q49 ← q r"ring_sum k {p | p permutes s}
        (\p. ring_product k s (\i. (f:K->K->A) i (p i))) =
      ring_of_int k a"
    let q50 ← q r"ring_add k (x:A) y = ring_of_int k a /\
    ring_sub k x y = ring_det k s (f:K->K->A)"
    let q51 ← q r"p:K->K"
    let q52 ← q r"ring_mul k (x:A) y IN ring_carrier(ring_of_integers k)"
    let q53 ← q r"y = ring_sum k {p | p permutes s}
          (\p. if evenperm p then ring_0 k
               else ring_product k s (\i. (f:K->K->A) i (p i)))"
    let q54 ← q r"x = ring_sum k {p | p permutes s}
          (\p. if evenperm p then ring_product k s (\i. (f:K->K->A) i (p i))
               else ring_0 k)"
    prove
      r"!k s (f:K->K->A) a d.
          field k /\ ring_char k = 0 /\ FINITE s /\
          (!i j. i IN s /\ j IN s
                 ==> f i j IN ring_carrier(ring_of_integers k)) /\
          ring_sum k {p | p permutes s} (\p. ring_product k s (\i. f i (p i))) =
          ring_of_int k a /\
          ring_pow k (ring_det k s f) 2 = ring_of_int k d
          ==> (d == a pow 2) (mod &4)"
      (REPEAT STRIP_TAC THEN ABBREV_TAC q54 THEN ABBREV_TAC q53 THEN SUBGOAL_THEN q52 ASSUME_TAC THENL [MATCH_MP_TAC IN_SUBRING_MUL THEN REWRITE_TAC [RING_OF_INTEGERS_SUBRING] THEN MAP_EVERY EXPAND_TAC ["x", "y"] THEN CONJ_TAC THEN MATCH_MP_TAC IN_SUBRING_SUM THEN REWRITE_TAC [RING_OF_INTEGERS_SUBRING] THEN X_GEN_TAC q51 THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN COND_CASES_TAC THEN SIMP_TAC [RING_OF_INTEGERS_SUBRING, IN_SUBRING_0] THEN MATCH_MP_TAC IN_SUBRING_PRODUCT THEN REWRITE_TAC [RING_OF_INTEGERS_SUBRING] THEN ASM_MESON_TAC [PERMUTES_IN_IMAGE], ALL_TAC] THEN SUBGOAL_THEN q50 STRIP_ASSUME_TAC THENL [UNDISCH_TAC q49 THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MAP_EVERY EXPAND_TAC ["x", "y"] THEN REWRITE_TAC [ring_det] THEN CONJ_TAC THENL [wPart lhand (rand o rand) RING_SUM_ADD, wPart lhand (rand o rand) RING_SUM_SUB] THEN (ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_PERMUTATIONS] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [RING_PRODUCT, RING_0], DISCH_THEN (SUBST1_TAC o SYM)]) THEN MATCH_MP_TAC RING_SUM_EQ THEN GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [ring_sign] THEN COND_CASES_TAC THEN SIMP_TAC [RING_ADD_LZERO, RING_ADD_RZERO, RING_SUB_RZERO, RING_SUB_LZERO, RING_MUL_LID, RING_MUL_LNEG, RING_PRODUCT, RING_1], ALL_TAC] THEN SUBGOAL_THEN q48 STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["x", "y"] THEN REWRITE_TAC [RING_SUM], ALL_TAC] THEN SUBGOAL_THEN q47 ASSUME_TAC THENL [REWRITE_TAC [v46] THEN REWRITE_TAC [v45, v42] THEN REWRITE_TAC [v39] THEN W (fun z36 => tactic_of do pure (MP_TAC (← RING_RULE (← (do pure (Prod.snd (← (pure z36)))))))) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC v35 THEN ASM_REWRITE_TAC [INT_OF_NUM_EQ, ARITH_EQ] THEN DISCH_THEN (X_CHOOSE_TAC q30) THEN UNDISCH_TAC q29 THEN ASM_SIMP_TAC [RING_OF_INT_CLAUSES, RING_OF_INT_EQ_CHAR_0] THEN DISCH_TAC THEN REWRITE_TAC [int_congruent] THEN EXISTS_TAC q28 THEN ASM_INT_ARITH_TAC)

  let NUMBER_FIELD_PERMANENT_INTEGRAL ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"(g:A->complex) IN complex_embeddings k"
    let q2 ← q r"m:int"
    let q3 ← q r"m:int"
    let q4 ← q r"x:A"
    let q5 ← q r"k:A ring"
    let v6 ← ISPECL [q5, q4] NUMBER_FIELD_NORM_INTEGRAL_Q
    let q7 ← q r"x:A"
    let q8 ← q r"g:A->complex"
    let q9 ← q r"k:A ring"
    let v10 ← ISPECL [q9, q8, q7] NUMBER_FIELD_NORM_COMPLEX_EMBEDDINGS
    let q11 ← q r"g:A->complex"
    let v12 ← GSYM MEMBER_NOT_EMPTY
    let p13 ← prove r"!k x:A.
        number_field k /\ x IN ring_carrier(ring_of_integers k)
        ==> cproduct (complex_embeddings k) (\g. g x) IN
            {ring_of_int complex_ring a | a IN (:int)}" (REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP COMPLEX_EMBEDDINGS_NONEMPTY)) THEN REWRITE_TAC [v12] THEN DISCH_THEN (X_CHOOSE_TAC q11) THEN MP_TAC v10 THEN ANTS_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], DISCH_THEN (SUBST1_TAC o SYM)] THEN MP_TAC v6 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN q3 SUBST1_TAC) THEN REWRITE_TAC [IN_ELIM_THM, IN_UNIV] THEN EXISTS_TAC q2 THEN UNDISCH_TAC q1 THEN REWRITE_TAC [complex_embeddings, IN_ELIM_THM] THEN DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_RING_OF_INT (← CONJUNCT1 th))])))
    let lemma := p13
    let q14 ← q r"t:K->bool"
    let q15 ← q r"w:K->A"
    let q16 ← q r"ring_homomorphism(k,complex_ring) ((e:K->A->complex) i)"
    let q17 ← q r"i:K"
    let q18 ← q r"ring_product complex_ring s
      (\i. ring_sum complex_ring t (\j. (e:K->A->complex) i (w j))) =
    ring_product complex_ring s (\i. e i (ring_sum k (t:K->bool) w))"
    let q19 ← q r"!j. j IN s ==> (w:K->A) j IN ring_carrier(ring_of_integers k)"
    let q20 ← q r"(t:K->bool) SUBSET s"
    let q21 ← q r"k:A ring"
    let v22 ← ISPEC q21 RING_OF_INTEGERS_SUBSET
    let q23 ← q r"FINITE(t:K->bool) /\
    !j. j IN t ==> (w:K->A) j IN ring_carrier(ring_of_integers k) /\
                   w j IN ring_carrier k"
    let q24 ← q r"t:K->bool"
    let q25 ← q r"!x:complex. x IN {ring_of_int complex_ring a | a IN (:int)}
                ==> ?a. x = ring_of_int complex_ring a"
    let r26 ← SET_RULE q25
    let v27 ← REWRITE_RULE [FUN_EQ_THM] COMPLEX_RING_OF_INT
    let v28 ← GSYM v27
    let q29 ← q r"\i:K j:K. (e:K->A->complex) i ((w:K->A) j)"
    let q30 ← q r"s:K->bool"
    let q31 ← q r"complex_ring"
    let v32 ← ISPECL [q31, q30, q29] RING_SUM_PERMUTATIONS_RYSER
    let v33 ← BETA_RULE v32
    let q34 ← q r"IMAGE (e:K->A->complex) s = complex_embeddings k"
    let q35 ← q r"!i. i IN s ==> ring_homomorphism(k,complex_ring) ((e:K->A->complex) i)"
    let q36 ← q r"!i j. i IN s /\ j IN s /\ (e:K->A->complex) i = e j ==> i = j"
    let q37 ← q r"FINITE(s:K->bool)"
    let v38 ← ASSUME q37
    let v39 ← GSYM COMPLEX_RING_PRODUCT
    let q40 ← q r"!x. ring_product complex_ring s (\i. (e:K->A->complex) i x) =
        cproduct (complex_embeddings k) (\g. g x)"
    let q41 ← q r"s:K->bool"
    let q42 ← q r"e:K->A->complex"
    let v43 ← ISPECL [q42, q41] FINITE_IMAGE_INJ_EQ
    let q44 ← q r"FINITE(s:K->bool)"
    prove
      r"!k s (e:K->A->complex) (w:K->A).
          number_field k /\
          (!j. j IN s ==> w j IN ring_carrier(ring_of_integers k)) /\
          (!i j. i IN s /\ j IN s /\ e i = e j ==> i = j) /\
          IMAGE e s = complex_embeddings k
          ==> ?a. ring_sum complex_ring {p | p permutes s}
                    (\p. ring_product complex_ring s (\i. e i (w (p i)))) =
                  Cx(real_of_int a)"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN q44 ASSUME_TAC THENL [MP_TAC v43 THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, DISCH_THEN (SUBST1_TAC o SYM)] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC FINITE_COMPLEX_EMBEDDINGS THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN SUBGOAL_THEN q40 ASSUME_TAC THENL [GEN_TAC THEN FIRST_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [(← SYM th)])) THEN SIMP_TAC [v39, FINITE_IMAGE, v38] THEN wPart rand (lhand o rand) RING_PRODUCT_IMAGE THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [o_DEF]], UNDISCH_THEN q36 (fun (_ : thm) => ALL_TAC)] THEN SUBGOAL_THEN q35 ASSUME_TAC THENL [UNDISCH_TAC q34 THEN REWRITE_TAC [EXTENSION, IN_IMAGE, complex_embeddings, IN_ELIM_THM] THEN MESON_TAC [], ALL_TAC] THEN MP_TAC v33 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [COMPLEX_RING_CLAUSES, IN_UNIV], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [v28] THEN MATCH_MP_TAC r26 THEN MATCH_MP_TAC IN_SUBRING_MUL THEN SIMP_TAC [PRIME_SUBRING, IN_SUBRING_POW, IN_SUBRING_NEG, IN_SUBRING_1] THEN MATCH_MP_TAC IN_SUBRING_SUM THEN REWRITE_TAC [PRIME_SUBRING] THEN X_GEN_TAC q24 THEN DISCH_THEN (ASSUME_TAC o (REWRITE_RULE [IN_ELIM_THM])) THEN MATCH_MP_TAC IN_SUBRING_MUL THEN SIMP_TAC [PRIME_SUBRING, IN_SUBRING_POW, IN_SUBRING_NEG, IN_SUBRING_1] THEN SUBGOAL_THEN q23 STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [ASM_MESON_TAC [FINITE_SUBSET], ALL_TAC] THEN MP_TAC v22 THEN UNDISCH_TAC q20 THEN UNDISCH_TAC q19 THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN q18 SUBST1_TAC THENL [MATCH_MP_TAC RING_PRODUCT_EQ THEN X_GEN_TAC q17 THEN DISCH_TAC THEN SUBGOAL_THEN q16 MP_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN DISCH_THEN (MP_TAC o ((ISPECL [q15, q14]) o (MATCH_MP RING_HOMOMORPHISM_SUM))) THEN ANTS_TAC THENL [ASM_SIMP_TAC [], SIMP_TAC [o_DEF]], ASM_REWRITE_TAC [] THEN MATCH_MP_TAC lemma THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IN_SUBRING_SUM THEN ASM_SIMP_TAC [RING_OF_INTEGERS_SUBRING]])

  let NUMBER_FIELD_DISCRIMINANT_MOD_4 ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"(a:int) pow 2"
    let q2 ← q r"!x y z n:int. (x == y) (mod n) /\ (y == z) (mod n)
                    ==> (x == z) (mod n)"
    let r3 ← INTEGER_RULE q2
    let q4 ← q r"a:int"
    let v5 ← SPEC q4 INT_REM_2_CASES
    let q6 ← q r"q:int"
    let q7 ← q r"a div &2"
    let q8 ← q r"&2:int"
    let q9 ← q r"a:int"
    let v10 ← SPECL [q9, q8] INT_DIVISION_SIMP
    let p11 ← prove r"!a d:int. (d == a pow 2) (mod &4)
               ==> (d == &0) (mod &4) \/ (d == &1) (mod &4)" (REPEAT GEN_TAC THEN DISCH_TAC THEN MP_TAC v10 THEN SPEC_TAC (q7, q6) THEN GEN_TAC THEN DISJ_CASES_THEN SUBST1_TAC v5 THEN DISCH_TAC THENL [DISJ1_TAC, DISJ2_TAC] THEN MATCH_MP_TAC r3 THEN EXISTS_TAC q1 THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN INTEGER_TAC)
    let lemma := p11
    let q12 ← q r"i:num"
    let q13 ← q r"!m. m < n ==> (e:num->A->complex) m IN complex_embeddings k"
    let q14 ← q r"ring_of_integers k:A ring"
    let q15 ← q r"j:num"
    let q16 ← q r"i:num"
    let q17 ← q r"\i:num j:num. (e:num->A->complex) i ((w:num->A) j)"
    let q18 ← q r"{i:num | i < n}"
    let q19 ← q r"complex_ring"
    let v20 ← ISPECL [q19, q18, q17] RING_DET_PERMANENT_MOD_4
    let v21 ← BETA_RULE v20
    let q22 ← q r"a:int"
    let q23 ← q r"a:int"
    let q24 ← q r"w:num->A"
    let q25 ← q r"e:num->A->complex"
    let q26 ← q r"{i:num | i < n}"
    let q27 ← q r"k:A ring"
    let v28 ← ISPECL [q27, q26, q25, q24] NUMBER_FIELD_PERMANENT_INTEGRAL
    let q29 ← q r"e:num->A->complex"
    let q30 ← q r"w:num->A"
    let q31 ← q r"n:num"
    let q32 ← q r"k:A ring"
    let v33 ← ISPECL [q32, q31, q30, q29] NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS
    let q34 ← q r"(!i j. i < n /\ j < n /\ (e:num->A->complex) i = e j ==> i = j) /\
    IMAGE e {i | i < n} = complex_embeddings k"
    let q35 ← q r"w:num->A"
    let q36 ← q r"e:num->A->complex"
    let q37 ← q r"n = extension_degree (subfield_generated k {ring_0 k:A},k) I"
    prove
      r"!k:A ring.
          number_field k
          ==> (number_field_discriminant k == &0) (mod &4) \/
              (number_field_discriminant k == &1) (mod &4)"
      (REPEAT STRIP_TAC THEN ABBREV_TAC q37 THEN FIRST_ASSUM (MP_TAC o (MATCH_MP RING_OF_INTEGERS_FREE)) THEN FIRST_ASSUM (MP_TAC o (MATCH_MP COMPLEX_EMBEDDINGS_HAS_SIZE)) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN ((X_CHOOSE_THEN q36 STRIP_ASSUME_TAC) o (MATCH_MP HAS_SIZE_INDEX)) THEN DISCH_THEN (X_CHOOSE_TAC q35) THEN SUBGOAL_THEN q34 STRIP_ASSUME_TAC THENL [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN ASM_MESON_TAC [EXISTS_UNIQUE_THM], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [free_basis]))) THEN MP_TAC v33 THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC, DISCH_TAC] THEN MP_TAC v28 THEN ANTS_TAC THENL [REWRITE_TAC [IN_ELIM_THM] THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC, DISCH_THEN (X_CHOOSE_TAC q23)] THEN MATCH_MP_TAC lemma THEN EXISTS_TAC q22 THEN MATCH_MP_TAC v21 THEN ASM_REWRITE_TAC [FIELD_COMPLEX_RING, RING_CHAR_COMPLEX_RING, FINITE_NUMSEG_LT, COMPLEX_RING_OF_INT, COMPLEX_RING_POW, IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [q16, q15] THEN STRIP_TAC THEN MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN EXISTS_TAC q14 THEN CONJ_TAC THENL [MATCH_MP_TAC RING_HOMOMORPHISM_RING_OF_INTEGERS THEN UNDISCH_TAC q13 THEN REWRITE_TAC [complex_embeddings, IN_ELIM_THM] THEN DISCH_THEN (MP_TAC o (SPEC q12)) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, SIMP_TAC []], FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC])

  -- @@RETURN BEGIN
  return { RING_DET_PERMANENT_MOD_4, NUMBER_FIELD_PERMANENT_INTEGRAL,
           NUMBER_FIELD_DISCRIMINANT_MOD_4 }
  -- @@RETURN END

end HolANT.Stickelberger
