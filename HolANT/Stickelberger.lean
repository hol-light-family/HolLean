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
    let lemma := (← prove r"!k x:A b c.
        field k /\ ring_char k = 0 /\
        x IN ring_carrier(ring_of_integers k) /\ ~(c = &0) /\
        ring_mul k (ring_of_int k c) x = ring_of_int k b
        ==> ?m. x = ring_of_int k m" (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_PRIME_SUBFIELD) THEN ASM_REWRITE_TAC [EXTENSION, IN_INTER, IN_ELIM_THM, IN_UNIV] THEN DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM th)])) THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{ring_0 k:A}")] SUBFIELD_SUBFIELD_GENERATED) THEN ASM_REWRITE_TAC [] THEN SPEC_TAC ((← q r"ring_carrier(subfield_generated k {ring_0 k:A})"), (← q r"u:A->bool")) THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"u:A->bool"), (← q r"ring_of_int k c:A")] IN_SUBFIELD_LINV) THEN ASM_SIMP_TAC [IN_SUBRING_INT, SUBFIELD_IMP_SUBRING_OF, RING_OF_INT_EQ_0, (← INTEGER_RULE (← q r"!x:int. &0 divides x <=> x = &0"))] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_of_int k c:A")] RING_INV) THEN REWRITE_TAC [RING_OF_INT] THEN SPEC_TAC ((← q r"ring_inv k (ring_of_int k c):A"), (← q r"z:A")) THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"x = ring_mul k z (ring_of_int k b):A") SUBST1_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun z3 => (do let z7 ← (do let z4 ← (do let z5 ← (pure z3); pure (concl z5)); liftExcept (rand z4)); let z6 ← (q r"ring_of_int k b:A"); pure (z6 == z7)))))) THEN UNDISCH_TAC (← q r"ring_mul k (ring_of_int k c) z = ring_1 k:A") THEN W (fun z1 => tactic_of do pure (MP_TAC (← RING_RULE (← (do pure (Prod.snd (← (pure z1)))))))) THEN ANTS_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], REWRITE_TAC []], MATCH_MP_TAC IN_SUBFIELD_MUL THEN ASM_SIMP_TAC [IN_SUBRING_INT, SUBFIELD_IMP_SUBRING_OF]]))
    prove
      r"!k s (f:K->K->A) a d.
          field k /\ ring_char k = 0 /\ FINITE s /\
          (!i j. i IN s /\ j IN s
                 ==> f i j IN ring_carrier(ring_of_integers k)) /\
          ring_sum k {p | p permutes s} (\p. ring_product k s (\i. f i (p i))) =
          ring_of_int k a /\
          ring_pow k (ring_det k s f) 2 = ring_of_int k d
          ==> (d == a pow 2) (mod &4)"
      (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"x = ring_sum k {p | p permutes s}
          (\p. if evenperm p then ring_product k s (\i. (f:K->K->A) i (p i))
               else ring_0 k)") THEN ABBREV_TAC (← q r"y = ring_sum k {p | p permutes s}
          (\p. if evenperm p then ring_0 k
               else ring_product k s (\i. (f:K->K->A) i (p i)))") THEN SUBGOAL_THEN (← q r"ring_mul k (x:A) y IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [MATCH_MP_TAC IN_SUBRING_MUL THEN REWRITE_TAC [RING_OF_INTEGERS_SUBRING] THEN MAP_EVERY EXPAND_TAC ["x", "y"] THEN CONJ_TAC THEN MATCH_MP_TAC IN_SUBRING_SUM THEN REWRITE_TAC [RING_OF_INTEGERS_SUBRING] THEN X_GEN_TAC (← q r"p:K->K") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN COND_CASES_TAC THEN SIMP_TAC [RING_OF_INTEGERS_SUBRING, IN_SUBRING_0] THEN MATCH_MP_TAC IN_SUBRING_PRODUCT THEN REWRITE_TAC [RING_OF_INTEGERS_SUBRING] THEN ASM_MESON_TAC [PERMUTES_IN_IMAGE], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_add k (x:A) y = ring_of_int k a /\
    ring_sub k x y = ring_det k s (f:K->K->A)") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"ring_sum k {p | p permutes s}
        (\p. ring_product k s (\i. (f:K->K->A) i (p i))) =
      ring_of_int k a") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MAP_EVERY EXPAND_TAC ["x", "y"] THEN REWRITE_TAC [ring_det] THEN CONJ_TAC THENL [wPart lhand (rand o rand) RING_SUM_ADD, wPart lhand (rand o rand) RING_SUM_SUB] THEN (ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_PERMUTATIONS] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [RING_PRODUCT, RING_0], DISCH_THEN (SUBST1_TAC o SYM)]) THEN MATCH_MP_TAC RING_SUM_EQ THEN GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [ring_sign] THEN COND_CASES_TAC THEN SIMP_TAC [RING_ADD_LZERO, RING_ADD_RZERO, RING_SUB_RZERO, RING_SUB_LZERO, RING_MUL_LID, RING_MUL_LNEG, RING_PRODUCT, RING_1], ALL_TAC] THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier k /\ y IN ring_carrier k") STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["x", "y"] THEN REWRITE_TAC [RING_SUM], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul k (ring_of_int k (&4)) (ring_mul k x y) =
    ring_of_int k (a pow 2 - d):A") ASSUME_TAC THENL [REWRITE_TAC [(← GSYM RING_OF_INT_CLAUSES)] THEN REWRITE_TAC [(← GSYM (← ASSUME (← q r"ring_add k (x:A) y = ring_of_int k a"))), (← GSYM (← ASSUME (← q r"ring_pow k (ring_det k s (f:K->K->A)) 2 =
                             ring_of_int k d")))] THEN REWRITE_TAC [(← GSYM (← ASSUME (← q r"ring_sub k (x:A) y = ring_det k s (f:K->K->A)")))] THEN W (fun z36 => tactic_of do pure (MP_TAC (← RING_RULE (← (do pure (Prod.snd (← (pure z36)))))))) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_mul k x y:A"), (← q r"a pow 2 - d:int"), (← q r"&4:int")] lemma) THEN ASM_REWRITE_TAC [INT_OF_NUM_EQ, ARITH_EQ] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"c:int")) THEN UNDISCH_TAC (← q r"ring_mul k (ring_of_int k (&4)) (ring_mul k x y) =
    ring_of_int k (a pow 2 - d):A") THEN ASM_SIMP_TAC [RING_OF_INT_CLAUSES, RING_OF_INT_EQ_CHAR_0] THEN DISCH_TAC THEN REWRITE_TAC [int_congruent] THEN EXISTS_TAC (← q r"--c:int") THEN ASM_INT_ARITH_TAC)

  let NUMBER_FIELD_PERMANENT_INTEGRAL ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let lemma := (← prove r"!k x:A.
        number_field k /\ x IN ring_carrier(ring_of_integers k)
        ==> cproduct (complex_embeddings k) (\g. g x) IN
            {ring_of_int complex_ring a | a IN (:int)}" (REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP COMPLEX_EMBEDDINGS_NONEMPTY)) THEN REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY)] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"g:A->complex")) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"g:A->complex"), (← q r"x:A")] NUMBER_FIELD_NORM_COMPLEX_EMBEDDINGS) THEN ANTS_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], DISCH_THEN (SUBST1_TAC o SYM)] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A")] NUMBER_FIELD_NORM_INTEGRAL_Q) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"m:int") SUBST1_TAC) THEN REWRITE_TAC [IN_ELIM_THM, IN_UNIV] THEN EXISTS_TAC (← q r"m:int") THEN UNDISCH_TAC (← q r"(g:A->complex) IN complex_embeddings k") THEN REWRITE_TAC [complex_embeddings, IN_ELIM_THM] THEN DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_RING_OF_INT (← CONJUNCT1 th))]))))
    prove
      r"!k s (e:K->A->complex) (w:K->A).
          number_field k /\
          (!j. j IN s ==> w j IN ring_carrier(ring_of_integers k)) /\
          (!i j. i IN s /\ j IN s /\ e i = e j ==> i = j) /\
          IMAGE e s = complex_embeddings k
          ==> ?a. ring_sum complex_ring {p | p permutes s}
                    (\p. ring_product complex_ring s (\i. e i (w (p i)))) =
                  Cx(real_of_int a)"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"FINITE(s:K->bool)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"e:K->A->complex"), (← q r"s:K->bool")] FINITE_IMAGE_INJ_EQ) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, DISCH_THEN (SUBST1_TAC o SYM)] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC FINITE_COMPLEX_EMBEDDINGS THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"!x. ring_product complex_ring s (\i. (e:K->A->complex) i x) =
        cproduct (complex_embeddings k) (\g. g x)") ASSUME_TAC THENL [GEN_TAC THEN FIRST_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [(← SYM th)])) THEN SIMP_TAC [(← GSYM COMPLEX_RING_PRODUCT), FINITE_IMAGE, (← ASSUME (← q r"FINITE(s:K->bool)"))] THEN wPart rand (lhand o rand) RING_PRODUCT_IMAGE THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [o_DEF]], UNDISCH_THEN (← q r"!i j. i IN s /\ j IN s /\ (e:K->A->complex) i = e j ==> i = j") (fun (_ : thm) => ALL_TAC)] THEN SUBGOAL_THEN (← q r"!i. i IN s ==> ring_homomorphism(k,complex_ring) ((e:K->A->complex) i)") ASSUME_TAC THENL [UNDISCH_TAC (← q r"IMAGE (e:K->A->complex) s = complex_embeddings k") THEN REWRITE_TAC [EXTENSION, IN_IMAGE, complex_embeddings, IN_ELIM_THM] THEN MESON_TAC [], ALL_TAC] THEN MP_TAC (← BETA_RULE (← ISPECL [(← q r"complex_ring"), (← q r"s:K->bool"), (← q r"\i:K j:K. (e:K->A->complex) i ((w:K->A) j)")] RING_SUM_PERMUTATIONS_RYSER)) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [COMPLEX_RING_CLAUSES, IN_UNIV], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [(← GSYM (← REWRITE_RULE [FUN_EQ_THM] COMPLEX_RING_OF_INT))] THEN MATCH_MP_TAC (← SET_RULE (← q r"!x:complex. x IN {ring_of_int complex_ring a | a IN (:int)}
                ==> ?a. x = ring_of_int complex_ring a")) THEN MATCH_MP_TAC IN_SUBRING_MUL THEN SIMP_TAC [PRIME_SUBRING, IN_SUBRING_POW, IN_SUBRING_NEG, IN_SUBRING_1] THEN MATCH_MP_TAC IN_SUBRING_SUM THEN REWRITE_TAC [PRIME_SUBRING] THEN X_GEN_TAC (← q r"t:K->bool") THEN DISCH_THEN (ASSUME_TAC o (REWRITE_RULE [IN_ELIM_THM])) THEN MATCH_MP_TAC IN_SUBRING_MUL THEN SIMP_TAC [PRIME_SUBRING, IN_SUBRING_POW, IN_SUBRING_NEG, IN_SUBRING_1] THEN SUBGOAL_THEN (← q r"FINITE(t:K->bool) /\
    !j. j IN t ==> (w:K->A) j IN ring_carrier(ring_of_integers k) /\
                   w j IN ring_carrier k") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [ASM_MESON_TAC [FINITE_SUBSET], ALL_TAC] THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_SUBSET) THEN UNDISCH_TAC (← q r"(t:K->bool) SUBSET s") THEN UNDISCH_TAC (← q r"!j. j IN s ==> (w:K->A) j IN ring_carrier(ring_of_integers k)") THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_product complex_ring s
      (\i. ring_sum complex_ring t (\j. (e:K->A->complex) i (w j))) =
    ring_product complex_ring s (\i. e i (ring_sum k (t:K->bool) w))") SUBST1_TAC THENL [MATCH_MP_TAC RING_PRODUCT_EQ THEN X_GEN_TAC (← q r"i:K") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_homomorphism(k,complex_ring) ((e:K->A->complex) i)") MP_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN DISCH_THEN (MP_TAC o ((ISPECL [(← q r"w:K->A"), (← q r"t:K->bool")]) o (MATCH_MP RING_HOMOMORPHISM_SUM))) THEN ANTS_TAC THENL [ASM_SIMP_TAC [], SIMP_TAC [o_DEF]], ASM_REWRITE_TAC [] THEN MATCH_MP_TAC lemma THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IN_SUBRING_SUM THEN ASM_SIMP_TAC [RING_OF_INTEGERS_SUBRING]])

  let NUMBER_FIELD_DISCRIMINANT_MOD_4 ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let lemma := (← prove r"!a d:int. (d == a pow 2) (mod &4)
               ==> (d == &0) (mod &4) \/ (d == &1) (mod &4)" (REPEAT GEN_TAC THEN DISCH_TAC THEN MP_TAC (← SPECL [(← q r"a:int"), (← q r"&2:int")] INT_DIVISION_SIMP) THEN SPEC_TAC ((← q r"a div &2"), (← q r"q:int")) THEN GEN_TAC THEN DISJ_CASES_THEN SUBST1_TAC (← SPEC (← q r"a:int") INT_REM_2_CASES) THEN DISCH_TAC THENL [DISJ1_TAC, DISJ2_TAC] THEN MATCH_MP_TAC (← INTEGER_RULE (← q r"!x y z n:int. (x == y) (mod n) /\ (y == z) (mod n)
                    ==> (x == z) (mod n)")) THEN EXISTS_TAC (← q r"(a:int) pow 2") THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN INTEGER_TAC))
    prove
      r"!k:A ring.
          number_field k
          ==> (number_field_discriminant k == &0) (mod &4) \/
              (number_field_discriminant k == &1) (mod &4)"
      (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"n = extension_degree (subfield_generated k {ring_0 k:A},k) I") THEN FIRST_ASSUM (MP_TAC o (MATCH_MP RING_OF_INTEGERS_FREE)) THEN FIRST_ASSUM (MP_TAC o (MATCH_MP COMPLEX_EMBEDDINGS_HAS_SIZE)) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"e:num->A->complex") STRIP_ASSUME_TAC) o (MATCH_MP HAS_SIZE_INDEX)) THEN DISCH_THEN (X_CHOOSE_TAC (← q r"w:num->A")) THEN SUBGOAL_THEN (← q r"(!i j. i < n /\ j < n /\ (e:num->A->complex) i = e j ==> i = j) /\
    IMAGE e {i | i < n} = complex_embeddings k") STRIP_ASSUME_TAC THENL [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN ASM_MESON_TAC [EXISTS_UNIQUE_THM], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [free_basis]))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"e:num->A->complex")] NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS) THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC, DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{i:num | i < n}"), (← q r"e:num->A->complex"), (← q r"w:num->A")] NUMBER_FIELD_PERMANENT_INTEGRAL) THEN ANTS_TAC THENL [REWRITE_TAC [IN_ELIM_THM] THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC, DISCH_THEN (X_CHOOSE_TAC (← q r"a:int"))] THEN MATCH_MP_TAC lemma THEN EXISTS_TAC (← q r"a:int") THEN MATCH_MP_TAC (← BETA_RULE (← ISPECL [(← q r"complex_ring"), (← q r"{i:num | i < n}"), (← q r"\i:num j:num. (e:num->A->complex) i ((w:num->A) j)")] RING_DET_PERMANENT_MOD_4)) THEN ASM_REWRITE_TAC [FIELD_COMPLEX_RING, RING_CHAR_COMPLEX_RING, FINITE_NUMSEG_LT, COMPLEX_RING_OF_INT, COMPLEX_RING_POW, IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"i:num"), (← q r"j:num")] THEN STRIP_TAC THEN MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN EXISTS_TAC (← q r"ring_of_integers k:A ring") THEN CONJ_TAC THENL [MATCH_MP_TAC RING_HOMOMORPHISM_RING_OF_INTEGERS THEN UNDISCH_TAC (← q r"!m. m < n ==> (e:num->A->complex) m IN complex_embeddings k") THEN REWRITE_TAC [complex_embeddings, IN_ELIM_THM] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"i:num"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, SIMP_TAC []], FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC])

  -- @@RETURN BEGIN
  return { RING_DET_PERMANENT_MOD_4, NUMBER_FIELD_PERMANENT_INTEGRAL,
           NUMBER_FIELD_DISCRIMINANT_MOD_4 }
  -- @@RETURN END

end HolANT.Stickelberger
