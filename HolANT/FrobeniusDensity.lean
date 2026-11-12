/- ========================================================================= -/
/- ANT: The Frobenius density theorem                                      -/
/- ========================================================================= -/
/- File: HolANT/FrobeniusDensity.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/frobenius_density.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antfrobeniusdensitydiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/frag.ml, Library/grouptheory.ml, Library/symmetric_group.ml, Library/galois.ml, Library/products.ml, Library/floor.ml, Multivariate/misc.ml, Multivariate/metric.ml, Multivariate/homology.ml, Multivariate/vectors.ml, Multivariate/determinants.ml, Multivariate/topology.ml, Multivariate/convex.ml, Multivariate/paths.ml, Multivariate/polytope.ml, Multivariate/degree.ml, Multivariate/derivatives.ml, Multivariate/integration.ml, Multivariate/measure.ml, Multivariate/complex_algebra.ml, Multivariate/complexes.ml, Multivariate/canal.ml, Multivariate/transcendentals.ml, Multivariate/realanalysis.ml, Library/isum.ml, ANT/algmisc.ml, ANT/ideal_arith.ml, ANT/integral.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/zlattice.ml, ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/classgroup.ml, ANT/prime_split.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/finite_field_trace.ml, ANT/ramification.ml, ANT/relative_degree.ml, ANT/splitting_types.ml, Library/ring_groups.ml, Library/finite_fields.ml, ANT/decomposition.ml, ANT/nf_valuation.ml, ANT/nf_decomposition.ml, ANT/decomposition_field.ml, ANT/integrality.ml, ANT/fingen_group.ml, Multivariate/moretop.ml, Multivariate/cauchy.ml, Multivariate/complex_ring.ml, Multivariate/complex_field.ml, ANT/complex_embeddings.ml, ANT/power_basis.ml, ANT/infinite_places.ml, ANT/dedekind_zeta.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.FrobeniusDensity fills them).

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
import HolLibrary.Products
import HolLibrary.Floor
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
import HolLibrary.Isum
import HolANT.Algmisc
import HolANT.IdealArith
import HolANT.Integral
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.IdealNorm
import HolANT.Zlattice
import HolANT.Numfield
import HolANT.RingOfIntegers
import HolANT.NormIndex
import HolANT.Classgroup
import HolANT.PrimeSplit
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.Discriminant
import HolANT.TraceForm
import HolANT.RelativeSplit
import HolANT.FiniteFieldTrace
import HolANT.Ramification
import HolANT.RelativeDegree
import HolANT.SplittingTypes
import HolLibrary.RingGroups
import HolLibrary.FiniteFields
import HolANT.Decomposition
import HolANT.NfValuation
import HolANT.NfDecomposition
import HolANT.DecompositionField
import HolANT.Integrality
import HolANT.FingenGroup
import HolMultiLib.MoreTop
import HolMultiLib.Cauchy
import HolMultiLib.ComplexRing
import HolMultiLib.ComplexField
import HolANT.ComplexEmbeddings
import HolANT.PowerBasis
import HolANT.InfinitePlaces
import HolANT.DedekindZeta

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
open HolANT.DedekindStruct
open HolANT.IdealNorm
open HolANT.Zlattice
open HolANT.Numfield
open HolANT.RingOfIntegers
open HolANT.NormIndex
open HolANT.Classgroup
open HolANT.PrimeSplit
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.Discriminant
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.FiniteFieldTrace
open HolANT.Ramification
open HolANT.RelativeDegree
open HolANT.SplittingTypes
open HolANT.Decomposition
open HolANT.NfValuation
open HolANT.NfDecomposition
open HolANT.DecompositionField
open HolANT.Integrality
open HolANT.FingenGroup
open HolANT.ComplexEmbeddings
open HolANT.PowerBasis
open HolANT.InfinitePlaces
open HolANT.DedekindZeta

namespace HolANT.FrobeniusDensity

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD_CLAUSES CARD_CLAUSES CARD_CONJUGATES_INTO_CYCLIC_GENERATORS
   CARD_CONJUGATES_IN_TORSION_NSUM CARD_CROSS CARD_CYCLIC_SUBGROUP_DIVISION
   CARD_EQ_0 CARD_IMAGE_INJ CARD_RESTRICT_POW_EQ_ID CARD_SING
   CARRIER_SUBGROUP_GENERATED_SUBGROUP COND_ID CONJ_ASSOC
   CYCLIC_SUBGROUP_TORSION_SUBGROUP DECOMPOSITION_GROUP DE_MORGAN_THM
   DIRICHLET_SERIES_FINITE_PERTURBATION DIVIDES_LE DIVIDES_REFL DIVIDES_TRANS
   EMPTY_GSPEC EQ_TRANS EXISTS_PAIR_THM EXTENSION FINITE_CROSS FINITE_DIVISORS
   FINITE_EMPTY FINITE_GALOIS_GROUP FINITE_GROUP_ELEMENT_ORDER_NONZERO
   FINITE_GROUP_NORMALIZER FINITE_IMAGE FINITE_RAMIFIED FINITE_RESTRICT
   FINITE_SUBSET FORALL_PAIR_THM FUN_EQ_THM GALOIS_EXTENSION_EQ_CARD
   GALOIS_EXTENSION_SUBFIELD_GENERATED GALOIS_GROUP GALOIS_GROUP_FIXED_FIELD
   GALOIS_GROUP_PERMUTES GALOIS_IMP_FIELD_EXTENSION GROUP_CARRIER_NONEMPTY
   GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET GROUP_CONJUGATION_BY_ID
   GROUP_CONJUGATION_CONJUGATION GROUP_CONJUGATION_EQ_ID GROUP_ID GROUP_INV
   GROUP_MUL GROUP_MUL_RCANCEL GROUP_NORMALIZER_NONEMPTY
   HAS_DIRICHLET_DENSITY_INFINITE HAS_DIRICHLET_DENSITY_LOG IMAGE_CLAUSES
   IMAGE_I IMAGE_o IMP_CONJ IN_CROSS IN_ELIM_THM IN_FIXED_FIELD IN_IMAGE
   IN_INSERT IN_INTER IN_SING IN_SUBGROUP_CONJUGATION I_O_ID LEFT_IMP_EXISTS_THM
   LE_0 LE_REFL MEMBER_NOT_EMPTY MONO_EXISTS MULT_CLAUSES MULT_SYM NOT_IN_EMPTY
   NSUM_CASES NSUM_CLAUSES NSUM_CONST NSUM_EQ NSUM_LMUL NSUM_RESTRICT_SET
   NSUM_SUBSET_SIMPLE NSUM_SWAP NUMBER_FIELD_DECOMPOSITION_GROUP_FROBENIUS : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (NUMBER_FIELD_DEGREE_ONE_PRIMES_LOG
   NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM
   NUMBER_FIELD_FROBENIUS_CONJUGATE_PRIME NUMBER_FIELD_FROBENIUS_ELEMENT
   NUMBER_FIELD_GALOIS_GROUP_TRANSITIVE NUMBER_FIELD_GALOIS_SPLITTING_TYPES
   NUMBER_FIELD_HOMOMORPHIC_PREIMAGE NUMBER_FIELD_IDEAL_SUM_BY_NORM
   NUMBER_FIELD_INTERMEDIATE_FIELD NUMBER_FIELD_INTERMEDIATE_SPLITTING
   NUMBER_FIELD_NONPRIME_NORM_SUM_LE NUMBER_FIELD_PRIME_IDEALS_ABOVE
   NUMBER_FIELD_PRIME_IDEALS_INTERMEDIATE NUMBER_FIELD_PRIME_IDEAL_DEGREE_ONE
   NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE NUMBER_FIELD_PRIME_NORM_CARD
   NUMBER_FIELD_TOWER_LAW NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED
   NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP PAIR_EQ PERMUTES_INJECTIVE
   PERMUTES_INVERSES_o PRIME_IDEAL_IMP_SUBSET PRIME_IMP_RING_IDEAL REAL_ABS_INV
   REAL_ABS_MUL REAL_ABS_NUM REAL_ADD_LDISTRIB REAL_ADD_LID REAL_ADD_RID
   REAL_DIV_EQ_0 REAL_EQ_IMP_LE REAL_INFSUM_ADD REAL_INFSUM_LMUL
   REAL_INFSUM_UNIQUE REAL_LE_DIV REAL_LE_INV_EQ REAL_LE_LMUL REAL_LE_TRANS
   REAL_MUL_ASSOC REAL_MUL_LID REAL_MUL_LINV REAL_MUL_LZERO REAL_OF_NUM_ADD
   REAL_OF_NUM_EQ REAL_OF_NUM_LE REAL_OF_NUM_MUL REAL_OF_NUM_SUM REAL_POS
   REAL_SERIES_FINITE_SUM REAL_SERIES_POS REAL_SERIES_SUB REAL_SUMMABLE_ADD
   REAL_SUMMABLE_LMUL REAL_SUMMABLE_POS_PARTIAL_BOUND REAL_SUMS_INFSUM
   RIGHT_EXISTS_IMP_THM RIGHT_IMP_EXISTS_THM RING_MONOMORPHISM_IMP_HOMOMORPHISM
   RING_OF_INTEGERS_SUBSET RPOW_POS_LE SING_SUBSET SKOLEM_THM SUBFIELD_GENERATED
   SUBGROUP_GENERATED_INC SUBGROUP_OF_IMP_SUBSET SUBSET SUM_ABS SUM_ADD
   SUM_CLAUSES SUM_EQ_NUMSEG SUM_LE SUM_RMUL SUM_SUBSET_SIMPLE
   TRIVIAL_SUBGROUP_OF UNRAMIFIED_IMP_WEAKLY_UNRAMIFIED field_extension num_WF
   real_div real_summable subgroup_of totally_split weakly_unramified : thm)
  deriving Inhabited

/-- What frobenius_density.ml uses from Session besides theorems. -/
structure FrobeniusDensityDeps where
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
  REAL_RING : term → ExceptT String IO thm
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
/- frobenius_density.ml phrases from line 119 to 528                      -/
/- ---------------------------------------------------------------------- -/

structure FrobeniusDensity01 where
  -- @@FIELDS
  NUMBER_FIELD_FIXED_FIELD_PRIME_DEGREE_ONE : thm
  NUMBER_FIELD_FIXED_FIELD_DEGREE_ONE_CARD : thm
  NUMBER_FIELD_DEGREE_ONE_CARD : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFrobeniusDensity01 [HolBase] (D : FrobeniusDensityDeps) :
    ExceptT String IO FrobeniusDensity01 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, GROUP_RULE, MESON, SET_TAC, TAUT, .. } := D
  let { CARD_CLAUSES, CARD_CROSS, CARD_IMAGE_INJ, DECOMPOSITION_GROUP, EQ_TRANS,
        EXISTS_PAIR_THM, EXTENSION, FINITE_CROSS, FINITE_GALOIS_GROUP, FINITE_SUBSET,
        FORALL_PAIR_THM, GALOIS_EXTENSION_SUBFIELD_GENERATED, GALOIS_GROUP,
        GALOIS_GROUP_FIXED_FIELD, GALOIS_GROUP_PERMUTES, GALOIS_IMP_FIELD_EXTENSION,
        GROUP_CONJUGATION_CONJUGATION, GROUP_INV, GROUP_MUL, GROUP_MUL_RCANCEL,
        IMAGE_I, IMAGE_o, IN_CROSS, IN_ELIM_THM, IN_FIXED_FIELD, IN_IMAGE, IN_INTER,
        IN_SUBGROUP_CONJUGATION, I_O_ID, LEFT_IMP_EXISTS_THM, MONO_EXISTS,
        NOT_IN_EMPTY, .. } := D.core1
  let { NUMBER_FIELD_FROBENIUS_CONJUGATE_PRIME, NUMBER_FIELD_FROBENIUS_ELEMENT,
        NUMBER_FIELD_GALOIS_GROUP_TRANSITIVE, NUMBER_FIELD_INTERMEDIATE_FIELD,
        NUMBER_FIELD_INTERMEDIATE_SPLITTING, NUMBER_FIELD_PRIME_IDEALS_ABOVE,
        NUMBER_FIELD_PRIME_IDEALS_INTERMEDIATE, NUMBER_FIELD_PRIME_IDEAL_DEGREE_ONE,
        NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE, NUMBER_FIELD_TOWER_LAW,
        NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP, PAIR_EQ, PERMUTES_INJECTIVE,
        PERMUTES_INVERSES_o, PRIME_IDEAL_IMP_SUBSET, RIGHT_IMP_EXISTS_THM,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_OF_INTEGERS_SUBSET, SING_SUBSET,
        SKOLEM_THM, SUBFIELD_GENERATED, SUBGROUP_OF_IMP_SUBSET, SUBSET,
        UNRAMIFIED_IMP_WEAKLY_UNRAMIFIED, field_extension, subgroup_of,
        weakly_unramified, .. } := D.core2
  -- @@SCOPE END

  let NUMBER_FIELD_FIXED_FIELD_PRIME_DEGREE_ONE ← prove
    r"!(h:A->B) k l H p Q g.
        number_field l /\ galois_extension(k,l) h /\
        H subgroup_of galois_group(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        unramified (ring_of_integers k,ring_of_integers l) h p /\
        prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q /\
        g IN group_carrier(galois_group(k,l) h)
        ==> prime_ideal
             (ring_of_integers(subfield_generated l (fixed_field l H)))
             (IMAGE g Q INTER fixed_field l H) /\
            ~(IMAGE g Q INTER fixed_field l H = {ring_0 l}) /\
            IMAGE h p SUBSET IMAGE g Q INTER fixed_field l H /\
            (residue_degree
              (ring_of_integers k,
               ring_of_integers(subfield_generated l (fixed_field l H)))
              h (IMAGE g Q INTER fixed_field l H) = 1 <=>
             group_conjugation (galois_group(k,l) h) g
               (frobenius_element (k,l) h (ring_of_integers l) Q) IN H)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"field k /\ ring_homomorphism(k,l) (h:A->B)") STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_IMP_FIELD_EXTENSION)) THEN SIMP_TAC [field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"H:(B->B)->bool"), (← q r"p:A->bool"), (← q r"Q:B->bool"), (← q r"g:B->B")] NUMBER_FIELD_FROBENIUS_CONJUGATE_PRIME) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"H:(B->B)->bool")] GALOIS_GROUP_FIXED_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"fixed_field l H:B->bool"), (← q r"p:A->bool"), (← q r"IMAGE (g:B->B) Q")] NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"fixed_field l H:B->bool"), (← q r"p:A->bool"), (← q r"IMAGE (g:B->B) Q")] NUMBER_FIELD_INTERMEDIATE_SPLITTING) THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"group_carrier(inertia_group(k,l) (h:A->B) (ring_of_integers l)
                   (IMAGE (g:B->B) Q)) SUBSET H") (fun th => REWRITE_TAC [th]) THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"IMAGE (g:B->B) Q")] NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP) THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ramification_index (ring_of_integers k,ring_of_integers l) (h:A->B)
        (IMAGE (g:B->B) Q) = 1") (fun th => REWRITE_TAC [th]) THENL [ASM_MESON_TAC [UNRAMIFIED_IMP_WEAKLY_UNRAMIFIED, weakly_unramified], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [SING_SUBSET] THEN FIRST_ASSUM (MP_TAC o ((MATCH_MP SUBGROUP_OF_IMP_SUBSET) o (checkM (fun th => (do let z7 ← (do let z8 ← (pure th); pure (concl z8)); canM (fun z9 => (do let z12 ← (pure z9); let z11 ← (q r"H subgroup_of (G:(B->B)group)"); let z10 ← (pure []); term_match z10 z11 z12)) z7))))) THEN FIRST_ASSUM (MP_TAC o (CONJUNCT1 o (CONJUNCT2 o ((GEN_REWRITE_RULE id [subgroup_of]) o (checkM (fun th => (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); canM (fun z3 => (do let z6 ← (pure z3); let z5 ← (q r"H subgroup_of (G:(B->B)group)"); let z4 ← (pure []); term_match z4 z5 z6)) z1))))))) THEN REWRITE_TAC [GALOIS_GROUP] THEN SIMP_TAC [], ALL_TAC] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_FIXED_FIELD_DEGREE_ONE_CARD ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"H subgroup_of G /\ (x:A) IN H /\ y IN H ==> group_mul G x y IN H"
    let r2 ← MESON [subgroup_of] q1
    let q3 ← q r"!G g h0 r:B->B.
        g IN group_carrier G /\ h0 IN group_carrier G /\ r IN group_carrier G
        ==> g = group_mul G (group_mul G h0
                  (group_mul G (group_inv G h0)
                     (group_mul G g (group_inv G r)))) r"
    let r4 ← GROUP_RULE q3
    let q21 ← q r"group_mul G = ((o):(B->B)->(B->B)->(B->B))"
    let v22 ← ASSUME q21
    let v23 ← GSYM v22
    let q24 ← q r"(q:B->bool) IN S1"
    let v25 ← ASSUME q24
    let q26 ← q r"(rep:(B->bool)->(B->B)) q = r"
    let v27 ← ASSUME q26
    let q28 ← q r"q:B->bool"
    let q29 ← q r"group_mul G (h0:B->B) kk"
    let q30 ← q r"galois_group(k,l) (h:A->B) = G"
    let v31 ← ASSUME q30
    let q32 ← q r"(r:B->B) IN X"
    let v33 ← ASSUME q32
    let q41 ← q r"r:B->B"
    let q42 ← q r"(kk:B->B) IN H"
    let v46 ← GSYM IMAGE_o
    let v53 ← GSYM IMAGE_o
    let q54 ← q r"IMAGE (inverse r) (IMAGE (r:B->B) Q) = Q"
    let q58 ← q r"IMAGE (kk:B->B) (IMAGE (r:B->B) Q) = IMAGE r Q"
    let q59 ← q r"k:A ring"
    let q60 ← q r"h:A->B"
    let q61 ← q r"(h0:B->B) permutes ring_carrier(l:B ring) /\
    (r:B->B) permutes ring_carrier l"
    let q62 ← q r"group_inv (G:(B->B)group) = (inverse:(B->B)->(B->B))"
    let v63 ← ASSUME q62
    let q64 ← q r"group_mul G = ((o):(B->B)->(B->B)->(B->B))"
    let v65 ← ASSUME q64
    let q66 ← q r"(kk:B->B) = inverse (h0:B->B) o (g:B->B) o inverse (r:B->B)"
    let q67 ← q r"(kk:B->B) IN group_carrier G"
    let q68 ← q r"kk = group_mul G (group_inv G h0)
              (group_mul G g (group_inv G (r:B->B)))"
    let q69 ← q r"(h0:B->B) IN group_carrier G"
    let q70 ← q r"h0:B->B"
    let q81 ← q r"g:B->B"
    let q82 ← q r"r:B->B"
    let q83 ← q r"(r:B->B) IN X /\ (c:(B->B)->B->bool) r = q /\ r IN group_carrier G"
    let q84 ← q r"r = (rep:(B->bool)->(B->B)) q"
    let q85 ← q r"(q:B->bool) IN S1"
    let q86 ← q r"q = (c:(B->B)->B->bool) g"
    let q92 ← q r"g:B->B"
    let q93 ← q r"(g:B->B) IN group_carrier G"
    let v94 ← GSYM GROUP_CONJUGATION_CONJUGATION
    let q95 ← q r"(h0:B->B) o (rep:(B->bool)->(B->B)) q = group_mul G h0 (rep q)"
    let q96 ← q r"(h0:B->B) IN group_carrier G"
    let q97 ← q r"(rep:(B->bool)->(B->B)) q IN X"
    let q98 ← q r"q:B->bool"
    let q99 ← q r"h0:B->B"
    let q100 ← q r"g:B->B"
    let q101 ← q r"(rep:(B->bool)->(B->B)) q2"
    let q102 ← q r"h2:B->B"
    let q103 ← q r"h1:B->B"
    let q104 ← q r"G:(B->B)group"
    let v105 ← ISPECL [q104, q103, q102, q101] GROUP_MUL_RCANCEL
    let q118 ← q r"(c:(B->B)->B->bool) ((rep:(B->bool)->(B->B)) q)"
    let q119 ← q r"!h0 q. h0 IN H /\ q IN S1
               ==> (c:(B->B)->B->bool) (h0 o (rep:(B->bool)->(B->B)) q) = q"
    let q120 ← q r"c:(B->B)->B->bool"
    let q121 ← q r"q1:B->bool = q2"
    let q122 ← q r"q2:B->bool"
    let q123 ← q r"h2:B->B"
    let q124 ← q r"q1:B->bool"
    let q125 ← q r"h1:B->B"
    let q126 ← q r"CARD(IMAGE (\z. FST z o (rep:(B->bool)->(B->B)) (SND z))
               ((H:(B->B)->bool) CROSS (S1:(B->bool)->bool)))"
    let q127 ← q r"CARD((H:(B->B)->bool) CROSS (S1:(B->bool)->bool))"
    let q128 ← q r"Q:B->bool"
    let q129 ← q r"p:A->bool"
    let q130 ← q r"l:B ring"
    let q131 ← q r"k:A ring"
    let q132 ← q r"h:A->B"
    let v133 ← ISPECL [q132, q131, q130, q129, q128] NUMBER_FIELD_FROBENIUS_ELEMENT
    let q134 ← q r"(Fr:B->B) IN group_carrier G"
    let q135 ← q r"!q. q IN S1 ==> (rep:(B->bool)->(B->B)) q IN group_carrier G"
    let q136 ← q r"(c:(B->B)->B->bool) g1 = c g2"
    let q137 ← q r"ring_0(M:B ring) = ring_0 l"
    let q138 ← q r"IMAGE (g2:B->B) Q"
    let q139 ← q r"IMAGE (g1:B->B) Q"
    let q140 ← q r"(c:(B->B)->B->bool) g2"
    let q141 ← q r"l:B ring"
    let q142 ← q r"M:B ring"
    let q143 ← q r"I:B->B"
    let v144 ← ISPECL [q143, q142, q141, q140, q139, q138] NUMBER_FIELD_GALOIS_GROUP_TRANSITIVE
    let q150 ← q r"g2:B->B"
    let q156 ← q r"g1:B->B"
    let q157 ← q r"!g1 g2. g1 IN group_carrier G /\ g2 IN group_carrier G /\
            (c:(B->B)->B->bool) g1 = c g2
            ==> ?h0. h0 IN H /\ IMAGE h0 (IMAGE g1 Q) = IMAGE (g2:B->B) Q"
    let q158 ← q r"y:B"
    let q159 ← q r"z:B = y"
    let q160 ← q r"z:B"
    let q166 ← q r"y:B"
    let q167 ← q r"(y:B) IN s"
    let q168 ← q r"y:B"
    let q169 ← q r"!y. y IN s ==> (h0:B->B) y = y /\ y IN ring_carrier l"
    let q170 ← q r"l:B ring"
    let v171 ← ISPEC q170 RING_OF_INTEGERS_SUBSET
    let q177 ← q r"r:B->B"
    let q178 ← q r"IMAGE (r:B->B) Q SUBSET ring_carrier l"
    let q179 ← q r"k:A ring"
    let q180 ← q r"h:A->B"
    let q181 ← q r"(h0:B->B) permutes ring_carrier l"
    let q182 ← q r"!h0 r. h0 IN H /\ r IN group_carrier G
           ==> (c:(B->B)->B->bool) (h0 o r) = c r"
    let q183 ← q r"p:A->bool"
    let q184 ← q r"h:A->B"
    let q185 ← q r"M:B ring"
    let q186 ← q r"k:A ring"
    let v187 ← ISPECL [q186, q185, q184, q183] NUMBER_FIELD_PRIME_IDEALS_ABOVE
    let q188 ← q r"{P | prime_ideal (ring_of_integers M) P /\
                     IMAGE (h:A->B) p SUBSET P}"
    let q189 ← q r"FINITE(S1:(B->bool)->bool)"
    let q190 ← q r"X SUBSET group_carrier(G:(B->B)group)"
    let q191 ← q r"rep:(B->bool)->(B->B)"
    let q203 ← q r"g:B->B"
    let q204 ← q r"(c:(B->B)->B->bool) g = P"
    let q205 ← q r"g:B->B"
    let q206 ← q r"Q':B->bool"
    let q207 ← q r"Q:B->bool"
    let q208 ← q r"p:A->bool"
    let q209 ← q r"l:B ring"
    let q210 ← q r"k:A ring"
    let q211 ← q r"h:A->B"
    let v212 ← ISPECL [q211, q210, q209, q208, q207, q206] NUMBER_FIELD_GALOIS_GROUP_TRANSITIVE
    let q213 ← q r"Q':B->bool"
    let q214 ← q r"(P:B->bool) IN S1"
    let q215 ← q r"P:B->bool"
    let q216 ← q r"p:A->bool"
    let q217 ← q r"s:B->bool"
    let q218 ← q r"l:B ring"
    let q219 ← q r"k:A ring"
    let q220 ← q r"h:A->B"
    let v221 ← ISPECL [q220, q219, q218, q217, q216] NUMBER_FIELD_PRIME_IDEALS_INTERMEDIATE
    let q222 ← q r"P:B->bool"
    let q223 ← q r"!P. P IN S1 ==> ?g. g IN X /\ (c:(B->B)->B->bool) g = P"
    let q224 ← q r"g:B->B"
    let q225 ← q r"Q:B->bool"
    let q226 ← q r"p:A->bool"
    let q227 ← q r"H:(B->B)->bool"
    let q228 ← q r"l:B ring"
    let q229 ← q r"k:A ring"
    let q230 ← q r"h:A->B"
    let v231 ← ISPECL [q230, q229, q228, q227, q226, q225, q224] NUMBER_FIELD_FIXED_FIELD_PRIME_DEGREE_ONE
    let q232 ← q r"g:B->B"
    let q233 ← q r"Q:B->bool"
    let q234 ← q r"p:A->bool"
    let q235 ← q r"H:(B->B)->bool"
    let q236 ← q r"l:B ring"
    let q237 ← q r"k:A ring"
    let q238 ← q r"h:A->B"
    let v239 ← ISPECL [q238, q237, q236, q235, q234, q233, q232] NUMBER_FIELD_FROBENIUS_CONJUGATE_PRIME
    let q240 ← q r"g:B->B"
    let q241 ← q r"!g. g IN group_carrier G
        ==> prime_ideal (ring_of_integers l) (IMAGE g Q) /\
            IMAGE (h:A->B) p SUBSET IMAGE g Q /\
            prime_ideal (ring_of_integers M) ((c:(B->B)->B->bool) g) /\
            ~(c g = {ring_0 l}) /\
            IMAGE h p SUBSET c g /\
            (c g IN S1 <=> g IN X) /\
            (group_carrier(decomposition_group(k,l) h (IMAGE g Q))
             SUBSET H <=> g IN X)"
    let q242 ← q r"p /\ (p ==> q) ==> p /\ q"
    let r243 ← TAUT q242
    let q244 ← q r"FINITE(group_carrier(G:(B->B)group))"
    let q245 ← q r"FINITE(group_carrier(G:(B->B)group)) /\ H SUBSET group_carrier G /\
    FINITE(H:(B->B)->bool)"
    let q246 ← q r"group_mul G = ((o):(B->B)->(B->B)->(B->B)) /\
    group_inv G = (inverse:(B->B)->(B->B)) /\
    group_id G = (I:B->B)"
    let q247 ← q r"c = \g:B->B. IMAGE g Q INTER (s:B->bool)"
    let q248 ← q r"X = {g | g IN group_carrier G /\
             group_conjugation G g (Fr:B->B) IN (H:(B->B)->bool)}"
    let q249 ← q r"S1 = {P | prime_ideal (ring_of_integers M) P /\
              IMAGE (h:A->B) p SUBSET P /\
              residue_degree (ring_of_integers k,ring_of_integers M) h P =
              1}"
    let q250 ← q r"Fr = frobenius_element (k,l) (h:A->B) (ring_of_integers l) Q"
    let q251 ← q r"M = subfield_generated l (s:B->bool)"
    let q252 ← q r"s = fixed_field l (H:(B->B)->bool)"
    let q253 ← q r"G = galois_group(k,l) (h:A->B)"
    let q254 ← q r"k:A ring"
    let q255 ← q r"h:A->B"
    let q256 ← q r"galois_extension(subfield_generated l (fixed_field l H),l) (I:B->B)"
    let q257 ← q r"fixed_field l H:B->bool"
    let q258 ← q r"l:B ring"
    let q259 ← q r"k:A ring"
    let q260 ← q r"h:A->B"
    let v261 ← ISPECL [q260, q259, q258, q257] NUMBER_FIELD_INTERMEDIATE_FIELD
    let q262 ← q r"H:(B->B)->bool"
    let q263 ← q r"l:B ring"
    let q264 ← q r"k:A ring"
    let q265 ← q r"h:A->B"
    let v266 ← ISPECL [q265, q264, q263, q262] GALOIS_GROUP_FIXED_FIELD
    let q267 ← q r"h:A->B"
    let q268 ← q r"l:B ring"
    let q269 ← q r"k:A ring"
    let v270 ← ISPECL [q269, q268, q267] NUMBER_FIELD_TOWER_LAW
    let q271 ← q r"field k /\ ring_homomorphism(k,l) (h:A->B)"
    prove
      r"!(h:A->B) k l H p Q.
          number_field l /\ galois_extension(k,l) h /\
          H subgroup_of galois_group(k,l) h /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
          unramified (ring_of_integers k,ring_of_integers l) h p /\
          prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q
          ==> CARD H *
              CARD {P | prime_ideal
                         (ring_of_integers
                           (subfield_generated l (fixed_field l H))) P /\
                        IMAGE h p SUBSET P /\
                        residue_degree
                         (ring_of_integers k,
                          ring_of_integers
                           (subfield_generated l (fixed_field l H)))
                         h P = 1} =
              CARD {g | g IN group_carrier(galois_group(k,l) h) /\
                        group_conjugation (galois_group(k,l) h) g
                          (frobenius_element (k,l) h (ring_of_integers l) Q)
                        IN H}"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN q271 STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_IMP_FIELD_EXTENSION)) THEN SIMP_TAC [field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN MP_TAC v270 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN MP_TAC v266 THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC v261 THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN q256 ASSUME_TAC THENL [MATCH_MP_TAC GALOIS_EXTENSION_SUBFIELD_GENERATED THEN MAP_EVERY EXISTS_TAC [q255, q254] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ABBREV_TAC q253 THEN ABBREV_TAC q252 THEN ABBREV_TAC q251 THEN ABBREV_TAC q250 THEN ABBREV_TAC q249 THEN ABBREV_TAC q248 THEN ABBREV_TAC q247 THEN SUBGOAL_THEN q246 STRIP_ASSUME_TAC THENL [EXPAND_TAC "G" THEN REWRITE_TAC [GALOIS_GROUP], ALL_TAC] THEN SUBGOAL_THEN q245 STRIP_ASSUME_TAC THENL [SUBGOAL_THEN q244 ASSUME_TAC THENL [EXPAND_TAC "G" THEN ASM_SIMP_TAC [FINITE_GALOIS_GROUP], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r243 THEN CONJ_TAC THENL [ASM_MESON_TAC [SUBGROUP_OF_IMP_SUBSET], ASM_MESON_TAC [FINITE_SUBSET]], ALL_TAC] THEN SUBGOAL_THEN q241 ASSUME_TAC THENL [X_GEN_TAC q240 THEN DISCH_TAC THEN MP_TAC v239 THEN MP_TAC v231 THEN ASM_REWRITE_TAC [] THEN REPEAT (DISCH_THEN STRIP_ASSUME_TAC) THEN EXPAND_TAC "c" THEN MAP_EVERY EXPAND_TAC ["S1", "X"] THEN ASM_REWRITE_TAC [IN_ELIM_THM], ALL_TAC] THEN SUBGOAL_THEN q223 MP_TAC THENL [X_GEN_TAC q222 THEN DISCH_TAC THEN MP_TAC v221 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o ((SPEC q215) o (GEN_REWRITE_RULE id [EXTENSION]))) THEN UNDISCH_TAC q214 THEN EXPAND_TAC "S1" THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN q213 STRIP_ASSUME_TAC) THEN MP_TAC v212 THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC q205 THEN STRIP_TAC THEN SUBGOAL_THEN q204 ASSUME_TAC THENL [EXPAND_TAC "c" THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (MP_TAC o ((SPEC q203) o (checkM (fun th => (do if ← (do let z198 ← (do let z199 ← (pure th); pure (concl z199)); pure (is_forall z198)) then (do let z201 ← (do let z202 ← (pure th); pure (concl z202)); let z200 ← (q r"S1:(B->bool)->bool"); pure (free_in z200 z201)) else pure false))))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (fun z195 => tactic_of do pure (SUBST1_TAC (← SYM (← (do let z196 ← (pure (CONJUNCTS z195)); let z197 ← (pure 5); liftExcept (el z197 z196)))))) THEN FIRST_ASSUM (SUBST1_TAC o (checkM (fun th => (do let z194 ← (q r"(c:(B->B)->B->bool) g = P"); let z193 ← (do let z192 ← (pure th); pure (concl z192)); pure (z193 == z194))))) THEN EXPAND_TAC "S1" THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN DISCH_THEN (X_CHOOSE_TAC q191) THEN SUBGOAL_THEN q190 ASSUME_TAC THENL [EXPAND_TAC "X" THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN q189 ASSUME_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC q188 THEN CONJ_TAC THENL [MP_TAC v187 THEN ASM_SIMP_TAC [], EXPAND_TAC "S1" THEN SET_TAC []], ALL_TAC] THEN SUBGOAL_THEN q182 ASSUME_TAC THENL [REPEAT STRIP_TAC THEN EXPAND_TAC "c" THEN REWRITE_TAC [IMAGE_o] THEN SUBGOAL_THEN q181 ASSUME_TAC THENL [MATCH_MP_TAC GALOIS_GROUP_PERMUTES THEN MAP_EVERY EXISTS_TAC [q180, q179] THEN EXPAND_TAC "G" THEN ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN q178 ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o ((SPEC q177) o (checkM (fun th => (do if ← (do let z172 ← (do let z173 ← (pure th); pure (concl z173)); pure (is_forall z172)) then (do let z175 ← (do let z176 ← (pure th); pure (concl z176)); let z174 ← (q r"S1:(B->bool)->bool"); pure (free_in z174 z175)) else pure false))))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (MP_TAC o ((MATCH_MP PRIME_IDEAL_IMP_SUBSET) o CONJUNCT1)) THEN MP_TAC v171 THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN q169 ASSUME_TAC THENL [EXPAND_TAC "s" THEN REWRITE_TAC [IN_FIXED_FIELD] THEN ASM_MESON_TAC [], ALL_TAC] THEN REWRITE_TAC [EXTENSION, IN_INTER, IN_IMAGE] THEN X_GEN_TAC q168 THEN ASM_CASES_TAC q167 THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MP_TAC o ((SPEC q166) o (checkM (fun th => (do if ← (do let z161 ← (do let z162 ← (pure th); pure (concl z162)); pure (is_forall z161)) then (do let z164 ← (do let z165 ← (pure th); pure (concl z165)); let z163 ← (q r"s:B->bool"); pure (free_in z163 z164)) else pure false))))) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PERMUTES_INJECTIVE)) THEN EQ_TAC THENL [DISCH_THEN (X_CHOOSE_THEN q160 STRIP_ASSUME_TAC) THEN SUBGOAL_THEN q159 (fun th => ASM_MESON_TAC [th]) THEN ASM_MESON_TAC [], DISCH_TAC THEN EXISTS_TAC q158 THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN q157 ASSUME_TAC THENL [REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o ((SPEC q156) o (checkM (fun th => (do if ← (do let z151 ← (do let z152 ← (pure th); pure (concl z152)); pure (is_forall z151)) then (do let z154 ← (do let z155 ← (pure th); pure (concl z155)); let z153 ← (q r"S1:(B->bool)->bool"); pure (free_in z153 z154)) else pure false))))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN FIRST_ASSUM (MP_TAC o ((SPEC q150) o (checkM (fun th => (do if ← (do let z145 ← (do let z146 ← (pure th); pure (concl z146)); pure (is_forall z145)) then (do let z148 ← (do let z149 ← (pure th); pure (concl z149)); let z147 ← (q r"S1:(B->bool)->bool"); pure (free_in z147 z148)) else pure false))))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN MP_TAC v144 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [IMAGE_I] THEN SUBGOAL_THEN q137 SUBST1_TAC THENL [EXPAND_TAC "M" THEN REWRITE_TAC [SUBFIELD_GENERATED], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC q136 THEN EXPAND_TAC "c" THEN SET_TAC [], ASM_MESON_TAC []], ALL_TAC] THEN SUBGOAL_THEN q135 ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN q134 ASSUME_TAC THENL [MP_TAC v133 THEN ANTS_TAC THENL [ASM_MESON_TAC [UNRAMIFIED_IMP_WEAKLY_UNRAMIFIED, weakly_unramified], ALL_TAC] THEN DISCH_THEN (MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC [DECOMPOSITION_GROUP] THEN SIMP_TAC [IN_ELIM_THM], ALL_TAC] THEN TRANS_TAC EQ_TRANS q127 THEN CONJ_TAC THENL [ASM_SIMP_TAC [CARD_CROSS], ALL_TAC] THEN TRANS_TAC EQ_TRANS q126 THEN CONJ_TAC THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_SIMP_TAC [FINITE_CROSS, FORALL_PAIR_THM, IN_CROSS, PAIR_EQ] THEN MAP_EVERY X_GEN_TAC [q125, q124, q123, q122] THEN STRIP_TAC THEN SUBGOAL_THEN q121 SUBST_ALL_TAC THENL [FIRST_X_ASSUM (MP_TAC o (AP_TERM q120)) THEN SUBGOAL_THEN q119 (fun th => ASM_SIMP_TAC [th]) THEN REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS q118 THEN CONJ_TAC THENL [FIRST_X_ASSUM (MATCH_MP_TAC o (checkM (fun th => (do if ← (do if ← (do let z106 ← (do let z107 ← (pure th); pure (concl z107)); pure (is_forall z106)) then (do let z108 ← (do let z109 ← (pure th); pure (concl z109)); canM (fun z110 => (do let z111 ← (pure z110); find_termM (fun z112 => (do let z114 ← (pure z112); let z113 ← (q r"(o):(B->B)->(B->B)->(B->B)"); pure (z113 == z114))) z111)) z108) else pure false) then (do pure !(← (do let z116 ← (do let z117 ← (pure th); pure (concl z117)); let z115 ← (q r"rep:(B->bool)->(B->B)"); pure (free_in z115 z116)))) else pure false)))) THEN ASM_SIMP_TAC [], ASM_SIMP_TAC []], ALL_TAC] THEN REWRITE_TAC [] THEN MP_TAC v105 THEN ASM_SIMP_TAC [] THEN ANTS_TAC THENL [ASM SET_TAC [], SIMP_TAC []], ALL_TAC] THEN AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_IMAGE, EXISTS_PAIR_THM, IN_CROSS] THEN X_GEN_TAC q100 THEN EQ_TAC THENL [REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [q99, q98] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN q97 MP_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN q96 ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN EXPAND_TAC "X" THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN SUBGOAL_THEN q95 SUBST1_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [GROUP_MUL, v94] THEN MATCH_MP_TAC IN_SUBGROUP_CONJUGATION THEN ASM_MESON_TAC [], ALL_TAC] THEN DISCH_TAC THEN SUBGOAL_THEN q93 ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN FIRST_ASSUM (MP_TAC o ((SPEC q92) o (checkM (fun th => (do if ← (do let z87 ← (do let z88 ← (pure th); pure (concl z88)); pure (is_forall z87)) then (do let z90 ← (do let z91 ← (pure th); pure (concl z91)); let z89 ← (q r"S1:(B->bool)->bool"); pure (free_in z89 z90)) else pure false))))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN ABBREV_TAC q86 THEN SUBGOAL_THEN q85 ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN ABBREV_TAC q84 THEN SUBGOAL_THEN q83 STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o ((SPECL [q82, q81]) o (checkM (fun th => (do if ← (do let z71 ← (do let z72 ← (pure th); pure (concl z72)); pure (is_forall z71)) then (do let b ← (do pure (Prod.snd (← (do let z73 ← (do let z74 ← (pure th); pure (concl z74)); pure (strip_forall z73))))); (do if ← (do if ← (do let z75 ← (pure b); pure (is_imp z75)) then (do let z76 ← (do let z77 ← (pure b); liftExcept (rand z77)); pure (is_exists z76)) else pure false) then (do let z79 ← (do let z80 ← (pure b); liftExcept (rand z80)); let z78 ← (q r"H:(B->B)->bool"); pure (free_in z78 z79)) else pure false)) else pure false))))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN q70 STRIP_ASSUME_TAC) THEN SUBGOAL_THEN q69 ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN ABBREV_TAC q68 THEN SUBGOAL_THEN q67 ASSUME_TAC THENL [EXPAND_TAC "kk" THEN ASM_SIMP_TAC [GROUP_MUL, GROUP_INV], ALL_TAC] THEN SUBGOAL_THEN q66 ASSUME_TAC THENL [EXPAND_TAC "kk" THEN REWRITE_TAC [v65, v63], ALL_TAC] THEN SUBGOAL_THEN q61 STRIP_ASSUME_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC GALOIS_GROUP_PERMUTES THEN MAP_EVERY EXISTS_TAC [q60, q59] THEN EXPAND_TAC "G" THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN q58 ASSUME_TAC THENL [FIRST_ASSUM (SUBST1_TAC o (checkM (fun th => (do let z57 ← (q r"(kk:B->B) = inverse (h0:B->B) o (g:B->B) o inverse (r:B->B)"); let z56 ← (do let z55 ← (pure th); pure (concl z55)); pure (z56 == z57))))) THEN REWRITE_TAC [IMAGE_o] THEN SUBGOAL_THEN q54 SUBST1_TAC THENL [REWRITE_TAC [v53] THEN FIRST_ASSUM (MP_TAC o ((MATCH_MP PERMUTES_INVERSES_o) o (checkM (fun th => (do let z52 ← (q r"(r:B->B) permutes ring_carrier l"); let z51 ← (do let z50 ← (pure th); pure (concl z50)); pure (z51 == z52)))))) THEN SIMP_TAC [IMAGE_I], ALL_TAC] THEN FIRST_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z49 ← (q r"IMAGE (h0:B->B) (IMAGE (r:B->B) Q) = IMAGE (g:B->B) Q"); let z48 ← (do let z47 ← (pure th); pure (concl z47)); pure (z48 == z49)))))) THEN REWRITE_TAC [v46] THEN FIRST_ASSUM (MP_TAC o ((MATCH_MP PERMUTES_INVERSES_o) o (checkM (fun th => (do let z45 ← (q r"(h0:B->B) permutes ring_carrier l"); let z44 ← (do let z43 ← (pure th); pure (concl z43)); pure (z44 == z45)))))) THEN SIMP_TAC [IMAGE_I, I_O_ID], ALL_TAC] THEN SUBGOAL_THEN q42 ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o ((SPEC q41) o (checkM (fun th => (do if ← (do let z36 ← (do let z37 ← (pure th); pure (concl z37)); pure (is_forall z36)) then (do let z39 ← (do let z40 ← (pure th); pure (concl z40)); let z38 ← (q r"S1:(B->bool)->bool"); pure (free_in z38 z39)) else pure false))))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (fun z34 => tactic_of do pure (MP_TAC (← (do let z35 ← (pure (CONJUNCTS z34)); liftExcept (last z35))))) THEN REWRITE_TAC [v33] THEN REWRITE_TAC [DECOMPOSITION_GROUP, SUBSET, IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC [v31] THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN MAP_EVERY EXISTS_TAC [q29, q28] THEN REWRITE_TAC [v27, v25] THEN CONJ_TAC THENL [REWRITE_TAC [v23] THEN FIRST_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do if ← (do if ← (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); pure (is_eq z5)) then (do let z10 ← (q r"kk:B->B"); let z9 ← (do let z7 ← (do let z8 ← (pure th); pure (concl z8)); liftExcept (rand z7)); pure (z9 == z10)) else pure false) then (do let z11 ← (do let z12 ← (do let z13 ← (pure th); pure (concl z13)); liftExcept (lhand z12)); pure (is_comb z11)) else pure false) then (do let z14 ← (do let z15 ← (do let z16 ← (pure th); pure (concl z16)); liftExcept (lhand z15)); canM (fun z17 => (do let z20 ← (pure z17); let z19 ← (q r"group_mul G x y:B->B"); let z18 ← (pure []); term_match z18 z19 z20)) z14) else pure false))))) THEN MP_TAC r4 THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [], MATCH_MP_TAC r2 THEN ASM_REWRITE_TAC []])

  let NUMBER_FIELD_DEGREE_ONE_CARD ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"P:A->bool"
    let q2 ← q r"k:A ring"
    let v3 ← ISPECL [q2, q1] NUMBER_FIELD_PRIME_IDEAL_DEGREE_ONE
    let q4 ← q r"P:A->bool"
    let q5 ← q r"(s:(A->bool)->bool) = {} ==> CARD s = 0"
    let r6 ← MESON [CARD_CLAUSES] q5
    let q7 ← q r"ideal_norm (ring_of_integers k) (P:A->bool) = m"
    let q8 ← q r"P = {ring_0(k:A ring)}"
    let q9 ← q r"prime_ideal (ring_of_integers k) (P:A->bool)"
    let q10 ← q r"P:A->bool"
    let q11 ← q r"k:A ring"
    let v12 ← ISPECL [q11, q10] NUMBER_FIELD_PRIME_IDEAL_DEGREE_ONE
    let q13 ← q r"P:A->bool"
    prove
      r"!k:A ring m.
          number_field k
          ==> CARD {P | prime_ideal (ring_of_integers k) P /\
                        ~(P = {ring_0 k}) /\
                        residue_degree (integer_ring,ring_of_integers k)
                          (ring_of_int k) P = 1 /\
                        ideal_norm (ring_of_integers k) P = m} =
              if prime m
              then CARD {P | prime_ideal (ring_of_integers k) P /\
                             ~(P = {ring_0 k}) /\
                             ideal_norm (ring_of_integers k) P = m}
              else 0"
      (REPEAT STRIP_TAC THEN COND_CASES_TAC THENL [AP_TERM_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC q13 THEN MP_TAC v12 THEN ASM_CASES_TAC q9 THEN ASM_CASES_TAC q8 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ASM_CASES_TAC q7 THEN ASM_REWRITE_TAC [], MATCH_MP_TAC r6 THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [NOT_IN_EMPTY, IN_ELIM_THM] THEN X_GEN_TAC q4 THEN STRIP_TAC THEN MP_TAC v3 THEN ASM_REWRITE_TAC []])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_FIXED_FIELD_PRIME_DEGREE_ONE,
           NUMBER_FIELD_FIXED_FIELD_DEGREE_ONE_CARD, NUMBER_FIELD_DEGREE_ONE_CARD }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- frobenius_density.ml phrases from line 559 to 1169                     -/
/- ---------------------------------------------------------------------- -/

structure FrobeniusDensity02 where
  -- @@FIELDS
  NUMBER_FIELD_FIXED_FIELD_FROBENIUS_LOG : thm
  DIRICHLET_SERIES_DIVISOR_INDUCTION : thm
  DIRICHLET_SERIES_CYCLIC_CONJUGATES : thm
  NUMBER_FIELD_NONPRIME_NORM_SERIES : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFrobeniusDensity02 [HolBase] (D : FrobeniusDensityDeps) (BFrobeniusDensity01 : FrobeniusDensity01) :
    ExceptT String IO FrobeniusDensity02 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON, MESON_TAC,
        NUMBER_RULE, REAL_ARITH, REAL_ARITH_TAC, REAL_FIELD, REAL_RING, SET_TAC, .. } := D
  let { ADD_CLAUSES, CARD_CLAUSES, CARD_CONJUGATES_INTO_CYCLIC_GENERATORS,
        CARD_CONJUGATES_IN_TORSION_NSUM, CARD_CYCLIC_SUBGROUP_DIVISION, CARD_EQ_0,
        CARD_RESTRICT_POW_EQ_ID, COND_ID, CONJ_ASSOC, CYCLIC_SUBGROUP_TORSION_SUBGROUP,
        DIRICHLET_SERIES_FINITE_PERTURBATION, DIVIDES_LE, DIVIDES_REFL, DIVIDES_TRANS,
        EQ_TRANS, EXTENSION, FINITE_DIVISORS, FINITE_GROUP_ELEMENT_ORDER_NONZERO,
        FINITE_GROUP_NORMALIZER, FINITE_IMAGE, FINITE_RAMIFIED, FINITE_RESTRICT,
        FINITE_SUBSET, FUN_EQ_THM, GALOIS_GROUP_FIXED_FIELD,
        GALOIS_IMP_FIELD_EXTENSION, GROUP_CARRIER_NONEMPTY,
        GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET, GROUP_NORMALIZER_NONEMPTY,
        IN_ELIM_THM, IN_INSERT, LE_0, LE_REFL, MULT_CLAUSES, MULT_SYM, NOT_IN_EMPTY,
        NSUM_CASES, NSUM_CLAUSES, NSUM_CONST, NSUM_EQ, NSUM_LMUL, NSUM_RESTRICT_SET,
        NSUM_SUBSET_SIMPLE, NSUM_SWAP, .. } := D.core1
  let { NUMBER_FIELD_DEGREE_ONE_PRIMES_LOG,
        NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM,
        NUMBER_FIELD_HOMOMORPHIC_PREIMAGE, NUMBER_FIELD_IDEAL_SUM_BY_NORM,
        NUMBER_FIELD_INTERMEDIATE_FIELD, NUMBER_FIELD_NONPRIME_NORM_SUM_LE,
        NUMBER_FIELD_PRIME_NORM_CARD, NUMBER_FIELD_TOWER_LAW, PRIME_IMP_RING_IDEAL,
        REAL_ABS_INV, REAL_ABS_MUL, REAL_ABS_NUM, REAL_ADD_LDISTRIB, REAL_EQ_IMP_LE,
        REAL_INFSUM_LMUL, REAL_INFSUM_UNIQUE, REAL_LE_DIV, REAL_LE_INV_EQ,
        REAL_LE_LMUL, REAL_LE_TRANS, REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LINV,
        REAL_OF_NUM_ADD, REAL_OF_NUM_EQ, REAL_OF_NUM_LE, REAL_OF_NUM_MUL,
        REAL_OF_NUM_SUM, REAL_POS, REAL_SERIES_FINITE_SUM, REAL_SERIES_POS,
        REAL_SERIES_SUB, REAL_SUMMABLE_LMUL, REAL_SUMMABLE_POS_PARTIAL_BOUND,
        REAL_SUMS_INFSUM, RIGHT_IMP_EXISTS_THM, RING_MONOMORPHISM_IMP_HOMOMORPHISM,
        RPOW_POS_LE, SKOLEM_THM, SUBSET, SUM_ABS, SUM_ADD, SUM_CLAUSES, SUM_EQ_NUMSEG,
        SUM_LE, SUM_RMUL, SUM_SUBSET_SIMPLE, field_extension, num_WF, real_div,
        real_summable, .. } := D.core2
  let { NUMBER_FIELD_DEGREE_ONE_CARD, NUMBER_FIELD_FIXED_FIELD_DEGREE_ONE_CARD, .. } := BFrobeniusDensity01
  -- @@SCOPE END

  let NUMBER_FIELD_FIXED_FIELD_FROBENIUS_LOG ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"&0 <= (x:real) ==> abs x = x")
    let r26 ← REAL_ARITH (← q r"abs(((x:real) + y) - x) = abs y")
    let r27 ← ARITH_RULE (← q r"x + y = x <=> y = 0")
    prove
      r"!(h:A->B) k l H fr.
          number_field l /\ galois_extension(k,l) h /\
          H subgroup_of galois_group(k,l) h /\
          (!p. prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
               unramified (ring_of_integers k,ring_of_integers l) h p
               ==> ?Q. prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q /\
                       fr p = frobenius_element (k,l) h (ring_of_integers l) Q)
          ==> ?C. !s. &1 < s /\ s <= &2
                  ==> real_summable (from 1)
                       (\m. &(if prime m
                              then nsum {p | prime_ideal (ring_of_integers k) p /\
                                             ~(p = {ring_0 k}) /\
                                             unramified
                                              (ring_of_integers k,
                                               ring_of_integers l) h p /\
                                             ideal_norm (ring_of_integers k) p =
                                             m}
                                        (\p. CARD
                                          {g | g IN group_carrier
                                                     (galois_group(k,l) h) /\
                                               group_conjugation
                                                (galois_group(k,l) h) g (fr p)
                                               IN H})
                              else 0) / &m rpow s) /\
                      abs(real_infsum (from 1)
                           (\m. &(if prime m
                                  then nsum {p | prime_ideal
                                                  (ring_of_integers k) p /\
                                                 ~(p = {ring_0 k}) /\
                                                 unramified (ring_of_integers k,
                                                             ring_of_integers l)
                                                  h p /\
                                                 ideal_norm (ring_of_integers k)
                                                  p = m}
                                            (\p. CARD
                                              {g | g IN group_carrier
                                                         (galois_group(k,l) h) /\
                                                   group_conjugation
                                                    (galois_group(k,l) h) g
                                                    (fr p)
                                                   IN H})
                                  else 0) / &m rpow s) +
                          &(CARD H) * log(s - &1)) <= C"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"field k /\ ring_homomorphism(k,l) (h:A->B)") STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_IMP_FIELD_EXTENSION)) THEN SIMP_TAC [field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"H:(B->B)->bool")] GALOIS_GROUP_FIXED_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"fixed_field l H:B->bool")] NUMBER_FIELD_INTERMEDIATE_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ABBREV_TAC (← q r"M = subfield_generated l (fixed_field l (H:(B->B)->bool))") THEN SUBGOAL_THEN (← q r"number_field(k:A ring)") ASSUME_TAC THENL [ASM_MESON_TAC [NUMBER_FIELD_HOMOMORPHIC_PREIMAGE], ALL_TAC] THEN ABBREV_TAC (← q r"nH = \p. CARD {P | prime_ideal (ring_of_integers M) P /\
                         IMAGE (h:A->B) p SUBSET P /\
                         residue_degree (ring_of_integers k,ring_of_integers M)
                           h P = 1}") THEN ABBREV_TAC (← q r"R = {p | prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
               ~(unramified (ring_of_integers k,ring_of_integers l) (h:A->B) p)}") THEN SUBGOAL_THEN (← q r"FINITE(R:(A->bool)->bool)") ASSUME_TAC THENL [EXPAND_TAC "R" THEN MATCH_MP_TAC FINITE_RAMIFIED THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!p. prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
          unramified (ring_of_integers k,ring_of_integers l) h p
          ==> CARD(H:(B->B)->bool) * (nH:(A->bool)->num) p =
              CARD {g | g IN group_carrier (galois_group(k,l) (h:A->B)) /\
                        group_conjugation (galois_group(k,l) h) g (fr p) IN H}") ASSUME_TAC THENL [X_GEN_TAC (← q r"p:A->bool") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"p:A->bool")) o (checkM (fun th => (do if ← (do let z33 ← (do let z34 ← (pure th); pure (concl z34)); pure (is_forall z33)) then (do let z36 ← (do let z37 ← (pure th); pure (concl z37)); let z35 ← (q r"fr:(A->bool)->B->B"); pure (free_in z35 z36)) else pure false))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"Q:B->bool") STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "nH" THEN EXPAND_TAC "M" THEN MATCH_MP_TAC NUMBER_FIELD_FIXED_FIELD_DEGREE_ONE_CARD THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPEC (← q r"M:B ring") NUMBER_FIELD_DEGREE_ONE_PRIMES_LOG) THEN ASM_REWRITE_TAC [NUMBER_FIELD_DEGREE_ONE_CARD] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"C0:real")) THEN SUBGOAL_THEN (← q r"!m. CARD {P | prime_ideal (ring_of_integers(M:B ring)) P /\
                    ~(P = {ring_0 M}) /\
                    residue_degree (integer_ring,ring_of_integers M)
                      (ring_of_int M) P = 1 /\
                    ideal_norm (ring_of_integers M) P = m} =
          if prime m
          then nsum {p | prime_ideal (ring_of_integers k) p /\
                         ~(p = {ring_0 k}) /\
                         ideal_norm (ring_of_integers k) p = m}
                    (nH:(A->bool)->num)
          else 0") (fun th => RULE_ASSUM_TAC (REWRITE_RULE [th])) THENL [X_GEN_TAC (← q r"m:num") THEN ASM_SIMP_TAC [NUMBER_FIELD_DEGREE_ONE_CARD] THEN COND_CASES_TAC THEN REWRITE_TAC [] THEN EXPAND_TAC "nH" THEN MATCH_MP_TAC NUMBER_FIELD_PRIME_NORM_CARD THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!m. CARD(H:(B->B)->bool) *
          (if prime m
           then nsum {p | prime_ideal (ring_of_integers k) p /\
                          ~(p = {ring_0 k}) /\
                          ideal_norm (ring_of_integers k) p = m}
                     (nH:(A->bool)->num)
           else 0) =
          (if prime m
           then nsum {p | prime_ideal (ring_of_integers k) p /\
                          ~(p = {ring_0 k}) /\
                          unramified (ring_of_integers k,ring_of_integers l)
                            (h:A->B) p /\
                          ideal_norm (ring_of_integers k) p = m}
                     (\p. CARD {g | g IN group_carrier(galois_group(k,l) h) /\
                                    group_conjugation (galois_group(k,l) h) g
                                      (fr p) IN H})
           else 0) +
          (if prime m
           then nsum {p | p IN R /\ ideal_norm (ring_of_integers k) p = m}
                     (\p. CARD H * nH p)
           else 0)") (LABEL_TAC "split") THENL [X_GEN_TAC (← q r"m:num") THEN COND_CASES_TAC THENL [ALL_TAC, REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES]] THEN REWRITE_TAC [(← GSYM NSUM_LMUL)] THEN SUBGOAL_THEN (← q r"FINITE {p | prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
                    ideal_norm (ring_of_integers k) (p:A->bool) = m}") ASSUME_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{p | prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
               ideal_norm (ring_of_integers k) (p:A->bool) <= m}") THEN ASM_SIMP_TAC [NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM] THEN SIMP_TAC [SUBSET, IN_ELIM_THM, LE_REFL], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"{p | prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
              ideal_norm (ring_of_integers k) (p:A->bool) = m}"), (← q r"unramified (ring_of_integers k,ring_of_integers l) (h:A->B)"), (← q r"\p. CARD(H:(B->B)->bool) * (nH:(A->bool)->num) p"), (← q r"\p. CARD(H:(B->B)->bool) * (nH:(A->bool)->num) p")] NSUM_CASES) THEN ASM_REWRITE_TAC [COND_ID] THEN DISCH_THEN SUBST1_TAC THEN BINOP_TAC THENL [TRANS_TAC EQ_TRANS (← q r"nsum {p | prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
                    unramified (ring_of_integers k,ring_of_integers l)
                      (h:A->B) p /\
                    ideal_norm (ring_of_integers k) p = m}
               (\p. CARD(H:(B->B)->bool) * (nH:(A->bool)->num) p)") THEN CONJ_TAC THENL [AP_THM_TAC THEN AP_TERM_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM] THEN MESON_TAC [], MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC []], AP_THM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "R" THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM] THEN MESON_TAC []], ALL_TAC] THEN ABBREV_TAC (← q r"B = &(nsum R (\p. CARD(H:(B->B)->bool) * (nH:(A->bool)->num) p)):real") THEN EXISTS_TAC (← q r"(B:real) * &(CARD(IMAGE (ideal_norm (ring_of_integers k))
                       (R:(A->bool)->bool))) +
      &(CARD(H:(B->B)->bool)) * C0") THEN X_GEN_TAC (← q r"s:real") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"s:real")) o (checkM (fun th => (do if ← (do let z28 ← (do let z29 ← (pure th); pure (concl z29)); pure (is_forall z28)) then (do let z31 ← (do let z32 ← (pure th); pure (concl z32)); let z30 ← (q r"C0:real"); pure (free_in z30 z31)) else pure false))))) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"\m. &(CARD(H:(B->B)->bool) *
             (if prime m
              then nsum {p | prime_ideal (ring_of_integers k) p /\
                             ~(p = {ring_0 k}) /\
                             ideal_norm (ring_of_integers k) p = m}
                        (nH:(A->bool)->num)
              else 0)):real"), (← q r"\m. &(if prime m
             then nsum {p | prime_ideal (ring_of_integers k) p /\
                            ~(p = {ring_0 k}) /\
                            unramified (ring_of_integers k,ring_of_integers l)
                              (h:A->B) p /\
                            ideal_norm (ring_of_integers k) p = m}
                       (\p. CARD {g | g IN group_carrier(galois_group(k,l) h) /\
                                      group_conjugation (galois_group(k,l) h) g
                                        (fr p) IN H})
             else 0):real"), (← q r"IMAGE (ideal_norm (ring_of_integers k)) (R:(A->bool)->bool)"), (← q r"B:real"), (← q r"s:real")] DIRICHLET_SERIES_FINITE_PERTURBATION) THEN REWRITE_TAC [] THEN ANTS_TAC THENL [REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL [ASM_SIMP_TAC [FINITE_IMAGE], X_GEN_TAC (← q r"m:num") THEN DISCH_TAC THEN USE_THEN "split" (fun th => REWRITE_TAC [th]) THEN REWRITE_TAC [REAL_OF_NUM_EQ, r27] THEN COND_CASES_TAC THEN REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"{p | p IN R /\ ideal_norm (ring_of_integers k) p = m} =
          {}:(A->bool)->bool") SUBST1_TAC THENL [ASM SET_TAC [], REWRITE_TAC [NSUM_CLAUSES]], X_GEN_TAC (← q r"m:num") THEN USE_THEN "split" (fun th => REWRITE_TAC [th]) THEN REWRITE_TAC [(← GSYM REAL_OF_NUM_ADD), r26, REAL_ABS_NUM] THEN EXPAND_TAC "B" THEN REWRITE_TAC [REAL_OF_NUM_LE] THEN COND_CASES_TAC THEN REWRITE_TAC [LE_0] THEN MATCH_MP_TAC NSUM_SUBSET_SIMPLE THEN ASM_REWRITE_TAC [] THEN SET_TAC [], ASM_REAL_ARITH_TAC, REWRITE_TAC [(← GSYM REAL_OF_NUM_MUL), real_div, (← GSYM REAL_MUL_ASSOC)] THEN MATCH_MP_TAC REAL_SUMMABLE_LMUL THEN ASM_REWRITE_TAC [(← GSYM real_div)]], ALL_TAC] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"real_infsum (from 1)
       (\m. &(CARD(H:(B->B)->bool) *
              (if prime m
               then nsum {p | prime_ideal (ring_of_integers k) p /\
                              ~(p = {ring_0 k}) /\
                              ideal_norm (ring_of_integers k) p = m}
                         (nH:(A->bool)->num)
               else 0)) / &m rpow s) =
      &(CARD H) *
      real_infsum (from 1)
       (\m. &(if prime m
              then nsum {p | prime_ideal (ring_of_integers k) p /\
                             ~(p = {ring_0 k}) /\
                             ideal_norm (ring_of_integers k) p = m}
                        (nH:(A->bool)->num)
              else 0) / &m rpow s)") ASSUME_TAC THENL [REWRITE_TAC [(← GSYM REAL_OF_NUM_MUL), real_div, (← GSYM REAL_MUL_ASSOC)] THEN MATCH_MP_TAC REAL_INFSUM_LMUL THEN ASM_REWRITE_TAC [(← GSYM real_div)], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do if ← (do let z21 ← (do let z22 ← (pure th); pure (concl z22)); let z20 ← (pure "real_le"); pure (is_binary z20 z21)) then (do let z24 ← (do let z25 ← (pure th); pure (concl z25)); let z23 ← (q r"B:real"); pure (free_in z23 z24)) else pure false)))) THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do if ← (do let z15 ← (do let z16 ← (pure th); pure (concl z16)); let z14 ← (pure "real_le"); pure (is_binary z14 z15)) then (do let z18 ← (do let z19 ← (pure th); pure (concl z19)); let z17 ← (q r"log(s - &1)"); pure (free_in z17 z18)) else pure false)))) THEN FIRST_X_ASSUM (SUBST1_TAC o (checkM (fun th => (do if ← (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); pure (is_eq z2)) then (do let z4 ← (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); liftExcept (rand z5)); pure (is_comb z4)) else pure false) then (do let z7 ← (do let z8 ← (do let z9 ← (pure th); pure (concl z9)); liftExcept (rand z8)); canM (fun z10 => (do let z13 ← (pure z10); let z12 ← (q r"&(CARD(H:(B->B)->bool)) * (x:real)"); let z11 ← (pure []); term_match z11 z12 z13)) z7) else pure false)))) THEN ABBREV_TAC (← q r"z = real_infsum (from 1)
       (\m. &(if prime m
              then nsum {p | prime_ideal (ring_of_integers k) p /\
                             ~(p = {ring_0 k}) /\
                             ideal_norm (ring_of_integers k) p = m}
                        (nH:(A->bool)->num)
              else 0) / &m rpow s)") THEN ABBREV_TAC (← q r"y = real_infsum (from 1)
       (\m. &(if prime m
              then nsum {p | prime_ideal (ring_of_integers k) p /\
                             ~(p = {ring_0 k}) /\
                             unramified (ring_of_integers k,ring_of_integers l)
                               (h:A->B) p /\
                             ideal_norm (ring_of_integers k) p = m}
                        (\p. CARD {g | g IN group_carrier(galois_group(k,l) h) /\
                                       group_conjugation (galois_group(k,l) h) g
                                         (fr p) IN H})
              else 0) / &m rpow s)") THEN ABBREV_TAC (← q r"ll = log(s - &1)") THEN ABBREV_TAC (← q r"hh = &(CARD(H:(B->B)->bool)):real") THEN ABBREV_TAC (← q r"tt = &(CARD(IMAGE (ideal_norm (ring_of_integers k))
                        (R:(A->bool)->bool))):real") THEN REPEAT DISCH_TAC THEN SUBGOAL_THEN (← q r"&0 <= (hh:real)") ASSUME_TAC THENL [EXPAND_TAC "hh" THEN REWRITE_TAC [REAL_POS], ALL_TAC] THEN SUBGOAL_THEN (← q r"abs(hh * (z:real) + hh * ll) <= hh * C0") MP_TAC THENL [REWRITE_TAC [(← GSYM REAL_ADD_LDISTRIB), REAL_ABS_MUL] THEN ASM_SIMP_TAC [r1] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC [], UNDISCH_TAC (← q r"abs((hh:real) * z - y) <= B * tt") THEN REAL_ARITH_TAC])

  let DIRICHLET_SERIES_DIVISOR_INDUCTION ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r6 ← REAL_RING (← q r"a:real = b ==> x * i = (x + a) * i - b * i")
    prove
      r"!n (w:num->num->real) (c:num->num).
          ~(n = 0) /\
          (!d. d divides n
               ==> ?C. !s. &1 < s /\ s <= &2
                       ==> real_summable (from 1)
                            (\m. sum {e | e divides d} (\e. w e m) /
                                 &m rpow s) /\
                           abs(real_infsum (from 1)
                                (\m. sum {e | e divides d} (\e. w e m) /
                                     &m rpow s) +
                               &(nsum {e | e divides d} c) * log(s - &1))
                           <= C)
          ==> !d. d divides n
                  ==> ?C. !s. &1 < s /\ s <= &2
                          ==> real_summable (from 1) (\m. w d m / &m rpow s) /\
                              abs(real_infsum (from 1)
                                   (\m. w d m / &m rpow s) +
                                  &(c d) * log(s - &1)) <= C"
      (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hyp")) THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC (← q r"d:num") THEN DISCH_THEN (LABEL_TAC "IH") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"~(d = 0)") ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC (← q r"(d:num) divides n") THEN ASM_REWRITE_TAC [(← ExceptT.mk (NUMBER_RULE (← q r"0 divides (n:num) <=> n = 0")))], ALL_TAC] THEN ABBREV_TAC (← q r"E = {e | e divides d /\ ~(e = (d:num))}") THEN SUBGOAL_THEN (← q r"FINITE(E:num->bool) /\ {e | e divides d} = d INSERT E /\ ~(d IN E) /\
      (!e. e IN E ==> e < d /\ e divides n)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "E" THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{e | e divides (d:num)}") THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_DIVISORS THEN ASM_REWRITE_TAC [], SET_TAC []], REWRITE_TAC [EXTENSION, IN_INSERT, IN_ELIM_THM] THEN X_GEN_TAC (← q r"e:num") THEN ASM_CASES_TAC (← q r"e:num = d") THEN ASM_REWRITE_TAC [DIVIDES_REFL], REWRITE_TAC [IN_ELIM_THM], REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"e:num") THEN STRIP_TAC THEN CONJ_TAC THENL [MP_TAC (← SPECL [(← q r"e:num"), (← q r"d:num")] DIVIDES_LE) THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC, MATCH_MP_TAC DIVIDES_TRANS THEN EXISTS_TAC (← q r"d:num") THEN ASM_REWRITE_TAC []]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!e. e IN (E:num->bool)
          ==> ?C. !s. &1 < s /\ s <= &2
                      ==> real_summable (from 1) (\m. w e m / &m rpow s) /\
                          abs(real_infsum (from 1) (\m. w e m / &m rpow s) +
                              &((c:num->num) e) * log(s - &1)) <= C") MP_TAC THENL [X_GEN_TAC (← q r"e:num") THEN DISCH_TAC THEN REMOVE_THEN "IH" (MP_TAC o (SPEC (← q r"e:num"))) THEN ASM_SIMP_TAC [], DISCH_THEN ((X_CHOOSE_TAC (← q r"Cf:num->real")) o (REWRITE_RULE [RIGHT_IMP_EXISTS_THM, SKOLEM_THM]))] THEN REMOVE_THEN "hyp" (MP_TAC o (SPEC (← q r"d:num"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"Cd:real")) THEN EXISTS_TAC (← q r"Cd + sum E (Cf:num->real)") THEN X_GEN_TAC (← q r"s:real") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"s:real")) o (checkM (fun th => (do if ← (do let z12 ← (do let z13 ← (pure th); pure (concl z13)); pure (is_forall z12)) then (do let z15 ← (do let z16 ← (pure th); pure (concl z16)); let z14 ← (q r"Cd:real"); pure (free_in z14 z15)) else pure false))))) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ABBREV_TAC (← q r"L = log(s - &1)") THEN ABBREV_TAC (← q r"A = \e. real_infsum (from 1)
               (\m. (w:num->num->real) e m / &m rpow s)") THEN SUBGOAL_THEN (← q r"!e. e IN E
          ==> ((\m. w e m / &m rpow s) real_sums A e) (from 1) /\
              abs(A e + &((c:num->num) e) * L) <= (Cf:num->real) e") ASSUME_TAC THENL [X_GEN_TAC (← q r"e:num") THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o ((SPEC (← q r"s:real")) o ((← do let c := (← ASSUME (← q r"(e:num) IN E")); pure (fun th => MP th c)) o ((SPEC (← q r"e:num")) o (checkM (fun th => (do if ← (do let z7 ← (do let z8 ← (pure th); pure (concl z8)); pure (is_forall z7)) then (do let z10 ← (do let z11 ← (pure th); pure (concl z11)); let z9 ← (q r"Cf:num->real"); pure (free_in z9 z10)) else pure false))))))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "A" THEN SIMP_TAC [REAL_SUMS_INFSUM], ALL_TAC] THEN ABBREV_TAC (← q r"Ad = real_infsum (from 1)
            (\m. sum (d INSERT E) (\e. (w:num->num->real) e m) /
                 &m rpow s)") THEN SUBGOAL_THEN (← q r"((\m. (w:num->num->real) d m / &m rpow s) real_sums
       (Ad - sum (E:num->bool) A)) (from 1)") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"(\m. w d m / &m rpow s) =
        (\m. sum (d INSERT E) (\e. (w:num->num->real) e m) /
             &m rpow s -
             sum E (\e. w e m / &m rpow s))") SUBST1_TAC THENL [REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"m:num") THEN ASM_SIMP_TAC [SUM_CLAUSES, real_div, SUM_RMUL] THEN MATCH_MP_TAC r6 THEN REWRITE_TAC [], MATCH_MP_TAC REAL_SERIES_SUB THEN CONJ_TAC THENL [EXPAND_TAC "Ad" THEN ASM_REWRITE_TAC [REAL_SUMS_INFSUM], MATCH_MP_TAC REAL_SERIES_FINITE_SUM THEN ASM_SIMP_TAC []]], ALL_TAC] THEN CONJ_TAC THENL [ASM_MESON_TAC [real_summable], ALL_TAC] THEN FIRST_ASSUM (SUBST1_TAC o (MATCH_MP REAL_INFSUM_UNIQUE)) THEN SUBGOAL_THEN (← q r"&(nsum (d INSERT E) c) = &(c d) + sum E (\e. &((c:num->num) e))") (fun th => RULE_ASSUM_TAC (REWRITE_RULE [th])) THENL [ASM_SIMP_TAC [NSUM_CLAUSES, (← GSYM REAL_OF_NUM_ADD), REAL_OF_NUM_SUM], ALL_TAC] THEN SUBGOAL_THEN (← q r"abs(sum E (\e. A e + &((c:num->num) e) * L)) <= sum E (Cf:num->real)") MP_TAC THENL [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"sum E (\e. abs(A e + &((c:num->num) e) * L))") THEN ASM_SIMP_TAC [SUM_ABS] THEN MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC [], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); let z1 ← (q r"Cd:real"); pure (free_in z1 z2)) then (do pure !(← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); pure (is_forall z4)))) else pure false)))) THEN ASM_SIMP_TAC [SUM_ADD, SUM_RMUL] THEN REAL_ARITH_TAC)

  let DIRICHLET_SERIES_CYCLIC_CONJUGATES ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_FIELD (← q r"x * y = z * u /\ ~(y = &0) /\ ~(z = &0) ==> x / z = inv y * u")
    prove
      r"!G (a:A) (S:num->B->bool) fr.
          FINITE(group_carrier G) /\ a IN group_carrier G /\
          (!m. FINITE(S m)) /\ (!m p. p IN S m ==> fr p IN group_carrier G) /\
          (!H. H subgroup_of G /\
               H SUBSET group_carrier(subgroup_generated G {a})
               ==> ?C. !s. &1 < s /\ s <= &2
                           ==> real_summable (from 1)
                                (\m. &(nsum (S m)
                                        (\p. CARD {g | g IN group_carrier G /\
                                                       group_conjugation G g
                                                        (fr p) IN H})) /
                                     &m rpow s) /\
                               abs(real_infsum (from 1)
                                    (\m. &(nsum (S m)
                                            (\p. CARD
                                                  {g | g IN group_carrier G /\
                                                       group_conjugation G g
                                                        (fr p) IN H})) /
                                         &m rpow s) +
                                   &(CARD H) * log(s - &1)) <= C)
          ==> ?C. !s. &1 < s /\ s <= &2
                      ==> real_summable (from 1)
                           (\m. &(CARD {p | p IN S m /\
                                            ?g. g IN group_carrier G /\
                                                group_carrier
                                                 (subgroup_generated G {fr p}) =
                                                IMAGE (group_conjugation G g)
                                                 (group_carrier
                                                  (subgroup_generated G {a}))}) /
                                &m rpow s) /\
                          abs(real_infsum (from 1)
                               (\m. &(CARD {p | p IN S m /\
                                                ?g. g IN group_carrier G /\
                                                    group_carrier
                                                     (subgroup_generated G
                                                       {fr p}) =
                                                    IMAGE
                                                     (group_conjugation G g)
                                                     (group_carrier
                                                      (subgroup_generated G
                                                        {a}))}) /
                                    &m rpow s) +
                              &(CARD {t | t IN group_carrier G /\
                                          ?g. g IN group_carrier G /\
                                              group_carrier
                                               (subgroup_generated G {t}) =
                                              IMAGE (group_conjugation G g)
                                               (group_carrier
                                                (subgroup_generated G {a}))}) /
                              &(CARD(group_carrier G)) * log(s - &1)) <= C"
      (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hyp"))))) THEN ABBREV_TAC (← q r"C = group_carrier(subgroup_generated G {a:A})") THEN ABBREV_TAC (← q r"n = group_element_order G (a:A)") THEN SUBGOAL_THEN (← q r"~(n = 0)") ASSUME_TAC THENL [EXPAND_TAC "n" THEN MATCH_MP_TAC FINITE_GROUP_ELEMENT_ORDER_NONZERO THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(C:A->bool) SUBSET group_carrier G /\ FINITE C") STRIP_ASSUME_TAC THENL [EXPAND_TAC "C" THEN REWRITE_TAC [GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET] THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"group_carrier(G:A group)") THEN ASM_REWRITE_TAC [GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"n:num"), (← q r"\e m. &(nsum ((S:num->B->bool) m)
                (\p. CARD {g | g IN group_carrier G /\
                               group_conjugation G g ((fr:B->A) p) IN
                               {y | y IN C /\
                                    group_element_order G y = e}})):real"), (← q r"\e. CARD {y | y IN (C:A->bool) /\ group_element_order G y = e}")] DIRICHLET_SERIES_DIVISOR_INDUCTION) THEN REWRITE_TAC [(← ASSUME (← q r"~(n = 0)"))] THEN ANTS_TAC THENL [X_GEN_TAC (← q r"d:num") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"~(d = 0)") ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC (← q r"(d:num) divides n") THEN ASM_REWRITE_TAC [(← ExceptT.mk (NUMBER_RULE (← q r"0 divides (n:num) <=> n = 0")))], ALL_TAC] THEN ABBREV_TAC (← q r"H = {y | y IN C /\ group_pow G y d = group_id (G:A group)}") THEN SUBGOAL_THEN (← q r"!m. sum {e | e divides d}
                (\e. &(nsum ((S:num->B->bool) m)
                        (\p. CARD {g | g IN group_carrier G /\
                                       group_conjugation G g ((fr:B->A) p) IN
                                       {y | y IN C /\
                                            group_element_order G y = e}}))) =
            &(nsum (S m) (\p. CARD {g | g IN group_carrier G /\
                                        group_conjugation G g (fr p) IN H}))") (fun th => REWRITE_TAC [th]) THENL [X_GEN_TAC (← q r"m:num") THEN ASM_SIMP_TAC [(← GSYM REAL_OF_NUM_SUM), FINITE_DIVISORS, REAL_OF_NUM_EQ] THEN wPart lhand (lhand o rand) NSUM_SWAP THEN ASM_SIMP_TAC [FINITE_DIVISORS] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC (← q r"p:B") THEN DISCH_TAC THEN EXPAND_TAC "H" THEN REWRITE_TAC [] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_CONJUGATES_IN_TORSION_NSUM THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"nsum {e | e divides d}
             (\e. CARD {y | y IN (C:A->bool) /\ group_element_order G y = e}) =
        CARD(H:A->bool)") SUBST1_TAC THENL [EXPAND_TAC "H" THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_RESTRICT_POW_EQ_ID THEN ASM_REWRITE_TAC [], ALL_TAC] THEN REMOVE_THEN "hyp" MATCH_MP_TAC THEN EXPAND_TAC "H" THEN CONJ_TAC THENL [ALL_TAC, SET_TAC []] THEN EXPAND_TAC "C" THEN MATCH_MP_TAC CYCLIC_SUBGROUP_TORSION_SUBGROUP THEN ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"n:num"))) THEN REWRITE_TAC [DIVIDES_REFL] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"C1:real")) THEN ABBREV_TAC (← q r"NN = CARD(group_normalizer G (C:A->bool))") THEN SUBGOAL_THEN (← q r"~(NN = 0)") ASSUME_TAC THENL [EXPAND_TAC "NN" THEN ASM_SIMP_TAC [CARD_EQ_0, FINITE_GROUP_NORMALIZER, GROUP_NORMALIZER_NONEMPTY], ALL_TAC] THEN SUBGOAL_THEN (← q r"!m. nsum ((S:num->B->bool) m)
               (\p. CARD {g | g IN group_carrier G /\
                              group_conjugation G g ((fr:B->A) p) IN
                              {y | y IN C /\ group_element_order G y = n}}) =
          NN * CARD {p | p IN S m /\
                         ?g. g IN group_carrier G /\
                             group_carrier(subgroup_generated G {fr p}) =
                             IMAGE (group_conjugation G g) C}") (fun th => tactic_of do pure (FIRST_X_ASSUM (MP_TAC o ((REWRITE_RULE [th]) o (checkM (fun th' => (do let z3 ← (do let z4 ← (pure th'); pure (concl z4)); let z2 ← (q r"C1:real"); pure (free_in z2 z3)))))))) THENL [X_GEN_TAC (← q r"m:num") THEN TRANS_TAC EQ_TRANS (← q r"nsum ((S:num->B->bool) m)
             (\p. if ?g. g IN group_carrier G /\
                         group_carrier(subgroup_generated G {(fr:B->A) p}) =
                         IMAGE (group_conjugation G g) C
                  then NN else 0)") THEN CONJ_TAC THENL [MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC (← q r"p:B") THEN DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["NN", "C", "n"] THEN REWRITE_TAC [] THEN MATCH_MP_TAC CARD_CONJUGATES_INTO_CYCLIC_GENERATORS THEN ASM_MESON_TAC [], ASM_SIMP_TAC [(← GSYM NSUM_RESTRICT_SET), NSUM_CONST, FINITE_RESTRICT] THEN MATCH_ACCEPT_TAC MULT_SYM], DISCH_TAC] THEN SUBGOAL_THEN (← q r"&(CARD {t | t IN group_carrier G /\
                  ?g. g IN group_carrier G /\
                      group_carrier(subgroup_generated G {t}) =
                      IMAGE (group_conjugation G g) C}) /
      &(CARD(group_carrier G)) =
      inv(&NN) * &(CARD {y | y IN (C:A->bool) /\ group_element_order G y = n})") SUBST1_TAC THENL [MP_TAC (← ISPECL [(← q r"G:A group"), (← q r"a:A")] CARD_CYCLIC_SUBGROUP_DIVISION) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC [REAL_OF_NUM_MUL, REAL_OF_NUM_EQ] THEN ASM_SIMP_TAC [CARD_EQ_0, GROUP_CARRIER_NONEMPTY], ALL_TAC] THEN EXISTS_TAC (← q r"inv(&NN) * C1") THEN X_GEN_TAC (← q r"s:real") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"s:real"))) THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(\m. &(CARD {p | p IN (S:num->B->bool) m /\
                       ?g. g IN group_carrier G /\
                           group_carrier(subgroup_generated G {(fr:B->A) p}) =
                           IMAGE (group_conjugation G g) C}) / &m rpow s) =
      (\m. inv(&NN) *
           &(NN * CARD {p | p IN S m /\
                            ?g. g IN group_carrier G /\
                                group_carrier(subgroup_generated G {fr p}) =
                                IMAGE (group_conjugation G g) C}) / &m rpow s)") SUBST1_TAC THENL [ABS_TAC THEN REWRITE_TAC [(← GSYM REAL_OF_NUM_MUL), real_div, REAL_MUL_ASSOC] THEN ASM_SIMP_TAC [REAL_MUL_LINV, REAL_OF_NUM_EQ, REAL_MUL_LID], ALL_TAC] THEN STRIP_TAC THEN ASM_SIMP_TAC [REAL_SUMMABLE_LMUL, REAL_INFSUM_LMUL] THEN REWRITE_TAC [(← GSYM REAL_MUL_ASSOC), (← GSYM REAL_ADD_LDISTRIB)] THEN REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_INV, REAL_ABS_NUM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC [REAL_LE_INV_EQ, REAL_POS])

  let NUMBER_FIELD_NONPRIME_NORM_SERIES ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"from 1"
    let q2 ← q r"f:num->real"
    let q3 ← q r"(&2:real) * &(extension_degree (subfield_generated k {ring_0 k},k)
                 (I:A->A))"
    let q4 ← q r"1"
    let q5 ← q r"f:num->real"
    let v6 ← ISPECL [q5, q4, q3] REAL_SUMMABLE_POS_PARTIAL_BOUND
    let q7 ← q r"(s:(A->bool)->bool) = {} ==> 0 = CARD s"
    let r8 ← MESON [CARD_CLAUSES] q7
    let q9 ← q r"m:num"
    let v10 ← GSYM CONJ_ASSOC
    let q11 ← q r"N:num"
    let q12 ← q r"\m. inv(&m rpow s)"
    let q13 ← q r"{q | q IN S /\ ~prime(ideal_norm (ring_of_integers k) (q:A->bool))}"
    let q14 ← q r"k:A ring"
    let v15 ← ISPECL [q14, q13, q12, q11] NUMBER_FIELD_IDEAL_SUM_BY_NORM
    let q16 ← q r"{q | prime_ideal (ring_of_integers k) q /\ ~(q = {ring_0 k}) /\
               ideal_norm (ring_of_integers k) (q:A->bool) <= N}"
    let q17 ← q r"sum {q | q IN S /\ ~prime(ideal_norm (ring_of_integers k) q) /\
               ideal_norm (ring_of_integers k) (q:A->bool) <= N}
          (\q. inv(&(ideal_norm (ring_of_integers k) q) rpow s))"
    let q18 ← q r"sum {q | prime_ideal (ring_of_integers k) q /\ ~(q = {ring_0 k}) /\
               ~prime(ideal_norm (ring_of_integers k) q) /\
               ideal_norm (ring_of_integers k) (q:A->bool) <= N}
          (\q. inv(&(ideal_norm (ring_of_integers k) q) rpow s))"
    let q19 ← q r"N:num"
    let q20 ← q r"!N. sum(1..N) f <=
        &2 * &(extension_degree (subfield_generated k {ring_0 k},k) (I:A->A))"
    let q21 ← q r"!m. &0 <= (f:num->real) m"
    let q22 ← q r"f = \m. &(if prime m then 0
              else CARD {p | p IN S /\
                             ideal_norm (ring_of_integers k) (p:A->bool) =
                             m}) / &m rpow s"
    prove
      r"!k:A ring S s.
          number_field k /\
          (!p. p IN S
               ==> prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})) /\
          &1 < s
          ==> real_summable (from 1)
               (\m. &(if prime m then 0
                      else CARD {p | p IN S /\
                                     ideal_norm (ring_of_integers k) p = m}) /
                    &m rpow s) /\
              &0 <= real_infsum (from 1)
                     (\m. &(if prime m then 0
                            else CARD {p | p IN S /\
                                           ideal_norm (ring_of_integers k) p =
                                           m}) /
                          &m rpow s) /\
              real_infsum (from 1)
               (\m. &(if prime m then 0
                      else CARD {p | p IN S /\
                                     ideal_norm (ring_of_integers k) p = m}) /
                    &m rpow s)
              <= &2 * &(extension_degree (subfield_generated k {ring_0 k},k) I)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN ABBREV_TAC q22 THEN SUBGOAL_THEN q21 ASSUME_TAC THENL [GEN_TAC THEN EXPAND_TAC "f" THEN SIMP_TAC [REAL_LE_DIV, REAL_POS, RPOW_POS_LE], ALL_TAC] THEN SUBGOAL_THEN q20 ASSUME_TAC THENL [X_GEN_TAC q19 THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC q18 THEN CONJ_TAC THENL [ALL_TAC, MATCH_MP_TAC NUMBER_FIELD_NONPRIME_NORM_SUM_LE THEN ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC] THEN TRANS_TAC REAL_LE_TRANS q17 THEN CONJ_TAC THENL [ALL_TAC, MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN SIMP_TAC [REAL_LE_INV_EQ, RPOW_POS_LE, REAL_POS] THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC q16 THEN ASM_SIMP_TAC [NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM] THEN SET_TAC [], REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC []]] THEN MP_TAC v15 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [PRIME_IMP_RING_IDEAL], ALL_TAC] THEN REWRITE_TAC [IN_ELIM_THM, v10] THEN DISCH_THEN (SUBST1_TAC o CONJUNCT2) THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC q9 THEN STRIP_TAC THEN EXPAND_TAC "f" THEN REWRITE_TAC [real_div] THEN AP_THM_TAC THEN AP_TERM_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THENL [REWRITE_TAC [REAL_OF_NUM_EQ] THEN MATCH_MP_TAC r8 THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM, NOT_IN_EMPTY] THEN ASM_MESON_TAC [], AP_TERM_TAC THEN AP_TERM_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC []], ALL_TAC] THEN MP_TAC v6 THEN ASM_SIMP_TAC [] THEN STRIP_TAC THEN MATCH_MP_TAC REAL_SERIES_POS THEN EXISTS_TAC q2 THEN EXISTS_TAC q1 THEN ASM_REWRITE_TAC [REAL_SUMS_INFSUM])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_FIXED_FIELD_FROBENIUS_LOG, DIRICHLET_SERIES_DIVISOR_INDUCTION,
           DIRICHLET_SERIES_CYCLIC_CONJUGATES, NUMBER_FIELD_NONPRIME_NORM_SERIES }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- frobenius_density.ml phrases from line 1261 to 1608                    -/
/- ---------------------------------------------------------------------- -/

structure FrobeniusDensity03 where
  -- @@FIELDS
  NUMBER_FIELD_NONPRIME_NORM_LOG : thm
  NUMBER_FIELD_FROBENIUS_DENSITY_LOG : thm
  NUMBER_FIELD_FROBENIUS_DENSITY : thm
  NUMBER_FIELD_FROBENIUS_INFINITE : thm
  NUMBER_FIELD_TOTALLY_SPLIT_DENSITY : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFrobeniusDensity03 [HolBase] (D : FrobeniusDensityDeps) (BFrobeniusDensity02 : FrobeniusDensity02) :
    ExceptT String IO FrobeniusDensity03 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON, MESON_TAC, REAL_ARITH, SET_RULE, .. } := D
  let { CARD_CLAUSES, CARD_EQ_0, CARD_SING, CARRIER_SUBGROUP_GENERATED_SUBGROUP,
        DECOMPOSITION_GROUP, DE_MORGAN_THM, EMPTY_GSPEC, EXTENSION, FINITE_EMPTY,
        FINITE_GALOIS_GROUP, FINITE_RESTRICT, FINITE_SUBSET, GALOIS_EXTENSION_EQ_CARD,
        GALOIS_GROUP, GALOIS_IMP_FIELD_EXTENSION, GROUP_CARRIER_NONEMPTY,
        GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET, GROUP_CONJUGATION_BY_ID,
        GROUP_CONJUGATION_EQ_ID, GROUP_ID, HAS_DIRICHLET_DENSITY_INFINITE,
        HAS_DIRICHLET_DENSITY_LOG, IMAGE_CLAUSES, IMP_CONJ, IN_ELIM_THM, IN_SING,
        LE_REFL, MEMBER_NOT_EMPTY, NOT_IN_EMPTY, NSUM_CLAUSES,
        NUMBER_FIELD_DECOMPOSITION_GROUP_FROBENIUS, .. } := D.core1
  let { NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM, NUMBER_FIELD_FROBENIUS_ELEMENT,
        NUMBER_FIELD_GALOIS_SPLITTING_TYPES, NUMBER_FIELD_HOMOMORPHIC_PREIMAGE,
        NUMBER_FIELD_PRIME_IDEALS_ABOVE, NUMBER_FIELD_TOWER_LAW,
        NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED, PRIME_IMP_RING_IDEAL,
        REAL_ADD_LID, REAL_ADD_RID, REAL_DIV_EQ_0, REAL_INFSUM_ADD, REAL_MUL_LZERO,
        REAL_OF_NUM_EQ, REAL_SUMMABLE_ADD, RIGHT_EXISTS_IMP_THM,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, SING_SUBSET, SKOLEM_THM,
        SUBGROUP_GENERATED_INC, SUBSET, TRIVIAL_SUBGROUP_OF,
        UNRAMIFIED_IMP_WEAKLY_UNRAMIFIED, field_extension, real_div, totally_split,
        weakly_unramified, .. } := D.core2
  let { DIRICHLET_SERIES_CYCLIC_CONJUGATES, NUMBER_FIELD_FIXED_FIELD_FROBENIUS_LOG,
        NUMBER_FIELD_NONPRIME_NORM_SERIES, .. } := BFrobeniusDensity02
  -- @@SCOPE END

  let NUMBER_FIELD_NONPRIME_NORM_LOG ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"abs(x + l) <= c /\ &0 <= y /\ y <= d
    ==> abs(((x:real) + y) + l) <= c + d")
    prove
      r"!k:A ring S c.
          number_field k /\
          (!p. p IN S
               ==> prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})) /\
          (?C. !s. &1 < s /\ s <= &2
                   ==> real_summable (from 1)
                        (\m. &(if prime m
                               then CARD {p | p IN S /\
                                              ideal_norm (ring_of_integers k) p =
                                              m}
                               else 0) / &m rpow s) /\
                       abs(real_infsum (from 1)
                            (\m. &(if prime m
                                   then CARD {p | p IN S /\
                                                  ideal_norm
                                                   (ring_of_integers k) p = m}
                                   else 0) / &m rpow s) +
                           c * log(s - &1)) <= C)
          ==> ?C. !s. &1 < s /\ s <= &2
                      ==> real_summable (from 1)
                           (\m. &(CARD {p | p IN S /\
                                            ideal_norm (ring_of_integers k) p =
                                            m}) / &m rpow s) /\
                          abs(real_infsum (from 1)
                               (\m. &(CARD {p | p IN S /\
                                                ideal_norm (ring_of_integers k)
                                                 p = m}) / &m rpow s) +
                              c * log(s - &1)) <= C"
      (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC (← q r"C:real")))) THEN EXISTS_TAC (← q r"(C:real) + &2 * &(extension_degree (subfield_generated k {ring_0 k},k)
                                         (I:A->A))") THEN X_GEN_TAC (← q r"s:real") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"s:real"))) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"S:(A->bool)->bool"), (← q r"s:real")] NUMBER_FIELD_NONPRIME_NORM_SERIES) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(\m. &(CARD {p | p IN S /\ ideal_norm (ring_of_integers k) p = m}) /
           &m rpow s) =
      (\m. &(if prime m
             then CARD {p | p IN S /\ ideal_norm (ring_of_integers k) p = m}
             else 0) / &m rpow s +
           &(if prime m then 0
             else CARD {p | p IN S /\
                            ideal_norm (ring_of_integers (k:A ring)) p = m}) /
           &m rpow s)") SUBST1_TAC THENL [ABS_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [real_div, REAL_MUL_LZERO, REAL_ADD_RID, REAL_ADD_LID], ALL_TAC] THEN ASM_SIMP_TAC [REAL_SUMMABLE_ADD, REAL_INFSUM_ADD] THEN MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_FROBENIUS_DENSITY_LOG ← prove
    r"!(h:A->B) k l a.
        number_field l /\ galois_extension(k,l) h /\
        a IN group_carrier(galois_group(k,l) h)
        ==> ?C. !s. &1 < s /\ s <= &2
                ==> real_summable (from 1)
                     (\m. &(CARD {p | p IN
                             {p | prime_ideal (ring_of_integers k) p /\
                                  ~(p = {ring_0 k}) /\
                                  unramified (ring_of_integers k,
                                              ring_of_integers l) h p /\
                                  ?Q g. prime_ideal (ring_of_integers l) Q /\
                                        IMAGE h p SUBSET Q /\
                                        g IN group_carrier
                                              (galois_group(k,l) h) /\
                                        group_carrier
                                         (subgroup_generated
                                          (galois_group(k,l) h)
                                          {frobenius_element (k,l) h
                                            (ring_of_integers l) Q}) =
                                        IMAGE (group_conjugation
                                                (galois_group(k,l) h) g)
                                         (group_carrier
                                          (subgroup_generated
                                           (galois_group(k,l) h) {a}))} /\
                             ideal_norm (ring_of_integers k) p = m}) /
                          &m rpow s) /\
                    abs(real_infsum (from 1)
                         (\m. &(CARD {p | p IN
                                 {p | prime_ideal (ring_of_integers k) p /\
                                      ~(p = {ring_0 k}) /\
                                      unramified (ring_of_integers k,
                                                  ring_of_integers l) h p /\
                                      ?Q g. prime_ideal
                                             (ring_of_integers l) Q /\
                                            IMAGE h p SUBSET Q /\
                                            g IN group_carrier
                                                  (galois_group(k,l) h) /\
                                            group_carrier
                                             (subgroup_generated
                                              (galois_group(k,l) h)
                                              {frobenius_element (k,l) h
                                                (ring_of_integers l) Q}) =
                                            IMAGE (group_conjugation
                                                    (galois_group(k,l) h) g)
                                             (group_carrier
                                              (subgroup_generated
                                               (galois_group(k,l) h)
                                               {a}))} /\
                                 ideal_norm (ring_of_integers k) p = m}) /
                              &m rpow s) +
                        &(CARD {t | t IN group_carrier(galois_group(k,l) h) /\
                                    ?g. g IN group_carrier
                                              (galois_group(k,l) h) /\
                                        group_carrier
                                         (subgroup_generated
                                          (galois_group(k,l) h) {t}) =
                                        IMAGE (group_conjugation
                                                (galois_group(k,l) h) g)
                                         (group_carrier
                                          (subgroup_generated
                                           (galois_group(k,l) h)
                                           {a}))}) /
                        &(CARD(group_carrier(galois_group(k,l) h))) *
                        log(s - &1)) <= C"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"field k /\ ring_homomorphism(k,l) (h:A->B)") STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_IMP_FIELD_EXTENSION)) THEN SIMP_TAC [field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN SUBGOAL_THEN (← q r"number_field(k:A ring)") ASSUME_TAC THENL [ASM_MESON_TAC [NUMBER_FIELD_HOMOMORPHIC_PREIMAGE], ALL_TAC] THEN ABBREV_TAC (← q r"G = galois_group(k,l) (h:A->B)") THEN SUBGOAL_THEN (← q r"FINITE(group_carrier(G:(B->B)group))") ASSUME_TAC THENL [EXPAND_TAC "G" THEN ASM_SIMP_TAC [FINITE_GALOIS_GROUP], ALL_TAC] THEN ABBREV_TAC (← q r"C = group_carrier(subgroup_generated G {a:B->B})") THEN ABBREV_TAC (← q r"FS = {p | prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
              unramified (ring_of_integers k,ring_of_integers l) (h:A->B) p /\
              ?Q g. prime_ideal (ring_of_integers l) Q /\
                    IMAGE h p SUBSET Q /\ g IN group_carrier G /\
                    group_carrier(subgroup_generated G
                     {frobenius_element (k,l) h (ring_of_integers l) Q}) =
                    IMAGE (group_conjugation G g) C}") THEN SUBGOAL_THEN (← q r"?fr. !p. prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
             unramified (ring_of_integers k,ring_of_integers l) (h:A->B) p
             ==> (?Q. prime_ideal (ring_of_integers l) Q /\
                      IMAGE h p SUBSET Q /\
                      fr p =
                      frobenius_element (k,l) h (ring_of_integers l) Q) /\
                 (p IN FS <=>
                  ?g. g IN group_carrier G /\
                      group_carrier(subgroup_generated G {fr p}) =
                      IMAGE (group_conjugation G g) C)") (X_CHOOSE_THEN (← q r"fr:(A->bool)->B->B") (LABEL_TAC "fr")) THENL [REWRITE_TAC [(← GSYM SKOLEM_THM), RIGHT_EXISTS_IMP_THM] THEN X_GEN_TAC (← q r"p:A->bool") THEN STRIP_TAC THEN EXPAND_TAC "FS" THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN ASM_CASES_TAC (← q r"?Q g. prime_ideal (ring_of_integers l) Q /\
            IMAGE (h:A->B) p SUBSET Q /\ g IN group_carrier G /\
            group_carrier(subgroup_generated G
             {frobenius_element (k,l) h (ring_of_integers l) Q}) =
            IMAGE (group_conjugation G g) C") THEN ASM_REWRITE_TAC [] THENL [FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"Q:B->bool") (X_CHOOSE_THEN (← q r"g:B->B") STRIP_ASSUME_TAC)) THEN EXISTS_TAC (← q r"frobenius_element (k,l) (h:A->B) (ring_of_integers l) Q") THEN CONJ_TAC THENL [EXISTS_TAC (← q r"Q:B->bool"), EXISTS_TAC (← q r"g:B->B")] THEN ASM_REWRITE_TAC [], MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_PRIME_IDEALS_ABOVE) THEN ASM_REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY), IN_ELIM_THM] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"Q:B->bool") STRIP_ASSUME_TAC) o CONJUNCT2) THEN EXISTS_TAC (← q r"frobenius_element (k,l) (h:A->B) (ring_of_integers l) Q") THEN CONJ_TAC THENL [EXISTS_TAC (← q r"Q:B->bool") THEN ASM_REWRITE_TAC [], ASM_MESON_TAC []]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!p. prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        unramified (ring_of_integers k,ring_of_integers l) (h:A->B) p
        ==> (fr:(A->bool)->B->B) p IN group_carrier G") (LABEL_TAC "frG") THENL [X_GEN_TAC (← q r"p:A->bool") THEN STRIP_TAC THEN USE_THEN "fr" (MP_TAC o (SPEC (← q r"p:A->bool"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"Q:B->bool") STRIP_ASSUME_TAC) o CONJUNCT1) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_FROBENIUS_ELEMENT) THEN ANTS_TAC THENL [ASM_MESON_TAC [UNRAMIFIED_IMP_WEAKLY_UNRAMIFIED, weakly_unramified], ALL_TAC] THEN DISCH_THEN (MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC [DECOMPOSITION_GROUP] THEN SIMP_TAC [IN_ELIM_THM], ALL_TAC] THEN MATCH_MP_TAC NUMBER_FIELD_NONPRIME_NORM_LOG THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [EXPAND_TAC "FS" THEN SIMP_TAC [IN_ELIM_THM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"G:(B->B)group"), (← q r"a:B->B"), (← q r"\m. if prime m
         then {p | prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
                   unramified (ring_of_integers k,ring_of_integers l)
                              (h:A->B) p /\
                   ideal_norm (ring_of_integers k) p = m}
         else {}"), (← q r"fr:(A->bool)->B->B")] DIRICHLET_SERIES_CYCLIC_CONJUGATES) THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"!b s (f:(A->bool)->num). nsum (if b then s else {}) f =
                             if b then nsum s f else 0") (fun th => REWRITE_TAC [th]) THENL [REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [NSUM_CLAUSES], ALL_TAC] THEN ANTS_TAC THENL [REPEAT CONJ_TAC THENL [X_GEN_TAC (← q r"m:num") THEN COND_CASES_TAC THEN REWRITE_TAC [FINITE_EMPTY] THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{P | prime_ideal (ring_of_integers k) P /\
                       ~(P = {ring_0(k:A ring)}) /\
                       ideal_norm (ring_of_integers k) P <= m}") THEN ASM_SIMP_TAC [NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN MESON_TAC [LE_REFL], MAP_EVERY X_GEN_TAC [(← q r"m:num"), (← q r"p:A->bool")] THEN COND_CASES_TAC THEN REWRITE_TAC [NOT_IN_EMPTY, IN_ELIM_THM] THEN STRIP_TAC THEN REMOVE_THEN "frG" MATCH_MP_TAC THEN ASM_REWRITE_TAC [], X_GEN_TAC (← q r"H:(B->B)->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"H:(B->B)->bool"), (← q r"fr:(A->bool)->B->B")] NUMBER_FIELD_FIXED_FIELD_FROBENIUS_LOG) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC (← q r"p:A->bool") THEN STRIP_TAC THEN USE_THEN "fr" (MP_TAC o (SPEC (← q r"p:A->bool"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], SIMP_TAC []]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!m. CARD {p | p IN (if prime m
                        then {p | prime_ideal (ring_of_integers k) p /\
                                  ~(p = {ring_0 k}) /\
                                  unramified (ring_of_integers k,
                                              ring_of_integers l)
                                             (h:A->B) p /\
                                  ideal_norm (ring_of_integers k) p = m}
                        else {}) /\
                  ?g. g IN group_carrier G /\
                      group_carrier(subgroup_generated G
                       {(fr:(A->bool)->B->B) p}) =
                      IMAGE (group_conjugation G g) C} =
        if prime m
        then CARD {p | p IN FS /\ ideal_norm (ring_of_integers k) p = m}
        else 0") (fun th => REWRITE_TAC [th]) THEN X_GEN_TAC (← q r"m:num") THEN COND_CASES_TAC THEN REWRITE_TAC [NOT_IN_EMPTY, EMPTY_GSPEC, CARD_CLAUSES] THEN AP_TERM_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"p:A->bool") THEN REWRITE_TAC [IN_ELIM_THM] THEN USE_THEN "fr" (MP_TAC o (SPEC (← q r"p:A->bool"))) THEN EXPAND_TAC "FS" THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_CASES_TAC (← q r"prime_ideal (ring_of_integers k) (p:A->bool)") THEN ASM_CASES_TAC (← q r"p = {ring_0(k:A ring)}") THEN ASM_CASES_TAC (← q r"unramified (ring_of_integers k,ring_of_integers l) (h:A->B) p") THEN ASM_REWRITE_TAC [] THEN MESON_TAC [])

  let NUMBER_FIELD_FROBENIUS_DENSITY ← prove
    r"!(h:A->B) k l a.
        number_field l /\ galois_extension(k,l) h /\
        a IN group_carrier(galois_group(k,l) h)
        ==> has_dirichlet_density k
             {p | prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
                  unramified (ring_of_integers k,ring_of_integers l) h p /\
                  ?Q g. prime_ideal (ring_of_integers l) Q /\
                        IMAGE h p SUBSET Q /\
                        g IN group_carrier(galois_group(k,l) h) /\
                        group_carrier
                         (subgroup_generated (galois_group(k,l) h)
                          {frobenius_element (k,l) h (ring_of_integers l) Q}) =
                        IMAGE (group_conjugation (galois_group(k,l) h) g)
                         (group_carrier
                          (subgroup_generated (galois_group(k,l) h) {a}))}
             (&(CARD {t | t IN group_carrier(galois_group(k,l) h) /\
                          ?g. g IN group_carrier(galois_group(k,l) h) /\
                              group_carrier
                               (subgroup_generated (galois_group(k,l) h)
                                {t}) =
                              IMAGE (group_conjugation (galois_group(k,l) h) g)
                               (group_carrier
                                (subgroup_generated (galois_group(k,l) h)
                                 {a}))}) /
              &(CARD(group_carrier(galois_group(k,l) h))))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC HAS_DIRICHLET_DENSITY_LOG THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"a:B->B")] NUMBER_FIELD_FROBENIUS_DENSITY_LOG) THEN ASM_MESON_TAC [GALOIS_IMP_FIELD_EXTENSION, field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM])

  let NUMBER_FIELD_FROBENIUS_INFINITE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(!x. x IN s ==> f x = x) ==> IMAGE (f:B->B) s = s")
    prove
      r"!(h:A->B) k l a.
          number_field l /\ galois_extension(k,l) h /\
          a IN group_carrier(galois_group(k,l) h)
          ==> INFINITE
               {p | prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
                    unramified (ring_of_integers k,ring_of_integers l) h p /\
                    ?Q g. prime_ideal (ring_of_integers l) Q /\
                          IMAGE h p SUBSET Q /\
                          g IN group_carrier(galois_group(k,l) h) /\
                          group_carrier
                           (subgroup_generated (galois_group(k,l) h)
                            {frobenius_element (k,l) h (ring_of_integers l) Q}) =
                          IMAGE (group_conjugation (galois_group(k,l) h) g)
                           (group_carrier
                            (subgroup_generated (galois_group(k,l) h) {a}))}"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"field k /\ ring_homomorphism(k,l) (h:A->B)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [GALOIS_IMP_FIELD_EXTENSION, field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"a:B->B")] NUMBER_FIELD_FROBENIUS_DENSITY) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MATCH_MP_TAC o (MATCH_MP (← ONCE_REWRITE_RULE [IMP_CONJ] HAS_DIRICHLET_DENSITY_INFINITE))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN ABBREV_TAC (← q r"G = galois_group(k,l) (h:A->B)") THEN SUBGOAL_THEN (← q r"FINITE(group_carrier(G:(B->B)group))") ASSUME_TAC THENL [EXPAND_TAC "G" THEN ASM_SIMP_TAC [FINITE_GALOIS_GROUP], ALL_TAC] THEN REWRITE_TAC [REAL_DIV_EQ_0, REAL_OF_NUM_EQ, DE_MORGAN_THM] THEN ASM_SIMP_TAC [CARD_EQ_0, FINITE_RESTRICT, GROUP_CARRIER_NONEMPTY] THEN REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY), IN_ELIM_THM] THEN EXISTS_TAC (← q r"a:B->B") THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"group_id G:B->B") THEN REWRITE_TAC [GROUP_ID] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC r1 THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC GROUP_CONJUGATION_BY_ID THEN ASM_MESON_TAC [GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET, SUBSET])

  let NUMBER_FIELD_TOTALLY_SPLIT_DENSITY ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"t:B->B"
    let q2 ← q r"{t | t IN group_carrier G /\
           ?g. g IN group_carrier G /\
               group_carrier(subgroup_generated G {t}) =
               IMAGE (group_conjugation G g) {I:B->B}} = {I}"
    let q3 ← q r"Q0:B->bool"
    let q4 ← q r"p:A->bool"
    let q5 ← q r"l:B ring"
    let q6 ← q r"k:A ring"
    let q7 ← q r"h:A->B"
    let v8 ← ISPECL [q7, q6, q5, q4, q3] NUMBER_FIELD_DECOMPOSITION_GROUP_FROBENIUS
    let q9 ← q r"Q0:B->bool"
    let q10 ← q r"p:A->bool"
    let q11 ← q r"l:B ring"
    let q12 ← q r"k:A ring"
    let q13 ← q r"h:A->B"
    let v14 ← ISPECL [q13, q12, q11, q10, q9] NUMBER_FIELD_GALOIS_SPLITTING_TYPES
    let q15 ← q r"I:B->B"
    let q16 ← q r"Q0:B->bool"
    let q17 ← q r"totally_split (ring_of_integers k,ring_of_integers l) (h:A->B) p"
    let q18 ← q r"p:A->bool"
    let q19 ← q r"h:A->B"
    let q20 ← q r"l:B ring"
    let q21 ← q r"k:A ring"
    let v22 ← ISPECL [q21, q20, q19, q18] NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED
    let q23 ← q r"unramified (ring_of_integers k,ring_of_integers l) (h:A->B) p"
    let q24 ← q r"Q:B->bool"
    let q25 ← q r"p:A->bool"
    let q26 ← q r"l:B ring"
    let q27 ← q r"k:A ring"
    let q28 ← q r"h:A->B"
    let v29 ← ISPECL [q28, q27, q26, q25, q24] NUMBER_FIELD_DECOMPOSITION_GROUP_FROBENIUS
    let q30 ← q r"Q:B->bool"
    let q31 ← q r"p:A->bool"
    let q32 ← q r"l:B ring"
    let q33 ← q r"k:A ring"
    let q34 ← q r"h:A->B"
    let v35 ← ISPECL [q34, q33, q32, q31, q30] NUMBER_FIELD_GALOIS_SPLITTING_TYPES
    let q36 ← q r"g:B->B"
    let q37 ← q r"Q:B->bool"
    let q38 ← q r"Q0:B->bool"
    let v39 ← GSYM MEMBER_NOT_EMPTY
    let q40 ← q r"p:A->bool"
    let q41 ← q r"h:A->B"
    let q42 ← q r"l:B ring"
    let q43 ← q r"k:A ring"
    let v44 ← ISPECL [q43, q42, q41, q40] NUMBER_FIELD_PRIME_IDEALS_ABOVE
    let q45 ← q r"p = {ring_0(k:A ring)}"
    let q46 ← q r"prime_ideal (ring_of_integers k) (p:A->bool)"
    let q47 ← q r"p:A->bool"
    let q48 ← q r"!S1 S2 d1 d2. S1 = S2 /\ d1 = d2
                  ==> has_dirichlet_density (k:A ring) S1 d1
                      ==> has_dirichlet_density k S2 d2"
    let r49 ← MESON [] q48
    let q50 ← q r"(I:B->B) IN group_carrier G"
    let v51 ← ASSUME q50
    let q52 ← q r"t:B->B"
    let q53 ← q r"{t:B->B}"
    let q54 ← q r"G:(B->B)group"
    let v55 ← ISPECL [q54, q53, q52] SUBGROUP_GENERATED_INC
    let q56 ← q r"t:B->B"
    let q57 ← q r"!t. t IN group_carrier G
        ==> (group_carrier(subgroup_generated G {t}) = {I:B->B} <=> t = I)"
    let q58 ← q r"!g. g IN group_carrier G
        ==> IMAGE (group_conjugation G g) {I:B->B} = {I}"
    let q59 ← q r"group_carrier(subgroup_generated G {I:B->B}) = {I}"
    let q60 ← q r"(I:B->B) IN group_carrier G"
    let q61 ← q r"group_id G = (I:B->B)"
    let q62 ← q r"G = galois_group(k,l) (h:A->B)"
    let q63 ← q r"I:B->B"
    let q64 ← q r"l:B ring"
    let q65 ← q r"k:A ring"
    let q66 ← q r"h:A->B"
    let v67 ← ISPECL [q66, q65, q64, q63] NUMBER_FIELD_FROBENIUS_DENSITY
    let q68 ← q r"CARD(group_carrier(galois_group(k,l) (h:A->B))) = extension_degree(k,l) h"
    let q69 ← q r"h:A->B"
    let q70 ← q r"l:B ring"
    let q71 ← q r"k:A ring"
    let v72 ← ISPECL [q71, q70, q69] NUMBER_FIELD_TOWER_LAW
    let q73 ← q r"field k /\ ring_homomorphism(k,l) (h:A->B)"
    prove
      r"!(h:A->B) k l.
          number_field l /\ galois_extension(k,l) h
          ==> has_dirichlet_density k
               {p | prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
                    totally_split (ring_of_integers k,ring_of_integers l) h p}
               (&1 / &(extension_degree(k,l) h))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN q73 STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [GALOIS_IMP_FIELD_EXTENSION, field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN MP_TAC v72 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN SUBGOAL_THEN q68 ASSUME_TAC THENL [ASM_MESON_TAC [GALOIS_EXTENSION_EQ_CARD], ALL_TAC] THEN MP_TAC v67 THEN ABBREV_TAC q62 THEN SUBGOAL_THEN q61 ASSUME_TAC THENL [EXPAND_TAC "G" THEN REWRITE_TAC [GALOIS_GROUP], ALL_TAC] THEN SUBGOAL_THEN q60 ASSUME_TAC THENL [ASM_MESON_TAC [GROUP_ID], ALL_TAC] THEN SUBGOAL_THEN q59 ASSUME_TAC THENL [ASM_MESON_TAC [CARRIER_SUBGROUP_GENERATED_SUBGROUP, TRIVIAL_SUBGROUP_OF], ALL_TAC] THEN SUBGOAL_THEN q58 ASSUME_TAC THENL [REWRITE_TAC [IMAGE_CLAUSES] THEN ASM_MESON_TAC [GROUP_CONJUGATION_EQ_ID, GROUP_ID], ALL_TAC] THEN SUBGOAL_THEN q57 ASSUME_TAC THENL [X_GEN_TAC q56 THEN DISCH_TAC THEN EQ_TAC THENL [DISCH_TAC THEN MP_TAC v55 THEN ASM_REWRITE_TAC [SING_SUBSET, IN_SING], DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC []], ALL_TAC] THEN ASM_SIMP_TAC [v51] THEN MATCH_MP_TAC r49 THEN CONJ_TAC THENL [GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC q47 THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_CASES_TAC q46 THEN ASM_REWRITE_TAC [] THEN ASM_CASES_TAC q45 THEN ASM_REWRITE_TAC [] THEN MP_TAC v44 THEN ASM_REWRITE_TAC [v39, IN_ELIM_THM] THEN DISCH_THEN ((X_CHOOSE_THEN q38 STRIP_ASSUME_TAC) o CONJUNCT2) THEN EQ_TAC THENL [DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN q37 (X_CHOOSE_THEN q36 STRIP_ASSUME_TAC))) THEN MP_TAC v35 THEN MP_TAC v29 THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [ASM_MESON_TAC [UNRAMIFIED_IMP_WEAKLY_UNRAMIFIED, weakly_unramified], ALL_TAC] THEN DISCH_THEN (SUBST1_TAC o (SYM o CONJUNCT1)) THEN ASM_SIMP_TAC [], DISCH_TAC THEN SUBGOAL_THEN q23 ASSUME_TAC THENL [MP_TAC v22 THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN DISCH_THEN SUBST1_TAC THEN UNDISCH_TAC q17 THEN REWRITE_TAC [totally_split, weakly_unramified] THEN MESON_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN MAP_EVERY EXISTS_TAC [q16, q15] THEN ASM_SIMP_TAC [] THEN MP_TAC v14 THEN MP_TAC v8 THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [ASM_MESON_TAC [UNRAMIFIED_IMP_WEAKLY_UNRAMIFIED, weakly_unramified], ALL_TAC] THEN DISCH_THEN (SUBST1_TAC o CONJUNCT1) THEN ASM_SIMP_TAC []], SUBGOAL_THEN q2 SUBST1_TAC THENL [GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC q1 THEN REWRITE_TAC [IN_ELIM_THM, IN_SING] THEN ASM_MESON_TAC [], REWRITE_TAC [CARD_SING]]])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_NONPRIME_NORM_LOG, NUMBER_FIELD_FROBENIUS_DENSITY_LOG,
           NUMBER_FIELD_FROBENIUS_DENSITY, NUMBER_FIELD_FROBENIUS_INFINITE,
           NUMBER_FIELD_TOTALLY_SPLIT_DENSITY }
  -- @@RETURN END

end HolANT.FrobeniusDensity
