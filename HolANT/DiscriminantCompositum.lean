/- ========================================================================= -/
/- ANT: Composita of number fields with coprime discriminants              -/
/- ========================================================================= -/
/- File: HolANT/DiscriminantCompositum.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/discriminant_compositum.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antdiscriminantcompositumdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/integer.ml, Library/isum.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/frag.ml, Library/grouptheory.ml, Library/symmetric_group.ml, Library/galois.ml, ANT/integral.ml, ANT/algmisc.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/discriminant.ml, ANT/prime_split.ml, ANT/trace_form.ml, ANT/finite_field_trace.ml, ANT/ramification.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/classgroup.ml, ANT/relative_split.ml, ANT/power_basis.ml, ANT/relative_degree.ml, ANT/splitting_types.ml, Library/ring_groups.ml, Library/finite_fields.ml, ANT/decomposition.ml, ANT/nf_valuation.ml, ANT/nf_decomposition.ml, ANT/decomposition_field.ml, ANT/integrality.ml, ANT/dedekind_kummer.ml, ANT/split_primes.ml, Library/modmul_group.ml, ANT/cyclotomic_poly.ml, ANT/cyclotomic_field.ml, ANT/cyclotomic_integers.ml, Library/cyclotomic.ml, ANT/cyclotomic_galois.ml, ANT/cyclotomic_subfields.ml, ANT/linear_forms.ml, ANT/classgroup_group.ml, ANT/quadratic.ml, ANT/fingen_group.ml, Multivariate/misc.ml, Multivariate/metric.ml, Multivariate/homology.ml, Multivariate/vectors.ml, Multivariate/determinants.ml, Multivariate/topology.ml, Multivariate/convex.ml, Multivariate/paths.ml, Multivariate/polytope.ml, Multivariate/degree.ml, Multivariate/derivatives.ml, Multivariate/integration.ml, Multivariate/measure.ml, Multivariate/complex_algebra.ml, Multivariate/complexes.ml, Multivariate/canal.ml, Multivariate/transcendentals.ml, Multivariate/realanalysis.ml, Multivariate/moretop.ml, Multivariate/cauchy.ml, Multivariate/complex_ring.ml, Multivariate/complex_field.ml, ANT/complex_embeddings.ml, ANT/infinite_places.ml, ANT/minkowski_theory.ml, ANT/inertia_generators.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.DiscriminantCompositum fills them).

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
import HolLibrary.Frag
import HolLibrary.GroupTheory
import HolLibrary.SymmetricGroup
import HolLibrary.Galois
import HolANT.Integral
import HolANT.Algmisc
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
import HolANT.PrimeSplit
import HolANT.TraceForm
import HolANT.FiniteFieldTrace
import HolANT.Ramification
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.Classgroup
import HolANT.RelativeSplit
import HolANT.PowerBasis
import HolANT.RelativeDegree
import HolANT.SplittingTypes
import HolLibrary.RingGroups
import HolLibrary.FiniteFields
import HolANT.Decomposition
import HolANT.NfValuation
import HolANT.NfDecomposition
import HolANT.DecompositionField
import HolANT.Integrality
import HolANT.DedekindKummer
import HolANT.SplitPrimes
import HolLibrary.ModmulGroup
import HolANT.CyclotomicPoly
import HolANT.CyclotomicField
import HolANT.CyclotomicIntegers
import HolLibrary.Cyclotomic
import HolANT.CyclotomicGalois
import HolANT.CyclotomicSubfields
import HolANT.LinearForms
import HolANT.ClassgroupGroup
import HolANT.Quadratic
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
import HolANT.InfinitePlaces
import HolANT.MinkowskiTheory
import HolANT.InertiaGenerators

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.Integral
open HolANT.Algmisc
open HolANT.Zlattice
open HolANT.Numfield
open HolANT.IdealArith
open HolANT.Dedekind
open HolANT.DedekindStruct
open HolANT.IdealNorm
open HolANT.RingOfIntegers
open HolANT.NormIndex
open HolANT.Discriminant
open HolANT.PrimeSplit
open HolANT.TraceForm
open HolANT.FiniteFieldTrace
open HolANT.Ramification
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.Classgroup
open HolANT.RelativeSplit
open HolANT.PowerBasis
open HolANT.RelativeDegree
open HolANT.SplittingTypes
open HolANT.Decomposition
open HolANT.NfValuation
open HolANT.NfDecomposition
open HolANT.DecompositionField
open HolANT.Integrality
open HolANT.DedekindKummer
open HolANT.SplitPrimes
open HolANT.CyclotomicPoly
open HolANT.CyclotomicField
open HolANT.CyclotomicIntegers
open HolANT.CyclotomicGalois
open HolANT.CyclotomicSubfields
open HolANT.LinearForms
open HolANT.ClassgroupGroup
open HolANT.Quadratic
open HolANT.FingenGroup
open HolANT.ComplexEmbeddings
open HolANT.InfinitePlaces
open HolANT.MinkowskiTheory
open HolANT.InertiaGenerators

namespace HolANT.DiscriminantCompositum

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH
   ALGEBRA_TRACE_NORM_IN_CARRIER ALGEBRA_TRACE_PRODUCT_BASIS BASIS_COORDINATES
   BASIS_COORDINATES_UNIQUE CARD_IMAGE_LE CARD_NUMSEG_LT DE_MORGAN_THM DIVISION
   EQ_MULT_LCANCEL EQ_MULT_RCANCEL EQ_TRANS ETA_AX EXISTS_IN_GSPEC
   EXISTS_UNIQUE_THM EXTENSIONAL_EQ EXTENSION_DEGREE_LE_INDEPENDENT_BOUND
   EXTENSION_DEGREE_REFL EXTENSION_DEGREE_SUBFIELD_TOWER
   FIELD_EXTENSION_SUBFIELD_GENERATED FIELD_EXTENSION_SUBFIELD_GENERATED_SUBSET
   FIELD_SUBFIELD_GENERATED FINITE_IMAGE FINITE_IMP_ALGEBRAIC_EXTENSION
   FINITE_NUMSEG_LT FORALL_IN_IMAGE FREE_BASIS_EXTENSION_DEGREE
   FREE_BASIS_INDEPENDENT FREE_BASIS_IN_CARRIER FREE_BASIS_SPANNING_DEGREE
   FUN_EQ_THM GALOIS_COMPOSITUM_DEGREE GALOIS_EXTENSION_GENERATED_CONJUGATES
   GALOIS_GROUP_I HAS_SIZE_INDEX HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS IMAGE_I
   IMAGE_UNION INSERT_SUBSET INTEGER_RING INTEGRAL_CLOSURE_SUBRING
   INTEGRAL_ELEMENT_HOMOMORPHIC_IMAGE INTEGRAL_ELEMENT_MONOMORPHIC_PREIMAGE
   INTER_SUBSET INT_COPRIME_BEZOUT INT_COPRIME_PRIME INT_DIVIDES_RPOW INT_PRIME
   INT_PRIME_DIVPOW IN_ELIM_THM IN_IMAGE IN_INSERT IN_INTER IN_SUBFIELD_0
   IN_SUBFIELD_1 IN_SUBFIELD_ADD IN_SUBFIELD_INV IN_SUBFIELD_MUL IN_SUBFIELD_NEG
   IN_SUBFIELD_SUM IN_SUBRING_INT IN_SUBRING_MUL IN_SUBRING_SUM IN_UNION
   IN_UNIONS IN_UNIV I_THM LE_1 LE_ANTISYM LE_MULT_LCANCEL LT MOD_LT_EQ
   MULT_ASSOC MULT_CLAUSES MULT_SYM NUMBER_FIELD_ALGEBRAIC
   NUMBER_FIELD_DEGREE_POS NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD
   NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS NUMBER_FIELD_GALOIS_CLOSURE_Q
   NUMBER_FIELD_GALOIS_UNRAMIFIED_MONO NUMBER_FIELD_IMP_FIELD
   NUMBER_FIELD_NORMAL_CLOSURE_SPLITTING_TYPES
   NUMBER_FIELD_RAMIFIED_DISCRIMINANT NUMBER_FIELD_SUBFIELD_DEGREE_POS
   NUMBER_FIELD_SUBFIELD_GENERATED NUMBER_FIELD_SUBFIELD_HOMOMORPHIC_IMAGE
   NUMBER_FIELD_SUBFIELD_UNRAMIFIED_DISCRIMINANT NUMBER_FIELD_TOWER_LAW
   NUMBER_FIELD_UNRAMIFIED_RATIONAL PRIME_INT_DIVPROD_EQ PRIME_SUBFIELD_MINIMAL
   PRIME_SUBFIELD_SUBFIELD_GENERATED RDIV_LT_EQ RIGHT_IMP_EXISTS_THM : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (RING_0_IN_SUBFIELD_GENERATED RING_ADD_RDISTRIB
   RING_CARRIER_SUBFIELD_GENERATED_SUBSET RING_CHAR_SUBFIELD_GENERATED RING_DET
   RING_DET_CRAMER_SUBRING RING_DET_EQ RING_DET_KRONECKER_MOD_DIV
   RING_DET_SUBRING RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED
   RING_HOMOMORPHISM_FROM_SUBFIELD_GENERATED
   RING_HOMOMORPHISM_INTEGER_RING_OF_INT RING_HOMOMORPHISM_IN_CARRIER
   RING_HOMOMORPHISM_MUL RING_HOMOMORPHISM_RING_OF_INT
   RING_HOMOMORPHISM_SUBFIELD_INCLUSION RING_HOMOMORPHISM_SUM
   RING_INDEPENDENT_IMP_SUBSET RING_INDEPENDENT_LE_SPAN RING_INV_0
   RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_MUL RING_MUL_ASSOC RING_MUL_LID
   RING_MUL_LZERO RING_MUL_RID RING_MUL_SYM RING_OF_INT RING_OF_INTEGERS
   RING_OF_INTEGERS_CARRIER RING_OF_INTEGERS_FREE
   RING_OF_INTEGERS_FREE_BASIS_FIELD RING_OF_INTEGERS_PRIME_SUBFIELD_PRIME_IDEAL
   RING_OF_INTEGERS_SUBFIELD_GENERATED RING_OF_INTEGERS_SUBRING
   RING_OF_INTEGERS_SUBSET RING_OF_INT_1 RING_OF_INT_ADD RING_OF_INT_EQ_0_CHAR_0
   RING_OF_INT_EQ_CHAR_0 RING_OF_INT_IN_RING_OF_INTEGERS
   RING_OF_INT_IN_SUBFIELD_GENERATED RING_OF_INT_MUL RING_OF_INT_POW
   RING_OF_INT_SUBFIELD_GENERATED RING_POW_2 RING_POW_SUBFIELD_GENERATED
   RING_SPAN_INC RING_SPAN_MUL RING_SPAN_SUM RING_SUM RING_SUM_ADD
   RING_SUM_CLOSED RING_SUM_EQ RING_SUM_EQ_0 RING_SUM_LMUL RING_SUM_MOD_DIV
   RING_SUM_PRODUCT_INDEX RING_SUM_RING_OF_INTEGERS RING_SUM_RMUL
   RING_SUM_SUBFIELD_GENERATED RING_SUM_SWAP SEPARABLE_EXTENSION_CHAR0
   SING_SUBSET SKOLEM_THM SUBFIELD_GENERATED
   SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED SUBFIELD_GENERATED_IDEMPOT
   SUBFIELD_GENERATED_IDEMPOT_GEN SUBFIELD_GENERATED_INC_GEN
   SUBFIELD_GENERATED_MINIMAL SUBFIELD_GENERATED_MONO
   SUBFIELD_GENERATED_RESTRICT SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC
   SUBFIELD_GENERATED_SUBSET_EQ SUBFIELD_GENERATED_UNION SUBFIELD_OF_FIELD_INV
   SUBFIELD_SUBFIELD_GENERATED SUBRING_GENERATED_INC SUBRING_GENERATED_MINIMAL
   SUBRING_SUBRING_GENERATED SUBSET SUBSET_ANTISYM
   SUBSET_CARRIER_SUBFIELD_GENERATED SUBSET_TRANS UNION_COMM UNION_OVER_INTER
   UNION_SUBSET algebraic_extension basis_discriminant field_extension
   free_basis number_field o_THM ring_homomorphism_extensions subring_of : thm)
  deriving Inhabited

/-- What discriminant_compositum.ml uses from Session besides theorems. -/
structure DiscriminantCompositumDeps where
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
/- discriminant_compositum.ml phrases from line 120 to 700                -/
/- ---------------------------------------------------------------------- -/

structure DiscriminantCompositum01 where
  -- @@FIELDS
  NUMBER_FIELD_SUBFIELD_INTEGRAL_BASIS : thm
  NUMBER_FIELD_SUBFIELD_INTEGRAL_COORDINATES : thm
  NUMBER_FIELD_COMPOSITUM_PRODUCT_SPAN : thm
  NUMBER_FIELD_COMPOSITUM_PRODUCT_BASIS : thm
  NUMBER_FIELD_COMPOSITUM_DEGREE_LE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDiscriminantCompositum01 [HolBase] (D : DiscriminantCompositumDeps) :
    ExceptT String IO DiscriminantCompositum01 := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, RING_RULE, SET_RULE,
        SET_TAC, .. } := D
  let { BASIS_COORDINATES, BASIS_COORDINATES_UNIQUE, CARD_IMAGE_LE, CARD_NUMSEG_LT,
        EQ_TRANS, EXTENSION_DEGREE_LE_INDEPENDENT_BOUND,
        FIELD_EXTENSION_SUBFIELD_GENERATED, FIELD_SUBFIELD_GENERATED, FINITE_IMAGE,
        FINITE_NUMSEG_LT, FORALL_IN_IMAGE, FREE_BASIS_EXTENSION_DEGREE,
        FREE_BASIS_IN_CARRIER, FREE_BASIS_SPANNING_DEGREE, IMAGE_I, INSERT_SUBSET,
        INTEGER_RING, IN_ELIM_THM, IN_IMAGE, IN_INSERT, IN_INTER, IN_SUBFIELD_0,
        IN_SUBFIELD_1, IN_SUBFIELD_ADD, IN_SUBFIELD_INV, IN_SUBFIELD_MUL,
        IN_SUBFIELD_NEG, IN_SUBFIELD_SUM, IN_UNION, IN_UNIV, I_THM, LT, MOD_LT_EQ,
        MULT_CLAUSES, NUMBER_FIELD_ALGEBRAIC, NUMBER_FIELD_DEGREE_POS,
        NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_SUBFIELD_GENERATED, PRIME_SUBFIELD_MINIMAL,
        PRIME_SUBFIELD_SUBFIELD_GENERATED, RDIV_LT_EQ, .. } := D.core1
  let { RING_ADD_RDISTRIB, RING_CARRIER_SUBFIELD_GENERATED_SUBSET,
        RING_HOMOMORPHISM_SUBFIELD_INCLUSION, RING_INDEPENDENT_IMP_SUBSET,
        RING_INDEPENDENT_LE_SPAN, RING_INV_0, RING_MUL, RING_MUL_LID, RING_MUL_LZERO,
        RING_MUL_RID, RING_OF_INTEGERS, RING_OF_INTEGERS_FREE,
        RING_OF_INTEGERS_FREE_BASIS_FIELD, RING_OF_INTEGERS_SUBFIELD_GENERATED,
        RING_OF_INTEGERS_SUBSET, RING_OF_INT_IN_RING_OF_INTEGERS,
        RING_OF_INT_IN_SUBFIELD_GENERATED, RING_OF_INT_SUBFIELD_GENERATED,
        RING_SPAN_INC, RING_SPAN_MUL, RING_SPAN_SUM, RING_SUM, RING_SUM_ADD,
        RING_SUM_CLOSED, RING_SUM_EQ, RING_SUM_EQ_0, RING_SUM_LMUL, RING_SUM_MOD_DIV,
        RING_SUM_RING_OF_INTEGERS, RING_SUM_RMUL, RING_SUM_SUBFIELD_GENERATED,
        SUBFIELD_GENERATED, SUBFIELD_GENERATED_INC_GEN, SUBFIELD_GENERATED_MINIMAL,
        SUBFIELD_GENERATED_RESTRICT, SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC,
        SUBFIELD_OF_FIELD_INV, SUBFIELD_SUBFIELD_GENERATED, SUBRING_GENERATED_MINIMAL,
        SUBSET, SUBSET_TRANS, subring_of, .. } := D.core2
  -- @@SCOPE END

  let NUMBER_FIELD_SUBFIELD_INTEGRAL_BASIS ← prove
    r"!(k:A ring) s n e.
        number_field k /\
        free_basis (integer_ring,ring_of_integers(subfield_generated k s))
                   (ring_of_int(subfield_generated k s)) n e
        ==> number_field(subfield_generated k s) /\
            extension_degree (subfield_generated k {ring_0 k},
                              subfield_generated k s) I = n /\
            free_basis (subfield_generated k {ring_0 k},subfield_generated k s)
                       I n e /\
            (!i. i < n ==> e i IN ring_carrier(subfield_generated k s)) /\
            (!i. i < n ==> e i IN ring_carrier(ring_of_integers k)) /\
            ring_of_int k (number_field_discriminant(subfield_generated k s)) =
            basis_discriminant (subfield_generated k {ring_0 k},
                                subfield_generated k s) I n e"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"number_field(subfield_generated k (s:A->bool))") ASSUME_TAC THENL [ASM_SIMP_TAC [NUMBER_FIELD_SUBFIELD_GENERATED], ASM_REWRITE_TAC []] THEN MP_TAC (← ISPECL [(← q r"subfield_generated k (s:A->bool)"), (← q r"n:num"), (← q r"e:num->A")] RING_OF_INTEGERS_FREE_BASIS_FIELD) THEN MP_TAC (← ISPECL [(← q r"subfield_generated k (s:A->bool)"), (← q r"n:num"), (← q r"e:num->A")] NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD) THEN ASM_REWRITE_TAC [PRIME_SUBFIELD_SUBFIELD_GENERATED, RING_OF_INT_SUBFIELD_GENERATED] THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP FREE_BASIS_IN_CARRIER) o (checkM (fun th => (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); canM (fun z3 => (do let z4 ← (pure z3); find_termM (fun z5 => (do let z7 ← (pure z5); let z6 ← (q r"integer_ring"); pure (z6 == z7))) z4)) z1))))) THEN RULE_ASSUM_TAC (REWRITE_RULE [RING_OF_INTEGERS_SUBFIELD_GENERATED, IN_INTER]) THEN ASM_SIMP_TAC [])

  let NUMBER_FIELD_SUBFIELD_INTEGRAL_COORDINATES ← prove
    r"!(k:A ring) t m f c.
        number_field k /\
        free_basis (integer_ring,ring_of_integers(subfield_generated k t))
                   (ring_of_int(subfield_generated k t)) m f /\
        (!j. j < m ==> c j IN ring_carrier(subfield_generated k {ring_0 k})) /\
        ring_sum k {j | j < m} (\j. ring_mul k (c j) (f j)) IN
        ring_carrier(ring_of_integers k)
        ==> !j. j < m ==> ?w. c j = ring_of_int k w"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"t:A->bool"), (← q r"m:num"), (← q r"f:num->A")] NUMBER_FIELD_SUBFIELD_INTEGRAL_BASIS) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_carrier(subfield_generated k t) subfield_of (k:A ring) /\
    ring_carrier(subfield_generated k {ring_0 k}) SUBSET
    ring_carrier(subfield_generated k (t:A->bool))") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED] THEN MATCH_MP_TAC PRIME_SUBFIELD_MINIMAL THEN ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED], ALL_TAC] THEN ABBREV_TAC (← q r"z = ring_sum k {j | j < m} (\j. ring_mul k (c j) ((f:num->A) j))") THEN ABBREV_TAC (← q r"L = subfield_generated k (t:A->bool)") THEN ABBREV_TAC (← q r"q = subfield_generated k {ring_0 k:A}") THEN SUBGOAL_THEN (← q r"ring_mul L = ring_mul (k:A ring) /\ ring_of_int L = ring_of_int k /\
    ring_mul (ring_of_integers L) = ring_mul k") STRIP_ASSUME_TAC THENL [EXPAND_TAC "L" THEN REWRITE_TAC [SUBFIELD_GENERATED, RING_OF_INT_SUBFIELD_GENERATED, RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"!j. j < m ==> (f:num->A) j IN ring_carrier(ring_of_integers L)") ASSUME_TAC THENL [FIRST_ASSUM (ACCEPT_TAC o ((MATCH_MP FREE_BASIS_IN_CARRIER) o (checkM (fun th => (do let z30 ← (do let z31 ← (pure th); pure (concl z31)); canM (fun z32 => (do let z33 ← (pure z32); find_termM (fun z34 => (do let z36 ← (pure z34); let z35 ← (q r"integer_ring"); pure (z35 == z36))) z33)) z30))))), ALL_TAC] THEN SUBGOAL_THEN (← q r"!x:A. x IN ring_carrier(ring_of_integers L) ==> x IN ring_carrier L") ASSUME_TAC THENL [MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"(z:A) IN ring_carrier(ring_of_integers L)") ASSUME_TAC THENL [EXPAND_TAC "L" THEN REWRITE_TAC [RING_OF_INTEGERS_SUBFIELD_GENERATED, IN_INTER] THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "z" THEN MATCH_MP_TAC IN_SUBFIELD_SUM THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"j:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN MATCH_MP_TAC IN_SUBFIELD_MUL THEN ASM_SIMP_TAC [] THEN ASM SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_int L:int->A"), (← q r"integer_ring"), (← q r"ring_of_integers L:A ring"), (← q r"m:num"), (← q r"f:num->A"), (← q r"z:A")] BASIS_COORDINATES) THEN ASM_REWRITE_TAC [INTEGER_RING, IN_UNIV] THEN ABBREV_TAC (← q r"w = basis_coordinates (integer_ring,ring_of_integers L)
          (ring_of_int k) m (f:num->A) z") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"!j. j < m
        ==> ring_mul k (ring_of_int k ((w:num->int) j)) ((f:num->A) j) IN
            ring_carrier(ring_of_integers L)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_of_int k ((w:num->int) j):A IN ring_carrier(ring_of_integers L)") ASSUME_TAC THENL [FIRST_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z29 ← (q r"ring_of_int L = ring_of_int (k:A ring)"); let z28 ← (do let z27 ← (pure th); pure (concl z27)); pure (z28 == z29)))))) THEN REWRITE_TAC [RING_OF_INT_IN_RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers L:A ring"), (← q r"ring_of_int k ((w:num->int) j):A"), (← q r"(f:num->A) j")] RING_MUL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sum L {j | j < m}
      (\j. ring_mul k (ring_of_int k ((w:num->int) j)) ((f:num->A) j)) =
    z") ASSUME_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do if ← (do let z14 ← (do let z15 ← (pure th); pure (concl z15)); pure (is_eq z14)) then (do let z19 ← (q r"z:A"); let z18 ← (do let z16 ← (do let z17 ← (pure th); pure (concl z17)); liftExcept (rhs z16)); pure (z18 == z19)) else pure false) then (do let z20 ← (do let z21 ← (pure th); pure (concl z21)); canM (fun z22 => (do let z23 ← (pure z22); find_termM (fun z24 => (do let z26 ← (pure z24); let z25 ← (q r"ring_of_integers L:A ring"); pure (z25 == z26))) z23)) z20) else pure false))))) THEN ASM_REWRITE_TAC [I_THM] THEN MP_TAC (← ISPECL [(← q r"L:A ring"), (← q r"{j:num | j < m}"), (← q r"\j. ring_mul k (ring_of_int k ((w:num->int) j))
                                   ((f:num->A) j)")] RING_SUM_RING_OF_INTEGERS) THEN ANTS_TAC THENL [ASM_SIMP_TAC [IN_ELIM_THM], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sum L {j | j < m} (\j. ring_mul k (c j) ((f:num->A) j)) = z") ASSUME_TAC THENL [ASM_REWRITE_TAC [I_THM] THEN FIRST_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_eq z1)) then (do let z6 ← (q r"z:A"); let z5 ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); liftExcept (rhs z3)); pure (z5 == z6)) else pure false) then (do let z7 ← (do let z8 ← (pure th); pure (concl z8)); canM (fun z9 => (do let z10 ← (pure z9); find_termM (fun z11 => (do let z13 ← (pure z11); let z12 ← (q r"c:num->A"); pure (z12 == z13))) z10)) z7) else pure false))))) THEN EXPAND_TAC "L" THEN MATCH_MP_TAC RING_SUM_SUBFIELD_GENERATED THEN REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IN_SUBFIELD_MUL THEN ASM_SIMP_TAC [] THEN ASM SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"q:A ring"), (← q r"L:A ring"), (← q r"m:num"), (← q r"f:num->A"), (← q r"z:A"), (← q r"c:num->A")] BASIS_COORDINATES_UNIQUE) THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"q:A ring"), (← q r"L:A ring"), (← q r"m:num"), (← q r"f:num->A"), (← q r"z:A"), (← q r"\j. ring_of_int k ((w:num->int) j):A")] BASIS_COORDINATES_UNIQUE) THEN ASM_REWRITE_TAC [I_THM] THEN SUBGOAL_THEN (← q r"ring_homomorphism(q,L) (I:A->A)") (fun th => REWRITE_TAC [th]) THENL [MAP_EVERY EXPAND_TAC ["q", "L"] THEN GEN_REWRITE_TAC (RATOR_CONV o (RAND_CONV o LAND_CONV)) [(← GSYM (← ISPECL [(← q r"k:A ring"), (← q r"t:A->bool")] PRIME_SUBFIELD_SUBFIELD_GENERATED))] THEN REWRITE_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION], ALL_TAC] THEN EXPAND_TAC "q" THEN REWRITE_TAC [RING_OF_INT_IN_SUBFIELD_GENERATED] THEN ASM_SIMP_TAC [] THEN MESON_TAC [])

  let NUMBER_FIELD_COMPOSITUM_PRODUCT_SPAN ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r4 ← SET_RULE (← q r"!t. y IN t /\ t SUBSET W ==> (y:A) IN W")
    let r26 ← RING_RULE (← q r"ring_mul r (ring_neg r (ring_1 r)) x = ring_neg r (x:A)")
    let r37 ← RING_RULE (← q r"ring_mul r c (ring_mul r e f) = ring_mul r (ring_mul r c e) (f:A)")
    let r47 ← RING_RULE (← q r"ring_mul r (ring_mul r x y) (ring_mul r d (ring_mul r e f)) =
        ring_mul r (ring_mul r x (ring_mul r d e)) (ring_mul r y (f:A))")
    let r54 ← RING_RULE (← q r"ring_mul r (ring_mul r a e) (ring_mul r b f) =
        ring_mul r (ring_mul r a b) (ring_mul r e (f:A))")
    prove
      r"!(k:A ring) s t n m e f.
          number_field k /\ subfield_generated k (s UNION t) = k /\
          free_basis (subfield_generated k {ring_0 k},subfield_generated k s)
                     I n e /\
          free_basis (subfield_generated k {ring_0 k},subfield_generated k t)
                     I m f
          ==> !x. x IN ring_carrier k
                  ==> ?c. (!u. u < n * m
                               ==> c u IN ring_carrier
                                            (subfield_generated k {ring_0 k})) /\
                          x = ring_sum k {u | u < n * m}
                                (\u. ring_mul k (c u)
                                       (ring_mul k (e(u MOD n)) (f(u DIV n))))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN (← q r"~(n = 0) /\ ~(m = 0)") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"subfield_generated k (t:A->bool)"), (← q r"m:num"), (← q r"f:num->A")] FREE_BASIS_EXTENSION_DEGREE) THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"subfield_generated k (s:A->bool)"), (← q r"n:num"), (← q r"e:num->A")] FREE_BASIS_EXTENSION_DEGREE) THEN MP_TAC (← ISPEC (← q r"subfield_generated k (t:A->bool)") NUMBER_FIELD_DEGREE_POS) THEN MP_TAC (← ISPEC (← q r"subfield_generated k (s:A->bool)") NUMBER_FIELD_DEGREE_POS) THEN ASM_SIMP_TAC [NUMBER_FIELD_SUBFIELD_GENERATED, PRIME_SUBFIELD_SUBFIELD_GENERATED, FIELD_SUBFIELD_GENERATED, NUMBER_FIELD_IMP_FIELD] THEN REWRITE_TAC [(← GEN_ALL (← REWRITE_RULE [PRIME_SUBFIELD_SUBFIELD_GENERATED] (← ISPECL [(← q r"subfield_generated k (u:A->bool)"), (← q r"{ring_0(subfield_generated k (u:A->bool))}")] RING_HOMOMORPHISM_SUBFIELD_INCLUSION)))] THEN ARITH_TAC, ALL_TAC] THEN ABBREV_TAC (← q r"q = subfield_generated k {ring_0 k:A}") THEN ABBREV_TAC (← q r"K = subfield_generated k (s:A->bool)") THEN ABBREV_TAC (← q r"L = subfield_generated k (t:A->bool)") THEN SUBGOAL_THEN (← q r"ring_carrier K subfield_of (k:A ring) /\ ring_carrier L subfield_of k /\
      ring_carrier q subfield_of k") STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["K", "L", "q"] THEN ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_carrier q SUBSET ring_carrier K /\
      ring_carrier q SUBSET ring_carrier (L:A ring)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "q" THEN CONJ_TAC THEN MATCH_MP_TAC PRIME_SUBFIELD_MINIMAL THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul K = ring_mul (k:A ring) /\ ring_mul L = ring_mul k") STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["K", "L"] THEN REWRITE_TAC [SUBFIELD_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"(!i. i < n ==> (e:num->A) i IN ring_carrier K) /\
      (!j. j < m ==> (f:num->A) j IN ring_carrier L)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [FREE_BASIS_IN_CARRIER], ALL_TAC] THEN SUBGOAL_THEN (← q r"(!x:A. x IN ring_carrier K ==> x IN ring_carrier k) /\
      (!x:A. x IN ring_carrier L ==> x IN ring_carrier k) /\
      (!x:A. x IN ring_carrier q ==> x IN ring_carrier k)") STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["K", "L", "q"] THEN MESON_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBSET], ALL_TAC] THEN ABBREV_TAC (← q r"B = \u. ring_mul k ((e:num->A)(u MOD n)) (f(u DIV n))") THEN SUBGOAL_THEN (← q r"!u. u < n * m ==> u MOD n < n /\ u DIV n < m") ASSUME_TAC THENL [ASM_SIMP_TAC [MOD_LT_EQ, RDIV_LT_EQ], ALL_TAC] THEN SUBGOAL_THEN (← q r"!u. u < n * m ==> (B:num->A) u IN ring_carrier k") ASSUME_TAC THENL [EXPAND_TAC "B" THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL THEN ASM_MESON_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"W = {x:A | ?c. (!u. u < n * m:num ==> c u IN ring_carrier q) /\
                     x = ring_sum k {u | u < n * m}
                           (\u. ring_mul k (c u) (B u))}") THEN SUBGOAL_THEN (← q r"!x:A. x IN W ==> x IN ring_carrier k") ASSUME_TAC THENL [EXPAND_TAC "W" THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [RING_SUM], ALL_TAC] THEN SUBGOAL_THEN (← q r"(ring_0 k:A) IN W") ASSUME_TAC THENL [EXPAND_TAC "W" THEN REWRITE_TAC [IN_ELIM_THM] THEN EXISTS_TAC (← q r"\u:num. ring_0 k:A") THEN REWRITE_TAC [] THEN CONJ_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_SUBFIELD_0 THEN ASM_REWRITE_TAC [], CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_EQ_0 THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_SIMP_TAC [RING_MUL_LZERO]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x y:A. x IN W /\ y IN W ==> ring_add k x y IN W") ASSUME_TAC THENL [EXPAND_TAC "W" THEN REWRITE_TAC [IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"y:A")] THEN DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"c:num->A") STRIP_ASSUME_TAC) (X_CHOOSE_THEN (← q r"d:num->A") STRIP_ASSUME_TAC)) THEN EXISTS_TAC (← q r"\u. ring_add k ((c:num->A) u) (d u)") THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_SUBFIELD_ADD THEN ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"\u. ring_mul k ((c:num->A) u) (B u)"), (← q r"\u. ring_mul k ((d:num->A) u) (B u)"), (← q r"{u:num | u < n * m}")] RING_SUM_ADD) THEN ANTS_TAC THENL [REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL THEN ASM_SIMP_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN REWRITE_TAC [] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_ADD_RDISTRIB THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!(g:num->A) r. (!i. i IN r ==> g i IN W) ==> ring_sum k r g IN W") (LABEL_TAC "sum") THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [] (← ISPECL [(← q r"k:A ring"), (← q r"\x:A. x IN W")] RING_SUM_CLOSED)) THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x y:A. x IN ring_carrier K /\ y IN ring_carrier L
              ==> ring_mul k x y IN W") (LABEL_TAC "prod") THENL [MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"y:A")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"q:A ring"), (← q r"K:A ring"), (← q r"n:num"), (← q r"e:num->A"), (← q r"x:A")] BASIS_COORDINATES) THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"q:A ring"), (← q r"L:A ring"), (← q r"m:num"), (← q r"f:num->A"), (← q r"y:A")] BASIS_COORDINATES) THEN ASM_REWRITE_TAC [I_THM] THEN ABBREV_TAC (← q r"b = basis_coordinates (q,L) (I:A->A) m f y") THEN ABBREV_TAC (← q r"a = basis_coordinates (q,K) (I:A->A) n e x") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "y")) THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "x")) THEN SUBGOAL_THEN (← q r"x = ring_sum k {i | i < n} (\i. ring_mul k ((a:num->A) i) (e i)) /\
        y = ring_sum k {j | j < m} (\j. ring_mul k ((b:num->A) j) (f j))") (CONJUNCTS_THEN SUBST1_TAC) THENL [CONJ_TAC THENL [USE_THEN "x" (SUBST1_TAC o SYM) THEN EXPAND_TAC "K" THEN MATCH_MP_TAC RING_SUM_SUBFIELD_GENERATED THEN REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_SUBFIELD_MUL THEN ASM_SIMP_TAC [] THEN ASM SET_TAC [], USE_THEN "y" (SUBST1_TAC o SYM) THEN EXPAND_TAC "L" THEN MATCH_MP_TAC RING_SUM_SUBFIELD_GENERATED THEN REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_SUBFIELD_MUL THEN ASM_SIMP_TAC [] THEN ASM SET_TAC []], ALL_TAC] THEN EXPAND_TAC "W" THEN REWRITE_TAC [IN_ELIM_THM] THEN EXISTS_TAC (← q r"\u. ring_mul k ((a:num->A)(u MOD n)) (b(u DIV n))") THEN REWRITE_TAC [] THEN CONJ_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_SUBFIELD_MUL THEN ASM_REWRITE_TAC [], ALL_TAC] THEN EXPAND_TAC "B" THEN REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"m:num"), (← q r"\i j. ring_mul k (ring_mul k ((a:num->A) i) ((b:num->A) j))
                          (ring_mul k ((e:num->A) i) ((f:num->A) j))")] RING_SUM_MOD_DIV) THEN REWRITE_TAC [] THEN ANTS_TAC THENL [REPEAT STRIP_TAC THEN REPEAT (MATCH_MP_TAC RING_MUL THEN CONJ_TAC) THEN ASM_SIMP_TAC [], DISCH_THEN SUBST1_TAC] THEN SUBGOAL_THEN (← q r"(!i. i < n ==> ring_mul k ((a:num->A) i) (e i) IN ring_carrier k) /\
        (!j. j < m ==> ring_mul k ((b:num->A) j) (f j) IN ring_carrier k)") STRIP_ASSUME_TAC THENL [CONJ_TAC THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL THEN ASM_SIMP_TAC [], ALL_TAC] THEN TRANS_TAC EQ_TRANS (← q r"ring_sum k {j | j < m}
          (\j. ring_mul k (ring_sum k {i | i < n}
                             (\i. ring_mul k ((a:num->A) i) (e i)))
                          (ring_mul k ((b:num->A) j) (f j)))") THEN CONJ_TAC THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_LMUL THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, RING_SUM], MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"j:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC [] THEN wPart lhand (rand o rand) RING_SUM_RMUL THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"i:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC [] THEN MATCH_MP_TAC r54 THEN ASM_SIMP_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"!a:A. a IN ring_carrier q ==> a IN W") ASSUME_TAC THENL [X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"a = ring_mul k a (ring_1 k:A)") SUBST1_TAC THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_MUL_RID THEN ASM_SIMP_TAC [], USE_THEN "prod" MATCH_MP_TAC THEN CONJ_TAC THENL [ASM SET_TAC [], MATCH_MP_TAC IN_SUBFIELD_1 THEN ASM_REWRITE_TAC []]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x y z:A. x IN ring_carrier K /\ y IN ring_carrier L /\ z IN W
                ==> ring_mul k (ring_mul k x y) z IN W") ASSUME_TAC THENL [MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"y:A"), (← q r"z:A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"?d. (!u. u < n * m ==> d u IN ring_carrier q) /\
            z = ring_sum k {u | u < n * m}
                  (\u. ring_mul k (d u) ((B:num->A) u))") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"(z:A) IN W") THEN EXPAND_TAC "W" THEN REWRITE_TAC [IN_ELIM_THM], ALL_TAC] THEN FIRST_X_ASSUM (SUBST1_TAC o (checkM (fun th => (do if ← (do let z48 ← (do let z49 ← (pure th); pure (concl z49)); pure (is_eq z48)) then (do let z53 ← (q r"z:A"); let z52 ← (do let z50 ← (do let z51 ← (pure th); pure (concl z51)); liftExcept (lhs z50)); pure (z52 == z53)) else pure false)))) THEN wPart lhand (rand o rand) RING_SUM_LMUL THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, RING_MUL] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL THEN ASM_SIMP_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN USE_THEN "sum" MATCH_MP_TAC THEN X_GEN_TAC (← q r"u:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN EXPAND_TAC "B" THEN REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ring_mul k (ring_mul k x y)
          (ring_mul k ((d:num->A) u) (ring_mul k (e(u MOD n)) (f(u DIV n)))) =
        ring_mul k (ring_mul k x (ring_mul k (d u) (e(u MOD n))))
                   (ring_mul k y (f(u DIV n)))") SUBST1_TAC THENL [MATCH_MP_TAC r47 THEN ASM_SIMP_TAC [], ALL_TAC] THEN USE_THEN "prod" MATCH_MP_TAC THEN SUBGOAL_THEN (← q r"u MOD n < n /\ u DIV n < m") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN CONJ_TAC THENL [MATCH_MP_TAC IN_SUBFIELD_MUL THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IN_SUBFIELD_MUL THEN ASM_SIMP_TAC [] THEN FIRST_ASSUM (MATCH_MP_TAC o ((REWRITE_RULE [SUBSET]) o (checkM (fun th => (do let z46 ← (q r"ring_carrier q SUBSET ring_carrier (K:A ring)"); let z45 ← (do let z44 ← (pure th); pure (concl z44)); pure (z45 == z46)))))) THEN ASM_SIMP_TAC [], MATCH_MP_TAC IN_SUBFIELD_MUL THEN ASM_SIMP_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x z:A. x IN W /\ z IN W ==> ring_mul k x z IN W") ASSUME_TAC THENL [MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"z:A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"?c. (!u. u < n * m ==> c u IN ring_carrier q) /\
            x = ring_sum k {u | u < n * m}
                  (\u. ring_mul k (c u) ((B:num->A) u))") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"(x:A) IN W") THEN EXPAND_TAC "W" THEN REWRITE_TAC [IN_ELIM_THM], ALL_TAC] THEN FIRST_X_ASSUM (SUBST1_TAC o (checkM (fun th => (do if ← (do let z38 ← (do let z39 ← (pure th); pure (concl z39)); pure (is_eq z38)) then (do let z43 ← (q r"x:A"); let z42 ← (do let z40 ← (do let z41 ← (pure th); pure (concl z41)); liftExcept (lhs z40)); pure (z42 == z43)) else pure false)))) THEN wPart lhand (rand o rand) RING_SUM_RMUL THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL THEN ASM_SIMP_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN USE_THEN "sum" MATCH_MP_TAC THEN X_GEN_TAC (← q r"u:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"u MOD n < n /\ u DIV n < m") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN EXPAND_TAC "B" THEN REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ring_mul k (ring_mul k ((c:num->A) u)
                      (ring_mul k (e(u MOD n)) (f(u DIV n)))) z =
        ring_mul k (ring_mul k (ring_mul k (c u) (e(u MOD n))) (f(u DIV n)))
                   (z:A)") SUBST1_TAC THENL [AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC r37 THEN ASM_SIMP_TAC [], ALL_TAC] THEN FIRST_X_ASSUM (MATCH_MP_TAC o (checkM (fun th => (do if ← (do let z30 ← (do let z31 ← (pure th); pure (concl z31)); pure (is_forall z30)) then (do let z36 ← (pure 3); let z35 ← (do let z32 ← (do pure (Prod.fst (← (do let z33 ← (do let z34 ← (pure th); pure (concl z34)); pure (strip_forall z33))))); pure (length z32)); pure (z35 == z36)) else pure false)))) THEN ASM_SIMP_TAC [] THEN MATCH_MP_TAC IN_SUBFIELD_MUL THEN ASM_SIMP_TAC [] THEN FIRST_ASSUM (MATCH_MP_TAC o ((REWRITE_RULE [SUBSET]) o (checkM (fun th => (do let z29 ← (q r"ring_carrier q SUBSET ring_carrier (K:A ring)"); let z28 ← (do let z27 ← (pure th); pure (concl z27)); pure (z28 == z29)))))) THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(W:A->bool) subring_of k") ASSUME_TAC THENL [REWRITE_TAC [subring_of] THEN ASM_SIMP_TAC [SUBSET] THEN SUBGOAL_THEN (← q r"ring_1 k IN ring_carrier q /\ ring_neg k (ring_1 k:A) IN
                    ring_carrier q") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [MATCH_MP_TAC IN_SUBFIELD_1 THEN ASM_REWRITE_TAC [], MATCH_MP_TAC IN_SUBFIELD_NEG THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IN_SUBFIELD_1 THEN ASM_REWRITE_TAC []], ALL_TAC] THEN ASM_SIMP_TAC [] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_neg k x = ring_mul k (ring_neg k (ring_1 k)) (x:A)") SUBST1_TAC THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC r26 THEN ASM_SIMP_TAC [], FIRST_X_ASSUM (MATCH_MP_TAC o (checkM (fun th => (do if ← (do if ← (do if ← (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); pure (is_forall z5)) then (do let z11 ← (pure 2); let z10 ← (do let z7 ← (do pure (Prod.fst (← (do let z8 ← (do let z9 ← (pure th); pure (concl z9)); pure (strip_forall z8))))); pure (length z7)); pure (z10 == z11)) else pure false) then (do let z12 ← (do let z13 ← (pure th); pure (concl z13)); canM (fun z14 => (do let z15 ← (pure z14); find_termM (fun z16 => (do let z18 ← (pure z16); let z17 ← (q r"ring_mul:(A ring)->A->A->A"); pure (z17 == z18))) z15)) z12) else pure false) then (do pure !(← (do let z19 ← (do let z20 ← (pure th); pure (concl z20)); canM (fun z21 => (do let z22 ← (pure z21); find_termM (fun z23 => (do let z25 ← (pure z23); let z24 ← (q r"K:A ring"); pure (z24 == z25))) z22)) z19))) else pure false)))) THEN ASM_SIMP_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"(W:A->bool) subfield_of k") ASSUME_TAC THENL [MATCH_MP_TAC SUBFIELD_OF_FIELD_INV THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"x = ring_0 (k:A ring)") THEN ASM_REWRITE_TAC [RING_INV_0] THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"q:A ring"), (← q r"k:A ring"), (← q r"x:A")] SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC) THEN ANTS_TAC THENL [EXPAND_TAC "q" THEN ASM_SIMP_TAC [NUMBER_FIELD_ALGEBRAIC, FIELD_EXTENSION_SUBFIELD_GENERATED], DISCH_THEN (ASSUME_TAC o CONJUNCT1)] THEN MATCH_MP_TAC r4 THEN EXISTS_TAC (← q r"ring_carrier(subring_generated k
          ((x:A) INSERT IMAGE I (ring_carrier q)))") THEN CONJ_TAC THENL [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IN_SUBFIELD_INV THEN ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED] THEN MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN ASM_REWRITE_TAC [IN_INSERT], MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [INSERT_SUBSET, IMAGE_I] THEN ASM_SIMP_TAC [SUBSET]], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_carrier k SUBSET (W:A->bool)") ASSUME_TAC THENL [FIRST_X_ASSUM ((fun th => tactic_of do pure (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [(← SYM th)])) o (checkM (fun th => (do let z3 ← (q r"subfield_generated k (s UNION t) = (k:A ring)"); let z2 ← (do let z1 ← (pure th); pure (concl z1)); pure (z2 == z3))))) THEN ONCE_REWRITE_TAC [SUBFIELD_GENERATED_RESTRICT] THEN MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [SUBSET, IN_INTER, IN_UNION] THEN X_GEN_TAC (← q r"x:A") THEN STRIP_TAC THENL [SUBGOAL_THEN (← q r"(x:A) IN ring_carrier K") ASSUME_TAC THENL [EXPAND_TAC "K" THEN MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"x = ring_mul k x (ring_1 k:A)") SUBST1_TAC THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_MUL_RID THEN ASM_REWRITE_TAC [], USE_THEN "prod" MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IN_SUBFIELD_1 THEN ASM_REWRITE_TAC []], SUBGOAL_THEN (← q r"(x:A) IN ring_carrier L") ASSUME_TAC THENL [EXPAND_TAC "L" THEN MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"x = ring_mul k (ring_1 k) (x:A)") SUBST1_TAC THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_MUL_LID THEN ASM_REWRITE_TAC [], USE_THEN "prod" MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IN_SUBFIELD_1 THEN ASM_REWRITE_TAC []]], ALL_TAC] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:A) IN W") MP_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN EXPAND_TAC "W" THEN EXPAND_TAC "B" THEN REWRITE_TAC [IN_ELIM_THM])

  let NUMBER_FIELD_COMPOSITUM_PRODUCT_BASIS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!t. x IN t /\ t SUBSET ring_carrier(k:A ring)
        ==> x IN ring_carrier k")
    prove
      r"!(k:A ring) s t n m e f.
          number_field k /\ subfield_generated k (s UNION t) = k /\
          free_basis (subfield_generated k {ring_0 k},subfield_generated k s)
                     I n e /\
          free_basis (subfield_generated k {ring_0 k},subfield_generated k t)
                     I m f /\
          extension_degree (subfield_generated k {ring_0 k},k) I = n * m
          ==> free_basis (subfield_generated k {ring_0 k},k) I (n * m)
                (\u. ring_mul k (e(u MOD n)) (f(u DIV n)))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"s:A->bool"), (← q r"t:A->bool"), (← q r"n:num"), (← q r"m:num"), (← q r"e:num->A"), (← q r"f:num->A")] NUMBER_FIELD_COMPOSITUM_PRODUCT_SPAN) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MATCH_MP_TAC FREE_BASIS_SPANNING_DEGREE THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, NUMBER_FIELD_IMP_FIELD, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, I_THM] THEN X_GEN_TAC (← q r"u:num") THEN DISCH_TAC THEN MATCH_MP_TAC RING_MUL THEN SUBGOAL_THEN (← q r"~(n = 0)") ASSUME_TAC THENL [UNDISCH_TAC (← q r"u < n * m:num") THEN ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [MULT_CLAUSES, LT], ALL_TAC] THEN SUBGOAL_THEN (← q r"u MOD n < n /\ u DIV n < m") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [MOD_LT_EQ, RDIV_LT_EQ], ALL_TAC] THEN CONJ_TAC THEN MATCH_MP_TAC r1 THENL [EXISTS_TAC (← q r"ring_carrier(subfield_generated k (s:A->bool))"), EXISTS_TAC (← q r"ring_carrier(subfield_generated k (t:A->bool))")] THEN REWRITE_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET] THEN FIRST_ASSUM (MATCH_MP_TAC o (MATCH_MP FREE_BASIS_IN_CARRIER)) THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_COMPOSITUM_DEGREE_LE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r13 ← SET_RULE (← q r"!t. x IN t /\ t SUBSET ring_carrier(k:A ring)
          ==> x IN ring_carrier k")
    prove
      r"!(k:A ring) s t.
          number_field k /\ subfield_generated k (s UNION t) = k
          ==> extension_degree (subfield_generated k {ring_0 k},k) I <=
              extension_degree (subfield_generated k {ring_0 k},
                                subfield_generated k s) I *
              extension_degree (subfield_generated k {ring_0 k},
                                subfield_generated k t) I"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"subfield_generated k (s:A->bool)") RING_OF_INTEGERS_FREE) THEN MP_TAC (← ISPEC (← q r"subfield_generated k (t:A->bool)") RING_OF_INTEGERS_FREE) THEN ASM_SIMP_TAC [NUMBER_FIELD_SUBFIELD_GENERATED, PRIME_SUBFIELD_SUBFIELD_GENERATED] THEN ABBREV_TAC (← q r"n = extension_degree (subfield_generated k {ring_0 k},
                            subfield_generated k s) (I:A->A)") THEN ABBREV_TAC (← q r"m = extension_degree (subfield_generated k {ring_0 k},
                            subfield_generated k t) (I:A->A)") THEN DISCH_THEN (X_CHOOSE_TAC (← q r"f:num->A")) THEN DISCH_THEN (X_CHOOSE_TAC (← q r"e:num->A")) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"t:A->bool"), (← q r"m:num"), (← q r"f:num->A")] NUMBER_FIELD_SUBFIELD_INTEGRAL_BASIS) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"s:A->bool"), (← q r"n:num"), (← q r"e:num->A")] NUMBER_FIELD_SUBFIELD_INTEGRAL_BASIS) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"s:A->bool"), (← q r"t:A->bool"), (← q r"n:num"), (← q r"m:num"), (← q r"e:num->A"), (← q r"f:num->A")] NUMBER_FIELD_COMPOSITUM_PRODUCT_SPAN) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASSUME_TAC (← MATCH_MP NUMBER_FIELD_IMP_FIELD (← ASSUME (← q r"number_field(k:A ring)"))) THEN ABBREV_TAC (← q r"q = subfield_generated k {ring_0 k:A}") THEN SUBGOAL_THEN (← q r"field(q:A ring) /\ ring_homomorphism(q,k) (I:A->A) /\
      (!a:A. a IN ring_carrier q ==> a IN ring_carrier k)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "q" THEN SIMP_TAC [FIELD_SUBFIELD_GENERATED, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, (← ASSUME (← q r"field(k:A ring)"))] THEN REWRITE_TAC [(← GSYM SUBSET), RING_CARRIER_SUBFIELD_GENERATED_SUBSET], ALL_TAC] THEN ABBREV_TAC (← q r"ps = IMAGE (\u. ring_mul k ((e:num->A)(u MOD n)) (f(u DIV n)))
                {u | u < n * m}") THEN SUBGOAL_THEN (← q r"FINITE(ps:A->bool) /\ CARD ps <= n * m") STRIP_ASSUME_TAC THENL [EXPAND_TAC "ps" THEN SIMP_TAC [FINITE_IMAGE, FINITE_NUMSEG_LT] THEN GEN_REWRITE_TAC RAND_CONV [(← GSYM CARD_NUMSEG_LT)] THEN MATCH_MP_TAC CARD_IMAGE_LE THEN REWRITE_TAC [FINITE_NUMSEG_LT], ALL_TAC] THEN SUBGOAL_THEN (← q r"(ps:A->bool) SUBSET ring_carrier k") ASSUME_TAC THENL [EXPAND_TAC "ps" THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN X_GEN_TAC (← q r"u:num") THEN DISCH_TAC THEN MATCH_MP_TAC RING_MUL THEN SUBGOAL_THEN (← q r"~(n = 0)") ASSUME_TAC THENL [UNDISCH_TAC (← q r"u < n * m:num") THEN ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [MULT_CLAUSES, LT], ALL_TAC] THEN SUBGOAL_THEN (← q r"u MOD n < n /\ u DIV n < m") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [MOD_LT_EQ, RDIV_LT_EQ], ALL_TAC] THEN CONJ_TAC THEN MATCH_MP_TAC r13 THENL [EXISTS_TAC (← q r"ring_carrier(subfield_generated k (s:A->bool))"), EXISTS_TAC (← q r"ring_carrier(subfield_generated k (t:A->bool))")] THEN ASM_SIMP_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_carrier k SUBSET ring_span (q,k) (I:A->A) ps") ASSUME_TAC THENL [REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"x:A")) o (checkM (fun th => (do if ← (do if ← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); pure (is_forall z4)) then (do let z6 ← (do pure (Prod.snd (← (do let z7 ← (do let z8 ← (pure th); pure (concl z8)); liftExcept (dest_forall z7))))); pure (is_imp z6)) else pure false) then (do let z9 ← (do let z10 ← (do pure (Prod.snd (← (do let z11 ← (do let z12 ← (pure th); pure (concl z12)); liftExcept (dest_forall z11))))); liftExcept (rand z10)); pure (is_exists z9)) else pure false))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:num->A") (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN MATCH_MP_TAC RING_SPAN_SUM THEN X_GEN_TAC (← q r"u:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"q:A ring"), (← q r"k:A ring"), (← q r"ps:A->bool"), (← q r"(c:num->A) u"), (← q r"ring_mul k ((e:num->A)(u MOD n)) (f(u DIV n))")] RING_SPAN_MUL) THEN REWRITE_TAC [I_THM] THEN DISCH_THEN MATCH_MP_TAC THEN SUBGOAL_THEN (← q r"ring_mul k ((e:num->A)(u MOD n)) (f(u DIV n)) IN ps") ASSUME_TAC THENL [EXPAND_TAC "ps" THEN REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN EXISTS_TAC (← q r"u:num") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [] THEN MATCH_MP_TAC RING_SPAN_INC THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (MATCH_MP_TAC o ((REWRITE_RULE [SUBSET]) o (checkM (fun th => (do let z3 ← (q r"(ps:A->bool) SUBSET ring_carrier k"); let z2 ← (do let z1 ← (pure th); pure (concl z1)); pure (z2 == z3)))))) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MATCH_MP_TAC EXTENSION_DEGREE_LE_INDEPENDENT_BOUND THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"w:A->bool") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"q:A ring"), (← q r"k:A ring"), (← q r"w:A->bool"), (← q r"ps:A->bool")] RING_INDEPENDENT_LE_SPAN) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC (← q r"ring_carrier(k:A ring)") THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [RING_INDEPENDENT_IMP_SUBSET], STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_SUBFIELD_INTEGRAL_BASIS,
           NUMBER_FIELD_SUBFIELD_INTEGRAL_COORDINATES,
           NUMBER_FIELD_COMPOSITUM_PRODUCT_SPAN, NUMBER_FIELD_COMPOSITUM_PRODUCT_BASIS,
           NUMBER_FIELD_COMPOSITUM_DEGREE_LE }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- discriminant_compositum.ml phrases from line 808 to 1029               -/
/- ---------------------------------------------------------------------- -/

structure DiscriminantCompositum02 where
  -- @@FIELDS
  BASIS_DISCRIMINANT_PRODUCT_BASIS : thm
  NUMBER_FIELD_COMPOSITUM_HOMOMORPHISMS : thm
  NUMBER_FIELD_COMPOSITUM_COORDINATES : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDiscriminantCompositum02 [HolBase] (D : DiscriminantCompositumDeps) (BDiscriminantCompositum01 : DiscriminantCompositum01) :
    ExceptT String IO DiscriminantCompositum02 := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON, MESON_TAC, RING_RULE, SET_TAC,
        TAUT, .. } := D
  let { ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD, ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH,
        ALGEBRA_TRACE_NORM_IN_CARRIER, ALGEBRA_TRACE_PRODUCT_BASIS, EQ_MULT_LCANCEL,
        EXISTS_UNIQUE_THM, EXTENSIONAL_EQ, FIELD_SUBFIELD_GENERATED,
        FINITE_IMP_ALGEBRAIC_EXTENSION, FINITE_NUMSEG_LT, FREE_BASIS_IN_CARRIER,
        FUN_EQ_THM, HAS_SIZE_INDEX, HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS,
        INTEGRAL_CLOSURE_SUBRING, INTEGRAL_ELEMENT_HOMOMORPHIC_IMAGE,
        INTEGRAL_ELEMENT_MONOMORPHIC_PREIMAGE, IN_ELIM_THM, IN_SUBFIELD_MUL,
        IN_SUBFIELD_SUM, IN_SUBRING_MUL, IN_UNION, I_THM, MOD_LT_EQ, MULT_CLAUSES,
        MULT_SYM, NUMBER_FIELD_DEGREE_POS, NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS,
        NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_TOWER_LAW, PRIME_SUBFIELD_MINIMAL,
        PRIME_SUBFIELD_SUBFIELD_GENERATED, RDIV_LT_EQ, .. } := D.core1
  let { RING_CARRIER_SUBFIELD_GENERATED_SUBSET, RING_CHAR_SUBFIELD_GENERATED, RING_DET,
        RING_DET_CRAMER_SUBRING, RING_DET_EQ, RING_DET_KRONECKER_MOD_DIV,
        RING_DET_SUBRING, RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED,
        RING_HOMOMORPHISM_FROM_SUBFIELD_GENERATED,
        RING_HOMOMORPHISM_INTEGER_RING_OF_INT, RING_HOMOMORPHISM_IN_CARRIER,
        RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_RING_OF_INT,
        RING_HOMOMORPHISM_SUBFIELD_INCLUSION, RING_HOMOMORPHISM_SUM,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL, RING_MUL_ASSOC, RING_MUL_SYM,
        RING_OF_INT, RING_OF_INTEGERS_CARRIER, RING_OF_INT_IN_SUBFIELD_GENERATED,
        RING_POW_2, RING_POW_SUBFIELD_GENERATED, RING_SUM_EQ, RING_SUM_LMUL,
        RING_SUM_RMUL, SEPARABLE_EXTENSION_CHAR0, SUBFIELD_GENERATED,
        SUBFIELD_GENERATED_INC_GEN, SUBFIELD_SUBFIELD_GENERATED, SUBSET,
        algebraic_extension, basis_discriminant, field_extension, number_field, o_THM,
        ring_homomorphism_extensions, .. } := D.core2
  let { NUMBER_FIELD_SUBFIELD_INTEGRAL_BASIS,
        NUMBER_FIELD_SUBFIELD_INTEGRAL_COORDINATES, .. } := BDiscriminantCompositum01
  -- @@SCOPE END

  let BASIS_DISCRIMINANT_PRODUCT_BASIS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r10 ← RING_RULE (← q r"ring_mul r (ring_mul r a b) (ring_mul r c d) =
      ring_mul r (ring_mul r a c) (ring_mul r b (d:A))")
    prove
      r"!(k:A ring) s t n m e f.
          field k /\
          free_basis (subfield_generated k {ring_0 k},subfield_generated k s)
                     I n e /\
          free_basis (subfield_generated k {ring_0 k},subfield_generated k t)
                     I m f /\
          free_basis (subfield_generated k {ring_0 k},k) I (n * m)
                     (\u. ring_mul k (e(u MOD n)) (f(u DIV n)))
          ==> basis_discriminant (subfield_generated k {ring_0 k},k) I (n * m)
                (\u. ring_mul k (e(u MOD n)) (f(u DIV n))) =
              ring_mul k
                (ring_pow k
                   (basis_discriminant (subfield_generated k {ring_0 k},
                                        subfield_generated k s) I n e) m)
                (ring_pow k
                   (basis_discriminant (subfield_generated k {ring_0 k},
                                        subfield_generated k t) I m f) n)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!x y. x IN ring_carrier(subfield_generated k s) /\
            y IN ring_carrier(subfield_generated k t)
            ==> algebra_trace (subfield_generated k {ring_0 k},k) I
                  (ring_mul k x y) =
                ring_mul k
                  (algebra_trace (subfield_generated k {ring_0 k},
                                  subfield_generated k s) I x)
                  (algebra_trace (subfield_generated k {ring_0 k},
                                  subfield_generated k t) I (y:A))") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC ALGEBRA_TRACE_PRODUCT_BASIS THEN MAP_EVERY EXISTS_TAC [(← q r"n:num"), (← q r"m:num"), (← q r"e:num->A"), (← q r"f:num->A")] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"q = subfield_generated k {ring_0 k:A}") THEN ABBREV_TAC (← q r"K = subfield_generated k (s:A->bool)") THEN ABBREV_TAC (← q r"L = subfield_generated k (t:A->bool)") THEN SUBGOAL_THEN (← q r"ring_mul q = ring_mul (k:A ring) /\ ring_pow q = ring_pow k /\
      ring_mul K = ring_mul k /\ ring_mul L = ring_mul k") STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["q", "K", "L"] THEN REWRITE_TAC [(← CONJUNCT2 SUBFIELD_GENERATED), RING_POW_SUBFIELD_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"(!i. i < n ==> (e:num->A) i IN ring_carrier K) /\
      (!j. j < m ==> (f:num->A) j IN ring_carrier L)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [FREE_BASIS_IN_CARRIER], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"q:A ring"), (← q r"n:num"), (← q r"m:num"), (← q r"\i j. algebra_trace (q,K) I (ring_mul K ((e:num->A) i) (e j))"), (← q r"\i j. algebra_trace (q,L) I (ring_mul L ((f:num->A) i) (f j))")] RING_DET_KRONECKER_MOD_DIV) THEN REWRITE_TAC [ALGEBRA_TRACE_NORM_IN_CARRIER] THEN ASM_REWRITE_TAC [basis_discriminant] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:num"), (← q r"b:num")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"a MOD n < n /\ a DIV n < m /\ b MOD n < n /\ b DIV n < m") STRIP_ASSUME_TAC THENL [SUBGOAL_THEN (← q r"~(n = 0)") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN ASM_SIMP_TAC [MOD_LT_EQ, RDIV_LT_EQ], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x:A. x IN ring_carrier K \/ x IN ring_carrier L
            ==> x IN ring_carrier k") ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["K", "L"] THEN MESON_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul k (ring_mul k (e(a MOD n)) (f(a DIV n)))
                 (ring_mul k (e(b MOD n)) (f(b DIV n))) =
      ring_mul k (ring_mul k ((e:num->A)(a MOD n)) (e(b MOD n)))
                 (ring_mul k ((f:num->A)(a DIV n)) (f(b DIV n)))") SUBST1_TAC THENL [MATCH_MP_TAC r10 THEN ASM_SIMP_TAC [], ALL_TAC] THEN FIRST_X_ASSUM (MATCH_MP_TAC o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_forall z1)) then (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); canM (fun z5 => (do let z6 ← (pure z5); find_termM (fun z7 => (do let z9 ← (pure z7); let z8 ← (q r"algebra_trace:(A ring#A ring)->(A->A)->A->A"); pure (z8 == z9))) z6)) z3) else pure false)))) THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"K:A ring"), (← q r"(e:num->A)(a MOD n)"), (← q r"(e:num->A)(b MOD n)")] RING_MUL), MP_TAC (← ISPECL [(← q r"L:A ring"), (← q r"(f:num->A)(a DIV n)"), (← q r"(f:num->A)(b DIV n)")] RING_MUL)] THEN ASM_SIMP_TAC [])

  let NUMBER_FIELD_COMPOSITUM_HOMOMORPHISMS ← prove
    r"!(k:A ring) s t.
        number_field k /\ subfield_generated k (s UNION t) = k /\
        extension_degree (subfield_generated k {ring_0 k},k) I =
        extension_degree (subfield_generated k {ring_0 k},
                          subfield_generated k s) I *
        extension_degree (subfield_generated k {ring_0 k},
                          subfield_generated k t) I
        ==> ?(l:(A#num)ring) g sig.
              field l /\ ring_monomorphism(k,l) g /\
              (!i. i < extension_degree (subfield_generated k {ring_0 k},
                                         subfield_generated k s) I
                   ==> ring_homomorphism(k,l) (sig i)) /\
              (!i x. i < extension_degree (subfield_generated k {ring_0 k},
                                           subfield_generated k s) I /\
                     x IN ring_carrier(subfield_generated k t)
                     ==> sig i x = g x) /\
              (!i j. i < extension_degree (subfield_generated k {ring_0 k},
                                           subfield_generated k s) I /\
                     j < extension_degree (subfield_generated k {ring_0 k},
                                           subfield_generated k s) I /\
                     (!x. x IN ring_carrier(subfield_generated k s)
                          ==> sig i x = sig j x)
                     ==> i = j)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN ABBREV_TAC (← q r"n = extension_degree (subfield_generated k {ring_0 k},
                          subfield_generated k s) (I:A->A)") THEN ABBREV_TAC (← q r"m = extension_degree (subfield_generated k {ring_0 k},
                          subfield_generated k t) (I:A->A)") THEN MP_TAC (← ISPEC (← q r"k:A ring") ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN ASM_REWRITE_TAC [algebraic_extension, field_extension] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"l:(A#num)ring") (X_CHOOSE_THEN (← q r"g:A->A#num") STRIP_ASSUME_TAC)) THEN MAP_EVERY EXISTS_TAC [(← q r"l:(A#num)ring"), (← q r"g:A->A#num")] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"subfield_generated k (t:A->bool)"), (← q r"k:A ring"), (← q r"I:A->A")] NUMBER_FIELD_TOWER_LAW) THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, PRIME_SUBFIELD_SUBFIELD_GENERATED] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"extension_degree (subfield_generated k t,k) (I:A->A) = n") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"~(m = 0)") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") NUMBER_FIELD_DEGREE_POS) THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"m * extension_degree (subfield_generated k t,k) (I:A->A) = m * n") MP_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z13 ← (do let z14 ← (pure th); pure (concl z14)); pure (is_eq z13)) then (do let z18 ← (q r"n * m:num"); let z17 ← (do let z15 ← (do let z16 ← (pure th); pure (concl z16)); liftExcept (lhs z15)); pure (z17 == z18)) else pure false))))) THEN REWRITE_TAC [MULT_SYM], ASM_REWRITE_TAC [EQ_MULT_LCANCEL]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"g:A->A#num"), (← q r"subfield_generated k (t:A->bool)"), (← q r"k:A ring"), (← q r"l:(A#num)ring")] HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_HOMOMORPHISM_FROM_SUBFIELD_GENERATED] THEN MATCH_MP_TAC SEPARABLE_EXTENSION_CHAR0 THEN ASM_SIMP_TAC [FINITE_IMP_ALGEBRAIC_EXTENSION, RING_CHAR_SUBFIELD_GENERATED], ALL_TAC] THEN DISCH_THEN (MP_TAC o (MATCH_MP HAS_SIZE_INDEX)) THEN REWRITE_TAC [EXISTS_UNIQUE_THM] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"sig:num->A->A#num") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"sig:num->A->A#num") THEN SUBGOAL_THEN (← q r"!i. i < n ==> ring_homomorphism(k,l) ((sig:num->A->A#num) i) /\
                  sig i IN EXTENSIONAL(ring_carrier k) /\
                  !x. x IN ring_carrier(subfield_generated k t)
                      ==> sig i x = g x") ASSUME_TAC THENL [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"i:num")) o (checkM (fun th => (do if ← (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_forall z1)) then (do let z3 ← (do pure (Prod.snd (← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); liftExcept (dest_forall z4))))); pure (is_imp z3)) else pure false) then (do let z6 ← (do let z7 ← (pure th); pure (concl z7)); canM (fun z8 => (do let z9 ← (pure z8); find_termM (fun z10 => (do let z12 ← (pure z10); let z11 ← (q r"ring_homomorphism_extensions:         (A ring#A ring#(A#num)ring)->((A->A)#(A->A#num))->         (A->A#num)->bool"); pure (z11 == z12))) z9)) z6) else pure false))))) THEN ASM_REWRITE_TAC [ring_homomorphism_extensions, IN_ELIM_THM, I_THM] THEN CONV_TAC TAUT, ALL_TAC] THEN ASM_SIMP_TAC [] THEN MAP_EVERY X_GEN_TAC [(← q r"i:num"), (← q r"j:num")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(sig:num->A->A#num) i = sig j") MP_TAC THENL [MATCH_MP_TAC EXTENSIONAL_EQ THEN EXISTS_TAC (← q r"ring_carrier k:A->bool") THEN ASM_SIMP_TAC [] THEN MP_TAC (← ISPECL [(← q r"(sig:num->A->A#num) i"), (← q r"(sig:num->A->A#num) j"), (← q r"k:A ring"), (← q r"l:(A#num)ring"), (← q r"s UNION t:A->bool")] RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED) THEN ASM_SIMP_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC (← q r"x:A") THEN REWRITE_TAC [IN_UNION] THEN STRIP_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN ASM_REWRITE_TAC [], SUBGOAL_THEN (← q r"(x:A) IN ring_carrier(subfield_generated k t)") ASSUME_TAC THENL [MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN ASM_REWRITE_TAC [], ASM_SIMP_TAC []]], ASM_MESON_TAC []])

  let NUMBER_FIELD_COMPOSITUM_COORDINATES ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"j0:num"
    let q2 ← q r"{j:num | j < m}"
    let q3 ← q r"ring_of_int k d:A"
    let q4 ← q r"\j. ring_mul k ((c:num->num->A) i0 j) ((f:num->A) j)"
    let q5 ← q r"k:A ring"
    let v6 ← ISPECL [q5, q4, q3, q2] RING_SUM_LMUL
    let q10 ← q r"a IN s ==> (b:A) = a ==> b IN s"
    let r11 ← MESON [] q10
    let q12 ← q r"\j. ring_mul k (ring_of_int k d) ((c:num->num->A) i0 j)"
    let q13 ← q r"f:num->A"
    let q14 ← q r"m:num"
    let q15 ← q r"t:A->bool"
    let q16 ← q r"k:A ring"
    let v17 ← ISPECL [q16, q15, q14, q13, q12] NUMBER_FIELD_SUBFIELD_INTEGRAL_COORDINATES
    let q18 ← q r"ring_of_int k d IN ring_carrier (q:A ring)"
    let q19 ← q r"ring_carrier q subfield_of (k:A ring)"
    let q20 ← q r"ring_mul l D (ring_mul l D ((g:A->A#num)((x:num->A) i0))) IN
                  itg"
    let q21 ← q r"k:A ring"
    let q22 ← q r"(D:A#num) IN ring_carrier l"
    let q26 ← q r"(g:A->A#num) (ring_mul k (ring_of_int k d) ((x:num->A) i0)) =
      ring_mul l D (ring_mul l D (g(x i0)))"
    let q27 ← q r"(g:A->A#num) o ring_of_int k = ring_of_int l"
    let q28 ← q r"ring_mul k (ring_of_int k d) ((x:num->A) i0)"
    let q29 ← q r"g:A->A#num"
    let q30 ← q r"ring_of_int k:int->A"
    let q31 ← q r"l:(A#num)ring"
    let q32 ← q r"k:A ring"
    let q33 ← q r"integer_ring"
    let v34 ← ISPECL [q33, q32, q31, q30, q29, q28] INTEGRAL_ELEMENT_MONOMORPHIC_PREIMAGE
    let q35 ← q r"ring_mul k (ring_of_int k d) ((x:num->A) i0) IN
    ring_carrier(ring_of_integers k)"
    let q36 ← q r"(D:A#num) IN itg"
    let q52 ← q r"subfield_generated K {ring_0 K} = (q:A ring)"
    let v53 ← ASSUME q52
    let q64 ← q r"ring_of_int l d = ring_pow l (D:A#num) 2"
    let q65 ← q r"D = ring_det l {i | i < n}
          (\i j. (sig:num->A->A#num) i ((e:num->A) j))"
    let q66 ← q r"j0:num"
    let q67 ← q r"i0:num"
    let q80 ← q r"g:A->A#num"
    let q81 ← q r"sig:num->A->A#num"
    let q82 ← q r"e:num->A"
    let q83 ← q r"n:num"
    let q84 ← q r"l:(A#num)ring"
    let q85 ← q r"K:A ring"
    let v86 ← ISPECL [q85, q84, q83, q82, q81, q80] NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS
    let q87 ← q r"k:A ring"
    let q88 ← q r"\r. (sig:num->A->A#num) r alpha"
    let q89 ← q r"\i. (g:A->A#num) ((x:num->A) i)"
    let q90 ← q r"\r i. (sig:num->A->A#num) r ((e:num->A) i)"
    let q91 ← q r"{i:num | i < n}"
    let q92 ← q r"itg:A#num->bool"
    let q93 ← q r"l:(A#num)ring"
    let v94 ← ISPECL [q93, q92, q91, q90, q89, q88] RING_DET_CRAMER_SUBRING
    let q95 ← q r"!r i. r < n /\ i < n
          ==> (sig:num->A->A#num) r ((e:num->A) i) IN (itg:A#num->bool)"
    let q96 ← q r"(z:A) IN ring_carrier(ring_of_integers k)"
    let q97 ← q r"k:A ring"
    let q98 ← q r"ring_of_int l = (hh:A->A#num) o ring_of_int k"
    let q99 ← q r"!hh z:A. ring_homomorphism(k,l) hh /\
              z IN ring_carrier(ring_of_integers k)
              ==> hh z IN (itg:A#num->bool)"
    let q100 ← q r"(itg:A#num->bool) subring_of l"
    let q101 ← q r"itg = {z:A#num | integral_element (integer_ring,l) (ring_of_int l) z}"
    let q102 ← q r"i:num"
    let q103 ← q r"ring_homomorphism(k,l) ((sig:num->A->A#num) r)"
    let q110 ← q r"r:num"
    let q111 ← q r"!r. r < n
        ==> ring_sum l {i | i < n}
              (\i. ring_mul l ((sig:num->A->A#num) r ((e:num->A) i))
                              ((g:A->A#num) ((x:num->A) i))) =
            sig r alpha"
    let q125 ← q r"ring_mul r c (ring_mul r e f) = ring_mul r (ring_mul r c f) (e:A)"
    let r126 ← RING_RULE q125
    let q127 ← q r"j:num"
    let q128 ← q r"i:num"
    let q142 ← q r"ring_sum k {i | i < n}
      (\i. ring_mul k ((x:num->A) i) ((e:num->A) i)) = alpha"
    let q143 ← q r"j:num"
    let q144 ← q r"i:num"
    let q145 ← q r"!i. i < n ==> (x:num->A) i IN ring_carrier L"
    let q146 ← q r"x = \i. ring_sum k {j | j < m}
              (\j. ring_mul k ((c:num->num->A) i j) ((f:num->A) j))"
    let q147 ← q r"(!x:A. x IN ring_carrier K ==> x IN ring_carrier k) /\
    (!x:A. x IN ring_carrier L ==> x IN ring_carrier k) /\
    (!x:A. x IN ring_carrier q ==> x IN ring_carrier k)"
    let q148 ← q r"d = number_field_discriminant (K:A ring)"
    let q149 ← q r"q = subfield_generated k {ring_0 k:A}"
    let q150 ← q r"L = subfield_generated k (t:A->bool)"
    let q151 ← q r"K = subfield_generated k (s:A->bool)"
    let q152 ← q r"!hh:A->A#num. ring_homomorphism(k,l) hh
                  ==> ring_homomorphism(subfield_generated k s,l) hh"
    let q153 ← q r"s:A->bool"
    let q154 ← q r"k:A ring"
    let v155 ← ISPECL [q154, q153] PRIME_SUBFIELD_SUBFIELD_GENERATED
    let q156 ← q r"ring_carrier(subfield_generated k s) subfield_of (k:A ring) /\
    ring_carrier(subfield_generated k t) subfield_of (k:A ring) /\
    ring_carrier(subfield_generated k {ring_0 k}) SUBSET
    ring_carrier(subfield_generated k (s:A->bool)) /\
    ring_carrier(subfield_generated k {ring_0 k}) SUBSET
    ring_carrier(subfield_generated k (t:A->bool))"
    let q157 ← q r"sig:num->A->A#num"
    let q158 ← q r"g:A->A#num"
    let q159 ← q r"l:(A#num)ring"
    let q160 ← q r"t:A->bool"
    let q161 ← q r"s:A->bool"
    let q162 ← q r"k:A ring"
    let v163 ← ISPECL [q162, q161, q160] NUMBER_FIELD_COMPOSITUM_HOMOMORPHISMS
    let q164 ← q r"f:num->A"
    let q165 ← q r"m:num"
    let q166 ← q r"t:A->bool"
    let q167 ← q r"k:A ring"
    let v168 ← ISPECL [q167, q166, q165, q164] NUMBER_FIELD_SUBFIELD_INTEGRAL_BASIS
    let q169 ← q r"e:num->A"
    let q170 ← q r"n:num"
    let q171 ← q r"s:A->bool"
    let q172 ← q r"k:A ring"
    let v173 ← ISPECL [q172, q171, q170, q169] NUMBER_FIELD_SUBFIELD_INTEGRAL_BASIS
    prove
      r"!(k:A ring) s t n m e f alpha c.
          number_field k /\ subfield_generated k (s UNION t) = k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = n * m /\
          free_basis (integer_ring,ring_of_integers(subfield_generated k s))
                     (ring_of_int(subfield_generated k s)) n e /\
          free_basis (integer_ring,ring_of_integers(subfield_generated k t))
                     (ring_of_int(subfield_generated k t)) m f /\
          alpha IN ring_carrier(ring_of_integers k) /\
          (!i j. i < n /\ j < m
                 ==> c i j IN ring_carrier(subfield_generated k {ring_0 k})) /\
          alpha = ring_sum k {i | i < n}
                    (\i. ring_sum k {j | j < m}
                           (\j. ring_mul k (c i j) (ring_mul k (e i) (f j))))
          ==> !i j. i < n /\ j < m
                    ==> ?z. ring_mul k
                              (ring_of_int k (number_field_discriminant
                                                (subfield_generated k s)))
                              (c i j) =
                            ring_of_int k z"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN MP_TAC v173 THEN MP_TAC v168 THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN STRIP_TAC THEN MP_TAC v163 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN q159 (X_CHOOSE_THEN q158 (X_CHOOSE_THEN q157 STRIP_ASSUME_TAC))) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN SUBGOAL_THEN q156 STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED] THEN CONJ_TAC THEN MATCH_MP_TAC PRIME_SUBFIELD_MINIMAL THEN ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED], ALL_TAC] THEN MP_TAC v155 THEN DISCH_TAC THEN SUBGOAL_THEN q152 ASSUME_TAC THENL [REWRITE_TAC [RING_HOMOMORPHISM_FROM_SUBFIELD_GENERATED], ALL_TAC] THEN ABBREV_TAC q151 THEN ABBREV_TAC q150 THEN ABBREV_TAC q149 THEN ABBREV_TAC q148 THEN SUBGOAL_THEN q147 STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["K", "L", "q"] THEN MESON_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBSET], ALL_TAC] THEN ABBREV_TAC q146 THEN SUBGOAL_THEN q145 ASSUME_TAC THENL [X_GEN_TAC q144 THEN DISCH_TAC THEN EXPAND_TAC "x" THEN REWRITE_TAC [] THEN MATCH_MP_TAC IN_SUBFIELD_SUM THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC q143 THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN MATCH_MP_TAC IN_SUBFIELD_MUL THEN ASM_SIMP_TAC [] THEN ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN q142 ASSUME_TAC THENL [CONV_TAC SYM_CONV THEN FIRST_ASSUM (SUBST1_TAC o (checkM (fun th => (do if ← (do if ← (do let z129 ← (do let z130 ← (pure th); pure (concl z130)); pure (is_eq z129)) then (do let z134 ← (q r"alpha:A"); let z133 ← (do let z131 ← (do let z132 ← (pure th); pure (concl z132)); liftExcept (lhs z131)); pure (z133 == z134)) else pure false) then (do let z135 ← (do let z136 ← (pure th); pure (concl z136)); canM (fun z137 => (do let z138 ← (pure z137); find_termM (fun z139 => (do let z141 ← (pure z139); let z140 ← (q r"c:num->num->A"); pure (z140 == z141))) z138)) z135) else pure false)))) THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC q128 THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN EXPAND_TAC "x" THEN REWRITE_TAC [] THEN wPart rand (rand o rand) RING_SUM_RMUL THEN ANTS_TAC THENL [REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN ASM_SIMP_TAC [] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL THEN ASM_SIMP_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC q127 THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC [] THEN MATCH_MP_TAC r126 THEN ASM_SIMP_TAC [], ALL_TAC] THEN FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o (checkM (fun th => (do if ← (do if ← (do let z112 ← (do let z113 ← (pure th); pure (concl z113)); pure (is_eq z112)) then (do let z117 ← (q r"alpha:A"); let z116 ← (do let z114 ← (do let z115 ← (pure th); pure (concl z115)); liftExcept (lhs z114)); pure (z116 == z117)) else pure false) then (do let z118 ← (do let z119 ← (pure th); pure (concl z119)); canM (fun z120 => (do let z121 ← (pure z120); find_termM (fun z122 => (do let z124 ← (pure z122); let z123 ← (q r"c:num->num->A"); pure (z123 == z124))) z121)) z118) else pure false)))) THEN SUBGOAL_THEN q111 ASSUME_TAC THENL [X_GEN_TAC q110 THEN DISCH_TAC THEN FIRST_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z104 ← (do let z105 ← (pure th); pure (concl z105)); pure (is_eq z104)) then (do let z109 ← (q r"alpha:A"); let z108 ← (do let z106 ← (do let z107 ← (pure th); pure (concl z107)); liftExcept (rhs z106)); pure (z108 == z109)) else pure false))))) THEN SUBGOAL_THEN q103 ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN FIRST_ASSUM (fun th => tactic_of do pure (wPart rand (lhand o rand) (← MATCH_MP RING_HOMOMORPHISM_SUM th))) THEN ANTS_TAC THENL [REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL THEN ASM_SIMP_TAC [], DISCH_THEN SUBST1_TAC] THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC q102 THEN REWRITE_TAC [IN_ELIM_THM, o_THM] THEN DISCH_TAC THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL th)])) THEN MATCH_MP_TAC RING_MUL_SYM THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN ABBREV_TAC q101 THEN SUBGOAL_THEN q100 ASSUME_TAC THENL [EXPAND_TAC "itg" THEN MATCH_MP_TAC INTEGRAL_CLOSURE_SUBRING THEN REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT], ALL_TAC] THEN SUBGOAL_THEN q99 (LABEL_TAC "img") THENL [REPEAT STRIP_TAC THEN EXPAND_TAC "itg" THEN REWRITE_TAC [IN_ELIM_THM] THEN SUBGOAL_THEN q98 SUBST1_TAC THENL [REWRITE_TAC [FUN_EQ_THM, o_THM] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_RING_OF_INT], ALL_TAC] THEN MATCH_MP_TAC INTEGRAL_ELEMENT_HOMOMORPHIC_IMAGE THEN EXISTS_TAC q97 THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN UNDISCH_TAC q96 THEN REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM], ALL_TAC] THEN SUBGOAL_THEN q95 ASSUME_TAC THENL [REPEAT STRIP_TAC THEN USE_THEN "img" MATCH_MP_TAC THEN ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC v94 THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN EXISTS_TAC q87 THEN ASM_SIMP_TAC [], REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC] THEN MP_TAC v86 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN ASM_SIMP_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM ((fun th => tactic_of do pure (REWRITE_TAC [(← GSYM th)])) o (checkM (fun th => (do if ← (do let z71 ← (do let z72 ← (pure th); pure (concl z72)); pure (is_eq z71)) then (do let z73 ← (do let z74 ← (do let z75 ← (pure th); pure (concl z75)); liftExcept (lhs z74)); canM (fun z76 => (do let z79 ← (pure z76); let z78 ← (q r"ring_of_int k (d:int):A"); let z77 ← (pure []); term_match z77 z78 z79)) z73) else pure false)))) THEN FIRST_ASSUM ((fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_RING_OF_INT th)])) o (checkM (fun th => (do let z70 ← (q r"ring_homomorphism(k,l) (g:A->A#num)"); let z69 ← (do let z68 ← (pure th); pure (concl z68)); pure (z69 == z70))))) THEN DISCH_TAC THEN MAP_EVERY X_GEN_TAC [q67, q66] THEN STRIP_TAC THEN ABBREV_TAC q65 THEN SUBGOAL_THEN q64 ASSUME_TAC THENL [FIRST_ASSUM ACCEPT_TAC ORELSE FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do if ← (do if ← (do let z54 ← (do let z55 ← (pure th); pure (concl z55)); pure (is_eq z54)) then (do let z56 ← (do let z57 ← (do let z58 ← (pure th); pure (concl z58)); liftExcept (lhs z57)); pure (is_comb z56)) else pure false) then (do let z63 ← (q r"g:A->A#num"); let z62 ← (do let z59 ← (do let z60 ← (do let z61 ← (pure th); pure (concl z61)); liftExcept (lhs z60)); liftExcept (rator z59)); pure (z62 == z63)) else pure false)))) THEN REWRITE_TAC [v53] THEN FIRST_ASSUM ((fun th => tactic_of do pure (REWRITE_TAC [(← GSYM th)])) o (checkM (fun th => (do if ← (do let z46 ← (do let z47 ← (pure th); pure (concl z47)); pure (is_eq z46)) then (do let z51 ← (q r"ring_of_int k (d:int):A"); let z50 ← (do let z48 ← (do let z49 ← (pure th); pure (concl z49)); liftExcept (lhs z48)); pure (z50 == z51)) else pure false)))) THEN FIRST_ASSUM ((fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_RING_OF_INT th)])) o (checkM (fun th => (do let z45 ← (q r"ring_homomorphism(k,l) (g:A->A#num)"); let z44 ← (do let z43 ← (pure th); pure (concl z43)); pure (z44 == z45))))), ALL_TAC] THEN FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o (checkM (fun th => (do if ← (do let z37 ← (do let z38 ← (pure th); pure (concl z38)); pure (is_eq z37)) then (do let z42 ← (q r"ring_of_int k (d:int):A"); let z41 ← (do let z39 ← (do let z40 ← (pure th); pure (concl z40)); liftExcept (lhs z39)); pure (z41 == z42)) else pure false)))) THEN SUBGOAL_THEN q36 ASSUME_TAC THENL [EXPAND_TAC "D" THEN MATCH_MP_TAC RING_DET_SUBRING THEN ASM_SIMP_TAC [IN_ELIM_THM], ALL_TAC] THEN SUBGOAL_THEN q35 ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM] THEN MP_TAC v34 THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN CONJ_TAC THENL [MATCH_MP_TAC RING_MUL THEN ASM_SIMP_TAC [RING_OF_INT], ALL_TAC] THEN SUBGOAL_THEN q27 SUBST1_TAC THENL [REWRITE_TAC [FUN_EQ_THM, o_THM] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_RING_OF_INT], ALL_TAC] THEN SUBGOAL_THEN q26 SUBST1_TAC THENL [FIRST_ASSUM ((fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL th), (← MATCH_MP RING_HOMOMORPHISM_RING_OF_INT th), RING_OF_INT])) o (checkM (fun th => (do let z25 ← (q r"ring_homomorphism(k,l) (g:A->A#num)"); let z24 ← (do let z23 ← (pure th); pure (concl z23)); pure (z24 == z25))))) THEN SUBGOAL_THEN q22 ASSUME_TAC THENL [EXPAND_TAC "D" THEN REWRITE_TAC [RING_DET], ALL_TAC] THEN ASM_SIMP_TAC [RING_POW_2] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_MUL_ASSOC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN EXISTS_TAC q21 THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN q20 MP_TAC THENL [MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_SIMP_TAC [], EXPAND_TAC "itg" THEN REWRITE_TAC [IN_ELIM_THM]], ALL_TAC] THEN SUBGOAL_THEN q19 ASSUME_TAC THENL [EXPAND_TAC "q" THEN ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED], ALL_TAC] THEN SUBGOAL_THEN q18 ASSUME_TAC THENL [EXPAND_TAC "q" THEN REWRITE_TAC [RING_OF_INT_IN_SUBFIELD_GENERATED], ALL_TAC] THEN MP_TAC v17 THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [CONJ_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_SUBFIELD_MUL THEN ASM_SIMP_TAC [], ALL_TAC] THEN FIRST_X_ASSUM (MATCH_MP_TAC o ((MATCH_MP r11) o (checkM (fun th => (do let z9 ← (q r"ring_mul k (ring_of_int k d) ((x:num->A) i0) IN                    ring_carrier(ring_of_integers k)"); let z8 ← (do let z7 ← (pure th); pure (concl z7)); pure (z8 == z9)))))) THEN EXPAND_TAC "x" THEN REWRITE_TAC [] THEN MP_TAC v6 THEN ANTS_TAC THENL [REWRITE_TAC [RING_OF_INT, FINITE_NUMSEG_LT, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL THEN ASM_SIMP_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN REWRITE_TAC [] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_MUL_ASSOC THEN ASM_SIMP_TAC [RING_OF_INT], DISCH_THEN (MP_TAC o (SPEC q1)) THEN ASM_REWRITE_TAC []])

  -- @@RETURN BEGIN
  return { BASIS_DISCRIMINANT_PRODUCT_BASIS, NUMBER_FIELD_COMPOSITUM_HOMOMORPHISMS,
           NUMBER_FIELD_COMPOSITUM_COORDINATES }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- discriminant_compositum.ml phrases from line 1307 to 1926              -/
/- ---------------------------------------------------------------------- -/

structure DiscriminantCompositum03 where
  -- @@FIELDS
  NUMBER_FIELD_COMPOSITUM_DEGREE_GALOIS : thm
  NUMBER_FIELD_COMPOSITUM_DEGREE_COPRIME : thm
  NUMBER_FIELD_COMPOSITUM_INTEGRAL_BASIS : thm
  NUMBER_FIELD_COMPOSITUM_DISCRIMINANT : thm
  NUMBER_FIELD_COMPOSITUM_RING_OF_INTEGERS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDiscriminantCompositum03 [HolBase] (D : DiscriminantCompositumDeps) (BDiscriminantCompositum01 : DiscriminantCompositum01) (BDiscriminantCompositum02 : DiscriminantCompositum02) :
    ExceptT String IO DiscriminantCompositum03 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, MESON_TAC, RING_RULE, SET_RULE, SET_TAC, .. } := D
  let { BASIS_COORDINATES, DE_MORGAN_THM, DIVISION, EQ_MULT_RCANCEL, ETA_AX,
        EXISTS_IN_GSPEC, EXTENSION_DEGREE_REFL, EXTENSION_DEGREE_SUBFIELD_TOWER,
        FIELD_EXTENSION_SUBFIELD_GENERATED_SUBSET, FIELD_SUBFIELD_GENERATED,
        FINITE_NUMSEG_LT, FREE_BASIS_INDEPENDENT, FREE_BASIS_IN_CARRIER,
        GALOIS_COMPOSITUM_DEGREE, GALOIS_EXTENSION_GENERATED_CONJUGATES,
        GALOIS_GROUP_I, IMAGE_I, IMAGE_UNION, INTEGER_RING, INTER_SUBSET,
        INT_COPRIME_BEZOUT, INT_COPRIME_PRIME, INT_PRIME, IN_ELIM_THM, IN_SUBRING_INT,
        IN_SUBRING_MUL, IN_SUBRING_SUM, IN_UNION, IN_UNIONS, IN_UNIV, I_THM,
        LE_ANTISYM, LE_MULT_LCANCEL, LT, MOD_LT_EQ, MULT_ASSOC, MULT_CLAUSES, MULT_SYM,
        NUMBER_FIELD_DEGREE_POS, NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD,
        NUMBER_FIELD_GALOIS_CLOSURE_Q, NUMBER_FIELD_GALOIS_UNRAMIFIED_MONO,
        NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_NORMAL_CLOSURE_SPLITTING_TYPES,
        NUMBER_FIELD_SUBFIELD_DEGREE_POS, NUMBER_FIELD_SUBFIELD_GENERATED,
        NUMBER_FIELD_SUBFIELD_HOMOMORPHIC_IMAGE,
        NUMBER_FIELD_SUBFIELD_UNRAMIFIED_DISCRIMINANT,
        NUMBER_FIELD_UNRAMIFIED_RATIONAL, PRIME_SUBFIELD_SUBFIELD_GENERATED,
        RDIV_LT_EQ, RIGHT_IMP_EXISTS_THM, .. } := D.core1
  let { RING_0_IN_SUBFIELD_GENERATED, RING_CARRIER_SUBFIELD_GENERATED_SUBSET,
        RING_HOMOMORPHISM_SUBFIELD_INCLUSION, RING_MONOMORPHISM_IMP_HOMOMORPHISM,
        RING_MUL, RING_MUL_SYM, RING_OF_INT, RING_OF_INTEGERS, RING_OF_INTEGERS_FREE,
        RING_OF_INTEGERS_PRIME_SUBFIELD_PRIME_IDEAL,
        RING_OF_INTEGERS_SUBFIELD_GENERATED, RING_OF_INTEGERS_SUBRING,
        RING_OF_INTEGERS_SUBSET, RING_OF_INT_1, RING_OF_INT_ADD,
        RING_OF_INT_EQ_0_CHAR_0, RING_OF_INT_EQ_CHAR_0,
        RING_OF_INT_IN_RING_OF_INTEGERS, RING_OF_INT_IN_SUBFIELD_GENERATED,
        RING_OF_INT_MUL, RING_OF_INT_POW, RING_SUM_EQ, RING_SUM_PRODUCT_INDEX,
        RING_SUM_RING_OF_INTEGERS, RING_SUM_SWAP, SING_SUBSET, SKOLEM_THM,
        SUBFIELD_GENERATED, SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED,
        SUBFIELD_GENERATED_IDEMPOT, SUBFIELD_GENERATED_IDEMPOT_GEN,
        SUBFIELD_GENERATED_MINIMAL, SUBFIELD_GENERATED_MONO,
        SUBFIELD_GENERATED_RESTRICT, SUBFIELD_GENERATED_SUBSET_EQ,
        SUBFIELD_GENERATED_UNION, SUBFIELD_SUBFIELD_GENERATED, SUBRING_GENERATED_INC,
        SUBRING_GENERATED_MINIMAL, SUBRING_SUBRING_GENERATED, SUBSET, SUBSET_ANTISYM,
        SUBSET_CARRIER_SUBFIELD_GENERATED, SUBSET_TRANS, UNION_COMM, UNION_OVER_INTER,
        UNION_SUBSET, field_extension, free_basis, number_field, .. } := D.core2
  let { NUMBER_FIELD_COMPOSITUM_DEGREE_LE, NUMBER_FIELD_COMPOSITUM_PRODUCT_BASIS,
        NUMBER_FIELD_SUBFIELD_INTEGRAL_BASIS, .. } := BDiscriminantCompositum01
  let { BASIS_DISCRIMINANT_PRODUCT_BASIS, NUMBER_FIELD_COMPOSITUM_COORDINATES, .. } := BDiscriminantCompositum02
  -- @@SCOPE END

  let NUMBER_FIELD_COMPOSITUM_DEGREE_GALOIS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"x:num = x * 1")
    let r2 ← ARITH_RULE (← q r"1 <= b <=> ~(b:num = 0)")
    prove
      r"!(m:A ring) s t.
          number_field m /\
          galois_extension(subfield_generated m {ring_0 m},m) I /\
          coprime(number_field_discriminant(subfield_generated m s),
                  number_field_discriminant(subfield_generated m t))
          ==> extension_degree(subfield_generated m {ring_0 m},
                               subfield_generated m (s UNION t)) I =
              extension_degree(subfield_generated m {ring_0 m},
                               subfield_generated m s) I *
              extension_degree(subfield_generated m {ring_0 m},
                               subfield_generated m t) I"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [number_field])) THEN ABBREV_TAC (← q r"Q = subfield_generated m {ring_0 m:A}") THEN ABBREV_TAC (← q r"K = ring_carrier(subfield_generated m (s:A->bool))") THEN ABBREV_TAC (← q r"L = ring_carrier(subfield_generated m (t:A->bool))") THEN ABBREV_TAC (← q r"KL = ring_carrier(subfield_generated m (s UNION t:A->bool))") THEN ABBREV_TAC (← q r"N = UNIONS {IMAGE f L |
                  f IN group_carrier(galois_group(Q,m) (I:A->A))}") THEN SUBGOAL_THEN (← q r"subfield_generated m (s:A->bool) = subfield_generated m K /\
      subfield_generated m (t:A->bool) = subfield_generated m L /\
      subfield_generated m (s UNION t:A->bool) = subfield_generated m KL") (fun th => ONCE_REWRITE_TAC [th]) THENL [MAP_EVERY EXPAND_TAC ["K", "L", "KL"] THEN REWRITE_TAC [SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_carrier Q SUBSET (K:A->bool) /\ ring_carrier Q SUBSET L /\
      K SUBSET KL /\ L SUBSET KL /\
      K SUBSET ring_carrier m /\ L SUBSET ring_carrier m /\
      KL SUBSET ring_carrier m") STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["Q", "K", "L", "KL"] THEN REWRITE_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET] THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED, SING_SUBSET, (← ASSUME (← q r"field(m:A ring)")), RING_0_IN_SUBFIELD_GENERATED], MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED, SING_SUBSET, (← ASSUME (← q r"field(m:A ring)")), RING_0_IN_SUBFIELD_GENERATED], MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN SET_TAC [], MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN SET_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"subfield_generated (m:A ring) (ring_carrier Q) = Q") ASSUME_TAC THENL [EXPAND_TAC "Q" THEN REWRITE_TAC [SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"Q:A ring"), (← q r"m:A ring"), (← q r"L:A->bool")] GALOIS_EXTENSION_GENERATED_CONJUGATES) THEN ASM_REWRITE_TAC [IMAGE_I] THEN STRIP_TAC THEN ABBREV_TAC (← q r"Nf = subfield_generated m (N:A->bool)") THEN SUBGOAL_THEN (← q r"(L:A->bool) SUBSET ring_carrier Nf /\
      ring_carrier Nf SUBSET ring_carrier (m:A ring) /\
      ring_carrier Nf subfield_of m /\
      subfield_generated m (ring_carrier Nf) = Nf") STRIP_ASSUME_TAC THENL [EXPAND_TAC "Nf" THEN SIMP_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED, SUBFIELD_SUBFIELD_GENERATED, (← ASSUME (← q r"field(m:A ring)"))] THEN MATCH_MP_TAC SUBSET_CARRIER_SUBFIELD_GENERATED THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "N" THEN REWRITE_TAC [SUBSET, IN_UNIONS, EXISTS_IN_GSPEC] THEN X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN EXISTS_TAC (← q r"I:A->A") THEN ASM_REWRITE_TAC [GALOIS_GROUP_I, IMAGE_I], ALL_TAC] THEN SUBGOAL_THEN (← q r"field(Q:A ring) /\ ring_homomorphism(Q,m) (I:A->A) /\
      ring_0 Q = ring_0 m /\ number_field(subfield_generated m (K:A->bool)) /\
      number_field(subfield_generated m (L:A->bool))") STRIP_ASSUME_TAC THENL [EXPAND_TAC "Q" THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, SUBFIELD_GENERATED, NUMBER_FIELD_SUBFIELD_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"coprime(number_field_discriminant(subfield_generated (m:A ring) K),
              number_field_discriminant(subfield_generated m L))") ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["K", "L"] THEN ASM_REWRITE_TAC [SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED], ALL_TAC] THEN ABBREV_TAC (← q r"M = subfield_generated m (ring_carrier Nf INTER (K:A->bool))") THEN SUBGOAL_THEN (← q r"!p. prime_ideal (ring_of_integers Q) p /\ ~(p = {ring_0 Q})
          ==> unramified (ring_of_integers Q,ring_of_integers M) (I:A->A) p") ASSUME_TAC THENL [X_GEN_TAC (← q r"p:A->bool") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"~(p = {ring_0(m:A ring)})") ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"m:A ring"), (← q r"p:A->bool")] RING_OF_INTEGERS_PRIME_SUBFIELD_PRIME_IDEAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"q:num") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"&q:int"), (← q r"number_field_discriminant
                        (subfield_generated m (K:A->bool))"), (← q r"number_field_discriminant
                        (subfield_generated m (L:A->bool))")] INT_COPRIME_PRIME) THEN ASM_REWRITE_TAC [INT_PRIME, DE_MORGAN_THM] THEN FIRST_X_ASSUM (SUBST_ALL_TAC o (checkM (fun th => (do if ← (do let z9 ← (do let z10 ← (pure th); pure (concl z10)); pure (is_eq z9)) then (do let z14 ← (q r"p:A->bool"); let z13 ← (do let z11 ← (do let z12 ← (pure th); pure (concl z12)); liftExcept (lhs z11)); pure (z13 == z14)) else pure false)))) THEN STRIP_TAC THEN EXPAND_TAC "M" THEN MATCH_MP_TAC NUMBER_FIELD_GALOIS_UNRAMIFIED_MONO THENL [EXISTS_TAC (← q r"K:A->bool") THEN ASM_REWRITE_TAC [IMAGE_I] THEN REPEAT CONJ_TAC THENL [SET_TAC [], UNDISCH_TAC (← q r"ring_carrier Q SUBSET (L:A->bool)") THEN UNDISCH_TAC (← q r"(L:A->bool) SUBSET ring_carrier Nf") THEN UNDISCH_TAC (← q r"ring_carrier Q SUBSET (K:A->bool)") THEN SET_TAC [], MP_TAC (← ISPECL [(← q r"m:A ring"), (← q r"K:A->bool"), (← q r"q:num")] NUMBER_FIELD_SUBFIELD_UNRAMIFIED_DISCRIMINANT) THEN ASM_REWRITE_TAC []], EXISTS_TAC (← q r"ring_carrier(Nf:A ring)") THEN ASM_REWRITE_TAC [IMAGE_I] THEN REPEAT CONJ_TAC THENL [SET_TAC [], UNDISCH_TAC (← q r"ring_carrier Q SUBSET (L:A->bool)") THEN UNDISCH_TAC (← q r"(L:A->bool) SUBSET ring_carrier Nf") THEN UNDISCH_TAC (← q r"ring_carrier Q SUBSET (K:A->bool)") THEN SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"Q:A ring"), (← q r"m:A ring"), (← q r"L:A->bool"), (← q r"ideal_generated (ring_of_integers Q) {ring_of_num m q:A}")] NUMBER_FIELD_NORMAL_CLOSURE_SPLITTING_TYPES) THEN ASM_REWRITE_TAC [IMAGE_I] THEN DISCH_THEN (SUBST1_TAC o CONJUNCT1) THEN MP_TAC (← ISPECL [(← q r"m:A ring"), (← q r"L:A->bool"), (← q r"q:num")] NUMBER_FIELD_SUBFIELD_UNRAMIFIED_DISCRIMINANT) THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"extension_degree(Q,M) (I:A->A) = 1") ASSUME_TAC THENL [MATCH_MP_TAC NUMBER_FIELD_UNRAMIFIED_RATIONAL THEN ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL [EXPAND_TAC "M" THEN ASM_SIMP_TAC [NUMBER_FIELD_SUBFIELD_GENERATED], SUBST1_TAC (← SYM (← ASSUME (← q r"subfield_generated m {ring_0 m:A} = Q"))) THEN EXPAND_TAC "M" THEN SUBGOAL_THEN (← q r"field_extension(subfield_generated m {ring_0 m},
                          subfield_generated m (ring_carrier Nf INTER K))
                         (I:A->A)") MP_TAC THENL [MATCH_MP_TAC FIELD_EXTENSION_SUBFIELD_GENERATED_SUBSET THEN REWRITE_TAC [(← ASSUME (← q r"field(m:A ring)"))] THEN TRANS_TAC SUBSET_TRANS (← q r"ring_carrier Nf INTER (K:A->bool)") THEN CONJ_TAC THENL [ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"ring_carrier Q SUBSET (L:A->bool)") THEN UNDISCH_TAC (← q r"(L:A->bool) SUBSET ring_carrier Nf") THEN UNDISCH_TAC (← q r"ring_carrier Q SUBSET (K:A->bool)") THEN SET_TAC [], MATCH_MP_TAC SUBSET_CARRIER_SUBFIELD_GENERATED THEN ASM SET_TAC []], SIMP_TAC [field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM]], SUBST1_TAC (← SYM (← ASSUME (← q r"subfield_generated m {ring_0 m:A} = Q"))) THEN REWRITE_TAC [SUBFIELD_GENERATED_IDEMPOT] THEN ASM_SIMP_TAC [EXTENSION_DEGREE_REFL, FIELD_SUBFIELD_GENERATED]], ALL_TAC] THEN SUBGOAL_THEN (← q r"(K:A->bool) subfield_of m /\ KL subfield_of m /\ L subfield_of m") STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["K", "L", "KL"] THEN ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"Q:A ring"), (← q r"m:A ring"), (← q r"ring_carrier(Nf:A ring)"), (← q r"K:A->bool")] GALOIS_COMPOSITUM_DEGREE) THEN ASM_REWRITE_TAC [IMAGE_I] THEN ANTS_TAC THENL [UNDISCH_TAC (← q r"ring_carrier Q SUBSET (L:A->bool)") THEN UNDISCH_TAC (← q r"(L:A->bool) SUBSET ring_carrier Nf") THEN SET_TAC [], DISCH_THEN (ASSUME_TAC o CONJUNCT1)] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"Q:A ring"), (← q r"m:A ring"), (← q r"ring_carrier(Nf:A ring)"), (← q r"KL:A->bool")] GALOIS_COMPOSITUM_DEGREE) THEN ASM_REWRITE_TAC [IMAGE_I] THEN ANTS_TAC THENL [CONJ_TAC THENL [UNDISCH_TAC (← q r"ring_carrier Q SUBSET (L:A->bool)") THEN UNDISCH_TAC (← q r"(L:A->bool) SUBSET ring_carrier Nf") THEN SET_TAC [], UNDISCH_TAC (← q r"ring_carrier Q SUBSET (K:A->bool)") THEN UNDISCH_TAC (← q r"(K:A->bool) SUBSET KL") THEN SET_TAC []], DISCH_THEN (ASSUME_TAC o CONJUNCT1)] THEN SUBGOAL_THEN (← q r"ring_carrier(subfield_generated m K) = (K:A->bool) /\
      ring_carrier(subfield_generated m L) = (L:A->bool) /\
      ring_carrier(subfield_generated m KL) = (KL:A->bool) /\
      ring_carrier(subfield_generated m (K UNION L)) = (KL:A->bool) /\
      ring_carrier(subfield_generated m (ring_carrier Nf)) = ring_carrier Nf") STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC [] THEN MAP_EVERY EXPAND_TAC ["K", "L", "KL"] THEN REWRITE_TAC [SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED, SUBFIELD_GENERATED_UNION], ALL_TAC] THEN SUBGOAL_THEN (← q r"!X:A->bool. ring_carrier Q SUBSET ring_carrier(subfield_generated m X)") ASSUME_TAC THENL [GEN_TAC THEN SUBST1_TAC (← SYM (← ASSUME (← q r"subfield_generated m {ring_0 m:A} = Q"))) THEN MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED, SING_SUBSET, (← ASSUME (← q r"field(m:A ring)")), RING_0_IN_SUBFIELD_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"(KL:A->bool) SUBSET
      ring_carrier(subfield_generated (m:A ring) (ring_carrier Nf UNION K))") ASSUME_TAC THENL [FIRST_ASSUM ((fun th => tactic_of do pure (GEN_REWRITE_TAC LAND_CONV [(← SYM th)])) o (checkM (fun th => (do let z8 ← (q r"ring_carrier(subfield_generated (m:A ring) (K UNION L))"); let z7 ← (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); liftExcept (lhs z5)); pure (z7 == z8))))) THEN MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED] THEN MATCH_MP_TAC SUBSET_CARRIER_SUBFIELD_GENERATED THEN ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"subfield_generated (m:A ring) (ring_carrier Nf UNION KL) =
      subfield_generated m (ring_carrier Nf UNION K)") (fun th => RULE_ASSUM_TAC (REWRITE_RULE [th])) THENL [MATCH_MP_TAC SUBFIELD_GENERATED_SUBSET_EQ THEN REWRITE_TAC [(← ASSUME (← q r"field(m:A ring)")), UNION_SUBSET] THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC SUBSET_CARRIER_SUBFIELD_GENERATED THEN ASM_REWRITE_TAC [] THEN SET_TAC [], FIRST_ASSUM ACCEPT_TAC, MATCH_MP_TAC SUBSET_CARRIER_SUBFIELD_GENERATED THEN ASM_REWRITE_TAC [] THEN SET_TAC [], MATCH_MP_TAC SUBSET_CARRIER_SUBFIELD_GENERATED THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"(K:A->bool) SUBSET KL") THEN SET_TAC []], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"m:A ring"), (← q r"{ring_0 m:A}"), (← q r"ring_carrier Nf INTER (K:A->bool)"), (← q r"ring_carrier(Nf:A ring)")] EXTENSION_DEGREE_SUBFIELD_TOWER) THEN ANTS_TAC THENL [REWRITE_TAC [(← ASSUME (← q r"field(m:A ring)"))] THEN CONJ_TAC THENL [SUBST1_TAC (← ASSUME (← q r"subfield_generated m {ring_0 m:A} = Q")) THEN FIRST_ASSUM MATCH_ACCEPT_TAC, MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN SET_TAC []], ASM_REWRITE_TAC [] THEN DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"m:A ring"), (← q r"K:A->bool"), (← q r"KL:A->bool"), (← q r"ring_carrier Nf UNION (K:A->bool)")] EXTENSION_DEGREE_SUBFIELD_TOWER) THEN ANTS_TAC THENL [REWRITE_TAC [(← ASSUME (← q r"field(m:A ring)"))] THEN CONJ_TAC THENL [MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN FIRST_ASSUM ACCEPT_TAC, ASM_REWRITE_TAC []], ASM_REWRITE_TAC [] THEN DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"m:A ring"), (← q r"L:A->bool"), (← q r"ring_carrier Nf INTER (KL:A->bool)"), (← q r"ring_carrier(Nf:A ring)")] EXTENSION_DEGREE_SUBFIELD_TOWER) THEN ANTS_TAC THENL [REWRITE_TAC [(← ASSUME (← q r"field(m:A ring)"))] THEN CONJ_TAC THEN MATCH_MP_TAC SUBFIELD_GENERATED_MONO THENL [UNDISCH_TAC (← q r"(L:A->bool) SUBSET KL") THEN UNDISCH_TAC (← q r"(L:A->bool) SUBSET ring_carrier Nf") THEN SET_TAC [], SET_TAC []], ASM_REWRITE_TAC [] THEN DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"m:A ring"), (← q r"{ring_0 m:A}"), (← q r"L:A->bool"), (← q r"ring_carrier(Nf:A ring)")] EXTENSION_DEGREE_SUBFIELD_TOWER) THEN ANTS_TAC THENL [REWRITE_TAC [(← ASSUME (← q r"field(m:A ring)"))] THEN CONJ_TAC THENL [SUBST1_TAC (← ASSUME (← q r"subfield_generated m {ring_0 m:A} = Q")) THEN FIRST_ASSUM MATCH_ACCEPT_TAC, MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN FIRST_ASSUM ACCEPT_TAC], ASM_REWRITE_TAC [] THEN DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"m:A ring"), (← q r"{ring_0 m:A}"), (← q r"K:A->bool"), (← q r"KL:A->bool")] EXTENSION_DEGREE_SUBFIELD_TOWER) THEN ANTS_TAC THENL [REWRITE_TAC [(← ASSUME (← q r"field(m:A ring)"))] THEN CONJ_TAC THENL [SUBST1_TAC (← ASSUME (← q r"subfield_generated m {ring_0 m:A} = Q")) THEN FIRST_ASSUM MATCH_ACCEPT_TAC, MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN FIRST_ASSUM ACCEPT_TAC], ASM_REWRITE_TAC [] THEN DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"m:A ring"), (← q r"ring_carrier Nf INTER (KL:A->bool)"), (← q r"ring_carrier(Nf:A ring)")] NUMBER_FIELD_SUBFIELD_DEGREE_POS) THEN MP_TAC (← ISPECL [(← q r"m:A ring"), (← q r"L:A->bool"), (← q r"ring_carrier Nf INTER (KL:A->bool)")] NUMBER_FIELD_SUBFIELD_DEGREE_POS) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [MATCH_MP_TAC SUBSET_CARRIER_SUBFIELD_GENERATED THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"(L:A->bool) SUBSET KL") THEN UNDISCH_TAC (← q r"(L:A->bool) SUBSET ring_carrier Nf") THEN SET_TAC [], DISCH_TAC] THEN ANTS_TAC THENL [MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [] THEN SET_TAC [], DISCH_TAC] THEN SUBGOAL_THEN (← q r"subfield_generated (subfield_generated m KL) (K:A->bool) =
      subfield_generated m K /\
      subfield_generated (subfield_generated m KL) (L:A->bool) =
      subfield_generated m L /\
      subfield_generated (subfield_generated m KL) (K UNION L:A->bool) =
      subfield_generated m KL") STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THEN W (fun (_, w) => tactic_of do pure (MP_TAC (← ISPECL [(← q r"m:A ring"), (← (do let z3 ← (do let z4 ← (pure w); liftExcept (lhs z4)); liftExcept (rand z3))), (← q r"KL:A->bool")] SUBFIELD_GENERATED_IDEMPOT_GEN))) THEN ASM_REWRITE_TAC [] THEN (ANTS_TAC THENL [ASM SET_TAC [], DISCH_THEN SUBST1_TAC]) THEN TRY (ONCE_REWRITE_TAC [(← GSYM SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED)] THEN ASM_REWRITE_TAC []) THEN NO_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"subfield_generated m (KL:A->bool)"), (← q r"K:A->bool"), (← q r"L:A->bool")] NUMBER_FIELD_COMPOSITUM_DEGREE_LE) THEN ASM_SIMP_TAC [NUMBER_FIELD_SUBFIELD_GENERATED, PRIME_SUBFIELD_SUBFIELD_GENERATED] THEN ABBREV_TAC (← q r"a = extension_degree (subfield_generated m K,
                                      subfield_generated m (KL:A->bool)) I") THEN ABBREV_TAC (← q r"b = extension_degree
                      (subfield_generated m (ring_carrier Nf INTER (KL:A->bool)),
                       Nf) I") THEN ABBREV_TAC (← q r"d = extension_degree
                      (subfield_generated m (L:A->bool),
                       subfield_generated m (ring_carrier Nf INTER (KL:A->bool)))
                      I") THEN ABBREV_TAC (← q r"dK = extension_degree (Q,subfield_generated m (K:A->bool)) I") THEN ABBREV_TAC (← q r"dL = extension_degree (Q,subfield_generated m (L:A->bool)) I") THEN SUBGOAL_THEN (← q r"a = (dL:num) * d") SUBST1_TAC THENL [UNDISCH_TAC (← q r"1 * a * b = (dL:num) * d * b") THEN UNDISCH_TAC (← q r"1 <= b:num") THEN REWRITE_TAC [MULT_CLAUSES, MULT_ASSOC, EQ_MULT_RCANCEL] THEN REWRITE_TAC [r2] THEN MESON_TAC [], ALL_TAC] THEN REWRITE_TAC [MULT_ASSOC] THEN DISCH_TAC THEN REWRITE_TAC [(← GSYM LE_ANTISYM)] THEN ASM_REWRITE_TAC [] THEN GEN_REWRITE_TAC LAND_CONV [r1] THEN REWRITE_TAC [LE_MULT_LCANCEL] THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_COMPOSITUM_DEGREE_COPRIME ← prove
    r"!(k:A ring) s t.
        number_field k /\
        coprime(number_field_discriminant(subfield_generated k s),
                number_field_discriminant(subfield_generated k t))
        ==> extension_degree(subfield_generated k {ring_0 k},
                             subfield_generated k (s UNION t)) I =
            extension_degree(subfield_generated k {ring_0 k},
                             subfield_generated k s) I *
            extension_degree(subfield_generated k {ring_0 k},
                             subfield_generated k t) I"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN MP_TAC (← ISPEC (← q r"k:A ring") NUMBER_FIELD_GALOIS_CLOSURE_Q) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"m:(A#num)ring") (X_CHOOSE_THEN (← q r"j:A->A#num") STRIP_ASSUME_TAC)) THEN SUBGOAL_THEN (← q r"field(m:(A#num)ring)") ASSUME_TAC THENL [ASM_SIMP_TAC [NUMBER_FIELD_IMP_FIELD], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"m:(A#num)ring"), (← q r"IMAGE (j:A->A#num) (ring_carrier k INTER s)"), (← q r"IMAGE (j:A->A#num) (ring_carrier k INTER t)")] NUMBER_FIELD_COMPOSITUM_DEGREE_GALOIS) THEN REWRITE_TAC [(← GSYM IMAGE_UNION), (← GSYM UNION_OVER_INTER)] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"m:(A#num)ring"), (← q r"j:A->A#num"), (← q r"ring_carrier k INTER (s:A->bool)")] NUMBER_FIELD_SUBFIELD_HOMOMORPHIC_IMAGE) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"m:(A#num)ring"), (← q r"j:A->A#num"), (← q r"ring_carrier k INTER (t:A->bool)")] NUMBER_FIELD_SUBFIELD_HOMOMORPHIC_IMAGE) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"m:(A#num)ring"), (← q r"j:A->A#num"), (← q r"ring_carrier k INTER (s UNION t:A->bool)")] NUMBER_FIELD_SUBFIELD_HOMOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [INTER_SUBSET, (← GSYM SUBFIELD_GENERATED_RESTRICT)] THEN REPEAT (DISCH_THEN (CONJUNCTS_THEN SUBST1_TAC)) THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_COMPOSITUM_INTEGRAL_BASIS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r14 ← RING_RULE (← q r"ring_add r (ring_mul r dk a) (ring_mul r dl b) = ring_1 r
        ==> c = ring_add r (ring_mul r a (ring_mul r dk c))
                           (ring_mul r b (ring_mul r dl (c:A)))")
    let r52 ← SET_RULE (← q r"!s. x IN s /\ s SUBSET t ==> (x:A) IN t")
    let r53 ← SET_RULE (← q r"!s. x IN s /\ s SUBSET t ==> (x:A) IN t")
    prove
      r"!(k:A ring) s t n m e f.
          number_field k /\ subfield_generated k (s UNION t) = k /\
          coprime(number_field_discriminant(subfield_generated k s),
                  number_field_discriminant(subfield_generated k t)) /\
          free_basis (integer_ring,ring_of_integers(subfield_generated k s))
                     (ring_of_int(subfield_generated k s)) n e /\
          free_basis (integer_ring,ring_of_integers(subfield_generated k t))
                     (ring_of_int(subfield_generated k t)) m f
          ==> free_basis (integer_ring,ring_of_integers k) (ring_of_int k)
                (n * m) (\u. ring_mul k (e(u MOD n)) (f(u DIV n))) /\
              number_field_discriminant k =
              number_field_discriminant(subfield_generated k s) pow m *
              number_field_discriminant(subfield_generated k t) pow n"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"s:A->bool"), (← q r"t:A->bool")] NUMBER_FIELD_COMPOSITUM_DEGREE_COPRIME) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"s:A->bool"), (← q r"n:num"), (← q r"e:num->A")] NUMBER_FIELD_SUBFIELD_INTEGRAL_BASIS) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"t:A->bool"), (← q r"m:num"), (← q r"f:num->A")] NUMBER_FIELD_SUBFIELD_INTEGRAL_BASIS) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN STRIP_TAC THEN RULE_ASSUM_TAC (fun th => do do let c ← (do let z61 ← (pure th); pure (concl z61)); pure (← do if ← (do if ← (do let z54 ← (pure c); pure (is_eq z54)) then (do let z55 ← (do let z56 ← (pure c); liftExcept (lhs z56)); canM (fun z57 => (do let z60 ← (pure z57); let z59 ← (q r"ring_of_int k (x:int):A"); let z58 ← (pure []); term_match z58 z59 z60)) z55) else pure false) then pure (← SYM th) else pure th)) THEN SUBGOAL_THEN (← q r"extension_degree (subfield_generated k {ring_0 k},k) (I:A->A) = n * m") ASSUME_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"s:A->bool"), (← q r"t:A->bool"), (← q r"n:num"), (← q r"m:num"), (← q r"e:num->A"), (← q r"f:num->A")] NUMBER_FIELD_COMPOSITUM_PRODUCT_BASIS) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"~(n = 0) /\ ~(m = 0)") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"k:A ring") NUMBER_FIELD_DEGREE_POS) THEN ASM_REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN ASM_CASES_TAC (← q r"m = 0") THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"!u. u < n * m ==> u MOD n < n /\ u DIV n < m /\
                        u MOD n + n * u DIV n = u") ASSUME_TAC THENL [ASM_SIMP_TAC [MOD_LT_EQ, RDIV_LT_EQ] THEN REPEAT STRIP_TAC THEN MP_TAC (← SPECL [(← q r"u:num"), (← q r"n:num")] DIVISION) THEN ASM_REWRITE_TAC [] THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_carrier(ring_of_integers k) subring_of (k:A ring)") ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_SUBRING], ALL_TAC] THEN ABBREV_TAC (← q r"B = \u. ring_mul k ((e:num->A)(u MOD n)) (f(u DIV n))") THEN SUBGOAL_THEN (← q r"!u. u < n * m ==> (B:num->A) u IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [EXPAND_TAC "B" THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!alpha. alpha IN ring_carrier(ring_of_integers k)
              ==> ?w. alpha = ring_sum k {u | u < n * m}
                                (\u. ring_mul k (ring_of_int k (w u))
                                                ((B:num->A) u))") (LABEL_TAC "span") THENL [X_GEN_TAC (← q r"alpha:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(alpha:A) IN ring_carrier k") ASSUME_TAC THENL [MATCH_MP_TAC r53 THEN EXISTS_TAC (← q r"ring_carrier(ring_of_integers k:A ring)") THEN ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"n * m:num"), (← q r"B:num->A"), (← q r"alpha:A")] BASIS_COORDINATES) THEN ASM_REWRITE_TAC [I_THM] THEN ABBREV_TAC (← q r"c = basis_coordinates (subfield_generated k {ring_0 k},k) (I:A->A)
              (n * m) (B:num->A) alpha") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(!i. i < n ==> (e:num->A) i IN ring_carrier k) /\
        (!j. j < m ==> (f:num->A) j IN ring_carrier k) /\
        (!u. (c:num->A) u IN ring_carrier k)") STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC r52 THENL [EXISTS_TAC (← q r"ring_carrier(ring_of_integers k:A ring)") THEN ASM_SIMP_TAC [RING_OF_INTEGERS_SUBSET], EXISTS_TAC (← q r"ring_carrier(ring_of_integers k:A ring)") THEN ASM_SIMP_TAC [RING_OF_INTEGERS_SUBSET], EXISTS_TAC (← q r"ring_carrier(subfield_generated k {ring_0 k:A})") THEN ASM_REWRITE_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET]], ALL_TAC] THEN SUBGOAL_THEN (← q r"alpha = ring_sum k {i | i < n}
                  (\i. ring_sum k {j | j < m}
                         (\j. ring_mul k ((c:num->A) (i + n * j))
                                         (ring_mul k ((e:num->A) i) (f j))))") ASSUME_TAC THENL [FIRST_ASSUM ((fun th => tactic_of do pure (GEN_REWRITE_TAC LAND_CONV [(← SYM th)])) o (checkM (fun th => (do if ← (do if ← (do let z39 ← (do let z40 ← (pure th); pure (concl z40)); pure (is_eq z39)) then (do let z44 ← (q r"alpha:A"); let z43 ← (do let z41 ← (do let z42 ← (pure th); pure (concl z42)); liftExcept (rhs z41)); pure (z43 == z44)) else pure false) then (do let z45 ← (do let z46 ← (pure th); pure (concl z46)); canM (fun z47 => (do let z48 ← (pure z47); find_termM (fun z49 => (do let z51 ← (pure z49); let z50 ← (q r"B:num->A"); pure (z50 == z51))) z48)) z45) else pure false)))) THEN EXPAND_TAC "B" THEN REWRITE_TAC [] THEN MATCH_MP_TAC RING_SUM_PRODUCT_INDEX THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"s:A->bool"), (← q r"t:A->bool"), (← q r"n:num"), (← q r"m:num"), (← q r"e:num->A"), (← q r"f:num->A"), (← q r"alpha:A"), (← q r"\i j. (c:num->A) (i + n * j)")] NUMBER_FIELD_COMPOSITUM_COORDINATES) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (LABEL_TAC "zK")] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"t:A->bool"), (← q r"s:A->bool"), (← q r"m:num"), (← q r"n:num"), (← q r"f:num->A"), (← q r"e:num->A"), (← q r"alpha:A"), (← q r"\j i. (c:num->A) (i + n * j)")] NUMBER_FIELD_COMPOSITUM_COORDINATES) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL [ONCE_REWRITE_TAC [UNION_COMM] THEN ASM_REWRITE_TAC [], REWRITE_TAC [MULT_SYM], MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"\i j. ring_mul k ((c:num->A) (i + n * j))
                     (ring_mul k ((e:num->A) i) ((f:num->A) j))"), (← q r"{i:num | i < n}"), (← q r"{j:num | j < m}")] RING_SUM_SWAP) THEN REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, ETA_AX] THEN ANTS_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL THEN ASM_SIMP_TAC [RING_MUL], DISCH_THEN SUBST1_TAC] THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"j:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC [] THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"i:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC [] THEN AP_TERM_TAC THEN MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC []], DISCH_THEN (LABEL_TAC "zL")] THEN FIRST_ASSUM (MP_TAC o ((GEN_REWRITE_RULE id [INT_COPRIME_BEZOUT]) o (checkM (fun th => (do let z33 ← (do let z34 ← (pure th); pure (concl z34)); canM (fun z35 => (do let z38 ← (pure z35); let z37 ← (q r"coprime(a:int,b)"); let z36 ← (pure []); term_match z36 z37 z38)) z33))))) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:int") (X_CHOOSE_TAC (← q r"b:int"))) THEN SUBGOAL_THEN (← q r"!u. u < n * m ==> ?z. (c:num->A) u = ring_of_int k z") MP_TAC THENL [X_GEN_TAC (← q r"u:num") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"u MOD n < n /\ u DIV n < m /\ u MOD n + n * u DIV n = u") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN REMOVE_THEN "zK" (MP_TAC o (SPECL [(← q r"u MOD n"), (← q r"u DIV n")])) THEN REMOVE_THEN "zL" (MP_TAC o (SPECL [(← q r"u DIV n"), (← q r"u MOD n")])) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"z2:int")) THEN DISCH_THEN (X_CHOOSE_TAC (← q r"z1:int")) THEN EXISTS_TAC (← q r"a * z1 + b * z2:int") THEN REWRITE_TAC [RING_OF_INT_ADD, RING_OF_INT_MUL] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z27 ← (do let z28 ← (pure th); pure (concl z28)); pure (is_eq z27)) then (do let z32 ← (q r"ring_of_int k z1:A"); let z31 ← (do let z29 ← (do let z30 ← (pure th); pure (concl z30)); liftExcept (rhs z29)); pure (z31 == z32)) else pure false))))) THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z21 ← (do let z22 ← (pure th); pure (concl z22)); pure (is_eq z21)) then (do let z26 ← (q r"ring_of_int k z2:A"); let z25 ← (do let z23 ← (do let z24 ← (pure th); pure (concl z24)); liftExcept (rhs z23)); pure (z25 == z26)) else pure false))))) THEN FIRST_X_ASSUM (MP_TAC o ((AP_TERM (← q r"ring_of_int k:int->A")) o (checkM (fun th => (do if ← (do let z15 ← (do let z16 ← (pure th); pure (concl z16)); pure (is_eq z15)) then (do let z20 ← (q r"&1:int"); let z19 ← (do let z17 ← (do let z18 ← (pure th); pure (concl z18)); liftExcept (rhs z17)); pure (z19 == z20)) else pure false))))) THEN REWRITE_TAC [RING_OF_INT_ADD, RING_OF_INT_MUL, RING_OF_INT_1] THEN MATCH_MP_TAC r14 THEN ASM_REWRITE_TAC [RING_OF_INT], DISCH_THEN (MP_TAC o (REWRITE_RULE [RIGHT_IMP_EXISTS_THM, SKOLEM_THM])) THEN DISCH_THEN (X_CHOOSE_TAC (← q r"w:num->int")) THEN EXISTS_TAC (← q r"w:num->int") THEN FIRST_ASSUM ((fun th => tactic_of do pure (GEN_REWRITE_TAC LAND_CONV [(← SYM th)])) o (checkM (fun th => (do if ← (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_eq z1)) then (do let z6 ← (q r"alpha:A"); let z5 ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); liftExcept (rhs z3)); pure (z5 == z6)) else pure false) then (do let z7 ← (do let z8 ← (pure th); pure (concl z8)); canM (fun z9 => (do let z10 ← (pure z9); find_termM (fun z11 => (do let z13 ← (pure z11); let z12 ← (q r"B:num->A"); pure (z12 == z13))) z10)) z7) else pure false)))) THEN MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC [IN_ELIM_THM]], ALL_TAC] THEN SUBGOAL_THEN (← q r"free_basis (integer_ring,ring_of_integers k) (ring_of_int k) (n * m)
                (B:num->A)") ASSUME_TAC THENL [REWRITE_TAC [free_basis, INTEGER_RING, IN_UNIV, RING_OF_INTEGERS] THEN ASM_SIMP_TAC [] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"alpha:A") THEN DISCH_TAC THEN USE_THEN "span" (MP_TAC o (SPEC (← q r"alpha:A"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"w:num->int") SUBST1_TAC) THEN EXISTS_TAC (← q r"w:num->int") THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_RING_OF_INTEGERS THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_SIMP_TAC [RING_OF_INT_IN_RING_OF_INTEGERS], X_GEN_TAC (← q r"w:num->int") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"n * m:num"), (← q r"B:num->A"), (← q r"\u. ring_of_int k ((w:num->int) u):A")] FREE_BASIS_INDEPENDENT) THEN ASM_REWRITE_TAC [I_THM, RING_OF_INT_IN_SUBFIELD_GENERATED] THEN ANTS_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_RING_OF_INTEGERS THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_SIMP_TAC [RING_OF_INT_IN_RING_OF_INTEGERS], ASM_SIMP_TAC [SUBFIELD_GENERATED, RING_OF_INT_EQ_0_CHAR_0]]], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n * m:num"), (← q r"B:num->A")] NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"s:A->bool"), (← q r"t:A->bool"), (← q r"n:num"), (← q r"m:num"), (← q r"e:num->A"), (← q r"f:num->A")] BASIS_DISCRIMINANT_PRODUCT_BASIS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [(← GSYM RING_OF_INT_POW), (← GSYM RING_OF_INT_MUL)] THEN ASM_SIMP_TAC [RING_OF_INT_EQ_CHAR_0] THEN MESON_TAC [])

  let NUMBER_FIELD_COMPOSITUM_DISCRIMINANT ← prove
    r"!(k:A ring) s t.
        number_field k /\ subfield_generated k (s UNION t) = k /\
        coprime(number_field_discriminant(subfield_generated k s),
                number_field_discriminant(subfield_generated k t))
        ==> number_field_discriminant k =
            number_field_discriminant(subfield_generated k s) pow
            extension_degree (subfield_generated k {ring_0 k},
                              subfield_generated k t) I *
            number_field_discriminant(subfield_generated k t) pow
            extension_degree (subfield_generated k {ring_0 k},
                              subfield_generated k s) I"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"subfield_generated k (s:A->bool)") RING_OF_INTEGERS_FREE) THEN MP_TAC (← ISPEC (← q r"subfield_generated k (t:A->bool)") RING_OF_INTEGERS_FREE) THEN ASM_SIMP_TAC [NUMBER_FIELD_SUBFIELD_GENERATED, PRIME_SUBFIELD_SUBFIELD_GENERATED] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"f:num->A")) THEN DISCH_THEN (X_CHOOSE_TAC (← q r"e:num->A")) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"s:A->bool"), (← q r"t:A->bool"), (← q r"extension_degree (subfield_generated k {ring_0 k},
                       subfield_generated k s) (I:A->A)"), (← q r"extension_degree (subfield_generated k {ring_0 k},
                       subfield_generated k t) (I:A->A)"), (← q r"e:num->A"), (← q r"f:num->A")] NUMBER_FIELD_COMPOSITUM_INTEGRAL_BASIS) THEN ASM_REWRITE_TAC [] THEN SIMP_TAC [])

  let NUMBER_FIELD_COMPOSITUM_RING_OF_INTEGERS ← prove
    r"!(k:A ring) s t.
        number_field k /\ subfield_generated k (s UNION t) = k /\
        coprime(number_field_discriminant(subfield_generated k s),
                number_field_discriminant(subfield_generated k t))
        ==> ring_carrier(ring_of_integers k) =
            ring_carrier(subring_generated k
              (ring_carrier(ring_of_integers(subfield_generated k s)) UNION
               ring_carrier(ring_of_integers(subfield_generated k t))))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"subfield_generated k (s:A->bool)") RING_OF_INTEGERS_FREE) THEN MP_TAC (← ISPEC (← q r"subfield_generated k (t:A->bool)") RING_OF_INTEGERS_FREE) THEN ASM_SIMP_TAC [NUMBER_FIELD_SUBFIELD_GENERATED, PRIME_SUBFIELD_SUBFIELD_GENERATED] THEN ABBREV_TAC (← q r"n = extension_degree (subfield_generated k {ring_0 k},
                          subfield_generated k s) (I:A->A)") THEN ABBREV_TAC (← q r"m = extension_degree (subfield_generated k {ring_0 k},
                          subfield_generated k t) (I:A->A)") THEN DISCH_THEN (X_CHOOSE_TAC (← q r"f:num->A")) THEN DISCH_THEN (X_CHOOSE_TAC (← q r"e:num->A")) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"s:A->bool"), (← q r"t:A->bool"), (← q r"n:num"), (← q r"m:num"), (← q r"e:num->A"), (← q r"f:num->A")] NUMBER_FIELD_COMPOSITUM_INTEGRAL_BASIS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o CONJUNCT1) THEN REWRITE_TAC [free_basis, INTEGER_RING, IN_UNIV, RING_OF_INTEGERS] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (fun (_ : thm) => ALL_TAC))) THEN SUBGOAL_THEN (← q r"ring_carrier(ring_of_integers(subfield_generated k s)) UNION
    ring_carrier(ring_of_integers(subfield_generated k t)) SUBSET
    ring_carrier(ring_of_integers(k:A ring))") ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_SUBFIELD_GENERATED] THEN SET_TAC [], ALL_TAC] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [ALL_TAC, MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBRING]] THEN REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"x:A")) o (checkM (fun th => (do if ← (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_forall z1)) then (do let z3 ← (do pure (Prod.snd (← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); liftExcept (dest_forall z4))))); pure (is_imp z3)) else pure false) then (do let z6 ← (do let z7 ← (do pure (Prod.snd (← (do let z8 ← (do let z9 ← (pure th); pure (concl z9)); liftExcept (dest_forall z8))))); liftExcept (rand z7)); pure (is_exists z6)) else pure false))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"w:num->int") SUBST1_TAC) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{u:num | u < n * m}"), (← q r"\u. ring_mul k (ring_of_int k ((w:num->int) u))
           (ring_mul k ((e:num->A)(u MOD n)) ((f:num->A)(u DIV n)))")] RING_SUM_RING_OF_INTEGERS) THEN ANTS_TAC THENL [REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_SIMP_TAC [RING_OF_INTEGERS_SUBRING, IN_SUBRING_INT], DISCH_THEN SUBST1_TAC] THEN MATCH_MP_TAC IN_SUBRING_SUM THEN REWRITE_TAC [SUBRING_SUBRING_GENERATED, IN_ELIM_THM] THEN X_GEN_TAC (← q r"u:num") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"~(n = 0)") ASSUME_TAC THENL [UNDISCH_TAC (← q r"u < n * m:num") THEN ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [MULT_CLAUSES, LT], ALL_TAC] THEN SUBGOAL_THEN (← q r"u MOD n < n /\ u DIV n < m") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [MOD_LT_EQ, RDIV_LT_EQ], ALL_TAC] THEN MATCH_MP_TAC IN_SUBRING_MUL THEN REWRITE_TAC [SUBRING_SUBRING_GENERATED] THEN CONJ_TAC THENL [MATCH_MP_TAC IN_SUBRING_INT THEN REWRITE_TAC [SUBRING_SUBRING_GENERATED], ALL_TAC] THEN MATCH_MP_TAC IN_SUBRING_MUL THEN REWRITE_TAC [SUBRING_SUBRING_GENERATED] THEN CONJ_TAC THEN MATCH_MP_TAC SUBRING_GENERATED_INC THEN (CONJ_TAC THENL [MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_SUBSET) THEN ASM SET_TAC [], REWRITE_TAC [IN_UNION]]) THENL [DISJ1_TAC, DISJ2_TAC] THEN FIRST_ASSUM (MATCH_MP_TAC o (MATCH_MP FREE_BASIS_IN_CARRIER)) THEN ASM_REWRITE_TAC [])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_COMPOSITUM_DEGREE_GALOIS, NUMBER_FIELD_COMPOSITUM_DEGREE_COPRIME,
           NUMBER_FIELD_COMPOSITUM_INTEGRAL_BASIS, NUMBER_FIELD_COMPOSITUM_DISCRIMINANT,
           NUMBER_FIELD_COMPOSITUM_RING_OF_INTEGERS }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- discriminant_compositum.ml phrases from line 2006 to 2006              -/
/- ---------------------------------------------------------------------- -/

structure DiscriminantCompositum04 where
  -- @@FIELDS
  NUMBER_FIELD_COMPOSITUM_RAMIFIED : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDiscriminantCompositum04 [HolBase] (D : DiscriminantCompositumDeps) (BDiscriminantCompositum03 : DiscriminantCompositum03) :
    ExceptT String IO DiscriminantCompositum04 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, .. } := D
  let { INT_DIVIDES_RPOW, INT_PRIME, INT_PRIME_DIVPOW, LE_1, NUMBER_FIELD_DEGREE_POS,
        NUMBER_FIELD_RAMIFIED_DISCRIMINANT, NUMBER_FIELD_SUBFIELD_GENERATED,
        PRIME_INT_DIVPROD_EQ, PRIME_SUBFIELD_SUBFIELD_GENERATED, .. } := D.core1
  let { NUMBER_FIELD_COMPOSITUM_DISCRIMINANT, .. } := BDiscriminantCompositum03
  -- @@SCOPE END

  let NUMBER_FIELD_COMPOSITUM_RAMIFIED ← prove
    r"!(k:A ring) s t p.
        number_field k /\ subfield_generated k (s UNION t) = k /\
        coprime(number_field_discriminant(subfield_generated k s),
                number_field_discriminant(subfield_generated k t)) /\
        prime p
        ==> ((?P. prime_ideal (ring_of_integers k) P /\ ring_of_num k p IN P /\
                  1 < ramification_index (integer_ring,ring_of_integers k)
                        (ring_of_int k) P) <=>
             (?P. prime_ideal (ring_of_integers(subfield_generated k s)) P /\
                  ring_of_num (subfield_generated k s) p IN P /\
                  1 < ramification_index
                        (integer_ring,ring_of_integers(subfield_generated k s))
                        (ring_of_int(subfield_generated k s)) P) \/
             (?P. prime_ideal (ring_of_integers(subfield_generated k t)) P /\
                  ring_of_num (subfield_generated k t) p IN P /\
                  1 < ramification_index
                        (integer_ring,ring_of_integers(subfield_generated k t))
                        (ring_of_int(subfield_generated k t)) P))"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"number_field(subfield_generated k (s:A->bool)) /\
    number_field(subfield_generated k (t:A->bool))") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [NUMBER_FIELD_SUBFIELD_GENERATED], ALL_TAC] THEN ASM_SIMP_TAC [NUMBER_FIELD_RAMIFIED_DISCRIMINANT] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"s:A->bool"), (← q r"t:A->bool")] NUMBER_FIELD_COMPOSITUM_DISCRIMINANT) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPEC (← q r"subfield_generated k (s:A->bool)") NUMBER_FIELD_DEGREE_POS) THEN MP_TAC (← ISPEC (← q r"subfield_generated k (t:A->bool)") NUMBER_FIELD_DEGREE_POS) THEN ASM_REWRITE_TAC [PRIME_SUBFIELD_SUBFIELD_GENERATED] THEN REPEAT DISCH_TAC THEN ASM_SIMP_TAC [PRIME_INT_DIVPROD_EQ] THEN MP_TAC (← ISPEC (← q r"p:num") INT_PRIME) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN BINOP_TAC THEN ASM_MESON_TAC [INT_PRIME_DIVPOW, INT_DIVIDES_RPOW, LE_1])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_COMPOSITUM_RAMIFIED }
  -- @@RETURN END

end HolANT.DiscriminantCompositum
