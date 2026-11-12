/- ========================================================================= -/
/- ANT: Hermite                                                            -/
/- ========================================================================= -/
/- File: HolANT/Hermite.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/hermite.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/anthermitediff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/isum.ml, Library/products.ml, ANT/ideal_arith.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, Library/floor.ml, ANT/zlattice.ml, ANT/linear_forms.ml, ANT/hermite_inequality.ml, ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/classgroup.ml, ANT/discriminant.ml, ANT/prime_split.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/relative_degree.ml, ANT/nf_valuation.ml, ANT/integrality.ml, ANT/dedekind_kummer.ml, Library/frag.ml, Library/grouptheory.ml, Library/ring_groups.ml, ANT/fingen_group.ml, Multivariate/misc.ml, Multivariate/metric.ml, Multivariate/homology.ml, Multivariate/vectors.ml, Multivariate/determinants.ml, Multivariate/topology.ml, Multivariate/convex.ml, Multivariate/paths.ml, Multivariate/polytope.ml, Multivariate/degree.ml, Multivariate/derivatives.ml, Multivariate/integration.ml, Multivariate/measure.ml, Multivariate/complex_algebra.ml, Multivariate/complexes.ml, Multivariate/canal.ml, Multivariate/transcendentals.ml, Multivariate/realanalysis.ml, Multivariate/moretop.ml, Multivariate/cauchy.ml, Multivariate/complex_ring.ml, Multivariate/complex_field.ml, ANT/complex_embeddings.ml, ANT/power_basis.ml, ANT/infinite_places.ml, ANT/classgroup_group.ml, ANT/finite_field_trace.ml, ANT/ramification.ml, ANT/quadratic.ml, ANT/minkowski_theory.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.Hermite fills them).

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
import HolLibrary.Isum
import HolLibrary.Products
import HolANT.IdealArith
import HolANT.Algmisc
import HolANT.Integral
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.IdealNorm
import HolLibrary.Floor
import HolANT.Zlattice
import HolANT.LinearForms
import HolANT.HermiteInequality
import HolANT.Numfield
import HolANT.RingOfIntegers
import HolANT.NormIndex
import HolANT.Classgroup
import HolANT.Discriminant
import HolANT.PrimeSplit
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.TraceForm
import HolANT.RelativeSplit
import HolANT.RelativeDegree
import HolANT.NfValuation
import HolANT.Integrality
import HolANT.DedekindKummer
import HolLibrary.Frag
import HolLibrary.GroupTheory
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
import HolANT.ClassgroupGroup
import HolANT.FiniteFieldTrace
import HolANT.Ramification
import HolANT.Quadratic
import HolANT.MinkowskiTheory

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
open HolANT.DedekindStruct
open HolANT.IdealNorm
open HolANT.Zlattice
open HolANT.LinearForms
open HolANT.HermiteInequality
open HolANT.Numfield
open HolANT.RingOfIntegers
open HolANT.NormIndex
open HolANT.Classgroup
open HolANT.Discriminant
open HolANT.PrimeSplit
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.RelativeDegree
open HolANT.NfValuation
open HolANT.Integrality
open HolANT.DedekindKummer
open HolANT.FingenGroup
open HolANT.ComplexEmbeddings
open HolANT.PowerBasis
open HolANT.InfinitePlaces
open HolANT.ClassgroupGroup
open HolANT.FiniteFieldTrace
open HolANT.Ramification
open HolANT.Quadratic
open HolANT.MinkowskiTheory

namespace HolANT.Hermite

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (AGM_ROOT ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING CARD_DELETE CARD_IMAGE_INJ
   CARD_NUMSEG_LT CARD_SING CARD_SUBSET CARD_SUBSET_EQ
   CARRIER_SUBFIELD_GENERATED_SUBFIELD CNJ_CNJ CNJ_MUL CNJ_VSUM COEFF_ABOVE_DEG
   COMPLEX_EMBEDDINGS_CNJ COMPLEX_EMBEDDINGS_CNJ_CNJ COMPLEX_EMBEDDINGS_HAS_SIZE
   COMPLEX_EMBEDDINGS_MONOMORPHISM COMPLEX_EMBEDDINGS_NONEMPTY COMPLEX_EQ
   COMPLEX_MUL_SYM COMPLEX_NORM_CNJ COMPLEX_NORM_CX COMPLEX_NORM_LE_RE_IM
   COMPLEX_NORM_POW_2_VSUM_FORM COMPLEX_NORM_ZERO
   COMPLEX_POLYFUN_MONIC_COEFF_BOUND COMPLEX_POLYFUN_ROOTBOUND COMPLEX_POW_ZERO
   COMPLEX_RING_CLAUSES COMPLEX_RING_OF_INT COMPLEX_RING_POW COMPLEX_RING_SUM
   CX_INJ EQ_TRANS EXISTS_IN_IMAGE EXTENSION EXTENSIONAL_EQ
   EXTENSION_DEGREE_EQ_1 FIELD_COMPLEX_RING FIELD_EXTENSION_SUBFIELD_GENERATED
   FIELD_IMP_INTEGRAL_DOMAIN FIELD_IMP_NONTRIVIAL_RING FINITE_COMPLEX_EMBEDDINGS
   FINITE_DELETE FINITE_EXTENSION_SUBFIELD_GENERATED FINITE_FUNSPACE
   FINITE_IMAGE FINITE_IMP_ALGEBRAIC_EXTENSION FINITE_INT_SEG FINITE_NUMSEG
   FINITE_NUMSEG_LT FINITE_SING FINITE_SUBSET FINITE_UNIONS FORALL_IN_IMAGE
   FREE_BASIS_IN_CARRIER FUN_EQ_COEFF FUN_EQ_THM HAS_SIZE HAS_SIZE_INDEX
   HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS HERMITE_INEQUALITY IDEAL_NORM_CARRIER
   IDEAL_NORM_POS IMAGE_CLAUSES IMAGE_I IM_CNJ INSERT_SUBSET INTEGER_RING
   INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING INTEGRAL_DOMAIN_RING_OF_INTEGERS
   INTEGRAL_DOMAIN_UNIT_IDEAL INT_ABS_BOUNDS IN_DELETE IN_ELIM_THM
   IN_IDEAL_GENERATED_SELF IN_IMAGE IN_INSERT IN_NUMSEG
   IN_RING_POLYNOMIAL_CARRIER_COMPOSE IN_SING IN_UNIONS IN_UNIV I_O_ID I_THM
   LE_0 LE_1 LE_REFL MEMBER_NOT_EMPTY MINIMAL_POLYNOMIAL_DEG_LE_EXTENSION_DEGREE
   MONIC_HOMOMORPHIC_IMAGE MONIC_IMP_NONZERO NORM_POS_LE NOT_LE
   NUMBER_FIELD_DEGREE_POS NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS
   NUMBER_FIELD_DISCRIMINANT_NONZERO NUMBER_FIELD_EMBEDDING_GRAM_DET
   NUMBER_FIELD_IDEAL_MINKOWSKI_LINEAR_FORMS
   NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS NUMBER_FIELD_IMP_FIELD
   POLY_EXTEND_COMPOSE_COEFFS : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (POLY_EXTEND_HOMOMORPHIC_IMAGE POLY_EXTEND_INTO_SUBRING_GENERATED
   POLY_EXTEND_UNIVARIATE POLY_RING_CLAUSES POLY_ROOT_BOUND
   PRIME_SUBFIELD_MINIMAL PRIME_SUBFIELD_SUBFIELD_GENERATED PRODUCT_CONST
   PRODUCT_DELETE PRODUCT_EQ PRODUCT_LE PRODUCT_MUL REAL_ABS_0 REAL_ABS_POS
   REAL_ARCH_SIMPLE REAL_LET_TRANS REAL_LE_LADD REAL_LE_LMUL REAL_LE_MUL
   REAL_LE_MUL2 REAL_LE_POW_2 REAL_LE_RDIV_EQ REAL_LE_REFL REAL_LE_RSQRT
   REAL_LE_TRANS REAL_MUL_LID REAL_MUL_RID REAL_NOT_LE REAL_OF_NUM_LE
   REAL_OF_NUM_LT REAL_POS REAL_POW_1_LT REAL_POW_2 REAL_POW_EQ_0 REAL_POW_LE
   REAL_POW_LE2 REAL_POW_LE_1 REAL_POW_MUL REAL_POW_ONE RESTRICTION RE_CNJ
   RING_CHAR_SUBFIELD_GENERATED RING_DET_DEPENDENT_COLUMNS
   RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED RING_HOMOMORPHISM_0
   RING_HOMOMORPHISM_FROM_SUBFIELD_GENERATED
   RING_HOMOMORPHISM_FROM_SUBRING_GENERATED RING_HOMOMORPHISM_I
   RING_HOMOMORPHISM_INTEGER_RING_OF_INT RING_HOMOMORPHISM_RING_OF_INT
   RING_HOMOMORPHISM_SUM_MUL RING_IDEAL_IDEAL_GENERATED
   RING_ISOMORPHISM_ONTO_SUBFIELD_IMAGE RING_OF_INT RING_OF_INTEGERS
   RING_OF_INTEGERS_FINITE_QUOTIENT RING_OF_INTEGERS_FREE
   RING_OF_INTEGERS_INTEGER_MINIMAL_POLYNOMIAL RING_OF_INTEGERS_SUBSET
   RING_OF_INT_SUBFIELD_GENERATED RING_POLYNOMIAL RING_SUM ROOT_1 ROOT_MONO_LE
   SEPARABLE_EXTENSION_CHAR0 SING_SUBSET SQRT_MONO_LE SQRT_POS_LE
   SUBFIELD_GENERATED SUBFIELD_GENERATED_BY_MONOMORPHIC_IMAGE
   SUBFIELD_GENERATED_INC_GEN SUBFIELD_GENERATED_MINIMAL
   SUBFIELD_GENERATED_SUPERSET SUBFIELD_OF_IMP_SUBSET
   SUBFIELD_OF_SUBFIELD_GENERATED SUBFIELD_SUBFIELD_GENERATED
   SUBFIELD_SUBFIELD_GENERATED_ALT SUBRING_GENERATED_BY_SUBFIELD_GENERATED
   SUBSET SUBSET_ANTISYM SUM_EQ SUM_IMAGE SUM_POS_EQ_0 SUM_POS_LE VSUM_EQ coeff
   complex_embeddings free_basis int_abs_th int_eq int_le int_of_num_th
   isomorphic_ring monic number_field o_DEF o_THM poly_eval poly_evaluate
   ring_homomorphism_extensions ring_of_integers : thm)
  deriving Inhabited

/-- What hermite.ml uses from Session besides theorems. -/
structure HermiteDeps where
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
/- hermite.ml phrases from line 99 to 648                                 -/
/- ---------------------------------------------------------------------- -/

structure Hermite01 where
  -- @@FIELDS
  RING_OF_INTEGERS_NORM_PRODUCT_GE_1 : thm
  RING_OF_INTEGERS_SUM_NORM_POW_2 : thm
  NUMBER_FIELD_DISCRIMINANT_HERMITE_BOUND : thm
  NUMBER_FIELD_GENERATOR_CONJUGATES : thm
  NUMBER_FIELD_HERMITE_GENERATOR : thm
  NUMBER_FIELD_HERMITE_POLYNOMIAL : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupHermite01 [HolBase] (D : HermiteDeps) :
    ExceptT String IO Hermite01 := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, INT_ARITH_TAC, MESON,
        MESON_TAC, NUM_REDUCE_CONV, REAL_ARITH, REAL_ARITH_TAC, REAL_RAT_REDUCE_CONV,
        SET_RULE, TAUT, .. } := D
  let { AGM_ROOT, ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING, CARD_DELETE, CARD_IMAGE_INJ,
        CARD_NUMSEG_LT, CARD_SING, CARD_SUBSET, CARD_SUBSET_EQ, CNJ_CNJ, CNJ_MUL,
        CNJ_VSUM, COEFF_ABOVE_DEG, COMPLEX_EMBEDDINGS_CNJ, COMPLEX_EMBEDDINGS_CNJ_CNJ,
        COMPLEX_EMBEDDINGS_HAS_SIZE, COMPLEX_EMBEDDINGS_NONEMPTY, COMPLEX_EQ,
        COMPLEX_MUL_SYM, COMPLEX_NORM_CNJ, COMPLEX_NORM_CX, COMPLEX_NORM_LE_RE_IM,
        COMPLEX_NORM_POW_2_VSUM_FORM, COMPLEX_NORM_ZERO,
        COMPLEX_POLYFUN_MONIC_COEFF_BOUND, COMPLEX_POLYFUN_ROOTBOUND, COMPLEX_POW_ZERO,
        COMPLEX_RING_CLAUSES, COMPLEX_RING_OF_INT, COMPLEX_RING_POW, COMPLEX_RING_SUM,
        CX_INJ, EQ_TRANS, EXTENSION, EXTENSIONAL_EQ, EXTENSION_DEGREE_EQ_1,
        FIELD_COMPLEX_RING, FIELD_EXTENSION_SUBFIELD_GENERATED,
        FIELD_IMP_INTEGRAL_DOMAIN, FINITE_COMPLEX_EMBEDDINGS, FINITE_DELETE,
        FINITE_EXTENSION_SUBFIELD_GENERATED, FINITE_IMP_ALGEBRAIC_EXTENSION,
        FINITE_NUMSEG, FINITE_NUMSEG_LT, FINITE_SING, FORALL_IN_IMAGE,
        FREE_BASIS_IN_CARRIER, FUN_EQ_THM, HAS_SIZE, HAS_SIZE_INDEX,
        HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS, HERMITE_INEQUALITY, IDEAL_NORM_CARRIER,
        IDEAL_NORM_POS, IMAGE_I, IM_CNJ, INSERT_SUBSET, INTEGER_RING,
        INTEGRAL_DOMAIN_RING_OF_INTEGERS, INTEGRAL_DOMAIN_UNIT_IDEAL, IN_DELETE,
        IN_ELIM_THM, IN_IDEAL_GENERATED_SELF, IN_IMAGE, IN_INSERT, IN_NUMSEG, IN_SING,
        IN_UNIV, I_THM, LE_0, LE_1, LE_REFL, MEMBER_NOT_EMPTY,
        MINIMAL_POLYNOMIAL_DEG_LE_EXTENSION_DEGREE, NORM_POS_LE,
        NUMBER_FIELD_DEGREE_POS, NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS,
        NUMBER_FIELD_DISCRIMINANT_NONZERO, NUMBER_FIELD_EMBEDDING_GRAM_DET,
        NUMBER_FIELD_IDEAL_MINKOWSKI_LINEAR_FORMS,
        NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS, NUMBER_FIELD_IMP_FIELD, .. } := D.core1
  let { POLY_EXTEND_HOMOMORPHIC_IMAGE, POLY_EXTEND_UNIVARIATE, PRIME_SUBFIELD_MINIMAL,
        PRODUCT_CONST, PRODUCT_DELETE, PRODUCT_EQ, PRODUCT_LE, PRODUCT_MUL, REAL_ABS_0,
        REAL_ABS_POS, REAL_LET_TRANS, REAL_LE_MUL, REAL_LE_MUL2, REAL_LE_POW_2,
        REAL_LE_RDIV_EQ, REAL_LE_REFL, REAL_LE_RSQRT, REAL_LE_TRANS, REAL_MUL_LID,
        REAL_MUL_RID, REAL_NOT_LE, REAL_OF_NUM_LE, REAL_OF_NUM_LT, REAL_POS,
        REAL_POW_1_LT, REAL_POW_2, REAL_POW_EQ_0, REAL_POW_LE, REAL_POW_LE2,
        REAL_POW_LE_1, REAL_POW_MUL, REAL_POW_ONE, RESTRICTION, RE_CNJ,
        RING_CHAR_SUBFIELD_GENERATED, RING_DET_DEPENDENT_COLUMNS,
        RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED, RING_HOMOMORPHISM_0,
        RING_HOMOMORPHISM_FROM_SUBFIELD_GENERATED,
        RING_HOMOMORPHISM_FROM_SUBRING_GENERATED,
        RING_HOMOMORPHISM_INTEGER_RING_OF_INT, RING_HOMOMORPHISM_RING_OF_INT,
        RING_HOMOMORPHISM_SUM_MUL, RING_IDEAL_IDEAL_GENERATED, RING_OF_INT,
        RING_OF_INTEGERS, RING_OF_INTEGERS_FINITE_QUOTIENT, RING_OF_INTEGERS_FREE,
        RING_OF_INTEGERS_INTEGER_MINIMAL_POLYNOMIAL, RING_OF_INTEGERS_SUBSET,
        RING_POLYNOMIAL, RING_SUM, ROOT_1, ROOT_MONO_LE, SEPARABLE_EXTENSION_CHAR0,
        SQRT_POS_LE, SUBFIELD_GENERATED_INC_GEN, SUBFIELD_GENERATED_MINIMAL,
        SUBFIELD_GENERATED_SUPERSET, SUBFIELD_SUBFIELD_GENERATED, SUBSET, SUM_EQ,
        SUM_IMAGE, SUM_POS_EQ_0, SUM_POS_LE, VSUM_EQ, complex_embeddings, free_basis,
        int_abs_th, int_eq, int_le, int_of_num_th, monic, number_field, o_DEF, o_THM,
        ring_homomorphism_extensions, ring_of_integers, .. } := D.core2
  -- @@SCOPE END

  let RING_OF_INTEGERS_NORM_PRODUCT_GE_1 ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!x:A s z. x IN s /\ ~(x = z) ==> ~(s = {z})")
    prove
      r"!k x:A.
          number_field k /\ x IN ring_carrier(ring_of_integers k) /\
          ~(x = ring_0 k)
          ==> &1 <= product (complex_embeddings k) (\g. norm(g x))"
      (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [(← GSYM NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS)] THEN REWRITE_TAC [REAL_OF_NUM_LE] THEN MATCH_MP_TAC IDEAL_NORM_POS THEN MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN MATCH_MP_TAC r1 THEN EXISTS_TAC (← q r"x:A") THEN ASM_REWRITE_TAC [IN_IDEAL_GENERATED_SELF])

  let RING_OF_INTEGERS_SUM_NORM_POW_2 ← prove
    r"!k x:A.
        number_field k /\ x IN ring_carrier(ring_of_integers k) /\
        ~(x = ring_0 k)
        ==> &(extension_degree (subfield_generated k {ring_0 k},k) I) <=
            sum (complex_embeddings k) (\g. norm(g x) pow 2)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_DEGREE_POS)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP COMPLEX_EMBEDDINGS_HAS_SIZE)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITE_COMPLEX_EMBEDDINGS)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A")] RING_OF_INTEGERS_NORM_PRODUCT_GE_1) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ABBREV_TAC (← q r"n = extension_degree (subfield_generated k {ring_0 k},k:A ring) I") THEN SUBGOAL_THEN (← q r"&1 <= product (complex_embeddings k) (\g. norm((g:A->complex) x) pow 2)") ASSUME_TAC THENL [ASM_SIMP_TAC [REAL_POW_2, PRODUCT_MUL] THEN GEN_REWRITE_TAC LAND_CONV [(← GSYM REAL_MUL_LID)] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC [REAL_POS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"complex_embeddings(k:A ring)"), (← q r"\g:A->complex. norm(g x) pow 2"), (← q r"n:num")] AGM_ROOT) THEN ASM_REWRITE_TAC [REAL_LE_POW_2] THEN ANTS_TAC THENL [ASM_ARITH_TAC, DISCH_TAC] THEN MP_TAC (← SPECL [(← q r"n:num"), (← q r"(&1:real)"), (← q r"product (complex_embeddings k) (\g. norm((g:A->complex) x) pow 2)")] ROOT_MONO_LE) THEN ASM_REWRITE_TAC [ROOT_1] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"&1 <= sum (complex_embeddings k) (\g. norm((g:A->complex) x) pow 2) / &n") MP_TAC THENL [ASM_MESON_TAC [REAL_LE_TRANS], ALL_TAC] THEN ASM_SIMP_TAC [REAL_LE_RDIV_EQ, REAL_OF_NUM_LT, LE_1, REAL_MUL_LID])

  let NUMBER_FIELD_DISCRIMINANT_HERMITE_BOUND ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"a <= b ==> b <= c ==> a <= c:real")
    let r13 ← REAL_ARITH (← q r"&0 <= x /\ ~(x = &0) ==> &0 < x:real")
    prove
      r"!k:A ring.
          number_field k
          ==> &(extension_degree (subfield_generated k {ring_0 k},k) I) pow
              (2 * extension_degree (subfield_generated k {ring_0 k},k) I) <=
              (&4 / &3) pow
              (extension_degree (subfield_generated k {ring_0 k},k) I *
               (extension_degree (subfield_generated k {ring_0 k},k) I - 1)) *
              real_of_int(number_field_discriminant k) pow 2"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM ((X_CHOOSE_TAC (← q r"w:num->A")) o (MATCH_MP RING_OF_INTEGERS_FREE)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_DEGREE_POS)) THEN MP_TAC (← ISPEC (← q r"k:A ring") COMPLEX_EMBEDDINGS_HAS_SIZE) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"n = extension_degree (subfield_generated k {ring_0 k},k:A ring) I") THEN DISCH_THEN (MP_TAC o (MATCH_MP HAS_SIZE_INDEX)) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"e:num->A->complex") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"!i j. i < n /\ j < n /\ (e:num->A->complex) i = e j ==> i = j") ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. i < n ==> (w:num->A) i IN ring_carrier k") ASSUME_TAC THENL [FIRST_X_ASSUM (MP_TAC o ((MATCH_MP FREE_BASIS_IN_CARRIER) o (checkM (fun th => (do if ← (do let z15 ← (do let z16 ← (pure th); pure (concl z16)); let z14 ← (q r"w:num->A"); pure (free_in z14 z15)) then (do pure !(← (do let z17 ← (do let z18 ← (pure th); pure (concl z18)); pure (is_forall z17)))) else pure false))))) THEN MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"{i:num | i < n}"), (← q r"\i j. Re(vsum {l | l < n}
                 (\l. cnj((e:num->A->complex) l ((w:num->A) i)) * e l (w j)))")] HERMITE_INEQUALITY) THEN REWRITE_TAC [FINITE_NUMSEG_LT, CARD_NUMSEG_LT] THEN ANTS_TAC THENL [REPEAT CONJ_TAC THENL [REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY), IN_ELIM_THM] THEN EXISTS_TAC (← q r"0") THEN ASM_ARITH_TAC, REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [(← GSYM RE_CNJ)] THEN AP_TERM_TAC THEN SIMP_TAC [CNJ_VSUM, FINITE_NUMSEG_LT, CNJ_MUL, CNJ_CNJ] THEN MATCH_MP_TAC VSUM_EQ THEN SIMP_TAC [COMPLEX_MUL_SYM], X_GEN_TAC (← q r"c:num->real") THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN MP_TAC (← BETA_RULE (← ISPECL [(← q r"{l:num | l < n}"), (← q r"{j:num | j < n}"), (← q r"\l j. (e:num->A->complex) l ((w:num->A) j)"), (← q r"c:num->real")] COMPLEX_NORM_POW_2_VSUM_FORM)) THEN REWRITE_TAC [FINITE_NUMSEG_LT] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC r13 THEN SIMP_TAC [SUM_POS_LE, FINITE_NUMSEG_LT, REAL_LE_POW_2] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"\l. norm(vsum {j | j < n}
                     (\j. Cx(c j) * (e:num->A->complex) l ((w:num->A) j))) pow 2"), (← q r"{l:num | l < n}")] SUM_POS_EQ_0) THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT, REAL_LE_POW_2, IN_ELIM_THM] THEN REWRITE_TAC [REAL_POW_EQ_0, COMPLEX_NORM_ZERO] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") NUMBER_FIELD_DISCRIMINANT_NONZERO) THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"e:num->A->complex")] NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS) THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ring_det complex_ring {i | i < n}
            (\i j. (e:num->A->complex) i ((w:num->A) j)) = Cx(&0)") SUBST1_TAC THENL [MP_TAC (← ISPECL [(← q r"complex_ring"), (← q r"{i:num | i < n}"), (← q r"\l j. (e:num->A->complex) l ((w:num->A) j)"), (← q r"\j. Cx((c:num->real) j)")] RING_DET_DEPENDENT_COLUMNS) THEN SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, FIELD_COMPLEX_RING, FINITE_NUMSEG_LT, COMPLEX_RING_CLAUSES, IN_UNIV, COMPLEX_RING_SUM] THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC [IN_ELIM_THM, CX_INJ] THEN CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN X_GEN_TAC (← q r"l:num") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"l:num")) o (checkM (fun th => (do if ← (do let z8 ← (do let z9 ← (pure th); pure (concl z9)); pure (is_forall z8)) then (do let z11 ← (do let z12 ← (pure th); pure (concl z12)); let z10 ← (q r"c:num->real"); pure (free_in z10 z11)) else pure false))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC VSUM_EQ THEN SIMP_TAC [COMPLEX_MUL_SYM], REWRITE_TAC [COMPLEX_POW_ZERO] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [CX_INJ] THEN DISCH_THEN (MP_TAC o SYM) THEN REWRITE_TAC [int_eq, int_of_num_th]]], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:num->int") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"e:num->A->complex")] NUMBER_FIELD_EMBEDDING_GRAM_DET) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => RULE_ASSUM_TAC (REWRITE_RULE [th])) THEN ABBREV_TAC (← q r"x = ring_sum (ring_of_integers k) {j | j < n}
            (\j. ring_mul (ring_of_integers k) (ring_of_int k ((c:num->int) j))
                          ((w:num->A) j))") THEN SUBGOAL_THEN (← q r"!j. j < n ==> ring_of_int k ((c:num->int) j) IN
                    ring_carrier(ring_of_integers (k:A ring)) /\
                    (w:num->A) j IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [REPEAT STRIP_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"(c:num->int) j")] RING_OF_INT) THEN REWRITE_TAC [RING_OF_INTEGERS], ASM_MESON_TAC [FREE_BASIS_IN_CARRIER]], ALL_TAC] THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier(ring_of_integers k) /\ ~(x = ring_0 k)") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [EXPAND_TAC "x" THEN REWRITE_TAC [RING_SUM], ALL_TAC] THEN DISCH_TAC THEN MP_TAC (← SPEC (← q r"c:num->int") (← CONJUNCT2 (← CONJUNCT2 (← GEN_REWRITE_RULE id [free_basis] (← ASSUME (← q r"free_basis (integer_ring,ring_of_integers k)
                                (ring_of_int k) n (w:num->A)")))))) THEN ASM_REWRITE_TAC [INTEGER_RING, IN_UNIV, RING_OF_INTEGERS] THEN RULE_ASSUM_TAC (REWRITE_RULE [IN_ELIM_THM]) THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!l. l < n
          ==> (e:num->A->complex) l x =
              vsum {j | j < n} (\j. Cx(real_of_int((c:num->int) j)) *
                                    e l ((w:num->A) j))") ASSUME_TAC THENL [X_GEN_TAC (← q r"l:num") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_homomorphism(ring_of_integers k,complex_ring)
          ((e:num->A->complex) l)") ASSUME_TAC THENL [REWRITE_TAC [ring_of_integers] THEN MATCH_MP_TAC RING_HOMOMORPHISM_FROM_SUBRING_GENERATED THEN ASM_MESON_TAC [complex_embeddings, IN_ELIM_THM], ALL_TAC] THEN EXPAND_TAC "x" THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"complex_ring"), (← q r"(e:num->A->complex) l"), (← q r"{j:num | j < n}"), (← q r"\j. ring_of_int k ((c:num->int) j):A"), (← q r"w:num->A")] RING_HOMOMORPHISM_SUM_MUL) THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, COMPLEX_RING_SUM] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC [IN_ELIM_THM, COMPLEX_RING_CLAUSES] THEN X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"complex_ring"), (← q r"(e:num->A->complex) l")] RING_HOMOMORPHISM_RING_OF_INT) THEN ANTS_TAC THENL [ASM_MESON_TAC [complex_embeddings, IN_ELIM_THM], SIMP_TAC [COMPLEX_RING_OF_INT]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A")] RING_OF_INTEGERS_SUM_NORM_POW_2) THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"sum (complex_embeddings k) (\g. norm((g:A->complex) x) pow 2) =
      sum {i | i < n} (\i. sum {i | i < n} (\j.
        Re(vsum {l | l < n} (\l. cnj(e l ((w:num->A) i)) * e l (w j))) *
        real_of_int((c:num->int) i) * real_of_int(c j)))") SUBST1_TAC THENL [TRANS_TAC EQ_TRANS (← q r"sum {l | l < n} (\l. norm((e:num->A->complex) l x) pow 2)") THEN CONJ_TAC THENL [SUBGOAL_THEN (← q r"complex_embeddings (k:A ring) = IMAGE (e:num->A->complex) {i | i < n}") SUBST1_TAC THENL [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN wPart lhand (lhand o rand) SUM_IMAGE THEN ANTS_TAC THENL [REWRITE_TAC [IN_ELIM_THM] THEN ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [o_DEF]], ALL_TAC] THEN TRANS_TAC EQ_TRANS (← q r"sum {l | l < n} (\l. norm(vsum {j | j < n}
          (\j. Cx(real_of_int((c:num->int) j)) *
               (e:num->A->complex) l ((w:num->A) j))) pow 2)") THEN CONJ_TAC THENL [MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC [IN_ELIM_THM], ALL_TAC] THEN MP_TAC (← BETA_RULE (← ISPECL [(← q r"{l:num | l < n}"), (← q r"{j:num | j < n}"), (← q r"\l j. (e:num->A->complex) l ((w:num->A) j)"), (← q r"\j. real_of_int((c:num->int) j)")] COMPLEX_NORM_POW_2_VSUM_FORM)) THEN REWRITE_TAC [FINITE_NUMSEG_LT], ALL_TAC] THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do if ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); let z2 ← (q r"number_field_discriminant (k:A ring)"); pure (free_in z2 z3)) then (do let z6 ← (do let z7 ← (pure th); pure (concl z7)); let z5 ← (q r"c:num->int"); pure (free_in z5 z6)) else pure false)))) THEN MATCH_MP_TAC r1 THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC [REAL_POS])

  let NUMBER_FIELD_GENERATOR_CONJUGATES ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"k:A ring"
    let q2 ← q r"L:A ring"
    let q3 ← q r"I:A->A"
    let v4 ← ISPECL [q3, q2, q1] EXTENSION_DEGREE_EQ_1
    let q5 ← q r"f:A->complex"
    let q6 ← q r"ring_homomorphism_extensions (L,k,complex_ring) (I,g:A->complex) = {g}"
    let q7 ← q r"complex_ring"
    let q8 ← q r"k:A ring"
    let q9 ← q r"L:A ring"
    let q10 ← q r"g:A->complex"
    let q11 ← q r"I:A->A"
    let v12 ← ISPECL [q11, q10, q9, q8, q7] HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS
    let q13 ← q r"ring_homomorphism(k,complex_ring) (g:A->complex)"
    let q14 ← q r"(x:A) IN ring_carrier L"
    let q15 ← q r"s SUBSET (x:A) INSERT s"
    let r16 ← SET_RULE q15
    let q17 ← q r"(x:A) INSERT ring_carrier(subfield_generated k {ring_0 k})"
    let q18 ← q r"k:A ring"
    let q19 ← q r"subfield_generated k {ring_0 k}:A ring"
    let q20 ← q r"I:A->A"
    let v21 ← ISPECL [q20, q19, q18, q17] FINITE_EXTENSION_SUBFIELD_GENERATED
    let q22 ← q r"finite_extension (L,k) (I:A->A)"
    let q23 ← q r"L = subfield_generated k
           ((x:A) INSERT ring_carrier(subfield_generated k {ring_0 k}))"
    let p24 ← prove r"!k (x:A) g.
          number_field k /\ x IN ring_carrier k /\ g IN complex_embeddings k /\
          (!h. h IN complex_embeddings k /\ h x = g x ==> h = g)
          ==> subfield_generated k {x} = k" (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [number_field])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN ABBREV_TAC q23 THEN SUBGOAL_THEN q22 ASSUME_TAC THENL [EXPAND_TAC "L" THEN MP_TAC v21 THEN ASM_SIMP_TAC [IMAGE_I, r16], ALL_TAC] THEN SUBGOAL_THEN q14 ASSUME_TAC THENL [EXPAND_TAC "L" THEN MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN ASM_REWRITE_TAC [IN_INSERT], ALL_TAC] THEN SUBGOAL_THEN q13 ASSUME_TAC THENL [ASM_MESON_TAC [complex_embeddings, IN_ELIM_THM], ALL_TAC] THEN MP_TAC v12 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING] THEN CONJ_TAC THENL [MATCH_MP_TAC SEPARABLE_EXTENSION_CHAR0 THEN ASM_SIMP_TAC [FINITE_IMP_ALGEBRAIC_EXTENSION] THEN EXPAND_TAC "L" THEN ASM_REWRITE_TAC [RING_CHAR_SUBFIELD_GENERATED], EXPAND_TAC "L" THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_FROM_SUBFIELD_GENERATED]], ALL_TAC] THEN SUBGOAL_THEN q6 SUBST1_TAC THENL [REWRITE_TAC [ring_homomorphism_extensions, EXTENSION, IN_ELIM_THM, IN_SING, I_THM] THEN X_GEN_TAC q5 THEN EQ_TAC THENL [STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC [complex_embeddings, IN_ELIM_THM], DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC [complex_embeddings, IN_ELIM_THM]], ALL_TAC] THEN REWRITE_TAC [HAS_SIZE, FINITE_SING, CARD_SING] THEN DISCH_THEN (ASSUME_TAC o SYM) THEN MP_TAC v4 THEN ANTS_TAC THENL [EXPAND_TAC "L" THEN ASM_REWRITE_TAC [FIELD_EXTENSION_SUBFIELD_GENERATED], ASM_REWRITE_TAC [IMAGE_I]] THEN DISCH_TAC THEN REWRITE_TAC [SUBFIELD_GENERATED_SUPERSET] THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN EXPAND_TAC "L" THEN MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED, INSERT_SUBSET] THEN ASM_SIMP_TAC [SUBFIELD_GENERATED_INC_GEN, IN_SING] THEN MATCH_MP_TAC PRIME_SUBFIELD_MINIMAL THEN ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED])
    let simple := p24
    let q25 ← q r"g:A->complex"
    let q26 ← q r"g:A->complex"
    let q27 ← q r"g:A->complex"
    let v28 ← GSYM MEMBER_NOT_EMPTY
    let q29 ← q r"g:A->complex"
    let q30 ← q r"{x:A}"
    let q31 ← q r"complex_ring"
    let q32 ← q r"k:A ring"
    let q33 ← q r"h:A->complex"
    let q34 ← q r"g:A->complex"
    let v35 ← ISPECL [q34, q33, q32, q31, q30] RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED
    let q36 ← q r"ring_carrier k:A->bool"
    let q37 ← q r"h:A->complex"
    let q38 ← q r"g:A->complex"
    let q39 ← q r"(a ==> b) /\ (b ==> c) /\ (c ==> a) ==> (a <=> b) /\ (a <=> c)"
    let r40 ← TAUT q39
    prove
      r"!k x:A.
          number_field k /\ x IN ring_carrier k
          ==> (subfield_generated k {x} = k <=>
               !g h. g IN complex_embeddings k /\ h IN complex_embeddings k /\
                     g x = h x
                     ==> g = h) /\
              (subfield_generated k {x} = k <=>
               ?g. g IN complex_embeddings k /\
                   !h. h IN complex_embeddings k /\ h x = g x ==> h = g)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC r40 THEN REPEAT CONJ_TAC THENL [DISCH_TAC THEN MAP_EVERY X_GEN_TAC [q38, q37] THEN STRIP_TAC THEN MATCH_MP_TAC EXTENSIONAL_EQ THEN EXISTS_TAC q36 THEN REPEAT CONJ_TAC THENL [ASM_MESON_TAC [complex_embeddings, IN_ELIM_THM], ASM_MESON_TAC [complex_embeddings, IN_ELIM_THM], ALL_TAC] THEN MP_TAC v35 THEN ASM_REWRITE_TAC [IN_SING] THEN ANTS_TAC THENL [ASM_MESON_TAC [complex_embeddings, IN_ELIM_THM, NUMBER_FIELD_IMP_FIELD], SIMP_TAC []], DISCH_TAC THEN FIRST_ASSUM ((X_CHOOSE_TAC q29) o ((REWRITE_RULE [v28]) o (MATCH_MP COMPLEX_EMBEDDINGS_NONEMPTY))) THEN EXISTS_TAC q27 THEN ASM_MESON_TAC [], DISCH_THEN (X_CHOOSE_THEN q26 STRIP_ASSUME_TAC) THEN MATCH_MP_TAC simple THEN EXISTS_TAC q25 THEN ASM_REWRITE_TAC []])

  let NUMBER_FIELD_HERMITE_GENERATOR ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r11 ← TAUT (← q r"(~p ==> F) ==> p")
    let r12 ← REAL_ARITH (← q r"(a * d) * b:real = d * (a * b)")
    prove
      r"!k:A ring.
          number_field k
          ==> ?x. x IN ring_carrier(ring_of_integers k) /\
                  subfield_generated k {x} = k /\
                  !g. g IN complex_embeddings k
                      ==> norm(g x) <=
                          &2 pow
                          (extension_degree (subfield_generated k {ring_0 k},k) I
                           - 1) *
                          sqrt(abs(real_of_int(number_field_discriminant k)))"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_DEGREE_POS)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP COMPLEX_EMBEDDINGS_HAS_SIZE)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITE_COMPLEX_EMBEDDINGS)) THEN ABBREV_TAC (← q r"n = extension_degree (subfield_generated k {ring_0 k},k:A ring) I") THEN ABBREV_TAC (← q r"D = sqrt(abs(real_of_int(number_field_discriminant(k:A ring))))") THEN SUBGOAL_THEN (← q r"&1 <= (D:real)") ASSUME_TAC THENL [EXPAND_TAC "D" THEN MATCH_MP_TAC REAL_LE_RSQRT THEN REWRITE_TAC [REAL_POW_ONE] THEN MP_TAC (← ISPEC (← q r"k:A ring") NUMBER_FIELD_DISCRIMINANT_NONZERO) THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [(← GSYM int_of_num_th), (← GSYM int_abs_th), (← GSYM int_le)] THEN INT_ARITH_TAC, ALL_TAC] THEN FIRST_ASSUM ((X_CHOOSE_TAC (← q r"g0:A->complex")) o ((REWRITE_RULE [(← GSYM MEMBER_NOT_EMPTY)]) o (MATCH_MP COMPLEX_EMBEDDINGS_NONEMPTY))) THEN ABBREV_TAC (← q r"(C:real) = &2 pow (n - 1) * D") THEN SUBGOAL_THEN (← q r"&1 <= (C:real)") ASSUME_TAC THENL [EXPAND_TAC "C" THEN GEN_REWRITE_TAC LAND_CONV [(← GSYM REAL_MUL_LID)] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC [REAL_POS] THEN MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_carrier(ring_of_integers k):A->bool"), (← q r"\g:A->complex. if g = g0 then C else &1 / &2")] NUMBER_FIELD_IDEAL_MINKOWSKI_LINEAR_FORMS) THEN ASM_REWRITE_TAC [IDEAL_NORM_CARRIER, REAL_MUL_RID] THEN ANTS_TAC THENL [REPEAT CONJ_TAC THENL [MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") INTEGRAL_DOMAIN_UNIT_IDEAL) THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_RING_OF_INTEGERS, RING_OF_INTEGERS], MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") INTEGRAL_DOMAIN_UNIT_IDEAL) THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_RING_OF_INTEGERS, RING_OF_INTEGERS], GEN_TAC THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"\g:A->complex. if g = g0 then C else &1 / &2"), (← q r"complex_embeddings(k:A ring)"), (← q r"g0:A->complex")] PRODUCT_DELETE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN SUBGOAL_THEN (← q r"product (complex_embeddings k DELETE g0)
          (\g:A->complex. if g = g0 then C else &1 / &2) =
        (&1 / &2) pow (n - 1)") SUBST1_TAC THENL [TRANS_TAC EQ_TRANS (← q r"product (complex_embeddings k DELETE (g0:A->complex)) (\g. &1 / &2)") THEN CONJ_TAC THENL [MATCH_MP_TAC PRODUCT_EQ THEN SIMP_TAC [IN_DELETE], ASM_SIMP_TAC [PRODUCT_CONST, FINITE_DELETE, CARD_DELETE] THEN RULE_ASSUM_TAC (REWRITE_RULE [HAS_SIZE]) THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"&2 pow (n - 1) * (&1 / &2) pow (n - 1) = &1") MP_TAC THENL [REWRITE_TAC [(← GSYM REAL_POW_MUL)] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC [REAL_POW_ONE], EXPAND_TAC "C" THEN REWRITE_TAC [r12] THEN SIMP_TAC [REAL_MUL_RID, REAL_LE_REFL]], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"x:A") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bd")))) THEN EXISTS_TAC (← q r"x:A") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"!g. g IN complex_embeddings k
          ==> RESTRICTION (ring_carrier k) (cnj o g) IN complex_embeddings k /\
              RESTRICTION (ring_carrier k) (cnj o g) x = cnj((g:A->complex) x)") ASSUME_TAC THENL [ASM_SIMP_TAC [COMPLEX_EMBEDDINGS_CNJ, RESTRICTION, o_THM], ALL_TAC] THEN ABBREV_TAC (← q r"g1 = RESTRICTION (ring_carrier k) (cnj o (g0:A->complex))") THEN SUBGOAL_THEN (← q r"(g1:A->complex) IN complex_embeddings k /\ g1 x = cnj((g0:A->complex) x)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!g. g IN complex_embeddings k /\ ~(g = g0) /\ ~(g = g1)
          ==> norm((g:A->complex) x) <= &1 / &2") ASSUME_TAC THENL [X_GEN_TAC (← q r"g:A->complex") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"~(RESTRICTION (ring_carrier k) (cnj o (g:A->complex)) = g0)") ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC (← q r"~((g:A->complex) = g1)") THEN REWRITE_TAC [] THEN EXPAND_TAC "g1" THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [COMPLEX_EMBEDDINGS_CNJ_CNJ], ALL_TAC] THEN SUBGOAL_THEN (← q r"RESTRICTION (ring_carrier k) (cnj o (g:A->complex)) IN
        complex_embeddings k /\
        RESTRICTION (ring_carrier k) (cnj o g) x = cnj(g x)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN USE_THEN "bd" (fun th => tactic_of do pure (MP_TAC (← MP (← SPEC (← q r"g:A->complex") th) (← ASSUME (← q r"(g:A->complex) IN complex_embeddings k"))) THEN MP_TAC (← MP (← SPEC (← q r"RESTRICTION (ring_carrier k) (cnj o (g:A->complex))") th) (← ASSUME (← q r"RESTRICTION (ring_carrier k) (cnj o (g:A->complex)) IN
                           complex_embeddings k"))))) THEN REWRITE_TAC [(← ASSUME (← q r"~((g:A->complex) = g0)")), (← ASSUME (← q r"~(RESTRICTION (ring_carrier k) (cnj o (g:A->complex)) = g0)")), (← ASSUME (← q r"RESTRICTION (ring_carrier k) (cnj o (g:A->complex)) x =
                cnj(g x)")), RE_CNJ, IM_CNJ] THEN MP_TAC (← SPEC (← q r"(g:A->complex) x") COMPLEX_NORM_LE_RE_IM) THEN REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"norm((g0:A->complex) x) <= C") ASSUME_TAC THENL [USE_THEN "bd" (fun th => tactic_of do pure (MP_TAC (← MP (← SPEC (← q r"g0:A->complex") th) (← ASSUME (← q r"(g0:A->complex) IN complex_embeddings k"))) THEN MP_TAC (← MP (← SPEC (← q r"g1:A->complex") th) (← ASSUME (← q r"(g1:A->complex) IN complex_embeddings k"))))) THEN REWRITE_TAC [(← ASSUME (← q r"(g1:A->complex) x = cnj((g0:A->complex) x)")), RE_CNJ, IM_CNJ] THEN MP_TAC (← SPEC (← q r"(g0:A->complex) x") COMPLEX_NORM_LE_RE_IM) THEN UNDISCH_TAC (← q r"&1 <= (C:real)") THEN COND_CASES_TAC THEN REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"&1 / &2 < norm((g0:A->complex) x)") ASSUME_TAC THENL [REWRITE_TAC [(← GSYM REAL_NOT_LE)] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A")] RING_OF_INTEGERS_NORM_PRODUCT_GE_1) THEN ASM_REWRITE_TAC [REAL_NOT_LE] THEN TRANS_TAC REAL_LET_TRANS (← q r"product (complex_embeddings k) (\g:A->complex. &1 / &2)") THEN CONJ_TAC THENL [MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC [NORM_POS_LE] THEN X_GEN_TAC (← q r"g:A->complex") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"g:A->complex = g0") THEN ASM_REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"g:A->complex = g1") THEN ASM_SIMP_TAC [COMPLEX_NORM_CNJ], ASM_SIMP_TAC [PRODUCT_CONST] THEN RULE_ASSUM_TAC (REWRITE_RULE [HAS_SIZE]) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_POW_1_LT THEN CONJ_TAC THENL [ASM_ARITH_TAC, REAL_ARITH_TAC]], ALL_TAC] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A")] NUMBER_FIELD_GENERATOR_CONJUGATES) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o CONJUNCT2) THEN EXISTS_TAC (← q r"g0:A->complex") THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"h:A->complex") THEN STRIP_TAC THEN MATCH_MP_TAC r11 THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"h:A->complex = g1") THENL [SUBGOAL_THEN (← q r"~(g1:A->complex = g0)") ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"Im((g0:A->complex) x) = &0") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"cnj((g0:A->complex) x) = g0 x") MP_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN REWRITE_TAC [COMPLEX_EQ, RE_CNJ, IM_CNJ] THEN REAL_ARITH_TAC, ALL_TAC] THEN USE_THEN "bd" (fun th => tactic_of do pure (MP_TAC (← MP (← SPEC (← q r"g1:A->complex") th) (← ASSUME (← q r"(g1:A->complex) IN complex_embeddings k"))))) THEN REWRITE_TAC [(← ASSUME (← q r"(g1:A->complex) x = cnj((g0:A->complex) x)")), (← ASSUME (← q r"~((g1:A->complex) = g0)")), RE_CNJ, IM_CNJ] THEN MP_TAC (← SPEC (← q r"(g0:A->complex) x") COMPLEX_NORM_LE_RE_IM) THEN UNDISCH_TAC (← q r"&1 / &2 < norm((g0:A->complex) x)") THEN UNDISCH_TAC (← q r"Im((g0:A->complex) x) = &0") THEN REAL_ARITH_TAC, FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"h:A->complex")) o (checkM (fun th => (do if ← (do let z7 ← (do let z8 ← (pure th); pure (concl z8)); let z6 ← (q r"g1:A->complex"); pure (free_in z6 z7)) then (do let z9 ← (do let z10 ← (pure th); pure (concl z10)); pure (is_forall z9)) else pure false))))) THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"&1 / &2 < norm((g0:A->complex) x)") THEN REAL_ARITH_TAC], X_GEN_TAC (← q r"g:A->complex") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"g:A->complex = g0") THEN ASM_REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"g:A->complex = g1") THEN ASM_SIMP_TAC [COMPLEX_NORM_CNJ] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"&1 / &2") THEN CONJ_TAC THENL [FIRST_X_ASSUM (MATCH_MP_TAC o (checkM (fun th => (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); let z1 ← (q r"g1:A->complex"); pure (free_in z1 z2)) then (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); pure (is_forall z4)) else pure false)))) THEN ASM_REWRITE_TAC [], UNDISCH_TAC (← q r"&1 <= (C:real)") THEN REAL_ARITH_TAC]])

  let NUMBER_FIELD_HERMITE_POLYNOMIAL ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"&0 <= (x:real) ==> &0 <= &1 + x"
    let r2 ← REAL_ARITH q1
    let q3 ← q r"i:num"
    let q4 ← q r"p:(1->num)->int"
    let q5 ← q r"integer_ring"
    let v6 ← ISPECL [q5, q4, q3] COEFF_ABOVE_DEG
    let q7 ← q r"coeff i (p:(1->num)->int) = &0"
    let q8 ← q r"i:num <= n"
    let q9 ← q r"i:num"
    let q10 ← q r"g:A->complex"
    let q11 ← q r"(w:complex) IN IMAGE (\g:A->complex. g x) (complex_embeddings k)"
    let q12 ← q r"w:complex"
    let q13 ← q r"R:real"
    let q14 ← q r"\i. Cx(real_of_int(coeff i (p:(1->num)->int)))"
    let q15 ← q r"n:num"
    let v16 ← ISPECL [q15, q14, q13] COMPLEX_POLYFUN_MONIC_COEFF_BOUND
    let q17 ← q r"IMAGE (\g:A->complex. g x) (complex_embeddings k) =
    {z | vsum(0..n) (\i. Cx(real_of_int(coeff i (p:(1->num)->int))) *
                         z pow i) = Cx(&0)}"
    let q18 ← q r"d:num = n"
    let q19 ← q r"{z | vsum(0..d) (\i. Cx(real_of_int(coeff i (p:(1->num)->int))) *
                          z pow i) = Cx(&0)}"
    let q20 ← q r"IMAGE (\g:A->complex. g x) (complex_embeddings k)"
    let v21 ← ISPECL [q20, q19] CARD_SUBSET
    let q22 ← q r"IMAGE (\g:A->complex. g x) (complex_embeddings k) SUBSET
    {z | vsum(0..d) (\i. Cx(real_of_int(coeff i (p:(1->num)->int))) *
                         z pow i) = Cx(&0)}"
    let q23 ← q r"d:num"
    let q24 ← q r"\i. Cx(real_of_int(coeff i (p:(1->num)->int)))"
    let q25 ← q r"d:num"
    let v26 ← ISPECL [q25, q24] COMPLEX_POLYFUN_ROOTBOUND
    let q27 ← q r"CARD(IMAGE (\g:A->complex. g x) (complex_embeddings k)) = n"
    let q28 ← q r"x:A"
    let q29 ← q r"k:A ring"
    let v30 ← ISPECL [q29, q28] NUMBER_FIELD_GENERATOR_CONJUGATES
    let q31 ← q r"!g h. g IN complex_embeddings k /\ h IN complex_embeddings k /\
          (g:A->complex) x = h x
          ==> g = h"
    let q32 ← q r"(a:complex) = b ==> c = a ==> b = c"
    let r33 ← MESON [] q32
    let q34 ← q r"p:(1->num)->int"
    let q35 ← q r"g:A->complex"
    let q36 ← q r"\v:1. (x:A)"
    let q37 ← q r"(:1)"
    let q38 ← q r"ring_of_int k:int->A"
    let q39 ← q r"complex_ring"
    let q40 ← q r"k:A ring"
    let q41 ← q r"integer_ring"
    let v42 ← ISPECL [q41, q40, q39, q38, q37, q36, q35, q34] POLY_EXTEND_HOMOMORPHIC_IMAGE
    let q43 ← q r"(g:A->complex) IN complex_embeddings k"
    let q44 ← q r"ring_homomorphism(k,complex_ring) (g:A->complex)"
    let q45 ← q r"g:A->complex"
    let q46 ← q r"!g. g IN complex_embeddings k
        ==> vsum(0..d) (\i. Cx(real_of_int(coeff i (p:(1->num)->int))) *
                            (g:A->complex) x pow i) = Cx(&0)"
    let q47 ← q r"(p:(1->num)->int) IN ring_carrier(poly_ring integer_ring (:1))"
    let v48 ← ASSUME q47
    let q49 ← q r"poly_deg integer_ring (p:(1->num)->int) = d"
    let v50 ← ASSUME q49
    let q51 ← q r"p:(1->num)->int"
    let q52 ← q r"\v:1. (z:complex)"
    let q53 ← q r"ring_of_int complex_ring:int->complex"
    let q54 ← q r"complex_ring"
    let q55 ← q r"integer_ring"
    let v56 ← ISPECL [q55, q54, q53, q52, q51] POLY_EXTEND_UNIVARIATE
    let q57 ← q r"!z. vsum(0..d) (\i. Cx(real_of_int(coeff i (p:(1->num)->int))) *
                        z pow i) =
        poly_extend (integer_ring,complex_ring) (ring_of_int complex_ring)
                    (\v:1. z) p"
    let q58 ← q r"monic integer_ring (p:(1->num)->int)"
    let q59 ← q r"coeff d (p:(1->num)->int) = &1"
    let q60 ← q r"d = poly_deg integer_ring (p:(1->num)->int)"
    let q61 ← q r"p:(1->num)->int"
    let q62 ← q r"x:A"
    let q67 ← q r"poly_deg integer_ring (p:(1->num)->int) <= n"
    let q68 ← q r"(x:A) IN ring_carrier k"
    let q69 ← q r"p:(1->num)->int"
    let q70 ← q r"x:A"
    let q71 ← q r"k:A ring"
    let v72 ← ISPECL [q71, q70] RING_OF_INTEGERS_INTEGER_MINIMAL_POLYNOMIAL
    let q73 ← q r"x:A"
    let q74 ← q r"R = &2 pow (n - 1) *
        sqrt(abs(real_of_int(number_field_discriminant(k:A ring))))"
    let q75 ← q r"k:A ring"
    let v76 ← ISPEC q75 NUMBER_FIELD_HERMITE_GENERATOR
    prove
      r"!(k:A ring) n.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = n
          ==> ?x p. x IN ring_carrier(ring_of_integers k) /\
                    subfield_generated k {x} = k /\
                    p IN ring_carrier(poly_ring integer_ring (:1)) /\
                    monic integer_ring p /\ poly_deg integer_ring p = n /\
                    (!i. abs(real_of_int(coeff i p)) <=
                         (&1 + &2 pow (n - 1) *
                               sqrt(abs(real_of_int
                                      (number_field_discriminant k)))) pow n) /\
                    poly_extend (integer_ring,k) (ring_of_int k) (\v. x) p =
                    ring_0 k"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [number_field])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP COMPLEX_EMBEDDINGS_HAS_SIZE)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITE_COMPLEX_EMBEDDINGS)) THEN MP_TAC v76 THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC q74 THEN DISCH_THEN (X_CHOOSE_THEN q73 STRIP_ASSUME_TAC) THEN MP_TAC v72 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN q69 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "deg") ASSUME_TAC)))) THEN SUBGOAL_THEN q68 ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN q67 ASSUME_TAC THENL [REMOVE_THEN "deg" SUBST1_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z66 ← (q r"n:num"); let z65 ← (do let z63 ← (do let z64 ← (pure th); pure (concl z64)); liftExcept (rand z63)); pure (z65 == z66)))))) THEN MATCH_MP_TAC MINIMAL_POLYNOMIAL_DEG_LE_EXTENSION_DEGREE THEN ASM_REWRITE_TAC [], REMOVE_THEN "deg" (fun (_ : thm) => ALL_TAC)] THEN MAP_EVERY EXISTS_TAC [q62, q61] THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC q60 THEN SUBGOAL_THEN q59 ASSUME_TAC THENL [UNDISCH_TAC q58 THEN ASM_REWRITE_TAC [monic, INTEGER_RING], ALL_TAC] THEN SUBGOAL_THEN q57 (LABEL_TAC "ext") THENL [GEN_TAC THEN MP_TAC v56 THEN REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, COMPLEX_RING_CLAUSES, IN_UNIV, v50, v48] THEN DISCH_THEN SUBST1_TAC THEN SIMP_TAC [COMPLEX_RING_SUM, FINITE_NUMSEG, COMPLEX_RING_CLAUSES, COMPLEX_RING_OF_INT, COMPLEX_RING_POW], ALL_TAC] THEN SUBGOAL_THEN q46 ASSUME_TAC THENL [X_GEN_TAC q45 THEN DISCH_TAC THEN SUBGOAL_THEN q44 ASSUME_TAC THENL [UNDISCH_TAC q43 THEN SIMP_TAC [complex_embeddings, IN_ELIM_THM], ALL_TAC] THEN USE_THEN "ext" (fun th => REWRITE_TAC [th]) THEN MP_TAC v42 THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN ANTS_TAC THENL [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_UNIV] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_0 th)])) THEN REWRITE_TAC [COMPLEX_RING_CLAUSES] THEN MATCH_MP_TAC r33 THEN AP_THM_TAC THEN BINOP_TAC THEN REWRITE_TAC [FUN_EQ_THM, o_THM] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_RING_OF_INT th)])), REMOVE_THEN "ext" (fun (_ : thm) => ALL_TAC)] THEN SUBGOAL_THEN q31 ASSUME_TAC THENL [MP_TAC v30 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ACCEPT_TAC o CONJUNCT1), ALL_TAC] THEN SUBGOAL_THEN q27 ASSUME_TAC THENL [wPart lhand (lhand o rand) CARD_IMAGE_INJ THEN ANTS_TAC THENL [ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN ASM_MESON_TAC [HAS_SIZE], ALL_TAC] THEN MP_TAC v26 THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [DISCH_THEN (MP_TAC o (SPEC q23)) THEN ASM_REWRITE_TAC [IN_NUMSEG, LE_0, LE_REFL, CX_INJ] THEN REWRITE_TAC [int_of_num_th] THEN REAL_ARITH_TAC, STRIP_TAC] THEN SUBGOAL_THEN q22 ASSUME_TAC THENL [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC v21 THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN q18 SUBST_ALL_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN q17 ASSUME_TAC THENL [MATCH_MP_TAC CARD_SUBSET_EQ THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC, ALL_TAC] THEN MP_TAC v16 THEN ASM_REWRITE_TAC [int_of_num_th] THEN ANTS_TAC THENL [X_GEN_TAC q12 THEN DISCH_TAC THEN SUBGOAL_THEN q11 MP_TAC THENL [ASM_REWRITE_TAC [IN_ELIM_THM], ALL_TAC] THEN REWRITE_TAC [IN_IMAGE] THEN DISCH_THEN (X_CHOOSE_THEN q10 (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN ASM_SIMP_TAC [], ALL_TAC] THEN REWRITE_TAC [COMPLEX_NORM_CX] THEN DISCH_TAC THEN X_GEN_TAC q9 THEN ASM_CASES_TAC q8 THEN ASM_SIMP_TAC [] THEN SUBGOAL_THEN q7 SUBST1_TAC THENL [MP_TAC v6 THEN ASM_REWRITE_TAC [RING_POLYNOMIAL, INTEGER_RING] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC, REWRITE_TAC [int_of_num_th, REAL_ABS_0] THEN MATCH_MP_TAC REAL_POW_LE THEN EXPAND_TAC "R" THEN MATCH_MP_TAC r2 THEN MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC [REAL_POW_LE, REAL_POS, SQRT_POS_LE, REAL_ABS_POS]])

  -- @@RETURN BEGIN
  return { RING_OF_INTEGERS_NORM_PRODUCT_GE_1, RING_OF_INTEGERS_SUM_NORM_POW_2,
           NUMBER_FIELD_DISCRIMINANT_HERMITE_BOUND, NUMBER_FIELD_GENERATOR_CONJUGATES,
           NUMBER_FIELD_HERMITE_GENERATOR, NUMBER_FIELD_HERMITE_POLYNOMIAL }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- hermite.ml phrases from line 812 to 987                                -/
/- ---------------------------------------------------------------------- -/

structure Hermite02 where
  -- @@FIELDS
  NUMBER_FIELD_HERMITE_POLYNOMIALS : thm
  NUMBER_FIELD_HERMITE : thm
  NUMBER_FIELD_HERMITE_ISOMORPHIC : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupHermite02 [HolBase] (D : HermiteDeps) (BHermite01 : Hermite01) :
    ExceptT String IO Hermite02 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON, REAL_ARITH, SET_TAC, .. } := D
  let { CARRIER_SUBFIELD_GENERATED_SUBFIELD, COEFF_ABOVE_DEG,
        COMPLEX_EMBEDDINGS_MONOMORPHISM, COMPLEX_EMBEDDINGS_NONEMPTY,
        COMPLEX_RING_CLAUSES, EXISTS_IN_IMAGE, FIELD_COMPLEX_RING,
        FIELD_IMP_INTEGRAL_DOMAIN, FIELD_IMP_NONTRIVIAL_RING, FINITE_FUNSPACE,
        FINITE_IMAGE, FINITE_INT_SEG, FINITE_NUMSEG, FINITE_SUBSET, FINITE_UNIONS,
        FORALL_IN_IMAGE, FUN_EQ_COEFF, FUN_EQ_THM, IMAGE_CLAUSES, INTEGER_RING,
        INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING, INT_ABS_BOUNDS, IN_ELIM_THM, IN_IMAGE,
        IN_NUMSEG, IN_RING_POLYNOMIAL_CARRIER_COMPOSE, IN_SING, IN_UNIONS, IN_UNIV,
        I_O_ID, LE_0, MEMBER_NOT_EMPTY, MONIC_HOMOMORPHIC_IMAGE, MONIC_IMP_NONZERO,
        NOT_LE, NUMBER_FIELD_IMP_FIELD, POLY_EXTEND_COMPOSE_COEFFS, .. } := D.core1
  let { POLY_EXTEND_HOMOMORPHIC_IMAGE, POLY_EXTEND_INTO_SUBRING_GENERATED,
        POLY_RING_CLAUSES, POLY_ROOT_BOUND, PRIME_SUBFIELD_SUBFIELD_GENERATED,
        REAL_ABS_POS, REAL_ARCH_SIMPLE, REAL_LE_LADD, REAL_LE_LMUL, REAL_LE_MUL,
        REAL_LE_TRANS, REAL_POS, REAL_POW_LE, REAL_POW_LE2, RING_HOMOMORPHISM_0,
        RING_HOMOMORPHISM_I, RING_HOMOMORPHISM_INTEGER_RING_OF_INT,
        RING_HOMOMORPHISM_RING_OF_INT, RING_ISOMORPHISM_ONTO_SUBFIELD_IMAGE,
        RING_OF_INTEGERS_SUBSET, RING_OF_INT_SUBFIELD_GENERATED, RING_POLYNOMIAL,
        SING_SUBSET, SQRT_MONO_LE, SQRT_POS_LE, SUBFIELD_GENERATED,
        SUBFIELD_GENERATED_BY_MONOMORPHIC_IMAGE, SUBFIELD_GENERATED_INC_GEN,
        SUBFIELD_GENERATED_MINIMAL, SUBFIELD_OF_IMP_SUBSET,
        SUBFIELD_OF_SUBFIELD_GENERATED, SUBFIELD_SUBFIELD_GENERATED,
        SUBFIELD_SUBFIELD_GENERATED_ALT, SUBRING_GENERATED_BY_SUBFIELD_GENERATED,
        SUBSET, SUBSET_ANTISYM, coeff, complex_embeddings, int_abs_th, int_le,
        int_of_num_th, isomorphic_ring, o_THM, poly_eval, poly_evaluate, .. } := D.core2
  let { NUMBER_FIELD_HERMITE_POLYNOMIAL, .. } := BHermite01
  -- @@SCOPE END

  let NUMBER_FIELD_HERMITE_POLYNOMIALS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"&0 <= (x:real) ==> &0 <= &1 + x")
    let r2 ← REAL_ARITH (← q r"b <= c ==> a <= b ==> a <= c:real")
    prove
      r"!n X. ?P. FINITE P /\
               (!p. p IN P
                    ==> p IN ring_carrier(poly_ring integer_ring (:1)) /\
                        monic integer_ring p /\ poly_deg integer_ring p = n) /\
               !k:A ring.
                  number_field k /\
                  extension_degree (subfield_generated k {ring_0 k},k) I = n /\
                  abs(real_of_int(number_field_discriminant k)) <= X
                  ==> ?p x. p IN P /\ x IN ring_carrier(ring_of_integers k) /\
                            subfield_generated k {x} = k /\
                            poly_extend (integer_ring,k) (ring_of_int k)
                                        (\v. x) p =
                            ring_0 k"
      (REPEAT GEN_TAC THEN ABBREV_TAC (← q r"B = (&1 + &2 pow (n - 1) * sqrt X) pow n") THEN EXISTS_TAC (← q r"{p | p IN ring_carrier(poly_ring integer_ring (:1)) /\
           monic integer_ring p /\ poly_deg integer_ring p = n /\
           !i. abs(real_of_int(coeff i p)) <= B}") THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"IMAGE (\c:num->int m:1->num. c(m one))
              {c | (!i. i IN 0..n ==> c i IN {u:int | abs(real_of_int u) <= B}) /\
                   (!i. ~(i IN 0..n) ==> c i = &0)}") THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_FUNSPACE THEN REWRITE_TAC [FINITE_NUMSEG] THEN MP_TAC (← SPEC (← q r"B:real") REAL_ARCH_SIMPLE) THEN DISCH_THEN (X_CHOOSE_TAC (← q r"N:num")) THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{u:int | --(&N) <= u /\ u <= &N}") THEN REWRITE_TAC [FINITE_INT_SEG, SUBSET, IN_ELIM_THM, (← GSYM INT_ABS_BOUNDS)] THEN REWRITE_TAC [int_le, int_abs_th, int_of_num_th] THEN ASM_MESON_TAC [REAL_LE_TRANS], ALL_TAC] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM, IN_IMAGE, IN_NUMSEG, LE_0, NOT_LE] THEN X_GEN_TAC (← q r"p:(1->num)->int") THEN STRIP_TAC THEN EXISTS_TAC (← q r"\i. coeff i (p:(1->num)->int)") THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [REWRITE_TAC [(← GSYM FUN_EQ_COEFF)] THEN REWRITE_TAC [coeff], REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"p:(1->num)->int"), (← q r"i:num")] COEFF_ABOVE_DEG) THEN ASM_REWRITE_TAC [RING_POLYNOMIAL, INTEGER_RING]], SIMP_TAC [IN_ELIM_THM], X_GEN_TAC (← q r"k:A ring") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num")] NUMBER_FIELD_HERMITE_POLYNOMIAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"x:A") (X_CHOOSE_THEN (← q r"p:(1->num)->int") STRIP_ASSUME_TAC)) THEN MAP_EVERY EXISTS_TAC [(← q r"p:(1->num)->int"), (← q r"x:A")] THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"i:num") THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"i:num")) o (checkM (fun th => (do if ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); pure (is_forall z3)) then (do let z6 ← (do let z7 ← (pure th); pure (concl z7)); let z5 ← (q r"coeff:num->((1->num)->int)->int"); pure (free_in z5 z6)) else pure false))))) THEN MATCH_MP_TAC r2 THEN EXPAND_TAC "B" THEN MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL [MATCH_MP_TAC r1 THEN MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC [REAL_POW_LE, REAL_POS, SQRT_POS_LE, REAL_ABS_POS], REWRITE_TAC [REAL_LE_LADD] THEN MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC [REAL_POW_LE, REAL_POS] THEN MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC []]])

  let NUMBER_FIELD_HERMITE ← prove
    r"!(l:B ring) n X.
        integral_domain l
        ==> FINITE {s | s subfield_of l /\
                        number_field(subfield_generated l s) /\
                        extension_degree (subfield_generated l {ring_0 l},
                                          subfield_generated l s) I = n /\
                        abs(real_of_int(number_field_discriminant
                                         (subfield_generated l s))) <= X}"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"n:num"), (← q r"X:real")] (← INST_TYPE [((← qty r"B"), (← qty r"A"))] NUMBER_FIELD_HERMITE_POLYNOMIALS)) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"P:((1->num)->int)->bool") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "P")))) THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"IMAGE (\x:B. ring_carrier(subfield_generated l {x}))
          (UNIONS (IMAGE (\p. {x | x IN ring_carrier l /\
                                   poly_eval l (ring_of_int l o p) x =
                                   ring_0 l}) P))") THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC [FINITE_UNIONS] THEN ASM_SIMP_TAC [FINITE_IMAGE, FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"p:(1->num)->int") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"p:(1->num)->int"))) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"ring_of_int (l:B ring) o (p:(1->num)->int)")] POLY_ROOT_BOUND) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [ALL_TAC, SIMP_TAC []] THEN SUBGOAL_THEN (← q r"~trivial_ring(l:B ring)") ASSUME_TAC THENL [ASM_MESON_TAC [INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"l:B ring"), (← q r"ring_of_int l:int->B"), (← q r"p:(1->num)->int")] MONIC_HOMOMORPHIC_IMAGE) THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"l:B ring"), (← q r"ring_of_int l:int->B"), (← q r"(:1)"), (← q r"p:(1->num)->int")] IN_RING_POLYNOMIAL_CARRIER_COMPOSE) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [POLY_RING_CLAUSES] THEN MATCH_MP_TAC MONIC_IMP_NONZERO THEN ASM_REWRITE_TAC [RING_POLYNOMIAL], ALL_TAC] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM, IN_IMAGE, IN_UNIONS, EXISTS_IN_IMAGE] THEN X_GEN_TAC (← q r"s:B->bool") THEN STRIP_TAC THEN REMOVE_THEN "P" (MP_TAC o (SPEC (← q r"subfield_generated l (s:B->bool)"))) THEN ASM_REWRITE_TAC [PRIME_SUBFIELD_SUBFIELD_GENERATED] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"p:(1->num)->int") (X_CHOOSE_THEN (← q r"x:B") STRIP_ASSUME_TAC)) THEN SUBGOAL_THEN (← q r"ring_carrier(subfield_generated l s) = (s:B->bool)") ASSUME_TAC THENL [ASM_SIMP_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD], ALL_TAC] THEN SUBGOAL_THEN (← q r"(x:B) IN s") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [SUBFIELD_OF_IMP_SUBSET, SUBSET], ALL_TAC] THEN EXISTS_TAC (← q r"x:B") THEN CONJ_TAC THENL [ALL_TAC, EXISTS_TAC (← q r"p:(1->num)->int") THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN SUBGOAL_THEN (← q r"(p:(1->num)->int) IN ring_carrier(poly_ring integer_ring (:1))") ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN REWRITE_TAC [poly_eval, poly_evaluate] THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"l:B ring"), (← q r"l:B ring"), (← q r"ring_of_int l:int->B"), (← q r"I:B->B"), (← q r"\v:1. (x:B)"), (← q r"p:(1->num)->int")] POLY_EXTEND_COMPOSE_COEFFS) THEN REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, RING_HOMOMORPHISM_I, I_O_ID] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"l:B ring"), (← q r"s:B->bool"), (← q r"ring_of_int l:int->B"), (← q r"(:1)"), (← q r"\v:1. (x:B)"), (← q r"p:(1->num)->int")] POLY_EXTEND_INTO_SUBRING_GENERATED) THEN SUBGOAL_THEN (← q r"subring_generated l s = subfield_generated l (s:B->bool)") SUBST1_TAC THENL [ASM_MESON_TAC [SUBRING_GENERATED_BY_SUBFIELD_GENERATED], ALL_TAC] THEN MP_TAC (← ISPEC (← q r"subfield_generated l (s:B->bool)") RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN REWRITE_TAC [RING_OF_INT_SUBFIELD_GENERATED] THEN DISCH_TAC THEN ASM_REWRITE_TAC [IN_UNIV] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); let z1 ← (q r"poly_extend:(int ring#B ring)->(int->B)->(1->B)->                            ((1->num)->int)->B"); pure (free_in z1 z2))))) THEN REWRITE_TAC [RING_OF_INT_SUBFIELD_GENERATED, (← CONJUNCT2 SUBFIELD_GENERATED)]] THEN SUBGOAL_THEN (← q r"ring_carrier(subfield_generated l {x:B}) SUBSET s") ASSUME_TAC THENL [MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN ASM SET_TAC [], ALL_TAC] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"s = ring_carrier(subfield_generated (subfield_generated l s) {x:B})") SUBST1_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN REWRITE_TAC [SING_SUBSET] THEN CONJ_TAC THENL [MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN ASM_REWRITE_TAC [IN_SING], MATCH_MP_TAC SUBFIELD_OF_SUBFIELD_GENERATED THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [SUBFIELD_SUBFIELD_GENERATED_ALT] THEN EXISTS_TAC (← q r"s:B->bool") THEN ASM SET_TAC []])

  let NUMBER_FIELD_HERMITE_ISOMORPHIC ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"(a:complex) = b ==> c = a ==> b = c"
    let r2 ← MESON [] q1
    let q3 ← q r"p:(1->num)->int"
    let q4 ← q r"g:A->complex"
    let q5 ← q r"\v:1. (x:A)"
    let q6 ← q r"(:1)"
    let q7 ← q r"ring_of_int k:int->A"
    let q8 ← q r"complex_ring"
    let q9 ← q r"k:A ring"
    let q10 ← q r"integer_ring"
    let v11 ← ISPECL [q10, q9, q8, q7, q6, q5, q4, q3] POLY_EXTEND_HOMOMORPHIC_IMAGE
    let q12 ← q r"p:(1->num)->int"
    let q13 ← q r"\v:1. (g:A->complex) x"
    let q14 ← q r"I:complex->complex"
    let q15 ← q r"ring_of_int complex_ring:int->complex"
    let q16 ← q r"complex_ring"
    let q17 ← q r"complex_ring"
    let q18 ← q r"integer_ring"
    let v19 ← ISPECL [q18, q17, q16, q15, q14, q13, q12] POLY_EXTEND_COMPOSE_COEFFS
    let q20 ← q r"p:(1->num)->int"
    let q21 ← q r"{x:A}"
    let q22 ← q r"g:A->complex"
    let q23 ← q r"complex_ring"
    let q24 ← q r"k:A ring"
    let v25 ← ISPECL [q24, q23, q22, q21] SUBFIELD_GENERATED_BY_MONOMORPHIC_IMAGE
    let q26 ← q r"(g:A->complex) x"
    let q27 ← q r"IMAGE (g:A->complex) (ring_carrier k)"
    let q28 ← q r"complex_ring"
    let q29 ← q r"k:A ring"
    let q30 ← q r"g:A->complex"
    let v31 ← ISPECL [q30, q29, q28] RING_ISOMORPHISM_ONTO_SUBFIELD_IMAGE
    let q32 ← q r"(p:(1->num)->int) IN ring_carrier(poly_ring integer_ring (:1))"
    let q33 ← q r"(x:A) IN ring_carrier k"
    let q34 ← q r"(g:A->complex) IN complex_embeddings k"
    let q35 ← q r"ring_homomorphism(k,complex_ring) (g:A->complex)"
    let v36 ← GSYM MEMBER_NOT_EMPTY
    let q37 ← q r"g:A->complex"
    let q38 ← q r"x:A"
    let q39 ← q r"p:(1->num)->int"
    let q40 ← q r"k:A ring"
    let q41 ← q r"k:A ring"
    let q42 ← q r"p:(1->num)->int"
    let q43 ← q r"(:1)"
    let q44 ← q r"ring_of_int complex_ring:int->complex"
    let q45 ← q r"complex_ring"
    let q46 ← q r"integer_ring"
    let v47 ← ISPECL [q46, q45, q44, q43, q42] IN_RING_POLYNOMIAL_CARRIER_COMPOSE
    let q48 ← q r"p:(1->num)->int"
    let q49 ← q r"ring_of_int complex_ring:int->complex"
    let q50 ← q r"complex_ring"
    let q51 ← q r"integer_ring"
    let v52 ← ISPECL [q51, q50, q49, q48] MONIC_HOMOMORPHIC_IMAGE
    let q53 ← q r"ring_of_int complex_ring o (p:(1->num)->int)"
    let q54 ← q r"complex_ring"
    let v55 ← ISPECL [q54, q53] POLY_ROOT_BOUND
    let q56 ← q r"p:(1->num)->int"
    let q57 ← q r"p:(1->num)->int"
    let q58 ← q r"IMAGE (\z. ring_carrier(subfield_generated complex_ring {z}))
          (UNIONS (IMAGE (\p. {z | z IN ring_carrier complex_ring /\
                                   poly_eval complex_ring
                                     (ring_of_int complex_ring o p) z =
                                   ring_0 complex_ring}) P))"
    let q59 ← q r"P:((1->num)->int)->bool"
    let q60 ← q r"X:real"
    let q61 ← q r"n:num"
    let v62 ← ISPECL [q61, q60] NUMBER_FIELD_HERMITE_POLYNOMIALS
    prove
      r"!n X. ?F. FINITE F /\ (!s. s IN F ==> s subfield_of complex_ring) /\
               !k:A ring.
                  number_field k /\
                  extension_degree (subfield_generated k {ring_0 k},k) I = n /\
                  abs(real_of_int(number_field_discriminant k)) <= X
                  ==> ?s. s IN F /\
                          k isomorphic_ring subfield_generated complex_ring s"
      (REPEAT GEN_TAC THEN MP_TAC v62 THEN DISCH_THEN (X_CHOOSE_THEN q59 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "P")))) THEN EXISTS_TAC q58 THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC [FINITE_UNIONS] THEN ASM_SIMP_TAC [FINITE_IMAGE, FORALL_IN_IMAGE] THEN X_GEN_TAC q57 THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC q56)) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC v55 THEN SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, FIELD_COMPLEX_RING] THEN ANTS_TAC THENL [ALL_TAC, SIMP_TAC []] THEN MP_TAC v52 THEN MP_TAC v47 THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, FIELD_COMPLEX_RING, FIELD_IMP_NONTRIVIAL_RING] THEN DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [POLY_RING_CLAUSES] THEN MATCH_MP_TAC MONIC_IMP_NONZERO THEN ASM_SIMP_TAC [RING_POLYNOMIAL, FIELD_COMPLEX_RING, FIELD_IMP_NONTRIVIAL_RING], REWRITE_TAC [FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBFIELD_SUBFIELD_GENERATED THEN REWRITE_TAC [FIELD_COMPLEX_RING], ALL_TAC] THEN X_GEN_TAC q41 THEN STRIP_TAC THEN REMOVE_THEN "P" (MP_TAC o (SPEC q40)) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN q39 (X_CHOOSE_THEN q38 STRIP_ASSUME_TAC)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM ((X_CHOOSE_TAC q37) o ((REWRITE_RULE [v36]) o (MATCH_MP COMPLEX_EMBEDDINGS_NONEMPTY))) THEN SUBGOAL_THEN q35 ASSUME_TAC THENL [UNDISCH_TAC q34 THEN SIMP_TAC [complex_embeddings, IN_ELIM_THM], ALL_TAC] THEN SUBGOAL_THEN q33 ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN q32 ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN MP_TAC v31 THEN ASM_REWRITE_TAC [FIELD_COMPLEX_RING] THEN STRIP_TAC THEN EXISTS_TAC q27 THEN CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC [isomorphic_ring]] THEN REWRITE_TAC [IN_IMAGE, IN_UNIONS, EXISTS_IN_IMAGE] THEN EXISTS_TAC q26 THEN CONJ_TAC THENL [MP_TAC v25 THEN ASM_REWRITE_TAC [IMAGE_CLAUSES, SING_SUBSET] THEN ASM_SIMP_TAC [COMPLEX_EMBEDDINGS_MONOMORPHISM], ALL_TAC] THEN EXISTS_TAC q20 THEN ASM_REWRITE_TAC [IN_ELIM_THM, COMPLEX_RING_CLAUSES, IN_UNIV] THEN REWRITE_TAC [poly_eval, poly_evaluate] THEN MP_TAC v19 THEN REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, RING_HOMOMORPHISM_I, I_O_ID] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC v11 THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN ANTS_TAC THENL [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_UNIV] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_0 th)])) THEN REWRITE_TAC [COMPLEX_RING_CLAUSES] THEN MATCH_MP_TAC r2 THEN AP_THM_TAC THEN BINOP_TAC THEN REWRITE_TAC [FUN_EQ_THM, o_THM] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_RING_OF_INT th)])))

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_HERMITE_POLYNOMIALS, NUMBER_FIELD_HERMITE,
           NUMBER_FIELD_HERMITE_ISOMORPHIC }
  -- @@RETURN END

end HolANT.Hermite
