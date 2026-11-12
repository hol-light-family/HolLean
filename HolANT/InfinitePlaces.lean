/- ========================================================================= -/
/- ANT: Real embeddings and infinite places of a number field k            -/
/- ========================================================================= -/
/- File: HolANT/InfinitePlaces.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/infinite_places.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antinfiniteplacesdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/products.ml, ANT/ideal_arith.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/discriminant.ml, ANT/power_basis.ml, Library/frag.ml, Library/grouptheory.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/classgroup.ml, ANT/nf_valuation.ml, ANT/prime_split.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/integrality.ml, Library/ring_groups.ml, ANT/fingen_group.ml, Multivariate/misc.ml, Multivariate/metric.ml, Multivariate/homology.ml, Multivariate/vectors.ml, Multivariate/determinants.ml, Multivariate/topology.ml, Multivariate/convex.ml, Multivariate/paths.ml, Multivariate/polytope.ml, Multivariate/degree.ml, Multivariate/derivatives.ml, Multivariate/integration.ml, Multivariate/measure.ml, Multivariate/complex_algebra.ml, Multivariate/complexes.ml, Multivariate/canal.ml, Multivariate/transcendentals.ml, Multivariate/realanalysis.ml, Multivariate/moretop.ml, Multivariate/cauchy.ml, Multivariate/complex_ring.ml, Multivariate/complex_field.ml, ANT/complex_embeddings.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.InfinitePlaces fills them).

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
import HolANT.IdealArith
import HolANT.Algmisc
import HolANT.Integral
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.IdealNorm
import HolLibrary.Isum
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolANT.RingOfIntegers
import HolANT.NormIndex
import HolANT.Discriminant
import HolANT.PowerBasis
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
open HolANT.Numfield
open HolANT.RingOfIntegers
open HolANT.NormIndex
open HolANT.Discriminant
open HolANT.PowerBasis
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

namespace HolANT.InfinitePlaces

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (AND_FORALL_THM ARITH_EQ CARD_CLAUSES CARD_DIFF CARD_EQ_0 CARD_EQ_NSUM
   CARD_IMAGE_INJ CARD_NUMSEG_LT CARD_SUBSET CARD_SUBSET_EQ CNJ_ADD CNJ_CNJ
   CNJ_CX CNJ_MUL CNJ_NEG CNJ_VSUM COMPLEX_EMBEDDINGS_HAS_SIZE
   COMPLEX_EMBEDDINGS_MONOMORPHISM COMPLEX_EMBEDDINGS_NONEMPTY
   COMPLEX_EMBEDDINGS_ROOT_OF_UNITY COMPLEX_EQ COMPLEX_MUL_CNJ COMPLEX_MUL_LID
   COMPLEX_MUL_LNEG COMPLEX_MUL_SYM COMPLEX_NORM_CNJ COMPLEX_NORM_CX
   COMPLEX_NORM_MUL COMPLEX_NORM_NZ COMPLEX_NORM_POW COMPLEX_NORM_ZERO
   COMPLEX_POW_2 COMPLEX_RING_CLAUSES COMPLEX_RING_OF_INT COMPLEX_RING_POW
   COMPLEX_RING_PRODUCT COMPLEX_RING_SUM COMPLEX_SQNORM CONTRAPOS_THM CX_ADD
   CX_INJ CX_MUL CX_NEG CX_POW DIV_MULT EQ_TRANS ETA_AX EXISTS_UNIQUE_THM
   EXTENSION EXTENSIONAL EXTENSIONAL_EQ FIELD_COMPLEX_RING
   FINITE_COMPLEX_EMBEDDINGS FINITE_EMPTY FINITE_IMAGE FINITE_INSERT
   FINITE_NUMSEG_LT FINITE_RESTRICT FINITE_SING FINITE_SUBSET FORALL_IN_IMAGE
   FREE_BASIS_IN_CARRIER FUN_EQ_THM HAS_SIZE HAS_SIZE_INDEX
   IDEAL_GENERATED_INC_GEN IDEAL_GENERATED_SING_EQ_CARRIER IDEAL_NORM_CARRIER
   IDEAL_NORM_GT_1 IM IMP_CONJ IM_ADD IM_CNJ IM_CX IM_NEG IN
   INJECTIVE_ON_LEFT_INVERSE INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING
   INTEGRAL_DOMAIN_RING_OF_INTEGERS IN_DIFF IN_ELIM_THM IN_EXTENSIONAL IN_IMAGE
   IN_INSERT IN_SING IN_UNIV MEMBER_NOT_EMPTY MONO_AND MONO_EXISTS MULT_SYM
   NORM_CPRODUCT NOT_FORALL_THM NOT_IMP : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (NOT_IN_EMPTY NSUM_ADD NSUM_CLAUSES NSUM_CONST NSUM_EQ NSUM_IMAGE_GEN
   NSUM_RESTRICT_SET NSUM_SING NUMBER_FIELD_DEGREE_POS
   NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS
   NUMBER_FIELD_DISCRIMINANT_NONZERO NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_Q
   NUMBER_FIELD_IMP_FIELD NUMBER_FIELD_NORM_HOMOMORPHISMS
   NUMBER_FIELD_TRACE_HOMOMORPHISMS PERMUTES_INVOLUTION PRODUCT_EQ_0 RE REAL
   REAL_CNJ REAL_LE_SQUARE REAL_MUL_LZERO REAL_MUL_RZERO REAL_OF_NUM_EQ
   REAL_POW2_ABS REAL_POW_NEG REAL_POW_ONE REAL_RING_CLAUSES REAL_SUB_RZERO
   RESTRICTION RESTRICTION_COMPOSE_RIGHT RESTRICTION_FIXPOINT
   RESTRICTION_IN_EXTENSIONAL RESTRICTION_UNIQUE RESTRICTION_UNIQUE_ALT RE_ADD
   RE_CNJ RE_CX RE_NEG RIGHT_FORALL_IMP_THM RING_0 RING_1 RING_ADD
   RING_CARRIER_SUBFIELD_GENERATED_SUBSET RING_DET_EQ RING_DET_HOMOMORPHISM
   RING_DET_MUL RING_DET_PERMUTE_ROWS RING_DET_REINDEX RING_DET_TRANSP
   RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED RING_HOMOMORPHISM_0
   RING_HOMOMORPHISM_CNJ RING_HOMOMORPHISM_MUL RING_HOMOMORPHISM_RING_OF_INT
   RING_IDEAL_IDEAL_GENERATED RING_MONOMORPHISM_ALT_EQ RING_MUL RING_NEG
   RING_OF_INTEGERS RING_OF_INTEGERS_FINITE_QUOTIENT RING_OF_INTEGERS_FREE
   RING_OF_INTEGERS_FREE_BASIS_FIELD RING_OF_INTEGERS_SUBSET
   RING_OF_INTEGERS_UNIT_NONZERO RING_UNIT_0 RING_UNIT_IN_CARRIER
   SIGN_INVOLUTION SUBSET SUBSET_ANTISYM SUBSET_RESTRICT SUBSET_UNIV SUM_CONST
   SUM_EQ SUM_IMAGE_GEN UNIT_GROUP VSUM_EQ VSUM_IMAGE complex_embeddings
   complex_mul int_abs_th int_eq int_lt int_of_num_th o_DEF o_THM real
   ring_homomorphism ring_monomorphism ring_sign sign : thm)
  deriving Inhabited

/-- What infinite_places.ml uses from Session besides theorems. -/
structure InfinitePlacesDeps where
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
  COMPLEX_RING : term → ExceptT String IO thm
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
/- infinite_places.ml phrases from line 87 to 613                         -/
/- ---------------------------------------------------------------------- -/

structure InfinitePlaces01 where
  -- @@FIELDS
  real_embeddings : thm
  infinite_places : thm
  COMPLEX_EMBEDDINGS_CNJ : thm
  COMPLEX_EMBEDDINGS_CNJ_CNJ : thm
  REAL_EMBEDDINGS_CNJ : thm
  COMPLEX_EMBEDDINGS_NORM_POS : thm
  COMPLEX_EMBEDDINGS_NORM_MUL : thm
  COMPLEX_EMBEDDINGS_NORM_EQ : thm
  FINITE_INFINITE_PLACES : thm
  CARD_INFINITE_PLACES : thm
  CARD_INFINITE_PLACES_EQ_1 : thm
  REAL_EMBEDDINGS_MONOMORPHISM : thm
  COMPLEX_EMBEDDINGS_PRIME_SUBFIELD_REAL : thm
  COMPLEX_EMBEDDINGS_NORM_FUN_EQ : thm
  INFINITE_PLACE_EMBEDDINGS : thm
  CARD_INFINITE_PLACE_EMBEDDINGS : thm
  INFINITE_PLACES_SUM : thm
  INFINITE_PLACES_DEGREE : thm
  INFINITE_PLACES_POS : thm
  INFINITE_PLACES_MUL : thm
  INFINITE_PLACES_ROOT_OF_UNITY : thm
  INFINITE_PLACES_UNIT_GROUP : thm
  NUMBER_FIELD_TRACE_COMPLEX_EMBEDDINGS : thm
  NUMBER_FIELD_NORM_COMPLEX_EMBEDDINGS : thm
  NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS : thm
  RING_OF_INTEGERS_UNIT_NORM_PRODUCT : thm
  NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS : thm
  COMPLEX_EMBEDDINGS_VSUM_CNJ_REAL : thm
  NUMBER_FIELD_EMBEDDING_GRAM_DET : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupInfinitePlaces01 [HolBase] (D : InfinitePlacesDeps) :
    ExceptT String IO InfinitePlaces01 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, COMPLEX_RING, MESON_TAC,
        NUM_REDUCE_CONV, REAL_ARITH, REAL_RING, TAUT, new_definition, .. } := D
  let { AND_FORALL_THM, CARD_CLAUSES, CARD_EQ_0, CARD_EQ_NSUM, CARD_IMAGE_INJ,
        CARD_NUMSEG_LT, CARD_SUBSET, CARD_SUBSET_EQ, CNJ_ADD, CNJ_CNJ, CNJ_CX, CNJ_MUL,
        CNJ_NEG, CNJ_VSUM, COMPLEX_EMBEDDINGS_HAS_SIZE,
        COMPLEX_EMBEDDINGS_MONOMORPHISM, COMPLEX_EMBEDDINGS_NONEMPTY,
        COMPLEX_EMBEDDINGS_ROOT_OF_UNITY, COMPLEX_EQ, COMPLEX_MUL_CNJ, COMPLEX_MUL_SYM,
        COMPLEX_NORM_CNJ, COMPLEX_NORM_CX, COMPLEX_NORM_MUL, COMPLEX_NORM_NZ,
        COMPLEX_NORM_POW, COMPLEX_NORM_ZERO, COMPLEX_RING_CLAUSES, COMPLEX_RING_OF_INT,
        COMPLEX_RING_POW, COMPLEX_RING_PRODUCT, COMPLEX_RING_SUM, COMPLEX_SQNORM,
        CONTRAPOS_THM, CX_ADD, CX_INJ, CX_MUL, CX_NEG, CX_POW, EQ_TRANS, ETA_AX,
        EXTENSION, EXTENSIONAL, EXTENSIONAL_EQ, FIELD_COMPLEX_RING,
        FINITE_COMPLEX_EMBEDDINGS, FINITE_EMPTY, FINITE_IMAGE, FINITE_INSERT,
        FINITE_NUMSEG_LT, FINITE_RESTRICT, FINITE_SING, FINITE_SUBSET, FORALL_IN_IMAGE,
        FREE_BASIS_IN_CARRIER, FUN_EQ_THM, HAS_SIZE, IDEAL_GENERATED_INC_GEN,
        IDEAL_GENERATED_SING_EQ_CARRIER, IDEAL_NORM_CARRIER, IDEAL_NORM_GT_1, IMP_CONJ,
        IM_ADD, IM_CNJ, IM_CX, IN, INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING,
        INTEGRAL_DOMAIN_RING_OF_INTEGERS, IN_ELIM_THM, IN_EXTENSIONAL, IN_IMAGE,
        IN_INSERT, IN_SING, IN_UNIV, MEMBER_NOT_EMPTY, MONO_AND, MONO_EXISTS, MULT_SYM,
        NORM_CPRODUCT, NOT_FORALL_THM, NOT_IMP, .. } := D.core1
  let { NOT_IN_EMPTY, NSUM_ADD, NSUM_CLAUSES, NSUM_CONST, NSUM_EQ, NSUM_IMAGE_GEN,
        NSUM_RESTRICT_SET, NSUM_SING, NUMBER_FIELD_DEGREE_POS,
        NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD, NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS,
        NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_Q, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_NORM_HOMOMORPHISMS, NUMBER_FIELD_TRACE_HOMOMORPHISMS,
        PRODUCT_EQ_0, RE, REAL, REAL_CNJ, REAL_MUL_LZERO, REAL_OF_NUM_EQ,
        REAL_POW2_ABS, REAL_RING_CLAUSES, REAL_SUB_RZERO, RESTRICTION,
        RESTRICTION_COMPOSE_RIGHT, RESTRICTION_FIXPOINT, RESTRICTION_IN_EXTENSIONAL,
        RESTRICTION_UNIQUE, RESTRICTION_UNIQUE_ALT, RE_ADD, RE_CNJ, RE_CX, RE_NEG,
        RIGHT_FORALL_IMP_THM, RING_0, RING_1, RING_ADD,
        RING_CARRIER_SUBFIELD_GENERATED_SUBSET, RING_DET_EQ, RING_DET_HOMOMORPHISM,
        RING_DET_MUL, RING_DET_TRANSP, RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED,
        RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_CNJ, RING_HOMOMORPHISM_MUL,
        RING_HOMOMORPHISM_RING_OF_INT, RING_IDEAL_IDEAL_GENERATED,
        RING_MONOMORPHISM_ALT_EQ, RING_MUL, RING_NEG, RING_OF_INTEGERS,
        RING_OF_INTEGERS_FINITE_QUOTIENT, RING_OF_INTEGERS_FREE_BASIS_FIELD,
        RING_OF_INTEGERS_SUBSET, RING_OF_INTEGERS_UNIT_NONZERO, RING_UNIT_0,
        RING_UNIT_IN_CARRIER, SUBSET, SUBSET_ANTISYM, SUBSET_RESTRICT, SUBSET_UNIV,
        SUM_CONST, SUM_EQ, SUM_IMAGE_GEN, UNIT_GROUP, VSUM_EQ, VSUM_IMAGE,
        complex_embeddings, complex_mul, int_abs_th, int_of_num_th, o_DEF, o_THM, real,
        ring_homomorphism, ring_monomorphism, .. } := D.core2
  -- @@SCOPE END

  let real_embeddings ← new_definition
    r"real_embeddings (k:A ring) =
  {g | g IN complex_embeddings k /\ !x. x IN ring_carrier k ==> real(g x)}"

  let infinite_places ← new_definition
    r"infinite_places (k:A ring) =
  IMAGE (\g:A->complex. \x. norm(g x)) (complex_embeddings k)"

  let COMPLEX_EMBEDDINGS_CNJ ← prove
    r"!k (g:A->complex).
        g IN complex_embeddings k
        ==> RESTRICTION (ring_carrier k) (cnj o g) IN complex_embeddings k"
    (REWRITE_TAC [complex_embeddings, IN_ELIM_THM, RESTRICTION_IN_EXTENSIONAL] THEN REWRITE_TAC [ring_homomorphism, COMPLEX_RING_CLAUSES, SUBSET_UNIV] THEN SIMP_TAC [RESTRICTION, RING_0, RING_1, RING_NEG, RING_ADD, RING_MUL, o_THM, CNJ_ADD, CNJ_MUL, CNJ_NEG, CNJ_CX])

  let COMPLEX_EMBEDDINGS_CNJ_CNJ ← prove
    r"!k (g:A->complex).
        g IN complex_embeddings k
        ==> RESTRICTION (ring_carrier k)
              (cnj o RESTRICTION (ring_carrier k) (cnj o g)) = g"
    (REWRITE_TAC [RESTRICTION_COMPOSE_RIGHT, o_DEF, CNJ_CNJ, ETA_AX] THEN SIMP_TAC [RESTRICTION_FIXPOINT, complex_embeddings, IN_ELIM_THM])

  let REAL_EMBEDDINGS_CNJ ← prove
    r"!k (g:A->complex).
        g IN real_embeddings k <=>
        g IN complex_embeddings k /\
        RESTRICTION (ring_carrier k) (cnj o g) = g"
    (REPEAT GEN_TAC THEN REWRITE_TAC [real_embeddings, IN_ELIM_THM] THEN ASM_CASES_TAC (← q r"(g:A->complex) IN complex_embeddings k") THEN ASM_REWRITE_TAC [RESTRICTION_UNIQUE, o_THM, REAL_CNJ] THEN RULE_ASSUM_TAC (REWRITE_RULE [complex_embeddings, IN_ELIM_THM, IN]) THEN ASM_REWRITE_TAC [])

  let COMPLEX_EMBEDDINGS_NORM_POS ← prove
    r"!k (g:A->complex) x.
        field k /\ g IN complex_embeddings k /\ x IN ring_carrier k
        ==> (&0 < norm(g x) <=> ~(x = ring_0 k))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"g:A->complex")] COMPLEX_EMBEDDINGS_MONOMORPHISM) THEN ASM_SIMP_TAC [RING_MONOMORPHISM_ALT_EQ, COMPLEX_NORM_NZ, COMPLEX_RING_CLAUSES])

  let COMPLEX_EMBEDDINGS_NORM_MUL ← prove
    r"!k (g:A->complex) x y.
        g IN complex_embeddings k /\ x IN ring_carrier k /\ y IN ring_carrier k
        ==> norm(g(ring_mul k x y)) = norm(g x) * norm(g y)"
    (REWRITE_TAC [complex_embeddings, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"complex_ring"), (← q r"g:A->complex")] RING_HOMOMORPHISM_MUL) THEN ASM_SIMP_TAC [COMPLEX_RING_CLAUSES, COMPLEX_NORM_MUL])

  let COMPLEX_EMBEDDINGS_NORM_EQ ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"\t:real. t pow 2"
    let p2 ← prove r"!a b. norm a = norm b /\ norm(a + Cx(&1)) = norm(b + Cx(&1))
           ==> a = b \/ a = cnj b" (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN (MP_TAC o (AP_TERM q1))) THEN REWRITE_TAC [COMPLEX_SQNORM, RE_ADD, IM_ADD, RE_CX, IM_CX, COMPLEX_EQ, RE_CNJ, IM_CNJ] THEN CONV_TAC REAL_RING)
    let lemma1 := p2
    let p3 ← prove r"!a b c d:complex.
        ~(a = c) /\ (a = c \/ a = cnj c) /\ (b = d \/ b = cnj d) /\
        (a + b = c + d \/ a + b = cnj c + cnj d)
        ==> b = cnj d" (CONV_TAC COMPLEX_RING)
    let lemma2 := p3
    let q4 ← q r"(g:A->complex) x"
    let q5 ← q r"(h:A->complex) x"
    let q6 ← q r"y:A"
    let q7 ← q r"x:A"
    let q8 ← q r"p \/ q <=> ~p ==> q"
    let r9 ← TAUT q8
    let q10 ← q r"!x. x IN ring_carrier k ==> (h:A->complex) x = g x \/ h x = cnj(g x)"
    let q11 ← q r"((h:A->complex) = g <=> !x. x IN ring_carrier k ==> h x = g x) /\
    (h = RESTRICTION (ring_carrier k) (cnj o g) <=>
     !x. x IN ring_carrier k ==> h x = cnj(g x))"
    prove
      r"!k (g:A->complex) h.
          g IN complex_embeddings k /\ h IN complex_embeddings k
          ==> ((!x. x IN ring_carrier k ==> norm(h x) = norm(g x)) <=>
               h = g \/ h = RESTRICTION (ring_carrier k) (cnj o g))"
      (REPEAT GEN_TAC THEN REWRITE_TAC [complex_embeddings, IN_ELIM_THM] THEN REWRITE_TAC [ring_homomorphism, COMPLEX_RING_CLAUSES, SUBSET_UNIV] THEN STRIP_TAC THEN SUBGOAL_THEN q11 (CONJUNCTS_THEN SUBST1_TAC) THENL [REWRITE_TAC [RESTRICTION_UNIQUE_ALT, o_THM] THEN ASM_MESON_TAC [EXTENSIONAL_EQ, IN], ALL_TAC] THEN EQ_TAC THENL [DISCH_TAC, STRIP_TAC THEN ASM_SIMP_TAC [COMPLEX_NORM_CNJ]] THEN SUBGOAL_THEN q10 MP_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma1 THEN FIRST_X_ASSUM (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"ring_add k x (ring_1 k):A") th) THEN MP_TAC (← SPEC (← q r"x:A") th))) THEN ASM_SIMP_TAC [RING_ADD, RING_1], DISCH_TAC] THEN REWRITE_TAC [r9, NOT_FORALL_THM, NOT_IMP] THEN DISCH_THEN (X_CHOOSE_THEN q7 STRIP_ASSUME_TAC) THEN X_GEN_TAC q6 THEN DISCH_TAC THEN MATCH_MP_TAC lemma2 THEN MAP_EVERY EXISTS_TAC [q5, q4] THEN FIRST_X_ASSUM (fun th => tactic_of do pure (MAP_EVERY (MP_TAC o (← do let c := th; pure (fun th => SPEC th c))) [(← q r"x:A"), (← q r"y:A"), (← q r"ring_add k x y:A")])) THEN ASM_SIMP_TAC [RING_ADD, CNJ_ADD])

  let FINITE_INFINITE_PLACES ← prove
    r"!k:A ring. number_field k ==> FINITE(infinite_places k)"
    (SIMP_TAC [infinite_places, FINITE_IMAGE, FINITE_COMPLEX_EMBEDDINGS])

  let CARD_INFINITE_PLACES ← prove
    r"!k:A ring.
        number_field k
        ==> CARD(complex_embeddings k) + CARD(real_embeddings k) =
            2 * CARD(infinite_places k)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITE_COMPLEX_EMBEDDINGS)) THEN ABBREV_TAC (← q r"c = \g:A->complex. RESTRICTION (ring_carrier k) (cnj o g)") THEN SUBGOAL_THEN (← q r"!g:A->complex. g IN complex_embeddings k
                   ==> c g IN complex_embeddings k /\ c(c g) = g /\
                       !x. ~(x IN ring_carrier k) ==> g x = ARB") ASSUME_TAC THENL [EXPAND_TAC "c" THEN SIMP_TAC [COMPLEX_EMBEDDINGS_CNJ, COMPLEX_EMBEDDINGS_CNJ_CNJ] THEN SIMP_TAC [complex_embeddings, IN_ELIM_THM, IN_EXTENSIONAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"CARD(complex_embeddings k) + CARD(real_embeddings k) =
    nsum (complex_embeddings k) (\g:A->complex. if c g = g then 2 else 1)") SUBST1_TAC THENL [SUBGOAL_THEN (← q r"real_embeddings k = {g:A->complex | g IN complex_embeddings k /\ c g = g}") SUBST1_TAC THENL [EXPAND_TAC "c" THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM, REAL_EMBEDDINGS_CNJ], ASM_SIMP_TAC [CARD_EQ_NSUM, FINITE_RESTRICT, NSUM_RESTRICT_SET, (← GSYM NSUM_ADD)] THEN MATCH_MP_TAC NSUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC [] THEN COND_CASES_TAC THEN CONV_TAC NUM_REDUCE_CONV], ALL_TAC] THEN REWRITE_TAC [infinite_places] THEN FIRST_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC LAND_CONV [(← MATCH_MP (← ISPEC (← q r"\g:A->complex. \x. norm(g x)") NSUM_IMAGE_GEN) th)])) THEN ASM_SIMP_TAC [FINITE_IMAGE, (← ONCE_REWRITE_RULE [MULT_SYM] (← GSYM NSUM_CONST))] THEN MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC [FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"g:A->complex") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"{h | h IN complex_embeddings k /\
         (\x. norm((h:A->complex) x)) = (\x. norm(g x))} = {g, c g}") SUBST1_TAC THENL [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_INSERT, NOT_IN_EMPTY] THEN X_GEN_TAC (← q r"h:A->complex") THEN ASM_CASES_TAC (← q r"(h:A->complex) IN complex_embeddings k") THENL [ALL_TAC, ASM_MESON_TAC []] THEN EXPAND_TAC "c" THEN ASM_SIMP_TAC [(← GSYM COMPLEX_EMBEDDINGS_NORM_EQ)] THEN REWRITE_TAC [FUN_EQ_THM] THEN EQ_TAC THEN SIMP_TAC [] THEN DISCH_TAC THEN X_GEN_TAC (← q r"x:A") THEN ASM_CASES_TAC (← q r"(x:A) IN ring_carrier k") THEN ASM_SIMP_TAC [], ASM_SIMP_TAC [NSUM_CLAUSES, FINITE_SING, IN_SING, NSUM_SING] THEN ASM_CASES_TAC (← q r"(c:(A->complex)->(A->complex)) g = g") THEN ASM_REWRITE_TAC [] THEN CONV_TAC NUM_REDUCE_CONV])

  let CARD_INFINITE_PLACES_EQ_1 ← prove
    r"!k:A ring.
        number_field k
        ==> (CARD(infinite_places k) = 1 <=>
             extension_degree (subfield_generated k {ring_0 k},k) I = 1 \/
             extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
             real_embeddings k = {})"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP CARD_INFINITE_PLACES)) THEN FIRST_ASSUM (MP_TAC o (MATCH_MP COMPLEX_EMBEDDINGS_HAS_SIZE)) THEN FIRST_ASSUM (MP_TAC o (MATCH_MP NUMBER_FIELD_DEGREE_POS)) THEN SUBGOAL_THEN (← q r"real_embeddings (k:A ring) SUBSET complex_embeddings k") ASSUME_TAC THENL [SIMP_TAC [real_embeddings, SUBSET_RESTRICT], ALL_TAC] THEN ABBREV_TAC (← q r"n = extension_degree (subfield_generated k {ring_0 k},k) (I:A->A)") THEN REWRITE_TAC [HAS_SIZE] THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"FINITE(real_embeddings(k:A ring))") ASSUME_TAC THENL [ASM_MESON_TAC [FINITE_SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"real_embeddings(k:A ring)"), (← q r"complex_embeddings(k:A ring)")] CARD_SUBSET) THEN ASM_SIMP_TAC [(← GSYM CARD_EQ_0)] THEN ASM_ARITH_TAC)

  let REAL_EMBEDDINGS_MONOMORPHISM ← prove
    r"!k (g:A->complex).
        field k /\ g IN real_embeddings k
        ==> ring_monomorphism(k,real_ring) (\x. Re(g x))"
    (REWRITE_TAC [real_embeddings, IN_ELIM_THM, real] THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"g:A->complex")] COMPLEX_EMBEDDINGS_MONOMORPHISM) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o CONJUNCT1) THEN REWRITE_TAC [ring_monomorphism, ring_homomorphism, COMPLEX_RING_CLAUSES, REAL_RING_CLAUSES, SUBSET, FORALL_IN_IMAGE, IN_UNIV, COMPLEX_EQ] THEN MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL [STRIP_TAC THEN ASM_SIMP_TAC [RE_CX, RE_NEG, RE_ADD, complex_mul, RE, REAL_MUL_LZERO, REAL_SUB_RZERO], ASM_MESON_TAC []])

  let COMPLEX_EMBEDDINGS_PRIME_SUBFIELD_REAL ← prove
    r"!k (g:A->complex) a.
        field k /\ g IN complex_embeddings k /\
        a IN ring_carrier(subfield_generated k {ring_0 k})
        ==> real(g a)"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [REAL_CNJ] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"g:A->complex")] COMPLEX_EMBEDDINGS_CNJ) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"g:A->complex"), (← q r"RESTRICTION (ring_carrier k) (cnj o (g:A->complex))"), (← q r"k:A ring"), (← q r"complex_ring"), (← q r"{ring_0 k:A}")] RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED) THEN RULE_ASSUM_TAC (REWRITE_RULE [complex_embeddings, IN_ELIM_THM]) THEN ASM_REWRITE_TAC [IN_SING] THEN ANTS_TAC THENL [X_GEN_TAC (← q r"y:A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [RESTRICTION, o_THM] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"complex_ring"), (← q r"g:A->complex")] RING_HOMOMORPHISM_0) THEN ASM_REWRITE_TAC [COMPLEX_RING_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [CNJ_CX], DISCH_THEN (MP_TAC o (SPEC (← q r"a:A"))) THEN ASM_REWRITE_TAC [RESTRICTION, o_THM] THEN MESON_TAC []])

  let COMPLEX_EMBEDDINGS_NORM_FUN_EQ ← prove
    r"!k (g:A->complex) h.
        g IN complex_embeddings k /\ h IN complex_embeddings k
        ==> ((\x. norm(h x)) = (\x. norm(g x)) <=>
             h = g \/ h = RESTRICTION (ring_carrier k) (cnj o g))"
    (REPEAT STRIP_TAC THEN wPart rand (lhand o rand) (← GSYM COMPLEX_EMBEDDINGS_NORM_EQ) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN EQ_TAC THEN SIMP_TAC [] THEN DISCH_TAC THEN X_GEN_TAC (← q r"x:A") THEN ASM_CASES_TAC (← q r"(x:A) IN ring_carrier k") THEN ASM_SIMP_TAC [] THEN RULE_ASSUM_TAC (REWRITE_RULE [complex_embeddings, IN_ELIM_THM, EXTENSIONAL]) THEN ASM_SIMP_TAC [])

  let INFINITE_PLACE_EMBEDDINGS ← prove
    r"!k (g:A->complex).
        g IN complex_embeddings k
        ==> {h | h IN complex_embeddings k /\
                 (\x. norm(h x)) = (\x. norm(g x))} =
            {g, RESTRICTION (ring_carrier k) (cnj o g)}"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_INSERT, NOT_IN_EMPTY] THEN X_GEN_TAC (← q r"h:A->complex") THEN ASM_CASES_TAC (← q r"(h:A->complex) IN complex_embeddings k") THEN ASM_SIMP_TAC [COMPLEX_EMBEDDINGS_NORM_FUN_EQ] THEN ASM_MESON_TAC [COMPLEX_EMBEDDINGS_CNJ])

  let CARD_INFINITE_PLACE_EMBEDDINGS ← prove
    r"!k (g:A->complex).
        g IN complex_embeddings k
        ==> CARD {h | h IN complex_embeddings k /\
                      (\x. norm(h x)) = (\x. norm(g x))} =
            if g IN real_embeddings k then 1 else 2"
    (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [INFINITE_PLACE_EMBEDDINGS] THEN ASM_REWRITE_TAC [REAL_EMBEDDINGS_CNJ] THEN SIMP_TAC [CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY, IN_INSERT, NOT_IN_EMPTY] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC [])

  let INFINITE_PLACES_SUM ← prove
    r"!k (f:(A->real)->real).
        number_field k
        ==> sum (infinite_places k)
              (\v. &(CARD {g | g IN complex_embeddings k /\
                               (\x. norm(g x)) = v}) * f v) =
            sum (complex_embeddings k) (\g. f (\x. norm(g x)))"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITE_COMPLEX_EMBEDDINGS)) THEN MP_TAC (← ISPECL [(← q r"\g:A->complex. \x. norm(g x)"), (← q r"\g:A->complex. (f:(A->real)->real) (\x. norm(g x))"), (← q r"complex_embeddings(k:A ring)")] SUM_IMAGE_GEN) THEN ASM_REWRITE_TAC [(← GSYM infinite_places)] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC (← q r"v:A->real") THEN DISCH_TAC THEN REWRITE_TAC [] THEN CONV_TAC SYM_CONV THEN TRANS_TAC EQ_TRANS (← q r"sum {g | g IN complex_embeddings k /\ (\x. norm(g x)) = v}
        (\g:A->complex. (f:(A->real)->real) v)") THEN CONJ_TAC THENL [MATCH_MP_TAC SUM_EQ THEN SIMP_TAC [IN_ELIM_THM], MATCH_MP_TAC SUM_CONST THEN MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC []])

  let INFINITE_PLACES_DEGREE ← prove
    r"!k v:A->real.
        number_field k /\ v IN infinite_places k
        ==> 1 <= CARD {g | g IN complex_embeddings k /\
                           (\x. norm(g x)) = v} /\
            CARD {g | g IN complex_embeddings k /\
                      (\x. norm(g x)) = v} <= 2"
    (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, infinite_places] THEN REWRITE_TAC [FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [CARD_INFINITE_PLACE_EMBEDDINGS] THEN COND_CASES_TAC THEN CONV_TAC NUM_REDUCE_CONV)

  let INFINITE_PLACES_POS ← prove
    r"!k (v:A->real) x.
        field k /\ v IN infinite_places k /\
        x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> &0 < v x"
    (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, infinite_places] THEN REWRITE_TAC [FORALL_IN_IMAGE] THEN SIMP_TAC [COMPLEX_EMBEDDINGS_NORM_POS])

  let INFINITE_PLACES_MUL ← prove
    r"!k (v:A->real) x y.
        v IN infinite_places k /\ x IN ring_carrier k /\ y IN ring_carrier k
        ==> v(ring_mul k x y) = v x * v y"
    (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, infinite_places] THEN REWRITE_TAC [FORALL_IN_IMAGE] THEN SIMP_TAC [COMPLEX_EMBEDDINGS_NORM_MUL])

  let INFINITE_PLACES_ROOT_OF_UNITY ← prove
    r"!k (v:A->real) x n.
        v IN infinite_places k /\ x IN ring_carrier k /\
        1 <= n /\ ring_pow k x n = ring_1 k
        ==> v x = &1"
    (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, infinite_places] THEN REWRITE_TAC [FORALL_IN_IMAGE] THEN MESON_TAC [COMPLEX_EMBEDDINGS_ROOT_OF_UNITY])

  let INFINITE_PLACES_UNIT_GROUP ← prove
    r"!k v:A->real.
        number_field k /\ v IN infinite_places k
        ==> (!x. x IN group_carrier(unit_group(ring_of_integers k))
                 ==> &0 < v x) /\
            (!x y. x IN group_carrier(unit_group(ring_of_integers k)) /\
                   y IN group_carrier(unit_group(ring_of_integers k))
                   ==> v(group_mul (unit_group(ring_of_integers k)) x y) =
                       v x * v y)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN REWRITE_TAC [UNIT_GROUP, IN_ELIM_THM, RING_OF_INTEGERS] THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL [MATCH_MP_TAC INFINITE_PLACES_POS, MATCH_MP_TAC INFINITE_PLACES_MUL] THEN ASM_MESON_TAC [RING_OF_INTEGERS_UNIT_NONZERO])

  let (NUMBER_FIELD_TRACE_COMPLEX_EMBEDDINGS, NUMBER_FIELD_NORM_COMPLEX_EMBEDDINGS) ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let v1 ← GSYM COMPLEX_RING_PRODUCT
    let v2 ← GSYM COMPLEX_RING_SUM
    let q3 ← q r"(p ==> q) /\ (p ==> r) <=> p ==> q /\ r"
    let r4 ← TAUT q3
    let p5 ← prove r"(!k (g:A->complex) x.
        number_field k /\ g IN complex_embeddings k /\ x IN ring_carrier k
        ==> g(algebra_trace (subfield_generated k {ring_0 k},k) I x) =
            vsum (complex_embeddings k) (\h. h x)) /\
   (!k (g:A->complex) x.
        number_field k /\ g IN complex_embeddings k /\ x IN ring_carrier k
        ==> g(algebra_norm (subfield_generated k {ring_0 k},k) I x) =
            cproduct (complex_embeddings k) (\h. h x))" (REWRITE_TAC [AND_FORALL_THM, r4] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [v2, v1, FINITE_COMPLEX_EMBEDDINGS] THEN CONJ_TAC THENL [MATCH_MP_TAC NUMBER_FIELD_TRACE_HOMOMORPHISMS, MATCH_MP_TAC NUMBER_FIELD_NORM_HOMOMORPHISMS] THEN RULE_ASSUM_TAC (REWRITE_RULE [complex_embeddings, IN_ELIM_THM]) THEN ASM_SIMP_TAC [FIELD_COMPLEX_RING, COMPLEX_EMBEDDINGS_HAS_SIZE, SUBSET, complex_embeddings, IN_ELIM_THM])
    CONJ_PAIR p5

  let NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS ← prove
    r"!k x:A.
        number_field k /\ x IN ring_carrier(ring_of_integers k) /\
        ~(x = ring_0 k)
        ==> &(ideal_norm (ring_of_integers k)
                (ideal_generated (ring_of_integers k) {x})) =
            product (complex_embeddings k) (\g. norm(g x))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A")] NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_Q) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"m:int") (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o (AP_TERM (← q r"real_of_int"))))) THEN REWRITE_TAC [int_of_num_th, int_abs_th] THEN DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ((X_CHOOSE_TAC (← q r"g:A->complex")) o ((REWRITE_RULE [(← GSYM MEMBER_NOT_EMPTY)]) o (MATCH_MP COMPLEX_EMBEDDINGS_NONEMPTY))) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (REWRITE_RULE [complex_embeddings, IN_ELIM_THM]))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"g:A->complex"), (← q r"x:A")] NUMBER_FIELD_NORM_COMPLEX_EMBEDDINGS) THEN ASM_SIMP_TAC [(← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET), (← MATCH_MP RING_HOMOMORPHISM_RING_OF_INT (← ASSUME (← q r"ring_homomorphism(k,complex_ring) (g:A->complex)")))] THEN DISCH_THEN (MP_TAC o (AP_TERM (← q r"norm:complex->real"))) THEN ASM_SIMP_TAC [NORM_CPRODUCT, FINITE_COMPLEX_EMBEDDINGS, COMPLEX_RING_OF_INT, COMPLEX_NORM_CX])

  let RING_OF_INTEGERS_UNIT_NORM_PRODUCT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"1 < n ==> ~(n = 1)")
    let r2 ← REAL_ARITH (← q r"x:real = &0 ==> ~(x = &1)")
    let r3 ← TAUT (← q r"~p /\ ~q ==> (p <=> q)")
    prove
      r"!k x:A.
          number_field k
          ==> (ring_unit (ring_of_integers k) x <=>
               x IN ring_carrier(ring_of_integers k) /\
               product (complex_embeddings k) (\g. norm(g x)) = &1)"
      (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"(x:A) IN ring_carrier(ring_of_integers k)") THENL [ASM_REWRITE_TAC [], ASM_MESON_TAC [RING_UNIT_IN_CARRIER]] THEN ASM_CASES_TAC (← q r"x:A = ring_0 k") THENL [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r3 THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_UNIT_0, RING_OF_INTEGERS, NUMBER_FIELD_IMP_FIELD, INTEGRAL_DOMAIN_RING_OF_INTEGERS, INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING], MATCH_MP_TAC r2 THEN ASM_SIMP_TAC [PRODUCT_EQ_0, FINITE_COMPLEX_EMBEDDINGS] THEN FIRST_ASSUM (MP_TAC o ((REWRITE_RULE [(← GSYM MEMBER_NOT_EMPTY)]) o (MATCH_MP COMPLEX_EMBEDDINGS_NONEMPTY))) THEN MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC [complex_embeddings, IN_ELIM_THM, COMPLEX_NORM_ZERO] THEN MESON_TAC [RING_HOMOMORPHISM_0, COMPLEX_RING_CLAUSES]], ALL_TAC] THEN ASM_SIMP_TAC [(← GSYM NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS), REAL_OF_NUM_EQ, (← GSYM IDEAL_GENERATED_SING_EQ_CARRIER)] THEN EQ_TAC THEN SIMP_TAC [IDEAL_NORM_CARRIER] THEN ONCE_REWRITE_TAC [(← GSYM CONTRAPOS_THM)] THEN DISCH_TAC THEN MATCH_MP_TAC r1 THEN MATCH_MP_TAC IDEAL_NORM_GT_1 THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED] THEN MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN DISCH_THEN (MP_TAC o (AP_TERM (← q r"\s:A->bool. (x:A) IN s"))) THEN ASM_SIMP_TAC [IDEAL_GENERATED_INC_GEN, IN_SING])

  let NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS ← prove
    r"!k n w (e:num->A->complex).
        number_field k /\
        free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w /\
        (!i. i < n ==> e i IN complex_embeddings k) /\
        (!i j. i < n /\ j < n /\ e i = e j ==> i = j)
        ==> ring_det complex_ring {i | i < n} (\i j. e i (w j)) pow 2 =
            Cx(real_of_int(number_field_discriminant k))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE [complex_embeddings, IN_ELIM_THM]) THEN FIRST_ASSUM ((X_CHOOSE_THEN (← q r"g:A->complex") (STRIP_ASSUME_TAC o (REWRITE_RULE [complex_embeddings, IN_ELIM_THM]))) o ((REWRITE_RULE [(← GSYM MEMBER_NOT_EMPTY)]) o (MATCH_MP COMPLEX_EMBEDDINGS_NONEMPTY))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A")] RING_OF_INTEGERS_FREE_BASIS_FIELD) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A")] NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (AP_TERM (← q r"g:A->complex"))) THEN REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_RING_OF_INT (← ASSUME (← q r"ring_homomorphism(k,complex_ring) (g:A->complex)"))), COMPLEX_RING_OF_INT] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [(← GSYM COMPLEX_RING_POW)] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS THEN ASM_REWRITE_TAC [FIELD_COMPLEX_RING] THEN CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"i:num"), (← q r"j:num")] THEN STRIP_TAC THEN FIRST_X_ASSUM (MATCH_MP_TAC o ((checkM (fun z6 => (do let z7 ← (do pure (Prod.snd (← (do let z8 ← (do let z9 ← (pure z6); pure (concl z9)); pure (strip_forall z8))))); pure (is_imp z7)))) o (checkM (fun th => (do let z5 ← (q r"i:num = j"); let z4 ← (do let z1 ← (do pure (Prod.snd (← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); pure (strip_forall z2))))); liftExcept (rand z1)); pure (z4 == z5)))))) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC EXTENSIONAL_EQ THEN EXISTS_TAC (← q r"ring_carrier k:A->bool") THEN ASM_SIMP_TAC [])

  let COMPLEX_EMBEDDINGS_VSUM_CNJ_REAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"q /\ (q ==> p) ==> p /\ q")
    prove
      r"!k (a:A) (b:A).
          number_field k /\ a IN ring_carrier k /\ b IN ring_carrier k
          ==> real(vsum (complex_embeddings k) (\g. cnj(g a) * g b))"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"FINITE(complex_embeddings (k:A ring))") ASSUME_TAC THENL [ASM_MESON_TAC [COMPLEX_EMBEDDINGS_HAS_SIZE, HAS_SIZE], ALL_TAC] THEN REWRITE_TAC [REAL_CNJ] THEN ASM_SIMP_TAC [CNJ_VSUM] THEN REWRITE_TAC [CNJ_MUL, CNJ_CNJ] THEN ABBREV_TAC (← q r"cj = \g:A->complex. RESTRICTION (ring_carrier k) (cnj o g)") THEN SUBGOAL_THEN (← q r"IMAGE (cj:(A->complex)->(A->complex)) (complex_embeddings k) =
      complex_embeddings k /\
      (!g. g IN complex_embeddings k ==> cj(cj g) = g)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "cj" THEN REWRITE_TAC [] THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [REWRITE_TAC [COMPLEX_EMBEDDINGS_CNJ_CNJ], DISCH_TAC] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, COMPLEX_EMBEDDINGS_CNJ] THEN X_GEN_TAC (← q r"g:A->complex") THEN DISCH_TAC THEN REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC (← q r"RESTRICTION (ring_carrier k) (cnj o (g:A->complex))") THEN ASM_SIMP_TAC [COMPLEX_EMBEDDINGS_CNJ], ALL_TAC] THEN FIRST_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [(← SYM th)])) THEN wPart rand (lhand o rand) VSUM_IMAGE THEN ANTS_TAC THENL [ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC (← q r"g:A->complex") THEN DISCH_TAC THEN EXPAND_TAC "cj" THEN ASM_REWRITE_TAC [o_THM, RESTRICTION, CNJ_CNJ] THEN REWRITE_TAC [COMPLEX_MUL_SYM])

  let NUMBER_FIELD_EMBEDDING_GRAM_DET ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let p1 ← prove r"ring_homomorphism(real_ring,complex_ring) Cx" (REWRITE_TAC [ring_homomorphism, COMPLEX_RING_CLAUSES, REAL_RING_CLAUSES, SUBSET_UNIV, IN_UNIV, CX_ADD, CX_MUL, CX_NEG])
    let cx_hom := p1
    let q2 ← q r"norm:complex->real"
    let q3 ← q r"e:num->A->complex"
    let q4 ← q r"w:num->A"
    let q5 ← q r"n:num"
    let q6 ← q r"k:A ring"
    let v7 ← ISPECL [q6, q5, q4, q3] NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS
    let v16 ← GSYM CX_POW
    let q17 ← q r"\l j. (e:num->A->complex) l ((w:num->A) j)"
    let q18 ← q r"{i:num | i < n}"
    let q19 ← q r"complex_ring"
    let v20 ← ISPECL [q19, q18, q17] RING_DET_TRANSP
    let q21 ← q r"\i l. (e:num->A->complex) l ((w:num->A) i)"
    let q22 ← q r"{i:num | i < n}"
    let q23 ← q r"cnj"
    let q24 ← q r"complex_ring"
    let q25 ← q r"complex_ring"
    let v26 ← ISPECL [q25, q24, q23, q22, q21] RING_DET_HOMOMORPHISM
    let q27 ← q r"\l j. (e:num->A->complex) l ((w:num->A) j)"
    let q28 ← q r"\i l. cnj((e:num->A->complex) l ((w:num->A) i))"
    let q29 ← q r"{i:num | i < n}"
    let q30 ← q r"complex_ring"
    let v31 ← ISPECL [q30, q29, q28, q27] RING_DET_MUL
    let q32 ← q r"ring_det complex_ring {i | i < n}
        (\i j. vsum {l | l < n}
                 (\l. cnj((e:num->A->complex) l (w i)) * e l
                  ((w:num->A) j)))"
    let q33 ← q r"\i j. Re(vsum {l | l < n}
                 (\l. cnj((e:num->A->complex) l (w i)) * e l ((w:num->A) j)))"
    let q34 ← q r"{i:num | i < n}"
    let q35 ← q r"Cx"
    let q36 ← q r"complex_ring"
    let q37 ← q r"real_ring"
    let v38 ← ISPECL [q37, q36, q35, q34, q33] RING_DET_HOMOMORPHISM
    let q39 ← q r"Cx(ring_det real_ring {i | i < n}
        (\i j. Re(vsum {l | l < n}
                 (\l. cnj((e:num->A->complex) l (w i)) * e l (w j))))) =
    cnj(ring_det complex_ring {i | i < n} (\l j. e l ((w:num->A) j))) *
    ring_det complex_ring {i | i < n} (\l j. e l (w j))"
    let q40 ← q r"vsum {l | l < n} (\l. cnj((e:num->A->complex) l (w i)) * e l (w j)) =
      vsum (complex_embeddings k) (\g. cnj(g((w:num->A) i)) * g(w j))"
    let v41 ← GSYM REAL
    let q42 ← q r"!i j. i < n /\ j < n
          ==> Cx(Re(vsum {l | l < n}
                     (\l. cnj((e:num->A->complex) l (w i)) * e l (w j)))) =
              vsum {l | l < n} (\l. cnj(e l (w i)) * e l (w j))"
    let q46 ← q r"!i. i < n ==> (w:num->A) i IN ring_carrier k"
    let q47 ← q r"k:A ring"
    let v48 ← ISPEC q47 COMPLEX_EMBEDDINGS_HAS_SIZE
    let q49 ← q r"IMAGE (e:num->A->complex) {i | i < n} = complex_embeddings k"
    let q50 ← q r"n = extension_degree (subfield_generated k {ring_0 k},k:A ring) I"
    prove
      r"!k n (w:num->A) (e:num->A->complex).
          number_field k /\
          free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w /\
          n = extension_degree (subfield_generated k {ring_0 k},k) I /\
          (!i. i < n ==> e i IN complex_embeddings k) /\
          (!i j. i < n /\ j < n /\ e i = e j ==> i = j)
          ==> ring_det real_ring {i | i < n}
                (\i j. Re(vsum {l | l < n} (\l. cnj(e l (w i)) * e l (w j))))
              pow 2 =
              real_of_int(number_field_discriminant k) pow 2"
      (REPEAT STRIP_TAC THEN UNDISCH_TAC q50 THEN DISCH_THEN (ASSUME_TAC o SYM) THEN SUBGOAL_THEN q49 ASSUME_TAC THENL [MP_TAC v48 THEN ASM_REWRITE_TAC [HAS_SIZE] THEN STRIP_TAC THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN ASM_MESON_TAC [], wPart lhand (lhand o rand) CARD_IMAGE_INJ THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, CARD_NUMSEG_LT] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN q46 ASSUME_TAC THENL [FIRST_X_ASSUM (MP_TAC o ((MATCH_MP FREE_BASIS_IN_CARRIER) o (checkM (fun th => (do let z44 ← (do let z45 ← (pure th); pure (concl z45)); let z43 ← (q r"w:num->A"); pure (free_in z43 z44)))))) THEN MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN q42 ASSUME_TAC THENL [REPEAT STRIP_TAC THEN REWRITE_TAC [v41] THEN SUBGOAL_THEN q40 SUBST1_TAC THENL [FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← SYM th)])) THEN wPart rand (lhand o rand) VSUM_IMAGE THEN ANTS_TAC THENL [REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [o_DEF]], MATCH_MP_TAC COMPLEX_EMBEDDINGS_VSUM_CNJ_REAL THEN ASM_SIMP_TAC []], ALL_TAC] THEN SUBGOAL_THEN q39 ASSUME_TAC THENL [MP_TAC v38 THEN REWRITE_TAC [cx_hom, FINITE_NUMSEG_LT, REAL_RING_CLAUSES, IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN TRANS_TAC EQ_TRANS q32 THEN CONJ_TAC THENL [MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC v31 THEN REWRITE_TAC [COMPLEX_RING_CLAUSES, IN_UNIV, FINITE_NUMSEG_LT] THEN ASM_SIMP_TAC [COMPLEX_RING_SUM, FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN MP_TAC v26 THEN REWRITE_TAC [RING_HOMOMORPHISM_CNJ, FINITE_NUMSEG_LT, COMPLEX_RING_CLAUSES, IN_UNIV] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN MP_TAC v20 THEN REWRITE_TAC [FINITE_NUMSEG_LT], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o ((REWRITE_RULE [COMPLEX_MUL_CNJ, v16, CX_INJ]) o (checkM (fun th => (do if ← (do if ← (do let z9 ← (do let z10 ← (pure th); pure (concl z10)); let z8 ← (q r"cnj"); pure (free_in z8 z9)) then (do let z11 ← (do let z12 ← (pure th); pure (concl z12)); pure (is_eq z11)) else pure false) then (do let z13 ← (do let z14 ← (do let z15 ← (pure th); pure (concl z15)); liftExcept (lhs z14)); pure (is_comb z13)) else pure false))))) THEN DISCH_THEN SUBST1_TAC THEN MP_TAC v7 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (AP_TERM q2)) THEN REWRITE_TAC [COMPLEX_NORM_POW, COMPLEX_NORM_CX] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [REAL_POW2_ABS])

  -- @@RETURN BEGIN
  return { real_embeddings, infinite_places, COMPLEX_EMBEDDINGS_CNJ,
           COMPLEX_EMBEDDINGS_CNJ_CNJ, REAL_EMBEDDINGS_CNJ, COMPLEX_EMBEDDINGS_NORM_POS,
           COMPLEX_EMBEDDINGS_NORM_MUL, COMPLEX_EMBEDDINGS_NORM_EQ,
           FINITE_INFINITE_PLACES, CARD_INFINITE_PLACES, CARD_INFINITE_PLACES_EQ_1,
           REAL_EMBEDDINGS_MONOMORPHISM, COMPLEX_EMBEDDINGS_PRIME_SUBFIELD_REAL,
           COMPLEX_EMBEDDINGS_NORM_FUN_EQ, INFINITE_PLACE_EMBEDDINGS,
           CARD_INFINITE_PLACE_EMBEDDINGS, INFINITE_PLACES_SUM, INFINITE_PLACES_DEGREE,
           INFINITE_PLACES_POS, INFINITE_PLACES_MUL, INFINITE_PLACES_ROOT_OF_UNITY,
           INFINITE_PLACES_UNIT_GROUP, NUMBER_FIELD_TRACE_COMPLEX_EMBEDDINGS,
           NUMBER_FIELD_NORM_COMPLEX_EMBEDDINGS,
           NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS,
           RING_OF_INTEGERS_UNIT_NORM_PRODUCT, NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS,
           COMPLEX_EMBEDDINGS_VSUM_CNJ_REAL, NUMBER_FIELD_EMBEDDING_GRAM_DET }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- infinite_places.ml phrases from line 722 to 722                        -/
/- ---------------------------------------------------------------------- -/

structure InfinitePlaces02 where
  -- @@FIELDS
  NUMBER_FIELD_DISCRIMINANT_SIGN : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupInfinitePlaces02 [HolBase] (D : InfinitePlacesDeps) (BInfinitePlaces01 : InfinitePlaces01) :
    ExceptT String IO InfinitePlaces02 := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_MESON_TAC, COMPLEX_RING, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, .. } := D
  let { ARITH_EQ, CARD_DIFF, COMPLEX_EMBEDDINGS_HAS_SIZE, COMPLEX_EQ, COMPLEX_MUL_LID,
        COMPLEX_MUL_LNEG, COMPLEX_POW_2, COMPLEX_RING_CLAUSES, CX_INJ, DIV_MULT,
        EXISTS_UNIQUE_THM, EXTENSION, FINITE_COMPLEX_EMBEDDINGS, FINITE_NUMSEG_LT,
        FORALL_IN_IMAGE, FREE_BASIS_IN_CARRIER, HAS_SIZE_INDEX, IM, IM_CNJ, IM_CX,
        IM_NEG, INJECTIVE_ON_LEFT_INVERSE, IN_DIFF, IN_ELIM_THM, IN_IMAGE, IN_UNIV, .. } := D.core1
  let { NUMBER_FIELD_DISCRIMINANT_NONZERO, PERMUTES_INVOLUTION, RE, REAL_LE_SQUARE,
        REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_POW_NEG, REAL_POW_ONE, RESTRICTION,
        RE_CNJ, RE_CX, RE_NEG, RING_DET_EQ, RING_DET_HOMOMORPHISM,
        RING_DET_PERMUTE_ROWS, RING_DET_REINDEX, RING_HOMOMORPHISM_CNJ,
        RING_OF_INTEGERS_FREE, RING_OF_INTEGERS_SUBSET, SIGN_INVOLUTION, SUBSET,
        SUBSET_RESTRICT, complex_mul, int_eq, int_lt, int_of_num_th, o_THM, ring_sign,
        sign, .. } := D.core2
  let { CARD_INFINITE_PLACES, COMPLEX_EMBEDDINGS_CNJ, COMPLEX_EMBEDDINGS_CNJ_CNJ,
        NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS, REAL_EMBEDDINGS_CNJ, real_embeddings, .. } := BInfinitePlaces01
  -- @@SCOPE END

  let NUMBER_FIELD_DISCRIMINANT_SIGN ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"Re z = &0"
    let q2 ← q r"Im z = &0"
    let q3 ← q r"Im z"
    let v4 ← SPEC q3 REAL_LE_SQUARE
    let q5 ← q r"Re z"
    let v6 ← SPEC q5 REAL_LE_SQUARE
    let q7 ← q r"x:real = --x <=> x = &0"
    let r8 ← REAL_ARITH q7
    let q9 ← q r"--x:real = x <=> x = &0"
    let r10 ← REAL_ARITH q9
    let p11 ← prove r"!z r. z pow 2 = Cx r /\ ~(r = &0) /\ (cnj z = z \/ cnj z = --z)
           ==> (&0 < r <=> cnj z = z)" (REPEAT GEN_TAC THEN REWRITE_TAC [COMPLEX_EQ, COMPLEX_POW_2, RE_CNJ, IM_CNJ, RE_NEG, IM_NEG, complex_mul, RE, IM, RE_CX, IM_CX, r10, r8] THEN MP_TAC v6 THEN MP_TAC v4 THEN MAP_EVERY ASM_CASES_TAC [q2, q1] THEN ASM_REWRITE_TAC [REAL_MUL_LZERO, REAL_MUL_RZERO] THEN REAL_ARITH_TAC)
    let lemma1 := p11
    let p12 ← prove r"!(p:B->B) s.
        FINITE s /\ (!x. p(p x) = x) /\ (!x. ~(x IN s) ==> p x = x)
        ==> (evenperm p <=> EVEN(CARD {x | ~(p x = x)} DIV 2))" (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o (MATCH_MP SIGN_INVOLUTION)) THEN REWRITE_TAC [sign, REAL_POW_NEG, REAL_POW_ONE] THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC)
    let lemma2 := p12
    let q13 ← q r"e:num->A->complex"
    let q14 ← q r"w:num->A"
    let q15 ← q r"n:num"
    let q16 ← q r"k:A ring"
    let v17 ← ISPECL [q16, q15, q14, q13] NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS
    let q18 ← q r"w:num->A"
    let q19 ← q r"n:num"
    let q20 ← q r"ring_of_integers k:A ring"
    let q21 ← q r"integer_ring"
    let q22 ← q r"ring_of_int k:int->A"
    let v23 ← ISPECL [q22, q21, q20, q19, q18] FREE_BASIS_IN_CARRIER
    let q24 ← q r"!i j. i IN {i | i < n} /\ j IN {i | i < n} /\
            (e:num->A->complex) i = e j ==> i = j"
    let q25 ← q r"\(h:A->complex) (h':A->complex).
         h(((w:num->A) o (f:(A->complex)->num)) h')"
    let q26 ← q r"{i:num | i < n}"
    let q27 ← q r"e:num->A->complex"
    let q28 ← q r"complex_ring"
    let v29 ← ISPECL [q28, q27, q26, q25] RING_DET_REINDEX
    let q30 ← q r"(w:num->A) o (f:(A->complex)->num)"
    let q31 ← q r"f:(A->complex)->num"
    let q32 ← q r"{i:num | i < n}"
    let q33 ← q r"e:num->A->complex"
    let v34 ← ISPECL [q33, q32] INJECTIVE_ON_LEFT_INVERSE
    let q35 ← q r"!x. x IN complex_embeddings k
            ==> (?m. m < n /\ (e:num->A->complex) m = x) /\
                (!m m'. (m < n /\ e m = x) /\ m' < n /\ e m' = x ==> m = m')"
    let q36 ← q r"(!i j. i IN {i | i < n} /\ j IN {i | i < n} /\
             (e:num->A->complex) i = e j ==> i = j) /\
      complex_embeddings k = IMAGE e {i | i < n}"
    let q37 ← q r"e:num->A->complex"
    let q38 ← q r"n = extension_degree (subfield_generated k {ring_0 k},k) (I:A->A)"
    let q39 ← q r"w:num->A"
    let p40 ← prove r"!k:A ring.
        number_field k
        ==> ?v. (!h. h IN complex_embeddings k ==> v h IN ring_carrier k) /\
                ring_det complex_ring (complex_embeddings k)
                  (\(h:A->complex) (h':A->complex). h(v h')) pow 2 =
                Cx(real_of_int(number_field_discriminant k))" (REPEAT STRIP_TAC THEN FIRST_ASSUM ((X_CHOOSE_TAC q39) o (MATCH_MP RING_OF_INTEGERS_FREE)) THEN FIRST_ASSUM (MP_TAC o ((MATCH_MP HAS_SIZE_INDEX) o (MATCH_MP COMPLEX_EMBEDDINGS_HAS_SIZE))) THEN ABBREV_TAC q38 THEN REWRITE_TAC [EXISTS_UNIQUE_THM] THEN DISCH_THEN (X_CHOOSE_THEN q37 STRIP_ASSUME_TAC) THEN SUBGOAL_THEN q36 MP_TAC THENL [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN ASM_MESON_TAC [], UNDISCH_THEN q35 (fun (_ : thm) => ALL_TAC) THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)] THEN MP_TAC v34 THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN DISCH_THEN (X_CHOOSE_TAC q31) THEN EXISTS_TAC q30 THEN MP_TAC v29 THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN UNDISCH_THEN q24 (fun (_ : thm) => ALL_TAC) THEN REWRITE_TAC [FORALL_IN_IMAGE, IN_ELIM_THM, o_THM] THEN CONJ_TAC THENL [MP_TAC v23 THEN ASM_SIMP_TAC [] THEN MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], MP_TAC v17 THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [ASM_MESON_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC RING_DET_EQ THEN ASM_SIMP_TAC [IN_ELIM_THM]])
    let lemma3 := p40
    let v41 ← GSYM CX_INJ
    let q42 ← q r"z pow 2 = Cx(real_of_int(number_field_discriminant(k:A ring)))"
    let q43 ← q r"~(real_of_int(number_field_discriminant(k:A ring)) = &0)"
    let q44 ← q r"evenperm(c:(A->complex)->(A->complex))"
    let q45 ← q r"real_of_int(number_field_discriminant(k:A ring))"
    let q46 ← q r"z:complex"
    let v47 ← ISPECL [q46, q45] lemma1
    let q48 ← q r"k:A ring"
    let v49 ← ISPEC q48 NUMBER_FIELD_DISCRIMINANT_NONZERO
    let q50 ← q r"CARD(complex_embeddings k) + CARD(real_embeddings(k:A ring)) =
        2 * CARD(infinite_places k)"
    let q51 ← q r"CARD(complex_embeddings k) - CARD(real_embeddings(k:A ring)) =
      2 * (CARD(infinite_places k) - CARD(real_embeddings k))"
    let q52 ← q r"(CARD(complex_embeddings k) - CARD(real_embeddings(k:A ring))) DIV 2 =
    CARD(infinite_places k) - CARD(real_embeddings k)"
    let q53 ← q r"real_embeddings k SUBSET complex_embeddings(k:A ring)"
    let q54 ← q r"{h | ~((c:(A->complex)->(A->complex)) h = h)} =
    complex_embeddings k DIFF real_embeddings k"
    let q55 ← q r"complex_embeddings(k:A ring)"
    let q56 ← q r"c:(A->complex)->(A->complex)"
    let v57 ← ISPECL [q56, q55] lemma2
    let q58 ← q r"c:(A->complex)->(A->complex)"
    let q59 ← q r"\(h:A->complex) (h':A->complex). h((v:(A->complex)->A) h')"
    let q60 ← q r"complex_embeddings(k:A ring)"
    let q61 ← q r"complex_ring"
    let v62 ← ISPECL [q61, q60, q59, q58] RING_DET_PERMUTE_ROWS
    let q63 ← q r"\(h:A->complex) (h':A->complex). h((v:(A->complex)->A) h')"
    let q64 ← q r"complex_embeddings(k:A ring)"
    let q65 ← q r"cnj"
    let q66 ← q r"complex_ring"
    let q67 ← q r"complex_ring"
    let v68 ← ISPECL [q67, q66, q65, q64, q63] RING_DET_HOMOMORPHISM
    let q69 ← q r"ring_det complex_ring (complex_embeddings k)
        (\(h:A->complex) (h':A->complex). h((v:(A->complex)->A) h')) = z"
    let q70 ← q r"cnj z = ring_sign complex_ring (c:(A->complex)->(A->complex)) * z"
    let q71 ← q r"(h:A->complex) IN complex_embeddings k"
    let q72 ← q r"h:A->complex"
    let q73 ← q r"(!h. (c:(A->complex)->(A->complex))(c h) = h) /\
    (!h. ~(h IN complex_embeddings k) ==> c h = h)"
    let q74 ← q r"c = \h:A->complex. if h IN complex_embeddings k
                       then RESTRICTION (ring_carrier k) (cnj o h) else h"
    let q75 ← q r"z = ring_det complex_ring (complex_embeddings k)
          (\(h:A->complex) (h':A->complex). h((v:(A->complex)->A) h'))"
    let q76 ← q r"v:(A->complex)->A"
    prove
      r"!k:A ring.
          number_field k
          ==> (&0 < number_field_discriminant k <=>
               EVEN(CARD(infinite_places k) - CARD(real_embeddings k)))"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITE_COMPLEX_EMBEDDINGS)) THEN FIRST_ASSUM (MP_TAC o (MATCH_MP CARD_INFINITE_PLACES)) THEN FIRST_ASSUM ((X_CHOOSE_THEN q76 STRIP_ASSUME_TAC) o (MATCH_MP lemma3)) THEN ABBREV_TAC q75 THEN DISCH_TAC THEN ABBREV_TAC q74 THEN SUBGOAL_THEN q73 STRIP_ASSUME_TAC THENL [EXPAND_TAC "c" THEN SIMP_TAC [] THEN X_GEN_TAC q72 THEN ASM_CASES_TAC q71 THEN ASM_SIMP_TAC [COMPLEX_EMBEDDINGS_CNJ, COMPLEX_EMBEDDINGS_CNJ_CNJ], ALL_TAC] THEN SUBGOAL_THEN q70 MP_TAC THENL [UNDISCH_THEN q69 (SUBST1_TAC o SYM) THEN MP_TAC v68 THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_CNJ, COMPLEX_RING_CLAUSES, IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC v62 THEN ASM_SIMP_TAC [PERMUTES_INVOLUTION, COMPLEX_RING_CLAUSES] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_DET_EQ THEN EXPAND_TAC "c" THEN ASM_SIMP_TAC [RESTRICTION, o_THM], REWRITE_TAC [ring_sign, COMPLEX_RING_CLAUSES] THEN DISCH_TAC] THEN MP_TAC v57 THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN q54 SUBST1_TAC THENL [EXPAND_TAC "c" THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_DIFF, REAL_EMBEDDINGS_CNJ] THEN GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN q53 ASSUME_TAC THENL [REWRITE_TAC [real_embeddings, SUBSET_RESTRICT], ALL_TAC] THEN ASM_SIMP_TAC [CARD_DIFF] THEN SUBGOAL_THEN q52 SUBST1_TAC THENL [SUBGOAL_THEN q51 SUBST1_TAC THENL [UNDISCH_TAC q50 THEN ARITH_TAC, SIMP_TAC [DIV_MULT, ARITH_EQ]], DISCH_THEN (SUBST1_TAC o SYM)] THEN REWRITE_TAC [int_lt, int_of_num_th] THEN MP_TAC v49 THEN ASM_REWRITE_TAC [int_eq, int_of_num_th] THEN DISCH_TAC THEN MP_TAC v47 THEN ASM_REWRITE_TAC [] THEN ASM_CASES_TAC q44 THEN ASM_REWRITE_TAC [COMPLEX_MUL_LID, COMPLEX_MUL_LNEG] THEN DISCH_THEN SUBST1_TAC THEN UNDISCH_TAC q43 THEN UNDISCH_TAC q42 THEN REWRITE_TAC [v41] THEN CONV_TAC COMPLEX_RING)

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_DISCRIMINANT_SIGN }
  -- @@RETURN END

end HolANT.InfinitePlaces
