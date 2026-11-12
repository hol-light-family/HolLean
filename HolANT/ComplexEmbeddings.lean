/- ========================================================================= -/
/- ANT: Embeddings of a number field into the complex numbers ...          -/
/- ========================================================================= -/
/- File: HolANT/ComplexEmbeddings.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/complex_embeddings.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antcomplexembeddingsdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/frag.ml, Library/grouptheory.ml, Library/products.ml, ANT/algmisc.ml, ANT/integral.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/classgroup.ml, ANT/nf_valuation.ml, ANT/prime_split.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/integrality.ml, Library/ring_groups.ml, ANT/fingen_group.ml, Multivariate/misc.ml, Multivariate/metric.ml, Multivariate/homology.ml, Multivariate/vectors.ml, Multivariate/determinants.ml, Multivariate/topology.ml, Multivariate/convex.ml, Multivariate/paths.ml, Multivariate/polytope.ml, Multivariate/degree.ml, Multivariate/derivatives.ml, Multivariate/integration.ml, Multivariate/measure.ml, Multivariate/complex_algebra.ml, Multivariate/complexes.ml, Multivariate/canal.ml, Multivariate/transcendentals.ml, Multivariate/realanalysis.ml, Multivariate/moretop.ml, Multivariate/cauchy.ml, Multivariate/complex_ring.ml, Multivariate/complex_field.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.ComplexEmbeddings fills them).

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
import HolLibrary.Products
import HolANT.Algmisc
import HolANT.Integral
import HolLibrary.Isum
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolANT.IdealArith
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.IdealNorm
import HolANT.RingOfIntegers
import HolANT.NormIndex
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.Classgroup
import HolANT.NfValuation
import HolANT.PrimeSplit
import HolANT.Discriminant
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
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.Classgroup
open HolANT.NfValuation
open HolANT.PrimeSplit
open HolANT.Discriminant
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.Integrality
open HolANT.FingenGroup

namespace HolANT.ComplexEmbeddings

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ABELIAN_UNIT_GROUP ADD1 ADD_EQ_0 ADD_SUB
   ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING
   ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM_ROOT ARITH_EQ COEFF_COMPOSE
   COMPLEX_ADD_LID COMPLEX_ADD_RID COMPLEX_MUL_ASSOC COMPLEX_MUL_LZERO
   COMPLEX_MUL_RZERO COMPLEX_NORM_0 COMPLEX_NORM_CX COMPLEX_NORM_MUL
   COMPLEX_NORM_NZ COMPLEX_NORM_POW COMPLEX_POLYFUN_EQ_0
   COMPLEX_POLYFUN_FINITE_ROOTS COMPLEX_POLYFUN_LINEAR_FACTOR_ROOT
   COMPLEX_POW_ADD COMPLEX_RING_CLAUSES COMPLEX_RING_DIV COMPLEX_RING_OF_INT
   COMPLEX_RING_POW COMPLEX_RING_SUM COMPLEX_SUB_0 COMPLEX_SUB_RDISTRIB
   COMPLEX_SUB_REFL COMPLEX_SUB_RZERO CX_DIV CX_INJ EMPTY_GSPEC EXTENSION
   FIELD_COMPLEX_RING FIELD_EXTENSION_SUBFIELD_GENERATED
   FIELD_IMP_INTEGRAL_DOMAIN FIELD_IMP_NONTRIVIAL_RING
   FIELD_RING_HOMOMORPHISM_MONOMORPHISM FIELD_SUBFIELD_GENERATED FIELD_UNIT
   FINITELY_GENERATED_ABELIAN_GROUP_DISCRETE FINITELY_GENERATED_UNIT_GROUP
   FINITE_EMPTY FINITE_FUNSPACE FINITE_IMAGE_INJ_GENERAL
   FINITE_IMP_ALGEBRAIC_EXTENSION FINITE_INTSEG FINITE_NUMSEG
   FINITE_PRODUCT_DEPENDENT FINITE_SUBSET FINITE_UNIONS FORALL_IN_GSPEC
   FORALL_IN_IMAGE FTA HAS_SIZE HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS
   INTEGER_CLOSED INTEGER_REAL_OF_INT INTEGER_RING
   INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING INTEGRAL_DOMAIN_REGULAR
   INTEGRAL_DOMAIN_RING_OF_INTEGERS INTEGRAL_ELEMENT_FROM_RELATION IN_ELIM_THM
   IN_IMAGE IN_NUMSEG IN_RING_POLYNOMIAL_CARRIER_COMPOSE IN_SING IN_UNIV
   IRREDUCIBLE_IMP_POLY_DEG_NZ I_O_ID I_THM LE LEFT_IMP_EXISTS_THM LE_0 LE_1
   LE_REFL MEMBER_NOT_EMPTY MINIMAL_POLYNOMIAL
   MINIMAL_POLYNOMIAL_DEG_LE_EXTENSION_DEGREE MONO_EXISTS NORM_POS_LE NOT_SUC
   NUMBER_FIELD_ALGEBRAIC NUMBER_FIELD_IMP_FIELD : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (POLY_DEG_MONOMORPHIC_IMAGE POLY_EVAL_COMPLEX_RING PRIME_SUBFIELD_CHAR_0
   PRIME_SUBFIELD_HOMOMORPHISM_EXISTS PRIME_SUBFIELD_SUBFIELD_GENERATED
   REAL_ABS_BOUNDS REAL_ABS_NUM REAL_LE_MUL2 REAL_LE_REFL REAL_LE_TRANS
   REAL_POW_EQ_1 REAL_POW_LE REAL_POW_MONO REAL_POW_ONE RESTRICTION
   RESTRICTION_IN_EXTENSIONAL RESTRICTION_IN_RING_HOMOMORPHISM_EXTENSIONS RING_1
   RING_ADD_RNEG RING_CHAR_COMPLEX_RING RING_CHAR_SUBFIELD_GENERATED
   RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED RING_HOMOMORPHISM_0
   RING_HOMOMORPHISM_1 RING_HOMOMORPHISM_COMPOSE RING_HOMOMORPHISM_EQ
   RING_HOMOMORPHISM_EXTENSIONS_NONEMPTY RING_HOMOMORPHISM_EXTENSIONS_ROOT
   RING_HOMOMORPHISM_FROM_SUBFIELD_GENERATED
   RING_HOMOMORPHISM_INTEGER_RING_OF_INT RING_HOMOMORPHISM_MUL
   RING_HOMOMORPHISM_POW RING_HOMOMORPHISM_RING_OF_INT
   RING_HOMOMORPHISM_SUBFIELD_INCLUSION RING_MATRIX_SOLVE RING_MONOMORPHISM_ALT
   RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_MUL_LZERO RING_MUL_RID RING_NEG
   RING_OF_INTEGERS RING_OF_INTEGERS_CARRIER
   RING_OF_INTEGERS_MINIMAL_POLYNOMIAL_Q RING_OF_INTEGERS_SUBSET RING_OF_INT_0
   RING_OF_INT_1 RING_OF_INT_CASES RING_OF_INT_EQ_CHAR_0 RING_OF_NUM_1
   RING_ORDER_NONZERO_MULTSYS RING_POLYNOMIAL RING_POW RING_POW_1 RING_POW_ADD
   RING_POW_RING_ORDER RING_PRODUCT_SUBRING_GENERATED_GEN RING_SUM_DELTA
   RING_SUM_EQ RING_UNIT_0 RING_UNIT_IN_CARRIER SEPARABLE_EXTENSION_CHAR0
   SKOLEM_THM SUBFIELD_GENERATED SUBSET SUC_SUB1 UNIONS_GSPEC UNIT_GROUP
   VSUM_CLAUSES_LEFT VSUM_CLAUSES_NUMSEG VSUM_COMPLEX_LMUL VSUM_EQ_NUMSEG
   VSUM_OFFSET VSUM_SUB_NUMSEG int_eq int_of_num_th int_tybij lemma monic
   number_field rational real_pow ring_homomorphism_extensions ring_monomorphism
   ring_multsys ring_of_integers ring_pow : thm)
  deriving Inhabited

/-- What complex_embeddings.ml uses from Session besides theorems. -/
structure ComplexEmbeddingsDeps where
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
  NORM_ARITH : term → ExceptT String IO thm
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
/- complex_embeddings.ml phrases from line 93 to 670                      -/
/- ---------------------------------------------------------------------- -/

structure ComplexEmbeddings where
  -- @@FIELDS
  complex_embeddings : thm
  COMPLEX_MATRIX_SOLVE : thm
  COMPLEX_PRIME_SUBFIELD : thm
  COMPLEX_POLYFUN_MONIC_COEFF_BOUND : thm
  COMPLEX_POLYFUN_MONIC_INTEGER_ROOTS_FINITE : thm
  COMPLEX_EMBEDDINGS_RESTRICTION : thm
  COMPLEX_EMBEDDINGS_MONOMORPHISM : thm
  COMPLEX_EMBEDDINGS_EXTENSIONS : thm
  COMPLEX_EMBEDDINGS_NONEMPTY : thm
  COMPLEX_EMBEDDINGS_HAS_SIZE : thm
  FINITE_COMPLEX_EMBEDDINGS : thm
  COMPLEX_EMBEDDINGS_CONJUGATES : thm
  RING_OF_INTEGERS_CONJUGATES_POLYFUN : thm
  RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE : thm
  COMPLEX_EMBEDDINGS_ROOT_OF_UNITY : thm
  RING_OF_INTEGERS_ROOT_OF_UNITY : thm
  NUMBER_FIELD_ROOTS_OF_UNITY_FINITE : thm
  NUMBER_FIELD_UNIT_GROUP_FINITELY_GENERATED : thm
  NUMBER_FIELD_UNITS_GENERATORS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupComplexEmbeddings [HolBase] (D : ComplexEmbeddingsDeps) :
    ExceptT String IO ComplexEmbeddings := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC,
        COMPLEX_RING, INDUCT_TAC, MESON, MESON_TAC, NORM_ARITH, REAL_ARITH,
        REAL_ARITH_TAC, REAL_RAT_REDUCE_CONV, new_definition, .. } := D
  let { ABELIAN_UNIT_GROUP, ADD1, ADD_EQ_0, ADD_SUB,
        ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING,
        ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM_ROOT, ARITH_EQ, COEFF_COMPOSE,
        COMPLEX_ADD_LID, COMPLEX_ADD_RID, COMPLEX_MUL_ASSOC, COMPLEX_MUL_LZERO,
        COMPLEX_MUL_RZERO, COMPLEX_NORM_0, COMPLEX_NORM_CX, COMPLEX_NORM_MUL,
        COMPLEX_NORM_NZ, COMPLEX_NORM_POW, COMPLEX_POLYFUN_EQ_0,
        COMPLEX_POLYFUN_FINITE_ROOTS, COMPLEX_POLYFUN_LINEAR_FACTOR_ROOT,
        COMPLEX_POW_ADD, COMPLEX_RING_CLAUSES, COMPLEX_RING_DIV, COMPLEX_RING_OF_INT,
        COMPLEX_RING_POW, COMPLEX_RING_SUM, COMPLEX_SUB_0, COMPLEX_SUB_RDISTRIB,
        COMPLEX_SUB_REFL, COMPLEX_SUB_RZERO, CX_DIV, CX_INJ, EMPTY_GSPEC, EXTENSION,
        FIELD_COMPLEX_RING, FIELD_EXTENSION_SUBFIELD_GENERATED,
        FIELD_IMP_INTEGRAL_DOMAIN, FIELD_IMP_NONTRIVIAL_RING,
        FIELD_RING_HOMOMORPHISM_MONOMORPHISM, FIELD_SUBFIELD_GENERATED, FIELD_UNIT,
        FINITELY_GENERATED_ABELIAN_GROUP_DISCRETE, FINITELY_GENERATED_UNIT_GROUP,
        FINITE_EMPTY, FINITE_FUNSPACE, FINITE_IMAGE_INJ_GENERAL,
        FINITE_IMP_ALGEBRAIC_EXTENSION, FINITE_INTSEG, FINITE_NUMSEG,
        FINITE_PRODUCT_DEPENDENT, FINITE_SUBSET, FINITE_UNIONS, FORALL_IN_GSPEC,
        FORALL_IN_IMAGE, FTA, HAS_SIZE, HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS,
        INTEGER_CLOSED, INTEGER_REAL_OF_INT, INTEGER_RING,
        INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING, INTEGRAL_DOMAIN_REGULAR,
        INTEGRAL_DOMAIN_RING_OF_INTEGERS, INTEGRAL_ELEMENT_FROM_RELATION, IN_ELIM_THM,
        IN_IMAGE, IN_NUMSEG, IN_RING_POLYNOMIAL_CARRIER_COMPOSE, IN_SING, IN_UNIV,
        IRREDUCIBLE_IMP_POLY_DEG_NZ, I_O_ID, I_THM, LE, LEFT_IMP_EXISTS_THM, LE_0,
        LE_1, LE_REFL, MEMBER_NOT_EMPTY, MINIMAL_POLYNOMIAL,
        MINIMAL_POLYNOMIAL_DEG_LE_EXTENSION_DEGREE, MONO_EXISTS, NORM_POS_LE, NOT_SUC,
        NUMBER_FIELD_ALGEBRAIC, NUMBER_FIELD_IMP_FIELD, .. } := D.core1
  let { POLY_DEG_MONOMORPHIC_IMAGE, POLY_EVAL_COMPLEX_RING, PRIME_SUBFIELD_CHAR_0,
        PRIME_SUBFIELD_HOMOMORPHISM_EXISTS, PRIME_SUBFIELD_SUBFIELD_GENERATED,
        REAL_ABS_BOUNDS, REAL_ABS_NUM, REAL_LE_MUL2, REAL_LE_REFL, REAL_LE_TRANS,
        REAL_POW_EQ_1, REAL_POW_LE, REAL_POW_MONO, REAL_POW_ONE, RESTRICTION,
        RESTRICTION_IN_EXTENSIONAL, RESTRICTION_IN_RING_HOMOMORPHISM_EXTENSIONS,
        RING_1, RING_ADD_RNEG, RING_CHAR_COMPLEX_RING, RING_CHAR_SUBFIELD_GENERATED,
        RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED, RING_HOMOMORPHISM_0,
        RING_HOMOMORPHISM_1, RING_HOMOMORPHISM_COMPOSE, RING_HOMOMORPHISM_EQ,
        RING_HOMOMORPHISM_EXTENSIONS_NONEMPTY, RING_HOMOMORPHISM_EXTENSIONS_ROOT,
        RING_HOMOMORPHISM_FROM_SUBFIELD_GENERATED,
        RING_HOMOMORPHISM_INTEGER_RING_OF_INT, RING_HOMOMORPHISM_MUL,
        RING_HOMOMORPHISM_POW, RING_HOMOMORPHISM_RING_OF_INT,
        RING_HOMOMORPHISM_SUBFIELD_INCLUSION, RING_MATRIX_SOLVE, RING_MONOMORPHISM_ALT,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL_LZERO, RING_MUL_RID, RING_NEG,
        RING_OF_INTEGERS, RING_OF_INTEGERS_CARRIER,
        RING_OF_INTEGERS_MINIMAL_POLYNOMIAL_Q, RING_OF_INTEGERS_SUBSET, RING_OF_INT_0,
        RING_OF_INT_1, RING_OF_INT_CASES, RING_OF_INT_EQ_CHAR_0, RING_OF_NUM_1,
        RING_ORDER_NONZERO_MULTSYS, RING_POLYNOMIAL, RING_POW, RING_POW_1,
        RING_POW_ADD, RING_POW_RING_ORDER, RING_PRODUCT_SUBRING_GENERATED_GEN,
        RING_SUM_DELTA, RING_SUM_EQ, RING_UNIT_0, RING_UNIT_IN_CARRIER,
        SEPARABLE_EXTENSION_CHAR0, SKOLEM_THM, SUBFIELD_GENERATED, SUBSET, SUC_SUB1,
        UNIONS_GSPEC, UNIT_GROUP, VSUM_CLAUSES_LEFT, VSUM_CLAUSES_NUMSEG,
        VSUM_COMPLEX_LMUL, VSUM_EQ_NUMSEG, VSUM_OFFSET, VSUM_SUB_NUMSEG, int_eq,
        int_of_num_th, int_tybij, monic, number_field, rational, real_pow,
        ring_homomorphism_extensions, ring_monomorphism, ring_multsys,
        ring_of_integers, ring_pow, .. } := D.core2
  -- @@SCOPE END

  let complex_embeddings ← new_definition
    r"complex_embeddings (k:A ring) =
  {f | ring_homomorphism(k,complex_ring) f /\
       f IN EXTENSIONAL (ring_carrier k)}"

  let COMPLEX_MATRIX_SOLVE ← prove
    r"!s (m:K->K->complex) v.
        FINITE s /\ ~(ring_det complex_ring s m = Cx(&0))
        ==> ?t. !i. i IN s ==> vsum s (\j. m i j * t j) = v i"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"complex_ring"), (← q r"s:K->bool"), (← q r"m:K->K->complex"), (← q r"v:K->complex")] RING_MATRIX_SOLVE) THEN ASM_SIMP_TAC [FIELD_UNIT, FIELD_COMPLEX_RING, COMPLEX_RING_CLAUSES, IN_UNIV, COMPLEX_RING_SUM] THEN MESON_TAC [])

  let COMPLEX_PRIME_SUBFIELD ← prove
    r"ring_carrier(subfield_generated complex_ring {Cx(&0)}) =
   {Cx q | rational q}"
    (MP_TAC (← ISPEC (← q r"complex_ring") PRIME_SUBFIELD_CHAR_0) THEN REWRITE_TAC [FIELD_COMPLEX_RING, RING_CHAR_COMPLEX_RING, COMPLEX_RING_CLAUSES, COMPLEX_RING_DIV, COMPLEX_RING_OF_INT] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM, rational, (← GSYM CX_DIV), int_eq, int_of_num_th] THEN MESON_TAC [int_tybij, INTEGER_REAL_OF_INT])

  let COMPLEX_POLYFUN_MONIC_COEFF_BOUND ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"~(SUC n <= n)"
    let r2 ← ARITH_RULE q1
    let v3 ← GSYM VSUM_COMPLEX_LMUL
    let v4 ← GSYM VSUM_COMPLEX_LMUL
    let q5 ← q r"SUC n"
    let v6 ← SPEC q5 LE_0
    let v7 ← MATCH_MP VSUM_CLAUSES_LEFT v6
    let v8 ← GSYM COMPLEX_MUL_ASSOC
    let p9 ← prove r"!n (b:num->complex) w z.
        (z - w) * vsum(0..n) (\i. b i * z pow i) =
        vsum(0..SUC n)
         (\i. ((if i = 0 then Cx(&0) else b(i - 1)) -
               w * (if i <= n then b i else Cx(&0))) * z pow i)" (REPEAT GEN_TAC THEN REWRITE_TAC [COMPLEX_SUB_RDISTRIB, VSUM_SUB_NUMSEG] THEN REWRITE_TAC [v8] THEN BINOP_TAC THENL [REWRITE_TAC [v7] THEN REWRITE_TAC [COMPLEX_MUL_LZERO, COMPLEX_ADD_LID, ADD1, VSUM_OFFSET] THEN REWRITE_TAC [ADD_EQ_0, ARITH_EQ, ADD_SUB] THEN SIMP_TAC [v4, FINITE_NUMSEG] THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC [COMPLEX_POW_ADD] THEN CONV_TAC COMPLEX_RING, SIMP_TAC [v3, FINITE_NUMSEG] THEN SIMP_TAC [VSUM_CLAUSES_NUMSEG, LE_0, r2] THEN REWRITE_TAC [COMPLEX_MUL_LZERO, COMPLEX_MUL_RZERO, COMPLEX_ADD_RID]])
    let lemma := p9
    let q10 ← q r"norm(x:complex) <= X /\ norm(y:complex) <= Y ==> norm(x - y) <= X + Y"
    let r11 ← NORM_ARITH q10
    let q12 ← q r"((&1:real) + R) * X = X + R * X"
    let r13 ← REAL_ARITH q12
    let q14 ← q r"i <= SUC n"
    let v15 ← ASSUME q14
    let q16 ← q r"i:num"
    let q17 ← q r"w:complex"
    let v18 ← ISPEC q17 NORM_POS_LE
    let q19 ← q r"&0:real <= (&1 + R) pow n"
    let q20 ← q r"z:complex"
    let q21 ← q r"R:real"
    let q22 ← q r"b:num->complex"
    let q23 ← q r"~(SUC n <= n)"
    let r24 ← ARITH_RULE q23
    let q25 ← q r"SUC n"
    let q26 ← q r"(b:num->complex) n = Cx(&1) /\ norm(w:complex) <= R"
    let q27 ← q r"\i. (a:num->complex) i -
          ((if i = 0 then Cx(&0) else b(i - 1)) -
           w * (if i <= n then b i else Cx(&0)))"
    let q28 ← q r"SUC n"
    let v29 ← ISPECL [q28, q27] COMPLEX_POLYFUN_EQ_0
    let q30 ← q r"!i. i <= SUC n
        ==> (a:num->complex) i =
            (if i = 0 then Cx(&0) else b(i - 1)) -
            w * (if i <= n then b i else Cx(&0))"
    let q31 ← q r"b:num->complex"
    let q32 ← q r"w:complex"
    let q33 ← q r"SUC n"
    let q34 ← q r"SUC n"
    let q35 ← q r"a:num->complex"
    let v36 ← ISPECL [q35, q34] FTA
    prove
      r"!n (a:num->complex) R.
          a n = Cx(&1) /\
          (!w. vsum(0..n) (\i. a i * w pow i) = Cx(&0) ==> norm w <= R)
          ==> !i. i <= n ==> norm(a i) <= (&1 + R) pow n"
      (INDUCT_TAC THENL [SIMP_TAC [LE, real_pow, COMPLEX_NORM_CX, REAL_ABS_NUM, REAL_LE_REFL], REPEAT GEN_TAC THEN STRIP_TAC] THEN MP_TAC v36 THEN ANTS_TAC THENL [DISJ2_TAC THEN DISCH_THEN (MP_TAC o (SPEC q33)) THEN ASM_REWRITE_TAC [IN_NUMSEG, CX_INJ] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ARITH_TAC, DISCH_THEN (X_CHOOSE_TAC q32)] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP COMPLEX_POLYFUN_LINEAR_FACTOR_ROOT)) THEN REWRITE_TAC [SUC_SUB1] THEN DISCH_THEN (X_CHOOSE_TAC q31) THEN SUBGOAL_THEN q30 ASSUME_TAC THENL [MP_TAC v29 THEN ASM_REWRITE_TAC [COMPLEX_SUB_RDISTRIB, VSUM_SUB_NUMSEG, lemma, COMPLEX_SUB_REFL] THEN REWRITE_TAC [COMPLEX_SUB_0, IN_NUMSEG, LE_0], ALL_TAC] THEN SUBGOAL_THEN q26 STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN FIRST_ASSUM (MP_TAC o (SPEC q25)) THEN REWRITE_TAC [LE_REFL, NOT_SUC, SUC_SUB1, r24, COMPLEX_MUL_RZERO, COMPLEX_SUB_RZERO] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (SPECL [q22, q21])) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN X_GEN_TAC q20 THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [COMPLEX_MUL_RZERO], DISCH_TAC] THEN SUBGOAL_THEN q19 ASSUME_TAC THENL [MATCH_MP_TAC REAL_POW_LE THEN MP_TAC v18 THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN X_GEN_TAC q16 THEN DISCH_TAC THEN FIRST_ASSUM (SUBST1_TAC o (← do let c := v15; pure (fun th => MATCH_MP th c))) THEN REWRITE_TAC [real_pow, r13] THEN MATCH_MP_TAC r11 THEN REWRITE_TAC [COMPLEX_NORM_MUL] THEN CONJ_TAC THENL [COND_CASES_TAC THEN ASM_REWRITE_TAC [COMPLEX_NORM_0] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC, MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC [NORM_POS_LE] THEN COND_CASES_TAC THEN ASM_SIMP_TAC [COMPLEX_NORM_0, REAL_LE_REFL]])

  let COMPLEX_POLYFUN_MONIC_INTEGER_ROOTS_FINITE ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"a = b ==> a = Cx(&0) ==> b = Cx(&0)"
    let r2 ← MESON [] q1
    let q3 ← q r"vsum(0..n) (\i. Cx(c i) * z pow i) = Cx(&0)"
    let q4 ← q r"i:num"
    let q5 ← q r"d:num"
    let q6 ← q r"(&1:real) + R"
    let v7 ← ISPECL [q6, q5] REAL_POW_LE
    let q8 ← q r"((&1:real) + R) pow n"
    let v9 ← GSYM REAL_ABS_BOUNDS
    let q10 ← q r"i:num"
    let q11 ← q r"z:complex"
    let q12 ← q r"z:complex"
    let v13 ← ISPEC q12 NORM_POS_LE
    let q14 ← q r"&1:real <= &1 + R"
    let q15 ← q r"R:real"
    let q16 ← q r"\i. Cx((c:num->real) i)"
    let q17 ← q r"n:num"
    let v18 ← ISPECL [q17, q16, q15] COMPLEX_POLYFUN_MONIC_COEFF_BOUND
    let q19 ← q r"\i. if i <= n then (c:num->real) i else &0"
    let q20 ← q r"n:num"
    let q21 ← q r"c:num->real"
    let q22 ← q r"n:num"
    let q23 ← q r"z:complex"
    let q24 ← q r"n:num"
    let q25 ← q r"(c:num->real) n = &1"
    let q26 ← q r"c:num->real"
    let q27 ← q r"n:num"
    let q28 ← q r"UNIONS {{z | c n = &1 /\ vsum(0..n) (\i. Cx(c i) * z pow i) = Cx(&0)} |
            n IN 0..d /\
            c IN {c | (!i. i IN 0..d
                           ==> c i IN {x | integer x /\
                                           --((&1 + R) pow d) <= x /\
                                           x <= (&1 + R) pow d}) /\
                      (!i. ~(i IN 0..d) ==> c i = &0)}}"
    prove
      r"!d R. FINITE {z | ?n c. 1 <= n /\ n <= d /\ (!i. integer(c i)) /\
                             c n = &1 /\
                             vsum(0..n) (\i. Cx(c i) * z pow i) = Cx(&0) /\
                             (!w. vsum(0..n) (\i. Cx(c i) * w pow i) = Cx(&0)
                                  ==> norm w <= R)}"
      (REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC q28 THEN CONJ_TAC THENL [REWRITE_TAC [FINITE_UNIONS, FORALL_IN_GSPEC] THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN SIMP_TAC [FINITE_NUMSEG, FINITE_FUNSPACE, FINITE_INTSEG], MAP_EVERY X_GEN_TAC [q27, q26] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN ASM_CASES_TAC q25 THEN ASM_REWRITE_TAC [EMPTY_GSPEC, FINITE_EMPTY, COMPLEX_POLYFUN_FINITE_ROOTS] THEN EXISTS_TAC q24 THEN ASM_REWRITE_TAC [IN_NUMSEG, LE_0, LE_REFL, CX_INJ] THEN REAL_ARITH_TAC], ALL_TAC] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM, UNIONS_GSPEC, IN_NUMSEG, LE_0] THEN X_GEN_TAC q23 THEN DISCH_THEN (X_CHOOSE_THEN q22 (X_CHOOSE_THEN q21 STRIP_ASSUME_TAC)) THEN MAP_EVERY EXISTS_TAC [q20, q19] THEN MP_TAC v18 THEN ASM_REWRITE_TAC [COMPLEX_NORM_CX] THEN DISCH_TAC THEN SUBGOAL_THEN q14 ASSUME_TAC THENL [MP_TAC v13 THEN FIRST_X_ASSUM (MP_TAC o (SPEC q11)) THEN ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [LE_REFL] THEN REPEAT CONJ_TAC THENL [X_GEN_TAC q10 THEN DISCH_TAC THEN COND_CASES_TAC THENL [ASM_REWRITE_TAC [v9] THEN TRANS_TAC REAL_LE_TRANS q8 THEN ASM_SIMP_TAC [REAL_POW_MONO], MP_TAC v7 THEN REWRITE_TAC [INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC], X_GEN_TAC q4 THEN DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [] THEN ASM_ARITH_TAC, UNDISCH_TAC q3 THEN MATCH_MP_TAC r2 THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN SIMP_TAC []])

  let COMPLEX_EMBEDDINGS_RESTRICTION ← prove
    r"!k:A ring f.
        ring_homomorphism(k,complex_ring) f
        ==> ?g. g IN complex_embeddings k /\
                !x. x IN ring_carrier k ==> g x = f x"
    (REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"RESTRICTION (ring_carrier k) (f:A->complex)") THEN REWRITE_TAC [complex_embeddings, IN_ELIM_THM, RESTRICTION_IN_EXTENSIONAL] THEN SIMP_TAC [RESTRICTION] THEN MATCH_MP_TAC RING_HOMOMORPHISM_EQ THEN EXISTS_TAC (← q r"f:A->complex") THEN ASM_SIMP_TAC [RESTRICTION])

  let COMPLEX_EMBEDDINGS_MONOMORPHISM ← prove
    r"!k:A ring g.
        field k /\ g IN complex_embeddings k
        ==> ring_monomorphism(k,complex_ring) g /\
            ring_monomorphism(subfield_generated k {ring_0 k},complex_ring) g"
    (REWRITE_TAC [complex_embeddings, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN ASM_SIMP_TAC [FIELD_IMP_NONTRIVIAL_RING, FIELD_COMPLEX_RING, FIELD_SUBFIELD_GENERATED] THEN SUBST1_TAC (← SYM (← CONJUNCT2 (← ISPEC (← q r"g:A->complex") I_O_ID))) THEN MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC (← q r"k:A ring") THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION])

  let COMPLEX_EMBEDDINGS_EXTENSIONS ← prove
    r"!(g:A->complex) (k:A ring).
        field k /\
        ring_homomorphism(subfield_generated k {ring_0 k},complex_ring) g
        ==> complex_embeddings k =
            ring_homomorphism_extensions
             (subfield_generated k {ring_0 k},k,complex_ring) (I,g)"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [complex_embeddings, ring_homomorphism_extensions, I_THM, EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC (← q r"f:A->complex") THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"f:A->complex"), (← q r"g:A->complex"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"complex_ring"), (← q r"{ring_0(subfield_generated k {ring_0 k:A})}")] RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED) THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, IN_SING, PRIME_SUBFIELD_SUBFIELD_GENERATED, RING_HOMOMORPHISM_FROM_SUBFIELD_GENERATED, (← ISPECL [(← q r"subfield_generated k {ring_0 k:A}"), (← q r"complex_ring")] RING_HOMOMORPHISM_0)])

  let COMPLEX_EMBEDDINGS_NONEMPTY ← prove
    r"!k:A ring. number_field k ==> ~(complex_embeddings k = {})"
    (REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [number_field])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"complex_ring")] PRIME_SUBFIELD_HOMOMORPHISM_EXISTS) THEN ASM_REWRITE_TAC [FIELD_COMPLEX_RING, RING_CHAR_COMPLEX_RING] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"g:A->complex")) THEN MP_TAC (← ISPECL [(← q r"g:A->complex"), (← q r"k:A ring")] COMPLEX_EMBEDDINGS_EXTENSIONS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_HOMOMORPHISM_EXTENSIONS_NONEMPTY THEN ASM_SIMP_TAC [ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING, FINITE_IMP_ALGEBRAIC_EXTENSION])

  let COMPLEX_EMBEDDINGS_HAS_SIZE ← prove
    r"!k:A ring.
        number_field k
        ==> complex_embeddings k HAS_SIZE
            extension_degree (subfield_generated k {ring_0 k},k) I"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [number_field])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"complex_ring")] PRIME_SUBFIELD_HOMOMORPHISM_EXISTS) THEN ASM_REWRITE_TAC [FIELD_COMPLEX_RING, RING_CHAR_COMPLEX_RING] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"g:A->complex")) THEN MP_TAC (← ISPECL [(← q r"g:A->complex"), (← q r"k:A ring")] COMPLEX_EMBEDDINGS_EXTENSIONS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS THEN ASM_SIMP_TAC [SEPARABLE_EXTENSION_CHAR0, FINITE_IMP_ALGEBRAIC_EXTENSION, ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING, RING_CHAR_SUBFIELD_GENERATED])

  let FINITE_COMPLEX_EMBEDDINGS ← prove
    r"!k:A ring. number_field k ==> FINITE(complex_embeddings k)"
    (MESON_TAC [COMPLEX_EMBEDDINGS_HAS_SIZE, HAS_SIZE])

  let COMPLEX_EMBEDDINGS_CONJUGATES ← prove
    r"!k:A ring g x.
        number_field k /\ g IN complex_embeddings k /\ x IN ring_carrier k
        ==> IMAGE (\h. h x) (complex_embeddings k) =
            {z | poly_eval complex_ring
                   (g o minimal_polynomial
                          (subfield_generated k {ring_0 k},k) I x) z =
                 Cx(&0)}"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [number_field])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN (← q r"ring_homomorphism(subfield_generated k {ring_0 k},complex_ring)
                     (g:A->complex) /\
    field_extension(subfield_generated k {ring_0 k},k) (I:A->A) /\
    algebraic_over(subfield_generated k {ring_0 k},k) (I:A->A) x") STRIP_ASSUME_TAC THENL [RULE_ASSUM_TAC (REWRITE_RULE [complex_embeddings, IN_ELIM_THM]) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_FROM_SUBFIELD_GENERATED, FIELD_EXTENSION_SUBFIELD_GENERATED, NUMBER_FIELD_ALGEBRAIC], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"g:A->complex"), (← q r"k:A ring")] COMPLEX_EMBEDDINGS_EXTENSIONS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN X_GEN_TAC (← q r"z:complex") THEN EQ_TAC THENL [DISCH_THEN (X_CHOOSE_THEN (← q r"h:A->complex") STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"g:A->complex"), (← q r"h:A->complex"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"complex_ring"), (← q r"x:A")] RING_HOMOMORPHISM_EXTENSIONS_ROOT) THEN ASM_REWRITE_TAC [COMPLEX_RING_CLAUSES], DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"complex_ring"), (← q r"I:A->A"), (← q r"g:A->complex"), (← q r"x:A"), (← q r"z:complex")] ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM_ROOT) THEN ASM_SIMP_TAC [ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING, COMPLEX_RING_CLAUSES, FINITE_IMP_ALGEBRAIC_EXTENSION, IN_UNIV] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"s:A->complex") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"RESTRICTION (ring_carrier k) (s:A->complex)") THEN ASM_SIMP_TAC [RESTRICTION] THEN MATCH_MP_TAC RESTRICTION_IN_RING_HOMOMORPHISM_EXTENSIONS THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION])

  let RING_OF_INTEGERS_CONJUGATES_POLYFUN ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"1 <= n <=> ~(n = 0)")
    prove
      r"!k:A ring x.
          number_field k /\ x IN ring_carrier(ring_of_integers k)
          ==> ?n c. 1 <= n /\
                    n <= extension_degree (subfield_generated k {ring_0 k},k) I /\
                    (!i. integer(c i)) /\ c n = &1 /\
                    IMAGE (\g. g x) (complex_embeddings k) =
                    {z | vsum(0..n) (\i. Cx(c i) * z pow i) = Cx(&0)}"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP COMPLEX_EMBEDDINGS_NONEMPTY)) THEN REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY)] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"g:A->complex")) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [number_field])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"g:A->complex")] COMPLEX_EMBEDDINGS_MONOMORPHISM) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_homomorphism(k,complex_ring) (g:A->complex) /\
      ring_homomorphism(subfield_generated k {ring_0 k},complex_ring) g") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"g:A->complex"), (← q r"x:A")] COMPLEX_EMBEDDINGS_CONJUGATES) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A")] RING_OF_INTEGERS_MINIMAL_POLYNOMIAL_Q) THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"x:A")] MINIMAL_POLYNOMIAL_DEG_LE_EXTENSION_DEGREE) THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"x:A")] MINIMAL_POLYNOMIAL) THEN ASM_SIMP_TAC [NUMBER_FIELD_ALGEBRAIC, FIELD_EXTENSION_SUBFIELD_GENERATED] THEN ABBREV_TAC (← q r"p = minimal_polynomial (subfield_generated k {ring_0 k},k) (I:A->A) x") THEN ABBREV_TAC (← q r"n = poly_deg (subfield_generated k {ring_0 k}) (p:(1->num)->A)") THEN STRIP_TAC THEN DISCH_TAC THEN REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"a:num->int") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"!w. poly_eval complex_ring ((g:A->complex) o p) w =
          vsum(0..n) (\i. Cx(real_of_int((a:num->int) i)) * w pow i)") (fun th => REWRITE_TAC [th]) THENL [GEN_TAC THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_0 k:A}"), (← q r"complex_ring"), (← q r"g:A->complex"), (← q r"p:(1->num)->A")] POLY_DEG_MONOMORPHIC_IMAGE) THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_0 k:A}"), (← q r"complex_ring"), (← q r"g:A->complex"), (← q r"(:1)"), (← q r"p:(1->num)->A")] IN_RING_POLYNOMIAL_CARRIER_COMPOSE) THEN ASM_REWRITE_TAC [RING_POLYNOMIAL] THEN SIMP_TAC [POLY_EVAL_COMPLEX_RING] THEN REPEAT DISCH_TAC THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN ASM_REWRITE_TAC [COEFF_COMPOSE, COMPLEX_RING_OF_INT, (← MATCH_MP RING_HOMOMORPHISM_RING_OF_INT (← ASSUME (← q r"ring_homomorphism(k,complex_ring) (g:A->complex)")))], DISCH_TAC] THEN MAP_EVERY EXISTS_TAC [(← q r"n:num"), (← q r"\i. real_of_int((a:num->int) i)")] THEN ASM_REWRITE_TAC [INTEGER_REAL_OF_INT] THEN CONJ_TAC THENL [EXPAND_TAC "n" THEN REWRITE_TAC [r1] THEN MATCH_MP_TAC IRREDUCIBLE_IMP_POLY_DEG_NZ THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED], UNDISCH_TAC (← q r"monic (subfield_generated k {ring_0 k}) (p:(1->num)->A)") THEN ASM_REWRITE_TAC [monic, (← CONJUNCT2 SUBFIELD_GENERATED), (← GSYM RING_OF_INT_1)] THEN ASM_SIMP_TAC [RING_OF_INT_EQ_CHAR_0, int_of_num_th]])

  let RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE ← prove
    r"!k:A ring R.
        number_field k
        ==> FINITE {x | x IN ring_carrier(ring_of_integers k) /\
                        !g. g IN complex_embeddings k ==> norm(g x) <= R}"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP COMPLEX_EMBEDDINGS_NONEMPTY)) THEN REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY)] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"g:A->complex")) THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{x | x IN ring_carrier k /\
         (g:A->complex) x IN
         {z | ?n c. 1 <= n /\
                    n <= extension_degree
                          (subfield_generated k {ring_0 k},k) I /\
                    (!i. integer(c i)) /\ c n = &1 /\
                    vsum(0..n) (\i. Cx(c i) * z pow i) = Cx(&0) /\
                    (!w. vsum(0..n) (\i. Cx(c i) * w pow i) = Cx(&0)
                         ==> norm w <= R)}}") THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_IMAGE_INJ_GENERAL THEN REWRITE_TAC [COMPLEX_POLYFUN_MONIC_INTEGER_ROOTS_FINITE] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"g:A->complex")] COMPLEX_EMBEDDINGS_MONOMORPHISM) THEN ASM_SIMP_TAC [NUMBER_FIELD_IMP_FIELD] THEN DISCH_THEN (ACCEPT_TAC o (CONJUNCT2 o ((GEN_REWRITE_RULE id [ring_monomorphism]) o CONJUNCT1))), ALL_TAC] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:A") THEN STRIP_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A")] RING_OF_INTEGERS_CONJUGATES_POLYFUN) THEN ASM_REWRITE_TAC [] THEN REPEAT (MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MP_TAC o (GEN_REWRITE_RULE id [EXTENSION])) THEN REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM th)])) THEN ASM_MESON_TAC [])

  let COMPLEX_EMBEDDINGS_ROOT_OF_UNITY ← prove
    r"!k:A ring g x n.
        g IN complex_embeddings k /\ x IN ring_carrier k /\
        1 <= n /\ ring_pow k x n = ring_1 k
        ==> norm(g x) = &1"
    (REWRITE_TAC [complex_embeddings, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"complex_ring"), (← q r"g:A->complex")] RING_HOMOMORPHISM_POW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (SPECL [(← q r"x:A"), (← q r"n:num")])) THEN ASM_SIMP_TAC [(← ISPECL [(← q r"k:A ring"), (← q r"complex_ring")] RING_HOMOMORPHISM_1), COMPLEX_RING_POW, COMPLEX_RING_CLAUSES] THEN DISCH_THEN (MP_TAC o ((AP_TERM (← q r"norm:complex->real")) o SYM)) THEN REWRITE_TAC [COMPLEX_NORM_POW, COMPLEX_NORM_CX, REAL_ABS_NUM] THEN REWRITE_TAC [REAL_POW_EQ_1] THEN MP_TAC (← ISPEC (← q r"(g:A->complex) x") NORM_POS_LE) THEN UNDISCH_TAC (← q r"1 <= n") THEN ARITH_TAC)

  let RING_OF_INTEGERS_ROOT_OF_UNITY ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"1 <= n <=> ~(n = 0)")
    prove
      r"!k:A ring x.
          number_field k /\ x IN ring_carrier(ring_of_integers k)
          ==> ((?n. 1 <= n /\ ring_pow k x n = ring_1 k) <=>
               !g. g IN complex_embeddings k ==> norm(g x) = &1)"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN EQ_TAC THENL [ASM_MESON_TAC [COMPLEX_EMBEDDINGS_ROOT_OF_UNITY], DISCH_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (MP_TAC o (MATCH_MP COMPLEX_EMBEDDINGS_NONEMPTY)) THEN REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY)] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"g:A->complex")) THEN SUBGOAL_THEN (← q r"~(x:A = ring_0 k)") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"g:A->complex"))) THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (MP_TAC o (CONJUNCT1 o (REWRITE_RULE [complex_embeddings, IN_ELIM_THM]))) THEN DISCH_THEN (SUBST1_TAC o (MATCH_MP RING_HOMOMORPHISM_0)) THEN REWRITE_TAC [COMPLEX_RING_CLAUSES, COMPLEX_NORM_0] THEN REAL_ARITH_TAC, ALL_TAC] THEN EXISTS_TAC (← q r"ring_order k (x:A)") THEN ASM_SIMP_TAC [RING_POW_RING_ORDER, r1] THEN MATCH_MP_TAC RING_ORDER_NONZERO_MULTSYS THEN EXISTS_TAC (← q r"IMAGE (ring_pow k (x:A)) (:num)") THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_REGULAR, FIELD_IMP_INTEGRAL_DOMAIN] THEN REWRITE_TAC [ring_multsys, SUBSET, FORALL_IN_IMAGE, IN_UNIV, IN_IMAGE] THEN ASM_SIMP_TAC [RING_POW] THEN REPEAT CONJ_TAC THENL [MESON_TAC [ring_pow], ASM_MESON_TAC [RING_POW_ADD], MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{y | y IN ring_carrier(ring_of_integers k) /\
             !g. g IN complex_embeddings k
                 ==> norm((g:A->complex) y) <= &1}") THEN ASM_SIMP_TAC [RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_UNIV, IN_ELIM_THM] THEN X_GEN_TAC (← q r"m:num") THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"x:A"), (← q r"m:num")] RING_POW) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], X_GEN_TAC (← q r"h:A->complex") THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o (CONJUNCT1 o (REWRITE_RULE [complex_embeddings, IN_ELIM_THM]))) THEN DISCH_THEN (MP_TAC o (MATCH_MP RING_HOMOMORPHISM_POW)) THEN ASM_SIMP_TAC [COMPLEX_RING_POW, COMPLEX_NORM_POW, REAL_POW_ONE, REAL_LE_REFL]], EXISTS_TAC (← q r"1") THEN ASM_SIMP_TAC [RING_POW_1]])

  let NUMBER_FIELD_ROOTS_OF_UNITY_FINITE ← prove
    r"!k:A ring.
        number_field k
        ==> FINITE {x | x IN ring_carrier k /\
                        ?n. 1 <= n /\ ring_pow k x n = ring_1 k}"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{x | x IN ring_carrier(ring_of_integers k) /\
         !g. g IN complex_embeddings k ==> norm((g:A->complex) x) <= &1}") THEN ASM_SIMP_TAC [RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"n:num") STRIP_ASSUME_TAC)) THEN CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC [COMPLEX_EMBEDDINGS_ROOT_OF_UNITY, REAL_LE_REFL]] THEN REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM] THEN MATCH_MP_TAC INTEGRAL_ELEMENT_FROM_RELATION THEN MAP_EVERY EXISTS_TAC [(← q r"n:num"), (← q r"\i:num. if i = 0 then -- &1 else &0:int")] THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, INTEGER_RING, IN_UNIV] THEN SUBGOAL_THEN (← q r"ring_sum k {i | i < n}
      (\i. ring_mul k (ring_of_int k (if i = 0 then -- &1 else &0))
                      (ring_pow k (x:A) i)) =
    ring_sum k {i | i < n} (\i. if i = 0 then ring_neg k (ring_1 k)
                                else ring_0 k)") SUBST1_TAC THENL [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"i:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [RING_OF_INT_0, RING_OF_INT_CASES, RING_OF_NUM_1, ring_pow, RING_MUL_LZERO, RING_POW, RING_MUL_RID, RING_NEG, RING_1], ASM_SIMP_TAC [RING_SUM_DELTA, IN_ELIM_THM, LE_1, RING_NEG, RING_1, RING_ADD_RNEG]])

  let NUMBER_FIELD_UNIT_GROUP_FINITELY_GENERATED ← prove
    r"!k:A ring.
        number_field k
        ==> finitely_generated_group(unit_group(ring_of_integers k))"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN MATCH_MP_TAC (← ISPECL [(← q r"unit_group(ring_of_integers k):A group"), (← q r"complex_embeddings (k:A ring)"), (← q r"\(g:A->complex) (u:A). norm(g u)")] FINITELY_GENERATED_ABELIAN_GROUP_DISCRETE) THEN ASM_SIMP_TAC [ABELIAN_UNIT_GROUP, FINITE_COMPLEX_EMBEDDINGS, UNIT_GROUP, IN_ELIM_THM, RING_OF_INTEGERS] THEN SUBGOAL_THEN (← q r"!u. ring_unit (ring_of_integers k) u
        ==> (u:A) IN ring_carrier(ring_of_integers k) /\
            u IN ring_carrier k /\ ~(u = ring_0 k)") ASSUME_TAC THENL [X_GEN_TAC (← q r"u:A") THEN DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_UNIT_IN_CARRIER)) THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], DISCH_TAC] THEN UNDISCH_TAC (← q r"ring_unit (ring_of_integers k) (u:A)") THEN ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [(← GSYM (← CONJUNCT1 RING_OF_INTEGERS))] THEN ASM_SIMP_TAC [RING_UNIT_0, INTEGRAL_DOMAIN_RING_OF_INTEGERS, INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING], ALL_TAC] THEN REPEAT CONJ_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"i:A->complex")] COMPLEX_EMBEDDINGS_MONOMORPHISM) THEN ASM_REWRITE_TAC [RING_MONOMORPHISM_ALT, COMPLEX_NORM_NZ] THEN REWRITE_TAC [COMPLEX_RING_CLAUSES] THEN ASM_MESON_TAC [], REWRITE_TAC [complex_embeddings, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"complex_ring"), (← q r"i:A->complex")] RING_HOMOMORPHISM_MUL) THEN ASM_SIMP_TAC [COMPLEX_RING_CLAUSES, COMPLEX_NORM_MUL], X_GEN_TAC (← q r"b:real") THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{x | x IN ring_carrier(ring_of_integers k) /\
           !g. g IN complex_embeddings k ==> norm((g:A->complex) x) <= b}") THEN ASM_SIMP_TAC [RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC []])

  let NUMBER_FIELD_UNITS_GENERATORS ← prove
    r"!k:A ring.
        number_field k
        ==> ?t. FINITE t /\
                (!u. u IN t ==> ring_unit (ring_of_integers k) u) /\
                !u. ring_unit (ring_of_integers k) u
                    ==> ?n. u = ring_product k t (\v. ring_pow k v (n v))"
    (GEN_TAC THEN DISCH_THEN (MP_TAC o (MATCH_MP NUMBER_FIELD_UNIT_GROUP_FINITELY_GENERATED)) THEN REWRITE_TAC [FINITELY_GENERATED_UNIT_GROUP] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"t:A->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"u:A") THEN DISCH_TAC THEN FIRST_X_ASSUM ((X_CHOOSE_TAC (← q r"n:A->num")) o (← do let c := (← ASSUME (← q r"ring_unit (ring_of_integers k) (u:A)")); pure (fun th => MATCH_MP th c))) THEN EXISTS_TAC (← q r"n:A->num") THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN REWRITE_TAC [ring_of_integers, RING_PRODUCT_SUBRING_GENERATED_GEN] THEN REWRITE_TAC [(← GSYM ring_of_integers)] THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC (← q r"v:A") THEN EQ_TAC THEN SIMP_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"v:A"), (← q r"(n:A->num) v")] RING_POW) THEN ASM_SIMP_TAC [RING_OF_INTEGERS, RING_UNIT_IN_CARRIER])

  -- @@RETURN BEGIN
  return { complex_embeddings, COMPLEX_MATRIX_SOLVE, COMPLEX_PRIME_SUBFIELD,
           COMPLEX_POLYFUN_MONIC_COEFF_BOUND, COMPLEX_POLYFUN_MONIC_INTEGER_ROOTS_FINITE,
           COMPLEX_EMBEDDINGS_RESTRICTION, COMPLEX_EMBEDDINGS_MONOMORPHISM,
           COMPLEX_EMBEDDINGS_EXTENSIONS, COMPLEX_EMBEDDINGS_NONEMPTY,
           COMPLEX_EMBEDDINGS_HAS_SIZE, FINITE_COMPLEX_EMBEDDINGS,
           COMPLEX_EMBEDDINGS_CONJUGATES, RING_OF_INTEGERS_CONJUGATES_POLYFUN,
           RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE, COMPLEX_EMBEDDINGS_ROOT_OF_UNITY,
           RING_OF_INTEGERS_ROOT_OF_UNITY, NUMBER_FIELD_ROOTS_OF_UNITY_FINITE,
           NUMBER_FIELD_UNIT_GROUP_FINITELY_GENERATED, NUMBER_FIELD_UNITS_GENERATORS }
  -- @@RETURN END

end HolANT.ComplexEmbeddings
