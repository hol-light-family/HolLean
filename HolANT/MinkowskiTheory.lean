/- ========================================================================= -/
/- ANT: Minkowski theory of a number field k with ring of integers ...     -/
/- ========================================================================= -/
/- File: HolANT/MinkowskiTheory.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/minkowski_theory.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antminkowskitheorydiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/isum.ml, Library/products.ml, Library/frag.ml, Library/grouptheory.ml, ANT/algmisc.ml, ANT/ideal_arith.ml, ANT/integral.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/zlattice.ml, Library/floor.ml, ANT/linear_forms.ml, ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/classgroup.ml, ANT/classgroup_group.ml, ANT/prime_split.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/finite_field_trace.ml, ANT/ramification.ml, ANT/quadratic.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/nf_valuation.ml, ANT/relative_split.ml, ANT/integrality.ml, Library/ring_groups.ml, ANT/fingen_group.ml, Multivariate/misc.ml, Multivariate/metric.ml, Multivariate/homology.ml, Multivariate/vectors.ml, Multivariate/determinants.ml, Multivariate/topology.ml, Multivariate/convex.ml, Multivariate/paths.ml, Multivariate/polytope.ml, Multivariate/degree.ml, Multivariate/derivatives.ml, Multivariate/integration.ml, Multivariate/measure.ml, Multivariate/complex_algebra.ml, Multivariate/complexes.ml, Multivariate/canal.ml, Multivariate/transcendentals.ml, Multivariate/realanalysis.ml, Multivariate/moretop.ml, Multivariate/cauchy.ml, Multivariate/complex_ring.ml, Multivariate/complex_field.ml, ANT/complex_embeddings.ml, ANT/power_basis.ml, ANT/infinite_places.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.MinkowskiTheory fills them).

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
import HolLibrary.Frag
import HolLibrary.GroupTheory
import HolANT.Algmisc
import HolANT.IdealArith
import HolANT.Integral
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.IdealNorm
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.LinearForms
import HolANT.Numfield
import HolANT.RingOfIntegers
import HolANT.NormIndex
import HolANT.Classgroup
import HolANT.ClassgroupGroup
import HolANT.PrimeSplit
import HolANT.Discriminant
import HolANT.TraceForm
import HolANT.FiniteFieldTrace
import HolANT.Ramification
import HolANT.Quadratic
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.NfValuation
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
open HolANT.IdealArith
open HolANT.Integral
open HolANT.Dedekind
open HolANT.DedekindStruct
open HolANT.IdealNorm
open HolANT.Zlattice
open HolANT.LinearForms
open HolANT.Numfield
open HolANT.RingOfIntegers
open HolANT.NormIndex
open HolANT.Classgroup
open HolANT.ClassgroupGroup
open HolANT.PrimeSplit
open HolANT.Discriminant
open HolANT.TraceForm
open HolANT.FiniteFieldTrace
open HolANT.Ramification
open HolANT.Quadratic
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.NfValuation
open HolANT.RelativeSplit
open HolANT.Integrality
open HolANT.FingenGroup
open HolANT.ComplexEmbeddings
open HolANT.PowerBasis
open HolANT.InfinitePlaces

namespace HolANT.MinkowskiTheory

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ARITH ARITH_EQ CARD_EQ_0 CARD_LE_2 CARD_SUBSET CLASS_GROUP CLASS_GROUP_MUL
   CNJ_ADD CNJ_CX CNJ_II CNJ_MUL CNJ_SUB CNJ_VSUM COMPLEX_ADD_RDISTRIB
   COMPLEX_EMBEDDINGS_CNJ COMPLEX_EMBEDDINGS_CNJ_CNJ COMPLEX_EMBEDDINGS_HAS_SIZE
   COMPLEX_EMBEDDINGS_NONEMPTY COMPLEX_EMBEDDINGS_NORM_EQ COMPLEX_EQ
   COMPLEX_MUL_CNJ COMPLEX_MUL_LZERO COMPLEX_NORM_CNJ COMPLEX_NORM_CX
   COMPLEX_NORM_LE_RE_IM COMPLEX_NORM_MUL COMPLEX_NORM_POW COMPLEX_POW_II_2
   COMPLEX_POW_ONE COMPLEX_RING_CLAUSES COMPLEX_RING_OF_INT COMPLEX_RING_SUM
   COMPLEX_VEC_0 CX_ADD CX_INJ CX_MUL CX_NEG CX_POW
   DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE DEDEKIND_IDEAL_PROD_CANCEL
   DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES DEDEKIND_IMP_INTEGRAL_DOMAIN
   DEDEKIND_IMP_NOETHERIAN DEDEKIND_RING_OF_INTEGERS DIVIDES_0 DIVIDES_LE
   EQ_SYM_EQ EQ_TRANS ETA_AX EXISTS_UNIQUE_THM EXTENSION
   FINITE_COMPLEX_EMBEDDINGS FINITE_DELETE FINITE_EMPTY FINITE_IMAGE_INJ_EQ
   FINITE_INSERT FINITE_NUMSEG_LT FINITE_SUBSET FORALL_AND_THM FORALL_IN_GSPEC
   FORALL_IN_IMAGE FORALL_UNWIND_THM2 FREE_BASIS_IN_CARRIER
   FREE_BASIS_QUOTIENT_RING_HAS_SIZE GROUP_ID_SUBGROUP GROUP_MUL_SUBGROUP
   HAS_SIZE HAS_SIZE_INDEX IDEAL_CLASS_EQ IDEAL_CLASS_EQ_ID
   IDEAL_CLASS_IN_CLASS_GROUP IDEAL_GENERATED_MINIMAL IDEAL_NORM_CARRIER
   IDEAL_NORM_IN_IDEAL IDEAL_NORM_POS IDEAL_NORM_SUBSET_DIVIDES IDEAL_PROD_ASSOC
   IDEAL_PROD_CARRIER IDEAL_PROD_COMM IDEAL_PROD_EQ_ZERO IDEAL_PROD_SUBSET_RIGHT
   IM IMP_CONJ IM_ADD IM_CNJ IM_CX IM_II IM_MUL_CX IM_SUB IM_VSUM INFINITE
   INTEGER_RING INTEGRAL_DOMAIN_RING_OF_INTEGERS INTEGRAL_DOMAIN_UNIT_IDEAL
   INT_ABS_NUM INT_ABS_POS INT_COSETS_MATRIX_IMAGE INT_DIVIDES_RABS
   INT_LATTICE_FULL_RANK INT_LATTICE_MATRIX_IMAGE INT_MATRIX_IMAGE_IN
   INT_MATRIX_IMAGE_INJECTIVE INT_MUL_RZERO INT_NOT_LE INT_OF_NUM_EQ
   INT_OF_NUM_OF_INT INT_REM_EQ INT_SUB_REFL IN_DELETE IN_ELIM_THM
   IN_IDEAL_CLASS IN_IDEAL_GENERATED_SELF IN_IMAGE IN_INSERT IN_RING_IDEAL_0
   IN_RING_IDEAL_RMUL IN_RING_IDEAL_SUB IN_SING IN_SUBRING_MUL IN_UNIV ISUM_0
   LE_1 MAXIMAL_IMP_PRIME_IDEAL MAXIMAL_IMP_PROPER_IDEAL MAXIMAL_IMP_RING_IDEAL
   MAXIMAL_SUPERIDEAL_EXISTS MEMBER_NOT_EMPTY MINKOWSKI_LINEAR_FORMS MONO_EXISTS
   NOETHERIAN_RING_INDUCT NORM_POS_LE NOT_FORALL_THM NOT_IMP NOT_IN_EMPTY
   NUMBER_FIELD_DEGREE_EQ_1 NUMBER_FIELD_DEGREE_POS
   NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS NUMBER_FIELD_DISCRIMINANT_NONZERO
   NUMBER_FIELD_IDEAL_NORM_MUL_Q NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS
   NUMBER_FIELD_IMP_FIELD NUMBER_FIELD_RAMIFIED_DISCRIMINANT NUM_OF_INT_OF_NUM
   PRIME_FACTOR : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (PRIME_IMP_RING_IDEAL PRODUCT_CONST PRODUCT_DELETE PRODUCT_IMAGE PRODUCT_LE
   PRODUCT_MUL PRODUCT_POS_LT PRODUCT_RESTRICT_SET PROPER_IDEAL_ALT PSUBSET
   QUADRATIC_FIELD_DISCRIMINANT QUADRATIC_FIELD_SQRT RE REAL_ABS_MUL REAL_ABS_NZ
   REAL_ADD_LDISTRIB REAL_EQ_ADD_LCANCEL REAL_EQ_ADD_RCANCEL REAL_EQ_INV2
   REAL_INV_LE_1 REAL_LET_TRANS REAL_LE_ADD REAL_LE_ANTISYM REAL_LE_INV
   REAL_LE_INV_EQ REAL_LE_LMUL REAL_LE_LMUL_EQ REAL_LE_MUL2 REAL_LE_POW2
   REAL_LE_REFL REAL_LE_TRANS REAL_LT_IMP_LE REAL_LT_INV_EQ REAL_LT_MUL
   REAL_LT_RMUL REAL_MUL_AC REAL_MUL_LID REAL_MUL_RID REAL_MUL_RINV REAL_MUL_SYM
   REAL_NOT_LE REAL_NOT_LT REAL_OF_INT_CLAUSES REAL_OF_NUM_EQ REAL_OF_NUM_LE
   REAL_OF_NUM_LT REAL_OF_NUM_MUL REAL_POS REAL_POW_EQ REAL_POW_INV REAL_POW_LE
   REAL_POW_LE2 REAL_POW_LE_1 REAL_POW_LT REAL_POW_NZ REAL_POW_ONE REAL_POW_POW
   REAL_POW_ROOT REAL_RING_CLAUSES REAL_RING_OF_INT REAL_RING_SUM RESTRICTION
   RE_ADD RE_CNJ RE_CX RE_II RE_MUL_CX RE_SUB RE_VSUM RIGHT_EXISTS_IMP_THM
   RIGHT_FORALL_IMP_THM RING_DET_EQ RING_DET_HOMOMORPHISM RING_DET_I
   RING_DET_MUL RING_DET_SING RING_HOMOMORPHISM_1 RING_HOMOMORPHISM_CNJ
   RING_HOMOMORPHISM_INTEGER_RING_OF_INT RING_HOMOMORPHISM_MUL
   RING_HOMOMORPHISM_RING_OF_INT RING_HOMOMORPHISM_SUM RING_IDEAL_CARRIER
   RING_IDEAL_IDEAL_GENERATED RING_IDEAL_IDEAL_PROD RING_IDEAL_IMP_SUBSET
   RING_INT_LINCOMB RING_MUL RING_MUL_RID RING_OF_INT RING_OF_INTEGERS
   RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE RING_OF_INTEGERS_FINITE_QUOTIENT
   RING_OF_INTEGERS_FREE RING_OF_INTEGERS_PRIME_SUBFIELD
   RING_OF_INTEGERS_SUBRING RING_OF_INTEGERS_SUBSET RING_OF_INT_1
   RING_OF_INT_EQ_0_CHAR_0 RING_OF_INT_IN_RING_OF_INTEGERS RING_OF_INT_OF_NUM
   RING_SUM RING_SUM_EQ RING_SUM_RING_OF_INTEGERS RING_SUM_SING ROOT_POS_LT
   SING_SUBSET SKOLEM_THM SQRT_1 SQRT_POS_LT SQRT_UNIQUE SUBGROUP_GENERATED_INC
   SUBGROUP_GENERATED_MONO SUBGROUP_GENERATED_SUPERSET SUBSET SUBSET_UNIV
   SUM_ADD SUM_EQ SUM_RMUL SUM_SWAP TRIVIAL_CLASS_GROUP
   TRIVIAL_GROUP_SUBGROUP_GENERATED_TRIVIAL VSUM_ADD VSUM_COMPLEX_LMUL
   VSUM_COMPLEX_RMUL VSUM_DELTA VSUM_EQ complex_embeddings complex_mul
   free_basis ideal_classes ideal_norm int_isum int_lattice int_mul_th
   num_INFINITE num_divides number_field o_THM principal_ideal ring_homomorphism
   ring_ideal squarefree : thm)
  deriving Inhabited

/-- What minkowski_theory.ml uses from Session besides theorems. -/
structure MinkowskiTheoryDeps where
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
/- minkowski_theory.ml phrases from line 97 to 614                        -/
/- ---------------------------------------------------------------------- -/

structure MinkowskiTheory01 where
  -- @@FIELDS
  NUMBER_FIELD_IDEAL_MINKOWSKI_LINEAR_FORMS : thm
  NUMBER_FIELD_IDEAL_MINKOWSKI : thm
  NUMBER_FIELD_IDEAL_MINKOWSKI_NORM : thm
  NUMBER_FIELD_IDEAL_CLASS_MINKOWSKI : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupMinkowskiTheory01 [HolBase] (D : MinkowskiTheoryDeps) :
    ExceptT String IO MinkowskiTheory01 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, COMPLEX_RING, MESON, MESON_TAC, REAL_ARITH,
        REAL_ARITH_TAC, REAL_RING, SET_RULE, SET_TAC, TAUT, .. } := D
  let { ARITH_EQ, CNJ_ADD, CNJ_CX, CNJ_II, CNJ_MUL, CNJ_SUB, COMPLEX_ADD_RDISTRIB,
        COMPLEX_EMBEDDINGS_CNJ, COMPLEX_EMBEDDINGS_CNJ_CNJ,
        COMPLEX_EMBEDDINGS_HAS_SIZE, COMPLEX_EMBEDDINGS_NONEMPTY, COMPLEX_EQ,
        COMPLEX_MUL_CNJ, COMPLEX_MUL_LZERO, COMPLEX_NORM_CNJ, COMPLEX_NORM_CX,
        COMPLEX_NORM_LE_RE_IM, COMPLEX_NORM_MUL, COMPLEX_NORM_POW, COMPLEX_POW_II_2,
        COMPLEX_RING_CLAUSES, COMPLEX_RING_OF_INT, COMPLEX_RING_SUM, COMPLEX_VEC_0,
        CX_ADD, CX_INJ, CX_MUL, CX_NEG, CX_POW, DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE,
        DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES, DEDEKIND_IMP_INTEGRAL_DOMAIN,
        DEDEKIND_RING_OF_INTEGERS, EQ_SYM_EQ, EQ_TRANS, EXISTS_UNIQUE_THM, EXTENSION,
        FINITE_NUMSEG_LT, FREE_BASIS_IN_CARRIER, FREE_BASIS_QUOTIENT_RING_HAS_SIZE,
        HAS_SIZE, HAS_SIZE_INDEX, IDEAL_GENERATED_MINIMAL, IDEAL_NORM_IN_IDEAL,
        IDEAL_NORM_POS, IDEAL_PROD_ASSOC, IDEAL_PROD_COMM, IDEAL_PROD_EQ_ZERO, IM,
        IM_ADD, IM_CNJ, IM_CX, IM_II, IM_MUL_CX, IM_SUB, IM_VSUM, INTEGER_RING,
        INT_ABS_NUM, INT_ABS_POS, INT_COSETS_MATRIX_IMAGE, INT_LATTICE_FULL_RANK,
        INT_LATTICE_MATRIX_IMAGE, INT_MATRIX_IMAGE_IN, INT_MATRIX_IMAGE_INJECTIVE,
        INT_MUL_RZERO, INT_OF_NUM_EQ, INT_OF_NUM_OF_INT, INT_SUB_REFL, IN_ELIM_THM,
        IN_IDEAL_CLASS, IN_IDEAL_GENERATED_SELF, IN_IMAGE, IN_RING_IDEAL_0,
        IN_RING_IDEAL_RMUL, IN_RING_IDEAL_SUB, IN_SUBRING_MUL, IN_UNIV, ISUM_0, LE_1,
        MEMBER_NOT_EMPTY, MINKOWSKI_LINEAR_FORMS, MONO_EXISTS, NORM_POS_LE,
        NUMBER_FIELD_DEGREE_POS, NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS,
        NUMBER_FIELD_DISCRIMINANT_NONZERO, NUMBER_FIELD_IDEAL_NORM_MUL_Q,
        NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS, .. } := D.core1
  let { PRODUCT_CONST, PRODUCT_IMAGE, PRODUCT_LE, RE, REAL_ABS_MUL, REAL_ABS_NZ,
        REAL_ADD_LDISTRIB, REAL_LE_LMUL_EQ, REAL_LE_REFL, REAL_LE_TRANS,
        REAL_LT_IMP_LE, REAL_LT_MUL, REAL_MUL_AC, REAL_MUL_SYM, REAL_OF_INT_CLAUSES,
        REAL_OF_NUM_LT, REAL_OF_NUM_MUL, REAL_POS, REAL_POW_EQ, REAL_POW_ONE,
        REAL_POW_ROOT, REAL_RING_CLAUSES, REAL_RING_OF_INT, REAL_RING_SUM, RESTRICTION,
        RE_ADD, RE_CNJ, RE_CX, RE_II, RE_MUL_CX, RE_SUB, RE_VSUM, RIGHT_EXISTS_IMP_THM,
        RING_DET_EQ, RING_DET_HOMOMORPHISM, RING_DET_I, RING_DET_MUL,
        RING_HOMOMORPHISM_CNJ, RING_HOMOMORPHISM_INTEGER_RING_OF_INT,
        RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_RING_OF_INT, RING_HOMOMORPHISM_SUM,
        RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_PROD, RING_IDEAL_IMP_SUBSET,
        RING_INT_LINCOMB, RING_MUL, RING_OF_INT, RING_OF_INTEGERS,
        RING_OF_INTEGERS_FINITE_QUOTIENT, RING_OF_INTEGERS_FREE,
        RING_OF_INTEGERS_SUBRING, RING_OF_INTEGERS_SUBSET,
        RING_OF_INT_IN_RING_OF_INTEGERS, RING_OF_INT_OF_NUM, RING_SUM, RING_SUM_EQ,
        RING_SUM_RING_OF_INTEGERS, ROOT_POS_LT, SING_SUBSET, SKOLEM_THM, SQRT_POS_LT,
        SQRT_UNIQUE, SUBSET, SUBSET_UNIV, SUM_ADD, SUM_EQ, SUM_RMUL, SUM_SWAP,
        VSUM_ADD, VSUM_DELTA, VSUM_EQ, complex_embeddings, complex_mul, free_basis,
        ideal_norm, int_isum, int_lattice, int_mul_th, o_THM, ring_homomorphism,
        ring_ideal, .. } := D.core2
  -- @@SCOPE END

  let NUMBER_FIELD_IDEAL_MINKOWSKI_LINEAR_FORMS ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let p1 ← prove r"ring_homomorphism(real_ring,complex_ring) Cx" (REWRITE_TAC [ring_homomorphism, COMPLEX_RING_CLAUSES, REAL_RING_CLAUSES, SUBSET_UNIV, IN_UNIV, CX_ADD, CX_MUL, CX_NEG])
    let cx_hom := p1
    let p2 ← prove r"!z. (Cx(&1 / &2) * (Cx(&1) - ii)) * z +
         (Cx(&1 / &2) * (Cx(&1) + ii)) * cnj z =
         Cx(Re z + Im z)" (REWRITE_TAC [COMPLEX_EQ, RE_ADD, IM_ADD, complex_mul, RE, IM, RE_CX, IM_CX, RE_II, IM_II, RE_SUB, IM_SUB, RE_CNJ, IM_CNJ] THEN REAL_ARITH_TAC)
    let reim := p2
    let q3 ← q r"vsum s (\l:K. (if l = i then a * X i else vec 0) +
                    (if l = i' then b * (X:K->complex) i' else vec 0))"
    let p4 ← prove r"!s i i' a b (X:K->complex).
          FINITE s /\ i IN s /\ i' IN s
          ==> vsum s (\l. ((if l = i then a else Cx(&0)) +
                           (if l = i' then b else Cx(&0))) * X l) =
              a * X i + b * X i'" (REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS q3 THEN CONJ_TAC THENL [MATCH_MP_TAC VSUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC [COMPLEX_ADD_RDISTRIB] THEN BINOP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [COMPLEX_VEC_0, COMPLEX_MUL_LZERO], ASM_SIMP_TAC [VSUM_ADD, VSUM_DELTA]])
    let vsum_delta2 := p4
    let q5 ← q r"Q:bool"
    let q6 ← q r"P:bool"
    let p7 ← prove r"!P Q. (Cx(&1 / &2) * (Cx(&1) - ii)) *
           ((if P then cnj(Cx(&1 / &2) * (Cx(&1) - ii)) else Cx(&0)) +
            (if Q then cnj(Cx(&1 / &2) * (Cx(&1) + ii)) else Cx(&0))) +
           (Cx(&1 / &2) * (Cx(&1) + ii)) *
           ((if Q then cnj(Cx(&1 / &2) * (Cx(&1) - ii)) else Cx(&0)) +
            (if P then cnj(Cx(&1 / &2) * (Cx(&1) + ii)) else Cx(&0))) =
           if P then Cx(&1) else Cx(&0)" (REWRITE_TAC [CNJ_MUL, CNJ_SUB, CNJ_ADD, CNJ_CX, CNJ_II] THEN REPEAT GEN_TAC THEN ASM_CASES_TAC q6 THEN ASM_CASES_TAC q5 THEN ASM_REWRITE_TAC [] THEN MP_TAC COMPLEX_POW_II_2 THEN CONV_TAC COMPLEX_RING)
    let bb := p7
    let q8 ← q r"2"
    let v9 ← GSYM CX_POW
    let q10 ← q r"B:K->K->complex"
    let q11 ← q r"s:K->bool"
    let q12 ← q r"cnj"
    let q13 ← q r"complex_ring"
    let q14 ← q r"complex_ring"
    let v15 ← ISPECL [q14, q13, q12, q11, q10] RING_DET_HOMOMORPHISM
    let q16 ← q r"l:K"
    let q17 ← q r"i:K"
    let v18 ← ISPECL [q17, q16] EQ_SYM_EQ
    let q19 ← q r"!b x y. cnj(if b then x else y) = if b then cnj x else cnj y"
    let r20 ← MESON [] q19
    let q21 ← q r"l:K"
    let q22 ← q r"i:K"
    let q23 ← q r"s:K->bool"
    let q24 ← q r"complex_ring"
    let v25 ← ISPECL [q24, q23] RING_DET_I
    let q26 ← q r"ring_mul complex_ring (ring_det complex_ring s B)
        (ring_det complex_ring s (\i l:K. cnj(B i l))) = Cx(&1)"
    let q27 ← q r"x:real = &1 ==> x * y = y"
    let r28 ← REAL_RING q27
    let q29 ← q r"ring_det complex_ring s (\i j:K. Cx(Re(M i j) + Im(M i j))) =
      ring_mul complex_ring (ring_det complex_ring s B)
        (ring_det complex_ring s M)"
    let q30 ← q r"!X:K->complex i. i IN s
          ==> vsum s (\l. B i l * X l) =
              (Cx(&1 / &2) * (Cx(&1) - ii)) * X i +
              (Cx(&1 / &2) * (Cx(&1) + ii)) * X((p:K->K) i)"
    let q31 ← q r"B = \i l:K. (if l = i then Cx(&1 / &2) * (Cx(&1) - ii)
                             else Cx(&0)) +
                            (if l = p i then Cx(&1 / &2) * (Cx(&1) + ii)
                             else Cx(&0))"
    let p32 ← prove r"!s (p:K->K) (M:K->K->complex).
          FINITE s /\ (!i. i IN s ==> p i IN s /\ p(p i) = i) /\
          (!i j. i IN s /\ j IN s ==> M (p i) j = cnj(M i j))
          ==> norm(ring_det complex_ring s (\i j. Cx(Re(M i j) + Im(M i j)))) =
              norm(ring_det complex_ring s M)" (REPEAT STRIP_TAC THEN ABBREV_TAC q31 THEN SUBGOAL_THEN q30 ASSUME_TAC THENL [REPEAT STRIP_TAC THEN EXPAND_TAC "B" THEN MATCH_MP_TAC vsum_delta2 THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN q29 SUBST1_TAC THENL [wPart rand (rand o rand) RING_DET_MUL THEN ASM_REWRITE_TAC [COMPLEX_RING_CLAUSES, IN_UNIV] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_DET_EQ THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [COMPLEX_RING_SUM] THEN REWRITE_TAC [reim], ALL_TAC] THEN REWRITE_TAC [COMPLEX_RING_CLAUSES, COMPLEX_NORM_MUL] THEN MATCH_MP_TAC r28 THEN SUBGOAL_THEN q26 MP_TAC THENL [wPart lhand (rand o rand) RING_DET_MUL THEN ASM_REWRITE_TAC [COMPLEX_RING_CLAUSES, IN_UNIV] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC v25 THEN ASM_REWRITE_TAC [COMPLEX_RING_CLAUSES] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_DET_EQ THEN MAP_EVERY X_GEN_TAC [q22, q21] THEN STRIP_TAC THEN ASM_SIMP_TAC [COMPLEX_RING_SUM] THEN EXPAND_TAC "B" THEN REWRITE_TAC [CNJ_ADD, CNJ_CX, r20] THEN ASM_SIMP_TAC [] THEN SUBST1_TAC v18 THEN REWRITE_TAC [bb], ALL_TAC] THEN MP_TAC v15 THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_CNJ, COMPLEX_RING_CLAUSES, IN_UNIV] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [COMPLEX_MUL_CNJ, v9, CX_INJ] THEN DISCH_TAC THEN MATCH_MP_TAC REAL_POW_EQ THEN EXISTS_TAC q8 THEN ASM_REWRITE_TAC [NORM_POS_LE, REAL_POS, REAL_POW_ONE, ARITH_EQ])
    let det_reim := p32
    let v33 ← GSYM COMPLEX_NORM_CX
    let v34 ← GSYM COMPLEX_NORM_POW
    let v35 ← GSYM SQRT_UNIQUE
    let q36 ← q r"i:num"
    let q37 ← q r"\i j. (e:num->A->complex) i ((w:num->A) j)"
    let q38 ← q r"p:num->num"
    let q39 ← q r"{i:num | i < n}"
    let v40 ← ISPECL [q39, q38, q37] det_reim
    let v41 ← BETA_RULE v40
    let q42 ← q r"\i j. Re((e:num->A->complex) i ((w:num->A) j)) + Im(e i (w j))"
    let q43 ← q r"{i:num | i < n}"
    let q44 ← q r"Cx"
    let q45 ← q r"complex_ring"
    let q46 ← q r"real_ring"
    let v47 ← ISPECL [q46, q45, q44, q43, q42] RING_DET_HOMOMORPHISM
    let v48 ← BETA_RULE v47
    let v49 ← GSYM COMPLEX_NORM_CX
    let q50 ← q r"k:A ring"
    let v51 ← ISPEC q50 RING_OF_INTEGERS_SUBSET
    let q52 ← q r"!j. j < n ==> (w:num->A) j IN ring_carrier k"
    let v53 ← GSYM SKOLEM_THM
    let q54 ← q r"?p. !i. i < n
              ==> p i < n /\
                  (e:num->A->complex)(p i) =
                  RESTRICTION (ring_carrier k) (cnj o e i)"
    let p55 ← prove r"!k n w (e:num->A->complex).
          number_field k /\
          free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w /\
          (!i. i < n ==> e i IN complex_embeddings k) /\
          (!i j. i < n /\ j < n /\ e i = e j ==> i = j) /\
          (!g. g IN complex_embeddings k ==> ?i. i < n /\ e i = g)
          ==> abs(ring_det real_ring {i | i < n}
                    (\i j. Re(e i (w j)) + Im(e i (w j)))) =
              sqrt(abs(real_of_int(number_field_discriminant k)))" (REPEAT STRIP_TAC THEN SUBGOAL_THEN q54 STRIP_ASSUME_TAC THENL [REWRITE_TAC [v53, RIGHT_EXISTS_IMP_THM] THEN ASM_MESON_TAC [COMPLEX_EMBEDDINGS_CNJ], ALL_TAC] THEN SUBGOAL_THEN q52 ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP FREE_BASIS_IN_CARRIER)) THEN MP_TAC v51 THEN SET_TAC [], ALL_TAC] THEN REWRITE_TAC [v49] THEN MP_TAC v48 THEN REWRITE_TAC [cx_hom, REAL_RING_CLAUSES, IN_UNIV, FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC v41 THEN ANTS_TAC THENL [REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN CONJ_TAC THENL [X_GEN_TAC q36 THEN DISCH_TAC THEN ASM_SIMP_TAC [] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC [] THEN ASM_MESON_TAC [COMPLEX_EMBEDDINGS_CNJ_CNJ], ASM_SIMP_TAC [RESTRICTION, o_THM]], DISCH_THEN SUBST1_TAC] THEN MATCH_MP_TAC v35 THEN REWRITE_TAC [NORM_POS_LE] THEN REWRITE_TAC [v34, v33] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS THEN ASM_REWRITE_TAC [])
    let det_disc := p55
    let q56 ← q r"(x:A) = y ==> P /\ x IN j ==> y IN j"
    let r57 ← SET_RULE q56
    let q58 ← q r"(\i. if i IN {i:num | i < n}
             then isum {l | l < n} (\l. (C:num->num->int) i l * z l)
             else &0) IN L"
    let q59 ← q r"z:num->int"
    let q60 ← q r"num_of_int(abs(ring_det integer_ring {i:num | i < n}
                                      (C:num->num->int)))"
    let q61 ← q r"j:A->bool"
    let q62 ← q r"w:num->A"
    let q63 ← q r"n:num"
    let q64 ← q r"r:A ring"
    let v65 ← ISPECL [q64, q63, q62, q61, q60] FREE_BASIS_QUOTIENT_RING_HAS_SIZE
    let q69 ← q r"1 <= n ==> ~(n = 0)"
    let r70 ← ARITH_RULE q69
    let q71 ← q r"&(ideal_norm r (j:A->bool)):int"
    let q72 ← q r"L:(num->int)->bool"
    let q73 ← q r"C:num->num->int"
    let q74 ← q r"{i:num | i < n}"
    let v75 ← ISPECL [q74, q73] INT_COSETS_MATRIX_IMAGE
    let q76 ← q r"C:num->num->int"
    let q77 ← q r"C:num->num->int"
    let q78 ← q r"L:(num->int)->bool"
    let q79 ← q r"{i:num | i < n}"
    let v80 ← ISPECL [q79, q78] INT_LATTICE_MATRIX_IMAGE
    let v81 ← GSYM RING_OF_INT_OF_NUM
    let q82 ← q r"w:num->A"
    let q83 ← q r"{i:num | i < n}"
    let q84 ← q r"r:A ring"
    let v85 ← ISPECL [q84, q83, q82] RING_INT_LINCOMB
    let q86 ← q r"int_lattice {i:num | i < n} L /\
      !x. (!i. ~(i IN {i:num | i < n}) ==> x i = &0)
          ==> (\i. &(ideal_norm r (j:A->bool)) * x i) IN L"
    let q87 ← q r"L = {z | (!i. ~(i < n) ==> z i = &0) /\
                         ring_sum r {i | i < n}
                           (\i. ring_mul r (ring_of_int r (z i)) ((w:num->A) i))
                         IN (j:A->bool)}"
    let p88 ← prove r"!r:A ring n w j.
          free_basis (integer_ring,r) (ring_of_int r) n w /\
          ring_ideal r j /\ FINITE(ring_carrier(quotient_ring r j))
          ==> ?C. &(ideal_norm r j) =
                  abs(ring_det integer_ring {i | i < n} C) /\
                  !z. ring_sum r {i | i < n}
                        (\i. ring_mul r
                               (ring_of_int r
                                 (isum {l | l < n} (\l. C i l * z l)))
                               (w i)) IN j" (REPEAT STRIP_TAC THEN ABBREV_TAC q87 THEN SUBGOAL_THEN q86 STRIP_ASSUME_TAC THENL [FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FREE_BASIS_IN_CARRIER)) THEN MP_TAC v85 THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN STRIP_TAC THEN EXPAND_TAC "L" THEN ASM_SIMP_TAC [int_lattice, SUBSET, IN_ELIM_THM, IN_RING_IDEAL_0, IN_RING_IDEAL_SUB, INT_SUB_REFL, INT_MUL_RZERO] THEN REWRITE_TAC [v81] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_RING_IDEAL_RMUL THEN ASM_SIMP_TAC [RING_SUM, RING_OF_INT_OF_NUM, IDEAL_NORM_IN_IDEAL], ALL_TAC] THEN MP_TAC v80 THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT] THEN DISCH_THEN (X_CHOOSE_TAC q77) THEN EXISTS_TAC q76 THEN CONJ_TAC THENL [MP_TAC v75 THEN REWRITE_TAC [FINITE_NUMSEG_LT] THEN ANTS_TAC THENL [MATCH_MP_TAC INT_LATTICE_FULL_RANK THEN MAP_EVERY EXISTS_TAC [q72, q71] THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT, INT_OF_NUM_EQ] THEN ASM_SIMP_TAC [IDEAL_NORM_POS, r70], ALL_TAC] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun z66 => (do let z67 ← (do let z68 ← (pure z66); pure (concl z68)); pure (is_eq z67)))))) THEN MP_TAC v65 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN SIMP_TAC [HAS_SIZE, ideal_norm] THEN DISCH_THEN (SUBST1_TAC o CONJUNCT2) THEN SIMP_TAC [INT_OF_NUM_OF_INT, INT_ABS_POS], X_GEN_TAC q59 THEN SUBGOAL_THEN q58 MP_TAC THENL [ASM_REWRITE_TAC [INT_MATRIX_IMAGE_IN] THEN MESON_TAC [], ALL_TAC] THEN EXPAND_TAC "L" THEN REWRITE_TAC [IN_ELIM_THM] THEN MATCH_MP_TAC r57 THEN MATCH_MP_TAC RING_SUM_EQ THEN SIMP_TAC [IN_ELIM_THM]])
    let lattice := p88
    let v89 ← GSYM SUM_ADD
    let q90 ← q r"i:K"
    let q91 ← q r"g(ring_sum k s (\i. ring_mul k (ring_of_int k (a i)) ((w:K->A) i))) =
      vsum s (\i. Cx(real_of_int(a i)) * (g:A->complex)(w i))"
    let p92 ← prove r"!k (g:A->complex) s (a:K->int) w.
          g IN complex_embeddings k /\ FINITE s /\
          (!i. i IN s ==> w i IN ring_carrier k)
          ==> Re(g(ring_sum k s (\i. ring_mul k (ring_of_int k (a i)) (w i)))) +
              Im(g(ring_sum k s (\i. ring_mul k (ring_of_int k (a i)) (w i)))) =
              sum s (\i. real_of_int(a i) * (Re(g(w i)) + Im(g(w i))))" (REWRITE_TAC [complex_embeddings, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN q91 SUBST1_TAC THENL [FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_SUM th), RING_MUL, RING_OF_INT])) THEN ASM_SIMP_TAC [COMPLEX_RING_SUM] THEN MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC q90 THEN DISCH_TAC THEN REWRITE_TAC [o_THM] THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL th), RING_OF_INT, (← MATCH_MP RING_HOMOMORPHISM_RING_OF_INT th)])) THEN REWRITE_TAC [COMPLEX_RING_OF_INT, COMPLEX_RING_CLAUSES], ASM_SIMP_TAC [RE_VSUM, IM_VSUM, RE_MUL_CX, IM_MUL_CX, v89, REAL_ADD_LDISTRIB]])
    let lincomb := p92
    let v93 ← GSYM SUM_RMUL
    let q94 ← q r"w:num->A"
    let q95 ← q r"\i. isum {l | l < n} (\l. (C:num->num->int) i l * z l)"
    let q96 ← q r"{i:num | i < n}"
    let q97 ← q r"(e:num->A->complex) i"
    let q98 ← q r"k:A ring"
    let v99 ← ISPECL [q98, q97, q96, q95, q94] lincomb
    let v100 ← BETA_RULE v99
    let q101 ← q r"x:real = y ==> abs x <= c ==> abs y <= c"
    let r102 ← REAL_ARITH q101
    let q103 ← q r"i:num"
    let q104 ← q r"i:num"
    let q105 ← q r"m0:num"
    let q106 ← q r"1 <= n ==> ~(n = 0)"
    let r107 ← ARITH_RULE q106
    let q108 ← q r"&(ideal_norm (ring_of_integers k) (j:A->bool)) =
                     abs(ring_det integer_ring {i:num | i < n} C)"
    let q109 ← q r"\l:num. &0:int"
    let q110 ← q r"z:num->int"
    let q111 ← q r"C:num->num->int"
    let q112 ← q r"{i:num | i < n}"
    let v113 ← ISPECL [q112, q111, q110, q109] INT_MATRIX_IMAGE_INJECTIVE
    let q116 ← q r"z:num->int"
    let q117 ← q r"ring_sum k {i | i < n}
                  (\i. ring_mul k
                         (ring_of_int k
                           (isum {l | l < n} (\l. (C:num->num->int) i l * z l)))
                         ((w:num->A) i))"
    let q118 ← q r"m0:num"
    let q119 ← q r"z:num->int"
    let q120 ← q r"0 < n <=> 1 <= n"
    let r121 ← ARITH_RULE q120
    let v122 ← GSYM REAL_ABS_NZ
    let q123 ← q r"&0:real < abs x ==> ~(x = &0)"
    let r124 ← REAL_ARITH q123
    let q125 ← q r"!g. g IN complex_embeddings k
                         ==> ?i. i < n /\ (e:num->A->complex) i = g"
    let v126 ← GSYM MEMBER_NOT_EMPTY
    let q127 ← q r"k:A ring"
    let v128 ← ISPEC q127 COMPLEX_EMBEDDINGS_NONEMPTY
    let q129 ← q r"abs(ring_det real_ring {i | i < n}
             (\i m. Re((e:num->A->complex) i ((w:num->A) m)) + Im(e i (w m))) *
            real_of_int(ring_det integer_ring {i | i < n} C)) =
        sqrt(abs(real_of_int(number_field_discriminant (k:A ring)))) *
        &(ideal_norm (ring_of_integers k) (j:A->bool))"
    let q130 ← q r"\i j. real_of_int((C:num->num->int) i j)"
    let q131 ← q r"\i m. Re((e:num->A->complex) i ((w:num->A) m)) +
                            Im(e i (w m))"
    let q132 ← q r"{i:num | i < n}"
    let q133 ← q r"real_ring"
    let v134 ← ISPECL [q133, q132, q131, q130] RING_DET_MUL
    let q135 ← q r"real_ring"
    let v136 ← ISPEC q135 RING_HOMOMORPHISM_INTEGER_RING_OF_INT
    let v137 ← REWRITE_RULE [REAL_RING_OF_INT] v136
    let q138 ← q r"C:num->num->int"
    let q139 ← q r"{i:num | i < n}"
    let q140 ← q r"real_of_int"
    let q141 ← q r"real_ring"
    let q142 ← q r"integer_ring"
    let v143 ← ISPECL [q142, q141, q140, q139, q138] RING_DET_HOMOMORPHISM
    let q144 ← q r"ring_det real_ring {i | i < n}
        (\i l. sum {m | m < n}
                 (\m. (Re((e:num->A->complex) i ((w:num->A) m)) +
                       Im(e i (w m))) *
                      real_of_int((C:num->num->int) m l))) =
      ring_det real_ring {i | i < n} (\i m. Re(e i (w m)) + Im(e i (w m))) *
      real_of_int(ring_det integer_ring {i | i < n} C)"
    let q145 ← q r"c:num->real"
    let q146 ← q r"\i l. sum {m:num | m < n}
               (\m. (Re((e:num->A->complex) i ((w:num->A) m)) + Im(e i (w m))) *
                    real_of_int((C:num->num->int) m l))"
    let q147 ← q r"{i:num | i < n}"
    let v148 ← ISPECL [q147, q146, q145] MINKOWSKI_LINEAR_FORMS
    let q149 ← q r"e:num->A->complex"
    let q150 ← q r"w:num->A"
    let q151 ← q r"n:num"
    let q152 ← q r"k:A ring"
    let v153 ← ISPECL [q152, q151, q150, q149] det_disc
    let q154 ← q r"C:num->num->int"
    let q155 ← q r"j:A->bool"
    let q156 ← q r"w:num->A"
    let q157 ← q r"n:num"
    let q158 ← q r"ring_of_integers k:A ring"
    let v159 ← ISPECL [q158, q157, q156, q155] lattice
    let q160 ← q r"!y. ring_sum (ring_of_integers k) {i | i < n}
            (\i. ring_mul k (ring_of_int k (y i)) ((w:num->A) i)) =
          ring_sum k {i | i < n} (\i. ring_mul k (ring_of_int k (y i)) (w i))"
    let q161 ← q r"!i. i < n ==> (w:num->A) i IN ring_carrier k"
    let p162 ← prove r"!k j n w (e:num->A->complex) c.
          number_field k /\
          ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
          free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w /\
          (!i. i < n ==> e i IN complex_embeddings k) /\
          (!i j. i < n /\ j < n /\ e i = e j ==> i = j) /\
          (!g. g IN complex_embeddings k ==> ?i. i < n /\ e i = g) /\
          (!i. i < n ==> &0 < c i) /\
          sqrt(abs(real_of_int(number_field_discriminant k))) *
          &(ideal_norm (ring_of_integers k) j) <= product {i | i < n} c
          ==> ?x. x IN j /\ ~(x = ring_0 k) /\
                  !i. i < n ==> abs(Re(e i x) + Im(e i x)) <= c i" (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FREE_BASIS_IN_CARRIER)) THEN SUBGOAL_THEN q161 ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN q160 ASSUME_TAC THENL [GEN_TAC THEN MATCH_MP_TAC RING_SUM_RING_OF_INTEGERS THEN ASM_SIMP_TAC [IN_ELIM_THM, IN_SUBRING_MUL, RING_OF_INTEGERS_SUBRING, RING_OF_INT_IN_RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC v159 THEN REWRITE_TAC [RING_OF_INTEGERS] THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_OF_INTEGERS_FINITE_QUOTIENT], ASM_REWRITE_TAC []] THEN DISCH_THEN (X_CHOOSE_THEN q154 (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C"))) THEN MP_TAC v153 THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC v148 THEN REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN SUBGOAL_THEN q144 SUBST1_TAC THENL [MP_TAC v143 THEN REWRITE_TAC [v137] THEN REWRITE_TAC [INTEGER_RING, IN_UNIV, FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC v134 THEN SIMP_TAC [REAL_RING_CLAUSES, IN_UNIV, FINITE_NUMSEG_LT, REAL_RING_SUM], ALL_TAC] THEN ANTS_TAC THENL [SUBGOAL_THEN q129 ASSUME_TAC THENL [ASM_REWRITE_TAC [REAL_ABS_MUL] THEN AP_TERM_TAC THEN REWRITE_TAC [REAL_OF_INT_CLAUSES] THEN CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [MP_TAC v128 THEN ASM_REWRITE_TAC [v126, IN_ELIM_THM] THEN UNDISCH_TAC q125 THEN MESON_TAC [], MATCH_MP_TAC r124 THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LT THEN REWRITE_TAC [v122, REAL_OF_INT_CLAUSES] THEN ASM_SIMP_TAC [NUMBER_FIELD_DISCRIMINANT_NONZERO], REWRITE_TAC [REAL_OF_NUM_LT, r121] THEN ASM_SIMP_TAC [IDEAL_NORM_POS, RING_OF_INTEGERS_FINITE_QUOTIENT]]], DISCH_THEN (X_CHOOSE_THEN q119 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC q118) (LABEL_TAC "bd"))))] THEN EXISTS_TAC q117 THEN REPEAT CONJ_TAC THENL [USE_THEN "C" (ACCEPT_TAC o (SPEC q116)), DISCH_TAC THEN FIRST_ASSUM (fun z114 => tactic_of do pure (MP_TAC (← SPEC (← q r"\i. isum {l | l < n} (\l. (C:num->num->int) i l * z l)") (← (do let z115 ← (do pure (CONJUNCTS (← GEN_REWRITE_RULE id [free_basis] z114))); liftExcept (last z115)))))) THEN ASM_REWRITE_TAC [INTEGER_RING, IN_UNIV, RING_OF_INTEGERS] THEN DISCH_TAC THEN MP_TAC v113 THEN ANTS_TAC THEN REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, INT_MUL_RZERO, ISUM_0] THENL [CONJ_TAC THENL [ALL_TAC, FIRST_ASSUM ACCEPT_TAC] THEN DISCH_TAC THEN UNDISCH_TAC q108 THEN ASM_REWRITE_TAC [INT_ABS_NUM, INT_OF_NUM_EQ] THEN MATCH_MP_TAC r107 THEN ASM_SIMP_TAC [IDEAL_NORM_POS, RING_OF_INTEGERS_FINITE_QUOTIENT], DISCH_THEN (MP_TAC o (SPEC q105)) THEN ASM_REWRITE_TAC []], X_GEN_TAC q104 THEN DISCH_TAC THEN REMOVE_THEN "bd" (MP_TAC o (SPEC q103)) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r102 THEN MP_TAC v100 THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [int_isum, int_mul_th, v93] THEN wPart lhand (lhand o rand) SUM_SWAP THEN REWRITE_TAC [FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC [REAL_MUL_AC]])
    let box := p162
    let q170 ← q r"i:num"
    let q171 ← q r"i:num"
    let q172 ← q r"h:A->complex"
    let q173 ← q r"h:A->complex"
    let q174 ← q r"IMAGE (e:num->A->complex) {i | i < n} =
                 complex_embeddings k"
    let q175 ← q r"x:A"
    let q176 ← q r"{i:num | i < n}"
    let q177 ← q r"c:(A->complex)->real"
    let q178 ← q r"e:num->A->complex"
    let v179 ← ISPECL [q178, q177, q176] PRODUCT_IMAGE
    let q180 ← q r"IMAGE (e:num->A->complex) {i | i < n} =
                     complex_embeddings k"
    let q181 ← q r"(c:(A->complex)->real) o (e:num->A->complex)"
    let q182 ← q r"e:num->A->complex"
    let q183 ← q r"w:num->A"
    let q184 ← q r"n:num"
    let q185 ← q r"j:A->bool"
    let q186 ← q r"k:A ring"
    let v187 ← ISPECL [q186, q185, q184, q183, q182, q181] box
    let q188 ← q r"(!i j. i < n /\ j < n /\ (e:num->A->complex) i = e j ==> i = j) /\
      IMAGE e {i | i < n} = complex_embeddings k"
    let q189 ← q r"e:num->A->complex"
    let q190 ← q r"n = extension_degree (subfield_generated k {ring_0 k},k) (I:A->A)"
    let q191 ← q r"w:num->A"
    prove
      r"!k j (c:(A->complex)->real).
            number_field k /\
            ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
            (!g. g IN complex_embeddings k ==> &0 < c g) /\
            sqrt(abs(real_of_int(number_field_discriminant k))) *
            &(ideal_norm (ring_of_integers k) j)
            <= product (complex_embeddings k) c
            ==> ?x. x IN j /\ ~(x = ring_0 k) /\
                    !g. g IN complex_embeddings k
                        ==> abs(Re(g x) + Im(g x)) <= c g"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM ((X_CHOOSE_TAC q191) o (MATCH_MP RING_OF_INTEGERS_FREE)) THEN FIRST_ASSUM (MP_TAC o (MATCH_MP COMPLEX_EMBEDDINGS_HAS_SIZE)) THEN ABBREV_TAC q190 THEN DISCH_THEN (MP_TAC o (MATCH_MP HAS_SIZE_INDEX)) THEN REWRITE_TAC [EXISTS_UNIQUE_THM] THEN DISCH_THEN (X_CHOOSE_THEN q189 STRIP_ASSUME_TAC) THEN SUBGOAL_THEN q188 STRIP_ASSUME_TAC THENL [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN MESON_TAC [], ALL_TAC] THEN MP_TAC v187 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [o_THM] THEN REPEAT CONJ_TAC THENL [UNDISCH_TAC q180 THEN REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN MESON_TAC [], ASM_SIMP_TAC [], MP_TAC v179 THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC], MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC q175 THEN STRIP_TAC THEN ASM_REWRITE_TAC []] THEN UNDISCH_TAC q174 THEN REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN DISCH_TAC THEN X_GEN_TAC q173 THEN FIRST_X_ASSUM (MP_TAC o (SPEC q172)) THEN DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM th)])) THEN DISCH_THEN (X_CHOOSE_THEN q171 (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN FIRST_X_ASSUM (MP_TAC o ((SPEC q170) o (checkM (fun th => (do let z163 ← (do let z164 ← (pure th); pure (concl z164)); canM (fun z165 => (do let z166 ← (pure z165); find_termM (fun z167 => (do let z169 ← (pure z167); let z168 ← (q r"Re"); pure (z168 == z169))) z166)) z163))))) THEN ASM_REWRITE_TAC [o_THM])

  let NUMBER_FIELD_IDEAL_MINKOWSKI ← prove
    r"!k j (c:(A->complex)->real).
        number_field k /\
        ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
        (!g. g IN complex_embeddings k ==> &0 < c g) /\
        (!g h. g IN complex_embeddings k /\ h IN complex_embeddings k /\
               (!x. x IN ring_carrier k ==> norm(h x) = norm(g x))
               ==> c h = c g) /\
        sqrt(abs(real_of_int(number_field_discriminant k))) *
        &(ideal_norm (ring_of_integers k) j)
        <= product (complex_embeddings k) c
        ==> ?x. x IN j /\ ~(x = ring_0 k) /\
                !g. g IN complex_embeddings k ==> norm(g x) <= c g"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"j:A->bool"), (← q r"c:(A->complex)->real")] NUMBER_FIELD_IDEAL_MINKOWSKI_LINEAR_FORMS) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"x:A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier k") ASSUME_TAC THENL [UNDISCH_TAC (← q r"(x:A) IN j") THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_SUBSET) THEN FIRST_ASSUM (MP_TAC o (MATCH_MP RING_IDEAL_IMP_SUBSET)) THEN SET_TAC [], ALL_TAC] THEN X_GEN_TAC (← q r"g:A->complex") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(c:(A->complex)->real)(RESTRICTION (ring_carrier k) (cnj o g)) = c g") ASSUME_TAC THENL [FIRST_X_ASSUM (MATCH_MP_TAC o (checkM (fun th => (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); canM (fun z3 => (do let z4 ← (pure z3); find_termM (fun z5 => (do let z7 ← (pure z5); let z6 ← (q r"norm:complex->real"); pure (z6 == z7))) z4)) z1)))) THEN ASM_SIMP_TAC [COMPLEX_EMBEDDINGS_CNJ, RESTRICTION, o_THM, COMPLEX_NORM_CNJ], ALL_TAC] THEN FIRST_ASSUM (MP_TAC o (SPEC (← q r"RESTRICTION (ring_carrier k) (cnj o (g:A->complex))"))) THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"g:A->complex"))) THEN ASM_SIMP_TAC [COMPLEX_EMBEDDINGS_CNJ, RESTRICTION, o_THM, RE_CNJ, IM_CNJ] THEN MP_TAC (← SPEC (← q r"(g:A->complex) x") COMPLEX_NORM_LE_RE_IM) THEN REAL_ARITH_TAC)

  let NUMBER_FIELD_IDEAL_MINKOWSKI_NORM ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"0 < n <=> 1 <= n")
    prove
      r"!k j:A->bool.
          number_field k /\
          ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
          ==> ?x. x IN j /\ ~(x = ring_0 k) /\
                  &(ideal_norm (ring_of_integers k)
                      (ideal_generated (ring_of_integers k) {x})) <=
                  sqrt(abs(real_of_int(number_field_discriminant k))) *
                  &(ideal_norm (ring_of_integers k) j)"
      (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"C = sqrt(abs(real_of_int(number_field_discriminant(k:A ring)))) *
                    &(ideal_norm (ring_of_integers k) j)") THEN FIRST_ASSUM (MP_TAC o (MATCH_MP COMPLEX_EMBEDDINGS_HAS_SIZE)) THEN FIRST_ASSUM (MP_TAC o (MATCH_MP NUMBER_FIELD_DEGREE_POS)) THEN ABBREV_TAC (← q r"n = extension_degree (subfield_generated k {ring_0 k},k) (I:A->A)") THEN REWRITE_TAC [HAS_SIZE] THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"&0:real < C") ASSUME_TAC THENL [EXPAND_TAC "C" THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LT THEN REWRITE_TAC [(← GSYM REAL_ABS_NZ), REAL_OF_INT_CLAUSES] THEN ASM_SIMP_TAC [NUMBER_FIELD_DISCRIMINANT_NONZERO], REWRITE_TAC [REAL_OF_NUM_LT, r1] THEN MATCH_MP_TAC IDEAL_NORM_POS THEN ASM_SIMP_TAC [RING_OF_INTEGERS_FINITE_QUOTIENT]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"j:A->bool"), (← q r"\g:A->complex. root n C")] NUMBER_FIELD_IDEAL_MINKOWSKI) THEN ASM_SIMP_TAC [PRODUCT_CONST, REAL_POW_ROOT, REAL_LT_IMP_LE, LE_1, REAL_LE_REFL, ROOT_POS_LT] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"x:A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [ASM_MESON_TAC [ring_ideal, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS] THEN TRANS_TAC REAL_LE_TRANS (← q r"product (complex_embeddings(k:A ring)) (\g:A->complex. root n C)") THEN CONJ_TAC THENL [MATCH_MP_TAC PRODUCT_LE THEN ASM_SIMP_TAC [NORM_POS_LE], ASM_SIMP_TAC [PRODUCT_CONST, REAL_POW_ROOT, REAL_LT_IMP_LE, LE_1, REAL_LE_REFL]])

  let NUMBER_FIELD_IDEAL_CLASS_MINKOWSKI ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"0 < n <=> 1 <= n")
    let r2 ← SET_RULE (← q r"!x:A s z. x IN s /\ ~(x = z) ==> ~(s = {z})")
    let r3 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!k j:A->bool.
          number_field k /\
          ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
          ==> ?j'. j' IN ideal_class (ring_of_integers k) j /\
                   &(ideal_norm (ring_of_integers k) j') <=
                   sqrt(abs(real_of_int(number_field_discriminant k)))"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"dedekind_domain(ring_of_integers k:A ring)") ASSUME_TAC THENL [ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN)) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"j:A->bool")] DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"i:A->bool") (X_CHOOSE_THEN (← q r"b:A") STRIP_ASSUME_TAC)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"i:A->bool")] NUMBER_FIELD_IDEAL_MINKOWSKI_NORM) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:A") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier(ring_of_integers k) /\
      ~(ideal_generated (ring_of_integers k) {a:A} = {ring_0 k})") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r3 THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], DISCH_TAC] THEN MATCH_MP_TAC r2 THEN EXISTS_TAC (← q r"a:A") THEN ASM_REWRITE_TAC [IN_IDEAL_GENERATED_SELF], ALL_TAC] THEN SUBGOAL_THEN (← q r"?j'. ring_ideal (ring_of_integers k) j' /\
           ideal_prod (ring_of_integers k) i j' =
           ideal_generated (ring_of_integers k) {a:A}") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ideal_generated (ring_of_integers k) {a:A}"), (← q r"i:A->bool")] DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(j' = {ring_0 k:A})") ASSUME_TAC THENL [DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"i:A->bool"), (← q r"j':A->bool")] IDEAL_PROD_EQ_ZERO) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN EXISTS_TAC (← q r"j':A->bool") THEN CONJ_TAC THENL [REWRITE_TAC [IN_IDEAL_CLASS, RING_OF_INTEGERS] THEN ASM_REWRITE_TAC [] THEN MAP_EVERY EXISTS_TAC [(← q r"a:A"), (← q r"b:A")] THEN ASM_REWRITE_TAC [] THEN SUBST1_TAC (← SYM (← ASSUME (← q r"ideal_prod (ring_of_integers k) i j' =
        ideal_generated (ring_of_integers k) {a:A}"))) THEN SUBST1_TAC (← SYM (← ASSUME (← q r"ideal_prod (ring_of_integers k) j i =
        ideal_generated (ring_of_integers k) {b:A}"))) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"j:A->bool"), (← q r"i:A->bool"), (← q r"j':A->bool")] IDEAL_PROD_ASSOC) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC IDEAL_PROD_COMM THEN CONJ_TAC THEN MATCH_MP_TAC RING_IDEAL_IMP_SUBSET THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_PROD], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"&(ideal_norm (ring_of_integers k) (j':A->bool)):real"), (← q r"sqrt(abs(real_of_int(number_field_discriminant(k:A ring))))"), (← q r"&(ideal_norm (ring_of_integers k) (i:A->bool)):real")] REAL_LE_LMUL_EQ) THEN ANTS_TAC THENL [REWRITE_TAC [REAL_OF_NUM_LT, r1] THEN MATCH_MP_TAC IDEAL_NORM_POS THEN MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_REWRITE_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"i:A->bool"), (← q r"j':A->bool")] NUMBER_FIELD_IDEAL_NORM_MUL_Q) THEN ASM_REWRITE_TAC [REAL_OF_NUM_MUL] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN ASM_REWRITE_TAC [])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_IDEAL_MINKOWSKI_LINEAR_FORMS, NUMBER_FIELD_IDEAL_MINKOWSKI,
           NUMBER_FIELD_IDEAL_MINKOWSKI_NORM, NUMBER_FIELD_IDEAL_CLASS_MINKOWSKI }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- minkowski_theory.ml phrases from line 697 to 1154                      -/
/- ---------------------------------------------------------------------- -/

structure MinkowskiTheory02 where
  -- @@FIELDS
  NUMBER_FIELD_CLASS_GROUP_MINKOWSKI : thm
  NUMBER_FIELD_PID_MINKOWSKI : thm
  NUMBER_FIELD_DISCRIMINANT_DEGREE_1 : thm
  NUMBER_FIELD_DISCRIMINANT_ABS_GT_1 : thm
  NUMBER_FIELD_RAMIFIED_PRIME_EXISTS : thm
  COMPLEX_NORM_POW_2_VSUM_FORM : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupMinkowskiTheory02 [HolBase] (D : MinkowskiTheoryDeps) (BMinkowskiTheory01 : MinkowskiTheory01) :
    ExceptT String IO MinkowskiTheory02 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_INT_ARITH_TAC, ASM_MESON_TAC,
        ASM_REAL_ARITH_TAC, COMPLEX_RING, INT_REDUCE_CONV, MESON, MESON_TAC,
        REAL_ARITH, REAL_ARITH_TAC, SET_RULE, SET_TAC, TAUT, .. } := D
  let { ARITH, CARD_EQ_0, CARD_LE_2, CARD_SUBSET, CLASS_GROUP, CLASS_GROUP_MUL, CNJ_CX,
        CNJ_MUL, CNJ_VSUM, COMPLEX_EMBEDDINGS_HAS_SIZE, COMPLEX_EMBEDDINGS_NONEMPTY,
        COMPLEX_EMBEDDINGS_NORM_EQ, COMPLEX_MUL_CNJ, COMPLEX_POW_ONE,
        COMPLEX_RING_CLAUSES, CX_INJ, CX_MUL, CX_POW, DEDEKIND_IDEAL_PROD_CANCEL,
        DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES, DEDEKIND_IMP_INTEGRAL_DOMAIN,
        DEDEKIND_IMP_NOETHERIAN, DEDEKIND_RING_OF_INTEGERS, DIVIDES_0, DIVIDES_LE,
        EQ_TRANS, ETA_AX, EXISTS_UNIQUE_THM, EXTENSION, FINITE_COMPLEX_EMBEDDINGS,
        FINITE_DELETE, FINITE_EMPTY, FINITE_IMAGE_INJ_EQ, FINITE_INSERT, FINITE_SUBSET,
        FORALL_AND_THM, FORALL_IN_GSPEC, FORALL_IN_IMAGE, FORALL_UNWIND_THM2,
        GROUP_ID_SUBGROUP, GROUP_MUL_SUBGROUP, HAS_SIZE, IDEAL_CLASS_EQ,
        IDEAL_CLASS_EQ_ID, IDEAL_CLASS_IN_CLASS_GROUP, IDEAL_NORM_CARRIER,
        IDEAL_NORM_POS, IDEAL_NORM_SUBSET_DIVIDES, IDEAL_PROD_CARRIER, IDEAL_PROD_COMM,
        IDEAL_PROD_SUBSET_RIGHT, IMP_CONJ, INFINITE, INTEGER_RING,
        INTEGRAL_DOMAIN_RING_OF_INTEGERS, INTEGRAL_DOMAIN_UNIT_IDEAL, INT_ABS_NUM,
        INT_ABS_POS, INT_DIVIDES_RABS, INT_NOT_LE, INT_OF_NUM_EQ, INT_OF_NUM_OF_INT,
        INT_REM_EQ, IN_DELETE, IN_ELIM_THM, IN_IDEAL_CLASS, IN_IDEAL_GENERATED_SELF,
        IN_INSERT, IN_RING_IDEAL_0, IN_SING, IN_UNIV, MAXIMAL_IMP_PRIME_IDEAL,
        MAXIMAL_IMP_PROPER_IDEAL, MAXIMAL_IMP_RING_IDEAL, MAXIMAL_SUPERIDEAL_EXISTS,
        MEMBER_NOT_EMPTY, MONO_EXISTS, NOETHERIAN_RING_INDUCT, NORM_POS_LE,
        NOT_FORALL_THM, NOT_IMP, NOT_IN_EMPTY, NUMBER_FIELD_DEGREE_EQ_1,
        NUMBER_FIELD_DEGREE_POS, NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS,
        NUMBER_FIELD_DISCRIMINANT_NONZERO,
        NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_RAMIFIED_DISCRIMINANT, NUM_OF_INT_OF_NUM, PRIME_FACTOR, .. } := D.core1
  let { PRIME_IMP_RING_IDEAL, PRODUCT_CONST, PRODUCT_DELETE, PRODUCT_LE, PRODUCT_MUL,
        PRODUCT_POS_LT, PRODUCT_RESTRICT_SET, PROPER_IDEAL_ALT, PSUBSET,
        QUADRATIC_FIELD_DISCRIMINANT, QUADRATIC_FIELD_SQRT, REAL_EQ_ADD_LCANCEL,
        REAL_EQ_ADD_RCANCEL, REAL_EQ_INV2, REAL_INV_LE_1, REAL_LET_TRANS, REAL_LE_ADD,
        REAL_LE_ANTISYM, REAL_LE_INV, REAL_LE_INV_EQ, REAL_LE_LMUL, REAL_LE_MUL2,
        REAL_LE_POW2, REAL_LE_REFL, REAL_LT_INV_EQ, REAL_LT_MUL, REAL_LT_RMUL,
        REAL_MUL_LID, REAL_MUL_RID, REAL_MUL_RINV, REAL_NOT_LE, REAL_NOT_LT,
        REAL_OF_INT_CLAUSES, REAL_OF_NUM_EQ, REAL_OF_NUM_LE, REAL_OF_NUM_LT, REAL_POS,
        REAL_POW_EQ, REAL_POW_INV, REAL_POW_LE, REAL_POW_LE2, REAL_POW_LE_1,
        REAL_POW_LT, REAL_POW_NZ, REAL_POW_POW, RE_CX, RE_MUL_CX, RE_VSUM,
        RIGHT_FORALL_IMP_THM, RING_DET_SING, RING_HOMOMORPHISM_1, RING_IDEAL_CARRIER,
        RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IMP_SUBSET, RING_MUL_RID, RING_OF_INT,
        RING_OF_INTEGERS, RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE,
        RING_OF_INTEGERS_FINITE_QUOTIENT, RING_OF_INTEGERS_PRIME_SUBFIELD,
        RING_OF_INTEGERS_SUBSET, RING_OF_INT_1, RING_OF_INT_EQ_0_CHAR_0, RING_SUM_SING,
        SKOLEM_THM, SQRT_1, SUBGROUP_GENERATED_INC, SUBGROUP_GENERATED_MONO,
        SUBGROUP_GENERATED_SUPERSET, SUBSET, SUM_EQ, SUM_RMUL, SUM_SWAP,
        TRIVIAL_CLASS_GROUP, TRIVIAL_GROUP_SUBGROUP_GENERATED_TRIVIAL,
        VSUM_COMPLEX_LMUL, VSUM_COMPLEX_RMUL, complex_embeddings, free_basis,
        ideal_classes, num_INFINITE, num_divides, number_field, principal_ideal,
        squarefree, .. } := D.core2
  let { NUMBER_FIELD_IDEAL_CLASS_MINKOWSKI, NUMBER_FIELD_IDEAL_MINKOWSKI, .. } := BMinkowskiTheory01
  -- @@SCOPE END

  let NUMBER_FIELD_CLASS_GROUP_MINKOWSKI ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"(j:A->bool) PSUBSET l"
    let q2 ← q r"(j:A->bool) SUBSET l
        ==> {f p | p | P p /\ Q p /\ l SUBSET p} SUBSET
            {(f:(A->bool)->(A->bool)->bool) p | p |
             P p /\ Q p /\ j SUBSET p}"
    let r3 ← SET_RULE q2
    let q4 ← q r"(x:(A->bool)->bool) IN s ==> s SUBSET t ==> x IN t"
    let r5 ← SET_RULE q4
    let q6 ← q r"m:A->bool"
    let q7 ← q r"ideal_class r (j:A->bool) =
      group_mul (class_group r) (ideal_class r m) (ideal_class r l)"
    let q8 ← q r"j:A->bool"
    let q9 ← q r"r:A ring"
    let v10 ← ISPECL [q9, q8] IN_RING_IDEAL_0
    let q11 ← q r"l:A->bool"
    let q12 ← q r"ideal_prod r m (j:A->bool)"
    let q13 ← q r"ring_carrier r:A->bool"
    let q14 ← q r"m:A->bool"
    let q15 ← q r"j:A->bool"
    let q16 ← q r"r:A ring"
    let v17 ← ISPECL [q16, q15, q14, q13] DEDEKIND_IDEAL_PROD_CANCEL
    let q18 ← q r"ideal_prod r m l = (j:A->bool)"
    let q19 ← q r"(j:A->bool) PSUBSET l"
    let q20 ← q r"l:A->bool"
    let q21 ← q r"m:A->bool"
    let q22 ← q r"j:A->bool"
    let q23 ← q r"r:A ring"
    let v24 ← ISPECL [q23, q22, q21] DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES
    let q25 ← q r"j:A->bool"
    let q26 ← q r"r:A ring"
    let v27 ← ISPECL [q26, q25] IN_RING_IDEAL_0
    let q28 ← q r"prime_ideal r (m:A->bool) /\ ~(m = {ring_0 r})"
    let q29 ← q r"m:A->bool"
    let q30 ← q r"j:A->bool"
    let q31 ← q r"r:A ring"
    let v32 ← ISPECL [q31, q30] MAXIMAL_SUPERIDEAL_EXISTS
    let v33 ← CONJUNCT2 CLASS_GROUP
    let v34 ← CONJUNCT1 v33
    let v35 ← GSYM v34
    let q36 ← q r"j = ring_carrier(r:A ring)"
    let q37 ← q r"j:A->bool"
    let q38 ← q r"r:A ring"
    let p39 ← prove r"!r j:A->bool.
          dedekind_domain r /\ ring_ideal r j /\ ~(j = {ring_0 r})
          ==> ideal_class r j IN
              group_carrier(subgroup_generated (class_group r)
                {ideal_class r p | p | prime_ideal r p /\ ~(p = {ring_0 r}) /\
                                       j SUBSET p})" (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN X_GEN_TAC q38 THEN DISCH_TAC THEN MATCH_MP_TAC NOETHERIAN_RING_INDUCT THEN ASM_SIMP_TAC [DEDEKIND_IMP_NOETHERIAN] THEN X_GEN_TAC q37 THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ind")) THEN DISCH_TAC THEN ASM_CASES_TAC q36 THENL [ASM_SIMP_TAC [v35, GROUP_ID_SUBGROUP], ALL_TAC] THEN MP_TAC v32 THEN ASM_REWRITE_TAC [PROPER_IDEAL_ALT] THEN DISCH_THEN (X_CHOOSE_THEN q29 STRIP_ASSUME_TAC) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_RING_IDEAL)) THEN SUBGOAL_THEN q28 STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [MAXIMAL_IMP_PRIME_IDEAL] THEN MP_TAC v27 THEN ASM SET_TAC [], ALL_TAC] THEN MP_TAC v24 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN q20 STRIP_ASSUME_TAC) THEN SUBGOAL_THEN q19 ASSUME_TAC THENL [REWRITE_TAC [PSUBSET] THEN CONJ_TAC THENL [UNDISCH_THEN q18 (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [IDEAL_PROD_SUBSET_RIGHT, RING_IDEAL_IMP_SUBSET], DISCH_THEN (SUBST_ALL_TAC o SYM) THEN MP_TAC v17 THEN ASM_SIMP_TAC [RING_IDEAL_CARRIER, IDEAL_PROD_CARRIER] THEN REWRITE_TAC [NOT_IMP] THEN CONJ_TAC THENL [TRANS_TAC EQ_TRANS q12 THEN CONJ_TAC THENL [ALL_TAC, FIRST_ASSUM ACCEPT_TAC] THEN MATCH_MP_TAC IDEAL_PROD_COMM THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET], ASM_MESON_TAC [MAXIMAL_IMP_PROPER_IDEAL, PROPER_IDEAL_ALT]]], ALL_TAC] THEN REMOVE_THEN "ind" (MP_TAC o (SPEC q11)) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [MP_TAC v10 THEN ASM SET_TAC [], DISCH_THEN (LABEL_TAC "l")] THEN SUBGOAL_THEN q7 SUBST1_TAC THENL [ASM_SIMP_TAC [CLASS_GROUP_MUL], ALL_TAC] THEN MATCH_MP_TAC GROUP_MUL_SUBGROUP THEN CONJ_TAC THENL [MATCH_MP_TAC SUBGROUP_GENERATED_INC THEN CONJ_TAC THENL [REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN ASM_SIMP_TAC [IDEAL_CLASS_IN_CLASS_GROUP, PRIME_IMP_RING_IDEAL], REWRITE_TAC [IN_ELIM_THM] THEN EXISTS_TAC q6 THEN ASM_REWRITE_TAC []], REMOVE_THEN "l" (MATCH_MP_TAC o (MATCH_MP r5)) THEN MATCH_MP_TAC SUBGROUP_GENERATED_MONO THEN MATCH_MP_TAC r3 THEN UNDISCH_TAC q1 THEN SIMP_TAC [PSUBSET]])
    let primes := p39
    let q40 ← q r"1 <= n ==> (m <= n \/ n = 0 ==> m <= n)"
    let r41 ← ARITH_RULE q40
    let q42 ← q r"p:A->bool"
    let q43 ← q r"j':A->bool"
    let q44 ← q r"ring_of_integers k:A ring"
    let v45 ← ISPECL [q44, q43, q42] IDEAL_NORM_SUBSET_DIVIDES
    let q46 ← q r"(x:real) <= c ==> y <= x ==> y <= c"
    let r47 ← REAL_ARITH q46
    let q48 ← q r"p:A->bool"
    let q49 ← q r"(!p. P p /\ Q p /\ R p ==> S p)
      ==> {(f:(A->bool)->(A->bool)->bool) p | p | P p /\ Q p /\ R p} SUBSET
          {f p | p | P p /\ Q p /\ S p}"
    let r50 ← SET_RULE q49
    let q51 ← q r"s SUBSET t ==> (x:(A->bool)->bool) IN s ==> x IN t"
    let r52 ← SET_RULE q51
    let q53 ← q r"j':A->bool"
    let q54 ← q r"ring_of_integers k:A ring"
    let v55 ← ISPECL [q54, q53] primes
    let q56 ← q r"j':A->bool"
    let q57 ← q r"j:A->bool"
    let q58 ← q r"ring_of_integers k:A ring"
    let v59 ← ISPECL [q58, q57, q56] IDEAL_CLASS_EQ
    let q60 ← q r"j':A->bool"
    let q61 ← q r"j:A->bool"
    let q62 ← q r"k:A ring"
    let v63 ← ISPECL [q62, q61] NUMBER_FIELD_IDEAL_CLASS_MINKOWSKI
    let q64 ← q r"j:A->bool"
    let q65 ← q r"dedekind_domain(ring_of_integers k:A ring)"
    prove
      r"!k:A ring.
            number_field k
            ==> subgroup_generated (class_group(ring_of_integers k))
                  {ideal_class (ring_of_integers k) P | P |
                   prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
                   &(ideal_norm (ring_of_integers k) P) <=
                   sqrt(abs(real_of_int(number_field_discriminant k)))} =
                class_group(ring_of_integers k)"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN q65 ASSUME_TAC THENL [ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS], ALL_TAC] THEN REWRITE_TAC [SUBGROUP_GENERATED_SUPERSET] THEN ASM_SIMP_TAC [CLASS_GROUP, SUBSET, ideal_classes, FORALL_IN_GSPEC, RING_OF_INTEGERS] THEN X_GEN_TAC q64 THEN STRIP_TAC THEN MP_TAC v63 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN q60 STRIP_ASSUME_TAC) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o ((REWRITE_RULE [RING_OF_INTEGERS]) o (GEN_REWRITE_RULE id [IN_IDEAL_CLASS]))) THEN MP_TAC v59 THEN ASM_SIMP_TAC [DEDEKIND_IMP_INTEGRAL_DOMAIN, RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC v55 THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN MATCH_MP_TAC r52 THEN MATCH_MP_TAC SUBGROUP_GENERATED_MONO THEN MATCH_MP_TAC r50 THEN X_GEN_TAC q48 THEN STRIP_TAC THEN FIRST_X_ASSUM (MATCH_MP_TAC o (MATCH_MP r47)) THEN REWRITE_TAC [REAL_OF_NUM_LE] THEN MP_TAC v45 THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS_FINITE_QUOTIENT] THEN DISCH_THEN (MP_TAC o (MATCH_MP DIVIDES_LE)) THEN MATCH_MP_TAC r41 THEN ASM_SIMP_TAC [IDEAL_NORM_POS, RING_OF_INTEGERS_FINITE_QUOTIENT])

  let NUMBER_FIELD_PID_MINKOWSKI ← prove
    r"!k:A ring.
        number_field k /\
        (!P. prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
             &(ideal_norm (ring_of_integers k) P) <=
             sqrt(abs(real_of_int(number_field_discriminant k)))
             ==> ?a. a IN ring_carrier(ring_of_integers k) /\
                     P = ideal_generated (ring_of_integers k) {a})
        ==> PID(ring_of_integers k)"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"dedekind_domain(ring_of_integers k:A ring)") ASSUME_TAC THENL [ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS], ALL_TAC] THEN ASM_SIMP_TAC [(← GSYM TRIVIAL_CLASS_GROUP)] THEN FIRST_ASSUM (SUBST1_TAC o (SYM o (MATCH_MP NUMBER_FIELD_CLASS_GROUP_MINKOWSKI))) THEN MATCH_MP_TAC TRIVIAL_GROUP_SUBGROUP_GENERATED_TRIVIAL THEN REWRITE_TAC [SUBSET, FORALL_IN_GSPEC, IN_SING] THEN X_GEN_TAC (← q r"p:A->bool") THEN STRIP_TAC THEN ASM_SIMP_TAC [IDEAL_CLASS_EQ_ID, principal_ideal, RING_OF_INTEGERS] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"p:A->bool"))) THEN ASM_REWRITE_TAC [] THEN MESON_TAC [])

  let NUMBER_FIELD_DISCRIMINANT_DEGREE_1 ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"(g:A->complex) IN complex_embeddings k"
    let q2 ← q r"\i:num. (g:A->complex)"
    let q3 ← q r"\i:num. ring_1 k:A"
    let q4 ← q r"1"
    let q5 ← q r"k:A ring"
    let v6 ← ISPECL [q5, q4, q3, q2] NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS
    let v7 ← GSYM MEMBER_NOT_EMPTY
    let q8 ← q r"g:A->complex"
    let q9 ← q r"\i:num. (n:int)"
    let q10 ← q r"!f:int->A a. ?n. f a = f n"
    let r11 ← MESON [] q10
    let q12 ← q r"i < 1 <=> i = 0"
    let r13 ← ARITH_RULE q12
    let q14 ← q r"free_basis (integer_ring,ring_of_integers k) (ring_of_int k) 1
               (\i:num. ring_1(k:A ring))"
    let q15 ← q r"{i:num | i < 1} = {0}"
    let q16 ← q r"k:A ring"
    let v17 ← ISPEC q16 RING_OF_INTEGERS_SUBSET
    let q18 ← q r"k:A ring"
    let v19 ← ISPEC q18 NUMBER_FIELD_DEGREE_EQ_1
    let q20 ← q r"k:A ring"
    let v21 ← ISPEC q20 RING_OF_INTEGERS_PRIME_SUBFIELD
    let q22 ← q r"ring_carrier(ring_of_integers (k:A ring)) =
    {ring_of_int k n | n IN (:int)}"
    prove
      r"!k:A ring.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 1
          ==> number_field_discriminant k = &1"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN SUBGOAL_THEN q22 ASSUME_TAC THENL [MP_TAC v21 THEN MP_TAC v19 THEN MP_TAC v17 THEN ASM_SIMP_TAC [NUMBER_FIELD_IMP_FIELD] THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN q15 ASSUME_TAC THENL [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_SING] THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN q14 ASSUME_TAC THENL [ASM_REWRITE_TAC [free_basis, RING_SUM_SING, r13, FORALL_UNWIND_THM2, INTEGER_RING, IN_UNIV] THEN REWRITE_TAC [RING_OF_INTEGERS, IN_ELIM_THM, IN_UNIV] THEN SIMP_TAC [RING_MUL_RID, RING_OF_INT] THEN REWRITE_TAC [r11] THEN ASM_SIMP_TAC [RING_OF_INT_EQ_0_CHAR_0] THEN CONJ_TAC THENL [MESON_TAC [RING_OF_INT_1], REPEAT STRIP_TAC THEN EXISTS_TAC q9 THEN ASM_REWRITE_TAC []], ALL_TAC] THEN FIRST_ASSUM ((X_CHOOSE_TAC q8) o ((REWRITE_RULE [v7]) o (MATCH_MP COMPLEX_EMBEDDINGS_NONEMPTY))) THEN MP_TAC v6 THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [ARITH_TAC, ALL_TAC] THEN SIMP_TAC [RING_DET_SING, COMPLEX_RING_CLAUSES, IN_UNIV] THEN UNDISCH_TAC q1 THEN REWRITE_TAC [complex_embeddings, IN_ELIM_THM] THEN DISCH_THEN (SUBST1_TAC o ((MATCH_MP RING_HOMOMORPHISM_1) o CONJUNCT1)) THEN REWRITE_TAC [COMPLEX_RING_CLAUSES, COMPLEX_POW_ONE, CX_INJ] THEN REWRITE_TAC [REAL_OF_INT_CLAUSES] THEN DISCH_THEN (ACCEPT_TAC o SYM))

  let NUMBER_FIELD_DISCRIMINANT_ABS_GT_1 ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"(f:K->real) i * product (s DELETE i) c"
    let q2 ← q r"i:K"
    let q3 ← q r"s:K->bool"
    let q4 ← q r"c:K->real"
    let v5 ← ISPECL [q4, q3, q2] PRODUCT_DELETE
    let q6 ← q r"i:K"
    let q7 ← q r"s:K->bool"
    let q8 ← q r"f:K->real"
    let v9 ← ISPECL [q8, q7, q6] PRODUCT_DELETE
    let q10 ← q r"product s (c:K->real) <= product s f"
    let v11 ← GSYM REAL_NOT_LT
    let v12 ← GSYM REAL_LE_ANTISYM
    let p13 ← prove r"!s (f:K->real) c.
          FINITE s /\ (!i. i IN s ==> &0 <= f i /\ f i <= c i /\ &0 < c i) /\
          product s c <= product s f
          ==> !i. i IN s ==> f i = c i" (REPEAT STRIP_TAC THEN REWRITE_TAC [v12] THEN ASM_SIMP_TAC [v11] THEN DISCH_TAC THEN UNDISCH_TAC q10 THEN REWRITE_TAC [REAL_NOT_LE] THEN MP_TAC v9 THEN MP_TAC v5 THEN ASM_REWRITE_TAC [] THEN REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC q1 THEN CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC [] THEN MATCH_MP_TAC PRODUCT_LE THEN ASM_SIMP_TAC [FINITE_DELETE, IN_DELETE], MATCH_MP_TAC REAL_LT_RMUL THEN ASM_SIMP_TAC [PRODUCT_POS_LT, FINITE_DELETE, IN_DELETE]])
    let product_eq := p13
    let q14 ← q r"x:A"
    let q15 ← q r"!x:A s z. x IN s /\ ~(x = z) ==> ~(s = {z})"
    let r16 ← SET_RULE q15
    let v17 ← GSYM NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS
    let q18 ← q r"x:A"
    let q19 ← q r"ring_of_integers k:A ring"
    let v20 ← ISPEC q19 INTEGRAL_DOMAIN_UNIT_IDEAL
    let q21 ← q r"c:(A->complex)->real"
    let q22 ← q r"ring_carrier(ring_of_integers k):A->bool"
    let q23 ← q r"k:A ring"
    let v24 ← ISPECL [q23, q22, q21] NUMBER_FIELD_IDEAL_MINKOWSKI
    let p25 ← prove r"!k (c:(A->complex)->real).
          number_field k /\
          abs(real_of_int(number_field_discriminant k)) = &1 /\
          (!g. g IN complex_embeddings k ==> &0 < c g) /\
          (!g h. g IN complex_embeddings k /\ h IN complex_embeddings k /\
                 (!x. x IN ring_carrier k ==> norm(h x) = norm(g x))
                 ==> c h = c g) /\
          product (complex_embeddings k) c = &1
          ==> ?x. x IN ring_carrier(ring_of_integers k) /\
                  !g. g IN complex_embeddings k ==> norm(g x) = c g" (REPEAT STRIP_TAC THEN MP_TAC v24 THEN ASM_REWRITE_TAC [IDEAL_NORM_CARRIER, SQRT_1, REAL_MUL_LID, REAL_LE_REFL] THEN ANTS_TAC THENL [MP_TAC v20 THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_RING_OF_INTEGERS, NUMBER_FIELD_IMP_FIELD, RING_OF_INTEGERS], MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC q18 THEN STRIP_TAC THEN ASM_REWRITE_TAC []] THEN MATCH_MP_TAC product_eq THEN ASM_SIMP_TAC [FINITE_COMPLEX_EMBEDDINGS, NORM_POS_LE] THEN ASM_SIMP_TAC [v17] THEN REWRITE_TAC [REAL_OF_NUM_LE] THEN MATCH_MP_TAC IDEAL_NORM_POS THEN MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN MATCH_MP_TAC r16 THEN EXISTS_TAC q14 THEN ASM_REWRITE_TAC [IN_IDEAL_GENERATED_SELF])
    let unit_box := p25
    let q26 ← q r"&1 + inv(&m1 + &1)"
    let q27 ← q r"&1 + inv(&m2 + &1)"
    let q28 ← q r"e2:num"
    let v29 ← ISPECL [q28, q27, q26] REAL_POW_EQ
    let q30 ← q r"m2:num"
    let q31 ← q r"m1:num"
    let v32 ← REWRITE_RULE [INFINITE] num_INFINITE
    let q33 ← q r"(:num)"
    let q34 ← q r"xf:num->A"
    let v35 ← ISPECL [q34, q33] FINITE_IMAGE_INJ_EQ
    let v36 ← REWRITE_RULE [IMP_CONJ] FINITE_SUBSET
    let q37 ← q r"IMAGE (xf:num->A) (:num)"
    let q38 ← q r"(&2:real) pow e2"
    let q39 ← q r"k:A ring"
    let v40 ← ISPECL [q39, q38] RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE
    let q41 ← q r"xf:num->A"
    let q42 ← q r"&1:real <= t ==> &0 <= t"
    let r43 ← REAL_ARITH q42
    let q44 ← q r"(u:real) * v <= U * &1 ==> u * v <= U"
    let r45 ← REAL_ARITH q44
    let q46 ← q r"g:A->complex"
    let q47 ← q r"x:A"
    let q48 ← q r"e2:num * e1 = e1 * e2"
    let q49 ← q r"h:A->complex"
    let q50 ← q r"g:A->complex"
    let q51 ← q r"&1:real <= t ==> &0 < t"
    let r52 ← REAL_ARITH q51
    let q53 ← q r"\g:A->complex.
           (if g IN P (g1:A->complex) then t pow e2 else &1) *
           (if g IN P (g2:A->complex) then inv(t pow e1) else &1)"
    let q54 ← q r"k:A ring"
    let v55 ← ISPECL [q54, q53] unit_box
    let q56 ← q r"&m + &1:real"
    let v57 ← SPEC q56 REAL_LE_INV
    let q58 ← q r"&m + &1:real"
    let v59 ← SPEC q58 REAL_INV_LE_1
    let q60 ← q r"&1:real <= t /\ t <= &2"
    let q61 ← q r"t = &1 + inv(&m + &1)"
    let q62 ← q r"m:num"
    let q63 ← q r"!m:num. ?x. x IN {x | x IN ring_carrier(ring_of_integers k) /\
                            !g. g IN complex_embeddings k
                                ==> norm(g x) <= &2 pow e2} /\
                  norm((g1:A->complex) x) = (&1 + inv(&m + &1)) pow e2"
    let q64 ← q r"(t:(A->complex)->bool) SUBSET s ==> {x | x IN s /\ x IN t} = t"
    let r65 ← SET_RULE q64
    let v66 ← GSYM PRODUCT_RESTRICT_SET
    let q67 ← q r"!(s:(A->complex)->bool) t a.
          FINITE s /\ t SUBSET s
          ==> product s (\x. if x IN t then a else &1) = a pow CARD t"
    let q68 ← q r"(g1:A->complex) IN P g1 /\
      !(g:A->complex) (h:A->complex).
          g IN complex_embeddings k /\ h IN complex_embeddings k /\
          (!x. x IN ring_carrier k ==> norm(h x) = norm(g x))
          ==> !g0. h IN P g0 <=> g IN P g0"
    let q69 ← q r"g2:A->complex"
    let v70 ← GSYM MEMBER_NOT_EMPTY
    let q71 ← q r"~(e2 = 0)"
    let q72 ← q r"e2 = CARD((P:(A->complex)->(A->complex)->bool) g2)"
    let q73 ← q r"e1 = CARD((P:(A->complex)->(A->complex)->bool) g1)"
    let q74 ← q r"~((g2:A->complex) IN P (g1:A->complex))"
    let q75 ← q r"~((g1:A->complex) IN P (g2:A->complex))"
    let q76 ← q r"RESTRICTION (ring_carrier k) (cnj o (g1:A->complex))"
    let q77 ← q r"g1:A->complex"
    let v78 ← ISPECL [q77, q76] CARD_LE_2
    let q79 ← q r"{g1:A->complex, RESTRICTION (ring_carrier k) (cnj o g1)}"
    let q80 ← q r"complex_embeddings (k:A ring)"
    let v81 ← ISPECL [q80, q79] CARD_SUBSET
    let q82 ← q r"s SUBSET t ==> t SUBSET u ==> (s:(A->complex)->bool) SUBSET u"
    let r83 ← SET_RULE q82
    let q84 ← q r"complex_embeddings k SUBSET
        {g1:A->complex, RESTRICTION (ring_carrier k) (cnj o g1)}"
    let q85 ← q r"~(s SUBSET t) ==> ?x:A->complex. x IN s /\ ~(x IN t)"
    let r86 ← SET_RULE q85
    let q87 ← q r"?g2:A->complex. g2 IN complex_embeddings k /\ ~(g2 IN P (g1:A->complex))"
    let v88 ← GSYM MEMBER_NOT_EMPTY
    let q89 ← q r"g1:A->complex"
    let q90 ← q r"p /\ (p ==> q) ==> p /\ q"
    let r91 ← TAUT q90
    let q92 ← q r"!g:A->complex. P g SUBSET complex_embeddings (k:A ring) /\ FINITE(P g)"
    let q93 ← q r"!(g:A->complex) (h:A->complex).
          h IN P g <=>
                       h IN complex_embeddings k /\
                       !x. x IN ring_carrier k ==> norm(h x) = norm(g x)"
    let q94 ← q r"P = \g:A->complex.
            {h | h IN complex_embeddings k /\
                 !x. x IN ring_carrier k ==> norm(h x) = norm(g x)}"
    let q95 ← q r"n = extension_degree (subfield_generated k {ring_0 k},k) (I:A->A)"
    let q96 ← q r"k:A ring"
    let v97 ← ISPEC q96 NUMBER_FIELD_DISCRIMINANT_NONZERO
    let q98 ← q r"abs(real_of_int(number_field_discriminant(k:A ring))) = &1"
    let v99 ← GSYM INT_NOT_LE
    let v100 ← GSYM INT_REM_EQ
    let q101 ← q r"d:int = -- &1"
    let q102 ← q r"2"
    let q103 ← q r"squarefree(num_of_int(abs(d:int)))"
    let q104 ← q r"~(d:int = &0)"
    let q105 ← q r"d:int"
    let q106 ← q r"x:A"
    let q107 ← q r"k:A ring"
    let v108 ← ISPECL [q107, q106, q105] QUADRATIC_FIELD_DISCRIMINANT
    let q109 ← q r"d:int"
    let q110 ← q r"k:A ring"
    let v111 ← ISPEC q110 QUADRATIC_FIELD_SQRT
    let q112 ← q r"extension_degree (subfield_generated k {ring_0 k},k) (I:A->A) = 2"
    prove
      r"!k:A ring.
            number_field k /\
            ~(extension_degree (subfield_generated k {ring_0 k},k) I = 1)
            ==> &1 < abs(number_field_discriminant k)"
      (REPEAT STRIP_TAC THEN ASM_CASES_TAC q112 THENL [MP_TAC v111 THEN ASM_REWRITE_TAC [EXISTS_UNIQUE_THM] THEN DISCH_THEN ((X_CHOOSE_THEN q109 STRIP_ASSUME_TAC) o CONJUNCT1) THEN MP_TAC v108 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN SUBGOAL_THEN q104 ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC q103 THEN ASM_REWRITE_TAC [INT_ABS_NUM, NUM_OF_INT_OF_NUM] THEN REWRITE_TAC [squarefree, NOT_FORALL_THM, NOT_IMP] THEN EXISTS_TAC q102 THEN REWRITE_TAC [DIVIDES_0] THEN ARITH_TAC, ALL_TAC] THEN ASM_CASES_TAC q101 THENL [ASM_REWRITE_TAC [v100] THEN CONV_TAC INT_REDUCE_CONV, COND_CASES_TAC THEN ASM_INT_ARITH_TAC], ALL_TAC] THEN REWRITE_TAC [v99] THEN DISCH_TAC THEN SUBGOAL_THEN q98 ASSUME_TAC THENL [MP_TAC v97 THEN ASM_REWRITE_TAC [REAL_OF_INT_CLAUSES] THEN ASM_INT_ARITH_TAC, ALL_TAC] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP COMPLEX_EMBEDDINGS_HAS_SIZE)) THEN FIRST_ASSUM (MP_TAC o (MATCH_MP NUMBER_FIELD_DEGREE_POS)) THEN ABBREV_TAC q95 THEN REWRITE_TAC [HAS_SIZE] THEN REPEAT STRIP_TAC THEN ABBREV_TAC q94 THEN SUBGOAL_THEN q93 (LABEL_TAC "P") THENL [EXPAND_TAC "P" THEN REWRITE_TAC [IN_ELIM_THM], ALL_TAC] THEN SUBGOAL_THEN q92 ASSUME_TAC THENL [GEN_TAC THEN MATCH_MP_TAC r91 THEN CONJ_TAC THENL [ASM SET_TAC [], ASM_MESON_TAC [FINITE_SUBSET]], ALL_TAC] THEN FIRST_ASSUM ((X_CHOOSE_TAC q89) o ((REWRITE_RULE [v88]) o (MATCH_MP COMPLEX_EMBEDDINGS_NONEMPTY))) THEN SUBGOAL_THEN q87 STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r86 THEN DISCH_TAC THEN SUBGOAL_THEN q84 MP_TAC THENL [FIRST_X_ASSUM (MATCH_MP_TAC o (MATCH_MP r83)) THEN ASM_REWRITE_TAC [SUBSET, IN_INSERT, NOT_IN_EMPTY] THEN ASM_MESON_TAC [COMPLEX_EMBEDDINGS_NORM_EQ], DISCH_TAC THEN MP_TAC v81 THEN ASM_REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY] THEN MP_TAC v78 THEN ASM_ARITH_TAC], ALL_TAC] THEN SUBGOAL_THEN q75 ASSUME_TAC THENL [UNDISCH_TAC q74 THEN ASM_REWRITE_TAC [] THEN MESON_TAC [], ALL_TAC] THEN ABBREV_TAC q73 THEN ABBREV_TAC q72 THEN SUBGOAL_THEN q71 ASSUME_TAC THENL [EXPAND_TAC "e2" THEN ASM_SIMP_TAC [CARD_EQ_0] THEN REWRITE_TAC [v70] THEN EXISTS_TAC q69 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN q68 (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c")) THENL [ASM_SIMP_TAC [], REMOVE_THEN "P" (fun (_ : thm) => ALL_TAC)] THEN SUBGOAL_THEN q67 ASSUME_TAC THENL [REPEAT STRIP_TAC THEN REWRITE_TAC [v66] THEN ASM_SIMP_TAC [r65] THEN ASM_MESON_TAC [PRODUCT_CONST, FINITE_SUBSET], ALL_TAC] THEN SUBGOAL_THEN q63 MP_TAC THENL [X_GEN_TAC q62 THEN ABBREV_TAC q61 THEN SUBGOAL_THEN q60 STRIP_ASSUME_TAC THENL [EXPAND_TAC "t" THEN MP_TAC v59 THEN MP_TAC v57 THEN REAL_ARITH_TAC, ALL_TAC] THEN MP_TAC v55 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [REAL_LT_INV_EQ, REAL_POW_LT, REAL_OF_NUM_LT, ARITH, r52], REPEAT STRIP_TAC THEN USE_THEN "c" (MP_TAC o (SPECL [q50, q49])) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (fun th => REWRITE_TAC [th])], ASM_SIMP_TAC [PRODUCT_MUL] THEN REWRITE_TAC [REAL_POW_POW, REAL_POW_INV] THEN SUBGOAL_THEN q48 SUBST1_TAC THENL [ARITH_TAC, ALL_TAC] THEN MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC REAL_POW_NZ THEN ASM_REAL_ARITH_TAC], MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC q47 THEN STRIP_TAC] THEN ASM_SIMP_TAC [IN_ELIM_THM] THEN ASM_REWRITE_TAC [REAL_MUL_RID] THEN X_GEN_TAC q46 THEN DISCH_TAC THEN MATCH_MP_TAC r45 THEN MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [REAL_POW_LE2, REAL_LE_POW2, REAL_POS, REAL_LE_INV_EQ, REAL_POW_LE, REAL_INV_LE_1, REAL_POW_LE_1, REAL_LE_REFL, r43], ALL_TAC] THEN REWRITE_TAC [SKOLEM_THM, FORALL_AND_THM] THEN DISCH_THEN (X_CHOOSE_THEN q41 (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "xf"))) THEN MP_TAC v40 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o ((SPEC q37) o (MATCH_MP v36))) THEN ANTS_TAC THENL [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_UNIV] THEN FIRST_ASSUM ACCEPT_TAC, DISCH_TAC] THEN MP_TAC v35 THEN ASM_REWRITE_TAC [IN_UNIV, v32] THEN MAP_EVERY X_GEN_TAC [q31, q30] THEN DISCH_TAC THEN REMOVE_THEN "xf" (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"m1:num") th) THEN MP_TAC (← SPEC (← q r"m2:num") th))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN MP_TAC v29 THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC [REAL_POS, REAL_LE_INV_EQ] THEN REAL_ARITH_TAC, REWRITE_TAC [REAL_EQ_ADD_LCANCEL, REAL_EQ_INV2, REAL_EQ_ADD_RCANCEL, REAL_OF_NUM_EQ] THEN DISCH_THEN (ACCEPT_TAC o SYM)])

  let NUMBER_FIELD_RAMIFIED_PRIME_EXISTS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"q ==> (p <=> q) ==> p")
    prove
      r"!k:A ring.
          number_field k /\
          ~(extension_degree (subfield_generated k {ring_0 k},k) I = 1)
          ==> ?p P. prime p /\ prime_ideal (ring_of_integers k) P /\
                    ring_of_num k p IN P /\
                    1 < ramification_index (integer_ring,ring_of_integers k)
                          (ring_of_int k) P"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") NUMBER_FIELD_DISCRIMINANT_ABS_GT_1) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← SPEC (← q r"num_of_int(abs(number_field_discriminant(k:A ring)))") PRIME_FACTOR) THEN ANTS_TAC THENL [REWRITE_TAC [(← GSYM INT_OF_NUM_EQ)] THEN SIMP_TAC [INT_OF_NUM_OF_INT, INT_ABS_POS] THEN ASM_INT_ARITH_TAC, DISCH_THEN (X_CHOOSE_THEN (← q r"p:num") STRIP_ASSUME_TAC)] THEN MAP_EVERY EXISTS_TAC [(← q r"p:num")] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"p:num")] NUMBER_FIELD_RAMIFIED_DISCRIMINANT) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r1 THEN UNDISCH_TAC (← q r"p divides num_of_int(abs(number_field_discriminant(k:A ring)))") THEN REWRITE_TAC [num_divides] THEN SIMP_TAC [INT_OF_NUM_OF_INT, INT_ABS_POS, INT_DIVIDES_RABS])

  let COMPLEX_NORM_POW_2_VSUM_FORM ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let v1 ← REWRITE_RULE [ETA_AX] RE_VSUM
    let q2 ← q r"j:K"
    let q3 ← q r"FINITE(t:K->bool)"
    let v4 ← ASSUME q3
    let q5 ← q r"FINITE(s:L->bool)"
    let v6 ← ASSUME q5
    let v7 ← CONJ v6 v4
    let v8 ← MATCH_MP SUM_SWAP v7
    let q9 ← q r"i:K"
    let q10 ← q r"FINITE(t:K->bool)"
    let v11 ← ASSUME q10
    let q12 ← q r"FINITE(s:L->bool)"
    let v13 ← ASSUME q12
    let v14 ← CONJ v13 v11
    let v15 ← MATCH_MP SUM_SWAP v14
    let q16 ← q r"sum t (\i. sum s (\l. sum t (\j.
       Re(cnj((M:L->K->complex) l i) * M l j) * c i * c j)))"
    let p17 ← prove r"!a b x y. (Cx a * x) * (Cx b * y) = Cx(a * b) * (x * y)" (REWRITE_TAC [CX_MUL] THEN CONV_TAC COMPLEX_RING)
    let q18 ← q r"j:K"
    let q19 ← q r"i:K"
    let v20 ← GSYM VSUM_COMPLEX_LMUL
    let v21 ← GSYM VSUM_COMPLEX_RMUL
    let v22 ← SPEC_ALL COMPLEX_MUL_CNJ
    let v23 ← CONJUNCT1 v22
    let v24 ← GSYM v23
    let v25 ← GSYM RE_CX
    let q26 ← q r"l:L"
    let q27 ← q r"!l. norm(vsum t (\j. Cx(c j) * (M:L->K->complex) l j)) pow 2 =
        sum t (\i. sum t (\j. Re(cnj(M l i) * M l j) * c i * c j))"
    prove
      r"!s t (M:L->K->complex) (c:K->real).
          FINITE s /\ FINITE t
          ==> sum s (\l. norm(vsum t (\j. Cx(c j) * M l j)) pow 2) =
              sum t (\i. sum t (\j. Re(vsum s (\l. cnj(M l i) * M l j)) *
                                    c i * c j))"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN q27 (fun th => REWRITE_TAC [th]) THENL [X_GEN_TAC q26 THEN GEN_REWRITE_TAC LAND_CONV [v25] THEN REWRITE_TAC [CX_POW, v24] THEN ASM_SIMP_TAC [CNJ_VSUM, CNJ_MUL, CNJ_CX] THEN ASM_SIMP_TAC [v21, v20, RE_VSUM] THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC q19 THEN DISCH_TAC THEN REWRITE_TAC [] THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC q18 THEN DISCH_TAC THEN REWRITE_TAC [] THEN REWRITE_TAC [p17] THEN REWRITE_TAC [RE_MUL_CX] THEN REAL_ARITH_TAC, ALL_TAC] THEN TRANS_TAC EQ_TRANS q16 THEN CONJ_TAC THENL [GEN_REWRITE_TAC LAND_CONV [v15] THEN REWRITE_TAC [], MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC q9 THEN DISCH_TAC THEN REWRITE_TAC [] THEN GEN_REWRITE_TAC LAND_CONV [v8] THEN REWRITE_TAC [] THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC q2 THEN DISCH_TAC THEN ASM_SIMP_TAC [v1, SUM_RMUL]])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_CLASS_GROUP_MINKOWSKI, NUMBER_FIELD_PID_MINKOWSKI,
           NUMBER_FIELD_DISCRIMINANT_DEGREE_1, NUMBER_FIELD_DISCRIMINANT_ABS_GT_1,
           NUMBER_FIELD_RAMIFIED_PRIME_EXISTS, COMPLEX_NORM_POW_2_VSUM_FORM }
  -- @@RETURN END

end HolANT.MinkowskiTheory
