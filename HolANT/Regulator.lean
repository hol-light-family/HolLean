/- ========================================================================= -/
/- ANT: The logarithmic embedding of the units of a number field and ...   -/
/- ========================================================================= -/
/- File: HolANT/Regulator.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/regulator.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antregulatordiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/frag.ml, Library/grouptheory.ml, Library/permutations.ml, Library/products.ml, Library/ring_det.ml, Library/matroids.ml, Library/fieldtheory.ml, Library/isum.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, Library/ring_groups.ml, ANT/fingen_group.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/classgroup.ml, ANT/nf_valuation.ml, ANT/prime_split.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/integrality.ml, Multivariate/misc.ml, Multivariate/metric.ml, Multivariate/homology.ml, Multivariate/vectors.ml, Multivariate/determinants.ml, Multivariate/topology.ml, Multivariate/convex.ml, Multivariate/paths.ml, Multivariate/polytope.ml, Multivariate/degree.ml, Multivariate/derivatives.ml, Multivariate/integration.ml, Multivariate/measure.ml, Multivariate/complex_algebra.ml, Multivariate/complexes.ml, Multivariate/canal.ml, Multivariate/transcendentals.ml, Multivariate/realanalysis.ml, Multivariate/moretop.ml, Multivariate/cauchy.ml, Multivariate/complex_ring.ml, Multivariate/complex_field.ml, ANT/complex_embeddings.ml, ANT/power_basis.ml, ANT/infinite_places.ml, ANT/linear_forms.ml, ANT/classgroup_group.ml, ANT/finite_field_trace.ml, ANT/ramification.ml, ANT/quadratic.ml, ANT/minkowski_theory.ml, ANT/unit_theorem.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.Regulator fills them).

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
import HolLibrary.Frag
import HolLibrary.GroupTheory
import HolLibrary.Permutations
import HolLibrary.Products
import HolLibrary.RingDet
import HolLibrary.Matroids
import HolLibrary.FieldTheory
import HolLibrary.Isum
import HolANT.Algmisc
import HolANT.Integral
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolLibrary.RingGroups
import HolANT.FingenGroup
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
import HolANT.LinearForms
import HolANT.ClassgroupGroup
import HolANT.FiniteFieldTrace
import HolANT.Ramification
import HolANT.Quadratic
import HolANT.MinkowskiTheory
import HolANT.UnitTheorem

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
open HolANT.FingenGroup
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
open HolANT.ComplexEmbeddings
open HolANT.PowerBasis
open HolANT.InfinitePlaces
open HolANT.LinearForms
open HolANT.ClassgroupGroup
open HolANT.FiniteFieldTrace
open HolANT.Ramification
open HolANT.Quadratic
open HolANT.MinkowskiTheory
open HolANT.UnitTheorem

namespace HolANT.Regulator

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ABELIAN_UNIT_GROUP CARD_DELETE CARD_EQ_0 CARD_EQ_BIJECTION CARD_IMAGE_LE
   CARD_NUMSEG_LT CARD_SUBSET COMPLEX_EMBEDDINGS_NONEMPTY
   COMPLEX_EMBEDDINGS_NORM_EQ COMPLEX_EMBEDDINGS_NORM_FUN_EQ
   COMPLEX_EMBEDDINGS_NORM_POS DE_MORGAN_THM EMPTY_GSPEC EQ_TRANS
   EXISTS_UNIQUE_THM EXTENSION FIELD_REAL_RING FIELD_UNIT
   FINITE_COMPLEX_EMBEDDINGS FINITE_DELETE FINITE_DIFF FINITE_IMAGE
   FINITE_INFINITE_PLACES FINITE_NUMSEG_LT FORALL_IN_IMAGE FUN_IN_IMAGE
   GROUP_REAL_MULTIPLICATIVE_ID_INV_POW GROUP_REAL_MULTIPLICATIVE_SUM
   GROUP_REAL_MULTIPLICATIVE_ZPOW GROUP_SUM GROUP_SUM_IMAGE GROUP_ZPOW HAS_SIZE
   HAS_SIZE_INDEX IMAGE_EQ_EMPTY IMP_CONJ INFINITE_PLACES_DEGREE
   INFINITE_PLACES_MUL INFINITE_PLACES_POS INFINITE_PLACES_ROOT_OF_UNITY
   INFINITE_PLACES_SUM INFINITE_PLACES_UNIT_GROUP INTEGER_RING
   INTEGRAL_DOMAIN_REAL_RING INT_MUL_EQ_1 IN_DELETE IN_DIFF IN_ELIM_THM IN_IMAGE
   IN_INSERT IN_UNIV LEFT_IMP_EXISTS_THM LOG_1 LOG_INJ LOG_MONO_LT_IMP
   LOG_PRODUCT LOG_ZPOW LT MEMBER_NOT_EMPTY MONO_EXISTS
   NUMBER_FIELD_FUNDAMENTAL_UNITS NUMBER_FIELD_IMP_FIELD
   NUMBER_FIELD_UNIT_DOMINANT_PLACE REAL_ABS_NEG REAL_ABS_NZ REAL_ENTIRE
   REAL_EQ_MUL_LCANCEL REAL_LT_01 REAL_LT_MUL REAL_MUL_ASSOC REAL_MUL_LID
   REAL_MUL_RID REAL_MUL_RNEG REAL_NEG_EQ REAL_NEG_NEG REAL_OF_NUM_LT
   REAL_RING_CLAUSES REAL_RING_OF_INT REAL_RING_SUM RIGHT_FORALL_IMP_THM
   RIGHT_IMP_EXISTS_THM RING_DET_DEPENDENT_COLUMNS RING_DET_EMPTY RING_DET_EQ
   RING_DET_HOMOMORPHISM RING_DET_MUL RING_DET_REAL_DIAGONALLY_DOMINANT
   RING_DET_REINDEX RING_DET_ROWS_OMIT RING_DET_ROWS_SAME_IMAGE
   RING_DET_ROW_NEG_SUM RING_HOMOMORPHISM_INTEGER_RING_OF_INT RING_MATRIX_SOLVE
   RING_OF_INTEGERS_ROOT_OF_UNITY RING_OF_INTEGERS_UNIT_NONZERO
   RING_OF_INTEGERS_UNIT_NORM_PRODUCT RING_UNIT_IN_CARRIER SELECT_UNIQUE
   SKOLEM_THM SUBSET SUB_REFL SUM_CLAUSES SUM_DELETE SUM_DIFF SUM_EQ SUM_IMAGE
   SUM_LMUL SUM_NEG SUM_POS_LE SUM_SWAP UNIT_GROUP infinite_places int_eq
   int_mul_th int_neg_th int_of_num_th o_DEF : thm)
  deriving Inhabited

/-- What regulator.ml uses from Session besides theorems. -/
structure RegulatorDeps where
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
/- regulator.ml phrases from line 98 to 583                               -/
/- ---------------------------------------------------------------------- -/

structure Regulator01 where
  -- @@FIELDS
  REAL_MATRIX_SOLVE : thm
  RING_DET_REAL_OF_INT : thm
  RING_DET_REAL_ROW_NEG_SUM : thm
  RING_DET_REAL_ROWS_SAME_IMAGE : thm
  RING_DET_REAL_ROWS_OMIT : thm
  GROUP_REAL_MULTIPLICATIVE_LOG_SUM_ZPOW : thm
  NUMBER_FIELD_LOG_UNIT_SUM : thm
  NUMBER_FIELD_LOG_UNIT_EQ_0 : thm
  NUMBER_FIELD_LOG_UNIT_COMBINATION : thm
  NUMBER_FIELD_UNIT_DOMINANT_INFINITE_PLACE : thm
  NUMBER_FIELD_LOG_MATRIX_CHANGE : thm
  NUMBER_FIELD_LOG_MATRIX_NONZERO : thm
  NUMBER_FIELD_LOG_MATRIX_SYSTEM : thm
  NUMBER_FIELD_LOG_MATRIX_INVARIANT : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupRegulator01 [HolBase] (D : RegulatorDeps) :
    ExceptT String IO Regulator01 := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_MESON_TAC, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, SET_RULE,
        TAUT, .. } := D
  let { ABELIAN_UNIT_GROUP, CARD_EQ_0, CARD_EQ_BIJECTION, CARD_IMAGE_LE, CARD_SUBSET,
        COMPLEX_EMBEDDINGS_NONEMPTY, COMPLEX_EMBEDDINGS_NORM_EQ,
        COMPLEX_EMBEDDINGS_NORM_FUN_EQ, COMPLEX_EMBEDDINGS_NORM_POS, DE_MORGAN_THM,
        EXTENSION, FIELD_REAL_RING, FIELD_UNIT, FINITE_COMPLEX_EMBEDDINGS,
        FINITE_DELETE, FINITE_DIFF, FINITE_IMAGE, FINITE_INFINITE_PLACES,
        FORALL_IN_IMAGE, FUN_IN_IMAGE, GROUP_REAL_MULTIPLICATIVE_ID_INV_POW,
        GROUP_REAL_MULTIPLICATIVE_SUM, GROUP_REAL_MULTIPLICATIVE_ZPOW, GROUP_SUM,
        GROUP_SUM_IMAGE, GROUP_ZPOW, IMAGE_EQ_EMPTY, IMP_CONJ, INFINITE_PLACES_MUL,
        INFINITE_PLACES_POS, INFINITE_PLACES_ROOT_OF_UNITY, INFINITE_PLACES_SUM,
        INFINITE_PLACES_UNIT_GROUP, INTEGER_RING, INT_MUL_EQ_1, IN_DELETE, IN_DIFF,
        IN_ELIM_THM, IN_IMAGE, IN_UNIV, LEFT_IMP_EXISTS_THM, LOG_1, LOG_INJ,
        LOG_MONO_LT_IMP, LOG_PRODUCT, LOG_ZPOW, MONO_EXISTS, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_UNIT_DOMINANT_PLACE, REAL_ABS_NEG, REAL_ENTIRE,
        REAL_EQ_MUL_LCANCEL, REAL_LT_01, REAL_LT_MUL, REAL_MUL_ASSOC, REAL_MUL_LID,
        REAL_MUL_RID, REAL_RING_CLAUSES, REAL_RING_OF_INT, REAL_RING_SUM,
        RIGHT_FORALL_IMP_THM, RIGHT_IMP_EXISTS_THM, RING_DET_EQ, RING_DET_HOMOMORPHISM,
        RING_DET_MUL, RING_DET_REAL_DIAGONALLY_DOMINANT, RING_DET_REINDEX,
        RING_DET_ROWS_OMIT, RING_DET_ROWS_SAME_IMAGE, RING_DET_ROW_NEG_SUM,
        RING_HOMOMORPHISM_INTEGER_RING_OF_INT, RING_MATRIX_SOLVE,
        RING_OF_INTEGERS_ROOT_OF_UNITY, RING_OF_INTEGERS_UNIT_NONZERO,
        RING_OF_INTEGERS_UNIT_NORM_PRODUCT, RING_UNIT_IN_CARRIER, SKOLEM_THM, SUBSET,
        SUM_DELETE, SUM_DIFF, SUM_EQ, SUM_IMAGE, SUM_LMUL, SUM_NEG, SUM_POS_LE,
        UNIT_GROUP, infinite_places, int_eq, int_mul_th, int_neg_th, int_of_num_th,
        o_DEF, .. } := D.core1
  -- @@SCOPE END

  let REAL_MATRIX_SOLVE ← prove
    r"!s (m:K->K->real) v.
        FINITE s /\ ~(ring_det real_ring s m = &0)
        ==> ?t. !i. i IN s ==> sum s (\j. m i j * t j) = v i"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"real_ring"), (← q r"s:K->bool"), (← q r"m:K->K->real"), (← q r"v:K->real")] RING_MATRIX_SOLVE) THEN ASM_SIMP_TAC [FIELD_UNIT, FIELD_REAL_RING, REAL_RING_CLAUSES, IN_UNIV, REAL_RING_SUM] THEN MESON_TAC [])

  let RING_DET_REAL_OF_INT ← prove
    r"!s (m:K->K->int).
        FINITE s
        ==> ring_det real_ring s (\i j. real_of_int(m i j)) =
            real_of_int(ring_det integer_ring s m)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"real_ring"), (← q r"ring_of_int real_ring"), (← q r"s:K->bool"), (← q r"m:K->K->int")] RING_DET_HOMOMORPHISM) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, REAL_RING_OF_INT, INTEGER_RING, IN_UNIV] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REFL_TAC)

  let RING_DET_REAL_ROW_NEG_SUM ← prove
    r"!s (f:K->K->real) k.
        FINITE s /\ k IN s
        ==> ring_det real_ring s
              (\i j. if i = k then --(sum s (\l. f l j)) else f i j) =
            --(ring_det real_ring s f)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"real_ring"), (← q r"s:K->bool"), (← q r"f:K->K->real"), (← q r"k:K")] RING_DET_ROW_NEG_SUM) THEN ASM_REWRITE_TAC [REAL_RING_CLAUSES, REAL_RING_SUM, IN_UNIV])

  let RING_DET_REAL_ROWS_SAME_IMAGE ← prove
    r"!s (f:B->K->real) p p'.
        FINITE s /\
        (!i j. i IN s /\ j IN s /\ p i = p j ==> i = j) /\
        (!i j. i IN s /\ j IN s /\ p' i = p' j ==> i = j) /\
        IMAGE p s = IMAGE p' s
        ==> abs(ring_det real_ring s (\i j. f (p' i) j)) =
            abs(ring_det real_ring s (\i j. f (p i) j))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"real_ring"), (← q r"s:K->bool"), (← q r"f:B->K->real"), (← q r"p:K->B"), (← q r"p':K->B")] RING_DET_ROWS_SAME_IMAGE) THEN ASM_REWRITE_TAC [REAL_RING_CLAUSES] THEN STRIP_TAC THEN ASM_REWRITE_TAC [REAL_ABS_NEG])

  let RING_DET_REAL_ROWS_OMIT ← prove
    r"!(P:B->bool) (s:K->bool) (f:B->K->real) p p'.
        FINITE P /\ FINITE s /\ CARD s = CARD P - 1 /\
        (!j. j IN s ==> sum P (\v. f v j) = &0) /\
        (!i. i IN s ==> p i IN P) /\
        (!i j. i IN s /\ j IN s /\ p i = p j ==> i = j) /\
        (!i. i IN s ==> p' i IN P) /\
        (!i j. i IN s /\ j IN s /\ p' i = p' j ==> i = j)
        ==> abs(ring_det real_ring s (\i j. f (p' i) j)) =
            abs(ring_det real_ring s (\i j. f (p i) j))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"real_ring"), (← q r"P:B->bool"), (← q r"s:K->bool"), (← q r"f:B->K->real"), (← q r"p:K->B"), (← q r"p':K->B")] RING_DET_ROWS_OMIT) THEN ASM_REWRITE_TAC [REAL_RING_CLAUSES, REAL_RING_SUM, IN_UNIV] THEN STRIP_TAC THEN ASM_REWRITE_TAC [REAL_ABS_NEG])

  let GROUP_REAL_MULTIPLICATIVE_LOG_SUM_ZPOW ← prove
    r"!G (g:A->real) (x:K->A) n t.
        abelian_group G /\
        (!x. x IN group_carrier G ==> &0 < g x) /\
        (!x y. x IN group_carrier G /\ y IN group_carrier G
               ==> g(group_mul G x y) = g x * g y) /\
        FINITE t /\ (!i. i IN t ==> x i IN group_carrier G)
        ==> log(g(group_sum G t (\i. group_zpow G (x i) (n i)))) =
            sum t (\i. real_of_int(n i) * log(g(x i)))"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"(g:A->real)(group_id G) = &1") ASSUME_TAC THENL [ASM_MESON_TAC [GROUP_REAL_MULTIPLICATIVE_ID_INV_POW], ALL_TAC] THEN wPart (rand o lhand) (lhand o rand) GROUP_REAL_MULTIPLICATIVE_SUM THEN ASM_SIMP_TAC [GROUP_ZPOW] THEN DISCH_THEN SUBST1_TAC THEN wPart lhand (lhand o rand) LOG_PRODUCT THEN ASM_SIMP_TAC [GROUP_ZPOW] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC (← q r"i:K") THEN DISCH_TAC THEN REWRITE_TAC [] THEN wPart (rand o lhand) (lhand o rand) GROUP_REAL_MULTIPLICATIVE_ZPOW THEN ASM_SIMP_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [LOG_ZPOW])

  let NUMBER_FIELD_LOG_UNIT_SUM ← prove
    r"!k u:A.
        number_field k /\ ring_unit (ring_of_integers k) u
        ==> sum (infinite_places k)
              (\v. &(CARD {g | g IN complex_embeddings k /\
                               (\x. norm(g x)) = v}) * log(v u)) = &0"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"u:A")] RING_OF_INTEGERS_UNIT_NONZERO) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_SIMP_TAC [INFINITE_PLACES_SUM] THEN wPart lhand (rand o rand) LOG_PRODUCT THEN ASM_SIMP_TAC [FINITE_COMPLEX_EMBEDDINGS, COMPLEX_EMBEDDINGS_NORM_POS] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"u:A")] RING_OF_INTEGERS_UNIT_NORM_PRODUCT) THEN ASM_SIMP_TAC [LOG_1])

  let NUMBER_FIELD_LOG_UNIT_EQ_0 ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"(p ==> (q <=> r)) ==> (p ==> q <=> p ==> r)")
    prove
      r"!k u:A.
          number_field k /\ ring_unit (ring_of_integers k) u
          ==> ((!v. v IN infinite_places k ==> log(v u) = &0) <=>
               ?m. 1 <= m /\ ring_pow k u m = ring_1 k)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"u:A")] RING_OF_INTEGERS_UNIT_NONZERO) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"u:A")] RING_OF_INTEGERS_ROOT_OF_UNITY) THEN ASM_SIMP_TAC [RING_UNIT_IN_CARRIER] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [infinite_places, FORALL_IN_IMAGE] THEN AP_TERM_TAC THEN ABS_TAC THEN MATCH_MP_TAC r1 THEN DISCH_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [(← GSYM LOG_1)] THEN MATCH_MP_TAC LOG_INJ THEN ASM_SIMP_TAC [COMPLEX_EMBEDDINGS_NORM_POS, REAL_LT_01])

  let NUMBER_FIELD_LOG_UNIT_COMBINATION ← prove
    r"!k (s:K->bool) (e:K->A) n z v.
        number_field k /\ FINITE s /\
        (!i. i IN s ==> ring_unit (ring_of_integers k) (e i)) /\
        z IN ring_carrier k /\ (?m. 1 <= m /\ ring_pow k z m = ring_1 k) /\
        v IN infinite_places k
        ==> log(v(ring_mul k z
                    (group_sum (unit_group(ring_of_integers k)) s
                       (\i. group_zpow (unit_group(ring_of_integers k))
                                       (e i) (n i))))) =
            sum s (\i. real_of_int(n i) * log(v(e i)))"
    (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"m:num") STRIP_ASSUME_TAC) ASSUME_TAC))))) THEN ABBREV_TAC (← q r"y = group_sum (unit_group(ring_of_integers k)) s
          (\i. group_zpow (unit_group(ring_of_integers k))
                          ((e:K->A) i) (n i))") THEN SUBGOAL_THEN (← q r"ring_unit (ring_of_integers k) (y:A)") ASSUME_TAC THENL [EXPAND_TAC "y" THEN MP_TAC (← ISPECL [(← q r"unit_group(ring_of_integers k):A group"), (← q r"s:K->bool"), (← q r"\i. group_zpow (unit_group(ring_of_integers k)) ((e:K->A) i) (n i)")] GROUP_SUM) THEN REWRITE_TAC [UNIT_GROUP, IN_ELIM_THM], ALL_TAC] THEN SUBGOAL_THEN (← q r"(y:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_UNIT_NONZERO, NUMBER_FIELD_IMP_FIELD], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"v:A->real"), (← q r"z:A"), (← q r"y:A")] INFINITE_PLACES_MUL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"v:A->real"), (← q r"z:A"), (← q r"m:num")] INFINITE_PLACES_ROOT_OF_UNITY) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [REAL_MUL_LID] THEN EXPAND_TAC "y" THEN MATCH_MP_TAC GROUP_REAL_MULTIPLICATIVE_LOG_SUM_ZPOW THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"v:A->real")] INFINITE_PLACES_UNIT_GROUP) THEN ASM_SIMP_TAC [ABELIAN_UNIT_GROUP, UNIT_GROUP, IN_ELIM_THM])

  let NUMBER_FIELD_UNIT_DOMINANT_INFINITE_PLACE ← prove
    r"!k v:A->real.
        number_field k /\ v IN infinite_places k
        ==> ?u. ring_unit (ring_of_integers k) u /\
                !w. w IN infinite_places k /\ ~(w = v) ==> w u < &1"
    (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, infinite_places] THEN REWRITE_TAC [FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"k:A ring") THEN DISCH_TAC THEN X_GEN_TAC (← q r"g:A->complex") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"g:A->complex")] NUMBER_FIELD_UNIT_DOMINANT_PLACE) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"u:A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [IMP_CONJ, FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"h:A->complex") THEN REPEAT DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [COMPLEX_EMBEDDINGS_NORM_EQ, COMPLEX_EMBEDDINGS_NORM_FUN_EQ])

  let NUMBER_FIELD_LOG_MATRIX_CHANGE ← prove
    r"!k (c:(A->real)->real) (s:K->bool) (e:K->A) (x:K->A) z a (p:K->A->real).
        number_field k /\ FINITE s /\
        (!i. i IN s ==> ring_unit (ring_of_integers k) (e i)) /\
        (!i. i IN s ==> p i IN infinite_places k) /\
        (!j. j IN s
             ==> z j IN ring_carrier k /\
                 (?m. 1 <= m /\ ring_pow k (z j) m = ring_1 k) /\
                 x j = ring_mul k (z j)
                        (group_sum (unit_group(ring_of_integers k)) s
                          (\l. group_zpow (unit_group(ring_of_integers k))
                                          (e l) (a j l))))
        ==> ring_det real_ring s (\i j. c(p i) * log(p i (x j))) =
            ring_det real_ring s (\i j. c(p i) * log(p i (e j))) *
            ring_det real_ring s (\l j. real_of_int(a j l))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"real_ring"), (← q r"s:K->bool"), (← q r"\i l. (c:(A->real)->real)(p i) * log((p:K->A->real) i ((e:K->A) l))"), (← q r"\l j. real_of_int((a:K->K->int) j l)")] RING_DET_MUL) THEN ASM_REWRITE_TAC [REAL_RING_CLAUSES, IN_UNIV, REAL_RING_SUM] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_DET_EQ THEN MAP_EVERY X_GEN_TAC [(← q r"i:K"), (← q r"j:K")] THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"j:K"))) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o (checkM (fun z1 => (do let z2 ← (do let z3 ← (pure z1); pure (concl z3)); pure (is_eq z2))))) THEN wPart (rand o lhand) (lhand o rand) NUMBER_FIELD_LOG_UNIT_COMBINATION THEN ANTS_TAC THENL [ASM_SIMP_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [(← GSYM SUM_LMUL)] THEN MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC [] THEN REAL_ARITH_TAC)

  let NUMBER_FIELD_LOG_MATRIX_NONZERO ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r4 ← REAL_ARITH (← q r"(x:real) < &0 ==> abs x = --x")
    let r5 ← REAL_ARITH (← q r"(x:real) < &0 ==> &0 <= --x")
    let r6 ← REAL_ARITH (← q r"(x:real) <= &0 <=> &0 <= --x")
    let r7 ← REAL_ARITH (← q r"x < &0 /\ (s':real) <= &0 ==> s' = s - x ==> s < &0")
    let r8 ← REAL_ARITH (← q r"!a b c x y:real. x = y /\ c < &0 ==> b = y ==> c = a - b ==> a = &0
                         ==> &0 < x")
    let r9 ← REAL_ARITH (← q r"&0 < --(x:real) <=> x < &0")
    let r10 ← REAL_ARITH (← q r"&0 < (x:real) * --y ==> x * y < &0")
    let r11 ← SET_RULE (← q r"~(t SUBSET u) ==> ?x:A->real. x IN t /\ ~(x IN u)")
    prove
      r"!k (c:(A->real)->real) (s:K->bool) (e:K->A) (p:K->A->real).
          number_field k /\
          (!v. v IN infinite_places k ==> &0 < c v) /\
          (!u. ring_unit (ring_of_integers k) u
               ==> sum (infinite_places k) (\v. c v * log(v u)) = &0) /\
          FINITE s /\ CARD s = CARD(infinite_places k) - 1 /\
          (!i. i IN s ==> ring_unit (ring_of_integers k) (e i)) /\
          (!u. ring_unit (ring_of_integers k) u
               ==> ?z n. z IN ring_carrier k /\
                         (?m. 1 <= m /\ ring_pow k z m = ring_1 k) /\
                         u = ring_mul k z
                              (group_sum (unit_group(ring_of_integers k)) s
                                (\i. group_zpow (unit_group(ring_of_integers k))
                                                (e i) (n i)))) /\
          (!i. i IN s ==> p i IN infinite_places k) /\
          (!i j. i IN s /\ j IN s /\ p i = p j ==> i = j)
          ==> ~(ring_det real_ring s (\i j. c(p i) * log(p i (e j))) = &0)"
      (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sum") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "gen") STRIP_ASSUME_TAC))))))) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITE_INFINITE_PLACES)) THEN SUBGOAL_THEN (← q r"?v0:A->real. v0 IN infinite_places k /\ ~(v0 IN IMAGE p (s:K->bool))") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r11 THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"p:K->A->real"), (← q r"s:K->bool")] CARD_IMAGE_LE) THEN MP_TAC (← ISPECL [(← q r"infinite_places(k:A ring)"), (← q r"IMAGE (p:K->A->real) s")] CARD_SUBSET) THEN ASM_SIMP_TAC [FINITE_IMAGE] THEN SUBGOAL_THEN (← q r"~(CARD(infinite_places(k:A ring)) = 0)") MP_TAC THENL [ASM_SIMP_TAC [CARD_EQ_0, infinite_places, IMAGE_EQ_EMPTY, COMPLEX_EMBEDDINGS_NONEMPTY], ARITH_TAC], ALL_TAC] THEN SUBGOAL_THEN (← q r"?d. !i. i IN s
              ==> ring_unit (ring_of_integers k) (d i:A) /\
                  !w. w IN infinite_places k /\ ~(w = (p:K->A->real) i)
                      ==> w(d i) < &1") STRIP_ASSUME_TAC THENL [REWRITE_TAC [(← GSYM SKOLEM_THM), (← GSYM RIGHT_IMP_EXISTS_THM)] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC NUMBER_FIELD_UNIT_DOMINANT_INFINITE_PLACE THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(ring_det real_ring s
         (\i j. (c:(A->real)->real)(p i) * log((p:K->A->real) i ((d:K->A) j)))
        = &0)") ASSUME_TAC THENL [MATCH_MP_TAC RING_DET_REAL_DIAGONALLY_DOMINANT THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"j:K") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"!w. w IN infinite_places k /\ ~(w = (p:K->A->real) j)
            ==> (c:(A->real)->real) w * log(w((d:K->A) j)) < &0") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC r10 THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC [] THEN REWRITE_TAC [r9] THEN GEN_REWRITE_TAC RAND_CONV [(← GSYM LOG_1)] THEN MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_SIMP_TAC [] THEN MATCH_MP_TAC INFINITE_PLACES_POS THEN EXISTS_TAC (← q r"k:A ring") THEN ASM_MESON_TAC [RING_OF_INTEGERS_UNIT_NONZERO], ALL_TAC] THEN SUBGOAL_THEN (← q r"&0 < sum s (\i. (c:(A->real)->real)(p i) *
                        log((p:K->A->real) i ((d:K->A) j)))") ASSUME_TAC THENL [USE_THEN "sum" (MP_TAC o (SPEC (← q r"(d:K->A) j"))) THEN ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"\v:A->real. (c:(A->real)->real) v * log(v((d:K->A) j))"), (← q r"infinite_places(k:A ring)"), (← q r"IMAGE (p:K->A->real) s")] SUM_DIFF) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"p:K->A->real"), (← q r"\v:A->real. (c:(A->real)->real) v * log(v((d:K->A) j))"), (← q r"s:K->bool")] SUM_IMAGE) THEN ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN REWRITE_TAC [o_DEF] THEN MATCH_MP_TAC r8 THEN CONJ_TAC THENL [REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"\v:A->real. (c:(A->real)->real) v * log(v((d:K->A) j))"), (← q r"infinite_places(k:A ring) DIFF IMAGE (p:K->A->real) s"), (← q r"v0:A->real")] SUM_DELETE) THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_DIFF, IN_DIFF], ALL_TAC] THEN MATCH_MP_TAC r7 THEN CONJ_TAC THENL [REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [FUN_IN_IMAGE], REWRITE_TAC [r6, (← GSYM SUM_NEG)] THEN MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC [FINITE_DELETE, FINITE_DIFF, IN_DELETE, IN_DIFF] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC r5 THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [FUN_IN_IMAGE]], ALL_TAC] THEN SUBGOAL_THEN (← q r"sum (s DELETE j)
          (\i. abs((c:(A->real)->real)(p i) *
                   log((p:K->A->real) i ((d:K->A) j)))) =
        --(sum (s DELETE j)
             (\i. c(p i) * log(p i (d j))))") SUBST1_TAC THENL [REWRITE_TAC [(← GSYM SUM_NEG)] THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC (← q r"i:K") THEN REWRITE_TAC [IN_DELETE] THEN STRIP_TAC THEN REWRITE_TAC [] THEN MATCH_MP_TAC r4 THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"\i. (c:(A->real)->real)(p i) * log((p:K->A->real) i ((d:K->A) j))"), (← q r"s:K->bool"), (← q r"j:K")] SUM_DELETE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"?z a. !j. j IN s
                ==> z j IN ring_carrier k /\
                    (?m. 1 <= m /\ ring_pow k (z j) m = ring_1 k) /\
                    (d:K->A) j =
                    ring_mul k (z j)
                     (group_sum (unit_group(ring_of_integers k)) s
                       (\l. group_zpow (unit_group(ring_of_integers k))
                                       ((e:K->A) l) (a j l)))") STRIP_ASSUME_TAC THENL [REWRITE_TAC [(← GSYM SKOLEM_THM), (← GSYM RIGHT_IMP_EXISTS_THM)] THEN X_GEN_TAC (← q r"j:K") THEN DISCH_TAC THEN REMOVE_THEN "gen" MATCH_MP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"j:K"))) THEN ASM_REWRITE_TAC [] THEN SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"c:(A->real)->real"), (← q r"s:K->bool"), (← q r"e:K->A"), (← q r"d:K->A"), (← q r"z:K->A"), (← q r"a:K->K->int"), (← q r"p:K->A->real")] NUMBER_FIELD_LOG_MATRIX_CHANGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN SUBST_ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun z1 => (do let z2 ← (do let z3 ← (pure z1); pure (concl z3)); pure (is_neg z2))))) THEN REWRITE_TAC [REAL_ENTIRE, DE_MORGAN_THM] THEN SIMP_TAC [])

  let NUMBER_FIELD_LOG_MATRIX_SYSTEM ← prove
    r"!k (c:(A->real)->real) (s:K->bool) (e:K->A) e' (p:K->A->real).
        number_field k /\
        (!v. v IN infinite_places k ==> &0 < c v) /\
        (!u. ring_unit (ring_of_integers k) u
             ==> sum (infinite_places k) (\v. c v * log(v u)) = &0) /\
        FINITE s /\ CARD s = CARD(infinite_places k) - 1 /\
        (!i. i IN s ==> ring_unit (ring_of_integers k) (e i)) /\
        (!u. ring_unit (ring_of_integers k) u
             ==> ?z n. z IN ring_carrier k /\
                       (?m. 1 <= m /\ ring_pow k z m = ring_1 k) /\
                       u = ring_mul k z
                            (group_sum (unit_group(ring_of_integers k)) s
                              (\i. group_zpow (unit_group(ring_of_integers k))
                                              (e i) (n i)))) /\
        (!i. i IN s ==> ring_unit (ring_of_integers k) (e' i)) /\
        (!u. ring_unit (ring_of_integers k) u
             ==> ?z n. z IN ring_carrier k /\
                       (?m. 1 <= m /\ ring_pow k z m = ring_1 k) /\
                       u = ring_mul k z
                            (group_sum (unit_group(ring_of_integers k)) s
                              (\i. group_zpow (unit_group(ring_of_integers k))
                                              (e' i) (n i)))) /\
        (!i. i IN s ==> p i IN infinite_places k) /\
        (!i j. i IN s /\ j IN s /\ p i = p j ==> i = j)
        ==> abs(ring_det real_ring s (\i j. c(p i) * log(p i (e' j)))) =
            abs(ring_det real_ring s (\i j. c(p i) * log(p i (e j))))"
    (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "gen") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "gen'") STRIP_ASSUME_TAC))))))))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"c:(A->real)->real"), (← q r"s:K->bool"), (← q r"e:K->A"), (← q r"p:K->A->real")] NUMBER_FIELD_LOG_MATRIX_NONZERO) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN SUBGOAL_THEN (← q r"?z a. !j. j IN s
              ==> z j IN ring_carrier k /\
                  (?m. 1 <= m /\ ring_pow k (z j) m = ring_1 k) /\
                  (e':K->A) j =
                  ring_mul k (z j)
                   (group_sum (unit_group(ring_of_integers k)) s
                     (\l. group_zpow (unit_group(ring_of_integers k))
                                     ((e:K->A) l) (a j l)))") STRIP_ASSUME_TAC THENL [REWRITE_TAC [(← GSYM SKOLEM_THM), (← GSYM RIGHT_IMP_EXISTS_THM)] THEN X_GEN_TAC (← q r"j:K") THEN DISCH_TAC THEN USE_THEN "gen" (MP_TAC o (SPEC (← q r"(e':K->A) j"))) THEN ANTS_TAC THENL [ASM_MESON_TAC [], DISCH_THEN ACCEPT_TAC], ALL_TAC] THEN SUBGOAL_THEN (← q r"?z' b. !j. j IN s
               ==> z' j IN ring_carrier k /\
                   (?m. 1 <= m /\ ring_pow k (z' j) m = ring_1 k) /\
                   (e:K->A) j =
                   ring_mul k (z' j)
                    (group_sum (unit_group(ring_of_integers k)) s
                      (\l. group_zpow (unit_group(ring_of_integers k))
                                      ((e':K->A) l) (b j l)))") STRIP_ASSUME_TAC THENL [REWRITE_TAC [(← GSYM SKOLEM_THM), (← GSYM RIGHT_IMP_EXISTS_THM)] THEN X_GEN_TAC (← q r"j:K") THEN DISCH_TAC THEN USE_THEN "gen'" (MP_TAC o (SPEC (← q r"(e:K->A) j"))) THEN ANTS_TAC THENL [ASM_MESON_TAC [], DISCH_THEN ACCEPT_TAC], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"c:(A->real)->real"), (← q r"s:K->bool"), (← q r"e:K->A"), (← q r"e':K->A"), (← q r"z:K->A"), (← q r"a:K->K->int"), (← q r"p:K->A->real")] NUMBER_FIELD_LOG_MATRIX_CHANGE) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"c:(A->real)->real"), (← q r"s:K->bool"), (← q r"e':K->A"), (← q r"e:K->A"), (← q r"z':K->A"), (← q r"b:K->K->int"), (← q r"p:K->A->real")] NUMBER_FIELD_LOG_MATRIX_CHANGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], POP_ASSUM MP_TAC] THEN MAP_EVERY (fun t => tactic_of do pure (MP_TAC (← BETA_RULE (← ISPECL [(← q r"s:K->bool"), t] RING_DET_REAL_OF_INT)) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, DISCH_THEN SUBST1_TAC])) [(← q r"\l j. (a:K->K->int) j l"), (← q r"\l j. (b:K->K->int) j l")] THEN ABBREV_TAC (← q r"X = ring_det integer_ring s (\l j. (a:K->K->int) j l)") THEN ABBREV_TAC (← q r"Y = ring_det integer_ring s (\l j. (b:K->K->int) j l)") THEN ABBREV_TAC (← q r"D = ring_det real_ring s
          (\i j. (c:(A->real)->real)(p i) *
                 log((p:K->A->real) i ((e:K->A) j)))") THEN ABBREV_TAC (← q r"D' = ring_det real_ring s
          (\i j. (c:(A->real)->real)(p i) *
                 log((p:K->A->real) i ((e':K->A) j)))") THEN DISCH_TAC THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"real_of_int X * real_of_int Y = &1") MP_TAC THENL [SUBGOAL_THEN (← q r"D * (real_of_int X * real_of_int Y) = D * &1") MP_TAC THENL [REWRITE_TAC [REAL_MUL_ASSOC, REAL_MUL_RID] THEN UNDISCH_TAC (← q r"D' = D * real_of_int X") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN UNDISCH_TAC (← q r"D = D' * real_of_int Y") THEN DISCH_THEN (ACCEPT_TAC o SYM), ASM_REWRITE_TAC [REAL_EQ_MUL_LCANCEL]], ALL_TAC] THEN REWRITE_TAC [(← GSYM int_mul_th), (← GSYM int_of_num_th), (← GSYM int_eq)] THEN REWRITE_TAC [INT_MUL_EQ_1] THEN DISCH_THEN (DISJ_CASES_THEN (MP_TAC o ((AP_TERM (← q r"real_of_int")) o CONJUNCT1))) THEN REWRITE_TAC [int_of_num_th, int_neg_th] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"D' = D * real_of_int X") THEN DISCH_THEN SUBST1_TAC THEN POP_ASSUM SUBST1_TAC THEN REAL_ARITH_TAC)

  let NUMBER_FIELD_LOG_MATRIX_INVARIANT ← prove
    r"!k (c:(A->real)->real) (s:K->bool) (e:K->A) (p:K->A->real)
     (s':L->bool) (e':L->A) (p':L->A->real).
        number_field k /\
        (!v. v IN infinite_places k ==> &0 < c v) /\
        (!u. ring_unit (ring_of_integers k) u
             ==> sum (infinite_places k) (\v. c v * log(v u)) = &0) /\
        FINITE s /\ CARD s = CARD(infinite_places k) - 1 /\
        (!i. i IN s ==> ring_unit (ring_of_integers k) (e i)) /\
        (!u. ring_unit (ring_of_integers k) u
             ==> ?z n. z IN ring_carrier k /\
                       (?m. 1 <= m /\ ring_pow k z m = ring_1 k) /\
                       u = ring_mul k z
                            (group_sum (unit_group(ring_of_integers k)) s
                              (\i. group_zpow (unit_group(ring_of_integers k))
                                              (e i) (n i)))) /\
        (!i. i IN s ==> p i IN infinite_places k) /\
        (!i j. i IN s /\ j IN s /\ p i = p j ==> i = j) /\
        FINITE s' /\ CARD s' = CARD(infinite_places k) - 1 /\
        (!i. i IN s' ==> ring_unit (ring_of_integers k) (e' i)) /\
        (!u. ring_unit (ring_of_integers k) u
             ==> ?z n. z IN ring_carrier k /\
                       (?m. 1 <= m /\ ring_pow k z m = ring_1 k) /\
                       u = ring_mul k z
                            (group_sum (unit_group(ring_of_integers k)) s'
                              (\i. group_zpow (unit_group(ring_of_integers k))
                                              (e' i) (n i)))) /\
        (!i. i IN s' ==> p' i IN infinite_places k) /\
        (!i j. i IN s' /\ j IN s' /\ p' i = p' j ==> i = j)
        ==> abs(ring_det real_ring s' (\i j. c(p' i) * log(p' i (e' j)))) =
            abs(ring_det real_ring s (\i j. c(p i) * log(p i (e j))))"
    (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "gen") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "pinj") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "gen'") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "p'inj"))))))))))))))) THEN MP_TAC (← ISPECL [(← q r"s:K->bool"), (← q r"s':L->bool")] CARD_EQ_BIJECTION) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"b:K->L") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "binj")))) THEN SUBGOAL_THEN (← q r"s' = IMAGE (b:K->L) s") SUBST_ALL_TAC THENL [REWRITE_TAC [EXTENSION, IN_IMAGE] THEN ASM_MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"real_ring"), (← q r"b:K->L"), (← q r"s:K->bool"), (← q r"\i j. (c:(A->real)->real)((p':L->A->real) i) * log(p' i ((e':L->A) j))")] RING_DET_REINDEX) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"infinite_places(k:A ring)"), (← q r"s:K->bool"), (← q r"\v j. (c:(A->real)->real) v * log(v((e':L->A)((b:K->L) j)))"), (← q r"p:K->A->real"), (← q r"\i. (p':L->A->real)((b:K->L) i)")] RING_DET_REAL_ROWS_OMIT) THEN REWRITE_TAC [] THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_INFINITE_PLACES] THEN CONJ_TAC THENL [USE_THEN "pinj" ACCEPT_TAC, MAP_EVERY X_GEN_TAC [(← q r"i:K"), (← q r"j:K")] THEN STRIP_TAC THEN USE_THEN "binj" MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN USE_THEN "p'inj" MATCH_MP_TAC THEN ASM_SIMP_TAC [FUN_IN_IMAGE]], DISCH_THEN SUBST1_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"c:(A->real)->real"), (← q r"s:K->bool"), (← q r"e:K->A"), (← q r"\i. (e':L->A)((b:K->L) i)"), (← q r"p:K->A->real")] NUMBER_FIELD_LOG_MATRIX_SYSTEM) THEN REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ASM_MESON_TAC [FUN_IN_IMAGE], ALL_TAC] THEN X_GEN_TAC (← q r"u:A") THEN DISCH_TAC THEN REMOVE_THEN "gen'" (MP_TAC o (SPEC (← q r"u:A"))) THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"z:A"), (← q r"n:L->int")] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN MAP_EVERY EXISTS_TAC [(← q r"z:A"), (← q r"\i. (n:L->int)((b:K->L) i)")] THEN ASM_REWRITE_TAC [] THEN AP_TERM_TAC THEN MP_TAC (← ISPECL [(← q r"unit_group(ring_of_integers k):A group"), (← q r"b:K->L"), (← q r"\i. group_zpow (unit_group(ring_of_integers k)) ((e':L->A) i)
                    ((n:L->int) i)"), (← q r"s:K->bool")] GROUP_SUM_IMAGE) THEN ANTS_TAC THENL [REWRITE_TAC [ABELIAN_UNIT_GROUP] THEN USE_THEN "binj" ACCEPT_TAC, DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [o_DEF]])

  -- @@RETURN BEGIN
  return { REAL_MATRIX_SOLVE, RING_DET_REAL_OF_INT, RING_DET_REAL_ROW_NEG_SUM,
           RING_DET_REAL_ROWS_SAME_IMAGE, RING_DET_REAL_ROWS_OMIT,
           GROUP_REAL_MULTIPLICATIVE_LOG_SUM_ZPOW, NUMBER_FIELD_LOG_UNIT_SUM,
           NUMBER_FIELD_LOG_UNIT_EQ_0, NUMBER_FIELD_LOG_UNIT_COMBINATION,
           NUMBER_FIELD_UNIT_DOMINANT_INFINITE_PLACE, NUMBER_FIELD_LOG_MATRIX_CHANGE,
           NUMBER_FIELD_LOG_MATRIX_NONZERO, NUMBER_FIELD_LOG_MATRIX_SYSTEM,
           NUMBER_FIELD_LOG_MATRIX_INVARIANT }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- regulator.ml phrases from line 667 to 1018                             -/
/- ---------------------------------------------------------------------- -/

structure Regulator02 where
  -- @@FIELDS
  NUMBER_FIELD_LOG_UNITS_LATTICE : thm
  INFINITE_PLACES_LOCAL_DEGREES : thm
  number_field_regulator : thm
  NUMBER_FIELD_REGULATOR_SYSTEM_EXISTS : thm
  NUMBER_FIELD_REGULATOR : thm
  NUMBER_FIELD_REGULATOR_POS : thm
  NUMBER_FIELD_REGULATOR_RANK_0 : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupRegulator02 [HolBase] (D : RegulatorDeps) (BRegulator01 : Regulator01) :
    ExceptT String IO Regulator02 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, REAL_ARITH,
        REAL_ARITH_TAC, TAUT, new_definition, .. } := D
  let { ABELIAN_UNIT_GROUP, CARD_DELETE, CARD_EQ_BIJECTION, CARD_NUMSEG_LT,
        COMPLEX_EMBEDDINGS_NONEMPTY, EMPTY_GSPEC, EQ_TRANS, EXISTS_UNIQUE_THM,
        EXTENSION, FINITE_DELETE, FINITE_IMAGE, FINITE_INFINITE_PLACES,
        FINITE_NUMSEG_LT, GROUP_SUM_IMAGE, HAS_SIZE, HAS_SIZE_INDEX, IMAGE_EQ_EMPTY,
        INFINITE_PLACES_DEGREE, INTEGRAL_DOMAIN_REAL_RING, IN_DELETE, IN_ELIM_THM,
        IN_IMAGE, IN_INSERT, IN_UNIV, LEFT_IMP_EXISTS_THM, LT, MEMBER_NOT_EMPTY,
        MONO_EXISTS, NUMBER_FIELD_FUNDAMENTAL_UNITS, REAL_ABS_NZ, REAL_MUL_RNEG,
        REAL_NEG_EQ, REAL_NEG_NEG, REAL_OF_NUM_LT, REAL_RING_CLAUSES, REAL_RING_SUM,
        RING_DET_DEPENDENT_COLUMNS, RING_DET_EMPTY, SELECT_UNIQUE, SUB_REFL,
        SUM_CLAUSES, SUM_EQ, SUM_IMAGE, SUM_LMUL, SUM_NEG, SUM_SWAP, infinite_places,
        o_DEF, .. } := D.core1
  let { NUMBER_FIELD_LOG_MATRIX_INVARIANT, NUMBER_FIELD_LOG_MATRIX_NONZERO,
        NUMBER_FIELD_LOG_UNIT_COMBINATION, NUMBER_FIELD_LOG_UNIT_SUM,
        REAL_MATRIX_SOLVE, .. } := BRegulator01
  -- @@SCOPE END

  let NUMBER_FIELD_LOG_UNITS_LATTICE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"(a:real) + b = &0 <=> a = --b")
    let r2 ← REAL_ARITH (← q r"(a:real) + b = &0 <=> a = --b")
    let r6 ← TAUT (← q r"q ==> ~q ==> p")
    prove
      r"!k (c:(A->real)->real) (s:K->bool) (e:K->A).
          number_field k /\
          (!v. v IN infinite_places k ==> &0 < c v) /\
          (!u. ring_unit (ring_of_integers k) u
               ==> sum (infinite_places k) (\v. c v * log(v u)) = &0) /\
          FINITE s /\ CARD s = CARD(infinite_places k) - 1 /\
          (!i. i IN s ==> ring_unit (ring_of_integers k) (e i)) /\
          (!u. ring_unit (ring_of_integers k) u
               ==> ?z n. z IN ring_carrier k /\
                         (?m. 1 <= m /\ ring_pow k z m = ring_1 k) /\
                         u = ring_mul k z
                              (group_sum (unit_group(ring_of_integers k)) s
                                (\i. group_zpow (unit_group(ring_of_integers k))
                                                (e i) (n i))))
          ==> (!x. (!v. v IN infinite_places k
                        ==> sum s (\i. x i * c v * log(v(e i))) = &0)
                   ==> !i. i IN s ==> x i = &0) /\
              (!y. sum (infinite_places k) y = &0
                   ==> ?x. !v. v IN infinite_places k
                               ==> y v = sum s (\i. x i * c v * log(v(e i)))) /\
              (!u. ring_unit (ring_of_integers k) u
                   ==> ?n. !v. v IN infinite_places k
                               ==> c v * log(v u) =
                                   sum s (\i. real_of_int(n i) * c v *
                                              log(v(e i))))"
      (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sum") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gen"))))))) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITE_INFINITE_PLACES)) THEN SUBGOAL_THEN (← q r"?v0:A->real. v0 IN infinite_places k") STRIP_ASSUME_TAC THENL [REWRITE_TAC [MEMBER_NOT_EMPTY, infinite_places, IMAGE_EQ_EMPTY] THEN ASM_SIMP_TAC [COMPLEX_EMBEDDINGS_NONEMPTY], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"s:K->bool"), (← q r"infinite_places(k:A ring) DELETE v0")] CARD_EQ_BIJECTION) THEN ASM_SIMP_TAC [FINITE_DELETE, CARD_DELETE] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"p:K->A->real") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pinj")))) THEN SUBGOAL_THEN (← q r"infinite_places k = (v0:A->real) INSERT IMAGE p (s:K->bool)") ASSUME_TAC THENL [REWRITE_TAC [EXTENSION, IN_INSERT, IN_IMAGE] THEN RULE_ASSUM_TAC (REWRITE_RULE [IN_DELETE]) THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. i IN s ==> (p:K->A->real) i IN infinite_places k /\
                                 ~(p i = v0)") ASSUME_TAC THENL [RULE_ASSUM_TAC (REWRITE_RULE [IN_DELETE]) THEN ASM_MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"c:(A->real)->real"), (← q r"s:K->bool"), (← q r"e:K->A"), (← q r"p:K->A->real")] NUMBER_FIELD_LOG_MATRIX_NONZERO) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"M = \i j. (c:(A->real)->real)((p:K->A->real) i) *
                          log(p i ((e:K->A) j))") THEN DISCH_TAC THEN CONJ_TAC THENL [X_GEN_TAC (← q r"x:K->real") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"?i. i IN s /\ ~((x:K->real) i = &0)") THENL [ALL_TAC, ASM_MESON_TAC []] THEN UNDISCH_TAC (← q r"~(ring_det real_ring s (M:K->K->real) = &0)") THEN MATCH_MP_TAC r6 THEN MP_TAC (← ISPECL [(← q r"real_ring"), (← q r"s:K->bool"), (← q r"M:K->K->real"), (← q r"x:K->real")] RING_DET_DEPENDENT_COLUMNS) THEN REWRITE_TAC [INTEGRAL_DOMAIN_REAL_RING, REAL_RING_CLAUSES, IN_UNIV, REAL_RING_SUM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"i:K") THEN DISCH_TAC THEN EXPAND_TAC "M" THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"(p:K->A->real) i")) o (checkM (fun z3 => (do let z4 ← (do let z5 ← (pure z3); pure (concl z5)); pure (is_forall z4)))))) THEN ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC [] THEN REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"!f. sum (infinite_places k) f = f v0 + sum s (\i. f((p:K->A->real) i))") ASSUME_TAC THENL [GEN_TAC THEN FIRST_ASSUM (fun th => GEN_REWRITE_TAC (LAND_CONV o (RATOR_CONV o RAND_CONV)) [th]) THEN MP_TAC (← ISPECL [(← q r"v0:A->real"), (← q r"f:(A->real)->real"), (← q r"IMAGE (p:K->A->real) s")] (← CONJUNCT2 SUM_CLAUSES)) THEN ANTS_TAC THENL [MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN SUBGOAL_THEN (← q r"~((v0:A->real) IN IMAGE p (s:K->bool))") (fun th => REWRITE_TAC [th]) THENL [REWRITE_TAC [IN_IMAGE] THEN ASM_MESON_TAC [], ALL_TAC] THEN AP_TERM_TAC THEN MP_TAC (← ISPECL [(← q r"p:K->A->real"), (← q r"f:(A->real)->real"), (← q r"s:K->bool")] SUM_IMAGE) THEN ANTS_TAC THENL [USE_THEN "pinj" ACCEPT_TAC, DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [o_DEF], ALL_TAC] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"y:(A->real)->real") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"s:K->bool"), (← q r"M:K->K->real"), (← q r"\i. (y:(A->real)->real)((p:K->A->real) i)")] REAL_MATRIX_SOLVE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"x:K->real") ((LABEL_TAC "sol") o BETA_RULE)) THEN EXISTS_TAC (← q r"x:K->real") THEN SUBGOAL_THEN (← q r"!i. i IN s
            ==> (y:(A->real)->real)(p i) =
                sum s (\j. x j * (c:(A->real)->real)(p i) *
                           log((p:K->A->real) i ((e:K->A) j)))") ASSUME_TAC THENL [X_GEN_TAC (← q r"i:K") THEN DISCH_TAC THEN USE_THEN "sol" (MP_TAC o (SPEC (← q r"i:K"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN EXPAND_TAC "M" THEN MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC [] THEN REAL_ARITH_TAC, ALL_TAC] THEN X_GEN_TAC (← q r"v:A->real") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"v = (v0:A->real) \/ ?i. i IN s /\ v = (p:K->A->real) i") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"(v:A->real) IN infinite_places k") THEN FIRST_ASSUM (fun th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN REWRITE_TAC [IN_INSERT, IN_IMAGE] THEN MESON_TAC [], ALL_TAC, FIRST_X_ASSUM SUBST1_TAC THEN ASM_SIMP_TAC []] THEN FIRST_X_ASSUM SUBST1_TAC THEN UNDISCH_TAC (← q r"sum (infinite_places k) (y:(A->real)->real) = &0") THEN ASM_REWRITE_TAC [r2] THEN DISCH_THEN SUBST1_TAC THEN SUBGOAL_THEN (← q r"!j. j IN s
            ==> (c:(A->real)->real) v0 * log(v0((e:K->A) j)) =
                --sum s (\i. c((p:K->A->real) i) * log(p i (e j)))") ASSUME_TAC THENL [X_GEN_TAC (← q r"j:K") THEN DISCH_TAC THEN USE_THEN "sum" (MP_TAC o (SPEC (← q r"(e:K->A) j"))) THEN ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [r1], ALL_TAC] THEN TRANS_TAC EQ_TRANS (← q r"sum s (\j. (x:K->real) j *
                   --sum s (\i. (c:(A->real)->real)((p:K->A->real) i) *
                                log(p i ((e:K->A) j))))") THEN CONJ_TAC THENL [ALL_TAC, MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC (← q r"j:K") THEN DISCH_TAC THEN ASM_SIMP_TAC []] THEN REWRITE_TAC [REAL_MUL_RNEG, SUM_NEG, REAL_NEG_EQ, REAL_NEG_NEG] THEN REWRITE_TAC [(← GSYM SUM_LMUL)] THEN wPart rand (lhand o rand) SUM_SWAP THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC (← q r"i:K") THEN DISCH_TAC THEN ASM_SIMP_TAC [] THEN MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC [] THEN REAL_ARITH_TAC, ALL_TAC] THEN X_GEN_TAC (← q r"u:A") THEN DISCH_TAC THEN USE_THEN "gen" (MP_TAC o (SPEC (← q r"u:A"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"z:A"), (← q r"n:K->int")] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN EXISTS_TAC (← q r"n:K->int") THEN X_GEN_TAC (← q r"v:A->real") THEN DISCH_TAC THEN wPart (rand o lhand) (lhand o rand) NUMBER_FIELD_LOG_UNIT_COMBINATION THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [(← GSYM SUM_LMUL)] THEN MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC [] THEN REAL_ARITH_TAC)

  let INFINITE_PLACES_LOCAL_DEGREES ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"0 < n <=> 1 <= n")
    prove
      r"!k:A ring.
          number_field k
          ==> (!v. v IN infinite_places k
                   ==> (&0:real) < &(CARD {g | g IN complex_embeddings k /\
                                        (\x. norm(g x)) = v})) /\
              (!u. ring_unit (ring_of_integers k) u
                   ==> sum (infinite_places k)
                         (\v. &(CARD {g | g IN complex_embeddings k /\
                                          (\x. norm(g x)) = v}) *
                              log(v u)) = &0)"
      (REPEAT STRIP_TAC THENL [REWRITE_TAC [REAL_OF_NUM_LT, r1] THEN ASM_MESON_TAC [INFINITE_PLACES_DEGREE], ASM_SIMP_TAC [NUMBER_FIELD_LOG_UNIT_SUM]])

  let number_field_regulator ← new_definition
    r"number_field_regulator (k:A ring) =
  @R. ?(e:num->A) (w:num->A->real).
        (!i. i < CARD(infinite_places k) - 1
             ==> ring_unit (ring_of_integers k) (e i)) /\
        (!u. ring_unit (ring_of_integers k) u
             ==> ?z n. z IN ring_carrier k /\
                       (?m. 1 <= m /\ ring_pow k z m = ring_1 k) /\
                       u = ring_mul k z
                            (group_sum (unit_group(ring_of_integers k))
                              {i | i < CARD(infinite_places k) - 1}
                              (\i. group_zpow (unit_group(ring_of_integers k))
                                              (e i) (n i)))) /\
        (!i. i < CARD(infinite_places k) - 1 ==> w i IN infinite_places k) /\
        (!i j. i < CARD(infinite_places k) - 1 /\
               j < CARD(infinite_places k) - 1 /\ w i = w j
               ==> i = j) /\
        R = abs(ring_det real_ring {i | i < CARD(infinite_places k) - 1}
                  (\i j. &(CARD {g | g IN complex_embeddings k /\
                                     (\x. norm(g x)) = w i}) *
                         log(w i (e j))))"

  let NUMBER_FIELD_REGULATOR_SYSTEM_EXISTS ← prove
    r"!k:A ring.
        number_field k
        ==> ?(e:num->A) (w:num->A->real).
              (!i. i < CARD(infinite_places k) - 1
                   ==> ring_unit (ring_of_integers k) (e i)) /\
              (!u. ring_unit (ring_of_integers k) u
                   ==> ?z n. z IN ring_carrier k /\
                             (?m. 1 <= m /\ ring_pow k z m = ring_1 k) /\
                             u = ring_mul k z
                                  (group_sum (unit_group(ring_of_integers k))
                                    {i | i < CARD(infinite_places k) - 1}
                                    (\i. group_zpow
                                          (unit_group(ring_of_integers k))
                                          (e i) (n i)))) /\
              (!i. i < CARD(infinite_places k) - 1
                   ==> w i IN infinite_places k) /\
              (!i j. i < CARD(infinite_places k) - 1 /\
                     j < CARD(infinite_places k) - 1 /\ w i = w j
                     ==> i = j)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP NUMBER_FIELD_FUNDAMENTAL_UNITS)) THEN ABBREV_TAC (← q r"r = CARD(infinite_places(k:A ring)) - 1") THEN DISCH_THEN (X_CHOOSE_THEN (← q r"t:A->bool") (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (fun (_ : thm) => ALL_TAC) (LABEL_TAC "gen"))))) THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"e:num->A") STRIP_ASSUME_TAC) o (MATCH_MP HAS_SIZE_INDEX)) THEN SUBGOAL_THEN (← q r"t = IMAGE (e:num->A) {i | i < r}") ASSUME_TAC THENL [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i j. i IN {i | i < r} /\ j IN {i | i < r} /\
                      (e:num->A) i = e j ==> i = j") ASSUME_TAC THENL [REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPEC (← q r"infinite_places(k:A ring)") HAS_SIZE_INDEX) THEN DISCH_THEN (MP_TAC o (SPEC (← q r"CARD(infinite_places(k:A ring))"))) THEN ASM_SIMP_TAC [HAS_SIZE, FINITE_INFINITE_PLACES] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"w:num->A->real") STRIP_ASSUME_TAC) THEN MAP_EVERY EXISTS_TAC [(← q r"e:num->A"), (← q r"w:num->A->real")] THEN REPEAT CONJ_TAC THENL [ASM_MESON_TAC [], X_GEN_TAC (← q r"u:A") THEN DISCH_TAC THEN REMOVE_THEN "gen" (MP_TAC o (SPEC (← q r"u:A"))) THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"z:A"), (← q r"n:A->int")] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN MAP_EVERY EXISTS_TAC [(← q r"z:A"), (← q r"\i. (n:A->int)((e:num->A) i)")] THEN ASM_REWRITE_TAC [] THEN AP_TERM_TAC THEN MP_TAC (← ISPECL [(← q r"unit_group(ring_of_integers k):A group"), (← q r"e:num->A"), (← q r"\x. group_zpow (unit_group(ring_of_integers k)) x ((n:A->int) x)"), (← q r"{i:num | i < r}")] GROUP_SUM_IMAGE) THEN ANTS_TAC THENL [REWRITE_TAC [ABELIAN_UNIT_GROUP] THEN FIRST_ASSUM ACCEPT_TAC, DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [o_DEF]], X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN FIRST_X_ASSUM (MATCH_MP_TAC o (checkM (fun z7 => (do let z8 ← (do let z9 ← (pure z7); pure (concl z9)); pure (is_forall z8))))) THEN ASM_ARITH_TAC, MAP_EVERY X_GEN_TAC [(← q r"i:num"), (← q r"j:num")] THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"(w:num->A->real) i")) o (checkM (fun z4 => (do let z5 ← (do let z6 ← (pure z4); pure (concl z6)); pure (is_forall z5)))))) THEN ANTS_TAC THENL [FIRST_X_ASSUM (MATCH_MP_TAC o (checkM (fun z1 => (do let z2 ← (do let z3 ← (pure z1); pure (concl z3)); pure (is_forall z2))))) THEN ASM_ARITH_TAC, REWRITE_TAC [EXISTS_UNIQUE_THM] THEN DISCH_THEN (MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC]])

  let NUMBER_FIELD_REGULATOR ← prove
    r"!k (s:K->bool) (e:K->A) (p:K->A->real).
        number_field k /\ s HAS_SIZE (CARD(infinite_places k) - 1) /\
        (!i. i IN s ==> ring_unit (ring_of_integers k) (e i)) /\
        (!u. ring_unit (ring_of_integers k) u
             ==> ?z n. z IN ring_carrier k /\
                       (?m. 1 <= m /\ ring_pow k z m = ring_1 k) /\
                       u = ring_mul k z
                            (group_sum (unit_group(ring_of_integers k)) s
                              (\i. group_zpow (unit_group(ring_of_integers k))
                                              (e i) (n i)))) /\
        (!i. i IN s ==> p i IN infinite_places k) /\
        (!i j. i IN s /\ j IN s /\ p i = p j ==> i = j)
        ==> number_field_regulator k =
            abs(ring_det real_ring s
                  (\i j. &(CARD {g | g IN complex_embeddings k /\
                                     (\x. norm(g x)) = p i}) *
                         log(p i (e j))))"
    (REWRITE_TAC [HAS_SIZE] THEN REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP INFINITE_PLACES_LOCAL_DEGREES)) THEN REWRITE_TAC [number_field_regulator] THEN MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC (← q r"y:real") THEN EQ_TAC THENL [REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"e':num->A"), (← q r"w:num->A->real")] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC (← BETA_RULE (← ISPECL [(← q r"k:A ring"), (← q r"\v. &(CARD {g | g IN complex_embeddings (k:A ring) /\
                       (\x. norm(g x)) = v}):real"), (← q r"s:K->bool"), (← q r"e:K->A"), (← q r"p:K->A->real"), (← q r"{i:num | i < CARD(infinite_places(k:A ring)) - 1}"), (← q r"e':num->A"), (← q r"w:num->A->real")] NUMBER_FIELD_LOG_MATRIX_INVARIANT)) THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT, CARD_NUMSEG_LT, IN_ELIM_THM], DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP NUMBER_FIELD_REGULATOR_SYSTEM_EXISTS)) THEN REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"e':num->A") THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"w:num->A->real") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONV_TAC SYM_CONV THEN MP_TAC (← BETA_RULE (← ISPECL [(← q r"k:A ring"), (← q r"\v. &(CARD {g | g IN complex_embeddings (k:A ring) /\
                       (\x. norm(g x)) = v}):real"), (← q r"s:K->bool"), (← q r"e:K->A"), (← q r"p:K->A->real"), (← q r"{i:num | i < CARD(infinite_places(k:A ring)) - 1}"), (← q r"e':num->A"), (← q r"w:num->A->real")] NUMBER_FIELD_LOG_MATRIX_INVARIANT)) THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT, CARD_NUMSEG_LT, IN_ELIM_THM]])

  let NUMBER_FIELD_REGULATOR_POS ← prove
    r"!k:A ring. number_field k ==> &0 < number_field_regulator k"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP INFINITE_PLACES_LOCAL_DEGREES)) THEN FIRST_ASSUM ((X_CHOOSE_THEN (← q r"e:num->A") (X_CHOOSE_THEN (← q r"w:num->A->real") STRIP_ASSUME_TAC)) o (MATCH_MP NUMBER_FIELD_REGULATOR_SYSTEM_EXISTS)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{i:num | i < CARD(infinite_places(k:A ring)) - 1}"), (← q r"e:num->A"), (← q r"w:num->A->real")] NUMBER_FIELD_REGULATOR) THEN ASM_REWRITE_TAC [HAS_SIZE, FINITE_NUMSEG_LT, CARD_NUMSEG_LT, IN_ELIM_THM] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [(← GSYM REAL_ABS_NZ)] THEN MP_TAC (← BETA_RULE (← ISPECL [(← q r"k:A ring"), (← q r"\v. &(CARD {g | g IN complex_embeddings (k:A ring) /\
                       (\x. norm(g x)) = v}):real"), (← q r"{i:num | i < CARD(infinite_places(k:A ring)) - 1}"), (← q r"e:num->A"), (← q r"w:num->A->real")] NUMBER_FIELD_LOG_MATRIX_NONZERO)) THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT, CARD_NUMSEG_LT, IN_ELIM_THM])

  let NUMBER_FIELD_REGULATOR_RANK_0 ← prove
    r"!k:A ring.
        number_field k /\ CARD(infinite_places k) = 1
        ==> number_field_regulator k = &1"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM ((X_CHOOSE_THEN (← q r"e:num->A") (X_CHOOSE_THEN (← q r"w:num->A->real") STRIP_ASSUME_TAC)) o (MATCH_MP NUMBER_FIELD_REGULATOR_SYSTEM_EXISTS)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{i:num | i < CARD(infinite_places(k:A ring)) - 1}"), (← q r"e:num->A"), (← q r"w:num->A->real")] NUMBER_FIELD_REGULATOR) THEN REWRITE_TAC [HAS_SIZE, FINITE_NUMSEG_LT, CARD_NUMSEG_LT, IN_ELIM_THM] THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC, DISCH_THEN SUBST1_TAC] THEN ASM_REWRITE_TAC [SUB_REFL, LT, EMPTY_GSPEC, RING_DET_EMPTY, REAL_RING_CLAUSES] THEN REAL_ARITH_TAC)

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_LOG_UNITS_LATTICE, INFINITE_PLACES_LOCAL_DEGREES,
           number_field_regulator, NUMBER_FIELD_REGULATOR_SYSTEM_EXISTS,
           NUMBER_FIELD_REGULATOR, NUMBER_FIELD_REGULATOR_POS,
           NUMBER_FIELD_REGULATOR_RANK_0 }
  -- @@RETURN END

end HolANT.Regulator
