/- ========================================================================= -/
/- ANT: Roots of unity in number fields                                    -/
/- ========================================================================= -/
/- File: HolANT/RootsOfUnity.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/roots_of_unity.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antrootsofunitydiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/isum.ml, Library/products.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, Library/frag.ml, Library/grouptheory.ml, Library/symmetric_group.ml, Library/galois.ml, Library/ring_groups.ml, Library/finite_fields.ml, Library/integer.ml, Library/multiplicative.ml, Library/primitive.ml, ANT/cyclotomic_poly.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/prime_split.ml, ANT/norm_index.ml, ANT/discriminant.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/classgroup.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/relative_degree.ml, ANT/nf_valuation.ml, ANT/integrality.ml, ANT/dedekind_kummer.ml, ANT/power_basis.ml, ANT/cyclotomic_field.ml, ANT/fingen_group.ml, Multivariate/misc.ml, Multivariate/metric.ml, Multivariate/homology.ml, Multivariate/vectors.ml, Multivariate/determinants.ml, Multivariate/topology.ml, Multivariate/convex.ml, Multivariate/paths.ml, Multivariate/polytope.ml, Multivariate/degree.ml, Multivariate/derivatives.ml, Multivariate/integration.ml, Multivariate/measure.ml, Multivariate/complex_algebra.ml, Multivariate/complexes.ml, Multivariate/canal.ml, Multivariate/transcendentals.ml, Multivariate/realanalysis.ml, Multivariate/moretop.ml, Multivariate/cauchy.ml, Multivariate/complex_ring.ml, Multivariate/complex_field.ml, ANT/complex_embeddings.ml, ANT/infinite_places.ml, ANT/linear_forms.ml, ANT/classgroup_group.ml, ANT/finite_field_trace.ml, ANT/ramification.ml, ANT/quadratic.ml, ANT/minkowski_theory.ml, ANT/unit_theorem.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.RootsOfUnity fills them).

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
import HolANT.Algmisc
import HolANT.Integral
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolLibrary.Frag
import HolLibrary.GroupTheory
import HolLibrary.SymmetricGroup
import HolLibrary.Galois
import HolLibrary.RingGroups
import HolLibrary.FiniteFields
import HolLibrary.Integer
import HolLibrary.Multiplicative
import HolLibrary.Primitive
import HolANT.CyclotomicPoly
import HolANT.IdealArith
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.IdealNorm
import HolANT.RingOfIntegers
import HolANT.PrimeSplit
import HolANT.NormIndex
import HolANT.Discriminant
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.Classgroup
import HolANT.TraceForm
import HolANT.RelativeSplit
import HolANT.RelativeDegree
import HolANT.NfValuation
import HolANT.Integrality
import HolANT.DedekindKummer
import HolANT.PowerBasis
import HolANT.CyclotomicField
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
open HolANT.CyclotomicPoly
open HolANT.IdealArith
open HolANT.Dedekind
open HolANT.DedekindStruct
open HolANT.IdealNorm
open HolANT.RingOfIntegers
open HolANT.PrimeSplit
open HolANT.NormIndex
open HolANT.Discriminant
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.Classgroup
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.RelativeDegree
open HolANT.NfValuation
open HolANT.Integrality
open HolANT.DedekindKummer
open HolANT.PowerBasis
open HolANT.CyclotomicField
open HolANT.FingenGroup
open HolANT.ComplexEmbeddings
open HolANT.InfinitePlaces
open HolANT.LinearForms
open HolANT.ClassgroupGroup
open HolANT.FiniteFieldTrace
open HolANT.Ramification
open HolANT.Quadratic
open HolANT.MinkowskiTheory
open HolANT.UnitTheorem

namespace HolANT.RootsOfUnity

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ARITH_EQ COMPLEX_EMBEDDINGS_MONOMORPHISM COMPLEX_EMBEDDINGS_ROOT_OF_UNITY
   COMPLEX_NORM_CX COMPLEX_RING_CLAUSES CONG_IMP_EQ CONG_REFL CONG_RMOD
   COPRIME_2 COPRIME_DIVPROD CX_NEG CYCLOTOMIC_POLY_DEG
   CYCLOTOMIC_POLY_MINIMAL_POLYNOMIAL DIVIDES_ZERO EXTENSION FIELD_NONTRIVIAL
   FIELD_REGULAR HAS_SIZE_IMAGE_INJ HAS_SIZE_NUMSEG_LT IN_ELIM_THM IN_IMAGE
   IN_INSERT LE_1 LE_REFL MEMBER_NOT_EMPTY
   MINIMAL_POLYNOMIAL_DEG_DIVIDES_EXTENSION_DEGREE MOD_LT_EQ MULT_SYM
   NOT_IN_EMPTY NOT_ODD NUMBER_FIELD_IMP_FIELD NUMBER_FIELD_RING_OF_NUM_EQ_0
   NUMBER_FIELD_ROOTS_OF_UNITY_CYCLIC NUMBER_FIELD_UNITS_ROOTS_OF_UNITY
   REAL_EXISTS RING_1 RING_ADD_LNEG RING_HOMOMORPHISM_1 RING_HOMOMORPHISM_NEG
   RING_MUL_LID RING_MUL_LNEG RING_MUL_RNEG RING_NEG RING_NEG_NEG
   RING_OF_INTEGERS_ROOT_OF_UNITY_UNIT RING_OF_INTEGERS_SUBSET RING_OF_NUM_1
   RING_OF_NUM_ADD RING_POW RING_POW_1 RING_POW_2 RING_POW_EQ RING_POW_EQ_1
   RING_POW_MUL RING_POW_ONE RING_POW_RING_ORDER RING_POW_ZERO
   RING_UNIT_IN_CARRIER SUBFIELD_GENERATED SUBSET number_field real_embeddings
   ring_monomorphism : thm)
  deriving Inhabited

/-- What roots_of_unity.ml uses from Session besides theorems. -/
structure RootsOfUnityDeps where
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
/- roots_of_unity.ml phrases from line 40 to 202                          -/
/- ---------------------------------------------------------------------- -/

structure RootsOfUnity where
  -- @@FIELDS
  NUMBER_FIELD_ROOT_OF_UNITY_PHI_DIVIDES : thm
  NUMBER_FIELD_ROOTS_OF_UNITY_CARD : thm
  NUMBER_FIELD_REAL_ROOTS_OF_UNITY : thm
  NUMBER_FIELD_UNITS_EQ_ROOTS_OF_UNITY : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupRootsOfUnity [HolBase] (D : RootsOfUnityDeps) :
    ExceptT String IO RootsOfUnity := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, REAL_ARITH, .. } := D
  let { ARITH_EQ, COMPLEX_EMBEDDINGS_MONOMORPHISM, COMPLEX_EMBEDDINGS_ROOT_OF_UNITY,
        COMPLEX_NORM_CX, COMPLEX_RING_CLAUSES, CONG_IMP_EQ, CONG_REFL, CONG_RMOD,
        COPRIME_2, COPRIME_DIVPROD, CX_NEG, CYCLOTOMIC_POLY_DEG,
        CYCLOTOMIC_POLY_MINIMAL_POLYNOMIAL, DIVIDES_ZERO, EXTENSION, FIELD_NONTRIVIAL,
        FIELD_REGULAR, HAS_SIZE_IMAGE_INJ, HAS_SIZE_NUMSEG_LT, IN_ELIM_THM, IN_IMAGE,
        IN_INSERT, LE_1, LE_REFL, MEMBER_NOT_EMPTY,
        MINIMAL_POLYNOMIAL_DEG_DIVIDES_EXTENSION_DEGREE, MOD_LT_EQ, MULT_SYM,
        NOT_IN_EMPTY, NOT_ODD, NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_RING_OF_NUM_EQ_0,
        NUMBER_FIELD_ROOTS_OF_UNITY_CYCLIC, NUMBER_FIELD_UNITS_ROOTS_OF_UNITY,
        REAL_EXISTS, RING_1, RING_ADD_LNEG, RING_HOMOMORPHISM_1, RING_HOMOMORPHISM_NEG,
        RING_MUL_LID, RING_MUL_LNEG, RING_MUL_RNEG, RING_NEG, RING_NEG_NEG,
        RING_OF_INTEGERS_ROOT_OF_UNITY_UNIT, RING_OF_INTEGERS_SUBSET, RING_OF_NUM_1,
        RING_OF_NUM_ADD, RING_POW, RING_POW_1, RING_POW_2, RING_POW_EQ, RING_POW_EQ_1,
        RING_POW_MUL, RING_POW_ONE, RING_POW_RING_ORDER, RING_POW_ZERO,
        RING_UNIT_IN_CARRIER, SUBFIELD_GENERATED, SUBSET, number_field,
        real_embeddings, ring_monomorphism, .. } := D.core1
  -- @@SCOPE END

  let NUMBER_FIELD_ROOT_OF_UNITY_PHI_DIVIDES ← prove
    r"!k (z:A) m.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = m /\ ~(m = 0)
        ==> phi m divides
            extension_degree (subfield_generated k {ring_0 k},k) I"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"m:num")] CYCLOTOMIC_POLY_MINIMAL_POLYNOMIAL) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"z:A")] MINIMAL_POLYNOMIAL_DEG_DIVIDES_EXTENSION_DEGREE) THEN ANTS_TAC THENL [ASM_MESON_TAC [number_field], ALL_TAC] THEN ASM_REWRITE_TAC [CYCLOTOMIC_POLY_DEG] THEN SUBGOAL_THEN (← q r"~(ring_1 (subfield_generated k {ring_0 k}) =
      ring_0 (subfield_generated k {ring_0 (k:A ring)}))") (fun th => REWRITE_TAC [th]) THEN REWRITE_TAC [SUBFIELD_GENERATED] THEN ASM_MESON_TAC [NUMBER_FIELD_IMP_FIELD, FIELD_NONTRIVIAL])

  let NUMBER_FIELD_ROOTS_OF_UNITY_CARD ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"2 = 1 + 1")
    let r2 ← ARITH_RULE (← q r"1 <= m ==> ~(m = 0)")
    prove
      r"!k:A ring.
          number_field k
          ==> ?w. {x | x IN ring_carrier k /\
                       ?n. 1 <= n /\ ring_pow k x n = ring_1 k} HAS_SIZE w /\
                  EVEN w /\
                  phi w divides
                  extension_degree (subfield_generated k {ring_0 k},k) I"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM ((X_CHOOSE_THEN (← q r"z:A") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"m:num") STRIP_ASSUME_TAC) (LABEL_TAC "gen")))) o (MATCH_MP NUMBER_FIELD_ROOTS_OF_UNITY_CYCLIC)) THEN ABBREV_TAC (← q r"w = ring_order k (z:A)") THEN SUBGOAL_THEN (← q r"~(w = 0)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"m:num")] RING_POW_EQ_1) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE [DIVIDES_ZERO]) THEN ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"~(z:A = ring_0 k)") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"ring_pow k (ring_0 k) m = ring_1 (k:A ring)") THEN ASM_SIMP_TAC [RING_POW_ZERO, r2] THEN ASM_MESON_TAC [FIELD_NONTRIVIAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_regular k (z:A)") ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_REGULAR], ALL_TAC] THEN EXISTS_TAC (← q r"w:num") THEN REPEAT CONJ_TAC THENL [SUBGOAL_THEN (← q r"{x | x IN ring_carrier k /\ ?n. 1 <= n /\ ring_pow k x n = ring_1 k} =
        IMAGE (\j. ring_pow k (z:A) j) {j | j < w}") SUBST1_TAC THENL [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_IMAGE] THEN X_GEN_TAC (← q r"x:A") THEN EQ_TAC THENL [STRIP_TAC THEN USE_THEN "gen" (MP_TAC o (SPEC (← q r"x:A"))) THEN ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"j:num") SUBST1_TAC) THEN EXISTS_TAC (← q r"j MOD w") THEN ASM_SIMP_TAC [MOD_LT_EQ] THEN ASM_SIMP_TAC [RING_POW_EQ] THEN REWRITE_TAC [CONG_RMOD, CONG_REFL], DISCH_THEN (X_CHOOSE_THEN (← q r"j:num") (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN ASM_SIMP_TAC [RING_POW] THEN EXISTS_TAC (← q r"w:num") THEN ASM_SIMP_TAC [LE_1, (← GSYM RING_POW_MUL)] THEN ONCE_REWRITE_TAC [MULT_SYM] THEN ASM_SIMP_TAC [RING_POW_MUL] THEN EXPAND_TAC "w" THEN ASM_SIMP_TAC [RING_POW_RING_ORDER, RING_POW_ONE]], MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN REWRITE_TAC [HAS_SIZE_NUMSEG_LT, IN_ELIM_THM] THEN ASM_SIMP_TAC [RING_POW_EQ] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC (← q r"w:num") THEN ASM_REWRITE_TAC []], SUBGOAL_THEN (← q r"~(ring_neg k (ring_1 k) = ring_1 (k:A ring))") ASSUME_TAC THENL [DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"2")] NUMBER_FIELD_RING_OF_NUM_EQ_0) THEN ASM_REWRITE_TAC [ARITH_EQ] THEN REWRITE_TAC [r1, RING_OF_NUM_ADD, RING_OF_NUM_1] THEN FIRST_X_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [(← SYM th)])) THEN SIMP_TAC [RING_ADD_LNEG, RING_1], ALL_TAC] THEN USE_THEN "gen" (MP_TAC o (SPEC (← q r"ring_neg k (ring_1 k):A"))) THEN ANTS_TAC THENL [SIMP_TAC [RING_NEG, RING_1] THEN EXISTS_TAC (← q r"2") THEN SIMP_TAC [RING_POW_2, RING_MUL_LNEG, RING_MUL_RNEG, RING_NEG_NEG, RING_MUL_LID, RING_1, RING_NEG] THEN ARITH_TAC, DISCH_THEN (X_CHOOSE_THEN (← q r"j:num") (LABEL_TAC "j"))] THEN SUBGOAL_THEN (← q r"w divides j * 2") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"j * 2")] RING_POW_EQ_1) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [RING_POW_MUL] THEN USE_THEN "j" (SUBST1_TAC o SYM) THEN SIMP_TAC [RING_POW_2, RING_MUL_LNEG, RING_MUL_RNEG, RING_NEG_NEG, RING_MUL_LID, RING_1, RING_NEG], ALL_TAC] THEN REWRITE_TAC [(← GSYM NOT_ODD)] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(w:num) divides j") MP_TAC THENL [MATCH_MP_TAC COPRIME_DIVPROD THEN EXISTS_TAC (← q r"2") THEN ONCE_REWRITE_TAC [MULT_SYM] THEN ASM_REWRITE_TAC [COPRIME_2], ALL_TAC] THEN EXPAND_TAC "w" THEN ASM_SIMP_TAC [(← GSYM RING_POW_EQ_1)] THEN USE_THEN "j" (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC [], MATCH_MP_TAC NUMBER_FIELD_ROOT_OF_UNITY_PHI_DIVIDES THEN EXISTS_TAC (← q r"z:A") THEN ASM_REWRITE_TAC []])

  let NUMBER_FIELD_REAL_ROOTS_OF_UNITY ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"abs (a:real) = &1 <=> a = &1 \/ a = -- &1")
    prove
      r"!k:A ring.
          number_field k /\ ~(real_embeddings k = {})
          ==> {x | x IN ring_carrier k /\
                   ?n. 1 <= n /\ ring_pow k x n = ring_1 k} =
              {ring_1 k, ring_neg k (ring_1 k)}"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_X_ASSUM ((X_CHOOSE_TAC (← q r"g:A->complex")) o (GEN_REWRITE_RULE id [(← GSYM MEMBER_NOT_EMPTY)])) THEN RULE_ASSUM_TAC (REWRITE_RULE [real_embeddings, IN_ELIM_THM]) THEN FIRST_X_ASSUM (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "real")) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"g:A->complex")] COMPLEX_EMBEDDINGS_MONOMORPHISM) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o CONJUNCT1) THEN REWRITE_TAC [ring_monomorphism] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inj")) THEN SUBGOAL_THEN (← q r"(g:A->complex)(ring_1 k) = Cx(&1) /\
                  g(ring_neg k (ring_1 k)) = Cx(-- &1)") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"complex_ring"), (← q r"g:A->complex")] RING_HOMOMORPHISM_1) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"complex_ring"), (← q r"g:A->complex")] RING_HOMOMORPHISM_NEG) THEN ASM_SIMP_TAC [COMPLEX_RING_CLAUSES, RING_1, CX_NEG], ALL_TAC] THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_INSERT, NOT_IN_EMPTY] THEN X_GEN_TAC (← q r"x:A") THEN EQ_TAC THENL [STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"g:A->complex"), (← q r"x:A"), (← q r"n:num")] COMPLEX_EMBEDDINGS_ROOT_OF_UNITY) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN USE_THEN "real" (MP_TAC o (SPEC (← q r"x:A"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN REWRITE_TAC [REAL_EXISTS] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:real") (LABEL_TAC "gx")) THEN USE_THEN "gx" SUBST1_TAC THEN REWRITE_TAC [COMPLEX_NORM_CX, r1] THEN DISCH_THEN (DISJ_CASES_THEN SUBST_ALL_TAC) THENL [DISJ1_TAC, DISJ2_TAC] THEN USE_THEN "inj" MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_1, RING_NEG], STRIP_TAC THEN ASM_SIMP_TAC [RING_1, RING_NEG] THENL [EXISTS_TAC (← q r"1") THEN REWRITE_TAC [RING_POW_1, LE_REFL] THEN ASM_SIMP_TAC [RING_POW_1, RING_1], EXISTS_TAC (← q r"2") THEN ASM_SIMP_TAC [RING_POW_2, RING_MUL_LNEG, RING_MUL_RNEG, RING_NEG_NEG, RING_MUL_LID, RING_1, RING_NEG] THEN ARITH_TAC]])

  let NUMBER_FIELD_UNITS_EQ_ROOTS_OF_UNITY ← prove
    r"!k:A ring.
        number_field k
        ==> ({u | ring_unit (ring_of_integers k) u} =
             {x | x IN ring_carrier k /\
                  ?n. 1 <= n /\ ring_pow k x n = ring_1 k} <=>
             CARD(infinite_places k) = 1)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM (← MATCH_MP NUMBER_FIELD_UNITS_ROOTS_OF_UNITY th))])) THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN EQ_TAC THEN DISCH_TAC THENL [X_GEN_TAC (← q r"u:A") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"u:A"))) THEN ASM_REWRITE_TAC [] THEN MESON_TAC [], X_GEN_TAC (← q r"u:A") THEN EQ_TAC THENL [DISCH_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_UNIT_IN_CARRIER, RING_OF_INTEGERS_SUBSET, SUBSET], ASM_MESON_TAC []], MESON_TAC [RING_OF_INTEGERS_ROOT_OF_UNITY_UNIT]]])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_ROOT_OF_UNITY_PHI_DIVIDES, NUMBER_FIELD_ROOTS_OF_UNITY_CARD,
           NUMBER_FIELD_REAL_ROOTS_OF_UNITY, NUMBER_FIELD_UNITS_EQ_ROOTS_OF_UNITY }
  -- @@RETURN END

end HolANT.RootsOfUnity
