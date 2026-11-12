/- ========================================================================= -/
/- ANT: S-units of a number field k and the finiteness of K(S,m) ...       -/
/- ========================================================================= -/
/- File: HolANT/Sunits.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/sunits.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antsunitsdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/frag.ml, Library/grouptheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/isum.ml, Library/products.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/classgroup.ml, ANT/nf_valuation.ml, Library/ring_groups.ml, ANT/fingen_group.ml, ANT/classgroup_group.ml, ANT/fractional_ideals.ml, ANT/dedekind_criteria.ml, ANT/s_integers.ml, ANT/prime_split.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/integrality.ml, Multivariate/misc.ml, Multivariate/metric.ml, Multivariate/homology.ml, Multivariate/vectors.ml, Multivariate/determinants.ml, Multivariate/topology.ml, Multivariate/convex.ml, Multivariate/paths.ml, Multivariate/polytope.ml, Multivariate/degree.ml, Multivariate/derivatives.ml, Multivariate/integration.ml, Multivariate/measure.ml, Multivariate/complex_algebra.ml, Multivariate/complexes.ml, Multivariate/canal.ml, Multivariate/transcendentals.ml, Multivariate/realanalysis.ml, Multivariate/moretop.ml, Multivariate/cauchy.ml, Multivariate/complex_ring.ml, Multivariate/complex_field.ml, ANT/complex_embeddings.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.Sunits fills them).

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
import HolANT.IdealArith
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.IdealNorm
import HolANT.RingOfIntegers
import HolANT.NormIndex
import HolANT.Classgroup
import HolANT.NfValuation
import HolLibrary.RingGroups
import HolANT.FingenGroup
import HolANT.ClassgroupGroup
import HolANT.FractionalIdeals
import HolANT.DedekindCriteria
import HolANT.SIntegers
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
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.IdealNorm
open HolANT.RingOfIntegers
open HolANT.NormIndex
open HolANT.Classgroup
open HolANT.NfValuation
open HolANT.FingenGroup
open HolANT.ClassgroupGroup
open HolANT.FractionalIdeals
open HolANT.DedekindCriteria
open HolANT.SIntegers
open HolANT.PrimeSplit
open HolANT.Discriminant
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.Integrality
open HolANT.ComplexEmbeddings

namespace HolANT.Sunits

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ABELIAN_GROUP_HOMOMORPHISM_POWERING ABELIAN_GROUP_SUM_CLAUSES
   ABELIAN_GROUP_SUM_MUL ABELIAN_GROUP_SUM_POW ABELIAN_INTEGER_GROUP
   ABELIAN_PRODUCT_GROUP ABELIAN_SUBGROUP_GENERATED ABELIAN_UNIT_GROUP
   CARRIER_SUBGROUP_GENERATED_SUBGROUP CYCLIC_IMP_FINITELY_GENERATED_GROUP
   CYCLIC_INTEGER_GROUP DE_MORGAN_THM DIVISION EXTENSION FIELD_DIV_EQ_0
   FIELD_IMP_INTEGRAL_DOMAIN FIELD_INV_EQ_0 FIELD_MUL_LINV FIELD_NONTRIVIAL
   FIELD_POW_EQ_0 FIELD_UNIT FIELD_UNIT_GROUP
   FINITELY_GENERATED_ABELIAN_GROUP_MOD_POW FINITELY_GENERATED_ABELIAN_GROUP_POW
   FINITELY_GENERATED_ABELIAN_SUBGROUP FINITELY_GENERATED_GROUP_EXTENSION
   FINITELY_GENERATED_PRODUCT_GROUP FINITE_IMAGE FINITE_INDUCT_STRONG
   FINITE_RESTRICT FINITE_SUBSET FINITE_UNION FORALL_IN_GSPEC FORALL_IN_IMAGE
   FORALL_IN_INSERT GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET GROUP_HOMOMORPHISM
   GROUP_ISOMORPHISM_IMP_ISOMORPHIC GROUP_KERNEL_SUBSET_CARRIER GROUP_POW
   GROUP_POW_ADD GROUP_POW_POW GROUP_POW_SUBGROUP_GENERATED GROUP_SUM
   GROUP_SUM_CLAUSES_EXISTS GROUP_SUM_EQ IMP_CONJ INTEGER_GROUP
   INTEGRAL_DOMAIN_MUL_EQ_0 INTEGRAL_DOMAIN_POW_EQ_0 INT_ADD_LID INT_DIV_ZERO
   INT_MUL_DIV_EQ INT_NEG_0 INT_SUB_0 IN_DIFF IN_ELIM_THM IN_IMAGE IN_SING
   IN_UNION IN_UNIV ISOMORPHIC_GROUP_FINITE_GENERATION I_THM LEFT_IMP_EXISTS_THM
   MOD_LT_EQ MONO_EXISTS NOT_IN_EMPTY NUMBER_FIELD_IMP_FIELD
   NUMBER_FIELD_UNIT_GROUP_FINITELY_GENERATED NUMBER_FIELD_VALUATION_1
   NUMBER_FIELD_VALUATION_DIV NUMBER_FIELD_VALUATION_FINITE
   NUMBER_FIELD_VALUATION_INV NUMBER_FIELD_VALUATION_MUL
   NUMBER_FIELD_VALUATION_POW NUMBER_FIELD_VALUATION_PRINCIPAL_OUTSIDE
   NUMBER_FIELD_VALUATION_UNIT PRODUCT_GROUP RESTRICTION RESTRICTION_EXTENSION
   RESTRICTION_IN_CARTESIAN_PRODUCT RIGHT_COSET_EQ RING_1 RING_DIV RING_INV
   RING_MUL RING_MUL_ASSOC RING_MUL_POW RING_MUL_RID RING_OF_INTEGERS
   RING_OF_INTEGERS_FRACTION_FIELD RING_OF_INTEGERS_SUBRING
   RING_OF_INTEGERS_SUBSET RING_POW RING_PRODUCT_CLAUSES RING_UNIT_IN_CARRIER
   RING_UNIT_RING_OF_S_INTEGERS SUBGROUP_GENERATED
   SUBGROUP_GENERATED_IDEMPOT_GEN SUBGROUP_GENERATED_MONO SUBGROUP_GROUP_IMAGE
   SUBSET SWAP_FORALL_THM UNIT_GROUP UNIT_GROUP_POW UNIT_GROUP_SUBRING_GENERATED
   group_div group_image group_kernel ring_div ring_of_s_integers subgroup_of : thm)
  deriving Inhabited

/-- What sunits.ml uses from Session besides theorems. -/
structure SunitsDeps where
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
/- sunits.ml phrases from line 63 to 463                                  -/
/- ---------------------------------------------------------------------- -/

structure Sunits where
  -- @@FIELDS
  s_unit_group : thm
  S_UNIT_GROUP : thm
  S_UNIT_GROUP_POW : thm
  ABELIAN_S_UNIT_GROUP : thm
  S_UNIT_GROUP_EMPTY : thm
  S_UNIT_GROUP_MONO : thm
  S_UNIT_GROUP_SUM : thm
  FINITELY_GENERATED_S_UNIT_GROUP : thm
  S_UNIT_GROUP_GENERATORS : thm
  S_UNIT_GROUP_GENERATORS_MOD_POW : thm
  NUMBER_FIELD_POW_S_UNIT_DECOMPOSITION : thm
  NUMBER_FIELD_KSM_FINITE : thm
  NUMBER_FIELD_KSM_QUOTIENT_FINITE : thm
  S_UNIT_GROUP_RING_OF_S_INTEGERS : thm
  FINITELY_GENERATED_UNIT_GROUP_RING_OF_S_INTEGERS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupSunits [HolBase] (D : SunitsDeps) :
    ExceptT String IO Sunits := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_MESON_TAC, INTEGER_RULE, MESON_TAC, RING_TAC, SET_TAC, TAUT,
        new_definition, .. } := D
  let { ABELIAN_GROUP_HOMOMORPHISM_POWERING, ABELIAN_GROUP_SUM_CLAUSES,
        ABELIAN_GROUP_SUM_MUL, ABELIAN_GROUP_SUM_POW, ABELIAN_INTEGER_GROUP,
        ABELIAN_PRODUCT_GROUP, ABELIAN_SUBGROUP_GENERATED, ABELIAN_UNIT_GROUP,
        CARRIER_SUBGROUP_GENERATED_SUBGROUP, CYCLIC_IMP_FINITELY_GENERATED_GROUP,
        CYCLIC_INTEGER_GROUP, DE_MORGAN_THM, DIVISION, EXTENSION, FIELD_DIV_EQ_0,
        FIELD_IMP_INTEGRAL_DOMAIN, FIELD_INV_EQ_0, FIELD_MUL_LINV, FIELD_NONTRIVIAL,
        FIELD_POW_EQ_0, FIELD_UNIT, FIELD_UNIT_GROUP,
        FINITELY_GENERATED_ABELIAN_GROUP_MOD_POW, FINITELY_GENERATED_ABELIAN_GROUP_POW,
        FINITELY_GENERATED_ABELIAN_SUBGROUP, FINITELY_GENERATED_GROUP_EXTENSION,
        FINITELY_GENERATED_PRODUCT_GROUP, FINITE_IMAGE, FINITE_INDUCT_STRONG,
        FINITE_RESTRICT, FINITE_SUBSET, FINITE_UNION, FORALL_IN_GSPEC, FORALL_IN_IMAGE,
        FORALL_IN_INSERT, GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET, GROUP_HOMOMORPHISM,
        GROUP_ISOMORPHISM_IMP_ISOMORPHIC, GROUP_KERNEL_SUBSET_CARRIER, GROUP_POW,
        GROUP_POW_ADD, GROUP_POW_POW, GROUP_POW_SUBGROUP_GENERATED, GROUP_SUM,
        GROUP_SUM_CLAUSES_EXISTS, GROUP_SUM_EQ, IMP_CONJ, INTEGER_GROUP,
        INTEGRAL_DOMAIN_MUL_EQ_0, INTEGRAL_DOMAIN_POW_EQ_0, INT_ADD_LID, INT_DIV_ZERO,
        INT_MUL_DIV_EQ, INT_NEG_0, INT_SUB_0, IN_DIFF, IN_ELIM_THM, IN_IMAGE, IN_SING,
        IN_UNION, IN_UNIV, ISOMORPHIC_GROUP_FINITE_GENERATION, I_THM,
        LEFT_IMP_EXISTS_THM, MOD_LT_EQ, MONO_EXISTS, NOT_IN_EMPTY,
        NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_UNIT_GROUP_FINITELY_GENERATED,
        NUMBER_FIELD_VALUATION_1, NUMBER_FIELD_VALUATION_DIV,
        NUMBER_FIELD_VALUATION_FINITE, NUMBER_FIELD_VALUATION_INV,
        NUMBER_FIELD_VALUATION_MUL, NUMBER_FIELD_VALUATION_POW,
        NUMBER_FIELD_VALUATION_PRINCIPAL_OUTSIDE, NUMBER_FIELD_VALUATION_UNIT,
        PRODUCT_GROUP, RESTRICTION, RESTRICTION_EXTENSION,
        RESTRICTION_IN_CARTESIAN_PRODUCT, RIGHT_COSET_EQ, RING_1, RING_DIV, RING_INV,
        RING_MUL, RING_MUL_ASSOC, RING_MUL_POW, RING_MUL_RID, RING_OF_INTEGERS,
        RING_OF_INTEGERS_FRACTION_FIELD, RING_OF_INTEGERS_SUBRING,
        RING_OF_INTEGERS_SUBSET, RING_POW, RING_PRODUCT_CLAUSES, RING_UNIT_IN_CARRIER,
        RING_UNIT_RING_OF_S_INTEGERS, SUBGROUP_GENERATED,
        SUBGROUP_GENERATED_IDEMPOT_GEN, SUBGROUP_GENERATED_MONO, SUBGROUP_GROUP_IMAGE,
        SUBSET, SWAP_FORALL_THM, UNIT_GROUP, UNIT_GROUP_POW,
        UNIT_GROUP_SUBRING_GENERATED, group_div, group_image, group_kernel, ring_div,
        ring_of_s_integers, subgroup_of, .. } := D.core1
  -- @@SCOPE END

  let s_unit_group ← new_definition
    r"s_unit_group (k:A ring) (S:(A->bool)->bool) =
  subgroup_generated (unit_group k)
   {x | x IN ring_carrier k /\ ~(x = ring_0 k) /\
        !P. prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
            ~(P IN S)
            ==> dedekind_valuation (ring_of_integers k,k) I P x = &0}"

  let S_UNIT_GROUP ← prove
    r"!k:A ring S.
        number_field k
        ==> group_carrier(s_unit_group k S) =
            {x | x IN ring_carrier k /\ ~(x = ring_0 k) /\
                 !P. prime_ideal (ring_of_integers k) P /\
                     ~(P = {ring_0 k}) /\ ~(P IN S)
                     ==> dedekind_valuation (ring_of_integers k,k) I P x =
                         &0} /\
            group_id(s_unit_group k S) = ring_1 k /\
            group_inv(s_unit_group k S) = ring_inv k /\
            group_mul(s_unit_group k S) = ring_mul k"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN REWRITE_TAC [s_unit_group, (← CONJUNCT2 SUBGROUP_GENERATED), UNIT_GROUP] THEN MATCH_MP_TAC CARRIER_SUBGROUP_GENERATED_SUBGROUP THEN REWRITE_TAC [subgroup_of, UNIT_GROUP, SUBSET, IN_ELIM_THM] THEN ASM_SIMP_TAC [FIELD_UNIT, RING_1, FIELD_NONTRIVIAL, NUMBER_FIELD_VALUATION_1] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [RING_INV, RING_MUL, FIELD_INV_EQ_0, INTEGRAL_DOMAIN_MUL_EQ_0, FIELD_IMP_INTEGRAL_DOMAIN, NUMBER_FIELD_VALUATION_INV, NUMBER_FIELD_VALUATION_MUL, INT_NEG_0, INT_ADD_LID])

  let S_UNIT_GROUP_POW ← prove
    r"!k:A ring S x n. group_pow (s_unit_group k S) x n = ring_pow k x n"
    (REWRITE_TAC [s_unit_group, GROUP_POW_SUBGROUP_GENERATED, UNIT_GROUP_POW])

  let ABELIAN_S_UNIT_GROUP ← prove
    r"!k:A ring S. abelian_group(s_unit_group k S)"
    (SIMP_TAC [s_unit_group, ABELIAN_SUBGROUP_GENERATED, ABELIAN_UNIT_GROUP])

  let S_UNIT_GROUP_EMPTY ← prove
    r"!k:A ring.
        number_field k
        ==> group_carrier(s_unit_group k {}) =
            {x | ring_unit (ring_of_integers k) x}"
    (SIMP_TAC [S_UNIT_GROUP, NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"x:A") THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_CASES_TAC (← q r"(x:A) IN ring_carrier k") THEN ASM_SIMP_TAC [NUMBER_FIELD_VALUATION_UNIT] THEN ASM_MESON_TAC [RING_UNIT_IN_CARRIER, RING_OF_INTEGERS_SUBSET, SUBSET])

  let S_UNIT_GROUP_MONO ← prove
    r"!k:A ring S S'.
        S SUBSET S'
        ==> group_carrier(s_unit_group k S) SUBSET
            group_carrier(s_unit_group k S')"
    (REWRITE_TAC [s_unit_group] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBGROUP_GENERATED_MONO THEN ASM SET_TAC [])

  let S_UNIT_GROUP_SUM ← prove
    r"!k:A ring S s (f:K->A).
        FINITE s /\ (!i. i IN s ==> f i IN group_carrier(s_unit_group k S))
        ==> group_sum (s_unit_group k S) s f = ring_product k s f"
    (GEN_TAC THEN GEN_TAC THEN GEN_REWRITE_TAC id [SWAP_FORALL_THM] THEN GEN_TAC THEN REWRITE_TAC [IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN SIMP_TAC [(← CONJUNCT1 (← SPEC_ALL GROUP_SUM_CLAUSES_EXISTS)), FINITE_RESTRICT, ABELIAN_GROUP_SUM_CLAUSES, ABELIAN_S_UNIT_GROUP, FORALL_IN_INSERT, RING_PRODUCT_CLAUSES] THEN REWRITE_TAC [s_unit_group, (← CONJUNCT2 SUBGROUP_GENERATED), UNIT_GROUP] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (MATCH_MP (← REWRITE_RULE [SUBSET] GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET))) THEN SIMP_TAC [UNIT_GROUP, IN_ELIM_THM, RING_UNIT_IN_CARRIER])

  let FINITELY_GENERATED_S_UNIT_GROUP ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (p ==> q /\ r) ==> p /\ q /\ r")
    prove
      r"!k:A ring S.
          number_field k /\ FINITE S
          ==> finitely_generated_group(s_unit_group k S)"
      (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"S' = {P | P IN S /\ prime_ideal (ring_of_integers k) P /\
                          ~(P = {ring_0 k:A})}") THEN MP_TAC (← ISPECL [(← q r"s_unit_group (k:A ring) S"), (← q r"product_group S' (\P:A->bool. integer_group)"), (← q r"\x:A. RESTRICTION S'
                           (\P. dedekind_valuation (ring_of_integers k,k) I P x)")] FINITELY_GENERATED_GROUP_EXTENSION) THEN DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [REWRITE_TAC [GROUP_HOMOMORPHISM, SUBSET, FORALL_IN_IMAGE, PRODUCT_GROUP, RESTRICTION_IN_CARTESIAN_PRODUCT, INTEGER_GROUP, IN_UNIV, RESTRICTION_EXTENSION] THEN ASM_SIMP_TAC [S_UNIT_GROUP, IN_ELIM_THM, RESTRICTION] THEN EXPAND_TAC "S'" THEN SIMP_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC NUMBER_FIELD_VALUATION_MUL THEN ASM_REWRITE_TAC [], DISCH_TAC THEN CONJ_TAC] THENL [REWRITE_TAC [s_unit_group] THEN SIMP_TAC [SUBGROUP_GENERATED_IDEMPOT_GEN, GROUP_KERNEL_SUBSET_CARRIER] THEN REWRITE_TAC [(← GSYM s_unit_group)] THEN SUBGOAL_THEN (← q r"group_kernel (s_unit_group k S,product_group S' (\P. integer_group))
         (\x:A. RESTRICTION S'
                 (\P. dedekind_valuation (ring_of_integers k,k) I P x)) =
        group_carrier(s_unit_group k {})") SUBST1_TAC THENL [REWRITE_TAC [group_kernel, PRODUCT_GROUP, INTEGER_GROUP, RESTRICTION_EXTENSION] THEN ASM_SIMP_TAC [S_UNIT_GROUP, NOT_IN_EMPTY] THEN GEN_REWRITE_TAC id [EXTENSION] THEN EXPAND_TAC "S'" THEN REWRITE_TAC [IN_ELIM_THM] THEN MESON_TAC [], MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_carrier(ring_of_integers k:A ring)")] UNIT_GROUP_SUBRING_GENERATED) THEN ASM_SIMP_TAC [RING_OF_INTEGERS_SUBRING, S_UNIT_GROUP_EMPTY] THEN DISCH_THEN (MP_TAC o ((MATCH_MP ISOMORPHIC_GROUP_FINITE_GENERATION) o ((MATCH_MP GROUP_ISOMORPHISM_IMP_ISOMORPHIC) o CONJUNCT2))) THEN ASM_SIMP_TAC [NUMBER_FIELD_UNIT_GROUP_FINITELY_GENERATED]], MATCH_MP_TAC FINITELY_GENERATED_ABELIAN_SUBGROUP THEN ASM_SIMP_TAC [SUBGROUP_GROUP_IMAGE, FINITELY_GENERATED_PRODUCT_GROUP, ABELIAN_PRODUCT_GROUP, ABELIAN_INTEGER_GROUP, CYCLIC_IMP_FINITELY_GENERATED_GROUP, CYCLIC_INTEGER_GROUP] THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"S:(A->bool)->bool") THEN ASM SET_TAC []])

  let S_UNIT_GROUP_GENERATORS ← prove
    r"!k:A ring S.
        number_field k /\ FINITE S
        ==> ?t. FINITE t /\ t SUBSET group_carrier(s_unit_group k S) /\
                !x. x IN group_carrier(s_unit_group k S)
                    ==> ?n. x = ring_product k t (\y. ring_pow k y (n y))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"s_unit_group (k:A ring) S") FINITELY_GENERATED_ABELIAN_GROUP_POW) THEN ASM_SIMP_TAC [ABELIAN_S_UNIT_GROUP, FINITELY_GENERATED_S_UNIT_GROUP] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"t:A->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_THEN (fun th => tactic_of do pure (FIRST_X_ASSUM (MP_TAC o (← do let c := th; pure (fun th => MATCH_MP th c))))) THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"n:A->num") THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [S_UNIT_GROUP_POW] THEN MATCH_MP_TAC S_UNIT_GROUP_SUM THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN REWRITE_TAC [(← GSYM (← ISPECL [(← q r"k:A ring"), (← q r"S:(A->bool)->bool")] S_UNIT_GROUP_POW))] THEN MATCH_MP_TAC GROUP_POW THEN ASM SET_TAC [])

  let S_UNIT_GROUP_GENERATORS_MOD_POW ← prove
    r"!k:A ring S.
        number_field k /\ FINITE S
        ==> ?t. FINITE t /\ t SUBSET group_carrier(s_unit_group k S) /\
                !m x. ~(m = 0) /\ x IN group_carrier(s_unit_group k S)
                      ==> ?n y. (!v. n v < m) /\
                                y IN group_carrier(s_unit_group k S) /\
                                x = ring_mul k
                                     (ring_product k t (\v. ring_pow k v (n v)))
                                     (ring_pow k y m)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"s_unit_group (k:A ring) S") FINITELY_GENERATED_ABELIAN_GROUP_POW) THEN ASM_SIMP_TAC [ABELIAN_S_UNIT_GROUP, FINITELY_GENERATED_S_UNIT_GROUP] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"t:A->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MAP_EVERY X_GEN_TAC [(← q r"m:num"), (← q r"x:A")] THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"x:A"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"n:A->num") SUBST1_TAC) THEN MAP_EVERY EXISTS_TAC [(← q r"\v:A. n v MOD m"), (← q r"group_sum (s_unit_group k S) t
      (\v:A. group_pow (s_unit_group k S) v (n v DIV m))")] THEN ASM_REWRITE_TAC [MOD_LT_EQ, GROUP_SUM] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"S:(A->bool)->bool")] S_UNIT_GROUP) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM (← CONJUNCT2 (← CONJUNCT2 (← CONJUNCT2 th))))])) THEN REWRITE_TAC [(← GSYM S_UNIT_GROUP_POW)] THEN ASM_SIMP_TAC [(← GSYM S_UNIT_GROUP_SUM), GROUP_POW, (← REWRITE_RULE [SUBSET] (← ASSUME (← q r"t SUBSET group_carrier(s_unit_group (k:A ring) S)")))] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"S:(A->bool)->bool")] ABELIAN_S_UNIT_GROUP) THEN UNDISCH_TAC (← q r"t SUBSET group_carrier(s_unit_group (k:A ring) S)") THEN SPEC_TAC ((← q r"s_unit_group (k:A ring) S"), (← q r"G:A group")) THEN REWRITE_TAC [SUBSET] THEN REPEAT STRIP_TAC THEN wPart (rand o rand) (rand o rand) ABELIAN_GROUP_SUM_POW THEN ASM_SIMP_TAC [FINITE_RESTRICT, GROUP_POW] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN wPart rand (rand o rand) ABELIAN_GROUP_SUM_MUL THEN ASM_SIMP_TAC [FINITE_RESTRICT, GROUP_POW] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC GROUP_SUM_EQ THEN ASM_SIMP_TAC [GROUP_POW_POW, (← GSYM GROUP_POW_ADD)] THEN X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN AP_TERM_TAC THEN MP_TAC (← SPECL [(← q r"(n:A->num) y"), (← q r"m:num")] DIVISION) THEN ASM_REWRITE_TAC [] THEN ARITH_TAC)

  let NUMBER_FIELD_POW_S_UNIT_DECOMPOSITION ← prove
    r"!k:A ring.
        number_field k
        ==> ?t. FINITE t /\
                !S m x. x IN ring_carrier k /\ ~(x = ring_0 k) /\
                        (!P. prime_ideal (ring_of_integers k) P /\
                             ~(P = {ring_0 k}) /\ ~(P IN S)
                             ==> &m divides dedekind_valuation
                                             (ring_of_integers k,k) I P x)
                        ==> ?y u. y IN ring_carrier k /\ ~(y = ring_0 k) /\
                                  u IN group_carrier
                                        (s_unit_group k (S UNION t)) /\
                                  x = ring_mul k u (ring_pow k y m)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (MP_TAC o (MATCH_MP NUMBER_FIELD_VALUATION_PRINCIPAL_OUTSIDE)) THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"t:(A->bool)->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MAP_EVERY X_GEN_TAC [(← q r"S:(A->bool)->bool"), (← q r"m:num"), (← q r"x:A")] THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"\P. if P IN S then &0
        else dedekind_valuation (ring_of_integers k,k) I P (x:A) div &m"))) THEN REWRITE_TAC [] THEN ANTS_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{P | prime_ideal (ring_of_integers k) P /\
                     ~(P = {ring_0 k}) /\
                     ~(dedekind_valuation (ring_of_integers k,k) I P (x:A) =
                       &0)}") THEN ASM_SIMP_TAC [NUMBER_FIELD_VALUATION_FINITE, SUBSET, IN_ELIM_THM] THEN MESON_TAC [INT_DIV_ZERO], MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"y:A") THEN STRIP_TAC] THEN EXISTS_TAC (← q r"ring_div k x (ring_pow k y m):A") THEN SUBGOAL_THEN (← q r"ring_pow k (y:A) m IN ring_carrier k /\
                ~(ring_pow k y m = ring_0 k)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_POW, FIELD_POW_EQ_0], ALL_TAC] THEN ASM_SIMP_TAC [S_UNIT_GROUP, IN_ELIM_THM, RING_DIV, FIELD_DIV_EQ_0, IN_UNION, DE_MORGAN_THM, NUMBER_FIELD_VALUATION_DIV, NUMBER_FIELD_VALUATION_POW] THEN CONJ_TAC THENL [REPEAT STRIP_TAC THEN REWRITE_TAC [INT_SUB_0] THEN CONV_TAC SYM_CONV THEN REWRITE_TAC [INT_MUL_DIV_EQ] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], REWRITE_TAC [ring_div] THEN ASM_SIMP_TAC [(← GSYM RING_MUL_ASSOC), RING_INV, FIELD_MUL_LINV, RING_MUL_RID]])

  let NUMBER_FIELD_KSM_FINITE ← prove
    r"!k:A ring S m.
        number_field k /\ FINITE S /\ ~(m = 0)
        ==> ?t. FINITE t /\
                (!c. c IN t
                     ==> c IN ring_carrier k /\ ~(c = ring_0 k) /\
                         !P. prime_ideal (ring_of_integers k) P /\
                             ~(P = {ring_0 k}) /\ ~(P IN S)
                             ==> &m divides dedekind_valuation
                                             (ring_of_integers k,k) I P c) /\
                !x. x IN ring_carrier k /\ ~(x = ring_0 k) /\
                    (!P. prime_ideal (ring_of_integers k) P /\
                         ~(P = {ring_0 k}) /\ ~(P IN S)
                         ==> &m divides dedekind_valuation
                                         (ring_of_integers k,k) I P x)
                    ==> ?c y. c IN t /\ y IN ring_carrier k /\
                              ~(y = ring_0 k) /\
                              x = ring_mul k c (ring_pow k y m)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM ((X_CHOOSE_THEN (← q r"t0:(A->bool)->bool") STRIP_ASSUME_TAC) o (MATCH_MP NUMBER_FIELD_POW_S_UNIT_DECOMPOSITION)) THEN MP_TAC (← ISPECL [(← q r"s_unit_group (k:A ring) (S UNION t0)"), (← q r"m:num")] FINITELY_GENERATED_ABELIAN_GROUP_MOD_POW) THEN ASM_SIMP_TAC [ABELIAN_S_UNIT_GROUP, FINITELY_GENERATED_S_UNIT_GROUP, FINITE_UNION, S_UNIT_GROUP_POW, S_UNIT_GROUP] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"s0:A->bool") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*")))) THEN EXISTS_TAC (← q r"{c:A | c IN s0 /\ c IN ring_carrier k /\ ~(c = ring_0 k) /\
           !P. prime_ideal (ring_of_integers k) P /\
               ~(P = {ring_0 k}) /\ ~(P IN S)
               ==> &m divides dedekind_valuation
                               (ring_of_integers k,k) I P c}") THEN SIMP_TAC [FINITE_RESTRICT, IN_ELIM_THM, (← ASSUME (← q r"FINITE(s0:A->bool)"))] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "x"))) THEN FIRST_X_ASSUM (MP_TAC o (SPECL [(← q r"S:(A->bool)->bool"), (← q r"m:num"), (← q r"x:A")])) THEN ASM_SIMP_TAC [S_UNIT_GROUP, LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"y:A"), (← q r"u:A")] THEN STRIP_TAC THEN REMOVE_THEN "*" (MP_TAC o (SPEC (← q r"u:A"))) THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:A") (X_CHOOSE_THEN (← q r"w:A") STRIP_ASSUME_TAC)) THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier k /\ ~(a = ring_0 k)") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN MAP_EVERY EXISTS_TAC [(← q r"a:A"), (← q r"ring_mul k w y:A")] THEN ASM_SIMP_TAC [RING_MUL, INTEGRAL_DOMAIN_MUL_EQ_0, FIELD_IMP_INTEGRAL_DOMAIN, RING_MUL_POW, RING_POW, RING_MUL_ASSOC] THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN REMOVE_THEN "x" (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN ASM_SIMP_TAC [NUMBER_FIELD_VALUATION_MUL, NUMBER_FIELD_VALUATION_POW, RING_MUL, RING_POW, FIELD_POW_EQ_0, INTEGRAL_DOMAIN_MUL_EQ_0, FIELD_IMP_INTEGRAL_DOMAIN] THEN CONV_TAC INTEGER_RULE)

  let NUMBER_FIELD_KSM_QUOTIENT_FINITE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"(p <=> q) ==> p ==> q")
    prove
      r"!k:A ring S m.
          number_field k /\ FINITE S /\ ~(m = 0)
          ==> FINITE {right_coset (unit_group k)
                       {ring_pow k y m | y | y IN ring_carrier k /\
                                             ~(y = ring_0 k)} x |
                      x | x IN ring_carrier k /\ ~(x = ring_0 k) /\
                          !P. prime_ideal (ring_of_integers k) P /\
                              ~(P = {ring_0 k}) /\ ~(P IN S)
                              ==> &m divides dedekind_valuation
                                              (ring_of_integers k,k) I P x}"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"S:(A->bool)->bool"), (← q r"m:num")] NUMBER_FIELD_KSM_FINITE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"t:A->bool") STRIP_ASSUME_TAC) THEN ABBREV_TAC (← q r"H = {ring_pow k y m | y | y IN ring_carrier k /\
                                         ~(y = ring_0 k:A)}") THEN SUBGOAL_THEN (← q r"(H:A->bool) subgroup_of unit_group k") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"unit_group k:A group"), (← q r"m:num")] ABELIAN_GROUP_HOMOMORPHISM_POWERING) THEN REWRITE_TAC [ABELIAN_UNIT_GROUP] THEN DISCH_THEN (MP_TAC o (MATCH_MP SUBGROUP_GROUP_IMAGE)) THEN MATCH_MP_TAC r1 THEN AP_THM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "H" THEN SIMP_TAC [group_image, FIELD_UNIT_GROUP, UNIT_GROUP_POW, (← ASSUME (← q r"field(k:A ring)"))] THEN REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM, IN_DIFF, IN_SING] THEN MESON_TAC [], ALL_TAC] THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"IMAGE (right_coset (unit_group k) (H:A->bool)) t") THEN ASM_SIMP_TAC [FINITE_IMAGE] THEN REWRITE_TAC [SUBSET, FORALL_IN_GSPEC, IN_IMAGE] THEN X_GEN_TAC (← q r"x:A") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"x:A"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:A") (X_CHOOSE_THEN (← q r"y:A") STRIP_ASSUME_TAC)) THEN EXISTS_TAC (← q r"c:A") THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"c:A"))) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"unit_group k:A group"), (← q r"H:A->bool"), (← q r"ring_mul k c (ring_pow k y m):A"), (← q r"c:A")] RIGHT_COSET_EQ) THEN ASM_SIMP_TAC [FIELD_UNIT_GROUP, IN_DIFF, IN_SING, RING_MUL, RING_POW, FIELD_IMP_INTEGRAL_DOMAIN, INTEGRAL_DOMAIN_MUL_EQ_0, INTEGRAL_DOMAIN_POW_EQ_0] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [group_div, UNIT_GROUP] THEN EXPAND_TAC "H" THEN REWRITE_TAC [IN_ELIM_THM] THEN EXISTS_TAC (← q r"y:A") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ring_inv k (c:A) IN ring_carrier k /\
                  ring_mul k (ring_inv k c) c = ring_1 k") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_INV, FIELD_MUL_LINV], ALL_TAC] THEN RING_TAC)

  let S_UNIT_GROUP_RING_OF_S_INTEGERS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!k:A ring S.
          number_field k
          ==> s_unit_group k S =
              subgroup_generated (unit_group k)
                {x | ring_unit (ring_of_s_integers (ring_of_integers k,k) I S)
                               x} /\
              group_isomorphism
               (unit_group(ring_of_s_integers (ring_of_integers k,k) I S),
                s_unit_group k S) I"
      (REPEAT GEN_TAC THEN DISCH_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_FRACTION_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [REWRITE_TAC [s_unit_group] THEN AP_TERM_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"x:A") THEN ASM_SIMP_TAC [IN_ELIM_THM, RING_UNIT_RING_OF_S_INTEGERS, RING_OF_INTEGERS, I_THM], DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [ring_of_s_integers] THEN REWRITE_TAC [UNIT_GROUP_SUBRING_GENERATED]])

  let FINITELY_GENERATED_UNIT_GROUP_RING_OF_S_INTEGERS ← prove
    r"!k:A ring S.
        number_field k /\ FINITE S
        ==> finitely_generated_group
             (unit_group(ring_of_s_integers (ring_of_integers k,k) I S))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"S:(A->bool)->bool")] S_UNIT_GROUP_RING_OF_S_INTEGERS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o ((MATCH_MP GROUP_ISOMORPHISM_IMP_ISOMORPHIC) o CONJUNCT2)) THEN DISCH_THEN (SUBST1_TAC o (MATCH_MP ISOMORPHIC_GROUP_FINITE_GENERATION)) THEN ASM_SIMP_TAC [FINITELY_GENERATED_S_UNIT_GROUP])

  -- @@RETURN BEGIN
  return { s_unit_group, S_UNIT_GROUP, S_UNIT_GROUP_POW, ABELIAN_S_UNIT_GROUP,
           S_UNIT_GROUP_EMPTY, S_UNIT_GROUP_MONO, S_UNIT_GROUP_SUM,
           FINITELY_GENERATED_S_UNIT_GROUP, S_UNIT_GROUP_GENERATORS,
           S_UNIT_GROUP_GENERATORS_MOD_POW, NUMBER_FIELD_POW_S_UNIT_DECOMPOSITION,
           NUMBER_FIELD_KSM_FINITE, NUMBER_FIELD_KSM_QUOTIENT_FINITE,
           S_UNIT_GROUP_RING_OF_S_INTEGERS,
           FINITELY_GENERATED_UNIT_GROUP_RING_OF_S_INTEGERS }
  -- @@RETURN END

end HolANT.Sunits
