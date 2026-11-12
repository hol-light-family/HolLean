/- ========================================================================= -/
/- ANT: Units of quadratic fields and the Pell equation, with the ...      -/
/- ========================================================================= -/
/- File: HolANT/QuadraticUnits.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/quadratic_units.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antquadraticunitsdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/frag.ml, Library/grouptheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/products.ml, ANT/algmisc.ml, ANT/integral.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, Library/ring_groups.ml, ANT/fingen_group.ml, ANT/norm_index.ml, ANT/discriminant.ml, ANT/quadratic.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/classgroup.ml, ANT/nf_valuation.ml, ANT/prime_split.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/integrality.ml, Multivariate/misc.ml, Multivariate/metric.ml, Multivariate/homology.ml, Multivariate/vectors.ml, Multivariate/determinants.ml, Multivariate/topology.ml, Multivariate/convex.ml, Multivariate/paths.ml, Multivariate/polytope.ml, Multivariate/degree.ml, Multivariate/derivatives.ml, Multivariate/integration.ml, Multivariate/measure.ml, Multivariate/complex_algebra.ml, Multivariate/complexes.ml, Multivariate/canal.ml, Multivariate/transcendentals.ml, Multivariate/realanalysis.ml, Multivariate/moretop.ml, Multivariate/cauchy.ml, Multivariate/complex_ring.ml, Multivariate/complex_field.ml, ANT/complex_embeddings.ml, ANT/power_basis.ml, ANT/infinite_places.ml, ANT/linear_forms.ml, ANT/classgroup_group.ml, ANT/finite_field_trace.ml, ANT/ramification.ml, ANT/minkowski_theory.ml, ANT/unit_theorem.ml, ANT/regulator.ml, Library/symmetric_group.ml, Library/galois.ml, Library/finite_fields.ml, Library/integer.ml, Library/multiplicative.ml, Library/primitive.ml, ANT/cyclotomic_poly.ml, ANT/relative_degree.ml, ANT/dedekind_kummer.ml, ANT/cyclotomic_field.ml, ANT/roots_of_unity.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.QuadraticUnits fills them).

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
import HolLibrary.RingGroups
import HolANT.FingenGroup
import HolANT.NormIndex
import HolANT.Discriminant
import HolANT.Quadratic
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.Classgroup
import HolANT.NfValuation
import HolANT.PrimeSplit
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
import HolANT.MinkowskiTheory
import HolANT.UnitTheorem
import HolANT.Regulator
import HolLibrary.SymmetricGroup
import HolLibrary.Galois
import HolLibrary.FiniteFields
import HolLibrary.Integer
import HolLibrary.Multiplicative
import HolLibrary.Primitive
import HolANT.CyclotomicPoly
import HolANT.RelativeDegree
import HolANT.DedekindKummer
import HolANT.CyclotomicField
import HolANT.RootsOfUnity

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
open HolANT.FingenGroup
open HolANT.NormIndex
open HolANT.Discriminant
open HolANT.Quadratic
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.Classgroup
open HolANT.NfValuation
open HolANT.PrimeSplit
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
open HolANT.MinkowskiTheory
open HolANT.UnitTheorem
open HolANT.Regulator
open HolANT.CyclotomicPoly
open HolANT.RelativeDegree
open HolANT.DedekindKummer
open HolANT.CyclotomicField
open HolANT.RootsOfUnity

namespace HolANT.QuadraticUnits

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ARITH_EQ CARD_CLAUSES CARD_INFINITE_PLACES CARD_INFINITE_PLACES_EQ_1
   CARD_INFINITE_PLACE_EMBEDDINGS CARD_SING CARD_SUBSET_EQ
   COMPLEX_EMBEDDINGS_HAS_SIZE COMPLEX_EMBEDDINGS_NONEMPTY
   COMPLEX_EMBEDDINGS_PRIME_SUBFIELD_REAL COMPLEX_EMBEDDINGS_ROOT_OF_UNITY
   COMPLEX_EQ COMPLEX_NORM_CX COMPLEX_NORM_MUL COMPLEX_POW_2
   COMPLEX_RING_CLAUSES COMPLEX_RING_OF_INT COMPLEX_RING_OF_NUM COMPLEX_RING_POW
   COMPLEX_SQNORM CONTRAPOS_THM CX_INJ CX_POW DIVIDES_REFL EXISTS_PAIR_THM
   EXTENSION EXTENSIONAL FIELD_IMP_INTEGRAL_DOMAIN FIELD_MUL_RINV FIELD_POW_EQ_0
   FINITE_EMPTY FINITE_IMAGE FINITE_INSERT FINITE_SING FINITE_SUBSET
   FORALL_IN_IMAGE FORALL_PAIR_THM FORALL_UNWIND_THM2 FST FUN_EQ_THM
   GROUP_REAL_MULTIPLICATIVE_ZPOW GROUP_SUM_SING GROUP_ZPOW GROUP_ZPOW_1
   GROUP_ZPOW_2 GROUP_ZPOW_INV HAS_SIZE HAS_SIZE_IMAGE_INJ IDEAL_GENERATED_INC
   IDEAL_GENERATED_SING_ALT IM IMP_CONJ IM_ADD IM_CX INFINITE INFINITE_IMAGE
   INFINITE_SUPERSET INTEGRAL_DOMAIN_MUL_EQ_0 INTEGRAL_ELEMENT_QUADRATIC
   INT_ABS_POS INT_ENTIRE INT_LE_LMUL INT_LE_MUL INT_LE_MUL2 INT_LE_SQUARE_ABS
   INT_LT_IMP_LE INT_LT_MUL INT_LT_REFL INT_LT_RMUL_EQ INT_MUL_LID INT_MUL_LZERO
   INT_MUL_RZERO INT_NEG_NEG INT_NORM_FORM_4_IMAGINARY INT_OF_NUM_ADD
   INT_OF_NUM_EQ INT_OF_NUM_LT INT_OF_NUM_MUL INT_OF_NUM_OF_INT INT_OF_NUM_POW
   INT_POW2_ABS INT_POW_LT INT_SQUAREFREE_DECOMPOSITION INT_SUB_RZERO
   IN_ELIM_PAIR_THM IN_ELIM_THM IN_IMAGE IN_INSERT IN_SING IN_UNIV
   LEFT_IMP_EXISTS_THM LE_1 LE_REFL LOG_POS_LT MEMBER_NOT_EMPTY MONO_EXISTS
   NOT_EXISTS_THM NOT_FORALL_THM NOT_IMP NOT_IN_EMPTY
   NUMBER_FIELD_FUNDAMENTAL_UNITS NUMBER_FIELD_IMP_FIELD
   NUMBER_FIELD_REAL_ROOTS_OF_UNITY NUMBER_FIELD_REGULATOR
   NUMBER_FIELD_RING_OF_NUM_EQ_0 NUMBER_FIELD_UNITS_EQ_ROOTS_OF_UNITY
   NUMBER_FIELD_UNITS_ROOTS_OF_UNITY NUM_OF_INT_OF_NUM PAIR PAIR_EQ
   PRODUCT_CLAUSES QUADRATIC_FIELD_COORDINATES QUADRATIC_FIELD_EXISTS
   QUADRATIC_FIELD_INTEGRAL_COORDINATES QUADRATIC_FIELD_INT_COORDINATES_EQ
   QUOTIENT_RING_CARRIER : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (RE REAL_ABS_MUL REAL_ABS_NZ REAL_ABS_REFL REAL_ADD REAL_ADD_RID
   REAL_EMBEDDINGS_MONOMORPHISM REAL_ENTIRE REAL_EXISTS REAL_FIELD_CLAUSES
   REAL_INV_1_LT REAL_INV_NEG REAL_LE_POW_2 REAL_LE_SQUARE REAL_LT_IMP_LE
   REAL_MUL REAL_MUL_LID REAL_MUL_LZERO REAL_MUL_RID REAL_MUL_RINV_UNIQ
   REAL_NORM REAL_OF_INT_CLAUSES REAL_POW_LT_1 REAL_RING_CLAUSES
   REAL_RING_OF_INT REAL_SUB_RZERO REAL_ZPOW_0 REAL_ZPOW_1 REAL_ZPOW_LT
   REAL_ZPOW_MONO REAL_ZPOW_MONO_LT RE_ADD RE_CX RE_NEG RING_0 RING_1 RING_ADD
   RING_ADD_LZERO RING_ADD_RNEG RING_CARRIER_SUBFIELD_GENERATED_SUBSET
   RING_COSET_EQ RING_DET_SING RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED
   RING_HOMOMORPHISM_0 RING_HOMOMORPHISM_ADD RING_HOMOMORPHISM_MUL
   RING_HOMOMORPHISM_POW RING_HOMOMORPHISM_RING_OF_INT
   RING_HOMOMORPHISM_RING_OF_NUM RING_IDEAL_IDEAL_GENERATED RING_INV
   RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_MUL RING_MUL_LID RING_MUL_LNEG
   RING_MUL_LZERO RING_MUL_RINV RING_MUL_RNEG RING_NEG RING_NEG_NEG RING_OF_INT
   RING_OF_INTEGERS RING_OF_INTEGERS_CARRIER RING_OF_INTEGERS_FINITE_QUOTIENT
   RING_OF_INTEGERS_SUBSET RING_OF_INTEGERS_UNIT_NONZERO
   RING_OF_INTEGERS_UNIT_NORM_PRODUCT RING_OF_INT_0 RING_OF_INT_1
   RING_OF_INT_ADD RING_OF_INT_EQ_0_CHAR_0 RING_OF_INT_IN_SUBFIELD_GENERATED
   RING_OF_INT_MUL RING_OF_INT_NEG RING_OF_INT_OF_NUM RING_OF_INT_POW
   RING_OF_INT_SUB RING_OF_NUM RING_OF_NUM_1 RING_OF_NUM_ADD RING_POW RING_POW_1
   RING_POW_2 RING_POW_ADD RING_SUB RING_UNIT_1 RING_UNIT_INV
   RING_UNIT_IN_CARRIER RING_UNIT_NEG RING_UNIT_POW SING_SUBSET SND
   SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD SUBFIELD_GENERATED SUBSET
   TRANSITIVE_STEPWISE_LT UNIT_GROUP UNIT_GROUP_ZPOW_RING_NEG WLOG_LT
   complex_embeddings complex_mul infinite_places int_abs_th int_mul_th
   int_of_num_th int_pow_th int_sub_th num_INFINITE num_RECURSION number_field
   real real_embeddings ring_homomorphism ring_monomorphism ring_unit squarefree : thm)
  deriving Inhabited

/-- What quadratic_units.ml uses from Session besides theorems. -/
structure QuadraticUnitsDeps where
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
  GEN_BETA_CONV : ioconv
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
/- quadratic_units.ml phrases from line 88 to 659                         -/
/- ---------------------------------------------------------------------- -/

structure QuadraticUnits01 where
  -- @@FIELDS
  NUMBER_FIELD_FUNDAMENTAL_UNIT_REAL : thm
  NUMBER_FIELD_REGULATOR_FUNDAMENTAL_UNIT_REAL : thm
  QUADRATIC_FIELD_REAL_EMBEDDINGS : thm
  QUADRATIC_FIELD_CONJUGATE_EMBEDDING : thm
  QUADRATIC_FIELD_INFINITE_PLACES : thm
  QUADRATIC_FIELD_UNITS_IMAGINARY_ROOTS_OF_UNITY : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupQuadraticUnits01 [HolBase] (D : QuadraticUnitsDeps) :
    ExceptT String IO QuadraticUnits01 := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_ARITH_TAC, ASM_INT_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC,
        COMPLEX_RING, HAS_SIZE_CONV, INT_ARITH, INT_ARITH_TAC, MESON_TAC,
        NUM_REDUCE_CONV, REAL_ARITH, REAL_ARITH_TAC, SET_TAC, TAUT, .. } := D
  let { ARITH_EQ, CARD_CLAUSES, CARD_INFINITE_PLACES, CARD_INFINITE_PLACE_EMBEDDINGS,
        CARD_SING, COMPLEX_EMBEDDINGS_HAS_SIZE, COMPLEX_EMBEDDINGS_NONEMPTY,
        COMPLEX_EMBEDDINGS_PRIME_SUBFIELD_REAL, COMPLEX_EQ, COMPLEX_POW_2,
        COMPLEX_RING_CLAUSES, COMPLEX_RING_OF_INT, COMPLEX_RING_POW, CONTRAPOS_THM,
        CX_INJ, CX_POW, EXTENSION, EXTENSIONAL, FIELD_POW_EQ_0, FINITE_SING,
        FORALL_UNWIND_THM2, FUN_EQ_THM, GROUP_REAL_MULTIPLICATIVE_ZPOW, GROUP_SUM_SING,
        GROUP_ZPOW, GROUP_ZPOW_1, GROUP_ZPOW_2, GROUP_ZPOW_INV, HAS_SIZE, IM, IM_CX,
        INT_NEG_NEG, INT_OF_NUM_EQ, IN_ELIM_THM, IN_IMAGE, IN_INSERT, IN_SING, IN_UNIV,
        LEFT_IMP_EXISTS_THM, LE_REFL, LOG_POS_LT, NOT_IN_EMPTY,
        NUMBER_FIELD_FUNDAMENTAL_UNITS, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_REAL_ROOTS_OF_UNITY, NUMBER_FIELD_REGULATOR,
        NUMBER_FIELD_UNITS_EQ_ROOTS_OF_UNITY, QUADRATIC_FIELD_COORDINATES, .. } := D.core1
  let { RE, REAL_ABS_MUL, REAL_ABS_NZ, REAL_ABS_REFL, REAL_ADD,
        REAL_EMBEDDINGS_MONOMORPHISM, REAL_ENTIRE, REAL_EXISTS, REAL_INV_1_LT,
        REAL_INV_NEG, REAL_LE_POW_2, REAL_LE_SQUARE, REAL_LT_IMP_LE, REAL_MUL,
        REAL_MUL_LID, REAL_MUL_LZERO, REAL_MUL_RINV_UNIQ, REAL_NORM,
        REAL_OF_INT_CLAUSES, REAL_RING_CLAUSES, REAL_ZPOW_0, REAL_ZPOW_1, REAL_ZPOW_LT,
        REAL_ZPOW_MONO, REAL_ZPOW_MONO_LT, RE_CX, RING_0, RING_1,
        RING_CARRIER_SUBFIELD_GENERATED_SUBSET, RING_DET_SING,
        RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED, RING_HOMOMORPHISM_0,
        RING_HOMOMORPHISM_ADD, RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_POW,
        RING_HOMOMORPHISM_RING_OF_INT, RING_MUL, RING_MUL_LID, RING_MUL_LNEG,
        RING_MUL_RINV, RING_MUL_RNEG, RING_NEG, RING_NEG_NEG, RING_OF_INTEGERS,
        RING_OF_INTEGERS_UNIT_NONZERO, RING_OF_INT_0, RING_POW_1, RING_POW_2,
        RING_UNIT_INV, RING_UNIT_NEG, SUBFIELD_GENERATED, SUBSET, UNIT_GROUP,
        UNIT_GROUP_ZPOW_RING_NEG, complex_embeddings, complex_mul, infinite_places,
        real, real_embeddings, ring_homomorphism, ring_monomorphism, .. } := D.core2
  -- @@SCOPE END

  let NUMBER_FIELD_FUNDAMENTAL_UNIT_REAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← INT_ARITH (← q r"~(&1:int <= n) ==> n <= &0")
    let r7 ← REAL_ARITH (← q r"!(a:real). ~(a = &0) /\ ~(a = &1) /\ ~(a = -- &1)
          ==> &1 < a \/ a < -- &1 \/ (&0 < a /\ a < &1) \/
              (-- &1 < a /\ a < &0)")
    let r8 ← TAUT (← q r"~p /\ ~q ==> (a ==> p) ==> (b ==> q) ==> ~a /\ ~b")
    prove
      r"!k (g:A->complex).
          number_field k /\ CARD(infinite_places k) = 2 /\
          g IN real_embeddings k
          ==> ?e. ring_unit (ring_of_integers k) e /\ &1 < Re(g e) /\
                  (!u. ring_unit (ring_of_integers k) u <=>
                       ?n. u = group_zpow (unit_group(ring_of_integers k)) e n \/
                           u = ring_neg k
                                (group_zpow (unit_group(ring_of_integers k))
                                            e n)) /\
                  (!n. group_zpow (unit_group(ring_of_integers k)) e n =
                       ring_1 k ==> n = &0) /\
                  (!u. ring_unit (ring_of_integers k) u /\ &1 < Re(g u)
                       ==> Re(g e) <= Re(g u))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN (← q r"ring_monomorphism(k,real_ring) (\x. Re((g:A->complex) x))") ASSUME_TAC THENL [MATCH_MP_TAC REAL_EMBEDDINGS_MONOMORPHISM THEN ASM_REWRITE_TAC [], ALL_TAC] THEN FIRST_ASSUM (MP_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [ring_monomorphism]))) THEN REWRITE_TAC [ring_homomorphism, REAL_RING_CLAUSES] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(!y. ring_unit (ring_of_integers k) y ==> (y:A) IN ring_carrier k) /\
      (!y n. ring_unit (ring_of_integers k) y
             ==> ring_unit (ring_of_integers k)
                   (group_zpow (unit_group(ring_of_integers k)) (y:A) n)) /\
      (!y. ring_unit (ring_of_integers k) y
           ==> ring_unit (ring_of_integers k) (ring_neg k y)) /\
      (!y. ring_unit (ring_of_integers k) y
           ==> ring_unit (ring_of_integers k)
                 (ring_inv (ring_of_integers k) y) /\
               ring_mul k y (ring_inv (ring_of_integers k) y) = ring_1 k)") (CONJUNCTS_THEN2 (LABEL_TAC "car") (CONJUNCTS_THEN2 (LABEL_TAC "zpow") (CONJUNCTS_THEN2 (LABEL_TAC "neg") (LABEL_TAC "inv")))) THENL [REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_UNIT_NONZERO], MP_TAC (← ISPECL [(← q r"unit_group(ring_of_integers k):A group"), (← q r"y:A"), (← q r"n:int")] GROUP_ZPOW) THEN ASM_REWRITE_TAC [UNIT_GROUP, IN_ELIM_THM], MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"y:A")] RING_UNIT_NEG) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"y:A")] RING_MUL_RINV) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"y:A")] RING_UNIT_INV) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN SIMP_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"!y. ring_unit (ring_of_integers k) y ==> ~(Re((g:A->complex) y) = &0)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN USE_THEN "inv" (MP_TAC o (SPEC (← q r"y:A"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, STRIP_TAC] THEN FIRST_X_ASSUM (MP_TAC o (AP_TERM (← q r"\x. Re((g:A->complex) x)"))) THEN REWRITE_TAC [] THEN ASM_SIMP_TAC [REAL_MUL_LZERO] THEN REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"!y n. ring_unit (ring_of_integers k) y
            ==> abs(Re((g:A->complex)
                      (group_zpow (unit_group(ring_of_integers k)) y n))) =
                abs(Re(g y)) zpow n") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"unit_group(ring_of_integers k):A group"), (← q r"\x. abs(Re((g:A->complex) x))"), (← q r"y:A"), (← q r"n:int")] GROUP_REAL_MULTIPLICATIVE_ZPOW) THEN REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC [UNIT_GROUP, IN_ELIM_THM, RING_OF_INTEGERS] THEN ASM_SIMP_TAC [(← GSYM REAL_ABS_NZ), REAL_ABS_MUL], ALL_TAC] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP NUMBER_FIELD_FUNDAMENTAL_UNITS)) THEN ASM_REWRITE_TAC [] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC (ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"t:A->bool") MP_TAC) THEN DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q r"e0:A")) MP_TAC) THEN FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC [IN_SING, FORALL_UNWIND_THM2, GROUP_SUM_SING] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_SIMP_TAC [GROUP_ZPOW, UNIT_GROUP, IN_ELIM_THM] THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "ind0") (LABEL_TAC "gen0")) THEN REMOVE_THEN "ind0" (MP_TAC o ((GEN (← q r"m:int")) o (SPEC (← q r"\x:A. (m:int)")))) THEN REWRITE_TAC [] THEN DISCH_THEN (LABEL_TAC "ind0") THEN SUBGOAL_THEN (← q r"!u. ring_unit (ring_of_integers k) u
          ==> ?n. u = group_zpow (unit_group(ring_of_integers k)) e0 n \/
                  u = ring_neg k
                       (group_zpow (unit_group(ring_of_integers k)) (e0:A) n)") (LABEL_TAC "gen1") THENL [X_GEN_TAC (← q r"u:A") THEN DISCH_TAC THEN REMOVE_THEN "gen0" (MP_TAC o (SPEC (← q r"u:A"))) THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"z:A"), (← q r"n:A->int")] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"m:num") STRIP_ASSUME_TAC) SUBST1_TAC)) THEN EXISTS_TAC (← q r"(n:A->int) e0") THEN MP_TAC (← ISPEC (← q r"k:A ring") NUMBER_FIELD_REAL_ROOTS_OF_UNITY) THEN ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_INSERT, NOT_IN_EMPTY] THEN DISCH_THEN (fun z9 => tactic_of do pure (MP_TAC (← (do pure (Prod.fst (← (do pure (← EQ_IMP_RULE (← SPEC (← q r"z:A") z9))))))))) THEN ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"group_zpow (unit_group(ring_of_integers k)) e0 ((n:A->int) e0) IN
        ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN DISCH_THEN (DISJ_CASES_THEN SUBST1_TAC) THEN ASM_SIMP_TAC [RING_MUL_LID, RING_MUL_LNEG, RING_1], ALL_TAC] THEN REMOVE_THEN "gen0" (fun (_ : thm) => ALL_TAC) THEN SUBGOAL_THEN (← q r"!e. ring_unit (ring_of_integers k) e /\
          (!u. ring_unit (ring_of_integers k) u
               ==> ?n. u = group_zpow (unit_group(ring_of_integers k)) e n \/
                       u = ring_neg k
                            (group_zpow (unit_group(ring_of_integers k)) e n))
          ==> (!u. ring_unit (ring_of_integers k) u
                   ==> ?n. u = group_zpow (unit_group(ring_of_integers k))
                                          (ring_neg k e) n \/
                           u = ring_neg k
                                (group_zpow (unit_group(ring_of_integers k))
                                            (ring_neg k e) n)) /\
              (!u. ring_unit (ring_of_integers k) u
                   ==> ?n. u = group_zpow (unit_group(ring_of_integers k))
                                          (ring_inv (ring_of_integers k) e) n \/
                           u = ring_neg k
                                (group_zpow (unit_group(ring_of_integers k))
                                  (ring_inv (ring_of_integers k) (e:A)) n))") (LABEL_TAC "transport") THENL [GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "g")) THEN CONJ_TAC THEN X_GEN_TAC (← q r"u:A") THEN DISCH_TAC THEN REMOVE_THEN "g" (MP_TAC o (SPEC (← q r"u:A"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"n:int") (LABEL_TAC "u")) THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_neg k e:A"), (← q r"n:int")] UNIT_GROUP_ZPOW_RING_NEG) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_neg k (ring_neg k e) = (e:A)") SUBST1_TAC THENL [ASM_MESON_TAC [RING_NEG_NEG], ALL_TAC] THEN SUBGOAL_THEN (← q r"group_zpow (unit_group(ring_of_integers k)) (ring_neg k e) n IN
          ring_carrier (k:A ring)") ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN DISCH_THEN (DISJ_CASES_THEN SUBST_ALL_TAC) THEN EXISTS_TAC (← q r"n:int") THEN REMOVE_THEN "u" MP_TAC THEN ASM_SIMP_TAC [RING_NEG_NEG] THEN MESON_TAC [], EXISTS_TAC (← q r"--n:int") THEN MP_TAC (← ISPECL [(← q r"unit_group(ring_of_integers k):A group"), (← q r"e:A"), (← q r"--n:int")] GROUP_ZPOW_INV) THEN ASM_REWRITE_TAC [UNIT_GROUP, IN_ELIM_THM, INT_NEG_NEG] THEN DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC], ALL_TAC] THEN REMOVE_THEN "ind0" (MP_TAC o ((GEN (← q r"m:int")) o ((ONCE_REWRITE_RULE [(← GSYM CONTRAPOS_THM)]) o (SPEC (← q r"m:int"))))) THEN DISCH_THEN (LABEL_TAC "ind0") THEN SUBGOAL_THEN (← q r"(e0:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"Re((g:A->complex)(ring_inv (ring_of_integers k) e0)) = inv(Re(g e0))") ASSUME_TAC THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_MUL_RINV_UNIQ THEN USE_THEN "inv" (MP_TAC o (SPEC (← q r"e0:A"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, STRIP_TAC] THEN FIRST_X_ASSUM (MP_TAC o (AP_TERM (← q r"\x. Re((g:A->complex) x)"))) THEN REWRITE_TAC [] THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(Re((g:A->complex) e0) = &1) /\ ~(Re(g e0) = -- &1)") STRIP_ASSUME_TAC THENL [MP_TAC (← CONJUNCT2 (← GEN_REWRITE_RULE id [ring_monomorphism] (← ASSUME (← q r"ring_monomorphism(k,real_ring) (\x. Re((g:A->complex) x))")))) THEN REWRITE_TAC [] THEN DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← SPECL [(← q r"e0:A"), (← q r"ring_neg k (ring_1 k):A")] th) THEN MP_TAC (← SPECL [(← q r"e0:A"), (← q r"ring_1 k:A")] th))) THEN ASM_SIMP_TAC [RING_1, RING_NEG] THEN MATCH_MP_TAC r8 THEN CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL [REMOVE_THEN "ind0" (MP_TAC o (SPEC (← q r"&1:int"))), REMOVE_THEN "ind0" (MP_TAC o (SPEC (← q r"&2:int")))] THEN ASM_SIMP_TAC [GROUP_ZPOW_1, GROUP_ZPOW_2, UNIT_GROUP, IN_ELIM_THM, RING_OF_INTEGERS, INT_OF_NUM_EQ, ARITH_EQ] THEN SIMP_TAC [RING_MUL_LNEG, RING_MUL_RNEG, RING_NEG_NEG, RING_MUL_LID, RING_1, RING_NEG], ALL_TAC] THEN SUBGOAL_THEN (← q r"?e. ring_unit (ring_of_integers k) e /\
          (!u. ring_unit (ring_of_integers k) u
               ==> ?n. u = group_zpow (unit_group(ring_of_integers k)) e n \/
                       u = ring_neg k
                            (group_zpow (unit_group(ring_of_integers k)) e n)) /\
          &1 < Re((g:A->complex) e)") MP_TAC THENL [SUBGOAL_THEN (← q r"ring_unit (ring_of_integers k) (ring_inv (ring_of_integers k) e0) /\
        ring_inv (ring_of_integers k) e0 IN ring_carrier (k:A ring)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN USE_THEN "transport" (MP_TAC o (SPEC (← q r"e0:A"))) THEN ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "gneg") (LABEL_TAC "ginv")) THEN USE_THEN "transport" (MP_TAC o (SPEC (← q r"ring_inv (ring_of_integers k) e0:A"))) THEN ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "gneginv") (fun (_ : thm) => ALL_TAC)) THEN MP_TAC (← ISPEC (← q r"Re((g:A->complex) e0)") r7) THEN ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN STRIP_TAC THENL [EXISTS_TAC (← q r"e0:A") THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC, EXISTS_TAC (← q r"ring_neg k e0:A") THEN REPEAT CONJ_TAC THENL [USE_THEN "neg" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC, USE_THEN "gneg" ACCEPT_TAC, ASM_SIMP_TAC [] THEN ASM_REAL_ARITH_TAC], EXISTS_TAC (← q r"ring_inv (ring_of_integers k) e0:A") THEN REPEAT CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC, USE_THEN "ginv" ACCEPT_TAC, ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_INV_1_LT THEN ASM_REWRITE_TAC []], EXISTS_TAC (← q r"ring_neg k (ring_inv (ring_of_integers k) e0):A") THEN REPEAT CONJ_TAC THENL [USE_THEN "neg" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC, USE_THEN "gneginv" ACCEPT_TAC, ASM_SIMP_TAC [] THEN REWRITE_TAC [(← GSYM REAL_INV_NEG)] THEN MATCH_MP_TAC REAL_INV_1_LT THEN ASM_REAL_ARITH_TAC]], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"e:A") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "gen") ASSUME_TAC))) THEN EXISTS_TAC (← q r"e:A") THEN SUBGOAL_THEN (← q r"!n. Re((g:A->complex)(group_zpow (unit_group(ring_of_integers k)) e n)) =
          Re(g e) zpow n \/
          Re(g(group_zpow (unit_group(ring_of_integers k)) e n)) =
          --(Re(g e) zpow n)") (LABEL_TAC "val") THENL [GEN_TAC THEN FIRST_ASSUM (MP_TAC o ((SPECL [(← q r"e:A"), (← q r"n:int")]) o (checkM (fun z2 => (do let z3 ← (do pure (Prod.snd (← (do let z4 ← (do pure (Prod.snd (← (do let z5 ← (do let z6 ← (pure z2); pure (concl z6)); pure (strip_forall z5))))); liftExcept (dest_imp z4))))); pure (is_eq z3)))))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"abs(Re((g:A->complex) e)) = Re(g e)") SUBST1_TAC THENL [ASM_REAL_ARITH_TAC, REAL_ARITH_TAC], ALL_TAC] THEN REPEAT CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC, FIRST_ASSUM ACCEPT_TAC, X_GEN_TAC (← q r"u:A") THEN EQ_TAC THENL [USE_THEN "gen" (ACCEPT_TAC o (SPEC (← q r"u:A"))), DISCH_THEN (X_CHOOSE_THEN (← q r"n:int") (DISJ_CASES_THEN SUBST1_TAC)) THEN ASM_MESON_TAC []], X_GEN_TAC (← q r"n:int") THEN DISCH_TAC THEN REMOVE_THEN "val" (MP_TAC o (SPEC (← q r"n:int"))) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"Re((g:A->complex) e) zpow n = &1") MP_TAC THENL [MP_TAC (← ISPECL [(← q r"Re((g:A->complex) e)"), (← q r"n:int")] REAL_ZPOW_LT) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"Re((g:A->complex) e)"), (← q r"n:int"), (← q r"&0:int")] REAL_ZPOW_MONO_LT) THEN MP_TAC (← ISPECL [(← q r"Re((g:A->complex) e)"), (← q r"&0:int"), (← q r"n:int")] REAL_ZPOW_MONO_LT) THEN ASM_REWRITE_TAC [REAL_ZPOW_0] THEN INT_ARITH_TAC, X_GEN_TAC (← q r"u:A") THEN STRIP_TAC THEN USE_THEN "gen" (MP_TAC o (SPEC (← q r"u:A"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"n:int") (LABEL_TAC "un")) THEN SUBGOAL_THEN (← q r"Re((g:A->complex) u) = Re(g e) zpow n") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"Re((g:A->complex) e)"), (← q r"n:int")] REAL_ZPOW_LT) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC, DISCH_TAC] THEN REMOVE_THEN "val" (MP_TAC o (SPEC (← q r"n:int"))) THEN UNDISCH_TAC (← q r"&1 < Re((g:A->complex) u)") THEN REMOVE_THEN "un" (DISJ_CASES_THEN SUBST1_TAC) THEN ASM_SIMP_TAC [] THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"Re((g:A->complex) e)"), (← q r"n:int"), (← q r"&0:int")] REAL_ZPOW_MONO) THEN MP_TAC (← ISPECL [(← q r"Re((g:A->complex) e)"), (← q r"&1:int"), (← q r"n:int")] REAL_ZPOW_MONO) THEN ASM_REWRITE_TAC [REAL_ZPOW_0, REAL_ZPOW_1] THEN UNDISCH_TAC (← q r"&1 < Re((g:A->complex) u)") THEN ASM_REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"&1:int <= n") THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [REAL_LT_IMP_LE, r1] THEN REAL_ARITH_TAC])

  let NUMBER_FIELD_REGULATOR_FUNDAMENTAL_UNIT_REAL ← prove
    r"!k (g:A->complex) e.
        number_field k /\ CARD(infinite_places k) = 2 /\
        g IN real_embeddings k /\
        ring_unit (ring_of_integers k) e /\ &1 < Re(g e) /\
        (!u. ring_unit (ring_of_integers k) u
             ==> ?n. u = group_zpow (unit_group(ring_of_integers k)) e n \/
                     u = ring_neg k
                          (group_zpow (unit_group(ring_of_integers k)) e n))
        ==> number_field_regulator k = log(Re(g e))"
    (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gen")))))) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN (← q r"(g:A->complex) IN complex_embeddings k /\
                !x. x IN ring_carrier k ==> real(g x)") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"(g:A->complex) IN real_embeddings k") THEN REWRITE_TAC [real_embeddings, IN_ELIM_THM], ALL_TAC] THEN SUBGOAL_THEN (← q r"(e:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_UNIT_NONZERO], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{e:A}"), (← q r"\x:A. x"), (← q r"\u:A. \x:A. norm((g:A->complex) x)")] NUMBER_FIELD_REGULATOR) THEN ASM_REWRITE_TAC [] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [HAS_SIZE, FINITE_SING, CARD_SING, IN_SING, FORALL_UNWIND_THM2] THEN ANTS_TAC THENL [ASM_REWRITE_TAC [GROUP_SUM_SING] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"u:A") THEN DISCH_TAC THEN USE_THEN "gen" (MP_TAC o (SPEC (← q r"u:A"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"n:int") MP_TAC) THEN SUBGOAL_THEN (← q r"group_zpow (unit_group(ring_of_integers k)) (e:A) n IN
        group_carrier(unit_group(ring_of_integers k))") ASSUME_TAC THENL [MATCH_MP_TAC GROUP_ZPOW THEN ASM_REWRITE_TAC [UNIT_GROUP, IN_ELIM_THM], ALL_TAC] THEN SUBGOAL_THEN (← q r"group_zpow (unit_group(ring_of_integers k)) (e:A) n IN
        ring_carrier k") ASSUME_TAC THENL [UNDISCH_TAC (← q r"group_zpow (unit_group(ring_of_integers k)) (e:A) n IN
          group_carrier(unit_group(ring_of_integers k))") THEN REWRITE_TAC [UNIT_GROUP, IN_ELIM_THM] THEN ASM_MESON_TAC [RING_OF_INTEGERS_UNIT_NONZERO], ALL_TAC] THEN STRIP_TAC THENL [EXISTS_TAC (← q r"ring_1 k:A"), EXISTS_TAC (← q r"ring_neg k (ring_1 k):A")] THEN EXISTS_TAC (← q r"\x:A. (n:int)") THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [RING_1, RING_NEG, RING_MUL_LID, RING_MUL_LNEG] THENL [EXISTS_TAC (← q r"1") THEN SIMP_TAC [RING_POW_1, LE_REFL, RING_1], EXISTS_TAC (← q r"2") THEN SIMP_TAC [RING_POW_2, RING_MUL_LNEG, RING_MUL_RNEG, RING_NEG_NEG, RING_MUL_LID, RING_1, RING_NEG] THEN ARITH_TAC], CONJ_TAC THENL [REWRITE_TAC [infinite_places, IN_IMAGE] THEN EXISTS_TAC (← q r"g:A->complex") THEN ASM_REWRITE_TAC [], MESON_TAC []]], DISCH_THEN SUBST1_TAC] THEN wPart (rand o lhand) (lhand o rand) RING_DET_SING THEN REWRITE_TAC [REAL_RING_CLAUSES, IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [CARD_INFINITE_PLACE_EMBEDDINGS, REAL_MUL_LID, REAL_NORM] THEN SUBGOAL_THEN (← q r"abs(Re((g:A->complex) e)) = Re(g e)") SUBST1_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [REAL_ABS_REFL] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC LOG_POS_LT THEN FIRST_ASSUM ACCEPT_TAC)

  let QUADRATIC_FIELD_REAL_EMBEDDINGS ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"Im w"
    let v2 ← SPEC q1 REAL_LE_SQUARE
    let q3 ← q r"Re w * Re w - Im w * Im w = r"
    let q4 ← q r"Re w * Im w = &0"
    let p5 ← prove r"!w r. w pow 2 = Cx r /\ &0 < r ==> real w" (REPEAT GEN_TAC THEN REWRITE_TAC [COMPLEX_EQ, COMPLEX_POW_2, complex_mul, RE, IM, RE_CX, IM_CX, real] THEN STRIP_TAC THEN SUBGOAL_THEN q4 MP_TAC THENL [ASM_REAL_ARITH_TAC, REWRITE_TAC [REAL_ENTIRE]] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC q3 THEN ASM_REWRITE_TAC [REAL_MUL_LZERO] THEN MP_TAC v2 THEN ASM_REAL_ARITH_TAC)
    let lemma1 := p5
    let v6 ← GSYM CX_POW
    let p7 ← prove r"!w r. w pow 2 = Cx r /\ real w ==> &0 <= r" (REWRITE_TAC [REAL_EXISTS] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE [v6, CX_INJ]) THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN REWRITE_TAC [REAL_LE_POW_2])
    let lemma2 := p7
    let q8 ← q r"real_of_int d"
    let q9 ← q r"(g:A->complex) x"
    let v10 ← ISPECL [q9, q8] lemma2
    let q11 ← q r"g:A->complex"
    let q12 ← q r"real_embeddings k = {}:(A->complex)->bool"
    let q13 ← q r"g:A->complex"
    let q14 ← q r"complex_ring"
    let q15 ← q r"k:A ring"
    let v16 ← ISPECL [q15, q14, q13] RING_HOMOMORPHISM_MUL
    let q17 ← q r"g:A->complex"
    let q18 ← q r"complex_ring"
    let q19 ← q r"k:A ring"
    let v20 ← ISPECL [q19, q18, q17] RING_HOMOMORPHISM_ADD
    let q21 ← q r"(g:A->complex) IN complex_embeddings k"
    let q22 ← q r"k:A ring"
    let q23 ← q r"real((g:A->complex) a) /\ real(g b)"
    let q24 ← q r"(a:A) IN ring_carrier k /\ (b:A) IN ring_carrier k"
    let q25 ← q r"b:A"
    let q26 ← q r"a:A"
    let q27 ← q r"z:A"
    let q28 ← q r"x:A"
    let q29 ← q r"k:A ring"
    let v30 ← ISPECL [q29, q28, q27] QUADRATIC_FIELD_COORDINATES
    let q31 ← q r"real_of_int d"
    let q32 ← q r"real((g:A->complex) x)"
    let q33 ← q r"z:A"
    let q34 ← q r"(g:A->complex) IN complex_embeddings k"
    let q35 ← q r"g:A->complex"
    let q36 ← q r"real_embeddings k = complex_embeddings(k:A ring)"
    let q37 ← q r"&0 < (d:int)"
    let q38 ← q r"~(complex_embeddings(k:A ring) = {})"
    let q39 ← q r"~(ring_0 k IN
          ring_carrier(subfield_generated k {ring_0 (k:A ring)}))"
    let q40 ← q r"ring_pow k (x:A) 2 = ring_of_int k (&0)"
    let q41 ← q r"~(d:int = &0)"
    let q42 ← q r"g:A->complex"
    let q43 ← q r"complex_ring"
    let q44 ← q r"k:A ring"
    let v45 ← ISPECL [q44, q43, q42] RING_HOMOMORPHISM_RING_OF_INT
    let q46 ← q r"2"
    let q47 ← q r"x:A"
    let q48 ← q r"g:A->complex"
    let q49 ← q r"complex_ring"
    let q50 ← q r"k:A ring"
    let v51 ← ISPECL [q50, q49, q48] RING_HOMOMORPHISM_POW
    let q52 ← q r"!g:A->complex. g IN complex_embeddings k
                     ==> (g x) pow 2 = Cx(real_of_int d)"
    prove
      r"!k (x:A) d.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
          x IN ring_carrier k /\
          ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
          ring_pow k x 2 = ring_of_int k d
          ==> (real_embeddings k = complex_embeddings k <=> &0 < d) /\
              (real_embeddings k = {} <=> d < &0)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN q52 ASSUME_TAC THENL [REWRITE_TAC [complex_embeddings, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MP_TAC v51 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (SPECL [q47, q46])) THEN ASM_REWRITE_TAC [COMPLEX_RING_POW] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC v45 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => REWRITE_TAC [th, COMPLEX_RING_OF_INT]), ALL_TAC] THEN SUBGOAL_THEN q41 ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC q40 THEN ASM_SIMP_TAC [RING_OF_INT_0, FIELD_POW_EQ_0, ARITH_EQ] THEN DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC q39 THEN REWRITE_TAC [] THEN MESON_TAC [SUBFIELD_GENERATED, RING_0], ALL_TAC] THEN SUBGOAL_THEN q38 ASSUME_TAC THENL [ASM_SIMP_TAC [COMPLEX_EMBEDDINGS_NONEMPTY], ALL_TAC] THEN ASM_CASES_TAC q37 THENL [SUBGOAL_THEN q36 ASSUME_TAC THENL [REWRITE_TAC [real_embeddings, EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC q35 THEN ASM_CASES_TAC q34 THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC q33 THEN DISCH_TAC THEN SUBGOAL_THEN q32 ASSUME_TAC THENL [MATCH_MP_TAC lemma1 THEN EXISTS_TAC q31 THEN ASM_SIMP_TAC [REAL_OF_INT_CLAUSES], ALL_TAC] THEN MP_TAC v30 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN q26 (X_CHOOSE_THEN q25 STRIP_ASSUME_TAC)) THEN SUBGOAL_THEN q24 STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN q23 STRIP_ASSUME_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC COMPLEX_EMBEDDINGS_PRIME_SUBFIELD_REAL THEN EXISTS_TAC q22 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN UNDISCH_TAC q21 THEN REWRITE_TAC [complex_embeddings, IN_ELIM_THM] THEN STRIP_TAC THEN MP_TAC v20 THEN MP_TAC v16 THEN ASM_REWRITE_TAC [] THEN REPEAT DISCH_TAC THEN ASM_SIMP_TAC [RING_MUL, COMPLEX_RING_CLAUSES] THEN MATCH_MP_TAC REAL_ADD THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_MUL THEN ASM_REWRITE_TAC [], ASM_REWRITE_TAC [] THEN ASM_INT_ARITH_TAC], SUBGOAL_THEN q12 ASSUME_TAC THENL [REWRITE_TAC [real_embeddings, EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY] THEN X_GEN_TAC q11 THEN STRIP_TAC THEN MP_TAC v10 THEN ASM_SIMP_TAC [REAL_OF_INT_CLAUSES] THEN ASM_INT_ARITH_TAC, ASM_REWRITE_TAC [] THEN ASM_INT_ARITH_TAC]])

  let QUADRATIC_FIELD_CONJUGATE_EMBEDDING ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"q ==> ~q ==> p")
    let r2 ← COMPLEX_RING (← q r"a pow 2 = b pow 2 <=> a = b \/ a = --b:complex")
    prove
      r"!k x (g:A->complex).
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
          x IN ring_carrier k /\
          ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
          ring_pow k x 2 IN ring_carrier(subfield_generated k {ring_0 k}) /\
          g IN complex_embeddings k
          ==> ?h. h IN complex_embeddings k /\ ~(h = g) /\
                  complex_embeddings k = {g,h} /\ h x = --(g x) /\
                  !a. a IN ring_carrier(subfield_generated k {ring_0 k})
                      ==> h a = g a"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN MP_TAC (← ISPEC (← q r"k:A ring") COMPLEX_EMBEDDINGS_HAS_SIZE) THEN ASM_REWRITE_TAC [] THEN CONV_TAC (LAND_CONV HAS_SIZE_CONV) THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"g1:A->complex"), (← q r"g2:A->complex")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"?h:A->complex. h IN complex_embeddings k /\ ~(h = g) /\
                     complex_embeddings k = {g,h}") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"(g:A->complex) IN complex_embeddings k") THEN ASM_REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN STRIP_TAC THENL [EXISTS_TAC (← q r"g2:A->complex"), EXISTS_TAC (← q r"g1:A->complex")] THEN ASM_REWRITE_TAC [IN_INSERT] THEN ASM SET_TAC [], ALL_TAC] THEN UNDISCH_THEN (← q r"complex_embeddings k = {g1:A->complex, g2}") (fun (_ : thm) => ALL_TAC) THEN EXISTS_TAC (← q r"h:A->complex") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"!a. a IN ring_carrier(subfield_generated k {ring_0 k})
          ==> (h:A->complex) a = g a") ASSUME_TAC THENL [MATCH_MP_TAC RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED THEN EXISTS_TAC (← q r"complex_ring") THEN RULE_ASSUM_TAC (REWRITE_RULE [complex_embeddings, IN_ELIM_THM]) THEN ASM_REWRITE_TAC [IN_SING] THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"complex_ring"), (← q r"h:A->complex")] RING_HOMOMORPHISM_0) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"complex_ring"), (← q r"g:A->complex")] RING_HOMOMORPHISM_0) THEN ASM_REWRITE_TAC [] THEN SIMP_TAC [], ASM_REWRITE_TAC []] THEN SUBGOAL_THEN (← q r"(h:A->complex) x pow 2 = g x pow 2") MP_TAC THENL [FIRST_ASSUM (MP_TAC o (SPEC (← q r"ring_pow k (x:A) 2"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN RULE_ASSUM_TAC (REWRITE_RULE [complex_embeddings, IN_ELIM_THM]) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"complex_ring"), (← q r"h:A->complex")] RING_HOMOMORPHISM_POW) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"complex_ring"), (← q r"g:A->complex")] RING_HOMOMORPHISM_POW) THEN ASM_REWRITE_TAC [COMPLEX_RING_POW] THEN DISCH_THEN (MP_TAC o (SPECL [(← q r"x:A"), (← q r"2")])) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, DISCH_THEN SUBST1_TAC] THEN DISCH_THEN (MP_TAC o (SPECL [(← q r"x:A"), (← q r"2")])) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (DISJ_CASES_TAC o (GEN_REWRITE_RULE id [r2])) THENL [ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"~((h:A->complex) = g)") THEN MATCH_MP_TAC r1 THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"z:A") THEN ASM_CASES_TAC (← q r"(z:A) IN ring_carrier k") THENL [ALL_TAC, RULE_ASSUM_TAC (REWRITE_RULE [complex_embeddings, IN_ELIM_THM, EXTENSIONAL]) THEN ASM_SIMP_TAC []] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"z:A")] QUADRATIC_FIELD_COORDINATES) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:A") (X_CHOOSE_THEN (← q r"b:A") STRIP_ASSUME_TAC)) THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier k /\ (b:A) IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBSET], ALL_TAC] THEN RULE_ASSUM_TAC (REWRITE_RULE [complex_embeddings, IN_ELIM_THM]) THEN MAP_EVERY (fun f => tactic_of do pure (MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"complex_ring"), f] RING_HOMOMORPHISM_ADD) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"complex_ring"), f] RING_HOMOMORPHISM_MUL))) [(← q r"g:A->complex"), (← q r"h:A->complex")] THEN ASM_REWRITE_TAC [] THEN REPEAT DISCH_TAC THEN ASM_SIMP_TAC [RING_MUL], ASM_REWRITE_TAC []])

  let QUADRATIC_FIELD_INFINITE_PLACES ← prove
    r"!k (x:A) d.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
        ring_pow k x 2 = ring_of_int k d
        ==> (&0 < d ==> CARD(infinite_places k) = 2) /\
            (d < &0 ==> CARD(infinite_places k) = 1)"
    (REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP QUADRATIC_FIELD_REAL_EMBEDDINGS)) THEN FIRST_X_ASSUM STRIP_ASSUME_TAC THEN DISCH_THEN (CONJUNCTS_THEN (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM th)]))) THEN MP_TAC (← ISPEC (← q r"k:A ring") CARD_INFINITE_PLACES) THEN MP_TAC (← ISPEC (← q r"k:A ring") COMPLEX_EMBEDDINGS_HAS_SIZE) THEN ASM_REWRITE_TAC [HAS_SIZE] THEN STRIP_TAC THEN DISCH_TAC THEN CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE [CARD_CLAUSES]) THEN ASM_ARITH_TAC)

  let QUADRATIC_FIELD_UNITS_IMAGINARY_ROOTS_OF_UNITY ← prove
    r"!k (x:A) d.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
        ring_pow k x 2 = ring_of_int k d /\ d < &0
        ==> {u | ring_unit (ring_of_integers k) u} =
            {z | z IN ring_carrier k /\
                 ?n. 1 <= n /\ ring_pow k z n = ring_1 k}"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP NUMBER_FIELD_UNITS_EQ_ROOTS_OF_UNITY th)])) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"d:int")] QUADRATIC_FIELD_INFINITE_PLACES) THEN ASM_SIMP_TAC [])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_FUNDAMENTAL_UNIT_REAL,
           NUMBER_FIELD_REGULATOR_FUNDAMENTAL_UNIT_REAL, QUADRATIC_FIELD_REAL_EMBEDDINGS,
           QUADRATIC_FIELD_CONJUGATE_EMBEDDING, QUADRATIC_FIELD_INFINITE_PLACES,
           QUADRATIC_FIELD_UNITS_IMAGINARY_ROOTS_OF_UNITY }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- quadratic_units.ml phrases from line 676 to 1126                       -/
/- ---------------------------------------------------------------------- -/

structure QuadraticUnits02 where
  -- @@FIELDS
  QUADRATIC_FIELD_UNIT_IMAGINARY : thm
  QUADRATIC_FIELD_UNITS_IMAGINARY : thm
  QUADRATIC_FIELD_UNITS_IMAGINARY_CARD : thm
  QUADRATIC_FIELD_UNITS_IMAGINARY_GENERIC : thm
  QUADRATIC_FIELD_FUNDAMENTAL_UNIT : thm
  QUADRATIC_FIELD_PELL_UNIT : thm
  QUADRATIC_FIELD_UNIT_POW_IN_ORDER : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupQuadraticUnits02 [HolBase] (D : QuadraticUnitsDeps) (BQuadraticUnits01 : QuadraticUnits01) :
    ExceptT String IO QuadraticUnits02 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_INT_ARITH_TAC, ASM_MESON_TAC,
        ASM_REAL_ARITH_TAC, GEN_BETA_CONV, INT_ARITH, INT_ARITH_TAC, INT_REDUCE_CONV,
        MESON_TAC, NUM_REDUCE_CONV, REAL_RAT_REDUCE_CONV, REAL_RING, RING_CARRIER_TAC,
        RING_RULE, RING_TAC, TAUT, .. } := D
  let { ARITH_EQ, CARD_CLAUSES, CARD_INFINITE_PLACES_EQ_1, CARD_SUBSET_EQ,
        COMPLEX_EMBEDDINGS_NONEMPTY, COMPLEX_EMBEDDINGS_ROOT_OF_UNITY, COMPLEX_EQ,
        COMPLEX_NORM_CX, COMPLEX_NORM_MUL, COMPLEX_POW_2, COMPLEX_RING_CLAUSES,
        COMPLEX_RING_OF_INT, COMPLEX_RING_OF_NUM, COMPLEX_RING_POW, COMPLEX_SQNORM,
        DIVIDES_REFL, EXISTS_PAIR_THM, EXTENSION, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_MUL_RINV, FINITE_EMPTY, FINITE_INSERT, FINITE_SUBSET, FORALL_IN_IMAGE,
        FORALL_PAIR_THM, HAS_SIZE, HAS_SIZE_IMAGE_INJ, IDEAL_GENERATED_INC,
        IDEAL_GENERATED_SING_ALT, IM, IMP_CONJ, IM_ADD, IM_CX, INFINITE,
        INFINITE_IMAGE, INTEGRAL_DOMAIN_MUL_EQ_0, INTEGRAL_ELEMENT_QUADRATIC,
        INT_NORM_FORM_4_IMAGINARY, IN_ELIM_PAIR_THM, IN_ELIM_THM, IN_IMAGE, IN_INSERT,
        IN_SING, IN_UNIV, LEFT_IMP_EXISTS_THM, MEMBER_NOT_EMPTY, MONO_EXISTS,
        NOT_EXISTS_THM, NOT_FORALL_THM, NOT_IMP, NOT_IN_EMPTY, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_RING_OF_NUM_EQ_0, NUMBER_FIELD_UNITS_ROOTS_OF_UNITY,
        NUM_OF_INT_OF_NUM, PAIR_EQ, QUADRATIC_FIELD_INTEGRAL_COORDINATES,
        QUADRATIC_FIELD_INT_COORDINATES_EQ, QUOTIENT_RING_CARRIER, .. } := D.core1
  let { RE, REAL_ENTIRE, REAL_LE_SQUARE, REAL_MUL_LZERO, REAL_OF_INT_CLAUSES,
        REAL_SUB_RZERO, RE_ADD, RE_CX, RING_1, RING_ADD, RING_ADD_LZERO, RING_ADD_RNEG,
        RING_COSET_EQ, RING_HOMOMORPHISM_ADD, RING_HOMOMORPHISM_MUL,
        RING_HOMOMORPHISM_POW, RING_HOMOMORPHISM_RING_OF_INT,
        RING_HOMOMORPHISM_RING_OF_NUM, RING_IDEAL_IDEAL_GENERATED, RING_INV, RING_MUL,
        RING_MUL_LZERO, RING_MUL_RINV, RING_NEG, RING_OF_INT, RING_OF_INTEGERS,
        RING_OF_INTEGERS_CARRIER, RING_OF_INTEGERS_FINITE_QUOTIENT,
        RING_OF_INTEGERS_SUBSET, RING_OF_INTEGERS_UNIT_NONZERO, RING_OF_INT_0,
        RING_OF_INT_1, RING_OF_INT_ADD, RING_OF_INT_EQ_0_CHAR_0, RING_OF_INT_MUL,
        RING_OF_INT_NEG, RING_OF_INT_OF_NUM, RING_OF_INT_POW, RING_OF_INT_SUB,
        RING_OF_NUM, RING_OF_NUM_1, RING_OF_NUM_ADD, RING_POW, RING_POW_ADD, RING_SUB,
        RING_UNIT_1, RING_UNIT_IN_CARRIER, RING_UNIT_NEG, RING_UNIT_POW, SING_SUBSET,
        SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD, SUBSET, WLOG_LT, complex_embeddings,
        complex_mul, num_INFINITE, number_field, ring_unit, squarefree, .. } := D.core2
  let { NUMBER_FIELD_FUNDAMENTAL_UNIT_REAL,
        NUMBER_FIELD_REGULATOR_FUNDAMENTAL_UNIT_REAL, QUADRATIC_FIELD_INFINITE_PLACES,
        QUADRATIC_FIELD_REAL_EMBEDDINGS, .. } := BQuadraticUnits01
  -- @@SCOPE END

  let QUADRATIC_FIELD_UNIT_IMAGINARY ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"Re w * Re w - Im w * Im w = d"
    let q2 ← q r"Re w"
    let v3 ← SPEC q2 REAL_LE_SQUARE
    let q4 ← q r"Re w * Re w - Im w * Im w = d"
    let q5 ← q r"Re w * Im w = &0"
    let q6 ← q r"Re w = &0"
    let p7 ← prove r"!w d A B. w pow 2 = Cx d /\ d < &0
               ==> norm(Cx A + Cx B * w) pow 2 = A pow 2 - d * B pow 2" (REPEAT GEN_TAC THEN REWRITE_TAC [COMPLEX_EQ, COMPLEX_POW_2, complex_mul, RE, IM, RE_CX, IM_CX] THEN STRIP_TAC THEN SUBGOAL_THEN q6 ASSUME_TAC THENL [SUBGOAL_THEN q5 MP_TAC THENL [ASM_REAL_ARITH_TAC, REWRITE_TAC [REAL_ENTIRE]] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC q4 THEN ASM_REWRITE_TAC [REAL_MUL_LZERO, REAL_SUB_RZERO] THEN MP_TAC v3 THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [COMPLEX_SQNORM, RE_ADD, IM_ADD, RE_CX, IM_CX, RE, IM] THEN UNDISCH_TAC q1 THEN ASM_REWRITE_TAC [] THEN CONV_TAC REAL_RING)
    let normlemma := p7
    let q8 ← q r"!k:A ring z x a b dd.
       ring_mul k (ring_of_num k 2) z = ring_add k a (ring_mul k b x) /\
       ring_pow k x 2 = dd /\
       ring_sub k (ring_pow k a 2) (ring_mul k dd (ring_pow k b 2)) =
       ring_of_num k 4
       ==> ring_mul k (ring_of_num k 4)
             (ring_add k (ring_pow k z 2)
                (ring_add k (ring_mul k (ring_neg k a) z) (ring_1 k))) =
           ring_0 k"
    let r9 ← RING_RULE q8
    let ringlemma := r9
    let q10 ← q r"!k:A ring z a.
                ring_add k (ring_pow k z 2)
                  (ring_add k (ring_mul k (ring_neg k a) z) (ring_1 k)) =
                ring_0 k
                ==> ring_mul k z (ring_sub k a z) = ring_1 k"
    let r11 ← RING_RULE q10
    let q12 ← q r"ring_of_int k A:A"
    let q13 ← q r"z:A"
    let q14 ← q r"k:A ring"
    let v15 ← ISPECL [q14, q13, q12] r11
    let q16 ← q r"!k:A ring z a.
                ring_add k (ring_pow k z 2)
                  (ring_add k (ring_mul k (ring_neg k a) z) (ring_1 k)) =
                ring_0 k
                ==> ring_add k (ring_pow k (ring_sub k a z) 2)
                     (ring_add k (ring_mul k (ring_neg k a) (ring_sub k a z))
                                 (ring_1 k)) = ring_0 k"
    let r17 ← RING_RULE q16
    let q18 ← q r"ring_of_int k A:A"
    let q19 ← q r"z:A"
    let q20 ← q r"k:A ring"
    let v21 ← ISPECL [q20, q19, q18] r17
    let q22 ← q r"ring_sub k (ring_of_int k A) (z:A)"
    let q23 ← q r"&1:int"
    let q24 ← q r"--A:int"
    let q25 ← q r"!y:A. y IN ring_carrier k /\
                ring_add k (ring_pow k y 2)
                 (ring_add k (ring_mul k (ring_neg k (ring_of_int k A)) y)
                             (ring_1 k)) = ring_0 k
                ==> y IN ring_carrier(ring_of_integers k)"
    let q26 ← q r"ring_add k (ring_pow k z 2)
               (ring_add k (ring_mul k (ring_neg k (ring_of_int k A)) z)
                           (ring_1 k)):A"
    let q27 ← q r"ring_of_num k 4:A"
    let q28 ← q r"k:A ring"
    let v29 ← ISPECL [q28, q27, q26] INTEGRAL_DOMAIN_MUL_EQ_0
    let v30 ← GSYM RING_OF_INT_SUB
    let v31 ← GSYM RING_OF_INT_MUL
    let v32 ← GSYM RING_OF_INT_POW
    let q33 ← q r"ring_of_int k d:A"
    let q34 ← q r"ring_of_int k B:A"
    let q35 ← q r"ring_of_int k A:A"
    let q36 ← q r"x:A"
    let q37 ← q r"z:A"
    let q38 ← q r"k:A ring"
    let v39 ← ISPECL [q38, q37, q36, q35, q34, q33] ringlemma
    let q40 ← q r"ring_add k (ring_pow k z 2)
            (ring_add k (ring_mul k (ring_neg k (ring_of_int k A)) z)
                        (ring_1 k)) = ring_0 (k:A ring)"
    let q41 ← q r"B:int"
    let q42 ← q r"A:int"
    let q43 ← q r"(A:int) pow 2 - d * B pow 2 = &4 * N"
    let v44 ← GSYM REAL_OF_INT_CLAUSES
    let q54 ← q r"2"
    let q55 ← q r"x:A"
    let q56 ← q r"real_of_int B"
    let q57 ← q r"real_of_int A"
    let q58 ← q r"real_of_int d"
    let q59 ← q r"(g:A->complex) x"
    let v60 ← ISPECL [q59, q58, q57, q56] normlemma
    let q61 ← q r"\w:complex. norm w pow 2"
    let q62 ← q r"(g:A->complex)(ring_mul k (ring_of_num k 2) z) =
          Cx(real_of_int A) + Cx(real_of_int B) * g x"
    let q63 ← q r"g:A->complex"
    let q64 ← q r"complex_ring"
    let q65 ← q r"k:A ring"
    let v66 ← ISPECL [q65, q64, q63] RING_HOMOMORPHISM_RING_OF_NUM
    let q67 ← q r"g:A->complex"
    let q68 ← q r"complex_ring"
    let q69 ← q r"k:A ring"
    let v70 ← ISPECL [q69, q68, q67] RING_HOMOMORPHISM_RING_OF_INT
    let q71 ← q r"g:A->complex"
    let q72 ← q r"complex_ring"
    let q73 ← q r"k:A ring"
    let v74 ← ISPECL [q73, q72, q71] RING_HOMOMORPHISM_POW
    let q75 ← q r"g:A->complex"
    let q76 ← q r"complex_ring"
    let q77 ← q r"k:A ring"
    let v78 ← ISPECL [q77, q76, q75] RING_HOMOMORPHISM_MUL
    let q79 ← q r"g:A->complex"
    let q80 ← q r"complex_ring"
    let q81 ← q r"k:A ring"
    let v82 ← ISPECL [q81, q80, q79] RING_HOMOMORPHISM_ADD
    let q83 ← q r"(g:A->complex) IN complex_embeddings k"
    let q84 ← q r"m:num"
    let q85 ← q r"z:A"
    let q86 ← q r"g:A->complex"
    let q87 ← q r"k:A ring"
    let v88 ← ISPECL [q87, q86, q85, q84] COMPLEX_EMBEDDINGS_ROOT_OF_UNITY
    let q89 ← q r"g:A->complex"
    let v90 ← GSYM MEMBER_NOT_EMPTY
    let q91 ← q r"d:int"
    let q92 ← q r"x:A"
    let q93 ← q r"k:A ring"
    let v94 ← ISPECL [q93, q92, q91] QUADRATIC_FIELD_REAL_EMBEDDINGS
    let q95 ← q r"CARD(infinite_places(k:A ring)) = 1"
    let q96 ← q r"k:A ring"
    let v97 ← ISPEC q96 NUMBER_FIELD_UNITS_ROOTS_OF_UNITY
    let q98 ← q r"?m. 1 <= m /\ ring_pow k (z:A) m = ring_1 k"
    let q99 ← q r"B:int"
    let q100 ← q r"A:int"
    let q101 ← q r"N:int"
    let q102 ← q r"B:int"
    let q103 ← q r"A:int"
    let q104 ← q r"z:A"
    let q105 ← q r"d:int"
    let q106 ← q r"x:A"
    let q107 ← q r"k:A ring"
    let v108 ← ISPECL [q107, q106, q105, q104] QUADRATIC_FIELD_INTEGRAL_COORDINATES
    let q109 ← q r"z:A"
    let q110 ← q r"k:A ring"
    let v111 ← ISPECL [q110, q109] RING_OF_INTEGERS_UNIT_NONZERO
    let q112 ← q r"~(ring_of_num k 2 = ring_0 (k:A ring)) /\
                  ~(ring_of_num k 4 = ring_0 (k:A ring))"
    let q113 ← q r"d:int"
    let q114 ← q r"~((x:A) IN ring_carrier(subfield_generated k {ring_0 k}))"
    let q115 ← q r"~(d:int = &1)"
    prove
      r"!k (x:A) d z.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
          x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
          squarefree(num_of_int(abs d)) /\ d < &0
          ==> (ring_unit (ring_of_integers k) z <=>
               z IN ring_carrier k /\
               ?A B. ring_mul k (ring_of_num k 2) z =
                     ring_add k (ring_of_int k A)
                                (ring_mul k (ring_of_int k B) x) /\
                     A pow 2 - d * B pow 2 = &4)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN q115 ASSUME_TAC THENL [ASM_INT_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN q114 ASSUME_TAC THENL [MATCH_MP_TAC SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD THEN EXISTS_TAC q113 THEN ASM_MESON_TAC [number_field], ALL_TAC] THEN SUBGOAL_THEN q112 STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [NUMBER_FIELD_RING_OF_NUM_EQ_0] THEN CONV_TAC NUM_REDUCE_CONV, ALL_TAC] THEN EQ_TAC THENL [DISCH_TAC THEN MP_TAC v111 THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC v108 THEN ASM_SIMP_TAC [RING_UNIT_IN_CARRIER] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [q103, q102, q101] THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC [q100, q99] THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN q98 STRIP_ASSUME_TAC THENL [MP_TAC v97 THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN q95 (fun th => REWRITE_TAC [th]) THENL [ASM_SIMP_TAC [CARD_INFINITE_PLACES_EQ_1] THEN MP_TAC v94 THEN ASM_REWRITE_TAC [] THEN SIMP_TAC [], DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC], ALL_TAC] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP COMPLEX_EMBEDDINGS_NONEMPTY)) THEN REWRITE_TAC [v90] THEN DISCH_THEN (X_CHOOSE_TAC q89) THEN MP_TAC v88 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN UNDISCH_TAC q83 THEN REWRITE_TAC [complex_embeddings, IN_ELIM_THM] THEN STRIP_TAC THEN MP_TAC v82 THEN MP_TAC v78 THEN MP_TAC v74 THEN MP_TAC v70 THEN MP_TAC v66 THEN ASM_REWRITE_TAC [COMPLEX_RING_CLAUSES, COMPLEX_RING_POW, COMPLEX_RING_OF_INT, COMPLEX_RING_OF_NUM] THEN REPEAT DISCH_TAC THEN SUBGOAL_THEN q62 MP_TAC THENL [ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [RING_OF_INT, RING_MUL], ALL_TAC] THEN ASM_SIMP_TAC [RING_OF_NUM] THEN DISCH_THEN (MP_TAC o (AP_TERM q61)) THEN REWRITE_TAC [] THEN MP_TAC v60 THEN ANTS_TAC THENL [CONJ_TAC THENL [FIRST_X_ASSUM (MP_TAC o ((SPECL [q55, q54]) o (checkM (fun th => (do if ← (do let z45 ← (do let z46 ← (pure th); pure (concl z46)); pure (is_forall z45)) then (do let z47 ← (do let z48 ← (pure th); pure (concl z48)); canM (fun z49 => (do let z50 ← (pure z49); find_termM (fun z51 => (do let z53 ← (pure z51); let z52 ← (q r"(pow):complex->num->complex"); pure (z52 == z53))) z50)) z47) else pure false))))) THEN ASM_REWRITE_TAC [] THEN MESON_TAC [], ASM_REWRITE_TAC [REAL_OF_INT_CLAUSES]], DISCH_THEN SUBST1_TAC] THEN ASM_REWRITE_TAC [COMPLEX_NORM_MUL, COMPLEX_NORM_CX] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC [v44] THEN UNDISCH_TAC q43 THEN INT_ARITH_TAC, REWRITE_TAC [LEFT_IMP_EXISTS_THM, IMP_CONJ] THEN DISCH_TAC THEN MAP_EVERY X_GEN_TAC [q42, q41] THEN REPEAT DISCH_TAC THEN SUBGOAL_THEN q40 ASSUME_TAC THENL [MP_TAC v39 THEN ASM_SIMP_TAC [RING_OF_INT] THEN ANTS_TAC THENL [REWRITE_TAC [v32, v31, v30] THEN ASM_REWRITE_TAC [RING_OF_INT_OF_NUM], ALL_TAC] THEN MP_TAC v29 THEN ANTS_TAC THENL [ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN] THEN CONJ_TAC THEN RING_CARRIER_TAC THEN ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN q25 ASSUME_TAC THENL [REPEAT STRIP_TAC THEN REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM] THEN MATCH_MP_TAC INTEGRAL_ELEMENT_QUADRATIC THEN MAP_EVERY EXISTS_TAC [q24, q23] THEN ASM_REWRITE_TAC [RING_OF_INT_NEG, RING_OF_INT_1], ALL_TAC] THEN REWRITE_TAC [ring_unit] THEN CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN EXISTS_TAC q22 THEN REWRITE_TAC [RING_OF_INTEGERS] THEN CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_SUB, RING_OF_INT] THEN MP_TAC v21 THEN ASM_REWRITE_TAC [RING_OF_INT], MP_TAC v15 THEN ASM_REWRITE_TAC [RING_OF_INT]]])

  let QUADRATIC_FIELD_UNITS_IMAGINARY ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!k:A ring t c y.
            ring_mul k c t = ring_1 k
            ==> ring_mul k c (ring_mul k t y) = y")
    let r2 ← RING_RULE (← q r"!k:A ring t y c.
            ring_mul k c t = ring_1 k
            ==> ring_mul k c (ring_mul k t y) = y")
    let r3 ← RING_RULE (← q r"!k:A ring z t y c.
            ring_mul k c t = ring_1 k /\ ring_mul k c z = y
            ==> z = ring_mul k t y")
    let r4 ← INT_ARITH (← q r"d:int < &0 ==> ~(d = &1)")
    prove
      r"!k (x:A) d.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
          x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
          squarefree(num_of_int(abs d)) /\ d < &0
          ==> {u | ring_unit (ring_of_integers k) u} =
              IMAGE (\(a,b). ring_mul k (ring_inv k (ring_of_num k 2))
                               (ring_add k (ring_of_int k a)
                                           (ring_mul k (ring_of_int k b) x)))
                    {(a,b) | a pow 2 - d * b pow 2 = &4} /\
              (!a b a' b'.
                  a pow 2 - d * b pow 2 = &4 /\
                  a' pow 2 - d * b' pow 2 = &4 /\
                  ring_mul k (ring_inv k (ring_of_num k 2))
                    (ring_add k (ring_of_int k a)
                                (ring_mul k (ring_of_int k b) x)) =
                  ring_mul k (ring_inv k (ring_of_num k 2))
                    (ring_add k (ring_of_int k a')
                                (ring_mul k (ring_of_int k b') x))
                  ==> a = a' /\ b = b')"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN (← q r"~((x:A) IN ring_carrier(subfield_generated k {ring_0 k}))") ASSUME_TAC THENL [MATCH_MP_TAC SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD THEN EXISTS_TAC (← q r"d:int") THEN ASM_MESON_TAC [number_field, r4], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_inv k (ring_of_num k 2) IN ring_carrier k /\
      ring_mul k (ring_of_num k 2) (ring_inv k (ring_of_num k 2)) =
      ring_1 (k:A ring)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_INV, FIELD_MUL_RINV, RING_OF_NUM, NUMBER_FIELD_RING_OF_NUM_EQ_0, ARITH_EQ], ALL_TAC] THEN CONJ_TAC THENL [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_IMAGE, EXISTS_PAIR_THM] THEN X_GEN_TAC (← q r"z:A") THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"d:int"), (← q r"z:A")] QUADRATIC_FIELD_UNIT_IMAGINARY) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [IN_ELIM_THM, PAIR_EQ] THEN EQ_TAC THENL [DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"a:int") (X_CHOOSE_THEN (← q r"b:int") STRIP_ASSUME_TAC))) THEN MAP_EVERY EXISTS_TAC [(← q r"a:int"), (← q r"b:int")] THEN CONJ_TAC THENL [ALL_TAC, MAP_EVERY EXISTS_TAC [(← q r"a:int"), (← q r"b:int")] THEN ASM_REWRITE_TAC []] THEN REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"ring_inv k (ring_of_num k 2):A"), (← q r"ring_add k (ring_of_int k a) (ring_mul k (ring_of_int k b) x):A"), (← q r"ring_of_num k 2:A")] r3) THEN ASM_SIMP_TAC [RING_ADD, RING_MUL, RING_OF_INT, RING_OF_NUM], DISCH_THEN (X_CHOOSE_THEN (← q r"a:int") (X_CHOOSE_THEN (← q r"b:int") (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC))) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a':int") (X_CHOOSE_THEN (← q r"b':int") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN SUBST_ALL_TAC)))) THEN ASM_SIMP_TAC [RING_MUL, RING_ADD, RING_OF_INT, RING_OF_NUM] THEN MAP_EVERY EXISTS_TAC [(← q r"a':int"), (← q r"b':int")] THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_inv k (ring_of_num k 2):A"), (← q r"ring_add k (ring_of_int k a') (ring_mul k (ring_of_int k b') x):A"), (← q r"ring_of_num k 2:A")] r2) THEN ASM_SIMP_TAC [RING_ADD, RING_MUL, RING_OF_INT, RING_OF_NUM]], REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"a:int"), (← q r"b:int"), (← q r"a':int"), (← q r"b':int")] QUADRATIC_FIELD_INT_COORDINATES_EQ) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [ASM_MESON_TAC [number_field], DISCH_THEN (SUBST1_TAC o SYM)] THEN FIRST_X_ASSUM (MP_TAC o (AP_TERM (← q r"ring_mul k (ring_of_num k 2):A->A"))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_inv k (ring_of_num k 2):A")] r1) THEN DISCH_THEN (MP_TAC o (SPEC (← q r"ring_of_num k 2:A"))) THEN ASM_SIMP_TAC [RING_ADD, RING_MUL, RING_OF_INT, RING_OF_NUM]])

  let QUADRATIC_FIELD_UNITS_IMAGINARY_CARD ← prove
    r"!k (x:A) d.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
        squarefree(num_of_int(abs d)) /\ d < &0
        ==> {u | ring_unit (ring_of_integers k) u} HAS_SIZE
            (if d = -- &1 then 4 else if d = -- &3 then 6 else 2)"
    (REPEAT GEN_TAC THEN DISCH_THEN (fun th => tactic_of do pure (STRIP_ASSUME_TAC th THEN MP_TAC (← MATCH_MP QUADRATIC_FIELD_UNITS_IMAGINARY th))) THEN DISCH_THEN (CONJUNCTS_THEN2 SUBST1_TAC (LABEL_TAC "inj")) THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL [REWRITE_TAC [FORALL_PAIR_THM, IN_ELIM_PAIR_THM, PAIR_EQ] THEN CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV) THEN REPEAT GEN_TAC THEN STRIP_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(d = -- &4:int)") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"squarefree(num_of_int(abs(-- &4:int)))") THEN CONV_TAC (ONCE_DEPTH_CONV INT_REDUCE_CONV) THEN REWRITE_TAC [NUM_OF_INT_OF_NUM, squarefree, NOT_FORALL_THM, NOT_IMP] THEN EXISTS_TAC (← q r"2") THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [DIVIDES_REFL], ALL_TAC] THEN SUBGOAL_THEN (← q r"{(a,b) | a pow 2 - d * b pow 2 = &4:int} =
    if d = -- &1 then {(&2,&0),(-- &2,&0),(&0,&2),(&0,-- &2)}
    else if d = -- &3
    then {(&2,&0),(-- &2,&0),(&1,&1),(&1,-- &1),(-- &1,&1),(-- &1,-- &1)}
    else {(&2,&0),(-- &2,&0)}") SUBST1_TAC THENL [REWRITE_TAC [EXTENSION, FORALL_PAIR_THM, IN_ELIM_PAIR_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:int"), (← q r"b:int")] THEN EQ_TAC THENL [DISCH_TAC THEN MP_TAC (← SPECL [(← q r"a:int"), (← q r"b:int"), (← q r"d:int")] INT_NORM_FORM_4_IMAGINARY) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC [] THEN CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC [] THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY, PAIR_EQ] THEN CONV_TAC INT_REDUCE_CONV, REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY, PAIR_EQ] THEN DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN (CONJUNCTS_THEN SUBST1_TAC)) THEN CONV_TAC INT_REDUCE_CONV THEN INT_ARITH_TAC], ASM_CASES_TAC (← q r"d = -- &1:int") THEN ASM_REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"d = -- &3:int") THEN ASM_REWRITE_TAC [] THEN SIMP_TAC [HAS_SIZE, FINITE_INSERT, FINITE_EMPTY, CARD_CLAUSES] THEN REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY, PAIR_EQ] THEN CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC [] THEN CONV_TAC NUM_REDUCE_CONV])

  let QUADRATIC_FIELD_UNITS_IMAGINARY_GENERIC ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"2 = 1 + 1")
    prove
      r"!k (x:A) d.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
          x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
          squarefree(num_of_int(abs d)) /\ d < &0 /\
          ~(d = -- &1) /\ ~(d = -- &3)
          ==> {u | ring_unit (ring_of_integers k) u} =
              {ring_1 k, ring_neg k (ring_1 k)}"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"d:int")] QUADRATIC_FIELD_UNITS_IMAGINARY_CARD) THEN ASM_REWRITE_TAC [HAS_SIZE] THEN STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [SUBGOAL_THEN (← q r"ring_unit (ring_of_integers k) (ring_1 k) /\
        ring_unit (ring_of_integers k) (ring_neg k (ring_1 (k:A ring)))") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_UNIT_1) THEN DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] th)] THEN MP_TAC (← MATCH_MP RING_UNIT_NEG th))) THEN REWRITE_TAC [RING_OF_INTEGERS], REWRITE_TAC [SUBSET, IN_INSERT, NOT_IN_EMPTY, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []], SUBGOAL_THEN (← q r"~(ring_1 k = ring_neg k (ring_1 (k:A ring)))") ASSUME_TAC THENL [DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"2")] NUMBER_FIELD_RING_OF_NUM_EQ_0) THEN ASM_REWRITE_TAC [ARITH_EQ] THEN REWRITE_TAC [r1, RING_OF_NUM_ADD, RING_OF_NUM_1] THEN FIRST_X_ASSUM (fun th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN SIMP_TAC [RING_ADD_RNEG, RING_1], ASM_SIMP_TAC [CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY, IN_INSERT, NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV]])

  let QUADRATIC_FIELD_FUNDAMENTAL_UNIT ← prove
    r"!k (x:A) d (g:A->complex).
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
        ring_pow k x 2 = ring_of_int k d /\ &0 < d /\
        g IN complex_embeddings k
        ==> ?e. ring_unit (ring_of_integers k) e /\ &1 < Re(g e) /\
                (!u. ring_unit (ring_of_integers k) u <=>
                     ?n. u = group_zpow (unit_group(ring_of_integers k)) e n \/
                         u = ring_neg k
                              (group_zpow (unit_group(ring_of_integers k))
                                          e n)) /\
                (!n. group_zpow (unit_group(ring_of_integers k)) e n =
                     ring_1 k ==> n = &0) /\
                (!u. ring_unit (ring_of_integers k) u /\ &1 < Re(g u)
                     ==> Re(g e) <= Re(g u)) /\
                number_field_regulator k = log(Re(g e))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"d:int")] QUADRATIC_FIELD_INFINITE_PLACES) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"d:int")] QUADRATIC_FIELD_REAL_EMBEDDINGS) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(g:A->complex) IN real_embeddings k") ASSUME_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"g:A->complex")] NUMBER_FIELD_FUNDAMENTAL_UNIT_REAL) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"e:A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC NUMBER_FIELD_REGULATOR_FUNDAMENTAL_UNIT_REAL THEN ASM_MESON_TAC [])

  let QUADRATIC_FIELD_PELL_UNIT ← prove
    r"!k (y:A) D a b.
        field k /\ y IN ring_carrier k /\ ring_pow k y 2 = ring_of_int k D /\
        a pow 2 - D * b pow 2 = &1
        ==> ring_unit (ring_of_integers k)
              (ring_add k (ring_of_int k a) (ring_mul k (ring_of_int k b) y))"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"(y:A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM] THEN MATCH_MP_TAC INTEGRAL_ELEMENT_QUADRATIC THEN MAP_EVERY EXISTS_TAC [(← q r"&0:int"), (← q r"--D:int")] THEN ASM_REWRITE_TAC [RING_OF_INT_0, RING_OF_INT_NEG] THEN ASM_SIMP_TAC [RING_MUL_LZERO, RING_ADD_LZERO, RING_OF_INT, RING_ADD_RNEG, RING_NEG], ALL_TAC] THEN REWRITE_TAC [ring_unit] THEN CONJ_TAC THENL [MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_ADD) THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_MUL) THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_OF_INT) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN ASM_MESON_TAC [], ALL_TAC] THEN EXISTS_TAC (← q r"ring_add k (ring_of_int k a) (ring_mul k (ring_of_int k (--b)) y):A") THEN CONJ_TAC THENL [MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_ADD) THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_MUL) THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_OF_INT) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN ASM_MESON_TAC [], ALL_TAC] THEN REWRITE_TAC [RING_OF_INTEGERS] THEN FIRST_X_ASSUM (MP_TAC o (AP_TERM (← q r"ring_of_int (k:A ring)"))) THEN ASM_REWRITE_TAC [RING_OF_INT_SUB, RING_OF_INT_MUL, RING_OF_INT_POW, RING_OF_INT_NEG, RING_OF_INT_1] THEN UNDISCH_TAC (← q r"ring_pow k y 2 = ring_of_int k D:A") THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:int")] RING_OF_INT) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"b:int")] RING_OF_INT) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"D:int")] RING_OF_INT) THEN UNDISCH_TAC (← q r"(y:A) IN ring_carrier k") THEN MAP_EVERY (fun t => tactic_of do pure (SPEC_TAC (t, (← (do let z1 ← (do let z2 ← (pure t); pure (type_of z2)); genvar z1))))) [(← q r"ring_of_int k a:A"), (← q r"ring_of_int k b:A"), (← q r"ring_of_int k D:A"), (← q r"y:A")] THEN RING_TAC)

  let QUADRATIC_FIELD_UNIT_POW_IN_ORDER ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!k:A ring P W v t T C a b x.
        ring_sub k (ring_mul k P W) P = ring_mul k (ring_mul k T C) t /\
        ring_mul k P v = ring_1 k /\
        ring_mul k T (ring_mul k v t) = ring_add k a (ring_mul k b x)
        ==> W = ring_add k (ring_add k (ring_1 k) (ring_mul k C a))
                           (ring_mul k b (ring_mul k C x))")
    let r2 ← ARITH_RULE (← q r"p < q ==> p + (q - p) = q:num")
    let r10 ← TAUT (← q r"(~p ==> F) ==> p")
    let r11 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!k (x:A) d c e.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
          x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
          squarefree(num_of_int(abs d)) /\ ~(d = &1) /\ ~(c = &0) /\
          ring_unit (ring_of_integers k) e
          ==> ?m a b. 1 <= m /\
                      ring_pow k e m =
                      ring_add k (ring_of_int k a)
                        (ring_mul k (ring_of_int k b)
                           (ring_mul k (ring_of_int k c) x))"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN (← q r"ring_char(k:A ring) = 0") ASSUME_TAC THENL [ASM_MESON_TAC [number_field], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_of_int k (&2 * c) IN ring_carrier(ring_of_integers k) /\
      ~(ring_of_int k (&2 * c) = ring_0 (k:A ring))") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_OF_INT_EQ_0_CHAR_0] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"&2 * c:int")] RING_OF_INT) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN ASM_INT_ARITH_TAC, ALL_TAC] THEN ABBREV_TAC (← q r"j = ideal_generated (ring_of_integers k)
                      {ring_of_int k (&2 * c):A}") THEN SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers k) (j:A->bool) /\
      FINITE(ring_carrier(quotient_ring (ring_of_integers k) j))") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r11 THEN CONJ_TAC THENL [EXPAND_TAC "j" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED], DISCH_TAC THEN MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_of_int k (&2 * c) IN (j:A->bool)") MP_TAC THENL [EXPAND_TAC "j" THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN ASM_REWRITE_TAC [SING_SUBSET, IN_SING], ASM_REWRITE_TAC [IN_SING]]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!n. ring_pow k e n IN ring_carrier(ring_of_integers k) /\
          ring_unit (ring_of_integers k) (ring_pow k (e:A) n)") ASSUME_TAC THENL [GEN_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"e:A"), (← q r"n:num")] RING_UNIT_POW) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN MESON_TAC [RING_UNIT_IN_CARRIER], ALL_TAC] THEN SUBGOAL_THEN (← q r"?p q. p < q /\
            ring_coset (ring_of_integers k) j (ring_pow k e q) =
            ring_coset (ring_of_integers k) j (ring_pow k (e:A) p)") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r10 THEN DISCH_THEN (ASSUME_TAC o (REWRITE_RULE [NOT_EXISTS_THM])) THEN MP_TAC (← ISPECL [(← q r"\n. ring_coset (ring_of_integers k) j (ring_pow k (e:A) n)"), (← q r"(:num)")] INFINITE_IMAGE) THEN ANTS_TAC THENL [REWRITE_TAC [num_INFINITE, IN_UNIV] THEN MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC [] THEN CONJ_TAC THENL [MESON_TAC [], ASM_MESON_TAC []], REWRITE_TAC [INFINITE] THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"ring_carrier(quotient_ring (ring_of_integers k) (j:A->bool))") THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, SUBSET, FORALL_IN_IMAGE, IN_UNIV] THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC []], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"j:A->bool"), (← q r"ring_pow k e q:A"), (← q r"ring_pow k e p:A")] RING_COSET_EQ) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o ((checkM (fun z7 => (do let z8 ← (do let z9 ← (pure z7); pure (concl z9)); pure (is_eq z8)))) o (checkM (fun th => (do let z6 ← (q r"j:A->bool"); let z5 ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); liftExcept (rand z3)); pure (z5 == z6))))))) THEN ASM_SIMP_TAC [IDEAL_GENERATED_SING_ALT, IN_ELIM_THM, RING_OF_INTEGERS] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"t:A") STRIP_ASSUME_TAC) THEN ABBREV_TAC (← q r"v = ring_inv (ring_of_integers k) (ring_pow k e p):A") THEN SUBGOAL_THEN (← q r"v IN ring_carrier(ring_of_integers k) /\
      ring_mul k (ring_pow k e p) v = ring_1 (k:A ring)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "v" THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_pow k e p:A")] RING_MUL_RINV) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_pow k e p:A")] RING_INV) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_carrier(ring_of_integers k) SUBSET ring_carrier(k:A ring)") ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"d:int"), (← q r"ring_mul k v t:A")] QUADRATIC_FIELD_INTEGRAL_COORDINATES) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"v:A"), (← q r"t:A")] RING_MUL) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], REWRITE_TAC [LEFT_IMP_EXISTS_THM]] THEN MAP_EVERY X_GEN_TAC [(← q r"A:int"), (← q r"B:int"), (← q r"N:int")] THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"q - p:num"), (← q r"&1 + c * A:int"), (← q r"B:int")] THEN CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"(e:A) IN ring_carrier k /\ (v:A) IN ring_carrier k /\
                  (t:A) IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [SUBSET, RING_UNIT_IN_CARRIER], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"e:A"), (← q r"p:num"), (← q r"q - p:num")] RING_POW_ADD) THEN ASM_SIMP_TAC [r2] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"ring_sub k (ring_pow k e q) (ring_pow k e p) =
      ring_mul k (ring_of_int k (&2 * c)) (t:A)") THEN ASM_REWRITE_TAC [RING_OF_INT_MUL, RING_OF_INT_OF_NUM] THEN DISCH_TAC THEN REWRITE_TAC [RING_OF_INT_ADD, RING_OF_INT_MUL, RING_OF_INT_1] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_pow k e p:A"), (← q r"ring_pow k e (q - p):A"), (← q r"v:A"), (← q r"t:A"), (← q r"ring_of_num k 2:A"), (← q r"ring_of_int k c:A"), (← q r"ring_of_int k A:A"), (← q r"ring_of_int k B:A"), (← q r"x:A")] r1) THEN ASM_SIMP_TAC [RING_POW, RING_OF_NUM, RING_OF_INT])

  -- @@RETURN BEGIN
  return { QUADRATIC_FIELD_UNIT_IMAGINARY, QUADRATIC_FIELD_UNITS_IMAGINARY,
           QUADRATIC_FIELD_UNITS_IMAGINARY_CARD, QUADRATIC_FIELD_UNITS_IMAGINARY_GENERIC,
           QUADRATIC_FIELD_FUNDAMENTAL_UNIT, QUADRATIC_FIELD_PELL_UNIT,
           QUADRATIC_FIELD_UNIT_POW_IN_ORDER }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- quadratic_units.ml phrases from line 1249 to 1554                      -/
/- ---------------------------------------------------------------------- -/

structure QuadraticUnits03 where
  -- @@FIELDS
  QUADRATIC_FIELD_PELL_SOLUTION : thm
  PELL_SOLUTION_IMP_INFINITE : thm
  PELL_EQUATION_INFINITE : thm
  PELL_EQUATION_INFINITE_NUM : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupQuadraticUnits03 [HolBase] (D : QuadraticUnitsDeps) (BQuadraticUnits01 : QuadraticUnits01) (BQuadraticUnits02 : QuadraticUnits02) :
    ExceptT String IO QuadraticUnits03 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_INT_ARITH_TAC, ASM_MESON_TAC,
        INDUCT_TAC, INT_ARITH_TAC, INT_REDUCE_CONV, MESON_TAC, REAL_RING, .. } := D
  let { ARITH_EQ, COMPLEX_EMBEDDINGS_NONEMPTY, CONTRAPOS_THM, EXISTS_PAIR_THM,
        EXTENSION, FINITE_EMPTY, FINITE_IMAGE, FINITE_INSERT, FINITE_SUBSET,
        FORALL_IN_IMAGE, FORALL_PAIR_THM, FST, INFINITE, INFINITE_IMAGE,
        INFINITE_SUPERSET, INT_ABS_POS, INT_ENTIRE, INT_LE_LMUL, INT_LE_MUL,
        INT_LE_MUL2, INT_LE_SQUARE_ABS, INT_LT_IMP_LE, INT_LT_MUL, INT_LT_REFL,
        INT_LT_RMUL_EQ, INT_MUL_LID, INT_MUL_LZERO, INT_MUL_RZERO, INT_OF_NUM_ADD,
        INT_OF_NUM_EQ, INT_OF_NUM_LT, INT_OF_NUM_MUL, INT_OF_NUM_OF_INT,
        INT_OF_NUM_POW, INT_POW2_ABS, INT_POW_LT, INT_SQUAREFREE_DECOMPOSITION,
        INT_SUB_RZERO, IN_ELIM_PAIR_THM, IN_ELIM_THM, IN_IMAGE, IN_INSERT, IN_UNIV,
        LEFT_IMP_EXISTS_THM, LE_1, MEMBER_NOT_EMPTY, NOT_IN_EMPTY,
        NUMBER_FIELD_IMP_FIELD, PAIR, PAIR_EQ, PRODUCT_CLAUSES, QUADRATIC_FIELD_EXISTS, .. } := D.core1
  let { REAL_ABS_MUL, REAL_ADD_RID, REAL_EMBEDDINGS_MONOMORPHISM, REAL_FIELD_CLAUSES,
        REAL_MUL_LZERO, REAL_MUL_RID, REAL_NORM, REAL_OF_INT_CLAUSES, REAL_POW_LT_1,
        REAL_RING_CLAUSES, REAL_RING_OF_INT, RE_NEG, RING_HOMOMORPHISM_POW,
        RING_HOMOMORPHISM_RING_OF_INT, RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL,
        RING_OF_INT, RING_OF_INTEGERS, RING_OF_INTEGERS_UNIT_NONZERO,
        RING_OF_INTEGERS_UNIT_NORM_PRODUCT, RING_OF_INT_IN_SUBFIELD_GENERATED,
        RING_POW, RING_UNIT_POW, SND, SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD, SUBSET,
        TRANSITIVE_STEPWISE_LT, WLOG_LT, int_abs_th, int_mul_th, int_of_num_th,
        int_pow_th, int_sub_th, num_INFINITE, num_RECURSION, number_field,
        real_embeddings, ring_homomorphism, .. } := D.core2
  let { QUADRATIC_FIELD_CONJUGATE_EMBEDDING, QUADRATIC_FIELD_REAL_EMBEDDINGS, .. } := BQuadraticUnits01
  let { QUADRATIC_FIELD_FUNDAMENTAL_UNIT, QUADRATIC_FIELD_UNIT_POW_IN_ORDER, .. } := BQuadraticUnits02
  -- @@SCOPE END

  let QUADRATIC_FIELD_PELL_SOLUTION ← prove
    r"!k (x:A) d c.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
        squarefree(num_of_int(abs d)) /\ &0 < d /\ ~(d = &1) /\ ~(c = &0)
        ==> ?a b. a pow 2 - (d * c pow 2) * b pow 2 = &1 /\ ~(b = &0)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN (← q r"~((x:A) IN ring_carrier(subfield_generated k {ring_0 k}))") ASSUME_TAC THENL [MATCH_MP_TAC SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD THEN EXISTS_TAC (← q r"d:int") THEN ASM_MESON_TAC [number_field], ALL_TAC] THEN FIRST_ASSUM ((X_CHOOSE_TAC (← q r"g:A->complex")) o ((REWRITE_RULE [(← GSYM MEMBER_NOT_EMPTY)]) o (MATCH_MP COMPLEX_EMBEDDINGS_NONEMPTY))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"d:int"), (← q r"g:A->complex")] QUADRATIC_FIELD_FUNDAMENTAL_UNIT) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"e:A") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (fun (_ : thm) => ALL_TAC)))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"d:int"), (← q r"c:int"), (← q r"e:A")] QUADRATIC_FIELD_UNIT_POW_IN_ORDER) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"m:num"), (← q r"a:int"), (← q r"b:int")] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"g:A->complex")] QUADRATIC_FIELD_CONJUGATE_EMBEDDING) THEN ASM_SIMP_TAC [RING_OF_INT_IN_SUBFIELD_GENERATED] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"h:A->complex") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"d:int")] QUADRATIC_FIELD_REAL_EMBEDDINGS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN SUBGOAL_THEN (← q r"ring_homomorphism(k,real_ring) (\x. Re((g:A->complex) x)) /\
    ring_homomorphism(k,real_ring) (\x. Re((h:A->complex) x))") STRIP_ASSUME_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC RING_MONOMORPHISM_IMP_HOMOMORPHISM THEN MATCH_MP_TAC REAL_EMBEDDINGS_MONOMORPHISM THEN ASM_REWRITE_TAC [IN_INSERT], ALL_TAC] THEN SUBGOAL_THEN (← q r"(e:A) IN ring_carrier k /\
                ring_unit (ring_of_integers k) (ring_pow k e m)") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_UNIT_NONZERO], MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"e:A"), (← q r"m:num")] RING_UNIT_POW) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS]], ALL_TAC] THEN MAP_EVERY (fun th => tactic_of do pure (ASSUME_TAC (← REWRITE_RULE [REAL_FIELD_CLAUSES, REAL_RING_OF_INT] th))) [(← MATCH_MP RING_HOMOMORPHISM_POW (← ASSUME (← q r"ring_homomorphism(k,real_ring) (\x. Re((g:A->complex) x))"))), (← MATCH_MP RING_HOMOMORPHISM_RING_OF_INT (← ASSUME (← q r"ring_homomorphism(k,real_ring) (\x. Re((g:A->complex) x))"))), (← MATCH_MP RING_HOMOMORPHISM_RING_OF_INT (← ASSUME (← q r"ring_homomorphism(k,real_ring) (\x. Re((h:A->complex) x))")))] THEN SUBGOAL_THEN (← q r"&1 < Re((g:A->complex)(ring_pow k e m))") ASSUME_TAC THENL [ASM_SIMP_TAC [] THEN MATCH_MP_TAC REAL_POW_LT_1 THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"abs(Re((g:A->complex)(ring_pow k e m))) *
    abs(Re((h:A->complex)(ring_pow k e m))) = &1") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"~((g:A->complex) = h)") ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_pow k e m:A")] RING_OF_INTEGERS_UNIT_NORM_PRODUCT) THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [PRODUCT_CLAUSES, FINITE_INSERT, FINITE_EMPTY, IN_INSERT, NOT_IN_EMPTY, REAL_MUL_RID] THEN SUBGOAL_THEN (← q r"real((g:A->complex)(ring_pow k e m)) /\
                  real((h:A->complex)(ring_pow k e m))") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"real_embeddings k = {g:A->complex, h}") THEN REWRITE_TAC [EXTENSION, real_embeddings, IN_ELIM_THM, IN_INSERT, NOT_IN_EMPTY] THEN DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"g:A->complex") th) THEN MP_TAC (← SPEC (← q r"h:A->complex") th))) THEN REWRITE_TAC [] THEN ASM_SIMP_TAC [RING_POW], ASM_SIMP_TAC [REAL_NORM] THEN MESON_TAC []], ALL_TAC] THEN DISCH_THEN SUBST_ALL_TAC THEN SUBGOAL_THEN (← q r"Re((g:A->complex)
      (ring_add k (ring_of_int k a)
        (ring_mul k (ring_of_int k b) (ring_mul k (ring_of_int k c) x)))) =
    real_of_int a + real_of_int b * (real_of_int c * Re(g x)) /\
    Re((h:A->complex)
      (ring_add k (ring_of_int k a)
        (ring_mul k (ring_of_int k b) (ring_mul k (ring_of_int k c) x)))) =
    real_of_int a + real_of_int b * (real_of_int c * --Re(g x))") (CONJUNCTS_THEN SUBST_ALL_TAC) THENL [UNDISCH_TAC (← q r"ring_homomorphism(k,real_ring) (\x. Re((g:A->complex) x))") THEN UNDISCH_TAC (← q r"ring_homomorphism(k,real_ring) (\x. Re((h:A->complex) x))") THEN REWRITE_TAC [ring_homomorphism, REAL_RING_CLAUSES] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [RING_OF_INT, RING_MUL, RE_NEG], ALL_TAC] THEN SUBGOAL_THEN (← q r"Re((g:A->complex) x) pow 2 = real_of_int d") ASSUME_TAC THENL [FIRST_X_ASSUM (MP_TAC o ((SPECL [(← q r"x:A"), (← q r"2")]) o ((checkM (fun z8 => (do let z9 ← (do let z10 ← (pure z8); pure (concl z10)); pure (is_forall z9)))) o (checkM (fun th => (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); canM (fun z3 => (do let z4 ← (pure z3); find_termM (fun z5 => (do let z7 ← (pure z5); let z6 ← (q r"ring_pow:A ring->A->num->A"); pure (z6 == z7))) z4)) z1)))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ACCEPT_TAC o SYM), ALL_TAC] THEN SUBGOAL_THEN (← q r"(real_of_int a + real_of_int b * real_of_int c * Re((g:A->complex) x)) *
    (real_of_int a + real_of_int b * real_of_int c * --Re(g x)) =
    real_of_int(a pow 2 - (d * c pow 2) * b pow 2)") ASSUME_TAC THENL [REWRITE_TAC [int_sub_th, int_mul_th, int_pow_th] THEN UNDISCH_TAC (← q r"Re((g:A->complex) x) pow 2 = real_of_int d") THEN CONV_TAC REAL_RING, ALL_TAC] THEN SUBGOAL_THEN (← q r"abs((a:int) pow 2 - (d * c pow 2) * b pow 2) = &1") ASSUME_TAC THENL [ONCE_REWRITE_TAC [(← GSYM (← CONJUNCT1 REAL_OF_INT_CLAUSES))] THEN REWRITE_TAC [int_abs_th, int_of_num_th] THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC [REAL_ABS_MUL], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(b:int = &0)") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"&1 < real_of_int a + real_of_int(&0) * real_of_int c *
                           Re((g:A->complex) x)") THEN UNDISCH_TAC (← q r"abs((a:int) pow 2 - (d * c pow 2) * &0 pow 2) = &1") THEN REWRITE_TAC [int_of_num_th, REAL_MUL_LZERO, REAL_ADD_RID] THEN CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC [INT_MUL_RZERO, INT_SUB_RZERO] THEN ONCE_REWRITE_TAC [(← GSYM INT_POW2_ABS)] THEN REWRITE_TAC [(← GSYM REAL_OF_INT_CLAUSES)] THEN DISCH_TAC THEN DISCH_TAC THEN MP_TAC (← SPECL [(← q r"&2:int"), (← q r"a:int")] INT_LE_SQUARE_ABS) THEN ASM_INT_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"&2 <= (d:int) /\ &1 <= (c:int) pow 2 /\ &1 <= (b:int) pow 2") STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THENL [ASM_INT_ARITH_TAC, MP_TAC (← SPECL [(← q r"&1:int"), (← q r"c:int")] INT_LE_SQUARE_ABS), MP_TAC (← SPECL [(← q r"&1:int"), (← q r"b:int")] INT_LE_SQUARE_ABS)] THEN CONV_TAC INT_REDUCE_CONV THEN ASM_INT_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"&2 <= (d * c pow 2) * (b:int) pow 2") ASSUME_TAC THENL [MP_TAC (← SPECL [(← q r"&2:int"), (← q r"d:int"), (← q r"&1:int"), (← q r"(c:int) pow 2")] INT_LE_MUL2) THEN MP_TAC (← SPECL [(← q r"&2:int"), (← q r"d * (c:int) pow 2"), (← q r"&1:int"), (← q r"(b:int) pow 2")] INT_LE_MUL2) THEN ASM_INT_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"~(a:int = &0)") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"abs((&0:int) pow 2 - (d * c pow 2) * b pow 2) = &1") THEN CONV_TAC INT_REDUCE_CONV THEN ASM_INT_ARITH_TAC, ALL_TAC] THEN MAP_EVERY EXISTS_TAC [(← q r"(a:int) pow 2 + (d * c pow 2) * b pow 2"), (← q r"&2 * (a:int) * b")] THEN ASM_REWRITE_TAC [INT_ENTIRE, INT_OF_NUM_EQ, ARITH_EQ] THEN SUBGOAL_THEN (← q r"((a:int) pow 2 + (d * c pow 2) * b pow 2) pow 2 -
    (d * c pow 2) * (&2 * a * b) pow 2 =
    (abs(a pow 2 - (d * c pow 2) * b pow 2)) pow 2") SUBST1_TAC THENL [REWRITE_TAC [INT_POW2_ABS] THEN INT_ARITH_TAC, ASM_REWRITE_TAC [] THEN CONV_TAC INT_REDUCE_CONV])

  let PELL_SOLUTION_IMP_INFINITE ← prove
    r"!d a b:int.
        &0 < d /\ a pow 2 - d * b pow 2 = &1 /\ ~(b = &0)
        ==> INFINITE {(x,y) | &0 < x /\ &0 < y /\ x pow 2 - d * y pow 2 = &1}"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"&1 <= (b:int) pow 2") ASSUME_TAC THENL [MP_TAC (← SPECL [(← q r"&1:int"), (← q r"b:int")] INT_LE_SQUARE_ABS) THEN CONV_TAC INT_REDUCE_CONV THEN ASM_INT_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"&1 <= d * (b:int) pow 2") ASSUME_TAC THENL [MP_TAC (← SPECL [(← q r"&1:int"), (← q r"d:int"), (← q r"&1:int"), (← q r"(b:int) pow 2")] INT_LE_MUL2) THEN ASM_INT_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"&2 <= abs(a:int)") ASSUME_TAC THENL [MP_TAC (← SPECL [(← q r"a:int"), (← q r"&1:int")] INT_LE_SQUARE_ABS) THEN CONV_TAC INT_REDUCE_CONV THEN ASM_INT_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"?p q:int. p pow 2 - d * q pow 2 = &1 /\ &2 <= p /\ &1 <= q") STRIP_ASSUME_TAC THENL [MAP_EVERY EXISTS_TAC [(← q r"abs(a:int)"), (← q r"abs(b:int)")] THEN ASM_REWRITE_TAC [INT_POW2_ABS] THEN ASM_INT_ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"(p,q):int#int"), (← q r"\(z:int#int) (n:num).
                    (FST z * p + d * SND z * q, FST z * q + SND z * p)")] num_RECURSION) THEN REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"f:num->int#int") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"!n. FST(f n) pow 2 - d * SND(f n) pow 2 = &1 /\
        &2 <= FST((f:num->int#int) n) /\ &1 <= SND(f n)") ASSUME_TAC THENL [INDUCT_TAC THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"FST((f:num->int#int) n) pow 2 - d * SND(f n) pow 2 = &1 /\
                 &2 <= FST(f n) /\ &1 <= SND(f n)") THEN SPEC_TAC ((← q r"SND((f:num->int#int) n)"), (← q r"v:int")) THEN SPEC_TAC ((← q r"FST((f:num->int#int) n)"), (← q r"u:int")) THEN REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"&4 <= u * p /\ &0 <= d * v * q /\ &0 <= u * q /\
                  &2 <= v * (p:int)") STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THENL [MP_TAC (← SPECL [(← q r"&2:int"), (← q r"u:int"), (← q r"&2:int"), (← q r"p:int")] INT_LE_MUL2), MATCH_MP_TAC INT_LE_MUL THEN CONJ_TAC THENL [ALL_TAC, MATCH_MP_TAC INT_LE_MUL], MATCH_MP_TAC INT_LE_MUL, MP_TAC (← SPECL [(← q r"&1:int"), (← q r"v:int"), (← q r"&2:int"), (← q r"p:int")] INT_LE_MUL2)] THEN ASM_INT_ARITH_TAC, ALL_TAC] THEN REPEAT CONJ_TAC THENL [SUBGOAL_THEN (← q r"(u * p + d * v * q) pow 2 - d * (u * q + v * p) pow 2 =
        (u pow 2 - d * v pow 2) * ((p:int) pow 2 - d * q pow 2)") SUBST1_TAC THENL [INT_ARITH_TAC, ASM_REWRITE_TAC [INT_MUL_LID]], ASM_INT_ARITH_TAC, ASM_INT_ARITH_TAC], ALL_TAC] THEN SUBGOAL_THEN (← q r"!m n. m < n ==> FST((f:num->int#int) m) < FST(f n)") ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"\m n. FST((f:num->int#int) m) < FST(f n)") TRANSITIVE_STEPWISE_LT) THEN REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL [INT_ARITH_TAC, ALL_TAC] THEN X_GEN_TAC (← q r"n:num") THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"n:num")) o (checkM (fun z5 => (do let z6 ← (do pure (Prod.snd (← (do let z7 ← (do let z8 ← (pure z5); pure (concl z8)); liftExcept (dest_forall z7))))); pure (is_conj z6)))))) THEN SPEC_TAC ((← q r"SND((f:num->int#int) n)"), (← q r"v:int")) THEN SPEC_TAC ((← q r"FST((f:num->int#int) n)"), (← q r"u:int")) THEN REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"u * &2 <= u * (p:int) /\ &0 <= d * v * (q:int)") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [MATCH_MP_TAC INT_LE_LMUL THEN ASM_INT_ARITH_TAC, MATCH_MP_TAC INT_LE_MUL THEN CONJ_TAC THENL [ALL_TAC, MATCH_MP_TAC INT_LE_MUL] THEN ASM_INT_ARITH_TAC], ASM_INT_ARITH_TAC], ALL_TAC] THEN MATCH_MP_TAC INFINITE_SUPERSET THEN EXISTS_TAC (← q r"IMAGE (f:num->int#int) (:num)") THEN CONJ_TAC THENL [MATCH_MP_TAC INFINITE_IMAGE THEN REWRITE_TAC [num_INFINITE, IN_UNIV] THEN MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC [] THEN CONJ_TAC THENL [MESON_TAC [], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"m:num"), (← q r"n:num")] THEN DISCH_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPECL [(← q r"m:num"), (← q r"n:num")])) THEN ASM_REWRITE_TAC [INT_LT_REFL], REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_UNIV, IN_ELIM_THM] THEN X_GEN_TAC (← q r"n:num") THEN MAP_EVERY EXISTS_TAC [(← q r"FST((f:num->int#int) n)"), (← q r"SND((f:num->int#int) n)")] THEN REWRITE_TAC [PAIR] THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"n:num")) o (checkM (fun z1 => (do let z2 ← (do pure (Prod.snd (← (do let z3 ← (do let z4 ← (pure z1); pure (concl z4)); liftExcept (dest_forall z3))))); pure (is_conj z2)))))) THEN INT_ARITH_TAC])

  let PELL_EQUATION_INFINITE ← prove
    r"!d:int.
        &0 < d /\ ~(?m. d = m pow 2)
        ==> INFINITE {(x,y) | &0 < x /\ &0 < y /\
                              x pow 2 - d * y pow 2 = &1}"
    (REPEAT STRIP_TAC THEN MP_TAC (← SPEC (← q r"d:int") INT_SQUAREFREE_DECOMPOSITION) THEN ANTS_TAC THENL [ASM_INT_ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"d0:int"), (← q r"c:num")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"&0 < (&c:int) pow 2") ASSUME_TAC THENL [MATCH_MP_TAC INT_POW_LT THEN ASM_SIMP_TAC [INT_OF_NUM_LT, LE_1], ALL_TAC] THEN SUBGOAL_THEN (← q r"&0 < d0 /\ ~(d0:int = &1)") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [MP_TAC (← SPECL [(← q r"&0:int"), (← q r"d0:int"), (← q r"(&c:int) pow 2")] INT_LT_RMUL_EQ) THEN ASM_REWRITE_TAC [INT_MUL_LZERO] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o ((checkM (fun z5 => (do let z6 ← (do let z7 ← (pure z5); pure (concl z7)); pure (is_eq z6)))) o (checkM (fun th => (do let z4 ← (q r"d:int"); let z3 ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); liftExcept (lhs z1)); pure (z3 == z4))))))) THEN FIRST_ASSUM ACCEPT_TAC, DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~(?m:int. d = m pow 2)") THEN REWRITE_TAC [] THEN EXISTS_TAC (← q r"&c:int") THEN ASM_REWRITE_TAC [] THEN INT_ARITH_TAC], ALL_TAC] THEN MP_TAC (← SPEC (← q r"d0:int") QUADRATIC_FIELD_EXISTS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"k:(((1->num)->real)->bool) ring") (X_CHOOSE_THEN (← q r"w:((1->num)->real)->bool") STRIP_ASSUME_TAC)) THEN MP_TAC (← ISPECL [(← q r"k:(((1->num)->real)->bool) ring"), (← q r"w:((1->num)->real)->bool"), (← q r"d0:int"), (← q r"&c:int")] QUADRATIC_FIELD_PELL_SOLUTION) THEN ASM_REWRITE_TAC [INT_OF_NUM_EQ] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:int") (X_CHOOSE_THEN (← q r"b:int") STRIP_ASSUME_TAC)) THEN MATCH_MP_TAC PELL_SOLUTION_IMP_INFINITE THEN MAP_EVERY EXISTS_TAC [(← q r"a:int"), (← q r"b:int")] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC INT_LT_MUL THEN ASM_REWRITE_TAC [])

  let PELL_EQUATION_INFINITE_NUM ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"0 < d <=> ~(d = 0)")
    prove
      r"!d. ~(?m. d = m EXP 2) ==> INFINITE {(x,y) | x EXP 2 = d * y EXP 2 + 1}"
      (REPEAT STRIP_TAC THEN MP_TAC (← SPEC (← q r"&d:int") PELL_EQUATION_INFINITE) THEN ANTS_TAC THENL [CONJ_TAC THENL [REWRITE_TAC [INT_OF_NUM_LT, r1] THEN DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~(?m. 0 = m EXP 2)") THEN REWRITE_TAC [] THEN EXISTS_TAC (← q r"0") THEN ARITH_TAC, DISCH_THEN (X_CHOOSE_TAC (← q r"m:int")) THEN UNDISCH_TAC (← q r"~(?m. d = m EXP 2)") THEN REWRITE_TAC [] THEN EXISTS_TAC (← q r"num_of_int(abs m)") THEN REWRITE_TAC [(← GSYM INT_OF_NUM_EQ), (← GSYM INT_OF_NUM_POW)] THEN ASM_SIMP_TAC [INT_OF_NUM_OF_INT, INT_ABS_POS, INT_POW2_ABS]], ALL_TAC] THEN REWRITE_TAC [INFINITE, CONTRAPOS_THM] THEN DISCH_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"IMAGE (\z:num#num. (&(FST z):int,&(SND z):int))
                      {(x,y) | x EXP 2 = d * y EXP 2 + 1}") THEN ASM_SIMP_TAC [FINITE_IMAGE] THEN REWRITE_TAC [SUBSET, FORALL_PAIR_THM, IN_ELIM_PAIR_THM, IN_IMAGE, EXISTS_PAIR_THM, PAIR_EQ, FST, SND] THEN MAP_EVERY X_GEN_TAC [(← q r"x:int"), (← q r"y:int")] THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"num_of_int x"), (← q r"num_of_int y")] THEN ASM_SIMP_TAC [INT_OF_NUM_OF_INT, INT_LT_IMP_LE] THEN REWRITE_TAC [(← GSYM INT_OF_NUM_EQ), (← GSYM INT_OF_NUM_POW), (← GSYM INT_OF_NUM_ADD), (← GSYM INT_OF_NUM_MUL)] THEN ASM_SIMP_TAC [INT_OF_NUM_OF_INT, INT_LT_IMP_LE] THEN ASM_INT_ARITH_TAC)

  -- @@RETURN BEGIN
  return { QUADRATIC_FIELD_PELL_SOLUTION, PELL_SOLUTION_IMP_INFINITE,
           PELL_EQUATION_INFINITE, PELL_EQUATION_INFINITE_NUM }
  -- @@RETURN END

end HolANT.QuadraticUnits
