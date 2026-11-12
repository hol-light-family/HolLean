/- ========================================================================= -/
/- ANT: Places of number fields and of the rationals                       -/
/- ========================================================================= -/
/- File: HolANT/Places.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/places.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antplacesdiff; the rest is by hand.  Its `needs` closure is
  Library/products.ml, Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/isum.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/norm_index.ml, ANT/classgroup.ml, ANT/nf_valuation.ml, ANT/prime_split.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/relative_split.ml, Library/frag.ml, Library/grouptheory.ml, ANT/integrality.ml, Library/ring_groups.ml, ANT/fingen_group.ml, Multivariate/misc.ml, Multivariate/metric.ml, Multivariate/homology.ml, Multivariate/vectors.ml, Multivariate/determinants.ml, Multivariate/topology.ml, Multivariate/convex.ml, Multivariate/paths.ml, Multivariate/polytope.ml, Multivariate/degree.ml, Multivariate/derivatives.ml, Multivariate/integration.ml, Multivariate/measure.ml, Multivariate/complex_algebra.ml, Multivariate/complexes.ml, Multivariate/canal.ml, Multivariate/transcendentals.ml, Multivariate/realanalysis.ml, Multivariate/moretop.ml, Multivariate/cauchy.ml, Multivariate/complex_ring.ml, Multivariate/complex_field.ml, ANT/complex_embeddings.ml, ANT/power_basis.ml, ANT/infinite_places.ml, ANT/valuation_ring.ml, ANT/dedekind_absolute.ml, ANT/product_formula.ml, ANT/absolute_values.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.Places fills them).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left; where a proof applies rules that print or use
  counters (MESON, ARITH_RULE, ...) they are bound first, in OCaml's order.
-/

import HolANT.Prelude
import HolLibrary.Products
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
import HolANT.Algmisc
import HolANT.Integral
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolANT.IdealArith
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.IdealNorm
import HolANT.RingOfIntegers
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.NormIndex
import HolANT.Classgroup
import HolANT.NfValuation
import HolANT.PrimeSplit
import HolANT.Discriminant
import HolANT.TraceForm
import HolANT.RelativeSplit
import HolLibrary.Frag
import HolLibrary.GroupTheory
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
import HolANT.ValuationRing
import HolANT.DedekindAbsolute
import HolANT.ProductFormula
import HolANT.AbsoluteValues

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
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.NormIndex
open HolANT.Classgroup
open HolANT.NfValuation
open HolANT.PrimeSplit
open HolANT.Discriminant
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.Integrality
open HolANT.FingenGroup
open HolANT.ComplexEmbeddings
open HolANT.PowerBasis
open HolANT.InfinitePlaces
open HolANT.ValuationRing
open HolANT.DedekindAbsolute
open HolANT.ProductFormula
open HolANT.AbsoluteValues

namespace HolANT.Places

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ABSOLUTE_VALUE_0 ABSOLUTE_VALUE_1 ABSOLUTE_VALUE_DIV ABSOLUTE_VALUE_MUL
   ABSOLUTE_VALUE_NEG ABSOLUTE_VALUE_POS ABSOLUTE_VALUE_RING_OF_NUM_LE
   ABSOLUTE_VALUE_TRIANGLE ADD1 ADD_CLAUSES COMPLEX_EMBEDDINGS_ABSOLUTE_VALUE
   COMPLEX_EMBEDDINGS_HAS_SIZE COMPLEX_EMBEDDINGS_MONOMORPHISM COMPLEX_NORM_CX
   COMPLEX_RING_CLAUSES COMPLEX_RING_OF_INT CONJ_ASSOC CX_DIV CX_INJ
   DEDEKIND_NONARCHIMEDEAN_ABSOLUTE_VALUE DIVIDES_PRIME_PRIME DIVISION EQ_IMP
   EQ_TRANS EXISTS_INT_CASES EXISTS_UNIQUE_THM EXP EXP_1 EXP_ADD EXP_EQ_0
   EXP_LOG EXP_LT_0 EXP_MONO_LE EXTENSION FIELD_HOMOMORPHISM_DIV
   FIELD_NONTRIVIAL FIELD_REAL_RING FIELD_SUBFIELD_GENERATED FINITE_IMAGE_INJ_EQ
   FORALL_INT_CASES HAS_SIZE IDEAL_GENERATED_INC_GEN IDEAL_NORM_GT_1
   INTEGER_CLOSED IN_ELIM_THM IN_IMAGE IN_SING I_THM LEFT_IMP_EXISTS_THM LE_1
   LE_EXP LE_TRANS LOG_MONO_LE LOG_MONO_LE_IMP LOG_POS_LT LOG_POW LOG_RPOW
   LTE_TRANS LT_IMP_LE LT_POW2_REFL MONO_EXISTS MONO_IMP
   NONARCHIMEDEAN_ABSOLUTE_VALUE_BOUNDED NONARCHIMEDEAN_ABSOLUTE_VALUE_INTEGRAL
   NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_INT NONARCHIMEDEAN_IMP_ABSOLUTE_VALUE
   NOT_FORALL_THM NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS
   NUMBER_FIELD_IMP_FIELD NUMBER_FIELD_PRIME_SUBFIELD
   NUMBER_FIELD_PRODUCT_FORMULA NUMBER_FIELD_RATIONAL_FIELD PRIME_IMP_NZ
   PRIME_IMP_PROPER_IDEAL PRIME_IMP_RING_IDEAL PRIME_SUBFIELD_CHAR_0
   PRIME_SUBFIELD_SUBFIELD_GENERATED PRODUCT_CONST PRODUCT_EQ PRODUCT_IMAGE
   PROPER_IDEAL_ALT RDIV_LT_EQ : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (REAL_ABS_DIV REAL_ABS_NEG REAL_ABS_NUM REAL_DIV_RMUL REAL_LE_ANTISYM
   REAL_LE_LDIV_EQ REAL_LE_LMUL REAL_LE_MUL2 REAL_LE_RADD REAL_LE_RDIV_EQ
   REAL_LE_REFL REAL_LE_TRANS REAL_LT_DIV REAL_LT_IMP_LE REAL_LT_IMP_NZ
   REAL_LT_RDIV_EQ REAL_MUL_LID REAL_MUL_RID REAL_NOT_LE REAL_NOT_LT
   REAL_OF_NUM_ADD REAL_OF_NUM_EQ REAL_OF_NUM_LE REAL_OF_NUM_LT REAL_OF_NUM_POW
   REAL_OF_NUM_SUC REAL_POS REAL_POW_1 REAL_POW_DIV
   REAL_POW_EVENTUALLY_GT_LINEAR REAL_POW_LE REAL_POW_LE_1 REAL_POW_LT
   REAL_RING_CHAR REAL_RING_CLAUSES REAL_RING_DIV REAL_RING_OF_INT
   REAL_RING_OF_NUM REAL_ZPOW_RPOW RINGS_EQ RING_CHAR_SUBFIELD_GENERATED
   RING_HOMOMORPHISM_INTEGER_RING_OF_INT RING_HOMOMORPHISM_MUL
   RING_HOMOMORPHISM_RING_OF_INT RING_HOMOMORPHISM_SUBFIELD_INCLUSION
   RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_OF_INT RING_OF_INTEGERS
   RING_OF_INTEGERS_CARRIER RING_OF_INTEGERS_FINITE_QUOTIENT
   RING_OF_INTEGERS_FRACTION_FIELD RING_OF_INTEGERS_PRIME_SUBFIELD_PRIME_IDEAL
   RING_OF_INTEGERS_RATIONAL_FIELD RING_OF_INT_CASES RING_OF_INT_IN_PRIME_IDEAL
   RING_OF_INT_OF_NUM RING_OF_INT_SUBFIELD_GENERATED RING_OF_NUM RING_OF_NUM_1
   RING_OF_NUM_ADD RING_OF_NUM_MUL RING_OF_NUM_SUBFIELD_GENERATED RPOW_DIV
   RPOW_LE_1 RPOW_LT_1 RPOW_MONO_LE RPOW_MONO_LE_EQ RPOW_ONE RPOW_POS_LT
   RPOW_POW RPOW_RPOW RPOW_ZERO SUBFIELD_GENERATED int_eq int_neg_th
   int_of_num_th num_WOP num_divides o_DEF real_pow ring_of_num rpow : thm)
  deriving Inhabited

/-- What places.ml uses from Session besides theorems. -/
structure PlacesDeps where
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
  COMPLEX_FIELD : term → ExceptT String IO thm
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
/- places.ml phrases from line 89 to 667                                  -/
/- ---------------------------------------------------------------------- -/

structure Places01 where
  -- @@FIELDS
  NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_INTEGERS : thm
  NUMBER_FIELD_NONARCHIMEDEAN_ABSOLUTE_VALUE : thm
  NUMBER_FIELD_NONARCHIMEDEAN_ABSOLUTE_VALUE_EQUIVALENT : thm
  COMPLEX_EMBEDDINGS_ABSOLUTE_VALUE_ARCHIMEDEAN : thm
  OSTROWSKI_DIGITS_LEMMA : thm
  OSTROWSKI_BOUND_LEMMA : thm
  OSTROWSKI_NUM_LEMMA : thm
  PRIME_SUBFIELD_IDEAL_GENERATED_PRIME_EQ : thm
  OSTROWSKI_PRIME_SUBFIELD : thm
  OSTROWSKI : thm
  OSTROWSKI_RATIONAL : thm
  RATIONAL_FIELD_COMPLEX_EMBEDDINGS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupPlaces01 [HolBase] (D : PlacesDeps) :
    ExceptT String IO Places01 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC,
        COMPLEX_FIELD, INDUCT_TAC, MESON, REAL_ARITH, REAL_ARITH_TAC, TAUT, .. } := D
  let { ABSOLUTE_VALUE_0, ABSOLUTE_VALUE_1, ABSOLUTE_VALUE_DIV, ABSOLUTE_VALUE_MUL,
        ABSOLUTE_VALUE_NEG, ABSOLUTE_VALUE_POS, ABSOLUTE_VALUE_RING_OF_NUM_LE,
        ABSOLUTE_VALUE_TRIANGLE, ADD1, ADD_CLAUSES, COMPLEX_EMBEDDINGS_ABSOLUTE_VALUE,
        COMPLEX_EMBEDDINGS_HAS_SIZE, COMPLEX_EMBEDDINGS_MONOMORPHISM, COMPLEX_NORM_CX,
        COMPLEX_RING_CLAUSES, COMPLEX_RING_OF_INT, CX_DIV, CX_INJ,
        DEDEKIND_NONARCHIMEDEAN_ABSOLUTE_VALUE, DIVIDES_PRIME_PRIME, DIVISION, EQ_IMP,
        EXISTS_INT_CASES, EXISTS_UNIQUE_THM, EXP, EXP_1, EXP_ADD, EXP_EQ_0, EXP_LOG,
        EXP_LT_0, EXP_MONO_LE, EXTENSION, FIELD_HOMOMORPHISM_DIV, FIELD_NONTRIVIAL,
        FIELD_REAL_RING, FIELD_SUBFIELD_GENERATED, FORALL_INT_CASES,
        IDEAL_GENERATED_INC_GEN, IDEAL_NORM_GT_1, IN_ELIM_THM, IN_SING, I_THM,
        LEFT_IMP_EXISTS_THM, LE_1, LE_EXP, LE_TRANS, LOG_MONO_LE, LOG_MONO_LE_IMP,
        LOG_POS_LT, LOG_POW, LOG_RPOW, LTE_TRANS, LT_IMP_LE, LT_POW2_REFL, MONO_EXISTS,
        MONO_IMP, NONARCHIMEDEAN_ABSOLUTE_VALUE_BOUNDED,
        NONARCHIMEDEAN_ABSOLUTE_VALUE_INTEGRAL,
        NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_INT, NONARCHIMEDEAN_IMP_ABSOLUTE_VALUE,
        NOT_FORALL_THM, NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_PRIME_SUBFIELD,
        NUMBER_FIELD_RATIONAL_FIELD, PRIME_IMP_PROPER_IDEAL, PRIME_IMP_RING_IDEAL,
        PRIME_SUBFIELD_CHAR_0, PRIME_SUBFIELD_SUBFIELD_GENERATED, PROPER_IDEAL_ALT,
        RDIV_LT_EQ, .. } := D.core1
  let { REAL_ABS_DIV, REAL_ABS_NEG, REAL_ABS_NUM, REAL_DIV_RMUL, REAL_LE_ANTISYM,
        REAL_LE_LDIV_EQ, REAL_LE_LMUL, REAL_LE_MUL2, REAL_LE_RADD, REAL_LE_RDIV_EQ,
        REAL_LE_REFL, REAL_LE_TRANS, REAL_LT_DIV, REAL_LT_IMP_LE, REAL_LT_IMP_NZ,
        REAL_LT_RDIV_EQ, REAL_MUL_LID, REAL_MUL_RID, REAL_NOT_LE, REAL_NOT_LT,
        REAL_OF_NUM_ADD, REAL_OF_NUM_LE, REAL_OF_NUM_LT, REAL_OF_NUM_POW,
        REAL_OF_NUM_SUC, REAL_POS, REAL_POW_1, REAL_POW_DIV,
        REAL_POW_EVENTUALLY_GT_LINEAR, REAL_POW_LE, REAL_POW_LE_1, REAL_POW_LT,
        REAL_RING_CHAR, REAL_RING_CLAUSES, REAL_RING_DIV, REAL_RING_OF_INT,
        REAL_RING_OF_NUM, REAL_ZPOW_RPOW, RINGS_EQ, RING_CHAR_SUBFIELD_GENERATED,
        RING_HOMOMORPHISM_INTEGER_RING_OF_INT, RING_HOMOMORPHISM_MUL,
        RING_HOMOMORPHISM_RING_OF_INT, RING_HOMOMORPHISM_SUBFIELD_INCLUSION,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_OF_INT, RING_OF_INTEGERS,
        RING_OF_INTEGERS_CARRIER, RING_OF_INTEGERS_FINITE_QUOTIENT,
        RING_OF_INTEGERS_FRACTION_FIELD, RING_OF_INTEGERS_PRIME_SUBFIELD_PRIME_IDEAL,
        RING_OF_INT_CASES, RING_OF_INT_IN_PRIME_IDEAL, RING_OF_INT_OF_NUM,
        RING_OF_INT_SUBFIELD_GENERATED, RING_OF_NUM, RING_OF_NUM_1, RING_OF_NUM_ADD,
        RING_OF_NUM_MUL, RING_OF_NUM_SUBFIELD_GENERATED, RPOW_DIV, RPOW_LE_1,
        RPOW_LT_1, RPOW_MONO_LE, RPOW_MONO_LE_EQ, RPOW_ONE, RPOW_POS_LT, RPOW_POW,
        RPOW_RPOW, RPOW_ZERO, SUBFIELD_GENERATED, int_eq, int_neg_th, int_of_num_th,
        num_WOP, num_divides, real_pow, ring_of_num, rpow, .. } := D.core2
  -- @@SCOPE END

  let NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_INTEGERS ← prove
    r"!k (f:A->real) x.
        field k /\ nonarchimedean_absolute_value k f /\
        x IN ring_carrier(ring_of_integers k)
        ==> f x <= &1"
    (REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"k:A ring"), (← q r"ring_of_int k:int->A")] NONARCHIMEDEAN_ABSOLUTE_VALUE_INTEGRAL) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN ASM_SIMP_TAC [NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_INT])

  let NUMBER_FIELD_NONARCHIMEDEAN_ABSOLUTE_VALUE ← prove
    r"!k (f:A->real).
        number_field k /\ nonarchimedean_absolute_value k f /\
        (?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ ~(f x = &1))
        ==> ?!P. prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
                 ?c. &1 < c /\
                     !x. x IN ring_carrier k /\ ~(x = ring_0 k)
                         ==> f x = c zpow
                                   --(dedekind_valuation
                                       (ring_of_integers k,k) I P x)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_FRACTION_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"f:A->real")] DEDEKIND_NONARCHIMEDEAN_ABSOLUTE_VALUE) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS, I_THM] THEN ANTS_TAC THENL [ALL_TAC, SIMP_TAC []] THEN CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_INTEGERS THEN EXISTS_TAC (← q r"k:A ring") THEN ASM_SIMP_TAC [NUMBER_FIELD_IMP_FIELD])

  let NUMBER_FIELD_NONARCHIMEDEAN_ABSOLUTE_VALUE_EQUIVALENT ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"x:A"
    let q2 ← q r"N rpow s"
    let q3 ← q r"s:real"
    let q4 ← q r"&1 < (c:real) ==> &0 < c"
    let r5 ← REAL_ARITH q4
    let q6 ← q r"&1 < (N:real) ==> &0 < N"
    let r7 ← REAL_ARITH q6
    let q8 ← q r"&1 < (N:real) ==> &0 < N"
    let r9 ← REAL_ARITH q8
    let q10 ← q r"x:A"
    let q11 ← q r"log c / log N"
    let q12 ← q r"c:real"
    let q13 ← q r"(f:A->real)(ring_0 k) = &0"
    let q14 ← q r"N = &(ideal_norm (ring_of_integers k) (P:A->bool)):real"
    let q15 ← q r"(&1:real) < &(ideal_norm (ring_of_integers k) (P:A->bool))"
    let q16 ← q r"P:A->bool"
    let q17 ← q r"(!P:A->bool. Q1 P /\ Q2 P ==> (R P <=> S P))
    ==> (?!P. Q1 P /\ Q2 P /\ R P) ==> (?!P. Q1 P /\ Q2 P /\ S P)"
    let r18 ← MESON [] q17
    prove
      r"!k (f:A->real).
          number_field k /\ nonarchimedean_absolute_value k f /\
          (?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ ~(f x = &1))
          ==> ?!P. prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
                   ?s. &0 < s /\
                       !x. x IN ring_carrier k
                           ==> f x =
                               (if x = ring_0 k then &0
                                else &(ideal_norm (ring_of_integers k) P) zpow
                                     --(dedekind_valuation
                                         (ring_of_integers k,k) I P x))
                               rpow s"
      (REPEAT GEN_TAC THEN DISCH_THEN (fun th => tactic_of do pure (ASSUME_TAC th THEN ASSUME_TAC (← CONJUNCT1 th) THEN ASSUME_TAC (← CONJUNCT1 (← CONJUNCT2 th)))) THEN FIRST_ASSUM (MP_TAC o (MATCH_MP NUMBER_FIELD_NONARCHIMEDEAN_ABSOLUTE_VALUE)) THEN MATCH_MP_TAC r18 THEN X_GEN_TAC q16 THEN STRIP_TAC THEN SUBGOAL_THEN q15 ASSUME_TAC THENL [REWRITE_TAC [REAL_OF_NUM_LT] THEN MATCH_MP_TAC IDEAL_NORM_GT_1 THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN CONJ_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP PRIME_IMP_PROPER_IDEAL)) THEN SIMP_TAC [PROPER_IDEAL_ALT], MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL]], ALL_TAC] THEN ABBREV_TAC q14 THEN SUBGOAL_THEN q13 ASSUME_TAC THENL [ASM_MESON_TAC [ABSOLUTE_VALUE_0, NONARCHIMEDEAN_IMP_ABSOLUTE_VALUE], ALL_TAC] THEN EQ_TAC THENL [DISCH_THEN (X_CHOOSE_THEN q12 STRIP_ASSUME_TAC) THEN EXISTS_TAC q11 THEN ASM_SIMP_TAC [REAL_LT_DIV, LOG_POS_LT] THEN X_GEN_TAC q10 THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [RPOW_ZERO, REAL_LT_IMP_NZ, REAL_LT_DIV, LOG_POS_LT] THEN ASM_SIMP_TAC [REAL_ZPOW_RPOW, r9] THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC [rpow, r7] THEN ASM_SIMP_TAC [REAL_DIV_RMUL, REAL_LT_IMP_NZ, LOG_POS_LT, EXP_LOG, r5], DISCH_THEN (X_CHOOSE_THEN q3 STRIP_ASSUME_TAC) THEN EXISTS_TAC q2 THEN ASM_SIMP_TAC [RPOW_LT_1] THEN X_GEN_TAC q1 THEN STRIP_TAC THEN ASM_SIMP_TAC [] THEN MATCH_MP_TAC REAL_ZPOW_RPOW THEN ASM_REAL_ARITH_TAC])

  let COMPLEX_EMBEDDINGS_ABSOLUTE_VALUE_ARCHIMEDEAN ← prove
    r"!k (g:A->complex).
        field k /\ g IN complex_embeddings k
        ==> ~nonarchimedean_absolute_value k (\x. norm(g x))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"\x. norm((g:A->complex) x)")] NONARCHIMEDEAN_ABSOLUTE_VALUE_BOUNDED) THEN ASM_SIMP_TAC [COMPLEX_EMBEDDINGS_ABSOLUTE_VALUE] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"&2:int")) o CONJUNCT1)) THEN SUBGOAL_THEN (← q r"ring_homomorphism(k,complex_ring) (g:A->complex)") ASSUME_TAC THENL [ASM_MESON_TAC [COMPLEX_EMBEDDINGS_MONOMORPHISM, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_RING_OF_INT th)])) THEN REWRITE_TAC [COMPLEX_RING_OF_INT, COMPLEX_NORM_CX, int_of_num_th] THEN REAL_ARITH_TAC)

  let OSTROWSKI_DIGITS_LEMMA ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"2 <= b ==> ~(b = 0)")
    prove
      r"!(g:num->real) b.
           (!m n. g(m * n) = g m * g n) /\ (!m n. g(m + n) <= g m + g n) /\
           (!n. &0 <= g n) /\ (!n. g n <= &n) /\ 2 <= b
           ==> !d N. N < b EXP (d + 1)
                     ==> g N <= &b * &(d + 1) * max (&1) (g b) pow d"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"&1 <= max (&1) ((g:num->real) b) /\ g b <= max (&1) (g b)") STRIP_ASSUME_TAC THENL [REAL_ARITH_TAC, ALL_TAC] THEN ABBREV_TAC (← q r"M = max (&1) ((g:num->real) b)") THEN INDUCT_TAC THENL [REWRITE_TAC [ADD_CLAUSES, EXP_1, real_pow, REAL_MUL_RID] THEN X_GEN_TAC (← q r"N:num") THEN DISCH_TAC THEN TRANS_TAC REAL_LE_TRANS (← q r"&N:real") THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [REAL_OF_NUM_LE, LT_IMP_LE], ALL_TAC] THEN X_GEN_TAC (← q r"N:num") THEN DISCH_TAC THEN MP_TAC (← SPECL [(← q r"N:num"), (← q r"b:num")] DIVISION) THEN ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN DISCH_THEN (CONJUNCTS_THEN2 (fun th => ONCE_REWRITE_TAC [th]) ASSUME_TAC) THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"N DIV b"))) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RDIV_LT_EQ, r1] THEN UNDISCH_TAC (← q r"N < b EXP (SUC d + 1)") THEN REWRITE_TAC [ADD1, EXP_ADD, EXP_1] THEN ARITH_TAC, DISCH_TAC] THEN TRANS_TAC REAL_LE_TRANS (← q r"(g:num->real)(N DIV b) * g b + g(N MOD b)") THEN CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(g:num->real)(N MOD b) <= &b") ASSUME_TAC THENL [TRANS_TAC REAL_LE_TRANS (← q r"&(N MOD b):real") THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [REAL_OF_NUM_LE, LT_IMP_LE], ALL_TAC] THEN SUBGOAL_THEN (← q r"(g:num->real)(N DIV b) * g b <= (&b * &(d + 1) * M pow d) * M") ASSUME_TAC THENL [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"&1 <= (M:real) * M pow d") ASSUME_TAC THENL [REWRITE_TAC [(← GSYM (← CONJUNCT2 real_pow))] THEN MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"&b <= &b * (M:real) * M pow d") ASSUME_TAC THENL [GEN_REWRITE_TAC LAND_CONV [(← GSYM REAL_MUL_RID)] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC [REAL_POS], ALL_TAC] THEN REWRITE_TAC [real_pow, (← GSYM REAL_OF_NUM_ADD), (← GSYM REAL_OF_NUM_SUC)] THEN RULE_ASSUM_TAC (REWRITE_RULE [(← GSYM REAL_OF_NUM_ADD)]) THEN ASM_REAL_ARITH_TAC)

  let OSTROWSKI_BOUND_LEMMA ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"&1 <= (R:real) ==> &0 < R")
    let r2 ← REAL_ARITH (← q r"&1 <= (M:real) ==> &0 <= M")
    let r3 ← REAL_ARITH (← q r"&1 <= (M:real) ==> &0 <= M")
    let r4 ← ARITH_RULE (← q r"2 <= n ==> 0 < n")
    let r5 ← ARITH_RULE (← q r"2 <= n ==> 0 < n")
    let r6 ← REAL_ARITH (← q r"&k * x / y = (&k * x) / y")
    let r7 ← ARITH_RULE (← q r"~(d = 0) ==> d - 1 < d /\ d - 1 + 1 = d")
    let r8 ← ARITH_RULE (← q r"1 <= n <=> ~(n = 0)")
    let r9 ← ARITH_RULE (← q r"N <= N + 1")
    let r10 ← REAL_ARITH (← q r"&1 <= (R:real) ==> &0 < R")
    prove
      r"!g. (!m n. g(m * n) = g m * g n) /\ (!m n. g(m + n) <= g m + g n) /\
         (!n. &0 <= g n) /\ g 1 = &1 /\ (!n. g n <= &n)
         ==> !m b. 2 <= m /\ 2 <= b
                   ==> g m <= max (&1) (g b) rpow (log(&m) / log(&b))"
      (GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [(← q r"m:num"), (← q r"b:num")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!n k. (g:num->real)(n EXP k) = g n pow k") ASSUME_TAC THENL [GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [EXP, real_pow], ALL_TAC] THEN ABBREV_TAC (← q r"M = max (&1) ((g:num->real) b)") THEN SUBGOAL_THEN (← q r"&1 <= (M:real)") ASSUME_TAC THENL [EXPAND_TAC "M" THEN REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"&0 < log(&m) /\ &0 < log(&b)") STRIP_ASSUME_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC [REAL_OF_NUM_LT] THEN ASM_ARITH_TAC, ALL_TAC] THEN ABBREV_TAC (← q r"L = log(&m) / log(&b)") THEN SUBGOAL_THEN (← q r"&0 < (L:real)") ASSUME_TAC THENL [EXPAND_TAC "L" THEN ASM_SIMP_TAC [REAL_LT_DIV], ALL_TAC] THEN ABBREV_TAC (← q r"R = M rpow L") THEN SUBGOAL_THEN (← q r"&1 <= (R:real)") ASSUME_TAC THENL [EXPAND_TAC "R" THEN MATCH_MP_TAC RPOW_LE_1 THEN ASM_SIMP_TAC [REAL_LT_IMP_LE], ALL_TAC] THEN REWRITE_TAC [(← GSYM REAL_NOT_LT)] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"(g:num->real) m / R"), (← q r"&b * (L:real)"), (← q r"&b:real")] REAL_POW_EVENTUALLY_GT_LINEAR) THEN ASM_SIMP_TAC [REAL_LT_RDIV_EQ, r10, REAL_MUL_LID] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"N:num") (MP_TAC o (SPEC (← q r"N + 1")))) THEN REWRITE_TAC [r9, REAL_NOT_LT] THEN ABBREV_TAC (← q r"k = N + 1") THEN SUBGOAL_THEN (← q r"1 <= k") ASSUME_TAC THENL [EXPAND_TAC "k" THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"?d. m EXP k < b EXP (d + 1) /\ (!e. e < d ==> ~(m EXP k < b EXP (e + 1)))") (X_CHOOSE_THEN (← q r"d:num") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "min"))) THENL [GEN_REWRITE_TAC id [(← GSYM (← REWRITE_RULE [] (← ISPEC (← q r"\d. m EXP k < b EXP (d + 1)") num_WOP)))] THEN EXISTS_TAC (← q r"m EXP k") THEN TRANS_TAC LTE_TRANS (← q r"2 EXP (m EXP k)") THEN REWRITE_TAC [LT_POW2_REFL] THEN TRANS_TAC LE_TRANS (← q r"b EXP (m EXP k)") THEN ASM_REWRITE_TAC [EXP_MONO_LE, LE_EXP] THEN ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"b EXP d <= m EXP k") ASSUME_TAC THENL [ASM_CASES_TAC (← q r"d = 0") THENL [ASM_REWRITE_TAC [EXP, r8, EXP_EQ_0] THEN ASM_ARITH_TAC, REMOVE_THEN "min" (MP_TAC o (SPEC (← q r"d - 1"))) THEN ASM_SIMP_TAC [r7] THEN ARITH_TAC], ALL_TAC] THEN SUBGOAL_THEN (← q r"&d <= &k * (L:real)") ASSUME_TAC THENL [EXPAND_TAC "L" THEN ASM_SIMP_TAC [r6, REAL_LE_RDIV_EQ] THEN ASM_SIMP_TAC [(← GSYM LOG_POW), REAL_OF_NUM_LT, LE_1, r5] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_SIMP_TAC [REAL_POW_LT, REAL_OF_NUM_LT, REAL_OF_NUM_POW, REAL_OF_NUM_LE, r4] THEN REWRITE_TAC [EXP_LT_0] THEN ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"(g:num->real) m pow k <= &b * (&k * L + &1) * R pow k") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"(g:num->real) m pow k = g(m EXP k)") SUBST1_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN TRANS_TAC REAL_LE_TRANS (← q r"&b * &(d + 1) * (M:real) pow d") THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"g:num->real"), (← q r"b:num")] OSTROWSKI_DIGITS_LEMMA) THEN ASM_SIMP_TAC [], ALL_TAC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [REAL_POS] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC [REAL_POS] THEN REPEAT CONJ_TAC THENL [REWRITE_TAC [(← GSYM REAL_OF_NUM_ADD)] THEN ASM_REAL_ARITH_TAC, ASM_SIMP_TAC [REAL_POW_LE, r3], EXPAND_TAC "R" THEN ASM_SIMP_TAC [(← GSYM RPOW_POW), RPOW_RPOW, r2] THEN MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC], ALL_TAC] THEN REWRITE_TAC [REAL_POW_DIV] THEN ASM_SIMP_TAC [REAL_LE_LDIV_EQ, REAL_POW_LT, r1] THEN UNDISCH_TAC (← q r"(g:num->real) m pow k <= &b * (&k * L + &1) * R pow k") THEN REAL_ARITH_TAC)

  let OSTROWSKI_NUM_LEMMA ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"&1 < (x:real) ==> &0 < x")
    let r2 ← ARITH_RULE (← q r"2 <= m ==> 0 < m")
    let r3 ← REAL_ARITH (← q r"(x / y) * (z:real) = (z * x) / y")
    let r4 ← REAL_ARITH (← q r"&1 < (x:real) ==> &0 < x")
    let r5 ← REAL_ARITH (← q r"&1 < (x:real) ==> max (&1) x = x")
    let r6 ← ARITH_RULE (← q r"~(n = 0) /\ ~(n = 1) ==> 2 <= n")
    prove
      r"!g. g 0 = &0 /\ g 1 = &1 /\ (!n. &0 <= g n) /\
         (!m n. g(m * n) = g m * g n) /\ (!m n. g(m + n) <= g m + g n) /\
         (?n. &1 < g n)
         ==> ?s. &0 < s /\ !n. g n = &n rpow s"
      (GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC (← q r"n0:num"))))))) THEN SUBGOAL_THEN (← q r"!n. (g:num->real) n <= &n") ASSUME_TAC THENL [INDUCT_TAC THEN ASM_REWRITE_TAC [REAL_LE_REFL] THEN REWRITE_TAC [ADD1, (← GSYM REAL_OF_NUM_ADD)] THEN TRANS_TAC REAL_LE_TRANS (← q r"(g:num->real) n + g 1") THEN CONJ_TAC THENL [ASM_MESON_TAC [], ASM_REWRITE_TAC [REAL_LE_RADD]], ALL_TAC] THEN MP_TAC (← ISPEC (← q r"g:num->real") OSTROWSKI_BOUND_LEMMA) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (LABEL_TAC "bd") THEN SUBGOAL_THEN (← q r"2 <= n0") ASSUME_TAC THENL [MATCH_MP_TAC r6 THEN CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"!m. 2 <= m ==> &1 < (g:num->real) m") ASSUME_TAC THENL [X_GEN_TAC (← q r"m:num") THEN DISCH_TAC THEN REWRITE_TAC [(← GSYM REAL_NOT_LE)] THEN DISCH_TAC THEN USE_THEN "bd" (MP_TAC o (SPECL [(← q r"n0:num"), (← q r"m:num")])) THEN ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"max (&1) ((g:num->real) m) = &1") SUBST1_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [RPOW_ONE] THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"!m b. 2 <= m /\ 2 <= b
            ==> log((g:num->real) m) / log(&m) <= log(g b) / log(&b)") ASSUME_TAC THENL [MAP_EVERY X_GEN_TAC [(← q r"m:num"), (← q r"b:num")] THEN STRIP_TAC THEN USE_THEN "bd" (MP_TAC o (SPECL [(← q r"m:num"), (← q r"b:num")])) THEN ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"max (&1) ((g:num->real) b) = g b") SUBST1_TAC THENL [MATCH_MP_TAC r5 THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"&0 < log(&m) /\ &0 < log(&b) /\ &1 < (g:num->real) m /\ &1 < g b") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [] THEN CONJ_TAC THEN MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC [REAL_OF_NUM_LT] THEN ASM_ARITH_TAC, ALL_TAC] THEN ASM_SIMP_TAC [(← GSYM LOG_MONO_LE), RPOW_POS_LT, r4, LOG_RPOW] THEN ASM_SIMP_TAC [REAL_LE_LDIV_EQ, r3, REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"&1 < (g:num->real) 2") ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"&0 < log((g:num->real) 2) / log(&2)") ASSUME_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THEN MATCH_MP_TAC LOG_POS_LT THEN ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC, ALL_TAC] THEN EXISTS_TAC (← q r"log((g:num->real) 2) / log(&2)") THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"m:num") THEN ASM_CASES_TAC (← q r"m = 0") THENL [ASM_SIMP_TAC [RPOW_ZERO, REAL_LT_IMP_NZ], ALL_TAC] THEN ASM_CASES_TAC (← q r"m = 1") THENL [ASM_REWRITE_TAC [RPOW_ONE], ALL_TAC] THEN SUBGOAL_THEN (← q r"2 <= m") ASSUME_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"&0 < log(&m) /\ &0 < log(&2) /\ &1 < (g:num->real) m") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [] THEN CONJ_TAC THEN MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC [REAL_OF_NUM_LT] THEN ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"log((g:num->real) m) / log(&m) = log(g 2) / log(&2)") MP_TAC THENL [REWRITE_TAC [(← GSYM REAL_LE_ANTISYM)] THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN ASM_SIMP_TAC [rpow, REAL_OF_NUM_LT, r2] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [REAL_DIV_RMUL, REAL_LT_IMP_NZ, EXP_LOG, r1])

  let PRIME_SUBFIELD_IDEAL_GENERATED_PRIME_EQ ← prove
    r"!k:A ring p q.
        field k /\ ring_char k = 0 /\ prime p /\ prime q
        ==> (ideal_generated
              (ring_of_integers(subfield_generated k {ring_0 k}))
              {ring_of_num k p} =
             ideal_generated
              (ring_of_integers(subfield_generated k {ring_0 k}))
              {ring_of_num k q} <=>
             p = q)"
    (REPEAT STRIP_TAC THEN EQ_TAC THENL [ALL_TAC, SIMP_TAC []] THEN ABBREV_TAC (← q r"O = ring_of_integers(subfield_generated k {ring_0 k:A})") THEN DISCH_THEN (LABEL_TAC "eq") THEN SUBGOAL_THEN (← q r"ring_of_num O = ring_of_num (k:A ring) /\
                ring_of_int O = ring_of_int (k:A ring)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "O" THEN REWRITE_TAC [RING_OF_INTEGERS, RING_OF_NUM_SUBFIELD_GENERATED, RING_OF_INT_SUBFIELD_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"prime_ideal O (ideal_generated O {ring_of_num k q:A})") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ideal_generated O {ring_of_num k q:A}")] RING_OF_INTEGERS_PRIME_SUBFIELD_PRIME_IDEAL) THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!n. ring_of_num k n IN ideal_generated O {ring_of_num k n:A}") ASSUME_TAC THENL [GEN_TAC THEN MATCH_MP_TAC IDEAL_GENERATED_INC_GEN THEN REWRITE_TAC [IN_SING] THEN ASM_MESON_TAC [RING_OF_NUM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"O:A ring"), (← q r"ideal_generated O {ring_of_num k q:A}"), (← q r"q:num")] RING_OF_INT_IN_PRIME_IDEAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"&p:int"))) THEN REWRITE_TAC [RING_OF_INT_OF_NUM] THEN REMOVE_THEN "eq" (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC [(← GSYM num_divides)] THEN ASM_MESON_TAC [DIVIDES_PRIME_PRIME])

  let OSTROWSKI_PRIME_SUBFIELD ← prove
    r"!k (f:A->real).
        field k /\ ring_char k = 0 /\
        absolute_value (subfield_generated k {ring_0 k}) f /\
        (?x. x IN ring_carrier(subfield_generated k {ring_0 k}) /\
             ~(x = ring_0 k) /\ ~(f x = &1))
        ==> (~nonarchimedean_absolute_value (subfield_generated k {ring_0 k}) f
             ==> ?s. &0 < s /\ s <= &1 /\
                     !n. f(ring_of_num k n) = &n rpow s) /\
            (nonarchimedean_absolute_value (subfield_generated k {ring_0 k}) f
             ==> ?!p. prime p /\
                      ?c. &1 < c /\
                          !x. x IN
                              ring_carrier(subfield_generated k {ring_0 k}) /\
                              ~(x = ring_0 k)
                              ==> f x =
                                  c zpow
                                  --(dedekind_valuation
                                      (ring_of_integers
                                        (subfield_generated k {ring_0 k}),
                                       subfield_generated k {ring_0 k}) I
                                      (ideal_generated
                                        (ring_of_integers
                                          (subfield_generated k {ring_0 k}))
                                        {ring_of_num k p}) x))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN ABBREV_TAC (← q r"Q = subfield_generated k {ring_0 k:A}") THEN SUBGOAL_THEN (← q r"ring_0 Q:A = ring_0 k /\ ring_1 Q = ring_1 k /\
    ring_neg Q = ring_neg k /\ ring_add Q = ring_add k /\
    ring_mul Q = ring_mul k /\ ring_of_num Q = ring_of_num k /\
    ring_of_int Q = ring_of_int k") STRIP_ASSUME_TAC THENL [EXPAND_TAC "Q" THEN REWRITE_TAC [SUBFIELD_GENERATED, RING_OF_NUM_SUBFIELD_GENERATED, RING_OF_INT_SUBFIELD_GENERATED], ALL_TAC] THEN CONJ_TAC THENL [DISCH_TAC THEN SUBGOAL_THEN (← q r"!n. ring_of_num k n:A IN ring_carrier Q") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_NUM], ALL_TAC] THEN MP_TAC (← ISPEC (← q r"\n. (f:A->real)(ring_of_num k n)") OSTROWSKI_NUM_LEMMA) THEN REWRITE_TAC [] THEN ANTS_TAC THENL [ALL_TAC, MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"s:real") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"Q:A ring"), (← q r"f:A->real"), (← q r"2")] ABSOLUTE_VALUE_RING_OF_NUM_LE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"s:real"), (← q r"(&1:real)"), (← q r"(&2:real)")] RPOW_MONO_LE_EQ) THEN REWRITE_TAC [RPOW_POW, REAL_POW_1] THEN ASM_REAL_ARITH_TAC] THEN REPEAT CONJ_TAC THENL [REWRITE_TAC [ring_of_num] THEN ASM_MESON_TAC [ABSOLUTE_VALUE_0], REWRITE_TAC [RING_OF_NUM_1] THEN ASM_MESON_TAC [ABSOLUTE_VALUE_1, FIELD_NONTRIVIAL], ASM_MESON_TAC [ABSOLUTE_VALUE_POS], REWRITE_TAC [RING_OF_NUM_MUL] THEN ASM_MESON_TAC [ABSOLUTE_VALUE_MUL], REWRITE_TAC [RING_OF_NUM_ADD] THEN ASM_MESON_TAC [ABSOLUTE_VALUE_TRIANGLE], ALL_TAC] THEN UNDISCH_TAC (← q r"~nonarchimedean_absolute_value Q (f:A->real)") THEN MP_TAC (← ISPECL [(← q r"Q:A ring"), (← q r"f:A->real")] NONARCHIMEDEAN_ABSOLUTE_VALUE_BOUNDED) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o CONJUNCT1) THEN REWRITE_TAC [NOT_FORALL_THM, REAL_NOT_LE, FORALL_INT_CASES, EXISTS_INT_CASES] THEN REWRITE_TAC [RING_OF_INT_CASES] THEN ASM_MESON_TAC [ABSOLUTE_VALUE_NEG], DISCH_TAC] THEN SUBGOAL_THEN (← q r"number_field(Q:A ring)") ASSUME_TAC THENL [EXPAND_TAC "Q" THEN ASM_SIMP_TAC [NUMBER_FIELD_PRIME_SUBFIELD], ALL_TAC] THEN SUBGOAL_THEN (← q r"!P. prime_ideal (ring_of_integers Q) P /\ ~(P = {ring_0 k}) <=>
        ?p. prime p /\
            P = ideal_generated (ring_of_integers Q) {ring_of_num k p:A}") ASSUME_TAC THENL [EXPAND_TAC "Q" THEN ASM_SIMP_TAC [RING_OF_INTEGERS_PRIME_SUBFIELD_PRIME_IDEAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"!p q. prime p /\ prime q /\
          ideal_generated (ring_of_integers Q) {ring_of_num k p} =
          ideal_generated (ring_of_integers Q) {ring_of_num k q:A}
          ==> p = q") (LABEL_TAC "inj") THENL [EXPAND_TAC "Q" THEN ASM_MESON_TAC [PRIME_SUBFIELD_IDEAL_GENERATED_PRIME_EQ], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"Q:A ring"), (← q r"f:A->real")] NUMBER_FIELD_NONARCHIMEDEAN_ABSOLUTE_VALUE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN REWRITE_TAC [EXISTS_UNIQUE_THM, (← ASSUME (← q r"ring_0 Q:A = ring_0 k"))] THEN DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"P:A->bool") STRIP_ASSUME_TAC) (LABEL_TAC "un")) THEN CONJ_TAC THENL [SUBGOAL_THEN (← q r"?p. prime p /\
          P = ideal_generated (ring_of_integers Q) {ring_of_num k p:A}") MP_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"p:num") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"p:num") THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (SUBST_ALL_TAC o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_eq z1)) then (do let z6 ← (q r"P:A->bool"); let z5 ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); liftExcept (lhs z3)); pure (z5 == z6)) else pure false)))) THEN ASM_MESON_TAC [], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"p:num"), (← q r"q:num")] THEN STRIP_TAC THEN REMOVE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN REMOVE_THEN "un" MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [])

  let OSTROWSKI ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"(p ==> r) ==> p /\ q ==> r /\ q")
    prove
      r"!k (f:A->real).
          field k /\ ring_char k = 0 /\
          ring_carrier(subfield_generated k {ring_0 k}) = ring_carrier k /\
          absolute_value k f /\
          (?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ ~(f x = &1))
          ==> (~nonarchimedean_absolute_value k f
               ==> ?s. &0 < s /\ s <= &1 /\
                       !g x. ring_homomorphism(k,real_ring) g /\
                             x IN ring_carrier k
                             ==> f x = abs(g x) rpow s) /\
              (nonarchimedean_absolute_value k f
               ==> ?!p. prime p /\
                        ?c. &1 < c /\
                            !x. x IN ring_carrier k /\ ~(x = ring_0 k)
                                ==> f x =
                                    c zpow
                                    --(dedekind_valuation
                                        (ring_of_integers k,k) I
                                        (ideal_generated (ring_of_integers k)
                                          {ring_of_num k p}) x))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"subfield_generated k {ring_0 k} = (k:A ring)") ASSUME_TAC THENL [ASM_REWRITE_TAC [RINGS_EQ, (← CONJUNCT2 SUBFIELD_GENERATED)], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"f:A->real")] OSTROWSKI_PRIME_SUBFIELD) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN MATCH_MP_TAC r1 THEN MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"s:real") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MAP_EVERY X_GEN_TAC [(← q r"g:A->real"), (← q r"y:A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!a. (f:A->real)(ring_of_int k a) = abs(real_of_int a) rpow s") ASSUME_TAC THENL [REWRITE_TAC [FORALL_INT_CASES, RING_OF_INT_CASES, int_of_num_th, int_neg_th, REAL_ABS_NEG, REAL_ABS_NUM] THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_NEG, RING_OF_NUM], ALL_TAC] THEN MP_TAC (← ISPEC (← q r"k:A ring") PRIME_SUBFIELD_CHAR_0) THEN ASM_REWRITE_TAC [EXTENSION] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"y:A"))) THEN ASM_REWRITE_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:int"), (← q r"b:int")] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"real_ring"), (← q r"g:A->real")] FIELD_HOMOMORPHISM_DIV) THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_DIV, RING_OF_INT, REAL_RING_DIV] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_RING_OF_INT th)])) THEN REWRITE_TAC [REAL_RING_OF_INT, REAL_ABS_DIV, RPOW_DIV])

  let OSTROWSKI_RATIONAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"(p ==> r) ==> p /\ q ==> r /\ q")
    prove
      r"!f. absolute_value (subfield_generated real_ring {&0}) f /\
         (?x. x IN ring_carrier(subfield_generated real_ring {&0}) /\
              ~(x = &0) /\ ~(f x = &1))
         ==> (~nonarchimedean_absolute_value (subfield_generated real_ring {&0}) f
              ==> ?s. &0 < s /\ s <= &1 /\
                      !x. x IN ring_carrier(subfield_generated real_ring {&0})
                          ==> f x = abs x rpow s) /\
             (nonarchimedean_absolute_value (subfield_generated real_ring {&0}) f
              ==> ?!p. prime p /\
                       ?c. &1 < c /\
                           !x. x IN ring_carrier
                                     (subfield_generated real_ring {&0}) /\
                               ~(x = &0)
                               ==> f x =
                                   c zpow
                                   --(dedekind_valuation
                                       (ring_of_integers
                                         (subfield_generated real_ring {&0}),
                                        subfield_generated real_ring {&0}) I
                                       (ideal_generated
                                         (ring_of_integers
                                           (subfield_generated real_ring {&0}))
                                         {&p}) x))"
      (GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"subfield_generated real_ring {&0}"), (← q r"f:real->real")] OSTROWSKI) THEN REWRITE_TAC [PRIME_SUBFIELD_SUBFIELD_GENERATED] THEN REWRITE_TAC [RING_CHAR_SUBFIELD_GENERATED, (← CONJUNCT2 SUBFIELD_GENERATED), RING_OF_NUM_SUBFIELD_GENERATED, REAL_RING_CLAUSES, REAL_RING_CHAR, REAL_RING_OF_NUM] THEN SIMP_TAC [FIELD_SUBFIELD_GENERATED, FIELD_REAL_RING] THEN ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN MATCH_MP_TAC r1 THEN MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"s:real") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"y:real") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPECL [(← q r"I:real->real"), (← q r"y:real")])) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION, I_THM])

  let RATIONAL_FIELD_COMPLEX_EMBEDDINGS ← prove
    r"complex_embeddings(subfield_generated real_ring {&0}) HAS_SIZE 1 /\
   !g x. g IN complex_embeddings(subfield_generated real_ring {&0}) /\
         x IN ring_carrier(subfield_generated real_ring {&0})
         ==> g x = Cx x"
    (ABBREV_TAC (← q r"Q = subfield_generated real_ring {&0}") THEN SUBGOAL_THEN (← q r"number_field (Q:real ring) /\ field Q") STRIP_ASSUME_TAC THENL [EXPAND_TAC "Q" THEN SIMP_TAC [NUMBER_FIELD_RATIONAL_FIELD, FIELD_SUBFIELD_GENERATED, FIELD_REAL_RING], ALL_TAC] THEN CONJ_TAC THENL [MP_TAC (← ISPEC (← q r"Q:real ring") COMPLEX_EMBEDDINGS_HAS_SIZE) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN EXPAND_TAC "Q" THEN REWRITE_TAC [PRIME_SUBFIELD_SUBFIELD_GENERATED, REAL_RING_CLAUSES] THEN MP_TAC (← ISPEC (← q r"real_ring") NUMBER_FIELD_PRIME_SUBFIELD) THEN REWRITE_TAC [FIELD_REAL_RING, REAL_RING_CHAR, REAL_RING_CLAUSES] THEN SIMP_TAC [], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"g:real->complex"), (← q r"x:real")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_homomorphism(Q,complex_ring) (g:real->complex)") ASSUME_TAC THENL [ASM_MESON_TAC [COMPLEX_EMBEDDINGS_MONOMORPHISM, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_carrier Q = {real_of_int a / real_of_int b | a,b | ~(b = &0)} /\
    ring_mul Q = ( * ) /\ ring_of_int Q = real_of_int") STRIP_ASSUME_TAC THENL [EXPAND_TAC "Q" THEN MP_TAC (← ISPEC (← q r"real_ring") PRIME_SUBFIELD_CHAR_0) THEN REWRITE_TAC [FIELD_REAL_RING, REAL_RING_CHAR, REAL_RING_CLAUSES, REAL_RING_OF_INT, REAL_RING_DIV] THEN SIMP_TAC [SUBFIELD_GENERATED, RING_OF_INT_SUBFIELD_GENERATED, REAL_RING_CLAUSES, REAL_RING_OF_INT], ALL_TAC] THEN UNDISCH_TAC (← q r"(x:real) IN ring_carrier Q") THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:int") (X_CHOOSE_THEN (← q r"b:int") STRIP_ASSUME_TAC)) THEN SUBGOAL_THEN (← q r"~(real_of_int b = &0)") ASSUME_TAC THENL [UNDISCH_TAC (← q r"~(b:int = &0)") THEN REWRITE_TAC [int_eq, int_of_num_th], ALL_TAC] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP RING_HOMOMORPHISM_RING_OF_INT)) THEN ASM_REWRITE_TAC [COMPLEX_RING_OF_INT] THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o ((SPECL [(← q r"x:real"), (← q r"real_of_int b")]) o (MATCH_MP RING_HOMOMORPHISM_MUL))) THEN ANTS_TAC THENL [CONJ_TAC THENL [ASM_REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [], ASM_MESON_TAC [RING_OF_INT]], ALL_TAC] THEN ASM_SIMP_TAC [REAL_DIV_RMUL, COMPLEX_RING_CLAUSES] THEN ASM_REWRITE_TAC [CX_DIV] THEN SUBGOAL_THEN (← q r"~(Cx(real_of_int b) = Cx(&0))") MP_TAC THENL [ASM_REWRITE_TAC [CX_INJ], ALL_TAC] THEN CONV_TAC COMPLEX_FIELD)

  -- @@RETURN BEGIN
  return { NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_INTEGERS,
           NUMBER_FIELD_NONARCHIMEDEAN_ABSOLUTE_VALUE,
           NUMBER_FIELD_NONARCHIMEDEAN_ABSOLUTE_VALUE_EQUIVALENT,
           COMPLEX_EMBEDDINGS_ABSOLUTE_VALUE_ARCHIMEDEAN, OSTROWSKI_DIGITS_LEMMA,
           OSTROWSKI_BOUND_LEMMA, OSTROWSKI_NUM_LEMMA,
           PRIME_SUBFIELD_IDEAL_GENERATED_PRIME_EQ, OSTROWSKI_PRIME_SUBFIELD, OSTROWSKI,
           OSTROWSKI_RATIONAL, RATIONAL_FIELD_COMPLEX_EMBEDDINGS }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- places.ml phrases from line 726 to 726                                 -/
/- ---------------------------------------------------------------------- -/

structure Places02 where
  -- @@FIELDS
  RATIONAL_PRODUCT_FORMULA : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupPlaces02 [HolBase] (D : PlacesDeps) (BPlaces01 : Places01) :
    ExceptT String IO Places02 := do
  -- @@SCOPE BEGIN
  let { COMPLEX_NORM_CX, CONJ_ASSOC, EQ_TRANS, EXTENSION, FIELD_REAL_RING,
        FINITE_IMAGE_INJ_EQ, HAS_SIZE, INTEGER_CLOSED, IN_ELIM_THM, IN_IMAGE,
        NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS, NUMBER_FIELD_PRODUCT_FORMULA,
        NUMBER_FIELD_RATIONAL_FIELD, PRIME_IMP_NZ, PRODUCT_CONST, PRODUCT_EQ,
        PRODUCT_IMAGE, .. } := D.core1
  let { REAL_ABS_NUM, REAL_OF_NUM_EQ, REAL_POW_1, REAL_RING_CHAR, REAL_RING_CLAUSES,
        REAL_RING_OF_INT, REAL_RING_OF_NUM, RING_OF_INT,
        RING_OF_INTEGERS_PRIME_SUBFIELD_PRIME_IDEAL, RING_OF_INTEGERS_RATIONAL_FIELD,
        RING_OF_INT_SUBFIELD_GENERATED, SUBFIELD_GENERATED, int_of_num_th, o_DEF, .. } := D.core2
  let { PRIME_SUBFIELD_IDEAL_GENERATED_PRIME_EQ, RATIONAL_FIELD_COMPLEX_EMBEDDINGS, .. } := BPlaces01
  -- @@SCOPE END

  let RATIONAL_PRODUCT_FORMULA ← prove
    r"!x. x IN ring_carrier(subfield_generated real_ring {&0}) /\ ~(x = &0)
       ==> FINITE {p | prime p /\
                       ~(dedekind_valuation
                          (ring_of_integers(subfield_generated real_ring {&0}),
                           subfield_generated real_ring {&0}) I
                          (ideal_generated
                            (ring_of_integers
                              (subfield_generated real_ring {&0})) {&p})
                          x = &0)} /\
           product {p | prime p /\
                        ~(dedekind_valuation
                           (ring_of_integers
                             (subfield_generated real_ring {&0}),
                            subfield_generated real_ring {&0}) I
                           (ideal_generated
                             (ring_of_integers
                               (subfield_generated real_ring {&0})) {&p})
                           x = &0)}
                   (\p. &p zpow
                        --(dedekind_valuation
                            (ring_of_integers
                              (subfield_generated real_ring {&0}),
                             subfield_generated real_ring {&0}) I
                            (ideal_generated
                              (ring_of_integers
                                (subfield_generated real_ring {&0})) {&p})
                            x)) *
           abs x = &1"
    (GEN_TAC THEN STRIP_TAC THEN ABBREV_TAC (← q r"Q = subfield_generated real_ring {&0}") THEN ABBREV_TAC (← q r"O = ring_of_integers(Q:real ring)") THEN SUBGOAL_THEN (← q r"number_field(Q:real ring) /\ ring_0 Q = &0") STRIP_ASSUME_TAC THENL [EXPAND_TAC "Q" THEN REWRITE_TAC [NUMBER_FIELD_RATIONAL_FIELD, SUBFIELD_GENERATED, REAL_RING_CLAUSES], ALL_TAC] THEN SUBGOAL_THEN (← q r"!y. y IN ring_carrier Q
        ==> product (complex_embeddings Q) (\g. norm(g y)) = abs y") (LABEL_TAC "emb") THENL [X_GEN_TAC (← q r"y:real") THEN DISCH_TAC THEN MP_TAC RATIONAL_FIELD_COMPLEX_EMBEDDINGS THEN ASM_REWRITE_TAC [HAS_SIZE] THEN STRIP_TAC THEN TRANS_TAC EQ_TRANS (← q r"product (complex_embeddings Q) (\g:real->complex. abs y)") THEN CONJ_TAC THENL [MATCH_MP_TAC PRODUCT_EQ THEN ASM_SIMP_TAC [COMPLEX_NORM_CX], ASM_SIMP_TAC [PRODUCT_CONST, REAL_POW_1]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"Q:real ring"), (← q r"x:real")] NUMBER_FIELD_PRODUCT_FORMULA) THEN ASM_SIMP_TAC [] THEN SUBGOAL_THEN (← q r"{P | prime_ideal O P /\ ~(P = {&0}) /\
         ~(dedekind_valuation (O,Q) I P (x:real) = &0)} =
    IMAGE (\p. ideal_generated O {&p})
          {p | prime p /\
               ~(dedekind_valuation (O,Q) I (ideal_generated O {&p}) x = &0)}") SUBST1_TAC THENL [MP_TAC (← ISPEC (← q r"real_ring") RING_OF_INTEGERS_PRIME_SUBFIELD_PRIME_IDEAL) THEN ASM_REWRITE_TAC [FIELD_REAL_RING, REAL_RING_CHAR, REAL_RING_CLAUSES, REAL_RING_OF_NUM] THEN DISCH_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"P:real->bool") THEN REWRITE_TAC [IN_ELIM_THM, IN_IMAGE] THEN REWRITE_TAC [CONJ_ASSOC] THEN ASM_REWRITE_TAC [] THEN EQ_TAC THENL [DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"p:num") STRIP_ASSUME_TAC) ASSUME_TAC) THEN EXISTS_TAC (← q r"p:num") THEN FIRST_X_ASSUM (SUBST_ALL_TAC o (checkM (fun th => (do if ← (do let z7 ← (do let z8 ← (pure th); pure (concl z8)); pure (is_eq z7)) then (do let z12 ← (q r"P:real->bool"); let z11 ← (do let z9 ← (do let z10 ← (pure th); pure (concl z10)); liftExcept (lhs z9)); pure (z11 == z12)) else pure false)))) THEN ASM_REWRITE_TAC [], DISCH_THEN (X_CHOOSE_THEN (← q r"p:num") STRIP_ASSUME_TAC) THEN FIRST_X_ASSUM (SUBST_ALL_TAC o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_eq z1)) then (do let z6 ← (q r"P:real->bool"); let z5 ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); liftExcept (lhs z3)); pure (z5 == z6)) else pure false)))) THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"p:num") THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"!p q. p IN {p | prime p /\
                    ~(dedekind_valuation (O,Q) I (ideal_generated O {&p}) x =
                      &0)} /\
          q IN {p | prime p /\
                    ~(dedekind_valuation (O,Q) I (ideal_generated O {&p}) x =
                      &0)} /\
          ideal_generated O {&p} = ideal_generated O {&q:real}
          ==> p = q") ASSUME_TAC THENL [REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"real_ring"), (← q r"p:num"), (← q r"q:num")] PRIME_SUBFIELD_IDEAL_GENERATED_PRIME_EQ) THEN ASM_REWRITE_TAC [FIELD_REAL_RING, REAL_RING_CHAR, REAL_RING_CLAUSES, REAL_RING_OF_NUM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"\p. ideal_generated O {&p:real}"), (← q r"{p | prime p /\
                       ~(dedekind_valuation (O,Q) I
                          (ideal_generated O {&p}) (x:real) = &0)}")] FINITE_IMAGE_INJ_EQ) THEN MP_TAC (← ISPECL [(← q r"\p. ideal_generated O {&p:real}"), (← q r"\P. &(ideal_norm O P) zpow
                      --(dedekind_valuation (O,Q) I P (x:real))"), (← q r"{p | prime p /\
                       ~(dedekind_valuation (O,Q) I
                          (ideal_generated O {&p}) (x:real) = &0)}")] PRODUCT_IMAGE) THEN ASM_REWRITE_TAC [o_DEF] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN ASM_REWRITE_TAC [] THEN AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC (← q r"p:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN REWRITE_TAC [] THEN AP_THM_TAC THEN AP_TERM_TAC THEN MP_TAC (← ISPECL [(← q r"Q:real ring"), (← q r"&p:real")] NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [EXPAND_TAC "O" THEN EXPAND_TAC "Q" THEN REWRITE_TAC [RING_OF_INTEGERS_RATIONAL_FIELD] THEN ASM_SIMP_TAC [INTEGER_CLOSED, REAL_OF_NUM_EQ, PRIME_IMP_NZ], DISCH_THEN SUBST1_TAC] THEN REMOVE_THEN "emb" (MP_TAC o (SPEC (← q r"&p:real"))) THEN ANTS_TAC THENL [MP_TAC (← ISPECL [(← q r"Q:real ring"), (← q r"&p:int")] RING_OF_INT) THEN EXPAND_TAC "Q" THEN REWRITE_TAC [RING_OF_INT_SUBFIELD_GENERATED, REAL_RING_OF_INT, int_of_num_th], SIMP_TAC [REAL_ABS_NUM]])

  -- @@RETURN BEGIN
  return { RATIONAL_PRODUCT_FORMULA }
  -- @@RETURN END

end HolANT.Places
