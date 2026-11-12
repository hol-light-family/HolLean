/- ========================================================================= -/
/- ANT: The product formula for number fields                              -/
/- ========================================================================= -/
/- File: HolANT/ProductFormula.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/product_formula.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antproductformuladiff; the rest is by hand.  Its `needs` closure is
  Library/products.ml, Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/isum.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/norm_index.ml, ANT/classgroup.ml, ANT/nf_valuation.ml, ANT/valuation_ring.ml, ANT/dedekind_absolute.ml, Library/frag.ml, Library/grouptheory.ml, ANT/prime_split.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/integrality.ml, Library/ring_groups.ml, ANT/fingen_group.ml, Multivariate/misc.ml, Multivariate/metric.ml, Multivariate/homology.ml, Multivariate/vectors.ml, Multivariate/determinants.ml, Multivariate/topology.ml, Multivariate/convex.ml, Multivariate/paths.ml, Multivariate/polytope.ml, Multivariate/degree.ml, Multivariate/derivatives.ml, Multivariate/integration.ml, Multivariate/measure.ml, Multivariate/complex_algebra.ml, Multivariate/complexes.ml, Multivariate/canal.ml, Multivariate/transcendentals.ml, Multivariate/realanalysis.ml, Multivariate/moretop.ml, Multivariate/cauchy.ml, Multivariate/complex_ring.ml, Multivariate/complex_field.ml, ANT/complex_embeddings.ml, ANT/power_basis.ml, ANT/infinite_places.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.ProductFormula fills them).

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
import HolANT.ValuationRing
import HolANT.DedekindAbsolute
import HolLibrary.Frag
import HolLibrary.GroupTheory
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
open HolANT.ValuationRing
open HolANT.DedekindAbsolute
open HolANT.PrimeSplit
open HolANT.Discriminant
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.Integrality
open HolANT.FingenGroup
open HolANT.ComplexEmbeddings
open HolANT.PowerBasis
open HolANT.InfinitePlaces

namespace HolANT.ProductFormula

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (COMPLEX_EMBEDDINGS_MONOMORPHISM COMPLEX_EMBEDDINGS_NORM_MUL
   COMPLEX_EMBEDDINGS_NORM_POS COMPLEX_NORM_MUL COMPLEX_NORM_ZERO
   COMPLEX_RING_CLAUSES DEDEKIND_VALUATION_IDEAL_NORM DEDEKIND_VALUATION_MUL
   DEDEKIND_VALUATION_NORMALIZED_ABSOLUTE_VALUE EQ_TRANS EXTENSION
   FIELD_IMP_INTEGRAL_DOMAIN FINITE_COMPLEX_EMBEDDINGS FINITE_SUBSET
   FINITE_UNION IDEAL_GENERATED_EQ_0 IDEAL_NORM_GT_1 INTEGRAL_DOMAIN_MUL_EQ_0
   INT_NEG_0 IN_ELIM_THM IN_UNION I_THM LEFT_IMP_EXISTS_THM NORM_CPRODUCT
   NORM_POS_LE NORM_TRIANGLE NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS
   NUMBER_FIELD_NORM_COMPLEX_EMBEDDINGS PRIME_IMP_PROPER_IDEAL
   PRIME_IMP_RING_IDEAL PRODUCT_DIV PRODUCT_EQ PRODUCT_MUL PRODUCT_POS_LT
   PRODUCT_SUPERSET PROPER_IDEAL_ALT REAL_LT_IMP_NZ REAL_OF_NUM_LT REAL_ZPOW_0
   REAL_ZPOW_MONO_LT REAL_ZPOW_SUB RING_IDEAL_IDEAL_GENERATED
   RING_MONOMORPHISM_ALT_EQ RING_OF_INTEGERS RING_OF_INTEGERS_FINITE_QUOTIENT
   RING_OF_INTEGERS_FRACTION_FIELD RING_OF_INTEGERS_SUBSET SUBSET SUBSET_UNION
   absolute_value field_of_fractions ring_homomorphism : thm)
  deriving Inhabited

/-- What product_formula.ml uses from Session besides theorems. -/
structure ProductFormulaDeps where
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
/- product_formula.ml phrases from line 48 to 275                         -/
/- ---------------------------------------------------------------------- -/

structure ProductFormula where
  -- @@FIELDS
  NUMBER_FIELD_PRODUCT_FORMULA : thm
  NUMBER_FIELD_PRODUCT_FORMULA_NORM : thm
  COMPLEX_EMBEDDINGS_ABSOLUTE_VALUE : thm
  NUMBER_FIELD_PRODUCT_FORMULA_ABSOLUTE_VALUES : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupProductFormula [HolBase] (D : ProductFormulaDeps) :
    ExceptT String IO ProductFormula := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, INT_ARITH, INT_ARITH_TAC,
        MESON_TAC, REAL_FIELD, SET_TAC, TAUT, .. } := D
  let { COMPLEX_EMBEDDINGS_MONOMORPHISM, COMPLEX_EMBEDDINGS_NORM_MUL,
        COMPLEX_EMBEDDINGS_NORM_POS, COMPLEX_NORM_MUL, COMPLEX_NORM_ZERO,
        COMPLEX_RING_CLAUSES, DEDEKIND_VALUATION_IDEAL_NORM, DEDEKIND_VALUATION_MUL,
        DEDEKIND_VALUATION_NORMALIZED_ABSOLUTE_VALUE, EQ_TRANS, EXTENSION,
        FIELD_IMP_INTEGRAL_DOMAIN, FINITE_COMPLEX_EMBEDDINGS, FINITE_SUBSET,
        FINITE_UNION, IDEAL_GENERATED_EQ_0, IDEAL_NORM_GT_1, INTEGRAL_DOMAIN_MUL_EQ_0,
        INT_NEG_0, IN_ELIM_THM, IN_UNION, I_THM, LEFT_IMP_EXISTS_THM, NORM_CPRODUCT,
        NORM_POS_LE, NORM_TRIANGLE, NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS,
        NUMBER_FIELD_NORM_COMPLEX_EMBEDDINGS, PRIME_IMP_PROPER_IDEAL,
        PRIME_IMP_RING_IDEAL, PRODUCT_DIV, PRODUCT_EQ, PRODUCT_MUL, PRODUCT_POS_LT,
        PRODUCT_SUPERSET, PROPER_IDEAL_ALT, REAL_LT_IMP_NZ, REAL_OF_NUM_LT,
        REAL_ZPOW_0, REAL_ZPOW_MONO_LT, REAL_ZPOW_SUB, RING_IDEAL_IDEAL_GENERATED,
        RING_MONOMORPHISM_ALT_EQ, RING_OF_INTEGERS, RING_OF_INTEGERS_FINITE_QUOTIENT,
        RING_OF_INTEGERS_FRACTION_FIELD, RING_OF_INTEGERS_SUBSET, SUBSET, SUBSET_UNION,
        absolute_value, field_of_fractions, ring_homomorphism, .. } := D.core1
  -- @@SCOPE END

  let NUMBER_FIELD_PRODUCT_FORMULA ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_FIELD (← q r"!B X:real. &0 < B /\ &0 < X ==> B / (B * X) * X = &1")
    let r2 ← TAUT (← q r"~(p /\ q /\ ~r) <=> p ==> q ==> r")
    let r3 ← ARITH_RULE (← q r"1 < n ==> 0 < n")
    prove
      r"!(k:A ring) x.
          number_field k /\ x IN ring_carrier k /\ ~(x = ring_0 k)
          ==> FINITE {P | prime_ideal (ring_of_integers k) P /\
                          ~(P = {ring_0 k}) /\
                          ~(dedekind_valuation (ring_of_integers k,k) I P x =
                            &0)} /\
              product {P | prime_ideal (ring_of_integers k) P /\
                           ~(P = {ring_0 k}) /\
                           ~(dedekind_valuation (ring_of_integers k,k) I P x =
                             &0)}
                      (\P. &(ideal_norm (ring_of_integers k) P) zpow
                           --(dedekind_valuation (ring_of_integers k,k) I P x)) *
              product (complex_embeddings k) (\g. norm(g x)) = &1"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_FRACTION_FIELD) THEN ASM_REWRITE_TAC [field_of_fractions, RING_OF_INTEGERS, I_THM] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"x:A"))) THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN ABBREV_TAC (← q r"O = ring_of_integers(k:A ring)") THEN SUBGOAL_THEN (← q r"ring_carrier(O:A ring) SUBSET ring_carrier k /\ ring_0 O = ring_0 k") STRIP_ASSUME_TAC THENL [EXPAND_TAC "O" THEN REWRITE_TAC [RING_OF_INTEGERS_SUBSET, RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier k /\ (b:A) IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(a:A = ring_0 k)") ASSUME_TAC THENL [UNDISCH_TAC (← q r"ring_mul k b x = (a:A)") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_MUL_EQ_0, FIELD_IMP_INTEGRAL_DOMAIN], ALL_TAC] THEN SUBGOAL_THEN (← q r"!y:A. y IN ring_carrier O /\ ~(y = ring_0 k)
            ==> FINITE {P | prime_ideal O P /\ ~(P = {ring_0 k}) /\
                            ~(dedekind_valuation (O,k) I P y = &0)} /\
                product {P | prime_ideal O P /\ ~(P = {ring_0 k}) /\
                             ~(dedekind_valuation (O,k) I P y = &0)}
                  (\P. &(ideal_norm O P) zpow dedekind_valuation (O,k) I P y) =
                product (complex_embeddings k) (\g. norm(g y))") (LABEL_TAC "int") THENL [X_GEN_TAC (← q r"y:A") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"y:A")] NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"O:A ring"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"y:A")] DEDEKIND_VALUATION_IDEAL_NORM) THEN ASM_REWRITE_TAC [I_THM] THEN DISCH_THEN MATCH_MP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ideal_generated O {y:A}")] RING_OF_INTEGERS_FINITE_QUOTIENT) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN DISCH_THEN MATCH_MP_TAC THEN UNDISCH_TAC (← q r"ring_0 O = ring_0 (k:A ring)") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC [IDEAL_GENERATED_EQ_0] THEN EXPAND_TAC "O" THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_FRACTION_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!P. prime_ideal O P /\ ~(P = {ring_0 k})
          ==> dedekind_valuation (O,k) I P x =
              dedekind_valuation (O,k) I P a -
              dedekind_valuation (O,k) I P (b:A)") (LABEL_TAC "sub") THENL [X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"O:A ring"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"P:A->bool"), (← q r"b:A"), (← q r"x:A")] DEDEKIND_VALUATION_MUL) THEN ASM_REWRITE_TAC [I_THM] THEN INT_ARITH_TAC, ALL_TAC] THEN USE_THEN "int" (MP_TAC o (SPEC (← q r"a:A"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN USE_THEN "int" (MP_TAC o (SPEC (← q r"b:A"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN SUBGOAL_THEN (← q r"!P. prime_ideal O P /\ ~(P = {ring_0 k})
          ==> &0 < (&(ideal_norm O (P:A->bool)):real)") (LABEL_TAC "npos") THENL [REPEAT STRIP_TAC THEN REWRITE_TAC [REAL_OF_NUM_LT] THEN MATCH_MP_TAC r3 THEN MATCH_MP_TAC IDEAL_NORM_GT_1 THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN CONJ_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP PRIME_IMP_PROPER_IDEAL)) THEN SIMP_TAC [PROPER_IDEAL_ALT], ALL_TAC] THEN UNDISCH_TAC (← q r"ring_of_integers k = (O:A ring)") THEN DISCH_THEN (SUBST_ALL_TAC o SYM) THEN MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], ALL_TAC] THEN ABBREV_TAC (← q r"Sa = {P | prime_ideal O P /\ ~(P = {ring_0 k}) /\
                ~(dedekind_valuation (O,k) I P (a:A) = &0)}") THEN ABBREV_TAC (← q r"Sb = {P | prime_ideal O P /\ ~(P = {ring_0 k}) /\
                ~(dedekind_valuation (O,k) I P (b:A) = &0)}") THEN ABBREV_TAC (← q r"Sx = {P | prime_ideal O P /\ ~(P = {ring_0 k}) /\
                ~(dedekind_valuation (O,k) I P (x:A) = &0)}") THEN SUBGOAL_THEN (← q r"(Sx:(A->bool)->bool) SUBSET Sa UNION Sb") ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["Sx", "Sa", "Sb"] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM, IN_UNION] THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"~(dedekind_valuation (O,k) I P (x:A) = &0)") THEN USE_THEN "sub" (fun th => ASM_SIMP_TAC [th]) THEN INT_ARITH_TAC, ALL_TAC] THEN CONJ_TAC THENL [ASM_MESON_TAC [FINITE_SUBSET, FINITE_UNION], ALL_TAC] THEN SUBGOAL_THEN (← q r"FINITE(Sa:(A->bool)->bool) /\ FINITE(Sb:(A->bool)->bool)") STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!P. P IN Sa UNION Sb
          ==> prime_ideal O P /\ ~(P = {ring_0 k:A})") (LABEL_TAC "inS") THENL [MAP_EVERY EXPAND_TAC ["Sa", "Sb"] THEN REWRITE_TAC [IN_UNION, IN_ELIM_THM] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"product Sx (\P. &(ideal_norm O P) zpow --dedekind_valuation (O,k) I P x) =
      product (Sa UNION Sb)
       (\P. &(ideal_norm O P) zpow dedekind_valuation (O,k) I P b) /
      product (Sa UNION Sb)
       (\P. &(ideal_norm O P) zpow dedekind_valuation (O,k) I P (a:A))") SUBST1_TAC THENL [ASM_SIMP_TAC [(← GSYM PRODUCT_DIV), FINITE_UNION] THEN CONV_TAC SYM_CONV THEN TRANS_TAC EQ_TRANS (← q r"product (Sa UNION Sb)
          (\P. &(ideal_norm O P) zpow --dedekind_valuation (O,k) I P (x:A))") THEN CONJ_TAC THENL [MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC (← q r"P:A->bool") THEN DISCH_TAC THEN USE_THEN "inS" (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN USE_THEN "sub" (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN USE_THEN "npos" (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN ASM_SIMP_TAC [(← GSYM REAL_ZPOW_SUB), REAL_LT_IMP_NZ] THEN AP_TERM_TAC THEN INT_ARITH_TAC, MATCH_MP_TAC PRODUCT_SUPERSET THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN USE_THEN "inS" (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN UNDISCH_TAC (← q r"~((P:A->bool) IN Sx)") THEN EXPAND_TAC "Sx" THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN SIMP_TAC [INT_NEG_0, REAL_ZPOW_0]], ALL_TAC] THEN SUBGOAL_THEN (← q r"product (Sa UNION Sb)
       (\P. &(ideal_norm O P) zpow dedekind_valuation (O,k) I P b) =
      product Sb
       (\P. &(ideal_norm O P) zpow dedekind_valuation (O,k) I P (b:A)) /\
      product (Sa UNION Sb)
       (\P. &(ideal_norm O P) zpow dedekind_valuation (O,k) I P a) =
      product Sa
       (\P. &(ideal_norm O P) zpow dedekind_valuation (O,k) I P (a:A))") (CONJUNCTS_THEN SUBST1_TAC) THENL [CONJ_TAC THEN MATCH_MP_TAC PRODUCT_SUPERSET THEN REWRITE_TAC [SUBSET_UNION] THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN USE_THEN "inS" (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN (ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC]) THEN MAP_EVERY EXPAND_TAC ["Sa", "Sb"] THEN RULE_ASSUM_TAC (REWRITE_RULE [(← SYM (← ASSUME (← q r"{P | prime_ideal O P /\ ~(P = {ring_0 k}) /\
                        ~(dedekind_valuation (O,k) I P (a:A) = &0)} = Sa"))), (← SYM (← ASSUME (← q r"{P | prime_ideal O P /\ ~(P = {ring_0 k}) /\
                        ~(dedekind_valuation (O,k) I P (b:A) = &0)} = Sb")))]) THEN RULE_ASSUM_TAC (REWRITE_RULE [IN_ELIM_THM, r2]) THEN ASM_SIMP_TAC [REAL_ZPOW_0], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"product (complex_embeddings k) (\g. norm((g:A->complex) a)) =
      product (complex_embeddings k) (\g. norm(g b)) *
      product (complex_embeddings k) (\g. norm(g x))") SUBST1_TAC THENL [ASM_SIMP_TAC [(← GSYM PRODUCT_MUL), FINITE_COMPLEX_EMBEDDINGS] THEN MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC (← q r"g:A->complex") THEN DISCH_TAC THEN UNDISCH_TAC (← q r"ring_mul k b x = (a:A)") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [] THEN MATCH_MP_TAC COMPLEX_EMBEDDINGS_NORM_MUL THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MATCH_MP_TAC r1 THEN CONJ_TAC THEN MATCH_MP_TAC PRODUCT_POS_LT THEN ASM_SIMP_TAC [FINITE_COMPLEX_EMBEDDINGS, COMPLEX_EMBEDDINGS_NORM_POS])

  let NUMBER_FIELD_PRODUCT_FORMULA_NORM ← prove
    r"!(k:A ring) (g:A->complex) x.
        number_field k /\ g IN complex_embeddings k /\
        x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> product {P | prime_ideal (ring_of_integers k) P /\
                         ~(P = {ring_0 k}) /\
                         ~(dedekind_valuation (ring_of_integers k,k) I P x =
                           &0)}
                    (\P. &(ideal_norm (ring_of_integers k) P) zpow
                         --(dedekind_valuation (ring_of_integers k,k) I P x)) *
            norm(g(algebra_norm (subfield_generated k {ring_0 k},k) I x)) =
            &1"
    (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_NORM_COMPLEX_EMBEDDINGS, NORM_CPRODUCT, FINITE_COMPLEX_EMBEDDINGS] THEN ASM_SIMP_TAC [NUMBER_FIELD_PRODUCT_FORMULA])

  let COMPLEX_EMBEDDINGS_ABSOLUTE_VALUE ← prove
    r"!k (g:A->complex).
        field k /\ g IN complex_embeddings k
        ==> absolute_value k (\x. norm(g x))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"g:A->complex")] COMPLEX_EMBEDDINGS_MONOMORPHISM) THEN ASM_REWRITE_TAC [RING_MONOMORPHISM_ALT_EQ, ring_homomorphism, COMPLEX_RING_CLAUSES] THEN STRIP_TAC THEN ASM_SIMP_TAC [absolute_value, NORM_POS_LE, COMPLEX_NORM_ZERO, COMPLEX_NORM_MUL, NORM_TRIANGLE])

  let NUMBER_FIELD_PRODUCT_FORMULA_ABSOLUTE_VALUES ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← INT_ARITH (← q r"&0 < --v:int \/ --v < &0:int \/ v = &0")
    let r2 ← TAUT (← q r"(a /\ b ==> (c <=> d)) ==> (a /\ b /\ c <=> a /\ b /\ d)")
    prove
      r"!(k:A ring) f.
          number_field k /\
          (!P x. f P x =
                 if x = ring_0 k then &0
                 else &(ideal_norm (ring_of_integers k) P) zpow
                      --(dedekind_valuation (ring_of_integers k,k) I P x))
          ==> (!P. prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k})
                   ==> nonarchimedean_absolute_value k (f P)) /\
              (!g. g IN complex_embeddings k
                   ==> absolute_value k (\x. norm(g x))) /\
              (!x. x IN ring_carrier k /\ ~(x = ring_0 k)
                   ==> FINITE {P | prime_ideal (ring_of_integers k) P /\
                                   ~(P = {ring_0 k}) /\ ~(f P x = &1)} /\
                       product {P | prime_ideal (ring_of_integers k) P /\
                                    ~(P = {ring_0 k}) /\ ~(f P x = &1)}
                               (\P. f P x) *
                       product (complex_embeddings k) (\g. norm(g x)) = &1)"
      (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_FRACTION_FIELD) THEN ASM_REWRITE_TAC [field_of_fractions, RING_OF_INTEGERS, I_THM] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"!P. prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k})
          ==> 1 < ideal_norm (ring_of_integers k) P /\
              nonarchimedean_absolute_value k ((f:(A->bool)->A->real) P)") (LABEL_TAC "nP") THENL [X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"P:A->bool"), (← q r"(f:(A->bool)->A->real) P")] DEDEKIND_VALUATION_NORMALIZED_ABSOLUTE_VALUE) THEN ASM_REWRITE_TAC [field_of_fractions, RING_OF_INTEGERS, I_THM] THEN ANTS_TAC THENL [MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], SIMP_TAC []], ALL_TAC] THEN REPEAT CONJ_TAC THENL [ASM_SIMP_TAC [], ASM_SIMP_TAC [COMPLEX_EMBEDDINGS_ABSOLUTE_VALUE], ALL_TAC] THEN X_GEN_TAC (← q r"x:A") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"{P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
           ~((f:(A->bool)->A->real) P x = &1)} =
      {P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
           ~(dedekind_valuation (ring_of_integers k,k) I P x = &0)}") SUBST1_TAC THENL [GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"P:A->bool") THEN REWRITE_TAC [IN_ELIM_THM] THEN MATCH_MP_TAC r2 THEN STRIP_TAC THEN USE_THEN "nP" (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (ASSUME_TAC o CONJUNCT1)] THEN ASM_REWRITE_TAC [] THEN SPEC_TAC ((← q r"dedekind_valuation (ring_of_integers k,k) I (P:A->bool) x"), (← q r"v:int")) THEN UNDISCH_TAC (← q r"1 < ideal_norm (ring_of_integers k) (P:A->bool)") THEN SPEC_TAC ((← q r"ideal_norm (ring_of_integers k) (P:A->bool)"), (← q r"N:num")) THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN EQ_TAC THENL [DISCH_TAC THEN SUBGOAL_THEN (← q r"&1 < (&N:real)") ASSUME_TAC THENL [ASM_REWRITE_TAC [REAL_OF_NUM_LT], ALL_TAC] THEN DISJ_CASES_TAC r1 THENL [MP_TAC (← ISPECL [(← q r"&N:real"), (← q r"&0:int"), (← q r"--v:int")] REAL_ZPOW_MONO_LT) THEN ASM_REWRITE_TAC [REAL_ZPOW_0] THEN ASM_REAL_ARITH_TAC, FIRST_X_ASSUM DISJ_CASES_TAC THENL [MP_TAC (← ISPECL [(← q r"&N:real"), (← q r"--v:int"), (← q r"&0:int")] REAL_ZPOW_MONO_LT) THEN ASM_REWRITE_TAC [REAL_ZPOW_0] THEN ASM_REAL_ARITH_TAC, ASM_REWRITE_TAC []]], SIMP_TAC [INT_NEG_0, REAL_ZPOW_0]], ALL_TAC] THEN SUBGOAL_THEN (← q r"product {P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
                   ~(dedekind_valuation (ring_of_integers k,k) I P x = &0)}
              (\P. (f:(A->bool)->A->real) P x) =
      product {P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
                   ~(dedekind_valuation (ring_of_integers k,k) I P x = &0)}
              (\P. &(ideal_norm (ring_of_integers k) P) zpow
                    --(dedekind_valuation (ring_of_integers k,k) I P x))") SUBST1_TAC THENL [MATCH_MP_TAC PRODUCT_EQ THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A")] NUMBER_FIELD_PRODUCT_FORMULA) THEN ASM_REWRITE_TAC [])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_PRODUCT_FORMULA, NUMBER_FIELD_PRODUCT_FORMULA_NORM,
           COMPLEX_EMBEDDINGS_ABSOLUTE_VALUE,
           NUMBER_FIELD_PRODUCT_FORMULA_ABSOLUTE_VALUES }
  -- @@RETURN END

end HolANT.ProductFormula
