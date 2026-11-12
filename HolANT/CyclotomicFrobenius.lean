/- ========================================================================= -/
/- ANT: Decomposition and Frobenius elements in cyclotomic fields          -/
/- ========================================================================= -/
/- File: HolANT/CyclotomicFrobenius.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/cyclotomic_frobenius.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antcyclotomicfrobeniusdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/frag.ml, Library/grouptheory.ml, Library/symmetric_group.ml, Library/galois.ml, Library/integer.ml, Library/isum.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/modmul_group.ml, Library/cyclotomic.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, Library/ring_groups.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/prime_split.ml, ANT/norm_index.ml, ANT/discriminant.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/classgroup.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/relative_degree.ml, ANT/nf_valuation.ml, ANT/integrality.ml, ANT/dedekind_kummer.ml, Library/finite_fields.ml, ANT/cyclotomic_poly.ml, ANT/power_basis.ml, ANT/cyclotomic_field.ml, ANT/cyclotomic_galois.ml, ANT/decomposition.ml, ANT/finite_field_trace.ml, ANT/ramification.ml, ANT/splitting_types.ml, ANT/nf_decomposition.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.CyclotomicFrobenius fills them).

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
import HolLibrary.SymmetricGroup
import HolLibrary.Galois
import HolLibrary.Integer
import HolLibrary.Isum
import HolLibrary.Products
import HolLibrary.Multiplicative
import HolLibrary.Primitive
import HolLibrary.ModmulGroup
import HolLibrary.Cyclotomic
import HolANT.Algmisc
import HolANT.Integral
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolLibrary.RingGroups
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
import HolLibrary.FiniteFields
import HolANT.CyclotomicPoly
import HolANT.PowerBasis
import HolANT.CyclotomicField
import HolANT.CyclotomicGalois
import HolANT.Decomposition
import HolANT.FiniteFieldTrace
import HolANT.Ramification
import HolANT.SplittingTypes
import HolANT.NfDecomposition

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
open HolANT.CyclotomicPoly
open HolANT.PowerBasis
open HolANT.CyclotomicField
open HolANT.CyclotomicGalois
open HolANT.Decomposition
open HolANT.FiniteFieldTrace
open HolANT.Ramification
open HolANT.SplittingTypes
open HolANT.NfDecomposition

namespace HolANT.CyclotomicFrobenius

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (CARD_IMAGE_INJ CARD_NUMSEG_LT CYCLOTOMIC_FIELD_GALOIS_EXTENSION
   CYCLOTOMIC_FIELD_GALOIS_GROUP_EQ DECOMPOSITION_GROUP_RING_OF_INTEGERS
   EXTENSION FINITE_NUMSEG_LT FROBENIUS_ELEMENT GALOIS_GROUP_I
   GALOIS_GROUP_RING_HOMOMORPHISM GALOIS_GROUP_RING_OF_INTEGERS IMAGE_I
   INERTIA_GROUP INTEGRAL_DOMAIN_RING_OF_INTEGERS INT_CONG_IMP_EQ INT_LT_REM
   INT_OF_NUM_EQ INT_OF_NUM_LT INT_OF_NUM_OF_INT INT_REM_DIV INT_REM_POS
   IN_ELIM_THM IN_IMAGE IN_INTER IN_RING_IDEAL_0 IN_SING IN_UNIV I_THM
   LEFT_IMP_EXISTS_THM LT_NZ MAXIMAL_IMP_PRIME_IDEAL MAXIMAL_IMP_RING_IDEAL
   MULT_SYM NUMBER_FIELD_IMP_FIELD PRIME_0 PRIME_IMP_NZ RING_COSET_EQ
   RING_HOMOMORPHISM_1 RING_HOMOMORPHISM_POW RING_OF_INTEGERS
   RING_OF_INTEGERS_FINITE_QUOTIENT RING_OF_INTEGERS_PRIME_SUBFIELD
   RING_OF_INTEGERS_SUBRING RING_OF_INTEGERS_SUBSET RING_OF_INT_IN_PRIME_IDEAL
   RING_OF_INT_IN_RING_OF_INTEGERS RING_OF_INT_OF_NUM RING_OF_INT_SUB
   RING_OF_NUM_EQ_0 RING_POW RING_POW_MUL RING_POW_ONE RING_POW_POW
   RING_POW_RING_ORDER RING_SUB_REFL ROOTS_OF_UNITY_EQ_MOD_IDEAL
   ROOT_OF_UNITY_IN_RING_OF_INTEGERS SUBSET int_congruent int_divides
   num_divides number_field : thm)
  deriving Inhabited

/-- What cyclotomic_frobenius.ml uses from Session besides theorems. -/
structure CyclotomicFrobeniusDeps where
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
/- cyclotomic_frobenius.ml phrases from line 20 to 161                    -/
/- ---------------------------------------------------------------------- -/

structure CyclotomicFrobenius where
  -- @@FIELDS
  NUMBER_FIELD_RESIDUE_PRIME_FIELD_CARD : thm
  CYCLOTOMIC_FIELD_INERTIA_GROUP : thm
  CYCLOTOMIC_FIELD_FROBENIUS_ELEMENT : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupCyclotomicFrobenius [HolBase] (D : CyclotomicFrobeniusDeps) :
    ExceptT String IO CyclotomicFrobenius := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, INTEGER_RULE, INT_ARITH_TAC, MESON_TAC, NUMBER_RULE, SET_TAC, .. } := D
  let { CARD_IMAGE_INJ, CARD_NUMSEG_LT, CYCLOTOMIC_FIELD_GALOIS_EXTENSION,
        CYCLOTOMIC_FIELD_GALOIS_GROUP_EQ, DECOMPOSITION_GROUP_RING_OF_INTEGERS,
        EXTENSION, FINITE_NUMSEG_LT, FROBENIUS_ELEMENT, GALOIS_GROUP_I,
        GALOIS_GROUP_RING_HOMOMORPHISM, GALOIS_GROUP_RING_OF_INTEGERS, IMAGE_I,
        INERTIA_GROUP, INTEGRAL_DOMAIN_RING_OF_INTEGERS, INT_CONG_IMP_EQ, INT_LT_REM,
        INT_OF_NUM_EQ, INT_OF_NUM_LT, INT_OF_NUM_OF_INT, INT_REM_DIV, INT_REM_POS,
        IN_ELIM_THM, IN_IMAGE, IN_INTER, IN_RING_IDEAL_0, IN_SING, IN_UNIV, I_THM,
        LEFT_IMP_EXISTS_THM, LT_NZ, MAXIMAL_IMP_PRIME_IDEAL, MAXIMAL_IMP_RING_IDEAL,
        MULT_SYM, NUMBER_FIELD_IMP_FIELD, PRIME_0, PRIME_IMP_NZ, RING_COSET_EQ,
        RING_HOMOMORPHISM_1, RING_HOMOMORPHISM_POW, RING_OF_INTEGERS,
        RING_OF_INTEGERS_FINITE_QUOTIENT, RING_OF_INTEGERS_PRIME_SUBFIELD,
        RING_OF_INTEGERS_SUBRING, RING_OF_INTEGERS_SUBSET, RING_OF_INT_IN_PRIME_IDEAL,
        RING_OF_INT_IN_RING_OF_INTEGERS, RING_OF_INT_OF_NUM, RING_OF_INT_SUB,
        RING_OF_NUM_EQ_0, RING_POW, RING_POW_MUL, RING_POW_ONE, RING_POW_POW,
        RING_POW_RING_ORDER, RING_SUB_REFL, ROOTS_OF_UNITY_EQ_MOD_IDEAL,
        ROOT_OF_UNITY_IN_RING_OF_INTEGERS, SUBSET, int_congruent, int_divides,
        num_divides, number_field, .. } := D.core1
  -- @@SCOPE END

  let NUMBER_FIELD_RESIDUE_PRIME_FIELD_CARD ← prove
    r"!(k:A ring) P p.
        field k /\ ring_char k = 0 /\ prime p /\
        ring_ideal (ring_of_integers k) P /\
        (!m. ring_of_int k m IN P <=> &p divides m)
        ==> CARD {ring_coset (ring_of_integers k) P (I a) | a |
                  a IN ring_carrier(subfield_generated k {ring_0 k}) /\
                  I a IN ring_carrier(ring_of_integers k)} = p"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [I_THM] THEN SUBGOAL_THEN (← q r"!a. a IN ring_carrier(subfield_generated k {ring_0 k}) /\
        a IN ring_carrier(ring_of_integers k) <=>
        ?n. a = ring_of_int (k:A ring) n") ASSUME_TAC THENL [GEN_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_PRIME_SUBFIELD) THEN ASM_REWRITE_TAC [EXTENSION, IN_INTER, IN_ELIM_THM, IN_UNIV] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"a:A"))) THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!n n'. ring_coset (ring_of_integers k) P (ring_of_int k n) =
           ring_coset (ring_of_integers k) P (ring_of_int (k:A ring) n') <=>
           &p divides (n - n')") ASSUME_TAC THENL [REPEAT GEN_TAC THEN wPart lhand (lhand o rand) RING_COSET_EQ THEN ASM_REWRITE_TAC [RING_OF_INT_IN_RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [RING_OF_INTEGERS, (← GSYM RING_OF_INT_SUB)] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"{ring_coset (ring_of_integers k) P a | a |
     a IN ring_carrier(subfield_generated k {ring_0 k}) /\
     a IN ring_carrier(ring_of_integers k)} =
    IMAGE (\i. ring_coset (ring_of_integers k) P
                (ring_of_int (k:A ring) (&i))) {i | i < p}") SUBST1_TAC THENL [GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM, IN_IMAGE] THEN X_GEN_TAC (← q r"X:A->bool") THEN ASM_REWRITE_TAC [] THEN EQ_TAC THENL [REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"a:A") THEN DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q r"n:int")) ASSUME_TAC) THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"num_of_int(n rem &p)") THEN SUBGOAL_THEN (← q r"~(&p:int = &0)") ASSUME_TAC THENL [REWRITE_TAC [INT_OF_NUM_EQ] THEN ASM_MESON_TAC [PRIME_0], ALL_TAC] THEN ASM_SIMP_TAC [INT_OF_NUM_OF_INT, INT_REM_POS] THEN CONJ_TAC THENL [REWRITE_TAC [INT_REM_DIV] THEN CONV_TAC INTEGER_RULE, REWRITE_TAC [(← GSYM INT_OF_NUM_LT)] THEN ASM_SIMP_TAC [INT_OF_NUM_OF_INT, INT_REM_POS] THEN MATCH_MP_TAC INT_LT_REM THEN REWRITE_TAC [INT_OF_NUM_LT] THEN UNDISCH_TAC (← q r"prime p") THEN REWRITE_TAC [(← GSYM LT_NZ)] THEN MESON_TAC [PRIME_IMP_NZ, LT_NZ]], DISCH_THEN (X_CHOOSE_THEN (← q r"i:num") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"ring_of_int (k:A ring) (&i)") THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [MESON_TAC [], CONV_TAC INTEGER_RULE]], ALL_TAC] THEN wPart lhand (lhand o rand) CARD_IMAGE_INJ THEN REWRITE_TAC [FINITE_NUMSEG_LT, CARD_NUMSEG_LT, IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN MAP_EVERY X_GEN_TAC [(← q r"i:num"), (← q r"j:num")] THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN REWRITE_TAC [(← GSYM INT_OF_NUM_EQ)] THEN MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC (← q r"&p:int") THEN ASM_REWRITE_TAC [int_congruent, (← GSYM int_divides)] THEN UNDISCH_TAC (← q r"i < p:num") THEN UNDISCH_TAC (← q r"j < p:num") THEN REWRITE_TAC [(← GSYM INT_OF_NUM_LT)] THEN INT_ARITH_TAC)

  let CYCLOTOMIC_FIELD_INERTIA_GROUP ← prove
    r"!(k:A ring) z n p P.
        number_field k /\ z IN ring_carrier k /\ ring_order k z = n /\
        subfield_generated k {z} = k /\
        prime p /\ ~(p divides n) /\
        maximal_ideal (ring_of_integers k) P /\ ring_of_num k p IN P
        ==> group_carrier(inertia_group(subfield_generated k {ring_0 k},k) I
                           (ring_of_integers k) P) = {I}"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN (← q r"~(n = 0)") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~((p:num) divides 0)") THEN CONV_TAC NUMBER_RULE, ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_PRIME_IDEAL)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"~(ring_of_num k n IN (P:A->bool))") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"p:num")] RING_OF_INT_IN_PRIME_IDEAL) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"&n:int"))) THEN ASM_REWRITE_TAC [RING_OF_INT_OF_NUM, (← GSYM num_divides)], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_pow k z n = ring_1 (k:A ring)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A")] RING_POW_RING_ORDER) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(z:A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [MATCH_MP_TAC ROOT_OF_UNITY_IN_RING_OF_INTEGERS THEN EXISTS_TAC (← q r"n:num") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k}:A ring"), (← q r"k:A ring"), (← q r"ring_of_integers k:A ring"), (← q r"P:A->bool")] (← CONJUNCT1 INERTIA_GROUP)) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBRING, DECOMPOSITION_GROUP_RING_OF_INTEGERS], DISCH_THEN SUBST1_TAC] THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"f:A->A") THEN REWRITE_TAC [IN_ELIM_THM, IN_SING] THEN EQ_TAC THENL [STRIP_TAC THEN SUBGOAL_THEN (← q r"(f:A->A) z = z") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"n:num"), (← q r"(f:A->A) z"), (← q r"z:A")] ROOTS_OF_UNITY_EQ_MOD_IDEAL) THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_RING_OF_INTEGERS, RING_OF_INTEGERS] THEN CONJ_TAC THENL [MP_TAC (← MATCH_MP GALOIS_GROUP_RING_OF_INTEGERS (← ASSUME (← q r"(f:A->A) IN group_carrier
            (galois_group(subfield_generated k {ring_0 k},k) I)"))) THEN UNDISCH_TAC (← q r"(z:A) IN ring_carrier(ring_of_integers k)") THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_homomorphism(k,k) (f:A->A)") ASSUME_TAC THENL [FIRST_ASSUM (MATCH_ACCEPT_TAC o (MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM)), ALL_TAC] THEN ASM_SIMP_TAC [(← GSYM (← MATCH_MP RING_HOMOMORPHISM_POW (← ASSUME (← q r"ring_homomorphism(k,k) (f:A->A)"))))] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_1], ALL_TAC] THEN MATCH_MP_TAC CYCLOTOMIC_FIELD_GALOIS_GROUP_EQ THEN MAP_EVERY EXISTS_TAC [(← q r"k:A ring"), (← q r"z:A")] THEN ASM_REWRITE_TAC [GALOIS_GROUP_I, I_THM], DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [GALOIS_GROUP_I, IMAGE_I, I_THM] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [RING_SUB_REFL] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool")] IN_RING_IDEAL_0) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS]])

  let CYCLOTOMIC_FIELD_FROBENIUS_ELEMENT ← prove
    r"!(k:A ring) z n p P.
        number_field k /\ z IN ring_carrier k /\ ring_order k z = n /\
        subfield_generated k {z} = k /\
        prime p /\ ~(p divides n) /\
        maximal_ideal (ring_of_integers k) P /\ ring_of_num k p IN P
        ==> frobenius_element (subfield_generated k {ring_0 k},k) I
              (ring_of_integers k) P z =
            ring_pow k z p"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN (← q r"~(n = 0)") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~((p:num) divides 0)") THEN CONV_TAC NUMBER_RULE, ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_PRIME_IDEAL)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"!m. ring_of_int (k:A ring) m IN P <=> &p divides m") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"p:num")] RING_OF_INT_IN_PRIME_IDEAL) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(ring_of_num k n IN (P:A->bool))") ASSUME_TAC THENL [ASM_REWRITE_TAC [(← GSYM RING_OF_INT_OF_NUM), (← GSYM num_divides)], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_pow k z n = ring_1 (k:A ring)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A")] RING_POW_RING_ORDER) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(z:A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [MATCH_MP_TAC ROOT_OF_UNITY_IN_RING_OF_INTEGERS THEN EXISTS_TAC (← q r"n:num") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(P = {ring_0 (k:A ring)})") ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC (← q r"ring_of_num k p IN (P:A->bool)") THEN ASM_REWRITE_TAC [IN_SING, RING_OF_NUM_EQ_0] THEN UNDISCH_TAC (← q r"number_field(k:A ring)") THEN SIMP_TAC [number_field] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN REWRITE_TAC [(← ExceptT.mk (NUMBER_RULE (← q r"((0:num) divides n) <=> n = 0")))] THEN ASM_MESON_TAC [PRIME_0], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num"), (← q r"p:num"), (← q r"P:A->bool")] CYCLOTOMIC_FIELD_INERTIA_GROUP) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"P:A->bool"), (← q r"p:num")] NUMBER_FIELD_RESIDUE_PRIME_FIELD_CARD) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"number_field(k:A ring)") THEN SIMP_TAC [number_field], DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k}:A ring"), (← q r"k:A ring"), (← q r"ring_of_integers k:A ring"), (← q r"P:A->bool")] FROBENIUS_ELEMENT) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBRING, GALOIS_GROUP_RING_OF_INTEGERS] THEN REPEAT CONJ_TAC THENL [UNDISCH_TAC (← q r"number_field(k:A ring)") THEN SIMP_TAC [number_field], MATCH_MP_TAC CYCLOTOMIC_FIELD_GALOIS_EXTENSION THEN MAP_EVERY EXISTS_TAC [(← q r"z:A"), (← q r"n:num")] THEN ASM_REWRITE_TAC [], MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_REWRITE_TAC []], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"g = frobenius_element (subfield_generated k {ring_0 k},k) I
          (ring_of_integers k) (P:A->bool)") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o (SPEC (← q r"g:A->A")))) THEN REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_homomorphism(k,k) (g:A->A)") ASSUME_TAC THENL [FIRST_ASSUM (MATCH_ACCEPT_TAC o (MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM)), ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"n:num"), (← q r"(g:A->A) z"), (← q r"ring_pow k (z:A) p")] ROOTS_OF_UNITY_EQ_MOD_IDEAL) THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_RING_OF_INTEGERS, RING_OF_INTEGERS] THEN REPEAT CONJ_TAC THENL [MP_TAC (← MATCH_MP GALOIS_GROUP_RING_OF_INTEGERS (← ASSUME (← q r"(g:A->A) IN group_carrier
        (galois_group(subfield_generated k {ring_0 k},k) I)"))) THEN UNDISCH_TAC (← q r"(z:A) IN ring_carrier(ring_of_integers k)") THEN SET_TAC [], MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"z:A"), (← q r"p:num")] RING_POW) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], ASM_SIMP_TAC [(← GSYM (← MATCH_MP RING_HOMOMORPHISM_POW (← ASSUME (← q r"ring_homomorphism(k,k) (g:A->A)"))))] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_1], ASM_SIMP_TAC [RING_POW_POW] THEN ONCE_REWRITE_TAC [MULT_SYM] THEN ASM_SIMP_TAC [RING_POW_MUL, RING_POW_ONE]])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_RESIDUE_PRIME_FIELD_CARD, CYCLOTOMIC_FIELD_INERTIA_GROUP,
           CYCLOTOMIC_FIELD_FROBENIUS_ELEMENT }
  -- @@RETURN END

end HolANT.CyclotomicFrobenius
