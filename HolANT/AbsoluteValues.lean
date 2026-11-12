/- ========================================================================= -/
/- ANT: Absolute values on fields                                          -/
/- ========================================================================= -/
/- File: HolANT/AbsoluteValues.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/absolute_values.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antabsolutevaluesdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/floor.ml, ANT/integral.ml, Library/products.ml, ANT/algmisc.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/ideal_norm.ml, ANT/valuation_ring.ml, ANT/dedekind_absolute.ml, Library/frag.ml, Library/grouptheory.ml, Multivariate/misc.ml, Multivariate/metric.ml, Multivariate/homology.ml, Multivariate/vectors.ml, Multivariate/determinants.ml, Multivariate/topology.ml, Multivariate/convex.ml, Multivariate/paths.ml, Multivariate/polytope.ml, Multivariate/degree.ml, Multivariate/derivatives.ml, Multivariate/integration.ml, Multivariate/measure.ml, Multivariate/complex_algebra.ml, Multivariate/complexes.ml, Multivariate/canal.ml, Multivariate/transcendentals.ml, Multivariate/realanalysis.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.AbsoluteValues fills them).

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
import HolLibrary.Floor
import HolANT.Integral
import HolLibrary.Products
import HolANT.Algmisc
import HolANT.IdealArith
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.IdealNorm
import HolANT.ValuationRing
import HolANT.DedekindAbsolute
import HolLibrary.Frag
import HolLibrary.GroupTheory
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

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.Integral
open HolANT.Algmisc
open HolANT.IdealArith
open HolANT.Dedekind
open HolANT.DedekindStruct
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.IdealNorm
open HolANT.ValuationRing
open HolANT.DedekindAbsolute

namespace HolANT.AbsoluteValues

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ABSOLUTE_VALUE_0 ABSOLUTE_VALUE_1 ABSOLUTE_VALUE_ABS_SUB_LE
   ABSOLUTE_VALUE_DIV ABSOLUTE_VALUE_INV ABSOLUTE_VALUE_MUL ABSOLUTE_VALUE_NEG
   ABSOLUTE_VALUE_NONTRIVIAL ABSOLUTE_VALUE_POS ABSOLUTE_VALUE_POS_LT
   ABSOLUTE_VALUE_POW ABSOLUTE_VALUE_RING_SUM ARCH_EVENTUALLY_POW CARD_EQ_0
   CONTRAPOS_THM DEDEKIND_IMP_INTEGRAL_DOMAIN DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL
   DEDEKIND_VALUATION_ABSOLUTE_VALUE DEDEKIND_VALUATION_IMAGE
   DEDEKIND_VALUATION_POS DEDEKIND_VALUATION_PRIME_IDEAL
   DEDEKIND_VALUATION_WEAK_APPROXIMATION DE_MORGAN_THM EVENTUALLY_AND
   EVENTUALLY_FORALL EVENTUALLY_HAPPENS_SEQUENTIALLY EVENTUALLY_MONO
   EVENTUALLY_TRUE EXISTS_UNIQUE_THM EXP_LOG EXTENSION FIELD_FRACTION_NONZERO
   FIELD_MUL_RINV FIELD_NONTRIVIAL FINITE_DELETE FINITE_INDUCT_STRONG
   FINITE_SING FORALL_IN_INSERT FORALL_UNWIND_THM2 IMP_CONJ INSERT_DELETE
   INSERT_SUBSET INT_NEG_0 INT_NEG_NEG INT_OF_NUM_EQ INT_OF_NUM_LT IN_DELETE
   IN_ELIM_THM IN_IMAGE IN_RING_IDEAL_0 IN_SING LEFT_IMP_EXISTS_THM LE_1
   LOG_MONO_LT LOG_MUL LOG_POS_LT LOG_POW NONARCHIMEDEAN_ABSOLUTE_VALUE
   NONARCHIMEDEAN_IMP_ABSOLUTE_VALUE NOT_EXISTS_THM NOT_FORALL_THM NOT_IMP
   NOT_IN_EMPTY PRIME_IDEAL_IMP_SUBSET PRIME_IMP_PROPER_IDEAL
   PRIME_IMP_RING_IDEAL PROPER_IDEAL_ALT PSUBSET REAL_ARCH_POW REAL_ARCH_POW_INV
   REAL_INV_1_LT REAL_INV_INV REAL_INV_LT_1 REAL_LET_TRANS REAL_LE_INV_EQ
   REAL_LE_LMUL REAL_LE_MAX REAL_LE_MUL2 REAL_LE_RMUL REAL_LE_TRANS
   REAL_LTE_TRANS REAL_LT_01 : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (REAL_LT_DIV REAL_LT_IMP_LE REAL_LT_IMP_NE REAL_LT_IMP_NZ REAL_LT_INV2
   REAL_LT_INV_EQ REAL_LT_LDIV_EQ REAL_LT_LE REAL_LT_LMUL REAL_LT_RDIV_EQ
   REAL_LT_REFL REAL_LT_TRANS REAL_MAX_LT REAL_MAX_RPOW REAL_MUL_LID
   REAL_MUL_RID REAL_MUL_RINV REAL_MUL_SYM REAL_NOT_LT REAL_NUM_FRACTIONS_EQ
   REAL_OF_NUM_LT REAL_POS REAL_POW_1 REAL_POW_1_LE REAL_POW_EVENTUALLY_LT
   REAL_POW_LE REAL_POW_LE_1 REAL_POW_LT REAL_POW_ONE REAL_SUB_LT REAL_ZPOW_0
   REAL_ZPOW_1 REAL_ZPOW_MONO_LT REAL_ZPOW_RPOW RIGHT_IMP_EXISTS_THM RING_0
   RING_1 RING_ADD RING_DIV RING_HOMOMORPHISM_0 RING_HOMOMORPHISM_1
   RING_HOMOMORPHISM_ADD RING_HOMOMORPHISM_MUL RING_HOMOMORPHISM_NEG RING_INV
   RING_MONOMORPHISM_EQ_0 RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_MUL RING_NEG
   RING_POW RING_SUB RING_SUM RING_SUM_CLAUSES RING_SUM_EQ RPOW_1_LE RPOW_ADD_LE
   RPOW_EQ_0 RPOW_LE2 RPOW_LT2 RPOW_LT_1 RPOW_MUL RPOW_ONE RPOW_POS_LE RPOW_POW
   RPOW_RPOW RPOW_ZERO SKOLEM_THM SUBSET SUBSET_REFL SUM_BOUND_LT absolute_value
   field_of_fractions lemma maximal_ideal nonarchimedean_absolute_value
   prime_ideal real_div ring_div ring_homomorphism ring_ideal ring_monomorphism
   rpow : thm)
  deriving Inhabited

/-- What absolute_values.ml uses from Session besides theorems. -/
structure AbsoluteValuesDeps where
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
/- absolute_values.ml phrases from line 72 to 615                         -/
/- ---------------------------------------------------------------------- -/

structure AbsoluteValues01 where
  -- @@FIELDS
  ABSOLUTE_VALUE_EQUIVALENT : thm
  ABSOLUTE_VALUE_EQUIVALENT_LE : thm
  ABSOLUTE_VALUE_EQUIVALENT_SYM : thm
  ABSOLUTE_VALUE_RPOW : thm
  NONARCHIMEDEAN_ABSOLUTE_VALUE_RPOW : thm
  ABSOLUTE_VALUE_POW_QUOTIENT : thm
  ABSOLUTE_VALUE_INEQUIVALENT_SEPARATE : thm
  ABSOLUTE_VALUE_INEQUIVALENT_DOMINANT : thm
  ABSOLUTE_VALUE_WEAK_APPROXIMATION : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupAbsoluteValues01 [HolBase] (D : AbsoluteValuesDeps) :
    ExceptT String IO AbsoluteValues01 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, REAL_ARITH, REAL_ARITH_TAC, REAL_FIELD,
        RING_CARRIER_TAC, RING_RULE, RING_TAC, .. } := D
  let { ABSOLUTE_VALUE_0, ABSOLUTE_VALUE_1, ABSOLUTE_VALUE_ABS_SUB_LE,
        ABSOLUTE_VALUE_DIV, ABSOLUTE_VALUE_INV, ABSOLUTE_VALUE_MUL, ABSOLUTE_VALUE_NEG,
        ABSOLUTE_VALUE_NONTRIVIAL, ABSOLUTE_VALUE_POS, ABSOLUTE_VALUE_POS_LT,
        ABSOLUTE_VALUE_POW, ABSOLUTE_VALUE_RING_SUM, ARCH_EVENTUALLY_POW, CARD_EQ_0,
        EVENTUALLY_AND, EVENTUALLY_FORALL, EVENTUALLY_HAPPENS_SEQUENTIALLY,
        EVENTUALLY_MONO, EVENTUALLY_TRUE, EXP_LOG, FIELD_MUL_RINV, FIELD_NONTRIVIAL,
        FINITE_DELETE, FINITE_INDUCT_STRONG, FORALL_IN_INSERT, IMP_CONJ, INSERT_DELETE,
        INSERT_SUBSET, IN_DELETE, LE_1, LOG_MONO_LT, LOG_MUL, LOG_POS_LT, LOG_POW,
        NONARCHIMEDEAN_ABSOLUTE_VALUE, NOT_FORALL_THM, NOT_IMP, NOT_IN_EMPTY,
        REAL_ARCH_POW, REAL_ARCH_POW_INV, REAL_INV_1_LT, REAL_INV_INV, REAL_INV_LT_1,
        REAL_LET_TRANS, REAL_LE_INV_EQ, REAL_LE_LMUL, REAL_LE_MAX, REAL_LE_RMUL,
        REAL_LE_TRANS, REAL_LTE_TRANS, .. } := D.core1
  let { REAL_LT_DIV, REAL_LT_IMP_LE, REAL_LT_IMP_NZ, REAL_LT_INV2, REAL_LT_INV_EQ,
        REAL_LT_LDIV_EQ, REAL_LT_LE, REAL_LT_LMUL, REAL_LT_RDIV_EQ, REAL_LT_TRANS,
        REAL_MAX_RPOW, REAL_MUL_LID, REAL_MUL_RID, REAL_MUL_RINV, REAL_MUL_SYM,
        REAL_NOT_LT, REAL_NUM_FRACTIONS_EQ, REAL_OF_NUM_LT, REAL_POS, REAL_POW_1,
        REAL_POW_1_LE, REAL_POW_EVENTUALLY_LT, REAL_POW_LE, REAL_POW_LE_1, REAL_POW_LT,
        REAL_POW_ONE, REAL_SUB_LT, RIGHT_IMP_EXISTS_THM, RING_0, RING_1, RING_ADD,
        RING_DIV, RING_INV, RING_MUL, RING_POW, RING_SUB, RING_SUM, RING_SUM_CLAUSES,
        RING_SUM_EQ, RPOW_1_LE, RPOW_ADD_LE, RPOW_EQ_0, RPOW_LE2, RPOW_LT2, RPOW_MUL,
        RPOW_ONE, RPOW_POS_LE, RPOW_POW, RPOW_RPOW, RPOW_ZERO, SKOLEM_THM, SUBSET,
        SUBSET_REFL, SUM_BOUND_LT, absolute_value, real_div, ring_div, rpow, .. } := D.core2
  -- @@SCOPE END

  let ABSOLUTE_VALUE_EQUIVALENT ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"&n * a / b = (&n * a) / b"
    let r2 ← REAL_ARITH q1
    let p3 ← prove r"!a b m n. &0 < b
               ==> (&n * a / b < &m <=> &n * a < &m * b) /\
                   (&m < &n * a / b <=> &m * b < &n * a)" (REPEAT STRIP_TAC THEN REWRITE_TAC [r2] THEN ASM_SIMP_TAC [REAL_LT_LDIV_EQ, REAL_LT_RDIV_EQ])
    let lemma := p3
    let q4 ← q r"&0 < log((f2:A->real) y)"
    let q5 ← q r"&0 < log((f1:A->real) y)"
    let q6 ← q r"(f1:A->real) y pow N"
    let q7 ← q r"inv((f1:A->real) z)"
    let q8 ← q r"(f1:A->real) z"
    let v9 ← ISPECL [q8, q7, q6] REAL_LT_LMUL
    let q10 ← q r"ring_mul k z (ring_pow k y N):A"
    let q11 ← q r"N:num"
    let q12 ← q r"inv((f1:A->real) z)"
    let q13 ← q r"(f1:A->real) y"
    let v14 ← ISPECL [q13, q12] REAL_ARCH_POW
    let q15 ← q r"log((f2:A->real) z) = s * log(f1 z)"
    let q16 ← q r"&0 < (f1:A->real) z /\ &0 < (f2:A->real) z /\
                &0 < (f1:A->real) y /\ &0 < (f2:A->real) y"
    let q17 ← q r"z:A = ring_0 k"
    let q18 ← q r"z:A"
    let q19 ← q r"(f2:A->real) z pow n = f2(ring_pow k z n) /\
       (f2:A->real) y pow m = f2(ring_pow k y m)"
    let q20 ← q r"n:num"
    let q21 ← q r"m:num"
    let v22 ← GSYM LOG_POW
    let q23 ← q r"&0 < (f1:A->real) z /\ &0 < (f2:A->real) z /\
                  &0 < (f1:A->real) y /\ &0 < (f2:A->real) y"
    let q24 ← q r"&1 < (f1:A->real) z"
    let q25 ← q r"~(z:A = ring_0 k)"
    let q26 ← q r"z:A"
    let q27 ← q r"!z:A. z IN ring_carrier k /\ &1 < f1 z
          ==> log(f2 z) / log(f2 y) = log(f1 z) / log(f1 y)"
    let q28 ← q r"s:real"
    let q29 ← q r"&0 < (s:real)"
    let q30 ← q r"s = log((f2:A->real) y) / log((f1:A->real) y)"
    let q31 ← q r"&0 < log((f1:A->real) y) /\ &0 < log((f2:A->real) y)"
    let q32 ← q r"&1 = (f2:A->real)(ring_1 k)"
    let q33 ← q r"&1 < (f2:A->real) y"
    let q34 ← q r"&1 < (f1:A->real) y"
    let q35 ← q r"~(y:A = ring_0 k)"
    let q36 ← q r"f1:A->real"
    let q37 ← q r"k:A ring"
    let v38 ← ISPECL [q37, q36] ABSOLUTE_VALUE_NONTRIVIAL
    let q39 ← q r"?y:A. y IN ring_carrier k /\ (&1:real) < f1 y"
    let q40 ← q r"ring_div k u v:A"
    let q41 ← q r"&0 < (f1:A->real) v /\ &0 < (f2:A->real) v"
    let q42 ← q r"(f1:A->real) u < f1 v"
    let q43 ← q r"~(v:A = ring_0 k)"
    let q44 ← q r"!u v:A. u IN ring_carrier k /\ v IN ring_carrier k /\
            (f1:A->real) u < f1 v
            ==> (f2:A->real) u < f2 v"
    let q45 ← q r"s:real"
    let v46 ← SPEC q45 RPOW_ONE
    let v47 ← GSYM v46
    let q48 ← q r"x:A"
    let q49 ← q r"s:real"
    prove
      r"!k (f1:A->real) f2.
          field k /\ absolute_value k f1 /\ absolute_value k f2 /\
          (?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ ~(f1 x = &1))
          ==> ((?s. &0 < s /\ !x. x IN ring_carrier k ==> f2 x = f1 x rpow s) <=>
               (!x. x IN ring_carrier k /\ f1 x < &1 ==> f2 x < &1))"
      (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nontriv")))) THEN EQ_TAC THENL [DISCH_THEN (X_CHOOSE_THEN q49 STRIP_ASSUME_TAC) THEN X_GEN_TAC q48 THEN STRIP_TAC THEN ASM_SIMP_TAC [] THEN GEN_REWRITE_TAC RAND_CONV [v47] THEN MATCH_MP_TAC RPOW_LT2 THEN ASM_MESON_TAC [ABSOLUTE_VALUE_POS], DISCH_TAC] THEN SUBGOAL_THEN q44 (LABEL_TAC "mono") THENL [REPEAT STRIP_TAC THEN SUBGOAL_THEN q43 ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC q42 THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_0, REAL_NOT_LT] THEN ASM_MESON_TAC [ABSOLUTE_VALUE_POS], ALL_TAC] THEN SUBGOAL_THEN q41 STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [ABSOLUTE_VALUE_POS_LT], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (SPEC q40)) THEN ASM_SIMP_TAC [RING_DIV, ABSOLUTE_VALUE_DIV, REAL_LT_LDIV_EQ, REAL_MUL_LID], ALL_TAC] THEN SUBGOAL_THEN q39 STRIP_ASSUME_TAC THENL [MP_TAC v38 THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN q35 ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC q34 THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_0] THEN REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN q33 ASSUME_TAC THENL [SUBGOAL_THEN q32 SUBST1_TAC THENL [ASM_SIMP_TAC [ABSOLUTE_VALUE_1, FIELD_NONTRIVIAL], ALL_TAC] THEN USE_THEN "mono" MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_1, ABSOLUTE_VALUE_1, FIELD_NONTRIVIAL], ALL_TAC] THEN SUBGOAL_THEN q31 STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [LOG_POS_LT], ALL_TAC] THEN ABBREV_TAC q30 THEN SUBGOAL_THEN q29 ASSUME_TAC THENL [EXPAND_TAC "s" THEN ASM_SIMP_TAC [REAL_LT_DIV], ALL_TAC] THEN EXISTS_TAC q28 THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN q27 (LABEL_TAC "key") THENL [X_GEN_TAC q26 THEN STRIP_TAC THEN SUBGOAL_THEN q25 ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC q24 THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_0] THEN REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN q23 STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [ABSOLUTE_VALUE_POS_LT], ALL_TAC] THEN MATCH_MP_TAC REAL_NUM_FRACTIONS_EQ THEN ASM_SIMP_TAC [REAL_LT_DIV, LOG_POS_LT, lemma] THEN ASM_SIMP_TAC [v22, LOG_MONO_LT, REAL_POW_LT] THEN CONJ_TAC THEN MAP_EVERY X_GEN_TAC [q21, q20] THEN DISCH_TAC THEN (SUBGOAL_THEN q19 (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_SIMP_TAC [ABSOLUTE_VALUE_POW, FIELD_NONTRIVIAL], ALL_TAC]) THEN USE_THEN "mono" MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_POW, ABSOLUTE_VALUE_POW, FIELD_NONTRIVIAL], ALL_TAC] THEN X_GEN_TAC q18 THEN DISCH_TAC THEN ASM_CASES_TAC q17 THENL [ASM_SIMP_TAC [ABSOLUTE_VALUE_0, RPOW_ZERO, REAL_LT_IMP_NZ], ALL_TAC] THEN SUBGOAL_THEN q16 STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [ABSOLUTE_VALUE_POS_LT], ALL_TAC] THEN ASM_SIMP_TAC [rpow] THEN SUBGOAL_THEN q15 (SUBST1_TAC o SYM) THENL [ALL_TAC, ASM_SIMP_TAC [EXP_LOG]] THEN MP_TAC v14 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC q11) THEN REMOVE_THEN "key" (MP_TAC o (SPEC q10)) THEN ASM_SIMP_TAC [RING_MUL, RING_POW, ABSOLUTE_VALUE_MUL, ABSOLUTE_VALUE_POW, FIELD_NONTRIVIAL] THEN ANTS_TAC THENL [MP_TAC v9 THEN ASM_SIMP_TAC [REAL_MUL_RINV, REAL_LT_IMP_NZ], ALL_TAC] THEN ASM_SIMP_TAC [LOG_MUL, REAL_POW_LT, LOG_POW] THEN EXPAND_TAC "s" THEN UNDISCH_TAC q5 THEN UNDISCH_TAC q4 THEN CONV_TAC REAL_FIELD)

  let ABSOLUTE_VALUE_EQUIVALENT_LE ← prove
    r"!k (f1:A->real) f2.
        field k /\ absolute_value k f1 /\ absolute_value k f2 /\
        (?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ ~(f1 x = &1)) /\
        (?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ ~(f2 x = &1))
        ==> ((?s. &0 < s /\ !x. x IN ring_carrier k ==> f2 x = f1 x rpow s) <=>
             (!x. x IN ring_carrier k /\ f1 x <= &1 ==> f2 x <= &1))"
    (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nt2"))))) THEN EQ_TAC THENL [DISCH_THEN (X_CHOOSE_THEN (← q r"s:real") STRIP_ASSUME_TAC) THEN X_GEN_TAC (← q r"x:A") THEN STRIP_TAC THEN ASM_SIMP_TAC [] THEN MATCH_MP_TAC RPOW_1_LE THEN ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN ASM_MESON_TAC [ABSOLUTE_VALUE_POS], DISCH_THEN (LABEL_TAC "le")] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"f1:A->real"), (← q r"f2:A->real")] ABSOLUTE_VALUE_EQUIVALENT) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN X_GEN_TAC (← q r"x:A") THEN STRIP_TAC THEN REWRITE_TAC [REAL_LT_LE] THEN CONJ_TAC THENL [USE_THEN "le" MATCH_MP_TAC THEN ASM_SIMP_TAC [REAL_LT_IMP_LE], DISCH_TAC] THEN SUBGOAL_THEN (← q r"~(x:A = ring_0 k)") ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC (← q r"(f2:A->real) x = &1") THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_0] THEN REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"!z:A. z IN ring_carrier k ==> (f2:A->real) z <= &1") (LABEL_TAC "bd") THENL [X_GEN_TAC (← q r"z:A") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"z:A = ring_0 k") THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_0, REAL_POS] THEN SUBGOAL_THEN (← q r"&0 < (f1:A->real) z") ASSUME_TAC THENL [ASM_MESON_TAC [ABSOLUTE_VALUE_POS_LT], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"(f1:A->real) x"), (← q r"inv((f1:A->real) z)")] REAL_ARCH_POW_INV) THEN ASM_REWRITE_TAC [REAL_LT_INV_EQ] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"n:num")) THEN REMOVE_THEN "le" (MP_TAC o (SPEC (← q r"ring_mul k (ring_pow k x n) z:A"))) THEN ASM_SIMP_TAC [RING_MUL, RING_POW, ABSOLUTE_VALUE_MUL, ABSOLUTE_VALUE_POW, FIELD_NONTRIVIAL, REAL_POW_ONE, REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN MP_TAC (← ISPECL [(← q r"(f1:A->real) z"), (← q r"(f1:A->real) x pow n"), (← q r"inv((f1:A->real) z)")] REAL_LT_LMUL) THEN ASM_SIMP_TAC [REAL_MUL_RINV, REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC, ALL_TAC] THEN REMOVE_THEN "nt2" (X_CHOOSE_THEN (← q r"w:A") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(f2:A->real) w <= &1 /\ inv((f2:A->real) w) <= &1 /\ &0 < f2 w") STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THENL [ASM_SIMP_TAC [], REMOVE_THEN "bd" (MP_TAC o (SPEC (← q r"ring_inv k w:A"))) THEN ASM_SIMP_TAC [RING_INV, ABSOLUTE_VALUE_INV], ASM_MESON_TAC [ABSOLUTE_VALUE_POS_LT]], ALL_TAC] THEN SUBGOAL_THEN (← q r"&1 <= (f2:A->real) w") MP_TAC THENL [MP_TAC (← ISPECL [(← q r"(f2:A->real) w"), (← q r"inv((f2:A->real) w)"), (← q r"(&1:real)")] REAL_LE_LMUL) THEN ASM_SIMP_TAC [REAL_MUL_RINV, REAL_LT_IMP_NZ, REAL_LT_IMP_LE, REAL_MUL_RID], ASM_REAL_ARITH_TAC])

  let ABSOLUTE_VALUE_EQUIVALENT_SYM ← prove
    r"!k (f1:A->real) f2.
        absolute_value k f1 /\
        (?s. &0 < s /\ !x. x IN ring_carrier k ==> f2 x = f1 x rpow s)
        ==> ?s. &0 < s /\ !x. x IN ring_carrier k ==> f1 x = f2 x rpow s"
    (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"s:real") STRIP_ASSUME_TAC)) THEN EXISTS_TAC (← q r"inv s:real") THEN ASM_SIMP_TAC [REAL_LT_INV_EQ] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"&0 <= (f1:A->real) x") ASSUME_TAC THENL [ASM_MESON_TAC [ABSOLUTE_VALUE_POS], ALL_TAC] THEN ASM_SIMP_TAC [RPOW_RPOW, REAL_MUL_RINV, REAL_LT_IMP_NZ] THEN REWRITE_TAC [RPOW_POW, REAL_POW_1])

  let ABSOLUTE_VALUE_RPOW ← prove
    r"!k (f:A->real) s.
        absolute_value k f /\ &0 < s /\ s <= &1
        ==> absolute_value k (\x. f x rpow s)"
    (REPEAT GEN_TAC THEN REWRITE_TAC [absolute_value] THEN STRIP_TAC THEN ASM_SIMP_TAC [RPOW_POS_LE, RPOW_EQ_0, REAL_LT_IMP_NZ, RPOW_MUL] THEN MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"y:A")] THEN STRIP_TAC THEN TRANS_TAC REAL_LE_TRANS (← q r"((f:A->real) x + f y) rpow s") THEN CONJ_TAC THENL [MATCH_MP_TAC RPOW_LE2 THEN ASM_SIMP_TAC [REAL_LT_IMP_LE, RING_ADD], MATCH_MP_TAC RPOW_ADD_LE THEN ASM_SIMP_TAC []])

  let NONARCHIMEDEAN_ABSOLUTE_VALUE_RPOW ← prove
    r"!k (f:A->real) s.
        nonarchimedean_absolute_value k f /\ &0 < s
        ==> nonarchimedean_absolute_value k (\x. f x rpow s)"
    (REPEAT GEN_TAC THEN REWRITE_TAC [NONARCHIMEDEAN_ABSOLUTE_VALUE] THEN STRIP_TAC THEN ASM_SIMP_TAC [RPOW_POS_LE, RPOW_EQ_0, REAL_LT_IMP_NZ, RPOW_MUL] THEN MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"y:A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"max ((f:A->real) x rpow s) (f y rpow s) = (max (f x) (f y)) rpow s") SUBST1_TAC THENL [MATCH_MP_TAC REAL_MAX_RPOW THEN ASM_SIMP_TAC [REAL_LT_IMP_LE], ALL_TAC] THEN MATCH_MP_TAC RPOW_LE2 THEN ASM_SIMP_TAC [REAL_LT_IMP_LE, RING_ADD] THEN ASM_SIMP_TAC [REAL_LE_MAX, RING_ADD])

  let ABSOLUTE_VALUE_POW_QUOTIENT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"&0 < (e:real) ==> &0 < &1 + e")
    let r2 ← REAL_ARITH (← q r"&0 < (e:real) ==> &0 < &1 + e")
    let r3 ← REAL_ARITH (← q r"&0 < (e:real) ==> &0 < &1 + e")
    let r4 ← RING_RULE (← q r"ring_sub k (ring_add k (ring_1 k) x) x = ring_1 k /\
      ring_sub k (ring_add k (ring_1 k) x) (ring_1 k) = (x:A)")
    prove
      r"!k (f:A->real) y.
          field k /\ absolute_value k f /\ y IN ring_carrier k
          ==> (f y < &1
               ==> !e. &0 < e
                       ==> eventually
                            (\m. f(ring_div k (ring_pow k y m)
                                    (ring_add k (ring_1 k) (ring_pow k y m)))
                                 < e) sequentially) /\
              (&1 < f y
               ==> !e. &0 < e
                       ==> eventually
                            (\m. f(ring_sub k
                                    (ring_div k (ring_pow k y m)
                                      (ring_add k (ring_1 k) (ring_pow k y m)))
                                    (ring_1 k)) < e) sequentially)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"&0 <= (f:A->real) y") ASSUME_TAC THENL [ASM_MESON_TAC [ABSOLUTE_VALUE_POS], ALL_TAC] THEN SUBGOAL_THEN (← q r"!m. (f:A->real) y pow m - &1 <=
          f(ring_add k (ring_1 k) (ring_pow k y m)) /\
          &1 - f y pow m <= f(ring_add k (ring_1 k) (ring_pow k y m))") (LABEL_TAC "D") THENL [GEN_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"f:A->real"), (← q r"ring_add k (ring_1 k) (ring_pow k y m):A"), (← q r"ring_pow k y m:A")] ABSOLUTE_VALUE_ABS_SUB_LE) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"f:A->real"), (← q r"ring_add k (ring_1 k) (ring_pow k y m):A"), (← q r"ring_1 k:A")] ABSOLUTE_VALUE_ABS_SUB_LE) THEN ASM_SIMP_TAC [RING_ADD, RING_1, RING_POW] THEN ASM_SIMP_TAC [r4, RING_POW, ABSOLUTE_VALUE_1, ABSOLUTE_VALUE_POW, FIELD_NONTRIVIAL] THEN REAL_ARITH_TAC, ALL_TAC] THEN CONJ_TAC THEN DISCH_TAC THEN X_GEN_TAC (← q r"e:real") THEN DISCH_TAC THENL [MP_TAC (← ISPECL [(← q r"(f:A->real) y"), (← q r"e / (&1 + e)")] REAL_POW_EVENTUALLY_LT) THEN ASM_SIMP_TAC [REAL_LT_DIV, r3] THEN MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] EVENTUALLY_MONO) THEN X_GEN_TAC (← q r"m:num") THEN REWRITE_TAC [] THEN DISCH_TAC THEN REMOVE_THEN "D" (MP_TAC o (CONJUNCT2 o (SPEC (← q r"m:num")))) THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_DIV, RING_POW, RING_ADD, RING_1, ABSOLUTE_VALUE_POW, FIELD_NONTRIVIAL] THEN ABBREV_TAC (← q r"D = (f:A->real)(ring_add k (ring_1 k) (ring_pow k y m))") THEN ABBREV_TAC (← q r"u = (f:A->real) y pow m") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"&0 <= (u:real) /\ u * (&1 + e) < e") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [EXPAND_TAC "u" THEN ASM_SIMP_TAC [REAL_POW_LE], ALL_TAC] THEN UNDISCH_TAC (← q r"u < e / (&1 + e)") THEN ASM_SIMP_TAC [REAL_LT_RDIV_EQ, r2], ALL_TAC] THEN SUBGOAL_THEN (← q r"e * (&1 - (u:real)) <= e * D") ASSUME_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"(u:real) < &1") ASSUME_TAC THENL [TRANS_TAC REAL_LT_TRANS (← q r"e / (&1 + e)") THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [REAL_LT_LDIV_EQ, r1] THEN REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"&0 < (D:real)") ASSUME_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN ASM_SIMP_TAC [REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"(f:A->real) y"), (← q r"&1 + inv e")] ARCH_EVENTUALLY_POW) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] EVENTUALLY_MONO) THEN X_GEN_TAC (← q r"m:num") THEN REWRITE_TAC [] THEN DISCH_TAC THEN REMOVE_THEN "D" (MP_TAC o (CONJUNCT1 o (SPEC (← q r"m:num")))) THEN ABBREV_TAC (← q r"b = ring_add k (ring_1 k) (ring_pow k y m):A") THEN SUBGOAL_THEN (← q r"(b:A) IN ring_carrier k") ASSUME_TAC THENL [EXPAND_TAC "b" THEN ASM_SIMP_TAC [RING_ADD, RING_1, RING_POW], ALL_TAC] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"inv e < (f:A->real) b") ASSUME_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"~(b:A = ring_0 k)") ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC (← q r"inv e < (f:A->real) b") THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_0, REAL_NOT_LT, REAL_LE_INV_EQ, REAL_LT_IMP_LE], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sub k (ring_div k (ring_pow k y m) b) (ring_1 k) =
      ring_neg k (ring_inv k b):A") SUBST1_TAC THENL [REWRITE_TAC [ring_div] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"b:A")] FIELD_MUL_RINV) THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"ring_add k (ring_1 k) (ring_pow k y m):A = b") THEN SUBGOAL_THEN (← q r"ring_pow k y m:A IN ring_carrier k /\
                    ring_inv k b:A IN ring_carrier k") MP_TAC THENL [ASM_SIMP_TAC [RING_POW, RING_INV], ALL_TAC] THEN SPEC_TAC ((← q r"ring_pow k y m:A"), (← q r"a:A")) THEN SPEC_TAC ((← q r"ring_inv k b:A"), (← q r"c:A")) THEN UNDISCH_TAC (← q r"(b:A) IN ring_carrier k") THEN SPEC_TAC ((← q r"b:A"), (← q r"b:A")) THEN RING_TAC, ALL_TAC] THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_NEG, RING_INV, ABSOLUTE_VALUE_INV] THEN GEN_REWRITE_TAC RAND_CONV [(← GSYM REAL_INV_INV)] THEN MATCH_MP_TAC REAL_LT_INV2 THEN ASM_SIMP_TAC [REAL_LT_INV_EQ])

  let ABSOLUTE_VALUE_INEQUIVALENT_SEPARATE ← prove
    r"!k (f1:A->real) f2.
        field k /\ absolute_value k f1 /\ absolute_value k f2 /\
        (?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ ~(f1 x = &1)) /\
        (?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ ~(f2 x = &1)) /\
        ~(?s. &0 < s /\ !x. x IN ring_carrier k ==> f2 x = f1 x rpow s)
        ==> ?z. z IN ring_carrier k /\ &1 < f1 z /\ f2 z < &1"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"~(?s. &0 < s /\ !x. x IN ring_carrier k ==> f1 x = (f2:A->real) x rpow s)") ASSUME_TAC THENL [ASM_MESON_TAC [ABSOLUTE_VALUE_EQUIVALENT_SYM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"f1:A->real"), (← q r"f2:A->real")] ABSOLUTE_VALUE_EQUIVALENT) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"f2:A->real"), (← q r"f1:A->real")] ABSOLUTE_VALUE_EQUIVALENT) THEN ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN DISCH_THEN (fun th => RULE_ASSUM_TAC (REWRITE_RULE [th])) THEN ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN DISCH_THEN (fun th => RULE_ASSUM_TAC (REWRITE_RULE [th])) THEN RULE_ASSUM_TAC (REWRITE_RULE [NOT_FORALL_THM, NOT_IMP, REAL_NOT_LT]) THEN SUBGOAL_THEN (← q r"?a:A. a IN ring_carrier k /\ (f1:A->real) a < &1 /\ &1 <= (f2:A->real) a") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"?b:A. b IN ring_carrier k /\ (f2:A->real) b < &1 /\ &1 <= (f1:A->real) b") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(a:A = ring_0 k)") ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC (← q r"&1 <= (f2:A->real) a") THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_0] THEN REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"&0 < (f1:A->real) a /\ &0 < (f2:A->real) a") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [ABSOLUTE_VALUE_POS_LT], ALL_TAC] THEN EXISTS_TAC (← q r"ring_div k b a:A") THEN ASM_SIMP_TAC [RING_DIV, ABSOLUTE_VALUE_DIV, REAL_LT_LDIV_EQ, REAL_LT_RDIV_EQ, REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC)

  let ABSOLUTE_VALUE_INEQUIVALENT_DOMINANT ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"s:K->bool = {}"
    let p2 ← prove r"!net (p:K->A->bool) s.
        FINITE s
        ==> (eventually (\x. !a. a IN s ==> p a x) net <=>
             !a. a IN s ==> eventually (p a) net)" (REPEAT STRIP_TAC THEN ASM_CASES_TAC q1 THEN ASM_SIMP_TAC [EVENTUALLY_FORALL, NOT_IN_EMPTY, EVENTUALLY_TRUE])
    let EVENTUALLY_FORALL_FINITE := p2
    let v3 ← GSYM REAL_MUL_LID
    let q4 ← q r"b:real"
    let v5 ← GSYM REAL_MUL_LID
    let q6 ← q r"b:real"
    let q7 ← q r"&0 <= (a:real) ==> &0 < a + &1"
    let r8 ← REAL_ARITH q7
    let v9 ← GSYM real_div
    let q10 ← q r"a * inv(a + &1)"
    let q11 ← q r"inv a:real"
    let q12 ← q r"b:real"
    let q13 ← q r"a:real"
    let v14 ← ISPECL [q13, q12, q11] REAL_LT_LMUL
    let q15 ← q r"b:real"
    let q16 ← q r"inv a:real"
    let q17 ← q r"a:real"
    let v18 ← ISPECL [q17, q16, q15] REAL_LT_LMUL
    let p19 ← prove r"(!a b:real. &0 < a /\ inv a < b ==> &1 < a * b) /\
     (!a b:real. &0 < a /\ &0 <= b /\ b < inv a ==> a * b < &1) /\
     (!a b:real. &0 <= a /\ &0 <= b /\ b < inv(a + &1) ==> a * b < &1) /\
     (!a b:real. &1 <= a /\ &1 < b ==> &1 < a * b) /\
     (!a b:real. &0 <= a /\ a <= &1 /\ &0 <= b /\ b < &1 ==> a * b < &1)" (REPEAT STRIP_TAC THENL [MP_TAC v18 THEN ASM_SIMP_TAC [REAL_MUL_RINV, REAL_LT_IMP_NZ], MP_TAC v14 THEN ASM_SIMP_TAC [REAL_MUL_RINV, REAL_LT_IMP_NZ], TRANS_TAC REAL_LET_TRANS q10 THEN CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC [REAL_LT_IMP_LE], REWRITE_TAC [v9] THEN ASM_SIMP_TAC [REAL_LT_LDIV_EQ, r8] THEN REAL_ARITH_TAC], TRANS_TAC REAL_LTE_TRANS q6 THEN ASM_REWRITE_TAC [] THEN GEN_REWRITE_TAC LAND_CONV [v5] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC, TRANS_TAC REAL_LET_TRANS q4 THEN ASM_REWRITE_TAC [] THEN GEN_REWRITE_TAC RAND_CONV [v3] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC])
    let RLEMMA := p19
    let q22 ← q r"l:K"
    let q23 ← q r"(f:K->A->real) j"
    let q26 ← q r"(f:K->A->real) i"
    let q29 ← q r"ring_1 k:A"
    let q30 ← q r"(q:num->A) m"
    let q31 ← q r"g:A->real"
    let q32 ← q r"k:A ring"
    let v33 ← ISPECL [q32, q31, q30, q29] ABSOLUTE_VALUE_ABS_SUB_LE
    let q34 ← q r"g:A->real"
    let q35 ← q r"!g:A->real. absolute_value k g
                ==> &1 - g(ring_sub k (q m) (ring_1 k)) <= g((q:num->A) m) /\
                    g(q m) <= &1 + g(ring_sub k (q m) (ring_1 k))"
    let q36 ← q r"ring_mul k w ((q:num->A) m)"
    let q37 ← q r"m:num"
    let q38 ← q r"&0 <= (a:real) ==> &0 < a + &1"
    let r39 ← REAL_ARITH q38
    let q40 ← q r"y:A"
    let q41 ← q r"(f:K->A->real) l"
    let q42 ← q r"k:A ring"
    let v43 ← ISPECL [q42, q41, q40] ABSOLUTE_VALUE_POW_QUOTIENT
    let q44 ← q r"l:K"
    let q45 ← q r"y:A"
    let q46 ← q r"(f:K->A->real) j"
    let q47 ← q r"k:A ring"
    let v48 ← ISPECL [q47, q46, q45] ABSOLUTE_VALUE_POW_QUOTIENT
    let q49 ← q r"y:A"
    let q50 ← q r"(f:K->A->real) i"
    let q51 ← q r"k:A ring"
    let v52 ← ISPECL [q51, q50, q49] ABSOLUTE_VALUE_POW_QUOTIENT
    let q53 ← q r"eventually
     (\m. (f:K->A->real) i (ring_sub k (q m) (ring_1 k)) <
          &1 - inv(f i w) /\
          f j (ring_sub k (q m) (ring_1 k)) < inv(f j w) - &1 /\
          !l. l IN t ==> f l (q m) < inv(f l w + &1))
     sequentially"
    let q54 ← q r"!m. (q:num->A) m IN ring_carrier k"
    let q55 ← q r"q = \m. ring_div k (ring_pow k y m)
              (ring_add k (ring_1 k) (ring_pow k y m)):A"
    let q60 ← q r"ring_mul k (ring_pow k y m) w:A"
    let q61 ← q r"m:num"
    let q64 ← q r"m:num"
    let v65 ← REWRITE_RULE [IMP_CONJ] EVENTUALLY_MONO
    let q66 ← q r"&0 <= (a:real) ==> &0 < a + &1"
    let r67 ← REAL_ARITH q66
    let q68 ← q r"inv((f:K->A->real) l w + &1)"
    let q69 ← q r"(f:K->A->real) l y"
    let v70 ← ISPECL [q69, q68] REAL_POW_EVENTUALLY_LT
    let q71 ← q r"l:K"
    let q72 ← q r"eventually (\m. !l. l IN t
                    ==> (f:K->A->real) l y pow m * f l w < &1)
                 sequentially"
    let q73 ← q r"(f:K->A->real) j y <= &1 \/ &1 < f j y"
    let r74 ← REAL_ARITH q73
    let q75 ← q r"&0 < (f:K->A->real) j w /\ &0 <= (f:K->A->real) i y /\
    &0 <= (f:K->A->real) j y /\
    !l. l IN t ==> &0 <= (f:K->A->real) l w /\ &0 <= f l y"
    let q76 ← q r"&1 < (f:K->A->real) i w"
    let q77 ← q r"~(w:A = ring_0 k)"
    let q78 ← q r"t SUBSET (s:K->bool) DELETE i"
    let q79 ← q r"!l. l IN t ==> absolute_value k ((f:K->A->real) l)"
    let q80 ← q r"w:A"
    let q81 ← q r"(f:K->A->real) j"
    let q82 ← q r"(f:K->A->real) i"
    let q83 ← q r"k:A ring"
    let v84 ← ISPECL [q83, q82, q81] ABSOLUTE_VALUE_INEQUIVALENT_SEPARATE
    let q85 ← q r"absolute_value k ((f:K->A->real) i) /\ absolute_value k (f j)"
    let q86 ← q r"y:A"
    let q87 ← q r"t:K->bool"
    let q88 ← q r"j:K"
    let q89 ← q r"(f:K->A->real) i"
    let q90 ← q r"k:A ring"
    let v91 ← ISPECL [q90, q89] ABSOLUTE_VALUE_NONTRIVIAL
    let q92 ← q r"s DELETE (i:K)"
    let q93 ← q r"!t. FINITE t
        ==> t SUBSET s DELETE i
            ==> ?z. z IN ring_carrier k /\ &1 < (f:K->A->real) i z /\
                    !j. j IN t ==> f j z < &1"
    prove
      r"!k (f:K->A->real) s i.
          field k /\ FINITE s /\ i IN s /\
          (!j. j IN s
               ==> absolute_value k (f j) /\
                   ?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ ~(f j x = &1)) /\
          (!j. j IN s /\ ~(j = i)
               ==> ~(?c. &0 < c /\
                         !x. x IN ring_carrier k ==> f j x = f i x rpow c))
          ==> ?z. z IN ring_carrier k /\ &1 < f i z /\
                  !j. j IN s /\ ~(j = i) ==> f j z < &1"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN q93 (MP_TAC o (SPEC q92)) THENL [ALL_TAC, ASM_SIMP_TAC [FINITE_DELETE, SUBSET_REFL, IN_DELETE]] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL [DISCH_TAC THEN REWRITE_TAC [NOT_IN_EMPTY] THEN MP_TAC v91 THEN ASM_SIMP_TAC [] THEN DISCH_THEN (SUBST1_TAC o (SYM o CONJUNCT1)) THEN ASM_SIMP_TAC [], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [q88, q87] THEN REWRITE_TAC [INSERT_SUBSET, IN_DELETE] THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN STRIP_TAC THEN REMOVE_THEN "ih" MP_TAC THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN q86 STRIP_ASSUME_TAC) THEN REWRITE_TAC [FORALL_IN_INSERT] THEN SUBGOAL_THEN q85 STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN MP_TAC v84 THEN ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN q80 STRIP_ASSUME_TAC) THEN SUBGOAL_THEN q79 ASSUME_TAC THENL [UNDISCH_TAC q78 THEN REWRITE_TAC [SUBSET, IN_DELETE] THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN q77 ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC q76 THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_0] THEN REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN q75 STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THENL [ASM_MESON_TAC [ABSOLUTE_VALUE_POS_LT], ASM_MESON_TAC [ABSOLUTE_VALUE_POS], ASM_MESON_TAC [ABSOLUTE_VALUE_POS], ASM_MESON_TAC [ABSOLUTE_VALUE_POS]], ALL_TAC] THEN DISJ_CASES_TAC r74 THENL [SUBGOAL_THEN q72 MP_TAC THENL [ASM_SIMP_TAC [EVENTUALLY_FORALL_FINITE] THEN X_GEN_TAC q71 THEN DISCH_TAC THEN MP_TAC v70 THEN ASM_SIMP_TAC [REAL_LT_INV_EQ, r67] THEN MATCH_MP_TAC v65 THEN X_GEN_TAC q64 THEN REWRITE_TAC [] THEN DISCH_TAC THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN MATCH_MP_TAC (← (do let z62 ← (pure (CONJUNCTS RLEMMA)); let z63 ← (pure 2); liftExcept (el z63 z62))) THEN ASM_SIMP_TAC [REAL_POW_LE], ALL_TAC] THEN DISCH_THEN ((X_CHOOSE_TAC q61) o (BETA_RULE o (MATCH_MP EVENTUALLY_HAPPENS_SEQUENTIALLY))) THEN EXISTS_TAC q60 THEN ASM_SIMP_TAC [RING_MUL, RING_POW, ABSOLUTE_VALUE_MUL, ABSOLUTE_VALUE_POW, FIELD_NONTRIVIAL] THEN CONJ_TAC THENL [MATCH_MP_TAC (← (do let z58 ← (pure (CONJUNCTS RLEMMA)); let z59 ← (pure 3); liftExcept (el z59 z58))) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_SIMP_TAC [REAL_LT_IMP_LE], MATCH_MP_TAC (← (do let z56 ← (pure (CONJUNCTS RLEMMA)); let z57 ← (pure 4); liftExcept (el z57 z56))) THEN ASM_SIMP_TAC [REAL_POW_LE, REAL_LT_IMP_LE, REAL_POW_1_LE]], ALL_TAC] THEN ABBREV_TAC q55 THEN SUBGOAL_THEN q54 ASSUME_TAC THENL [EXPAND_TAC "q" THEN ASM_SIMP_TAC [RING_DIV, RING_ADD, RING_1, RING_POW], ALL_TAC] THEN SUBGOAL_THEN q53 MP_TAC THENL [REWRITE_TAC [EVENTUALLY_AND] THEN ASM_SIMP_TAC [EVENTUALLY_FORALL_FINITE] THEN EXPAND_TAC "q" THEN REPEAT CONJ_TAC THENL [MP_TAC v52 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MATCH_MP_TAC o CONJUNCT2) THEN ASM_SIMP_TAC [REAL_SUB_LT, REAL_INV_LT_1], MP_TAC v48 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MATCH_MP_TAC o CONJUNCT2) THEN ASM_SIMP_TAC [REAL_SUB_LT, REAL_INV_1_LT], X_GEN_TAC q44 THEN DISCH_TAC THEN MP_TAC v43 THEN ASM_SIMP_TAC [] THEN DISCH_THEN (MATCH_MP_TAC o CONJUNCT1) THEN ASM_SIMP_TAC [REAL_LT_INV_EQ, r39]], ALL_TAC] THEN DISCH_THEN ((X_CHOOSE_THEN q37 STRIP_ASSUME_TAC) o (MATCH_MP EVENTUALLY_HAPPENS_SEQUENTIALLY)) THEN EXISTS_TAC q36 THEN ASM_SIMP_TAC [RING_MUL, ABSOLUTE_VALUE_MUL] THEN SUBGOAL_THEN q35 ASSUME_TAC THENL [X_GEN_TAC q34 THEN DISCH_TAC THEN MP_TAC v33 THEN ASM_SIMP_TAC [RING_1, ABSOLUTE_VALUE_1, FIELD_NONTRIVIAL] THEN REAL_ARITH_TAC, ALL_TAC] THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC (← (do let z27 ← (pure (CONJUNCTS RLEMMA)); let z28 ← (pure 0); liftExcept (el z28 z27))) THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (SPEC q26)) THEN ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC, MATCH_MP_TAC (← (do let z24 ← (pure (CONJUNCTS RLEMMA)); let z25 ← (pure 1); liftExcept (el z25 z24))) THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ASM_MESON_TAC [ABSOLUTE_VALUE_POS], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (SPEC q23)) THEN ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC, X_GEN_TAC q22 THEN DISCH_TAC THEN MATCH_MP_TAC (← (do let z20 ← (pure (CONJUNCTS RLEMMA)); let z21 ← (pure 2); liftExcept (el z21 z20))) THEN ASM_SIMP_TAC [] THEN ASM_MESON_TAC [ABSOLUTE_VALUE_POS]])

  let ABSOLUTE_VALUE_WEAK_APPROXIMATION ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"&0 <= (a:real) ==> &0 < a + &1"
    let r2 ← REAL_ARITH q1
    let q3 ← q r"b < d / (a + &1)"
    let p4 ← prove r"!a b d. &0 <= a /\ &0 <= b /\ &0 < d /\ b < d / (a + &1)
             ==> a * b < d" (REPEAT STRIP_TAC THEN UNDISCH_TAC q3 THEN ASM_SIMP_TAC [REAL_LT_RDIV_EQ, r2] THEN ASM_REAL_ARITH_TAC)
    let RLEMMA := p4
    let q5 ← q r"i:K"
    let q6 ← q r"&(CARD(s:K->bool)) * (d:real) = e"
    let v7 ← ASSUME q6
    let v8 ← SYM v7
    let q9 ← q r"s:K->bool"
    let q10 ← q r"\j. (c:K->K->num->A) i j m"
    let q11 ← q r"(f:K->A->real) i"
    let q12 ← q r"k:A ring"
    let v13 ← ISPECL [q12, q11, q10, q9] ABSOLUTE_VALUE_RING_SUM
    let v14 ← BETA_RULE v13
    let q15 ← q r"sum s (\j. (f:K->A->real) i ((c:K->K->num->A) i j m))"
    let q16 ← q r"!j. j IN s ==> (c:K->K->num->A) i j m IN ring_carrier k"
    let q17 ← q r"w:A"
    let q18 ← q r"(q:K->num->A) i m"
    let q19 ← q r"v:A"
    let q20 ← q r"(a:K->A) i"
    let q21 ← q r"u:A"
    let q22 ← q r"ring_sum k (s DELETE i)
               (\j. ring_mul k ((a:K->A) j) ((q:K->num->A) j m))"
    let q23 ← q r"ring_sum k (s DELETE i) (\j. ring_mul k ((a:K->A) j) ((q:K->num->A) j m))
      IN ring_carrier k /\ (a:K->A) i IN ring_carrier k /\
      (q:K->num->A) i m IN ring_carrier k"
    let q24 ← q r"ring_sum k (s DELETE i)
       (\j. if j = i
            then ring_mul k ((a:K->A) i)
                   (ring_sub k ((q:K->num->A) i m) (ring_1 k))
            else ring_mul k (a j) (q j m)) =
      ring_sum k (s DELETE i) (\j. ring_mul k (a j) (q j m))"
    let q25 ← q r"s = (i:K) INSERT (s DELETE i)"
    let q26 ← q r"ring_sub k (ring_sum k s (\j. ring_mul k ((a:K->A) j) ((q:K->num->A) j m)))
               (a i) =
    ring_sum k s (\j. (c:K->K->num->A) i j m)"
    let q27 ← q r"i:K"
    let q28 ← q r"ring_sum k s (\j. ring_mul k ((a:K->A) j) ((q:K->num->A) j m))"
    let q29 ← q r"m:num"
    let q30 ← q r"ring_div k (ring_pow k ((z:K->A) j) m)
          (ring_add k (ring_1 k) (ring_pow k (z j) m)) IN ring_carrier k"
    let q31 ← q r"m:num"
    let v32 ← REWRITE_RULE [IMP_CONJ] EVENTUALLY_MONO
    let q33 ← q r"&0 <= (a:real) ==> &0 < a + &1"
    let r34 ← REAL_ARITH q33
    let q35 ← q r"d / ((f:K->A->real) i ((a:K->A) j) + &1)"
    let q36 ← q r"(z:K->A) j"
    let q37 ← q r"(f:K->A->real) i"
    let q38 ← q r"k:A ring"
    let v39 ← ISPECL [q38, q37, q36] ABSOLUTE_VALUE_POW_QUOTIENT
    let q40 ← q r"ring_sub k (ring_div k (ring_pow k ((z:K->A) i) m)
                      (ring_add k (ring_1 k) (ring_pow k (z i) m)))
                   (ring_1 k) IN ring_carrier k"
    let q41 ← q r"m:num"
    let v42 ← REWRITE_RULE [IMP_CONJ] EVENTUALLY_MONO
    let q43 ← q r"&0 <= (a:real) ==> &0 < a + &1"
    let r44 ← REAL_ARITH q43
    let q45 ← q r"d / ((f:K->A->real) i (a i) + &1)"
    let q46 ← q r"(z:K->A) i"
    let q47 ← q r"(f:K->A->real) i"
    let q48 ← q r"k:A ring"
    let v49 ← ISPECL [q48, q47, q46] ABSOLUTE_VALUE_POW_QUOTIENT
    let q50 ← q r"j:K = i"
    let q51 ← q r"&0 <= (f:K->A->real) i (a i) /\ &0 <= f i (a j)"
    let q52 ← q r"(z:K->A) i IN ring_carrier k /\ (z:K->A) j IN ring_carrier k"
    let q53 ← q r"absolute_value k ((f:K->A->real) i)"
    let q54 ← q r"j:K"
    let q55 ← q r"i:K"
    let q56 ← q r"eventually (\m. !i. i IN s ==> !j. j IN s
                    ==> (f:K->A->real) i ((c:K->K->num->A) i j m) < d)
               sequentially"
    let q57 ← q r"c = \i j m. if j = i
                then ring_mul k ((a:K->A) i)
                       (ring_sub k ((q:K->num->A) i m) (ring_1 k))
                else ring_mul k (a j) (q j m)"
    let q58 ← q r"(&0:real) < &(CARD(s:K->bool))"
    let q59 ← q r"(&0:real) < &(CARD(s:K->bool))"
    let q60 ← q r"&0 < (d:real) /\ &(CARD(s:K->bool)) * d = e"
    let q61 ← q r"d = e / &(CARD(s:K->bool))"
    let q62 ← q r"!i m. i IN s ==> (q:K->num->A) i m IN ring_carrier k"
    let q63 ← q r"q = \i m. ring_div k (ring_pow k ((z:K->A) i) m)
                (ring_add k (ring_1 k) (ring_pow k (z i) m))"
    let q64 ← q r"z:K->A"
    let q65 ← q r"j:K"
    let q66 ← q r"i:K"
    let q67 ← q r"!i. i IN s
        ==> ?z. z IN ring_carrier k /\ &1 < (f:K->A->real) i z /\
                !j. j IN s /\ ~(j = i) ==> f j z < &1"
    let q68 ← q r"ring_0 k:A"
    let q69 ← q r"s:K->bool = {}"
    prove
      r"!k (f:K->A->real) a s e.
          field k /\ FINITE s /\
          (!i. i IN s
               ==> absolute_value k (f i) /\
                   ?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ ~(f i x = &1)) /\
          (!i j. i IN s /\ j IN s /\ ~(i = j)
                 ==> ~(?c. &0 < c /\
                           !x. x IN ring_carrier k ==> f j x = f i x rpow c)) /\
          (!i. i IN s ==> a i IN ring_carrier k) /\ &0 < e
          ==> ?x. x IN ring_carrier k /\
                  !i. i IN s ==> f i (ring_sub k x (a i)) < e"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC q69 THENL [EXISTS_TAC q68 THEN ASM_REWRITE_TAC [NOT_IN_EMPTY, RING_0], ALL_TAC] THEN SUBGOAL_THEN q67 MP_TAC THENL [X_GEN_TAC q66 THEN DISCH_TAC THEN MATCH_MP_TAC ABSOLUTE_VALUE_INEQUIVALENT_DOMINANT THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC q65 THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], DISCH_THEN ((X_CHOOSE_TAC q64) o (REWRITE_RULE [RIGHT_IMP_EXISTS_THM, SKOLEM_THM]))] THEN ABBREV_TAC q63 THEN SUBGOAL_THEN q62 ASSUME_TAC THENL [EXPAND_TAC "q" THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_DIV THEN ASM_SIMP_TAC [RING_ADD, RING_1, RING_POW], ALL_TAC] THEN ABBREV_TAC q61 THEN SUBGOAL_THEN q60 STRIP_ASSUME_TAC THENL [SUBGOAL_THEN q59 ASSUME_TAC THENL [ASM_SIMP_TAC [REAL_OF_NUM_LT, CARD_EQ_0, LE_1], ALL_TAC] THEN EXPAND_TAC "d" THEN CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC [], UNDISCH_TAC q58 THEN CONV_TAC REAL_FIELD], ALL_TAC] THEN ABBREV_TAC q57 THEN SUBGOAL_THEN q56 MP_TAC THENL [ASM_SIMP_TAC [EVENTUALLY_FORALL] THEN X_GEN_TAC q55 THEN DISCH_TAC THEN X_GEN_TAC q54 THEN DISCH_TAC THEN SUBGOAL_THEN q53 ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN q52 STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN q51 STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [ABSOLUTE_VALUE_POS], ALL_TAC] THEN EXPAND_TAC "c" THEN REWRITE_TAC [] THEN ASM_CASES_TAC q50 THEN ASM_REWRITE_TAC [] THENL [MP_TAC v49 THEN ASM_SIMP_TAC [] THEN DISCH_THEN (MP_TAC o ((SPEC q45) o CONJUNCT2)) THEN ASM_SIMP_TAC [REAL_LT_DIV, r44] THEN MATCH_MP_TAC v42 THEN X_GEN_TAC q41 THEN EXPAND_TAC "q" THEN REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN q40 ASSUME_TAC THENL [RING_CARRIER_TAC, ALL_TAC] THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_MUL] THEN MATCH_MP_TAC RLEMMA THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [ABSOLUTE_VALUE_POS], MP_TAC v39 THEN ASM_SIMP_TAC [] THEN DISCH_THEN (MP_TAC o ((SPEC q35) o CONJUNCT1)) THEN ASM_SIMP_TAC [REAL_LT_DIV, r34] THEN MATCH_MP_TAC v32 THEN X_GEN_TAC q31 THEN EXPAND_TAC "q" THEN REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN q30 ASSUME_TAC THENL [RING_CARRIER_TAC, ALL_TAC] THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_MUL] THEN MATCH_MP_TAC RLEMMA THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [ABSOLUTE_VALUE_POS]], ALL_TAC] THEN DISCH_THEN ((X_CHOOSE_TAC q29) o (BETA_RULE o (MATCH_MP EVENTUALLY_HAPPENS_SEQUENTIALLY))) THEN EXISTS_TAC q28 THEN ASM_SIMP_TAC [RING_SUM] THEN X_GEN_TAC q27 THEN DISCH_TAC THEN SUBGOAL_THEN q26 SUBST1_TAC THENL [EXPAND_TAC "c" THEN REWRITE_TAC [] THEN SUBGOAL_THEN q25 SUBST1_TAC THENL [ASM_SIMP_TAC [INSERT_DELETE], ALL_TAC] THEN ASM_SIMP_TAC [RING_SUM_CLAUSES, FINITE_DELETE, IN_DELETE, RING_MUL, RING_SUB, RING_1] THEN SUBGOAL_THEN q24 SUBST1_TAC THENL [MATCH_MP_TAC RING_SUM_EQ THEN SIMP_TAC [IN_DELETE], ALL_TAC] THEN SUBGOAL_THEN q23 MP_TAC THENL [ASM_SIMP_TAC [RING_SUM], ALL_TAC] THEN SPEC_TAC (q22, q21) THEN SPEC_TAC (q20, q19) THEN SPEC_TAC (q18, q17) THEN RING_TAC, ALL_TAC] THEN SUBGOAL_THEN q16 ASSUME_TAC THENL [EXPAND_TAC "c" THEN REPEAT STRIP_TAC THEN REWRITE_TAC [] THEN COND_CASES_TAC THEN ASM_SIMP_TAC [RING_MUL, RING_SUB, RING_1], ALL_TAC] THEN TRANS_TAC REAL_LET_TRANS q15 THEN CONJ_TAC THENL [MATCH_MP_TAC v14 THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBST1_TAC v8 THEN MATCH_MP_TAC SUM_BOUND_LT THEN ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN EXISTS_TAC q5 THEN ASM_SIMP_TAC [])

  -- @@RETURN BEGIN
  return { ABSOLUTE_VALUE_EQUIVALENT, ABSOLUTE_VALUE_EQUIVALENT_LE,
           ABSOLUTE_VALUE_EQUIVALENT_SYM, ABSOLUTE_VALUE_RPOW,
           NONARCHIMEDEAN_ABSOLUTE_VALUE_RPOW, ABSOLUTE_VALUE_POW_QUOTIENT,
           ABSOLUTE_VALUE_INEQUIVALENT_SEPARATE, ABSOLUTE_VALUE_INEQUIVALENT_DOMINANT,
           ABSOLUTE_VALUE_WEAK_APPROXIMATION }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- absolute_values.ml phrases from line 782 to 1018                       -/
/- ---------------------------------------------------------------------- -/

structure AbsoluteValues02 where
  -- @@FIELDS
  DEDEKIND_VALUATION_ABSOLUTE_VALUE_NONTRIVIAL : thm
  DEDEKIND_ABSOLUTE_VALUE_PRIME : thm
  DEDEKIND_VALUATION_ABSOLUTE_VALUE_UNIQUE : thm
  DEDEKIND_NONARCHIMEDEAN_ABSOLUTE_VALUE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupAbsoluteValues02 [HolBase] (D : AbsoluteValuesDeps) (BAbsoluteValues01 : AbsoluteValues01) :
    ExceptT String IO AbsoluteValues02 := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_INT_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, REAL_ARITH,
        REAL_ARITH_TAC, REAL_RAT_REDUCE_CONV, SET_TAC, TAUT, .. } := D
  let { ABSOLUTE_VALUE_0, ABSOLUTE_VALUE_1, ABSOLUTE_VALUE_MUL, ABSOLUTE_VALUE_NEG,
        ABSOLUTE_VALUE_NONTRIVIAL, ABSOLUTE_VALUE_POS, CONTRAPOS_THM,
        DEDEKIND_IMP_INTEGRAL_DOMAIN, DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL,
        DEDEKIND_VALUATION_ABSOLUTE_VALUE, DEDEKIND_VALUATION_IMAGE,
        DEDEKIND_VALUATION_POS, DEDEKIND_VALUATION_PRIME_IDEAL,
        DEDEKIND_VALUATION_WEAK_APPROXIMATION, DE_MORGAN_THM, EXISTS_UNIQUE_THM,
        EXTENSION, FIELD_FRACTION_NONZERO, FIELD_NONTRIVIAL, FINITE_SING,
        FORALL_UNWIND_THM2, INT_NEG_0, INT_NEG_NEG, INT_OF_NUM_EQ, INT_OF_NUM_LT,
        IN_ELIM_THM, IN_IMAGE, IN_RING_IDEAL_0, IN_SING, LEFT_IMP_EXISTS_THM,
        NONARCHIMEDEAN_IMP_ABSOLUTE_VALUE, NOT_EXISTS_THM, PRIME_IDEAL_IMP_SUBSET,
        PRIME_IMP_PROPER_IDEAL, PRIME_IMP_RING_IDEAL, PROPER_IDEAL_ALT, PSUBSET,
        REAL_LET_TRANS, REAL_LE_MUL2, REAL_LE_RMUL, REAL_LT_01, .. } := D.core1
  let { REAL_LT_IMP_NE, REAL_LT_REFL, REAL_MAX_LT, REAL_MUL_LID, REAL_NOT_LT, REAL_POS,
        REAL_ZPOW_0, REAL_ZPOW_1, REAL_ZPOW_MONO_LT, REAL_ZPOW_RPOW, RING_0, RING_1,
        RING_ADD, RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_1, RING_HOMOMORPHISM_ADD,
        RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_NEG, RING_MONOMORPHISM_EQ_0,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL, RING_NEG, RPOW_LT_1, SUBSET,
        field_of_fractions, maximal_ideal, nonarchimedean_absolute_value, prime_ideal,
        ring_homomorphism, ring_ideal, ring_monomorphism, .. } := D.core2
  let { ABSOLUTE_VALUE_EQUIVALENT_LE, .. } := BAbsoluteValues01
  -- @@SCOPE END

  let DEDEKIND_VALUATION_ABSOLUTE_VALUE_NONTRIVIAL ← prove
    r"!r k (h:A->B) P c (f:B->real).
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\ &1 < c /\
        (!x. x IN ring_carrier k /\ ~(x = ring_0 k)
             ==> f x = c zpow --(dedekind_valuation (r,k) h P x))
        ==> ?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ f x < &1"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN SUBGOAL_THEN (← q r"?a:A. a IN P /\ ~(a = ring_0 r)") STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN REWRITE_TAC [ring_ideal] THEN STRIP_TAC THEN ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [PRIME_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN EXISTS_TAC (← q r"(h:A->B) a") THEN SUBGOAL_THEN (← q r"(h:A->B) a IN ring_carrier k /\ ~(h a = ring_0 k)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0, ring_monomorphism, ring_homomorphism, SUBSET, IN_IMAGE], ASM_SIMP_TAC []] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"a:A")] DEDEKIND_VALUATION_PRIME_IDEAL) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"c:real"), (← q r"--(dedekind_valuation (r,k) (h:A->B) P (h a))"), (← q r"&0:int")] REAL_ZPOW_MONO_LT) THEN ASM_REWRITE_TAC [REAL_ZPOW_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_INT_ARITH_TAC)

  let DEDEKIND_ABSOLUTE_VALUE_PRIME ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"(x:real) <= &1 ==> &1 <= x ==> x = &1")
    let r2 ← TAUT (← q r"q /\ (p ==> r) ==> (p <=> q) ==> r")
    prove
      r"!r k (h:A->B) (f:B->real).
          dedekind_domain r /\ field_of_fractions (r,k) h /\
          nonarchimedean_absolute_value k f /\
          (?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ ~(f x = &1)) /\
          (!a. a IN ring_carrier r ==> f(h a) <= &1)
          ==> prime_ideal r {a | a IN ring_carrier r /\ f(h a) < &1} /\
              ~({a | a IN ring_carrier r /\ f(h a) < &1} = {ring_0 r}) /\
              ?c. &1 < c /\
                  !x. x IN ring_carrier k /\ ~(x = ring_0 k)
                      ==> f x =
                          c zpow --(dedekind_valuation (r,k) h
                                     {a | a IN ring_carrier r /\ f(h a) < &1}
                                     x)"
      (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "nt") (LABEL_TAC "le1"))))) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NONARCHIMEDEAN_IMP_ABSOLUTE_VALUE)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN FIRST_ASSUM (fun th => tactic_of do pure (MAP_EVERY (fun t => tactic_of do pure (ASSUME_TAC (← MATCH_MP t th))) [RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_1, RING_HOMOMORPHISM_NEG, RING_HOMOMORPHISM_ADD, RING_HOMOMORPHISM_MUL])) THEN SUBGOAL_THEN (← q r"!a:A. a IN ring_carrier r ==> (h:A->B) a IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [ring_homomorphism, SUBSET, IN_IMAGE], ALL_TAC] THEN ABBREV_TAC (← q r"P = {a:A | a IN ring_carrier r /\ (f:B->real)(h a) < &1}") THEN SUBGOAL_THEN (← q r"prime_ideal r (P:A->bool)") ASSUME_TAC THENL [EXPAND_TAC "P" THEN REWRITE_TAC [prime_ideal, PROPER_IDEAL_ALT, ring_ideal] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM, EXTENSION] THEN REPEAT CONJ_TAC THENL [SIMP_TAC [], REWRITE_TAC [RING_0], ASM_SIMP_TAC [RING_0, ABSOLUTE_VALUE_0, REAL_LT_01], ASM_SIMP_TAC [RING_NEG, ABSOLUTE_VALUE_NEG], MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"y:A")] THEN STRIP_TAC THEN ASM_SIMP_TAC [RING_ADD] THEN TRANS_TAC REAL_LET_TRANS (← q r"max ((f:B->real)(h(x:A))) (f(h y))") THEN ASM_REWRITE_TAC [REAL_MAX_LT] THEN FIRST_X_ASSUM (MATCH_MP_TAC o (CONJUNCT2 o (GEN_REWRITE_RULE id [nonarchimedean_absolute_value]))) THEN ASM_SIMP_TAC [], MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"y:A")] THEN STRIP_TAC THEN ASM_SIMP_TAC [RING_MUL, ABSOLUTE_VALUE_MUL] THEN TRANS_TAC REAL_LET_TRANS (← q r"(f:B->real)(h(y:A))") THEN ASM_REWRITE_TAC [] THEN GEN_REWRITE_TAC RAND_CONV [(← GSYM REAL_MUL_LID)] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC [] THEN ASM_MESON_TAC [ABSOLUTE_VALUE_POS], DISCH_THEN (MP_TAC o (SPEC (← q r"ring_1 r:A"))) THEN ASM_SIMP_TAC [RING_1, ABSOLUTE_VALUE_1, FIELD_NONTRIVIAL, REAL_LT_REFL], MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"y:A")] THEN STRIP_TAC THEN ASM_SIMP_TAC [] THEN UNDISCH_TAC (← q r"(f:B->real)(h(ring_mul r x y:A)) < &1") THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_MUL] THEN ONCE_REWRITE_TAC [(← GSYM CONTRAPOS_THM)] THEN REWRITE_TAC [DE_MORGAN_THM, REAL_NOT_LT] THEN STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [(← GSYM REAL_MUL_LID)] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC [REAL_POS]], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(P = {ring_0 r:A})") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:B ring"), (← q r"f:B->real")] ABSOLUTE_VALUE_NONTRIVIAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o CONJUNCT2) THEN USE_THEN "nt" (fun th => REWRITE_TAC [th]) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"x:B") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"x:B")] FIELD_FRACTION_NONZERO) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(a:A) IN P") MP_TAC THENL [ALL_TAC, ASM_REWRITE_TAC [IN_SING]] THEN EXPAND_TAC "P" THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"ring_mul k ((h:A->B) b) x = h a") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_MUL] THEN TRANS_TAC REAL_LET_TRANS (← q r"(f:B->real) x") THEN ASM_REWRITE_TAC [] THEN GEN_REWRITE_TAC RAND_CONV [(← GSYM REAL_MUL_LID)] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC [] THEN ASM_MESON_TAC [ABSOLUTE_VALUE_POS], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"g = \x. if x = ring_0 k then &0
              else &2 zpow --(dedekind_valuation (r,k) (h:A->B) P x)") THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"&2:real"), (← q r"g:B->real")] DEDEKIND_VALUATION_ABSOLUTE_VALUE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN EXPAND_TAC "g" THEN REWRITE_TAC [], STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"&2:real"), (← q r"g:B->real")] DEDEKIND_VALUATION_ABSOLUTE_VALUE_NONTRIVIAL) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN EXPAND_TAC "g" THEN SIMP_TAC [], DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"k:B ring"), (← q r"g:B->real"), (← q r"f:B->real")] ABSOLUTE_VALUE_EQUIVALENT_LE) THEN ANTS_TAC THENL [ASM_SIMP_TAC [NONARCHIMEDEAN_IMP_ABSOLUTE_VALUE] THEN ASM_MESON_TAC [REAL_LT_REFL], ALL_TAC] THEN MATCH_MP_TAC r2 THEN CONJ_TAC THENL [X_GEN_TAC (← q r"x:B") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"x = ring_0 k \/ &0 <= dedekind_valuation (r,k) (h:A->B) P x") MP_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"x:B")] DEDEKIND_VALUATION_POS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:A") (X_CHOOSE_THEN (← q r"b:A") STRIP_ASSUME_TAC)) THEN SUBGOAL_THEN (← q r"(f:B->real)(h(b:A)) = &1") ASSUME_TAC THENL [UNDISCH_TAC (← q r"~((b:A) IN P)") THEN EXPAND_TAC "P" THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_REWRITE_TAC [REAL_NOT_LT] THEN MATCH_MP_TAC r1 THEN USE_THEN "le1" MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN UNDISCH_TAC (← q r"ring_mul k ((h:A->B) b) x = h a") THEN DISCH_THEN (MP_TAC o (AP_TERM (← q r"f:B->real"))) THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_MUL, REAL_MUL_LID] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [], DISCH_THEN (X_CHOOSE_THEN (← q r"s:real") STRIP_ASSUME_TAC)] THEN EXISTS_TAC (← q r"&2 rpow s") THEN CONJ_TAC THENL [MATCH_MP_TAC RPOW_LT_1 THEN ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC, ALL_TAC] THEN X_GEN_TAC (← q r"x:B") THEN STRIP_TAC THEN ASM_SIMP_TAC [] THEN EXPAND_TAC "g" THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_ZPOW_RPOW THEN REAL_ARITH_TAC)

  let DEDEKIND_VALUATION_ABSOLUTE_VALUE_UNIQUE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"(~p ==> F) ==> p")
    let r2 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!r k (h:A->B) P Q c d.
          dedekind_domain r /\ field_of_fractions (r,k) h /\
          prime_ideal r P /\ ~(P = {ring_0 r}) /\
          prime_ideal r Q /\ ~(Q = {ring_0 r}) /\ &1 < c /\ &1 < d /\
          (!x. x IN ring_carrier k /\ ~(x = ring_0 k)
               ==> c zpow --(dedekind_valuation (r,k) h P x) =
                   d zpow --(dedekind_valuation (r,k) h Q x))
          ==> P = Q /\ c = d"
      (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "eq"))))))))) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN SUBGOAL_THEN (← q r"!a:A. a IN ring_carrier r ==> (h:A->B) a IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM, ring_homomorphism, SUBSET, IN_IMAGE], ALL_TAC] THEN MATCH_MP_TAC r2 THEN CONJ_TAC THENL [ALL_TAC, DISCH_THEN SUBST_ALL_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"{Q:A->bool}"), (← q r"\P:A->bool. --(&1):int")] DEDEKIND_VALUATION_WEAK_APPROXIMATION) THEN ASM_REWRITE_TAC [FINITE_SING, IN_SING, FORALL_UNWIND_THM2] THEN ASM_SIMP_TAC [DEDEKIND_IMP_INTEGRAL_DOMAIN] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"x:B") STRIP_ASSUME_TAC) THEN REMOVE_THEN "eq" (MP_TAC o (SPEC (← q r"x:B"))) THEN ASM_REWRITE_TAC [INT_NEG_NEG, REAL_ZPOW_1]] THEN MATCH_MP_TAC r1 THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"?a:A. a IN P /\ ~(a IN Q)") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool")] DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL) THEN ASM_REWRITE_TAC [maximal_ideal] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"Q:A->bool")) o ((REWRITE_RULE [NOT_EXISTS_THM]) o CONJUNCT2))) THEN ASM_SIMP_TAC [PRIME_IMP_PROPER_IDEAL, PSUBSET] THEN ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier r /\ ~(a = ring_0 r)") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [ASM_MESON_TAC [PRIME_IDEAL_IMP_SUBSET, SUBSET], DISCH_TAC THEN UNDISCH_TAC (← q r"~((a:A) IN Q)") THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IN_RING_IDEAL_0 THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL]], ALL_TAC] THEN SUBGOAL_THEN (← q r"dedekind_valuation (r,k) (h:A->B) Q (h a) = &0 /\
      &0 < dedekind_valuation (r,k) h P (h a)") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"Q:A->bool"), (← q r"a:A")] DEDEKIND_VALUATION_PRIME_IDEAL) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"Q:A->bool"), (← q r"a:A")] DEDEKIND_VALUATION_IMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [INT_OF_NUM_LT, INT_OF_NUM_EQ] THEN ARITH_TAC, MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"a:A")] DEDEKIND_VALUATION_PRIME_IDEAL) THEN ASM_REWRITE_TAC []], ALL_TAC] THEN REMOVE_THEN "eq" (MP_TAC o (SPEC (← q r"(h:A->B) a"))) THEN ANTS_TAC THENL [ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0], ALL_TAC] THEN ASM_REWRITE_TAC [INT_NEG_0, REAL_ZPOW_0] THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN MP_TAC (← ISPECL [(← q r"c:real"), (← q r"--(dedekind_valuation (r,k) (h:A->B) P (h a))"), (← q r"&0:int")] REAL_ZPOW_MONO_LT) THEN ASM_REWRITE_TAC [REAL_ZPOW_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_INT_ARITH_TAC)

  let DEDEKIND_NONARCHIMEDEAN_ABSOLUTE_VALUE ← prove
    r"!r k (h:A->B) (f:B->real).
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        nonarchimedean_absolute_value k f /\
        (?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ ~(f x = &1)) /\
        (!a. a IN ring_carrier r ==> f(h a) <= &1)
        ==> ?!P. prime_ideal r P /\ ~(P = {ring_0 r}) /\
                 ?c. &1 < c /\
                     !x. x IN ring_carrier k /\ ~(x = ring_0 k)
                         ==> f x = c zpow --(dedekind_valuation (r,k) h P x)"
    (REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL [EXISTS_TAC (← q r"{a | a IN ring_carrier r /\ (f:B->real)((h:A->B) a) < &1}") THEN MATCH_MP_TAC DEDEKIND_ABSOLUTE_VALUE_PRIME THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"P:A->bool"), (← q r"Q:A->bool")] THEN DISCH_THEN (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"c:real") STRIP_ASSUME_TAC))) (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"d:real") STRIP_ASSUME_TAC)))) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"Q:A->bool"), (← q r"c:real"), (← q r"d:real")] DEDEKIND_VALUATION_ABSOLUTE_VALUE_UNIQUE) THEN ANTS_TAC THENL [ALL_TAC, SIMP_TAC []] THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"x:B") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"x:B"))) THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"x:B"))) THEN ASM_REWRITE_TAC [] THEN MESON_TAC [])

  -- @@RETURN BEGIN
  return { DEDEKIND_VALUATION_ABSOLUTE_VALUE_NONTRIVIAL, DEDEKIND_ABSOLUTE_VALUE_PRIME,
           DEDEKIND_VALUATION_ABSOLUTE_VALUE_UNIQUE,
           DEDEKIND_NONARCHIMEDEAN_ABSOLUTE_VALUE }
  -- @@RETURN END

end HolANT.AbsoluteValues
