/- ========================================================================= -/
/- ANT: Absolute values, and the P-adic absolute values of a ...           -/
/- ========================================================================= -/
/- File: HolANT/DedekindAbsolute.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/dedekind_absolute.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antdedekindabsolutediff; the rest is by hand.  Its `needs` closure is
  Library/products.ml, Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, ANT/algmisc.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, ANT/integral.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/ideal_norm.ml, ANT/valuation_ring.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.DedekindAbsolute fills them).

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
import HolANT.Algmisc
import HolLibrary.Matroids
import HolLibrary.Permutations
import HolLibrary.RingDet
import HolLibrary.FieldTheory
import HolANT.Integral
import HolANT.IdealArith
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.IdealNorm
import HolANT.ValuationRing

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.Algmisc
open HolANT.Integral
open HolANT.IdealArith
open HolANT.Dedekind
open HolANT.DedekindStruct
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.IdealNorm
open HolANT.ValuationRing

namespace HolANT.DedekindAbsolute

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (CARD_CLAUSES CARD_SUBSET CARRIER_SUBRING_GENERATED_SUBRING CONJ_ASSOC
   CONTRAPOS_THM DEDEKIND_IDEAL_FACTORIZATION DEDEKIND_VALUATION_ADD
   DEDEKIND_VALUATION_IMAGE DEDEKIND_VALUATION_MUL
   DEDEKIND_VALUATION_PRIME_IDEAL EMPTY_SUBSET EQ_IMP EXTENSION
   FIELD_IMP_INTEGRAL_DOMAIN FIELD_MUL_RINV FIELD_NONTRIVIAL FINITE_EMPTY
   FINITE_INDUCT_STRONG FINITE_INSERT FINITE_INTEGRAL_DOMAIN_POW_CARD
   FINITE_NUMSEG FORALL_INT_CASES FORALL_IN_IMAGE FORALL_IN_INSERT FUN_EQ_THM
   IDEAL_GENERATED_EQ_0 IDEAL_GENERATED_INC_GEN IDEAL_GENERATED_MINIMAL
   IDEAL_NORM_FACTORIZATION IDEAL_NORM_GT_1 IDEAL_NORM_IDEAL_POW IMP_CONJ
   INSERT_SUBSET INTEGRAL_DOMAIN_MUL_EQ_0 INTEGRAL_DOMAIN_NONTRIVIAL
   INTEGRAL_ELEMENT_OVER_SUBRING INT_ABS_NUM INT_DIVISION INT_LE_NEG2 INT_MIN_LE
   INT_NEG_ADD INT_NOT_LE INT_OF_NUM_EQ INT_OF_NUM_LT INT_OF_NUM_OF_INT
   IN_ELIM_THM IN_IMAGE IN_INSERT IN_SING LE_REFL LE_TRANS LT_IMP_LE MONO_EXISTS
   MONO_OR MULT_SYM NOT_IN_EMPTY PRIME_IMP_PROPER_IDEAL PRIME_IMP_RING_IDEAL
   PRODUCT_EQ PROPER_IDEAL_ALT REAL_ABS_POS REAL_ARCH REAL_ENTIRE REAL_INV_0
   REAL_INV_1 REAL_INV_1_LT REAL_INV_LT_1 REAL_LE_ADD2 REAL_LE_ANTISYM
   REAL_LE_LADD REAL_LE_LDIV_EQ REAL_LE_MAX REAL_LE_MUL REAL_LE_MUL2
   REAL_LE_REFL REAL_LE_RMUL REAL_LE_TRANS REAL_LTE_TRANS REAL_LT_01
   REAL_LT_IMP_LE REAL_LT_LE REAL_LT_LMUL REAL_LT_RDIV_EQ : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (REAL_MAX_LE REAL_MUL_LID REAL_MUL_LINV REAL_MUL_LZERO REAL_MUL_RZERO
   REAL_NOT_LE REAL_NOT_LT REAL_OF_NUM_ADD REAL_OF_NUM_EQ REAL_OF_NUM_LE
   REAL_OF_NUM_LT REAL_OF_NUM_NPRODUCT REAL_OF_NUM_POW REAL_OF_NUM_SUC REAL_POS
   REAL_POW_2 REAL_POW_ADD REAL_POW_DIV REAL_POW_EQ_0 REAL_POW_EQ_1_IMP
   REAL_POW_LBOUND REAL_POW_LE REAL_POW_LE2 REAL_POW_LT REAL_POW_POW REAL_SUB_LT
   REAL_ZPOW_0 REAL_ZPOW_ADD REAL_ZPOW_EQ_0 REAL_ZPOW_LE REAL_ZPOW_MONO
   REAL_ZPOW_MONO_LT REAL_ZPOW_NUM REAL_ZPOW_POW RIGHT_FORALL_IMP_THM RING_0
   RING_1 RING_ADD RING_ADD_LZERO RING_ADD_RZERO RING_BINOMIAL_THEOREM
   RING_IDEAL_IDEAL_GENERATED RING_INV RING_INV_0 RING_MONOMORPHISM_EQ_0
   RING_MUL RING_MUL_LID RING_MUL_LNEG RING_MUL_LZERO RING_MUL_RNEG
   RING_MUL_RZERO RING_NEG RING_NEG_NEG RING_NEG_SUB RING_OF_INT_CASES
   RING_OF_INT_OF_NUM RING_OF_INT_REM RING_OF_NUM RING_POW RING_SUB RING_SUM
   RING_SUM_CLAUSES SING_SUBSET SQRT_1 SQRT_MONO_LT SQRT_POW_2 SUBSET SUB_0
   SUM_CLAUSES SUM_CONST_NUMSEG SUM_LE_NUMSEG VALUATION_SUBRING_INTEGRAL_ELEMENT
   VALUATION_SUBRING_MAXIMAL_IDEAL field_of_fractions real_div real_pow ring_div
   ring_homomorphism ring_of_num ring_pow ring_sub subring_of valuation_subring : thm)
  deriving Inhabited

/-- What dedekind_absolute.ml uses from Session besides theorems. -/
structure DedekindAbsoluteDeps where
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
/- dedekind_absolute.ml phrases from line 76 to 762                       -/
/- ---------------------------------------------------------------------- -/

structure DedekindAbsolute where
  -- @@FIELDS
  absolute_value : thm
  nonarchimedean_absolute_value : thm
  NONARCHIMEDEAN_IMP_ABSOLUTE_VALUE : thm
  NONARCHIMEDEAN_ABSOLUTE_VALUE : thm
  ABSOLUTE_VALUE_POS : thm
  ABSOLUTE_VALUE_EQ_0 : thm
  ABSOLUTE_VALUE_POS_LT : thm
  ABSOLUTE_VALUE_0 : thm
  ABSOLUTE_VALUE_MUL : thm
  ABSOLUTE_VALUE_TRIANGLE : thm
  ABSOLUTE_VALUE_1 : thm
  ABSOLUTE_VALUE_NEG : thm
  ABSOLUTE_VALUE_SUB : thm
  ABSOLUTE_VALUE_SUB_LE : thm
  ABSOLUTE_VALUE_ABS_SUB_LE : thm
  ABSOLUTE_VALUE_POW : thm
  ABSOLUTE_VALUE_INV : thm
  ABSOLUTE_VALUE_DIV : thm
  ABSOLUTE_VALUE_RING_SUM : thm
  ABSOLUTE_VALUE_RING_OF_NUM_LE : thm
  ABSOLUTE_VALUE_EQ : thm
  ABSOLUTE_VALUE_NONTRIVIAL : thm
  NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_NUM : thm
  NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_INT : thm
  REAL_POW_EVENTUALLY_GT_LINEAR : thm
  NONARCHIMEDEAN_ABSOLUTE_VALUE_BOUNDED : thm
  NONARCHIMEDEAN_ABSOLUTE_VALUE_CHAR : thm
  ABSOLUTE_VALUE_FINITE : thm
  NONARCHIMEDEAN_ABSOLUTE_VALUE_VALUATION_SUBRING : thm
  NONARCHIMEDEAN_ABSOLUTE_VALUE_INTEGRAL : thm
  DEDEKIND_VALUATION_ABSOLUTE_VALUE : thm
  DEDEKIND_VALUATION_IDEAL_NORM : thm
  DEDEKIND_VALUATION_NORMALIZED_ABSOLUTE_VALUE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDedekindAbsolute [HolBase] (D : DedekindAbsoluteDeps) :
    ExceptT String IO DedekindAbsolute := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_INT_ARITH_TAC, ASM_MESON_TAC,
        ASM_REAL_ARITH_TAC, INDUCT_TAC, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC,
        REAL_FIELD, REAL_RING, RING_RULE, TAUT, new_definition, .. } := D
  let { CARD_CLAUSES, CARD_SUBSET, CARRIER_SUBRING_GENERATED_SUBRING, CONJ_ASSOC,
        CONTRAPOS_THM, DEDEKIND_IDEAL_FACTORIZATION, DEDEKIND_VALUATION_ADD,
        DEDEKIND_VALUATION_IMAGE, DEDEKIND_VALUATION_MUL,
        DEDEKIND_VALUATION_PRIME_IDEAL, EMPTY_SUBSET, EQ_IMP, EXTENSION,
        FIELD_IMP_INTEGRAL_DOMAIN, FIELD_MUL_RINV, FIELD_NONTRIVIAL, FINITE_EMPTY,
        FINITE_INDUCT_STRONG, FINITE_INSERT, FINITE_INTEGRAL_DOMAIN_POW_CARD,
        FINITE_NUMSEG, FORALL_INT_CASES, FORALL_IN_IMAGE, FORALL_IN_INSERT, FUN_EQ_THM,
        IDEAL_GENERATED_EQ_0, IDEAL_GENERATED_INC_GEN, IDEAL_GENERATED_MINIMAL,
        IDEAL_NORM_FACTORIZATION, IDEAL_NORM_GT_1, IDEAL_NORM_IDEAL_POW, IMP_CONJ,
        INSERT_SUBSET, INTEGRAL_DOMAIN_MUL_EQ_0, INTEGRAL_DOMAIN_NONTRIVIAL,
        INTEGRAL_ELEMENT_OVER_SUBRING, INT_ABS_NUM, INT_DIVISION, INT_LE_NEG2,
        INT_MIN_LE, INT_NEG_ADD, INT_NOT_LE, INT_OF_NUM_EQ, INT_OF_NUM_LT,
        INT_OF_NUM_OF_INT, IN_ELIM_THM, IN_IMAGE, IN_INSERT, IN_SING, LE_REFL,
        LE_TRANS, LT_IMP_LE, MONO_EXISTS, MONO_OR, MULT_SYM, NOT_IN_EMPTY,
        PRIME_IMP_PROPER_IDEAL, PRIME_IMP_RING_IDEAL, PRODUCT_EQ, PROPER_IDEAL_ALT,
        REAL_ABS_POS, REAL_ARCH, REAL_ENTIRE, REAL_INV_0, REAL_INV_1, REAL_INV_1_LT,
        REAL_INV_LT_1, REAL_LE_ADD2, REAL_LE_ANTISYM, REAL_LE_LADD, REAL_LE_LDIV_EQ,
        REAL_LE_MAX, REAL_LE_MUL, REAL_LE_MUL2, REAL_LE_REFL, REAL_LE_RMUL,
        REAL_LE_TRANS, REAL_LTE_TRANS, REAL_LT_01, REAL_LT_IMP_LE, REAL_LT_LE,
        REAL_LT_LMUL, REAL_LT_RDIV_EQ, .. } := D.core1
  let { REAL_MAX_LE, REAL_MUL_LID, REAL_MUL_LINV, REAL_MUL_LZERO, REAL_MUL_RZERO,
        REAL_NOT_LE, REAL_NOT_LT, REAL_OF_NUM_ADD, REAL_OF_NUM_EQ, REAL_OF_NUM_LE,
        REAL_OF_NUM_LT, REAL_OF_NUM_NPRODUCT, REAL_OF_NUM_POW, REAL_OF_NUM_SUC,
        REAL_POS, REAL_POW_2, REAL_POW_ADD, REAL_POW_DIV, REAL_POW_EQ_0,
        REAL_POW_EQ_1_IMP, REAL_POW_LBOUND, REAL_POW_LE, REAL_POW_LE2, REAL_POW_LT,
        REAL_POW_POW, REAL_SUB_LT, REAL_ZPOW_0, REAL_ZPOW_ADD, REAL_ZPOW_EQ_0,
        REAL_ZPOW_LE, REAL_ZPOW_MONO, REAL_ZPOW_MONO_LT, REAL_ZPOW_NUM, REAL_ZPOW_POW,
        RIGHT_FORALL_IMP_THM, RING_0, RING_1, RING_ADD, RING_ADD_LZERO, RING_ADD_RZERO,
        RING_BINOMIAL_THEOREM, RING_IDEAL_IDEAL_GENERATED, RING_INV, RING_INV_0,
        RING_MONOMORPHISM_EQ_0, RING_MUL, RING_MUL_LID, RING_MUL_LNEG, RING_MUL_LZERO,
        RING_MUL_RNEG, RING_MUL_RZERO, RING_NEG, RING_NEG_NEG, RING_NEG_SUB,
        RING_OF_INT_CASES, RING_OF_INT_OF_NUM, RING_OF_INT_REM, RING_OF_NUM, RING_POW,
        RING_SUB, RING_SUM, RING_SUM_CLAUSES, SING_SUBSET, SQRT_1, SQRT_MONO_LT,
        SQRT_POW_2, SUBSET, SUB_0, SUM_CLAUSES, SUM_CONST_NUMSEG, SUM_LE_NUMSEG,
        VALUATION_SUBRING_INTEGRAL_ELEMENT, VALUATION_SUBRING_MAXIMAL_IDEAL,
        field_of_fractions, real_div, real_pow, ring_div, ring_homomorphism,
        ring_of_num, ring_pow, ring_sub, subring_of, valuation_subring, .. } := D.core2
  -- @@SCOPE END

  let absolute_value ← new_definition
    r"absolute_value (k:A ring) (f:A->real) <=>
        (!x. x IN ring_carrier k
             ==> &0 <= f x /\ (f x = &0 <=> x = ring_0 k)) /\
        (!x y. x IN ring_carrier k /\ y IN ring_carrier k
               ==> f(ring_mul k x y) = f x * f y) /\
        (!x y. x IN ring_carrier k /\ y IN ring_carrier k
               ==> f(ring_add k x y) <= f x + f y)"

  let nonarchimedean_absolute_value ← new_definition
    r"nonarchimedean_absolute_value (k:A ring) (f:A->real) <=>
        absolute_value k f /\
        !x y. x IN ring_carrier k /\ y IN ring_carrier k
              ==> f(ring_add k x y) <= max (f x) (f y)"

  let NONARCHIMEDEAN_IMP_ABSOLUTE_VALUE ← prove
    r"!k (f:A->real). nonarchimedean_absolute_value k f ==> absolute_value k f"
    (SIMP_TAC [nonarchimedean_absolute_value])

  let NONARCHIMEDEAN_ABSOLUTE_VALUE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"&0 <= (a:real) /\ &0 <= (b:real) /\ (c:real) <= max a b
    ==> c <= a + b")
    prove
      r"!k (f:A->real).
          nonarchimedean_absolute_value k f <=>
          (!x. x IN ring_carrier k
               ==> &0 <= f x /\ (f x = &0 <=> x = ring_0 k)) /\
          (!x y. x IN ring_carrier k /\ y IN ring_carrier k
                 ==> f(ring_mul k x y) = f x * f y) /\
          (!x y. x IN ring_carrier k /\ y IN ring_carrier k
                 ==> f(ring_add k x y) <= max (f x) (f y))"
      (REPEAT GEN_TAC THEN REWRITE_TAC [nonarchimedean_absolute_value, absolute_value] THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"y:A")] THEN STRIP_TAC THEN MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [])

  let ABSOLUTE_VALUE_POS ← prove
    r"!k (f:A->real) x.
        absolute_value k f /\ x IN ring_carrier k ==> &0 <= f x"
    (SIMP_TAC [absolute_value])

  let ABSOLUTE_VALUE_EQ_0 ← prove
    r"!k (f:A->real) x.
        absolute_value k f /\ x IN ring_carrier k
        ==> (f x = &0 <=> x = ring_0 k)"
    (SIMP_TAC [absolute_value])

  let ABSOLUTE_VALUE_POS_LT ← prove
    r"!k (f:A->real) x.
        absolute_value k f /\ x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> &0 < f x"
    (MESON_TAC [ABSOLUTE_VALUE_POS, ABSOLUTE_VALUE_EQ_0, REAL_LT_LE])

  let ABSOLUTE_VALUE_0 ← prove
    r"!k (f:A->real). absolute_value k f ==> f(ring_0 k) = &0"
    (MESON_TAC [absolute_value, RING_0])

  let ABSOLUTE_VALUE_MUL ← prove
    r"!k (f:A->real) x y.
        absolute_value k f /\ x IN ring_carrier k /\ y IN ring_carrier k
        ==> f(ring_mul k x y) = f x * f y"
    (SIMP_TAC [absolute_value])

  let ABSOLUTE_VALUE_TRIANGLE ← prove
    r"!k (f:A->real) x y.
        absolute_value k f /\ x IN ring_carrier k /\ y IN ring_carrier k
        ==> f(ring_add k x y) <= f x + f y"
    (SIMP_TAC [absolute_value])

  let ABSOLUTE_VALUE_1 ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"(a:real) = a * a <=> a * (a - &1) = &0")
    prove
      r"!k (f:A->real).
          absolute_value k f /\ ~(ring_1 k = ring_0 k) ==> f(ring_1 k) = &1"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"f:A->real"), (← q r"ring_1 k:A"), (← q r"ring_1 k:A")] ABSOLUTE_VALUE_MUL) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"f:A->real"), (← q r"ring_1 k:A")] ABSOLUTE_VALUE_POS_LT) THEN ASM_SIMP_TAC [RING_1, RING_MUL_LID] THEN REWRITE_TAC [r1, REAL_ENTIRE] THEN REAL_ARITH_TAC)

  let ABSOLUTE_VALUE_NEG ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"(a:real) * a = &1 <=> (a - &1) * (a + &1) = &0")
    let r2 ← REAL_RING (← q r"(a:real) = &1 ==> a * x = x")
    prove
      r"!k (f:A->real) x.
          absolute_value k f /\ x IN ring_carrier k
          ==> f(ring_neg k x) = f x"
      (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"ring_1 k:A = ring_0 k") THENL [SUBGOAL_THEN (← q r"!y:A. y IN ring_carrier k ==> y = ring_0 k") (fun th => ASM_SIMP_TAC [th, RING_NEG]) THEN ASM_MESON_TAC [RING_MUL_LID, RING_MUL_LZERO], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_neg k x:A = ring_mul k (ring_neg k (ring_1 k)) x") SUBST1_TAC THENL [ASM_SIMP_TAC [RING_MUL_LNEG, RING_1, RING_MUL_LID], ALL_TAC] THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_MUL, RING_NEG, RING_1] THEN MATCH_MP_TAC r2 THEN SUBGOAL_THEN (← q r"f(ring_neg k (ring_1 k):A) * f(ring_neg k (ring_1 k)) = (&1:real)") MP_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"f:A->real"), (← q r"ring_neg k (ring_1 k):A"), (← q r"ring_neg k (ring_1 k):A")] ABSOLUTE_VALUE_MUL) THEN ASM_SIMP_TAC [RING_NEG, RING_1, RING_MUL_LNEG, RING_MUL_RNEG, RING_NEG_NEG, RING_MUL_LID, ABSOLUTE_VALUE_1], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"f:A->real"), (← q r"ring_neg k (ring_1 k):A")] ABSOLUTE_VALUE_POS) THEN ASM_SIMP_TAC [RING_NEG, RING_1] THEN SPEC_TAC ((← q r"f(ring_neg k (ring_1 k):A):real"), (← q r"a:real")) THEN REWRITE_TAC [r1, REAL_ENTIRE] THEN REAL_ARITH_TAC)

  let ABSOLUTE_VALUE_SUB ← prove
    r"!k (f:A->real) x y.
        absolute_value k f /\ x IN ring_carrier k /\ y IN ring_carrier k
        ==> f(ring_sub k x y) = f(ring_sub k y x)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"f:A->real"), (← q r"ring_sub k x y:A")] ABSOLUTE_VALUE_NEG) THEN ASM_SIMP_TAC [RING_SUB, RING_NEG_SUB])

  let ABSOLUTE_VALUE_SUB_LE ← prove
    r"!k (f:A->real) x y.
        absolute_value k f /\ x IN ring_carrier k /\ y IN ring_carrier k
        ==> f(ring_sub k x y) <= f x + f y"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [ring_sub] THEN ASM_MESON_TAC [ABSOLUTE_VALUE_TRIANGLE, ABSOLUTE_VALUE_NEG, RING_NEG])

  let ABSOLUTE_VALUE_ABS_SUB_LE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_add k (ring_sub k x y) y = (x:A) /\
    ring_add k (ring_sub k y x) x = (y:A)")
    prove
      r"!k (f:A->real) x y.
          absolute_value k f /\ x IN ring_carrier k /\ y IN ring_carrier k
          ==> abs(f x - f y) <= f(ring_sub k x y)"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"f:A->real"), (← q r"ring_sub k x y:A"), (← q r"y:A")] ABSOLUTE_VALUE_TRIANGLE) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"f:A->real"), (← q r"ring_sub k y x:A"), (← q r"x:A")] ABSOLUTE_VALUE_TRIANGLE) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"f:A->real"), (← q r"x:A"), (← q r"y:A")] ABSOLUTE_VALUE_SUB) THEN ASM_SIMP_TAC [RING_SUB] THEN ASM_SIMP_TAC [r1] THEN REAL_ARITH_TAC)

  let ABSOLUTE_VALUE_POW ← prove
    r"!k (f:A->real) x n.
        absolute_value k f /\ ~(ring_1 k = ring_0 k) /\ x IN ring_carrier k
        ==> f(ring_pow k x n) = f x pow n"
    (REPLICATE_TAC 3 GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC [ring_pow, real_pow, ABSOLUTE_VALUE_1, ABSOLUTE_VALUE_MUL, RING_POW])

  let ABSOLUTE_VALUE_INV ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_FIELD (← q r"x * y = &1 ==> y = inv x")
    prove
      r"!k (f:A->real) x.
          field k /\ absolute_value k f /\ x IN ring_carrier k
          ==> f(ring_inv k x) = inv(f x)"
      (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"x:A = ring_0 k") THEN ASM_SIMP_TAC [RING_INV_0, ABSOLUTE_VALUE_0, REAL_INV_0] THEN MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [(← GSYM ABSOLUTE_VALUE_MUL), RING_INV, FIELD_MUL_RINV] THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_1, FIELD_NONTRIVIAL])

  let ABSOLUTE_VALUE_DIV ← prove
    r"!k (f:A->real) x y.
        field k /\ absolute_value k f /\
        x IN ring_carrier k /\ y IN ring_carrier k
        ==> f(ring_div k x y) = f x / f y"
    (SIMP_TAC [ring_div, real_div, ABSOLUTE_VALUE_MUL, ABSOLUTE_VALUE_INV, RING_INV])

  let ABSOLUTE_VALUE_RING_SUM ← prove
    r"!k (f:A->real) (g:K->A) s.
        absolute_value k f /\ FINITE s /\
        (!i. i IN s ==> g i IN ring_carrier k)
        ==> f(ring_sum k s g) <= sum s (\i. f(g i))"
    (REPLICATE_TAC 3 GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN SIMP_TAC [RING_SUM_CLAUSES, SUM_CLAUSES, FORALL_IN_INSERT] THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_0, REAL_LE_REFL] THEN REPEAT STRIP_TAC THEN TRANS_TAC REAL_LE_TRANS (← q r"(f:A->real)((g:K->A) x) + f(ring_sum k s g)") THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_TRIANGLE, RING_SUM, REAL_LE_LADD])

  let ABSOLUTE_VALUE_RING_OF_NUM_LE ← prove
    r"!k (f:A->real) n.
        absolute_value k f ==> f(ring_of_num k n) <= &n"
    (REPLICATE_TAC 2 GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC [ring_of_num, ABSOLUTE_VALUE_0, REAL_LE_REFL] THEN TRANS_TAC REAL_LE_TRANS (← q r"(f:A->real)(ring_of_num k n) + f(ring_1 k)") THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_TRIANGLE, RING_OF_NUM, RING_1] THEN REWRITE_TAC [(← GSYM REAL_OF_NUM_SUC)] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"ring_1 k:A = ring_0 k") THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_0, ABSOLUTE_VALUE_1, REAL_POS, REAL_LE_REFL])

  let ABSOLUTE_VALUE_EQ ← prove
    r"!k (f:A->real) g.
        (!x. x IN ring_carrier k ==> f x = g x)
        ==> (absolute_value k f <=> absolute_value k g) /\
            (nonarchimedean_absolute_value k f <=>
             nonarchimedean_absolute_value k g)"
    (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [NONARCHIMEDEAN_ABSOLUTE_VALUE, absolute_value, RING_ADD, RING_MUL])

  let ABSOLUTE_VALUE_NONTRIVIAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"f(x:A) < (&1:real) \/ &1 < f x \/ f x = &1")
    let r2 ← TAUT (← q r"(p ==> q /\ r) /\ (q ==> p) /\ (r ==> p)
                     ==> (p <=> q) /\ (p <=> r)")
    prove
      r"!k (f:A->real).
          field k /\ absolute_value k f
          ==> ((?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ ~(f x = &1)) <=>
               (?x. x IN ring_carrier k /\ &1 < f x)) /\
              ((?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ ~(f x = &1)) <=>
               (?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\ f x < &1))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC r2 THEN REPEAT CONJ_TAC THENL [DISCH_THEN (X_CHOOSE_THEN (← q r"x:A") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(&0:real) < f(x:A)") ASSUME_TAC THENL [ASM_MESON_TAC [ABSOLUTE_VALUE_POS_LT], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(ring_inv k x:A = ring_0 k) /\ ring_inv k x IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_INV, FIELD_MUL_RINV, RING_MUL_RZERO, FIELD_NONTRIVIAL], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"f:A->real"), (← q r"x:A")] ABSOLUTE_VALUE_INV) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN DISJ_CASES_TAC r1 THENL [CONJ_TAC THENL [EXISTS_TAC (← q r"ring_inv k x:A"), EXISTS_TAC (← q r"x:A")] THEN ASM_SIMP_TAC [REAL_INV_LT_1] THEN ASM_SIMP_TAC [REAL_INV_1_LT], FIRST_X_ASSUM DISJ_CASES_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN CONJ_TAC THENL [EXISTS_TAC (← q r"x:A"), EXISTS_TAC (← q r"ring_inv k x:A")] THEN ASM_SIMP_TAC [REAL_INV_LT_1]], MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"x:A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [DISCH_TAC THEN UNDISCH_TAC (← q r"(&1:real) < f(x:A)") THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_0] THEN REAL_ARITH_TAC, ASM_REAL_ARITH_TAC], MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC [] THEN REAL_ARITH_TAC])

  let NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_NUM ← prove
    r"!k (f:A->real) n.
        nonarchimedean_absolute_value k f ==> f(ring_of_num k n) <= &1"
    (REPLICATE_TAC 2 GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NONARCHIMEDEAN_IMP_ABSOLUTE_VALUE)) THEN SUBGOAL_THEN (← q r"(f:A->real)(ring_1 k) <= &1") ASSUME_TAC THENL [ASM_CASES_TAC (← q r"ring_1 k:A = ring_0 k") THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_0, ABSOLUTE_VALUE_1, REAL_POS, REAL_LE_REFL], ALL_TAC] THEN INDUCT_TAC THEN ASM_SIMP_TAC [ring_of_num, ABSOLUTE_VALUE_0, REAL_POS] THEN TRANS_TAC REAL_LE_TRANS (← q r"max ((f:A->real)(ring_of_num k n)) (f(ring_1 k))") THEN ASM_REWRITE_TAC [REAL_MAX_LE] THEN FIRST_X_ASSUM (MATCH_MP_TAC o (CONJUNCT2 o (GEN_REWRITE_RULE id [nonarchimedean_absolute_value]))) THEN REWRITE_TAC [RING_OF_NUM, RING_1])

  let NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_INT ← prove
    r"!k (f:A->real) n.
        nonarchimedean_absolute_value k f ==> f(ring_of_int k n) <= &1"
    (REPLICATE_TAC 2 GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NONARCHIMEDEAN_IMP_ABSOLUTE_VALUE)) THEN REWRITE_TAC [FORALL_INT_CASES, RING_OF_INT_CASES] THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_NEG, RING_OF_NUM, NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_NUM])

  let REAL_POW_EVENTUALLY_GT_LINEAR ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"(a:real) <= abs a /\ (b:real) <= abs b")
    let r2 ← REAL_ARITH (← q r"(x:real) <= y ==> z < x ==> z < y")
    let r3 ← REAL_ARITH (← q r"&0 <= (x:real) ==> &0 <= &1 + x")
    let r4 ← REAL_ARITH (← q r"&1 < (t:real) ==> &0 <= t")
    let r5 ← ARITH_RULE (← q r"1 <= n <=> ~(n = 0)")
    prove
      r"!(t:real) a b. &1 < t ==> ?N. !n. N <= n ==> a * &n + b < t pow n"
      (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"e = sqrt t - &1") THEN SUBGOAL_THEN (← q r"&0 < (e:real)") ASSUME_TAC THENL [EXPAND_TAC "e" THEN REWRITE_TAC [REAL_SUB_LT] THEN GEN_REWRITE_TAC LAND_CONV [(← GSYM SQRT_1)] THEN MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← SPEC (← q r"(e:real) pow 2") REAL_ARCH) THEN ASM_SIMP_TAC [REAL_POW_LT] THEN DISCH_THEN ((X_CHOOSE_TAC (← q r"N:num")) o (SPEC (← q r"abs (a:real) + abs b + &1"))) THEN EXISTS_TAC (← q r"N:num") THEN X_GEN_TAC (← q r"n:num") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"abs (a:real) + abs b + &1 < &n * e pow 2") ASSUME_TAC THENL [TRANS_TAC REAL_LTE_TRANS (← q r"&N * (e:real) pow 2") THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC [REAL_OF_NUM_LE, REAL_POW_LE, REAL_LT_IMP_LE], ALL_TAC] THEN SUBGOAL_THEN (← q r"(&1:real) <= &n") ASSUME_TAC THENL [REWRITE_TAC [REAL_OF_NUM_LE] THEN REWRITE_TAC [r5] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"abs (a:real) + abs b + &1 < &n * e pow 2") THEN ASM_REWRITE_TAC [REAL_MUL_LZERO] THEN REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"(&1 + &n * (e:real)) pow 2 <= t pow n") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"t pow n = (sqrt t pow n) pow 2") SUBST1_TAC THENL [REWRITE_TAC [REAL_POW_POW] THEN ONCE_REWRITE_TAC [MULT_SYM] THEN REWRITE_TAC [(← GSYM REAL_POW_POW)] THEN ASM_SIMP_TAC [SQRT_POW_2, r4], ALL_TAC] THEN MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL [MATCH_MP_TAC r3 THEN ASM_SIMP_TAC [REAL_LE_MUL, REAL_POS, REAL_LT_IMP_LE], SUBGOAL_THEN (← q r"sqrt t = &1 + e") SUBST1_TAC THENL [EXPAND_TAC "e" THEN REAL_ARITH_TAC, ALL_TAC] THEN MATCH_MP_TAC REAL_POW_LBOUND THEN ASM_SIMP_TAC [REAL_LT_IMP_LE]], ALL_TAC] THEN FIRST_X_ASSUM (MATCH_MP_TAC o (MATCH_MP r2)) THEN SUBGOAL_THEN (← q r"&n * (abs (a:real) + abs b + &1) < &n * (&n * e pow 2)") MP_TAC THENL [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"&0 <= &n * (e:real)") MP_TAC THENL [ASM_SIMP_TAC [REAL_LE_MUL, REAL_POS, REAL_LT_IMP_LE], ALL_TAC] THEN SUBGOAL_THEN (← q r"abs (b:real) <= &n * abs b") MP_TAC THENL [GEN_REWRITE_TAC LAND_CONV [(← GSYM REAL_MUL_LID)] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC [REAL_ABS_POS], ALL_TAC] THEN REWRITE_TAC [REAL_POW_2] THEN MAP_EVERY (fun t => tactic_of do pure (MP_TAC (← SPEC t REAL_ABS_POS))) [(← q r"a:real"), (← q r"b:real")] THEN MP_TAC r1 THEN SUBGOAL_THEN (← q r"(a:real) * &n <= abs a * &n") MP_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC [REAL_POS] THEN REAL_ARITH_TAC, ALL_TAC] THEN REAL_ARITH_TAC)

  let NONARCHIMEDEAN_ABSOLUTE_VALUE_BOUNDED ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"(p ==> q) /\ (q ==> r) /\ (r ==> p)
                     ==> (p <=> q) /\ (p <=> r)")
    prove
      r"!k (f:A->real).
          absolute_value k f
          ==> (nonarchimedean_absolute_value k f <=>
               !n. f(ring_of_int k n) <= &1) /\
              (nonarchimedean_absolute_value k f <=>
               ?c. !n. f(ring_of_int k n) <= c)"
      (REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC r1 THEN REPEAT CONJ_TAC THENL [MESON_TAC [NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_INT], MESON_TAC [], DISCH_THEN (X_CHOOSE_THEN (← q r"c:real") (LABEL_TAC "c"))] THEN ASM_REWRITE_TAC [nonarchimedean_absolute_value] THEN MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"y:A")] THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"ring_1 k:A = ring_0 k") THENL [SUBGOAL_THEN (← q r"!z:A. z IN ring_carrier k ==> z = ring_0 k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_MUL_LID, RING_MUL_LZERO], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_add k x y:A = ring_0 k /\ x = ring_0 k") (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_SIMP_TAC [RING_ADD], ALL_TAC] THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_0, REAL_LE_MAX, REAL_LE_REFL], ALL_TAC] THEN SUBGOAL_THEN (← q r"!j. (f:A->real)(ring_of_num k j) <= c") ASSUME_TAC THENL [GEN_TAC THEN REWRITE_TAC [(← GSYM RING_OF_INT_OF_NUM)] THEN USE_THEN "c" MATCH_ACCEPT_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"&0 <= (c:real)") ASSUME_TAC THENL [TRANS_TAC REAL_LE_TRANS (← q r"(f:A->real)(ring_of_num k 0)") THEN ASM_REWRITE_TAC [ring_of_num] THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_0, REAL_LE_REFL], ALL_TAC] THEN ABBREV_TAC (← q r"M = max ((f:A->real) x) (f y)") THEN SUBGOAL_THEN (← q r"&0 <= (f:A->real) x /\ &0 <= f y /\ f x <= M /\ f y <= M") STRIP_ASSUME_TAC THENL [EXPAND_TAC "M" THEN REWRITE_TAC [REAL_LE_MAX, REAL_LE_REFL] THEN ASM_MESON_TAC [ABSOLUTE_VALUE_POS], ALL_TAC] THEN SUBGOAL_THEN (← q r"!m. (f:A->real)(ring_add k x y) pow m <= (c * &m + c) * M pow m") ASSUME_TAC THENL [X_GEN_TAC (← q r"m:num") THEN SUBGOAL_THEN (← q r"(f:A->real)(ring_add k x y) pow m = f(ring_pow k (ring_add k x y) m)") SUBST1_TAC THENL [ASM_SIMP_TAC [ABSOLUTE_VALUE_POW, RING_ADD], ALL_TAC] THEN ASM_SIMP_TAC [RING_BINOMIAL_THEOREM] THEN TRANS_TAC REAL_LE_TRANS (← q r"sum(0..m) (\i. (f:A->real)
          (ring_mul k (ring_of_num k (binom(m,i)))
            (ring_mul k (ring_pow k x i) (ring_pow k y (m - i)))))") THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"f:A->real"), (← q r"\i. ring_mul k (ring_of_num k (binom(m,i)))
                  (ring_mul k (ring_pow k x i) (ring_pow k (y:A) (m - i)))"), (← q r"0..m")] ABSOLUTE_VALUE_RING_SUM) THEN ASM_SIMP_TAC [FINITE_NUMSEG, RING_MUL, RING_POW, RING_OF_NUM] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM], ALL_TAC] THEN TRANS_TAC REAL_LE_TRANS (← q r"sum(0..m) (\i. c * M pow m)") THEN CONJ_TAC THENL [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_MUL, ABSOLUTE_VALUE_POW, RING_MUL, RING_POW, RING_OF_NUM] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [REAL_LE_MUL, REAL_POW_LE] THEN SUBGOAL_THEN (← q r"(M:real) pow m = M pow i * M pow (m - i)") SUBST1_TAC THENL [REWRITE_TAC [(← GSYM REAL_POW_ADD)] THEN AP_TERM_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN CONJ_TAC THENL [ASM_MESON_TAC [ABSOLUTE_VALUE_POS, RING_OF_NUM], ALL_TAC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC [REAL_POW_LE, REAL_POW_LE2], REWRITE_TAC [SUM_CONST_NUMSEG, SUB_0, (← GSYM REAL_OF_NUM_ADD)] THEN REAL_ARITH_TAC], ALL_TAC] THEN ASM_CASES_TAC (← q r"(M:real) = &0") THENL [SUBGOAL_THEN (← q r"x:A = ring_0 k /\ y = ring_0 k") (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_MESON_TAC [ABSOLUTE_VALUE_EQ_0, REAL_LE_ANTISYM], ALL_TAC] THEN ASM_SIMP_TAC [RING_ADD_LZERO, RING_0, ABSOLUTE_VALUE_0, REAL_LE_REFL], ALL_TAC] THEN SUBGOAL_THEN (← q r"&0 < (M:real)") ASSUME_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [(← GSYM REAL_NOT_LT)] THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"(f:A->real)(ring_add k x y) / M"), (← q r"c:real"), (← q r"c:real")] REAL_POW_EVENTUALLY_GT_LINEAR) THEN ASM_SIMP_TAC [REAL_LT_RDIV_EQ, REAL_MUL_LID] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"N:num") (MP_TAC o (SPEC (← q r"N:num")))) THEN REWRITE_TAC [LE_REFL, REAL_NOT_LT, REAL_POW_DIV] THEN ASM_SIMP_TAC [REAL_LE_LDIV_EQ, REAL_POW_LT])

  let NONARCHIMEDEAN_ABSOLUTE_VALUE_CHAR ← prove
    r"!k (f:A->real).
        absolute_value k f /\ ~(ring_char k = 0)
        ==> nonarchimedean_absolute_value k f"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"f:A->real")] NONARCHIMEDEAN_ABSOLUTE_VALUE_BOUNDED) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o CONJUNCT2) THEN EXISTS_TAC (← q r"&(ring_char(k:A ring)):real") THEN X_GEN_TAC (← q r"n:int") THEN ONCE_REWRITE_TAC [(← GSYM RING_OF_INT_REM)] THEN MP_TAC (← ISPECL [(← q r"n:int"), (← q r"&(ring_char(k:A ring)):int")] INT_DIVISION) THEN ASM_REWRITE_TAC [INT_OF_NUM_EQ, INT_ABS_NUM] THEN DISCH_THEN (STRIP_ASSUME_TAC o CONJUNCT2) THEN SUBGOAL_THEN (← q r"&(num_of_int(n rem &(ring_char(k:A ring)))) = n rem &(ring_char k)") (SUBST1_TAC o SYM) THENL [ASM_SIMP_TAC [INT_OF_NUM_OF_INT], ALL_TAC] THEN REWRITE_TAC [RING_OF_INT_OF_NUM] THEN TRANS_TAC REAL_LE_TRANS (← q r"&(num_of_int(n rem &(ring_char(k:A ring)))):real") THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_RING_OF_NUM_LE, REAL_OF_NUM_LE] THEN MATCH_MP_TAC LT_IMP_LE THEN REWRITE_TAC [(← GSYM INT_OF_NUM_LT)] THEN ASM_SIMP_TAC [INT_OF_NUM_OF_INT])

  let ABSOLUTE_VALUE_FINITE ← prove
    r"!k (f:A->real) x.
        integral_domain k /\ FINITE(ring_carrier k) /\ absolute_value k f /\
        x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> f x = &1"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"~(ring_1 k:A = ring_0 k)") ASSUME_TAC THENL [ASM_SIMP_TAC [INTEGRAL_DOMAIN_NONTRIVIAL], ALL_TAC] THEN ABBREV_TAC (← q r"N = CARD(ring_carrier k:A->bool)") THEN SUBGOAL_THEN (← q r"2 <= N") ASSUME_TAC THENL [EXPAND_TAC "N" THEN TRANS_TAC LE_TRANS (← q r"CARD {ring_0 k:A,ring_1 k}") THEN CONJ_TAC THENL [ASM_SIMP_TAC [CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY, IN_INSERT, NOT_IN_EMPTY] THEN ARITH_TAC, MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC [INSERT_SUBSET, EMPTY_SUBSET, RING_0, RING_1]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A")] FINITE_INTEGRAL_DOMAIN_POW_CARD) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (AP_TERM (← q r"f:A->real"))) THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_POW] THEN SUBGOAL_THEN (← q r"&0 < (f:A->real) x") ASSUME_TAC THENL [ASM_MESON_TAC [ABSOLUTE_VALUE_POS_LT], ALL_TAC] THEN SUBGOAL_THEN (← q r"N = SUC(N - 1)") SUBST1_TAC THENL [ASM_ARITH_TAC, REWRITE_TAC [real_pow]] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(f:A->real) x pow (N - 1) = &1") MP_TAC THENL [UNDISCH_TAC (← q r"(f:A->real) x * f x pow (N - 1) = f x") THEN UNDISCH_TAC (← q r"&0 < (f:A->real) x") THEN CONV_TAC REAL_FIELD, ALL_TAC] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"(f:A->real) x"), (← q r"N - 1")] REAL_POW_EQ_1_IMP) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [ASM_ARITH_TAC, ASM_REAL_ARITH_TAC])

  let NONARCHIMEDEAN_ABSOLUTE_VALUE_VALUATION_SUBRING ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"(f:A->real) x <= &1 \/ &1 < f x")
    let r2 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!k (f:A->real).
          field k /\ nonarchimedean_absolute_value k f
          ==> valuation_subring k {x | x IN ring_carrier k /\ f x <= &1} /\
              maximal_ideal
               (subring_generated k {x | x IN ring_carrier k /\ f x <= &1})
               {x | x IN ring_carrier k /\ f x < &1}"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NONARCHIMEDEAN_IMP_ABSOLUTE_VALUE)) THEN MATCH_MP_TAC r2 THEN CONJ_TAC THENL [ASM_REWRITE_TAC [valuation_subring, subring_of] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ASM_SIMP_TAC [RING_0, RING_1, RING_NEG, RING_ADD, RING_MUL, RING_INV, ABSOLUTE_VALUE_0, ABSOLUTE_VALUE_1, FIELD_NONTRIVIAL, ABSOLUTE_VALUE_NEG, ABSOLUTE_VALUE_MUL, ABSOLUTE_VALUE_INV, REAL_POS, REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL [MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"y:A")] THEN STRIP_TAC THEN TRANS_TAC REAL_LE_TRANS (← q r"max ((f:A->real) x) (f y)") THEN ASM_REWRITE_TAC [REAL_MAX_LE] THEN FIRST_X_ASSUM (MATCH_MP_TAC o (CONJUNCT2 o (GEN_REWRITE_RULE id [nonarchimedean_absolute_value]))) THEN ASM_REWRITE_TAC [], MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"y:A")] THEN STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [(← GSYM REAL_MUL_LID)] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_MESON_TAC [ABSOLUTE_VALUE_POS], X_GEN_TAC (← q r"x:A") THEN STRIP_TAC THEN DISJ_CASES_TAC r1 THEN ASM_SIMP_TAC [REAL_INV_LT_1, REAL_LT_IMP_LE]], DISCH_TAC] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP VALUATION_SUBRING_MAXIMAL_IDEAL th)])) THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:A") THEN ASM_CASES_TAC (← q r"(x:A) IN ring_carrier k") THEN ASM_REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"x:A = ring_0 k") THEN ASM_SIMP_TAC [ABSOLUTE_VALUE_0, REAL_LT_01, REAL_POS] THEN ASM_SIMP_TAC [RING_INV, ABSOLUTE_VALUE_INV] THEN SUBGOAL_THEN (← q r"&0 < (f:A->real) x") MP_TAC THENL [ASM_MESON_TAC [ABSOLUTE_VALUE_POS_LT], ALL_TAC] THEN SPEC_TAC ((← q r"(f:A->real) x"), (← q r"t:real")) THEN GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL [ASM_SIMP_TAC [REAL_LT_IMP_LE, REAL_NOT_LE, REAL_INV_1_LT], ALL_TAC] THEN REWRITE_TAC [REAL_NOT_LE] THEN STRIP_TAC THEN ASM_REWRITE_TAC [REAL_LT_LE] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"&1 < inv t") THEN ASM_REWRITE_TAC [REAL_INV_1] THEN REAL_ARITH_TAC)

  let NONARCHIMEDEAN_ABSOLUTE_VALUE_INTEGRAL ← prove
    r"!r k (h:B->A) (f:A->real) x.
        field k /\ nonarchimedean_absolute_value k f /\
        ring_homomorphism(r,k) h /\
        (!a. a IN ring_carrier r ==> f(h a) <= &1) /\
        integral_element (r,k) h x
        ==> f x <= &1"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"f:A->real")] NONARCHIMEDEAN_ABSOLUTE_VALUE_VALUATION_SUBRING) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN SUBGOAL_THEN (← q r"(x:A) IN {x | x IN ring_carrier k /\ f x <= (&1:real)}") MP_TAC THENL [ALL_TAC, SIMP_TAC [IN_ELIM_THM]] THEN MATCH_MP_TAC VALUATION_SUBRING_INTEGRAL_ELEMENT THEN EXISTS_TAC (← q r"k:A ring") THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC (← ISPECL [(← q r"r:B ring"), (← q r"k:A ring"), (← q r"h:B->A")] INTEGRAL_ELEMENT_OVER_SUBRING) THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP CARRIER_SUBRING_GENERATED_SUBRING (← CONJUNCT1 (← CONJUNCT2 (← GEN_REWRITE_RULE id [valuation_subring] th))))])) THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN ASM_MESON_TAC [ring_homomorphism, SUBSET, IN_IMAGE])

  let DEDEKIND_VALUATION_ABSOLUTE_VALUE ← prove
    r"!r k (h:A->B) P c (f:B->real).
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\ &1 < c /\
        (!x. f x = if x = ring_0 k then &0
                   else c zpow --(dedekind_valuation (r,k) h P x))
        ==> nonarchimedean_absolute_value k f /\
            (!x. x IN ring_carrier k
                 ==> (f x <= &1 <=>
                      x = ring_0 k \/ &0 <= dedekind_valuation (r,k) h P x))"
    (REWRITE_TAC [NONARCHIMEDEAN_ABSOLUTE_VALUE, (← GSYM CONJ_ASSOC)] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"&0 < c /\ ~(c = &0) /\ &1 <= (c:real)") STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN REPEAT CONJ_TAC THENL [X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [REAL_LE_REFL, REAL_ZPOW_LE, REAL_LT_IMP_LE, REAL_ZPOW_EQ_0], MAP_EVERY X_GEN_TAC [(← q r"x:B"), (← q r"y:B")] THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"x:B = ring_0 k") THEN ASM_SIMP_TAC [RING_MUL_LZERO, REAL_MUL_LZERO] THEN ASM_CASES_TAC (← q r"y:B = ring_0 k") THEN ASM_SIMP_TAC [RING_MUL_RZERO, REAL_MUL_RZERO] THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_MUL_EQ_0, FIELD_IMP_INTEGRAL_DOMAIN] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"x:B"), (← q r"y:B")] DEDEKIND_VALUATION_MUL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [INT_NEG_ADD, REAL_ZPOW_ADD], MAP_EVERY X_GEN_TAC [(← q r"x:B"), (← q r"y:B")] THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"x:B = ring_0 k") THENL [ASM_SIMP_TAC [RING_ADD_LZERO] THEN COND_CASES_TAC THEN ASM_SIMP_TAC [REAL_LE_MAX, REAL_LE_REFL], ALL_TAC] THEN ASM_CASES_TAC (← q r"y:B = ring_0 k") THENL [ASM_SIMP_TAC [RING_ADD_RZERO, REAL_LE_MAX, REAL_LE_REFL], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN COND_CASES_TAC THENL [ASM_SIMP_TAC [REAL_LE_MAX, REAL_ZPOW_LE, REAL_LT_IMP_LE], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"x:B"), (← q r"y:B")] DEDEKIND_VALUATION_ADD) THEN ASM_REWRITE_TAC [INT_MIN_LE, REAL_LE_MAX] THEN MATCH_MP_TAC MONO_OR THEN CONJ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_ZPOW_MONO THEN ASM_REWRITE_TAC [INT_LE_NEG2], X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"x:B = ring_0 k") THEN ASM_REWRITE_TAC [REAL_POS] THEN EQ_TAC THENL [ONCE_REWRITE_TAC [(← GSYM CONTRAPOS_THM)] THEN REWRITE_TAC [INT_NOT_LE, REAL_NOT_LE] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"c:real"), (← q r"&0:int"), (← q r"--(dedekind_valuation (r,k) (h:A->B) P x)")] REAL_ZPOW_MONO_LT) THEN ASM_REWRITE_TAC [REAL_ZPOW_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_INT_ARITH_TAC, DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"c:real"), (← q r"--(dedekind_valuation (r,k) (h:A->B) P x)"), (← q r"&0:int")] REAL_ZPOW_MONO) THEN ASM_REWRITE_TAC [REAL_ZPOW_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_INT_ARITH_TAC]])

  let DEDEKIND_VALUATION_IDEAL_NORM ← prove
    r"!r k (h:A->B) a.
        dedekind_domain r /\ ring_monomorphism(r,k) h /\
        a IN ring_carrier r /\ ~(a = ring_0 r) /\
        FINITE(ring_carrier(quotient_ring r (ideal_generated r {a})))
        ==> FINITE {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
                        ~(dedekind_valuation (r,k) h P (h a) = &0)} /\
            product {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
                         ~(dedekind_valuation (r,k) h P (h a) = &0)}
                    (\P. &(ideal_norm r P) zpow
                         dedekind_valuation (r,k) h P (h a)) =
            &(ideal_norm r (ideal_generated r {a}))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"{P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
         ~(dedekind_valuation (r,k) (h:A->B) P (h a) = &0)} =
    {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
         ideal_generated r {a} SUBSET P}") SUBST1_TAC THENL [GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"P:A->bool") THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_CASES_TAC (← q r"prime_ideal r (P:A->bool)") THEN ASM_REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"P = {ring_0 r:A}") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ideal_generated r {a} SUBSET P <=> (a:A) IN P") SUBST1_TAC THENL [EQ_TAC THEN DISCH_TAC THENL [FIRST_X_ASSUM (MATCH_MP_TAC o (REWRITE_RULE [SUBSET])) THEN MATCH_MP_TAC IDEAL_GENERATED_INC_GEN THEN ASM_REWRITE_TAC [IN_SING], MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_SIMP_TAC [SING_SUBSET, PRIME_IMP_RING_IDEAL]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"a:A")] DEDEKIND_VALUATION_PRIME_IDEAL) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"a:A")] DEDEKIND_VALUATION_IMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [INT_OF_NUM_EQ, INT_OF_NUM_LT] THEN ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_generated r {a:A}")] DEDEKIND_IDEAL_FACTORIZATION) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_generated r {a:A}")] IDEAL_NORM_FACTORIZATION) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN ASM_SIMP_TAC [REAL_OF_NUM_NPRODUCT] THEN MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC (← q r"P:A->bool") THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"a:A")] DEDEKIND_VALUATION_IMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [REAL_ZPOW_NUM, REAL_OF_NUM_POW])

  let DEDEKIND_VALUATION_NORMALIZED_ABSOLUTE_VALUE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"(p /\ q /\ r /\ s) /\ t ==> p /\ q /\ r /\ s /\ t")
    prove
      r"!r k (h:A->B) P (f:B->real).
          dedekind_domain r /\ field_of_fractions (r,k) h /\
          prime_ideal r P /\ ~(P = {ring_0 r}) /\
          FINITE(ring_carrier(quotient_ring r P)) /\
          (!x. f x = if x = ring_0 k then &0
                     else &(ideal_norm r P) zpow
                          --(dedekind_valuation (r,k) h P x))
          ==> 1 < ideal_norm r P /\
              nonarchimedean_absolute_value k f /\
              (!x. x IN ring_carrier k
                   ==> (f x <= &1 <=>
                        x = ring_0 k \/ &0 <= dedekind_valuation (r,k) h P x)) /\
              (!a. a IN ring_carrier r /\ ~(a = ring_0 r)
                   ==> f(h a) *
                       &(ideal_norm r
                          (ideal_pow r P
                            (ideal_valuation r P (ideal_generated r {a})))) =
                       &1)"
      (REWRITE_TAC [NONARCHIMEDEAN_ABSOLUTE_VALUE, (← GSYM CONJ_ASSOC)] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN SUBGOAL_THEN (← q r"1 < ideal_norm r (P:A->bool)") ASSUME_TAC THENL [MATCH_MP_TAC IDEAL_NORM_GT_1 THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP PRIME_IMP_PROPER_IDEAL)) THEN SIMP_TAC [PROPER_IDEAL_ALT], ASM_REWRITE_TAC []] THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [MATCH_MP_TAC (← REWRITE_RULE [NONARCHIMEDEAN_ABSOLUTE_VALUE, (← GSYM CONJ_ASSOC)] DEDEKIND_VALUATION_ABSOLUTE_VALUE) THEN EXISTS_TAC (← q r"&(ideal_norm r (P:A->bool)):real") THEN ASM_REWRITE_TAC [REAL_OF_NUM_LT], X_GEN_TAC (← q r"a:A") THEN STRIP_TAC] THEN SUBGOAL_THEN (← q r"~((h:A->B) a = ring_0 k)") ASSUME_TAC THENL [ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0], ASM_REWRITE_TAC []] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"a:A")] DEDEKIND_VALUATION_IMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"ideal_valuation r P (ideal_generated r {a:A})")] IDEAL_NORM_IDEAL_POW) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN REWRITE_TAC [REAL_ZPOW_POW, (← GSYM REAL_OF_NUM_POW)] THEN MATCH_MP_TAC REAL_MUL_LINV THEN REWRITE_TAC [REAL_POW_EQ_0, REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC)

  -- @@RETURN BEGIN
  return { absolute_value, nonarchimedean_absolute_value,
           NONARCHIMEDEAN_IMP_ABSOLUTE_VALUE, NONARCHIMEDEAN_ABSOLUTE_VALUE,
           ABSOLUTE_VALUE_POS, ABSOLUTE_VALUE_EQ_0, ABSOLUTE_VALUE_POS_LT,
           ABSOLUTE_VALUE_0, ABSOLUTE_VALUE_MUL, ABSOLUTE_VALUE_TRIANGLE,
           ABSOLUTE_VALUE_1, ABSOLUTE_VALUE_NEG, ABSOLUTE_VALUE_SUB,
           ABSOLUTE_VALUE_SUB_LE, ABSOLUTE_VALUE_ABS_SUB_LE, ABSOLUTE_VALUE_POW,
           ABSOLUTE_VALUE_INV, ABSOLUTE_VALUE_DIV, ABSOLUTE_VALUE_RING_SUM,
           ABSOLUTE_VALUE_RING_OF_NUM_LE, ABSOLUTE_VALUE_EQ, ABSOLUTE_VALUE_NONTRIVIAL,
           NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_NUM,
           NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_INT, REAL_POW_EVENTUALLY_GT_LINEAR,
           NONARCHIMEDEAN_ABSOLUTE_VALUE_BOUNDED, NONARCHIMEDEAN_ABSOLUTE_VALUE_CHAR,
           ABSOLUTE_VALUE_FINITE, NONARCHIMEDEAN_ABSOLUTE_VALUE_VALUATION_SUBRING,
           NONARCHIMEDEAN_ABSOLUTE_VALUE_INTEGRAL, DEDEKIND_VALUATION_ABSOLUTE_VALUE,
           DEDEKIND_VALUATION_IDEAL_NORM, DEDEKIND_VALUATION_NORMALIZED_ABSOLUTE_VALUE }
  -- @@RETURN END

end HolANT.DedekindAbsolute
