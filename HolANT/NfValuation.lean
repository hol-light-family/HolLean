/- ========================================================================= -/
/- ANT: Valuations of the elements of a number field k at the ...          -/
/- ========================================================================= -/
/- File: HolANT/NfValuation.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/nf_valuation.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antnfvaluationdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/permutations.ml, Library/ring_det.ml, ANT/ideal_arith.ml, Library/products.ml, ANT/algmisc.ml, Library/matroids.ml, Library/fieldtheory.ml, ANT/integral.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/ideal_norm.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/classgroup.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.NfValuation fills them).

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
import HolLibrary.Permutations
import HolLibrary.RingDet
import HolANT.IdealArith
import HolLibrary.Products
import HolANT.Algmisc
import HolLibrary.Matroids
import HolLibrary.FieldTheory
import HolANT.Integral
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.IdealNorm
import HolLibrary.Isum
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolANT.RingOfIntegers
import HolANT.NormIndex
import HolANT.Classgroup

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.IdealArith
open HolANT.Algmisc
open HolANT.Integral
open HolANT.Dedekind
open HolANT.DedekindStruct
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.IdealNorm
open HolANT.Zlattice
open HolANT.Numfield
open HolANT.RingOfIntegers
open HolANT.NormIndex
open HolANT.Classgroup

namespace HolANT.NfValuation

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (DEDEKIND_DENOMINATOR_IDEAL DEDEKIND_IDEAL_FACTORIZATION
   DEDEKIND_IDEAL_MUL_INTEGRAL DEDEKIND_IDEAL_PRESCRIBED_VALUATIONS
   DEDEKIND_IDEAL_SUBSET_VALUATION DEDEKIND_RING_OF_INTEGERS DEDEKIND_VALUATION
   DEDEKIND_VALUATION_1 DEDEKIND_VALUATION_ADD DEDEKIND_VALUATION_ADD_STRICT
   DEDEKIND_VALUATION_APPROXIMATION DEDEKIND_VALUATION_DIV DEDEKIND_VALUATION_EQ
   DEDEKIND_VALUATION_FINITE DEDEKIND_VALUATION_IMAGE
   DEDEKIND_VALUATION_INTEGRAL DEDEKIND_VALUATION_INV DEDEKIND_VALUATION_MUL
   DEDEKIND_VALUATION_NEG DEDEKIND_VALUATION_POW DEDEKIND_VALUATION_PRIME_IDEAL
   DEDEKIND_VALUATION_UNIT DIVIDES_LE_IMP EXISTS_IN_IMAGE EXP_ONE
   FIELD_IMP_INTEGRAL_DOMAIN FIELD_INV_EQ_0 FIELD_MUL_RINV FINITE_FINITE_UNIONS
   FINITE_IMAGE FINITE_SUBSET FORALL_IN_IMAGE IDEAL_GENERATED_EQ_0
   IDEAL_NORM_IDEAL_POW IDEAL_NORM_IN_IDEAL IDEAL_NORM_POS
   IDEAL_NORM_SUBSET_DIVIDES IDEAL_POW_EQ_ZERO IDEAL_VALUATION_EQ_0
   IDEAL_VALUATION_IDEAL_POW IDEAL_VALUATION_IDEAL_PROD IMAGE_I IMP_CONJ
   INTEGRAL_DOMAIN_MUL_EQ_0 INTEGRAL_DOMAIN_POW_EQ_0
   INTEGRAL_DOMAIN_RING_OF_INTEGERS INT_MAX INT_MUL_RNEG INT_MUL_RZERO
   INT_OF_NUM_ADD INT_OF_NUM_EQ INT_OF_NUM_LE INT_OF_NUM_MUL INT_OF_NUM_OF_INT
   INT_POS IN_ELIM_THM IN_IDEAL_CLASS IN_UNIONS I_DEF I_THM LE_REFL MONO_EXISTS
   NOT_EXISTS_THM NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM
   NUMBER_FIELD_IDEAL_CLASS_BOUND NUMBER_FIELD_IMP_FIELD RING_0 RING_1 RING_DIV
   RING_IDEAL_IDEAL_GENERATED RING_IDEAL_IDEAL_POW RING_INV
   RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_MONOMORPHISM_INCLUSION RING_MUL
   RING_MUL_ASSOC RING_MUL_LID RING_MUL_RZERO RING_OF_INTEGERS
   RING_OF_INTEGERS_DENOMINATOR RING_OF_INTEGERS_FINITE_QUOTIENT
   RING_OF_INTEGERS_SUBSET RING_OF_NUM_1 RING_POW SUBSET field_of_fractions
   ring_div ring_of_integers : thm)
  deriving Inhabited

/-- What nf_valuation.ml uses from Session besides theorems. -/
structure NfValuationDeps where
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
/- nf_valuation.ml phrases from line 73 to 522                            -/
/- ---------------------------------------------------------------------- -/

structure NfValuation where
  -- @@FIELDS
  RING_OF_INTEGERS_FRACTION_FIELD : thm
  NUMBER_FIELD_VALUATION : thm
  NUMBER_FIELD_VALUATION_RING_OF_INTEGERS : thm
  NUMBER_FIELD_VALUATION_1 : thm
  NUMBER_FIELD_VALUATION_MUL : thm
  NUMBER_FIELD_VALUATION_INV : thm
  NUMBER_FIELD_VALUATION_DIV : thm
  NUMBER_FIELD_VALUATION_POW : thm
  NUMBER_FIELD_VALUATION_NEG : thm
  NUMBER_FIELD_VALUATION_ADD : thm
  NUMBER_FIELD_VALUATION_ADD_STRICT : thm
  NUMBER_FIELD_VALUATION_FINITE : thm
  NUMBER_FIELD_VALUATION_INTEGRAL : thm
  NUMBER_FIELD_VALUATION_UNIT : thm
  NUMBER_FIELD_VALUATION_PRIME_IDEAL : thm
  NUMBER_FIELD_VALUATION_EQ : thm
  NUMBER_FIELD_VALUATION_APPROXIMATION : thm
  NUMBER_FIELD_VALUATION_PRINCIPAL_OUTSIDE : thm
  NUMBER_FIELD_DENOMINATOR_IDEAL : thm
  NUMBER_FIELD_IDEAL_MUL_INTEGRAL : thm
  NUMBER_FIELD_ROOT_DENOMINATOR : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupNfValuation [HolBase] (D : NfValuationDeps) :
    ExceptT String IO NfValuation := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_INT_ARITH_TAC, ASM_MESON_TAC, INT_ARITH, INT_ARITH_TAC,
        MESON_TAC, TAUT, .. } := D
  let { DEDEKIND_DENOMINATOR_IDEAL, DEDEKIND_IDEAL_FACTORIZATION,
        DEDEKIND_IDEAL_MUL_INTEGRAL, DEDEKIND_IDEAL_PRESCRIBED_VALUATIONS,
        DEDEKIND_IDEAL_SUBSET_VALUATION, DEDEKIND_RING_OF_INTEGERS, DEDEKIND_VALUATION,
        DEDEKIND_VALUATION_1, DEDEKIND_VALUATION_ADD, DEDEKIND_VALUATION_ADD_STRICT,
        DEDEKIND_VALUATION_APPROXIMATION, DEDEKIND_VALUATION_DIV,
        DEDEKIND_VALUATION_EQ, DEDEKIND_VALUATION_FINITE, DEDEKIND_VALUATION_IMAGE,
        DEDEKIND_VALUATION_INTEGRAL, DEDEKIND_VALUATION_INV, DEDEKIND_VALUATION_MUL,
        DEDEKIND_VALUATION_NEG, DEDEKIND_VALUATION_POW, DEDEKIND_VALUATION_PRIME_IDEAL,
        DEDEKIND_VALUATION_UNIT, DIVIDES_LE_IMP, EXISTS_IN_IMAGE, EXP_ONE,
        FIELD_IMP_INTEGRAL_DOMAIN, FIELD_INV_EQ_0, FIELD_MUL_RINV,
        FINITE_FINITE_UNIONS, FINITE_IMAGE, FINITE_SUBSET, FORALL_IN_IMAGE,
        IDEAL_GENERATED_EQ_0, IDEAL_NORM_IDEAL_POW, IDEAL_NORM_IN_IDEAL,
        IDEAL_NORM_POS, IDEAL_NORM_SUBSET_DIVIDES, IDEAL_POW_EQ_ZERO,
        IDEAL_VALUATION_EQ_0, IDEAL_VALUATION_IDEAL_POW, IDEAL_VALUATION_IDEAL_PROD,
        IMAGE_I, IMP_CONJ, INTEGRAL_DOMAIN_MUL_EQ_0, INTEGRAL_DOMAIN_POW_EQ_0,
        INTEGRAL_DOMAIN_RING_OF_INTEGERS, INT_MAX, INT_MUL_RNEG, INT_MUL_RZERO,
        INT_OF_NUM_ADD, INT_OF_NUM_EQ, INT_OF_NUM_LE, INT_OF_NUM_MUL,
        INT_OF_NUM_OF_INT, INT_POS, IN_ELIM_THM, IN_IDEAL_CLASS, IN_UNIONS, I_DEF,
        I_THM, LE_REFL, MONO_EXISTS, NOT_EXISTS_THM,
        NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM, NUMBER_FIELD_IDEAL_CLASS_BOUND,
        NUMBER_FIELD_IMP_FIELD, RING_0, RING_1, RING_DIV, RING_IDEAL_IDEAL_GENERATED,
        RING_IDEAL_IDEAL_POW, RING_INV, RING_MONOMORPHISM_IMP_HOMOMORPHISM,
        RING_MONOMORPHISM_INCLUSION, RING_MUL, RING_MUL_ASSOC, RING_MUL_LID,
        RING_MUL_RZERO, RING_OF_INTEGERS, RING_OF_INTEGERS_DENOMINATOR,
        RING_OF_INTEGERS_FINITE_QUOTIENT, RING_OF_INTEGERS_SUBSET, RING_OF_NUM_1,
        RING_POW, SUBSET, field_of_fractions, ring_div, ring_of_integers, .. } := D.core1
  -- @@SCOPE END

  let RING_OF_INTEGERS_FRACTION_FIELD ← prove
    r"!k:A ring.
        ring_monomorphism(ring_of_integers k,k) I /\
        (number_field k
         ==> dedekind_domain(ring_of_integers k) /\
             field_of_fractions(ring_of_integers k,k) I)"
    (GEN_TAC THEN SUBGOAL_THEN (← q r"ring_monomorphism(ring_of_integers k:A ring,k) I") ASSUME_TAC THENL [REWRITE_TAC [ring_of_integers, I_DEF, RING_MONOMORPHISM_INCLUSION], ASM_REWRITE_TAC [field_of_fractions, RING_OF_INTEGERS, I_THM] THEN DISCH_TAC] THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, NUMBER_FIELD_IMP_FIELD] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A")] RING_OF_INTEGERS_DENOMINATOR) THEN ASM_REWRITE_TAC [] THEN MESON_TAC [])

  let NUMBER_FIELD_VALUATION ← prove
    r"!k:A ring P x a b.
        number_field k /\
        prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
        x IN ring_carrier k /\
        a IN ring_carrier(ring_of_integers k) /\
        b IN ring_carrier(ring_of_integers k) /\
        ~(a = ring_0 k) /\ ~(b = ring_0 k) /\ ring_mul k b x = a
        ==> dedekind_valuation (ring_of_integers k,k) I P x =
            &(ideal_valuation (ring_of_integers k) P
               (ideal_generated (ring_of_integers k) {a})) -
            &(ideal_valuation (ring_of_integers k) P
               (ideal_generated (ring_of_integers k) {b}))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_FRACTION_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS, I_THM] (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"k:A ring"), (← q r"I:A->A")] DEDEKIND_VALUATION)) THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_VALUATION_RING_OF_INTEGERS ← prove
    r"!k:A ring P x.
        number_field k /\
        prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
        x IN ring_carrier(ring_of_integers k) /\ ~(x = ring_0 k)
        ==> dedekind_valuation (ring_of_integers k,k) I P x =
            &(ideal_valuation (ring_of_integers k) P
               (ideal_generated (ring_of_integers k) {x}))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_FRACTION_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS, I_THM] (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"k:A ring"), (← q r"I:A->A")] DEDEKIND_VALUATION_IMAGE)) THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_VALUATION_1 ← prove
    r"!k:A ring P.
        field k
        ==> dedekind_valuation (ring_of_integers k,k) I P (ring_1 k) = &0"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC DEDEKIND_VALUATION_1 THEN ASM_REWRITE_TAC [RING_OF_INTEGERS_FRACTION_FIELD])

  let NUMBER_FIELD_VALUATION_MUL ← prove
    r"!k:A ring P x y.
        number_field k /\
        prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
        x IN ring_carrier k /\ ~(x = ring_0 k) /\
        y IN ring_carrier k /\ ~(y = ring_0 k)
        ==> dedekind_valuation (ring_of_integers k,k) I P (ring_mul k x y) =
            dedekind_valuation (ring_of_integers k,k) I P x +
            dedekind_valuation (ring_of_integers k,k) I P y"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_FRACTION_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS, I_THM] (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"k:A ring"), (← q r"I:A->A")] DEDEKIND_VALUATION_MUL)) THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_VALUATION_INV ← prove
    r"!k:A ring P x.
        number_field k /\
        prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
        x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> dedekind_valuation (ring_of_integers k,k) I P (ring_inv k x) =
            --(dedekind_valuation (ring_of_integers k,k) I P x)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_FRACTION_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS, I_THM] (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"k:A ring"), (← q r"I:A->A")] DEDEKIND_VALUATION_INV)) THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_VALUATION_DIV ← prove
    r"!k:A ring P x y.
        number_field k /\
        prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
        x IN ring_carrier k /\ ~(x = ring_0 k) /\
        y IN ring_carrier k /\ ~(y = ring_0 k)
        ==> dedekind_valuation (ring_of_integers k,k) I P (ring_div k x y) =
            dedekind_valuation (ring_of_integers k,k) I P x -
            dedekind_valuation (ring_of_integers k,k) I P y"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_FRACTION_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS, I_THM] (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"k:A ring"), (← q r"I:A->A")] DEDEKIND_VALUATION_DIV)) THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_VALUATION_POW ← prove
    r"!k:A ring P x n.
        number_field k /\
        prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
        x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> dedekind_valuation (ring_of_integers k,k) I P (ring_pow k x n) =
            &n * dedekind_valuation (ring_of_integers k,k) I P x"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_FRACTION_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS, I_THM] (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"k:A ring"), (← q r"I:A->A")] DEDEKIND_VALUATION_POW)) THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_VALUATION_NEG ← prove
    r"!k:A ring P x.
        x IN ring_carrier k
        ==> dedekind_valuation (ring_of_integers k,k) I P (ring_neg k x) =
            dedekind_valuation (ring_of_integers k,k) I P x"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC DEDEKIND_VALUATION_NEG THEN ASM_SIMP_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_OF_INTEGERS_FRACTION_FIELD])

  let NUMBER_FIELD_VALUATION_ADD ← prove
    r"!k:A ring P x y.
        number_field k /\
        prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
        x IN ring_carrier k /\ y IN ring_carrier k /\
        ~(ring_add k x y = ring_0 k)
        ==> min (dedekind_valuation (ring_of_integers k,k) I P x)
                (dedekind_valuation (ring_of_integers k,k) I P y)
            <= dedekind_valuation (ring_of_integers k,k) I P (ring_add k x y)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_FRACTION_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS, I_THM] (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"k:A ring"), (← q r"I:A->A")] DEDEKIND_VALUATION_ADD)) THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_VALUATION_ADD_STRICT ← prove
    r"!k:A ring P x y.
        number_field k /\
        prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
        x IN ring_carrier k /\ ~(x = ring_0 k) /\ y IN ring_carrier k /\
        dedekind_valuation (ring_of_integers k,k) I P x <
        dedekind_valuation (ring_of_integers k,k) I P y
        ==> dedekind_valuation (ring_of_integers k,k) I P (ring_add k x y) =
            dedekind_valuation (ring_of_integers k,k) I P x"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_FRACTION_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS, I_THM] (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"k:A ring"), (← q r"I:A->A")] DEDEKIND_VALUATION_ADD_STRICT)) THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_VALUATION_FINITE ← prove
    r"!k:A ring x.
        number_field k /\ x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> FINITE
             {P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
                  ~(dedekind_valuation (ring_of_integers k,k) I P x = &0)}"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_FRACTION_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS, I_THM] (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"k:A ring"), (← q r"I:A->A")] DEDEKIND_VALUATION_FINITE)) THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_VALUATION_INTEGRAL ← prove
    r"!k:A ring x.
        number_field k /\ x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> (x IN ring_carrier(ring_of_integers k) <=>
             !P. prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k})
                 ==> &0 <= dedekind_valuation (ring_of_integers k,k) I P x)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_FRACTION_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS, I_THM, IMAGE_I] (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"k:A ring"), (← q r"I:A->A")] DEDEKIND_VALUATION_INTEGRAL)) THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_VALUATION_UNIT ← prove
    r"!k:A ring x.
        number_field k /\ x IN ring_carrier k
        ==> (ring_unit (ring_of_integers k) x <=>
             ~(x = ring_0 k) /\
             !P. prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k})
                 ==> dedekind_valuation (ring_of_integers k,k) I P x = &0)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_FRACTION_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS, I_THM, IMAGE_I, IN_ELIM_THM] (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"k:A ring"), (← q r"I:A->A")] DEDEKIND_VALUATION_UNIT)) THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_VALUATION_PRIME_IDEAL ← prove
    r"!k:A ring P x.
        number_field k /\
        prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
        x IN ring_carrier(ring_of_integers k) /\ ~(x = ring_0 k)
        ==> (x IN P <=> &0 < dedekind_valuation (ring_of_integers k,k) I P x)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_FRACTION_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS, I_THM] (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"k:A ring"), (← q r"I:A->A")] DEDEKIND_VALUATION_PRIME_IDEAL)) THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_VALUATION_EQ ← prove
    r"!k:A ring x y.
        number_field k /\
        x IN ring_carrier k /\ ~(x = ring_0 k) /\
        y IN ring_carrier k /\ ~(y = ring_0 k)
        ==> ((!P. prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k})
                  ==> dedekind_valuation (ring_of_integers k,k) I P x =
                      dedekind_valuation (ring_of_integers k,k) I P y) <=>
             ?u. ring_unit (ring_of_integers k) u /\ x = ring_mul k u y)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_FRACTION_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS, I_THM] (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"k:A ring"), (← q r"I:A->A")] DEDEKIND_VALUATION_EQ)) THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_VALUATION_APPROXIMATION ← prove
    r"!k s (e:(A->bool)->int).
        number_field k /\ FINITE s /\
        (!P. P IN s ==> prime_ideal (ring_of_integers k) P /\
                        ~(P = {ring_0 k}))
        ==> ?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\
                (!P. P IN s
                     ==> dedekind_valuation (ring_of_integers k,k) I P x =
                         e P) /\
                (!P. prime_ideal (ring_of_integers k) P /\
                     ~(P = {ring_0 k}) /\ ~(P IN s)
                     ==> &0 <= dedekind_valuation (ring_of_integers k,k) I
                                                  P x)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"s:(A->bool)->bool"), (← q r"e:(A->bool)->int")] DEDEKIND_VALUATION_APPROXIMATION) THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, NUMBER_FIELD_IMP_FIELD, RING_OF_INTEGERS_FRACTION_FIELD, RING_OF_INTEGERS])

  let NUMBER_FIELD_VALUATION_PRINCIPAL_OUTSIDE ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let v1 ← GSYM INT_OF_NUM_ADD
    let v2 ← GSYM INT_OF_NUM_EQ
    let q3 ← q r"j0:A->bool"
    let q4 ← q r"P:A->bool"
    let q5 ← q r"ring_of_integers k:A ring"
    let v6 ← ISPECL [q5, q4, q3] IDEAL_VALUATION_EQ_0
    let q7 ← q r"ideal_valuation (ring_of_integers k) (P:A->bool)"
    let q8 ← q r"a:A"
    let q9 ← q r"b:A"
    let q10 ← q r"ring_mul k (ring_inv k a) b:A"
    let q11 ← q r"P:A->bool"
    let q12 ← q r"k:A ring"
    let v13 ← ISPECL [q12, q11, q10, q9, q8] NUMBER_FIELD_VALUATION
    let q14 ← q r"j0:A->bool"
    let q15 ← q r"P:A->bool"
    let q16 ← q r"ring_mul k (ring_inv k a) b:A"
    let q17 ← q r"(a:A) IN ring_carrier k /\ (b:A) IN ring_carrier k"
    let q18 ← q r"j0:A->bool"
    let q19 ← q r"j:A->bool"
    let q20 ← q r"j:A->bool"
    let q21 ← q r"j:A->bool"
    let q22 ← q r"ring_of_integers k:A ring"
    let v23 ← ISPECL [q22, q21] DEDEKIND_IDEAL_FACTORIZATION
    let q24 ← q r"j:A->bool"
    let q25 ← q r"UNIONS (IMAGE (\j. {P | prime_ideal (ring_of_integers k) P /\
                              ~(P = {ring_0 k}) /\ j SUBSET P})
                    {j | ring_ideal (ring_of_integers k) j /\
                         ~(j = {ring_0 k}) /\
                         ideal_norm (ring_of_integers k:A ring) j <= c})"
    let q26 ← q r"c:num"
    let p27 ← prove r"!k:A ring.
        number_field k
        ==> ?t. FINITE t /\
                (!P. P IN t ==> prime_ideal (ring_of_integers k) P /\
                                ~(P = {ring_0 k})) /\
                !j. ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
                    ==> ?y. y IN ring_carrier k /\ ~(y = ring_0 k) /\
                            !P. prime_ideal (ring_of_integers k) P /\
                                ~(P = {ring_0 k}) /\ ~(P IN t)
                                ==> dedekind_valuation
                                      (ring_of_integers k,k) I P y =
                                    &(ideal_valuation (ring_of_integers k)
                                        P j)" (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_RING_OF_INTEGERS)) THEN FIRST_ASSUM ((X_CHOOSE_TAC q26) o (MATCH_MP NUMBER_FIELD_IDEAL_CLASS_BOUND)) THEN EXISTS_TAC q25 THEN REWRITE_TAC [IN_UNIONS, EXISTS_IN_IMAGE, IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL [ASM_SIMP_TAC [FINITE_FINITE_UNIONS, FINITE_IMAGE, FORALL_IN_IMAGE, NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM] THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC q24 THEN STRIP_TAC THEN MP_TAC v23 THEN ASM_SIMP_TAC [RING_OF_INTEGERS], MESON_TAC [], X_GEN_TAC q20 THEN STRIP_TAC] THEN FIRST_X_ASSUM (MP_TAC o (SPEC q19)) THEN ASM_REWRITE_TAC [IN_IDEAL_CLASS, RING_OF_INTEGERS] THEN DISCH_THEN (X_CHOOSE_THEN q18 STRIP_ASSUME_TAC) THEN SUBGOAL_THEN q17 STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN EXISTS_TAC q16 THEN ASM_SIMP_TAC [RING_MUL, RING_INV, INTEGRAL_DOMAIN_MUL_EQ_0, FIELD_IMP_INTEGRAL_DOMAIN, FIELD_INV_EQ_0] THEN X_GEN_TAC q15 THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC q14) o (REWRITE_RULE [NOT_EXISTS_THM]))) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC v13 THEN ASM_SIMP_TAC [RING_MUL, RING_INV, RING_MUL_ASSOC, FIELD_MUL_RINV, RING_MUL_LID] THEN DISCH_THEN SUBST1_TAC THEN FIRST_X_ASSUM (MP_TAC o (AP_TERM q7)) THEN MP_TAC v6 THEN ASM_SIMP_TAC [IDEAL_VALUATION_IDEAL_PROD, RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0, RING_OF_INTEGERS] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN REWRITE_TAC [v2, v1] THEN INT_ARITH_TAC)
    let class_lemma := p27
    let q28 ← q r"&0 <= max (x:int) (&0)"
    let r29 ← INT_ARITH q28
    let v30 ← GSYM ring_div
    let q31 ← q r"ring_div k y1 y2:A"
    let q32 ← q r"y2:A"
    let q33 ← q r"y1:A"
    let q34 ← q r"j2:A->bool"
    let q35 ← q r"j1:A->bool"
    let q36 ← q r"&0 <= max (x:int) (&0)"
    let r37 ← INT_ARITH q36
    let v38 ← GSYM INT_OF_NUM_EQ
    let v39 ← REWRITE_RULE [IMP_CONJ] FINITE_SUBSET
    let q40 ← q r"(p /\ q) /\ (r ==> s ==> t) ==> (p ==> r) ==> (q ==> s) ==> t"
    let r41 ← TAUT q40
    let q42 ← q r"\P:A->bool. num_of_int(max (e P) (&0))"
    let q43 ← q r"ring_of_integers k:A ring"
    let v44 ← ISPECL [q43, q42] DEDEKIND_IDEAL_PRESCRIBED_VALUATIONS
    let q45 ← q r"\P:A->bool. num_of_int(max (--(e P)) (&0))"
    let q46 ← q r"ring_of_integers k:A ring"
    let v47 ← ISPECL [q46, q45] DEDEKIND_IDEAL_PRESCRIBED_VALUATIONS
    let q48 ← q r"e:(A->bool)->int"
    let q49 ← q r"t:(A->bool)->bool"
    prove
      r"!k:A ring.
          number_field k
          ==> ?t. FINITE t /\
                  (!P. P IN t
                       ==> prime_ideal (ring_of_integers k) P /\
                           ~(P = {ring_0 k})) /\
                  !e. FINITE {P | prime_ideal (ring_of_integers k) P /\
                                  ~(P = {ring_0 k}) /\ ~(e P = &0)}
                      ==> ?y. y IN ring_carrier k /\ ~(y = ring_0 k) /\
                              !P. prime_ideal (ring_of_integers k) P /\
                                  ~(P = {ring_0 k}) /\ ~(P IN t)
                                  ==> dedekind_valuation
                                        (ring_of_integers k,k) I P y = e P"
      (GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP class_lemma)) THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC q49 THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "class"))) THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC q48 THEN DISCH_TAC THEN MP_TAC v47 THEN MP_TAC v44 THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_OF_INTEGERS] THEN MATCH_MP_TAC r41 THEN CONJ_TAC THENL [CONJ_TAC THEN FIRST_ASSUM (MATCH_MP_TAC o (MATCH_MP v39)) THEN REWRITE_TAC [SUBSET, IN_ELIM_THM, v38] THEN SIMP_TAC [INT_OF_NUM_OF_INT, r37] THEN INT_ARITH_TAC, DISCH_THEN (X_CHOOSE_THEN q35 STRIP_ASSUME_TAC) THEN DISCH_THEN (X_CHOOSE_THEN q34 STRIP_ASSUME_TAC)] THEN REMOVE_THEN "class" (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"j2:A->bool") th) THEN MP_TAC (← SPEC (← q r"j1:A->bool") th))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN q33 STRIP_ASSUME_TAC) THEN DISCH_THEN (X_CHOOSE_THEN q32 STRIP_ASSUME_TAC) THEN EXISTS_TAC q31 THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN ASM_SIMP_TAC [RING_DIV, ring_div, INTEGRAL_DOMAIN_MUL_EQ_0, RING_INV, FIELD_IMP_INTEGRAL_DOMAIN, FIELD_INV_EQ_0] THEN ASM_SIMP_TAC [v30, NUMBER_FIELD_VALUATION_DIV] THEN SIMP_TAC [INT_OF_NUM_OF_INT, r29] THEN INT_ARITH_TAC)

  let NUMBER_FIELD_DENOMINATOR_IDEAL ← prove
    r"!k:A ring x.
        number_field k /\ x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> ?J. ring_ideal (ring_of_integers k) J /\ ~(J = {ring_0 k}) /\
                !P. prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k})
                    ==> &(ideal_valuation (ring_of_integers k) P J):int =
                        max (&0)
                         (--dedekind_valuation (ring_of_integers k,k) I P x)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_FRACTION_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS, I_THM] (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"k:A ring"), (← q r"I:A->A")] DEDEKIND_DENOMINATOR_IDEAL)) THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_IDEAL_MUL_INTEGRAL ← prove
    r"!k:A ring J x c.
        number_field k /\ ring_ideal (ring_of_integers k) J /\
        x IN ring_carrier k /\
        (!P. prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k})
             ==> &0 <= &(ideal_valuation (ring_of_integers k) P J) +
                       dedekind_valuation (ring_of_integers k,k) I P x) /\
        c IN J
        ==> ring_mul k c x IN ring_carrier(ring_of_integers k)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_FRACTION_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS, I_THM, IMAGE_I] (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"J:A->bool")] DEDEKIND_IDEAL_MUL_INTEGRAL)) THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_ROOT_DENOMINATOR ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"1 <= n ==> n = 0 ==> m = 0")
    let r2 ← TAUT (← q r"p /\ (p ==> q /\ r) ==> p /\ q /\ r")
    let r3 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!k:A ring x a p.
          number_field k /\ x IN ring_carrier k /\
          a IN ring_carrier(ring_of_integers k) /\ ~(a = ring_0 k) /\
          ring_mul k a (ring_pow k x p) IN ring_carrier(ring_of_integers k)
          ==> ?b. 1 <= b /\
                  b EXP p <= ideal_norm (ring_of_integers k)
                               (ideal_generated (ring_of_integers k) {a}) /\
                  ring_mul k (ring_of_num k b) x
                  IN ring_carrier(ring_of_integers k)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_RING_OF_INTEGERS)) THEN SUBGOAL_THEN (← q r"~(ideal_generated (ring_of_integers k) {a} = {ring_0 k:A}) /\
      FINITE(ring_carrier(quotient_ring (ring_of_integers k)
              (ideal_generated (ring_of_integers k) {a})))") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r3 THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"a:A")] IDEAL_GENERATED_EQ_0) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], DISCH_TAC THEN MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED]], ALL_TAC] THEN ASM_CASES_TAC (← q r"x:A = ring_0 k") THENL [EXISTS_TAC (← q r"1") THEN ASM_SIMP_TAC [EXP_ONE, IDEAL_NORM_POS, LE_REFL, RING_OF_NUM_1, RING_MUL_RZERO, RING_1] THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_0) THEN REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A")] NUMBER_FIELD_DENOMINATOR_IDEAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"J:A->bool") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "val")))) THEN SUBGOAL_THEN (← q r"FINITE(ring_carrier(quotient_ring (ring_of_integers k) (J:A->bool)))") ASSUME_TAC THENL [MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_REWRITE_TAC [], ALL_TAC] THEN EXISTS_TAC (← q r"ideal_norm (ring_of_integers k) (J:A->bool)") THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_NORM_POS THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN CONJ_TAC THENL [SUBGOAL_THEN (← q r"a IN ring_carrier k /\ ~(ring_pow k x p = ring_0 k) /\
        ~(ring_mul k a (ring_pow k x p) = ring_0 k:A)") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r2 THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], DISCH_TAC] THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_MUL_EQ_0, INTEGRAL_DOMAIN_POW_EQ_0, RING_POW, FIELD_IMP_INTEGRAL_DOMAIN], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(ideal_pow (ring_of_integers k) J p = {ring_0 k:A})") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"J:A->bool"), (← q r"p:num")] IDEAL_POW_EQ_ZERO) THEN ASM_SIMP_TAC [RING_OF_INTEGERS, INTEGRAL_DOMAIN_RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"J:A->bool"), (← q r"p:num")] IDEAL_NORM_IDEAL_POW) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN MATCH_MP_TAC DIVIDES_LE_IMP THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_NORM_SUBSET_DIVIDES, MATCH_MP_TAC r1 THEN MATCH_MP_TAC IDEAL_NORM_POS THEN ASM_REWRITE_TAC []] THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW, RING_IDEAL_IDEAL_GENERATED] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ideal_generated (ring_of_integers k) {a:A}"), (← q r"ideal_pow (ring_of_integers k) J p:A->bool")] DEDEKIND_IDEAL_SUBSET_VALUATION) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS, RING_IDEAL_IDEAL_POW, RING_IDEAL_IDEAL_GENERATED] THEN DISCH_THEN SUBST1_TAC THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"J:A->bool"), (← q r"p:num")] IDEAL_VALUATION_IDEAL_POW) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"P:A->bool"), (← q r"a:A")] NUMBER_FIELD_VALUATION_RING_OF_INTEGERS) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_mul k a (ring_pow k x p):A")] NUMBER_FIELD_VALUATION_INTEGRAL) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"P:A->bool"), (← q r"a:A"), (← q r"ring_pow k x p:A")] NUMBER_FIELD_VALUATION_MUL) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"P:A->bool"), (← q r"x:A"), (← q r"p:num")] NUMBER_FIELD_VALUATION_POW) THEN ASM_SIMP_TAC [RING_POW, RING_MUL] THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_THEN (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN ASM_REWRITE_TAC [(← GSYM INT_OF_NUM_LE), (← GSYM INT_OF_NUM_MUL)] THEN USE_THEN "val" (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [INT_MAX] THEN COND_CASES_TAC THEN REWRITE_TAC [INT_MUL_RZERO, INT_MUL_RNEG, INT_POS] THEN ASM_INT_ARITH_TAC, ALL_TAC] THEN MATCH_MP_TAC NUMBER_FIELD_IDEAL_MUL_INTEGRAL THEN EXISTS_TAC (← q r"J:A->bool") THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN USE_THEN "val" (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], INT_ARITH_TAC], MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"J:A->bool")] IDEAL_NORM_IN_IDEAL) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS]])

  -- @@RETURN BEGIN
  return { RING_OF_INTEGERS_FRACTION_FIELD, NUMBER_FIELD_VALUATION,
           NUMBER_FIELD_VALUATION_RING_OF_INTEGERS, NUMBER_FIELD_VALUATION_1,
           NUMBER_FIELD_VALUATION_MUL, NUMBER_FIELD_VALUATION_INV,
           NUMBER_FIELD_VALUATION_DIV, NUMBER_FIELD_VALUATION_POW,
           NUMBER_FIELD_VALUATION_NEG, NUMBER_FIELD_VALUATION_ADD,
           NUMBER_FIELD_VALUATION_ADD_STRICT, NUMBER_FIELD_VALUATION_FINITE,
           NUMBER_FIELD_VALUATION_INTEGRAL, NUMBER_FIELD_VALUATION_UNIT,
           NUMBER_FIELD_VALUATION_PRIME_IDEAL, NUMBER_FIELD_VALUATION_EQ,
           NUMBER_FIELD_VALUATION_APPROXIMATION,
           NUMBER_FIELD_VALUATION_PRINCIPAL_OUTSIDE, NUMBER_FIELD_DENOMINATOR_IDEAL,
           NUMBER_FIELD_IDEAL_MUL_INTEGRAL, NUMBER_FIELD_ROOT_DENOMINATOR }
  -- @@RETURN END

end HolANT.NfValuation
