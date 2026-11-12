/- ========================================================================= -/
/- ANT: Relative integrality, traces, norms and units of number ...        -/
/- ========================================================================= -/
/- File: HolANT/Integrality.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/integrality.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antintegralitydiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, ANT/integral.ml, Library/isum.ml, Library/products.ml, ANT/algmisc.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/classgroup.ml, ANT/nf_valuation.ml, ANT/prime_split.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/relative_split.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.Integrality fills them).

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
import HolANT.Integral
import HolLibrary.Isum
import HolLibrary.Products
import HolANT.Algmisc
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
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

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.Integral
open HolANT.Algmisc
open HolANT.Zlattice
open HolANT.Numfield
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

namespace HolANT.Integrality

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD_CLAUSES ALGEBRA_NORM_MINIMAL_POLYNOMIAL ALGEBRA_NORM_UNIT AND_FORALL_THM
   EQ_TRANS EXTENSION_DEGREE_EQ_0 FIELD_EXTENSION_SUBFIELD_GENERATED
   FIELD_MUL_LINV FIELD_SUBFIELD_GENERATED FINITE_EXTENSION_SUBFIELD_GENERATED
   FINITE_IMP_ALGEBRAIC_EXTENSION FINITE_IMP_FIELD_EXTENSION FORALL_IN_IMAGE
   FUN_EQ_THM FUN_IN_IMAGE IMAGE_I INSERT_SUBSET INTEGER_RING_UNIT
   INTEGRALLY_CLOSED_ALGEBRA_TRACE_NORM INTEGRALLY_CLOSED_MINIMAL_POLYNOMIAL
   INTEGRALLY_CLOSED_RING_OF_INTEGERS INTEGRALLY_CLOSED_UNIT_NORM
   INTEGRAL_CLOSURE_SUBRING INTEGRAL_CLOSURE_SUPSET_IMAGE
   INTEGRAL_ELEMENT_INTERMEDIATE INTEGRAL_ELEMENT_SUBRING_GENERATED
   INTEGRAL_ELEMENT_TRANS IN_ELIM_THM IN_IDEAL_GENERATED_SELF IN_INSERT
   IN_NUMSEG IN_RING_IDEAL_LMUL IN_RING_IDEAL_NEG IN_RING_IDEAL_RMUL
   IN_RING_IDEAL_SUM IN_SING IN_SUBRING_0 I_O_ID I_THM LEFT_IMP_EXISTS_THM LE_0
   MINIMAL_POLYNOMIAL MONO_EXISTS NUMBER_FIELD_HOMOMORPHIC_PREIMAGE
   NUMBER_FIELD_IMP_FIELD NUMBER_FIELD_INTEGRAL_MULTIPLE
   NUMBER_FIELD_NORM_INTEGRAL_BASIS NUMBER_FIELD_TOWER_LAW
   POLY_EXTEND_UNIVARIATE PRIMITIVE_ELEMENT_THEOREM RING_1 RING_HOMOMORPHISM_1
   RING_HOMOMORPHISM_FROM_SUBRING_GENERATED
   RING_HOMOMORPHISM_INTEGER_RING_OF_INT RING_HOMOMORPHISM_IN_CARRIER
   RING_HOMOMORPHISM_MUL RING_HOMOMORPHISM_NEG RING_HOMOMORPHISM_POW
   RING_HOMOMORPHISM_RING_OF_INT RING_HOMOMORPHISM_RING_OF_INTEGERS
   RING_HOMOMORPHISM_SUBFIELD_INCLUSION RING_IDEAL_IDEAL_GENERATED
   RING_IDEAL_IMP_SUBSET RING_INV RING_MUL RING_MUL_IN_SUBRING_GENERATED
   RING_MUL_RID RING_NEG RING_OF_INT RING_OF_INTEGERS RING_OF_INTEGERS_CARRIER
   RING_OF_INTEGERS_FRACTION_FIELD RING_OF_INTEGERS_FREE
   RING_OF_INTEGERS_PRIME_SUBFIELD_CARRIER RING_OF_INTEGERS_SUBSET RING_OF_INT_1
   RING_OF_INT_EQ_0_CHAR_0 RING_OF_INT_EQ_CHAR_0 RING_OF_INT_NEG RING_POW
   RING_RNEG_UNIQUE RING_SUM RING_SUM_CLAUSES_LEFT RING_SUM_RING_OF_INTEGERS
   RING_UNIT_IN_CARRIER SEPARABLE_EXTENSION_CHAR0 SING_SUBSET
   SUBFIELD_GENERATED_INC_GEN SUBFIELD_GENERATED_MINIMAL
   SUBFIELD_GENERATED_SUPERSET SUBFIELD_SUBFIELD_GENERATED
   SUBRING_GENERATED_INC_GEN SUBRING_GENERATED_MINIMAL
   SUBRING_GENERATED_SUPERSET SUBRING_SUBFIELD_GENERATED
   SUBRING_SUBRING_GENERATED SUBSET algebraic_extension field_extension
   number_field o_THM ring_of_integers ring_pow ring_unit : thm)
  deriving Inhabited

/-- What integrality.ml uses from Session besides theorems. -/
structure IntegralityDeps where
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
/- integrality.ml phrases from line 53 to 431                             -/
/- ---------------------------------------------------------------------- -/

structure Integrality where
  -- @@FIELDS
  RING_OF_INTEGERS_INTEGRAL_ELEMENT : thm
  RING_OF_INTEGERS_MINIMAL_POLYNOMIAL : thm
  RING_OF_INTEGERS_MINIMAL_POLYNOMIAL_Q : thm
  NUMBER_FIELD_TRACE_INTEGRAL : thm
  NUMBER_FIELD_NORM_INTEGRAL : thm
  RING_OF_INTEGERS_UNIT_NORM : thm
  RING_OF_INTEGERS_UNIT_NORM_Q : thm
  NUMBER_FIELD_NORM_MULTIPLE : thm
  NUMBER_FIELD_INTEGRAL_PRIMITIVE_ELEMENT : thm
  NUMBER_FIELD_INTEGRAL_PRIMITIVE_ELEMENT_Q : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupIntegrality [HolBase] (D : IntegralityDeps) :
    ExceptT String IO Integrality := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, RING_RULE, SET_RULE, SET_TAC, TAUT, .. } := D
  let { ADD_CLAUSES, ALGEBRA_NORM_MINIMAL_POLYNOMIAL, ALGEBRA_NORM_UNIT,
        AND_FORALL_THM, EQ_TRANS, EXTENSION_DEGREE_EQ_0,
        FIELD_EXTENSION_SUBFIELD_GENERATED, FIELD_MUL_LINV, FIELD_SUBFIELD_GENERATED,
        FINITE_EXTENSION_SUBFIELD_GENERATED, FINITE_IMP_ALGEBRAIC_EXTENSION,
        FINITE_IMP_FIELD_EXTENSION, FORALL_IN_IMAGE, FUN_EQ_THM, FUN_IN_IMAGE, IMAGE_I,
        INSERT_SUBSET, INTEGER_RING_UNIT, INTEGRALLY_CLOSED_ALGEBRA_TRACE_NORM,
        INTEGRALLY_CLOSED_MINIMAL_POLYNOMIAL, INTEGRALLY_CLOSED_RING_OF_INTEGERS,
        INTEGRALLY_CLOSED_UNIT_NORM, INTEGRAL_CLOSURE_SUBRING,
        INTEGRAL_CLOSURE_SUPSET_IMAGE, INTEGRAL_ELEMENT_INTERMEDIATE,
        INTEGRAL_ELEMENT_SUBRING_GENERATED, INTEGRAL_ELEMENT_TRANS, IN_ELIM_THM,
        IN_IDEAL_GENERATED_SELF, IN_INSERT, IN_NUMSEG, IN_RING_IDEAL_LMUL,
        IN_RING_IDEAL_NEG, IN_RING_IDEAL_RMUL, IN_RING_IDEAL_SUM, IN_SING,
        IN_SUBRING_0, I_O_ID, I_THM, LEFT_IMP_EXISTS_THM, LE_0, MINIMAL_POLYNOMIAL,
        MONO_EXISTS, NUMBER_FIELD_HOMOMORPHIC_PREIMAGE, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_INTEGRAL_MULTIPLE, NUMBER_FIELD_NORM_INTEGRAL_BASIS,
        NUMBER_FIELD_TOWER_LAW, POLY_EXTEND_UNIVARIATE, PRIMITIVE_ELEMENT_THEOREM,
        RING_1, RING_HOMOMORPHISM_1, RING_HOMOMORPHISM_FROM_SUBRING_GENERATED,
        RING_HOMOMORPHISM_INTEGER_RING_OF_INT, RING_HOMOMORPHISM_IN_CARRIER,
        RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_NEG, RING_HOMOMORPHISM_POW,
        RING_HOMOMORPHISM_RING_OF_INT, RING_HOMOMORPHISM_RING_OF_INTEGERS,
        RING_HOMOMORPHISM_SUBFIELD_INCLUSION, RING_IDEAL_IDEAL_GENERATED,
        RING_IDEAL_IMP_SUBSET, RING_INV, RING_MUL, RING_MUL_IN_SUBRING_GENERATED,
        RING_MUL_RID, RING_NEG, RING_OF_INT, RING_OF_INTEGERS,
        RING_OF_INTEGERS_CARRIER, RING_OF_INTEGERS_FRACTION_FIELD,
        RING_OF_INTEGERS_FREE, RING_OF_INTEGERS_PRIME_SUBFIELD_CARRIER,
        RING_OF_INTEGERS_SUBSET, RING_OF_INT_1, RING_OF_INT_EQ_0_CHAR_0,
        RING_OF_INT_EQ_CHAR_0, RING_OF_INT_NEG, RING_POW, RING_RNEG_UNIQUE, RING_SUM,
        RING_SUM_CLAUSES_LEFT, RING_SUM_RING_OF_INTEGERS, RING_UNIT_IN_CARRIER,
        SEPARABLE_EXTENSION_CHAR0, SING_SUBSET, SUBFIELD_GENERATED_INC_GEN,
        SUBFIELD_GENERATED_MINIMAL, SUBFIELD_GENERATED_SUPERSET,
        SUBFIELD_SUBFIELD_GENERATED, SUBRING_GENERATED_INC_GEN,
        SUBRING_GENERATED_MINIMAL, SUBRING_GENERATED_SUPERSET,
        SUBRING_SUBFIELD_GENERATED, SUBRING_SUBRING_GENERATED, SUBSET,
        algebraic_extension, field_extension, number_field, o_THM, ring_of_integers,
        ring_pow, ring_unit, .. } := D.core1
  -- @@SCOPE END

  let RING_OF_INTEGERS_INTEGRAL_ELEMENT ← prove
    r"!k:A ring l:B ring h x.
        ring_homomorphism(k,l) h
        ==> (integral_element (ring_of_integers k,l) h x <=>
             x IN ring_carrier(ring_of_integers l))"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_homomorphism(ring_of_integers k,l) (h:A->B)") ASSUME_TAC THENL [REWRITE_TAC [ring_of_integers] THEN MATCH_MP_TAC RING_HOMOMORPHISM_FROM_SUBRING_GENERATED THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_homomorphism(integer_ring,ring_of_integers k) (ring_of_int k:int->A)") ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"ring_of_integers(k:A ring)") RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"(h:A->B) o ring_of_int k = ring_of_int l") ASSUME_TAC THENL [REWRITE_TAC [FUN_EQ_THM, o_THM] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_RING_OF_INT], ALL_TAC] THEN REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM] THEN EQ_TAC THENL [DISCH_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN MATCH_MP_TAC INTEGRAL_ELEMENT_TRANS THEN EXISTS_TAC (← q r"ring_of_integers(k:A ring)") THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"y:A") THEN REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC [ring_of_integers] THEN wPart Except.ok (lhand o rand) INTEGRAL_ELEMENT_SUBRING_GENERATED THEN REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN ANTS_TAC THENL [CONJ_TAC THENL [MATCH_MP_TAC INTEGRAL_CLOSURE_SUBRING THEN REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT], MATCH_MP_TAC INTEGRAL_CLOSURE_SUPSET_IMAGE THEN REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT]], DISCH_THEN SUBST1_TAC] THEN ASM_REWRITE_TAC [IN_ELIM_THM], DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"ring_of_integers k:A ring"), (← q r"l:B ring"), (← q r"ring_of_int k:int->A"), (← q r"h:A->B"), (← q r"x:B")] INTEGRAL_ELEMENT_INTERMEDIATE) THEN ASM_REWRITE_TAC []])

  let RING_OF_INTEGERS_MINIMAL_POLYNOMIAL ← prove
    r"!k:A ring l:B ring h x.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        x IN ring_carrier l
        ==> (x IN ring_carrier(ring_of_integers l) <=>
             !i. coeff i (minimal_polynomial (k,l) h x) IN
                 ring_carrier(ring_of_integers k))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITE_IMP_FIELD_EXTENSION)) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"I:A->A"), (← q r"h:A->B"), (← q r"x:B")] INTEGRALLY_CLOSED_MINIMAL_POLYNOMIAL) THEN ASM_SIMP_TAC [INTEGRALLY_CLOSED_RING_OF_INTEGERS, RING_OF_INTEGERS_FRACTION_FIELD, I_O_ID, IMAGE_I, RING_OF_INTEGERS_INTEGRAL_ELEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC [FINITE_IMP_ALGEBRAIC_EXTENSION, algebraic_extension])

  let RING_OF_INTEGERS_MINIMAL_POLYNOMIAL_Q ← prove
    r"!k:A ring x.
        number_field k /\ x IN ring_carrier k
        ==> (x IN ring_carrier(ring_of_integers k) <=>
             !i. ?m. coeff i (minimal_polynomial
                                (subfield_generated k {ring_0 k},k) I x) =
                     ring_of_int k m)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_0 k}:A ring"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"x:A")] RING_OF_INTEGERS_MINIMAL_POLYNOMIAL) THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, NUMBER_FIELD_IMP_FIELD, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, RING_OF_INTEGERS_PRIME_SUBFIELD_CARRIER] THEN DISCH_THEN SUBST1_TAC THEN SET_TAC [])

  let (NUMBER_FIELD_TRACE_INTEGRAL, NUMBER_FIELD_NORM_INTEGRAL) ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"x:B"
    let q2 ← q r"h:A->B"
    let q3 ← q r"I:A->A"
    let q4 ← q r"l:B ring"
    let q5 ← q r"k:A ring"
    let q6 ← q r"ring_of_integers k:A ring"
    let v7 ← ISPECL [q6, q5, q4, q3, q2, q1] INTEGRALLY_CLOSED_ALGEBRA_TRACE_NORM
    let q8 ← q r"h:A->B"
    let q9 ← q r"l:B ring"
    let q10 ← q r"k:A ring"
    let v11 ← ISPECL [q10, q9, q8] NUMBER_FIELD_TOWER_LAW
    let q12 ← q r"h:A->B"
    let q13 ← q r"l:B ring"
    let q14 ← q r"k:A ring"
    let v15 ← ISPECL [q14, q13, q12] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE
    let q16 ← q r"(p ==> q) /\ (p ==> r) <=> p ==> q /\ r"
    let r17 ← TAUT q16
    let p18 ← prove r"(!k:A ring l:B ring h x.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        x IN ring_carrier(ring_of_integers l)
        ==> algebra_trace (k,l) h x IN ring_carrier(ring_of_integers k)) /\
   (!k:A ring l:B ring h x.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        x IN ring_carrier(ring_of_integers l)
        ==> algebra_norm (k,l) h x IN ring_carrier(ring_of_integers k))" (REWRITE_TAC [AND_FORALL_THM] THEN REPEAT GEN_TAC THEN REWRITE_TAC [r17] THEN STRIP_TAC THEN MP_TAC v15 THEN MP_TAC v11 THEN ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN MP_TAC v7 THEN ASM_SIMP_TAC [INTEGRALLY_CLOSED_RING_OF_INTEGERS, RING_OF_INTEGERS_FRACTION_FIELD, I_O_ID, IMAGE_I, RING_OF_INTEGERS_INTEGRAL_ELEMENT])
    CONJ_PAIR p18

  let RING_OF_INTEGERS_UNIT_NORM ← prove
    r"!k:A ring l:B ring h x.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        x IN ring_carrier(ring_of_integers l)
        ==> (ring_unit (ring_of_integers l) x <=>
             ring_unit (ring_of_integers k) (algebra_norm (k,l) h x))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"I:A->A"), (← q r"h:A->B"), (← q r"x:B")] INTEGRALLY_CLOSED_UNIT_NORM) THEN ASM_SIMP_TAC [INTEGRALLY_CLOSED_RING_OF_INTEGERS, RING_OF_INTEGERS_FRACTION_FIELD, I_O_ID, I_THM, RING_OF_INTEGERS_INTEGRAL_ELEMENT] THEN DISCH_TAC THEN TRANS_TAC EQ_TRANS (← q r"?y:B. y IN ring_carrier(ring_of_integers l) /\ ring_mul l x y = ring_1 l") THEN CONJ_TAC THENL [ASM_REWRITE_TAC [ring_unit, RING_OF_INTEGERS], ASM_REWRITE_TAC [] THEN MESON_TAC []])

  let RING_OF_INTEGERS_UNIT_NORM_Q ← prove
    r"!k x:A.
        number_field k
        ==> (ring_unit (ring_of_integers k) x <=>
             x IN ring_carrier(ring_of_integers k) /\
             (algebra_norm (subfield_generated k {ring_0 k},k) I x =
              ring_1 k \/
              algebra_norm (subfield_generated k {ring_0 k},k) I x =
              ring_neg k (ring_1 k)))"
    (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"(x:A) IN ring_carrier(ring_of_integers k)") THENL [ASM_REWRITE_TAC [], ASM_MESON_TAC [RING_UNIT_IN_CARRIER]] THEN FIRST_ASSUM ((X_CHOOSE_TAC (← q r"w:num->A")) o (MATCH_MP RING_OF_INTEGERS_FREE)) THEN MP_TAC (← ISPECL [(← q r"ring_of_int k:int->A"), (← q r"integer_ring"), (← q r"ring_of_integers k:A ring"), (← q r"x:A")] ALGEBRA_NORM_UNIT) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN MP_TAC (← ISPEC (← q r"ring_of_integers(k:A ring)") RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN REWRITE_TAC [RING_OF_INTEGERS], DISCH_THEN (SUBST1_TAC o SYM)] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"extension_degree (subfield_generated k {ring_0 k},k:A ring) I"), (← q r"w:num->A"), (← q r"x:A")] NUMBER_FIELD_NORM_INTEGRAL_BASIS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [INTEGER_RING_UNIT, (← GSYM RING_OF_INT_1)] THEN REWRITE_TAC [(← GSYM RING_OF_INT_NEG)] THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN ASM_SIMP_TAC [RING_OF_INT_EQ_CHAR_0])

  let NUMBER_FIELD_NORM_MULTIPLE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r4 ← RING_RULE (← q r"ring_mul (r:B ring) a (ring_mul r x y) =
        ring_mul r x (ring_mul r a y)")
    prove
      r"!k:A ring l:B ring h x.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          x IN ring_carrier(ring_of_integers l)
          ==> h(algebra_norm (k,l) h x) IN
              ideal_generated (ring_of_integers l) {x}"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITE_IMP_FIELD_EXTENSION)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o ((REWRITE_RULE [field_extension]) o (checkM (fun th => (do let z10 ← (q r"field_extension(k:A ring,l:B ring) h"); let z9 ← (do let z8 ← (pure th); pure (concl z8)); pure (z9 == z10)))))) THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN ABBREV_TAC (← q r"J = ideal_generated (ring_of_integers l) {x:B}") THEN SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers l) (J:B->bool)") ASSUME_TAC THENL [EXPAND_TAC "J" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"(x:B) IN J") ASSUME_TAC THENL [EXPAND_TAC "J" THEN ASM_REWRITE_TAC [IN_IDEAL_GENERATED_SELF], ALL_TAC] THEN SUBGOAL_THEN (← q r"algebraic_over (k,l) (h:A->B) x") ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o ((MATCH_MP FINITE_IMP_ALGEBRAIC_EXTENSION) o (checkM (fun th => (do let z7 ← (q r"finite_extension(k:A ring,l:B ring) h"); let z6 ← (do let z5 ← (pure th); pure (concl z5)); pure (z6 == z7)))))) THEN REWRITE_TAC [algebraic_extension] THEN ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"x:B")] RING_OF_INTEGERS_MINIMAL_POLYNOMIAL) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"x:B")] MINIMAL_POLYNOMIAL) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"x:B")] ALGEBRA_NORM_MINIMAL_POLYNOMIAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ABBREV_TAC (← q r"p = minimal_polynomial (k,l) (h:A->B) x") THEN ABBREV_TAC (← q r"m = extension_degree
           (subfield_generated l (x INSERT IMAGE (h:A->B) (ring_carrier k)),l)
           I") THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"~(m = 0)") ASSUME_TAC THENL [EXPAND_TAC "m" THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"x INSERT IMAGE (h:A->B) (ring_carrier k)")] FINITE_EXTENSION_SUBFIELD_GENERATED) THEN ANTS_TAC THENL [ASM SET_TAC [], STRIP_TAC] THEN ASM_SIMP_TAC [EXTENSION_DEGREE_EQ_0, FIELD_EXTENSION_SUBFIELD_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. coeff i (p:(1->num)->A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. (h:A->B)(coeff i p) IN ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. (h:A->B)(coeff i p) IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"(h:A->B)(coeff 0 p) IN J") ASSUME_TAC THENL [UNDISCH_TAC (← q r"poly_extend (k,l) (h:A->B) (\v:1. x) p = ring_0 l") THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"\v:1. (x:B)"), (← q r"p:(1->num)->A")] POLY_EXTEND_UNIVARIATE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN SIMP_TAC [RING_SUM_CLAUSES_LEFT, LE_0] THEN ASM_SIMP_TAC [RING_MUL, RING_POW, RING_1, ring_pow, RING_MUL_RID, ADD_CLAUSES] THEN ABBREV_TAC (← q r"S = ring_sum l (1..poly_deg k p)
              (\i. ring_mul l ((h:A->B) (coeff i p)) (ring_pow l x i))") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"(h:A->B)(coeff 0 p)"), (← q r"S:B")] RING_RNEG_UNIQUE) THEN ASM_SIMP_TAC [] THEN ANTS_TAC THENL [EXPAND_TAC "S" THEN REWRITE_TAC [RING_SUM], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") IN_RING_IDEAL_NEG)) THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "S" THEN wPart lhand (rand o rand) RING_SUM_RING_OF_INTEGERS THEN ANTS_TAC THENL [ASM_SIMP_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_MUL)), (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_POW))], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC IN_RING_IDEAL_SUM THEN ASM_REWRITE_TAC [IN_NUMSEG] THEN X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"i = SUC(i - 1)") SUBST1_TAC THENL [ASM_ARITH_TAC, REWRITE_TAC [ring_pow]] THEN SUBGOAL_THEN (← q r"ring_mul l ((h:A->B) (coeff (SUC (i - 1)) p))
          (ring_mul l x (ring_pow l x (i - 1))) =
        ring_mul l x (ring_mul l (h(coeff (SUC (i - 1)) p))
                                   (ring_pow l x (i - 1)))") SUBST1_TAC THENL [MATCH_MP_TAC r4 THEN ASM_SIMP_TAC [RING_POW], ALL_TAC] THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") IN_RING_IDEAL_RMUL)) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_MUL)) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_POW)) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_pow k (ring_neg k (ring_1 k)) (poly_deg k p) IN ring_carrier k /\
      ring_mul k (ring_pow k (ring_neg k (ring_1 k)) (poly_deg k p))
        (coeff 0 (p:(1->num)->A)) IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_POW, RING_NEG, RING_1, RING_MUL], ALL_TAC] THEN FIRST_ASSUM ((fun th => tactic_of do pure (ASM_SIMP_TAC (RING_POW :: (RING_MUL :: (RING_NEG :: (RING_1 :: (← ([RING_HOMOMORPHISM_POW, RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_NEG, RING_HOMOMORPHISM_1]).mapM (← do let c := th; pure (fun th => MATCH_MP th c))))))))) o (checkM (fun th => (do let z3 ← (q r"ring_homomorphism(k:A ring,l:B ring) h"); let z2 ← (do let z1 ← (pure th); pure (concl z1)); pure (z2 == z3))))) THEN SUBGOAL_THEN (← q r"ring_mul l (ring_pow l (ring_neg l (ring_1 l)) (poly_deg k p))
        ((h:A->B)(coeff 0 p)) IN J") ASSUME_TAC THENL [MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") IN_RING_IDEAL_LMUL)) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_POW)) THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_NEG)) THEN REWRITE_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_1))], ALL_TAC] THEN SUBGOAL_THEN (← q r"m = SUC(m - 1)") SUBST1_TAC THENL [ASM_ARITH_TAC, REWRITE_TAC [ring_pow]] THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") IN_RING_IDEAL_RMUL)) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_POW)) THEN ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET])

  let NUMBER_FIELD_INTEGRAL_PRIMITIVE_ELEMENT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul (l:B ring) u v = ring_1 l
      ==> b = ring_mul l u (ring_mul l v b)")
    prove
      r"!k:A ring l:B ring h.
          field k /\ number_field l /\ ring_homomorphism(k,l) h
          ==> ?a. a IN ring_carrier(ring_of_integers l) /\
                  subring_generated l (a INSERT IMAGE h (ring_carrier k)) = l"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring")] PRIMITIVE_ELEMENT_THEOREM) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SEPARABLE_EXTENSION_CHAR0 THEN ASM_SIMP_TAC [FINITE_IMP_ALGEBRAIC_EXTENSION] THEN ASM_MESON_TAC [number_field], DISCH_THEN (X_CHOOSE_THEN (← q r"b:B") STRIP_ASSUME_TAC)] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"b:B")] NUMBER_FIELD_INTEGRAL_MULTIPLE) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"d:int") THEN STRIP_TAC THEN EXISTS_TAC (← q r"ring_mul l (ring_of_int l d) (b:B)") THEN ASM_REWRITE_TAC [SUBRING_GENERATED_SUPERSET] THEN FIRST_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [(← SYM th)])) THEN MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN REWRITE_TAC [SUBRING_SUBRING_GENERATED, INSERT_SUBSET] THEN SUBGOAL_THEN (← q r"IMAGE (h:A->B) (ring_carrier k) SUBSET ring_carrier l") ASSUME_TAC THENL [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN SUBGOAL_THEN (← q r"IMAGE (h:A->B) (ring_carrier k) SUBSET
      ring_carrier(subring_generated l
       (ring_mul l (ring_of_int l d) b INSERT IMAGE h (ring_carrier k)))") ASSUME_TAC THENL [REWRITE_TAC [SUBSET] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN ASM SET_TAC [], ASM_REWRITE_TAC []] THEN SUBGOAL_THEN (← q r"~(ring_of_int k d:A = ring_0 k)") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INT_EQ_0_CHAR_0, number_field], ALL_TAC] THEN SUBGOAL_THEN (← q r"(b:B) = ring_mul l ((h:A->B) (ring_inv k (ring_of_int k d)))
                         (ring_mul l (ring_of_int l d) b)") (fun th => GEN_REWRITE_TAC LAND_CONV [th]) THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_HOMOMORPHISM_RING_OF_INT) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM th)])) THEN SUBGOAL_THEN (← q r"ring_mul l ((h:A->B) (ring_inv k (ring_of_int k d)))
                   (h (ring_of_int k d)) = ring_1 l") MP_TAC THENL [FIRST_ASSUM ((fun th => tactic_of do pure (ASM_SIMP_TAC [RING_INV, RING_OF_INT, FIELD_MUL_LINV, (← GSYM (← MATCH_MP RING_HOMOMORPHISM_MUL th)), (← MATCH_MP RING_HOMOMORPHISM_1 th)])) o (checkM (fun th => (do let z4 ← (q r"ring_homomorphism(k,l) (h:A->B)"); let z3 ← (do let z2 ← (pure th); pure (concl z2)); pure (z3 == z4))))), ALL_TAC] THEN MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THEN MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN EXISTS_TAC (← q r"k:A ring") THEN ASM_SIMP_TAC [RING_INV, RING_OF_INT], ALL_TAC] THEN MATCH_MP_TAC RING_MUL_IN_SUBRING_GENERATED THEN CONJ_TAC THENL [FIRST_X_ASSUM (MATCH_MP_TAC o (REWRITE_RULE [SUBSET])) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC [RING_INV, RING_OF_INT], MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN ASM_SIMP_TAC [IN_INSERT, RING_MUL, RING_OF_INT]])

  let NUMBER_FIELD_INTEGRAL_PRIMITIVE_ELEMENT_Q ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(t:A->bool) SUBSET u ==> s SUBSET t ==> s SUBSET u")
    prove
      r"!k:A ring.
          number_field k
          ==> ?a. a IN ring_carrier(ring_of_integers k) /\
                  subfield_generated k {a} = k"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"I:A->A")] NUMBER_FIELD_INTEGRAL_PRIMITIVE_ELEMENT) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION, FIELD_SUBFIELD_GENERATED, IMAGE_I] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"a:A") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN REWRITE_TAC [SUBRING_GENERATED_SUPERSET, SUBFIELD_GENERATED_SUPERSET] THEN MATCH_MP_TAC r1 THEN MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN REWRITE_TAC [SUBRING_SUBFIELD_GENERATED, INSERT_SUBSET] THEN CONJ_TAC THENL [MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN ASM_REWRITE_TAC [IN_SING], MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED, SING_SUBSET] THEN MATCH_MP_TAC IN_SUBRING_0 THEN REWRITE_TAC [SUBRING_SUBFIELD_GENERATED]])

  -- @@RETURN BEGIN
  return { RING_OF_INTEGERS_INTEGRAL_ELEMENT, RING_OF_INTEGERS_MINIMAL_POLYNOMIAL,
           RING_OF_INTEGERS_MINIMAL_POLYNOMIAL_Q, NUMBER_FIELD_TRACE_INTEGRAL,
           NUMBER_FIELD_NORM_INTEGRAL, RING_OF_INTEGERS_UNIT_NORM,
           RING_OF_INTEGERS_UNIT_NORM_Q, NUMBER_FIELD_NORM_MULTIPLE,
           NUMBER_FIELD_INTEGRAL_PRIMITIVE_ELEMENT,
           NUMBER_FIELD_INTEGRAL_PRIMITIVE_ELEMENT_Q }
  -- @@RETURN END

end HolANT.Integrality
