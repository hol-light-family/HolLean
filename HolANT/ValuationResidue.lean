/- ========================================================================= -/
/- ANT: Residue fields and decomposition groups of valuation ...           -/
/- ========================================================================= -/
/- File: HolANT/ValuationResidue.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/valuation_residue.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antvaluationresiduediff; the rest is by hand.  Its `needs` closure is
  Library/wo.ml, Library/card.ml, Library/matroids.ml, Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/ringtheory.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/frag.ml, Library/grouptheory.ml, Library/symmetric_group.ml, Library/galois.ml, ANT/integral.ml, ANT/ideal_arith.ml, Library/products.ml, ANT/algmisc.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/valuation_ring.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/classgroup.ml, ANT/nf_valuation.ml, ANT/prime_split.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/relative_split.ml, Library/ring_groups.ml, Library/finite_fields.ml, ANT/decomposition.ml, ANT/relative_degree.ml, ANT/finite_field_trace.ml, ANT/ramification.ml, ANT/splitting_types.ml, ANT/nf_decomposition.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.ValuationResidue fills them).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left; where a proof applies rules that print or use
  counters (MESON, ARITH_RULE, ...) they are bound first, in OCaml's order.
-/

import HolANT.Prelude
import HolLibrary.Wo
import HolLibrary.Card
import HolLibrary.Matroids
import HolLibrary.Binomial
import HolLibrary.Iter
import HolLibrary.Prime
import HolLibrary.Pocklington
import HolLibrary.RingTheory
import HolLibrary.Permutations
import HolLibrary.RingDet
import HolLibrary.FieldTheory
import HolLibrary.Frag
import HolLibrary.GroupTheory
import HolLibrary.SymmetricGroup
import HolLibrary.Galois
import HolANT.Integral
import HolANT.IdealArith
import HolLibrary.Products
import HolANT.Algmisc
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.ValuationRing
import HolLibrary.Isum
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolANT.IdealNorm
import HolANT.RingOfIntegers
import HolANT.NormIndex
import HolANT.Classgroup
import HolANT.NfValuation
import HolANT.PrimeSplit
import HolANT.Discriminant
import HolANT.TraceForm
import HolANT.RelativeSplit
import HolLibrary.RingGroups
import HolLibrary.FiniteFields
import HolANT.Decomposition
import HolANT.RelativeDegree
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
open HolANT.Integral
open HolANT.IdealArith
open HolANT.Algmisc
open HolANT.Dedekind
open HolANT.DedekindStruct
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.ValuationRing
open HolANT.Zlattice
open HolANT.Numfield
open HolANT.IdealNorm
open HolANT.RingOfIntegers
open HolANT.NormIndex
open HolANT.Classgroup
open HolANT.NfValuation
open HolANT.PrimeSplit
open HolANT.Discriminant
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.Decomposition
open HolANT.RelativeDegree
open HolANT.FiniteFieldTrace
open HolANT.Ramification
open HolANT.SplittingTypes
open HolANT.NfDecomposition

namespace HolANT.ValuationResidue

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD ALGEBRAIC_OVER_DIV
   CARRIER_SUBFIELD_GENERATED_SUBFIELD CARRIER_SUBRING_GENERATED_SUBRING COEFF
   CONTRAPOS_THM DECOMPOSITION_GROUP DECOMPOSITION_GROUP_RESIDUE_HOMOMORPHISM
   DECOMPOSITION_GROUP_RING_OF_INTEGERS DEDEKIND_RING_OF_INTEGERS
   DEDEKIND_VALUATION_IMAGE DEDEKIND_VALUATION_INV DEDEKIND_VALUATION_MUL
   DEDEKIND_VALUATION_POS DEDEKIND_VALUATION_PRIME_IDEAL DIVIDES_ONE EQ_IMP
   ETA_AX EXTENSION FIELD_EXTENSION_SUBFIELD_GENERATED FIELD_HOMOMORPHISM_INV
   FIELD_IMP_INTEGRAL_DOMAIN FIELD_INV_EQ_0 FIELD_MUL_RINV FIELD_QUOTIENT_RING
   FIELD_SUBFIELD_GENERATED FIELD_UNIT FORALL_IN_GSPEC FORALL_IN_IMAGE
   FUN_EQ_THM GALOIS_GROUP_IMAGE_INVERSE GALOIS_GROUP_INVERSE
   GALOIS_GROUP_PERMUTES GALOIS_GROUP_RING_HOMOMORPHISM
   GALOIS_GROUP_RING_OF_INTEGERS IMAGE_I IMP_CONJ INTEGER_RING
   INTEGRAL_DOMAIN_CHAR INTEGRAL_DOMAIN_MUL_EQ_0
   INTEGRAL_DOMAIN_SUBRING_GENERATED INTEGRAL_ELEMENT_OVER_SUBRING INT_LT_IMP_LE
   INT_NOT_LT IN_ELIM_THM IN_IMAGE IN_INSERT IN_INTER IN_RING_IDEAL_0
   IN_RING_IDEAL_LMUL IN_RING_IDEAL_RMUL IN_RING_IDEAL_SUB IN_UNIV I_DEF I_O_ID
   I_THM LEFT_IMP_EXISTS_THM MAXIMAL_IMP_PRIME_IDEAL MAXIMAL_IMP_RING_IDEAL
   MONIC_CMUL MONO_EXISTS NOT_EXISTS_THM PERMUTES_INJECTIVE PERMUTES_INVERSES
   PERMUTES_IN_IMAGE POLY_DEG_EQ_COEFF_EQ POLY_EVAL_HOMOMORPHIC_IMAGE
   POLY_EVAL_SUBRING_GENERATED POLY_EXTEND_CONST POLY_EXTEND_MUL POLY_RING
   PRIME_1 PRIME_IDEAL_HOMOMORPHIC_PREIMAGE PRIME_IMP_RING_IDEAL
   PRIME_INT_DIVPROD_EQ PRIME_SUBFIELD_SUBFIELD_GENERATED PRIME_SUBRING
   PROPER_IDEAL QUOTIENT_RING_0 QUOTIENT_RING_CARRIER QUOTIENT_RING_MUL
   RIGHT_FORALL_IMP_THM RING_0 RING_CHAR_SUBFIELD_GENERATED : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (RING_CHAR_UNIQUE RING_COSET_EQ_IDEAL RING_HOMOMORPHISM_0
   RING_HOMOMORPHISM_BETWEEN_SUBRINGS RING_HOMOMORPHISM_I
   RING_HOMOMORPHISM_INCLUSION RING_HOMOMORPHISM_INTEGER_RING_OF_INT
   RING_HOMOMORPHISM_IN_CARRIER RING_HOMOMORPHISM_MUL
   RING_HOMOMORPHISM_RING_COSET RING_HOMOMORPHISM_RING_OF_INT
   RING_HOMOMORPHISM_RING_OF_INTEGERS RING_HOMOMORPHISM_RING_OF_NUM RING_INV
   RING_INV_INV RING_INV_MUL RING_INV_SUBFIELD_GENERATED
   RING_MONOMORPHISM_INCLUSION RING_MUL_RZERO RING_OF_INT RING_OF_INTEGERS
   RING_OF_INTEGERS_ALGEBRAIC RING_OF_INTEGERS_CARRIER
   RING_OF_INTEGERS_FRACTION_FIELD RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE
   RING_OF_INTEGERS_SUBFIELD_GENERATED RING_OF_INTEGERS_SUBRING
   RING_OF_INTEGERS_SUBSET RING_OF_INT_0 RING_OF_INT_1 RING_OF_INT_ADD
   RING_OF_INT_EQ RING_OF_INT_EQ_0 RING_OF_INT_MUL RING_OF_INT_NEG
   RING_OF_INT_OF_NUM RING_OF_INT_SUBFIELD_GENERATED
   RING_OF_INT_SUBRING_GENERATED RING_OF_NUM RING_OF_NUM_SUBRING_GENERATED
   RING_POLYNOMIAL RING_POLYNOMIAL_CONST RING_POLYNOMIAL_MUL RING_SUB
   RING_SUB_SUBRING_GENERATED RING_UNIT_SUBRING_OF_FIELD SIMPLE_IMAGE
   SUBFIELD_GENERATED SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED
   SUBFIELD_GENERATED_INC_GEN SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC
   SUBFIELD_OF_IMP_SUBSET SUBFIELD_SUBFIELD_GENERATED SUBRING_GENERATED SUBSET
   SUBSET_REFL SUBSET_UNIV VALUATION_SUBRING_DOMINATES
   VALUATION_SUBRING_INTEGRAL_ELEMENT VALUATION_SUBRING_INV_MAXIMAL_IDEAL
   VALUATION_SUBRING_MAXIMAL_IDEAL VALUATION_SUBRING_SUBFIELD
   algebraic_extension algebraically_closed_field decomposition_group
   field_of_fractions inertia_group integral_element num_divides number_field
   o_THM poly_deg poly_eval poly_evaluate poly_extend prime_ideal ring_div
   ring_homomorphism ring_ideal ring_polynomial ring_powerseries subring_of
   valuation_subring : thm)
  deriving Inhabited

/-- What valuation_residue.ml uses from Session besides theorems. -/
structure ValuationResidueDeps where
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
/- valuation_residue.ml phrases from line 92 to 675                       -/
/- ---------------------------------------------------------------------- -/

structure ValuationResidue01 where
  -- @@FIELDS
  VALUATION_SUBRING_RESIDUE_ALGEBRAICALLY_CLOSED : thm
  VALUATION_SUBRING_OVER_PRIME : thm
  VALUATION_SUBRING_RESIDUE_CHAR : thm
  VALUATION_SUBRING_RESIDUE_CHAR_CASES : thm
  ALGEBRAICALLY_CLOSED_VALUATION_OVER_PRIME : thm
  VALUATION_SUBRING_DECOMPOSITION_GROUP : thm
  VALUATION_SUBRING_RESIDUE_HOMOMORPHISM : thm
  VALUATION_SUBRING_RESIDUE_DIV : thm
  VALUATION_SUBRING_RING_OF_INTEGERS : thm
  VALUATION_SUBRING_CONTRACTION_RING_OF_INTEGERS : thm
  VALUATION_SUBRING_DECOMPOSITION_RESIDUE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupValuationResidue01 [HolBase] (D : ValuationResidueDeps) :
    ExceptT String IO ValuationResidue01 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, INTEGER_RULE, INTEGER_TAC, MESON_TAC, RING_RULE, SET_TAC, TAUT, .. } := D
  let { ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD, CARRIER_SUBRING_GENERATED_SUBRING, COEFF,
        CONTRAPOS_THM, DECOMPOSITION_GROUP, DECOMPOSITION_GROUP_RESIDUE_HOMOMORPHISM,
        DECOMPOSITION_GROUP_RING_OF_INTEGERS, DIVIDES_ONE, EQ_IMP, ETA_AX, EXTENSION,
        FIELD_HOMOMORPHISM_INV, FIELD_IMP_INTEGRAL_DOMAIN, FIELD_MUL_RINV,
        FIELD_QUOTIENT_RING, FORALL_IN_IMAGE, FUN_EQ_THM, GALOIS_GROUP_IMAGE_INVERSE,
        GALOIS_GROUP_INVERSE, GALOIS_GROUP_PERMUTES, GALOIS_GROUP_RING_HOMOMORPHISM,
        IMAGE_I, IMP_CONJ, INTEGER_RING, INTEGRAL_DOMAIN_CHAR,
        INTEGRAL_DOMAIN_SUBRING_GENERATED, INTEGRAL_ELEMENT_OVER_SUBRING, IN_ELIM_THM,
        IN_IMAGE, IN_INTER, IN_RING_IDEAL_0, IN_RING_IDEAL_LMUL, IN_RING_IDEAL_RMUL,
        IN_RING_IDEAL_SUB, IN_UNIV, I_DEF, I_O_ID, I_THM, MAXIMAL_IMP_PRIME_IDEAL,
        MAXIMAL_IMP_RING_IDEAL, MONIC_CMUL, MONO_EXISTS, PERMUTES_INJECTIVE,
        PERMUTES_INVERSES, PERMUTES_IN_IMAGE, POLY_DEG_EQ_COEFF_EQ,
        POLY_EVAL_HOMOMORPHIC_IMAGE, POLY_EVAL_SUBRING_GENERATED, POLY_EXTEND_CONST,
        POLY_EXTEND_MUL, POLY_RING, PRIME_1, PRIME_IDEAL_HOMOMORPHIC_PREIMAGE,
        PRIME_IMP_RING_IDEAL, PRIME_INT_DIVPROD_EQ, PRIME_SUBRING, PROPER_IDEAL,
        QUOTIENT_RING_0, QUOTIENT_RING_CARRIER, RIGHT_FORALL_IMP_THM, RING_0, .. } := D.core1
  let { RING_CHAR_UNIQUE, RING_COSET_EQ_IDEAL, RING_HOMOMORPHISM_0,
        RING_HOMOMORPHISM_BETWEEN_SUBRINGS, RING_HOMOMORPHISM_I,
        RING_HOMOMORPHISM_INCLUSION, RING_HOMOMORPHISM_INTEGER_RING_OF_INT,
        RING_HOMOMORPHISM_IN_CARRIER, RING_HOMOMORPHISM_MUL,
        RING_HOMOMORPHISM_RING_COSET, RING_HOMOMORPHISM_RING_OF_INT,
        RING_HOMOMORPHISM_RING_OF_NUM, RING_INV, RING_MUL_RZERO, RING_OF_INT,
        RING_OF_INTEGERS_CARRIER, RING_OF_INTEGERS_SUBRING, RING_OF_INT_0,
        RING_OF_INT_1, RING_OF_INT_ADD, RING_OF_INT_EQ, RING_OF_INT_EQ_0,
        RING_OF_INT_MUL, RING_OF_INT_NEG, RING_OF_INT_OF_NUM,
        RING_OF_INT_SUBRING_GENERATED, RING_OF_NUM, RING_OF_NUM_SUBRING_GENERATED,
        RING_POLYNOMIAL, RING_POLYNOMIAL_CONST, RING_POLYNOMIAL_MUL,
        RING_SUB_SUBRING_GENERATED, RING_UNIT_SUBRING_OF_FIELD, SIMPLE_IMAGE,
        SUBRING_GENERATED, SUBSET, SUBSET_REFL, SUBSET_UNIV,
        VALUATION_SUBRING_DOMINATES, VALUATION_SUBRING_INTEGRAL_ELEMENT,
        VALUATION_SUBRING_INV_MAXIMAL_IDEAL, VALUATION_SUBRING_MAXIMAL_IDEAL,
        algebraically_closed_field, integral_element, num_divides, o_THM, poly_deg,
        poly_eval, poly_evaluate, poly_extend, prime_ideal, ring_div, ring_ideal,
        ring_polynomial, ring_powerseries, subring_of, valuation_subring, .. } := D.core2
  -- @@SCOPE END

  let VALUATION_SUBRING_RESIDUE_ALGEBRAICALLY_CLOSED ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ q /\ (p /\ q ==> r) ==> p /\ q /\ r")
    prove
      r"!(k:A ring) v m.
          algebraically_closed_field k /\ valuation_subring k v /\
          maximal_ideal (subring_generated k v) m
          ==> algebraically_closed_field
               (quotient_ring (subring_generated k v) m)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [valuation_subring])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"ring_carrier(subring_generated k v) = (v:A->bool)") ASSUME_TAC THENL [ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING], ALL_TAC] THEN REWRITE_TAC [algebraically_closed_field] THEN ASM_SIMP_TAC [FIELD_QUOTIENT_RING] THEN X_GEN_TAC (← q r"p:(1->num)->(A->bool)") THEN STRIP_TAC THEN ABBREV_TAC (← q r"R = subring_generated k (v:A->bool)") THEN ABBREV_TAC (← q r"kq = quotient_ring R (m:A->bool)") THEN SUBGOAL_THEN (← q r"ring_0 R = ring_0 (k:A ring) /\
      ring_carrier kq = {ring_coset R (m:A->bool) a | a IN v} /\
      ring_0 kq = (m:A->bool) /\
      (!a. a IN v ==> (ring_coset R m a = m <=> a IN m))") STRIP_ASSUME_TAC THENL [EXPAND_TAC "kq" THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, QUOTIENT_RING_0] THEN CONJ_TAC THENL [EXPAND_TAC "R" THEN REWRITE_TAC [(← CONJUNCT2 SUBRING_GENERATED)], X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN MATCH_MP_TAC RING_COSET_EQ_IDEAL THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"!mon. (p:(1->num)->(A->bool)) mon IN ring_carrier kq") ASSUME_TAC THENL [UNDISCH_TAC (← q r"(p:(1->num)->(A->bool)) IN
        ring_carrier(poly_ring (kq:(A->bool)ring) (:1))") THEN REWRITE_TAC [POLY_RING, IN_ELIM_THM, ring_polynomial, ring_powerseries] THEN SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_0 (k:A ring) IN v /\ ring_0 k IN (m:A->bool)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_0, IN_RING_IDEAL_0], ALL_TAC] THEN ABBREV_TAC (← q r"P = \mon:1->num. if p mon = ring_0 kq then ring_0 k
                       else @a:A. a IN v /\ ring_coset R m a = p mon") THEN SUBGOAL_THEN (← q r"!mon:1->num. (P:(1->num)->A) mon IN v /\
                   ring_coset R m (P mon) = p mon /\
                   (P mon = ring_0 k <=> p mon = ring_0 kq)") ASSUME_TAC THENL [X_GEN_TAC (← q r"mon:1->num") THEN EXPAND_TAC "P" THEN REWRITE_TAC [] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"?a:A. a IN v /\ ring_coset R m a = p(mon:1->num)") MP_TAC THENL [UNDISCH_TAC (← q r"!mon. (p:(1->num)->(A->bool)) mon IN ring_carrier kq") THEN DISCH_THEN (MP_TAC o (SPEC (← q r"mon:1->num"))) THEN ASM_REWRITE_TAC [] THEN SET_TAC [], DISCH_THEN (STRIP_ASSUME_TAC o SELECT_RULE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_MESON_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"(p:(1->num)->(A->bool)) IN ring_carrier(poly_ring kq (:1)) ==>
      (P:(1->num)->A) IN ring_carrier(poly_ring R (:1)) /\
      P IN ring_carrier(poly_ring k (:1)) /\
      poly_deg R P = poly_deg kq p /\ poly_deg k P = poly_deg kq p") MP_TAC THENL [REWRITE_TAC [POLY_RING, IN_ELIM_THM, ring_polynomial, ring_powerseries, SUBSET_UNIV, poly_deg] THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"(v:A->bool) subring_of k") THEN REWRITE_TAC [subring_of, SUBSET] THEN ASM_MESON_TAC [], ASM_REWRITE_TAC [] THEN STRIP_TAC] THEN SUBGOAL_THEN (← q r"?x. x IN ring_carrier k /\ poly_eval k (P:(1->num)->A) x = ring_0 k") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"algebraically_closed_field (k:A ring)") THEN REWRITE_TAC [algebraically_closed_field] THEN DISCH_THEN (MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"n = poly_deg kq (p:(1->num)->(A->bool))") THEN SUBGOAL_THEN (← q r"~(coeff n (p:(1->num)->(A->bool)) = ring_0 kq)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"kq:(A->bool)ring"), (← q r"p:(1->num)->(A->bool)"), (← q r"n:num")] POLY_DEG_EQ_COEFF_EQ) THEN ASM_REWRITE_TAC [RING_POLYNOMIAL] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"coeff n (P:(1->num)->A) IN v /\ ~(coeff n P IN m) /\
      ring_unit R (coeff n P)") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"~(coeff n (p:(1->num)->(A->bool)) = ring_0 kq)") THEN REWRITE_TAC [COEFF] THEN DISCH_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o ((SPEC (← q r"(\v:1. n):1->num")) o (checkM (fun th => (do if ← (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); pure (is_forall z2)) then (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); canM (fun z6 => (do let z7 ← (pure z6); find_termM (fun z8 => (do let z10 ← (pure z8); let z9 ← (q r"P:(1->num)->A"); pure (z9 == z10))) z7)) z4) else pure false) then (do let z11 ← (do let z12 ← (pure th); pure (concl z12)); canM (fun z13 => (do let z14 ← (pure z13); find_termM (fun z15 => (do let z17 ← (pure z15); let z16 ← (q r"ring_coset:(A)ring->(A->bool)->A->A->bool"); pure (z16 == z17))) z14)) z11) else pure false))))) THEN MATCH_MP_TAC r1 THEN REPEAT CONJ_TAC THENL [ASM_REWRITE_TAC [], ASM_MESON_TAC [], STRIP_TAC THEN EXPAND_TAC "R" THEN ASM_SIMP_TAC [RING_UNIT_SUBRING_OF_FIELD] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"v:A->bool"), (← q r"m:A->bool")] VALUATION_SUBRING_MAXIMAL_IDEAL) THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"maximal_ideal R (m:A->bool)") THEN EXPAND_TAC "R" THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~((P:(1->num)->A) (\v. n) IN
            {x | x IN v /\ (x = ring_0 k \/ ~(ring_inv k x IN v))})") THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN CONV_TAC TAUT], ALL_TAC] THEN ABBREV_TAC (← q r"y = ring_inv R (coeff n (P:(1->num)->A))") THEN SUBGOAL_THEN (← q r"(y:A) IN v /\ y IN ring_carrier k") STRIP_ASSUME_TAC THENL [EXPAND_TAC "y" THEN ASM_MESON_TAC [RING_INV, subring_of, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"(x:A) IN v") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"v:A->bool"), (← q r"x:A")] VALUATION_SUBRING_INTEGRAL_ELEMENT) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [integral_element] THEN EXISTS_TAC (← q r"poly_mul R (poly_const R y) (P:(1->num)->A)") THEN REPEAT CONJ_TAC THENL [REWRITE_TAC [(← GSYM RING_POLYNOMIAL)] THEN MATCH_MP_TAC RING_POLYNOMIAL_MUL THEN ASM_REWRITE_TAC [RING_POLYNOMIAL_CONST, RING_POLYNOMIAL], UNDISCH_TAC (← q r"ring_inv R (coeff n (P:(1->num)->A)) = y") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN SUBGOAL_THEN (← q r"coeff n (P:(1->num)->A) = coeff (poly_deg R P) P") SUBST1_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN MATCH_MP_TAC MONIC_CMUL THEN ASM_REWRITE_TAC [RING_POLYNOMIAL] THEN EXPAND_TAC "R" THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_SUBRING_GENERATED, FIELD_IMP_INTEGRAL_DOMAIN], SUBGOAL_THEN (← q r"ring_homomorphism(R,k) (I:A->A)") ASSUME_TAC THENL [EXPAND_TAC "R" THEN REWRITE_TAC [(← REWRITE_RULE [(← GSYM I_DEF)] RING_HOMOMORPHISM_INCLUSION)], ALL_TAC] THEN wPart lhand (lhand o rand) POLY_EXTEND_MUL THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_POLYNOMIAL_CONST, RING_POLYNOMIAL], DISCH_THEN SUBST1_TAC] THEN wPart (lhand o lhand) (lhand o rand) POLY_EXTEND_CONST THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN SUBGOAL_THEN (← q r"poly_extend (R,k) I (\v:1. x) (P:(1->num)->A) = poly_eval k P x") SUBST1_TAC THENL [REWRITE_TAC [poly_eval, poly_evaluate, poly_extend] THEN UNDISCH_TAC (← q r"ring_0 R = ring_0 (k:A ring)") THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC, ASM_REWRITE_TAC [I_THM] THEN ASM_SIMP_TAC [RING_MUL_RZERO]]], ALL_TAC] THEN EXISTS_TAC (← q r"ring_coset R m (x:A)") THEN CONJ_TAC THENL [REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"p = ring_coset R m o (P:(1->num)->A)") SUBST1_TAC THENL [GEN_REWRITE_TAC id [FUN_EQ_THM] THEN X_GEN_TAC (← q r"mon:1->num") THEN REWRITE_TAC [o_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"R:A ring"), (← q r"kq:(A->bool)ring"), (← q r"x:A"), (← q r"ring_coset R (m:A->bool)"), (← q r"P:(1->num)->A")] POLY_EVAL_HOMOMORPHIC_IMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN EXPAND_TAC "kq" THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_COSET], DISCH_THEN (SUBST1_TAC o SYM)] THEN SUBGOAL_THEN (← q r"poly_eval R (P:(1->num)->A) x = ring_0 k") SUBST1_TAC THENL [UNDISCH_TAC (← q r"poly_eval k (P:(1->num)->A) x = ring_0 k") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN EXPAND_TAC "R" THEN MATCH_MP_TAC POLY_EVAL_SUBRING_GENERATED THEN ASM_REWRITE_TAC [], ASM_MESON_TAC []])

  let VALUATION_SUBRING_OVER_PRIME ← prove
    r"!(k:A ring) p.
        field k /\ ring_char k = 0 /\ prime p
        ==> ?v m. valuation_subring k v /\
                  maximal_ideal (subring_generated k v) m /\
                  !n. ring_of_int k n IN m <=> &p divides n"
    (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"a = {ring_of_int (k:A ring) n | n IN (:int)}") THEN SUBGOAL_THEN (← q r"(a:A->bool) subring_of k") ASSUME_TAC THENL [EXPAND_TAC "a" THEN REWRITE_TAC [PRIME_SUBRING], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_carrier(subring_generated k a) = (a:A->bool)") ASSUME_TAC THENL [ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING], ALL_TAC] THEN SUBGOAL_THEN (← q r"!n n'. ring_of_int k n = ring_of_int (k:A ring) n' <=> n = n'") ASSUME_TAC THENL [ASM_REWRITE_TAC [RING_OF_INT_EQ] THEN INTEGER_TAC, ALL_TAC] THEN ABBREV_TAC (← q r"P = {ring_of_int (k:A ring) n | n | &p divides n}") THEN SUBGOAL_THEN (← q r"!n. ring_of_int (k:A ring) n IN P <=> &p divides n") ASSUME_TAC THENL [EXPAND_TAC "P" THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"prime_ideal (subring_generated k a) (P:A->bool)") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"a = IMAGE (ring_of_int (k:A ring)) (:int) /\
      P = IMAGE (ring_of_int k) {n | &p divides n}") (CONJUNCTS_THEN SUBST_ALL_TAC) THENL [CONJ_TAC THENL [UNDISCH_TAC (← q r"{ring_of_int (k:A ring) n | n IN (:int)} = a") THEN REWRITE_TAC [SIMPLE_IMAGE, ETA_AX] THEN MESON_TAC [], UNDISCH_TAC (← q r"{ring_of_int (k:A ring) n | &p divides n} = P") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN MESON_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"!e s. ring_of_int (k:A ring) e IN IMAGE (ring_of_int k) s <=> e IN s") ASSUME_TAC THENL [REWRITE_TAC [IN_IMAGE] THEN ASM_MESON_TAC [], ALL_TAC] THEN REWRITE_TAC [prime_ideal, PROPER_IDEAL, ring_ideal] THEN ASM_REWRITE_TAC [(← CONJUNCT2 SUBRING_GENERATED)] THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_IMAGE, IN_UNIV, SUBSET] THEN REWRITE_TAC [(← GSYM RING_OF_INT_0), (← GSYM RING_OF_INT_1), (← GSYM RING_OF_INT_NEG), (← GSYM RING_OF_INT_ADD), (← GSYM RING_OF_INT_MUL)] THEN ASM_REWRITE_TAC [IN_ELIM_THM, IN_UNIV] THEN ASM_SIMP_TAC [PRIME_INT_DIVPROD_EQ] THEN CONJ_TAC THENL [CONV_TAC INTEGER_RULE, REWRITE_TAC [(← GSYM num_divides), DIVIDES_ONE] THEN ASM_MESON_TAC [PRIME_1]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!n. ring_of_int (k:A ring) n IN a") ASSUME_TAC THENL [UNDISCH_TAC (← q r"{ring_of_int (k:A ring) n | n IN (:int)} = a") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A->bool"), (← q r"P:A->bool")] VALUATION_SUBRING_DOMINATES) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"v:A->bool") THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"m:A->bool") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"n:int") THEN UNDISCH_TAC (← q r"!n. ring_of_int (k:A ring) n IN P <=> &p divides n") THEN DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM th)])) THEN UNDISCH_TAC (← q r"a INTER m = (P:A->bool)") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC [IN_INTER])

  let VALUATION_SUBRING_RESIDUE_CHAR ← prove
    r"!(k:A ring) v m p.
        valuation_subring k v /\ maximal_ideal (subring_generated k v) m /\
        (!n. ring_of_int k n IN m <=> &p divides n)
        ==> ring_char(quotient_ring (subring_generated k v) m) = p"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_RING_IDEAL)) THEN REWRITE_TAC [RING_CHAR_UNIQUE] THEN X_GEN_TAC (← q r"n:num") THEN MP_TAC (← ISPECL [(← q r"subring_generated k (v:A->bool)"), (← q r"quotient_ring (subring_generated k v) (m:A->bool)"), (← q r"ring_coset (subring_generated k v) (m:A->bool)")] RING_HOMOMORPHISM_RING_OF_NUM) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_COSET] THEN DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM th)])) THEN ASM_SIMP_TAC [QUOTIENT_RING_0, RING_COSET_EQ_IDEAL, RING_OF_NUM] THEN REWRITE_TAC [RING_OF_NUM_SUBRING_GENERATED, (← GSYM RING_OF_INT_OF_NUM)] THEN ASM_REWRITE_TAC [num_divides, RING_OF_INT_SUBRING_GENERATED])

  let VALUATION_SUBRING_RESIDUE_CHAR_CASES ← prove
    r"!(k:A ring) v m.
        valuation_subring k v /\ maximal_ideal (subring_generated k v) m
        ==> ?p. (p = 0 \/ prime p) /\
                !n. ring_of_int k n IN m <=> &p divides n"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_RING_IDEAL)) THEN EXISTS_TAC (← q r"ring_char(quotient_ring (subring_generated k v) (m:A->bool))") THEN CONJ_TAC THENL [MATCH_MP_TAC INTEGRAL_DOMAIN_CHAR THEN MATCH_MP_TAC FIELD_IMP_INTEGRAL_DOMAIN THEN ASM_SIMP_TAC [FIELD_QUOTIENT_RING], X_GEN_TAC (← q r"n:int") THEN REWRITE_TAC [(← GSYM RING_OF_INT_EQ_0)] THEN MP_TAC (← ISPECL [(← q r"subring_generated k (v:A->bool)"), (← q r"quotient_ring (subring_generated k v) (m:A->bool)"), (← q r"ring_coset (subring_generated k v) (m:A->bool)")] RING_HOMOMORPHISM_RING_OF_INT) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_COSET] THEN DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM th)])) THEN ASM_SIMP_TAC [QUOTIENT_RING_0, RING_COSET_EQ_IDEAL, RING_OF_INT] THEN REWRITE_TAC [RING_OF_INT_SUBRING_GENERATED]])

  let ALGEBRAICALLY_CLOSED_VALUATION_OVER_PRIME ← prove
    r"!(k:A ring) p.
        algebraically_closed_field k /\ ring_char k = 0 /\ prime p
        ==> ?v m. valuation_subring k v /\
                  maximal_ideal (subring_generated k v) m /\
                  (!n. ring_of_int k n IN m <=> &p divides n) /\
                  algebraically_closed_field
                   (quotient_ring (subring_generated k v) m) /\
                  ring_char(quotient_ring (subring_generated k v) m) = p"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"p:num")] VALUATION_SUBRING_OVER_PRIME) THEN ASM_SIMP_TAC [ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD] THEN REPEAT (MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [MATCH_MP_TAC VALUATION_SUBRING_RESIDUE_ALGEBRAICALLY_CLOSED THEN ASM_REWRITE_TAC [], MATCH_MP_TAC VALUATION_SUBRING_RESIDUE_CHAR THEN ASM_REWRITE_TAC []])

  let VALUATION_SUBRING_DECOMPOSITION_GROUP ← prove
    r"!(h:A->B) k l v m.
        valuation_subring l v /\ maximal_ideal (subring_generated l v) m
        ==> group_carrier(decomposition_group(k,l) h m) =
            {f | f IN group_carrier(galois_group(k,l) h) /\ IMAGE f v = v}"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [valuation_subring])) THEN SUBGOAL_THEN (← q r"(v:B->bool) SUBSET ring_carrier l /\ m SUBSET v") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [ASM_MESON_TAC [subring_of], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"v:B->bool"), (← q r"m:B->bool")] VALUATION_SUBRING_MAXIMAL_IDEAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!g. g IN group_carrier(galois_group(k,l) (h:A->B))
        ==> g permutes ring_carrier l /\
            (!x. x IN ring_carrier l ==> g(ring_inv l x) = ring_inv l (g x)) /\
            g(ring_0 l) = ring_0 l") (LABEL_TAC "aut") THENL [X_GEN_TAC (← q r"g:B->B") THEN DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM)) THEN REPEAT CONJ_TAC THENL [FIRST_ASSUM (ACCEPT_TAC o (MATCH_MP GALOIS_GROUP_PERMUTES)), MATCH_MP_TAC FIELD_HOMOMORPHISM_INV THEN ASM_REWRITE_TAC [], MATCH_MP_TAC RING_HOMOMORPHISM_0 THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"!g. g IN group_carrier(galois_group(k,l) (h:A->B)) /\ IMAGE g m = m
        ==> IMAGE g v SUBSET v") ASSUME_TAC THENL [X_GEN_TAC (← q r"g:B->B") THEN STRIP_TAC THEN USE_THEN "aut" (MP_TAC o (SPEC (← q r"g:B->B"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier l /\ (g:B->B) x IN ring_carrier l") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [SUBSET, PERMUTES_IN_IMAGE], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"v:B->bool"), (← q r"m:B->bool"), (← q r"x:B")] VALUATION_SUBRING_INV_MAXIMAL_IDEAL) THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"v:B->bool"), (← q r"m:B->bool"), (← q r"(g:B->B) x")] VALUATION_SUBRING_INV_MAXIMAL_IDEAL) THEN ASM_REWRITE_TAC [] THEN REPEAT (DISCH_THEN SUBST1_TAC) THEN ASM_CASES_TAC (← q r"x:B = ring_0 l") THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN DISJ2_TAC THEN FIRST_X_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM (← MATCH_MP th (← ASSUME (← q r"(x:B) IN ring_carrier l"))))])) THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(g:B->B)(ring_inv l x) IN IMAGE g m") MP_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN REWRITE_TAC [IN_IMAGE] THEN ASM_MESON_TAC [PERMUTES_INJECTIVE], ALL_TAC] THEN SUBGOAL_THEN (← q r"!g. g IN group_carrier(galois_group(k,l) (h:A->B)) /\ IMAGE g v = v
        ==> IMAGE g m SUBSET m") ASSUME_TAC THENL [X_GEN_TAC (← q r"g:B->B") THEN STRIP_TAC THEN USE_THEN "aut" (MP_TAC o (SPEC (← q r"g:B->B"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"v:B->bool"), (← q r"m:B->bool")] VALUATION_SUBRING_MAXIMAL_IDEAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN X_GEN_TAC (← q r"q:B") THEN DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(q:B) IN ring_carrier l") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN ASM_CASES_TAC (← q r"q:B = ring_0 l") THEN ASM_REWRITE_TAC [] THEN DISJ2_TAC THEN SUBGOAL_THEN (← q r"~(ring_inv l (q:B) IN v)") MP_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN REWRITE_TAC [CONTRAPOS_THM] THEN FIRST_X_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM (← MATCH_MP th (← ASSUME (← q r"(q:B) IN ring_carrier l"))))])) THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(g:B->B)(ring_inv l q) IN IMAGE g v") MP_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN REWRITE_TAC [IN_IMAGE] THEN ASM_MESON_TAC [PERMUTES_INJECTIVE], ALL_TAC] THEN REWRITE_TAC [DECOMPOSITION_GROUP] THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"f:B->B") THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_CASES_TAC (← q r"f IN group_carrier(galois_group(k,l) (h:A->B))") THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_GROUP_PERMUTES)) THEN DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP PERMUTES_INVERSES)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP GALOIS_GROUP_INVERSE)) THEN EQ_TAC THEN DISCH_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"f:B->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"m:B->bool")] GALOIS_GROUP_IMAGE_INVERSE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"IMAGE (f:B->B) v SUBSET v /\ IMAGE (inverse f) v SUBSET v") MP_TAC THENL [ASM_MESON_TAC [], ALL_TAC], MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"f:B->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"v:B->bool")] GALOIS_GROUP_IMAGE_INVERSE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"IMAGE (f:B->B) m SUBSET m /\ IMAGE (inverse f) m SUBSET m") MP_TAC THENL [ASM_MESON_TAC [], ALL_TAC]] THEN UNDISCH_TAC (← q r"!x:B. (f:B->B)(inverse f x) = x") THEN SET_TAC [])

  let VALUATION_SUBRING_RESIDUE_HOMOMORPHISM ← prove
    r"!(h:A->B) k l v m.
        valuation_subring l v /\ maximal_ideal (subring_generated l v) m
        ==> group_homomorphism
             (decomposition_group(k,l) h m,
              galois_group
               (subring_generated (quotient_ring (subring_generated l v) m)
                 (IMAGE (ring_coset (subring_generated l v) m o h)
                        {a | a IN ring_carrier k /\ h a IN v}),
                quotient_ring (subring_generated l v) m) I)
             (\f X. if X IN ring_carrier
                             (quotient_ring (subring_generated l v) m)
                    then IMAGE f X else X) /\
            group_kernel
             (decomposition_group(k,l) h m,
              galois_group
               (subring_generated (quotient_ring (subring_generated l v) m)
                 (IMAGE (ring_coset (subring_generated l v) m o h)
                        {a | a IN ring_carrier k /\ h a IN v}),
                quotient_ring (subring_generated l v) m) I)
             (\f X. if X IN ring_carrier
                             (quotient_ring (subring_generated l v) m)
                    then IMAGE f X else X) =
            group_carrier(inertia_group(k,l) h (subring_generated l v) m)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [valuation_subring])) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"subring_generated l (v:B->bool)"), (← q r"m:B->bool")] DECOMPOSITION_GROUP_RESIDUE_HOMOMORPHISM) THEN ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING, MAXIMAL_IMP_RING_IDEAL] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [VALUATION_SUBRING_DECOMPOSITION_GROUP, IN_ELIM_THM] THEN SIMP_TAC [SUBSET_REFL])

  let VALUATION_SUBRING_RESIDUE_DIV ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!k a s b t i j:A.
        a IN ring_carrier k /\ s IN ring_carrier k /\
        b IN ring_carrier k /\ t IN ring_carrier k /\
        i IN ring_carrier k /\ j IN ring_carrier k /\
        ring_mul k s i = ring_1 k /\ ring_mul k t j = ring_1 k
        ==> ring_sub k (ring_mul k b j) (ring_mul k a i) =
            ring_mul k
             (ring_mul k
               (ring_sub k (ring_mul k (ring_sub k b a) s)
                           (ring_mul k a (ring_sub k t s))) j) i")
    prove
      r"!(k:A ring) v m (f:A->A) a s.
          valuation_subring k v /\ maximal_ideal (subring_generated k v) m /\
          ring_homomorphism(k,k) f /\
          a IN v /\ s IN v /\ ~(s IN m) /\ f s IN v /\ ~(f s IN m) /\
          ring_sub k (f a) a IN m /\ ring_sub k (f s) s IN m
          ==> ring_sub k (f(ring_div k a s)) (ring_div k a s) IN m"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [valuation_subring])) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"v:A->bool"), (← q r"m:A->bool")] VALUATION_SUBRING_MAXIMAL_IDEAL) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(!x y:A. x IN m /\ y IN v ==> ring_mul k x y IN m) /\
      (!x y:A. x IN v /\ y IN m ==> ring_mul k x y IN m) /\
      (!x y:A. x IN m /\ y IN m ==> ring_sub k x y IN m)") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"subring_generated k (v:A->bool)"), (← q r"m:A->bool")] MAXIMAL_IMP_RING_IDEAL) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN REPEAT CONJ_TAC THEN MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"y:A")] THEN STRIP_TAC THENL [MP_TAC (← ISPECL [(← q r"subring_generated k (v:A->bool)"), (← q r"m:A->bool"), (← q r"x:A"), (← q r"y:A")] IN_RING_IDEAL_RMUL), MP_TAC (← ISPECL [(← q r"subring_generated k (v:A->bool)"), (← q r"m:A->bool"), (← q r"x:A"), (← q r"y:A")] IN_RING_IDEAL_LMUL), MP_TAC (← ISPECL [(← q r"subring_generated k (v:A->bool)"), (← q r"m:A->bool"), (← q r"x:A"), (← q r"y:A")] IN_RING_IDEAL_SUB)] THEN ASM_SIMP_TAC [(← CONJUNCT2 SUBRING_GENERATED), RING_SUB_SUBRING_GENERATED, CARRIER_SUBRING_GENERATED_SUBRING], ALL_TAC] THEN SUBGOAL_THEN (← q r"!z:A. z IN v /\ ~(z IN m)
            ==> z IN ring_carrier k /\ ~(z = ring_0 k) /\ ring_inv k z IN v") ASSUME_TAC THENL [X_GEN_TAC (← q r"z:A") THEN STRIP_TAC THEN UNDISCH_TAC (← q r"~((z:A) IN m)") THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [subring_of, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [subring_of, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"(s:A) IN ring_carrier k /\ ~(s = ring_0 k) /\ ring_inv k s IN v /\
      (f:A->A) s IN ring_carrier k /\ ~(f s = ring_0 k) /\
      ring_inv k (f s) IN v") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sub k ((f:A->A)(ring_div k a s)) (ring_div k a s) =
      ring_mul k
       (ring_mul k
         (ring_sub k (ring_mul k (ring_sub k (f a) a) s)
                     (ring_mul k a (ring_sub k (f s) s)))
         (ring_inv k (f s)))
       (ring_inv k s)") SUBST1_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"k:A ring"), (← q r"f:A->A")] RING_HOMOMORPHISM_MUL) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"k:A ring"), (← q r"f:A->A")] FIELD_HOMOMORPHISM_INV) THEN ASM_SIMP_TAC [ring_div, RING_INV] THEN REPEAT DISCH_TAC THEN MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [RING_INV, FIELD_MUL_RINV] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ASM_MESON_TAC []])

  let VALUATION_SUBRING_RING_OF_INTEGERS ← prove
    r"!(k:A ring) v.
        valuation_subring k v
        ==> ring_carrier(ring_of_integers k) SUBSET v"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [valuation_subring])) THEN REWRITE_TAC [SUBSET, RING_OF_INTEGERS_CARRIER, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN MATCH_MP_TAC VALUATION_SUBRING_INTEGRAL_ELEMENT THEN EXISTS_TAC (← q r"k:A ring") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"k:A ring"), (← q r"ring_of_int (k:A ring)"), (← q r"v:A->bool"), (← q r"x:A")] INTEGRAL_ELEMENT_OVER_SUBRING) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, CARRIER_SUBRING_GENERATED_SUBRING] THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, INTEGER_RING, IN_UNIV] THEN X_GEN_TAC (← q r"n:int") THEN MP_TAC (← ISPECL [(← q r"subring_generated k (v:A->bool)"), (← q r"n:int")] RING_OF_INT) THEN ASM_SIMP_TAC [RING_OF_INT_SUBRING_GENERATED, CARRIER_SUBRING_GENERATED_SUBRING])

  let VALUATION_SUBRING_CONTRACTION_RING_OF_INTEGERS ← prove
    r"!(k:A ring) v m.
        valuation_subring k v /\ maximal_ideal (subring_generated k v) m
        ==> prime_ideal (ring_of_integers k)
                        (m INTER ring_carrier(ring_of_integers k))"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [valuation_subring])) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"subring_generated k v:A ring"), (← q r"I:A->A"), (← q r"m:A->bool")] PRIME_IDEAL_HOMOMORPHIC_PREIMAGE) THEN ANTS_TAC THENL [ASM_SIMP_TAC [MAXIMAL_IMP_PRIME_IDEAL] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"k:A ring"), (← q r"ring_carrier(ring_of_integers k:A ring)"), (← q r"v:A->bool"), (← q r"I:A->A")] RING_HOMOMORPHISM_BETWEEN_SUBRINGS) THEN REWRITE_TAC [RING_HOMOMORPHISM_I, IMAGE_I, RING_OF_INTEGERS_SUBRING] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC [VALUATION_SUBRING_RING_OF_INTEGERS], MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC [I_THM] THEN SET_TAC []])

  let VALUATION_SUBRING_DECOMPOSITION_RESIDUE ← prove
    r"!(k:A ring) v m Q.
        valuation_subring k v /\ maximal_ideal (subring_generated k v) m /\
        Q = m INTER ring_carrier(ring_of_integers k)
        ==> group_homomorphism
             (decomposition_group (subfield_generated k {ring_0 k},k) I Q,
              galois_group
               (subring_generated (quotient_ring (ring_of_integers k) Q)
                 (IMAGE (ring_coset (ring_of_integers k) Q)
                    {a | a IN ring_carrier(subfield_generated k {ring_0 k}) /\
                         a IN ring_carrier(ring_of_integers k)}),
                quotient_ring (ring_of_integers k) Q) I)
             (\f X. if X IN ring_carrier(quotient_ring (ring_of_integers k) Q)
                    then IMAGE f X else X) /\
            group_kernel
             (decomposition_group (subfield_generated k {ring_0 k},k) I Q,
              galois_group
               (subring_generated (quotient_ring (ring_of_integers k) Q)
                 (IMAGE (ring_coset (ring_of_integers k) Q)
                    {a | a IN ring_carrier(subfield_generated k {ring_0 k}) /\
                         a IN ring_carrier(ring_of_integers k)}),
                quotient_ring (ring_of_integers k) Q) I)
             (\f X. if X IN ring_carrier(quotient_ring (ring_of_integers k) Q)
                    then IMAGE f X else X) =
            group_carrier(inertia_group (subfield_generated k {ring_0 k},k) I
                            (ring_of_integers k) Q)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0(k:A ring)}"), (← q r"k:A ring"), (← q r"ring_of_integers k:A ring"), (← q r"Q:A->bool")] DECOMPOSITION_GROUP_RESIDUE_HOMOMORPHISM) THEN REWRITE_TAC [I_O_ID, I_THM] THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC [RING_OF_INTEGERS_SUBRING, DECOMPOSITION_GROUP_RING_OF_INTEGERS] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC PRIME_IMP_RING_IDEAL THEN MATCH_MP_TAC VALUATION_SUBRING_CONTRACTION_RING_OF_INTEGERS THEN EXISTS_TAC (← q r"v:A->bool") THEN ASM_REWRITE_TAC [])

  -- @@RETURN BEGIN
  return { VALUATION_SUBRING_RESIDUE_ALGEBRAICALLY_CLOSED, VALUATION_SUBRING_OVER_PRIME,
           VALUATION_SUBRING_RESIDUE_CHAR, VALUATION_SUBRING_RESIDUE_CHAR_CASES,
           ALGEBRAICALLY_CLOSED_VALUATION_OVER_PRIME,
           VALUATION_SUBRING_DECOMPOSITION_GROUP, VALUATION_SUBRING_RESIDUE_HOMOMORPHISM,
           VALUATION_SUBRING_RESIDUE_DIV, VALUATION_SUBRING_RING_OF_INTEGERS,
           VALUATION_SUBRING_CONTRACTION_RING_OF_INTEGERS,
           VALUATION_SUBRING_DECOMPOSITION_RESIDUE }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- valuation_residue.ml phrases from line 716 to 1181                     -/
/- ---------------------------------------------------------------------- -/

structure ValuationResidue02 where
  -- @@FIELDS
  NUMBER_FIELD_VALUATION_SUBRING_LOCALIZATION : thm
  VALUATION_SUBRING_NUMBER_SUBFIELD : thm
  VALUATION_SUBRING_NUMBER_SUBFIELD_VALUATION : thm
  ALGEBRAIC_VALUATION_SUBRING_LOCALIZATION : thm
  ALGEBRAIC_VALUATION_SUBRING_RESIDUE_ALGEBRAIC : thm
  ALGEBRAIC_CLOSURE_VALUATION_OVER_PRIME : thm
  ALGEBRAIC_VALUATION_SUBRING_DECOMPOSITION_GROUP : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupValuationResidue02 [HolBase] (D : ValuationResidueDeps) (BValuationResidue01 : ValuationResidue01) :
    ExceptT String IO ValuationResidue02 := do
  -- @@SCOPE BEGIN
  let { ASM_INT_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, RING_RULE, SET_TAC, TAUT, .. } := D
  let { ALGEBRAIC_OVER_DIV, CARRIER_SUBFIELD_GENERATED_SUBFIELD,
        CARRIER_SUBRING_GENERATED_SUBRING, CONTRAPOS_THM, DECOMPOSITION_GROUP,
        DEDEKIND_RING_OF_INTEGERS, DEDEKIND_VALUATION_IMAGE, DEDEKIND_VALUATION_INV,
        DEDEKIND_VALUATION_MUL, DEDEKIND_VALUATION_POS, DEDEKIND_VALUATION_PRIME_IDEAL,
        EQ_IMP, EXTENSION, FIELD_EXTENSION_SUBFIELD_GENERATED, FIELD_HOMOMORPHISM_INV,
        FIELD_IMP_INTEGRAL_DOMAIN, FIELD_INV_EQ_0, FIELD_MUL_RINV, FIELD_QUOTIENT_RING,
        FIELD_SUBFIELD_GENERATED, FIELD_UNIT, FORALL_IN_GSPEC, FORALL_IN_IMAGE,
        GALOIS_GROUP_IMAGE_INVERSE, GALOIS_GROUP_INVERSE, GALOIS_GROUP_PERMUTES,
        GALOIS_GROUP_RING_HOMOMORPHISM, GALOIS_GROUP_RING_OF_INTEGERS, IMAGE_I,
        INTEGRAL_DOMAIN_MUL_EQ_0, INT_LT_IMP_LE, INT_NOT_LT, IN_ELIM_THM, IN_IMAGE,
        IN_INSERT, IN_INTER, IN_RING_IDEAL_0, I_DEF, I_THM, LEFT_IMP_EXISTS_THM,
        MAXIMAL_IMP_RING_IDEAL, MONO_EXISTS, NOT_EXISTS_THM, PERMUTES_INJECTIVE,
        PERMUTES_INVERSES, PRIME_SUBFIELD_SUBFIELD_GENERATED, QUOTIENT_RING_0,
        QUOTIENT_RING_CARRIER, QUOTIENT_RING_MUL, RING_CHAR_SUBFIELD_GENERATED, .. } := D.core1
  let { RING_COSET_EQ_IDEAL, RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_MUL,
        RING_HOMOMORPHISM_RING_COSET, RING_HOMOMORPHISM_RING_OF_INTEGERS, RING_INV,
        RING_INV_INV, RING_INV_MUL, RING_INV_SUBFIELD_GENERATED,
        RING_MONOMORPHISM_INCLUSION, RING_OF_INT, RING_OF_INTEGERS,
        RING_OF_INTEGERS_ALGEBRAIC, RING_OF_INTEGERS_FRACTION_FIELD,
        RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE, RING_OF_INTEGERS_SUBFIELD_GENERATED,
        RING_OF_INTEGERS_SUBSET, RING_OF_INT_SUBFIELD_GENERATED, SUBFIELD_GENERATED,
        SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED, SUBFIELD_GENERATED_INC_GEN,
        SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC, SUBFIELD_OF_IMP_SUBSET,
        SUBFIELD_SUBFIELD_GENERATED, SUBRING_GENERATED, SUBSET,
        VALUATION_SUBRING_MAXIMAL_IDEAL, VALUATION_SUBRING_SUBFIELD,
        algebraic_extension, field_of_fractions, number_field, ring_div,
        ring_homomorphism, subring_of, valuation_subring, .. } := D.core2
  let { ALGEBRAICALLY_CLOSED_VALUATION_OVER_PRIME,
        VALUATION_SUBRING_CONTRACTION_RING_OF_INTEGERS,
        VALUATION_SUBRING_RING_OF_INTEGERS, .. } := BValuationResidue01
  -- @@SCOPE END

  let NUMBER_FIELD_VALUATION_SUBRING_LOCALIZATION ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!k s x t:A. s IN ring_carrier k /\ x IN ring_carrier k /\
                  t IN ring_carrier k /\ ring_mul k s t = ring_1 k
                  ==> x = ring_mul k (ring_mul k s x) t")
    prove
      r"!(k:A ring) v m.
          number_field k /\ valuation_subring k v /\
          maximal_ideal (subring_generated k v) m
          ==> v = {ring_div k a s | a,s |
                   a IN ring_carrier(ring_of_integers k) /\
                   s IN ring_carrier(ring_of_integers k) /\ ~(s IN m)}"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [valuation_subring])) THEN SUBGOAL_THEN (← q r"dedekind_domain(ring_of_integers k:A ring) /\
      field_of_fractions(ring_of_integers k,k) I /\
      ring_carrier(ring_of_integers k) SUBSET v /\
      prime_ideal (ring_of_integers k)
                  (m INTER ring_carrier(ring_of_integers k)) /\
      ring_0(ring_of_integers k) = ring_0 k /\
      ring_1(ring_of_integers k) = ring_1 k /\
      ring_carrier(ring_of_integers k) SUBSET ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_OF_INTEGERS_FRACTION_FIELD, RING_OF_INTEGERS, RING_OF_INTEGERS_SUBSET, I_THM] THEN CONJ_TAC THENL [MATCH_MP_TAC VALUATION_SUBRING_RING_OF_INTEGERS THEN ASM_REWRITE_TAC [], MATCH_MP_TAC VALUATION_SUBRING_CONTRACTION_RING_OF_INTEGERS THEN EXISTS_TAC (← q r"v:A->bool") THEN ASM_REWRITE_TAC []], ALL_TAC] THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN ABBREV_TAC (← q r"O = ring_of_integers(k:A ring)") THEN ABBREV_TAC (← q r"Q = m INTER ring_carrier(O:A ring)") THEN SUBGOAL_THEN (← q r"!s:A. s IN ring_carrier(O:A ring) /\ ~(s IN m)
            ==> ~(s = ring_0 k) /\ ring_inv k s IN v /\ s IN v") ASSUME_TAC THENL [X_GEN_TAC (← q r"s:A") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"v:A->bool"), (← q r"m:A->bool")] VALUATION_SUBRING_MAXIMAL_IDEAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~((s:A) IN {x | x IN v /\ (x = ring_0 k \/ ~(ring_inv k x IN v))})") THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(v:A->bool) SUBSET ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [subring_of], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x:A. x IN v
            ==> ?a b. a IN ring_carrier(O:A ring) /\ b IN ring_carrier O /\
                      ~(b IN m) /\ ring_mul k b x = a") ASSUME_TAC THENL [X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier k") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN ASM_CASES_TAC (← q r"Q = {ring_0(O:A ring)}") THENL [SUBGOAL_THEN (← q r"?a b:A. a IN ring_carrier O /\ b IN ring_carrier O /\
                  ~(b = ring_0 O) /\ ring_mul k (I b) x = I a") MP_TAC THENL [ASM_MESON_TAC [], REWRITE_TAC [I_THM]] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"a:A") THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"b:A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"?a b:A. a IN ring_carrier O /\ b IN ring_carrier O /\
                ~(b IN Q) /\ ring_mul k b x = a") MP_TAC THENL [ALL_TAC, MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"a:A") THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"b:A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ASM SET_TAC []] THEN MP_TAC (← ISPECL [(← q r"O:A ring"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"Q:A->bool"), (← q r"x:A")] DEDEKIND_VALUATION_POS) THEN ASM_REWRITE_TAC [I_THM] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_CASES_TAC (← q r"x:A = ring_0 k") THEN ASM_REWRITE_TAC [(← GSYM INT_NOT_LT)] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_inv k (x:A) IN ring_carrier k /\ ~(ring_inv k x = ring_0 k) /\
        &0 < dedekind_valuation (O,k) I Q (ring_inv k x)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_INV, FIELD_INV_EQ_0] THEN MP_TAC (← ISPECL [(← q r"O:A ring"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"Q:A->bool"), (← q r"x:A")] DEDEKIND_VALUATION_INV) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ASM_INT_ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"O:A ring"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"Q:A->bool"), (← q r"ring_inv k x:A")] DEDEKIND_VALUATION_POS) THEN ASM_SIMP_TAC [INT_LT_IMP_LE, I_THM] THEN REWRITE_TAC [NOT_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"~((b:A) IN m) /\ (a:A) IN ring_carrier k /\ (b:A) IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(b:A = ring_0 k) /\ ring_inv k b IN v") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(a:A = ring_0 k)") ASSUME_TAC THENL [UNDISCH_TAC (← q r"ring_mul k b (ring_inv k x) = (a:A)") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_MUL_EQ_0, FIELD_IMP_INTEGRAL_DOMAIN], ALL_TAC] THEN SUBGOAL_THEN (← q r"(a:A) IN m") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"(a:A) IN Q") MP_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN MP_TAC (← ISPECL [(← q r"O:A ring"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"Q:A->bool"), (← q r"a:A")] DEDEKIND_VALUATION_PRIME_IDEAL) THEN ASM_REWRITE_TAC [I_THM] THEN DISCH_THEN SUBST1_TAC THEN UNDISCH_TAC (← q r"ring_mul k b (ring_inv k x) = (a:A)") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"O:A ring"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"Q:A->bool"), (← q r"b:A"), (← q r"ring_inv k x:A")] DEDEKIND_VALUATION_MUL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"O:A ring"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"Q:A->bool"), (← q r"b:A")] DEDEKIND_VALUATION_IMAGE) THEN ASM_REWRITE_TAC [I_THM] THEN DISCH_THEN SUBST1_TAC THEN ASM_INT_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"~(ring_inv k (a:A) IN v)") MP_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"v:A->bool"), (← q r"m:A->bool")] VALUATION_SUBRING_MAXIMAL_IDEAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"a:A")) o (GEN_REWRITE_RULE id [EXTENSION]))) THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN MESON_TAC [], ALL_TAC] THEN UNDISCH_TAC (← q r"ring_mul k b (ring_inv k x) = (a:A)") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [RING_INV_MUL, RING_INV] THEN SUBGOAL_THEN (← q r"ring_inv k (ring_inv k x) = (x:A)") SUBST1_TAC THENL [MATCH_MP_TAC RING_INV_INV THEN ASM_SIMP_TAC [FIELD_UNIT], ALL_TAC] THEN REWRITE_TAC [] THEN ASM_MESON_TAC [subring_of], ALL_TAC] THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"x:A") THEN REWRITE_TAC [IN_ELIM_THM] THEN EQ_TAC THENL [DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"x:A"))) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"a:A") THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"s:A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [ring_div] THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN MATCH_MP_TAC r1 THEN SUBGOAL_THEN (← q r"(s:A) IN ring_carrier k /\ ~(s = ring_0 k)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [RING_INV, FIELD_MUL_RINV] THEN ASM SET_TAC [], REWRITE_TAC [LEFT_IMP_EXISTS_THM, ring_div] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"s:A")] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [SUBSET, subring_of]])

  let VALUATION_SUBRING_NUMBER_SUBFIELD ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"q ==> (p /\ q <=> p)")
    prove
      r"!(k:A ring) v m l.
          valuation_subring k v /\ maximal_ideal (subring_generated k v) m /\
          l subfield_of k /\ number_field(subfield_generated k l)
          ==> prime_ideal (ring_of_integers(subfield_generated k l))
               (m INTER
                ring_carrier(ring_of_integers(subfield_generated k l))) /\
              (!n. ring_of_int (subfield_generated k l) n IN
                   m INTER
                   ring_carrier(ring_of_integers(subfield_generated k l)) <=>
                   ring_of_int k n IN m) /\
              v INTER l =
              {ring_div k a s | a,s |
               a IN ring_carrier(ring_of_integers(subfield_generated k l)) /\
               s IN ring_carrier(ring_of_integers(subfield_generated k l)) /\
               ~(s IN m)}"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"v:A->bool"), (← q r"m:A->bool"), (← q r"l:A->bool")] VALUATION_SUBRING_SUBFIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_carrier(subfield_generated k l) = (l:A->bool) /\
      field(subfield_generated k l) /\
      ring_carrier(ring_of_integers(subfield_generated k l)) SUBSET l /\
      ring_0 k IN m") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"valuation_subring (k:A ring) v") THEN REWRITE_TAC [valuation_subring] THEN STRIP_TAC THEN ASM_SIMP_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD, FIELD_SUBFIELD_GENERATED] THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, CARRIER_SUBFIELD_GENERATED_SUBFIELD], MP_TAC (← ISPECL [(← q r"subring_generated k (v:A->bool)"), (← q r"m:A->bool")] MAXIMAL_IMP_RING_IDEAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (MATCH_MP IN_RING_IDEAL_0)) THEN REWRITE_TAC [(← CONJUNCT2 SUBRING_GENERATED)]], ALL_TAC] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"subfield_generated k (l:A->bool)"), (← q r"v INTER (l:A->bool)"), (← q r"m INTER (l:A->bool)")] VALUATION_SUBRING_CONTRACTION_RING_OF_INTEGERS) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC [], ALL_TAC] THEN CONJ_TAC THENL [GEN_TAC THEN REWRITE_TAC [RING_OF_INT_SUBFIELD_GENERATED, IN_INTER] THEN MATCH_MP_TAC r1 THEN MP_TAC (← ISPECL [(← q r"ring_of_integers(subfield_generated k (l:A->bool))"), (← q r"n:int")] RING_OF_INT) THEN REWRITE_TAC [RING_OF_INTEGERS, RING_OF_INT_SUBFIELD_GENERATED], MP_TAC (← ISPECL [(← q r"subfield_generated k (l:A->bool)"), (← q r"v INTER (l:A->bool)"), (← q r"m INTER (l:A->bool)")] NUMBER_FIELD_VALUATION_SUBRING_LOCALIZATION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_INTER] THEN X_GEN_TAC (← q r"x:A") THEN REWRITE_TAC [ring_div, (← CONJUNCT2 SUBFIELD_GENERATED)] THEN EQ_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"a:A") THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"s:A") THEN STRIP_TAC THEN (SUBGOAL_THEN (← q r"(s:A) IN l /\ ~(s = ring_0 k)") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC]) THEN ASM_SIMP_TAC [RING_INV_SUBFIELD_GENERATED] THEN ASM SET_TAC []])

  let VALUATION_SUBRING_NUMBER_SUBFIELD_VALUATION ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!k x s t:A. x IN ring_carrier k /\ s IN ring_carrier k /\
                  t IN ring_carrier k /\ ring_mul k s t = ring_1 k
                  ==> x = ring_mul k (ring_mul k s x) t")
    let r2 ← RING_RULE (← q r"!k a s t:A. a IN ring_carrier k /\ s IN ring_carrier k /\
                  t IN ring_carrier k /\ ring_mul k s t = ring_1 k
                  ==> ring_mul k s (ring_mul k a t) = a")
    prove
      r"!(k:A ring) v m l x.
          valuation_subring k v /\ maximal_ideal (subring_generated k v) m /\
          l subfield_of k /\ number_field(subfield_generated k l) /\
          ~(m INTER ring_carrier(ring_of_integers(subfield_generated k l)) =
            {ring_0 k}) /\
          x IN l /\ ~(x = ring_0 k)
          ==> (x IN v <=>
               &0 <= dedekind_valuation
                      (ring_of_integers(subfield_generated k l),
                       subfield_generated k l) I
                      (m INTER
                       ring_carrier(ring_of_integers(subfield_generated k l)))
                      x)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [valuation_subring])) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"v:A->bool"), (← q r"m:A->bool"), (← q r"l:A->bool")] VALUATION_SUBRING_NUMBER_SUBFIELD) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o CONJUNCT2)) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers(subfield_generated k (l:A->bool))"), (← q r"subfield_generated k (l:A->bool)"), (← q r"I:A->A"), (← q r"m INTER
       ring_carrier(ring_of_integers(subfield_generated k (l:A->bool)))"), (← q r"x:A")] DEDEKIND_VALUATION_POS) THEN MP_TAC (← ISPEC (← q r"subfield_generated k (l:A->bool)") RING_OF_INTEGERS_FRACTION_FIELD) THEN ASM_SIMP_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD, RING_OF_INTEGERS, (← CONJUNCT2 SUBFIELD_GENERATED), I_THM] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN DISCH_THEN SUBST1_TAC THEN SUBGOAL_THEN (← q r"(x:A) IN v <=> x IN v INTER l") SUBST1_TAC THENL [ASM SET_TAC [], ASM_REWRITE_TAC [] THEN REWRITE_TAC [IN_ELIM_THM, IN_INTER]] THEN SUBGOAL_THEN (← q r"ring_carrier(ring_of_integers(subfield_generated k (l:A->bool))) SUBSET
      ring_carrier k /\ ring_0 k IN m /\ (x:A) IN ring_carrier k") STRIP_ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_SUBFIELD_GENERATED] THEN REPEAT CONJ_TAC THENL [MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_SUBSET) THEN SET_TAC [], MP_TAC (← ISPECL [(← q r"subring_generated k (v:A->bool)"), (← q r"m:A->bool")] MAXIMAL_IMP_RING_IDEAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (MATCH_MP IN_RING_IDEAL_0)) THEN REWRITE_TAC [(← CONJUNCT2 SUBRING_GENERATED)], ASM_MESON_TAC [SUBFIELD_OF_IMP_SUBSET, SUBSET]], ALL_TAC] THEN EQ_TAC THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"s:A")] THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"a:A"), (← q r"s:A")] THEN ASM_REWRITE_TAC [] THEN (SUBGOAL_THEN (← q r"(a:A) IN ring_carrier k /\ (s:A) IN ring_carrier k /\
                   ~(s = ring_0 k)") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC]) THEN REWRITE_TAC [ring_div] THENL [ASM_REWRITE_TAC [ring_div] THEN MATCH_MP_TAC r2 THEN ASM_SIMP_TAC [RING_INV, FIELD_MUL_RINV], CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [RING_INV, FIELD_MUL_RINV]])

  let ALGEBRAIC_VALUATION_SUBRING_LOCALIZATION ← prove
    r"!(k:A ring) v m.
        ring_char k = 0 /\
        algebraic_extension(subfield_generated k {ring_0 k},k) I /\
        valuation_subring k v /\ maximal_ideal (subring_generated k v) m
        ==> v = {ring_div k a s | a,s |
                 a IN ring_carrier(ring_of_integers k) /\
                 s IN ring_carrier(ring_of_integers k) /\ ~(s IN m)}"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [valuation_subring])) THEN SUBGOAL_THEN (← q r"(v:A->bool) SUBSET ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [subring_of], ALL_TAC] THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"x:A") THEN REWRITE_TAC [IN_ELIM_THM] THEN EQ_TAC THENL [DISCH_TAC THEN ABBREV_TAC (← q r"l = ring_carrier(subfield_generated k
           ((x:A) INSERT ring_carrier(subfield_generated k {ring_0 k})))") THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"v:A->bool"), (← q r"m:A->bool"), (← q r"l:A->bool")] VALUATION_SUBRING_NUMBER_SUBFIELD) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN EXPAND_TAC "l" THEN ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED, SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED] THEN REWRITE_TAC [number_field, RING_CHAR_SUBFIELD_GENERATED, PRIME_SUBFIELD_SUBFIELD_GENERATED] THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"x:A")] SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC) THEN ASM_SIMP_TAC [FIELD_EXTENSION_SUBFIELD_GENERATED, IMAGE_I] THEN ANTS_TAC THENL [ASM_MESON_TAC [algebraic_extension, SUBSET], SIMP_TAC []], ALL_TAC] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"x:A")) o ((GEN_REWRITE_RULE id [EXTENSION]) o (CONJUNCT2 o CONJUNCT2)))) THEN REWRITE_TAC [IN_INTER, IN_ELIM_THM, RING_OF_INTEGERS_SUBFIELD_GENERATED] THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(x:A) IN l") (fun th => REWRITE_TAC [th]) THENL [EXPAND_TAC "l" THEN MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN REWRITE_TAC [IN_INSERT] THEN ASM SET_TAC [], MESON_TAC []], REWRITE_TAC [LEFT_IMP_EXISTS_THM, ring_div] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"s:A")] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ring_carrier(ring_of_integers k) SUBSET (v:A->bool)") ASSUME_TAC THENL [MATCH_MP_TAC VALUATION_SUBRING_RING_OF_INTEGERS THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"v:A->bool"), (← q r"m:A->bool")] VALUATION_SUBRING_MAXIMAL_IDEAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"s:A")) o (GEN_REWRITE_RULE id [EXTENSION]))) THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN SUBGOAL_THEN (← q r"(a:A) IN v /\ (s:A) IN v") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ASM_REWRITE_TAC []] THEN ASM_MESON_TAC [subring_of]])

  let ALGEBRAIC_VALUATION_SUBRING_RESIDUE_ALGEBRAIC ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!r y s t:B. y IN ring_carrier r /\ s IN ring_carrier r /\
                    t IN ring_carrier r /\ ring_mul r s t = ring_1 r
                    ==> y = ring_mul r (ring_mul r y s) t")
    let r2 ← RING_RULE (← q r"!k a s t:A. a IN ring_carrier k /\ s IN ring_carrier k /\
                    t IN ring_carrier k /\ ring_mul k s t = ring_1 k
                    ==> a = ring_mul k (ring_mul k a t) s")
    prove
      r"!(k:A ring) v m.
          ring_char k = 0 /\
          algebraic_extension(subfield_generated k {ring_0 k},k) I /\
          valuation_subring k v /\ maximal_ideal (subring_generated k v) m
          ==> algebraic_extension
               (subfield_generated (quotient_ring (subring_generated k v) m)
                 {ring_0(quotient_ring (subring_generated k v) m)},
                quotient_ring (subring_generated k v) m) I"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [valuation_subring])) THEN SUBGOAL_THEN (← q r"ring_ideal (subring_generated k v) (m:A->bool) /\
      field(quotient_ring (subring_generated k v) m) /\
      ring_carrier(subring_generated k v) = v /\
      ring_monomorphism(subring_generated k v,k) I /\
      ring_carrier(ring_of_integers k) SUBSET v") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [MAXIMAL_IMP_RING_IDEAL, FIELD_QUOTIENT_RING, CARRIER_SUBRING_GENERATED_SUBRING, VALUATION_SUBRING_RING_OF_INTEGERS] THEN REWRITE_TAC [I_DEF, RING_MONOMORPHISM_INCLUSION], ALL_TAC] THEN ABBREV_TAC (← q r"R = subring_generated k (v:A->bool)") THEN ABBREV_TAC (← q r"kq = quotient_ring R (m:A->bool)") THEN ASM_REWRITE_TAC [algebraic_extension, FIELD_EXTENSION_SUBFIELD_GENERATED] THEN EXPAND_TAC "kq" THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER] THEN ASM_REWRITE_TAC [FORALL_IN_GSPEC] THEN X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"v:A->bool"), (← q r"m:A->bool")] ALGEBRAIC_VALUATION_SUBRING_LOCALIZATION) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"y:A")) o (GEN_REWRITE_RULE id [EXTENSION]))) THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"s:A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(a:A) IN v /\ (s:A) IN v /\ ~(s = ring_0 k) /\ ring_inv k s IN v") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"v:A->bool"), (← q r"m:A->bool")] VALUATION_SUBRING_MAXIMAL_IDEAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"s:A")) o (GEN_REWRITE_RULE id [EXTENSION]))) THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!z:A. z IN ring_carrier(ring_of_integers k)
            ==> ring_coset R m z IN ring_carrier(ring_of_integers kq)") ASSUME_TAC THENL [X_GEN_TAC (← q r"z:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(z:A) IN ring_carrier(ring_of_integers R)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"R:A ring"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"z:A")] RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE) THEN ASM_REWRITE_TAC [I_THM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"R:A ring"), (← q r"kq:(A->bool)ring"), (← q r"ring_coset R (m:A->bool)")] RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN ANTS_TAC THENL [EXPAND_TAC "kq" THEN MATCH_MP_TAC RING_HOMOMORPHISM_RING_COSET THEN ASM_REWRITE_TAC [], ALL_TAC] THEN REWRITE_TAC [ring_homomorphism, SUBSET, FORALL_IN_IMAGE] THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_coset R m (y:A) IN ring_carrier kq /\
      ring_coset R m (s:A) IN ring_carrier kq /\
      ~(ring_coset R m s = ring_0 kq)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "kq" THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, QUOTIENT_RING_0, RING_COSET_EQ_IDEAL] THEN ASM SET_TAC [], ALL_TAC] THEN UNDISCH_TAC (← q r"y = ring_div k a (s:A)") THEN DISCH_THEN SUBST_ALL_TAC THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier k /\ (s:A) IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_coset R m (ring_div k a s:A) =
      ring_div kq (ring_coset R m a) (ring_coset R m s)") SUBST1_TAC THENL [SUBGOAL_THEN (← q r"ring_coset R m (a:A) =
        ring_mul kq (ring_coset R m (ring_div k a s)) (ring_coset R m s)") SUBST1_TAC THENL [EXPAND_TAC "kq" THEN ASM_SIMP_TAC [QUOTIENT_RING_MUL] THEN AP_TERM_TAC THEN EXPAND_TAC "R" THEN REWRITE_TAC [(← CONJUNCT2 SUBRING_GENERATED), ring_div] THEN MATCH_MP_TAC r2 THEN ASM_SIMP_TAC [RING_INV, FIELD_MUL_RINV], GEN_REWRITE_TAC RAND_CONV [ring_div] THEN MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [RING_INV, FIELD_MUL_RINV]], MATCH_MP_TAC ALGEBRAIC_OVER_DIV THEN ASM_SIMP_TAC [FIELD_EXTENSION_SUBFIELD_GENERATED, RING_OF_INTEGERS_ALGEBRAIC]])

  let ALGEBRAIC_CLOSURE_VALUATION_OVER_PRIME ← prove
    r"!(k:A ring) p.
        algebraically_closed_field k /\ ring_char k = 0 /\
        algebraic_extension(subfield_generated k {ring_0 k},k) I /\ prime p
        ==> ?v m. valuation_subring k v /\
                  maximal_ideal (subring_generated k v) m /\
                  (!n. ring_of_int k n IN m <=> &p divides n) /\
                  algebraically_closed_field
                   (quotient_ring (subring_generated k v) m) /\
                  ring_char(quotient_ring (subring_generated k v) m) = p /\
                  algebraic_extension
                   (subfield_generated
                     (quotient_ring (subring_generated k v) m)
                     {ring_0(quotient_ring (subring_generated k v) m)},
                    quotient_ring (subring_generated k v) m) I"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"p:num")] ALGEBRAICALLY_CLOSED_VALUATION_OVER_PRIME) THEN ASM_REWRITE_TAC [] THEN REPEAT (MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC ALGEBRAIC_VALUATION_SUBRING_RESIDUE_ALGEBRAIC THEN ASM_REWRITE_TAC [])

  let ALGEBRAIC_VALUATION_SUBRING_DECOMPOSITION_GROUP ← prove
    r"!(k:A ring) v m.
        ring_char k = 0 /\
        algebraic_extension(subfield_generated k {ring_0 k},k) I /\
        valuation_subring k v /\ maximal_ideal (subring_generated k v) m
        ==> group_carrier
             (decomposition_group (subfield_generated k {ring_0 k},k) I
                (m INTER ring_carrier(ring_of_integers k))) =
            {f | f IN group_carrier
                       (galois_group(subfield_generated k {ring_0 k},k) I) /\
                 IMAGE f v = v}"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [valuation_subring])) THEN SUBGOAL_THEN (← q r"(v:A->bool) SUBSET ring_carrier k /\
    ring_carrier(ring_of_integers k) SUBSET v") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [subring_of, VALUATION_SUBRING_RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"!g. g IN group_carrier
              (galois_group(subfield_generated k {ring_0 k},k) (I:A->A))
        ==> g permutes ring_carrier k /\
            (!x y. x IN ring_carrier k /\ y IN ring_carrier k
                   ==> g(ring_mul k x y) = ring_mul k (g x) (g y)) /\
            (!x. x IN ring_carrier k ==> g(ring_inv k x) = ring_inv k (g x)) /\
            g(ring_0 k) = ring_0 k /\
            IMAGE g (ring_carrier(ring_of_integers k)) SUBSET
            ring_carrier(ring_of_integers k)") (LABEL_TAC "aut") THENL [X_GEN_TAC (← q r"g:A->A") THEN DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM)) THEN REPEAT CONJ_TAC THENL [FIRST_ASSUM (ACCEPT_TAC o (MATCH_MP GALOIS_GROUP_PERMUTES)), MATCH_MP_TAC RING_HOMOMORPHISM_MUL THEN ASM_REWRITE_TAC [], MATCH_MP_TAC FIELD_HOMOMORPHISM_INV THEN ASM_REWRITE_TAC [], MATCH_MP_TAC RING_HOMOMORPHISM_0 THEN ASM_REWRITE_TAC [], FIRST_ASSUM (ACCEPT_TAC o (MATCH_MP GALOIS_GROUP_RING_OF_INTEGERS))], ALL_TAC] THEN SUBGOAL_THEN (← q r"!g. g IN group_carrier
              (galois_group(subfield_generated k {ring_0 k},k) (I:A->A)) /\
        IMAGE g (m INTER ring_carrier(ring_of_integers k)) =
        m INTER ring_carrier(ring_of_integers k)
        ==> IMAGE g v SUBSET v") ASSUME_TAC THENL [X_GEN_TAC (← q r"g:A->A") THEN STRIP_TAC THEN USE_THEN "aut" (MP_TAC o (SPEC (← q r"g:A->A"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"v:A->bool"), (← q r"m:A->bool")] ALGEBRAIC_VALUATION_SUBRING_LOCALIZATION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, FORALL_IN_GSPEC, IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"s:A")] THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"(g:A->A) a"), (← q r"(g:A->A) s")] THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier k /\ (s:A) IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [ring_div, RING_INV] THEN CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(g:A->A) s IN IMAGE g (m INTER ring_carrier(ring_of_integers k))") MP_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN REWRITE_TAC [IN_IMAGE, IN_INTER] THEN ASM_MESON_TAC [PERMUTES_INJECTIVE], ALL_TAC] THEN SUBGOAL_THEN (← q r"!g. g IN group_carrier
              (galois_group(subfield_generated k {ring_0 k},k) (I:A->A)) /\
        IMAGE g v = v
        ==> IMAGE g (m INTER ring_carrier(ring_of_integers k)) SUBSET
            m INTER ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [X_GEN_TAC (← q r"g:A->A") THEN STRIP_TAC THEN USE_THEN "aut" (MP_TAC o (SPEC (← q r"g:A->A"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"v:A->bool"), (← q r"m:A->bool")] VALUATION_SUBRING_MAXIMAL_IDEAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_INTER, IN_ELIM_THM] THEN X_GEN_TAC (← q r"q:A") THEN DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(q:A) IN ring_carrier k") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN REPEAT CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC, ASM SET_TAC []] THEN ASM_CASES_TAC (← q r"q:A = ring_0 k") THEN ASM_REWRITE_TAC [] THEN DISJ2_TAC THEN SUBGOAL_THEN (← q r"~(ring_inv k (q:A) IN v)") MP_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN REWRITE_TAC [CONTRAPOS_THM] THEN FIRST_X_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM (← MATCH_MP th (← ASSUME (← q r"(q:A) IN ring_carrier k"))))])) THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(g:A->A)(ring_inv k q) IN IMAGE g v") MP_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN REWRITE_TAC [IN_IMAGE] THEN ASM_MESON_TAC [PERMUTES_INJECTIVE], ALL_TAC] THEN REWRITE_TAC [DECOMPOSITION_GROUP] THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"f:A->A") THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_CASES_TAC (← q r"f IN group_carrier
          (galois_group(subfield_generated k {ring_0 k},k) (I:A->A))") THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_GROUP_PERMUTES)) THEN DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP PERMUTES_INVERSES)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP GALOIS_GROUP_INVERSE)) THEN EQ_TAC THEN DISCH_TAC THENL [MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"f:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"m INTER ring_carrier(ring_of_integers k):A->bool")] GALOIS_GROUP_IMAGE_INVERSE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"IMAGE (f:A->A) v SUBSET v /\ IMAGE (inverse f) v SUBSET v") MP_TAC THENL [ASM_MESON_TAC [], ALL_TAC], MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"f:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"v:A->bool")] GALOIS_GROUP_IMAGE_INVERSE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"IMAGE (f:A->A) (m INTER ring_carrier(ring_of_integers k)) SUBSET
      m INTER ring_carrier(ring_of_integers k) /\
      IMAGE (inverse f) (m INTER ring_carrier(ring_of_integers k)) SUBSET
      m INTER ring_carrier(ring_of_integers k)") MP_TAC THENL [ASM_MESON_TAC [], ALL_TAC]] THEN UNDISCH_TAC (← q r"!x:A. (f:A->A)(inverse f x) = x") THEN SET_TAC [])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_VALUATION_SUBRING_LOCALIZATION,
           VALUATION_SUBRING_NUMBER_SUBFIELD,
           VALUATION_SUBRING_NUMBER_SUBFIELD_VALUATION,
           ALGEBRAIC_VALUATION_SUBRING_LOCALIZATION,
           ALGEBRAIC_VALUATION_SUBRING_RESIDUE_ALGEBRAIC,
           ALGEBRAIC_CLOSURE_VALUATION_OVER_PRIME,
           ALGEBRAIC_VALUATION_SUBRING_DECOMPOSITION_GROUP }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- valuation_residue.ml phrases from line 1307 to 1451                    -/
/- ---------------------------------------------------------------------- -/

structure ValuationResidue03 where
  -- @@FIELDS
  ALGEBRAIC_VALUATION_SUBRING_DECOMPOSITION_INERTIA : thm
  ALGEBRAIC_VALUATION_SUBRING_RESIDUE_HOMOMORPHISM : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupValuationResidue03 [HolBase] (D : ValuationResidueDeps) (BValuationResidue01 : ValuationResidue01) (BValuationResidue02 : ValuationResidue02) :
    ExceptT String IO ValuationResidue03 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, SET_TAC, .. } := D
  let { CARRIER_SUBRING_GENERATED_SUBRING, DECOMPOSITION_GROUP, EXTENSION,
        FIELD_HOMOMORPHISM_INV, GALOIS_GROUP_PERMUTES, GALOIS_GROUP_RING_HOMOMORPHISM,
        GALOIS_GROUP_RING_OF_INTEGERS, IN_ELIM_THM, IN_IMAGE, IN_INTER,
        IN_RING_IDEAL_LMUL, IN_RING_IDEAL_RMUL, IN_RING_IDEAL_SUB, I_O_ID, I_THM,
        LEFT_IMP_EXISTS_THM, MAXIMAL_IMP_RING_IDEAL, PERMUTES_INJECTIVE, .. } := D.core1
  let { RING_HOMOMORPHISM_MUL, RING_OF_INTEGERS, RING_SUB, RING_SUB_SUBRING_GENERATED,
        SUBRING_GENERATED, decomposition_group, inertia_group, subring_of,
        valuation_subring, .. } := D.core2
  let { VALUATION_SUBRING_DECOMPOSITION_GROUP, VALUATION_SUBRING_RESIDUE_DIV,
        VALUATION_SUBRING_RESIDUE_HOMOMORPHISM, VALUATION_SUBRING_RING_OF_INTEGERS, .. } := BValuationResidue01
  let { ALGEBRAIC_VALUATION_SUBRING_DECOMPOSITION_GROUP,
        ALGEBRAIC_VALUATION_SUBRING_LOCALIZATION, .. } := BValuationResidue02
  -- @@SCOPE END

  let ALGEBRAIC_VALUATION_SUBRING_DECOMPOSITION_INERTIA ← prove
    r"!(k:A ring) v m.
        ring_char k = 0 /\
        algebraic_extension(subfield_generated k {ring_0 k},k) I /\
        valuation_subring k v /\ maximal_ideal (subring_generated k v) m
        ==> decomposition_group (subfield_generated k {ring_0 k},k) I
              (m INTER ring_carrier(ring_of_integers k)) =
            decomposition_group (subfield_generated k {ring_0 k},k) I m /\
            inertia_group (subfield_generated k {ring_0 k},k) I
              (ring_of_integers k) (m INTER ring_carrier(ring_of_integers k)) =
            inertia_group (subfield_generated k {ring_0 k},k) I
              (subring_generated k v) m"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!f. f IN group_carrier
              (galois_group(subfield_generated k {ring_0 k},k) (I:A->A))
        ==> (IMAGE f (m INTER ring_carrier(ring_of_integers k)) =
             m INTER ring_carrier(ring_of_integers k) <=> IMAGE f v = v) /\
            (IMAGE f m = m <=> IMAGE f v = v)") (LABEL_TAC "stab") THENL [X_GEN_TAC (← q r"f:A->A") THEN DISCH_TAC THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"v:A->bool"), (← q r"m:A->bool")] ALGEBRAIC_VALUATION_SUBRING_DECOMPOSITION_GROUP), MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"v:A->bool"), (← q r"m:A->bool")] VALUATION_SUBRING_DECOMPOSITION_GROUP)] THEN ASM_REWRITE_TAC [DECOMPOSITION_GROUP] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"f:A->A")) o (GEN_REWRITE_RULE id [EXTENSION]))) THEN ASM_REWRITE_TAC [IN_ELIM_THM], ALL_TAC] THEN CONJ_TAC THENL [REWRITE_TAC [decomposition_group] THEN AP_TERM_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"f:A->A") THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_CASES_TAC (← q r"f IN group_carrier
            (galois_group(subfield_generated k {ring_0 k},k) (I:A->A))") THEN ASM_SIMP_TAC [], ALL_TAC] THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [valuation_subring])) THEN SUBGOAL_THEN (← q r"(v:A->bool) SUBSET ring_carrier k /\
    ring_carrier(ring_of_integers k) SUBSET v /\
    ring_carrier(subring_generated k v) = v /\
    (!x y:A. x IN m /\ y IN v ==> ring_mul k x y IN m) /\
    (!x y:A. x IN v /\ y IN m ==> ring_mul k x y IN m) /\
    (!x y:A. x IN m /\ y IN m ==> ring_sub k x y IN m)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING, VALUATION_SUBRING_RING_OF_INTEGERS] THEN CONJ_TAC THENL [ASM_MESON_TAC [subring_of], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"subring_generated k (v:A->bool)"), (← q r"m:A->bool")] MAXIMAL_IMP_RING_IDEAL) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN REPEAT CONJ_TAC THEN MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"y:A")] THEN STRIP_TAC THENL [MP_TAC (← ISPECL [(← q r"subring_generated k (v:A->bool)"), (← q r"m:A->bool"), (← q r"x:A"), (← q r"y:A")] IN_RING_IDEAL_RMUL), MP_TAC (← ISPECL [(← q r"subring_generated k (v:A->bool)"), (← q r"m:A->bool"), (← q r"x:A"), (← q r"y:A")] IN_RING_IDEAL_LMUL), MP_TAC (← ISPECL [(← q r"subring_generated k (v:A->bool)"), (← q r"m:A->bool"), (← q r"x:A"), (← q r"y:A")] IN_RING_IDEAL_SUB)] THEN ASM_SIMP_TAC [(← CONJUNCT2 SUBRING_GENERATED), RING_SUB_SUBRING_GENERATED, CARRIER_SUBRING_GENERATED_SUBRING], ALL_TAC] THEN REWRITE_TAC [inertia_group] THEN AP_TERM_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"f:A->A") THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_CASES_TAC (← q r"f IN group_carrier
          (galois_group(subfield_generated k {ring_0 k},k) (I:A->A))") THEN ASM_REWRITE_TAC [] THEN USE_THEN "stab" (MP_TAC o (SPEC (← q r"f:A->A"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN ASM_CASES_TAC (← q r"IMAGE (f:A->A) v = v") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(f:A->A) permutes ring_carrier k /\
    (!x y. x IN ring_carrier (k:A ring) /\ y IN ring_carrier k
           ==> f(ring_mul k x y) = ring_mul k (f x) (f y)) /\
    (!x. x IN ring_carrier k ==> f(ring_inv k x) = ring_inv k (f x)) /\
    IMAGE f (ring_carrier(ring_of_integers k)) SUBSET
    ring_carrier(ring_of_integers k) /\
    IMAGE f (m INTER ring_carrier(ring_of_integers k)) =
    m INTER ring_carrier(ring_of_integers k)") STRIP_ASSUME_TAC THENL [FIRST_ASSUM (ASSUME_TAC o (MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM)) THEN REPEAT CONJ_TAC THENL [FIRST_ASSUM (ACCEPT_TAC o (MATCH_MP GALOIS_GROUP_PERMUTES)), MATCH_MP_TAC RING_HOMOMORPHISM_MUL THEN ASM_REWRITE_TAC [], MATCH_MP_TAC FIELD_HOMOMORPHISM_INV THEN ASM_REWRITE_TAC [], FIRST_ASSUM (ACCEPT_TAC o (MATCH_MP GALOIS_GROUP_RING_OF_INTEGERS)), USE_THEN "stab" (MP_TAC o (SPEC (← q r"f:A->A"))) THEN ASM_SIMP_TAC []], ALL_TAC] THEN EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THENL [FIRST_ASSUM (ASSUME_TAC o (MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"v:A->bool"), (← q r"m:A->bool")] ALGEBRAIC_VALUATION_SUBRING_LOCALIZATION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"x:A")) o (GEN_REWRITE_RULE id [EXTENSION]))) THEN ASM_REWRITE_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"s:A")] THEN STRIP_TAC THEN UNDISCH_TAC (← q r"x = ring_div k a (s:A)") THEN DISCH_THEN SUBST_ALL_TAC THEN SUBGOAL_THEN (← q r"(a:A) IN v /\ (s:A) IN v /\ (f:A->A) s IN v /\
      (f:A->A) s IN ring_carrier(ring_of_integers k)") STRIP_ASSUME_TAC THENL [MAP_EVERY UNDISCH_TAC [(← q r"ring_carrier(ring_of_integers k) SUBSET (v:A->bool)"), (← q r"IMAGE (f:A->A) (ring_carrier(ring_of_integers k)) SUBSET
         ring_carrier(ring_of_integers k)"), (← q r"(a:A) IN ring_carrier(ring_of_integers k)"), (← q r"(s:A) IN ring_carrier(ring_of_integers k)")] THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"~((f:A->A) s IN m)") ASSUME_TAC THENL [DISCH_TAC THEN SUBGOAL_THEN (← q r"(f:A->A) s IN IMAGE f (m INTER ring_carrier(ring_of_integers k))") MP_TAC THENL [ASM_REWRITE_TAC [IN_INTER], REWRITE_TAC [IN_IMAGE, IN_INTER]] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"w:A") STRIP_ASSUME_TAC) THEN UNDISCH_TAC (← q r"(f:A->A) s = f w") THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP PERMUTES_INJECTIVE th)])) THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sub k ((f:A->A) a) a IN m /\ ring_sub k ((f:A->A) s) s IN m") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"!x:A. x IN ring_carrier(ring_of_integers k)
              ==> ring_sub k (f x) x IN
                  m INTER ring_carrier(ring_of_integers k)") THEN ASM_SIMP_TAC [IN_INTER], ALL_TAC] THEN MATCH_MP_TAC VALUATION_SUBRING_RESIDUE_DIV THEN EXISTS_TAC (← q r"v:A->bool") THEN ASM_REWRITE_TAC [], REWRITE_TAC [IN_INTER] THEN CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC [], MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"(f:A->A) x"), (← q r"x:A")] RING_SUB) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC []]])

  let ALGEBRAIC_VALUATION_SUBRING_RESIDUE_HOMOMORPHISM ← prove
    r"!(k:A ring) v m.
        ring_char k = 0 /\
        algebraic_extension(subfield_generated k {ring_0 k},k) I /\
        valuation_subring k v /\ maximal_ideal (subring_generated k v) m
        ==> group_homomorphism
             (decomposition_group (subfield_generated k {ring_0 k},k) I
                (m INTER ring_carrier(ring_of_integers k)),
              galois_group
               (subring_generated (quotient_ring (subring_generated k v) m)
                 (IMAGE (ring_coset (subring_generated k v) m)
                    {a | a IN ring_carrier(subfield_generated k {ring_0 k}) /\
                         a IN v}),
                quotient_ring (subring_generated k v) m) I)
             (\f X. if X IN ring_carrier
                             (quotient_ring (subring_generated k v) m)
                    then IMAGE f X else X) /\
            group_kernel
             (decomposition_group (subfield_generated k {ring_0 k},k) I
                (m INTER ring_carrier(ring_of_integers k)),
              galois_group
               (subring_generated (quotient_ring (subring_generated k v) m)
                 (IMAGE (ring_coset (subring_generated k v) m)
                    {a | a IN ring_carrier(subfield_generated k {ring_0 k}) /\
                         a IN v}),
                quotient_ring (subring_generated k v) m) I)
             (\f X. if X IN ring_carrier
                             (quotient_ring (subring_generated k v) m)
                    then IMAGE f X else X) =
            group_carrier
             (inertia_group (subfield_generated k {ring_0 k},k) I
                (ring_of_integers k)
                (m INTER ring_carrier(ring_of_integers k)))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"v:A->bool"), (← q r"m:A->bool")] ALGEBRAIC_VALUATION_SUBRING_DECOMPOSITION_INERTIA) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN SUBST1_TAC) THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"v:A->bool"), (← q r"m:A->bool")] VALUATION_SUBRING_RESIDUE_HOMOMORPHISM) THEN ASM_REWRITE_TAC [I_O_ID, I_THM])

  -- @@RETURN BEGIN
  return { ALGEBRAIC_VALUATION_SUBRING_DECOMPOSITION_INERTIA,
           ALGEBRAIC_VALUATION_SUBRING_RESIDUE_HOMOMORPHISM }
  -- @@RETURN END

end HolANT.ValuationResidue
