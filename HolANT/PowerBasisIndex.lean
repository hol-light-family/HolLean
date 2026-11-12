/- ========================================================================= -/
/- ANT: Power bases                                                        -/
/- ========================================================================= -/
/- File: HolANT/PowerBasisIndex.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/power_basis_index.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antpowerbasisindexdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/products.ml, ANT/algmisc.ml, Library/isum.ml, ANT/integral.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/discriminant.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/classgroup.ml, ANT/nf_valuation.ml, ANT/prime_split.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/integrality.ml, ANT/relative_degree.ml, ANT/dedekind_kummer.ml, ANT/power_basis.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.PowerBasisIndex fills them).

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
import HolLibrary.Products
import HolANT.Algmisc
import HolLibrary.Isum
import HolANT.Integral
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolANT.IdealArith
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.IdealNorm
import HolANT.RingOfIntegers
import HolANT.NormIndex
import HolANT.Discriminant
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.Classgroup
import HolANT.NfValuation
import HolANT.PrimeSplit
import HolANT.TraceForm
import HolANT.RelativeSplit
import HolANT.Integrality
import HolANT.RelativeDegree
import HolANT.DedekindKummer
import HolANT.PowerBasis

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
open HolANT.NormIndex
open HolANT.Discriminant
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.Classgroup
open HolANT.NfValuation
open HolANT.PrimeSplit
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.Integrality
open HolANT.RelativeDegree
open HolANT.DedekindKummer
open HolANT.PowerBasis

namespace HolANT.PowerBasisIndex

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH ALGEBRA_TRACE_NORM_IN_CARRIER
   CARD_NUMSEG_LT COEFF_ABOVE_DEG COEFF_COMPOSE COEFF_IN_CARRIER_ALT
   COEFF_POLY_DERIV COEFF_POLY_MUL_X_MINUS EQ_TRANS EXISTS_UNIQUE_THM EXTENSION
   EXTENSIONAL_EQ EXTENSION_DEGREE_SIMPLE FIELD_EXTENSION_SUBFIELD_GENERATED
   FIELD_HOMOMORPHISM_INV FIELD_IMP_INTEGRAL_DOMAIN FIELD_IMP_NONTRIVIAL_RING
   FIELD_MUL_LINV FIELD_RING_HOMOMORPHISM_MONOMORPHISM FIELD_SUBFIELD_GENERATED
   FINITE_DELETE FINITE_NUMSEG_LT FORALL_IN_IMAGE FREE_BASIS_FIELD
   FREE_BASIS_IN_CARRIER FUN_EQ_THM HAS_SIZE_0 HAS_SIZE_CLAUSES HAS_SIZE_INDEX
   IMAGE_I IMP_CONJ_ALT INTEGER_RING INTEGRAL_DOMAIN_MUL_LCANCEL
   INTEGRAL_DOMAIN_POLY_RING INTEGRAL_DOMAIN_PRODUCT_EQ_0 INT_ABS_MUL
   INT_ABS_NUM INT_ABS_POS INT_ABS_POW INT_MUL_LID INT_OF_NUM_POW INT_POS
   INT_POW_ONE IN_DELETE IN_ELIM_THM IN_IMAGE IN_SING IN_SUBFIELD_0
   IN_SUBFIELD_INV IN_SUBFIELD_MUL IN_SUBRING_1 IN_SUBRING_ADD IN_SUBRING_INT
   IN_SUBRING_MUL IN_SUBRING_NUM IN_SUBRING_POW IN_SUBRING_SUM IN_UNIV I_O_ID
   I_THM LE_REFL MINIMAL_POLYNOMIAL_DIVIDES MINIMAL_POLYNOMIAL_IN_CARRIER
   MINIMAL_POLYNOMIAL_MONIC MINIMAL_POLYNOMIAL_VANISHES_HOMOMORPHIC_IMAGE
   MONIC_DIVIDES_EQ MONIC_HOMOMORPHIC_IMAGE MONIC_IMP_NONZERO MONIC_POLY_0
   MONIC_POLY_EQ_ROOTS_PRODUCT MONIC_X_MINUS_A MONO_EXISTS NOT_EXISTS_THM
   NOT_IN_EMPTY NUMBER_FIELD_ALGEBRAIC NUMBER_FIELD_DEGREE_POS
   NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS NUMBER_FIELD_DISCRIMINANT_INDEX
   NUMBER_FIELD_FREE_BASIS_POWERS NUMBER_FIELD_HOMOMORPHISMS_HAS_SIZE
   NUMBER_FIELD_IMP_FIELD NUMBER_FIELD_INTEGRAL_MULTIPLE
   NUMBER_FIELD_TRACE_FORM_INJECTIVE NUMBER_FIELD_TRACE_HOMOMORPHISMS
   NUMBER_FIELD_TRACE_IN_RING_OF_INTEGERS NUMBER_FIELD_TRACE_MUL_LINCOMB
   NUM_OF_INT_MUL NUM_OF_INT_OF_NUM ONE POLY_COMPOSE_HOMOMORPHISM_CONST
   POLY_COMPOSE_HOMOMORPHISM_MUL POLY_COMPOSE_HOMOMORPHISM_SUB
   POLY_COMPOSE_HOMOMORPHISM_VAR POLY_CONST_1 POLY_DEG_MONOMORPHIC_IMAGE
   POLY_DEG_MUL_X_MINUS_A POLY_DERIV_HOMOMORPHIC_IMAGE POLY_DERIV_IN_CARRIER
   POLY_DISCRIMINANT_HOMOMORPHISM POLY_DISCRIMINANT_IN_CARRIER
   POLY_DISCRIMINANT_VANDERMONDE POLY_EVAL_DERIV_RING_PRODUCT_X_MINUS
   POLY_EXTEND POLY_EXTEND_EVALUATE POLY_EXTEND_HOMOMORPHIC_IMAGE
   POLY_EXTEND_UNIVARIATE POLY_MUL_0 POLY_RING : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (POLY_RING_CLAUSES RIGHT_IMP_EXISTS_THM RING_0 RING_1
   RING_CARRIER_SUBFIELD_GENERATED_SUBSET RING_CHAR_MONOMORPHIC_IMAGE
   RING_COSET_EQ RING_DET RING_DET_EQ RING_HOMOMORPHISMS_EQ_FROM_RING_SPAN
   RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED RING_HOMOMORPHISM_0
   RING_HOMOMORPHISM_1 RING_HOMOMORPHISM_FROM_SUBRING_GENERATED
   RING_HOMOMORPHISM_INTEGER_RING_OF_INT RING_HOMOMORPHISM_IN_CARRIER
   RING_HOMOMORPHISM_MUL RING_HOMOMORPHISM_POW
   RING_HOMOMORPHISM_SUBFIELD_INCLUSION RING_INT_LINCOMB
   RING_INT_LINCOMB_LINCOMB RING_INV RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_MUL
   RING_MUL_ASSOC RING_MUL_INT_LINCOMB RING_MUL_LID RING_MUL_LZERO RING_MUL_RID
   RING_MUL_RZERO RING_MUL_SYM RING_OF_INT RING_OF_INTEGERS
   RING_OF_INTEGERS_CARRIER RING_OF_INTEGERS_INTEGER_MINIMAL_POLYNOMIAL
   RING_OF_INTEGERS_MINIMAL_POLYNOMIAL_Q RING_OF_INTEGERS_SUBRING
   RING_OF_INTEGERS_SUBSET RING_OF_INT_0 RING_OF_INT_1 RING_OF_INT_EQ_0_CHAR_0
   RING_OF_INT_EQ_CHAR_0 RING_OF_INT_IN_RING_OF_INTEGERS
   RING_OF_INT_IN_SUBFIELD_GENERATED RING_OF_INT_ISUM RING_OF_INT_MUL
   RING_OF_INT_NEG RING_OF_INT_SUBFIELD_GENERATED RING_OF_NUM_SUBFIELD_GENERATED
   RING_POLYNOMIAL RING_POLYNOMIAL_COMPOSE RING_POLYNOMIAL_CONST
   RING_POLYNOMIAL_IMP_POWERSERIES RING_POLYNOMIAL_SUB RING_POLYNOMIAL_VAR
   RING_POW RING_POWERSERIES_CONST RING_POWERSERIES_VAR RING_POW_ONE
   RING_PRODUCT RING_PRODUCT_DELETE RING_SUB_EQ_0 RING_SUB_RZERO RING_SUM
   RING_SUM_DELTA RING_SUM_EQ RING_SUM_IMAGE RING_SUM_LAGRANGE_COEFF SING_SUBSET
   SKOLEM_THM SUBFIELDS_GENERATED_EQ SUBFIELD_GENERATED SUBFIELD_GENERATED_EQ
   SUBFIELD_GENERATED_INSERT SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC
   SUBFIELD_SUBFIELD_GENERATED SUBRING_GENERATED_BY_SUBFIELD_GENERATED
   SUBRING_GENERATED_INC SUBRING_GENERATED_INDEX_COPRIME
   SUBRING_GENERATED_INT_LINCOMB SUBRING_GENERATED_MINIMAL
   SUBRING_SUBRING_GENERATED SUBRING_SUBSET_SUBFIELD_GENERATED SUBSET
   SUBSET_ANTISYM SUBSET_ANTISYM_EQ SUB_0 UNWIND_THM2 algebraic_extension
   basis_discriminant field_extension integral_element monic num_divides
   number_field o_DEF o_THM poly_eval ring_basis ring_div ring_monomorphism
   ring_polynomial ring_pow ring_powerseries ring_spanning squarefree subring_of : thm)
  deriving Inhabited

/-- What power_basis_index.ml uses from Session besides theorems. -/
structure PowerBasisIndexDeps where
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
/- power_basis_index.ml phrases from line 89 to 723                       -/
/- ---------------------------------------------------------------------- -/

structure PowerBasisIndex01 where
  -- @@FIELDS
  NUMBER_FIELD_POWER_BASIS_HOMOMORPHISMS : thm
  NUMBER_FIELD_POWER_BASIS_POLY_DISCRIMINANT : thm
  NUMBER_FIELD_GENERATOR_MINIMAL_POLYNOMIAL_DEGREE : thm
  NUMBER_FIELD_POLY_DISCRIMINANT_INDEX : thm
  NUMBER_FIELD_POLY_DISCRIMINANT_INDEX_INTEGER : thm
  NUMBER_FIELD_POLY_DISCRIMINANT_SQUAREFREE : thm
  NUMBER_FIELD_POLY_DISCRIMINANT_INDEX_COPRIME : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupPowerBasisIndex01 [HolBase] (D : PowerBasisIndexDeps) :
    ExceptT String IO PowerBasisIndex01 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, INTEGER_RULE, MESON_TAC, NUMBER_RULE, SET_RULE, SET_TAC, TAUT, .. } := D
  let { ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH, CARD_NUMSEG_LT, COEFF_COMPOSE,
        EXISTS_UNIQUE_THM, EXTENSION, EXTENSIONAL_EQ, EXTENSION_DEGREE_SIMPLE,
        FIELD_EXTENSION_SUBFIELD_GENERATED, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_IMP_NONTRIVIAL_RING, FIELD_RING_HOMOMORPHISM_MONOMORPHISM,
        FIELD_SUBFIELD_GENERATED, FINITE_NUMSEG_LT, FORALL_IN_IMAGE, FREE_BASIS_FIELD,
        FUN_EQ_THM, HAS_SIZE_0, HAS_SIZE_CLAUSES, HAS_SIZE_INDEX, IMAGE_I,
        IMP_CONJ_ALT, INTEGER_RING, INT_ABS_MUL, INT_ABS_NUM, INT_ABS_POS, INT_ABS_POW,
        INT_MUL_LID, INT_OF_NUM_POW, INT_POS, INT_POW_ONE, IN_ELIM_THM, IN_IMAGE,
        IN_SING, IN_SUBFIELD_0, IN_UNIV, I_O_ID, I_THM, LE_REFL,
        MINIMAL_POLYNOMIAL_DIVIDES, MINIMAL_POLYNOMIAL_IN_CARRIER,
        MINIMAL_POLYNOMIAL_MONIC, MINIMAL_POLYNOMIAL_VANISHES_HOMOMORPHIC_IMAGE,
        MONIC_DIVIDES_EQ, MONIC_HOMOMORPHIC_IMAGE, MONIC_POLY_EQ_ROOTS_PRODUCT,
        MONO_EXISTS, NOT_IN_EMPTY, NUMBER_FIELD_ALGEBRAIC,
        NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS, NUMBER_FIELD_DISCRIMINANT_INDEX,
        NUMBER_FIELD_FREE_BASIS_POWERS, NUMBER_FIELD_HOMOMORPHISMS_HAS_SIZE,
        NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_TRACE_HOMOMORPHISMS, NUM_OF_INT_MUL,
        NUM_OF_INT_OF_NUM, ONE, POLY_CONST_1, POLY_DEG_MONOMORPHIC_IMAGE,
        POLY_DERIV_HOMOMORPHIC_IMAGE, POLY_DERIV_IN_CARRIER,
        POLY_DISCRIMINANT_HOMOMORPHISM, POLY_DISCRIMINANT_IN_CARRIER,
        POLY_DISCRIMINANT_VANDERMONDE, POLY_EVAL_DERIV_RING_PRODUCT_X_MINUS,
        POLY_EXTEND_EVALUATE, POLY_EXTEND_HOMOMORPHIC_IMAGE, POLY_RING, .. } := D.core1
  let { RING_0, RING_1, RING_CARRIER_SUBFIELD_GENERATED_SUBSET,
        RING_CHAR_MONOMORPHIC_IMAGE, RING_COSET_EQ, RING_DET, RING_DET_EQ,
        RING_HOMOMORPHISMS_EQ_FROM_RING_SPAN,
        RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED, RING_HOMOMORPHISM_0,
        RING_HOMOMORPHISM_1, RING_HOMOMORPHISM_FROM_SUBRING_GENERATED,
        RING_HOMOMORPHISM_INTEGER_RING_OF_INT, RING_HOMOMORPHISM_IN_CARRIER,
        RING_HOMOMORPHISM_POW, RING_HOMOMORPHISM_SUBFIELD_INCLUSION,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL_LID, RING_OF_INTEGERS,
        RING_OF_INTEGERS_CARRIER, RING_OF_INTEGERS_INTEGER_MINIMAL_POLYNOMIAL,
        RING_OF_INTEGERS_SUBRING, RING_OF_INTEGERS_SUBSET, RING_OF_INT_EQ_CHAR_0,
        RING_OF_INT_SUBFIELD_GENERATED, RING_POLYNOMIAL, RING_POLYNOMIAL_COMPOSE,
        RING_POLYNOMIAL_IMP_POWERSERIES, RING_POW, RING_POW_ONE, RING_SUB_RZERO,
        RING_SUM_IMAGE, SING_SUBSET, SUBFIELDS_GENERATED_EQ, SUBFIELD_GENERATED_INSERT,
        SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC, SUBRING_GENERATED_BY_SUBFIELD_GENERATED,
        SUBRING_GENERATED_INDEX_COPRIME, SUBRING_GENERATED_INT_LINCOMB,
        SUBRING_GENERATED_MINIMAL, SUBRING_SUBRING_GENERATED, SUBSET, SUBSET_ANTISYM,
        UNWIND_THM2, algebraic_extension, basis_discriminant, field_extension,
        integral_element, monic, num_divides, number_field, o_DEF, o_THM, poly_eval,
        ring_basis, ring_monomorphism, ring_polynomial, ring_powerseries,
        ring_spanning, squarefree, subring_of, .. } := D.core2
  -- @@SCOPE END

  let NUMBER_FIELD_POWER_BASIS_HOMOMORPHISMS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ q /\ (p /\ q ==> r) ==> p /\ q /\ r")
    prove
      r"!(k:A ring) a f m.
          number_field k /\ a IN ring_carrier k /\
          f = minimal_polynomial (subfield_generated k {ring_0 k},k) I a /\
          m = extension_degree (subfield_generated k {ring_0 k},k) I /\
          poly_deg (subfield_generated k {ring_0 k}) f = m
          ==> ?(l:(A#num)ring) g e.
                field l /\ ring_monomorphism(k,l) g /\
                (!i. i < m ==> ring_homomorphism(k,l) (e i) /\
                               e i a IN ring_carrier l) /\
                (!i y. i < m /\
                       y IN ring_carrier(subfield_generated k {ring_0 k})
                       ==> e i y = g y) /\
                (!u v. u < m /\ v < m ==> (e u a = e v a <=> u = v)) /\
                g o f =
                ring_product (poly_ring l (:1)) {i | i < m}
                  (\i. poly_sub l (poly_var l one) (poly_const l (e i a))) /\
                (!i. i < m
                     ==> e i (poly_extend (subfield_generated k {ring_0 k},k) I
                                (\v. a)
                                (poly_deriv (subfield_generated k {ring_0 k})
                                   f)) =
                         ring_product l ({t | t < m} DELETE i)
                           (\t. ring_sub l (e i a) (e t a))) /\
                (!x. x IN ring_carrier k
                     ==> g(algebra_trace (subfield_generated k {ring_0 k},k) I
                             x) =
                         ring_sum l {i | i < m} (\i. e i x))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM (ASSUME_TAC o (SYM o (checkM (fun th => (do let z9 ← (q r"m:num"); let z8 ← (do let z6 ← (do let z7 ← (pure th); pure (concl z7)); liftExcept (lhs z6)); pure (z8 == z9)))))) THEN FIRST_X_ASSUM (ASSUME_TAC o (SYM o (checkM (fun th => (do let z5 ← (q r"f:(1->num)->A"); let z4 ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); liftExcept (lhs z2)); pure (z4 == z5)))))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A")] NUMBER_FIELD_FREE_BASIS_POWERS) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [number_field])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN (← q r"algebraic_over (subfield_generated k {ring_0 k},k) (I:A->A) a /\
        field_extension (subfield_generated k {ring_0 k},k) (I:A->A)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [NUMBER_FIELD_ALGEBRAIC, FIELD_EXTENSION_SUBFIELD_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_polynomial (subfield_generated k {ring_0 k}) (f:(1->num)->A) /\
        monic (subfield_generated k {ring_0 k}) f") STRIP_ASSUME_TAC THENL [EXPAND_TAC "f" THEN ASM_SIMP_TAC [RING_POLYNOMIAL, MINIMAL_POLYNOMIAL_IN_CARRIER, MINIMAL_POLYNOMIAL_MONIC], ALL_TAC] THEN MP_TAC (← ISPEC (← q r"k:A ring") ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN ASM_REWRITE_TAC [algebraic_extension, field_extension] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"l:(A#num)ring") (X_CHOOSE_THEN (← q r"g:A->A#num") STRIP_ASSUME_TAC)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN SUBGOAL_THEN (← q r"ring_char(l:(A#num)ring) = 0") ASSUME_TAC THENL [ASM_MESON_TAC [RING_CHAR_MONOMORPHIC_IMAGE], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:(A#num)ring")] NUMBER_FIELD_HOMOMORPHISMS_HAS_SIZE) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"E = {h:A->A#num | ring_homomorphism(k,l) h /\
                          h IN EXTENSIONAL(ring_carrier k)}") THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP HAS_SIZE_INDEX)) THEN REWRITE_TAC [EXISTS_UNIQUE_THM] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"e:num->A->A#num") (fun th0 => tactic_of do pure ((← do let (th1, th2) ← (do pure (← CONJ_PAIR th0)); pure (SUBGOAL_THEN (← q r"!i j. i < m /\ j < m ==> ((e:num->A->A#num) i = e j <=> i = j)") ASSUME_TAC THENL [MESON_TAC [th1, th2], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. i < m ==> ring_homomorphism(k,l) ((e:num->A->A#num) i) /\                       e i IN EXTENSIONAL(ring_carrier k)") ASSUME_TAC THENL [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN MP_TAC (← SPEC (← q r"i:num") th1) THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "E" THEN SIMP_TAC [IN_ELIM_THM], ALL_TAC] THEN SUBGOAL_THEN (← q r"E = IMAGE (e:num->A->A#num) {i | i < m}") SUBST_ALL_TAC THENL [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN MESON_TAC [th1, th2], ALL_TAC]))))) THEN SUBGOAL_THEN (← q r"!i y. i < m /\ y IN ring_carrier(subfield_generated k {ring_0 k})
              ==> (e:num->A->A#num) i y = g y") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"(e:num->A->A#num) i"), (← q r"g:A->A#num"), (← q r"k:A ring"), (← q r"l:(A#num)ring"), (← q r"{ring_0 k:A}")] RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED) THEN ASM_SIMP_TAC [IN_SING, (← ISPECL [(← q r"k:A ring"), (← q r"l:(A#num)ring")] RING_HOMOMORPHISM_0)], ALL_TAC] THEN SUBGOAL_THEN (← q r"!u v. u < m /\ v < m
              ==> ((e:num->A->A#num) u a = e v a <=> u = v)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(e:num->A->A#num) u = e v") MP_TAC THENL [ALL_TAC, ASM_SIMP_TAC []] THEN MATCH_MP_TAC EXTENSIONAL_EQ THEN EXISTS_TAC (← q r"ring_carrier k:A->bool") THEN ASM_SIMP_TAC [] THEN SUBGOAL_THEN (← q r"ring_span (subfield_generated k {ring_0 k},k) I
           (IMAGE (\i. ring_pow k (a:A) i) {i | i < m}) = ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [FREE_BASIS_FIELD, FIELD_SUBFIELD_GENERATED, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, ring_basis, ring_spanning], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"(e:num->A->A#num) u"), (← q r"(e:num->A->A#num) v"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"l:(A#num)ring"), (← q r"IMAGE (\i. ring_pow k (a:A) i) {i | i < m}")] RING_HOMOMORPHISMS_EQ_FROM_RING_SPAN) THEN ANTS_TAC THENL [ASM_SIMP_TAC [I_THM, IMP_CONJ_ALT, FORALL_IN_IMAGE, IN_ELIM_THM, (← ISPECL [(← q r"k:A ring"), (← q r"l:(A#num)ring")] RING_HOMOMORPHISM_POW)], ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. i < m ==> (e:num->A->A#num) i o (f:(1->num)->A) = g o f") ASSUME_TAC THENL [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN REWRITE_TAC [FUN_EQ_THM, o_THM] THEN X_GEN_TAC (← q r"u:1->num") THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"ring_polynomial (subfield_generated k {ring_0 k}) (f:(1->num)->A)") THEN SIMP_TAC [ring_polynomial, ring_powerseries], ALL_TAC] THEN UNDISCH_THEN (← q r"!i y. i < m /\ y IN ring_carrier(subfield_generated k {ring_0 k})
              ==> (e:num->A->A#num) i y = g y") (fun (_ : thm) => ALL_TAC) THEN SUBGOAL_THEN (← q r"!i. i < m ==> (e:num->A->A#num) i a IN ring_carrier l") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN EXISTS_TAC (← q r"k:A ring") THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_monomorphism(subfield_generated k {ring_0 k},l) (g:A->A#num)") ASSUME_TAC THENL [MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, FIELD_IMP_NONTRIVIAL_RING] THEN MP_TAC (← ISPECL [(← q r"g:A->A#num"), (← q r"k:A ring"), (← q r"l:(A#num)ring"), (← q r"ring_carrier(subfield_generated k {ring_0 k:A})")] RING_HOMOMORPHISM_FROM_SUBRING_GENERATED) THEN ASM_REWRITE_TAC [SUBRING_GENERATED_BY_SUBFIELD_GENERATED], FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM))] THEN SUBGOAL_THEN (← q r"ring_polynomial l ((g:A->A#num) o f) /\ poly_deg l (g o f) = m /\
        monic l (g o f)") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r1 THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC RING_POLYNOMIAL_COMPOSE THEN EXISTS_TAC (← q r"subfield_generated k {ring_0 k:A}") THEN ASM_REWRITE_TAC [], MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_0 k:A}"), (← q r"l:(A#num)ring"), (← q r"g:A->A#num"), (← q r"f:(1->num)->A")] POLY_DEG_MONOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [], STRIP_TAC THEN UNDISCH_TAC (← q r"monic (subfield_generated k {ring_0 k}) (f:(1->num)->A)") THEN ASM_REWRITE_TAC [monic, COEFF_COMPOSE] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_0 k:A}"), (← q r"l:(A#num)ring"), (← q r"g:A->A#num")] RING_HOMOMORPHISM_1) THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"(g:A->A#num) o (f:(1->num)->A) =
        ring_product (poly_ring l (:1)) {i | i < m}
          (\i. poly_sub l (poly_var l one)
                          (poly_const l ((e:num->A->A#num) i a)))") ASSUME_TAC THENL [MATCH_MP_TAC MONIC_POLY_EQ_ROOTS_PRODUCT THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, (← GSYM RING_POLYNOMIAL), FINITE_NUMSEG_LT, CARD_NUMSEG_LT, IN_ELIM_THM] THEN CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"(e:num->A->A#num) i"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"l:(A#num)ring"), (← q r"a:A")] MINIMAL_POLYNOMIAL_VANISHES_HOMOMORPHIC_IMAGE) THEN ASM_SIMP_TAC [I_O_ID], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. i < m
            ==> (e:num->A->A#num) i
                  (poly_extend (subfield_generated k {ring_0 k},k) I (\v. a)
                     (poly_deriv (subfield_generated k {ring_0 k}) f)) =
                poly_eval l (poly_deriv l ((g:A->A#num) o (f:(1->num)->A)))
                  (e i a)") ASSUME_TAC THENL [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_homomorphism(subfield_generated k {ring_0 k},l)
                           ((e:num->A->A#num) i)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"(e:num->A->A#num) i"), (← q r"k:A ring"), (← q r"l:(A#num)ring"), (← q r"ring_carrier(subfield_generated k {ring_0 k:A})")] RING_HOMOMORPHISM_FROM_SUBRING_GENERATED) THEN ASM_SIMP_TAC [SUBRING_GENERATED_BY_SUBFIELD_GENERATED], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"l:(A#num)ring"), (← q r"I:A->A"), (← q r"(:1)"), (← q r"\v:1. (a:A)"), (← q r"(e:num->A->A#num) i"), (← q r"poly_deriv (subfield_generated k {ring_0 k:A}) f")] POLY_EXTEND_HOMOMORPHIC_IMAGE) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION, POLY_DERIV_IN_CARRIER, (← GSYM RING_POLYNOMIAL), SUBSET, FORALL_IN_IMAGE, I_O_ID] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [POLY_EXTEND_EVALUATE] THEN REWRITE_TAC [poly_eval] THEN BINOP_TAC THENL [MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_0 k:A}"), (← q r"l:(A#num)ring"), (← q r"(e:num->A->A#num) i"), (← q r"f:(1->num)->A")] POLY_DERIV_HOMOMORPHIC_IMAGE) THEN ASM_SIMP_TAC [RING_POLYNOMIAL_IMP_POWERSERIES], REWRITE_TAC [o_DEF]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. i < m
            ==> poly_eval l (poly_deriv l ((g:A->A#num) o (f:(1->num)->A)))
                  ((e:num->A->A#num) i a) =
                ring_product l ({t | t < m} DELETE i)
                  (\t. ring_sub l (e i a) (e t a))") ASSUME_TAC THENL [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"l:(A#num)ring"), (← q r"\t. (e:num->A->A#num) t a"), (← q r"{t:num | t < m}"), (← q r"i:num")] POLY_EVAL_DERIV_RING_PRODUCT_X_MINUS) THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x. x IN ring_carrier k
            ==> (g:A->A#num)
                  (algebra_trace (subfield_generated k {ring_0 k},k) I x) =
                ring_sum l {i | i < m} (\i. (e:num->A->A#num) i x)") ASSUME_TAC THENL [X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:(A#num)ring"), (← q r"IMAGE (e:num->A->A#num) {i | i < m}"), (← q r"g:A->A#num"), (← q r"x:A")] NUMBER_FIELD_TRACE_HOMOMORPHISMS) THEN ANTS_TAC THENL [ASM_SIMP_TAC [FORALL_IN_IMAGE, SUBSET, IN_ELIM_THM], DISCH_THEN SUBST1_TAC] THEN wPart lhand (lhand o rand) RING_SUM_IMAGE THEN ANTS_TAC THENL [REWRITE_TAC [IN_ELIM_THM] THEN UNDISCH_TAC (← q r"!i j. i < m /\ j < m ==> ((e:num->A->A#num) i = e j <=> i = j)") THEN MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [o_DEF], ALL_TAC] THEN MAP_EVERY EXISTS_TAC [(← q r"l:(A#num)ring"), (← q r"g:A->A#num"), (← q r"e:num->A->A#num")] THEN ASM_SIMP_TAC [] THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"(e:num->A->A#num) i"), (← q r"g:A->A#num"), (← q r"k:A ring"), (← q r"l:(A#num)ring"), (← q r"{ring_0 k:A}")] RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED) THEN ASM_SIMP_TAC [IN_SING, (← ISPECL [(← q r"k:A ring"), (← q r"l:(A#num)ring")] RING_HOMOMORPHISM_0)])

  let NUMBER_FIELD_POWER_BASIS_POLY_DISCRIMINANT ← prove
    r"!(k:A ring) a.
        number_field k /\ a IN ring_carrier k /\
        poly_deg (subfield_generated k {ring_0 k})
          (minimal_polynomial (subfield_generated k {ring_0 k},k) I a) =
        extension_degree (subfield_generated k {ring_0 k},k) I
        ==> basis_discriminant (subfield_generated k {ring_0 k},k) I
              (extension_degree (subfield_generated k {ring_0 k},k) I)
              (\i. ring_pow k a i) =
            poly_discriminant (subfield_generated k {ring_0 k})
              (minimal_polynomial (subfield_generated k {ring_0 k},k) I a)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A")] NUMBER_FIELD_FREE_BASIS_POWERS) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"algebraic_over (subfield_generated k {ring_0 k},k) (I:A->A) a /\
    field_extension (subfield_generated k {ring_0 k},k) (I:A->A)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [NUMBER_FIELD_ALGEBRAIC, FIELD_EXTENSION_SUBFIELD_GENERATED], ALL_TAC] THEN ABBREV_TAC (← q r"f = minimal_polynomial (subfield_generated k {ring_0 k},k) (I:A->A) a") THEN ABBREV_TAC (← q r"m = extension_degree (subfield_generated k {ring_0 k},k:A ring) I") THEN SUBGOAL_THEN (← q r"f IN ring_carrier(poly_ring (subfield_generated k {ring_0 k}) (:1)) /\
    monic (subfield_generated k {ring_0 k}) (f:(1->num)->A)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "f" THEN ASM_SIMP_TAC [MINIMAL_POLYNOMIAL_IN_CARRIER, MINIMAL_POLYNOMIAL_MONIC], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"f:(1->num)->A"), (← q r"m:num")] NUMBER_FIELD_POWER_BASIS_HOMOMORPHISMS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"l:(A#num)ring") (X_CHOOSE_THEN (← q r"g:A->A#num") (X_CHOOSE_THEN (← q r"e:num->A->A#num") STRIP_ASSUME_TAC))) THEN FIRST_X_ASSUM (ASSUME_TAC o (SYM o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_eq z1)) then (do let z6 ← (q r"(g:A->A#num) o (f:(1->num)->A)"); let z5 ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); liftExcept (lhs z3)); pure (z5 == z6)) else pure false))))) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN SUBGOAL_THEN (← q r"ring_monomorphism(subfield_generated k {ring_0 k},l) (g:A->A#num)") ASSUME_TAC THENL [MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, FIELD_IMP_NONTRIVIAL_RING] THEN MP_TAC (← ISPECL [(← q r"g:A->A#num"), (← q r"k:A ring"), (← q r"l:(A#num)ring"), (← q r"ring_carrier(subfield_generated k {ring_0 k:A})")] RING_HOMOMORPHISM_FROM_SUBRING_GENERATED) THEN ASM_REWRITE_TAC [SUBRING_GENERATED_BY_SUBFIELD_GENERATED], FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM))] THEN UNDISCH_TAC (← q r"ring_monomorphism(k,l) (g:A->A#num)") THEN REWRITE_TAC [ring_monomorphism] THEN DISCH_THEN (MATCH_MP_TAC o CONJUNCT2) THEN REPEAT CONJ_TAC THENL [REWRITE_TAC [basis_discriminant] THEN MESON_TAC [RING_DET, RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBSET], MESON_TAC [POLY_DISCRIMINANT_IN_CARRIER, RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:(A#num)ring"), (← q r"m:num"), (← q r"\i. ring_pow k (a:A) i"), (← q r"e:num->A->A#num"), (← q r"g:A->A#num")] NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS) THEN ANTS_TAC THENL [ASM_SIMP_TAC [] THEN ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN MP_TAC (← ISPECL [(← q r"g:A->A#num"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"l:(A#num)ring"), (← q r"f:(1->num)->A")] POLY_DISCRIMINANT_HOMOMORPHISM) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_0 k:A}"), (← q r"l:(A#num)ring"), (← q r"g:A->A#num"), (← q r"f:(1->num)->A")] POLY_DEG_MONOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [RING_POLYNOMIAL], DISCH_THEN SUBST1_TAC] THEN SUBGOAL_THEN (← q r"poly_deg l ((g:A->A#num) o (f:(1->num)->A)) = m") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_0 k:A}"), (← q r"l:(A#num)ring"), (← q r"g:A->A#num"), (← q r"f:(1->num)->A")] POLY_DEG_MONOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [RING_POLYNOMIAL], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"l:(A#num)ring"), (← q r"(g:A->A#num) o (f:(1->num)->A)"), (← q r"ring_1 l:A#num"), (← q r"\i. (e:num->A->A#num) i a")] POLY_DISCRIMINANT_VANDERMONDE) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_1] THEN CONJ_TAC THENL [REWRITE_TAC [(← GSYM RING_POLYNOMIAL)] THEN MATCH_MP_TAC RING_POLYNOMIAL_COMPOSE THEN EXISTS_TAC (← q r"subfield_generated k {ring_0 k:A}") THEN ASM_REWRITE_TAC [RING_POLYNOMIAL], ALL_TAC] THEN REWRITE_TAC [POLY_CONST_1] THEN REWRITE_TAC [(← GSYM (← ISPECL [(← q r"l:(A#num)ring"), (← q r"(:1)")] (← CONJUNCT1 (← CONJUNCT2 (← CONJUNCT2 POLY_RING)))))] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_MUL_LID THEN REWRITE_TAC [(← GSYM RING_POLYNOMIAL)] THEN MATCH_MP_TAC RING_POLYNOMIAL_COMPOSE THEN EXISTS_TAC (← q r"subfield_generated k {ring_0 k:A}") THEN ASM_REWRITE_TAC [RING_POLYNOMIAL], DISCH_THEN SUBST1_TAC] THEN ASM_REWRITE_TAC [RING_POW_ONE] THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN SUBGOAL_THEN (← q r"ring_det l {i | i < m} (\i j. (e:num->A->A#num) i (ring_pow k a j)) =
    ring_det l {i | i < m} (\i j. ring_pow l (e i a) j)") SUBST1_TAC THENL [MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:(A#num)ring"), (← q r"(e:num->A->A#num) i")] RING_HOMOMORPHISM_POW) THEN ASM_SIMP_TAC [], ALL_TAC] THEN MATCH_MP_TAC RING_MUL_LID THEN REWRITE_TAC [RING_DET])

  let NUMBER_FIELD_GENERATOR_MINIMAL_POLYNOMIAL_DEGREE ← prove
    r"!(k:A ring) a.
        number_field k /\ a IN ring_carrier k /\ subfield_generated k {a} = k
        ==> poly_deg (subfield_generated k {ring_0 k})
              (minimal_polynomial (subfield_generated k {ring_0 k},k) I a) =
            extension_degree (subfield_generated k {ring_0 k},k) I"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN (← q r"algebraic_over (subfield_generated k {ring_0 k},k) (I:A->A) a /\
    field_extension (subfield_generated k {ring_0 k},k) (I:A->A)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [NUMBER_FIELD_ALGEBRAIC, FIELD_EXTENSION_SUBFIELD_GENERATED], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"a:A")] EXTENSION_DEGREE_SIMPLE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"a:A")] SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o CONJUNCT1) THEN SUBGOAL_THEN (← q r"subfield_generated k
      (a INSERT IMAGE I (ring_carrier(subfield_generated k {ring_0 k}))) =
    subfield_generated k {a:A}") (fun th => ASM_REWRITE_TAC [th]) THEN REWRITE_TAC [IMAGE_I, SUBFIELD_GENERATED_INSERT] THEN MATCH_MP_TAC SUBFIELDS_GENERATED_EQ THEN REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP IN_SUBFIELD_0)) THEN SET_TAC [])

  let NUMBER_FIELD_POLY_DISCRIMINANT_INDEX ← prove
    r"!(k:A ring) a.
        number_field k /\ a IN ring_carrier(ring_of_integers k) /\
        poly_deg (subfield_generated k {ring_0 k})
          (minimal_polynomial (subfield_generated k {ring_0 k},k) I a) =
        extension_degree (subfield_generated k {ring_0 k},k) I
        ==> ?N. {ring_coset (ring_of_integers k)
                   (ring_carrier(subring_generated k {a})) x |
                 x | x IN ring_carrier(ring_of_integers k)} HAS_SIZE N /\
                poly_discriminant (subfield_generated k {ring_0 k})
                  (minimal_polynomial (subfield_generated k {ring_0 k},k) I
                     a) =
                ring_of_int k (&N pow 2 * number_field_discriminant k)"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A")] RING_OF_INTEGERS_INTEGER_MINIMAL_POLYNOMIAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"q:(1->num)->int") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"q:(1->num)->int")] SUBRING_GENERATED_INT_LINCOMB) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"extension_degree
                    (subfield_generated k {ring_0 k},k:A ring) I"), (← q r"\i. ring_pow k (a:A) i"), (← q r"ring_carrier(subring_generated k {a:A})")] NUMBER_FIELD_DISCRIMINANT_INDEX) THEN ANTS_TAC THENL [ASM_SIMP_TAC [NUMBER_FIELD_FREE_BASIS_POWERS] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"a:A"), (← q r"i:num")] RING_POW) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"N:num") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"N:num") THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_eq z1)) then (do let z3 ← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); liftExcept (rhs z4)); pure (is_comb z3)) else pure false) then (do let z10 ← (q r"ring_of_int:(A ring)->int->A"); let z9 ← (do pure (Prod.fst (← (do let z6 ← (do let z7 ← (do let z8 ← (pure th); pure (concl z8)); liftExcept (rhs z7)); pure (strip_comb z6))))); pure (z9 == z10)) else pure false))))) THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC NUMBER_FIELD_POWER_BASIS_POLY_DISCRIMINANT THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_POLY_DISCRIMINANT_INDEX_INTEGER ← prove
    r"!(k:A ring) a m.
        number_field k /\ a IN ring_carrier k /\
        subfield_generated k {a} = k /\
        m IN ring_carrier(poly_ring integer_ring (:1)) /\
        monic integer_ring m /\
        poly_deg integer_ring m =
        extension_degree (subfield_generated k {ring_0 k},k) I /\
        poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m = ring_0 k
        ==> ?N. {ring_coset (ring_of_integers k)
                   (ring_carrier(subring_generated k {a})) x |
                 x | x IN ring_carrier(ring_of_integers k)} HAS_SIZE N /\
                poly_discriminant integer_ring m =
                &N pow 2 * number_field_discriminant k"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM, integral_element] THEN ASM_MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A")] NUMBER_FIELD_GENERATOR_MINIMAL_POLYNOMIAL_DEGREE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A")] NUMBER_FIELD_POLY_DISCRIMINANT_INDEX) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"N:num") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"algebraic_over (subfield_generated k {ring_0 k},k) (I:A->A) a /\
    field_extension (subfield_generated k {ring_0 k},k) (I:A->A)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [NUMBER_FIELD_ALGEBRAIC, FIELD_EXTENSION_SUBFIELD_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_monomorphism(integer_ring,subfield_generated k {ring_0 k})
                     (ring_of_int k:int->A)") ASSUME_TAC THENL [REWRITE_TAC [ring_monomorphism, INTEGER_RING, IN_UNIV] THEN ASM_SIMP_TAC [RING_OF_INT_EQ_CHAR_0] THEN MP_TAC (← ISPEC (← q r"subfield_generated k {ring_0 k:A}") RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN REWRITE_TAC [RING_OF_INT_SUBFIELD_GENERATED], FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM))] THEN SUBGOAL_THEN (← q r"(ring_of_int k:int->A) o m IN
    ring_carrier(poly_ring (subfield_generated k {ring_0 k}) (:1))") ASSUME_TAC THENL [REWRITE_TAC [(← GSYM RING_POLYNOMIAL)] THEN MATCH_MP_TAC RING_POLYNOMIAL_COMPOSE THEN EXISTS_TAC (← q r"integer_ring") THEN ASM_REWRITE_TAC [RING_POLYNOMIAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"poly_extend (subfield_generated k {ring_0 k},k) I (\v:1. a)
      ((ring_of_int k:int->A) o (m:(1->num)->int)) = ring_0 k") ASSUME_TAC THENL [FIRST_ASSUM ((fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [(← SYM th)])) o (checkM (fun th => (do if ← (do if ← (do if ← (do let z21 ← (do let z22 ← (pure th); pure (concl z22)); pure (is_eq z21)) then (do let z26 ← (q r"ring_0 k:A"); let z25 ← (do let z23 ← (do let z24 ← (pure th); pure (concl z24)); liftExcept (rand z23)); pure (z25 == z26)) else pure false) then (do let z27 ← (do let z28 ← (do let z29 ← (pure th); pure (concl z29)); liftExcept (lhs z28)); pure (is_comb z27)) else pure false) then (do let z34 ← (q r"m:(1->num)->int"); let z33 ← (do let z30 ← (do let z31 ← (do let z32 ← (pure th); pure (concl z32)); liftExcept (lhs z31)); liftExcept (rand z30)); pure (z33 == z34)) else pure false)))) THEN SIMP_TAC [POLY_EXTEND_EVALUATE, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN REWRITE_TAC [I_O_ID], ALL_TAC] THEN SUBGOAL_THEN (← q r"minimal_polynomial (subfield_generated k {ring_0 k},k) I a =
    (ring_of_int k:int->A) o m") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"ring_of_int k:int->A"), (← q r"m:(1->num)->int")] MONIC_HOMOMORPHIC_IMAGE) THEN ASM_SIMP_TAC [FIELD_IMP_NONTRIVIAL_RING, FIELD_SUBFIELD_GENERATED] THEN STRIP_TAC THEN MATCH_MP_TAC MONIC_DIVIDES_EQ THEN EXISTS_TAC (← q r"subfield_generated k {ring_0 k:A}") THEN ASM_SIMP_TAC [MINIMAL_POLYNOMIAL_MONIC, MINIMAL_POLYNOMIAL_DIVIDES] THEN ASM_REWRITE_TAC [LE_REFL], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_int k:int->A"), (← q r"integer_ring"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"m:(1->num)->int")] POLY_DISCRIMINANT_HOMOMORPHISM) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"ring_of_int k:int->A"), (← q r"m:(1->num)->int")] POLY_DEG_MONOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [RING_POLYNOMIAL], ALL_TAC] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do if ← (do let z11 ← (do let z12 ← (pure th); pure (concl z12)); pure (is_eq z11)) then (do let z13 ← (do let z14 ← (do let z15 ← (pure th); pure (concl z15)); liftExcept (lhs z14)); pure (is_comb z13)) else pure false) then (do let z20 ← (q r"minimal_polynomial       (subfield_generated k {ring_0 k},k) (I:A->A)"); let z19 ← (do let z16 ← (do let z17 ← (do let z18 ← (pure th); pure (concl z18)); liftExcept (lhs z17)); liftExcept (rator z16)); pure (z19 == z20)) else pure false))))) THEN FIRST_X_ASSUM (SUBST1_TAC o (checkM (fun th => (do if ← (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_eq z1)) then (do let z3 ← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); liftExcept (lhs z4)); pure (is_comb z3)) else pure false) then (do let z10 ← (q r"poly_discriminant:(A ring)->((1->num)->A)->A"); let z9 ← (do pure (Prod.fst (← (do let z6 ← (do let z7 ← (do let z8 ← (pure th); pure (concl z8)); liftExcept (lhs z7)); pure (strip_comb z6))))); pure (z9 == z10)) else pure false)))) THEN ASM_SIMP_TAC [RING_OF_INT_EQ_CHAR_0])

  let NUMBER_FIELD_POLY_DISCRIMINANT_SQUAREFREE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!(f:A->A->bool) s u v c.
        {f y | y | y IN s} = {c} /\ u IN s /\ v IN s ==> f u = f v")
    prove
      r"!(k:A ring) a m.
          number_field k /\ a IN ring_carrier k /\
          subfield_generated k {a} = k /\
          m IN ring_carrier(poly_ring integer_ring (:1)) /\
          monic integer_ring m /\
          poly_deg integer_ring m =
          extension_degree (subfield_generated k {ring_0 k},k) I /\
          poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m = ring_0 k /\
          squarefree(num_of_int(abs(poly_discriminant integer_ring m)))
          ==> ring_carrier(subring_generated k {a}) =
              ring_carrier(ring_of_integers k) /\
              number_field_discriminant k = poly_discriminant integer_ring m"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"m:(1->num)->int")] NUMBER_FIELD_POLY_DISCRIMINANT_INDEX_INTEGER) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"N:num") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"N = 1") SUBST_ALL_TAC THENL [FIRST_X_ASSUM (MATCH_MP_TAC o ((GEN_REWRITE_RULE id [squarefree]) o (checkM (fun th => (do let z5 ← (q r"squarefree"); let z4 ← (do pure (Prod.fst (← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); pure (strip_comb z2))))); pure (z4 == z5)))))) THEN ASM_REWRITE_TAC [INT_ABS_MUL, INT_ABS_POW, INT_ABS_NUM] THEN SIMP_TAC [NUM_OF_INT_MUL, INT_POS, INT_ABS_POS, INT_OF_NUM_POW, NUM_OF_INT_OF_NUM] THEN CONV_TAC NUMBER_RULE, ALL_TAC] THEN ASM_REWRITE_TAC [INT_POW_ONE, INT_MUL_LID] THEN SUBGOAL_THEN (← q r"ring_carrier(subring_generated k {a:A}) SUBSET
      ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN REWRITE_TAC [RING_OF_INTEGERS_SUBRING, SING_SUBSET] THEN REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM, integral_element] THEN ASM_MESON_TAC [], ALL_TAC] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN UNDISCH_TAC (← q r"{ring_coset (ring_of_integers k)
                  (ring_carrier(subring_generated k {a:A}))
                  x | x | x IN ring_carrier(ring_of_integers k)} HAS_SIZE 1") THEN REWRITE_TAC [ONE, HAS_SIZE_CLAUSES, HAS_SIZE_0, UNWIND_THM2, NOT_IN_EMPTY] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"c:A->bool")) THEN SUBGOAL_THEN (← q r"ring_0 k IN ring_carrier(ring_of_integers k:A ring)") ASSUME_TAC THENL [MESON_TAC [RING_0, RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_coset (ring_of_integers k)
        (ring_carrier(subring_generated k {a:A})) x =
      ring_coset (ring_of_integers k)
        (ring_carrier(subring_generated k {a})) (ring_0 k)") MP_TAC THENL [MATCH_MP_TAC r1 THEN MAP_EVERY EXISTS_TAC [(← q r"ring_carrier(ring_of_integers k:A ring)"), (← q r"c:A->bool")] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_carrier(subring_generated k {a:A}) subring_of ring_of_integers k") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{a:A}")] SUBRING_SUBRING_GENERATED) THEN REWRITE_TAC [subring_of, RING_OF_INTEGERS] THEN ASM_SIMP_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [RING_COSET_EQ] THEN REWRITE_TAC [RING_OF_INTEGERS] THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [RING_SUB_RZERO])

  let NUMBER_FIELD_POLY_DISCRIMINANT_INDEX_COPRIME ← prove
    r"!(k:A ring) a m p.
        number_field k /\ a IN ring_carrier k /\
        subfield_generated k {a} = k /\
        m IN ring_carrier(poly_ring integer_ring (:1)) /\
        monic integer_ring m /\
        poly_deg integer_ring m =
        extension_degree (subfield_generated k {ring_0 k},k) I /\
        poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m = ring_0 k /\
        prime p /\ ~(&p pow 2 divides poly_discriminant integer_ring m)
        ==> ring_setadd (ring_of_integers k)
              (ring_carrier(subring_generated k {a}))
              (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
            ring_carrier(ring_of_integers k)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"m:(1->num)->int")] NUMBER_FIELD_POLY_DISCRIMINANT_INDEX_INTEGER) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"N:num") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"p:num"), (← q r"N:num")] SUBRING_GENERATED_INDEX_COPRIME) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM, integral_element] THEN ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"~(&p pow 2 divides poly_discriminant integer_ring m)") THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"(p:num) divides N") THEN REWRITE_TAC [num_divides] THEN CONV_TAC INTEGER_RULE)

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_POWER_BASIS_HOMOMORPHISMS,
           NUMBER_FIELD_POWER_BASIS_POLY_DISCRIMINANT,
           NUMBER_FIELD_GENERATOR_MINIMAL_POLYNOMIAL_DEGREE,
           NUMBER_FIELD_POLY_DISCRIMINANT_INDEX,
           NUMBER_FIELD_POLY_DISCRIMINANT_INDEX_INTEGER,
           NUMBER_FIELD_POLY_DISCRIMINANT_SQUAREFREE,
           NUMBER_FIELD_POLY_DISCRIMINANT_INDEX_COPRIME }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- power_basis_index.ml phrases from line 765 to 1397                     -/
/- ---------------------------------------------------------------------- -/

structure PowerBasisIndex02 where
  -- @@FIELDS
  NUMBER_FIELD_POWER_BASIS_DUAL : thm
  NUMBER_FIELD_TRACE_DUAL_LATTICE : thm
  SUBRING_GENERATED_HORNER_SPAN : thm
  NUMBER_FIELD_MINIMAL_POLYNOMIAL_DERIV_SUBRING : thm
  NUMBER_FIELD_SUBRING_GENERATED_EQ_RING_OF_INTEGERS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupPowerBasisIndex02 [HolBase] (D : PowerBasisIndexDeps) (BPowerBasisIndex01 : PowerBasisIndex01) :
    ExceptT String IO PowerBasisIndex02 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON,
        MESON_TAC, RING_RULE, TAUT, .. } := D
  let { ALGEBRA_TRACE_NORM_IN_CARRIER, COEFF_ABOVE_DEG, COEFF_COMPOSE,
        COEFF_IN_CARRIER_ALT, COEFF_POLY_DERIV, COEFF_POLY_MUL_X_MINUS, EQ_TRANS,
        EXTENSION, FIELD_EXTENSION_SUBFIELD_GENERATED, FIELD_HOMOMORPHISM_INV,
        FIELD_IMP_INTEGRAL_DOMAIN, FIELD_IMP_NONTRIVIAL_RING, FIELD_MUL_LINV,
        FINITE_DELETE, FINITE_NUMSEG_LT, FREE_BASIS_IN_CARRIER, FUN_EQ_THM,
        INTEGRAL_DOMAIN_MUL_LCANCEL, INTEGRAL_DOMAIN_POLY_RING,
        INTEGRAL_DOMAIN_PRODUCT_EQ_0, IN_DELETE, IN_ELIM_THM, IN_SING, IN_SUBFIELD_INV,
        IN_SUBFIELD_MUL, IN_SUBRING_1, IN_SUBRING_ADD, IN_SUBRING_INT, IN_SUBRING_MUL,
        IN_SUBRING_NUM, IN_SUBRING_POW, IN_SUBRING_SUM, IN_UNIV, I_THM, LE_REFL,
        MINIMAL_POLYNOMIAL_IN_CARRIER, MONIC_IMP_NONZERO, MONIC_POLY_0,
        MONIC_X_MINUS_A, NOT_EXISTS_THM, NUMBER_FIELD_ALGEBRAIC,
        NUMBER_FIELD_DEGREE_POS, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_INTEGRAL_MULTIPLE, NUMBER_FIELD_TRACE_FORM_INJECTIVE,
        NUMBER_FIELD_TRACE_IN_RING_OF_INTEGERS, NUMBER_FIELD_TRACE_MUL_LINCOMB,
        POLY_COMPOSE_HOMOMORPHISM_CONST, POLY_COMPOSE_HOMOMORPHISM_MUL,
        POLY_COMPOSE_HOMOMORPHISM_SUB, POLY_COMPOSE_HOMOMORPHISM_VAR,
        POLY_DEG_MUL_X_MINUS_A, POLY_DERIV_IN_CARRIER, POLY_EXTEND,
        POLY_EXTEND_UNIVARIATE, POLY_MUL_0, .. } := D.core1
  let { POLY_RING_CLAUSES, RIGHT_IMP_EXISTS_THM, RING_0, RING_1,
        RING_CARRIER_SUBFIELD_GENERATED_SUBSET, RING_HOMOMORPHISM_0,
        RING_HOMOMORPHISM_1, RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_POW,
        RING_HOMOMORPHISM_SUBFIELD_INCLUSION, RING_INT_LINCOMB,
        RING_INT_LINCOMB_LINCOMB, RING_INV, RING_MONOMORPHISM_IMP_HOMOMORPHISM,
        RING_MUL, RING_MUL_ASSOC, RING_MUL_INT_LINCOMB, RING_MUL_LID, RING_MUL_LZERO,
        RING_MUL_RID, RING_MUL_RZERO, RING_MUL_SYM, RING_OF_INT,
        RING_OF_INTEGERS_MINIMAL_POLYNOMIAL_Q, RING_OF_INTEGERS_SUBSET, RING_OF_INT_0,
        RING_OF_INT_1, RING_OF_INT_EQ_0_CHAR_0, RING_OF_INT_IN_RING_OF_INTEGERS,
        RING_OF_INT_IN_SUBFIELD_GENERATED, RING_OF_INT_ISUM, RING_OF_INT_MUL,
        RING_OF_INT_NEG, RING_OF_NUM_SUBFIELD_GENERATED, RING_POLYNOMIAL,
        RING_POLYNOMIAL_COMPOSE, RING_POLYNOMIAL_CONST,
        RING_POLYNOMIAL_IMP_POWERSERIES, RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_VAR,
        RING_POW, RING_POWERSERIES_CONST, RING_POWERSERIES_VAR, RING_PRODUCT,
        RING_PRODUCT_DELETE, RING_SUB_EQ_0, RING_SUB_RZERO, RING_SUM, RING_SUM_DELTA,
        RING_SUM_EQ, RING_SUM_LAGRANGE_COEFF, SING_SUBSET, SKOLEM_THM,
        SUBFIELD_GENERATED, SUBFIELD_GENERATED_EQ, SUBFIELD_SUBFIELD_GENERATED,
        SUBRING_GENERATED_INC, SUBRING_SUBRING_GENERATED,
        SUBRING_SUBSET_SUBFIELD_GENERATED, SUBSET, SUBSET_ANTISYM_EQ, SUB_0, monic,
        number_field, o_THM, ring_div, ring_monomorphism, ring_polynomial, ring_pow,
        ring_powerseries, .. } := D.core2
  let { NUMBER_FIELD_POWER_BASIS_HOMOMORPHISMS, .. } := BPowerBasisIndex01
  -- @@SCOPE END

  let NUMBER_FIELD_POWER_BASIS_DUAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul r u (ring_mul r v w) = ring_mul r (ring_mul r v u) (w:B)")
    let r48 ← TAUT (← q r"q /\ (q ==> p) ==> p /\ q")
    prove
      r"!(k:A ring) a f m d b.
          number_field k /\ a IN ring_carrier k /\
          f = minimal_polynomial (subfield_generated k {ring_0 k},k) I a /\
          m = extension_degree (subfield_generated k {ring_0 k},k) I /\
          poly_deg (subfield_generated k {ring_0 k}) f = m /\
          d = poly_extend (subfield_generated k {ring_0 k},k) I (\v. a)
                (poly_deriv (subfield_generated k {ring_0 k}) f) /\
          b IN ring_carrier(poly_ring k (:1)) /\
          f = poly_mul k (poly_sub k (poly_var k one) (poly_const k a)) b
          ==> ~(d = ring_0 k) /\
              !i j. i < m /\ j < m
                    ==> algebra_trace (subfield_generated k {ring_0 k},k) I
                          (ring_mul k (ring_inv k d)
                             (ring_mul k (ring_pow k a i) (coeff j b))) =
                        if j = i then ring_1 k else ring_0 k"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM (ASSUME_TAC o (SYM o (checkM (fun th => (do if ← (do if ← (do let z82 ← (do let z83 ← (pure th); pure (concl z83)); pure (is_eq z82)) then (do let z87 ← (q r"f:(1->num)->A"); let z86 ← (do let z84 ← (do let z85 ← (pure th); pure (concl z85)); liftExcept (lhs z84)); pure (z86 == z87)) else pure false) then (do let z88 ← (do let z89 ← (do let z90 ← (pure th); pure (concl z90)); liftExcept (rhs z89)); canM (fun z91 => (do let z94 ← (pure z91); let z93 ← (q r"poly_mul k p q:(1->num)->A"); let z92 ← (pure []); term_match z92 z93 z94)) z88) else pure false))))) THEN FIRST_X_ASSUM (ASSUME_TAC o (SYM o (checkM (fun th => (do let z81 ← (q r"d:A"); let z80 ← (do let z78 ← (do let z79 ← (pure th); pure (concl z79)); liftExcept (lhs z78)); pure (z80 == z81)))))) THEN FIRST_X_ASSUM (ASSUME_TAC o (SYM o (checkM (fun th => (do let z77 ← (q r"m:num"); let z76 ← (do let z74 ← (do let z75 ← (pure th); pure (concl z75)); liftExcept (lhs z74)); pure (z76 == z77)))))) THEN FIRST_X_ASSUM (ASSUME_TAC o (SYM o (checkM (fun th => (do let z73 ← (q r"f:(1->num)->A"); let z72 ← (do let z70 ← (do let z71 ← (pure th); pure (concl z71)); liftExcept (lhs z70)); pure (z72 == z73)))))) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN (← q r"ring_polynomial k (b:(1->num)->A)") ASSUME_TAC THENL [ASM_REWRITE_TAC [RING_POLYNOMIAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_polynomial (subfield_generated k {ring_0 k}) (f:(1->num)->A)") ASSUME_TAC THENL [EXPAND_TAC "f" THEN ASM_SIMP_TAC [RING_POLYNOMIAL, MINIMAL_POLYNOMIAL_IN_CARRIER, NUMBER_FIELD_ALGEBRAIC, FIELD_EXTENSION_SUBFIELD_GENERATED], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"f:(1->num)->A"), (← q r"m:num")] NUMBER_FIELD_POWER_BASIS_HOMOMORPHISMS) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"l:(A#num)ring") (X_CHOOSE_THEN (← q r"g:A->A#num") (X_CHOOSE_THEN (← q r"e:num->A->A#num") STRIP_ASSUME_TAC))) THEN FIRST_X_ASSUM (ASSUME_TAC o (SYM o (checkM (fun th => (do if ← (do let z64 ← (do let z65 ← (pure th); pure (concl z65)); pure (is_eq z64)) then (do let z69 ← (q r"(g:A->A#num) o (f:(1->num)->A)"); let z68 ← (do let z66 ← (do let z67 ← (pure th); pure (concl z67)); liftExcept (lhs z66)); pure (z68 == z69)) else pure false))))) THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do if ← (do let z55 ← (do let z56 ← (pure th); pure (concl z56)); pure (is_forall z55)) then (do let z57 ← (do let z58 ← (pure th); pure (concl z58)); canM (fun z59 => (do let z60 ← (pure z59); find_termM (fun z61 => (do let z63 ← (pure z61); let z62 ← (q r"poly_deriv:(A ring)->((1->num)->A)->((1->num)->A)"); pure (z62 == z63))) z60)) z57) else pure false)))) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN) o (checkM (fun th => (do let z54 ← (q r"field(l:(A#num)ring)"); let z53 ← (do let z52 ← (pure th); pure (concl z52)); pure (z53 == z54)))))) THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP FIELD_IMP_NONTRIVIAL_RING) o (checkM (fun th => (do let z51 ← (q r"field(l:(A#num)ring)"); let z50 ← (do let z49 ← (pure th); pure (concl z49)); pure (z50 == z51)))))) THEN SUBGOAL_THEN (← q r"0 < m") ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"k:A ring") NUMBER_FIELD_DEGREE_POS) THEN ASM_REWRITE_TAC [] THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"(d:A) IN ring_carrier k") ASSUME_TAC THENL [EXPAND_TAC "d" THEN REWRITE_TAC [POLY_EXTEND], ALL_TAC] THEN SUBGOAL_THEN (← q r"!t. t < m
          ==> ~((e:num->A->A#num) t d = ring_0 l) /\
              e t d = ring_product l ({s | s < m} DELETE t)
                        (\s. ring_sub l (e t a) (e s a))") ASSUME_TAC THENL [X_GEN_TAC (← q r"t:num") THEN DISCH_TAC THEN MATCH_MP_TAC r48 THEN CONJ_TAC THENL [ASM_SIMP_TAC [], DISCH_THEN SUBST1_TAC] THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_PRODUCT_EQ_0, FINITE_DELETE, FINITE_NUMSEG_LT] THEN REWRITE_TAC [IN_DELETE, IN_ELIM_THM, NOT_EXISTS_THM] THEN X_GEN_TAC (← q r"s:num") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"l:(A#num)ring"), (← q r"(e:num->A->A#num) t a"), (← q r"(e:num->A->A#num) s a")] RING_SUB_EQ_0) THEN ASM_SIMP_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN CONJ_TAC THENL [DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"0")) o (checkM (fun th => (do if ← (do let z39 ← (do let z40 ← (pure th); pure (concl z40)); pure (is_forall z39)) then (do let z41 ← (do let z42 ← (pure th); pure (concl z42)); canM (fun z43 => (do let z44 ← (pure z43); find_termM (fun z45 => (do let z47 ← (pure z45); let z46 ← (q r"ring_product:((A#num)ring)->(num->bool)->(num->A#num)->A#num"); pure (z46 == z47))) z44)) z41) else pure false))))) THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:(A#num)ring"), (← q r"(e:num->A->A#num) 0")] RING_HOMOMORPHISM_0) THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!t. t < m
          ==> (e:num->A->A#num) t o (b:(1->num)->A) =
              ring_product (poly_ring l (:1)) ({s | s < m} DELETE t)
                (\s. poly_sub l (poly_var l one) (poly_const l (e s a)))") ASSUME_TAC THENL [X_GEN_TAC (← q r"t:num") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_homomorphism(k,l) ((e:num->A->A#num) t)") ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(e:num->A->A#num) t a IN ring_carrier l") ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN EXISTS_TAC (← q r"poly_ring l (:1):((1->num)->A#num)ring") THEN EXISTS_TAC (← q r"poly_sub l (poly_var l one)
                    (poly_const l ((e:num->A->A#num) t a))") THEN ASM_REWRITE_TAC [INTEGRAL_DOMAIN_POLY_RING] THEN REWRITE_TAC [RING_PRODUCT, (← GSYM RING_POLYNOMIAL)] THEN ASM_SIMP_TAC [RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_CONST] THEN REPEAT CONJ_TAC THENL [REWRITE_TAC [POLY_RING_CLAUSES] THEN MATCH_MP_TAC MONIC_IMP_NONZERO THEN ASM_SIMP_TAC [MONIC_X_MINUS_A, RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_CONST], MATCH_MP_TAC RING_POLYNOMIAL_COMPOSE THEN EXISTS_TAC (← q r"k:A ring") THEN ASM_REWRITE_TAC [RING_POLYNOMIAL], ALL_TAC] THEN REWRITE_TAC [POLY_RING_CLAUSES] THEN TRANS_TAC EQ_TRANS (← q r"(e:num->A->A#num) t o (f:(1->num)->A)") THEN CONJ_TAC THENL [FIRST_ASSUM ((fun th => tactic_of do pure (GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [(← SYM th)])) o (checkM (fun th => (do if ← (do if ← (do let z26 ← (do let z27 ← (pure th); pure (concl z27)); pure (is_eq z26)) then (do let z31 ← (q r"f:(1->num)->A"); let z30 ← (do let z28 ← (do let z29 ← (pure th); pure (concl z29)); liftExcept (rhs z28)); pure (z30 == z31)) else pure false) then (do let z32 ← (do let z33 ← (do let z34 ← (pure th); pure (concl z34)); liftExcept (lhs z33)); canM (fun z35 => (do let z38 ← (pure z35); let z37 ← (q r"poly_mul k p q:(1->num)->A"); let z36 ← (pure []); term_match z36 z37 z38)) z32) else pure false)))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:(A#num)ring"), (← q r"(e:num->A->A#num) t"), (← q r"poly_sub k (poly_var k one) (poly_const k (a:A))"), (← q r"b:(1->num)->A")] POLY_COMPOSE_HOMOMORPHISM_MUL) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN CONJ_TAC THEN MATCH_MP_TAC RING_POLYNOMIAL_IMP_POWERSERIES THEN ASM_SIMP_TAC [RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_CONST] THEN ASM_REWRITE_TAC [RING_POLYNOMIAL], DISCH_THEN SUBST1_TAC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:(A#num)ring"), (← q r"(e:num->A->A#num) t"), (← q r"poly_var k one:(1->num)->A"), (← q r"poly_const k (a:A):(1->num)->A")] POLY_COMPOSE_HOMOMORPHISM_SUB) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_POWERSERIES_VAR, RING_POWERSERIES_CONST], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [(← MATCH_MP POLY_COMPOSE_HOMOMORPHISM_VAR (← ASSUME (← q r"ring_homomorphism(k,l) ((e:num->A->A#num) t)")))] THEN REWRITE_TAC [(← MATCH_MP POLY_COMPOSE_HOMOMORPHISM_CONST (← CONJ (← ASSUME (← q r"ring_homomorphism(k,l) ((e:num->A->A#num) t)")) (← ASSUME (← q r"(a:A) IN ring_carrier k"))))], ALL_TAC] THEN TRANS_TAC EQ_TRANS (← q r"(g:A->A#num) o (f:(1->num)->A)") THEN CONJ_TAC THENL [REWRITE_TAC [FUN_EQ_THM, o_THM] THEN X_GEN_TAC (← q r"u:1->num") THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"ring_polynomial (subfield_generated k {ring_0 k}) (f:(1->num)->A)") THEN SIMP_TAC [ring_polynomial, ring_powerseries], ALL_TAC] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z20 ← (do let z21 ← (pure th); pure (concl z21)); pure (is_eq z20)) then (do let z25 ← (q r"(g:A->A#num) o (f:(1->num)->A)"); let z24 ← (do let z22 ← (do let z23 ← (pure th); pure (concl z23)); liftExcept (rhs z22)); pure (z24 == z25)) else pure false))))) THEN MP_TAC (← ISPECL [(← q r"poly_ring l (:1):((1->num)->A#num)ring"), (← q r"\s. poly_sub l (poly_var l one)
                            (poly_const l ((e:num->A->A#num) s a))"), (← q r"{s:num | s < m}"), (← q r"t:num")] RING_PRODUCT_DELETE) THEN REWRITE_TAC [] THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, (← GSYM RING_POLYNOMIAL), RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_CONST], DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [POLY_RING_CLAUSES]], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"i:num"), (← q r"j:num")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_mul k (ring_inv k d)
        (ring_mul k (ring_pow k a i) (coeff j (b:(1->num)->A))) IN
      ring_carrier k") ASSUME_TAC THENL [MATCH_MP_TAC RING_MUL THEN ASM_SIMP_TAC [RING_INV, RING_MUL, RING_POW, COEFF_IN_CARRIER_ALT], ALL_TAC] THEN UNDISCH_TAC (← q r"ring_monomorphism(k,l) (g:A->A#num)") THEN REWRITE_TAC [ring_monomorphism] THEN DISCH_THEN (MATCH_MP_TAC o CONJUNCT2) THEN REPEAT CONJ_TAC THENL [MESON_TAC [ALGEBRA_TRACE_NORM_IN_CARRIER, RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBSET], COND_CASES_TAC THEN REWRITE_TAC [RING_0, RING_1], ALL_TAC] THEN FIRST_ASSUM ((fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP th (← ASSUME (← q r"ring_mul k (ring_inv k d) (ring_mul k (ring_pow k a i)
                (coeff j (b:(1->num)->A))) IN ring_carrier (k:A ring)")))])) o (checkM (fun th => (do if ← (do let z11 ← (do let z12 ← (pure th); pure (concl z12)); pure (is_forall z11)) then (do let z13 ← (do let z14 ← (pure th); pure (concl z14)); canM (fun z15 => (do let z16 ← (pure z15); find_termM (fun z17 => (do let z19 ← (pure z17); let z18 ← (q r"algebra_trace:(A ring#A ring)->(A->A)->A->A"); pure (z18 == z19))) z16)) z13) else pure false)))) THEN MP_TAC (← ISPECL [(← q r"l:(A#num)ring"), (← q r"\t. (e:num->A->A#num) t a"), (← q r"m:num"), (← q r"i:num"), (← q r"j:num")] RING_SUM_LAGRANGE_COEFF) THEN ANTS_TAC THENL [ASM_SIMP_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(g:A->A#num) (if j:num = i then ring_1 k else ring_0 k) =
      if j = i then ring_1 (l:(A#num)ring) else ring_0 l") SUBST1_TAC THENL [COND_CASES_TAC THEN ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_0 (← ASSUME (← q r"ring_homomorphism(k,l) (g:A->A#num)"))), (← MATCH_MP RING_HOMOMORPHISM_1 (← ASSUME (← q r"ring_homomorphism(k,l) (g:A->A#num)")))], ALL_TAC] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"t:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ring_homomorphism(k,l) ((e:num->A->A#num) t)") ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"coeff j (b:(1->num)->A) IN ring_carrier k") ASSUME_TAC THENL [ASM_SIMP_TAC [COEFF_IN_CARRIER_ALT], ALL_TAC] THEN SUBGOAL_THEN (← q r"(e:num->A->A#num) t (coeff j b) =
      coeff j (ring_product (poly_ring l (:1)) ({s | s < m} DELETE t)
                 (\s. poly_sub l (poly_var l one) (poly_const l (e s a))))") ASSUME_TAC THENL [FIRST_ASSUM ((fun th => tactic_of do pure (REWRITE_TAC [(← GSYM (← MATCH_MP th (← ASSUME (← q r"t:num < m"))))])) o (checkM (fun th => (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); pure (is_forall z2)) then (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); canM (fun z6 => (do let z7 ← (pure z6); find_termM (fun z8 => (do let z10 ← (pure z8); let z9 ← (q r"b:(1->num)->A"); pure (z9 == z10))) z7)) z4) else pure false)))) THEN REWRITE_TAC [COEFF_COMPOSE], ALL_TAC] THEN ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL (← ASSUME (← q r"ring_homomorphism(k,l) ((e:num->A->A#num) t)"))), (← MATCH_MP RING_HOMOMORPHISM_POW (← ASSUME (← q r"ring_homomorphism(k,l) ((e:num->A->A#num) t)"))), (← MATCH_MP (← MATCH_MP FIELD_HOMOMORPHISM_INV (← CONJ (← ASSUME (← q r"field(k:A ring)")) (← ASSUME (← q r"ring_homomorphism(k,l) ((e:num->A->A#num) t)")))) (← ASSUME (← q r"(d:A) IN ring_carrier k"))), RING_INV, RING_POW, RING_MUL] THEN REWRITE_TAC [ring_div] THEN MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [RING_INV, RING_POW, RING_PRODUCT, COEFF_IN_CARRIER_ALT, RING_POLYNOMIAL])

  let NUMBER_FIELD_TRACE_DUAL_LATTICE ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"i:num"
    let q2 ← q r"c:num->int"
    let q3 ← q r"i:num"
    let q4 ← q r"isum {i | i < n} (\i. (e:num->int) i * c i)"
    let q5 ← q r"!y m. y = ring_of_int k m
            ==> y IN ring_carrier(ring_of_integers (k:A ring))"
    let r6 ← MESON [RING_OF_INT_IN_RING_OF_INTEGERS] q5
    let q7 ← q r"e:num->int"
    let q8 ← q r"c:num->int"
    let q9 ← q r"ring_mul k ((w:num->A) i)
        (ring_sum k {j | j < n}
           (\j. ring_mul k (ring_of_int k (c j)) ((w':num->A) j))) =
      ring_mul k
        (ring_sum k {j | j < n}
           (\j. ring_mul k (ring_of_int k (c j)) (w' j))) (w i)"
    let q10 ← q r"ring_mul k ((w:num->A) i) x = ring_mul k x (w i)"
    let q11 ← q r"i:num"
    let q12 ← q r"w:num->A"
    let q13 ← q r"n:num"
    let q14 ← q r"k:A ring"
    let q15 ← q r"c:num->int"
    let q16 ← q r"c:num->int"
    let q17 ← q r"j:num"
    let q18 ← q r"ring_sum k {j | j < n} (\j. if j = i then (w:num->A) i
                                    else ring_0 k)"
    let q19 ← q r"(a:A) = b ==> a IN s ==> b IN s"
    let r20 ← MESON [] q19
    let q21 ← q r"\j:num. if j = i then &1:int else &0"
    let q22 ← q r"ring_mul k x ((w:num->A) i)"
    let q23 ← q r"k:A ring"
    let v24 ← ISPECL [q23, q22] NUMBER_FIELD_TRACE_IN_RING_OF_INTEGERS
    let q25 ← q r"i:num"
    let q26 ← q r"!i. i < n
          ==> ?m. algebra_trace (subfield_generated k {ring_0 k},k) I
                    (ring_mul k x ((w:num->A) i)) = ring_of_int k m"
    let q27 ← q r"x:A"
    let q28 ← q r"j:num"
    let q29 ← q r"ring_sum k {j | j < n}
        (\j. if j = i then ring_of_int k ((c:num->int) i)
             else ring_0 (k:A ring))"
    let q30 ← q r"ring_mul k
        (ring_sum k {j | j < n}
           (\j. ring_mul k (ring_of_int k (c j)) ((w':num->A) j)))
        ((w:num->A) i) =
      ring_mul k (w i)
        (ring_sum k {j | j < n}
           (\j. ring_mul k (ring_of_int k (c j)) (w' j)))"
    let q31 ← q r"!c i. i < n
          ==> algebra_trace (subfield_generated k {ring_0 k},k) I
                (ring_mul k
                   (ring_sum k {j | j < n}
                      (\j. ring_mul k (ring_of_int k (c j)) ((w':num->A) j)))
                   ((w:num->A) i)) =
              ring_of_int k (c i)"
    let q32 ← q r"!x (c:num->int).
        x IN ring_carrier k
        ==> algebra_trace (subfield_generated k {ring_0 k},k) I
              (ring_mul k x
                 (ring_sum k {i | i < n}
                    (\i. ring_mul k (ring_of_int k (c i)) ((w:num->A) i)))) =
            ring_sum k {i | i < n}
              (\i. ring_mul k (ring_of_int k (c i))
                     (algebra_trace (subfield_generated k {ring_0 k},k) I
                        (ring_mul k x (w i))))"
    prove
      r"!k:A ring n w w'.
          number_field k /\
          free_basis (subfield_generated k {ring_0 k},k) I n w /\
          (!j. j < n ==> w' j IN ring_carrier k) /\
          (!i j. i < n /\ j < n
                 ==> algebra_trace (subfield_generated k {ring_0 k},k) I
                       (ring_mul k (w i) (w' j)) =
                     if i = j then ring_1 k else ring_0 k)
          ==> {x | x IN ring_carrier k /\
                   !c. algebra_trace (subfield_generated k {ring_0 k},k) I
                         (ring_mul k x
                            (ring_sum k {i | i < n}
                               (\i. ring_mul k (ring_of_int k (c i)) (w i)))) IN
                       ring_carrier(ring_of_integers k)} =
              {ring_sum k {i | i < n}
                 (\i. ring_mul k (ring_of_int k (c i)) (w' i)) |
               c IN (:num->int)}"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FREE_BASIS_IN_CARRIER)) THEN SUBGOAL_THEN q32 (LABEL_TAC "lin") THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC NUMBER_FIELD_TRACE_MUL_LINCOMB THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, RING_OF_INT_IN_SUBFIELD_GENERATED], ALL_TAC] THEN SUBGOAL_THEN q31 (LABEL_TAC "dual") THENL [REPEAT STRIP_TAC THEN SUBGOAL_THEN q30 SUBST1_TAC THENL [MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC [RING_SUM], ALL_TAC] THEN ASM_SIMP_TAC [NUMBER_FIELD_TRACE_MUL_LINCOMB, FINITE_NUMSEG_LT, IN_ELIM_THM, RING_OF_INT_IN_SUBFIELD_GENERATED] THEN TRANS_TAC EQ_TRANS q29 THEN CONJ_TAC THENL [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC q28 THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN ASM_SIMP_TAC [] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [RING_MUL_RID, RING_MUL_RZERO, RING_OF_INT] THEN ASM_MESON_TAC [], ASM_REWRITE_TAC [RING_SUM_DELTA, IN_ELIM_THM, RING_OF_INT]], ALL_TAC] THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC q27 THEN REWRITE_TAC [IN_ELIM_THM, IN_UNIV] THEN EQ_TAC THENL [STRIP_TAC THEN SUBGOAL_THEN q26 MP_TAC THENL [X_GEN_TAC q25 THEN DISCH_TAC THEN MP_TAC v24 THEN ASM_SIMP_TAC [RING_MUL] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN FIRST_X_ASSUM (MP_TAC o (SPEC q21)) THEN MATCH_MP_TAC r20 THEN AP_TERM_TAC THEN AP_TERM_TAC THEN TRANS_TAC EQ_TRANS q18 THEN CONJ_TAC THENL [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC q17 THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC [] THEN COND_CASES_TAC THEN ASM_SIMP_TAC [RING_OF_INT_1, RING_OF_INT_0, RING_MUL_LID, RING_MUL_LZERO], ASM_SIMP_TAC [RING_SUM_DELTA, IN_ELIM_THM]], ALL_TAC] THEN DISCH_THEN (MP_TAC o (REWRITE_RULE [RIGHT_IMP_EXISTS_THM, SKOLEM_THM])) THEN DISCH_THEN (X_CHOOSE_TAC q16) THEN EXISTS_TAC q15 THEN MATCH_MP_TAC NUMBER_FIELD_TRACE_FORM_INJECTIVE THEN MAP_EVERY EXISTS_TAC [q14, q13, q12] THEN ASM_SIMP_TAC [RING_SUM] THEN X_GEN_TAC q11 THEN DISCH_TAC THEN SUBGOAL_THEN q10 SUBST1_TAC THENL [MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN q9 SUBST1_TAC THENL [MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC [RING_SUM], ALL_TAC] THEN ASM_SIMP_TAC [], DISCH_THEN (X_CHOOSE_THEN q8 SUBST1_TAC) THEN REWRITE_TAC [RING_SUM] THEN X_GEN_TAC q7 THEN USE_THEN "lin" (fun th => SIMP_TAC [th, RING_SUM]) THEN MATCH_MP_TAC r6 THEN EXISTS_TAC q4 THEN SIMP_TAC [RING_OF_INT_ISUM, FINITE_NUMSEG_LT, RING_OF_INT_MUL] THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC q3 THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC [] THEN AP_TERM_TAC THEN REMOVE_THEN "dual" (MP_TAC o (SPECL [q2, q1])) THEN ASM_REWRITE_TAC []])

  let SUBRING_GENERATED_HORNER_SPAN ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r40 ← RING_RULE (← q r"ring_sub r (ring_add r x y) x = (y:A)")
    let r62 ← RING_RULE (← q r"ring_neg r (ring_sub r (ring_0 r) y) = (y:A)")
    let r63 ← RING_RULE (← q r"ring_add r (ring_sub r x y) y = (x:A)")
    prove
      r"!(k:A ring) a f b m.
          ~trivial_ring k /\ a IN ring_carrier k /\
          ring_polynomial k f /\ monic k f /\ poly_deg k f = m /\
          (!i. ?n. coeff i f = ring_of_int k n) /\
          ring_polynomial k b /\
          f = poly_mul k (poly_sub k (poly_var k one) (poly_const k a)) b /\
          ring_carrier(subring_generated k {a}) =
          {ring_sum k {i | i < m}
             (\i. ring_mul k (ring_of_int k (c i)) (ring_pow k a i)) |
           c IN (:num->int)}
          ==> ring_carrier(subring_generated k {a}) =
              {ring_sum k {j | j < m}
                 (\j. ring_mul k (ring_of_int k (c j)) (coeff j b)) |
               c IN (:num->int)}"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM (ASSUME_TAC o (SYM o (checkM (fun th => (do if ← (do if ← (do let z85 ← (do let z86 ← (pure th); pure (concl z86)); pure (is_eq z85)) then (do let z90 ← (q r"f:(1->num)->A"); let z89 ← (do let z87 ← (do let z88 ← (pure th); pure (concl z88)); liftExcept (lhs z87)); pure (z89 == z90)) else pure false) then (do let z91 ← (do let z92 ← (do let z93 ← (pure th); pure (concl z93)); liftExcept (rhs z92)); pure (is_comb z91)) else pure false))))) THEN SUBGOAL_THEN (← q r"!t. coeff t (f:(1->num)->A) =
          ring_sub k (if t = 0 then ring_0 k else coeff (t - 1) b)
                     (ring_mul k a (coeff t b))") ASSUME_TAC THENL [GEN_TAC THEN FIRST_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z79 ← (do let z80 ← (pure th); pure (concl z80)); pure (is_eq z79)) then (do let z84 ← (q r"f:(1->num)->A"); let z83 ← (do let z81 ← (do let z82 ← (pure th); pure (concl z82)); liftExcept (rhs z81)); pure (z83 == z84)) else pure false))))) THEN MATCH_MP_TAC COEFF_POLY_MUL_X_MINUS THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(b = poly_0 k:(1->num)->A)") ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC (← q r"monic k (f:(1->num)->A)") THEN FIRST_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z73 ← (do let z74 ← (pure th); pure (concl z74)); pure (is_eq z73)) then (do let z78 ← (q r"f:(1->num)->A"); let z77 ← (do let z75 ← (do let z76 ← (pure th); pure (concl z76)); liftExcept (rhs z75)); pure (z77 == z78)) else pure false))))) THEN FIRST_ASSUM (SUBST1_TAC o (checkM (fun th => (do let z72 ← (q r"b = poly_0 k:(1->num)->A"); let z71 ← (do let z70 ← (pure th); pure (concl z70)); pure (z71 == z72))))) THEN SIMP_TAC [POLY_MUL_0, RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_CONST, MONIC_POLY_0, (← ASSUME (← q r"(a:A) IN ring_carrier k"))] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"poly_deg k (b:(1->num)->A) + 1 = m") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"b:(1->num)->A")] POLY_DEG_MUL_X_MINUS_A) THEN FIRST_ASSUM (SUBST1_TAC o (checkM (fun th => (do if ← (do let z64 ← (do let z65 ← (pure th); pure (concl z65)); pure (is_eq z64)) then (do let z69 ← (q r"f:(1->num)->A"); let z68 ← (do let z66 ← (do let z67 ← (pure th); pure (concl z67)); liftExcept (rhs z66)); pure (z68 == z69)) else pure false)))) THEN ASM_REWRITE_TAC [] THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"!t. m <= t ==> coeff t (b:(1->num)->A) = ring_0 k") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC COEFF_ABOVE_DEG THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"!t. coeff t (b:(1->num)->A) IN ring_carrier k") ASSUME_TAC THENL [ASM_SIMP_TAC [COEFF_IN_CARRIER_ALT], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(m = 0)") ASSUME_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"coeff (m - 1) (b:(1->num)->A) = ring_1 k") ASSUME_TAC THENL [UNDISCH_TAC (← q r"monic k (f:(1->num)->A)") THEN ASM_REWRITE_TAC [monic] THEN ASM_SIMP_TAC [LE_REFL, RING_MUL_RZERO, RING_SUB_RZERO], ALL_TAC] THEN SUBGOAL_THEN (← q r"!t. 1 <= t /\ t < m
          ==> coeff (t - 1) (b:(1->num)->A) =
              ring_add k (coeff t f) (ring_mul k a (coeff t b))") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN COND_CASES_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC r63 THEN ASM_SIMP_TAC [RING_MUL], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul k a (coeff 0 (b:(1->num)->A)) = ring_neg k (coeff 0 f)") ASSUME_TAC THENL [ASM_REWRITE_TAC [] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC r62 THEN ASM_SIMP_TAC [RING_MUL], ALL_TAC] THEN SUBGOAL_THEN (← q r"!t0 x. t0 < m
             ==> ring_sum k {t | t < m}
                   (\t. ring_mul k (ring_of_int k (if t = t0 then x else &0))
                                   (coeff t (b:(1->num)->A))) =
                 ring_mul k (ring_of_int k x) (coeff t0 b)") (LABEL_TAC "delta") THENL [REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS (← q r"ring_sum k {t | t < m}
          (\t. if t = t0 then ring_mul k (ring_of_int k x)
                                (coeff t0 (b:(1->num)->A))
               else ring_0 k)") THEN CONJ_TAC THENL [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"t:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC [] THEN COND_CASES_TAC THEN ASM_SIMP_TAC [RING_OF_INT_0, RING_MUL_LZERO], ASM_SIMP_TAC [RING_SUM_DELTA, IN_ELIM_THM, RING_MUL, RING_OF_INT]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!n. ?e. ring_of_int k n =
              ring_sum k {t | t < m}
                (\t. ring_mul k (ring_of_int k (e t))
                       (coeff t (b:(1->num)->A)))") ASSUME_TAC THENL [X_GEN_TAC (← q r"n:int") THEN EXISTS_TAC (← q r"\t:num. if t = m - 1 then (n:int) else &0") THEN USE_THEN "delta" (fun th => tactic_of do pure (ASM_SIMP_TAC [th, (← ARITH_RULE (← q r"~(m = 0) ==> m - 1 < m"))])) THEN ASM_SIMP_TAC [RING_MUL_RID, RING_OF_INT], ALL_TAC] THEN SUBGOAL_THEN (← q r"!j. j < m
          ==> ?e. ring_mul k a (coeff j (b:(1->num)->A)) =
                  ring_sum k {t | t < m}
                    (\t. ring_mul k (ring_of_int k (e t)) (coeff t b))") ASSUME_TAC THENL [X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN FIRST_ASSUM ((X_CHOOSE_TAC (← q r"n:int")) o ((SPEC (← q r"j:num")) o (checkM (fun th => (do if ← (do if ← (do let z50 ← (do let z51 ← (pure th); pure (concl z51)); pure (is_forall z50)) then (do let z52 ← (do pure (Prod.snd (← (do let z53 ← (do let z54 ← (pure th); pure (concl z54)); liftExcept (dest_forall z53))))); pure (is_exists z52)) else pure false) then (do let z55 ← (do let z56 ← (pure th); pure (concl z56)); canM (fun z57 => (do let z58 ← (pure z57); find_termM (fun z59 => (do let z61 ← (pure z59); let z60 ← (q r"f:(1->num)->A"); pure (z60 == z61))) z58)) z55) else pure false))))) THEN ASM_CASES_TAC (← q r"j = 0") THENL [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [(← GSYM RING_OF_INT_NEG)] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul k a (coeff j (b:(1->num)->A)) =
        ring_sub k (coeff (j - 1) b) (ring_of_int k n)") SUBST1_TAC THENL [FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"j:num")) o (checkM (fun th => (do if ← (do let z41 ← (do let z42 ← (pure th); pure (concl z42)); pure (is_forall z41)) then (do let z43 ← (do let z44 ← (pure th); pure (concl z44)); canM (fun z45 => (do let z46 ← (pure z45); find_termM (fun z47 => (do let z49 ← (pure z47); let z48 ← (q r"ring_add:(A ring)->A->A->A"); pure (z48 == z49))) z46)) z43) else pure false))))) THEN ANTS_TAC THENL [ASM_ARITH_TAC, DISCH_THEN SUBST1_TAC] THEN ASM_REWRITE_TAC [] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC r40 THEN ASM_SIMP_TAC [RING_MUL, RING_OF_INT], ALL_TAC] THEN EXISTS_TAC (← q r"\t:num. (if t = j - 1 then &1 else &0) -
                          (if t = m - 1 then (n:int) else &0)") THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{t:num | t < m}"), (← q r"\t:num. coeff t (b:(1->num)->A)")] RING_INT_LINCOMB) THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT] THEN DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [(← CONJUNCT1 (← CONJUNCT2 th))])) THEN SUBGOAL_THEN (← q r"j - 1 < m /\ m - 1 < m") STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN USE_THEN "delta" (fun th => ASM_SIMP_TAC [th]) THEN ASM_SIMP_TAC [RING_OF_INT_1, RING_MUL_LID, RING_MUL_RID, RING_OF_INT], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. ?c. ring_pow k a i =
              ring_sum k {t | t < m}
                (\t. ring_mul k (ring_of_int k (c t))
                       (coeff t (b:(1->num)->A)))") ASSUME_TAC THENL [INDUCT_TAC THENL [REWRITE_TAC [ring_pow, (← GSYM RING_OF_INT_1)] THEN ASM_REWRITE_TAC [], REWRITE_TAC [ring_pow] THEN FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"c:num->int") SUBST1_TAC) THEN ASM_SIMP_TAC [RING_MUL_INT_LINCOMB, FINITE_NUMSEG_LT, IN_ELIM_THM] THEN MATCH_MP_TAC RING_INT_LINCOMB_LINCOMB THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!d. d < m ==> coeff (m - 1 - d) (b:(1->num)->A) IN
                    ring_carrier(subring_generated k {a})") ASSUME_TAC THENL [INDUCT_TAC THENL [DISCH_TAC THEN REWRITE_TAC [SUB_0] THEN FIRST_ASSUM (SUBST1_TAC o (checkM (fun th => (do let z39 ← (q r"coeff (m - 1) (b:(1->num)->A) = ring_1 k"); let z38 ← (do let z37 ← (pure th); pure (concl z37)); pure (z38 == z39))))) THEN MATCH_MP_TAC IN_SUBRING_1 THEN REWRITE_TAC [SUBRING_SUBRING_GENERATED], DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun z34 => (do let z35 ← (do let z36 ← (pure z34); pure (concl z36)); pure (is_imp z35))))) THEN ANTS_TAC THENL [ASM_ARITH_TAC, DISCH_TAC] THEN SUBGOAL_THEN (← q r"m - 1 - SUC d = (m - 1 - d) - 1") SUBST1_TAC THENL [ARITH_TAC, ALL_TAC] THEN FIRST_ASSUM (MP_TAC o ((SPEC (← q r"m - 1 - d")) o (checkM (fun th => (do if ← (do let z25 ← (do let z26 ← (pure th); pure (concl z26)); pure (is_forall z25)) then (do let z27 ← (do let z28 ← (pure th); pure (concl z28)); canM (fun z29 => (do let z30 ← (pure z29); find_termM (fun z31 => (do let z33 ← (pure z31); let z32 ← (q r"ring_add:(A ring)->A->A->A"); pure (z32 == z33))) z30)) z27) else pure false))))) THEN ANTS_TAC THENL [ASM_ARITH_TAC, DISCH_THEN SUBST1_TAC] THEN FIRST_ASSUM ((X_CHOOSE_THEN (← q r"n:int") SUBST1_TAC) o ((SPEC (← q r"m - 1 - d")) o (checkM (fun th => (do if ← (do if ← (do let z13 ← (do let z14 ← (pure th); pure (concl z14)); pure (is_forall z13)) then (do let z15 ← (do pure (Prod.snd (← (do let z16 ← (do let z17 ← (pure th); pure (concl z17)); liftExcept (dest_forall z16))))); pure (is_exists z15)) else pure false) then (do let z18 ← (do let z19 ← (pure th); pure (concl z19)); canM (fun z20 => (do let z21 ← (pure z20); find_termM (fun z22 => (do let z24 ← (pure z22); let z23 ← (q r"f:(1->num)->A"); pure (z23 == z24))) z21)) z18) else pure false))))) THEN MATCH_MP_TAC IN_SUBRING_ADD THEN REWRITE_TAC [SUBRING_SUBRING_GENERATED] THEN CONJ_TAC THENL [MATCH_MP_TAC IN_SUBRING_INT THEN REWRITE_TAC [SUBRING_SUBRING_GENERATED], MATCH_MP_TAC IN_SUBRING_MUL THEN REWRITE_TAC [SUBRING_SUBRING_GENERATED] THEN CONJ_TAC THENL [ALL_TAC, FIRST_ASSUM ACCEPT_TAC] THEN MATCH_MP_TAC SUBRING_GENERATED_INC THEN ASM_REWRITE_TAC [SING_SUBSET, IN_SING]]], ALL_TAC] THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"z:A") THEN REWRITE_TAC [IN_ELIM_THM, IN_UNIV] THEN EQ_TAC THENL [ASM_REWRITE_TAC [IN_ELIM_THM, IN_UNIV] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:num->int") SUBST1_TAC) THEN MATCH_MP_TAC RING_INT_LINCOMB_LINCOMB THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM], DISCH_THEN (X_CHOOSE_THEN (← q r"c:num->int") SUBST1_TAC) THEN MATCH_MP_TAC IN_SUBRING_SUM THEN REWRITE_TAC [SUBRING_SUBRING_GENERATED, IN_ELIM_THM] THEN X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN MATCH_MP_TAC IN_SUBRING_MUL THEN REWRITE_TAC [SUBRING_SUBRING_GENERATED] THEN CONJ_TAC THENL [MATCH_MP_TAC IN_SUBRING_INT THEN REWRITE_TAC [SUBRING_SUBRING_GENERATED], FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"m - 1 - j")) o (checkM (fun th => (do if ← (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_forall z1)) then (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); canM (fun z5 => (do let z6 ← (pure z5); find_termM (fun z7 => (do let z9 ← (pure z7); let z8 ← (q r"subring_generated:(A ring)->(A->bool)->A ring"); pure (z8 == z9))) z6)) z3) else pure false) then (do let z10 ← (do pure (Prod.snd (← (do let z11 ← (do let z12 ← (pure th); pure (concl z12)); liftExcept (dest_forall z11))))); pure (is_imp z10)) else pure false))))) THEN ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"m - 1 - (m - 1 - j) = j") SUBST1_TAC THENL [ASM_ARITH_TAC, REWRITE_TAC []]]])

  let NUMBER_FIELD_MINIMAL_POLYNOMIAL_DERIV_SUBRING ← prove
    r"!(k:A ring) a.
        number_field k /\ a IN ring_carrier(ring_of_integers k)
        ==> poly_extend (subfield_generated k {ring_0 k},k) I (\v. a)
              (poly_deriv (subfield_generated k {ring_0 k})
                 (minimal_polynomial (subfield_generated k {ring_0 k},k) I a))
            IN ring_carrier(subring_generated k {a})"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. ?n. coeff i (minimal_polynomial (subfield_generated k {ring_0 k},k) I
                       (a:A)) = ring_of_int k n") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A")] RING_OF_INTEGERS_MINIMAL_POLYNOMIAL_Q) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"f = minimal_polynomial (subfield_generated k {ring_0 k},k) I (a:A)") THEN SUBGOAL_THEN (← q r"(f:(1->num)->A) IN
    ring_carrier(poly_ring (subfield_generated k {ring_0 k}) (:1))") ASSUME_TAC THENL [EXPAND_TAC "f" THEN MATCH_MP_TAC MINIMAL_POLYNOMIAL_IN_CARRIER THEN ASM_SIMP_TAC [NUMBER_FIELD_ALGEBRAIC, FIELD_EXTENSION_SUBFIELD_GENERATED], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"(\v. a):1->A"), (← q r"poly_deriv (subfield_generated k {ring_0 k:A}) f")] POLY_EXTEND_UNIVARIATE) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION, POLY_DERIV_IN_CARRIER] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC IN_SUBRING_SUM THEN REWRITE_TAC [SUBRING_SUBRING_GENERATED] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN REWRITE_TAC [I_THM, COEFF_POLY_DERIV, SUBFIELD_GENERATED, RING_OF_NUM_SUBFIELD_GENERATED] THEN FIRST_X_ASSUM ((X_CHOOSE_THEN (← q r"n:int") SUBST1_TAC) o (SPEC (← q r"i + 1"))) THEN MATCH_MP_TAC IN_SUBRING_MUL THEN REWRITE_TAC [SUBRING_SUBRING_GENERATED] THEN CONJ_TAC THENL [MATCH_MP_TAC IN_SUBRING_MUL THEN SIMP_TAC [SUBRING_SUBRING_GENERATED, IN_SUBRING_NUM, IN_SUBRING_INT], MATCH_MP_TAC IN_SUBRING_POW THEN REWRITE_TAC [SUBRING_SUBRING_GENERATED] THEN MATCH_MP_TAC SUBRING_GENERATED_INC THEN ASM_REWRITE_TAC [SING_SUBSET, IN_SING]])

  let NUMBER_FIELD_SUBRING_GENERATED_EQ_RING_OF_INTEGERS ← prove
    r"!(k:A ring) a.
        number_field k /\
        ring_carrier(subring_generated k {a}) =
        ring_carrier(ring_of_integers k)
        ==> subfield_generated k {a} = k"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN REWRITE_TAC [SUBFIELD_GENERATED_EQ, (← GSYM SUBSET_ANTISYM_EQ), RING_CARRIER_SUBFIELD_GENERATED_SUBSET] THEN REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A")] NUMBER_FIELD_INTEGRAL_MULTIPLE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"n:int") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"~(ring_of_int k n = ring_0 (k:A ring))") ASSUME_TAC THENL [ASM_MESON_TAC [number_field, RING_OF_INT_EQ_0_CHAR_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"x = ring_mul k (ring_inv k (ring_of_int k n))
          (ring_mul k (ring_of_int k n) (x:A))") SUBST1_TAC THENL [ASM_SIMP_TAC [RING_MUL_ASSOC, RING_INV, RING_OF_INT, FIELD_MUL_LINV, RING_MUL_LID], ALL_TAC] THEN SUBGOAL_THEN (← q r"!y. y IN ring_carrier(ring_of_integers k)
        ==> (y:A) IN ring_carrier(subfield_generated k {a})") ASSUME_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_eq z1)) then (do let z6 ← (q r"ring_carrier(ring_of_integers k:A ring)"); let z5 ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); liftExcept (rhs z3)); pure (z5 == z6)) else pure false))))) THEN REWRITE_TAC [(← GSYM SUBSET), SUBRING_SUBSET_SUBFIELD_GENERATED], ALL_TAC] THEN MATCH_MP_TAC IN_SUBFIELD_MUL THEN ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED] THEN MATCH_MP_TAC IN_SUBFIELD_INV THEN ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED, RING_OF_INT_IN_RING_OF_INTEGERS])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_POWER_BASIS_DUAL, NUMBER_FIELD_TRACE_DUAL_LATTICE,
           SUBRING_GENERATED_HORNER_SPAN, NUMBER_FIELD_MINIMAL_POLYNOMIAL_DERIV_SUBRING,
           NUMBER_FIELD_SUBRING_GENERATED_EQ_RING_OF_INTEGERS }
  -- @@RETURN END

end HolANT.PowerBasisIndex
