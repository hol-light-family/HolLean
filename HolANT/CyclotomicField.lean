/- ========================================================================= -/
/- ANT: Cyclotomic fields, abstractly (no complex numbers), in the ...     -/
/- ========================================================================= -/
/- File: HolANT/CyclotomicField.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/cyclotomic_field.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antcyclotomicfielddiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, ANT/integral.ml, Library/isum.ml, Library/products.ml, ANT/algmisc.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/prime_split.ml, ANT/norm_index.ml, ANT/discriminant.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/classgroup.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/relative_degree.ml, ANT/nf_valuation.ml, ANT/integrality.ml, ANT/dedekind_kummer.ml, Library/frag.ml, Library/grouptheory.ml, Library/symmetric_group.ml, Library/galois.ml, Library/ring_groups.ml, Library/finite_fields.ml, Library/integer.ml, Library/multiplicative.ml, Library/primitive.ml, ANT/cyclotomic_poly.ml, ANT/power_basis.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.CyclotomicField fills them).

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
import HolLibrary.Frag
import HolLibrary.GroupTheory
import HolLibrary.SymmetricGroup
import HolLibrary.Galois
import HolLibrary.RingGroups
import HolLibrary.FiniteFields
import HolLibrary.Integer
import HolLibrary.Multiplicative
import HolLibrary.Primitive
import HolANT.CyclotomicPoly
import HolANT.PowerBasis

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

namespace HolANT.CyclotomicField

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (CARD_IMAGE_INJ CARD_SUBSET COEFF_IN_CARRIER COEFF_POLY_LMUL CONTRAPOS_THM
   COPRIME_0 COPRIME_LMUL CYCLOTOMIC_POLY_DEG CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE
   CYCLOTOMIC_POLY_IN_CARRIER CYCLOTOMIC_POLY_MONIC CYCLOTOMIC_POLY_ROOT
   CYCLOTOMIC_POLY_ROOT_EQ DIVIDES_ZERO EQ_IMP_LE EXTENSION_DEGREE_SIMPLE
   FIELD_EXTENSION_SUBFIELD_GENERATED FIELD_IMP_INTEGRAL_DOMAIN
   FIELD_IMP_NONTRIVIAL_RING FIELD_NONTRIVIAL FIELD_POLY_DEG_EQ_0
   FIELD_REAL_RING FIELD_SUBFIELD_GENERATED FINITE_IMP_FIELD_EXTENSION
   FINITE_NUMSEG_LT FINITE_SIMPLE_ALGEBRAIC_EXTENSION FINITE_SUBSET
   FORALL_IN_IMAGE FUN_EQ_THM IMP_CONJ INTEGER_RING INTEGRAL_DOMAIN_MUL_EQ_0
   IN_ELIM_THM IN_RING_POLYNOMIAL_CARRIER_COMPOSE I_O_ID
   KRONECKER_SIMPLE_FIELD_EXTENSION LEFT_IMP_EXISTS_THM LE_0 LE_TRANS
   MEMBER_NOT_EMPTY MINIMAL_POLYNOMIAL_DEG_LE MINIMAL_POLYNOMIAL_DIVIDES
   MINIMAL_POLYNOMIAL_MONIC MONIC_DIVIDES_EQ MONIC_HOMOMORPHIC_IMAGE
   MONIC_IMP_NONZERO MONO_OR MULT_SYM NOT_LT NUMBER_FIELD_ALGEBRAIC
   NUMBER_FIELD_FREE_BASIS_POWERS NUMBER_FIELD_IMP_FIELD
   NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q NUMBER_FIELD_PRIME_SUBFIELD PHI_0 PHI_ALT
   PHI_EQ_0 POLY_COMPOSE_HOMOMORPHISM_MUL POLY_CONST_1 POLY_DEG_0 POLY_DEG_EQ_0
   POLY_DEG_MONOMORPHIC_IMAGE POLY_DEG_MUL POLY_DEG_SUBFIELD_GENERATED
   POLY_DEG_UNIT POLY_DERIV_1 POLY_DERIV_SUB POLY_DERIV_VAR_POW
   POLY_DIVIDES_X_MINUS_ROOT POLY_DIV_REM POLY_EQ_0_MONOMORPHIC_IMAGE POLY_EVAL
   POLY_EVAL_0 POLY_EVAL_1 POLY_EVAL_CONST POLY_EVAL_MUL POLY_EVAL_POW
   POLY_EVAL_SUB POLY_EVAL_VAR POLY_EXTEND POLY_EXTEND_CONST
   POLY_EXTEND_EVALUATE POLY_EXTEND_HOMOMORPHIC_IMAGE
   POLY_EXTEND_RING_OF_INTEGERS POLY_EXTEND_SUB POLY_EXTEND_VARPOW POLY_MUL_0
   POLY_MUL_SYM POLY_RING_CLAUSES POLY_ROOT_BOUND
   POLY_VAR_POW_SUB_1_HOMOMORPHIC_IMAGE PRIME_COPRIME_EQ PRIME_FACTOR_INDUCT : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (PRIME_IMP_NZ PRIME_IMP_RING_IDEAL PRIME_SUBFIELD_MONOMORPHIC_IMAGE
   PRIME_SUBFIELD_SUBFIELD_GENERATED PRIME_SUBFIELD_TOWER_LAW REAL_RING_CHAR
   REPEATED_ROOT_POLY_DERIV_ZERO RING_0 RING_1 RING_ADD_LZERO RING_ADD_RZERO
   RING_CHAR_SUBFIELD_GENERATED RING_DIVIDES_IN_CARRIER RING_DIVIDES_MUL2
   RING_ENDOMORPHISM_FROBENIUS RING_HOMOMORPHISM_0 RING_HOMOMORPHISM_ADD
   RING_HOMOMORPHISM_INTEGER_RING_OF_INT RING_HOMOMORPHISM_INTO_SUBRING
   RING_HOMOMORPHISM_IN_CARRIER RING_HOMOMORPHISM_MUL
   RING_HOMOMORPHISM_POLY_EXTEND RING_HOMOMORPHISM_POLY_RINGS
   RING_HOMOMORPHISM_POW RING_HOMOMORPHISM_RING_COSET
   RING_HOMOMORPHISM_RING_OF_INT RING_HOMOMORPHISM_SUBFIELD_INCLUSION
   RING_MONOMORPHISM_I RING_MONOMORPHISM_IMP_HOMOMORPHISM
   RING_MONOMORPHISM_INTEGER_RING_OF_INT RING_MUL RING_MUL_LZERO RING_MUL_RZERO
   RING_MUL_SYM RING_OF_INTEGERS RING_OF_INTEGERS_CARRIER
   RING_OF_INTEGERS_INTEGER_MINIMAL_POLYNOMIAL RING_OF_INT_1
   RING_OF_INT_SUBFIELD_GENERATED RING_OF_NUM RING_OF_NUM_0 RING_OF_NUM_EQ_0
   RING_OF_NUM_IN_PRIME_IDEAL RING_ORDER_EQ_1 RING_POLYNOMIAL RING_POLYNOMIAL_0
   RING_POLYNOMIAL_1 RING_POLYNOMIAL_CONST RING_POLYNOMIAL_IMP_POWERSERIES
   RING_POLYNOMIAL_MUL RING_POLYNOMIAL_POW RING_POLYNOMIAL_SUB
   RING_POLYNOMIAL_VAR RING_POW RING_POWERSERIES_1 RING_POWERSERIES_POW
   RING_POWERSERIES_VAR RING_POW_1 RING_POW_2 RING_POW_EQ_LT_EQ RING_POW_ONE
   RING_POW_POW RING_POW_RING_ORDER RING_POW_ZERO RING_SUB_EQ_0 RING_SUB_REFL
   RING_SUB_RZERO RING_UNIT_1 RING_UNIT_HOMOMORPHIC_IMAGE RING_UNIT_POLY_CONST
   SUBFIELD_GENERATED SUBFIELD_GENERATED_SING_ALGEBRAIC
   SUBRING_GENERATED_BY_SUBFIELD_GENERATED SUBSET SUBSET_REFL SUC_SUB1
   TRIVIAL_RING_10 algebraic_over field_extension integral_element monic
   num_CASES number_field o_THM poly_0 poly_const poly_eval ring_divides
   ring_endomorphism ring_irreducible ring_pow ring_unit : thm)
  deriving Inhabited

/-- What cyclotomic_field.ml uses from Session besides theorems. -/
structure CyclotomicFieldDeps where
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
/- cyclotomic_field.ml phrases from line 74 to 745                        -/
/- ---------------------------------------------------------------------- -/

structure CyclotomicField01 where
  -- @@FIELDS
  NUMBER_FIELD_FINITE_EXTENSION : thm
  POLY_EXTEND_INTEGER_RING_HOMOMORPHIC_IMAGE : thm
  POLY_EXTEND_INTEGER_RING_VAR_POW_SUB_1 : thm
  RING_UNIT_POLY_DIVIDES_MONIC : thm
  POLY_VAR_POW_SUB_1_COMMON_ROOT : thm
  POLY_VAR_POW_SUB_1_FROBENIUS_ROOT : thm
  NUMBER_FIELD_VAR_POW_SUB_1_FROBENIUS_ROOT : thm
  NUMBER_FIELD_VAR_POW_SUB_1_DIVISOR_ROOT_POW : thm
  NUMBER_FIELD_VAR_POW_SUB_1_DIVISOR_DEG : thm
  NUMBER_FIELD_INTEGER_MINIMAL_POLYNOMIAL_DIVIDES : thm
  CYCLOTOMIC_POLY_MINIMAL_POLYNOMIAL : thm
  PHI_LE_POLY_DEG_PRIMITIVE_ROOT : thm
  PHI_LE_POLY_DEG_CYCLOTOMIC_DIVISOR_ROOT : thm
  PHI_LE_POLY_DEG_CYCLOTOMIC_DIVISOR : thm
  CYCLOTOMIC_POLY_IRREDUCIBLE_PRIME_SUBFIELD : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupCyclotomicField01 [HolBase] (D : CyclotomicFieldDeps) :
    ExceptT String IO CyclotomicField01 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, RING_RULE, SET_TAC, .. } := D
  let { CARD_IMAGE_INJ, CARD_SUBSET, COEFF_IN_CARRIER, COEFF_POLY_LMUL, CONTRAPOS_THM,
        COPRIME_0, COPRIME_LMUL, CYCLOTOMIC_POLY_DEG,
        CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE, CYCLOTOMIC_POLY_IN_CARRIER,
        CYCLOTOMIC_POLY_MONIC, CYCLOTOMIC_POLY_ROOT, CYCLOTOMIC_POLY_ROOT_EQ,
        DIVIDES_ZERO, EQ_IMP_LE, FIELD_EXTENSION_SUBFIELD_GENERATED,
        FIELD_IMP_INTEGRAL_DOMAIN, FIELD_IMP_NONTRIVIAL_RING, FIELD_NONTRIVIAL,
        FIELD_POLY_DEG_EQ_0, FIELD_SUBFIELD_GENERATED, FINITE_IMP_FIELD_EXTENSION,
        FINITE_NUMSEG_LT, FINITE_SIMPLE_ALGEBRAIC_EXTENSION, FINITE_SUBSET,
        FORALL_IN_IMAGE, FUN_EQ_THM, IMP_CONJ, INTEGER_RING, INTEGRAL_DOMAIN_MUL_EQ_0,
        IN_ELIM_THM, IN_RING_POLYNOMIAL_CARRIER_COMPOSE, I_O_ID,
        KRONECKER_SIMPLE_FIELD_EXTENSION, LEFT_IMP_EXISTS_THM, LE_0, LE_TRANS,
        MEMBER_NOT_EMPTY, MINIMAL_POLYNOMIAL_DEG_LE, MINIMAL_POLYNOMIAL_DIVIDES,
        MINIMAL_POLYNOMIAL_MONIC, MONIC_DIVIDES_EQ, MONIC_HOMOMORPHIC_IMAGE,
        MONIC_IMP_NONZERO, MULT_SYM, NOT_LT, NUMBER_FIELD_ALGEBRAIC,
        NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q,
        NUMBER_FIELD_PRIME_SUBFIELD, PHI_0, PHI_ALT, PHI_EQ_0,
        POLY_COMPOSE_HOMOMORPHISM_MUL, POLY_CONST_1, POLY_DEG_0, POLY_DEG_EQ_0,
        POLY_DEG_MONOMORPHIC_IMAGE, POLY_DEG_MUL, POLY_DEG_SUBFIELD_GENERATED,
        POLY_DEG_UNIT, POLY_DERIV_1, POLY_DERIV_SUB, POLY_DERIV_VAR_POW,
        POLY_DIVIDES_X_MINUS_ROOT, POLY_DIV_REM, POLY_EQ_0_MONOMORPHIC_IMAGE,
        POLY_EVAL, POLY_EVAL_0, POLY_EVAL_1, POLY_EVAL_CONST, POLY_EVAL_MUL,
        POLY_EVAL_POW, POLY_EVAL_SUB, POLY_EVAL_VAR, POLY_EXTEND, POLY_EXTEND_CONST,
        POLY_EXTEND_EVALUATE, POLY_EXTEND_HOMOMORPHIC_IMAGE,
        POLY_EXTEND_RING_OF_INTEGERS, POLY_EXTEND_SUB, POLY_EXTEND_VARPOW, POLY_MUL_0,
        POLY_RING_CLAUSES, POLY_ROOT_BOUND, POLY_VAR_POW_SUB_1_HOMOMORPHIC_IMAGE,
        PRIME_COPRIME_EQ, PRIME_FACTOR_INDUCT, .. } := D.core1
  let { PRIME_IMP_NZ, PRIME_IMP_RING_IDEAL, PRIME_SUBFIELD_MONOMORPHIC_IMAGE,
        PRIME_SUBFIELD_SUBFIELD_GENERATED, PRIME_SUBFIELD_TOWER_LAW,
        REPEATED_ROOT_POLY_DERIV_ZERO, RING_0, RING_1, RING_ADD_LZERO, RING_ADD_RZERO,
        RING_CHAR_SUBFIELD_GENERATED, RING_DIVIDES_IN_CARRIER, RING_DIVIDES_MUL2,
        RING_ENDOMORPHISM_FROBENIUS, RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_ADD,
        RING_HOMOMORPHISM_INTEGER_RING_OF_INT, RING_HOMOMORPHISM_INTO_SUBRING,
        RING_HOMOMORPHISM_IN_CARRIER, RING_HOMOMORPHISM_MUL,
        RING_HOMOMORPHISM_POLY_EXTEND, RING_HOMOMORPHISM_POW,
        RING_HOMOMORPHISM_RING_COSET, RING_HOMOMORPHISM_RING_OF_INT,
        RING_HOMOMORPHISM_SUBFIELD_INCLUSION, RING_MONOMORPHISM_I,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MONOMORPHISM_INTEGER_RING_OF_INT,
        RING_MUL, RING_MUL_LZERO, RING_MUL_RZERO, RING_MUL_SYM, RING_OF_INTEGERS,
        RING_OF_INTEGERS_CARRIER, RING_OF_INTEGERS_INTEGER_MINIMAL_POLYNOMIAL,
        RING_OF_INT_1, RING_OF_INT_SUBFIELD_GENERATED, RING_OF_NUM, RING_OF_NUM_0,
        RING_OF_NUM_EQ_0, RING_OF_NUM_IN_PRIME_IDEAL, RING_ORDER_EQ_1, RING_POLYNOMIAL,
        RING_POLYNOMIAL_0, RING_POLYNOMIAL_1, RING_POLYNOMIAL_CONST,
        RING_POLYNOMIAL_IMP_POWERSERIES, RING_POLYNOMIAL_MUL, RING_POLYNOMIAL_POW,
        RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_VAR, RING_POW, RING_POWERSERIES_1,
        RING_POWERSERIES_POW, RING_POWERSERIES_VAR, RING_POW_1, RING_POW_2,
        RING_POW_EQ_LT_EQ, RING_POW_ONE, RING_POW_POW, RING_POW_RING_ORDER,
        RING_POW_ZERO, RING_SUB_EQ_0, RING_SUB_REFL, RING_SUB_RZERO, RING_UNIT_1,
        RING_UNIT_POLY_CONST, SUBFIELD_GENERATED,
        SUBRING_GENERATED_BY_SUBFIELD_GENERATED, SUBSET, SUBSET_REFL, SUC_SUB1,
        algebraic_over, field_extension, integral_element, monic, num_CASES,
        number_field, o_THM, poly_0, poly_const, poly_eval, ring_divides,
        ring_endomorphism, ring_irreducible, ring_pow, ring_unit, .. } := D.core2
  -- @@SCOPE END

  let NUMBER_FIELD_FINITE_EXTENSION ← prove
    r"!(k:A ring) (l:B ring) h.
        number_field k /\ finite_extension(k,l) h ==> number_field l"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP FINITE_IMP_FIELD_EXTENSION)) THEN REWRITE_TAC [field_extension] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring")] PRIME_SUBFIELD_TOWER_LAW) THEN RULE_ASSUM_TAC (REWRITE_RULE [number_field]) THEN ASM_SIMP_TAC [number_field, RING_MONOMORPHISM_IMP_HOMOMORPHISM])

  let POLY_EXTEND_INTEGER_RING_HOMOMORPHIC_IMAGE ← prove
    r"!(r:A ring) (s:B ring) f x p.
        ring_homomorphism(r,s) f /\ x IN ring_carrier r /\
        p IN ring_carrier(poly_ring integer_ring (:1))
        ==> f(poly_extend (integer_ring,r) (ring_of_int r) (\v. x) p) =
            poly_extend (integer_ring,s) (ring_of_int s) (\v. f x) p"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"r:A ring"), (← q r"s:B ring"), (← q r"ring_of_int r:int->A"), (← q r"(:1)"), (← q r"\v:1. (x:A)"), (← q r"f:A->B"), (← q r"p:(1->num)->int")] POLY_EXTEND_HOMOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, SUBSET, FORALL_IN_IMAGE] THEN DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN BINOP_TAC THEN REWRITE_TAC [FUN_EQ_THM, o_THM] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_RING_OF_INT])

  let POLY_EXTEND_INTEGER_RING_VAR_POW_SUB_1 ← prove
    r"!(r:A ring) x n.
        x IN ring_carrier r
        ==> poly_extend (integer_ring,r) (ring_of_int r) (\v. x)
              (poly_sub integer_ring
                (poly_pow integer_ring (poly_var integer_ring one) n)
                (poly_1 integer_ring)) =
            ring_sub r (ring_pow r x n) (ring_1 r)"
    (SIMP_TAC [POLY_EXTEND_SUB, RING_POLYNOMIAL_POW, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_1, RING_HOMOMORPHISM_INTEGER_RING_OF_INT, POLY_EXTEND_VARPOW] THEN REWRITE_TAC [(← GSYM POLY_CONST_1)] THEN SIMP_TAC [POLY_EXTEND_CONST, RING_HOMOMORPHISM_INTEGER_RING_OF_INT, RING_1, INTEGER_RING, RING_OF_INT_1])

  let RING_UNIT_POLY_DIVIDES_MONIC ← prove
    r"!(r:A ring) p q.
        monic r q /\ ring_divides (poly_ring r (:1)) p q /\ poly_deg r p = 0
        ==> ring_unit (poly_ring r (:1)) p"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (GEN_REWRITE_RULE id [ring_divides])) THEN REWRITE_TAC [(← CONJUNCT2 POLY_RING_CLAUSES)] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"b:(1->num)->A") (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)))) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:(1->num)->A")] POLY_DEG_EQ_0) THEN ASM_REWRITE_TAC [RING_POLYNOMIAL] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:A") STRIP_ASSUME_TAC) THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC [RING_UNIT_POLY_CONST] THEN UNDISCH_TAC (← q r"monic r (poly_mul r (poly_const r c) (b:(1->num)->A))") THEN ASM_SIMP_TAC [monic, COEFF_POLY_LMUL, RING_POLYNOMIAL_IMP_POWERSERIES, RING_POLYNOMIAL] THEN DISCH_TAC THEN REWRITE_TAC [ring_unit] THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"coeff (poly_deg r (poly_mul r (poly_const r c) b))
                    (b:(1->num)->A)") THEN ASM_SIMP_TAC [COEFF_IN_CARRIER, RING_POLYNOMIAL_IMP_POWERSERIES, RING_POLYNOMIAL])

  let POLY_VAR_POW_SUB_1_COMMON_ROOT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!r:A ring a b c.
        a IN ring_carrier r /\ b IN ring_carrier r /\ c IN ring_carrier r /\
        ring_mul r a b = ring_1 r /\ ring_mul r c b = ring_0 r
        ==> c = ring_0 r")
    prove
      r"!(r:A ring) p q n a.
          p IN ring_carrier(poly_ring r (:1)) /\
          q IN ring_carrier(poly_ring r (:1)) /\
          poly_mul r p q =
          poly_sub r (poly_pow r (poly_var r one) n) (poly_1 r) /\
          a IN ring_carrier r /\
          poly_eval r p a = ring_0 r /\ poly_eval r q a = ring_0 r
          ==> ring_of_num r n = ring_0 r"
      (REPEAT GEN_TAC THEN ABBREV_TAC (← q r"u = poly_sub r (poly_var r one) (poly_const r (a:A))") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_divides (poly_ring r (:1)) u (p:(1->num)->A) /\
                  ring_divides (poly_ring r (:1)) u (q:(1->num)->A)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "u" THEN ASM_SIMP_TAC [POLY_DIVIDES_X_MINUS_ROOT], ALL_TAC] THEN SUBGOAL_THEN (← q r"poly_pow r u 2 = poly_mul r u (u:(1->num)->A)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"poly_ring (r:A ring) (:1)"), (← q r"u:(1->num)->A")] RING_POW_2) THEN REWRITE_TAC [(← CONJUNCT2 POLY_RING_CLAUSES)] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC [RING_DIVIDES_IN_CARRIER], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"poly_mul r p q:(1->num)->A"), (← q r"a:A")] REPEATED_ROOT_POLY_DERIV_ZERO) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"poly_ring (r:A ring) (:1)"), (← q r"u:(1->num)->A"), (← q r"p:(1->num)->A"), (← q r"u:(1->num)->A"), (← q r"q:(1->num)->A")] RING_DIVIDES_MUL2) THEN ASM_REWRITE_TAC [(← CONJUNCT2 POLY_RING_CLAUSES)], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_pow r a n = ring_1 (r:A ring)") MP_TAC THENL [MP_TAC (← AP_TERM (← q r"\p. poly_eval r p (a:A)") (← ASSUME (← q r"poly_mul r p q = poly_sub r (poly_pow r (poly_var r one) n)
                                    (poly_1 (r:A ring))"))) THEN RULE_ASSUM_TAC (REWRITE_RULE [POLY_RING_CLAUSES, IN_ELIM_THM]) THEN ASM_SIMP_TAC [POLY_EVAL_MUL, POLY_EVAL_SUB, POLY_EVAL_POW, POLY_EVAL_VAR, POLY_EVAL_1, RING_POLYNOMIAL_POW, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_1, RING_MUL_LZERO, RING_0] THEN DISCH_THEN (MP_TAC o SYM) THEN ASM_SIMP_TAC [RING_SUB_EQ_0, RING_POW, RING_1], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN SIMP_TAC [POLY_DERIV_SUB, RING_POWERSERIES_POW, RING_POWERSERIES_VAR, RING_POWERSERIES_1, POLY_DERIV_VAR_POW, POLY_DERIV_1] THEN ASM_SIMP_TAC [POLY_EVAL_SUB, POLY_EVAL_0, POLY_EVAL_MUL, POLY_EVAL_CONST, POLY_EVAL_POW, POLY_EVAL_VAR, RING_POLYNOMIAL_MUL, RING_POLYNOMIAL_CONST, RING_POLYNOMIAL_POW, RING_POLYNOMIAL_0, RING_POLYNOMIAL_VAR, RING_OF_NUM, RING_SUB_RZERO, RING_MUL, RING_POW] THEN DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN (← q r"m:num") SUBST1_TAC) (← SPEC (← q r"n:num") num_CASES) THEN REWRITE_TAC [RING_OF_NUM_0, SUC_SUB1, ring_pow] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC r1 THEN MAP_EVERY EXISTS_TAC [(← q r"a:A"), (← q r"ring_pow r (a:A) m")] THEN ASM_SIMP_TAC [RING_POW, RING_OF_NUM])

  let POLY_VAR_POW_SUB_1_FROBENIUS_ROOT ← prove
    r"!(r:A ring) q g n x.
        prime(ring_char r) /\
        q IN ring_carrier(poly_ring integer_ring (:1)) /\
        g IN ring_carrier(poly_ring integer_ring (:1)) /\
        poly_mul integer_ring q g =
        poly_sub integer_ring
          (poly_pow integer_ring (poly_var integer_ring one) n)
          (poly_1 integer_ring) /\
        x IN ring_carrier r /\
        poly_extend (integer_ring,r) (ring_of_int r) (\v. x) q = ring_0 r /\
        poly_extend (integer_ring,r) (ring_of_int r)
          (\v. ring_pow r x (ring_char r)) g = ring_0 r
        ==> ring_char r divides n"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [(← GSYM RING_OF_NUM_EQ_0)] THEN MATCH_MP_TAC POLY_VAR_POW_SUB_1_COMMON_ROOT THEN MAP_EVERY EXISTS_TAC [(← q r"ring_of_int (r:A ring) o (q:(1->num)->int)"), (← q r"ring_of_int (r:A ring) o (g:(1->num)->int)"), (← q r"ring_pow r (x:A) (ring_char r)")] THEN MP_TAC (← ISPEC (← q r"r:A ring") RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN DISCH_THEN (fun th => tactic_of do pure ((← do let hom ← (pure (fun t => (do pure (← MATCH_MP (← REWRITE_RULE [IMP_CONJ] t) th)))); pure (REWRITE_TAC [poly_eval, (← GSYM (← MATCH_MP POLY_EXTEND_EVALUATE th))] THEN ASM_SIMP_TAC [RING_POW, (← hom IN_RING_POLYNOMIAL_CARRIER_COMPOSE)] THEN CONJ_TAC THENL [MP_TAC (← BETA_RULE (← AP_TERM (← q r"\p:(1->num)->int. ring_of_int (r:A ring) o p") (← ASSUME (← q r"poly_mul integer_ring q g =                  poly_sub integer_ring                    (poly_pow integer_ring (poly_var integer_ring one) n)                    (poly_1 integer_ring)")))) THEN ASM_SIMP_TAC [(← hom POLY_COMPOSE_HOMOMORPHISM_MUL), RING_POLYNOMIAL_IMP_POWERSERIES, RING_POLYNOMIAL, (← MATCH_MP POLY_VAR_POW_SUB_1_HOMOMORPHIC_IMAGE th)], ALL_TAC])))) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"r:A ring"), (← q r"\y:A. ring_pow r y (ring_char r)"), (← q r"x:A"), (← q r"q:(1->num)->int")] POLY_EXTEND_INTEGER_RING_HOMOMORPHIC_IMAGE) THEN ASM_SIMP_TAC [(← GSYM ring_endomorphism), RING_ENDOMORPHISM_FROBENIUS] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [RING_POW_ZERO, PRIME_IMP_NZ])

  let NUMBER_FIELD_VAR_POW_SUB_1_FROBENIUS_ROOT ← prove
    r"!(k:A ring) q g n p w.
        number_field k /\ prime p /\
        q IN ring_carrier(poly_ring integer_ring (:1)) /\
        g IN ring_carrier(poly_ring integer_ring (:1)) /\
        poly_mul integer_ring q g =
        poly_sub integer_ring
          (poly_pow integer_ring (poly_var integer_ring one) n)
          (poly_1 integer_ring) /\
        w IN ring_carrier(ring_of_integers k) /\
        poly_extend (integer_ring,k) (ring_of_int k) (\v. w) q = ring_0 k /\
        poly_extend (integer_ring,k) (ring_of_int k) (\v. ring_pow k w p) g =
        ring_0 k
        ==> p divides n"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"p:num")] NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q) THEN ASM_REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY), IN_ELIM_THM] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"P:A->bool") STRIP_ASSUME_TAC) o (CONJUNCT1 o CONJUNCT2)) THEN ABBREV_TAC (← q r"R = quotient_ring (ring_of_integers k) (P:A->bool)") THEN ABBREV_TAC (← q r"h = ring_coset (ring_of_integers k) (P:A->bool)") THEN SUBGOAL_THEN (← q r"ring_homomorphism(ring_of_integers k,R) (h:A->A->bool) /\
    ring_char R = p") STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["R", "h"] THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_COSET, PRIME_IMP_RING_IDEAL] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"p:num")] RING_OF_NUM_IN_PRIME_IDEAL) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x f. x IN ring_carrier(ring_of_integers k) /\
          f IN ring_carrier(poly_ring integer_ring (:1))
          ==> (h:A->A->bool)
                (poly_extend (integer_ring,k) (ring_of_int k) (\v. x) f) =
              poly_extend (integer_ring,R) (ring_of_int R) (\v. h x) f") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"\v:1. (x:A)"), (← q r"f:(1->num)->int")] POLY_EXTEND_RING_OF_INTEGERS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o (SYM o CONJUNCT1)) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"R:(A->bool)ring"), (← q r"h:A->A->bool"), (← q r"x:A"), (← q r"f:(1->num)->int")] POLY_EXTEND_INTEGER_RING_HOMOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN FIRST_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC LAND_CONV [(← SYM th)])) THEN MATCH_MP_TAC POLY_VAR_POW_SUB_1_FROBENIUS_ROOT THEN MAP_EVERY EXISTS_TAC [(← q r"q:(1->num)->int"), (← q r"g:(1->num)->int"), (← q r"(h:A->A->bool) w")] THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ring_pow R ((h:A->A->bool) w) p = h(ring_pow k w p) /\
                h(ring_0 k) = ring_0 R /\
                ring_pow k w p IN ring_carrier(ring_of_integers k)") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"w:A"), (← q r"p:num")] RING_POW) THEN MP_TAC (← MATCH_MP RING_HOMOMORPHISM_POW (← ASSUME (← q r"ring_homomorphism(ring_of_integers k,R) (h:A->A->bool)"))) THEN MP_TAC (← MATCH_MP RING_HOMOMORPHISM_0 (← ASSUME (← q r"ring_homomorphism(ring_of_integers k,R) (h:A->A->bool)"))) THEN ASM_SIMP_TAC [RING_OF_INTEGERS], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], FIRST_X_ASSUM (MP_TAC o (SPECL [(← q r"w:A"), (← q r"q:(1->num)->int")])), FIRST_X_ASSUM (MP_TAC o (SPECL [(← q r"ring_pow k w p:A"), (← q r"g:(1->num)->int")]))] THEN ANTS_TAC THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ACCEPT_TAC o SYM))

  let NUMBER_FIELD_VAR_POW_SUB_1_DIVISOR_ROOT_POW ← prove
    r"!(k:A ring) q n p w.
        number_field k /\ monic integer_ring q /\
        ring_divides (poly_ring integer_ring (:1)) q
          (poly_sub integer_ring
             (poly_pow integer_ring (poly_var integer_ring one) n)
             (poly_1 integer_ring)) /\
        w IN ring_carrier k /\
        poly_extend (integer_ring,k) (ring_of_int k) (\v. w) q = ring_0 k /\
        prime p /\ ~(p divides n)
        ==> poly_extend (integer_ring,k) (ring_of_int k)
              (\v. ring_pow k w p) q = ring_0 k"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (GEN_REWRITE_RULE id [ring_divides])) THEN REWRITE_TAC [(← CONJUNCT2 POLY_RING_CLAUSES)] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"g:(1->num)->int") (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))))) THEN SUBGOAL_THEN (← q r"!x. x IN ring_carrier(k:A ring)
        ==> ring_mul k
              (poly_extend (integer_ring,k) (ring_of_int k) (\v. x)
                           (q:(1->num)->int))
              (poly_extend (integer_ring,k) (ring_of_int k) (\v. x)
                           (g:(1->num)->int)) =
            ring_sub k (ring_pow k x n) (ring_1 k)") ASSUME_TAC THENL [X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"k:A ring"), (← q r"(:1)"), (← q r"ring_of_int k:int->A"), (← q r"\v:1. (x:A)")] RING_HOMOMORPHISM_POLY_EXTEND) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN DISCH_THEN (MP_TAC o ((SPECL [(← q r"q:(1->num)->int"), (← q r"g:(1->num)->int")]) o (MATCH_MP RING_HOMOMORPHISM_MUL))) THEN ASM_REWRITE_TAC [(← CONJUNCT2 POLY_RING_CLAUSES)] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [POLY_EXTEND_INTEGER_RING_VAR_POW_SUB_1], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_pow k w n = ring_1 (k:A ring)") ASSUME_TAC THENL [FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"w:A"))) THEN ASM_SIMP_TAC [RING_MUL_LZERO, POLY_EXTEND] THEN DISCH_THEN (MP_TAC o SYM) THEN ASM_SIMP_TAC [RING_SUB_EQ_0, RING_POW, RING_1], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"ring_pow k w p:A"))) THEN ASM_SIMP_TAC [RING_POW, RING_POW_POW] THEN ONCE_REWRITE_TAC [MULT_SYM] THEN ASM_SIMP_TAC [(← GSYM RING_POW_POW), RING_POW_ONE, RING_SUB_REFL, RING_1] THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_MUL_EQ_0, POLY_EXTEND, FIELD_IMP_INTEGRAL_DOMAIN, NUMBER_FIELD_IMP_FIELD] THEN ASM_CASES_TAC (← q r"poly_extend (integer_ring,k:A ring) (ring_of_int k) (\v. ring_pow k w p)
                (q:(1->num)->int) = ring_0 k") THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"~((p:num) divides n)") THEN REWRITE_TAC [] THEN MATCH_MP_TAC NUMBER_FIELD_VAR_POW_SUB_1_FROBENIUS_ROOT THEN MAP_EVERY EXISTS_TAC [(← q r"k:A ring"), (← q r"q:(1->num)->int"), (← q r"g:(1->num)->int"), (← q r"w:A")] THEN ASM_REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM, integral_element] THEN EXISTS_TAC (← q r"q:(1->num)->int") THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_VAR_POW_SUB_1_DIVISOR_DEG ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"c:num <= d ==> a <= c ==> a <= d")
    prove
      r"!(k:A ring) z n q.
          number_field k /\ z IN ring_carrier k /\ ring_order k z = n /\
          monic integer_ring q /\
          ring_divides (poly_ring integer_ring (:1)) q
            (poly_sub integer_ring
               (poly_pow integer_ring (poly_var integer_ring one) n)
               (poly_1 integer_ring)) /\
          poly_extend (integer_ring,k) (ring_of_int k) (\v. z) q = ring_0 k
          ==> phi n <= poly_deg integer_ring q"
      (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [PHI_0, LE_0] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP RING_DIVIDES_IN_CARRIER)) THEN SUBGOAL_THEN (← q r"!c. coprime(c,n)
          ==> poly_extend (integer_ring,k) (ring_of_int k) (\v. ring_pow k z c)
                (q:(1->num)->int) = ring_0(k:A ring)") ASSUME_TAC THENL [MATCH_MP_TAC PRIME_FACTOR_INDUCT THEN REPEAT CONJ_TAC THENL [REWRITE_TAC [COPRIME_0] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_pow k z 0 = (z:A)") (fun th => ASM_REWRITE_TAC [th]) THEN REWRITE_TAC [ring_pow] THEN CONV_TAC SYM_CONV THEN ASM_MESON_TAC [RING_ORDER_EQ_1], ASM_SIMP_TAC [RING_POW_1], MAP_EVERY X_GEN_TAC [(← q r"p:num"), (← q r"m:num")] THEN REWRITE_TAC [COPRIME_LMUL] THEN STRIP_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC [MULT_SYM] THEN ASM_SIMP_TAC [(← GSYM RING_POW_POW)] THEN MATCH_MP_TAC NUMBER_FIELD_VAR_POW_SUB_1_DIVISOR_ROOT_POW THEN EXISTS_TAC (← q r"n:num") THEN ASM_SIMP_TAC [RING_POW, (← GSYM PRIME_COPRIME_EQ)]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"k:A ring"), (← q r"ring_of_int k:int->A"), (← q r"q:(1->num)->int")] MONIC_HOMOMORPHIC_IMAGE) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, FIELD_IMP_NONTRIVIAL_RING] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_of_int (k:A ring) o (q:(1->num)->int)")] POLY_ROOT_BOUND) THEN ANTS_TAC THENL [ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, (← CONJUNCT2 POLY_RING_CLAUSES)] THEN CONJ_TAC THENL [MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN EXISTS_TAC (← q r"integer_ring") THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT], MATCH_MP_TAC MONIC_IMP_NONZERO THEN ASM_SIMP_TAC [FIELD_IMP_NONTRIVIAL_RING, RING_POLYNOMIAL] THEN MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN EXISTS_TAC (← q r"integer_ring") THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT]], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN FIRST_X_ASSUM (MATCH_MP_TAC o (MATCH_MP r1)) THEN REWRITE_TAC [PHI_ALT] THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"CARD(IMAGE (\c. ring_pow k (z:A) c)
                           {c | coprime(c,n) /\ c < n})") THEN CONJ_TAC THENL [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL [REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [RING_POW_EQ_LT_EQ], MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{c:num | c < n}") THEN REWRITE_TAC [FINITE_NUMSEG_LT] THEN SET_TAC []], MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN X_GEN_TAC (← q r"c:num") THEN STRIP_TAC THEN ASM_SIMP_TAC [RING_POW] THEN REWRITE_TAC [poly_eval, (← GSYM (← MATCH_MP POLY_EXTEND_EVALUATE (← ISPEC (← q r"k:A ring") RING_HOMOMORPHISM_INTEGER_RING_OF_INT)))] THEN ASM_SIMP_TAC []])

  let NUMBER_FIELD_INTEGER_MINIMAL_POLYNOMIAL_DIVIDES ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r5 ← ARITH_RULE (← q r"b:num = c ==> a <= b ==> a <= c")
    prove
      r"!(k:A ring) z q p.
          number_field k /\ z IN ring_carrier k /\
          q IN ring_carrier(poly_ring integer_ring (:1)) /\
          monic integer_ring q /\
          poly_deg integer_ring q =
          poly_deg (subfield_generated k {ring_0 k})
            (minimal_polynomial (subfield_generated k {ring_0 k},k) I z) /\
          poly_extend (integer_ring,k) (ring_of_int k) (\v. z) q = ring_0 k /\
          p IN ring_carrier(poly_ring integer_ring (:1)) /\
          poly_extend (integer_ring,k) (ring_of_int k) (\v. z) p = ring_0 k
          ==> ring_divides (poly_ring integer_ring (:1)) q p"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"p:(1->num)->int"), (← q r"q:(1->num)->int")] POLY_DIV_REM) THEN ANTS_TAC THENL [RULE_ASSUM_TAC (REWRITE_RULE [monic]) THEN ASM_REWRITE_TAC [RING_UNIT_1], ALL_TAC] THEN MAP_EVERY ABBREV_TAC [(← q r"d = poly_div integer_ring p q"), (← q r"s = poly_rem integer_ring p q")] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"k:A ring"), (← q r"(:1)"), (← q r"ring_of_int k:int->A"), (← q r"\v:1. (z:A)")] RING_HOMOMORPHISM_POLY_EXTEND) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"poly_extend (integer_ring,k) (ring_of_int k) (\v. z)
                  (s:(1->num)->int) = ring_0(k:A ring)") ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o ((AP_TERM (← q r"poly_extend (integer_ring,k) (ring_of_int k) (\v:1. (z:A))")) o (checkM (fun th => (do let z12 ← (q r"p:(1->num)->int"); let z11 ← (do let z9 ← (do let z10 ← (pure th); pure (concl z10)); liftExcept (rand z9)); pure (z11 == z12)))))) THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_ADD th), (← MATCH_MP RING_HOMOMORPHISM_MUL th), RING_MUL, RING_MUL_RZERO, RING_ADD_LZERO, POLY_EXTEND])), ALL_TAC] THEN SUBGOAL_THEN (← q r"s = ring_0(poly_ring integer_ring (:1))") SUBST_ALL_TAC THENL [FIRST_X_ASSUM ((DISJ_CASES_THEN2 MP_TAC ACCEPT_TAC) o (checkM (fun z6 => (do let z7 ← (do let z8 ← (pure z6); pure (concl z8)); pure (is_disj z7))))) THEN ONCE_REWRITE_TAC [(← GSYM CONTRAPOS_THM)] THEN REWRITE_TAC [NOT_LT, (← CONJUNCT2 POLY_RING_CLAUSES)] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"z:A"), (← q r"ring_of_int(subfield_generated k {ring_0 k:A}) o
                      (s:(1->num)->int)")] MINIMAL_POLYNOMIAL_DEG_LE) THEN ANTS_TAC THENL [ASM_SIMP_TAC [FIELD_EXTENSION_SUBFIELD_GENERATED, NUMBER_FIELD_ALGEBRAIC] THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN EXISTS_TAC (← q r"integer_ring") THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT], MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"ring_of_int(subfield_generated k {ring_0 k:A})"), (← q r"s:(1->num)->int")] POLY_EQ_0_MONOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [RING_MONOMORPHISM_INTEGER_RING_OF_INT, RING_CHAR_SUBFIELD_GENERATED, RING_POLYNOMIAL], SIMP_TAC [POLY_EXTEND_EVALUATE, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, I_O_ID, RING_OF_INT_SUBFIELD_GENERATED] THEN ASM_REWRITE_TAC [(← GSYM (← MATCH_MP POLY_EXTEND_EVALUATE (← ISPEC (← q r"k:A ring") RING_HOMOMORPHISM_INTEGER_RING_OF_INT)))]], MATCH_MP_TAC r5 THEN MATCH_MP_TAC POLY_DEG_MONOMORPHIC_IMAGE THEN ASM_REWRITE_TAC [RING_MONOMORPHISM_INTEGER_RING_OF_INT, RING_POLYNOMIAL, RING_CHAR_SUBFIELD_GENERATED]], ALL_TAC] THEN REWRITE_TAC [ring_divides] THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"d:(1->num)->int") THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z4 ← (q r"p:(1->num)->int"); let z3 ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); liftExcept (rand z1)); pure (z3 == z4)))))) THEN ASM_SIMP_TAC [RING_ADD_RZERO, RING_MUL] THEN MATCH_MP_TAC RING_MUL_SYM THEN ASM_REWRITE_TAC [])

  let CYCLOTOMIC_POLY_MINIMAL_POLYNOMIAL ← prove
    r"!(k:A ring) z n.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = n /\ ~(n = 0)
        ==> minimal_polynomial (subfield_generated k {ring_0 k},k) I z =
            cyclotomic_poly (subfield_generated k {ring_0 k}) n"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN (← q r"poly_eval k (cyclotomic_poly k n) z = ring_0(k:A ring)") ASSUME_TAC THENL [MATCH_MP_TAC CYCLOTOMIC_POLY_ROOT THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN], ALL_TAC] THEN SUBGOAL_THEN (← q r"(z:A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM, integral_element] THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"cyclotomic_poly integer_ring n") THEN ASM_REWRITE_TAC [CYCLOTOMIC_POLY_IN_CARRIER, CYCLOTOMIC_POLY_MONIC, (← MATCH_MP POLY_EXTEND_EVALUATE (← ISPEC (← q r"k:A ring") RING_HOMOMORPHISM_INTEGER_RING_OF_INT)), (← MATCH_MP CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE (← ISPEC (← q r"k:A ring") RING_HOMOMORPHISM_INTEGER_RING_OF_INT)), (← GSYM poly_eval)], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A")] RING_OF_INTEGERS_INTEGER_MINIMAL_POLYNOMIAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"q:(1->num)->int") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num"), (← q r"q:(1->num)->int")] NUMBER_FIELD_VAR_POW_SUB_1_DIVISOR_DEG) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"q:(1->num)->int"), (← q r"poly_sub integer_ring
                     (poly_pow integer_ring (poly_var integer_ring one) n)
                     (poly_1 integer_ring)")] NUMBER_FIELD_INTEGER_MINIMAL_POLYNOMIAL_DIVIDES) THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [REWRITE_TAC [(← GSYM RING_POLYNOMIAL)] THEN SIMP_TAC [RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_POW, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_1], MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A")] RING_POW_RING_ORDER) THEN ASM_SIMP_TAC [POLY_EXTEND_INTEGER_RING_VAR_POW_SUB_1, RING_SUB_REFL, RING_1]], DISCH_TAC] THEN MATCH_MP_TAC MONIC_DIVIDES_EQ THEN EXISTS_TAC (← q r"subfield_generated k {ring_0 k:A}") THEN ASM_SIMP_TAC [MINIMAL_POLYNOMIAL_MONIC, CYCLOTOMIC_POLY_MONIC, FIELD_EXTENSION_SUBFIELD_GENERATED, NUMBER_FIELD_ALGEBRAIC] THEN CONJ_TAC THENL [ASM_SIMP_TAC [MINIMAL_POLYNOMIAL_DIVIDES, CYCLOTOMIC_POLY_IN_CARRIER, FIELD_EXTENSION_SUBFIELD_GENERATED, NUMBER_FIELD_ALGEBRAIC] THEN REWRITE_TAC [(← MATCH_MP POLY_EXTEND_EVALUATE (← ISPECL [(← q r"k:A ring"), (← q r"{ring_0 k:A}")] RING_HOMOMORPHISM_SUBFIELD_INCLUSION))] THEN ASM_REWRITE_TAC [(← MATCH_MP CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE (← ISPECL [(← q r"k:A ring"), (← q r"{ring_0 k:A}")] RING_HOMOMORPHISM_SUBFIELD_INCLUSION)), (← GSYM poly_eval)], ASM_REWRITE_TAC [CYCLOTOMIC_POLY_DEG, SUBFIELD_GENERATED] THEN ASM_SIMP_TAC [FIELD_NONTRIVIAL] THEN ASM_ARITH_TAC])

  let PHI_LE_POLY_DEG_PRIMITIVE_ROOT ← prove
    r"!(k:A ring) z n p.
        number_field k /\ z IN ring_carrier k /\ ring_order k z = n /\
        p IN ring_carrier(poly_ring (subfield_generated k {ring_0 k}) (:1)) /\
        ~(p = poly_0 k) /\ poly_eval k p z = ring_0 k
        ==> phi n <= poly_deg k p"
    (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [PHI_0, LE_0] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_0 k:A}"), (← q r"n:num")] CYCLOTOMIC_POLY_DEG) THEN ASM_SIMP_TAC [POLY_DEG_SUBFIELD_GENERATED, SUBFIELD_GENERATED, FIELD_NONTRIVIAL] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"z:A"), (← q r"p:(1->num)->A")] MINIMAL_POLYNOMIAL_DEG_LE) THEN ASM_SIMP_TAC [CYCLOTOMIC_POLY_MINIMAL_POLYNOMIAL, FIELD_EXTENSION_SUBFIELD_GENERATED, NUMBER_FIELD_ALGEBRAIC, POLY_DEG_SUBFIELD_GENERATED] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL [UNDISCH_TAC (← q r"~(p:(1->num)->A = poly_0 k)") THEN REWRITE_TAC [poly_0, poly_const, SUBFIELD_GENERATED], ASM_SIMP_TAC [POLY_EXTEND_EVALUATE, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, I_O_ID, (← GSYM poly_eval)]])

  let PHI_LE_POLY_DEG_CYCLOTOMIC_DIVISOR_ROOT ← prove
    r"!(r:A ring) (l:B ring) h n a w.
        field r /\ number_field l /\
        ring_monomorphism(subfield_generated r {ring_0 r},l) h /\
        ring_divides (poly_ring (subfield_generated r {ring_0 r}) (:1)) a
          (cyclotomic_poly (subfield_generated r {ring_0 r}) n) /\
        w IN ring_carrier l /\ poly_eval l (h o a) w = ring_0 l
        ==> phi n <= poly_deg (subfield_generated r {ring_0 r}) a"
    (REPEAT GEN_TAC THEN ABBREV_TAC (← q r"Q = subfield_generated r {ring_0 r:A}") THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [PHI_0, LE_0] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN SUBGOAL_THEN (← q r"field(Q:A ring) /\ subfield_generated Q {ring_0 Q} = Q") STRIP_ASSUME_TAC THENL [EXPAND_TAC "Q" THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, PRIME_SUBFIELD_SUBFIELD_GENERATED], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (GEN_REWRITE_RULE id [ring_divides])) THEN REWRITE_TAC [(← CONJUNCT2 POLY_RING_CLAUSES)] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"b:(1->num)->A") STRIP_ASSUME_TAC))) THEN SUBGOAL_THEN (← q r"~(a:(1->num)->A = poly_0 Q)") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN MP_TAC (← ISPECL [(← q r"Q:A ring"), (← q r"cyclotomic_poly Q n:(1->num)->A")] MONIC_IMP_NONZERO) THEN ASM_SIMP_TAC [CYCLOTOMIC_POLY_MONIC, FIELD_IMP_NONTRIVIAL_RING, RING_POLYNOMIAL, POLY_MUL_0], ALL_TAC] THEN FIRST_ASSUM (fun th => tactic_of do pure ((← do let hom ← (pure (fun t => (do pure (← MATCH_MP (← REWRITE_RULE [IMP_CONJ] t) th)))); pure (MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"w:B"), (← q r"n:num"), (← q r"(h:A->B) o (a:(1->num)->A)")] PHI_LE_POLY_DEG_PRIMITIVE_ROOT) THEN ASM_SIMP_TAC [RING_POLYNOMIAL, (← hom POLY_DEG_MONOMORPHIC_IMAGE), (← hom POLY_EQ_0_MONOMORPHIC_IMAGE)] THEN DISCH_THEN MATCH_MP_TAC)))) THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"w:B"), (← q r"n:num")] CYCLOTOMIC_POLY_ROOT_EQ) THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, NUMBER_FIELD_IMP_FIELD, RING_OF_NUM_EQ_0, DIVIDES_ZERO] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN FIRST_ASSUM (fun th => tactic_of do pure ((← do let hom ← (pure (fun t => (do pure (← MATCH_MP (← REWRITE_RULE [IMP_CONJ] t) th)))); pure (REWRITE_TAC [(← GSYM (← MATCH_MP CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE th))] THEN ASM_SIMP_TAC [(← hom POLY_COMPOSE_HOMOMORPHISM_MUL), POLY_EVAL_MUL, RING_POLYNOMIAL_IMP_POWERSERIES, RING_POLYNOMIAL, (← hom IN_RING_POLYNOMIAL_CARRIER_COMPOSE), RING_MUL_LZERO, POLY_EVAL])))), MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN EXISTS_TAC (← q r"Q:A ring") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"Q:A ring"), (← q r"l:B ring"), (← q r"ring_carrier(subfield_generated l {ring_0 l:B})"), (← q r"h:A->B")] RING_HOMOMORPHISM_INTO_SUBRING) THEN REWRITE_TAC [SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"Q:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] PRIME_SUBFIELD_MONOMORPHIC_IMAGE) THEN ASM_SIMP_TAC [SUBSET_REFL]])

  let PHI_LE_POLY_DEG_CYCLOTOMIC_DIVISOR ← prove
    r"!(r:A ring) n a.
        field r /\ ring_char r = 0 /\
        ~(poly_deg (subfield_generated r {ring_0 r}) a = 0) /\
        ring_divides (poly_ring (subfield_generated r {ring_0 r}) (:1)) a
          (cyclotomic_poly (subfield_generated r {ring_0 r}) n)
        ==> phi n <= poly_deg (subfield_generated r {ring_0 r}) a"
    (REPEAT GEN_TAC THEN ABBREV_TAC (← q r"Q = subfield_generated r {ring_0 r:A}") THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [PHI_0, LE_0] THEN SUBGOAL_THEN (← q r"field(Q:A ring) /\ number_field Q /\ ~(a = poly_0 Q) /\
    a IN ring_carrier(poly_ring Q (:1))") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [FIELD_SUBFIELD_GENERATED, NUMBER_FIELD_PRIME_SUBFIELD, POLY_DEG_0, RING_DIVIDES_IN_CARRIER], ALL_TAC] THEN ASM_CASES_TAC (← q r"?x. x IN ring_carrier Q /\ poly_eval Q a x = ring_0(Q:A ring)") THENL [FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"x:A") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"Q:A ring"), (← q r"I:A->A"), (← q r"n:num"), (← q r"a:(1->num)->A"), (← q r"x:A")] PHI_LE_POLY_DEG_CYCLOTOMIC_DIVISOR_ROOT) THEN ASM_REWRITE_TAC [I_O_ID, RING_MONOMORPHISM_I], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"Q:A ring"), (← q r"a:(1->num)->A")] KRONECKER_SIMPLE_FIELD_EXTENSION) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"l:(((1->num)->A)->bool)ring"), (← q r"h:A->((1->num)->A)->bool"), (← q r"w:((1->num)->A)->bool")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"l:(((1->num)->A)->bool)ring"), (← q r"h:A->((1->num)->A)->bool"), (← q r"n:num"), (← q r"a:(1->num)->A"), (← q r"w:((1->num)->A)->bool")] PHI_LE_POLY_DEG_CYCLOTOMIC_DIVISOR_ROOT) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_extension])) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC NUMBER_FIELD_FINITE_EXTENSION THEN MAP_EVERY EXISTS_TAC [(← q r"Q:A ring"), (← q r"h:A->((1->num)->A)->bool")] THEN MP_TAC (← ISPECL [(← q r"h:A->((1->num)->A)->bool"), (← q r"Q:A ring"), (← q r"l:(((1->num)->A)->bool)ring"), (← q r"w:((1->num)->A)->bool")] FINITE_SIMPLE_ALGEBRAIC_EXTENSION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [algebraic_over] THEN EXISTS_TAC (← q r"a:(1->num)->A") THEN ASM_SIMP_TAC [POLY_EXTEND_EVALUATE, (← GSYM poly_eval), POLY_RING_CLAUSES, RING_MONOMORPHISM_IMP_HOMOMORPHISM])

  let CYCLOTOMIC_POLY_IRREDUCIBLE_PRIME_SUBFIELD ← prove
    r"!(r:A ring) n.
        field r /\ ring_char r = 0 /\ ~(n = 0)
        ==> ring_irreducible (poly_ring (subfield_generated r {ring_0 r}) (:1))
              (cyclotomic_poly (subfield_generated r {ring_0 r}) n)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"n:num")] PHI_LE_POLY_DEG_CYCLOTOMIC_DIVISOR) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"Q = subfield_generated r {ring_0 r:A}") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"field(Q:A ring)") ASSUME_TAC THENL [EXPAND_TAC "Q" THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"poly_deg (Q:A ring) (cyclotomic_poly Q n) = phi n") ASSUME_TAC THENL [ASM_SIMP_TAC [CYCLOTOMIC_POLY_DEG, FIELD_NONTRIVIAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(cyclotomic_poly Q n = poly_0(Q:A ring))") ASSUME_TAC THENL [MATCH_MP_TAC MONIC_IMP_NONZERO THEN ASM_SIMP_TAC [CYCLOTOMIC_POLY_MONIC, FIELD_IMP_NONTRIVIAL_RING, RING_POLYNOMIAL, CYCLOTOMIC_POLY_IN_CARRIER], ALL_TAC] THEN ASM_REWRITE_TAC [ring_irreducible, CYCLOTOMIC_POLY_IN_CARRIER, (← CONJUNCT2 POLY_RING_CLAUSES)] THEN CONJ_TAC THENL [DISCH_THEN (MP_TAC o ((MATCH_MP POLY_DEG_UNIT) o (CONJ (← MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN (← ASSUME (← q r"field(Q:A ring)")))))) THEN ASM_REWRITE_TAC [PHI_EQ_0], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"a:(1->num)->A"), (← q r"b:(1->num)->A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"~(a:(1->num)->A = poly_0 Q) /\ ~(b:(1->num)->A = poly_0 Q)") STRIP_ASSUME_TAC THENL [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~(cyclotomic_poly Q n = poly_0(Q:A ring))") THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [POLY_MUL_0, RING_POLYNOMIAL], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"Q:A ring"), (← q r"a:(1->num)->A"), (← q r"b:(1->num)->A")] POLY_DEG_MUL) THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, RING_POLYNOMIAL] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"Q:A ring"), (← q r"b:(1->num)->A")] FIELD_POLY_DEG_EQ_0) THEN MP_TAC (← ISPECL [(← q r"Q:A ring"), (← q r"a:(1->num)->A")] FIELD_POLY_DEG_EQ_0) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_CASES_TAC (← q r"poly_deg Q (a:(1->num)->A) = 0") THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"a:(1->num)->A"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [ring_divides, CYCLOTOMIC_POLY_IN_CARRIER] THEN EXISTS_TAC (← q r"b:(1->num)->A") THEN ASM_REWRITE_TAC [POLY_RING_CLAUSES], ASM_ARITH_TAC])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_FINITE_EXTENSION, POLY_EXTEND_INTEGER_RING_HOMOMORPHIC_IMAGE,
           POLY_EXTEND_INTEGER_RING_VAR_POW_SUB_1, RING_UNIT_POLY_DIVIDES_MONIC,
           POLY_VAR_POW_SUB_1_COMMON_ROOT, POLY_VAR_POW_SUB_1_FROBENIUS_ROOT,
           NUMBER_FIELD_VAR_POW_SUB_1_FROBENIUS_ROOT,
           NUMBER_FIELD_VAR_POW_SUB_1_DIVISOR_ROOT_POW,
           NUMBER_FIELD_VAR_POW_SUB_1_DIVISOR_DEG,
           NUMBER_FIELD_INTEGER_MINIMAL_POLYNOMIAL_DIVIDES,
           CYCLOTOMIC_POLY_MINIMAL_POLYNOMIAL, PHI_LE_POLY_DEG_PRIMITIVE_ROOT,
           PHI_LE_POLY_DEG_CYCLOTOMIC_DIVISOR_ROOT, PHI_LE_POLY_DEG_CYCLOTOMIC_DIVISOR,
           CYCLOTOMIC_POLY_IRREDUCIBLE_PRIME_SUBFIELD }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- cyclotomic_field.ml phrases from line 794 to 880                       -/
/- ---------------------------------------------------------------------- -/

structure CyclotomicField02 where
  -- @@FIELDS
  CYCLOTOMIC_POLY_IRREDUCIBLE : thm
  CYCLOTOMIC_FIELD_DEGREE : thm
  CYCLOTOMIC_FIELD_FREE_BASIS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupCyclotomicField02 [HolBase] (D : CyclotomicFieldDeps) (BCyclotomicField01 : CyclotomicField01) :
    ExceptT String IO CyclotomicField02 := do
  -- @@SCOPE BEGIN
  let { INT_ARITH_TAC, .. } := D
  let { CYCLOTOMIC_POLY_DEG, CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE,
        CYCLOTOMIC_POLY_IN_CARRIER, CYCLOTOMIC_POLY_MONIC, EXTENSION_DEGREE_SIMPLE,
        FIELD_EXTENSION_SUBFIELD_GENERATED, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_NONTRIVIAL, FIELD_REAL_RING, FIELD_SUBFIELD_GENERATED, IMP_CONJ,
        INTEGER_RING, IN_RING_POLYNOMIAL_CARRIER_COMPOSE, MONIC_IMP_NONZERO, MONO_OR,
        NUMBER_FIELD_ALGEBRAIC, NUMBER_FIELD_FREE_BASIS_POWERS, NUMBER_FIELD_IMP_FIELD,
        POLY_COMPOSE_HOMOMORPHISM_MUL, POLY_DEG_MONOMORPHIC_IMAGE, POLY_DEG_UNIT,
        POLY_MUL_SYM, POLY_RING_CLAUSES, .. } := D.core1
  let { REAL_RING_CHAR, RING_CHAR_SUBFIELD_GENERATED,
        RING_HOMOMORPHISM_INTEGER_RING_OF_INT, RING_HOMOMORPHISM_POLY_RINGS,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MONOMORPHISM_INTEGER_RING_OF_INT,
        RING_POLYNOMIAL, RING_POLYNOMIAL_IMP_POWERSERIES, RING_UNIT_HOMOMORPHIC_IMAGE,
        SUBFIELD_GENERATED, SUBFIELD_GENERATED_SING_ALGEBRAIC, TRIVIAL_RING_10,
        ring_divides, ring_irreducible, .. } := D.core2
  let { CYCLOTOMIC_POLY_IRREDUCIBLE_PRIME_SUBFIELD, CYCLOTOMIC_POLY_MINIMAL_POLYNOMIAL,
        RING_UNIT_POLY_DIVIDES_MONIC, .. } := BCyclotomicField01
  -- @@SCOPE END

  let CYCLOTOMIC_POLY_IRREDUCIBLE ← prove
    r"!n. ~(n = 0)
       ==> ring_irreducible (poly_ring integer_ring (:1))
             (cyclotomic_poly integer_ring n)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"real_ring"), (← q r"n:num")] CYCLOTOMIC_POLY_IRREDUCIBLE_PRIME_SUBFIELD) THEN ASM_REWRITE_TAC [FIELD_REAL_RING, REAL_RING_CHAR] THEN ABBREV_TAC (← q r"Q = subfield_generated real_ring {ring_0 real_ring}") THEN SUBGOAL_THEN (← q r"field(Q:real ring) /\ ring_monomorphism(integer_ring,Q) (ring_of_int Q)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "Q" THEN SIMP_TAC [FIELD_SUBFIELD_GENERATED, FIELD_REAL_RING, REAL_RING_CHAR, RING_MONOMORPHISM_INTEGER_RING_OF_INT, RING_CHAR_SUBFIELD_GENERATED], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN REWRITE_TAC [(← GSYM (← MATCH_MP CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE (← ISPEC (← q r"Q:real ring") RING_HOMOMORPHISM_INTEGER_RING_OF_INT)))] THEN REWRITE_TAC [ring_irreducible, CYCLOTOMIC_POLY_IN_CARRIER, (← CONJUNCT2 POLY_RING_CLAUSES)] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC MONIC_IMP_NONZERO THEN REWRITE_TAC [CYCLOTOMIC_POLY_MONIC, RING_POLYNOMIAL, CYCLOTOMIC_POLY_IN_CARRIER, TRIVIAL_RING_10, INTEGER_RING] THEN INT_ARITH_TAC, DISCH_TAC THEN UNDISCH_TAC (← q r"~ring_unit (poly_ring (Q:real ring) (:1))
                  (ring_of_int Q o cyclotomic_poly integer_ring n)") THEN REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"poly_ring integer_ring (:1)"), (← q r"poly_ring (Q:real ring) (:1)"), (← q r"\p:(1->num)->int. ring_of_int (Q:real ring) o p"), (← q r"cyclotomic_poly integer_ring n")] RING_UNIT_HOMOMORPHIC_IMAGE) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_POLY_RINGS], MAP_EVERY X_GEN_TAC [(← q r"a:(1->num)->int"), (← q r"b:(1->num)->int")] THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPECL [(← q r"ring_of_int (Q:real ring) o (a:(1->num)->int)"), (← q r"ring_of_int (Q:real ring) o (b:(1->num)->int)")])) THEN FIRST_ASSUM (fun th => tactic_of do pure ((← do let hom ← (pure (fun t => (do pure (← MATCH_MP (← REWRITE_RULE [IMP_CONJ] t) th)))); pure (ASM_SIMP_TAC [(← hom IN_RING_POLYNOMIAL_CARRIER_COMPOSE)] THEN ANTS_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [(← hom POLY_COMPOSE_HOMOMORPHISM_MUL), RING_POLYNOMIAL_IMP_POWERSERIES, RING_POLYNOMIAL], ALL_TAC])))) THEN MATCH_MP_TAC MONO_OR THEN CONJ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC RING_UNIT_POLY_DIVIDES_MONIC THEN EXISTS_TAC (← q r"cyclotomic_poly integer_ring n") THEN FIRST_X_ASSUM (MP_TAC o ((MATCH_MP POLY_DEG_UNIT) o (CONJ (← MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN (← ASSUME (← q r"field(Q:real ring)")))))) THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [RING_POLYNOMIAL, (← MATCH_MP (← REWRITE_RULE [IMP_CONJ] POLY_DEG_MONOMORPHIC_IMAGE) th)])) THEN DISCH_TAC THEN ASM_REWRITE_TAC [CYCLOTOMIC_POLY_MONIC, ring_divides, CYCLOTOMIC_POLY_IN_CARRIER, (← CONJUNCT2 POLY_RING_CLAUSES)] THENL [EXISTS_TAC (← q r"b:(1->num)->int"), EXISTS_TAC (← q r"a:(1->num)->int")] THEN ASM_SIMP_TAC [POLY_MUL_SYM, RING_POLYNOMIAL_IMP_POWERSERIES, RING_POLYNOMIAL]])

  let CYCLOTOMIC_FIELD_DEGREE ← prove
    r"!(k:A ring) z n.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = n /\ ~(n = 0) /\ subfield_generated k {z} = k
        ==> extension_degree (subfield_generated k {ring_0 k},k) I = phi n"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"z:A")] EXTENSION_DEGREE_SIMPLE) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A")] SUBFIELD_GENERATED_SING_ALGEBRAIC) THEN ASM_SIMP_TAC [FIELD_EXTENSION_SUBFIELD_GENERATED, NUMBER_FIELD_ALGEBRAIC, NUMBER_FIELD_IMP_FIELD] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [CYCLOTOMIC_POLY_MINIMAL_POLYNOMIAL, CYCLOTOMIC_POLY_DEG, SUBFIELD_GENERATED, FIELD_NONTRIVIAL, NUMBER_FIELD_IMP_FIELD])

  let CYCLOTOMIC_FIELD_FREE_BASIS ← prove
    r"!(k:A ring) z n.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = n /\ ~(n = 0) /\ subfield_generated k {z} = k
        ==> free_basis (subfield_generated k {ring_0 k},k) I (phi n)
                       (\i. ring_pow k z i)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A")] NUMBER_FIELD_FREE_BASIS_POWERS) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num")] CYCLOTOMIC_FIELD_DEGREE) THEN ASM_SIMP_TAC [CYCLOTOMIC_POLY_MINIMAL_POLYNOMIAL, CYCLOTOMIC_POLY_DEG, SUBFIELD_GENERATED, FIELD_NONTRIVIAL, NUMBER_FIELD_IMP_FIELD])

  -- @@RETURN BEGIN
  return { CYCLOTOMIC_POLY_IRREDUCIBLE, CYCLOTOMIC_FIELD_DEGREE,
           CYCLOTOMIC_FIELD_FREE_BASIS }
  -- @@RETURN END

end HolANT.CyclotomicField
