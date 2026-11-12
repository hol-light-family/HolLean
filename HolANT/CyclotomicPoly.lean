/- ========================================================================= -/
/- ANT: Cyclotomic polynomials over an arbitrary ring                      -/
/- ========================================================================= -/
/- File: HolANT/CyclotomicPoly.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/cyclotomic_poly.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antcyclotomicpolydiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/frag.ml, Library/grouptheory.ml, Library/symmetric_group.ml, Library/galois.ml, Library/ring_groups.ml, Library/finite_fields.ml, Library/integer.ml, Library/isum.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.CyclotomicPoly fills them).

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
import HolLibrary.RingGroups
import HolLibrary.FiniteFields
import HolLibrary.Integer
import HolLibrary.Isum
import HolLibrary.Products
import HolLibrary.Multiplicative
import HolLibrary.Primitive

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude

namespace HolANT.CyclotomicPoly

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD1 ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH ARITH_EQ BEZOUT_GCD_STRONG CARD_EQ_0
   CARD_NUMSEG_LT COEFF COEFF_IN_CARRIER_ALT COEFF_POLY_0 COEFF_POLY_1
   COEFF_POLY_SUB COEFF_POLY_VARPOW COPRIME_0 COPRIME_GCD DE_MORGAN_THM DISJOINT
   DISJ_SYM DIVIDES_0 DIVIDES_1 DIVIDES_ANTISYM DIVIDES_EXP_LE_IMP DIVIDES_LE
   DIVIDES_LMUL DIVIDES_LMUL2_EQ DIVIDES_MUL2 DIVIDES_ONE DIVIDES_PRIMEPOW
   DIVIDES_PRIME_PRIME DIVIDES_REFL DIVIDES_REXP DIVIDES_RMUL DIVIDES_TRANS
   DIVIDES_ZERO DIVISION_DECOMP DIV_1 EMPTY_GSPEC EQ_MULT_LCANCEL EQ_PRIMEPOW
   EQ_TRANS EXP EXP_EQ_0 EXTENSION FIELD_IMP_INTEGRAL_DOMAIN
   FIELD_IMP_NONTRIVIAL_RING FIELD_MONIC_IRREDUCIBLE_ASSOCIATE FINITE_DELETE
   FINITE_DIVISORS FINITE_FIELD_IRREDUCIBLE_ROOT_POW FINITE_IMAGE FINITE_NUMSEG
   FINITE_NUMSEG_LT FINITE_RESTRICT FINITE_SUBSET FORALL_IN_IMAGE FUN_EQ_THM GCD
   GCD_SYM GCD_ZERO IMP_CONJ IMP_IMP INDEX_DECOMPOSITION_PRIME INTEGER_RING
   INTEGER_RING_OF_NUM INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING
   INTEGRAL_DOMAIN_INTEGER_RING INTEGRAL_DOMAIN_NONTRIVIAL
   INTEGRAL_DOMAIN_POLY_RING INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE
   INTEGRAL_DOMAIN_PRODUCT_EQ_0 INTEGRAL_DOMAIN_REGULAR INT_EQ_MUL_RCANCEL
   INT_MUL_LID INT_OF_NUM_EQ IN_DELETE IN_ELIM_THM IN_IMAGE IN_INSERT IN_INTER
   IN_NUMSEG IN_RING_POLYNOMIAL_CARRIER_COMPOSE IN_SING IN_UNION
   IRREDUCIBLE_IMP_POLY_DEG_NZ LE LEFT_IMP_EXISTS_THM LET_TRANS LE_ANTISYM
   LE_EXP LE_REFL LT_LE LT_MULT_LCANCEL LT_REFL MEMBER_NOT_EMPTY
   MONIC_ASSOCIATES_EQ MONIC_IMP_NONZERO MONIC_IN_TRIVIAL_RING MONIC_POLY_1
   MONIC_POLY_EQ_ROOTS_PRODUCT MONIC_POLY_POW MONIC_POLY_PRODUCT MULT_ASSOC
   MULT_CLAUSES MULT_EQ_0 MULT_SYM NOT_EXISTS_THM NOT_IN_EMPTY NOT_LT
   NSUM_CLAUSES NSUM_CONST NSUM_EQ NUMSEG_LT ORDER_DIVIDES PHI_0 PHI_1 PHI_ALT
   PHI_DIVISORSUM PHI_PRIMEPOW_SUC PID_IMP_UFD PID_POLY_RING POLY_CLAUSES
   POLY_COMPOSE_HOMOMORPHISM_CONST POLY_COMPOSE_HOMOMORPHISM_POW
   POLY_COMPOSE_HOMOMORPHISM_SUB POLY_COMPOSE_HOMOMORPHISM_VAR POLY_CONST
   POLY_CONST_DIVIDES_COEFFS_EQ POLY_CONST_EQ_0 POLY_DEG_0 POLY_DEG_1
   POLY_DEG_CONST POLY_DEG_DIVIDES_LE POLY_DEG_EQ_0 POLY_DEG_MONOMORPHIC_IMAGE
   POLY_DEG_PRODUCT_MONIC POLY_DEG_RMUL_MONIC POLY_DEG_SUB_CONST
   POLY_DEG_VAR_POW POLY_DERIV_1 POLY_DERIV_SUB POLY_DERIV_VAR_POW POLY_DIV
   POLY_DIVIDES_X_MINUS_ROOT POLY_DIVIDES_X_MINUS_ROOT_EQ POLY_DIV_REM_SIMP : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (POLY_EVAL POLY_EVAL_1 POLY_EVAL_HOMOMORPHIC_IMAGE POLY_EVAL_MUL POLY_EVAL_POW
   POLY_EVAL_RING_PRODUCT POLY_EVAL_RING_SUM POLY_EVAL_SUB POLY_EVAL_VAR
   POLY_MUL_0 POLY_MUL_LEADING_COEFF POLY_REM_UNIQUE POLY_RING_CLAUSES
   POLY_SEPARABLE_IMP_SQUAREFREE POLY_TOP_NONZERO POLY_VAR_UNIV
   POLY_X_MINUS_A_IN_CARRIER PRIME_COPRIME_EQ PRIME_DIVEXP PRIME_FACTOR
   PRIME_IMP_NZ RIGHT_EXISTS_IMP_THM RING_0 RING_1 RING_ADD_RZERO
   RING_ASSOCIATES_PRODUCT RING_ASSOCIATES_SYM RING_ASSOCIATES_TRANS
   RING_CHAR_DIVIDES_ORDER RING_CHAR_EQ_1 RING_CHAR_MONOMORPHIC_IMAGE
   RING_CHAR_POLY_RING RING_COPRIME_PRODUCT_DIVIDES RING_COPRIME_SYM
   RING_DIVIDES_0 RING_DIVIDES_IN_CARRIER RING_DIVIDES_IRREDUCIBLE_ROOT
   RING_DIVIDES_LMUL RING_DIVIDES_MUL2 RING_DIVIDES_PRODUCT_SUBSET
   RING_DIVIDES_REFL RING_DIVIDES_RMUL RING_DIVIDES_SUB RING_DIVIDES_SUB_POW
   RING_DIVIDES_TRANS RING_ENDOMORPHISM_FROBENIUS_ITERATE RING_GEOM_SERIES
   RING_HOMOMORPHISM_1 RING_HOMOMORPHISM_INTEGER_RING_OF_INT
   RING_HOMOMORPHISM_MUL RING_HOMOMORPHISM_POLY_RINGS RING_HOMOMORPHISM_PRODUCT
   RING_HOMOMORPHISM_RING_OF_INT RING_HOMOMORPHISM_SUB
   RING_IRREDUCIBLE_IN_CARRIER RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_MUL
   RING_MUL_LCANCEL RING_MUL_RCANCEL RING_MUL_RID RING_MUL_RZERO RING_MUL_SYM
   RING_NEG RING_OF_NUM RING_OF_NUM_0 RING_OF_NUM_EQ_0 RING_ORDER_0
   RING_ORDER_POW_GEN RING_POLYNOMIAL RING_POLYNOMIAL_1
   RING_POLYNOMIAL_IMP_POWERSERIES RING_POLYNOMIAL_POW RING_POLYNOMIAL_SUB
   RING_POLYNOMIAL_VAR RING_POW RING_POWERSERIES_CONST RING_POWERSERIES_POW
   RING_POWERSERIES_VAR RING_POW_1 RING_POW_2 RING_POW_ADD RING_POW_EQ
   RING_POW_EQ_1 RING_POW_EQ_LT_EQ RING_POW_ONE RING_POW_POW RING_POW_ZERO
   RING_PRODUCT RING_PRODUCT_CLAUSES RING_PRODUCT_CONST RING_PRODUCT_DELTA
   RING_PRODUCT_EQ RING_PRODUCT_IMAGE RING_PRODUCT_IMAGE_GEN RING_PRODUCT_POW
   RING_PRODUCT_SING RING_PRODUCT_UNION RING_PRODUCT_ZERO
   RING_SQUAREFREE_DIVISOR RING_SQUAREFREE_POW RING_SUB RING_SUB_EQ_0
   RING_SUB_LZERO RING_SUB_REFL RING_SUB_RZERO RING_SUM RING_SUM_CONST
   RING_UNIT_1 RING_UNIT_DIVIDES RING_UNIT_IMP_REGULAR RING_UNIT_POLY_CONST
   RING_UNIT_X_MINUS_A SING_SUBSET SKOLEM_THM SUBSET TRIVIAL_RING_10
   TRIVIAL_RING_POLY_0 UFD_EQ_PRIMEFACT UFD_INTEGER_RING UFD_POLY_RING WF_REC
   WF_num algebraic_extension algebraically_closed_field divides field_extension
   monic num_CASES num_WF o_ASSOC o_DEF o_THM pairwise poly_1 poly_separable
   ring_coprime ring_divides ring_endomorphism ring_irreducible ring_of_num
   ring_pow ring_regular ring_squarefree ring_zerodivisor : thm)
  deriving Inhabited

/-- What cyclotomic_poly.ml uses from Session besides theorems. -/
structure CyclotomicPolyDeps where
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
  new_specification : List String → thm → ExceptT String IO thm
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
/- cyclotomic_poly.ml phrases from line 88 to 785                         -/
/- ---------------------------------------------------------------------- -/

structure CyclotomicPoly01 where
  -- @@FIELDS
  cyclotomic_poly : thm
  RING_REGULAR_POLY_UNIT_LEADING : thm
  POLY_DIV_MUL : thm
  MONIC_POLY_MUL_EQ : thm
  POLY_DEG_VAR_POW_SUB_1 : thm
  MONIC_POLY_VAR_POW_SUB_1 : thm
  POLY_DERIV_VAR_POW_SUB_1 : thm
  POLY_SEPARABLE_VAR_POW_SUB_1 : thm
  RING_DIVIDES_POW_SUB_1 : thm
  POLY_VAR_POW_SUB_1_HOMOMORPHIC_IMAGE : thm
  FINITE_DIVISORS_LT : thm
  DIVISORS_INSERT_LT : thm
  RING_PRODUCT_DIVISORS : thm
  CYCLOTOMIC_POLY_0 : thm
  CYCLOTOMIC_POLY_IN_CARRIER : thm
  CYCLOTOMIC_POLY_1 : thm
  CYCLOTOMIC_POLY_UNIQUE : thm
  CYCLOTOMIC_POLY_INTEGER_PRODUCT : thm
  CYCLOTOMIC_POLY_RING_OF_INT : thm
  CYCLOTOMIC_POLY_MONIC : thm
  CYCLOTOMIC_POLY_PRODUCT : thm
  CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE : thm
  CYCLOTOMIC_POLY_DEG : thm
  CYCLOTOMIC_POLY_ROOT : thm
  CYCLOTOMIC_POLY_ROOT_EQ : thm
  POLY_VAR_POW_SUB_1_PRODUCT : thm
  CYCLOTOMIC_POLY_SPLITS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupCyclotomicPoly01 [HolBase] (D : CyclotomicPolyDeps) :
    ExceptT String IO CyclotomicPoly01 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, MESON_TAC, NUMBER_RULE, RING_RULE, SET_TAC, TAUT,
        new_specification, .. } := D
  let { ARITH_EQ, BEZOUT_GCD_STRONG, CARD_NUMSEG_LT, COEFF, COEFF_IN_CARRIER_ALT,
        COEFF_POLY_0, COEFF_POLY_1, COEFF_POLY_SUB, COEFF_POLY_VARPOW, COPRIME_0,
        COPRIME_GCD, DISJ_SYM, DIVIDES_ANTISYM, DIVIDES_LE, DIVIDES_ONE, DIVIDES_REFL,
        DIVIDES_TRANS, DIVIDES_ZERO, DIV_1, EMPTY_GSPEC, EXTENSION, FINITE_DIVISORS,
        FINITE_NUMSEG_LT, FINITE_SUBSET, FUN_EQ_THM, GCD, GCD_SYM, GCD_ZERO,
        INTEGER_RING, INTEGER_RING_OF_NUM, INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING,
        INTEGRAL_DOMAIN_INTEGER_RING, INTEGRAL_DOMAIN_NONTRIVIAL,
        INTEGRAL_DOMAIN_PRODUCT_EQ_0, INT_OF_NUM_EQ, IN_ELIM_THM, IN_INSERT,
        IN_RING_POLYNOMIAL_CARRIER_COMPOSE, LE, LEFT_IMP_EXISTS_THM, LET_TRANS,
        LE_ANTISYM, LT_LE, LT_REFL, MONIC_IN_TRIVIAL_RING, MONIC_POLY_1,
        MONIC_POLY_EQ_ROOTS_PRODUCT, MONIC_POLY_PRODUCT, MULT_CLAUSES, NOT_EXISTS_THM,
        NOT_LT, NSUM_CLAUSES, NSUM_EQ, PHI_0, PHI_ALT, PHI_DIVISORSUM, POLY_CLAUSES,
        POLY_COMPOSE_HOMOMORPHISM_CONST, POLY_COMPOSE_HOMOMORPHISM_POW,
        POLY_COMPOSE_HOMOMORPHISM_SUB, POLY_COMPOSE_HOMOMORPHISM_VAR, POLY_CONST,
        POLY_CONST_DIVIDES_COEFFS_EQ, POLY_CONST_EQ_0, POLY_DEG_0, POLY_DEG_1,
        POLY_DEG_CONST, POLY_DEG_DIVIDES_LE, POLY_DEG_EQ_0, POLY_DEG_PRODUCT_MONIC,
        POLY_DEG_RMUL_MONIC, POLY_DEG_SUB_CONST, POLY_DEG_VAR_POW, POLY_DERIV_1,
        POLY_DERIV_SUB, POLY_DERIV_VAR_POW, POLY_DIV, POLY_DIVIDES_X_MINUS_ROOT,
        POLY_DIVIDES_X_MINUS_ROOT_EQ, POLY_DIV_REM_SIMP, .. } := D.core1
  let { POLY_EVAL_1, POLY_EVAL_POW, POLY_EVAL_RING_PRODUCT, POLY_EVAL_SUB,
        POLY_EVAL_VAR, POLY_MUL_0, POLY_MUL_LEADING_COEFF, POLY_REM_UNIQUE,
        POLY_RING_CLAUSES, POLY_SEPARABLE_IMP_SQUAREFREE, POLY_TOP_NONZERO,
        POLY_VAR_UNIV, POLY_X_MINUS_A_IN_CARRIER, RING_0, RING_1, RING_ADD_RZERO,
        RING_COPRIME_PRODUCT_DIVIDES, RING_COPRIME_SYM, RING_DIVIDES_0,
        RING_DIVIDES_IN_CARRIER, RING_DIVIDES_LMUL, RING_DIVIDES_MUL2,
        RING_DIVIDES_PRODUCT_SUBSET, RING_DIVIDES_REFL, RING_DIVIDES_RMUL,
        RING_DIVIDES_SUB, RING_DIVIDES_SUB_POW, RING_DIVIDES_TRANS,
        RING_HOMOMORPHISM_1, RING_HOMOMORPHISM_INTEGER_RING_OF_INT,
        RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_POLY_RINGS, RING_HOMOMORPHISM_PRODUCT,
        RING_HOMOMORPHISM_RING_OF_INT, RING_MUL, RING_MUL_LCANCEL, RING_MUL_RCANCEL,
        RING_MUL_RID, RING_MUL_RZERO, RING_MUL_SYM, RING_OF_NUM, RING_ORDER_POW_GEN,
        RING_POLYNOMIAL, RING_POLYNOMIAL_1, RING_POLYNOMIAL_IMP_POWERSERIES,
        RING_POLYNOMIAL_POW, RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_VAR, RING_POW,
        RING_POWERSERIES_CONST, RING_POWERSERIES_POW, RING_POWERSERIES_VAR, RING_POW_1,
        RING_POW_2, RING_POW_ADD, RING_POW_EQ_1, RING_POW_EQ_LT_EQ, RING_POW_ONE,
        RING_POW_POW, RING_PRODUCT, RING_PRODUCT_CLAUSES, RING_PRODUCT_EQ,
        RING_PRODUCT_SING, RING_PRODUCT_ZERO, RING_SUB, RING_SUB_EQ_0, RING_SUB_REFL,
        RING_SUB_RZERO, RING_UNIT_1, RING_UNIT_DIVIDES, RING_UNIT_IMP_REGULAR,
        RING_UNIT_POLY_CONST, RING_UNIT_X_MINUS_A, SING_SUBSET, SKOLEM_THM, SUBSET,
        TRIVIAL_RING_10, TRIVIAL_RING_POLY_0, UFD_INTEGER_RING, UFD_POLY_RING, WF_REC,
        WF_num, divides, monic, num_WF, o_ASSOC, o_THM, pairwise, poly_1,
        poly_separable, ring_coprime, ring_divides, ring_of_num, ring_pow,
        ring_regular, ring_squarefree, ring_zerodivisor, .. } := D.core2
  -- @@SCOPE END

  let cyclotomic_poly ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let v1 ← MATCH_MP WF_REC WF_num
    let v2 ← GSYM SKOLEM_THM
    let p3 ← prove r"?cp. !(r:A ring) n.
        cp r n =
        if n = 0 then poly_1 r
        else poly_div r
               (poly_sub r (poly_pow r (poly_var r one) n) (poly_1 r))
               (ring_product (poly_ring r (:1)) {d | d divides n /\ d < n}
                             (cp r))" (REWRITE_TAC [v2] THEN GEN_TAC THEN MATCH_MP_TAC v1 THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [] THEN AP_TERM_TAC THEN MATCH_MP_TAC RING_PRODUCT_EQ THEN ASM_SIMP_TAC [IN_ELIM_THM])
    let th := p3
    new_specification ["cyclotomic_poly"] th

  let RING_REGULAR_POLY_UNIT_LEADING ← prove
    r"!(r:A ring) p.
        p IN ring_carrier(poly_ring r (:1)) /\
        ring_unit r (coeff (poly_deg r p) p)
        ==> ring_regular (poly_ring r (:1)) p"
    (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [ring_regular, ring_zerodivisor, NOT_EXISTS_THM] THEN X_GEN_TAC (← q r"x:(1->num)->A") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"x:(1->num)->A")] POLY_TOP_NONZERO) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"coeff (poly_deg r p) (p:(1->num)->A)")] RING_MUL_LCANCEL) THEN RULE_ASSUM_TAC (REWRITE_RULE [(← GSYM RING_POLYNOMIAL)]) THEN ASM_SIMP_TAC [RING_UNIT_IMP_REGULAR, COEFF_IN_CARRIER_ALT, RING_0] THEN ASM_SIMP_TAC [(← GSYM POLY_MUL_LEADING_COEFF), RING_MUL_RZERO, COEFF_IN_CARRIER_ALT] THEN RULE_ASSUM_TAC (REWRITE_RULE [POLY_RING_CLAUSES]) THEN ASM_REWRITE_TAC [COEFF_POLY_0])

  let POLY_DIV_MUL ← prove
    r"!(r:A ring) p d.
        p IN ring_carrier(poly_ring r (:1)) /\
        d IN ring_carrier(poly_ring r (:1)) /\
        ring_unit r (coeff (poly_deg r d) d)
        ==> poly_div r (ring_mul (poly_ring r (:1)) p d) d = p"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC (← ISPECL [(← q r"poly_ring (r:A ring) (:1)"), (← q r"d:(1->num)->A")] RING_MUL_RCANCEL) THEN ASM_SIMP_TAC [POLY_DIV, RING_MUL, RING_REGULAR_POLY_UNIT_LEADING] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ring_mul (poly_ring r (:1)) p d:(1->num)->A"), (← q r"d:(1->num)->A")] POLY_DIV_REM_SIMP) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ring_mul (poly_ring r (:1)) p d:(1->num)->A"), (← q r"d:(1->num)->A"), (← q r"ring_0(poly_ring r (:1)):(1->num)->A")] POLY_REM_UNIQUE) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ring_mul (poly_ring r (:1)) p d:(1->num)->A"), (← q r"d:(1->num)->A")] POLY_DIV) THEN ASM_SIMP_TAC [RING_MUL, RING_0, RING_SUB_RZERO, RING_DIVIDES_LMUL, RING_DIVIDES_REFL, RING_ADD_RZERO])

  let MONIC_POLY_MUL_EQ ← prove
    r"!r p q:(1->num)->A.
        ring_polynomial r p /\ ring_polynomial r q /\ monic r q
        ==> (monic r (poly_mul r p q) <=> monic r p)"
    (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"p:(1->num)->A = poly_0 r") THEN ASM_SIMP_TAC [POLY_MUL_0] THEN REWRITE_TAC [monic] THEN ASM_SIMP_TAC [POLY_DEG_RMUL_MONIC, POLY_MUL_LEADING_COEFF] THEN RULE_ASSUM_TAC (REWRITE_RULE [monic]) THEN ASM_SIMP_TAC [RING_MUL_RID, COEFF_IN_CARRIER_ALT])

  let POLY_DEG_VAR_POW_SUB_1 ← prove
    r"!(r:A ring) n.
        poly_deg r (poly_sub r (poly_pow r (poly_var r one) n) (poly_1 r)) =
        if ring_1 r = ring_0 r then 0 else n"
    (SIMP_TAC [poly_1, POLY_DEG_SUB_CONST, RING_POLYNOMIAL_POW, RING_POLYNOMIAL_VAR, RING_1, POLY_DEG_VAR_POW])

  let MONIC_POLY_VAR_POW_SUB_1 ← prove
    r"!(r:A ring) n.
        ~(n = 0)
        ==> monic r (poly_sub r (poly_pow r (poly_var r one) n) (poly_1 r))"
    (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"trivial_ring(r:A ring)") THENL [MATCH_MP_TAC MONIC_IN_TRIVIAL_RING THEN ASM_SIMP_TAC [RING_POLYNOMIAL_IMP_POWERSERIES, RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_POW, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_1], RULE_ASSUM_TAC (REWRITE_RULE [TRIVIAL_RING_10]) THEN ASM_REWRITE_TAC [monic, POLY_DEG_VAR_POW_SUB_1] THEN ASM_SIMP_TAC [COEFF_POLY_SUB, COEFF_POLY_VARPOW, COEFF_POLY_1, RING_SUB_RZERO, RING_1]])

  let POLY_DERIV_VAR_POW_SUB_1 ← prove
    r"!(r:A ring) n.
        poly_deriv r (poly_sub r (poly_pow r (poly_var r one) n) (poly_1 r)) =
        poly_mul r (poly_const r (ring_of_num r n))
                   (poly_pow r (poly_var r one) (n - 1))"
    (SIMP_TAC [POLY_DERIV_SUB, RING_POLYNOMIAL_IMP_POWERSERIES, RING_POLYNOMIAL_POW, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_1, POLY_DERIV_VAR_POW, POLY_DERIV_1] THEN REWRITE_TAC [POLY_CLAUSES] THEN SIMP_TAC [RING_SUB_RZERO, RING_MUL, POLY_CONST, RING_OF_NUM, RING_POW, POLY_VAR_UNIV])

  let POLY_SEPARABLE_VAR_POW_SUB_1 ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!R c x y:B.
         c IN ring_carrier R /\ x IN ring_carrier R /\ y IN ring_carrier R
         ==> c = ring_sub R (ring_mul R x (ring_mul R c y))
                   (ring_mul R c
                     (ring_sub R (ring_mul R x y) (ring_1 R)))")
    let r2 ← ARITH_RULE (← q r"~(n = 0) ==> SUC(n - 1) = n")
    prove
      r"!(r:A ring) n.
          integral_domain r /\ ~(ring_of_num r n = ring_0 r)
          ==> poly_separable r
                (poly_sub r (poly_pow r (poly_var r one) n) (poly_1 r))"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"~(n = 0)") ASSUME_TAC THENL [ASM_MESON_TAC [ring_of_num], ALL_TAC] THEN SUBGOAL_THEN (← q r"coeff n (poly_sub r (poly_pow r (poly_var r one) n) (poly_1 r)) =
      ring_1 (r:A ring)") MP_TAC THENL [ASM_SIMP_TAC [COEFF_POLY_SUB, COEFF_POLY_VARPOW, COEFF_POLY_1, RING_SUB_RZERO, RING_1], ALL_TAC] THEN REWRITE_TAC [poly_separable, POLY_DERIV_VAR_POW_SUB_1, COEFF] THEN REWRITE_TAC [POLY_CLAUSES] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"(:1)"), (← q r"ring_of_num r n:A")] POLY_CONST) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"one")] POLY_VAR_UNIV) THEN REWRITE_TAC [RING_OF_NUM] THEN SPEC_TAC ((← q r"poly_var r one:(1->num)->A"), (← q r"x:(1->num)->A")) THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_pow (poly_ring r (:1)) x n =
      ring_mul (poly_ring (r:A ring) (:1)) x
       (ring_pow (poly_ring r (:1)) x (n - 1))") SUBST_ALL_TAC THENL [ASM_SIMP_TAC [(← GSYM (← CONJUNCT2 ring_pow)), r2], ALL_TAC] THEN ASM_SIMP_TAC [ring_coprime, RING_SUB, RING_MUL, RING_POW, RING_1] THEN X_GEN_TAC (← q r"h:(1->num)->A") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_divides (poly_ring r (:1)) h
        (poly_const r (ring_of_num r n):(1->num)->A)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"poly_ring (r:A ring) (:1)"), (← q r"poly_const r (ring_of_num r n):(1->num)->A"), (← q r"x:(1->num)->A"), (← q r"ring_pow (poly_ring (r:A ring) (:1)) x (n - 1)")] r1) THEN ASM_SIMP_TAC [RING_POW] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_DIVIDES_SUB THEN CONJ_TAC THEN MATCH_MP_TAC RING_DIVIDES_LMUL THEN ASM_SIMP_TAC [RING_POW], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"(:1)"), (← q r"h:(1->num)->A"), (← q r"poly_const r (ring_of_num r n):(1->num)->A")] POLY_DEG_DIVIDES_LE) THEN ASM_REWRITE_TAC [POLY_CONST_EQ_0, POLY_DEG_CONST, LE] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"h:(1->num)->A")] POLY_DEG_EQ_0) THEN ANTS_TAC THENL [ASM_MESON_TAC [RING_POLYNOMIAL, RING_DIVIDES_IN_CARRIER], DISCH_THEN SUBST1_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:A") (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN REWRITE_TAC [RING_UNIT_POLY_CONST, RING_UNIT_DIVIDES] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"(:1)"), (← q r"a:A"), (← q r"ring_sub (poly_ring r (:1))
         (ring_mul (poly_ring r (:1)) x (ring_pow (poly_ring r (:1)) x (n - 1)))
         (ring_1 (poly_ring (r:A ring) (:1)))")] POLY_CONST_DIVIDES_COEFFS_EQ) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"\v:1. (n:num)")) o CONJUNCT2)) THEN ASM_REWRITE_TAC [])

  let RING_DIVIDES_POW_SUB_1 ← prove
    r"!r (x:A) m n.
        x IN ring_carrier r /\ m divides n
        ==> ring_divides r (ring_sub r (ring_pow r x m) (ring_1 r))
                           (ring_sub r (ring_pow r x n) (ring_1 r))"
    (REPEAT GEN_TAC THEN REWRITE_TAC [divides] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"k:num") SUBST1_TAC)) THEN ASM_CASES_TAC (← q r"k = 0") THEN ASM_SIMP_TAC [MULT_CLAUSES, ring_pow, RING_SUB_REFL, RING_DIVIDES_0, RING_SUB, RING_POW, RING_1] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ring_pow r (x:A) m"), (← q r"ring_1 r:A"), (← q r"k:num")] RING_DIVIDES_SUB_POW) THEN ASM_SIMP_TAC [RING_POW, RING_1, RING_POW_ONE, RING_POW_POW])

  let POLY_VAR_POW_SUB_1_HOMOMORPHIC_IMAGE ← prove
    r"!(r:A ring) (r':B ring) f n.
        ring_homomorphism(r,r') f
        ==> f o poly_sub r (poly_pow r (poly_var r one) n) (poly_1 r) =
            poly_sub r' (poly_pow r' (poly_var r' one) n) (poly_1 r')"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [poly_1] THEN ASM_SIMP_TAC [POLY_COMPOSE_HOMOMORPHISM_SUB, POLY_COMPOSE_HOMOMORPHISM_POW, RING_POWERSERIES_POW, RING_POWERSERIES_VAR, RING_POWERSERIES_CONST, RING_1] THEN ASM_SIMP_TAC [POLY_COMPOSE_HOMOMORPHISM_VAR, POLY_COMPOSE_HOMOMORPHISM_CONST, RING_1] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_1])

  let FINITE_DIVISORS_LT ← prove
    r"!n:num. FINITE {d | d divides n /\ d < n}"
    (GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{d:num | d < n}") THEN REWRITE_TAC [FINITE_NUMSEG_LT] THEN SET_TAC [])

  let DIVISORS_INSERT_LT ← prove
    r"!n. ~(n = 0) ==> {d | d divides n} = n INSERT {d | d divides n /\ d < n}"
    (REWRITE_TAC [EXTENSION, IN_INSERT, IN_ELIM_THM] THEN MESON_TAC [DIVIDES_LE, DIVIDES_REFL, LT_LE])

  let RING_PRODUCT_DIVISORS ← prove
    r"!r (f:num->A) n.
        ~(n = 0) /\ f n IN ring_carrier r
        ==> ring_product r {d | d divides n} f =
            ring_mul r (f n) (ring_product r {d | d divides n /\ d < n} f)"
    (SIMP_TAC [DIVISORS_INSERT_LT, RING_PRODUCT_CLAUSES, FINITE_DIVISORS_LT, IN_ELIM_THM, LT_REFL])

  let CYCLOTOMIC_POLY_0 ← prove
    r"!r:A ring. cyclotomic_poly r 0 = poly_1 r"
    (ONCE_REWRITE_TAC [cyclotomic_poly] THEN REWRITE_TAC [])

  let CYCLOTOMIC_POLY_IN_CARRIER ← prove
    r"!(r:A ring) n. cyclotomic_poly r n IN ring_carrier(poly_ring r (:1))"
    (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [cyclotomic_poly] THEN COND_CASES_TAC THEN REWRITE_TAC [POLY_CLAUSES, RING_1] THEN MATCH_MP_TAC POLY_DIV THEN SIMP_TAC [RING_PRODUCT, RING_SUB, RING_POW, RING_1, POLY_VAR_UNIV])

  let CYCLOTOMIC_POLY_1 ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"~(d = 1 /\ d = 0)")
    let r2 ← ARITH_RULE (← q r"d < 1 <=> d = 0")
    prove
      r"!r:A ring.
          cyclotomic_poly r 1 = poly_sub r (poly_var r one) (poly_1 r)"
      (GEN_TAC THEN ONCE_REWRITE_TAC [cyclotomic_poly] THEN REWRITE_TAC [ARITH_EQ, DIVIDES_ONE, r2] THEN REWRITE_TAC [r1, EMPTY_GSPEC] THEN REWRITE_TAC [RING_PRODUCT_CLAUSES, POLY_CLAUSES] THEN SIMP_TAC [RING_POW_1, POLY_VAR_UNIV] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ring_sub (poly_ring r (:1)) (poly_var r one)
                (ring_1 (poly_ring (r:A ring) (:1)))"), (← q r"ring_1 (poly_ring (r:A ring) (:1))")] POLY_DIV_MUL) THEN SIMP_TAC [RING_MUL_RID, RING_SUB, RING_1, POLY_VAR_UNIV] THEN REWRITE_TAC [POLY_RING_CLAUSES, POLY_DEG_1, COEFF_POLY_1, RING_UNIT_1])

  let CYCLOTOMIC_POLY_UNIQUE ← prove
    r"!(r:A ring) n q.
        ~(n = 0) /\
        (!d. d divides n /\ d < n ==> monic r (cyclotomic_poly r d)) /\
        q IN ring_carrier(poly_ring r (:1)) /\
        poly_sub r (poly_pow r (poly_var r one) n) (poly_1 r) =
        ring_mul (poly_ring r (:1)) q
          (ring_product (poly_ring r (:1)) {d | d divides n /\ d < n}
                        (cyclotomic_poly r))
        ==> cyclotomic_poly r n = q /\ monic r q /\
            ring_product (poly_ring r (:1)) {d | d divides n}
              (cyclotomic_poly r) =
            poly_sub r (poly_pow r (poly_var r one) n) (poly_1 r)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN ABBREV_TAC (← q r"P = ring_product (poly_ring r (:1)) {d | d divides n /\ d < n}
                    (cyclotomic_poly (r:A ring))") THEN SUBGOAL_THEN (← q r"monic r (P:(1->num)->A) /\ P IN ring_carrier(poly_ring r (:1))") STRIP_ASSUME_TAC THENL [EXPAND_TAC "P" THEN REWRITE_TAC [RING_PRODUCT] THEN MATCH_MP_TAC MONIC_POLY_PRODUCT THEN ASM_SIMP_TAC [IN_ELIM_THM, RING_POLYNOMIAL, CYCLOTOMIC_POLY_IN_CARRIER, FINITE_DIVISORS_LT], ALL_TAC] THEN SUBGOAL_THEN (← q r"cyclotomic_poly r n = (q:(1->num)->A)") ASSUME_TAC THENL [GEN_REWRITE_TAC LAND_CONV [cyclotomic_poly] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC POLY_DIV_MUL THEN RULE_ASSUM_TAC (REWRITE_RULE [monic]) THEN ASM_REWRITE_TAC [RING_UNIT_1], ASM_SIMP_TAC [RING_PRODUCT_DIVISORS, CYCLOTOMIC_POLY_IN_CARRIER]] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"n:num")] MONIC_POLY_VAR_POW_SUB_1) THEN ASM_REWRITE_TAC [POLY_RING_CLAUSES] THEN ASM_MESON_TAC [MONIC_POLY_MUL_EQ, RING_POLYNOMIAL])

  let CYCLOTOMIC_POLY_INTEGER_PRODUCT ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"ring_product R {b | b divides g} (f:num->B)"
    let q2 ← q r"ring_divides (R:B ring) h
        (ring_product R {b:num | b divides d /\ b < d} f)"
    let q3 ← q r"!d u:num. d divides d * u"
    let v4 ← ExceptT.mk (NUMBER_RULE q3)
    let q5 ← q r"ring_sub R (ring_pow R x e) (ring_1 R):B"
    let q6 ← q r"ring_sub R (ring_pow R x d) (ring_1 R):B"
    let q7 ← q r"d:num * u = e * v + g"
    let v8 ← ASSUME q7
    let v9 ← GSYM v8
    let q10 ← q r"(x:B) IN ring_carrier R"
    let v11 ← ASSUME q10
    let v12 ← GSYM RING_POW_ADD
    let q13 ← q r"!R a b:B. a IN ring_carrier R /\ b IN ring_carrier R
                   ==> ring_sub R b (ring_1 R) =
                       ring_sub R (ring_sub R (ring_mul R a b) (ring_1 R))
                         (ring_mul R b (ring_sub R a (ring_1 R)))"
    let r14 ← RING_RULE q13
    let q15 ← q r"ring_pow R (x:B) g"
    let q16 ← q r"ring_pow R (x:B) (e * v)"
    let q17 ← q r"R:B ring"
    let v18 ← ISPECL [q17, q16, q15] r14
    let q19 ← q r"v:num"
    let q20 ← q r"u:num"
    let q21 ← q r"e:num"
    let q22 ← q r"d:num"
    let v23 ← SPECL [q22, q21] BEZOUT_GCD_STRONG
    let q24 ← q r"ring_divides R h (ring_sub (R:B ring) (ring_pow R x g) (ring_1 R))"
    let q25 ← q r"!c. c = d \/ c = e
          ==> ring_divides R h
                (ring_sub (R:B ring) (ring_pow R x c) (ring_1 R))"
    let q26 ← q r"(h:B) IN ring_carrier R"
    let q27 ← q r"h:B"
    let q28 ← q r"c:num"
    let q29 ← q r"!c. ~(c = 0) /\ (c divides d \/ c divides e)
          ==> ring_sub R (ring_pow R x c) (ring_1 R) =
              ring_mul (R:B ring) (f c)
                (ring_product R {b | b divides c /\ b < c} f)"
    let q30 ← q r"g:num"
    let q31 ← q r"g divides d /\ g divides e /\ ~(g = 0)"
    let q32 ← q r"g:num = gcd(d,e)"
    let p33 ← prove r"!R (x:B) (f:num->B) d e.
          x IN ring_carrier R /\ (!c. f c IN ring_carrier R) /\
          ~(d = 0) /\ ~(e = 0) /\ gcd(d,e) < d /\
          ring_squarefree R (ring_sub R (ring_pow R x d) (ring_1 R)) /\
          (!c. ~(c = 0) /\ (c divides d \/ c divides e)
               ==> ring_product R {b | b divides c} f =
                   ring_sub R (ring_pow R x c) (ring_1 R))
          ==> ring_coprime R (f d,f e)" (REPEAT STRIP_TAC THEN ABBREV_TAC q32 THEN SUBGOAL_THEN q31 STRIP_ASSUME_TAC THENL [EXPAND_TAC "g" THEN ASM_REWRITE_TAC [GCD, GCD_ZERO], ALL_TAC] THEN FIRST_ASSUM (MP_TAC o (SPEC q30)) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN SUBGOAL_THEN q29 ASSUME_TAC THENL [REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC q28)) THEN ASM_SIMP_TAC [RING_PRODUCT_DIVISORS], ALL_TAC] THEN ASM_REWRITE_TAC [ring_coprime] THEN X_GEN_TAC q27 THEN STRIP_TAC THEN SUBGOAL_THEN q26 ASSUME_TAC THENL [ASM_MESON_TAC [RING_DIVIDES_IN_CARRIER], ALL_TAC] THEN SUBGOAL_THEN q25 ASSUME_TAC THENL [REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN ASM_SIMP_TAC [DIVIDES_REFL] THEN MATCH_MP_TAC RING_DIVIDES_RMUL THEN ASM_REWRITE_TAC [RING_PRODUCT], ALL_TAC] THEN SUBGOAL_THEN q24 ASSUME_TAC THENL [MP_TAC v23 THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [q20, q19] THEN DISCH_TAC THEN MP_TAC v18 THEN SIMP_TAC [RING_POW, v12, v11] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [v9] THEN MATCH_MP_TAC RING_DIVIDES_SUB THEN CONJ_TAC THEN TRY (MATCH_MP_TAC RING_DIVIDES_LMUL THEN ASM_SIMP_TAC [RING_POW]) THEN MATCH_MP_TAC RING_DIVIDES_TRANS THENL [EXISTS_TAC q6, EXISTS_TAC q5] THEN (CONJ_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [], MATCH_MP_TAC RING_DIVIDES_POW_SUB_1 THEN ASM_REWRITE_TAC [v4]]), ALL_TAC] THEN SUBGOAL_THEN q2 ASSUME_TAC THENL [MATCH_MP_TAC RING_DIVIDES_TRANS THEN EXISTS_TAC q1 THEN CONJ_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN MATCH_MP_TAC RING_DIVIDES_PRODUCT_SUBSET THEN REWRITE_TAC [FINITE_DIVISORS_LT, SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC [DIVIDES_TRANS, DIVIDES_LE, LET_TRANS], ALL_TAC] THEN FIRST_X_ASSUM (MATCH_MP_TAC o (CONJUNCT2 o (GEN_REWRITE_RULE id [ring_squarefree]))) THEN ASM_SIMP_TAC [DIVIDES_REFL, RING_POW_2, RING_DIVIDES_MUL2])
    let lemma := p33
    let q34 ← q r"cyclotomic_poly integer_ring"
    let q35 ← q r"poly_var integer_ring one"
    let q36 ← q r"poly_ring integer_ring (:1)"
    let v37 ← ISPECL [q36, q35, q34] lemma
    let v38 ← GSYM POLY_CLAUSES
    let v39 ← REWRITE_RULE [v38, POLY_VAR_UNIV, CYCLOTOMIC_POLY_IN_CARRIER] v37
    let clemma := v39
    let q40 ← q r"q:(1->num)->int"
    let q41 ← q r"n:num"
    let q42 ← q r"integer_ring"
    let v43 ← ISPECL [q42, q41, q40] CYCLOTOMIC_POLY_UNIQUE
    let q44 ← q r"q:(1->num)->int"
    let q45 ← q r"d:num"
    let q46 ← q r"poly_sub integer_ring
                  (poly_pow integer_ring (poly_var integer_ring one) d)
                  (poly_1 integer_ring)"
    let q47 ← q r"~(d = 0)"
    let q48 ← q r"d:num"
    let q49 ← q r"e:num"
    let q50 ← q r"d:num"
    let v51 ← SPECL [q50, q49] GCD
    let q52 ← q r"gcd(d:num,e) < d"
    let q53 ← q r"!c. ~(c = 0) /\ (c divides d \/ c divides e)
            ==> ring_product (poly_ring integer_ring (:1)) {b | b divides c}
                  (cyclotomic_poly integer_ring) =
                poly_sub integer_ring
                  (poly_pow integer_ring (poly_var integer_ring one) c)
                  (poly_1 integer_ring)"
    let q54 ← q r"~(d = 0) /\ ~(e = 0)"
    let q55 ← q r"e:num"
    let q56 ← q r"d:num"
    let v57 ← GSYM POLY_CLAUSES
    let q58 ← q r"ring_divides (poly_ring integer_ring (:1))
      (ring_product (poly_ring integer_ring (:1)) {d | d divides n /\ d < n}
                    (cyclotomic_poly integer_ring))
      (poly_sub integer_ring
        (poly_pow integer_ring (poly_var integer_ring one) n)
        (poly_1 integer_ring))"
    let q59 ← q r"n = 0"
    let q60 ← q r"n:num"
    let q61 ← q r"!d. ~(d = 0)
        ==> ring_squarefree (poly_ring integer_ring (:1))
              (poly_sub integer_ring
                (poly_pow integer_ring (poly_var integer_ring one) d)
                (poly_1 integer_ring))"
    prove
      r"!n. monic integer_ring (cyclotomic_poly integer_ring n) /\
         (~(n = 0)
          ==> ring_product (poly_ring integer_ring (:1)) {d | d divides n}
                (cyclotomic_poly integer_ring) =
              poly_sub integer_ring
                (poly_pow integer_ring (poly_var integer_ring one) n)
                (poly_1 integer_ring))"
      (SUBGOAL_THEN q61 ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC POLY_SEPARABLE_IMP_SQUAREFREE THEN MATCH_MP_TAC POLY_SEPARABLE_VAR_POW_SUB_1 THEN ASM_REWRITE_TAC [INTEGRAL_DOMAIN_INTEGER_RING, INTEGER_RING_OF_NUM, INTEGER_RING, INT_OF_NUM_EQ], ALL_TAC] THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC q60 THEN DISCH_TAC THEN ASM_CASES_TAC q59 THEN ASM_REWRITE_TAC [CYCLOTOMIC_POLY_0, MONIC_POLY_1] THEN SUBGOAL_THEN q58 MP_TAC THENL [wPart Except.ok (lhand o rand) RING_COPRIME_PRODUCT_DIVIDES THEN REWRITE_TAC [POLY_CLAUSES] THEN SIMP_TAC [UFD_POLY_RING, UFD_INTEGER_RING, FINITE_DIVISORS_LT, RING_SUB, RING_POW, RING_1, POLY_VAR_UNIV, CYCLOTOMIC_POLY_IN_CARRIER] THEN REWRITE_TAC [v57] THEN ANTS_TAC THENL [REWRITE_TAC [pairwise, IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [q56, q55] THEN STRIP_TAC THEN SUBGOAL_THEN q54 STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [DIVIDES_ZERO], ALL_TAC] THEN SUBGOAL_THEN q53 ASSUME_TAC THENL [ASM_MESON_TAC [DIVIDES_LE, LET_TRANS], ALL_TAC] THEN ASM_CASES_TAC q52 THENL [MATCH_MP_TAC clemma THEN ASM_SIMP_TAC [], ONCE_REWRITE_TAC [RING_COPRIME_SYM] THEN MATCH_MP_TAC clemma THEN ONCE_REWRITE_TAC [GCD_SYM] THEN ONCE_REWRITE_TAC [DISJ_SYM] THEN ASM_SIMP_TAC [] THEN MP_TAC v51 THEN ASM_MESON_TAC [DIVIDES_LE, LT_LE, LE_ANTISYM, NOT_LT]], DISCH_THEN SUBST1_TAC] THEN X_GEN_TAC q48 THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN SUBGOAL_THEN q47 ASSUME_TAC THENL [ASM_MESON_TAC [DIVIDES_ZERO], ALL_TAC] THEN MATCH_MP_TAC RING_DIVIDES_TRANS THEN EXISTS_TAC q46 THEN CONJ_TAC THENL [FIRST_X_ASSUM (MP_TAC o (SPEC q45)) THEN ASM_SIMP_TAC [RING_PRODUCT_DIVISORS, CYCLOTOMIC_POLY_IN_CARRIER] THEN DISCH_THEN (SUBST1_TAC o (SYM o CONJUNCT2)) THEN MATCH_MP_TAC RING_DIVIDES_RMUL THEN REWRITE_TAC [RING_DIVIDES_REFL, CYCLOTOMIC_POLY_IN_CARRIER, RING_PRODUCT], REWRITE_TAC [POLY_CLAUSES] THEN MATCH_MP_TAC RING_DIVIDES_POW_SUB_1 THEN ASM_REWRITE_TAC [POLY_VAR_UNIV]], ALL_TAC] THEN REWRITE_TAC [ring_divides] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN q44 STRIP_ASSUME_TAC))) THEN MP_TAC v43 THEN ANTS_TAC THENL [ASM_SIMP_TAC [] THEN ASM_MESON_TAC [RING_MUL_SYM], SIMP_TAC []])

  let CYCLOTOMIC_POLY_RING_OF_INT ← prove
    r"!(r:A ring) n.
        cyclotomic_poly r n = ring_of_int r o cyclotomic_poly integer_ring n /\
        monic r (cyclotomic_poly r n) /\
        (~(n = 0)
         ==> ring_product (poly_ring r (:1)) {d | d divides n}
               (cyclotomic_poly r) =
             poly_sub r (poly_pow r (poly_var r one) n) (poly_1 r))"
    (GEN_TAC THEN MP_TAC (← ISPEC (← q r"(:1)") (← MATCH_MP RING_HOMOMORPHISM_POLY_RINGS (← ISPEC (← q r"r:A ring") RING_HOMOMORPHISM_INTEGER_RING_OF_INT))) THEN DISCH_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC (← q r"n:num") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"n = 0") THENL [ASM_REWRITE_TAC [CYCLOTOMIC_POLY_0, MONIC_POLY_1] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP RING_HOMOMORPHISM_1)) THEN REWRITE_TAC [POLY_RING_CLAUSES] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"n:num"), (← q r"ring_of_int (r:A ring) o cyclotomic_poly integer_ring n")] CYCLOTOMIC_POLY_UNIQUE) THEN ANTS_TAC THENL [ALL_TAC, SIMP_TAC []] THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"d:num") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"d:num"))) THEN ASM_SIMP_TAC [], ALL_TAC] THEN CONJ_TAC THENL [MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN EXISTS_TAC (← q r"integer_ring") THEN REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, CYCLOTOMIC_POLY_IN_CARRIER], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_product (poly_ring r (:1)) {d | d divides n /\ d < n}
      (cyclotomic_poly r) =
    ring_of_int (r:A ring) o
    ring_product (poly_ring integer_ring (:1)) {d | d divides n /\ d < n}
      (cyclotomic_poly integer_ring)") SUBST1_TAC THENL [FIRST_ASSUM (MP_TAC o ((ISPECL [(← q r"cyclotomic_poly integer_ring"), (← q r"{d:num | d divides n /\ d < n}")]) o (MATCH_MP RING_HOMOMORPHISM_PRODUCT))) THEN REWRITE_TAC [FINITE_DIVISORS_LT, CYCLOTOMIC_POLY_IN_CARRIER] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_PRODUCT_EQ THEN REWRITE_TAC [IN_ELIM_THM, o_THM] THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBST1_TAC (← SYM (← SPEC (← q r"n:num") (← MATCH_MP POLY_VAR_POW_SUB_1_HOMOMORPHIC_IMAGE (← ISPEC (← q r"r:A ring") RING_HOMOMORPHISM_INTEGER_RING_OF_INT)))) THEN MP_TAC (← SPEC (← q r"n:num") CYCLOTOMIC_POLY_INTEGER_PRODUCT) THEN SIMP_TAC [(← ASSUME (← q r"~(n = 0)")), RING_PRODUCT_DIVISORS, CYCLOTOMIC_POLY_IN_CARRIER] THEN DISCH_THEN (SUBST1_TAC o (SYM o CONJUNCT2)) THEN FIRST_ASSUM (MP_TAC o (MATCH_MP RING_HOMOMORPHISM_MUL)) THEN REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC [CYCLOTOMIC_POLY_IN_CARRIER, RING_PRODUCT])

  let CYCLOTOMIC_POLY_MONIC ← prove
    r"!(r:A ring) n. monic r (cyclotomic_poly r n)"
    (MESON_TAC [CYCLOTOMIC_POLY_RING_OF_INT])

  let CYCLOTOMIC_POLY_PRODUCT ← prove
    r"!(r:A ring) n.
        ~(n = 0)
        ==> ring_product (poly_ring r (:1)) {d | d divides n}
                         (cyclotomic_poly r) =
            poly_sub r (poly_pow r (poly_var r one) n) (poly_1 r)"
    (MESON_TAC [CYCLOTOMIC_POLY_RING_OF_INT])

  let CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE ← prove
    r"!(r:A ring) (r':B ring) h n.
        ring_homomorphism(r,r') h
        ==> h o cyclotomic_poly r n = cyclotomic_poly r' n"
    (REPEAT STRIP_TAC THEN MP_TAC (← CONJUNCT1 (← ISPECL [(← q r"r:A ring"), (← q r"n:num")] CYCLOTOMIC_POLY_RING_OF_INT)) THEN MP_TAC (← CONJUNCT1 (← ISPECL [(← q r"r':B ring"), (← q r"n:num")] CYCLOTOMIC_POLY_RING_OF_INT)) THEN REPEAT (DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC [o_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM, o_THM] THEN FIRST_ASSUM (ACCEPT_TAC o (MATCH_MP RING_HOMOMORPHISM_RING_OF_INT)))

  let CYCLOTOMIC_POLY_DEG ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"a:num = b ==> x + a = n ==> y + b = n ==> y = x")
    prove
      r"!(r:A ring) n.
          poly_deg r (cyclotomic_poly r n) =
          if ring_1 r = ring_0 r then 0 else phi n"
      (GEN_TAC THEN ASM_CASES_TAC (← q r"ring_1 r = ring_0 (r:A ring)") THEN ASM_REWRITE_TAC [] THENL [GEN_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"cyclotomic_poly (r:A ring) n")] TRIVIAL_RING_POLY_0) THEN ASM_REWRITE_TAC [TRIVIAL_RING_10, RING_POLYNOMIAL, CYCLOTOMIC_POLY_IN_CARRIER] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [POLY_DEG_0], ALL_TAC] THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC (← q r"n:num") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [CYCLOTOMIC_POLY_0, POLY_DEG_1, PHI_0] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"n:num")] POLY_DEG_VAR_POW_SUB_1) THEN MP_TAC (← SPEC (← q r"n:num") PHI_DIVISORSUM) THEN ASM_SIMP_TAC [(← GSYM CYCLOTOMIC_POLY_PRODUCT), POLY_DEG_PRODUCT_MONIC, FINITE_DIVISORS, RING_POLYNOMIAL, CYCLOTOMIC_POLY_IN_CARRIER, CYCLOTOMIC_POLY_MONIC] THEN ASM_SIMP_TAC [DIVISORS_INSERT_LT, NSUM_CLAUSES, FINITE_DIVISORS_LT, IN_ELIM_THM, LT_REFL] THEN MATCH_MP_TAC r1 THEN MATCH_MP_TAC NSUM_EQ THEN ASM_SIMP_TAC [IN_ELIM_THM])

  let CYCLOTOMIC_POLY_ROOT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (q ==> r) ==> (p <=> q) ==> r")
    prove
      r"!(r:A ring) x n.
          integral_domain r /\ x IN ring_carrier r /\
          ring_order r x = n /\ ~(n = 0)
          ==> poly_eval r (cyclotomic_poly r n) x = ring_0 r"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"!d. ~(d = 0)
          ==> (ring_product (r:A ring) {c | c divides d}
                 (\c. poly_eval r (cyclotomic_poly r c) x) = ring_0 r <=>
               n divides d)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"{c:num | c divides d}"), (← q r"cyclotomic_poly (r:A ring)"), (← q r"x:A")] POLY_EVAL_RING_PRODUCT) THEN ASM_SIMP_TAC [FINITE_DIVISORS, CYCLOTOMIC_POLY_IN_CARRIER, CYCLOTOMIC_POLY_PRODUCT] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [POLY_EVAL_SUB, POLY_EVAL_POW, POLY_EVAL_VAR, POLY_EVAL_1, RING_POLYNOMIAL_POW, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_1, RING_SUB_EQ_0, RING_POW, RING_1] THEN ASM_MESON_TAC [RING_POW_EQ_1], ALL_TAC] THEN FIRST_ASSUM (MP_TAC o (SPEC (← q r"n:num"))) THEN SIMP_TAC [(← ASSUME (← q r"~(n = 0)")), (← ASSUME (← q r"integral_domain (r:A ring)")), DIVIDES_REFL, INTEGRAL_DOMAIN_PRODUCT_EQ_0, FINITE_DIVISORS, IN_ELIM_THM] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"d:num") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"~(d = 0)") ASSUME_TAC THENL [ASM_MESON_TAC [DIVIDES_ZERO], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"d:num"))) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [MATCH_MP_TAC RING_PRODUCT_ZERO THEN EXISTS_TAC (← q r"d:num") THEN ASM_SIMP_TAC [FINITE_DIVISORS, IN_ELIM_THM, DIVIDES_REFL], ASM_MESON_TAC [DIVIDES_ANTISYM]])

  let CYCLOTOMIC_POLY_ROOT_EQ ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"(~p ==> F) ==> p")
    prove
      r"!(r:A ring) x n.
          integral_domain r /\ ~(ring_of_num r n = ring_0 r) /\
          x IN ring_carrier r
          ==> (poly_eval r (cyclotomic_poly r n) x = ring_0 r <=>
               ring_order r x = n)"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"~(n = 0)") ASSUME_TAC THENL [ASM_MESON_TAC [ring_of_num], ALL_TAC] THEN EQ_TAC THENL [DISCH_TAC, ASM_MESON_TAC [CYCLOTOMIC_POLY_ROOT]] THEN SUBGOAL_THEN (← q r"poly_sub r (poly_pow r (poly_var r one) n) (poly_1 r) IN
      ring_carrier(poly_ring (r:A ring) (:1))") ASSUME_TAC THENL [REWRITE_TAC [POLY_CLAUSES] THEN SIMP_TAC [RING_SUB, RING_POW, RING_1, POLY_VAR_UNIV], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_pow r x n = ring_1 (r:A ring)") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"!p. ring_divides (poly_ring r (:1)) p (cyclotomic_poly r n)
            ==> ring_divides (poly_ring r (:1)) p
                 (poly_sub r (poly_pow r (poly_var r one) n)
                    (poly_1 (r:A ring)))") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN ASM_SIMP_TAC [(← GSYM CYCLOTOMIC_POLY_PRODUCT)] THEN ASM_SIMP_TAC [RING_PRODUCT_DIVISORS, CYCLOTOMIC_POLY_IN_CARRIER] THEN MATCH_MP_TAC RING_DIVIDES_RMUL THEN ASM_REWRITE_TAC [RING_PRODUCT], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"x:A"), (← q r"poly_sub r (poly_pow r (poly_var r one) n) (poly_1 r):(1->num)->A")] POLY_DIVIDES_X_MINUS_ROOT_EQ) THEN ASM_SIMP_TAC [POLY_DIVIDES_X_MINUS_ROOT, CYCLOTOMIC_POLY_IN_CARRIER] THEN ASM_SIMP_TAC [POLY_EVAL_SUB, POLY_EVAL_POW, POLY_EVAL_VAR, POLY_EVAL_1, RING_POLYNOMIAL_POW, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_1, RING_SUB_EQ_0, RING_POW, RING_1], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_order r x divides n /\ ~(ring_order r (x:A) = 0)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_POW_EQ_1, DIVIDES_ZERO], ALL_TAC] THEN MATCH_MP_TAC r1 THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_order r (x:A) < n") ASSUME_TAC THENL [ASM_MESON_TAC [DIVIDES_LE, LT_LE], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_divides (poly_ring r (:1))
        (ring_mul (poly_ring r (:1))
          (poly_sub r (poly_var r one) (poly_const r x))
          (poly_sub r (poly_var r one) (poly_const r x)))
        (poly_sub r (poly_pow r (poly_var r one) n) (poly_1 (r:A ring)))") MP_TAC THENL [ASM_SIMP_TAC [(← GSYM CYCLOTOMIC_POLY_PRODUCT), RING_PRODUCT_DIVISORS, CYCLOTOMIC_POLY_IN_CARRIER] THEN MATCH_MP_TAC RING_DIVIDES_MUL2 THEN ASM_SIMP_TAC [POLY_DIVIDES_X_MINUS_ROOT, CYCLOTOMIC_POLY_IN_CARRIER] THEN MATCH_MP_TAC RING_DIVIDES_TRANS THEN EXISTS_TAC (← q r"cyclotomic_poly r (ring_order r (x:A))") THEN ASM_SIMP_TAC [POLY_DIVIDES_X_MINUS_ROOT, CYCLOTOMIC_POLY_IN_CARRIER, CYCLOTOMIC_POLY_ROOT] THEN MP_TAC (← ISPECL [(← q r"poly_ring (r:A ring) (:1)"), (← q r"cyclotomic_poly (r:A ring)"), (← q r"{ring_order r (x:A)}"), (← q r"{d:num | d divides n /\ d < n}")] RING_DIVIDES_PRODUCT_SUBSET) THEN ASM_REWRITE_TAC [FINITE_DIVISORS_LT, SING_SUBSET, IN_ELIM_THM, RING_PRODUCT_SING, CYCLOTOMIC_POLY_IN_CARRIER], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"n:num")] POLY_SEPARABLE_VAR_POW_SUB_1) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"poly_sub r (poly_var r one) (poly_const r x):(1->num)->A")) o (CONJUNCT2 o ((GEN_REWRITE_RULE id [ring_squarefree]) o (MATCH_MP POLY_SEPARABLE_IMP_SQUAREFREE))))) THEN ASM_SIMP_TAC [RING_POW_2, POLY_X_MINUS_A_IN_CARRIER, RING_UNIT_X_MINUS_A, INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING])

  let POLY_VAR_POW_SUB_1_PRODUCT ← prove
    r"!(r:A ring) z n.
        integral_domain r /\ z IN ring_carrier r /\
        ring_order r z = n /\ ~(n = 0)
        ==> poly_sub r (poly_pow r (poly_var r one) n) (poly_1 r) =
            ring_product (poly_ring r (:1)) {j | j < n}
              (\j. poly_sub r (poly_var r one)
                              (poly_const r (ring_pow r z j)))"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC MONIC_POLY_EQ_ROOTS_PRODUCT THEN ASM_SIMP_TAC [MONIC_POLY_VAR_POW_SUB_1, POLY_DEG_VAR_POW_SUB_1, INTEGRAL_DOMAIN_NONTRIVIAL, FINITE_NUMSEG_LT, CARD_NUMSEG_LT, RING_POW, IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL [REWRITE_TAC [POLY_CLAUSES] THEN SIMP_TAC [RING_SUB, RING_POW, RING_1, POLY_VAR_UNIV], X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN ASM_SIMP_TAC [POLY_EVAL_SUB, POLY_EVAL_POW, POLY_EVAL_VAR, POLY_EVAL_1, RING_POLYNOMIAL_POW, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_1, RING_SUB_EQ_0, RING_POW, RING_1, RING_POW_POW] THEN ASM_SIMP_TAC [RING_POW_EQ_1, (← ExceptT.mk (NUMBER_RULE (← q r"!n j:num. n divides j * n")))], ASM_MESON_TAC [RING_POW_EQ_LT_EQ]])

  let CYCLOTOMIC_POLY_SPLITS ← prove
    r"!(r:A ring) z n.
        integral_domain r /\ z IN ring_carrier r /\
        ring_order r z = n /\ ~(n = 0)
        ==> cyclotomic_poly r n =
            ring_product (poly_ring r (:1)) {j | j < n /\ coprime(j,n)}
              (\j. poly_sub r (poly_var r one)
                              (poly_const r (ring_pow r z j)))"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC MONIC_POLY_EQ_ROOTS_PRODUCT THEN ASM_SIMP_TAC [CYCLOTOMIC_POLY_IN_CARRIER, CYCLOTOMIC_POLY_MONIC, CYCLOTOMIC_POLY_DEG, INTEGRAL_DOMAIN_NONTRIVIAL, RING_POW, IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{j:num | j < n}") THEN REWRITE_TAC [FINITE_NUMSEG_LT] THEN SET_TAC [], REWRITE_TAC [PHI_ALT] THEN AP_TERM_TAC THEN SET_TAC [], X_GEN_TAC (← q r"j:num") THEN STRIP_TAC THEN MATCH_MP_TAC CYCLOTOMIC_POLY_ROOT THEN ASM_SIMP_TAC [RING_POW, RING_ORDER_POW_GEN] THEN COND_CASES_TAC THENL [ASM_MESON_TAC [COPRIME_0], ALL_TAC] THEN ASM_MESON_TAC [COPRIME_GCD, GCD_SYM, DIV_1], ASM_MESON_TAC [RING_POW_EQ_LT_EQ]])

  -- @@RETURN BEGIN
  return { cyclotomic_poly, RING_REGULAR_POLY_UNIT_LEADING, POLY_DIV_MUL,
           MONIC_POLY_MUL_EQ, POLY_DEG_VAR_POW_SUB_1, MONIC_POLY_VAR_POW_SUB_1,
           POLY_DERIV_VAR_POW_SUB_1, POLY_SEPARABLE_VAR_POW_SUB_1,
           RING_DIVIDES_POW_SUB_1, POLY_VAR_POW_SUB_1_HOMOMORPHIC_IMAGE,
           FINITE_DIVISORS_LT, DIVISORS_INSERT_LT, RING_PRODUCT_DIVISORS,
           CYCLOTOMIC_POLY_0, CYCLOTOMIC_POLY_IN_CARRIER, CYCLOTOMIC_POLY_1,
           CYCLOTOMIC_POLY_UNIQUE, CYCLOTOMIC_POLY_INTEGER_PRODUCT,
           CYCLOTOMIC_POLY_RING_OF_INT, CYCLOTOMIC_POLY_MONIC, CYCLOTOMIC_POLY_PRODUCT,
           CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE, CYCLOTOMIC_POLY_DEG, CYCLOTOMIC_POLY_ROOT,
           CYCLOTOMIC_POLY_ROOT_EQ, POLY_VAR_POW_SUB_1_PRODUCT, CYCLOTOMIC_POLY_SPLITS }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- cyclotomic_poly.ml phrases from line 813 to 1433                       -/
/- ---------------------------------------------------------------------- -/

structure CyclotomicPoly02 where
  -- @@FIELDS
  CYCLOTOMIC_POLY_PRODUCT_NONDIVISORS : thm
  CYCLOTOMIC_POLY_PRIME_POWER : thm
  CYCLOTOMIC_POLY_EVAL_1_PRIME_POWER : thm
  CYCLOTOMIC_POLY_EVAL_1 : thm
  CYCLOTOMIC_POLY_EVAL_0 : thm
  CYCLOTOMIC_POLY_SQUAREFREE : thm
  CYCLOTOMIC_POLY_RING_CHAR : thm
  CYCLOTOMIC_POLY_IRREDUCIBLE_FACTOR_DEG : thm
  MONIC_POLY_IRREDUCIBLE_FACTORIZATION : thm
  CYCLOTOMIC_POLY_IRREDUCIBLE_FACTORIZATION : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupCyclotomicPoly02 [HolBase] (D : CyclotomicPolyDeps) (BCyclotomicPoly01 : CyclotomicPoly01) :
    ExceptT String IO CyclotomicPoly02 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON, MESON_TAC,
        NUMBER_RULE, RING_TAC, SET_TAC, TAUT, .. } := D
  let { ADD1, ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH, CARD_EQ_0, CARD_NUMSEG_LT,
        DE_MORGAN_THM, DISJOINT, DIVIDES_0, DIVIDES_1, DIVIDES_ANTISYM,
        DIVIDES_EXP_LE_IMP, DIVIDES_LE, DIVIDES_LMUL, DIVIDES_LMUL2_EQ, DIVIDES_MUL2,
        DIVIDES_PRIMEPOW, DIVIDES_PRIME_PRIME, DIVIDES_REFL, DIVIDES_REXP,
        DIVIDES_RMUL, DIVIDES_TRANS, DIVIDES_ZERO, DIVISION_DECOMP, EQ_MULT_LCANCEL,
        EQ_PRIMEPOW, EQ_TRANS, EXP, EXP_EQ_0, EXTENSION, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_IMP_NONTRIVIAL_RING, FIELD_MONIC_IRREDUCIBLE_ASSOCIATE, FINITE_DELETE,
        FINITE_DIVISORS, FINITE_FIELD_IRREDUCIBLE_ROOT_POW, FINITE_IMAGE,
        FINITE_NUMSEG, FINITE_NUMSEG_LT, FINITE_RESTRICT, FINITE_SUBSET,
        FORALL_IN_IMAGE, GCD, IMP_CONJ, IMP_IMP, INDEX_DECOMPOSITION_PRIME,
        INTEGER_RING, INTEGER_RING_OF_NUM, INTEGRAL_DOMAIN_POLY_RING,
        INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE, INTEGRAL_DOMAIN_REGULAR,
        INT_EQ_MUL_RCANCEL, INT_MUL_LID, INT_OF_NUM_EQ, IN_DELETE, IN_ELIM_THM,
        IN_IMAGE, IN_INSERT, IN_INTER, IN_NUMSEG, IN_RING_POLYNOMIAL_CARRIER_COMPOSE,
        IN_SING, IN_UNION, IRREDUCIBLE_IMP_POLY_DEG_NZ, LE, LEFT_IMP_EXISTS_THM,
        LE_EXP, LE_REFL, LT_LE, LT_MULT_LCANCEL, MEMBER_NOT_EMPTY, MONIC_ASSOCIATES_EQ,
        MONIC_IMP_NONZERO, MONIC_POLY_POW, MONIC_POLY_PRODUCT, MULT_ASSOC,
        MULT_CLAUSES, MULT_EQ_0, MULT_SYM, NOT_IN_EMPTY, NSUM_CONST, NSUM_EQ,
        NUMSEG_LT, ORDER_DIVIDES, PHI_1, PHI_PRIMEPOW_SUC, PID_IMP_UFD, PID_POLY_RING,
        POLY_CLAUSES, POLY_DEG_MONOMORPHIC_IMAGE, POLY_DEG_PRODUCT_MONIC, .. } := D.core1
  let { POLY_EVAL, POLY_EVAL_1, POLY_EVAL_HOMOMORPHIC_IMAGE, POLY_EVAL_MUL,
        POLY_EVAL_POW, POLY_EVAL_RING_PRODUCT, POLY_EVAL_RING_SUM, POLY_EVAL_SUB,
        POLY_EVAL_VAR, POLY_RING_CLAUSES, POLY_SEPARABLE_IMP_SQUAREFREE, POLY_VAR_UNIV,
        PRIME_COPRIME_EQ, PRIME_DIVEXP, PRIME_FACTOR, PRIME_IMP_NZ,
        RIGHT_EXISTS_IMP_THM, RING_0, RING_1, RING_ASSOCIATES_PRODUCT,
        RING_ASSOCIATES_SYM, RING_ASSOCIATES_TRANS, RING_CHAR_DIVIDES_ORDER,
        RING_CHAR_EQ_1, RING_CHAR_MONOMORPHIC_IMAGE, RING_CHAR_POLY_RING,
        RING_DIVIDES_IRREDUCIBLE_ROOT, RING_DIVIDES_PRODUCT_SUBSET,
        RING_ENDOMORPHISM_FROBENIUS_ITERATE, RING_GEOM_SERIES, RING_HOMOMORPHISM_1,
        RING_HOMOMORPHISM_INTEGER_RING_OF_INT, RING_HOMOMORPHISM_SUB,
        RING_IRREDUCIBLE_IN_CARRIER, RING_MONOMORPHISM_IMP_HOMOMORPHISM,
        RING_MUL_LCANCEL, RING_MUL_RCANCEL, RING_MUL_RID, RING_MUL_SYM, RING_NEG,
        RING_OF_NUM, RING_OF_NUM_0, RING_OF_NUM_EQ_0, RING_ORDER_0, RING_POLYNOMIAL,
        RING_POLYNOMIAL_1, RING_POLYNOMIAL_POW, RING_POLYNOMIAL_VAR, RING_POW,
        RING_POW_1, RING_POW_ADD, RING_POW_EQ, RING_POW_ONE, RING_POW_POW,
        RING_POW_ZERO, RING_PRODUCT, RING_PRODUCT_CLAUSES, RING_PRODUCT_CONST,
        RING_PRODUCT_DELTA, RING_PRODUCT_EQ, RING_PRODUCT_IMAGE,
        RING_PRODUCT_IMAGE_GEN, RING_PRODUCT_POW, RING_PRODUCT_SING,
        RING_PRODUCT_UNION, RING_SQUAREFREE_DIVISOR, RING_SQUAREFREE_POW, RING_SUB,
        RING_SUB_LZERO, RING_SUM, RING_SUM_CONST, RING_UNIT_1, SING_SUBSET, SKOLEM_THM,
        TRIVIAL_RING_10, UFD_EQ_PRIMEFACT, algebraic_extension,
        algebraically_closed_field, divides, field_extension, monic, num_CASES, num_WF,
        o_DEF, o_THM, ring_endomorphism, ring_irreducible, .. } := D.core2
  let { CYCLOTOMIC_POLY_0, CYCLOTOMIC_POLY_1, CYCLOTOMIC_POLY_DEG,
        CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE, CYCLOTOMIC_POLY_IN_CARRIER,
        CYCLOTOMIC_POLY_MONIC, CYCLOTOMIC_POLY_PRODUCT, CYCLOTOMIC_POLY_ROOT_EQ,
        FINITE_DIVISORS_LT, MONIC_POLY_VAR_POW_SUB_1, POLY_SEPARABLE_VAR_POW_SUB_1,
        RING_PRODUCT_DIVISORS, RING_REGULAR_POLY_UNIT_LEADING, .. } := BCyclotomicPoly01
  -- @@SCOPE END

  let CYCLOTOMIC_POLY_PRODUCT_NONDIVISORS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"m * n:num = n * m")
    let r2 ← ARITH_RULE (← q r"~(m = 0) ==> SUC(m - 1) = m")
    prove
      r"!(r:A ring) m n.
          ~(m = 0) /\ ~(n = 0)
          ==> ring_product (poly_ring r (:1))
                {d | d divides m * n /\ ~(d divides n)} (cyclotomic_poly r) =
              ring_sum (poly_ring r (:1)) {i | i < m}
                (\i. poly_pow r (poly_var r one) (n * i))"
      (REPEAT STRIP_TAC THEN MATCH_MP_TAC (← ISPECL [(← q r"poly_ring (r:A ring) (:1)"), (← q r"poly_sub r (poly_pow r (poly_var r one) n) (poly_1 (r:A ring))")] RING_MUL_RCANCEL) THEN REWRITE_TAC [RING_PRODUCT, RING_SUM] THEN CONJ_TAC THENL [MATCH_MP_TAC RING_REGULAR_POLY_UNIT_LEADING THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"n:num")] MONIC_POLY_VAR_POW_SUB_1) THEN ASM_SIMP_TAC [monic, RING_UNIT_1] THEN DISCH_TAC THEN REWRITE_TAC [POLY_CLAUSES] THEN SIMP_TAC [RING_SUB, RING_POW, RING_1, POLY_VAR_UNIV], ALL_TAC] THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (← q r"poly_sub r (poly_pow r (poly_var r one) (m * n))
                           (poly_1 (r:A ring))") THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m * n:num")] CYCLOTOMIC_POLY_PRODUCT) THEN ASM_REWRITE_TAC [MULT_EQ_0] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [(← GSYM CYCLOTOMIC_POLY_PRODUCT)] THEN SUBGOAL_THEN (← q r"{d:num | d divides m * n} =
        {d | d divides m * n /\ ~(d divides n)} UNION {d | d divides n}") SUBST1_TAC THENL [REWRITE_TAC [EXTENSION, IN_UNION, IN_ELIM_THM] THEN MESON_TAC [DIVIDES_LMUL], CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_PRODUCT_UNION] THEN ASM_SIMP_TAC [FINITE_DIVISORS] THEN CONJ_TAC THENL [ALL_TAC, SET_TAC []] THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{d:num | d divides m * n}") THEN ASM_SIMP_TAC [FINITE_DIVISORS, MULT_EQ_0] THEN SET_TAC [], REWRITE_TAC [POLY_CLAUSES] THEN MP_TAC (← ISPECL [(← q r"poly_ring (r:A ring) (:1)"), (← q r"ring_pow (poly_ring r (:1)) (poly_var r one) n:(1->num)->A"), (← q r"m - 1")] RING_GEOM_SERIES) THEN ASM_SIMP_TAC [RING_POW, POLY_VAR_UNIV, RING_POW_POW, r2] THEN SUBST1_TAC r1 THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC [NUMSEG_LT] THEN MATCH_MP_TAC RING_MUL_SYM THEN SIMP_TAC [RING_SUM, RING_SUB, RING_POW, RING_1, POLY_VAR_UNIV]])

  let CYCLOTOMIC_POLY_PRIME_POWER ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"~(SUC k <= k)")
    prove
      r"!(r:A ring) p k.
          prime p
          ==> cyclotomic_poly r (p EXP (k + 1)) =
              ring_sum (poly_ring r (:1)) {i | i < p}
                (\i. poly_pow r (poly_var r one) (p EXP k * i))"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:num"), (← q r"p EXP k")] CYCLOTOMIC_POLY_PRODUCT_NONDIVISORS) THEN ASM_SIMP_TAC [PRIME_IMP_NZ, EXP_EQ_0] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN SUBGOAL_THEN (← q r"{d | d divides p * p EXP k /\ ~(d divides p EXP k)} = {p EXP (k + 1)}") SUBST1_TAC THENL [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_SING, (← GSYM (← CONJUNCT2 EXP)), (← GSYM ADD1)] THEN ASM_SIMP_TAC [DIVIDES_PRIMEPOW] THEN ASM_MESON_TAC [EQ_PRIMEPOW, LE, LE_REFL, r1], REWRITE_TAC [RING_PRODUCT_SING, CYCLOTOMIC_POLY_IN_CARRIER]])

  let CYCLOTOMIC_POLY_EVAL_1_PRIME_POWER ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"~(k = 0) ==> k = (k - 1) + 1")
    prove
      r"!(r:A ring) p k.
          prime p /\ ~(k = 0)
          ==> poly_eval r (cyclotomic_poly r (p EXP k)) (ring_1 r) =
              ring_of_num r p"
      (REPEAT STRIP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o (MATCH_MP r1)) THEN ASM_SIMP_TAC [CYCLOTOMIC_POLY_PRIME_POWER] THEN SIMP_TAC [POLY_EVAL_RING_SUM, FINITE_NUMSEG_LT, RING_1, POLY_CLAUSES, RING_POW, POLY_VAR_UNIV] THEN SIMP_TAC [(← GSYM POLY_CLAUSES), POLY_EVAL_POW, POLY_EVAL_VAR, RING_POLYNOMIAL_VAR, RING_1, RING_POW_ONE] THEN SIMP_TAC [RING_SUM_CONST, FINITE_NUMSEG_LT, CARD_NUMSEG_LT, RING_1, RING_MUL_RID, RING_OF_NUM])

  let CYCLOTOMIC_POLY_EVAL_1 ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"p EXP a * e"
    let q2 ← q r"p * p EXP (a - 1) = p EXP a"
    let v3 ← ASSUME q2
    let v4 ← ONCE_REWRITE_RULE [MULT_SYM] v3
    let q5 ← q r"p EXP (a - 1)"
    let q6 ← q r"!c p m:num. ~(c = 0) /\ (c * p) divides (c * m) ==> p divides m"
    let v7 ← ExceptT.mk (NUMBER_RULE q6)
    let q8 ← q r"~((p:num) divides m)"
    let q9 ← q r"e:num"
    let q10 ← q r"!d k m:num. d divides k * m ==> d divides gcd(d,k) * m"
    let v11 ← ExceptT.mk (NUMBER_RULE q10)
    let q12 ← q r"gcd(d,p EXP a) * m"
    let q13 ← q r"p ==> ~p ==> q"
    let r14 ← TAUT q13
    let q15 ← q r"~(d divides p EXP (a - 1) * m)"
    let q16 ← q r"p EXP a * e divides p EXP a * m"
    let q17 ← q r"e:num"
    let q18 ← q r"e:num"
    let q19 ← q r"p EXP a"
    let q20 ← q r"d:num"
    let v21 ← SPECL [q20, q19] GCD
    let q22 ← q r"p EXP a divides d"
    let q23 ← q r"i:num = a"
    let q24 ← q r"i:num"
    let q25 ← q r"prime p"
    let v26 ← ASSUME q25
    let q27 ← q r"k:num"
    let q28 ← q r"a:num"
    let v29 ← INST [(q28, q27)] DIVIDES_PRIMEPOW
    let v30 ← MATCH_MP v29 v26
    let q31 ← q r"gcd(d,p EXP a)"
    let v32 ← SPEC q31 v30
    let q33 ← q r"d:num"
    let q34 ← q r"~(p EXP a = 0) /\ ~(p EXP (a - 1) = 0)"
    let q35 ← q r"~(a = 0) ==> SUC(a - 1) = a"
    let r36 ← ARITH_RULE q35
    let v37 ← CONJUNCT2 EXP
    let v38 ← GSYM v37
    let q39 ← q r"p * p EXP (a - 1) = p EXP a"
    let p40 ← prove r"!p a m. prime p /\ ~(a = 0) /\ ~(p divides m)
               ==> {d | d divides p * p EXP (a - 1) * m /\
                        ~(d divides p EXP (a - 1) * m)} =
                   IMAGE (\e. p EXP a * e) {e | e divides m}" (REPEAT STRIP_TAC THEN SUBGOAL_THEN q39 ASSUME_TAC THENL [ASM_SIMP_TAC [v38, r36], ALL_TAC] THEN SUBGOAL_THEN q34 STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [EXP_EQ_0, PRIME_IMP_NZ], ALL_TAC] THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_IMAGE, MULT_ASSOC] THEN X_GEN_TAC q33 THEN ASM_REWRITE_TAC [] THEN EQ_TAC THENL [STRIP_TAC THEN MP_TAC v32 THEN ASM_REWRITE_TAC [GCD, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC q24 THEN STRIP_TAC THEN ASM_CASES_TAC q23 THENL [FIRST_X_ASSUM SUBST_ALL_TAC THEN SUBGOAL_THEN q22 MP_TAC THENL [MP_TAC v21 THEN ASM_SIMP_TAC [], ALL_TAC] THEN DISCH_THEN ((X_CHOOSE_THEN q18 SUBST_ALL_TAC) o (REWRITE_RULE [divides])) THEN EXISTS_TAC q17 THEN REWRITE_TAC [] THEN UNDISCH_TAC q16 THEN ASM_SIMP_TAC [DIVIDES_LMUL2_EQ], UNDISCH_TAC q15 THEN MATCH_MP_TAC r14 THEN MATCH_MP_TAC DIVIDES_TRANS THEN EXISTS_TAC q12 THEN CONJ_TAC THENL [ASM_MESON_TAC [v11], ASM_REWRITE_TAC [] THEN MATCH_MP_TAC DIVIDES_MUL2 THEN REWRITE_TAC [DIVIDES_REFL] THEN MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN ASM_ARITH_TAC]], DISCH_THEN (X_CHOOSE_THEN q9 STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC [DIVIDES_LMUL2_EQ] THEN DISCH_TAC THEN UNDISCH_TAC q8 THEN REWRITE_TAC [] THEN MATCH_MP_TAC v7 THEN EXISTS_TAC q5 THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [v4] THEN MATCH_MP_TAC DIVIDES_TRANS THEN EXISTS_TAC q1 THEN ASM_REWRITE_TAC [] THEN MESON_TAC [DIVIDES_RMUL, DIVIDES_REFL]])
    let lemma := p40
    let v41 ← GSYM INT_MUL_LID
    let q42 ← q r"~(m = 0) /\ ~(m = 1) ==> 1 < m"
    let r43 ← ARITH_RULE q42
    let q44 ← q r"t:num"
    let q45 ← q r"p:num"
    let q46 ← q r"p EXP a * e"
    let q47 ← q r"t:num"
    let q48 ← q r"e:num"
    let v49 ← SPEC q48 PRIME_FACTOR
    let q50 ← q r"e:num"
    let q51 ← q r"ring_product integer_ring {d | d divides m /\ d < m}
                    (\e. if e = 1 then ring_of_num integer_ring p
                         else ring_1 integer_ring)"
    let q52 ← q r"ring_product integer_ring {d | d divides m /\ d < m}
        (\e. poly_eval integer_ring
               (cyclotomic_poly integer_ring (p EXP a * e))
               (ring_1 integer_ring)) =
      ring_of_num integer_ring p"
    let v53 ← GSYM POLY_CLAUSES
    let v54 ← REWRITE_RULE [POLY_CLAUSES] POLY_EVAL_MUL
    let q55 ← q r"\p. poly_eval integer_ring p (ring_1 integer_ring)"
    let q56 ← q r"m:num"
    let q57 ← q r"cyclotomic_poly integer_ring o (\e. p EXP a * e)"
    let q58 ← q r"poly_ring integer_ring (:1)"
    let v59 ← ISPECL [q58, q57, q56] RING_PRODUCT_DIVISORS
    let q60 ← q r"{e:num | e divides m}"
    let q61 ← q r"cyclotomic_poly integer_ring"
    let q62 ← q r"\e. p EXP a * e"
    let q63 ← q r"poly_ring integer_ring (:1)"
    let v64 ← ISPECL [q63, q62, q61, q60] RING_PRODUCT_IMAGE
    let q65 ← q r"p EXP (a - 1) * m"
    let q66 ← q r"p:num"
    let q67 ← q r"integer_ring"
    let v68 ← ISPECL [q67, q66, q65] CYCLOTOMIC_POLY_PRODUCT_NONDIVISORS
    let q69 ← q r"q divides p EXP a * 1"
    let q70 ← q r"p divides p EXP 0 * m"
    let q71 ← q r"~(a = 0) /\ ~(m = 0) /\ ~(m = 1)"
    let q72 ← q r"~((p:num) divides m)"
    let q73 ← q r"m:num"
    let q74 ← q r"a:num"
    let q75 ← q r"a:num"
    let q76 ← q r"index p n"
    let q77 ← q r"p:num"
    let q78 ← q r"n:num"
    let v79 ← SPECL [q78, q77] INDEX_DECOMPOSITION_PRIME
    let q80 ← q r"n = 0"
    let q81 ← q r"q:num"
    let q82 ← q r"p:num"
    let q83 ← q r"n:num"
    let p84 ← prove r"!n p q. prime p /\ prime q /\ ~(p = q) /\ p divides n /\ q divides n
             ==> poly_eval integer_ring (cyclotomic_poly integer_ring n)
                   (ring_1 integer_ring) = ring_1 integer_ring" (MATCH_MP_TAC num_WF THEN X_GEN_TAC q83 THEN DISCH_TAC THEN MAP_EVERY X_GEN_TAC [q82, q81] THEN STRIP_TAC THEN ASM_CASES_TAC q80 THEN ASM_REWRITE_TAC [CYCLOTOMIC_POLY_0, POLY_EVAL_1] THEN MP_TAC v79 THEN ASM_REWRITE_TAC [] THEN SPEC_TAC (q76, q75) THEN X_GEN_TAC q74 THEN DISCH_THEN (X_CHOOSE_THEN q73 (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC)) THEN SUBGOAL_THEN q72 ASSUME_TAC THENL [ASM_MESON_TAC [PRIME_COPRIME_EQ], ALL_TAC] THEN SUBGOAL_THEN q71 STRIP_ASSUME_TAC THENL [RULE_ASSUM_TAC (REWRITE_RULE [MULT_EQ_0, DE_MORGAN_THM]) THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL [UNDISCH_TAC q70 THEN ASM_REWRITE_TAC [EXP, MULT_CLAUSES], UNDISCH_TAC q69 THEN REWRITE_TAC [MULT_CLAUSES] THEN ASM_MESON_TAC [PRIME_DIVEXP, DIVIDES_PRIME_PRIME]], ALL_TAC] THEN MP_TAC v68 THEN ASM_SIMP_TAC [PRIME_IMP_NZ, MULT_EQ_0, EXP_EQ_0, lemma] THEN MP_TAC v64 THEN ASM_SIMP_TAC [EQ_MULT_LCANCEL, EXP_EQ_0, PRIME_IMP_NZ] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC v59 THEN ASM_REWRITE_TAC [o_THM, CYCLOTOMIC_POLY_IN_CARRIER] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN (MP_TAC o (AP_TERM q55)) THEN SIMP_TAC [v54, RING_POLYNOMIAL, CYCLOTOMIC_POLY_IN_CARRIER, RING_PRODUCT, RING_1] THEN SIMP_TAC [POLY_EVAL_RING_PRODUCT, POLY_EVAL_RING_SUM, FINITE_DIVISORS_LT, FINITE_NUMSEG_LT, RING_1, o_THM, CYCLOTOMIC_POLY_IN_CARRIER, POLY_CLAUSES, RING_POW, POLY_VAR_UNIV] THEN SIMP_TAC [v53, POLY_EVAL_POW, POLY_EVAL_VAR, RING_POLYNOMIAL_VAR, RING_1, RING_POW_ONE] THEN SIMP_TAC [RING_SUM_CONST, FINITE_NUMSEG_LT, CARD_NUMSEG_LT, RING_1, RING_MUL_RID, RING_OF_NUM] THEN SUBGOAL_THEN q52 SUBST1_TAC THENL [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC q51 THEN CONJ_TAC THENL [MATCH_MP_TAC RING_PRODUCT_EQ THEN X_GEN_TAC q50 THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [MULT_CLAUSES, CYCLOTOMIC_POLY_EVAL_1_PRIME_POWER] THEN MP_TAC v49 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN q47 STRIP_ASSUME_TAC) THEN FIRST_X_ASSUM (MP_TAC o (SPEC q46)) THEN ASM_SIMP_TAC [LT_MULT_LCANCEL, EXP_EQ_0, PRIME_IMP_NZ] THEN DISCH_THEN (MP_TAC o (SPECL [q45, q44])) THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL [ASM_MESON_TAC [DIVIDES_TRANS], MATCH_MP_TAC DIVIDES_RMUL THEN MATCH_MP_TAC DIVIDES_REXP THEN ASM_REWRITE_TAC [DIVIDES_REFL], MATCH_MP_TAC DIVIDES_LMUL THEN ASM_REWRITE_TAC []], ASM_SIMP_TAC [RING_PRODUCT_DELTA, IN_ELIM_THM, DIVIDES_1, RING_OF_NUM, r43]], ALL_TAC] THEN REWRITE_TAC [INTEGER_RING_OF_NUM, INTEGER_RING] THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [v41] THEN ASM_SIMP_TAC [INT_EQ_MUL_RCANCEL, INT_OF_NUM_EQ, PRIME_IMP_NZ])
    let integer_case := p84
    let q85 ← q r"r:A ring"
    let v86 ← ISPEC q85 RING_HOMOMORPHISM_INTEGER_RING_OF_INT
    prove
      r"!(r:A ring) n p q.
          prime p /\ prime q /\ ~(p = q) /\ p divides n /\ q divides n
          ==> poly_eval r (cyclotomic_poly r n) (ring_1 r) = ring_1 r"
      (REPEAT STRIP_TAC THEN MP_TAC v86 THEN DISCH_THEN (fun th => tactic_of do pure (SUBST1_TAC (← SYM (← SPEC (← q r"n:num") (← MATCH_MP CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE th))) THEN SUBST1_TAC (← SYM (← MATCH_MP RING_HOMOMORPHISM_1 th)) THEN MP_TAC (← SPECL [(← q r"ring_1 integer_ring"), (← q r"cyclotomic_poly integer_ring n")] (← MATCH_MP (← REWRITE_RULE [IMP_CONJ] POLY_EVAL_HOMOMORPHIC_IMAGE) th)))) THEN REWRITE_TAC [RING_1, CYCLOTOMIC_POLY_IN_CARRIER] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN MATCH_MP_TAC integer_case THEN ASM_MESON_TAC [])

  let CYCLOTOMIC_POLY_EVAL_0 ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"2 <= n ==> ~(n = 0)")
    let r2 ← ARITH_RULE (← q r"2 <= n ==> 1 < n")
    let r3 ← ARITH_RULE (← q r"2 <= n ==> ~(n = 0)")
    let r4 ← ARITH_RULE (← q r"~(n = 0) /\ ~(n = 1) ==> 2 <= n")
    let r5 ← ARITH_RULE (← q r"2 <= n ==> ~(n = 0)")
    prove
      r"!(r:A ring) n.
          2 <= n ==> poly_eval r (cyclotomic_poly r n) (ring_0 r) = ring_1 r"
      (GEN_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC (← q r"n:num") THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"n:num")] CYCLOTOMIC_POLY_PRODUCT) THEN ASM_SIMP_TAC [r5, RING_PRODUCT_DIVISORS, CYCLOTOMIC_POLY_IN_CARRIER] THEN DISCH_THEN (MP_TAC o (AP_TERM (← q r"\p. poly_eval r p (ring_0(r:A ring))"))) THEN SIMP_TAC [(← REWRITE_RULE [POLY_CLAUSES] POLY_EVAL_MUL), RING_POLYNOMIAL, CYCLOTOMIC_POLY_IN_CARRIER, RING_PRODUCT, RING_0] THEN SIMP_TAC [POLY_EVAL_RING_PRODUCT, FINITE_DIVISORS_LT, RING_0, CYCLOTOMIC_POLY_IN_CARRIER] THEN SUBGOAL_THEN (← q r"ring_product r {d | d divides n /\ d < n}
        (\d. poly_eval r (cyclotomic_poly r d) (ring_0 r)) =
      ring_neg r (ring_1 (r:A ring))") SUBST1_TAC THENL [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (← q r"ring_product r {d | d divides n /\ d < n}
                    (\d. if d = 1 then ring_neg r (ring_1 r)
                         else ring_1 (r:A ring))") THEN CONJ_TAC THENL [MATCH_MP_TAC RING_PRODUCT_EQ THEN X_GEN_TAC (← q r"d:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN COND_CASES_TAC THENL [ASM_REWRITE_TAC [CYCLOTOMIC_POLY_1] THEN SIMP_TAC [POLY_EVAL_SUB, POLY_EVAL_VAR, POLY_EVAL_1, RING_0, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_1, RING_SUB_LZERO, RING_1], FIRST_X_ASSUM (MATCH_MP_TAC o (REWRITE_RULE [IMP_IMP])) THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [DIVIDES_ZERO, r4, r3]], ASM_SIMP_TAC [RING_PRODUCT_DELTA, IN_ELIM_THM, DIVIDES_1, RING_NEG, RING_1, r2]], ALL_TAC] THEN SIMP_TAC [POLY_EVAL_SUB, POLY_EVAL_POW, POLY_EVAL_VAR, POLY_EVAL_1, RING_POLYNOMIAL_POW, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_1, RING_0, RING_POW_ZERO] THEN ASM_SIMP_TAC [r1, RING_SUB_LZERO, RING_1] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"cyclotomic_poly (r:A ring) n"), (← q r"ring_0(r:A ring)")] POLY_EVAL) THEN SPEC_TAC ((← q r"poly_eval r (cyclotomic_poly r n) (ring_0(r:A ring))"), (← q r"y:A")) THEN RING_TAC)

  let CYCLOTOMIC_POLY_SQUAREFREE ← prove
    r"!(r:A ring) m.
        integral_domain r /\ ~(ring_of_num r m = ring_0 r)
        ==> ring_squarefree (poly_ring r (:1)) (cyclotomic_poly r m)"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"~(m = 0)") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_NUM_0], ALL_TAC] THEN MATCH_MP_TAC RING_SQUAREFREE_DIVISOR THEN EXISTS_TAC (← q r"poly_sub r (poly_pow r (poly_var r one) m)
                         (poly_1 r):(1->num)->A") THEN ASM_SIMP_TAC [POLY_SEPARABLE_IMP_SQUAREFREE, POLY_SEPARABLE_VAR_POW_SUB_1] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM (← MATCH_MP CYCLOTOMIC_POLY_PRODUCT th))])) THEN MP_TAC (← ISPECL [(← q r"poly_ring (r:A ring) (:1)"), (← q r"cyclotomic_poly (r:A ring)"), (← q r"{m:num}"), (← q r"{d:num | d divides m}")] RING_DIVIDES_PRODUCT_SUBSET) THEN ASM_SIMP_TAC [FINITE_DIVISORS, SING_SUBSET, IN_ELIM_THM, DIVIDES_REFL, RING_PRODUCT_SING, CYCLOTOMIC_POLY_IN_CARRIER])

  let CYCLOTOMIC_POLY_RING_CHAR ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let PR ← ((← (do let z1 ← (pure (CONJUNCTS POLY_RING_CLAUSES)); liftExcept (tl z1)))).mapM (fun th => do GSYM (← ISPECL [(← q r"r:A ring"), (← q r"(:1)")] th))
    let v2 ← GSYM RING_POLYNOMIAL
    let v3 ← REWRITE_RULE [v2] CYCLOTOMIC_POLY_IN_CARRIER
    let CPP := v3
    let q4 ← q r"k:num"
    let q5 ← q r"poly_ring (r:A ring) (:1)"
    let v6 ← ISPECL [q5, q4] RING_ENDOMORPHISM_FROBENIUS_ITERATE
    let p7 ← prove r"!(r:A ring) p k n.
        prime p /\ ring_char r = p
        ==> poly_pow r (poly_sub r (poly_pow r (poly_var r one) n)
                                   (poly_1 r)) (p EXP k) =
            poly_sub r (poly_pow r (poly_var r one) (p EXP k * n))
                       (poly_1 r)" (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM)) THEN DISCH_TAC THEN REWRITE_TAC PR THEN MP_TAC v6 THEN ASM_REWRITE_TAC [RING_CHAR_POLY_RING, ring_endomorphism] THEN DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← MATCH_MP RING_HOMOMORPHISM_SUB th) THEN MP_TAC (← MATCH_MP RING_HOMOMORPHISM_1 th))) THEN SIMP_TAC [RING_POW, RING_1, POLY_VAR_UNIV, RING_POW_POW, MULT_SYM])
    let FROB := p7
    let p8 ← prove r"!r p:(1->num)->A.
        p IN ring_carrier(poly_ring r (:1)) /\ monic r p
        ==> ring_regular (poly_ring r (:1)) p" (SIMP_TAC [RING_REGULAR_POLY_UNIT_LEADING, monic, RING_UNIT_1])
    let MONIC_REGULAR := p8
    let q9 ← q r"p EXP SUC a * e = p EXP a * p * e"
    let q10 ← q r"d divides p EXP a * m"
    let q11 ← q r"~((p:num) divides m)"
    let q12 ← q r"e:num"
    let v13 ← GSYM MULT_ASSOC
    let q14 ← q r"p EXP a * m"
    let q15 ← q r"c:num"
    let q16 ← q r"i:num"
    let q17 ← q r"b divides p EXP SUC a"
    let q18 ← q r"c:num"
    let q19 ← q r"b:num"
    let q20 ← q r"d:num"
    let p21 ← prove r"!p a m.
        prime p /\ ~(p divides m)
        ==> {d | d divides p EXP SUC a * m} =
            {d | d divides p EXP a * m} UNION
            IMAGE (\e. p EXP SUC a * e) {e | e divides m} /\
            DISJOINT {d | d divides p EXP a * m}
                     (IMAGE (\e. p EXP SUC a * e) {e | e divides m})" (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_NZ)) THEN REWRITE_TAC [EXTENSION, DISJOINT, IN_INTER, IN_UNION, IN_IMAGE, IN_ELIM_THM, NOT_IN_EMPTY] THEN CONJ_TAC THEN X_GEN_TAC q20 THENL [EQ_TAC THENL [DISCH_THEN ((X_CHOOSE_THEN q19 (X_CHOOSE_THEN q18 STRIP_ASSUME_TAC)) o (MATCH_MP DIVISION_DECOMP)) THEN UNDISCH_TAC q17 THEN ASM_SIMP_TAC [DIVIDES_PRIMEPOW, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC q16 THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC SUBST_ALL_TAC) THEN REWRITE_TAC [LE] THEN STRIP_TAC THENL [DISJ2_TAC THEN EXISTS_TAC q15 THEN ASM_REWRITE_TAC [], DISJ1_TAC THEN ASM_SIMP_TAC [DIVIDES_MUL2, DIVIDES_EXP_LE_IMP]], STRIP_TAC THEN ASM_REWRITE_TAC [] THENL [MATCH_MP_TAC DIVIDES_TRANS THEN EXISTS_TAC q14 THEN ASM_REWRITE_TAC [EXP, v13] THEN MATCH_MP_TAC DIVIDES_LMUL THEN REWRITE_TAC [DIVIDES_REFL], ASM_SIMP_TAC [DIVIDES_LMUL2_EQ, EXP_EQ_0]]], DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN q12 STRIP_ASSUME_TAC)) THEN UNDISCH_TAC q11 THEN REWRITE_TAC [] THEN UNDISCH_TAC q10 THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN q9 SUBST1_TAC THENL [REWRITE_TAC [EXP] THEN ARITH_TAC, ASM_SIMP_TAC [DIVIDES_LMUL2_EQ, EXP_EQ_0]] THEN CONV_TAC NUMBER_RULE])
    let DIVISORS := p21
    let q22 ← q r"a:num <= b ==> b = a + (b - a)"
    let r23 ← ARITH_RULE q22
    let v24 ← GSYM RING_POW_ADD
    let q25 ← q r"phi(p EXP SUC n)"
    let q26 ← q r"{e:num | e divides m}"
    let q27 ← q r"cyclotomic_poly (r:A ring)"
    let q28 ← q r"poly_ring (r:A ring) (:1)"
    let v29 ← ISPECL [q28, q27, q26, q25] RING_PRODUCT_POW
    let q30 ← q r"m:num"
    let q31 ← q r"n:num"
    let q32 ← q r"p:num"
    let q33 ← q r"r:A ring"
    let v34 ← ISPECL [q33, q32, q31, q30] FROB
    let q35 ← q r"m:num"
    let q36 ← q r"SUC n"
    let q37 ← q r"p:num"
    let q38 ← q r"r:A ring"
    let v39 ← ISPECL [q38, q37, q36, q35] FROB
    let q40 ← q r"m:num"
    let q41 ← q r"n:num"
    let q42 ← q r"p:num"
    let v43 ← SPECL [q42, q41, q40] DIVISORS
    let q44 ← q r"p EXP n * m"
    let q45 ← q r"r:A ring"
    let v46 ← ISPECL [q45, q44] CYCLOTOMIC_POLY_PRODUCT
    let q47 ← q r"p EXP SUC n * m"
    let q48 ← q r"r:A ring"
    let v49 ← ISPECL [q48, q47] CYCLOTOMIC_POLY_PRODUCT
    let q50 ← q r"poly_sub r (poly_pow r (poly_var r one) (p EXP SUC n * m))
                 (poly_1 r):(1->num)->A"
    let q51 ← q r"p EXP n * m"
    let q52 ← q r"r:A ring"
    let v53 ← ISPECL [q52, q51] CYCLOTOMIC_POLY_PRODUCT
    let q54 ← q r"poly_sub r (poly_pow r (poly_var r one) (p EXP n * m))
                           (poly_1 r):(1->num)->A"
    let q55 ← q r"poly_ring (r:A ring) (:1)"
    let v56 ← ISPEC q55 RING_MUL_LCANCEL
    let q57 ← q r"~(m = 0) /\ ~(p = 0)"
    let p58 ← prove r"!(r:A ring) p n m.
        prime p /\ ring_char r = p /\ ~(p divides m)
        ==> ring_product (poly_ring r (:1)) {e | e divides m}
              (\e. cyclotomic_poly r (p EXP SUC n * e)) =
            ring_product (poly_ring r (:1)) {e | e divides m}
              (\e. poly_pow r (cyclotomic_poly r e) (phi(p EXP SUC n)))" (REPEAT STRIP_TAC THEN SUBGOAL_THEN q57 STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [DIVIDES_0, PRIME_IMP_NZ], ALL_TAC] THEN MATCH_MP_TAC v56 THEN EXISTS_TAC q54 THEN REWRITE_TAC [RING_PRODUCT] THEN CONJ_TAC THENL [MATCH_MP_TAC MONIC_REGULAR THEN MP_TAC v53 THEN ASM_REWRITE_TAC [MULT_EQ_0, EXP_EQ_0] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [RING_PRODUCT, MONIC_POLY_PRODUCT, FINITE_DIVISORS, MULT_EQ_0, EXP_EQ_0, CYCLOTOMIC_POLY_MONIC, CPP], ALL_TAC] THEN TRANS_TAC EQ_TRANS q50 THEN CONJ_TAC THENL [MP_TAC v49 THEN MP_TAC v46 THEN ASM_REWRITE_TAC [MULT_EQ_0, EXP_EQ_0] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC v43 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN ASM_SIMP_TAC [RING_PRODUCT_UNION, FINITE_DIVISORS, FINITE_IMAGE, MULT_EQ_0, EXP_EQ_0] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN wPart lhand (lhand o rand) RING_PRODUCT_IMAGE THEN ASM_SIMP_TAC [EQ_MULT_LCANCEL, EXP_EQ_0, o_DEF], ALL_TAC] THEN MP_TAC v39 THEN MP_TAC v34 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC v29 THEN ASM_SIMP_TAC [FINITE_DIVISORS, CYCLOTOMIC_POLY_IN_CARRIER] THEN REWRITE_TAC PR THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [CYCLOTOMIC_POLY_PRODUCT] THEN REWRITE_TAC PR THEN SIMP_TAC [v24, RING_SUB, RING_POW, RING_1, POLY_VAR_UNIV] THEN AP_TERM_TAC THEN ASM_SIMP_TAC [ADD1, PHI_PRIMEPOW_SUC] THEN MATCH_MP_TAC r23 THEN ASM_SIMP_TAC [LE_EXP] THEN ARITH_TAC)
    let STEP := p58
    let q59 ← q r"~(m = 0)"
    let v60 ← ASSUME q59
    let q61 ← q r"ring_product (poly_ring r (:1)) ({e | e divides m} DELETE m)
         (\e. ring_pow (poly_ring r (:1)) (cyclotomic_poly (r:A ring) e)
                       (phi (p EXP SUC n)))"
    let q62 ← q r"poly_ring (r:A ring) (:1)"
    let v63 ← ISPEC q62 RING_MUL_RCANCEL
    let q64 ← q r"e:num"
    let q65 ← q r"(y':B) = y /\ (ring_mul (r:B ring) a y = ring_mul r b y ==> a = b)
      ==> ring_mul r a y' = ring_mul r b y ==> a = b"
    let r66 ← MESON [] q65
    let q67 ← q r"{e:num | e divides m} = m INSERT ({e | e divides m} DELETE m)"
    let q68 ← q r"m:num"
    let q69 ← q r"n:num"
    let q70 ← q r"p:num"
    let q71 ← q r"r:A ring"
    let v72 ← SPECL [q71, q70, q69, q68] STEP
    let q73 ← q r"~(m = 0)"
    let q74 ← q r"m:num"
    let q75 ← q r"m:num"
    let q76 ← q r"m:num"
    let q77 ← q r"~((p:num) divides m)"
    let q78 ← q r"a:num"
    let v79 ← SPEC q78 num_CASES
    prove
      r"!(r:A ring) p a m.
          prime p /\ ring_char r = p /\ ~(p divides m)
          ==> cyclotomic_poly r (p EXP a * m) =
              poly_pow r (cyclotomic_poly r m) (phi(p EXP a))"
      (REWRITE_TAC [IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN STRUCT_CASES_TAC v79 THENL [REWRITE_TAC [EXP, MULT_CLAUSES, PHI_1] THEN REWRITE_TAC PR THEN SIMP_TAC [RING_POW_1, CYCLOTOMIC_POLY_IN_CARRIER], UNDISCH_TAC q77 THEN SPEC_TAC (q76, q75)] THEN REWRITE_TAC PR THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC q74 THEN DISCH_TAC THEN DISCH_TAC THEN SUBGOAL_THEN q73 ASSUME_TAC THENL [ASM_MESON_TAC [DIVIDES_0], ALL_TAC] THEN MP_TAC v72 THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN q67 SUBST1_TAC THENL [REWRITE_TAC [EXTENSION, IN_INSERT, IN_DELETE, IN_ELIM_THM] THEN MESON_TAC [DIVIDES_REFL], REWRITE_TAC PR] THEN ASM_SIMP_TAC [RING_PRODUCT_CLAUSES, FINITE_DELETE, FINITE_DIVISORS, IN_DELETE, CYCLOTOMIC_POLY_IN_CARRIER, RING_POW] THEN MATCH_MP_TAC r66 THEN CONJ_TAC THENL [MATCH_MP_TAC RING_PRODUCT_EQ THEN REWRITE_TAC [IN_DELETE, IN_ELIM_THM] THEN X_GEN_TAC q64 THEN STRIP_TAC THEN FIRST_X_ASSUM (MATCH_MP_TAC o (REWRITE_RULE [IMP_IMP])) THEN CONJ_TAC THENL [ASM_MESON_TAC [DIVIDES_LE, LT_LE], ASM_MESON_TAC [DIVIDES_TRANS]], DISCH_TAC THEN MATCH_MP_TAC v63 THEN EXISTS_TAC q61 THEN ASM_SIMP_TAC [CYCLOTOMIC_POLY_IN_CARRIER, RING_POW] THEN MATCH_MP_TAC MONIC_REGULAR THEN REWRITE_TAC [RING_PRODUCT] THEN REWRITE_TAC (← (PR).mapM GSYM) THEN MATCH_MP_TAC MONIC_POLY_PRODUCT THEN SIMP_TAC [FINITE_DELETE, FINITE_DIVISORS, v60] THEN SIMP_TAC [RING_POLYNOMIAL_POW, MONIC_POLY_POW, CPP, CYCLOTOMIC_POLY_MONIC]])

  let CYCLOTOMIC_POLY_IRREDUCIBLE_FACTOR_DEG ← prove
    r"!(r:A ring) m g.
        field r /\ FINITE(ring_carrier r) /\
        coprime(m,CARD(ring_carrier r)) /\
        ring_irreducible (poly_ring r (:1)) g /\
        ring_divides (poly_ring r (:1)) g (cyclotomic_poly r m)
        ==> poly_deg r g = order m (CARD(ring_carrier r))"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_IRREDUCIBLE_IN_CARRIER)) THEN MP_TAC (← ISPEC (← q r"r:A ring") ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN ASM_REWRITE_TAC [algebraic_extension, LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"l:(A#num)ring"), (← q r"h:A->A#num")] THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_extension])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN SUBGOAL_THEN (← q r"?x. x IN ring_carrier l /\ poly_eval l ((h:A->A#num) o g) x = ring_0 l") STRIP_ASSUME_TAC THENL [FIRST_X_ASSUM (MATCH_MP_TAC o (CONJUNCT2 o (GEN_REWRITE_RULE id [algebraically_closed_field]))) THEN CONJ_TAC THENL [MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN EXISTS_TAC (← q r"r:A ring") THEN ASM_REWRITE_TAC [], ASM_SIMP_TAC [POLY_DEG_MONOMORPHIC_IMAGE, RING_POLYNOMIAL, IRREDUCIBLE_IMP_POLY_DEG_NZ]], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(ring_of_num l m = ring_0 (l:(A#num)ring))") ASSUME_TAC THENL [REWRITE_TAC [RING_OF_NUM_EQ_0] THEN ASM_MESON_TAC [RING_CHAR_MONOMORPHIC_IMAGE, RING_CHAR_DIVIDES_ORDER, RING_CHAR_EQ_1, FIELD_IMP_NONTRIVIAL_RING, (← ExceptT.mk (NUMBER_RULE (← q r"!c m q. c divides m /\ c divides q /\ coprime(m,q) ==> c = 1")))], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_order l (x:A#num) = m") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"l:(A#num)ring"), (← q r"x:A#num"), (← q r"m:num")] CYCLOTOMIC_POLY_ROOT_EQ) THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM (← MATCH_MP CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE th))])) THEN ASM_MESON_TAC [RING_DIVIDES_IRREDUCIBLE_ROOT, CYCLOTOMIC_POLY_IN_CARRIER], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_regular l (x:A#num)") ASSUME_TAC THENL [ASM_SIMP_TAC [INTEGRAL_DOMAIN_REGULAR, FIELD_IMP_INTEGRAL_DOMAIN] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"ring_order l (x:A#num) = m") THEN ASM_SIMP_TAC [RING_ORDER_0, FIELD_IMP_NONTRIVIAL_RING] THEN ASM_MESON_TAC [RING_OF_NUM_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"!n. poly_deg r (g:(1->num)->A) divides n <=>
        order m (CARD(ring_carrier r)) divides n") (fun th => MESON_TAC [th, DIVIDES_ANTISYM, DIVIDES_REFL]) THEN X_GEN_TAC (← q r"n:num") THEN MP_TAC (← ISPECL [(← q r"h:A->A#num"), (← q r"r:A ring"), (← q r"l:(A#num)ring"), (← q r"g:(1->num)->A"), (← q r"x:A#num"), (← q r"n:num")] FINITE_FIELD_IRREDUCIBLE_ROOT_POW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"l:(A#num)ring"), (← q r"x:A#num"), (← q r"CARD(ring_carrier(r:A ring)) EXP n"), (← q r"1")] RING_POW_EQ) THEN ASM_SIMP_TAC [RING_POW_1, ORDER_DIVIDES])

  let MONIC_POLY_IRREDUCIBLE_FACTORIZATION ← prove
    r"!(r:A ring) f.
        field r /\ f IN ring_carrier(poly_ring r (:1)) /\ monic r f
        ==> ?s e. FINITE s /\
                  (!g. g IN s
                       ==> g IN ring_carrier(poly_ring r (:1)) /\ monic r g /\
                           ring_irreducible (poly_ring r (:1)) g /\
                           ~(e g = 0)) /\
                  f = ring_product (poly_ring r (:1)) s
                        (\g. ring_pow (poly_ring r (:1)) g (e g))"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN)) THEN SUBGOAL_THEN (← q r"UFD(poly_ring (r:A ring) (:1))") MP_TAC THENL [ASM_SIMP_TAC [PID_IMP_UFD, PID_POLY_RING], ALL_TAC] THEN REWRITE_TAC [UFD_EQ_PRIMEFACT] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"f:(1->num)->A")) o CONJUNCT2)) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [POLY_RING_CLAUSES] THEN ASM_MESON_TAC [MONIC_IMP_NONZERO, RING_POLYNOMIAL, FIELD_IMP_NONTRIVIAL_RING], REWRITE_TAC [LEFT_IMP_EXISTS_THM]] THEN MAP_EVERY X_GEN_TAC [(← q r"n:num"), (← q r"p:num->(1->num)->A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"?q. !i. i IN 1..n
            ==> ring_polynomial r (q i) /\ monic r (q i) /\
                ring_irreducible (poly_ring r (:1)) (q i) /\
                ring_associates (poly_ring r (:1)) ((p:num->(1->num)->A) i)
                                (q i)") STRIP_ASSUME_TAC THENL [REWRITE_TAC [(← GSYM SKOLEM_THM), RIGHT_EXISTS_IMP_THM, IN_NUMSEG] THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"(p:num->(1->num)->A) i")] FIELD_MONIC_IRREDUCIBLE_ASSOCIATE) THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE, INTEGRAL_DOMAIN_POLY_RING] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"f = ring_product (poly_ring r (:1)) (1..n)
                      (q:num->(1->num)->A)") SUBST1_TAC THENL [MATCH_MP_TAC MONIC_ASSOCIATES_EQ THEN EXISTS_TAC (← q r"r:A ring") THEN ASM_SIMP_TAC [MONIC_POLY_PRODUCT, FINITE_NUMSEG] THEN MATCH_MP_TAC RING_ASSOCIATES_TRANS THEN EXISTS_TAC (← q r"ring_product (poly_ring r (:1)) (1..n)
                  (p:num->(1->num)->A)") THEN CONJ_TAC THENL [ONCE_REWRITE_TAC [RING_ASSOCIATES_SYM] THEN ASM_REWRITE_TAC [], MATCH_MP_TAC RING_ASSOCIATES_PRODUCT THEN ASM_SIMP_TAC [FINITE_NUMSEG]], ALL_TAC] THEN MAP_EVERY EXISTS_TAC [(← q r"IMAGE (q:num->(1->num)->A) (1..n)"), (← q r"\g. CARD {i | i IN 1..n /\ (q:num->(1->num)->A) i = g}")] THEN REWRITE_TAC [FORALL_IN_IMAGE] THEN SIMP_TAC [FINITE_IMAGE, FINITE_NUMSEG] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN ASM_SIMP_TAC [(← GSYM RING_POLYNOMIAL), CARD_EQ_0, FINITE_RESTRICT, FINITE_NUMSEG] THEN REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY), IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"poly_ring (r:A ring) (:1)"), (← q r"q:num->(1->num)->A"), (← q r"q:num->(1->num)->A"), (← q r"1..n")] RING_PRODUCT_IMAGE_GEN) THEN REWRITE_TAC [FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_PRODUCT_EQ THEN REWRITE_TAC [FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN TRANS_TAC EQ_TRANS (← q r"ring_product (poly_ring r (:1)) {j | j IN 1..n /\ q j = q i}
                 (\j. (q:num->(1->num)->A) i)") THEN CONJ_TAC THENL [MATCH_MP_TAC RING_PRODUCT_EQ THEN SIMP_TAC [IN_ELIM_THM], MATCH_MP_TAC RING_PRODUCT_CONST THEN ASM_SIMP_TAC [FINITE_RESTRICT, FINITE_NUMSEG, (← GSYM RING_POLYNOMIAL)]])

  let CYCLOTOMIC_POLY_IRREDUCIBLE_FACTORIZATION ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r6 ← TAUT (← q r"p /\ ~q ==> (p <=> q \/ s /\ t) ==> t")
    prove
      r"!(r:A ring) m.
          field r /\ FINITE(ring_carrier r) /\ coprime(m,CARD(ring_carrier r))
          ==> ?s. FINITE s /\
                  (!g. g IN s
                       ==> g IN ring_carrier(poly_ring r (:1)) /\ monic r g /\
                           ring_irreducible (poly_ring r (:1)) g /\
                           poly_deg r g = order m (CARD(ring_carrier r))) /\
                  cyclotomic_poly r m =
                  ring_product (poly_ring r (:1)) s (\g. g) /\
                  CARD s * order m (CARD(ring_carrier r)) = phi m"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"~(ring_of_num r m = ring_0 (r:A ring))") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_NUM_EQ_0, RING_CHAR_DIVIDES_ORDER, RING_CHAR_EQ_1, FIELD_IMP_NONTRIVIAL_RING, (← ExceptT.mk (NUMBER_RULE (← q r"!c m q. c divides m /\ c divides q /\ coprime(m,q) ==> c = 1")))], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"cyclotomic_poly (r:A ring) m")] MONIC_POLY_IRREDUCIBLE_FACTORIZATION) THEN ASM_REWRITE_TAC [CYCLOTOMIC_POLY_IN_CARRIER, CYCLOTOMIC_POLY_MONIC] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"s:((1->num)->A)->bool"), (← q r"e:((1->num)->A)->num")] THEN STRIP_TAC THEN EXISTS_TAC (← q r"s:((1->num)->A)->bool") THEN SUBGOAL_THEN (← q r"cyclotomic_poly r m = ring_product (poly_ring r (:1)) s (\g:(1->num)->A. g)") ASSUME_TAC THENL [FIRST_ASSUM (fun th => GEN_REWRITE_TAC LAND_CONV [th]) THEN MATCH_MP_TAC RING_PRODUCT_EQ THEN X_GEN_TAC (← q r"g:(1->num)->A") THEN DISCH_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (← do let c := (← ASSUME (← q r"(g:(1->num)->A) IN s")); pure (fun th => MATCH_MP th c))) THEN SUBGOAL_THEN (← q r"(e:((1->num)->A)->num) g = 1") (fun th => ASM_SIMP_TAC [th, RING_POW_1]) THEN MP_TAC (← ISPECL [(← q r"poly_ring (r:A ring) (:1)"), (← q r"g:(1->num)->A"), (← q r"(e:((1->num)->A)->num) g")] RING_SQUAREFREE_POW) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r6 THEN CONJ_TAC THENL [MATCH_MP_TAC RING_SQUAREFREE_DIVISOR THEN EXISTS_TAC (← q r"cyclotomic_poly (r:A ring) m") THEN CONJ_TAC THENL [ASM_SIMP_TAC [CYCLOTOMIC_POLY_SQUAREFREE, FIELD_IMP_INTEGRAL_DOMAIN], ALL_TAC] THEN FIRST_ASSUM (fun th => GEN_REWRITE_TAC RAND_CONV [th]) THEN MP_TAC (← ISPECL [(← q r"poly_ring (r:A ring) (:1)"), (← q r"\g. ring_pow (poly_ring r (:1)) g ((e:((1->num)->A)->num) g)"), (← q r"{g:(1->num)->A}"), (← q r"s:((1->num)->A)->bool")] RING_DIVIDES_PRODUCT_SUBSET) THEN ASM_SIMP_TAC [SING_SUBSET, RING_PRODUCT_SING, RING_POW], ASM_MESON_TAC [ring_irreducible]], FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_eq z1)) then (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); let z3 ← (q r"e:((1->num)->A)->num"); pure (free_in z3 z4)) else pure false))))] THEN SUBGOAL_THEN (← q r"!g:(1->num)->A. g IN s ==> poly_deg r g = order m (CARD(ring_carrier r))") ASSUME_TAC THENL [X_GEN_TAC (← q r"g:(1->num)->A") THEN DISCH_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (← do let c := (← ASSUME (← q r"(g:(1->num)->A) IN s")); pure (fun th => MATCH_MP th c))) THEN MATCH_MP_TAC CYCLOTOMIC_POLY_IRREDUCIBLE_FACTOR_DEG THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"poly_ring (r:A ring) (:1)"), (← q r"\g:(1->num)->A. g"), (← q r"{g:(1->num)->A}"), (← q r"s:((1->num)->A)->bool")] RING_DIVIDES_PRODUCT_SUBSET) THEN ASM_SIMP_TAC [SING_SUBSET, RING_PRODUCT_SING], ALL_TAC] THEN ASM_SIMP_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:num")] CYCLOTOMIC_POLY_DEG) THEN ASM_SIMP_TAC [(← GSYM TRIVIAL_RING_10), FIELD_IMP_NONTRIVIAL_RING] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"\g:(1->num)->A. g"), (← q r"s:((1->num)->A)->bool")] POLY_DEG_PRODUCT_MONIC) THEN ASM_SIMP_TAC [RING_POLYNOMIAL] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN ASM_SIMP_TAC [(← GSYM NSUM_CONST)] THEN MATCH_MP_TAC NSUM_EQ THEN ASM_SIMP_TAC [])

  -- @@RETURN BEGIN
  return { CYCLOTOMIC_POLY_PRODUCT_NONDIVISORS, CYCLOTOMIC_POLY_PRIME_POWER,
           CYCLOTOMIC_POLY_EVAL_1_PRIME_POWER, CYCLOTOMIC_POLY_EVAL_1,
           CYCLOTOMIC_POLY_EVAL_0, CYCLOTOMIC_POLY_SQUAREFREE, CYCLOTOMIC_POLY_RING_CHAR,
           CYCLOTOMIC_POLY_IRREDUCIBLE_FACTOR_DEG, MONIC_POLY_IRREDUCIBLE_FACTORIZATION,
           CYCLOTOMIC_POLY_IRREDUCIBLE_FACTORIZATION }
  -- @@RETURN END

end HolANT.CyclotomicPoly
