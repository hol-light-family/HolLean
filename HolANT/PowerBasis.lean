/- ========================================================================= -/
/- ANT: Trace, norm and discriminant of a number field through ring ...    -/
/- ========================================================================= -/
/- File: HolANT/PowerBasis.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/power_basis.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antpowerbasisdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/products.ml, ANT/algmisc.ml, Library/isum.ml, ANT/integral.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.PowerBasis fills them).

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

namespace HolANT.PowerBasis

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH ALGEBRA_NORM_FREE_BASIS
   ALGEBRA_TRACE_FREE_BASIS ALGEBRA_TRACE_NORM_EQ_IMAGE
   ALGEBRA_TRACE_NORM_INTERMEDIATE ALGEBRA_TRACE_NORM_IN_CARRIER AND_FORALL_THM
   BASIS_COORDINATES BASIS_COORDINATES_UNIQUE CARD_IMAGE_EQ_INJ CARD_NUMSEG_LT
   COEFF_COMPOSE EQ_TRANS EXISTS_UNIQUE_THM EXTENSION EXTENSIONAL_EQ
   FIELD_EXTENSION_SUBFIELD_GENERATED FIELD_EXTENSION_TRANS
   FIELD_IMP_INTEGRAL_DOMAIN FIELD_IMP_NONTRIVIAL_RING
   FIELD_RING_HOMOMORPHISM_MONOMORPHISM FIELD_SUBFIELD_GENERATED FIELD_UNIT
   FINITE_EXTENSION_RING_MATROID FINITE_IMP_ALGEBRAIC_EXTENSION FINITE_NUMSEG_LT
   FORALL_IN_IMAGE FREE_BASIS_FIELD FREE_BASIS_IN_CARRIER FUN_EQ_THM HAS_SIZE
   HAS_SIZE_INDEX HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS IMAGE_I IMP_CONJ_ALT
   IN_ELIM_THM IN_IMAGE IN_SING IN_SUBFIELD_0 I_O_ID I_THM LE_REFL LT
   MATROID_BASIS_LARGE_INDEPENDENT MINIMAL_POLYNOMIAL_IN_CARRIER
   MINIMAL_POLYNOMIAL_MONIC MINIMAL_POLYNOMIAL_POWERS_HAS_SIZE
   MINIMAL_POLYNOMIAL_VANISHES_HOMOMORPHIC_IMAGE MOD_LT_EQ
   MONIC_POLY_EQ_ROOTS_PRODUCT MULT_CLAUSES MUL_MATRIX_EXPAND
   MUL_MATRIX_IN_CARRIER NUMBER_FIELD_ALGEBRAIC NUMBER_FIELD_FREE_BASIS
   NUMBER_FIELD_IMP_FIELD POLY_DEG_MONOMORPHIC_IMAGE
   POLY_DERIV_HOMOMORPHIC_IMAGE POLY_DERIV_IN_CARRIER
   POLY_EVAL_DERIV_RING_PRODUCT_X_MINUS POLY_EXTEND POLY_EXTEND_EVALUATE
   POLY_EXTEND_HOMOMORPHIC_IMAGE PRIME_SUBFIELD_HOMOMORPHISM_EXISTS
   PRIME_SUBFIELD_MONOMORPHIC_IMAGE PRIME_SUBFIELD_SUBFIELD_GENERATED RDIV_LT_EQ
   RING_1 RING_CARRIER_SUBFIELD_GENERATED_SUBSET RING_CHAR_MONOMORPHIC_IMAGE
   RING_CHAR_SUBFIELD_GENERATED RING_DET RING_DET_EQ RING_DET_HOMOMORPHISM
   RING_DET_INDEPENDENT_ROWS RING_DET_MUL RING_DET_TRANSP RING_DET_VANDERMONDE
   RING_HOMOMORPHISMS_EQ_FROM_RING_SPAN
   RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED RING_HOMOMORPHISMS_INDEPENDENT
   RING_HOMOMORPHISM_0 RING_HOMOMORPHISM_1 RING_HOMOMORPHISM_COMPOSE
   RING_HOMOMORPHISM_FROM_SUBRING_GENERATED RING_HOMOMORPHISM_IN_CARRIER
   RING_HOMOMORPHISM_MUL RING_HOMOMORPHISM_NEG RING_HOMOMORPHISM_POW
   RING_HOMOMORPHISM_RING_OF_NUM RING_HOMOMORPHISM_SUBFIELD_INCLUSION
   RING_HOMOMORPHISM_SUM RING_HOMOMORPHISM_SUM_MUL
   RING_INDEPENDENT_MINIMAL_POLYNOMIAL_POWERS RING_MATROID_BASIS
   RING_MATROID_INDEPENDENT RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_MUL
   RING_MUL_RZERO RING_MUL_SYM RING_NEG RING_OF_NUM
   RING_OF_NUM_SUBFIELD_GENERATED RING_POLYNOMIAL RING_POLYNOMIAL_COMPOSE
   RING_POLYNOMIAL_IMP_POWERSERIES RING_POW RING_POW_2
   RING_POW_SUBFIELD_GENERATED RING_PRODUCT_DIFFERENCES_SQUARE RING_PRODUCT_EQ
   RING_PRODUCT_IMAGE RING_SUM_EQ RING_SUM_EQ_0 RING_SUM_IMAGE
   RING_SUM_MUL_MOD_DIV RING_SUM_MUL_SWAP RING_TRACE_DET_SIMILAR_DIAGONAL
   SEPARABLE_EXTENSION_CHAR0 SIMPLE_IMAGE_GEN SING_SUBSET SUBFIELD_GENERATED
   SUBFIELD_GENERATED_MINIMAL SUBFIELD_SUBFIELD_GENERATED
   SUBRING_GENERATED_BY_SUBFIELD_GENERATED SUBSET algebraic_extension
   algebraically_closed_field basis_discriminant extension_degree
   field_extension monic mul_matrix number_field o_DEF o_THM poly_eval
   ring_basis ring_homomorphism ring_homomorphism_extensions ring_monomorphism
   ring_polynomial ring_powerseries ring_spanning : thm)
  deriving Inhabited

/-- What power_basis.ml uses from Session besides theorems. -/
structure PowerBasisDeps where
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
/- power_basis.ml phrases from line 82 to 465                             -/
/- ---------------------------------------------------------------------- -/

structure PowerBasis01 where
  -- @@FIELDS
  NUMBER_FIELD_TRACE_HOMOMORPHISMS : thm
  NUMBER_FIELD_NORM_HOMOMORPHISMS : thm
  NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS : thm
  NUMBER_FIELD_HOMOMORPHISMS_HAS_SIZE : thm
  NUMBER_FIELD_FREE_BASIS_POWERS : thm
  NUMBER_FIELD_DISCRIMINANT_POWER_BASIS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupPowerBasis01 [HolBase] (D : PowerBasisDeps) :
    ExceptT String IO PowerBasis01 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, TAUT, .. } := D
  let { ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH, ALGEBRA_NORM_FREE_BASIS,
        ALGEBRA_TRACE_FREE_BASIS, ALGEBRA_TRACE_NORM_IN_CARRIER, AND_FORALL_THM,
        BASIS_COORDINATES, CARD_IMAGE_EQ_INJ, CARD_NUMSEG_LT, COEFF_COMPOSE, EQ_TRANS,
        EXISTS_UNIQUE_THM, EXTENSION, EXTENSIONAL_EQ,
        FIELD_EXTENSION_SUBFIELD_GENERATED, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_IMP_NONTRIVIAL_RING, FIELD_RING_HOMOMORPHISM_MONOMORPHISM,
        FIELD_SUBFIELD_GENERATED, FIELD_UNIT, FINITE_EXTENSION_RING_MATROID,
        FINITE_IMP_ALGEBRAIC_EXTENSION, FINITE_NUMSEG_LT, FORALL_IN_IMAGE,
        FREE_BASIS_FIELD, FREE_BASIS_IN_CARRIER, FUN_EQ_THM, HAS_SIZE, HAS_SIZE_INDEX,
        HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS, IMP_CONJ_ALT, IN_ELIM_THM, IN_IMAGE,
        IN_SING, I_O_ID, I_THM, LE_REFL, MATROID_BASIS_LARGE_INDEPENDENT,
        MINIMAL_POLYNOMIAL_IN_CARRIER, MINIMAL_POLYNOMIAL_MONIC,
        MINIMAL_POLYNOMIAL_POWERS_HAS_SIZE,
        MINIMAL_POLYNOMIAL_VANISHES_HOMOMORPHIC_IMAGE, MONIC_POLY_EQ_ROOTS_PRODUCT,
        MUL_MATRIX_EXPAND, MUL_MATRIX_IN_CARRIER, NUMBER_FIELD_ALGEBRAIC,
        NUMBER_FIELD_FREE_BASIS, NUMBER_FIELD_IMP_FIELD, POLY_DEG_MONOMORPHIC_IMAGE,
        POLY_DERIV_HOMOMORPHIC_IMAGE, POLY_DERIV_IN_CARRIER,
        POLY_EVAL_DERIV_RING_PRODUCT_X_MINUS, POLY_EXTEND, POLY_EXTEND_EVALUATE,
        POLY_EXTEND_HOMOMORPHIC_IMAGE, PRIME_SUBFIELD_HOMOMORPHISM_EXISTS,
        PRIME_SUBFIELD_SUBFIELD_GENERATED, RING_1,
        RING_CARRIER_SUBFIELD_GENERATED_SUBSET, RING_CHAR_MONOMORPHIC_IMAGE,
        RING_CHAR_SUBFIELD_GENERATED, RING_DET, RING_DET_EQ, RING_DET_HOMOMORPHISM,
        RING_DET_INDEPENDENT_ROWS, RING_DET_MUL, RING_DET_TRANSP, RING_DET_VANDERMONDE,
        RING_HOMOMORPHISMS_EQ_FROM_RING_SPAN,
        RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED, RING_HOMOMORPHISMS_INDEPENDENT,
        RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_1, RING_HOMOMORPHISM_COMPOSE,
        RING_HOMOMORPHISM_FROM_SUBRING_GENERATED, RING_HOMOMORPHISM_IN_CARRIER,
        RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_NEG, RING_HOMOMORPHISM_POW,
        RING_HOMOMORPHISM_SUBFIELD_INCLUSION, RING_HOMOMORPHISM_SUM,
        RING_HOMOMORPHISM_SUM_MUL, RING_INDEPENDENT_MINIMAL_POLYNOMIAL_POWERS,
        RING_MATROID_BASIS, RING_MATROID_INDEPENDENT,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL, RING_MUL_RZERO, RING_MUL_SYM,
        RING_NEG, RING_POLYNOMIAL, RING_POLYNOMIAL_COMPOSE,
        RING_POLYNOMIAL_IMP_POWERSERIES, RING_POW, RING_POW_2,
        RING_PRODUCT_DIFFERENCES_SQUARE, RING_PRODUCT_EQ, RING_PRODUCT_IMAGE,
        RING_SUM_EQ, RING_SUM_EQ_0, RING_SUM_IMAGE, RING_SUM_MUL_SWAP,
        RING_TRACE_DET_SIMILAR_DIAGONAL, SEPARABLE_EXTENSION_CHAR0, SIMPLE_IMAGE_GEN,
        SUBFIELD_GENERATED, SUBRING_GENERATED_BY_SUBFIELD_GENERATED, SUBSET,
        algebraic_extension, algebraically_closed_field, basis_discriminant,
        extension_degree, field_extension, monic, number_field, o_DEF, o_THM,
        poly_eval, ring_basis, ring_homomorphism_extensions, ring_monomorphism,
        ring_polynomial, ring_powerseries, ring_spanning, .. } := D.core1
  -- @@SCOPE END

  let (NUMBER_FIELD_TRACE_HOMOMORPHISMS, NUMBER_FIELD_NORM_HOMOMORPHISMS, NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS) ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"w:num->A"
    let q2 ← q r"q:num->A"
    let q3 ← q r"{j:num | j < n}"
    let q4 ← q r"(e:num->A->B) i"
    let q5 ← q r"l:B ring"
    let q6 ← q r"k:A ring"
    let v7 ← ISPECL [q6, q5, q4, q3, q2, q1] RING_HOMOMORPHISM_SUM_MUL
    let q8 ← q r"i:num"
    let q9 ← q r"ring_sum l {i | i < n}
        (\i. ring_mul l ((c:num->B) i)
               (ring_sum l {j | j < n}
                  (\j. ring_mul l ((g:A->B)((q:num->A) j))
                                  ((e:num->A->B) i (w j)))))"
    let q10 ← q r"l:B ring"
    let q11 ← q r"k:A ring"
    let v12 ← ISPECL [q11, q10] RING_HOMOMORPHISM_0
    let q13 ← q r"{ring_0 k:A}"
    let q14 ← q r"l:B ring"
    let q15 ← q r"k:A ring"
    let q16 ← q r"g:A->B"
    let q17 ← q r"(e:num->A->B) i"
    let v18 ← ISPECL [q17, q16, q15, q14, q13] RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED
    let q19 ← q r"!i j. i < n /\ j < n
            ==> (e:num->A->B) i ((q:num->A) j) = g(q j)"
    let q20 ← q r"!j. j < n ==> (q:num->A) j IN ring_carrier k /\
                    (g:A->B)(q j) IN ring_carrier l"
    let q21 ← q r"q = basis_coordinates (subfield_generated k {ring_0 k},k) (I:A->A)
            n w y"
    let q22 ← q r"y:A"
    let q23 ← q r"w:num->A"
    let q24 ← q r"n:num"
    let q25 ← q r"k:A ring"
    let q26 ← q r"subfield_generated k {ring_0 k:A}"
    let q27 ← q r"I:A->A"
    let v28 ← ISPECL [q27, q26, q25, q24, q23, q22] BASIS_COORDINATES
    let q29 ← q r"y:A"
    let q30 ← q r"c:num->B"
    let q31 ← q r"{i:num | i < n}"
    let q32 ← q r"l:B ring"
    let q33 ← q r"k:A ring"
    let q34 ← q r"e:num->A->B"
    let v35 ← ISPECL [q34, q33, q32, q31, q30] RING_HOMOMORPHISMS_INDEPENDENT
    let q36 ← q r"c:num->B"
    let q37 ← q r"\i j. (e:num->A->B) i ((w:num->A) j)"
    let q38 ← q r"{i:num | i < n}"
    let q39 ← q r"l:B ring"
    let v40 ← ISPECL [q39, q38, q37] RING_DET_INDEPENDENT_ROWS
    let q41 ← q r"!i x. i < n /\ x IN ring_carrier k
            ==> (e:num->A->B) i x IN ring_carrier l"
    let q51 ← q r"!i j. i IN {i | i < n} /\ j IN {i | i < n} /\ ~(i = j)
            ==> ?x. x IN ring_carrier k /\ ~((e:num->A->B) i x = e j x)"
    let p52 ← prove r"!k (l:B ring) n w (e:num->A->B) g.
          field k /\ field l /\
          free_basis (subfield_generated k {ring_0 k},k) I n w /\
          (!i. i < n ==> ring_homomorphism(k,l) (e i)) /\
          (!i j. i < n /\ j < n /\ (!x. x IN ring_carrier k ==> e i x = e j x)
                 ==> i = j) /\
          ring_homomorphism(k,l) g
          ==> ~(ring_det l {i | i < n} (\i j. e i (w j)) = ring_0 l)" (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN q51 MP_TAC THENL [REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o ((checkM (fun z47 => (do let z48 ← (do pure (Prod.snd (← (do let z49 ← (do let z50 ← (pure z47); pure (concl z50)); pure (strip_forall z49))))); pure (is_imp z48)))) o (checkM (fun th => (do let z46 ← (q r"i:num = j"); let z45 ← (do let z42 ← (do pure (Prod.snd (← (do let z43 ← (do let z44 ← (pure th); pure (concl z44)); pure (strip_forall z43))))); liftExcept (rand z42)); pure (z45 == z46)))))) THEN DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FREE_BASIS_IN_CARRIER)) THEN SUBGOAL_THEN q41 ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN MP_TAC v40 THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC q36 THEN STRIP_TAC THEN MP_TAC v35 THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, FINITE_NUMSEG_LT] THEN X_GEN_TAC q29 THEN DISCH_TAC THEN MP_TAC v28 THEN ASM_REWRITE_TAC [I_THM] THEN ABBREV_TAC q21 THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN SUBGOAL_THEN q20 ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN q19 ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC v18 THEN ASM_SIMP_TAC [IN_SING, v12], ALL_TAC] THEN TRANS_TAC EQ_TRANS q9 THEN CONJ_TAC THENL [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC q8 THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN AP_TERM_TAC THEN MP_TAC v7 THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC [IN_ELIM_THM], ALL_TAC] THEN wPart lhand (lhand o rand) RING_SUM_MUL_SWAP THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ_0 THEN ASM_SIMP_TAC [IN_ELIM_THM, RING_MUL_RZERO])
    let lemma_det := p52
    let q53 ← q r"ring_homomorphism(subfield_generated k {ring_0 k},l) (g:A->B)"
    let v54 ← ASSUME q53
    let v55 ← MATCH_MP RING_HOMOMORPHISM_SUM v54
    let q56 ← q r"x:A"
    let q57 ← q r"w:num->A"
    let q58 ← q r"n:num"
    let q59 ← q r"k:A ring"
    let q60 ← q r"subfield_generated k {ring_0 k:A}"
    let q61 ← q r"I:A->A"
    let v62 ← ISPECL [q61, q60, q59, q58, q57, q56] ALGEBRA_TRACE_FREE_BASIS
    let q63 ← q r"x:A"
    let q64 ← q r"w:num->A"
    let q65 ← q r"n:num"
    let q66 ← q r"k:A ring"
    let q67 ← q r"subfield_generated k {ring_0 k:A}"
    let q68 ← q r"I:A->A"
    let v69 ← ISPECL [q68, q67, q66, q65, q64, q63] ALGEBRA_NORM_FREE_BASIS
    let q70 ← q r"l:B ring"
    let q71 ← q r"k:A ring"
    let v72 ← ISPECL [q71, q70] RING_HOMOMORPHISM_0
    let q73 ← q r"{ring_0 k:A}"
    let q74 ← q r"l:B ring"
    let q75 ← q r"k:A ring"
    let q76 ← q r"g:A->B"
    let q77 ← q r"(e:num->A->B) a"
    let v78 ← ISPECL [q77, q76, q75, q74, q73] RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED
    let q79 ← q r"t:num"
    let q80 ← q r"ring_homomorphism(k,l) ((e:num->A->B) a)"
    let v81 ← ASSUME q80
    let v82 ← MATCH_MP RING_HOMOMORPHISM_MUL v81
    let q83 ← q r"w:num->A"
    let q84 ← q r"\i. (X:num->num->A) i b"
    let q85 ← q r"{i:num | i < n}"
    let q86 ← q r"(e:num->A->B) a"
    let q87 ← q r"l:B ring"
    let q88 ← q r"k:A ring"
    let v89 ← ISPECL [q88, q87, q86, q85, q84, q83] RING_HOMOMORPHISM_SUM_MUL
    let q90 ← q r"(e:num->A->B) a"
    let q91 ← q r"b:num"
    let q92 ← q r"x:A"
    let q93 ← q r"w:num->A"
    let q94 ← q r"n:num"
    let q95 ← q r"k:A ring"
    let q96 ← q r"subfield_generated k {ring_0 k:A}"
    let q97 ← q r"I:A->A"
    let v98 ← ISPECL [q97, q96, q95, q94, q93, q92, q91] MUL_MATRIX_EXPAND
    let q99 ← q r"ring_homomorphism(k,l) ((e:num->A->B) a)"
    let q100 ← q r"b:num"
    let q101 ← q r"a:num"
    let q102 ← q r"\i:num. (e:num->A->B) i x"
    let q103 ← q r"\i j:num. (g:A->B)((X:num->num->A) i j)"
    let q104 ← q r"\i j:num. (e:num->A->B) i ((w:num->A) j)"
    let q105 ← q r"{i:num | i < n}"
    let q106 ← q r"l:B ring"
    let v107 ← ISPECL [q106, q105, q104, q103, q102] RING_TRACE_DET_SIMILAR_DIAGONAL
    let q108 ← q r"!i j. i < n /\ j < n
            ==> (X:num->num->A) i j IN
                ring_carrier(subfield_generated k {ring_0 k})"
    let q109 ← q r"X = mul_matrix (subfield_generated k {ring_0 k},k) (I:A->A)
                                n w x"
    let q110 ← q r"k:A ring"
    let q111 ← q r"g:A->B"
    let v112 ← ISPEC q111 I_O_ID
    let v113 ← CONJUNCT2 v112
    let v114 ← SYM v113
    let q115 ← q r"ring_homomorphism(subfield_generated k {ring_0 k},l) (g:A->B)"
    let q125 ← q r"g:A->B"
    let q126 ← q r"e:num->A->B"
    let q127 ← q r"w:num->A"
    let q128 ← q r"n:num"
    let q129 ← q r"l:B ring"
    let q130 ← q r"k:A ring"
    let v131 ← ISPECL [q130, q129, q128, q127, q126, q125] lemma_det
    let p132 ← prove r"!k (l:B ring) n w (e:num->A->B) g x.
          number_field k /\ field l /\
          free_basis (subfield_generated k {ring_0 k},k) I n w /\
          (!i. i < n ==> ring_homomorphism(k,l) (e i)) /\
          (!i j. i < n /\ j < n /\ (!x. x IN ring_carrier k ==> e i x = e j x)
                 ==> i = j) /\
          ring_homomorphism(k,l) g /\ x IN ring_carrier k
          ==> g(algebra_trace (subfield_generated k {ring_0 k},k) I x) =
              ring_sum l {i | i < n} (\i. e i x) /\
              g(algebra_norm (subfield_generated k {ring_0 k},k) I x) =
              ring_product l {i | i < n} (\i. e i x)" (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN MP_TAC v131 THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o ((checkM (fun z121 => (do let z122 ← (do pure (Prod.snd (← (do let z123 ← (do let z124 ← (pure z121); pure (concl z124)); pure (strip_forall z123))))); pure (is_imp z122)))) o (checkM (fun th => (do let z120 ← (q r"i:num = j"); let z119 ← (do let z116 ← (do pure (Prod.snd (← (do let z117 ← (do let z118 ← (pure th); pure (concl z118)); pure (strip_forall z117))))); liftExcept (rand z116)); pure (z119 == z120)))))) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FREE_BASIS_IN_CARRIER)) THEN SUBGOAL_THEN q115 ASSUME_TAC THENL [SUBST1_TAC v114 THEN MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC q110 THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION], ALL_TAC] THEN ABBREV_TAC q109 THEN SUBGOAL_THEN q108 ASSUME_TAC THENL [EXPAND_TAC "X" THEN ASM_SIMP_TAC [MUL_MATRIX_IN_CARRIER], ALL_TAC] THEN MP_TAC v107 THEN REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN ANTS_TAC THENL [ASM_SIMP_TAC [FIELD_UNIT, RING_DET] THEN REPEAT CONJ_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], MAP_EVERY X_GEN_TAC [q101, q100] THEN STRIP_TAC] THEN SUBGOAL_THEN q99 ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC v98 THEN ASM_REWRITE_TAC [I_THM] THEN DISCH_THEN (MP_TAC o (AP_TERM q90)) THEN MP_TAC v89 THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN ANTS_TAC THENL [ASM_MESON_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBSET], DISCH_THEN SUBST1_TAC] THEN ASM_SIMP_TAC [v82] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC q79 THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN MP_TAC v78 THEN ASM_SIMP_TAC [IN_SING, v72] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN MATCH_MP_TAC RING_MUL_SYM THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], DISCH_THEN (CONJUNCTS_THEN (SUBST1_TAC o SYM))] THEN MP_TAC v69 THEN MP_TAC v62 THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION] THEN REPEAT (DISCH_THEN SUBST1_TAC) THEN CONJ_TAC THENL [ASM_SIMP_TAC [v55, FINITE_NUMSEG_LT, IN_ELIM_THM, o_DEF], MATCH_MP_TAC RING_DET_HOMOMORPHISM THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM]])
    let lemma_core := p132
    let q133 ← q r"ring_carrier k:A->bool"
    let q134 ← q r"j:num"
    let q135 ← q r"i:num"
    let q136 ← q r"w:num->A"
    let q137 ← q r"{i:num | i < n}"
    let q138 ← q r"\h:A->B. h x"
    let q139 ← q r"e:num->A->B"
    let q140 ← q r"l:B ring"
    let v141 ← ISPECL [q140, q139, q138, q137] RING_PRODUCT_IMAGE
    let q142 ← q r"{i:num | i < n}"
    let q143 ← q r"\h:A->B. h x"
    let q144 ← q r"e:num->A->B"
    let q145 ← q r"l:B ring"
    let v146 ← ISPECL [q145, q144, q143, q142] RING_SUM_IMAGE
    let q147 ← q r"e:num->A->B"
    let q148 ← q r"n = extension_degree (subfield_generated k {ring_0 k},k) (I:A->A)"
    let q149 ← q r"w:num->A"
    let q150 ← q r"(p ==> q) /\ (p ==> r) <=> p ==> q /\ r"
    let r151 ← TAUT q150
    let p152 ← prove r"(!(k:A ring) (l:B ring) E g x.
          number_field k /\ field l /\
          E HAS_SIZE extension_degree (subfield_generated k {ring_0 k},k) I /\
          (!h. h IN E ==> ring_homomorphism(k,l) h) /\
          E SUBSET EXTENSIONAL(ring_carrier k) /\
          ring_homomorphism(k,l) g /\ x IN ring_carrier k
          ==> g(algebra_trace (subfield_generated k {ring_0 k},k) I x) =
              ring_sum l E (\h. h x)) /\
     (!(k:A ring) (l:B ring) E g x.
          number_field k /\ field l /\
          E HAS_SIZE extension_degree (subfield_generated k {ring_0 k},k) I /\
          (!h. h IN E ==> ring_homomorphism(k,l) h) /\
          E SUBSET EXTENSIONAL(ring_carrier k) /\
          ring_homomorphism(k,l) g /\ x IN ring_carrier k
          ==> g(algebra_norm (subfield_generated k {ring_0 k},k) I x) =
              ring_product l E (\h. h x))" (REWRITE_TAC [AND_FORALL_THM, r151] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM ((X_CHOOSE_TAC q149) o (MATCH_MP NUMBER_FIELD_FREE_BASIS)) THEN FIRST_X_ASSUM (MP_TAC o (MATCH_MP HAS_SIZE_INDEX)) THEN ABBREV_TAC q148 THEN REWRITE_TAC [EXISTS_UNIQUE_THM] THEN DISCH_THEN (X_CHOOSE_THEN q147 (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN DISCH_THEN (fun th => tactic_of do pure (SUBGOAL_THEN (← q r"!i j. i < n /\ j < n /\ (e:num->A->B) i = e j ==> i = j") ASSUME_TAC THENL [ASM_MESON_TAC [th], ALL_TAC] THEN SUBGOAL_THEN (← q r"E = IMAGE (e:num->A->B) {i | i < n}") SUBST_ALL_TAC THENL [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN ASM_MESON_TAC [th], ALL_TAC])) THEN MP_TAC v146 THEN MP_TAC v141 THEN ASM_REWRITE_TAC [IN_ELIM_THM, o_DEF] THEN REPEAT (DISCH_THEN SUBST1_TAC) THEN MATCH_MP_TAC lemma_core THEN EXISTS_TAC q136 THEN RULE_ASSUM_TAC (REWRITE_RULE [FORALL_IN_IMAGE, SUBSET, IN_ELIM_THM]) THEN ASM_REWRITE_TAC [] THEN MAP_EVERY X_GEN_TAC [q135, q134] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC EXTENSIONAL_EQ THEN EXISTS_TAC q133 THEN ASM_SIMP_TAC [])
    let v153 ← CONJ_PAIR p152
    let (th1, th2) := v153
    let q154 ← q r"\i j:num. (e:num->A->B) i ((w:num->A) j)"
    let q155 ← q r"{i:num | i < n}"
    let q156 ← q r"l:B ring"
    let v157 ← ISPECL [q156, q155, q154] RING_DET_TRANSP
    let q158 ← q r"\t j:num. (e:num->A->B) t ((w:num->A) j)"
    let q159 ← q r"\i t:num. (e:num->A->B) t ((w:num->A) i)"
    let q160 ← q r"{i:num | i < n}"
    let q161 ← q r"l:B ring"
    let v162 ← ISPECL [q161, q160, q159, q158] RING_DET_MUL
    let q163 ← q r"!i j. i < n /\ j < n ==> (e:num->A->B) i (w j) IN ring_carrier l"
    let q164 ← q r"ring_homomorphism(k,l) ((e:num->A->B) t)"
    let q165 ← q r"t:num"
    let q166 ← q r"ring_mul k ((w:num->A) a) (w b) IN ring_carrier k"
    let q167 ← q r"b:num"
    let q168 ← q r"a:num"
    let q169 ← q r"ring_det l {i | i < n}
        (\i j. ring_sum l {t | t < n}
                 (\t. ring_mul l ((e:num->A->B) t (w i)) (e t (w j))))"
    let q170 ← q r"\i j:num. algebra_trace (subfield_generated k {ring_0 k},k) (I:A->A)
                   (ring_mul k (w i) (w j))"
    let q171 ← q r"{i:num | i < n}"
    let q172 ← q r"g:A->B"
    let q173 ← q r"l:B ring"
    let q174 ← q r"subfield_generated k {ring_0 k:A}"
    let v175 ← ISPECL [q174, q173, q172, q171, q170] RING_DET_HOMOMORPHISM
    let q176 ← q r"k:A ring"
    let q177 ← q r"g:A->B"
    let v178 ← ISPEC q177 I_O_ID
    let v179 ← CONJUNCT2 v178
    let v180 ← SYM v179
    let q181 ← q r"ring_homomorphism(subfield_generated k {ring_0 k},l) (g:A->B)"
    let q191 ← q r"y:A"
    let q192 ← q r"g:A->B"
    let q193 ← q r"e:num->A->B"
    let q194 ← q r"w:num->A"
    let q195 ← q r"n:num"
    let q196 ← q r"l:B ring"
    let q197 ← q r"k:A ring"
    let v198 ← ISPECL [q197, q196, q195, q194, q193, q192, q191] lemma_core
    let q199 ← q r"!y. y IN ring_carrier k
          ==> (g:A->B)(algebra_trace (subfield_generated k {ring_0 k},k) I y) =
              ring_sum l {i | i < n} (\i. (e:num->A->B) i y)"
    let p200 ← prove r"!(k:A ring) (l:B ring) n w e g.
          number_field k /\ field l /\
          free_basis (subfield_generated k {ring_0 k},k) I n w /\
          (!i. i < n ==> ring_homomorphism(k,l) (e i)) /\
          (!i j. i < n /\ j < n /\
                 (!x. x IN ring_carrier k ==> e i x = e j x)
                 ==> i = j) /\
          ring_homomorphism(k,l) g
          ==> g(basis_discriminant (subfield_generated k {ring_0 k},k) I
                                       n w) =
              ring_pow l (ring_det l {i | i < n} (\i j. e i (w j))) 2" (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN q199 ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC v198 THEN ASM_REWRITE_TAC [] THEN SIMP_TAC [], FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o ((checkM (fun z187 => (do let z188 ← (do pure (Prod.snd (← (do let z189 ← (do let z190 ← (pure z187); pure (concl z190)); pure (strip_forall z189))))); pure (is_imp z188)))) o (checkM (fun th => (do let z186 ← (q r"i:num = j"); let z185 ← (do let z182 ← (do pure (Prod.snd (← (do let z183 ← (do let z184 ← (pure th); pure (concl z184)); pure (strip_forall z183))))); liftExcept (rand z182)); pure (z185 == z186))))))] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FREE_BASIS_IN_CARRIER)) THEN SUBGOAL_THEN q181 ASSUME_TAC THENL [SUBST1_TAC v180 THEN MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC q176 THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION], ALL_TAC] THEN REWRITE_TAC [basis_discriminant] THEN MP_TAC v175 THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT, ALGEBRA_TRACE_NORM_IN_CARRIER] THEN DISCH_THEN SUBST1_TAC THEN TRANS_TAC EQ_TRANS q169 THEN CONJ_TAC THENL [MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [q168, q167] THEN STRIP_TAC THEN SUBGOAL_THEN q166 ASSUME_TAC THENL [ASM_SIMP_TAC [RING_MUL], ALL_TAC] THEN ASM_SIMP_TAC [] THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC q165 THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN SUBGOAL_THEN q164 MP_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN DISCH_THEN (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL th)])), ALL_TAC] THEN SUBGOAL_THEN q163 ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN MP_TAC v162 THEN MP_TAC v157 THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, RING_POW_2, RING_DET])
    let th3 := p200
    pure (th1, th2, th3)

  let NUMBER_FIELD_HOMOMORPHISMS_HAS_SIZE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"(a <=> b) ==> a ==> b")
    prove
      r"!(k:A ring) (l:B ring).
          number_field k /\ algebraically_closed_field l /\ ring_char l = 0
          ==> {h | ring_homomorphism(k,l) h /\ h IN EXTENSIONAL(ring_carrier k)}
              HAS_SIZE extension_degree (subfield_generated k {ring_0 k},k) I"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [number_field])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [algebraically_closed_field]))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring")] PRIME_SUBFIELD_HOMOMORPHISM_EXISTS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"g:A->B")) THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"g:A->B"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"l:B ring")] HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS) THEN ASM_SIMP_TAC [SEPARABLE_EXTENSION_CHAR0, FINITE_IMP_ALGEBRAIC_EXTENSION, RING_CHAR_SUBFIELD_GENERATED] THEN MATCH_MP_TAC r1 THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [ring_homomorphism_extensions, I_THM, EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC (← q r"h:A->B") THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"g:A->B"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"l:B ring"), (← q r"{ring_0(subfield_generated k {ring_0 k:A})}")] RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED) THEN REWRITE_TAC [PRIME_SUBFIELD_SUBFIELD_GENERATED, IN_SING] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"ring_carrier(subfield_generated k {ring_0 k:A})")] RING_HOMOMORPHISM_FROM_SUBRING_GENERATED) THEN ASM_REWRITE_TAC [SUBRING_GENERATED_BY_SUBFIELD_GENERATED], REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_0 k:A}"), (← q r"l:B ring"), (← q r"g:A->B")] RING_HOMOMORPHISM_0) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_HOMOMORPHISM_0) THEN ASM_REWRITE_TAC [(← CONJUNCT1 (← CONJUNCT2 SUBFIELD_GENERATED))] THEN MESON_TAC []])

  let NUMBER_FIELD_FREE_BASIS_POWERS ← prove
    r"!k:A ring a.
        number_field k /\ a IN ring_carrier k /\
        poly_deg (subfield_generated k {ring_0 k})
          (minimal_polynomial (subfield_generated k {ring_0 k},k) I a) =
        extension_degree (subfield_generated k {ring_0 k},k) I
        ==> free_basis (subfield_generated k {ring_0 k},k) I
              (extension_degree (subfield_generated k {ring_0 k},k) I)
              (\i. ring_pow k a i)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [number_field])) THEN SUBGOAL_THEN (← q r"field_extension(subfield_generated k {ring_0 k},k) (I:A->A) /\
    algebraic_over(subfield_generated k {ring_0 k},k) I a") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_EXTENSION_SUBFIELD_GENERATED, NUMBER_FIELD_ALGEBRAIC], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"a:A")] MINIMAL_POLYNOMIAL_POWERS_HAS_SIZE) THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"a:A")] RING_INDEPENDENT_MINIMAL_POLYNOMIAL_POWERS) THEN ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN REWRITE_TAC [HAS_SIZE] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [FREE_BASIS_FIELD, FIELD_SUBFIELD_GENERATED, RING_HOMOMORPHISM_SUBFIELD_INCLUSION] THEN CONJ_TAC THENL [ASM_SIMP_TAC [(← GSYM RING_MATROID_BASIS), FIELD_SUBFIELD_GENERATED, RING_HOMOMORPHISM_SUBFIELD_INCLUSION] THEN MATCH_MP_TAC MATROID_BASIS_LARGE_INDEPENDENT THEN ASM_SIMP_TAC [RING_MATROID_INDEPENDENT, FIELD_SUBFIELD_GENERATED, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, (← GSYM FINITE_EXTENSION_RING_MATROID)] THEN UNDISCH_TAC (← q r"finite_extension(subfield_generated k {ring_0 k},k) (I:A->A)") THEN REWRITE_TAC [FINITE_EXTENSION_RING_MATROID, extension_degree] THEN ASM_SIMP_TAC [LE_REFL], MP_TAC (← ISPECL [(← q r"\i. ring_pow k (a:A) i"), (← q r"{i | i < extension_degree(subfield_generated k {ring_0 k},k)
                 (I:A->A)}")] CARD_IMAGE_EQ_INJ) THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT, CARD_NUMSEG_LT, IN_ELIM_THM]])

  let NUMBER_FIELD_DISCRIMINANT_POWER_BASIS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ q /\ (p /\ q ==> r) ==> p /\ q /\ r")
    prove
      r"!(k:A ring) a f m.
            number_field k /\ a IN ring_carrier k /\
            f = minimal_polynomial (subfield_generated k {ring_0 k},k) I a /\
            m = extension_degree (subfield_generated k {ring_0 k},k) I /\
            poly_deg (subfield_generated k {ring_0 k}) f = m
            ==> basis_discriminant (subfield_generated k {ring_0 k},k) I m
                  (\i. ring_pow k a i) =
                ring_mul k
                  (ring_pow k (ring_neg k (ring_1 k)) ((m * (m - 1)) DIV 2))
                  (algebra_norm (subfield_generated k {ring_0 k},k) I
                     (poly_extend (subfield_generated k {ring_0 k},k) I (\v. a)
                        (poly_deriv (subfield_generated k {ring_0 k}) f)))"
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
                  (\t. ring_sub l (e i a) (e t a))") ASSUME_TAC THENL [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"l:(A#num)ring"), (← q r"\t. (e:num->A->A#num) t a"), (← q r"{t:num | t < m}"), (← q r"i:num")] POLY_EVAL_DERIV_RING_PRODUCT_X_MINUS) THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM], ALL_TAC] THEN ABBREV_TAC (← q r"y = poly_extend (subfield_generated k {ring_0 k},k) (I:A->A) (\v. a)
              (poly_deriv (subfield_generated k {ring_0 k}) f)") THEN SUBGOAL_THEN (← q r"(y:A) IN ring_carrier k") ASSUME_TAC THENL [EXPAND_TAC "y" THEN REWRITE_TAC [POLY_EXTEND], ALL_TAC] THEN SUBGOAL_THEN (← q r"(g:A->A#num)(algebra_norm (subfield_generated k {ring_0 k},k) I y) =
        ring_product l {i | i < m}
          (\i. ring_product l ({t | t < m} DELETE i)
                 (\t. ring_sub l ((e:num->A->A#num) i a) (e t a)))") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:(A#num)ring"), (← q r"IMAGE (e:num->A->A#num) {i | i < m}"), (← q r"g:A->A#num"), (← q r"y:A")] NUMBER_FIELD_NORM_HOMOMORPHISMS) THEN ANTS_TAC THENL [ASM_SIMP_TAC [FORALL_IN_IMAGE, SUBSET, IN_ELIM_THM], DISCH_THEN SUBST1_TAC] THEN wPart lhand (lhand o rand) RING_PRODUCT_IMAGE THEN ANTS_TAC THENL [REWRITE_TAC [IN_ELIM_THM] THEN UNDISCH_TAC (← q r"!i j. i < m /\ j < m ==> ((e:num->A->A#num) i = e j <=> i = j)") THEN MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [o_DEF] THEN MATCH_MP_TAC RING_PRODUCT_EQ THEN ASM_SIMP_TAC [IN_ELIM_THM], ALL_TAC] THEN SUBGOAL_THEN (← q r"(g:A->A#num)(basis_discriminant (subfield_generated k {ring_0 k},k) I
                       m (\i. ring_pow k a i)) =
        ring_pow l (ring_product l {j | j < m}
                     (\j. ring_product l {i | i < j}
                            (\i. ring_sub l ((e:num->A->A#num) j a) (e i a)))) 2") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:(A#num)ring"), (← q r"m:num"), (← q r"\i. ring_pow k (a:A) i"), (← q r"e:num->A->A#num"), (← q r"g:A->A#num")] NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS) THEN ANTS_TAC THENL [ASM_SIMP_TAC [] THEN MAP_EVERY X_GEN_TAC [(← q r"u:num"), (← q r"v:num")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(e:num->A->A#num) u = e v") MP_TAC THENL [MATCH_MP_TAC EXTENSIONAL_EQ THEN EXISTS_TAC (← q r"ring_carrier k:A->bool") THEN ASM_SIMP_TAC [], ASM_SIMP_TAC []], DISCH_THEN SUBST1_TAC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN TRANS_TAC EQ_TRANS (← q r"ring_det l {i | i < m}
            (\i j. ring_pow l ((e:num->A->A#num) i a) j)") THEN CONJ_TAC THENL [MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:(A#num)ring"), (← q r"(e:num->A->A#num) i")] RING_HOMOMORPHISM_POW) THEN ASM_SIMP_TAC [], MP_TAC (← BETA_RULE (← ISPECL [(← q r"l:(A#num)ring"), (← q r"m:num"), (← q r"\i. (e:num->A->A#num) i a")] RING_DET_VANDERMONDE)) THEN ASM_SIMP_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"algebra_norm (subfield_generated k {ring_0 k},k) I (y:A) IN
        ring_carrier k") ASSUME_TAC THENL [MESON_TAC [ALGEBRA_TRACE_NORM_IN_CARRIER, RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBSET], ALL_TAC] THEN UNDISCH_TAC (← q r"ring_monomorphism(k,l) (g:A->A#num)") THEN REWRITE_TAC [ring_monomorphism] THEN DISCH_THEN (MATCH_MP_TAC o CONJUNCT2) THEN REPEAT CONJ_TAC THENL [REWRITE_TAC [basis_discriminant] THEN MESON_TAC [RING_DET, RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBSET], ASM_SIMP_TAC [RING_MUL, RING_POW, RING_NEG, RING_1], ALL_TAC] THEN MAP_EVERY (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP th (← ASSUME (← q r"ring_homomorphism(k,l) (g:A->A#num)"))), RING_POW, RING_NEG, RING_1])) [RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_POW, RING_HOMOMORPHISM_NEG, RING_HOMOMORPHISM_1] THEN MP_TAC (← BETA_RULE (← ISPECL [(← q r"l:(A#num)ring"), (← q r"\i. (e:num->A->A#num) i a"), (← q r"m:num")] RING_PRODUCT_DIFFERENCES_SQUARE)) THEN ASM_SIMP_TAC [])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_TRACE_HOMOMORPHISMS, NUMBER_FIELD_NORM_HOMOMORPHISMS,
           NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS, NUMBER_FIELD_HOMOMORPHISMS_HAS_SIZE,
           NUMBER_FIELD_FREE_BASIS_POWERS, NUMBER_FIELD_DISCRIMINANT_POWER_BASIS }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- power_basis.ml phrases from line 775 to 840                            -/
/- ---------------------------------------------------------------------- -/

structure PowerBasis02 where
  -- @@FIELDS
  NUMBER_FIELD_TRACE_TOWER : thm
  NUMBER_FIELD_NORM_TOWER : thm
  ALGEBRA_TRACE_PRODUCT_BASIS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupPowerBasis02 [HolBase] (D : PowerBasisDeps) :
    ExceptT String IO PowerBasis02 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, RING_RULE, TAUT, .. } := D
  let { ALGEBRA_TRACE_FREE_BASIS, ALGEBRA_TRACE_NORM_EQ_IMAGE,
        ALGEBRA_TRACE_NORM_INTERMEDIATE, ALGEBRA_TRACE_NORM_IN_CARRIER, AND_FORALL_THM,
        BASIS_COORDINATES_UNIQUE, EQ_TRANS, FIELD_EXTENSION_SUBFIELD_GENERATED,
        FIELD_EXTENSION_TRANS, FINITE_NUMSEG_LT, FREE_BASIS_IN_CARRIER, IMAGE_I,
        IN_ELIM_THM, IN_SUBFIELD_0, I_O_ID, I_THM, LT, MOD_LT_EQ, MULT_CLAUSES,
        MUL_MATRIX_EXPAND, MUL_MATRIX_IN_CARRIER, PRIME_SUBFIELD_MONOMORPHIC_IMAGE,
        RDIV_LT_EQ, RING_CARRIER_SUBFIELD_GENERATED_SUBSET,
        RING_HOMOMORPHISM_IN_CARRIER, RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_POW,
        RING_HOMOMORPHISM_RING_OF_NUM, RING_HOMOMORPHISM_SUBFIELD_INCLUSION,
        RING_HOMOMORPHISM_SUM, RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL,
        RING_OF_NUM, RING_OF_NUM_SUBFIELD_GENERATED, RING_POW_SUBFIELD_GENERATED,
        RING_SUM_EQ, RING_SUM_MUL_MOD_DIV, SING_SUBSET, SUBFIELD_GENERATED,
        SUBFIELD_GENERATED_MINIMAL, SUBFIELD_SUBFIELD_GENERATED, SUBSET,
        field_extension, mul_matrix, ring_homomorphism, .. } := D.core1
  -- @@SCOPE END

  let (NUMBER_FIELD_TRACE_TOWER, NUMBER_FIELD_NORM_TOWER) ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"I:A->A"
    let q2 ← q r"k:A ring"
    let q3 ← q r"K:A ring"
    let v4 ← ISPECL [q3, q2, q1] RING_HOMOMORPHISM_RING_OF_NUM
    let q5 ← q r"I:A->A"
    let q6 ← q r"k:A ring"
    let q7 ← q r"K:A ring"
    let v8 ← ISPECL [q7, q6, q5] RING_HOMOMORPHISM_POW
    let q9 ← q r"I:A->A"
    let q10 ← q r"k:A ring"
    let q11 ← q r"K:A ring"
    let v12 ← ISPECL [q11, q10, q9] RING_HOMOMORPHISM_MUL
    let q13 ← q r"algebra_trace (subfield_generated K {ring_0 K},K) I (x:A) IN
    ring_carrier K /\
    algebra_norm (subfield_generated K {ring_0 K},K) I (x:A) IN
    ring_carrier K"
    let v14 ← CONJUNCT2 SUBFIELD_GENERATED
    let q15 ← q r"x:A"
    let q16 ← q r"k:A ring"
    let q17 ← q r"K:A ring"
    let q18 ← q r"subfield_generated K {ring_0 K:A}"
    let q19 ← q r"I:A->A"
    let q20 ← q r"I:A->A"
    let v21 ← ISPECL [q20, q19, q18, q17, q16, q15] ALGEBRA_TRACE_NORM_INTERMEDIATE
    let q22 ← q r"I:A->A"
    let q23 ← q r"k:A ring"
    let q24 ← q r"K:A ring"
    let v25 ← ISPECL [q24, q23, q22] PRIME_SUBFIELD_MONOMORPHIC_IMAGE
    let q26 ← q r"x:A"
    let q27 ← q r"k:A ring"
    let q28 ← q r"subfield_generated k {ring_0 k:A}"
    let q29 ← q r"subfield_generated K {ring_0 K:A}"
    let q30 ← q r"I:A->A"
    let q31 ← q r"I:A->A"
    let v32 ← ISPECL [q31, q30, q29, q28, q27, q26] ALGEBRA_TRACE_NORM_EQ_IMAGE
    let q33 ← q r"(x:A) IN ring_carrier k"
    let q34 ← q r"k:A ring"
    let q35 ← q r"K:A ring"
    let q36 ← q r"subfield_generated K {ring_0 K:A}"
    let q37 ← q r"I:A->A"
    let q38 ← q r"I:A->A"
    let v39 ← ISPECL [q38, q37, q36, q35, q34] FIELD_EXTENSION_TRANS
    let q40 ← q r"field_extension(subfield_generated K {ring_0 K},K) (I:A->A) /\
    field_extension(subfield_generated k {ring_0 k},k) (I:A->A) /\
    field_extension(subfield_generated K {ring_0 K},k) (I:A->A)"
    let q41 ← q r"(p ==> q) /\ (p ==> r) <=> p ==> q /\ r"
    let r42 ← TAUT q41
    let p43 ← prove r"(!(k:A ring) K x.
        number_field k /\ field_extension(K,k) I /\ x IN ring_carrier K
        ==> algebra_trace (subfield_generated k {ring_0 k},k) I x =
            ring_mul k (ring_of_num k (extension_degree (K,k) I))
              (algebra_trace (subfield_generated K {ring_0 K},K) I x)) /\
   (!(k:A ring) K x.
        number_field k /\ field_extension(K,k) I /\ x IN ring_carrier K
        ==> algebra_norm (subfield_generated k {ring_0 k},k) I x =
            ring_pow k (algebra_norm (subfield_generated K {ring_0 K},K) I x)
              (extension_degree (K,k) I))" (REWRITE_TAC [AND_FORALL_THM, r42] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_extension])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN SUBGOAL_THEN q40 STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC [FIELD_EXTENSION_SUBFIELD_GENERATED] THEN MP_TAC v39 THEN ASM_REWRITE_TAC [I_O_ID, FIELD_EXTENSION_SUBFIELD_GENERATED], ALL_TAC] THEN SUBGOAL_THEN q33 ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, I_THM], ALL_TAC] THEN MP_TAC v32 THEN ANTS_TAC THENL [RULE_ASSUM_TAC (REWRITE_RULE [field_extension]) THEN ASM_REWRITE_TAC [IMAGE_I] THEN MP_TAC v25 THEN ASM_REWRITE_TAC [IMAGE_I], REWRITE_TAC [I_THM] THEN DISCH_THEN (CONJUNCTS_THEN (SUBST1_TAC o SYM))] THEN MP_TAC v21 THEN ASM_REWRITE_TAC [I_O_ID, I_THM] THEN DISCH_THEN (CONJUNCTS_THEN SUBST1_TAC) THEN REWRITE_TAC [v14, RING_OF_NUM_SUBFIELD_GENERATED, RING_POW_SUBFIELD_GENERATED] THEN SUBGOAL_THEN q13 STRIP_ASSUME_TAC THENL [MESON_TAC [ALGEBRA_TRACE_NORM_IN_CARRIER, RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC v12 THEN MP_TAC v8 THEN MP_TAC v4 THEN ASM_REWRITE_TAC [I_THM] THEN REPEAT DISCH_TAC THEN ASM_SIMP_TAC [RING_OF_NUM])
    CONJ_PAIR p43

  let ALGEBRA_TRACE_PRODUCT_BASIS ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let v1 ← CONJUNCT2 SUBFIELD_GENERATED
    let q2 ← q r"s:A->bool"
    let q3 ← q r"k:A ring"
    let v4 ← ISPECL [q3, q2] RING_HOMOMORPHISM_SUBFIELD_INCLUSION
    let v5 ← MATCH_MP RING_HOMOMORPHISM_SUM v4
    let q6 ← q r"t:num->bool"
    let q7 ← q r"\i. ring_mul (subfield_generated k s) ((g:num->A) i) (h i)"
    let v8 ← ISPECL [q7, q6] v5
    let p9 ← prove r"!(k:A ring) s t (g:num->A) h.
        FINITE t /\
        (!i. i IN t ==> g i IN ring_carrier(subfield_generated k s) /\
                        h i IN ring_carrier(subfield_generated k s))
        ==> ring_sum (subfield_generated k s) t
              (\i. ring_mul (subfield_generated k s) (g i) (h i)) =
            ring_sum k t (\i. ring_mul k (g i) (h i))" (REPEAT STRIP_TAC THEN MP_TAC v8 THEN ASM_SIMP_TAC [RING_MUL, I_THM, I_O_ID] THEN REWRITE_TAC [v1])
    let sum_lemma := p9
    let v10 ← CONJUNCT2 SUBFIELD_GENERATED
    let q11 ← q r"\i. (b:num->num->A) i i"
    let q12 ← q r"\i. (a:num->num->A) i i"
    let q13 ← q r"R:num"
    let q14 ← q r"P:num"
    let q15 ← q r"subfield_generated k {ring_0 k:A}"
    let v16 ← ISPECL [q15, q14, q13, q12, q11] RING_SUM_MUL_MOD_DIV
    let v17 ← CONJUNCT2 SUBFIELD_GENERATED
    let q18 ← q r"ring_sum (subfield_generated k {ring_0 k}) {t | t < P * R}
      (\t. ring_mul (subfield_generated k {ring_0 k})
             ((a:num->num->A) (t MOD P) (t MOD P))
             ((b:num->num->A) (t DIV P) (t DIV P)))"
    let q19 ← q r"y:A"
    let q20 ← q r"f:num->A"
    let q21 ← q r"R:num"
    let q22 ← q r"subfield_generated k s2:A ring"
    let q23 ← q r"subfield_generated k {ring_0 k:A}"
    let q24 ← q r"I:A->A"
    let v25 ← ISPECL [q24, q23, q22, q21, q20, q19] ALGEBRA_TRACE_FREE_BASIS
    let q26 ← q r"x:A"
    let q27 ← q r"e:num->A"
    let q28 ← q r"P:num"
    let q29 ← q r"subfield_generated k s1:A ring"
    let q30 ← q r"subfield_generated k {ring_0 k:A}"
    let q31 ← q r"I:A->A"
    let v32 ← ISPECL [q31, q30, q29, q28, q27, q26] ALGEBRA_TRACE_FREE_BASIS
    let q33 ← q r"ring_mul k x y:A"
    let q34 ← q r"\t. ring_mul k ((e:num->A) (t MOD P)) ((f:num->A) (t DIV P))"
    let q35 ← q r"P:num * R"
    let q36 ← q r"k:A ring"
    let q37 ← q r"subfield_generated k {ring_0 k:A}"
    let q38 ← q r"I:A->A"
    let v39 ← ISPECL [q38, q37, q36, q35, q34, q33] ALGEBRA_TRACE_FREE_BASIS
    let q40 ← q r"ring_mul r (ring_mul r a e) (ring_mul r b f) =
      ring_mul r (ring_mul r a b) (ring_mul r e (f:A))"
    let r41 ← RING_RULE q40
    let q42 ← q r"v MOD P < P /\ v DIV P < R"
    let q43 ← q r"v:num"
    let q44 ← q r"ring_mul r (ring_mul r x y) (ring_mul r e f) =
        ring_mul r (ring_mul r x e) (ring_mul r y (f:A))"
    let r45 ← RING_RULE q44
    let q46 ← q r"ring_mul k (ring_mul k x ((e:num->A) (t MOD P)))
                 (ring_mul k y ((f:num->A) (t DIV P)))"
    let v47 ← CONJUNCT2 SUBFIELD_GENERATED
    let q48 ← q r"(b:num->num->A) (v DIV P) (t DIV P)"
    let q49 ← q r"(a:num->num->A) (v MOD P) (t MOD P)"
    let q50 ← q r"subfield_generated k {ring_0 k:A}"
    let v51 ← ISPECL [q50, q49, q48] RING_MUL
    let q52 ← q r"~(P = 0) ==> v MOD P < P /\ v DIV P < R"
    let q53 ← q r"v:num"
    let q54 ← q r"u:num"
    let q55 ← q r"\u. ring_mul k ((a:num->num->A) (u MOD P) (t MOD P))
                      ((b:num->num->A) (u DIV P) (t DIV P))"
    let q56 ← q r"ring_mul k (ring_mul k x y)
         (ring_mul k ((e:num->A) (t MOD P)) ((f:num->A) (t DIV P)))"
    let q57 ← q r"\t. ring_mul k ((e:num->A) (t MOD P)) ((f:num->A) (t DIV P))"
    let q58 ← q r"P:num * R"
    let q59 ← q r"k:A ring"
    let q60 ← q r"subfield_generated k {ring_0 k:A}"
    let q61 ← q r"I:A->A"
    let v62 ← ISPECL [q61, q60, q59, q58, q57, q56, q55] BASIS_COORDINATES_UNIQUE
    let q63 ← q r"P = 0"
    let q64 ← q r"~(P = 0) /\ t MOD P < P /\ t DIV P < R"
    let q65 ← q r"!u t. u < P * R /\ t < P * R
          ==> mul_matrix (subfield_generated k {ring_0 k},k) I
                (P * R) (\t. ring_mul k (e (t MOD P)) (f (t DIV P)))
                (ring_mul k x y) u t =
              ring_mul k ((a:num->num->A) (u MOD P) (t MOD P))
                         ((b:num->num->A) (u DIV P) (t DIV P))"
    let q66 ← q r"(y:A) IN ring_carrier(subfield_generated k s2)"
    let q67 ← q r"(x:A) IN ring_carrier(subfield_generated k s1)"
    let q68 ← q r"!i j. i < R /\ j < R
             ==> (b:num->num->A) i j IN
                 ring_carrier(subfield_generated k {ring_0 k})"
    let q69 ← q r"!i j. i < P /\ j < P
             ==> (a:num->num->A) i j IN
                 ring_carrier(subfield_generated k {ring_0 k})"
    let q70 ← q r"free_basis (subfield_generated k {ring_0 k},subfield_generated k s2)
                 I R (f:num->A)"
    let v71 ← ASSUME q70
    let v72 ← MATCH_MP FREE_BASIS_IN_CARRIER v71
    let q73 ← q r"free_basis (subfield_generated k {ring_0 k},subfield_generated k s1)
                 I P (e:num->A)"
    let v74 ← ASSUME q73
    let v75 ← MATCH_MP FREE_BASIS_IN_CARRIER v74
    let q76 ← q r"{ring_0 k:A}"
    let q77 ← q r"k:A ring"
    let v78 ← ISPECL [q77, q76] RING_CARRIER_SUBFIELD_GENERATED_SUBSET
    let q79 ← q r"s2:A->bool"
    let q80 ← q r"k:A ring"
    let v81 ← ISPECL [q80, q79] RING_CARRIER_SUBFIELD_GENERATED_SUBSET
    let q82 ← q r"s1:A->bool"
    let q83 ← q r"k:A ring"
    let v84 ← ISPECL [q83, q82] RING_CARRIER_SUBFIELD_GENERATED_SUBSET
    let q85 ← q r"x IN ring_carrier k /\ y IN ring_carrier k /\
    (!i. i < P ==> (e:num->A) i IN ring_carrier k) /\
    (!i. i < R ==> (f:num->A) i IN ring_carrier k) /\
    (!i j. i < P /\ j < P ==> (a:num->num->A) i j IN ring_carrier k) /\
    (!i j. i < R /\ j < R ==> (b:num->num->A) i j IN ring_carrier k)"
    let v86 ← CONJUNCT2 SUBFIELD_GENERATED
    let q87 ← q r"i:num"
    let q88 ← q r"y:A"
    let q89 ← q r"f:num->A"
    let q90 ← q r"R:num"
    let q91 ← q r"subfield_generated k s2:A ring"
    let q92 ← q r"subfield_generated k {ring_0 k:A}"
    let q93 ← q r"I:A->A"
    let v94 ← ISPECL [q93, q92, q91, q90, q89, q88, q87] MUL_MATRIX_EXPAND
    let q95 ← q r"i:num"
    let q96 ← q r"x:A"
    let q97 ← q r"e:num->A"
    let q98 ← q r"P:num"
    let q99 ← q r"subfield_generated k s1:A ring"
    let q100 ← q r"subfield_generated k {ring_0 k:A}"
    let q101 ← q r"I:A->A"
    let v102 ← ISPECL [q101, q100, q99, q98, q97, q96, q95] MUL_MATRIX_EXPAND
    let q103 ← q r"i:num"
    let q104 ← q r"(!i. i < P
         ==> ring_mul k x (e i) =
             ring_sum k {j | j < P}
               (\j. ring_mul k ((a:num->num->A) j i) (e j))) /\
    (!i. i < R
         ==> ring_mul k y (f i) =
             ring_sum k {j | j < R}
               (\j. ring_mul k ((b:num->num->A) j i) (f j)))"
    let q105 ← q r"(!i j. i < P /\ j < P
           ==> (a:num->num->A) i j IN
               ring_carrier(subfield_generated k {ring_0 k})) /\
    (!i j. i < R /\ j < R
           ==> (b:num->num->A) i j IN
               ring_carrier(subfield_generated k {ring_0 k}))"
    let q106 ← q r"b = mul_matrix (subfield_generated k {ring_0 k},
                              subfield_generated k s2) I R f (y:A)"
    let q107 ← q r"a = mul_matrix (subfield_generated k {ring_0 k},
                              subfield_generated k s1) I P e (x:A)"
    let v108 ← CONJUNCT2 SUBFIELD_GENERATED
    let q109 ← q r"!s. ring_homomorphism(subfield_generated k {ring_0 k},
                          subfield_generated (k:A ring) s) I"
    let q110 ← q r"!s. ring_carrier(subfield_generated k {ring_0 k}) SUBSET
        ring_carrier(subfield_generated (k:A ring) s)"
    prove
      r"!(k:A ring) s1 s2 P R e f x y.
          field k /\
          free_basis (subfield_generated k {ring_0 k},subfield_generated k s1)
                     I P e /\
          free_basis (subfield_generated k {ring_0 k},subfield_generated k s2)
                     I R f /\
          free_basis (subfield_generated k {ring_0 k},k) I (P * R)
                     (\t. ring_mul k (e (t MOD P)) (f (t DIV P))) /\
          x IN ring_carrier(subfield_generated k s1) /\
          y IN ring_carrier(subfield_generated k s2)
          ==> algebra_trace (subfield_generated k {ring_0 k},k) I
                (ring_mul k x y) =
              ring_mul k
                (algebra_trace (subfield_generated k {ring_0 k},
                                subfield_generated k s1) I x)
                (algebra_trace (subfield_generated k {ring_0 k},
                                subfield_generated k s2) I y)"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN q110 ASSUME_TAC THENL [GEN_TAC THEN MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED, SING_SUBSET, IN_SUBFIELD_0], ALL_TAC] THEN SUBGOAL_THEN q109 ASSUME_TAC THENL [GEN_TAC THEN ASM_REWRITE_TAC [ring_homomorphism, v108, I_THM, IMAGE_I], ALL_TAC] THEN ABBREV_TAC q107 THEN ABBREV_TAC q106 THEN SUBGOAL_THEN q105 STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["a", "b"] THEN ASM_MESON_TAC [MUL_MATRIX_IN_CARRIER], ALL_TAC] THEN SUBGOAL_THEN q104 STRIP_ASSUME_TAC THENL [CONJ_TAC THEN X_GEN_TAC q103 THEN DISCH_TAC THENL [MP_TAC v102, MP_TAC v94] THEN ASM_REWRITE_TAC [I_THM] THEN wPart (lhand o lhand) (lhand o rand) sum_lemma THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN (ANTS_TAC THENL [ASM_MESON_TAC [SUBSET, FREE_BASIS_IN_CARRIER], ALL_TAC]) THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [v86] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN q85 STRIP_ASSUME_TAC THENL [MP_TAC v84 THEN MP_TAC v81 THEN MP_TAC v78 THEN MP_TAC v75 THEN MP_TAC v72 THEN MAP_EVERY UNDISCH_TAC [q69, q68, q67, q66] THEN REWRITE_TAC [SUBSET] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN q65 ASSUME_TAC THENL [REPEAT STRIP_TAC THEN REWRITE_TAC [mul_matrix] THEN SUBGOAL_THEN q64 STRIP_ASSUME_TAC THENL [ASM_CASES_TAC q63 THENL [ASM_MESON_TAC [MULT_CLAUSES, LT], ALL_TAC] THEN ASM_SIMP_TAC [MOD_LT_EQ, RDIV_LT_EQ], ALL_TAC] THEN MP_TAC v62 THEN REWRITE_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION, I_THM] THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [ALL_TAC, DISCH_THEN (MP_TAC o (SPEC q54)) THEN ASM_REWRITE_TAC []] THEN CONJ_TAC THENL [X_GEN_TAC q53 THEN DISCH_TAC THEN SUBGOAL_THEN q52 MP_TAC THENL [ASM_SIMP_TAC [MOD_LT_EQ, RDIV_LT_EQ], ASM_REWRITE_TAC [] THEN STRIP_TAC] THEN MP_TAC v51 THEN ASM_SIMP_TAC [v47], ALL_TAC] THEN CONV_TAC SYM_CONV THEN TRANS_TAC EQ_TRANS q46 THEN CONJ_TAC THENL [MATCH_MP_TAC r45 THEN ASM_SIMP_TAC [], ASM_SIMP_TAC []] THEN wPart lhand (lhand o rand) RING_SUM_MUL_MOD_DIV THEN ASM_SIMP_TAC [RING_MUL] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC q43 THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN SUBGOAL_THEN q42 STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [MOD_LT_EQ, RDIV_LT_EQ], ALL_TAC] THEN MATCH_MP_TAC r41 THEN ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC v39 THEN MP_TAC v32 THEN MP_TAC v25 THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION, RING_MUL] THEN REPEAT (DISCH_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC [] THEN TRANS_TAC EQ_TRANS q18 THEN CONJ_TAC THENL [MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC [IN_ELIM_THM, v17], ALL_TAC] THEN MP_TAC v16 THEN ASM_SIMP_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [v10])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_TRACE_TOWER, NUMBER_FIELD_NORM_TOWER,
           ALGEBRA_TRACE_PRODUCT_BASIS }
  -- @@RETURN END

end HolANT.PowerBasis
