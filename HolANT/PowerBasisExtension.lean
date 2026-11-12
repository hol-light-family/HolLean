/- ========================================================================= -/
/- ANT: The different of a power basis over any base field (Euler) ...     -/
/- ========================================================================= -/
/- File: HolANT/PowerBasisExtension.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/power_basis_extension.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antpowerbasisextensiondiff; the rest is by hand.  Its `needs` closure is
  Library/wo.ml, Library/card.ml, Library/matroids.ml, Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/ringtheory.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, ANT/ideal_arith.ml, Library/products.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/dedekind.ml, Library/frag.ml, Library/grouptheory.ml, Library/ring_groups.ml, Library/symmetric_group.ml, Library/galois.ml, Library/finite_fields.ml, ANT/hensel.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ideal_euler.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/norm_index.ml, ANT/classgroup.ml, ANT/prime_split.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/nf_valuation.ml, ANT/integrality.ml, ANT/different.ml, ANT/relative_degree.ml, ANT/dedekind_kummer.ml, ANT/power_basis.ml, ANT/power_basis_index.ml, ANT/finite_field_trace.ml, ANT/different_extension.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.PowerBasisExtension fills them).

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
import HolANT.IdealArith
import HolLibrary.Products
import HolANT.Algmisc
import HolANT.Integral
import HolANT.Dedekind
import HolLibrary.Frag
import HolLibrary.GroupTheory
import HolLibrary.RingGroups
import HolLibrary.SymmetricGroup
import HolLibrary.Galois
import HolLibrary.FiniteFields
import HolANT.Hensel
import HolANT.DedekindStruct
import HolANT.IdealNorm
import HolANT.IdealEuler
import HolLibrary.Isum
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolANT.RingOfIntegers
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.NormIndex
import HolANT.Classgroup
import HolANT.PrimeSplit
import HolANT.Discriminant
import HolANT.TraceForm
import HolANT.RelativeSplit
import HolANT.NfValuation
import HolANT.Integrality
import HolANT.Different
import HolANT.RelativeDegree
import HolANT.DedekindKummer
import HolANT.PowerBasis
import HolANT.PowerBasisIndex
import HolANT.FiniteFieldTrace
import HolANT.DifferentExtension

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
open HolANT.Hensel
open HolANT.DedekindStruct
open HolANT.IdealNorm
open HolANT.IdealEuler
open HolANT.Zlattice
open HolANT.Numfield
open HolANT.RingOfIntegers
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.NormIndex
open HolANT.Classgroup
open HolANT.PrimeSplit
open HolANT.Discriminant
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.NfValuation
open HolANT.Integrality
open HolANT.Different
open HolANT.RelativeDegree
open HolANT.DedekindKummer
open HolANT.PowerBasis
open HolANT.PowerBasisIndex
open HolANT.FiniteFieldTrace
open HolANT.DifferentExtension

namespace HolANT.PowerBasisExtension

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH
   ALGEBRA_TRACE_MUL_LINCOMB ALGEBRA_TRACE_NORM_EMBEDDINGS_SEPARABLE
   ALGEBRA_TRACE_NORM_IN_CARRIER ALGEBRA_TRACE_SUB ALGEBRA_TRACE_SURJECTIVE
   BASIS_COORDINATES_EXPAND BASIS_COORDINATES_IN_CARRIER
   BASIS_DISCRIMINANT_TIMES_COORD CARD_NUMSEG_LT COEFF_COMPOSE
   COEFF_IN_CARRIER_ALT DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT
   DEDEKIND_IDEAL_SUBSET_POW_VALUATION DEDEKIND_IMP_INTEGRAL_DOMAIN
   DEDEKIND_IN_IDEAL_POW_VALUATION DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL
   DEDEKIND_RESIDUE_GENERATOR_UNIFORMIZER DEDEKIND_RING_OF_INTEGERS
   DEDEKIND_SUBRING_DENSE EMPTY_SUBSET EQ_IMP EQ_SYM_EQ EQ_TRANS
   EXISTS_UNIQUE_THM EXTENSION EXTENSION_DEGREE_EQ_0
   EXTENSION_DEGREE_LE_SPANNING EXTENSION_LINCOMB_ADD EXTENSION_LINCOMB_LMUL
   FIELD_HOMOMORPHISM_INV FIELD_IMP_INTEGRAL_DOMAIN FIELD_IMP_NONTRIVIAL_RING
   FIELD_MUL_EQ_0 FIELD_MUL_LINV FIELD_MUL_RINV FIELD_NONTRIVIAL
   FIELD_POLY_COFACTOR_COEFFS FIELD_QUOTIENT_RING FIELD_SUBFIELD_GENERATED
   FINITE_DELETE FINITE_EXTENSION_SIMPLE_EQ FINITE_IMP_ALGEBRAIC_EXTENSION
   FINITE_IMP_FIELD_EXTENSION FINITE_NUMSEG_LT FORALL_IN_GSPEC FORALL_IN_IMAGE
   FREE_BASIS_EXTENSION_DEGREE FREE_BASIS_IN_CARRIER FREE_BASIS_SIMPLE_EXTENSION
   FUN_EQ_THM FUN_IN_IMAGE HAS_SIZE_INDEX HAS_SIZE_SEPARABLE_DEGREE
   IDEAL_EXTENSION_POW_SUPPLEMENT IDEAL_GENERATED_EQ_0
   IDEAL_GENERATED_IMAGE_IDEAL_GENERATED IDEAL_GENERATED_INC
   IDEAL_GENERATED_MINIMAL IDEAL_GENERATED_SING_ALT IDEAL_POW_1 IDEAL_POW_SUC
   IDEAL_PRODUCT_SING IDEAL_PROD_COMM IDEAL_PROD_HOMOMORPHIC_IMAGE
   IDEAL_PROD_MONO IDEAL_VALUATION_PRINCIPAL_MUL IMAGE_CLAUSES IMAGE_I
   IMAGE_POLY_EXTEND_1 IMP_CONJ INSERT_SUBSET INTEGRAL_DOMAIN_MUL_EQ_0
   INTEGRAL_DOMAIN_MUL_LCANCEL INTEGRAL_DOMAIN_POLY_RING
   INTEGRAL_DOMAIN_PRODUCT_EQ_0 IN_DELETE IN_ELIM_THM IN_IMAGE IN_INSERT
   IN_INTER IN_RING_IDEAL_0 IN_SING IN_SUBRING_0 IN_SUBRING_1 IN_SUBRING_ADD
   IN_SUBRING_MUL IN_SUBRING_POW IN_SUBRING_SUB IN_SUBRING_SUM
   LEFT_AND_EXISTS_THM LEFT_IMP_EXISTS_THM LE_ANTISYM LE_REFL
   MINIMAL_POLYNOMIAL_DEG_LE_EXTENSION_DEGREE MINIMAL_POLYNOMIAL_IN_CARRIER
   MINIMAL_POLYNOMIAL_MONIC MINIMAL_POLYNOMIAL_VANISHES
   MINIMAL_POLYNOMIAL_VANISHES_HOMOMORPHIC_IMAGE MONIC_IMP_NONZERO
   MONIC_POLY_EQ_ROOTS_PRODUCT MONIC_SUBRING_GENERATED MONIC_X_MINUS_A
   MONO_EXISTS NOT_EXISTS_THM NOT_FORALL_THM NOT_IMP
   NUMBER_FIELD_CODIFFERENT_BASIS_DISCRIMINANT NUMBER_FIELD_DIFFERENT_NONZERO
   NUMBER_FIELD_HOMOMORPHIC_PREIMAGE NUMBER_FIELD_IMP_FIELD
   NUMBER_FIELD_INTEGRAL_MULTIPLE NUMBER_FIELD_PRIME_FACTORIZATION
   NUMBER_FIELD_PRIME_IDEAL_ABOVE NUMBER_FIELD_TOWER_LAW
   NUMBER_FIELD_TRACE_INTEGRAL POLY_COMPOSE_HOMOMORPHISM_CONST
   POLY_COMPOSE_HOMOMORPHISM_MUL POLY_COMPOSE_HOMOMORPHISM_SUB
   POLY_COMPOSE_HOMOMORPHISM_VAR POLY_DEG_MONOMORPHIC_IMAGE : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (POLY_DEG_SUBRING_GENERATED POLY_DERIV_HOMOMORPHIC_IMAGE POLY_DERIV_IN_CARRIER
   POLY_DERIV_SUBRING_GENERATED POLY_EVAL_DERIV_RING_PRODUCT_X_MINUS POLY_EXTEND
   POLY_EXTEND_EVALUATE POLY_EXTEND_FROM_SUBRING_GENERATED
   POLY_EXTEND_HOMOMORPHIC_IMAGE POLY_RING_CLAUSES POLY_ROOT_DECOMPOSE
   PRIME_IDEAL_IMP_SUBSET PRIME_IMP_RING_IDEAL PRIME_SUBRING_MINIMAL
   QUOTIENT_RING RINGS_EQ RING_0 RING_1 RING_ADD RING_COSET_EQ
   RING_HOMOMORPHISM_0 RING_HOMOMORPHISM_1 RING_HOMOMORPHISM_COMPOSE
   RING_HOMOMORPHISM_EXTENSIONS_SIMPLE_EQ
   RING_HOMOMORPHISM_FROM_SUBRING_GENERATED RING_HOMOMORPHISM_IN_CARRIER
   RING_HOMOMORPHISM_MUL RING_HOMOMORPHISM_POW RING_HOMOMORPHISM_RING_COSET
   RING_HOMOMORPHISM_RING_OF_INT RING_HOMOMORPHISM_RING_OF_INTEGERS
   RING_HOMOMORPHISM_SUBFIELD_INCLUSION RING_HOMOMORPHISM_SUM
   RING_IDEAL_IDEAL_GENERATED RING_IDEAL_IDEAL_POW RING_IDEAL_IDEAL_QUOTIENT
   RING_IDEAL_IMP_SUBSET RING_IDEAL_NUMBER_FIELD_DIFFERENT RING_INV
   RING_MONOMORPHISM_COMPOSE RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_MUL
   RING_MUL_ASSOC RING_MUL_IN_IDEAL_PROD RING_MUL_LID RING_MUL_LZERO
   RING_MUL_RID RING_MUL_RZERO RING_MUL_SYM RING_OF_INT RING_OF_INTEGERS
   RING_OF_INTEGERS_IDEAL_GENERATED_SING_EQ_0
   RING_OF_INTEGERS_MINIMAL_POLYNOMIAL RING_OF_INTEGERS_PRIME_SUBFIELD_CARRIER
   RING_OF_INTEGERS_QUOTIENT_TRACE RING_OF_INTEGERS_SUBFIELD_GENERATED
   RING_OF_INTEGERS_SUBRING RING_OF_INTEGERS_SUBSET
   RING_OF_INTEGERS_SUBSET_CODIFFERENT RING_OF_INT_EQ_0_CHAR_0 RING_POLYNOMIAL
   RING_POLYNOMIAL_COMPOSE RING_POLYNOMIAL_CONST RING_POLYNOMIAL_IMP_POWERSERIES
   RING_POLYNOMIAL_SUB RING_POLYNOMIAL_SUBRING_COEFF RING_POLYNOMIAL_VAR
   RING_POW RING_POWERSERIES_CONST RING_POWERSERIES_VAR RING_PRODUCT
   RING_PRODUCT_DELETE RING_SUB RING_SUB_EQ_0 RING_SUB_LDISTRIB RING_SUB_REFL
   RING_SUB_RZERO RING_SUM RING_SUM_DELTA RING_SUM_EQ RING_SUM_EQ_0
   RING_SUM_IMAGE RING_SUM_LAGRANGE_COEFF RING_SUM_LMUL
   RING_SUM_RING_OF_INTEGERS SEPARABLE_DEGREE_EQ_EXTENSION_DEGREE
   SEPARABLE_EXTENSION_CHAR0 SING_SUBSET SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC
   SUBRING_GENERATED SUBRING_GENERATED_INC SUBRING_GENERATED_INC_GEN
   SUBRING_GENERATED_MINIMAL SUBRING_GENERATED_MONIC_ROOT_SPAN
   SUBRING_GENERATED_MONO SUBRING_GENERATED_SUPERSET SUBRING_SUBRING_GENERATED
   SUBSET SUBSET_ANTISYM SUBSET_ANTISYM_EQ SUBSET_REFL SUBSET_TRANS
   algebraic_extension field_extension free_basis monic number_field
   number_field_codifferent number_field_different o_ASSOC o_DEF o_THM poly_eval
   ring_div ring_homomorphism_extensions ring_monomorphism ring_of_integers
   ring_polynomial ring_powerseries ring_setadd subring_of : thm)
  deriving Inhabited

/-- What power_basis_extension.ml uses from Session besides theorems. -/
structure PowerBasisExtensionDeps where
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
/- power_basis_extension.ml phrases from line 102 to 649                  -/
/- ---------------------------------------------------------------------- -/

structure PowerBasisExtension01 where
  -- @@FIELDS
  FIELD_POWER_BASIS_EMBEDDINGS : thm
  ALGEBRA_TRACE_POWER_BASIS_DUAL : thm
  ALGEBRA_TRACE_FORM_INJECTIVE : thm
  NUMBER_FIELD_SEPARABLE_EXTENSION : thm
  ALGEBRA_TRACE_DUAL_BASIS_EXPANSION : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupPowerBasisExtension01 [HolBase] (D : PowerBasisExtensionDeps) :
    ExceptT String IO PowerBasisExtension01 := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_MESON_TAC, MESON_TAC, RING_RULE, SET_RULE, TAUT, .. } := D
  let { ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD, ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH,
        ALGEBRA_TRACE_MUL_LINCOMB, ALGEBRA_TRACE_NORM_EMBEDDINGS_SEPARABLE,
        ALGEBRA_TRACE_NORM_IN_CARRIER, ALGEBRA_TRACE_SUB, ALGEBRA_TRACE_SURJECTIVE,
        CARD_NUMSEG_LT, COEFF_COMPOSE, COEFF_IN_CARRIER_ALT, EQ_TRANS,
        EXISTS_UNIQUE_THM, EXTENSION, EXTENSION_DEGREE_EQ_0, FIELD_HOMOMORPHISM_INV,
        FIELD_IMP_INTEGRAL_DOMAIN, FIELD_IMP_NONTRIVIAL_RING, FIELD_MUL_RINV,
        FIELD_NONTRIVIAL, FINITE_DELETE, FINITE_IMP_ALGEBRAIC_EXTENSION,
        FINITE_IMP_FIELD_EXTENSION, FINITE_NUMSEG_LT, FORALL_IN_IMAGE,
        FREE_BASIS_IN_CARRIER, FUN_EQ_THM, HAS_SIZE_INDEX, HAS_SIZE_SEPARABLE_DEGREE,
        INTEGRAL_DOMAIN_MUL_LCANCEL, INTEGRAL_DOMAIN_POLY_RING,
        INTEGRAL_DOMAIN_PRODUCT_EQ_0, IN_DELETE, IN_ELIM_THM, IN_IMAGE,
        MINIMAL_POLYNOMIAL_IN_CARRIER, MINIMAL_POLYNOMIAL_MONIC,
        MINIMAL_POLYNOMIAL_VANISHES_HOMOMORPHIC_IMAGE, MONIC_IMP_NONZERO,
        MONIC_POLY_EQ_ROOTS_PRODUCT, MONIC_X_MINUS_A, NOT_EXISTS_THM,
        NUMBER_FIELD_HOMOMORPHIC_PREIMAGE, NUMBER_FIELD_TOWER_LAW,
        POLY_COMPOSE_HOMOMORPHISM_CONST, POLY_COMPOSE_HOMOMORPHISM_MUL,
        POLY_COMPOSE_HOMOMORPHISM_SUB, POLY_COMPOSE_HOMOMORPHISM_VAR,
        POLY_DEG_MONOMORPHIC_IMAGE, .. } := D.core1
  let { POLY_DERIV_HOMOMORPHIC_IMAGE, POLY_DERIV_IN_CARRIER,
        POLY_EVAL_DERIV_RING_PRODUCT_X_MINUS, POLY_EXTEND, POLY_EXTEND_EVALUATE,
        POLY_EXTEND_HOMOMORPHIC_IMAGE, POLY_RING_CLAUSES, RING_0, RING_1,
        RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_1, RING_HOMOMORPHISM_COMPOSE,
        RING_HOMOMORPHISM_EXTENSIONS_SIMPLE_EQ, RING_HOMOMORPHISM_IN_CARRIER,
        RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_POW, RING_INV,
        RING_MONOMORPHISM_COMPOSE, RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL,
        RING_MUL_ASSOC, RING_MUL_LID, RING_MUL_RID, RING_MUL_RZERO, RING_MUL_SYM,
        RING_POLYNOMIAL, RING_POLYNOMIAL_COMPOSE, RING_POLYNOMIAL_CONST,
        RING_POLYNOMIAL_IMP_POWERSERIES, RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_VAR,
        RING_POW, RING_POWERSERIES_CONST, RING_POWERSERIES_VAR, RING_PRODUCT,
        RING_PRODUCT_DELETE, RING_SUB, RING_SUB_EQ_0, RING_SUB_LDISTRIB, RING_SUB_REFL,
        RING_SUM, RING_SUM_DELTA, RING_SUM_EQ, RING_SUM_EQ_0, RING_SUM_IMAGE,
        RING_SUM_LAGRANGE_COEFF, SEPARABLE_DEGREE_EQ_EXTENSION_DEGREE,
        SEPARABLE_EXTENSION_CHAR0, SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC, SUBSET,
        algebraic_extension, field_extension, free_basis, monic, number_field, o_ASSOC,
        o_DEF, o_THM, poly_eval, ring_div, ring_homomorphism_extensions,
        ring_monomorphism, ring_polynomial, ring_powerseries, .. } := D.core2
  -- @@SCOPE END

  let FIELD_POWER_BASIS_EMBEDDINGS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ q /\ (p /\ q ==> r) ==> p /\ q /\ r")
    prove
      r"!(h:A->B) k l a.
          finite_extension(k,l) h /\ separable_extension(k,l) h /\
          a IN ring_carrier l /\
          subring_generated l (a INSERT IMAGE h (ring_carrier k)) = l
          ==> ?(m:(B#num)ring) g e.
                field m /\ ring_monomorphism(k,m) g /\
                (!t. t < extension_degree(k,l) h
                     ==> ring_homomorphism(l,m) (e t) /\
                         (!y. y IN ring_carrier k ==> e t (h y) = g y)) /\
                (!u v. u < extension_degree(k,l) h /\
                       v < extension_degree(k,l) h
                       ==> (e u a = e v a <=> u = v)) /\
                g o minimal_polynomial (k,l) h a =
                ring_product (poly_ring m (:1)) {t | t < extension_degree(k,l) h}
                  (\t. poly_sub m (poly_var m one) (poly_const m (e t a))) /\
                (!t. t < extension_degree(k,l) h
                     ==> e t (poly_extend (k,l) h (\v. a)
                                (poly_deriv k (minimal_polynomial (k,l) h a))) =
                         ring_product m
                           ({s | s < extension_degree(k,l) h} DELETE t)
                           (\s. ring_sub m (e t a) (e s a))) /\
                (!x. x IN ring_carrier l
                     ==> g(algebra_trace (k,l) h x) =
                         ring_sum m {t | t < extension_degree(k,l) h}
                           (\t. e t x))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN ABBREV_TAC (← q r"f = minimal_polynomial (k,l) (h:A->B) a") THEN ABBREV_TAC (← q r"n = extension_degree (k,l) (h:A->B)") THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITE_IMP_FIELD_EXTENSION)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_extension])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN SUBGOAL_THEN (← q r"algebraic_over (k,l) (h:A->B) a") ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP FINITE_IMP_ALGEBRAIC_EXTENSION)) THEN REWRITE_TAC [algebraic_extension] THEN ASM_MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"a:B")] SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) MP_TAC) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o SYM) THEN SUBGOAL_THEN (← q r"ring_polynomial k (f:(1->num)->A) /\ monic k f") STRIP_ASSUME_TAC THENL [EXPAND_TAC "f" THEN ASM_SIMP_TAC [RING_POLYNOMIAL, MINIMAL_POLYNOMIAL_IN_CARRIER, MINIMAL_POLYNOMIAL_MONIC], ALL_TAC] THEN MP_TAC (← ISPEC (← q r"l:B ring") ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN ASM_REWRITE_TAC [algebraic_extension, field_extension] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"m:(B#num)ring") (X_CHOOSE_THEN (← q r"j:B->B#num") STRIP_ASSUME_TAC)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD)) THEN ABBREV_TAC (← q r"g = (j:B->B#num) o (h:A->B)") THEN SUBGOAL_THEN (← q r"ring_monomorphism(k,m) (g:A->B#num)") ASSUME_TAC THENL [EXPAND_TAC "g" THEN MATCH_MP_TAC RING_MONOMORPHISM_COMPOSE THEN EXISTS_TAC (← q r"l:B ring") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) o (checkM (fun th => (do let z4 ← (q r"ring_monomorphism(k,m) (g:A->B#num)"); let z3 ← (do let z2 ← (pure th); pure (concl z2)); pure (z3 == z4)))))) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"g:A->B#num"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"m:(B#num)ring")] HAS_SIZE_SEPARABLE_DEGREE) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring")] SEPARABLE_DEGREE_EQ_EXTENSION_DEGREE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP HAS_SIZE_INDEX)) THEN REWRITE_TAC [EXISTS_UNIQUE_THM] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"e:num->B->B#num") (fun th0 => tactic_of do pure ((← do let (th1, th2) ← (do pure (← CONJ_PAIR th0)); pure (SUBGOAL_THEN (← q r"!u v. u < n /\ v < n ==> ((e:num->B->B#num) u = e v <=> u = v)") ASSUME_TAC THENL [MESON_TAC [th1, th2], ALL_TAC] THEN SUBGOAL_THEN (← q r"IMAGE (e:num->B->B#num) {t | t < n} =       ring_homomorphism_extensions (k,l,m) (h:A->B,g:A->B#num)") ASSUME_TAC THENL [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN MESON_TAC [th1, th2], ALL_TAC] THEN SUBGOAL_THEN (← q r"!t. t < n ==> ring_homomorphism(l,m) ((e:num->B->B#num) t) /\                     (!y. y IN ring_carrier k ==> e t ((h:A->B) y) = g y)") ASSUME_TAC THENL [X_GEN_TAC (← q r"t:num") THEN DISCH_TAC THEN MP_TAC (← SPEC (← q r"t:num") th1) THEN ASM_REWRITE_TAC [] THEN SIMP_TAC [ring_homomorphism_extensions, IN_ELIM_THM], ALL_TAC] THEN SUBGOAL_THEN (← q r"!t. t < n ==> (e:num->B->B#num) t IN                     ring_homomorphism_extensions (k,l,m) (h:A->B,g:A->B#num)") ASSUME_TAC THENL [MESON_TAC [th1], ALL_TAC]))))) THEN SUBGOAL_THEN (← q r"!u v. u < n /\ v < n
            ==> ((e:num->B->B#num) u a = e v a <=> u = v)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN EQ_TAC THENL [ALL_TAC, SIMP_TAC []] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(e:num->B->B#num) u = e v") MP_TAC THENL [ALL_TAC, ASM_SIMP_TAC []] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"g:A->B#num"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"m:(B#num)ring"), (← q r"a:B"), (← q r"(e:num->B->B#num) u"), (← q r"(e:num->B->B#num) v")] RING_HOMOMORPHISM_EXTENSIONS_SIMPLE_EQ) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!t. t < n ==> (e:num->B->B#num) t o (h:A->B) o (f:(1->num)->A) = g o f") ASSUME_TAC THENL [X_GEN_TAC (← q r"t:num") THEN DISCH_TAC THEN REWRITE_TAC [FUN_EQ_THM, o_THM] THEN X_GEN_TAC (← q r"u:1->num") THEN SUBGOAL_THEN (← q r"(f:(1->num)->A) u IN ring_carrier k") MP_TAC THENL [UNDISCH_TAC (← q r"ring_polynomial k (f:(1->num)->A)") THEN SIMP_TAC [ring_polynomial, ring_powerseries], ASM_SIMP_TAC [o_THM]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!t. t < n ==> (e:num->B->B#num) t a IN ring_carrier m") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN EXISTS_TAC (← q r"l:B ring") THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_polynomial m ((g:A->B#num) o f) /\ poly_deg m (g o f) = n /\
      monic m (g o f)") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r1 THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC RING_POLYNOMIAL_COMPOSE THEN EXISTS_TAC (← q r"k:A ring") THEN ASM_REWRITE_TAC [], MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"m:(B#num)ring"), (← q r"g:A->B#num"), (← q r"f:(1->num)->A")] POLY_DEG_MONOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [], STRIP_TAC THEN UNDISCH_TAC (← q r"monic k (f:(1->num)->A)") THEN ASM_REWRITE_TAC [monic, COEFF_COMPOSE] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"m:(B#num)ring"), (← q r"g:A->B#num")] RING_HOMOMORPHISM_1) THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"(g:A->B#num) o (f:(1->num)->A) =
      ring_product (poly_ring m (:1)) {t | t < n}
        (\t. poly_sub m (poly_var m one) (poly_const m ((e:num->B->B#num) t a)))") ASSUME_TAC THENL [MATCH_MP_TAC MONIC_POLY_EQ_ROOTS_PRODUCT THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, (← GSYM RING_POLYNOMIAL), FINITE_NUMSEG_LT, CARD_NUMSEG_LT, IN_ELIM_THM] THEN CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN X_GEN_TAC (← q r"t:num") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"(e:num->B->B#num) t"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"m:(B#num)ring"), (← q r"a:B")] MINIMAL_POLYNOMIAL_VANISHES_HOMOMORPHIC_IMAGE) THEN ASM_SIMP_TAC [(← GSYM o_ASSOC)], ALL_TAC] THEN SUBGOAL_THEN (← q r"!t. t < n
          ==> (e:num->B->B#num) t
                (poly_extend (k,l) h (\v. a) (poly_deriv k f)) =
              poly_eval m (poly_deriv m ((g:A->B#num) o (f:(1->num)->A)))
                (e t a)") ASSUME_TAC THENL [X_GEN_TAC (← q r"t:num") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"m:(B#num)ring"), (← q r"h:A->B"), (← q r"(:1)"), (← q r"\v:1. (a:B)"), (← q r"(e:num->B->B#num) t"), (← q r"poly_deriv k (f:(1->num)->A)")] POLY_EXTEND_HOMOMORPHIC_IMAGE) THEN ASM_SIMP_TAC [POLY_DERIV_IN_CARRIER, (← GSYM RING_POLYNOMIAL), SUBSET, FORALL_IN_IMAGE] THEN DISCH_THEN SUBST1_TAC THEN SUBGOAL_THEN (← q r"ring_homomorphism(k,m) ((e:num->B->B#num) t o (h:A->B))") ASSUME_TAC THENL [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC (← q r"l:B ring") THEN ASM_SIMP_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [POLY_EXTEND_EVALUATE] THEN REWRITE_TAC [poly_eval] THEN BINOP_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"m:(B#num)ring"), (← q r"g:A->B#num"), (← q r"f:(1->num)->A")] POLY_DERIV_HOMOMORPHIC_IMAGE) THEN ASM_SIMP_TAC [RING_POLYNOMIAL_IMP_POWERSERIES] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN REWRITE_TAC [FUN_EQ_THM, o_THM] THEN X_GEN_TAC (← q r"u:1->num") THEN SUBGOAL_THEN (← q r"poly_deriv k (f:(1->num)->A) u IN ring_carrier k") MP_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"f:(1->num)->A")] POLY_DERIV_IN_CARRIER) THEN ASM_REWRITE_TAC [(← GSYM RING_POLYNOMIAL)] THEN SIMP_TAC [(← GSYM RING_POLYNOMIAL), ring_polynomial, ring_powerseries], ASM_SIMP_TAC [o_THM]], REWRITE_TAC [o_DEF]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!t. t < n
          ==> poly_eval m (poly_deriv m ((g:A->B#num) o (f:(1->num)->A)))
                ((e:num->B->B#num) t a) =
              ring_product m ({s | s < n} DELETE t)
                (\s. ring_sub m (e t a) (e s a))") ASSUME_TAC THENL [X_GEN_TAC (← q r"t:num") THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"m:(B#num)ring"), (← q r"\s. (e:num->B->B#num) s a"), (← q r"{s:num | s < n}"), (← q r"t:num")] POLY_EVAL_DERIV_RING_PRODUCT_X_MINUS) THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x. x IN ring_carrier l
          ==> (g:A->B#num) (algebra_trace (k,l) h x) =
              ring_sum m {t | t < n} (\t. (e:num->B->B#num) t x)") ASSUME_TAC THENL [X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"g:A->B#num"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"m:(B#num)ring"), (← q r"x:B")] ALGEBRA_TRACE_NORM_EMBEDDINGS_SEPARABLE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o CONJUNCT2) THEN UNDISCH_TAC (← q r"IMAGE (e:num->B->B#num) {t | t < n} =
        ring_homomorphism_extensions (k,l,m) (h:A->B,g:A->B#num)") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN wPart lhand (lhand o rand) RING_SUM_IMAGE THEN ANTS_TAC THENL [REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [o_DEF], ALL_TAC] THEN MAP_EVERY EXISTS_TAC [(← q r"m:(B#num)ring"), (← q r"g:A->B#num"), (← q r"e:num->B->B#num")] THEN ASM_SIMP_TAC [])

  let ALGEBRA_TRACE_POWER_BASIS_DUAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul r u (ring_mul r v w) = ring_mul r (ring_mul r v u) (w:B)")
    let r57 ← TAUT (← q r"q /\ (q ==> p) ==> p /\ q")
    prove
      r"!(h:A->B) k l a f d b.
          finite_extension(k,l) h /\ separable_extension(k,l) h /\
          a IN ring_carrier l /\
          subring_generated l (a INSERT IMAGE h (ring_carrier k)) = l /\
          f = minimal_polynomial (k,l) h a /\
          d = poly_extend (k,l) h (\v. a) (poly_deriv k f) /\
          b IN ring_carrier(poly_ring l (:1)) /\
          h o f = poly_mul l (poly_sub l (poly_var l one) (poly_const l a)) b
          ==> ~(d = ring_0 l) /\
              !i j. i < extension_degree(k,l) h /\ j < extension_degree(k,l) h
                    ==> algebra_trace (k,l) h
                          (ring_mul l (ring_inv l d)
                             (ring_mul l (ring_pow l a i) (coeff j b))) =
                        if j = i then ring_1 k else ring_0 k"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM (ASSUME_TAC o (SYM o (checkM (fun th => (do if ← (do let z75 ← (do let z76 ← (pure th); pure (concl z76)); pure (is_eq z75)) then (do let z80 ← (q r"(h:A->B) o (f:(1->num)->A)"); let z79 ← (do let z77 ← (do let z78 ← (pure th); pure (concl z78)); liftExcept (lhs z77)); pure (z79 == z80)) else pure false))))) THEN FIRST_X_ASSUM (ASSUME_TAC o (SYM o (checkM (fun th => (do let z74 ← (q r"d:B"); let z73 ← (do let z71 ← (do let z72 ← (pure th); pure (concl z72)); liftExcept (lhs z71)); pure (z73 == z74)))))) THEN FIRST_X_ASSUM (ASSUME_TAC o (SYM o (checkM (fun th => (do let z70 ← (q r"f:(1->num)->A"); let z69 ← (do let z67 ← (do let z68 ← (pure th); pure (concl z68)); liftExcept (lhs z67)); pure (z69 == z70)))))) THEN ABBREV_TAC (← q r"n = extension_degree (k,l) (h:A->B)") THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITE_IMP_FIELD_EXTENSION)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_extension])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN SUBGOAL_THEN (← q r"algebraic_over (k,l) (h:A->B) a") ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP FINITE_IMP_ALGEBRAIC_EXTENSION)) THEN REWRITE_TAC [algebraic_extension] THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_polynomial l (b:(1->num)->B)") ASSUME_TAC THENL [ASM_REWRITE_TAC [RING_POLYNOMIAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_polynomial k (f:(1->num)->A)") ASSUME_TAC THENL [EXPAND_TAC "f" THEN ASM_SIMP_TAC [RING_POLYNOMIAL, MINIMAL_POLYNOMIAL_IN_CARRIER], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"a:B")] FIELD_POWER_BASIS_EMBEDDINGS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"m:(B#num)ring") (X_CHOOSE_THEN (← q r"g:A->B#num") (X_CHOOSE_THEN (← q r"e:num->B->B#num") STRIP_ASSUME_TAC))) THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) o (checkM (fun th => (do let z66 ← (q r"ring_monomorphism(k,m) (g:A->B#num)"); let z65 ← (do let z64 ← (pure th); pure (concl z64)); pure (z65 == z66)))))) THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN) o (checkM (fun th => (do let z63 ← (q r"field(m:(B#num)ring)"); let z62 ← (do let z61 ← (pure th); pure (concl z61)); pure (z62 == z63)))))) THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP FIELD_IMP_NONTRIVIAL_RING) o (checkM (fun th => (do let z60 ← (q r"field(m:(B#num)ring)"); let z59 ← (do let z58 ← (pure th); pure (concl z58)); pure (z59 == z60)))))) THEN SUBGOAL_THEN (← q r"0 < n") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring")] EXTENSION_DEGREE_EQ_0) THEN ASM_REWRITE_TAC [] THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"(d:B) IN ring_carrier l") ASSUME_TAC THENL [EXPAND_TAC "d" THEN REWRITE_TAC [POLY_EXTEND], ALL_TAC] THEN SUBGOAL_THEN (← q r"!t. t < n ==> (e:num->B->B#num) t a IN ring_carrier m") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN EXISTS_TAC (← q r"l:B ring") THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!t. t < n
          ==> ~((e:num->B->B#num) t d = ring_0 m) /\
              e t d = ring_product m ({s | s < n} DELETE t)
                        (\s. ring_sub m (e t a) (e s a))") ASSUME_TAC THENL [X_GEN_TAC (← q r"t:num") THEN DISCH_TAC THEN MATCH_MP_TAC r57 THEN CONJ_TAC THENL [ASM_SIMP_TAC [], DISCH_THEN SUBST1_TAC] THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_PRODUCT_EQ_0, FINITE_DELETE, FINITE_NUMSEG_LT] THEN REWRITE_TAC [IN_DELETE, IN_ELIM_THM, NOT_EXISTS_THM] THEN X_GEN_TAC (← q r"s:num") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"m:(B#num)ring"), (← q r"(e:num->B->B#num) t a"), (← q r"(e:num->B->B#num) s a")] RING_SUB_EQ_0) THEN ASM_SIMP_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN CONJ_TAC THENL [DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"0")) o (checkM (fun th => (do if ← (do if ← (do let z41 ← (do let z42 ← (pure th); pure (concl z42)); pure (is_forall z41)) then (do let z43 ← (do let z44 ← (pure th); pure (concl z44)); canM (fun z45 => (do let z46 ← (pure z45); find_termM (fun z47 => (do let z49 ← (pure z47); let z48 ← (q r"ring_product:((B#num)ring)->(num->bool)->(num->B#num)->B#num"); pure (z48 == z49))) z46)) z43) else pure false) then (do let z50 ← (do let z51 ← (pure th); pure (concl z51)); canM (fun z52 => (do let z53 ← (pure z52); find_termM (fun z54 => (do let z56 ← (pure z54); let z55 ← (q r"d:B"); pure (z55 == z56))) z53)) z50) else pure false))))) THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"m:(B#num)ring"), (← q r"(e:num->B->B#num) 0")] RING_HOMOMORPHISM_0) THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!t. t < n
          ==> (e:num->B->B#num) t o (b:(1->num)->B) =
              ring_product (poly_ring m (:1)) ({s | s < n} DELETE t)
                (\s. poly_sub m (poly_var m one) (poly_const m (e s a)))") ASSUME_TAC THENL [X_GEN_TAC (← q r"t:num") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_homomorphism(l,m) ((e:num->B->B#num) t)") ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN EXISTS_TAC (← q r"poly_ring m (:1):((1->num)->B#num)ring") THEN EXISTS_TAC (← q r"poly_sub m (poly_var m one)
                    (poly_const m ((e:num->B->B#num) t a))") THEN ASM_REWRITE_TAC [INTEGRAL_DOMAIN_POLY_RING] THEN REWRITE_TAC [RING_PRODUCT, (← GSYM RING_POLYNOMIAL)] THEN ASM_SIMP_TAC [RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_CONST] THEN REPEAT CONJ_TAC THENL [REWRITE_TAC [POLY_RING_CLAUSES] THEN MATCH_MP_TAC MONIC_IMP_NONZERO THEN ASM_SIMP_TAC [MONIC_X_MINUS_A, RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_CONST], MATCH_MP_TAC RING_POLYNOMIAL_COMPOSE THEN EXISTS_TAC (← q r"l:B ring") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN REWRITE_TAC [POLY_RING_CLAUSES] THEN TRANS_TAC EQ_TRANS (← q r"(e:num->B->B#num) t o (h:A->B) o (f:(1->num)->A)") THEN CONJ_TAC THENL [FIRST_ASSUM ((fun th => tactic_of do pure (GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [(← SYM th)])) o (checkM (fun th => (do if ← (do let z35 ← (do let z36 ← (pure th); pure (concl z36)); pure (is_eq z35)) then (do let z40 ← (q r"(h:A->B) o (f:(1->num)->A)"); let z39 ← (do let z37 ← (do let z38 ← (pure th); pure (concl z38)); liftExcept (rhs z37)); pure (z39 == z40)) else pure false)))) THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"m:(B#num)ring"), (← q r"(e:num->B->B#num) t"), (← q r"poly_sub l (poly_var l one) (poly_const l (a:B))"), (← q r"b:(1->num)->B")] POLY_COMPOSE_HOMOMORPHISM_MUL) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN CONJ_TAC THEN MATCH_MP_TAC RING_POLYNOMIAL_IMP_POWERSERIES THEN ASM_SIMP_TAC [RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_CONST], DISCH_THEN SUBST1_TAC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"m:(B#num)ring"), (← q r"(e:num->B->B#num) t"), (← q r"poly_var l one:(1->num)->B"), (← q r"poly_const l (a:B):(1->num)->B")] POLY_COMPOSE_HOMOMORPHISM_SUB) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_POWERSERIES_VAR, RING_POWERSERIES_CONST], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [(← MATCH_MP POLY_COMPOSE_HOMOMORPHISM_VAR (← ASSUME (← q r"ring_homomorphism(l,m) ((e:num->B->B#num) t)")))] THEN REWRITE_TAC [(← MATCH_MP POLY_COMPOSE_HOMOMORPHISM_CONST (← CONJ (← ASSUME (← q r"ring_homomorphism(l,m) ((e:num->B->B#num) t)")) (← ASSUME (← q r"(a:B) IN ring_carrier l"))))], ALL_TAC] THEN TRANS_TAC EQ_TRANS (← q r"(g:A->B#num) o (f:(1->num)->A)") THEN CONJ_TAC THENL [REWRITE_TAC [FUN_EQ_THM, o_THM] THEN X_GEN_TAC (← q r"u:1->num") THEN FIRST_ASSUM (MATCH_MP_TAC o (CONJUNCT2 o ((← do let c := (← ASSUME (← q r"t:num < n")); pure (fun th => MATCH_MP th c)) o (checkM (fun th => (do if ← (do let z26 ← (do let z27 ← (pure th); pure (concl z27)); pure (is_forall z26)) then (do let z28 ← (do let z29 ← (pure th); pure (concl z29)); canM (fun z30 => (do let z31 ← (pure z30); find_termM (fun z32 => (do let z34 ← (pure z32); let z33 ← (q r"ring_homomorphism:(B ring#(B#num)ring)->                                 (B->B#num)->bool"); pure (z33 == z34))) z31)) z28) else pure false)))))) THEN UNDISCH_TAC (← q r"ring_polynomial k (f:(1->num)->A)") THEN SIMP_TAC [ring_polynomial, ring_powerseries], ALL_TAC] THEN FIRST_ASSUM (SUBST1_TAC o (checkM (fun th => (do if ← (do let z20 ← (do let z21 ← (pure th); pure (concl z21)); pure (is_eq z20)) then (do let z25 ← (q r"(g:A->B#num) o (f:(1->num)->A)"); let z24 ← (do let z22 ← (do let z23 ← (pure th); pure (concl z23)); liftExcept (lhs z22)); pure (z24 == z25)) else pure false)))) THEN MP_TAC (← ISPECL [(← q r"poly_ring m (:1):((1->num)->B#num)ring"), (← q r"\s. poly_sub m (poly_var m one)
                            (poly_const m ((e:num->B->B#num) s a))"), (← q r"{s:num | s < n}"), (← q r"t:num")] RING_PRODUCT_DELETE) THEN REWRITE_TAC [] THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, (← GSYM RING_POLYNOMIAL), RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_CONST], DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [POLY_RING_CLAUSES]], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"i:num"), (← q r"j:num")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_mul l (ring_inv l d)
        (ring_mul l (ring_pow l a i) (coeff j (b:(1->num)->B))) IN
      ring_carrier l") ASSUME_TAC THENL [MATCH_MP_TAC RING_MUL THEN ASM_SIMP_TAC [RING_INV, RING_MUL, RING_POW, COEFF_IN_CARRIER_ALT], ALL_TAC] THEN UNDISCH_TAC (← q r"ring_monomorphism(k,m) (g:A->B#num)") THEN REWRITE_TAC [ring_monomorphism] THEN DISCH_THEN (MATCH_MP_TAC o CONJUNCT2) THEN REPEAT CONJ_TAC THENL [REWRITE_TAC [ALGEBRA_TRACE_NORM_IN_CARRIER], COND_CASES_TAC THEN REWRITE_TAC [RING_0, RING_1], ALL_TAC] THEN FIRST_ASSUM ((fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP th (← ASSUME (← q r"ring_mul l (ring_inv l d) (ring_mul l (ring_pow l a i)
                (coeff j (b:(1->num)->B))) IN ring_carrier (l:B ring)")))])) o (checkM (fun th => (do if ← (do let z11 ← (do let z12 ← (pure th); pure (concl z12)); pure (is_forall z11)) then (do let z13 ← (do let z14 ← (pure th); pure (concl z14)); canM (fun z15 => (do let z16 ← (pure z15); find_termM (fun z17 => (do let z19 ← (pure z17); let z18 ← (q r"algebra_trace:(A ring#B ring)->(A->B)->B->A"); pure (z18 == z19))) z16)) z13) else pure false)))) THEN MP_TAC (← ISPECL [(← q r"m:(B#num)ring"), (← q r"\t. (e:num->B->B#num) t a"), (← q r"n:num"), (← q r"i:num"), (← q r"j:num")] RING_SUM_LAGRANGE_COEFF) THEN ANTS_TAC THENL [ASM_SIMP_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(g:A->B#num) (if j:num = i then ring_1 k else ring_0 k) =
      if j = i then ring_1 (m:(B#num)ring) else ring_0 m") SUBST1_TAC THENL [COND_CASES_TAC THEN ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_0 (← ASSUME (← q r"ring_homomorphism(k,m) (g:A->B#num)"))), (← MATCH_MP RING_HOMOMORPHISM_1 (← ASSUME (← q r"ring_homomorphism(k,m) (g:A->B#num)")))], ALL_TAC] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"t:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ring_homomorphism(l,m) ((e:num->B->B#num) t)") ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"coeff j (b:(1->num)->B) IN ring_carrier l") ASSUME_TAC THENL [ASM_SIMP_TAC [COEFF_IN_CARRIER_ALT], ALL_TAC] THEN SUBGOAL_THEN (← q r"(e:num->B->B#num) t (coeff j b) =
      coeff j (ring_product (poly_ring m (:1)) ({s | s < n} DELETE t)
                 (\s. poly_sub m (poly_var m one) (poly_const m (e s a))))") ASSUME_TAC THENL [FIRST_ASSUM ((fun th => tactic_of do pure (REWRITE_TAC [(← GSYM (← MATCH_MP th (← ASSUME (← q r"t:num < n"))))])) o (checkM (fun th => (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); pure (is_forall z2)) then (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); canM (fun z6 => (do let z7 ← (pure z6); find_termM (fun z8 => (do let z10 ← (pure z8); let z9 ← (q r"b:(1->num)->B"); pure (z9 == z10))) z7)) z4) else pure false)))) THEN REWRITE_TAC [COEFF_COMPOSE], ALL_TAC] THEN ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL (← ASSUME (← q r"ring_homomorphism(l,m) ((e:num->B->B#num) t)"))), (← MATCH_MP RING_HOMOMORPHISM_POW (← ASSUME (← q r"ring_homomorphism(l,m) ((e:num->B->B#num) t)"))), (← MATCH_MP (← MATCH_MP FIELD_HOMOMORPHISM_INV (← CONJ (← ASSUME (← q r"field(l:B ring)")) (← ASSUME (← q r"ring_homomorphism(l,m) ((e:num->B->B#num) t)")))) (← ASSUME (← q r"(d:B) IN ring_carrier l"))), RING_INV, RING_POW, RING_MUL] THEN REWRITE_TAC [ring_div] THEN MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [RING_INV, RING_POW, RING_PRODUCT, COEFF_IN_CARRIER_ALT, RING_POLYNOMIAL])

  let ALGEBRA_TRACE_FORM_INJECTIVE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r14 ← SET_RULE (← q r"IMAGE (f:B->A) s = t ==> !y. y IN t ==> ?x. x IN s /\ f x = y")
    prove
      r"!(h:A->B) k l n w x y.
          finite_extension(k,l) h /\ separable_extension(k,l) h /\
          free_basis (k,l) h n w /\
          x IN ring_carrier l /\ y IN ring_carrier l /\
          (!i. i < n
               ==> algebra_trace (k,l) h (ring_mul l (w i) x) =
                   algebra_trace (k,l) h (ring_mul l (w i) y))
          ==> x = y"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o ((GEN_REWRITE_RULE id [field_extension]) o (MATCH_MP FINITE_IMP_FIELD_EXTENSION))) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FREE_BASIS_IN_CARRIER)) THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"x:B"), (← q r"y:B")] RING_SUB_EQ_0) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN SUBGOAL_THEN (← q r"!i. i < (n:num)
          ==> algebra_trace (k,l) (h:A->B)
                (ring_mul l (w i) (ring_sub l x y)) = ring_0 k") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN ASM_SIMP_TAC [RING_SUB_LDISTRIB, ALGEBRA_TRACE_SUB, RING_MUL] THEN MATCH_MP_TAC RING_SUB_REFL THEN REWRITE_TAC [ALGEBRA_TRACE_NORM_IN_CARRIER], ALL_TAC] THEN ABBREV_TAC (← q r"z = ring_sub l x (y:B)") THEN SUBGOAL_THEN (← q r"(z:B) IN ring_carrier l") ASSUME_TAC THENL [EXPAND_TAC "z" THEN ASM_SIMP_TAC [RING_SUB], ALL_TAC] THEN ASM_CASES_TAC (← q r"z:B = ring_0 l") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"?u. u IN ring_carrier l /\ algebra_trace (k,l) (h:A->B) u = ring_1 k") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring")] ALGEBRA_TRACE_SURJECTIVE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"ring_1 k:A")) o (MATCH_MP r14))) THEN REWRITE_TAC [RING_1], ALL_TAC] THEN FIRST_ASSUM (MP_TAC o ((SPEC (← q r"ring_mul l (ring_inv l z) (u:B)")) o (CONJUNCT1 o (CONJUNCT2 o ((GEN_REWRITE_RULE id [free_basis]) o (checkM (fun th => (do let z13 ← (q r"free_basis (k,l) (h:A->B) n w"); let z12 ← (do let z11 ← (pure th); pure (concl z11)); pure (z12 == z13))))))))) THEN ASM_SIMP_TAC [RING_MUL, RING_INV] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:num->A") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(u:B) = ring_mul l z (ring_mul l (ring_inv l z) u)") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_MUL_ASSOC, RING_INV, FIELD_MUL_RINV, RING_MUL_LID], ALL_TAC] THEN UNDISCH_TAC (← q r"algebra_trace (k,l) (h:A->B) u = ring_1 k") THEN FIRST_X_ASSUM (SUBST1_TAC o (checkM (fun th => (do let z10 ← (q r"u:B"); let z9 ← (do let z7 ← (do let z8 ← (pure th); pure (concl z8)); liftExcept (lhs z7)); pure (z9 == z10))))) THEN FIRST_X_ASSUM (SUBST1_TAC o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_eq z1)) then (do let z6 ← (q r"ring_mul l (ring_inv l z) (u:B)"); let z5 ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); liftExcept (lhs z3)); pure (z5 == z6)) else pure false)))) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"{i:num | i < n}"), (← q r"c:num->A"), (← q r"w:num->B"), (← q r"z:B")] ALGEBRA_TRACE_MUL_LINCOMB) THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN DISCH_THEN SUBST1_TAC THEN SUBGOAL_THEN (← q r"ring_sum k {i | i < n}
        (\i. ring_mul k ((c:num->A) i)
               (algebra_trace (k,l) (h:A->B) (ring_mul l z (w i)))) =
      ring_0 k") SUBST1_TAC THENL [MATCH_MP_TAC RING_SUM_EQ_0 THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_mul l z ((w:num->B) i) = ring_mul l (w i) z") SUBST1_TAC THENL [MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC [], ASM_SIMP_TAC [RING_MUL_RZERO]], ASM_MESON_TAC [FIELD_NONTRIVIAL]])

  let NUMBER_FIELD_SEPARABLE_EXTENSION ← prove
    r"!k:A ring l:B ring h.
        field k /\ number_field l /\ ring_homomorphism(k,l) h
        ==> finite_extension(k,l) h /\ separable_extension(k,l) h"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SEPARABLE_EXTENSION_CHAR0 THEN ASM_SIMP_TAC [FINITE_IMP_ALGEBRAIC_EXTENSION] THEN ASM_MESON_TAC [number_field, NUMBER_FIELD_HOMOMORPHIC_PREIMAGE])

  let ALGEBRA_TRACE_DUAL_BASIS_EXPANSION ← prove
    r"!(h:A->B) k l n w w' x.
        finite_extension(k,l) h /\ separable_extension(k,l) h /\
        free_basis (k,l) h n w /\ (!j. j < n ==> w' j IN ring_carrier l) /\
        (!i j. i < n /\ j < n
               ==> algebra_trace (k,l) h (ring_mul l (w i) (w' j)) =
                   if i = j then ring_1 k else ring_0 k) /\
        x IN ring_carrier l
        ==> x = ring_sum l {j | j < n}
                  (\j. ring_mul l
                         (h(algebra_trace (k,l) h (ring_mul l (w j) x)))
                         (w' j))"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o ((GEN_REWRITE_RULE id [field_extension]) o (MATCH_MP FINITE_IMP_FIELD_EXTENSION))) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FREE_BASIS_IN_CARRIER)) THEN MATCH_MP_TAC ALGEBRA_TRACE_FORM_INJECTIVE THEN MAP_EVERY EXISTS_TAC [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"n:num"), (← q r"w:num->B")] THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [REWRITE_TAC [RING_SUM], ALL_TAC] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"{j:num | j < n}"), (← q r"\j. algebra_trace (k,l) (h:A->B)
                        (ring_mul l ((w:num->B) j) x)"), (← q r"w':num->B"), (← q r"(w:num->B) i")] ALGEBRA_TRACE_MUL_LINCOMB) THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, ALGEBRA_TRACE_NORM_IN_CARRIER] THEN DISCH_THEN SUBST1_TAC THEN TRANS_TAC EQ_TRANS (← q r"ring_sum k {j | j < n}
      (\j. if j = i
           then algebra_trace (k,l) (h:A->B) (ring_mul l ((w:num->B) i) x)
           else ring_0 k)") THEN CONJ_TAC THENL [ASM_SIMP_TAC [RING_SUM_DELTA, IN_ELIM_THM, ALGEBRA_TRACE_NORM_IN_CARRIER], MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"j:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN ASM_SIMP_TAC [] THEN ASM_CASES_TAC (← q r"j:num = i") THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [RING_MUL_RID, RING_MUL_RZERO, ALGEBRA_TRACE_NORM_IN_CARRIER]])

  -- @@RETURN BEGIN
  return { FIELD_POWER_BASIS_EMBEDDINGS, ALGEBRA_TRACE_POWER_BASIS_DUAL,
           ALGEBRA_TRACE_FORM_INJECTIVE, NUMBER_FIELD_SEPARABLE_EXTENSION,
           ALGEBRA_TRACE_DUAL_BASIS_EXPANSION }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- power_basis_extension.ml phrases from line 695 to 1300                 -/
/- ---------------------------------------------------------------------- -/

structure PowerBasisExtension02 where
  -- @@FIELDS
  NUMBER_FIELD_POWER_BASIS_DATA : thm
  NUMBER_FIELD_CODIFFERENT_POWER_BASIS : thm
  NUMBER_FIELD_POWER_BASIS_GENERATOR : thm
  NUMBER_FIELD_DERIVATIVE_IN_DIFFERENT : thm
  NUMBER_FIELD_DIFFERENT_POWER_BASIS : thm
  NUMBER_FIELD_CODIFFERENT_POWER_BASIS_Q : thm
  NUMBER_FIELD_DERIVATIVE_IN_DIFFERENT_Q : thm
  NUMBER_FIELD_DIFFERENT_POWER_BASIS_Q : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupPowerBasisExtension02 [HolBase] (D : PowerBasisExtensionDeps) (BPowerBasisExtension01 : PowerBasisExtension01) :
    ExceptT String IO PowerBasisExtension02 := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, RING_RULE, SET_TAC, .. } := D
  let { ALGEBRA_TRACE_MUL_LINCOMB, ALGEBRA_TRACE_NORM_IN_CARRIER, EMPTY_SUBSET,
        EQ_SYM_EQ, EXTENSION, EXTENSION_DEGREE_EQ_0, FIELD_MUL_EQ_0, FIELD_MUL_LINV,
        FIELD_MUL_RINV, FIELD_NONTRIVIAL, FIELD_POLY_COFACTOR_COEFFS,
        FIELD_SUBFIELD_GENERATED, FINITE_EXTENSION_SIMPLE_EQ,
        FINITE_IMP_ALGEBRAIC_EXTENSION, FINITE_IMP_FIELD_EXTENSION, FINITE_NUMSEG_LT,
        FORALL_IN_IMAGE, FREE_BASIS_SIMPLE_EXTENSION, FUN_IN_IMAGE,
        IDEAL_GENERATED_SING_ALT, IMAGE_I, IMAGE_POLY_EXTEND_1, INSERT_SUBSET,
        IN_ELIM_THM, IN_IMAGE, IN_INSERT, IN_INTER, IN_SUBRING_0, IN_SUBRING_1,
        IN_SUBRING_MUL, IN_SUBRING_POW, IN_SUBRING_SUM, MINIMAL_POLYNOMIAL_IN_CARRIER,
        MINIMAL_POLYNOMIAL_MONIC, MINIMAL_POLYNOMIAL_VANISHES, MONIC_SUBRING_GENERATED,
        NUMBER_FIELD_HOMOMORPHIC_PREIMAGE, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_INTEGRAL_MULTIPLE, POLY_DEG_MONOMORPHIC_IMAGE, .. } := D.core1
  let { POLY_DEG_SUBRING_GENERATED, POLY_DERIV_IN_CARRIER,
        POLY_DERIV_SUBRING_GENERATED, POLY_EXTEND, POLY_EXTEND_EVALUATE,
        POLY_EXTEND_FROM_SUBRING_GENERATED, POLY_ROOT_DECOMPOSE, PRIME_SUBRING_MINIMAL,
        RINGS_EQ, RING_1, RING_HOMOMORPHISM_1,
        RING_HOMOMORPHISM_FROM_SUBRING_GENERATED, RING_HOMOMORPHISM_IN_CARRIER,
        RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_RING_OF_INT,
        RING_HOMOMORPHISM_RING_OF_INTEGERS, RING_HOMOMORPHISM_SUBFIELD_INCLUSION,
        RING_INV, RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL, RING_MUL_ASSOC,
        RING_MUL_LID, RING_MUL_RID, RING_MUL_SYM, RING_OF_INT, RING_OF_INTEGERS,
        RING_OF_INTEGERS_MINIMAL_POLYNOMIAL, RING_OF_INTEGERS_PRIME_SUBFIELD_CARRIER,
        RING_OF_INTEGERS_SUBFIELD_GENERATED, RING_OF_INTEGERS_SUBRING,
        RING_OF_INTEGERS_SUBSET, RING_OF_INT_EQ_0_CHAR_0, RING_POLYNOMIAL,
        RING_POLYNOMIAL_COMPOSE, RING_POLYNOMIAL_SUBRING_COEFF, RING_POW, RING_SUM_EQ,
        RING_SUM_LMUL, SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC, SUBRING_GENERATED,
        SUBRING_GENERATED_INC, SUBRING_GENERATED_INC_GEN, SUBRING_GENERATED_MINIMAL,
        SUBRING_GENERATED_MONIC_ROOT_SPAN, SUBRING_GENERATED_MONO,
        SUBRING_GENERATED_SUPERSET, SUBRING_SUBRING_GENERATED, SUBSET, SUBSET_ANTISYM,
        algebraic_extension, field_extension, number_field, number_field_codifferent,
        number_field_different, poly_eval, ring_of_integers, subring_of, .. } := D.core2
  let { ALGEBRA_TRACE_DUAL_BASIS_EXPANSION, ALGEBRA_TRACE_POWER_BASIS_DUAL,
        NUMBER_FIELD_SEPARABLE_EXTENSION, .. } := BPowerBasisExtension01
  -- @@SCOPE END

  let NUMBER_FIELD_POWER_BASIS_DATA ← prove
    r"!k:A ring l:B ring h a f d.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        a IN ring_carrier(ring_of_integers l) /\
        subring_generated l (a INSERT IMAGE h (ring_carrier k)) = l /\
        f = minimal_polynomial (k,l) h a /\
        d = poly_extend (k,l) h (\v. a) (poly_deriv k f)
        ==> ?b. b IN ring_carrier(poly_ring l (:1)) /\
                h o f =
                poly_mul l (poly_sub l (poly_var l one) (poly_const l a)) b /\
                ~(extension_degree(k,l) h = 0) /\
                poly_deg k f = extension_degree(k,l) h /\
                coeff (extension_degree(k,l) h - 1) b = ring_1 l /\
                (!j. coeff j b IN
                     ring_carrier(subring_generated l
                      (a INSERT IMAGE h (ring_carrier(ring_of_integers k))))) /\
                ~(d = ring_0 l) /\
                d IN ring_carrier(subring_generated l
                       (a INSERT IMAGE h (ring_carrier(ring_of_integers k)))) /\
                (!i j. i < extension_degree(k,l) h /\
                       j < extension_degree(k,l) h
                       ==> algebra_trace (k,l) h
                             (ring_mul l (ring_inv l d)
                               (ring_mul l (ring_pow l a i) (coeff j b))) =
                           if j = i then ring_1 k else ring_0 k) /\
                ring_carrier(subring_generated l
                  (a INSERT IMAGE h (ring_carrier(ring_of_integers k)))) =
                {ring_sum l {i | i < extension_degree(k,l) h}
                   (\i. ring_mul l (h(c i)) (ring_pow l a i)) |
                 c | !i. c i IN ring_carrier(ring_of_integers k)} /\
                ring_carrier(subring_generated l
                  (a INSERT IMAGE h (ring_carrier(ring_of_integers k)))) SUBSET
                ring_carrier(ring_of_integers l)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM (ASSUME_TAC o (SYM o (checkM (fun th => (do let z18 ← (q r"d:B"); let z17 ← (do let z15 ← (do let z16 ← (pure th); pure (concl z16)); liftExcept (lhs z15)); pure (z17 == z18)))))) THEN FIRST_X_ASSUM (ASSUME_TAC o (SYM o (checkM (fun th => (do let z14 ← (q r"f:(1->num)->A"); let z13 ← (do let z11 ← (do let z12 ← (pure th); pure (concl z12)); liftExcept (lhs z11)); pure (z13 == z14)))))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_SEPARABLE_EXTENSION) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITE_IMP_FIELD_EXTENSION)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_extension])) THEN SUBGOAL_THEN (← q r"(a:B) IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"algebraic_over (k,l) (h:A->B) a") ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP FINITE_IMP_ALGEBRAIC_EXTENSION)) THEN REWRITE_TAC [algebraic_extension] THEN ASM_MESON_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"n = extension_degree (k,l) (h:A->B)") THEN SUBGOAL_THEN (← q r"poly_deg k (f:(1->num)->A) = n") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"a:B")] SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) MP_TAC) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(n = 0)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring")] EXTENSION_DEGREE_EQ_0) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_polynomial k (f:(1->num)->A) /\ monic k f") STRIP_ASSUME_TAC THENL [EXPAND_TAC "f" THEN ASM_SIMP_TAC [RING_POLYNOMIAL, MINIMAL_POLYNOMIAL_IN_CARRIER, MINIMAL_POLYNOMIAL_MONIC], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. coeff i (f:(1->num)->A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"a:B")] RING_OF_INTEGERS_MINIMAL_POLYNOMIAL) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"poly_extend (k,l) (h:A->B) (\v:1. a) f = ring_0 l") ASSUME_TAC THENL [EXPAND_TAC "f" THEN ASM_SIMP_TAC [MINIMAL_POLYNOMIAL_VANISHES], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"(h:A->B) o (f:(1->num)->A)"), (← q r"a:B")] POLY_ROOT_DECOMPOSE) THEN ANTS_TAC THENL [REPEAT CONJ_TAC THENL [MATCH_MP_TAC RING_POLYNOMIAL_COMPOSE THEN EXISTS_TAC (← q r"k:A ring") THEN ASM_REWRITE_TAC [], MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"f:(1->num)->A")] POLY_DEG_MONOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [], ASM_REWRITE_TAC [], UNDISCH_TAC (← q r"poly_extend (k,l) (h:A->B) (\v:1. a) f = ring_0 l") THEN ASM_SIMP_TAC [POLY_EXTEND_EVALUATE, poly_eval]], DISCH_THEN (X_CHOOSE_THEN (← q r"b:(1->num)->B") STRIP_ASSUME_TAC)] THEN EXISTS_TAC (← q r"b:(1->num)->B") THEN ASM_REWRITE_TAC [(← GSYM RING_POLYNOMIAL)] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"a:B"), (← q r"f:(1->num)->A"), (← q r"d:B"), (← q r"b:(1->num)->B")] ALGEBRA_TRACE_POWER_BASIS_DUAL) THEN ASM_REWRITE_TAC [(← GSYM RING_POLYNOMIAL)] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"R = ring_carrier(subring_generated l
          (a INSERT IMAGE (h:A->B) (ring_carrier(ring_of_integers k))))") THEN SUBGOAL_THEN (← q r"ring_homomorphism(ring_of_integers k,l) (h:A->B)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"{x | integral_element (integer_ring,k:A ring)
                                            (ring_of_int k) x}")] RING_HOMOMORPHISM_FROM_SUBRING_GENERATED) THEN ASM_SIMP_TAC [(← GSYM ring_of_integers), RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN SUBGOAL_THEN (← q r"(R:B->bool) subring_of l /\ (a:B) IN R /\
    (!c. c IN ring_carrier(ring_of_integers k) ==> (h:A->B) c IN R)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "R" THEN REWRITE_TAC [SUBRING_SUBRING_GENERATED] THEN SUBGOAL_THEN (← q r"(a:B) INSERT IMAGE (h:A->B) (ring_carrier(ring_of_integers k)) SUBSET
      ring_carrier l") ASSUME_TAC THENL [ASM_REWRITE_TAC [INSERT_SUBSET, SUBSET, FORALL_IN_IMAGE] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN CONJ_TAC THENL [MATCH_MP_TAC SUBRING_GENERATED_INC THEN ASM_REWRITE_TAC [IN_INSERT], REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBRING_GENERATED_INC THEN ASM_REWRITE_TAC [IN_INSERT] THEN DISJ2_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC []], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"f:(1->num)->A"), (← q r"a:B"), (← q r"b:(1->num)->B"), (← q r"R:B->bool")] FIELD_POLY_COFACTOR_COEFFS) THEN ASM_SIMP_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"f IN ring_carrier(poly_ring (ring_of_integers k) (:1)) /\
    monic (ring_of_integers k) (f:(1->num)->A) /\
    poly_deg (ring_of_integers k) f = n /\
    poly_extend (ring_of_integers k,l) (h:A->B) (\v:1. a) f = ring_0 l /\
    poly_deriv (ring_of_integers k) f = poly_deriv k f /\
    poly_extend (ring_of_integers k,l) (h:A->B):(1->B)->((1->num)->A)->B =
    poly_extend (k,l) h") STRIP_ASSUME_TAC THENL [REWRITE_TAC [ring_of_integers, POLY_DERIV_SUBRING_GENERATED, MONIC_SUBRING_GENERATED, POLY_DEG_SUBRING_GENERATED, POLY_EXTEND_FROM_SUBRING_GENERATED] THEN ASM_REWRITE_TAC [(← GSYM RING_POLYNOMIAL)] THEN MATCH_MP_TAC RING_POLYNOMIAL_SUBRING_COEFF THEN ASM_REWRITE_TAC [(← GSYM ring_of_integers)], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"ring_of_integers k:A ring"), (← q r"l:B ring"), (← q r"a:B")] IMAGE_POLY_EXTEND_1) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); pure (is_eq z5)) then (do let z10 ← (q r"d:B"); let z9 ← (do let z7 ← (do let z8 ← (pure th); pure (concl z8)); liftExcept (rhs z7)); pure (z9 == z10)) else pure false))))) THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z4 ← (q r"poly_deriv (ring_of_integers k) (f:(1->num)->A)"); let z3 ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); liftExcept (lhs z1)); pure (z3 == z4)))))) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC [POLY_DERIV_IN_CARRIER], MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"ring_of_integers k:A ring"), (← q r"l:B ring"), (← q r"a:B"), (← q r"f:(1->num)->A")] SUBRING_GENERATED_MONIC_ROOT_SPAN) THEN ASM_REWRITE_TAC [], EXPAND_TAC "R" THEN MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN REWRITE_TAC [RING_OF_INTEGERS_SUBRING] THEN ASM_REWRITE_TAC [INSERT_SUBSET, SUBSET, FORALL_IN_IMAGE] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN ASM_SIMP_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER]])

  let NUMBER_FIELD_CODIFFERENT_POWER_BASIS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r42 ← RING_RULE (← q r"ring_mul r u (ring_mul r v w) = ring_mul r v (ring_mul r u (w:B))")
    let r43 ← RING_RULE (← q r"ring_mul r v (ring_mul r u w) =
        ring_mul r u (ring_mul r v (w:B))")
    prove
      r"!k:A ring l:B ring h a f d.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          a IN ring_carrier(ring_of_integers l) /\
          subring_generated l (a INSERT IMAGE h (ring_carrier k)) = l /\
          f = minimal_polynomial (k,l) h a /\
          d = poly_extend (k,l) h (\v. a) (poly_deriv k f)
          ==> ~(d = ring_0 l) /\
              {x | x IN ring_carrier l /\
                   !y. y IN ring_carrier(subring_generated l
                        (a INSERT IMAGE h (ring_carrier(ring_of_integers k))))
                       ==> algebra_trace (k,l) h (ring_mul l x y) IN
                           ring_carrier(ring_of_integers k)} =
              IMAGE (ring_mul l (ring_inv l d))
                    (ring_carrier(subring_generated l
                       (a INSERT IMAGE h (ring_carrier(ring_of_integers k)))))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM (ASSUME_TAC o (SYM o (checkM (fun th => (do let z60 ← (q r"d:B"); let z59 ← (do let z57 ← (do let z58 ← (pure th); pure (concl z58)); liftExcept (lhs z57)); pure (z59 == z60)))))) THEN FIRST_X_ASSUM (ASSUME_TAC o (SYM o (checkM (fun th => (do let z56 ← (q r"f:(1->num)->A"); let z55 ← (do let z53 ← (do let z54 ← (pure th); pure (concl z54)); liftExcept (lhs z53)); pure (z55 == z56)))))) THEN ABBREV_TAC (← q r"n = extension_degree (k,l) (h:A->B)") THEN ABBREV_TAC (← q r"R = ring_carrier(subring_generated l
            (a INSERT IMAGE (h:A->B) (ring_carrier(ring_of_integers k))))") THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_SEPARABLE_EXTENSION) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITE_IMP_FIELD_EXTENSION)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_extension])) THEN SUBGOAL_THEN (← q r"!c. c IN ring_carrier k ==> (h:A->B) c IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN SUBGOAL_THEN (← q r"!c. c IN ring_carrier(ring_of_integers k) ==> c IN ring_carrier(k:A ring)") ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_SUBSET) THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(a:B) IN ring_carrier l") ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"l:B ring") RING_OF_INTEGERS_SUBSET) THEN UNDISCH_TAC (← q r"(a:B) IN ring_carrier(ring_of_integers l)") THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"algebraic_over (k,l) (h:A->B) a") ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP FINITE_IMP_ALGEBRAIC_EXTENSION)) THEN REWRITE_TAC [algebraic_extension] THEN DISCH_THEN (MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(d:B) IN ring_carrier l") ASSUME_TAC THENL [EXPAND_TAC "d" THEN REWRITE_TAC [POLY_EXTEND], ALL_TAC] THEN SUBGOAL_THEN (← q r"(R:B->bool) subring_of l") ASSUME_TAC THENL [EXPAND_TAC "R" THEN REWRITE_TAC [SUBRING_SUBRING_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"(R:B->bool) SUBSET ring_carrier l") ASSUME_TAC THENL [UNDISCH_TAC (← q r"(R:B->bool) subring_of l") THEN SIMP_TAC [subring_of], ALL_TAC] THEN SUBGOAL_THEN (← q r"(a:B) INSERT IMAGE (h:A->B) (ring_carrier(ring_of_integers k)) SUBSET
      ring_carrier l") ASSUME_TAC THENL [ASM_SIMP_TAC [INSERT_SUBSET, SUBSET, FORALL_IN_IMAGE], ALL_TAC] THEN SUBGOAL_THEN (← q r"(a:B) IN R") ASSUME_TAC THENL [EXPAND_TAC "R" THEN MATCH_MP_TAC SUBRING_GENERATED_INC THEN ASM_REWRITE_TAC [IN_INSERT], ALL_TAC] THEN SUBGOAL_THEN (← q r"!j. ring_pow l (a:B) j IN R") ASSUME_TAC THENL [GEN_TAC THEN MATCH_MP_TAC IN_SUBRING_POW THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!c. c IN ring_carrier(ring_of_integers k) ==> (h:A->B) c IN R") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN EXPAND_TAC "R" THEN MATCH_MP_TAC SUBRING_GENERATED_INC THEN ASM_REWRITE_TAC [IN_INSERT] THEN DISJ2_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"a:B"), (← q r"f:(1->num)->A"), (← q r"d:B")] NUMBER_FIELD_POWER_BASIS_DATA) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"b:(1->num)->B") STRIP_ASSUME_TAC) THEN FIRST_X_ASSUM (ASSUME_TAC o (SYM o (checkM (fun th => (do if ← (do let z47 ← (do let z48 ← (pure th); pure (concl z48)); pure (is_eq z47)) then (do let z52 ← (q r"R:B->bool"); let z51 ← (do let z49 ← (do let z50 ← (pure th); pure (concl z50)); liftExcept (lhs z49)); pure (z51 == z52)) else pure false))))) THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"free_basis (k,l) (h:A->B) n (ring_pow l a)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"a:B")] FREE_BASIS_SIMPLE_EXTENSION) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!j. coeff j (b:(1->num)->B) IN ring_carrier l") ASSUME_TAC THENL [GEN_TAC THEN FIRST_ASSUM (MATCH_MP_TAC o ((REWRITE_RULE [SUBSET]) o (checkM (fun th => (do let z46 ← (q r"(R:B->bool) SUBSET ring_carrier l"); let z45 ← (do let z44 ← (pure th); pure (concl z44)); pure (z45 == z46)))))) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i j. i < n /\ j < n
            ==> algebra_trace (k,l) (h:A->B)
                  (ring_mul l (ring_pow l a i)
                     (ring_mul l (ring_inv l d) (coeff j b))) =
                if i = j then ring_1 k else ring_0 k") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_mul l (ring_pow l a i) (ring_mul l (ring_inv l d) (coeff j b)) =
        ring_mul l (ring_inv l d) (ring_mul l (ring_pow l a i)
          (coeff j (b:(1->num)->B)))") SUBST1_TAC THENL [MATCH_MP_TAC r43 THEN ASM_SIMP_TAC [RING_INV, RING_POW], ASM_SIMP_TAC [] THEN REWRITE_TAC [EQ_SYM_EQ]], ALL_TAC] THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"x:B") THEN REWRITE_TAC [IN_ELIM_THM, IN_IMAGE] THEN EQ_TAC THENL [STRIP_TAC THEN EXISTS_TAC (← q r"ring_sum l {j | j < n}
          (\j. ring_mul l ((h:A->B)(algebra_trace (k,l) h
                                     (ring_mul l (ring_pow l a j) x)))
                          (coeff j (b:(1->num)->B)))") THEN SUBGOAL_THEN (← q r"!j. algebra_trace (k,l) (h:A->B) (ring_mul l (ring_pow l a j) x) IN
            ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [GEN_TAC THEN ONCE_REWRITE_TAC [(← MATCH_MP RING_MUL_SYM (← CONJ (← SPEC (← q r"j:num") (← MATCH_MP RING_POW (← ASSUME (← q r"(a:B) IN ring_carrier l")))) (← ASSUME (← q r"(x:B) IN ring_carrier l"))))] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN CONJ_TAC THENL [ALL_TAC, MATCH_MP_TAC IN_SUBRING_SUM THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_SIMP_TAC []] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"n:num"), (← q r"ring_pow l (a:B)"), (← q r"\j. ring_mul l (ring_inv l d) (coeff j (b:(1->num)->B))"), (← q r"x:B")] ALGEBRA_TRACE_DUAL_BASIS_EXPANSION) THEN ASM_SIMP_TAC [RING_MUL, RING_INV] THEN DISCH_THEN (fun th => GEN_REWRITE_TAC LAND_CONV [th]) THEN wPart rand (rand o rand) RING_SUM_LMUL THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_INV, FINITE_NUMSEG_LT, RING_MUL, ALGEBRA_TRACE_NORM_IN_CARRIER], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"j:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC [] THEN MATCH_MP_TAC r42 THEN ASM_SIMP_TAC [RING_INV, ALGEBRA_TRACE_NORM_IN_CARRIER], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"w:B") (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN SUBGOAL_THEN (← q r"(w:B) IN ring_carrier l") ASSUME_TAC THENL [FIRST_ASSUM (MATCH_MP_TAC o ((REWRITE_RULE [SUBSET]) o (checkM (fun th => (do let z41 ← (q r"(R:B->bool) SUBSET ring_carrier l"); let z40 ← (do let z39 ← (pure th); pure (concl z39)); pure (z40 == z41)))))) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [RING_MUL, RING_INV] THEN X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(y:B) IN ring_carrier l") ASSUME_TAC THENL [FIRST_ASSUM (MATCH_MP_TAC o ((REWRITE_RULE [SUBSET]) o (checkM (fun th => (do let z38 ← (q r"(R:B->bool) SUBSET ring_carrier l"); let z37 ← (do let z36 ← (pure th); pure (concl z36)); pure (z37 == z38)))))) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul l (w:B) y IN R") MP_TAC THENL [MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_REWRITE_TAC [], ALL_TAC] THEN FIRST_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do if ← (do let z23 ← (do let z24 ← (pure th); pure (concl z24)); pure (is_eq z23)) then (do let z28 ← (q r"R:B->bool"); let z27 ← (do let z25 ← (do let z26 ← (pure th); pure (concl z26)); liftExcept (rhs z25)); pure (z27 == z28)) else pure false) then (do let z29 ← (do let z30 ← (pure th); pure (concl z30)); canM (fun z31 => (do let z32 ← (pure z31); find_termM (fun z33 => (do let z35 ← (pure z33); let z34 ← (q r"ring_pow:(B ring)->B->num->B"); pure (z34 == z35))) z32)) z29) else pure false))))) THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:num->A") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"ring_mul l (ring_mul l (ring_inv l d) w) (y:B) =
      ring_mul l (ring_inv l d) (ring_mul l w y)") SUBST1_TAC THENL [ASM_SIMP_TAC [RING_MUL_ASSOC, RING_INV], ALL_TAC] THEN FIRST_X_ASSUM (SUBST1_TAC o (checkM (fun th => (do if ← (do let z17 ← (do let z18 ← (pure th); pure (concl z18)); pure (is_eq z17)) then (do let z22 ← (q r"ring_mul l (w:B) y"); let z21 ← (do let z19 ← (do let z20 ← (pure th); pure (concl z20)); liftExcept (lhs z19)); pure (z21 == z22)) else pure false)))) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"{i:num | i < n}"), (← q r"c:num->A"), (← q r"ring_pow l (a:B)"), (← q r"ring_inv l (d:B)")] ALGEBRA_TRACE_MUL_LINCOMB) THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_NUMSEG_LT, RING_POW, RING_INV], DISCH_THEN SUBST1_TAC] THEN MATCH_MP_TAC IN_SUBRING_SUM THEN REWRITE_TAC [RING_OF_INTEGERS_SUBRING, IN_ELIM_THM] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBRING] THEN SUBGOAL_THEN (← q r"ring_mul l (ring_inv l d) (ring_pow l a i) =
      ring_mul l (ring_inv l d)
        (ring_mul l (ring_pow l a i) (coeff (n - 1) (b:(1->num)->B)))") SUBST1_TAC THENL [ASM_SIMP_TAC [RING_MUL_RID, RING_POW], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o ((SPECL [(← q r"i:num"), (← q r"n - 1")]) o (checkM (fun th => (do if ← (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_forall z1)) then (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); canM (fun z5 => (do let z6 ← (pure z5); find_termM (fun z7 => (do let z9 ← (pure z7); let z8 ← (q r"ring_inv l (d:B)"); pure (z8 == z9))) z6)) z3) else pure false) then (do let z10 ← (do let z11 ← (pure th); pure (concl z11)); canM (fun z12 => (do let z13 ← (pure z12); find_termM (fun z14 => (do let z16 ← (pure z14); let z15 ← (q r"ring_mul l (ring_inv l d) (ring_mul l (ring_pow l a i)           (coeff j (b:(1->num)->B)))"); pure (z15 == z16))) z13)) z10) else pure false))))) THEN ANTS_TAC THENL [ASM_ARITH_TAC, DISCH_THEN SUBST1_TAC] THEN COND_CASES_TAC THEN REWRITE_TAC [RING_OF_INTEGERS_SUBRING, IN_SUBRING_0, IN_SUBRING_1] THEN MESON_TAC [RING_OF_INTEGERS_SUBRING, IN_SUBRING_0, IN_SUBRING_1])

  let NUMBER_FIELD_POWER_BASIS_GENERATOR ← prove
    r"!k:A ring l:B ring h a s.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        a IN ring_carrier l /\ s IN ring_carrier k /\ ~(s = ring_0 k) /\
        (!y. y IN ring_carrier(ring_of_integers l)
             ==> ring_mul l (h s) y IN
                 ring_carrier(subring_generated l
                   (a INSERT IMAGE h (ring_carrier(ring_of_integers k)))))
        ==> subring_generated l (a INSERT IMAGE h (ring_carrier k)) = l"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [SUBRING_GENERATED_SUPERSET] THEN REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP NUMBER_FIELD_IMP_FIELD) o (checkM (fun th => (do let z12 ← (q r"number_field(l:B ring)"); let z11 ← (do let z10 ← (pure th); pure (concl z10)); pure (z11 == z12)))))) THEN SUBGOAL_THEN (← q r"number_field(k:A ring)") ASSUME_TAC THENL [ASM_MESON_TAC [NUMBER_FIELD_HOMOMORPHIC_PREIMAGE], ALL_TAC] THEN SUBGOAL_THEN (← q r"!c. c IN ring_carrier k ==> (h:A->B) c IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"x:B")] NUMBER_FIELD_INTEGRAL_MULTIPLE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"m:int") STRIP_ASSUME_TAC) THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"ring_mul l (ring_of_int l m) (x:B)")) o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_forall z1)) then (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); canM (fun z5 => (do let z6 ← (pure z5); find_termM (fun z7 => (do let z9 ← (pure z7); let z8 ← (q r"ring_of_integers(l:B ring)"); pure (z8 == z9))) z6)) z3) else pure false))))) THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ring_carrier(subring_generated l
      (a INSERT IMAGE (h:A->B) (ring_carrier(ring_of_integers k)))) SUBSET
    ring_carrier(subring_generated l (a INSERT IMAGE h (ring_carrier k)))") MP_TAC THENL [MATCH_MP_TAC SUBRING_GENERATED_MONO THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_SUBSET) THEN SET_TAC [], REWRITE_TAC [SUBSET] THEN DISCH_THEN (fun th => DISCH_THEN (MP_TAC o (MATCH_MP th)))] THEN ABBREV_TAC (← q r"S = ring_carrier(subring_generated l
          (a INSERT IMAGE (h:A->B) (ring_carrier k)))") THEN SUBGOAL_THEN (← q r"(S:B->bool) subring_of l") ASSUME_TAC THENL [EXPAND_TAC "S" THEN REWRITE_TAC [SUBRING_SUBRING_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"!c. c IN ring_carrier k ==> (h:A->B) c IN S") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN EXPAND_TAC "S" THEN MATCH_MP_TAC SUBRING_GENERATED_INC THEN ASM_SIMP_TAC [INSERT_SUBSET, SUBSET, FORALL_IN_IMAGE, IN_INSERT] THEN DISJ2_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"t = ring_mul k s (ring_of_int k m:A)") THEN SUBGOAL_THEN (← q r"(t:A) IN ring_carrier k /\ ~(t = ring_0 k)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "t" THEN ASM_SIMP_TAC [RING_MUL, RING_OF_INT, FIELD_MUL_EQ_0] THEN ASM_MESON_TAC [RING_OF_INT_EQ_0_CHAR_0, number_field], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul l ((h:A->B) s) (ring_mul l (ring_of_int l m) x) =
    ring_mul l (h t) x") SUBST1_TAC THENL [EXPAND_TAC "t" THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL th), RING_OF_INT, (← MATCH_MP RING_HOMOMORPHISM_RING_OF_INT th)])) THEN ASM_SIMP_TAC [RING_MUL_ASSOC, RING_OF_INT], ALL_TAC] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_mul l ((h:A->B)(ring_inv k t)) (h t) = ring_1 l") ASSUME_TAC THENL [FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← GSYM (← MATCH_MP RING_HOMOMORPHISM_MUL th)), RING_INV, FIELD_MUL_LINV, (← MATCH_MP RING_HOMOMORPHISM_1 th)])), ALL_TAC] THEN SUBGOAL_THEN (← q r"(x:B) = ring_mul l (h(ring_inv k t)) (ring_mul l ((h:A->B) t) x)") SUBST1_TAC THENL [ASM_SIMP_TAC [RING_MUL_ASSOC, RING_INV, RING_MUL_LID], MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_SIMP_TAC [RING_INV]])

  let NUMBER_FIELD_DERIVATIVE_IN_DIFFERENT ← prove
    r"!k:A ring l:B ring h a.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        a IN ring_carrier(ring_of_integers l) /\
        subring_generated l (a INSERT IMAGE h (ring_carrier k)) = l
        ==> poly_extend (k,l) h (\v. a)
              (poly_deriv k (minimal_polynomial (k,l) h a)) IN
            number_field_different (k,l) h"
    (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"f = minimal_polynomial (k,l) (h:A->B) a") THEN ABBREV_TAC (← q r"d = poly_extend (k,l) (h:A->B) (\v. a) (poly_deriv k f)") THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"a:B"), (← q r"f:(1->num)->A"), (← q r"d:B")] NUMBER_FIELD_POWER_BASIS_DATA) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"a:B"), (← q r"f:(1->num)->A"), (← q r"d:B")] NUMBER_FIELD_CODIFFERENT_POWER_BASIS) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"R = ring_carrier(subring_generated l
          (a INSERT IMAGE (h:A->B) (ring_carrier(ring_of_integers k))))") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "codiff")) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"b:(1->num)->B") STRIP_ASSUME_TAC) THEN FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o (checkM (fun th => (do if ← (do let z20 ← (do let z21 ← (pure th); pure (concl z21)); pure (is_eq z20)) then (do let z25 ← (q r"R:B->bool"); let z24 ← (do let z22 ← (do let z23 ← (pure th); pure (concl z23)); liftExcept (lhs z22)); pure (z24 == z25)) else pure false)))) THEN SUBGOAL_THEN (← q r"!z. z IN R ==> (z:B) IN ring_carrier(ring_of_integers l) /\
                   z IN ring_carrier l") ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"l:B ring") RING_OF_INTEGERS_SUBSET) THEN UNDISCH_TAC (← q r"R SUBSET ring_carrier(ring_of_integers(l:B ring))") THEN SET_TAC [], ALL_TAC] THEN REWRITE_TAC [number_field_different, IN_ELIM_THM] THEN CONJ_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN X_GEN_TAC (← q r"y:B") THEN REWRITE_TAC [number_field_codifferent, IN_ELIM_THM] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(y:B) IN IMAGE (ring_mul l (ring_inv l d)) R") MP_TAC THENL [USE_THEN "codiff" (SUBST1_TAC o SYM) THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MATCH_MP_TAC o (checkM (fun th => (do if ← (do if ← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); pure (is_forall z4)) then (do let z6 ← (do let z7 ← (pure th); pure (concl z7)); canM (fun z8 => (do let z9 ← (pure z8); find_termM (fun z10 => (do let z12 ← (pure z10); let z11 ← (q r"ring_of_integers(l:B ring)"); pure (z11 == z12))) z9)) z6) else pure false) then (do let z13 ← (do let z14 ← (pure th); pure (concl z14)); canM (fun z15 => (do let z16 ← (pure z15); find_termM (fun z17 => (do let z19 ← (pure z17); let z18 ← (q r"y:B"); pure (z18 == z19))) z16)) z13) else pure false)))) THEN ASM_SIMP_TAC [], ALL_TAC] THEN REWRITE_TAC [IN_IMAGE] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"w:B") (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN SUBGOAL_THEN (← q r"(d:B) IN ring_carrier l /\ (w:B) IN ring_carrier l") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP NUMBER_FIELD_IMP_FIELD) o (checkM (fun th => (do let z3 ← (q r"number_field(l:B ring)"); let z2 ← (do let z1 ← (pure th); pure (concl z1)); pure (z2 == z3)))))) THEN ASM_SIMP_TAC [RING_MUL_ASSOC, RING_INV, FIELD_MUL_RINV, RING_MUL_LID])

  let NUMBER_FIELD_DIFFERENT_POWER_BASIS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!(l:B ring) d e z w.
            ring_mul l d e = ring_1 l
            ==> ring_mul l (ring_mul l d z) (ring_mul l e w) =
                ring_mul l z w")
    prove
      r"!k:A ring l:B ring h a f d.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          a IN ring_carrier l /\
          ring_carrier(subring_generated l
            (a INSERT IMAGE h (ring_carrier(ring_of_integers k)))) =
          ring_carrier(ring_of_integers l) /\
          f = minimal_polynomial (k,l) h a /\
          d = poly_extend (k,l) h (\v. a) (poly_deriv k f)
          ==> number_field_codifferent (k,l) h =
              IMAGE (ring_mul l (ring_inv l d))
                    (ring_carrier(ring_of_integers l)) /\
              number_field_different (k,l) h =
              ideal_generated (ring_of_integers l) {d}"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM (ASSUME_TAC o (SYM o (checkM (fun th => (do let z21 ← (q r"d:B"); let z20 ← (do let z18 ← (do let z19 ← (pure th); pure (concl z19)); liftExcept (lhs z18)); pure (z20 == z21)))))) THEN FIRST_X_ASSUM (ASSUME_TAC o (SYM o (checkM (fun th => (do let z17 ← (q r"f:(1->num)->A"); let z16 ← (do let z14 ← (do let z15 ← (pure th); pure (concl z15)); liftExcept (lhs z14)); pure (z16 == z17)))))) THEN SUBGOAL_THEN (← q r"(a:B) IN ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z8 ← (do let z9 ← (pure th); pure (concl z9)); pure (is_eq z8)) then (do let z13 ← (q r"ring_carrier(ring_of_integers(l:B ring))"); let z12 ← (do let z10 ← (do let z11 ← (pure th); pure (concl z11)); liftExcept (rhs z10)); pure (z12 == z13)) else pure false))))) THEN MATCH_MP_TAC SUBRING_GENERATED_INC THEN REWRITE_TAC [IN_INSERT] THEN REWRITE_TAC [INSERT_SUBSET, SUBSET, FORALL_IN_IMAGE] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"subring_generated l (a INSERT IMAGE (h:A->B) (ring_carrier k)) = l") ASSUME_TAC THENL [MATCH_MP_TAC NUMBER_FIELD_POWER_BASIS_GENERATOR THEN EXISTS_TAC (← q r"ring_1 k:A") THEN ASM_REWRITE_TAC [RING_1] THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP NUMBER_FIELD_IMP_FIELD) o (checkM (fun th => (do let z7 ← (q r"number_field(l:B ring)"); let z6 ← (do let z5 ← (pure th); pure (concl z5)); pure (z6 == z7)))))) THEN ASM_SIMP_TAC [FIELD_NONTRIVIAL] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_1 th)])) THEN MP_TAC (← ISPEC (← q r"l:B ring") RING_OF_INTEGERS_SUBSET) THEN SIMP_TAC [SUBSET, RING_MUL_LID], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"a:B"), (← q r"f:(1->num)->A"), (← q r"d:B")] NUMBER_FIELD_CODIFFERENT_POWER_BASIS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN REWRITE_TAC [(← GSYM number_field_codifferent)] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP NUMBER_FIELD_IMP_FIELD) o (checkM (fun th => (do let z4 ← (q r"number_field(l:B ring)"); let z3 ← (do let z2 ← (pure th); pure (concl z2)); pure (z3 == z4)))))) THEN SUBGOAL_THEN (← q r"(d:B) IN ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"a:B")] NUMBER_FIELD_DERIVATIVE_IN_DIFFERENT) THEN ASM_REWRITE_TAC [] THEN SIMP_TAC [number_field_different, IN_ELIM_THM], ALL_TAC] THEN SUBGOAL_THEN (← q r"!z. z IN ring_carrier(ring_of_integers l) ==> (z:B) IN ring_carrier l") ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"l:B ring") RING_OF_INTEGERS_SUBSET) THEN SET_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [IDEAL_GENERATED_SING_ALT, RING_OF_INTEGERS] THEN REWRITE_TAC [number_field_different] THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [FORALL_IN_IMAGE, EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:B") THEN EQ_TAC THENL [STRIP_TAC THEN EXISTS_TAC (← q r"ring_mul l x (ring_mul l (ring_inv l d) (ring_1 l:B))") THEN ASM_SIMP_TAC [RING_1, IN_SUBRING_1, RING_OF_INTEGERS_SUBRING] THEN ASM_SIMP_TAC [RING_MUL_RID, RING_INV, RING_MUL_ASSOC] THEN ONCE_REWRITE_TAC [(← MATCH_MP RING_MUL_SYM (← CONJ (← MATCH_MP (← ASSUME (← q r"!z. z IN ring_carrier(ring_of_integers l)
                              ==> (z:B) IN ring_carrier l")) (← ASSUME (← q r"(d:B) IN ring_carrier(ring_of_integers l)"))) (← MATCH_MP (← ASSUME (← q r"!z. z IN ring_carrier(ring_of_integers l)
                              ==> (z:B) IN ring_carrier l")) (← ASSUME (← q r"(x:B) IN ring_carrier(ring_of_integers l)")))))] THEN ASM_SIMP_TAC [(← GSYM RING_MUL_ASSOC), RING_INV, FIELD_MUL_RINV, RING_MUL_RID], DISCH_THEN (X_CHOOSE_THEN (← q r"z:B") STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBRING], X_GEN_TAC (← q r"w:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_mul l (ring_mul l d z) (ring_mul l (ring_inv l d) w) =
          ring_mul l (z:B) w") SUBST1_TAC THENL [MP_TAC r1 THEN DISCH_THEN (MP_TAC o (SPECL [(← q r"l:B ring"), (← q r"d:B"), (← q r"ring_inv l d:B"), (← q r"z:B"), (← q r"w:B")])) THEN ASM_SIMP_TAC [RING_INV, FIELD_MUL_RINV], MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBRING]]]])

  let (NUMBER_FIELD_CODIFFERENT_POWER_BASIS_Q, NUMBER_FIELD_DERIVATIVE_IN_DIFFERENT_Q, NUMBER_FIELD_DIFFERENT_POWER_BASIS_Q) ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let v1 ← CONJUNCT2 SUBRING_GENERATED
    let p2 ← prove r"!k:A ring a.
          field k /\ a IN ring_carrier k
          ==> subring_generated k
                (a INSERT IMAGE I (ring_carrier(ring_of_integers
                  (subfield_generated k {ring_0 k})))) =
              subring_generated k {a}" (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [RING_OF_INTEGERS_PRIME_SUBFIELD_CARRIER, IMAGE_I] THEN REWRITE_TAC [RINGS_EQ, v1] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN REWRITE_TAC [SUBRING_SUBRING_GENERATED, INSERT_SUBSET, EMPTY_SUBSET] THEN ASM_SIMP_TAC [SUBRING_GENERATED_INC_GEN, IN_INSERT] THEN MATCH_MP_TAC PRIME_SUBRING_MINIMAL THEN REWRITE_TAC [SUBRING_SUBRING_GENERATED])
    let lemma_zq := p2
    let q3 ← q r"d:A"
    let q4 ← q r"f:(1->num)->A"
    let q5 ← q r"a:A"
    let q6 ← q r"I:A->A"
    let q7 ← q r"k:A ring"
    let q8 ← q r"subfield_generated k {ring_0 k}:A ring"
    let v9 ← ISPECL [q8, q7, q6, q5, q4, q3] NUMBER_FIELD_CODIFFERENT_POWER_BASIS
    let q10 ← q r"(a:A) IN ring_carrier k"
    let p11 ← prove r"!(k:A ring) a f d.
          number_field k /\ a IN ring_carrier(ring_of_integers k) /\
          f = minimal_polynomial (subfield_generated k {ring_0 k},k) I a /\
          poly_deg (subfield_generated k {ring_0 k}) f =
          extension_degree (subfield_generated k {ring_0 k},k) I /\
          d = poly_extend (subfield_generated k {ring_0 k},k) I (\v. a)
                (poly_deriv (subfield_generated k {ring_0 k}) f)
          ==> ~(d = ring_0 k) /\
              {x | x IN ring_carrier k /\
                   !y. y IN ring_carrier(subring_generated k {a})
                       ==> algebra_trace (subfield_generated k {ring_0 k},k) I
                             (ring_mul k x y) IN
                           ring_carrier(ring_of_integers k)} =
              IMAGE (ring_mul k (ring_inv k d))
                    (ring_carrier(subring_generated k {a}))" (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN q10 ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC v9 THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, lemma_zq] THEN ANTS_TAC THENL [ASM_MESON_TAC [FINITE_EXTENSION_SIMPLE_EQ, number_field], REWRITE_TAC [RING_OF_INTEGERS_SUBFIELD_GENERATED, IN_INTER, ALGEBRA_TRACE_NORM_IN_CARRIER]])
    let th1 := p11
    let q12 ← q r"(a:A) IN ring_carrier k"
    let p13 ← prove r"!(k:A ring) a f d.
          number_field k /\ a IN ring_carrier(ring_of_integers k) /\
          f = minimal_polynomial (subfield_generated k {ring_0 k},k) I a /\
          poly_deg (subfield_generated k {ring_0 k}) f =
          extension_degree (subfield_generated k {ring_0 k},k) I /\
          d = poly_extend (subfield_generated k {ring_0 k},k) I (\v. a)
                (poly_deriv (subfield_generated k {ring_0 k}) f)
          ==> d IN
              number_field_different (subfield_generated k {ring_0 k},k) I" (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN q12 ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC NUMBER_FIELD_DERIVATIVE_IN_DIFFERENT THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, RING_HOMOMORPHISM_SUBFIELD_INCLUSION] THEN ASM_MESON_TAC [FINITE_EXTENSION_SIMPLE_EQ, number_field])
    let th2 := p13
    let q14 ← q r"d:A"
    let q15 ← q r"f:(1->num)->A"
    let q16 ← q r"a:A"
    let q17 ← q r"I:A->A"
    let q18 ← q r"k:A ring"
    let q19 ← q r"subfield_generated k {ring_0 k}:A ring"
    let v20 ← ISPECL [q19, q18, q17, q16, q15, q14] NUMBER_FIELD_DIFFERENT_POWER_BASIS
    let p21 ← prove r"!(k:A ring) a f d.
          number_field k /\ a IN ring_carrier k /\
          ring_carrier(subring_generated k {a}) =
          ring_carrier(ring_of_integers k) /\
          f = minimal_polynomial (subfield_generated k {ring_0 k},k) I a /\
          d = poly_extend (subfield_generated k {ring_0 k},k) I (\v. a)
                (poly_deriv (subfield_generated k {ring_0 k}) f)
          ==> number_field_codifferent (subfield_generated k {ring_0 k},k) I =
              IMAGE (ring_mul k (ring_inv k d))
                    (ring_carrier(ring_of_integers k)) /\
              number_field_different (subfield_generated k {ring_0 k},k) I =
              ideal_generated (ring_of_integers k) {d}" (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN MP_TAC v20 THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, lemma_zq])
    let th3 := p21
    pure (th1, th2, th3)

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_POWER_BASIS_DATA, NUMBER_FIELD_CODIFFERENT_POWER_BASIS,
           NUMBER_FIELD_POWER_BASIS_GENERATOR, NUMBER_FIELD_DERIVATIVE_IN_DIFFERENT,
           NUMBER_FIELD_DIFFERENT_POWER_BASIS, NUMBER_FIELD_CODIFFERENT_POWER_BASIS_Q,
           NUMBER_FIELD_DERIVATIVE_IN_DIFFERENT_Q, NUMBER_FIELD_DIFFERENT_POWER_BASIS_Q }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- power_basis_extension.ml phrases from line 1391 to 1934                -/
/- ---------------------------------------------------------------------- -/

structure PowerBasisExtension03 where
  -- @@FIELDS
  NUMBER_FIELD_DIFFERENT_LOCAL_POWER_BASIS : thm
  RING_OF_INTEGERS_LOCAL_SPAN : thm
  RING_OF_INTEGERS_SPAN_MOD_PRIME_DEGREE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupPowerBasisExtension03 [HolBase] (D : PowerBasisExtensionDeps) (BPowerBasisExtension02 : PowerBasisExtension02) :
    ExceptT String IO PowerBasisExtension03 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, MESON_TAC, RING_RULE, SET_TAC, TAUT, .. } := D
  let { BASIS_COORDINATES_EXPAND, BASIS_COORDINATES_IN_CARRIER,
        BASIS_DISCRIMINANT_TIMES_COORD, DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT,
        DEDEKIND_IDEAL_SUBSET_POW_VALUATION, DEDEKIND_IMP_INTEGRAL_DOMAIN,
        DEDEKIND_IN_IDEAL_POW_VALUATION, DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL,
        DEDEKIND_RING_OF_INTEGERS, EQ_IMP, EQ_TRANS, EXTENSION_DEGREE_LE_SPANNING,
        EXTENSION_LINCOMB_ADD, EXTENSION_LINCOMB_LMUL, FIELD_MUL_RINV,
        FIELD_QUOTIENT_RING, FINITE_NUMSEG_LT, FORALL_IN_IMAGE,
        FREE_BASIS_EXTENSION_DEGREE, FUN_IN_IMAGE, IDEAL_EXTENSION_POW_SUPPLEMENT,
        IDEAL_GENERATED_EQ_0, IDEAL_GENERATED_IMAGE_IDEAL_GENERATED,
        IDEAL_GENERATED_INC, IDEAL_GENERATED_MINIMAL, IDEAL_GENERATED_SING_ALT,
        IDEAL_POW_1, IDEAL_POW_SUC, IDEAL_PROD_COMM, IDEAL_PROD_HOMOMORPHIC_IMAGE,
        IDEAL_PROD_MONO, IDEAL_VALUATION_PRINCIPAL_MUL, IMAGE_CLAUSES, IMP_CONJ,
        INTEGRAL_DOMAIN_MUL_EQ_0, IN_ELIM_THM, IN_RING_IDEAL_0, IN_SUBRING_0,
        IN_SUBRING_1, IN_SUBRING_ADD, IN_SUBRING_MUL, IN_SUBRING_SUB,
        LEFT_IMP_EXISTS_THM, LE_ANTISYM, LE_REFL, NOT_FORALL_THM, NOT_IMP,
        NUMBER_FIELD_CODIFFERENT_BASIS_DISCRIMINANT, NUMBER_FIELD_DIFFERENT_NONZERO,
        NUMBER_FIELD_HOMOMORPHIC_PREIMAGE, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_PRIME_IDEAL_ABOVE, NUMBER_FIELD_TRACE_INTEGRAL, .. } := D.core1
  let { PRIME_IDEAL_IMP_SUBSET, PRIME_IMP_RING_IDEAL, QUOTIENT_RING, RING_COSET_EQ,
        RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_IN_CARRIER, RING_HOMOMORPHISM_MUL,
        RING_HOMOMORPHISM_RING_COSET, RING_HOMOMORPHISM_RING_OF_INTEGERS,
        RING_HOMOMORPHISM_SUM, RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_POW,
        RING_IDEAL_IDEAL_QUOTIENT, RING_IDEAL_IMP_SUBSET,
        RING_IDEAL_NUMBER_FIELD_DIFFERENT, RING_INV, RING_MUL, RING_MUL_IN_IDEAL_PROD,
        RING_MUL_LZERO, RING_OF_INTEGERS, RING_OF_INTEGERS_IDEAL_GENERATED_SING_EQ_0,
        RING_OF_INTEGERS_QUOTIENT_TRACE, RING_OF_INTEGERS_SUBRING,
        RING_OF_INTEGERS_SUBSET, RING_OF_INTEGERS_SUBSET_CODIFFERENT, RING_SUM,
        RING_SUM_EQ, RING_SUM_EQ_0, RING_SUM_RING_OF_INTEGERS, SING_SUBSET,
        SUBRING_SUBRING_GENERATED, SUBSET, SUBSET_REFL, SUBSET_TRANS,
        number_field_codifferent, number_field_different, o_THM, .. } := D.core2
  let { NUMBER_FIELD_CODIFFERENT_POWER_BASIS, NUMBER_FIELD_DERIVATIVE_IN_DIFFERENT,
        NUMBER_FIELD_POWER_BASIS_GENERATOR, .. } := BPowerBasisExtension02
  -- @@SCOPE END

  let NUMBER_FIELD_DIFFERENT_LOCAL_POWER_BASIS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r7 ← RING_RULE (← q r"!(l:B ring) d e t x.
        ring_mul l d e = ring_1 l
        ==> ring_mul l t x = ring_mul l d (ring_mul l x (ring_mul l t e))")
    let r8 ← RING_RULE (← q r"ring_mul r (ring_mul r e (ring_mul r t z)) (ring_1 r) =
      ring_mul r (ring_mul r t e) (z:B)")
    prove
      r"!k:A ring l:B ring h p a s Q.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
          a IN ring_carrier(ring_of_integers l) /\
          s IN ring_carrier(ring_of_integers k) /\ ~(s IN p) /\
          (!y. y IN ring_carrier(ring_of_integers l)
               ==> ring_mul l (h s) y IN
                   ring_carrier(subring_generated l
                     (a INSERT IMAGE h (ring_carrier(ring_of_integers k))))) /\
          prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q
          ==> ideal_valuation (ring_of_integers l) Q
                (number_field_different (k,l) h) =
              ideal_valuation (ring_of_integers l) Q
                (ideal_generated (ring_of_integers l)
                   {poly_extend (k,l) h (\v. a)
                      (poly_deriv k (minimal_polynomial (k,l) h a))})"
      (REPEAT GEN_TAC THEN ABBREV_TAC (← q r"R = ring_carrier(subring_generated l
            (a INSERT IMAGE (h:A->B) (ring_carrier(ring_of_integers k))))") THEN STRIP_TAC THEN ABBREV_TAC (← q r"f = minimal_polynomial (k,l) (h:A->B) a") THEN ABBREV_TAC (← q r"d = poly_extend (k,l) (h:A->B) (\v. a) (poly_deriv k f)") THEN ABBREV_TAC (← q r"D = number_field_different (k,l) (h:A->B)") THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP NUMBER_FIELD_IMP_FIELD) o (checkM (fun th => (do let z14 ← (q r"number_field(l:B ring)"); let z13 ← (do let z12 ← (pure th); pure (concl z12)); pure (z13 == z14)))))) THEN SUBGOAL_THEN (← q r"!z. z IN ring_carrier(ring_of_integers l) ==> (z:B) IN ring_carrier l") ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"l:B ring") RING_OF_INTEGERS_SUBSET) THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!c. c IN ring_carrier(ring_of_integers k) ==> (c:A) IN ring_carrier k") ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_SUBSET) THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(a:B) IN ring_carrier l /\ (s:A) IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(s:A = ring_0 k)") ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC (← q r"~((s:A) IN p)") THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (MP_TAC o ((MATCH_MP IN_RING_IDEAL_0) o ((MATCH_MP PRIME_IMP_RING_IDEAL) o (checkM (fun th => (do let z11 ← (q r"prime_ideal (ring_of_integers k) (p:A->bool)"); let z10 ← (do let z9 ← (pure th); pure (concl z9)); pure (z10 == z11))))))) THEN REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"subring_generated l (a INSERT IMAGE (h:A->B) (ring_carrier k)) = l") ASSUME_TAC THENL [MATCH_MP_TAC NUMBER_FIELD_POWER_BASIS_GENERATOR THEN EXISTS_TAC (← q r"s:A") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"a:B"), (← q r"f:(1->num)->A"), (← q r"d:B")] NUMBER_FIELD_CODIFFERENT_POWER_BASIS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "codiff")) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"a:B")] NUMBER_FIELD_DERIVATIVE_IN_DIFFERENT) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(d:B) IN ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [UNDISCH_TAC (← q r"(d:B) IN D") THEN EXPAND_TAC "D" THEN SIMP_TAC [number_field_different, IN_ELIM_THM], ALL_TAC] THEN SUBGOAL_THEN (← q r"(R:B->bool) subring_of l") ASSUME_TAC THENL [EXPAND_TAC "R" THEN REWRITE_TAC [SUBRING_SUBRING_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul l ((h:A->B) s) (ring_inv l d) IN number_field_codifferent (k,l) h") ASSUME_TAC THENL [REWRITE_TAC [number_field_codifferent, IN_ELIM_THM] THEN SUBGOAL_THEN (← q r"(h:A->B) s IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN ASM_SIMP_TAC [RING_MUL, RING_INV] THEN X_GEN_TAC (← q r"z:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_mul l ((h:A->B) s) z IN R") ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul l (ring_inv l d) (ring_mul l ((h:A->B) s) z) IN
        IMAGE (ring_mul l (ring_inv l d)) R") MP_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC [], ALL_TAC] THEN USE_THEN "codiff" (SUBST1_TAC o SYM) THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"ring_1 l:B")) o CONJUNCT2)) THEN ANTS_TAC THENL [MATCH_MP_TAC IN_SUBRING_1 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN SUBGOAL_THEN (← q r"(d:B) IN ring_carrier l /\ (z:B) IN ring_carrier l") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN MATCH_MP_TAC r8 THEN ASM_SIMP_TAC [RING_INV], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x. x IN D
          ==> ring_mul l ((h:A->B) s) x IN
              ideal_generated (ring_of_integers l) {d}") ASSUME_TAC THENL [X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN UNDISCH_TAC (← q r"(x:B) IN D") THEN EXPAND_TAC "D" THEN REWRITE_TAC [number_field_different, IN_ELIM_THM] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o (SPEC (← q r"ring_mul l ((h:A->B) s) (ring_inv l d)")))) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_SIMP_TAC [IDEAL_GENERATED_SING_ALT] THEN REWRITE_TAC [IN_ELIM_THM, RING_OF_INTEGERS] THEN EXISTS_TAC (← q r"ring_mul l x (ring_mul l ((h:A->B) s) (ring_inv l d))") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(d:B) IN ring_carrier l /\ (x:B) IN ring_carrier l /\
        (h:A->B) s IN ring_carrier l") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN MP_TAC r7 THEN DISCH_THEN (MP_TAC o (SPECL [(← q r"l:B ring"), (← q r"d:B"), (← q r"ring_inv l d:B"), (← q r"(h:A->B) s"), (← q r"x:B")])) THEN ASM_SIMP_TAC [RING_INV, FIELD_MUL_RINV], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_PRIME_IDEAL_ABOVE) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"~((h:A->B) s IN Q)") ASSUME_TAC THENL [DISCH_TAC THEN SUBGOAL_THEN (← q r"(s:A) IN {c | c IN ring_carrier k /\ (h:A->B) c IN Q}") MP_TAC THENL [REWRITE_TAC [IN_ELIM_THM] THEN ASM_REWRITE_TAC [], ASM_REWRITE_TAC []], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP DEDEKIND_RING_OF_INTEGERS) o (checkM (fun th => (do let z6 ← (q r"number_field(l:B ring)"); let z5 ← (do let z4 ← (pure th); pure (concl z4)); pure (z5 == z6)))))) THEN SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers l) (D:B->bool) /\ ~(D = {ring_0 l})") STRIP_ASSUME_TAC THENL [EXPAND_TAC "D" THEN ASM_SIMP_TAC [RING_IDEAL_NUMBER_FIELD_DIFFERENT, NUMBER_FIELD_DIFFERENT_NONZERO], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers l)
        (ideal_generated (ring_of_integers l) {d:B}) /\
      ~(ideal_generated (ring_of_integers l) {d} = {ring_0 l})") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, RING_OF_INTEGERS_IDEAL_GENERATED_SING_EQ_0], ALL_TAC] THEN REWRITE_TAC [(← GSYM LE_ANTISYM)] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool"), (← q r"ideal_generated (ring_of_integers l) {d:B}"), (← q r"ideal_valuation (ring_of_integers l) Q (D:B->bool)")] DEDEKIND_IDEAL_SUBSET_POW_VALUATION) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN TRANS_TAC SUBSET_TRANS (← q r"D:B->bool") THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET], MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool"), (← q r"D:B->bool"), (← q r"ideal_valuation (ring_of_integers l) Q (D:B->bool)")] DEDEKIND_IDEAL_SUBSET_POW_VALUATION) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS, LE_REFL]], ABBREV_TAC (← q r"t = ideal_valuation (ring_of_integers l) Q
              (ideal_generated (ring_of_integers l) {d:B})") THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool"), (← q r"D:B->bool"), (← q r"t:num")] DEDEKIND_IDEAL_SUBSET_POW_VALUATION) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o ((MATCH_MP RING_IDEAL_IMP_SUBSET) o (checkM (fun th => (do let z3 ← (q r"ring_ideal (ring_of_integers l) (D:B->bool)"); let z2 ← (do let z1 ← (pure th); pure (concl z1)); pure (z2 == z3)))))) THEN REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_CASES_TAC (← q r"x:B = ring_0 l") THENL [ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"ideal_pow (ring_of_integers l) Q t:B->bool")] IN_RING_IDEAL_0) THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW, RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"(h:A->B) s IN ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN EXISTS_TAC (← q r"ring_of_integers k:A ring") THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"~((h:A->B) s = ring_0 l)") ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC (← q r"~((h:A->B) s IN Q)") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool")] IN_RING_IDEAL_0) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul l ((h:A->B) s) x IN ideal_pow (ring_of_integers l) Q t") MP_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool"), (← q r"ideal_generated (ring_of_integers l) {d:B}"), (← q r"t:num")] DEDEKIND_IDEAL_SUBSET_POW_VALUATION) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS, LE_REFL, SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul l ((h:A->B) s) x IN ring_carrier(ring_of_integers l) /\
        ~(ring_mul l ((h:A->B) s) x = ring_0 l)") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"(h:A->B) s"), (← q r"x:B")] RING_MUL) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"(h:A->B) s"), (← q r"x:B")] INTEGRAL_DOMAIN_MUL_EQ_0) THEN ASM_SIMP_TAC [DEDEKIND_IMP_INTEGRAL_DOMAIN, RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool"), (← q r"ring_mul l ((h:A->B) s) x"), (← q r"t:num")] DEDEKIND_IN_IDEAL_POW_VALUATION) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool"), (← q r"x:B"), (← q r"t:num")] DEDEKIND_IN_IDEAL_POW_VALUATION) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool"), (← q r"(h:A->B) s"), (← q r"x:B")] IDEAL_VALUATION_PRINCIPAL_MUL) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN (MP_TAC o (REWRITE_RULE [RING_OF_INTEGERS])) THEN DISCH_THEN SUBST1_TAC THEN SUBGOAL_THEN (← q r"ideal_valuation (ring_of_integers l) Q
          (ideal_generated (ring_of_integers l) {(h:A->B) s}) = 0") SUBST1_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool"), (← q r"(h:A->B) s"), (← q r"1")] DEDEKIND_IN_IDEAL_POW_VALUATION) THEN ASM_SIMP_TAC [RING_OF_INTEGERS, IDEAL_POW_1, PRIME_IMP_RING_IDEAL] THEN ARITH_TAC, ARITH_TAC]])

  let RING_OF_INTEGERS_LOCAL_SPAN ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r13 ← RING_RULE (← q r"ring_mul (r:B ring) a x =
      ring_add r (ring_mul r a m) (ring_mul r a (ring_sub r x m))")
    let r29 ← ARITH_RULE (← q r"~(SUC t <= t)")
    let r30 ← TAUT (← q r"p /\ (p ==> q) /\ (p /\ q ==> r) ==> p /\ q /\ r")
    prove
      r"!k:A ring l:B ring h p w.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
          free_basis (k,l) h (extension_degree(k,l) h) w /\
          (!i. i < extension_degree(k,l) h
               ==> w i IN ring_carrier(ring_of_integers l)) /\
          (!x. x IN ring_carrier(ring_of_integers l)
               ==> ?c. (!i. c i IN ring_carrier(ring_of_integers k)) /\
                       ring_sub l x
                        (ring_sum l {i | i < extension_degree(k,l) h}
                           (\i. ring_mul l (h(c i)) (w i))) IN
                       ideal_generated (ring_of_integers l) (IMAGE h p))
          ==> ?s. s IN ring_carrier(ring_of_integers k) /\ ~(s IN p) /\
                  !x. x IN ring_carrier(ring_of_integers l)
                      ==> ?c. (!i. c i IN ring_carrier(ring_of_integers k)) /\
                              ring_mul l (h s) x =
                              ring_sum l {i | i < extension_degree(k,l) h}
                                (\i. ring_mul l (h(c i)) (w i))"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP NUMBER_FIELD_IMP_FIELD) o (checkM (fun th => (do let z52 ← (q r"number_field(l:B ring)"); let z51 ← (do let z50 ← (pure th); pure (concl z50)); pure (z51 == z52)))))) THEN ABBREV_TAC (← q r"n = extension_degree(k:A ring,l:B ring) h") THEN MP_TAC (← ISPEC (← q r"l:B ring") (← CONJUNCT1 RING_OF_INTEGERS_SUBRING)) THEN MP_TAC (← ISPEC (← q r"k:A ring") (← CONJUNCT1 RING_OF_INTEGERS_SUBRING)) THEN REPEAT DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP (← REWRITE_RULE [IMP_CONJ] RING_HOMOMORPHISM_IN_CARRIER))) THEN SUBGOAL_THEN (← q r"!i. i < n ==> (w:num->B) i IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN ABBREV_TAC (← q r"M = {y | ?c. (!i. c i IN ring_carrier(ring_of_integers k)) /\
                   y = ring_sum l {i | i < n}
                         (\i. ring_mul l ((h:A->B)(c i)) ((w:num->B) i))}") THEN SUBGOAL_THEN (← q r"!c. (!i. c i IN ring_carrier(ring_of_integers k))
          ==> ring_sum l {i | i < n}
                (\i. ring_mul l ((h:A->B)(c i)) ((w:num->B) i)) IN
              ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN wPart lhand (rand o rand) RING_SUM_RING_OF_INTEGERS THEN ASM_SIMP_TAC [IN_ELIM_THM, (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_MUL))] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [RING_SUM], ALL_TAC] THEN SUBGOAL_THEN (← q r"M SUBSET ring_carrier(ring_of_integers l) /\ ring_0 l IN M /\
      (!x y. x IN M /\ y IN M ==> ring_add l x y IN M) /\
      (!a x. a IN ring_carrier(ring_of_integers k) /\ x IN M
             ==> ring_mul l ((h:A->B) a) x IN M)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "M" THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL [GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [], EXISTS_TAC (← q r"\i:num. ring_0 k:A") THEN SIMP_TAC [IN_SUBRING_0, RING_OF_INTEGERS_SUBRING] THEN REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_0 (← ASSUME (← q r"ring_homomorphism(k:A ring,l:B ring) h")))] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_EQ_0 THEN ASM_SIMP_TAC [IN_ELIM_THM, RING_MUL_LZERO], MAP_EVERY X_GEN_TAC [(← q r"x:B"), (← q r"y:B")] THEN DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"c:num->A") STRIP_ASSUME_TAC) (X_CHOOSE_THEN (← q r"d:num->A") STRIP_ASSUME_TAC)) THEN EXISTS_TAC (← q r"\i. ring_add k ((c:num->A) i) (d i)") THEN ASM_SIMP_TAC [IN_SUBRING_ADD] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXTENSION_LINCOMB_ADD THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"x:B")] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"c:num->A") STRIP_ASSUME_TAC)) THEN EXISTS_TAC (← q r"\i. ring_mul k (a:A) ((c:num->A) i)") THEN ASM_SIMP_TAC [IN_SUBRING_MUL] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXTENSION_LINCOMB_LMUL THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"n:num"), (← q r"w:num->B"), (← q r"ring_1 l:B")] NUMBER_FIELD_CODIFFERENT_BASIS_DISCRIMINANT) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_OF_INTEGERS_SUBSET_CODIFFERENT) THEN ASM_REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN SIMP_TAC [IN_SUBRING_1, RING_OF_INTEGERS_SUBRING], ALL_TAC] THEN ABBREV_TAC (← q r"d = basis_discriminant (k:A ring,l:B ring) h n w") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!y. y IN ring_carrier(ring_of_integers l)
          ==> ring_mul l ((h:A->B) d) y IN M") ASSUME_TAC THENL [X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(y:B) IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"n:num"), (← q r"w:num->B"), (← q r"ring_carrier(ring_of_integers k:A ring)"), (← q r"y:B")] BASIS_DISCRIMINANT_TIMES_COORD) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [CONJ_TAC THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC NUMBER_FIELD_TRACE_INTEGRAL THEN ASM_SIMP_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_MUL))], DISCH_TAC] THEN EXPAND_TAC "M" THEN REWRITE_TAC [IN_ELIM_THM] THEN EXISTS_TAC (← q r"\i. if i < n
            then ring_mul k (d:A) (basis_coordinates (k,l) (h:A->B) n w y i)
            else ring_0 k") THEN REWRITE_TAC [] THEN CONJ_TAC THENL [GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [IN_SUBRING_0], ALL_TAC] THEN TRANS_TAC EQ_TRANS (← q r"ring_sum l {i | i < n}
          (\i. ring_mul l ((h:A->B)
                 (ring_mul k d (basis_coordinates (k,l) h n w y i)))
               ((w:num->B) i))") THEN CONJ_TAC THENL [ALL_TAC, MATCH_MP_TAC RING_SUM_EQ THEN SIMP_TAC [IN_ELIM_THM]] THEN SUBGOAL_THEN (← q r"(d:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [EXTENSION_LINCOMB_LMUL, BASIS_COORDINATES_IN_CARRIER, FINITE_NUMSEG_LT, IN_ELIM_THM] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC BASIS_COORDINATES_EXPAND THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"J = ideal_generated (ring_of_integers l) (IMAGE (h:A->B) p)") THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"M:B->bool")] IDEAL_EXTENSION_POW_SUPPLEMENT) THEN ASM_SIMP_TAC [PRIME_IDEAL_IMP_SUBSET, RING_OF_INTEGERS] THEN ANTS_TAC THENL [X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((← do let c := (← ASSUME (← q r"(x:B) IN ring_carrier(ring_of_integers l)")); pure (fun th => MATCH_MP th c)) o (checkM (fun th => (do if ← (do if ← (do let z34 ← (do let z35 ← (pure th); pure (concl z35)); pure (is_forall z34)) then (do let z36 ← (do let z37 ← (pure th); pure (concl z37)); canM (fun z38 => (do let z39 ← (pure z38); find_termM (fun z40 => (do let z42 ← (pure z40); let z41 ← (q r"J:B->bool"); pure (z41 == z42))) z39)) z36) else pure false) then (do let z43 ← (do let z44 ← (pure th); pure (concl z44)); canM (fun z45 => (do let z46 ← (pure z45); find_termM (fun z47 => (do let z49 ← (pure z47); let z48 ← (q r"ring_sub:B ring->B->B->B"); pure (z48 == z49))) z46)) z43) else pure false))))) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:num->A") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"ring_sum l {i | i < n}
          (\i. ring_mul l ((h:A->B)(c i)) ((w:num->B) i))") THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "M" THEN REWRITE_TAC [IN_ELIM_THM] THEN EXISTS_TAC (← q r"c:num->A") THEN ASM_REWRITE_TAC [], DISCH_TAC] THEN ABBREV_TAC (← q r"t = ideal_valuation (ring_of_integers k) p
            (ideal_generated (ring_of_integers k) {d:A})") THEN ABBREV_TAC (← q r"b = ideal_quotient (ring_of_integers k)
            (ideal_generated (ring_of_integers k) {d:A})
            (ideal_pow (ring_of_integers k) p t)") THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP PRIME_IMP_RING_IDEAL) o (checkM (fun th => (do let z33 ← (q r"prime_ideal (ring_of_integers k) (p:A->bool)"); let z32 ← (do let z31 ← (pure th); pure (concl z31)); pure (z32 == z33)))))) THEN SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers k) (b:A->bool) /\
      ideal_prod (ring_of_integers k) (ideal_pow (ring_of_integers k) p t) b =
      ideal_generated (ring_of_integers k) {d:A} /\
      ~(b SUBSET p)") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:A->bool"), (← q r"ideal_generated (ring_of_integers k) {d:A}")] DEDEKIND_IDEAL_SUBSET_POW_VALUATION) THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0, RING_OF_INTEGERS] THEN DISCH_TAC THEN MATCH_MP_TAC r30 THEN REPEAT CONJ_TAC THENL [EXPAND_TAC "b" THEN MATCH_MP_TAC RING_IDEAL_IDEAL_QUOTIENT THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN MESON_TAC [RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_POW], DISCH_TAC THEN EXPAND_TAC "b" THEN MATCH_MP_TAC DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_POW, LE_REFL], STRIP_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"SUC t"))) THEN REWRITE_TAC [r29] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z23 ← (do let z24 ← (pure th); pure (concl z24)); pure (is_eq z23)) then (do let z28 ← (q r"ideal_generated (ring_of_integers k) {d:A}"); let z27 ← (do let z25 ← (do let z26 ← (pure th); pure (concl z26)); liftExcept (rhs z25)); pure (z27 == z28)) else pure false))))) THEN REWRITE_TAC [IDEAL_POW_SUC] THEN wPart rand (lhand o rand) IDEAL_PROD_COMM THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_POW] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC IDEAL_PROD_MONO THEN ASM_REWRITE_TAC [SUBSET_REFL]], ALL_TAC] THEN UNDISCH_TAC (← q r"~((b:A->bool) SUBSET p)") THEN REWRITE_TAC [SUBSET, NOT_FORALL_THM, NOT_IMP] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"s:A") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(s:A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN EXISTS_TAC (← q r"s:A") THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPECL [(← q r"t:num"), (← q r"x:B")]) o (checkM (fun th => (do if ← (do let z14 ← (do let z15 ← (pure th); pure (concl z15)); pure (is_forall z14)) then (do let z16 ← (do let z17 ← (pure th); pure (concl z17)); canM (fun z18 => (do let z19 ← (pure z18); find_termM (fun z20 => (do let z22 ← (pure z20); let z21 ← (q r"ideal_pow (ring_of_integers k) (p:A->bool)"); pure (z21 == z22))) z19)) z16) else pure false))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"m:B") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"ring_mul l ((h:A->B) s) x IN M") MP_TAC THENL [ALL_TAC, EXPAND_TAC "M" THEN REWRITE_TAC [IN_ELIM_THM]] THEN SUBGOAL_THEN (← q r"(m:B) IN ring_carrier(ring_of_integers l) /\
      (h:A->B) s IN ring_carrier(ring_of_integers l)") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul l ((h:A->B) s) x =
      ring_add l (ring_mul l (h s) m) (ring_mul l (h s) (ring_sub l x m))") SUBST1_TAC THENL [MATCH_MP_TAC r13 THEN ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_generated (ring_of_integers l) {(h:A->B) d} =
      ideal_prod (ring_of_integers l)
        (ideal_generated (ring_of_integers l) (IMAGE h b))
        (ideal_generated (ring_of_integers l)
           (IMAGE h (ideal_pow (ring_of_integers k) p t)))") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring"), (← q r"h:A->B"), (← q r"b:A->bool"), (← q r"ideal_pow (ring_of_integers k) p t:A->bool")] IDEAL_PROD_HOMOMORPHIC_IMAGE) THEN ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN CONJ_TAC THEN MATCH_MP_TAC RING_IDEAL_IMP_SUBSET THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN FIRST_ASSUM ACCEPT_TAC, DISCH_THEN (SUBST1_TAC o SYM)] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"b:A->bool"), (← q r"ideal_pow (ring_of_integers k) p t:A->bool")] IDEAL_PROD_COMM) THEN ANTS_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC RING_IDEAL_IMP_SUBSET THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN FIRST_ASSUM ACCEPT_TAC, DISCH_THEN SUBST1_TAC] THEN FIRST_ASSUM (SUBST1_TAC o (checkM (fun th => (do if ← (do let z7 ← (do let z8 ← (pure th); pure (concl z8)); pure (is_eq z7)) then (do let z12 ← (q r"ideal_generated (ring_of_integers k) {d:A}"); let z11 ← (do let z9 ← (do let z10 ← (pure th); pure (concl z10)); liftExcept (rhs z9)); pure (z11 == z12)) else pure false)))) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring"), (← q r"h:A->B"), (← q r"{d:A}")] IDEAL_GENERATED_IMAGE_IDEAL_GENERATED) THEN ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN ASM_REWRITE_TAC [SING_SUBSET], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [IMAGE_CLAUSES], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul l ((h:A->B) s) (ring_sub l x m) IN
      ideal_generated (ring_of_integers l) {h d}") MP_TAC THENL [FIRST_ASSUM (SUBST1_TAC o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_eq z1)) then (do let z6 ← (q r"ideal_generated (ring_of_integers l) {(h:A->B) d}"); let z5 ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); liftExcept (lhs z3)); pure (z5 == z6)) else pure false)))) THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_MUL_IN_IDEAL_PROD)) THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_INC THEN CONJ_TAC THENL [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN MP_TAC (← MATCH_MP RING_IDEAL_IMP_SUBSET (← ASSUME (← q r"ring_ideal (ring_of_integers k) (b:A->bool)"))) THEN REWRITE_TAC [SUBSET] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"y:A"))) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC, MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC], FIRST_ASSUM ACCEPT_TAC, FIRST_ASSUM ACCEPT_TAC, MATCH_MP_TAC IN_SUBRING_SUB THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"(h:A->B) d IN ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"(h:A->B) d")] IDEAL_GENERATED_SING_ALT) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [IN_ELIM_THM, RING_OF_INTEGERS] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"y:B") STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC)

  let RING_OF_INTEGERS_SPAN_MOD_PRIME_DEGREE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r34 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!k:A ring l:B ring h p d w.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
          (!i. i < d ==> w i IN ring_carrier(ring_of_integers l)) /\
          (!x. x IN ring_carrier(ring_of_integers l)
               ==> ?c. (!i. c i IN ring_carrier(ring_of_integers k)) /\
                       ring_sub l x
                        (ring_sum l {i | i < d}
                           (\i. ring_mul l (h(c i)) (w i))) IN
                       ideal_generated (ring_of_integers l) (IMAGE h p))
          ==> extension_degree(k,l) h <= d"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] RING_OF_INTEGERS_QUOTIENT_TRACE) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"J = ideal_generated (ring_of_integers l) (IMAGE (h:A->B) p)") THEN DISCH_THEN (X_CHOOSE_THEN (← q r"g:(A->bool)->(B->bool)") (X_CHOOSE_THEN (← q r"G:num->B->bool") STRIP_ASSUME_TAC)) THEN SUBGOAL_THEN (← q r"number_field(k:A ring)") ASSUME_TAC THENL [ASM_MESON_TAC [NUMBER_FIELD_HOMOMORPHIC_PREIMAGE], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers k) (p:A->bool) /\
      ring_ideal (ring_of_integers l) (J:B->bool)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "J" THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"field(quotient_ring (ring_of_integers k) (p:A->bool))") ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_QUOTIENT_RING] THEN MATCH_MP_TAC DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"g:(A->bool)->(B->bool)"), (← q r"quotient_ring (ring_of_integers k) (p:A->bool)"), (← q r"quotient_ring (ring_of_integers l) (J:B->bool)"), (← q r"extension_degree(k:A ring,l:B ring) h"), (← q r"G:num->B->bool")] FREE_BASIS_EXTENSION_DEGREE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC EXTENSION_DEGREE_LE_SPANNING THEN EXISTS_TAC (← q r"\i. ring_coset (ring_of_integers l) J ((w:num->B) i)") THEN ASM_SIMP_TAC [(← CONJUNCT1 QUOTIENT_RING), IN_ELIM_THM] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN EXISTS_TAC (← q r"(w:num->B) i") THEN ASM_SIMP_TAC [], ALL_TAC] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"X:B->bool"), (← q r"y:B")] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"y:B")) o (checkM (fun th => (do if ← (do if ← (do let z35 ← (do let z36 ← (pure th); pure (concl z36)); pure (is_forall z35)) then (do let z37 ← (do let z38 ← (pure th); pure (concl z38)); canM (fun z39 => (do let z40 ← (pure z39); find_termM (fun z41 => (do let z43 ← (pure z41); let z42 ← (q r"J:B->bool"); pure (z42 == z43))) z40)) z37) else pure false) then (do let z44 ← (do let z45 ← (pure th); pure (concl z45)); canM (fun z46 => (do let z47 ← (pure z46); find_termM (fun z48 => (do let z50 ← (pure z48); let z49 ← (q r"w:num->B"); pure (z49 == z50))) z47)) z44) else pure false))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:num->A") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"\i. ring_coset (ring_of_integers k) p ((c:num->A) i)") THEN REWRITE_TAC [] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN EXISTS_TAC (← q r"(c:num->A) i") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. i < d
          ==> (h:A->B)(c i) IN ring_carrier(ring_of_integers l) /\
              ring_mul l (h(c i)) ((w:num->B) i) IN
              ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC r34 THEN CONJ_TAC THENL [MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN EXISTS_TAC (← q r"ring_of_integers k:A ring") THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_OF_INTEGERS], DISCH_TAC THEN MP_TAC (← ISPEC (← q r"ring_of_integers l:B ring") RING_MUL) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sum l {i | i < d} (\i. ring_mul l ((h:A->B)(c i)) ((w:num->B) i))
      IN ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"{i:num | i < d}"), (← q r"\i. ring_mul l ((h:A->B)(c i)) ((w:num->B) i)")] RING_SUM_RING_OF_INTEGERS) THEN ASM_SIMP_TAC [IN_ELIM_THM] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [RING_SUM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"J:B->bool"), (← q r"y:B"), (← q r"ring_sum l {i | i < d}
                      (\i. ring_mul l ((h:A->B)(c i)) ((w:num->B) i))")] RING_COSET_EQ) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"{i:num | i < d}"), (← q r"\i. ring_mul l ((h:A->B)(c i)) ((w:num->B) i)")] RING_SUM_RING_OF_INTEGERS) THEN ASM_SIMP_TAC [IN_ELIM_THM] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN FIRST_ASSUM (MP_TAC o ((MATCH_MP RING_HOMOMORPHISM_RING_COSET) o (checkM (fun th => (do let z33 ← (q r"ring_ideal (ring_of_integers l) (J:B->bool)"); let z32 ← (do let z31 ← (pure th); pure (concl z31)); pure (z32 == z33)))))) THEN DISCH_THEN (fun th => tactic_of do pure (wPart lhand (lhand o rand) (← MATCH_MP RING_HOMOMORPHISM_SUM th) THEN ASSUME_TAC th)) THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM], DISCH_THEN SUBST1_TAC] THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"i:num") THEN REWRITE_TAC [IN_ELIM_THM, o_THM] THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"i:num")) o (checkM (fun th => (do if ← (do if ← (do let z15 ← (do let z16 ← (pure th); pure (concl z16)); pure (is_forall z15)) then (do let z17 ← (do let z18 ← (pure th); pure (concl z18)); canM (fun z19 => (do let z20 ← (pure z19); find_termM (fun z21 => (do let z23 ← (pure z21); let z22 ← (q r"c:num->A"); pure (z22 == z23))) z20)) z17) else pure false) then (do let z24 ← (do let z25 ← (pure th); pure (concl z25)); canM (fun z26 => (do let z27 ← (pure z26); find_termM (fun z28 => (do let z30 ← (pure z28); let z29 ← (q r"ring_of_integers l:B ring"); pure (z29 == z30))) z27)) z24) else pure false))))) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN FIRST_ASSUM ((fun th => tactic_of do pure (MP_TAC (← SPECL [(← q r"(h:A->B)(c(i:num))"), (← q r"(w:num->B) i")] (← REWRITE_RULE [RING_OF_INTEGERS] (← MATCH_MP RING_HOMOMORPHISM_MUL th))))) o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); canM (fun z3 => (do let z4 ← (pure z3); find_termM (fun z5 => (do let z7 ← (pure z5); let z6 ← (q r"ring_coset (ring_of_integers l) (J:B->bool)"); pure (z6 == z7))) z4)) z1) then (do let z8 ← (do let z9 ← (pure th); pure (concl z9)); canM (fun z10 => (do let z11 ← (pure z10); find_termM (fun z12 => (do let z14 ← (pure z12); let z13 ← (q r"ring_homomorphism:(B ring#(B->bool)ring)->                            (B->B->bool)->bool"); pure (z13 == z14))) z11)) z8) else pure false)))) THEN ASM_SIMP_TAC [])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_DIFFERENT_LOCAL_POWER_BASIS, RING_OF_INTEGERS_LOCAL_SPAN,
           RING_OF_INTEGERS_SPAN_MOD_PRIME_DEGREE }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- power_basis_extension.ml phrases from line 2055 to 2389                -/
/- ---------------------------------------------------------------------- -/

structure PowerBasisExtension04 where
  -- @@FIELDS
  RING_OF_INTEGERS_ADJOIN_SPAN : thm
  NUMBER_FIELD_POWER_BASIS_MOD_PRIME : thm
  NUMBER_FIELD_ONE_PRIME_GENERATOR : thm
  NUMBER_FIELD_LOCAL_POWER_BASIS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupPowerBasisExtension04 [HolBase] (D : PowerBasisExtensionDeps) (BPowerBasisExtension01 : PowerBasisExtension01) (BPowerBasisExtension03 : PowerBasisExtension03) :
    ExceptT String IO PowerBasisExtension04 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, MESON_TAC, RING_RULE, SET_TAC, TAUT, .. } := D
  let { DEDEKIND_RESIDUE_GENERATOR_UNIFORMIZER, DEDEKIND_RING_OF_INTEGERS,
        DEDEKIND_SUBRING_DENSE, EXTENSION, FINITE_EXTENSION_SIMPLE_EQ,
        FINITE_IMP_ALGEBRAIC_EXTENSION, FINITE_IMP_FIELD_EXTENSION, FORALL_IN_GSPEC,
        FORALL_IN_IMAGE, FREE_BASIS_SIMPLE_EXTENSION, IDEAL_PRODUCT_SING,
        INSERT_SUBSET, IN_ELIM_THM, IN_INSERT, IN_SING, IN_SUBRING_POW, IN_SUBRING_SUB,
        LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM,
        MINIMAL_POLYNOMIAL_DEG_LE_EXTENSION_DEGREE, MINIMAL_POLYNOMIAL_IN_CARRIER,
        MINIMAL_POLYNOMIAL_MONIC, MINIMAL_POLYNOMIAL_VANISHES, MONIC_SUBRING_GENERATED,
        MONO_EXISTS, NUMBER_FIELD_PRIME_FACTORIZATION, NUMBER_FIELD_PRIME_IDEAL_ABOVE, .. } := D.core1
  let { POLY_DEG_SUBRING_GENERATED, POLY_EXTEND_FROM_SUBRING_GENERATED,
        PRIME_IMP_RING_IDEAL, RING_ADD, RING_HOMOMORPHISM_FROM_SUBRING_GENERATED,
        RING_HOMOMORPHISM_IN_CARRIER, RING_HOMOMORPHISM_RING_OF_INTEGERS,
        RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_POW, RING_IDEAL_IMP_SUBSET,
        RING_OF_INTEGERS, RING_OF_INTEGERS_MINIMAL_POLYNOMIAL,
        RING_OF_INTEGERS_SUBRING, RING_OF_INTEGERS_SUBSET, RING_POLYNOMIAL,
        RING_POLYNOMIAL_SUBRING_COEFF, RING_POW, RING_SUB_RZERO, RING_SUM,
        SUBRING_GENERATED_INC, SUBRING_GENERATED_MINIMAL,
        SUBRING_GENERATED_MONIC_ROOT_SPAN, SUBRING_SUBRING_GENERATED, SUBSET,
        SUBSET_ANTISYM_EQ, algebraic_extension, ring_of_integers, ring_setadd,
        subring_of, .. } := D.core2
  let { NUMBER_FIELD_SEPARABLE_EXTENSION, .. } := BPowerBasisExtension01
  let { RING_OF_INTEGERS_LOCAL_SPAN, RING_OF_INTEGERS_SPAN_MOD_PRIME_DEGREE, .. } := BPowerBasisExtension03
  -- @@SCOPE END

  let RING_OF_INTEGERS_ADJOIN_SPAN ← prove
    r"!k:A ring l:B ring h a.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        a IN ring_carrier(ring_of_integers l)
        ==> ring_carrier(subring_generated l
              (a INSERT IMAGE h (ring_carrier(ring_of_integers k)))) =
            {ring_sum l {i | i < poly_deg k (minimal_polynomial (k,l) h a)}
               (\i. ring_mul l (h(c i)) (ring_pow l a i)) |
             c | !i. c i IN ring_carrier(ring_of_integers k)}"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_SEPARABLE_EXTENSION) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITE_IMP_FIELD_EXTENSION)) THEN SUBGOAL_THEN (← q r"(a:B) IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"algebraic_over (k,l) (h:A->B) a") ASSUME_TAC THENL [ASM_MESON_TAC [FINITE_IMP_ALGEBRAIC_EXTENSION, algebraic_extension], ALL_TAC] THEN ABBREV_TAC (← q r"f = minimal_polynomial (k,l) (h:A->B) a") THEN SUBGOAL_THEN (← q r"f IN ring_carrier(poly_ring (ring_of_integers k) (:1)) /\
    monic (ring_of_integers k) (f:(1->num)->A) /\
    poly_deg (ring_of_integers k) f = poly_deg k f /\
    poly_extend (ring_of_integers k,l) (h:A->B) (\v:1. a) f = ring_0 l") STRIP_ASSUME_TAC THENL [REWRITE_TAC [ring_of_integers, MONIC_SUBRING_GENERATED, POLY_DEG_SUBRING_GENERATED, POLY_EXTEND_FROM_SUBRING_GENERATED] THEN ASM_REWRITE_TAC [(← GSYM RING_POLYNOMIAL)] THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC RING_POLYNOMIAL_SUBRING_COEFF THEN REWRITE_TAC [(← GSYM ring_of_integers)] THEN CONJ_TAC THENL [EXPAND_TAC "f" THEN ASM_SIMP_TAC [RING_POLYNOMIAL, MINIMAL_POLYNOMIAL_IN_CARRIER], MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"a:B")] RING_OF_INTEGERS_MINIMAL_POLYNOMIAL) THEN ASM_REWRITE_TAC []], EXPAND_TAC "f" THEN ASM_SIMP_TAC [MINIMAL_POLYNOMIAL_MONIC], EXPAND_TAC "f" THEN ASM_SIMP_TAC [MINIMAL_POLYNOMIAL_VANISHES]], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_homomorphism(ring_of_integers k,l) (h:A->B)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"{x | integral_element (integer_ring,k:A ring)
                                            (ring_of_int k) x}")] RING_HOMOMORPHISM_FROM_SUBRING_GENERATED) THEN ASM_SIMP_TAC [(← GSYM ring_of_integers)], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"ring_of_integers k:A ring"), (← q r"l:B ring"), (← q r"a:B"), (← q r"f:(1->num)->A")] SUBRING_GENERATED_MONIC_ROOT_SPAN) THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_POWER_BASIS_MOD_PRIME ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r13 ← ARITH_RULE (← q r"d <= n /\ n <= d ==> d:num = n")
    let r14 ← RING_RULE (← q r"ring_sub r (ring_add r z j) z = (j:B)")
    let r15 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!k:A ring l:B ring h p a.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
          a IN ring_carrier(ring_of_integers l) /\
          ring_setadd (ring_of_integers l)
            (ring_carrier(subring_generated l
               (a INSERT IMAGE h (ring_carrier(ring_of_integers k)))))
            (ideal_generated (ring_of_integers l) (IMAGE h p)) =
          ring_carrier(ring_of_integers l)
          ==> subring_generated l (a INSERT IMAGE h (ring_carrier k)) = l /\
              ?s. s IN ring_carrier(ring_of_integers k) /\ ~(s IN p) /\
                  !y. y IN ring_carrier(ring_of_integers l)
                      ==> ring_mul l (h s) y IN
                          ring_carrier(subring_generated l
                         (a INSERT IMAGE h (ring_carrier(ring_of_integers k))))"
      (REPEAT GEN_TAC THEN ABBREV_TAC (← q r"R = ring_carrier(subring_generated l
            (a INSERT IMAGE (h:A->B) (ring_carrier(ring_of_integers k))))") THEN ABBREV_TAC (← q r"J = ideal_generated (ring_of_integers l) (IMAGE (h:A->B) p)") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_SEPARABLE_EXTENSION) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITE_IMP_FIELD_EXTENSION)) THEN SUBGOAL_THEN (← q r"(a:B) IN ring_carrier l /\ algebraic_over (k,l) (h:A->B) a") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r15 THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ASM_MESON_TAC [FINITE_IMP_ALGEBRAIC_EXTENSION, algebraic_extension]], ALL_TAC] THEN ABBREV_TAC (← q r"d = poly_deg k (minimal_polynomial (k,l) (h:A->B) a)") THEN ABBREV_TAC (← q r"n = extension_degree (k,l) (h:A->B)") THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"a:B")] RING_OF_INTEGERS_ADJOIN_SPAN) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"!i. ring_pow l (a:B) i IN ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [GEN_TAC THEN MP_TAC (← ISPEC (← q r"ring_of_integers l:B ring") RING_POW) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!y. y IN ring_carrier(ring_of_integers l)
          ==> ?c. (!i. c i IN ring_carrier(ring_of_integers k)) /\
                  ring_sub l y
                    (ring_sum l {i | i < d}
                       (\i. ring_mul l ((h:A->B)(c i)) (ring_pow l a i))) IN J") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"!j:B. j IN J ==> j IN ring_carrier l") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"J:B->bool")] RING_IDEAL_IMP_SUBSET) THEN EXPAND_TAC "J" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN UNDISCH_TAC (← q r"ring_setadd (ring_of_integers l) R J =
        ring_carrier(ring_of_integers(l:B ring))") THEN REWRITE_TAC [EXTENSION, ring_setadd, IN_ELIM_THM] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"y:B"))) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS, IN_ELIM_THM] THEN REWRITE_TAC [LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"z:B"), (← q r"j:B"), (← q r"c:num->A")] THEN STRIP_TAC THEN EXISTS_TAC (← q r"c:num->A") THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [r14, RING_SUM], ALL_TAC] THEN SUBGOAL_THEN (← q r"d:num = n") ASSUME_TAC THENL [MATCH_MP_TAC r13 THEN CONJ_TAC THENL [MAP_EVERY EXPAND_TAC ["d", "n"] THEN MATCH_MP_TAC MINIMAL_POLYNOMIAL_DEG_LE_EXTENSION_DEGREE THEN ASM_REWRITE_TAC [], EXPAND_TAC "n" THEN MATCH_MP_TAC RING_OF_INTEGERS_SPAN_MOD_PRIME_DEGREE THEN MAP_EVERY EXISTS_TAC [(← q r"p:A->bool"), (← q r"ring_pow l (a:B)")] THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"subring_generated l (a INSERT IMAGE (h:A->B) (ring_carrier k)) = l") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"a:B")] FINITE_EXTENSION_SIMPLE_EQ) THEN ASM_REWRITE_TAC [], ASM_REWRITE_TAC []] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"ring_pow l (a:B)")] RING_OF_INTEGERS_LOCAL_SPAN) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"a:B")] FREE_BASIS_SIMPLE_EXTENSION) THEN ASM_REWRITE_TAC [], FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z12 ← (q r"d:num = n"); let z11 ← (do let z10 ← (pure th); pure (concl z10)); pure (z11 == z12)))))) THEN ASM_REWRITE_TAC []], ALL_TAC] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"s:A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((← do let c := (← ASSUME (← q r"(y:B) IN ring_carrier(ring_of_integers l)")); pure (fun th => MATCH_MP th c)) o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_forall z1)) then (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); canM (fun z5 => (do let z6 ← (pure z5); find_termM (fun z7 => (do let z9 ← (pure z7); let z8 ← (q r"ring_mul l ((h:A->B) s)"); pure (z8 == z9))) z6)) z3) else pure false))))) THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"c:num->A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_ONE_PRIME_GENERATOR ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_add r z (ring_sub r y z) = (y:B)")
    prove
      r"!k:A ring l:B ring h p Q.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
          {P | prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P} = {Q}
          ==> ?a. a IN ring_carrier(ring_of_integers l) /\
                  ring_setadd (ring_of_integers l)
                    (ring_carrier(subring_generated l
                       (a INSERT IMAGE h (ring_carrier(ring_of_integers k)))))
                    (ideal_generated (ring_of_integers l) (IMAGE h p)) =
                  ring_carrier(ring_of_integers l)"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"prime_ideal (ring_of_integers l) (Q:B->bool) /\ IMAGE (h:A->B) p SUBSET Q") STRIP_ASSUME_TAC THENL [FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"Q:B->bool")) o ((REWRITE_RULE [EXTENSION, IN_ELIM_THM, IN_SING]) o (checkM (fun th => (do if ← (do let z38 ← (do let z39 ← (pure th); pure (concl z39)); pure (is_eq z38)) then (do let z43 ← (q r"{Q:B->bool}"); let z42 ← (do let z40 ← (do let z41 ← (pure th); pure (concl z41)); liftExcept (rhs z40)); pure (z42 == z43)) else pure false)))))) THEN MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_PRIME_IDEAL_ABOVE) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP DEDEKIND_RING_OF_INTEGERS) o (checkM (fun th => (do let z37 ← (q r"number_field(l:B ring)"); let z36 ← (do let z35 ← (pure th); pure (concl z35)); pure (z36 == z37)))))) THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP PRIME_IMP_RING_IDEAL) o (checkM (fun th => (do let z34 ← (q r"prime_ideal (ring_of_integers l) (Q:B->bool)"); let z33 ← (do let z32 ← (pure th); pure (concl z32)); pure (z33 == z34)))))) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool")] DEDEKIND_RESIDUE_GENERATOR_UNIFORMIZER) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN ABBREV_TAC (← q r"q = CARD(ring_carrier(quotient_ring (ring_of_integers l) (Q:B->bool)))") THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:B") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"a:B") THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"R = ring_carrier(subring_generated l
            (a INSERT IMAGE (h:A->B) (ring_carrier(ring_of_integers k))))") THEN ABBREV_TAC (← q r"J = ideal_generated (ring_of_integers l) (IMAGE (h:A->B) p)") THEN SUBGOAL_THEN (← q r"!z. z IN ring_carrier(ring_of_integers l) ==> (z:B) IN ring_carrier l") ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"l:B ring") RING_OF_INTEGERS_SUBSET) THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!c. c IN ring_carrier(ring_of_integers k)
          ==> (h:A->B) c IN ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN EXISTS_TAC (← q r"ring_of_integers k:A ring") THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"(R:B->bool) SUBSET ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [EXPAND_TAC "R" THEN MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN REWRITE_TAC [RING_OF_INTEGERS_SUBRING] THEN ASM_SIMP_TAC [INSERT_SUBSET, SUBSET, FORALL_IN_IMAGE], ALL_TAC] THEN SUBGOAL_THEN (← q r"(R:B->bool) subring_of (ring_of_integers l)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"a INSERT IMAGE (h:A->B) (ring_carrier(ring_of_integers k))")] SUBRING_SUBRING_GENERATED) THEN ASM_REWRITE_TAC [subring_of, RING_OF_INTEGERS] THEN SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(a:B) IN R") ASSUME_TAC THENL [EXPAND_TAC "R" THEN MATCH_MP_TAC SUBRING_GENERATED_INC THEN ASM_SIMP_TAC [IN_INSERT, INSERT_SUBSET, SUBSET, FORALL_IN_IMAGE], ALL_TAC] THEN ABBREV_TAC (← q r"t = ring_sub l (ring_pow l a q) (a:B)") THEN SUBGOAL_THEN (← q r"(t:B) IN Q /\ ~(t IN ideal_pow (ring_of_integers l) Q 2)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "t" THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(t:B) IN R") ASSUME_TAC THENL [EXPAND_TAC "t" THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"R:B->bool"), (← q r"ring_pow (ring_of_integers l) a q:B"), (← q r"a:B")] IN_SUBRING_SUB) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"R:B->bool"), (← q r"a:B"), (← q r"q:num")] IN_SUBRING_POW) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!n y. y IN ring_carrier(ring_of_integers l)
            ==> ?z. z IN R /\
                    ring_sub l y z IN ideal_pow (ring_of_integers l) Q n:B->bool") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool"), (← q r"t:B"), (← q r"R:B->bool"), (← q r"n:num"), (← q r"y:B")] DEDEKIND_SUBRING_DENSE) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC (← q r"w:B") THEN DISCH_TAC THEN FIRST_X_ASSUM ((DISJ_CASES_THEN MP_TAC) o ((← do let c := (← ASSUME (← q r"(w:B) IN ring_carrier(ring_of_integers l)")); pure (fun th => MATCH_MP th c)) o (checkM (fun th => (do if ← (do let z24 ← (do let z25 ← (pure th); pure (concl z25)); pure (is_forall z24)) then (do let z26 ← (do let z27 ← (pure th); pure (concl z27)); canM (fun z28 => (do let z29 ← (pure z28); find_termM (fun z30 => (do let z31 ← (pure z30); pure (is_disj z31))) z29)) z26) else pure false))))) THENL [DISCH_TAC THEN EXISTS_TAC (← q r"ring_0 l:B") THEN UNDISCH_TAC (← q r"(R:B->bool) subring_of (ring_of_integers l)") THEN SIMP_TAC [subring_of, RING_OF_INTEGERS] THEN DISCH_TAC THEN ASM_SIMP_TAC [RING_SUB_RZERO], DISCH_THEN (X_CHOOSE_TAC (← q r"m:num")) THEN EXISTS_TAC (← q r"ring_pow l (a:B) m") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"R:B->bool"), (← q r"a:B"), (← q r"m:num")] IN_SUBRING_POW) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS]], ALL_TAC] THEN SUBGOAL_THEN (← q r"J = ideal_pow (ring_of_integers l) Q
            (ramification_index (ring_of_integers k,ring_of_integers l)
                                (h:A->B) Q)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_PRIME_FACTORIZATION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN SIMP_TAC [IDEAL_PRODUCT_SING, RING_IDEAL_IDEAL_POW], ALL_TAC] THEN REWRITE_TAC [(← GSYM SUBSET_ANTISYM_EQ)] THEN CONJ_TAC THENL [REWRITE_TAC [SUBSET, ring_setadd, FORALL_IN_GSPEC] THEN MAP_EVERY X_GEN_TAC [(← q r"z:B"), (← q r"j:B")] THEN STRIP_TAC THEN MP_TAC (← ISPEC (← q r"ring_of_integers l:B ring") RING_ADD) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL [FIRST_ASSUM (MATCH_MP_TAC o ((REWRITE_RULE [SUBSET]) o (checkM (fun th => (do let z23 ← (q r"(R:B->bool) SUBSET ring_carrier(ring_of_integers l)"); let z22 ← (do let z21 ← (pure th); pure (concl z21)); pure (z22 == z23)))))) THEN ASM_REWRITE_TAC [], MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"J:B->bool")] RING_IDEAL_IMP_SUBSET) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW, SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"(j:B) IN J") THEN ASM_REWRITE_TAC []], ALL_TAC] THEN REWRITE_TAC [SUBSET, ring_setadd, IN_ELIM_THM] THEN X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((← do let c := (← ASSUME (← q r"(y:B) IN ring_carrier(ring_of_integers l)")); pure (fun th => MATCH_MP th c)) o ((SPEC (← q r"ramification_index (ring_of_integers k,ring_of_integers l) (h:A->B) Q")) o (checkM (fun th => (do if ← (do if ← (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); pure (is_forall z5)) then (do let z7 ← (do let z8 ← (pure th); pure (concl z8)); canM (fun z9 => (do let z10 ← (pure z9); find_termM (fun z11 => (do let z13 ← (pure z11); let z12 ← (q r"R:B->bool"); pure (z12 == z13))) z10)) z7) else pure false) then (do let z14 ← (do let z15 ← (pure th); pure (concl z15)); canM (fun z16 => (do let z17 ← (pure z16); find_termM (fun z18 => (do let z20 ← (pure z18); let z19 ← (q r"ideal_pow:(B ring)->(B->bool)->num->B->bool"); pure (z19 == z20))) z17)) z14) else pure false)))))) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"z:B") STRIP_ASSUME_TAC) THEN MAP_EVERY EXISTS_TAC [(← q r"z:B"), (← q r"ring_sub l y (z:B)")] THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN SUBGOAL_THEN (← q r"(z:B) IN ring_carrier l /\ (y:B) IN ring_carrier l") STRIP_ASSUME_TAC THENL [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (MATCH_MP_TAC o ((REWRITE_RULE [SUBSET]) o (checkM (fun th => (do let z4 ← (q r"(R:B->bool) SUBSET ring_carrier(ring_of_integers l)"); let z3 ← (do let z2 ← (pure th); pure (concl z2)); pure (z3 == z4)))))) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_LOCAL_POWER_BASIS ← prove
    r"!k:A ring l:B ring h p Q.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        {P | prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P} = {Q}
        ==> ?a s. a IN ring_carrier(ring_of_integers l) /\
                  subring_generated l (a INSERT IMAGE h (ring_carrier k)) = l /\
                  s IN ring_carrier(ring_of_integers k) /\ ~(s IN p) /\
                  !y. y IN ring_carrier(ring_of_integers l)
                      ==> ring_mul l (h s) y IN
                          ring_carrier(subring_generated l
                       (a INSERT IMAGE h (ring_carrier(ring_of_integers k))))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_ONE_PRIME_GENERATOR) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:B") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"a:B")] NUMBER_FIELD_POWER_BASIS_MOD_PRIME) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC (← q r"s:A"))) THEN MAP_EVERY EXISTS_TAC [(← q r"a:B"), (← q r"s:A")] THEN ASM_REWRITE_TAC [])

  -- @@RETURN BEGIN
  return { RING_OF_INTEGERS_ADJOIN_SPAN, NUMBER_FIELD_POWER_BASIS_MOD_PRIME,
           NUMBER_FIELD_ONE_PRIME_GENERATOR, NUMBER_FIELD_LOCAL_POWER_BASIS }
  -- @@RETURN END

end HolANT.PowerBasisExtension
