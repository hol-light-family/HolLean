/- ========================================================================= -/
/- Finite fields.                                                            -/
/-                                                                           -/
/- The multiplicative group and primitive roots; subfields of finite fields  -/
/- and homomorphisms between them; norm and trace (surjectivity, fibres,     -/
/- Hilbert 90); irreducible polynomials over finite fields, their roots, the -/
/- factorization of X^(q^n) - X, the existence and the number of monic       -/
/- irreducible polynomials of each degree, and the irreducibility test of    -/
/- Rabin.                                                                    -/
/-                                                                           -/
/- The existence and uniqueness of finite fields of each prime power order   -/
/- are in Library/fieldtheory.ml (FINITE_FIELD_EXISTS,                       -/
/- ISOMORPHIC_FINITE_FIELDS), their Galois groups in Library/galois.ml       -/
/- (GALOIS_GROUP_FINITE_FIELD).                                              -/
/- ========================================================================= -/
/- File: HolLibrary/FiniteFields.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/finite_fields.ml`, by hand, in file
  order, in the style of HolLibrary/Galois.lean (see there and
  HolMath/Base.lean for the conventions).  finite_fields.ml begins with
  `needs "Library/galois.ml"` and `needs "Library/ring_groups.ml"`, then
  `prioritize_num()` (run at the start of the first bundle); the theorems it
  uses from them (and from the files they need) and from the core library
  are supplied via the CoreThms structures (SessionLibrary.FiniteFields
  fills them).  Each section is a bundle (a `structure`) built by a `setup`
  function; SessionLibrary/FiniteFields.lean builds the bundles in order and
  exports every name under its HOL Light name.

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, SET_RULE, RING_RULE, ARITH_RULE, TAUT) they are bound
  first, in OCaml's order.
-/

import HolLibrary.Galois
import HolLibrary.RingGroups

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolLibrary.FiniteFields

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ALGEBRAICALLY_CLOSED_FIELD_FINITE_SUBFIELD ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH
   ALGEBRAIC_IMP_FIELD_EXTENSION ALGEBRA_NORM_EQ_0 ALGEBRA_NORM_INV
   ALGEBRA_NORM_MUL ALGEBRA_NORM_POW ALGEBRA_TRACE_ADD ALGEBRA_TRACE_NEG
   ALGEBRA_TRACE_NORM_FINITE_FIELD ALGEBRA_TRACE_NORM_GALOIS
   ALGEBRA_TRACE_NORM_IN_CARRIER ALGEBRA_TRACE_SUB ALGEBRA_TRACE_SURJECTIVE
   CARD_DELETE CARD_EQ_0 CARD_EQ_FIBRES_HAS_SIZE CARD_EQ_IMAGE
   CARD_EXTENSION_DEGREE CARD_IMAGE_INJ CARRIER_SUBFIELD_GENERATED_SUBFIELD
   CARRIER_SUBFIELD_OF CARRIER_SUBGROUP_GENERATED_BY_SING CONG_IMP_EQ
   CYCLIC_GALOIS_GROUP_FINITE_FIELD CYCLIC_GROUP_ELEMENT_ORDER
   CYCLIC_IMP_ABELIAN_GROUP DE_MORGAN_THM DIVIDES_DIV_MULT DIVIDES_EXP_MINUS1
   DIVIDES_GCD_LEFT DIVIDES_LE DIVIDES_PRIME_PRIME DIVIDES_REFL DIVIDES_REXP
   DIVIDES_ZERO DIVISION DIV_MULT EQ_EXP EQ_MULT_LCANCEL EQ_TRANS
   EXISTS_UNIQUE_THM EXP EXP_1 EXP_ADD EXP_EQ_0 EXP_EXP EXP_ZERO EXTENSION
   EXTENSION_DEGREE_SIMPLE FIELD_DIV_EQ_0 FIELD_EXTENSION_IMP_HOMOMORPHISM
   FIELD_EXTENSION_INTO_SUBFIELD_GENERATED FIELD_EXTENSION_SUBFIELD_GENERATED
   FIELD_IMP_INTEGRAL_DOMAIN FIELD_IMP_NONTRIVIAL_RING FIELD_INV_EQ_0
   FIELD_MONIC_IRREDUCIBLE_ASSOCIATE FIELD_MUL_EQ_0 FIELD_MUL_RINV
   FIELD_NONTRIVIAL FIELD_POW_EQ_0 FIELD_RING_HOMOMORPHISM_MONOMORPHISM
   FIELD_SUBFIELD_GENERATED FIELD_UNIT FIELD_UNIT_GROUP FINITE_DELETE
   FINITE_DIFF FINITE_FIELD_CARD_GE_2 FINITE_FIELD_CARD_ROOTS_OF_UNITY
   FINITE_FIELD_GALOIS_EXTENSION FINITE_FIELD_IMP_PERFECT
   FINITE_FIELD_INTERMEDIATE_FIELDS FINITE_FIELD_PRIMITIVE_ELEMENT
   FINITE_FINITE_FIELD_EXTENSION FINITE_GALOIS_SUBFIELDS_ELEMENT
   FINITE_GALOIS_SUBFIELDS_FINITE FINITE_IMAGE FINITE_IMP_ALGEBRAIC_EXTENSION
   FINITE_INTEGRAL_DOMAIN_CHAR FINITE_INTEGRAL_DOMAIN_IMP_FIELD
   FINITE_INTEGRAL_DOMAIN_POW_CARD FINITE_INTEGRAL_DOMAIN_SIZE FINITE_NUMSEG_LT
   FINITE_POLY_DEG_LE FINITE_RESTRICT FINITE_RING_MONOMORPHIC_PREIMAGE
   FINITE_SIMPLE_ALGEBRAIC_EXTENSION FINITE_SUBFIELD_EXPLICIT FINITE_SUBSET
   FORALL_IN_IMAGE FUN_EQ_THM GALOIS_GROUP GALOIS_GROUP_FINITE_FIELD
   GALOIS_GROUP_FROBENIUS GALOIS_GROUP_PERMUTES GALOIS_GROUP_POW_RING_POW
   GALOIS_GROUP_RESTRICTION_NORMAL GALOIS_IMP_NORMAL_EXTENSION
   GALOIS_IMP_SEPARABLE_EXTENSION GROUP_ELEMENT_ORDER_UNIQUE GROUP_HOMOMORPHISM
   GROUP_NPOW GROUP_POW_EQ GROUP_POW_EQ_ID GROUP_ZPOW_REM_ELEMENT_ORDER HAS_SIZE
   HAS_SIZE_IMAGE_INJ HAS_SIZE_NUMSEG_LT HILBERT_90_ADDITIVE_CYCLIC_EQ
   HILBERT_90_CYCLIC_EQ IMP_CONJ IMP_CONJ_ALT INSERT_SUBSET
   INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING INTEGRAL_DOMAIN_MUL_LCANCEL
   INTEGRAL_DOMAIN_MUL_RCANCEL INTEGRAL_DOMAIN_NONTRIVIAL
   INTEGRAL_DOMAIN_POLY_RING INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE INT_LT_REM
   INT_OF_NUM_EQ INT_OF_NUM_LT INT_OF_NUM_OF_INT INT_REM_POS IN_DELETE IN_DIFF
   IN_ELIM_THM IN_FINITE_GALOIS_SUBFIELDS IN_IMAGE IN_INSERT
   IN_RING_POLYNOMIAL_CARRIER_COMPOSE IN_SING IN_UNIV
   IRREDUCIBLE_IMP_POLY_DEG_NZ ISOMORPHIC_FINITE_FIELDS I_O_ID I_THM
   LEFT_ADD_DISTRIB LEFT_IMP_EXISTS_THM LE_1 LE_EXP LE_TRANS LT_REFL
   MINIMAL_POLYNOMIAL MINIMAL_POLYNOMIAL_ASSOCIATES_IRREDUCIBLE
   MONIC_ASSOCIATES_EQ : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (MONIC_POLY_PRODUCT MONIC_VAR_POW_SUB_VAR MONO_EXISTS MULT_CLAUSES MULT_EQ_0
   MULT_EQ_1 MULT_SYM NOETHERIAN_DOMAIN_IRREDUCIBLE_FACTOR_EXISTS
   NORMAL_IMP_ALGEBRAIC_EXTENSION NOT_EXISTS_THM NOT_SUC NSUM_CLAUSES NSUM_CONST
   NSUM_EQ NSUM_GROUP NUMSEG_CLAUSES_LT PERFECT_FIELD_IMP_SEPARABLE_EXTENSION
   PID_IMP_UFD PID_POLY_RING POLY_CLAUSES POLY_DEG_CONST POLY_DEG_DIVIDES_LE
   POLY_DEG_EQ_0_UNIT POLY_DEG_MONOMORPHIC_IMAGE POLY_DEG_MUL
   POLY_DEG_PRODUCT_MONIC POLY_EQ_0_MONOMORPHIC_IMAGE
   POLY_EVAL_HOMOMORPHIC_IMAGE POLY_EVAL_VAR_POW_SUB_VAR
   POLY_MONOMIAL_IN_CARRIER POLY_RING_CLAUSES POLY_ROOT_BOUND_EXTENSION
   POLY_SEPARABLE_IMP_SQUAREFREE POLY_SEPARABLE_VAR_POW_SUB_VAR
   POLY_SPLITS_DIVISOR POLY_SPLITS_HAS_ROOT POLY_SPLITS_OVER_DISTINCT_ROOTS
   POLY_SPLITS_OVER_SEPARABLE_ROOT_COUNT POLY_VAR_POW_SUB_VAR PRIME_1
   PRIME_DIVEXP PRIME_FACTOR PRIME_IMP_NZ PRIME_SUBFIELD_HOMOMORPHISM_EXISTS
   RING_0 RING_1 RING_ADD RING_ADD_LZERO RING_ADD_RCANCEL
   RING_ASSOCIATES_DIVIDES RING_ASSOCIATES_IRREDUCIBLE RING_ASSOCIATES_REFL
   RING_ASSOCIATES_RMUL RING_CARRIER_NONEMPTY
   RING_CARRIER_SUBFIELD_GENERATED_SUBSET RING_CHAR_DIVIDES_ORDER
   RING_CHAR_MONOMORPHIC_IMAGE RING_COPRIME_DISTINCT_MONIC_IRREDUCIBLES
   RING_COPRIME_PRODUCT_DIVIDES RING_DIV RING_DIVIDES_HOMOMORPHIC_IMAGE
   RING_DIVIDES_IN_CARRIER RING_DIVIDES_IRREDUCIBLE_ROOT
   RING_DIVIDES_PRODUCT_SUBSET RING_DIVIDES_TRANS RING_ENDOMORPHISM_POW_CARD
   RING_HOMOMORPHISM_1 RING_HOMOMORPHISM_COMPOSE RING_HOMOMORPHISM_IN_CARRIER
   RING_HOMOMORPHISM_POLY_RINGS RING_HOMOMORPHISM_POW
   RING_HOMOMORPHISM_SUBFIELD_INCLUSION RING_INV RING_INV_INV
   RING_IRREDUCIBLE_COPRIME_EQ RING_IRREDUCIBLE_IN_CARRIER
   RING_ISOMORPHISM_IMP_HOMOMORPHISM RING_MONOMORPHISM_EQ_0
   RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_MONOMORPHISM_INJECTIVE_EQ RING_MUL
   RING_MUL_LID RING_MUL_RID RING_MUL_RZERO RING_NEG RING_NEG_EQ_0 RING_ORDER_0
   RING_ORDER_MONOMORPHIC_IMAGE RING_ORDER_POW RING_POLYNOMIAL
   RING_POLYNOMIAL_POW RING_POLYNOMIAL_SUB RING_POLYNOMIAL_VAR RING_POW
   RING_POW_1 RING_POW_EQ_1 RING_POW_INV RING_POW_POW
   RING_POW_SUBFIELD_GENERATED RING_POW_SUBRING_GENERATED RING_POW_ZERO
   RING_PRODUCT RING_PRODUCT_NSUM RING_PRODUCT_SING RING_SQUAREFREE_DIVIDES
   RING_SUB RING_SUB_EQ_0 RING_SUB_REFL RING_UNIT_POLY_DOMAIN
   ROOTS_OF_UNITY_HAS_SIZE_PRIMITIVE ROOTS_OF_UNITY_RING_ORDER SING_SUBSET
   SPLITTING_EXTENSION_EXISTS_BIGENOUGH SUBFIELD_IMP_SUBRING_OF
   SUBFIELD_OF_FIXPOINTS SUBFIELD_OF_MONOMORPHIC_IMAGE SUBRING_GENERATED_INC_GEN
   SUBRING_GENERATED_MINIMAL SUBSET SUBSET_ANTISYM SUB_0 SUC_SUB1
   TRIVIAL_RING_HAS_SIZE_1 UNIT_GROUP UNIT_GROUP_POW WLOG_LE abelian_group
   algebraic_extension algebraically_closed_field divides field_extension
   galois_extension group_homomorphism isomorphic_ring o_THM pairwise permutes
   poly_splits_over ring_associates ring_coprime ring_div ring_divides
   ring_endomorphism ring_irreducible ring_monomorphism ring_pow
   splitting_extension : thm)
  deriving Inhabited

/-- What finite_fields.ml uses from Session besides theorems. -/
structure FiniteFieldsDeps where
  new_definition : String → ExceptT String IO thm
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_ARITH_TAC : tactic
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  ASM_MESON_TAC : List thm → tactic
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  TAUT : term → ExceptT String IO thm
  INDUCT_TAC : tactic
  RING_RULE : term → ExceptT String IO thm  -- ringtheory.ml's RING_RULE
  FIELD_TAC : tactic  -- ringtheory.ml's FIELD_TAC
  GROUP_TAC : tactic  -- grouptheory.ml's GROUP_TAC
  NUM_REDUCE_CONV : ioconv  -- calc_num.ml's NUM_REDUCE_CONV
  HAS_SIZE_CONV : ioconv  -- card.ml's HAS_SIZE_CONV
  EXPAND_CASES_CONV : ioconv  -- calc_num.ml's EXPAND_CASES_CONV
  DIVIDES_CONV : ioconv  -- prime.ml's DIVIDES_CONV
  prioritize_num : IO Unit  -- prioritize_num ()
  num_CONV : ioconv  -- calc_num.ml's num_CONV
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

/- ------------------------------------------------------------------------- -/
/- Two basic facts on a finite field f: x^|f| = x for all x, and |f| is a    -/
/- power of the characteristic of f with a nonzero exponent.                 -/
/- ------------------------------------------------------------------------- -/

structure BasicFacts where
  -- @@FIELDS
  FINITE_FIELD_ELEMENT_POW : thm
  FINITE_FIELD_CARD_CHAR_POWER : thm
  deriving Inhabited

@[nospecialize]
def setupBasicFacts [HolBase] (D : FiniteFieldsDeps) :
    ExceptT String IO BasicFacts := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, prioritize_num, .. } := D
  let { DIVIDES_PRIME_PRIME, FIELD_IMP_INTEGRAL_DOMAIN, FINITE_INTEGRAL_DOMAIN_CHAR,
        FINITE_INTEGRAL_DOMAIN_POW_CARD, FINITE_INTEGRAL_DOMAIN_SIZE,
        LEFT_IMP_EXISTS_THM, .. } := D.core1
  let { PRIME_DIVEXP, RING_CHAR_DIVIDES_ORDER, .. } := D.core2
  -- @@SCOPE END
  prioritize_num

  let FINITE_FIELD_ELEMENT_POW ← prove
   r"!f:A ring.
        field f /\ FINITE(ring_carrier f)
        ==> !x. x IN ring_carrier f
                ==> ring_pow f x (CARD(ring_carrier f)) = x"
   (SIMP_TAC [FINITE_INTEGRAL_DOMAIN_POW_CARD, FIELD_IMP_INTEGRAL_DOMAIN])

  let FINITE_FIELD_CARD_CHAR_POWER ← prove
   r"!f:A ring.
        field f /\ FINITE(ring_carrier f)
        ==> ?e. ~(e = 0) /\ CARD(ring_carrier f) = ring_char f EXP e"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"f:A ring") FINITE_INTEGRAL_DOMAIN_SIZE) THEN
    ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"p:num", ← q r"e:num"] THEN STRIP_TAC THEN
    EXISTS_TAC (← q r"e:num") THEN ASM_REWRITE_TAC [] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC (← ISPEC (← q r"f:A ring") RING_CHAR_DIVIDES_ORDER) THEN
    MP_TAC (← ISPEC (← q r"f:A ring") FINITE_INTEGRAL_DOMAIN_CHAR) THEN
    ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN] THEN
    ASM_MESON_TAC [PRIME_DIVEXP, DIVIDES_PRIME_PRIME])

  -- @@RETURN BEGIN
  return { FINITE_FIELD_ELEMENT_POW, FINITE_FIELD_CARD_CHAR_POWER }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- The multiplicative group of a finite field. In a finite field k with q    -/
/- elements x^(q-1) = 1 exactly for the nonzero x, so X^d - 1 has d roots in -/
/- k for every divisor d of q - 1, and k has an element of order q - 1, a    -/
/- primitive root, of which every nonzero element is a power.                -/
/- ------------------------------------------------------------------------- -/

structure MultiplicativeGroup where
  -- @@FIELDS
  FINITE_INTEGRAL_DOMAIN_POW_CARD_SUB_1 : thm
  FINITE_FIELD_ROOTS_OF_UNITY : thm
  FINITE_FIELD_PRIMITIVE_ROOT : thm
  FINITE_FIELD_CYCLIC_UNIT_GROUP : thm
  deriving Inhabited

@[nospecialize]
def setupMultiplicativeGroup [HolBase] (D : FiniteFieldsDeps) :
    ExceptT String IO MultiplicativeGroup := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, SET_RULE, .. } := D
  let { CARD_DELETE, CYCLIC_GROUP_ELEMENT_ORDER, DIVIDES_GCD_LEFT, DIVIDES_REFL,
        DIVIDES_ZERO, EXTENSION, FIELD_IMP_INTEGRAL_DOMAIN, FIELD_UNIT,
        FIELD_UNIT_GROUP, FINITE_DIFF, FINITE_FIELD_CARD_GE_2,
        FINITE_FIELD_CARD_ROOTS_OF_UNITY, FINITE_INTEGRAL_DOMAIN_IMP_FIELD,
        FINITE_INTEGRAL_DOMAIN_POW_CARD, FINITE_RESTRICT, GROUP_ELEMENT_ORDER_UNIQUE,
        HAS_SIZE, INTEGRAL_DOMAIN_MUL_LCANCEL, INTEGRAL_DOMAIN_NONTRIVIAL, IN_DIFF,
        IN_ELIM_THM, IN_IMAGE, IN_SING, LE_1, .. } := D.core1
  let { MONO_EXISTS, RING_0, RING_1, RING_MUL_RID, RING_POW, RING_POW_EQ_1,
        RING_POW_ZERO, ROOTS_OF_UNITY_HAS_SIZE_PRIMITIVE, ROOTS_OF_UNITY_RING_ORDER,
        UNIT_GROUP, UNIT_GROUP_POW, ring_pow, .. } := D.core2
  -- @@SCOPE END

  let FINITE_INTEGRAL_DOMAIN_POW_CARD_SUB_1 ← prove
   r"!r x:A.
        integral_domain r /\ FINITE(ring_carrier r) /\ x IN ring_carrier r
        ==> (ring_pow r x (CARD(ring_carrier r) - 1) = ring_1 r <=>
             ~(x = ring_0 r))"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"2 <= CARD(ring_carrier(r:A ring))") ASSUME_TAC THENL
     [ASM_MESON_TAC [FINITE_FIELD_CARD_GE_2, FINITE_INTEGRAL_DOMAIN_IMP_FIELD],
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"x:A = ring_0 r") THEN ASM_REWRITE_TAC [RING_POW_ZERO] THENL
     [COND_CASES_TAC THENL
       [ASM_ARITH_TAC, ASM_MESON_TAC [INTEGRAL_DOMAIN_NONTRIVIAL]],
      ALL_TAC] THEN
    MATCH_MP_TAC (← ISPEC (← q r"r:A ring") INTEGRAL_DOMAIN_MUL_LCANCEL) THEN
    EXISTS_TAC (← q r"x:A") THEN ASM_SIMP_TAC [RING_POW, RING_1, RING_MUL_RID] THEN
    REWRITE_TAC [← GSYM (← CONJUNCT2 ring_pow)] THEN
    SUBGOAL_THEN (← q r"SUC(CARD(ring_carrier(r:A ring)) - 1) = CARD(ring_carrier r)")
    SUBST1_TAC THENL
     [ASM_ARITH_TAC, ASM_SIMP_TAC [FINITE_INTEGRAL_DOMAIN_POW_CARD]])

  let FINITE_FIELD_ROOTS_OF_UNITY ← prove
   r"!(k:A ring) d.
        field k /\ FINITE(ring_carrier k)
        ==> ({x | x IN ring_carrier k /\ ring_pow k x d = ring_1 k}
             HAS_SIZE d <=>
             d divides CARD(ring_carrier k) - 1)"
   (← do
    let s1 ← SET_RULE (← q r"{x | x IN s} = s")
    pure (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [HAS_SIZE, FINITE_RESTRICT] THEN
    ASM_CASES_TAC (← q r"d = 0") THENL
     [ASM_REWRITE_TAC [ring_pow, DIVIDES_ZERO, s1] THEN
      MP_TAC (← ISPEC (← q r"k:A ring") FINITE_FIELD_CARD_GE_2) THEN
      ASM_REWRITE_TAC [] THEN ARITH_TAC,
      ASM_SIMP_TAC [FINITE_FIELD_CARD_ROOTS_OF_UNITY, LE_1, DIVIDES_GCD_LEFT]]))

  let FINITE_FIELD_PRIMITIVE_ROOT ← prove
   r"!k:A ring.
        field k /\ FINITE(ring_carrier k)
        ==> ?g. g IN ring_carrier k /\
                ring_order k g = CARD(ring_carrier k) - 1 /\
                !x. x IN ring_carrier k /\ ~(x = ring_0 k)
                    ==> ?n. ring_pow k g n = x"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN) THEN
    SUBGOAL_THEN (← q r"2 <= CARD(ring_carrier(k:A ring))") ASSUME_TAC THENL
     [ASM_SIMP_TAC [FINITE_FIELD_CARD_GE_2], ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"k:A ring", ← q r"CARD(ring_carrier(k:A ring)) - 1"]
      FINITE_FIELD_ROOTS_OF_UNITY) THEN
    ASM_REWRITE_TAC [DIVIDES_REFL] THEN DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"k:A ring", ← q r"CARD(ring_carrier(k:A ring)) - 1"]
      ROOTS_OF_UNITY_HAS_SIZE_PRIMITIVE) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC (← q r"g:A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MP_TAC (← ISPECL [← q r"k:A ring", ← q r"g:A", ← q r"CARD(ring_carrier(k:A ring)) - 1"]
      ROOTS_OF_UNITY_RING_ORDER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC, ALL_TAC] THEN
    DISCH_THEN (MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_IMAGE] THEN
    DISCH_TAC THEN X_GEN_TAC (← q r"x:A") THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:A")) THEN
    ASM_SIMP_TAC [FINITE_INTEGRAL_DOMAIN_POW_CARD_SUB_1] THEN MESON_TAC [])

  let FINITE_FIELD_CYCLIC_UNIT_GROUP ← prove
   r"!k:A ring.
        field k /\ FINITE(ring_carrier k) ==> cyclic_group(unit_group k)"
   (← do
    let s1 ← SET_RULE (← q r"{x:A | x IN s /\ ~(x = a)} = s DELETE a")
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"k:A ring") FINITE_FIELD_PRIMITIVE_ROOT) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"g:A") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"~(g:A = ring_0 k)") ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q r"k:A ring", ← q r"g:A"]
        FINITE_INTEGRAL_DOMAIN_POW_CARD_SUB_1) THEN
      ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, RING_POW_EQ_1, DIVIDES_REFL],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(g:A) IN group_carrier(unit_group k)") ASSUME_TAC THENL
     [ASM_SIMP_TAC [FIELD_UNIT_GROUP, IN_DIFF, IN_SING], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"FINITE(group_carrier(unit_group(k:A ring)))") ASSUME_TAC THENL
     [ASM_SIMP_TAC [FIELD_UNIT_GROUP, FINITE_DIFF], ALL_TAC] THEN
    ASM_SIMP_TAC [CYCLIC_GROUP_ELEMENT_ORDER] THEN EXISTS_TAC (← q r"g:A") THEN
    ASM_SIMP_TAC [GROUP_ELEMENT_ORDER_UNIQUE, UNIT_GROUP_POW, UNIT_GROUP,
                 RING_POW_EQ_1] THEN
    ASM_SIMP_TAC [FIELD_UNIT, CARD_DELETE, RING_0, s1]))

  -- @@RETURN BEGIN
  return { FINITE_INTEGRAL_DOMAIN_POW_CARD_SUB_1, FINITE_FIELD_ROOTS_OF_UNITY,
           FINITE_FIELD_PRIMITIVE_ROOT, FINITE_FIELD_CYCLIC_UNIT_GROUP }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Subfields and homomorphisms. A finite field with a subfield s has |s|^d   -/
/- elements, d the degree over s. A homomorphism from a finite field k into  -/
/- an integral domain l maps k onto the set of solutions of x^|k| = x, so    -/
/- all such homomorphisms have the same image. There is a homomorphism from  -/
/- k into a finite field l exactly when |l| is a power of |k|: then the      -/
/- characteristics agree, the degree of k over its prime field divides the   -/
/- degree of l over the image of that prime field, and the intermediate      -/
/- field of l of the same degree has |k| elements, so it is isomorphic to k  -/
/- (ISOMORPHIC_FINITE_FIELDS).                                               -/
/- ------------------------------------------------------------------------- -/

structure SubfieldsHomomorphisms where
  -- @@FIELDS
  FINITE_FIELD_SUBFIELD_CARD : thm
  FINITE_FIELD_HOMOMORPHISM_IMAGE : thm
  FINITE_FIELD_HOMOMORPHISM_EXISTS : thm
  deriving Inhabited

@[nospecialize]
def setupSubfieldsHomomorphisms [HolBase] (D : FiniteFieldsDeps) :
    ExceptT String IO SubfieldsHomomorphisms := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, .. } := D
  let { CARD_EQ_0, CARD_EXTENSION_DEGREE, CARD_IMAGE_INJ,
        CARRIER_SUBFIELD_GENERATED_SUBFIELD, CARRIER_SUBFIELD_OF, DIVIDES_PRIME_PRIME,
        EQ_EXP, EXISTS_UNIQUE_THM, EXP_EXP, FIELD_EXTENSION_INTO_SUBFIELD_GENERATED,
        FIELD_EXTENSION_SUBFIELD_GENERATED, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_IMP_NONTRIVIAL_RING, FIELD_RING_HOMOMORPHISM_MONOMORPHISM,
        FIELD_SUBFIELD_GENERATED, FINITE_FIELD_INTERMEDIATE_FIELDS, FINITE_IMAGE,
        FINITE_INTEGRAL_DOMAIN_CHAR, FINITE_INTEGRAL_DOMAIN_SIZE,
        FINITE_SUBFIELD_EXPLICIT, FINITE_SUBSET, HAS_SIZE,
        INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING, ISOMORPHIC_FINITE_FIELDS, I_O_ID,
        LEFT_IMP_EXISTS_THM, .. } := D.core1
  let { PRIME_DIVEXP, PRIME_SUBFIELD_HOMOMORPHISM_EXISTS, RING_CARRIER_NONEMPTY,
        RING_CARRIER_SUBFIELD_GENERATED_SUBSET, RING_CHAR_DIVIDES_ORDER,
        RING_HOMOMORPHISM_COMPOSE, RING_HOMOMORPHISM_SUBFIELD_INCLUSION,
        RING_ISOMORPHISM_IMP_HOMOMORPHISM, SUBFIELD_OF_MONOMORPHIC_IMAGE,
        TRIVIAL_RING_HAS_SIZE_1, divides, field_extension, isomorphic_ring,
        ring_monomorphism, .. } := D.core2
  -- @@SCOPE END

  let FINITE_FIELD_SUBFIELD_CARD ← prove
   r"!(l:A ring) s.
        field l /\ FINITE(ring_carrier l) /\ s subfield_of l
        ==> ?d. CARD(ring_carrier l) = CARD s EXP d"
   (REPEAT STRIP_TAC THEN
    EXISTS_TAC (← q r"extension_degree(subfield_generated l s,l) (I:A->A)") THEN
    MP_TAC (← ISPECL [← q r"I:A->A", ← q r"subfield_generated l (s:A->bool)", ← q r"l:A ring"]
      CARD_EXTENSION_DEGREE) THEN
    ASM_SIMP_TAC [FIELD_EXTENSION_SUBFIELD_GENERATED,
                 CARRIER_SUBFIELD_GENERATED_SUBFIELD])

  let FINITE_FIELD_HOMOMORPHISM_IMAGE ← prove
   r"!(h:A->B) k l.
        field k /\ FINITE(ring_carrier k) /\ integral_domain l /\
        ring_homomorphism(k,l) h
        ==> IMAGE h (ring_carrier k) =
            {x | x IN ring_carrier l /\
                 ring_pow l x (CARD(ring_carrier k)) = x}"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"ring_monomorphism(k,l) (h:A->B)") ASSUME_TAC THENL
     [MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
      ASM_SIMP_TAC [INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"CARD(IMAGE (h:A->B) (ring_carrier k)) = CARD(ring_carrier k)")
    (SUBST1_TAC o SYM) THENL
     [MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_MESON_TAC [ring_monomorphism],
      MATCH_MP_TAC FINITE_SUBFIELD_EXPLICIT THEN
      ASM_SIMP_TAC [FINITE_IMAGE] THEN
      MATCH_MP_TAC SUBFIELD_OF_MONOMORPHIC_IMAGE THEN
      EXISTS_TAC (← q r"k:A ring") THEN ASM_REWRITE_TAC [CARRIER_SUBFIELD_OF]])

  let FINITE_FIELD_HOMOMORPHISM_EXISTS ← prove
   r"!(k:A ring) (l:B ring).
        field k /\ FINITE(ring_carrier k) /\ field l /\ FINITE(ring_carrier l)
        ==> ((?h. ring_homomorphism(k,l) h) <=>
             ?d. CARD(ring_carrier l) = CARD(ring_carrier k) EXP d)"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [DISCH_THEN (X_CHOOSE_TAC (← q r"h:A->B")) THEN
      EXISTS_TAC (← q r"extension_degree(k,l) (h:A->B)") THEN
      MATCH_MP_TAC CARD_EXTENSION_DEGREE THEN
      ASM_REWRITE_TAC [field_extension] THEN
      MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
      ASM_SIMP_TAC [FIELD_IMP_NONTRIVIAL_RING],
      DISCH_THEN (X_CHOOSE_TAC (← q r"d:num"))] THEN
    SUBGOAL_THEN (← q r"ring_char(k:A ring) = ring_char(l:B ring)") ASSUME_TAC THENL
     [MP_TAC (← ISPEC (← q r"k:A ring") FINITE_INTEGRAL_DOMAIN_SIZE) THEN
      ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"p:num", ← q r"m:num"] THEN STRIP_TAC THEN
      SUBGOAL_THEN (← q r"prime(ring_char(k:A ring)) /\ prime(ring_char(l:B ring))")
      STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC [FINITE_INTEGRAL_DOMAIN_CHAR, FIELD_IMP_INTEGRAL_DOMAIN],
        ALL_TAC] THEN
      MP_TAC (← ISPEC (← q r"k:A ring") RING_CHAR_DIVIDES_ORDER) THEN
      MP_TAC (← ISPEC (← q r"l:B ring") RING_CHAR_DIVIDES_ORDER) THEN
      ASM_REWRITE_TAC [EXP_EXP] THEN
      ASM_MESON_TAC [PRIME_DIVEXP, DIVIDES_PRIME_PRIME],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"k:A ring", ← q r"l:B ring"]
      PRIME_SUBFIELD_HOMOMORPHISM_EXISTS) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"j:A->B")) THEN
    SUBGOAL_THEN
     (← q r"field(subfield_generated k {ring_0 k:A}) /\
      FINITE(ring_carrier(subfield_generated k {ring_0 k:A})) /\
      field_extension(subfield_generated k {ring_0 k},k) (I:A->A) /\
      field_extension(subfield_generated k {ring_0 k},l) (j:A->B)")
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC [FIELD_EXTENSION_SUBFIELD_GENERATED] THEN
      ASM_SIMP_TAC [field_extension, FIELD_SUBFIELD_GENERATED] THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC [FINITE_SUBSET, RING_CARRIER_SUBFIELD_GENERATED_SUBSET],
        MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
        ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, FIELD_IMP_NONTRIVIAL_RING]],
      ABBREV_TAC (← q r"k0 = subfield_generated k {ring_0 k:A}")] THEN
    MP_TAC (← ISPECL [← q r"I:A->A", ← q r"k0:A ring", ← q r"k:A ring"] CARD_EXTENSION_DEGREE) THEN
    MP_TAC (← ISPECL [← q r"j:A->B", ← q r"k0:A ring", ← q r"l:B ring"] CARD_EXTENSION_DEGREE) THEN
    ASM_REWRITE_TAC [] THEN
    ABBREV_TAC (← q r"a = extension_degree(k0,k) (I:A->A)") THEN
    ABBREV_TAC (← q r"b = extension_degree(k0,l) (j:A->B)") THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN (← q r"a divides b") ASSUME_TAC THENL
     [REWRITE_TAC [divides] THEN EXISTS_TAC (← q r"d:num") THEN
      SUBGOAL_THEN
       (← q r"CARD(ring_carrier(k0:A ring)) EXP b = CARD(ring_carrier k0) EXP (a * d)")
      MP_TAC THENL
       [REWRITE_TAC [← GSYM EXP_EXP] THEN ASM_MESON_TAC [], ALL_TAC] THEN
      REWRITE_TAC [EQ_EXP] THEN
      ASM_SIMP_TAC [CARD_EQ_0, RING_CARRIER_NONEMPTY] THEN
      ASM_MESON_TAC [HAS_SIZE, TRIVIAL_RING_HAS_SIZE_1,
                    FIELD_IMP_NONTRIVIAL_RING],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"j:A->B", ← q r"k0:A ring", ← q r"l:B ring", ← q r"a:num"]
      FINITE_FIELD_INTERMEDIATE_FIELDS) THEN
    ASM_REWRITE_TAC [EXISTS_UNIQUE_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"s:B->bool") STRIP_ASSUME_TAC o CONJUNCT1) THEN
    MP_TAC (← ISPECL [← q r"k:A ring", ← q r"subfield_generated l (s:B->bool)"]
      ISOMORPHIC_FINITE_FIELDS) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED] THEN CONJ_TAC THENL
       [ASM_MESON_TAC [FINITE_SUBSET, RING_CARRIER_SUBFIELD_GENERATED_SUBSET],
        ALL_TAC] THEN
      MP_TAC (← ISPECL [← q r"j:A->B", ← q r"k0:A ring", ← q r"subfield_generated l (s:B->bool)"]
        CARD_EXTENSION_DEGREE) THEN
      ASM_SIMP_TAC [FIELD_EXTENSION_INTO_SUBFIELD_GENERATED] THEN
      ANTS_TAC THENL
       [ASM_MESON_TAC [FINITE_SUBSET, RING_CARRIER_SUBFIELD_GENERATED_SUBSET],
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC []],
      ALL_TAC] THEN
    REWRITE_TAC [isomorphic_ring, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"f:A->B") THEN
    DISCH_THEN (ASSUME_TAC o MATCH_MP RING_ISOMORPHISM_IMP_HOMOMORPHISM) THEN
    EXISTS_TAC (← q r"f:A->B") THEN
    MP_TAC (← ISPECL [← q r"k:A ring", ← q r"subfield_generated l (s:B->bool)", ← q r"l:B ring",
                   ← q r"f:A->B", ← q r"I:B->B"] RING_HOMOMORPHISM_COMPOSE) THEN
    ASM_REWRITE_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION, I_O_ID])

  -- @@RETURN BEGIN
  return { FINITE_FIELD_SUBFIELD_CARD, FINITE_FIELD_HOMOMORPHISM_IMAGE,
           FINITE_FIELD_HOMOMORPHISM_EXISTS }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Norm and trace of finite fields. Let l be a finite extension of k, where  -/
/- k has q elements and l has q^n. The norm is x |-> x^((q^n - 1)/(q - 1)),  -/
/- the product of the Frobenius conjugates                                   -/
/- (ALGEBRA_TRACE_NORM_FINITE_FIELD). The trace is surjective since l is     -/
/- separable over k, and the norm maps the nonzero elements of l onto those  -/
/- of k, since the norm of a primitive root of l has order q - 1. By         -/
/- translation every element of k is the trace of q^(n-1) elements of l, and -/
/- every nonzero element of k the norm of (q^n - 1)/(q - 1) elements.        -/
/- Hilbert 90 for the Galois group generated by the Frobenius map: the       -/
/- elements of norm 1 are the (q-1)-th powers of the nonzero elements, those -/
/- of trace 0 the elements y^q - y.                                          -/
/- ------------------------------------------------------------------------- -/

structure NormTrace where
  -- @@FIELDS
  ALGEBRA_NORM_FINITE_FIELD_POW : thm
  ALGEBRA_TRACE_SURJECTIVE_FINITE : thm
  ALGEBRA_NORM_SURJECTIVE_FINITE : thm
  ALGEBRA_TRACE_FIBRE_FINITE : thm
  ALGEBRA_NORM_FIBRE_FINITE : thm
  HILBERT_90_FINITE_FIELD : thm
  HILBERT_90_ADDITIVE_FINITE_FIELD : thm
  deriving Inhabited

@[nospecialize]
def setupNormTrace [HolBase] (D : FiniteFieldsDeps) (BMultiplicativeGroup : MultiplicativeGroup) :
    ExceptT String IO NormTrace := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, FIELD_TAC, INDUCT_TAC, RING_RULE, .. } := D
  let { ALGEBRA_NORM_EQ_0, ALGEBRA_NORM_INV, ALGEBRA_NORM_MUL, ALGEBRA_NORM_POW,
        ALGEBRA_TRACE_ADD, ALGEBRA_TRACE_NEG, ALGEBRA_TRACE_NORM_FINITE_FIELD,
        ALGEBRA_TRACE_NORM_GALOIS, ALGEBRA_TRACE_NORM_IN_CARRIER, ALGEBRA_TRACE_SUB,
        ALGEBRA_TRACE_SURJECTIVE, CARD_DELETE, CARD_EQ_0, CARD_EQ_FIBRES_HAS_SIZE,
        CARD_EQ_IMAGE, CARD_EXTENSION_DEGREE, DIVIDES_DIV_MULT, DIVIDES_EXP_MINUS1,
        DIV_MULT, EXP, EXP_EQ_0, EXP_ZERO, EXTENSION, FIELD_DIV_EQ_0,
        FIELD_EXTENSION_IMP_HOMOMORPHISM, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_IMP_NONTRIVIAL_RING, FIELD_INV_EQ_0, FIELD_MUL_EQ_0, FIELD_MUL_RINV,
        FIELD_POW_EQ_0, FIELD_UNIT, FINITE_DELETE, FINITE_FIELD_CARD_GE_2,
        FINITE_FIELD_GALOIS_EXTENSION, FINITE_NUMSEG_LT,
        FINITE_RING_MONOMORPHIC_PREIMAGE, FORALL_IN_IMAGE, GALOIS_GROUP_FINITE_FIELD,
        GALOIS_IMP_SEPARABLE_EXTENSION, HILBERT_90_ADDITIVE_CYCLIC_EQ,
        HILBERT_90_CYCLIC_EQ, INTEGRAL_DOMAIN_MUL_RCANCEL, IN_DELETE, IN_ELIM_THM,
        IN_IMAGE, LEFT_ADD_DISTRIB, LT_REFL, .. } := D.core1
  let { MULT_CLAUSES, NOT_SUC, NSUM_CLAUSES, NUMSEG_CLAUSES_LT, RING_0, RING_1,
        RING_ADD, RING_ADD_LZERO, RING_ADD_RCANCEL, RING_CARRIER_NONEMPTY, RING_DIV,
        RING_HOMOMORPHISM_1, RING_INV, RING_INV_INV, RING_MONOMORPHISM_EQ_0,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MONOMORPHISM_INJECTIVE_EQ, RING_MUL,
        RING_MUL_LID, RING_NEG, RING_NEG_EQ_0, RING_ORDER_0,
        RING_ORDER_MONOMORPHIC_IMAGE, RING_ORDER_POW, RING_POW, RING_POW_INV,
        RING_PRODUCT_NSUM, RING_SUB, RING_SUB_REFL, ROOTS_OF_UNITY_RING_ORDER, SUBSET,
        SUBSET_ANTISYM, SUB_0, SUC_SUB1, divides, field_extension, ring_div, ring_pow, .. } := D.core2
  let { FINITE_FIELD_PRIMITIVE_ROOT, FINITE_INTEGRAL_DOMAIN_POW_CARD_SUB_1, .. } := BMultiplicativeGroup
  -- @@SCOPE END

  let ALGEBRA_NORM_FINITE_FIELD_POW ← (do
    let lemma ← prove
     r"!q n. (q - 1) * nsum {i | i < n} (\i. q EXP i) = q EXP n - 1"
     (GEN_TAC THEN ASM_CASES_TAC (← q r"q = 0") THENL
       [ASM_REWRITE_TAC [EXP_ZERO, SUB_0, MULT_CLAUSES] THEN
        GEN_TAC THEN COND_CASES_TAC THEN ARITH_TAC,
        ALL_TAC] THEN
      INDUCT_TAC THEN
      ASM_SIMP_TAC [NUMSEG_CLAUSES_LT, NSUM_CLAUSES, FINITE_NUMSEG_LT,
                   IN_ELIM_THM, LT_REFL, EXP, LEFT_ADD_DISTRIB] THENL
       [ARITH_TAC, ALL_TAC] THEN
      SUBGOAL_THEN (← q r"~(q EXP n = 0)") MP_TAC THENL
       [ASM_REWRITE_TAC [EXP_EQ_0], ALL_TAC] THEN
      UNDISCH_TAC (← q r"~(q = 0)") THEN
      SPEC_TAC (← q r"q EXP n", ← q r"a:num") THEN SPEC_TAC (← q r"q:num", ← q r"q:num") THEN
      INDUCT_TAC THEN REWRITE_TAC [NOT_SUC, SUC_SUB1, MULT_CLAUSES] THEN
      ARITH_TAC)
    prove
     r"!(h:A->B) k l x.
        field_extension(k,l) h /\ FINITE(ring_carrier l) /\ x IN ring_carrier l
        ==> h(algebra_norm(k,l) h x) =
            ring_pow l x ((CARD(ring_carrier l) - 1) DIV
                          (CARD(ring_carrier k) - 1))"
     (REPEAT GEN_TAC THEN STRIP_TAC THEN
      FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
      SUBGOAL_THEN (← q r"FINITE(ring_carrier(k:A ring))") ASSUME_TAC THENL
       [ASM_MESON_TAC [FINITE_RING_MONOMORPHIC_PREIMAGE], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"2 <= CARD(ring_carrier(k:A ring))") ASSUME_TAC THENL
       [ASM_SIMP_TAC [FINITE_FIELD_CARD_GE_2], ALL_TAC] THEN
      MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"x:B"]
        ALGEBRA_TRACE_NORM_FINITE_FIELD) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o CONJUNCT1) THEN
      ASM_SIMP_TAC [← GSYM RING_PRODUCT_NSUM, FINITE_NUMSEG_LT] THEN
      AP_TERM_TAC THEN
      MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring"] CARD_EXTENSION_DEGREE) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC [← GSYM lemma] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC DIV_MULT THEN ASM_ARITH_TAC))

  let ALGEBRA_TRACE_SURJECTIVE_FINITE ← prove
   r"!(h:A->B) k l.
        field_extension(k,l) h /\ FINITE(ring_carrier l)
        ==> IMAGE (algebra_trace(k,l) h) (ring_carrier l) = ring_carrier k"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC ALGEBRA_TRACE_SURJECTIVE THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring"]
      FINITE_FIELD_GALOIS_EXTENSION) THEN
    ASM_SIMP_TAC [GALOIS_IMP_SEPARABLE_EXTENSION])

  let ALGEBRA_NORM_SURJECTIVE_FINITE ← prove
   r"!(h:A->B) k l.
        field_extension(k,l) h /\ FINITE(ring_carrier l)
        ==> IMAGE (algebra_norm(k,l) h) (ring_carrier l DELETE ring_0 l) =
            ring_carrier k DELETE ring_0 k"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_HOMOMORPHISM) THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    SUBGOAL_THEN (← q r"finite_extension(k,l) (h:A->B) /\ FINITE(ring_carrier k)")
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC [FINITE_FIELD_GALOIS_EXTENSION,
                    FINITE_RING_MONOMORPHIC_PREIMAGE],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"2 <= CARD(ring_carrier(k:A ring)) /\ 2 <= CARD(ring_carrier(l:B ring))")
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [FINITE_FIELD_CARD_GE_2], ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_DELETE] THEN
      ASM_SIMP_TAC [ALGEBRA_TRACE_NORM_IN_CARRIER, ALGEBRA_NORM_EQ_0],
      ALL_TAC] THEN
    MP_TAC (← ISPEC (← q r"l:B ring") FINITE_FIELD_PRIMITIVE_ROOT) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"g:B") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"~(g:B = ring_0 l)") ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC (← q r"ring_order l (ring_0 l:B) = CARD(ring_carrier l) - 1") THEN
      ASM_SIMP_TAC [RING_ORDER_0, FIELD_IMP_NONTRIVIAL_RING] THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"g:B"]
      ALGEBRA_NORM_FINITE_FIELD_POW) THEN
    MP_TAC (← ISPECL [← q r"extension_degree(k,l) (h:A->B)",
                   ← q r"CARD(ring_carrier(k:A ring))"] DIVIDES_EXP_MINUS1) THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring"] CARD_EXTENSION_DEGREE) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [DIVIDES_DIV_MULT] THEN
    ABBREV_TAC
     (← q r"m = (CARD(ring_carrier(l:B ring)) - 1) DIV
          (CARD(ring_carrier(k:A ring)) - 1)") THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN (← q r"~(m = 0)") ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC (← q r"m * (CARD(ring_carrier(k:A ring)) - 1) =
                   CARD(ring_carrier(l:B ring)) - 1") THEN
      ASM_REWRITE_TAC [MULT_CLAUSES] THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"ring_order k (algebra_norm(k,l) (h:A->B) g) = CARD(ring_carrier k) - 1")
    ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring",
                     ← q r"algebra_norm(k,l) (h:A->B) g"]
        RING_ORDER_MONOMORPHIC_IMAGE) THEN
      ASM_SIMP_TAC [ALGEBRA_TRACE_NORM_IN_CARRIER] THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN
      MP_TAC (← ISPECL [← q r"l:B ring", ← q r"g:B", ← q r"m:num"] RING_ORDER_POW) THEN
      ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
       [REWRITE_TAC [divides] THEN
        EXISTS_TAC (← q r"CARD(ring_carrier(k:A ring)) - 1") THEN
        ASM_REWRITE_TAC [],
        DISCH_THEN SUBST1_TAC] THEN
      UNDISCH_TAC (← q r"m * (CARD(ring_carrier(k:A ring)) - 1) =
                   CARD(ring_carrier(l:B ring)) - 1") THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [DIV_MULT],
      ALL_TAC] THEN
    REWRITE_TAC [SUBSET, IN_DELETE, IN_IMAGE] THEN
    X_GEN_TAC (← q r"a:A") THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"k:A ring", ← q r"algebra_norm(k,l) (h:A->B) g",
                   ← q r"CARD(ring_carrier(k:A ring)) - 1"]
      ROOTS_OF_UNITY_RING_ORDER) THEN
    ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, ALGEBRA_TRACE_NORM_IN_CARRIER] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"a:A") o REWRITE_RULE [EXTENSION] o CONJUNCT1) THEN
    ASM_SIMP_TAC [IN_ELIM_THM, IN_IMAGE, FINITE_INTEGRAL_DOMAIN_POW_CARD_SUB_1,
                 FIELD_IMP_INTEGRAL_DOMAIN] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"j:num") (SUBST1_TAC o CONJUNCT1)) THEN
    EXISTS_TAC (← q r"ring_pow l (g:B) j") THEN
    ASM_SIMP_TAC [ALGEBRA_NORM_POW, RING_POW, FIELD_POW_EQ_0])

  let ALGEBRA_TRACE_FIBRE_FINITE ← prove
   r"!(h:A->B) k l a.
        field_extension(k,l) h /\ FINITE(ring_carrier l) /\ a IN ring_carrier k
        ==> {x | x IN ring_carrier l /\ algebra_trace(k,l) h x = a} HAS_SIZE
            CARD(ring_carrier l) DIV CARD(ring_carrier k)"
   (← do
    let r1 ← RING_RULE
     (← q r"!r x z:B. x IN ring_carrier r /\ z IN ring_carrier r
                  ==> z = ring_add r (ring_sub r z x) x")
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_HOMOMORPHISM) THEN
    SUBGOAL_THEN (← q r"finite_extension(k,l) (h:A->B)") ASSUME_TAC THENL
     [ASM_MESON_TAC [FINITE_FIELD_GALOIS_EXTENSION], ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring"]
      ALGEBRA_TRACE_SURJECTIVE_FINITE) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
    MATCH_MP_TAC (← ISPECL
     [← q r"algebra_trace(k,l) (h:A->B)", ← q r"ring_carrier l:B->bool",
      ← q r"{y:B | y IN ring_carrier l /\ algebra_trace(k,l) (h:A->B) y = ring_0 k}"]
     CARD_EQ_FIBRES_HAS_SIZE) THEN
    ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN
    SUBGOAL_THEN
     (← q r"{z | z IN ring_carrier l /\
           algebra_trace(k,l) (h:A->B) z = algebra_trace(k,l) h x} =
      IMAGE (\y. ring_add l y x)
            {y | y IN ring_carrier l /\ algebra_trace(k,l) h y = ring_0 k}")
    SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_IMAGE] THEN
      X_GEN_TAC (← q r"z:B") THEN EQ_TAC THENL
       [STRIP_TAC THEN EXISTS_TAC (← q r"ring_sub l z x:B") THEN
        ASM_SIMP_TAC [RING_SUB, ALGEBRA_TRACE_SUB, RING_SUB_REFL,
                     ALGEBRA_TRACE_NORM_IN_CARRIER] THEN
        MATCH_MP_TAC r1 THEN
        ASM_REWRITE_TAC [],
        DISCH_THEN (X_CHOOSE_THEN (← q r"y:B") STRIP_ASSUME_TAC) THEN
        ASM_SIMP_TAC [RING_ADD, ALGEBRA_TRACE_ADD, RING_ADD_LZERO,
                     ALGEBRA_TRACE_NORM_IN_CARRIER]],
      MATCH_MP_TAC CARD_EQ_IMAGE THEN SIMP_TAC [IN_ELIM_THM] THEN
      ASM_MESON_TAC [RING_ADD_RCANCEL]]))

  let ALGEBRA_NORM_FIBRE_FINITE ← (do
    let lemma ← prove
     r"!r x z:B. field r /\ x IN ring_carrier r /\ z IN ring_carrier r /\
                 ~(x = ring_0 r)
                 ==> z = ring_mul r (ring_mul r z (ring_inv r x)) x"
     FIELD_TAC
    prove
     r"!(h:A->B) k l a.
        field_extension(k,l) h /\ FINITE(ring_carrier l) /\
        a IN ring_carrier k /\ ~(a = ring_0 k)
        ==> {x | x IN ring_carrier l /\ algebra_norm(k,l) h x = a} HAS_SIZE
            (CARD(ring_carrier l) - 1) DIV (CARD(ring_carrier k) - 1)"
     (REPEAT GEN_TAC THEN STRIP_TAC THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_HOMOMORPHISM) THEN
      FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
      SUBGOAL_THEN (← q r"finite_extension(k,l) (h:A->B) /\ FINITE(ring_carrier k)")
      STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC [FINITE_FIELD_GALOIS_EXTENSION,
                      FINITE_RING_MONOMORPHIC_PREIMAGE],
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"{x | x IN ring_carrier l /\ algebra_norm(k,l) (h:A->B) x = a} =
        {x | x IN ring_carrier l DELETE ring_0 l /\ algebra_norm(k,l) h x = a} /\
        CARD(ring_carrier(l:B ring)) - 1 = CARD(ring_carrier l DELETE ring_0 l) /\
        CARD(ring_carrier(k:A ring)) - 1 = CARD(ring_carrier k DELETE ring_0 k)")
      (fun th => REWRITE_TAC [th]) THENL
       [ASM_SIMP_TAC [CARD_DELETE, RING_0] THEN
        REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_DELETE] THEN
        ASM_MESON_TAC [ALGEBRA_NORM_EQ_0],
        ALL_TAC] THEN
      MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring"]
        ALGEBRA_NORM_SURJECTIVE_FINITE) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC (← ISPECL
       [← q r"algebra_norm(k,l) (h:A->B)", ← q r"ring_carrier(l:B ring) DELETE ring_0 l",
        ← q r"{y:B | y IN ring_carrier l DELETE ring_0 l /\
               algebra_norm(k,l) (h:A->B) y = ring_1 k}"]
       CARD_EQ_FIBRES_HAS_SIZE) THEN
      REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC [FINITE_DELETE],
        ALL_TAC,
        ASM_SIMP_TAC [ALGEBRA_NORM_SURJECTIVE_FINITE, IN_DELETE]] THEN
      X_GEN_TAC (← q r"x:B") THEN
      DISCH_THEN (STRIP_ASSUME_TAC o REWRITE_RULE [IN_DELETE]) THEN
      SUBGOAL_THEN
       (← q r"algebra_norm(k,l) (h:A->B) x IN ring_carrier k /\
        ~(algebra_norm(k,l) h x = ring_0 k)")
      STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC [ALGEBRA_TRACE_NORM_IN_CARRIER, ALGEBRA_NORM_EQ_0],
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"{z | z IN ring_carrier l DELETE ring_0 l /\
             algebra_norm(k,l) (h:A->B) z = algebra_norm(k,l) h x} =
        IMAGE (\y. ring_mul l y x)
              {y | y IN ring_carrier l DELETE ring_0 l /\
                   algebra_norm(k,l) h y = ring_1 k}")
      SUBST1_TAC THENL
       [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_IMAGE, IN_DELETE] THEN
        X_GEN_TAC (← q r"z:B") THEN EQ_TAC THENL
         [STRIP_TAC THEN EXISTS_TAC (← q r"ring_div l z x:B") THEN
          ASM_SIMP_TAC [RING_DIV, FIELD_DIV_EQ_0] THEN
          ASM_SIMP_TAC [ring_div, ALGEBRA_NORM_MUL, ALGEBRA_NORM_INV, RING_INV,
                       FIELD_MUL_RINV] THEN
          MATCH_MP_TAC lemma THEN ASM_REWRITE_TAC [],
          DISCH_THEN (X_CHOOSE_THEN (← q r"y:B") STRIP_ASSUME_TAC) THEN
          ASM_SIMP_TAC [RING_MUL, ALGEBRA_NORM_MUL, RING_MUL_LID, FIELD_MUL_EQ_0,
                       ALGEBRA_TRACE_NORM_IN_CARRIER]],
        MATCH_MP_TAC CARD_EQ_IMAGE THEN SIMP_TAC [IN_ELIM_THM, IN_DELETE] THEN
        ASM_MESON_TAC [INTEGRAL_DOMAIN_MUL_RCANCEL, FIELD_IMP_INTEGRAL_DOMAIN]]))

  let HILBERT_90_FINITE_FIELD ← (do
    let lemma0 ← prove
     r"!(l:B ring) y z.
          field l /\ y IN ring_carrier l /\ z IN ring_carrier l /\
          ~(y = ring_0 l) /\ ~(z = ring_0 l)
          ==> ring_div l y (ring_mul l y z) = ring_inv l z"
     FIELD_TAC
    let lemma ← prove
     r"!(l:B ring) y q.
          field l /\ y IN ring_carrier l /\ ~(y = ring_0 l) /\ ~(q = 0)
          ==> ring_div l y (ring_pow l y q) = ring_pow l (ring_inv l y) (q - 1)"
     (REPEAT STRIP_TAC THEN
      SUBGOAL_THEN (← q r"ring_pow l y q = ring_mul l y (ring_pow l y (q - 1)):B")
      SUBST1_TAC THENL
       [REWRITE_TAC [← GSYM (← CONJUNCT2 ring_pow)] THEN AP_TERM_TAC THEN
        ASM_ARITH_TAC,
        ASM_SIMP_TAC [RING_POW_INV] THEN MATCH_MP_TAC lemma0 THEN
        ASM_SIMP_TAC [RING_POW, FIELD_POW_EQ_0]])
    prove
     r"!(h:A->B) k l x.
        field_extension(k,l) h /\ FINITE(ring_carrier l) /\ x IN ring_carrier l
        ==> (algebra_norm(k,l) h x = ring_1 k <=>
             ?y. y IN ring_carrier l /\ ~(y = ring_0 l) /\
                 x = ring_pow l y (CARD(ring_carrier k) - 1))"
     (REPEAT GEN_TAC THEN STRIP_TAC THEN
      FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
      SUBGOAL_THEN (← q r"~(CARD(ring_carrier(k:A ring)) = 0)") ASSUME_TAC THENL
       [ASM_MESON_TAC [CARD_EQ_0, RING_CARRIER_NONEMPTY,
                      FINITE_RING_MONOMORPHIC_PREIMAGE],
        ALL_TAC] THEN
      MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring"]
        FINITE_FIELD_GALOIS_EXTENSION) THEN
      ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
      SUBGOAL_THEN
       (← q r"algebra_norm(k,l) (h:A->B) x = ring_1 k <=>
        ring_product l (group_carrier(galois_group(k,l) h)) (\f. f x) = ring_1 l")
      SUBST1_TAC THENL
       [MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"x:B"]
          ALGEBRA_TRACE_NORM_GALOIS) THEN
        ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM o CONJUNCT1) THEN
        FIRST_ASSUM (fun th => tactic_of do
          pure (REWRITE_TAC [← GSYM (← MATCH_MP RING_HOMOMORPHISM_1 th)])) THEN
        CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC (← ISPECL [← q r"k:A ring", ← q r"l:B ring", ← q r"h:A->B"]
          RING_MONOMORPHISM_INJECTIVE_EQ) THEN
        ASM_SIMP_TAC [ALGEBRA_TRACE_NORM_IN_CARRIER, RING_1],
        ALL_TAC] THEN
      MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring"]
        GALOIS_GROUP_FINITE_FIELD) THEN
      ASM_REWRITE_TAC [] THEN
      ABBREV_TAC
       (← q r"g = \y. if y IN ring_carrier l
              then ring_pow l y (CARD(ring_carrier(k:A ring))) else y:B") THEN
      STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"g:B->B", ← q r"x:B"]
        HILBERT_90_CYCLIC_EQ) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN
       (← q r"!y:B. y IN ring_carrier l /\ ~(y = ring_0 l)
            ==> ring_div l y (g y) =
                ring_pow l (ring_inv l y) (CARD(ring_carrier(k:A ring)) - 1)")
      ASSUME_TAC THENL
       [EXPAND_TAC "g" THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC lemma THEN ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      EQ_TAC THEN DISCH_THEN (X_CHOOSE_THEN (← q r"y:B") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"ring_inv l y:B") THEN
      ASM_SIMP_TAC [RING_INV, FIELD_INV_EQ_0, RING_INV_INV, FIELD_UNIT]))

  let HILBERT_90_ADDITIVE_FINITE_FIELD ← prove
   r"!(h:A->B) k l x.
        field_extension(k,l) h /\ FINITE(ring_carrier l) /\ x IN ring_carrier l
        ==> (algebra_trace(k,l) h x = ring_0 k <=>
             ?y. y IN ring_carrier l /\
                 x = ring_sub l (ring_pow l y (CARD(ring_carrier k))) y)"
   (← do
    let r1 ← RING_RULE
     (← q r"!r x y z:B.
          x IN ring_carrier r /\ y IN ring_carrier r /\ z IN ring_carrier r
          ==> (ring_neg r x = ring_sub r y z <=> x = ring_sub r z y)")
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_HOMOMORPHISM) THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring"]
      FINITE_FIELD_GALOIS_EXTENSION) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"algebra_trace(k,l) (h:A->B) x = ring_0 k <=>
      ring_sum l (group_carrier(galois_group(k,l) h)) (\f. f(ring_neg l x)) =
      ring_0 l")
    SUBST1_TAC THENL
     [MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"ring_neg l x:B"]
        ALGEBRA_TRACE_NORM_GALOIS) THEN
      ASM_SIMP_TAC [RING_NEG, ALGEBRA_TRACE_NEG] THEN
      DISCH_THEN (SUBST1_TAC o SYM o CONJUNCT2) THEN
      MP_TAC (← ISPECL [← q r"k:A ring", ← q r"l:B ring", ← q r"h:A->B",
                     ← q r"ring_neg k (algebra_trace(k,l) (h:A->B) x)"]
        RING_MONOMORPHISM_EQ_0) THEN
      ASM_SIMP_TAC [RING_NEG, ALGEBRA_TRACE_NORM_IN_CARRIER, RING_NEG_EQ_0],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring"]
      GALOIS_GROUP_FINITE_FIELD) THEN
    ASM_REWRITE_TAC [] THEN
    ABBREV_TAC
     (← q r"g = \y. if y IN ring_carrier l
            then ring_pow l y (CARD(ring_carrier(k:A ring))) else y:B") THEN
    STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"g:B->B", ← q r"ring_neg l x:B"]
      HILBERT_90_ADDITIVE_CYCLIC_EQ) THEN
    ASM_SIMP_TAC [RING_NEG] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN ABS_TAC THEN
    EXPAND_TAC "g" THEN ASM_CASES_TAC (← q r"(y:B) IN ring_carrier l") THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC r1 THEN
    ASM_SIMP_TAC [RING_POW]))

  -- @@RETURN BEGIN
  return { ALGEBRA_NORM_FINITE_FIELD_POW, ALGEBRA_TRACE_SURJECTIVE_FINITE,
           ALGEBRA_NORM_SURJECTIVE_FINITE, ALGEBRA_TRACE_FIBRE_FINITE,
           ALGEBRA_NORM_FIBRE_FINITE, HILBERT_90_FINITE_FIELD,
           HILBERT_90_ADDITIVE_FINITE_FIELD }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Irreducible polynomials over a finite field and X^(q^n) - X. Let k have q -/
/- elements. In a finite extension l of k all elements satisfy x^(q^n) = x   -/
/- exactly when [l:k] divides n, since the Frobenius map x |-> x^q has order -/
/- [l:k] in the Galois group. For a root x of an irreducible polynomial p    -/
/- over k, applied to the field k(x) of degree deg(p) over k, this says that -/
/- x^(q^n) = x exactly when deg(p) divides n. So the elements x^(q^i) with i -/
/- < deg(p), all roots of p, are distinct; they are all the roots of p in    -/
/- any extension of k. With x in an algebraic closure: p divides X^(q^n) - X -/
/- exactly when deg(p) divides n. For n > 0 the polynomial X^(q^n) - X is    -/
/- monic and separable, so it is the product of its monic irreducible        -/
/- factors, the monic irreducible polynomials of degree dividing n.          -/
/- Comparing degrees, q^n is the sum of d N(d) over the divisors d of n,     -/
/- where N(d) is the number of monic irreducible polynomials of degree d.    -/
/- ------------------------------------------------------------------------- -/

structure IrreducibleXPow where
  -- @@FIELDS
  FINITE_FIELD_POW_CARD_EXP : thm
  FINITE_FIELD_IRREDUCIBLE_ROOT_POW : thm
  FINITE_FIELD_IRREDUCIBLE_ROOTS : thm
  IRREDUCIBLE_DIVIDES_X_POW_SUB_X : thm
  X_POW_SUB_X_FINITE_FIELD : thm
  X_POW_SUB_X_EQ_PRODUCT_IRREDUCIBLES : thm
  FINITE_FIELD_IRREDUCIBLE_COUNT : thm
  deriving Inhabited

@[nospecialize]
def setupIrreducibleXPow [HolBase] (D : FiniteFieldsDeps) :
    ExceptT String IO IrreducibleXPow := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, SET_TAC, .. } := D
  let { ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH, CARD_EQ_0, DIVIDES_LE, DIVIDES_REFL,
        DIVIDES_REXP, EQ_TRANS, EXP_1, EXP_ADD, EXP_EQ_0, EXTENSION,
        EXTENSION_DEGREE_SIMPLE, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_MONIC_IRREDUCIBLE_ASSOCIATE, FIELD_NONTRIVIAL, FINITE_FIELD_CARD_GE_2,
        FINITE_FINITE_FIELD_EXTENSION, FINITE_POLY_DEG_LE, FINITE_RESTRICT,
        FINITE_SIMPLE_ALGEBRAIC_EXTENSION, FINITE_SUBSET, FORALL_IN_IMAGE, FUN_EQ_THM,
        GALOIS_GROUP, GALOIS_GROUP_FROBENIUS, GALOIS_GROUP_POW_RING_POW,
        GROUP_POW_EQ_ID, HAS_SIZE_IMAGE_INJ, HAS_SIZE_NUMSEG_LT, IMP_CONJ_ALT,
        INSERT_SUBSET, INTEGRAL_DOMAIN_POLY_RING,
        INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE, IN_ELIM_THM, IN_INSERT,
        IN_RING_POLYNOMIAL_CARRIER_COMPOSE, IRREDUCIBLE_IMP_POLY_DEG_NZ, I_THM,
        LEFT_IMP_EXISTS_THM, LE_EXP, LE_TRANS,
        MINIMAL_POLYNOMIAL_ASSOCIATES_IRREDUCIBLE, MONIC_ASSOCIATES_EQ, .. } := D.core1
  let { MONIC_POLY_PRODUCT, MONIC_VAR_POW_SUB_VAR, MULT_SYM, NSUM_CONST, NSUM_EQ,
        NSUM_GROUP, PID_IMP_UFD, PID_POLY_RING, POLY_DEG_MONOMORPHIC_IMAGE,
        POLY_DEG_PRODUCT_MONIC, POLY_EVAL_HOMOMORPHIC_IMAGE, POLY_EVAL_VAR_POW_SUB_VAR,
        POLY_MONOMIAL_IN_CARRIER, POLY_RING_CLAUSES, POLY_SEPARABLE_IMP_SQUAREFREE,
        POLY_SEPARABLE_VAR_POW_SUB_VAR, POLY_SPLITS_OVER_DISTINCT_ROOTS,
        POLY_VAR_POW_SUB_VAR, RING_ASSOCIATES_DIVIDES, RING_ASSOCIATES_REFL,
        RING_CARRIER_NONEMPTY, RING_CHAR_DIVIDES_ORDER,
        RING_COPRIME_DISTINCT_MONIC_IRREDUCIBLES, RING_COPRIME_PRODUCT_DIVIDES,
        RING_DIVIDES_IN_CARRIER, RING_DIVIDES_IRREDUCIBLE_ROOT,
        RING_DIVIDES_PRODUCT_SUBSET, RING_DIVIDES_TRANS, RING_ENDOMORPHISM_POW_CARD,
        RING_HOMOMORPHISM_IN_CARRIER, RING_IRREDUCIBLE_IN_CARRIER,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_POLYNOMIAL, RING_POLYNOMIAL_POW,
        RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_VAR, RING_POW, RING_POW_POW,
        RING_POW_SUBRING_GENERATED, RING_POW_ZERO, RING_PRODUCT, RING_PRODUCT_SING,
        RING_SQUAREFREE_DIVIDES, RING_SUB_EQ_0, SING_SUBSET, SUBFIELD_IMP_SUBRING_OF,
        SUBFIELD_OF_FIXPOINTS, SUBRING_GENERATED_INC_GEN, SUBRING_GENERATED_MINIMAL,
        SUBSET, WLOG_LE, algebraic_extension, algebraically_closed_field,
        field_extension, o_THM, pairwise, ring_associates, ring_endomorphism,
        ring_irreducible, .. } := D.core2
  -- @@SCOPE END

  let FINITE_FIELD_POW_CARD_EXP ← prove
   r"!(h:A->B) k l n.
        field_extension(k,l) h /\ FINITE(ring_carrier l)
        ==> ((!x. x IN ring_carrier l
                  ==> ring_pow l x (CARD(ring_carrier k) EXP n) = x) <=>
             extension_degree(k,l) h divides n)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP GALOIS_GROUP_FROBENIUS) THEN
    ABBREV_TAC (← q r"f = \x. if x IN ring_carrier l
                        then ring_pow l x (CARD(ring_carrier(k:A ring)))
                        else x:B") THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (REWRITE_TAC [← GSYM (← MATCH_MP GROUP_POW_EQ_ID th)])) THEN
    EXPAND_TAC "f" THEN REWRITE_TAC [GALOIS_GROUP_POW_RING_POW, GALOIS_GROUP] THEN
    REWRITE_TAC [FUN_EQ_THM, I_THM] THEN MESON_TAC [])

  let FINITE_FIELD_IRREDUCIBLE_ROOT_POW ← prove
   r"!(h:A->B) k l p x n.
        field_extension(k,l) h /\ FINITE(ring_carrier k) /\
        ring_irreducible(poly_ring k (:1)) p /\
        x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l
        ==> (ring_pow l x (CARD(ring_carrier k) EXP n) = x <=>
             poly_deg k p divides n)"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"p:(1->num)->A", ← q r"x:B"]
      MINIMAL_POLYNOMIAL_ASSOCIATES_IRREDUCIBLE) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"x:B"]
      FINITE_SIMPLE_ALGEBRAIC_EXTENSION) THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"x:B"]
      EXTENSION_DEGREE_SIMPLE) THEN
    ASM_SIMP_TAC [FINITE_FINITE_FIELD_EXTENSION] THEN
    ABBREV_TAC
     (← q r"K = subring_generated l (x INSERT IMAGE (h:A->B) (ring_carrier k))") THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"K:B ring", ← q r"n:num"]
      FINITE_FIELD_POW_CARD_EXP) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    EXPAND_TAC "K" THEN REWRITE_TAC [RING_POW_SUBRING_GENERATED] THEN
    EQ_TAC THEN DISCH_TAC THENL
     [MP_TAC (← ISPECL [← q r"k:A ring", ← q r"l:B ring", ← q r"h:A->B", ← q r"n:num"]
        RING_ENDOMORPHISM_POW_CARD) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN
      MP_TAC (← ISPECL
       [← q r"l:B ring", ← q r"\y:B. ring_pow l y (CARD(ring_carrier(k:A ring)) EXP n)"]
       SUBFIELD_OF_FIXPOINTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
      DISCH_THEN (MP_TAC o MATCH_MP SUBFIELD_IMP_SUBRING_OF) THEN
      DISCH_THEN (MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ_ALT]
        SUBRING_GENERATED_MINIMAL)) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"x INSERT IMAGE (h:A->B) (ring_carrier k)")) THEN
      ANTS_TAC THENL
       [REWRITE_TAC [INSERT_SUBSET, SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN
        ASM_SIMP_TAC [] THEN X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN
        MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN
        EXISTS_TAC (← q r"k:A ring") THEN ASM_REWRITE_TAC [],
        SET_TAC []],
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN
      ASM_REWRITE_TAC [IN_INSERT]])

  let FINITE_FIELD_IRREDUCIBLE_ROOTS ← prove
   r"!(h:A->B) k l p x.
        field_extension(k,l) h /\ FINITE(ring_carrier k) /\
        ring_irreducible(poly_ring k (:1)) p /\
        x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l
        ==> {y | y IN ring_carrier l /\ poly_eval l (h o p) y = ring_0 l} =
            IMAGE (\i. ring_pow l x (CARD(ring_carrier k) EXP i))
                  {i | i < poly_deg k p} /\
            {y | y IN ring_carrier l /\ poly_eval l (h o p) y = ring_0 l}
            HAS_SIZE poly_deg k p"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_IRREDUCIBLE_IN_CARRIER) THEN
    SUBGOAL_THEN (← q r"(h:A->B) o p IN ring_carrier(poly_ring l (:1))")
    ASSUME_TAC THENL
     [MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
      EXISTS_TAC (← q r"k:A ring") THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"p:(1->num)->A", ← q r"x:B"]
      FINITE_FIELD_IRREDUCIBLE_ROOT_POW) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"~(CARD(ring_carrier(k:A ring)) = 0)") ASSUME_TAC THENL
     [ASM_SIMP_TAC [CARD_EQ_0, RING_CARRIER_NONEMPTY], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!i. poly_eval l ((h:A->B) o p)
            (ring_pow l x (CARD(ring_carrier(k:A ring)) EXP i)) = ring_0 l")
    ASSUME_TAC THENL
     [X_GEN_TAC (← q r"i:num") THEN
      MP_TAC (← ISPECL [← q r"k:A ring", ← q r"l:B ring", ← q r"h:A->B", ← q r"i:num"]
        RING_ENDOMORPHISM_POW_CARD) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC [], REWRITE_TAC [ring_endomorphism]] THEN
      STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"l:B ring", ← q r"l:B ring", ← q r"x:B",
                     ← q r"\y:B. ring_pow l y (CARD(ring_carrier(k:A ring)) EXP i)",
                     ← q r"(h:A->B) o (p:(1->num)->A)"]
        POLY_EVAL_HOMOMORPHIC_IMAGE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"(\y:B. ring_pow l y (CARD(ring_carrier(k:A ring)) EXP i)) o h o p =
        (h:A->B) o (p:(1->num)->A)")
      SUBST1_TAC THENL
       [REWRITE_TAC [FUN_EQ_THM, o_THM] THEN X_GEN_TAC (← q r"m:1->num") THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        MATCH_MP_TAC POLY_MONOMIAL_IN_CARRIER THEN
        EXISTS_TAC (← q r"(:1)") THEN ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      ASM_REWRITE_TAC [RING_POW_ZERO, EXP_EQ_0] THEN
      DISCH_THEN (ACCEPT_TAC o SYM),
      ALL_TAC] THEN
    ABBREV_TAC (← q r"q = CARD(ring_carrier(k:A ring))") THEN
    ABBREV_TAC (← q r"d = poly_deg k (p:(1->num)->A)") THEN
    SUBGOAL_THEN
     (← q r"!i j. i < d /\ j < d /\
            ring_pow l x (q EXP i) = ring_pow l (x:B) (q EXP j)
            ==> i = j")
    ASSUME_TAC THENL
     [MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL [MESON_TAC [], ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [← q r"i:num", ← q r"j:num"] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o AP_TERM (← q r"\y:B. ring_pow l y (q EXP (d - j))")) THEN
      ASM_SIMP_TAC [RING_POW_POW, ← GSYM EXP_ADD] THEN
      SUBGOAL_THEN (← q r"j + (d - j) = d") SUBST1_TAC THENL
       [ASM_ARITH_TAC, ALL_TAC] THEN
      SUBGOAL_THEN (← q r"ring_pow l x (q EXP d) = (x:B)") SUBST1_TAC THENL
       [ASM_REWRITE_TAC [DIVIDES_REFL], ASM_REWRITE_TAC []] THEN
      DISCH_THEN (MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"p:(1->num)->A",
                   ← q r"IMAGE (\i. ring_pow l (x:B) (q EXP i)) {i | i < d}"]
      POLY_SPLITS_OVER_DISTINCT_ROOTS) THEN
    SUBGOAL_THEN
     (← q r"IMAGE (\i. ring_pow l (x:B) (q EXP i)) {i | i < d} HAS_SIZE d")
    ASSUME_TAC THENL
     [MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
      REWRITE_TAC [HAS_SIZE_NUMSEG_LT, IN_ELIM_THM] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [FORALL_IN_IMAGE, IN_ELIM_THM] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC [RING_POW] THEN
      ASM_MESON_TAC [ring_irreducible, POLY_RING_CLAUSES],
      ASM_SIMP_TAC []])

  let IRREDUCIBLE_DIVIDES_X_POW_SUB_X ← prove
   r"!(k:A ring) p n.
        field k /\ FINITE(ring_carrier k) /\
        ring_irreducible(poly_ring k (:1)) p
        ==> (ring_divides (poly_ring k (:1)) p
               (poly_sub k (poly_pow k (poly_var k one)
                              (CARD(ring_carrier k) EXP n))
                           (poly_var k one)) <=>
             poly_deg k p divides n)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"k:A ring") ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
    ASM_REWRITE_TAC [algebraic_extension, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"m:(A#num)ring", ← q r"f:A->A#num"] THEN STRIP_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_IRREDUCIBLE_IN_CARRIER) THEN
    SUBGOAL_THEN
     (← q r"?x. x IN ring_carrier m /\ poly_eval m ((f:A->A#num) o p) x = ring_0 m")
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM (MATCH_MP_TAC o CONJUNCT2 o
        GEN_REWRITE_RULE I [algebraically_closed_field]) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
        EXISTS_TAC (← q r"k:A ring") THEN ASM_REWRITE_TAC [],
        MP_TAC (← ISPECL [← q r"k:A ring", ← q r"m:(A#num)ring", ← q r"f:A->A#num",
                       ← q r"p:(1->num)->A"] POLY_DEG_MONOMORPHIC_IMAGE) THEN
        ANTS_TAC THENL
         [ASM_MESON_TAC [RING_POLYNOMIAL], DISCH_THEN SUBST1_TAC] THEN
        ASM_SIMP_TAC [IRREDUCIBLE_IMP_POLY_DEG_NZ]],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"f:A->A#num", ← q r"k:A ring", ← q r"m:(A#num)ring", ← q r"p:(1->num)->A",
                   ← q r"poly_sub k (poly_pow k (poly_var k one)
                       (CARD(ring_carrier k) EXP n)) (poly_var k one):
                    (1->num)->A", ← q r"x:A#num"]
      RING_DIVIDES_IRREDUCIBLE_ROOT) THEN
    ASM_SIMP_TAC [POLY_EVAL_VAR_POW_SUB_VAR] THEN ANTS_TAC THENL
     [REWRITE_TAC [← GSYM RING_POLYNOMIAL] THEN
      SIMP_TAC [RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_POW, RING_POLYNOMIAL_VAR],
      DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC [RING_SUB_EQ_0, RING_POW] THEN
    MATCH_MP_TAC FINITE_FIELD_IRREDUCIBLE_ROOT_POW THEN
    EXISTS_TAC (← q r"f:A->A#num") THEN ASM_REWRITE_TAC [])

  let X_POW_SUB_X_FINITE_FIELD ← prove
   r"!(k:A ring) n.
        field k /\ FINITE(ring_carrier k) /\ ~(n = 0)
        ==> poly_sub k (poly_pow k (poly_var k one)
                          (CARD(ring_carrier k) EXP n)) (poly_var k one) IN
            ring_carrier(poly_ring k (:1)) /\
            ~(poly_sub k (poly_pow k (poly_var k one)
                            (CARD(ring_carrier k) EXP n)) (poly_var k one) =
              poly_0 k) /\
            poly_deg k (poly_sub k (poly_pow k (poly_var k one)
                                      (CARD(ring_carrier k) EXP n))
                                   (poly_var k one)) =
            CARD(ring_carrier k) EXP n /\
            monic k (poly_sub k (poly_pow k (poly_var k one)
                                   (CARD(ring_carrier k) EXP n))
                                (poly_var k one)) /\
            poly_separable k (poly_sub k (poly_pow k (poly_var k one)
                                            (CARD(ring_carrier k) EXP n))
                                         (poly_var k one))"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"2 <= CARD(ring_carrier(k:A ring)) EXP n") ASSUME_TAC THENL
     [TRANS_TAC LE_TRANS (← q r"CARD(ring_carrier(k:A ring)) EXP 1") THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC [EXP_1, FINITE_FIELD_CARD_GE_2],
        REWRITE_TAC [LE_EXP] THEN COND_CASES_TAC THEN ASM_ARITH_TAC],
      ALL_TAC] THEN
    ASM_SIMP_TAC [POLY_VAR_POW_SUB_VAR, MONIC_VAR_POW_SUB_VAR,
                 FIELD_NONTRIVIAL] THEN
    MATCH_MP_TAC POLY_SEPARABLE_VAR_POW_SUB_VAR THEN
    MATCH_MP_TAC DIVIDES_REXP THEN ASM_SIMP_TAC [RING_CHAR_DIVIDES_ORDER])

  let X_POW_SUB_X_EQ_PRODUCT_IRREDUCIBLES ← prove
   r"!(k:A ring) n.
        field k /\ FINITE(ring_carrier k) /\ ~(n = 0)
        ==> poly_sub k (poly_pow k (poly_var k one)
                          (CARD(ring_carrier k) EXP n))
                       (poly_var k one) =
            ring_product (poly_ring k (:1))
              {p | p IN ring_carrier(poly_ring k (:1)) /\ monic k p /\
                   ring_irreducible(poly_ring k (:1)) p /\
                   poly_deg k p divides n}
              (\p. p)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"k:A ring", ← q r"n:num"] X_POW_SUB_X_FINITE_FIELD) THEN
    ASM_REWRITE_TAC [] THEN
    ABBREV_TAC
     (← q r"f = poly_sub k (poly_pow k (poly_var k one)
                       (CARD(ring_carrier k) EXP n))
                     (poly_var k one):(1->num)->A") THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP POLY_SEPARABLE_IMP_SQUAREFREE) THEN
    ABBREV_TAC
     (← q r"s = {p | p IN ring_carrier(poly_ring k (:1)) /\ monic k p /\
               ring_irreducible(poly_ring (k:A ring) (:1)) p /\
               poly_deg k p divides n}") THEN
    SUBGOAL_THEN (← q r"FINITE(s:((1->num)->A)->bool)") ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC (← q r"{p | p IN ring_carrier(poly_ring k (:1)) /\
                       poly_deg (k:A ring) p <= n}") THEN
      ASM_SIMP_TAC [FINITE_POLY_DEG_LE] THEN EXPAND_TAC "s" THEN
      REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC [DIVIDES_LE],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!p. p IN ring_carrier(poly_ring k (:1)) /\ monic k p /\
          ring_irreducible(poly_ring k (:1)) p
          ==> (p IN s <=> ring_divides (poly_ring k (:1)) p (f:(1->num)->A))")
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["s", "f"] THEN
      ASM_SIMP_TAC [IN_ELIM_THM, IRREDUCIBLE_DIVIDES_X_POW_SUB_X],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!p. p IN s
          ==> p IN ring_carrier(poly_ring k (:1)) /\ monic k p /\
              ring_irreducible(poly_ring (k:A ring) (:1)) p")
    ASSUME_TAC THENL
     [EXPAND_TAC "s" THEN SIMP_TAC [IN_ELIM_THM], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"UFD(poly_ring (k:A ring) (:1))") ASSUME_TAC THENL
     [ASM_SIMP_TAC [PID_IMP_UFD, PID_POLY_RING], ALL_TAC] THEN
    MATCH_MP_TAC MONIC_ASSOCIATES_EQ THEN EXISTS_TAC (← q r"k:A ring") THEN
    ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MONIC_POLY_PRODUCT THEN ASM_MESON_TAC [RING_POLYNOMIAL],
      REWRITE_TAC [ring_associates]] THEN
    CONJ_TAC THENL
     [MP_TAC (← ISPECL [← q r"poly_ring (k:A ring) (:1)", ← q r"f:(1->num)->A",
                     ← q r"ring_product (poly_ring (k:A ring) (:1)) s (\p. p)"]
        RING_SQUAREFREE_DIVIDES) THEN
      ASM_REWRITE_TAC [RING_PRODUCT, POLY_RING_CLAUSES] THEN
      DISCH_THEN SUBST1_TAC THEN X_GEN_TAC (← q r"g:(1->num)->A") THEN STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"k:A ring", ← q r"g:(1->num)->A"]
        FIELD_MONIC_IRREDUCIBLE_ASSOCIATE) THEN
      ASM_SIMP_TAC [INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE,
                   INTEGRAL_DOMAIN_POLY_RING, FIELD_IMP_INTEGRAL_DOMAIN] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"g':(1->num)->A") STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC RING_DIVIDES_TRANS THEN EXISTS_TAC (← q r"g':(1->num)->A") THEN
      CONJ_TAC THENL [ASM_MESON_TAC [ring_associates], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"(g':(1->num)->A) IN s") ASSUME_TAC THENL
       [FIRST_X_ASSUM (fun th =>
          wPart (fun w => .ok w) (fun t => do lhand (← rand t)) th) THEN
        ASM_REWRITE_TAC [← GSYM RING_POLYNOMIAL] THEN DISCH_THEN SUBST1_TAC THEN
        ASM_MESON_TAC [RING_ASSOCIATES_DIVIDES, RING_ASSOCIATES_REFL,
                      RING_DIVIDES_IN_CARRIER],
        ALL_TAC] THEN
      MP_TAC (← ISPECL [← q r"poly_ring (k:A ring) (:1)", ← q r"\p:(1->num)->A. p",
                     ← q r"{g':(1->num)->A}", ← q r"s:((1->num)->A)->bool"]
        RING_DIVIDES_PRODUCT_SUBSET) THEN
      ASM_REWRITE_TAC [SING_SUBSET, RING_PRODUCT_SING] THEN
      ASM_MESON_TAC [RING_POLYNOMIAL],
      MP_TAC (← ISPECL [← q r"poly_ring (k:A ring) (:1)", ← q r"\p:(1->num)->A. p",
                     ← q r"s:((1->num)->A)->bool", ← q r"f:(1->num)->A"]
        RING_COPRIME_PRODUCT_DIVIDES) THEN
      ASM_SIMP_TAC [] THEN ANTS_TAC THENL
       [REWRITE_TAC [pairwise] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC RING_COPRIME_DISTINCT_MONIC_IRREDUCIBLES THEN
        ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN],
        DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC []]])

  let FINITE_FIELD_IRREDUCIBLE_COUNT ← prove
   r"!(k:A ring) n.
        field k /\ FINITE(ring_carrier k) /\ ~(n = 0)
        ==> nsum {d | d divides n}
              (\d. d * CARD {p | p IN ring_carrier(poly_ring k (:1)) /\
                                 monic k p /\
                                 ring_irreducible(poly_ring k (:1)) p /\
                                 poly_deg k p = d}) =
            CARD(ring_carrier k) EXP n"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"k:A ring", ← q r"n:num"] X_POW_SUB_X_FINITE_FIELD) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_SIMP_TAC [X_POW_SUB_X_EQ_PRODUCT_IRREDUCIBLES] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    ABBREV_TAC
     (← q r"s = {p | p IN ring_carrier(poly_ring k (:1)) /\ monic k p /\
               ring_irreducible(poly_ring (k:A ring) (:1)) p /\
               poly_deg k p divides n}") THEN
    SUBGOAL_THEN (← q r"FINITE(s:((1->num)->A)->bool)") ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC (← q r"{p | p IN ring_carrier(poly_ring k (:1)) /\
                       poly_deg (k:A ring) p <= n}") THEN
      ASM_SIMP_TAC [FINITE_POLY_DEG_LE] THEN EXPAND_TAC "s" THEN
      REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC [DIVIDES_LE],
      ALL_TAC] THEN
    wPart rand (fun t => do lhand (← rand t)) POLY_DEG_PRODUCT_MONIC THEN
    ANTS_TAC THENL
     [EXPAND_TAC "s" THEN ASM_SIMP_TAC [IN_ELIM_THM, RING_POLYNOMIAL],
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC []] THEN
    MP_TAC (← ISPECL [← q r"\p:(1->num)->A. poly_deg k p",
                   ← q r"\p:(1->num)->A. poly_deg k p",
                   ← q r"s:((1->num)->A)->bool", ← q r"{d:num | d divides n}"]
      NSUM_GROUP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN EXPAND_TAC "s" THEN
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN MESON_TAC [],
      DISCH_THEN (SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC (← q r"d:num") THEN
    REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     (← q r"{p | p IN s /\ poly_deg k p = d} =
      {p | p IN ring_carrier(poly_ring k (:1)) /\ monic k p /\
           ring_irreducible(poly_ring (k:A ring) (:1)) p /\ poly_deg k p = d}")
    (SUBST1_TAC o SYM) THENL
     [EXPAND_TAC "s" THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
      ASM_MESON_TAC [],
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"nsum {p | p IN s /\ poly_deg (k:A ring) p = d}
                      (\p:(1->num)->A. d)") THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC [NSUM_CONST, FINITE_RESTRICT, MULT_SYM],
      MATCH_MP_TAC NSUM_EQ THEN SIMP_TAC [IN_ELIM_THM]])

  -- @@RETURN BEGIN
  return { FINITE_FIELD_POW_CARD_EXP, FINITE_FIELD_IRREDUCIBLE_ROOT_POW,
           FINITE_FIELD_IRREDUCIBLE_ROOTS, IRREDUCIBLE_DIVIDES_X_POW_SUB_X,
           X_POW_SUB_X_FINITE_FIELD, X_POW_SUB_X_EQ_PRODUCT_IRREDUCIBLES,
           FINITE_FIELD_IRREDUCIBLE_COUNT }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Extensions and irreducible polynomials of every degree. For n > 0 the     -/
/- roots of X^(q^n) - X in a splitting extension l form a subfield           -/
/- containing the image of k, so they are all of l; hence l has q^n elements -/
/- and degree n over k. The minimal polynomial of an element generating l    -/
/- over k is a monic irreducible polynomial of degree n.                     -/
/- ------------------------------------------------------------------------- -/

structure EveryDegree where
  -- @@FIELDS
  FINITE_FIELD_EXTENSION_EXISTS : thm
  FINITE_FIELD_IRREDUCIBLE_EXISTS : thm
  deriving Inhabited

@[nospecialize]
def setupEveryDegree [HolBase] (D : FiniteFieldsDeps) (BIrreducibleXPow : IrreducibleXPow) :
    ExceptT String IO EveryDegree := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, SET_RULE, .. } := D
  let { CARD_EXTENSION_DEGREE, CARRIER_SUBFIELD_GENERATED_SUBFIELD, EQ_EXP, EXTENSION,
        EXTENSION_DEGREE_SIMPLE, FINITE_FIELD_CARD_GE_2,
        FINITE_FIELD_PRIMITIVE_ELEMENT, FINITE_FINITE_FIELD_EXTENSION,
        FINITE_IMP_ALGEBRAIC_EXTENSION, FORALL_IN_IMAGE, IN_ELIM_THM,
        LEFT_IMP_EXISTS_THM, MINIMAL_POLYNOMIAL, .. } := D.core1
  let { MONO_EXISTS, POLY_EVAL_VAR_POW_SUB_VAR, POLY_ROOT_BOUND_EXTENSION,
        POLY_SPLITS_OVER_SEPARABLE_ROOT_COUNT, RING_ENDOMORPHISM_POW_CARD,
        RING_HOMOMORPHISM_IN_CARRIER, RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_POW,
        RING_SUB_EQ_0, SPLITTING_EXTENSION_EXISTS_BIGENOUGH, SUBFIELD_OF_FIXPOINTS,
        SUBSET, algebraic_extension, field_extension, splitting_extension, .. } := D.core2
  let { X_POW_SUB_X_FINITE_FIELD, .. } := BIrreducibleXPow
  -- @@SCOPE END

  let FINITE_FIELD_EXTENSION_EXISTS ← prove
   r"!(k:A ring) n.
        field k /\ FINITE(ring_carrier k) /\ ~(n = 0)
        ==> ?l (h:A->A#num).
                field_extension(k,l) h /\ FINITE(ring_carrier l) /\
                extension_degree(k,l) h = n"
   (← do
    let s1 ← SET_RULE (← q r"(s:A#num->bool) SUBSET t ==> s UNION t = t")
    pure (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"2 <= CARD(ring_carrier(k:A ring))") ASSUME_TAC THENL
     [ASM_SIMP_TAC [FINITE_FIELD_CARD_GE_2], ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"k:A ring", ← q r"n:num"] X_POW_SUB_X_FINITE_FIELD) THEN
    ASM_REWRITE_TAC [] THEN
    ABBREV_TAC
     (← q r"f = poly_sub k (poly_pow k (poly_var k one)
                       (CARD(ring_carrier k) EXP n))
                     (poly_var k one):(1->num)->A") THEN
    STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"k:A ring", ← q r"f:(1->num)->A"]
      SPLITTING_EXTENSION_EXISTS_BIGENOUGH) THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"l:(A#num)ring") THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"h:A->A#num") THEN
    REWRITE_TAC [splitting_extension] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
    SUBGOAL_THEN
     (← q r"{x | x IN ring_carrier l /\
           poly_eval l ((h:A->A#num) o f) x = ring_0 l} =
      {x | x IN ring_carrier l /\
           ring_pow l x (CARD(ring_carrier(k:A ring)) EXP n) = x}")
    ASSUME_TAC THENL
     [EXPAND_TAC "f" THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
      X_GEN_TAC (← q r"x:A#num") THEN
      ASM_CASES_TAC (← q r"(x:A#num) IN ring_carrier l") THEN
      ASM_SIMP_TAC [POLY_EVAL_VAR_POW_SUB_VAR, RING_SUB_EQ_0, RING_POW],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"ring_carrier l =
      {x | x IN ring_carrier l /\
           ring_pow l x (CARD(ring_carrier(k:A ring)) EXP n) = x:A#num}")
    ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q r"k:A ring", ← q r"l:(A#num)ring", ← q r"h:A->A#num", ← q r"n:num"]
        RING_ENDOMORPHISM_POW_CARD) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN
      MP_TAC (← ISPECL
       [← q r"l:(A#num)ring",
        ← q r"\y:A#num. ring_pow l y (CARD(ring_carrier(k:A ring)) EXP n)"]
       SUBFIELD_OF_FIXPOINTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC [], REWRITE_TAC []] THEN
      DISCH_THEN (SUBST1_TAC o SYM o MATCH_MP
        CARRIER_SUBFIELD_GENERATED_SUBFIELD) THEN
      AP_TERM_TAC THEN FIRST_X_ASSUM (fun th => tactic_of do
        let c ← q r"l:(A#num)ring"
        if !((← liftExcept (rand (concl th))) == c) then throw "check"
        pure (GEN_REWRITE_TAC LAND_CONV [← SYM th])) THEN
      AP_TERM_TAC THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC s1 THEN
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN
      ASM_SIMP_TAC [] THEN X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN
      MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN
      EXISTS_TAC (← q r"k:A ring") THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"h:A->A#num", ← q r"k:A ring", ← q r"l:(A#num)ring", ← q r"f:(1->num)->A"]
      POLY_ROOT_BOUND_EXTENSION) THEN
    MP_TAC (← ISPECL [← q r"h:A->A#num", ← q r"k:A ring", ← q r"l:(A#num)ring", ← q r"f:(1->num)->A"]
      POLY_SPLITS_OVER_SEPARABLE_ROOT_COUNT) THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (fun th => tactic_of do
      let c ← q r"ring_carrier(l:(A#num)ring)"
      let ok := is_eq (concl th) &&
        (match lhs (concl th) with | .ok t => t == c | .error _ => false)
      if !ok then throw "check"
      pure ((SUBST1_TAC o SYM) th)) THEN
    REPEAT DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    MP_TAC (← ISPECL [← q r"h:A->A#num", ← q r"k:A ring", ← q r"l:(A#num)ring"]
      CARD_EXTENSION_DEGREE) THEN
    ASM_REWRITE_TAC [EQ_EXP] THEN ASM_ARITH_TAC))

  let FINITE_FIELD_IRREDUCIBLE_EXISTS ← prove
   r"!(k:A ring) n.
        field k /\ FINITE(ring_carrier k) /\ ~(n = 0)
        ==> ?p. p IN ring_carrier(poly_ring k (:1)) /\ monic k p /\
                ring_irreducible(poly_ring k (:1)) p /\ poly_deg k p = n"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"k:A ring", ← q r"n:num"] FINITE_FIELD_EXTENSION_EXISTS) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"l:(A#num)ring", ← q r"h:A->A#num"] THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"h:A->A#num", ← q r"k:A ring", ← q r"l:(A#num)ring"]
      FINITE_FIELD_PRIMITIVE_ELEMENT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [field_extension], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"a:A#num") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"algebraic_over (k,l) (h:A->A#num) a") ASSUME_TAC THENL
     [ASM_MESON_TAC [FINITE_IMP_ALGEBRAIC_EXTENSION, algebraic_extension,
                    FINITE_FINITE_FIELD_EXTENSION],
      ALL_TAC] THEN
    EXISTS_TAC (← q r"minimal_polynomial (k,l) (h:A->A#num) a") THEN
    ASM_SIMP_TAC [MINIMAL_POLYNOMIAL] THEN
    MP_TAC (← ISPECL [← q r"h:A->A#num", ← q r"k:A ring", ← q r"l:(A#num)ring", ← q r"a:A#num"]
      EXTENSION_DEGREE_SIMPLE) THEN
    ASM_REWRITE_TAC [] THEN ARITH_TAC)

  -- @@RETURN BEGIN
  return { FINITE_FIELD_EXTENSION_EXISTS, FINITE_FIELD_IRREDUCIBLE_EXISTS }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Finite fields inside an algebraically closed or a normal extension: the   -/
/- "layers" {x | x^(q^n) = x} and the Galois group.                          -/
/- ------------------------------------------------------------------------- -/

structure Layers where
  -- @@FIELDS
  FINITE_FIELD_POW_ITERATE : thm
  FINITE_FIELD_ALGEBRAIC_CLOSURE_LAYER : thm
  FINITE_FIELD_IRREDUCIBLE_ROOT_EXISTS : thm
  FINITE_FIELD_NORMAL_IMP_GALOIS : thm
  FINITE_GALOIS_SUBFIELDS_FINITE_FIELD : thm
  FINITE_FIELD_LAYERS_COVER : thm
  FINITE_FIELD_LAYER_POW : thm
  ABELIAN_GALOIS_GROUP_FINITE_FIELD : thm
  GALOIS_GROUP_FINITE_FIELD_EXPONENT : thm
  deriving Inhabited

@[nospecialize]
def setupLayers [HolBase] (D : FiniteFieldsDeps) (BBasicFacts : BasicFacts) (BIrreducibleXPow : IrreducibleXPow) :
    ExceptT String IO Layers := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, SET_TAC, TAUT, .. } := D
  let { ALGEBRAICALLY_CLOSED_FIELD_FINITE_SUBFIELD, ALGEBRAIC_IMP_FIELD_EXTENSION,
        CARD_EXTENSION_DEGREE, CARRIER_SUBFIELD_GENERATED_SUBFIELD,
        CARRIER_SUBGROUP_GENERATED_BY_SING, CONG_IMP_EQ,
        CYCLIC_GALOIS_GROUP_FINITE_FIELD, CYCLIC_IMP_ABELIAN_GROUP, DIVIDES_REFL,
        DIVISION, EQ_EXP, EXISTS_UNIQUE_THM, EXP, EXP_ADD, EXP_EXP,
        FIELD_EXTENSION_INTO_SUBFIELD_GENERATED, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_IMP_NONTRIVIAL_RING, FIELD_SUBFIELD_GENERATED, FINITE_FIELD_CARD_GE_2,
        FINITE_FIELD_GALOIS_EXTENSION, FINITE_FIELD_IMP_PERFECT,
        FINITE_FINITE_FIELD_EXTENSION, FINITE_GALOIS_SUBFIELDS_ELEMENT,
        FINITE_GALOIS_SUBFIELDS_FINITE, FINITE_INTEGRAL_DOMAIN_CHAR,
        FINITE_RING_MONOMORPHIC_PREIMAGE, FINITE_SUBFIELD_EXPLICIT, FORALL_IN_IMAGE,
        FUN_EQ_THM, GALOIS_GROUP, GALOIS_GROUP_FINITE_FIELD, GALOIS_GROUP_FROBENIUS,
        GALOIS_GROUP_PERMUTES, GALOIS_GROUP_POW_RING_POW,
        GALOIS_GROUP_RESTRICTION_NORMAL, GALOIS_IMP_NORMAL_EXTENSION,
        GROUP_HOMOMORPHISM, GROUP_NPOW, GROUP_POW_EQ, GROUP_ZPOW_REM_ELEMENT_ORDER,
        HAS_SIZE, INT_LT_REM, INT_OF_NUM_EQ, INT_OF_NUM_LT, INT_OF_NUM_OF_INT,
        INT_REM_POS, IN_ELIM_THM, IN_FINITE_GALOIS_SUBFIELDS, IN_UNIV,
        IRREDUCIBLE_IMP_POLY_DEG_NZ, LE_1, .. } := D.core1
  let { MULT_CLAUSES, MULT_EQ_0, MULT_SYM, NORMAL_IMP_ALGEBRAIC_EXTENSION,
        PERFECT_FIELD_IMP_SEPARABLE_EXTENSION, POLY_DEG_MONOMORPHIC_IMAGE,
        POLY_EQ_0_MONOMORPHIC_IMAGE, POLY_EVAL_VAR_POW_SUB_VAR, POLY_SPLITS_DIVISOR,
        POLY_SPLITS_HAS_ROOT, POLY_SPLITS_OVER_DISTINCT_ROOTS,
        RING_CHAR_MONOMORPHIC_IMAGE, RING_DIVIDES_HOMOMORPHIC_IMAGE,
        RING_HOMOMORPHISM_IN_CARRIER, RING_HOMOMORPHISM_POLY_RINGS,
        RING_HOMOMORPHISM_POW, RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_POLYNOMIAL,
        RING_POW, RING_POW_1, RING_POW_POW, RING_POW_SUBFIELD_GENERATED, RING_SUB_EQ_0,
        SUBSET, TRIVIAL_RING_HAS_SIZE_1, abelian_group, field_extension,
        galois_extension, group_homomorphism, o_THM, permutes, poly_splits_over, .. } := D.core2
  let { FINITE_FIELD_CARD_CHAR_POWER, FINITE_FIELD_ELEMENT_POW, .. } := BBasicFacts
  let { FINITE_FIELD_POW_CARD_EXP, IRREDUCIBLE_DIVIDES_X_POW_SUB_X,
        X_POW_SUB_X_FINITE_FIELD, .. } := BIrreducibleXPow
  -- @@SCOPE END

  let FINITE_FIELD_POW_ITERATE ← prove
   r"!(k:A ring) x n.
        field k /\ FINITE(ring_carrier k) /\ x IN ring_carrier k
        ==> ring_pow k x (CARD(ring_carrier k) EXP n) = x"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN SPEC_TAC (← q r"n:num", ← q r"n:num") THEN
    INDUCT_TAC THEN ASM_SIMP_TAC [EXP, RING_POW_1] THEN
    ASM_SIMP_TAC [← GSYM RING_POW_POW, FINITE_FIELD_ELEMENT_POW])

  let FINITE_FIELD_ALGEBRAIC_CLOSURE_LAYER ← prove
   r"!(h:A->B) k l n.
        field_extension(k,l) h /\ FINITE(ring_carrier k) /\
        algebraically_closed_field l /\ ~(n = 0)
        ==> {x | x IN ring_carrier l /\
                 ring_pow l x (CARD(ring_carrier k) EXP n) = x} subfield_of l /\
            IMAGE h (ring_carrier k) SUBSET
            {x | x IN ring_carrier l /\
                 ring_pow l x (CARD(ring_carrier k) EXP n) = x} /\
            {x | x IN ring_carrier l /\
                 ring_pow l x (CARD(ring_carrier k) EXP n) = x}
            HAS_SIZE CARD(ring_carrier k) EXP n"
   (← do
    let t1 ← TAUT (← q r"(p /\ r) /\ q ==> p /\ q /\ r")
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    SUBGOAL_THEN (← q r"ring_homomorphism(k:A ring,l:B ring) h") ASSUME_TAC THENL
     [ASM_SIMP_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"ring_char(l:B ring) = ring_char(k:A ring) /\ prime(ring_char k)")
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_CHAR_MONOMORPHIC_IMAGE THEN
        EXISTS_TAC (← q r"h:A->B") THEN ASM_REWRITE_TAC [],
        MATCH_MP_TAC FINITE_INTEGRAL_DOMAIN_CHAR THEN
        ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN]],
      ALL_TAC] THEN
    MATCH_MP_TAC t1 THEN CONJ_TAC THENL
     [MP_TAC (← ISPEC (← q r"k:A ring") FINITE_FIELD_CARD_CHAR_POWER) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"e:num") STRIP_ASSUME_TAC) THEN
      MP_TAC (← ISPECL [← q r"l:B ring", ← q r"e * n:num"]
        ALGEBRAICALLY_CLOSED_FIELD_FINITE_SUBFIELD) THEN
      ASM_REWRITE_TAC [MULT_EQ_0, EXP_EXP],
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN
      X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN
      CONJ_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN
      FIRST_ASSUM (fun th => tactic_of do
        pure (ASM_SIMP_TAC [← GSYM (← MATCH_MP RING_HOMOMORPHISM_POW th)])) THEN
      AP_TERM_TAC THEN MATCH_MP_TAC FINITE_FIELD_POW_ITERATE THEN
      ASM_REWRITE_TAC []]))

  /- An irreducible p over a finite field k whose degree divides [l:k] has a   -/
  /- root in l (FINITE_FIELD_IRREDUCIBLE_ROOT_EXISTS): in an algebraic closure -/
  /- of l a root b of p satisfies b^(q^d) = b, and the q^d elements of the     -/
  /- image of l are all the solutions of x^(q^d) = x there                     -/
  /- (FINITE_FIELD_ALGEBRAIC_CLOSURE_LAYER).                                   -/
  let FINITE_FIELD_IRREDUCIBLE_ROOT_EXISTS ← prove
   r"!(k:A ring) (l:B ring) h p.
        field_extension(k,l) h /\ FINITE(ring_carrier l) /\
        p IN ring_carrier(poly_ring k (:1)) /\
        ring_irreducible (poly_ring k (:1)) p /\
        poly_deg k p divides extension_degree(k,l) h
        ==> ?x. x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
    SUBGOAL_THEN (← q r"FINITE(ring_carrier(k:A ring))") ASSUME_TAC THENL
     [ASM_MESON_TAC [FINITE_RING_MONOMORPHIC_PREIMAGE], ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring"] CARD_EXTENSION_DEGREE) THEN
    ASM_REWRITE_TAC [] THEN
    ABBREV_TAC (← q r"m = extension_degree(k,l) (h:A->B)") THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"~(m = 0)") ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      MP_TAC (← ISPEC (← q r"l:B ring") FINITE_FIELD_CARD_GE_2) THEN
      ASM_REWRITE_TAC [EXP] THEN ARITH_TAC,
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"k:A ring", ← q r"m:num"] X_POW_SUB_X_FINITE_FIELD) THEN
    ASM_REWRITE_TAC [] THEN
    ABBREV_TAC
     (← q r"P = poly_sub k (poly_pow k (poly_var k one) (CARD(ring_carrier k) EXP m))
                     (poly_var k one):(1->num)->A") THEN
    STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"P:(1->num)->A",
                   ← q r"ring_carrier(l:B ring)"]
      POLY_SPLITS_OVER_DISTINCT_ROOTS) THEN
    ASM_REWRITE_TAC [HAS_SIZE, poly_splits_over] THEN ANTS_TAC THENL
     [X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
      EXPAND_TAC "P" THEN
      ASM_SIMP_TAC [POLY_EVAL_VAR_POW_SUB_VAR, RING_SUB_EQ_0, RING_POW] THEN
      MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"m:num"]
        FINITE_FIELD_POW_CARD_EXP) THEN
      ASM_REWRITE_TAC [DIVIDES_REFL] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"x:B")) THEN ASM_REWRITE_TAC [],
      STRIP_TAC] THEN
    MP_TAC (← ISPECL [← q r"k:A ring", ← q r"p:(1->num)->A", ← q r"m:num"]
      IRREDUCIBLE_DIVIDES_X_POW_SUB_X) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"poly_ring (k:A ring) (:1)", ← q r"poly_ring (l:B ring) (:1)",
                   ← q r"\q:(1->num)->A. (h:A->B) o q",
                   ← q r"p:(1->num)->A", ← q r"P:(1->num)->A"]
      RING_DIVIDES_HOMOMORPHIC_IMAGE) THEN
    ASM_SIMP_TAC [RING_HOMOMORPHISM_POLY_RINGS] THEN DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"l:B ring", ← q r"(h:A->B) o (P:(1->num)->A)",
                   ← q r"(h:A->B) o (p:(1->num)->A)"] POLY_SPLITS_DIVISOR) THEN
    ASM_SIMP_TAC [POLY_EQ_0_MONOMORPHIC_IMAGE, RING_POLYNOMIAL] THEN
    DISCH_TAC THEN MATCH_MP_TAC POLY_SPLITS_HAS_ROOT THEN
    ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, POLY_DEG_MONOMORPHIC_IMAGE,
                 RING_POLYNOMIAL, IRREDUCIBLE_IMP_POLY_DEG_NZ] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC [POLY_EQ_0_MONOMORPHIC_IMAGE, RING_POLYNOMIAL],
      ASM_MESON_TAC [POLY_DEG_MONOMORPHIC_IMAGE, RING_POLYNOMIAL,
                    IRREDUCIBLE_IMP_POLY_DEG_NZ]])

  let FINITE_FIELD_NORMAL_IMP_GALOIS ← prove
   r"!(h:A->B) k l.
        FINITE(ring_carrier k) /\ normal_extension(k,l) h
        ==> galois_extension(k,l) h"
   (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [galois_extension] THEN
    MATCH_MP_TAC PERFECT_FIELD_IMP_SEPARABLE_EXTENSION THEN
    ASM_SIMP_TAC [NORMAL_IMP_ALGEBRAIC_EXTENSION] THEN
    MATCH_MP_TAC FINITE_FIELD_IMP_PERFECT THEN
    ASM_MESON_TAC [NORMAL_IMP_ALGEBRAIC_EXTENSION,
                  ALGEBRAIC_IMP_FIELD_EXTENSION, field_extension])

  let FINITE_GALOIS_SUBFIELDS_FINITE_FIELD ← prove
   r"!(h:A->B) k l e.
        FINITE(ring_carrier k) /\ field l /\
        e IN finite_galois_subfields(k,l) h
        ==> FINITE e /\
            ~(extension_degree(k,subfield_generated l e) h = 0) /\
            e = {x | x IN ring_carrier l /\
                     ring_pow l x
                      (CARD(ring_carrier k) EXP
                       extension_degree(k,subfield_generated l e) h) = x}"
   (REWRITE_TAC [IN_FINITE_GALOIS_SUBFIELDS] THEN REPEAT GEN_TAC THEN
    STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"subfield_generated l (e:B->bool)"]
                  FINITE_FINITE_FIELD_EXTENSION) THEN
    ASM_SIMP_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"subfield_generated l (e:B->bool)"]
                  CARD_EXTENSION_DEGREE) THEN
    ASM_SIMP_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC (← q r"CARD(e:B->bool) =
        CARD(ring_carrier(k:A ring)) EXP
        extension_degree(k,subfield_generated l e) (h:A->B)") THEN
      ASM_REWRITE_TAC [EXP] THEN DISCH_TAC THEN
      MP_TAC (← ISPEC (← q r"subfield_generated l (e:B->bool)")
                   FIELD_IMP_NONTRIVIAL_RING) THEN
      ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED] THEN
      ASM_SIMP_TAC [TRIVIAL_RING_HAS_SIZE_1, CARRIER_SUBFIELD_GENERATED_SUBFIELD,
                   HAS_SIZE],
      MP_TAC (← ISPECL [← q r"l:B ring", ← q r"e:B->bool"] FINITE_SUBFIELD_EXPLICIT) THEN
      ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN]])

  let FINITE_FIELD_LAYERS_COVER ← prove
   r"!(h:A->B) k l s.
        FINITE(ring_carrier k) /\ normal_extension(k,l) h /\
        FINITE s /\ s SUBSET ring_carrier l
        ==> ?n. ~(n = 0) /\
                s SUBSET {x | x IN ring_carrier l /\
                              ring_pow l x (CARD(ring_carrier k) EXP n) = x}"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"s:B->bool"]
                  FINITE_GALOIS_SUBFIELDS_FINITE) THEN
    ASM_SIMP_TAC [FINITE_FIELD_NORMAL_IMP_GALOIS] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"e:B->bool") STRIP_ASSUME_TAC) THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"e:B->bool"]
                  FINITE_GALOIS_SUBFIELDS_FINITE_FIELD) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC [NORMAL_IMP_ALGEBRAIC_EXTENSION,
                    ALGEBRAIC_IMP_FIELD_EXTENSION, field_extension],
      STRIP_TAC] THEN
    EXISTS_TAC (← q r"extension_degree(k,subfield_generated l e) (h:A->B)") THEN
    ASM SET_TAC [])

  let FINITE_FIELD_LAYER_POW ← prove
   r"!(l:B ring) q n x.
        x IN ring_carrier l /\ ring_pow l x (q EXP n) = x
        ==> (!a. ring_pow l x (q EXP (a * n)) = x) /\
            (!j. ~(n = 0) ==> ring_pow l x (q EXP j) =
                              ring_pow l x (q EXP (j MOD n))) /\
            (!m. ring_pow l (ring_pow l x m) (q EXP n) = ring_pow l x m)"
   (← do
    let t1 ← TAUT (← q r"p /\ (p ==> q) /\ r ==> p /\ q /\ r")
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC t1 THEN
    REPEAT CONJ_TAC THENL
     [INDUCT_TAC THEN ASM_SIMP_TAC [MULT_CLAUSES, EXP, RING_POW_1] THEN
      ASM_SIMP_TAC [EXP_ADD, ← GSYM RING_POW_POW],
      DISCH_TAC THEN X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN
      MP_TAC (← SPECL [← q r"j:num", ← q r"n:num"] DIVISION) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (fun th => tactic_of do
        pure (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
          [← CONJUNCT1 th])) THEN
      ASM_SIMP_TAC [EXP_ADD, ← GSYM RING_POW_POW],
      GEN_TAC THEN ASM_SIMP_TAC [RING_POW_POW] THEN
      ONCE_REWRITE_TAC [MULT_SYM] THEN ASM_SIMP_TAC [← GSYM RING_POW_POW]]))

  let ABELIAN_GALOIS_GROUP_FINITE_FIELD ← prove
   r"!(h:A->B) k l.
        FINITE(ring_carrier k) /\ normal_extension(k,l) h
        ==> abelian_group(galois_group(k,l) h)"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"field_extension(k:A ring,l:B ring) h") ASSUME_TAC THENL
     [ASM_MESON_TAC [NORMAL_IMP_ALGEBRAIC_EXTENSION,
                    ALGEBRAIC_IMP_FIELD_EXTENSION],
      ALL_TAC] THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    REWRITE_TAC [abelian_group, ← CONJUNCT2 (← CONJUNCT2 (← CONJUNCT2 GALOIS_GROUP))]
    THEN MAP_EVERY X_GEN_TAC [← q r"f:B->B", ← q r"g:B->B"] THEN STRIP_TAC THEN
    REWRITE_TAC [FUN_EQ_THM, o_THM] THEN X_GEN_TAC (← q r"x:B") THEN
    ASM_CASES_TAC (← q r"(x:B) IN ring_carrier l") THENL
     [ALL_TAC,
      MP_TAC (← ISPECL [← q r"h:A->B", ← q r"g:B->B", ← q r"k:A ring", ← q r"l:B ring"]
                    GALOIS_GROUP_PERMUTES) THEN
      MP_TAC (← ISPECL [← q r"h:A->B", ← q r"f:B->B", ← q r"k:A ring", ← q r"l:B ring"]
                    GALOIS_GROUP_PERMUTES) THEN
      ASM_REWRITE_TAC [permutes] THEN
      REPEAT (DISCH_THEN (MP_TAC o SPEC (← q r"x:B") o CONJUNCT1) THEN
             ASM_REWRITE_TAC [] THEN DISCH_TAC) THEN
      ASM_REWRITE_TAC []] THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"x:B"]
                  FINITE_GALOIS_SUBFIELDS_ELEMENT) THEN
    ASM_SIMP_TAC [FINITE_FIELD_NORMAL_IMP_GALOIS] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"e:B->bool") STRIP_ASSUME_TAC) THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"e:B->bool"]
                  FINITE_GALOIS_SUBFIELDS_FINITE_FIELD) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o
      GEN_REWRITE_RULE I [IN_FINITE_GALOIS_SUBFIELDS]) THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"e:B->bool"]
                  GALOIS_GROUP_RESTRICTION_NORMAL) THEN
    ASM_SIMP_TAC [GALOIS_IMP_NORMAL_EXTENSION] THEN
    DISCH_THEN (MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    REWRITE_TAC [GROUP_HOMOMORPHISM, SUBSET, FORALL_IN_IMAGE] THEN
    REWRITE_TAC [← CONJUNCT2 (← CONJUNCT2 (← CONJUNCT2 GALOIS_GROUP))] THEN
    STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"subfield_generated l (e:B->bool)"]
                  CYCLIC_GALOIS_GROUP_FINITE_FIELD) THEN
    ASM_SIMP_TAC [FIELD_EXTENSION_INTO_SUBFIELD_GENERATED,
                 CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
    DISCH_THEN (MP_TAC o MATCH_MP CYCLIC_IMP_ABELIAN_GROUP) THEN
    REWRITE_TAC [abelian_group, ← CONJUNCT2 (← CONJUNCT2 (← CONJUNCT2 GALOIS_GROUP))]
    THEN DISCH_THEN (MP_TAC o SPECL
     [← q r"\x. if x IN e then (f:B->B) x else x",
      ← q r"\x. if x IN e then (g:B->B) x else x"]) THEN
    ASM_SIMP_TAC [] THEN
    FIRST_X_ASSUM (fun th => tactic_of do
      pure (MP_TAC (← SPECL [← q r"f:B->B", ← q r"g:B->B"] th) THEN
            MP_TAC (← SPECL [← q r"g:B->B", ← q r"f:B->B"] th))) THEN
    ASM_REWRITE_TAC [] THEN
    REPLICATE_TAC 2 (DISCH_THEN (SUBST1_TAC o SYM)) THEN
    DISCH_THEN (MP_TAC o flip AP_THM (← q r"x:B")) THEN ASM_REWRITE_TAC [o_THM])

  let GALOIS_GROUP_FINITE_FIELD_EXPONENT ← prove
   r"!(h:A->B) k l n f.
        FINITE(ring_carrier k) /\ field_extension(k,l) h /\
        algebraically_closed_field l /\ ~(n = 0) /\
        f IN group_carrier(galois_group(k,l) h)
        ==> ?!j. j < n /\
                 !x. x IN ring_carrier l /\
                     ring_pow l x (CARD(ring_carrier k) EXP n) = x
                     ==> f x = ring_pow l x (CARD(ring_carrier k) EXP j)"
   (← do
    let a1 ← ARITH_RULE (← q r"2 <= q:num ==> ~(q = 0) /\ ~(q = 1)")
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"n:num"]
                  FINITE_FIELD_ALGEBRAIC_CLOSURE_LAYER) THEN
    ASM_REWRITE_TAC [] THEN
    ABBREV_TAC
     (← q r"e = {x | x IN ring_carrier l /\
               ring_pow l x (CARD(ring_carrier(k:A ring)) EXP n) = (x:B)}") THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"!x:B. x IN e <=>
            x IN ring_carrier l /\
            ring_pow l x (CARD(ring_carrier(k:A ring)) EXP n) = x")
    (fun th => tactic_of do pure (REWRITE_TAC [← GSYM th])) THENL
     [EXPAND_TAC "e" THEN REWRITE_TAC [IN_ELIM_THM], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"field_extension(k,subfield_generated l e) (h:A->B) /\
      FINITE(ring_carrier(subfield_generated l e))")
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC [FIELD_EXTENSION_INTO_SUBFIELD_GENERATED,
                   CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
      ASM_MESON_TAC [HAS_SIZE],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"extension_degree(k,subfield_generated l e) (h:A->B) = n")
    ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"subfield_generated l (e:B->bool)"]
                    CARD_EXTENSION_DEGREE) THEN
      ASM_SIMP_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [HAS_SIZE]) THEN ASM_REWRITE_TAC [] THEN
      MP_TAC (← ISPEC (← q r"k:A ring") FINITE_FIELD_CARD_GE_2) THEN
      ANTS_TAC THENL [ASM_MESON_TAC [field_extension], ALL_TAC] THEN
      SIMP_TAC [EQ_EXP, a1] THEN
      MESON_TAC [],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"e:B->bool"]
                  GALOIS_GROUP_RESTRICTION_NORMAL) THEN
    ASM_SIMP_TAC [GALOIS_IMP_NORMAL_EXTENSION, FINITE_FIELD_GALOIS_EXTENSION] THEN
    DISCH_THEN (MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    REWRITE_TAC [group_homomorphism, SUBSET, FORALL_IN_IMAGE] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"f:B->B") o CONJUNCT1) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"subfield_generated l (e:B->bool)"]
                  GALOIS_GROUP_FINITE_FIELD) THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"subfield_generated l (e:B->bool)"]
                  GALOIS_GROUP_FROBENIUS) THEN
    ASM_REWRITE_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD,
                    RING_POW_SUBFIELD_GENERATED] THEN
    ASM_SIMP_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
    ABBREV_TAC
     (← q r"frob = \x:B. if x IN e then ring_pow l x (CARD(ring_carrier(k:A ring)))
                  else x") THEN
    STRIP_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"!j. group_pow (galois_group(k,subfield_generated l e) (h:A->B)) frob j =
          (\x:B. if x IN e
                 then ring_pow l x (CARD(ring_carrier(k:A ring)) EXP j) else x)")
    ASSUME_TAC THENL
     [X_GEN_TAC (← q r"j:num") THEN EXPAND_TAC "frob" THEN
      MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"subfield_generated l (e:B->bool)",
                     ← q r"CARD(ring_carrier(k:A ring))", ← q r"j:num"]
                    GALOIS_GROUP_POW_RING_POW) THEN
      ASM_SIMP_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD,
                   RING_POW_SUBFIELD_GENERATED],
      ALL_TAC] THEN
    REWRITE_TAC [EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL
     [MP_TAC (← ISPECL [← q r"galois_group(k,subfield_generated l e) (h:A->B)",
                     ← q r"frob:B->B"] CARRIER_SUBGROUP_GENERATED_BY_SING) THEN
      ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
      SUBGOAL_THEN
       (← q r"(\x. if x IN e then (f:B->B) x else x) IN
        {group_zpow (galois_group(k,subfield_generated l e) (h:A->B)) frob m |
         m IN (:int)}")
      MP_TAC THENL [ASM_MESON_TAC [], REWRITE_TAC [IN_ELIM_THM, IN_UNIV]] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"m:int")) THEN
      SUBGOAL_THEN (← q r"&0 <= m rem &n /\ m rem &n < &n") STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC [INT_REM_POS, INT_LT_REM, INT_OF_NUM_EQ, INT_OF_NUM_LT,
                     LE_1],
        ALL_TAC] THEN
      ABBREV_TAC (← q r"j = num_of_int(m rem &n)") THEN
      SUBGOAL_THEN (← q r"m rem &n = &j") ASSUME_TAC THENL
       [EXPAND_TAC "j" THEN ASM_SIMP_TAC [INT_OF_NUM_OF_INT], ALL_TAC] THEN
      EXISTS_TAC (← q r"j:num") THEN CONJ_TAC THENL
       [REWRITE_TAC [← GSYM INT_OF_NUM_LT] THEN ASM_MESON_TAC [], ALL_TAC] THEN
      X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (fun th => tactic_of do
        if !(is_eq (concl th)) then throw "check"
        pure (MP_TAC (← AP_THM th (← q r"x:B")))) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
      MP_TAC (← ISPECL [← q r"galois_group(k,subfield_generated l e) (h:A->B)",
                     ← q r"frob:B->B", ← q r"m:int"] GROUP_ZPOW_REM_ELEMENT_ORDER) THEN
      ASM_REWRITE_TAC [GROUP_NPOW] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC [],
      MAP_EVERY X_GEN_TAC [← q r"i:num", ← q r"j:num"] THEN STRIP_TAC THEN
      MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC (← q r"n:num") THEN
      ASM_REWRITE_TAC [] THEN
      MP_TAC (← ISPECL [← q r"galois_group(k,subfield_generated l e) (h:A->B)",
                     ← q r"frob:B->B", ← q r"i:num", ← q r"j:num"] GROUP_POW_EQ) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
      REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"x:B") THEN
      COND_CASES_TAC THEN ASM_MESON_TAC []]))

  -- @@RETURN BEGIN
  return { FINITE_FIELD_POW_ITERATE, FINITE_FIELD_ALGEBRAIC_CLOSURE_LAYER,
           FINITE_FIELD_IRREDUCIBLE_ROOT_EXISTS, FINITE_FIELD_NORMAL_IMP_GALOIS,
           FINITE_GALOIS_SUBFIELDS_FINITE_FIELD, FINITE_FIELD_LAYERS_COVER,
           FINITE_FIELD_LAYER_POW, ABELIAN_GALOIS_GROUP_FINITE_FIELD,
           GALOIS_GROUP_FINITE_FIELD_EXPONENT }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Rabin irreducibility test (M. O. Rabin, Probabilistic algorithms in       -/
/- finite fields, SIAM J. Comput. 9, 1980): a polynomial p of degree n > 0   -/
/- over a field with q elements is irreducible exactly when p divides        -/
/- X^(q^n) - X and p is coprime to X^(q^(n DIV r)) - X for each prime r      -/
/- dividing n.                                                               -/
/- ------------------------------------------------------------------------- -/

structure RabinTest where
  -- @@FIELDS
  RABIN_IRREDUCIBILITY_NECESSARY : thm
  RABIN_IRREDUCIBILITY_SUFFICIENT : thm
  RABIN_IRREDUCIBILITY_TEST : thm
  deriving Inhabited

@[nospecialize]
def setupRabinTest [HolBase] (D : FiniteFieldsDeps) (BIrreducibleXPow : IrreducibleXPow) :
    ExceptT String IO RabinTest := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, TAUT, .. } := D
  let { DE_MORGAN_THM, DIVIDES_REFL, DIV_MULT, EQ_MULT_LCANCEL,
        FIELD_IMP_INTEGRAL_DOMAIN, IMP_CONJ, INTEGRAL_DOMAIN_POLY_RING,
        IRREDUCIBLE_IMP_POLY_DEG_NZ, LEFT_IMP_EXISTS_THM, .. } := D.core1
  let { MULT_EQ_0, MULT_EQ_1, NOETHERIAN_DOMAIN_IRREDUCIBLE_FACTOR_EXISTS,
        NOT_EXISTS_THM, PID_IMP_UFD, PID_POLY_RING, POLY_CLAUSES, POLY_DEG_CONST,
        POLY_DEG_DIVIDES_LE, POLY_DEG_EQ_0_UNIT, POLY_DEG_MUL, POLY_RING_CLAUSES,
        PRIME_1, PRIME_FACTOR, PRIME_IMP_NZ, RING_ASSOCIATES_IRREDUCIBLE,
        RING_ASSOCIATES_RMUL, RING_DIVIDES_TRANS, RING_IRREDUCIBLE_COPRIME_EQ,
        RING_IRREDUCIBLE_IN_CARRIER, RING_MUL_RZERO, RING_POLYNOMIAL,
        RING_POLYNOMIAL_POW, RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_VAR,
        RING_UNIT_POLY_DOMAIN, divides, ring_coprime, ring_divides, ring_irreducible, .. } := D.core2
  let { IRREDUCIBLE_DIVIDES_X_POW_SUB_X, .. } := BIrreducibleXPow
  -- @@SCOPE END

  let RABIN_IRREDUCIBILITY_NECESSARY ← (do
    let lemma ← prove
     r"!n r. prime r /\ r divides n /\ ~(n = 0) ==> ~(n divides n DIV r)"
     (← do
      let a1 ← ARITH_RULE
       (← q r"m = (r * m) * c <=> m * (r * c) = m * 1")
      pure (REPEAT GEN_TAC THEN REWRITE_TAC [divides] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      REWRITE_TAC [IMP_CONJ, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"m:num") THEN
      DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
      ASM_SIMP_TAC [DIV_MULT, NOT_EXISTS_THM] THEN X_GEN_TAC (← q r"c:num") THEN
      RULE_ASSUM_TAC (REWRITE_RULE [MULT_EQ_0, DE_MORGAN_THM]) THEN
      ONCE_REWRITE_TAC [a1] THEN
      ASM_REWRITE_TAC [EQ_MULT_LCANCEL, MULT_EQ_1] THEN
      ASM_MESON_TAC [PRIME_1]))
    prove
     r"!(k:A ring) p n.
        field k /\ FINITE(ring_carrier k) /\
        p IN ring_carrier(poly_ring k (:1)) /\
        poly_deg k p = n /\ ~(n = 0) /\
        ring_irreducible (poly_ring k (:1)) p
        ==> ring_divides (poly_ring k (:1)) p
              (ring_sub (poly_ring k (:1))
                 (ring_pow (poly_ring k (:1)) (poly_var k one)
                           (CARD(ring_carrier k) EXP n))
                 (poly_var k one)) /\
            !q. prime q /\ q divides n
                ==> ring_coprime (poly_ring k (:1))
                      (p,ring_sub (poly_ring k (:1))
                           (ring_pow (poly_ring k (:1)) (poly_var k one)
                                     (CARD(ring_carrier k) EXP (n DIV q)))
                           (poly_var k one))"
     (REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [POLY_RING_CLAUSES] THEN
      ASM_SIMP_TAC [IRREDUCIBLE_DIVIDES_X_POW_SUB_X, RING_IRREDUCIBLE_COPRIME_EQ,
                   DIVIDES_REFL] THEN
      X_GEN_TAC (← q r"r:num") THEN STRIP_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC [← GSYM RING_POLYNOMIAL] THEN
        SIMP_TAC [RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_POW, RING_POLYNOMIAL_VAR],
        MATCH_MP_TAC lemma THEN ASM_REWRITE_TAC []]))

  let RABIN_IRREDUCIBILITY_SUFFICIENT ← (do
    let lemma ← prove
     r"!d n. d divides n /\ ~(d = 0) /\ d < n
             ==> ?r. prime r /\ r divides n /\ d divides n DIV r"
     (REPEAT GEN_TAC THEN
      REWRITE_TAC [IMP_CONJ, LEFT_IMP_EXISTS_THM, divides] THEN
      X_GEN_TAC (← q r"m:num") THEN DISCH_THEN SUBST1_TAC THEN REPEAT DISCH_TAC THEN
      MP_TAC (← SPEC (← q r"m:num") PRIME_FACTOR) THEN ANTS_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"d < d * 1") THEN ARITH_TAC,
        REWRITE_TAC [divides]] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"r:num") (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN (← q r"s:num") SUBST_ALL_TAC))) THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
      EXISTS_TAC (← q r"r:num") THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"d * r * s = r * d * s") SUBST1_TAC THENL
       [ARITH_TAC, ASM_SIMP_TAC [DIV_MULT]] THEN
      MESON_TAC [])
    prove
     r"!(k:A ring) p n.
        field k /\ FINITE(ring_carrier k) /\
        p IN ring_carrier(poly_ring k (:1)) /\
        ~(p = ring_0(poly_ring k (:1))) /\
        poly_deg k p = n /\ ~(n = 0) /\
        ring_divides (poly_ring k (:1)) p
          (ring_sub (poly_ring k (:1))
             (ring_pow (poly_ring k (:1)) (poly_var k one)
                       (CARD(ring_carrier k) EXP n))
             (poly_var k one)) /\
        (!q. prime q /\ q divides n
             ==> ring_coprime (poly_ring k (:1))
                   (p,ring_sub (poly_ring k (:1))
                        (ring_pow (poly_ring k (:1)) (poly_var k one)
                                  (CARD(ring_carrier k) EXP (n DIV q)))
                        (poly_var k one)))
        ==> ring_irreducible (poly_ring k (:1)) p"
     (← do
      -- right to left: the rules in reverse order of appearance
      let t2 ← TAUT (← q r"(~b ==> d) /\ ~b ==> d /\ ~b")
      let t1 ← TAUT (← q r"d /\ ~b ==> (d <=> a \/ b) ==> a")
      let a1 ← ARITH_RULE (← q r"~(d < n) /\ d <= n ==> d = n")
      pure (REPEAT GEN_TAC THEN REWRITE_TAC [← CONJUNCT2 POLY_RING_CLAUSES] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN
       (← q r"UFD(poly_ring (k:A ring) (:1)) /\ integral_domain(poly_ring k (:1))")
      STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC [PID_IMP_UFD, PID_POLY_RING, INTEGRAL_DOMAIN_POLY_RING,
                     FIELD_IMP_INTEGRAL_DOMAIN],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"~ring_unit (poly_ring (k:A ring) (:1)) p") ASSUME_TAC THENL
       [ASM_SIMP_TAC [RING_UNIT_POLY_DOMAIN, FIELD_IMP_INTEGRAL_DOMAIN] THEN
        ASM_MESON_TAC [POLY_DEG_CONST],
        ALL_TAC] THEN
      MP_TAC (← ISPECL [← q r"poly_ring (k:A ring) (:1)", ← q r"p:(1->num)->A"]
        NOETHERIAN_DOMAIN_IRREDUCIBLE_FACTOR_EXISTS) THEN
      ASM_REWRITE_TAC [POLY_RING_CLAUSES] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"g:(1->num)->A") STRIP_ASSUME_TAC) THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_IRREDUCIBLE_IN_CARRIER) THEN
      SUBGOAL_THEN (← q r"poly_deg k (g:(1->num)->A) = n") ASSUME_TAC THENL
       [MATCH_MP_TAC a1 THEN
        CONJ_TAC THENL
         [DISCH_TAC,
          FIRST_X_ASSUM (fun th => tactic_of do
            let c ← q r"n:num"
            if !((← liftExcept (rand (concl th))) == c) then throw "check"
            pure ((SUBST1_TAC o SYM) th)) THEN
          MATCH_MP_TAC POLY_DEG_DIVIDES_LE THEN EXISTS_TAC (← q r"(:1)") THEN
          ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN]] THEN
        MP_TAC (← ISPECL [← q r"poly_deg k (g:(1->num)->A)", ← q r"n:num"] lemma) THEN
        ANTS_TAC THENL
         [ASM_SIMP_TAC [IRREDUCIBLE_IMP_POLY_DEG_NZ,
                       ← GSYM IRREDUCIBLE_DIVIDES_X_POW_SUB_X] THEN
          ASM_MESON_TAC [RING_DIVIDES_TRANS],
          DISCH_THEN (X_CHOOSE_THEN (← q r"r:num") STRIP_ASSUME_TAC)] THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"r:num")) THEN
        ASM_REWRITE_TAC [] THEN REWRITE_TAC [ring_coprime] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"g:(1->num)->A") o CONJUNCT2 o CONJUNCT2) THEN
        ASM_SIMP_TAC [IRREDUCIBLE_DIVIDES_X_POW_SUB_X] THEN
        ASM_MESON_TAC [ring_irreducible],
        ALL_TAC] THEN
      FIRST_X_ASSUM (fun th => tactic_of do
        let c ← q r"ring_divides (poly_ring k (:1)) g (p:(1->num)->A)"
        if !(concl th == c) then throw "check"
        pure (MP_TAC (← GEN_REWRITE_RULE I [ring_divides] th)))
      THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN (← q r"u:(1->num)->A") STRIP_ASSUME_TAC))) THEN
      SUBGOAL_THEN (← q r"ring_unit (poly_ring k (:1)) (u:(1->num)->A)") ASSUME_TAC THENL
       [MP_TAC (← ISPECL [← q r"k:A ring", ← q r"(:1)", ← q r"u:(1->num)->A"]
          POLY_DEG_EQ_0_UNIT) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC [RING_POLYNOMIAL], ALL_TAC] THEN
        MATCH_MP_TAC t1 THEN
        MATCH_MP_TAC t2 THEN CONJ_TAC THENL
         [DISCH_TAC THEN
          MP_TAC (← ISPECL [← q r"k:A ring", ← q r"g:(1->num)->A", ← q r"u:(1->num)->A"]
            POLY_DEG_MUL) THEN
          ANTS_TAC THENL
           [ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, RING_POLYNOMIAL] THEN
            ASM_MESON_TAC [ring_irreducible, POLY_RING_CLAUSES],
            ALL_TAC] THEN
          SUBGOAL_THEN (← q r"poly_mul k g u = (p:(1->num)->A)") SUBST1_TAC THENL
           [ASM_REWRITE_TAC [POLY_RING_CLAUSES], ASM_ARITH_TAC],
          DISCH_TAC THEN UNDISCH_TAC (← q r"~(p:(1->num)->A = poly_0 k)") THEN
          ASM_SIMP_TAC [RING_MUL_RZERO, POLY_CLAUSES]],
        ALL_TAC] THEN
      MP_TAC (← ISPECL [← q r"poly_ring (k:A ring) (:1)", ← q r"g:(1->num)->A",
                     ← q r"p:(1->num)->A"] RING_ASSOCIATES_IRREDUCIBLE) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC RING_ASSOCIATES_RMUL THEN
      ASM_REWRITE_TAC [])))

  let RABIN_IRREDUCIBILITY_TEST ← prove
   r"!(k:A ring) p n.
        field k /\ FINITE(ring_carrier k) /\
        p IN ring_carrier(poly_ring k (:1)) /\
        ~(p = ring_0(poly_ring k (:1))) /\
        ~(ring_unit (poly_ring k (:1)) p) /\
        poly_deg k p = n /\ ~(n = 0)
        ==> (ring_irreducible (poly_ring k (:1)) p <=>
             ring_divides (poly_ring k (:1)) p
               (ring_sub (poly_ring k (:1))
                  (ring_pow (poly_ring k (:1)) (poly_var k one)
                            (CARD(ring_carrier k) EXP n))
                  (poly_var k one)) /\
             !q. prime q /\ q divides n
                 ==> ring_coprime (poly_ring k (:1))
                       (p,ring_sub (poly_ring k (:1))
                            (ring_pow (poly_ring k (:1)) (poly_var k one)
                                      (CARD(ring_carrier k) EXP (n DIV q)))
                            (poly_var k one)))"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN MATCH_MP_TAC RABIN_IRREDUCIBILITY_NECESSARY THEN
      ASM_REWRITE_TAC [],
      STRIP_TAC THEN MATCH_MP_TAC RABIN_IRREDUCIBILITY_SUFFICIENT THEN
      EXISTS_TAC (← q r"n:num") THEN ASM_REWRITE_TAC []])

  -- @@RETURN BEGIN
  return { RABIN_IRREDUCIBILITY_NECESSARY, RABIN_IRREDUCIBILITY_SUFFICIENT,
           RABIN_IRREDUCIBILITY_TEST }
  -- @@RETURN END

end HolLibrary.FiniteFields
