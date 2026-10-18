/- ========================================================================= -/
/- Rabin's test for irreducibility of polynomials over finite fields.       -/
/-                                                                           -/
/- All development (statements and proof) written by Claude Code, Opus 4.6  -/
/- ========================================================================= -/
/- File: HolLibrary/RabinTest.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/rabin_test.ml`, by hand, in file
  order, in the style of HolLibrary/FieldTheory.lean (see there and
  HolMath/Base.lean for the conventions).  rabin_test.ml begins with
  `needs "Library/fieldtheory.ml"`; the theorems it uses from fieldtheory.ml,
  the files it needs, and the core library are supplied via the CoreThms
  structures (SessionLibrary.RabinTest fills them).  Each section is a bundle
  (a `structure`) built by a `setup` function; SessionLibrary/RabinTest.lean
  builds the bundles in order and exports every name under its HOL Light
  name.

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first (`let ... in` lemmas first, in text order).  Where one
  proof applies two or more rules that print or use counters (MESON,
  ARITH_RULE, TAUT, RING_RULE) they are bound first, in OCaml's order.
-/

import HolLibrary.FieldTheory

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolLibrary.RabinTest

-- @@COREFILL BEGIN
/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD_SYM CARD_CLAUSES CARD_DELETE CARD_EQ_0 CARD_IMAGE_LE CARD_NUMSEG_LT
   CARD_SUBSET DE_MORGAN_THM DIVIDES_0 DIVIDES_DIVIDES_DIV
   DIVIDES_DIVIDES_DIV_EQ DIVIDES_DIV_MULT DIVIDES_DIV_SELF
   DIVIDES_PRIME_PRIME DIVIDES_TRANS DIVISION_SIMP EMPTY_SUBSET
   EQ_MULT_LCANCEL EXP EXP_1 EXP_ADD EXP_EQ_0 EXP_EXP
   FIELD_IMP_INTEGRAL_DOMAIN FIELD_MUL_EQ_0 FIELD_MUL_LINV FIELD_MUL_RINV
   FIELD_NONTRIVIAL FIELD_QUOTIENT_RING FIELD_UNIT FINITE_DELETE FINITE_EMPTY
   FINITE_EXTENSION_BASIS FINITE_IMAGE
   FINITE_IMP_ALGEBRAIC_EXTENSION_EXPLICIT FINITE_INSERT
   FINITE_INTEGRAL_DOMAIN_CHAR FINITE_INTEGRAL_DOMAIN_SIZE FINITE_NUMSEG_LT
   FINITE_SIMPLE_ALGEBRAIC_EXTENSION FORALL_IN_GSPEC FORALL_IN_INSERT
   HAS_SIZE HAS_SIZE_FINITE_EXTENSION IMAGE_POLY_EXTEND_1 INSERT_SUBSET
   INTEGRAL_DOMAIN_MUL_RCANCEL INTEGRAL_DOMAIN_POLY_RING
   INTEGRAL_DOMAIN_PRODUCT_EQ_0 IN_DELETE IN_ELIM_THM IN_IDEAL_GENERATED_SELF
   IN_IDEAL_GENERATED_SING IN_IDEAL_GENERATED_SING_EQ IN_IMAGE IN_INSERT
   IN_POLY_RING_CARRIER IN_UNIV KRONECKER_FIELD_EXTENSION LE_ANTISYM LE_EXP
   LE_REFL LE_TRANS MAXIMAL_IMP_RING_IDEAL MOD_LT_EQ MULT_CLAUSES MULT_EQ_1
   MULT_SYM NOETHERIAN_DOMAIN_IRREDUCIBLE_FACTOR_EXISTS NOT_FORALL_THM : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (NOT_IMP NOT_IN_EMPTY NOT_SUC PID_IMP_UFD PID_POLY_RING POLY_CONST
   POLY_CONST_0 POLY_DEG_CONST POLY_DEG_EQ_0 POLY_DEG_MUL POLY_DEG_SUB_LE
   POLY_DEG_VAR POLY_DEG_VAR_POW POLY_EVAL_POW POLY_EVAL_SUB POLY_EVAL_VAR
   POLY_EXTEND_UNIQUE POLY_RING POLY_RING_CLAUSES POLY_ROOT_BOUND
   POLY_VAR_UNIV PRIME_DIVEXP PRIME_FACTOR PRIME_GE_2 QUOTIENT_RING_0
   QUOTIENT_RING_CARRIER RING_0 RING_1 RING_CARRIER_NONEMPTY
   RING_CHAR_DIVIDES_ORDER RING_CHAR_DIVIDES_PRIME
   RING_CHAR_HOMOMORPHIC_IMAGE RING_CHAR_MONOMORPHIC_IMAGE RING_COSET_EQ
   RING_COSET_EQ_IDEAL RING_DIVIDES_0 RING_DIVIDES_ADD RING_DIVIDES_SUB
   RING_DIVIDES_SUB_POW RING_DIVIDES_TRANS RING_ENDOMORPHISM_EQ
   RING_ENDOMORPHISM_FROBENIUS RING_EPIMORPHISM_RING_COSET
   RING_HOMOMORPHISMS_EQ_FROM_POLY_RING RING_HOMOMORPHISM_COMPOSE
   RING_HOMOMORPHISM_ID RING_HOMOMORPHISM_POLY_CONST RING_HOMOMORPHISM_POW
   RING_HOMOMORPHISM_RING_COSET RING_HOMOMORPHISM_SUB
   RING_INDEPENDENT_LE_SPAN RING_INV RING_IRREDUCIBLE_DIVIDES_OR_COPRIME
   RING_IRREDUCIBLE_EQ_MAXIMAL_IDEAL RING_KERNEL_RING_COSET
   RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_MONOMORPHISM_POLY_CONST RING_MUL
   RING_MUL_ASSOC RING_MUL_LID RING_MUL_LZERO RING_MUL_RID RING_MUL_RZERO
   RING_POLYNOMIAL_POW RING_POLYNOMIAL_VAR RING_POW RING_POW_1 RING_POW_ADD
   RING_POW_MUL RING_POW_POW : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms3 where
  (RING_POW_ZERO RING_PRODUCT RING_PRODUCT_EQ_GENERAL_INVERSES
   RING_PRODUCT_LMUL RING_SIMPLE_ALGEBRAIC_EXTENSION_SPAN RING_SUB
   RING_SUB_EQ_0 RING_SUB_REFL RING_SUB_TELESCOPE RING_UNIT_INV
   RING_UNIT_POLY_CONST RING_UNIT_POLY_DOMAIN SIMPLE_IMAGE_GEN
   SUBRING_GENERATED_SUPERSET SUBSET SUBSET_REFL SUBSET_UNIV TRIVIAL_RING_10
   UNIV_1 algebraic_over divides field_extension o_THM one ring_basis
   ring_coprime ring_divides ring_endomorphism ring_epimorphism
   ring_homomorphism ring_independent ring_irreducible ring_kernel ring_pow
   ring_spanning : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms4 where
  deriving Inhabited

-- @@COREFILL END

/-- What rabintest.ml uses from Session besides theorems. -/
structure RabinTestDeps where
  -- decision procedures and tactics
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_ARITH_TAC : tactic
  MESON_TAC : List thm → tactic
  ASM_MESON_TAC : List thm → tactic
  SET_TAC : List thm → tactic
  INDUCT_TAC : tactic
  RING_RULE : term → ExceptT String IO thm   -- ringtheory.ml's RING_RULE (from RingTheory's RingRule bundle)
  TAUT : term → ExceptT String IO thm         -- bool.ml's TAUT
  -- (add fields here as needed, with a comment naming the HOL Light value)
  core1 : CoreThms1
  core2 : CoreThms2
  core3 : CoreThms3
  core4 : CoreThms4

/- rabin_test.ml begins with `needs "Library/fieldtheory.ml"`. -/

/- ------------------------------------------------------------------------- -/
/- General lemmas.                                                           -/
/- ------------------------------------------------------------------------- -/

structure GeneralLemmas where
  -- @@FIELDS
  RING_DIVIDES_POW_ITERATE : thm
  POLY_NONUNIT_DEGREE_GE_1 : thm
  RING_DIVIDES_REDUCE : thm
  deriving Inhabited

@[nospecialize]
def setupGeneralLemmas [HolBase] (D : RabinTestDeps) :
    ExceptT String IO GeneralLemmas := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, RING_RULE, .. } := D
  let { EXP, EXP_1, FIELD_UNIT, IN_POLY_RING_CARRIER, MULT_CLAUSES, MULT_SYM, .. } := D.core1
  let { NOT_SUC, POLY_CONST_0, POLY_DEG_EQ_0, POLY_RING, RING_DIVIDES_ADD,
        RING_DIVIDES_SUB, RING_DIVIDES_SUB_POW, RING_DIVIDES_TRANS, RING_POW,
        RING_POW_POW, .. } := D.core2
  let { RING_SUB, RING_SUB_TELESCOPE, RING_UNIT_POLY_CONST, ring_divides, .. } := D.core3
  -- @@SCOPE END

  let RING_DIVIDES_POW_ITERATE ← prove
   r"!r (p:A) x m k. integral_domain r /\
       p IN ring_carrier r /\ x IN ring_carrier r /\
       ring_divides r p (ring_sub r (ring_pow r x m) x) /\ ~(k = 0) /\ 1 <= m
       ==> ring_divides r p (ring_sub r (ring_pow r x (m EXP k)) x)"
   (GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
    INDUCT_TAC THENL [MESON_TAC [], ALL_TAC] THEN REWRITE_TAC [NOT_SUC] THEN
    DISCH_TAC THEN ASM_CASES_TAC (← q r"k = 0") THENL
    [ASM_REWRITE_TAC [EXP, EXP_1, MULT_CLAUSES], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_divides r (p:A) (ring_sub r (ring_pow r x (m EXP k)) x)")
      ASSUME_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_pow r (x:A) (m EXP k) IN ring_carrier r") ASSUME_TAC THENL
    [MATCH_MP_TAC RING_POW THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_pow r (x:A) (m EXP (SUC k)) =
                  ring_pow r (ring_pow r x (m EXP k)) m") SUBST1_TAC THENL
    [REWRITE_TAC [EXP] THEN ONCE_REWRITE_TAC [MULT_SYM] THEN
     ASM_SIMP_TAC [RING_POW_POW], ALL_TAC] THEN
    SUBGOAL_THEN
      (← q r"ring_sub r (ring_pow r (ring_pow r (x:A) (m EXP k)) m) x = ring_add r
         (ring_sub r (ring_pow r (ring_pow r x (m EXP k)) m) (ring_pow r x m))
         (ring_sub r (ring_pow r x m) x)") SUBST1_TAC THENL
    [MATCH_MP_TAC (← GSYM RING_SUB_TELESCOPE) THEN ASM_SIMP_TAC [RING_POW], ALL_TAC] THEN
    MATCH_MP_TAC RING_DIVIDES_ADD THEN CONJ_TAC THENL
    [
     MATCH_MP_TAC RING_DIVIDES_TRANS THEN
     EXISTS_TAC (← q r"ring_sub r (ring_pow r (x:A) (m EXP k)) x") THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC RING_DIVIDES_SUB_POW THEN
     ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC,
     ASM_REWRITE_TAC []])

  /- Helper: non-unit non-zero polynomial over a field has degree >= 1 -/
  let POLY_NONUNIT_DEGREE_GE_1 ← prove
   r"!f:A ring p (s:V->bool).
       field f /\
       p IN ring_carrier(poly_ring f s) /\
       ~(p = ring_0(poly_ring f s)) /\
       ~(ring_unit (poly_ring f s) p)
       ==> 1 <= poly_deg f p"
   (REWRITE_TAC [IN_POLY_RING_CARRIER, ← ARITH_RULE (← q r"1 <= d <=> ~(d = 0)")] THEN
    SIMP_TAC [POLY_DEG_EQ_0] THEN
    MESON_TAC [RING_UNIT_POLY_CONST, FIELD_UNIT, POLY_CONST_0, POLY_RING])

  /- Helper: if p | (u - x) and p | (u^m - x) and m >= 1, then p | (x^m - x) -/
  let RING_DIVIDES_REDUCE ← prove
   r"!r (p:A) u x m.
      u IN ring_carrier r /\ x IN ring_carrier r /\
      ring_divides r p (ring_sub r u x) /\
      ring_divides r p (ring_sub r (ring_pow r u m) x) /\ ~(m = 0)
      ==> ring_divides r p (ring_sub r (ring_pow r x m) x)"
   (← do
    let r1 ← RING_RULE (← q r"ring_sub r (ring_sub r (a:A) b) (ring_sub r a c) = ring_sub r c b")
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"(p:A) IN ring_carrier r") ASSUME_TAC THENL
    [ASM_MESON_TAC [ring_divides], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_divides r (p:A)
      (ring_sub r (ring_pow r u m) (ring_pow r x m))") ASSUME_TAC THENL
    [MATCH_MP_TAC RING_DIVIDES_TRANS THEN
     EXISTS_TAC (← q r"ring_sub r (u:A) x") THEN ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC RING_DIVIDES_SUB_POW THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_divides r (p:A)
      (ring_sub r (ring_sub r (ring_pow r u m) x)
                  (ring_sub r (ring_pow r u m) (ring_pow r x m)))") MP_TAC THENL
    [MATCH_MP_TAC RING_DIVIDES_SUB THEN
     ASM_SIMP_TAC [RING_POW, RING_SUB], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_sub r (ring_sub r (ring_pow r (u:A) m) x)
                  (ring_sub r (ring_pow r u m) (ring_pow r x m)) =
       ring_sub r (ring_pow r x m) x")
      (fun th => REWRITE_TAC [th]) THEN ASM_SIMP_TAC [RING_POW, r1]))

  -- @@RETURN BEGIN
  return { RING_DIVIDES_POW_ITERATE, POLY_NONUNIT_DEGREE_GE_1, RING_DIVIDES_REDUCE }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Finite field Fermat / Frobenius                                           -/
/- ------------------------------------------------------------------------- -/

structure FiniteFieldFrobenius where
  -- @@FIELDS
  FIELD_NONZERO_PRODUCT_PERMUTE : thm
  FINITE_FIELD_ELEMENT_POW : thm
  QUOTIENT_POLY_RING_FINITE_CARD : thm
  deriving Inhabited

@[nospecialize]
def setupFiniteFieldFrobenius [HolBase] (D : RabinTestDeps) :
    ExceptT String IO FiniteFieldFrobenius := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, MESON_TAC, TAUT, .. } := D
  let { CARD_DELETE, CARD_EQ_0, CARD_IMAGE_LE, CARD_NUMSEG_LT,
        FIELD_IMP_INTEGRAL_DOMAIN, FIELD_MUL_EQ_0, FIELD_MUL_LINV, FIELD_MUL_RINV,
        FIELD_QUOTIENT_RING, FIELD_UNIT, FINITE_DELETE, FINITE_EXTENSION_BASIS,
        FINITE_IMAGE, FINITE_IMP_ALGEBRAIC_EXTENSION_EXPLICIT, FINITE_NUMSEG_LT,
        FINITE_SIMPLE_ALGEBRAIC_EXTENSION, FORALL_IN_GSPEC, HAS_SIZE,
        HAS_SIZE_FINITE_EXTENSION, IMAGE_POLY_EXTEND_1, INTEGRAL_DOMAIN_MUL_RCANCEL,
        INTEGRAL_DOMAIN_PRODUCT_EQ_0, IN_DELETE, IN_ELIM_THM, IN_IDEAL_GENERATED_SELF,
        IN_IDEAL_GENERATED_SING_EQ, IN_IMAGE, IN_UNIV, KRONECKER_FIELD_EXTENSION,
        LE_ANTISYM, LE_REFL, LE_TRANS, MAXIMAL_IMP_RING_IDEAL, .. } := D.core1
  let { PID_POLY_RING, POLY_DEG_MUL, POLY_EXTEND_UNIQUE, POLY_RING_CLAUSES,
        POLY_VAR_UNIV, QUOTIENT_RING_0, QUOTIENT_RING_CARRIER, RING_0, RING_1,
        RING_CARRIER_NONEMPTY, RING_COSET_EQ_IDEAL, RING_HOMOMORPHISM_RING_COSET,
        RING_INDEPENDENT_LE_SPAN, RING_INV, RING_IRREDUCIBLE_EQ_MAXIMAL_IDEAL,
        RING_KERNEL_RING_COSET, RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL,
        RING_MUL_ASSOC, RING_MUL_LID, RING_MUL_RID, RING_MUL_RZERO, RING_POW,
        RING_POW_1, RING_POW_ADD, .. } := D.core2
  let { RING_POW_ZERO, RING_PRODUCT, RING_PRODUCT_EQ_GENERAL_INVERSES,
        RING_PRODUCT_LMUL, RING_SIMPLE_ALGEBRAIC_EXTENSION_SPAN, RING_UNIT_INV,
        SIMPLE_IMAGE_GEN, SUBRING_GENERATED_SUPERSET, SUBSET, SUBSET_REFL, SUBSET_UNIV,
        algebraic_over, field_extension, o_THM, one, ring_basis, ring_divides,
        ring_homomorphism, ring_independent, ring_irreducible, ring_kernel, ring_pow,
        ring_spanning, .. } := D.core3
  -- @@SCOPE END

  let FIELD_NONZERO_PRODUCT_PERMUTE ← prove
   r"!f:A ring x. field f /\ FINITE(ring_carrier f) /\
      x IN ring_carrier f /\ ~(x = ring_0 f)
      ==> ring_product f (ring_carrier f DELETE ring_0 f) (\y. ring_mul f x y) =
          ring_product f (ring_carrier f DELETE ring_0 f) (\y. y)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_PRODUCT_EQ_GENERAL_INVERSES THEN
    EXISTS_TAC (← q r"\y:A. ring_mul f x y") THEN
    EXISTS_TAC (← q r"\y:A. ring_mul f (ring_inv f x) y") THEN
    SUBGOAL_THEN (← q r"ring_inv f (x:A) IN ring_carrier f /\
                  ~(ring_inv f x = ring_0 f)") STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC [RING_INV, FIELD_UNIT, RING_UNIT_INV], ALL_TAC] THEN
    REWRITE_TAC [] THEN
    CONJ_TAC THEN X_GEN_TAC (← q r"y:A") THEN REWRITE_TAC [IN_DELETE] THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THENL [
     ASM_MESON_TAC [RING_MUL],
     ASM_SIMP_TAC [FIELD_MUL_EQ_0],
     ASM_SIMP_TAC [RING_MUL_ASSOC, FIELD_MUL_RINV, RING_MUL_LID],
     ASM_MESON_TAC [RING_MUL],
     ASM_SIMP_TAC [FIELD_MUL_EQ_0],
     ASM_SIMP_TAC [RING_MUL_ASSOC, FIELD_MUL_LINV, RING_MUL_LID]])

  let FINITE_FIELD_ELEMENT_POW ← prove
   r"!f:A ring. field f /\ FINITE(ring_carrier f) ==> !x. x IN ring_carrier f
         ==> ring_pow f x (CARD(ring_carrier f)) = x"
   (← do
    let a1 ← ARITH_RULE (← q r"~(n = 0) ==> n = (n - 1) + 1")
    pure (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"x:A = ring_0 f") THENL [ASM_SIMP_TAC [RING_POW_ZERO] THEN
     COND_CASES_TAC THENL
     [ASM_MESON_TAC [CARD_EQ_0, RING_CARRIER_NONEMPTY], REFL_TAC], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"CARD(ring_carrier(f:A ring)) =
                  (CARD(ring_carrier f) - 1) + 1") SUBST1_TAC THENL
    [MATCH_MP_TAC a1 THEN
     ASM_MESON_TAC [CARD_EQ_0, RING_CARRIER_NONEMPTY], ALL_TAC] THEN
    ASM_SIMP_TAC [RING_POW_ADD, RING_POW] THEN
    REWRITE_TAC [ring_pow, RING_MUL_RID] THEN
    SUBGOAL_THEN (← q r"ring_pow f x (CARD(ring_carrier(f:A ring)) - 1) = ring_1 f")
      (fun th => ASM_SIMP_TAC [th, RING_MUL_RID, RING_MUL_LID,
                              RING_POW_1, RING_POW]) THEN
    ABBREV_TAC (← q r"s = ring_carrier f DELETE (ring_0 (f:A ring))") THEN SUBGOAL_THEN
      (← q r"FINITE (s:A->bool) /\ CARD s = CARD(ring_carrier(f:A ring)) - 1")
      STRIP_ASSUME_TAC THENL [EXPAND_TAC "s" THEN
     ASM_SIMP_TAC [FINITE_DELETE, CARD_DELETE, RING_0], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(x:A) IN s") ASSUME_TAC THENL
    [EXPAND_TAC "s" THEN ASM_REWRITE_TAC [IN_DELETE], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!y:A. y IN s ==> y IN ring_carrier f /\ ~(y = ring_0 f)")
      ASSUME_TAC THENL [EXPAND_TAC "s" THEN SIMP_TAC [IN_DELETE], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"~(ring_product f s (\y:A. y) = ring_0 f)") ASSUME_TAC THENL
    [ASM_SIMP_TAC [INTEGRAL_DOMAIN_PRODUCT_EQ_0, FIELD_IMP_INTEGRAL_DOMAIN] THEN
     ASM_MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_product f s (\y:A. ring_mul f x y) =
       ring_product f s (\y:A. y)") ASSUME_TAC THENL
    [EXPAND_TAC "s" THEN MATCH_MP_TAC FIELD_NONZERO_PRODUCT_PERMUTE THEN
     ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_product f s (\y:A. ring_mul f x y) =
       ring_mul f (ring_pow f x (CARD(s:A->bool)))
                 (ring_product f s (\y:A. y))") ASSUME_TAC THENL
    [MATCH_MP_TAC RING_PRODUCT_LMUL THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [],
     ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_pow f x (CARD(s:A->bool)) = ring_1 (f:A ring)")
      (fun th => ASM_MESON_TAC [th]) THEN MP_TAC (← ISPECL [← q r"f:A ring",
                    ← q r"ring_product f s (\y:A. y)",
                    ← q r"ring_pow f (x:A) (CARD(s:A->bool))", ← q r"ring_1 (f:A ring)"]
                   INTEGRAL_DOMAIN_MUL_RCANCEL) THEN
    ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, RING_POW, RING_1,
                 RING_MUL_LID, RING_PRODUCT] THEN ASM_MESON_TAC []))

  /- Helper: The quotient F[x]/(p) for irreducible p of degree d over a
     finite field F with q elements is a finite field with q^d elements -/
  let QUOTIENT_POLY_RING_FINITE_CARD ← prove
   r"!f:A ring p. field f /\ FINITE(ring_carrier f) /\
     ring_irreducible (poly_ring f (:1)) p
     ==> field(quotient_ring (poly_ring f (:1))
                (ideal_generated (poly_ring f (:1)) {p})) /\
         FINITE(ring_carrier(quotient_ring (poly_ring f (:1))
                (ideal_generated (poly_ring f (:1)) {p}))) /\
         CARD(ring_carrier(quotient_ring (poly_ring f (:1))
                (ideal_generated (poly_ring f (:1)) {p}))) =
         CARD(ring_carrier f) EXP (poly_deg f p)"
   (← do
    let t1 ← TAUT (← q r"~p /\ ~q ==> (p <=> q)")
    let a1 ← ARITH_RULE (← q r"b <= c ==> a <= b ==> a <= c")
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"(p:(1->num)->A) IN ring_carrier(poly_ring f (:1))")
      ASSUME_TAC THENL [ASM_MESON_TAC [ring_irreducible], ALL_TAC] THEN
    ABBREV_TAC (← q r"R = poly_ring (f:A ring) (:1)") THEN
    ABBREV_TAC (← q r"J = ideal_generated R {p:(1->num)->A}") THEN
    ABBREV_TAC (← q r"K = quotient_ring R (J:((1->num)->A)->bool)") THEN
    ABBREV_TAC (← q r"h:A->((1->num)->A)->bool =
      ring_coset R J o poly_const (f:A ring)") THEN
    ABBREV_TAC (← q r"a:((1->num)->A)->bool =
      ring_coset R J (poly_var (f:A ring) one)") THEN
    SUBGOAL_THEN (← q r"PID (R:((1->num)->A)ring)") ASSUME_TAC THENL
    [EXPAND_TAC "R" THEN ASM_MESON_TAC [PID_POLY_RING], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"maximal_ideal R (J:((1->num)->A)->bool) /\
                  ring_ideal R (J:((1->num)->A)->bool)") STRIP_ASSUME_TAC THENL
    [EXPAND_TAC "J" THEN
     ASM_MESON_TAC [RING_IRREDUCIBLE_EQ_MAXIMAL_IDEAL, MAXIMAL_IMP_RING_IDEAL],
     ALL_TAC] THEN
    SUBGOAL_THEN (← q r"field (K:(((1->num)->A)->bool)ring)") ASSUME_TAC THENL
    [EXPAND_TAC "K" THEN ASM_MESON_TAC [FIELD_QUOTIENT_RING], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"field_extension (f:A ring, K:(((1->num)->A)->bool)ring)
      (h:A->((1->num)->A)->bool)") ASSUME_TAC THENL
    [EXPAND_TAC "K" THEN EXPAND_TAC "h" THEN EXPAND_TAC "J" THEN
     EXPAND_TAC "R" THEN MATCH_MP_TAC KRONECKER_FIELD_EXTENSION THEN
     CONJ_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
     ASM_MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_homomorphism
      (R:((1->num)->A)ring, K:(((1->num)->A)->bool)ring)
      (ring_coset R (J:((1->num)->A)->bool))") ASSUME_TAC THENL
    [EXPAND_TAC "K" THEN ASM_MESON_TAC [RING_HOMOMORPHISM_RING_COSET],
     ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_homomorphism (f:A ring, K:(((1->num)->A)->bool)ring)
      (h:A->((1->num)->A)->bool)") ASSUME_TAC THENL
    [ASM_MESON_TAC [field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM],
     ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(a:((1->num)->A)->bool) IN ring_carrier K") ASSUME_TAC THENL
    [SUBGOAL_THEN (← q r"poly_var (f:A ring) one IN ring_carrier R") ASSUME_TAC THENL
     [EXPAND_TAC "R" THEN REWRITE_TAC [POLY_VAR_UNIV], ALL_TAC] THEN
     ASM_MESON_TAC [ring_homomorphism, IN_IMAGE, SUBSET], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!g. g IN ring_carrier R
           ==> poly_extend (f:A ring,K:(((1->num)->A)->bool)ring) h (\v:1. a) g =
               ring_coset R (J:((1->num)->A)->bool) g") ASSUME_TAC THENL
    [X_GEN_TAC (← q r"g:(1->num)->A") THEN DISCH_TAC THEN
     MP_TAC (← ISPECL [← q r"f:A ring", ← q r"K:(((1->num)->A)->bool)ring",
       ← q r"(:1)", ← q r"h:A->((1->num)->A)->bool", ← q r"(\v:1. a:((1->num)->A)->bool)",
       ← q r"ring_coset R (J:((1->num)->A)->bool)",
       ← q r"g:(1->num)->A"] POLY_EXTEND_UNIQUE) THEN
     ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
     CONJ_TAC THENL [X_GEN_TAC (← q r"c:A") THEN DISCH_TAC THEN EXPAND_TAC "h" THEN
      REWRITE_TAC [o_THM], X_GEN_TAC (← q r"i:1") THEN REWRITE_TAC [IN_UNIV] THEN
      SUBGOAL_THEN (← q r"i:1 = one") SUBST1_TAC THENL [MESON_TAC [one], ALL_TAC] THEN
      EXPAND_TAC "a" THEN REFL_TAC], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"p:(1->num)->A IN J") ASSUME_TAC THENL
    [EXPAND_TAC "J" THEN REWRITE_TAC [IN_IDEAL_GENERATED_SELF] THEN
     ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_coset R (J:((1->num)->A)->bool) (p:(1->num)->A) =
       ring_0 (K:(((1->num)->A)->bool)ring)") ASSUME_TAC THENL
    [EXPAND_TAC "K" THEN ASM_SIMP_TAC [QUOTIENT_RING_0] THEN
     ASM_MESON_TAC [RING_COSET_EQ_IDEAL], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"algebraic_over (f:A ring,K:(((1->num)->A)->bool)ring)
        (h:A->((1->num)->A)->bool) (a:((1->num)->A)->bool)") ASSUME_TAC THENL
    [REWRITE_TAC [algebraic_over] THEN
     CONJ_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
     EXISTS_TAC (← q r"p:(1->num)->A") THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [ASM_MESON_TAC [ring_irreducible, POLY_RING_CLAUSES], ALL_TAC] THEN
     SUBGOAL_THEN (← q r"poly_extend (f:A ring,K:(((1->num)->A)->bool)ring)
         h (\v:1. a) p = ring_coset R (J:((1->num)->A)->bool) p")
       SUBST1_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN
     ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"subring_generated K ((a:((1->num)->A)->bool) INSERT
          IMAGE (h:A->((1->num)->A)->bool) (ring_carrier f)) = K")
      ASSUME_TAC THENL [REWRITE_TAC [SUBRING_GENERATED_SUPERSET] THEN
     MP_TAC (← ISPECL [← q r"h:A->((1->num)->A)->bool", ← q r"f:A ring",
       ← q r"K:(((1->num)->A)->bool)ring", ← q r"a:((1->num)->A)->bool"]
       IMAGE_POLY_EXTEND_1) THEN ASM_REWRITE_TAC [] THEN
     DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← GSYM th])) THEN
     SUBGOAL_THEN (← q r"ring_carrier(K:(((1->num)->A)->bool)ring) =
        {ring_coset R (J:((1->num)->A)->bool) x |x| x IN ring_carrier R}")
       SUBST1_TAC THENL
     [EXPAND_TAC "K" THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER], ALL_TAC] THEN
     REWRITE_TAC [SUBSET, FORALL_IN_GSPEC, IN_IMAGE] THEN
     X_GEN_TAC (← q r"g:(1->num)->A") THEN DISCH_TAC THEN
     EXISTS_TAC (← q r"g:(1->num)->A") THEN ASM_SIMP_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"finite_extension (f:A ring, K:(((1->num)->A)->bool)ring)
      (h:A->((1->num)->A)->bool)") ASSUME_TAC THENL
    [MP_TAC (← ISPECL [← q r"h:A->((1->num)->A)->bool",
       ← q r"f:A ring", ← q r"K:(((1->num)->A)->bool)ring", ← q r"a:((1->num)->A)->bool"]
       FINITE_SIMPLE_ALGEBRAIC_EXTENSION) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [FINITE_EXTENSION_BASIS]) THEN
    DISCH_THEN (CONJUNCTS_THEN2 (fun _ => ALL_TAC)
      (X_CHOOSE_THEN (← q r"b:(((1->num)->A)->bool)->bool") STRIP_ASSUME_TAC)) THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"h:A->((1->num)->A)->bool",
      ← q r"f:A ring", ← q r"K:(((1->num)->A)->bool)ring", ← q r"b:(((1->num)->A)->bool)->bool"]
      HAS_SIZE_FINITE_EXTENSION) THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [HAS_SIZE] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (fun th => REWRITE_TAC [th])) THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q r"CARD (b:(((1->num)->A)->bool)->bool) =
                  poly_deg (f:A ring) (p:(1->num)->A)")
      (fun th => REWRITE_TAC [th]) THEN
    ABBREV_TAC (← q r"d = poly_deg (f:A ring) (p:(1->num)->A)") THEN
    REWRITE_TAC [← GSYM LE_ANTISYM] THEN CONJ_TAC THENL
    [
     SUBGOAL_THEN (← q r"~(p:(1->num)->A = ring_0 R)") ASSUME_TAC THENL
     [ASM_MESON_TAC [ring_irreducible], ALL_TAC] THEN
     SUBGOAL_THEN (← q r"poly_extend (f:A ring,K:(((1->num)->A)->bool)ring)
       h (\v:1. a) p = ring_0 K") ASSUME_TAC THENL
     [SUBGOAL_THEN (← q r"poly_extend (f:A ring,K:(((1->num)->A)->bool)ring)
       h (\v:1. a) (p:(1->num)->A) = ring_coset R J p") SUBST1_TAC THENL
      [ASM_SIMP_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
     SUBGOAL_THEN (← q r"ring_independent (f:A ring,K:(((1->num)->A)->bool)ring)
       (h:A->((1->num)->A)->bool) (b:(((1->num)->A)->bool)->bool)")
       ASSUME_TAC THENL [ASM_MESON_TAC [ring_basis], ALL_TAC] THEN
     SUBGOAL_THEN (← q r"(b:(((1->num)->A)->bool)->bool) SUBSET
       ring_carrier (K:(((1->num)->A)->bool)ring)") ASSUME_TAC THENL
     [ASM_MESON_TAC [ring_independent], ALL_TAC] THEN
     MP_TAC (← ISPECL [← q r"h:A->((1->num)->A)->bool", ← q r"f:A ring",
       ← q r"K:(((1->num)->A)->bool)ring", ← q r"p:(1->num)->A",
       ← q r"a:((1->num)->A)->bool"] RING_SIMPLE_ALGEBRAIC_EXTENSION_SPAN) THEN
     ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
     MP_TAC (← ISPECL [← q r"h:A->((1->num)->A)->bool", ← q r"f:A ring",
       ← q r"K:(((1->num)->A)->bool)ring", ← q r"b:(((1->num)->A)->bool)->bool",
       ← q r"{ring_pow (K:(((1->num)->A)->bool)ring)
                  (a:((1->num)->A)->bool) n | n < d}"]
       RING_INDEPENDENT_LE_SPAN) THEN ANTS_TAC THENL [REPEAT CONJ_TAC THENL
      [ASM_REWRITE_TAC [], ASM_REWRITE_TAC [],
       REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN
       X_GEN_TAC (← q r"n:num") THEN DISCH_TAC THEN
       MATCH_MP_TAC RING_POW THEN ASM_REWRITE_TAC [],
       ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
       MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC [FINITE_NUMSEG_LT],
       ASM_REWRITE_TAC [],
       SUBGOAL_THEN (← q r"ring_span (f:A ring,K:(((1->num)->A)->bool)ring)
          (h:A->((1->num)->A)->bool)
          {ring_pow K (a:((1->num)->A)->bool) n | n < d} =
         ring_carrier (K:(((1->num)->A)->bool)ring)")
         (fun th => REWRITE_TAC [th]) THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC []], ALL_TAC] THEN
     DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← CONJUNCT2 th))) THEN
     MATCH_MP_TAC a1 THEN
     ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
     TRANS_TAC LE_TRANS (← q r"CARD {n:num | n < d}") THEN CONJ_TAC THENL
     [MATCH_MP_TAC CARD_IMAGE_LE THEN REWRITE_TAC [FINITE_NUMSEG_LT],
      REWRITE_TAC [CARD_NUMSEG_LT, LE_REFL]],
     SUBGOAL_THEN (← q r"ring_span (f:A ring,K:(((1->num)->A)->bool)ring)
       (h:A->((1->num)->A)->bool) (b:(((1->num)->A)->bool)->bool) =
       ring_carrier K") ASSUME_TAC THENL
     [ASM_MESON_TAC [ring_basis, ring_spanning], ALL_TAC] THEN
     SUBGOAL_THEN (← q r"(b:(((1->num)->A)->bool)->bool) SUBSET
       ring_carrier (K:(((1->num)->A)->bool)ring)") ASSUME_TAC THENL
     [ASM_MESON_TAC [ring_basis, ring_independent], ALL_TAC] THEN
     MP_TAC (← ISPECL [← q r"h:A->((1->num)->A)->bool", ← q r"f:A ring",
       ← q r"K:(((1->num)->A)->bool)ring", ← q r"a:((1->num)->A)->bool",
       ← q r"b:(((1->num)->A)->bool)->bool", ← q r"CARD (b:(((1->num)->A)->bool)->bool)"]
       FINITE_IMP_ALGEBRAIC_EXTENSION_EXPLICIT) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC [HAS_SIZE, SUBSET_REFL], ALL_TAC] THEN
     DISCH_THEN (X_CHOOSE_THEN (← q r"q:(1->num)->A") STRIP_ASSUME_TAC) THEN
     SUBGOAL_THEN (← q r"(q:(1->num)->A) IN ring_carrier R") ASSUME_TAC THENL
     [ASM_MESON_TAC [], ALL_TAC] THEN
     SUBGOAL_THEN (← q r"ring_coset R (J:((1->num)->A)->bool) (q:(1->num)->A) =
       ring_0 (K:(((1->num)->A)->bool)ring)") ASSUME_TAC THENL
     [FIRST_X_ASSUM (fun th => tactic_of do
       pure (MP_TAC (← SPEC (← q r"q:(1->num)->A") th))) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC [], ALL_TAC] THEN
     SUBGOAL_THEN (← q r"(q:(1->num)->A) IN J") ASSUME_TAC THENL
     [SUBGOAL_THEN (← q r"ring_kernel(R,K) (ring_coset R (J:((1->num)->A)->bool)) = J")
        (SUBST1_TAC o SYM) THENL
      [EXPAND_TAC "K" THEN ASM_MESON_TAC [RING_KERNEL_RING_COSET], ALL_TAC] THEN
      REWRITE_TAC [ring_kernel, IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN
     SUBGOAL_THEN (← q r"ring_divides R (p:(1->num)->A) q") ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q r"R:((1->num)->A)ring", ← q r"p:(1->num)->A",
        ← q r"q:(1->num)->A"] IN_IDEAL_GENERATED_SING_EQ) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (fun th => tactic_of do pure (ASM_REWRITE_TAC [← GSYM th])), ALL_TAC] THEN
     TRANS_TAC LE_TRANS (← q r"poly_deg (f:A ring) (q:(1->num)->A)") THEN
     CONJ_TAC THENL [EXPAND_TAC "d" THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [ring_divides]) THEN
      EXPAND_TAC "R" THEN
      REWRITE_TAC [POLY_RING_CLAUSES, SUBSET_UNIV, IN_ELIM_THM] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (X_CHOOSE_THEN (← q r"s:(1->num)->A") STRIP_ASSUME_TAC))) THEN
      SUBGOAL_THEN (← q r"poly_deg (f:A ring) (q:(1->num)->A) =
        poly_deg f (p:(1->num)->A) + poly_deg f (s:(1->num)->A)") MP_TAC THENL
      [SUBGOAL_THEN (← q r"(q:(1->num)->A) = poly_mul (f:A ring) p s") SUBST1_TAC THENL
       [ASM_REWRITE_TAC [], ALL_TAC] THEN MATCH_MP_TAC POLY_DEG_MUL THEN
       ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN] THEN
       SUBGOAL_THEN (← q r"poly_0 (f:A ring) = ring_0 (R:((1->num)->A)ring)")
         (fun th => REWRITE_TAC [th]) THENL
       [EXPAND_TAC "R" THEN REWRITE_TAC [POLY_RING_CLAUSES], ALL_TAC] THEN
       MATCH_MP_TAC t1 THEN
       FIRST_X_ASSUM (STRIP_ASSUME_TAC o
         GEN_REWRITE_RULE I [ring_irreducible]) THEN
       CONJ_TAC THENL [ASM_REWRITE_TAC [],
        DISCH_TAC THEN
        SUBGOAL_THEN (← q r"ring_mul (R:((1->num)->A)ring) (p:(1->num)->A)
          (ring_0 R) = ring_0 R") ASSUME_TAC THENL
        [MATCH_MP_TAC RING_MUL_RZERO THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
        SUBGOAL_THEN (← q r"poly_mul (f:A ring) (p:(1->num)->A)
          (ring_0 (R:((1->num)->A)ring)) =
          ring_mul R p (ring_0 R)") ASSUME_TAC THENL
        [EXPAND_TAC "R" THEN REWRITE_TAC [POLY_RING_CLAUSES], ALL_TAC] THEN
        ASM_MESON_TAC []], ALL_TAC] THEN EXPAND_TAC "d" THEN ARITH_TAC,
      ASM_REWRITE_TAC []]]))

  -- @@RETURN BEGIN
  return { FIELD_NONZERO_PRODUCT_PERMUTE, FINITE_FIELD_ELEMENT_POW,
           QUOTIENT_POLY_RING_FINITE_CARD }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Irreducibility and the polynomial x^(q^n) - x.  (rabin_test.ml 366-527)   -/
/- ------------------------------------------------------------------------- -/

structure IrreducibleDivides where
  -- @@FIELDS
  IRREDUCIBLE_DIVIDES_XQ_MINUS_X_GEN : thm
  IRREDUCIBLE_DIVIDES_XQ_MINUS_X : thm
  FINITE_FIELD_POW_ITERATE : thm
  RING_ENDOMORPHISM_FROBENIUS_ITERATE : thm
  deriving Inhabited

@[nospecialize]
def setupIrreducibleDivides [HolBase] (D : RabinTestDeps) (BGeneralLemmas : GeneralLemmas) (BFiniteFieldFrobenius : FiniteFieldFrobenius) :
    ExceptT String IO IrreducibleDivides := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, .. } := D
  let { CARD_CLAUSES, CARD_SUBSET, EMPTY_SUBSET, EXP, EXP_EQ_0, EXP_EXP,
        FIELD_IMP_INTEGRAL_DOMAIN, FIELD_NONTRIVIAL, FINITE_EMPTY, FINITE_INSERT,
        INSERT_SUBSET, INTEGRAL_DOMAIN_POLY_RING, IN_ELIM_THM,
        IN_IDEAL_GENERATED_SING_EQ, IN_IMAGE, IN_INSERT, MAXIMAL_IMP_RING_IDEAL,
        MULT_CLAUSES, MULT_SYM, .. } := D.core1
  let { NOT_IN_EMPTY, PID_POLY_RING, POLY_VAR_UNIV, RING_0, RING_1, RING_DIVIDES_0,
        RING_ENDOMORPHISM_EQ, RING_ENDOMORPHISM_FROBENIUS, RING_HOMOMORPHISM_COMPOSE,
        RING_HOMOMORPHISM_ID, RING_HOMOMORPHISM_POW, RING_HOMOMORPHISM_RING_COSET,
        RING_HOMOMORPHISM_SUB, RING_IRREDUCIBLE_EQ_MAXIMAL_IDEAL,
        RING_KERNEL_RING_COSET, RING_POW, RING_POW_1, RING_POW_MUL, RING_POW_POW, .. } := D.core2
  let { RING_SUB, RING_SUB_REFL, SUBSET, TRIVIAL_RING_10, divides, o_THM,
        ring_endomorphism, ring_homomorphism, ring_irreducible, ring_kernel, .. } := D.core3
  let { RING_DIVIDES_POW_ITERATE, .. } := BGeneralLemmas
  let { FINITE_FIELD_ELEMENT_POW, QUOTIENT_POLY_RING_FINITE_CARD, .. } := BFiniteFieldFrobenius
  -- @@SCOPE END

  -- Generalized: irreducible p with deg(p) | n implies p | x^(q^n) - x
  let IRREDUCIBLE_DIVIDES_XQ_MINUS_X_GEN ← prove
   r"!f:A ring p n. field f /\ FINITE(ring_carrier f) /\
     ring_irreducible (poly_ring f (:1)) p /\ (poly_deg f p) divides n
     ==> ring_divides (poly_ring f (:1)) p (ring_sub (poly_ring f (:1))
              (ring_pow (poly_ring f (:1)) (poly_var f one)
                        (CARD(ring_carrier f) EXP n))
              (poly_var f one))"
   (← do
    let a1 ← ARITH_RULE (← q r"1 <= n <=> ~(n = 0)")
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"(p:(1->num)->A) IN ring_carrier(poly_ring f (:1))")
      ASSUME_TAC THENL [ASM_MESON_TAC [ring_irreducible], ALL_TAC] THEN
    ABBREV_TAC (← q r"R = poly_ring (f:A ring) (:1)") THEN
    ABBREV_TAC (← q r"J = ideal_generated R {p:(1->num)->A}") THEN
    ABBREV_TAC (← q r"K = quotient_ring R (J:((1->num)->A)->bool)") THEN
    SUBGOAL_THEN (← q r"PID (R:((1->num)->A)ring)") ASSUME_TAC THENL
    [EXPAND_TAC "R" THEN ASM_MESON_TAC [PID_POLY_RING], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"maximal_ideal R (J:((1->num)->A)->bool) /\
                  ring_ideal R (J:((1->num)->A)->bool)") STRIP_ASSUME_TAC THENL
    [EXPAND_TAC "J" THEN
     ASM_MESON_TAC [RING_IRREDUCIBLE_EQ_MAXIMAL_IDEAL, MAXIMAL_IMP_RING_IDEAL],
     ALL_TAC] THEN
    SUBGOAL_THEN
      (← q r"field (K:(((1->num)->A)->bool) ring) /\ FINITE(ring_carrier K) /\
       CARD(ring_carrier K) =
       CARD(ring_carrier(f:A ring)) EXP (poly_deg f (p:(1->num)->A))")
      STRIP_ASSUME_TAC THENL
    [MP_TAC (← ISPECL [← q r"f:A ring", ← q r"p:(1->num)->A"] QUOTIENT_POLY_RING_FINITE_CARD) THEN
     ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_homomorphism(R,K)
                    (ring_coset R (J:((1->num)->A)->bool))") ASSUME_TAC THENL
    [EXPAND_TAC "K" THEN ASM_MESON_TAC [RING_HOMOMORPHISM_RING_COSET],
     ALL_TAC] THEN
    SUBGOAL_THEN (← q r"poly_var f one IN ring_carrier(R:((1->num)->A)ring)")
      ASSUME_TAC THENL
    [EXPAND_TAC "R" THEN REWRITE_TAC [POLY_VAR_UNIV], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_coset R (J:((1->num)->A)->bool)
         (poly_var (f:A ring) one) IN ring_carrier K") ASSUME_TAC THENL
    [ASM_MESON_TAC [ring_homomorphism, IN_IMAGE, SUBSET], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_pow K
         (ring_coset R (J:((1->num)->A)->bool) (poly_var (f:A ring) one))
         (CARD(ring_carrier(f:A ring)) EXP (poly_deg f (p:(1->num)->A))) =
       ring_coset R J (poly_var f one)") ASSUME_TAC THENL [SUBGOAL_THEN
       (← q r"CARD(ring_carrier(f:A ring)) EXP (poly_deg f (p:(1->num)->A)) =
        CARD(ring_carrier(K:(((1->num)->A)->bool) ring))")
       SUBST1_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
     MP_TAC (← ISPEC (← q r"K:(((1->num)->A)->bool) ring") FINITE_FIELD_ELEMENT_POW) THEN
     ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o SPEC
       (← q r"ring_coset R (J:((1->num)->A)->bool) (poly_var (f:A ring) one)")) THEN
     ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_coset R (J:((1->num)->A)->bool) (ring_sub R
            (ring_pow R (poly_var f one) (CARD(ring_carrier(f:A ring)) EXP
                (poly_deg f (p:(1->num)->A)))) (poly_var f one)) =
       ring_0 (K:(((1->num)->A)->bool) ring)") ASSUME_TAC THENL
    [ FIRST_ASSUM (fun hom => tactic_of do
       let t ← MATCH_MP RING_HOMOMORPHISM_SUB hom
       pure (MP_TAC t)) THEN DISCH_THEN (fun th => tactic_of do
       let t ← SPECL [← q r"ring_pow R (poly_var f one)
          (CARD(ring_carrier(f:A ring)) EXP
           (poly_deg f (p:(1->num)->A)))", ← q r"poly_var (f:A ring) one"] th
       pure (MP_TAC t)) THEN
     ASM_SIMP_TAC [RING_POW] THEN DISCH_THEN SUBST1_TAC THEN
     FIRST_ASSUM (fun hom => tactic_of do
       let t ← MATCH_MP RING_HOMOMORPHISM_POW hom
       pure (MP_TAC t)) THEN DISCH_THEN (fun th => tactic_of do
       let t ← SPECL [← q r"poly_var (f:A ring) one", ← q r"CARD(ring_carrier(f:A ring)) EXP
          (poly_deg f (p:(1->num)->A))"] th
       pure (MP_TAC t)) THEN
     ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
     ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [RING_SUB_REFL], ALL_TAC] THEN
    SUBGOAL_THEN
      (← q r"ring_sub R (ring_pow R (poly_var f one) (CARD(ring_carrier(f:A ring)) EXP
             (poly_deg f (p:(1->num)->A))))
         (poly_var (f:A ring) one) IN J") ASSUME_TAC THENL [SUBGOAL_THEN
       (← q r"ring_kernel(R,K) (ring_coset R (J:((1->num)->A)->bool)) = J")
       (SUBST1_TAC o SYM) THENL
     [EXPAND_TAC "K" THEN ASM_MESON_TAC [RING_KERNEL_RING_COSET], ALL_TAC] THEN
     REWRITE_TAC [ring_kernel, IN_ELIM_THM] THEN
     CONJ_TAC THENL [ASM_MESON_TAC [RING_SUB, RING_POW],
      ASM_REWRITE_TAC []], ALL_TAC] THEN
    SUBGOAL_THEN
      (← q r"ring_divides R (p:(1->num)->A) (ring_sub R (ring_pow R (poly_var f one)
               (CARD(ring_carrier(f:A ring)) EXP (poly_deg f (p:(1->num)->A))))
            (poly_var f one))") ASSUME_TAC THENL
    [MP_TAC (← ISPECL [← q r"R:((1->num)->A)ring", ← q r"p:(1->num)->A",
       ← q r"ring_sub R (ring_pow R (poly_var f one) (CARD(ring_carrier(f:A ring)) EXP
             (poly_deg f (p:(1->num)->A))))
         (poly_var (f:A ring) one)"] IN_IDEAL_GENERATED_SING_EQ) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
     DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← GSYM th])) THEN
     ASM_REWRITE_TAC [], ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [divides]) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"k:num")) THEN ASM_CASES_TAC (← q r"k = 0") THENL
    [
     SUBGOAL_THEN (← q r"n = 0") SUBST_ALL_TAC THENL
     [ASM_REWRITE_TAC [MULT_CLAUSES], ALL_TAC] THEN REWRITE_TAC [EXP] THEN
     SUBGOAL_THEN (← q r"ring_sub R (ring_pow R (poly_var (f:A ring) one) 1)
          (poly_var f one) = ring_0 R") SUBST1_TAC THENL
     [ASM_SIMP_TAC [RING_POW_1] THEN ASM_MESON_TAC [RING_SUB_REFL], ALL_TAC] THEN
     REWRITE_TAC [RING_DIVIDES_0] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"CARD(ring_carrier(f:A ring)) EXP n =
       (CARD(ring_carrier f) EXP (poly_deg f (p:(1->num)->A))) EXP k")
      SUBST1_TAC THENL
    [REWRITE_TAC [EXP_EXP] THEN AP_TERM_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"R:((1->num)->A)ring",
       ← q r"p:(1->num)->A", ← q r"poly_var (f:A ring) one",
       ← q r"CARD(ring_carrier(f:A ring)) EXP poly_deg f (p:(1->num)->A)",
       ← q r"k:num"] RING_DIVIDES_POW_ITERATE) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
    [ASM_MESON_TAC [FIELD_IMP_INTEGRAL_DOMAIN, INTEGRAL_DOMAIN_POLY_RING],
     ALL_TAC] THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q r"2 <= CARD(ring_carrier(f:A ring))") ASSUME_TAC THENL
    [SUBGOAL_THEN (← q r"~(ring_1 (f:A ring) = ring_0 f)") ASSUME_TAC THENL
     [MP_TAC (← ISPEC (← q r"f:A ring") FIELD_NONTRIVIAL) THEN
      ASM_REWRITE_TAC [TRIVIAL_RING_10], ALL_TAC] THEN
     MP_TAC (← ISPECL [← q r"{ring_0 f, ring_1 (f:A ring)}", ← q r"ring_carrier(f:A ring)"]
       CARD_SUBSET) THEN ASM_REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY,
                      INSERT_SUBSET, EMPTY_SUBSET, RING_0, RING_1] THEN
     SIMP_TAC [CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY,
              IN_INSERT, NOT_IN_EMPTY] THEN
     ASM_REWRITE_TAC [] THEN ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [a1, EXP_EQ_0] THEN ASM_ARITH_TAC))

  -- Special case: p | x^(q^(deg p)) - x
  let IRREDUCIBLE_DIVIDES_XQ_MINUS_X ← prove
   r"!f:A ring p. field f /\ FINITE(ring_carrier f) /\
     ring_irreducible (poly_ring f (:1)) p
     ==> ring_divides (poly_ring f (:1)) p (ring_sub (poly_ring f (:1))
              (ring_pow (poly_ring f (:1)) (poly_var f one)
                        (CARD(ring_carrier f) EXP (poly_deg f p)))
              (poly_var f one))"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:A ring", ← q r"p:(1->num)->A", ← q r"poly_deg f (p:(1->num)->A)"]
      IRREDUCIBLE_DIVIDES_XQ_MINUS_X_GEN) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN MATCH_MP_TAC THEN MESON_TAC [divides, MULT_CLAUSES])

  -- Helper: x^(q^r) = x for elements of GF(q), for any r
  let FINITE_FIELD_POW_ITERATE ← prove
   r"!f:A ring x r. field f /\ FINITE(ring_carrier f) /\ x IN ring_carrier f
       ==> ring_pow f x (CARD(ring_carrier f) EXP r) = x"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL [SIMP_TAC [EXP, RING_POW_1],
     STRIP_TAC THEN REWRITE_TAC [EXP] THEN
     ASM_SIMP_TAC [RING_POW_MUL, FINITE_FIELD_ELEMENT_POW] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []])

  -- Helper: iterated Frobenius x -> x^(p^k) is a ring endomorphism
  let RING_ENDOMORPHISM_FROBENIUS_ITERATE ← prove
   r"!r:A ring k. prime(ring_char r)
       ==> ring_endomorphism r (\x. ring_pow r x (ring_char r EXP k))"
   (GEN_TAC THEN INDUCT_TAC THENL [
     DISCH_TAC THEN REWRITE_TAC [EXP] THEN MP_TAC (← ISPECL [← q r"r:A ring", ← q r"\x:A. x",
                     ← q r"\x:A. ring_pow r x 1"] RING_ENDOMORPHISM_EQ) THEN
     SIMP_TAC [ring_endomorphism, RING_HOMOMORPHISM_ID, RING_POW_1],
     DISCH_TAC THEN SUBGOAL_THEN
       (← q r"ring_endomorphism (r:A ring) ((\x. ring_pow r x (ring_char r)) o
          (\x. ring_pow r x (ring_char r EXP k)))") ASSUME_TAC THENL
     [REWRITE_TAC [ring_endomorphism] THEN
      MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC (← q r"r:A ring") THEN
      REWRITE_TAC [← GSYM ring_endomorphism] THEN
      CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
       ASM_SIMP_TAC [RING_ENDOMORPHISM_FROBENIUS]], ALL_TAC] THEN
     MP_TAC (← ISPECL [← q r"r:A ring", ← q r"(\x:A. ring_pow r x (ring_char r)) o
        (\x. ring_pow r x (ring_char r EXP k))",
       ← q r"\x:A. ring_pow r x (ring_char r EXP (SUC k))"]
       RING_ENDOMORPHISM_EQ) THEN ASM_REWRITE_TAC [] THEN
     DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN
     REWRITE_TAC [o_THM, EXP] THEN ONCE_REWRITE_TAC [MULT_SYM] THEN
     ASM_SIMP_TAC [RING_POW_POW]])

  -- @@RETURN BEGIN
  return { IRREDUCIBLE_DIVIDES_XQ_MINUS_X_GEN, IRREDUCIBLE_DIVIDES_XQ_MINUS_X,
           FINITE_FIELD_POW_ITERATE, RING_ENDOMORPHISM_FROBENIUS_ITERATE }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Root bounds and the degree bound.  (rabin_test.ml 528-769)                -/
/- ------------------------------------------------------------------------- -/

structure DegreeBound where
  -- @@FIELDS
  FIELD_ROOTS_BOUND : thm
  FINITE_FIELD_CARD_CHAR_POWER : thm
  IRREDUCIBLE_DIVIDES_DEGREE_BOUND : thm
  deriving Inhabited

@[nospecialize]
def setupDegreeBound [HolBase] (D : RabinTestDeps) (BFiniteFieldFrobenius : FiniteFieldFrobenius) (BIrreducibleDivides : IrreducibleDivides) :
    ExceptT String IO DegreeBound := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, ASM_MESON_TAC, SET_TAC, .. } := D
  let { CARD_SUBSET, DIVIDES_PRIME_PRIME, EXP_1, EXP_EXP, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_NONTRIVIAL, FINITE_INTEGRAL_DOMAIN_CHAR, FINITE_INTEGRAL_DOMAIN_SIZE,
        FORALL_IN_INSERT, IN_ELIM_THM, IN_IDEAL_GENERATED_SING, IN_UNIV, LE_EXP,
        LE_TRANS, MAXIMAL_IMP_RING_IDEAL, .. } := D.core1
  let { NOT_IN_EMPTY, PID_POLY_RING, POLY_CONST, POLY_DEG_SUB_LE, POLY_DEG_VAR,
        POLY_DEG_VAR_POW, POLY_EVAL_POW, POLY_EVAL_SUB, POLY_EVAL_VAR,
        POLY_RING_CLAUSES, POLY_ROOT_BOUND, POLY_VAR_UNIV, PRIME_DIVEXP, PRIME_GE_2,
        RING_CHAR_DIVIDES_ORDER, RING_CHAR_DIVIDES_PRIME, RING_CHAR_HOMOMORPHIC_IMAGE,
        RING_CHAR_MONOMORPHIC_IMAGE, RING_COSET_EQ, RING_EPIMORPHISM_RING_COSET,
        RING_HOMOMORPHISMS_EQ_FROM_POLY_RING, RING_HOMOMORPHISM_COMPOSE,
        RING_HOMOMORPHISM_POLY_CONST, RING_HOMOMORPHISM_POW,
        RING_HOMOMORPHISM_RING_COSET, RING_IRREDUCIBLE_EQ_MAXIMAL_IDEAL,
        RING_MONOMORPHISM_POLY_CONST, RING_POLYNOMIAL_POW, RING_POLYNOMIAL_VAR,
        RING_POW, .. } := D.core2
  let { RING_SUB, RING_SUB_EQ_0, SUBSET, TRIVIAL_RING_10, UNIV_1, o_THM,
        ring_endomorphism, ring_epimorphism, ring_irreducible, .. } := D.core3
  let { QUOTIENT_POLY_RING_FINITE_CARD, .. } := BFiniteFieldFrobenius
  let { FINITE_FIELD_POW_ITERATE, RING_ENDOMORPHISM_FROBENIUS_ITERATE, .. } := BIrreducibleDivides
  -- @@SCOPE END

  -- Helper: in a field, if every element satisfies x^n = x, then |field| <= n
  let FIELD_ROOTS_BOUND ← prove
   r"!r:A ring n. field r /\ FINITE(ring_carrier r) /\ 2 <= n /\
       (!a. a IN ring_carrier r ==> ring_pow r a n = a)
       ==> CARD(ring_carrier r) <= n"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"~(ring_1 r:A = ring_0 r)") ASSUME_TAC THENL
    [ASM_MESON_TAC [FIELD_NONTRIVIAL, TRIVIAL_RING_10], ALL_TAC] THEN
    ABBREV_TAC (← q r"P = poly_ring (r:A ring) (:1)") THEN ABBREV_TAC (← q r"g = ring_sub P
      (ring_pow P (poly_var r one) n) (poly_var (r:A ring) one)") THEN
    SUBGOAL_THEN (← q r"(g:(1->num)->A) IN ring_carrier P") ASSUME_TAC THENL
    [EXPAND_TAC "g" THEN EXPAND_TAC "P" THEN
     SIMP_TAC [RING_SUB, RING_POW, POLY_VAR_UNIV], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"~(g:(1->num)->A = ring_0 P)") ASSUME_TAC THENL [DISCH_TAC THEN
     SUBGOAL_THEN (← q r"ring_pow P (poly_var r one:(1->num)->A) n =
                    poly_var r one") MP_TAC THENL
     [SUBGOAL_THEN (← q r"ring_sub P (ring_pow P (poly_var r one:(1->num)->A) n)
                      (poly_var r one) = ring_0 P") MP_TAC THENL
      [ASM_MESON_TAC [], ALL_TAC] THEN EXPAND_TAC "P" THEN
      SIMP_TAC [RING_SUB_EQ_0, RING_POW, POLY_VAR_UNIV], ALL_TAC] THEN
     DISCH_THEN (MP_TAC o AP_TERM (← q r"poly_deg (r:A ring):((1->num)->A)->num")) THEN
     EXPAND_TAC "P" THEN REWRITE_TAC [POLY_DEG_VAR_POW, POLY_DEG_VAR] THEN
     ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC, ALL_TAC] THEN
    SUBGOAL_THEN (← q r"poly_deg r (g:(1->num)->A) <= n") ASSUME_TAC THENL
    [EXPAND_TAC "g" THEN EXPAND_TAC "P" THEN
     MP_TAC (← ISPECL [← q r"r:A ring", ← q r"ring_pow (poly_ring r (:1))
       (poly_var r one:(1->num)->A) n", ← q r"poly_var (r:A ring) one"]
       POLY_DEG_SUB_LE) THEN ANTS_TAC THENL
     [REWRITE_TAC [POLY_RING_CLAUSES, RING_POLYNOMIAL_VAR, IN_UNIV] THEN
      MATCH_MP_TAC RING_POLYNOMIAL_POW THEN
      REWRITE_TAC [RING_POLYNOMIAL_VAR, IN_UNIV], ALL_TAC] THEN
     REWRITE_TAC [POLY_RING_CLAUSES, POLY_DEG_VAR_POW, POLY_DEG_VAR] THEN
     ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC, ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_carrier r SUBSET
      {x:A | x IN ring_carrier r /\ poly_eval r g x = ring_0 r}") ASSUME_TAC THENL
    [REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC (← q r"a:A") THEN
     DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
     EXPAND_TAC "g" THEN EXPAND_TAC "P" THEN REWRITE_TAC [POLY_RING_CLAUSES] THEN
     ASM_SIMP_TAC [POLY_EVAL_SUB, RING_POLYNOMIAL_VAR, IN_UNIV,
       RING_POLYNOMIAL_POW, POLY_EVAL_POW, POLY_EVAL_VAR] THEN
     ASM_SIMP_TAC [RING_SUB_EQ_0, RING_POW], ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"r:A ring", ← q r"g:(1->num)->A"] POLY_ROOT_BOUND) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN] THEN
     EXPAND_TAC "P" THEN ASM_REWRITE_TAC [], ALL_TAC] THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"ring_carrier r:A->bool",
      ← q r"{x:A | x IN ring_carrier r /\ poly_eval r g x = ring_0 r}"]
      CARD_SUBSET) THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC)

  -- Helper: CARD(ring_carrier f) = ring_char(f)^e for some e >= 1
  let FINITE_FIELD_CARD_CHAR_POWER ← prove
   r"!f:A ring. field f /\ FINITE(ring_carrier f)
     ==> ?e. ~(e = 0) /\ CARD(ring_carrier f) = ring_char f EXP e"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"prime(ring_char(f:A ring))") ASSUME_TAC THENL
    [MATCH_MP_TAC FINITE_INTEGRAL_DOMAIN_CHAR THEN
     ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN], ALL_TAC] THEN
    MP_TAC (← ISPEC (← q r"f:A ring") FINITE_INTEGRAL_DOMAIN_SIZE) THEN
    ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"pp:num")
      (X_CHOOSE_THEN (← q r"ee:num") STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC (← q r"ee:num") THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q r"(pp:num) = ring_char(f:A ring)") (fun th => ASM_REWRITE_TAC [th]) THEN
    MP_TAC (← ISPEC (← q r"f:A ring") RING_CHAR_DIVIDES_ORDER) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th => tactic_of do
      let t ← MATCH_MP PRIME_DIVEXP
        (← CONJ (← ASSUME (← q r"prime(ring_char(f:A ring))")) th)
      pure (MP_TAC t)) THEN
    ASM_SIMP_TAC [DIVIDES_PRIME_PRIME])

  -- Degree bound: if p | x^(q^n) - x with n >= 1, then deg(p) <= n
  let IRREDUCIBLE_DIVIDES_DEGREE_BOUND ← prove
   r"!f:A ring p n. field f /\ FINITE(ring_carrier f) /\
     ring_irreducible (poly_ring f (:1)) p /\ ring_divides (poly_ring f (:1)) p
       (ring_sub (poly_ring f (:1)) (ring_pow (poly_ring f (:1)) (poly_var f one)
                    (CARD(ring_carrier f) EXP n)) (poly_var f one)) /\
     1 <= n ==> poly_deg f p <= n"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"(p:(1->num)->A) IN ring_carrier(poly_ring f (:1))")
      ASSUME_TAC THENL [ASM_MESON_TAC [ring_irreducible], ALL_TAC] THEN
    ABBREV_TAC (← q r"R = poly_ring (f:A ring) (:1)") THEN
    ABBREV_TAC (← q r"q = CARD(ring_carrier(f:A ring))") THEN
    ABBREV_TAC (← q r"d = poly_deg f (p:(1->num)->A)") THEN
    ABBREV_TAC (← q r"J = ideal_generated R {p:(1->num)->A}") THEN
    ABBREV_TAC (← q r"K = quotient_ring R (J:((1->num)->A)->bool)") THEN
    SUBGOAL_THEN (← q r"PID (R:((1->num)->A)ring)") ASSUME_TAC THENL
    [EXPAND_TAC "R" THEN ASM_MESON_TAC [PID_POLY_RING], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"maximal_ideal R (J:((1->num)->A)->bool) /\
                  ring_ideal R (J:((1->num)->A)->bool)") STRIP_ASSUME_TAC THENL
    [EXPAND_TAC "J" THEN
     ASM_MESON_TAC [RING_IRREDUCIBLE_EQ_MAXIMAL_IDEAL, MAXIMAL_IMP_RING_IDEAL],
     ALL_TAC] THEN SUBGOAL_THEN
      (← q r"field (K:(((1->num)->A)->bool) ring) /\ FINITE(ring_carrier K) /\
       CARD(ring_carrier K) =
       CARD(ring_carrier(f:A ring)) EXP (poly_deg f (p:(1->num)->A))")
      STRIP_ASSUME_TAC THENL
    [MP_TAC (← ISPECL [← q r"f:A ring", ← q r"p:(1->num)->A"] QUOTIENT_POLY_RING_FINITE_CARD)
     THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"CARD(ring_carrier(K:(((1->num)->A)->bool) ring)) = q EXP d")
      ASSUME_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"prime(ring_char(f:A ring))") ASSUME_TAC THENL
    [MATCH_MP_TAC FINITE_INTEGRAL_DOMAIN_CHAR THEN
     ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_homomorphism(R,K)
                    (ring_coset R (J:((1->num)->A)->bool))") ASSUME_TAC THENL
    [EXPAND_TAC "K" THEN ASM_MESON_TAC [RING_HOMOMORPHISM_RING_COSET],
     ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_char(R:((1->num)->A)ring) = ring_char(f:A ring)")
      ASSUME_TAC THENL
    [MP_TAC (← ISPECL [← q r"f:A ring", ← q r"(:1)"] RING_MONOMORPHISM_POLY_CONST) THEN
     EXPAND_TAC "R" THEN
     DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← MATCH_MP RING_CHAR_MONOMORPHIC_IMAGE th))) THEN
     SIMP_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_char(K:(((1->num)->A)->bool) ring) =
                  ring_char(f:A ring)") ASSUME_TAC THENL
    [MP_TAC (← ISPECL [← q r"R:((1->num)->A)ring", ← q r"K:(((1->num)->A)->bool) ring",
       ← q r"ring_coset R (J:((1->num)->A)->bool)"]
       RING_CHAR_HOMOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
     MP_TAC (← ISPECL [← q r"K:(((1->num)->A)->bool) ring",
       ← q r"ring_char(f:A ring)"] RING_CHAR_DIVIDES_PRIME) THEN
     ANTS_TAC THENL [ASM_MESON_TAC [FIELD_IMP_INTEGRAL_DOMAIN], ALL_TAC] THEN
     DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← GSYM th])) THEN
     ASM_MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"?e. ~(e = 0) /\ q = ring_char(f:A ring) EXP e")
      STRIP_ASSUME_TAC THENL
    [MP_TAC (← ISPEC (← q r"f:A ring") FINITE_FIELD_CARD_CHAR_POWER) THEN
     ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"q EXP n = ring_char(K:(((1->num)->A)->bool) ring) EXP (e * n)")
      ASSUME_TAC THENL [ASM_REWRITE_TAC [EXP_EXP], ALL_TAC] THEN
    ABBREV_TAC (← q r"frob = \y:(((1->num)->A)->bool). ring_pow K y (q EXP n)") THEN
    SUBGOAL_THEN (← q r"ring_endomorphism (K:(((1->num)->A)->bool) ring) frob")
      ASSUME_TAC THENL [SUBGOAL_THEN (← q r"frob = (\y:(((1->num)->A)->bool).
       ring_pow K y (ring_char K EXP (e * n)))") SUBST1_TAC THENL
     [EXPAND_TAC "frob" THEN
      REWRITE_TAC [← ASSUME (← q r"q EXP n = ring_char(K:(((1->num)->A)->bool) ring) EXP (e * n)")],
      ALL_TAC] THEN MATCH_MP_TAC RING_ENDOMORPHISM_FROBENIUS_ITERATE THEN
     ASM_REWRITE_TAC [], ALL_TAC] THEN
    ABBREV_TAC (← q r"proj = ring_coset R (J:((1->num)->A)->bool)") THEN
    SUBGOAL_THEN (← q r"ring_epimorphism(R,K)
      (proj:((1->num)->A) -> ((1->num)->A)->bool)") ASSUME_TAC THENL
    [EXPAND_TAC "K" THEN EXPAND_TAC "proj" THEN
     MATCH_MP_TAC RING_EPIMORPHISM_RING_COSET THEN ASM_REWRITE_TAC [],
     ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_homomorphism(R,K)
      ((frob:(((1->num)->A)->bool) -> ((1->num)->A)->bool) o
       (proj:((1->num)->A) -> ((1->num)->A)->bool))") ASSUME_TAC THENL
    [REWRITE_TAC [ring_endomorphism] THEN
     MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN
     EXISTS_TAC (← q r"K:(((1->num)->A)->bool) ring") THEN
     CONJ_TAC THENL [ASM_MESON_TAC [ring_epimorphism], ALL_TAC] THEN
     ASM_REWRITE_TAC [← GSYM ring_endomorphism], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_homomorphism(R,K)
      (proj:((1->num)->A) -> ((1->num)->A)->bool)") ASSUME_TAC THENL
    [ASM_MESON_TAC [ring_epimorphism], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!c:A. c IN ring_carrier f
       ==> ((frob:(((1->num)->A)->bool) -> ((1->num)->A)->bool) o
            (proj:((1->num)->A) -> ((1->num)->A)->bool)) (poly_const f c) =
            proj (poly_const f c)") ASSUME_TAC THENL
    [X_GEN_TAC (← q r"c:A") THEN DISCH_TAC THEN REWRITE_TAC [o_THM] THEN
     SUBGOAL_THEN (← q r"(frob:(((1->num)->A)->bool) -> ((1->num)->A)->bool)
          ((proj:((1->num)->A) -> ((1->num)->A)->bool) (poly_const (f:A ring) c)) =
        ring_pow K (proj (poly_const f c)) (q EXP n)") SUBST1_TAC THENL
     [EXPAND_TAC "frob" THEN REWRITE_TAC [], ALL_TAC] THEN
     SUBGOAL_THEN (← q r"poly_const (f:A ring) c IN ring_carrier (R:((1->num)->A)ring)") ASSUME_TAC THENL
     [EXPAND_TAC "R" THEN REWRITE_TAC [POLY_CONST] THEN
      ASM_REWRITE_TAC [], ALL_TAC] THEN
     FIRST_ASSUM (fun hom => tactic_of do pure (MP_TAC (← MATCH_MP RING_HOMOMORPHISM_POW hom))) THEN
     DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← SPECL [← q r"(poly_const (f:A ring) c):(1->num)->A",
         ← q r"q EXP n"] th))) THEN
     REWRITE_TAC [← ASSUME (← q r"poly_const (f:A ring) c IN ring_carrier (R:((1->num)->A)ring)")] THEN
     DISCH_THEN (SUBST1_TAC o SYM) THEN
     MP_TAC (← ISPECL [← q r"f:A ring", ← q r"(:1)"] RING_HOMOMORPHISM_POLY_CONST) THEN
     EXPAND_TAC "R" THEN
     DISCH_THEN (fun hom => tactic_of do pure (MP_TAC (← MATCH_MP RING_HOMOMORPHISM_POW hom))) THEN
     DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← SPECL [← q r"c:A", ← q r"q EXP n"] th))) THEN
     REWRITE_TAC [← ASSUME (← q r"(c:A) IN ring_carrier (f:A ring)")] THEN
     DISCH_THEN (SUBST1_TAC o SYM) THEN
     AP_TERM_TAC THEN AP_TERM_TAC THEN
     REWRITE_TAC [← GSYM (← ASSUME (← q r"CARD(ring_carrier(f:A ring)) = q"))] THEN
     MATCH_MP_TAC FINITE_FIELD_POW_ITERATE THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"((frob:(((1->num)->A)->bool) -> ((1->num)->A)->bool) o
       (proj:((1->num)->A) -> ((1->num)->A)->bool))
        (poly_var (f:A ring) one) = proj (poly_var f one)") ASSUME_TAC THENL
    [REWRITE_TAC [o_THM] THEN
     SUBGOAL_THEN (← q r"(frob:(((1->num)->A)->bool) -> ((1->num)->A)->bool)
          ((proj:((1->num)->A) -> ((1->num)->A)->bool) (poly_var (f:A ring) one)) =
        ring_pow K (proj (poly_var f one)) (q EXP n)") SUBST1_TAC THENL
     [EXPAND_TAC "frob" THEN REWRITE_TAC [], ALL_TAC] THEN
     SUBGOAL_THEN (← q r"poly_var (f:A ring) one IN ring_carrier (R:((1->num)->A)ring)")
       ASSUME_TAC THENL
     [EXPAND_TAC "R" THEN REWRITE_TAC [POLY_VAR_UNIV], ALL_TAC] THEN
     FIRST_ASSUM (fun hom => tactic_of do let t ← MATCH_MP RING_HOMOMORPHISM_POW hom; pure (MP_TAC t)) THEN
     DISCH_THEN (fun th => tactic_of do
       let t ← SPECL [← q r"poly_var (f:A ring) one", ← q r"q EXP n"] th
       pure (MP_TAC t)) THEN
     REWRITE_TAC [← ASSUME (← q r"poly_var (f:A ring) one IN ring_carrier (R:((1->num)->A)ring)")] THEN
     DISCH_THEN (SUBST1_TAC o SYM) THEN
     EXPAND_TAC "proj" THEN
     MP_TAC (← ISPECL [← q r"R:((1->num)->A)ring", ← q r"J:((1->num)->A)->bool",
                     ← q r"ring_pow (R:((1->num)->A)ring) (poly_var (f:A ring) one) (q EXP n)",
                     ← q r"poly_var (f:A ring) one"] RING_COSET_EQ) THEN
     ANTS_TAC THENL [ASM_SIMP_TAC [RING_POW], ALL_TAC] THEN
     DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [th])) THEN
     EXPAND_TAC "J" THEN MATCH_MP_TAC IN_IDEAL_GENERATED_SING THEN
     ASM_MESON_TAC [], ALL_TAC] THEN
    MP_TAC (← ISPECL [ ← q r"(frob:(((1->num)->A)->bool) -> ((1->num)->A)->bool) o
       (proj:((1->num)->A) -> ((1->num)->A)->bool)",
      ← q r"proj:((1->num)->A) -> ((1->num)->A)->bool", ← q r"f:A ring",
      ← q r"(:1)", ← q r"K:(((1->num)->A)->bool) ring"
    ] RING_HOMOMORPHISMS_EQ_FROM_POLY_RING) THEN
    REWRITE_TAC [← ASSUME (← q r"poly_ring (f:A ring) (:1) = R")] THEN ANTS_TAC THENL
    [ASM_REWRITE_TAC [UNIV_1, FORALL_IN_INSERT, NOT_IN_EMPTY], ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN (← q r"!y:(((1->num)->A)->bool). y IN ring_carrier K
       ==> ring_pow K y (q EXP n) = y") ASSUME_TAC THENL
    [X_GEN_TAC (← q r"y:(((1->num)->A)->bool)") THEN DISCH_TAC THEN
     SUBGOAL_THEN (← q r"?x:(1->num)->A. x IN ring_carrier R /\
       (proj:((1->num)->A) -> ((1->num)->A)->bool) x = y") STRIP_ASSUME_TAC THENL
     [MP_TAC (← ASSUME (← q r"ring_epimorphism (R:((1->num)->A)ring,
        K:(((1->num)->A)->bool) ring)
        (proj:((1->num)->A) -> ((1->num)->A)->bool)")) THEN
      REWRITE_TAC [ring_epimorphism] THEN ASM SET_TAC [], ALL_TAC] THEN
     FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN SUBGOAL_THEN
       (← q r"ring_pow K ((proj:((1->num)->A) -> ((1->num)->A)->bool) (x:(1->num)->A))
          (q EXP n) =
        ((frob:(((1->num)->A)->bool) -> ((1->num)->A)->bool) o proj) x")
       SUBST1_TAC THENL [EXPAND_TAC "frob" THEN REWRITE_TAC [o_THM], ALL_TAC] THEN
     FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"2 <= q") ASSUME_TAC THENL
    [SUBGOAL_THEN (← q r"2 <= ring_char(f:A ring)") ASSUME_TAC THENL
     [ASM_MESON_TAC [PRIME_GE_2], ALL_TAC] THEN
     MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"ring_char(f:A ring) EXP 1") THEN
     CONJ_TAC THENL [REWRITE_TAC [EXP_1] THEN ASM_ARITH_TAC,
      REWRITE_TAC [← ASSUME (← q r"q = ring_char(f:A ring) EXP e"), LE_EXP] THEN
      COND_CASES_TAC THEN ASM_ARITH_TAC], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"2 <= q EXP n") ASSUME_TAC THENL
    [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"q EXP 1") THEN
     REWRITE_TAC [EXP_1, LE_EXP] THEN
     CONJ_TAC THENL [ASM_ARITH_TAC, COND_CASES_TAC THEN ASM_ARITH_TAC],
     ALL_TAC] THEN
    SUBGOAL_THEN (← q r"CARD(ring_carrier(K:(((1->num)->A)->bool) ring)) <= q EXP n")
      ASSUME_TAC THENL [MP_TAC (← ISPECL [← q r"K:(((1->num)->A)->bool) ring", ← q r"q EXP n"]
      FIELD_ROOTS_BOUND) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"q EXP d <= q EXP n") MP_TAC THENL
    [ASM_MESON_TAC [], ALL_TAC] THEN REWRITE_TAC [LE_EXP] THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC)

  -- @@RETURN BEGIN
  return { FIELD_ROOTS_BOUND, FINITE_FIELD_CARD_CHAR_POWER,
           IRREDUCIBLE_DIVIDES_DEGREE_BOUND }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Converse: if p is monic irreducible of degree d over GF(q) and            -/
/- p divides x^(q^n) - x, then d divides n.                                  -/
/- (rabin_test.ml 777-863)                                                   -/
/- ------------------------------------------------------------------------- -/

structure IrreducibleDividesDegree where
  -- @@FIELDS
  IRREDUCIBLE_DIVIDES_DEGREE : thm
  deriving Inhabited

@[nospecialize]
def setupIrreducibleDividesDegree [HolBase] (D : RabinTestDeps) (BGeneralLemmas : GeneralLemmas) (BIrreducibleDivides : IrreducibleDivides) (BDegreeBound : DegreeBound) :
    ExceptT String IO IrreducibleDividesDegree := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, .. } := D
  let { ADD_SYM, CARD_EQ_0, DIVIDES_0, DIVISION_SIMP, EXP_ADD, EXP_EQ_0,
        FIELD_IMP_INTEGRAL_DOMAIN, INTEGRAL_DOMAIN_POLY_RING, MOD_LT_EQ, .. } := D.core1
  let { POLY_VAR_UNIV, RING_CARRIER_NONEMPTY, RING_POW, RING_POW_POW, .. } := D.core2
  let { divides, ring_irreducible, .. } := D.core3
  let { POLY_NONUNIT_DEGREE_GE_1, RING_DIVIDES_REDUCE, .. } := BGeneralLemmas
  let { IRREDUCIBLE_DIVIDES_XQ_MINUS_X, IRREDUCIBLE_DIVIDES_XQ_MINUS_X_GEN, .. } := BIrreducibleDivides
  let { IRREDUCIBLE_DIVIDES_DEGREE_BOUND, .. } := BDegreeBound
  -- @@SCOPE END

  /- Converse: if p is monic irreducible of degree d over GF(q) and
     p divides x^(q^n) - x, then d divides n.
     Proof: Write n = k*d + r with 0 <= r < d. Show p | x^(q^(k*d))-x
     via IRREDUCIBLE_DIVIDES_XQ_MINUS_X_GEN, let u = x^(q^(k*d)),
     then u^(q^r) = x^(q^n), so p | u^(q^r)-x. By RING_DIVIDES_REDUCE,
     p | x^(q^r)-x. If r > 0, IRREDUCIBLE_DIVIDES_DEGREE_BOUND gives
     d <= r < d, contradiction. So r = 0 and d | n. -/
  let IRREDUCIBLE_DIVIDES_DEGREE ← prove
   r"!f:A ring p n. field f /\ FINITE(ring_carrier f) /\
   ring_irreducible (poly_ring f (:1)) p /\ ring_divides (poly_ring f (:1)) p
     (ring_sub (poly_ring f (:1)) (ring_pow (poly_ring f (:1)) (poly_var f one)
                  (CARD(ring_carrier f) EXP n)) (poly_var f one))
   ==> (poly_deg f p) divides n"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"(p:(1->num)->A) IN ring_carrier(poly_ring f (:1))")
      ASSUME_TAC THENL [ASM_MESON_TAC [ring_irreducible], ALL_TAC] THEN
    ABBREV_TAC (← q r"R = poly_ring (f:A ring) (:1)") THEN
    ABBREV_TAC (← q r"q = CARD(ring_carrier(f:A ring))") THEN
    ABBREV_TAC (← q r"d = poly_deg (f:A ring) (p:(1->num)->A)") THEN
    ABBREV_TAC (← q r"x = poly_var (f:A ring) one") THEN
    ASM_CASES_TAC (← q r"n = 0") THENL [ASM_REWRITE_TAC [DIVIDES_0], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"1 <= d") ASSUME_TAC THENL
    [EXPAND_TAC "d" THEN
     MP_TAC (← ISPECL [← q r"f:A ring", ← q r"p:(1->num)->A", ← q "(:1)"] POLY_NONUNIT_DEGREE_GE_1) THEN
     ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [ring_irreducible],
      REWRITE_TAC []],
     ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(x:(1->num)->A) IN ring_carrier R") ASSUME_TAC THENL
    [EXPAND_TAC "x" THEN EXPAND_TAC "R" THEN
     REWRITE_TAC [POLY_VAR_UNIV], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"integral_domain (R:((1->num)->A)ring)") ASSUME_TAC THENL
    [EXPAND_TAC "R" THEN
     ASM_MESON_TAC [INTEGRAL_DOMAIN_POLY_RING, FIELD_IMP_INTEGRAL_DOMAIN],
     ALL_TAC] THEN
    SUBGOAL_THEN (← q r"~(q = 0)") ASSUME_TAC THENL
    [EXPAND_TAC "q" THEN ASM_MESON_TAC [CARD_EQ_0, RING_CARRIER_NONEMPTY],
     ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_divides R (p:(1->num)->A)
       (ring_sub R (ring_pow R x (q EXP d)) x)") ASSUME_TAC THENL
    [MP_TAC (← ISPECL [← q r"f:A ring", ← q r"p:(1->num)->A"]
      IRREDUCIBLE_DIVIDES_XQ_MINUS_X) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    ABBREV_TAC (← q r"k = n DIV d") THEN ABBREV_TAC (← q r"r = n MOD d") THEN
    SUBGOAL_THEN (← q r"n = k * d + r") ASSUME_TAC THENL
    [MAP_EVERY EXPAND_TAC ["k", "r"] THEN
     MESON_TAC [DIVISION_SIMP, ADD_SYM], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"r < d") ASSUME_TAC THENL
    [EXPAND_TAC "r" THEN REWRITE_TAC [MOD_LT_EQ] THEN ASM_ARITH_TAC, ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_divides R (p:(1->num)->A)
       (ring_sub R (ring_pow R x (q EXP (k * d))) x)") ASSUME_TAC THENL
    [MP_TAC (← ISPECL [← q r"f:A ring", ← q r"p:(1->num)->A", ← q r"k * d"]
      IRREDUCIBLE_DIVIDES_XQ_MINUS_X_GEN) THEN ASM_REWRITE_TAC [] THEN
     DISCH_THEN MATCH_MP_TAC THEN
     REWRITE_TAC [divides] THEN EXISTS_TAC (← q r"k:num") THEN ARITH_TAC, ALL_TAC] THEN
    ABBREV_TAC (← q r"u = ring_pow R (x:(1->num)->A) (q EXP (k * d))") THEN
    SUBGOAL_THEN (← q r"(u:(1->num)->A) IN ring_carrier R") ASSUME_TAC THENL
    [EXPAND_TAC "u" THEN MATCH_MP_TAC RING_POW THEN ASM_REWRITE_TAC [],
     ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_divides R (p:(1->num)->A)
       (ring_sub R (ring_pow R u (q EXP r)) x)") ASSUME_TAC THENL
    [SUBGOAL_THEN (← q r"ring_pow R (u:(1->num)->A) (q EXP r) =
                   ring_pow R x (q EXP n)") SUBST1_TAC THENL [EXPAND_TAC "u" THEN
      MP_TAC (← ISPECL [← q r"R:((1->num)->A)ring", ← q r"x:(1->num)->A",
                      ← q r"q EXP (k * d)", ← q r"q EXP r"] RING_POW_POW) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [← GSYM EXP_ADD] THEN
      AP_TERM_TAC THEN ASM_ARITH_TAC, FIRST_ASSUM ACCEPT_TAC], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"~(q EXP r = 0)") ASSUME_TAC THENL
    [ASM_REWRITE_TAC [EXP_EQ_0], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_divides R (p:(1->num)->A)
       (ring_sub R (ring_pow R x (q EXP r)) x)") ASSUME_TAC THENL
    [MP_TAC (← ISPECL [← q r"R:((1->num)->A)ring", ← q r"p:(1->num)->A",
                     ← q r"u:(1->num)->A", ← q r"x:(1->num)->A", ← q r"q EXP r"]
      RING_DIVIDES_REDUCE) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"r = 0") THENL
    [REWRITE_TAC [divides] THEN EXISTS_TAC (← q r"k:num") THEN ASM_ARITH_TAC,
     ALL_TAC] THEN
     MP_TAC (← ISPECL [← q r"f:A ring", ← q r"p:(1->num)->A", ← q r"r:num"]
      IRREDUCIBLE_DIVIDES_DEGREE_BOUND) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC, ALL_TAC] THEN
    ASM_ARITH_TAC)

  -- @@RETURN BEGIN
  return { IRREDUCIBLE_DIVIDES_DEGREE }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Rabin's Irreducibility Test                                               -/
/-                                                                           -/
/- Let f be a monic polynomial of degree n > 0 over GF(q).                   -/
/- Let n = p1^a1 * ... * pk^ak be the prime factorization of n.              -/
/- Then f is irreducible over GF(q) if and only if:                          -/
/- (1) f divides x^(q^n) - x                                                 -/
/- (2) gcd(f, x^(q^(n/p)) - x) = 1 for each prime divisor p of n             -/
/-                                                                           -/
/- Note: condition (1) is equivalent to saying that all roots of f           -/
/- lie in GF(q^n), and condition (2) says no root lies in a proper subfield. -/
/- (rabin_test.ml 865-1159)                                                  -/
/- ------------------------------------------------------------------------- -/

structure RabinTest where
  -- @@FIELDS
  RABIN_IRREDUCIBILITY_NECESSARY : thm
  RABIN_IRREDUCIBILITY_SUFFICIENT : thm
  RABIN_IRREDUCIBILITY_TEST : thm
  deriving Inhabited

@[nospecialize]
def setupRabinTest [HolBase] (D : RabinTestDeps) (BGeneralLemmas : GeneralLemmas) (BIrreducibleDivides : IrreducibleDivides) (BIrreducibleDividesDegree : IrreducibleDividesDegree) :
    ExceptT String IO RabinTest := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, TAUT, .. } := D
  let { DE_MORGAN_THM, DIVIDES_DIVIDES_DIV, DIVIDES_DIVIDES_DIV_EQ, DIVIDES_DIV_MULT,
        DIVIDES_DIV_SELF, DIVIDES_TRANS, EQ_MULT_LCANCEL, FIELD_IMP_INTEGRAL_DOMAIN,
        INTEGRAL_DOMAIN_POLY_RING, IN_ELIM_THM, MULT_CLAUSES, MULT_EQ_1, MULT_SYM,
        NOETHERIAN_DOMAIN_IRREDUCIBLE_FACTOR_EXISTS, NOT_FORALL_THM, .. } := D.core1
  let { NOT_IMP, PID_IMP_UFD, PID_POLY_RING, POLY_DEG_CONST, POLY_DEG_MUL,
        POLY_RING_CLAUSES, POLY_VAR_UNIV, PRIME_FACTOR, PRIME_GE_2, RING_DIVIDES_TRANS,
        RING_IRREDUCIBLE_DIVIDES_OR_COPRIME, RING_MUL_LZERO, RING_MUL_RZERO, RING_POW, .. } := D.core2
  let { RING_SUB, RING_UNIT_POLY_DOMAIN, divides, ring_coprime, ring_divides,
        ring_irreducible, .. } := D.core3
  let { POLY_NONUNIT_DEGREE_GE_1, .. } := BGeneralLemmas
  let { IRREDUCIBLE_DIVIDES_XQ_MINUS_X, IRREDUCIBLE_DIVIDES_XQ_MINUS_X_GEN, .. } := BIrreducibleDivides
  let { IRREDUCIBLE_DIVIDES_DEGREE, .. } := BIrreducibleDividesDegree
  -- @@SCOPE END

  /- Rabin's Test - forward direction: irreducible implies conditions -/
  let RABIN_IRREDUCIBILITY_NECESSARY ← prove
   r"!f:A ring p n.
   field f /\ FINITE(ring_carrier f) /\
   p IN ring_carrier(poly_ring f (:1)) /\
   poly_deg f p = n /\ ~(n = 0) /\
   ring_irreducible (poly_ring f (:1)) p
   ==> ring_divides (poly_ring f (:1)) p
         (ring_sub (poly_ring f (:1))
            (ring_pow (poly_ring f (:1)) (poly_var f one)
                      (CARD(ring_carrier f) EXP n))
            (poly_var f one)) /\
       !q. prime q /\ q divides n
           ==> ring_coprime (poly_ring f (:1))
                 (p, ring_sub (poly_ring f (:1))
                       (ring_pow (poly_ring f (:1)) (poly_var f one)
                                 (CARD(ring_carrier f) EXP (n DIV q)))
                       (poly_var f one))"
   (← do
    let DIVIDES_DIV_PRIME_ABSURD ← prove
     r"!n q. prime q /\ q divides n /\ ~(n = 0) /\ n divides (n DIV q) ==> F"
     (REPEAT GEN_TAC THEN STRIP_TAC THEN
      SUBGOAL_THEN (← q r"2 <= q /\ ~(q = 0)") STRIP_ASSUME_TAC THENL
      [MP_TAC (← SPEC (← q r"q:num") PRIME_GE_2) THEN ASM_REWRITE_TAC [] THEN ARITH_TAC,
       ALL_TAC] THEN
      SUBGOAL_THEN (← q r"n = (n DIV q) * q") ASSUME_TAC THENL
      [ASM_MESON_TAC [DIVIDES_DIV_MULT], ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [divides]) THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"k:num")) THEN
      SUBGOAL_THEN (← q r"n * (k * q) = n * 1") MP_TAC THENL
      [REWRITE_TAC [MULT_CLAUSES] THEN
       UNDISCH_TAC (← q r"n = (n DIV q) * q") THEN
       ASM_REWRITE_TAC [] THEN ARITH_TAC,
       ALL_TAC] THEN
      REWRITE_TAC [EQ_MULT_LCANCEL] THEN
      ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
      MP_TAC (← SPECL [← q r"k:num", ← q r"q:num"] MULT_EQ_1) THEN
      ASM_ARITH_TAC)
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
    [MP_TAC (← ISPECL [← q r"f:A ring", ← q r"p:(1->num)->A"]
       IRREDUCIBLE_DIVIDES_XQ_MINUS_X) THEN
     ASM_REWRITE_TAC [],
     ALL_TAC] THEN
    X_GEN_TAC (← q r"q':num") THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"poly_ring (f:A ring) (:1)",
                    ← q r"p:(1->num)->A",
                    ← q r"ring_sub (poly_ring (f:A ring) (:1))
                       (ring_pow (poly_ring (f:A ring) (:1))
                                 (poly_var f one)
                                 (CARD(ring_carrier f) EXP (n DIV q')))
                       (poly_var (f:A ring) one)"]
                   RING_IRREDUCIBLE_DIVIDES_OR_COPRIME) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC RING_SUB THEN
     CONJ_TAC THENL [MATCH_MP_TAC RING_POW, ALL_TAC] THEN
     REWRITE_TAC [POLY_VAR_UNIV],
     ALL_TAC] THEN
    DISCH_THEN (DISJ_CASES_TAC) THENL
    [MP_TAC (← ISPECL [← q r"f:A ring", ← q r"p:(1->num)->A", ← q r"n DIV q'"]
       IRREDUCIBLE_DIVIDES_DEGREE) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_TAC THEN
     MP_TAC (← SPECL [← q r"n:num", ← q r"q':num"] DIVIDES_DIV_PRIME_ABSURD) THEN
     ASM_REWRITE_TAC [],
     ASM_REWRITE_TAC []]))

  /- Rabin's Test - backward direction: conditions imply irreducible -/
  let RABIN_IRREDUCIBILITY_SUFFICIENT ← prove
   r"!f:A ring p n.
   field f /\ FINITE(ring_carrier f) /\
   p IN ring_carrier(poly_ring f (:1)) /\
   ~(p = ring_0(poly_ring f (:1))) /\
   poly_deg f p = n /\ ~(n = 0) /\
   ring_divides (poly_ring f (:1)) p
     (ring_sub (poly_ring f (:1))
        (ring_pow (poly_ring f (:1)) (poly_var f one)
                  (CARD(ring_carrier f) EXP n))
        (poly_var f one)) /\
   (!q. prime q /\ q divides n
        ==> ring_coprime (poly_ring f (:1))
              (p, ring_sub (poly_ring f (:1))
                    (ring_pow (poly_ring f (:1)) (poly_var f one)
                              (CARD(ring_carrier f) EXP (n DIV q)))
                    (poly_var f one)))
   ==> ring_irreducible (poly_ring f (:1)) p"
   (← do
    let PROPER_DIVISOR_PRIME_FACTOR ← prove
     r"!d n. d divides n /\ 1 <= d /\ d < n
             ==> ?q. prime q /\ q divides n /\ d divides (n DIV q)"
     (REPEAT GEN_TAC THEN STRIP_TAC THEN
      SUBGOAL_THEN (← q r"~(n DIV d = 1)") ASSUME_TAC THENL
      [DISCH_TAC THEN
       MP_TAC (← SPECL [← q r"d:num", ← q r"n:num"] DIVIDES_DIV_MULT) THEN
       ASM_REWRITE_TAC [MULT_CLAUSES] THEN ASM_ARITH_TAC,
       ALL_TAC] THEN
      MP_TAC (← SPEC (← q r"n DIV d") PRIME_FACTOR) THEN
      ANTS_TAC THENL
      [MP_TAC (← SPECL [← q r"d:num", ← q r"n:num"] DIVIDES_DIV_MULT) THEN
       ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC,
       ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"r:num") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"r:num") THEN
      SUBGOAL_THEN (← q r"(d * r) divides n") ASSUME_TAC THENL
      [ASM_REWRITE_TAC [← GSYM DIVIDES_DIVIDES_DIV_EQ], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"r divides n") ASSUME_TAC THENL
      [ASM_MESON_TAC [DIVIDES_TRANS, DIVIDES_DIV_SELF], ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN
      MP_TAC (← SPECL [← q r"n:num", ← q r"r:num", ← q r"d:num"] DIVIDES_DIVIDES_DIV) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_MESON_TAC [MULT_SYM])
    -- the two TAUTs below print, so bind the later-in-text one (which OCaml,
    -- evaluating right to left, runs first); the earlier one stays inline.
    let loc_t1 ← TAUT (← q r"~(a \/ b) <=> ~a /\ ~b")
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
    ABBREV_TAC (← q r"R = poly_ring (f:A ring) (:1)") THEN
    SUBGOAL_THEN (← q r"integral_domain (R:((1->num)->A)ring)") ASSUME_TAC THENL
    [EXPAND_TAC "R" THEN
     ASM_MESON_TAC [INTEGRAL_DOMAIN_POLY_RING, FIELD_IMP_INTEGRAL_DOMAIN],
     ALL_TAC] THEN
    SUBGOAL_THEN (← q r"~(ring_unit R (p:(1->num)->A))") ASSUME_TAC THENL
    [DISCH_TAC THEN
     MP_TAC (← ISPECL [← q r"f:A ring", ← q "(:1)", ← q r"p:(1->num)->A"]
       RING_UNIT_POLY_DOMAIN) THEN
     ANTS_TAC THENL [ASM_MESON_TAC [FIELD_IMP_INTEGRAL_DOMAIN], ALL_TAC] THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (X_CHOOSE_THEN (← q r"c:A") STRIP_ASSUME_TAC) THEN
     ASM_MESON_TAC [POLY_DEG_CONST],
     ALL_TAC] THEN
    MATCH_MP_TAC (← TAUT (← q r"(~p ==> F) ==> p")) THEN DISCH_TAC THEN
    SUBGOAL_THEN
      (← q r"?a b:(1->num)->A.
         a IN ring_carrier R /\ b IN ring_carrier R /\
         ring_mul R a b = p /\
         ~(ring_unit R a) /\ ~(ring_unit R b)")
      STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC (← q r"~ring_irreducible R (p:(1->num)->A)") THEN
     REWRITE_TAC [ring_irreducible, DE_MORGAN_THM, NOT_FORALL_THM,
                 NOT_IMP] THEN
     ASM_REWRITE_TAC [POLY_RING_CLAUSES] THEN
     REWRITE_TAC [loc_t1] THEN
     STRIP_TAC THEN MAP_EVERY EXISTS_TAC
       [← q r"a:(1->num)->A", ← q r"b:(1->num)->A"] THEN
     ASM_REWRITE_TAC [← GSYM POLY_RING_CLAUSES],
     ALL_TAC] THEN
    SUBGOAL_THEN (← q r"~(a:(1->num)->A = ring_0 R) /\ ~(b:(1->num)->A = ring_0 R)")
      STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC [RING_MUL_LZERO, RING_MUL_RZERO], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_polynomial f (a:(1->num)->A) /\
                  ring_polynomial f (b:(1->num)->A)") STRIP_ASSUME_TAC THENL
    [CONJ_TAC THENL
     [UNDISCH_TAC (← q r"a:(1->num)->A IN ring_carrier R"),
      UNDISCH_TAC (← q r"b:(1->num)->A IN ring_carrier R")] THEN
     EXPAND_TAC "R" THEN REWRITE_TAC [POLY_RING_CLAUSES, IN_ELIM_THM] THEN
     SIMP_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"poly_deg f (poly_mul f (a:(1->num)->A) (b:(1->num)->A)) =
                  poly_deg f a + poly_deg f b") ASSUME_TAC THENL
    [MATCH_MP_TAC POLY_DEG_MUL THEN
     ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN] THEN
     SUBGOAL_THEN (← q r"ring_0 (R:((1->num)->A)ring) = poly_0 (f:A ring)")
       (SUBST1_TAC o SYM) THENL
     [EXPAND_TAC "R" THEN REWRITE_TAC [POLY_RING_CLAUSES], ALL_TAC] THEN
     ASM_REWRITE_TAC [],
     ALL_TAC] THEN
    SUBGOAL_THEN (← q r"poly_deg f (a:(1->num)->A) + poly_deg f (b:(1->num)->A) = n")
      ASSUME_TAC THENL
    [SUBGOAL_THEN (← q r"poly_mul f (a:(1->num)->A) (b:(1->num)->A) = p:(1->num)->A")
       ASSUME_TAC THENL
     [ASM_MESON_TAC [POLY_RING_CLAUSES], ALL_TAC] THEN
     ASM_MESON_TAC [],
     ALL_TAC] THEN
    SUBGOAL_THEN (← q r"1 <= poly_deg f (a:(1->num)->A) /\
                  1 <= poly_deg f (b:(1->num)->A)") STRIP_ASSUME_TAC THENL
    [CONJ_TAC THENL
     [MP_TAC (← ISPECL [← q r"f:A ring", ← q r"a:(1->num)->A", ← q "(:1)"] POLY_NONUNIT_DEGREE_GE_1),
      MP_TAC (← ISPECL [← q r"f:A ring", ← q r"b:(1->num)->A", ← q "(:1)"] POLY_NONUNIT_DEGREE_GE_1)] THEN
     (ANTS_TAC THENL
      [ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [POLY_RING_CLAUSES], SIMP_TAC []]),
     ALL_TAC] THEN
    SUBGOAL_THEN (← q r"poly_deg f (a:(1->num)->A) < n") ASSUME_TAC THENL
    [ASM_ARITH_TAC, ALL_TAC] THEN
    SUBGOAL_THEN (← q r"UFD (R:((1->num)->A)ring)") ASSUME_TAC THENL
    [EXPAND_TAC "R" THEN ASM_MESON_TAC [PID_IMP_UFD, PID_POLY_RING],
     ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"R:((1->num)->A)ring", ← q r"a:(1->num)->A"]
      NOETHERIAN_DOMAIN_IRREDUCIBLE_FACTOR_EXISTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"g:(1->num)->A") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"ring_divides R (g:(1->num)->A) p") ASSUME_TAC THENL
    [MATCH_MP_TAC RING_DIVIDES_TRANS THEN EXISTS_TAC (← q r"a:(1->num)->A") THEN
     ASM_REWRITE_TAC [] THEN
     REWRITE_TAC [ring_divides] THEN ASM_REWRITE_TAC [] THEN
     EXISTS_TAC (← q r"b:(1->num)->A") THEN ASM_REWRITE_TAC [],
     ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_divides R (g:(1->num)->A)
       (ring_sub R (ring_pow R (poly_var f one)
                    (CARD(ring_carrier f) EXP n)) (poly_var f one))")
      ASSUME_TAC THENL
    [MATCH_MP_TAC RING_DIVIDES_TRANS THEN EXISTS_TAC (← q r"p:(1->num)->A") THEN
     ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [POLY_RING_CLAUSES],
     ALL_TAC] THEN
    SUBGOAL_THEN (← q r"g:(1->num)->A IN ring_carrier R") ASSUME_TAC THENL
    [ASM_MESON_TAC [ring_irreducible], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(poly_deg f (g:(1->num)->A)) divides n") ASSUME_TAC THENL
    [MP_TAC (← ISPECL [← q r"f:A ring", ← q r"g:(1->num)->A", ← q r"n:num"]
      IRREDUCIBLE_DIVIDES_DEGREE) THEN
     ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
     ASM_MESON_TAC [POLY_RING_CLAUSES],
     ALL_TAC] THEN
    SUBGOAL_THEN (← q r"1 <= poly_deg f (g:(1->num)->A)") ASSUME_TAC THENL
    [MP_TAC (← ISPECL [← q r"f:A ring", ← q r"g:(1->num)->A", ← q "(:1)"] POLY_NONUNIT_DEGREE_GE_1) THEN
     ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [ring_irreducible, POLY_RING_CLAUSES],
      SIMP_TAC []],
     ALL_TAC] THEN
    SUBGOAL_THEN (← q r"poly_deg f (g:(1->num)->A) <= poly_deg f (a:(1->num)->A)") ASSUME_TAC THENL
    [UNDISCH_TAC (← q r"ring_divides R (g:(1->num)->A) (a:(1->num)->A)") THEN
     REWRITE_TAC [ring_divides] THEN
     DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC
         (X_CHOOSE_THEN (← q r"h:(1->num)->A") STRIP_ASSUME_TAC))) THEN
     SUBGOAL_THEN (← q r"~(h:(1->num)->A = ring_0 R)") ASSUME_TAC THENL
     [ASM_MESON_TAC [RING_MUL_RZERO], ALL_TAC] THEN
     SUBGOAL_THEN (← q r"poly_deg f (a:(1->num)->A) =
                   poly_deg f (g:(1->num)->A) + poly_deg f (h:(1->num)->A)") MP_TAC THENL
     [SUBGOAL_THEN (← q r"poly_deg f (a:(1->num)->A) =
                    poly_deg f (poly_mul f (g:(1->num)->A) (h:(1->num)->A))") SUBST1_TAC THENL
      [AP_TERM_TAC THEN ASM_MESON_TAC [POLY_RING_CLAUSES], ALL_TAC] THEN
      MATCH_MP_TAC POLY_DEG_MUL THEN
      ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN] THEN
      CONJ_TAC THENL
      [UNDISCH_TAC (← q r"g:(1->num)->A IN ring_carrier R") THEN
       EXPAND_TAC "R" THEN REWRITE_TAC [POLY_RING_CLAUSES, IN_ELIM_THM] THEN
       SIMP_TAC [], ALL_TAC] THEN
      CONJ_TAC THENL
      [UNDISCH_TAC (← q r"h:(1->num)->A IN ring_carrier R") THEN
       EXPAND_TAC "R" THEN REWRITE_TAC [POLY_RING_CLAUSES, IN_ELIM_THM] THEN
       SIMP_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"ring_0 (R:((1->num)->A)ring) = poly_0 (f:A ring)")
        (SUBST1_TAC o SYM) THENL
      [EXPAND_TAC "R" THEN REWRITE_TAC [POLY_RING_CLAUSES], ALL_TAC] THEN
      ASM_MESON_TAC [ring_irreducible],
      ARITH_TAC],
     ALL_TAC] THEN
    SUBGOAL_THEN (← q r"poly_deg f (g:(1->num)->A) < n") ASSUME_TAC THENL
    [ASM_ARITH_TAC, ALL_TAC] THEN
    MP_TAC (← SPECL [← q r"poly_deg f (g:(1->num)->A)", ← q r"n:num"]
      PROPER_DIVISOR_PRIME_FACTOR) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"l:num") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"ring_divides R (g:(1->num)->A)
       (ring_sub R (ring_pow R (poly_var f one)
                    (CARD(ring_carrier f) EXP (n DIV l))) (poly_var f one))")
      ASSUME_TAC THENL
    [MP_TAC (← ISPECL [← q r"f:A ring", ← q r"g:(1->num)->A", ← q r"n DIV l"]
      IRREDUCIBLE_DIVIDES_XQ_MINUS_X_GEN) THEN
     ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
     ASM_MESON_TAC [POLY_RING_CLAUSES],
     ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_unit R (g:(1->num)->A)") MP_TAC THENL
    [FIRST_X_ASSUM (MP_TAC o SPEC (← q r"l:num")) THEN ASM_REWRITE_TAC [] THEN
     REWRITE_TAC [ring_coprime] THEN
     DISCH_THEN (MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
     DISCH_THEN (MP_TAC o SPEC (← q r"g:(1->num)->A")) THEN
     ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
     ASM_MESON_TAC [POLY_RING_CLAUSES],
     ALL_TAC] THEN
    ASM_MESON_TAC [ring_irreducible]))

  /- Combined Rabin's Test -/
  let RABIN_IRREDUCIBILITY_TEST ← prove
   r"!f:A ring p n.
   field f /\ FINITE(ring_carrier f) /\
   p IN ring_carrier(poly_ring f (:1)) /\
   ~(p = ring_0(poly_ring f (:1))) /\
   ~(ring_unit (poly_ring f (:1)) p) /\
   poly_deg f p = n /\ ~(n = 0)
   ==> (ring_irreducible (poly_ring f (:1)) p <=>
        ring_divides (poly_ring f (:1)) p
          (ring_sub (poly_ring f (:1))
             (ring_pow (poly_ring f (:1)) (poly_var f one)
                       (CARD(ring_carrier f) EXP n))
             (poly_var f one)) /\
        !q. prime q /\ q divides n
            ==> ring_coprime (poly_ring f (:1))
                  (p, ring_sub (poly_ring f (:1))
                        (ring_pow (poly_ring f (:1)) (poly_var f one)
                                  (CARD(ring_carrier f) EXP (n DIV q)))
                        (poly_var f one)))"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"f:A ring", ← q r"p:(1->num)->A", ← q r"n:num"]
      RABIN_IRREDUCIBILITY_NECESSARY) THEN
    ASM_REWRITE_TAC [],
    STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:A ring", ← q r"p:(1->num)->A", ← q r"n:num"]
      RABIN_IRREDUCIBILITY_SUFFICIENT) THEN
    ASM_REWRITE_TAC []])

  -- @@RETURN BEGIN
  return { RABIN_IRREDUCIBILITY_NECESSARY, RABIN_IRREDUCIBILITY_SUFFICIENT,
           RABIN_IRREDUCIBILITY_TEST }
  -- @@RETURN END

end HolLibrary.RabinTest
