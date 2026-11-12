/- ========================================================================= -/
/- ANT: The ideal norm                                                     -/
/- ========================================================================= -/
/- File: HolANT/IdealNorm.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/ideal_norm.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antidealnormdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/permutations.ml, Library/ring_det.ml, ANT/ideal_arith.ml, Library/products.ml, ANT/algmisc.ml, Library/matroids.ml, Library/fieldtheory.ml, ANT/integral.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.IdealNorm fills them).

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

namespace HolANT.IdealNorm

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (CARD_EQ_0 CARD_EQ_CARD_IMP CARD_EQ_IMAGES CARD_EQ_REFL
   CARD_EQ_RING_IMAGE_KERNEL CARD_EQ_SYM CARD_EQ_TRANS CARD_FINITE_CONG
   CARD_LE_1 CARD_MUL_C CARD_MUL_CONG CARD_MUL_FINITE CARD_MUL_FINITE_EQ
   DEDEKIND_IDEAL_FACTORIZATION DEDEKIND_IDEAL_QUOTIENT_CANCEL
   DEDEKIND_IMP_INTEGRAL_DOMAIN DEDEKIND_IMP_NOETHERIAN
   DEDEKIND_TWO_GENERATORS_STRONG EMPTY_SUBSET EQ_IMP EQ_MULT_LCANCEL ETA_AX EXP
   FIELD_EQ_TRIVIAL_IDEALS FINITE_FUNSPACE FINITE_IMAGE FINITE_IMAGE_INJ_EQ
   FINITE_INDUCT_STRONG FINITE_INTEGRAL_DOMAIN_IMP_FIELD FINITE_SUBSET
   FINITE_SUBSET_IMAGE FORALL_IN_IMAGE FORALL_IN_INSERT FUN_IN_IMAGE HAS_SIZE
   IDEAL_GENERATED_FINITE IDEAL_GENERATED_INC_GEN IDEAL_GENERATED_INSERT
   IDEAL_GENERATED_MINIMAL IDEAL_GENERATED_SING_ALT IDEAL_POW_0
   IDEAL_POW_EQ_ZERO IDEAL_POW_SUC IDEAL_PRODUCT_EMPTY IDEAL_PRODUCT_EQ_ZERO
   IDEAL_PRODUCT_INSERT IDEAL_PROD_CARRIER_LEFT IDEAL_PROD_COMM
   IDEAL_PROD_EQ_ZERO IDEAL_PROD_LZERO IDEAL_PROD_SUBSET_LEFT IMAGE_EQ_EMPTY
   IMP_CONJ INSERT_SUBSET IN_ELIM_THM IN_IMAGE IN_RING_IDEAL_0
   IN_RING_IDEAL_LMUL IN_RING_IDEAL_SUM IN_SING ITERATE_EQ LEFT_AND_EXISTS_THM
   LEFT_IMP_EXISTS_THM LE_REFL MONOIDAL_MUL MONO_EXISTS MULT_CLAUSES
   NOT_EXISTS_THM NOT_IN_EMPTY NPRODUCT_CLAUSES PRIME_1 PRIME_IMP_RING_IDEAL
   PROPER_IDEAL_ALT PSUBSET QUOTIENT_RING_0 QUOTIENT_RING_CARRIER
   QUOTIENT_RING_UNIVERSAL_EPIMORPHISM RIGHT_AND_EXISTS_THM RIGHT_EXISTS_IMP_THM
   RIGHT_FORALL_IMP_THM RING_0 RING_ADD RING_CARRIER_NONEMPTY
   RING_CHAR_DIVIDES_ORDER RING_COSET_EQ RING_COSET_EQ_IDEAL RING_COSET_TRIVIAL
   RING_EPIMORPHISM RING_EPIMORPHISM_RING_COSET RING_HOMOMORPHISM_RING_COSET
   RING_HOMOMORPHISM_RING_OF_NUM RING_IDEAL_0 RING_IDEAL_CARRIER
   RING_IDEAL_IDEAL_POW RING_IDEAL_IDEAL_PROD RING_IDEAL_IDEAL_PRODUCT
   RING_IDEAL_IMP_NONEMPTY RING_IDEAL_IMP_SUBSET RING_IDEAL_QUOTIENT_LMUL
   RING_KERNEL_RING_COSET RING_MUL RING_MUL_IN_IDEAL_PROD RING_OF_NUM
   RING_OF_NUM_EQ_0 RING_SETADD_MONO RING_SUB RING_SUB_RDISTRIB RING_SUB_RZERO
   RING_SUM RING_SUM_SUB SIMPLE_IMAGE SING_SUBSET SKOLEM_THM SUBSET
   SUBSET_ANTISYM SUBSET_REFL TRIVIAL_IMP_FINITE_RING TRIVIAL_QUOTIENT_RING
   TRIVIAL_RING_HAS_SIZE_1 divides finitely_generated_ideal ideal_quotient
   maximal_ideal noetherian_ring nproduct prime proper_ideal ring_kernel
   ring_setadd : thm)
  deriving Inhabited

/-- What ideal_norm.ml uses from Session besides theorems. -/
structure IdealNormDeps where
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
/- ideal_norm.ml phrases from line 47 to 553                              -/
/- ---------------------------------------------------------------------- -/

structure IdealNorm where
  -- @@FIELDS
  ideal_norm : thm
  IDEAL_NORM_CARRIER : thm
  IDEAL_NORM_POS : thm
  IDEAL_NORM_GT_1 : thm
  IDEAL_NORM_IN_IDEAL : thm
  CARD_EQ_QUOTIENT_RING_CHAIN : thm
  FINITE_QUOTIENT_RING_CHAIN : thm
  FINITE_QUOTIENT_RING_MONO : thm
  CARD_QUOTIENT_RING_CHAIN : thm
  IDEAL_NORM_SUBSET_EQ : thm
  IDEAL_NORM_SUBSET_DIVIDES : thm
  FINITE_QUOTIENT_RING_IDEAL_PROD : thm
  FINITE_QUOTIENT_RING_IDEAL_POW : thm
  IDEAL_NORM_PRIME_IMP_MAXIMAL : thm
  CARD_EQ_QUOTIENT_RING_IDEAL_PROD : thm
  IDEAL_NORM_MUL : thm
  IDEAL_NORM_IDEAL_POW : thm
  IDEAL_NORM_PRIME_POWER : thm
  IDEAL_NORM_IDEAL_PRODUCT : thm
  IDEAL_NORM_FACTORIZATION : thm
  DEDEKIND_IDEAL_NORM_PRIME_POWERS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupIdealNorm [HolBase] (D : IdealNormDeps) :
    ExceptT String IO IdealNorm := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC,
        RING_RULE, SET_RULE, SET_TAC, TAUT, new_definition, .. } := D
  let { CARD_EQ_0, CARD_EQ_CARD_IMP, CARD_EQ_IMAGES, CARD_EQ_REFL,
        CARD_EQ_RING_IMAGE_KERNEL, CARD_EQ_SYM, CARD_EQ_TRANS, CARD_FINITE_CONG,
        CARD_LE_1, CARD_MUL_C, CARD_MUL_CONG, CARD_MUL_FINITE, CARD_MUL_FINITE_EQ,
        DEDEKIND_IDEAL_FACTORIZATION, DEDEKIND_IDEAL_QUOTIENT_CANCEL,
        DEDEKIND_IMP_INTEGRAL_DOMAIN, DEDEKIND_IMP_NOETHERIAN,
        DEDEKIND_TWO_GENERATORS_STRONG, EMPTY_SUBSET, EQ_IMP, EQ_MULT_LCANCEL, ETA_AX,
        EXP, FIELD_EQ_TRIVIAL_IDEALS, FINITE_FUNSPACE, FINITE_IMAGE,
        FINITE_IMAGE_INJ_EQ, FINITE_INDUCT_STRONG, FINITE_INTEGRAL_DOMAIN_IMP_FIELD,
        FINITE_SUBSET, FINITE_SUBSET_IMAGE, FORALL_IN_IMAGE, FORALL_IN_INSERT,
        FUN_IN_IMAGE, HAS_SIZE, IDEAL_GENERATED_FINITE, IDEAL_GENERATED_INC_GEN,
        IDEAL_GENERATED_INSERT, IDEAL_GENERATED_MINIMAL, IDEAL_GENERATED_SING_ALT,
        IDEAL_POW_0, IDEAL_POW_EQ_ZERO, IDEAL_POW_SUC, IDEAL_PRODUCT_EMPTY,
        IDEAL_PRODUCT_EQ_ZERO, IDEAL_PRODUCT_INSERT, IDEAL_PROD_CARRIER_LEFT,
        IDEAL_PROD_COMM, IDEAL_PROD_EQ_ZERO, IDEAL_PROD_LZERO, IDEAL_PROD_SUBSET_LEFT,
        IMAGE_EQ_EMPTY, IMP_CONJ, INSERT_SUBSET, IN_ELIM_THM, IN_IMAGE,
        IN_RING_IDEAL_0, IN_RING_IDEAL_LMUL, IN_RING_IDEAL_SUM, IN_SING, ITERATE_EQ,
        LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM, LE_REFL, MONOIDAL_MUL, MONO_EXISTS,
        MULT_CLAUSES, NOT_EXISTS_THM, NOT_IN_EMPTY, NPRODUCT_CLAUSES, PRIME_1,
        PRIME_IMP_RING_IDEAL, PROPER_IDEAL_ALT, PSUBSET, QUOTIENT_RING_0,
        QUOTIENT_RING_CARRIER, QUOTIENT_RING_UNIVERSAL_EPIMORPHISM,
        RIGHT_AND_EXISTS_THM, RIGHT_EXISTS_IMP_THM, RIGHT_FORALL_IMP_THM, RING_0,
        RING_ADD, RING_CARRIER_NONEMPTY, RING_CHAR_DIVIDES_ORDER, RING_COSET_EQ,
        RING_COSET_EQ_IDEAL, RING_COSET_TRIVIAL, RING_EPIMORPHISM,
        RING_EPIMORPHISM_RING_COSET, RING_HOMOMORPHISM_RING_COSET,
        RING_HOMOMORPHISM_RING_OF_NUM, RING_IDEAL_0, RING_IDEAL_CARRIER,
        RING_IDEAL_IDEAL_POW, RING_IDEAL_IDEAL_PROD, RING_IDEAL_IDEAL_PRODUCT,
        RING_IDEAL_IMP_NONEMPTY, RING_IDEAL_IMP_SUBSET, RING_IDEAL_QUOTIENT_LMUL,
        RING_KERNEL_RING_COSET, RING_MUL, RING_MUL_IN_IDEAL_PROD, RING_OF_NUM,
        RING_OF_NUM_EQ_0, RING_SETADD_MONO, RING_SUB, RING_SUB_RDISTRIB,
        RING_SUB_RZERO, RING_SUM, RING_SUM_SUB, SIMPLE_IMAGE, SING_SUBSET, SKOLEM_THM,
        SUBSET, SUBSET_ANTISYM, SUBSET_REFL, TRIVIAL_IMP_FINITE_RING,
        TRIVIAL_QUOTIENT_RING, TRIVIAL_RING_HAS_SIZE_1, divides,
        finitely_generated_ideal, ideal_quotient, maximal_ideal, noetherian_ring,
        nproduct, prime, proper_ideal, ring_kernel, ring_setadd, .. } := D.core1
  -- @@SCOPE END

  let ideal_norm ← new_definition
    r"ideal_norm (r:A ring) j = CARD(ring_carrier(quotient_ring r j))"

  let IDEAL_NORM_CARRIER ← prove
    r"!r:A ring. ideal_norm r (ring_carrier r) = 1"
    (GEN_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ring_carrier r:A->bool")] TRIVIAL_QUOTIENT_RING) THEN REWRITE_TAC [RING_IDEAL_CARRIER, PROPER_IDEAL_ALT] THEN SIMP_TAC [TRIVIAL_RING_HAS_SIZE_1, HAS_SIZE, ideal_norm])

  let IDEAL_NORM_POS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"1 <= n <=> ~(n = 0)")
    prove
      r"!r j:A->bool.
          FINITE(ring_carrier(quotient_ring r j)) ==> 1 <= ideal_norm r j"
      (SIMP_TAC [ideal_norm, r1, CARD_EQ_0, RING_CARRIER_NONEMPTY])

  let IDEAL_NORM_GT_1 ← prove
    r"!r (j:A->bool).
     ring_ideal r j /\ ~(j = ring_carrier r) /\
     FINITE(ring_carrier(quotient_ring r j))
     ==> 1 < ideal_norm r j"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool")] TRIVIAL_QUOTIENT_RING) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool")] IDEAL_NORM_POS) THEN ASM_REWRITE_TAC [PROPER_IDEAL_ALT, TRIVIAL_RING_HAS_SIZE_1, HAS_SIZE] THEN REWRITE_TAC [ideal_norm] THEN ARITH_TAC)

  let IDEAL_NORM_IN_IDEAL ← prove
    r"!r j:A->bool.
     ring_ideal r j /\ FINITE(ring_carrier(quotient_ring r j))
     ==> ring_of_num r (ideal_norm r j) IN j"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"quotient_ring r (j:A->bool)") RING_CHAR_DIVIDES_ORDER) THEN ASM_REWRITE_TAC [(← GSYM RING_OF_NUM_EQ_0), (← GSYM ideal_norm)] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP RING_HOMOMORPHISM_RING_COSET)) THEN DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM (← MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM th))])) THEN ASM_SIMP_TAC [QUOTIENT_RING_0, RING_COSET_EQ_IDEAL, RING_OF_NUM])

  let CARD_EQ_QUOTIENT_RING_CHAIN ← prove
    r"!r j k:A->bool.
        ring_ideal r j /\ ring_ideal r k /\ j SUBSET k
        ==> ring_carrier(quotient_ring r j) =_c
            ring_carrier(quotient_ring r k) *_c IMAGE (ring_coset r j) k"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"quotient_ring r (k:A->bool)"), (← q r"j:A->bool"), (← q r"ring_coset r (k:A->bool)")] QUOTIENT_RING_UNIVERSAL_EPIMORPHISM) THEN ASM_SIMP_TAC [RING_EPIMORPHISM_RING_COSET, RING_KERNEL_RING_COSET] THEN REWRITE_TAC [RING_EPIMORPHISM, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"g:(A->bool)->(A->bool)") THEN STRIP_TAC THEN FIRST_ASSUM (MP_TAC o ((ONCE_REWRITE_RULE [CARD_EQ_SYM]) o (MATCH_MP CARD_EQ_RING_IMAGE_KERNEL))) THEN ASM_SIMP_TAC [ring_kernel, QUOTIENT_RING_CARRIER, QUOTIENT_RING_0] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_TERM_TAC THEN SUBGOAL_THEN (← q r"!x:A. x IN ring_carrier r ==> (g(ring_coset r j x) = k <=> x IN k)") MP_TAC THENL [ASM_SIMP_TAC [RING_COSET_EQ_IDEAL], ALL_TAC] THEN MP_TAC (← MATCH_MP RING_IDEAL_IMP_SUBSET (← ASSUME (← q r"ring_ideal r (k:A->bool)"))) THEN SET_TAC [])

  let FINITE_QUOTIENT_RING_CHAIN ← prove
    r"!r j k:A->bool.
        ring_ideal r j /\ ring_ideal r k /\ j SUBSET k
        ==> (FINITE(ring_carrier(quotient_ring r j)) <=>
             FINITE(ring_carrier(quotient_ring r k)) /\
             FINITE(IMAGE (ring_coset r j) k))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"k:A->bool")] CARD_EQ_QUOTIENT_RING_CHAIN) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o (MATCH_MP CARD_FINITE_CONG)) THEN REWRITE_TAC [CARD_MUL_FINITE_EQ, RING_CARRIER_NONEMPTY, IMAGE_EQ_EMPTY] THEN ASM_MESON_TAC [RING_IDEAL_IMP_NONEMPTY])

  let FINITE_QUOTIENT_RING_MONO ← prove
    r"!r (j:A->bool) k.
     ring_ideal r j /\ ring_ideal r k /\ j SUBSET k /\
     FINITE(ring_carrier(quotient_ring r j))
     ==> FINITE(ring_carrier(quotient_ring r k))"
    (MESON_TAC [FINITE_QUOTIENT_RING_CHAIN])

  let CARD_QUOTIENT_RING_CHAIN ← prove
    r"!r (j:A->bool) k.
     ring_ideal r j /\ ring_ideal r k /\ j SUBSET k /\
     FINITE(ring_carrier(quotient_ring r j))
     ==> CARD(ring_carrier(quotient_ring r j)) =
         CARD(ring_carrier(quotient_ring r k)) *
         CARD(IMAGE (ring_coset r j) k)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"k:A->bool")] FINITE_QUOTIENT_RING_CHAIN) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_SIMP_TAC [(← GSYM CARD_MUL_C)] THEN MATCH_MP_TAC CARD_EQ_CARD_IMP THEN ASM_SIMP_TAC [CARD_MUL_FINITE, CARD_EQ_QUOTIENT_RING_CHAIN])

  let IDEAL_NORM_SUBSET_EQ ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"1 <= n ==> ~(n = 0)")
    let r2 ← ARITH_RULE (← q r"n = n * 1")
    prove
      r"!r j k:A->bool.
          ring_ideal r j /\ ring_ideal r k /\ j SUBSET k /\
          FINITE(ring_carrier(quotient_ring r j))
          ==> (ideal_norm r k = ideal_norm r j <=> k = j)"
      (REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"k:A->bool")] FINITE_QUOTIENT_RING_CHAIN) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"k:A->bool")] CARD_QUOTIENT_RING_CHAIN) THEN ASM_REWRITE_TAC [(← GSYM ideal_norm)] THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:A->bool")] IDEAL_NORM_POS) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [r2] THEN ASM_SIMP_TAC [EQ_MULT_LCANCEL, r1] THEN DISCH_THEN (ASSUME_TAC o SYM) THEN MP_TAC (← ISPEC (← q r"IMAGE (ring_coset r j) (k:A->bool)") CARD_LE_1) THEN ASM_REWRITE_TAC [LE_REFL, SUBSET, FORALL_IN_IMAGE, IN_SING] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"c:A->bool")) THEN SUBGOAL_THEN (← q r"!x:A. x IN k ==> x IN j") MP_TAC THENL [X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_coset r j (x:A) = ring_coset r j (ring_0 r)") MP_TAC THENL [FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP th (← ASSUME (← q r"(x:A) IN k")))])) THEN CONV_TAC SYM_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC [IN_RING_IDEAL_0], ASM_SIMP_TAC [RING_COSET_EQ, RING_0, RING_SUB_RZERO]], ASM SET_TAC []])

  let IDEAL_NORM_SUBSET_DIVIDES ← prove
    r"!r j k:A->bool.
        ring_ideal r j /\ ring_ideal r k /\ j SUBSET k /\
        FINITE(ring_carrier(quotient_ring r j))
        ==> ideal_norm r k divides ideal_norm r j"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [ideal_norm, divides] THEN EXISTS_TAC (← q r"CARD(IMAGE (ring_coset r j) (k:A->bool))") THEN MATCH_MP_TAC CARD_QUOTIENT_RING_CHAIN THEN ASM_REWRITE_TAC [])

  let FINITE_QUOTIENT_RING_IDEAL_PROD ← prove
    r"!r j k:A->bool.
        noetherian_ring r /\ ring_ideal r j /\ ring_ideal r k /\
        FINITE(ring_carrier(quotient_ring r j)) /\
        FINITE(ring_carrier(quotient_ring r k))
        ==> FINITE(ring_carrier(quotient_ring r (ideal_prod r j k)))"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_ideal r (ideal_prod r j k) /\ ideal_prod r j k SUBSET (j:A->bool)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IDEAL_PROD, IDEAL_PROD_SUBSET_LEFT, RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_prod r j k:A->bool"), (← q r"j:A->bool")] FINITE_QUOTIENT_RING_CHAIN) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"ring_coset r (k:A->bool)"), (← q r"ring_carrier r:A->bool"), (← q r"ring_carrier(quotient_ring r (k:A->bool))")] FINITE_SUBSET_IMAGE) THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, SIMPLE_IMAGE, ETA_AX, SUBSET_REFL] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"u:A->bool") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"!a:A. ?y. a IN ring_carrier r ==> y IN u /\ ring_sub r a y IN k") MP_TAC THENL [X_GEN_TAC (← q r"a:A") THEN REWRITE_TAC [RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_coset r k (a:A) IN IMAGE (ring_coset r k) u") MP_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun z1 => (do let z2 ← (do let z3 ← (pure z1); pure (concl z3)); pure (is_eq z2)))))) THEN ASM_SIMP_TAC [FUN_IN_IMAGE], REWRITE_TAC [IN_IMAGE]] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"y:A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:A->bool"), (← q r"a:A"), (← q r"y:A")] RING_COSET_EQ) THEN ANTS_TAC THENL [ASM SET_TAC [], ASM_MESON_TAC []], REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM]] THEN X_GEN_TAC (← q r"d:A->A") THEN DISCH_THEN (LABEL_TAC "d") THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"j:A->bool")) o (GEN_REWRITE_RULE id [noetherian_ring]))) THEN ASM_REWRITE_TAC [finitely_generated_ideal, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"t:A->bool") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!a:A. a IN t ==> a IN j") ASSUME_TAC THENL [EXPAND_TAC "j" THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC IDEAL_GENERATED_INC_GEN THEN ASM SET_TAC [], ALL_TAC] THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"IMAGE (\e. ring_coset r (ideal_prod r j k)
                 (ring_sum r t (\a. ring_mul r (e a) a)))
          {e:A->A | (!a. a IN t ==> e a IN u) /\
                    (!a. ~(a IN t) ==> e a = ring_0 r)}") THEN ASM_SIMP_TAC [FINITE_IMAGE, FINITE_FUNSPACE] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"x:A") THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [(← SYM (← ASSUME (← q r"ideal_generated r t = (j:A->bool)")))] THEN SIMP_TAC [IDEAL_GENERATED_FINITE, (← ASSUME (← q r"FINITE(t:A->bool)")), (← ASSUME (← q r"(t:A->bool) SUBSET ring_carrier r"))] THEN REWRITE_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"c:A->A") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN EXISTS_TAC (← q r"\a:A. if a IN t then (d:A->A)(c a) else ring_0 r") THEN REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"!a:A. a IN t ==> a IN ring_carrier r /\ (d:A->A)(c a) IN ring_carrier r /\
                     (d:A->A)(c a) IN u /\ ring_sub r (c a) (d(c a)) IN k") ASSUME_TAC THENL [X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN USE_THEN "d" (MP_TAC o (SPEC (← q r"(c:A->A) a"))) THEN ASM_SIMP_TAC [] THEN ASM SET_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_prod r j k:A->bool"), (← q r"ring_sum r t (\a. ring_mul r ((c:A->A) a) a)"), (← q r"ring_sum r t (\a. ring_mul r
                    (if a IN t then (d:A->A)((c:A->A) a) else ring_0 r) a)")] RING_COSET_EQ) THEN ASM_REWRITE_TAC [RING_SUM] THEN DISCH_THEN SUBST1_TAC THEN wPart lhand (rand o rand) RING_SUM_SUB THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_MUL, RING_0], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC IN_RING_IDEAL_SUM THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN ASM_SIMP_TAC [(← GSYM RING_SUB_RDISTRIB)] THEN SUBGOAL_THEN (← q r"ideal_prod r j k = ideal_prod r k (j:A->bool)") SUBST1_TAC THENL [ASM_SIMP_TAC [IDEAL_PROD_COMM, RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_PROD THEN ASM_SIMP_TAC [RING_SUB])

  let FINITE_QUOTIENT_RING_IDEAL_POW ← prove
    r"!(a:A ring) j n.
        noetherian_ring a /\ ring_ideal a j /\
        FINITE(ring_carrier(quotient_ring a j))
        ==> FINITE(ring_carrier(quotient_ring a (ideal_pow a j n)))"
    (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL [REWRITE_TAC [IDEAL_POW_0] THEN MATCH_MP_TAC FINITE_QUOTIENT_RING_MONO THEN EXISTS_TAC (← q r"j:A->bool") THEN ASM_SIMP_TAC [RING_IDEAL_CARRIER, RING_IDEAL_IMP_SUBSET], REWRITE_TAC [IDEAL_POW_SUC] THEN MATCH_MP_TAC FINITE_QUOTIENT_RING_IDEAL_PROD THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW]])

  let IDEAL_NORM_PRIME_IMP_MAXIMAL ← prove
    r"!r j:A->bool.
        ring_ideal r j /\ FINITE(ring_carrier(quotient_ring r j)) /\
        prime(ideal_norm r j)
        ==> maximal_ideal r j"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [maximal_ideal, proper_ideal, PSUBSET] THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET] THEN CONJ_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"prime(ideal_norm r (ring_carrier r:A->bool))") THEN REWRITE_TAC [IDEAL_NORM_CARRIER, PRIME_1], REWRITE_TAC [NOT_EXISTS_THM] THEN X_GEN_TAC (← q r"k:A->bool") THEN STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"k:A->bool")] IDEAL_NORM_SUBSET_DIVIDES) THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MP_TAC o (CONJUNCT2 o (GEN_REWRITE_RULE id [prime]))) THEN DISCH_THEN (fun th => DISCH_THEN (DISJ_CASES_TAC o (MATCH_MP th))) THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:A->bool")] IDEAL_NORM_GT_1) THEN ANTS_TAC THENL [ASM_MESON_TAC [FINITE_QUOTIENT_RING_MONO], ASM_ARITH_TAC], MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"k:A->bool")] IDEAL_NORM_SUBSET_EQ) THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC []])

  let CARD_EQ_QUOTIENT_RING_IDEAL_PROD ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let v1 ← GSYM RING_SUB_RDISTRIB
    let q2 ← q r"ring_sub r (ring_add r w (ring_mul r b z)) (ring_mul r z b):A = w"
    let r3 ← RING_RULE q2
    let q4 ← q r"(w:A) IN ring_carrier r"
    let q5 ← q r"z:A"
    let q6 ← q r"z:A"
    let q7 ← q r"u:A"
    let q8 ← q r"w:A"
    let q9 ← q r"y:A"
    let q10 ← q r"y:A"
    let q11 ← q r"IMAGE (ring_coset r l) j =
      IMAGE (\x:A. ring_coset r l (ring_mul r x b)) (ring_carrier r)"
    let q12 ← q r"(b:A) IN ring_carrier r"
    let p13 ← prove r"!r j k l (b:A).
          ring_ideal r j /\ ring_ideal r k /\ ring_ideal r l /\ b IN j /\
          j SUBSET ring_setadd r l (ideal_generated r {b}) /\
          (!x. x IN ring_carrier r ==> (ring_mul r x b IN l <=> x IN k))
          ==> IMAGE (ring_coset r l) j =_c ring_carrier(quotient_ring r k)" (REPEAT STRIP_TAC THEN SUBGOAL_THEN q12 ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN q11 SUBST1_TAC THENL [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_SIMP_TAC [SUBSET, FORALL_IN_IMAGE, FUN_IN_IMAGE, IN_RING_IDEAL_LMUL] THEN X_GEN_TAC q10 THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC q9) o (GEN_REWRITE_RULE id [SUBSET]))) THEN ASM_SIMP_TAC [ring_setadd, IDEAL_GENERATED_SING_ALT, IN_ELIM_THM] THEN REWRITE_TAC [LEFT_AND_EXISTS_THM, RIGHT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM, IN_IMAGE] THEN MAP_EVERY X_GEN_TAC [q8, q7, q6] THEN STRIP_TAC THEN EXISTS_TAC q5 THEN SUBGOAL_THEN q4 ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [RING_COSET_EQ, RING_ADD, RING_MUL, r3], ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, SIMPLE_IMAGE] THEN MATCH_MP_TAC CARD_EQ_IMAGES THEN ASM_SIMP_TAC [RING_COSET_EQ, RING_MUL, v1, RING_SUB]])
    let lemma := p13
    let q14 ← q r"ideal_generated r {a:A,b} = j"
    let v15 ← ASSUME q14
    let v16 ← SYM v15
    let q17 ← q r"ring_carrier r:A->bool"
    let q18 ← q r"!t. s SUBSET {y:A | y IN t /\ P y} ==> !y. y IN s ==> P y"
    let r19 ← SET_RULE q18
    let q20 ← q r"k:A->bool"
    let q21 ← q r"j:A->bool"
    let q22 ← q r"r:A ring"
    let v23 ← ISPECL [q22, q21, q20] IDEAL_PROD_COMM
    let q24 ← q r"j:A->bool"
    let q25 ← q r"k:A->bool"
    let q26 ← q r"r:A ring"
    let v27 ← ISPECL [q26, q25, q24] DEDEKIND_IDEAL_QUOTIENT_CANCEL
    let q28 ← q r"ideal_quotient r (ideal_prod r j k) j = (k:A->bool)"
    let q29 ← q r"x:A"
    let q30 ← q r"ideal_generated r {a:A,b} = j"
    let v31 ← ASSUME q30
    let v32 ← SYM v31
    let q33 ← q r"(a:A) IN ring_carrier r /\ b IN ring_carrier r"
    let q34 ← q r"b:A"
    let q35 ← q r"a:A"
    let q36 ← q r"j:A->bool"
    let q37 ← q r"r:A ring"
    let v38 ← ISPECL [q37, q36, q35] DEDEKIND_TWO_GENERATORS_STRONG
    let q39 ← q r"ideal_prod r j k:A->bool"
    let q40 ← q r"r:A ring"
    let v41 ← ISPECL [q40, q39] IN_RING_IDEAL_0
    let q42 ← q r"k:A->bool"
    let q43 ← q r"j:A->bool"
    let q44 ← q r"r:A ring"
    let v45 ← ISPECL [q44, q43, q42] IDEAL_PROD_EQ_ZERO
    let q46 ← q r"?a:A. a IN ideal_prod r j k /\ ~(a = ring_0 r)"
    let q47 ← q r"ring_carrier(quotient_ring r j) *_c
    IMAGE (ring_coset r (ideal_prod r j k)) (j:A->bool)"
    let q48 ← q r"ring_ideal r (ideal_prod r j k) /\ ideal_prod r j k SUBSET (j:A->bool)"
    prove
      r"!r j k:A->bool.
          dedekind_domain r /\ ring_ideal r j /\ ring_ideal r k /\
          ~(j = {ring_0 r}) /\ ~(k = {ring_0 r})
          ==> ring_carrier(quotient_ring r (ideal_prod r j k)) =_c
              ring_carrier(quotient_ring r j) *_c
              ring_carrier(quotient_ring r k)"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN q48 STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IDEAL_PROD, IDEAL_PROD_SUBSET_LEFT, RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN TRANS_TAC CARD_EQ_TRANS q47 THEN ASM_SIMP_TAC [CARD_EQ_QUOTIENT_RING_CHAIN] THEN MATCH_MP_TAC CARD_MUL_CONG THEN REWRITE_TAC [CARD_EQ_REFL] THEN MATCH_MP_TAC lemma THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN q46 STRIP_ASSUME_TAC THENL [MP_TAC v45 THEN MP_TAC v41 THEN ASM_SIMP_TAC [DEDEKIND_IMP_INTEGRAL_DOMAIN] THEN SET_TAC [], ALL_TAC] THEN MP_TAC v38 THEN ANTS_TAC THENL [ASM SET_TAC [], MATCH_MP_TAC MONO_EXISTS] THEN X_GEN_TAC q34 THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN q33 STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN CONJ_TAC THENL [GEN_REWRITE_TAC LAND_CONV [v32] THEN GEN_REWRITE_TAC LAND_CONV [IDEAL_GENERATED_INSERT] THEN MATCH_MP_TAC RING_SETADD_MONO THEN ASM_SIMP_TAC [SUBSET_REFL, IDEAL_GENERATED_MINIMAL, SING_SUBSET], ALL_TAC] THEN X_GEN_TAC q29 THEN DISCH_TAC THEN SUBGOAL_THEN q28 (fun th => tactic_of do pure (GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [(← SYM th)])) THENL [MP_TAC v27 THEN MP_TAC v23 THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET], ASM_REWRITE_TAC [ideal_quotient, IN_ELIM_THM]] THEN EQ_TAC THENL [DISCH_TAC, DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC []] THEN MATCH_MP_TAC r19 THEN EXISTS_TAC q17 THEN GEN_REWRITE_TAC LAND_CONV [v16] THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_SIMP_TAC [RING_IDEAL_QUOTIENT_LMUL, INSERT_SUBSET, EMPTY_SUBSET, IN_ELIM_THM, IN_RING_IDEAL_LMUL])

  let IDEAL_NORM_MUL ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"FINITE(ring_carrier(quotient_ring r {ring_0 r:A}))"
    let q2 ← q r"field(r:A ring)"
    let p3 ← prove r"!r k:A->bool.
        integral_domain r /\ ring_ideal r k /\ ~(k = {ring_0 r}) /\
        FINITE(ring_carrier(quotient_ring r {ring_0 r}))
        ==> k = ring_carrier r" (REPEAT STRIP_TAC THEN SUBGOAL_THEN q2 MP_TAC THENL [MATCH_MP_TAC FINITE_INTEGRAL_DOMAIN_IMP_FIELD THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC q1 THEN SIMP_TAC [QUOTIENT_RING_CARRIER, RING_IDEAL_0, SIMPLE_IMAGE, ETA_AX] THEN MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN SIMP_TAC [IMP_CONJ, RING_COSET_TRIVIAL] THEN SET_TAC [], REWRITE_TAC [FIELD_EQ_TRIVIAL_IDEALS] THEN ASM_MESON_TAC []])
    let lemma := p3
    let v4 ← GSYM CARD_MUL_C
    let q5 ← q r"j = ring_carrier r:A->bool"
    let q6 ← q r"k = ring_carrier r:A->bool"
    let q7 ← q r"k = {ring_0 r:A}"
    let q8 ← q r"j = {ring_0 r:A}"
    prove
      r"!r j k:A->bool.
       dedekind_domain r /\
       ring_ideal r j /\ ring_ideal r k /\
       (~(j = {ring_0 r}) \/ ~(k = {ring_0 r})) /\
       FINITE(ring_carrier(quotient_ring r j)) /\
       FINITE(ring_carrier(quotient_ring r k))
       ==> ideal_norm r (ideal_prod r j k) =
           ideal_norm r j * ideal_norm r k"
      (REPEAT GEN_TAC THEN ASM_CASES_TAC q8 THEN ASM_CASES_TAC q7 THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THENL [SUBGOAL_THEN q6 SUBST1_TAC THENL [MATCH_MP_TAC lemma THEN ASM_SIMP_TAC [DEDEKIND_IMP_INTEGRAL_DOMAIN], SIMP_TAC [IDEAL_PROD_LZERO, SUBSET_REFL, IDEAL_NORM_CARRIER, MULT_CLAUSES]], SUBGOAL_THEN q5 SUBST1_TAC THENL [MATCH_MP_TAC lemma THEN ASM_SIMP_TAC [DEDEKIND_IMP_INTEGRAL_DOMAIN], SIMP_TAC [IDEAL_PROD_CARRIER_LEFT, RING_IDEAL_0, IDEAL_NORM_CARRIER, MULT_CLAUSES]], ASM_SIMP_TAC [ideal_norm, v4] THEN MATCH_MP_TAC CARD_EQ_CARD_IMP THEN ASM_SIMP_TAC [CARD_MUL_FINITE, CARD_EQ_QUOTIENT_RING_IDEAL_PROD]])

  let IDEAL_NORM_IDEAL_POW ← prove
    r"!r j:A->bool n.
        dedekind_domain r /\ ring_ideal r j /\ ~(j = {ring_0 r}) /\
        FINITE(ring_carrier(quotient_ring r j))
        ==> FINITE(ring_carrier(quotient_ring r (ideal_pow r j n))) /\
            ideal_norm r (ideal_pow r j n) = ideal_norm r j EXP n"
    (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL [REWRITE_TAC [IDEAL_POW_0, IDEAL_NORM_CARRIER, EXP] THEN MATCH_MP_TAC FINITE_QUOTIENT_RING_MONO THEN EXISTS_TAC (← q r"j:A->bool") THEN ASM_SIMP_TAC [RING_IDEAL_CARRIER, RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_ideal r (ideal_pow r j n) /\ ~(ideal_pow r j n = {ring_0 r:A})") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, IDEAL_POW_EQ_ZERO, DEDEKIND_IMP_INTEGRAL_DOMAIN], ASM_SIMP_TAC [IDEAL_POW_SUC, EXP, FINITE_QUOTIENT_RING_IDEAL_PROD, DEDEKIND_IMP_NOETHERIAN, IDEAL_NORM_MUL]])

  let IDEAL_NORM_PRIME_POWER ← prove
    r"!r (p:A->bool) n.
     dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
     FINITE(ring_carrier(quotient_ring r p))
     ==> FINITE(ring_carrier(quotient_ring r (ideal_pow r p (SUC n)))) /\
         ideal_norm r (ideal_pow r p (SUC n)) =
         ideal_norm r p EXP (SUC n)"
    (SIMP_TAC [IDEAL_NORM_IDEAL_POW, PRIME_IMP_RING_IDEAL])

  let IDEAL_NORM_IDEAL_PRODUCT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"~(p /\ q) <=> p ==> ~q")
    prove
      r"!r s (f:K->A->bool).
          dedekind_domain r /\ FINITE s /\
          (!i. i IN s
               ==> ring_ideal r (f i) /\ ~(f i = {ring_0 r}) /\
                   FINITE(ring_carrier(quotient_ring r (f i))))
          ==> FINITE(ring_carrier(quotient_ring r (ideal_product r s f))) /\
              ideal_norm r (ideal_product r s f) =
              nproduct s (\i. ideal_norm r (f i))"
      (GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN SIMP_TAC [IDEAL_PRODUCT_EMPTY, IDEAL_NORM_CARRIER, NPRODUCT_CLAUSES, FORALL_IN_INSERT, NOT_IN_EMPTY] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ring_carrier r:A->bool")] TRIVIAL_QUOTIENT_RING) THEN SIMP_TAC [RING_IDEAL_CARRIER, PROPER_IDEAL_ALT, TRIVIAL_IMP_FINITE_RING], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"a:K"), (← q r"t:K->bool")] THEN STRIP_TAC THEN X_GEN_TAC (← q r"f:K->A->bool") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"f:K->A->bool"))) THEN ASM_SIMP_TAC [IDEAL_PRODUCT_INSERT] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_ideal r (ideal_product r t (f:K->A->bool)) /\
      ~(ideal_product r t f = {ring_0 r})") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IDEAL_PRODUCT, IDEAL_PRODUCT_EQ_ZERO, DEDEKIND_IMP_INTEGRAL_DOMAIN, NOT_EXISTS_THM, r1], ASM_SIMP_TAC [FINITE_QUOTIENT_RING_IDEAL_PROD, DEDEKIND_IMP_NOETHERIAN, IDEAL_NORM_MUL]])

  let IDEAL_NORM_FACTORIZATION ← prove
    r"!r j:A->bool.
     dedekind_domain r /\ ring_ideal r j /\ ~(j = {ring_0 r}) /\
     FINITE(ring_carrier(quotient_ring r j))
     ==> ideal_norm r j =
         nproduct {p | prime_ideal r p /\ ~(p = {ring_0 r}) /\ j SUBSET p}
                  (\p. ideal_norm r p EXP ideal_valuation r p j)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool")] DEDEKIND_IDEAL_FACTORIZATION) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"s = {p | prime_ideal r p /\ ~(p = {ring_0 r}) /\ (j:A->bool) SUBSET p}") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!p:A->bool. p IN s ==> prime_ideal r p /\ ~(p = {ring_0 r}) /\
                           FINITE(ring_carrier(quotient_ring r p))") ASSUME_TAC THENL [EXPAND_TAC "s" THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"p:A->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC FINITE_QUOTIENT_RING_MONO THEN EXISTS_TAC (← q r"j:A->bool") THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:(A->bool)->bool"), (← q r"\p:A->bool. ideal_pow r p (ideal_valuation r p j)")] IDEAL_NORM_IDEAL_PRODUCT) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, PRIME_IMP_RING_IDEAL, IDEAL_POW_EQ_ZERO, DEDEKIND_IMP_INTEGRAL_DOMAIN, IDEAL_NORM_IDEAL_POW], ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [nproduct] THEN MATCH_MP_TAC (← MATCH_MP ITERATE_EQ MONOIDAL_MUL) THEN ASM_SIMP_TAC [IDEAL_NORM_IDEAL_POW, PRIME_IMP_RING_IDEAL])

  let DEDEKIND_IDEAL_NORM_PRIME_POWERS ← prove
    r"!r t (e:(A->bool)->num).
        dedekind_domain r /\ FINITE t /\
        (!P. P IN t ==> prime_ideal r P /\ ~(P = {ring_0 r}) /\
                        FINITE(ring_carrier(quotient_ring r P)))
        ==> FINITE(ring_carrier(quotient_ring r
                     (ideal_product r t (\P. ideal_pow r P (e P))))) /\
            ideal_norm r (ideal_product r t (\P. ideal_pow r P (e P))) =
            nproduct t (\P. ideal_norm r P EXP e P)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN)) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"t:(A->bool)->bool"), (← q r"\P:A->bool. ideal_pow r P (e P)")] IDEAL_NORM_IDEAL_PRODUCT) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, IDEAL_POW_EQ_ZERO, PRIME_IMP_RING_IDEAL, IDEAL_NORM_IDEAL_POW] THEN ANTS_TAC THENL [ALL_TAC, SIMP_TAC []] THEN ASM_MESON_TAC [IDEAL_NORM_IDEAL_POW, PRIME_IMP_RING_IDEAL])

  -- @@RETURN BEGIN
  return { ideal_norm, IDEAL_NORM_CARRIER, IDEAL_NORM_POS, IDEAL_NORM_GT_1,
           IDEAL_NORM_IN_IDEAL, CARD_EQ_QUOTIENT_RING_CHAIN, FINITE_QUOTIENT_RING_CHAIN,
           FINITE_QUOTIENT_RING_MONO, CARD_QUOTIENT_RING_CHAIN, IDEAL_NORM_SUBSET_EQ,
           IDEAL_NORM_SUBSET_DIVIDES, FINITE_QUOTIENT_RING_IDEAL_PROD,
           FINITE_QUOTIENT_RING_IDEAL_POW, IDEAL_NORM_PRIME_IMP_MAXIMAL,
           CARD_EQ_QUOTIENT_RING_IDEAL_PROD, IDEAL_NORM_MUL, IDEAL_NORM_IDEAL_POW,
           IDEAL_NORM_PRIME_POWER, IDEAL_NORM_IDEAL_PRODUCT, IDEAL_NORM_FACTORIZATION,
           DEDEKIND_IDEAL_NORM_PRIME_POWERS }
  -- @@RETURN END

end HolANT.IdealNorm
