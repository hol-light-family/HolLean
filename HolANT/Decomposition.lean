/- ========================================================================= -/
/- ANT: Decomposition and inertia groups and Frobenius elements of a ...   -/
/- ========================================================================= -/
/- File: HolANT/Decomposition.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/decomposition.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antdecompositiondiff; the rest is by hand.  Its `needs` closure is
  Library/frag.ml, Library/wo.ml, Library/card.ml, Library/prime.ml, Library/grouptheory.ml, Library/matroids.ml, Library/binomial.ml, Library/iter.ml, Library/pocklington.ml, Library/ringtheory.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/symmetric_group.ml, Library/galois.ml, Library/ring_groups.ml, Library/finite_fields.ml, ANT/ideal_arith.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.Decomposition fills them).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left; where a proof applies rules that print or use
  counters (MESON, ARITH_RULE, ...) they are bound first, in OCaml's order.
-/

import HolANT.Prelude
import HolLibrary.Frag
import HolLibrary.Wo
import HolLibrary.Card
import HolLibrary.Prime
import HolLibrary.GroupTheory
import HolLibrary.Matroids
import HolLibrary.Binomial
import HolLibrary.Iter
import HolLibrary.Pocklington
import HolLibrary.RingTheory
import HolLibrary.Permutations
import HolLibrary.RingDet
import HolLibrary.FieldTheory
import HolLibrary.SymmetricGroup
import HolLibrary.Galois
import HolLibrary.RingGroups
import HolLibrary.FiniteFields
import HolANT.IdealArith

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.IdealArith

namespace HolANT.Decomposition

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (CARD_EQ_0 CARD_EQ_CARD CARD_EQ_GROUP_IMAGE_KERNEL CARD_IMAGE_INJ CARD_MUL_C
   CARD_MUL_FINITE CARRIER_SUBFIELD_GENERATED_SUBFIELD
   CARRIER_SUBGROUP_GENERATED_SUBGROUP CARRIER_SUBRING_GENERATED_SUBRING
   CARRIER_SUBRING_OF CHINESE_REMAINDER_IDEALS CONJ_ASSOC EQ_MULT_LCANCEL
   EXISTS_IN_GSPEC EXP EXTENSION FIELD_EXTENSION_SUBRING_GENERATED_FINITE
   FIELD_IMP_INTEGRAL_DOMAIN FIELD_IMP_NONTRIVIAL_RING FIELD_QUOTIENT_RING
   FINITE_EXTENSION_SUBFIELD_GENERATED FINITE_FIELD_PRIMITIVE_ROOT
   FINITE_GALOIS_GROUP FINITE_GROUP_ORBIT FINITE_IMAGE
   FINITE_INTEGRAL_DOMAIN_IMP_FIELD FINITE_SUBRING_GENERATED FINITE_SUBSET
   FIXED_FIELD_GALOIS_GROUP FORALL_IN_GSPEC FORALL_IN_IMAGE FUN_EQ_THM
   FUN_IN_IMAGE GALOIS_EXTENSION_EQ_CARD GALOIS_EXTENSION_SUBFIELD_GENERATED
   GALOIS_GROUP GALOIS_GROUP_ACTION GALOIS_GROUP_ANTIMONO GALOIS_GROUP_COMPOSE
   GALOIS_GROUP_FINITE_FIELD GALOIS_GROUP_FIXED_FIELD GALOIS_GROUP_FIXES
   GALOIS_GROUP_I GALOIS_GROUP_IMAGE_INVERSE GALOIS_GROUP_INVERSE
   GALOIS_GROUP_IN_CARRIER GALOIS_GROUP_PERMUTES GALOIS_GROUP_RING_AUTOMORPHISM
   GALOIS_GROUP_RING_HOMOMORPHISM GALOIS_PRODUCT_IN_BASE GROUP_ACTION_ON_SUBSET
   GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET GROUP_EPIMORPHISM_ALT
   GROUP_HOMOMORPHISM GROUP_ID GROUP_ORBIT GROUP_POW GROUP_STABILIZER_OF_ACTION
   HAS_SIZE IMAGE_CLAUSES IMAGE_I IMAGE_ID IMAGE_SUBSET IMAGE_o IMP_CONJ
   INTEGRAL_DOMAIN_SUBRING_GENERATED IN_ELIM_THM IN_FIXED_FIELD IN_GALOIS_GROUP
   IN_GALOIS_GROUP_INTERMEDIATE IN_IMAGE IN_INTER IN_RING_IDEAL_0
   IN_RING_IDEAL_ADD IN_RING_IDEAL_SUB IN_RING_POLYNOMIAL_CARRIER_COMPOSE
   IN_SING IN_UNIONS IN_UNIV I_DEF I_THM MAXIMAL_IDEAL_COMAXIMAL
   MAXIMAL_IDEAL_ISOMORPHIC_IMAGE_EQ MAXIMAL_IMP_PRIME_IDEAL
   MAXIMAL_IMP_PROPER_IDEAL MAXIMAL_IMP_RING_IDEAL MEMBER_NOT_EMPTY MONO_EXISTS
   MULT_SYM NORMAL_SUBGROUP_GROUP_KERNEL NOT_EXISTS_THM ORBIT_STABILIZER_MUL
   PERMUTES_BIJECTIONS PERMUTES_INJECTIVE PERMUTES_INVERSES : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (PERMUTES_INVERSE_INVERSE PERMUTES_IN_IMAGE POLY_EVAL_CONST
   POLY_EVAL_HOMOMORPHIC_IMAGE POLY_EVAL_RING_PRODUCT POLY_EVAL_SUB
   POLY_EVAL_VAR POLY_X_MINUS_A_IN_CARRIER PRIME_AVOIDANCE
   PRIME_IDEAL_IMP_SUBSET PRIME_IDEAL_ISOMORPHIC_IMAGE_EQ PRIME_IMP_PROPER_IDEAL
   PRIME_IMP_RING_IDEAL PSUBSET QUOTIENT_RING_0 QUOTIENT_RING_CARRIER
   QUOTIENT_RING_UNIVERSAL RIGHT_FORALL_IMP_THM RING_0 RING_CARRIER_NONEMPTY
   RING_CARRIER_SUBRING_GENERATED_SUBSET RING_COSET_EQ RING_COSET_EQ_IDEAL
   RING_HOMOMORPHISMS_EQ_FROM_SUBRING_GENERATED RING_HOMOMORPHISM_0
   RING_HOMOMORPHISM_ADD RING_HOMOMORPHISM_BETWEEN_SUBRINGS
   RING_HOMOMORPHISM_COMPOSE RING_HOMOMORPHISM_EQ RING_HOMOMORPHISM_I
   RING_HOMOMORPHISM_POW RING_HOMOMORPHISM_RING_COSET RING_HOMOMORPHISM_SUB
   RING_IDEAL_IMP_SUBSET RING_IDEAL_ISOMORPHIC_IMAGE_EQ
   RING_ISOMORPHISM_BETWEEN_SUBRINGS RING_ISOMORPHISM_IMP_HOMOMORPHISM
   RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_MONOMORPHISM_INCLUSION RING_NEG_SUB
   RING_ORDER_0 RING_POLYNOMIAL_CONST RING_POLYNOMIAL_VAR RING_POW RING_POW_1
   RING_POW_IN_PRIME_IDEAL RING_POW_POW RING_POW_SUBRING_GENERATED RING_PRODUCT
   RING_PRODUCT_EQ RING_PRODUCT_IN_PRIME_IDEAL
   RING_PRODUCT_SUBRING_GENERATED_GEN RING_PRODUCT_X_MINUS_A_IN_FIXED_FIELD
   RING_SUB RING_SUB_REFL RING_SUB_RZERO RING_SUB_SUBRING_GENERATED
   SELECT_UNIQUE SIMPLE_IMAGE SUBGROUP_GENERATED SUBGROUP_OF_SUBGROUP_GENERATED
   SUBGROUP_SUBGROUP_GENERATED SUBRING_GENERATED SUBRING_GENERATED_INC_GEN
   SUBRING_OF_HOMOMORPHIC_IMAGE SUBRING_OF_HOMOMORPHIC_PREIMAGE
   SUBRING_SUBRING_GENERATED SUBSET SUBSET_ANTISYM SUBSET_REFL SUBSET_UNIV
   TRIVIAL_RING_HAS_SIZE_1 field_extension finite_extension group_conjugation
   group_epimorphism group_image group_kernel group_pow group_stabilizer
   maximal_ideal o_DEF o_THM pairwise permutes ring_automorphism ring_coset
   ring_homomorphism ring_ideal ring_isomorphism ring_isomorphisms ring_kernel
   subgroup_of subring_of : thm)
  deriving Inhabited

/-- What decomposition.ml uses from Session besides theorems. -/
structure DecompositionDeps where
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
/- decomposition.ml phrases from line 108 to 762                          -/
/- ---------------------------------------------------------------------- -/

structure Decomposition01 where
  -- @@FIELDS
  GALOIS_GROUP_SUBRING_IMAGE : thm
  GALOIS_GROUP_PRIME_IDEAL_IMAGE : thm
  GALOIS_GROUP_IMAGE_RING_COSET : thm
  GALOIS_GROUP_ACTION_SUBRING : thm
  GALOIS_GROUP_TRANSITIVE_PRIME_IDEALS : thm
  GALOIS_GROUP_ORBIT_MAXIMAL_IDEAL : thm
  decomposition_group : thm
  inertia_group : thm
  DECOMPOSITION_GROUP : thm
  DECOMPOSITION_GROUP_SUBRING_IMAGE : thm
  INERTIA_GROUP : thm
  INERTIA_GROUP_SUBGROUP_OF_DECOMPOSITION_GROUP : thm
  DECOMPOSITION_GROUP_INDEX : thm
  DECOMPOSITION_GROUP_CONJUGATE : thm
  INERTIA_GROUP_CONJUGATE : thm
  CARD_DECOMPOSITION_GROUP_CONJUGATE : thm
  SUBRING_GENERATED_QUOTIENT_RING_IMAGE : thm
  GALOIS_GROUP_QUOTIENT_RING_IMAGE : thm
  DECOMPOSITION_GROUP_IMAGE_RING_COSET : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDecomposition01 [HolBase] (D : DecompositionDeps) :
    ExceptT String IO Decomposition01 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, RING_RULE, SET_TAC, TAUT, new_definition, .. } := D
  let { CARD_IMAGE_INJ, CARRIER_SUBGROUP_GENERATED_SUBGROUP,
        CARRIER_SUBRING_GENERATED_SUBRING, CARRIER_SUBRING_OF, EXISTS_IN_GSPEC,
        EXTENSION, FINITE_GALOIS_GROUP, FINITE_GROUP_ORBIT, FINITE_IMAGE,
        FINITE_SUBSET, FORALL_IN_IMAGE, FUN_EQ_THM, GALOIS_EXTENSION_EQ_CARD,
        GALOIS_GROUP, GALOIS_GROUP_ACTION, GALOIS_GROUP_COMPOSE, GALOIS_GROUP_FIXES,
        GALOIS_GROUP_I, GALOIS_GROUP_IMAGE_INVERSE, GALOIS_GROUP_INVERSE,
        GALOIS_GROUP_PERMUTES, GALOIS_GROUP_RING_AUTOMORPHISM, GALOIS_PRODUCT_IN_BASE,
        GROUP_ACTION_ON_SUBSET, GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET, GROUP_ORBIT,
        GROUP_STABILIZER_OF_ACTION, IMAGE_I, IMAGE_o, IN_ELIM_THM, IN_IMAGE, IN_UNIONS,
        IN_UNIV, I_THM, MAXIMAL_IDEAL_ISOMORPHIC_IMAGE_EQ, MAXIMAL_IMP_PRIME_IDEAL,
        MAXIMAL_IMP_RING_IDEAL, MONO_EXISTS, NOT_EXISTS_THM, ORBIT_STABILIZER_MUL,
        PERMUTES_INVERSES, .. } := D.core1
  let { PRIME_AVOIDANCE, PRIME_IDEAL_IMP_SUBSET, PRIME_IDEAL_ISOMORPHIC_IMAGE_EQ,
        PRIME_IMP_PROPER_IDEAL, PSUBSET, QUOTIENT_RING_CARRIER,
        RING_CARRIER_SUBRING_GENERATED_SUBSET, RING_HOMOMORPHISM_ADD,
        RING_HOMOMORPHISM_BETWEEN_SUBRINGS, RING_HOMOMORPHISM_COMPOSE,
        RING_HOMOMORPHISM_RING_COSET, RING_HOMOMORPHISM_SUB, RING_IDEAL_IMP_SUBSET,
        RING_IDEAL_ISOMORPHIC_IMAGE_EQ, RING_ISOMORPHISM_BETWEEN_SUBRINGS,
        RING_ISOMORPHISM_IMP_HOMOMORPHISM, RING_NEG_SUB, RING_PRODUCT_IN_PRIME_IDEAL,
        RING_PRODUCT_SUBRING_GENERATED_GEN, RING_SUB_REFL, SIMPLE_IMAGE,
        SUBGROUP_GENERATED, SUBGROUP_OF_SUBGROUP_GENERATED,
        SUBGROUP_SUBGROUP_GENERATED, SUBRING_GENERATED, SUBRING_OF_HOMOMORPHIC_IMAGE,
        SUBRING_OF_HOMOMORPHIC_PREIMAGE, SUBRING_SUBRING_GENERATED, SUBSET,
        SUBSET_ANTISYM, SUBSET_UNIV, group_conjugation, group_stabilizer,
        maximal_ideal, o_THM, ring_automorphism, ring_coset, ring_ideal, subgroup_of,
        subring_of, .. } := D.core2
  -- @@SCOPE END

  let GALOIS_GROUP_SUBRING_IMAGE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!(h:A->B) k l b f.
          subring_generated l (ring_carrier b) = b /\
          (!f. f IN group_carrier(galois_group(k,l) h)
               ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
          f IN group_carrier(galois_group(k,l) h)
          ==> IMAGE f (ring_carrier b) = ring_carrier b /\
              ring_isomorphism(b,b) f"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN ABBREV_TAC (← q r"B = ring_carrier(b:B ring)") THEN UNDISCH_TAC (← q r"subring_generated l B = (b:B ring)") THEN DISCH_THEN (SUBST_ALL_TAC o SYM) THEN SUBGOAL_THEN (← q r"(B:B->bool) subring_of l") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"B:B->bool")] SUBRING_SUBRING_GENERATED) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_SIMP_TAC [] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_GROUP_PERMUTES)) THEN DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP PERMUTES_INVERSES)) THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"inverse(f:B->B)"))) THEN ASM_SIMP_TAC [GALOIS_GROUP_INVERSE] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_IMAGE] THEN ASM_MESON_TAC [], DISCH_TAC THEN MATCH_MP_TAC RING_ISOMORPHISM_BETWEEN_SUBRINGS THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ASM_MESON_TAC [GALOIS_GROUP_RING_AUTOMORPHISM, ring_automorphism], ASM_MESON_TAC [subring_of]]])

  let GALOIS_GROUP_PRIME_IDEAL_IMAGE ← prove
    r"!(h:A->B) k l b f Q.
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        f IN group_carrier(galois_group(k,l) h) /\ Q SUBSET ring_carrier b
        ==> (ring_ideal b (IMAGE f Q) <=> ring_ideal b Q) /\
            (prime_ideal b (IMAGE f Q) <=> prime_ideal b Q) /\
            (maximal_ideal b (IMAGE f Q) <=> maximal_ideal b Q) /\
            IMAGE f Q SUBSET ring_carrier b /\
            {a | a IN ring_carrier k /\ h a IN IMAGE f Q} =
            {a | a IN ring_carrier k /\ h a IN Q}"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"f:B->B")] GALOIS_GROUP_SUBRING_IMAGE) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_SIMP_TAC [(← ISPECL [(← q r"b:B ring"), (← q r"b:B ring")] RING_IDEAL_ISOMORPHIC_IMAGE_EQ), (← ISPECL [(← q r"b:B ring"), (← q r"b:B ring")] PRIME_IDEAL_ISOMORPHIC_IMAGE_EQ), (← ISPECL [(← q r"b:B ring"), (← q r"b:B ring")] MAXIMAL_IDEAL_ISOMORPHIC_IMAGE_EQ)] THEN CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"a:A") THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_CASES_TAC (← q r"(a:A) IN ring_carrier k") THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_GROUP_PERMUTES)) THEN DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP PERMUTES_INVERSES)) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"f:B->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"a:A")] GALOIS_GROUP_FIXES) THEN ASM_REWRITE_TAC [IN_IMAGE] THEN ASM_MESON_TAC [])

  let GALOIS_GROUP_IMAGE_RING_COSET ← prove
    r"!(h:A->B) k l b Q f x.
        subring_generated l (ring_carrier b) = b /\ Q SUBSET ring_carrier b /\
        f IN group_carrier(galois_group(k,l) h) /\ x IN ring_carrier b
        ==> IMAGE f (ring_coset b Q x) = ring_coset b (IMAGE f Q) (f x)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_carrier b SUBSET ring_carrier l /\ ring_add b = ring_add (l:B ring)") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"subring_generated l (ring_carrier b) = (b:B ring)") THEN DISCH_THEN (fun th => tactic_of do pure (ONCE_REWRITE_TAC [(← SYM th)])) THEN REWRITE_TAC [RING_CARRIER_SUBRING_GENERATED_SUBSET, (← CONJUNCT2 SUBRING_GENERATED)], ALL_TAC] THEN SUBGOAL_THEN (← q r"!y. y IN Q ==> (f:B->B) (ring_add l x y) = ring_add l (f x) (f y)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"l:B ring"), (← q r"f:B->B")] RING_HOMOMORPHISM_ADD) THEN ANTS_TAC THENL [ASM_MESON_TAC [GALOIS_GROUP_RING_AUTOMORPHISM, ring_automorphism, RING_ISOMORPHISM_IMP_HOMOMORPHISM], DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC []], ALL_TAC] THEN ASM_REWRITE_TAC [ring_coset] THEN ASM SET_TAC [])

  let GALOIS_GROUP_ACTION_SUBRING ← prove
    r"!(h:A->B) k l b.
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b)
        ==> group_action (galois_group(k,l) h) (ring_carrier b) (\f x. f x) /\
            group_action (galois_group(k,l) h) {Q | prime_ideal b Q} IMAGE /\
            group_action (galois_group(k,l) h) {Q | maximal_ideal b Q} IMAGE"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC GROUP_ACTION_ON_SUBSET THENL [EXISTS_TAC (← q r"ring_carrier l:B->bool") THEN REWRITE_TAC [GALOIS_GROUP_ACTION] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"ring_carrier(b:B ring)")] RING_CARRIER_SUBRING_GENERATED_SUBSET) THEN ASM_REWRITE_TAC [], ASM SET_TAC []], EXISTS_TAC (← q r"(:B->bool)"), EXISTS_TAC (← q r"(:B->bool)")] THEN REWRITE_TAC [GALOIS_GROUP_ACTION, SUBSET_UNIV, IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"f:B->B"), (← q r"Q:B->bool")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"f:B->B"), (← q r"Q:B->bool")] GALOIS_GROUP_PRIME_IDEAL_IMAGE) THEN ASM_SIMP_TAC [PRIME_IDEAL_IMP_SUBSET, MAXIMAL_IMP_PRIME_IDEAL])

  let GALOIS_GROUP_TRANSITIVE_PRIME_IDEALS ← prove
    r"!(h:A->B) k l b Q Q'.
        finite_extension(k,l) h /\ galois_extension(k,l) h /\
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        prime_ideal b Q /\ maximal_ideal b Q' /\
        {a | a IN ring_carrier k /\ h a IN Q'} =
        {a | a IN ring_carrier k /\ h a IN Q}
        ==> ?f. f IN group_carrier(galois_group(k,l) h) /\ IMAGE f Q = Q'"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"FINITE(group_carrier(galois_group(k,l) (h:A->B)))") ASSUME_TAC THENL [ASM_SIMP_TAC [FINITE_GALOIS_GROUP], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_PRIME_IDEAL)) THEN SUBGOAL_THEN (← q r"Q SUBSET ring_carrier b /\ Q' SUBSET ring_carrier b /\
    ring_carrier b SUBSET ring_carrier(l:B ring)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [PRIME_IDEAL_IMP_SUBSET] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"ring_carrier(b:B ring)")] RING_CARRIER_SUBRING_GENERATED_SUBSET) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!f. f IN group_carrier(galois_group(k,l) (h:A->B))
        ==> prime_ideal b (IMAGE f Q)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"f:B->B"), (← q r"Q:B->bool")] GALOIS_GROUP_PRIME_IDEAL_IMAGE) THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"Q' SUBSET
    UNIONS {IMAGE f Q | f IN group_carrier(galois_group(k,l) (h:A->B))}") ASSUME_TAC THENL [REWRITE_TAC [SUBSET, IN_UNIONS, EXISTS_IN_GSPEC] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier b /\ x IN ring_carrier l") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!f. f IN group_carrier(galois_group(k,l) (h:A->B))
          ==> f x IN ring_carrier b") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_product b (group_carrier(galois_group(k,l) (h:A->B))) (\f. f x) =
      ring_product l (group_carrier(galois_group(k,l) h)) (\f. f x)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"ring_carrier(b:B ring)"), (← q r"group_carrier(galois_group(k,l) (h:A->B))"), (← q r"\f:B->B. f x")] RING_PRODUCT_SUBRING_GENERATED_GEN) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_product b (group_carrier(galois_group(k,l) (h:A->B))) (\f. f x)
      IN Q'") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"Q':B->bool"), (← q r"group_carrier(galois_group(k,l) (h:A->B))"), (← q r"\f:B->B. f x")] RING_PRODUCT_IN_PRIME_IDEAL) THEN ANTS_TAC THENL [ASM_SIMP_TAC [], DISCH_THEN SUBST1_TAC] THEN EXISTS_TAC (← q r"I:B->B") THEN ASM_REWRITE_TAC [GALOIS_GROUP_I, I_THM], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_product b (group_carrier(galois_group(k,l) (h:A->B))) (\f. f x)
      IN Q") MP_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"x:B")] GALOIS_PRODUCT_IN_BASE) THEN ASM_REWRITE_TAC [IN_IMAGE] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"a:A") STRIP_ASSUME_TAC) o CONJUNCT1) THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(h:A->B) a IN Q'") MP_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN UNDISCH_TAC (← q r"{a | a IN ring_carrier k /\ (h:A->B) a IN Q'} =
        {a | a IN ring_carrier k /\ h a IN Q}") THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"group_carrier(galois_group(k,l) (h:A->B))"), (← q r"\f:B->B. f x")] RING_PRODUCT_IN_PRIME_IDEAL) THEN ANTS_TAC THENL [ASM_SIMP_TAC [], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"f:B->B") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"inverse(f:B->B)") THEN ASM_SIMP_TAC [GALOIS_GROUP_INVERSE] THEN REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC (← q r"(f:B->B) x") THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_GROUP_PERMUTES)) THEN DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP PERMUTES_INVERSES)) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"Q':B->bool"), (← q r"{IMAGE f Q | f IN group_carrier(galois_group(k,l) (h:A->B))}")] PRIME_AVOIDANCE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [MAXIMAL_IMP_RING_IDEAL, SIMPLE_IMAGE, FINITE_IMAGE, FORALL_IN_IMAGE], REWRITE_TAC [EXISTS_IN_GSPEC]] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"f:B->B") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"maximal_ideal b (Q':B->bool)") THEN REWRITE_TAC [maximal_ideal, NOT_EXISTS_THM] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"IMAGE (f:B->B) Q")) o CONJUNCT2)) THEN ASM_SIMP_TAC [PRIME_IMP_PROPER_IDEAL, PSUBSET] THEN ASM SET_TAC [])

  let GALOIS_GROUP_ORBIT_MAXIMAL_IDEAL ← prove
    r"!(h:A->B) k l b Q.
        finite_extension(k,l) h /\ galois_extension(k,l) h /\
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        maximal_ideal b Q
        ==> group_orbit (galois_group(k,l) h) {Q | maximal_ideal b Q} IMAGE Q =
            {Q' | maximal_ideal b Q' /\
                  {a | a IN ring_carrier k /\ h a IN Q'} =
                  {a | a IN ring_carrier k /\ h a IN Q}}"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring")] GALOIS_GROUP_ACTION_SUBRING) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_SIMP_TAC [GROUP_ORBIT, IN_ELIM_THM] THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"Q':B->bool") THEN REWRITE_TAC [IN_ELIM_THM] THEN EQ_TAC THENL [DISCH_THEN (X_CHOOSE_THEN (← q r"f:B->B") (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"f:B->B"), (← q r"Q:B->bool")] GALOIS_GROUP_PRIME_IDEAL_IMAGE) THEN ASM_SIMP_TAC [MAXIMAL_IMP_PRIME_IDEAL, PRIME_IDEAL_IMP_SUBSET], STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"Q':B->bool")] GALOIS_GROUP_TRANSITIVE_PRIME_IDEALS) THEN ASM_SIMP_TAC [MAXIMAL_IMP_PRIME_IDEAL] THEN MESON_TAC []])

  let decomposition_group ← new_definition
    r"decomposition_group (k:A ring,l:B ring) (h:A->B) (Q:B->bool) =
    subgroup_generated (galois_group(k,l) h)
      {f | f IN group_carrier(galois_group(k,l) h) /\ IMAGE f Q = Q}"

  let inertia_group ← new_definition
    r"inertia_group (k:A ring,l:B ring) (h:A->B) (b:B ring) (Q:B->bool) =
    subgroup_generated (galois_group(k,l) h)
      {f | f IN group_carrier(galois_group(k,l) h) /\ IMAGE f Q = Q /\
           !x. x IN ring_carrier b ==> ring_sub l (f x) x IN Q}"

  let DECOMPOSITION_GROUP ← prove
    r"(!(h:A->B) k l Q.
        group_carrier(decomposition_group(k,l) h Q) =
        {f | f IN group_carrier(galois_group(k,l) h) /\ IMAGE f Q = Q}) /\
   (!(h:A->B) k l Q. group_id(decomposition_group(k,l) h Q) = I) /\
   (!(h:A->B) k l Q. group_inv(decomposition_group(k,l) h Q) = inverse) /\
   (!(h:A->B) k l Q. group_mul(decomposition_group(k,l) h Q) = (o))"
    (REWRITE_TAC [decomposition_group, (← CONJUNCT2 SUBGROUP_GENERATED), (← CONJUNCT2 GALOIS_GROUP)] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC CARRIER_SUBGROUP_GENERATED_SUBGROUP THEN REWRITE_TAC [subgroup_of, SUBSET, IN_ELIM_THM] THEN REWRITE_TAC [(← CONJUNCT2 GALOIS_GROUP), GALOIS_GROUP_I, IMAGE_I] THEN SIMP_TAC [GALOIS_GROUP_INVERSE, GALOIS_GROUP_COMPOSE, IMAGE_o] THEN MESON_TAC [GALOIS_GROUP_IMAGE_INVERSE])

  let DECOMPOSITION_GROUP_SUBRING_IMAGE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!(h:A->B) k l b Q f.
          subring_generated l (ring_carrier b) = b /\
          (!f. f IN group_carrier(decomposition_group(k,l) h Q)
               ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
          f IN group_carrier(decomposition_group(k,l) h Q)
          ==> IMAGE f (ring_carrier b) = ring_carrier b /\
              ring_isomorphism(b,b) f"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"f IN group_carrier(galois_group(k,l) (h:A->B)) /\
      inverse f IN group_carrier(decomposition_group(k,l) h Q)") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"f IN group_carrier(decomposition_group(k,l) (h:A->B) Q)") THEN REWRITE_TAC [DECOMPOSITION_GROUP, IN_ELIM_THM] THEN MESON_TAC [GALOIS_GROUP_INVERSE, GALOIS_GROUP_IMAGE_INVERSE], ALL_TAC] THEN ABBREV_TAC (← q r"B = ring_carrier(b:B ring)") THEN UNDISCH_TAC (← q r"subring_generated l B = (b:B ring)") THEN DISCH_THEN (SUBST_ALL_TAC o SYM) THEN SUBGOAL_THEN (← q r"(B:B->bool) subring_of l") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"B:B->bool")] SUBRING_SUBRING_GENERATED) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_SIMP_TAC [] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_GROUP_PERMUTES)) THEN DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP PERMUTES_INVERSES)) THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"inverse(f:B->B)"))) THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_IMAGE] THEN ASM_MESON_TAC [], DISCH_TAC THEN MATCH_MP_TAC RING_ISOMORPHISM_BETWEEN_SUBRINGS THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ASM_MESON_TAC [GALOIS_GROUP_RING_AUTOMORPHISM, ring_automorphism], ASM_MESON_TAC [subring_of]]])

  let INERTIA_GROUP ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_add r (ring_sub r a c) (ring_sub r c d) = ring_sub r a (d:A)")
    prove
      r"(!(h:A->B) k l b Q.
          subring_generated l (ring_carrier b) = b /\
          (!f. f IN group_carrier(decomposition_group(k,l) h Q)
               ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
          ring_ideal b Q
          ==> group_carrier(inertia_group(k,l) h b Q) =
              {f | f IN group_carrier(galois_group(k,l) h) /\ IMAGE f Q = Q /\
                   !x. x IN ring_carrier b ==> ring_sub l (f x) x IN Q}) /\
     (!(h:A->B) k l b Q. group_id(inertia_group(k,l) h b Q) = I) /\
     (!(h:A->B) k l b Q. group_inv(inertia_group(k,l) h b Q) = inverse) /\
     (!(h:A->B) k l b Q. group_mul(inertia_group(k,l) h b Q) = (o))"
      (CONJ_TAC THENL [REWRITE_TAC [inertia_group] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE [DECOMPOSITION_GROUP, IN_ELIM_THM]) THEN SUBGOAL_THEN (← q r"ring_carrier b SUBSET ring_carrier l /\ ring_0 (l:B ring) IN Q /\
        (!x. x IN Q ==> ring_neg l x IN Q) /\
        (!x y. x IN Q /\ y IN Q ==> ring_add l x y IN Q)") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"ring_ideal b (Q:B->bool)") THEN UNDISCH_TAC (← q r"subring_generated l (ring_carrier b) = (b:B ring)") THEN DISCH_THEN (fun th => tactic_of do pure (ONCE_REWRITE_TAC [(← SYM th)])) THEN SIMP_TAC [ring_ideal, (← CONJUNCT2 SUBRING_GENERATED), RING_CARRIER_SUBRING_GENERATED_SUBSET], ALL_TAC] THEN MATCH_MP_TAC CARRIER_SUBGROUP_GENERATED_SUBGROUP THEN REWRITE_TAC [subgroup_of, SUBSET, IN_ELIM_THM] THEN REWRITE_TAC [(← CONJUNCT2 GALOIS_GROUP), GALOIS_GROUP_I, IMAGE_I, I_THM] THEN SIMP_TAC [GALOIS_GROUP_INVERSE, GALOIS_GROUP_COMPOSE, IMAGE_o, o_THM] THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_SUB_REFL, SUBSET], ALL_TAC] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"f:B->B") THEN STRIP_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_GROUP_PERMUTES)) THEN DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP PERMUTES_INVERSES)) THEN CONJ_TAC THENL [ASM_MESON_TAC [GALOIS_GROUP_IMAGE_INVERSE], ALL_TAC] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"inverse (f:B->B) x IN ring_carrier b") ASSUME_TAC THENL [ASM_MESON_TAC [GALOIS_GROUP_INVERSE, GALOIS_GROUP_IMAGE_INVERSE, SUBSET, IN_IMAGE], ALL_TAC] THEN UNDISCH_TAC (← q r"!x. x IN ring_carrier b ==> ring_sub l ((f:B->B) x) x IN Q") THEN DISCH_THEN (MP_TAC o (SPEC (← q r"inverse (f:B->B) x"))) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"x:B"), (← q r"inverse (f:B->B) x")] RING_NEG_SUB) THEN ANTS_TAC THENL [ASM SET_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN ASM_SIMP_TAC [], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"f:B->B"), (← q r"g:B->B")] THEN STRIP_TAC THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"IMAGE (f:B->B) (ring_carrier b) SUBSET ring_carrier b /\
        IMAGE (g:B->B) (ring_carrier b) SUBSET ring_carrier b") MP_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(g:B->B) x IN ring_carrier b /\ f(g x) IN ring_carrier b") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sub l ((f:B->B) (g x)) x =
        ring_add l (ring_sub l (f (g x)) (g x)) (ring_sub l (g x) x)") SUBST1_TAC THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC r1 THEN ASM SET_TAC [], ASM_SIMP_TAC []], REWRITE_TAC [inertia_group, (← CONJUNCT2 SUBGROUP_GENERATED), (← CONJUNCT2 GALOIS_GROUP)]])

  let INERTIA_GROUP_SUBGROUP_OF_DECOMPOSITION_GROUP ← prove
    r"!(h:A->B) k l b Q.
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        ring_ideal b Q
        ==> group_carrier(inertia_group(k,l) h b Q) subgroup_of
            decomposition_group(k,l) h Q"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"!f. f IN group_carrier(decomposition_group(k,l) (h:A->B) Q)
        ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b") ASSUME_TAC THENL [REWRITE_TAC [DECOMPOSITION_GROUP, IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN REWRITE_TAC [decomposition_group] THEN MATCH_MP_TAC SUBGROUP_OF_SUBGROUP_GENERATED THEN CONJ_TAC THENL [REWRITE_TAC [inertia_group, SUBGROUP_SUBGROUP_GENERATED], ASM_SIMP_TAC [INERTIA_GROUP] THEN SET_TAC []])

  let DECOMPOSITION_GROUP_INDEX ← prove
    r"!(h:A->B) k l b Q.
        finite_extension(k,l) h /\ galois_extension(k,l) h /\
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        maximal_ideal b Q
        ==> FINITE {Q' | maximal_ideal b Q' /\
                         {a | a IN ring_carrier k /\ h a IN Q'} =
                         {a | a IN ring_carrier k /\ h a IN Q}} /\
            CARD {Q' | maximal_ideal b Q' /\
                       {a | a IN ring_carrier k /\ h a IN Q'} =
                       {a | a IN ring_carrier k /\ h a IN Q}} *
            CARD(group_carrier(decomposition_group(k,l) h Q)) =
            extension_degree(k,l) h"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool")] GALOIS_GROUP_ORBIT_MAXIMAL_IDEAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring")] GALOIS_GROUP_ACTION_SUBRING) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"FINITE(group_carrier(galois_group(k,l) (h:A->B)))") ASSUME_TAC THENL [ASM_SIMP_TAC [FINITE_GALOIS_GROUP], ALL_TAC] THEN ASM_SIMP_TAC [FINITE_GROUP_ORBIT] THEN SUBGOAL_THEN (← q r"CARD(group_carrier(galois_group(k,l) (h:A->B))) = extension_degree(k,l) h") (SUBST1_TAC o SYM) THENL [ASM_MESON_TAC [GALOIS_EXTENSION_EQ_CARD], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"galois_group(k,l) (h:A->B)"), (← q r"{Q | maximal_ideal b Q}:(B->bool)->bool"), (← q r"IMAGE:(B->B)->(B->bool)->(B->bool)"), (← q r"Q:B->bool")] ORBIT_STABILIZER_MUL) THEN ASM_REWRITE_TAC [IN_ELIM_THM, group_stabilizer, DECOMPOSITION_GROUP])

  let DECOMPOSITION_GROUP_CONJUGATE ← prove
    r"!(h:A->B) k l f Q.
        f IN group_carrier(galois_group(k,l) h)
        ==> group_carrier(decomposition_group(k,l) h (IMAGE f Q)) =
            IMAGE (\g. f o g o inverse f)
                  (group_carrier(decomposition_group(k,l) h Q))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"galois_group(k,l) (h:A->B)"), (← q r"(:B->bool)"), (← q r"IMAGE:(B->B)->(B->bool)->(B->bool)"), (← q r"f:B->B"), (← q r"Q:B->bool")] GROUP_STABILIZER_OF_ACTION) THEN ASM_REWRITE_TAC [GALOIS_GROUP_ACTION, IN_UNIV] THEN SUBGOAL_THEN (← q r"group_conjugation (galois_group(k,l) (h:A->B)) f =
                (\g. f o g o inverse f)") SUBST1_TAC THENL [REWRITE_TAC [FUN_EQ_THM, group_conjugation, (← CONJUNCT2 GALOIS_GROUP)], REWRITE_TAC [group_stabilizer, DECOMPOSITION_GROUP]])

  let INERTIA_GROUP_CONJUGATE ← prove
    r"!(h:A->B) k l b f Q.
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        ring_ideal b Q /\ f IN group_carrier(galois_group(k,l) h)
        ==> group_carrier(inertia_group(k,l) h b (IMAGE f Q)) =
            IMAGE (\g. f o g o inverse f)
                  (group_carrier(inertia_group(k,l) h b Q))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"f:B->B"), (← q r"Q:B->bool")] GALOIS_GROUP_PRIME_IDEAL_IMAGE) THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET] THEN STRIP_TAC THEN ASM_SIMP_TAC [INERTIA_GROUP, DECOMPOSITION_GROUP, IN_ELIM_THM] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_GROUP_PERMUTES)) THEN DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP PERMUTES_INVERSES)) THEN SUBGOAL_THEN (← q r"!y:B. y IN IMAGE (f:B->B) Q <=> inverse f y IN Q") (fun th => REWRITE_TAC [th]) THENL [REWRITE_TAC [IN_IMAGE] THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_homomorphism(l,l) (inverse(f:B->B)) /\
    ring_carrier b SUBSET ring_carrier l /\
    (!x. x IN ring_carrier b ==> f x IN ring_carrier b) /\
    (!x. x IN ring_carrier b ==> inverse f x IN ring_carrier b)") STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THENL [ASM_MESON_TAC [GALOIS_GROUP_RING_AUTOMORPHISM, GALOIS_GROUP_INVERSE, ring_automorphism, RING_ISOMORPHISM_IMP_HOMOMORPHISM], MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"ring_carrier(b:B ring)")] RING_CARRIER_SUBRING_GENERATED_SUBSET) THEN ASM_REWRITE_TAC [], ASM SET_TAC [], ASM_MESON_TAC [GALOIS_GROUP_INVERSE, SUBSET, IN_IMAGE]], ALL_TAC] THEN SUBGOAL_THEN (← q r"IMAGE (inverse f) (IMAGE (f:B->B) Q) = Q") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"l:B ring"), (← q r"inverse(f:B->B)")] RING_HOMOMORPHISM_SUB) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"g:B->B") THEN REWRITE_TAC [IN_ELIM_THM] THEN GEN_REWRITE_TAC RAND_CONV [IN_IMAGE] THEN REWRITE_TAC [IN_ELIM_THM] THEN EQ_TAC THENL [STRIP_TAC THEN EXISTS_TAC (← q r"inverse (f:B->B) o (g:B->B) o f") THEN ASM_SIMP_TAC [GALOIS_GROUP_COMPOSE, GALOIS_GROUP_INVERSE, IMAGE_o] THEN REWRITE_TAC [FUN_EQ_THM, o_THM] THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN UNDISCH_TAC (← q r"!x:B. x IN ring_carrier b
            ==> inverse (f:B->B) (ring_sub l ((g:B->B) x) x) IN Q") THEN DISCH_THEN (MP_TAC o (SPEC (← q r"(f:B->B) x"))) THEN FIRST_X_ASSUM (MP_TAC o (SPECL [(← q r"(g:B->B) ((f:B->B) x)"), (← q r"(f:B->B) x")])) THEN ANTS_TAC THENL [ASM SET_TAC [], DISCH_THEN SUBST1_TAC] THEN ASM_SIMP_TAC [], DISCH_THEN (X_CHOOSE_THEN (← q r"g':B->B") (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN ASM_SIMP_TAC [GALOIS_GROUP_COMPOSE, GALOIS_GROUP_INVERSE, IMAGE_o] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN REWRITE_TAC [o_THM] THEN FIRST_X_ASSUM (MP_TAC o (SPECL [(← q r"(f:B->B) ((g':B->B) (inverse f (x:B)))"), (← q r"x:B")])) THEN ANTS_TAC THENL [ASM SET_TAC [], DISCH_THEN SUBST1_TAC] THEN ASM_SIMP_TAC []])

  let CARD_DECOMPOSITION_GROUP_CONJUGATE ← prove
    r"!(h:A->B) k l b f Q.
        finite_extension(k,l) h /\
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        ring_ideal b Q /\ f IN group_carrier(galois_group(k,l) h)
        ==> CARD(group_carrier(decomposition_group(k,l) h (IMAGE f Q))) =
            CARD(group_carrier(decomposition_group(k,l) h Q)) /\
            CARD(group_carrier(inertia_group(k,l) h b (IMAGE f Q))) =
            CARD(group_carrier(inertia_group(k,l) h b Q))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [DECOMPOSITION_GROUP_CONJUGATE, INERTIA_GROUP_CONJUGATE] THEN FIRST_ASSUM (MP_TAC o ((MATCH_MP GALOIS_GROUP_PERMUTES) o (checkM (fun th => (do let z3 ← (q r"f IN group_carrier(galois_group(k,l) (h:A->B))"); let z2 ← (do let z1 ← (pure th); pure (concl z1)); pure (z2 == z3)))))) THEN DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP PERMUTES_INVERSES)) THEN CONJ_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN (CONJ_TAC THENL [MAP_EVERY X_GEN_TAC [(← q r"g1:B->B"), (← q r"g2:B->B")] THEN REWRITE_TAC [FUN_EQ_THM, o_THM] THEN STRIP_TAC THEN X_GEN_TAC (← q r"z:B") THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"(f:B->B) z"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (AP_TERM (← q r"inverse(f:B->B)"))) THEN ASM_REWRITE_TAC [], MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"group_carrier(galois_group(k,l) (h:A->B))") THEN ASM_SIMP_TAC [FINITE_GALOIS_GROUP] THEN REWRITE_TAC [decomposition_group, inertia_group, GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET]]))

  let SUBRING_GENERATED_QUOTIENT_RING_IMAGE ← prove
    r"!(h:A->B) k l b Q.
        ring_homomorphism(k,l) h /\
        subring_generated l (ring_carrier b) = b /\ ring_ideal b Q
        ==> ring_carrier
             (subring_generated (quotient_ring b Q)
               (IMAGE (ring_coset b Q o h)
                      {a | a IN ring_carrier k /\ h a IN ring_carrier b})) =
            {ring_coset b Q (h a) | a | a IN ring_carrier k /\
                                        h a IN ring_carrier b}"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"IMAGE (ring_coset b Q o (h:A->B))
          {a | a IN ring_carrier k /\ h a IN ring_carrier b} =
    {ring_coset b Q (h a) | a | a IN ring_carrier k /\ h a IN ring_carrier b}") (SUBST1_TAC o SYM) THENL [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM, o_THM] THEN MESON_TAC [], ALL_TAC] THEN MATCH_MP_TAC CARRIER_SUBRING_GENERATED_SUBRING THEN ABBREV_TAC (← q r"A = {a | a IN ring_carrier k /\ (h:A->B) a IN ring_carrier b}") THEN SUBGOAL_THEN (← q r"(A:A->bool) subring_of k") ASSUME_TAC THENL [EXPAND_TAC "A" THEN MATCH_MP_TAC SUBRING_OF_HOMOMORPHIC_PREIMAGE THEN EXISTS_TAC (← q r"l:B ring") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"ring_carrier(b:B ring)")] SUBRING_SUBRING_GENERATED) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"A = ring_carrier(subring_generated k (A:A->bool))") SUBST1_TAC THENL [ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING], ALL_TAC] THEN MATCH_MP_TAC SUBRING_OF_HOMOMORPHIC_IMAGE THEN EXISTS_TAC (← q r"subring_generated k (A:A->bool)") THEN REWRITE_TAC [CARRIER_SUBRING_OF] THEN MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC (← q r"b:B ring") THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_COSET] THEN UNDISCH_TAC (← q r"subring_generated l (ring_carrier b) = (b:B ring)") THEN DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [(← SYM th)])) THEN MATCH_MP_TAC RING_HOMOMORPHISM_BETWEEN_SUBRINGS THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "A" THEN SET_TAC [])

  let GALOIS_GROUP_QUOTIENT_RING_IMAGE ← prove
    r"!(h:A->B) k l b f Q.
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        ring_ideal b Q /\ f IN group_carrier(galois_group(k,l) h)
        ==> ring_carrier(quotient_ring b (IMAGE f Q)) =
            IMAGE (IMAGE f) (ring_carrier(quotient_ring b Q))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"f:B->B"), (← q r"Q:B->bool")] GALOIS_GROUP_PRIME_IDEAL_IMAGE) THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET] THEN STRIP_TAC THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER] THEN FIRST_ASSUM (MP_TAC o ((MATCH_MP GALOIS_GROUP_PERMUTES) o (checkM (fun th => (do let z3 ← (q r"f IN group_carrier(galois_group(k,l) (h:A->B))"); let z2 ← (do let z1 ← (pure th); pure (concl z1)); pure (z2 == z3)))))) THEN DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP PERMUTES_INVERSES)) THEN SUBGOAL_THEN (← q r"(!x. x IN ring_carrier b ==> (f:B->B) x IN ring_carrier b) /\
    (!x. x IN ring_carrier b ==> inverse f x IN ring_carrier b) /\
    (!x. x IN ring_carrier b
         ==> IMAGE f (ring_coset b Q x) = ring_coset b (IMAGE f Q) (f x))") STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THENL [ASM SET_TAC [], ASM_MESON_TAC [GALOIS_GROUP_INVERSE, SUBSET, IN_IMAGE], REPEAT STRIP_TAC THEN MATCH_MP_TAC GALOIS_GROUP_IMAGE_RING_COSET THEN MAP_EVERY EXISTS_TAC [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring")] THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET]], ALL_TAC] THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"X:B->bool") THEN REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN EQ_TAC THENL [DISCH_THEN (X_CHOOSE_THEN (← q r"y:B") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"ring_coset b Q (inverse (f:B->B) y)") THEN ASM_SIMP_TAC [] THEN EXISTS_TAC (← q r"inverse (f:B->B) y") THEN ASM_SIMP_TAC [], DISCH_THEN (X_CHOOSE_THEN (← q r"Y:B->bool") (CONJUNCTS_THEN2 SUBST1_TAC (X_CHOOSE_THEN (← q r"x:B") STRIP_ASSUME_TAC))) THEN EXISTS_TAC (← q r"(f:B->B) x") THEN ASM_SIMP_TAC []])

  let DECOMPOSITION_GROUP_IMAGE_RING_COSET ← prove
    r"!(h:A->B) k l b Q f x.
        subring_generated l (ring_carrier b) = b /\ ring_ideal b Q /\
        f IN group_carrier(decomposition_group(k,l) h Q) /\
        x IN ring_carrier b
        ==> IMAGE f (ring_coset b Q x) = ring_coset b Q (f x)"
    (REPEAT GEN_TAC THEN REWRITE_TAC [DECOMPOSITION_GROUP, IN_ELIM_THM] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"f:B->B"), (← q r"x:B")] GALOIS_GROUP_IMAGE_RING_COSET) THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET])

  -- @@RETURN BEGIN
  return { GALOIS_GROUP_SUBRING_IMAGE, GALOIS_GROUP_PRIME_IDEAL_IMAGE,
           GALOIS_GROUP_IMAGE_RING_COSET, GALOIS_GROUP_ACTION_SUBRING,
           GALOIS_GROUP_TRANSITIVE_PRIME_IDEALS, GALOIS_GROUP_ORBIT_MAXIMAL_IDEAL,
           decomposition_group, inertia_group, DECOMPOSITION_GROUP,
           DECOMPOSITION_GROUP_SUBRING_IMAGE, INERTIA_GROUP,
           INERTIA_GROUP_SUBGROUP_OF_DECOMPOSITION_GROUP, DECOMPOSITION_GROUP_INDEX,
           DECOMPOSITION_GROUP_CONJUGATE, INERTIA_GROUP_CONJUGATE,
           CARD_DECOMPOSITION_GROUP_CONJUGATE, SUBRING_GENERATED_QUOTIENT_RING_IMAGE,
           GALOIS_GROUP_QUOTIENT_RING_IMAGE, DECOMPOSITION_GROUP_IMAGE_RING_COSET }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- decomposition.ml phrases from line 778 to 1101                         -/
/- ---------------------------------------------------------------------- -/

structure Decomposition02 where
  -- @@FIELDS
  DECOMPOSITION_GROUP_RESIDUE_AUTOMORPHISM : thm
  DECOMPOSITION_GROUP_RESIDUE_HOMOMORPHISM : thm
  INERTIA_GROUP_NORMAL_SUBGROUP : thm
  GALOIS_GROUP_RESIDUE_CONJUGATE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDecomposition02 [HolBase] (D : DecompositionDeps) (BDecomposition01 : Decomposition01) :
    ExceptT String IO Decomposition02 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_TAC, TAUT, .. } := D
  let { EXTENSION, FINITE_GALOIS_GROUP, FINITE_IMAGE, FIXED_FIELD_GALOIS_GROUP,
        FORALL_IN_GSPEC, FORALL_IN_IMAGE, FUN_EQ_THM, GALOIS_GROUP,
        GALOIS_GROUP_COMPOSE, GALOIS_GROUP_FIXES, GALOIS_GROUP_I,
        GALOIS_GROUP_IMAGE_INVERSE, GALOIS_GROUP_INVERSE, GALOIS_GROUP_PERMUTES,
        GROUP_HOMOMORPHISM, IMAGE_o, IN_ELIM_THM, IN_FIXED_FIELD, IN_GALOIS_GROUP,
        IN_IMAGE, IN_RING_IDEAL_0, IN_RING_POLYNOMIAL_CARRIER_COMPOSE, I_THM,
        MONO_EXISTS, NORMAL_SUBGROUP_GROUP_KERNEL, PERMUTES_BIJECTIONS,
        PERMUTES_INVERSES, .. } := D.core1
  let { PERMUTES_IN_IMAGE, POLY_EVAL_CONST, POLY_EVAL_HOMOMORPHIC_IMAGE,
        POLY_EVAL_RING_PRODUCT, POLY_EVAL_SUB, POLY_EVAL_VAR,
        POLY_X_MINUS_A_IN_CARRIER, PRIME_IMP_RING_IDEAL, QUOTIENT_RING_0,
        QUOTIENT_RING_CARRIER, QUOTIENT_RING_UNIVERSAL,
        RING_CARRIER_SUBRING_GENERATED_SUBSET, RING_COSET_EQ, RING_COSET_EQ_IDEAL,
        RING_HOMOMORPHISMS_EQ_FROM_SUBRING_GENERATED, RING_HOMOMORPHISM_0,
        RING_HOMOMORPHISM_COMPOSE, RING_HOMOMORPHISM_EQ, RING_HOMOMORPHISM_I,
        RING_HOMOMORPHISM_RING_COSET, RING_IDEAL_IMP_SUBSET,
        RING_ISOMORPHISM_IMP_HOMOMORPHISM, RING_POLYNOMIAL_CONST, RING_POLYNOMIAL_VAR,
        RING_PRODUCT, RING_PRODUCT_EQ, RING_PRODUCT_IN_PRIME_IDEAL,
        RING_PRODUCT_X_MINUS_A_IN_FIXED_FIELD, RING_SUB, RING_SUB_REFL,
        RING_SUB_SUBRING_GENERATED, SIMPLE_IMAGE, SUBRING_GENERATED_INC_GEN, SUBSET,
        SUBSET_ANTISYM, group_kernel, o_THM, ring_automorphism, ring_isomorphism,
        ring_isomorphisms, ring_kernel, .. } := D.core2
  let { DECOMPOSITION_GROUP, DECOMPOSITION_GROUP_IMAGE_RING_COSET,
        DECOMPOSITION_GROUP_SUBRING_IMAGE, GALOIS_GROUP_SUBRING_IMAGE, INERTIA_GROUP, .. } := BDecomposition01
  -- @@SCOPE END

  let DECOMPOSITION_GROUP_RESIDUE_AUTOMORPHISM ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ q /\ (q ==> r) ==> p /\ q /\ r")
    prove
      r"!(h:A->B) k l b Q f.
          subring_generated l (ring_carrier b) = b /\
          (!f. f IN group_carrier(decomposition_group(k,l) h Q)
               ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
          ring_ideal b Q /\ f IN group_carrier(decomposition_group(k,l) h Q)
          ==> (!x. x IN ring_carrier b
                   ==> (\X. if X IN ring_carrier(quotient_ring b Q)
                            then IMAGE f X else X)
                       (ring_coset b Q x) = ring_coset b Q (f x)) /\
              (\X. if X IN ring_carrier(quotient_ring b Q) then IMAGE f X else X)
              permutes ring_carrier(quotient_ring b Q) /\
              ring_automorphism (quotient_ring b Q)
               (\X. if X IN ring_carrier(quotient_ring b Q)
                    then IMAGE f X else X)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!g x. g IN group_carrier(decomposition_group(k,l) (h:A->B) Q) /\
            x IN ring_carrier b
            ==> g x IN ring_carrier b /\
                ring_coset b Q x IN ring_carrier(quotient_ring b Q) /\
                (\X. if X IN ring_carrier(quotient_ring b Q)
                     then IMAGE g X else X)
                (ring_coset b Q x) = ring_coset b Q (g x)") ASSUME_TAC THENL [REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"IMAGE (g:B->B) (ring_carrier b) SUBSET ring_carrier b /\
        g IN group_carrier(galois_group(k,l) (h:A->B)) /\ IMAGE g Q = Q") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [] THEN UNDISCH_TAC (← q r"g IN group_carrier(decomposition_group(k,l) (h:A->B) Q)") THEN SIMP_TAC [DECOMPOSITION_GROUP, IN_ELIM_THM], ALL_TAC] THEN MATCH_MP_TAC r1 THEN REPEAT CONJ_TAC THENL [ASM SET_TAC [], ASM_SIMP_TAC [QUOTIENT_RING_CARRIER] THEN ASM SET_TAC [], DISCH_TAC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC DECOMPOSITION_GROUP_IMAGE_RING_COSET THEN MAP_EVERY EXISTS_TAC [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring")] THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"!g. g IN group_carrier(decomposition_group(k,l) (h:A->B) Q)
          ==> ring_homomorphism(quotient_ring b Q,quotient_ring b Q)
               (\X. if X IN ring_carrier(quotient_ring b Q)
                    then IMAGE g X else X)") ASSUME_TAC THENL [X_GEN_TAC (← q r"g:B->B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"IMAGE (g:B->B) (ring_carrier b) SUBSET ring_carrier b /\
        g IN group_carrier(galois_group(k,l) (h:A->B)) /\ IMAGE g Q = Q") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [] THEN UNDISCH_TAC (← q r"g IN group_carrier(decomposition_group(k,l) (h:A->B) Q)") THEN SIMP_TAC [DECOMPOSITION_GROUP, IN_ELIM_THM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"g:B->B")] DECOMPOSITION_GROUP_SUBRING_IMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"quotient_ring b (Q:B->bool)"), (← q r"Q:B->bool"), (← q r"ring_coset b Q o (g:B->B)")] QUOTIENT_RING_UNIVERSAL) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC (← q r"b:B ring") THEN ASM_SIMP_TAC [RING_ISOMORPHISM_IMP_HOMOMORPHISM, RING_HOMOMORPHISM_RING_COSET], FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_IDEAL_IMP_SUBSET)) THEN REWRITE_TAC [SUBSET, ring_kernel, IN_ELIM_THM, o_THM] THEN X_GEN_TAC (← q r"q:B") THEN DISCH_TAC THEN CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [QUOTIENT_RING_0] THEN wPart Except.ok (lhand o rand) RING_COSET_EQ_IDEAL THEN ANTS_TAC THENL [ASM SET_TAC [], DISCH_THEN SUBST1_TAC] THEN ASM SET_TAC []], DISCH_THEN (X_CHOOSE_THEN (← q r"g':(B->bool)->(B->bool)") STRIP_ASSUME_TAC) THEN MATCH_MP_TAC RING_HOMOMORPHISM_EQ THEN EXISTS_TAC (← q r"g':(B->bool)->(B->bool)") THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, FORALL_IN_GSPEC] THEN ASM_SIMP_TAC [o_THM] THEN X_GEN_TAC (← q r"a:B") THEN DISCH_TAC THEN MATCH_MP_TAC DECOMPOSITION_GROUP_IMAGE_RING_COSET THEN MAP_EVERY EXISTS_TAC [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring")] THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"inverse f IN group_carrier(decomposition_group(k,l) (h:A->B) Q) /\
      !x. inverse f ((f:B->B) x) = x /\ f (inverse f x) = x") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"f IN group_carrier(decomposition_group(k,l) (h:A->B) Q)") THEN REWRITE_TAC [DECOMPOSITION_GROUP, IN_ELIM_THM] THEN STRIP_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_GROUP_PERMUTES)) THEN DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP PERMUTES_INVERSES)) THEN ASM_MESON_TAC [GALOIS_GROUP_INVERSE, GALOIS_GROUP_IMAGE_INVERSE], ALL_TAC] THEN CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x. x IN ring_carrier b
          ==> f x IN ring_carrier b /\ inverse f x IN ring_carrier b /\
              ring_coset b Q x IN ring_carrier(quotient_ring b Q) /\
              IMAGE f (ring_coset b Q x) = ring_coset b Q (f x) /\
              IMAGE (inverse f) (ring_coset b Q x) =
              ring_coset b (Q:B->bool) (inverse f x)") ASSUME_TAC THENL [X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"f:B->B"), (← q r"x:B")] DECOMPOSITION_GROUP_IMAGE_RING_COSET) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"inverse f:B->B"), (← q r"x:B")] DECOMPOSITION_GROUP_IMAGE_RING_COSET) THEN ASM_REWRITE_TAC [] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!X. X IN ring_carrier(quotient_ring b Q)
          ==> ?x. x IN ring_carrier b /\ X = ring_coset b (Q:B->bool) x") ASSUME_TAC THENL [ASM_SIMP_TAC [QUOTIENT_RING_CARRIER] THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!X. (X IN ring_carrier(quotient_ring b Q)
           ==> (\X. if X IN ring_carrier(quotient_ring b Q)
                    then IMAGE f X else X) X
               IN ring_carrier(quotient_ring b Q) /\
               (\X. if X IN ring_carrier(quotient_ring b Q)
                    then IMAGE (inverse f) X else X) X
               IN ring_carrier(quotient_ring b Q)) /\
          (\X. if X IN ring_carrier(quotient_ring b Q) then IMAGE f X else X)
           ((\X. if X IN ring_carrier(quotient_ring b Q)
                 then IMAGE (inverse f) X else X) X) = X /\
          (\X. if X IN ring_carrier(quotient_ring b Q)
               then IMAGE (inverse f) X else X)
           ((\X. if X IN ring_carrier(quotient_ring b Q)
                 then IMAGE (f:B->B) X else X) X) = X") ASSUME_TAC THENL [X_GEN_TAC (← q r"X:B->bool") THEN REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"X IN ring_carrier(quotient_ring b (Q:B->bool))") THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MP_TAC o (← do let c := (← ASSUME (← q r"X IN ring_carrier(quotient_ring b (Q:B->bool))")); pure (fun th => MATCH_MP th c))) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"x:B") (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN ASM_SIMP_TAC [], ALL_TAC] THEN CONJ_TAC THENL [MATCH_MP_TAC PERMUTES_BIJECTIONS THEN EXISTS_TAC (← q r"\X. if X IN ring_carrier(quotient_ring b Q)
                      then IMAGE (inverse f) X else (X:B->bool)") THEN ASM_SIMP_TAC [] THEN REWRITE_TAC [] THEN MESON_TAC [], REWRITE_TAC [ring_automorphism, ring_isomorphism] THEN EXISTS_TAC (← q r"\X. if X IN ring_carrier(quotient_ring b Q)
                      then IMAGE (inverse f) X else (X:B->bool)") THEN ASM_SIMP_TAC [ring_isomorphisms]])

  let DECOMPOSITION_GROUP_RESIDUE_HOMOMORPHISM ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r21 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!(h:A->B) k l b Q.
          subring_generated l (ring_carrier b) = b /\
          (!f. f IN group_carrier(decomposition_group(k,l) h Q)
               ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
          ring_ideal b Q
          ==> group_homomorphism
               (decomposition_group(k,l) h Q,
                galois_group
                 (subring_generated (quotient_ring b Q)
                   (IMAGE (ring_coset b Q o h)
                          {a | a IN ring_carrier k /\ h a IN ring_carrier b}),
                  quotient_ring b Q) I)
               (\f X. if X IN ring_carrier(quotient_ring b Q)
                      then IMAGE f X else X) /\
              group_kernel
               (decomposition_group(k,l) h Q,
                galois_group
                 (subring_generated (quotient_ring b Q)
                   (IMAGE (ring_coset b Q o h)
                          {a | a IN ring_carrier k /\ h a IN ring_carrier b}),
                  quotient_ring b Q) I)
               (\f X. if X IN ring_carrier(quotient_ring b Q)
                      then IMAGE f X else X) =
              group_carrier(inertia_group(k,l) h b Q)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN ABBREV_TAC (← q r"kP = subring_generated (quotient_ring b Q)
            (IMAGE (ring_coset b Q o (h:A->B))
                   {a | a IN ring_carrier k /\ h a IN ring_carrier b})") THEN SUBGOAL_THEN (← q r"!f. f IN group_carrier(decomposition_group(k,l) (h:A->B) Q)
          ==> (!x. x IN ring_carrier b
                   ==> (\X. if X IN ring_carrier(quotient_ring b Q)
                            then IMAGE f X else X)
                       (ring_coset b Q x) = ring_coset b Q (f x)) /\
              (\X. if X IN ring_carrier(quotient_ring b Q) then IMAGE f X else X)
              permutes ring_carrier(quotient_ring b Q) /\
              ring_automorphism (quotient_ring b Q)
               (\X. if X IN ring_carrier(quotient_ring b Q)
                    then IMAGE f X else X)") (LABEL_TAC "rho") THENL [X_GEN_TAC (← q r"f:B->B") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"f:B->B")] DECOMPOSITION_GROUP_RESIDUE_AUTOMORPHISM) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MATCH_MP_TAC r21 THEN CONJ_TAC THENL [REWRITE_TAC [GROUP_HOMOMORPHISM, SUBSET, FORALL_IN_IMAGE] THEN REWRITE_TAC [(← CONJUNCT2 DECOMPOSITION_GROUP), (← CONJUNCT2 GALOIS_GROUP)] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"f:B->B") THEN DISCH_TAC THEN USE_THEN "rho" (MP_TAC o (← do let c := (← ASSUME (← q r"f IN group_carrier(decomposition_group(k,l) (h:A->B) Q)")); pure (fun th => MATCH_MP th c))) THEN DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [])) THEN ASM_REWRITE_TAC [IN_GALOIS_GROUP, I_THM] THEN EXPAND_TAC "kP" THEN MP_TAC (← ISPECL [(← q r"\X. if X IN ring_carrier(quotient_ring b Q)
               then IMAGE (f:B->B) X else X"), (← q r"I:(B->bool)->(B->bool)"), (← q r"quotient_ring b (Q:B->bool)"), (← q r"quotient_ring b (Q:B->bool)"), (← q r"IMAGE (ring_coset b Q o (h:A->B))
                 {a | a IN ring_carrier k /\ h a IN ring_carrier b}")] RING_HOMOMORPHISMS_EQ_FROM_SUBRING_GENERATED) THEN REWRITE_TAC [I_THM, RING_HOMOMORPHISM_I] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC [ring_automorphism, RING_ISOMORPHISM_IMP_HOMOMORPHISM], REWRITE_TAC [IN_IMAGE, IN_ELIM_THM, o_THM] THEN X_GEN_TAC (← q r"X:B->bool") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"a:A") STRIP_ASSUME_TAC)) THEN ASM_SIMP_TAC [] THEN UNDISCH_TAC (← q r"f IN group_carrier(decomposition_group(k,l) (h:A->B) Q)") THEN REWRITE_TAC [DECOMPOSITION_GROUP, IN_ELIM_THM] THEN ASM_MESON_TAC [GALOIS_GROUP_FIXES]], MAP_EVERY X_GEN_TAC [(← q r"f:B->B"), (← q r"g:B->B")] THEN STRIP_TAC THEN USE_THEN "rho" (MP_TAC o (← do let c := (← ASSUME (← q r"g IN group_carrier(decomposition_group(k,l) (h:A->B) Q)")); pure (fun th => MATCH_MP th c))) THEN DISCH_THEN (ASSUME_TAC o ((MATCH_MP PERMUTES_IN_IMAGE) o (CONJUNCT1 o CONJUNCT2))) THEN REWRITE_TAC [FUN_EQ_THM, o_THM] THEN X_GEN_TAC (← q r"X:B->bool") THEN ASM_CASES_TAC (← q r"X IN ring_carrier(quotient_ring b (Q:B->bool))") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"IMAGE (g:B->B) X IN ring_carrier(quotient_ring b Q)") (fun th => REWRITE_TAC [th, IMAGE_o]) THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"X:B->bool"))) THEN ASM_REWRITE_TAC []], DISCH_TAC THEN REWRITE_TAC [group_kernel, (← CONJUNCT2 GALOIS_GROUP)] THEN ASM_SIMP_TAC [(← CONJUNCT1 INERTIA_GROUP)] THEN SUBGOAL_THEN (← q r"ring_sub b = ring_sub (l:B ring)") ASSUME_TAC THENL [UNDISCH_TAC (← q r"subring_generated l (ring_carrier b) = (b:B ring)") THEN DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [(← SYM th)])) THEN REWRITE_TAC [RING_SUB_SUBRING_GENERATED], ALL_TAC] THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"f:B->B") THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_CASES_TAC (← q r"f IN group_carrier(decomposition_group(k,l) (h:A->B) Q)") THEN ASM_REWRITE_TAC [] THENL [ALL_TAC, POP_ASSUM MP_TAC THEN REWRITE_TAC [DECOMPOSITION_GROUP, IN_ELIM_THM] THEN MESON_TAC []] THEN USE_THEN "rho" (MP_TAC o (CONJUNCT1 o (← do let c := (← ASSUME (← q r"f IN group_carrier(decomposition_group(k,l) (h:A->B) Q)")); pure (fun th => MATCH_MP th c)))) THEN REWRITE_TAC [] THEN DISCH_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o ((REWRITE_RULE [DECOMPOSITION_GROUP, IN_ELIM_THM]) o (checkM (fun th => (do let z20 ← (q r"f IN group_carrier(decomposition_group(k,l) (h:A->B) Q)"); let z19 ← (do let z18 ← (pure th); pure (concl z18)); pure (z19 == z20)))))) THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"IMAGE (f:B->B) (ring_carrier b) SUBSET ring_carrier b") MP_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN DISCH_TAC THEN GEN_REWRITE_TAC LAND_CONV [FUN_EQ_THM] THEN REWRITE_TAC [I_THM] THEN EQ_TAC THENL [DISCH_TAC THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"ring_coset b Q (x:B)"))) THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"x:B")) o ((checkM (fun z15 => (do let z16 ← (do let z17 ← (pure z15); pure (concl z17)); pure (is_forall z16)))) o (checkM (fun th => (do let z8 ← (do let z9 ← (do pure (← SPEC (← q r"x:B") th)); pure (concl z9)); canM (fun z10 => (do let z11 ← (pure z10); find_termM (fun z12 => (do let z14 ← (pure z12); let z13 ← (q r"ring_coset b Q ((f:B->B) x)"); pure (z13 == z14))) z11)) z8)))))) THEN SUBGOAL_THEN (← q r"ring_coset b Q (x:B) IN ring_carrier(quotient_ring b Q)") (fun th => ASM_REWRITE_TAC [th]) THENL [ASM_SIMP_TAC [QUOTIENT_RING_CARRIER] THEN ASM SET_TAC [], ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [RING_COSET_EQ], DISCH_TAC THEN X_GEN_TAC (← q r"X:B->bool") THEN COND_CASES_TAC THEN REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"?x. x IN ring_carrier b /\ X = ring_coset b (Q:B->bool) x") (X_CHOOSE_THEN (← q r"x:B") (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THENL [UNDISCH_TAC (← q r"X IN ring_carrier(quotient_ring b (Q:B->bool))") THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER] THEN SET_TAC [], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"x:B")) o (checkM (fun th => (do let z1 ← (do let z2 ← (do pure (← SPEC (← q r"x:B") th)); pure (concl z2)); canM (fun z3 => (do let z4 ← (pure z3); find_termM (fun z5 => (do let z7 ← (pure z5); let z6 ← (q r"ring_coset b Q ((f:B->B) x)"); pure (z6 == z7))) z4)) z1))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [RING_COSET_EQ]]])

  let INERTIA_GROUP_NORMAL_SUBGROUP ← prove
    r"!(h:A->B) k l b Q.
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        ring_ideal b Q
        ==> group_carrier(inertia_group(k,l) h b Q) normal_subgroup_of
            decomposition_group(k,l) h Q"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool")] DECOMPOSITION_GROUP_RESIDUE_HOMOMORPHISM) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [DECOMPOSITION_GROUP, IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN DISCH_THEN (CONJUNCTS_THEN2 (MP_TAC o (MATCH_MP NORMAL_SUBGROUP_GROUP_KERNEL)) SUBST1_TAC) THEN REWRITE_TAC [])

  let GALOIS_GROUP_RESIDUE_CONJUGATE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!(h:A->B) k l b Q s x.
          finite_extension(k,l) h /\ galois_extension(k,l) h /\
          subring_generated l (ring_carrier b) = b /\
          (!f. f IN group_carrier(galois_group(k,l) h)
               ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
          prime_ideal b Q /\ x IN ring_carrier b /\
          s IN group_carrier
                (galois_group
                  (subring_generated (quotient_ring b Q)
                    (IMAGE (ring_coset b Q o h)
                           {a | a IN ring_carrier k /\ h a IN ring_carrier b}),
                   quotient_ring b Q) I)
          ==> ?f. f IN group_carrier(galois_group(k,l) h) /\
                  s(ring_coset b Q x) = ring_coset b Q (f x)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"FINITE(group_carrier(galois_group(k,l) (h:A->B)))") ASSUME_TAC THENL [ASM_SIMP_TAC [FINITE_GALOIS_GROUP], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_carrier b SUBSET ring_carrier(l:B ring)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"ring_carrier(b:B ring)")] RING_CARRIER_SUBRING_GENERATED_SUBSET) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"t = {(f:B->B) x | f IN group_carrier(galois_group(k,l) (h:A->B))}") THEN SUBGOAL_THEN (← q r"FINITE(t:B->bool) /\ t SUBSET ring_carrier b /\ (x:B) IN t /\
      !g. g IN group_carrier(galois_group(k,l) (h:A->B))
          ==> ring_automorphism b g /\ IMAGE g t = t") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"{(f:B->B) x | f IN group_carrier(galois_group(k,l) (h:A->B))} = t") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [SIMPLE_IMAGE, FINITE_IMAGE] THEN REPEAT CONJ_TAC THENL [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"f:B->B") THEN DISCH_TAC THEN UNDISCH_TAC (← q r"!f. f IN group_carrier(galois_group(k,l) (h:A->B))
              ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b") THEN DISCH_THEN (MP_TAC o (SPEC (← q r"f:B->B"))) THEN ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN ASM_SIMP_TAC [], REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC (← q r"I:B->B") THEN REWRITE_TAC [GALOIS_GROUP_I, I_THM], X_GEN_TAC (← q r"g:B->B") THEN DISCH_TAC THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"g:B->B")] GALOIS_GROUP_SUBRING_IMAGE) THEN ASM_SIMP_TAC [ring_automorphism], REWRITE_TAC [(← GSYM IMAGE_o)] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, o_THM] THEN CONJ_TAC THEN X_GEN_TAC (← q r"f:B->B") THEN DISCH_TAC THEN REWRITE_TAC [IN_IMAGE, o_THM] THENL [EXISTS_TAC (← q r"(g:B->B) o (f:B->B)") THEN ASM_SIMP_TAC [GALOIS_GROUP_COMPOSE, o_THM], EXISTS_TAC (← q r"inverse(g:B->B) o (f:B->B)") THEN ASM_SIMP_TAC [GALOIS_GROUP_COMPOSE, GALOIS_GROUP_INVERSE, o_THM] THEN FIRST_ASSUM (MP_TAC o ((MATCH_MP GALOIS_GROUP_PERMUTES) o (checkM (fun th => (do let z20 ← (q r"g IN group_carrier(galois_group(k,l) (h:A->B))"); let z19 ← (do let z18 ← (pure th); pure (concl z18)); pure (z19 == z20)))))) THEN DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP PERMUTES_INVERSES)) THEN ASM_REWRITE_TAC []]]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"group_carrier(galois_group(k,l) (h:A->B))"), (← q r"t:B->bool")] RING_PRODUCT_X_MINUS_A_IN_FIXED_FIELD) THEN ASM_SIMP_TAC [] THEN ABBREV_TAC (← q r"p = ring_product (poly_ring b (:1)) t
            (\c. poly_sub b (poly_var b one) (poly_const (b:B ring) c))") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"p IN ring_carrier(poly_ring (b:B ring) (:1))") ASSUME_TAC THENL [EXPAND_TAC "p" THEN REWRITE_TAC [RING_PRODUCT], ALL_TAC] THEN SUBGOAL_THEN (← q r"!m. (p:(1->num)->B) m IN ring_carrier b /\
          ?a. a IN ring_carrier k /\ (h:A->B) a = p m") ASSUME_TAC THENL [X_GEN_TAC (← q r"m:1->num") THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"m:1->num"))) THEN REWRITE_TAC [IN_FIXED_FIELD] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(p:(1->num)->B) m IN ring_carrier l") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring")] FIXED_FIELD_GALOIS_GROUP) THEN ASM_REWRITE_TAC [EXTENSION, IN_FIXED_FIELD, IN_IMAGE] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"(p:(1->num)->B) m"))) THEN ASM_REWRITE_TAC [] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_homomorphism(b,quotient_ring b Q) (ring_coset b (Q:B->bool))") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_COSET], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o ((REWRITE_RULE [IN_GALOIS_GROUP, I_THM]) o (checkM (fun th => (do let z11 ← (do let z12 ← (pure th); pure (concl z12)); canM (fun z13 => (do let z14 ← (pure z13); find_termM (fun z15 => (do let z17 ← (pure z15); let z16 ← (q r"s:(B->bool)->(B->bool)"); pure (z16 == z17))) z14)) z11))))) THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fix"))) THEN SUBGOAL_THEN (← q r"ring_homomorphism(quotient_ring b Q,quotient_ring b Q)
        (s:(B->bool)->(B->bool))") ASSUME_TAC THENL [ASM_MESON_TAC [ring_automorphism, RING_ISOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN SUBGOAL_THEN (← q r"(s:(B->bool)->(B->bool)) o (ring_coset b Q o (p:(1->num)->B)) =
      ring_coset b (Q:B->bool) o p") ASSUME_TAC THENL [GEN_REWRITE_TAC id [FUN_EQ_THM] THEN X_GEN_TAC (← q r"m:1->num") THEN REWRITE_TAC [o_THM] THEN USE_THEN "fix" MATCH_MP_TAC THEN MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN FIRST_X_ASSUM (STRIP_ASSUME_TAC o ((SPEC (← q r"m:1->num")) o (checkM (fun th => (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); canM (fun z4 => (do let z5 ← (pure z4); find_termM (fun z6 => (do let z8 ← (pure z6); let z7 ← (q r"p:(1->num)->B"); pure (z7 == z8))) z5)) z2) then (do let z9 ← (do let z10 ← (pure th); pure (concl z10)); pure (is_forall z9)) else pure false))))) THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, IN_ELIM_THM, IN_IMAGE, o_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!y:B. y IN ring_carrier b
            ==> poly_eval b p y = ring_product b t (\c. ring_sub b y c)") ASSUME_TAC THENL [X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN UNDISCH_TAC (← q r"ring_product (poly_ring b (:1)) t
          (\c. poly_sub b (poly_var b one) (poly_const (b:B ring) c)) = p") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN wPart lhand (lhand o rand) POLY_EVAL_RING_PRODUCT THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC POLY_X_MINUS_A_IN_CARRIER THEN ASM SET_TAC [], DISCH_THEN SUBST1_TAC] THEN MATCH_MP_TAC RING_PRODUCT_EQ THEN X_GEN_TAC (← q r"c:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(c:B) IN ring_carrier b") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [POLY_EVAL_SUB, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_CONST, POLY_EVAL_VAR, POLY_EVAL_CONST], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_coset b Q (x:B) IN ring_carrier(quotient_ring b Q) /\
      s(ring_coset b Q x) IN ring_carrier(quotient_ring b (Q:B->bool))") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r1 THEN CONJ_TAC THENL [ASM_SIMP_TAC [QUOTIENT_RING_CARRIER] THEN ASM SET_TAC [], ASM_MESON_TAC [PERMUTES_IN_IMAGE]], ALL_TAC] THEN SUBGOAL_THEN (← q r"?y. y IN ring_carrier b /\
          s(ring_coset b Q x) = ring_coset b (Q:B->bool) y") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"s(ring_coset b Q x) IN ring_carrier(quotient_ring b (Q:B->bool))") THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER] THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_coset b Q (ring_product b t (\c. ring_sub b x c)) = (Q:B->bool)") ASSUME_TAC THENL [wPart Except.ok (lhand o rand) RING_COSET_EQ_IDEAL THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_PRODUCT], DISCH_THEN SUBST1_TAC] THEN MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"t:B->bool"), (← q r"\c. ring_sub b (x:B) c")] RING_PRODUCT_IN_PRIME_IDEAL) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"c:B") THEN DISCH_TAC THEN MATCH_MP_TAC RING_SUB THEN ASM_MESON_TAC [SUBSET], DISCH_THEN SUBST1_TAC] THEN EXISTS_TAC (← q r"x:B") THEN ASM_SIMP_TAC [RING_SUB_REFL, IN_RING_IDEAL_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"(s:(B->bool)->(B->bool)) Q = Q") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"quotient_ring b (Q:B->bool)"), (← q r"quotient_ring b (Q:B->bool)"), (← q r"s:(B->bool)->(B->bool)")] RING_HOMOMORPHISM_0) THEN ASM_SIMP_TAC [QUOTIENT_RING_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_coset b Q (ring_product b t (\c. ring_sub b y c)) = (Q:B->bool)") MP_TAC THENL [SUBGOAL_THEN (← q r"ring_coset b Q (poly_eval b p (x:B)) = (Q:B->bool)") ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_product b t (\c. ring_sub b y c) = poly_eval b p (y:B)") SUBST1_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"quotient_ring b (Q:B->bool)"), (← q r"y:B"), (← q r"ring_coset b (Q:B->bool)"), (← q r"p:(1->num)->B")] POLY_EVAL_HOMOMORPHIC_IMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN UNDISCH_TAC (← q r"s(ring_coset b Q x) = ring_coset b (Q:B->bool) y") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN UNDISCH_TAC (← q r"(s:(B->bool)->(B->bool)) o (ring_coset b Q o (p:(1->num)->B)) =
        ring_coset b (Q:B->bool) o p") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"quotient_ring b (Q:B->bool)"), (← q r"quotient_ring b (Q:B->bool)"), (← q r"ring_coset b Q (x:B)"), (← q r"s:(B->bool)->(B->bool)"), (← q r"ring_coset b (Q:B->bool) o (p:(1->num)->B)")] POLY_EVAL_HOMOMORPHIC_IMAGE) THEN ANTS_TAC THENL [ASM_SIMP_TAC [] THEN MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN EXISTS_TAC (← q r"b:B ring") THEN ASM_REWRITE_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"quotient_ring b (Q:B->bool)"), (← q r"x:B"), (← q r"ring_coset b (Q:B->bool)"), (← q r"p:(1->num)->B")] POLY_EVAL_HOMOMORPHIC_IMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN wPart lhand (lhand o rand) RING_COSET_EQ_IDEAL THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_PRODUCT], DISCH_THEN SUBST1_TAC] THEN MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"t:B->bool"), (← q r"\c. ring_sub b (y:B) c")] RING_PRODUCT_IN_PRIME_IDEAL) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"c:B") THEN DISCH_TAC THEN MATCH_MP_TAC RING_SUB THEN ASM_MESON_TAC [SUBSET], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:B") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(c:B) IN ring_carrier b") ASSUME_TAC THENL [ASM_MESON_TAC [SUBSET], ALL_TAC] THEN UNDISCH_TAC (← q r"(c:B) IN t") THEN EXPAND_TAC "t" THEN REWRITE_TAC [IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"f:B->B") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [RING_COSET_EQ])

  -- @@RETURN BEGIN
  return { DECOMPOSITION_GROUP_RESIDUE_AUTOMORPHISM,
           DECOMPOSITION_GROUP_RESIDUE_HOMOMORPHISM, INERTIA_GROUP_NORMAL_SUBGROUP,
           GALOIS_GROUP_RESIDUE_CONJUGATE }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- decomposition.ml phrases from line 1328 to 1741                        -/
/- ---------------------------------------------------------------------- -/

structure Decomposition03 where
  -- @@FIELDS
  DECOMPOSITION_GROUP_RESIDUE_EPIMORPHISM : thm
  CARD_DECOMPOSITION_GROUP : thm
  EXTENSION_DEGREE_RESIDUE_CONJUGATE : thm
  frobenius_element : thm
  DECOMPOSITION_GROUP_FROBENIUS_EXISTS : thm
  FROBENIUS_ELEMENT : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDecomposition03 [HolBase] (D : DecompositionDeps) (BDecomposition01 : Decomposition01) (BDecomposition02 : Decomposition02) :
    ExceptT String IO Decomposition03 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, MESON_TAC, RING_RULE, SET_TAC, TAUT, new_definition, .. } := D
  let { CARD_EQ_0, CARD_EQ_CARD, CARD_EQ_GROUP_IMAGE_KERNEL, CARD_MUL_C,
        CARD_MUL_FINITE, CHINESE_REMAINDER_IDEALS, EQ_MULT_LCANCEL, EXTENSION,
        FIELD_EXTENSION_SUBRING_GENERATED_FINITE, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_IMP_NONTRIVIAL_RING, FIELD_QUOTIENT_RING, FINITE_FIELD_PRIMITIVE_ROOT,
        FINITE_GALOIS_GROUP, FINITE_IMAGE, FINITE_INTEGRAL_DOMAIN_IMP_FIELD,
        FINITE_SUBRING_GENERATED, FINITE_SUBSET, FORALL_IN_GSPEC, FORALL_IN_IMAGE,
        FUN_EQ_THM, FUN_IN_IMAGE, GALOIS_GROUP_COMPOSE, GALOIS_GROUP_FINITE_FIELD,
        GALOIS_GROUP_I, GALOIS_GROUP_IMAGE_INVERSE, GALOIS_GROUP_INVERSE,
        GALOIS_GROUP_PERMUTES, GALOIS_GROUP_RING_AUTOMORPHISM,
        GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET, GROUP_EPIMORPHISM_ALT, GROUP_ID,
        HAS_SIZE, IMAGE_I, IMAGE_o, IMP_CONJ, INTEGRAL_DOMAIN_SUBRING_GENERATED,
        IN_ELIM_THM, IN_GALOIS_GROUP, IN_IMAGE, IN_RING_IDEAL_ADD, IN_RING_IDEAL_SUB,
        IN_SING, I_DEF, I_THM, MAXIMAL_IDEAL_COMAXIMAL, MAXIMAL_IMP_PRIME_IDEAL,
        MAXIMAL_IMP_PROPER_IDEAL, MAXIMAL_IMP_RING_IDEAL, MEMBER_NOT_EMPTY,
        MONO_EXISTS, MULT_SYM, NOT_EXISTS_THM, PERMUTES_INJECTIVE, PERMUTES_INVERSES, .. } := D.core1
  let { PERMUTES_INVERSE_INVERSE, PERMUTES_IN_IMAGE, PRIME_IDEAL_IMP_SUBSET, PSUBSET,
        QUOTIENT_RING_0, QUOTIENT_RING_CARRIER, RIGHT_FORALL_IMP_THM, RING_0,
        RING_CARRIER_NONEMPTY, RING_CARRIER_SUBRING_GENERATED_SUBSET, RING_COSET_EQ,
        RING_COSET_EQ_IDEAL, RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_POW,
        RING_HOMOMORPHISM_RING_COSET, RING_HOMOMORPHISM_SUB, RING_IDEAL_IMP_SUBSET,
        RING_ISOMORPHISM_IMP_HOMOMORPHISM, RING_MONOMORPHISM_IMP_HOMOMORPHISM,
        RING_MONOMORPHISM_INCLUSION, RING_ORDER_0, RING_POW, RING_POW_IN_PRIME_IDEAL,
        RING_POW_SUBRING_GENERATED, RING_SUB_RZERO, RING_SUB_SUBRING_GENERATED,
        SELECT_UNIQUE, SIMPLE_IMAGE, SUBRING_GENERATED, SUBSET,
        TRIVIAL_RING_HAS_SIZE_1, field_extension, finite_extension, group_epimorphism,
        group_image, maximal_ideal, o_THM, pairwise, permutes, ring_automorphism, .. } := D.core2
  let { CARD_DECOMPOSITION_GROUP_CONJUGATE, DECOMPOSITION_GROUP,
        DECOMPOSITION_GROUP_IMAGE_RING_COSET, GALOIS_GROUP_PRIME_IDEAL_IMAGE,
        GALOIS_GROUP_QUOTIENT_RING_IMAGE, INERTIA_GROUP,
        SUBRING_GENERATED_QUOTIENT_RING_IMAGE, inertia_group, .. } := BDecomposition01
  let { DECOMPOSITION_GROUP_RESIDUE_AUTOMORPHISM,
        DECOMPOSITION_GROUP_RESIDUE_HOMOMORPHISM, GALOIS_GROUP_RESIDUE_CONJUGATE, .. } := BDecomposition02
  -- @@SCOPE END

  let DECOMPOSITION_GROUP_RESIDUE_EPIMORPHISM ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r35 ← TAUT (← q r"(~p ==> F) ==> p")
    let r36 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    let r49 ← ARITH_RULE (← q r"~(q = 0) /\ ~(q = 1) ==> ~(0 = q - 1)")
    prove
      r"!(h:A->B) k l b Q.
          finite_extension(k,l) h /\ galois_extension(k,l) h /\
          subring_generated l (ring_carrier b) = b /\
          (!f. f IN group_carrier(galois_group(k,l) h)
               ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
          maximal_ideal b Q /\ FINITE(ring_carrier(quotient_ring b Q))
          ==> group_epimorphism
               (decomposition_group(k,l) h Q,
                galois_group
                 (subring_generated (quotient_ring b Q)
                   (IMAGE (ring_coset b Q o h)
                          {a | a IN ring_carrier k /\ h a IN ring_carrier b}),
                  quotient_ring b Q) I)
               (\f X. if X IN ring_carrier(quotient_ring b Q)
                      then IMAGE f X else X)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!f. f IN group_carrier(decomposition_group(k,l) (h:A->B) Q)
          ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b") ASSUME_TAC THENL [REWRITE_TAC [DECOMPOSITION_GROUP, IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_PRIME_IDEAL)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_RING_IDEAL)) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool")] DECOMPOSITION_GROUP_RESIDUE_HOMOMORPHISM) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC [GROUP_EPIMORPHISM_ALT, group_image, SUBSET, IN_IMAGE] THEN X_GEN_TAC (← q r"s:(B->bool)->(B->bool)") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"field(quotient_ring b (Q:B->bool))") ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_QUOTIENT_RING], ALL_TAC] THEN MP_TAC (← ISPEC (← q r"quotient_ring b (Q:B->bool)") FINITE_FIELD_PRIMITIVE_ROOT) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"z:B->bool") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"~(z = ring_0(quotient_ring b (Q:B->bool)))") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"ring_order (quotient_ring b Q) (ring_0 (quotient_ring b Q)) =
        CARD(ring_carrier(quotient_ring b (Q:B->bool))) - 1") THEN ASM_SIMP_TAC [RING_ORDER_0, FIELD_IMP_NONTRIVIAL_RING] THEN MATCH_MP_TAC r49 THEN ASM_SIMP_TAC [CARD_EQ_0, RING_CARRIER_NONEMPTY] THEN ASM_MESON_TAC [HAS_SIZE, TRIVIAL_RING_HAS_SIZE_1, FIELD_IMP_NONTRIVIAL_RING], ALL_TAC] THEN SUBGOAL_THEN (← q r"?z0. z0 IN ring_carrier b /\ z = ring_coset b (Q:B->bool) z0") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"(z:B->bool) IN ring_carrier(quotient_ring b Q)") THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER] THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!g. g IN group_carrier(galois_group(k,l) (h:A->B))
          ==> maximal_ideal b (IMAGE g Q) /\ ring_ideal b (IMAGE g (Q:B->bool))") ASSUME_TAC THENL [X_GEN_TAC (← q r"g:B->B") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"g:B->B"), (← q r"Q:B->bool")] GALOIS_GROUP_PRIME_IDEAL_IMAGE) THEN ASM_SIMP_TAC [MAXIMAL_IMP_RING_IDEAL, PRIME_IDEAL_IMP_SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"?w. w IN ring_carrier b /\ ring_sub b w z0 IN Q /\
          !g. g IN group_carrier(galois_group(k,l) (h:A->B)) /\
              ~(IMAGE g Q = Q)
              ==> w IN IMAGE g (Q:B->bool)") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"{IMAGE g Q | g IN group_carrier(galois_group(k,l) (h:A->B))}"), (← q r"\i:B->bool. i"), (← q r"\i. if i = (Q:B->bool) then (z0:B) else ring_0(b:B ring)")] CHINESE_REMAINDER_IDEALS) THEN ANTS_TAC THENL [REWRITE_TAC [FORALL_IN_GSPEC, pairwise, IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN REPEAT CONJ_TAC THENL [ASM_SIMP_TAC [SIMPLE_IMAGE, FINITE_IMAGE, FINITE_GALOIS_GROUP], X_GEN_TAC (← q r"g:B->B") THEN DISCH_TAC THEN ASM_SIMP_TAC [] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [RING_0], X_GEN_TAC (← q r"g:B->B") THEN DISCH_TAC THEN X_GEN_TAC (← q r"g':B->B") THEN DISCH_TAC THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"maximal_ideal b (IMAGE (g:B->B) Q) /\
            maximal_ideal b (IMAGE (g':B->B) Q)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"IMAGE (g:B->B) Q"), (← q r"IMAGE (g':B->B) Q")] MAXIMAL_IDEAL_COMAXIMAL) THEN ANTS_TAC THENL [ASM_SIMP_TAC [MAXIMAL_IMP_RING_IDEAL], DISCH_THEN SUBST1_TAC] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"maximal_ideal b (IMAGE (g':B->B) Q)") THEN REWRITE_TAC [maximal_ideal, NOT_EXISTS_THM] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"IMAGE (g:B->B) Q")) o CONJUNCT2)) THEN ASM_SIMP_TAC [MAXIMAL_IMP_PROPER_IDEAL, PSUBSET] THEN ASM_MESON_TAC []], REWRITE_TAC [FORALL_IN_GSPEC] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"w:B") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"I:B->B"))) THEN REWRITE_TAC [GALOIS_GROUP_I, IMAGE_I], X_GEN_TAC (← q r"g:B->B") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"g:B->B"))) THEN ASM_SIMP_TAC [RING_SUB_RZERO]]], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_coset b Q (w:B) = z") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_COSET_EQ], ALL_TAC] THEN FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o (checkM (fun th => (do let z48 ← (q r"z = ring_coset b (Q:B->bool) z0"); let z47 ← (do let z46 ← (pure th); pure (concl z46)); pure (z47 == z48))))) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"s:(B->bool)->(B->bool)"), (← q r"w:B")] GALOIS_GROUP_RESIDUE_CONJUGATE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"f:B->B") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"f:B->B") THEN FIRST_X_ASSUM (MP_TAC o ((REWRITE_RULE [IN_GALOIS_GROUP, I_THM]) o (checkM (fun th => (do if ← (do let z37 ← (do let z38 ← (pure th); pure (concl z38)); canM (fun z39 => (do let z40 ← (pure z39); find_termM (fun z41 => (do let z43 ← (pure z41); let z42 ← (q r"s:(B->bool)->(B->bool)"); pure (z42 == z43))) z40)) z37) then (do pure !(← (do let z44 ← (do let z45 ← (pure th); pure (concl z45)); pure (is_eq z44)))) else pure false))))) THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_homomorphism(quotient_ring b Q,quotient_ring b Q)
        (s:(B->bool)->(B->bool)) /\
      s Q = Q") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r36 THEN CONJ_TAC THENL [ASM_MESON_TAC [ring_automorphism, RING_ISOMORPHISM_IMP_HOMOMORPHISM], DISCH_THEN (MP_TAC o (MATCH_MP RING_HOMOMORPHISM_0)) THEN ASM_SIMP_TAC [QUOTIENT_RING_0]], ALL_TAC] THEN SUBGOAL_THEN (← q r"f IN group_carrier(decomposition_group(k,l) (h:A->B) Q)") ASSUME_TAC THENL [REWRITE_TAC [DECOMPOSITION_GROUP, IN_ELIM_THM] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r35 THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o ((MATCH_MP GALOIS_GROUP_PERMUTES) o (checkM (fun th => (do let z34 ← (q r"f IN group_carrier(galois_group(k,l) (h:A->B))"); let z33 ← (do let z32 ← (pure th); pure (concl z32)); pure (z33 == z34)))))) THEN DISCH_THEN (fun th => tactic_of do pure (STRIP_ASSUME_TAC (← MATCH_MP PERMUTES_INVERSES th) THEN ASSUME_TAC (← MATCH_MP PERMUTES_INVERSE_INVERSE th))) THEN SUBGOAL_THEN (← q r"~(IMAGE (inverse f) Q = (Q:B->bool))") ASSUME_TAC THENL [DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"inverse(f:B->B)"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"Q:B->bool")] GALOIS_GROUP_IMAGE_INVERSE) THEN ASM_SIMP_TAC [GALOIS_GROUP_INVERSE], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"inverse(f:B->B)")) o (checkM (fun th => (do if ← (do let z23 ← (do let z24 ← (pure th); pure (concl z24)); canM (fun z25 => (do let z26 ← (pure z25); find_termM (fun z27 => (do let z29 ← (pure z27); let z28 ← (q r"w:B"); pure (z28 == z29))) z26)) z23) then (do let z30 ← (do let z31 ← (pure th); pure (concl z31)); pure (is_forall z30)) else pure false))))) THEN ASM_SIMP_TAC [GALOIS_GROUP_INVERSE, IN_IMAGE] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"q:B") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"ring_coset b Q ((f:B->B) w) = Q") MP_TAC THENL [ASM_REWRITE_TAC [] THEN wPart Except.ok (lhand o rand) RING_COSET_EQ_IDEAL THEN ANTS_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC []], ALL_TAC] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z17 ← (do let z18 ← (pure th); pure (concl z18)); pure (is_eq z17)) then (do let z22 ← (q r"(s:(B->bool)->(B->bool)) z"); let z21 ← (do let z19 ← (do let z20 ← (pure th); pure (concl z20)); liftExcept (lhand z19)); pure (z21 == z22)) else pure false))))) THEN UNDISCH_TAC (← q r"~(z = ring_0(quotient_ring b (Q:B->bool)))") THEN ASM_SIMP_TAC [QUOTIENT_RING_0] THEN ASM_MESON_TAC [PERMUTES_INJECTIVE], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"f:B->B")] DECOMPOSITION_GROUP_RESIDUE_AUTOMORPHISM) THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"IMAGE (f:B->B) Q = Q") ASSUME_TAC THENL [UNDISCH_TAC (← q r"f IN group_carrier(decomposition_group(k,l) (h:A->B) Q)") THEN SIMP_TAC [DECOMPOSITION_GROUP, IN_ELIM_THM], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_homomorphism(quotient_ring b Q,quotient_ring b Q)
       (\X. if X IN ring_carrier(quotient_ring b Q)
            then IMAGE (f:B->B) X else X)") ASSUME_TAC THENL [ASM_MESON_TAC [ring_automorphism, RING_ISOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN SUBGOAL_THEN (← q r"IMAGE (f:B->B) z = s z") ASSUME_TAC THENL [UNDISCH_TAC (← q r"ring_coset b Q (w:B) = z") THEN DISCH_THEN (SUBST_ALL_TAC o SYM) THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"w:B")) o (checkM (fun th => (do if ← (do let z8 ← (do let z9 ← (pure th); pure (concl z9)); pure (is_forall z8)) then (do let z10 ← (do let z11 ← (do pure (← SPEC (← q r"x:B") th)); pure (concl z11)); canM (fun z12 => (do let z13 ← (pure z12); find_termM (fun z14 => (do let z16 ← (pure z14); let z15 ← (q r"ring_coset b Q ((f:B->B) x)"); pure (z15 == z16))) z13)) z10) else pure false))))) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN GEN_REWRITE_TAC id [FUN_EQ_THM] THEN X_GEN_TAC (← q r"X:B->bool") THEN REWRITE_TAC [] THEN COND_CASES_TAC THENL [ALL_TAC, ASM_MESON_TAC [permutes]] THEN ASM_CASES_TAC (← q r"X = ring_0(quotient_ring b (Q:B->bool))") THENL [ASM_SIMP_TAC [QUOTIENT_RING_0], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"X:B->bool")) o (checkM (fun th => (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); canM (fun z3 => (do let z4 ← (pure z3); find_termM (fun z5 => (do let z7 ← (pure z5); let z6 ← (q r"ring_pow (quotient_ring b (Q:B->bool)) z"); pure (z6 == z7))) z4)) z1))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"n:num") (SUBST_ALL_TAC o SYM)) THEN MP_TAC (← ISPECL [(← q r"quotient_ring b (Q:B->bool)"), (← q r"quotient_ring b (Q:B->bool)"), (← q r"s:(B->bool)->(B->bool)")] RING_HOMOMORPHISM_POW) THEN MP_TAC (← ISPECL [(← q r"quotient_ring b (Q:B->bool)"), (← q r"quotient_ring b (Q:B->bool)"), (← q r"\X. if X IN ring_carrier(quotient_ring b Q)
                        then IMAGE (f:B->B) X else X")] RING_HOMOMORPHISM_POW) THEN ASM_REWRITE_TAC [] THEN REPEAT (DISCH_THEN (MP_TAC o (SPECL [(← q r"z:B->bool"), (← q r"n:num")]))) THEN ASM_SIMP_TAC [RING_POW])

  let CARD_DECOMPOSITION_GROUP ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!(h:A->B) k l b Q.
          finite_extension(k,l) h /\ galois_extension(k,l) h /\
          subring_generated l (ring_carrier b) = b /\
          (!f. f IN group_carrier(galois_group(k,l) h)
               ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
          maximal_ideal b Q /\ FINITE(ring_carrier(quotient_ring b Q))
          ==> CARD(group_carrier(decomposition_group(k,l) h Q)) =
              CARD(group_carrier(inertia_group(k,l) h b Q)) *
              extension_degree
               (subring_generated (quotient_ring b Q)
                 (IMAGE (ring_coset b Q o h)
                        {a | a IN ring_carrier k /\ h a IN ring_carrier b}),
                quotient_ring b Q) I"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!f. f IN group_carrier(decomposition_group(k,l) (h:A->B) Q)
          ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b") ASSUME_TAC THENL [REWRITE_TAC [DECOMPOSITION_GROUP, IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool")] DECOMPOSITION_GROUP_RESIDUE_EPIMORPHISM) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool")] DECOMPOSITION_GROUP_RESIDUE_HOMOMORPHISM) THEN ASM_SIMP_TAC [MAXIMAL_IMP_RING_IDEAL] THEN ABBREV_TAC (← q r"kP = subring_generated (quotient_ring b Q)
            (IMAGE (ring_coset b Q o (h:A->B))
                   {a | a IN ring_carrier k /\ h a IN ring_carrier b})") THEN ABBREV_TAC (← q r"rho = \f X. if X IN ring_carrier(quotient_ring b Q)
                  then IMAGE (f:B->B) X else X") THEN REWRITE_TAC [group_epimorphism] THEN STRIP_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"decomposition_group(k,l) (h:A->B) Q"), (← q r"galois_group(kP,quotient_ring b (Q:B->bool)) I"), (← q r"rho:(B->B)->(B->bool)->(B->bool)")] CARD_EQ_GROUP_IMAGE_KERNEL) THEN ASM_REWRITE_TAC [group_image] THEN SUBGOAL_THEN (← q r"FINITE(group_carrier(decomposition_group(k,l) (h:A->B) Q)) /\
      FINITE(group_carrier(inertia_group(k,l) h b Q)) /\
      FINITE(group_carrier(galois_group(kP,quotient_ring b (Q:B->bool)) I))") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r1 THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"group_carrier(galois_group(k,l) (h:A->B))") THEN ASM_SIMP_TAC [FINITE_GALOIS_GROUP] THEN REWRITE_TAC [DECOMPOSITION_GROUP] THEN SET_TAC [], DISCH_TAC THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"group_carrier(galois_group(k,l) (h:A->B))") THEN ASM_SIMP_TAC [FINITE_GALOIS_GROUP] THEN REWRITE_TAC [inertia_group, GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET], ASM_MESON_TAC [FINITE_IMAGE]]], ASM_SIMP_TAC [CARD_EQ_CARD, CARD_MUL_FINITE, CARD_MUL_C] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [MULT_SYM] THEN AP_TERM_TAC] THEN MP_TAC (← ISPECL [(← q r"I:(B->bool)->(B->bool)"), (← q r"kP:(B->bool)ring"), (← q r"quotient_ring b (Q:B->bool)")] GALOIS_GROUP_FINITE_FIELD) THEN ANTS_TAC THENL [ALL_TAC, SIMP_TAC []] THEN ASM_REWRITE_TAC [field_extension] THEN SUBGOAL_THEN (← q r"field(quotient_ring b (Q:B->bool))") ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_QUOTIENT_RING, MAXIMAL_IMP_RING_IDEAL], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "kP" THEN REWRITE_TAC [(← REWRITE_RULE [(← GSYM I_DEF)] RING_MONOMORPHISM_INCLUSION)] THEN MATCH_MP_TAC FINITE_INTEGRAL_DOMAIN_IMP_FIELD THEN ASM_SIMP_TAC [FINITE_SUBRING_GENERATED, INTEGRAL_DOMAIN_SUBRING_GENERATED, FIELD_IMP_INTEGRAL_DOMAIN])

  let EXTENSION_DEGREE_RESIDUE_CONJUGATE ← prove
    r"!(h:A->B) k l b f Q.
        finite_extension(k,l) h /\ galois_extension(k,l) h /\
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        maximal_ideal b Q /\ FINITE(ring_carrier(quotient_ring b Q)) /\
        f IN group_carrier(galois_group(k,l) h)
        ==> extension_degree
             (subring_generated (quotient_ring b (IMAGE f Q))
               (IMAGE (ring_coset b (IMAGE f Q) o h)
                      {a | a IN ring_carrier k /\ h a IN ring_carrier b}),
              quotient_ring b (IMAGE f Q)) I =
            extension_degree
             (subring_generated (quotient_ring b Q)
               (IMAGE (ring_coset b Q o h)
                      {a | a IN ring_carrier k /\ h a IN ring_carrier b}),
              quotient_ring b Q) I"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_RING_IDEAL)) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"f:B->B"), (← q r"Q:B->bool")] GALOIS_GROUP_PRIME_IDEAL_IMAGE) THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"f:B->B"), (← q r"Q:B->bool")] GALOIS_GROUP_QUOTIENT_RING_IMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool")] CARD_DECOMPOSITION_GROUP) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"IMAGE (f:B->B) Q")] CARD_DECOMPOSITION_GROUP) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"f:B->B"), (← q r"Q:B->bool")] CARD_DECOMPOSITION_GROUP_CONJUGATE) THEN ASM_SIMP_TAC [FINITE_IMAGE] THEN SUBGOAL_THEN (← q r"~(CARD(group_carrier(inertia_group(k,l) (h:A->B) b Q)) = 0)") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"FINITE(group_carrier(inertia_group(k,l) (h:A->B) b Q))") ASSUME_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"group_carrier(galois_group(k,l) (h:A->B))") THEN ASM_SIMP_TAC [FINITE_GALOIS_GROUP] THEN REWRITE_TAC [inertia_group, GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET], ASM_SIMP_TAC [CARD_EQ_0, (← GSYM MEMBER_NOT_EMPTY)] THEN EXISTS_TAC (← q r"group_id(inertia_group(k,l) (h:A->B) b Q)") THEN REWRITE_TAC [GROUP_ID]], ASM_REWRITE_TAC [EQ_MULT_LCANCEL]])

  let frobenius_element ← new_definition
    r"frobenius_element (k:A ring,l:B ring) (h:A->B) (b:B ring) (Q:B->bool) =
    @f. f IN group_carrier(galois_group(k,l) h) /\ IMAGE f Q = Q /\
        !x. x IN ring_carrier b
            ==> ring_sub l (f x)
                  (ring_pow l x
                     (CARD {ring_coset b Q (h a) | a |
                            a IN ring_carrier k /\ h a IN ring_carrier b}))
                IN Q"

  let DECOMPOSITION_GROUP_FROBENIUS_EXISTS ← prove
    r"!(h:A->B) k l b Q.
        finite_extension(k,l) h /\ galois_extension(k,l) h /\
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        maximal_ideal b Q /\ FINITE(ring_carrier(quotient_ring b Q))
        ==> ?f. f IN group_carrier(decomposition_group(k,l) h Q) /\
                !x. x IN ring_carrier b
                    ==> ring_sub l (f x)
                         (ring_pow l x
                           (CARD {ring_coset b Q (h a) | a |
                                  a IN ring_carrier k /\
                                  h a IN ring_carrier b}))
                        IN Q"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"ring_homomorphism(k,l) (h:A->B)") ASSUME_TAC THENL [ASM_MESON_TAC [finite_extension, field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool")] SUBRING_GENERATED_QUOTIENT_RING_IMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ABBREV_TAC (← q r"kP = subring_generated (quotient_ring b Q)
          (IMAGE (ring_coset b Q o (h:A->B))
                 {a | a IN ring_carrier k /\ h a IN ring_carrier b})") THEN SUBGOAL_THEN (← q r"field(quotient_ring b (Q:B->bool))") ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_QUOTIENT_RING], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"I:(B->bool)->(B->bool)"), (← q r"kP:(B->bool)ring"), (← q r"quotient_ring b (Q:B->bool)")] GALOIS_GROUP_FINITE_FIELD) THEN ANTS_TAC THENL [EXPAND_TAC "kP" THEN ASM_SIMP_TAC [FIELD_EXTENSION_SUBRING_GENERATED_FINITE], DISCH_THEN (ASSUME_TAC o CONJUNCT1)] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool")] DECOMPOSITION_GROUP_RESIDUE_EPIMORPHISM) THEN ASM_REWRITE_TAC [group_epimorphism] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"\X. if X IN ring_carrier(quotient_ring b Q)
        then ring_pow (quotient_ring b Q) X
               (CARD(ring_carrier(kP:(B->bool)ring)))
        else (X:B->bool)")) o ((GEN_REWRITE_RULE id [EXTENSION]) o CONJUNCT2))) THEN ASM_REWRITE_TAC [IN_IMAGE] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"f:B->B") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (← do let c := (← q r"ring_coset b Q (x:B)"); pure (fun th => AP_THM th c))) THEN REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ring_coset b Q (x:B) IN ring_carrier(quotient_ring b Q)") (fun th => REWRITE_TAC [th]) THENL [ASM_SIMP_TAC [QUOTIENT_RING_CARRIER] THEN ASM SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"f:B->B"), (← q r"x:B")] DECOMPOSITION_GROUP_IMAGE_RING_COSET) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"quotient_ring b (Q:B->bool)"), (← q r"ring_coset b (Q:B->bool)")] RING_HOMOMORPHISM_POW) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_COSET] THEN DISCH_THEN (MP_TAC o (SPECL [(← q r"x:B"), (← q r"CARD(ring_carrier(kP:(B->bool)ring))")])) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN SUBGOAL_THEN (← q r"(f:B->B) x IN ring_carrier b") ASSUME_TAC THENL [UNDISCH_TAC (← q r"f IN group_carrier(decomposition_group(k,l) (h:A->B) Q)") THEN REWRITE_TAC [DECOMPOSITION_GROUP, IN_ELIM_THM] THEN ASM SET_TAC [], ALL_TAC] THEN CONV_TAC (LAND_CONV SYM_CONV) THEN ASM_SIMP_TAC [RING_COSET_EQ, RING_POW] THEN UNDISCH_TAC (← q r"subring_generated l (ring_carrier b) = (b:B ring)") THEN DISCH_THEN (fun th => tactic_of do pure (ONCE_REWRITE_TAC [(← SYM th)])) THEN REWRITE_TAC [RING_SUB_SUBRING_GENERATED, RING_POW_SUBRING_GENERATED])

  let FROBENIUS_ELEMENT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_sub r (ring_sub r a c) (ring_sub r d c) = ring_sub r a (d:A)")
    let r2 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    let r9 ← RING_RULE (← q r"ring_add r (ring_sub r a c) c = (a:A)")
    prove
      r"!(h:A->B) k l b Q.
          finite_extension(k,l) h /\ galois_extension(k,l) h /\
          subring_generated l (ring_carrier b) = b /\
          (!f. f IN group_carrier(galois_group(k,l) h)
               ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
          maximal_ideal b Q /\ FINITE(ring_carrier(quotient_ring b Q)) /\
          group_carrier(inertia_group(k,l) h b Q) = {I}
          ==> frobenius_element (k,l) h b Q
              IN group_carrier(decomposition_group(k,l) h Q) /\
              !f. f IN group_carrier(galois_group(k,l) h) /\
                  (!x. x IN ring_carrier b
                       ==> ring_sub l (f x)
                            (ring_pow l x
                              (CARD {ring_coset b Q (h a) | a |
                                     a IN ring_carrier k /\
                                     h a IN ring_carrier b}))
                           IN Q)
                  <=> f = frobenius_element (k,l) h b Q"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_PRIME_IDEAL)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_RING_IDEAL)) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool")] DECOMPOSITION_GROUP_FROBENIUS_EXISTS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"f0:B->B") STRIP_ASSUME_TAC) THEN REWRITE_TAC [frobenius_element] THEN ABBREV_TAC (← q r"q = CARD {ring_coset b Q ((h:A->B) a) | a |
                a IN ring_carrier k /\ h a IN ring_carrier b}") THEN SUBGOAL_THEN (← q r"ring_carrier b SUBSET ring_carrier l /\
      ring_add b = ring_add l /\ ring_sub b = ring_sub (l:B ring)") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"subring_generated l (ring_carrier b) = (b:B ring)") THEN DISCH_THEN (fun th => tactic_of do pure (ONCE_REWRITE_TAC [(← SYM th)])) THEN REWRITE_TAC [RING_CARRIER_SUBRING_GENERATED_SUBSET, (← CONJUNCT2 SUBRING_GENERATED), RING_SUB_SUBRING_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(q = 0)") ASSUME_TAC THENL [EXPAND_TAC "q" THEN wPart rand (lhand o rand) CARD_EQ_0 THEN ANTS_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"ring_carrier(quotient_ring b (Q:B->bool))") THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER] THEN REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN REWRITE_TAC [IN_ELIM_THM] THEN MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY), IN_ELIM_THM] THEN EXISTS_TAC (← q r"ring_coset b Q ((h:A->B)(ring_0 k))") THEN EXISTS_TAC (← q r"ring_0(k:A ring)") THEN REWRITE_TAC [RING_0] THEN SUBGOAL_THEN (← q r"(h:A->B)(ring_0 k) = ring_0 l") SUBST1_TAC THENL [ASM_MESON_TAC [finite_extension, field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_HOMOMORPHISM_0], UNDISCH_TAC (← q r"subring_generated l (ring_carrier b) = (b:B ring)") THEN DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [(← SYM th)])) THEN MESON_TAC [RING_0, SUBRING_GENERATED]], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_pow b = ring_pow (l:B ring)") ASSUME_TAC THENL [UNDISCH_TAC (← q r"subring_generated l (ring_carrier b) = (b:B ring)") THEN DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [(← SYM th)])) THEN REWRITE_TAC [RING_POW_SUBRING_GENERATED], ALL_TAC] THEN FIRST_ASSUM (STRIP_ASSUME_TAC o ((REWRITE_RULE [DECOMPOSITION_GROUP, IN_ELIM_THM]) o (checkM (fun th => (do let z12 ← (q r"f0 IN group_carrier(decomposition_group(k,l) (h:A->B) Q)"); let z11 ← (do let z10 ← (pure th); pure (concl z10)); pure (z11 == z12)))))) THEN SUBGOAL_THEN (← q r"!f. f IN group_carrier(galois_group(k,l) (h:A->B)) /\
          (!x. x IN ring_carrier b ==> ring_sub l (f x) (ring_pow l x q) IN Q)
          ==> f = f0") ASSUME_TAC THENL [X_GEN_TAC (← q r"f:B->B") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"f:B->B"), (← q r"Q:B->bool")] GALOIS_GROUP_PRIME_IDEAL_IMAGE) THEN ASM_SIMP_TAC [PRIME_IDEAL_IMP_SUBSET] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"IMAGE (f:B->B) Q = Q") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"IMAGE (f:B->B) Q SUBSET Q") ASSUME_TAC THENL [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(y:B) IN ring_carrier b") ASSUME_TAC THENL [ASM_MESON_TAC [PRIME_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"(f:B->B) y = ring_add l (ring_sub l (f y) (ring_pow l y q))
                                    (ring_pow l y q)") SUBST1_TAC THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC r9 THEN SUBGOAL_THEN (← q r"(y:B) IN ring_carrier l") ASSUME_TAC THENL [UNDISCH_TAC (← q r"ring_carrier b SUBSET ring_carrier(l:B ring)") THEN REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ASM_SIMP_TAC [RING_POW]] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"f:B->B"), (← q r"k:A ring"), (← q r"l:B ring")] GALOIS_GROUP_PERMUTES) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => tactic_of do pure (ASM_REWRITE_TAC [(← MATCH_MP PERMUTES_IN_IMAGE th)])), ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_pow l y q IN (Q:B->bool)") ASSUME_TAC THENL [UNDISCH_TAC (← q r"ring_pow b = ring_pow (l:B ring)") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [RING_POW_IN_PRIME_IDEAL], ALL_TAC] THEN UNDISCH_TAC (← q r"ring_add b = ring_add (l:B ring)") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC IN_RING_IDEAL_ADD THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"maximal_ideal b (IMAGE (f:B->B) Q)") MP_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN REWRITE_TAC [maximal_ideal, NOT_EXISTS_THM] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"Q:B->bool")) o CONJUNCT2)) THEN ASM_SIMP_TAC [MAXIMAL_IMP_PROPER_IDEAL, PSUBSET] THEN ASM SET_TAC [], ALL_TAC] THEN FIRST_ASSUM (MP_TAC o ((MATCH_MP GALOIS_GROUP_PERMUTES) o (checkM (fun th => (do let z8 ← (q r"f0 IN group_carrier(galois_group(k,l) (h:A->B))"); let z7 ← (do let z6 ← (pure th); pure (concl z6)); pure (z7 == z8)))))) THEN DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP PERMUTES_INVERSES)) THEN SUBGOAL_THEN (← q r"inverse(f0:B->B) o (f:B->B) = I") MP_TAC THENL [FIRST_ASSUM (MP_TAC o (checkM (fun th => (do let z5 ← (q r"group_carrier (inertia_group (k,l) (h:A->B) b Q) = {I}"); let z4 ← (do let z3 ← (pure th); pure (concl z3)); pure (z4 == z5))))) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool")] (← CONJUNCT1 INERTIA_GROUP)) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [DECOMPOSITION_GROUP, IN_ELIM_THM] THEN ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"inverse(f0:B->B) o (f:B->B)")) o (GEN_REWRITE_RULE id [EXTENSION]))) THEN REWRITE_TAC [IN_ELIM_THM, IN_SING] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [GALOIS_GROUP_COMPOSE, GALOIS_GROUP_INVERSE, IMAGE_o] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"f0:B->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"Q:B->bool")] GALOIS_GROUP_IMAGE_INVERSE) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN REWRITE_TAC [o_THM] THEN SUBGOAL_THEN (← q r"(y:B) IN ring_carrier l /\ (f:B->B) y IN ring_carrier l /\
          (f0:B->B) y IN ring_carrier l /\ ring_pow l y q IN ring_carrier l") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r2 THEN CONJ_TAC THENL [UNDISCH_TAC (← q r"ring_carrier b SUBSET ring_carrier(l:B ring)") THEN REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [], DISCH_TAC THEN ASM_SIMP_TAC [RING_POW] THEN ASM_MESON_TAC [GALOIS_GROUP_PERMUTES, PERMUTES_IN_IMAGE]], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sub l ((f:B->B) y) (f0 y) IN Q") MP_TAC THENL [SUBGOAL_THEN (← q r"ring_sub l ((f:B->B) y) (f0 y) =
            ring_sub l (ring_sub l (f y) (ring_pow l y q))
                       (ring_sub l (f0 y) (ring_pow l y q))") SUBST1_TAC THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC [], MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"ring_sub l ((f:B->B) y) (ring_pow l y q)"), (← q r"ring_sub l ((f0:B->B) y) (ring_pow l y q)")] IN_RING_IDEAL_SUB) THEN ASM_SIMP_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_homomorphism(l,l) (inverse(f0:B->B))") ASSUME_TAC THENL [ASM_MESON_TAC [GALOIS_GROUP_RING_AUTOMORPHISM, GALOIS_GROUP_INVERSE, ring_automorphism, RING_ISOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN DISCH_THEN (MP_TAC o ((ISPEC (← q r"inverse(f0:B->B)")) o (MATCH_MP FUN_IN_IMAGE))) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"f0:B->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"Q:B->bool")] GALOIS_GROUP_IMAGE_INVERSE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"l:B ring"), (← q r"inverse(f0:B->B)")] RING_HOMOMORPHISM_SUB) THEN ASM_SIMP_TAC [], REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM] THEN DISCH_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN ASM_MESON_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"(@f. f IN group_carrier(galois_group(k,l) (h:A->B)) /\ IMAGE f Q = Q /\
           (!x. x IN ring_carrier b
                ==> ring_sub l (f x) (ring_pow l x q) IN Q)) = f0") SUBST1_TAC THENL [MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC (← q r"g:B->B") THEN REWRITE_TAC [] THEN EQ_TAC THENL [STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC []], ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"f:B->B") THEN EQ_TAC THENL [DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC []]])

  -- @@RETURN BEGIN
  return { DECOMPOSITION_GROUP_RESIDUE_EPIMORPHISM, CARD_DECOMPOSITION_GROUP,
           EXTENSION_DEGREE_RESIDUE_CONJUGATE, frobenius_element,
           DECOMPOSITION_GROUP_FROBENIUS_EXISTS, FROBENIUS_ELEMENT }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- decomposition.ml phrases from line 1935 to 2393                        -/
/- ---------------------------------------------------------------------- -/

structure Decomposition04 where
  -- @@FIELDS
  FROBENIUS_ELEMENT_CONJUGATE : thm
  DECOMPOSITION_GROUP_INTERMEDIATE : thm
  INERTIA_GROUP_INTERMEDIATE : thm
  INERTIA_GROUP_TOWER : thm
  DECOMPOSITION_GROUP_INTERMEDIATE_UNIQUE : thm
  DECOMPOSITION_FIELD_UNIQUE_PRIME : thm
  FINITE_DECOMPOSITION_INERTIA_GROUPS : thm
  FROBENIUS_ELEMENT_IN_DECOMPOSITION_GROUP : thm
  DECOMPOSITION_GROUP_POW_CONGRUENCE : thm
  DECOMPOSITION_GROUP_CONGRUENT_EQ : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDecomposition04 [HolBase] (D : DecompositionDeps) (BDecomposition01 : Decomposition01) (BDecomposition03 : Decomposition03) :
    ExceptT String IO Decomposition04 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, RING_RULE, SET_TAC, TAUT, .. } := D
  let { CARD_IMAGE_INJ, CARRIER_SUBFIELD_GENERATED_SUBFIELD, CONJ_ASSOC, EXP,
        EXTENSION, FINITE_EXTENSION_SUBFIELD_GENERATED, FINITE_GALOIS_GROUP,
        FINITE_IMAGE, FINITE_SUBSET, FORALL_IN_GSPEC, FORALL_IN_IMAGE, FUN_EQ_THM,
        FUN_IN_IMAGE, GALOIS_EXTENSION_SUBFIELD_GENERATED, GALOIS_GROUP,
        GALOIS_GROUP_ANTIMONO, GALOIS_GROUP_COMPOSE, GALOIS_GROUP_FIXED_FIELD,
        GALOIS_GROUP_FIXES, GALOIS_GROUP_I, GALOIS_GROUP_IMAGE_INVERSE,
        GALOIS_GROUP_INVERSE, GALOIS_GROUP_IN_CARRIER, GALOIS_GROUP_PERMUTES,
        GALOIS_GROUP_RING_AUTOMORPHISM, GALOIS_GROUP_RING_HOMOMORPHISM,
        GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET, GROUP_ID, GROUP_ORBIT, GROUP_POW,
        IMAGE_CLAUSES, IMAGE_I, IMAGE_ID, IMAGE_SUBSET, IMAGE_o, IN_ELIM_THM,
        IN_GALOIS_GROUP_INTERMEDIATE, IN_IMAGE, IN_INTER, IN_RING_IDEAL_0,
        IN_RING_IDEAL_ADD, IN_SING, I_THM, MAXIMAL_IMP_RING_IDEAL, MEMBER_NOT_EMPTY,
        MULT_SYM, PERMUTES_INVERSES, .. } := D.core1
  let { PERMUTES_IN_IMAGE, QUOTIENT_RING_CARRIER,
        RING_CARRIER_SUBRING_GENERATED_SUBSET, RING_COSET_EQ, RING_HOMOMORPHISM_POW,
        RING_HOMOMORPHISM_RING_COSET, RING_HOMOMORPHISM_SUB, RING_IDEAL_IMP_SUBSET,
        RING_ISOMORPHISM_IMP_HOMOMORPHISM, RING_POW, RING_POW_1, RING_POW_POW,
        RING_POW_SUBRING_GENERATED, RING_SUB_REFL, RING_SUB_SUBRING_GENERATED,
        SUBGROUP_SUBGROUP_GENERATED, SUBRING_GENERATED, SUBSET, SUBSET_REFL, group_pow,
        o_DEF, o_THM, ring_automorphism, ring_homomorphism, .. } := D.core2
  let { DECOMPOSITION_GROUP, GALOIS_GROUP_ACTION_SUBRING,
        GALOIS_GROUP_IMAGE_RING_COSET, GALOIS_GROUP_ORBIT_MAXIMAL_IDEAL,
        GALOIS_GROUP_PRIME_IDEAL_IMAGE, INERTIA_GROUP, INERTIA_GROUP_CONJUGATE,
        decomposition_group, inertia_group, .. } := BDecomposition01
  let { DECOMPOSITION_GROUP_FROBENIUS_EXISTS, FROBENIUS_ELEMENT, frobenius_element, .. } := BDecomposition03
  -- @@SCOPE END

  let FROBENIUS_ELEMENT_CONJUGATE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!(h:A->B) k l b Q f.
          finite_extension(k,l) h /\ galois_extension(k,l) h /\
          subring_generated l (ring_carrier b) = b /\
          (!f. f IN group_carrier(galois_group(k,l) h)
               ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
          maximal_ideal b Q /\ FINITE(ring_carrier(quotient_ring b Q)) /\
          group_carrier(inertia_group(k,l) h b Q) = {I} /\
          f IN group_carrier(galois_group(k,l) h)
          ==> frobenius_element (k,l) h b (IMAGE f Q) =
              f o frobenius_element (k,l) h b Q o inverse f"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_RING_IDEAL)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_IDEAL_IMP_SUBSET)) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"f:B->B"), (← q r"Q:B->bool")] GALOIS_GROUP_PRIME_IDEAL_IMAGE) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN FIRST_ASSUM (MP_TAC o ((MATCH_MP GALOIS_GROUP_PERMUTES) o (checkM (fun th => (do let z4 ← (q r"f IN group_carrier(galois_group(k,l) (h:A->B))"); let z3 ← (do let z2 ← (pure th); pure (concl z2)); pure (z3 == z4)))))) THEN DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP PERMUTES_INVERSES)) THEN SUBGOAL_THEN (← q r"ring_homomorphism(l,l) (f:B->B) /\
      ring_carrier b SUBSET ring_carrier l /\
      (!x. x IN ring_carrier b ==> f x IN ring_carrier b) /\
      (!x. x IN ring_carrier b ==> inverse f x IN ring_carrier b)") STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THENL [ASM_MESON_TAC [GALOIS_GROUP_RING_AUTOMORPHISM, ring_automorphism, RING_ISOMORPHISM_IMP_HOMOMORPHISM], MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"ring_carrier(b:B ring)")] RING_CARRIER_SUBRING_GENERATED_SUBSET) THEN ASM_REWRITE_TAC [], ASM SET_TAC [], ASM_MESON_TAC [GALOIS_GROUP_INVERSE, SUBSET, IN_IMAGE]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x. x IN ring_carrier b
          ==> IMAGE f (ring_coset b Q x) =
              ring_coset b (IMAGE (f:B->B) Q) (f x)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC GALOIS_GROUP_IMAGE_RING_COSET THEN MAP_EVERY EXISTS_TAC [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring")] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"FINITE(ring_carrier(quotient_ring b (IMAGE (f:B->B) Q)))") ASSUME_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"IMAGE (IMAGE (f:B->B)) (ring_carrier(quotient_ring b Q))") THEN ASM_SIMP_TAC [FINITE_IMAGE, QUOTIENT_RING_CARRIER] THEN REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN EXISTS_TAC (← q r"ring_coset b Q (inverse (f:B->B) y)") THEN ASM_SIMP_TAC [] THEN EXISTS_TAC (← q r"inverse (f:B->B) y") THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"group_carrier(inertia_group(k,l) (h:A->B) b (IMAGE (f:B->B) Q)) = {I}") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"f:B->B"), (← q r"Q:B->bool")] INERTIA_GROUP_CONJUGATE) THEN ASM_REWRITE_TAC [IMAGE_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM], ALL_TAC] THEN SUBGOAL_THEN (← q r"{ring_coset b (IMAGE (f:B->B) Q) ((h:A->B) a) | a |
       a IN ring_carrier k /\ h a IN ring_carrier b} =
      IMAGE (IMAGE (f:B->B)) {ring_coset b Q (h a) | a |
                              a IN ring_carrier k /\ h a IN ring_carrier b}") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"!a. a IN ring_carrier k /\ (h:A->B) a IN ring_carrier b
            ==> IMAGE (f:B->B) (ring_coset b Q (h a)) =
                ring_coset b (IMAGE f Q) (h a)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN ASM_SIMP_TAC [] THEN ASM_MESON_TAC [GALOIS_GROUP_FIXES], ALL_TAC] THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"CARD {ring_coset b (IMAGE (f:B->B) Q) ((h:A->B) a) | a |
            a IN ring_carrier k /\ h a IN ring_carrier b} =
      CARD {ring_coset b Q (h a) | a |
            a IN ring_carrier k /\ h a IN ring_carrier b}") ASSUME_TAC THENL [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL [MAP_EVERY X_GEN_TAC [(← q r"X:B->bool"), (← q r"Y:B->bool")] THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (AP_TERM (← q r"IMAGE (inverse(f:B->B))"))) THEN ASM_REWRITE_TAC [(← GSYM IMAGE_o), o_DEF, IMAGE_ID], MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"ring_carrier(quotient_ring b (Q:B->bool))") THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN MESON_TAC []], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"IMAGE (f:B->B) Q")] FROBENIUS_ELEMENT) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"(f:B->B) o frobenius_element (k,l) (h:A->B) b Q o inverse f")) o CONJUNCT2)) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool")] FROBENIUS_ELEMENT) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"frobenius_element (k,l) (h:A->B) b Q")) o CONJUNCT2)) THEN REWRITE_TAC [] THEN ABBREV_TAC (← q r"q = CARD {ring_coset b Q ((h:A->B) a) | a |
                a IN ring_carrier k /\ h a IN ring_carrier b}") THEN ABBREV_TAC (← q r"fr = frobenius_element (k,l) (h:A->B) b Q") THEN STRIP_TAC THEN CONV_TAC (RAND_CONV SYM_CONV) THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [GALOIS_GROUP_COMPOSE, GALOIS_GROUP_INVERSE] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN REWRITE_TAC [o_THM] THEN SUBGOAL_THEN (← q r"?y. y IN ring_carrier b /\ x = (f:B->B) y") (X_CHOOSE_THEN (← q r"y:B") (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THENL [EXISTS_TAC (← q r"inverse (f:B->B) x") THEN ASM_SIMP_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(y:B) IN ring_carrier l /\ (fr:B->B) y IN ring_carrier l") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r1 THEN CONJ_TAC THENL [UNDISCH_TAC (← q r"ring_carrier b SUBSET ring_carrier(l:B ring)") THEN REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ASM_MESON_TAC [GALOIS_GROUP_PERMUTES, PERMUTES_IN_IMAGE]], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sub l ((f:B->B) (fr y)) (ring_pow l (f y) q) =
      f (ring_sub l ((fr:B->B) y) (ring_pow l y q))") SUBST1_TAC THENL [MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"l:B ring"), (← q r"f:B->B")] RING_HOMOMORPHISM_POW) THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"l:B ring"), (← q r"f:B->B")] RING_HOMOMORPHISM_SUB) THEN ASM_SIMP_TAC [RING_POW], MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC []])

  let DECOMPOSITION_GROUP_INTERMEDIATE ← prove
    r"!(h:A->B) k l s Q.
        s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s
        ==> group_carrier(decomposition_group(subfield_generated l s,l) I Q) =
            group_carrier(decomposition_group(k,l) h Q) INTER
            group_carrier(galois_group(subfield_generated l s,l) I)"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [DECOMPOSITION_GROUP] THEN REWRITE_TAC [EXTENSION, IN_INTER, IN_ELIM_THM] THEN ASM_MESON_TAC [IN_GALOIS_GROUP_INTERMEDIATE])

  let INERTIA_GROUP_INTERMEDIATE ← prove
    r"!(h:A->B) k l b s Q.
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        ring_ideal b Q /\
        s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s
        ==> group_carrier(inertia_group(subfield_generated l s,l) I b Q) =
            group_carrier(inertia_group(k,l) h b Q) INTER
            group_carrier(galois_group(subfield_generated l s,l) I)"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"!f. f IN group_carrier(galois_group(subfield_generated l s,l) (I:B->B))
        ==> f IN group_carrier(galois_group(k,l) (h:A->B))") ASSUME_TAC THENL [ASM_MESON_TAC [IN_GALOIS_GROUP_INTERMEDIATE], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool")] (← CONJUNCT1 INERTIA_GROUP)) THEN MP_TAC (← ISPECL [(← q r"I:B->B"), (← q r"subfield_generated l (s:B->bool)"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool")] (← CONJUNCT1 INERTIA_GROUP)) THEN ANTS_TAC THENL [REWRITE_TAC [DECOMPOSITION_GROUP, IN_ELIM_THM] THEN ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN ANTS_TAC THENL [REWRITE_TAC [DECOMPOSITION_GROUP, IN_ELIM_THM] THEN ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [EXTENSION, IN_INTER, IN_ELIM_THM] THEN ASM_MESON_TAC [])

  let INERTIA_GROUP_TOWER ← prove
    r"!(h:A->B) (j:B->C) k l m b Q.
        ring_homomorphism(k,l) h /\
        subring_generated m (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,m) (j o h))
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        ring_ideal b Q
        ==> group_carrier(inertia_group(l,m) j b Q) =
            group_carrier(inertia_group(k,m) (j o h) b Q) INTER
            group_carrier(galois_group(l,m) j)"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"group_carrier(galois_group(l,m) (j:B->C)) SUBSET
    group_carrier(galois_group(k,m) (j o (h:A->B)))") ASSUME_TAC THENL [MATCH_MP_TAC GALOIS_GROUP_ANTIMONO THEN REWRITE_TAC [IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM (ACCEPT_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [ring_homomorphism]))), ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"(j:B->C) o (h:A->B)"), (← q r"k:A ring"), (← q r"m:C ring"), (← q r"b:C ring"), (← q r"Q:C->bool")] (← CONJUNCT1 INERTIA_GROUP)) THEN MP_TAC (← ISPECL [(← q r"j:B->C"), (← q r"l:B ring"), (← q r"m:C ring"), (← q r"b:C ring"), (← q r"Q:C->bool")] (← CONJUNCT1 INERTIA_GROUP)) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [DECOMPOSITION_GROUP, IN_ELIM_THM] THEN X_GEN_TAC (← q r"f:C->C") THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC [], DISCH_THEN SUBST1_TAC] THEN ANTS_TAC THENL [ASM_REWRITE_TAC [DECOMPOSITION_GROUP, IN_ELIM_THM] THEN ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [EXTENSION, IN_INTER, IN_ELIM_THM] THEN ASM SET_TAC [])

  let DECOMPOSITION_GROUP_INTERMEDIATE_UNIQUE ← prove
    r"!(h:A->B) k l b s Q.
        finite_extension(k,l) h /\ galois_extension(k,l) h /\
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        maximal_ideal b Q /\
        s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s
        ==> ({Q' | maximal_ideal b Q' /\ Q' INTER s = Q INTER s} = {Q} <=>
             group_carrier(galois_group(subfield_generated l s,l) I) SUBSET
             group_carrier(decomposition_group(k,l) h Q))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!f. f IN group_carrier(galois_group(subfield_generated l s,l) (I:B->B))
        ==> f IN group_carrier(galois_group(k,l) (h:A->B))") ASSUME_TAC THENL [ASM_MESON_TAC [IN_GALOIS_GROUP_INTERMEDIATE], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"I:B->B"), (← q r"subfield_generated l (s:B->bool)"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool")] GALOIS_GROUP_ORBIT_MAXIMAL_IDEAL) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"s:B->bool")] FINITE_EXTENSION_SUBFIELD_GENERATED) THEN ASM_SIMP_TAC [], MATCH_MP_TAC GALOIS_EXTENSION_SUBFIELD_GENERATED THEN MAP_EVERY EXISTS_TAC [(← q r"h:A->B"), (← q r"k:A ring")] THEN ASM_REWRITE_TAC [], ASM_MESON_TAC []], ALL_TAC] THEN ASM_SIMP_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD, I_THM] THEN SUBGOAL_THEN (← q r"!Q'. {a | a IN s /\ a IN Q'} = Q' INTER (s:B->bool)") (fun th => REWRITE_TAC [th]) THENL [SET_TAC [], ALL_TAC] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"I:B->B"), (← q r"subfield_generated l (s:B->bool)"), (← q r"l:B ring"), (← q r"b:B ring")] GALOIS_GROUP_ACTION_SUBRING) THEN ANTS_TAC THENL [ASM_MESON_TAC [], STRIP_TAC] THEN ASM_SIMP_TAC [GROUP_ORBIT, IN_ELIM_THM] THEN REWRITE_TAC [DECOMPOSITION_GROUP, SUBSET, IN_ELIM_THM] THEN EQ_TAC THENL [DISCH_TAC THEN X_GEN_TAC (← q r"f:B->B") THEN DISCH_TAC THEN ASM_SIMP_TAC [] THEN FIRST_X_ASSUM (MP_TAC o (AP_TERM (← q r"(IN) (IMAGE (f:B->B) Q)"))) THEN REWRITE_TAC [IN_ELIM_THM, IN_SING] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN EXISTS_TAC (← q r"f:B->B") THEN ASM_REWRITE_TAC [], DISCH_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"P:B->bool") THEN REWRITE_TAC [IN_ELIM_THM, IN_SING] THEN EQ_TAC THENL [DISCH_THEN (X_CHOOSE_THEN (← q r"f:B->B") STRIP_ASSUME_TAC) THEN ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC THEN EXISTS_TAC (← q r"I:B->B") THEN REWRITE_TAC [GALOIS_GROUP_I, IMAGE_I]]])

  let DECOMPOSITION_FIELD_UNIQUE_PRIME ← prove
    r"!(h:A->B) k l b Q.
        finite_extension(k,l) h /\ galois_extension(k,l) h /\
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        maximal_ideal b Q
        ==> {Q' | maximal_ideal b Q' /\
                  Q' INTER
                  fixed_field l (group_carrier(decomposition_group(k,l) h Q)) =
                  Q INTER
                  fixed_field l (group_carrier(decomposition_group(k,l) h Q))} =
            {Q}"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"group_carrier(decomposition_group(k,l) (h:A->B) Q)")] GALOIS_GROUP_FIXED_FIELD) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [decomposition_group, SUBGROUP_SUBGROUP_GENERATED], STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"fixed_field l (group_carrier(decomposition_group(k,l)
                                   (h:A->B) Q))"), (← q r"Q:B->bool")] DECOMPOSITION_GROUP_INTERMEDIATE_UNIQUE) THEN ASM_REWRITE_TAC [SUBSET_REFL])

  let FINITE_DECOMPOSITION_INERTIA_GROUPS ← prove
    r"!(h:A->B) k l b Q.
        finite_extension(k,l) h
        ==> FINITE(group_carrier(decomposition_group(k,l) h Q)) /\
            ~(group_carrier(decomposition_group(k,l) h Q) = {}) /\
            FINITE(group_carrier(inertia_group(k,l) h b Q)) /\
            ~(group_carrier(inertia_group(k,l) h b Q) = {})"
    (REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY)] THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"group_carrier(galois_group(k,l) (h:A->B))") THEN ASM_SIMP_TAC [FINITE_GALOIS_GROUP] THEN REWRITE_TAC [decomposition_group, GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET], MESON_TAC [GROUP_ID], MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"group_carrier(galois_group(k,l) (h:A->B))") THEN ASM_SIMP_TAC [FINITE_GALOIS_GROUP] THEN REWRITE_TAC [inertia_group, GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET], MESON_TAC [GROUP_ID]])

  let FROBENIUS_ELEMENT_IN_DECOMPOSITION_GROUP ← prove
    r"!(h:A->B) k l b Q.
        finite_extension(k,l) h /\ galois_extension(k,l) h /\
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        maximal_ideal b Q /\ FINITE(ring_carrier(quotient_ring b Q))
        ==> frobenius_element (k,l) h b Q
            IN group_carrier(decomposition_group(k,l) h Q) /\
            !x. x IN ring_carrier b
                ==> ring_sub l (frobenius_element (k,l) h b Q x)
                     (ring_pow l x
                       (CARD {ring_coset b Q (h a) | a |
                              a IN ring_carrier k /\ h a IN ring_carrier b}))
                    IN Q"
    (REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP DECOMPOSITION_GROUP_FROBENIUS_EXISTS)) THEN REWRITE_TAC [DECOMPOSITION_GROUP, IN_ELIM_THM, (← GSYM CONJ_ASSOC)] THEN DISCH_THEN (MP_TAC o SELECT_RULE) THEN REWRITE_TAC [(← GSYM frobenius_element)] THEN SIMP_TAC [])

  let DECOMPOSITION_GROUP_POW_CONGRUENCE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_add r (ring_sub r a c) (ring_sub r c d) = ring_sub r a (d:B)")
    prove
      r"!(h:A->B) k l b Q f q.
          subring_generated l (ring_carrier b) = b /\
          (!f. f IN group_carrier(galois_group(k,l) h)
               ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
          ring_ideal b Q /\
          f IN group_carrier(decomposition_group(k,l) h Q) /\
          (!x. x IN ring_carrier b ==> ring_sub l (f x) (ring_pow l x q) IN Q)
          ==> !n x. x IN ring_carrier b
                    ==> ring_sub l (group_pow (galois_group(k,l) h) f n x)
                                   (ring_pow l x (q EXP n)) IN Q"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o ((REWRITE_RULE [DECOMPOSITION_GROUP, IN_ELIM_THM]) o (checkM (fun th => (do let z14 ← (q r"f IN group_carrier(decomposition_group(k,l) (h:A->B) Q)"); let z13 ← (do let z12 ← (pure th); pure (concl z12)); pure (z13 == z14)))))) THEN SUBGOAL_THEN (← q r"ring_carrier b SUBSET ring_carrier l /\ ring_0 b = ring_0 l /\
      ring_add b = ring_add l /\
      ring_sub b = ring_sub l /\ ring_pow b = ring_pow (l:B ring)") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"subring_generated l (ring_carrier b) = (b:B ring)") THEN DISCH_THEN (fun th => tactic_of do pure (ONCE_REWRITE_TAC [(← SYM th)])) THEN REWRITE_TAC [RING_CARRIER_SUBRING_GENERATED_SUBSET, SUBRING_GENERATED, RING_SUB_SUBRING_GENERATED, RING_POW_SUBRING_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x y m. x IN ring_carrier b /\ y IN ring_carrier b /\
              ring_sub l x y IN Q
              ==> ring_sub l (ring_pow l x m) (ring_pow l y m) IN (Q:B->bool)") (LABEL_TAC "pow") THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"ring_pow b x m:B"), (← q r"ring_pow b y m:B")] RING_COSET_EQ) THEN MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"x:B"), (← q r"y:B")] RING_COSET_EQ) THEN ASM_SIMP_TAC [RING_POW] THEN MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"quotient_ring b (Q:B->bool)"), (← q r"ring_coset b (Q:B->bool)")] RING_HOMOMORPHISM_POW) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_COSET] THEN REPEAT DISCH_TAC THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!g x. g IN group_carrier(galois_group(k,l) (h:A->B)) /\
            x IN ring_carrier b ==> g x IN ring_carrier b") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"g:B->B")) o (checkM (fun th => (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); pure (is_forall z2)) then (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); canM (fun z6 => (do let z7 ← (pure z6); find_termM (fun t => (do if ← (do let z8 ← (pure t); pure (is_const z8)) then (do let z11 ← (pure "IMAGE"); let z10 ← (do pure (Prod.fst (← (do let z9 ← (pure t); liftExcept (dest_const z9))))); pure (z10 == z11)) else pure false)) z7)) z4) else pure false))))) THEN ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x:B. x IN ring_carrier b ==> x IN ring_carrier l") ASSUME_TAC THENL [MP_TAC (← ASSUME (← q r"ring_carrier b SUBSET ring_carrier(l:B ring)")) THEN REWRITE_TAC [SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x. x IN ring_carrier b
          ==> ring_sub l ((f:B->B) x) (ring_pow l x q) IN (Q:B->bool)") (LABEL_TAC "frob") THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN INDUCT_TAC THENL [REWRITE_TAC [group_pow, GALOIS_GROUP, I_THM, EXP] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [RING_POW_1, RING_SUB_REFL] THEN UNDISCH_TAC (← q r"ring_0 b = ring_0(l:B ring)") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC IN_RING_IDEAL_0 THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN REWRITE_TAC [group_pow, GALOIS_GROUP, o_THM] THEN ABBREV_TAC (← q r"g = group_pow (galois_group(k,l) (h:A->B)) f n") THEN SUBGOAL_THEN (← q r"g IN group_carrier(galois_group(k,l) (h:A->B))") ASSUME_TAC THENL [EXPAND_TAC "g" THEN ASM_SIMP_TAC [GROUP_POW], ALL_TAC] THEN SUBGOAL_THEN (← q r"(g:B->B) x IN ring_carrier b") ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_pow l (ring_pow l x (q EXP n)) q = ring_pow l (x:B) (q EXP SUC n)") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_POW_POW, EXP] THEN REWRITE_TAC [MULT_SYM], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sub l ((f:B->B) (g x)) (ring_pow l x (q EXP SUC n)) =
      ring_add l (ring_sub l (f (g x)) (ring_pow l (g x) q))
                 (ring_sub l (ring_pow l (g x) q)
                             (ring_pow l (ring_pow l x (q EXP n)) q))") SUBST1_TAC THENL [FIRST_ASSUM (fun th => REWRITE_TAC [th]) THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [RING_POW] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"f:B->B"), (← q r"k:A ring"), (← q r"l:B ring")] GALOIS_GROUP_IN_CARRIER) THEN ASM_SIMP_TAC [], ALL_TAC] THEN UNDISCH_TAC (← q r"ring_add b = ring_add (l:B ring)") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC IN_RING_IDEAL_ADD THEN REPEAT CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC, USE_THEN "frob" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC, USE_THEN "pow" MATCH_MP_TAC THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN CONJ_TAC THENL [UNDISCH_TAC (← q r"ring_pow b = ring_pow (l:B ring)") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [RING_POW], FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]])

  let DECOMPOSITION_GROUP_CONGRUENT_EQ ← prove
    r"!(h:A->B) k l b Q f g.
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        ring_ideal b Q /\
        group_carrier(inertia_group(k,l) h b Q) = {I} /\
        f IN group_carrier(decomposition_group(k,l) h Q) /\
        g IN group_carrier(decomposition_group(k,l) h Q) /\
        (!x. x IN ring_carrier b ==> ring_sub l (f x) (g x) IN Q)
        ==> f = g"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE [DECOMPOSITION_GROUP, IN_ELIM_THM]) THEN FIRST_ASSUM (MP_TAC o ((MATCH_MP GALOIS_GROUP_PERMUTES) o (CONJUNCT1 o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_conj z1)) then (do let z6 ← (q r"g IN group_carrier(galois_group(k,l) (h:A->B))"); let z5 ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); liftExcept (lhand z3)); pure (z5 == z6)) else pure false)))))) THEN DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP PERMUTES_INVERSES)) THEN SUBGOAL_THEN (← q r"inverse(g:B->B) o f = I") MP_TAC THENL [SUBGOAL_THEN (← q r"inverse(g:B->B) o f IN group_carrier(inertia_group(k,l) (h:A->B) b Q)") MP_TAC THENL [ALL_TAC, ASM_REWRITE_TAC [IN_SING]] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool")] (← CONJUNCT1 INERTIA_GROUP)) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [DECOMPOSITION_GROUP, IN_ELIM_THM] THEN ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [IN_ELIM_THM] THEN SUBGOAL_THEN (← q r"inverse(g:B->B) IN group_carrier(galois_group(k,l) (h:A->B)) /\
      IMAGE (inverse g) Q = Q") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [GALOIS_GROUP_INVERSE] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"g:B->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"Q:B->bool")] GALOIS_GROUP_IMAGE_INVERSE) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [GALOIS_GROUP_COMPOSE, IMAGE_o] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN REWRITE_TAC [o_THM] THEN SUBGOAL_THEN (← q r"ring_carrier b SUBSET ring_carrier(l:B ring)") ASSUME_TAC THENL [UNDISCH_TAC (← q r"subring_generated l (ring_carrier b) = (b:B ring)") THEN DISCH_THEN (fun th => tactic_of do pure (ONCE_REWRITE_TAC [(← SYM th)])) THEN REWRITE_TAC [RING_CARRIER_SUBRING_GENERATED_SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sub l (inverse g ((f:B->B) x)) x =
      inverse g (ring_sub l (f x) ((g:B->B) x))") SUBST1_TAC THENL [MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"l:B ring"), (← q r"inverse(g:B->B)")] RING_HOMOMORPHISM_SUB) THEN ANTS_TAC THENL [ASM_MESON_TAC [GALOIS_GROUP_RING_HOMOMORPHISM], ALL_TAC] THEN DISCH_THEN (MP_TAC o (SPECL [(← q r"(f:B->B) x"), (← q r"(g:B->B) x")])) THEN ANTS_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC GALOIS_GROUP_IN_CARRIER THEN MAP_EVERY EXISTS_TAC [(← q r"h:A->B"), (← q r"k:A ring")] THEN ASM SET_TAC [], DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC []], ALL_TAC] THEN UNDISCH_TAC (← q r"IMAGE (inverse g) Q = (Q:B->bool)") THEN DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [(← SYM th)])) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC [], REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM] THEN DISCH_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN ASM_MESON_TAC []])

  -- @@RETURN BEGIN
  return { FROBENIUS_ELEMENT_CONJUGATE, DECOMPOSITION_GROUP_INTERMEDIATE,
           INERTIA_GROUP_INTERMEDIATE, INERTIA_GROUP_TOWER,
           DECOMPOSITION_GROUP_INTERMEDIATE_UNIQUE, DECOMPOSITION_FIELD_UNIQUE_PRIME,
           FINITE_DECOMPOSITION_INERTIA_GROUPS, FROBENIUS_ELEMENT_IN_DECOMPOSITION_GROUP,
           DECOMPOSITION_GROUP_POW_CONGRUENCE, DECOMPOSITION_GROUP_CONGRUENT_EQ }
  -- @@RETURN END

end HolANT.Decomposition
