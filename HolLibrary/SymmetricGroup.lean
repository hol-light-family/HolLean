/- ========================================================================= -/
/- The symmetric group, of permutations on a set under composition.          -/
/-                                                                           -/
/- Definition and basic properties, plus the key theorem that S_n is not     -/
/- solvable for n >= 5, following Stillwell's "Galois Theory for Beginners". -/
/- ========================================================================= -/
/- File: HolLibrary/SymmetricGroup.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/symmetric_group.ml`, by hand, in file
  order, in the style of HolLibrary/GroupTheory.lean (see there and
  HolMath/Base.lean for the conventions).  symmetric_group.ml begins with
  `needs "Library/permutations.ml"` and `needs "Library/grouptheory.ml"`;
  the theorems it uses from them (and from the files they need) and from the
  core library are supplied via the CoreThms structures
  (SessionLibrary.SymmetricGroup fills them), and grouptheory.ml's GROUP_RULE
  via SymmetricGroupDeps.  Each section is a bundle (a `structure`) built by
  a `setup` function; SessionLibrary/SymmetricGroup.lean builds the bundles
  in order and exports every name under its HOL Light name.

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, SET_RULE) they are bound first, in OCaml's
  order.
-/

import HolLibrary.Permutations
import HolLibrary.GroupTheory

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

set_option maxRecDepth 8000

namespace HolLibrary.SymmetricGroup

-- @@COREFILL BEGIN
/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ABELIAN_QUOTIENT_COMMUTATOR ADD1 AND_FORALL_THM CARD_CLAUSES CARD_DELETE
   CARD_IMAGE_INJ CARD_LE_2 CARD_LE_3 CARD_LE_4 CARD_NUMSEG_LT
   CARD_PERMUTATIONS CARD_SING CARD_SUBSET CARD_SUBSET_EQ
   CARRIER_SUBGROUP_GENERATED_SUBGROUP CARRIER_SUBGROUP_OF
   CAUCHY_GROUP_THEOREM CONJ_ASSOC COPRIME_GCD DIVIDES_FACT_PRIME DIVIDES_LE
   DIVIDES_REFL DIV_1 EQ_TRANS EXTENSION FINITE_DELETE FINITE_EMPTY
   FINITE_INSERT FINITE_NUMSEG_LT FINITE_PERMUTATIONS FINITE_SUBSET
   FORALL_IN_IMAGE FUN_EQ_THM GROUP_ACTION_FROM_SUBGROUP
   GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER GROUP_ELEMENT_ORDER_EQ_1
   GROUP_ELEMENT_ORDER_ID GROUP_ELEMENT_ORDER_POW_GEN
   GROUP_ELEMENT_ORDER_SUBGROUP_GENERATED GROUP_HOMOMORPHISM GROUP_ID
   GROUP_INV GROUP_ISOMORPHISM_ONTO_IMAGE GROUP_MONOMORPHISM_ALT
   GROUP_MONOMORPHISM_IMP_HOMOMORPHISM GROUP_MUL GROUP_MUL_ASSOC
   GROUP_MUL_RID GROUP_ORBIT_SUBSET GROUP_POW GROUP_POW_1 GROUP_POW_ADD
   GROUP_POW_EQ_ID IMP_CONJ INTER_SUBSET IN_DELETE IN_DIFF IN_ELIM_THM
   IN_GROUP_ORBIT IN_IMAGE IN_INTER IN_SING IN_SUBGROUP_CONJUGATION
   IN_SUBGROUP_INV IN_SUBGROUP_MUL IN_SUBGROUP_POW ISOMORPHIC_GROUP_SYM
   I_O_ID I_THM LE_REFL : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (LT_NZ MEMBER_NOT_EMPTY MULT_SYM NORMAL_SUBGROUP_IMP_SUBGROUP ONE
   ORBIT_STABILIZER_MUL PAIR_EQ PERMUTES_COMPOSE PERMUTES_I
   PERMUTES_INDUCT_STRONG PERMUTES_INJECTIVE PERMUTES_INVERSE
   PERMUTES_INVERSES_o PERMUTES_INVERSE_FUNCTION PERMUTES_IN_IMAGE
   PERMUTES_SUBSET PERMUTES_SUPERSET PERMUTES_SWAP PERMUTES_THREE_CYCLE
   PRIME_0 PRIME_1 PRIME_COPRIME_EQ RESTRICT_COMPOSE RESTRICT_I
   RESTRICT_INVERSE RESTRICT_PERMUTES_SUBSET SUBGROUP_GENERATED
   SUBGROUP_GROUP_IMAGE SUBGROUP_OF_IMP_SUBSET
   SUBGROUP_OF_SUBGROUP_GENERATED_SUBGROUP_EQ SUBSET SUBSET_ANTISYM_EQ
   SWAP_CONJUGATE SWAP_REFL SWAP_SYM SWAP_TRIPLE SWAP_TRIPLE_ALT
   THREE_CYCLE_COMMUTATOR THREE_CYCLE_NOT_I divides group_action
   group_carrier group_conjugation group_homomorphism group_id group_inv
   group_mul group_pow group_tybij isomorphic_group o_ASSOC o_THM prime
   solvable_group subgroup_of : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms3 where
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms4 where
  deriving Inhabited

-- @@COREFILL END

/-- What symmetricgroup.ml uses from Session besides theorems. -/
structure SymmetricGroupDeps where
  -- definitions and parser state
  new_definition : String → ExceptT String IO thm
  -- decision procedures and tactics
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_ARITH_TAC : tactic
  MESON_TAC : List thm → tactic
  ASM_MESON_TAC : List thm → tactic
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  INDUCT_TAC : tactic
  -- grouptheory.ml's GROUP_RULE (SessionLibrary.GroupTheory exports it)
  GROUP_RULE : term → ExceptT String IO thm
  core1 : CoreThms1
  core2 : CoreThms2
  core3 : CoreThms3
  core4 : CoreThms4

/- ------------------------------------------------------------------------- -/
/- Basic definition and properties                                           -/
/- ------------------------------------------------------------------------- -/

structure Basics where
  -- @@FIELDS
  symmetric_group : thm
  SYMMETRIC_GROUP : thm
  FINITE_SYMMETRIC_GROUP : thm
  CARD_SYMMETRIC_GROUP : thm
  SYMMETRIC_GROUP_MUL : thm
  SYMMETRIC_GROUP_INV : thm
  SYMMETRIC_GROUP_ID : thm
  SWAP_IN_SYMMETRIC_GROUP : thm
  THREE_CYCLE_IN_SYMMETRIC : thm
  deriving Inhabited

@[nospecialize]
def setupBasics [HolBase] (D : SymmetricGroupDeps) :
    ExceptT String IO Basics := do
  -- @@SCOPE BEGIN
  let { MESON_TAC, new_definition, .. } := D
  let { AND_FORALL_THM, CARD_PERMUTATIONS, FINITE_PERMUTATIONS, IN_ELIM_THM, I_O_ID, .. } := D.core1
  let { PAIR_EQ, PERMUTES_COMPOSE, PERMUTES_I, PERMUTES_INVERSE, PERMUTES_INVERSES_o,
        PERMUTES_SWAP, PERMUTES_THREE_CYCLE, group_carrier, group_id, group_inv,
        group_mul, group_tybij, o_ASSOC, .. } := D.core2
  -- @@SCOPE END

  let symmetric_group ← new_definition
   r"symmetric_group (s:A->bool) =
    group({p:A->A | p permutes s}, I:(A->A), (inverse:(A->A)->A->A), (o))"

  let SYMMETRIC_GROUP ← prove
   r"(!s:A->bool.
     group_carrier(symmetric_group s) = {p | p permutes s}) /\
   (!s:A->bool. group_id(symmetric_group s) = I) /\
   (!s:A->bool. group_inv(symmetric_group s) = (inverse:(A->A)->A->A)) /\
   (!s:A->bool. group_mul(symmetric_group s) = (o))"
   (REWRITE_TAC [AND_FORALL_THM, ← GSYM PAIR_EQ] THEN
    REWRITE_TAC [group_carrier, group_id, group_inv, group_mul] THEN
    REWRITE_TAC [symmetric_group, ← GSYM (← CONJUNCT2 group_tybij)] THEN
    SIMP_TAC [o_ASSOC, I_O_ID, IN_ELIM_THM, PERMUTES_COMPOSE,
             PERMUTES_I, PERMUTES_INVERSE] THEN
    MESON_TAC [PERMUTES_INVERSES_o])

  let FINITE_SYMMETRIC_GROUP ← prove
   r"!s:A->bool. FINITE s ==> FINITE(group_carrier(symmetric_group s))"
   (SIMP_TAC [SYMMETRIC_GROUP, FINITE_PERMUTATIONS])

  let CARD_SYMMETRIC_GROUP ← prove
   r"!s:A->bool. FINITE s
    ==> CARD(group_carrier(symmetric_group s)) = FACT(CARD s)"
   (SIMP_TAC [SYMMETRIC_GROUP, CARD_PERMUTATIONS])

  let SYMMETRIC_GROUP_MUL ← prove
   r"!s (p:A->A) q. group_mul (symmetric_group s) p q = p o q"
   (REWRITE_TAC [SYMMETRIC_GROUP])

  let SYMMETRIC_GROUP_INV ← prove
   r"!s (p:A->A). group_inv (symmetric_group s) p = inverse p"
   (REWRITE_TAC [SYMMETRIC_GROUP])

  let SYMMETRIC_GROUP_ID ← prove
   r"!s:A->bool. group_id (symmetric_group s) = I"
   (REWRITE_TAC [SYMMETRIC_GROUP])

  let SWAP_IN_SYMMETRIC_GROUP ← prove
   r"!s a b:A. a IN s /\ b IN s
             ==> swap(a,b) IN group_carrier(symmetric_group s)"
   (SIMP_TAC [SYMMETRIC_GROUP, IN_ELIM_THM, PERMUTES_SWAP])

  let THREE_CYCLE_IN_SYMMETRIC ← prove
   r"!s a b c:A. a IN s /\ b IN s /\ c IN s /\
               ~(a = b) /\ ~(b = c) /\ ~(a = c)
               ==> three_cycle a b c IN
                   group_carrier(symmetric_group s)"
   (SIMP_TAC [SYMMETRIC_GROUP, IN_ELIM_THM, PERMUTES_THREE_CYCLE])

  -- @@RETURN BEGIN
  return { symmetric_group, SYMMETRIC_GROUP, FINITE_SYMMETRIC_GROUP,
           CARD_SYMMETRIC_GROUP, SYMMETRIC_GROUP_MUL, SYMMETRIC_GROUP_INV,
           SYMMETRIC_GROUP_ID, SWAP_IN_SYMMETRIC_GROUP, THREE_CYCLE_IN_SYMMETRIC }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Cayley's theorem: every group embeds into the symmetric group on          -/
/- its carrier via left multiplication                                       -/
/- ------------------------------------------------------------------------- -/

structure Cayley where
  -- @@FIELDS
  CAYLEY_THEOREM_EXPLICIT : thm
  CAYLEY_THEOREM : thm
  SYMMETRIC_GROUP_ACTION : thm
  deriving Inhabited

@[nospecialize]
def setupCayley [HolBase] (D : SymmetricGroupDeps) (BBasics : Basics) :
    ExceptT String IO Cayley := do
  -- @@SCOPE BEGIN
  let { MESON_TAC, .. } := D
  let { CONJ_ASSOC, FORALL_IN_IMAGE, FUN_EQ_THM, GROUP_HOMOMORPHISM, GROUP_ID,
        GROUP_INV, GROUP_ISOMORPHISM_ONTO_IMAGE, GROUP_MONOMORPHISM_ALT,
        GROUP_MONOMORPHISM_IMP_HOMOMORPHISM, GROUP_MUL, GROUP_MUL_ASSOC, GROUP_MUL_RID,
        IN_ELIM_THM, ISOMORPHIC_GROUP_SYM, I_THM, .. } := D.core1
  let { PERMUTES_INVERSE_FUNCTION, PERMUTES_IN_IMAGE, SUBGROUP_GROUP_IMAGE, SUBSET,
        group_action, isomorphic_group, o_THM, .. } := D.core2
  let { SYMMETRIC_GROUP, .. } := BBasics
  -- @@SCOPE END

  let CAYLEY_THEOREM_EXPLICIT ← prove
   r"!G:A group.
        group_monomorphism (G,symmetric_group(group_carrier G))
                           (\a x. if x IN group_carrier G
                                  then group_mul G a x else x)"
   (GEN_TAC THEN REWRITE_TAC [GROUP_MONOMORPHISM_ALT, GROUP_HOMOMORPHISM] THEN
    REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, SYMMETRIC_GROUP] THEN
    REWRITE_TAC [FUN_EQ_THM, o_THM, IN_ELIM_THM, I_THM] THEN
    SIMP_TAC [PERMUTES_INVERSE_FUNCTION, ← GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
     [ALL_TAC,
      MESON_TAC [GROUP_MUL_ASSOC, GROUP_MUL_RID, GROUP_MUL, GROUP_ID]] THEN
    X_GEN_TAC (← q "a:A") THEN DISCH_TAC THEN
    EXISTS_TAC (← q r"group_mul G (group_inv G a:A)") THEN
    ASM_SIMP_TAC [GROUP_MUL, GROUP_INV] THEN
    REPEAT STRIP_TAC THEN
    W (fun (_asl, w) => tactic_of do
          let th ← D.GROUP_RULE w
          pure (MATCH_MP_TAC th)) THEN ASM_REWRITE_TAC [])

  let CAYLEY_THEOREM ← prove
   r"!G:A group.
        ?h. h subgroup_of symmetric_group(group_carrier G) /\
            subgroup_generated (symmetric_group(group_carrier G)) h
            isomorphic_group G"
   (GEN_TAC THEN ONCE_REWRITE_TAC [ISOMORPHIC_GROUP_SYM] THEN
    EXISTS_TAC
     (← q r"group_image ((G:A group),
                 symmetric_group(group_carrier (G:A group)))
                (\(a:A) (x:A). if x IN group_carrier G
                                then group_mul G a x else x)") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBGROUP_GROUP_IMAGE THEN
      MATCH_MP_TAC GROUP_MONOMORPHISM_IMP_HOMOMORPHISM THEN
      REWRITE_TAC [CAYLEY_THEOREM_EXPLICIT],
      REWRITE_TAC [isomorphic_group] THEN
      EXISTS_TAC
        (← q r"\(a:A) (x:A). if x IN group_carrier (G:A group)
                      then group_mul G a x else x") THEN
      REWRITE_TAC [GROUP_ISOMORPHISM_ONTO_IMAGE, CAYLEY_THEOREM_EXPLICIT]])

  let SYMMETRIC_GROUP_ACTION ← prove
   r"!s:A->bool. group_action (symmetric_group s) s (\f x. (f:A->A) x)"
   (GEN_TAC THEN REWRITE_TAC [group_action, SYMMETRIC_GROUP, IN_ELIM_THM] THEN
    SIMP_TAC [] THEN REPEAT CONJ_TAC THENL
     [MESON_TAC [PERMUTES_IN_IMAGE],
      GEN_TAC THEN REWRITE_TAC [I_THM],
      REPEAT STRIP_TAC THEN REWRITE_TAC [o_THM]])

  -- @@RETURN BEGIN
  return { CAYLEY_THEOREM_EXPLICIT, CAYLEY_THEOREM, SYMMETRIC_GROUP_ACTION }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- S_n is not solvable for n >= 5                                            -/
/- ------------------------------------------------------------------------- -/

/- Stillwell p.26-27 (within proof of Theorem 3): "We use [the commutator
   fact] to prove by induction on i that, if n >= 5, each G_i contains all
   3-cycles. [...] But G_k = {1} contains no 3-cycles, contradiction."
   Stillwell credits this argument to Milgram's appendix to Artin [1]. -/

structure NotSolvable where
  -- @@FIELDS
  CHAIN_STEP_THREE_CYCLES_GEN : thm
  NOT_SOLVABLE_SYMMETRIC_GROUP : thm
  deriving Inhabited

@[nospecialize]
def setupNotSolvable [HolBase] (D : SymmetricGroupDeps) (BBasics : Basics) :
    ExceptT String IO NotSolvable := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, SET_RULE, .. } := D
  let { ABELIAN_QUOTIENT_COMMUTATOR, CARD_CLAUSES, CARD_LE_2, CARD_LE_3, CARD_LE_4,
        CARD_SING, CARD_SUBSET, CARRIER_SUBGROUP_GENERATED_SUBGROUP,
        CARRIER_SUBGROUP_OF, FINITE_EMPTY, FINITE_INSERT, IMP_CONJ, IN_SING, LE_REFL, .. } := D.core1
  let { MEMBER_NOT_EMPTY, NORMAL_SUBGROUP_IMP_SUBGROUP, SUBGROUP_GENERATED,
        SUBGROUP_OF_SUBGROUP_GENERATED_SUBGROUP_EQ, THREE_CYCLE_COMMUTATOR,
        THREE_CYCLE_NOT_I, solvable_group, .. } := D.core2
  let { SYMMETRIC_GROUP, SYMMETRIC_GROUP_ID, THREE_CYCLE_IN_SYMMETRIC, .. } := BBasics
  -- @@SCOPE END

  -- Generalized chain step: works for any group with composition/inverse
  let CHAIN_STEP_THREE_CYCLES_GEN ← prove
   r"!s:A->bool (H:(A->A) group) (n:(A->A)->bool).
     5 <= CARD s /\ FINITE s /\
     n normal_subgroup_of H /\
     abelian_group(quotient_group H n) /\
     group_mul H = (o) /\ group_inv H = (inverse:(A->A)->A->A) /\
     (!a b c. a IN s /\ b IN s /\ c IN s /\
              ~(a = b) /\ ~(b = c) /\ ~(a = c)
              ==> three_cycle a b c IN group_carrier H)
     ==> (!a b c. a IN s /\ b IN s /\ c IN s /\
                   ~(a = b) /\ ~(b = c) /\ ~(a = c)
                   ==> three_cycle a b c IN n)"
   (← do
    let s2 ← SET_RULE (← q r"~(s SUBSET {a,b,c,d:A})
       ==> ?e. e IN s /\ ~(e = a) /\ ~(e = b) /\ ~(e = c) /\ ~(e = d)")
    let s1 ← SET_RULE (← q r"~(s SUBSET {a,b,c:A})
       ==> ?d. d IN s /\ ~(d = a) /\ ~(d = b) /\ ~(d = c)")
    pure (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"?d:A. d IN s /\ ~(d = a) /\ ~(d = b) /\ ~(d = c)")
      STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC s1 THEN
      DISCH_THEN (MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ] CARD_SUBSET)) THEN
      REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY] THEN
      MP_TAC (← ISPECL [← q "a:A", ← q "b:A", ← q "c:A"] CARD_LE_3) THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"?e:A. e IN s /\ ~(e = a) /\ ~(e = b) /\ ~(e = c) /\ ~(e = d)")
      STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC s2 THEN
      DISCH_THEN (MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ] CARD_SUBSET)) THEN
      REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY] THEN
      MP_TAC (← ISPECL [← q "a:A", ← q "b:A", ← q "c:A", ← q "d:A"] CARD_LE_4) THEN
      ASM_ARITH_TAC,
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q "H:(A->A) group", ← q r"n:(A->A)->bool",
                  ← q r"three_cycle d a (c:A)", ← q r"three_cycle c e (b:A)"]
      ABELIAN_QUOTIENT_COMMUTATOR) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"three_cycle a b (c:A) =
    inverse(three_cycle d a c) o
    (inverse(three_cycle c e b) o
    (three_cycle d a c o three_cycle c e b))") SUBST1_TAC THENL
     [MATCH_MP_TAC THREE_CYCLE_COMMUTATOR THEN ASM_MESON_TAC [],
      ASM_REWRITE_TAC []]))

  /- Stillwell p.26-27 (Theorem 3 proof, second half): S_n is not solvable
     for n >= 5. The proof shows that any solvability chain
     G_0 > G_1 > ... > G_k = {1} must have all 3-cycles in every G_i,
     contradicting G_k = {1}. -/
  let NOT_SOLVABLE_SYMMETRIC_GROUP ← prove
   r"!s:A->bool. FINITE s /\ 5 <= CARD s
               ==> ~(solvable_group(symmetric_group s))"
   (← do
    let s2 ← SET_RULE (← q r"~(s SUBSET {x:A, y}) ==> ?z. z IN s /\ ~(z = x) /\ ~(z = y)")
    let s1 ← SET_RULE (← q r"~(s SUBSET {x:A}) ==> ?y. y IN s /\ ~(y = x)")
    pure (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [solvable_group]) THEN
    REWRITE_TAC [SYMMETRIC_GROUP_ID] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "k:num") (X_CHOOSE_THEN (← q r"c:num->(A->A)->bool")
      STRIP_ASSUME_TAC)) THEN
    -- Induction: all 3-cycles are in c(i) for i <= k
    SUBGOAL_THEN
      (← q r"!i. i <= k
         ==> (c:num->(A->A)->bool) i subgroup_of symmetric_group (s:A->bool) /\
             (!a b c'. a IN s /\ b IN s /\ c' IN s /\
                       ~(a = b) /\ ~(b = c') /\ ~(a = c')
                       ==> three_cycle a b c' IN c i)")
      MP_TAC THENL
     [INDUCT_TAC THENL
       [-- Base case: i = 0
        DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [CARRIER_SUBGROUP_OF] THEN
        SIMP_TAC [THREE_CYCLE_IN_SYMMETRIC],
        -- Inductive step: SUC i <= k
        DISCH_TAC THEN
        SUBGOAL_THEN (← q "i <= (k:num)") ASSUME_TAC THENL
         [ASM_ARITH_TAC, ALL_TAC] THEN
        FIRST_X_ASSUM (MP_TAC o check (is_imp o concl)) THEN
        ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
        SUBGOAL_THEN (← q "i < (k:num)") ASSUME_TAC THENL
         [ASM_ARITH_TAC, ALL_TAC] THEN
        SUBGOAL_THEN
          (← q r"(c:num->(A->A)->bool) (SUC i) normal_subgroup_of
         subgroup_generated (symmetric_group (s:A->bool)) (c i) /\
         abelian_group(quotient_group
           (subgroup_generated (symmetric_group s) (c i)) (c(SUC i)))")
          STRIP_ASSUME_TAC THENL
         [FIRST_X_ASSUM (MP_TAC o SPEC (← q "i:num")) THEN ASM_REWRITE_TAC [],
          ALL_TAC] THEN
        -- c(SUC i) subgroup_of subgroup_generated(sym s)(c i)
        SUBGOAL_THEN
          (← q r"(c:num->(A->A)->bool) (SUC i) subgroup_of
         subgroup_generated (symmetric_group (s:A->bool)) (c i)")
          ASSUME_TAC THENL
         [ASM_MESON_TAC [NORMAL_SUBGROUP_IMP_SUBGROUP], ALL_TAC] THEN
        -- c(SUC i) subgroup_of symmetric_group s and SUBSET c(i)
        SUBGOAL_THEN
          (← q r"(c:num->(A->A)->bool) (SUC i) subgroup_of
         symmetric_group (s:A->bool) /\
         c(SUC i) SUBSET c i")
          STRIP_ASSUME_TAC THENL
         [MP_TAC (← ISPECL [← q r"symmetric_group (s:A->bool)",
                          ← q r"(c:num->(A->A)->bool) (SUC i)",
                          ← q r"(c:num->(A->A)->bool) i"]
            SUBGROUP_OF_SUBGROUP_GENERATED_SUBGROUP_EQ) THEN
          ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [],
          ALL_TAC] THEN
        CONJ_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
        -- All 3-cycles in c(SUC i) via generalized chain step
        MATCH_MP_TAC CHAIN_STEP_THREE_CYCLES_GEN THEN
        EXISTS_TAC (← q r"subgroup_generated (symmetric_group (s:A->bool))
                    ((c:num->(A->A)->bool) i)") THEN
        ASM_REWRITE_TAC [] THEN
        REPEAT CONJ_TAC THENL
         [REWRITE_TAC [SUBGROUP_GENERATED, SYMMETRIC_GROUP],
          REWRITE_TAC [SUBGROUP_GENERATED, SYMMETRIC_GROUP],
          ASM_SIMP_TAC [CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN
          ASM_REWRITE_TAC []]],
      -- Specialize to i = k: 3-cycles in c(k) = {I}, contradiction
      DISCH_THEN (MP_TAC o SPEC (← q "k:num")) THEN REWRITE_TAC [LE_REFL] THEN
      STRIP_TAC THEN
      -- Find 3 distinct elements in s
      SUBGOAL_THEN (← q "?x:A. x IN s") STRIP_ASSUME_TAC THENL
       [REWRITE_TAC [MEMBER_NOT_EMPTY] THEN
        DISCH_THEN SUBST_ALL_TAC THEN
        RULE_ASSUM_TAC (REWRITE_RULE [CARD_CLAUSES]) THEN ASM_ARITH_TAC,
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"?y:A. y IN s /\ ~(y = x)") STRIP_ASSUME_TAC THENL
       [MATCH_MP_TAC s1 THEN
        DISCH_THEN (MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ] CARD_SUBSET)) THEN
        REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY] THEN
        MP_TAC (← ISPEC (← q "x:A") CARD_SING) THEN ASM_ARITH_TAC,
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"?z:A. z IN s /\ ~(z = x) /\ ~(z = y)") STRIP_ASSUME_TAC THENL
       [MATCH_MP_TAC s2 THEN
        DISCH_THEN (MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ] CARD_SUBSET)) THEN
        REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY] THEN
        MP_TAC (← ISPECL [← q "x:A", ← q "y:A"] CARD_LE_2) THEN ASM_ARITH_TAC,
        ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [← q "x:A", ← q "y:A", ← q "z:A"]) THEN
      ASM_REWRITE_TAC [IN_SING] THEN DISCH_TAC THEN
      MP_TAC (← ISPECL [← q "x:A", ← q "y:A", ← q "z:A"] THREE_CYCLE_NOT_I) THEN
      ASM_MESON_TAC [THREE_CYCLE_NOT_I]]))

  -- @@RETURN BEGIN
  return { CHAIN_STEP_THREE_CYCLES_GEN, NOT_SOLVABLE_SYMMETRIC_GROUP }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Transpositions and generators of the symmetric group                      -/
/- ------------------------------------------------------------------------- -/

structure Transpositions where
  -- @@FIELDS
  POINT_TRANSPOSITIONS_GENERATE_ALL : thm
  RESTRICT_SYMMETRIC_GROUP_HOMOMORPHISM : thm
  SUBGROUP_RESTRICT_PERMUTES : thm
  ALL_TRANSPOSITIONS_GENERATE_SYMMETRIC : thm
  deriving Inhabited

@[nospecialize]
def setupTranspositions [HolBase] (D : SymmetricGroupDeps) (BBasics : Basics) :
    ExceptT String IO Transpositions := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, SET_TAC, .. } := D
  let { CARRIER_SUBGROUP_GENERATED_SUBGROUP, FORALL_IN_IMAGE, INTER_SUBSET,
        IN_ELIM_THM, IN_INTER, IN_SUBGROUP_INV, IN_SUBGROUP_MUL, .. } := D.core1
  let { PERMUTES_COMPOSE, PERMUTES_I, PERMUTES_INDUCT_STRONG, PERMUTES_INVERSE,
        PERMUTES_SUBSET, RESTRICT_COMPOSE, RESTRICT_I, RESTRICT_INVERSE,
        RESTRICT_PERMUTES_SUBSET, SUBGROUP_GENERATED, SUBSET, SWAP_REFL, SWAP_SYM,
        SWAP_TRIPLE_ALT, group_homomorphism, subgroup_of, .. } := D.core2
  let { SYMMETRIC_GROUP, .. } := BBasics
  -- @@SCOPE END

  /- Transpositions from a fixed point a generate all transpositions.
     If a subgroup h of S_s contains swap(a,x) for every x in s \ {a},
     then it contains swap(x,y) for all distinct x,y in s. -/
  let POINT_TRANSPOSITIONS_GENERATE_ALL ← prove
   r"!s (a:A) h.
    a IN s /\
    h subgroup_of (symmetric_group s) /\
    (!x. x IN s /\ ~(x = a) ==> swap(a,x) IN h)
    ==> (!x y. x IN s /\ y IN s /\ ~(x = y) ==> swap(x,y) IN h)"
   (REWRITE_TAC [subgroup_of, SYMMETRIC_GROUP] THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q "x:A = a") THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    ASM_CASES_TAC (← q "y:A = a") THENL [ASM_MESON_TAC [SWAP_SYM], ALL_TAC] THEN
    ASM_CASES_TAC (← q "x:A = y") THENL [ASM_MESON_TAC [SWAP_REFL], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"swap(x:A,y) = swap(a,x) o swap(a,y) o swap(a,x)")
    SUBST1_TAC THEN ASM_MESON_TAC [SWAP_TRIPLE_ALT])

  /- The restriction map is a group homomorphism from any subgroup of
     symmetric_group s that preserves t, to symmetric_group t -/
  let RESTRICT_SYMMETRIC_GROUP_HOMOMORPHISM ← prove
   r"!s t (h:(A->A)->bool).
    FINITE t /\ t SUBSET s /\
    h subgroup_of symmetric_group s /\
    (!f. f IN h ==> IMAGE f t = t)
    ==> group_homomorphism
         (subgroup_generated (symmetric_group s) h,
          symmetric_group t)
         (\f:A->A. \x:A. if x IN t then f x else x)"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
      (← q r"group_carrier(subgroup_generated (symmetric_group s) (h:(A->A)->bool)) = h")
      ASSUME_TAC THENL
     [ASM_SIMP_TAC [CARRIER_SUBGROUP_GENERATED_SUBGROUP], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!f:A->A. f IN h ==> f permutes s") ASSUME_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN
      RULE_ASSUM_TAC (REWRITE_RULE
        [subgroup_of, SYMMETRIC_GROUP, SUBSET, IN_ELIM_THM]) THEN
      ASM_MESON_TAC [],
      ALL_TAC] THEN
    REWRITE_TAC [group_homomorphism] THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [SUBGROUP_GENERATED, SYMMETRIC_GROUP] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    REPEAT CONJ_TAC THENL
     [-- IMAGE: restriction permutes t
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN
      X_GEN_TAC (← q "f:A->A") THEN DISCH_TAC THEN
      MP_TAC (← ISPECL [← q r"s:A->bool", ← q r"t:A->bool", ← q "f:A->A"]
        RESTRICT_PERMUTES_SUBSET) THEN
      ASM_SIMP_TAC [],
      -- Identity: restrict(I) = I
      REWRITE_TAC [RESTRICT_I],
      -- Inverse: restrict(inverse f) = inverse(restrict f)
      X_GEN_TAC (← q "f:A->A") THEN DISCH_TAC THEN
      MP_TAC (← ISPECL [← q r"s:A->bool", ← q r"t:A->bool", ← q "f:A->A"]
        RESTRICT_INVERSE) THEN
      ASM_SIMP_TAC [],
      -- Multiplication: restrict(f o g) = restrict(f) o restrict(g)
      MAP_EVERY X_GEN_TAC [← q "f:A->A", ← q "g:A->A"] THEN STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"s:A->bool", ← q r"t:A->bool", ← q "f:A->A", ← q "g:A->A"]
        RESTRICT_COMPOSE) THEN
      ASM_SIMP_TAC []])

  /- Helper: restricting a subgroup of symmetric_group(s) to permutations of
     a subset t gives a subgroup of symmetric_group(t). -/
  let SUBGROUP_RESTRICT_PERMUTES ← prove
   r"!s t (h:(A->A)->bool).
    t SUBSET s /\
    h subgroup_of (symmetric_group s)
    ==> (h INTER group_carrier(symmetric_group t)) subgroup_of
        (symmetric_group t)"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [subgroup_of, SYMMETRIC_GROUP, INTER_SUBSET] THEN
    REWRITE_TAC [IN_INTER, IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THENL
     [-- I IN h
      ASM_MESON_TAC [subgroup_of, SYMMETRIC_GROUP],
      -- I permutes t
      REWRITE_TAC [PERMUTES_I],
      -- Closed under inverse
      X_GEN_TAC (← q "p:A->A") THEN STRIP_TAC THEN CONJ_TAC THENL
       [SUBGOAL_THEN (← q r"(p:A->A) IN group_carrier(symmetric_group (s:A->bool))")
          ASSUME_TAC THENL
         [REWRITE_TAC [SYMMETRIC_GROUP, IN_ELIM_THM] THEN
          MATCH_MP_TAC PERMUTES_SUBSET THEN EXISTS_TAC (← q r"t:A->bool") THEN
          ASM_REWRITE_TAC [],
          ALL_TAC] THEN
        SUBGOAL_THEN (← q r"inverse (p:A->A) =
         group_inv (symmetric_group (s:A->bool)) p") SUBST1_TAC THENL
         [REWRITE_TAC [SYMMETRIC_GROUP], ALL_TAC] THEN
        ASM_MESON_TAC [IN_SUBGROUP_INV],
        MATCH_MP_TAC PERMUTES_INVERSE THEN ASM_REWRITE_TAC []],
      -- Closed under composition
      MAP_EVERY X_GEN_TAC [← q "p:A->A", ← q "q:A->A"] THEN STRIP_TAC THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN (← q r"(p:A->A) IN group_carrier(symmetric_group (s:A->bool)) /\
                     (q:A->A) IN group_carrier(symmetric_group (s:A->bool))")
          STRIP_ASSUME_TAC THENL
         [REWRITE_TAC [SYMMETRIC_GROUP, IN_ELIM_THM] THEN CONJ_TAC THEN
          MATCH_MP_TAC PERMUTES_SUBSET THEN EXISTS_TAC (← q r"t:A->bool") THEN
          ASM_REWRITE_TAC [],
          ALL_TAC] THEN
        SUBGOAL_THEN (← q r"(p:A->A) o (q:A->A) =
         group_mul (symmetric_group (s:A->bool)) p q") SUBST1_TAC THENL
         [REWRITE_TAC [SYMMETRIC_GROUP], ALL_TAC] THEN
        MATCH_MP_TAC IN_SUBGROUP_MUL THEN ASM_REWRITE_TAC [],
        MATCH_MP_TAC PERMUTES_COMPOSE THEN ASM_REWRITE_TAC []]])

  /- Every permutation of a finite set is generated by transpositions.
     If a subgroup of S_s contains all transpositions, it contains all of S_s. -/
  let ALL_TRANSPOSITIONS_GENERATE_SYMMETRIC ← prove
   r"!s (h:(A->A)->bool).
    FINITE s /\
    h subgroup_of (symmetric_group s) /\
    (!a b. a IN s /\ b IN s /\ ~(a = b) ==> swap(a,b) IN h)
    ==> group_carrier(symmetric_group s) SUBSET h"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [SYMMETRIC_GROUP, SUBSET, IN_ELIM_THM] THEN
    MATCH_MP_TAC PERMUTES_INDUCT_STRONG THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [subgroup_of]) THEN
    REWRITE_TAC [SYMMETRIC_GROUP] THEN ASM SET_TAC [])

  -- @@RETURN BEGIN
  return { POINT_TRANSPOSITIONS_GENERATE_ALL, RESTRICT_SYMMETRIC_GROUP_HOMOMORPHISM,
           SUBGROUP_RESTRICT_PERMUTES, ALL_TRANSPOSITIONS_GENERATE_SYMMETRIC }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Machinery for: transposition + p-cycle generates S_p                      -/
/- ------------------------------------------------------------------------- -/

structure PcycleMachinery where
  -- @@FIELDS
  SYMMETRIC_GROUP_POW : thm
  SYMMETRIC_GROUP_POW_IN : thm
  PRIME_ORDER_PERM_NO_FIXPOINT : thm
  deriving Inhabited

@[nospecialize]
def setupPcycleMachinery [HolBase] (D : SymmetricGroupDeps) (BBasics : Basics) :
    ExceptT String IO PcycleMachinery := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, .. } := D
  let { CARD_DELETE, DIVIDES_FACT_PRIME, DIVIDES_REFL, FINITE_DELETE,
        GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER, GROUP_ELEMENT_ORDER_EQ_1,
        GROUP_ELEMENT_ORDER_ID, GROUP_POW_EQ_ID, IN_DELETE, IN_DIFF, IN_ELIM_THM,
        I_THM, .. } := D.core1
  let { PERMUTES_IN_IMAGE, PERMUTES_SUPERSET, PRIME_0, PRIME_1, group_pow, o_THM,
        prime, .. } := D.core2
  let { CARD_SYMMETRIC_GROUP, FINITE_SYMMETRIC_GROUP, SYMMETRIC_GROUP, .. } := BBasics
  -- @@SCOPE END

  -- group_pow in symmetric_group is independent of the underlying set
  let SYMMETRIC_GROUP_POW ← prove
   r"!s t (sigma:A->A) n.
     group_pow (symmetric_group s) sigma n =
     group_pow (symmetric_group t) sigma n"
   (GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [group_pow, SYMMETRIC_GROUP])

  -- group_pow in symmetric_group preserves membership
  let SYMMETRIC_GROUP_POW_IN ← prove
   r"!s (sigma:A->A) n a.
     sigma permutes s /\ a IN s
     ==> group_pow (symmetric_group s) sigma n a IN s"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC [group_pow, SYMMETRIC_GROUP, I_THM, o_THM] THENL
     [MESON_TAC [],
      ASM_MESON_TAC [PERMUTES_IN_IMAGE]])

  -- Element of prime order p in S_p has no fixed points
  let PRIME_ORDER_PERM_NO_FIXPOINT ← prove
   r"!s (sigma:A->A) a.
     FINITE s /\ prime(CARD s) /\
     sigma permutes s /\
     group_element_order (symmetric_group s) sigma = CARD s /\
     a IN s
     ==> ~(sigma a = a)"
   (← do
    let a1 ← ARITH_RULE (← q r"~(p = 0) /\ ~(p = 1) ==> ~(p <= p - 1)")
    pure (REPEAT STRIP_TAC THEN
    -- sigma permutes s DELETE a
    SUBGOAL_THEN (← q r"(sigma:A->A) permutes (s DELETE (a:A))") ASSUME_TAC THENL
     [MATCH_MP_TAC PERMUTES_SUPERSET THEN EXISTS_TAC (← q r"s:A->bool") THEN
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [IN_DIFF, IN_DELETE] THEN
      ASM_MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(sigma:A->A) IN
    group_carrier(symmetric_group(s DELETE (a:A)))") ASSUME_TAC THENL
     [ASM_REWRITE_TAC [SYMMETRIC_GROUP, IN_ELIM_THM], ALL_TAC] THEN
    -- sigma^(CARD s) = I in symmetric_group s
    SUBGOAL_THEN (← q r"group_pow (symmetric_group (s:A->bool))
    (sigma:A->A) (CARD s) = group_id(symmetric_group s)") ASSUME_TAC THENL
     [ASM_SIMP_TAC [GROUP_POW_EQ_ID, SYMMETRIC_GROUP, IN_ELIM_THM,
                   DIVIDES_REFL],
      ALL_TAC] THEN
    -- Transfer to symmetric_group(s DELETE a)
    SUBGOAL_THEN (← q r"group_pow (symmetric_group (s DELETE (a:A)))
    (sigma:A->A) (CARD(s:A->bool)) =
    group_id(symmetric_group(s DELETE a))") ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q r"s DELETE (a:A)", ← q r"s:A->bool", ← q "sigma:A->A",
                      ← q r"CARD(s:A->bool)"] SYMMETRIC_GROUP_POW) THEN
      ASM_REWRITE_TAC [SYMMETRIC_GROUP],
      ALL_TAC] THEN
    -- group_element_order in symm(s DELETE a) divides CARD s
    SUBGOAL_THEN (← q r"group_element_order (symmetric_group(s DELETE (a:A)))
    (sigma:A->A) divides CARD(s:A->bool)") ASSUME_TAC THENL
     [ASM_SIMP_TAC [← GSYM GROUP_POW_EQ_ID],
      ALL_TAC] THEN
    -- Since prime(CARD s), the order is 1 or CARD s
    SUBGOAL_THEN
      (← q r"group_element_order (symmetric_group(s DELETE (a:A)))
      (sigma:A->A) = 1 \/
     group_element_order (symmetric_group(s DELETE (a:A)))
      (sigma:A->A) = CARD(s:A->bool)") MP_TAC THENL
     [ASM_MESON_TAC [prime], ALL_TAC] THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [-- Case: order = 1, so sigma = I
      MP_TAC (← ISPECL [← q r"symmetric_group(s DELETE (a:A))", ← q "sigma:A->A"]
        GROUP_ELEMENT_ORDER_EQ_1) THEN
      ASM_REWRITE_TAC [SYMMETRIC_GROUP] THEN DISCH_TAC THEN
      MP_TAC (← ISPEC (← q r"symmetric_group(s:A->bool)") GROUP_ELEMENT_ORDER_ID) THEN
      REWRITE_TAC [SYMMETRIC_GROUP] THEN
      ASM_MESON_TAC [PRIME_1],
      -- Case: order = CARD s, so CARD s divides FACT(CARD s - 1)
      SUBGOAL_THEN (← q r"(CARD(s:A->bool)) divides FACT(CARD s - 1)") MP_TAC THENL
       [SUBGOAL_THEN
          (← q r"FINITE(group_carrier(symmetric_group(s DELETE (a:A))))")
          ASSUME_TAC THENL
         [ASM_SIMP_TAC [FINITE_SYMMETRIC_GROUP, FINITE_DELETE], ALL_TAC] THEN
        MP_TAC (← ISPECL [← q r"symmetric_group(s DELETE (a:A))", ← q "sigma:A->A"]
          GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER) THEN
        ASM_REWRITE_TAC [] THEN
        ASM_SIMP_TAC [CARD_SYMMETRIC_GROUP, FINITE_DELETE, CARD_DELETE],
        ASM_SIMP_TAC [DIVIDES_FACT_PRIME] THEN
        ASM_MESON_TAC [PRIME_0, PRIME_1, a1]]]))

  -- @@RETURN BEGIN
  return { SYMMETRIC_GROUP_POW, SYMMETRIC_GROUP_POW_IN, PRIME_ORDER_PERM_NO_FIXPOINT }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Powers of a prime-order permutation and the orbit it generates.           -/
/- (symmetric_group.ml 486-634)                                              -/
/- ------------------------------------------------------------------------- -/

structure PowOrbit where
  -- @@FIELDS
  PRIME_ORDER_POW_PERM : thm
  PRIME_ORDER_PERM_ORBIT : thm
  deriving Inhabited

@[nospecialize]
def setupPowOrbit [HolBase] (D : SymmetricGroupDeps) (BBasics : Basics) (BPcycleMachinery : PcycleMachinery) :
    ExceptT String IO PowOrbit := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, MESON_TAC, .. } := D
  let { CARD_IMAGE_INJ, CARD_NUMSEG_LT, CARD_SUBSET_EQ, COPRIME_GCD, DIVIDES_LE, DIV_1,
        EQ_TRANS, EXTENSION, FINITE_NUMSEG_LT, GROUP_ELEMENT_ORDER_POW_GEN, GROUP_POW,
        GROUP_POW_ADD, IN_ELIM_THM, IN_IMAGE, .. } := D.core1
  let { PERMUTES_INJECTIVE, PRIME_COPRIME_EQ, SUBSET, o_THM, .. } := D.core2
  let { SYMMETRIC_GROUP, .. } := BBasics
  let { PRIME_ORDER_PERM_NO_FIXPOINT, SYMMETRIC_GROUP_POW_IN, .. } := BPcycleMachinery
  -- @@SCOPE END

  -- Helper: order of sigma^d is still CARD s when 0 < d < CARD s
  let PRIME_ORDER_POW_PERM ← prove
   r"!s (sigma:A->A) d.
     FINITE s /\ prime(CARD s) /\
     sigma permutes s /\
     group_element_order (symmetric_group s) sigma = CARD s /\
     0 < d /\ d < CARD s
     ==> group_element_order (symmetric_group s)
           (group_pow (symmetric_group s) sigma d) = CARD s"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"symmetric_group(s:A->bool)", ← q "sigma:A->A", ← q "d:num"]
      GROUP_ELEMENT_ORDER_POW_GEN) THEN
    ASM_REWRITE_TAC [SYMMETRIC_GROUP, IN_ELIM_THM] THEN
    ASM_SIMP_TAC [← ARITH_RULE (← q r"0 < d ==> ~(d = 0)")] THEN
    SUBGOAL_THEN (← q r"gcd(CARD(s:A->bool), d) = 1") SUBST1_TAC THENL
     [REWRITE_TAC [← GSYM COPRIME_GCD] THEN
      ASM_SIMP_TAC [PRIME_COPRIME_EQ] THEN
      DISCH_TAC THEN
      MP_TAC (← ISPECL [← q r"CARD(s:A->bool)", ← q "d:num"] DIVIDES_LE) THEN
      ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC,
      REWRITE_TAC [DIV_1]])

  -- Orbit of a prime-order permutation covers the whole set
  let PRIME_ORDER_PERM_ORBIT ← prove
   r"!s (sigma:A->A) a x.
     FINITE s /\ prime(CARD s) /\
     sigma permutes s /\
     group_element_order (symmetric_group s) sigma = CARD s /\
     a IN s /\ x IN s
     ==> ?k. k < CARD s /\
             group_pow (symmetric_group s) sigma k a = x"
   (← do
    -- the printing rules bound last-first, as OCaml evaluates the proof
    let a2 ← ARITH_RULE (← q r"~(i < j) /\ ~(i:num = j) ==> j + (i - j) = i")
    let a1 ← ARITH_RULE (← q r"i < j ==> i + (j - i) = j:num")
    pure (REPEAT STRIP_TAC THEN
    -- Show IMAGE (\k. sigma^k a) {k | k < CARD s} = s
    SUBGOAL_THEN
      (← q r"IMAGE (\k. group_pow (symmetric_group (s:A->bool)) (sigma:A->A) k a)
           {k | k < CARD s} = s") MP_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN
      DISCH_THEN (MP_TAC o SPEC (← q "x:A")) THEN ASM_REWRITE_TAC [] THEN
      MESON_TAC []] THEN
    MATCH_MP_TAC CARD_SUBSET_EQ THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [-- IMAGE is a subset of s
      REWRITE_TAC [SUBSET, IN_IMAGE, IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC SYMMETRIC_GROUP_POW_IN THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    -- CARD of IMAGE = CARD s by injectivity
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"CARD {k:num | k < CARD(s:A->bool)}") THEN CONJ_TAC THENL
     [MATCH_MP_TAC CARD_IMAGE_INJ THEN
      REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN
      -- Injectivity: sigma^i(a) = sigma^j(a) with i,j < p ==> i = j
      MAP_EVERY X_GEN_TAC [← q "i:num", ← q "j:num"] THEN STRIP_TAC THEN
      -- Suffices to show: for any d with 0 < d < CARD s,
      --    sigma^d(a) <> a. Then i = j by contradiction.
      ASM_CASES_TAC (← q "i:num = j") THEN ASM_REWRITE_TAC [] THEN
      -- Derive a contradictory fixed point
      SUBGOAL_THEN (← q r"?d. 0 < d /\ d < CARD(s:A->bool) /\
      group_pow (symmetric_group s) (sigma:A->A) d a = a") MP_TAC THENL
       [ASM_CASES_TAC (← q "i:num < j") THENL
         [EXISTS_TAC (← q "j - i:num") THEN CONJ_TAC THENL
           [ASM_ARITH_TAC, ALL_TAC] THEN
          CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
          -- sigma^j(a) = (sigma^i o sigma^{j-i})(a), and
          --    sigma^j(a) = sigma^i(a)
          MP_TAC (← ISPECL [← q r"symmetric_group(s:A->bool)", ← q "sigma:A->A",
                          ← q "i:num", ← q "j - i:num"] GROUP_POW_ADD) THEN
          ASM_REWRITE_TAC [SYMMETRIC_GROUP, IN_ELIM_THM] THEN
          ASM_SIMP_TAC [a1] THEN
          REWRITE_TAC [SYMMETRIC_GROUP, o_THM] THEN DISCH_TAC THEN
          MP_TAC (← ISPECL
            [← q r"group_pow (symmetric_group (s:A->bool)) (sigma:A->A) i",
             ← q "s:A->bool"] PERMUTES_INJECTIVE) THEN
          ANTS_TAC THENL
           [MP_TAC (← ISPECL [← q r"symmetric_group(s:A->bool)", ← q "sigma:A->A", ← q "i:num"]
              GROUP_POW) THEN
            ASM_REWRITE_TAC [SYMMETRIC_GROUP, IN_ELIM_THM],
            ALL_TAC] THEN
          DISCH_THEN (fun th => tactic_of do
            let sp ← SPECL
             [← q r"group_pow (symmetric_group (s:A->bool)) (sigma:A->A) (j - i) (a:A)",
              ← q "a:A"] th
            pure (MP_TAC (← EQ_IMP_RULE sp).1)) THEN
          ANTS_TAC THENL
           [UNDISCH_TAC
             (← q r"group_pow (symmetric_group (s:A->bool)) (sigma:A->A) j =
            group_pow (symmetric_group s) sigma i o
            group_pow (symmetric_group s) sigma (j - i)") THEN
            DISCH_THEN (fun th => tactic_of do
              pure (REWRITE_TAC [← GSYM (← REWRITE_RULE [o_THM] (← AP_THM th (← q "a:A")))])) THEN
            ASM_REWRITE_TAC [],
            REWRITE_TAC []],
          -- i > j case: symmetric, use i - j
          EXISTS_TAC (← q "i - j:num") THEN CONJ_TAC THENL
           [ASM_ARITH_TAC, ALL_TAC] THEN
          CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
          MP_TAC (← ISPECL [← q r"symmetric_group(s:A->bool)", ← q "sigma:A->A",
                          ← q "j:num", ← q "i - j:num"] GROUP_POW_ADD) THEN
          ASM_REWRITE_TAC [SYMMETRIC_GROUP, IN_ELIM_THM] THEN
          ASM_SIMP_TAC [a2] THEN
          REWRITE_TAC [SYMMETRIC_GROUP, o_THM] THEN DISCH_TAC THEN
          MP_TAC (← ISPECL
            [← q r"group_pow (symmetric_group (s:A->bool)) (sigma:A->A) j",
             ← q "s:A->bool"] PERMUTES_INJECTIVE) THEN
          ANTS_TAC THENL
           [MP_TAC (← ISPECL [← q r"symmetric_group(s:A->bool)", ← q "sigma:A->A", ← q "j:num"]
              GROUP_POW) THEN
            ASM_REWRITE_TAC [SYMMETRIC_GROUP, IN_ELIM_THM],
            ALL_TAC] THEN
          DISCH_THEN (fun th => tactic_of do
            let sp ← SPECL
             [← q r"group_pow (symmetric_group (s:A->bool)) (sigma:A->A) (i - j) (a:A)",
              ← q "a:A"] th
            pure (MP_TAC (← EQ_IMP_RULE sp).1)) THEN
          ANTS_TAC THENL
           [UNDISCH_TAC
             (← q r"group_pow (symmetric_group (s:A->bool)) (sigma:A->A) i =
            group_pow (symmetric_group s) sigma j o
            group_pow (symmetric_group s) sigma (i - j)") THEN
            DISCH_THEN (fun th => tactic_of do
              pure (REWRITE_TAC [← GSYM (← REWRITE_RULE [o_THM] (← AP_THM th (← q "a:A")))])) THEN
            FIRST_X_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← SYM th])),
            REWRITE_TAC []]],
        ALL_TAC] THEN
      -- Now we have d with 0 < d < CARD s and sigma^d(a) = a
      STRIP_TAC THEN
      SUBGOAL_THEN
        (← q r"group_pow (symmetric_group (s:A->bool)) (sigma:A->A) d
       permutes s") ASSUME_TAC THENL
       [MP_TAC (← ISPECL [← q r"symmetric_group(s:A->bool)", ← q "sigma:A->A", ← q "d:num"]
          GROUP_POW) THEN
        ASM_REWRITE_TAC [SYMMETRIC_GROUP, IN_ELIM_THM],
        ALL_TAC] THEN
      SUBGOAL_THEN
        (← q r"group_element_order (symmetric_group (s:A->bool))
        (group_pow (symmetric_group s) (sigma:A->A) d) = CARD s")
        ASSUME_TAC THENL
       [MATCH_MP_TAC PRIME_ORDER_POW_PERM THEN ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      MP_TAC (← ISPECL [← q "s:A->bool",
        ← q r"group_pow (symmetric_group (s:A->bool)) (sigma:A->A) d",
        ← q "a:A"] PRIME_ORDER_PERM_NO_FIXPOINT) THEN
      ASM_REWRITE_TAC [],
      REWRITE_TAC [CARD_NUMSEG_LT]]))

  -- @@RETURN BEGIN
  return { PRIME_ORDER_POW_PERM, PRIME_ORDER_PERM_ORBIT }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Conjugating a transposition inside a subgroup, and a transposition        -/
/- together with a p-cycle generating the whole symmetric group.             -/
/- (symmetric_group.ml 635-890)                                              -/
/- ------------------------------------------------------------------------- -/

structure SwapGen where
  -- @@FIELDS
  SWAP_CONJUGATE_IN_SUBGROUP : thm
  TRANSPOSITION_PCYCLE_GENERATES : thm
  deriving Inhabited

@[nospecialize]
def setupSwapGen [HolBase] (D : SymmetricGroupDeps) (BBasics : Basics) (BTranspositions : Transpositions) (BPcycleMachinery : PcycleMachinery) (BPowOrbit : PowOrbit) :
    ExceptT String IO SwapGen := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, .. } := D
  let { ADD1, GROUP_POW, GROUP_POW_1, GROUP_POW_ADD, IN_ELIM_THM,
        IN_SUBGROUP_CONJUGATION, IN_SUBGROUP_MUL, IN_SUBGROUP_POW, I_THM, .. } := D.core1
  let { LT_NZ, ONE, SUBGROUP_OF_IMP_SUBSET, SUBSET, SWAP_CONJUGATE, SWAP_SYM,
        SWAP_TRIPLE, SWAP_TRIPLE_ALT, group_conjugation, group_pow, o_ASSOC, o_THM, .. } := D.core2
  let { SYMMETRIC_GROUP, .. } := BBasics
  let { ALL_TRANSPOSITIONS_GENERATE_SYMMETRIC, .. } := BTranspositions
  let { PRIME_ORDER_PERM_NO_FIXPOINT, SYMMETRIC_GROUP_POW_IN, .. } := BPcycleMachinery
  let { PRIME_ORDER_PERM_ORBIT, PRIME_ORDER_POW_PERM, .. } := BPowOrbit
  -- @@SCOPE END

  -- Helper: conjugate of swap(a,b) by sigma^k is swap(sigma^k a, sigma^k b)
  let SWAP_CONJUGATE_IN_SUBGROUP ← prove
   r"!s (sigma:A->A) a b h k.
     FINITE s /\
     h subgroup_of symmetric_group s /\
     sigma permutes s /\
     sigma IN h /\
     swap(a,b) IN h /\
     a IN s /\ b IN s
     ==> swap(group_pow (symmetric_group s) sigma k a,
              group_pow (symmetric_group s) sigma k b) IN h"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
      (← q r"group_pow (symmetric_group (s:A->bool)) (sigma:A->A) k permutes s")
      ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q r"symmetric_group(s:A->bool)", ← q "sigma:A->A", ← q "k:num"]
        GROUP_POW) THEN
      ASM_REWRITE_TAC [SYMMETRIC_GROUP, IN_ELIM_THM],
      ALL_TAC] THEN
    SUBGOAL_THEN
      (← q r"swap(group_pow (symmetric_group (s:A->bool)) (sigma:A->A) k a,
          group_pow (symmetric_group s) sigma k b) =
     group_conjugation (symmetric_group s)
       (group_pow (symmetric_group s) sigma k) (swap(a:A,b))")
      SUBST1_TAC THENL
     [REWRITE_TAC [group_conjugation, SYMMETRIC_GROUP, o_ASSOC] THEN
      MP_TAC (← ISPECL [← q r"group_pow (symmetric_group (s:A->bool)) (sigma:A->A) k",
                      ← q "s:A->bool", ← q "a:A", ← q "b:A"] SWAP_CONJUGATE) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← SYM th])) THEN
      REWRITE_TAC [o_ASSOC],
      ALL_TAC] THEN
    MATCH_MP_TAC IN_SUBGROUP_CONJUGATION THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC IN_SUBGROUP_POW THEN
    ASM_REWRITE_TAC [])

  /- A transposition and a p-cycle generate S_p. The key step is showing that
     swap(a,x) IN h for all x in s, by setting tau = sigma^m where b = tau(a)
     and inducting on k to get swap(a, tau^k(a)) IN h using SWAP_TRIPLE.      -/
  let TRANSPOSITION_PCYCLE_GENERATES ← prove
   r"!s (sigma:A->A) a b h.
     FINITE s /\ prime(CARD s) /\
     h subgroup_of symmetric_group s /\
     sigma IN h /\
     group_element_order (symmetric_group s) sigma = CARD s /\
     swap(a,b) IN h /\
     a IN s /\ b IN s /\ ~(a = b)
     ==> group_carrier(symmetric_group s) SUBSET h"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"(sigma:A->A) permutes s") ASSUME_TAC THENL
     [MP_TAC (← ISPEC (← q r"symmetric_group(s:A->bool)") SUBGROUP_OF_IMP_SUBSET) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"h:(A->A)->bool")) THEN
      ASM_REWRITE_TAC [SYMMETRIC_GROUP, IN_ELIM_THM, SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    -- Step 1: Show swap(x,y) IN h for all x,y IN s with x <> y
    MATCH_MP_TAC ALL_TRANSPOSITIONS_GENERATE_SYMMETRIC THEN
    ASM_REWRITE_TAC [] THEN
    -- Step 2: First show swap(a,x) IN h for all x IN s with x <> a
    SUBGOAL_THEN (← q r"!x:A. x IN s /\ ~(x = a) ==> swap(a,x) IN h")
      ASSUME_TAC THENL
     [ALL_TAC,
      -- Then derive swap(x,y) IN h for all x,y IN s
      MAP_EVERY X_GEN_TAC [← q "x':A", ← q "y':A"] THEN STRIP_TAC THEN
      ASM_CASES_TAC (← q r"(x':A) = a") THENL
       [ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_MESON_TAC [],
        ALL_TAC] THEN
      ASM_CASES_TAC (← q r"(y':A) = a") THENL
       [ASM_REWRITE_TAC [SWAP_SYM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_MESON_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"swap(x':A,y') =
      group_mul (symmetric_group (s:A->bool))
        (swap(a,x'))
        (group_mul (symmetric_group s) (swap(a,y')) (swap(a:A,x')))")
      SUBST1_TAC THENL
       [REWRITE_TAC [SYMMETRIC_GROUP] THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC SWAP_TRIPLE_ALT THEN
        ASM_MESON_TAC [],
        ALL_TAC] THEN
      MATCH_MP_TAC IN_SUBGROUP_MUL THEN ASM_REWRITE_TAC [] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC [],
        MATCH_MP_TAC IN_SUBGROUP_MUL THEN ASM_REWRITE_TAC [] THEN
        CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC []]] THEN
    -- Now prove: for all x IN s with x <> a, swap(a,x) IN h
    X_GEN_TAC (← q "c:A") THEN STRIP_TAC THEN
    -- b = sigma^m(a) for some m with 0 < m < p by orbit
    MP_TAC (← ISPECL [← q "s:A->bool", ← q "sigma:A->A", ← q "a:A", ← q "b:A"]
      PRIME_ORDER_PERM_ORBIT) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "m:num") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q "0 < m") ASSUME_TAC THENL
     [ASM_CASES_TAC (← q "m = 0") THEN ASM_REWRITE_TAC [LT_NZ] THEN
      UNDISCH_TAC
       (← q r"group_pow (symmetric_group (s:A->bool)) (sigma:A->A) m a = b") THEN
      ASM_REWRITE_TAC [group_pow, SYMMETRIC_GROUP, I_THM] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    -- Let tau = sigma^m. tau permutes s with order p, and tau(a) = b
    ABBREV_TAC (← q r"tau:A->A = group_pow (symmetric_group s) sigma m") THEN
    SUBGOAL_THEN (← q r"(tau:A->A) permutes s") ASSUME_TAC THENL
     [EXPAND_TAC "tau" THEN
      MP_TAC (← ISPECL [← q r"symmetric_group(s:A->bool)", ← q "sigma:A->A", ← q "m:num"]
        GROUP_POW) THEN
      ASM_REWRITE_TAC [SYMMETRIC_GROUP, IN_ELIM_THM],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"group_element_order (symmetric_group (s:A->bool)) (tau:A->A) =
                CARD s") ASSUME_TAC THENL
     [EXPAND_TAC "tau" THEN
      MP_TAC (← ISPECL [← q "s:A->bool", ← q "sigma:A->A", ← q "m:num"]
        PRIME_ORDER_POW_PERM) THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(tau:A->A) a = b") ASSUME_TAC THENL
     [EXPAND_TAC "tau" THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(tau:A->A) IN h") ASSUME_TAC THENL
     [EXPAND_TAC "tau" THEN
      MATCH_MP_TAC IN_SUBGROUP_POW THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"swap(a:A,b) IN h") ASSUME_TAC THENL
     [ASM_REWRITE_TAC [], ALL_TAC] THEN
    -- c = tau^n(a) for some n with 0 < n < p by orbit
    MP_TAC (← ISPECL [← q "s:A->bool", ← q "tau:A->A", ← q "a:A", ← q "c:A"]
      PRIME_ORDER_PERM_ORBIT) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "n:num") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q "0 < n") ASSUME_TAC THENL
     [ASM_CASES_TAC (← q "n = 0") THEN ASM_REWRITE_TAC [LT_NZ] THEN
      UNDISCH_TAC
       (← q r"group_pow (symmetric_group (s:A->bool)) (tau:A->A) n a = c") THEN
      ASM_REWRITE_TAC [group_pow, SYMMETRIC_GROUP, I_THM] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    -- Rewrite c back to tau^n(a) so the induction result can match
    UNDISCH_TAC (← q r"group_pow (symmetric_group (s:A->bool)) (tau:A->A) n a = c") THEN
    DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← SYM th])) THEN
    -- Goal is now: swap(a, group_pow ... tau n a) IN h
    SUBGOAL_THEN
      (← q r"!k. 0 < k /\ k < CARD(s:A->bool)
         ==> swap(a:A, group_pow (symmetric_group s) (tau:A->A) k a) IN h")
      (fun th => MATCH_MP_TAC th THEN ASM_REWRITE_TAC []) THEN
    INDUCT_TAC THENL [ARITH_TAC, ALL_TAC] THEN
    STRIP_TAC THEN
    ASM_CASES_TAC (← q "k = 0") THENL
     [-- Base: n = 1, tau^1(a) = tau(a) = b, swap(a,b) IN h
      ASM_REWRITE_TAC [ONE, group_pow, SYMMETRIC_GROUP, o_THM, I_THM],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"swap(a:A, group_pow (symmetric_group (s:A->bool)) (tau:A->A) k a) IN h")
    ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN
    -- tau^{SUC k}(a) = tau(tau^k(a))
    SUBGOAL_THEN
      (← q r"group_pow (symmetric_group (s:A->bool)) (tau:A->A) (SUC k) a =
     tau(group_pow (symmetric_group s) tau k a)")
      SUBST1_TAC THENL
     [REWRITE_TAC [group_pow, SYMMETRIC_GROUP, o_THM], ALL_TAC] THEN
    ABBREV_TAC
      (← q r"x0 = group_pow (symmetric_group (s:A->bool)) (tau:A->A) k (a:A)") THEN
    -- x0 IN s
    SUBGOAL_THEN (← q r"(x0:A) IN s") ASSUME_TAC THENL
     [EXPAND_TAC "x0" THEN MATCH_MP_TAC SYMMETRIC_GROUP_POW_IN THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    -- x0 <> a
    SUBGOAL_THEN (← q r"~((x0:A) = a)") ASSUME_TAC THENL
     [EXPAND_TAC "x0" THEN
      MP_TAC (← ISPECL [← q "s:A->bool",
        ← q r"group_pow (symmetric_group (s:A->bool)) (tau:A->A) k",
        ← q "a:A"] PRIME_ORDER_PERM_NO_FIXPOINT) THEN
      ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [MP_TAC (← ISPECL [← q r"symmetric_group(s:A->bool)", ← q "tau:A->A", ← q "k:num"]
            GROUP_POW) THEN
          ASM_REWRITE_TAC [SYMMETRIC_GROUP, IN_ELIM_THM],
          MP_TAC (← ISPECL [← q "s:A->bool", ← q "tau:A->A", ← q "k:num"]
            PRIME_ORDER_POW_PERM) THEN
          ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC],
        REWRITE_TAC []],
      ALL_TAC] THEN
    -- tau(x0) <> a: tau^{SUC k} has no fixed points
    SUBGOAL_THEN (← q r"~((tau:A->A) (x0:A) = a)") ASSUME_TAC THENL
     [EXPAND_TAC "x0" THEN
      SUBGOAL_THEN
        (← q r"(tau:A->A) (group_pow (symmetric_group (s:A->bool)) tau k a) =
       group_pow (symmetric_group s) tau (SUC k) a")
        SUBST1_TAC THENL
       [REWRITE_TAC [group_pow, SYMMETRIC_GROUP, o_THM], ALL_TAC] THEN
      MP_TAC (← ISPECL [← q "s:A->bool",
        ← q r"group_pow (symmetric_group (s:A->bool)) (tau:A->A) (SUC k)",
        ← q "a:A"] PRIME_ORDER_PERM_NO_FIXPOINT) THEN
      ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [MP_TAC (← ISPECL [← q r"symmetric_group(s:A->bool)", ← q "tau:A->A", ← q "SUC k"]
            GROUP_POW) THEN
          ASM_REWRITE_TAC [SYMMETRIC_GROUP, IN_ELIM_THM],
          MP_TAC (← ISPECL [← q "s:A->bool", ← q "tau:A->A", ← q "SUC k"]
            PRIME_ORDER_POW_PERM) THEN
          ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC],
        REWRITE_TAC []],
      ALL_TAC] THEN
    -- tau(x0) <> x0: tau has no fixed points
    SUBGOAL_THEN (← q r"~((tau:A->A) (x0:A) = x0)") ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q "s:A->bool", ← q "tau:A->A", ← q "x0:A"]
        PRIME_ORDER_PERM_NO_FIXPOINT) THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    -- swap(x0, tau(x0)) IN h by conjugation
    SUBGOAL_THEN (← q r"swap(x0:A, (tau:A->A) x0) IN h") ASSUME_TAC THENL
     [EXPAND_TAC "x0" THEN
      -- tau^k(a) and tau(tau^k(a)) = tau^k(tau(a)) = tau^k(b)
      SUBGOAL_THEN
        (← q r"(tau:A->A)(group_pow (symmetric_group (s:A->bool)) tau k a) =
       group_pow (symmetric_group s) tau k b")
        SUBST1_TAC THENL
       [SUBGOAL_THEN
          (← q r"(tau:A->A)(group_pow (symmetric_group (s:A->bool)) tau k a) =
         group_pow (symmetric_group s) tau k ((tau:A->A) a)")
          SUBST1_TAC THENL
         [-- tau(tau^k(a)) = tau^{k+1}(a) = tau^k(tau(a))
          SUBGOAL_THEN
            (← q r"(tau:A->A)(group_pow (symmetric_group (s:A->bool)) tau k a) =
           group_pow (symmetric_group s) tau (SUC k) a")
            SUBST1_TAC THENL
           [REWRITE_TAC [group_pow, SYMMETRIC_GROUP, o_THM], ALL_TAC] THEN
          REWRITE_TAC [ADD1] THEN
          MP_TAC (← ISPECL [← q r"symmetric_group(s:A->bool)", ← q "tau:A->A",
                          ← q "k:num", ← q "1"] GROUP_POW_ADD) THEN
          ANTS_TAC THENL
           [ASM_REWRITE_TAC [SYMMETRIC_GROUP, IN_ELIM_THM], ALL_TAC] THEN
          DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [th])) THEN
          REWRITE_TAC [SYMMETRIC_GROUP, o_THM] THEN
          MP_TAC (← ISPECL [← q r"symmetric_group(s:A->bool)", ← q "tau:A->A"]
            GROUP_POW_1) THEN
          ANTS_TAC THENL
           [ASM_REWRITE_TAC [SYMMETRIC_GROUP, IN_ELIM_THM], ALL_TAC] THEN
          DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [th])),
          ALL_TAC] THEN
        ASM_REWRITE_TAC [],
        MATCH_MP_TAC SWAP_CONJUGATE_IN_SUBGROUP THEN ASM_REWRITE_TAC []],
      ALL_TAC] THEN
    -- swap(a, tau(x0)) = swap(a,x0) o swap(x0,tau x0) o swap(a,x0)
    SUBGOAL_THEN (← q r"swap(a:A, (tau:A->A) x0) =
    group_mul (symmetric_group (s:A->bool))
      (swap(a,x0))
      (group_mul (symmetric_group s) (swap(x0, tau x0)) (swap(a:A,x0)))")
    SUBST1_TAC THENL
     [REWRITE_TAC [SYMMETRIC_GROUP] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC SWAP_TRIPLE THEN
      ASM_MESON_TAC [],
      ALL_TAC] THEN
    MATCH_MP_TAC IN_SUBGROUP_MUL THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC IN_SUBGROUP_MUL THEN ASM_REWRITE_TAC [])

  -- @@RETURN BEGIN
  return { SWAP_CONJUGATE_IN_SUBGROUP, TRANSPOSITION_PCYCLE_GENERATES }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Main theorem: a transitive subgroup containing a transposition generates  -/
/- the whole symmetric group when the degree is prime.                       -/
/- (symmetric_group.ml 891-968)                                              -/
/- ------------------------------------------------------------------------- -/

structure Transitive where
  -- @@FIELDS
  TRANSITIVE_TRANSPOSITION_GENERATES_SYMMETRIC : thm
  deriving Inhabited

@[nospecialize]
def setupTransitive [HolBase] (D : SymmetricGroupDeps) (BBasics : Basics) (BCayley : Cayley) (BSwapGen : SwapGen) :
    ExceptT String IO Transitive := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, .. } := D
  let { CARRIER_SUBGROUP_GENERATED_SUBGROUP, CAUCHY_GROUP_THEOREM, FINITE_SUBSET,
        GROUP_ACTION_FROM_SUBGROUP, GROUP_ELEMENT_ORDER_SUBGROUP_GENERATED,
        GROUP_ORBIT_SUBSET, IN_GROUP_ORBIT, .. } := D.core1
  let { MULT_SYM, ORBIT_STABILIZER_MUL, SUBGROUP_OF_IMP_SUBSET, SUBSET,
        SUBSET_ANTISYM_EQ, divides, .. } := D.core2
  let { FINITE_SYMMETRIC_GROUP, .. } := BBasics
  let { SYMMETRIC_GROUP_ACTION, .. } := BCayley
  let { TRANSPOSITION_PCYCLE_GENERATES, .. } := BSwapGen
  -- @@SCOPE END

  -- Main theorem: transitive subgroup with transposition generates S_p
  let TRANSITIVE_TRANSPOSITION_GENERATES_SYMMETRIC ← prove
   r"!s (a:A) b h.
     FINITE s /\ prime(CARD s) /\
     h subgroup_of symmetric_group s /\
     (!x y. x IN s /\ y IN s ==> ?sigma. sigma IN h /\ sigma x = y) /\
     swap(a,b) IN h /\
     a IN s /\ b IN s /\ ~(a = b)
     ==> group_carrier(symmetric_group s) SUBSET h"
   (REPEAT STRIP_TAC THEN
    -- Step 1: h is finite
    SUBGOAL_THEN (← q r"FINITE(h:(A->A)->bool)") ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC (← q r"group_carrier(symmetric_group(s:A->bool))") THEN
      ASM_SIMP_TAC [FINITE_SYMMETRIC_GROUP] THEN
      ASM_MESON_TAC [SUBGROUP_OF_IMP_SUBSET],
      ALL_TAC] THEN
    -- Step 2: Set up group action of subgroup on s
    ABBREV_TAC (← q r"H:(A->A)group = subgroup_generated (symmetric_group s) h") THEN
    SUBGOAL_THEN (← q r"group_carrier(H:(A->A)group) = h") ASSUME_TAC THENL
     [EXPAND_TAC "H" THEN
      MATCH_MP_TAC CARRIER_SUBGROUP_GENERATED_SUBGROUP THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"FINITE(group_carrier(H:(A->A)group))") ASSUME_TAC THENL
     [ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"group_action (H:(A->A)group) (s:A->bool) (\f x. f x)")
      ASSUME_TAC THENL
     [EXPAND_TAC "H" THEN
      MATCH_MP_TAC GROUP_ACTION_FROM_SUBGROUP THEN
      REWRITE_TAC [SYMMETRIC_GROUP_ACTION],
      ALL_TAC] THEN
    -- Step 3: Orbit of a under H = s (by transitivity)
    SUBGOAL_THEN
      (← q r"group_orbit (H:(A->A)group) (s:A->bool) (\f x. f x) a = s")
      ASSUME_TAC THENL
     [REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ] THEN CONJ_TAC THENL
       [REWRITE_TAC [GROUP_ORBIT_SUBSET],
        REWRITE_TAC [SUBSET, IN_GROUP_ORBIT] THEN
        X_GEN_TAC (← q "y:A") THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
        FIRST_X_ASSUM (MP_TAC o SPECL [← q "a:A", ← q "y:A"]) THEN
        ASM_REWRITE_TAC [] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "sigma:A->A") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q "sigma:A->A") THEN ASM_REWRITE_TAC []],
      ALL_TAC] THEN
    -- Step 4: By orbit-stabilizer, CARD s divides CARD h
    SUBGOAL_THEN (← q r"CARD(s:A->bool) divides CARD(h:(A->A)->bool)") ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q r"H:(A->A)group", ← q "s:A->bool",
                      ← q r"\(f:A->A) (x:A). f x", ← q "a:A"]
        ORBIT_STABILIZER_MUL) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_TAC THEN
      REWRITE_TAC [divides] THEN
      EXISTS_TAC (← q r"CARD(group_stabilizer (H:(A->A)group) (\f x. f x) (a:A))") THEN
      ASM_MESON_TAC [MULT_SYM],
      ALL_TAC] THEN
    -- Step 5: By Cauchy, H has element of order CARD s
    MP_TAC (← ISPECL [← q r"H:(A->A)group", ← q r"CARD(s:A->bool)"]
      CAUCHY_GROUP_THEOREM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "sigma:A->A") STRIP_ASSUME_TAC) THEN
    -- Step 6: sigma has order CARD s in symmetric_group s
    SUBGOAL_THEN
      (← q r"group_element_order (symmetric_group (s:A->bool)) (sigma:A->A) = CARD s")
      ASSUME_TAC THENL
     [UNDISCH_TAC
        (← q r"group_element_order (H:(A->A)group) (sigma:A->A) = CARD(s:A->bool)") THEN
      EXPAND_TAC "H" THEN
      REWRITE_TAC [GROUP_ELEMENT_ORDER_SUBGROUP_GENERATED],
      ALL_TAC] THEN
    -- Step 7: sigma IN h
    SUBGOAL_THEN (← q r"(sigma:A->A) IN h") ASSUME_TAC THENL
     [ASM_MESON_TAC [], ALL_TAC] THEN
    -- Step 8: Apply TRANSPOSITION_PCYCLE_GENERATES
    MATCH_MP_TAC TRANSPOSITION_PCYCLE_GENERATES THEN
    MAP_EVERY EXISTS_TAC [← q "sigma:A->A", ← q "a:A", ← q "b:A"] THEN
    ASM_REWRITE_TAC [])

  -- @@RETURN BEGIN
  return { TRANSITIVE_TRANSPOSITION_GENERATES_SYMMETRIC }
  -- @@RETURN END

end HolLibrary.SymmetricGroup
