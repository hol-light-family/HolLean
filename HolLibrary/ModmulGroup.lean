/- ========================================================================= -/
/- The multiplicative group of integers modulo n.                            -/
/- ========================================================================= -/
/- File: HolLibrary/ModmulGroup.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/modmul_group.ml`, by hand, in file
  order, in the style of HolLibrary/GroupTheory.lean (see there and
  HolMath/Base.lean for the conventions).  modmul_group.ml begins with
  `needs "Library/grouptheory.ml"` and `needs "Library/primitive.ml"`; the
  theorems it uses from them (and from the files they need) and from the
  core library are supplied via the CoreThms structures
  (SessionLibrary.ModmulGroup fills them).  Each section is a bundle (a
  `structure`) built by a `setup` function; SessionLibrary/ModmulGroup.lean
  builds the bundles in order and exports every name under its HOL Light
  name.

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, NUMBER_RULE, TAUT) they are bound first,
  in OCaml's order.
-/

import HolLibrary.GroupTheory
import HolLibrary.Primitive

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolLibrary.ModmulGroup

-- @@COREFILL BEGIN
/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (AND_FORALL_THM ARITH CARD_CROSS CARD_SING CONG CONG_IMP_EQ CONG_LMOD
   CONG_REFL CONJ_SYM COPRIME_0 COPRIME_LMOD COPRIME_LMUL COPRIME_REFL
   COPRIME_RMUL COPRIME_SYM CYCLIC_GROUP_ELEMENT_ORDER EQ_SYM_EQ EXP EXP_ONE
   FINITE_NUMSEG FINITE_PROD_GROUP FINITE_SING FINITE_SUBSET FORALL_IN_IMAGE
   FORALL_PAIR_THM FUN_EQ_THM GROUP_ELEMENT_ORDER_UNIQUE GROUP_HOMOMORPHISM
   GROUP_ISOMORPHISM_EQ_MONOMORPHISM_FINITE HAS_SIZE INVERSE_MOD_BOUND
   INVERSE_MOD_LMUL_EQ INVERSE_MOD_RMUL_EQ IN_CROSS IN_ELIM_THM IN_NUMSEG
   IN_SING ISOMORPHIC_GROUP_SYM ISOMORPHIC_PROD_TRIVIAL_GROUP
   ISOMORPHIC_TRIVIAL_GROUPS LE_0 LE_MULT2 LE_REFL MOD_EXP_MOD MOD_LT
   MOD_LT_EQ MOD_MOD MOD_MOD_REFL MOD_MULT_MOD2 MOD_UNIQUE MULT_ASSOC
   MULT_CLAUSES MULT_EQ_0 MULT_EQ_1 MULT_SYM NOT_IMP NOT_LE ORDER_CONG
   ORDER_DIVIDES ORDER_EQ_0 PAIR_EQ PHI_1 PHI_2 PHI_ALT PHI_EQ_0
   PHI_LOWERBOUND_2 PHI_MULTIPLICATIVE PRIMITIVE_ROOT_EXISTS PROD_GROUP
   SINGLETON_GROUP : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (SUBSET TRIVIAL_GROUP_HAS_SIZE_1 TRIVIAL_IMP_CYCLIC_GROUP
   TRIVIAL_PROD_GROUP abelian_group group_carrier group_id group_inv
   group_monomorphism group_mul group_pow group_tybij inverse_mod
   isomorphic_group : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms3 where
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms4 where
  deriving Inhabited

-- @@COREFILL END

/-- What modmulgroup.ml uses from Session besides theorems. -/
structure ModmulGroupDeps where
  -- definitions and parser state
  new_definition : String → ExceptT String IO thm
  -- decision procedures and tactics
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_ARITH_TAC : tactic
  NUMBER_RULE : term → ExceptT String IO thm
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  ASM_MESON_TAC : List thm → tactic
  INDUCT_TAC : tactic
  -- (add fields here as needed, with a comment naming the HOL Light value)
  core1 : CoreThms1
  core2 : CoreThms2
  core3 : CoreThms3
  core4 : CoreThms4

/-- RingTheory's `wPart` (copied verbatim).  `W(MP_TAC o PART_MATCH f th o g
    o snd)`: match `th`'s part `f` against the part `g` of the goal, and
    MP_TAC the instance. -/
def wPart [HolBase] (g : term → Except String term) (f : term → Except String term)
    (th : thm) : tactic := fun gl =>
  ExceptT.run do
    let t ← liftExcept (g gl.2)
    ExceptT.mk (MP_TAC (← PART_MATCH f th t) gl)

/- ------------------------------------------------------------------------- -/
/- A trivial general lemma used to dispose of degnerate cases.               -/
/- ------------------------------------------------------------------------- -/

structure Gen where
  -- @@FIELDS
  MULT_EQ_2 : thm
  deriving Inhabited

@[nospecialize]
def setupGen [HolBase] (D : ModmulGroupDeps) :
    ExceptT String IO Gen := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, .. } := D
  let { ARITH, LE_MULT2, MULT_CLAUSES, .. } := D.core1
  -- @@SCOPE END

  let MULT_EQ_2 ← prove
   r"!m n. m * n = 2 <=> m = 1 /\ n = 2 \/ m = 2 /\ n = 1"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q "m = 0") THEN ASM_REWRITE_TAC [MULT_CLAUSES, ARITH] THEN
    ASM_CASES_TAC (← q "n = 0") THEN ASM_REWRITE_TAC [MULT_CLAUSES, ARITH] THEN
    ASM_CASES_TAC (← q "m = 1") THEN ASM_REWRITE_TAC [MULT_CLAUSES, ARITH] THEN
    ASM_CASES_TAC (← q "n = 1") THEN ASM_REWRITE_TAC [MULT_CLAUSES, ARITH] THEN
    MATCH_MP_TAC (← ARITH_RULE (← q r"2 * 2 <= p ==> ~(p = 2)")) THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC)

  -- @@RETURN BEGIN
  return { MULT_EQ_2 }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Multiplicative group of integers mod n, with degenerate {1} for n <= 1.   -/
/- ------------------------------------------------------------------------- -/

structure Modmul where
  -- @@FIELDS
  modmul_group : thm
  MODMUL_GROUP : thm
  FINITE_MODMUL_GROUP : thm
  ORDER_MODMUL_GROUP : thm
  HAS_SIZE_MODMUL_GROUP : thm
  ABELIAN_MODMUL_GROUP : thm
  TRIVIAL_MODMUL_GROUP : thm
  deriving Inhabited

@[nospecialize]
def setupModmul [HolBase] (D : ModmulGroupDeps) :
    ExceptT String IO Modmul := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, NUMBER_RULE,
        new_definition, .. } := D
  let { AND_FORALL_THM, ARITH, CARD_SING, CONJ_SYM, COPRIME_LMOD, COPRIME_LMUL,
        COPRIME_SYM, FINITE_NUMSEG, FINITE_SING, FINITE_SUBSET, FUN_EQ_THM, HAS_SIZE,
        INVERSE_MOD_BOUND, INVERSE_MOD_LMUL_EQ, INVERSE_MOD_RMUL_EQ, IN_ELIM_THM,
        IN_NUMSEG, LE_0, LE_REFL, MOD_LT, MOD_LT_EQ, MOD_MOD_REFL, MOD_MULT_MOD2,
        MOD_UNIQUE, MULT_ASSOC, MULT_CLAUSES, MULT_SYM, PAIR_EQ, PHI_1, PHI_2, PHI_ALT,
        PHI_LOWERBOUND_2, SINGLETON_GROUP, .. } := D.core1
  let { SUBSET, TRIVIAL_GROUP_HAS_SIZE_1, abelian_group, group_carrier, group_id,
        group_inv, group_mul, group_tybij, inverse_mod, .. } := D.core2
  -- @@SCOPE END

  let modmul_group ← new_definition
   r"modmul_group n =
          if n <= 1 then singleton_group 1
          else group({m | m < n /\ coprime(m,n)},
                     1,inverse_mod n,(\a b. (a * b) MOD n))"

  let MODMUL_GROUP ← prove
   r"(!n. group_carrier(modmul_group n) =
          if n <= 1 then {1} else {m | m < n /\ coprime(m,n)}) /\
     (!n. group_id(modmul_group n) = 1) /\
     (!n. group_inv(modmul_group n) = inverse_mod n) /\
     (!n. group_mul(modmul_group n) =
          if n <= 1 then (\a b. 1) else (\a b. (a * b) MOD n))"
   (← do
    let n6 ← ARITH_RULE (← q r"2 <= n ==> 1 < n")
    let n5 ← ARITH_RULE (← q r"2 <= n ==> ~(n = 0)")
    let n4 ← NUMBER_RULE (← q r"!m. (a * m == 1) (mod n) ==> coprime(a,n)")
    let n3 ← NUMBER_RULE (← q r"coprime(1,n)")
    let n2 ← ARITH_RULE (← q r"1 < n <=> 2 <= n")
    let n1 ← ARITH_RULE (← q r"~(n <= 1) <=> 2 <= n")
    pure (REWRITE_TAC [AND_FORALL_THM] THEN X_GEN_TAC (← q "n:num") THEN
    REWRITE_TAC [modmul_group] THEN
    ASM_CASES_TAC (← q "n <= 1") THEN ASM_REWRITE_TAC [] THENL
     [REWRITE_TAC [SINGLETON_GROUP] THEN ASM_REWRITE_TAC [FUN_EQ_THM, inverse_mod],
      RULE_ASSUM_TAC (REWRITE_RULE [n1])] THEN
    REWRITE_TAC [group_carrier, group_id, group_inv, group_mul] THEN
    REWRITE_TAC [← GSYM PAIR_EQ, ← GSYM (← CONJUNCT2 group_tybij)] THEN
    ASM_REWRITE_TAC [IN_ELIM_THM, n2] THEN
    REWRITE_TAC [n3, PAIR_EQ] THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC (← q "m:num") THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [INVERSE_MOD_BOUND] THEN
      MATCH_MP_TAC n4 THEN
      EXISTS_TAC (← q "m:num") THEN REWRITE_TAC [INVERSE_MOD_LMUL_EQ] THEN
      ASM_MESON_TAC [COPRIME_SYM],
      REWRITE_TAC [COPRIME_LMOD, COPRIME_LMUL] THEN
      ASM_SIMP_TAC [MOD_LT_EQ, n5],
      REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM MOD_MULT_MOD2] THEN
      REWRITE_TAC [MOD_MOD_REFL] THEN REWRITE_TAC [MOD_MULT_MOD2] THEN
      REWRITE_TAC [MULT_ASSOC],
      SIMP_TAC [MULT_CLAUSES, MOD_LT],
      REWRITE_TAC [MOD_UNIQUE, INVERSE_MOD_RMUL_EQ, INVERSE_MOD_LMUL_EQ] THEN
      ASM_SIMP_TAC [n6] THEN
      MESON_TAC [COPRIME_SYM]]))

  let FINITE_MODMUL_GROUP ← prove
   r"!n. FINITE(group_carrier(modmul_group n))"
   (GEN_TAC THEN REWRITE_TAC [MODMUL_GROUP] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [FINITE_SING] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q "0..n") THEN
    REWRITE_TAC [FINITE_NUMSEG, SUBSET, IN_ELIM_THM, IN_NUMSEG] THEN
    ARITH_TAC)

  let ORDER_MODMUL_GROUP ← prove
   r"!n. CARD(group_carrier(modmul_group n)) =
         if n = 0 then 1 else phi n"
   (GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [MODMUL_GROUP, LE_0, CARD_SING] THEN
    ASM_CASES_TAC (← q "n = 1") THEN ASM_REWRITE_TAC [LE_REFL, PHI_1, CARD_SING] THEN
    ASM_REWRITE_TAC [← ARITH_RULE (← q r"n <= 1 <=> n = 0 \/ n = 1")] THEN
    ONCE_REWRITE_TAC [CONJ_SYM] THEN REWRITE_TAC [PHI_ALT])

  let HAS_SIZE_MODMUL_GROUP ← prove
   r"!n. ~(n = 0) ==> group_carrier(modmul_group n) HAS_SIZE phi n"
   (SIMP_TAC [HAS_SIZE, FINITE_MODMUL_GROUP] THEN
    SIMP_TAC [ORDER_MODMUL_GROUP])

  let ABELIAN_MODMUL_GROUP ← prove
   r"!n. abelian_group(modmul_group n)"
   (GEN_TAC THEN REWRITE_TAC [abelian_group, MODMUL_GROUP] THEN
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [MULT_SYM])

  let TRIVIAL_MODMUL_GROUP ← prove
   r"!n. trivial_group(modmul_group n) <=> n <= 2"
   (GEN_TAC THEN REWRITE_TAC [TRIVIAL_GROUP_HAS_SIZE_1, HAS_SIZE] THEN
    REWRITE_TAC [FINITE_MODMUL_GROUP] THEN
    REWRITE_TAC [ORDER_MODMUL_GROUP] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [ARITH] THEN
    ASM_CASES_TAC (← q "n = 1") THEN ASM_REWRITE_TAC [PHI_1, ARITH] THEN
    ASM_CASES_TAC (← q "n = 2") THEN ASM_REWRITE_TAC [PHI_2, ARITH] THEN
    MATCH_MP_TAC (← ARITH_RULE
      (← q r"~(n <= 2) /\ 2 <= p ==> (p = 1 <=> n <= 2)")) THEN
    CONJ_TAC THENL [ALL_TAC, MATCH_MP_TAC PHI_LOWERBOUND_2] THEN
    ASM_ARITH_TAC)

  -- @@RETURN BEGIN
  return { modmul_group, MODMUL_GROUP, FINITE_MODMUL_GROUP, ORDER_MODMUL_GROUP,
           HAS_SIZE_MODMUL_GROUP, ABELIAN_MODMUL_GROUP, TRIVIAL_MODMUL_GROUP }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Chinese remainder theorem in group-theoretic language.                    -/
/- ------------------------------------------------------------------------- -/

structure Crt where
  -- @@FIELDS
  GROUP_HOMOMORPHISM_PROD_MODMUL_GROUP : thm
  GROUP_ISOMORPHISM_PROD_MODMUL_GROUP : thm
  ISOMORPHIC_GROUP_MODMUL_GROUP : thm
  GROUP_POW_MODMUL_GROUP : thm
  GROUP_ELEMENT_ORDER_MODMUL_GROUP : thm
  deriving Inhabited

@[nospecialize]
def setupCrt [HolBase] (D : ModmulGroupDeps) (BGen : Gen) (BModmul : Modmul) :
    ExceptT String IO Crt := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON, MESON_TAC,
        NUMBER_RULE, .. } := D
  let { ARITH, CARD_CROSS, CONG, CONG_IMP_EQ, COPRIME_0, COPRIME_LMOD, COPRIME_REFL,
        COPRIME_RMUL, EXP, EXP_ONE, FINITE_PROD_GROUP, FORALL_IN_IMAGE,
        FORALL_PAIR_THM, GROUP_ELEMENT_ORDER_UNIQUE, GROUP_HOMOMORPHISM,
        GROUP_ISOMORPHISM_EQ_MONOMORPHISM_FINITE, IN_CROSS, IN_ELIM_THM, IN_SING,
        ISOMORPHIC_GROUP_SYM, ISOMORPHIC_PROD_TRIVIAL_GROUP, ISOMORPHIC_TRIVIAL_GROUPS,
        MOD_EXP_MOD, MOD_LT, MOD_LT_EQ, MOD_MOD, MOD_MOD_REFL, MOD_MULT_MOD2,
        MULT_CLAUSES, MULT_EQ_0, MULT_EQ_1, MULT_SYM, NOT_LE, ORDER_DIVIDES, PAIR_EQ,
        PHI_MULTIPLICATIVE, PROD_GROUP, .. } := D.core1
  let { SUBSET, TRIVIAL_PROD_GROUP, group_monomorphism, group_pow, isomorphic_group, .. } := D.core2
  let { MULT_EQ_2, .. } := BGen
  let { FINITE_MODMUL_GROUP, MODMUL_GROUP, ORDER_MODMUL_GROUP, TRIVIAL_MODMUL_GROUP, .. } := BModmul
  -- @@SCOPE END

  let GROUP_HOMOMORPHISM_PROD_MODMUL_GROUP ← prove
   r"!m n. 2 <= m /\ 2 <= n
           ==> group_homomorphism (modmul_group(m * n),
                                   prod_group (modmul_group m)
                                              (modmul_group n))
                                  (\a. (a MOD m),(a MOD n))"
   (← do
    let a2 ← ARITH_RULE (← q r"2 <= n ==> ~(n = 0) /\ ~(n = 1)")
    let a1 ← ARITH_RULE (← q r"n <= 1 <=> n = 0 \/ n = 1")
    pure (REPEAT STRIP_TAC THEN
    REWRITE_TAC [GROUP_HOMOMORPHISM, PROD_GROUP, SUBSET] THEN
    REWRITE_TAC [FORALL_IN_IMAGE, FORALL_PAIR_THM, IN_CROSS] THEN
    REWRITE_TAC [MODMUL_GROUP] THEN
    REWRITE_TAC [a1] THEN
    ASM_SIMP_TAC [MULT_EQ_0, MULT_EQ_1, IN_ELIM_THM, MOD_LT_EQ, COPRIME_LMOD,
                 PAIR_EQ, a2] THEN
    SIMP_TAC [COPRIME_RMUL, MOD_MOD, ← ONCE_REWRITE_RULE [MULT_SYM] MOD_MOD] THEN
    REWRITE_TAC [MOD_MULT_MOD2]))

  let GROUP_ISOMORPHISM_PROD_MODMUL_GROUP ← prove
   r"!m n. 2 <= m /\ 2 <= n /\ coprime(m,n)
           ==> group_isomorphism (modmul_group(m * n),
                                  prod_group (modmul_group m)
                                             (modmul_group n))
                                 (\a. (a MOD m),(a MOD n))"
   (← do
    let n4 ← NUMBER_RULE
      (← q r"coprime(m:num,n) /\ (x == y) (mod m) /\ (x == y) (mod n)
      ==> (x == y) (mod(m * n))")
    let a3 ← ARITH_RULE (← q r"2 <= n ==> ~(n = 0) /\ ~(n = 1)")
    let a2 ← ARITH_RULE (← q r"n <= 1 <=> n = 0 \/ n = 1")
    let a1 ← ARITH_RULE (← q r"2 <= n ==> ~(n = 0)")
    pure (REPEAT STRIP_TAC THEN
    wPart (fun t => pure t) (fun t => do lhand (← rand t))
      GROUP_ISOMORPHISM_EQ_MONOMORPHISM_FINITE THEN
    ASM_SIMP_TAC [ORDER_MODMUL_GROUP, FINITE_PROD_GROUP,
                 FINITE_MODMUL_GROUP, MULT_EQ_0,
                 ← CONJUNCT1 PROD_GROUP, CARD_CROSS, PHI_MULTIPLICATIVE,
                 a1] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [group_monomorphism] THEN
    ASM_SIMP_TAC [GROUP_HOMOMORPHISM_PROD_MODMUL_GROUP] THEN
    ASM_SIMP_TAC [MODMUL_GROUP, MULT_EQ_0, MULT_EQ_1, a2, a3] THEN
    REWRITE_TAC [PAIR_EQ, IN_ELIM_THM, ← GSYM CONG] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CONG_IMP_EQ THEN
    EXISTS_TAC (← q "m * n:num") THEN ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [n4]))

  let ISOMORPHIC_GROUP_MODMUL_GROUP ← prove
   r"!m n. coprime(m,n)
           ==> prod_group (modmul_group m)
                          (modmul_group n)
               isomorphic_group (modmul_group (m * n))"
   (← do
    let a2 ← ARITH_RULE (← q r"n <= 2 <=> n = 0 \/ n = 1 \/ n = 2")
    let m1 ← MESON [ISOMORPHIC_TRIVIAL_GROUPS]
      (← q r"(trivial_group G <=> trivial_group H) /\
      (~trivial_group G /\ ~trivial_group H ==> G isomorphic_group H)
      ==> G isomorphic_group H")
    pure (REPEAT STRIP_TAC THEN MATCH_MP_TAC m1 THEN
    REWRITE_TAC [TRIVIAL_PROD_GROUP, TRIVIAL_MODMUL_GROUP] THEN
    POP_ASSUM MP_TAC THEN
    ASM_CASES_TAC (← q "m = 0") THEN ASM_SIMP_TAC [COPRIME_0, ARITH] THEN
    ASM_CASES_TAC (← q "n = 0") THEN ASM_SIMP_TAC [COPRIME_0, ARITH] THEN
    DISCH_TAC THEN
    ASM_CASES_TAC (← q "m = 1") THEN
    ASM_SIMP_TAC [MULT_CLAUSES, ISOMORPHIC_PROD_TRIVIAL_GROUP,
                TRIVIAL_MODMUL_GROUP, ARITH] THEN
    ASM_CASES_TAC (← q "n = 1") THEN
    ASM_SIMP_TAC [MULT_CLAUSES, ISOMORPHIC_PROD_TRIVIAL_GROUP,
                 TRIVIAL_MODMUL_GROUP, ARITH] THEN
    ASM_REWRITE_TAC [a2] THEN
    ASM_REWRITE_TAC [MULT_EQ_0, MULT_EQ_1, MULT_EQ_2] THEN
    CONJ_TAC THENL [ASM_MESON_TAC [COPRIME_REFL], DISCH_THEN (K ALL_TAC)] THEN
    ONCE_REWRITE_TAC [ISOMORPHIC_GROUP_SYM] THEN
    REWRITE_TAC [isomorphic_group] THEN
    EXISTS_TAC (← q r"\a. (a MOD m),(a MOD n)") THEN
    MATCH_MP_TAC GROUP_ISOMORPHISM_PROD_MODMUL_GROUP THEN
    ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC))

  let GROUP_POW_MODMUL_GROUP ← prove
   r"!n a k. group_pow (modmul_group n) a k =
             if n <= 1 then 1 else (a EXP k) MOD n"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [group_pow, MODMUL_GROUP] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [EXP] THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC,
      MESON_TAC [MOD_MULT_MOD2, MOD_MOD_REFL, MOD_EXP_MOD]])

  let GROUP_ELEMENT_ORDER_MODMUL_GROUP ← prove
   r"!n a. a IN group_carrier(modmul_group n)
           ==> group_element_order (modmul_group n) a = order n a"
   (REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [GROUP_ELEMENT_ORDER_UNIQUE] THEN
    REWRITE_TAC [← GSYM ORDER_DIVIDES] THEN
    X_GEN_TAC (← q "k:num") THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC [GROUP_POW_MODMUL_GROUP] THEN
    REWRITE_TAC [MODMUL_GROUP] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [IN_SING, EXP_ONE, CONG] THEN
    DISCH_THEN (K ALL_TAC) THEN RULE_ASSUM_TAC (REWRITE_RULE [NOT_LE]) THEN
    ASM_SIMP_TAC [MOD_LT])

  -- @@RETURN BEGIN
  return { GROUP_HOMOMORPHISM_PROD_MODMUL_GROUP, GROUP_ISOMORPHISM_PROD_MODMUL_GROUP,
           ISOMORPHIC_GROUP_MODMUL_GROUP, GROUP_POW_MODMUL_GROUP,
           GROUP_ELEMENT_ORDER_MODMUL_GROUP }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Existence of primitive roots in group-theoretic language.                 -/
/- ------------------------------------------------------------------------- -/

structure Primroot where
  -- @@FIELDS
  CYCLIC_MODMUL_GROUP : thm
  deriving Inhabited

@[nospecialize]
def setupPrimroot [HolBase] (D : ModmulGroupDeps) (BModmul : Modmul) (BCrt : Crt) :
    ExceptT String IO Primroot := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, MESON_TAC, .. } := D
  let { CONG_LMOD, CONG_REFL, COPRIME_SYM, CYCLIC_GROUP_ELEMENT_ORDER, EQ_SYM_EQ,
        IN_ELIM_THM, MOD_LT_EQ, NOT_IMP, NOT_LE, ORDER_CONG, ORDER_EQ_0, PHI_EQ_0,
        PRIMITIVE_ROOT_EXISTS, .. } := D.core1
  let { TRIVIAL_IMP_CYCLIC_GROUP, .. } := D.core2
  let { FINITE_MODMUL_GROUP, MODMUL_GROUP, ORDER_MODMUL_GROUP, TRIVIAL_MODMUL_GROUP, .. } := BModmul
  let { GROUP_ELEMENT_ORDER_MODMUL_GROUP, .. } := BCrt
  -- @@SCOPE END

  let CYCLIC_MODMUL_GROUP ← prove
   r"!n. cyclic_group(modmul_group n) <=>
         n = 0 \/ n = 1 \/ n = 2 \/ n = 4 \/
         ?p k. prime p /\ 3 <= p /\ (n = p EXP k \/ n = 2 * p EXP k)"
   (← do
    let c5 ← ARITH_RULE (← q r"2 < n ==> ~(n = 0)")
    let c4 ← TAUT (← q r"(~p ==> ~q) /\ q ==> p /\ q")
    let c3 ← ARITH_RULE (← q r"2 < n ==> ~(n = 0)")
    let c2 ← ARITH_RULE
      (← q r"2 < n ==> ~(n = 0) /\ ~(n = 1) /\ ~(n <= 1)")
    let c1 ← TAUT (← q r"p /\ q <=> ~(p ==> ~q)")
    pure (GEN_TAC THEN ASM_CASES_TAC (← q "n <= 2") THENL
     [ASM_SIMP_TAC [TRIVIAL_MODMUL_GROUP,
                   TRIVIAL_IMP_CYCLIC_GROUP] THEN
      ASM_ARITH_TAC,
      RULE_ASSUM_TAC (REWRITE_RULE [NOT_LE])] THEN
    SIMP_TAC [CYCLIC_GROUP_ELEMENT_ORDER, FINITE_MODMUL_GROUP] THEN
    ONCE_REWRITE_TAC [c1] THEN
    SIMP_TAC [GROUP_ELEMENT_ORDER_MODMUL_GROUP] THEN
    MP_TAC (← SPEC (← q "n:num") PRIMITIVE_ROOT_EXISTS) THEN
    ASM_SIMP_TAC [ORDER_MODMUL_GROUP, FINITE_MODMUL_GROUP,
                 MODMUL_GROUP, c2] THEN
    REWRITE_TAC [IN_ELIM_THM, NOT_IMP] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    EQ_TAC THENL [MESON_TAC [], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "k:num") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q "k MOD n") THEN
    ASM_SIMP_TAC [MOD_LT_EQ, c3] THEN
    MATCH_MP_TAC c4 THEN
    ONCE_REWRITE_TAC [COPRIME_SYM] THEN SIMP_TAC [← GSYM ORDER_EQ_0] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    ASM_SIMP_TAC [PHI_EQ_0, c5] THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN MATCH_MP_TAC ORDER_CONG THEN
    REWRITE_TAC [CONG_LMOD, CONG_REFL]))

  -- @@RETURN BEGIN
  return { CYCLIC_MODMUL_GROUP }
  -- @@RETURN END

end HolLibrary.ModmulGroup
