/- ========================================================================= -/
/- ANT: Finite generation of groups                                        -/
/- ========================================================================= -/
/- File: HolANT/FingenGroup.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/fingen_group.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antfingengroupdiff; the rest is by hand.  Its `needs` closure is
  Library/products.ml, Library/frag.ml, Library/wo.ml, Library/card.ml, Library/prime.ml, Library/grouptheory.ml, Library/binomial.ml, Library/iter.ml, Library/pocklington.ml, Library/ringtheory.ml, Library/ring_groups.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.FingenGroup fills them).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left; where a proof applies rules that print or use
  counters (MESON, ARITH_RULE, ...) they are bound first, in OCaml's order.
-/

import HolANT.Prelude
import HolLibrary.Products
import HolLibrary.Frag
import HolLibrary.Wo
import HolLibrary.Card
import HolLibrary.Prime
import HolLibrary.GroupTheory
import HolLibrary.Binomial
import HolLibrary.Iter
import HolLibrary.Pocklington
import HolLibrary.RingTheory
import HolLibrary.RingGroups

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude

namespace HolANT.FingenGroup

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ABELIAN_GROUP_MUL_POW ABELIAN_GROUP_SUM_CLAUSES ABELIAN_GROUP_SUM_INV
   ABELIAN_GROUP_SUM_MUL ABELIAN_GROUP_SUM_POW ADD1 ADD_EQ_0 ARITH ARITH_EQ
   CARD_CLAUSES CARD_IMAGE_INJ CARD_IMAGE_LE CARD_NUMSEG CARD_SUBSET
   CARD_UNIONS_LE CARRIER_SUBGROUP_GENERATED_SUBGROUP CONJ_ASSOC CONTRAPOS_THM
   DIVISION EMPTY_SUBSET EQ_IMP_LE EQ_TRANS EXP EXP_EQ_0 EXP_MONO_LE_IMP
   FINITELY_GENERATED_ABELIAN_GROUP_EXPONENTS
   FINITELY_GENERATED_ABELIAN_GROUP_POW FINITELY_GENERATED_GROUP
   FINITE_CARTESIAN_PRODUCT FINITE_CYCLIC_SUBGROUP_ORDER FINITE_EMPTY
   FINITE_FUNSPACE FINITE_IMAGE FINITE_INDUCT_STRONG FINITE_INSERT
   FINITE_INT_SEG FINITE_NUMSEG FINITE_NUMSEG_LT FINITE_PRODUCT_DEPENDENT
   FINITE_RESTRICT FINITE_SUBSET FINITE_SUBSET_IMAGE FINITE_UNION FINITE_UNIONS
   FORALL_INT_CASES FORALL_IN_GSPEC FORALL_IN_IMAGE FORALL_IN_INSERT FUN_EQ_THM
   GROUP_HOMOMORPHISM_PREIMAGE_IMAGE GROUP_ID GROUP_INV GROUP_INV_INV
   GROUP_KERNEL_SUBSET_CARRIER GROUP_LINV_UNIQUE GROUP_MUL GROUP_MUL_ASSOC
   GROUP_MUL_LID GROUP_MUL_LINV GROUP_MUL_RID GROUP_MUL_RINV GROUP_NPOW
   GROUP_POW GROUP_POW_ADD GROUP_POW_POW GROUP_REAL_MULTIPLICATIVE_ID_INV_POW
   GROUP_RINV_UNIQUE GROUP_SUM GROUP_SUM_CLAUSES_EXISTS GROUP_SUM_EQ
   GROUP_SUM_RESTRICT_SET GROUP_ZPOW GROUP_ZPOW_0 GROUP_ZPOW_ADD
   GROUP_ZPOW_EQ_ID GROUP_ZPOW_MUL GROUP_ZPOW_NEG GROUP_ZPOW_SUB HAS_SIZE
   HAS_SIZE_FUNSPACE IMP_CONJ INSERT_SUBSET INT_ABS_NUM INT_DIVISION INT_IMAGE
   INT_LE_NEG2 INT_LT_IMP_LE INT_NEG_EQ_0 INT_OF_NUM_EQ INT_OF_NUM_LE
   INT_OF_NUM_OF_INT INT_SUB_0 IN_ELIM_THM IN_IMAGE IN_INSERT IN_NUMSEG IN_SING
   IN_SUBGROUP_INV IN_SUBGROUP_MUL : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (IN_SUBGROUP_SUM IN_SUBGROUP_ZPOW IN_UNION LEFT_AND_EXISTS_THM
   LEFT_IMP_EXISTS_THM LET_TRANS LE_0 LE_ADD LE_ADDR LE_EXP LE_MULT_LCANCEL
   LE_TRANS LTE_TRANS LT_IMP_LE LT_MULT_RCANCEL LT_POW2_REFL MEMBER_NOT_EMPTY
   MOD_LT_EQ MONO_EXISTS MONO_FORALL MULT_2 MULT_ASSOC MULT_CLAUSES MULT_EXP
   NOT_EXISTS_THM NOT_FORALL_THM NOT_IMP NOT_IN_EMPTY NOT_LE NOT_LT
   REAL_ARCH_POW2 REAL_ARCH_SIMPLE REAL_INV_1 REAL_INV_1_LT REAL_INV_INV
   REAL_INV_LE_1 REAL_INV_MUL REAL_LET_TRANS REAL_LE_INV2 REAL_LE_INV_EQ
   REAL_LE_LDIV_EQ REAL_LE_LMUL REAL_LE_MUL2 REAL_LE_RDIV_EQ REAL_LE_REFL
   REAL_LE_TRANS REAL_LTE_TRANS REAL_LT_IMP_LE REAL_LT_IMP_NZ REAL_LT_INV_EQ
   REAL_LT_LMUL_EQ REAL_LT_MUL REAL_LT_POW2 REAL_MAX_LE REAL_MUL_RINV
   REAL_OF_NUM_EQ REAL_OF_NUM_LE REAL_OF_NUM_LT REAL_OF_NUM_POW REAL_POS
   REAL_POW_ADD REAL_POW_INV REAL_POW_LE REAL_POW_LE2 REAL_POW_LE2_REV
   REAL_POW_LT REAL_POW_MONO REAL_POW_MONO_INV REAL_POW_POW REAL_ZPOW_ADD
   REAL_ZPOW_LT REAL_ZPOW_NEG REAL_ZPOW_NUM RESTRICTION
   RESTRICTION_IN_CARTESIAN_PRODUCT RIGHT_EXISTS_IMP_THM SIMPLE_IMAGE SKOLEM_THM
   SUBGROUP_GENERATED_BY_HOMOMORPHIC_IMAGE SUBGROUP_GENERATED_IDEMPOT_GEN
   SUBGROUP_GENERATED_INC_GEN SUBGROUP_GENERATED_MONO
   SUBGROUP_GENERATED_SUPERSET SUBGROUP_GROUP_IMAGE SUBGROUP_GROUP_KERNEL
   SUBGROUP_OF_TORSION SUBGROUP_SUBGROUP_GENERATED SUBSET SUBSET_RESTRICT
   SUBSET_TRANS SUBSET_UNION UNIONS_IMAGE UNION_SUBSET group_div group_image
   num_MAX num_WOP real_div real_pow : thm)
  deriving Inhabited

/-- What fingen_group.ml uses from Session besides theorems. -/
structure FingenGroupDeps where
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
/- fingen_group.ml phrases from line 55 to 479                            -/
/- ---------------------------------------------------------------------- -/

structure FingenGroup01 where
  -- @@FIELDS
  FINITELY_GENERATED_GROUP_EXTENSION : thm
  FINITELY_GENERATED_ABELIAN_GROUP_MOD_POW : thm
  GROUP_SUM_POW_REAL_MULTIPLICATIVE_BOUND : thm
  GROUP_REAL_MULTIPLICATIVE_BOX_COUNT : thm
  ABELIAN_GROUP_DISCRETE_DEPENDENT : thm
  FINITELY_GENERATED_ABELIAN_GROUP_DISCRETE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFingenGroup01 [HolBase] (D : FingenGroupDeps) :
    ExceptT String IO FingenGroup01 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC,
        INT_ARITH_TAC, MESON, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, SET_RULE, SET_TAC,
        TAUT, .. } := D
  let { ABELIAN_GROUP_MUL_POW, ABELIAN_GROUP_SUM_CLAUSES, ABELIAN_GROUP_SUM_INV,
        ABELIAN_GROUP_SUM_MUL, ABELIAN_GROUP_SUM_POW, ADD1, ADD_EQ_0, ARITH, ARITH_EQ,
        CARD_CLAUSES, CARD_IMAGE_INJ, CARD_IMAGE_LE, CARD_NUMSEG, CARD_SUBSET,
        CARD_UNIONS_LE, CARRIER_SUBGROUP_GENERATED_SUBGROUP, CONJ_ASSOC, DIVISION,
        EMPTY_SUBSET, EQ_IMP_LE, EQ_TRANS, EXP, EXP_EQ_0, EXP_MONO_LE_IMP,
        FINITELY_GENERATED_ABELIAN_GROUP_POW, FINITELY_GENERATED_GROUP, FINITE_EMPTY,
        FINITE_FUNSPACE, FINITE_IMAGE, FINITE_INDUCT_STRONG, FINITE_INSERT,
        FINITE_NUMSEG, FINITE_NUMSEG_LT, FINITE_PRODUCT_DEPENDENT, FINITE_RESTRICT,
        FINITE_SUBSET, FINITE_SUBSET_IMAGE, FINITE_UNION, FINITE_UNIONS,
        FORALL_IN_GSPEC, FORALL_IN_IMAGE, FORALL_IN_INSERT, FUN_EQ_THM,
        GROUP_HOMOMORPHISM_PREIMAGE_IMAGE, GROUP_INV, GROUP_INV_INV,
        GROUP_KERNEL_SUBSET_CARRIER, GROUP_LINV_UNIQUE, GROUP_MUL, GROUP_MUL_ASSOC,
        GROUP_MUL_LID, GROUP_MUL_LINV, GROUP_MUL_RID, GROUP_MUL_RINV, GROUP_NPOW,
        GROUP_POW, GROUP_POW_ADD, GROUP_POW_POW, GROUP_REAL_MULTIPLICATIVE_ID_INV_POW,
        GROUP_RINV_UNIQUE, GROUP_SUM, GROUP_SUM_CLAUSES_EXISTS, GROUP_SUM_EQ,
        GROUP_ZPOW, GROUP_ZPOW_0, GROUP_ZPOW_ADD, GROUP_ZPOW_MUL, GROUP_ZPOW_NEG,
        GROUP_ZPOW_SUB, HAS_SIZE, HAS_SIZE_FUNSPACE, IMP_CONJ, INSERT_SUBSET,
        INT_ABS_NUM, INT_DIVISION, INT_IMAGE, INT_LT_IMP_LE, INT_NEG_EQ_0,
        INT_OF_NUM_EQ, INT_OF_NUM_LE, INT_OF_NUM_OF_INT, INT_SUB_0, IN_ELIM_THM,
        IN_IMAGE, IN_INSERT, IN_NUMSEG, IN_SUBGROUP_INV, IN_SUBGROUP_MUL, .. } := D.core1
  let { IN_SUBGROUP_SUM, IN_SUBGROUP_ZPOW, IN_UNION, LEFT_AND_EXISTS_THM,
        LEFT_IMP_EXISTS_THM, LET_TRANS, LE_0, LE_ADD, LE_ADDR, LE_EXP, LE_MULT_LCANCEL,
        LE_TRANS, LTE_TRANS, LT_MULT_RCANCEL, MEMBER_NOT_EMPTY, MOD_LT_EQ, MONO_EXISTS,
        MULT_2, MULT_ASSOC, MULT_CLAUSES, MULT_EXP, NOT_EXISTS_THM, NOT_FORALL_THM,
        NOT_IN_EMPTY, NOT_LT, REAL_ARCH_POW2, REAL_INV_1, REAL_INV_1_LT, REAL_INV_INV,
        REAL_INV_LE_1, REAL_INV_MUL, REAL_LET_TRANS, REAL_LE_INV2, REAL_LE_INV_EQ,
        REAL_LE_LDIV_EQ, REAL_LE_LMUL, REAL_LE_MUL2, REAL_LE_RDIV_EQ, REAL_LE_REFL,
        REAL_LE_TRANS, REAL_LT_IMP_LE, REAL_LT_IMP_NZ, REAL_LT_INV_EQ, REAL_LT_LMUL_EQ,
        REAL_LT_MUL, REAL_MAX_LE, REAL_MUL_RINV, REAL_OF_NUM_LE, REAL_OF_NUM_LT,
        REAL_POS, REAL_POW_ADD, REAL_POW_INV, REAL_POW_LE, REAL_POW_LE2,
        REAL_POW_LE2_REV, REAL_POW_LT, REAL_POW_MONO, REAL_POW_MONO_INV, REAL_POW_POW,
        RIGHT_EXISTS_IMP_THM, SIMPLE_IMAGE, SKOLEM_THM,
        SUBGROUP_GENERATED_BY_HOMOMORPHIC_IMAGE, SUBGROUP_GENERATED_IDEMPOT_GEN,
        SUBGROUP_GENERATED_INC_GEN, SUBGROUP_GENERATED_MONO,
        SUBGROUP_GENERATED_SUPERSET, SUBGROUP_GROUP_IMAGE, SUBGROUP_GROUP_KERNEL,
        SUBGROUP_SUBGROUP_GENERATED, SUBSET, SUBSET_RESTRICT, SUBSET_TRANS,
        SUBSET_UNION, UNIONS_IMAGE, UNION_SUBSET, group_div, group_image, num_MAX,
        num_WOP, real_div, real_pow, .. } := D.core2
  -- @@SCOPE END

  let FINITELY_GENERATED_GROUP_EXTENSION ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let p1 ← prove r"!G h:A->bool.
        h subgroup_of G /\ finitely_generated_group(subgroup_generated G h)
        ==> ?s. FINITE s /\ s SUBSET h /\
                group_carrier(subgroup_generated G s) = h" (REWRITE_TAC [FINITELY_GENERATED_GROUP] THEN MESON_TAC [SUBGROUP_GENERATED_IDEMPOT_GEN, CARRIER_SUBGROUP_GENERATED_SUBGROUP])
    let lemma := p1
    let q2 ← q r"IMAGE (f:A->B) (group_carrier(subgroup_generated G u)) =
    IMAGE f (group_carrier G)"
    let q3 ← q r"s UNION u:A->bool"
    let q4 ← q r"u:A->bool"
    let q5 ← q r"G:A group"
    let v6 ← ISPECL [q5, q4, q3] SUBGROUP_GENERATED_MONO
    let q7 ← q r"s UNION u:A->bool"
    let q8 ← q r"s:A->bool"
    let q9 ← q r"G:A group"
    let v10 ← ISPECL [q9, q8, q7] SUBGROUP_GENERATED_MONO
    let q11 ← q r"group_carrier(subgroup_generated G (s UNION u:A->bool))"
    let q12 ← q r"f:A->B"
    let q13 ← q r"H:B group"
    let q14 ← q r"G:A group"
    let v15 ← ISPECL [q14, q13, q12, q11] GROUP_HOMOMORPHISM_PREIMAGE_IMAGE
    let q16 ← q r"s UNION u:A->bool"
    let q17 ← q r"u:A->bool"
    let q18 ← q r"t:B->bool"
    let q19 ← q r"s:A->bool"
    let q20 ← q r"group_kernel(G,H) (f:A->B)"
    let q21 ← q r"G:A group"
    let v22 ← ISPECL [q21, q20] lemma
    let q23 ← q r"group_image(G,H) (f:A->B)"
    let q24 ← q r"H:B group"
    let v25 ← ISPECL [q24, q23] lemma
    prove
      r"!G H (f:A->B).
          group_homomorphism(G,H) f /\
          finitely_generated_group(subgroup_generated G (group_kernel(G,H) f)) /\
          finitely_generated_group(subgroup_generated H (group_image(G,H) f))
          ==> finitely_generated_group G"
      (REPEAT STRIP_TAC THEN MP_TAC v25 THEN MP_TAC v22 THEN ASM_SIMP_TAC [SUBGROUP_GROUP_KERNEL, SUBGROUP_GROUP_IMAGE] THEN DISCH_THEN (X_CHOOSE_THEN q19 STRIP_ASSUME_TAC) THEN REWRITE_TAC [group_image, CONJ_ASSOC, FINITE_SUBSET_IMAGE] THEN REWRITE_TAC [LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [q18, q17] THEN DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN ASM_SIMP_TAC [SUBGROUP_GENERATED_BY_HOMOMORPHIC_IMAGE] THEN DISCH_TAC THEN REWRITE_TAC [FINITELY_GENERATED_GROUP] THEN EXISTS_TAC q16 THEN ASM_REWRITE_TAC [FINITE_UNION, UNION_SUBSET, SUBGROUP_GENERATED_SUPERSET] THEN CONJ_TAC THENL [ASM_MESON_TAC [GROUP_KERNEL_SUBSET_CARRIER, SUBSET_TRANS], ALL_TAC] THEN MP_TAC v15 THEN MP_TAC v10 THEN MP_TAC v6 THEN ASM_REWRITE_TAC [SUBGROUP_SUBGROUP_GENERATED, SUBSET_UNION] THEN UNDISCH_TAC q2 THEN SET_TAC [])

  let FINITELY_GENERATED_ABELIAN_GROUP_MOD_POW ← prove
    r"!G:A group m.
        abelian_group G /\ finitely_generated_group G /\ ~(m = 0)
        ==> ?s. FINITE s /\ s SUBSET group_carrier G /\
                !x. x IN group_carrier G
                    ==> ?a y. a IN s /\ y IN group_carrier G /\
                              x = group_mul G a (group_pow G y m)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"G:A group") FINITELY_GENERATED_ABELIAN_GROUP_POW) THEN ASM_REWRITE_TAC [SUBSET] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"t:A->bool") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"IMAGE (\r. group_sum G t (\y. group_pow G y (r y)))
                    {r | (!y:A. y IN t ==> r y IN {i | i < m}) /\
                         (!y. ~(y IN t) ==> r y = 0)}") THEN ASM_SIMP_TAC [FINITE_IMAGE, FINITE_FUNSPACE, FINITE_NUMSEG_LT] THEN REWRITE_TAC [FORALL_IN_IMAGE, GROUP_SUM] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_THEN (fun th => tactic_of do pure (FIRST_X_ASSUM ((X_CHOOSE_THEN (← q r"n:A->num") SUBST1_TAC) o (← do let c := th; pure (fun th => MATCH_MP th c))))) THEN MAP_EVERY EXISTS_TAC [(← q r"group_sum G t (\y:A. group_pow G y (n y MOD m))"), (← q r"group_sum G t (\y:A. group_pow G y (n y DIV m))")] THEN REWRITE_TAC [GROUP_SUM, IN_IMAGE, IN_ELIM_THM] THEN CONJ_TAC THENL [EXISTS_TAC (← q r"\y:A. if y IN t then n y MOD m else 0") THEN ASM_SIMP_TAC [MOD_LT_EQ], ALL_TAC] THEN wPart (rand o rand) (rand o rand) ABELIAN_GROUP_SUM_POW THEN ASM_SIMP_TAC [FINITE_RESTRICT, GROUP_POW] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN wPart rand (rand o rand) ABELIAN_GROUP_SUM_MUL THEN ASM_SIMP_TAC [FINITE_RESTRICT, GROUP_POW] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC GROUP_SUM_EQ THEN ASM_SIMP_TAC [GROUP_POW_POW, (← GSYM GROUP_POW_ADD)] THEN X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN AP_TERM_TAC THEN MP_TAC (← SPECL [(← q r"(n:A->num) y"), (← q r"m:num")] DIVISION) THEN ASM_REWRITE_TAC [] THEN ARITH_TAC)

  let GROUP_SUM_POW_REAL_MULTIPLICATIVE_BOUND ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"&2:real"
    let q2 ← q r"L + M:num"
    let q3 ← q r"M:num"
    let v4 ← SPECL [q3, q2, q1] REAL_POW_MONO
    let q5 ← q r"&2:real"
    let q6 ← q r"L + M:num"
    let q7 ← q r"L:num"
    let v8 ← SPECL [q7, q6, q5] REAL_POW_MONO
    let q9 ← q r"L + M:num"
    let q10 ← q r"z:real"
    let v11 ← SPEC q10 REAL_ARCH_POW2
    let q12 ← q r"M:num"
    let q13 ← q r"L:num"
    let q14 ← q r"w:real->bool"
    let q15 ← q r"z:real"
    let p16 ← prove r"!w:real->bool. FINITE w ==> ?L. !y. y IN w ==> y <= &2 pow L" (MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC [NOT_IN_EMPTY, FORALL_IN_INSERT] THEN MAP_EVERY X_GEN_TAC [q15, q14] THEN DISCH_THEN ((X_CHOOSE_TAC q13) o CONJUNCT1) THEN X_CHOOSE_TAC q12 v11 THEN EXISTS_TAC q9 THEN MP_TAC v8 THEN MP_TAC v4 THEN REWRITE_TAC [LE_ADD, LE_ADDR, REAL_OF_NUM_LE, ARITH] THEN ASM_MESON_TAC [REAL_LE_TRANS, REAL_LT_IMP_LE])
    let lemma := p16
    let q17 ← q r"(b:real) pow (n:A->num) x"
    let q18 ← q r"inv(b:real) pow (n:A->num) x"
    let v19 ← GSYM REAL_POW_INV
    let q20 ← q r"inv(b pow N) <= (g:A->real) x pow n x /\ g x pow n x <= b pow N"
    let q21 ← q r"b:real"
    let v22 ← SPEC q21 REAL_INV_1_LT
    let q23 ← q r"&0:real <= b /\ &1 <= b"
    let q24 ← q r"&0 < (g:A->real) x"
    let q25 ← q r"t:A->bool"
    let q26 ← q r"x:A"
    let v27 ← SPEC_ALL GROUP_SUM_CLAUSES_EXISTS
    let v28 ← CONJUNCT1 v27
    let q29 ← q r"t:A->bool"
    let q30 ← q r"t:A->bool"
    let q31 ← q r"g:A->real"
    let q32 ← q r"G:A group"
    let v33 ← ISPECL [q32, q31] GROUP_REAL_MULTIPLICATIVE_ID_INV_POW
    let p34 ← prove r"!G (g:A->real) t (n:A->num) b N.
        abelian_group G /\
        (!x. x IN group_carrier G ==> &0 < g x) /\
        (!x y. x IN group_carrier G /\ y IN group_carrier G
               ==> g(group_mul G x y) = g x * g y) /\
        FINITE t /\
        (!x. x IN t
             ==> x IN group_carrier G /\ inv b <= g x /\ g x <= b /\ n x <= N)
        ==> inv(b pow (N * CARD t)) <=
            g(group_sum G t (\x. group_pow G x (n x))) /\
            g(group_sum G t (\x. group_pow G x (n x))) <= b pow (N * CARD t)" (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN MP_TAC v33 THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN REWRITE_TAC [IMP_CONJ] THEN SPEC_TAC (q30, q29) THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN ASM_SIMP_TAC [v28, CARD_CLAUSES, ABELIAN_GROUP_SUM_CLAUSES, FINITE_RESTRICT, FORALL_IN_INSERT] THEN REWRITE_TAC [MULT_CLAUSES, real_pow, REAL_INV_1, REAL_LE_REFL] THEN MAP_EVERY X_GEN_TAC [q26, q25] THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN DISCH_THEN (fun ih => DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (MP_TAC o (MATCH_MP ih)))) THEN ASM_SIMP_TAC [GROUP_POW, GROUP_SUM, REAL_POW_ADD, REAL_INV_MUL] THEN STRIP_TAC THEN SUBGOAL_THEN q24 ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN q23 STRIP_ASSUME_TAC THENL [MP_TAC v22 THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN q20 STRIP_ASSUME_TAC THENL [REWRITE_TAC [v19] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL [EXISTS_TAC q18, EXISTS_TAC q17] THEN ASM_SIMP_TAC [REAL_POW_LE2, REAL_POW_MONO, REAL_POW_MONO_INV, REAL_LE_INV_EQ, REAL_INV_LE_1, REAL_LT_IMP_LE], CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC [REAL_LE_INV_EQ, REAL_POW_LE, REAL_LT_IMP_LE, GROUP_SUM]])
    let bound := p34
    let v35 ← GSYM REAL_INV_INV
    let q36 ← q r"x:A"
    let q37 ← q r"N:num"
    let q38 ← q r"(&2:real) pow L"
    let q39 ← q r"n:A->num"
    let q40 ← q r"t:A->bool"
    let q41 ← q r"(f:K->A->real) i"
    let q42 ← q r"G:A group"
    let v43 ← ISPECL [q42, q41, q40, q39, q38, q37] bound
    let q44 ← q r"N:num"
    let q45 ← q r"n:A->num"
    let q46 ← q r"i:K"
    let q47 ← q r"L:num"
    let q48 ← q r"{max ((f:K->A->real) i x) (inv(f i x)) | i IN s /\ x IN t}"
    let v49 ← ISPEC q48 lemma
    prove
      r"!G (s:K->bool) (f:K->A->real) t.
          abelian_group G /\ FINITE s /\
          (!i x. i IN s /\ x IN group_carrier G ==> &0 < f i x) /\
          (!i x y. i IN s /\ x IN group_carrier G /\ y IN group_carrier G
                   ==> f i (group_mul G x y) = f i x * f i y) /\
          FINITE t /\ t SUBSET group_carrier G
          ==> ?L. !i n N.
                    i IN s /\ (!x. x IN t ==> n x <= N)
                    ==> inv(&2 pow (L * N * CARD t)) <=
                        f i (group_sum G t (\x. group_pow G x (n x))) /\
                        f i (group_sum G t (\x. group_pow G x (n x))) <=
                        &2 pow (L * N * CARD t)"
      (REPEAT GEN_TAC THEN REWRITE_TAC [SUBSET] THEN STRIP_TAC THEN MP_TAC v49 THEN ASM_SIMP_TAC [FINITE_PRODUCT_DEPENDENT, FORALL_IN_GSPEC, REAL_MAX_LE] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC q47 THEN DISCH_TAC THEN MAP_EVERY X_GEN_TAC [q46, q45, q44] THEN STRIP_TAC THEN MP_TAC v43 THEN ASM_SIMP_TAC [REAL_POW_POW] THEN DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC q36 THEN DISCH_TAC THEN ASM_SIMP_TAC [] THEN GEN_REWRITE_TAC RAND_CONV [v35] THEN MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC [REAL_LT_INV_EQ])

  let GROUP_REAL_MULTIPLICATIVE_BOX_COUNT ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"~(j = 0) ==> SUC(j - 1) = j /\ j - 1 < j"
    let r2 ← ARITH_RULE q1
    let v3 ← CONJUNCT2 real_pow
    let v4 ← GSYM v3
    let q5 ← q r"j - 1"
    let q6 ← q r"j = 0"
    let v7 ← GSYM NOT_LT
    let q8 ← q r"j:num"
    let q9 ← q r"?j. (&2:real) pow k * y < &2 * &2 pow j"
    let q10 ← q r"&0:real < x ==> x < &2 * x"
    let r11 ← REAL_ARITH q10
    let q12 ← q r"(&2:real) pow k * &2 pow k"
    let q13 ← q r"&2 pow k * inv(&2 pow k)"
    let q14 ← q r"&1:real <= &2 pow k * y /\ &2 pow k * y < &2 * &2 pow (2 * k)"
    let q15 ← q r"&0:real < &2 pow k"
    let p16 ← prove r"!y k. inv(&2 pow k) <= y /\ y <= &2 pow k
           ==> ?j. j <= 2 * k /\ &2 pow j <= &2 pow k * y /\
                   &2 pow k * y < &2 * &2 pow j" (REPEAT STRIP_TAC THEN SUBGOAL_THEN q15 ASSUME_TAC THENL [SIMP_TAC [REAL_POW_LT, REAL_OF_NUM_LT, ARITH], ALL_TAC] THEN SUBGOAL_THEN q14 STRIP_ASSUME_TAC THENL [REWRITE_TAC [MULT_2, REAL_POW_ADD] THEN CONJ_TAC THENL [TRANS_TAC REAL_LE_TRANS q13 THEN ASM_SIMP_TAC [REAL_LE_LMUL, REAL_LT_IMP_LE, REAL_MUL_RINV, REAL_LT_IMP_NZ, REAL_LE_REFL], TRANS_TAC REAL_LET_TRANS q12 THEN ASM_SIMP_TAC [REAL_LE_LMUL, REAL_LT_IMP_LE, REAL_LT_MUL, r11]], ALL_TAC] THEN SUBGOAL_THEN q9 MP_TAC THENL [ASM_MESON_TAC [], GEN_REWRITE_TAC LAND_CONV [num_WOP]] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC q8 THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [REWRITE_TAC [v7] THEN ASM_MESON_TAC [], ASM_CASES_TAC q6 THEN ASM_REWRITE_TAC [real_pow] THEN FIRST_X_ASSUM (MP_TAC o (SPEC q5)) THEN ASM_SIMP_TAC [v4, r2] THEN REAL_ARITH_TAC])
    let dyadic := p16
    let q17 ← q r"&0:real < b"
    let v18 ← ASSUME q17
    let v19 ← MATCH_MP REAL_LT_LMUL_EQ v18
    let v20 ← GSYM v19
    let v21 ← GSYM real_div
    let p22 ← prove r"!a b u v. &0 < b /\ &0 < v /\ a <= b * u /\ b * u < &2 * a /\
               a <= b * v /\ b * v < &2 * a
               ==> inv(&2) <= u * inv v /\ u * inv v <= &2" (REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [v21, REAL_LE_LDIV_EQ, REAL_LE_RDIV_EQ] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ONCE_REWRITE_TAC [v20] THEN ASM_REAL_ARITH_TAC)
    let ratio := p22
    let q23 ← q r"y:A"
    let v24 ← GSYM MEMBER_NOT_EMPTY
    let q25 ← q r"y:A"
    let q26 ← q r"c:A->bool = {}"
    let p27 ← prove r"!c z (h:A->A->A).
        FINITE z /\ (!y. y IN c ==> c SUBSET IMAGE (h y) z)
        ==> FINITE c /\ CARD c <= CARD z" (REPEAT GEN_TAC THEN ASM_CASES_TAC q26 THEN ASM_REWRITE_TAC [FINITE_EMPTY, CARD_CLAUSES, LE_0] THEN FIRST_X_ASSUM ((X_CHOOSE_TAC q25) o (REWRITE_RULE [v24])) THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC q23)) THEN ASM_MESON_TAC [FINITE_SUBSET, FINITE_IMAGE, CARD_SUBSET, CARD_IMAGE_LE, LE_TRANS])
    let translate := p27
    let q28 ← q r"(&2:real) pow k"
    let q29 ← q r"(&2:real) pow (c:K->num) i"
    let q30 ← q r"(f:K->A->real) i"
    let q31 ← q r"G:A group"
    let v32 ← ISPECL [q31, q30] GROUP_REAL_MULTIPLICATIVE_ID_INV_POW
    let q33 ← q r"i:K"
    let v34 ← GSYM GROUP_MUL_ASSOC
    let q35 ← q r"group_mul G x (group_inv G y):A"
    let q36 ← q r"x:A"
    let q37 ← q r"y:A"
    let q38 ← q r"\y z:A. group_mul G z y"
    let p39 ← prove r"!G (s:K->bool) (f:K->A->real) k c.
        (!i x. i IN s /\ x IN group_carrier G ==> &0 < f i x) /\
        (!i x y. i IN s /\ x IN group_carrier G /\ y IN group_carrier G
                 ==> f i (group_mul G x y) = f i x * f i y) /\
        FINITE {x | x IN group_carrier G /\
                    !i. i IN s ==> inv(&2) <= f i x /\ f i x <= &2}
        ==> FINITE {x | x IN group_carrier G /\
                        !i. i IN s ==> &2 pow c i <= &2 pow k * f i x /\
                                       &2 pow k * f i x < &2 * &2 pow c i} /\
            CARD {x | x IN group_carrier G /\
                      !i. i IN s ==> &2 pow c i <= &2 pow k * f i x /\
                                     &2 pow k * f i x < &2 * &2 pow c i} <=
            CARD {x | x IN group_carrier G /\
                      !i. i IN s ==> inv(&2) <= f i x /\ f i x <= &2}" (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC translate THEN EXISTS_TAC q38 THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC q37 THEN REWRITE_TAC [IN_ELIM_THM, SUBSET, IN_IMAGE] THEN STRIP_TAC THEN X_GEN_TAC q36 THEN STRIP_TAC THEN EXISTS_TAC q35 THEN ASM_SIMP_TAC [v34, GROUP_MUL_LINV, GROUP_MUL_RID, GROUP_INV, GROUP_MUL] THEN X_GEN_TAC q33 THEN DISCH_TAC THEN MP_TAC v32 THEN ASM_SIMP_TAC [GROUP_INV] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN MATCH_MP_TAC ratio THEN MAP_EVERY EXISTS_TAC [q29, q28] THEN ASM_SIMP_TAC [REAL_POW_LT, REAL_OF_NUM_LT, ARITH])
    let cell := p39
    let q40 ← q r"\i. if i IN s then (c:K->num) i else 0"
    let q41 ← q r"c:K->num"
    let q42 ← q r"!i. ?j. i IN s
                ==> j <= 2 * k /\
                    &2 pow j <= &2 pow k * (f:K->A->real) i x /\
                    &2 pow k * f i x < &2 * &2 pow j"
    let q43 ← q r"x:A"
    let q44 ← q r"UNIONS {{x | x IN group_carrier G /\
                   !i. i IN s ==> &2 pow c i <= &2 pow k * (f:K->A->real) i x /\
                                  &2 pow k * f i x < &2 * &2 pow c i} |
              c | c IN {c | (!i. i IN s ==> c i IN 0..2 * k) /\
                        (!i. ~(i IN s) ==> c i = 0)}}"
    let q45 ← q r"!u:A->bool. FINITE u /\ s SUBSET u /\ CARD u <= n
                  ==> FINITE s /\ CARD s <= n"
    let r46 ← MESON [FINITE_SUBSET, CARD_SUBSET, LE_TRANS] q45
    prove
      r"!G (s:K->bool) (f:K->A->real) k.
          FINITE s /\
          (!i x. i IN s /\ x IN group_carrier G ==> &0 < f i x) /\
          (!i x y. i IN s /\ x IN group_carrier G /\ y IN group_carrier G
                   ==> f i (group_mul G x y) = f i x * f i y) /\
          FINITE {x | x IN group_carrier G /\
                      !i. i IN s ==> inv(&2) <= f i x /\ f i x <= &2}
          ==> FINITE {x | x IN group_carrier G /\
                          !i. i IN s ==> inv(&2 pow k) <= f i x /\
                                         f i x <= &2 pow k} /\
              CARD {x | x IN group_carrier G /\
                        !i. i IN s ==> inv(&2 pow k) <= f i x /\
                                       f i x <= &2 pow k}
              <= (2 * k + 1) EXP CARD s *
                 CARD {x | x IN group_carrier G /\
                           !i. i IN s ==> inv(&2) <= f i x /\ f i x <= &2}"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC r46 THEN EXISTS_TAC q44 THEN REPEAT CONJ_TAC THENL [ASM_SIMP_TAC [FINITE_UNIONS, SIMPLE_IMAGE, FINITE_IMAGE, FORALL_IN_IMAGE, FINITE_FUNSPACE, FINITE_NUMSEG, cell], REWRITE_TAC [SUBSET, SIMPLE_IMAGE, UNIONS_IMAGE, IN_ELIM_THM, IN_NUMSEG, LE_0] THEN X_GEN_TAC q43 THEN STRIP_TAC THEN SUBGOAL_THEN q42 MP_TAC THENL [REWRITE_TAC [RIGHT_EXISTS_IMP_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC dyadic THEN ASM_SIMP_TAC [], REWRITE_TAC [SKOLEM_THM] THEN DISCH_THEN (X_CHOOSE_TAC q41)] THEN EXISTS_TAC q40 THEN ASM_SIMP_TAC [], MATCH_MP_TAC CARD_UNIONS_LE THEN ASM_SIMP_TAC [cell] THEN MATCH_MP_TAC HAS_SIZE_FUNSPACE THEN ASM_REWRITE_TAC [HAS_SIZE, CARD_NUMSEG, FINITE_NUMSEG] THEN ARITH_TAC])

  let ABELIAN_GROUP_DISCRETE_DEPENDENT ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let v1 ← CONJUNCT2 EXP
    let v2 ← GSYM v1
    let q3 ← q r"N * N EXP m"
    let v4 ← GSYM MULT_EXP
    let v5 ← GSYM MULT_ASSOC
    let q6 ← q r"(a * (c + 1) EXP m) * N EXP m"
    let q7 ← q r"N = a * (c + 1) EXP m + 1"
    let q8 ← q r"a * (c + 1) EXP m + 1"
    let p9 ← prove r"!a c m. ?N. a * (c * N + 1) EXP m < (N + 1) EXP (m + 1)" (REPEAT GEN_TAC THEN EXISTS_TAC q8 THEN ABBREV_TAC q7 THEN TRANS_TAC LET_TRANS q6 THEN CONJ_TAC THENL [REWRITE_TAC [v5, v4, LE_MULT_LCANCEL] THEN DISJ2_TAC THEN MATCH_MP_TAC EXP_MONO_LE_IMP THEN EXPAND_TAC "N" THEN ARITH_TAC, TRANS_TAC LTE_TRANS q3 THEN CONJ_TAC THENL [REWRITE_TAC [LT_MULT_RCANCEL, EXP_EQ_0] THEN EXPAND_TAC "N" THEN ARITH_TAC, REWRITE_TAC [v2, ADD1] THEN MATCH_MP_TAC EXP_MONO_LE_IMP THEN ARITH_TAC]])
    let count := p9
    let q10 ← q r"group_sum G t (\x. group_mul G (group_pow G x ((a:A->num) x))
                                     (group_inv G (group_pow G x (b x))))"
    let q11 ← q r"~(a:A->num = b)"
    let q12 ← q r"\x:A. &((a:A->num) x) - &(b x):int"
    let p13 ← prove r"!G t (a:A->num) b.
        abelian_group G /\ FINITE t /\ t SUBSET group_carrier G /\
        (!x. ~(x IN t) ==> a x = 0 /\ b x = 0) /\ ~(a = b) /\
        group_sum G t (\x. group_pow G x (a x)) =
        group_sum G t (\x. group_pow G x (b x))
        ==> ?n. (?x. x IN t /\ ~(n x = &0)) /\
                group_sum G t (\x. group_zpow G x (n x)) = group_id G" (REWRITE_TAC [SUBSET] THEN REPEAT STRIP_TAC THEN EXISTS_TAC q12 THEN REWRITE_TAC [] THEN CONJ_TAC THENL [UNDISCH_TAC q11 THEN REWRITE_TAC [FUN_EQ_THM, NOT_FORALL_THM, INT_SUB_0, INT_OF_NUM_EQ] THEN ASM_MESON_TAC [], ALL_TAC] THEN TRANS_TAC EQ_TRANS q10 THEN CONJ_TAC THENL [MATCH_MP_TAC GROUP_SUM_EQ THEN ASM_SIMP_TAC [GROUP_ZPOW_SUB, GROUP_NPOW, group_div], ALL_TAC] THEN wPart lhand (lhand o rand) ABELIAN_GROUP_SUM_MUL THEN ASM_SIMP_TAC [FINITE_RESTRICT, GROUP_POW, GROUP_INV] THEN DISCH_THEN SUBST1_TAC THEN wPart (rand o lhand) (lhand o rand) ABELIAN_GROUP_SUM_INV THEN ASM_SIMP_TAC [FINITE_RESTRICT, GROUP_POW] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [GROUP_MUL_RINV, GROUP_SUM])
    let relation := p13
    let q14 ← q r"a:A->num"
    let q15 ← q r"CARD(IMAGE (\a. group_sum G t (\x:A. group_pow G x (a x))) D)"
    let q16 ← q r"(D:(A->num)->bool) HAS_SIZE (N + 1) EXP CARD(t:A->bool)"
    let q17 ← q r"!a b c:num. b * a < c ==> a * b < c"
    let r18 ← ARITH_RULE q17
    let q19 ← q r"(N + 1) EXP (CARD(s:K->bool) + 1)"
    let q20 ← q r"2 * L * N * CARD(t:A->bool) + 1 = (2 * L * CARD t) * N + 1"
    let r21 ← ARITH_RULE q20
    let q22 ← q r"(N + 1) EXP CARD(t:A->bool)"
    let q23 ← q r"!x y z:num. x < y /\ y <= z ==> ~(z <= x)"
    let r24 ← ARITH_RULE q23
    let q25 ← q r"L * N * CARD(t:A->bool)"
    let q26 ← q r"f:K->A->real"
    let q27 ← q r"s:K->bool"
    let q28 ← q r"G:A group"
    let v29 ← ISPECL [q28, q27, q26, q25] GROUP_REAL_MULTIPLICATIVE_BOX_COUNT
    let q30 ← q r"(?a b:A->num. P a /\ P b /\ ~(a = b) /\ (Q a:B) = Q b) <=>
      ~(!a b. P a /\ P b /\ Q a = Q b ==> a = b)"
    let r31 ← MESON [] q30
    let q32 ← q r"?a b. a IN D /\ b IN D /\ ~(a = b) /\
                        group_sum G t (\x. group_pow G x (a x)) =
                        group_sum G t (\x:A. group_pow G x (b x))"
    let q33 ← q r"D = {a | (!x:A. x IN t ==> a x IN 0..N) /\
                         (!x. ~(x IN t) ==> a x = 0)}"
    let q34 ← q r"N:num"
    let q35 ← q r"CARD(s:K->bool)"
    let q36 ← q r"2 * L * CARD(t:A->bool)"
    let q37 ← q r"CARD {x | x IN group_carrier G /\
                 !i. i IN s ==> inv(&2) <= (f:K->A->real) i x /\ f i x <= &2}"
    let v38 ← SPECL [q37, q36, q35] count
    let q39 ← q r"L:num"
    let q40 ← q r"t:A->bool"
    let q41 ← q r"f:K->A->real"
    let q42 ← q r"s:K->bool"
    let q43 ← q r"G:A group"
    let v44 ← ISPECL [q43, q42, q41, q40] GROUP_SUM_POW_REAL_MULTIPLICATIVE_BOUND
    prove
      r"!G:A group (s:K->bool) (f:K->A->real) t.
          abelian_group G /\ FINITE s /\
          (!i x. i IN s /\ x IN group_carrier G ==> &0 < f i x) /\
          (!i x y. i IN s /\ x IN group_carrier G /\ y IN group_carrier G
                   ==> f i (group_mul G x y) = f i x * f i y) /\
          (!b. FINITE {x | x IN group_carrier G /\
                           !i. i IN s ==> inv b <= f i x /\ f i x <= b}) /\
          FINITE t /\ t SUBSET group_carrier G /\ CARD s < CARD t
          ==> ?n. (?x. x IN t /\ ~(n x = &0)) /\
                  group_sum G t (\x. group_zpow G x (n x)) = group_id G"
      (REPEAT STRIP_TAC THEN MATCH_MP_TAC relation THEN ASM_REWRITE_TAC [] THEN MP_TAC v44 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC q39) THEN MP_TAC v38 THEN DISCH_THEN (X_CHOOSE_TAC q34) THEN ABBREV_TAC q33 THEN SUBGOAL_THEN q32 MP_TAC THENL [ALL_TAC, EXPAND_TAC "D" THEN REWRITE_TAC [IN_ELIM_THM] THEN MESON_TAC []] THEN REWRITE_TAC [r31] THEN DISCH_TAC THEN MP_TAC v29 THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r24 THEN EXISTS_TAC q22 THEN CONJ_TAC THENL [REWRITE_TAC [r21] THEN TRANS_TAC LTE_TRANS q19 THEN ASM_REWRITE_TAC [LE_EXP, ADD_EQ_0, ARITH_EQ] THEN CONJ_TAC THENL [ALL_TAC, ASM_ARITH_TAC] THEN MATCH_MP_TAC r18 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN q16 MP_TAC THENL [EXPAND_TAC "D" THEN MATCH_MP_TAC HAS_SIZE_FUNSPACE THEN ASM_REWRITE_TAC [HAS_SIZE, FINITE_NUMSEG, CARD_NUMSEG] THEN ARITH_TAC, REWRITE_TAC [HAS_SIZE] THEN STRIP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o SYM)] THEN TRANS_TAC LE_TRANS q15 THEN CONJ_TAC THENL [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC [], MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC []] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM, GROUP_SUM] THEN X_GEN_TAC q14 THEN EXPAND_TAC "D" THEN REWRITE_TAC [IN_ELIM_THM, IN_NUMSEG, LE_0] THEN STRIP_TAC THEN ASM_SIMP_TAC [])

  let FINITELY_GENERATED_ABELIAN_GROUP_DISCRETE ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"(x:A) INSERT B"
    let q2 ← q r"~(SUC k <= k)"
    let r3 ← ARITH_RULE q2
    let q4 ← q r"CARD((x:A) INSERT B)"
    let q5 ← q r"x:A"
    let q6 ← q r"B:A->bool"
    let q7 ← q r"B:A->bool"
    let q8 ← q r"k:num"
    let q9 ← q r"~(?n. (?x:A. x IN C /\ ~(n x = &0)) /\
                group_sum G C (\x. group_zpow G x (n x)) = group_id G)"
    let v10 ← GSYM NOT_LT
    let q11 ← q r"C:A->bool"
    let q12 ← q r"j:num"
    let q13 ← q r"m:num"
    let q14 ← q r"{}:A->bool"
    let q15 ← q r"0"
    let q16 ← q r"p /\ (q ==> r) ==> (p <=> q) ==> r"
    let r17 ← TAUT q16
    let q18 ← q r"\k. ?B. FINITE B /\ B SUBSET group_carrier G /\ CARD B = k /\
              ~(?n. (?x:A. x IN B /\ ~(n x = &0)) /\
                    group_sum G B (\x. group_zpow G x (n x)) = group_id G)"
    let v19 ← ISPEC q18 num_MAX
    let p20 ← prove r"!G:A group m.
        (!t. FINITE t /\ t SUBSET group_carrier G /\ m < CARD t
             ==> ?n. (?x. x IN t /\ ~(n x = &0)) /\
                     group_sum G t (\x. group_zpow G x (n x)) = group_id G)
        ==> ?B. FINITE B /\ B SUBSET group_carrier G /\
                ~(?n. (?x. x IN B /\ ~(n x = &0)) /\
                      group_sum G B (\x. group_zpow G x (n x)) = group_id G) /\
                !x. x IN group_carrier G /\ ~(x IN B)
                    ==> ?n. (?y. y IN x INSERT B /\ ~(n y = &0)) /\
                            group_sum G (x INSERT B)
                                      (\y. group_zpow G y (n y)) =
                            group_id G" (REPEAT STRIP_TAC THEN MP_TAC v19 THEN REWRITE_TAC [] THEN MATCH_MP_TAC r17 THEN CONJ_TAC THENL [CONJ_TAC THENL [MAP_EVERY EXISTS_TAC [q15, q14] THEN REWRITE_TAC [FINITE_EMPTY, EMPTY_SUBSET, CARD_CLAUSES, NOT_IN_EMPTY], EXISTS_TAC q13 THEN X_GEN_TAC q12 THEN DISCH_THEN (X_CHOOSE_THEN q11 STRIP_ASSUME_TAC) THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN REWRITE_TAC [v10] THEN DISCH_TAC THEN UNDISCH_TAC q9 THEN REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []], DISCH_THEN (X_CHOOSE_THEN q8 (CONJUNCTS_THEN2 (X_CHOOSE_THEN q7 STRIP_ASSUME_TAC) ASSUME_TAC))] THEN EXISTS_TAC q6 THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC q5 THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC q4)) THEN ASM_SIMP_TAC [CARD_CLAUSES, r3, NOT_EXISTS_THM] THEN DISCH_THEN (MP_TAC o (SPEC q1)) THEN ASM_SIMP_TAC [FINITE_INSERT, INSERT_SUBSET, CARD_CLAUSES, NOT_FORALL_THM])
    let maximal := p20
    let q21 ← q r"group_sum G B (\y:A. group_zpow G y ((n:A->int) y))"
    let q22 ← q r"group_inv G (group_pow G x q):A"
    let q23 ← q r"G:A group"
    let v24 ← ISPECL [q23, q22, q21] GROUP_LINV_UNIQUE
    let q25 ← q r"n:A->int"
    let q26 ← q r"\y. --((n:A->int) y)"
    let q27 ← q r"q:num"
    let q28 ← q r"(n:A->int) x"
    let v29 ← SPEC q28 INT_IMAGE
    let q30 ← q r"q:num"
    let q31 ← q r"group_sum G B (\y. group_inv G (group_zpow G y ((n:A->int) y)))"
    let q32 ← q r"group_sum G B (\y. group_zpow G y (--(n y))) =
      group_inv G (group_sum G B (\y:A. group_zpow G y (n y)))"
    let q33 ← q r"(n:A->int) x = &0"
    let q34 ← q r"group_sum G ((x:A) INSERT B)
                   (\y. group_zpow G y ((n:A->int) y)) = group_id G"
    let p35 ← prove r"!G B (x:A) n.
        abelian_group G /\ FINITE B /\ B SUBSET group_carrier G /\
        x IN group_carrier G /\ ~(x IN B) /\
        ~(?n. (?y. y IN B /\ ~(n y = &0)) /\
              group_sum G B (\y. group_zpow G y (n y)) = group_id G) /\
        (?y. y IN x INSERT B /\ ~(n y = &0)) /\
        group_sum G (x INSERT B) (\y. group_zpow G y (n y)) = group_id G
        ==> ?q d. ~(q = 0) /\
                  group_pow G x q = group_sum G B (\y. group_zpow G y (d y))" (REPEAT GEN_TAC THEN REWRITE_TAC [SUBSET] THEN DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN UNDISCH_TAC q34 THEN ASM_SIMP_TAC [ABELIAN_GROUP_SUM_CLAUSES, FINITE_RESTRICT, GROUP_ZPOW] THEN ASM_CASES_TAC q33 THENL [ASM_SIMP_TAC [GROUP_ZPOW_0, GROUP_MUL_LID, GROUP_SUM] THEN ASM_MESON_TAC [IN_INSERT], ALL_TAC] THEN SUBGOAL_THEN q32 ASSUME_TAC THENL [TRANS_TAC EQ_TRANS q31 THEN CONJ_TAC THENL [MATCH_MP_TAC GROUP_SUM_EQ THEN ASM_SIMP_TAC [GROUP_ZPOW_NEG], MATCH_MP_TAC ABELIAN_GROUP_SUM_INV THEN ASM_SIMP_TAC [FINITE_RESTRICT, GROUP_ZPOW]], ALL_TAC] THEN DISJ_CASES_THEN (X_CHOOSE_THEN q30 SUBST_ALL_TAC) v29 THEN RULE_ASSUM_TAC (REWRITE_RULE [INT_NEG_EQ_0, INT_OF_NUM_EQ]) THEN ASM_SIMP_TAC [GROUP_ZPOW_NEG, GROUP_NPOW] THEN DISCH_TAC THEN EXISTS_TAC q27 THEN ASM_REWRITE_TAC [] THENL [EXISTS_TAC q26, EXISTS_TAC q25] THEN ASM_REWRITE_TAC [] THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC GROUP_RINV_UNIQUE, MP_TAC v24] THEN ASM_SIMP_TAC [GROUP_INV_INV, GROUP_INV, GROUP_POW, GROUP_SUM])
    let power := p35
    let v36 ← GSYM GROUP_MUL_ASSOC
    let q37 ← q r"x = group_mul G (group_mul G x w) (group_inv G w):A"
    let q38 ← q r"&q:int"
    let q39 ← q r"(d:A->int) y"
    let v40 ← SPECL [q39, q38] INT_DIVISION
    let v41 ← GSYM GROUP_ZPOW_ADD
    let v42 ← GSYM GROUP_ZPOW_MUL
    let v43 ← GSYM GROUP_NPOW
    let q44 ← q r"y:A"
    let q45 ← q r"group_sum G B (\y:A. group_zpow G y (--(d y div &q))) = w"
    let v46 ← GSYM INT_OF_NUM_LE
    let q47 ← q r"&q:int"
    let q48 ← q r"(d:A->int) y"
    let v49 ← SPECL [q48, q47] INT_DIVISION
    let q50 ← q r"y:A"
    let q51 ← q r"\y:A. num_of_int(d y rem &q)"
    let q52 ← q r"group_mul G x w:A"
    let q53 ← q r"(w:A) IN group_carrier G"
    let q54 ← q r"w = group_sum G B (\y:A. group_zpow G y (--(d y div &q)))"
    let p55 ← prove r"!G B (x:A) q d.
        abelian_group G /\ FINITE B /\ B SUBSET group_carrier G /\
        x IN group_carrier G /\ ~(q = 0) /\
        group_pow G x q = group_sum G B (\y. group_zpow G y (d y))
        ==> ?z r. z IN group_carrier G /\ (!y. r y <= q) /\
                  group_pow G z q = group_sum G B (\y. group_pow G y (r y)) /\
                  x IN group_carrier(subgroup_generated G (z INSERT B))" (REPEAT GEN_TAC THEN REWRITE_TAC [SUBSET] THEN STRIP_TAC THEN ABBREV_TAC q54 THEN SUBGOAL_THEN q53 ASSUME_TAC THENL [EXPAND_TAC "w" THEN REWRITE_TAC [GROUP_SUM], ALL_TAC] THEN MAP_EVERY EXISTS_TAC [q52, q51] THEN ASM_SIMP_TAC [GROUP_MUL] THEN REPEAT CONJ_TAC THENL [X_GEN_TAC q50 THEN MP_TAC v49 THEN ASM_REWRITE_TAC [INT_OF_NUM_EQ, INT_ABS_NUM] THEN STRIP_TAC THEN ASM_SIMP_TAC [v46, INT_OF_NUM_OF_INT, INT_LT_IMP_LE], UNDISCH_THEN q45 (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [ABELIAN_GROUP_MUL_POW, GROUP_SUM] THEN wPart (rand o lhand) (rand o rand) ABELIAN_GROUP_SUM_POW THEN ASM_SIMP_TAC [FINITE_RESTRICT, GROUP_ZPOW] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN wPart lhand (rand o rand) ABELIAN_GROUP_SUM_MUL THEN ASM_SIMP_TAC [FINITE_RESTRICT, GROUP_ZPOW, GROUP_POW] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC GROUP_SUM_EQ THEN X_GEN_TAC q44 THEN DISCH_TAC THEN ASM_SIMP_TAC [v43, v42, v41] THEN AP_TERM_TAC THEN MP_TAC v40 THEN ASM_SIMP_TAC [INT_OF_NUM_EQ, INT_OF_NUM_OF_INT] THEN INT_ARITH_TAC, SUBGOAL_THEN q37 (fun th => GEN_REWRITE_TAC LAND_CONV [th]) THENL [ASM_SIMP_TAC [v36, GROUP_INV, GROUP_MUL_RINV, GROUP_MUL_RID], MATCH_MP_TAC IN_SUBGROUP_MUL THEN REWRITE_TAC [SUBGROUP_SUBGROUP_GENERATED]] THEN CONJ_TAC THENL [MATCH_MP_TAC SUBGROUP_GENERATED_INC_GEN THEN ASM_SIMP_TAC [GROUP_MUL, IN_INSERT], MATCH_MP_TAC IN_SUBGROUP_INV THEN REWRITE_TAC [SUBGROUP_SUBGROUP_GENERATED]] THEN EXPAND_TAC "w" THEN MATCH_MP_TAC IN_SUBGROUP_SUM THEN REWRITE_TAC [SUBGROUP_SUBGROUP_GENERATED] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_SUBGROUP_ZPOW THEN ASM_SIMP_TAC [SUBGROUP_SUBGROUP_GENERATED, SUBGROUP_GENERATED_INC_GEN, IN_INSERT]])
    let remainder := p55
    let q56 ← q r"(x:A) IN s ==> s SUBSET t ==> x IN t"
    let r57 ← SET_RULE q56
    let q58 ← q r"B UNION Z:A->bool"
    let q59 ← q r"(z:A) INSERT B"
    let q60 ← q r"G:A group"
    let v61 ← ISPECL [q60, q59, q58] SUBGROUP_GENERATED_MONO
    let q62 ← q r"q:num"
    let v63 ← GSYM REAL_POW_INV
    let q64 ← q r"(&2:real) pow (L * q * CARD(B:A->bool)) = (&2 pow (L * CARD B)) pow q"
    let q65 ← q r"(f:K->A->real) i"
    let q66 ← q r"G:A group"
    let v67 ← ISPECL [q66, q65] GROUP_REAL_MULTIPLICATIVE_ID_INV_POW
    let q68 ← q r"group_pow G z q = group_sum G B (\y:A. group_pow G y (r y))"
    let q69 ← q r"q:num"
    let q70 ← q r"r:A->num"
    let q71 ← q r"i:K"
    let q72 ← q r"i:K"
    let q73 ← q r"(z:A) IN Z"
    let q74 ← q r"r:A->num"
    let q75 ← q r"z:A"
    let q76 ← q r"d:A->int"
    let q77 ← q r"q:num"
    let q78 ← q r"x:A"
    let q79 ← q r"B:A->bool"
    let q80 ← q r"G:A group"
    let v81 ← ISPECL [q80, q79, q78, q77, q76] remainder
    let q82 ← q r"d:A->int"
    let q83 ← q r"q:num"
    let q84 ← q r"n:A->int"
    let q85 ← q r"x:A"
    let q86 ← q r"B:A->bool"
    let q87 ← q r"G:A group"
    let v88 ← ISPECL [q87, q86, q85, q84] power
    let q89 ← q r"n:A->int"
    let q90 ← q r"x:A"
    let q91 ← q r"(x:A) IN B"
    let q92 ← q r"x:A"
    let q93 ← q r"(Z:A->bool) SUBSET group_carrier G"
    let q94 ← q r"B UNION Z:A->bool"
    let q95 ← q r"Z = {x | x IN group_carrier G /\
               !i. i IN s ==> inv(&2 pow (L * CARD B)) <= (f:K->A->real) i x /\
                              f i x <= &2 pow (L * CARD(B:A->bool))}"
    let q96 ← q r"(&2:real) pow (L * CARD(B:A->bool))"
    let q97 ← q r"L:num"
    let q98 ← q r"B:A->bool"
    let q99 ← q r"f:K->A->real"
    let q100 ← q r"s:K->bool"
    let q101 ← q r"G:A group"
    let v102 ← ISPECL [q101, q100, q99, q98] GROUP_SUM_POW_REAL_MULTIPLICATIVE_BOUND
    let q103 ← q r"B:A->bool"
    let q104 ← q r"f:K->A->real"
    let q105 ← q r"s:K->bool"
    let q106 ← q r"CARD(s:K->bool)"
    let q107 ← q r"G:A group"
    let v108 ← ISPECL [q107, q106] maximal
    prove
      r"!G:A group (s:K->bool) (f:K->A->real).
          abelian_group G /\ FINITE s /\
          (!i x. i IN s /\ x IN group_carrier G ==> &0 < f i x) /\
          (!i x y. i IN s /\ x IN group_carrier G /\ y IN group_carrier G
                   ==> f i (group_mul G x y) = f i x * f i y) /\
          (!b. FINITE {x | x IN group_carrier G /\
                           !i. i IN s ==> inv b <= f i x /\ f i x <= b})
          ==> finitely_generated_group G"
      (REPEAT STRIP_TAC THEN MP_TAC v108 THEN ANTS_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC ABELIAN_GROUP_DISCRETE_DEPENDENT THEN MAP_EVERY EXISTS_TAC [q105, q104] THEN ASM_REWRITE_TAC [], DISCH_THEN (X_CHOOSE_THEN q103 STRIP_ASSUME_TAC)] THEN MP_TAC v102 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC q97) THEN FIRST_ASSUM (MP_TAC o (SPEC q96)) THEN ABBREV_TAC q95 THEN DISCH_TAC THEN REWRITE_TAC [FINITELY_GENERATED_GROUP] THEN EXISTS_TAC q94 THEN SUBGOAL_THEN q93 ASSUME_TAC THENL [EXPAND_TAC "Z" THEN REWRITE_TAC [SUBSET_RESTRICT], ALL_TAC] THEN ASM_REWRITE_TAC [FINITE_UNION, UNION_SUBSET, SUBGROUP_GENERATED_SUPERSET] THEN REWRITE_TAC [SUBSET] THEN X_GEN_TAC q92 THEN DISCH_TAC THEN ASM_CASES_TAC q91 THENL [MATCH_MP_TAC SUBGROUP_GENERATED_INC_GEN THEN ASM_REWRITE_TAC [IN_UNION], FIRST_X_ASSUM (MP_TAC o (SPEC q90)) THEN ASM_REWRITE_TAC []] THEN DISCH_THEN (X_CHOOSE_THEN q89 (CONJUNCTS_THEN ASSUME_TAC)) THEN MP_TAC v88 THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [q83, q82] THEN STRIP_TAC THEN MP_TAC v81 THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [q75, q74] THEN STRIP_TAC THEN SUBGOAL_THEN q73 ASSUME_TAC THENL [EXPAND_TAC "Z" THEN REWRITE_TAC [IN_ELIM_THM] THEN CONJ_TAC THENL [ASM_REWRITE_TAC [], X_GEN_TAC q72 THEN DISCH_TAC] THEN FIRST_X_ASSUM (MP_TAC o (SPECL [q71, q70, q69])) THEN UNDISCH_THEN q68 (SUBST1_TAC o SYM) THEN MP_TAC v67 THEN ASM_SIMP_TAC [] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN SUBGOAL_THEN q64 SUBST1_TAC THENL [REWRITE_TAC [REAL_POW_POW] THEN AP_TERM_TAC THEN ARITH_TAC, REWRITE_TAC [v63]] THEN STRIP_TAC THEN CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC q62 THEN ASM_SIMP_TAC [REAL_LT_IMP_LE, REAL_POW_LE, REAL_POS], ALL_TAC] THEN MP_TAC v61 THEN ASM_REWRITE_TAC [INSERT_SUBSET, IN_UNION, SUBSET_UNION] THEN MATCH_MP_TAC r57 THEN ASM_REWRITE_TAC [])

  -- @@RETURN BEGIN
  return { FINITELY_GENERATED_GROUP_EXTENSION, FINITELY_GENERATED_ABELIAN_GROUP_MOD_POW,
           GROUP_SUM_POW_REAL_MULTIPLICATIVE_BOUND, GROUP_REAL_MULTIPLICATIVE_BOX_COUNT,
           ABELIAN_GROUP_DISCRETE_DEPENDENT, FINITELY_GENERATED_ABELIAN_GROUP_DISCRETE }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- fingen_group.ml phrases from line 699 to 699                           -/
/- ---------------------------------------------------------------------- -/

structure FingenGroup02 where
  -- @@FIELDS
  FINITELY_GENERATED_ABELIAN_GROUP_INDEPENDENT_BASIS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFingenGroup02 [HolBase] (D : FingenGroupDeps) (BFingenGroup01 : FingenGroup01) :
    ExceptT String IO FingenGroup02 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, INTEGER_RULE, INT_ARITH_TAC, MESON_TAC, .. } := D
  let { ABELIAN_GROUP_SUM_MUL, ARITH, ARITH_EQ, CONTRAPOS_THM, EQ_TRANS,
        FINITELY_GENERATED_ABELIAN_GROUP_EXPONENTS, FINITE_CARTESIAN_PRODUCT,
        FINITE_CYCLIC_SUBGROUP_ORDER, FINITE_IMAGE, FINITE_INT_SEG, FINITE_RESTRICT,
        FINITE_SUBSET, FORALL_INT_CASES, GROUP_ID, GROUP_MUL_LID, GROUP_MUL_RID,
        GROUP_SUM_EQ, GROUP_SUM_RESTRICT_SET, GROUP_ZPOW, GROUP_ZPOW_0,
        GROUP_ZPOW_EQ_ID, INT_LE_NEG2, INT_OF_NUM_LE, IN_ELIM_THM, IN_IMAGE, IN_SING, .. } := D.core1
  let { IN_SUBGROUP_SUM, IN_SUBGROUP_ZPOW, LT_IMP_LE, LT_POW2_REFL, MONO_EXISTS,
        MONO_FORALL, NOT_FORALL_THM, NOT_IMP, NOT_LE, REAL_ARCH_SIMPLE, REAL_INV_INV,
        REAL_LE_INV2, REAL_LE_TRANS, REAL_LTE_TRANS, REAL_LT_INV_EQ, REAL_LT_POW2,
        REAL_OF_NUM_EQ, REAL_OF_NUM_LE, REAL_OF_NUM_LT, REAL_OF_NUM_POW, REAL_ZPOW_ADD,
        REAL_ZPOW_LT, REAL_ZPOW_NEG, REAL_ZPOW_NUM, RESTRICTION,
        RESTRICTION_IN_CARTESIAN_PRODUCT, SUBGROUP_GENERATED_INC_GEN,
        SUBGROUP_OF_TORSION, SUBGROUP_SUBGROUP_GENERATED, SUBSET, .. } := D.core2
  let { ABELIAN_GROUP_DISCRETE_DEPENDENT, .. } := BFingenGroup01
  -- @@SCOPE END

  let FINITELY_GENERATED_ABELIAN_GROUP_INDEPENDENT_BASIS ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"inv(&2 pow n)"
    let q2 ← q r"inv(&2 pow n):real"
    let q3 ← q r"inv b:real"
    let v4 ← ISPECL [q3, q2] REAL_LE_INV2
    let q5 ← q r"b:real"
    let q6 ← q r"(&2:real) pow n"
    let q7 ← q r"b:real"
    let v8 ← GSYM REAL_OF_NUM_LE
    let q9 ← q r"!n (b:real) N. &2 pow n <= b /\ b <= &N ==> n <= N"
    let p10 ← prove r"!a b N. inv b <= &2 zpow a /\ &2 zpow a <= b /\ b <= &N
             ==> --(&N) <= a /\ a <= &N" (SUBGOAL_THEN q9 ASSUME_TAC THENL [REPEAT STRIP_TAC THEN REWRITE_TAC [v8] THEN TRANS_TAC REAL_LE_TRANS q7 THEN ASM_REWRITE_TAC [] THEN TRANS_TAC REAL_LE_TRANS q6 THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [REAL_OF_NUM_POW, REAL_OF_NUM_LE] THEN MATCH_MP_TAC LT_IMP_LE THEN REWRITE_TAC [LT_POW2_REFL], ALL_TAC] THEN REWRITE_TAC [FORALL_INT_CASES, REAL_ZPOW_NEG, REAL_ZPOW_NUM] THEN REWRITE_TAC [INT_LE_NEG2, INT_OF_NUM_LE] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL [CONJ_TAC THENL [INT_ARITH_TAC, ASM_MESON_TAC []], CONJ_TAC THENL [ALL_TAC, INT_ARITH_TAC] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC q5 THEN ASM_REWRITE_TAC [] THEN MP_TAC v4 THEN REWRITE_TAC [REAL_INV_INV] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [REAL_LT_INV_EQ] THEN TRANS_TAC REAL_LTE_TRANS q1 THEN ASM_REWRITE_TAC [REAL_LT_INV_EQ, REAL_LT_POW2]])
    let zpowbound := p10
    let v11 ← GSYM SUBSET
    let q12 ← q r"!x:A. x IN t0 ==> x IN group_carrier G"
    let q13 ← q r"E:A->A->int"
    let q14 ← q r"t0:A->bool"
    let q15 ← q r"G:A group"
    let v16 ← ISPEC q15 FINITELY_GENERATED_ABELIAN_GROUP_EXPONENTS
    prove
      r"!G:A group.
          abelian_group G /\ finitely_generated_group G
          ==> ?t. FINITE t /\ t SUBSET group_carrier G /\
                  (!n. group_sum G t (\x. group_zpow G x (n x)) = group_id G
                       ==> !x. x IN t ==> n x = &0) /\
                  (!y. y IN group_carrier G
                       ==> ?z n. z IN group_carrier G /\
                                 ~(group_element_order G z = 0) /\
                                 y = group_mul G z
                                      (group_sum G t
                                        (\x. group_zpow G x (n x)))) /\
                  (!s. FINITE s /\ s SUBSET group_carrier G /\
                       (!n. group_sum G s (\x. group_zpow G x (n x)) =
                            group_id G
                            ==> !x. x IN s ==> n x = &0)
                       ==> CARD s <= CARD t)"
      (REPEAT STRIP_TAC THEN MP_TAC v16 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN q14 (X_CHOOSE_THEN q13 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "rep") (CONJUNCTS_THEN2 (LABEL_TAC "add") MP_TAC)))))) THEN SUBGOAL_THEN q12 ASSUME_TAC THENL [ASM_REWRITE_TAC [v11], ALL_TAC] THEN DISCH_THEN (fun inj => tactic_of do pure (EXISTS_TAC (← q r"{x:A | x IN t0 /\ group_element_order G x = 0}") THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC [], ALL_TAC] THEN CONJ_TAC THENL [REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ASM_SIMP_TAC [], ALL_TAC] THEN REPEAT CONJ_TAC THENL [X_GEN_TAC (← q r"n:A->int") THEN DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"\x:A. if group_element_order G x = 0 then (n:A->int) x else &0") inj) THEN ANTS_TAC THENL [GEN_REWRITE_TAC RAND_CONV [(← GSYM th)] THEN REWRITE_TAC [GROUP_SUM_RESTRICT_SET] THEN MATCH_MP_TAC GROUP_SUM_EQ THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [GROUP_ZPOW_0], ALL_TAC])) THEN REWRITE_TAC [IN_ELIM_THM] THEN MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC (← q r"x:A") THEN ASM_CASES_TAC (← q r"(x:A) IN t0") THEN ASM_REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"group_element_order G (x:A) = 0") THEN ASM_SIMP_TAC [GROUP_ZPOW_EQ_ID, (← INTEGER_RULE (← q r"!x:int. &0 divides x <=> x = &0"))], X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN ABBREV_TAC (← q r"z = group_sum G {x | x IN t0 /\ ~(group_element_order G x = 0)}
                          (\x:A. group_zpow G x ((E:A->A->int) x y))") THEN SUBGOAL_THEN (← q r"z IN {x:A | x IN group_carrier G /\ ~(group_element_order G x = 0)}") MP_TAC THENL [EXPAND_TAC "z" THEN MATCH_MP_TAC IN_SUBGROUP_SUM THEN ASM_SIMP_TAC [SUBGROUP_OF_TORSION] THEN X_GEN_TAC (← q r"x:A") THEN STRIP_TAC THEN MATCH_MP_TAC IN_SUBGROUP_ZPOW THEN RULE_ASSUM_TAC (REWRITE_RULE [IN_ELIM_THM]) THEN ASM_SIMP_TAC [SUBGROUP_OF_TORSION, IN_ELIM_THM], REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC] THEN MAP_EVERY EXISTS_TAC [(← q r"z:A"), (← q r"\x:A. (E:A->A->int) x y")] THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "z" THEN REWRITE_TAC [GROUP_SUM_RESTRICT_SET] THEN wPart rand (rand o rand) ABELIAN_GROUP_SUM_MUL THEN SIMP_TAC [FINITE_RESTRICT, (← ASSUME (← q r"FINITE(t0:A->bool)")), (← ASSUME (← q r"abelian_group(G:A group)"))] THEN ANTS_TAC THENL [REPEAT STRIP_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [GROUP_ZPOW, GROUP_ID], DISCH_THEN (SUBST1_TAC o SYM)] THEN TRANS_TAC EQ_TRANS (← q r"group_sum G t0 (\x:A. group_zpow G x ((E:A->A->int) x y))") THEN CONJ_TAC THENL [CONV_TAC SYM_CONV THEN USE_THEN "rep" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC, MATCH_MP_TAC GROUP_SUM_EQ THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [GROUP_MUL_LID, GROUP_MUL_RID, GROUP_ZPOW]], X_GEN_TAC (← q r"s:A->bool") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN ONCE_REWRITE_TAC [(← GSYM CONTRAPOS_THM)] THEN REWRITE_TAC [NOT_LE, NOT_FORALL_THM, NOT_IMP] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"G:A group"), (← q r"{x:A | x IN t0 /\ group_element_order G x = 0}"), (← q r"\x y. &2 zpow ((E:A->A->int) x y)"), (← q r"s:A->bool")] ABELIAN_GROUP_DISCRETE_DEPENDENT) THEN ANTS_TAC THENL [ALL_TAC, MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC []] THEN ASM_SIMP_TAC [FINITE_RESTRICT, REAL_ZPOW_LT, REAL_OF_NUM_LT, ARITH, IN_ELIM_THM] THEN CONJ_TAC THENL [ASM_SIMP_TAC [REAL_ZPOW_ADD, REAL_OF_NUM_EQ, ARITH_EQ], ALL_TAC] THEN X_GEN_TAC (← q r"b:real") THEN X_CHOOSE_TAC (← q r"N:num") (← SPEC (← q r"b:real") REAL_ARCH_SIMPLE) THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"IMAGE (group_sum G t0)
              (cartesian_product t0
                (\x:A. if group_element_order G x = 0
                       then IMAGE (group_zpow G x) {n | --(&N) <= n /\ n <= &N}
                       else group_carrier(subgroup_generated G {x})))") THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC [FINITE_CARTESIAN_PRODUCT] THEN DISJ2_TAC THEN ASM_SIMP_TAC [FINITE_RESTRICT] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [FINITE_IMAGE, FINITE_INT_SEG, FINITE_CYCLIC_SUBGROUP_ORDER], ALL_TAC] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM, IN_IMAGE] THEN X_GEN_TAC (← q r"y:A") THEN STRIP_TAC THEN EXISTS_TAC (← q r"RESTRICTION t0 (\x:A. group_zpow G x ((E:A->A->int) x y))") THEN CONJ_TAC THENL [TRANS_TAC EQ_TRANS (← q r"group_sum G t0 (\x:A. group_zpow G x ((E:A->A->int) x y))") THEN CONJ_TAC THENL [CONV_TAC SYM_CONV THEN USE_THEN "rep" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC, MATCH_MP_TAC GROUP_SUM_EQ THEN SIMP_TAC [RESTRICTION]], REWRITE_TAC [RESTRICTION_IN_CARTESIAN_PRODUCT] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN BETA_TAC THEN COND_CASES_TAC THENL [REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN EXISTS_TAC (← q r"(E:A->A->int) x y") THEN REWRITE_TAC [] THEN MATCH_MP_TAC zpowbound THEN EXISTS_TAC (← q r"b:real") THEN ASM_SIMP_TAC [], MATCH_MP_TAC IN_SUBGROUP_ZPOW THEN ASM_SIMP_TAC [SUBGROUP_SUBGROUP_GENERATED, SUBGROUP_GENERATED_INC_GEN, IN_SING]]]])))

  -- @@RETURN BEGIN
  return { FINITELY_GENERATED_ABELIAN_GROUP_INDEPENDENT_BASIS }
  -- @@RETURN END

end HolANT.FingenGroup
