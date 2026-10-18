/- ========================================================================= -/
/- Basic notions of cardinal arithmetic.                                     -/
/- ========================================================================= -/
/- File: HolLibrary/Card.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/card.ml`, by hand, in file order, in
  the style of HolLibrary/Wo.lean and HolLibrary/Transc.lean (see there and
  HolMath/Base.lean for the conventions).  card.ml begins with
  `needs "Library/wo.ml"`; wo.ml's bundles are passed to each setup as
  `(AX : HolLibrary.Wo.X)`.  Each section of card.ml is a bundle (a
  `structure`) built by a `setup` function; SessionLibrary/Card.lean builds
  the bundles in order and exports every name under its HOL Light name.

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, REAL_ARITH, TAUT, SET_RULE) they are bound
  first, in OCaml's order.
-/

import HolLibrary.Wo

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolLibrary.Wo (list3 lastThm elThm undischCheck subgoalLhand2 subgoalAnte2 NO_TAC)

namespace HolLibrary.Card

/- ------------------------------------------------------------------------- -/
/- What card.ml uses from the core library (supplied by Session).            -/
/- ------------------------------------------------------------------------- -/

/-- Theorems card.ml uses from the core library (part 1 of 3). -/
structure CoreThms1 where
  (ADD1 AND_FORALL_THM ARB ARITH CARD_BOOL CARD_CLAUSES CARD_CROSS CARD_DIFF
   CARD_IMAGE_INJ CARD_LE_1 CARD_NUMSEG_1 CARD_SING CARD_SUBSET
   CARD_SUBSET_EQ CARD_UNION CARTESIAN_PRODUCT_EQ_EMPTY
   CARTESIAN_PRODUCT_EQ_MEMBERS CART_EQ COMPL_COMPL COND_RAND COND_RATOR
   CONJ_ACI CONJ_ASSOC CONJ_SYM CONS_11 CONTRAPOS_THM COUNTABLE CROSS
   DE_MORGAN_THM DIFF_EMPTY DIMINDEX_GE_1 DISJOINT DISJOINT_SING EL
   EMPTY_GSPEC EMPTY_SUBSET EQ_IMP EQ_SYM_EQ EQ_TRANS ETA_AX EXISTS_IN_GSPEC
   EXISTS_IN_IMAGE EXISTS_PAIR_THM EXISTS_REFL EXISTS_SUBSET_IMAGE_INJ
   EXISTS_UNIQUE_ALT EXISTS_UNIQUE_DEF EXISTS_UNIQUE_THM EXP EXTENSION
   EXTENSIONAL FINITE_BOOL FINITE_CROSS FINITE_CROSS_EQ FINITE_DIFF
   FINITE_EMPTY FINITE_IMAGE FINITE_INDEX_NUMBERS FINITE_INDUCT_STRONG
   FINITE_INSERT FINITE_INTER FINITE_NUMSEG FINITE_POWERSET FINITE_PRODUCT
   FINITE_RESTRICTED_FUNSPACE FINITE_RULES FINITE_SING FINITE_SUBSET
   FINITE_UNION FINITE_UNIONS FORALL_AND_THM FORALL_CURRY FORALL_INT_CASES
   FORALL_IN_GSPEC FORALL_IN_IMAGE FORALL_IN_INSERT FORALL_IN_PCROSS
   FORALL_IN_UNION FORALL_IN_UNIONS FORALL_PAIR_THM FSTCART_PASTECART
   FUNCTION_FACTORS_LEFT_GEN FUN_EQ_THM HAS_SIZE HD IMAGE_CLAUSES IMAGE_ID
   IMAGE_SUBSET IMAGE_UNION IMAGE_o IMP_CONJ IMP_CONJ_ALT IMP_IMP IN : thm)
  deriving Inhabited

/-- Theorems card.ml uses from the core library (part 2 of 3). -/
structure CoreThms2 where
  (INFINITE INFINITE_CROSS_EQ INFINITE_ENUMERATE_SUBSET
   INJECTIVE_LEFT_INVERSE INJECTIVE_ON_ALT INJECTIVE_ON_LEFT_INVERSE INTER
   INTERSECTION_OF INTERSECTION_OF_EMPTY INTERSECTION_OF_INC INTERS_0
   INTERS_1 INTERS_2 INTERS_GSPEC INTERS_IMAGE INTERS_INSERT INTERS_UNIONS
   INTER_COMM INTER_SUBSET INTER_UNIONS INTER_UNIV INT_OF_NUM_EQ
   IN_CARTESIAN_PRODUCT IN_CROSS IN_DIFF IN_ELIM_PAIR_THM IN_ELIM_THM
   IN_GSPEC IN_IMAGE IN_INTER IN_INTERS IN_NUMSEG IN_SING IN_UNION IN_UNIONS
   IN_UNIV ITLIST I_THM LAMBDA_BETA LE LEFT_AND_EXISTS_THM
   LEFT_IMP_EXISTS_THM LEFT_IMP_FORALL_THM LENGTH LENGTH_EQ_NIL LET_ANTISYM
   LE_0 LE_1 LE_ADD_LCANCEL LE_ANTISYM LE_C LE_REFL LE_TRANS LT LT_LE LT_SUC
   MAP MAP_EQ_NIL MEM MEMBER_NOT_EMPTY MEM_LIST_OF_SET MEM_MAP MONO_AND
   MONO_EXISTS MONO_FORALL NOT_CONS_NIL NOT_EXISTS_THM NOT_FORALL_THM NOT_IMP
   NOT_INSERT_EMPTY NOT_IN_EMPTY NOT_LE NOT_SUC NUMPAIR_INJ NUMSEG_CLAUSES
   NUMSEG_EMPTY NUMSEG_SING OR_EXISTS_THM PAIR PAIRWISE_IMAGE PAIRWISE_SING
   PAIR_EQ PASTECART_FST_SND PASTECART_IN_PCROSS REAL_ADD_RID REAL_ARCH
   REAL_ARCH_LT REAL_BOUNDS_LT REAL_EQ_ADD_LCANCEL REAL_EQ_MUL_LCANCEL
   REAL_INV_MUL REAL_LET_TRANS REAL_LE_DIV REAL_LE_INV_EQ : thm)
  deriving Inhabited

/-- Theorems card.ml uses from the core library (part 3 of 3). -/
structure CoreThms3 where
  (REAL_LE_MUL REAL_LT_DIV REAL_LT_IMP_LE REAL_LT_INV_EQ REAL_LT_LMUL_EQ
   REAL_MUL_ASSOC REAL_OF_NUM_LT REAL_OF_NUM_SUC REAL_POS REAL_POW_1
   REAL_POW_ADD REAL_POW_LE REAL_POW_LT REAL_SHRINK_EQ REAL_SHRINK_RANGE
   REAL_SUB_LT REAL_SUP_LE REAL_WLOG_LT RESTRICTION
   RESTRICTION_IN_CARTESIAN_PRODUCT RESTRICTION_UNIQUE RIGHT_AND_EXISTS_THM
   RIGHT_EXISTS_AND_THM RIGHT_EXISTS_IMP_THM RIGHT_FORALL_IMP_THM
   RIGHT_IMP_EXISTS_THM RIGHT_IMP_FORALL_THM SET_OF_LIST_OF_SET SIMPLE_IMAGE
   SING_GSPEC SING_SUBSET SKOLEM_THM SNDCART_PASTECART SUBSET SUBSET_ANTISYM
   SUBSET_DIFF SUBSET_IMAGE_INJ SUBSET_NUMSEG SUBSET_REFL SUBSET_RESTRICT
   SUBSET_TRANS SUBSET_UNION SUBSET_UNIV SUC_INJ SUM_CLAUSES SUM_CLAUSES_LEFT
   SUM_CLAUSES_RIGHT SUM_COMBINE_R SUM_EQ_NUMSEG SUM_RESTRICT_SET SUM_SING
   SUM_SUBSET_SIMPLE SUP SURJECTIVE_ON_RIGHT_INVERSE SURJECTIVE_RIGHT_INVERSE
   SWAP_EXISTS_THM SWAP_FORALL_THM TL UNIONS UNIONS_0 UNIONS_1 UNIONS_2
   UNIONS_GSPEC UNIONS_IMAGE UNIONS_INSERT UNIONS_INTERS UNIONS_UNION
   UNION_COMM UNION_EMPTY UNION_OF UNION_OF_EMPTY UNION_OF_INC UNIV_NOT_EMPTY
   UNWIND_THM1 UNWIND_THM2 WF_MEASURE_GEN WF_SUBSET cartesian_product eq_c
   ge_c le_c lt_c num_INDUCTION num_INFINITE num_WOP o_DEF o_THM
   pair_RECURSION pairwise real_INFINITE real_div real_pow sum_INDUCT
   sum_RECURSION : thm)
  deriving Inhabited

/-- What card.ml uses from Session besides theorems. -/
structure CardDeps where
  -- definitions, datatypes and parser state
  new_definition : String → ExceptT String IO thm
  parse_as_infix : String × (Int × String) → IO Unit
  distinctness : String → ExceptT String IO thm
  injectivity : String → ExceptT String IO thm
  prove_cases_thm : thm → ExceptT String IO thm
  prove_recursive_functions_exist : thm → term → ExceptT String IO thm
  -- decision procedures and tactics
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_ARITH_TAC : tactic
  ASM_MESON_TAC : List thm → tactic
  ASM_METIS_TAC : List thm → tactic
  ASM_REAL_ARITH_TAC : tactic
  INDUCT_TAC : tactic
  LIST_INDUCT_TAC : tactic
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  METIS_TAC : List thm → tactic
  REAL_ARITH : term → ExceptT String IO thm
  REAL_ARITH_TAC : tactic
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  WF_INDUCT_TAC : term → tactic
  -- conversions
  GEN_BETA_CONV : ioconv
  NUM_REDUCE_CONV : ioconv
  REAL_RAT_REDUCE_CONV : ioconv
  SELECT_CONV : ioconv
  core1 : CoreThms1
  core2 : CoreThms2
  core3 : CoreThms3

/- ------------------------------------------------------------------------- -/
/- Sum-type lemmas, Knaster-Tarski, bijections, variants of cardinal         -/
/- equality, the "easy" ordering properties.  (card.ml 1-224)                -/
/- ------------------------------------------------------------------------- -/

structure Basics where
  -- @@FIELDS
  TRANS_CHAIN_TAC : thm → List term → tactic
  sum_DISTINCT : thm
  sum_INJECTIVE : thm
  sum_CASES : thm
  FORALL_SUM_THM : thm
  EXISTS_SUM_THM : thm
  FLATTEN_LEMMA : thm
  TARSKI_SET : thm
  INJECTIVE_LEFT_INVERSE_NONEMPTY : thm
  BIJECTIVE_INJECTIVE_SURJECTIVE : thm
  BIJECTIVE_INVERSES : thm
  EQ_C_BIJECTIONS : thm
  EQ_C : thm
  EQ_C_ALT : thm
  CARD_LE_REFL : thm
  CARD_EMPTY_LE : thm
  CARD_LE_TRANS : thm
  CARD_LT_REFL : thm
  CARD_LET_TRANS : thm
  CARD_LTE_TRANS : thm
  CARD_LT_TRANS : thm
  CARD_EQ_REFL : thm
  CARD_EQ_REFL_IMP : thm
  CARD_EQ_SYM : thm
  CARD_EQ_IMP_LE : thm
  CARD_LT_IMP_LE : thm
  CARD_LE_RELATIONAL : thm
  CARD_LE_RELATIONAL_FULL : thm
  CARD_LE_EMPTY : thm
  CARD_EQ_EMPTY : thm
  deriving Inhabited

@[nospecialize]
def setupBasics [HolBase] (D : CardDeps) :
    ExceptT String IO Basics := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, GEN_BETA_CONV, MESON_TAC, distinctness, injectivity,
        prove_cases_thm, .. } := D
  let { AND_FORALL_THM, CONJ_ACI, EXISTS_UNIQUE_ALT, EXTENSION, FUN_EQ_THM, .. } := D.core1
  let { INJECTIVE_ON_LEFT_INVERSE, IN_ELIM_THM, IN_INTERS, LE_C, MONO_EXISTS,
        NOT_IN_EMPTY, .. } := D.core2
  let { RIGHT_AND_EXISTS_THM, RIGHT_IMP_EXISTS_THM, SKOLEM_THM, SUBSET, SUBSET_ANTISYM,
        SUBSET_TRANS, SURJECTIVE_ON_RIGHT_INVERSE, SWAP_EXISTS_THM, eq_c, le_c, lt_c,
        o_THM, sum_INDUCT, .. } := D.core3
  -- @@SCOPE END

  let TRANS_CHAIN_TAC : thm → List term → tactic ← pure (fun th =>
    MAP_EVERY (fun t => TRANS_TAC th t THEN ASM_REWRITE_TAC []))

  -- We need these a few times, so give them names.

  let sum_DISTINCT ← distinctness "sum"

  let sum_INJECTIVE ← injectivity "sum"

  let sum_CASES ← prove_cases_thm sum_INDUCT

  let FORALL_SUM_THM ← prove
   r"(!z. P z) <=> (!x. P(INL x)) /\ (!x. P(INR x))"
   (MESON_TAC [sum_CASES])

  let EXISTS_SUM_THM ← prove
   r"(?z. P z) <=> (?x. P(INL x)) \/ (?x. P(INR x))"
   (MESON_TAC [sum_CASES])

  -- Useful lemma to reduce some higher order stuff to first order.

  let FLATTEN_LEMMA ← prove
   r"(!x. x IN s ==> (g(f(x)) = x)) <=> !y x. x IN s /\ (y = f x) ==> (g y = x)"
   (MESON_TAC [])

  -- Knaster-Tarski fixpoint theorem (used in Schroeder-Bernstein below).

  let TARSKI_SET ← prove
   r"!f. (!s t. s SUBSET t ==> f(s) SUBSET f(t)) ==> ?s:A->bool. f(s) = s"
   (REPEAT STRIP_TAC THEN MAP_EVERY ABBREV_TAC
     [← q r"Y = {b:A->bool | f(b) SUBSET b}", ← q r"a:A->bool = INTERS Y"] THEN
    SUBGOAL_THEN (← q r"!b:A->bool. b IN Y <=> f(b) SUBSET b") ASSUME_TAC THENL
     [EXPAND_TAC "Y" THEN REWRITE_TAC [IN_ELIM_THM], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!b:A->bool. b IN Y ==> f(a:A->bool) SUBSET b") ASSUME_TAC THENL
     [ASM_MESON_TAC [SUBSET_TRANS, IN_INTERS, SUBSET], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"f(a:A->bool) SUBSET a")
     (fun th => ASM_MESON_TAC [SUBSET_ANTISYM, IN_INTERS, th]) THEN
    ASM_MESON_TAC [IN_INTERS, SUBSET])

  -- We need a nonemptiness hypothesis for the nicest total function form.

  let INJECTIVE_LEFT_INVERSE_NONEMPTY ← prove
   r"(?x. x IN s)
   ==> ((!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) <=>
        ?g. (!y. y IN t ==> g(y) IN s) /\
            (!x. x IN s ==> (g(f(x)) = x)))"
   (REWRITE_TAC [FLATTEN_LEMMA, ← GSYM SKOLEM_THM, AND_FORALL_THM] THEN
    MESON_TAC [])

  -- Now bijectivity.

  let BIJECTIVE_INJECTIVE_SURJECTIVE ← prove
   r"(!x. x IN s ==> f(x) IN t) /\
   (!y. y IN t ==> ?!x. x IN s /\ (f x = y)) <=>
   (!x. x IN s ==> f(x) IN t) /\
   (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\
   (!y. y IN t ==> ?x. x IN s /\ (f x = y))"
   (MESON_TAC [])

  let BIJECTIVE_INVERSES ← prove
   r"(!x. x IN s ==> f(x) IN t) /\
   (!y. y IN t ==> ?!x. x IN s /\ (f x = y)) <=>
   (!x. x IN s ==> f(x) IN t) /\
   ?g. (!y. y IN t ==> g(y) IN s) /\
       (!y. y IN t ==> (f(g(y)) = y)) /\
       (!x. x IN s ==> (g(f(x)) = x))"
   (← do
    let t ← TAUT (← q r"(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)")
    pure (REWRITE_TAC [BIJECTIVE_INJECTIVE_SURJECTIVE,
                  INJECTIVE_ON_LEFT_INVERSE,
                  SURJECTIVE_ON_RIGHT_INVERSE] THEN
      MATCH_MP_TAC t THEN
      DISCH_TAC THEN REWRITE_TAC [RIGHT_AND_EXISTS_THM] THEN
      AP_TERM_TAC THEN ABS_TAC THEN EQ_TAC THEN ASM_MESON_TAC []))

  -- Other variants of cardinal equality.

  let EQ_C_BIJECTIONS ← prove
   r"!s:A->bool t:B->bool.
        s =_c t <=> ?f g. (!x. x IN s ==> f x IN t /\ g(f x) = x) /\
                          (!y. y IN t ==> g y IN s /\ f(g y) = y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [eq_c] THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC id [FUN_EQ_THM] THEN
    X_GEN_TAC (← q r"f:A->B") THEN REWRITE_TAC [] THEN
    EQ_TAC THENL [STRIP_TAC, MESON_TAC []] THEN
    EXISTS_TAC (← q r"(\y. @x. x IN s /\ f x = y):B->A") THEN
    ASM_MESON_TAC [])

  let EQ_C ← prove
   r"s =_c t <=>
   ?R:A#B->bool. (!x y. R(x,y) ==> x IN s /\ y IN t) /\
                 (!x. x IN s ==> ?!y. y IN t /\ R(x,y)) /\
                 (!y. y IN t ==> ?!x. x IN s /\ R(x,y))"
   (REWRITE_TAC [eq_c] THEN EQ_TAC THENL
     [DISCH_THEN (X_CHOOSE_THEN (← q r"f:A->B") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"\(x:A,y:B). x IN s /\ y IN t /\ (y = f x)") THEN
      CONV_TAC (ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_MESON_TAC [],
      DISCH_THEN (CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
       [EXISTS_UNIQUE_ALT, RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN
      MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC []])

  let EQ_C_ALT ← prove
   r"s =_c t <=>
   ?R:A#B->bool. (!x. x IN s ==> ?!y. y IN t /\ R(x,y)) /\
                 (!y. y IN t ==> ?!x. x IN s /\ R(x,y))"
   (GEN_REWRITE_TAC LAND_CONV [EQ_C] THEN
    EQ_TAC THENL [MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC [], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"R:A#B->bool") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"\(x,y). (R:A#B->bool)(x,y) /\ x IN s /\ y IN t") THEN
    ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [])

  -- The "easy" ordering properties.

  let CARD_LE_REFL ← prove
   r"!s:A->bool. s <=_c s"
   (GEN_TAC THEN REWRITE_TAC [le_c] THEN EXISTS_TAC (← q r"\x:A. x") THEN SIMP_TAC [])

  let CARD_EMPTY_LE ← prove
   r"!s:B->bool. ({}:A->bool) <=_c s"
   (REWRITE_TAC [LE_C, NOT_IN_EMPTY])

  let CARD_LE_TRANS ← prove
   r"!s:A->bool t:B->bool u:C->bool.
       s <=_c t /\ t <=_c u ==> s <=_c u"
   (REPEAT GEN_TAC THEN REWRITE_TAC [le_c] THEN
    DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_TAC (← q r"f:A->B")) (X_CHOOSE_TAC (← q r"g:B->C"))) THEN
    EXISTS_TAC (← q r"(g:B->C) o (f:A->B)") THEN REWRITE_TAC [o_THM] THEN
    ASM_MESON_TAC [])

  let CARD_LT_REFL ← prove
   r"!s:A->bool. ~(s <_c s)"
   (MESON_TAC [lt_c, CARD_LE_REFL])

  let CARD_LET_TRANS ← prove
   r"!s:A->bool t:B->bool u:C->bool.
       s <=_c t /\ t <_c u ==> s <_c u"
   (← do
    let t ← TAUT (← q r"(a /\ b ==> c) /\ (c' /\ a ==> b')
                     ==> a /\ b /\ ~b' ==> c /\ ~c'")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [lt_c] THEN
      MATCH_MP_TAC t THEN
      REWRITE_TAC [CARD_LE_TRANS]))

  let CARD_LTE_TRANS ← prove
   r"!s:A->bool t:B->bool u:C->bool.
       s <_c t /\ t <=_c u ==> s <_c u"
   (← do
    let t ← TAUT (← q r"(a /\ b ==> c) /\ (b /\ c' ==> a')
                     ==> (a /\ ~a') /\ b ==> c /\ ~c'")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [lt_c] THEN
      MATCH_MP_TAC t THEN
      REWRITE_TAC [CARD_LE_TRANS]))

  let CARD_LT_TRANS ← prove
   r"!s:A->bool t:B->bool u:C->bool.
       s <_c t /\ t <_c u ==> s <_c u"
   (MESON_TAC [lt_c, CARD_LTE_TRANS])

  let CARD_EQ_REFL ← prove
   r"!s:A->bool. s =_c s"
   (GEN_TAC THEN REWRITE_TAC [eq_c] THEN EXISTS_TAC (← q r"\x:A. x") THEN
    SIMP_TAC [] THEN MESON_TAC [])

  let CARD_EQ_REFL_IMP ← prove
   r"!s t:A->bool. s = t ==> s =_c t"
   (SIMP_TAC [CARD_EQ_REFL])

  let CARD_EQ_SYM ← prove
   r"!s t. s =_c t <=> t =_c s"
   (REPEAT GEN_TAC THEN REWRITE_TAC [eq_c, BIJECTIVE_INVERSES] THEN
    REWRITE_TAC [RIGHT_AND_EXISTS_THM] THEN
    GEN_REWRITE_TAC RAND_CONV [SWAP_EXISTS_THM] THEN
    REPEAT (AP_TERM_TAC THEN ABS_TAC) THEN REWRITE_TAC [CONJ_ACI])

  let CARD_EQ_IMP_LE ← prove
   r"!s t. s =_c t ==> s <=_c t"
   (REWRITE_TAC [le_c, eq_c] THEN MESON_TAC [])

  let CARD_LT_IMP_LE ← prove
   r"!s t. s <_c t ==> s <=_c t"
   (SIMP_TAC [lt_c])

  let CARD_LE_RELATIONAL ← prove
   r"!R:A->B->bool.
        (!x y y'. x IN s /\ R x y /\ R x y' ==> y = y')
        ==> {y | ?x. x IN s /\ R x y} <=_c s"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [le_c] THEN
    EXISTS_TAC (← q r"\y:B. @x:A. x IN s /\ R x y") THEN
    REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [])

  let CARD_LE_RELATIONAL_FULL ← prove
   r"!R:A->B->bool s t.
        (!y. y IN t ==> ?x. x IN s /\ R x y) /\
        (!x y y'. x IN s /\ y IN t /\ y' IN t /\ R x y /\ R x y' ==> y = y')
        ==> t <=_c s"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [le_c] THEN
    EXISTS_TAC (← q r"\y:B. @x:A. x IN s /\ R x y") THEN
    REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [])

  let CARD_LE_EMPTY ← prove
   r"!s. s <=_c {} <=> s = {}"
   (REWRITE_TAC [le_c, EXTENSION, NOT_IN_EMPTY] THEN MESON_TAC [])

  let CARD_EQ_EMPTY ← prove
   r"!s. s =_c {} <=> s = {}"
   (REWRITE_TAC [eq_c, EXTENSION, NOT_IN_EMPTY] THEN MESON_TAC [])

  -- @@RETURN BEGIN
  return { TRANS_CHAIN_TAC, sum_DISTINCT, sum_INJECTIVE, sum_CASES, FORALL_SUM_THM,
           EXISTS_SUM_THM, FLATTEN_LEMMA, TARSKI_SET, INJECTIVE_LEFT_INVERSE_NONEMPTY,
           BIJECTIVE_INJECTIVE_SURJECTIVE, BIJECTIVE_INVERSES, EQ_C_BIJECTIONS, EQ_C,
           EQ_C_ALT, CARD_LE_REFL, CARD_EMPTY_LE, CARD_LE_TRANS, CARD_LT_REFL,
           CARD_LET_TRANS, CARD_LTE_TRANS, CARD_LT_TRANS, CARD_EQ_REFL, CARD_EQ_REFL_IMP,
           CARD_EQ_SYM, CARD_EQ_IMP_LE, CARD_LT_IMP_LE, CARD_LE_RELATIONAL,
           CARD_LE_RELATIONAL_FULL, CARD_LE_EMPTY, CARD_EQ_EMPTY }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Antisymmetry (Schroeder-Bernstein), totality, trichotomy; finiteness in   -/
/- terms of N; images and preimages; strict cardinal comparability is        -/
/- wellfounded.  (card.ml 225-614)                                           -/
/- ------------------------------------------------------------------------- -/

structure Order where
  -- @@FIELDS
  CARD_LE_ANTISYM : thm
  CARD_LE_TOTAL : thm
  CARD_LET_TOTAL : thm
  CARD_LTE_TOTAL : thm
  CARD_LT_TOTAL : thm
  CARD_NOT_LE : thm
  CARD_NOT_LT : thm
  CARD_LT_LE : thm
  CARD_LE_LT : thm
  CARD_LE_CONG : thm
  CARD_LT_CONG : thm
  CARD_EQ_TRANS : thm
  CARD_EQ_CONG : thm
  INFINITE_CARD_LE : thm
  FINITE_CARD_LT : thm
  CARD_LE_SUBSET : thm
  CARD_LE_UNIV : thm
  CARD_LE_EQ_SUBSET : thm
  CARD_LE_EQ_SUBSET_UNIV : thm
  CARD_INFINITE_CONG : thm
  CARD_FINITE_CONG : thm
  CARD_LE_FINITE : thm
  CARD_EQ_FINITE : thm
  CARD_EQ_INFINITE : thm
  CARD_LE_INFINITE : thm
  CARD_LT_FINITE_INFINITE : thm
  CARD_LE_FINITE_INFINITE : thm
  CARD_LE_CARD_IMP : thm
  CARD_EQ_CARD_IMP : thm
  CARD_LE_CARD : thm
  CARD_EQ_CARD : thm
  CARD_LT_CARD : thm
  CARD_HAS_SIZE_CONG : thm
  NUMSEG_CARD_LE : thm
  CARD_LE_IMAGE : thm
  CARD_LE_IMAGE_GEN : thm
  CARD_EQ_IMAGE : thm
  CARD_GE_PREIMAGE : thm
  CARD_LE_PREIMAGE : thm
  CARD_EQ_PREIMAGE : thm
  CARD_LE_IMAGES : thm
  CARD_EQ_IMAGES : thm
  LE_C_IMAGE : thm
  LE_C_IMAGE_SUBSET : thm
  CARD_LE_SING : thm
  CARD_SING_LE : thm
  CARD_EQ_ORDINAL_EXISTS : thm
  WF_CARD_LT : thm
  deriving Inhabited

@[nospecialize]
def setupOrder [HolBase] (D : CardDeps) (BBasics : Basics) (ADefs : HolLibrary.Wo.Defs) (AOrders : HolLibrary.Wo.Orders) (ASegs : HolLibrary.Wo.Segs) (AInseg : HolLibrary.Wo.Inseg) (AWellOrder : HolLibrary.Wo.WellOrder) (AZorn : HolLibrary.Wo.Zorn) :
    ExceptT String IO Order := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, GEN_BETA_CONV, MESON_TAC, METIS_TAC, SET_RULE,
        SET_TAC, .. } := D
  let { AND_FORALL_THM, CARD_IMAGE_INJ, CARD_LE_1, CARD_NUMSEG_1, CARD_SING,
        CARD_SUBSET, CARD_SUBSET_EQ, DE_MORGAN_THM, EMPTY_SUBSET, ETA_AX, EXTENSION,
        FINITE_NUMSEG, FINITE_SING, FINITE_SUBSET, FORALL_IN_IMAGE, FORALL_PAIR_THM,
        FUNCTION_FACTORS_LEFT_GEN, HAS_SIZE, IMP_CONJ, IMP_CONJ_ALT, IN, .. } := D.core1
  let { INFINITE, INFINITE_ENUMERATE_SUBSET, INJECTIVE_ON_ALT, IN_ELIM_THM, IN_IMAGE,
        IN_SING, IN_UNIV, I_THM, LEFT_IMP_EXISTS_THM, LE_ANTISYM, LE_C, LE_TRANS,
        LT_LE, MEMBER_NOT_EMPTY, NOT_FORALL_THM, NOT_IMP, NOT_INSERT_EMPTY, NOT_LE, .. } := D.core2
  let { RIGHT_AND_EXISTS_THM, RIGHT_IMP_EXISTS_THM, SKOLEM_THM, SUBSET, SUBSET_REFL,
        SUBSET_UNIV, UNIONS, WF_MEASURE_GEN, WF_SUBSET, eq_c, le_c, lt_c, .. } := D.core3
  let { CARD_EMPTY_LE, CARD_EQ_IMP_LE, CARD_EQ_REFL, CARD_EQ_SYM, CARD_LET_TRANS,
        CARD_LE_EMPTY, CARD_LE_TRANS, CARD_LTE_TRANS, CARD_LT_IMP_LE, EQ_C, TARSKI_SET,
        TRANS_CHAIN_TAC, .. } := BBasics
  let { woset, .. } := ADefs
  let { properly, .. } := AOrders
  let { INSEG_REFL, inseg, ordinal, .. } := ASegs
  let { INSEG_ORDINAL, INSEG_SUBSET_FLD, ORDINAL_CHAINED, ORDINAL_IMP_WOSET, .. } := AInseg
  let { FLD_RESTRICT, SUBWOSET_ISO_INSEG, WF_INSEG_WOSET, WO_ORDINAL, .. } := AWellOrder
  let { ZL_SUBSETS_UNIONS, .. } := AZorn
  -- @@SCOPE END
  let tautConv : ioconv := fun t => (TAUT t).run

  -- Antisymmetry (the Schroeder-Bernstein theorem).

  let CARD_LE_ANTISYM ← prove
   r"!s:A->bool t:B->bool. s <=_c t /\ t <=_c s <=> (s =_c t)"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [REWRITE_TAC [le_c, EQ_C, INJECTIVE_ON_ALT],
      MESON_TAC [CARD_EQ_IMP_LE, CARD_EQ_SYM]] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"f:A->B") STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN (← q r"g:B->A") STRIP_ASSUME_TAC)) THEN
    MP_TAC (← ISPEC
     (← q r"\X. IMAGE (g:B->A) (t DIFF IMAGE (f:A->B) (s DIFF X))") TARSKI_SET) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL [SET_TAC [], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"u:A->bool")) THEN
    EXISTS_TAC (← q r"\(x:A,y:B). x IN s /\ y IN t /\
                            (~(x IN u) /\ y = f x \/ x IN u /\ x = g y)") THEN
    REWRITE_TAC [] THEN REPEAT (CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC]) THEN
    X_GEN_TAC (← q "y:B") THEN STRIP_TAC THEN
    ASM_CASES_TAC (← q r"y IN IMAGE (f:A->B) (s DIFF u)") THEN ASM SET_TAC [])

  -- Totality (cardinal comparability).

  let CARD_LE_TOTAL ← prove
   r"!s:A->bool t:B->bool. s <=_c t \/ t <=_c s"
   (REPEAT GEN_TAC THEN
    ABBREV_TAC
     (← q r"P = \R. (!x:A y:B. R(x,y) ==> x IN s /\ y IN t) /\
              (!x y y'. R(x,y) /\ R(x,y') ==> (y = y')) /\
              (!x x' y. R(x,y) /\ R(x',y) ==> (x = x'))") THEN
    MP_TAC (← ISPEC (← q r"P:((A#B)->bool)->bool") ZL_SUBSETS_UNIONS) THEN ANTS_TAC THENL
     [GEN_TAC THEN EXPAND_TAC "P" THEN
      REWRITE_TAC [UNIONS, IN_ELIM_THM] THEN
      REWRITE_TAC [SUBSET, IN] THEN MESON_TAC [],
      ALL_TAC] THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"R:A#B->bool") STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC (← q r"(!x:A. x IN s ==> ?y:B. y IN t /\ R(x,y)) \/
                   (!y:B. y IN t ==> ?x:A. x IN s /\ R(x,y))")
    THENL
     [FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o SPEC (← q r"\(x:A,y:B). T")) THEN
      FIRST_X_ASSUM (DISJ_CASES_THEN MP_TAC) THEN
      REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM, le_c] THEN ASM_MESON_TAC [],
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [DE_MORGAN_THM]) THEN
      REWRITE_TAC [NOT_FORALL_THM, NOT_IMP] THEN
      DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q "a:A")) (X_CHOOSE_TAC (← q "b:B"))) THEN
      FIRST_X_ASSUM (MP_TAC o SPEC
        (← q r"\(x:A,y:B). (x = a) /\ (y = b) \/ R(x,y)")) THEN
      REWRITE_TAC [SUBSET, FORALL_PAIR_THM, IN, EXTENSION] THEN
      CONV_TAC (ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      RULE_ASSUM_TAC (REWRITE_RULE [IN]) THEN ASM_MESON_TAC []])

  -- Other variants like "trichotomy of cardinals" now follow easily.

  let CARD_LET_TOTAL ← prove
   r"!s:A->bool t:B->bool. s <=_c t \/ t <_c s"
   (REWRITE_TAC [lt_c] THEN MESON_TAC [CARD_LE_TOTAL])

  let CARD_LTE_TOTAL ← prove
   r"!s:A->bool t:B->bool. s <_c t \/ t <=_c s"
   (REWRITE_TAC [lt_c] THEN MESON_TAC [CARD_LE_TOTAL])

  let CARD_LT_TOTAL ← prove
   r"!s:A->bool t:B->bool. s =_c t \/ s <_c t \/ t <_c s"
   (REWRITE_TAC [lt_c, ← GSYM CARD_LE_ANTISYM] THEN MESON_TAC [CARD_LE_TOTAL])

  let CARD_NOT_LE ← prove
   r"!s:A->bool t:B->bool. ~(s <=_c t) <=> t <_c s"
   (REWRITE_TAC [lt_c] THEN MESON_TAC [CARD_LE_TOTAL])

  let CARD_NOT_LT ← prove
   r"!s:A->bool t:B->bool. ~(s <_c t) <=> t <=_c s"
   (REWRITE_TAC [lt_c] THEN MESON_TAC [CARD_LE_TOTAL])

  let CARD_LT_LE ← prove
   r"!s t. s <_c t <=> s <=_c t /\ ~(s =_c t)"
   (REWRITE_TAC [lt_c, ← GSYM CARD_LE_ANTISYM] THEN CONV_TAC tautConv)

  let CARD_LE_LT ← prove
   r"!s t. s <=_c t <=> s <_c t \/ s =_c t"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM CARD_NOT_LT] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [CARD_LT_LE] THEN
    REWRITE_TAC [DE_MORGAN_THM, CARD_NOT_LE, CARD_EQ_SYM])

  let CARD_LE_CONG ← prove
   r"!s:A->bool s':B->bool t:C->bool t':D->bool.
      s =_c s' /\ t =_c t' ==> (s <=_c t <=> s' <=_c t')"
   (← do
    let t ← TAUT
     (← q r"!x y. (b /\ e ==> x) /\ (x /\ c ==> f) /\ (a /\ f ==> y) /\ (y /\ d ==> e)
            ==> (a /\ b) /\ (c /\ d) ==> (e <=> f)")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM CARD_LE_ANTISYM] THEN
      MATCH_MP_TAC t THEN
      MAP_EVERY EXISTS_TAC
       [← q r"(s':B->bool) <=_c (t:C->bool)",
        ← q r"(s:A->bool) <=_c (t':D->bool)"] THEN
      REWRITE_TAC [CARD_LE_TRANS]))

  let CARD_LT_CONG ← prove
   r"!s:A->bool s':B->bool t:C->bool t':D->bool.
      s =_c s' /\ t =_c t' ==> (s <_c t <=> s' <_c t')"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM CARD_NOT_LE] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC CARD_LE_CONG THEN
    ASM_REWRITE_TAC [])

  let CARD_EQ_TRANS ← prove
   r"!s:A->bool t:B->bool u:C->bool.
       s =_c t /\ t =_c u ==> s =_c u"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM CARD_LE_ANTISYM] THEN
    REPEAT STRIP_TAC THEN ASM_MESON_TAC [CARD_LE_TRANS])

  let CARD_EQ_CONG ← prove
   r"!s:A->bool s':B->bool t:C->bool t':D->bool.
      s =_c s' /\ t =_c t' ==> (s =_c t <=> s' =_c t')"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [TRANS_CHAIN_TAC CARD_EQ_TRANS [← q r"t:C->bool", ← q r"s:A->bool"],
      TRANS_CHAIN_TAC CARD_EQ_TRANS [← q r"s':B->bool", ← q r"t':D->bool"]] THEN
    ASM_MESON_TAC [CARD_EQ_SYM])

  -- Finiteness and infiniteness in terms of cardinality of N.

  let INFINITE_CARD_LE ← prove
   r"!s:A->bool. INFINITE s <=> (UNIV:num->bool) <=_c s"
   (REWRITE_TAC [INFINITE_ENUMERATE_SUBSET, le_c, IN_UNIV])

  let FINITE_CARD_LT ← prove
   r"!s:A->bool. FINITE s <=> s <_c (UNIV:num->bool)"
   (← do
    let t ← TAUT (← q r"(a <=> b) <=> (~a <=> ~b)")
    pure (ONCE_REWRITE_TAC [t] THEN
      REWRITE_TAC [← GSYM INFINITE, CARD_NOT_LT, INFINITE_CARD_LE]))

  let CARD_LE_SUBSET ← prove
   r"!s:A->bool t. s SUBSET t ==> s <=_c t"
   (REWRITE_TAC [SUBSET, le_c] THEN METIS_TAC [I_THM])

  let CARD_LE_UNIV ← prove
   r"!s:A->bool. s <=_c (:A)"
   (GEN_TAC THEN MATCH_MP_TAC CARD_LE_SUBSET THEN REWRITE_TAC [SUBSET_UNIV])

  let CARD_LE_EQ_SUBSET ← prove
   r"!s:A->bool t:B->bool. s <=_c t <=> ?u. u SUBSET t /\ (s =_c u)"
   (← do
    let t ← TAUT (← q r"(a <=> b) ==> b ==> a")
    pure (REPEAT GEN_TAC THEN EQ_TAC THENL
       [ALL_TAC,
        REPEAT STRIP_TAC THEN
        FIRST_ASSUM (MP_TAC o MATCH_MP CARD_LE_SUBSET) THEN
        MATCH_MP_TAC t THEN
        MATCH_MP_TAC CARD_LE_CONG THEN
        ASM_REWRITE_TAC [CARD_LE_CONG, CARD_EQ_REFL]] THEN
      REWRITE_TAC [le_c, eq_c] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"f:A->B") STRIP_ASSUME_TAC) THEN
      REWRITE_TAC [RIGHT_AND_EXISTS_THM] THEN EXISTS_TAC (← q r"IMAGE (f:A->B) s") THEN
      EXISTS_TAC (← q r"f:A->B") THEN REWRITE_TAC [IN_IMAGE, SUBSET] THEN
      ASM_MESON_TAC []))

  let CARD_LE_EQ_SUBSET_UNIV ← prove
   r"!s:A->bool. (?t:B->bool. t =_c s) <=> s <=_c (:B)"
   (REWRITE_TAC [CARD_LE_EQ_SUBSET, SUBSET_UNIV] THEN
    MESON_TAC [CARD_EQ_SYM])

  let CARD_INFINITE_CONG ← prove
   r"!s:A->bool t:B->bool. s =_c t ==> (INFINITE s <=> INFINITE t)"
   (REWRITE_TAC [INFINITE_CARD_LE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CARD_LE_CONG THEN ASM_REWRITE_TAC [CARD_EQ_REFL])

  let CARD_FINITE_CONG ← prove
   r"!s:A->bool t:B->bool. s =_c t ==> (FINITE s <=> FINITE t)"
   (← do
    let t ← TAUT (← q r"(a <=> b) <=> (~a <=> ~b)")
    pure (ONCE_REWRITE_TAC [t] THEN
      REWRITE_TAC [← GSYM INFINITE, CARD_INFINITE_CONG]))

  let CARD_LE_FINITE ← prove
   r"!s:A->bool t:B->bool. FINITE t /\ s <=_c t ==> FINITE s"
   (ASM_MESON_TAC [CARD_LE_EQ_SUBSET, FINITE_SUBSET, CARD_FINITE_CONG])

  let CARD_EQ_FINITE ← prove
   r"!s t:A->bool. FINITE t /\ s =_c t ==> FINITE s"
   (REWRITE_TAC [← GSYM CARD_LE_ANTISYM] THEN MESON_TAC [CARD_LE_FINITE])

  let CARD_EQ_INFINITE ← prove
   r"!(s:A->bool) (t:B->bool). INFINITE t /\ s =_c t ==> INFINITE s"
   (ONCE_REWRITE_TAC [CARD_EQ_SYM] THEN REWRITE_TAC [INFINITE] THEN
    MESON_TAC [CARD_EQ_FINITE])

  let CARD_LE_INFINITE ← prove
   r"!s:A->bool t:B->bool. INFINITE s /\ s <=_c t ==> INFINITE t"
   (MESON_TAC [CARD_LE_FINITE, INFINITE])

  let CARD_LT_FINITE_INFINITE ← prove
   r"!s:A->bool t:B->bool. FINITE s /\ INFINITE t ==> s <_c t"
   (REWRITE_TAC [← GSYM CARD_NOT_LE, INFINITE] THEN MESON_TAC [CARD_LE_FINITE])

  let CARD_LE_FINITE_INFINITE ← prove
   r"!s:A->bool t:B->bool.
        FINITE s /\ INFINITE t ==> s <=_c t"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CARD_LT_IMP_LE THEN
    ASM_SIMP_TAC [CARD_LT_FINITE_INFINITE])

  let CARD_LE_CARD_IMP ← prove
   r"!s:A->bool t:B->bool. FINITE t /\ s <=_c t ==> CARD s <= CARD t"
   (← do
    let ar ← ARITH_RULE (← q r"(m = n:num) ==> n <= m")
    pure (REPEAT STRIP_TAC THEN
      SUBGOAL_THEN (← q r"FINITE(s:A->bool)") ASSUME_TAC THENL
       [ASM_MESON_TAC [CARD_LE_FINITE], ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [le_c]) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"f:A->B") STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"CARD(IMAGE (f:A->B) s)") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC ar THEN
        MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC [],
        MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC [] THEN
        ASM_MESON_TAC [SUBSET, IN_IMAGE]]))

  let CARD_EQ_CARD_IMP ← prove
   r"!s:A->bool t:B->bool. FINITE t /\ s =_c t ==> (CARD s = CARD t)"
   (MESON_TAC [CARD_FINITE_CONG, LE_ANTISYM, CARD_LE_ANTISYM, CARD_LE_CARD_IMP])

  let CARD_LE_CARD ← prove
   r"!s:A->bool t:B->bool.
        FINITE s /\ FINITE t ==> (s <=_c t <=> CARD s <= CARD t)"
   (← do
    let t2 ← TAUT (← q r"(c ==> a ==> b) ==> a /\ ~b ==> ~c")
    let t1 ← TAUT (← q r"(a ==> b) /\ (~a ==> ~b) ==> (a <=> b)")
    pure (REPEAT STRIP_TAC THEN
      MATCH_MP_TAC t1 THEN
      ASM_SIMP_TAC [CARD_LE_CARD_IMP] THEN
      REWRITE_TAC [CARD_NOT_LE, NOT_LE] THEN REWRITE_TAC [lt_c, LT_LE] THEN
      ASM_SIMP_TAC [CARD_LE_CARD_IMP] THEN
      MATCH_MP_TAC t2 THEN
      DISCH_TAC THEN GEN_REWRITE_TAC LAND_CONV [CARD_LE_EQ_SUBSET] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"u:A->bool") STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC CARD_EQ_IMP_LE THEN
      SUBGOAL_THEN (← q r"u:A->bool = s") (fun th => ASM_MESON_TAC [th, CARD_EQ_SYM]) THEN
      ASM_MESON_TAC [CARD_SUBSET_EQ, CARD_EQ_CARD_IMP, CARD_EQ_SYM]))

  let CARD_EQ_CARD ← prove
   r"!s:A->bool t:B->bool.
        FINITE s /\ FINITE t ==> (s =_c t <=> (CARD s = CARD t))"
   (MESON_TAC [CARD_FINITE_CONG, LE_ANTISYM, CARD_LE_ANTISYM, CARD_LE_CARD])

  let CARD_LT_CARD ← prove
   r"!s:A->bool t:B->bool.
        FINITE s /\ FINITE t ==> (s <_c t <=> CARD s < CARD t)"
   (SIMP_TAC [CARD_LE_CARD, ← GSYM NOT_LE, ← GSYM CARD_NOT_LE])

  let CARD_HAS_SIZE_CONG ← prove
   r"!(s:A->bool) (t:B->bool) n. s =_c t ==> (s HAS_SIZE n <=> t HAS_SIZE n)"
   (REWRITE_TAC [HAS_SIZE] THEN
    MESON_TAC [CARD_EQ_CARD, CARD_FINITE_CONG])

  let NUMSEG_CARD_LE ← prove
   r"!(s:A->bool). (1..n) <=_c s <=> (FINITE s ==> n <= CARD s)"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"FINITE(s:A->bool)") THEN
    ASM_SIMP_TAC [CARD_LE_CARD, FINITE_NUMSEG, CARD_NUMSEG_1] THEN
    ASM_SIMP_TAC [CARD_LE_FINITE_INFINITE, INFINITE, FINITE_NUMSEG])

  let CARD_LE_IMAGE ← prove
   r"!f s. IMAGE f s <=_c s"
   (REWRITE_TAC [LE_C, FORALL_IN_IMAGE] THEN MESON_TAC [])

  let CARD_LE_IMAGE_GEN ← prove
   r"!f:A->B s t. t SUBSET IMAGE f s ==> t <=_c s"
   (REPEAT STRIP_TAC THEN TRANS_TAC CARD_LE_TRANS (← q r"IMAGE (f:A->B) s") THEN
    ASM_SIMP_TAC [CARD_LE_IMAGE, CARD_LE_SUBSET])

  let CARD_EQ_IMAGE ← prove
   r"!f:A->B s.
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> IMAGE f s =_c s"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [CARD_EQ_SYM] THEN
    REWRITE_TAC [eq_c] THEN EXISTS_TAC (← q r"f:A->B") THEN ASM SET_TAC [])

  let CARD_GE_PREIMAGE ← prove
   r"!(f:A->B) s t.
        t SUBSET IMAGE f s ==> t <=_c {x | x IN s /\ f x IN t}"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [LE_C] THEN EXISTS_TAC (← q r"f:A->B") THEN
    ASM SET_TAC [])

  let CARD_LE_PREIMAGE ← prove
   r"!(f:A->B) s t.
        (!x y. x IN s /\ y IN s /\ f x IN t /\ f y IN t /\ f x = f y ==> x = y)
        ==> {x | x IN s /\ f x IN t} <=_c t"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [le_c] THEN EXISTS_TAC (← q r"f:A->B") THEN
    ASM SET_TAC [])

  let CARD_EQ_PREIMAGE ← prove
   r"!(f:A->B) s t.
     (!x y. x IN s /\ y IN s /\ f x IN t /\ f y IN t /\ f x = f y ==> x = y) /\
     t SUBSET IMAGE f s
     ==> {x | x IN s /\ f x IN t} =_c t"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM CARD_LE_ANTISYM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CARD_LE_PREIMAGE, MATCH_MP_TAC CARD_GE_PREIMAGE] THEN
    ASM SET_TAC [])

  let CARD_LE_IMAGES ← prove
   r"!(f:A->B) (g:A->C) s.
        (!x y. x IN s /\ y IN s /\ g x = g y ==> f x = f y)
        ==> IMAGE f s <=_c IMAGE g s"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [FUNCTION_FACTORS_LEFT_GEN, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"h:C->B") THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"IMAGE f s = IMAGE (h:C->B) (IMAGE (g:A->C) s)") SUBST1_TAC THENL
     [ASM SET_TAC [], REWRITE_TAC [CARD_LE_IMAGE]])

  let CARD_EQ_IMAGES ← prove
   r"!(f:A->B) (g:A->C) s.
        (!x y. x IN s /\ y IN s ==> (f x = f y <=> g x = g y))
        ==> IMAGE f s =_c IMAGE g s"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM CARD_LE_ANTISYM] THEN
    CONJ_TAC THEN MATCH_MP_TAC CARD_LE_IMAGES THEN ASM_MESON_TAC [])

  let LE_C_IMAGE ← prove
   r"!s:A->bool t:B->bool.
        s <=_c t <=> s = {} \/ ?f. IMAGE f t = s"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"s:A->bool = {}") THEN
    ASM_REWRITE_TAC [CARD_EMPTY_LE] THEN EQ_TAC THENL
     [FIRST_X_ASSUM (X_CHOOSE_TAC (← q "a:A") o
        GEN_REWRITE_RULE id [← GSYM MEMBER_NOT_EMPTY]) THEN
      REWRITE_TAC [LE_C] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"f:B->A")) THEN
      EXISTS_TAC (← q r"\x. if (f:B->A) x IN s then f x else a") THEN
      ASM SET_TAC [],
      DISCH_THEN (CHOOSE_THEN (SUBST1_TAC o SYM)) THEN
      REWRITE_TAC [CARD_LE_IMAGE]])

  let LE_C_IMAGE_SUBSET ← prove
   r"!s:A->bool t:B->bool. s <=_c t <=> ?f. s SUBSET IMAGE f t"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [REWRITE_TAC [LE_C_IMAGE] THEN MESON_TAC [EMPTY_SUBSET, SUBSET_REFL],
      DISCH_THEN (CHOOSE_THEN (MP_TAC o MATCH_MP CARD_LE_SUBSET)) THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] CARD_LE_TRANS) THEN
      REWRITE_TAC [CARD_LE_IMAGE]])

  let CARD_LE_SING ← prove
   r"!(c:B) (s:A->bool). s <=_c {c} <=> ?a. s SUBSET {a}"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"FINITE(s:A->bool)") THENL
     [ASM_SIMP_TAC [CARD_LE_CARD, FINITE_SING, ← GSYM CARD_LE_1, CARD_SING],
      ASM_MESON_TAC [FINITE_SUBSET, FINITE_SING, CARD_LE_FINITE]])

  let CARD_SING_LE ← prove
   r"!a:A s:B->bool. {a} <=_c s <=> ~(s = {})"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"s:B->bool = {}") THEN
    ASM_REWRITE_TAC [CARD_LE_EMPTY, NOT_INSERT_EMPTY] THEN
    FIRST_X_ASSUM (X_CHOOSE_TAC (← q "b:B") o
      GEN_REWRITE_RULE id [← GSYM MEMBER_NOT_EMPTY]) THEN
    REWRITE_TAC [le_c] THEN EXISTS_TAC (← q r"(\x. b):A->B") THEN
    ASM_SIMP_TAC [IN_SING])

  -- Strict cardinal comparability on a given type is a wellfounded relation.

  let CARD_EQ_ORDINAL_EXISTS ← prove
   r"!s:A->bool. ?l:A->A->bool. ordinal l /\ fld l =_c s"
   (← do
    let s2 ← SET_RULE (← q r"(\x. x IN s) = s")
    let s1 ← SET_RULE (← q r"s = UNIV <=> !x. s x")
    let io ← REWRITE_RULE [IMP_CONJ_ALT] INSEG_ORDINAL
    pure (REPEAT STRIP_TAC THEN
      SUBGOAL_THEN (← q r"?l:A->A->bool. ordinal l /\ !x. fld l x") STRIP_ASSUME_TAC THENL
       [REWRITE_TAC [WO_ORDINAL],
        MP_TAC (← ISPECL [← q r"l:A->A->bool", ← q r"s:A->bool"] SUBWOSET_ISO_INSEG)] THEN
      FIRST_ASSUM (ASSUME_TAC o CONJUNCT1 o REWRITE_RULE [ordinal]) THEN
      ASM_REWRITE_TAC [s1] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"f:A->A") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"\x y. x IN IMAGE (f:A->A) s /\ y IN IMAGE f s /\ l x y") THEN
      CONJ_TAC THENL
       [FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP io) THEN ASM_SIMP_TAC [inseg, FLD_RESTRICT],
        GEN_REWRITE_TAC LAND_CONV [← GSYM ETA_AX] THEN
        ASM_SIMP_TAC [FLD_RESTRICT, s2] THEN
        MATCH_MP_TAC CARD_EQ_IMAGE] THEN
      REPEAT (POP_ASSUM MP_TAC) THEN REWRITE_TAC [properly, woset] THEN SET_TAC []))

  let WF_CARD_LT ← prove
   r"WF((<_c):(A->bool)->(A->bool)->bool)"
   (← do
    let s1 ← SET_RULE (← q r"(!x. s x ==> t x) <=> s SUBSET t")
    let t1 ← TAUT (← q r"~p /\ (~p /\ q ==> r) ==> p \/ q ==> r")
    let wfs ← REWRITE_RULE [IMP_CONJ] WF_SUBSET
    let wm ← MATCH_MP WF_MEASURE_GEN
      (← HolLight.INST_TYPE [(← qty "B", ← qty "A")] WF_INSEG_WOSET)
    pure (SUBGOAL_THEN
       (← q r"?w:(A->bool)->A->A->bool. (!s. ordinal(w s)) /\ (!s. fld(w s) =_c s)")
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC [AND_FORALL_THM, ← GSYM SKOLEM_THM, CARD_EQ_ORDINAL_EXISTS],
        ALL_TAC] THEN
      MP_TAC (← ISPEC (← q r"w:(A->bool)->A->A->bool") wm) THEN
      MATCH_MP_TAC wfs THEN
      REWRITE_TAC [] THEN
      MAP_EVERY X_GEN_TAC [← q r"s:A->bool", ← q r"t:A->bool"] THEN DISCH_TAC THEN
      ASM_SIMP_TAC [ORDINAL_IMP_WOSET] THEN
      MP_TAC (← ISPECL [← q r"(w:(A->bool)->A->A->bool) s", ← q r"(w:(A->bool)->A->A->bool) t"]
            ORDINAL_CHAINED) THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC t1 THEN
      CONJ_TAC THENL [ALL_TAC, MESON_TAC [INSEG_REFL]] THEN
      DISCH_THEN (MP_TAC o MATCH_MP INSEG_SUBSET_FLD) THEN
      REWRITE_TAC [s1, ETA_AX] THEN
      DISCH_THEN (MP_TAC o MATCH_MP CARD_LE_SUBSET) THEN
      REWRITE_TAC [CARD_NOT_LE] THEN
      TRANS_TAC CARD_LET_TRANS (← q r"s:A->bool") THEN
      ASM_SIMP_TAC [CARD_EQ_IMP_LE] THEN
      TRANS_TAC CARD_LTE_TRANS (← q r"t:A->bool") THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC CARD_EQ_IMP_LE THEN ONCE_REWRITE_TAC [CARD_EQ_SYM] THEN
      ASM_REWRITE_TAC []))

  -- @@RETURN BEGIN
  return { CARD_LE_ANTISYM, CARD_LE_TOTAL, CARD_LET_TOTAL, CARD_LTE_TOTAL, CARD_LT_TOTAL,
           CARD_NOT_LE, CARD_NOT_LT, CARD_LT_LE, CARD_LE_LT, CARD_LE_CONG, CARD_LT_CONG,
           CARD_EQ_TRANS, CARD_EQ_CONG, INFINITE_CARD_LE, FINITE_CARD_LT, CARD_LE_SUBSET,
           CARD_LE_UNIV, CARD_LE_EQ_SUBSET, CARD_LE_EQ_SUBSET_UNIV, CARD_INFINITE_CONG,
           CARD_FINITE_CONG, CARD_LE_FINITE, CARD_EQ_FINITE, CARD_EQ_INFINITE,
           CARD_LE_INFINITE, CARD_LT_FINITE_INFINITE, CARD_LE_FINITE_INFINITE,
           CARD_LE_CARD_IMP, CARD_EQ_CARD_IMP, CARD_LE_CARD, CARD_EQ_CARD, CARD_LT_CARD,
           CARD_HAS_SIZE_CONG, NUMSEG_CARD_LE, CARD_LE_IMAGE, CARD_LE_IMAGE_GEN,
           CARD_EQ_IMAGE, CARD_GE_PREIMAGE, CARD_LE_PREIMAGE, CARD_EQ_PREIMAGE,
           CARD_LE_IMAGES, CARD_EQ_IMAGES, LE_C_IMAGE, LE_C_IMAGE_SUBSET, CARD_LE_SING,
           CARD_SING_LE, CARD_EQ_ORDINAL_EXISTS, WF_CARD_LT }
  -- @@RETURN END

/-- `W(MP_TAC o PART_MATCH f th o lhand o snd)` -/
def mpPartLhand [HolBase] (f : term → Except String term) (th : thm) : tactic := fun gl =>
  ExceptT.run do
    let t ← liftExcept (lhand gl.2)
    ExceptT.mk (MP_TAC (← PART_MATCH f th t) gl)

/- ------------------------------------------------------------------------- -/
/- Cardinal arithmetic operations; congruences; misc lemmas; "arithmetical"  -/
/- lemmas; cardinal addition and union.  (card.ml 622-886)                   -/
/- ------------------------------------------------------------------------- -/

structure Arith where
  -- @@FIELDS
  add_c : thm
  mul_c : thm
  CARD_LE_ADD : thm
  CARD_LE_MUL : thm
  CARD_FUNSPACE_LE : thm
  CARD_ADD_CONG : thm
  CARD_MUL_CONG : thm
  CARD_FUNSPACE_CONG : thm
  MUL_C_UNIV : thm
  CARD_FUNSPACE_CURRY : thm
  IN_CARD_ADD : thm
  IN_CARD_MUL : thm
  CARD_LE_SQUARE : thm
  CARD_SQUARE_NUM : thm
  UNION_LE_ADD_C : thm
  CARD_ADD_C : thm
  CARD_MUL_C : thm
  CARD_ADD_SYM : thm
  CARD_ADD_ASSOC : thm
  CARD_MUL_SYM : thm
  CARD_MUL_ASSOC : thm
  CARD_LDISTRIB : thm
  CARD_RDISTRIB : thm
  CARD_LE_ADDR : thm
  CARD_LE_ADDL : thm
  CARD_MUL_LID : thm
  CARD_MUL_RID : thm
  CARD_ADD_LE_MUL_INFINITE : thm
  CARD_DISJOINT_UNION : thm
  CARD_LE_EXISTS : thm
  CARD_LT_IMP_SUC_LE : thm
  deriving Inhabited

@[nospecialize]
def setupArith [HolBase] (D : CardDeps) (BBasics : Basics) (BOrder : Order) :
    ExceptT String IO Arith := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, GEN_BETA_CONV, MESON_TAC, NUM_REDUCE_CONV, SELECT_CONV,
        SET_RULE, SET_TAC, new_definition, parse_as_infix,
        prove_recursive_functions_exist, .. } := D
  let { CARD_CROSS, CARD_IMAGE_INJ, CARD_SING, CARD_UNION, COND_RAND, COND_RATOR,
        CROSS, EXISTS_PAIR_THM, EXISTS_UNIQUE_THM, EXTENSION, FINITE_IMAGE,
        FINITE_SING, FORALL_PAIR_THM, FUN_EQ_THM, IMAGE_UNION, IMAGE_o, IMP_CONJ_ALT, .. } := D.core1
  let { INJECTIVE_LEFT_INVERSE, INJECTIVE_ON_ALT, IN_DIFF, IN_ELIM_PAIR_THM,
        IN_ELIM_THM, IN_INTER, IN_SING, IN_UNION, IN_UNIV, LEFT_IMP_EXISTS_THM,
        LEFT_IMP_FORALL_THM, LE_REFL, MONO_EXISTS, NOT_EXISTS_THM, NOT_IN_EMPTY,
        NUMPAIR_INJ, PAIR_EQ, .. } := D.core2
  let { SIMPLE_IMAGE, eq_c, le_c, o_DEF, pair_RECURSION, sum_INDUCT, sum_RECURSION, .. } := D.core3
  let { CARD_EQ_IMP_LE, CARD_EQ_REFL, CARD_EQ_REFL_IMP, CARD_EQ_SYM, CARD_LE_TRANS,
        EQ_C_BIJECTIONS, EXISTS_SUM_THM, FORALL_SUM_THM, sum_DISTINCT, sum_INJECTIVE, .. } := BBasics
  let { CARD_EQ_IMAGE, CARD_EQ_TRANS, CARD_LE_ANTISYM, CARD_LE_CARD, CARD_LE_IMAGE_GEN,
        CARD_LE_SUBSET, CARD_LT_LE, INFINITE_CARD_LE, .. } := BOrder
  -- @@SCOPE END

  parse_as_infix ("+_c", (16, "right"))
  parse_as_infix ("*_c", (20, "right"))

  let add_c ← new_definition
   r"s +_c t = {INL x | x IN s} UNION {INR y | y IN t}"

  let mul_c ← new_definition
   r"s *_c t = {(x,y) | x IN s /\ y IN t}"

  -- Congruence properties for the arithmetic operators.

  let CARD_LE_ADD ← prove
   r"!s:A->bool s':B->bool t:C->bool t':D->bool.
      s <=_c s' /\ t <=_c t' ==> s +_c t <=_c s' +_c t'"
   (← do
    let pr ← prove_recursive_functions_exist sum_RECURSION
     (← q r"(!x. h(INL x) = INL((f:A->B) x)) /\ (!y. h(INR y) = INR((g:C->D) y))")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [le_c, add_c] THEN
      DISCH_THEN (CONJUNCTS_THEN2
       (X_CHOOSE_THEN (← q r"f:A->B") STRIP_ASSUME_TAC)
       (X_CHOOSE_THEN (← q r"g:C->D") STRIP_ASSUME_TAC)) THEN
      MP_TAC pr THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"h:(A+C)->(B+D)") THEN STRIP_TAC THEN
      REWRITE_TAC [IN_UNION, IN_ELIM_THM] THEN
      CONJ_TAC THEN REPEAT GEN_TAC THEN
      REPEAT (DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
             ASM_REWRITE_TAC []) THEN
      ASM_REWRITE_TAC [sum_DISTINCT,
                      sum_INJECTIVE] THEN
      ASM_MESON_TAC []))

  let CARD_LE_MUL ← prove
   r"!s:A->bool s':B->bool t:C->bool t':D->bool.
      s <=_c s' /\ t <=_c t' ==> s *_c t <=_c s' *_c t'"
   (REPEAT GEN_TAC THEN REWRITE_TAC [le_c, mul_c] THEN
    DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_THEN (← q r"f:A->B") STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN (← q r"g:C->D") STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC (← q r"\(x,y). (f:A->B) x,(g:C->D) y") THEN
    REWRITE_TAC [FORALL_PAIR_THM, IN_ELIM_THM] THEN
    CONV_TAC (ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC [PAIR_EQ] THEN ASM_MESON_TAC [])

  let CARD_FUNSPACE_LE ← prove
   r"(:A) <=_c (:A') /\ (:B) <=_c (:B') ==> (:A->B) <=_c (:A'->B')"
   (REWRITE_TAC [le_c, IN_UNIV] THEN DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_TAC (← q r"f:A->A'")) (X_CHOOSE_TAC (← q r"g:B->B'"))) THEN
    SUBGOAL_THEN (← q r"?f':A'->A. !x. f'(f x) = x") STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC [← GSYM INJECTIVE_LEFT_INVERSE], ALL_TAC] THEN
    EXISTS_TAC (← q r"\h. (g:B->B') o (h:A->B) o (f':A'->A)") THEN
    ASM_REWRITE_TAC [o_DEF, FUN_EQ_THM] THEN ASM_MESON_TAC [])

  let CARD_ADD_CONG ← prove
   r"!s:A->bool s':B->bool t:C->bool t':D->bool.
      s =_c s' /\ t =_c t' ==> s +_c t =_c s' +_c t'"
   (SIMP_TAC [CARD_LE_ADD, ← GSYM CARD_LE_ANTISYM])

  let CARD_MUL_CONG ← prove
   r"!s:A->bool s':B->bool t:C->bool t':D->bool.
      s =_c s' /\ t =_c t' ==> s *_c t =_c s' *_c t'"
   (SIMP_TAC [CARD_LE_MUL, ← GSYM CARD_LE_ANTISYM])

  let CARD_FUNSPACE_CONG ← prove
   r"(:A) =_c (:A') /\ (:B) =_c (:B') ==> (:A->B) =_c (:A'->B')"
   (SIMP_TAC [← GSYM CARD_LE_ANTISYM, CARD_FUNSPACE_LE])

  -- Misc lemmas.

  let MUL_C_UNIV ← prove
   r"(:A) *_c (:B) = (:A#B)"
   (REWRITE_TAC [EXTENSION, FORALL_PAIR_THM, mul_c, IN_ELIM_PAIR_THM, IN_UNIV])

  let CARD_FUNSPACE_CURRY ← prove
   r"(:A->B->C) =_c (:A#B->C)"
   (REWRITE_TAC [EQ_C_BIJECTIONS] THEN
    EXISTS_TAC (← q r"\(f:A->B->C) (x,y). f x y") THEN
    EXISTS_TAC (← q r"\(g:A#B->C) x y. g(x,y)") THEN
    REWRITE_TAC [IN_UNIV] THEN
    REWRITE_TAC [FUN_EQ_THM, FORALL_PAIR_THM])

  let IN_CARD_ADD ← prove
   r"(!x. INL(x) IN (s +_c t) <=> x IN s) /\
   (!y. INR(y) IN (s +_c t) <=> y IN t)"
   (REWRITE_TAC [add_c, IN_UNION, IN_ELIM_THM] THEN
    REWRITE_TAC [sum_DISTINCT, sum_INJECTIVE] THEN MESON_TAC [])

  let IN_CARD_MUL ← prove
   r"!s t x y. (x,y) IN (s *_c t) <=> x IN s /\ y IN t"
   (REWRITE_TAC [mul_c, IN_ELIM_THM, PAIR_EQ] THEN MESON_TAC [])

  let CARD_LE_SQUARE ← prove
   r"!s:A->bool. s <=_c s *_c s"
   (GEN_TAC THEN REWRITE_TAC [le_c] THEN EXISTS_TAC (← q r"\x:A. x,(@z:A. z IN s)") THEN
    SIMP_TAC [IN_CARD_MUL, PAIR_EQ] THEN
    CONV_TAC (ONCE_DEPTH_CONV SELECT_CONV) THEN MESON_TAC [])

  let CARD_SQUARE_NUM ← prove
   r"(UNIV:num->bool) *_c (UNIV:num->bool) =_c (UNIV:num->bool)"
   (REWRITE_TAC [← GSYM CARD_LE_ANTISYM, CARD_LE_SQUARE] THEN
    REWRITE_TAC [le_c, IN_UNIV, mul_c, IN_ELIM_THM] THEN
    EXISTS_TAC (← q r"\(x,y). NUMPAIR x y") THEN
    REWRITE_TAC [FORALL_PAIR_THM] THEN
    CONV_TAC (ONCE_DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC [NUMPAIR_INJ])

  let UNION_LE_ADD_C ← prove
   r"!s t:A->bool. (s UNION t) <=_c s +_c t"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC CARD_LE_IMAGE_GEN THEN
    EXISTS_TAC (← q r"function INL x -> (x:A) | INR x -> x") THEN
    REWRITE_TAC [add_c, IMAGE_UNION] THEN ONCE_REWRITE_TAC [SIMPLE_IMAGE] THEN
    REWRITE_TAC [← GSYM IMAGE_o, o_DEF] THEN SET_TAC [])

  let CARD_ADD_C ← prove
   r"!s t. FINITE s /\ FINITE t ==> CARD(s +_c t) = CARD s + CARD t"
   (← do
    let s1 ← SET_RULE (← q r"IMAGE f s INTER IMAGE g t = {} <=>
                          !x y. x IN s /\ y IN t ==> ~(f x = g y)")
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [add_c] THEN
      mpPartLhand (fun c => do lhs (← rand c)) CARD_UNION THEN
      ASM_SIMP_TAC [SIMPLE_IMAGE, FINITE_IMAGE] THEN
      REWRITE_TAC [s1] THEN
      REWRITE_TAC [sum_DISTINCT] THEN DISCH_THEN SUBST1_TAC THEN
      BINOP_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
      ASM_SIMP_TAC [sum_INJECTIVE]))

  let CARD_MUL_C ← prove
   r"!s t. FINITE s /\ FINITE t ==> CARD(s *_c t) = CARD s * CARD t"
   (SIMP_TAC [mul_c, ← GSYM CROSS, CARD_CROSS])

  -- Various "arithmetical" lemmas.

  let CARD_ADD_SYM ← prove
   r"!s:A->bool t:B->bool. s +_c t =_c t +_c s"
   (← do
    let pr ← prove_recursive_functions_exist sum_RECURSION
      (← q r"(!x. (h:A+B->B+A) (INL x) = INR x) /\ (!y. h(INR y) = INL y)")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [eq_c] THEN
      MP_TAC pr THEN
      MATCH_MP_TAC MONO_EXISTS THEN
      SIMP_TAC [FORALL_SUM_THM, EXISTS_SUM_THM, EXISTS_UNIQUE_THM] THEN
      REWRITE_TAC [sum_DISTINCT, sum_INJECTIVE, IN_CARD_ADD] THEN MESON_TAC []))

  let CARD_ADD_ASSOC ← prove
   r"!s:A->bool t:B->bool u:C->bool. s +_c (t +_c u) =_c (s +_c t) +_c u"
   (← do
    let pr2 ← prove_recursive_functions_exist sum_RECURSION
      (← q r"(!x. (h:A+B+C->(A+B)+C) (INL x) = INL(INL x)) /\
       (!z. h(INR z) = i(z))")
    let pr1 ← prove_recursive_functions_exist sum_RECURSION
      (← q r"(!u. (i:B+C->(A+B)+C) (INL u) = INL(INR u)) /\
       (!v. i(INR v) = INR v)")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [eq_c] THEN
      CHOOSE_TAC pr1 THEN
      MP_TAC pr2 THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [FORALL_SUM_THM, EXISTS_SUM_THM, EXISTS_UNIQUE_THM,
                      sum_DISTINCT, sum_INJECTIVE, IN_CARD_ADD] THEN
      MESON_TAC []))

  let CARD_MUL_SYM ← prove
   r"!s:A->bool t:B->bool. s *_c t =_c t *_c s"
   (← do
    let pr ← prove_recursive_functions_exist pair_RECURSION
      (← q r"(!x:A y:B. h(x,y) = (y,x))")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [eq_c] THEN
      MP_TAC pr THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
      REWRITE_TAC [EXISTS_UNIQUE_THM, FORALL_PAIR_THM, EXISTS_PAIR_THM] THEN
      ASM_REWRITE_TAC [FORALL_PAIR_THM, IN_CARD_MUL, PAIR_EQ] THEN
      MESON_TAC []))

  let CARD_MUL_ASSOC ← prove
   r"!s:A->bool t:B->bool u:C->bool. s *_c (t *_c u) =_c (s *_c t) *_c u"
   (← do
    let pr2 ← prove_recursive_functions_exist pair_RECURSION
      (← q r"(!x p. (h:A#B#C->(A#B)#C) (x,p) = i x p)")
    let pr1 ← prove_recursive_functions_exist pair_RECURSION
      (← q r"(!x y z. (i:A->B#C->(A#B)#C) x (y,z) = (x,y),z)")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [eq_c] THEN
      CHOOSE_TAC pr1 THEN
      MP_TAC pr2 THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
      REWRITE_TAC [EXISTS_UNIQUE_THM, FORALL_PAIR_THM, EXISTS_PAIR_THM] THEN
      ASM_REWRITE_TAC [FORALL_PAIR_THM, IN_CARD_MUL, PAIR_EQ] THEN
      MESON_TAC []))

  let CARD_LDISTRIB ← prove
   r"!s:A->bool t:B->bool u:C->bool.
        s *_c (t +_c u) =_c (s *_c t) +_c (s *_c u)"
   (← do
    let pr2 ← prove_recursive_functions_exist pair_RECURSION
      (← q r"(!x s. (h:A#(B+C)->(A#B)+(A#C)) (x,s) = i x s)")
    let pr1 ← prove_recursive_functions_exist sum_RECURSION
      (← q r"(!x y. (i:A->(B+C)->A#B+A#C) x (INL y) = INL(x,y)) /\
       (!x z. (i:A->(B+C)->A#B+A#C) x (INR z) = INR(x,z))")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [eq_c] THEN
      CHOOSE_TAC pr1 THEN
      MP_TAC pr2 THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [EXISTS_UNIQUE_THM, FORALL_PAIR_THM, EXISTS_PAIR_THM,
                      FORALL_SUM_THM, EXISTS_SUM_THM, PAIR_EQ, IN_CARD_MUL,
                      sum_DISTINCT, sum_INJECTIVE, IN_CARD_ADD] THEN
      MESON_TAC []))

  let CARD_RDISTRIB ← prove
   r"!s:A->bool t:B->bool u:C->bool.
        (s +_c t) *_c u =_c (s *_c u) +_c (t *_c u)"
   (REPEAT GEN_TAC THEN
    TRANS_TAC CARD_EQ_TRANS
     (← q r"(u:C->bool) *_c ((s:A->bool) +_c (t:B->bool))") THEN
    REWRITE_TAC [CARD_MUL_SYM] THEN
    TRANS_TAC CARD_EQ_TRANS
     (← q r"(u:C->bool) *_c (s:A->bool) +_c (u:C->bool) *_c (t:B->bool)") THEN
    REWRITE_TAC [CARD_LDISTRIB] THEN
    MATCH_MP_TAC CARD_ADD_CONG THEN REWRITE_TAC [CARD_MUL_SYM])

  let CARD_LE_ADDR ← prove
   r"!s:A->bool t:B->bool. s <=_c s +_c t"
   (REPEAT GEN_TAC THEN REWRITE_TAC [le_c] THEN
    EXISTS_TAC (← q r"INL:A->A+B") THEN SIMP_TAC [IN_CARD_ADD, sum_INJECTIVE])

  let CARD_LE_ADDL ← prove
   r"!s:A->bool t:B->bool. t <=_c s +_c t"
   (REPEAT GEN_TAC THEN REWRITE_TAC [le_c] THEN
    EXISTS_TAC (← q r"INR:B->A+B") THEN SIMP_TAC [IN_CARD_ADD, sum_INJECTIVE])

  let CARD_MUL_LID ← prove
   r"!(a:A) (t:B->bool). {a} *_c t =_c t"
   (REPEAT GEN_TAC THEN REWRITE_TAC [EQ_C_BIJECTIONS] THEN
    EXISTS_TAC (← q r"SND:A#B->B") THEN EXISTS_TAC (← q r"\b:B. (a:A,b)") THEN
    REWRITE_TAC [mul_c, FORALL_PAIR_THM, IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC [IN_SING, PAIR_EQ] THEN SET_TAC [])

  let CARD_MUL_RID ← prove
   r"!(s:A->bool) (b:B). s *_c {b} =_c s"
   (REPEAT GEN_TAC THEN REWRITE_TAC [EQ_C_BIJECTIONS] THEN
    EXISTS_TAC (← q r"FST:A#B->A") THEN EXISTS_TAC (← q r"\a:A. (a,(b:B))") THEN
    REWRITE_TAC [mul_c, FORALL_PAIR_THM, IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC [IN_SING, PAIR_EQ] THEN SET_TAC [])

  -- A rather special lemma but temporarily useful.

  let CARD_ADD_LE_MUL_INFINITE ← prove
   r"!s:A->bool. INFINITE s ==> s +_c s <=_c s *_c s"
   (← do
    let nr ← ExceptT.mk (NUM_REDUCE_CONV (← q "1 = 0"))
    let pr ← prove_recursive_functions_exist sum_RECURSION
      (← q r"(!x. h(INL x) = (f(0),x):A#A) /\ (!x. h(INR x) = (f(1),x))")
    pure (GEN_TAC THEN REWRITE_TAC [INFINITE_CARD_LE, le_c, IN_UNIV] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"f:num->A") STRIP_ASSUME_TAC) THEN
      MP_TAC pr THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"h:A+A->A#A") THEN
      STRIP_TAC THEN
      REPEAT ((MATCH_MP_TAC sum_INDUCT THEN
              ASM_REWRITE_TAC [IN_CARD_ADD, IN_CARD_MUL, PAIR_EQ])
             ORELSE STRIP_TAC) THEN
      ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [nr]))

  -- Relate cardinal addition to the simple union operation.

  let CARD_DISJOINT_UNION ← prove
   r"!s:A->bool t. (s INTER t = {}) ==> (s UNION t =_c s +_c t)"
   (← do
    let t ← TAUT (← q r"(if b then x else y) <=> b /\ x \/ ~b /\ y")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN
      STRIP_TAC THEN REWRITE_TAC [eq_c, IN_UNION] THEN
      EXISTS_TAC (← q r"\x:A. if x IN s then INL x else INR x") THEN
      REWRITE_TAC [FORALL_SUM_THM, IN_CARD_ADD] THEN
      REWRITE_TAC [COND_RAND, COND_RATOR] THEN
      REWRITE_TAC [t] THEN
      REWRITE_TAC [sum_DISTINCT, sum_INJECTIVE, IN_CARD_ADD] THEN
      ASM_MESON_TAC []))

  let CARD_LE_EXISTS ← prove
   r"!s:A->bool t:B->bool. s <=_c t <=> ?u:B->bool. t =_c s +_c u"
   (← do
    let ct ← REWRITE_RULE [IMP_CONJ_ALT] CARD_EQ_TRANS
    pure (REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
       [FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [le_c]) THEN
        REWRITE_TAC [INJECTIVE_ON_ALT, LEFT_IMP_EXISTS_THM] THEN
        X_GEN_TAC (← q r"f:A->B") THEN STRIP_TAC THEN
        EXISTS_TAC (← q r"t DIFF IMAGE (f:A->B) s") THEN
        TRANS_TAC CARD_EQ_TRANS (← q r"(IMAGE (f:A->B) s) UNION (t DIFF IMAGE f s)") THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CARD_EQ_REFL_IMP THEN ASM SET_TAC [],
          mpPartLhand (fun c => do lhand (← rand c)) CARD_DISJOINT_UNION THEN
          ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
          MATCH_MP_TAC ct THEN
          MATCH_MP_TAC CARD_ADD_CONG THEN REWRITE_TAC [CARD_EQ_REFL] THEN
          MATCH_MP_TAC CARD_EQ_IMAGE THEN ASM SET_TAC []],
        TRANS_TAC CARD_LE_TRANS (← q r"(s:A->bool) +_c (u:B->bool)") THEN
        REWRITE_TAC [CARD_LE_ADDR] THEN
        MATCH_MP_TAC CARD_EQ_IMP_LE THEN ONCE_REWRITE_TAC [CARD_EQ_SYM] THEN
        ASM_REWRITE_TAC []]))

  let CARD_LT_IMP_SUC_LE ← prove
   r"!s:A->bool t:B->bool a:C. s <_c t ==> s +_c {a} <=_c t"
   (← do
    let lt ← REWRITE_RULE [IMP_CONJ_ALT] CARD_LE_TRANS
    let s1 ← SET_RULE (← q r"~(b IN IMAGE f s) <=> !x. x IN s ==> ~(f x = b)")
    pure (REWRITE_TAC [CARD_LT_LE] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [le_c]) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"f:A->B") STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN (← q r"?b. b IN t DIFF IMAGE (f:A->B) s") MP_TAC THENL
       [FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [eq_c]) THEN
        REWRITE_TAC [NOT_EXISTS_THM, LEFT_IMP_FORALL_THM] THEN
        EXISTS_TAC (← q r"f:A->B") THEN ASM SET_TAC [],
        REWRITE_TAC [IN_DIFF, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q "b:B") THEN
        SIMP_TAC [s1] THEN
        STRIP_TAC THEN TRANS_TAC CARD_LE_TRANS (← q r"IMAGE (f:A->B) s +_c {b:B}") THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CARD_LE_ADD THEN
          SIMP_TAC [CARD_LE_CARD, FINITE_SING, CARD_SING, LE_REFL] THEN
          MATCH_MP_TAC CARD_EQ_IMP_LE THEN ONCE_REWRITE_TAC [CARD_EQ_SYM] THEN
          MATCH_MP_TAC CARD_EQ_IMAGE THEN ASM SET_TAC [],
          mpPartLhand (fun c => do rand (← rand c)) CARD_DISJOINT_UNION THEN
          ANTS_TAC THENL [ASM SET_TAC [], ONCE_REWRITE_TAC [CARD_EQ_SYM]] THEN
          DISCH_THEN (MP_TAC o MATCH_MP CARD_EQ_IMP_LE) THEN
          MATCH_MP_TAC lt THEN
          MATCH_MP_TAC CARD_LE_SUBSET THEN ASM SET_TAC []]]))

  -- @@RETURN BEGIN
  return { add_c, mul_c, CARD_LE_ADD, CARD_LE_MUL, CARD_FUNSPACE_LE, CARD_ADD_CONG,
           CARD_MUL_CONG, CARD_FUNSPACE_CONG, MUL_C_UNIV, CARD_FUNSPACE_CURRY,
           IN_CARD_ADD, IN_CARD_MUL, CARD_LE_SQUARE, CARD_SQUARE_NUM, UNION_LE_ADD_C,
           CARD_ADD_C, CARD_MUL_C, CARD_ADD_SYM, CARD_ADD_ASSOC, CARD_MUL_SYM,
           CARD_MUL_ASSOC, CARD_LDISTRIB, CARD_RDISTRIB, CARD_LE_ADDR, CARD_LE_ADDL,
           CARD_MUL_LID, CARD_MUL_RID, CARD_ADD_LE_MUL_INFINITE, CARD_DISJOINT_UNION,
           CARD_LE_EXISTS, CARD_LT_IMP_SUC_LE }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- The key to arithmetic on infinite cardinals: k^2 = k; preservation of     -/
/- finiteness; the "absorption laws".  (card.ml 934-1238)                    -/
/- ------------------------------------------------------------------------- -/

structure Square where
  -- @@FIELDS
  CARD_SQUARE_INFINITE : thm
  CARD_ADD_FINITE : thm
  CARD_ADD_FINITE_EQ : thm
  CARD_MUL_FINITE : thm
  CARD_MUL_FINITE_EQ : thm
  CARD_MUL_ABSORB_LE : thm
  CARD_MUL2_ABSORB_LE : thm
  CARD_MUL2_ABSORB_LE_ALT : thm
  CARD_ADD_ABSORB_LE : thm
  CARD_ADD2_ABSORB_LE : thm
  CARD_MUL_ABSORB : thm
  CARD_ADD_ABSORB_LEFT : thm
  CARD_ADD_ABSORB_RIGHT : thm
  CARD_UNION_ABSORB_LEFT : thm
  CARD_UNION_ABSORB_RIGHT : thm
  CARD_ADD2_ABSORB_LT : thm
  CARD_DIFF_ABSORB : thm
  deriving Inhabited

@[nospecialize]
def setupSquare [HolBase] (D : CardDeps) (BBasics : Basics) (BOrder : Order) (BArith : Arith) (AZorn : HolLibrary.Wo.Zorn) :
    ExceptT String IO Square := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, .. } := D
  let { CONTRAPOS_THM, CROSS, DE_MORGAN_THM, EXISTS_PAIR_THM, EXISTS_UNIQUE_THM,
        EXTENSION, FINITE_CROSS_EQ, FINITE_IMAGE, FINITE_PRODUCT, FINITE_RULES,
        FINITE_SUBSET, FINITE_UNION, FORALL_AND_THM, FORALL_PAIR_THM, FUN_EQ_THM,
        IMP_CONJ_ALT, IN, .. } := D.core1
  let { INFINITE, IN_DIFF, IN_ELIM_THM, IN_INTER, IN_UNION, MEMBER_NOT_EMPTY,
        MONO_EXISTS, NOT_FORALL_THM, NOT_IMP, NOT_IN_EMPTY, PAIR_EQ, .. } := D.core2
  let { RIGHT_EXISTS_AND_THM, SIMPLE_IMAGE, SUBSET, SUBSET_DIFF, SUBSET_UNION,
        SWAP_EXISTS_THM, UNIONS, UNION_COMM, UNWIND_THM2, le_c, num_INFINITE, .. } := D.core3
  let { CARD_EQ_IMP_LE, CARD_EQ_REFL, CARD_EQ_SYM, CARD_LET_TRANS, CARD_LE_REFL,
        CARD_LE_TRANS, EQ_C, .. } := BBasics
  let { CARD_EQ_TRANS, CARD_INFINITE_CONG, CARD_LE_ANTISYM, CARD_LE_EQ_SUBSET,
        CARD_LE_FINITE, CARD_LE_INFINITE, CARD_LE_SUBSET, CARD_LE_TOTAL,
        CARD_LT_FINITE_INFINITE, CARD_NOT_LE, CARD_NOT_LT, INFINITE_CARD_LE, .. } := BOrder
  let { CARD_ADD_CONG, CARD_ADD_LE_MUL_INFINITE, CARD_ADD_SYM, CARD_DISJOINT_UNION,
        CARD_LE_ADD, CARD_LE_ADDL, CARD_LE_ADDR, CARD_LE_MUL, CARD_LE_SQUARE,
        CARD_MUL_CONG, CARD_SQUARE_NUM, IN_CARD_MUL, UNION_LE_ADD_C, add_c, mul_c, .. } := BArith
  let { ZL_SUBSETS_UNIONS_NONEMPTY, .. } := AZorn
  -- @@SCOPE END

  let CARD_SQUARE_INFINITE ← prove
   r"!k:A->bool. INFINITE k ==> (k *_c k =_c k)"
   (← do
    let lemma ← prove
     r"INFINITE(s:A->bool) /\ s SUBSET k /\
       (!x y. R(x,y) ==> x IN (s *_c s) /\ y IN s) /\
       (!x. x IN (s *_c s) ==> ?!y. y IN s /\ R(x,y)) /\
       (!y:A. y IN s ==> ?!x. x IN (s *_c s) /\ R(x,y))
       ==> (s = {z | ?p. R(p,z)})"
     (REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN MESON_TAC [])
    -- Built when OCaml builds the tactic, last first.
    let aad ← ASSUME (← q r"a:A IN d")
    let fs ← ONCE_REWRITE_RULE [← TAUT (← q r"a /\ b ==> c <=> b ==> a ==> c")]
                      FINITE_SUBSET
    let t3 ← TAUT
     (← q r"(c /\ d ==> f) /\ (a /\ b ==> e)
      ==> (a /\ (b /\ c) /\ d ==> e /\ f)")
    let t2 ← TAUT (← q r"a ==> b /\ c <=> (a ==> b) /\ (a ==> c)")
    let t1 ← MATCH_MP (← TAUT (← q r"(a ==> b) ==> (a <=> b /\ a)")) lemma
    pure (REPEAT STRIP_TAC THEN
      ABBREV_TAC
        (← q r"P = \R. ?s. INFINITE(s:A->bool) /\ s SUBSET k /\
                     (!x y. R(x,y) ==> x IN (s *_c s) /\ y IN s) /\
                     (!x. x IN (s *_c s) ==> ?!y. y IN s /\ R(x,y)) /\
                     (!y. y IN s ==> ?!x. x IN (s *_c s) /\ R(x,y))") THEN
      MP_TAC (← ISPEC (← q r"P:((A#A)#A->bool)->bool") ZL_SUBSETS_UNIONS_NONEMPTY) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN REWRITE_TAC [] THEN
          ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
          REWRITE_TAC [RIGHT_EXISTS_AND_THM, ← GSYM EQ_C] THEN
          FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [INFINITE_CARD_LE]) THEN
          REWRITE_TAC [CARD_LE_EQ_SUBSET] THEN
          MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"s:A->bool") THEN
          STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
           [ASM_MESON_TAC [num_INFINITE, CARD_INFINITE_CONG], ALL_TAC] THEN
          FIRST_ASSUM (fun th => tactic_of do
           pure (MP_TAC (← MATCH_MP CARD_MUL_CONG (← CONJ th th)))) THEN
          GEN_REWRITE_TAC LAND_CONV [CARD_EQ_SYM] THEN
          DISCH_THEN (MP_TAC o (fun th => CONJ th CARD_SQUARE_NUM)) THEN
          DISCH_THEN (MP_TAC o MATCH_MP CARD_EQ_TRANS) THEN
          FIRST_ASSUM (fun th =>
            DISCH_THEN (ACCEPT_TAC o MATCH_MP CARD_EQ_TRANS o (fun a => CONJ a th))),
          ALL_TAC] THEN
        SUBGOAL_THEN
         (← q r"P = \R. INFINITE {z | ?x y. R((x,y),z)} /\
                  (!x:A y z. R((x,y),z) ==> x IN k /\ y IN k /\ z IN k) /\
                  (!x y. (?u v. R((u,v),x)) /\ (?u v. R((u,v),y))
                         ==> ?z. R((x,y),z)) /\
                  (!x y. (?z. R((x,y),z))
                         ==> (?u v. R((u,v),x)) /\ (?u v. R((u,v),y))) /\
                  (!x y z1 z2. R((x,y),z1) /\ R((x,y),z2) ==> (z1 = z2)) /\
                  (!x1 y1 x2 y2 z. R((x1,y1),z) /\ R((x2,y2),z)
                                   ==> (x1 = x2) /\ (y1 = y2))")
        SUBST1_TAC THENL
         [FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN REWRITE_TAC [] THEN
          ONCE_REWRITE_TAC [t1] THEN
          REWRITE_TAC [UNWIND_THM2] THEN REWRITE_TAC [FUN_EQ_THM] THEN
          REWRITE_TAC [IN_CARD_MUL, EXISTS_PAIR_THM, SUBSET, FUN_EQ_THM,
                      IN_ELIM_THM, FORALL_PAIR_THM, EXISTS_UNIQUE_THM,
                      UNIONS, PAIR_EQ] THEN
          GEN_TAC THEN AP_TERM_TAC THEN MESON_TAC [],
          ALL_TAC] THEN
        FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o SYM) THEN REWRITE_TAC [] THEN GEN_TAC THEN
        GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [t2] THEN
        GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [FORALL_AND_THM] THEN
        MATCH_MP_TAC t3 THEN
        CONJ_TAC THENL
         [REWRITE_TAC [UNIONS, IN_ELIM_THM] THEN
          REWRITE_TAC [SUBSET, IN] THEN MESON_TAC [],
          ALL_TAC] THEN
        DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q r"s:(A#A)#A->bool")) MP_TAC) THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"s:(A#A)#A->bool")) THEN
        ASM_REWRITE_TAC [INFINITE, CONTRAPOS_THM] THEN
        MATCH_MP_TAC fs THEN
        REWRITE_TAC [SUBSET, IN_ELIM_THM, UNIONS] THEN ASM_MESON_TAC [IN],
        ALL_TAC] THEN
      FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"R:(A#A)#A->bool")
       (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q r"s:A->bool")) ASSUME_TAC)) THEN
      SUBGOAL_THEN (← q r"(s:A->bool) *_c s =_c s") ASSUME_TAC THENL
       [REWRITE_TAC [EQ_C] THEN EXISTS_TAC (← q r"R:(A#A)#A->bool") THEN ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"s +_c s <=_c (s:A->bool)") ASSUME_TAC THENL
       [TRANS_TAC CARD_LE_TRANS (← q r"(s:A->bool) *_c s") THEN
        ASM_SIMP_TAC [CARD_EQ_IMP_LE, CARD_ADD_LE_MUL_INFINITE],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"(s:A->bool) INTER (k DIFF s) = {}") ASSUME_TAC THENL
       [REWRITE_TAC [EXTENSION, IN_INTER, IN_DIFF, NOT_IN_EMPTY] THEN MESON_TAC [],
        ALL_TAC] THEN
      DISJ_CASES_TAC (← ISPECL [← q r"k DIFF (s:A->bool)", ← q r"s:A->bool"] CARD_LE_TOTAL)
      THENL
       [SUBGOAL_THEN (← q r"k = (s:A->bool) UNION (k DIFF s)") SUBST1_TAC THENL
         [FIRST_ASSUM (MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
          REWRITE_TAC [SUBSET, EXTENSION, IN_INTER, NOT_IN_EMPTY,
                      IN_UNION, IN_DIFF] THEN
          MESON_TAC [],
          ALL_TAC] THEN
        REWRITE_TAC [← GSYM CARD_LE_ANTISYM, CARD_LE_SQUARE] THEN
        TRANS_TAC CARD_LE_TRANS
         (← q r"((s:A->bool) +_c (k DIFF s:A->bool)) *_c (s +_c k DIFF s)") THEN
        ASM_SIMP_TAC [CARD_DISJOINT_UNION, CARD_EQ_IMP_LE, CARD_MUL_CONG] THEN
        TRANS_TAC CARD_LE_TRANS (← q r"((s:A->bool) +_c s) *_c (s +_c s)") THEN
        ASM_SIMP_TAC [CARD_LE_ADD, CARD_LE_MUL, CARD_LE_REFL] THEN
        TRANS_TAC CARD_LE_TRANS (← q r"(s:A->bool) *_c s") THEN
        ASM_SIMP_TAC [CARD_LE_MUL] THEN
        TRANS_TAC CARD_LE_TRANS (← q r"s:A->bool") THEN ASM_SIMP_TAC [CARD_EQ_IMP_LE] THEN
        REWRITE_TAC [CARD_LE_EQ_SUBSET] THEN EXISTS_TAC (← q r"s:A->bool") THEN
        SIMP_TAC [CARD_EQ_REFL, SUBSET, IN_UNION],
        ALL_TAC] THEN
      UNDISCH_TAC (← q r"s:A->bool <=_c k DIFF s") THEN
      REWRITE_TAC [CARD_LE_EQ_SUBSET] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"d:A->bool") STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN (← q r"(s:A->bool *_c d) UNION (d *_c s) UNION (d *_c d) =_c d")
      MP_TAC THENL
       [TRANS_TAC CARD_EQ_TRANS
           (← q r"((s:A->bool) *_c (d:A->bool)) +_c ((d *_c s) +_c (d *_c d))") THEN
        CONJ_TAC THENL
         [TRANS_TAC CARD_EQ_TRANS
           (← q r"((s:A->bool) *_c d) +_c ((d *_c s) UNION (d *_c d))") THEN
          CONJ_TAC THENL
           [ALL_TAC,
            MATCH_MP_TAC CARD_ADD_CONG THEN REWRITE_TAC [CARD_EQ_REFL]] THEN
          MATCH_MP_TAC CARD_DISJOINT_UNION THEN
          UNDISCH_TAC (← q r"s INTER (k DIFF s:A->bool) = {}") THEN
          UNDISCH_TAC (← q r"d SUBSET (k DIFF s:A->bool)") THEN
          REWRITE_TAC [EXTENSION, SUBSET, FORALL_PAIR_THM, NOT_IN_EMPTY,
                      IN_INTER, IN_UNION, IN_CARD_MUL, IN_DIFF] THEN MESON_TAC [],
          ALL_TAC] THEN
        TRANS_TAC CARD_EQ_TRANS (← q r"s:A->bool") THEN ASM_REWRITE_TAC [] THEN
        TRANS_TAC CARD_EQ_TRANS
          (← q r"(s:A->bool *_c s) +_c (s *_c s) +_c (s *_c s)") THEN
        CONJ_TAC THENL
         [REPEAT (MATCH_MP_TAC CARD_ADD_CONG THEN CONJ_TAC) THEN
          MATCH_MP_TAC CARD_MUL_CONG THEN ASM_REWRITE_TAC [CARD_EQ_REFL] THEN
          ONCE_REWRITE_TAC [CARD_EQ_SYM] THEN ASM_REWRITE_TAC [],
          ALL_TAC] THEN
        TRANS_TAC CARD_EQ_TRANS (← q r"(s:A->bool) +_c s +_c s") THEN CONJ_TAC THENL
         [REPEAT (MATCH_MP_TAC CARD_ADD_CONG THEN ASM_REWRITE_TAC []),
          ALL_TAC] THEN
        REWRITE_TAC [← GSYM CARD_LE_ANTISYM, CARD_LE_ADDR] THEN
        TRANS_TAC CARD_LE_TRANS (← q r"(s:A->bool) +_c s") THEN
        ASM_SIMP_TAC [CARD_LE_ADD, CARD_LE_REFL],
        ALL_TAC] THEN
      FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC) THEN
      FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC) THEN
      REWRITE_TAC [EQ_C, IN_UNION] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"S:(A#A)#A->bool")) THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"\x:(A#A)#A. R(x) \/ S(x)")) THEN
      ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN DISCH_THEN (fun _ => ALL_TAC) THEN
      REWRITE_TAC [NOT_IMP] THEN REPEAT CONJ_TAC THENL
       [EXISTS_TAC (← q r"(s:A->bool) UNION d"),
        SIMP_TAC [SUBSET, IN],
        SUBGOAL_THEN (← q r"~(d:A->bool = {})") MP_TAC THENL
         [DISCH_THEN (MP_TAC o AP_TERM (← q r"FINITE:(A->bool)->bool")) THEN
          REWRITE_TAC [FINITE_RULES, ← GSYM INFINITE] THEN
          ASM_MESON_TAC [CARD_INFINITE_CONG],
          ALL_TAC] THEN
        REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN (X_CHOOSE_TAC (← q "a:A")) THEN
        FIRST_ASSUM (MP_TAC o (fun a => MATCH_MP a aad) o
          (fun (th : thm) => lastThm (CONJUNCTS th))) THEN
        DISCH_THEN (MP_TAC o EXISTENCE) THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"b:A#A") (CONJUNCTS_THEN ASSUME_TAC)) THEN
        REWRITE_TAC [EXTENSION, NOT_FORALL_THM] THEN
        EXISTS_TAC (← q r"(b:A#A,a:A)") THEN ASM_REWRITE_TAC [IN] THEN
        DISCH_THEN (fun th => FIRST_ASSUM
         (MP_TAC o CONJUNCT2 o (fun a => MATCH_MP a th) o CONJUNCT1)) THEN
        MAP_EVERY UNDISCH_TAC
         [← q r"a:A IN d", ← q r"(d:A->bool) SUBSET (k DIFF s)"] THEN
        REWRITE_TAC [SUBSET, IN_DIFF] THEN MESON_TAC []] THEN
      REWRITE_TAC [INFINITE, FINITE_UNION, DE_MORGAN_THM] THEN
      ASM_REWRITE_TAC [← GSYM INFINITE] THEN CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [← q r"(d:A->bool) SUBSET (k DIFF s)", ← q r"(s:A->bool) SUBSET k"] THEN
        REWRITE_TAC [SUBSET, IN_UNION, IN_DIFF] THEN MESON_TAC [],
        ALL_TAC] THEN
      REPEAT (FIRST_ASSUM (undischCheck (fun c => pure (is_conj c)))) THEN
      REWRITE_TAC [FORALL_PAIR_THM, EXISTS_UNIQUE_THM, EXISTS_PAIR_THM,
                  IN_CARD_MUL, IN_UNION, PAIR_EQ] THEN
      MAP_EVERY UNDISCH_TAC
       [← q r"(s:A->bool) SUBSET k",
        ← q r"(d:A->bool) SUBSET (k DIFF s)"] THEN
      REWRITE_TAC [SUBSET, EXTENSION, NOT_IN_EMPTY, IN_INTER, IN_DIFF] THEN
      POP_ASSUM_LIST (fun _ => ALL_TAC) THEN
      REPEAT DISCH_TAC THEN REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC [], ASM_MESON_TAC [], ALL_TAC] THEN
      GEN_TAC THEN DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN
      DISCH_THEN (fun th => CONJ_TAC THEN MP_TAC th) THENL
       [ALL_TAC, ASM_MESON_TAC []] THEN
      DISCH_THEN (fun th =>
       FIRST_ASSUM (MP_TAC o (fun a => MATCH_MP a th) o
         (fun (th : thm) => lastThm (CONJUNCTS th)))) THEN
      MESON_TAC []))

  -- Preservation of finiteness.

  let CARD_ADD_FINITE ← prove
   r"!s t. FINITE s /\ FINITE t ==> FINITE(s +_c t)"
   (SIMP_TAC [add_c, FINITE_UNION, SIMPLE_IMAGE, FINITE_IMAGE])

  let CARD_ADD_FINITE_EQ ← prove
   r"!s:A->bool t:B->bool. FINITE(s +_c t) <=> FINITE s /\ FINITE t"
   (REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC [CARD_ADD_FINITE] THEN
    DISCH_THEN (fun th => CONJ_TAC THEN MP_TAC th) THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] CARD_LE_FINITE) THEN
    REWRITE_TAC [CARD_LE_ADDL, CARD_LE_ADDR])

  let CARD_MUL_FINITE ← prove
   r"!s t. FINITE s /\ FINITE t ==> FINITE(s *_c t)"
   (SIMP_TAC [mul_c, FINITE_PRODUCT])

  let CARD_MUL_FINITE_EQ ← prove
   r"!s:A->bool t:B->bool.
        FINITE(s *_c t) <=> s = {} \/ t = {} \/ FINITE s /\ FINITE t"
   (REWRITE_TAC [mul_c, ← GSYM CROSS, FINITE_CROSS_EQ])

  -- Hence the "absorption laws" for arithmetic with an infinite cardinal.

  let CARD_MUL_ABSORB_LE ← prove
   r"!s:A->bool t:B->bool. INFINITE(t) /\ s <=_c t ==> s *_c t <=_c t"
   (REPEAT STRIP_TAC THEN
    TRANS_TAC CARD_LE_TRANS (← q r"(t:B->bool) *_c t") THEN
    ASM_SIMP_TAC [CARD_LE_MUL, CARD_LE_REFL,
                 CARD_SQUARE_INFINITE, CARD_EQ_IMP_LE])

  let CARD_MUL2_ABSORB_LE ← prove
   r"!s:A->bool t:B->bool u:C->bool.
     INFINITE(u) /\ s <=_c u /\ t <=_c u ==> s *_c t <=_c u"
   (REPEAT STRIP_TAC THEN
    TRANS_TAC CARD_LE_TRANS (← q r"(s:A->bool) *_c (u:C->bool)") THEN
    ASM_SIMP_TAC [CARD_MUL_ABSORB_LE] THEN MATCH_MP_TAC CARD_LE_MUL THEN
    ASM_REWRITE_TAC [CARD_LE_REFL])

  let CARD_MUL2_ABSORB_LE_ALT ← prove
   r"!(s:A->bool) (t:B->bool) (u:C->bool).
        (INFINITE s \/ INFINITE t) /\ s <=_c u /\ t <=_c u
        ==> s *_c t <=_c u"
   (MESON_TAC [CARD_LE_INFINITE, CARD_MUL2_ABSORB_LE])

  let CARD_ADD_ABSORB_LE ← prove
   r"!s:A->bool t:B->bool. INFINITE(t) /\ s <=_c t ==> s +_c t <=_c t"
   (REPEAT STRIP_TAC THEN
    TRANS_TAC CARD_LE_TRANS (← q r"(t:B->bool) *_c t") THEN
    ASM_SIMP_TAC [CARD_SQUARE_INFINITE, CARD_EQ_IMP_LE] THEN
    TRANS_TAC CARD_LE_TRANS (← q r"(t:B->bool) +_c t") THEN
    ASM_SIMP_TAC [CARD_ADD_LE_MUL_INFINITE, CARD_LE_ADD, CARD_LE_REFL])

  let CARD_ADD2_ABSORB_LE ← prove
   r"!s:A->bool t:B->bool u:C->bool.
     INFINITE(u) /\ s <=_c u /\ t <=_c u ==> s +_c t <=_c u"
   (REPEAT STRIP_TAC THEN
    TRANS_TAC CARD_LE_TRANS (← q r"(s:A->bool) +_c (u:C->bool)") THEN
    ASM_SIMP_TAC [CARD_ADD_ABSORB_LE] THEN MATCH_MP_TAC CARD_LE_ADD THEN
    ASM_REWRITE_TAC [CARD_LE_REFL])

  let CARD_MUL_ABSORB ← prove
   r"!s:A->bool t:B->bool.
     INFINITE(t) /\ ~(s = {}) /\ s <=_c t ==> s *_c t =_c t"
   (SIMP_TAC [← GSYM CARD_LE_ANTISYM, CARD_MUL_ABSORB_LE] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (X_CHOOSE_TAC (← q "a:A") o
     GEN_REWRITE_RULE id [← GSYM MEMBER_NOT_EMPTY]) THEN
    REWRITE_TAC [le_c] THEN EXISTS_TAC (← q r"\x:B. (a:A,x)") THEN
    ASM_SIMP_TAC [IN_CARD_MUL, PAIR_EQ])

  let CARD_ADD_ABSORB_LEFT ← prove
   r"!s:A->bool t:B->bool. INFINITE(t) /\ s <=_c t ==> s +_c t =_c t"
   (SIMP_TAC [← GSYM CARD_LE_ANTISYM, CARD_LE_ADDL, CARD_ADD_ABSORB_LE])

  let CARD_ADD_ABSORB_RIGHT ← prove
   r"!s:A->bool t:B->bool. INFINITE(s) /\ t <=_c s ==> s +_c t =_c s"
   (REPEAT STRIP_TAC THEN
    TRANS_TAC CARD_EQ_TRANS (← q r"(t:B->bool) +_c (s:A->bool)") THEN
    ASM_SIMP_TAC [CARD_ADD_ABSORB_LEFT, CARD_ADD_SYM])

  let CARD_UNION_ABSORB_LEFT ← prove
   r"!s t:A->bool. INFINITE(t) /\ s <=_c t ==> s UNION t =_c t"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM CARD_LE_ANTISYM] THEN
    SIMP_TAC [CARD_LE_SUBSET, SUBSET_UNION] THEN
    TRANS_TAC CARD_LE_TRANS (← q r"(s:A->bool) +_c (t:A->bool)") THEN
    REWRITE_TAC [UNION_LE_ADD_C] THEN MATCH_MP_TAC CARD_EQ_IMP_LE THEN
    ASM_SIMP_TAC [CARD_ADD_ABSORB_LEFT])

  let CARD_UNION_ABSORB_RIGHT ← prove
   r"!s t:A->bool. INFINITE(s) /\ t <=_c s ==> s UNION t =_c s"
   (ONCE_REWRITE_TAC [UNION_COMM] THEN REWRITE_TAC [CARD_UNION_ABSORB_LEFT])

  let CARD_ADD2_ABSORB_LT ← prove
   r"!s:A->bool t:B->bool u:C->bool.
        INFINITE u /\ s <_c u /\ t <_c u ==> s +_c t <_c u"
   (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"FINITE((s:A->bool) +_c (t:B->bool))") THEN
    ASM_SIMP_TAC [CARD_LT_FINITE_INFINITE] THEN
    DISJ_CASES_TAC (← ISPECL [← q r"s:A->bool", ← q r"t:B->bool"] CARD_LE_TOTAL) THENL
     [ASM_CASES_TAC (← q r"FINITE(t:B->bool)") THENL
       [ASM_MESON_TAC [CARD_LE_FINITE, CARD_ADD_FINITE],
        TRANS_TAC CARD_LET_TRANS (← q r"t:B->bool")],
      ASM_CASES_TAC (← q r"FINITE(s:A->bool)") THENL
       [ASM_MESON_TAC [CARD_LE_FINITE, CARD_ADD_FINITE],
        TRANS_TAC CARD_LET_TRANS (← q r"s:A->bool")]] THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC CARD_ADD2_ABSORB_LE THEN
    ASM_REWRITE_TAC [INFINITE, CARD_LE_REFL])

  let CARD_DIFF_ABSORB ← prove
   r"!s t:A->bool. INFINITE s /\ t <_c s ==> s DIFF t =_c s"
   (← do
    let s1 ← SET_RULE (← q r"s SUBSET (s DIFF t) UNION t:A->bool")
    pure (SIMP_TAC [← GSYM CARD_LE_ANTISYM, CARD_LE_SUBSET, SUBSET_DIFF] THEN
      REWRITE_TAC [← GSYM CARD_NOT_LT] THEN REPEAT STRIP_TAC THEN
      MP_TAC s1 THEN
      DISCH_THEN (MP_TAC o MATCH_MP CARD_LE_SUBSET) THEN
      REWRITE_TAC [CARD_NOT_LE] THEN
      TRANS_TAC CARD_LET_TRANS (← q r"(s DIFF t:A->bool) +_c t") THEN
      ASM_SIMP_TAC [UNION_LE_ADD_C, CARD_ADD2_ABSORB_LT]))

  -- @@RETURN BEGIN
  return { CARD_SQUARE_INFINITE, CARD_ADD_FINITE, CARD_ADD_FINITE_EQ, CARD_MUL_FINITE,
           CARD_MUL_FINITE_EQ, CARD_MUL_ABSORB_LE, CARD_MUL2_ABSORB_LE,
           CARD_MUL2_ABSORB_LE_ALT, CARD_ADD_ABSORB_LE, CARD_ADD2_ABSORB_LE,
           CARD_MUL_ABSORB, CARD_ADD_ABSORB_LEFT, CARD_ADD_ABSORB_RIGHT,
           CARD_UNION_ABSORB_LEFT, CARD_UNION_ABSORB_RIGHT, CARD_ADD2_ABSORB_LT,
           CARD_DIFF_ABSORB }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Strict monotonicity and cancellation of addition; unions; differences;    -/
/- bijections of disjoint pieces and subsets; ad-hoc product lemmas.         -/
/- (card.ml 1246-1528)                                                       -/
/- ------------------------------------------------------------------------- -/

structure Cancel where
  -- @@FIELDS
  CARD_LT_ADD : thm
  CARD_LE_ADD_LCANCEL : thm
  CARD_LE_ADD_LCANCEL_EQ : thm
  CARD_LE_ADD_RCANCEL : thm
  CARD_LE_ADD_RCANCEL_EQ : thm
  CARD_EQ_ADD_LCANCEL : thm
  CARD_EQ_ADD_LCANCEL_EQ : thm
  CARD_EQ_ADD_RCANCEL : thm
  CARD_EQ_ADD_RCANCEL_EQ : thm
  CARD_LE_UNIONS2 : thm
  CARD_LE_UNIONS : thm
  CARD_LE_DISJOINT_UNIONS : thm
  CARD_EQ_DISJOINT_UNIONS : thm
  CARD_EQ_IMAGE_MUL_FIBRES : thm
  CARD_DIFF_CONG : thm
  EQ_C_BIJECTIONS_DISJOINT : thm
  EQ_C_BIJECTIONS_SUBSETS : thm
  EQ_C_BIJECTIONS_SUBSETS_LT : thm
  EQ_C_BIJECTIONS_EXTEND : thm
  EQ_C_INVOLUTION : thm
  CARD_MUL_LT_LEMMA : thm
  CARD_MUL_LT_INFINITE : thm
  deriving Inhabited

@[nospecialize]
def setupCancel [HolBase] (D : CardDeps) (BBasics : Basics) (BOrder : Order) (BArith : Arith) (BSquare : Square) :
    ExceptT String IO Cancel := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, .. } := D
  let { CARD_DIFF, CONJ_ASSOC, CONTRAPOS_THM, EQ_IMP, EXISTS_IN_IMAGE, EXISTS_PAIR_THM,
        EXISTS_UNIQUE_THM, FINITE_DIFF, FINITE_SUBSET, FORALL_IN_IMAGE,
        FORALL_PAIR_THM, IMP_CONJ, IMP_CONJ_ALT, .. } := D.core1
  let { INFINITE, IN_ELIM_PAIR_THM, IN_ELIM_THM, IN_IMAGE, IN_UNIONS,
        LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM, LE_ADD_LCANCEL, MONO_AND,
        MONO_EXISTS, PAIR_EQ, .. } := D.core2
  let { RIGHT_AND_EXISTS_THM, RIGHT_EXISTS_AND_THM, RIGHT_FORALL_IMP_THM,
        RIGHT_IMP_EXISTS_THM, SKOLEM_THM, SUBSET, SURJECTIVE_ON_RIGHT_INVERSE, eq_c,
        le_c, pairwise, .. } := D.core3
  let { CARD_EQ_IMP_LE, CARD_EQ_SYM, CARD_LET_TRANS, CARD_LE_REFL, CARD_LE_TRANS,
        CARD_LTE_TRANS, CARD_LT_IMP_LE, EQ_C_BIJECTIONS, .. } := BBasics
  let { CARD_EQ_CARD, CARD_EQ_TRANS, CARD_FINITE_CONG, CARD_INFINITE_CONG,
        CARD_LE_ANTISYM, CARD_LE_CARD, CARD_LE_CONG, CARD_LE_FINITE,
        CARD_LE_FINITE_INFINITE, CARD_LE_IMAGE, CARD_LE_SUBSET, CARD_LE_TOTAL,
        CARD_LT_CARD, CARD_LT_CONG, CARD_NOT_LE, CARD_NOT_LT, LE_C_IMAGE_SUBSET, .. } := BOrder
  let { CARD_ADD_C, CARD_ADD_SYM, CARD_LE_ADD, CARD_LE_ADDL, CARD_LE_ADDR,
        CARD_MUL_SYM, IN_CARD_MUL, mul_c, .. } := BArith
  let { CARD_ADD2_ABSORB_LT, CARD_ADD_ABSORB_LEFT, CARD_ADD_FINITE, CARD_ADD_FINITE_EQ,
        CARD_DIFF_ABSORB, CARD_MUL_ABSORB_LE, CARD_MUL_FINITE, CARD_SQUARE_INFINITE, .. } := BSquare
  -- @@SCOPE END

  let CARD_LT_ADD ← prove
   r"!s:A->bool s':B->bool t:C->bool t':D->bool.
        s <_c s' /\ t <_c t' ==> s +_c t <_c s' +_c t'"
   (← do
    let lf ← REWRITE_RULE [IMP_CONJ_ALT] CARD_LE_FINITE
    pure (REPEAT STRIP_TAC THEN
      ASM_CASES_TAC (← q r"FINITE((s':B->bool) +_c (t':D->bool))") THENL
       [FIRST_X_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE id
          [CARD_ADD_FINITE_EQ]) THEN
        SUBGOAL_THEN (← q r"FINITE(s:A->bool) /\ FINITE(t:C->bool)")
        STRIP_ASSUME_TAC THENL
         [CONJ_TAC THEN FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP lf o
            MATCH_MP CARD_LT_IMP_LE) THEN
          ASM_REWRITE_TAC [],
          MAP_EVERY UNDISCH_TAC
           [← q r"(s:A->bool) <_c (s':B->bool)",
            ← q r"(t:C->bool) <_c (t':D->bool)"] THEN
          ASM_SIMP_TAC [CARD_LT_CARD, CARD_ADD_FINITE, CARD_ADD_C] THEN
          ARITH_TAC],
        MATCH_MP_TAC CARD_ADD2_ABSORB_LT THEN ASM_REWRITE_TAC [INFINITE] THEN
        CONJ_TAC THENL
         [TRANS_TAC CARD_LTE_TRANS (← q r"s':B->bool") THEN
          ASM_REWRITE_TAC [CARD_LE_ADDR],
          TRANS_TAC CARD_LTE_TRANS (← q r"t':D->bool") THEN
          ASM_REWRITE_TAC [CARD_LE_ADDL]]]))

  let CARD_LE_ADD_LCANCEL ← prove
   r"!(s:A->bool) (t:B->bool) (u:C->bool).
        (FINITE s \/ s <=_c u) /\
        s +_c t <=_c s +_c u
        ==> t <=_c u"
   (← do
    let lf ← REWRITE_RULE [IMP_CONJ_ALT] CARD_LE_FINITE
    pure (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"FINITE(u:C->bool)") THENL
       [ASM_CASES_TAC (← q r"FINITE(s:A->bool)") THENL
         [ALL_TAC, ASM_MESON_TAC [CARD_LE_FINITE]] THEN
        DISCH_THEN (MP_TAC o CONJUNCT2) THEN
        DISCH_THEN (fun th => tactic_of do
            pure (MP_TAC th THEN MP_TAC (← MATCH_MP lf th))) THEN
        ASM_SIMP_TAC [CARD_LE_CARD, CARD_ADD_FINITE_EQ, CARD_ADD_C] THEN
        SIMP_TAC [LE_ADD_LCANCEL],
        ALL_TAC] THEN
      ASM_CASES_TAC (← q r"FINITE(t:B->bool)") THENL
       [ASM_MESON_TAC [CARD_LE_FINITE_INFINITE, INFINITE], ALL_TAC] THEN
      ASM_CASES_TAC (← q r"(s:A->bool) <=_c (u:C->bool)") THENL
       [ASM_REWRITE_TAC [], ASM_MESON_TAC [CARD_LE_FINITE_INFINITE, INFINITE]] THEN
      ASM_CASES_TAC (← q r"(s:A->bool) <=_c (t:B->bool)") THENL
       [ALL_TAC, ASM_MESON_TAC [CARD_NOT_LE, CARD_LT_IMP_LE, CARD_LE_TRANS]] THEN
      MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC CARD_LE_CONG THEN
      CONJ_TAC THEN MATCH_MP_TAC CARD_ADD_ABSORB_LEFT THEN
      ASM_REWRITE_TAC [INFINITE]))

  let CARD_LE_ADD_LCANCEL_EQ ← prove
   r"!(s:A->bool) (t:B->bool) (u:C->bool).
        (FINITE s \/ s <=_c u)
        ==> (s +_c t <=_c s +_c u <=> t <=_c u)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THEN
    ASM_SIMP_TAC [CARD_LE_ADD, CARD_LE_REFL] THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] CARD_LE_ADD_LCANCEL) THEN
    ASM_REWRITE_TAC [])

  let CARD_LE_ADD_RCANCEL ← prove
   r"!(s:A->bool) (t:B->bool) (u:C->bool).
        (FINITE u \/ u <=_c t) /\
        s +_c u <=_c t +_c u
        ==> s <=_c t"
   (← do
    let lemma ← prove
     r"s +_c u <=_c t +_c u <=> u +_c s <=_c u +_c t"
     (MATCH_MP_TAC CARD_LE_CONG THEN REWRITE_TAC [CARD_ADD_SYM])
    pure (ONCE_REWRITE_TAC [lemma] THEN REWRITE_TAC [CARD_LE_ADD_LCANCEL]))

  let CARD_LE_ADD_RCANCEL_EQ ← prove
   r"!(s:A->bool) (t:B->bool) (u:C->bool).
        (FINITE u \/ u <=_c t)
        ==> (s +_c u <=_c t +_c u <=> s <=_c t)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THEN
    ASM_SIMP_TAC [CARD_LE_ADD, CARD_LE_REFL] THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] CARD_LE_ADD_RCANCEL) THEN
    ASM_REWRITE_TAC [])

  let CARD_EQ_ADD_LCANCEL ← prove
   r"!(s:A->bool) (t:B->bool) (u:C->bool).
        (FINITE s \/ s <=_c t /\ s <=_c u) /\
        s +_c t =_c s +_c u
        ==> t =_c u"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC [← GSYM CARD_LE_ANTISYM] THEN MATCH_MP_TAC MONO_AND THEN
    CONJ_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] CARD_LE_ADD_LCANCEL) THEN
    ASM_MESON_TAC [])

  let CARD_EQ_ADD_LCANCEL_EQ ← prove
   r"!(s:A->bool) (t:B->bool) (u:C->bool).
        (FINITE s \/ s <=_c t /\ s <=_c u)
        ==> (s +_c t =_c s +_c u <=> t =_c u)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [← GSYM CARD_LE_ANTISYM] THEN BINOP_TAC THEN
    MATCH_MP_TAC CARD_LE_ADD_LCANCEL_EQ THEN ASM_MESON_TAC [])

  let CARD_EQ_ADD_RCANCEL ← prove
   r"!(s:A->bool) (t:B->bool) (u:C->bool).
        (FINITE u \/ u <=_c s /\ u <=_c t) /\
        s +_c u =_c t +_c u
        ==> s =_c t"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC [← GSYM CARD_LE_ANTISYM] THEN MATCH_MP_TAC MONO_AND THEN
    CONJ_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] CARD_LE_ADD_RCANCEL) THEN
    ASM_MESON_TAC [])

  let CARD_EQ_ADD_RCANCEL_EQ ← prove
   r"!(s:A->bool) (t:B->bool) (u:C->bool).
        (FINITE u \/ u <=_c s /\ u <=_c t)
        ==> (s +_c u =_c t +_c u <=> s =_c t)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [← GSYM CARD_LE_ANTISYM] THEN BINOP_TAC THEN
    MATCH_MP_TAC CARD_LE_ADD_RCANCEL_EQ THEN ASM_MESON_TAC [])

  let CARD_LE_UNIONS2 ← prove
   r"!u:((A->bool)->bool) k:B->bool l:C->bool.
     u <=_c k /\ (!s. s IN u ==> s <=_c l) ==> UNIONS u <=_c k *_c l"
   (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [LE_C_IMAGE_SUBSET] THEN
    REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM, LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC [RIGHT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"f:B->A->bool", ← q r"g:(A->bool)->C->A"] THEN STRIP_TAC THEN
    TRANS_TAC CARD_LE_TRANS
     (← q r"IMAGE (\(x,y). (g:(A->bool)->C->A) (f x) y)
            ((k:B->bool) *_c (l:C->bool))") THEN
    REWRITE_TAC [CARD_LE_IMAGE] THEN MATCH_MP_TAC CARD_LE_SUBSET THEN
    REPEAT (POP_ASSUM MP_TAC) THEN
    REWRITE_TAC [SUBSET, IN_UNIONS, IN_IMAGE, mul_c, IN_ELIM_PAIR_THM,
                EXISTS_PAIR_THM] THEN
    MESON_TAC [])

  let CARD_LE_UNIONS ← prove
   r"!k:B->bool u:(A->bool)->bool.
        INFINITE k /\ u <=_c k /\ (!s. s IN u ==> s <=_c k)
        ==> UNIONS u <=_c k"
   (REPEAT GEN_TAC THEN DISCH_THEN
     (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o MATCH_MP CARD_LE_UNIONS2)) THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] CARD_LE_TRANS) THEN
    MATCH_MP_TAC CARD_EQ_IMP_LE THEN MATCH_MP_TAC CARD_SQUARE_INFINITE THEN
    ASM_REWRITE_TAC [])

  let CARD_LE_DISJOINT_UNIONS ← prove
   r"!(s:(A->bool)->bool) (t:B->bool).
        pairwise DISJOINT s /\ (!u. u IN s ==> t <=_c u)
        ==> s *_c t <=_c UNIONS s"
   (← do
    let s1 ← SET_RULE (← q r"DISJOINT s t <=> !x. ~(x IN s /\ x IN t)")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [pairwise, s1] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN REWRITE_TAC [le_c] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
      REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"f:(A->bool)->B->A") THEN DISCH_TAC THEN
      EXISTS_TAC (← q r"\(u,y). (f:(A->bool)->B->A) u y") THEN
      REWRITE_TAC [FORALL_PAIR_THM, IN_CARD_MUL, IN_UNIONS, PAIR_EQ] THEN
      ASM_MESON_TAC []))

  let CARD_EQ_DISJOINT_UNIONS ← prove
   r"!(s:(A->bool)->bool) (t:B->bool).
        pairwise DISJOINT s /\ (!u. u IN s ==> u =_c t)
        ==> UNIONS s =_c s *_c t"
   (REWRITE_TAC [← GSYM CARD_LE_ANTISYM] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [CARD_LE_DISJOINT_UNIONS] THEN
    MATCH_MP_TAC CARD_LE_UNIONS2 THEN ASM_SIMP_TAC [CARD_LE_REFL])

  let CARD_EQ_IMAGE_MUL_FIBRES ← prove
   r"!(f:A->B) s (t:C->bool).
           (!x. x IN s ==> {z | z IN s /\ f z = f x} =_c t)
           ==> IMAGE f s *_c t =_c s"
   (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [CARD_EQ_SYM] THEN
    REWRITE_TAC [eq_c] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM, IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"k:A->C->A") THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"!y. y IN IMAGE (f:A->B) s ==> ?x. x IN s /\ f x = y")
    MP_TAC THENL [SET_TAC [], REWRITE_TAC [SURJECTIVE_ON_RIGHT_INVERSE]] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"h:B->A")) THEN
    EXISTS_TAC (← q r"\(y,z). (k:A->C->A) ((h:B->A) y) z") THEN
    REWRITE_TAC [EXISTS_UNIQUE_THM, FORALL_PAIR_THM] THEN
    REWRITE_TAC [IN_CARD_MUL, EXISTS_PAIR_THM, PAIR_EQ] THEN
    REWRITE_TAC [← GSYM CONJ_ASSOC, RIGHT_EXISTS_AND_THM, EXISTS_IN_IMAGE] THEN
    REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_IMAGE] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [FORALL_IN_IMAGE]) THEN ASM_SIMP_TAC [] THEN
    ASM_MESON_TAC [])

  let CARD_DIFF_CONG ← prove
   r"!(s:A->bool) s' (t:B->bool) t'.
        s' SUBSET s /\ t' SUBSET t /\
        s =_c t /\ s' =_c t' /\
        (INFINITE s ==> s' <_c s)
        ==> s DIFF s' =_c t DIFF t'"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"INFINITE(s:A->bool)") THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THENL
     [TRANS_TAC CARD_EQ_TRANS (← q r"(s:A->bool)") THEN
      ASM_SIMP_TAC [CARD_DIFF_ABSORB] THEN
      TRANS_TAC CARD_EQ_TRANS (← q r"(t:B->bool)") THEN
      ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [CARD_EQ_SYM] THEN
      MATCH_MP_TAC CARD_DIFF_ABSORB THEN
      ASM_MESON_TAC [CARD_LT_CONG, CARD_INFINITE_CONG],
      RULE_ASSUM_TAC (REWRITE_RULE [INFINITE]) THEN
      SUBGOAL_THEN (← q r"FINITE(t:B->bool)") ASSUME_TAC THENL
       [ASM_MESON_TAC [CARD_FINITE_CONG], ALL_TAC] THEN
      ASM_SIMP_TAC [CARD_EQ_CARD, FINITE_DIFF, CARD_DIFF] THEN
      ASM_MESON_TAC [CARD_EQ_CARD, FINITE_SUBSET]])

  let EQ_C_BIJECTIONS_DISJOINT ← prove
   r"!(s:A->bool) s' (t:B->bool) t'.
        DISJOINT s s' /\ DISJOINT t t'
        ==> (s =_c t /\ s' =_c t' <=>
             ?f g. (!x. x IN s ==> f x IN t /\ g (f x) = x) /\
                   (!y. y IN t ==> g y IN s /\ f (g y) = y) /\
                   (!x. x IN s' ==> f x IN t' /\ g (f x) = x) /\
                   (!y. y IN t' ==> g y IN s' /\ f (g y) = y))"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [EQ_C_BIJECTIONS] THEN EQ_TAC THENL
     [REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN
      REWRITE_TAC [RIGHT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM],
      DISCH_THEN (fun th => CONJ_TAC THEN MP_TAC th) THEN
      REPEAT (MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN MESON_TAC []] THEN
    MAP_EVERY X_GEN_TAC [← q r"f:A->B", ← q r"g:B->A", ← q r"f':A->B", ← q r"g':B->A"] THEN
    STRIP_TAC THEN
    EXISTS_TAC (← q r"\x. if x IN s then (f:A->B) x else f' x") THEN
    EXISTS_TAC (← q r"\y. if y IN t then (g:B->A) y else g' y") THEN
    ASM SET_TAC [])

  let EQ_C_BIJECTIONS_SUBSETS ← prove
   r"!(s:A->bool) s' (t:B->bool) t'.
        s' SUBSET s /\ t' SUBSET t
        ==> (s' =_c t' /\ s DIFF s' =_c t DIFF t' <=>
             ?f g. (!x. x IN s ==> f x IN t /\ g (f x) = x) /\
                   (!y. y IN t ==> g y IN s /\ f (g y) = y) /\
                   IMAGE f s' = t' /\ IMAGE g t' = s')"
   (← do
    let s1 ← SET_RULE (← q r"DISJOINT t (s DIFF t)")
    pure (REPEAT STRIP_TAC THEN
      mpPartLhand (fun c => do lhand (← rand c)) EQ_C_BIJECTIONS_DISJOINT THEN
      REWRITE_TAC [s1] THEN
      DISCH_THEN SUBST1_TAC THEN REPEAT (AP_TERM_TAC THEN ABS_TAC) THEN
      ASM SET_TAC []))

  let EQ_C_BIJECTIONS_SUBSETS_LT ← prove
   r"!(s:A->bool) s' (t:B->bool) t'.
        s' SUBSET s /\ t' SUBSET t /\ (INFINITE s ==> s' <_c s)
        ==> (s =_c t /\ s' =_c t' <=>
             ?f g. (!x. x IN s ==> f x IN t /\ g (f x) = x) /\
                   (!y. y IN t ==> g y IN s /\ f (g y) = y) /\
                   IMAGE f s' = t' /\ IMAGE g t' = s')"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_SIMP_TAC [← GSYM EQ_C_BIJECTIONS_SUBSETS] THEN
      MATCH_MP_TAC CARD_DIFF_CONG THEN ASM_REWRITE_TAC [],
      DISCH_THEN (fun th => CONJ_TAC THEN MP_TAC th) THEN
      REWRITE_TAC [EQ_C_BIJECTIONS] THEN
      REPEAT (MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN ASM SET_TAC []])

  let EQ_C_BIJECTIONS_EXTEND ← prove
   r"!(f:A->B) g (s:A->bool) s' (t:B->bool) t'.
        s SUBSET s' /\ t SUBSET t' /\ s' DIFF s =_c t' DIFF t /\
        (!x. x IN s ==> f x IN t /\ g (f x) = x) /\
        (!y. y IN t ==> g y IN s /\ f (g y) = y)
        ==> ?f' g'. (!x. x IN s' ==> f' x IN t' /\ g' (f' x) = x) /\
                    (!y. y IN t' ==> g' y IN s' /\ f' (g' y) = y) /\
                    (!x. x IN s ==> f' x = f x) /\
                    (!y. y IN t ==> g' y = g y)"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [EQ_C_BIJECTIONS]) THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"f':A->B", ← q r"g':B->A"] THEN
    STRIP_TAC THEN
    EXISTS_TAC (← q r"\x. if x IN s then (f:A->B) x else f' x") THEN
    EXISTS_TAC (← q r"\y. if y IN t then (g:B->A) y else g' y") THEN
    ASM SET_TAC [])

  let EQ_C_INVOLUTION ← prove
   r"!f s t:A->bool.
        (!x. x IN s ==> f x IN t) /\ (!x. x IN t ==> f x IN s) /\
        (!x. x IN s \/ x IN t ==> f(f x) = x)
        ==> s =_c t"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [EQ_C_BIJECTIONS] THEN
    REPEAT (EXISTS_TAC (← q r"f:A->A")) THEN ASM SET_TAC [])

  -- Some more ad-hoc but useful theorems.

  let CARD_MUL_LT_LEMMA ← prove
   r"!s t:B->bool u. s <=_c t /\ t <_c u /\ INFINITE u ==> s *_c t <_c u"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"FINITE(t:B->bool)") THENL
     [REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC [CARD_NOT_LT, INFINITE] THEN
      ASM_MESON_TAC [CARD_LE_FINITE, CARD_MUL_FINITE],
      ASM_MESON_TAC [INFINITE, CARD_MUL_ABSORB_LE, CARD_LET_TRANS]])

  let CARD_MUL_LT_INFINITE ← prove
   r"!s:A->bool t:B->bool u. s <_c u /\ t <_c u /\ INFINITE u ==> s *_c t <_c u"
   (REPEAT GEN_TAC THEN
    DISJ_CASES_TAC (← ISPECL [← q r"s:A->bool", ← q r"t:B->bool"] CARD_LE_TOTAL) THENL
     [ASM_MESON_TAC [CARD_MUL_SYM, CARD_MUL_LT_LEMMA],
      STRIP_TAC THEN TRANS_TAC CARD_LET_TRANS (← q r"t:B->bool *_c s:A->bool") THEN
      ASM_MESON_TAC [CARD_EQ_IMP_LE, CARD_MUL_SYM, CARD_MUL_LT_LEMMA]])

  -- @@RETURN BEGIN
  return { CARD_LT_ADD, CARD_LE_ADD_LCANCEL, CARD_LE_ADD_LCANCEL_EQ, CARD_LE_ADD_RCANCEL,
           CARD_LE_ADD_RCANCEL_EQ, CARD_EQ_ADD_LCANCEL, CARD_EQ_ADD_LCANCEL_EQ,
           CARD_EQ_ADD_RCANCEL, CARD_EQ_ADD_RCANCEL_EQ, CARD_LE_UNIONS2, CARD_LE_UNIONS,
           CARD_LE_DISJOINT_UNIONS, CARD_EQ_DISJOINT_UNIONS, CARD_EQ_IMAGE_MUL_FIBRES,
           CARD_DIFF_CONG, EQ_C_BIJECTIONS_DISJOINT, EQ_C_BIJECTIONS_SUBSETS,
           EQ_C_BIJECTIONS_SUBSETS_LT, EQ_C_BIJECTIONS_EXTEND, EQ_C_INVOLUTION,
           CARD_MUL_LT_LEMMA, CARD_MUL_LT_INFINITE }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Cantor's theorem; lemmas about countability.  (card.ml 1543-1882)         -/
/- ------------------------------------------------------------------------- -/

structure Countable where
  -- @@FIELDS
  CANTOR_THM : thm
  CANTOR_THM_UNIV : thm
  NUM_COUNTABLE : thm
  COUNTABLE_ALT : thm
  COUNTABLE_CASES : thm
  CARD_LE_COUNTABLE : thm
  CARD_EQ_COUNTABLE : thm
  CARD_COUNTABLE_CONG : thm
  COUNTABLE_SUBSET : thm
  COUNTABLE_RESTRICT : thm
  COUNTABLE_SUBSET_NUM : thm
  FINITE_IMP_COUNTABLE : thm
  CARD_LE_COUNTABLE_INFINITE : thm
  CARD_LT_COUNTABLE_UNCOUNTABLE : thm
  COUNTABLE_IMAGE : thm
  COUNTABLE_IMAGE_INJ_GENERAL : thm
  COUNTABLE_IMAGE_INJ_EQ : thm
  COUNTABLE_IMAGE_INJ : thm
  COUNTABLE_EMPTY : thm
  COUNTABLE_INTER : thm
  COUNTABLE_UNION_IMP : thm
  COUNTABLE_UNION : thm
  COUNTABLE_SING : thm
  COUNTABLE_INSERT : thm
  COUNTABLE_DELETE : thm
  COUNTABLE_DIFF_FINITE : thm
  COUNTABLE_DIFF : thm
  COUNTABLE_CROSS : thm
  COUNTABLE_AS_IMAGE_SUBSET : thm
  COUNTABLE_AS_IMAGE_SUBSET_EQ : thm
  COUNTABLE_AS_IMAGE : thm
  FORALL_COUNTABLE_AS_IMAGE : thm
  COUNTABLE_AS_INJECTIVE_IMAGE : thm
  COUNTABLE_AS_IMAGE_NUM_SUBSET : thm
  COUNTABLE_AS_INJECTIVE_IMAGE_SUBSET : thm
  COUNTABLE_UNIONS : thm
  COUNTABLE_PRODUCT_DEPENDENT : thm
  COUNTABLE_CARD_ADD : thm
  COUNTABLE_CARD_ADD_EQ : thm
  COUNTABLE_CARD_MUL : thm
  COUNTABLE_CARD_MUL_EQ : thm
  CARD_EQ_PCROSS : thm
  COUNTABLE_PCROSS_EQ : thm
  COUNTABLE_PCROSS : thm
  INT_COUNTABLE : thm
  CARD_EQ_INT_NUM : thm
  int_INFINITE : thm
  deriving Inhabited

@[nospecialize]
def setupCountable [HolBase] (D : CardDeps) (BBasics : Basics) (BOrder : Order) (BArith : Arith) (BSquare : Square) (BCancel : Cancel) :
    ExceptT String IO Countable := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, .. } := D
  let { AND_FORALL_THM, CONJ_SYM, COUNTABLE, CROSS, DIFF_EMPTY, EMPTY_GSPEC, EQ_IMP,
        EQ_TRANS, EXISTS_PAIR_THM, EXTENSION, FINITE_INDEX_NUMBERS,
        FINITE_INDUCT_STRONG, FINITE_RULES, FINITE_SING, FORALL_INT_CASES,
        FORALL_IN_GSPEC, FORALL_IN_PCROSS, FORALL_IN_UNIONS, FORALL_PAIR_THM,
        FSTCART_PASTECART, FUN_EQ_THM, IMP_CONJ_ALT, IMP_IMP, IN, .. } := D.core1
  let { INFINITE, INJECTIVE_ON_LEFT_INVERSE, INT_OF_NUM_EQ, IN_CROSS, IN_ELIM_PAIR_THM,
        IN_ELIM_THM, IN_IMAGE, IN_UNIV, LEFT_IMP_EXISTS_THM, LE_C, MEMBER_NOT_EMPTY,
        MONO_EXISTS, NOT_EXISTS_THM, NOT_IN_EMPTY, PASTECART_FST_SND,
        PASTECART_IN_PCROSS, .. } := D.core2
  let { RIGHT_FORALL_IMP_THM, RIGHT_IMP_EXISTS_THM, SKOLEM_THM, SNDCART_PASTECART,
        SUBSET, SUBSET_UNIV, SURJECTIVE_RIGHT_INVERSE, eq_c, ge_c, le_c, lt_c,
        num_INFINITE, .. } := D.core3
  let { CARD_LET_TRANS, CARD_LE_REFL, CARD_LE_TRANS, EQ_C_BIJECTIONS, .. } := BBasics
  let { CARD_INFINITE_CONG, CARD_LE_ANTISYM, CARD_LE_IMAGE, CARD_LE_LT, CARD_LE_SUBSET,
        CARD_NOT_LE, FINITE_CARD_LT, INFINITE_CARD_LE, .. } := BOrder
  let { CARD_LE_ADD, CARD_LE_ADDL, CARD_LE_ADDR, UNION_LE_ADD_C, mul_c, .. } := BArith
  let { CARD_ADD2_ABSORB_LE, CARD_ADD_ABSORB_LE, CARD_MUL2_ABSORB_LE, .. } := BSquare
  let { CARD_LE_UNIONS, .. } := BCancel
  -- @@SCOPE END

  let CANTOR_THM ← prove
   r"!s:A->bool. s <_c {t | t SUBSET s}"
   (GEN_TAC THEN REWRITE_TAC [lt_c] THEN CONJ_TAC THENL
     [REWRITE_TAC [le_c] THEN EXISTS_TAC (← q r"(=):A->A->bool") THEN
      REWRITE_TAC [FUN_EQ_THM, IN_ELIM_THM, SUBSET, IN] THEN MESON_TAC [],
      REWRITE_TAC [LE_C, IN_ELIM_THM, SURJECTIVE_RIGHT_INVERSE] THEN
      REWRITE_TAC [NOT_EXISTS_THM] THEN X_GEN_TAC (← q r"g:A->(A->bool)") THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"\x:A. s(x) /\ ~(g x x)")) THEN
      REWRITE_TAC [SUBSET, IN, FUN_EQ_THM] THEN MESON_TAC []])

  let CANTOR_THM_UNIV ← prove
   r"(UNIV:A->bool) <_c (UNIV:(A->bool)->bool)"
   (MP_TAC (← ISPEC (← q r"UNIV:A->bool") CANTOR_THM) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION, SUBSET, IN_UNIV, IN_ELIM_THM])

  -- Lemmas about countability.

  let NUM_COUNTABLE ← prove
   r"COUNTABLE(:num)"
   (REWRITE_TAC [COUNTABLE, ge_c, CARD_LE_REFL])

  let COUNTABLE_ALT ← prove
   r"!s. COUNTABLE s <=> s <=_c (:num)"
   (REWRITE_TAC [COUNTABLE, ge_c])

  let COUNTABLE_CASES ← prove
   r"!s. COUNTABLE s <=> FINITE s \/ s =_c (:num)"
   (REWRITE_TAC [COUNTABLE_ALT, FINITE_CARD_LT, CARD_LE_LT])

  let CARD_LE_COUNTABLE ← prove
   r"!s t:A->bool. COUNTABLE t /\ s <=_c t ==> COUNTABLE s"
   (REWRITE_TAC [COUNTABLE, ge_c] THEN REPEAT STRIP_TAC THEN
    TRANS_TAC CARD_LE_TRANS (← q r"t:A->bool") THEN ASM_REWRITE_TAC [])

  let CARD_EQ_COUNTABLE ← prove
   r"!s t:A->bool. COUNTABLE t /\ s =_c t ==> COUNTABLE s"
   (REWRITE_TAC [← GSYM CARD_LE_ANTISYM] THEN MESON_TAC [CARD_LE_COUNTABLE])

  let CARD_COUNTABLE_CONG ← prove
   r"!s t. s =_c t ==> (COUNTABLE s <=> COUNTABLE t)"
   (REWRITE_TAC [← GSYM CARD_LE_ANTISYM] THEN MESON_TAC [CARD_LE_COUNTABLE])

  let COUNTABLE_SUBSET ← prove
   r"!s t:A->bool. COUNTABLE t /\ s SUBSET t ==> COUNTABLE s"
   (REWRITE_TAC [COUNTABLE, ge_c] THEN REPEAT STRIP_TAC THEN
    TRANS_TAC CARD_LE_TRANS (← q r"t:A->bool") THEN
    ASM_SIMP_TAC [CARD_LE_SUBSET])

  let COUNTABLE_RESTRICT ← prove
   r"!s P. COUNTABLE s ==> COUNTABLE {x | x IN s /\ P x}"
   (REPEAT GEN_TAC THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] COUNTABLE_SUBSET) THEN
    SET_TAC [])

  let COUNTABLE_SUBSET_NUM ← prove
   r"!s:num->bool. COUNTABLE s"
   (MESON_TAC [NUM_COUNTABLE, COUNTABLE_SUBSET, SUBSET_UNIV])

  let FINITE_IMP_COUNTABLE ← prove
   r"!s. FINITE s ==> COUNTABLE s"
   (SIMP_TAC [FINITE_CARD_LT, lt_c, COUNTABLE, ge_c])

  let CARD_LE_COUNTABLE_INFINITE ← prove
   r"!(s:A->bool) (t:B->bool). COUNTABLE s /\ INFINITE t ==> s <=_c t"
   (REWRITE_TAC [COUNTABLE, ge_c, INFINITE_CARD_LE, CARD_LE_TRANS])

  let CARD_LT_COUNTABLE_UNCOUNTABLE ← prove
   r"!(s:A->bool) (t:B->bool).
        COUNTABLE s /\ ~COUNTABLE t ==> s <_c t"
   (REWRITE_TAC [COUNTABLE, ge_c, CARD_NOT_LE, CARD_LET_TRANS])

  let COUNTABLE_IMAGE ← prove
   r"!f:A->B s. COUNTABLE s ==> COUNTABLE (IMAGE f s)"
   (REWRITE_TAC [COUNTABLE, ge_c] THEN REPEAT STRIP_TAC THEN
    TRANS_TAC CARD_LE_TRANS (← q r"s:A->bool") THEN
    ASM_SIMP_TAC [CARD_LE_IMAGE])

  let COUNTABLE_IMAGE_INJ_GENERAL ← prove
   r"!(f:A->B) A s.
        (!x y. x IN s /\ y IN s /\ f(x) = f(y) ==> x = y) /\
        COUNTABLE A
        ==> COUNTABLE {x | x IN s /\ f(x) IN A}"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [INJECTIVE_ON_LEFT_INVERSE]) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"g:B->A")) THEN
    MATCH_MP_TAC COUNTABLE_SUBSET THEN EXISTS_TAC (← q r"IMAGE (g:B->A) A") THEN
    ASM_SIMP_TAC [COUNTABLE_IMAGE] THEN ASM SET_TAC [])

  let COUNTABLE_IMAGE_INJ_EQ ← prove
   r"!(f:A->B) s.
        (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y))
        ==> (COUNTABLE(IMAGE f s) <=> COUNTABLE s)"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC [COUNTABLE_IMAGE] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC [IMP_IMP] THEN
    DISCH_THEN (MP_TAC o MATCH_MP COUNTABLE_IMAGE_INJ_GENERAL) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN SET_TAC [])

  let COUNTABLE_IMAGE_INJ ← prove
   r"!(f:A->B) A.
        (!x y. (f(x) = f(y)) ==> (x = y)) /\
         COUNTABLE A
         ==> COUNTABLE {x | f(x) IN A}"
   (REPEAT GEN_TAC THEN
    MP_TAC (← SPECL [← q r"f:A->B", ← q r"A:B->bool", ← q r"UNIV:A->bool"]
      COUNTABLE_IMAGE_INJ_GENERAL) THEN REWRITE_TAC [IN_UNIV])

  let COUNTABLE_EMPTY ← prove
   r"COUNTABLE {}"
   (SIMP_TAC [FINITE_IMP_COUNTABLE, FINITE_RULES])

  let COUNTABLE_INTER ← prove
   r"!s t. COUNTABLE s \/ COUNTABLE t ==> COUNTABLE (s INTER t)"
   (← do
    let cs ← REWRITE_RULE [IMP_CONJ_ALT] COUNTABLE_SUBSET
    let t ← TAUT (← q r"(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)")
    pure (REWRITE_TAC [t] THEN
      REPEAT GEN_TAC THEN CONJ_TAC THEN
      MATCH_MP_TAC cs THEN
      SET_TAC []))

  let COUNTABLE_UNION_IMP ← prove
   r"!s t:A->bool. COUNTABLE s /\ COUNTABLE t ==> COUNTABLE(s UNION t)"
   (REWRITE_TAC [COUNTABLE, ge_c] THEN REPEAT STRIP_TAC THEN
    TRANS_TAC CARD_LE_TRANS (← q r"(s:A->bool) +_c (t:A->bool)") THEN
    ASM_SIMP_TAC [CARD_ADD2_ABSORB_LE, num_INFINITE, UNION_LE_ADD_C])

  let COUNTABLE_UNION ← prove
   r"!s t:A->bool. COUNTABLE(s UNION t) <=> COUNTABLE s /\ COUNTABLE t"
   (REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC [COUNTABLE_UNION_IMP] THEN
    DISCH_THEN (fun th => CONJ_TAC THEN MP_TAC th) THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] COUNTABLE_SUBSET) THEN
    SET_TAC [])

  let COUNTABLE_SING ← prove
   r"!x. COUNTABLE {x}"
   (SIMP_TAC [FINITE_IMP_COUNTABLE, FINITE_SING])

  let COUNTABLE_INSERT ← prove
   r"!x s. COUNTABLE(x INSERT s) <=> COUNTABLE s"
   (ONCE_REWRITE_TAC [← SET_RULE (← q r"x INSERT s = {x} UNION s")] THEN
    REWRITE_TAC [COUNTABLE_UNION, COUNTABLE_SING])

  let COUNTABLE_DELETE ← prove
   r"!x:A s. COUNTABLE(s DELETE x) <=> COUNTABLE s"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"(x:A) IN s") THEN
    ASM_SIMP_TAC [← SET_RULE (← q r"~(x IN s) ==> s DELETE x = s")] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"COUNTABLE((x:A) INSERT (s DELETE x))") THEN CONJ_TAC THENL
     [REWRITE_TAC [COUNTABLE_INSERT], AP_TERM_TAC THEN ASM SET_TAC []])

  let COUNTABLE_DIFF_FINITE ← prove
   r"!s t. FINITE s ==> (COUNTABLE(t DIFF s) <=> COUNTABLE t)"
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [DIFF_EMPTY, ← SET_RULE (← q r"s DIFF (x INSERT t) = (s DIFF t) DELETE x"),
             COUNTABLE_DELETE])

  let COUNTABLE_DIFF ← prove
   r"!s t:A->bool. COUNTABLE s ==> COUNTABLE(s DIFF t)"
   (MESON_TAC [COUNTABLE_SUBSET, ← SET_RULE (← q r"s DIFF t SUBSET s")])

  let COUNTABLE_CROSS ← prove
   r"!s t. COUNTABLE s /\ COUNTABLE t ==> COUNTABLE(s CROSS t)"
   (REWRITE_TAC [COUNTABLE, ge_c, CROSS, ← GSYM mul_c] THEN
    SIMP_TAC [CARD_MUL2_ABSORB_LE, num_INFINITE])

  let COUNTABLE_AS_IMAGE_SUBSET ← prove
   r"!s. COUNTABLE s ==> ?f. s SUBSET (IMAGE f (:num))"
   (REWRITE_TAC [COUNTABLE, ge_c, LE_C, SUBSET, IN_IMAGE] THEN MESON_TAC [])

  let COUNTABLE_AS_IMAGE_SUBSET_EQ ← prove
   r"!s:A->bool. COUNTABLE s <=> ?f. s SUBSET (IMAGE f (:num))"
   (REWRITE_TAC [COUNTABLE, ge_c, LE_C, SUBSET, IN_IMAGE] THEN MESON_TAC [])

  let COUNTABLE_AS_IMAGE ← prove
   r"!s:A->bool. COUNTABLE s /\ ~(s = {}) ==> ?f. s = IMAGE f (:num)"
   (REPEAT STRIP_TAC THEN FIRST_X_ASSUM (X_CHOOSE_TAC (← q "a:A") o
      GEN_REWRITE_RULE id [← GSYM MEMBER_NOT_EMPTY]) THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP COUNTABLE_AS_IMAGE_SUBSET) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"f:num->A")) THEN
    EXISTS_TAC (← q r"\n. if (f:num->A) n IN s then f n else a") THEN
    ASM SET_TAC [])

  let FORALL_COUNTABLE_AS_IMAGE ← prove
   r"(!d. COUNTABLE d ==> P d) <=> P {} /\ (!f. P(IMAGE f (:num)))"
   (MESON_TAC [COUNTABLE_AS_IMAGE, COUNTABLE_IMAGE, NUM_COUNTABLE,
              COUNTABLE_EMPTY])

  let COUNTABLE_AS_INJECTIVE_IMAGE ← prove
   r"!s. COUNTABLE s /\ INFINITE s
       ==> ?f. s = IMAGE f (:num) /\ (!m n. f(m) = f(n) ==> m = n)"
   (GEN_TAC THEN ONCE_REWRITE_TAC [CONJ_SYM] THEN
    REWRITE_TAC [INFINITE_CARD_LE, COUNTABLE, ge_c] THEN
    REWRITE_TAC [CARD_LE_ANTISYM, eq_c] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SET_TAC [])

  let (COUNTABLE_AS_IMAGE_NUM_SUBSET, COUNTABLE_AS_INJECTIVE_IMAGE_SUBSET) ← CONJ_PAIR (← prove
   r"(!s. COUNTABLE s <=> ?(f:num->A) k. s = IMAGE f k) /\
   (!s. COUNTABLE s <=>
       ?(f:num->A) k. s = IMAGE f k /\
                      (!m n. m IN k /\ n IN k /\ f m = f n ==> m = n))"
   (← do
    let t ← TAUT
     (← q r"(r ==> q) /\ (q ==> p) /\ (p ==> r) ==> (p <=> q) /\ (p <=> r)")
    pure (REWRITE_TAC [AND_FORALL_THM] THEN X_GEN_TAC (← q r"s:A->bool") THEN
      MATCH_MP_TAC t THEN
      REPEAT CONJ_TAC THENL
       [MESON_TAC [],
        SIMP_TAC [LEFT_IMP_EXISTS_THM, COUNTABLE_IMAGE, COUNTABLE_SUBSET_NUM],
        DISCH_TAC THEN ASM_CASES_TAC (← q r"FINITE(s:A->bool)") THENL
         [ASM_MESON_TAC [FINITE_INDEX_NUMBERS],
          ASM_MESON_TAC [COUNTABLE_AS_INJECTIVE_IMAGE, INFINITE]]])))

  let COUNTABLE_UNIONS ← prove
   r"!A:(A->bool)->bool.
        COUNTABLE A /\ (!s. s IN A ==> COUNTABLE s)
        ==> COUNTABLE (UNIONS A)"
   (REWRITE_TAC [COUNTABLE, ge_c] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CARD_LE_UNIONS THEN ASM_REWRITE_TAC [num_INFINITE])

  let COUNTABLE_PRODUCT_DEPENDENT ← prove
   r"!f:A->B->C s t.
        COUNTABLE s /\ (!x. x IN s ==> COUNTABLE(t x))
        ==> COUNTABLE {f x y | x IN s /\ y IN (t x)}"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"{(f:A->B->C) x y | x IN s /\ y IN (t x)} =
                  IMAGE (\(x,y). f x y) {(x,y) | x IN s /\ y IN (t x)}")
    SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_IMAGE, EXISTS_PAIR_THM, IN_ELIM_PAIR_THM] THEN
      SET_TAC [],
      MATCH_MP_TAC COUNTABLE_IMAGE THEN POP_ASSUM MP_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [COUNTABLE_AS_IMAGE_SUBSET_EQ] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q r"f:num->A")) MP_TAC) THEN
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [SKOLEM_THM] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"g:A->num->B")) THEN
    MATCH_MP_TAC COUNTABLE_SUBSET THEN
    EXISTS_TAC (← q r"IMAGE (\(m,n). (f:num->A) m,(g:A->num->B)(f m) n)
                      ((:num) CROSS (:num))") THEN
    ASM_SIMP_TAC [COUNTABLE_IMAGE, COUNTABLE_CROSS, NUM_COUNTABLE] THEN
    REWRITE_TAC [SUBSET, FORALL_IN_UNIONS] THEN
    REWRITE_TAC [IN_IMAGE, FORALL_PAIR_THM, IN_ELIM_PAIR_THM,
                EXISTS_PAIR_THM, IN_CROSS, IN_UNIV] THEN
    ASM SET_TAC [])

  let COUNTABLE_CARD_ADD ← prove
   r"!s:A->bool t:B->bool. COUNTABLE s /\ COUNTABLE t ==> COUNTABLE(s +_c t)"
   (REWRITE_TAC [COUNTABLE, ge_c] THEN REPEAT STRIP_TAC THEN
    TRANS_TAC CARD_LE_TRANS (← q r"(:num) +_c (:num)") THEN
    ASM_SIMP_TAC [CARD_LE_ADD] THEN MATCH_MP_TAC CARD_ADD_ABSORB_LE THEN
    REWRITE_TAC [num_INFINITE, CARD_LE_REFL])

  let COUNTABLE_CARD_ADD_EQ ← prove
   r"!s:A->bool t:B->bool. COUNTABLE(s +_c t) <=> COUNTABLE s /\ COUNTABLE t"
   (REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC [COUNTABLE_CARD_ADD] THEN
    DISCH_THEN (fun th => CONJ_TAC THEN MP_TAC th) THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] CARD_LE_COUNTABLE) THEN
    REWRITE_TAC [CARD_LE_ADDL, CARD_LE_ADDR])

  let COUNTABLE_CARD_MUL ← prove
   r"!s:A->bool t:B->bool. COUNTABLE s /\ COUNTABLE t ==> COUNTABLE(s *_c t)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [mul_c] THEN
    ASM_SIMP_TAC [COUNTABLE_PRODUCT_DEPENDENT])

  let COUNTABLE_CARD_MUL_EQ ← prove
   r"!s:A->bool t:B->bool.
        COUNTABLE(s *_c t) <=> s = {} \/ t = {} \/ COUNTABLE s /\ COUNTABLE t"
   (← do
    let cm ← REWRITE_RULE [mul_c] COUNTABLE_CARD_MUL
    let s1 ← SET_RULE (← q r"{x,y | F} = {}")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [mul_c] THEN
      MAP_EVERY ASM_CASES_TAC [← q r"s:A->bool = {}", ← q r"t:B->bool = {}"] THEN
      ASM_REWRITE_TAC [COUNTABLE_EMPTY, EMPTY_GSPEC, NOT_IN_EMPTY, s1] THEN
      EQ_TAC THEN SIMP_TAC [cm] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC COUNTABLE_SUBSET THENL
       [EXISTS_TAC (← q r"IMAGE FST ((s:A->bool) *_c (t:B->bool))"),
        EXISTS_TAC (← q r"IMAGE SND ((s:A->bool) *_c (t:B->bool))")] THEN
      ASM_SIMP_TAC [COUNTABLE_IMAGE, mul_c, SUBSET, IN_IMAGE, EXISTS_PAIR_THM] THEN
      REWRITE_TAC [IN_ELIM_PAIR_THM] THEN ASM SET_TAC []))

  let CARD_EQ_PCROSS ← prove
   r"!s:A^M->bool t:A^N->bool. s PCROSS t =_c s *_c t"
   (REPEAT GEN_TAC THEN REWRITE_TAC [EQ_C_BIJECTIONS, mul_c] THEN
    EXISTS_TAC (← q r"\z:A^(M,N)finite_sum. fstcart z,sndcart z") THEN
    EXISTS_TAC (← q r"\(x:A^M,y:A^N). pastecart x y") THEN
    REWRITE_TAC [FORALL_IN_GSPEC, PASTECART_IN_PCROSS] THEN
    REWRITE_TAC [IN_ELIM_PAIR_THM, PASTECART_FST_SND] THEN
    REWRITE_TAC [FORALL_IN_PCROSS, FSTCART_PASTECART, SNDCART_PASTECART])

  let COUNTABLE_PCROSS_EQ ← prove
   r"!s:A^M->bool t:A^N->bool.
        COUNTABLE(s PCROSS t) <=>
        s = {} \/ t = {} \/ COUNTABLE s /\ COUNTABLE t"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"COUNTABLE((s:A^M->bool) *_c (t:A^N->bool))") THEN CONJ_TAC THENL
     [MATCH_MP_TAC CARD_COUNTABLE_CONG THEN REWRITE_TAC [CARD_EQ_PCROSS],
      REWRITE_TAC [COUNTABLE_CARD_MUL_EQ]])

  let COUNTABLE_PCROSS ← prove
   r"!s:A^M->bool t:A^N->bool.
        COUNTABLE s /\ COUNTABLE t ==> COUNTABLE(s PCROSS t)"
   (SIMP_TAC [COUNTABLE_PCROSS_EQ])

  let INT_COUNTABLE ← prove
   r"COUNTABLE (:int)"
   (MATCH_MP_TAC COUNTABLE_SUBSET THEN
    EXISTS_TAC (← q r"IMAGE (\n. (&n:int)) (:num) UNION IMAGE (\n. --(&n)) (:num)") THEN
    SIMP_TAC [COUNTABLE_UNION, COUNTABLE_IMAGE, NUM_COUNTABLE] THEN
    REWRITE_TAC [SUBSET, FORALL_INT_CASES] THEN SET_TAC [])

  let CARD_EQ_INT_NUM ← prove
   r"(:int) =_c (:num)"
   (REWRITE_TAC [← GSYM CARD_LE_ANTISYM, ← GSYM COUNTABLE_ALT, INT_COUNTABLE] THEN
    REWRITE_TAC [le_c] THEN EXISTS_TAC (← q "int_of_num") THEN
    SIMP_TAC [INT_OF_NUM_EQ, IN_UNIV])

  let int_INFINITE ← prove
   r"INFINITE (:int)"
   (SUBST1_TAC (← MATCH_MP CARD_INFINITE_CONG CARD_EQ_INT_NUM) THEN
    REWRITE_TAC [num_INFINITE])

  -- @@RETURN BEGIN
  return { CANTOR_THM, CANTOR_THM_UNIV, NUM_COUNTABLE, COUNTABLE_ALT, COUNTABLE_CASES,
           CARD_LE_COUNTABLE, CARD_EQ_COUNTABLE, CARD_COUNTABLE_CONG, COUNTABLE_SUBSET,
           COUNTABLE_RESTRICT, COUNTABLE_SUBSET_NUM, FINITE_IMP_COUNTABLE,
           CARD_LE_COUNTABLE_INFINITE, CARD_LT_COUNTABLE_UNCOUNTABLE, COUNTABLE_IMAGE,
           COUNTABLE_IMAGE_INJ_GENERAL, COUNTABLE_IMAGE_INJ_EQ, COUNTABLE_IMAGE_INJ,
           COUNTABLE_EMPTY, COUNTABLE_INTER, COUNTABLE_UNION_IMP, COUNTABLE_UNION,
           COUNTABLE_SING, COUNTABLE_INSERT, COUNTABLE_DELETE, COUNTABLE_DIFF_FINITE,
           COUNTABLE_DIFF, COUNTABLE_CROSS, COUNTABLE_AS_IMAGE_SUBSET,
           COUNTABLE_AS_IMAGE_SUBSET_EQ, COUNTABLE_AS_IMAGE, FORALL_COUNTABLE_AS_IMAGE,
           COUNTABLE_AS_INJECTIVE_IMAGE, COUNTABLE_AS_IMAGE_NUM_SUBSET,
           COUNTABLE_AS_INJECTIVE_IMAGE_SUBSET, COUNTABLE_UNIONS,
           COUNTABLE_PRODUCT_DEPENDENT, COUNTABLE_CARD_ADD, COUNTABLE_CARD_ADD_EQ,
           COUNTABLE_CARD_MUL, COUNTABLE_CARD_MUL_EQ, CARD_EQ_PCROSS,
           COUNTABLE_PCROSS_EQ, COUNTABLE_PCROSS, INT_COUNTABLE, CARD_EQ_INT_NUM,
           int_INFINITE }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Countable products of vectors; countable subsets of images; countable    -/
/- unions and intersections of a family.  (card.ml 1866-2190)                -/
/- ------------------------------------------------------------------------- -/

structure UnionOf where
  -- @@FIELDS
  COUNTABLE_CART : thm
  EXISTS_COUNTABLE_SUBSET_IMAGE_INJ : thm
  FORALL_COUNTABLE_SUBSET_IMAGE_INJ : thm
  EXISTS_COUNTABLE_SUBSET_IMAGE : thm
  FORALL_COUNTABLE_SUBSET_IMAGE : thm
  COUNTABLE_SUBSET_IMAGE : thm
  COUNTABLE_IMAGE_EQ : thm
  COUNTABLE_IMAGE_EQ_INJ : thm
  COUNTABLE_FLD : thm
  COUNTABLE_UNION_OF_EMPTY : thm
  COUNTABLE_INTERSECTION_OF_EMPTY : thm
  COUNTABLE_UNION_OF_INC : thm
  COUNTABLE_INTERSECTION_OF_INC : thm
  COUNTABLE_UNION_OF_COMPLEMENT : thm
  COUNTABLE_INTERSECTION_OF_COMPLEMENT : thm
  COUNTABLE_UNION_OF_EXPLICIT : thm
  COUNTABLE_UNION_OF_ASCENDING : thm
  COUNTABLE_UNION_OF_IDEMPOT : thm
  COUNTABLE_INTERSECTION_OF_IDEMPOT : thm
  COUNTABLE_UNION_OF_UNIONS : thm
  COUNTABLE_UNION_OF_UNION : thm
  COUNTABLE_INTERSECTION_OF_INTERS : thm
  COUNTABLE_INTERSECTION_OF_INTER : thm
  COUNTABLE_UNION_OF_INTER_EQ : thm
  COUNTABLE_UNION_OF_INTER : thm
  COUNTABLE_INTERSECTION_OF_UNION_EQ : thm
  COUNTABLE_INTERSECTION_OF_UNION : thm
  COUNTABLE_INTERSECTION_OF_UNIONS_NONEMPTY : thm
  COUNTABLE_INTERSECTION_OF_UNIONS : thm
  deriving Inhabited

@[nospecialize]
def setupUnionOf [HolBase] (D : CardDeps) (BCountable : Countable) (ADefs : HolLibrary.Wo.Defs) :
    ExceptT String IO UnionOf := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, ASM_METIS_TAC, INDUCT_TAC, MESON, MESON_TAC,
        SET_RULE, SET_TAC, .. } := D
  let { CART_EQ, COMPL_COMPL, CONJ_ASSOC, CROSS, EMPTY_GSPEC, ETA_AX, EXISTS_IN_GSPEC,
        EXISTS_PAIR_THM, EXISTS_SUBSET_IMAGE_INJ, EXTENSION, FINITE_INDUCT_STRONG,
        FORALL_IN_GSPEC, FORALL_IN_IMAGE, FORALL_IN_INSERT, FORALL_PAIR_THM,
        FUN_EQ_THM, IMAGE_ID, IMAGE_SUBSET, IMP_CONJ, IMP_CONJ_ALT, IMP_IMP, .. } := D.core1
  let { INTERSECTION_OF, INTERSECTION_OF_EMPTY, INTERSECTION_OF_INC, INTERS_2,
        INTERS_UNIONS, INTER_UNIONS, IN_CROSS, IN_ELIM_PAIR_THM, IN_ELIM_THM, IN_IMAGE,
        IN_SING, IN_UNION, IN_UNIV, LAMBDA_BETA, LE, LEFT_IMP_EXISTS_THM, LET_ANTISYM,
        LE_REFL, MONO_EXISTS, NOT_IMP, NOT_INSERT_EMPTY, NOT_IN_EMPTY, PAIR_EQ, .. } := D.core2
  let { RIGHT_FORALL_IMP_THM, RIGHT_IMP_EXISTS_THM, RIGHT_IMP_FORALL_THM, SIMPLE_IMAGE,
        SKOLEM_THM, SUBSET, SUBSET_IMAGE_INJ, SUBSET_REFL, UNIONS_0, UNIONS_1,
        UNIONS_2, UNIONS_GSPEC, UNIONS_IMAGE, UNIONS_INSERT, UNIONS_INTERS,
        UNIONS_UNION, UNION_OF, UNION_OF_EMPTY, UNION_OF_INC, .. } := D.core3
  let { COUNTABLE_AS_IMAGE, COUNTABLE_CROSS, COUNTABLE_EMPTY, COUNTABLE_IMAGE,
        COUNTABLE_IMAGE_INJ_EQ, COUNTABLE_INSERT, COUNTABLE_PRODUCT_DEPENDENT,
        COUNTABLE_SING, COUNTABLE_SUBSET, COUNTABLE_SUBSET_NUM, COUNTABLE_UNION, .. } := BCountable
  let { fld, .. } := ADefs
  -- @@SCOPE END

  let COUNTABLE_CART ← prove
   r"!P. (!i. 1 <= i /\ i <= dimindex(:N) ==> COUNTABLE {x | P i x})
       ==> COUNTABLE {v:A^N | !i. 1 <= i /\ i <= dimindex(:N) ==> P i (v$i)}"
   (← do
    let a8 ← ARITH_RULE (← q r"n < i /\ ~(i = SUC n) ==> SUC n < i")
    let a7 ← ARITH_RULE (← q r"1 <= SUC n")
    let a6 ← ARITH_RULE (← q r"i <= n ==> ~(i = SUC n)")
    let a5 ← ARITH_RULE (← q r"SUC n <= m ==> n <= m")
    let a4 ← ARITH_RULE (← q r"1 <= SUC n")
    let cc ← REWRITE_RULE [CROSS] COUNTABLE_CROSS
    let a2 ← ARITH_RULE (← q r"1 <= i /\ i <= n /\ 0 < i <=> 1 <= i /\ i <= n")
    let a1 ← ARITH_RULE (← q r"1 <= i /\ i <= n /\ i <= 0 <=> F")
    pure (GEN_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN
       (← q r"!n. n <= dimindex(:N)
            ==> COUNTABLE {v:A^N | (!i. 1 <= i /\ i <= dimindex(:N) /\ i <= n
                                     ==> P i (v$i)) /\
                                (!i. 1 <= i /\ i <= dimindex(:N) /\ n < i
                                     ==> v$i = @x. F)}")
       (MP_TAC o SPEC (← q r"dimindex(:N)")) THEN REWRITE_TAC [LE_REFL, LET_ANTISYM] THEN
      INDUCT_TAC THENL
       [REWRITE_TAC [a1] THEN
        SIMP_TAC [a2] THEN
        SUBGOAL_THEN
         (← q r"{v | !i. 1 <= i /\ i <= dimindex (:N) ==> v$i = (@x. F)} =
          {(lambda i. @x. F):A^N}")
         (fun th => SIMP_TAC [COUNTABLE_SING, th]) THEN
        SIMP_TAC [EXTENSION, IN_SING, IN_ELIM_THM, CART_EQ, LAMBDA_BETA],
        ALL_TAC] THEN
      DISCH_TAC THEN
      MATCH_MP_TAC COUNTABLE_SUBSET THEN EXISTS_TAC
       (← q r"IMAGE (\(x:A,v:A^N). (lambda i. if i = SUC n then x else v$i):A^N)
              {x,v | x IN {x:A | P (SUC n) x} /\
                     v IN {v:A^N | (!i. 1 <= i /\ i <= dimindex(:N) /\ i <= n
                                    ==> P i (v$i)) /\
                               (!i. 1 <= i /\ i <= dimindex (:N) /\ n < i
                                    ==> v$i = (@x. F))}}") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC COUNTABLE_IMAGE THEN
        ASM_SIMP_TAC [cc, a4, a5],
        ALL_TAC] THEN
      REWRITE_TAC [SUBSET, IN_IMAGE, IN_ELIM_PAIR_THM, EXISTS_PAIR_THM] THEN
      X_GEN_TAC (← q r"v:A^N") THEN REWRITE_TAC [IN_ELIM_THM] THEN
      STRIP_TAC THEN EXISTS_TAC (← q r"(v:A^N)$(SUC n)") THEN
      EXISTS_TAC (← q r"(lambda i. if i = SUC n then @x. F else (v:A^N)$i):A^N") THEN
      SIMP_TAC [CART_EQ, LAMBDA_BETA, a6] THEN
      ASM_MESON_TAC [LE, a7, a8]))

  let EXISTS_COUNTABLE_SUBSET_IMAGE_INJ ← prove
   r"!P f s.
    (?t. COUNTABLE t /\ t SUBSET IMAGE f s /\ P t) <=>
    (?t. COUNTABLE t /\ t SUBSET s /\
         (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y)) /\
         P (IMAGE f t))"
   (← do
    let t ← TAUT (← q r"p /\ q /\ r <=> q /\ p /\ r")
    pure (ONCE_REWRITE_TAC [t] THEN
      REPEAT GEN_TAC THEN REWRITE_TAC [EXISTS_SUBSET_IMAGE_INJ] THEN
      AP_TERM_TAC THEN ABS_TAC THEN MESON_TAC [COUNTABLE_IMAGE_INJ_EQ]))

  let FORALL_COUNTABLE_SUBSET_IMAGE_INJ ← prove
   r"!P f s. (!t. COUNTABLE t /\ t SUBSET IMAGE f s ==> P t) <=>
           (!t. COUNTABLE t /\ t SUBSET s /\
                (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y))
                 ==> P(IMAGE f t))"
   (REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC [← MESON [] (← q r"(!t. p t) <=> ~(?t. ~p t)")] THEN
    REWRITE_TAC [NOT_IMP, EXISTS_COUNTABLE_SUBSET_IMAGE_INJ, ← GSYM CONJ_ASSOC])

  let EXISTS_COUNTABLE_SUBSET_IMAGE ← prove
   r"!P f s.
    (?t. COUNTABLE t /\ t SUBSET IMAGE f s /\ P t) <=>
    (?t. COUNTABLE t /\ t SUBSET s /\ P (IMAGE f t))"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [REWRITE_TAC [EXISTS_COUNTABLE_SUBSET_IMAGE_INJ] THEN MESON_TAC [],
      MESON_TAC [COUNTABLE_IMAGE, IMAGE_SUBSET]])

  let FORALL_COUNTABLE_SUBSET_IMAGE ← prove
   r"!P f s. (!t. COUNTABLE t /\ t SUBSET IMAGE f s ==> P t) <=>
           (!t. COUNTABLE t /\ t SUBSET s ==> P(IMAGE f t))"
   (REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC [← MESON [] (← q r"(!x. P x) <=> ~(?x. ~P x)")] THEN
    REWRITE_TAC [NOT_IMP, ← GSYM CONJ_ASSOC, EXISTS_COUNTABLE_SUBSET_IMAGE])

  let COUNTABLE_SUBSET_IMAGE ← prove
   r"!f:A->B s t.
        COUNTABLE(t) /\ t SUBSET (IMAGE f s) <=>
        ?s'. COUNTABLE s' /\ s' SUBSET s /\ (t = IMAGE f s')"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [ALL_TAC, ASM_MESON_TAC [COUNTABLE_IMAGE, IMAGE_SUBSET]] THEN
    SPEC_TAC (← q r"t:B->bool", ← q r"t:B->bool") THEN
    REWRITE_TAC [FORALL_COUNTABLE_SUBSET_IMAGE] THEN MESON_TAC [])

  let COUNTABLE_IMAGE_EQ ← prove
   r"!(f:A->B) s. COUNTABLE(IMAGE f s) <=>
                ?t. COUNTABLE t /\ t SUBSET s /\ IMAGE f s = IMAGE f t"
   (MESON_TAC [COUNTABLE_SUBSET_IMAGE, COUNTABLE_IMAGE, SUBSET_REFL])

  let COUNTABLE_IMAGE_EQ_INJ ← prove
   r"!(f:A->B) s. COUNTABLE(IMAGE f s) <=>
                ?t. COUNTABLE t /\ t SUBSET s /\ IMAGE f s = IMAGE f t /\
                    (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y))"
   (REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC, MESON_TAC [COUNTABLE_IMAGE]] THEN
    DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"f:A->B", ← q r"IMAGE (f:A->B) s", ← q r"s:A->bool"]
          SUBSET_IMAGE_INJ) THEN
    REWRITE_TAC [SUBSET_REFL] THEN MATCH_MP_TAC MONO_EXISTS THEN
    ASM_METIS_TAC [COUNTABLE_IMAGE_INJ_EQ])

  let COUNTABLE_FLD ← prove
   r"!l:A->A->bool. COUNTABLE(fld l) <=> COUNTABLE {(x,y) | l x y}"
   (← do
    let tFST ← q r"FST:A#A->A"
    let tSND ← q r"SND:A#A->A"
    pure (GEN_TAC THEN EQ_TAC THENL
       [DISCH_THEN (fun th => tactic_of do
          pure (MP_TAC (← MATCH_MP COUNTABLE_CROSS (← CONJ th th)))),
        DISCH_THEN ((fun th => tactic_of do
          let b2 ← ISPEC tSND th
          let b1 ← ISPEC tFST th
          pure (MP_TAC b1 THEN MP_TAC b2)) o
          MATCH_MP COUNTABLE_IMAGE) THEN
        REWRITE_TAC [IMP_IMP, ← GSYM COUNTABLE_UNION]] THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] COUNTABLE_SUBSET) THEN
      REWRITE_TAC [SUBSET, FORALL_PAIR_THM, IN_ELIM_PAIR_THM] THEN
      REWRITE_TAC [IN_CROSS, fld, IN_IMAGE, IN_ELIM_THM, IN_UNION] THEN
      REWRITE_TAC [EXISTS_PAIR_THM, PAIR_EQ] THEN SET_TAC []))

  let COUNTABLE_UNION_OF_EMPTY ← prove
   r"!P:(A->bool)->bool. (COUNTABLE UNION_OF P) {}"
   (SIMP_TAC [UNION_OF_EMPTY, COUNTABLE_EMPTY])

  let COUNTABLE_INTERSECTION_OF_EMPTY ← prove
   r"!P:(A->bool)->bool. (COUNTABLE INTERSECTION_OF P) UNIV"
   (SIMP_TAC [INTERSECTION_OF_EMPTY, COUNTABLE_EMPTY])

  let COUNTABLE_UNION_OF_INC ← prove
   r"!P s:A->bool. P s ==> (COUNTABLE UNION_OF P) s"
   (SIMP_TAC [UNION_OF_INC, COUNTABLE_SING])

  let COUNTABLE_INTERSECTION_OF_INC ← prove
   r"!P s:A->bool. P s ==> (COUNTABLE INTERSECTION_OF P) s"
   (SIMP_TAC [INTERSECTION_OF_INC, COUNTABLE_SING])

  let COUNTABLE_UNION_OF_COMPLEMENT ← prove
   r"!P s. (COUNTABLE UNION_OF P) s <=>
         (COUNTABLE INTERSECTION_OF (\s. P((:A) DIFF s))) ((:A) DIFF s)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [UNION_OF, INTERSECTION_OF] THEN
    EQ_TAC THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"u:(A->bool)->bool") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"IMAGE (\c. (:A) DIFF c) u") THEN
    ASM_SIMP_TAC [COUNTABLE_IMAGE, FORALL_IN_IMAGE, COMPL_COMPL] THEN
    ONCE_REWRITE_TAC [UNIONS_INTERS, INTERS_UNIONS] THEN
    REWRITE_TAC [← SET_RULE (← q r"{f y | y IN IMAGE g s} = IMAGE (\x. f(g x)) s")] THEN
    ASM_REWRITE_TAC [IMAGE_ID, COMPL_COMPL])

  let COUNTABLE_INTERSECTION_OF_COMPLEMENT ← prove
   r"!P s. (COUNTABLE INTERSECTION_OF P) s <=>
         (COUNTABLE UNION_OF (\s. P((:A) DIFF s))) ((:A) DIFF s)"
   (REWRITE_TAC [COUNTABLE_UNION_OF_COMPLEMENT] THEN
    REWRITE_TAC [ETA_AX, COMPL_COMPL])

  let COUNTABLE_UNION_OF_EXPLICIT ← prove
   r"!P s:A->bool.
        P {}
        ==> ((COUNTABLE UNION_OF P) s <=>
             ?t. (!n. P(t n)) /\ UNIONS {t n | n IN (:num)} = s)"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN
    REWRITE_TAC [UNION_OF, LEFT_IMP_EXISTS_THM] THENL
     [X_GEN_TAC (← q r"u:(A->bool)->bool") THEN
      ASM_CASES_TAC (← q r"u:(A->bool)->bool = {}") THENL
       [ASM_REWRITE_TAC [UNIONS_0] THEN
        DISCH_THEN (SUBST1_TAC o SYM o (fun (th : thm) => lastThm (CONJUNCTS th))) THEN
        EXISTS_TAC (← q r"(\n. {}):num->A->bool") THEN
        ASM_REWRITE_TAC [UNIONS_GSPEC, NOT_IN_EMPTY, EMPTY_GSPEC],
        STRIP_TAC THEN
        MP_TAC (← ISPEC (← q r"u:(A->bool)->bool") COUNTABLE_AS_IMAGE) THEN
        ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC []],
      X_GEN_TAC (← q r"t:num->A->bool") THEN STRIP_TAC THEN
      EXISTS_TAC (← q r"{t n:A->bool | n IN (:num)}") THEN
      ASM_REWRITE_TAC [FORALL_IN_GSPEC] THEN
      SIMP_TAC [SIMPLE_IMAGE, COUNTABLE_IMAGE, COUNTABLE_SUBSET_NUM]])

  let COUNTABLE_UNION_OF_ASCENDING ← prove
   r"!P s:A->bool.
        P {} /\ (!t u. P t /\ P u ==> P(t UNION u))
        ==> ((COUNTABLE UNION_OF P) s <=>
             ?t. (!n. P(t n)) /\
                 (!n. t n SUBSET t(SUC n)) /\
                 UNIONS {t n | n IN (:num)} = s)"
   (← do
    let s2 ← SET_RULE (← q r"{f x | x = a} = {f a}")
    let s1 ← SET_RULE (← q r"{f x | P x \/ Q x} = {f x | P x} UNION {f x | Q x}")
    pure (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [COUNTABLE_UNION_OF_EXPLICIT] THEN
      EQ_TAC THENL [ALL_TAC, MESON_TAC []] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"t:num->A->bool") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"(\n. UNIONS {t m | m <= n}):num->A->bool") THEN
      RULE_ASSUM_TAC (REWRITE_RULE [FORALL_IN_IMAGE, IN_UNIV]) THEN
      REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
       [INDUCT_TAC THEN REWRITE_TAC [LE] THEN
        REWRITE_TAC [s1, s2, UNIONS_UNION] THEN
        ASM_SIMP_TAC [UNIONS_1],
        REWRITE_TAC [UNIONS_GSPEC, LE] THEN SET_TAC [],
        FIRST_X_ASSUM (SUBST1_TAC o SYM o (fun (th : thm) => lastThm (CONJUNCTS th))) THEN
        REWRITE_TAC [UNIONS_GSPEC, IN_ELIM_THM, IN_UNIV] THEN
        GEN_REWRITE_TAC id [EXTENSION] THEN
        REWRITE_TAC [UNIONS_IMAGE, IN_ELIM_THM, IN_UNIV] THEN
        MESON_TAC [LE_REFL]]))

  let COUNTABLE_UNION_OF_IDEMPOT ← prove
   r"!P:(A->bool)->bool.
        COUNTABLE UNION_OF COUNTABLE UNION_OF P = COUNTABLE UNION_OF P"
   (GEN_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"s:A->bool") THEN
    EQ_TAC THEN REWRITE_TAC [COUNTABLE_UNION_OF_INC] THEN
    REWRITE_TAC [UNION_OF, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"u:(A->bool)->bool") THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM)) THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"f:(A->bool)->(A->bool)->bool") THEN DISCH_TAC THEN
    EXISTS_TAC
      (← q r"IMAGE SND {s,t | s IN u /\ t IN (f:(A->bool)->(A->bool)->bool) s}") THEN
    ASM_SIMP_TAC [COUNTABLE_IMAGE, COUNTABLE_PRODUCT_DEPENDENT] THEN
    REWRITE_TAC [FORALL_IN_IMAGE, FORALL_IN_GSPEC] THEN
    CONJ_TAC THENL [ASM SET_TAC [], REWRITE_TAC [UNIONS_IMAGE]] THEN
    REWRITE_TAC [EXISTS_IN_GSPEC] THEN ASM SET_TAC [])

  let COUNTABLE_INTERSECTION_OF_IDEMPOT ← prove
   r"!P:(A->bool)->bool.
        COUNTABLE INTERSECTION_OF COUNTABLE INTERSECTION_OF P =
        COUNTABLE INTERSECTION_OF P"
   (REWRITE_TAC [COMPL_COMPL, ETA_AX, ← REWRITE_RULE [← GSYM FUN_EQ_THM, ETA_AX]
                COUNTABLE_INTERSECTION_OF_COMPLEMENT] THEN
    REWRITE_TAC [COUNTABLE_UNION_OF_IDEMPOT])

  let COUNTABLE_UNION_OF_UNIONS ← prove
   r"!P u:(A->bool)->bool.
        COUNTABLE u /\ (!s. s IN u ==> (COUNTABLE UNION_OF P) s)
        ==> (COUNTABLE UNION_OF P) (UNIONS u)"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM COUNTABLE_UNION_OF_IDEMPOT] THEN
    ONCE_REWRITE_TAC [UNION_OF] THEN REWRITE_TAC [] THEN
    EXISTS_TAC (← q r"u:(A->bool)->bool") THEN ASM_REWRITE_TAC [])

  let COUNTABLE_UNION_OF_UNION ← prove
   r"!P s t. (COUNTABLE UNION_OF P) s /\ (COUNTABLE UNION_OF P) t
           ==> (COUNTABLE UNION_OF P) (s UNION t)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM UNIONS_2] THEN
    MATCH_MP_TAC COUNTABLE_UNION_OF_UNIONS THEN
    ASM_REWRITE_TAC [COUNTABLE_INSERT, FORALL_IN_INSERT] THEN
    REWRITE_TAC [COUNTABLE_EMPTY, NOT_IN_EMPTY])

  let COUNTABLE_INTERSECTION_OF_INTERS ← prove
   r"!P u:(A->bool)->bool.
        COUNTABLE u /\ (!s. s IN u ==> (COUNTABLE INTERSECTION_OF P) s)
        ==> (COUNTABLE INTERSECTION_OF P) (INTERS u)"
   (REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [← GSYM COUNTABLE_INTERSECTION_OF_IDEMPOT] THEN
    ONCE_REWRITE_TAC [INTERSECTION_OF] THEN REWRITE_TAC [] THEN
    EXISTS_TAC (← q r"u:(A->bool)->bool") THEN ASM_REWRITE_TAC [])

  let COUNTABLE_INTERSECTION_OF_INTER ← prove
   r"!P s t. (COUNTABLE INTERSECTION_OF P) s /\ (COUNTABLE INTERSECTION_OF P) t
           ==> (COUNTABLE INTERSECTION_OF P) (s INTER t)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM INTERS_2] THEN
    MATCH_MP_TAC COUNTABLE_INTERSECTION_OF_INTERS THEN
    ASM_REWRITE_TAC [COUNTABLE_INSERT, FORALL_IN_INSERT] THEN
    REWRITE_TAC [COUNTABLE_EMPTY, NOT_IN_EMPTY])

  let COUNTABLE_UNION_OF_INTER_EQ ← prove
   r"!P:(A->bool)->bool.
        (!s t. (COUNTABLE UNION_OF P) s /\ (COUNTABLE UNION_OF P) t
                   ==> (COUNTABLE UNION_OF P) (s INTER t)) <=>
        (!s t. P s /\ P t ==> (COUNTABLE UNION_OF P) (s INTER t))"
   (GEN_TAC THEN
    EQ_TAC THENL [MESON_TAC [COUNTABLE_UNION_OF_INC], DISCH_TAC] THEN
    REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [UNION_OF] THEN
    REWRITE_TAC [] THEN DISCH_THEN (STRIP_ASSUME_TAC o GSYM) THEN
    ASM_REWRITE_TAC [INTER_UNIONS] THEN
    REPLICATE_TAC 2
     (MATCH_MP_TAC COUNTABLE_UNION_OF_UNIONS THEN
      ASM_SIMP_TAC [SIMPLE_IMAGE, COUNTABLE_IMAGE, FORALL_IN_IMAGE] THEN
      REPEAT STRIP_TAC))

  let COUNTABLE_UNION_OF_INTER ← prove
   r"!P:(A->bool)->bool.
        (!s t. P s /\ P t ==> P(s INTER t))
        ==> (!s t. (COUNTABLE UNION_OF P) s /\ (COUNTABLE UNION_OF P) t
                   ==> (COUNTABLE UNION_OF P) (s INTER t))"
   (REWRITE_TAC [COUNTABLE_UNION_OF_INTER_EQ] THEN
    MESON_TAC [COUNTABLE_UNION_OF_INC])

  let COUNTABLE_INTERSECTION_OF_UNION_EQ ← prove
   r"!P:(A->bool)->bool.
        (!s t. (COUNTABLE INTERSECTION_OF P) s /\
               (COUNTABLE INTERSECTION_OF P) t
               ==> (COUNTABLE INTERSECTION_OF P) (s UNION t)) <=>
        (!s t. P s /\ P t ==> (COUNTABLE INTERSECTION_OF P) (s UNION t))"
   (← do
    let m4 ← MESON [COMPL_COMPL] (← q r"(!s. P(UNIV DIFF s)) <=> (!s. P s)")
    let s3 ← SET_RULE
     (← q r"s INTER t = UNIV DIFF ((UNIV DIFF s) UNION (UNIV DIFF t))")
    let m2 ← MESON [COMPL_COMPL] (← q r"(!s. P(UNIV DIFF s)) <=> (!s. P s)")
    let s1 ← SET_RULE
      (← q r"UNIV DIFF (s UNION t) = (UNIV DIFF s) INTER (UNIV DIFF t)")
    pure (ONCE_REWRITE_TAC [COUNTABLE_INTERSECTION_OF_COMPLEMENT] THEN
      REWRITE_TAC [s1] THEN
      REWRITE_TAC [m2] THEN
      REWRITE_TAC [COUNTABLE_UNION_OF_INTER_EQ] THEN
      REWRITE_TAC [s3] THEN
      REWRITE_TAC [m4] THEN
      REWRITE_TAC [COMPL_COMPL]))

  let COUNTABLE_INTERSECTION_OF_UNION ← prove
   r"!P:(A->bool)->bool.
        (!s t. P s /\ P t ==> P(s UNION t))
        ==> (!s t. (COUNTABLE INTERSECTION_OF P) s /\
                   (COUNTABLE INTERSECTION_OF P) t
                   ==> (COUNTABLE INTERSECTION_OF P) (s UNION t))"
   (REWRITE_TAC [COUNTABLE_INTERSECTION_OF_UNION_EQ] THEN
    MESON_TAC [COUNTABLE_INTERSECTION_OF_INC])

  let COUNTABLE_INTERSECTION_OF_UNIONS_NONEMPTY ← prove
   r"!P u:(A->bool)->bool.
        (!s t. P s /\ P t ==> P (s UNION t)) /\
        FINITE u /\ ~(u = {}) /\
        (!s. s IN u ==> (COUNTABLE INTERSECTION_OF P) s)
        ==> (COUNTABLE INTERSECTION_OF P) (UNIONS u)"
   (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    GEN_TAC THEN DISCH_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE [IMP_IMP, RIGHT_IMP_FORALL_THM]) THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC [FORALL_IN_INSERT, NOT_INSERT_EMPTY] THEN
    MAP_EVERY X_GEN_TAC [← q r"s:A->bool", ← q r"u:(A->bool)->bool"] THEN
    ASM_CASES_TAC (← q r"u:(A->bool)->bool = {}") THEN
    ASM_SIMP_TAC [UNIONS_1] THEN REWRITE_TAC [UNIONS_INSERT] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP COUNTABLE_INTERSECTION_OF_UNION) THEN
    ASM_SIMP_TAC [])

  let COUNTABLE_INTERSECTION_OF_UNIONS ← prove
   r"!P u:(A->bool)->bool.
        (COUNTABLE INTERSECTION_OF P) {} /\
        (!s t. P s /\ P t ==> P (s UNION t)) /\
        FINITE u /\
        (!s. s IN u ==> (COUNTABLE INTERSECTION_OF P) s)
        ==> (COUNTABLE INTERSECTION_OF P) (UNIONS u)"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_CASES_TAC (← q r"u:(A->bool)->bool = {}") THEN
    ASM_REWRITE_TAC [UNIONS_0] THEN STRIP_TAC THEN
    MATCH_MP_TAC COUNTABLE_INTERSECTION_OF_UNIONS_NONEMPTY THEN
    ASM_REWRITE_TAC [])

  -- @@RETURN BEGIN
  return { COUNTABLE_CART, EXISTS_COUNTABLE_SUBSET_IMAGE_INJ,
           FORALL_COUNTABLE_SUBSET_IMAGE_INJ, EXISTS_COUNTABLE_SUBSET_IMAGE,
           FORALL_COUNTABLE_SUBSET_IMAGE, COUNTABLE_SUBSET_IMAGE, COUNTABLE_IMAGE_EQ,
           COUNTABLE_IMAGE_EQ_INJ, COUNTABLE_FLD, COUNTABLE_UNION_OF_EMPTY,
           COUNTABLE_INTERSECTION_OF_EMPTY, COUNTABLE_UNION_OF_INC,
           COUNTABLE_INTERSECTION_OF_INC, COUNTABLE_UNION_OF_COMPLEMENT,
           COUNTABLE_INTERSECTION_OF_COMPLEMENT, COUNTABLE_UNION_OF_EXPLICIT,
           COUNTABLE_UNION_OF_ASCENDING, COUNTABLE_UNION_OF_IDEMPOT,
           COUNTABLE_INTERSECTION_OF_IDEMPOT, COUNTABLE_UNION_OF_UNIONS,
           COUNTABLE_UNION_OF_UNION, COUNTABLE_INTERSECTION_OF_INTERS,
           COUNTABLE_INTERSECTION_OF_INTER, COUNTABLE_UNION_OF_INTER_EQ,
           COUNTABLE_UNION_OF_INTER, COUNTABLE_INTERSECTION_OF_UNION_EQ,
           COUNTABLE_INTERSECTION_OF_UNION, COUNTABLE_INTERSECTION_OF_UNIONS_NONEMPTY,
           COUNTABLE_INTERSECTION_OF_UNIONS }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- More countable unions/intersections; a countable chain has an omega-chain; -/
/- cardinality of lists, cartesian powers and the reals.                     -/
/- (card.ml 2199-2557)                                                       -/
/- ------------------------------------------------------------------------- -/

structure Reals where
  -- @@FIELDS
  COUNTABLE_UNION_OF_INTERS_NONEMPTY : thm
  COUNTABLE_UNION_OF_INTERS : thm
  COUNTABLE_DISJOINT_UNION_OF_IDEMPOT : thm
  COUNTABLE_ASCENDING_CHAIN : thm
  COUNTABLE_DESCENDING_CHAIN : thm
  CARD_EQ_LIST_GEN : thm
  CARD_EQ_LIST : thm
  CARD_EQ_CART : thm
  CARD_EQ_REAL : thm
  UNCOUNTABLE_REAL : thm
  CARD_EQ_REAL_IMP_UNCOUNTABLE : thm
  COUNTABLE_IMP_CARD_LT_REAL : thm
  CARD_LT_NUM_REAL : thm
  CARD_EQ_REAL_SUBSET : thm
  deriving Inhabited

@[nospecialize]
def setupReals [HolBase] (D : CardDeps) (BBasics : Basics) (BOrder : Order) (BArith : Arith) (BSquare : Square) (BCountable : Countable) (BUnionOf : UnionOf) :
    ExceptT String IO Reals := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, INDUCT_TAC,
        LIST_INDUCT_TAC, MESON, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC,
        REAL_RAT_REDUCE_CONV, SET_RULE, SET_TAC, WF_INDUCT_TAC, .. } := D
  let { ADD1, ARITH, CART_EQ, CONJ_ACI, CONS_11, CONTRAPOS_THM, COUNTABLE,
        DIMINDEX_GE_1, EL, EQ_SYM_EQ, EXISTS_IN_GSPEC, EXISTS_PAIR_THM, EXISTS_REFL,
        EXTENSION, FINITE_EMPTY, FINITE_INDUCT_STRONG, FINITE_INTER, FINITE_NUMSEG,
        FORALL_CURRY, FORALL_IN_GSPEC, FORALL_IN_IMAGE, FORALL_IN_INSERT,
        FORALL_PAIR_THM, FUN_EQ_THM, HD, IMAGE_CLAUSES, IMP_CONJ, IMP_IMP, IN, .. } := D.core1
  let { INFINITE, INJECTIVE_LEFT_INVERSE, INTER, INTERS_0, INTERS_1, INTERS_GSPEC,
        INTERS_IMAGE, INTERS_INSERT, INTER_COMM, INTER_SUBSET, INTER_UNIV,
        IN_ELIM_PAIR_THM, IN_ELIM_THM, IN_NUMSEG, IN_UNIV, ITLIST, LAMBDA_BETA,
        LEFT_IMP_EXISTS_THM, LENGTH, LENGTH_EQ_NIL, LE_0, LE_1, LE_C, LE_REFL, LT,
        LT_SUC, MEM, MEMBER_NOT_EMPTY, MONO_EXISTS, NOT_FORALL_THM, NOT_INSERT_EMPTY,
        NOT_LE, NOT_SUC, NUMSEG_CLAUSES, NUMSEG_EMPTY, NUMSEG_SING, OR_EXISTS_THM,
        PAIRWISE_IMAGE, PAIRWISE_SING, PAIR_EQ, REAL_ADD_RID, REAL_ARCH, REAL_ARCH_LT,
        REAL_BOUNDS_LT, REAL_EQ_ADD_LCANCEL, REAL_EQ_MUL_LCANCEL, REAL_INV_MUL,
        REAL_LET_TRANS, REAL_LE_DIV, REAL_LE_INV_EQ, .. } := D.core2
  let { REAL_LE_MUL, REAL_LT_DIV, REAL_LT_IMP_LE, REAL_LT_INV_EQ, REAL_LT_LMUL_EQ,
        REAL_MUL_ASSOC, REAL_OF_NUM_LT, REAL_OF_NUM_SUC, REAL_POS, REAL_POW_1,
        REAL_POW_ADD, REAL_POW_LE, REAL_POW_LT, REAL_SHRINK_EQ, REAL_SHRINK_RANGE,
        REAL_SUB_LT, REAL_SUP_LE, REAL_WLOG_LT, RIGHT_EXISTS_AND_THM,
        RIGHT_FORALL_IMP_THM, RIGHT_IMP_EXISTS_THM, RIGHT_IMP_FORALL_THM, SKOLEM_THM,
        SUBSET_NUMSEG, SUC_INJ, SUM_CLAUSES, SUM_CLAUSES_LEFT, SUM_CLAUSES_RIGHT,
        SUM_COMBINE_R, SUM_EQ_NUMSEG, SUM_RESTRICT_SET, SUM_SING, SUM_SUBSET_SIMPLE,
        SUP, SWAP_FORALL_THM, TL, UNIONS_0, UNIONS_GSPEC, UNIONS_IMAGE, UNIONS_INSERT,
        UNION_EMPTY, UNION_OF, UNION_OF_INC, ge_c, le_c, num_INDUCTION, num_INFINITE,
        num_WOP, pairwise, real_div, real_pow, .. } := D.core3
  let { CARD_EQ_IMP_LE, CARD_EQ_SYM, CARD_LE_REFL, CARD_LE_TRANS, CARD_LTE_TRANS,
        CARD_LT_IMP_LE, .. } := BBasics
  let { CARD_LE_ANTISYM, CARD_LE_UNIV, CARD_NOT_LE, INFINITE_CARD_LE, .. } := BOrder
  let { CARD_LE_MUL, mul_c, .. } := BArith
  let { CARD_MUL2_ABSORB_LE, CARD_MUL_ABSORB_LE, .. } := BSquare
  let { CANTOR_THM_UNIV, CARD_EQ_COUNTABLE, CARD_LE_COUNTABLE, COUNTABLE_AS_IMAGE,
        COUNTABLE_IMAGE, COUNTABLE_PRODUCT_DEPENDENT, COUNTABLE_SING, NUM_COUNTABLE, .. } := BCountable
  let { COUNTABLE_UNION_OF_INTER, .. } := BUnionOf
  -- @@SCOPE END

  let COUNTABLE_UNION_OF_INTERS_NONEMPTY ← prove
   r"!P u:(A->bool)->bool.
        (!s t. P s /\ P t ==> P (s INTER t)) /\
        FINITE u /\ ~(u = {}) /\
        (!s. s IN u ==> (COUNTABLE UNION_OF P) s)
        ==> (COUNTABLE UNION_OF P) (INTERS u)"
   (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    GEN_TAC THEN DISCH_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE [IMP_IMP, RIGHT_IMP_FORALL_THM]) THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC [FORALL_IN_INSERT, NOT_INSERT_EMPTY] THEN
    MAP_EVERY X_GEN_TAC [← q r"s:A->bool", ← q r"u:(A->bool)->bool"] THEN
    ASM_CASES_TAC (← q r"u:(A->bool)->bool = {}") THEN
    ASM_SIMP_TAC [INTERS_1] THEN REWRITE_TAC [INTERS_INSERT] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP COUNTABLE_UNION_OF_INTER) THEN
    ASM_SIMP_TAC [])

  let COUNTABLE_UNION_OF_INTERS ← prove
   r"!P u:(A->bool)->bool.
        (COUNTABLE UNION_OF P) (:A) /\
        (!s t. P s /\ P t ==> P (s INTER t)) /\
        FINITE u /\
        (!s. s IN u ==> (COUNTABLE UNION_OF P) s)
        ==> (COUNTABLE UNION_OF P) (INTERS u)"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_CASES_TAC (← q r"u:(A->bool)->bool = {}") THEN
    ASM_REWRITE_TAC [INTERS_0] THEN STRIP_TAC THEN
    MATCH_MP_TAC COUNTABLE_UNION_OF_INTERS_NONEMPTY THEN
    ASM_REWRITE_TAC [])

  let COUNTABLE_DISJOINT_UNION_OF_IDEMPOT ← prove
   r"!P:(A->bool)->bool.
        ((COUNTABLE INTER pairwise DISJOINT) UNION_OF
         (COUNTABLE INTER pairwise DISJOINT) UNION_OF P) =
        (COUNTABLE INTER pairwise DISJOINT) UNION_OF P"
   (← do
    let ui ← REWRITE_RULE [IMP_CONJ] UNION_OF_INC
    let s1 ← SET_RULE (← q r"s INTER t = \x. s x /\ t x")
    pure (GEN_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"s:A->bool") THEN
      EQ_TAC THENL
       [REWRITE_TAC [s1],
        MATCH_MP_TAC ui THEN
        REWRITE_TAC [INTER, IN_ELIM_THM] THEN REWRITE_TAC [IN] THEN
        REWRITE_TAC [COUNTABLE_SING, PAIRWISE_SING]] THEN
      REWRITE_TAC [UNION_OF, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"u:(A->bool)->bool") THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM)) THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
      REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"f:(A->bool)->(A->bool)->bool") THEN DISCH_TAC THEN
      EXISTS_TAC
        (← q r"IMAGE SND {s,t | s IN u /\ t IN (f:(A->bool)->(A->bool)->bool) s}") THEN
      ASM_SIMP_TAC [COUNTABLE_IMAGE, COUNTABLE_PRODUCT_DEPENDENT] THEN
      REWRITE_TAC [FORALL_IN_IMAGE, FORALL_IN_GSPEC] THEN
      REWRITE_TAC [UNIONS_IMAGE, EXISTS_IN_GSPEC, PAIRWISE_IMAGE] THEN
      CONJ_TAC THENL [REWRITE_TAC [pairwise], ASM SET_TAC []] THEN
      REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_GSPEC] THEN
      MAP_EVERY (fun x => X_GEN_TAC x THEN DISCH_TAC)
       [← q r"s1:A->bool", ← q r"t1:A->bool", ← q r"s2:A->bool", ← q r"t2:A->bool"] THEN
      DISCH_THEN (fun _ => ALL_TAC) THEN ASM_CASES_TAC (← q r"s2:A->bool = s1") THEN
      RULE_ASSUM_TAC (REWRITE_RULE [pairwise]) THENL
       [ASM_MESON_TAC [], ASM SET_TAC []]))

  -- A countable chain has an "equivalent" omega-chain.

  let COUNTABLE_ASCENDING_CHAIN ← prove
   r"!f:(A->bool)->bool.
        COUNTABLE f /\ ~(f = {}) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
        ==> ?u. (!n. u(n) IN f) /\ (!n. u(n) SUBSET u(SUC n)) /\
                UNIONS {u n | n IN (:num)} = UNIONS f"
   (← do
    let s3 ← SET_RULE (← q r"a UNION b = b <=> a SUBSET b")
    let s2 ← SET_RULE (← q r"a UNION b = a <=> b SUBSET a")
    let m1 ← MESON [] (← q r"a IN f /\ b IN f /\ (a UNION b = a \/ a UNION b = b)
        ==> (a UNION b) IN f")
    pure (REPEAT STRIP_TAC THEN
      MP_TAC (← ISPEC (← q r"f:(A->bool)->bool") COUNTABLE_AS_IMAGE) THEN
      ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"b:num->A->bool") THEN DISCH_THEN (ASSUME_TAC o SYM) THEN
      EXISTS_TAC (← q r"\n. UNIONS(IMAGE (b:num->A->bool) (0..n))") THEN
      ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
       [INDUCT_TAC THEN
        ASM_REWRITE_TAC [NUMSEG_CLAUSES, LE_0, IMAGE_CLAUSES] THEN
        REWRITE_TAC [UNIONS_0, UNIONS_INSERT, UNION_EMPTY] THENL
         [ASM SET_TAC [], ALL_TAC] THEN
        MATCH_MP_TAC m1 THEN
        ASM_REWRITE_TAC [s2, s3] THEN
        ASM SET_TAC [],
        GEN_TAC THEN REWRITE_TAC [NUMSEG_CLAUSES, LE_0] THEN SET_TAC [],
        EXPAND_TAC "f" THEN REWRITE_TAC [UNIONS_GSPEC, UNIONS_IMAGE] THEN
        REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_UNIV, IN_NUMSEG, LE_0] THEN
        MESON_TAC [LE_REFL]]))

  let COUNTABLE_DESCENDING_CHAIN ← prove
   r"!f:(A->bool)->bool.

        COUNTABLE f /\ ~(f = {}) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
        ==> ?u. (!n. u(n) IN f) /\ (!n. u(SUC n) SUBSET u(n)) /\
                INTERS {u n | n IN (:num)} = INTERS f"
   (← do
    let s3 ← SET_RULE (← q r"a INTER b = b <=> b SUBSET a")
    let s2 ← SET_RULE (← q r"a INTER b = a <=> a SUBSET b")
    let m1 ← MESON [] (← q r"a IN f /\ b IN f /\ (a INTER b = a \/ a INTER b = b)
        ==> (a INTER b) IN f")
    pure (REPEAT STRIP_TAC THEN
      MP_TAC (← ISPEC (← q r"f:(A->bool)->bool") COUNTABLE_AS_IMAGE) THEN
      ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"b:num->A->bool") THEN DISCH_THEN (ASSUME_TAC o SYM) THEN
      EXISTS_TAC (← q r"\n. INTERS(IMAGE (b:num->A->bool) (0..n))") THEN
      ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
       [INDUCT_TAC THEN
        ASM_REWRITE_TAC [NUMSEG_CLAUSES, LE_0, IMAGE_CLAUSES] THEN
        REWRITE_TAC [INTERS_0, INTERS_INSERT, INTER_UNIV] THENL
         [ASM SET_TAC [], ALL_TAC] THEN
        MATCH_MP_TAC m1 THEN
        ASM_REWRITE_TAC [s2, s3] THEN
        ASM SET_TAC [],
        GEN_TAC THEN REWRITE_TAC [NUMSEG_CLAUSES, LE_0] THEN SET_TAC [],
        EXPAND_TAC "f" THEN REWRITE_TAC [INTERS_GSPEC, INTERS_IMAGE] THEN
        REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_UNIV, IN_NUMSEG, LE_0] THEN
        MESON_TAC [LE_REFL]]))

  -- Cardinality of infinite list and cartesian product types.

  let CARD_EQ_LIST_GEN ← prove
   r"!s:A->bool. INFINITE(s) ==> {l | !x. MEM x l ==> x IN s} =_c s"
   (GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [← GSYM CARD_LE_ANTISYM] THEN CONJ_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [le_c, IN_UNIV] THEN
      EXISTS_TAC (← q r"\x:A. [x]") THEN SIMP_TAC [CONS_11, IN_ELIM_THM, MEM]] THEN
    TRANS_TAC CARD_LE_TRANS (← q r"(:num) *_c (s:A->bool)") THEN CONJ_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC CARD_MUL2_ABSORB_LE THEN
      ASM_REWRITE_TAC [← GSYM INFINITE_CARD_LE, CARD_LE_REFL]] THEN
    SUBGOAL_THEN (← q r"s *_c s <=_c (s:A->bool)") MP_TAC THENL
     [MATCH_MP_TAC CARD_MUL2_ABSORB_LE THEN ASM_REWRITE_TAC [CARD_LE_REFL],
      ALL_TAC] THEN
    REWRITE_TAC [le_c, mul_c, FORALL_PAIR_THM, IN_ELIM_PAIR_THM, PAIR_EQ] THEN
    REWRITE_TAC [IN_UNIV, LEFT_IMP_EXISTS_THM] THEN
    GEN_REWRITE_TAC id [FORALL_CURRY] THEN
    X_GEN_TAC (← q r"pair:A->A->A") THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"?b:A. b IN s") CHOOSE_TAC THENL
     [ASM_MESON_TAC [INFINITE, FINITE_EMPTY, MEMBER_NOT_EMPTY], ALL_TAC] THEN
    EXISTS_TAC (← q r"\l. LENGTH l,ITLIST (pair:A->A->A) l b") THEN
    REWRITE_TAC [PAIR_EQ, RIGHT_EXISTS_AND_THM, ← GSYM EXISTS_REFL] THEN
    SUBGOAL_THEN
     (← q r"!l:A list. (!x. MEM x l ==> x IN s) ==> (ITLIST pair l b) IN s")
    ASSUME_TAC THENL
     [LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [MEM, ITLIST] THEN ASM_MESON_TAC [],
      CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC]] THEN
    ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    LIST_INDUCT_TAC THEN SIMP_TAC [LENGTH_EQ_NIL, LENGTH] THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [LENGTH, NOT_SUC] THEN
    REWRITE_TAC [ITLIST, SUC_INJ, MEM, CONS_11] THEN
    REPEAT STRIP_TAC THENL [ALL_TAC, FIRST_X_ASSUM MATCH_MP_TAC] THEN
    ASM_MESON_TAC [])

  let CARD_EQ_LIST ← prove
   r"INFINITE(:A) ==> (:A list) =_c (:A)"
   (DISCH_THEN (MP_TAC o MATCH_MP CARD_EQ_LIST_GEN) THEN
    REWRITE_TAC [IN_UNIV, ← SET_RULE (← q r"{x | T} = UNIV")])

  let CARD_EQ_CART ← prove
   r"INFINITE(:A) ==> (:A^N) =_c (:A)"
   (← do
    let ar ← ARITH_RULE (← q r"i < n + 1 <=> i <= n")
    pure (DISCH_TAC THEN REWRITE_TAC [← GSYM CARD_LE_ANTISYM] THEN CONJ_TAC THENL
       [ALL_TAC,
        REWRITE_TAC [le_c, IN_UNIV] THEN
        EXISTS_TAC (← q r"(\x. lambda i. x):A->A^N") THEN
        SIMP_TAC [CART_EQ, LAMBDA_BETA] THEN
        MESON_TAC [LE_REFL, DIMINDEX_GE_1]] THEN
      TRANS_TAC CARD_LE_TRANS (← q r"(:A list)") THEN
      ASM_SIMP_TAC [CARD_EQ_LIST, CARD_EQ_IMP_LE] THEN REWRITE_TAC [LE_C] THEN
      EXISTS_TAC (← q r"(\l. lambda i. EL i l):(A)list->A^N") THEN
      ASM_SIMP_TAC [CART_EQ, IN_UNIV, LAMBDA_BETA] THEN X_GEN_TAC (← q r"x:A^N") THEN
      SUBGOAL_THEN (← q r"!n f. ?l. !i. i < n ==> EL i l:A = f i") MP_TAC THENL
       [INDUCT_TAC THEN REWRITE_TAC [← CONJUNCT1 LT] THEN X_GEN_TAC (← q r"f:num->A") THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"\i. (f:num->A)(SUC i)")) THEN
        REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"l:A list") THEN
        DISCH_TAC THEN EXISTS_TAC (← q r"CONS ((f:num->A) 0) l") THEN
        INDUCT_TAC THEN ASM_SIMP_TAC [EL, HD, TL, LT_SUC],
        DISCH_THEN (MP_TAC o SPECL [← q r"dimindex(:N)+1", ← q r"\i. (x:A^N)$i"]) THEN
        REWRITE_TAC [LEFT_IMP_EXISTS_THM, ar] THEN
        MESON_TAC []]))

  -- Cardinality of the reals. This is done in a rather laborious way to avoid
  -- any dependence on the theories of analysis.

  let CARD_EQ_REAL ← prove
   r"(:real) =_c (:num->bool)"
   (← do
    let lemma ← prove
     r"!s m n. sum (s INTER (m..n)) (\i. inv(&3 pow i)) < &3 / &2 / &3 pow m"
     (← do
      let l2 ← REAL_ARITH (← q r"inv x < &3 / &2 / x <=> &0 < inv x")
      let l1 ← REAL_ARITH (← q r"a + j:real <= k ==> x < j ==> a + x < k")
      pure (REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC (← q r"sum (m..n) (\i. inv(&3 pow i))") THEN CONJ_TAC THENL
         [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
          SIMP_TAC [FINITE_NUMSEG, INTER_SUBSET, REAL_LE_INV_EQ,
                   REAL_POW_LE, REAL_POS],
          WF_INDUCT_TAC (← q r"n - m:num") THEN
          ASM_CASES_TAC (← q r"m:num <= n") THENL
           [ASM_SIMP_TAC [SUM_CLAUSES_LEFT] THEN ASM_CASES_TAC (← q r"m + 1 <= n") THENL
             [FIRST_X_ASSUM (MP_TAC o SPECL [← q "n:num", ← q "SUC m"]) THEN
              ANTS_TAC THENL [ASM_ARITH_TAC, REWRITE_TAC [ADD1, REAL_POW_ADD]] THEN
              MATCH_MP_TAC l1 THEN
              REWRITE_TAC [real_div, REAL_INV_MUL, REAL_POW_1] THEN REAL_ARITH_TAC,
              ALL_TAC],
            ALL_TAC] THEN
          RULE_ASSUM_TAC (REWRITE_RULE [NOT_LE, ← GSYM NUMSEG_EMPTY]) THEN
          ASM_REWRITE_TAC [SUM_CLAUSES, REAL_ADD_RID] THEN
          REWRITE_TAC [l2] THEN
          SIMP_TAC [REAL_LT_INV_EQ, REAL_LT_DIV, REAL_POW_LT, REAL_OF_NUM_LT,
                   ARITH]]))
    -- Built when OCaml builds the tactic, last first.
    let m11 ← REAL_ARITH (← q r"&1 / &2 * x < x <=> &0 < x")
    let m10 ← ARITH_RULE (← q r"~(n = 0) /\ m <= n - 1 ==> m < n")
    let m9 ← REAL_ARITH (← q r"s:real = t /\ d < e ==> s + d < t + e")
    let m8 ← SET_RULE (← q r"s SUBSET t ==> u INTER s SUBSET u INTER t")
    let m7 ← REAL_ARITH (← q r"y:real <= x /\ &0 <= d ==> y <= x + d")
    let m6 ← REAL_ARITH (← q r"!d. s:real = t + d /\ d <= e ==> s <= t + e")
    let m5 ← REAL_ARITH (← q r"!z:real. y < z /\ z <= x ==> ~(x = y)")
    let m4 ← MESON [IN]
     (← q r"((!P Q n. R P Q n <=> R Q P n) /\ (!P Q. S P Q <=> S Q P)) /\
      (!P Q. (?n. n IN P /\ ~(n IN Q) /\ R P Q n) ==> S P Q)
      ==> !P Q. (?n:num. ~(n IN P <=> n IN Q) /\ R P Q n) ==> S P Q")
    let m3 ← REAL_ARITH (← q r"x:real < &0 <=> ~(&0 <= x)")
    let m2 ← TAUT (← q r"~p ==> p ==> q")
    let m1 ← MESON [] (← q r"P 0 \/ P 1 ==> ?n. P n")
    let tp ← q "p:num"
    let tq ← q "q:num"
    pure (REWRITE_TAC [← GSYM CARD_LE_ANTISYM] THEN CONJ_TAC THENL
       [TRANS_TAC CARD_LE_TRANS (← q r"(:num) *_c (:num->bool)") THEN CONJ_TAC THENL
         [ALL_TAC,
          MATCH_MP_TAC CARD_MUL2_ABSORB_LE THEN REWRITE_TAC [INFINITE_CARD_LE] THEN
          SIMP_TAC [CANTOR_THM_UNIV, CARD_LT_IMP_LE, CARD_LE_REFL]] THEN
        TRANS_TAC CARD_LE_TRANS (← q r"(:num) *_c {x:real | &0 <= x}") THEN CONJ_TAC THENL
         [REWRITE_TAC [LE_C, mul_c, EXISTS_PAIR_THM, IN_ELIM_PAIR_THM, IN_UNIV] THEN
          EXISTS_TAC (← q r"\(n,x:real). --(&1) pow n * x") THEN X_GEN_TAC (← q "x:real") THEN
          MATCH_MP_TAC m1 THEN
          REWRITE_TAC [OR_EXISTS_THM] THEN EXISTS_TAC (← q "abs x") THEN
          REWRITE_TAC [IN_ELIM_THM] THEN REAL_ARITH_TAC,
          ALL_TAC] THEN
        MATCH_MP_TAC CARD_LE_MUL THEN REWRITE_TAC [CARD_LE_REFL] THEN
        MP_TAC (← ISPECL [← q "(:num)", ← q "(:num)"] CARD_MUL_ABSORB_LE) THEN
        REWRITE_TAC [CARD_LE_REFL, num_INFINITE] THEN
        REWRITE_TAC [le_c, mul_c, IN_UNIV, FORALL_PAIR_THM, IN_ELIM_PAIR_THM] THEN
        REWRITE_TAC [← GSYM FORALL_PAIR_THM, INJECTIVE_LEFT_INVERSE] THEN
        REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
        MAP_EVERY X_GEN_TAC [← q r"pair:num#num->num", ← q r"unpair:num->num#num"] THEN
        DISCH_TAC THEN
        EXISTS_TAC (← q r"\x:real n:num. &(FST(unpair n)) * x <= &(SND(unpair n))") THEN
        MATCH_MP_TAC REAL_WLOG_LT THEN REWRITE_TAC [IN_ELIM_THM, FUN_EQ_THM] THEN
        CONJ_TAC THENL [REWRITE_TAC [EQ_SYM_EQ, CONJ_ACI], ALL_TAC] THEN
        MAP_EVERY X_GEN_TAC [← q "x:real", ← q "y:real"] THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM (MP_TAC o GENL [tp, tq] o
          SPEC (← q r"(pair:num#num->num) (p,q)")) THEN
        ASM_REWRITE_TAC [] THEN MATCH_MP_TAC m2 THEN
        MP_TAC (← SPEC (← q r"y - x:real") REAL_ARCH) THEN
        ASM_REWRITE_TAC [REAL_SUB_LT, NOT_FORALL_THM] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"&2")) THEN MATCH_MP_TAC MONO_EXISTS THEN
        X_GEN_TAC (← q "p:num") THEN DISCH_TAC THEN
        MP_TAC (← ISPEC (← q r"&p * x:real") REAL_ARCH_LT) THEN
        GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN MATCH_MP_TAC MONO_EXISTS THEN
        MATCH_MP_TAC num_INDUCTION THEN
        ASM_SIMP_TAC [REAL_LE_MUL, REAL_POS, m3] THEN
        X_GEN_TAC (← q "q:num") THEN REWRITE_TAC [← GSYM REAL_OF_NUM_SUC] THEN
        DISCH_THEN (fun _ => ALL_TAC) THEN STRIP_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q "q:num")) THEN
        REWRITE_TAC [LT] THEN ASM_REAL_ARITH_TAC,
        REWRITE_TAC [le_c, IN_UNIV] THEN
        EXISTS_TAC (← q r"\s:num->bool. sup { sum (s INTER (0..n)) (\i. inv(&3 pow i)) |
                                        n IN (:num) }") THEN
        MAP_EVERY X_GEN_TAC [← q r"x:num->bool", ← q r"y:num->bool"] THEN
        ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
        REWRITE_TAC [EXTENSION, NOT_FORALL_THM] THEN
        GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
        MAP_EVERY (fun w => SPEC_TAC (w, w)) [← q r"y:num->bool", ← q r"x:num->bool"] THEN
        MATCH_MP_TAC m4 THEN
        CONJ_TAC THENL [REWRITE_TAC [EQ_SYM_EQ], REWRITE_TAC []] THEN
        MAP_EVERY X_GEN_TAC [← q r"x:num->bool", ← q r"y:num->bool"] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "n:num") STRIP_ASSUME_TAC) THEN
        MATCH_MP_TAC m5 THEN
        EXISTS_TAC (← q r"sum (x INTER (0..n)) (\i. inv(&3 pow i))") THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC
           (← q r"sum (y INTER (0..n)) (\i. inv(&3 pow i)) +
            &3 / &2 / &3 pow (SUC n)") THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC REAL_SUP_LE THEN
            CONJ_TAC THENL [SET_TAC [], REWRITE_TAC [FORALL_IN_GSPEC, IN_UNIV]] THEN
            X_GEN_TAC (← q "p:num") THEN ASM_CASES_TAC (← q "n:num <= p") THENL
             [MATCH_MP_TAC m6 THEN
              EXISTS_TAC (← q r"sum(y INTER (n+1..p)) (\i. inv (&3 pow i))") THEN
              CONJ_TAC THENL
               [ONCE_REWRITE_TAC [INTER_COMM] THEN
                REWRITE_TAC [INTER, SUM_RESTRICT_SET] THEN
                ASM_SIMP_TAC [SUM_COMBINE_R, LE_0],
                SIMP_TAC [ADD1, lemma, REAL_LT_IMP_LE]],
              MATCH_MP_TAC m7 THEN
              SIMP_TAC [REAL_LE_DIV, REAL_POS, REAL_POW_LE] THEN
              MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
              SIMP_TAC [REAL_LE_INV_EQ, REAL_POW_LE, REAL_POS] THEN
              SIMP_TAC [FINITE_INTER, FINITE_NUMSEG] THEN MATCH_MP_TAC
               m8 THEN
              REWRITE_TAC [SUBSET_NUMSEG] THEN ASM_ARITH_TAC],
            ONCE_REWRITE_TAC [INTER_COMM] THEN
            REWRITE_TAC [INTER, SUM_RESTRICT_SET] THEN ASM_CASES_TAC (← q "n = 0") THENL
             [FIRST_X_ASSUM SUBST_ALL_TAC THEN
              ASM_REWRITE_TAC [SUM_SING, NUMSEG_SING, real_pow] THEN REAL_ARITH_TAC,
              ASM_SIMP_TAC [SUM_CLAUSES_RIGHT, LE_1, LE_0, REAL_ADD_RID] THEN
              MATCH_MP_TAC m9 THEN
              CONJ_TAC THENL
               [MATCH_MP_TAC SUM_EQ_NUMSEG THEN
                ASM_SIMP_TAC [m10],
                REWRITE_TAC [real_pow, real_div, REAL_INV_MUL, REAL_MUL_ASSOC] THEN
                CONV_TAC REAL_RAT_REDUCE_CONV THEN
                REWRITE_TAC [m11] THEN
                SIMP_TAC [REAL_LT_INV_EQ, REAL_POW_LT, REAL_OF_NUM_LT, ARITH]]]],
          MP_TAC (← ISPEC (← q r"{ sum (x INTER (0..n)) (\i. inv(&3 pow i)) | n IN (:num) }")
              SUP) THEN REWRITE_TAC [FORALL_IN_GSPEC, IN_UNIV] THEN
          ANTS_TAC THENL [ALL_TAC, SIMP_TAC []] THEN
          CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN
          EXISTS_TAC (← q r"&3 / &2 / &3 pow 0") THEN
          SIMP_TAC [lemma, REAL_LT_IMP_LE]]]))

  let UNCOUNTABLE_REAL ← prove
   r"~COUNTABLE(:real)"
   (REWRITE_TAC [COUNTABLE, CARD_NOT_LE, ge_c] THEN
    TRANS_TAC CARD_LTE_TRANS (← q r"(:num->bool)") THEN
    REWRITE_TAC [CANTOR_THM_UNIV] THEN MATCH_MP_TAC CARD_EQ_IMP_LE THEN
    ONCE_REWRITE_TAC [CARD_EQ_SYM] THEN REWRITE_TAC [CARD_EQ_REAL])

  let CARD_EQ_REAL_IMP_UNCOUNTABLE ← prove
   r"!s. s =_c (:real) ==> ~COUNTABLE s"
   (← do
    let cc ← REWRITE_RULE [IMP_CONJ] CARD_EQ_COUNTABLE
    pure (GEN_TAC THEN STRIP_TAC THEN
      DISCH_THEN (MP_TAC o ISPEC (← q r"(:real)") o MATCH_MP cc) THEN
      REWRITE_TAC [UNCOUNTABLE_REAL] THEN ASM_MESON_TAC [CARD_EQ_SYM]))

  let COUNTABLE_IMP_CARD_LT_REAL ← prove
   r"!s:A->bool. COUNTABLE s ==> s <_c (:real)"
   (REWRITE_TAC [← GSYM CARD_NOT_LE] THEN
    ASM_MESON_TAC [CARD_LE_COUNTABLE, UNCOUNTABLE_REAL])

  let CARD_LT_NUM_REAL ← prove
   r"(:num) <_c (:real)"
   (SIMP_TAC [COUNTABLE_IMP_CARD_LT_REAL, NUM_COUNTABLE])

  let CARD_EQ_REAL_SUBSET ← prove
   r"!s a b:real.
        a < b /\ (!x. a < x /\ x < b ==> x IN s) ==> s =_c (:real)"
   (← do
    let ra ← REAL_ARITH
     (← q r"(a < (a + b) / &2 + (b - a) / &2 * x <=>
       (b - a) * -- &1 < (b - a) * x) /\
      ((a + b) / &2 + (b - a) / &2 * x < b <=>
       (b - a) * x < (b - a) * &1)")
    pure (REPEAT STRIP_TAC THEN
      REWRITE_TAC [← GSYM CARD_LE_ANTISYM, CARD_LE_UNIV] THEN
      REWRITE_TAC [le_c, IN_UNIV] THEN
      EXISTS_TAC (← q r"\x. (a + b) / &2 + (b - a) / &2 * x / (&1 + abs x)") THEN
      REWRITE_TAC [REAL_EQ_ADD_LCANCEL, REAL_EQ_MUL_LCANCEL] THEN
      REWRITE_TAC [REAL_SHRINK_EQ] THEN
      CONJ_TAC THENL [ALL_TAC, ASM_REAL_ARITH_TAC] THEN
      X_GEN_TAC (← q "x:real") THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC [ra] THEN

      ASM_SIMP_TAC [REAL_LT_LMUL_EQ, REAL_SUB_LT, REAL_BOUNDS_LT] THEN
      REWRITE_TAC [REAL_SHRINK_RANGE]))

  -- @@RETURN BEGIN
  return { COUNTABLE_UNION_OF_INTERS_NONEMPTY, COUNTABLE_UNION_OF_INTERS,
           COUNTABLE_DISJOINT_UNION_OF_IDEMPOT, COUNTABLE_ASCENDING_CHAIN,
           COUNTABLE_DESCENDING_CHAIN, CARD_EQ_LIST_GEN, CARD_EQ_LIST, CARD_EQ_CART,
           CARD_EQ_REAL, UNCOUNTABLE_REAL, CARD_EQ_REAL_IMP_UNCOUNTABLE,
           COUNTABLE_IMP_CARD_LT_REAL, CARD_LT_NUM_REAL, CARD_EQ_REAL_SUBSET }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Cardinal exponentiation.  (card.ml 2559-2826)                             -/
/- ------------------------------------------------------------------------- -/

structure Exp where
  -- @@FIELDS
  exp_c : thm
  EXP_C : thm
  CARD_EXP_UNIV : thm
  CARD_EXP_GRAPH : thm
  CARD_EXP_GRAPH_PAIRED : thm
  CARD_EXP_0 : thm
  CARD_EXP_ZERO : thm
  CARD_EXP_ADD : thm
  CARD_EXP_MUL : thm
  CARD_MUL_EXP : thm
  CARD_EXP_SING : thm
  CARD_LE_EXP_LEFT : thm
  CARD_LE_EXP_RIGHT : thm
  CARD_LE_EXP : thm
  CARD_EXP_CONG : thm
  CARD_EXP_FINITE : thm
  CARD_EXP_C : thm
  CARD_EXP_POWERSET : thm
  CARD_EXP_CANTOR : thm
  CARD_EXP_ABSORB : thm
  CARD_EXP_LE_REAL : thm
  CARD_EXP_EQ_REAL : thm
  deriving Inhabited

@[nospecialize]
def setupExp [HolBase] (D : CardDeps) (BBasics : Basics) (BOrder : Order) (BArith : Arith) (BSquare : Square) (BCountable : Countable) (BReals : Reals) :
    ExceptT String IO Exp := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, distinctness,
        injectivity, new_definition, parse_as_infix, .. } := D
  let { ARB, CARD_CLAUSES, CARD_SING, CONJ_ASSOC, CONJ_SYM, COUNTABLE, DE_MORGAN_THM,
        EMPTY_GSPEC, EQ_TRANS, EXP, EXTENSIONAL, FINITE_CROSS, FINITE_EMPTY,
        FINITE_INDUCT_STRONG, FINITE_INSERT, FINITE_POWERSET, FINITE_SING,
        FORALL_IN_GSPEC, FORALL_IN_IMAGE, FORALL_IN_INSERT, FORALL_IN_UNION,
        FORALL_PAIR_THM, FUN_EQ_THM, IMP_CONJ, IMP_CONJ_ALT, .. } := D.core1
  let { INJECTIVE_ON_LEFT_INVERSE, IN_CROSS, IN_ELIM_PAIR_THM, IN_ELIM_THM, IN_SING,
        IN_UNION, IN_UNIV, MEMBER_NOT_EMPTY, MONO_FORALL, NOT_IN_EMPTY, PAIR, PAIR_EQ, .. } := D.core2
  let { RIGHT_FORALL_IMP_THM, SUBSET, UNIV_NOT_EMPTY, UNWIND_THM1, ge_c, le_c,
        sum_INDUCT, .. } := D.core3
  let { CARD_EMPTY_LE, CARD_EQ_EMPTY, CARD_EQ_IMP_LE, CARD_EQ_REFL, CARD_EQ_SYM,
        CARD_LE_REFL, CARD_LE_TRANS, CARD_LTE_TRANS, EQ_C_BIJECTIONS, .. } := BBasics
  let { CARD_EQ_CARD, CARD_EQ_CARD_IMP, CARD_EQ_TRANS, CARD_LE_ANTISYM, CARD_LE_FINITE,
        CARD_LE_SUBSET, CARD_SING_LE, .. } := BOrder
  let { CARD_ADD_C, CARD_FUNSPACE_CONG, CARD_FUNSPACE_CURRY, CARD_MUL_C,
        CARD_SQUARE_NUM, MUL_C_UNIV, add_c, mul_c, .. } := BArith
  let { CARD_ADD_FINITE, CARD_MUL_FINITE, CARD_SQUARE_INFINITE, .. } := BSquare
  let { CANTOR_THM, .. } := BCountable
  let { CARD_EQ_REAL, .. } := BReals
  -- @@SCOPE END

  parse_as_infix ("^_c", (24, "left"))

  let exp_c ← new_definition
   r"s ^_c t = {f:B->A | (!x. x IN t ==> f x IN s) /\
                       (!x. ~(x IN t) ==> f x = @y. F)}"

  let EXP_C ← prove
   r"!(s:A->bool) (t:B->bool).
        s ^_c t = {f:B->A | IMAGE f t SUBSET s /\ EXTENSIONAL t f}"
   (REWRITE_TAC [EXTENSIONAL, ARB, IN_ELIM_THM, SUBSET, FORALL_IN_IMAGE] THEN
    REWRITE_TAC [exp_c])

  let CARD_EXP_UNIV ← prove
   r"(:A) ^_c (:B) = (:B->A)"
   (REWRITE_TAC [exp_c, IN_UNIV] THEN SET_TAC [])

  let CARD_EXP_GRAPH ← prove
   r"!s:A->bool t:B->bool.
        (s ^_c t) =_c {R:B->A->bool | (!x y. R x y ==> x IN t /\ y IN s) /\
                                      (!x. x IN t ==> ?!y. R x y)}"
   (REPEAT GEN_TAC THEN REWRITE_TAC [EQ_C_BIJECTIONS, exp_c, FORALL_IN_GSPEC] THEN
    MAP_EVERY EXISTS_TAC
     [← q r"\f:B->A x y. x IN t /\ f x = y",
      ← q r"\(R:B->A->bool) x. if x IN t then @y. R x y else @y. F"] THEN
    SIMP_TAC [IN_ELIM_THM, FUN_EQ_THM] THEN MESON_TAC [])

  let CARD_EXP_GRAPH_PAIRED ← prove
   r"!s:A->bool t:B->bool.
        (s ^_c t) =_c {R:B#A->bool | (!x y. R(x,y) ==> x IN t /\ y IN s) /\
                                     (!x. x IN t ==> ?!y. R(x,y))}"
   (MP_TAC CARD_EXP_GRAPH THEN
    REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] CARD_EQ_TRANS) THEN
    REWRITE_TAC [EQ_C_BIJECTIONS, FORALL_IN_GSPEC] THEN
    MAP_EVERY EXISTS_TAC
     [← q r"\(R:B->A->bool) (x,y). R x y",
      ← q r"\(R:B#A->bool) x y. R(x,y)"] THEN
    REWRITE_TAC [IN_ELIM_THM, FORALL_PAIR_THM, FUN_EQ_THM])

  let CARD_EXP_0 ← prove
   r"!s c:C. (s:A->bool) ^_c ({}:B->bool) =_c {c}"
   (REPEAT GEN_TAC THEN REWRITE_TAC [exp_c, NOT_IN_EMPTY] THEN
    ONCE_REWRITE_TAC [← GSYM FUN_EQ_THM] THEN
    REWRITE_TAC [← SET_RULE (← q r"{x | x = a} = {a}")] THEN
    SIMP_TAC [CARD_EQ_CARD, FINITE_SING, CARD_SING])

  let CARD_EXP_ZERO ← prove
   r"!s:B->bool c:C. ({}:A->bool) ^_c s =_c if s = {} then {c} else {}"
   (← do
    let s2 ← SET_RULE (← q r"{x | x = a} = {a}")
    let s1 ← SET_RULE (← q r"~(s = {}) ==> ~(!x. ~(x IN s))")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [exp_c] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [NOT_IN_EMPTY] THEN
      ASM_SIMP_TAC [s1] THEN
      REWRITE_TAC [CARD_EQ_EMPTY, EMPTY_GSPEC] THEN
      ONCE_REWRITE_TAC [← GSYM FUN_EQ_THM] THEN
      REWRITE_TAC [s2] THEN
      SIMP_TAC [CARD_EQ_CARD, FINITE_SING, CARD_SING]))

  let CARD_EXP_ADD ← prove
   r"!s:A->bool t:B->bool u:C->bool.
        s ^_c (t +_c u) =_c (s ^_c t) *_c (s ^_c u)"
   (← do
    let us ← ONCE_REWRITE_RULE [CONJ_SYM] UNWIND_THM1
    pure (REPEAT GEN_TAC THEN
      REWRITE_TAC [add_c, mul_c, exp_c, EQ_C_BIJECTIONS] THEN
      REWRITE_TAC [FORALL_IN_UNION, FORALL_IN_GSPEC] THEN
      MAP_EVERY EXISTS_TAC
       [← q r"\f:B+C->A. (\x. if x IN t then f(INL x) else @x. F),
                    (\x. if x IN u then f(INR x) else @x. F)",
        ← q r"\(g:B->A,h:C->A) z. if ?x. x IN t /\ INL x = z
                             then g(@x. x IN t /\ INL x = z)
                             else if ?y. y IN u /\ INR y = z
                             then h(@y. y IN u /\ INR y = z)
                             else @y. F"] THEN
      REWRITE_TAC [IN_ELIM_THM, IN_UNION] THEN
      REWRITE_TAC [← injectivity "sum", ← distinctness "sum", PAIR_EQ] THEN
      REWRITE_TAC [us, CONJ_ASSOC] THEN
      REWRITE_TAC [FUN_EQ_THM] THEN CONJ_TAC THENL [SIMP_TAC [], MESON_TAC []] THEN
      GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC sum_INDUCT THEN
      REWRITE_TAC [← injectivity "sum", ← distinctness "sum", PAIR_EQ] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
      CONV_TAC SYM_CONV THEN TRY (FIRST_X_ASSUM MATCH_MP_TAC) THEN
      ASM_MESON_TAC [← injectivity "sum", ← distinctness "sum"]))

  let CARD_EXP_MUL ← prove
   r"!s:A->bool t:B->bool u:C->bool.
        s ^_c (t *_c u) =_c (s ^_c t) ^_c u"
   (REPEAT GEN_TAC THEN REWRITE_TAC [mul_c, exp_c, EQ_C_BIJECTIONS] THEN
    MAP_EVERY EXISTS_TAC
     [← q r"\f:B#C->A y. if y IN u then \x. f(x,y) else @x. F",
      ← q r"\f:C->B->A (x,y). if x IN t /\ y IN u then f y x else @x. F"] THEN
    REWRITE_TAC [FORALL_IN_GSPEC, FORALL_PAIR_THM, IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC [FUN_EQ_THM, IN_ELIM_THM, FORALL_PAIR_THM, DE_MORGAN_THM] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC [] THEN ASM_MESON_TAC [])

  let CARD_MUL_EXP ← prove
   r"!s:A->bool t:B->bool u:C->bool.
        (s *_c t) ^_c u =_c (s ^_c u) *_c (t ^_c u)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [mul_c, exp_c, EQ_C_BIJECTIONS] THEN
    MAP_EVERY EXISTS_TAC
     [← q r"\f:C->A#B. (\x. if x IN u then FST(f x) else @x. F),
                  (\x. if x IN u then SND(f x) else @x. F)",
      ← q r"\(g:C->A,h:C->B) x. if x IN u then (g x,h x) else @x. F"] THEN
    REWRITE_TAC [FUN_EQ_THM, FORALL_IN_GSPEC] THEN
    REWRITE_TAC [IN_ELIM_THM, FORALL_PAIR_THM, PAIR_EQ] THEN
    REWRITE_TAC [← ONCE_REWRITE_RULE [CONJ_SYM] UNWIND_THM1, CONJ_ASSOC] THEN
    REWRITE_TAC [FUN_EQ_THM] THEN MESON_TAC [PAIR, PAIR_EQ])

  let CARD_EXP_SING ← prove
   r"!s:A->bool b:B. (s ^_c {b}) =_c s"
   (REPEAT GEN_TAC THEN REWRITE_TAC [exp_c, EQ_C_BIJECTIONS] THEN
    REWRITE_TAC [FORALL_IN_INSERT, NOT_IN_EMPTY] THEN
    REWRITE_TAC [IN_ELIM_THM, IN_SING] THEN
    MAP_EVERY EXISTS_TAC
     [← q r"\f:(B->A). f b", ← q r"\x:A y:B. if y = b then x else @y. F"] THEN
    SIMP_TAC [FUN_EQ_THM] THEN MESON_TAC [])

  let CARD_LE_EXP_LEFT ← prove
   r"!s:A->bool s':B->bool t:C->bool. s <=_c s' ==> s ^_c t <=_c s' ^_c t"
   (REPEAT GEN_TAC THEN REWRITE_TAC [le_c, exp_c] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"f:A->B")) THEN
    EXISTS_TAC (← q r"\(g:C->A) z:C. if z IN t then f(g z):B else @x. F") THEN
    SIMP_TAC [IN_ELIM_THM, FUN_EQ_THM] THEN ASM_MESON_TAC [])

  let CARD_LE_EXP_RIGHT ← prove
   r"!s:A->bool t:B->bool t':C->bool.
      ~(s = {}) /\ t <=_c t' ==> s ^_c t <=_c s ^_c t'"
   (REPEAT GEN_TAC THEN REWRITE_TAC [le_c, exp_c, ← GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q "a:A"))
     (X_CHOOSE_THEN (← q r"f:B->C") STRIP_ASSUME_TAC)) THEN
    FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE id [INJECTIVE_ON_LEFT_INVERSE]) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"h:C->B")) THEN
    EXISTS_TAC (← q r"\g:(B->A) c:C. if c IN t' then if h c IN t then g(h c) else a
                               else @x:A. F") THEN
    SIMP_TAC [IN_ELIM_THM] THEN CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [← q r"k:B->A", ← q r"l:B->A"] THEN
    REWRITE_TAC [FUN_EQ_THM] THEN STRIP_TAC THEN X_GEN_TAC (← q "b:B") THEN
    ASM_CASES_TAC (← q r"(b:B) IN t") THEN ASM_SIMP_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"(f:B->C) b")) THEN ASM_MESON_TAC [])

  let CARD_LE_EXP ← prove
   r"!s:A->bool s':B->bool t:C->bool t':D->bool.
        ~(s = {}) /\ s <=_c s' /\ t <=_c t' ==> s ^_c t <=_c s' ^_c t'"
   (REPEAT STRIP_TAC THEN
    TRANS_TAC CARD_LE_TRANS (← q r"(s:A->bool) ^_c (t':D->bool)") THEN
    ASM_SIMP_TAC [CARD_LE_EXP_RIGHT, CARD_LE_EXP_LEFT])

  let CARD_EXP_CONG ← prove
   r"!s:A->bool s':B->bool t:C->bool t':D->bool.
      s =_c s' /\ t =_c t' ==> s ^_c t =_c s' ^_c t'"
   (← do
    let ce ← REWRITE_RULE [IMP_CONJ] CARD_EQ_TRANS
    pure (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"t':D->bool = {}") THEN
      ASM_SIMP_TAC [CARD_EQ_EMPTY] THENL
       [REPEAT STRIP_TAC THEN TRANS_TAC CARD_EQ_TRANS (← q "{0}") THEN
        REWRITE_TAC [CARD_EXP_0, ← ONCE_REWRITE_RULE [CARD_EQ_SYM] CARD_EXP_0],
        ONCE_REWRITE_TAC [CARD_EQ_SYM] THEN
        ASM_CASES_TAC (← q r"t:C->bool = {}") THEN
        ASM_REWRITE_TAC [CARD_EQ_EMPTY]] THEN
      ASM_CASES_TAC (← q r"s:A->bool = {}") THEN ASM_SIMP_TAC [CARD_EQ_EMPTY] THENL
       [STRIP_TAC THEN MP_TAC (← ISPECL [← q r"t:C->bool", ← q "0"] CARD_EXP_ZERO) THEN
        ASM_REWRITE_TAC [] THEN GEN_REWRITE_TAC LAND_CONV [CARD_EQ_SYM] THEN
        MATCH_MP_TAC ce THEN
        MP_TAC (← HolLight.INST_TYPE [(← qty "B", ← qty "A")]
           (← ISPECL [← q r"t':D->bool", ← q "0"] CARD_EXP_ZERO)) THEN
        ASM_REWRITE_TAC [],
        ONCE_REWRITE_TAC [CARD_EQ_SYM] THEN
        ASM_CASES_TAC (← q r"s':B->bool = {}") THEN
        ASM_REWRITE_TAC [CARD_EQ_EMPTY] THEN
        ASM_SIMP_TAC [CARD_LE_EXP, ← GSYM CARD_LE_ANTISYM]]))

  let CARD_EXP_FINITE ← prove
   r"!s:A->bool t:B->bool. FINITE s /\ FINITE t ==> FINITE(s ^_c t)"
   (← do
    let lt ← REWRITE_RULE [IMP_CONJ_ALT] CARD_LE_TRANS
    let lf ← REWRITE_RULE [IMP_CONJ_ALT] CARD_LE_FINITE
    pure (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [CONJ_SYM] THEN
      DISCH_THEN (MP_TAC o MATCH_MP FINITE_POWERSET o MATCH_MP FINITE_CROSS) THEN
      MATCH_MP_TAC lf THEN
      MP_TAC (← ISPECL [← q r"s:A->bool", ← q r"t:B->bool"] CARD_EXP_GRAPH_PAIRED) THEN
      DISCH_THEN (MP_TAC o MATCH_MP CARD_EQ_IMP_LE) THEN
      MATCH_MP_TAC lt THEN
      MATCH_MP_TAC CARD_LE_SUBSET THEN
      REWRITE_TAC [SUBSET, FORALL_PAIR_THM, IN_CROSS] THEN SET_TAC []))

  let CARD_EXP_C ← prove
   r"!s:A->bool t:B->bool.
        FINITE s /\ FINITE t ==> CARD(s ^_c t) = (CARD s) EXP (CARD t)"
   (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC [CARD_CLAUSES, EXP] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC [← GSYM (← ISPEC (← q "0") CARD_SING)] THEN
      MATCH_MP_TAC CARD_EQ_CARD_IMP THEN SIMP_TAC [CARD_EXP_0, FINITE_SING],
      MAP_EVERY X_GEN_TAC [← q "b:B", ← q r"t:B->bool"] THEN STRIP_TAC] THEN
    TRANS_TAC EQ_TRANS (← q r"CARD((s:A->bool) ^_c ({b:B} +_c (t:B->bool)))") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_EQ_CARD_IMP THEN
      ASM_SIMP_TAC [CARD_EXP_FINITE, CARD_ADD_FINITE, FINITE_SING] THEN
      MATCH_MP_TAC CARD_EXP_CONG THEN REWRITE_TAC [CARD_EQ_REFL] THEN
      ASM_SIMP_TAC [CARD_EQ_CARD, FINITE_INSERT, CARD_ADD_FINITE, FINITE_EMPTY,
                   CARD_ADD_C, CARD_SING, CARD_CLAUSES] THEN
      ARITH_TAC,
      ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
      (← q r"CARD(((s:A->bool) ^_c {b:B}) *_c (s ^_c (t:B->bool)))") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_EQ_CARD_IMP THEN REWRITE_TAC [CARD_EXP_ADD] THEN
      ASM_SIMP_TAC [CARD_EXP_FINITE, CARD_MUL_FINITE, FINITE_SING],
      ASM_SIMP_TAC [CARD_MUL_C, CARD_EXP_FINITE, FINITE_SING]] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC CARD_EQ_CARD_IMP THEN
    ASM_SIMP_TAC [CARD_EXP_SING])

  let CARD_EXP_POWERSET ← prove
   r"!s:A->bool. (:bool) ^_c s =_c {t | t SUBSET s}"
   (GEN_TAC THEN REWRITE_TAC [exp_c, EQ_C_BIJECTIONS, IN_UNIV] THEN
    MAP_EVERY EXISTS_TAC
     [← q r"\P:A->bool. {x | x IN s /\ P x}",
      ← q r"\t x:A. if x IN s then x IN t else @b. F"] THEN
    SIMP_TAC [IN_ELIM_THM] THEN SET_TAC [])

  let CARD_EXP_CANTOR ← prove
   r"!s:A->bool. s <_c (:bool) ^_c s"
   (GEN_TAC THEN
    TRANS_TAC CARD_LTE_TRANS (← q r"{t:A->bool | t SUBSET s}") THEN
    REWRITE_TAC [CANTOR_THM] THEN
    MATCH_MP_TAC CARD_EQ_IMP_LE THEN
    ONCE_REWRITE_TAC [CARD_EQ_SYM] THEN REWRITE_TAC [CARD_EXP_POWERSET])

  let CARD_EXP_ABSORB ← prove
   r"!s:A->bool t:B->bool.
        INFINITE t /\ (:bool) <=_c s /\ s <=_c (:bool) ^_c t
        ==> s ^_c t =_c (:bool) ^_c t"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM CARD_LE_ANTISYM] THEN
    ASM_SIMP_TAC [CARD_LE_EXP_LEFT, CARD_LE_REFL] THEN
    TRANS_TAC CARD_LE_TRANS (← q r"((:bool) ^_c t) ^_c (t:B->bool)") THEN
    ASM_SIMP_TAC [CARD_LE_EXP_LEFT] THEN MATCH_MP_TAC CARD_EQ_IMP_LE THEN
    TRANS_TAC CARD_EQ_TRANS (← q r"(:bool) ^_c ((t:B->bool) *_c t)") THEN
    SIMP_TAC [← ONCE_REWRITE_RULE [CARD_EQ_SYM] CARD_EXP_MUL] THEN
    MATCH_MP_TAC CARD_EXP_CONG THEN
    ASM_SIMP_TAC [CARD_SQUARE_INFINITE, CARD_EQ_REFL])

  let CARD_EXP_LE_REAL ← prove
   r"!s:A->bool t:B->bool.
        s <=_c (:real) /\ COUNTABLE t ==> s ^_c t <=_c (:real)"
   (← do
    let lt ← REWRITE_RULE [IMP_CONJ_ALT] CARD_LE_TRANS
    pure (REWRITE_TAC [COUNTABLE, ge_c] THEN REPEAT STRIP_TAC THEN
      ASM_CASES_TAC (← q r"s:A->bool = {}") THEN ASM_REWRITE_TAC [] THENL
       [mpPartLhand lhand CARD_EXP_ZERO THEN
        DISCH_THEN (MP_TAC o MATCH_MP CARD_EQ_IMP_LE) THEN
        MATCH_MP_TAC lt THEN
        COND_CASES_TAC THEN
        REWRITE_TAC [CARD_EMPTY_LE, CARD_SING_LE, UNIV_NOT_EMPTY],
        ALL_TAC] THEN
      TRANS_TAC CARD_LE_TRANS (← q r"(:num->num->bool)") THEN CONJ_TAC THENL
       [REWRITE_TAC [← GSYM CARD_EXP_UNIV] THEN
        MATCH_MP_TAC CARD_LE_EXP THEN ASM_REWRITE_TAC [] THEN
        TRANS_TAC CARD_LE_TRANS (← q "(:real)") THEN ASM_REWRITE_TAC [] THEN
        SIMP_TAC [CARD_EXP_UNIV, CARD_EQ_IMP_LE, CARD_EQ_REAL],
        TRANS_TAC CARD_LE_TRANS (← q r"(:num#num->bool)") THEN
        SIMP_TAC [CARD_FUNSPACE_CURRY, CARD_EQ_IMP_LE] THEN
        MATCH_MP_TAC CARD_EQ_IMP_LE THEN ONCE_REWRITE_TAC [CARD_EQ_SYM] THEN
        TRANS_TAC CARD_EQ_TRANS (← q r"(:num->bool)") THEN REWRITE_TAC [CARD_EQ_REAL] THEN
        MATCH_MP_TAC CARD_FUNSPACE_CONG THEN REWRITE_TAC [CARD_EQ_REFL] THEN
        ONCE_REWRITE_TAC [CARD_EQ_SYM] THEN
        REWRITE_TAC [← GSYM MUL_C_UNIV, CARD_SQUARE_NUM]]))

  let CARD_EXP_EQ_REAL ← prove
   r"!s:A->bool. COUNTABLE s /\ ~(s = {}) ==> (:real) ^_c s =_c (:real)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM CARD_LE_ANTISYM] THEN
    ASM_SIMP_TAC [CARD_EXP_LE_REAL, CARD_LE_REFL] THEN
    TRANS_TAC CARD_LE_TRANS (← q r"(:real) ^_c {a:A}") THEN
    SIMP_TAC [← ONCE_REWRITE_RULE [CARD_EQ_SYM] CARD_EXP_SING, CARD_EQ_IMP_LE] THEN
    MATCH_MP_TAC CARD_LE_EXP THEN
    ASM_REWRITE_TAC [UNIV_NOT_EMPTY, CARD_LE_REFL, CARD_SING_LE])

  -- @@RETURN BEGIN
  return { exp_c, EXP_C, CARD_EXP_UNIV, CARD_EXP_GRAPH, CARD_EXP_GRAPH_PAIRED,
           CARD_EXP_0, CARD_EXP_ZERO, CARD_EXP_ADD, CARD_EXP_MUL, CARD_MUL_EXP,
           CARD_EXP_SING, CARD_LE_EXP_LEFT, CARD_LE_EXP_RIGHT, CARD_LE_EXP,
           CARD_EXP_CONG, CARD_EXP_FINITE, CARD_EXP_C, CARD_EXP_POWERSET,
           CARD_EXP_CANTOR, CARD_EXP_ABSORB, CARD_EXP_LE_REAL, CARD_EXP_EQ_REAL }
  -- @@RETURN END

/-- `W(MP_TAC o PART_MATCH f th o rand o snd)` -/
def mpPartRand [HolBase] (f : term → Except String term) (th : thm) : tactic := fun gl =>
  ExceptT.run do
    let t ← liftExcept (rand gl.2)
    ExceptT.mk (MP_TAC (← PART_MATCH f th t) gl)

/- ------------------------------------------------------------------------- -/
/- Restricted and limited powersets; more about cardinality of lists and     -/
/- restricted powersets; restricted function spaces.  (card.ml 2828-3183)    -/
/- ------------------------------------------------------------------------- -/

structure Powerset where
  -- @@FIELDS
  CARD_EQ_RESTRICTED_POWERSET : thm
  CARD_EQ_LIMITED_POWERSET : thm
  CARD_EQ_FULLSIZE_POWERSET : thm
  CARD_EQ_EXP_INFINITE_FINITE : thm
  CARD_EQ_FINITE_SUBSETS : thm
  CARD_LE_LIST : thm
  CARD_LE_SUBPOWERSET : thm
  CARD_LE_FINITE_SUBSETS : thm
  CARD_LE_COUNTABLE_SUBSETS : thm
  CARD_LE_POWERSET : thm
  CARD_POWERSET_CONG : thm
  COUNTABLE_LIST_GEN : thm
  COUNTABLE_LIST : thm
  COUNTABLE_FINITE_SUBSETS : thm
  CARD_EQ_REAL_SEQUENCES : thm
  CARD_EQ_COUNTABLE_SUBSETS_SUBREAL : thm
  CARD_EQ_COUNTABLE_SUBSETS_REAL : thm
  CARD_LE_RESTRICTED_FUNSPACE : thm
  COUNTABLE_RESTRICTED_FUNSPACE : thm
  CARD_LE_RESTRICTED_FUNSPACE_INFINITE : thm
  CARD_EQ_RESTRICTED_FUNSPACE_INFINITE : thm
  CARD_EQ_FUNSPACE : thm
  deriving Inhabited

@[nospecialize]
def setupPowerset [HolBase] (D : CardDeps) (BBasics : Basics) (BOrder : Order) (BArith : Arith) (BSquare : Square) (BCountable : Countable) (BReals : Reals) (BExp : Exp) :
    ExceptT String IO Powerset := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, LIST_INDUCT_TAC, MESON_TAC, SET_RULE, SET_TAC, .. } := D
  let { AND_FORALL_THM, ARB, CONJ_ASSOC, CONS_11, CONTRAPOS_THM, COUNTABLE, CROSS,
        DISJOINT, DISJOINT_SING, EXISTS_PAIR_THM, EXISTS_UNIQUE_DEF, EXTENSION,
        FINITE_BOOL, FINITE_EMPTY, FINITE_IMAGE, FINITE_INDUCT_STRONG, FINITE_SING,
        FINITE_SUBSET, FORALL_AND_THM, FORALL_IN_GSPEC, FORALL_IN_IMAGE,
        FORALL_PAIR_THM, FUN_EQ_THM, IMP_CONJ, IMP_CONJ_ALT, IN, .. } := D.core1
  let { INFINITE, INFINITE_CROSS_EQ, IN_CROSS, IN_ELIM_THM, IN_IMAGE, IN_SING,
        IN_UNION, IN_UNIV, LE_C, MAP, MAP_EQ_NIL, MEM, MEMBER_NOT_EMPTY,
        MEM_LIST_OF_SET, MEM_MAP, NOT_CONS_NIL, NOT_INSERT_EMPTY, NOT_IN_EMPTY,
        PAIR_EQ, .. } := D.core2
  let { RIGHT_FORALL_IMP_THM, SET_OF_LIST_OF_SET, SING_GSPEC, SING_SUBSET, SKOLEM_THM,
        SUBSET, SUBSET_UNIV, SWAP_FORALL_THM, UNWIND_THM1, UNWIND_THM2, eq_c, ge_c,
        le_c, num_INFINITE, real_INFINITE, .. } := D.core3
  let { CARD_EMPTY_LE, CARD_EQ_EMPTY, CARD_EQ_IMP_LE, CARD_EQ_REFL, CARD_EQ_REFL_IMP,
        CARD_EQ_SYM, CARD_LE_EMPTY, CARD_LE_REFL, CARD_LE_TRANS, CARD_LT_IMP_LE,
        EQ_C_BIJECTIONS, .. } := BBasics
  let { CARD_EQ_IMAGE, CARD_EQ_TRANS, CARD_LE_ANTISYM, CARD_LE_FINITE_INFINITE,
        CARD_LE_IMAGE, CARD_LE_INFINITE, CARD_LE_SUBSET, CARD_LE_TOTAL, CARD_SING_LE,
        INFINITE_CARD_LE, LE_C_IMAGE, .. } := BOrder
  let { CARD_DISJOINT_UNION, CARD_FUNSPACE_CONG, CARD_FUNSPACE_CURRY, CARD_MUL_CONG,
        CARD_SQUARE_NUM, MUL_C_UNIV, UNION_LE_ADD_C, mul_c, .. } := BArith
  let { CARD_ADD_ABSORB_LEFT, CARD_MUL2_ABSORB_LE_ALT, CARD_MUL_ABSORB_LE,
        CARD_SQUARE_INFINITE, .. } := BSquare
  let { CARD_LE_COUNTABLE, COUNTABLE_CROSS, COUNTABLE_IMAGE, .. } := BCountable
  let { CARD_EQ_LIST, CARD_EQ_LIST_GEN, CARD_EQ_REAL, .. } := BReals
  let { CARD_EXP_0, CARD_EXP_ABSORB, CARD_EXP_ADD, CARD_EXP_CANTOR, CARD_EXP_CONG,
        CARD_EXP_GRAPH_PAIRED, CARD_EXP_POWERSET, CARD_EXP_SING, CARD_EXP_UNIV, exp_c, .. } := BExp
  -- @@SCOPE END

  let (CARD_EQ_RESTRICTED_POWERSET, CARD_EQ_LIMITED_POWERSET) ← CONJ_PAIR (← prove
   r"(!s:A->bool t:B->bool.
        INFINITE s
        ==> { k | k SUBSET s /\ k =_c t} =_c
            (if t <=_c s then s ^_c t else {})) /\
   (!s:A->bool t:B->bool.
        INFINITE s
        ==> if t <=_c s then { k | k SUBSET s /\ k <=_c t} =_c s ^_c t
            else { k | k SUBSET s /\ k <=_c t} =_c (:bool) ^_c s)"
   (← do
    let lemma ← prove
     r"!s:A->bool t:B->bool u:C->bool.
          s <=_c t /\ t <=_c u /\ u <=_c s
          ==> s =_c u /\ t =_c u"
     (SIMP_TAC [← GSYM CARD_LE_ANTISYM] THEN REPEAT STRIP_TAC THENL
       [TRANS_TAC CARD_LE_TRANS (← q r"t:B->bool"),
        TRANS_TAC CARD_LE_TRANS (← q r"s:A->bool")] THEN
      ASM_SIMP_TAC [])
    -- Built when OCaml builds the tactic, last first.
    let r10 ← REWRITE_RULE [IMP_CONJ_ALT] CARD_LE_TRANS
    let s9 ← SET_RULE (← q r"{a} = {b} <=> a = b")
    let r8 ← REWRITE_RULE [IMP_CONJ_ALT] CARD_LE_INFINITE
    let t7 ← TAUT (← q r"(p ==> q) /\ p ==> p /\ q")
    let r6 ← REWRITE_RULE [IMP_CONJ_ALT] CARD_LE_TRANS
    let r5 ← ONCE_REWRITE_RULE [CARD_EQ_SYM] CARD_EQ_IMP_LE
    let s4 ← SET_RULE (← q r"k SUBSET s /\ k = {} <=> k = {}")
    let s3 ← SET_RULE (← q r"{x | P x /\ Q x} = {x | P x} <=> !x. P x ==> Q x")
    let r2 ← ONCE_REWRITE_RULE [CARD_EQ_SYM] CARD_EXP_POWERSET
    pure (REWRITE_TAC [AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
      ASM_CASES_TAC (← q r"INFINITE(s:A->bool)") THEN ASM_REWRITE_TAC [] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THENL
       [ALL_TAC,
        CONJ_TAC THENL
         [REWRITE_TAC [CARD_EQ_EMPTY, EXTENSION, NOT_IN_EMPTY, IN_ELIM_THM] THEN
          X_GEN_TAC (← q r"k:A->bool") THEN
          FIRST_X_ASSUM (fun th => tactic_of do
            if is_neg (concl th) then pure (MP_TAC th) else throw "check") THEN
          REWRITE_TAC [CONTRAPOS_THM] THEN STRIP_TAC THEN
          TRANS_TAC CARD_LE_TRANS (← q r"k:A->bool") THEN
          ASM_SIMP_TAC [CARD_LE_SUBSET] THEN MATCH_MP_TAC CARD_EQ_IMP_LE THEN
          ONCE_REWRITE_TAC [CARD_EQ_SYM] THEN FIRST_ASSUM ACCEPT_TAC,
          TRANS_TAC CARD_EQ_TRANS (← q r"{k:A->bool | k SUBSET s}") THEN
          REWRITE_TAC [r2] THEN
          MATCH_MP_TAC CARD_EQ_REFL_IMP THEN
          REWRITE_TAC [s3] THEN
          X_GEN_TAC (← q r"k:A->bool") THEN DISCH_TAC THEN
          TRANS_TAC CARD_LE_TRANS (← q r"s:A->bool") THEN
          ASM_SIMP_TAC [CARD_LE_SUBSET] THEN
          ASM_MESON_TAC [CARD_LE_TOTAL]]] THEN
      MATCH_MP_TAC lemma THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CARD_LE_SUBSET THEN
        SIMP_TAC [SUBSET, IN_ELIM_THM, CARD_EQ_IMP_LE],
        ASM_CASES_TAC (← q r"t:B->bool = {}") THENL
         [ASM_REWRITE_TAC [CARD_LE_EMPTY, SING_GSPEC, s4] THEN
          MATCH_MP_TAC r5 THEN
          REWRITE_TAC [CARD_EXP_0],
          ALL_TAC] THEN
        TRANS_TAC CARD_LE_TRANS
         (← q r"{k:A->bool | k SUBSET s /\ ~(k = {}) /\ k <=_c (t:B->bool)}") THEN
        CONJ_TAC THENL
         [ALL_TAC,
          GEN_REWRITE_TAC id [LE_C] THEN
          SIMP_TAC [FORALL_IN_GSPEC, IMP_CONJ, LE_C_IMAGE] THEN
          EXISTS_TAC (← q r"\f:B->A. IMAGE f t") THEN
          X_GEN_TAC (← q r"k:A->bool") THEN STRIP_TAC THEN STRIP_TAC THEN
          DISCH_THEN (X_CHOOSE_THEN (← q r"f:B->A") (SUBST_ALL_TAC o SYM)) THEN
          EXISTS_TAC (← q r"\y. if y IN t then (f:B->A) y else @y. F") THEN
          ASM_SIMP_TAC [exp_c, IN_ELIM_THM] THEN ASM SET_TAC []] THEN
        TRANS_TAC CARD_LE_TRANS
         (← q r"{{}} UNION
          {k:A->bool | k SUBSET s /\ ~(k = {}) /\ k <=_c (t:B->bool)}") THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CARD_LE_SUBSET THEN GEN_REWRITE_TAC id [SUBSET] THEN
          REWRITE_TAC [IN_ELIM_THM, IN_UNION, IN_SING] THEN
          X_GEN_TAC (← q r"k:A->bool") THEN ASM_CASES_TAC (← q r"k:A->bool = {}") THEN
          ASM_REWRITE_TAC [CARD_EMPTY_LE],
          ALL_TAC] THEN
        mpPartLhand lhand UNION_LE_ADD_C THEN
        MATCH_MP_TAC r6 THEN
        MATCH_MP_TAC CARD_EQ_IMP_LE THEN MATCH_MP_TAC CARD_ADD_ABSORB_LEFT THEN
        MATCH_MP_TAC t7 THEN CONJ_TAC THENL
         [DISCH_TAC THEN MATCH_MP_TAC CARD_LE_FINITE_INFINITE THEN
          ASM_REWRITE_TAC [FINITE_SING],
          ALL_TAC] THEN
        UNDISCH_TAC (← q r"INFINITE(s:A->bool)") THEN
        MATCH_MP_TAC r8 THEN
        ONCE_REWRITE_TAC [le_c] THEN EXISTS_TAC (← q r"\x:A. {x}") THEN
        SIMP_TAC [s9, IN_ELIM_THM] THEN
        ASM_SIMP_TAC [SING_SUBSET, NOT_INSERT_EMPTY, CARD_SING_LE],
        TRANS_TAC CARD_LE_TRANS
         (← q r"{k | k SUBSET ((t:B->bool) *_c (s:A->bool)) /\ k =_c t}") THEN
        CONJ_TAC THENL
         [MP_TAC (← ISPECL [← q r"s:A->bool", ← q r"t:B->bool"] CARD_EXP_GRAPH_PAIRED) THEN
          DISCH_THEN (MP_TAC o MATCH_MP CARD_EQ_IMP_LE) THEN
          MATCH_MP_TAC r10 THEN
          MATCH_MP_TAC CARD_LE_SUBSET THEN
          REWRITE_TAC [SUBSET, mul_c, IN_ELIM_THM] THEN
          X_GEN_TAC (← q r"R:B#A->bool") THEN REWRITE_TAC [FORALL_PAIR_THM] THEN
          REPEAT STRIP_TAC THENL [ASM_MESON_TAC [IN], ALL_TAC] THEN
          REWRITE_TAC [eq_c] THEN EXISTS_TAC (← q r"FST:B#A->B") THEN
          REWRITE_TAC [EXISTS_UNIQUE_DEF, FORALL_PAIR_THM, EXISTS_PAIR_THM] THEN
          ASM_MESON_TAC [PAIR_EQ, IN],
          SUBGOAL_THEN (← q r"(t:B->bool) *_c (s:A->bool) <=_c s") MP_TAC THENL
           [ASM_SIMP_TAC [CARD_MUL_ABSORB_LE], ALL_TAC] THEN
          REWRITE_TAC [le_c] THEN
          DISCH_THEN (X_CHOOSE_THEN (← q r"p:B#A->A") STRIP_ASSUME_TAC) THEN
          EXISTS_TAC (← q r"IMAGE (p:B#A->A)") THEN REWRITE_TAC [IN_ELIM_THM] THEN
          CONJ_TAC THENL [X_GEN_TAC (← q r"u:B#A->bool"), ASM SET_TAC []] THEN
          REPEAT STRIP_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
          TRANS_TAC CARD_EQ_TRANS (← q r"u:B#A->bool") THEN
          ASM_SIMP_TAC [] THEN MATCH_MP_TAC CARD_EQ_IMAGE THEN ASM SET_TAC []]])))

  let CARD_EQ_FULLSIZE_POWERSET ← prove
   r"!s:A->bool.
        INFINITE s ==> {t | t SUBSET s /\ t =_c s} =_c {t | t SUBSET s}"
   (← do
    let ce ← REWRITE_RULE [IMP_CONJ_ALT] CARD_EQ_TRANS
    pure (REPEAT STRIP_TAC THEN
      FIRST_ASSUM (MP_TAC o ISPEC (← q r"s:A->bool") o MATCH_MP
        CARD_EQ_RESTRICTED_POWERSET) THEN
      REWRITE_TAC [CARD_LE_REFL] THEN
      MATCH_MP_TAC ce THEN
      TRANS_TAC CARD_EQ_TRANS (← q r"(:bool) ^_c (s:A->bool)") THEN
      ASM_REWRITE_TAC [CARD_EXP_POWERSET] THEN
      MATCH_MP_TAC CARD_EXP_ABSORB THEN
      ASM_SIMP_TAC [CARD_LT_IMP_LE, CARD_EXP_CANTOR] THEN
      MATCH_MP_TAC CARD_LE_FINITE_INFINITE THEN
      ASM_REWRITE_TAC [FINITE_BOOL]))

  let CARD_EQ_EXP_INFINITE_FINITE ← prove
   r"!(s:A->bool) (t:B->bool).
       INFINITE s /\ FINITE t /\ ~(t = {}) ==> s ^_c t =_c s"
   (← do
    let ce ← REWRITE_RULE [IMP_CONJ_ALT] CARD_EQ_TRANS
    let s1 ← SET_RULE (← q r"a INSERT s = {a} UNION s")
    pure (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
      GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
      REWRITE_TAC [NOT_INSERT_EMPTY] THEN
      MAP_EVERY X_GEN_TAC [← q "b:B", ← q r"t:B->bool"] THEN
      ASM_CASES_TAC (← q r"t:B->bool = {}") THEN ASM_REWRITE_TAC [CARD_EXP_SING] THEN
      STRIP_TAC THEN TRANS_TAC CARD_EQ_TRANS (← q r"(s:A->bool) *_c s") THEN
      ASM_SIMP_TAC [CARD_SQUARE_INFINITE] THEN
      ONCE_REWRITE_TAC [s1] THEN
      TRANS_TAC CARD_EQ_TRANS (← q r"(s:A->bool) ^_c ({b:B} +_c (t:B->bool))") THEN
      ASM_SIMP_TAC [CARD_EXP_CONG, CARD_EQ_REFL, CARD_DISJOINT_UNION,
                   ← GSYM DISJOINT, DISJOINT_SING] THEN
      mpPartLhand lhand CARD_EXP_ADD THEN
      MATCH_MP_TAC ce THEN
      ASM_SIMP_TAC [CARD_MUL_CONG, CARD_EQ_REFL, CARD_EXP_SING]))

  -- More about cardinality of lists and restricted powersets etc.

  let CARD_EQ_FINITE_SUBSETS ← prove
   r"!s:A->bool. INFINITE(s) ==> {t | t SUBSET s /\ FINITE t} =_c s"
   (GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [← GSYM CARD_LE_ANTISYM] THEN
    CONJ_TAC THENL
     [TRANS_TAC CARD_LE_TRANS (← q r"{l:A list | !x. MEM x l ==> x IN s}") THEN
      CONJ_TAC THENL
       [REWRITE_TAC [LE_C, IN_ELIM_THM] THEN
        EXISTS_TAC (← q r"set_of_list:A list->(A->bool)") THEN
        X_GEN_TAC (← q r"t:A->bool") THEN STRIP_TAC THEN
        EXISTS_TAC (← q r"list_of_set(t:A->bool)") THEN
        ASM_SIMP_TAC [MEM_LIST_OF_SET, ← GSYM SUBSET, SET_OF_LIST_OF_SET],
        MATCH_MP_TAC CARD_EQ_IMP_LE THEN
        MATCH_MP_TAC CARD_EQ_LIST_GEN THEN ASM_REWRITE_TAC []],
     REWRITE_TAC [le_c] THEN EXISTS_TAC (← q r"\x:A. {x}") THEN
     REWRITE_TAC [IN_ELIM_THM, FINITE_SING] THEN SET_TAC []])

  let CARD_LE_LIST ← prove
   r"!s:A->bool t:B->bool.
        s <=_c t
        ==> {l | !x. MEM x l ==> x IN s} <=_c {l | !x. MEM x l ==> x IN t}"
   (← do
    let t ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    pure (GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [le_c, IN_ELIM_THM] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"f:A->B") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"MAP (f:A->B)") THEN
      MATCH_MP_TAC t THEN CONJ_TAC THENL
       [REWRITE_TAC [MEM_MAP] THEN ASM_MESON_TAC [], DISCH_TAC] THEN
      ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
      LIST_INDUCT_TAC THEN SIMP_TAC [MAP_EQ_NIL, MAP] THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC [MAP, NOT_CONS_NIL, MEM, CONS_11] THEN
      ASM_MESON_TAC []))

  let CARD_LE_SUBPOWERSET ← prove
   r"!s:A->bool t:B->bool.
        s <=_c t /\ (!f s. P s ==> Q(IMAGE f s))
        ==> {u | u SUBSET s /\ P u} <=_c {v | v SUBSET t /\ Q v}"
   (REPEAT GEN_TAC THEN REWRITE_TAC [le_c, IN_ELIM_THM] THEN DISCH_THEN
     (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"f:A->B") STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    EXISTS_TAC (← q r"IMAGE (f:A->B)") THEN ASM_SIMP_TAC [] THEN ASM SET_TAC [])

  let CARD_LE_FINITE_SUBSETS ← prove
   r"!s:A->bool t:B->bool.
    s <=_c t
    ==> {u | u SUBSET s /\ FINITE u} <=_c {v | v SUBSET t /\ FINITE v}"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_LE_SUBPOWERSET THEN
    ASM_SIMP_TAC [FINITE_IMAGE])

  let CARD_LE_COUNTABLE_SUBSETS ← prove
   r"!s:A->bool t:B->bool.
    s <=_c t
    ==> {u | u SUBSET s /\ COUNTABLE u} <=_c {v | v SUBSET t /\ COUNTABLE v}"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_LE_SUBPOWERSET THEN
    ASM_SIMP_TAC [COUNTABLE_IMAGE])

  let CARD_LE_POWERSET ← prove
   r"!s:A->bool t:B->bool.
    s <=_c t ==> {u | u SUBSET s} <=_c {v | v SUBSET t}"
   (REPEAT STRIP_TAC THEN PURE_ONCE_REWRITE_TAC [← SET_RULE
      (← q r"{x | x SUBSET y} = {x | x SUBSET y /\ T}")] THEN
    MATCH_MP_TAC CARD_LE_SUBPOWERSET THEN
    ASM_SIMP_TAC [])

  let CARD_POWERSET_CONG ← prove
   r"!s:A->bool t:B->bool.
        s =_c t ==> {u | u SUBSET s} =_c {v | v SUBSET t}"
   (SIMP_TAC [← GSYM CARD_LE_ANTISYM, CARD_LE_POWERSET])

  let COUNTABLE_LIST_GEN ← prove
   r"!s:A->bool. COUNTABLE s ==> COUNTABLE {l | !x. MEM x l ==> x IN s}"
   (← do
    let s1 ← SET_RULE (← q r"{x | T} = UNIV")
    let lt ← REWRITE_RULE [IMP_CONJ_ALT] CARD_LE_TRANS
    pure (GEN_TAC THEN REWRITE_TAC [COUNTABLE, ge_c] THEN
      DISCH_THEN (MP_TAC o MATCH_MP CARD_LE_LIST) THEN
      MATCH_MP_TAC lt THEN
      MATCH_MP_TAC CARD_EQ_IMP_LE THEN
      REWRITE_TAC [IN_UNIV, s1] THEN
      SIMP_TAC [CARD_EQ_LIST, num_INFINITE]))

  let COUNTABLE_LIST ← prove
   r"COUNTABLE(:A) ==> COUNTABLE(:A list)"
   (← do
    let s1 ← SET_RULE (← q r"{x | T} = UNIV")
    pure (MP_TAC (← ISPEC (← q "(:A)") COUNTABLE_LIST_GEN) THEN
      REWRITE_TAC [IN_UNIV, s1]))

  let COUNTABLE_FINITE_SUBSETS ← prove
   r"!s:A->bool. COUNTABLE(s) ==> COUNTABLE {t | t SUBSET s /\ FINITE t}"
   (← do
    let s1 ← SET_RULE (← q r"{x | T} = UNIV")
    let lt ← REWRITE_RULE [IMP_CONJ_ALT] CARD_LE_TRANS
    pure (GEN_TAC THEN REWRITE_TAC [COUNTABLE, ge_c] THEN
      DISCH_THEN (MP_TAC o MATCH_MP CARD_LE_FINITE_SUBSETS) THEN
      MATCH_MP_TAC lt THEN
      MATCH_MP_TAC CARD_EQ_IMP_LE THEN
      REWRITE_TAC [IN_UNIV, s1] THEN
      SIMP_TAC [CARD_EQ_FINITE_SUBSETS, num_INFINITE]))

  let CARD_EQ_REAL_SEQUENCES ← prove
   r"(:num->real) =_c (:real)"
   (← do
    let sq ← REWRITE_RULE [MUL_C_UNIV] CARD_SQUARE_NUM
    let er ← ONCE_REWRITE_RULE [CARD_EQ_SYM] CARD_EQ_REAL
    pure (TRANS_TAC CARD_EQ_TRANS (← q r"(:num->num->bool)") THEN
      ASM_SIMP_TAC [CARD_FUNSPACE_CONG, CARD_EQ_REFL, CARD_EQ_REAL] THEN
      TRANS_TAC CARD_EQ_TRANS (← q r"(:num#num->bool)") THEN
      ASM_SIMP_TAC [CARD_FUNSPACE_CURRY] THEN
      TRANS_TAC CARD_EQ_TRANS (← q r"(:num->bool)") THEN
      ASM_SIMP_TAC [CARD_FUNSPACE_CONG, CARD_EQ_REFL, er, sq]))

  let CARD_EQ_COUNTABLE_SUBSETS_SUBREAL ← prove
   r"!s:A->bool. INFINITE s /\ s <=_c (:real)
               ==> {t | t SUBSET s /\ COUNTABLE t} =_c (:real)"
   (← do
    let er ← ONCE_REWRITE_RULE [CARD_EQ_SYM] CARD_EQ_REAL
    let ce ← REWRITE_RULE [IMP_CONJ_ALT] CARD_EQ_TRANS
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [COUNTABLE, ge_c] THEN
      FIRST_ASSUM (MP_TAC o ISPEC (← q "(:num)") o MATCH_MP
        CARD_EQ_LIMITED_POWERSET) THEN
      ASM_REWRITE_TAC [← GSYM INFINITE_CARD_LE] THEN
      MATCH_MP_TAC ce THEN
      TRANS_TAC CARD_EQ_TRANS (← q r"(:num->bool)") THEN
      REWRITE_TAC [er] THEN
      REWRITE_TAC [← GSYM CARD_EXP_UNIV] THEN MATCH_MP_TAC CARD_EXP_ABSORB THEN
      REWRITE_TAC [num_INFINITE] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CARD_LE_FINITE_INFINITE THEN
        ASM_REWRITE_TAC [FINITE_BOOL],
        TRANS_TAC CARD_LE_TRANS (← q "(:real)") THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC CARD_EQ_IMP_LE THEN
        TRANS_TAC CARD_EQ_TRANS (← q r"(:num->bool)") THEN
        REWRITE_TAC [CARD_EQ_REAL, CARD_EXP_UNIV, CARD_EQ_REFL]]))

  let CARD_EQ_COUNTABLE_SUBSETS_REAL ← prove
   r"{s:real->bool | COUNTABLE s} =_c (:real)"
   (MP_TAC (← ISPEC (← q "(:real)") CARD_EQ_COUNTABLE_SUBSETS_SUBREAL) THEN
    REWRITE_TAC [SUBSET_UNIV, CARD_LE_REFL, real_INFINITE])

  let CARD_LE_RESTRICTED_FUNSPACE ← prove
   r"!s:A->bool t:B->bool k.
        {f | IMAGE f s SUBSET t /\
             {x | ~(f x = k x)} SUBSET s /\
             FINITE {x | ~(f x = k x)}}
        <=_c {u | u SUBSET (s CROSS t) /\ FINITE u}"
   (← do
    let lemma ← prove
     r"!(f:A->B) s t. t SUBSET IMAGE f s ==> t <=_c s"
     (← do
      let lt ← REWRITE_RULE [IMP_CONJ_ALT] CARD_LE_TRANS
      pure (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP CARD_LE_SUBSET) THEN
        MATCH_MP_TAC lt THEN
        REWRITE_TAC [CARD_LE_IMAGE]))
    pure (REPEAT GEN_TAC THEN MATCH_MP_TAC lemma THEN EXISTS_TAC
       (← q r"\u:(A#B)->bool x. if ?y. (x,y) IN u then @y. (x,y) IN u else k x") THEN
      GEN_REWRITE_TAC id [SUBSET] THEN REWRITE_TAC [FORALL_IN_GSPEC] THEN
      X_GEN_TAC (← q r"f:A->B") THEN STRIP_TAC THEN
      REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN
      EXISTS_TAC (← q r"IMAGE (\x. x,(f:A->B) x) {x | ~(f x = k x)}") THEN
      ASM_SIMP_TAC [FINITE_IMAGE] THEN CONJ_TAC THENL
       [ALL_TAC,
        REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM, IN_CROSS] THEN
        ASM SET_TAC []] THEN
      REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q "x:A") THEN
      REWRITE_TAC [IN_IMAGE, IN_ELIM_THM, PAIR_EQ] THEN
      REWRITE_TAC [← GSYM CONJ_ASSOC, UNWIND_THM1, UNWIND_THM2] THEN
      ASM_CASES_TAC (← q r"(f:A->B) x = k x") THEN ASM_REWRITE_TAC []))

  let COUNTABLE_RESTRICTED_FUNSPACE ← prove
   r"!s:A->bool t:B->bool k.
        COUNTABLE s /\ COUNTABLE t
        ==> COUNTABLE {f | IMAGE f s SUBSET t /\
                           {x | ~(f x = k x)} SUBSET s /\
                           FINITE {x | ~(f x = k x)}}"
   (← do
    let lc ← REWRITE_RULE [IMP_CONJ] CARD_LE_COUNTABLE
    pure (REPEAT STRIP_TAC THEN
      mpPartRand lhand CARD_LE_RESTRICTED_FUNSPACE THEN
      MATCH_MP_TAC lc THEN
      ASM_SIMP_TAC [COUNTABLE_FINITE_SUBSETS, COUNTABLE_CROSS, COUNTABLE_IMAGE]))

  let CARD_LE_RESTRICTED_FUNSPACE_INFINITE ← prove
   r"!(s:A->bool) (t:B->bool) k.
        INFINITE s /\ ~(t = {})
        ==> {f | IMAGE f s SUBSET t /\
                 {x | ~(f x = k x)} SUBSET s /\
                 FINITE {x | ~(f x = k x)}} <=_c
            s *_c t"
   (← do
    let lt ← REWRITE_RULE [IMP_CONJ_ALT] CARD_LE_TRANS
    pure (REPEAT STRIP_TAC THEN
      mpPartLhand lhand CARD_LE_RESTRICTED_FUNSPACE THEN
      MATCH_MP_TAC lt THEN
      MATCH_MP_TAC CARD_EQ_IMP_LE THEN REWRITE_TAC [mul_c, ← GSYM CROSS] THEN
      MATCH_MP_TAC CARD_EQ_FINITE_SUBSETS THEN
      ASM_REWRITE_TAC [INFINITE_CROSS_EQ]))

  let CARD_EQ_RESTRICTED_FUNSPACE_INFINITE ← prove
   r"!(s:A->bool) (t:B->bool) k.
        INFINITE s /\ ~(?a. t SUBSET {a}) /\ IMAGE k s SUBSET t
        ==> {f | IMAGE f s SUBSET t /\
                 {x | ~(f x = k x)} SUBSET s /\
                 FINITE {x | ~(f x = k x)}} =_c
            s *_c t"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM CARD_LE_ANTISYM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CARD_LE_RESTRICTED_FUNSPACE_INFINITE THEN ASM SET_TAC [],
      MATCH_MP_TAC CARD_MUL2_ABSORB_LE_ALT THEN ASM_REWRITE_TAC []] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN (← q r"!x:A. ?y:B. y IN t /\ ~(k x = y)") MP_TAC THENL
       [ASM SET_TAC [], REWRITE_TAC [FORALL_AND_THM, le_c, SKOLEM_THM]] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"f:A->B") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"\a x. if x = a then (f:A->B) x else k x") THEN
      REWRITE_TAC [IN_ELIM_THM, SUBSET, FORALL_IN_IMAGE] THEN
      CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN X_GEN_TAC (← q "a:A"),
      SUBGOAL_THEN (← q r"?a:A. a IN s") STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC [MEMBER_NOT_EMPTY, FINITE_EMPTY, INFINITE], ALL_TAC] THEN
      REWRITE_TAC [le_c] THEN
      EXISTS_TAC (← q r"\b x. if x = a then b else (k:A->B) x") THEN
      REWRITE_TAC [IN_ELIM_THM, SUBSET, FORALL_IN_IMAGE] THEN
      CONJ_TAC THENL [X_GEN_TAC (← q "b:B"), ASM SET_TAC []]] THEN
    (STRIP_TAC THEN
     REPEAT (CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC]) THEN
     MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q "{a:A}") THEN
     REWRITE_TAC [FINITE_SING] THEN ASM SET_TAC []))

  let CARD_EQ_FUNSPACE ← prove
   r"!(s:A->bool) (t:B->bool) k.
        {f | IMAGE f s SUBSET t /\ {x | ~(f x = k x)} SUBSET s} =_c
        t ^_c s"
   (REWRITE_TAC [exp_c, SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [EQ_C_BIJECTIONS] THEN
    EXISTS_TAC (← q r"\f x. if x IN s then (f:A->B) x else ARB") THEN
    EXISTS_TAC (← q r"\f x. if x IN s then (f:A->B) x else k x") THEN
    REWRITE_TAC [IN_ELIM_THM, ARB] THEN REWRITE_TAC [FUN_EQ_THM] THEN
    MESON_TAC [])

  -- @@RETURN BEGIN
  return { CARD_EQ_RESTRICTED_POWERSET, CARD_EQ_LIMITED_POWERSET,
           CARD_EQ_FULLSIZE_POWERSET, CARD_EQ_EXP_INFINITE_FINITE,
           CARD_EQ_FINITE_SUBSETS, CARD_LE_LIST, CARD_LE_SUBPOWERSET,
           CARD_LE_FINITE_SUBSETS, CARD_LE_COUNTABLE_SUBSETS, CARD_LE_POWERSET,
           CARD_POWERSET_CONG, COUNTABLE_LIST_GEN, COUNTABLE_LIST,
           COUNTABLE_FINITE_SUBSETS, CARD_EQ_REAL_SEQUENCES,
           CARD_EQ_COUNTABLE_SUBSETS_SUBREAL, CARD_EQ_COUNTABLE_SUBSETS_REAL,
           CARD_LE_RESTRICTED_FUNSPACE, COUNTABLE_RESTRICTED_FUNSPACE,
           CARD_LE_RESTRICTED_FUNSPACE_INFINITE, CARD_EQ_RESTRICTED_FUNSPACE_INFINITE,
           CARD_EQ_FUNSPACE }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Cardinality properties of Cartesian products.  (card.ml 3185-3406)        -/
/- ------------------------------------------------------------------------- -/

structure Cartesian where
  -- @@FIELDS
  CARTESIAN_PRODUCT_CONST : thm
  CARD_LE_CARTESIAN_PRODUCT : thm
  CARD_EQ_CARTESIAN_PRODUCT : thm
  CARD_LE_CARTESIAN_PRODUCT_SUBINDEX : thm
  FINITE_CARTESIAN_PRODUCT : thm
  COUNTABLE_CARTESIAN_PRODUCT : thm
  CARD_EXP_FINITE_EQ : thm
  CARD_EQ_CARTESIAN_PRODUCT_DISJOINT_UNION : thm
  deriving Inhabited

@[nospecialize]
def setupCartesian [HolBase] (D : CardDeps) (BBasics : Basics) (BOrder : Order) (BArith : Arith) (BSquare : Square) (BCountable : Countable) (BReals : Reals) (BExp : Exp) (BPowerset : Powerset) :
    ExceptT String IO Cartesian := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON, NUM_REDUCE_CONV, SET_RULE, SET_TAC, .. } := D
  let { ARB, CARD_BOOL, CARD_SING, CARTESIAN_PRODUCT_EQ_EMPTY,
        CARTESIAN_PRODUCT_EQ_MEMBERS, CONTRAPOS_THM, COUNTABLE, EMPTY_GSPEC,
        EMPTY_SUBSET, EXTENSIONAL, FINITE_BOOL, FINITE_EMPTY, FINITE_IMAGE,
        FINITE_RESTRICTED_FUNSPACE, FINITE_SING, FINITE_SUBSET, FINITE_UNIONS,
        FORALL_IN_GSPEC, FORALL_IN_IMAGE, FORALL_IN_UNION, FORALL_PAIR_THM, FUN_EQ_THM,
        IMP_CONJ, .. } := D.core1
  let { INFINITE, IN_CARTESIAN_PRODUCT, IN_CROSS, IN_DIFF, IN_ELIM_THM, IN_GSPEC,
        IN_IMAGE, LEFT_IMP_EXISTS_THM, MEMBER_NOT_EMPTY, NOT_IN_EMPTY, PAIR_EQ, .. } := D.core2
  let { RESTRICTION, RESTRICTION_IN_CARTESIAN_PRODUCT, RESTRICTION_UNIQUE,
        RIGHT_EXISTS_IMP_THM, RIGHT_IMP_EXISTS_THM, SIMPLE_IMAGE, SKOLEM_THM, SUBSET,
        SUBSET_RESTRICT, UNIV_NOT_EMPTY, cartesian_product, ge_c, le_c, .. } := D.core3
  let { CARD_EQ_IMP_LE, CARD_LE_TRANS, CARD_LTE_TRANS, CARD_LT_IMP_LE, EQ_C_BIJECTIONS, .. } := BBasics
  let { CARD_LE_ANTISYM, CARD_LE_CARD, CARD_LE_IMAGE, CARD_LE_SING, CARD_LE_SUBSET,
        CARD_NOT_LE, INFINITE_CARD_LE, .. } := BOrder
  let { CARD_ADD_C, CARD_LT_IMP_SUC_LE, .. } := BArith
  let { CARD_ADD_FINITE_EQ, .. } := BSquare
  let { COUNTABLE_EMPTY, COUNTABLE_IMAGE, COUNTABLE_SUBSET, COUNTABLE_UNIONS,
        FINITE_IMP_COUNTABLE, .. } := BCountable
  let { CARD_EQ_REAL, CARD_LT_NUM_REAL, .. } := BReals
  let { CARD_EXP_UNIV, CARD_LE_EXP_RIGHT, exp_c, .. } := BExp
  let { COUNTABLE_RESTRICTED_FUNSPACE, .. } := BPowerset
  -- @@SCOPE END

  let CARTESIAN_PRODUCT_CONST ← prove
   r"!(s:A->bool) (t:B->bool).
        cartesian_product t (\i. s) = s ^_c t"
   (REWRITE_TAC [EXTENSIONAL, IN_ELIM_THM, cartesian_product, exp_c, ARB] THEN
    SET_TAC [])

  let CARD_LE_CARTESIAN_PRODUCT ← prove
   r"!(s:K->A->bool) (t:K->B->bool) k.
        (!i. i IN k ==> s i <=_c t i)
        ==> cartesian_product k s <=_c cartesian_product k t"
   (REPEAT GEN_TAC THEN REWRITE_TAC [le_c] THEN
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"f:K->A->B") THEN DISCH_TAC THEN
    EXISTS_TAC (← q r"\g i. if i IN k then (f:K->A->B) i ((g:K->A) i) else ARB") THEN
    REWRITE_TAC [] THEN CONJ_TAC THENL
     [REWRITE_TAC [cartesian_product, IN_ELIM_THM, EXTENSIONAL] THEN
      ASM_MESON_TAC [],
      REPEAT STRIP_TAC THEN MATCH_MP_TAC CARTESIAN_PRODUCT_EQ_MEMBERS THEN
      MAP_EVERY EXISTS_TAC [← q r"k:K->bool", ← q r"s:K->A->bool"] THEN
      ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q "i:K") THEN DISCH_TAC THEN
      RULE_ASSUM_TAC (REWRITE_RULE [FUN_EQ_THM]) THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o SPEC (← q "i:K"))) THEN
      RULE_ASSUM_TAC (REWRITE_RULE [cartesian_product, IN_ELIM_THM]) THEN
      ASM_MESON_TAC []])

  let CARD_EQ_CARTESIAN_PRODUCT ← prove
   r"!(s:K->A->bool) (t:K->B->bool) k.
        (!i. i IN k ==> s i =_c t i)
        ==> cartesian_product k s =_c cartesian_product k t"
   (SIMP_TAC [← GSYM CARD_LE_ANTISYM, CARD_LE_CARTESIAN_PRODUCT])

  let CARD_LE_CARTESIAN_PRODUCT_SUBINDEX ← prove
   r"!(s:K->A->bool) k l.
        k SUBSET l /\ ~(cartesian_product l s = {})
        ==> cartesian_product k s <=_c cartesian_product l s"
   (REPEAT STRIP_TAC THEN TRANS_TAC CARD_LE_TRANS
     (← q r"IMAGE (\(f:K->A) i. if i IN k then f i else ARB)
            (cartesian_product l s)") THEN
    REWRITE_TAC [CARD_LE_IMAGE] THEN MATCH_MP_TAC CARD_LE_SUBSET THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [← GSYM MEMBER_NOT_EMPTY]) THEN
    REWRITE_TAC [cartesian_product, SUBSET, IN_ELIM_THM, IN_IMAGE,
                EXTENSIONAL, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"z:K->A") THEN STRIP_TAC THEN
    X_GEN_TAC (← q r"x:K->A") THEN STRIP_TAC THEN
    EXISTS_TAC (← q r"\i. if i IN k then (x:K->A) i else z i") THEN
    REWRITE_TAC [FUN_EQ_THM] THEN ASM SET_TAC [])

  let FINITE_CARTESIAN_PRODUCT ← prove
   r"!(s:K->A->bool) k.
        FINITE(cartesian_product k s) <=>
        cartesian_product k s = {} \/
        FINITE {i | i IN k /\ ~(?a. s i SUBSET {a})} /\
        (!i. i IN k ==> FINITE(s i))"
   (← do
    let lt ← REWRITE_RULE [IMP_CONJ] CARD_LE_TRANS
    let tT ← q "T"
    pure (REPEAT GEN_TAC THEN
      ASM_CASES_TAC (← q r"cartesian_product k (s:K->A->bool) = {}") THEN
      ASM_REWRITE_TAC [FINITE_EMPTY] THEN EQ_TAC THENL
       [DISCH_TAC THEN CONJ_TAC THENL
         [UNDISCH_TAC (← q r"FINITE (cartesian_product k (s:K->A->bool))") THEN
          GEN_REWRITE_TAC id [← GSYM CONTRAPOS_THM] THEN
          REWRITE_TAC [← GSYM INFINITE] THEN DISCH_TAC THEN
          ABBREV_TAC (← q r"l = {i | i IN k /\ ~(?a. (s:K->A->bool) i SUBSET {a})}") THEN
          REWRITE_TAC [INFINITE_CARD_LE] THEN
          TRANS_TAC CARD_LE_TRANS (← q r"cartesian_product l (s:K->A->bool)") THEN
          EXPAND_TAC "l" THEN
          ASM_SIMP_TAC [CARD_LE_CARTESIAN_PRODUCT_SUBINDEX, SUBSET_RESTRICT] THEN
          TRANS_TAC CARD_LE_TRANS (← q r"cartesian_product l (\i:K. (:bool))") THEN
          CONJ_TAC THENL
           [REWRITE_TAC [CARTESIAN_PRODUCT_CONST] THEN
            TRANS_TAC CARD_LE_TRANS (← q "(:real)") THEN
            SIMP_TAC [CARD_LT_NUM_REAL, CARD_LT_IMP_LE] THEN
            TRANS_TAC CARD_LE_TRANS (← q r"(:num->bool)") THEN
            SIMP_TAC [CARD_EQ_REAL, CARD_EQ_IMP_LE] THEN
            REWRITE_TAC [← GSYM CARD_EXP_UNIV] THEN
            MATCH_MP_TAC CARD_LE_EXP_RIGHT THEN
            ASM_REWRITE_TAC [← GSYM INFINITE_CARD_LE, UNIV_NOT_EMPTY],
            MATCH_MP_TAC CARD_LE_CARTESIAN_PRODUCT THEN
            EXPAND_TAC "l" THEN REWRITE_TAC [IN_ELIM_THM] THEN
            REWRITE_TAC [← GSYM CARD_LE_SING, CARD_NOT_LE] THEN
            GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
             (MP_TAC o ISPEC tT o MATCH_MP CARD_LT_IMP_SUC_LE)) THEN
            MATCH_MP_TAC lt THEN
            SIMP_TAC [CARD_LE_CARD, FINITE_BOOL, CARD_ADD_FINITE_EQ, FINITE_SING,
                     CARD_ADD_C, CARD_SING, CARD_BOOL] THEN
            CONV_TAC NUM_REDUCE_CONV],
          X_GEN_TAC (← q "i:K") THEN DISCH_TAC THEN
          MATCH_MP_TAC FINITE_SUBSET THEN
          EXISTS_TAC (← q r"IMAGE (\x:K->A. x i) (cartesian_product k s)") THEN
          ASM_SIMP_TAC [FINITE_IMAGE, SUBSET, IN_IMAGE] THEN
          FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [← GSYM MEMBER_NOT_EMPTY]) THEN
          REWRITE_TAC [cartesian_product, SUBSET, IN_ELIM_THM, IN_IMAGE,
                      EXTENSIONAL, LEFT_IMP_EXISTS_THM] THEN
          X_GEN_TAC (← q r"z:K->A") THEN STRIP_TAC THEN
          X_GEN_TAC (← q "x:A") THEN STRIP_TAC THEN
          EXISTS_TAC (← q r"\j. if j = i then x else (z:K->A) j") THEN
          ASM_SIMP_TAC [] THEN ASM_MESON_TAC []],
        STRIP_TAC THEN
        ABBREV_TAC (← q r"l = {i | i IN k /\ ~(?a. (s:K->A->bool) i SUBSET {a})}") THEN
        SUBGOAL_THEN (← q r"?a. !i. i IN k DIFF l ==> (s:K->A->bool) i = {a i}")
        STRIP_ASSUME_TAC THENL
         [REWRITE_TAC [← GSYM SKOLEM_THM, RIGHT_EXISTS_IMP_THM] THEN
          X_GEN_TAC (← q "i:K") THEN EXPAND_TAC "l" THEN
          SIMP_TAC [IN_DIFF, IN_ELIM_THM, IMP_CONJ] THEN DISCH_TAC THEN
          FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV
           [CARTESIAN_PRODUCT_EQ_EMPTY]) THEN
          ASM SET_TAC [],
          MATCH_MP_TAC FINITE_SUBSET THEN
          EXISTS_TAC
           (← q r"{f | IMAGE f l SUBSET UNIONS {(s:K->A->bool) i | i IN l} /\
                 {i | ~(f i = if i IN k then a i else ARB)} SUBSET l}") THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC FINITE_RESTRICTED_FUNSPACE THEN
            ASM_REWRITE_TAC [FINITE_UNIONS, FORALL_IN_GSPEC] THEN
            ASM_SIMP_TAC [SIMPLE_IMAGE, FINITE_IMAGE] THEN ASM SET_TAC [],
            GEN_REWRITE_TAC id [SUBSET] THEN X_GEN_TAC (← q r"f:K->A") THEN
            REWRITE_TAC [cartesian_product, IN_ELIM_THM, EXTENSIONAL] THEN
            ASM SET_TAC []]]]))

  let COUNTABLE_CARTESIAN_PRODUCT ← prove
   r"!(s:K->A->bool) k.
        COUNTABLE(cartesian_product k s) <=>
        cartesian_product k s = {} \/
        FINITE {i | i IN k /\ ~(?a. s i SUBSET {a})} /\
        (!i. i IN k ==> COUNTABLE(s i))"
   (← do
    let m ← MESON [FINITE_SUBSET]
     (← q r"FINITE t ==> (s SUBSET t /\ FINITE s <=> s SUBSET t)")
    let lt ← REWRITE_RULE [IMP_CONJ] CARD_LE_TRANS
    let tT ← q "T"
    pure (REPEAT GEN_TAC THEN
      ASM_CASES_TAC (← q r"cartesian_product k (s:K->A->bool) = {}") THEN
      ASM_REWRITE_TAC [COUNTABLE_EMPTY] THEN EQ_TAC THENL
       [DISCH_TAC THEN CONJ_TAC THENL
         [UNDISCH_TAC (← q r"COUNTABLE(cartesian_product k (s:K->A->bool))") THEN
          GEN_REWRITE_TAC id [← GSYM CONTRAPOS_THM] THEN
          REWRITE_TAC [← GSYM INFINITE] THEN DISCH_TAC THEN
          ABBREV_TAC (← q r"l = {i | i IN k /\ ~(?a. (s:K->A->bool) i SUBSET {a})}") THEN
          REWRITE_TAC [COUNTABLE, ge_c, CARD_NOT_LE] THEN
          TRANS_TAC CARD_LTE_TRANS (← q r"cartesian_product l (s:K->A->bool)") THEN
          EXPAND_TAC "l" THEN
          ASM_SIMP_TAC [CARD_LE_CARTESIAN_PRODUCT_SUBINDEX, SUBSET_RESTRICT] THEN
          TRANS_TAC CARD_LTE_TRANS (← q r"cartesian_product l (\i:K. (:bool))") THEN
          CONJ_TAC THENL
           [REWRITE_TAC [CARTESIAN_PRODUCT_CONST] THEN
            TRANS_TAC CARD_LTE_TRANS (← q "(:real)") THEN
            REWRITE_TAC [CARD_LT_NUM_REAL] THEN
            TRANS_TAC CARD_LE_TRANS (← q r"(:num->bool)") THEN
            SIMP_TAC [CARD_EQ_REAL, CARD_EQ_IMP_LE] THEN
            REWRITE_TAC [← GSYM CARD_EXP_UNIV] THEN
            MATCH_MP_TAC CARD_LE_EXP_RIGHT THEN
            ASM_REWRITE_TAC [← GSYM INFINITE_CARD_LE, UNIV_NOT_EMPTY],
            MATCH_MP_TAC CARD_LE_CARTESIAN_PRODUCT THEN
            EXPAND_TAC "l" THEN REWRITE_TAC [IN_ELIM_THM] THEN
            REWRITE_TAC [← GSYM CARD_LE_SING, CARD_NOT_LE] THEN
            GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
             (MP_TAC o ISPEC tT o MATCH_MP CARD_LT_IMP_SUC_LE)) THEN
            MATCH_MP_TAC lt THEN
            SIMP_TAC [CARD_LE_CARD, FINITE_BOOL, CARD_ADD_FINITE_EQ, FINITE_SING,
                     CARD_ADD_C, CARD_SING, CARD_BOOL] THEN
            CONV_TAC NUM_REDUCE_CONV],
          X_GEN_TAC (← q "i:K") THEN DISCH_TAC THEN
          MATCH_MP_TAC COUNTABLE_SUBSET THEN
          EXISTS_TAC (← q r"IMAGE (\x:K->A. x i) (cartesian_product k s)") THEN
          ASM_SIMP_TAC [COUNTABLE_IMAGE, SUBSET, IN_IMAGE] THEN
          FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [← GSYM MEMBER_NOT_EMPTY]) THEN
          REWRITE_TAC [cartesian_product, SUBSET, IN_ELIM_THM, IN_IMAGE,
                      EXTENSIONAL, LEFT_IMP_EXISTS_THM] THEN
          X_GEN_TAC (← q r"z:K->A") THEN STRIP_TAC THEN
          X_GEN_TAC (← q "x:A") THEN STRIP_TAC THEN
          EXISTS_TAC (← q r"\j. if j = i then x else (z:K->A) j") THEN
          ASM_SIMP_TAC [] THEN ASM_MESON_TAC []],
        STRIP_TAC THEN
        ABBREV_TAC (← q r"l = {i | i IN k /\ ~(?a. (s:K->A->bool) i SUBSET {a})}") THEN
        SUBGOAL_THEN (← q r"?a. !i. i IN k DIFF l ==> (s:K->A->bool) i = {a i}")
        STRIP_ASSUME_TAC THENL
         [REWRITE_TAC [← GSYM SKOLEM_THM, RIGHT_EXISTS_IMP_THM] THEN
          X_GEN_TAC (← q "i:K") THEN EXPAND_TAC "l" THEN
          SIMP_TAC [IN_DIFF, IN_ELIM_THM, IMP_CONJ] THEN DISCH_TAC THEN
          FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV
           [CARTESIAN_PRODUCT_EQ_EMPTY]) THEN
          ASM SET_TAC [],
          MATCH_MP_TAC COUNTABLE_SUBSET THEN
          EXISTS_TAC
           (← q r"{f | IMAGE f l SUBSET UNIONS {(s:K->A->bool) i | i IN l} /\
                 {i | ~(f i = if i IN k then a i else ARB)} SUBSET l /\
                 FINITE {i | ~(f i = if i IN k then a i else ARB)}}") THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC COUNTABLE_RESTRICTED_FUNSPACE THEN
            ASM_SIMP_TAC [FINITE_IMP_COUNTABLE] THEN
            MATCH_MP_TAC COUNTABLE_UNIONS THEN
            ASM_SIMP_TAC [SIMPLE_IMAGE, FORALL_IN_IMAGE, FINITE_IMP_COUNTABLE,
                         COUNTABLE_IMAGE] THEN
            ASM SET_TAC [],
            GEN_REWRITE_TAC id [SUBSET] THEN X_GEN_TAC (← q r"f:K->A") THEN
            REWRITE_TAC [cartesian_product, IN_ELIM_THM, EXTENSIONAL] THEN
            ASM_SIMP_TAC [m] THEN
            ASM SET_TAC []]]]))

  let CARD_EXP_FINITE_EQ ← prove
   r"!(s:A->bool) (t:B->bool).
        FINITE(s ^_c t) <=>
        (?a. s SUBSET {a}) \/ t = {} \/ FINITE s /\ FINITE t"
   (← do
    let s2 ← SET_RULE (← q r"~(t = {}) ==> ((!a. a IN t ==> P) <=> P)")
    let m1 ← MESON [] (← q r"(?x. P x /\ Q x) <=> ~(!x. P x ==> ~Q x)")
    pure (REPEAT GEN_TAC THEN
      REWRITE_TAC [← GSYM CARTESIAN_PRODUCT_CONST, FINITE_CARTESIAN_PRODUCT] THEN
      REWRITE_TAC [CARTESIAN_PRODUCT_EQ_EMPTY] THEN
      ASM_CASES_TAC (← q r"t:B->bool = {}") THEN
      ASM_REWRITE_TAC [NOT_IN_EMPTY, EMPTY_GSPEC, FINITE_EMPTY] THEN
      ASM_CASES_TAC (← q r"?a:A. s SUBSET {a}") THEN
      ASM_REWRITE_TAC [EMPTY_GSPEC, FINITE_EMPTY, IN_GSPEC] THEN
      REWRITE_TAC [m1] THEN
      ASM_SIMP_TAC [s2] THEN
      ASM_MESON_TAC [FINITE_SUBSET, FINITE_SING, EMPTY_SUBSET]))

  let CARD_EQ_CARTESIAN_PRODUCT_DISJOINT_UNION ← prove
   r"!(f:K->A->bool) k l.
        DISJOINT k l
        ==> cartesian_product (k UNION l) f =_c
            cartesian_product k f CROSS cartesian_product l f"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [EQ_C_BIJECTIONS] THEN
    EXISTS_TAC (← q r"\(f:K->A). RESTRICTION k f,RESTRICTION l f") THEN
    EXISTS_TAC (← q r"\((f:K->A),g) x. if x IN k then f x else g x") THEN
    REWRITE_TAC [FORALL_PAIR_THM, IN_CROSS, PAIR_EQ] THEN
    REWRITE_TAC [RESTRICTION_IN_CARTESIAN_PRODUCT] THEN
    REWRITE_TAC [RESTRICTION_UNIQUE, IN_CARTESIAN_PRODUCT] THEN
    SIMP_TAC [FORALL_IN_UNION] THEN
    REWRITE_TAC [EXTENSIONAL, IN_ELIM_THM] THEN
    REWRITE_TAC [FUN_EQ_THM, RESTRICTION] THEN ASM SET_TAC [])

  -- @@RETURN BEGIN
  return { CARTESIAN_PRODUCT_CONST, CARD_LE_CARTESIAN_PRODUCT, CARD_EQ_CARTESIAN_PRODUCT,
           CARD_LE_CARTESIAN_PRODUCT_SUBINDEX, FINITE_CARTESIAN_PRODUCT,
           COUNTABLE_CARTESIAN_PRODUCT, CARD_EXP_FINITE_EQ,
           CARD_EQ_CARTESIAN_PRODUCT_DISJOINT_UNION }
  -- @@RETURN END

end HolLibrary.Card
