/- ========================================================================= -/
/- All you wanted to know about reflexive symmetric and transitive closures. -/
/- ========================================================================= -/
/- File: HolLibrary/RSTC.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/rstc.ml`, by hand, in file order, in
  the style of HolLibrary/Analysis.lean (see there and HolMath/Base.lean for
  the conventions).  Each section of rstc.ml is a bundle (a `structure`)
  built by a `setup` function; SessionLibrary/RSTC.lean builds the bundles
  in order and exports every name under its HOL Light name.

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more such rules
  (ARITH_RULE in RELPOW_SEQUENCE) they are bound first, in OCaml's order.
-/

import HolMath

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolLibrary.RSTC

/- ------------------------------------------------------------------------- -/
/- What rstc.ml uses from the core library (supplied by Session).            -/
/- ------------------------------------------------------------------------- -/

/-- Theorems rstc.ml uses from the core library. -/
structure CoreThms1 where
  (ADD_CLAUSES ARITH DISJ_ACI DISJ_SYM EQ_SYM_EQ FUN_EQ_THM IMP_IMP
   LEFT_EXISTS_AND_THM LEFT_IMP_EXISTS_THM LE_0 LE_LT LE_REFL LE_SUC_LT LT
   NOT_SUC SWAP_EXISTS_THM SWAP_FORALL_THM UNWIND_THM1 WF WF_SUBSET
   num_RECURSION : thm)
  deriving Inhabited

/-- What rstc.ml uses from Session besides theorems. -/
structure RSTCDeps where
  -- definitions
  new_definition : String → ExceptT String IO thm
  new_inductive_definition : String → ExceptT String IO (thm × thm × thm)
  new_recursive_definition : thm → String → ExceptT String IO thm
  -- parser state
  prioritize_num : IO Unit
  -- decision procedures and tactics
  ARITH_RULE : term → ExceptT String IO thm
  ASM_MESON_TAC : List thm → tactic
  INDUCT_TAC : tactic
  MESON_TAC : List thm → tactic
  core1 : CoreThms1

/- ------------------------------------------------------------------------- -/
/- Little lemmas about equivalent forms of symmetry and transitivity;        -/
/- reflexive, symmetric and transitive closure.  (rstc.ml 1-166)             -/
/- ------------------------------------------------------------------------- -/

structure Closures where
  -- @@FIELDS
  RULE_INDUCT_TAC : thm_tactic
  SYM_ALT : thm
  TRANS_ALT : thm
  RC_RULES : thm
  RC_INDUCT : thm
  RC_CASES : thm
  RC_INC : thm
  RC_REFL : thm
  RC_EXPLICIT : thm
  RC_MONO : thm
  RC_CLOSED : thm
  RC_IDEMP : thm
  RC_SYM : thm
  RC_TRANS : thm
  SC_RULES : thm
  SC_INDUCT : thm
  SC_CASES : thm
  SC_INC : thm
  SC_SYM : thm
  SC_EXPLICIT : thm
  SC_MONO : thm
  SC_CLOSED : thm
  SC_IDEMP : thm
  SC_REFL : thm
  TC_RULES : thm
  TC_INDUCT : thm
  TC_CASES : thm
  TC_INC : thm
  TC_TRANS : thm
  TC_MONO : thm
  TC_CLOSED : thm
  TC_IDEMP : thm
  TC_REFL : thm
  TC_SYM : thm
  deriving Inhabited

@[nospecialize]
def setupClosures [HolBase] (D : RSTCDeps) :
    ExceptT String IO Closures := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, new_inductive_definition, prioritize_num, .. } := D
  let { EQ_SYM_EQ, FUN_EQ_THM, LEFT_IMP_EXISTS_THM, .. } := D.core1
  -- @@SCOPE END
  prioritize_num

  let RULE_INDUCT_TAC : thm_tactic ← pure
    (MATCH_MP_TAC o DISCH_ALL o SPEC_ALL o UNDISCH o SPEC_ALL)

  -- Little lemmas about equivalent forms of symmetry and transitivity.

  let SYM_ALT ← prove
   r"!R:A->A->bool. (!x y. R x y ==> R y x) <=> (!x y. R x y <=> R y x)"
   (GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
     [EQ_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC,
      FIRST_ASSUM (fun th => GEN_REWRITE_TAC id [th])] THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC)

  let TRANS_ALT ← prove
   r"!(R:A->A->bool) (S:A->A->bool) U.
        (!x z. (?y. R x y /\ S y z) ==> U x z) <=>
        (!x y z. R x y /\ S y z ==> U x z)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [])

  -- Reflexive closure

  let (RC_RULES, RC_INDUCT, RC_CASES) ← new_inductive_definition
   r"(!x y. R x y ==> RC R x y) /\
   (!x:A. RC R x x)"

  let RC_INC ← prove
   r"!(R:A->A->bool) x y. R x y ==> RC R x y"
   (REWRITE_TAC [RC_RULES])

  let RC_REFL ← prove
   r"!(R:A->A->bool) x. RC R x x"
   (REWRITE_TAC [RC_RULES])

  let RC_EXPLICIT ← prove
   r"!(R:A->A->bool) x y. RC R x y <=> R x y \/ (x = y)"
   (REWRITE_TAC [RC_CASES, EQ_SYM_EQ])

  let RC_MONO ← prove
   r"!(R:A->A->bool) S.
        (!x y. R x y ==> S x y) ==>
            (!x y. RC R x y ==> RC S x y)"
   (MESON_TAC [RC_CASES])

  let RC_CLOSED ← prove
   r"!R:A->A->bool. (RC R = R) <=> !x. R x x"
   (REWRITE_TAC [FUN_EQ_THM, RC_EXPLICIT] THEN MESON_TAC [])

  let RC_IDEMP ← prove
   r"!R:A->A->bool. RC(RC R) = RC R"
   (REWRITE_TAC [RC_CLOSED, RC_REFL])

  let RC_SYM ← prove
   r"!R:A->A->bool.
        (!x y. R x y ==> R y x) ==> (!x y. RC R x y ==> RC R y x)"
   (MESON_TAC [RC_CASES])

  let RC_TRANS ← prove
   r"!R:A->A->bool.
        (!x y z. R x y /\ R y z ==> R x z) ==>
        (!x y z. RC R x y /\ RC R y z ==> RC R x z)"
   (REWRITE_TAC [RC_CASES] THEN MESON_TAC [])

  -- Symmetric closure

  let (SC_RULES, SC_INDUCT, SC_CASES) ← new_inductive_definition
   r"(!x y. R x y ==> SC R x y) /\
   (!x:A y. SC R x y ==> SC R y x)"

  let SC_INC ← prove
   r"!(R:A->A->bool) x y. R x y ==> SC R x y"
   (REWRITE_TAC [SC_RULES])

  let SC_SYM ← prove
   r"!(R:A->A->bool) x y. SC R x y ==> SC R y x"
   (REWRITE_TAC [SC_RULES])

  let SC_EXPLICIT ← prove
   r"!R:A->A->bool. SC(R) x y <=> R x y \/ R y x"
   (GEN_TAC THEN EQ_TAC THENL
     [RULE_INDUCT_TAC SC_INDUCT THEN MESON_TAC [], MESON_TAC [SC_CASES]])

  let SC_MONO ← prove
   r"!(R:A->A->bool) S.
        (!x y. R x y ==> S x y) ==>
        (!x y. SC R x y ==> SC S x y)"
   (MESON_TAC [SC_EXPLICIT])

  let SC_CLOSED ← prove
   r"!R:A->A->bool. (SC R = R) <=> !x y. R x y ==> R y x"
   (REWRITE_TAC [FUN_EQ_THM, SC_EXPLICIT] THEN MESON_TAC [])

  let SC_IDEMP ← prove
   r"!R:A->A->bool. SC(SC R) = SC R"
   (REWRITE_TAC [SC_CLOSED, SC_SYM])

  let SC_REFL ← prove
   r"!R:A->A->bool. (!x. R x x) ==> (!x. SC R x x)"
   (MESON_TAC [SC_EXPLICIT])

  -- Transitive closure

  let (TC_RULES, TC_INDUCT, TC_CASES) ← new_inductive_definition
   r"(!x y. R x y ==> TC R x y) /\
    (!(x:A) y z. TC R x y /\ TC R y z ==> TC R x z)"

  let TC_INC ← prove
   r"!(R:A->A->bool) x y. R x y ==> TC R x y"
   (REWRITE_TAC [TC_RULES])

  let TC_TRANS ← prove
   r"!(R:A->A->bool) x y z. TC R x y /\ TC R y z ==> TC R x z"
   (REWRITE_TAC [TC_RULES])

  let TC_MONO ← prove
   r"!(R:A->A->bool) S.
        (!x y. R x y ==> S x y) ==>
        (!x y. TC R x y ==> TC S x y)"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC TC_INDUCT THEN ASM_MESON_TAC [TC_RULES])

  let TC_CLOSED ← prove
   r"!R:A->A->bool. (TC R = R) <=> !x y z. R x y /\ R y z ==> R x z"
   (GEN_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN EQ_TAC THENL
     [MESON_TAC [TC_RULES], REPEAT STRIP_TAC] THEN
    EQ_TAC THENL
     [RULE_INDUCT_TAC TC_INDUCT THEN ASM_MESON_TAC [],
      MESON_TAC [TC_RULES]])

  let TC_IDEMP ← prove
   r"!R:A->A->bool. TC(TC R) = TC R"
   (REWRITE_TAC [TC_CLOSED, TC_TRANS])

  let TC_REFL ← prove
   r"!R:A->A->bool. (!x. R x x) ==> (!x. TC R x x)"
   (MESON_TAC [TC_INC])

  let TC_SYM ← prove
   r"!R:A->A->bool. (!x y. R x y ==> R y x) ==> (!x y. TC R x y ==> TC R y x)"
   (GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC TC_INDUCT THEN
    ASM_MESON_TAC [TC_RULES])

  -- @@RETURN BEGIN
  return { RULE_INDUCT_TAC, SYM_ALT, TRANS_ALT, RC_RULES, RC_INDUCT, RC_CASES, RC_INC,
           RC_REFL, RC_EXPLICIT, RC_MONO, RC_CLOSED, RC_IDEMP, RC_SYM, RC_TRANS,
           SC_RULES, SC_INDUCT, SC_CASES, SC_INC, SC_SYM, SC_EXPLICIT, SC_MONO,
           SC_CLOSED, SC_IDEMP, SC_REFL, TC_RULES, TC_INDUCT, TC_CASES, TC_INC, TC_TRANS,
           TC_MONO, TC_CLOSED, TC_IDEMP, TC_REFL, TC_SYM }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Commutativity properties of the three basic closure operations; left and  -/
/- right variants of TC.  (rstc.ml 168-246)                                  -/
/- ------------------------------------------------------------------------- -/

structure Commute where
  -- @@FIELDS
  RC_SC : thm
  SC_RC : thm
  RC_TC : thm
  TC_RC : thm
  TC_SC : thm
  SC_TC : thm
  TC_TRANS_L : thm
  TC_TRANS_R : thm
  TC_CASES_L : thm
  TC_CASES_R : thm
  TC_INDUCT_L : thm
  TC_INDUCT_R : thm
  WF_TC : thm
  deriving Inhabited

@[nospecialize]
def setupCommute [HolBase] (D : RSTCDeps) (BClosures : Closures) :
    ExceptT String IO Commute := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, .. } := D
  let { FUN_EQ_THM, WF, WF_SUBSET, .. } := D.core1
  let { RC_EXPLICIT, RC_INDUCT, RC_MONO, RC_RULES, RC_TRANS, RULE_INDUCT_TAC,
        SC_EXPLICIT, SC_INDUCT, SC_RULES, TC_INC, TC_INDUCT, TC_MONO, TC_RULES, TC_SYM, .. } := BClosures
  -- @@SCOPE END
  -- Commutativity properties of the three basic closure operations

  let RC_SC ← prove
   r"!R:A->A->bool. RC(SC R) = SC(RC R)"
   (REWRITE_TAC [FUN_EQ_THM, RC_EXPLICIT, SC_EXPLICIT] THEN MESON_TAC [])

  let SC_RC ← prove
   r"!R:A->A->bool. SC(RC R) = RC(SC R)"
   (REWRITE_TAC [RC_SC])

  let RC_TC ← prove
   r"!R:A->A->bool. RC(TC R) = TC(RC R)"
   (REWRITE_TAC [FUN_EQ_THM] THEN REPEAT GEN_TAC THEN EQ_TAC THENL
     [RULE_INDUCT_TAC RC_INDUCT THEN MESON_TAC [TC_RULES, RC_RULES, TC_MONO],
      RULE_INDUCT_TAC TC_INDUCT THEN MESON_TAC [RC_TRANS, TC_RULES, RC_MONO]])

  let TC_RC ← prove
   r"!R:A->A->bool. TC(RC R) = RC(TC R)"
   (REWRITE_TAC [RC_TC])

  let TC_SC ← prove
   r"!(R:A->A->bool) x y. SC(TC R) x y ==> TC(SC R) x y"
   (GEN_TAC THEN MATCH_MP_TAC SC_INDUCT THEN
    MESON_TAC [TC_MONO, TC_SYM, SC_RULES])

  let SC_TC ← prove
   r"!(R:A->A->bool) x y. SC(TC R) x y ==> TC(SC R) x y"
   (REWRITE_TAC [TC_SC])

  -- Left and right variants of TC.

  let TC_TRANS_L ← prove
   r"!(R:A->A->bool) x y z. TC R x y /\ R y z ==> TC R x z"
   (MESON_TAC [TC_RULES])

  let TC_TRANS_R ← prove
   r"!(R:A->A->bool) x y z. R x y /\ TC R y z ==> TC R x z"
   (MESON_TAC [TC_RULES])

  let TC_CASES_L ← prove
   r"!(R:A->A->bool) x z. TC R x z <=> R x z \/ (?y. TC R x y /\ R y z)"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [RULE_INDUCT_TAC TC_INDUCT THEN MESON_TAC [TC_RULES], MESON_TAC [TC_RULES]])

  let TC_CASES_R ← prove
   r"!(R:A->A->bool) x z. TC R x z <=> R x z \/ (?y. R x y /\ TC R y z)"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [RULE_INDUCT_TAC TC_INDUCT THEN MESON_TAC [TC_RULES], MESON_TAC [TC_RULES]])

  let TC_INDUCT_L ← prove
   r"!(R:A->A->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x y z. P x y /\ R y z ==> P x z) ==>
            (!x y. TC R x y ==> P x y)"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"!y:A z. TC(R) y z ==> !x:A. P x y ==> P x z") MP_TAC THENL
     [MATCH_MP_TAC TC_INDUCT THEN ASM_MESON_TAC [], ASM_MESON_TAC [TC_CASES_R]])

  let TC_INDUCT_R ← prove
   r"!(R:A->A->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x z. (?y. R x y /\ P y z) ==> P x z) ==>
            (!x y. TC R x y ==> P x y)"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"!x:A y. TC(R) x y ==> !z:A. P y z ==> P x z") MP_TAC THENL
     [MATCH_MP_TAC TC_INDUCT THEN ASM_MESON_TAC [], ASM_MESON_TAC [TC_CASES_L]])

  let WF_TC ← prove
   r"!R:A->A->bool. WF(TC R) <=> WF(R)"
   (GEN_TAC THEN EQ_TAC THENL
     [MESON_TAC [WF_SUBSET, TC_INC],
      REWRITE_TAC [WF] THEN DISCH_TAC THEN X_GEN_TAC (← q r"P:A->bool") THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"\y:A. ?z. P z /\ TC(R) z y")) THEN
      REWRITE_TAC [] THEN MESON_TAC [TC_CASES_L]])

  -- @@RETURN BEGIN
  return { RC_SC, SC_RC, RC_TC, TC_RC, TC_SC, SC_TC, TC_TRANS_L, TC_TRANS_R, TC_CASES_L,
           TC_CASES_R, TC_INDUCT_L, TC_INDUCT_R, WF_TC }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Reflexive symmetric closure; reflexive transitive closure.                -/
/- (rstc.ml 248-383)                                                         -/
/- ------------------------------------------------------------------------- -/

structure RscRtc where
  -- @@FIELDS
  RSC : thm
  RSC_INC : thm
  RSC_REFL : thm
  RSC_SYM : thm
  RSC_CASES : thm
  RSC_INDUCT : thm
  RSC_MONO : thm
  RSC_CLOSED : thm
  RSC_IDEMP : thm
  RTC : thm
  RTC_INC : thm
  RTC_REFL : thm
  RTC_TRANS : thm
  RTC_RULES : thm
  RTC_TRANS_L : thm
  RTC_TRANS_R : thm
  RTC_CASES : thm
  RTC_CASES_L : thm
  RTC_CASES_R : thm
  RTC_INDUCT : thm
  RTC_INDUCT_L : thm
  RTC_INDUCT_R : thm
  RTC_MONO : thm
  RTC_CLOSED : thm
  RTC_IDEMP : thm
  RTC_SYM : thm
  RTC_STUTTER : thm
  TC_RTC_CASES_L : thm
  TC_RTC_CASES_R : thm
  TC_TC_RTC_CASES : thm
  TC_RTC_TC_CASES : thm
  RTC_NE_IMP_TC : thm
  deriving Inhabited

@[nospecialize]
def setupRscRtc [HolBase] (D : RSTCDeps) (BClosures : Closures) (BCommute : Commute) :
    ExceptT String IO RscRtc := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, new_definition, .. } := D
  let { DISJ_ACI, FUN_EQ_THM, IMP_IMP, .. } := D.core1
  let { RC_CASES, RC_EXPLICIT, RC_INC, RC_MONO, RC_REFL, RC_SYM, SC_EXPLICIT, SC_INC,
        SC_MONO, SC_SYM, TC_CASES, TC_CLOSED, TC_INC, TC_INDUCT, TC_MONO, TC_RULES,
        TC_SYM, TC_TRANS, .. } := BClosures
  let { RC_SC, RC_TC, TC_CASES_L, TC_CASES_R, TC_INDUCT_L, TC_INDUCT_R, TC_TRANS_L,
        TC_TRANS_R, .. } := BCommute
  -- @@SCOPE END
  -- Reflexive symmetric closure

  let RSC ← new_definition
   r"RSC(R:A->A->bool) = RC(SC R)"

  let RSC_INC ← prove
   r"!(R:A->A->bool) x y. R x y ==> RSC R x y"
   (REWRITE_TAC [RSC] THEN MESON_TAC [RC_INC, SC_INC])

  let RSC_REFL ← prove
   r"!(R:A->A->bool) x. RSC R x x"
   (REWRITE_TAC [RSC, RC_REFL])

  let RSC_SYM ← prove
   r"!(R:A->A->bool) x y. RSC R x y ==> RSC R y x"
   (REWRITE_TAC [RSC, RC_SC, SC_SYM])

  let RSC_CASES ← prove
   r"!(R:A->A->bool) x y. RSC R x y <=> (x = y) \/ R x y \/ R y x"
   (REWRITE_TAC [RSC, RC_EXPLICIT, SC_EXPLICIT, DISJ_ACI])

  let RSC_INDUCT ← prove
   r"!(R:A->A->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x. P x x) /\
        (!x y. P x y ==> P y x)
        ==>  !x y. RSC R x y ==> P x y"
   (REWRITE_TAC [RSC, RC_EXPLICIT, SC_EXPLICIT] THEN MESON_TAC [])

  let RSC_MONO ← prove
   r"!(R:A->A->bool) S.
        (!x y. R x y ==> S x y) ==>
        (!x y. RSC R x y ==> RSC S x y)"
   (REWRITE_TAC [RSC] THEN MESON_TAC [SC_MONO, RC_MONO])

  let RSC_CLOSED ← prove
   r"!R:A->A->bool. (RSC R = R) <=> (!x. R x x) /\ (!x y. R x y ==> R y x)"
   (REWRITE_TAC [FUN_EQ_THM, RSC, RC_EXPLICIT, SC_EXPLICIT] THEN MESON_TAC [])

  let RSC_IDEMP ← prove
   r"!R:A->A->bool. RSC(RSC R) = RSC R"
   (REWRITE_TAC [RSC_CLOSED, RSC_REFL, RSC_SYM])

  -- Reflexive transitive closure

  let RTC ← new_definition
   r"RTC(R:A->A->bool) = RC(TC R)"

  let RTC_INC ← prove
   r"!(R:A->A->bool) x y. R x y ==> RTC R x y"
   (REWRITE_TAC [RTC] THEN MESON_TAC [RC_INC, TC_INC])

  let RTC_REFL ← prove
   r"!(R:A->A->bool) x. RTC R x x"
   (REWRITE_TAC [RTC, RC_REFL])

  let RTC_TRANS ← prove
   r"!(R:A->A->bool) x y z. RTC R x y /\ RTC R y z ==> RTC R x z"
   (REWRITE_TAC [RTC, RC_TC, TC_TRANS])

  let RTC_RULES ← prove
   r"!(R:A->A->bool).
        (!x y. R x y ==> RTC R x y) /\
        (!x. RTC R x x) /\
        (!x y z. RTC R x y /\ RTC R y z ==> RTC R x z)"
   (REWRITE_TAC [RTC_INC, RTC_REFL, RTC_TRANS])

  let RTC_TRANS_L ← prove
   r"!(R:A->A->bool) x y z. RTC R x y /\ R y z ==> RTC R x z"
   (REWRITE_TAC [RTC, RC_TC] THEN MESON_TAC [TC_TRANS_L, RC_INC])

  let RTC_TRANS_R ← prove
   r"!(R:A->A->bool) x y z. R x y /\ RTC R y z ==> RTC R x z"
   (REWRITE_TAC [RTC, RC_TC] THEN MESON_TAC [TC_TRANS_R, RC_INC])

  let RTC_CASES ← prove
   r"!(R:A->A->bool) x z. RTC R x z <=> (x = z) \/ ?y. RTC R x y /\ RTC R y z"
   (REWRITE_TAC [RTC, RC_EXPLICIT] THEN MESON_TAC [TC_TRANS])

  let RTC_CASES_L ← prove
   r"!(R:A->A->bool) x z. RTC R x z <=> (x = z) \/ ?y. RTC R x y /\ R y z"
   (REWRITE_TAC [RTC, RC_EXPLICIT] THEN MESON_TAC [TC_CASES_L, TC_TRANS_L])

  let RTC_CASES_R ← prove
   r"!(R:A->A->bool) x z. RTC R x z <=> (x = z) \/ ?y. R x y /\ RTC R y z"
   (REWRITE_TAC [RTC, RC_EXPLICIT] THEN MESON_TAC [TC_CASES_R, TC_TRANS_R])

  let RTC_INDUCT ← prove
   r"!(R:A->A->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x. P x x) /\
        (!x y z. P x y /\ P y z ==> P x z)
        ==> !x y. RTC R x y ==> P x y"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [RTC, RC_TC] THEN
    MATCH_MP_TAC TC_INDUCT THEN REWRITE_TAC [RC_EXPLICIT] THEN ASM_MESON_TAC [])

  let RTC_INDUCT_L ← prove
   r"!(R:A->A->bool) P.
        (!x. P x x) /\
        (!x y z. P x y /\ R y z ==> P x z)
        ==> !x y. RTC R x y ==> P x y"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [RTC, RC_TC] THEN
    MATCH_MP_TAC TC_INDUCT_L THEN REWRITE_TAC [RC_EXPLICIT] THEN
    ASM_MESON_TAC [])

  let RTC_INDUCT_R ← prove
   r"!(R:A->A->bool) P.
        (!x. P x x) /\
        (!x y z. R x y /\ P y z ==> P x z)
        ==> !x y. RTC R x y ==> P x y"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [RTC, RC_TC] THEN
    MATCH_MP_TAC TC_INDUCT_R THEN REWRITE_TAC [RC_EXPLICIT] THEN
    ASM_MESON_TAC [])

  let RTC_MONO ← prove
   r"!(R:A->A->bool) S.
        (!x y. R x y ==> S x y) ==>
        (!x y. RTC R x y ==> RTC S x y)"
   (REWRITE_TAC [RTC] THEN MESON_TAC [RC_MONO, TC_MONO])

  let RTC_CLOSED ← prove
   r"!R:A->A->bool. (RTC R = R) <=> (!x. R x x) /\
                                  (!x y z. R x y /\ R y z ==> R x z)"
   (REWRITE_TAC [FUN_EQ_THM, RTC, RC_EXPLICIT] THEN
    MESON_TAC [TC_CLOSED, TC_RULES])

  let RTC_IDEMP ← prove
   r"!R:A->A->bool. RTC(RTC R) = RTC R"
   (REWRITE_TAC [RTC_CLOSED, RTC_REFL, RTC_TRANS])

  let RTC_SYM ← prove
   r"!R:A->A->bool. (!x y. R x y ==> R y x) ==> (!x y. RTC R x y ==> RTC R y x)"
   (REWRITE_TAC [RTC] THEN MESON_TAC [RC_SYM, TC_SYM])

  let RTC_STUTTER ← prove
   r"RTC R = RTC (\x y. R x y /\ ~(x = y))"
   (REWRITE_TAC [RC_TC, RTC] THEN
    AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN
    REWRITE_TAC [RC_CASES] THEN MESON_TAC [])

  let TC_RTC_CASES_L ← prove
   r"TC R x z <=> ?y. RTC R x y /\ R y z"
   (REWRITE_TAC [RTC, RC_CASES] THEN MESON_TAC [TC_CASES_L, TC_INC])

  let TC_RTC_CASES_R ← prove
   r"!R x z. TC R x z <=> ?y. R x y /\ RTC R y z"
   (REWRITE_TAC [RTC, RC_CASES] THEN MESON_TAC [TC_CASES_R, TC_INC])

  let TC_TC_RTC_CASES ← prove
   r"!R x z. TC R x z <=> ?y. TC R x y /\ RTC R y z"
   (REWRITE_TAC [RTC, RC_CASES] THEN MESON_TAC [TC_TRANS])

  let TC_RTC_TC_CASES ← prove
   r"!R x z. TC R x z <=> ?y. RTC R x y /\ TC R y z"
   (REWRITE_TAC [RTC, RC_CASES] THEN MESON_TAC [TC_TRANS])

  let RTC_NE_IMP_TC ← prove
   r"!R x y. RTC R x y /\ ~(x = y) ==> TC R x y"
   (GEN_TAC THEN ONCE_REWRITE_TAC [← GSYM IMP_IMP] THEN
    MATCH_MP_TAC RTC_INDUCT THEN REWRITE_TAC [] THEN
    MESON_TAC [TC_INC, TC_CASES])

  -- @@RETURN BEGIN
  return { RSC, RSC_INC, RSC_REFL, RSC_SYM, RSC_CASES, RSC_INDUCT, RSC_MONO, RSC_CLOSED,
           RSC_IDEMP, RTC, RTC_INC, RTC_REFL, RTC_TRANS, RTC_RULES, RTC_TRANS_L,
           RTC_TRANS_R, RTC_CASES, RTC_CASES_L, RTC_CASES_R, RTC_INDUCT, RTC_INDUCT_L,
           RTC_INDUCT_R, RTC_MONO, RTC_CLOSED, RTC_IDEMP, RTC_SYM, RTC_STUTTER,
           TC_RTC_CASES_L, TC_RTC_CASES_R, TC_TC_RTC_CASES, TC_RTC_TC_CASES,
           RTC_NE_IMP_TC }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Symmetric transitive closure; reflexive symmetric transitive closure      -/
/- (smallest equivalence relation).  (rstc.ml 385-541)                       -/
/- ------------------------------------------------------------------------- -/

structure StcRstc where
  -- @@FIELDS
  STC : thm
  STC_INC : thm
  STC_SYM : thm
  STC_TRANS : thm
  STC_TRANS_L : thm
  STC_TRANS_R : thm
  STC_CASES : thm
  STC_CASES_L : thm
  STC_CASES_R : thm
  STC_INDUCT : thm
  STC_MONO : thm
  STC_CLOSED : thm
  STC_IDEMP : thm
  STC_REFL : thm
  RSTC : thm
  RSTC_INC : thm
  RSTC_REFL : thm
  RSTC_SYM : thm
  RSTC_TRANS : thm
  RSTC_RULES : thm
  RSTC_TRANS_L : thm
  RSTC_TRANS_R : thm
  RSTC_CASES : thm
  RSTC_CASES_L : thm
  RSTC_CASES_R : thm
  RSTC_INDUCT : thm
  RSTC_MONO : thm
  RSTC_CLOSED : thm
  RSTC_IDEMP : thm
  deriving Inhabited

@[nospecialize]
def setupStcRstc [HolBase] (D : RSTCDeps) (BClosures : Closures) (BCommute : Commute) :
    ExceptT String IO StcRstc := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, new_definition, .. } := D
  let { FUN_EQ_THM, .. } := D.core1
  let { RC_CASES, RC_EXPLICIT, RC_INC, RC_MONO, RC_REFL, RC_SYM, SC_CLOSED,
        SC_EXPLICIT, SC_INC, SC_MONO, SC_SYM, TC_CLOSED, TC_INC, TC_INDUCT, TC_MONO,
        TC_SYM, TC_TRANS, .. } := BClosures
  let { RC_SC, RC_TC, TC_TRANS_L, TC_TRANS_R, .. } := BCommute
  -- @@SCOPE END
  -- Symmetric transitive closure

  let STC ← new_definition
   r"STC(R:A->A->bool) = TC(SC R)"

  let STC_INC ← prove
   r"!(R:A->A->bool) x y. R x y ==> STC R x y"
   (REWRITE_TAC [STC] THEN MESON_TAC [SC_INC, TC_INC])

  let STC_SYM ← prove
   r"!(R:A->A->bool) x y. STC R x y ==> STC R y x"
   (REWRITE_TAC [STC] THEN MESON_TAC [TC_SYM, SC_SYM])

  let STC_TRANS ← prove
   r"!(R:A->A->bool) x y z. STC R x y /\ STC R y z ==> STC R x z"
   (REWRITE_TAC [STC, TC_TRANS])

  let STC_TRANS_L ← prove
   r"!(R:A->A->bool) x y z. STC R x y /\ R y z ==> STC R x z"
   (REWRITE_TAC [STC] THEN MESON_TAC [TC_TRANS_L, SC_INC])

  let STC_TRANS_R ← prove
   r"!(R:A->A->bool) x y z. R x y /\ STC R y z ==> STC R x z"
   (REWRITE_TAC [STC] THEN MESON_TAC [TC_TRANS_R, SC_INC])

  let STC_CASES ← prove
   r"!(R:A->A->bool) x z. STC R x z <=> R x z \/ STC R z x \/
                                      ?y. STC R x y /\ STC R y z"
   (REWRITE_TAC [STC] THEN MESON_TAC [SC_SYM, TC_SYM, TC_INC, TC_TRANS, SC_INC])

  let STC_CASES_L ← prove
   r"!(R:A->A->bool) x z. STC R x z <=> R x z \/ STC R z x \/
                                      ?y. STC R x y /\ R y z"
   (REWRITE_TAC [STC] THEN MESON_TAC [SC_SYM, TC_SYM, TC_INC, TC_TRANS, SC_INC])

  let STC_CASES_R ← prove
   r"!(R:A->A->bool) x z. STC R x z <=> R x z \/ STC R z x \/
                                      ?y. R x y /\ STC R y z"
   (REWRITE_TAC [STC] THEN MESON_TAC [SC_SYM, TC_SYM, TC_INC, TC_TRANS, SC_INC])

  let STC_INDUCT ← prove
   r"!(R:A->A->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x y. P x y ==> P y x) /\
        (!x y z. P x y /\ P y z ==> P x z) ==>
                !x y. STC R x y ==> P x y"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [STC] THEN
    MATCH_MP_TAC TC_INDUCT THEN ASM_MESON_TAC [SC_EXPLICIT])

  let STC_MONO ← prove
   r"!(R:A->A->bool) S.
        (!x y. R x y ==> S x y) ==>
        (!x y. STC R x y ==> STC S x y)"
   (REWRITE_TAC [STC] THEN MESON_TAC [SC_MONO, TC_MONO])

  let STC_CLOSED ← prove
   r"!R:A->A->bool. (STC R = R) <=> (!x y. R x y ==> R y x) /\
                                  (!x y z. R x y /\ R y z ==> R x z)"
   (GEN_TAC THEN REWRITE_TAC [STC, SC_EXPLICIT] THEN EQ_TAC THENL
     [DISCH_THEN (SUBST1_TAC o SYM) THEN MESON_TAC [TC_TRANS, TC_SYM, SC_SYM],
      REWRITE_TAC [← GSYM SC_CLOSED, ← GSYM TC_CLOSED] THEN MESON_TAC []])

  let STC_IDEMP ← prove
   r"!R:A->A->bool. STC(STC R) = STC R"
   (REWRITE_TAC [STC_CLOSED, STC_SYM, STC_TRANS])

  let STC_REFL ← prove
   r"!R:A->A->bool. (!x. R x x) ==> !x. STC R x x"
   (MESON_TAC [STC_INC])

  -- Reflexive symmetric transitive closure (smallest equivalence relation)

  let RSTC ← new_definition
   r"RSTC(R:A->A->bool) = RC(TC(SC R))"

  let RSTC_INC ← prove
   r"!(R:A->A->bool) x y. R x y ==> RSTC R x y"
   (REWRITE_TAC [RSTC] THEN MESON_TAC [RC_INC, TC_INC, SC_INC])

  let RSTC_REFL ← prove
   r"!(R:A->A->bool) x. RSTC R x x"
   (REWRITE_TAC [RSTC, RC_REFL])

  let RSTC_SYM ← prove
   r"!(R:A->A->bool) x y. RSTC R x y ==> RSTC R y x"
   (REWRITE_TAC [RSTC] THEN MESON_TAC [SC_SYM, TC_SYM, RC_SYM])

  let RSTC_TRANS ← prove
   r"!(R:A->A->bool) x y z. RSTC R x y /\ RSTC R y z ==> RSTC R x z"
   (REWRITE_TAC [RSTC, RC_TC, TC_TRANS])

  let RSTC_RULES ← prove
   r"!(R:A->A->bool).
        (!x y. R x y ==> RSTC R x y) /\
        (!x. RSTC R x x) /\
        (!x y. RSTC R x y ==> RSTC R y x) /\
        (!x y z. RSTC R x y /\ RSTC R y z ==> RSTC R x z)"
   (REWRITE_TAC [RSTC_INC, RSTC_REFL, RSTC_SYM, RSTC_TRANS])

  let RSTC_TRANS_L ← prove
   r"!(R:A->A->bool) x y z. RSTC R x y /\ R y z ==> RSTC R x z"
   (REWRITE_TAC [RSTC, RC_TC] THEN MESON_TAC [TC_TRANS_L, RC_INC, SC_INC])

  let RSTC_TRANS_R ← prove
   r"!(R:A->A->bool) x y z. R x y /\ RSTC R y z ==> RSTC R x z"
   (REWRITE_TAC [RSTC, RC_TC] THEN MESON_TAC [TC_TRANS_R, RC_INC, SC_INC])

  let RSTC_CASES ← prove
   r"!(R:A->A->bool) x z. RSTC R x z <=> (x = z) \/ R x z \/ RSTC R z x \/
                                       ?y. RSTC R x y /\ RSTC R y z"
   (REWRITE_TAC [RSTC, RC_TC, RC_SC] THEN REWRITE_TAC [← GSYM STC] THEN
    MESON_TAC [STC_CASES, RC_CASES])

  let RSTC_CASES_L ← prove
   r"!(R:A->A->bool) x z. RSTC R x z <=> (x = z) \/ R x z \/ RSTC R z x \/
                                     ?y. RSTC R x y /\ R y z"
   (REWRITE_TAC [RSTC, RC_TC, RC_SC] THEN REWRITE_TAC [← GSYM STC] THEN
    MESON_TAC [STC_CASES_L, RC_CASES])

  let RSTC_CASES_R ← prove
   r"!(R:A->A->bool) x z. RSTC R x z <=> (x = z) \/ R x z \/ RSTC R z x \/
                                       ?y. R x y /\ RSTC R y z"
   (REWRITE_TAC [RSTC, RC_TC, RC_SC] THEN REWRITE_TAC [← GSYM STC] THEN
    MESON_TAC [STC_CASES_R, RC_CASES])

  let RSTC_INDUCT ← prove
   r"!(R:A->A->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x. P x x) /\
        (!x y. P x y ==> P y x) /\
        (!x y z. P x y /\ P y z ==> P x z)
        ==> !x y. RSTC R x y ==> P x y"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC [RSTC, RC_TC, RC_SC] THEN REWRITE_TAC [← GSYM STC] THEN
    MATCH_MP_TAC STC_INDUCT THEN REWRITE_TAC [RC_EXPLICIT] THEN ASM_MESON_TAC [])

  let RSTC_MONO ← prove
   r"!(R:A->A->bool) S.
        (!x y. R x y ==> S x y) ==>
        (!x y. RSTC R x y ==> RSTC S x y)"
   (REWRITE_TAC [RSTC] THEN MESON_TAC [RC_MONO, SC_MONO, TC_MONO])

  let RSTC_CLOSED ← prove
   r"!R:A->A->bool. (RSTC R = R) <=> (!x. R x x) /\
                                   (!x y. R x y ==> R y x) /\
                                   (!x y z. R x y /\ R y z ==> R x z)"
   (REWRITE_TAC [RSTC] THEN REWRITE_TAC [← GSYM STC, ← GSYM STC_CLOSED] THEN
    REWRITE_TAC [RC_EXPLICIT, FUN_EQ_THM] THEN MESON_TAC [STC_INC])

  let RSTC_IDEMP ← prove
   r"!R:A->A->bool. RSTC(RSTC R) = RSTC R"
   (REWRITE_TAC [RSTC_CLOSED, RSTC_REFL, RSTC_SYM, RSTC_TRANS])

  -- @@RETURN BEGIN
  return { STC, STC_INC, STC_SYM, STC_TRANS, STC_TRANS_L, STC_TRANS_R, STC_CASES,
           STC_CASES_L, STC_CASES_R, STC_INDUCT, STC_MONO, STC_CLOSED, STC_IDEMP,
           STC_REFL, RSTC, RSTC_INC, RSTC_REFL, RSTC_SYM, RSTC_TRANS, RSTC_RULES,
           RSTC_TRANS_L, RSTC_TRANS_R, RSTC_CASES, RSTC_CASES_L, RSTC_CASES_R,
           RSTC_INDUCT, RSTC_MONO, RSTC_CLOSED, RSTC_IDEMP }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Inclusion properties for composite closures; reverse relations; an        -/
/- iterative version of (R)TC.  (rstc.ml 543-709)                            -/
/- ------------------------------------------------------------------------- -/

structure Relpow where
  -- @@FIELDS
  RSC_INC_RC : thm
  RSC_INC_SC : thm
  RTC_INC_RC : thm
  RTC_INC_TC : thm
  STC_INC_SC : thm
  STC_INC_TC : thm
  RSTC_INC_RC : thm
  RSTC_INC_SC : thm
  RSTC_INC_TC : thm
  RSTC_INC_RSC : thm
  RSTC_INC_RTC : thm
  RSTC_INC_STC : thm
  INV : thm
  RC_INV : thm
  SC_INV : thm
  SC_INV_STRONG : thm
  TC_INV : thm
  RSC_INV : thm
  RTC_INV : thm
  STC_INV : thm
  RSTC_INV : thm
  RELPOW : thm
  RELPOW_R : thm
  RELPOW_M : thm
  RTC_RELPOW : thm
  TC_RELPOW : thm
  RELPOW_SEQUENCE : thm
  deriving Inhabited

@[nospecialize]
def setupRelpow [HolBase] (D : RSTCDeps) (BClosures : Closures) (BCommute : Commute) (BRscRtc : RscRtc) (BStcRstc : StcRstc) :
    ExceptT String IO Relpow := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, new_definition,
        new_recursive_definition, .. } := D
  let { ADD_CLAUSES, ARITH, DISJ_SYM, EQ_SYM_EQ, FUN_EQ_THM, LEFT_EXISTS_AND_THM,
        LEFT_IMP_EXISTS_THM, LE_0, LE_LT, LE_REFL, LE_SUC_LT, LT, NOT_SUC,
        SWAP_EXISTS_THM, SWAP_FORALL_THM, UNWIND_THM1, num_RECURSION, .. } := D.core1
  let { RC_EXPLICIT, RC_INC, RULE_INDUCT_TAC, SC_EXPLICIT, SC_INC, TC_INC, TC_INDUCT,
        TC_MONO, TC_RULES, .. } := BClosures
  let { RC_SC, RC_TC, TC_CASES_L, .. } := BCommute
  let { RSC, RSC_INC, RTC, RTC_INC, RTC_INDUCT_L, RTC_MONO, RTC_REFL, RTC_TRANS_L, .. } := BRscRtc
  let { RSTC, STC, STC_INC, .. } := BStcRstc
  -- @@SCOPE END
  -- Finally, we prove the inclusion properties for composite closures

  let RSC_INC_RC ← prove
   r"!R:A->A->bool. !x y. RC R x y ==> RSC R x y"
   (REWRITE_TAC [RSC, RC_SC, SC_INC])

  let RSC_INC_SC ← prove
   r"!R:A->A->bool. !x y. SC R x y ==> RSC R x y"
   (REWRITE_TAC [RSC, RC_INC])

  let RTC_INC_RC ← prove
   r"!R:A->A->bool. !x y. RC R x y ==> RTC R x y"
   (REWRITE_TAC [RTC, RC_TC, TC_INC])

  let RTC_INC_TC ← prove
   r"!R:A->A->bool. !x y. TC R x y ==> RTC R x y"
   (REWRITE_TAC [RTC, RC_INC])

  let STC_INC_SC ← prove
   r"!R:A->A->bool. !x y. SC R x y ==> STC R x y"
   (REWRITE_TAC [STC, TC_INC])

  let STC_INC_TC ← prove
   r"!R:A->A->bool. !x y. TC R x y ==> STC R x y"
   (REWRITE_TAC [STC] THEN MESON_TAC [TC_MONO, SC_INC])

  let RSTC_INC_RC ← prove
   r"!R:A->A->bool. !x y. RC R x y ==> RSTC R x y"
   (REWRITE_TAC [RSTC, RC_TC, RC_SC, ← GSYM STC, STC_INC])

  let RSTC_INC_SC ← prove
   r"!R:A->A->bool. !x y. SC R x y ==> RSTC R x y"
   (REWRITE_TAC [RSTC, ← GSYM RTC, RTC_INC])

  let RSTC_INC_TC ← prove
   r"!R:A->A->bool. !x y. TC R x y ==> RSTC R x y"
   (REWRITE_TAC [RSTC, RC_TC, ← GSYM RSC] THEN MESON_TAC [TC_MONO, RSC_INC])

  let RSTC_INC_RSC ← prove
   r"!R:A->A->bool. !x y. RSC R x y ==> RSTC R x y"
   (REWRITE_TAC [RSC, RSTC, RC_TC, TC_INC])

  let RSTC_INC_RTC ← prove
   r"!R:A->A->bool. !x y. RTC R x y ==> RSTC R x y"
   (REWRITE_TAC [← GSYM RTC, RSTC] THEN MESON_TAC [RTC_MONO, SC_INC])

  let RSTC_INC_STC ← prove
   r"!R:A->A->bool. !x y. STC R x y ==> RSTC R x y"
   (REWRITE_TAC [← GSYM STC, RSTC, RC_INC])

  -- Handy things about reverse relations.

  let INV ← new_definition
   r"INV R (x:A) (y:B) <=> R y x"

  let RC_INV ← prove
   r"RC(INV R) = INV(RC R)"
   (REWRITE_TAC [FUN_EQ_THM, RC_EXPLICIT, INV, EQ_SYM_EQ])

  let SC_INV ← prove
   r"SC(INV R) = INV(SC R)"
   (REWRITE_TAC [FUN_EQ_THM, SC_EXPLICIT, INV, DISJ_SYM])

  let SC_INV_STRONG ← prove
   r"SC(INV R) = SC R"
   (REWRITE_TAC [FUN_EQ_THM, SC_EXPLICIT, INV, DISJ_SYM])

  let TC_INV ← prove
   r"TC(INV R) = INV(TC R)"
   (REWRITE_TAC [FUN_EQ_THM, INV] THEN REPEAT GEN_TAC THEN EQ_TAC THEN
    RULE_INDUCT_TAC TC_INDUCT THEN MESON_TAC [INV, TC_RULES])

  let RSC_INV ← prove
   r"RSC(INV R) = INV(RSC R)"
   (REWRITE_TAC [RSC, RC_INV, SC_INV])

  let RTC_INV ← prove
   r"RTC(INV R) = INV(RTC R)"
   (REWRITE_TAC [RTC, RC_INV, TC_INV])

  let STC_INV ← prove
   r"STC(INV R) = INV(STC R)"
   (REWRITE_TAC [STC, SC_INV, TC_INV])

  let RSTC_INV ← prove
   r"RSTC(INV R) = INV(RSTC R)"
   (REWRITE_TAC [RSTC, RC_INV, SC_INV, TC_INV])

  -- An iterative version of (R)TC.

  let RELPOW ← new_recursive_definition num_RECURSION
   r"(RELPOW 0 (R:A->A->bool) x y <=> (x = y)) /\
   (RELPOW (SUC n) R x y <=> ?z. RELPOW n R x z /\ R z y)"

  let RELPOW_R ← prove
   r"(RELPOW 0 (R:A->A->bool) x y <=> (x = y)) /\
   (RELPOW (SUC n) R x y <=> ?z. R x z /\ RELPOW n R z y)"
   (CONJ_TAC THENL [REWRITE_TAC [RELPOW], ALL_TAC] THEN
    MAP_EVERY (fun t => SPEC_TAC (t, t)) [← q "x:A", ← q "y:A", ← q "n:num"] THEN
    INDUCT_TAC THEN ASM_MESON_TAC [RELPOW])

  let RELPOW_M ← prove
   r"!m n x:A y. RELPOW (m + n) R x y <=> ?z. RELPOW m R x z /\ RELPOW n R z y"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [ADD_CLAUSES, RELPOW_R, UNWIND_THM1] THEN
    MESON_TAC [])

  let RTC_RELPOW ← prove
   r"!R (x:A) y. RTC R x y <=> ?n. RELPOW n R x y"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [RULE_INDUCT_TAC RTC_INDUCT_L THEN MESON_TAC [RELPOW],
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN SPEC_TAC (← q "y:A", ← q "y:A") THEN
      ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN INDUCT_TAC THEN
      REWRITE_TAC [RELPOW] THEN ASM_MESON_TAC [RTC_REFL, RTC_TRANS_L]])

  let TC_RELPOW ← prove
   r"!R (x:A) y. TC R x y <=> ?n. RELPOW (SUC n) R x y"
   (REWRITE_TAC [RELPOW] THEN ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
    REWRITE_TAC [LEFT_EXISTS_AND_THM, ← GSYM RTC_RELPOW] THEN
    ONCE_REWRITE_TAC [TC_CASES_L] THEN REWRITE_TAC [RTC, RC_EXPLICIT] THEN
    MESON_TAC [])

  let RELPOW_SEQUENCE ← prove
   r"!R n x y. RELPOW n R x y <=> ?f. (f(0) = x:A) /\ (f(n) = y) /\
                                    !i. i < n ==> R (f i) (f(SUC i))"
   (← do
    -- The ARITH_RULEs in OCaml's order: the THENL list is built right to
    -- left and the later rule in a THEN chain first.
    let ar3 ← ARITH_RULE (← q r"~(SUC n <= n)")
    let ar2 ← ARITH_RULE (← q r"~(SUC n <= n)")
    let ar1 ← ARITH_RULE (← q r"(n = 0) \/ 0 < n")
    pure (GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [LT, RELPOW] THENL
     [REPEAT GEN_TAC THEN EQ_TAC THENL
       [DISCH_THEN SUBST1_TAC THEN EXISTS_TAC (← q r"\n:num. y:A") THEN REWRITE_TAC [],
        MESON_TAC []],
      REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
       [DISJ_CASES_TAC ar1 THENL
         [EXISTS_TAC (← q r"\i. if i = 0 then x else y:A") THEN
          ASM_REWRITE_TAC [ARITH, LT] THEN
          REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [NOT_SUC] THEN
          ASM_MESON_TAC [],
          EXISTS_TAC (← q r"\i. if i <= n then f(i) else (y:A)") THEN
          ASM_REWRITE_TAC [LE_0, ar2] THEN
          REPEAT STRIP_TAC THEN
          ASM_REWRITE_TAC [LE_REFL, ar3] THEN
          ASM_REWRITE_TAC [LE_SUC_LT] THEN
          ASM_REWRITE_TAC [LE_LT] THEN
          FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []],
        EXISTS_TAC (← q r"(f:num->A) n") THEN CONJ_TAC THENL
         [EXISTS_TAC (← q r"f:num->A") THEN ASM_REWRITE_TAC [] THEN
          REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
          ASM_REWRITE_TAC [],
          ASM_MESON_TAC []]]]))

  -- @@RETURN BEGIN
  return { RSC_INC_RC, RSC_INC_SC, RTC_INC_RC, RTC_INC_TC, STC_INC_SC, STC_INC_TC,
           RSTC_INC_RC, RSTC_INC_SC, RSTC_INC_TC, RSTC_INC_RSC, RSTC_INC_RTC,
           RSTC_INC_STC, INV, RC_INV, SC_INV, SC_INV_STRONG, TC_INV, RSC_INV, RTC_INV,
           STC_INV, RSTC_INV, RELPOW, RELPOW_R, RELPOW_M, RTC_RELPOW, TC_RELPOW,
           RELPOW_SEQUENCE }
  -- @@RETURN END

end HolLibrary.RSTC
