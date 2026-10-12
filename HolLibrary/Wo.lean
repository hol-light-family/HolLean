/- ========================================================================= -/
/- Some general material about ordered sets of various kinds including WQOs. -/
/- Proof of some useful AC equivalents like wellordering and Zorn's Lemma.   -/
/- ========================================================================= -/
/- File: HolLibrary/Wo.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/wo.ml`, by hand, in file order, in
  the style of HolLibrary/RSTC.lean (see there and HolMath/Base.lean for the
  conventions).  Each section of wo.ml is a bundle (a `structure`) built by a
  `setup` function; SessionLibrary/Wo.lean builds the bundles in order and
  exports every name under its HOL Light name.

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, TAUT, SET_RULE) they are bound first, in
  OCaml's order.
-/

import HolMath

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolLibrary.Wo

/- ------------------------------------------------------------------------- -/
/- What wo.ml uses from the core library (supplied by Session).              -/
/- ------------------------------------------------------------------------- -/

/-- Theorems wo.ml uses from the core library. -/
structure CoreThms1 where
  (AND_FORALL_THM COND_ID CONJ_ASSOC CONTRAPOS_THM DEPENDENT_CHOICE DISJ_SYM
   EQ_IMP ETA_AX EXISTS_FINITE_SUBSET_IMAGE EXISTS_IN_IMAGE EXISTS_IN_INSERT
   EXISTS_PAIR_THM EXTENSION FINITE_CROSS FINITE_EMPTY FINITE_IMAGE
   FINITE_INDUCT_STRONG FINITE_NUMSEG_LT FINITE_SING FINITE_SUBSET
   FINITE_UNION FORALL_AND_THM FORALL_IN_IMAGE FORALL_IN_INSERT
   FORALL_PAIR_THM FORALL_UNWIND_THM2 FUN_EQ_THM IMP_CONJ IMP_CONJ_ALT
   IMP_IMP IN INFINITE INFINITE_ENUMERATE_EQ INFINITE_ENUMERATE_SUBSET
   INFINITE_IMAGE INJECTIVE_ALT INJECTIVE_LEFT_INVERSE INSERT_SUBSET IN_CROSS
   IN_DIFF IN_ELIM_PAIR_THM IN_ELIM_THM IN_IMAGE IN_UNION IN_UNIONS IN_UNIV
   LEFT_AND_EXISTS_THM LEFT_IMP_EXISTS_THM LE_CASES LE_LT LT_ADD_RCANCEL
   LT_CASES LT_IMP_LE LT_IMP_NE LT_LE LT_SUC_LE LT_TRANS MEMBER_NOT_EMPTY
   MONO_AND MONO_EXISTS MONO_FORALL MONO_IMP NOT_EXISTS_THM NOT_FORALL_THM
   NOT_IMP NOT_INSERT_EMPTY NOT_IN_EMPTY OR_EXISTS_THM PAIRWISE_IMAGE PAIR_EQ
   RIGHT_FORALL_IMP_THM RIGHT_IMP_EXISTS_THM SKOLEM_THM SUBSET SUBSET_ANTISYM
   SUBSET_EMPTY SUBSET_REFL SUBSET_TRANS SUBSET_UNIV SWAP_EXISTS_THM
   SWAP_FORALL_THM TRANSITIVE_STEPWISE_LE TRANSITIVE_STEPWISE_LT UNIONS
   UNIONS_GSPEC UNIV UNWIND_THM2 WF WF_ANTISYM WF_DCHAIN WF_FINITE WF_IND
   WF_REC WF_REC_EXISTS WF_SUBSET WF_num WLOG_LT num_FINITE num_INFINITE
   o_THM pairwise : thm)
  deriving Inhabited

/-- What wo.ml uses from Session besides theorems. -/
structure WoDeps where
  -- definitions and parser state
  new_definition : String → ExceptT String IO thm
  parse_as_infix : String × (Int × String) → IO Unit
  -- decision procedures and tactics
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_ARITH_TAC : tactic
  ASM_MESON_TAC : List thm → tactic
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  METIS_TAC : List thm → tactic
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  -- conversions
  GEN_BETA_CONV : ioconv
  SELECT_CONV : ioconv
  core1 : CoreThms1

/- ------------------------------------------------------------------------- -/
/- Definitions and general lemmas: field, the kinds of order, chains and     -/
/- antichains, the trivial implications.  (wo.ml 1-183)                      -/
/- ------------------------------------------------------------------------- -/

structure Defs where
  -- @@FIELDS
  PBETA_TAC : tactic
  SUBSET_PRED : thm
  UNIONS_PRED : thm
  fld : thm
  IN_FLD : thm
  FLD_EQ_EMPTY : thm
  FLD_SUBSET : thm
  FINITE_FLD : thm
  qoset : thm
  poset : thm
  toset : thm
  woset : thm
  wqoset : thm
  chain : thm
  antichain : thm
  CHAIN : thm
  ANTICHAIN : thm
  CHAIN_SUBSET : thm
  ANTICHAIN_SUBSET : thm
  QOSET_REFL : thm
  QOSET_TRANS : thm
  QOSET_REFL_EQ : thm
  QOSET_FLDEQ : thm
  QOSET_FLD : thm
  WOSET_IMP_TOSET : thm
  WOSET_IMP_POSET : thm
  WOSET_IMP_QOSET : thm
  TOSET_IMP_POSET : thm
  TOSET_IMP_QOSET : thm
  POSET_IMP_QOSET : thm
  WQOSET_IMP_QOSET : thm
  deriving Inhabited

@[nospecialize]
def setupDefs [HolBase] (D : WoDeps) :
    ExceptT String IO Defs := do
  -- @@SCOPE BEGIN
  let { GEN_BETA_CONV, MESON_TAC, SET_TAC, new_definition, .. } := D
  let { EXISTS_PAIR_THM, EXTENSION, FINITE_CROSS, FINITE_IMAGE, FINITE_SUBSET,
        FINITE_UNION, FORALL_PAIR_THM, FUN_EQ_THM, IMP_CONJ_ALT, IMP_IMP, IN, IN_CROSS,
        IN_ELIM_PAIR_THM, IN_ELIM_THM, IN_IMAGE, IN_UNION, PAIR_EQ, SUBSET, UNIONS,
        pairwise, .. } := D.core1
  -- @@SCOPE END

  let PBETA_TAC : tactic ← pure (CONV_TAC (ONCE_DEPTH_CONV GEN_BETA_CONV))

  let SUBSET_PRED ← prove
   r"!P Q. P SUBSET Q <=> !x. P x ==> Q x"
   (REWRITE_TAC [SUBSET, IN])

  let UNIONS_PRED ← prove
   r"UNIONS P = \x. ?p. P p /\ p x"
   (REWRITE_TAC [UNIONS, FUN_EQ_THM, IN_ELIM_THM, IN])

  -- Field of an uncurried binary relation

  let fld ← new_definition
   r"fld R = {x:A | ?y. R x y \/ R y x}"

  let IN_FLD ← prove
   r"!l x:A. x IN fld l <=> ?y. l x y \/ l y x"
   (REWRITE_TAC [fld, IN_ELIM_THM])

  let FLD_EQ_EMPTY ← prove
   r"!R:A->A->bool. fld R = {} <=> R = (\x y. F)"
   (GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
    REWRITE_TAC [FUN_EQ_THM] THEN REWRITE_TAC [fld] THEN SET_TAC [])

  let FLD_SUBSET ← prove
   r"!l r. (!x y. l x y ==> r x y) ==> fld l SUBSET fld r"
   (REWRITE_TAC [fld] THEN SET_TAC [])

  let FINITE_FLD ← prove
   r"!l:A->A->bool. FINITE(fld l) <=> FINITE {(x,y) | l x y}"
   (← do
    let tFST ← q r"FST:A#A->A"
    let tSND ← q r"SND:A#A->A"
    pure (GEN_TAC THEN EQ_TAC THENL
       [DISCH_THEN (fun th => tactic_of do
          pure (MP_TAC (← MATCH_MP FINITE_CROSS (← CONJ th th)))),
        DISCH_THEN ((fun th => tactic_of do
          let b2 ← ISPEC tSND th
          let b1 ← ISPEC tFST th
          pure (MP_TAC b1 THEN MP_TAC b2)) o
          MATCH_MP FINITE_IMAGE) THEN
        REWRITE_TAC [IMP_IMP, ← GSYM FINITE_UNION]] THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] FINITE_SUBSET) THEN
      REWRITE_TAC [SUBSET, FORALL_PAIR_THM, IN_ELIM_PAIR_THM] THEN
      REWRITE_TAC [IN_CROSS, fld, IN_IMAGE, IN_ELIM_THM, IN_UNION] THEN
      REWRITE_TAC [EXISTS_PAIR_THM, PAIR_EQ] THEN SET_TAC []))

  -- Various kinds of order

  let qoset ← new_definition
   r"qoset (l:A->A->bool) <=>
       (!x. x IN fld l ==> l x x) /\
       (!x y z. l x y /\ l y z ==> l x z)"

  let poset ← new_definition
   r"poset (l:A->A->bool) <=>
       (!x. x IN fld l ==> l x x) /\
       (!x y z. l x y /\ l y z ==> l x z) /\
       (!x y. l x y /\ l y x ==> x = y)"

  let toset ← new_definition
   r"toset (l:A->A->bool) <=>
       (!x. x IN fld l ==> l x x) /\
       (!x y z. l x y /\ l y z ==> l x z) /\
       (!x y. l x y /\ l y x ==> x = y) /\
       (!x y. x IN fld l /\ y IN fld l ==> l x y \/ l y x)"

  let woset ← new_definition
   r"woset (l:A->A->bool) <=>
       (!x. x IN fld l ==> l x x) /\
       (!x y z. l x y /\ l y z ==> l x z) /\
       (!x y. l x y /\ l y x ==> x = y) /\
       (!x y. x IN fld l /\ y IN fld l ==> l x y \/ l y x) /\
       (!s. s SUBSET fld l /\ ~(s = {})
            ==> ?x. x IN s /\ !y. y IN s ==> l x y)"

  let wqoset ← new_definition
   r"wqoset (l:A->A->bool) <=>
        (!x. x IN fld l ==> l x x) /\
        (!x y z. l x y /\ l y z ==> l x z) /\
        (!s. s SUBSET fld l
             ==> ?t. FINITE t /\ t SUBSET s /\
                     !y. y IN s ==> ?x. x IN t /\ l x y)"

  -- Chains and antichains (subsets of the carrier, not the ordering)

  let chain ← new_definition
   r"chain (l:A->A->bool) s <=>
        !x y. x IN s /\ y IN s ==> l x y \/ l y x"

  let antichain ← new_definition
   r"antichain (l:A->A->bool) s <=>
        s SUBSET fld l /\ pairwise (\x y. ~(l x y)) s"

  let CHAIN ← prove
   r"!l s:A->bool.
        chain l s <=>
        s SUBSET fld l /\
        !x y. x IN s /\ y IN s ==> l x y \/ l y x"
   (REWRITE_TAC [chain, fld] THEN SET_TAC [])

  let ANTICHAIN ← prove
   r"!l s:A->bool.
        antichain l s <=>
        s SUBSET fld l /\
        !x y. x IN s /\ y IN s /\ ~(x = y) ==> ~(l x y)"
   (REWRITE_TAC [antichain, pairwise, fld] THEN SET_TAC [])

  let CHAIN_SUBSET ← prove
   r"!(l:A->A->bool) s t. chain l s /\ t SUBSET s ==> chain l t"
   (REWRITE_TAC [chain] THEN SET_TAC [])

  let ANTICHAIN_SUBSET ← prove
   r"!(l:A->A->bool) s t. antichain l s /\ t SUBSET s ==> antichain l t"
   (REWRITE_TAC [ANTICHAIN] THEN SET_TAC [])

  -- The trivial implications.

  let QOSET_REFL ← prove
   r"!l:A->A->bool. qoset l ==> !x. fld(l) x ==> l x x"
   (REWRITE_TAC [qoset, IN] THEN MESON_TAC [])

  let QOSET_TRANS ← prove
   r"!l:A->A->bool. qoset l ==> !x y z. l x y /\ l y z ==> l x z"
   (REWRITE_TAC [qoset] THEN MESON_TAC [])

  let QOSET_REFL_EQ ← prove
   r"!l (x:A). qoset l ==> (l x x <=> x IN fld l)"
   (REWRITE_TAC [qoset, fld, IN_ELIM_THM] THEN MESON_TAC [])

  let QOSET_FLDEQ ← prove
   r"!l:A->A->bool. qoset l ==> (!x. fld(l) x <=> l x x)"
   (MESON_TAC [QOSET_REFL_EQ, IN])

  let QOSET_FLD ← prove
   r"!l:A->A->bool. qoset l ==> fld l = {x | l x x}"
   (SIMP_TAC [QOSET_REFL_EQ] THEN SET_TAC [])

  let WOSET_IMP_TOSET ← prove
   r"!l:A->A->bool. woset l ==> toset l"
   (GEN_TAC THEN REWRITE_TAC [woset, toset] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [])

  let WOSET_IMP_POSET ← prove
   r"!l:A->A->bool. woset l ==> poset l"
   (GEN_TAC THEN REWRITE_TAC [woset, poset] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [])

  let WOSET_IMP_QOSET ← prove
   r"!l:A->A->bool. woset l ==> qoset l"
   (GEN_TAC THEN REWRITE_TAC [woset, qoset] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [])

  let TOSET_IMP_POSET ← prove
   r"!l:A->A->bool. toset l ==> poset l"
   (GEN_TAC THEN REWRITE_TAC [toset, poset] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [])

  let TOSET_IMP_QOSET ← prove
   r"!l:A->A->bool. toset l ==> qoset l"
   (GEN_TAC THEN REWRITE_TAC [toset, qoset] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [])

  let POSET_IMP_QOSET ← prove
   r"!l:A->A->bool. poset l ==> qoset l"
   (GEN_TAC THEN REWRITE_TAC [poset, qoset] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [])

  let WQOSET_IMP_QOSET ← prove
   r"!l:A->A->bool. wqoset l ==> qoset l"
   (GEN_TAC THEN REWRITE_TAC [wqoset, qoset] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [])

  -- @@RETURN BEGIN
  return { PBETA_TAC, SUBSET_PRED, UNIONS_PRED, fld, IN_FLD, FLD_EQ_EMPTY, FLD_SUBSET,
           FINITE_FLD, qoset, poset, toset, woset, wqoset, chain, antichain, CHAIN,
           ANTICHAIN, CHAIN_SUBSET, ANTICHAIN_SUBSET, QOSET_REFL, QOSET_TRANS,
           QOSET_REFL_EQ, QOSET_FLDEQ, QOSET_FLD, WOSET_IMP_TOSET, WOSET_IMP_POSET,
           WOSET_IMP_QOSET, TOSET_IMP_POSET, TOSET_IMP_QOSET, POSET_IMP_QOSET,
           WQOSET_IMP_QOSET }
  -- @@RETURN END

/-- `let [a; b; c] = l` (OCaml raises Match_failure on any other length). -/
def list3 (l : List thm) : ExceptT String IO (thm × thm × thm) :=
  match l with
  | [a, b, c] => pure (a, b, c)
  | _ => throw "Match_failure"

/- ------------------------------------------------------------------------- -/
/- Strict and proper orders; interrelations and alternative forms of the     -/
/- definitions; restrictions; finite sets have maximal/minimal/greatest/     -/
/- least elements.  (wo.ml 185-614)                                          -/
/- ------------------------------------------------------------------------- -/

structure Orders where
  -- @@FIELDS
  strictly : thm
  properly : thm
  PROPERLY_EQ_STRICTLY : thm
  STRICTLY_EQ_PROPERLY : thm
  STRICTLY_IMP_PROPERLY : thm
  STRICTLY_STRICTLY : thm
  PROPERLY_PROPERLY : thm
  STRICTLY_PROPERLY : thm
  PROPERLY_STRICTLY : thm
  PROPERLY_MONO : thm
  POSET_QOSET : thm
  TOSET : thm
  TOSET_POSET : thm
  WOSET_TOSET : thm
  WQOSET : thm
  WQOSET_QOSET : thm
  WOSET_POSET : thm
  WOSET : thm
  WOSET_WF : thm
  WOSET_IMP_WQOSET : thm
  WQOSET_SUPERSET : thm
  WQOSET_NOBAD : thm
  WQOSET_NOBAD_SUBSEQ : thm
  WQOSET_ANTICHAIN : thm
  WQOSET_IMP_WF : thm
  WQOSET_WF_SUPERSET : thm
  WQOSET_WF_SUPERSET_EQ : thm
  WOSET_WQOSET : thm
  FLD_RESTRICT_QOSET : thm
  FLD_RESTRICT_POSET : thm
  FLD_RESTRICT_TOSET : thm
  FLD_RESTRICT_WOSET : thm
  FLD_RESTRICT_WQOSET : thm
  QOSET_RESTRICT : thm
  POSET_RESTRICT : thm
  TOSET_RESTRICT : thm
  WOSET_RESTRICT : thm
  WQOSET_RESTRICT : thm
  QOSET_MIN : thm
  QOSET_MAX : thm
  POSET_MIN : thm
  POSET_MAX : thm
  TOSET_MIN : thm
  TOSET_MAX : thm
  deriving Inhabited

@[nospecialize]
def setupOrders [HolBase] (D : WoDeps) (BDefs : Defs) :
    ExceptT String IO Orders := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON, MESON_TAC,
        METIS_TAC, SET_TAC, new_definition, .. } := D
  let { AND_FORALL_THM, CONJ_ASSOC, CONTRAPOS_THM, DEPENDENT_CHOICE,
        EXISTS_FINITE_SUBSET_IMAGE, EXISTS_IN_IMAGE, EXISTS_IN_INSERT, FINITE_EMPTY,
        FINITE_IMAGE, FINITE_INDUCT_STRONG, FINITE_NUMSEG_LT, FINITE_SING,
        FORALL_AND_THM, FORALL_IN_IMAGE, FORALL_IN_INSERT, FUN_EQ_THM, IMP_CONJ,
        IMP_IMP, INFINITE, INFINITE_ENUMERATE_EQ, INFINITE_ENUMERATE_SUBSET,
        INFINITE_IMAGE, INJECTIVE_ALT, INSERT_SUBSET, IN_DIFF, IN_ELIM_THM, IN_UNIV,
        LEFT_IMP_EXISTS_THM, LT_ADD_RCANCEL, LT_CASES, LT_IMP_LE, LT_IMP_NE, LT_SUC_LE,
        LT_TRANS, MONO_EXISTS, MONO_FORALL, NOT_EXISTS_THM, NOT_FORALL_THM, NOT_IMP,
        NOT_INSERT_EMPTY, NOT_IN_EMPTY, PAIRWISE_IMAGE, RIGHT_FORALL_IMP_THM, SUBSET,
        SUBSET_EMPTY, SUBSET_REFL, SUBSET_UNIV, TRANSITIVE_STEPWISE_LE,
        TRANSITIVE_STEPWISE_LT, UNIONS_GSPEC, WF, WF_ANTISYM, WF_DCHAIN, WF_REC_EXISTS,
        WF_num, WLOG_LT, num_FINITE, num_INFINITE, o_THM, pairwise, .. } := D.core1
  let { POSET_IMP_QOSET, TOSET_IMP_POSET, TOSET_IMP_QOSET, WOSET_IMP_QOSET,
        WOSET_IMP_TOSET, WQOSET_IMP_QOSET, antichain, fld, poset, qoset, toset, woset,
        wqoset, .. } := BDefs
  -- @@SCOPE END

  -- In general, these need to be distinguished, but not for partial orders.

  let strictly ← new_definition
   r"strictly R = \x y:A. R x y /\ ~(R y x)"

  let properly ← new_definition
   r"properly R = \x y:A. R x y /\ ~(x = y)"

  let PROPERLY_EQ_STRICTLY ← prove
   r"!l:A->A->bool. poset l ==> properly l = strictly l"
   (REWRITE_TAC [poset, properly, strictly, FUN_EQ_THM] THEN MESON_TAC [])

  let STRICTLY_EQ_PROPERLY ← prove
   r"!l:A->A->bool. poset l ==> strictly l = properly l"
   (REWRITE_TAC [poset, properly, strictly, FUN_EQ_THM] THEN MESON_TAC [])

  let STRICTLY_IMP_PROPERLY ← prove
   r"!l x y:A. qoset l /\ strictly l x y ==> properly l x y"
   (REWRITE_TAC [qoset, properly, strictly, FUN_EQ_THM] THEN MESON_TAC [])

  let STRICTLY_STRICTLY ← prove
   r"!R:A->A->bool. strictly(strictly R) = strictly R"
   (REWRITE_TAC [FUN_EQ_THM, strictly] THEN MESON_TAC [])

  let PROPERLY_PROPERLY ← prove
   r"!R:A->A->bool. properly(properly R) = properly R"
   (REWRITE_TAC [FUN_EQ_THM, properly] THEN MESON_TAC [])

  let STRICTLY_PROPERLY ← prove
   r"!R:A->A->bool. strictly(properly R) = strictly R"
   (REWRITE_TAC [FUN_EQ_THM, strictly, properly] THEN MESON_TAC [])

  let PROPERLY_STRICTLY ← prove
   r"!R:A->A->bool. properly(strictly R) = strictly R"
   (REWRITE_TAC [FUN_EQ_THM, strictly, properly] THEN MESON_TAC [])

  let PROPERLY_MONO ← prove
   r"!R S. (!x y. R x y ==> S x y)
         ==> (!x y. properly R x y ==> properly S x y)"
   (REWRITE_TAC [properly] THEN MESON_TAC [])

  -- Various interrelations and alternative forms of definitions.

  let POSET_QOSET ← prove
   r"!l:A->A->bool.
        poset l <=> qoset l /\ (!x y. l x y /\ l y x ==> x = y)"
   (REWRITE_TAC [poset, qoset, ← GSYM CONJ_ASSOC])

  let TOSET ← prove
   r"!l:A->A->bool.
        toset l <=>
        (!x y z. l x y /\ l y z ==> l x z) /\
        (!x y. l x y /\ l y x ==> x = y) /\
        (!x y. x IN fld l /\ y IN fld l ==> l x y \/ l y x)"
   (REWRITE_TAC [toset] THEN MESON_TAC [])

  let TOSET_POSET ← prove
   r"!l:A->A->bool.
        toset l <=>
        poset l /\ (!x y. x IN fld l /\ y IN fld l ==> l x y \/ l y x)"
   (REWRITE_TAC [toset, poset, ← GSYM CONJ_ASSOC])

  let WOSET_TOSET ← prove
   r"!l:A->A->bool.
       woset l <=>
       toset l /\
       !s. s SUBSET fld l /\ ~(s = {}) ==> ?x. x IN s /\ !y. y IN s ==> l x y"
   (REWRITE_TAC [woset, toset, ← GSYM CONJ_ASSOC])

  let WQOSET ← prove
   r"!l:A->A->bool.
        wqoset l <=>
        (!x y z. l x y /\ l y z ==> l x z) /\
        (!s. s SUBSET fld l
             ==> ?t. FINITE t /\
                     t SUBSET s /\
                     !y. y IN s ==> ?x. x IN t /\ l x y)"
   (GEN_TAC THEN REWRITE_TAC [wqoset] THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC (← q "x:A") THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q "{x:A}")) THEN ASM SET_TAC [])

  let WQOSET_QOSET ← prove
   r"!l:A->A->bool.
       wqoset l <=>
       qoset l /\
       !s. s SUBSET fld l
           ==> ?t. FINITE t /\ t SUBSET s /\
                   !y. y IN s ==> ?x. x IN t /\ l x y"
   (REWRITE_TAC [wqoset, qoset, ← GSYM CONJ_ASSOC])

  let WOSET_POSET ← prove
   r"!l:A->A->bool.
       woset l <=>
       poset l /\
       !s. s SUBSET fld l /\ ~(s = {}) ==> ?x. x IN s /\ !y. y IN s ==> l x y"
   (GEN_TAC THEN REWRITE_TAC [woset, poset] THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MAP_EVERY X_GEN_TAC [← q "x:A", ← q "y:A"] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q "{x:A,y}")) THEN ASM SET_TAC [])

  let WOSET ← prove
   r"!l:A->A->bool.
       woset l <=>
       (!x y. l x y /\ l y x ==> x = y) /\
       !s. s SUBSET fld l /\ ~(s = {}) ==> ?x. x IN s /\ !y. y IN s ==> l x y"
   (← do
    let t ← TAUT (← q r"(r ==> p) /\ r /\ q ==> p /\ q /\ r")
    pure (GEN_TAC THEN REWRITE_TAC [woset] THEN
      EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC t THEN
      REPEAT CONJ_TAC THENL
       [MESON_TAC [],
        MAP_EVERY X_GEN_TAC [← q "x:A", ← q "y:A"] THEN STRIP_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q "{x:A,y}")) THEN ASM SET_TAC [],
        MAP_EVERY X_GEN_TAC [← q "x:A", ← q "y:A", ← q "z:A"] THEN STRIP_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q "{x:A,y,z}")) THEN
        REWRITE_TAC [fld] THEN ASM SET_TAC []]))

  let WOSET_WF ← prove
   r"!l:A->A->bool.
        woset l <=>
        (!x y. x IN fld l /\ y IN fld l ==> l x y \/ l y x) /\
        WF(properly l)"
   (← do
    let t2 ← TAUT (← q r"(p ==> q) /\ (q ==> (p <=> r)) ==> (q /\ r <=> p)")
    let t1 ← TAUT (← q r"(p ==> q) /\ (q ==> (p <=> r)) ==> (p <=> q /\ r)")
    pure (GEN_TAC THEN
      MATCH_MP_TAC t1 THEN
      CONJ_TAC THENL [SIMP_TAC [woset], DISCH_TAC THEN REWRITE_TAC [WOSET]] THEN
      MATCH_MP_TAC t2 THEN
      REWRITE_TAC [properly] THEN CONJ_TAC THENL
       [DISCH_THEN (MP_TAC o MATCH_MP WF_ANTISYM) THEN MESON_TAC [], DISCH_TAC] THEN
      REWRITE_TAC [WF] THEN EQ_TAC THEN DISCH_TAC THENL
       [X_GEN_TAC (← q r"s:A->bool") THEN STRIP_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"\x:A. x IN s")) THEN ASM SET_TAC [],
        X_GEN_TAC (← q r"P:A->bool") THEN DISCH_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"{x:A | x IN fld l /\ P x}")) THEN
        REWRITE_TAC [fld] THEN RULE_ASSUM_TAC (REWRITE_RULE [fld]) THEN
        ASM SET_TAC []]))

  let WOSET_IMP_WQOSET ← prove
   r"!l:A->A->bool. woset l ==> wqoset l"
   (GEN_TAC THEN REWRITE_TAC [woset, wqoset] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    X_GEN_TAC (← q r"s:A->bool") THEN DISCH_TAC THEN
    ASM_CASES_TAC (← q r"s:A->bool = {}") THEN ASM_REWRITE_TAC [NOT_IN_EMPTY] THENL
     [ASM_MESON_TAC [FINITE_EMPTY, SUBSET_EMPTY], ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"s:A->bool")) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "x:A") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q "{x:A}") THEN ASM_REWRITE_TAC [FINITE_SING] THEN ASM SET_TAC [])

  let WQOSET_SUPERSET ← prove
   r"!l m:A->A->bool.
        wqoset l /\
        qoset m /\
        fld m SUBSET fld l /\
        (!x y. l x y ==> m x y)
        ==> wqoset m"
   (REPEAT GEN_TAC THEN REWRITE_TAC [WQOSET_QOSET] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"s:A->bool") THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"s:A->bool")) THEN ASM SET_TAC [])

  let (WQOSET_NOBAD, WQOSET_NOBAD_SUBSEQ, WQOSET_ANTICHAIN) ← list3 (CONJUNCTS (← prove
   r"(!l:A->A->bool.
        wqoset l <=>
        qoset l /\
        !x. (!n:num. x n IN fld l) ==> ?i j. i < j /\ l (x i) (x j)) /\
   (!l:A->A->bool.
        wqoset l <=>
        qoset l /\
        !x. (!n. x n IN fld l)
            ==> ?r:num->num.
                    (!m n. m < n ==> r(m) < r(n)) /\
                    (!i j. i <= j ==> l (x(r i)) (x(r j)))) /\
   (!l:A->A->bool.
        wqoset l <=>
        qoset l /\
        WF(strictly l) /\
        !s. antichain l s ==> FINITE s)"
   (← do
    -- Built when OCaml builds the tactic, last first.
    let rG ← TAUT (← q r"~(p /\ q) <=> p ==> ~q")
    let rF ← MESON [] (← q r"(?x. P x /\ Q x /\ R x) <=> ~(!x. P x /\ Q x ==> ~R x)")
    let rE ← ARITH_RULE (← q r"n < SUC n")
    let rD ← TAUT (← q r"(p ==> q) /\ (p ==> (r <=> s)) ==> p /\ r ==> q /\ s")
    let rC ← MESON [] (← q r"!p. (!m. P m ==> Q(m - (p + 1))) ==> (?m. P m) ==> (?m. Q m)")
    let rB ← ARITH_RULE (← q r"~(n + p + 1 <= p)")
    let rA ← TAUT (← q r"(p ==> q) /\ (q ==> r) /\ (r ==> s) /\ (s ==> p)
      ==> (p <=> q) /\ (p <=> r) /\ (p <=> s)")
    let wfRec ← MATCH_MP WF_REC_EXISTS WF_num
    let infEnum ← REWRITE_RULE [INFINITE] INFINITE_ENUMERATE_SUBSET
    pure (REWRITE_TAC [AND_FORALL_THM] THEN X_GEN_TAC (← q r"l:A->A->bool") THEN
      REWRITE_TAC [wqoset, qoset, antichain, FORALL_AND_THM] THEN
      ASM_CASES_TAC (← q r"!x:A. x IN fld l ==> l x x") THEN ASM_REWRITE_TAC [] THEN
      ASM_CASES_TAC (← q r"!x y z:A. l x y /\ l y z ==> l x z") THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC rA THEN
      REPEAT CONJ_TAC THENL
       [DISCH_TAC THEN X_GEN_TAC (← q r"x:num->A") THEN DISCH_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"IMAGE (x:num->A) (:num)")) THEN ANTS_TAC THENL
         [ASM SET_TAC [], REWRITE_TAC [EXISTS_FINITE_SUBSET_IMAGE]] THEN
        REWRITE_TAC [FORALL_IN_IMAGE, EXISTS_IN_IMAGE, SUBSET_UNIV, IN_UNIV] THEN
        REWRITE_TAC [num_FINITE] THEN ASM_MESON_TAC [LT_SUC_LE],
        DISCH_TAC THEN X_GEN_TAC (← q r"x:num->A") THEN DISCH_TAC THEN
        SUBGOAL_THEN (← q r"~INFINITE {n | !p. n < p ==> ~l ((x:num->A) n) (x p)}")
        MP_TAC THENL
         [REWRITE_TAC [INFINITE_ENUMERATE_EQ, NOT_EXISTS_THM] THEN
          X_GEN_TAC (← q r"r:num->num") THEN STRIP_TAC THEN
          FIRST_X_ASSUM (MP_TAC o SPEC (← q r"(x:num->A) o (r:num->num)")) THEN
          ASM_REWRITE_TAC [o_THM] THEN ASM SET_TAC [],
          REWRITE_TAC [INFINITE, num_FINITE, IN_ELIM_THM]] THEN
        DISCH_THEN (X_CHOOSE_TAC (← q "p:num")) THEN
        SUBGOAL_THEN
         (← q r"?t:num->num.
            (!n:num. T) /\
            (!n. t n < t (SUC n) /\
                 (l:A->A->bool) (x(t n + p + 1)) (x(t(SUC n) + p + 1)))")
        MP_TAC THENL
        [MATCH_MP_TAC DEPENDENT_CHOICE THEN REWRITE_TAC [] THEN
         X_GEN_TAC (← q "n:num") THEN FIRST_X_ASSUM (MP_TAC o
           GEN_REWRITE_RULE id [← GSYM CONTRAPOS_THM] o SPEC (← q "n + p + 1")) THEN
         REWRITE_TAC [NOT_FORALL_THM, NOT_IMP, rB] THEN
         MATCH_MP_TAC rC THEN
         EXISTS_TAC (← q "p:num") THEN X_GEN_TAC (← q "q:num") THEN MATCH_MP_TAC rD THEN
         REPEAT STRIP_TAC THENL [ALL_TAC, AP_TERM_TAC THEN AP_TERM_TAC] THEN
         ASM_ARITH_TAC,
         REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"t:num->num") THEN
         STRIP_TAC THEN EXISTS_TAC (← q r"\i. (t:num->num) i + p + 1") THEN
         REWRITE_TAC [] THEN CONJ_TAC THENL
          [MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN
           ASM_REWRITE_TAC [LT_ADD_RCANCEL] THEN ARITH_TAC,
           MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN ASM_REWRITE_TAC [] THEN
           ASM_MESON_TAC []]],
         DISCH_TAC THEN CONJ_TAC THENL
          [REWRITE_TAC [WF_DCHAIN, strictly, NOT_EXISTS_THM, FORALL_AND_THM] THEN
           X_GEN_TAC (← q r"x:num->A") THEN STRIP_TAC THEN
           SUBGOAL_THEN
            (← q r"!m n:num. m < n ==> (l:A->A->bool) (x n) (x m) /\ ~l (x m) (x n)")
           ASSUME_TAC THENL
            [MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN ASM_MESON_TAC [],
             FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:num->A")) THEN
             REWRITE_TAC [fld, IN_ELIM_THM, NOT_IMP] THEN
             ASM_MESON_TAC [rE, LT_IMP_LE]],
           X_GEN_TAC (← q r"s:A->bool") THEN GEN_REWRITE_TAC id [← GSYM CONTRAPOS_THM] THEN
           REWRITE_TAC [infEnum] THEN
           REWRITE_TAC [INJECTIVE_ALT, LEFT_IMP_EXISTS_THM] THEN
           X_GEN_TAC (← q r"x:num->A") THEN REPEAT STRIP_TAC THEN
           FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:num->A")) THEN
           REWRITE_TAC [NOT_IMP] THEN CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
           DISCH_THEN (X_CHOOSE_THEN (← q r"r:num->num")
            (CONJUNCTS_THEN (MP_TAC o SPECL [← q "n:num", ← q "SUC n"]))) THEN
           REPEAT (ANTS_TAC THENL [ARITH_TAC, DISCH_TAC]) THEN
           FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [pairwise]) THEN
           DISCH_THEN (MP_TAC o SPECL
            [← q r"(x:num->A)(r(n:num))", ← q r"(x:num->A)(r(SUC n))"]) THEN
           ASM_SIMP_TAC [LT_IMP_NE]],
        STRIP_TAC THEN X_GEN_TAC (← q r"s:A->bool") THEN DISCH_TAC THEN
        ONCE_REWRITE_TAC [rF] THEN
        GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV)
         [NOT_FORALL_THM, NOT_IMP, NOT_EXISTS_THM] THEN
        DISCH_TAC THEN
        SUBGOAL_THEN
         (← q r"?x:num->A.
            !n. x n IN s DIFF UNIONS {{y | l (x m) y} | m < n} /\
                !z. z IN s DIFF UNIONS {{y | l (x m) y} | m < n}
                    ==> ~(l z (x n) /\ ~(l (x n) z))")
        MP_TAC THENL
         [MATCH_MP_TAC wfRec THEN
          REWRITE_TAC [UNIONS_GSPEC] THEN CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN
          MAP_EVERY X_GEN_TAC [← q r"x:num->A", ← q "n:num"] THEN
          REWRITE_TAC [IN_DIFF, IN_ELIM_THM] THEN DISCH_THEN (LABEL_TAC "*") THEN
          FIRST_X_ASSUM (MP_TAC o SPEC (← q r"IMAGE (x:num->A) {m | m < n}")) THEN
          SIMP_TAC [FINITE_IMAGE, FINITE_NUMSEG_LT] THEN
          REWRITE_TAC [SUBSET, rG] THEN
          ASM_SIMP_TAC [FORALL_IN_IMAGE, IN_ELIM_THM] THEN DISCH_TAC THEN
          FIRST_X_ASSUM (MP_TAC o SPEC
           (← q r"\y. y IN s /\ !m:num. m < n ==> ~((l:A->A->bool) (x m) y)") o
           GEN_REWRITE_RULE id [WF]) THEN
          ASM_REWRITE_TAC [strictly] THEN MATCH_MP_TAC MONO_EXISTS THEN
          ASM SET_TAC [],
          REWRITE_TAC [IN_DIFF, UNIONS_GSPEC, IN_ELIM_THM] THEN
          REWRITE_TAC [FORALL_AND_THM] THEN
          DISCH_THEN (X_CHOOSE_THEN (← q r"x:num->A") STRIP_ASSUME_TAC) THEN
          SUBGOAL_THEN (← q r"FINITE(IMAGE (x:num->A) (:num))") MP_TAC THENL
           [FIRST_X_ASSUM MATCH_MP_TAC THEN
            CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
            REWRITE_TAC [PAIRWISE_IMAGE] THEN REWRITE_TAC [pairwise, IN_UNIV],
            REWRITE_TAC [← GSYM INFINITE] THEN MATCH_MP_TAC INFINITE_IMAGE THEN
            REWRITE_TAC [num_INFINITE, IN_UNIV]] THEN
          MATCH_MP_TAC WLOG_LT THEN ASM SET_TAC []]]))))

  let WQOSET_IMP_WF ← prove
   r"!l:A->A->bool. wqoset l ==> WF(strictly l)"
   (SIMP_TAC [WQOSET_ANTICHAIN])

  let WQOSET_WF_SUPERSET ← prove
   r"!l m:A->A->bool.
        wqoset l /\ qoset m /\ fld m SUBSET fld l /\ (!x y. l x y ==> m x y)
        ==> WF(strictly m)"
   (MESON_TAC [WQOSET_SUPERSET, WQOSET_IMP_WF])

  let WQOSET_WF_SUPERSET_EQ ← prove
   r"!l:A->A->bool.
        wqoset l <=>
        qoset l /\
        !m. qoset m /\ fld m = fld l /\ (!x y. l x y ==> m x y)
            ==> WF(strictly m)"
   (← do
    let r5 ← ARITH_RULE (← q r"~(n < l) /\ ~(k < SUC n) ==> ~(k < l)")
    let r4 ← ARITH_RULE (← q r"n < SUC n")
    let r3 ← ARITH_RULE (← q r"n < SUC n")
    let r2 ← TAUT (← q r"r /\ (r ==> p /\ q /\ s) ==> p /\ q /\ r /\ s")
    let r1 ← MESON [] (← q r"~(!i j. P i j ==> ~Q i j) ==> ?i j. P i j /\ Q i j")
    pure (GEN_TAC THEN EQ_TAC THENL
       [MESON_TAC [WQOSET_WF_SUPERSET, WQOSET_IMP_QOSET, SUBSET_REFL],
        STRIP_TAC THEN ASM_REWRITE_TAC [WQOSET_NOBAD]] THEN
      X_GEN_TAC (← q r"a:num->A") THEN DISCH_TAC THEN MATCH_MP_TAC r1 THEN
      DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC
       (← q r"\x y:A. l x y \/ ?i j:num. i < j /\ l x (a j) /\ l (a i) y")) THEN
      REWRITE_TAC [qoset, NOT_IMP, ← GSYM CONJ_ASSOC] THEN SIMP_TAC [] THEN
      MATCH_MP_TAC r2 THEN
      CONJ_TAC THENL
       [REWRITE_TAC [fld] THEN RULE_ASSUM_TAC (REWRITE_RULE [fld]) THEN ASM SET_TAC [],
        DISCH_THEN SUBST1_TAC] THEN
      FIRST_X_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE id [qoset]) THEN
      ASM_SIMP_TAC [] THEN CONJ_TAC THENL
       [ASM_MESON_TAC [LT_TRANS, LT_CASES], ALL_TAC] THEN
      REWRITE_TAC [WF_DCHAIN, strictly] THEN EXISTS_TAC (← q r"a:num->A") THEN
      X_GEN_TAC (← q "n:num") THEN CONJ_TAC THENL
       [ASM_MESON_TAC [r3], ALL_TAC] THEN
      ASM_SIMP_TAC [r4, NOT_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q "k:num", ← q "l:num"] THEN STRIP_TAC THEN
      ASM_MESON_TAC [r5]))

  let WOSET_WQOSET ← prove
   r"!l:A->A->bool. woset l <=> toset l /\ wqoset l"
   (GEN_TAC THEN EQ_TAC THEN SIMP_TAC [WOSET_IMP_TOSET, WOSET_IMP_WQOSET] THEN
    SIMP_TAC [WOSET_WF, PROPERLY_EQ_STRICTLY, WQOSET_IMP_WF, TOSET_IMP_POSET] THEN
    REWRITE_TAC [toset] THEN STRIP_TAC THEN ASM_REWRITE_TAC [])

  -- Restrictions of ordered sets.

  let FLD_RESTRICT_QOSET ← prove
   r"!(l:A->A->bool) P.
        qoset l ==> fld (\x y. P x /\ P y /\ l x y) = {x | x IN fld l /\ P x}"
   (REWRITE_TAC [qoset, fld] THEN SET_TAC [])

  let FLD_RESTRICT_POSET ← prove
   r"!(l:A->A->bool) P.
        poset l ==> fld (\x y. P x /\ P y /\ l x y) = {x | x IN fld l /\ P x}"
   (SIMP_TAC [FLD_RESTRICT_QOSET, POSET_IMP_QOSET])

  let FLD_RESTRICT_TOSET ← prove
   r"!(l:A->A->bool) P.
        toset l ==> fld (\x y. P x /\ P y /\ l x y) = {x | x IN fld l /\ P x}"
   (SIMP_TAC [FLD_RESTRICT_QOSET, TOSET_IMP_QOSET])

  let FLD_RESTRICT_WOSET ← prove
   r"!(l:A->A->bool) P.
        woset l ==> fld (\x y. P x /\ P y /\ l x y) = {x | x IN fld l /\ P x}"
   (SIMP_TAC [FLD_RESTRICT_QOSET, WOSET_IMP_QOSET])

  let FLD_RESTRICT_WQOSET ← prove
   r"!(l:A->A->bool) P.
       wqoset l ==> fld (\x y. P x /\ P y /\ l x y) = {x | x IN fld l /\ P x}"
   (SIMP_TAC [FLD_RESTRICT_QOSET, WQOSET_IMP_QOSET])

  let QOSET_RESTRICT ← prove
   r"!(l:A->A->bool) P. qoset l ==> qoset (\x y. P x /\ P y /\ l x y)"
   (REWRITE_TAC [qoset, fld] THEN SET_TAC [])

  let POSET_RESTRICT ← prove
   r"!(l:A->A->bool) P. poset l ==> poset (\x y. P x /\ P y /\ l x y)"
   (REWRITE_TAC [poset, fld] THEN SET_TAC [])

  let TOSET_RESTRICT ← prove
   r"!(l:A->A->bool) P. toset l ==> toset (\x y. P x /\ P y /\ l x y)"
   (REWRITE_TAC [toset, fld] THEN SET_TAC [])

  let WOSET_RESTRICT ← prove
   r"!(l:A->A->bool) P. woset l ==> woset (\x y. P x /\ P y /\ l x y)"
   (REPEAT GEN_TAC THEN
    SIMP_TAC [WOSET_POSET, FLD_RESTRICT_POSET, POSET_RESTRICT] THEN
    SET_TAC [])

  let WQOSET_RESTRICT ← prove
   r"!(l:A->A->bool) P. wqoset l ==> wqoset (\x y. P x /\ P y /\ l x y)"
   (REPEAT GEN_TAC THEN
    SIMP_TAC [WQOSET_NOBAD_SUBSEQ, FLD_RESTRICT_QOSET, QOSET_RESTRICT] THEN
    SET_TAC [])

  -- Finite sets have maximal/minimal/greatest/least in various senses.

  let (QOSET_MIN, QOSET_MAX) ← CONJ_PAIR (← prove
   r"(!l s:A->bool.
        qoset l /\ FINITE s /\ ~(s = {}) /\ s SUBSET fld l
        ==> ?a. a IN s /\ !x. x IN s ==> ~(strictly l x a)) /\
   (!l s:A->bool.
        qoset l /\ FINITE s /\ ~(s = {}) /\ s SUBSET fld l
        ==> ?a. a IN s /\ !x. x IN s ==> ~(strictly l a x))"
   (← do
    let t ← TAUT (← q r"~(p /\ ~p)")
    pure (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
      CONJ_TAC THEN GEN_TAC THEN DISCH_TAC THEN
      MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
      REWRITE_TAC [IMP_IMP, NOT_INSERT_EMPTY] THEN
      REWRITE_TAC [FORALL_IN_INSERT, EXISTS_IN_INSERT, INSERT_SUBSET] THEN
      MAP_EVERY X_GEN_TAC [← q "a:A", ← q r"s:A->bool"] THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC (← q r"s:A->bool = {}") THEN
      ASM_REWRITE_TAC [NOT_IN_EMPTY, strictly, t] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [qoset, SUBSET, fld, IN_ELIM_THM]) THEN
      ASM METIS_TAC [])))

  let (POSET_MIN, POSET_MAX) ← CONJ_PAIR (← prove
   r"(!l s:A->bool.
        poset l /\ FINITE s /\ ~(s = {}) /\ s SUBSET fld l
        ==> ?a. a IN s /\ !x. x IN s ==> ~(properly l x a)) /\
   (!l s:A->bool.
        poset l /\ FINITE s /\ ~(s = {}) /\ s SUBSET fld l
        ==> ?a. a IN s /\ !x. x IN s ==> ~(properly l a x))"
   (SIMP_TAC [PROPERLY_EQ_STRICTLY, QOSET_MIN, QOSET_MAX, POSET_IMP_QOSET]))

  let (TOSET_MIN, TOSET_MAX) ← CONJ_PAIR (← prove
   r"(!l s:A->bool.
        toset l /\ FINITE s /\ ~(s = {}) /\ s SUBSET fld l
        ==> ?a. a IN s /\ !x. x IN s ==> l a x) /\
   (!l s:A->bool.
        toset l /\ FINITE s /\ ~(s = {}) /\ s SUBSET fld l
        ==> ?a. a IN s /\ !x. x IN s ==> l x a)"
   (CONJ_TAC THENL [MP_TAC POSET_MIN, MP_TAC POSET_MAX] THEN
    REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN
    ASM_SIMP_TAC [TOSET_IMP_POSET] THEN MATCH_MP_TAC MONO_EXISTS THEN
    REWRITE_TAC [properly] THEN RULE_ASSUM_TAC (REWRITE_RULE [toset]) THEN
    ASM SET_TAC []))

  -- @@RETURN BEGIN
  return { strictly, properly, PROPERLY_EQ_STRICTLY, STRICTLY_EQ_PROPERLY,
           STRICTLY_IMP_PROPERLY, STRICTLY_STRICTLY, PROPERLY_PROPERLY,
           STRICTLY_PROPERLY, PROPERLY_STRICTLY, PROPERLY_MONO, POSET_QOSET, TOSET,
           TOSET_POSET, WOSET_TOSET, WQOSET, WQOSET_QOSET, WOSET_POSET, WOSET, WOSET_WF,
           WOSET_IMP_WQOSET, WQOSET_SUPERSET, WQOSET_NOBAD, WQOSET_NOBAD_SUBSEQ,
           WQOSET_ANTICHAIN, WQOSET_IMP_WF, WQOSET_WF_SUPERSET, WQOSET_WF_SUPERSET_EQ,
           WOSET_WQOSET, FLD_RESTRICT_QOSET, FLD_RESTRICT_POSET, FLD_RESTRICT_TOSET,
           FLD_RESTRICT_WOSET, FLD_RESTRICT_WQOSET, QOSET_RESTRICT, POSET_RESTRICT,
           TOSET_RESTRICT, WOSET_RESTRICT, WQOSET_RESTRICT, QOSET_MIN, QOSET_MAX,
           POSET_MIN, POSET_MAX, TOSET_MIN, TOSET_MAX }
  -- @@RETURN END

/-- `let [a; b; c; d; e] = l`. -/
def list5 (l : List thm) : ExceptT String IO (thm × thm × thm × thm × thm) :=
  match l with
  | [a, b, c, d, e] => pure (a, b, c, d, e)
  | _ => throw "Match_failure"

/- ------------------------------------------------------------------------- -/
/- The trivial relation and the natural numbers are every kind of ordered    -/
/- set; pointwise orders and Dickson's lemma; initial segments, `linseg`,    -/
/- ordinals; useful things about the orderings.  (wo.ml 616-798)             -/
/- ------------------------------------------------------------------------- -/

structure Segs where
  -- @@FIELDS
  FLD_TRIVIAL : thm
  WOSET_TRIVIAL : thm
  WQOSET_TRIVIAL : thm
  TOSET_TRIVIAL : thm
  POSET_TRIVIAL : thm
  QOSET_TRIVIAL : thm
  FLD_num : thm
  WOSET_num : thm
  WQOSET_num : thm
  TOSET_num : thm
  POSET_num : thm
  QOSET_num : thm
  QOSET_POINTWISE : thm
  FLD_POINTWISE : thm
  WQOSET_POINTWISE : thm
  DICKSON : thm
  inseg : thm
  INSEG_ANTISYM : thm
  INSEG_REFL : thm
  INSEG_TRANS : thm
  linseg : thm
  ordinal : thm
  POSET_REFL : thm
  POSET_TRANS : thm
  POSET_ANTISYM : thm
  POSET_FLDEQ : thm
  WOSET_REFL : thm
  WOSET_TRANS : thm
  WOSET_ANTISYM : thm
  WOSET_TOTAL : thm
  WOSET_WELL : thm
  WOSET_FLDEQ : thm
  WOSET_TRANS_LESS : thm
  PAIRED_EXT : thm
  deriving Inhabited

@[nospecialize]
def setupSegs [HolBase] (D : WoDeps) (BDefs : Defs) (BOrders : Orders) :
    ExceptT String IO Segs := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON, MESON_TAC, SET_TAC, new_definition, parse_as_infix, .. } := D
  let { ETA_AX, FINITE_INDUCT_STRONG, FINITE_NUMSEG_LT, FORALL_AND_THM,
        FORALL_IN_INSERT, FORALL_PAIR_THM, FUN_EQ_THM, IMP_CONJ, IN, IN_ELIM_THM,
        IN_UNIV, LEFT_IMP_EXISTS_THM, LE_CASES, LE_LT, LT_LE, MEMBER_NOT_EMPTY,
        MONO_AND, MONO_IMP, NOT_IN_EMPTY, RIGHT_FORALL_IMP_THM, SUBSET, WF_num, o_THM, .. } := D.core1
  let { FLD_EQ_EMPTY, IN_FLD, QOSET_FLD, WOSET_IMP_POSET, WOSET_IMP_QOSET,
        WOSET_IMP_TOSET, WQOSET_IMP_QOSET, fld, poset, qoset, woset, .. } := BDefs
  let { WOSET_IMP_WQOSET, WOSET_WF, WQOSET_NOBAD, WQOSET_NOBAD_SUBSEQ, properly, .. } := BOrders
  -- @@SCOPE END

  -- The trivial relation is every kind of ordered set.

  let FLD_TRIVIAL ← prove
   r"fld(\x y:A. F) = {}"
   (REWRITE_TAC [FLD_EQ_EMPTY])

  let WOSET_TRIVIAL ← prove
   r"woset(\x y:A. F)"
   (REWRITE_TAC [woset, FLD_TRIVIAL, NOT_IN_EMPTY] THEN SET_TAC [])

  let WQOSET_TRIVIAL ← prove
   r"wqoset(\x y:A. F)"
   (SIMP_TAC [WOSET_IMP_WQOSET, WOSET_TRIVIAL])

  let TOSET_TRIVIAL ← prove
   r"toset(\x y:A. F)"
   (SIMP_TAC [WOSET_IMP_TOSET, WOSET_TRIVIAL])

  let POSET_TRIVIAL ← prove
   r"poset(\x y:A. F)"
   (SIMP_TAC [WOSET_IMP_POSET, WOSET_TRIVIAL])

  let QOSET_TRIVIAL ← prove
   r"qoset(\x y:A. F)"
   (SIMP_TAC [WOSET_IMP_QOSET, WOSET_TRIVIAL])

  -- The natural numbers with the usual <= are every kind of ordered set.

  let FLD_num ← prove
   r"fld(<=) = (:num)"
   (REWRITE_TAC [fld, IN_ELIM_THM, LE_CASES] THEN SET_TAC [])

  let WOSET_num ← prove
   r"woset((<=):num->num->bool)"
   (REWRITE_TAC [WOSET_WF, fld, IN_ELIM_THM, LE_CASES, properly] THEN
    REWRITE_TAC [← GSYM LT_LE, ETA_AX, WF_num])

  let WQOSET_num ← prove
   r"wqoset((<=):num->num->bool)"
   (SIMP_TAC [WOSET_IMP_WQOSET, WOSET_num])

  let TOSET_num ← prove
   r"toset((<=):num->num->bool)"
   (SIMP_TAC [WOSET_IMP_TOSET, WOSET_num])

  let POSET_num ← prove
   r"poset((<=):num->num->bool)"
   (SIMP_TAC [WOSET_IMP_POSET, WOSET_num])

  let QOSET_num ← prove
   r"qoset((<=):num->num->bool)"
   (SIMP_TAC [WOSET_IMP_QOSET, WOSET_num])

  -- Pointwise orders (no domain restriction, a quasi-order in general).
  -- Hence Dickson's lemma in the general WQO setting and common special case.

  let QOSET_POINTWISE ← prove
   r"!l s. qoset(\x y:K->A. !i. i IN s ==> l (x i) (y i)) <=>
         s = {} \/ qoset l"
   (← do
    let m ← MESON [] (← q r"(!a. P (\i. a) ==> Q a) ==> (!a. P a) ==> !b. Q b")
    pure (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"s:K->bool = {}") THENL
       [ASM_REWRITE_TAC [NOT_IN_EMPTY, qoset], ASM_REWRITE_TAC []] THEN
      ASM_REWRITE_TAC [qoset, fld, IN_ELIM_THM] THEN
      EQ_TAC THENL [ALL_TAC, SET_TAC []] THEN
      MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN
      REPEAT (MATCH_MP_TAC m THEN GEN_TAC)
      THENL [ALL_TAC, ASM SET_TAC []] THEN MATCH_MP_TAC MONO_IMP THEN
      REWRITE_TAC [] THEN CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q "y:A")) THEN EXISTS_TAC (← q r"(\i. y):K->A") THEN
      ASM SET_TAC []))

  let FLD_POINTWISE ← prove
   r"!l s. qoset l
         ==> fld(\x y:K->A. !i. i IN s ==> l (x i) (y i)) =
             {x | !i. i IN s ==> x i IN fld l}"
   (← do
    -- `W(MP_TAC o PART_MATCH (lhand o rand) QOSET_FLD o lhand o snd)`
    let mpPart : tactic := fun gl => ExceptT.run do
      let t ← liftExcept (lhand gl.2)
      ExceptT.mk (MP_TAC (← PART_MATCH (fun c => do lhand (← rand c)) QOSET_FLD t) gl)
    pure (SIMP_TAC [QOSET_FLD, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      mpPart THEN
      REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
      POP_ASSUM MP_TAC THEN ASM_SIMP_TAC [QOSET_POINTWISE]))

  let WQOSET_POINTWISE ← prove
   r"!l s. wqoset l /\ FINITE s
         ==> wqoset(\x y:K->A. !i. i IN s ==> l (x i) (y i))"
   (← do
    let tx ← q r"x:num->K->A"
    pure (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, WQOSET_NOBAD_SUBSEQ] THEN
      GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
      ASM_SIMP_TAC [QOSET_POINTWISE, FLD_POINTWISE, IN_UNIV, IN_ELIM_THM] THEN
      MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
       [REWRITE_TAC [NOT_IN_EMPTY] THEN EXISTS_TAC (← q r"\n:num. n") THEN REWRITE_TAC [],
        MAP_EVERY X_GEN_TAC [← q "a:K", ← q r"s:K->bool"]] THEN
      REWRITE_TAC [FORALL_IN_INSERT, FORALL_AND_THM] THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN DISCH_THEN (fun th =>
        X_GEN_TAC tx THEN STRIP_TAC THEN
        tactic_of do pure (MP_TAC (← SPEC tx th))) THEN
      ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"l:num->num") THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"\i:num. (x:num->K->A) (l i) a")) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"r:num->num") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"(l:num->num) o (r:num->num)") THEN
      ASM_SIMP_TAC [o_THM] THEN ASM_MESON_TAC [LE_LT]))

  let DICKSON ← prove
   r"!n x:num->num->num. ?i j. i < j /\ (!k. k < n ==> x i k <= x j k)"
   (GEN_TAC THEN
    MP_TAC (← ISPECL [← q r"(<=):num->num->bool", ← q r"{m:num | m < n}"]
          WQOSET_POINTWISE) THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [WQOSET_NOBAD] THEN
    SIMP_TAC [FLD_POINTWISE, WQOSET_IMP_QOSET, QOSET_POINTWISE] THEN
    SIMP_TAC [WOSET_IMP_WQOSET, WOSET_num, FLD_num, IN_UNIV, IN_ELIM_THM] THEN
    SIMP_TAC [FINITE_NUMSEG_LT])

  -- General (reflexive) notion of initial segment.

  parse_as_infix ("inseg", (12, "right"))

  let inseg ← new_definition
   r"(l:A->A->bool) inseg m <=> !x y. l x y <=> m x y /\ fld(l) y"

  let INSEG_ANTISYM ← prove
   r"!l m:A->A->bool. l inseg m /\ m inseg l ==> l = m"
   (REWRITE_TAC [FUN_EQ_THM, FORALL_PAIR_THM] THEN
    REWRITE_TAC [inseg] THEN MESON_TAC [])

  let INSEG_REFL ← prove
   r"!l:A->A->bool. l inseg l"
   (REWRITE_TAC [inseg, ← REWRITE_RULE [IN] IN_FLD] THEN MESON_TAC [])

  let INSEG_TRANS ← prove
   r"!l m n:A->A->bool. l inseg m /\ m inseg n ==> l inseg n"
   (REWRITE_TAC [inseg, ← REWRITE_RULE [IN] IN_FLD] THEN MESON_TAC [])

  -- Specific form of initial segment: `all elements in fld(l) less than a`.

  let linseg ← new_definition
   r"linseg (l:A->A->bool) a = \ x y. l x y /\ (properly l) y a"

  -- `Ordinals`, i.e. canonical wosets using choice operator.

  let ordinal ← new_definition
   r"ordinal(l:A->A->bool) <=>
    woset(l) /\ (!x. fld(l) x ==> (x = (@) (\y. ~(properly l) y x)))"

  -- Now useful things about the orderings

  let (POSET_REFL, POSET_TRANS, POSET_ANTISYM) ← list3 (← do
    let tl ← q r"l:A->A->bool"
    let ths := CONJUNCTS (← REWRITE_RULE [poset, IN] (← ASSUME (← q r"poset (l:A->A->bool)")))
    ths.mapM (fun th => do GEN tl (← DISCH_ALL th)))

  let POSET_FLDEQ ← prove
   r"!l:A->A->bool. poset l ==> (!x. fld(l) x <=> l x x)"
   (MESON_TAC [POSET_REFL, ← REWRITE_RULE [IN] IN_FLD])

  let (WOSET_REFL, WOSET_TRANS, WOSET_ANTISYM, WOSET_TOTAL, WOSET_WELL) ← list5 (← do
    let tl ← q r"l:A->A->bool"
    let ths := CONJUNCTS (← REWRITE_RULE [woset, SUBSET, ← GSYM MEMBER_NOT_EMPTY, IN]
         (← ASSUME (← q r"woset (l:A->A->bool)")))
    ths.mapM (fun th => do GEN tl (← DISCH_ALL th)))

  let WOSET_FLDEQ ← prove
   r"!l:A->A->bool. woset l ==> (!x. fld(l) x <=> l x x)"
   (MESON_TAC [WOSET_IMP_POSET, POSET_FLDEQ])

  let WOSET_TRANS_LESS ← prove
   r"!l:A->A->bool. woset l ==>
       !x y z. (properly l) x y /\ l y z ==> (properly l) x z"
   (REWRITE_TAC [woset, properly] THEN MESON_TAC [])

  -- Misc lemmas.

  let PAIRED_EXT ← prove
   r"!(l:A->B->C) m. (!x y. l x y = m x y) <=> (l = m)"
   (REWRITE_TAC [FUN_EQ_THM])

  -- @@RETURN BEGIN
  return { FLD_TRIVIAL, WOSET_TRIVIAL, WQOSET_TRIVIAL, TOSET_TRIVIAL, POSET_TRIVIAL,
           QOSET_TRIVIAL, FLD_num, WOSET_num, WQOSET_num, TOSET_num, POSET_num,
           QOSET_num, QOSET_POINTWISE, FLD_POINTWISE, WQOSET_POINTWISE, DICKSON, inseg,
           INSEG_ANTISYM, INSEG_REFL, INSEG_TRANS, linseg, ordinal, POSET_REFL,
           POSET_TRANS, POSET_ANTISYM, POSET_FLDEQ, WOSET_REFL, WOSET_TRANS,
           WOSET_ANTISYM, WOSET_TOTAL, WOSET_WELL, WOSET_FLDEQ, WOSET_TRANS_LESS,
           PAIRED_EXT }
  -- @@RETURN END

/-- `UNDISCH_TAC o check p o concl`, for `FIRST_ASSUM`. -/
def undischCheck [HolBase] (p : term → Except String Bool) : thm_tactic := fun th =>
  tactic_of do
    if (← liftExcept (p (concl th))) then pure (UNDISCH_TAC (concl th))
    else throw "check"

/-- `W(C SUBGOAL_THEN ttac o funpow 2 lhand o snd)` -/
def subgoalLhand2 [HolBase] (ttac : thm_tactic) : tactic := fun gl => ExceptT.run do
  let t ← liftExcept (funpow 2 (fun (m : Except String term) => do lhand (← m)) (pure gl.2))
  ExceptT.mk (SUBGOAL_THEN t ttac gl)

/- ------------------------------------------------------------------------- -/
/- More woset lemmas; (2) AXIOM OF CHOICE ==> CANTOR-ZERMELO WELLORDERING    -/
/- THEOREM: unions and woset-ness of initial segments, `linseg` segments,    -/
/- canonicality of ordinals, successors.  (wo.ml 800-1088)                   -/
/- ------------------------------------------------------------------------- -/

structure Inseg where
  -- @@FIELDS
  WOSET_TRANS_LE : thm
  WOSET_WELL_CONTRAPOS : thm
  WOSET_TOTAL_LE : thm
  WOSET_TOTAL_LT : thm
  ORDINAL_IMP_WOSET : thm
  WOSET_FINITE_TOSET : thm
  UNION_FLD : thm
  UNION_INSEG : thm
  INSEG_SUBSET : thm
  INSEG_SUBSET_FLD : thm
  INSEG_FLD_SUBSET : thm
  INSEG_WOSET : thm
  INSEG_ORDINAL : thm
  LINSEG_INSEG : thm
  LINSEG_WOSET : thm
  LINSEG_FLD : thm
  INSEG_PROPER_SUBSET : thm
  INSEG_PROPER_SUBSET_FLD : thm
  INSEG_LINSEG : thm
  EXTEND_FLD : thm
  EXTEND_INSEG : thm
  EXTEND_LINSEG : thm
  ORDINAL_CHAINED_LEMMA : thm
  ORDINAL_CHAINED : thm
  ORDINAL_FLD_UNIQUE : thm
  ORDINAL_FLD_SUBSET : thm
  ORDINAL_FLD_SUBSET_EQ : thm
  FLD_SUC : thm
  ORDINAL_SUC : thm
  deriving Inhabited

@[nospecialize]
def setupInseg [HolBase] (D : WoDeps) (BDefs : Defs) (BOrders : Orders) (BSegs : Segs) :
    ExceptT String IO Inseg := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON, MESON_TAC, SELECT_CONV, SET_TAC, .. } := D
  let { EQ_IMP, FINITE_SUBSET, FORALL_PAIR_THM, FUN_EQ_THM, IMP_CONJ, IN, IN_ELIM_THM,
        MEMBER_NOT_EMPTY, NOT_EXISTS_THM, SUBSET, WF_FINITE, .. } := D.core1
  let { FINITE_FLD, IN_FLD, PBETA_TAC, UNIONS_PRED, fld, poset, .. } := BDefs
  let { TOSET_POSET, WOSET, WOSET_WF, properly, .. } := BOrders
  let { INSEG_REFL, PAIRED_EXT, WOSET_ANTISYM, WOSET_REFL, WOSET_TOTAL, WOSET_TRANS,
        WOSET_WELL, inseg, linseg, ordinal, .. } := BSegs
  -- @@SCOPE END

  let WOSET_TRANS_LE ← prove
   r"!l:A->A->bool. woset l ==>
       !x y z. l x y /\ (properly l) y z ==> (properly l) x z"
   (REWRITE_TAC [properly] THEN MESON_TAC [WOSET_TRANS, WOSET_ANTISYM])

  let WOSET_WELL_CONTRAPOS ← prove
   r"!l:A->A->bool. woset l ==>
                (!P. (!x. P x ==> fld(l) x) /\ (?x. P x) ==>
                     (?y. P y /\ (!z. (properly l) z y ==> ~P z)))"
   (GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q r"P:A->bool") o MATCH_MP WOSET_WELL) THEN
    ASM_MESON_TAC [WOSET_TRANS_LE, properly])

  let WOSET_TOTAL_LE ← prove
   r"!l:A->A->bool. woset l
                 ==> !x y. fld(l) x /\ fld(l) y ==> l x y \/ (properly l) y x"
   (REWRITE_TAC [properly] THEN MESON_TAC [WOSET_REFL, WOSET_TOTAL])

  let WOSET_TOTAL_LT ← prove
   r"!l:A->A->bool. woset l ==>
     !x y. fld(l) x /\ fld(l) y
           ==> x = y \/ (properly l) x y \/ (properly l) y x"
   (REWRITE_TAC [properly] THEN MESON_TAC [WOSET_TOTAL])

  let ORDINAL_IMP_WOSET ← prove
   r"!l:A->A->bool. ordinal l ==> woset l"
   (SIMP_TAC [ordinal])

  let WOSET_FINITE_TOSET ← prove
   r"!l:A->A->bool. toset l /\ FINITE {(x,y) | l x y} ==> woset l"
   (← do
    let fs ← ONCE_REWRITE_RULE [IMP_CONJ] FINITE_SUBSET
    pure (ONCE_REWRITE_TAC [← GSYM FINITE_FLD] THEN
      SIMP_TAC [TOSET_POSET, WOSET_WF, properly, poset, IN] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC WF_FINITE THEN REWRITE_TAC [] THEN
      CONJ_TAC THENL [ASM_MESON_TAC [], X_GEN_TAC (← q "a:A")] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP fs) THEN
      REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN
      REWRITE_TAC [← REWRITE_RULE [IN] IN_FLD, IN] THEN
      ASM_MESON_TAC []))

  -- UNIONS of initial segments is an initial segment.

  let UNION_FLD ← prove
   r"!P. fld(\x y:A. ?l. P l /\ l x y) x <=> ?l. P l /\ fld(l) x"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← REWRITE_RULE [IN] IN_FLD] THEN MESON_TAC [])

  let UNION_INSEG ← prove
   r"!P (l:A->A->bool).
        (!m. P m ==> m inseg l)
        ==> (\x y. ?l. P l /\ l x y) inseg l"
   (REWRITE_TAC [inseg, UNION_FLD, UNIONS_PRED] THEN ASM_MESON_TAC [])

  -- Initial segment of a woset is a woset.

  let INSEG_SUBSET ← prove
   r"!(l:A->A->bool) m. m inseg l ==> !x y. m x y ==> l x y"
   (REPEAT GEN_TAC THEN REWRITE_TAC [inseg] THEN MESON_TAC [])

  let INSEG_SUBSET_FLD ← prove
   r"!(l:A->A->bool) m. m inseg l ==> !x. fld(m) x ==> fld(l) x"
   (REWRITE_TAC [← REWRITE_RULE [IN] IN_FLD] THEN MESON_TAC [INSEG_SUBSET])

  let INSEG_FLD_SUBSET ← prove
   r"!l m:A->A->bool. l inseg m ==> fld l SUBSET fld m"
   (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP INSEG_SUBSET_FLD) THEN
    SET_TAC [])

  let INSEG_WOSET ← prove
   r"!(l:A->A->bool) m. m inseg l /\ woset l ==> woset m"
   (REWRITE_TAC [inseg] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [WOSET, SUBSET, ← GSYM MEMBER_NOT_EMPTY, IN] THEN CONJ_TAC THENL
     [ASM_MESON_TAC [WOSET_ANTISYM],
      X_GEN_TAC (← q r"P:A->bool") THEN
      FIRST_ASSUM (MP_TAC o SPEC (← q r"P:A->bool") o MATCH_MP WOSET_WELL) THEN
      REWRITE_TAC [fld, SUBSET, IN_ELIM_THM] THEN
      ASM_MESON_TAC [← REWRITE_RULE [IN] IN_FLD]])

  let INSEG_ORDINAL ← prove
   r"!l m:A->A->bool. m inseg l /\ ordinal l ==> ordinal m"
   (REPEAT GEN_TAC THEN REWRITE_TAC [ordinal] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC [INSEG_WOSET], ALL_TAC] THEN
    X_GEN_TAC (← q "x:A") THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q "x:A")) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP INSEG_SUBSET_FLD) THEN
    ASM_SIMP_TAC [] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE [inseg]) THEN ASM_REWRITE_TAC [properly])

  -- Properties of segments of the `linseg` form.

  let LINSEG_INSEG ← prove
   r"!(l:A->A->bool) a. woset l ==> (linseg l a) inseg l"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [inseg, linseg, ← REWRITE_RULE [IN] IN_FLD] THEN PBETA_TAC THEN
    ASM_MESON_TAC [WOSET_TRANS_LE])

  let LINSEG_WOSET ← prove
   r"!(l:A->A->bool) a. woset l ==> woset(linseg l a)"
   (MESON_TAC [INSEG_WOSET, LINSEG_INSEG])

  let LINSEG_FLD ← prove
   r"!(l:A->A->bool) a x. woset l ==> (fld (linseg l a) x <=> (properly l) x a)"
   (REWRITE_TAC [← REWRITE_RULE [IN] IN_FLD, linseg, properly] THEN PBETA_TAC THEN
    MESON_TAC [WOSET_REFL, WOSET_TRANS, WOSET_ANTISYM, ← REWRITE_RULE [IN] IN_FLD])

  -- Key fact: a proper initial segment is of the special form.

  let INSEG_PROPER_SUBSET ← prove
   r"!(l:A->A->bool) m. m inseg l /\ ~(l = m) ==>
                   ?x y. l x y /\ ~m x y"
   (REWRITE_TAC [← GSYM PAIRED_EXT] THEN MESON_TAC [INSEG_SUBSET])

  let INSEG_PROPER_SUBSET_FLD ← prove
   r"!(l:A->A->bool) m. m inseg l /\ ~(l = m) ==>
                   ?a. fld(l) a /\ ~fld(m) a"
   (MESON_TAC [INSEG_PROPER_SUBSET, ← REWRITE_RULE [IN] IN_FLD, inseg])

  let INSEG_LINSEG ← prove
   r"!(l:A->A->bool) m. woset l ==>
      (m inseg l <=> (m = l) \/ (?a. fld(l) a /\ (m = linseg l a)))"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"m:A->A->bool = l") THEN
    ASM_REWRITE_TAC [] THENL
     [REWRITE_TAC [inseg, ← REWRITE_RULE [IN] IN_FLD] THEN MESON_TAC [], ALL_TAC] THEN
    EQ_TAC THEN STRIP_TAC THENL [ALL_TAC, ASM_MESON_TAC [LINSEG_INSEG]] THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP WOSET_WELL_CONTRAPOS) THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"\x:A. fld(l) x /\ ~fld(m) x")) THEN
    REWRITE_TAC [] THEN REWRITE_TAC [linseg, ← GSYM PAIRED_EXT] THEN PBETA_TAC THEN
    subgoalLhand2 (fun t => REWRITE_TAC [t]) THENL
     [ASM_MESON_TAC [INSEG_PROPER_SUBSET_FLD], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "a:A") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q "a:A") THEN ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [INSEG_SUBSET, INSEG_SUBSET_FLD, ← REWRITE_RULE [IN] IN_FLD,
      WOSET_TOTAL_LE, properly, inseg])

  -- A proper initial segment can be extended by its bounding element.

  let EXTEND_FLD ← prove
   r"!(l:A->A->bool) x. woset l ==> (fld (\ x y. l x y /\ l y a) x <=> l x a)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← REWRITE_RULE [IN] IN_FLD] THEN PBETA_TAC THEN
    ASM_MESON_TAC [WOSET_TRANS, WOSET_REFL, ← REWRITE_RULE [IN] IN_FLD])

  let EXTEND_INSEG ← prove
   r"!(l:A->A->bool) a. woset l /\ fld(l) a ==> (\ x y. l x y /\ l y a) inseg l"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [inseg] THEN PBETA_TAC THEN
    REPEAT GEN_TAC THEN IMP_RES_THEN (fun t => REWRITE_TAC [t]) EXTEND_FLD)

  let EXTEND_LINSEG ← prove
   r"!(l:A->A->bool) a. woset l /\ fld(l) a ==>
       (\ x y. linseg l a  x y \/ (y = a) /\ (fld(linseg l a) x \/ (x = a)))
                inseg l"
   (REPEAT GEN_TAC THEN DISCH_THEN (fun th => STRIP_ASSUME_TAC th THEN
      tactic_of do pure (MP_TAC (← MATCH_MP EXTEND_INSEG th))) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN ONCE_REWRITE_TAC [← GSYM PAIRED_EXT] THEN PBETA_TAC THEN
    REPEAT GEN_TAC THEN IMP_RES_THEN (fun th => REWRITE_TAC [th]) LINSEG_FLD THEN
    REWRITE_TAC [linseg, properly] THEN ASM_MESON_TAC [WOSET_REFL])

  -- Key canonicality property of ordinals.

  let ORDINAL_CHAINED_LEMMA ← prove
   r"!(k:A->A->bool) l m.
        ordinal(l) /\ ordinal(m)
        ==> k inseg l /\ k inseg m
            ==> k = l \/ k = m \/ ?a. fld(l) a /\ fld(m) a /\
                                      k = linseg l a /\
                                      k = linseg m a"
   (← do
    let aFa ← ASSUME (← q r"fld(l) (a:A)")
    let aFb ← ASSUME (← q r"fld(m) (b:A)")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [ordinal] THEN STRIP_TAC THEN
      EVERY_ASSUM (fun th => TRY
        (tactic_of do pure (REWRITE_TAC [← MATCH_MP INSEG_LINSEG th]))) THEN
      ASM_CASES_TAC (← q r"k:A->A->bool = l") THEN ASM_REWRITE_TAC [] THEN
      ASM_CASES_TAC (← q r"k:A->A->bool = m") THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q "a:A") STRIP_ASSUME_TAC)
                                 (X_CHOOSE_THEN (← q "b:A") STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC (← q "a:A") THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q "a:A = b") (fun th => ASM_MESON_TAC [th]) THEN
      FIRST_ASSUM (fun th => tactic_of do pure (SUBST1_TAC (← MATCH_MP th aFa))) THEN
      FIRST_ASSUM (fun th => tactic_of do pure (SUBST1_TAC (← MATCH_MP th aFb))) THEN
      AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC (← q r"k = linseg m (b:A)") THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [linseg, ← GSYM PAIRED_EXT] THEN PBETA_TAC THEN
      ASM_MESON_TAC [WOSET_REFL, properly, ← REWRITE_RULE [IN] IN_FLD]))

  let ORDINAL_CHAINED ← prove
   r"!(l:A->A->bool) m. ordinal(l) /\ ordinal(m) ==> m inseg l \/ l inseg m"
   (← do
    let t ← TAUT (← q r"(a /\ b ==> a) /\ (a /\ b ==> b)")
    let aU ← ASSUME (← q r"(\x y. ?k. (k inseg l /\ k inseg m) /\ k x y) = linseg l (a:A)")
    let tl ← q r"l:A->A->bool"
    let tm ← q r"m:A->A->bool"
    pure (REPEAT GEN_TAC THEN
      DISCH_THEN (fun th => tactic_of do
        let b2 ← MATCH_MP ORDINAL_CHAINED_LEMMA th
        let b1 ← REWRITE_RULE [ordinal] th
        pure (STRIP_ASSUME_TAC b1 THEN ASSUME_TAC b2)) THEN
      MP_TAC (← SPEC (← q r"\k:A->A->bool. k inseg l /\ k inseg m") UNION_INSEG) THEN
      DISCH_THEN (fun th => tactic_of do
        let c2 ← SPEC tm th
        let c1 ← SPEC tl th
        pure (MP_TAC (← CONJ c1 c2))) THEN
      REWRITE_TAC [t] THEN
      DISCH_THEN (fun th => STRIP_ASSUME_TAC th THEN
                           FIRST_ASSUM (REPEAT_TCL DISJ_CASES_THEN MP_TAC o
                           (fun a => MATCH_MP a th))) THENL
       [ASM_MESON_TAC [], ASM_MESON_TAC [], ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "a:A") STRIP_ASSUME_TAC) THEN
      MP_TAC aU THEN
      CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN (fun _ => ALL_TAC) THEN
      REWRITE_TAC [FUN_EQ_THM] THEN DISCH_THEN (MP_TAC o SPECL [← q "a:A", ← q "a:A"]) THEN
      REWRITE_TAC [linseg] THEN PBETA_TAC THEN REWRITE_TAC [properly] THEN
      EXISTS_TAC
      (← q r"\x y. linseg l a x y \/ (y = a) /\ (fld(linseg l a) x \/ (x = a:A))") THEN
      PBETA_TAC THEN REWRITE_TAC [] THEN CONJ_TAC THENL
       [ALL_TAC,
        UNDISCH_TAC
         (← q r"(\x y. ?k. (k inseg l /\ k inseg m) /\ k x y) = linseg l (a:A)") THEN
        ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM)] THEN
      REWRITE_TAC [] THEN MATCH_MP_TAC EXTEND_LINSEG THEN ASM_REWRITE_TAC []))

  let ORDINAL_FLD_UNIQUE ← prove
   r"!l m:A->A->bool.
        ordinal l /\ ordinal m /\ fld l = fld m ==> l = m"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"l:A->A->bool", ← q r"m:A->A->bool"]
          ORDINAL_CHAINED) THEN
    REWRITE_TAC [inseg, FUN_EQ_THM, FORALL_PAIR_THM] THEN
    ASM_MESON_TAC [← REWRITE_RULE [IN] IN_FLD])

  let ORDINAL_FLD_SUBSET ← prove
   r"!l m:A->A->bool.
        ordinal l /\ ordinal m /\ fld l SUBSET fld m ==> l inseg m"
   (← do
    let m1 ← MESON [INSEG_REFL] (← q r"x = y ==> x inseg y")
    pure (REPEAT STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"l:A->A->bool", ← q r"m:A->A->bool"]
            ORDINAL_CHAINED) THEN
      ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
      MATCH_MP_TAC m1 THEN
      MATCH_MP_TAC ORDINAL_FLD_UNIQUE THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP INSEG_SUBSET_FLD) THEN ASM SET_TAC []))

  let ORDINAL_FLD_SUBSET_EQ ← prove
   r"!l m:A->A->bool.
        ordinal l /\ ordinal m ==> (fld l SUBSET fld m <=> l inseg m)"
   (MESON_TAC [ORDINAL_FLD_SUBSET, INSEG_FLD_SUBSET])

  -- Proof that any non-universe ordinal can be extended to its "successor".

  let FLD_SUC ← prove
   r"!(l:A->A->bool) a.
     fld(\ x y. l x y \/ (y = a) /\ (fld(l) x \/ (x = a))) x <=>
     fld(l) x \/ (x = a)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← REWRITE_RULE [IN] IN_FLD] THEN EQ_TAC THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN TRY DISJ1_TAC THEN
    ASM_MESON_TAC [])

  let ORDINAL_SUC ← prove
   r"!l:A->A->bool. ordinal(l) /\ (?x. ~(fld(l) x)) ==>
                 ordinal(\x y. l x y \/ (y = @y. ~fld(l) y) /\
                                           (fld(l) x \/ (x = @y. ~fld(l) y)))"
   (← do
    let t ← TAUT (← q r"a /\ b ==> b")
    let aSel ← ASSUME (← q r"(@y:A. ~fld(l) y) = a")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [ordinal] THEN
      DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
      ABBREV_TAC (← q r"a:A = @y. ~fld(l) y") THEN
      SUBGOAL_THEN (← q r"~fld(l:A->A->bool) a") ASSUME_TAC THENL
       [EXPAND_TAC "a" THEN CONV_TAC SELECT_CONV THEN
        ASM_REWRITE_TAC [], ALL_TAC] THEN
      PBETA_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC [WOSET, SUBSET, ← GSYM MEMBER_NOT_EMPTY, IN] THEN CONJ_TAC THENL
         [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THENL
           [ASM_MESON_TAC [WOSET_ANTISYM], ALL_TAC, ALL_TAC] THEN
          UNDISCH_TAC (← q r"~fld(l:A->A->bool) a") THEN CONV_TAC CONTRAPOS_CONV THEN
          DISCH_TAC THEN FIRST_ASSUM (undischCheck (fun c => pure (is_eq c))) THEN
          DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC [← REWRITE_RULE [IN] IN_FLD] THENL
           [EXISTS_TAC (← q "y:A"), EXISTS_TAC (← q "x:A")] THEN
          ASM_REWRITE_TAC [],
          X_GEN_TAC (← q r"P:A->bool") THEN REWRITE_TAC [FLD_SUC] THEN
          DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC (← q "w:A"))) THEN
          IMP_RES_THEN (MP_TAC o SPEC (← q r"\x:A. P x /\ fld(l) x")) WOSET_WELL THEN
          BETA_TAC THEN REWRITE_TAC [t] THEN
          ASM_CASES_TAC (← q r"?x:A. P x /\ fld(l) x") THEN ASM_REWRITE_TAC [] THENL
           [ASM_MESON_TAC [],
            FIRST_ASSUM (MP_TAC o SPEC (← q "w:A") o
              GEN_REWRITE_RULE id [NOT_EXISTS_THM]) THEN
            ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
            ASM_MESON_TAC []]],
        X_GEN_TAC (← q "z:A") THEN REWRITE_TAC [FLD_SUC, properly] THEN
        PBETA_TAC THEN DISCH_THEN DISJ_CASES_TAC THENL
         [UNDISCH_TAC (← q r"!x:A. fld l x ==> (x = (@y. ~properly l y x))") THEN
          DISCH_THEN (IMP_RES_THEN MP_TAC) THEN
          DISCH_THEN (fun th => GEN_REWRITE_TAC LAND_CONV [th]) THEN
          AP_TERM_TAC THEN GEN_REWRITE_TAC id [FUN_EQ_THM] THEN
          X_GEN_TAC (← q "y:A") THEN
          BETA_TAC THEN REWRITE_TAC [properly] THEN AP_TERM_TAC THEN
          ASM_CASES_TAC (← q "y:A = z") THEN ASM_REWRITE_TAC [] THEN
          EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
          UNDISCH_TAC (← q r"fld(l:A->A->bool) z") THEN ASM_REWRITE_TAC [],
          UNDISCH_TAC (← q "z:A = a") THEN DISCH_THEN SUBST_ALL_TAC THEN
          GEN_REWRITE_TAC LAND_CONV [← SYM aSel] THEN
          AP_TERM_TAC THEN GEN_REWRITE_TAC id [FUN_EQ_THM] THEN
          X_GEN_TAC (← q "y:A") THEN
          BETA_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [] THEN
          ASM_CASES_TAC (← q "y:A = a") THEN ASM_REWRITE_TAC [] THEN
          EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
          REWRITE_TAC [← REWRITE_RULE [IN] IN_FLD] THEN
          EXISTS_TAC (← q "a:A") THEN ASM_REWRITE_TAC []]]))

  -- @@RETURN BEGIN
  return { WOSET_TRANS_LE, WOSET_WELL_CONTRAPOS, WOSET_TOTAL_LE, WOSET_TOTAL_LT,
           ORDINAL_IMP_WOSET, WOSET_FINITE_TOSET, UNION_FLD, UNION_INSEG, INSEG_SUBSET,
           INSEG_SUBSET_FLD, INSEG_FLD_SUBSET, INSEG_WOSET, INSEG_ORDINAL, LINSEG_INSEG,
           LINSEG_WOSET, LINSEG_FLD, INSEG_PROPER_SUBSET, INSEG_PROPER_SUBSET_FLD,
           INSEG_LINSEG, EXTEND_FLD, EXTEND_INSEG, EXTEND_LINSEG, ORDINAL_CHAINED_LEMMA,
           ORDINAL_CHAINED, ORDINAL_FLD_UNIQUE, ORDINAL_FLD_SUBSET,
           ORDINAL_FLD_SUBSET_EQ, FLD_SUC, ORDINAL_SUC }
  -- @@RETURN END

/-- tactics.ml's NO_TAC. -/
def NO_TAC : tactic := HolCore.Tactics.NO_TAC

/-- lib.ml's `last` on a list of theorems. -/
def lastThm (l : List thm) : ExceptT String IO thm :=
  match l.getLast? with
  | some x => pure x
  | none => throw "last"

/- ------------------------------------------------------------------------- -/
/- The union of a set of ordinals is an ordinal; every type, and every set,  -/
/- can be wellordered; the ordinals are wellordered by "inseg".              -/
/- (wo.ml 1114-1374)                                                         -/
/- ------------------------------------------------------------------------- -/

structure WellOrder where
  -- @@FIELDS
  ORDINAL_UNION : thm
  ORDINAL_UNION_LEMMA : thm
  ORDINAL_UP : thm
  WO_ORDINAL : thm
  FLD_RESTRICT : thm
  WO : thm
  WF_INSEG_WOSET : thm
  WOSET_INSEG_ORDINAL : thm
  SUBWOSET_ISO_INSEG : thm
  deriving Inhabited

@[nospecialize]
def setupWellOrder [HolBase] (D : WoDeps) (BDefs : Defs) (BOrders : Orders) (BSegs : Segs) (BInseg : Inseg) :
    ExceptT String IO WellOrder := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON, MESON_TAC, SELECT_CONV, SET_TAC, .. } := D
  let { CONJ_ASSOC, EQ_IMP, FORALL_AND_THM, FORALL_UNWIND_THM2, FUN_EQ_THM, IMP_CONJ,
        IMP_CONJ_ALT, IMP_IMP, IN, IN_DIFF, IN_ELIM_THM, IN_IMAGE, IN_UNIV,
        LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM, MEMBER_NOT_EMPTY, MONO_EXISTS,
        MONO_FORALL, NOT_EXISTS_THM, NOT_FORALL_THM, NOT_IMP, RIGHT_FORALL_IMP_THM,
        RIGHT_IMP_EXISTS_THM, SKOLEM_THM, SUBSET, SWAP_EXISTS_THM, SWAP_FORALL_THM,
        UNIV, UNWIND_THM2, WF, WF_IND, WF_REC, WF_SUBSET, .. } := D.core1
  let { IN_FLD, PBETA_TAC, UNIONS_PRED, woset, .. } := BDefs
  let { WOSET, WOSET_WF, properly, .. } := BOrders
  let { INSEG_REFL, INSEG_TRANS, WOSET_ANTISYM, WOSET_REFL, WOSET_TOTAL, WOSET_WELL,
        inseg, ordinal, .. } := BSegs
  let { FLD_SUC, INSEG_LINSEG, INSEG_SUBSET, INSEG_SUBSET_FLD, LINSEG_FLD,
        LINSEG_INSEG, ORDINAL_CHAINED, ORDINAL_SUC, UNION_FLD, .. } := BInseg
  -- @@SCOPE END

  let ORDINAL_UNION ← prove
   r"!P. (!l:A->A->bool. P l ==> ordinal(l))
       ==> ordinal(\x y. ?l. P l /\ l x y)"
   (← do
    let t ← TAUT (← q r"a /\ b ==> a")
    pure (GEN_TAC THEN DISCH_TAC THEN
      REWRITE_TAC [ordinal, WOSET, SUBSET, ← GSYM MEMBER_NOT_EMPTY, IN] THEN
      REPEAT CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [← q "x:A", ← q "y:A"] THEN REWRITE_TAC [UNIONS_PRED] THEN
        BETA_TAC THEN DISCH_THEN (CONJUNCTS_THEN2
         (X_CHOOSE_THEN (← q r"l:A->A->bool") (CONJUNCTS_THEN2 (ANTE_RES_THEN ASSUME_TAC)
            ASSUME_TAC))
         (X_CHOOSE_THEN (← q r"m:A->A->bool") (CONJUNCTS_THEN2 (ANTE_RES_THEN ASSUME_TAC)
            ASSUME_TAC))) THEN
        MP_TAC (← SPECL [← q r"l:A->A->bool", ← q r"m:A->A->bool"] ORDINAL_CHAINED) THEN
        ASM_REWRITE_TAC [] THEN DISCH_THEN DISJ_CASES_TAC THENL
         [MP_TAC (← SPEC (← q r"l:A->A->bool") WOSET_ANTISYM),
          MP_TAC (← SPEC (← q r"m:A->A->bool") WOSET_ANTISYM)] THEN
        RULE_ASSUM_TAC (REWRITE_RULE [ordinal]) THEN
        ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC [] THEN IMP_RES_THEN MATCH_MP_TAC INSEG_SUBSET THEN
        ASM_REWRITE_TAC [],
        X_GEN_TAC (← q r"Q:A->bool") THEN REWRITE_TAC [UNION_FLD] THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC (← q "a:A"))) THEN
        MP_TAC (← ASSUME (← q r"!x:A. Q x ==> (?l. P l /\ fld l x)")) THEN
        DISCH_THEN (IMP_RES_THEN
          (X_CHOOSE_THEN (← q r"l:A->A->bool") STRIP_ASSUME_TAC)) THEN
        IMP_RES_THEN ASSUME_TAC (← ASSUME (← q r"!l:A->A->bool. P l ==> ordinal l")) THEN
        ASSUME_TAC (← CONJUNCT1
          (← REWRITE_RULE [ordinal] (← ASSUME (← q r"ordinal(l:A->A->bool)")))) THEN
        IMP_RES_THEN (MP_TAC o SPEC (← q r"\x:A. fld(l) x /\ Q x")) WOSET_WELL THEN
        BETA_TAC THEN REWRITE_TAC [t] THEN
        SUBGOAL_THEN (← q r"?x:A. fld(l) x /\ Q x") (fun th => REWRITE_TAC [th]) THENL
         [EXISTS_TAC (← q "a:A") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "b:A") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q "b:A") THEN ASM_REWRITE_TAC [] THEN
        X_GEN_TAC (← q "x:A") THEN DISCH_TAC THEN
        ANTE_RES_THEN MP_TAC (← ASSUME (← q r"(Q:A->bool) x")) THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"m:A->A->bool") STRIP_ASSUME_TAC) THEN
        ANTE_RES_THEN ASSUME_TAC (← ASSUME (← q r"(P:(A->A->bool)->bool) m")) THEN
        MP_TAC (← SPECL [← q r"l:A->A->bool", ← q r"m:A->A->bool"] ORDINAL_CHAINED) THEN
        ASM_REWRITE_TAC [UNIONS_PRED] THEN BETA_TAC THEN
        DISCH_THEN DISJ_CASES_TAC THENL
         [EXISTS_TAC (← q r"l:A->A->bool") THEN ASM_REWRITE_TAC [] THEN
          FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
          IMP_RES_THEN MATCH_MP_TAC INSEG_SUBSET_FLD THEN ASM_REWRITE_TAC [],
          EXISTS_TAC (← q r"m:A->A->bool") THEN ASM_REWRITE_TAC [] THEN
          FIRST_ASSUM (MP_TAC o SPECL [← q "x:A", ← q "b:A"] o REWRITE_RULE [inseg]) THEN
          ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o SYM) THEN
          IMP_RES_THEN (MP_TAC o SPEC (← q "b:A")) INSEG_SUBSET_FLD THEN
          ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
          MP_TAC (← CONJUNCT1 (← REWRITE_RULE [ordinal]
            (← ASSUME (← q r"ordinal(m:A->A->bool)")))) THEN
          DISCH_THEN (MP_TAC o SPECL [← q "b:A", ← q "x:A"] o MATCH_MP WOSET_TOTAL) THEN
          ASM_REWRITE_TAC [] THEN DISCH_THEN (DISJ_CASES_THEN MP_TAC) THEN
          ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
          IMP_RES_THEN MATCH_MP_TAC INSEG_SUBSET THEN
          FIRST_ASSUM MATCH_MP_TAC THEN
          ASM_REWRITE_TAC [← REWRITE_RULE [IN] IN_FLD] THEN
          EXISTS_TAC (← q "b:A") THEN ASM_REWRITE_TAC []],
        X_GEN_TAC (← q "x:A") THEN REWRITE_TAC [UNION_FLD] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"l:A->A->bool") STRIP_ASSUME_TAC) THEN
        MP_TAC (← ASSUME (← q r"!l:A->A->bool. P l ==> ordinal l")) THEN
        DISCH_THEN (IMP_RES_THEN MP_TAC) THEN REWRITE_TAC [ordinal] THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC (← q "x:A"))) THEN
        ASM_REWRITE_TAC [] THEN MATCH_MP_TAC EQ_IMP THEN
        REPEAT AP_TERM_TAC THEN GEN_REWRITE_TAC id [FUN_EQ_THM] THEN
        X_GEN_TAC (← q "y:A") THEN BETA_TAC THEN AP_TERM_TAC THEN
        ASM_CASES_TAC (← q "y:A = x") THEN ASM_REWRITE_TAC [properly, UNIONS_PRED] THEN
        BETA_TAC THEN EQ_TAC THEN DISCH_TAC THENL
         [EXISTS_TAC (← q r"l:A->A->bool") THEN ASM_REWRITE_TAC [],
          FIRST_ASSUM (X_CHOOSE_THEN (← q r"m:A->A->bool") STRIP_ASSUME_TAC) THEN
          SUBGOAL_THEN (← q r"ordinal(l:A->A->bool) /\ ordinal(m:A->A->bool)")
          MP_TAC THENL
           [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
            DISCH_THEN (DISJ_CASES_TAC o MATCH_MP ORDINAL_CHAINED)] THENL
           [IMP_RES_THEN MATCH_MP_TAC INSEG_SUBSET THEN ASM_REWRITE_TAC [],
            RULE_ASSUM_TAC (REWRITE_RULE [inseg]) THEN ASM_REWRITE_TAC []]]]))

  -- Consequently, every type can be wellordered (and by an ordinal).

  let ORDINAL_UNION_LEMMA ← prove
   r"!(l:A->A->bool) x.
      ordinal l ==> fld(l) x ==> fld(\a b. ?l. ordinal l /\ l a b) x"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [UNION_FLD] THEN
    EXISTS_TAC (← q r"l:A->A->bool") THEN ASM_REWRITE_TAC [])

  let ORDINAL_UP ← prove
   r"!l:A->A->bool. ordinal(l) ==> (!x. fld(l) x) \/
                          (?m x. ordinal(m) /\ fld(m) x /\ ~fld(l) x)"
   (← do
    let t ← TAUT (← q r"a \/ b <=> ~a ==> b")
    pure (GEN_TAC THEN DISCH_TAC THEN
      REWRITE_TAC [t] THEN
      GEN_REWRITE_TAC LAND_CONV [NOT_FORALL_THM] THEN DISCH_TAC THEN
      MP_TAC (← SPEC (← q r"l:A->A->bool") ORDINAL_SUC) THEN ASM_REWRITE_TAC [] THEN
      DISCH_TAC THEN MAP_EVERY EXISTS_TAC
       [← q r"\x y. l x y \/ (y = @y:A. ~fld l y) /\ (fld(l) x \/ (x = @y. ~fld l y))",
        ← q r"@y. ~fld(l:A->A->bool) y"] THEN
      ASM_REWRITE_TAC [FLD_SUC] THEN
      CONV_TAC SELECT_CONV THEN ASM_REWRITE_TAC []))

  let WO_ORDINAL ← prove
   r"?l:A->A->bool. ordinal(l) /\ !x. fld(l) x"
   (← do
    let t ← TAUT (← q r"a /\ (a ==> b) ==> a /\ b")
    pure (EXISTS_TAC (← q r"\a b:A. ?l. ordinal l /\ l a b") THEN
      MATCH_MP_TAC t THEN CONJ_TAC THENL
       [MATCH_MP_TAC ORDINAL_UNION THEN REWRITE_TAC [],
        DISCH_THEN (DISJ_CASES_TAC o MATCH_MP ORDINAL_UP) THEN
        ASM_REWRITE_TAC [] THEN POP_ASSUM (X_CHOOSE_THEN (← q r"m:A->A->bool")
         (X_CHOOSE_THEN (← q "x:A") STRIP_ASSUME_TAC)) THEN
        IMP_RES_THEN (IMP_RES_THEN MP_TAC) ORDINAL_UNION_LEMMA THEN
        ASM_REWRITE_TAC []]))

  -- At least -- every set can be wellordered.

  let FLD_RESTRICT ← prove
   r"!l. woset l ==>
       !P. fld(\x y:A. P x /\ P y /\ l x y) x <=> P x /\ fld(l) x"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← REWRITE_RULE [IN] IN_FLD] THEN EQ_TAC THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    TRY (EXISTS_TAC (← q "y:A") THEN ASM_REWRITE_TAC [] THEN NO_TAC) THEN
    EXISTS_TAC (← q "x:A") THEN ASM_REWRITE_TAC [] THEN
    IMP_RES_THEN MATCH_MP_TAC WOSET_REFL THEN
    REWRITE_TAC [← REWRITE_RULE [IN] IN_FLD] THEN EXISTS_TAC (← q "y:A") THEN
    ASM_REWRITE_TAC [])

  let WO ← prove
   r"!P. ?l:A->A->bool. woset l /\ (fld(l) = P)"
   (GEN_TAC THEN X_CHOOSE_THEN (← q r"l:A->A->bool") STRIP_ASSUME_TAC
     (← REWRITE_RULE [ordinal] WO_ORDINAL) THEN
    EXISTS_TAC (← q r"\x y:A. P x /\ P y /\ l x y") THEN
    REWRITE_TAC [WOSET, SUBSET, ← GSYM MEMBER_NOT_EMPTY, IN] THEN
    GEN_REWRITE_TAC RAND_CONV [FUN_EQ_THM] THEN
    FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP FLD_RESTRICT th])) THEN
    PBETA_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN DISCH_TAC THEN
      FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP WOSET_ANTISYM) THEN
      ASM_REWRITE_TAC [],
      X_GEN_TAC (← q r"Q:A->bool") THEN DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC) THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP WOSET_WELL) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"Q:A->bool")) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "y:A") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q "y:A") THEN ASM_REWRITE_TAC [] THEN GEN_TAC THEN DISCH_TAC THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC])

  -- Moreover, the ordinals themselves are wellordered by "inseg".

  let WF_INSEG_WOSET ← prove
   r"WF(\(x:A->A->bool) y. woset x /\ woset y /\ x inseg y /\ ~(x = y))"
   (← do
    let t3 ← TAUT (← q r"P /\ x = y <=> x = y /\ P")
    let t2 ← TAUT (← q r"~(p /\ q) <=> p ==> ~q")
    let m1 ← MESON [] (← q r"(?x. P x) <=> ~(!x. ~P x)")
    let lw ← q r"(l:(A->A->bool)->(A->A->bool)) w"
    let tw ← q r"w:A->A->bool"
    pure (REWRITE_TAC [WF] THEN X_GEN_TAC (← q r"P:(A->A->bool)->bool") THEN
      DISCH_TAC THEN
      ONCE_REWRITE_TAC [m1] THEN
      REWRITE_TAC [t2] THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [NOT_FORALL_THM] THEN
      REWRITE_TAC [NOT_IMP] THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"!x:A->A->bool. P x ==> woset x") ASSUME_TAC THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"!y. ?(a:A) z. P y ==> P z /\ fld y a /\ linseg y a = z")
      MP_TAC THENL
       [X_GEN_TAC (← q r"y:A->A->bool") THEN
        ASM_CASES_TAC (← q r"(P:(A->A->bool)->bool) y") THEN ASM_REWRITE_TAC [] THEN
        REPEAT (FIRST_X_ASSUM (MP_TAC o SPEC (← q r"y:A->A->bool"))) THEN
        ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [INSEG_LINSEG],
        ALL_TAC] THEN
      REWRITE_TAC [SKOLEM_THM, NOT_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC
       [← q r"a:(A->A->bool)->A", ← q r"l:(A->A->bool)->(A->A->bool)"] THEN
      DISCH_TAC THEN FIRST_X_ASSUM (X_CHOOSE_TAC (← q r"z:A->A->bool")) THEN
      SUBGOAL_THEN (← q r"woset(z:A->A->bool)") MP_TAC THENL
       [ASM_MESON_TAC [],
        REWRITE_TAC [woset, SUBSET, ← GSYM MEMBER_NOT_EMPTY, IN]] THEN
      REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"{(a:(A->A->bool)->A) x | P x /\ x inseg z}")) THEN
      REWRITE_TAC [IN_ELIM_THM] THEN
      REWRITE_TAC [t3] THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM, LEFT_AND_EXISTS_THM] THEN
      REWRITE_TAC [← GSYM CONJ_ASSOC] THEN
      ONCE_REWRITE_TAC [SWAP_EXISTS_THM, SWAP_FORALL_THM] THEN
      REWRITE_TAC [UNWIND_THM2, FORALL_UNWIND_THM2, IMP_CONJ,
                  RIGHT_FORALL_IMP_THM] THEN
      ONCE_REWRITE_TAC [SWAP_EXISTS_THM, SWAP_FORALL_THM] THEN
      REWRITE_TAC [UNWIND_THM2, FORALL_UNWIND_THM2, IMP_CONJ,
                  RIGHT_FORALL_IMP_THM, NOT_IMP] THEN
      CONJ_TAC THENL [ASM_MESON_TAC [INSEG_SUBSET_FLD], ALL_TAC] THEN
      CONJ_TAC THENL [ASM_MESON_TAC [INSEG_REFL], ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN tw MP_TAC) THEN
      REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN (MP_TAC o SPEC lw) THEN
      ASM_SIMP_TAC [NOT_IMP] THEN CONJ_TAC THENL
       [ASM_MESON_TAC [LINSEG_INSEG, INSEG_TRANS], DISCH_TAC] THEN
      FIRST_X_ASSUM (fun th => tactic_of do
        let b2 ← SPEC tw th
        let b1 ← SPEC lw th
        pure (MP_TAC b1 THEN MP_TAC b2)) THEN
      ASM_SIMP_TAC [] THEN REPEAT STRIP_TAC THEN
      UNDISCH_TAC (← q r"fld ((l:(A->A->bool)->(A->A->bool)) w) (a (l w))") THEN
      FIRST_X_ASSUM (fun th => tactic_of do
        pure (GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [← SYM th])) THEN
      ASM_SIMP_TAC [LINSEG_FLD, properly] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      RULE_ASSUM_TAC (REWRITE_RULE [inseg]) THEN ASM_MESON_TAC []))

  let WOSET_INSEG_ORDINAL ← prove
   r"woset (\(x:A->A->bool) y. ordinal x /\ ordinal y /\ x inseg y)"
   (REWRITE_TAC [WOSET_WF, IN, properly, ← REWRITE_RULE [IN] IN_FLD] THEN
    CONJ_TAC THENL [MESON_TAC [ORDINAL_CHAINED], ALL_TAC] THEN
    MATCH_MP_TAC (← MATCH_MP (← REWRITE_RULE [IMP_CONJ_ALT] WF_SUBSET)
          WF_INSEG_WOSET) THEN
    SIMP_TAC [ordinal])

  let SUBWOSET_ISO_INSEG ← prove
   r"!l s. woset l /\ fld l = (:A)
         ==> ?f. (!x y. x IN s /\ y IN s ==> (l(f x) (f y) <=> l x y)) /\
                 (!x y. y IN IMAGE f s /\ l x y ==> x IN IMAGE f s)"
   (← do
    let m1 ← MESON [] (← q r"(!x y. P x y /\ P y x ==> Q x y)
        ==> (!x y. P x y) ==> (!x y. Q x y)")
    let tdiff ← q r"(:A) DIFF IMAGE (f:A->A) {u | u IN s /\ properly l u x}"
    pure (REPEAT STRIP_TAC THEN
      FIRST_ASSUM (MP_TAC o (fun (th : thm) => lastThm (CONJUNCTS th)) o GEN_REWRITE_RULE id [woset]) THEN
      ASM_REWRITE_TAC [UNIV, MEMBER_NOT_EMPTY] THEN
      GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
      REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"m:(A->bool)->A") THEN DISCH_TAC THEN
      SUBGOAL_THEN
       (← q r"?f:A->A. !x. f(x) = m (UNIV DIFF IMAGE f {u | u IN s /\ properly l u x})")
      MP_TAC THENL
       [FIRST_ASSUM (MP_TAC o CONJUNCT2 o REWRITE_RULE [WOSET_WF, properly]) THEN
        DISCH_THEN (MATCH_MP_TAC o MATCH_MP WF_REC) THEN
        REWRITE_TAC [properly] THEN REPEAT STRIP_TAC THEN
        AP_TERM_TAC THEN ASM SET_TAC [],
        MATCH_MP_TAC MONO_EXISTS] THEN
      X_GEN_TAC (← q r"f:A->A") THEN DISCH_THEN (ASSUME_TAC o GSYM) THEN
      SUBGOAL_THEN (← q r"!x. x IN s ==> (l:A->A->bool)(f x) x") ASSUME_TAC THENL
       [FIRST_ASSUM (MP_TAC o CONJUNCT2 o REWRITE_RULE [WOSET_WF, properly]) THEN
        REWRITE_TAC [WF_IND] THEN DISCH_THEN MATCH_MP_TAC THEN
        X_GEN_TAC (← q "x:A") THEN REWRITE_TAC [IMP_IMP, ← GSYM CONJ_ASSOC] THEN
        STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC tdiff) THEN
        ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
         [REPEAT (POP_ASSUM MP_TAC) THEN
          REWRITE_TAC [properly, woset] THEN SET_TAC [],
          REWRITE_TAC [IN_DIFF, IN_IMAGE, IN_ELIM_THM, IN_UNIV] THEN
          DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MATCH_MP_TAC) THEN
          REPEAT (POP_ASSUM MP_TAC) THEN
          REWRITE_TAC [properly, woset] THEN SET_TAC []],
        ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o MATCH_MP MONO_FORALL o GEN (← q "x:A") o SPEC tdiff) THEN
      ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
       [REPEAT (POP_ASSUM MP_TAC) THEN REWRITE_TAC [properly, woset] THEN SET_TAC [],
        FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o CONV_RULE (BINDER_CONV SYM_CONV))] THEN
      REWRITE_TAC [IN_UNIV, IN_IMAGE, IN_DIFF, IN_ELIM_THM, FORALL_AND_THM] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN
       (← q r"!x z:A. x IN s /\ properly l z (f x)
                ==> ?u. u IN s /\ properly l u x /\ f u = z")
      ASSUME_TAC THENL
       [REPEAT (POP_ASSUM MP_TAC) THEN REWRITE_TAC [properly, woset] THEN SET_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"!x z:A. x IN s /\ l z (f x) ==> ?u. u IN s /\ l u x /\ f u = z")
      ASSUME_TAC THENL
       [REPEAT (POP_ASSUM MP_TAC) THEN REWRITE_TAC [properly, woset] THEN SET_TAC [],
        ALL_TAC] THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN
         (← q r"!x y:A. x IN s /\ y IN s /\ properly l x y ==> properly l (f x) (f y)")
        MP_TAC THENL
         [REPEAT STRIP_TAC THEN
          REPEAT (FIRST_X_ASSUM (MP_TAC o SPECL [← q "x:A", ← q r"(f:A->A) y"])) THEN
          REPEAT (POP_ASSUM MP_TAC) THEN
          REWRITE_TAC [properly, woset] THEN SET_TAC [],
          MATCH_MP_TAC m1 THEN
          REPEAT (POP_ASSUM MP_TAC) THEN REWRITE_TAC [properly, woset] THEN
          SET_TAC []],
        REPEAT (POP_ASSUM MP_TAC) THEN REWRITE_TAC [properly, woset] THEN
        SET_TAC []]))

  -- @@RETURN BEGIN
  return { ORDINAL_UNION, ORDINAL_UNION_LEMMA, ORDINAL_UP, WO_ORDINAL, FLD_RESTRICT, WO,
           WF_INSEG_WOSET, WOSET_INSEG_ORDINAL, SUBWOSET_ISO_INSEG }
  -- @@RETURN END

/-- `W(C SUBGOAL_THEN ttac o funpow 2 (fst o dest_imp) o snd)` -/
def subgoalAnte2 [HolBase] (ttac : thm_tactic) : tactic := fun gl => ExceptT.run do
  let t ← liftExcept (funpow 2 (fun (m : Except String term) => do
    pure (← dest_imp (← m)).1) (pure gl.2))
  ExceptT.mk (SUBGOAL_THEN t ttac gl)

/- ------------------------------------------------------------------------- -/
/- (3) Cantor-Zermelo ==> Hausdorff maximal principle; (4) ==> Zorn's lemma;  -/
/- (5) ==> Kuratowski's lemma; Zorn's lemma for the subset lattice.          -/
/- (wo.ml 1399-1655)                                                         -/
/- ------------------------------------------------------------------------- -/

structure Zorn where
  -- @@FIELDS
  HP : thm
  ZL_STRONG : thm
  ZL : thm
  KL_POSET_LEMMA : thm
  KL : thm
  POSET_RESTRICTED_SUBSET : thm
  FLD_RESTRICTED_SUBSET : thm
  ZL_SUBSETS : thm
  ZL_SUBSETS_UNIONS : thm
  ZL_SUBSETS_UNIONS_NONEMPTY : thm
  deriving Inhabited

@[nospecialize]
def setupZorn [HolBase] (D : WoDeps) (BDefs : Defs) (BOrders : Orders) (BSegs : Segs) (BInseg : Inseg) (BWellOrder : WellOrder) :
    ExceptT String IO Zorn := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, GEN_BETA_CONV, MESON_TAC, .. } := D
  let { COND_ID, DISJ_SYM, ETA_AX, EXTENSION, FORALL_PAIR_THM, FUN_EQ_THM, IN,
        IN_UNIONS, MONO_FORALL, MONO_IMP, NOT_EXISTS_THM, NOT_FORALL_THM, SUBSET,
        SUBSET_ANTISYM, SUBSET_REFL, SUBSET_TRANS, WF_REC, .. } := D.core1
  let { CHAIN_SUBSET, IN_FLD, PBETA_TAC, POSET_IMP_QOSET, QOSET_FLDEQ, QOSET_REFL,
        QOSET_TRANS, SUBSET_PRED, UNIONS_PRED, chain, poset, .. } := BDefs
  let { WOSET_WF, properly, .. } := BOrders
  let { POSET_ANTISYM, POSET_FLDEQ, WOSET_WELL, .. } := BSegs
  let { WOSET_TOTAL_LT, .. } := BInseg
  let { WO, .. } := BWellOrder
  -- @@SCOPE END

  let HP ← prove
   r"!l:A->A->bool.
        qoset l
        ==> ?P. chain(l) P /\ !Q. chain(l) Q  /\ P SUBSET Q ==> Q = P"
   (GEN_TAC THEN DISCH_TAC THEN
    X_CHOOSE_THEN (← q r"w:A->A->bool") MP_TAC (← SPEC (← q r"\x:A. T") WO) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    GEN_REWRITE_TAC LAND_CONV [FUN_EQ_THM] THEN BETA_TAC THEN
    REWRITE_TAC [] THEN DISCH_TAC THEN
    IMP_RES_THEN (MP_TAC o SPEC (← q r"\x:A. fld(l) x")) WOSET_WELL THEN
    BETA_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q r"?x:A. fld(l) x") THEN ASM_REWRITE_TAC [] THENL
     [DISCH_THEN (X_CHOOSE_THEN (← q "b:A") STRIP_ASSUME_TAC),
      FIRST_ASSUM (ASSUME_TAC o GEN_REWRITE_RULE id [NOT_EXISTS_THM]) THEN
      EXISTS_TAC (← q r"\x:A. F") THEN REWRITE_TAC [chain, IN, SUBSET_PRED] THEN
      GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [FUN_EQ_THM] THEN
      CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "u:A") MP_TAC o
        GEN_REWRITE_RULE id [NOT_FORALL_THM]) THEN
      REWRITE_TAC [] THEN DISCH_TAC THEN
      DISCH_THEN (MP_TAC o SPECL [← q "u:A", ← q "u:A"]) THEN
      IMP_RES_THEN (ASSUME_TAC o GSYM) QOSET_FLDEQ THEN ASM_REWRITE_TAC []] THEN
    SUBGOAL_THEN
      (← q r"?f. !x. f x = if fld(l) x /\
                        !y. properly w  y x ==> l x (f y) \/ l (f y) x
                     then (x:A) else b")
    (CHOOSE_TAC o GSYM) THENL
     [SUBGOAL_THEN (← q r"WF(\x:A y. (properly w) x y)") MP_TAC THENL
       [RULE_ASSUM_TAC (REWRITE_RULE [WOSET_WF]) THEN ASM_REWRITE_TAC [ETA_AX],
        DISCH_THEN (MATCH_MP_TAC o MATCH_MP WF_REC) THEN
        REWRITE_TAC [] THEN REPEAT GEN_TAC THEN
        REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
        ASM_MESON_TAC []], ALL_TAC] THEN
    IMP_RES_THEN (IMP_RES_THEN ASSUME_TAC) QOSET_REFL THEN
    SUBGOAL_THEN (← q r"(f:A->A) b = b") ASSUME_TAC THENL
     [FIRST_ASSUM (SUBST1_TAC o SYM o SPEC (← q "b:A")) THEN
      REWRITE_TAC [COND_ID] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!x:A. fld(l:A->A->bool) (f x)") ASSUME_TAC THENL
     [GEN_TAC THEN FIRST_ASSUM (SUBST1_TAC o SYM o SPEC (← q "x:A")) THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    FIRST_ASSUM (ANTE_RES_THEN (ASSUME_TAC o GEN_ALL) o SPEC_ALL) THEN
    SUBGOAL_THEN (← q r"!x:A. (l:A->A->bool) b (f x) \/ l (f x) b") ASSUME_TAC THENL
     [GEN_TAC THEN MP_TAC (← SPEC (← q "x:A")
        (← ASSUME (← q r"!x:A. (w:A->A->bool) b (f x)"))) THEN
      FIRST_ASSUM (SUBST1_TAC o SYM o SPEC (← q "x:A")) THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
      ASM_CASES_TAC (← q "x:A = b") THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"(properly w) (b:A) x") MP_TAC THENL
       [ASM_REWRITE_TAC [properly] THEN CONV_TAC (RAND_CONV SYM_CONV) THEN
        FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
      DISCH_THEN (fun th => FIRST_ASSUM (MP_TAC o (fun (a : thm) => MATCH_MP a th) o CONJUNCT2)) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN DISJ_CASES_TAC THEN
      ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!x y. l((f:A->A) x) (f y) \/ l(f y) (f x)") ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN
      IMP_RES_THEN (MP_TAC o SPECL [← q "x:A", ← q "y:A"]) WOSET_TOTAL_LT THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
       [ASM_REWRITE_TAC [] THEN IMP_RES_THEN MATCH_MP_TAC QOSET_REFL,
        ONCE_REWRITE_TAC [DISJ_SYM] THEN
        FIRST_ASSUM (SUBST1_TAC o SYM o SPEC (← q "y:A")),
        FIRST_ASSUM (SUBST1_TAC o SYM o SPEC (← q "x:A"))] THEN
      TRY COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
      FIRST_ASSUM (IMP_RES_THEN ACCEPT_TAC o CONJUNCT2), ALL_TAC] THEN
    EXISTS_TAC (← q r"\y:A. ?x:A. y = f(x)") THEN
    SUBGOAL_THEN (← q r"chain(l:A->A->bool)(\y. ?x:A. y = f x)") ASSUME_TAC THENL
     [REWRITE_TAC [chain, IN] THEN BETA_TAC THEN REPEAT GEN_TAC THEN
      DISCH_THEN (CONJUNCTS_THEN (CHOOSE_THEN SUBST1_TAC)), ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"Q:A->bool") THEN STRIP_TAC THEN
    GEN_REWRITE_TAC id [FUN_EQ_THM] THEN X_GEN_TAC (← q "z:A") THEN EQ_TAC THENL
     [DISCH_TAC THEN BETA_TAC THEN EXISTS_TAC (← q "z:A") THEN
      FIRST_ASSUM (SUBST1_TAC o SYM o SPEC (← q "z:A")) THEN
      SUBGOAL_THEN (← q r"fld(l:A->A->bool) z /\
                    !y. (properly w) y z ==> l z (f y) \/ l (f y) z")
      (fun th => REWRITE_TAC [th]) THEN CONJ_TAC THENL
       [UNDISCH_TAC (← q r"chain(l:A->A->bool) Q") THEN REWRITE_TAC [chain, IN] THEN
        DISCH_THEN (MP_TAC o SPECL [← q "z:A", ← q "z:A"]) THEN
        ASM_REWRITE_TAC [← REWRITE_RULE [IN] IN_FLD] THEN
        DISCH_TAC THEN EXISTS_TAC (← q "z:A") THEN ASM_REWRITE_TAC [],
        X_GEN_TAC (← q "y:A") THEN DISCH_TAC THEN
        UNDISCH_TAC (← q r"chain(l:A->A->bool) Q") THEN REWRITE_TAC [chain, IN] THEN
        DISCH_THEN (MP_TAC o SPECL [← q "z:A", ← q r"(f:A->A) y"]) THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
        FIRST_ASSUM (MATCH_MP_TAC o REWRITE_RULE [SUBSET_PRED]) THEN
        BETA_TAC THEN EXISTS_TAC (← q "y:A") THEN REFL_TAC],
      SPEC_TAC (← q "z:A", ← q "z:A") THEN ASM_REWRITE_TAC [← GSYM SUBSET_PRED]])

  -- (4) HAUSDORFF MAXIMAL PRINCIPLE ==> ZORN'S LEMMA
  -- The version for qosets (preorders) is proved first as ZL_STRONG.

  let ZL_STRONG ← prove
   r"!l:A->A->bool.
        qoset l /\
        (!c. chain(l) c ==> ?y. y IN fld(l) /\ !x. x IN c ==> l x y)
        ==> ?y. y IN fld(l) /\ !x. l y x ==> l x y"
   (REWRITE_TAC [IN] THEN GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM (X_CHOOSE_THEN (← q r"M:A->bool") STRIP_ASSUME_TAC o MATCH_MP HP) THEN
    UNDISCH_TAC (← q r"!c. chain(l:A->A->bool) c
                     ==> (?y. fld(l) y /\ !x. c x ==> l x y)") THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"M:A->bool")) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "m:A") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q "m:A") THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q "z:A") THEN
    DISCH_TAC THEN
    SUBGOAL_THEN (← q r"chain(l) (\x:A. M x \/ x = z)") MP_TAC THENL
     [REWRITE_TAC [chain, IN] THEN BETA_TAC THEN REPEAT GEN_TAC THEN
      DISCH_THEN (CONJUNCTS_THEN DISJ_CASES_TAC) THEN
      ASM_REWRITE_TAC [] THENL
       [UNDISCH_TAC (← q r"chain(l:A->A->bool) M") THEN REWRITE_TAC [chain, IN] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
        DISJ1_TAC THEN FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP QOSET_TRANS) THEN
        EXISTS_TAC (← q "m:A") THEN ASM_REWRITE_TAC [] THEN
        FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC,
        DISJ2_TAC THEN FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP QOSET_TRANS) THEN
        EXISTS_TAC (← q "m:A") THEN ASM_REWRITE_TAC [] THEN
        FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC,
        FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP QOSET_REFL) THEN
        REWRITE_TAC [← REWRITE_RULE [IN] IN_FLD] THEN EXISTS_TAC (← q "m:A") THEN
        ASM_REWRITE_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"M SUBSET (\x:A. M x \/ x = z)") MP_TAC THENL
     [REWRITE_TAC [SUBSET_PRED] THEN GEN_TAC THEN BETA_TAC THEN
      DISCH_THEN (fun th => REWRITE_TAC [th]), ALL_TAC] THEN
    ASM_MESON_TAC [])

  let ZL ← prove
   r"!l:A->A->bool.
        poset l /\
        (!P. chain(l) P ==> ?y. fld(l) y /\ !x. P x ==> l x y)
        ==> ?y. fld(l) y /\ !x. l y x ==> y = x"
   (GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← REWRITE_RULE [IN] (← ISPEC (← q r"l:A->A->bool") ZL_STRONG)) THEN
    ASM_SIMP_TAC [POSET_IMP_QOSET] THEN ASM_MESON_TAC [POSET_ANTISYM])

  -- (5) ZORN'S LEMMA ==> KURATOWSKI'S LEMMA

  let KL_POSET_LEMMA ← prove
   r"poset (\ c1 c2. C SUBSET c1 /\ c1 SUBSET c2 /\ chain(l:A->A->bool) c2)"
   (REWRITE_TAC [poset, IN] THEN PBETA_TAC THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC (← q r"P:A->bool") THEN REWRITE_TAC [← REWRITE_RULE [IN] IN_FLD] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"Q:A->bool") STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC [SUBSET_REFL] THENL
       [MATCH_MP_TAC CHAIN_SUBSET, MATCH_MP_TAC SUBSET_TRANS],
      GEN_TAC THEN X_GEN_TAC (← q r"Q:A->bool") THEN GEN_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SUBSET_TRANS,
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM] THEN
    TRY (EXISTS_TAC (← q r"Q:A->bool")) THEN ASM_REWRITE_TAC [])

  let KL ← prove
   r"!l:A->A->bool. poset l ==>
        !C. chain(l) C ==>
            ?P. (chain(l) P /\ C SUBSET P) /\
                (!R. chain(l) R /\ P SUBSET R ==> (R = P))"
   (← do
    let t ← TAUT (← q r"a /\ b /\ (a /\ b ==> c) ==> (a /\ b) /\ c")
    pure (REPEAT STRIP_TAC THEN
      MP_TAC (← ISPEC (← q r"\c1 c2. C SUBSET c1 /\ c1 SUBSET c2 /\
                              chain(l:A->A->bool) c2") ZL) THEN PBETA_TAC THEN
      REWRITE_TAC [KL_POSET_LEMMA, ← MATCH_MP POSET_FLDEQ KL_POSET_LEMMA] THEN
      PBETA_TAC THEN
      subgoalAnte2 (fun t => REWRITE_TAC [t]) THENL
       [X_GEN_TAC (← q r"P:(A->bool)->bool") THEN GEN_REWRITE_TAC LAND_CONV [chain] THEN
        REWRITE_TAC [IN] THEN
        PBETA_TAC THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"?D:A->bool. P D") THENL
         [EXISTS_TAC (← q r"UNIONS(P) :A->bool") THEN REWRITE_TAC [SUBSET_REFL] THEN
          FIRST_ASSUM (X_CHOOSE_TAC (← q r"D:A->bool")) THEN
          FIRST_ASSUM (MP_TAC o SPECL [← q r"D:A->bool", ← q r"D:A->bool"]) THEN
          REWRITE_TAC [← ASSUME (← q r"(P:(A->bool)->bool) D"), SUBSET_REFL] THEN
          STRIP_TAC THEN
          MATCH_MP_TAC t THEN
          REPEAT CONJ_TAC THENL
           [REWRITE_TAC [UNIONS_PRED, SUBSET_PRED] THEN REPEAT STRIP_TAC THEN
            BETA_TAC THEN EXISTS_TAC (← q r"D:A->bool") THEN ASM_REWRITE_TAC [] THEN
            FIRST_ASSUM (MATCH_MP_TAC o REWRITE_RULE [SUBSET_PRED]) THEN
            ASM_REWRITE_TAC [],
            REWRITE_TAC [chain, IN, UNIONS_PRED] THEN
            MAP_EVERY X_GEN_TAC [← q "x:A", ← q "y:A"] THEN
            BETA_TAC THEN DISCH_THEN (CONJUNCTS_THEN2
             (X_CHOOSE_TAC (← q r"A:A->bool")) (X_CHOOSE_TAC (← q r"B:A->bool"))) THEN
            FIRST_ASSUM (undischCheck (fun c => pure (is_forall c))) THEN
            DISCH_THEN (MP_TAC o SPECL [← q r"A:A->bool", ← q r"B:A->bool"]) THEN
            ASM_REWRITE_TAC [] THEN STRIP_TAC THENL
             [UNDISCH_TAC (← q r"chain(l:A->A->bool) B"),
              UNDISCH_TAC (← q r"chain(l:A->A->bool) A")] THEN
            REWRITE_TAC [chain, IN] THEN DISCH_THEN MATCH_MP_TAC THEN
            ASM_REWRITE_TAC [] THEN
            FIRST_ASSUM (MATCH_MP_TAC o REWRITE_RULE [SUBSET_PRED]) THEN
            ASM_REWRITE_TAC [],
            STRIP_TAC THEN X_GEN_TAC (← q r"X:A->bool") THEN DISCH_TAC THEN
            FIRST_ASSUM (MP_TAC o SPECL [← q r"X:A->bool", ← q r"X:A->bool"]) THEN
            REWRITE_TAC [] THEN DISCH_THEN (IMP_RES_THEN STRIP_ASSUME_TAC) THEN
            ASM_REWRITE_TAC [] THEN REWRITE_TAC [UNIONS_PRED, SUBSET_PRED] THEN
            REPEAT STRIP_TAC THEN BETA_TAC THEN EXISTS_TAC (← q r"X:A->bool") THEN
            ASM_REWRITE_TAC []],
          EXISTS_TAC (← q r"C:A->bool") THEN
          FIRST_ASSUM (ASSUME_TAC o GEN_REWRITE_RULE id [NOT_EXISTS_THM]) THEN
          ASM_REWRITE_TAC [SUBSET_REFL]],
        DISCH_THEN (X_CHOOSE_THEN (← q r"D:A->bool") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q r"D:A->bool") THEN ASM_REWRITE_TAC [] THEN
        REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []]))

  -- Special case of Zorn's Lemma for restriction of subset lattice.

  let POSET_RESTRICTED_SUBSET ← prove
   r"!P. poset(\x y. P(x) /\ P(y) /\ x SUBSET y)"
   (GEN_TAC THEN REWRITE_TAC [poset, IN, ← REWRITE_RULE [IN] IN_FLD] THEN
    CONV_TAC (ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC [SUBSET, EXTENSION] THEN MESON_TAC [])

  let FLD_RESTRICTED_SUBSET ← prove
   r"!P. fld(\ x y. P(x) /\ P(y) /\ x SUBSET y) = P"
   (REWRITE_TAC [← REWRITE_RULE [IN] IN_FLD, FORALL_PAIR_THM, FUN_EQ_THM] THEN
    CONV_TAC (ONCE_DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC [SUBSET_REFL])

  let ZL_SUBSETS ← prove
   r"!P. (!c. (!x. x IN c ==> P x) /\
            (!x y. x IN c /\ y IN c ==> x SUBSET y \/ y SUBSET x)
            ==> ?z. P z /\ (!x. x IN c ==> x SUBSET z))
       ==> ?a:A->bool. P a /\ (!x. P x /\ a SUBSET x ==> (a = x))"
   (GEN_TAC THEN
    MP_TAC (← ISPEC (← q r"\x y. P(x:A->bool) /\ P(y) /\ x SUBSET y") ZL) THEN
    REWRITE_TAC [POSET_RESTRICTED_SUBSET, FLD_RESTRICTED_SUBSET] THEN
    REWRITE_TAC [chain, IN] THEN
    CONV_TAC (ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC [IN] THEN MATCH_MP_TAC MONO_IMP THEN CONJ_TAC THENL
     [MATCH_MP_TAC MONO_FORALL, ALL_TAC] THEN
    MESON_TAC [])

  let ZL_SUBSETS_UNIONS ← prove
   r"!P. (!c. (!x. x IN c ==> P x) /\
            (!x y. x IN c /\ y IN c ==> x SUBSET y \/ y SUBSET x)
            ==> P(UNIONS c))
       ==> ?a:A->bool. P a /\ (!x. P x /\ a SUBSET x ==> (a = x))"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC ZL_SUBSETS THEN
    REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"UNIONS(c:(A->bool)->bool)") THEN
    ASM_MESON_TAC [SUBSET, IN_UNIONS])

  let ZL_SUBSETS_UNIONS_NONEMPTY ← prove
   r"!P. (?x. P x) /\
       (!c. (?x. x IN c) /\
            (!x. x IN c ==> P x) /\
            (!x y. x IN c /\ y IN c ==> x SUBSET y \/ y SUBSET x)
            ==> P(UNIONS c))
       ==> ?a:A->bool. P a /\ (!x. P x /\ a SUBSET x ==> (a = x))"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC ZL_SUBSETS THEN
    REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"?x:A->bool. x IN c") THENL
     [EXISTS_TAC (← q r"UNIONS(c:(A->bool)->bool)") THEN
      ASM_SIMP_TAC [] THEN MESON_TAC [SUBSET, IN_UNIONS],
      ASM_MESON_TAC []])

  -- @@RETURN BEGIN
  return { HP, ZL_STRONG, ZL, KL_POSET_LEMMA, KL, POSET_RESTRICTED_SUBSET,
           FLD_RESTRICTED_SUBSET, ZL_SUBSETS, ZL_SUBSETS_UNIONS,
           ZL_SUBSETS_UNIONS_NONEMPTY }
  -- @@RETURN END

/-- lib.ml's `el n` on a list of theorems. -/
def elThm (n : Nat) (l : List thm) : ExceptT String IO thm :=
  match l[n]? with
  | some x => pure x
  | none => throw "el"

/- ------------------------------------------------------------------------- -/
/- A form of Tukey's lemma; the order extension theorem (Abian's proof);     -/
/- every toset contains a cofinal woset.  (wo.ml 1657-1900)                  -/
/- ------------------------------------------------------------------------- -/

structure Tukey where
  -- @@FIELDS
  TUKEY : thm
  OEP : thm
  TOSET_COFINAL_WOSET : thm
  deriving Inhabited

@[nospecialize]
def setupTukey [HolBase] (D : WoDeps) (BDefs : Defs) (BOrders : Orders) (BSegs : Segs) (BInseg : Inseg) (BWellOrder : WellOrder) (BZorn : Zorn) :
    ExceptT String IO Tukey := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON, MESON_TAC, SELECT_CONV, SET_RULE, SET_TAC, .. } := D
  let { CONJ_ASSOC, CONTRAPOS_THM, EXISTS_IN_IMAGE, EXTENSION, FINITE_INDUCT_STRONG,
        FORALL_PAIR_THM, FUN_EQ_THM, IN, INJECTIVE_LEFT_INVERSE, INSERT_SUBSET,
        IN_ELIM_THM, IN_IMAGE, IN_UNIV, MEMBER_NOT_EMPTY, MONO_EXISTS, MONO_FORALL,
        NOT_EXISTS_THM, NOT_FORALL_THM, NOT_IMP, NOT_IN_EMPTY, OR_EXISTS_THM, SUBSET,
        SUBSET_ANTISYM, UNIV, WF_REC, .. } := D.core1
  let { IN_FLD, poset, woset, .. } := BDefs
  let { TOSET_POSET, WOSET_WF, properly, .. } := BOrders
  let { FLD_TRIVIAL, .. } := BSegs
  let { ORDINAL_IMP_WOSET, .. } := BInseg
  let { WO, WO_ORDINAL, .. } := BWellOrder
  let { ZL_SUBSETS_UNIONS_NONEMPTY, .. } := BZorn
  -- @@SCOPE END

  let TUKEY ← prove
   r"!s:(A->bool)->bool.
        ~(s = {}) /\
        (!t. (!c. FINITE c /\ c SUBSET t ==> c IN s) <=> t IN s)
        ==> ?u. u IN s /\ !v. v IN s /\ u SUBSET v ==> u = v"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC ZL_SUBSETS_UNIONS_NONEMPTY THEN
    CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    X_GEN_TAC (← q r"c:(A->bool)->bool") THEN
    DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC id [← GSYM th])) THEN
    SUBGOAL_THEN
     (← q r"!d. FINITE d ==> d SUBSET UNIONS c ==> ?e:A->bool. e IN c /\ d SUBSET e")
    MP_TAC THENL [ALL_TAC, MATCH_MP_TAC MONO_FORALL THEN ASM SET_TAC []] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC [INSERT_SUBSET] THEN ASM SET_TAC [])

  -- Also the order extension theorem, using Abian's proof.

  let OEP ← prove
   r"!p:A->A->bool.
     poset p ==> ?t. toset t /\ fld(t) = fld(p) /\ !x y. p x y ==> t x y"
   (← do
    let t ← TAUT (← q r"q /\ (q ==> p) ==> p /\ q")
    pure (REPEAT STRIP_TAC THEN
      MP_TAC (← ISPEC (← q r"fld(p:A->A->bool)") WO) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"w:A->A->bool") STRIP_ASSUME_TAC) THEN
      ABBREV_TAC
       (← q r"t = \(x:A) (y:A). fld p x /\ fld p y /\
                        (x = y \/
                         ?i. fld p i /\
                             (!j. w j i /\ ~(j = i) ==> (p j x <=> p j y)) /\
                             ~p i x /\ p i y)") THEN
      EXISTS_TAC (← q r"t:A->A->bool") THEN
      SUBGOAL_THEN
       (← q r"!x:A y:A. fld p x /\ fld p y /\ ~(x = y)
                  ==> ?i. fld p i /\
                          (!j:A. w j i /\ ~(j = i) ==> (p j x <=> p j y)) /\
                          ~(p i x <=> p i y)")
      (LABEL_TAC "*") THENL
       [REPEAT STRIP_TAC THEN
        FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE id [woset]) THEN ASM_SIMP_TAC [IN] THEN
        REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"\i:A. fld p i /\ ~(p i x <=> p i y)")) THEN
        ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
         [FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE id [poset]) THEN ASM SET_TAC [],
          MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q "i:A") THEN
           ASM_MESON_TAC [← REWRITE_RULE [IN] IN_FLD]],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"!x:A y:A. p x y ==> t x y") ASSUME_TAC THENL
       [EXPAND_TAC "t" THEN REWRITE_TAC [] THEN
        REPEAT GEN_TAC THEN STRIP_TAC THEN
        REPEAT (CONJ_TAC THENL
         [ASM_MESON_TAC [← REWRITE_RULE [IN] IN_FLD], ALL_TAC]) THEN
        ASM_CASES_TAC (← q "x:A = y") THENL
         [ASM_MESON_TAC [← REWRITE_RULE [IN] IN_FLD], ALL_TAC] THEN
        REMOVE_THEN "*" (MP_TAC o SPECL [← q "x:A", ← q "y:A"]) THEN ASM_SIMP_TAC [] THEN
        ANTS_TAC THENL
         [ASM_MESON_TAC [← REWRITE_RULE [IN] IN_FLD], MATCH_MP_TAC MONO_EXISTS] THEN
        FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE id [poset]) THEN ASM SET_TAC [],
        ALL_TAC] THEN
      ASM_REWRITE_TAC [SUBSET, FORALL_PAIR_THM, IN] THEN
      MATCH_MP_TAC t THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_ANTISYM THEN
        ASM_REWRITE_TAC [SUBSET, FORALL_PAIR_THM, IN] THEN
        EXPAND_TAC "t" THEN REWRITE_TAC [← REWRITE_RULE [IN] IN_FLD] THEN
        ASM_MESON_TAC [],
        DISCH_TAC THEN ASM_REWRITE_TAC [TOSET_POSET, poset, IN]] THEN
      EXPAND_TAC "t" THEN REWRITE_TAC [] THEN
      FIRST_X_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE id [poset]) THEN
      REWRITE_TAC [IN] THEN REPEAT CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [← q "x:A", ← q "y:A", ← q "z:A"] THEN
        ASM_CASES_TAC (← q "x:A = z") THEN ASM_REWRITE_TAC [] THEN SIMP_TAC [] THEN
        ASM_CASES_TAC (← q "y:A = z") THEN ASM_REWRITE_TAC [] THEN SIMP_TAC [] THEN
        ASM_CASES_TAC (← q "y:A = x") THEN ASM_REWRITE_TAC [] THEN SIMP_TAC [] THEN
        ASM_CASES_TAC (← q "fld p (x:A)") THEN ASM_REWRITE_TAC [] THEN
        ASM_CASES_TAC (← q "fld p (y:A)") THEN ASM_REWRITE_TAC [] THEN
        ASM_CASES_TAC (← q "fld p (z:A)") THEN ASM_REWRITE_TAC [] THEN
        DISCH_THEN (CONJUNCTS_THEN2
         (X_CHOOSE_THEN (← q "m:A") STRIP_ASSUME_TAC)
         (X_CHOOSE_THEN (← q "n:A") STRIP_ASSUME_TAC)) THEN
        FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE id [woset]) THEN
        REWRITE_TAC [SUBSET, ← GSYM MEMBER_NOT_EMPTY, IN] THEN
        REPLICATE_TAC 3 (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN (MP_TAC o SPECL [← q "m:A", ← q "n:A"] o CONJUNCT1) THEN
        ANTS_TAC THENL [ASM_MESON_TAC [← REWRITE_RULE [IN] IN_FLD], ALL_TAC] THEN
        STRIP_TAC THENL
         [EXISTS_TAC (← q "m:A"), EXISTS_TAC (← q "n:A")] THEN ASM_MESON_TAC [],
        MAP_EVERY X_GEN_TAC [← q "x:A", ← q "y:A"] THEN
        ASM_CASES_TAC (← q "y:A = x") THEN ASM_REWRITE_TAC [] THEN
        ASM_CASES_TAC (← q "fld p (x:A)") THEN ASM_REWRITE_TAC [] THEN
        ASM_CASES_TAC (← q "fld p (y:A)") THEN ASM_REWRITE_TAC [] THEN
        DISCH_THEN (CONJUNCTS_THEN2
         (X_CHOOSE_THEN (← q "m:A") STRIP_ASSUME_TAC)
         (X_CHOOSE_THEN (← q "n:A") STRIP_ASSUME_TAC)) THEN
        FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE id [woset]) THEN
        REWRITE_TAC [SUBSET, ← GSYM MEMBER_NOT_EMPTY, IN] THEN
        REPLICATE_TAC 3 (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN (MP_TAC o SPECL [← q "m:A", ← q "n:A"] o CONJUNCT1) THEN
        ASM_MESON_TAC [],
        MAP_EVERY X_GEN_TAC [← q "x:A", ← q "y:A"] THEN
        ASM_CASES_TAC (← q "y:A = x") THEN ASM_REWRITE_TAC [IN] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
        REMOVE_THEN "*" (MP_TAC o SPECL [← q "x:A", ← q "y:A"]) THEN
        ASM_REWRITE_TAC [OR_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
        MESON_TAC []]))

  -- Every toset contains a cofinal woset.

  let TOSET_COFINAL_WOSET ← prove
   r"!l. toset l
       ==> ?w. (!x y. w x y ==> l x y) /\ woset w /\
               !x:A. x IN fld l ==> ?y. y IN fld w /\ l x y"
   (← do
    -- Built when OCaml builds the tactic, last first.
    let s9 ← SET_RULE
     (← q r"(!z. P z ==> z IN IMAGE f s)
      ==> (!x. x IN s /\ P(f x) ==> Q(f x))
          ==> !y. P y ==> Q y")
    let s8 ← SET_RULE (← q r"fld l x <=> x IN fld l")
    let m7 ← MESON [] (← q r"~(f x = f y) ==> ~(x = y)")
    let m6 ← MESON [] (← q r"(l a b \/ l b a) /\ (~(b = a) ==> ~l b a) ==> l a b")
    let m5 ← MESON [] (← q r"(y = @x. P x) ==> (?x. P x) ==> P y")
    let m4 ← MESON [] (← q r"(!x y. P x y ==> P y x) /\ (!x y. R x y ==> P x y)
        ==> (!x y. R x y \/ R y x) ==> (!x y. P x y)")
    let t3 ← TAUT (← q r"~(p /\ q /\ r) <=> (p /\ q ==> ~r)")
    let m2 ← MESON [] (← q r"(?w. P w) <=> ~(!w. ~P w)")
    let m1 ← MESON [] (← q r"(p <=> p') /\ x' = x
          ==> (if p then x else a) = (if p' then x' else a)")
    pure (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"fld l:A->bool = {}") THENL
       [EXISTS_TAC (← q r"(\x y. F):A->A->bool") THEN
        ASM_REWRITE_TAC [woset, FLD_TRIVIAL, NOT_IN_EMPTY] THEN SET_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"?r. ordinal r /\ fld r = (:A->bool)") STRIP_ASSUME_TAC THENL
       [REWRITE_TAC [EXTENSION, IN_UNIV] THEN REWRITE_TAC [IN, WO_ORDINAL],
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"?f. !w. f w = if ?x:A. x IN fld l /\
                               !v:A->bool. r v w /\ ~(v = w) ==> ~l x (f v)
                      then @x:A. x IN fld l /\
                                 !v. r v w /\ ~(v = w) ==> ~l x (f v)
                      else @x:A. x IN fld l")
      STRIP_ASSUME_TAC THENL
       [FIRST_ASSUM (MP_TAC o MATCH_MP ORDINAL_IMP_WOSET) THEN
        REWRITE_TAC [WOSET_WF, properly] THEN
        DISCH_THEN (MATCH_MP_TAC o MATCH_MP WF_REC o CONJUNCT2) THEN
        REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC m1 THEN
        CONJ_TAC THENL [ALL_TAC, AP_TERM_TAC THEN ABS_TAC] THEN
        ASM_MESON_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"!w. (f:(A->bool)->A) w IN fld l")
      ASSUME_TAC THENL
       [GEN_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
        COND_CASES_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
        CONV_TAC SELECT_CONV THEN ASM_REWRITE_TAC [MEMBER_NOT_EMPTY],
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"?w:A->bool. (!x. x IN fld l ==> ?v. r v w /\ ~(v = w) /\ l (x:A) (f v)) /\
                    !z. (!x. x IN fld l ==> ?v. r v z /\ ~(v = z) /\ l x (f v))
                        ==> r w z")
      STRIP_ASSUME_TAC THENL
       [FIRST_ASSUM (MATCH_MP_TAC o (fun (th : thm) => lastThm (CONJUNCTS th)) o
            REWRITE_RULE [← REWRITE_RULE [SUBSET, ← GSYM MEMBER_NOT_EMPTY, IN] woset] o
            MATCH_MP ORDINAL_IMP_WOSET) THEN
        CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
        ONCE_REWRITE_TAC [m2] THEN
        GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [NOT_FORALL_THM] THEN
        REWRITE_TAC [NOT_IMP, NOT_EXISTS_THM, t3] THEN
        DISCH_TAC THEN
        SUBGOAL_THEN (← q r"!v w:A->bool. f v:A = f w ==> v = w") MP_TAC THENL
         [FIRST_ASSUM (MP_TAC o (fun (th : thm) => elThm 3 (CONJUNCTS th)) o
            REWRITE_RULE [← REWRITE_RULE [SUBSET, ← GSYM MEMBER_NOT_EMPTY, IN] woset] o
            MATCH_MP ORDINAL_IMP_WOSET) THEN
          FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC [UNIV] THEN
          MATCH_MP_TAC m4 THEN
          CONJ_TAC THENL [MESON_TAC [], ALL_TAC] THEN
          REPEAT GEN_TAC THEN DISCH_TAC THEN
          GEN_REWRITE_TAC id [← GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
          FIRST_X_ASSUM (fun t => GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [t]) THEN
          ASM_SIMP_TAC [] THEN DISCH_THEN (MP_TAC o MATCH_MP m5) THEN
          ASM_SIMP_TAC [] THEN RULE_ASSUM_TAC (REWRITE_RULE [TOSET_POSET]) THEN
          ASM_MESON_TAC [],
          REWRITE_TAC [INJECTIVE_LEFT_INVERSE, NOT_EXISTS_THM] THEN
          X_GEN_TAC (← q r"g:A->(A->bool)") THEN
          DISCH_THEN (MP_TAC o SPEC (← q r"\x:A. ~(g x x)")) THEN
          REWRITE_TAC [FUN_EQ_THM] THEN MESON_TAC []],
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"!x y. r x y /\ r y w /\ ~(y = w) ==> l((f:(A->bool)->A) x) (f y)")
      ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN
        MATCH_MP_TAC m6 THEN
        CONJ_TAC THENL
         [RULE_ASSUM_TAC (REWRITE_RULE [TOSET_POSET]) THEN ASM SET_TAC [],
          DISCH_THEN (ASSUME_TAC o MATCH_MP m7)] THEN
        FIRST_X_ASSUM (fun th =>
         GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [th]) THEN
        COND_CASES_TAC THENL
         [FIRST_X_ASSUM (MATCH_MP_TAC o CONJUNCT2 o SELECT_RULE) THEN
          ASM_REWRITE_TAC [],
          FIRST_ASSUM (MP_TAC o
            REWRITE_RULE [← REWRITE_RULE [SUBSET, ← GSYM MEMBER_NOT_EMPTY, IN] woset] o
            MATCH_MP ORDINAL_IMP_WOSET) THEN
          ASM_MESON_TAC []],
        ALL_TAC] THEN
      EXISTS_TAC (← q r"\x y. x IN IMAGE (f:(A->bool)->A) {v | r v w /\ ~(v = w)} /\
                        y IN IMAGE (f:(A->bool)->A) {v | r v w /\ ~(v = w)} /\
                        l x y") THEN
      SUBGOAL_THEN
       (← q r"fld(\ x y. x IN IMAGE (f:(A->bool)->A) {v | r v w /\ ~(v = w)} /\
                   y IN IMAGE (f:(A->bool)->A) {v | r v w /\ ~(v = w)} /\
                   l x y) =
        IMAGE f {v | r v w /\ ~(v = w)}")
      ASSUME_TAC THENL
       [GEN_REWRITE_TAC id [EXTENSION] THEN
        REWRITE_TAC [IN_ELIM_THM, IN_IMAGE] THEN
        REWRITE_TAC [IN, ← REWRITE_RULE [IN] IN_FLD] THEN
        RULE_ASSUM_TAC (REWRITE_RULE [TOSET_POSET]) THEN ASM_MESON_TAC [],
        ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [SIMP_TAC [SUBSET, FORALL_PAIR_THM, IN],
        ASM_REWRITE_TAC [← REWRITE_RULE [s8]
          (← REWRITE_RULE [SUBSET, ← GSYM MEMBER_NOT_EMPTY, IN] woset)],
        ASM_REWRITE_TAC [] THEN REWRITE_TAC [EXISTS_IN_IMAGE] THEN
        ASM SET_TAC []] THEN
      FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE id [TOSET_POSET]) THEN
      FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE id [poset]) THEN
      REWRITE_TAC [CONJ_ASSOC] THEN
      CONJ_TAC THENL [ASM SET_TAC [], SIMP_TAC []] THEN
      X_GEN_TAC (← q r"P:A->bool") THEN REWRITE_TAC [] THEN STRIP_TAC THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP ORDINAL_IMP_WOSET) THEN
      REWRITE_TAC [← REWRITE_RULE [SUBSET, ← GSYM MEMBER_NOT_EMPTY, IN] woset] THEN
      DISCH_THEN (MP_TAC o SPEC
        (← q r"\x:A->bool. (P:A->bool) (f x)") o (fun (th : thm) => lastThm (CONJUNCTS th))) THEN
      REWRITE_TAC [] THEN ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"z:A->bool") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"(f:(A->bool)->A) z") THEN
      CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP s9) THEN
      X_GEN_TAC (← q r"y:A->bool") THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC,
        ASM SET_TAC []]))

  -- @@RETURN BEGIN
  return { TUKEY, OEP, TOSET_COFINAL_WOSET }
  -- @@RETURN END

end HolLibrary.Wo
