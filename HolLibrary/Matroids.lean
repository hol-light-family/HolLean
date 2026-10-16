/- ========================================================================= -/
/- Axiomatic approach to independence. This is matroid-like but without      -/
/- any finiteness assumptions, closely following Pete Clark's "Field Theory" -/
/- notes (http://alpha.math.uga.edu/~pete/FieldTheory.pdf), section 11.4.    -/
/- ========================================================================= -/
/- File: HolLibrary/Matroids.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/matroids.ml`, by hand, in file order,
  in the style of HolLibrary/Card.lean and HolLibrary/Wo.lean (see there and
  HolMath/Base.lean for the conventions).  matroids.ml begins with
  `needs "Library/card.ml"`; card.ml's and wo.ml's theorems it uses are
  supplied via the CoreThms structures (SessionLibrary.Matroids fills them).
  Each section is a bundle (a `structure`) built by a `setup` function;
  SessionLibrary/Matroids.lean builds the bundles in order and exports every
  name under its HOL Light name.  The type `:A matroid` is made with
  `new_type_definition`, as HOL Light does.

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, SET_RULE, TAUT) they are bound first, in
  OCaml's order.
-/

import HolLibrary.Card

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

set_option maxRecDepth 8000

namespace HolLibrary.Matroids

-- @@COREFILL BEGIN
/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD1 AND_FORALL_THM CARD_CLAUSES CARD_DIFF CARD_LE_ANTISYM CARD_LE_CARD
   CARD_LE_FINITE CARD_LE_FINITE_INFINITE CARD_LE_IMAGE CARD_LE_SUBSET
   CARD_LE_TRANS CARD_LE_UNIONS CARD_PSUBSET CARD_SUBSET
   CHOOSE_SUBSET_BETWEEN CHOOSE_SUBSET_STRONG CONJ_ASSOC CONTRAPOS_THM
   DELETE_SUBSET EMPTY_SUBSET EQ_IMP EQ_IMP_LE FINITE_DIFF FINITE_EMPTY
   FINITE_INDUCT_STRONG FINITE_INSERT FINITE_RULES FINITE_SING FINITE_SUBSET
   FINITE_SUBSET_UNIONS_CHAIN FINITE_UNION FORALL_IN_GSPEC FORALL_IN_IMAGE
   FORALL_IN_INSERT FUN_EQ_THM HAS_SIZE IMP_CONJ IMP_CONJ_ALT IMP_IMP
   INFINITE INSERT_SUBSET INTERS_2 INTER_IDEMPOT INTER_SUBSET IN_DELETE
   IN_DIFF IN_INSERT LEFT_IMP_EXISTS_THM LE_ANTISYM LE_REFL LE_TRANS
   LTE_TRANS LT_REFL MONO_EXISTS NOT_IMP NOT_IN_EMPTY NOT_LT PAIR PAIR_EQ
   PSUBSET PSUBSET_ALT RIGHT_FORALL_IMP_THM RIGHT_IMP_EXISTS_THM SIMPLE_IMAGE
   SING_SUBSET SKOLEM_THM SUBSET SUBSET_ANTISYM SUBSET_ANTISYM_EQ SUBSET_DIFF : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (SUBSET_INTER SUBSET_INTERS SUBSET_REFL SUBSET_TRANS SUBSET_UNION SUB_ADD
   SWAP_FORALL_THM UNIONS_0 UNIONS_SUBSET UNION_COMM UNION_EMPTY UNION_SUBSET
   WF WF_PSUBSET ZL_SUBSETS_UNIONS_NONEMPTY : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms3 where
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms4 where
  deriving Inhabited

-- @@COREFILL END

/-- What matroids.ml uses from Session besides theorems. -/
structure MatroidsDeps where
  -- definitions and parser state
  new_definition : String → ExceptT String IO thm
  define : String → ExceptT String IO thm
  -- decision procedures and tactics
  ARITH_RULE : term → ExceptT String IO thm
  ASM_ARITH_TAC : tactic
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  ASM_MESON_TAC : List thm → tactic
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  -- type definitions (Session provides new_type_definition)
  new_type_definition : String → String × String → thm → ExceptT String IO thm
  -- (add fields here as needed, with a comment naming the HOL Light value)
  core1 : CoreThms1
  core2 : CoreThms2
  core3 : CoreThms3
  core4 : CoreThms4

/-- Destructure a list of six theorems. -/
def list6 (l : List thm) : ExceptT String IO (thm × thm × thm × thm × thm × thm) :=
  match l with
  | [a, b, c, d, e, f] => pure (a, b, c, d, e, f)
  | _ => throw "Match_failure"

/- ------------------------------------------------------------------------- -/
/- Basic finitary matroid type definition.                                   -/
/- ------------------------------------------------------------------------- -/

structure MatroidType where
  -- @@FIELDS
  matroid_tybij : thm
  matroid_set : thm
  matroid_span : thm
  MATROID_SPAN_SUBSET : thm
  MATROID_SPAN_SUPERSET : thm
  MATROID_SPAN_MONO : thm
  MATROID_SPAN_SPAN : thm
  MATROID_SPAN_FINITARY : thm
  MATROID_SPAN_EXCHANGE : thm
  MATROID_SPAN_INC : thm
  SUBSET_MATROID_SPAN : thm
  MATROID_SPAN_MINIMAL : thm
  MATROID_SPAN_SET : thm
  MATROID_SPAN_EQ : thm
  MATROID_SPAN_EQ_SET : thm
  MATROID_SPAN_SUBSET_EQ : thm
  MATROID_SPAN_INTER_SUBSET : thm
  MATROID_SPAN_UNION : thm
  MATROID_SPAN_UNION_LEFT : thm
  MATROID_SPAN_UNION_RIGHT : thm
  MATROID_SPAN_UNION_SUBSET : thm
  MATROID_SPAN_EXCHANGE_DELETE : thm
  MATROID_SPAN_UNION_EQ : thm
  MATROID_SPAN_INSERT_EQ : thm
  MATROID_SPAN_DELETE_EQ : thm
  MATROID_SPAN_TRANS : thm
  MATROID_SPAN_FINITARY_GEN : thm
  MATROID_SPAN_FINITARY_MINIMAL : thm
  deriving Inhabited

@[nospecialize]
def setupMatroidType [HolBase] (D : MatroidsDeps) :
    ExceptT String IO MatroidType := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, new_definition,
        new_type_definition, .. } := D
  let { CONJ_ASSOC, DELETE_SUBSET, EMPTY_SUBSET, FINITE_EMPTY, FINITE_INDUCT_STRONG,
        FINITE_SUBSET, FINITE_UNION, FUN_EQ_THM, IMP_CONJ, IMP_IMP, INSERT_SUBSET,
        LEFT_IMP_EXISTS_THM, MONO_EXISTS, RIGHT_FORALL_IMP_THM, SING_SUBSET, SUBSET,
        SUBSET_ANTISYM, SUBSET_ANTISYM_EQ, .. } := D.core1
  let { SUBSET_INTER, SUBSET_REFL, SUBSET_TRANS, SUBSET_UNION, UNION_SUBSET, WF,
        WF_PSUBSET, .. } := D.core2
  -- @@SCOPE END

  let matroid_tybij ← do
    let eth ← prove
     r"?m. (!s:A->bool. s SUBSET FST m ==> SND m s SUBSET FST m) /\
         (!s:A->bool. s SUBSET FST m ==> s SUBSET SND m s) /\
         (!s t. s SUBSET t /\ t SUBSET FST m ==> SND m s SUBSET SND m t) /\
         (!s. s SUBSET FST m ==> SND m (SND m s) = SND m s) /\
         (!s x. s SUBSET FST m /\ x IN SND m s
                ==> ?s'. FINITE s' /\ s' SUBSET s /\ x IN SND m (s')) /\
         (!s x y. s SUBSET FST m /\ x IN FST m /\
                  y IN SND m (x INSERT s) /\ ~(y IN SND m s)
                  ==> x IN SND m (y INSERT s))"
     (EXISTS_TAC (← q r"({}:A->bool,(\x:A->bool. x))") THEN SET_TAC [])
    new_type_definition "matroid" ("matroid", "dest_matroid") eth

  let matroid_set ← new_definition
   r"matroid_set:A matroid->A->bool = \m. FST(dest_matroid m)"

  let matroid_span ← new_definition
   r"matroid_span = \m:A matroid. SND(dest_matroid m)"

  let (MATROID_SPAN_SUBSET, MATROID_SPAN_SUPERSET, MATROID_SPAN_MONO,
       MATROID_SPAN_SPAN, MATROID_SPAN_FINITARY, MATROID_SPAN_EXCHANGE) ← do
    let rw ← [matroid_set, matroid_span].mapM (fun t => do
      REWRITE_RULE [] (← ONCE_REWRITE_RULE [FUN_EQ_THM] (← SYM t)))
    let big ← REWRITE_RULE ((← CONJUNCT1 matroid_tybij) :: rw)
      (← SPEC (← q r"dest_matroid(m:A matroid)") (← CONJUNCT2 matroid_tybij))
    let cjs ← (CONJUNCTS big).mapM (fun c => do GEN (← q r"m:A matroid") c)
    list6 cjs

  let MATROID_SPAN_INC ← prove
   r"!(m:A matroid) s x.
        s SUBSET matroid_set m /\ x IN s ==> x IN matroid_span m s"
   (MESON_TAC [MATROID_SPAN_SUPERSET, SUBSET])

  let SUBSET_MATROID_SPAN ← prove
   r"!(m:A matroid) s t.
        s SUBSET matroid_set m /\ t SUBSET matroid_set m
        ==> (matroid_span m s SUBSET matroid_span m t <=>
             s SUBSET matroid_span m t)"
   (MESON_TAC [MATROID_SPAN_MONO, MATROID_SPAN_SPAN, MATROID_SPAN_SUBSET,
               MATROID_SPAN_SUPERSET, SUBSET_TRANS])

  let MATROID_SPAN_MINIMAL ← prove
   r"!(m:A matroid) s t.
        t SUBSET matroid_set m /\
        s SUBSET matroid_span m t
        ==> matroid_span m s SUBSET matroid_span m t"
   (MESON_TAC [SUBSET_MATROID_SPAN, MATROID_SPAN_SUBSET, SUBSET_TRANS])

  let MATROID_SPAN_SET ← prove
   r"!(m:A matroid). matroid_span m (matroid_set m) = matroid_set m"
   (REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ] THEN
    MESON_TAC [MATROID_SPAN_SUPERSET, SUBSET_REFL, MATROID_SPAN_SUBSET])

  let MATROID_SPAN_EQ ← prove
   r"!(m:A matroid) s t.
        s SUBSET matroid_set m /\ t SUBSET matroid_set m
        ==> (matroid_span m s = matroid_span m t <=>
             s SUBSET matroid_span m t /\ t SUBSET matroid_span m s)"
   (SIMP_TAC [← GSYM SUBSET_ANTISYM_EQ, SUBSET_MATROID_SPAN])

  let MATROID_SPAN_EQ_SET ← prove
   r"!(m:A matroid) s.
        s SUBSET matroid_set m
        ==> (matroid_span m s = matroid_set m <=>
             matroid_set m SUBSET matroid_span m s)"
   (MESON_TAC [MATROID_SPAN_EQ, SUBSET_REFL, MATROID_SPAN_SET])

  let MATROID_SPAN_SUBSET_EQ ← prove
   r"!(m:A matroid) s t.
        s SUBSET t /\ t SUBSET matroid_set m
        ==> (matroid_span m s = matroid_span m t <=>
             t SUBSET matroid_span m s)"
   (MESON_TAC [MATROID_SPAN_EQ, SUBSET_TRANS, MATROID_SPAN_SUPERSET])

  let MATROID_SPAN_INTER_SUBSET ← prove
   r"!(m:A matroid) s t.
        s SUBSET matroid_set m /\ t SUBSET matroid_set m
        ==> matroid_span m (s INTER t) SUBSET
            matroid_span m s INTER matroid_span m t"
   (REWRITE_TAC [SUBSET_INTER] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MATROID_SPAN_MONO THEN ASM SET_TAC [])

  let MATROID_SPAN_UNION ← prove
   r"!(m:A matroid) s t.
        s SUBSET matroid_set m /\ t SUBSET matroid_set m
        ==> matroid_span m (s UNION t) =
            matroid_span m (matroid_span m s UNION matroid_span m t)"
   (← do
    let s1 ← SET_RULE (← q
     r"s SUBSET s' /\ t SUBSET t' ==> s UNION t SUBSET s' UNION t'")
    pure (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC MATROID_SPAN_MONO,
      MATCH_MP_TAC MATROID_SPAN_MINIMAL] THEN
    ASM_SIMP_TAC [MATROID_SPAN_SUPERSET, s1] THEN
    ASM_SIMP_TAC [UNION_SUBSET, MATROID_SPAN_SUBSET,
                 MATROID_SPAN_MONO, SUBSET_UNION]))

  let MATROID_SPAN_UNION_LEFT ← prove
   r"!(m:A matroid) s t.
        s SUBSET matroid_set m /\ t SUBSET matroid_set m
        ==> matroid_span m (s UNION t) =
            matroid_span m (matroid_span m s UNION t)"
   (ASM_MESON_TAC [MATROID_SPAN_UNION, MATROID_SPAN_SPAN, MATROID_SPAN_SUBSET])

  let MATROID_SPAN_UNION_RIGHT ← prove
   r"!(m:A matroid) s t.
        s SUBSET matroid_set m /\ t SUBSET matroid_set m
        ==> matroid_span m (s UNION t) =
            matroid_span m (s UNION matroid_span m t)"
   (ASM_MESON_TAC [MATROID_SPAN_UNION, MATROID_SPAN_SPAN, MATROID_SPAN_SUBSET])

  let MATROID_SPAN_UNION_SUBSET ← prove
   r"!(m:A matroid) s t.
        s SUBSET matroid_set m /\ t SUBSET matroid_set m
        ==> matroid_span m s UNION matroid_span m t SUBSET
            matroid_span m (s UNION t)"
   (REWRITE_TAC [UNION_SUBSET] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MATROID_SPAN_MONO THEN ASM SET_TAC [])

  let MATROID_SPAN_EXCHANGE_DELETE ← prove
   r"!(m:A matroid) a b s.
        s SUBSET matroid_set m /\
        b IN matroid_set m /\
        a IN matroid_span m s /\
        ~(a IN matroid_span m (s DELETE b))
        ==> b IN matroid_span m (a INSERT (s DELETE b))"
   (← do
    let s1 ← SET_RULE (← q r"x IN s ==> s SUBSET t ==> x IN t")
    pure (REPEAT STRIP_TAC THEN MATCH_MP_TAC MATROID_SPAN_EXCHANGE THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP s1) THEN
    MATCH_MP_TAC MATROID_SPAN_MONO THEN ASM SET_TAC []))

  let MATROID_SPAN_UNION_EQ ← prove
   r"!m s t:A->bool.
        s SUBSET matroid_set m /\ t SUBSET matroid_set m
        ==> (matroid_span m (s UNION t) = matroid_span m t <=>
             s SUBSET matroid_span m t)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"m:A matroid", ← q r"t:A->bool", ← q r"s UNION t:A->bool"]
          MATROID_SPAN_SUBSET_EQ) THEN
    ASM_REWRITE_TAC [UNION_SUBSET, SUBSET_UNION] THEN
    ASM_MESON_TAC [MATROID_SPAN_SUPERSET])

  let MATROID_SPAN_INSERT_EQ ← prove
   r"!(m:A matroid) s x.
        s SUBSET matroid_set m /\ x IN matroid_set m
        ==> (matroid_span m (x INSERT s) = matroid_span m s <=>
             x IN matroid_span m s)"
   (← do
    let s1 ← SET_RULE (← q r"x INSERT s = {x} UNION s")
    pure (ONCE_REWRITE_TAC [s1] THEN
    MESON_TAC [← GSYM SING_SUBSET, MATROID_SPAN_UNION_EQ]))

  let MATROID_SPAN_DELETE_EQ ← prove
   r"!(m:A matroid) s x.
        x IN s /\ s SUBSET matroid_set m
        ==> (matroid_span m (s DELETE x) = matroid_span m s <=>
             x IN matroid_span m (s DELETE x))"
   (← do
    let s1 ← SET_RULE (← q
     r"x IN s ==> (s SUBSET t <=> x IN t /\ s DELETE x SUBSET t)")
    pure (SIMP_TAC [MATROID_SPAN_SUBSET_EQ, DELETE_SUBSET] THEN
    ASM_MESON_TAC [MATROID_SPAN_SUPERSET, s1]))

  let MATROID_SPAN_TRANS ← prove
   r"!(m:A matroid) x y s.
        s SUBSET matroid_set m /\
        x IN matroid_span m s /\
        y IN matroid_span m (x INSERT s)
        ==> y IN matroid_span m s"
   (MESON_TAC [SUBSET, MATROID_SPAN_SUBSET, MATROID_SPAN_INSERT_EQ])

  let MATROID_SPAN_FINITARY_GEN ← prove
   r"!(m:A matroid) s k.
        s SUBSET matroid_set m /\
        FINITE k /\ k SUBSET matroid_span m s
        ==> exists s'. FINITE s' /\ s' SUBSET s /\ k SUBSET matroid_span m s'"
   (← do
    let s2 ← SET_RULE (← q r"x IN s ==> s SUBSET t ==> x IN t")
    pure (GEN_TAC THEN GEN_TAC THEN
    REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC [EMPTY_SUBSET, INSERT_SUBSET, IMP_IMP, ← GSYM CONJ_ASSOC] THEN
    CONJ_TAC THENL [MESON_TAC [FINITE_EMPTY, EMPTY_SUBSET], ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"k:A->bool"] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"t:A->bool") THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"m:A matroid", ← q r"s:A->bool", ← q r"x:A"] MATROID_SPAN_FINITARY) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"u:A->bool") THEN STRIP_TAC THEN
    EXISTS_TAC (← q r"t UNION u:A->bool") THEN
    ASM_REWRITE_TAC [FINITE_UNION, UNION_SUBSET] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP s2),
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP
       (← REWRITE_RULE [IMP_CONJ] SUBSET_TRANS))] THEN
    MATCH_MP_TAC MATROID_SPAN_MONO THEN ASM SET_TAC []))

  let MATROID_SPAN_FINITARY_MINIMAL ← prove
   r"!(m:A matroid) s x.
         s SUBSET matroid_set m /\
         x IN matroid_span m s
         ==> ?t. FINITE t /\ t SUBSET s /\ x IN matroid_span m t /\
                 !t'. t' PSUBSET t ==> ~(x IN matroid_span m t')"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"m:A matroid", ← q r"s:A->bool", ← q r"x:A"] MATROID_SPAN_FINITARY) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"u:A->bool") STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP WF_PSUBSET) THEN REWRITE_TAC [WF] THEN
    DISCH_THEN (MP_TAC o SPEC
      (← q r"\s. s SUBSET u /\ (x:A) IN matroid_span m s")) THEN
    REWRITE_TAC [] THEN
    ANTS_TAC THENL [ASM_MESON_TAC [SUBSET_REFL], MATCH_MP_TAC MONO_EXISTS] THEN
    GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC [FINITE_SUBSET], ASM SET_TAC []])

  -- @@RETURN BEGIN
  return { matroid_tybij, matroid_set, matroid_span, MATROID_SPAN_SUBSET,
           MATROID_SPAN_SUPERSET, MATROID_SPAN_MONO, MATROID_SPAN_SPAN,
           MATROID_SPAN_FINITARY, MATROID_SPAN_EXCHANGE, MATROID_SPAN_INC,
           SUBSET_MATROID_SPAN, MATROID_SPAN_MINIMAL, MATROID_SPAN_SET, MATROID_SPAN_EQ,
           MATROID_SPAN_EQ_SET, MATROID_SPAN_SUBSET_EQ, MATROID_SPAN_INTER_SUBSET,
           MATROID_SPAN_UNION, MATROID_SPAN_UNION_LEFT, MATROID_SPAN_UNION_RIGHT,
           MATROID_SPAN_UNION_SUBSET, MATROID_SPAN_EXCHANGE_DELETE,
           MATROID_SPAN_UNION_EQ, MATROID_SPAN_INSERT_EQ, MATROID_SPAN_DELETE_EQ,
           MATROID_SPAN_TRANS, MATROID_SPAN_FINITARY_GEN, MATROID_SPAN_FINITARY_MINIMAL }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Definitions of linear algebra notions in terms of span.                   -/
/- We build in the assumption that they are subsets of the overall set.      -/
/- ------------------------------------------------------------------------- -/

structure LinearNotions where
  -- @@FIELDS
  matroid_spanning : thm
  matroid_independent : thm
  matroid_basis : thm
  matroid_dependent : thm
  MATROID_SPANNING_IMP_SUBSET : thm
  MATROID_INDEPENDENT_IMP_SUBSET : thm
  MATROID_DEPENDENT_IMP_SUBSET : thm
  MATROID_BASIS_IMP_SUBSET : thm
  MATROID_SPANNING_ALT : thm
  MATROID_SPANNING_SET : thm
  MATROID_INDEPENDENT : thm
  MATROID_DEPENDENT : thm
  deriving Inhabited

@[nospecialize]
def setupLinearNotions [HolBase] (D : MatroidsDeps) (BMatroidType : MatroidType) :
    ExceptT String IO LinearNotions := do
  -- @@SCOPE BEGIN
  let { MESON_TAC, SET_TAC, define, new_definition, .. } := D
  let { SUBSET_REFL, .. } := D.core2
  let { MATROID_SPAN_EQ_SET, MATROID_SPAN_SET, .. } := BMatroidType
  -- @@SCOPE END

  let matroid_spanning ← new_definition
   r"matroid_spanning (m:A matroid) s <=>
        s SUBSET matroid_set m /\ matroid_span m s = matroid_set m"

  let matroid_independent ← new_definition
   r"matroid_independent (m:A matroid) s <=>
        s SUBSET matroid_set m /\
        !x. x IN s ==> ~(x IN matroid_span m (s DELETE x))"

  let matroid_basis ← new_definition
   r"matroid_basis (m:A matroid) s <=>
        matroid_spanning m s /\ matroid_independent m s"

  let matroid_dependent ← define
   r"matroid_dependent (m:A matroid) s <=>
        s SUBSET matroid_set m /\ ~matroid_independent m s"

  let MATROID_SPANNING_IMP_SUBSET ← prove
   r"!(m:A matroid) s. matroid_spanning m s ==> s SUBSET matroid_set m"
   (SIMP_TAC [matroid_spanning])

  let MATROID_INDEPENDENT_IMP_SUBSET ← prove
   r"!(m:A matroid) s. matroid_independent m s ==> s SUBSET matroid_set m"
   (SIMP_TAC [matroid_independent])

  let MATROID_DEPENDENT_IMP_SUBSET ← prove
   r"!(m:A matroid) s. matroid_dependent m s ==> s SUBSET matroid_set m"
   (SIMP_TAC [matroid_dependent])

  let MATROID_BASIS_IMP_SUBSET ← prove
   r"!(m:A matroid) s. matroid_basis m s ==> s SUBSET matroid_set m"
   (SIMP_TAC [matroid_basis, matroid_spanning])

  let MATROID_SPANNING_ALT ← prove
   r"!(m:A matroid) s.
        matroid_spanning m s <=>
        s SUBSET matroid_set m /\
        matroid_set m SUBSET matroid_span m s"
   (REWRITE_TAC [matroid_spanning] THEN MESON_TAC [MATROID_SPAN_EQ_SET])

  let MATROID_SPANNING_SET ← prove
   r"!(m:A matroid).
        matroid_spanning m (matroid_set m)"
   (SIMP_TAC [matroid_spanning, SUBSET_REFL, MATROID_SPAN_SET])

  let MATROID_INDEPENDENT ← prove
   r"!(m:A matroid) s.
        matroid_independent m s <=>
        s SUBSET matroid_set m /\ ~matroid_dependent m s"
   (REWRITE_TAC [matroid_dependent, matroid_independent] THEN SET_TAC [])

  let MATROID_DEPENDENT ← prove
   r"!(m:A matroid) s.
        matroid_dependent m s <=>
        s SUBSET matroid_set m /\
        ?x. x IN s /\ x IN matroid_span m (s DELETE x)"
   (REWRITE_TAC [matroid_dependent, matroid_independent] THEN SET_TAC [])

  -- @@RETURN BEGIN
  return { matroid_spanning, matroid_independent, matroid_basis, matroid_dependent,
           MATROID_SPANNING_IMP_SUBSET, MATROID_INDEPENDENT_IMP_SUBSET,
           MATROID_DEPENDENT_IMP_SUBSET, MATROID_BASIS_IMP_SUBSET, MATROID_SPANNING_ALT,
           MATROID_SPANNING_SET, MATROID_INDEPENDENT, MATROID_DEPENDENT }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Properties of independent sets (which in other formulations could         -/
/- be the matroid axioms).                                                   -/
/- ------------------------------------------------------------------------- -/

structure IndependentSets where
  -- @@FIELDS
  MATROID_INDEPENDENT_EMPTY : thm
  MATROID_INDEPENDENT_MONO : thm
  MATROID_INDEPENDENT_FINITARY : thm
  MATROID_DEPENDENT_FINITARY : thm
  MATROID_INDEPENDENT_INSERT : thm
  MATROID_SPAN_PSUBSET_INDEPENDENT : thm
  MATROID_SPAN_PSUBSET_EXPLICIT : thm
  MATROID_SPANNING_SUBSET_INDEPENDENT : thm
  MATROID_SPANNING_PSUBSET_INDEPENDENT : thm
  MATROID_MAXIMAL_INDEPENDENT_SUBSET_SPAN : thm
  MATROID_BASIS_EQ_MAXIMAL_INDEPENDENT : thm
  MATROID_BASIS_EQ_MINIMAL_SPANNING : thm
  MATROID_INDEPENDENT_CHAIN : thm
  MATROID_SPAN_CHAIN : thm
  MATROID_INTERMEDIATE_SPAN : thm
  MATROID_INTERMEDIATE_BASIS : thm
  MATROID_INDEPENDENT_EXTENDS_TO_BASIS : thm
  MATROID_BASIS_EXISTS : thm
  MATROID_SPANNING_CONTAINS_BASIS : thm
  MATROID_SPAN_DEPENDENCE : thm
  deriving Inhabited

@[nospecialize]
def setupIndependentSets [HolBase] (D : MatroidsDeps) (BMatroidType : MatroidType) (BLinearNotions : LinearNotions) :
    ExceptT String IO IndependentSets := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON, MESON_TAC, SET_RULE, SET_TAC, .. } := D
  let { CONJ_ASSOC, CONTRAPOS_THM, EMPTY_SUBSET, EQ_IMP, FINITE_INSERT,
        FINITE_SUBSET_UNIONS_CHAIN, FORALL_IN_GSPEC, FORALL_IN_INSERT, IMP_CONJ_ALT,
        INSERT_SUBSET, IN_INSERT, LEFT_IMP_EXISTS_THM, MONO_EXISTS, NOT_IMP,
        NOT_IN_EMPTY, PSUBSET_ALT, SUBSET, SUBSET_ANTISYM, SUBSET_ANTISYM_EQ, .. } := D.core1
  let { SUBSET_REFL, SUBSET_TRANS, UNIONS_0, UNIONS_SUBSET, UNION_EMPTY, UNION_SUBSET,
        ZL_SUBSETS_UNIONS_NONEMPTY, .. } := D.core2
  let { MATROID_SPAN_DELETE_EQ, MATROID_SPAN_EXCHANGE, MATROID_SPAN_FINITARY,
        MATROID_SPAN_INC, MATROID_SPAN_MINIMAL, MATROID_SPAN_MONO, MATROID_SPAN_SET,
        MATROID_SPAN_SUBSET, MATROID_SPAN_SUPERSET, SUBSET_MATROID_SPAN, .. } := BMatroidType
  let { MATROID_INDEPENDENT_IMP_SUBSET, MATROID_SPANNING_IMP_SUBSET,
        MATROID_SPANNING_SET, matroid_basis, matroid_dependent, matroid_independent,
        matroid_spanning, .. } := BLinearNotions
  -- @@SCOPE END

  let MATROID_INDEPENDENT_EMPTY ← prove
   r"!m:A matroid. matroid_independent m {}"
   (REWRITE_TAC [matroid_independent, NOT_IN_EMPTY, EMPTY_SUBSET])

  let MATROID_INDEPENDENT_MONO ← prove
   r"!(m:A matroid) s t.
        matroid_independent m t /\ s SUBSET t ==> matroid_independent m s"
   (REPEAT GEN_TAC THEN REWRITE_TAC [matroid_independent] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:A")) THEN
    MP_TAC (← ISPECL
     [← q r"m:A matroid", ← q r"s DELETE (x:A)", ← q r"t DELETE (x:A)"] MATROID_SPAN_MONO) THEN
    ASM SET_TAC [])

  let MATROID_INDEPENDENT_FINITARY ← prove
   r"!(m:A matroid) s.
        matroid_independent m s <=>
        s SUBSET matroid_set m /\
        !t. FINITE t /\ t SUBSET s ==> matroid_independent m t"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [ASM_MESON_TAC [MATROID_INDEPENDENT_MONO, MATROID_INDEPENDENT_IMP_SUBSET],
      ASM_REWRITE_TAC [matroid_independent] THEN STRIP_TAC] THEN
    ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"x:A") THEN REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL
     [← q r"m:A matroid", ← q r"s DELETE (x:A)", ← q r"x:A"] MATROID_SPAN_FINITARY) THEN
    ANTS_TAC THENL [ASM SET_TAC [], REWRITE_TAC [LEFT_IMP_EXISTS_THM]] THEN
    X_GEN_TAC (← q r"t:A->bool") THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"(x:A) INSERT t")) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC [FINITE_INSERT] THEN ASM SET_TAC [],
      DISCH_THEN (MP_TAC o SPEC (← q r"x:A") o CONJUNCT2)] THEN
    ASM_REWRITE_TAC [IN_INSERT, CONTRAPOS_THM] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC [])

  let MATROID_DEPENDENT_FINITARY ← prove
   r"!(m:A matroid) s.
         matroid_dependent m s <=>
         s SUBSET matroid_set m /\
         ?t. FINITE t /\ t SUBSET s /\ matroid_dependent m t"
   (REPEAT GEN_TAC THEN REWRITE_TAC [matroid_dependent] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [MATROID_INDEPENDENT_FINITARY] THEN
    SET_TAC [])

  let MATROID_INDEPENDENT_INSERT ← prove
   r"!(m:A matroid) s a.
        matroid_independent m (a INSERT s) <=>
        if a IN s then matroid_independent m s
        else a IN matroid_set m /\
             matroid_independent m s /\
             ~(a IN matroid_span m s)"
   (← do
    let s4 ← SET_RULE (← q r"b IN s ==> b INSERT (s DELETE b) = s")
    let s3 ← SET_RULE
     (← q r"~(a IN s) /\ ~(b = a)
     ==> ((a INSERT s) DELETE b = a INSERT (s DELETE b))")
    let s2b ← SET_RULE (← q r"~(a IN s) ==> (a INSERT s) DELETE a = s")
    let s2a ← SET_RULE (← q r"s SUBSET t ==> a IN s ==> a IN t")
    let s1c ← SET_RULE (← q
     r"(!x. p x ==> (q x <=> r x))
      ==> ((!x. p x ==> ~q x) <=> (!x. p x ==> ~r x))")
    let t1 ← TAUT (← q r"(~p /\ q <=> q' /\ ~p) <=> ~p ==> (q <=> q')")
    let s1b ← SET_RULE (← q r"~(a IN s) ==> (a INSERT s) DELETE a = s")
    let s1a ← SET_RULE (← q r"a IN s ==> a INSERT s = s")
    pure (REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [s1a] THEN
    REWRITE_TAC [matroid_independent, INSERT_SUBSET, FORALL_IN_INSERT] THEN
    ASM_CASES_TAC (← q r"(a:A) IN matroid_set m") THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q r"(s:A->bool) SUBSET matroid_set m") THEN ASM_REWRITE_TAC [] THEN
    ASM_SIMP_TAC [s1b] THEN
    REWRITE_TAC [t1] THEN
    DISCH_TAC THEN MATCH_MP_TAC s1c THEN
    X_GEN_TAC (← q r"b:A") THEN DISCH_TAC THEN EQ_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC s2a THEN
      MATCH_MP_TAC MATROID_SPAN_MONO THEN ASM SET_TAC []] THEN
    ASM_CASES_TAC (← q r"b:A = a") THEN
    ASM_SIMP_TAC [s2b] THEN
    ASM_SIMP_TAC [s3] THEN
    MP_TAC (← ISPECL [← q r"m:A matroid", ← q r"s DELETE (b:A)", ← q r"a:A", ← q r"b:A"]
          MATROID_SPAN_EXCHANGE) THEN
    ASM_SIMP_TAC [s4] THEN
    ASM SET_TAC []))

  let MATROID_SPAN_PSUBSET_INDEPENDENT ← prove
   r"!(m:A matroid) s t.
        s PSUBSET t /\ matroid_independent m t
        ==> matroid_span m s PSUBSET matroid_span m t"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [PSUBSET_ALT]) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN (← q r"x:A") STRIP_ASSUME_TAC)) THEN
    FIRST_ASSUM (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC (← q r"x:A")) o
      GEN_REWRITE_RULE I [matroid_independent]) THEN
    ASM_SIMP_TAC [PSUBSET_ALT, MATROID_SPAN_MONO] THEN
    DISCH_TAC THEN EXISTS_TAC (← q r"(x:A)") THEN
    MP_TAC (← SPECL [← q r"m:A matroid", ← q r"s:A->bool", ← q r"t DELETE (x:A)"]
          MATROID_SPAN_MONO) THEN
    ASM SET_TAC [MATROID_SPAN_INC])

  let MATROID_SPAN_PSUBSET_EXPLICIT ← prove
   r"!(m:A matroid) s t.
        s PSUBSET t /\ matroid_independent m t
        ==> ?a. a IN t /\ ~(a IN matroid_span m s)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"m:A matroid", ← q r"s:A->bool", ← q r"t:A->bool"]
          MATROID_SPAN_PSUBSET_INDEPENDENT) THEN
    MP_TAC (← ISPECL [← q r"m:A matroid", ← q r"t:A->bool", ← q r"s:A->bool"]
      SUBSET_MATROID_SPAN) THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP MATROID_INDEPENDENT_IMP_SUBSET) THEN
    ASM SET_TAC [])

  let MATROID_SPANNING_SUBSET_INDEPENDENT ← prove
   r"!(m:A matroid) s t.
        t SUBSET s /\ matroid_independent m s /\ s SUBSET matroid_span m t
        ==> s = t"
   (SIMP_TAC [← GSYM SUBSET_ANTISYM_EQ] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [matroid_independent]) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC (← q r"a:A"))) THEN
    MP_TAC (← ISPECL [← q r"m:A matroid", ← q r"t:A->bool", ← q r"s DELETE (a:A)"]
      MATROID_SPAN_MONO) THEN
    ASM SET_TAC [])

  let MATROID_SPANNING_PSUBSET_INDEPENDENT ← prove
   r"!(m:A matroid) s t.
        ~(s PSUBSET t /\ matroid_spanning m s /\ matroid_independent m t)"
   (← do
    let s1 ← SET_RULE (← q r"s SUBSET t ==> ~(t PSUBSET s)")
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"m:A matroid", ← q r"s:A->bool", ← q r"t:A->bool"]
          MATROID_SPAN_PSUBSET_INDEPENDENT) THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC s1 THEN
    ASM_MESON_TAC [MATROID_SPAN_SUBSET, matroid_spanning, matroid_independent]))

  let MATROID_MAXIMAL_INDEPENDENT_SUBSET_SPAN ← prove
   r"!(m:A matroid) s t.
        s SUBSET t /\ t SUBSET matroid_set m /\
        matroid_independent m s /\
        (!s'. s PSUBSET s' /\ s' SUBSET t ==> ~matroid_independent m s')
        ==> matroid_span m s = matroid_span m t"
   (← do
    let s1 ← SET_RULE (← q r"s PSUBSET x INSERT s <=> ~(x IN s)")
    pure (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP MATROID_INDEPENDENT_IMP_SUBSET) THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_SIMP_TAC [MATROID_SPAN_MONO] THEN
    ASM_SIMP_TAC [SUBSET_MATROID_SPAN] THEN
    REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"(x:A) INSERT s")) THEN
    ASM_REWRITE_TAC [MATROID_INDEPENDENT_INSERT] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [s1] THEN
    ASM_MESON_TAC [SUBSET, INSERT_SUBSET, MATROID_SPAN_SUPERSET]))

  let MATROID_BASIS_EQ_MAXIMAL_INDEPENDENT ← prove
   r"!(m:A matroid) s.
        matroid_basis m s <=>
        matroid_independent m s /\
        !s'. s PSUBSET s' ==> ~matroid_independent m s'"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [ASM_MESON_TAC [MATROID_SPANNING_PSUBSET_INDEPENDENT, matroid_basis],
      STRIP_TAC THEN ASM_REWRITE_TAC [matroid_basis]] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP MATROID_INDEPENDENT_IMP_SUBSET) THEN
    ASM_REWRITE_TAC [matroid_spanning] THEN
    ONCE_REWRITE_TAC [← GSYM MATROID_SPAN_SET] THEN
    MATCH_MP_TAC MATROID_MAXIMAL_INDEPENDENT_SUBSET_SPAN THEN
    ASM_SIMP_TAC [SUBSET_REFL])

  let MATROID_BASIS_EQ_MINIMAL_SPANNING ← prove
   r"!(m:A matroid) s.
        matroid_basis m s <=>
        matroid_spanning m s /\
        !s'. s' PSUBSET s ==> ~matroid_spanning m s'"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [ASM_MESON_TAC [MATROID_SPANNING_PSUBSET_INDEPENDENT, matroid_basis],
      STRIP_TAC THEN ASM_REWRITE_TAC [matroid_basis]] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP MATROID_SPANNING_IMP_SUBSET) THEN
    ASM_REWRITE_TAC [matroid_independent] THEN
    X_GEN_TAC (← q r"x:A") THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"s DELETE (x:A)")) THEN
    REWRITE_TAC [matroid_spanning, NOT_IMP] THEN
    REPEAT (CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC]) THEN
    ASM_MESON_TAC [MATROID_SPAN_DELETE_EQ, matroid_spanning])

  let MATROID_INDEPENDENT_CHAIN ← prove
   r"!(m:A matroid) c.
        (!s. s IN c ==> matroid_independent m s) /\
        (!s t. s IN c /\ t IN c ==> s SUBSET t \/ t SUBSET s)
        ==> matroid_independent m (UNIONS c)"
   (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"c:(A->bool)->bool = {}") THEN
    ASM_REWRITE_TAC [UNIONS_0, MATROID_INDEPENDENT_EMPTY] THEN
    ONCE_REWRITE_TAC [MATROID_INDEPENDENT_FINITARY] THEN CONJ_TAC THENL
     [RULE_ASSUM_TAC (REWRITE_RULE [matroid_independent]) THEN ASM SET_TAC [],
      X_GEN_TAC (← q r"s:A->bool") THEN STRIP_TAC] THEN
    MP_TAC (← ISPECL [← q r"c:(A->bool)->bool", ← q r"s:A->bool"]
      FINITE_SUBSET_UNIONS_CHAIN) THEN
    ASM_MESON_TAC [MATROID_INDEPENDENT_MONO])

  let MATROID_SPAN_CHAIN ← prove
   r"!(m:A matroid) c.
        ~(c = {}) /\
        (!s. s IN c ==> s SUBSET matroid_set m) /\
        (!s t. s IN c /\ t IN c ==> s SUBSET t \/ t SUBSET s)
        ==> matroid_span m (UNIONS c) = UNIONS {matroid_span m s | s IN c}"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"a:A") THEN DISCH_TAC,
      REWRITE_TAC [UNIONS_SUBSET, FORALL_IN_GSPEC] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MATROID_SPAN_MONO THEN
      ASM SET_TAC []] THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ_ALT]
          MATROID_SPAN_FINITARY)) THEN
    ASM_REWRITE_TAC [UNIONS_SUBSET] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"t:A->bool") STRIP_ASSUME_TAC) THEN
    MP_TAC (← ISPECL [← q r"c:(A->bool)->bool", ← q r"t:A->bool"]
      FINITE_SUBSET_UNIONS_CHAIN) THEN
    ASM SET_TAC [MATROID_SPAN_MONO])

  let MATROID_INTERMEDIATE_SPAN ← prove
   r"!(m:A matroid) s t.
        matroid_independent m s /\
        t SUBSET matroid_set m /\
        s SUBSET matroid_span m t
        ==> ?b. s SUBSET b /\ b SUBSET (s UNION t) /\
                matroid_independent m b /\
                matroid_span m b = matroid_span m t"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"\u:A->bool. s SUBSET u /\ u SUBSET (s UNION t) /\
                            matroid_independent m u")
      ZL_SUBSETS_UNIONS_NONEMPTY) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [EXISTS_TAC (← q r"s:A->bool") THEN ASM SET_TAC [], ALL_TAC] THEN
      X_GEN_TAC (← q r"c:(A->bool)->bool") THEN STRIP_TAC THEN
      ASM_SIMP_TAC [MATROID_INDEPENDENT_CHAIN, UNION_SUBSET] THEN ASM SET_TAC [],
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"b:A->bool")] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP MATROID_INDEPENDENT_IMP_SUBSET) THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
    MATCH_MP_TAC MATROID_SPAN_MINIMAL THEN
    (CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC]) THENL
     [TRANS_TAC SUBSET_TRANS (← q r"s UNION t:A->bool") THEN
      ASM_REWRITE_TAC [UNION_SUBSET] THEN ASM_SIMP_TAC [MATROID_SPAN_SUPERSET],
      REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"(x:A) INSERT b")) THEN
      ASM_REWRITE_TAC [MATROID_INDEPENDENT_INSERT] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THENL
       [ASM_MESON_TAC [MATROID_SPAN_INC], ASM SET_TAC []]])

  let MATROID_INTERMEDIATE_BASIS ← prove
   r"!(m:A matroid) s t.
        matroid_independent m s /\ matroid_spanning m t
        ==> ?b. s SUBSET b /\ b SUBSET (s UNION t) /\ matroid_basis m b"
   (REWRITE_TAC [matroid_spanning, matroid_basis] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"m:A matroid", ← q r"s:A->bool", ← q r"t:A->bool"]
          MATROID_INTERMEDIATE_SPAN) THEN
    ASM_MESON_TAC [matroid_independent])

  let MATROID_INDEPENDENT_EXTENDS_TO_BASIS ← prove
   r"!(m:A matroid) s.
        matroid_independent m s ==> ?b. s SUBSET b /\ matroid_basis m b"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"m:A matroid", ← q r"s:A->bool", ← q r"matroid_set m:A->bool"]
          MATROID_INTERMEDIATE_BASIS) THEN
    ASM_REWRITE_TAC [MATROID_SPANNING_SET] THEN MESON_TAC [])

  let MATROID_BASIS_EXISTS ← prove
   r"!(m:A matroid). ?b. matroid_basis m b"
   (MESON_TAC [MATROID_INDEPENDENT_EXTENDS_TO_BASIS, MATROID_INDEPENDENT_EMPTY])

  let MATROID_SPANNING_CONTAINS_BASIS ← prove
   r"!(m:A matroid) s.
        matroid_spanning m s ==> ?b. b SUBSET s /\ matroid_basis m b"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"m:A matroid", ← q r"{}:A->bool", ← q r"s:A->bool"]
          MATROID_INTERMEDIATE_BASIS) THEN
    ASM_REWRITE_TAC [MATROID_INDEPENDENT_EMPTY, UNION_EMPTY] THEN MESON_TAC [])

  let MATROID_SPAN_DEPENDENCE ← prove
   r"!(m:A matroid) s x.
        x IN matroid_set m /\ s SUBSET matroid_set m
        ==> (x IN matroid_span m s <=>
             x IN s \/
             ?t. t SUBSET s /\
                 matroid_independent m t /\
                 matroid_dependent m (x INSERT t))"
   (← do
    let m1 ← MESON [] (← q r"~(if p then T else ~x) <=> ~p /\ x")
    let t2 ← TAUT (← q r"p /\ q /\ r <=> ~(q ==> ~(p /\ r))")
    pure (REPEAT STRIP_TAC THEN
    REWRITE_TAC [MATROID_INDEPENDENT_INSERT, matroid_dependent] THEN
    ASM_REWRITE_TAC [INSERT_SUBSET] THEN
    ONCE_REWRITE_TAC [t2] THEN
    SIMP_TAC [m1] THEN
    REWRITE_TAC [NOT_IMP, ← GSYM CONJ_ASSOC] THEN EQ_TAC THENL
     [DISCH_TAC, ASM_MESON_TAC [MATROID_SPAN_MONO, MATROID_SPAN_INC, SUBSET]] THEN
    ASM_CASES_TAC (← q r"(x:A) IN s") THEN ASM_REWRITE_TAC [] THEN
    MP_TAC (← ISPECL [← q r"m:A matroid", ← q r"{}:A->bool", ← q r"s:A->bool"]
          MATROID_INTERMEDIATE_SPAN) THEN
    ASM_REWRITE_TAC [MATROID_INDEPENDENT_EMPTY, EMPTY_SUBSET, UNION_EMPTY] THEN
    MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC []))

  -- @@RETURN BEGIN
  return { MATROID_INDEPENDENT_EMPTY, MATROID_INDEPENDENT_MONO,
           MATROID_INDEPENDENT_FINITARY, MATROID_DEPENDENT_FINITARY,
           MATROID_INDEPENDENT_INSERT, MATROID_SPAN_PSUBSET_INDEPENDENT,
           MATROID_SPAN_PSUBSET_EXPLICIT, MATROID_SPANNING_SUBSET_INDEPENDENT,
           MATROID_SPANNING_PSUBSET_INDEPENDENT, MATROID_MAXIMAL_INDEPENDENT_SUBSET_SPAN,
           MATROID_BASIS_EQ_MAXIMAL_INDEPENDENT, MATROID_BASIS_EQ_MINIMAL_SPANNING,
           MATROID_INDEPENDENT_CHAIN, MATROID_SPAN_CHAIN, MATROID_INTERMEDIATE_SPAN,
           MATROID_INTERMEDIATE_BASIS, MATROID_INDEPENDENT_EXTENDS_TO_BASIS,
           MATROID_BASIS_EXISTS, MATROID_SPANNING_CONTAINS_BASIS,
           MATROID_SPAN_DEPENDENCE }
  -- @@RETURN END

structure SteinitzExchange where
  -- @@FIELDS
  MATROID_STEINITZ_EXCHANGE : thm
  MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE : thm
  MATROID_EQ_SPANS_FINITE : thm
  MATROID_EQ_SPANS_SIZE : thm
  MATROID_BASES_FINITE : thm
  MATROID_BASES_SIZE : thm
  MATROID_INDEPENDENT_CARD_LE_SPAN : thm
  MATROID_INDEPENDENT_CARD_LE_SPANNING : thm
  MATROID_EQ_SPANS_CARD_EQ : thm
  MATROID_BASES_CARD_EQ : thm
  MATROID_INDEPENDENT_SPANNING_FINITE : thm
  MATROID_DEPENDENT_FINITARY_MINIMAL : thm
  MATROID_MINIMALLY_DEPENDENT : thm
  MATROID_MINIMALLY_DEPENDENT_SUBSET : thm
  deriving Inhabited

@[nospecialize]
def setupSteinitzExchange [HolBase] (D : MatroidsDeps) (BMatroidType : MatroidType) (BLinearNotions : LinearNotions) (BIndependentSets : IndependentSets) :
    ExceptT String IO SteinitzExchange := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, .. } := D
  let { CARD_CLAUSES, CARD_LE_ANTISYM, CARD_LE_CARD, CARD_LE_FINITE,
        CARD_LE_FINITE_INFINITE, CARD_LE_IMAGE, CARD_LE_SUBSET, CARD_LE_TRANS,
        CARD_LE_UNIONS, CARD_SUBSET, CHOOSE_SUBSET_STRONG, EMPTY_SUBSET, FINITE_EMPTY,
        FINITE_INDUCT_STRONG, FINITE_INSERT, FINITE_SUBSET, FORALL_IN_GSPEC,
        FORALL_IN_IMAGE, FORALL_IN_INSERT, HAS_SIZE, IMP_CONJ, IMP_CONJ_ALT, IMP_IMP,
        INFINITE, INSERT_SUBSET, IN_DELETE, IN_DIFF, LEFT_IMP_EXISTS_THM, LE_ANTISYM,
        MONO_EXISTS, NOT_IMP, NOT_IN_EMPTY, RIGHT_FORALL_IMP_THM, RIGHT_IMP_EXISTS_THM,
        SIMPLE_IMAGE, SING_SUBSET, SKOLEM_THM, SUBSET, SUBSET_ANTISYM, .. } := D.core1
  let { SUBSET_REFL, SUBSET_TRANS, SWAP_FORALL_THM, UNIONS_SUBSET, UNION_SUBSET, WF,
        WF_PSUBSET, .. } := D.core2
  let { MATROID_SPAN_EXCHANGE, MATROID_SPAN_FINITARY, MATROID_SPAN_FINITARY_MINIMAL,
        MATROID_SPAN_MINIMAL, MATROID_SPAN_MONO, MATROID_SPAN_SUBSET,
        MATROID_SPAN_SUPERSET, SUBSET_MATROID_SPAN, .. } := BMatroidType
  let { MATROID_DEPENDENT, matroid_basis, matroid_dependent, matroid_independent,
        matroid_spanning, .. } := BLinearNotions
  let { MATROID_DEPENDENT_FINITARY, MATROID_INDEPENDENT_MONO,
        MATROID_INTERMEDIATE_SPAN, MATROID_SPAN_PSUBSET_INDEPENDENT, .. } := BIndependentSets
  -- @@SCOPE END

  let MATROID_STEINITZ_EXCHANGE ← prove
   r"!(m:A matroid) s t.
      t SUBSET matroid_set m /\
      FINITE s /\ matroid_independent m s /\ s SUBSET matroid_span m t
      ==> ?t'. t' SUBSET t /\ t' HAS_SIZE (CARD s) /\
               matroid_span m ((t DIFF t') UNION s) = matroid_span m t"
   (← do
    let s4 ← SET_RULE (← q r"y IN v ==> y INSERT (v DELETE y) = v")
    let s3 ← SET_RULE (← q r"~(x IN s) ==> (x INSERT s) DELETE x = s")
    let s2 ← SET_RULE
     (← q r"v SUBSET t UNION s ==> v SUBSET s \/ ?a. a IN v /\ a IN t")
    let s1 ← SET_RULE (← q r"s SUBSET x INSERT s")
    pure (GEN_TAC THEN
    GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC THEN
    REWRITE_TAC [RIGHT_FORALL_IMP_THM, IMP_CONJ] THEN DISCH_TAC THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"{}:A->bool") THEN
      REWRITE_TAC [HAS_SIZE, FINITE_EMPTY, EMPTY_SUBSET] THEN
      AP_TERM_TAC THEN SET_TAC [],
      MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"s:A->bool"] THEN REWRITE_TAC [IMP_IMP]] THEN
    REWRITE_TAC [INSERT_SUBSET] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o check (is_imp ∘ concl)) THEN ANTS_TAC THENL
     [ASM_MESON_TAC [MATROID_INDEPENDENT_MONO, s1],
      DISCH_THEN (X_CHOOSE_THEN (← q r"u:A->bool") STRIP_ASSUME_TAC)] THEN
    MP_TAC (← ISPECL [← q r"m:A matroid", ← q r"t DIFF u UNION s:A->bool", ← q r"x:A"]
          MATROID_SPAN_FINITARY_MINIMAL) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [ASM SET_TAC [MATROID_SPAN_SUBSET],
      ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM]] THEN
    X_GEN_TAC (← q r"v:A->bool") THEN STRIP_TAC THEN
    FIRST_ASSUM (DISJ_CASES_THEN MP_TAC o MATCH_MP s2)
    THENL
     [FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [matroid_independent]) THEN
      REWRITE_TAC [FORALL_IN_INSERT, INSERT_SUBSET] THEN
      ASM_SIMP_TAC [s3] THEN
      ASM_MESON_TAC [MATROID_SPAN_MONO, SUBSET],
      REWRITE_TAC [IN_DIFF, LEFT_IMP_EXISTS_THM]] THEN
    X_GEN_TAC (← q r"y:A") THEN STRIP_TAC THEN EXISTS_TAC (← q r"(y:A) INSERT u") THEN
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [HAS_SIZE]) THEN
    ABBREV_TAC (← q r"n = CARD(s:A->bool)") THEN
    ASM_SIMP_TAC [INSERT_SUBSET, HAS_SIZE, CARD_CLAUSES, FINITE_INSERT] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN
    CONJ_TAC THEN MATCH_MP_TAC MATROID_SPAN_MINIMAL THENL
     [ASM SET_TAC [MATROID_SPAN_SUPERSET], ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC [MATROID_SPAN_SUBSET], ALL_TAC] THEN
      TRANS_TAC SUBSET_TRANS (← q r"matroid_span (m:A matroid) (t DIFF u UNION s)") THEN
    CONJ_TAC THENL [ASM_SIMP_TAC [MATROID_SPAN_SUPERSET], ALL_TAC] THEN
    MATCH_MP_TAC MATROID_SPAN_MINIMAL THEN
    CONJ_TAC THENL [ASM SET_TAC [MATROID_SPAN_SUBSET], ALL_TAC] THEN
    TRANS_TAC SUBSET_TRANS
     (← q r"{y:A} UNION (t DIFF (y INSERT u) UNION (x INSERT s))") THEN CONJ_TAC
    THENL [SET_TAC [], ONCE_REWRITE_TAC [UNION_SUBSET]] THEN CONJ_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC MATROID_SPAN_SUPERSET THEN
      ASM SET_TAC [MATROID_SPAN_SUBSET]] THEN
    TRANS_TAC SUBSET_TRANS (← q r"matroid_span m ((x:A) INSERT (v DELETE y))") THEN
    CONJ_TAC THENL
     [REWRITE_TAC [SING_SUBSET],
      MATCH_MP_TAC MATROID_SPAN_MONO THEN ASM SET_TAC [MATROID_SPAN_SUBSET]] THEN
    MATCH_MP_TAC MATROID_SPAN_EXCHANGE THEN
    ASM_SIMP_TAC [s4] THEN
    REPEAT (CONJ_TAC THENL [ASM SET_TAC [MATROID_SPAN_SUBSET], ALL_TAC]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC []))

  let MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE ← prove
   r"!(m:A matroid) s t.
        FINITE t /\ t SUBSET matroid_set m /\
        matroid_independent m s /\ s SUBSET matroid_span m t
        ==> FINITE s /\ CARD s <= CARD t"
   (← do
    let a3 ← ARITH_RULE (← q r"m <= n ==> ~(n + 1 = m)")
    let a2 ← ARITH_RULE (← q r"~(a <= b) <=> b + 1 <= a")
    let t1 ← TAUT (← q r"p /\ q <=> ~(p ==> ~q)")
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC [t1] THEN
    REWRITE_TAC [a2] THEN DISCH_TAC THEN
    FIRST_ASSUM (X_CHOOSE_THEN (← q r"u:A->bool") STRIP_ASSUME_TAC o
      REWRITE_RULE [HAS_SIZE] o MATCH_MP CHOOSE_SUBSET_STRONG) THEN
    MP_TAC (← ISPECL [← q r"m:A matroid", ← q r"u:A->bool", ← q r"t:A->bool"]
          MATROID_STEINITZ_EXCHANGE) THEN
    ASM_REWRITE_TAC [NOT_IMP, HAS_SIZE] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC [MATROID_INDEPENDENT_MONO],
      ASM SET_TAC [],
      ASM_MESON_TAC [FINITE_SUBSET, CARD_SUBSET, a3]]))

  let MATROID_EQ_SPANS_FINITE ← prove
   r"!(m:A matroid) s t.
        matroid_independent m s /\ matroid_independent m t /\
        matroid_span m s = matroid_span m t
        ==> (FINITE s <=> FINITE t)"
   (MESON_TAC [SUBSET_MATROID_SPAN, SUBSET_REFL, matroid_independent,
               MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE])

  let MATROID_EQ_SPANS_SIZE ← prove
   r"!(m:A matroid) s t n.
        matroid_independent m s /\ matroid_independent m t /\
        matroid_span m s = matroid_span m t
        ==> (s HAS_SIZE n <=> t HAS_SIZE n)"
   (REWRITE_TAC [HAS_SIZE] THEN
    MESON_TAC [SUBSET_MATROID_SPAN, SUBSET_REFL, matroid_independent,
               MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE, LE_ANTISYM])

  let MATROID_BASES_FINITE ← prove
   r"!(m:A matroid) s t.
        matroid_basis m s /\ matroid_basis m t ==> (FINITE s <=> FINITE t)"
   (REWRITE_TAC [matroid_basis, matroid_spanning] THEN
    MESON_TAC [MATROID_EQ_SPANS_FINITE])

  let MATROID_BASES_SIZE ← prove
   r"!(m:A matroid) s t n.
        matroid_basis m s /\ matroid_basis m t
        ==> (s HAS_SIZE n <=> t HAS_SIZE n)"
   (REWRITE_TAC [matroid_basis, matroid_spanning] THEN
    MESON_TAC [MATROID_EQ_SPANS_SIZE])

  let MATROID_INDEPENDENT_CARD_LE_SPAN ← prove
   r"!(m:A matroid) s t.
        t SUBSET matroid_set m /\
        matroid_independent m s /\ s SUBSET matroid_span m t
        ==> s <=_c t"
   (← do
    let lemma ← prove
     r"!(m:A matroid) s t.
          matroid_independent m s /\
          INFINITE t /\ t SUBSET matroid_set m /\
          matroid_span m t = matroid_span m s
          ==> s <=_c t"
     (← do
      let s3 ← SET_RULE (← q r"x IN t ==> t SUBSET s ==> x IN s")
      let s2 ← SET_RULE
       (← q r"t SUBSET s /\ (t SUBSET s ==> s' SUBSET t' /\ (s SUBSET t ==> P))
        ==> (t PSUBSET s ==> t' PSUBSET s') ==> P")
      pure (REPEAT STRIP_TAC THEN
      SUBGOAL_THEN
       (← q r"!x:A. x IN t
              ==> ?k. FINITE k /\ k SUBSET s /\ x IN matroid_span m k")
      MP_TAC THENL
       [REPEAT STRIP_TAC THEN MATCH_MP_TAC MATROID_SPAN_FINITARY THEN
        ASM_MESON_TAC [MATROID_SPAN_SUPERSET, matroid_independent, SUBSET],
        REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM]] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"k:A->A->bool")) THEN
      MP_TAC (← ISPECL
       [← q r"m:A matroid", ← q r"UNIONS {(k:A->A->bool) x | x IN t}", ← q r"s:A->bool"]
            MATROID_SPAN_PSUBSET_INDEPENDENT) THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC s2 THEN
      CONJ_TAC THENL
       [REWRITE_TAC [UNIONS_SUBSET, FORALL_IN_GSPEC] THEN
        ASM_MESON_TAC [MATROID_SPAN_SUPERSET, SUBSET],
        STRIP_TAC] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
        MATCH_MP_TAC MATROID_SPAN_MINIMAL THEN
        CONJ_TAC THENL [ASM SET_TAC [matroid_independent], ALL_TAC] THEN
        REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:A")) THEN
        ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP s3) THEN
        MATCH_MP_TAC MATROID_SPAN_MONO THEN
        RULE_ASSUM_TAC (REWRITE_RULE [matroid_independent]) THEN ASM SET_TAC [],
        DISCH_THEN (MP_TAC o MATCH_MP CARD_LE_SUBSET) THEN
        MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] CARD_LE_TRANS) THEN
        MATCH_MP_TAC CARD_LE_UNIONS THEN
        ASM_SIMP_TAC [SIMPLE_IMAGE, CARD_LE_IMAGE, FORALL_IN_IMAGE] THEN
        ASM_SIMP_TAC [CARD_LE_FINITE_INFINITE]]))
    pure (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"FINITE(t:A->bool)") THENL
     [ASM_MESON_TAC [MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE,
                    CARD_LE_CARD],
      RULE_ASSUM_TAC (REWRITE_RULE [← GSYM INFINITE])] THEN
    MP_TAC (← ISPECL [← q r"m:A matroid", ← q r"s:A->bool", ← q r"t:A->bool"]
          MATROID_INTERMEDIATE_SPAN) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"b:A->bool") THEN STRIP_TAC THEN
    TRANS_TAC CARD_LE_TRANS (← q r"b:A->bool") THEN
    ASM_SIMP_TAC [CARD_LE_SUBSET] THEN MATCH_MP_TAC lemma THEN ASM_MESON_TAC []))

  let MATROID_INDEPENDENT_CARD_LE_SPANNING ← prove
   r"!(m:A matroid) s t.
        matroid_independent m s /\ matroid_spanning m t
        ==> s <=_c t"
   (REWRITE_TAC [matroid_spanning] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MATROID_INDEPENDENT_CARD_LE_SPAN THEN
    ASM_MESON_TAC [matroid_independent])

  let MATROID_EQ_SPANS_CARD_EQ ← prove
   r"!(m:A matroid) s t.
        matroid_independent m s /\ matroid_independent m t /\
        matroid_span m s = matroid_span m t
        ==> s =_c t"
   (GEN_TAC THEN REWRITE_TAC [← GSYM CARD_LE_ANTISYM] THEN
    MESON_TAC [MATROID_INDEPENDENT_CARD_LE_SPAN, matroid_independent,
               MATROID_SPAN_SUPERSET])

  let MATROID_BASES_CARD_EQ ← prove
   r"!(m:A matroid) s t.
        matroid_basis m s /\ matroid_basis m t ==> s =_c t"
   (REWRITE_TAC [matroid_basis, matroid_spanning] THEN
    MESON_TAC [MATROID_EQ_SPANS_CARD_EQ])

  let MATROID_INDEPENDENT_SPANNING_FINITE ← prove
   r"!(m:A matroid) s t.
        matroid_independent m s /\ matroid_spanning m t /\ FINITE t
        ==> FINITE s"
   (MESON_TAC [CARD_LE_FINITE, MATROID_INDEPENDENT_CARD_LE_SPANNING])

  let MATROID_DEPENDENT_FINITARY_MINIMAL ← prove
   r"!(m:A matroid) s.
        matroid_dependent m s
        ==> ?t. FINITE t /\ t SUBSET s /\ matroid_dependent m t /\
                forall t'. t' PSUBSET t ==> matroid_independent m t'"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"m:A matroid", ← q r"s:A->bool"] MATROID_DEPENDENT_FINITARY) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2
      ASSUME_TAC (X_CHOOSE_THEN (← q r"u:A->bool") STRIP_ASSUME_TAC)) THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP WF_PSUBSET) THEN REWRITE_TAC [WF] THEN
    DISCH_THEN (MP_TAC o SPEC
      (← q r"\s:A->bool. s SUBSET u /\ matroid_dependent m s")) THEN
    REWRITE_TAC [] THEN
    ANTS_TAC THENL [ASM_MESON_TAC [SUBSET_REFL], MATCH_MP_TAC MONO_EXISTS] THEN
    GEN_TAC THEN STRIP_TAC THEN
    REPEAT (CONJ_TAC THENL [ASM_MESON_TAC [FINITE_SUBSET, SUBSET], ALL_TAC]) THEN
    X_GEN_TAC (← q r"v:A->bool") THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"v:A->bool")) THEN
    REWRITE_TAC [matroid_dependent] THEN ASM SET_TAC [])

  let MATROID_MINIMALLY_DEPENDENT ← prove
   r"!(m:A matroid) s.
        (!t. t PSUBSET s ==> matroid_independent m t)
        ==> (matroid_dependent m s <=>
             ~(s = {}) /\ s SUBSET matroid_set m /\
             !a. a IN s ==> a IN matroid_span m (s DELETE a))"
   (← do
    let s4 ← SET_RULE (← q r"s DELETE a DELETE b = s DIFF {a,b}")
    let s3 ← SET_RULE
     (← q r"a IN s /\ b IN s /\ ~(a = b)
      ==> a INSERT (s DIFF {a, b}) = s DELETE b /\
          b INSERT  (s DIFF {a, b}) = s DELETE a")
    let s2 ← SET_RULE (← q r"s DELETE a PSUBSET s <=> a IN s")
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [MATROID_DEPENDENT] THEN
    ASM_CASES_TAC (← q r"(s:A->bool) SUBSET matroid_set m") THEN
    ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q r"s:A->bool = {}") THEN ASM_REWRITE_TAC [NOT_IN_EMPTY] THEN
    EQ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"b:A") STRIP_ASSUME_TAC) THEN
    X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN
    ASM_CASES_TAC (← q r"a:A = b") THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    MP_TAC (← ISPECL
     [← q r"m:A matroid", ← q r"s DIFF {a:A,b}", ← q r"a:A", ← q r"b:A"] MATROID_SPAN_EXCHANGE) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"s DELETE (a:A)")) THEN
    ASM_REWRITE_TAC [matroid_independent, s2] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"b:A") o CONJUNCT2) THEN
    ASM_SIMP_TAC [IN_DELETE, s3] THEN
    REWRITE_TAC [s4] THEN
    ASM SET_TAC []))

  let MATROID_MINIMALLY_DEPENDENT_SUBSET ← prove
   r"!(m:A matroid) s.
        matroid_dependent m s
        ==> ?t. FINITE t /\ t SUBSET s /\
                matroid_dependent m t /\ ~(t = {}) /\
                !a. a IN t ==> a IN matroid_span m (t DELETE a)"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP MATROID_DEPENDENT_FINITARY_MINIMAL) THEN
    MESON_TAC [MATROID_MINIMALLY_DEPENDENT])

  -- @@RETURN BEGIN
  return { MATROID_STEINITZ_EXCHANGE, MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE,
           MATROID_EQ_SPANS_FINITE, MATROID_EQ_SPANS_SIZE, MATROID_BASES_FINITE,
           MATROID_BASES_SIZE, MATROID_INDEPENDENT_CARD_LE_SPAN,
           MATROID_INDEPENDENT_CARD_LE_SPANNING, MATROID_EQ_SPANS_CARD_EQ,
           MATROID_BASES_CARD_EQ, MATROID_INDEPENDENT_SPANNING_FINITE,
           MATROID_DEPENDENT_FINITARY_MINIMAL, MATROID_MINIMALLY_DEPENDENT,
           MATROID_MINIMALLY_DEPENDENT_SUBSET }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Subspaces, i.e. sets closed under the matroid span operation.             -/
/- ------------------------------------------------------------------------- -/

structure Subspaces where
  -- @@FIELDS
  matroid_subspace : thm
  MATROID_SUBSPACE_IMP_SUBSET : thm
  MATROID_SUBSPACE_SET : thm
  MATROID_SUBSPACE_SPAN : thm
  MATROID_SUBSPACE : thm
  MATROID_SUBSPACE_INTERS : thm
  MATROID_SUBSPACE_INTER : thm
  MATROID_SPAN_INTER_SPANS : thm
  MATROID_SUBSPACE_CHAIN : thm
  MATROID_SPAN_SUBSPACE : thm
  MATROID_SPAN_EQ_SELF : thm
  MATROID_SPAN_OF_SUBSPACE : thm
  MATROID_SPAN_SUBSET_SUBSPACE : thm
  deriving Inhabited

@[nospecialize]
def setupSubspaces [HolBase] (D : MatroidsDeps) (BMatroidType : MatroidType) (BIndependentSets : IndependentSets) :
    ExceptT String IO Subspaces := do
  -- @@SCOPE BEGIN
  let { MESON_TAC, SET_TAC, new_definition, .. } := D
  let { INTERS_2, SUBSET_ANTISYM_EQ, .. } := D.core1
  let { SUBSET_INTERS, SUBSET_REFL, .. } := D.core2
  let { MATROID_SPAN_MINIMAL, MATROID_SPAN_MONO, MATROID_SPAN_SET, MATROID_SPAN_SPAN,
        MATROID_SPAN_SUBSET, MATROID_SPAN_SUPERSET, .. } := BMatroidType
  let { MATROID_SPAN_CHAIN, .. } := BIndependentSets
  -- @@SCOPE END

  let matroid_subspace ← new_definition
   r"matroid_subspace (m:A matroid) s <=>
        s SUBSET matroid_set m /\ matroid_span m s = s"

  let MATROID_SUBSPACE_IMP_SUBSET ← prove
   r"!(m:A matroid) s. matroid_subspace m s ==> s SUBSET matroid_set m"
   (SIMP_TAC [matroid_subspace])

  let MATROID_SUBSPACE_SET ← prove
   r"!m:A matroid. matroid_subspace m (matroid_set m)"
   (REWRITE_TAC [matroid_subspace, SUBSET_REFL, MATROID_SPAN_SET])

  let MATROID_SUBSPACE_SPAN ← prove
   r"!(m:A matroid) s.
        s SUBSET matroid_set m
        ==> matroid_subspace m (matroid_span m s)"
   (SIMP_TAC [matroid_subspace, MATROID_SPAN_SUBSET, MATROID_SPAN_SPAN])

  let MATROID_SUBSPACE ← prove
   r"!(m:A matroid) s.
        matroid_subspace m s <=>
        s SUBSET matroid_set m /\ matroid_span m s SUBSET s"
   (REWRITE_TAC [matroid_subspace, ← GSYM SUBSET_ANTISYM_EQ] THEN
    MESON_TAC [MATROID_SPAN_SUPERSET])

  let MATROID_SUBSPACE_INTERS ← prove
   r"!(m:A matroid) f.
        ~(f = {}) /\ (!s. s IN f ==> matroid_subspace m s)
        ==> matroid_subspace m (INTERS f)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [MATROID_SUBSPACE, SUBSET_INTERS] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [matroid_subspace]) THEN
    CONJ_TAC THENL [ASM SET_TAC [], X_GEN_TAC (← q r"s:A->bool") THEN STRIP_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"s:A->bool")) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
    MATCH_MP_TAC MATROID_SPAN_MONO THEN ASM SET_TAC [])

  let MATROID_SUBSPACE_INTER ← prove
   r"!(m:A matroid) s t.
        matroid_subspace m s /\ matroid_subspace m t
        ==> matroid_subspace m (s INTER t)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM INTERS_2] THEN
    MATCH_MP_TAC MATROID_SUBSPACE_INTERS THEN ASM SET_TAC [])

  let MATROID_SPAN_INTER_SPANS ← prove
   r"!(m:A matroid) s t.
        s SUBSET matroid_set m /\ t SUBSET matroid_set m
        ==> matroid_span m (matroid_span m s INTER matroid_span m t) =
            matroid_span m s INTER matroid_span m t"
   (MESON_TAC [matroid_subspace, MATROID_SPAN_SPAN, MATROID_SPAN_SUBSET,
             MATROID_SUBSPACE_INTER])

  let MATROID_SUBSPACE_CHAIN ← prove
   r"!(m:A matroid) c.
        ~(c = {}) /\
        (!s. s IN c ==> matroid_subspace m s) /\
        (!s t. s IN c /\ t IN c ==> s SUBSET t \/ t SUBSET s)
        ==> matroid_subspace m (UNIONS c)"
   (REWRITE_TAC [matroid_subspace] THEN
    ASM_SIMP_TAC [MATROID_SPAN_CHAIN] THEN SET_TAC [])

  let MATROID_SPAN_SUBSPACE ← prove
   r"!(m:A matroid) s b.
        b SUBSET s /\ s SUBSET matroid_span m b /\ matroid_subspace m s
        ==> matroid_span m b = s"
   (SIMP_TAC [← GSYM SUBSET_ANTISYM_EQ] THEN
    MESON_TAC [MATROID_SPAN_MINIMAL, matroid_subspace])

  let MATROID_SPAN_EQ_SELF ← prove
   r"!(m:A matroid) s.
        s SUBSET matroid_set m
        ==> (matroid_span m s = s <=> matroid_subspace m s)"
   (SIMP_TAC [matroid_subspace])

  let MATROID_SPAN_OF_SUBSPACE ← prove
   r"!(m:A matroid) s.
        matroid_subspace m s ==> matroid_span m s = s"
   (SIMP_TAC [matroid_subspace])

  let MATROID_SPAN_SUBSET_SUBSPACE ← prove
   r"!(m:A matroid) s t.
        s SUBSET t /\ matroid_subspace m t ==> matroid_span m s SUBSET t"
   (MESON_TAC [matroid_subspace, MATROID_SPAN_MONO])

  -- @@RETURN BEGIN
  return { matroid_subspace, MATROID_SUBSPACE_IMP_SUBSET, MATROID_SUBSPACE_SET,
           MATROID_SUBSPACE_SPAN, MATROID_SUBSPACE, MATROID_SUBSPACE_INTERS,
           MATROID_SUBSPACE_INTER, MATROID_SPAN_INTER_SPANS, MATROID_SUBSPACE_CHAIN,
           MATROID_SPAN_SUBSPACE, MATROID_SPAN_EQ_SELF, MATROID_SPAN_OF_SUBSPACE,
           MATROID_SPAN_SUBSET_SUBSPACE }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Sub-matroids                                                              -/
/- ------------------------------------------------------------------------- -/

structure Submatroids where
  -- @@FIELDS
  submatroid : thm
  SUBMATROID_GEN : thm
  SUBMATROID : thm
  SUBMATROID_SPAN : thm
  SUBMATROID_SUBSET : thm
  SUBMATROID_SET : thm
  MATROID_INDEPENDENT_SUBMATROID : thm
  MATROID_SPANNING_SUBMATROID : thm
  MATROID_SPANNING_SUBMATROID_SELF : thm
  MATROID_BASIS_SUBMATROID : thm
  MATROID_SUBSET_CONTAINS_BASIS : thm
  MATROID_STEINITZ_EXCHANGE_FINITE : thm
  MATROID_STEINITZ_EXCHANGE_ALT : thm
  deriving Inhabited

@[nospecialize]
def setupSubmatroids [HolBase] (D : MatroidsDeps) (BMatroidType : MatroidType) (BLinearNotions : LinearNotions) (BIndependentSets : IndependentSets) (BSteinitzExchange : SteinitzExchange) (BSubspaces : Subspaces) :
    ExceptT String IO Submatroids := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, new_definition, .. } := D
  let { AND_FORALL_THM, CARD_DIFF, CARD_SUBSET, CHOOSE_SUBSET_BETWEEN, FINITE_DIFF,
        HAS_SIZE, INTER_IDEMPOT, INTER_SUBSET, MONO_EXISTS, PAIR, PAIR_EQ,
        SUBSET_ANTISYM, SUBSET_DIFF, .. } := D.core1
  let { SUBSET_TRANS, SUBSET_UNION, SUB_ADD, UNION_COMM, .. } := D.core2
  let { MATROID_SPAN_EXCHANGE, MATROID_SPAN_FINITARY, MATROID_SPAN_MINIMAL,
        MATROID_SPAN_MONO, MATROID_SPAN_SET, MATROID_SPAN_SPAN, MATROID_SPAN_SUBSET,
        MATROID_SPAN_SUPERSET, MATROID_SPAN_UNION_EQ, matroid_set, matroid_span,
        matroid_tybij, .. } := BMatroidType
  let { MATROID_INDEPENDENT_IMP_SUBSET, matroid_basis, matroid_independent,
        matroid_spanning, .. } := BLinearNotions
  let { MATROID_INTERMEDIATE_BASIS, MATROID_SPANNING_CONTAINS_BASIS, .. } := BIndependentSets
  let { MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE, MATROID_STEINITZ_EXCHANGE, .. } := BSteinitzExchange
  let { MATROID_SUBSPACE_SPAN, matroid_subspace, .. } := BSubspaces
  -- @@SCOPE END

  let submatroid ← new_definition
   r"submatroid (m:A matroid) s =
        matroid(matroid_span m (matroid_set m INTER s),matroid_span m)"

  let SUBMATROID_GEN ← prove
   r"(!m s:A->bool. matroid_set (submatroid m s) =
                  matroid_span m (matroid_set m INTER s)) /\
     (!m s:A->bool. matroid_span (submatroid m s) = matroid_span m)"
   (REWRITE_TAC [AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [matroid_set, matroid_span] THEN
    REWRITE_TAC [← GSYM PAIR_EQ, submatroid] THEN
    REWRITE_TAC [← GSYM (← CONJUNCT2 matroid_tybij)] THEN
    MP_TAC (← ISPECL [← q r"m:A matroid", ← q r"matroid_set m INTER s:A->bool"]
          MATROID_SPAN_SUBSET) THEN
    REWRITE_TAC [INTER_SUBSET] THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC MATROID_SPAN_MINIMAL,
      MATCH_MP_TAC MATROID_SPAN_SUPERSET,
      MATCH_MP_TAC MATROID_SPAN_MONO,
      MATCH_MP_TAC MATROID_SPAN_SPAN,
      MATCH_MP_TAC MATROID_SPAN_FINITARY,
      MATCH_MP_TAC MATROID_SPAN_EXCHANGE] THEN
    ASM SET_TAC [])

  let SUBMATROID ← prove
   r"(!m s:A->bool.
        matroid_subspace m s ==> matroid_set (submatroid m s) = s) /\
     (!m s:A->bool. matroid_span (submatroid m s) = matroid_span m)"
   (← do
    let s1 ← SET_RULE (← q r"s SUBSET u ==> u INTER s = s")
    pure (REWRITE_TAC [SUBMATROID_GEN] THEN
    SIMP_TAC [matroid_subspace, s1]))

  let SUBMATROID_SPAN ← prove
   r"!m s:A->bool.
        s SUBSET matroid_set m
        ==> submatroid m (matroid_span m s) = submatroid m s"
   (← do
    let s1 ← SET_RULE (← q r"t SUBSET s ==> s INTER t = t")
    pure (SIMP_TAC [submatroid, MATROID_SPAN_SPAN, MATROID_SPAN_SUBSET, s1]))

  let SUBMATROID_SUBSET ← prove
   r"(!m s:A->bool.
        s SUBSET matroid_set m
        ==> matroid_set (submatroid m s) = matroid_span m s) /\
     (!m s:A->bool. matroid_span (submatroid m s) = matroid_span m)"
   (MESON_TAC [SUBMATROID_SPAN, SUBMATROID, MATROID_SUBSPACE_SPAN])

  let SUBMATROID_SET ← prove
   r"!m:A matroid. submatroid m (matroid_set m) = m"
   (REWRITE_TAC [submatroid, INTER_IDEMPOT, MATROID_SPAN_SET] THEN
    REWRITE_TAC [matroid_set, matroid_span, PAIR, ← CONJUNCT1 matroid_tybij])

  let MATROID_INDEPENDENT_SUBMATROID ← prove
   r"!(m:A matroid) s b.
        s SUBSET matroid_set m
        ==> (matroid_independent (submatroid m s) b <=>
             b SUBSET matroid_span m s /\ matroid_independent m b)"
   (SIMP_TAC [matroid_independent, SUBMATROID_SUBSET] THEN
    MESON_TAC [MATROID_SPAN_SUBSET, SUBSET_TRANS])

  let MATROID_SPANNING_SUBMATROID ← prove
   r"!(m:A matroid) s b.
       s SUBSET matroid_set m
       ==> (matroid_spanning (submatroid m s) b <=>
            b SUBSET matroid_span m s /\ matroid_span m b = matroid_span m s)"
   (SIMP_TAC [matroid_spanning, SUBMATROID_SUBSET])

  let MATROID_SPANNING_SUBMATROID_SELF ← prove
   r"!(m:A matroid) s.
       s SUBSET matroid_set m ==> matroid_spanning (submatroid m s) s"
   (SIMP_TAC [MATROID_SPANNING_SUBMATROID, MATROID_SPAN_SUPERSET])

  let MATROID_BASIS_SUBMATROID ← prove
   r"!(m:A matroid) s b.
       s SUBSET matroid_set m
       ==> (matroid_basis (submatroid m s) b <=>
            b SUBSET matroid_span m s /\
            matroid_independent m b /\
            matroid_span m b = matroid_span m s)"
   (REWRITE_TAC [matroid_basis] THEN
    SIMP_TAC [MATROID_INDEPENDENT_SUBMATROID, MATROID_SPANNING_SUBMATROID] THEN
    MESON_TAC [])

  let MATROID_SUBSET_CONTAINS_BASIS ← prove
   r"!(m:A matroid) s.
        s SUBSET matroid_set m
        ==> ?b. b SUBSET s /\
                matroid_independent m b /\
                matroid_span m b = matroid_span m s"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP MATROID_SPANNING_SUBMATROID_SELF) THEN
    DISCH_THEN (MP_TAC o MATCH_MP MATROID_SPANNING_CONTAINS_BASIS) THEN
    ASM_SIMP_TAC [MATROID_BASIS_SUBMATROID] THEN MESON_TAC [])

  let MATROID_STEINITZ_EXCHANGE_FINITE ← prove
   r"!(m:A matroid) s t.
        FINITE t /\ t SUBSET matroid_set m /\
        matroid_independent m s /\ s SUBSET matroid_span m t
        ==> ?t'. t' HAS_SIZE (CARD t) /\
                 s SUBSET t' /\
                 t' SUBSET (s UNION t) /\
                 matroid_span m t' = matroid_span m t"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"submatroid m (t:A->bool)", ← q r"s:A->bool", ← q r"t:A->bool"]
          MATROID_INTERMEDIATE_BASIS) THEN
    ASM_SIMP_TAC [MATROID_INDEPENDENT_SUBMATROID, SUBMATROID, matroid_basis,
                 MATROID_SPANNING_SUBMATROID, MATROID_SPAN_SUPERSET] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"b:A->bool") STRIP_ASSUME_TAC) THEN
    MP_TAC (← SPECL [← q r"CARD(t:A->bool)", ← q r"b:A->bool", ← q r"s UNION t:A->bool"]
          CHOOSE_SUBSET_BETWEEN) THEN
    ASM_SIMP_TAC [CARD_SUBSET, SUBSET_UNION] THEN ANTS_TAC THENL
     [ASM_MESON_TAC [MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE],
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"u:A->bool") THEN STRIP_TAC] THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MP_TAC (← ISPECL [← q r"m:A matroid", ← q r"s:A->bool", ← q r"t:A->bool"]
       MATROID_SPAN_UNION_EQ) THEN
      ASM_SIMP_TAC [MATROID_INDEPENDENT_IMP_SUBSET] THEN
      DISCH_THEN (SUBST1_TAC o SYM),
      FIRST_X_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC LAND_CONV [← SYM th]))] THEN
    MATCH_MP_TAC MATROID_SPAN_MONO THEN ASM SET_TAC [MATROID_SPAN_SUBSET])

  let MATROID_STEINITZ_EXCHANGE_ALT ← prove
   r"!(m:A matroid) s t.
        FINITE t /\ t SUBSET matroid_set m /\
        matroid_independent m s /\ s SUBSET matroid_span m t
        ==> ?t'. t' SUBSET t /\ CARD(t') + CARD s = CARD t /\
                 matroid_span m (s UNION t') = matroid_span m t"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"m:(A)matroid", ← q r"s:A->bool", ← q r"t:A->bool"]
     MATROID_STEINITZ_EXCHANGE) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC [MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE],
      DISCH_THEN (X_CHOOSE_THEN (← q r"u:A->bool") STRIP_ASSUME_TAC)] THEN
    EXISTS_TAC (← q r"t DIFF u:A->bool") THEN ONCE_REWRITE_TAC [UNION_COMM] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [HAS_SIZE]) THEN
    ASM_SIMP_TAC [SUBSET_DIFF, CARD_DIFF, FINITE_DIFF] THEN
    MATCH_MP_TAC SUB_ADD THEN ASM_MESON_TAC [CARD_SUBSET])

  -- @@RETURN BEGIN
  return { submatroid, SUBMATROID_GEN, SUBMATROID, SUBMATROID_SPAN, SUBMATROID_SUBSET,
           SUBMATROID_SET, MATROID_INDEPENDENT_SUBMATROID, MATROID_SPANNING_SUBMATROID,
           MATROID_SPANNING_SUBMATROID_SELF, MATROID_BASIS_SUBMATROID,
           MATROID_SUBSET_CONTAINS_BASIS, MATROID_STEINITZ_EXCHANGE_FINITE,
           MATROID_STEINITZ_EXCHANGE_ALT }
  -- @@RETURN END

/-- Destructure a list of three theorems. -/
def list3 (l : List thm) : ExceptT String IO (thm × thm × thm) :=
  match l with
  | [a, b, c] => pure (a, b, c)
  | _ => throw "Match_failure"

/- ------------------------------------------------------------------------- -/
/- Finite-dimensionality and dimension, both of whole matroid and a subset.  -/
/- (matroids.ml 1051-1270)                                                   -/
/- ------------------------------------------------------------------------- -/

structure FiniteDim where
  -- @@FIELDS
  matroid_finite_dimensional : thm
  matroid_dimension : thm
  matroid_finite_dim : thm
  matroid_dim : thm
  MATROID_FINITE_DIM_IMP_SUBSET : thm
  MATROID_FINITE_DIM_SET : thm
  MATROID_DIM_SET : thm
  MATROID_FINITE_DIM_SPAN_EQ : thm
  MATROID_FINITE_DIM_SPAN : thm
  MATROID_DIM_SPAN : thm
  MATROID_FINITE_DIMENSIONAL : thm
  MATROID_FINITE_DIMENSIONAL_BASIS : thm
  MATROID_FINITE_DIMENSIONAL_CONTAINS_BASIS : thm
  MATROID_FINITE_DIMENSIONAL_ANY : thm
  MATROID_FINITE_DIM : thm
  MATROID_FINITE_DIM_SUBSET : thm
  MATROID_FINITE_DIM_BASIS : thm
  MATROID_FINITE_DIMENSIONAL_DIM : thm
  FINITE_IMP_MATROID_FINITE_DIM : thm
  MATROID_FINITE_DIM_FINITE : thm
  MATROID_FINITE_DIM_EMPTY : thm
  MATROID_FINITE_DIM_MONO : thm
  MATROID_FINITE_DIM_UNION : thm
  MATROID_FINITE_DIM_INSERT : thm
  deriving Inhabited

@[nospecialize]
def setupFiniteDim [HolBase] (D : MatroidsDeps) (BMatroidType : MatroidType) (BLinearNotions : LinearNotions) (BIndependentSets : IndependentSets) (BSteinitzExchange : SteinitzExchange) (BSubmatroids : Submatroids) :
    ExceptT String IO FiniteDim := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, define, .. } := D
  let { AND_FORALL_THM, EMPTY_SUBSET, FINITE_EMPTY, FINITE_SING, FINITE_SUBSET,
        FINITE_UNION, MONO_EXISTS, NOT_IMP, SING_SUBSET, SUBSET, SUBSET_ANTISYM_EQ, .. } := D.core1
  let { SUBSET_REFL, SUBSET_TRANS, SUBSET_UNION, UNION_SUBSET, .. } := D.core2
  let { MATROID_SPAN_EQ_SET, MATROID_SPAN_MINIMAL, MATROID_SPAN_MONO,
        MATROID_SPAN_SUBSET, MATROID_SPAN_SUPERSET, SUBSET_MATROID_SPAN, .. } := BMatroidType
  let { matroid_basis, matroid_spanning, .. } := BLinearNotions
  let { MATROID_BASIS_EXISTS, MATROID_SPANNING_CONTAINS_BASIS, .. } := BIndependentSets
  let { MATROID_BASES_FINITE, MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE, .. } := BSteinitzExchange
  let { MATROID_SPANNING_SUBMATROID, MATROID_SUBSET_CONTAINS_BASIS, SUBMATROID_SET,
        SUBMATROID_SPAN, SUBMATROID_SUBSET, .. } := BSubmatroids
  -- @@SCOPE END

  let matroid_finite_dimensional ← define
   r"matroid_finite_dimensional (m:A matroid) <=>
          ?b. FINITE b /\ matroid_spanning m b"

  let matroid_dimension ← define
   r"matroid_dimension (m:A matroid) =
          @n. !b. matroid_basis m b ==> b HAS_SIZE n"

  let matroid_finite_dim ← define
   r"matroid_finite_dim (m:A matroid) s <=>
          s SUBSET matroid_set m /\
          matroid_finite_dimensional(submatroid m s)"

  let matroid_dim ← define
   r"matroid_dim (m:A matroid) s = matroid_dimension(submatroid m s)"

  let MATROID_FINITE_DIM_IMP_SUBSET ← prove
   r"!(m:A matroid) s. matroid_finite_dim m s ==> s SUBSET matroid_set m"
   (SIMP_TAC [matroid_finite_dim])

  let MATROID_FINITE_DIM_SET ← prove
   r"!(m:A matroid).
      matroid_finite_dim m (matroid_set m) = matroid_finite_dimensional m"
   (REWRITE_TAC [matroid_finite_dim, SUBMATROID_SET, SUBSET_REFL])

  let MATROID_DIM_SET ← prove
   r"!(m:A matroid).
        matroid_dim m (matroid_set m) = matroid_dimension m"
   (REWRITE_TAC [matroid_dim, SUBMATROID_SET])

  let MATROID_FINITE_DIM_SPAN_EQ ← prove
   r"!(m:A matroid) s.
          matroid_finite_dim m s <=>
          s SUBSET matroid_set m /\ matroid_finite_dim m (matroid_span m s)"
   (REWRITE_TAC [matroid_finite_dim] THEN
    MESON_TAC [SUBMATROID_SPAN, MATROID_SPAN_SUBSET])

  let MATROID_FINITE_DIM_SPAN ← prove
   r"!(m:A matroid) s.
          s SUBSET matroid_set m
          ==> (matroid_finite_dim m (matroid_span m s) <=>
               matroid_finite_dim m s)"
   (MESON_TAC [MATROID_FINITE_DIM_SPAN_EQ])

  let MATROID_DIM_SPAN ← prove
   r"!(m:A matroid) s.
          s SUBSET matroid_set m
          ==> matroid_dim m (matroid_span m s) = matroid_dim m s"
   (SIMP_TAC [matroid_dim, SUBMATROID_SPAN])

  let MATROID_FINITE_DIMENSIONAL ← prove
   r"!(m:A matroid).
          matroid_finite_dimensional m <=>
          ?b. FINITE b /\
              b SUBSET matroid_set m /\
              matroid_set m SUBSET matroid_span m b"
   (REWRITE_TAC [matroid_finite_dimensional, matroid_spanning] THEN
    MESON_TAC [MATROID_SPAN_EQ_SET])

  let MATROID_FINITE_DIMENSIONAL_BASIS ← prove
   r"!(m:A matroid).
          matroid_finite_dimensional m <=>
          ?b. FINITE b /\ matroid_basis m b"
   (REWRITE_TAC [matroid_finite_dimensional] THEN
    MESON_TAC [MATROID_SPANNING_CONTAINS_BASIS, FINITE_SUBSET,
              matroid_basis])

  let MATROID_FINITE_DIMENSIONAL_CONTAINS_BASIS ← prove
   r"!(m:A matroid) s.
          matroid_finite_dimensional m /\ matroid_spanning m s
          ==> ?b. FINITE b /\ b SUBSET s /\ matroid_basis m b"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP MATROID_SPANNING_CONTAINS_BASIS) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [MATROID_FINITE_DIMENSIONAL_BASIS]) THEN
    ASM_MESON_TAC [MATROID_BASES_FINITE])

  let MATROID_FINITE_DIMENSIONAL_ANY ← prove
   r"!(m:A matroid) b.
          matroid_basis m b
          ==> (matroid_finite_dimensional (m:A matroid) <=> FINITE b)"
   (MESON_TAC [MATROID_FINITE_DIMENSIONAL_BASIS, MATROID_BASES_FINITE,
               MATROID_BASIS_EXISTS])

  let (MATROID_FINITE_DIM, MATROID_FINITE_DIM_SUBSET, MATROID_FINITE_DIM_BASIS) ←
    list3 (CONJUNCTS (← prove
   r"(!(m:A matroid) s.
          matroid_finite_dim m s <=>
          ?b. FINITE b /\ b SUBSET matroid_set m /\ s SUBSET matroid_span m b) /\
     (!(m:A matroid) s.
          matroid_finite_dim m s <=>
          s SUBSET matroid_set m /\
          ?b. FINITE b /\ b SUBSET s /\ s SUBSET matroid_span m b) /\
     (!(m:A matroid) s.
          matroid_finite_dim m s <=>
          s SUBSET matroid_set m /\
          ?b. FINITE b /\
              b SUBSET s /\
              matroid_independent m b /\
              matroid_span m b = matroid_span m s)"
   (← do
    let t2 ← TAUT (← q
     r"p /\ q <=> ~(p ==> ~q)")
    let t1 ← TAUT (← q
     r"(s ==> r) /\ (r ==> p) /\ (p ==> q) /\ (q ==> s)
      ==> (p <=> q) /\ (p <=> r) /\ (p <=> s)")
    pure (REWRITE_TAC [AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
    MATCH_MP_TAC t1 THEN
    CONJ_TAC THENL [ASM SET_TAC [MATROID_SPAN_SUPERSET], ALL_TAC] THEN
    REWRITE_TAC [← ONCE_REWRITE_RULE [t2] matroid_finite_dim] THEN
    SIMP_TAC [matroid_finite_dimensional, SUBMATROID_SUBSET,
             MATROID_SPANNING_SUBMATROID] THEN
    REWRITE_TAC [NOT_IMP] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ] THEN
      MESON_TAC [MATROID_SPAN_MINIMAL, MATROID_SPAN_SUPERSET, SUBSET_TRANS],
      MESON_TAC [SUBSET_MATROID_SPAN, MATROID_SPAN_SUBSET, SUBSET],
      DISCH_THEN (X_CHOOSE_THEN (← q r"c:A->bool") STRIP_ASSUME_TAC)] THEN
    MATCH_MP_TAC (← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")) THEN CONJ_TAC THENL
     [ASM SET_TAC [MATROID_SPAN_SUBSET], DISCH_TAC] THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP MATROID_SUBSET_CONTAINS_BASIS) THEN
    MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MP_TAC (← ISPECL [← q r"m:A matroid", ← q r"b:A->bool", ← q r"c:A->bool"]
          MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE) THEN
    ASM SET_TAC [MATROID_SPAN_SUBSET, MATROID_SPAN_SUPERSET]))))

  let MATROID_FINITE_DIMENSIONAL_DIM ← prove
   r"!(m:A matroid) s.
          matroid_finite_dimensional m /\ s SUBSET matroid_set m
          ==> matroid_finite_dim m s"
   (REWRITE_TAC [matroid_finite_dimensional, matroid_spanning,
                MATROID_FINITE_DIM] THEN
    SET_TAC [])

  let FINITE_IMP_MATROID_FINITE_DIM ← prove
   r"!(m:A matroid) s.
          FINITE s /\ s SUBSET matroid_set m ==> matroid_finite_dim m s"
   (REWRITE_TAC [MATROID_FINITE_DIM] THEN MESON_TAC [MATROID_SPAN_SUPERSET])

  let MATROID_FINITE_DIM_FINITE ← prove
   r"!m s:A->bool.
          FINITE s ==> (matroid_finite_dim m s <=> s SUBSET matroid_set m)"
   (MESON_TAC [matroid_finite_dim, FINITE_IMP_MATROID_FINITE_DIM])

  let MATROID_FINITE_DIM_EMPTY ← prove
   r"!m:A matroid. matroid_finite_dim m {}"
   (SIMP_TAC [FINITE_IMP_MATROID_FINITE_DIM, EMPTY_SUBSET, FINITE_EMPTY])

  let MATROID_FINITE_DIM_MONO ← prove
   r"!(m:A matroid) s t.
          matroid_finite_dim m t /\ s SUBSET t ==> matroid_finite_dim m s"
   (REWRITE_TAC [MATROID_FINITE_DIM] THEN SET_TAC [])

  let MATROID_FINITE_DIM_UNION ← prove
   r"!m s t:A->bool.
          matroid_finite_dim m (s UNION t) <=>
          matroid_finite_dim m s /\ matroid_finite_dim m t"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [MESON_TAC [MATROID_FINITE_DIM_MONO, SUBSET_UNION],
      REWRITE_TAC [MATROID_FINITE_DIM]] THEN
    DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_THEN (← q r"b:A->bool") STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN (← q r"c:A->bool") STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC (← q r"b UNION c:A->bool") THEN
    ASM_REWRITE_TAC [UNION_SUBSET, FINITE_UNION] THEN CONJ_TAC THEN
    ASM_MESON_TAC [MATROID_SPAN_MONO, UNION_SUBSET, SUBSET_TRANS, SUBSET_UNION])

  let MATROID_FINITE_DIM_INSERT ← prove
   r"!m s x:A.
          matroid_finite_dim m (x INSERT s) <=>
          x IN matroid_set m /\ matroid_finite_dim m s"
   (← do
    let s1 ← SET_RULE (← q r"a INSERT s = {a} UNION s")
    pure (REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC [s1] THEN
    SIMP_TAC [MATROID_FINITE_DIM_UNION, MATROID_FINITE_DIM_FINITE, FINITE_SING,
             SING_SUBSET]))

  -- @@RETURN BEGIN
  return { matroid_finite_dimensional, matroid_dimension, matroid_finite_dim,
           matroid_dim, MATROID_FINITE_DIM_IMP_SUBSET, MATROID_FINITE_DIM_SET,
           MATROID_DIM_SET, MATROID_FINITE_DIM_SPAN_EQ, MATROID_FINITE_DIM_SPAN,
           MATROID_DIM_SPAN, MATROID_FINITE_DIMENSIONAL,
           MATROID_FINITE_DIMENSIONAL_BASIS, MATROID_FINITE_DIMENSIONAL_CONTAINS_BASIS,
           MATROID_FINITE_DIMENSIONAL_ANY, MATROID_FINITE_DIM, MATROID_FINITE_DIM_SUBSET,
           MATROID_FINITE_DIM_BASIS, MATROID_FINITE_DIMENSIONAL_DIM,
           FINITE_IMP_MATROID_FINITE_DIM, MATROID_FINITE_DIM_FINITE,
           MATROID_FINITE_DIM_EMPTY, MATROID_FINITE_DIM_MONO, MATROID_FINITE_DIM_UNION,
           MATROID_FINITE_DIM_INSERT }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Dimension of whole matroid and of a subset: basic characterizations.      -/
/- (matroids.ml 1272-1470)                                                   -/
/- ------------------------------------------------------------------------- -/

structure Dimension where
  -- @@FIELDS
  MATROID_DIMENSION_ALT : thm
  MATROID_DIM_BASIS : thm
  MATROID_DIM_ALT : thm
  MATROID_DIMENSION_UNIQUE : thm
  MATROID_DIMENSION_EQ_CARD : thm
  MATROID_DIM_UNIQUE_ALT : thm
  MATROID_DIM_UNIQUE : thm
  MATROID_SPAN_DIM_EQ : thm
  MATROID_SPAN_INSERT_REFL : thm
  MATROID_BASIS_EXISTS_DIMENSION : thm
  MATROID_BASIS_EXISTS_DIM : thm
  MATROID_CONTAINS_BASIS_DIM : thm
  MATROID_DIM_EQ_CARD_GEN : thm
  MATROID_DIM_EQ_CARD : thm
  MATROID_DIMENSION_LE : thm
  MATROID_DIMENSION_FINITE_LE : thm
  MATROID_DIM_LE : thm
  MATROID_DIM_FINITE_LE : thm
  MATROID_DIM_LE_CARD_GEN : thm
  MATROID_DIM_LE_CARD : thm
  MATROID_DIMENSION_GE_FINITE_CARD : thm
  MATROID_DIMENSION_GE : thm
  MATROID_DIMENSION_GE_CARD : thm
  MATROID_DIM_GE_FINITE_CARD : thm
  MATROID_DIM_GE : thm
  MATROID_DIM_GE_CARD_GEN : thm
  MATROID_DIM_GE_CARD : thm
  FINITE_IMP_MATROID_FINITE_DIM_SPAN : thm
  MATROID_INDEPENDENT_IMP_FINITE : thm
  deriving Inhabited

@[nospecialize]
def setupDimension [HolBase] (D : MatroidsDeps) (BMatroidType : MatroidType) (BLinearNotions : LinearNotions) (BIndependentSets : IndependentSets) (BSteinitzExchange : SteinitzExchange) (BSubmatroids : Submatroids) (BFiniteDim : FiniteDim) :
    ExceptT String IO Dimension := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, SET_TAC, .. } := D
  let { CARD_SUBSET, EQ_IMP_LE, FINITE_SUBSET, FUN_EQ_THM, HAS_SIZE, LE_REFL, LE_TRANS,
        SUBSET, .. } := D.core1
  let { SUBSET_REFL, SUBSET_TRANS, .. } := D.core2
  let { MATROID_SPAN_EQ, MATROID_SPAN_INSERT_EQ, MATROID_SPAN_MINIMAL,
        MATROID_SPAN_SUBSET, MATROID_SPAN_SUPERSET, .. } := BMatroidType
  let { MATROID_INDEPENDENT_IMP_SUBSET, MATROID_SPANNING_ALT, matroid_basis,
        matroid_spanning, .. } := BLinearNotions
  let { MATROID_BASIS_EXISTS, .. } := BIndependentSets
  let { MATROID_BASES_SIZE, MATROID_EQ_SPANS_SIZE,
        MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE, .. } := BSteinitzExchange
  let { MATROID_BASIS_SUBMATROID, MATROID_INDEPENDENT_SUBMATROID,
        MATROID_SUBSET_CONTAINS_BASIS, .. } := BSubmatroids
  let { FINITE_IMP_MATROID_FINITE_DIM, MATROID_DIM_SPAN, MATROID_FINITE_DIM,
        MATROID_FINITE_DIMENSIONAL, MATROID_FINITE_DIMENSIONAL_BASIS,
        MATROID_FINITE_DIM_BASIS, MATROID_FINITE_DIM_SPAN, matroid_dim,
        matroid_dimension, matroid_finite_dim, .. } := BFiniteDim
  -- @@SCOPE END

  let MATROID_DIMENSION_ALT ← prove
   r"!m:A matroid.
          matroid_dimension m = @n. ?b. matroid_basis m b /\ b HAS_SIZE n"
   (GEN_TAC THEN REWRITE_TAC [matroid_dimension] THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    MESON_TAC [MATROID_BASES_SIZE, MATROID_BASIS_EXISTS])

  let MATROID_DIM_BASIS ← prove
   r"!(m:A matroid) s.
          s SUBSET matroid_set m
          ==> (matroid_dim m s =
               @n. ?b. b SUBSET s /\
                       matroid_independent m b /\
                       matroid_span m b = matroid_span m s /\
                       b HAS_SIZE n)"
   (REWRITE_TAC [matroid_dim, MATROID_DIMENSION_ALT] THEN
    SIMP_TAC [MATROID_BASIS_SUBMATROID] THEN
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP MATROID_SUBSET_CONTAINS_BASIS) THEN
    ASM_MESON_TAC [MATROID_EQ_SPANS_SIZE, MATROID_SPAN_SUPERSET, SUBSET_TRANS])

  let MATROID_DIM_ALT ← prove
   r"!(m:A matroid) s.
          s SUBSET matroid_set m
          ==> (matroid_dim m s =
               @n. ?b. b SUBSET s /\
                       matroid_independent m b /\
                       s SUBSET matroid_span m b /\
                       b HAS_SIZE n)"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [MATROID_DIM_BASIS] THEN
    REPLICATE_TAC 2 (AP_TERM_TAC THEN ABS_TAC) THEN
    ASM_MESON_TAC [MATROID_SPAN_EQ, MATROID_SPAN_MINIMAL, SUBSET_TRANS])

  let MATROID_DIMENSION_UNIQUE ← prove
   r"!(m:A matroid) b n.
          matroid_basis m b /\ b HAS_SIZE n ==> matroid_dimension m = n"
   (REWRITE_TAC [matroid_dimension] THEN
    MESON_TAC [MATROID_BASES_SIZE, HAS_SIZE])

  let MATROID_DIMENSION_EQ_CARD ← prove
   r"!(m:A matroid) b.
          matroid_basis m b /\ FINITE b ==> matroid_dimension m = CARD b"
   (MESON_TAC [MATROID_DIMENSION_UNIQUE, HAS_SIZE])

  let MATROID_DIM_UNIQUE_ALT ← prove
   r"!(m:A matroid) s b n.
          s SUBSET matroid_set m /\ b SUBSET matroid_set m /\ b HAS_SIZE n /\
          matroid_independent m b /\ matroid_span m b = matroid_span m s
          ==> matroid_dim m s = n"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [matroid_dim] THEN
    MATCH_MP_TAC MATROID_DIMENSION_UNIQUE THEN EXISTS_TAC (← q r"b:A->bool") THEN
    SUBGOAL_THEN (← q r"(s:A->bool) SUBSET matroid_set m") ASSUME_TAC THENL
     [ASM_MESON_TAC [MATROID_SPAN_SUBSET, SUBSET_TRANS],
      ASM_SIMP_TAC [MATROID_BASIS_SUBMATROID]] THEN
    ASM_MESON_TAC [MATROID_SPAN_SUPERSET])

  let MATROID_DIM_UNIQUE ← prove
   r"!(m:A matroid) s b n.
          b SUBSET s /\ b HAS_SIZE n /\
          matroid_independent m b /\ s SUBSET matroid_span m b
          ==> matroid_dim m s = n"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC MATROID_DIM_UNIQUE_ALT THEN
    EXISTS_TAC (← q r"b:A->bool") THEN ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP MATROID_INDEPENDENT_IMP_SUBSET) THEN
    ASM_MESON_TAC [MATROID_SPAN_EQ, MATROID_SPAN_SUBSET, SUBSET_TRANS])

  let MATROID_SPAN_DIM_EQ ← prove
   r"!m s t:A->bool.
          s SUBSET matroid_set m /\
          t SUBSET matroid_set m /\
          matroid_span m s = matroid_span m t
          ==> matroid_dim m s = matroid_dim m t"
   (MESON_TAC [MATROID_DIM_SPAN])

  let MATROID_SPAN_INSERT_REFL ← prove
   r"!m s x:A.
          s SUBSET matroid_set m /\ x IN matroid_span m s
          ==> matroid_span m (x INSERT s) = matroid_span m s"
   (MESON_TAC [MATROID_SPAN_INSERT_EQ, MATROID_SPAN_SUBSET, SUBSET])

  let MATROID_BASIS_EXISTS_DIMENSION ← prove
   r"!m:A matroid.
          matroid_finite_dimensional m <=>
          ?b. b HAS_SIZE matroid_dimension m /\ matroid_basis m b"
   (REWRITE_TAC [MATROID_FINITE_DIMENSIONAL_BASIS, HAS_SIZE] THEN
    MESON_TAC [MATROID_DIMENSION_UNIQUE, HAS_SIZE])

  let MATROID_BASIS_EXISTS_DIM ← prove
   r"!m s:A->bool.
          matroid_finite_dim m s <=>
          s SUBSET matroid_set m /\
          ?b. b HAS_SIZE matroid_dim m s /\
              b SUBSET matroid_span m s /\
              matroid_independent m b /\
              matroid_span m b = matroid_span m s"
   (REPEAT GEN_TAC THEN REWRITE_TAC [matroid_finite_dim] THEN
    ASM_CASES_TAC (← q r"(s:A->bool) SUBSET matroid_set m") THEN ASM_REWRITE_TAC [] THEN
    ASM_SIMP_TAC [MATROID_BASIS_EXISTS_DIMENSION, MATROID_BASIS_SUBMATROID] THEN
    MESON_TAC [matroid_dim])

  let MATROID_CONTAINS_BASIS_DIM ← prove
   r"!m s:A->bool.
          matroid_finite_dim m s <=>
          s SUBSET matroid_set m /\
          ?b. b HAS_SIZE matroid_dim m s /\
              b SUBSET s /\
              matroid_independent m b /\
              matroid_span m b = matroid_span m s"
   (REPEAT GEN_TAC THEN REWRITE_TAC [MATROID_FINITE_DIM_BASIS, HAS_SIZE] THEN
    ASM_CASES_TAC (← q r"(s:A->bool) SUBSET matroid_set m") THEN ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [MATROID_DIM_UNIQUE_ALT, HAS_SIZE, SUBSET])

  let MATROID_DIM_EQ_CARD_GEN ← prove
   r"!(m:A matroid) s b.
          b SUBSET s /\ FINITE b /\
          matroid_independent m b /\ s SUBSET matroid_span m b
          ==> matroid_dim m s = CARD b"
   (MESON_TAC [MATROID_DIM_UNIQUE, HAS_SIZE])

  let MATROID_DIM_EQ_CARD ← prove
   r"!(m:A matroid) b.
          FINITE b /\ matroid_independent m b
          ==> matroid_dim m b = CARD b"
   (MESON_TAC [MATROID_DIM_EQ_CARD_GEN, MATROID_INDEPENDENT_IMP_SUBSET,
              SUBSET_REFL, MATROID_SPAN_SUPERSET])

  let MATROID_DIMENSION_LE ← prove
   r"!(m:A matroid) b n.
          b SUBSET matroid_set m /\ matroid_set m SUBSET matroid_span m b /\
          FINITE b /\ CARD b <= n
          ==> matroid_dimension m <= n"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP MATROID_SUBSET_CONTAINS_BASIS) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"c:A->bool") STRIP_ASSUME_TAC) THEN
    TRANS_TAC LE_TRANS (← q r"CARD(c:A->bool)") THEN CONJ_TAC THENL
     [MATCH_MP_TAC EQ_IMP_LE, ASM_MESON_TAC [CARD_SUBSET, LE_TRANS]] THEN
    MATCH_MP_TAC MATROID_DIMENSION_UNIQUE THEN
    EXISTS_TAC (← q r"c:A->bool") THEN ASM_REWRITE_TAC [matroid_basis, HAS_SIZE] THEN
    ASM_REWRITE_TAC [MATROID_SPANNING_ALT] THEN
    ASM_MESON_TAC [FINITE_SUBSET, SUBSET_TRANS])

  let MATROID_DIMENSION_FINITE_LE ← prove
   r"!(m:A matroid) b n.
          b SUBSET matroid_set m /\ matroid_set m SUBSET matroid_span m b /\
          FINITE b /\ CARD b <= n
          ==> matroid_finite_dimensional m /\ matroid_dimension m <= n"
   (MESON_TAC [MATROID_DIMENSION_LE, MATROID_FINITE_DIMENSIONAL])

  let MATROID_DIM_LE ← prove
   r"!(m:A matroid) s b n.
          FINITE b /\ CARD b <= n /\
          b SUBSET matroid_set m /\ s SUBSET matroid_span m b
          ==> matroid_dim m s <= n"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"(s:A->bool) SUBSET matroid_set m") ASSUME_TAC THENL
     [ASM_MESON_TAC [MATROID_SPAN_SUBSET, SUBSET_TRANS],
      FIRST_ASSUM (MP_TAC o MATCH_MP MATROID_SUBSET_CONTAINS_BASIS)] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"c:A->bool") STRIP_ASSUME_TAC) THEN
    MP_TAC (← ISPECL [← q r"m:A matroid", ← q r"c:A->bool", ← q r"b:A->bool"]
            MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE) THEN
    ANTS_TAC THENL [ASM SET_TAC [], STRIP_TAC] THEN
    MP_TAC (← ISPECL [← q r"m:A matroid", ← q r"s:A->bool", ← q r"c:A->bool"]
           MATROID_DIM_EQ_CARD_GEN) THEN
    ASM_SIMP_TAC [MATROID_SPAN_SUPERSET] THEN ASM_ARITH_TAC)

  let MATROID_DIM_FINITE_LE ← prove
   r"!(m:A matroid) s b n.
          FINITE b /\ CARD b <= n /\
          b SUBSET matroid_set m /\ s SUBSET matroid_span m b
          ==> matroid_finite_dim m s /\ matroid_dim m s <= n"
   (MESON_TAC [MATROID_DIM_LE, MATROID_FINITE_DIM])

  let MATROID_DIM_LE_CARD_GEN ← prove
   r"!(m:A matroid) s b.
          FINITE b /\
          b SUBSET matroid_set m /\ s SUBSET matroid_span m b
          ==> matroid_dim m s <= CARD b"
   (MESON_TAC [MATROID_DIM_LE, LE_REFL, HAS_SIZE])

  let MATROID_DIM_LE_CARD ← prove
   r"!(m:A matroid) s.
          FINITE s /\ s SUBSET matroid_set m ==> matroid_dim m s <= CARD s"
   (MESON_TAC [MATROID_DIM_LE_CARD_GEN, MATROID_SPAN_SUPERSET])

  let MATROID_DIMENSION_GE_FINITE_CARD ← prove
   r"!(m:A matroid) b.
          matroid_finite_dimensional m /\
          matroid_independent m b
          ==> FINITE b /\ CARD b <= matroid_dimension m"
   (ASM_MESON_TAC [MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE, matroid_basis,
                  MATROID_FINITE_DIMENSIONAL_BASIS, matroid_spanning,
                  MATROID_INDEPENDENT_IMP_SUBSET, MATROID_DIMENSION_EQ_CARD])

  let MATROID_DIMENSION_GE ← prove
   r"!(m:A matroid) b n.
          matroid_finite_dimensional m /\
          matroid_independent m b /\
          n <= CARD b
          ==> n <= matroid_dimension m"
   (MESON_TAC [MATROID_DIMENSION_GE_FINITE_CARD, LE_TRANS])

  let MATROID_DIMENSION_GE_CARD ← prove
   r"!(m:A matroid) b.
          matroid_finite_dimensional m /\ matroid_independent m b
          ==> CARD b <= matroid_dimension m"
   (MESON_TAC [MATROID_DIMENSION_GE_FINITE_CARD])

  let MATROID_DIM_GE_FINITE_CARD ← prove
   r"!(m:A matroid) s b.
          matroid_finite_dim m s /\ matroid_independent m b /\ b SUBSET s
          ==> FINITE b /\ CARD b <= matroid_dim m s"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [matroid_dim] THEN
    MATCH_MP_TAC MATROID_DIMENSION_GE_FINITE_CARD THEN
    ASM_MESON_TAC [matroid_finite_dim, MATROID_INDEPENDENT_SUBMATROID,
                  MATROID_SPAN_SUPERSET, SUBSET_TRANS])

  let MATROID_DIM_GE ← prove
   r"!(m:A matroid) s b n.
          matroid_finite_dim m s /\ matroid_independent m b /\
          b SUBSET s /\ n <= CARD b
          ==> n <= matroid_dim m s"
   (MESON_TAC [MATROID_DIM_GE_FINITE_CARD, LE_TRANS])

  let MATROID_DIM_GE_CARD_GEN ← prove
   r"!(m:A matroid) s b.
          matroid_finite_dim m s /\ matroid_independent m b /\ b SUBSET s
          ==> CARD b <= matroid_dim m s"
   (MESON_TAC [MATROID_DIM_GE_FINITE_CARD, LE_TRANS])

  let MATROID_DIM_GE_CARD ← prove
   r"!(m:A matroid) s.
          matroid_finite_dim m s /\ matroid_independent m s
          ==> CARD s <= matroid_dim m s"
   (MESON_TAC [MATROID_DIM_GE_CARD_GEN, SUBSET_REFL])

  let FINITE_IMP_MATROID_FINITE_DIM_SPAN ← prove
   r"!(m:A matroid) s.
          FINITE s /\ s SUBSET matroid_set m
          ==> matroid_finite_dim m (matroid_span m s)"
   (MESON_TAC [MATROID_FINITE_DIM_SPAN, FINITE_IMP_MATROID_FINITE_DIM])

  let MATROID_INDEPENDENT_IMP_FINITE ← prove
   r"!(m:A matroid) s.
          matroid_finite_dim m s /\ matroid_independent m s
          ==> FINITE s"
   (MESON_TAC [MATROID_DIM_GE_FINITE_CARD, SUBSET_REFL])

  -- @@RETURN BEGIN
  return { MATROID_DIMENSION_ALT, MATROID_DIM_BASIS, MATROID_DIM_ALT,
           MATROID_DIMENSION_UNIQUE, MATROID_DIMENSION_EQ_CARD, MATROID_DIM_UNIQUE_ALT,
           MATROID_DIM_UNIQUE, MATROID_SPAN_DIM_EQ, MATROID_SPAN_INSERT_REFL,
           MATROID_BASIS_EXISTS_DIMENSION, MATROID_BASIS_EXISTS_DIM,
           MATROID_CONTAINS_BASIS_DIM, MATROID_DIM_EQ_CARD_GEN, MATROID_DIM_EQ_CARD,
           MATROID_DIMENSION_LE, MATROID_DIMENSION_FINITE_LE, MATROID_DIM_LE,
           MATROID_DIM_FINITE_LE, MATROID_DIM_LE_CARD_GEN, MATROID_DIM_LE_CARD,
           MATROID_DIMENSION_GE_FINITE_CARD, MATROID_DIMENSION_GE,
           MATROID_DIMENSION_GE_CARD, MATROID_DIM_GE_FINITE_CARD, MATROID_DIM_GE,
           MATROID_DIM_GE_CARD_GEN, MATROID_DIM_GE_CARD,
           FINITE_IMP_MATROID_FINITE_DIM_SPAN, MATROID_INDEPENDENT_IMP_FINITE }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Monotonicity, equality of spans via dimension, choosing subsets and       -/
/- subspaces, extending low-dimensional subsets.  (matroids.ml 1472-1677)    -/
/- ------------------------------------------------------------------------- -/

structure DimSpan where
  -- @@FIELDS
  MATROID_DIM_EQ_FINITE_CARD_EQ : thm
  MATROID_DIM_GE_FINITE_CARD_EQ : thm
  MATROID_DIM_EMPTY : thm
  MATROID_DIM_INSERT : thm
  MATROID_DIM_SUBSET : thm
  MATROID_DIM_SUBSET_ALT : thm
  MATROID_DIM_SPAN_SUBSET : thm
  MATROID_DIM_SPAN_PSUBSET : thm
  MATROID_DIM_SPAN_EQ_GEN : thm
  MATROID_DIM_SPAN_EQ : thm
  MATROID_DIM_EQ_SPAN : thm
  MATROID_CHOOSE_SUBSET : thm
  MATROID_CHOOSE_SUBSPACE : thm
  MATROID_LOWDIM_EXPAND_BASIS : thm
  MATROID_LOWDIM_EXPAND_DIMENSION : thm
  deriving Inhabited

@[nospecialize]
def setupDimSpan [HolBase] (D : MatroidsDeps) (BMatroidType : MatroidType) (BLinearNotions : LinearNotions) (BIndependentSets : IndependentSets) (BSubspaces : Subspaces) (BSubmatroids : Submatroids) (BFiniteDim : FiniteDim) (BDimension : Dimension) :
    ExceptT String IO DimSpan := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, MESON_TAC, SET_TAC, .. } := D
  let { ADD1, AND_FORALL_THM, CARD_CLAUSES, CARD_PSUBSET, CHOOSE_SUBSET_BETWEEN,
        CHOOSE_SUBSET_STRONG, EMPTY_SUBSET, FINITE_INSERT, FINITE_RULES, FINITE_SUBSET,
        HAS_SIZE, INSERT_SUBSET, LEFT_IMP_EXISTS_THM, LE_REFL, LE_TRANS, LTE_TRANS,
        LT_REFL, MONO_EXISTS, NOT_LT, PSUBSET, PSUBSET_ALT, SUBSET, .. } := D.core1
  let { SUBSET_REFL, SUBSET_TRANS, .. } := D.core2
  let { MATROID_SPAN_INC, MATROID_SPAN_MINIMAL, MATROID_SPAN_MONO, MATROID_SPAN_SUBSET,
        MATROID_SPAN_SUPERSET, .. } := BMatroidType
  let { MATROID_BASIS_IMP_SUBSET, MATROID_INDEPENDENT_IMP_SUBSET, matroid_basis, .. } := BLinearNotions
  let { MATROID_BASIS_EQ_MINIMAL_SPANNING, MATROID_INDEPENDENT_EMPTY,
        MATROID_INDEPENDENT_EXTENDS_TO_BASIS, MATROID_INDEPENDENT_INSERT,
        MATROID_INDEPENDENT_MONO, .. } := BIndependentSets
  let { MATROID_SUBSPACE_SPAN, .. } := BSubspaces
  let { MATROID_BASIS_SUBMATROID, MATROID_SPANNING_SUBMATROID,
        MATROID_SUBSET_CONTAINS_BASIS, .. } := BSubmatroids
  let { FINITE_IMP_MATROID_FINITE_DIM, MATROID_DIM_SPAN, MATROID_FINITE_DIM_BASIS,
        MATROID_FINITE_DIM_IMP_SUBSET, MATROID_FINITE_DIM_MONO,
        MATROID_FINITE_DIM_SPAN, matroid_finite_dimensional, .. } := BFiniteDim
  let { MATROID_CONTAINS_BASIS_DIM, MATROID_DIMENSION_UNIQUE, MATROID_DIM_EQ_CARD,
        MATROID_DIM_FINITE_LE, MATROID_DIM_LE_CARD_GEN, MATROID_DIM_UNIQUE,
        MATROID_INDEPENDENT_IMP_FINITE, MATROID_SPAN_DIM_EQ, MATROID_SPAN_INSERT_REFL, .. } := BDimension
  -- @@SCOPE END

  let (MATROID_DIM_EQ_FINITE_CARD_EQ, MATROID_DIM_GE_FINITE_CARD_EQ) ←
    CONJ_PAIR (← prove
   r"(!m s:A->bool.
          s SUBSET matroid_set m /\ FINITE s /\ matroid_dim m s = CARD s <=>
          matroid_finite_dim m s /\ matroid_independent m s) /\
     (!m s:A->bool.
          s SUBSET matroid_set m /\ FINITE s /\ CARD s <= matroid_dim m s <=>
          matroid_finite_dim m s /\ matroid_independent m s)"
   (← do
    let t1 ← TAUT (← q
     r"(p ==> q) /\ (r ==> p) /\ (q ==> r) ==> (p <=> r) /\ (q <=> r)")
    pure (REWRITE_TAC [AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
    MATCH_MP_TAC t1 THEN
    SIMP_TAC [LE_REFL] THEN CONJ_TAC THENL
     [MESON_TAC [MATROID_FINITE_DIM_IMP_SUBSET, MATROID_INDEPENDENT_IMP_FINITE,
                SUBSET_REFL, MATROID_DIM_EQ_CARD],
      STRIP_TAC THEN ASM_SIMP_TAC [FINITE_IMP_MATROID_FINITE_DIM]] THEN
    MP_TAC (← ISPECL [← q r"submatroid m (s:A->bool)", ← q r"s:A->bool"]
          MATROID_BASIS_EQ_MINIMAL_SPANNING) THEN
    ASM_SIMP_TAC [MATROID_BASIS_SUBMATROID, MATROID_SPANNING_SUBMATROID,
                 MATROID_SPAN_SUPERSET] THEN
    DISCH_THEN (K ALL_TAC) THEN X_GEN_TAC (← q r"t:A->bool") THEN REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"m:A matroid", ← q r"s:A->bool", ← q r"t:A->bool"]
      MATROID_DIM_LE_CARD_GEN) THEN
    ASM_MESON_TAC [MATROID_SPAN_SUPERSET, SUBSET, PSUBSET, FINITE_SUBSET,
                  CARD_PSUBSET, NOT_LT, LE_TRANS])))

  let MATROID_DIM_EMPTY ← prove
   r"!m:A matroid. matroid_dim m {} = 0"
   (GEN_TAC THEN MATCH_MP_TAC MATROID_DIM_UNIQUE THEN
    EXISTS_TAC (← q r"{}:A->bool") THEN
    REWRITE_TAC [MATROID_INDEPENDENT_EMPTY, HAS_SIZE, FINITE_RULES, CARD_CLAUSES,
                EMPTY_SUBSET])

  let MATROID_DIM_INSERT ← prove
   r"!m s x:A.
          matroid_finite_dim m s /\ x IN matroid_set m
          ==> matroid_dim m (x INSERT s) =
              if x IN matroid_span m s then matroid_dim m s
              else matroid_dim m s + 1"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP MATROID_FINITE_DIM_IMP_SUBSET) THEN
    COND_CASES_TAC THENL
     [ASM_MESON_TAC [MATROID_SPAN_INSERT_REFL, MATROID_SPAN_DIM_EQ,
                    INSERT_SUBSET, MATROID_SPAN_SUBSET, SUBSET],
      FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE I [MATROID_CONTAINS_BASIS_DIM])] THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM, HAS_SIZE] THEN
    X_GEN_TAC (← q r"b:A->bool") THEN STRIP_TAC THEN
    MATCH_MP_TAC MATROID_DIM_UNIQUE THEN EXISTS_TAC (← q r"(x:A) INSERT b") THEN
    ASM_REWRITE_TAC [HAS_SIZE, FINITE_INSERT, MATROID_INDEPENDENT_INSERT] THEN
    CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    ASM_SIMP_TAC [CARD_CLAUSES, INSERT_SUBSET] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THENL
     [ASM_MESON_TAC [MATROID_SPAN_SUPERSET, SUBSET], REWRITE_TAC [ADD1]] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MATROID_SPAN_INC THEN ASM SET_TAC [], ALL_TAC] THEN
    TRANS_TAC SUBSET_TRANS (← q r"matroid_span m b:A->bool") THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC [MATROID_SPAN_SUPERSET],
      MATCH_MP_TAC MATROID_SPAN_MONO THEN ASM SET_TAC []])

  let MATROID_DIM_SUBSET ← prove
   r"!m s t:A->bool.
          s SUBSET t /\ matroid_finite_dim m t
          ==> matroid_dim m s <= matroid_dim m t"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [MATROID_FINITE_DIM_BASIS]) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN (← q r"b:A->bool") (STRIP_ASSUME_TAC o GSYM))) THEN
    MP_TAC (← ISPECL [← q r"m:A matroid", ← q r"s:A->bool", ← q r"b:A->bool", ← q r"CARD(b:A->bool)"]
          MATROID_DIM_FINITE_LE) THEN
    MP_TAC (← ISPECL [← q r"m:A matroid", ← q r"b:A->bool"] MATROID_DIM_EQ_CARD) THEN
    MP_TAC (← ISPECL [← q r"m:A matroid", ← q r"t:A->bool"] MATROID_DIM_SPAN) THEN
    ASM_REWRITE_TAC [LE_REFL] THEN
    ASM SET_TAC [MATROID_DIM_SPAN, MATROID_SPAN_SUPERSET])

  let MATROID_DIM_SUBSET_ALT ← prove
   r"!m s t:A->bool.
          s SUBSET matroid_span m t /\ matroid_finite_dim m t
          ==> matroid_dim m s <= matroid_dim m t"
   (MESON_TAC [MATROID_DIM_SUBSET, MATROID_FINITE_DIM_SPAN, MATROID_DIM_SPAN,
              MATROID_FINITE_DIM_IMP_SUBSET])

  let MATROID_DIM_SPAN_SUBSET ← prove
   r"!m s t:A->bool.
          s SUBSET matroid_set m /\
          matroid_span m s SUBSET matroid_span m t /\
          matroid_finite_dim m t
          ==> matroid_dim m s <= matroid_dim m t"
   (MESON_TAC [MATROID_SPAN_MINIMAL, MATROID_DIM_SPAN, MATROID_DIM_SUBSET_ALT,
              MATROID_FINITE_DIM_IMP_SUBSET])

  let MATROID_DIM_SPAN_PSUBSET ← prove
   r"!m s t:A->bool.
          s SUBSET matroid_set m /\
          matroid_span m s PSUBSET matroid_span m t /\
          matroid_finite_dim m t
          ==> matroid_dim m s < matroid_dim m t"
   (← do
    let a1 ← ARITH_RULE (← q r"n < n + 1")
    pure (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP MATROID_FINITE_DIM_IMP_SUBSET) THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [PSUBSET_ALT]) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN (← q r"a:A") STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN (← q r"matroid_finite_dim m (s:A->bool)") ASSUME_TAC THENL
     [ASM_MESON_TAC [MATROID_FINITE_DIM_SPAN, MATROID_FINITE_DIM_MONO],
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"(a:A) IN matroid_set m") THENL
     [ALL_TAC, ASM_MESON_TAC [MATROID_SPAN_SUBSET, SUBSET]] THEN
    TRANS_TAC LTE_TRANS (← q r"matroid_dim m ((a:A) INSERT s)") THEN CONJ_TAC THENL
     [ASM_SIMP_TAC [MATROID_DIM_INSERT, a1], ALL_TAC] THEN
    TRANS_TAC LE_TRANS (← q r"matroid_dim m (matroid_span m t:A->bool)") THEN
    CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC [MATROID_DIM_SPAN, LE_REFL]] THEN
    MATCH_MP_TAC MATROID_DIM_SUBSET THEN
    ASM_SIMP_TAC [MATROID_FINITE_DIM_SPAN, INSERT_SUBSET] THEN
    ASM_MESON_TAC [MATROID_SPAN_SUPERSET, SUBSET_TRANS]))

  let MATROID_DIM_SPAN_EQ_GEN ← prove
   r"!m s t:A->bool.
          s SUBSET matroid_set m /\ matroid_finite_dim m t /\
          matroid_span m s SUBSET matroid_span m t /\
          matroid_dim m t <= matroid_dim m s
          ==> matroid_span m s = matroid_span m t"
   (MESON_TAC [MATROID_DIM_SPAN_PSUBSET, PSUBSET, NOT_LT])

  let MATROID_DIM_SPAN_EQ ← prove
   r"!m s t:A->bool.
          s SUBSET matroid_set m /\ matroid_finite_dim m t /\
          matroid_span m s SUBSET matroid_span m t /\
          matroid_dim m s = matroid_dim m t
          ==> matroid_span m s = matroid_span m t"
   (MESON_TAC [MATROID_DIM_SPAN_PSUBSET, PSUBSET, LT_REFL])

  let MATROID_DIM_EQ_SPAN ← prove
   r"!m s t:A->bool.
       matroid_finite_dim m t /\ s SUBSET t /\ matroid_dim m t <= matroid_dim m s
       ==> matroid_span m s = matroid_span m t"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC MATROID_DIM_SPAN_EQ_GEN THEN
    ASM_MESON_TAC [MATROID_SPAN_MONO, MATROID_FINITE_DIM_IMP_SUBSET, SUBSET])

  let MATROID_CHOOSE_SUBSET ← prove
   r"!(m:A matroid) s n.
          s SUBSET matroid_set m /\
          (matroid_finite_dim m s ==> n <= matroid_dim m s)
          ==> ?t. t SUBSET s /\ matroid_independent m t /\ t HAS_SIZE n"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (X_CHOOSE_THEN (← q r"b:A->bool") STRIP_ASSUME_TAC o MATCH_MP
      MATROID_SUBSET_CONTAINS_BASIS) THEN
    MP_TAC (← ISPECL [← q r"n:num", ← q r"b:A->bool"] CHOOSE_SUBSET_STRONG) THEN ANTS_TAC
    THENL [DISCH_TAC, ASM_MESON_TAC [MATROID_INDEPENDENT_MONO, SUBSET]] THEN
    ASM_SIMP_TAC [← GSYM MATROID_DIM_EQ_CARD] THEN
    ASM_MESON_TAC [MATROID_FINITE_DIM_BASIS, MATROID_SPAN_DIM_EQ, SUBSET])

  let MATROID_CHOOSE_SUBSPACE ← prove
   r"!(m:A matroid) s n.
          s SUBSET matroid_set m /\
          (matroid_finite_dim m s ==> n <= matroid_dim m s)
          ==> ?t. matroid_subspace m t /\ t SUBSET matroid_span m s /\
                  matroid_finite_dim m t /\ matroid_dim m t = n"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (X_CHOOSE_THEN (← q r"b:A->bool") STRIP_ASSUME_TAC o
      REWRITE_RULE [HAS_SIZE] o MATCH_MP MATROID_CHOOSE_SUBSET) THEN
    EXISTS_TAC (← q r"matroid_span m b:A->bool") THEN
    SUBGOAL_THEN (← q r"(b:A->bool) SUBSET matroid_set m") ASSUME_TAC THENL
     [ASM SET_TAC [], ALL_TAC] THEN
    ASM_SIMP_TAC [MATROID_SUBSPACE_SPAN, MATROID_SPAN_MONO, MATROID_DIM_EQ_CARD,
     MATROID_FINITE_DIM_SPAN, MATROID_DIM_SPAN, FINITE_IMP_MATROID_FINITE_DIM])

  let MATROID_LOWDIM_EXPAND_BASIS ← prove
   r"!m (s:A->bool) n.
          matroid_finite_dim m s /\ matroid_dim m s <= n /\
          (matroid_finite_dimensional m ==> n <= matroid_dimension m)
          ==> ?b. b HAS_SIZE n /\ matroid_independent m b /\
                  matroid_span m s SUBSET matroid_span m b"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC o
      GEN_REWRITE_RULE I [MATROID_FINITE_DIM_BASIS]) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"b:A->bool") STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM (X_CHOOSE_THEN (← q r"d:A->bool") STRIP_ASSUME_TAC o
          MATCH_MP MATROID_INDEPENDENT_EXTENDS_TO_BASIS) THEN
    MP_TAC (← ISPECL [← q r"n:num", ← q r"b:A->bool", ← q r"d:A->bool"]
          CHOOSE_SUBSET_BETWEEN) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC [MATROID_DIM_EQ_CARD, MATROID_SPAN_DIM_EQ, SUBSET],
        DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o check (is_imp ∘ concl))] THEN
      ANTS_TAC THENL
       [ASM_MESON_TAC [matroid_finite_dimensional, matroid_basis],
        ASM_MESON_TAC [MATROID_DIMENSION_UNIQUE, HAS_SIZE]],
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"c:A->bool") THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [ASM_MESON_TAC [matroid_basis, MATROID_INDEPENDENT_MONO],
        ASM_MESON_TAC [MATROID_SPAN_MONO, SUBSET, MATROID_BASIS_IMP_SUBSET]]])

  let MATROID_LOWDIM_EXPAND_DIMENSION ← prove
   r"!m (s:A->bool) n.
          matroid_finite_dim m s /\ matroid_dim m s <= n /\
          (matroid_finite_dimensional m ==> n <= matroid_dimension m)
          ==> ?t. matroid_finite_dim m t /\ matroid_dim m t = n /\
                  matroid_span m s SUBSET matroid_span m t"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP MATROID_LOWDIM_EXPAND_BASIS) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"t:A->bool") THEN
    REWRITE_TAC [HAS_SIZE] THEN STRIP_TAC THEN
    ASM_SIMP_TAC [MATROID_DIM_EQ_CARD, FINITE_IMP_MATROID_FINITE_DIM,
                 MATROID_INDEPENDENT_IMP_SUBSET])

  -- @@RETURN BEGIN
  return { MATROID_DIM_EQ_FINITE_CARD_EQ, MATROID_DIM_GE_FINITE_CARD_EQ,
           MATROID_DIM_EMPTY, MATROID_DIM_INSERT, MATROID_DIM_SUBSET,
           MATROID_DIM_SUBSET_ALT, MATROID_DIM_SPAN_SUBSET, MATROID_DIM_SPAN_PSUBSET,
           MATROID_DIM_SPAN_EQ_GEN, MATROID_DIM_SPAN_EQ, MATROID_DIM_EQ_SPAN,
           MATROID_CHOOSE_SUBSET, MATROID_CHOOSE_SUBSPACE, MATROID_LOWDIM_EXPAND_BASIS,
           MATROID_LOWDIM_EXPAND_DIMENSION }
  -- @@RETURN END

end HolLibrary.Matroids
