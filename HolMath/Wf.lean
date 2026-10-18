/- File: Wf.lean
Theory of wellfounded relations.
John Harrison, University of Cambridge Computer Laboratory
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Lean4 translation by Chris Walton 2026 -/

import HolCore.Bool
import HolCore.Equal
import HolCore.Drule
import HolCore.Tactics
import HolCore.Itab
import HolCore.Simp
import HolCore.Parser
import HolCore.Printer
import HolCore.Theorems
import HolCore.IndDefs
import HolCore.Classic
import HolCore.Canon
import HolCore.Meson
import HolCore.ImpConv
import HolMath.Pair
import HolMath.Nums
import HolMath.Recursion
import HolMath.Arith
import HolMath.Base

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand)
open HolCore.Bool (BoolThms list_mk_forall)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax

namespace HolMath.Wf

/-- Parse a term in the `ExceptT String IO` monad. -/
private def pt (s : String) : ExceptT String IO term := parse_term s

/- ---------------------------------------------------------------------- -/
/- Definition of wellfoundedness for arbitrary (infix) relation <<        -/
/- ---------------------------------------------------------------------- -/

/-- Register `wf.ml`'s two relation infixes.  The OCaml declares `<<` at the top
    of the file and `<<<` further down (just before `WF_SUBSET`); registering
    both up front is equivalent, since the two are independent. -/
def setupWfInfixes : IO Unit := do
  HolCore.Printer.parse_as_infix ("<<", (12, "right"))
  HolCore.Printer.parse_as_infix ("<<<", (12, "right"))

/- ---------------------------------------------------------------------- -/
/- The theorems established by this layer.                                -/
/- ---------------------------------------------------------------------- -/

/-- The `wf.ml` theorems. -/
structure WfThms where
  WF                   : thm
  WF_EQ                : thm
  WF_IND               : thm
  WF_DCHAIN            : thm
  WF_DCHAIN_TRANSITIVE : thm
  WF_UREC              : thm
  WF_UREC_WF           : thm
  WF_REC_INVARIANT     : thm
  WF_REC               : thm
  WF_REC_WF            : thm
  WF_EREC              : thm
  WF_REC_EXISTS        : thm
  WF_SUBSET            : thm
  WF_RESTRICT          : thm
  WF_MEASURE_GEN       : thm
  WF_LEX_DEPENDENT     : thm
  WF_LEX               : thm
  WF_POINTWISE         : thm
  WF_num               : thm
  WF_REC_num           : thm
  MEASURE              : thm
  WF_MEASURE           : thm
  MEASURE_LE           : thm
  WF_ANTISYM           : thm
  WF_REFL              : thm
  WF_FALSE             : thm
  MINIMAL_BAD_SEQUENCE : thm
  WF_REC_TAIL          : thm
  WF_REC_TAIL_GENERAL  : thm
  deriving Inhabited

/-- Establish the `wf.ml` layer: one `let` per OCaml `let`, in file order
    (see HolMath/Base.lean for the conventions).  `new_definition`,
    `prove_recursive_functions_exist`, `prove_inductive_relations_exist` and
    `SELECT_CONV` are passed in because they need session state. -/
@[nospecialize]
def setupWf [HolBase]
    (new_definition' : term → IO (Except String thm))
    (A2 : HolMath.Arith.ArithThms2) (A3 : HolMath.Arith.ArithThms3)
    (A4 : HolMath.Arith.ArithThms4)
    (A9 : HolMath.Arith.ArithThms9)
    (N : HolMath.Nums.NumsThms)
    (Pr : HolMath.Pair.PairThms)
    (ETA_AX : thm)
    (MESON_TAC ASM_MESON_TAC : List thm → tactic)
    (prove_recursive_functions_exist' : thm → term → IO (Except String thm))
    (prove_inductive_relations_exist' : term → IO (Except String thm))
    (SELECT_CONV' : term → Except String thm) :
    ExceptT String IO WfThms := do
  let new_definition (s : String) : ExceptT String IO thm := do
    ExceptT.mk (new_definition' (← q s))
  let prove_recursive_functions_exist (th : thm) (t : term) : ExceptT String IO thm :=
    ExceptT.mk (prove_recursive_functions_exist' th t)
  let prove_inductive_relations_exist (t : term) : ExceptT String IO thm :=
    ExceptT.mk (prove_inductive_relations_exist' t)
  let SELECT_CONV : ioconv := fun t => pure (SELECT_CONV' t)
  -- meson.ml: `let MESON ths tm = prove(tm,MESON_TAC ths)`
  let MESON (ths : List thm) (tm : term) : ExceptT String IO thm :=
    ExceptT.mk (Tactics.prove HolBase.B tm (MESON_TAC ths))
  let INDUCT_TAC := HolMath.Nums.INDUCT_TAC N.num_INDUCTION
  let { MONO_EXISTS, LEFT_IMP_EXISTS_THM, IMP_CONJ, FORALL_AND_THM,
        RIGHT_FORALL_IMP_THM, MONO_FORALL, .. } := HolBase.T
  let { SKOLEM_THM, NOT_IMP, FUN_EQ_THM, SELECT_UNIQUE, NOT_FORALL_THM, .. } := HolBase.C
  let { LT, LT_0, LT_SUC, .. } := A2
  let { NOT_LE, LTE_TRANS, LT_REFL, .. } := A3
  let { num_WOP, num_WF, .. } := A4
  let { TRANSITIVE_STEPWISE_LT, .. } := A9
  let { num_RECURSION, num_CASES, NOT_SUC, .. } := N
  let { FORALL_PAIR_THM, .. } := Pr

  /- ---------------------------------------------------------------------- -/
  /- Definition of wellfoundedness for arbitrary (infix) relation <<        -/
  /- (`parse_as_infix("<<",(12,"right"))` is run first: setupWfInfixes.)    -/
  /- ---------------------------------------------------------------------- -/

  let WF ← new_definition
    r"WF(<<) <=> !P:A->bool. (?x. P(x)) ==> (?x. P(x) /\ !y. y << x ==> ~P(y))"

  /- ---------------------------------------------------------------------- -/
  /- Strengthen it to equality.                                             -/
  /- ---------------------------------------------------------------------- -/

  let WF_EQ ← prove
   r"WF(<<) <=> !P:A->bool. (?x. P(x)) <=> (?x. P(x) /\ !y. y << x ==> ~P(y))"
   (REWRITE_TAC [WF] THEN MESON_TAC [])

  /- ---------------------------------------------------------------------- -/
  /- Equivalence of wellfounded induction.                                  -/
  /- ---------------------------------------------------------------------- -/

  let WF_IND ← prove
   r"WF(<<) <=> !P:A->bool. (!x. (!y. y << x ==> P(y)) ==> P(x)) ==> !x. P(x)"
   (REWRITE_TAC [WF] THEN EQ_TAC THEN DISCH_TAC THEN GEN_TAC THEN
    POP_ASSUM (MP_TAC o SPEC (← q r"\x:A. ~P(x)")) THEN REWRITE_TAC [] THEN MESON_TAC [])

  /- ---------------------------------------------------------------------- -/
  /- Equivalence of the "infinite descending chains" version.               -/
  /- ---------------------------------------------------------------------- -/

  let WF_DCHAIN ← prove
   r"WF(<<) <=> ~(?s:num->A. !n. s(SUC n) << s(n))"
   (REWRITE_TAC [WF, ← TAUT (← q r"(a <=> ~b) <=> (~a <=> b)"), NOT_FORALL_THM] THEN
    EQ_TAC THEN DISCH_THEN CHOOSE_TAC THENL
     [POP_ASSUM (MP_TAC o REWRITE_RULE [NOT_IMP]) THEN
      DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q r"a:A")) ASSUME_TAC) THEN
      SUBGOAL_THEN (← q r"!x:A. ?y. P(x) ==> P(y) /\ y << x") MP_TAC THENL
       [ASM_MESON_TAC [], REWRITE_TAC [SKOLEM_THM]] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"f:A->A") STRIP_ASSUME_TAC) THEN
      CHOOSE_TAC (← prove_recursive_functions_exist num_RECURSION
       (← q r"(s(0) = a:A) /\ (!n. s(SUC n) = f(s n))")) THEN
      EXISTS_TAC (← q r"s:num->A") THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"!n. P(s n) /\ s(SUC n):A << s(n)")
        (fun th => ASM_MESON_TAC [th]) THEN
      INDUCT_TAC THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [],
      EXISTS_TAC (← q r"\y:A. ?n:num. y = s(n)") THEN REWRITE_TAC [] THEN
      ASM_MESON_TAC []])

  -- OCaml `WF_DHAIN_TRANSITIVE`: a typo for WF_DCHAIN_TRANSITIVE, the name
  -- used here (only database.ml's name index uses the typo).
  let WF_DCHAIN_TRANSITIVE ← prove
   r"!(<<):A->A->bool.
        (!x y z. x << y /\ y << z ==> x << z)
        ==> (WF(<<) <=> ~(?s:num->A. !i j. i < j ==> s j << s i))"
   (GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [WF_DCHAIN] THEN
    AP_TERM_TAC THEN EQ_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC (← q r"s:num->A") THEN SIMP_TAC [LT] THEN DISCH_TAC THEN
    MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN ASM_MESON_TAC [])

  /- ---------------------------------------------------------------------- -/
  /- Equivalent to just *uniqueness* part of recursion.                     -/
  /- ---------------------------------------------------------------------- -/

  let WF_UREC ← prove
   r"WF(<<) ==>
       !H. (!f g x. (!z. z << x ==> (f z = g z)) ==> (H f x = H g x))
            ==> !(f:A->B) g. (!x. f x = H f x) /\ (!x. g x = H g x)
                              ==> (f = g)"
   (REWRITE_TAC [WF_IND] THEN REPEAT STRIP_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN GEN_TAC THEN
    DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN ASM_REWRITE_TAC [])

  let WF_UREC_WF ← prove
   r"(!H. (!f g x. (!z. z << x ==> (f z = g z)) ==> (H f x = H g x))
        ==> !(f:A->bool) g. (!x. f x = H f x) /\ (!x. g x = H g x)
                          ==> (f = g))
   ==> WF(<<)"
   (REWRITE_TAC [WF_IND] THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"\f x. P(x:A) \/ !z:A. z << x ==> f(z)")) THEN
    REWRITE_TAC [] THEN
    -- W(C SUBGOAL_THEN (fun t -> REWRITE_TAC[t]) o funpow 2 lhand o snd)
    W ((fun tm => SUBGOAL_THEN tm (fun t => REWRITE_TAC [t])) o (lhand o lhand) o snd) THENL
     [MESON_TAC [], DISCH_THEN (MP_TAC o SPECL [← q r"P:A->bool", ← q r"\x:A. T"]) THEN
      REWRITE_TAC [FUN_EQ_THM] THEN ASM_MESON_TAC []])

  /- ---------------------------------------------------------------------- -/
  /- Stronger form of recursion with "inductive invariant" (Krstic/Matthews).-/
  /- ---------------------------------------------------------------------- -/

  let WF_REC_INVARIANT ← prove
   r"WF(<<)
   ==> !H S. (!f g x. (!z. z << x ==> (f z = g z) /\ S z (f z))
                      ==> (H f x = H g x) /\ S x (H f x))
             ==> ?f:A->B. !x. (f x = H f x)"
   (← do
    let lemma ← prove_inductive_relations_exist
      (← q r"!f:A->B x. (!z. z << x ==> R z (f z)) ==> R x (H f x)")
    pure
     (REWRITE_TAC [WF_IND] THEN REPEAT STRIP_TAC THEN
      X_CHOOSE_THEN (← q r"R:A->B->bool") STRIP_ASSUME_TAC lemma THEN
      SUBGOAL_THEN (← q r"!x:A. ?!y:B. R x y") (fun th => ASM_MESON_TAC [th]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM (fun th => GEN_REWRITE_TAC BINDER_CONV [th]) THEN
      SUBGOAL_THEN (← q r"!x:A y:B. R x y ==> S x y") MP_TAC THEN ASM_MESON_TAC []))

  /- ---------------------------------------------------------------------- -/
  /- Equivalent to just *existence* part of recursion.                      -/
  /- ---------------------------------------------------------------------- -/

  let WF_REC ← prove
   r"WF(<<)
   ==> !H. (!f g x. (!z. z << x ==> (f z = g z)) ==> (H f x = H g x))
           ==> ?f:A->B. !x. f x = H f x"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP WF_REC_INVARIANT) THEN
    EXISTS_TAC (← q r"\x:A y:B. T") THEN ASM_REWRITE_TAC [])

  let WF_REC_WF ← prove
   r"(!H. (!f g x. (!z. z << x ==> (f z = g z)) ==> (H f x = H g x))
                 ==> ?f:A->num. !x. f x = H f x)
   ==> WF(<<)"
   (DISCH_TAC THEN REWRITE_TAC [WF_DCHAIN] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"x:num->A")) THEN
    SUBGOAL_THEN (← q r"!n. (x:num->A)(@m. x(m) << x(n)) << x(n)") ASSUME_TAC THENL
     [CONV_TAC (BINDER_CONV SELECT_CONV) THEN ASM_MESON_TAC [], ALL_TAC] THEN
    FIRST_ASSUM (MP_TAC o SPEC
     (← q r"\f:A->num. \y:A. if ?p:num. y = x(p)
                       then SUC(f(x(@m. x(m) << y)))
                       else 0")) THEN
    REWRITE_TAC [NOT_IMP] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [] THEN
      FIRST_ASSUM (X_CHOOSE_THEN (← q r"p:num") SUBST_ALL_TAC) THEN
      AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      FIRST_ASSUM MATCH_ACCEPT_TAC, ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"f:A->num") MP_TAC) THEN
    DISCH_THEN (MP_TAC o GEN (← q r"n:num") o SPEC (← q r"(x:num->A) n")) THEN
    SUBGOAL_THEN (← q r"!n. ?p. (x:num->A) n = x p") (fun th => REWRITE_TAC [th]) THENL
     [MESON_TAC [], DISCH_TAC] THEN
    SUBGOAL_THEN (← q r"!n:num. ?k. f(x(k):A) < f(x(n))") ASSUME_TAC THENL
     [GEN_TAC THEN EXISTS_TAC (← q r"@m:num. x(m):A << x(n)") THEN
      FIRST_ASSUM (fun th => GEN_REWRITE_TAC RAND_CONV [th]) THEN REWRITE_TAC [LT],
      MP_TAC (← SPEC (← q r"\n:num. ?i:num. n = f(x(i):A)") num_WOP) THEN
      REWRITE_TAC [] THEN ASM_MESON_TAC []])

  /- ---------------------------------------------------------------------- -/
  /- Combine the two versions of the recursion theorem.                     -/
  /- ---------------------------------------------------------------------- -/

  let WF_EREC ← prove
   r"WF(<<) ==>
       !H. (!f g x. (!z. z << x ==> (f z = g z)) ==> (H f x = H g x))
            ==> ?!f:A->B. !x. f x = H f x"
   (MESON_TAC [WF_REC, WF_UREC])

  /- ---------------------------------------------------------------------- -/
  /- Defining a recursive function via an existence condition.              -/
  /- ---------------------------------------------------------------------- -/

  let WF_REC_EXISTS ← prove
   r"WF((<<):A->A->bool)
   ==> !P. (!f g x y. (!z. z << x ==> f z = g z) ==> (P f x y <=> P g x y)) /\
           (!f x. (!z. z << x ==> P f z (f z)) ==> ?y. P f x y)
           ==> ?f:A->B. !x. P f x (f x)"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"?f:A->B. !x. f x = @y. P f x y") MP_TAC THENL
     [FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP WF_REC) THEN
      REPEAT STRIP_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"f:A->B") THEN
      DISCH_THEN (fun th => tactic_of do pure (
        ONCE_REWRITE_TAC [th] THEN ASSUME_TAC (← GSYM th))) THEN
      CONV_TAC (BINDER_CONV SELECT_CONV) THEN
      FIRST_ASSUM (MATCH_MP_TAC o GEN_REWRITE_RULE I [WF_IND]) THEN
      ASM_MESON_TAC []])

  /- ---------------------------------------------------------------------- -/
  /- Some preservation theorems for wellfoundedness.                        -/
  /- (`parse_as_infix("<<<",(12,"right"))`: setupWfInfixes.)                -/
  /- ---------------------------------------------------------------------- -/

  let WF_SUBSET ← prove
   r"!(<<) (<<<). (!(x:A) y. x << y ==> x <<< y) /\ WF(<<<) ==> WF(<<)"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN REWRITE_TAC [WF] THEN
    DISCH_TAC THEN GEN_TAC THEN DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN
    UNDISCH_TAC (← q r"!(x:A) (y:A). x << y ==> x <<< y") THEN MESON_TAC [])

  let WF_RESTRICT ← prove
   r"!(<<) P:A->bool. WF(<<) ==> WF(\x y. P x /\ P y /\ x << y)"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] WF_SUBSET) THEN
    SIMP_TAC [])

  let WF_MEASURE_GEN ← prove
   r"!(<<) (m:A->B). WF(<<) ==> WF(\x x'. m x << m x')"
   (REPEAT GEN_TAC THEN REWRITE_TAC [WF_IND] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q r"\y:B. !x:A. (m(x) = y) ==> P x")) THEN
    UNDISCH_TAC (← q r"!x. (!y. (m:A->B) y << m x ==> P y) ==> P x") THEN
    REWRITE_TAC [] THEN MESON_TAC [])

  let WF_LEX_DEPENDENT ← prove
   r"!R:A->A->bool S:A->B->B->bool. WF(R) /\ (!a. WF(S a))
         ==> WF(\(r1,s1) (r2,s2). R r1 r2 \/ (r1 = r2) /\ S r1 s1 s2)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [WF] THEN STRIP_TAC THEN
    X_GEN_TAC (← q r"P:A#B->bool") THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"a0:A", ← q r"b0:B"] THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"\a:A. ?b:B. P(a,b)")) THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    DISCH_THEN (MP_TAC o SPECL [← q r"a0:A", ← q r"b0:B"]) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"a:A") (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"b1:B")) THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"a:A", ← q r"\b. (P:A#B->bool) (a,b)"]) THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"b1:B")) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"b:B") (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    DISCH_TAC THEN EXISTS_TAC (← q r"(a:A,b:B)") THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [FORALL_PAIR_THM] THEN ASM_MESON_TAC [])

  let WF_LEX ← prove
   r"!R:A->A->bool S:B->B->bool. WF(R) /\ WF(S)
         ==> WF(\(r1,s1) (r2,s2). R r1 r2 \/ (r1 = r2) /\ S s1 s2)"
   (SIMP_TAC [WF_LEX_DEPENDENT, ETA_AX])

  let WF_POINTWISE ← prove
   r"WF((<<) :A->A->bool) /\ WF((<<<) :B->B->bool)
   ==> WF(\(x1,y1) (x2,y2). x1 << x2 /\ y1 <<< y2)"
   (STRIP_TAC THEN MATCH_MP_TAC WF_SUBSET THEN EXISTS_TAC
     (← q r"\(x1,y1) (x2,y2). x1 << x2 \/ (x1:A = x2) /\ (y1:B) <<< (y2:B)") THEN
    CONJ_TAC THENL
     [REWRITE_TAC [FORALL_PAIR_THM] THEN CONV_TAC TAUT,
      MATCH_MP_TAC WF_LEX THEN ASM_REWRITE_TAC []])

  /- ---------------------------------------------------------------------- -/
  /- Wellfoundedness properties of natural numbers.                         -/
  /- ---------------------------------------------------------------------- -/

  let WF_num ← prove
   r"WF(<)"
   (REWRITE_TAC [WF_IND, num_WF])

  let WF_REC_num ← prove
   r"!H. (!f g n. (!m. m < n ==> (f m = g m)) ==> (H f n = H g n))
        ==> ?f:num->A. !n. f n = H f n"
   (MATCH_ACCEPT_TAC (← MATCH_MP WF_REC WF_num))

  /- ---------------------------------------------------------------------- -/
  /- Natural number measures (useful in program verification).              -/
  /- ---------------------------------------------------------------------- -/

  let MEASURE ← new_definition
    r"MEASURE (m:A->num) = \x y. m(x) < m(y)"

  let WF_MEASURE ← prove
   r"!m:A->num. WF(MEASURE m)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [MEASURE] THEN
    MATCH_MP_TAC WF_MEASURE_GEN THEN
    MATCH_ACCEPT_TAC WF_num)

  let MEASURE_LE ← prove
   r"!m:A->num. (!y. MEASURE m y a ==> MEASURE m y b) <=> m(a) <= m(b)"
   (REWRITE_TAC [MEASURE] THEN MESON_TAC [NOT_LE, LTE_TRANS, LT_REFL])

  /- ---------------------------------------------------------------------- -/
  /- Trivially, a WF relation is irreflexive and antisymmetric.             -/
  /- ---------------------------------------------------------------------- -/

  let WF_ANTISYM ← prove
   r"!(<<) x y:A. WF(<<) ==> ~(x << y /\ y << x)"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [WF]) THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"\z:A. z = x \/ z = y")) THEN
    ASM_MESON_TAC [])

  let WF_REFL ← prove
   r"!x:A. WF(<<) ==> ~(x << x)"
   (MESON_TAC [WF_ANTISYM])

  /- ---------------------------------------------------------------------- -/
  /- Even more trivially, the everywhere-false relation is wellfounded.     -/
  /- ---------------------------------------------------------------------- -/

  let WF_FALSE ← prove
   r"WF(\x y:A. F)"
   (REWRITE_TAC [WF])

  /- ---------------------------------------------------------------------- -/
  /- The Nash-Williams minimal bad sequence argument for some predicate     -/
  /- `bad` that is a "safety property" in the Lamport/Alpern/Schneider sense.-/
  /- ---------------------------------------------------------------------- -/

  let MINIMAL_BAD_SEQUENCE ← prove
   r"!(<<) (bad:(num->A)->bool).
        WF(<<) /\
        (!x. ~bad x ==> ?n. !y. (!k. k < n ==> y k = x k) ==> ~bad y) /\
        (?x. bad x)
         ==> ?y. bad y /\
                 !z n. bad z /\ (!k. k < n ==> z k = y k) ==> ~(z n << y n)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN SUBGOAL_THEN
     (← q r"?x:num->A. !n. (?y. bad y /\ (!k. k < n ==> y k = x k) /\ y n = x n) /\
                     !z. bad z /\ (!k. k < n ==> z k = x k) ==> ~(z n << x n)")
    MP_TAC THENL
     [MATCH_MP_TAC (← MATCH_MP WF_REC_EXISTS WF_num) THEN SIMP_TAC [],
      MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC []] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:num->A", ← q r"n:num"] THEN
    DISCH_TAC THEN REWRITE_TAC [← MESON []
      (← q r"(?a. (?y. P y /\ Q y /\ f y = a) /\ (!z. A z ==> ~B a z)) <=>
       ?y. (P y /\ Q y) /\ (!z. B (f y) z ==> ~A z)")] THEN
    MP_TAC (← ISPECL [← q r"(<<):A->A->bool", ← q r"\x:num->A. x n"] WF_MEASURE_GEN) THEN
    ASM_REWRITE_TAC [] THEN REWRITE_TAC [WF] THEN DISCH_THEN MATCH_MP_TAC THEN
    POP_ASSUM_LIST (MP_TAC o end_itlist CONJ) THEN SPEC_TAC ((← q r"n:num"), (← q r"n:num")) THEN
    INDUCT_TAC THEN SIMP_TAC [LT] THEN MESON_TAC [])

  /- ---------------------------------------------------------------------- -/
  /- Tail recursion.                                                        -/
  /- ---------------------------------------------------------------------- -/

  let WF_REC_TAIL ← prove
   r"!P g h. ?f:A->B. !x. f x = if P(x) then f(g x) else h x"
   (← do
    let lemma1 ← prove
     r"~(P 0) ==> ((?n. P(SUC n)) <=> (?n. P(n)))"
     (MESON_TAC [num_CASES, NOT_SUC])
    let lemma2 ← prove
     r"(P 0) ==> ((!m. m < n ==> P(SUC m)) <=> (!m. m < SUC n ==> P(m)))"
     (REPEAT (DISCH_TAC ORELSE EQ_TAC) THEN INDUCT_TAC THEN
      ASM_MESON_TAC [LT_SUC, LT_0])
    pure
     (REPEAT GEN_TAC THEN
      MP_TAC (← GEN (← q r"x:A") (← ISPECL [← q r"x:A", ← q r"\y:A n:num. g(y):A"] num_RECURSION)) THEN
      REWRITE_TAC [SKOLEM_THM, FORALL_AND_THM] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"s:A->num->A") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"\x:A. if ?n:num. ~P(s x n)
                      then (h:A->B)(@y. ?n. (y = s x n) /\ ~P(s x n) /\
                                            !m. m < n ==> P(s x m))
                      else something_arbitrary:B") THEN
      X_GEN_TAC (← q r"x:A") THEN
      SUBGOAL_THEN (← q r"!n x:A. s (g x) n :A = s x (SUC n)") ASSUME_TAC THENL
       [INDUCT_TAC THEN ASM_REWRITE_TAC [],
        UNDISCH_THEN (← q r"!x:A n. s x (SUC n) :A = g (s x n)") (K ALL_TAC)] THEN
      ASM_CASES_TAC (← q r"(P:A->bool) x") THEN ASM_REWRITE_TAC [] THENL
       [ASM_SIMP_TAC [lemma1] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
        CONV_TAC SYM_CONV THEN ASM_SIMP_TAC [lemma2, lemma1],
        COND_CASES_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
        AP_TERM_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
        REWRITE_TAC [] THEN X_GEN_TAC (← q r"y:A") THEN EQ_TAC THENL
         [SIMP_TAC [LEFT_IMP_EXISTS_THM] THEN
          INDUCT_TAC THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [LT_0],
          ASM_MESON_TAC [LT]]]))

  /- ---------------------------------------------------------------------- -/
  /- A more general mix of tail and wellfounded recursion.                  -/
  /- ---------------------------------------------------------------------- -/

  let WF_REC_TAIL_GENERAL ← prove
   r"!P G H. WF(<<) /\
           (!f g x. (!z. z << x ==> (f z = g z))
                    ==> (P f x <=> P g x) /\ G f x = G g x /\ H f x = H g x) /\
           (!f g x. (!z. z << x ==> (f z = g z)) ==> (H f x = H g x)) /\
           (!f x y. P f x /\ y << G f x ==> y << x)
           ==> ?f:A->B. !x. f x = if P f x then f(G f x) else H f x"
   (← do
    let t1 ← TAUT (← q r"a ==> b ==> c <=> b ==> a ==> c")
    let m1 ← MESON []
       (← q r"(a = b) /\ (a /\ b ==> (x = y) /\ (f x = g x))
        ==> ((if a then f x else d) = (if b then g y else d))")
    let pire ← prove_inductive_relations_exist
       (← q r"(!x:A. ~(P f x) ==> terminates f x) /\
        (!x. P (f:A->B) x /\ terminates f (G f x) ==> terminates f x)")
    pure
      (REPEAT STRIP_TAC THEN
        CHOOSE_THEN MP_TAC pire THEN
        REWRITE_TAC [FORALL_AND_THM] THEN
        DISCH_THEN (STRIP_ASSUME_TAC o GSYM) THEN
        SUBGOAL_THEN
         (← q r"?while. !f:A->B x:A. while f x = if P f x then while f (G f x) else x")
         (STRIP_ASSUME_TAC o GSYM)
        THENL [REWRITE_TAC [← GSYM SKOLEM_THM, WF_REC_TAIL], ALL_TAC] THEN
        SUBGOAL_THEN
         (← q r"?f:A->B. !x. f x = if terminates f x then H f (while f x :A) else anything")
        MP_TAC THENL
         [FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP WF_REC) THEN
          REPEAT STRIP_TAC THEN MATCH_MP_TAC m1 THEN
          REPEAT STRIP_TAC THENL
           [SUBGOAL_THEN
             (← q r"!f g x.
                 (!x y. P f x /\ y << G (f:A->B) x ==> y << x) /\
                 (!y:A. (!z:A. z << y ==> z << x)
                        ==> (P f y = P g y) /\ (G f y = G g y))
                     ==> terminates f x ==> terminates g x")
             (fun th => EQ_TAC THEN MATCH_MP_TAC th THEN ASM_MESON_TAC []) THEN
            GEN_TAC THEN GEN_TAC THEN
            REWRITE_TAC [RIGHT_FORALL_IMP_THM, IMP_CONJ] THEN DISCH_TAC THEN
            ONCE_REWRITE_TAC [t1] THEN
            FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC [],
            SUBGOAL_THEN
             (← q r"!x:A. terminates (f:A->B) x /\
                    (!y:A. (!z:A. z << y ==> z << x)
                           ==> (P f y <=> P g y) /\ (G f y :A = G g y))
                    ==> (while f x :A = while g x)")
             (fun th => MATCH_MP_TAC th THEN ASM_MESON_TAC []) THEN
            REWRITE_TAC [IMP_CONJ] THEN
            FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC [],
            FIRST_X_ASSUM MATCH_MP_TAC THEN
            SUBGOAL_THEN
             (← q r"!f:A->B. (!x:A y:A. P f x /\ y << G f x ==> y << x)
               ==> !x. terminates f x ==> !y. y << while f x ==> y << x")
             (fun th => ASM_MESON_TAC [th]) THEN
            GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
            ASM_MESON_TAC []],
          MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
          DISCH_THEN (fun th => tactic_of do pure (ASSUME_TAC (← GSYM th) THEN MP_TAC th)) THEN
          MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC (← q r"x:A") THEN
          ASM_CASES_TAC (← q r"P (f:A->B) (x:A) :bool") THEN ASM_MESON_TAC []]))

  return { WF, WF_EQ, WF_IND, WF_DCHAIN, WF_DCHAIN_TRANSITIVE, WF_UREC, WF_UREC_WF,
           WF_REC_INVARIANT, WF_REC, WF_REC_WF, WF_EREC, WF_REC_EXISTS, WF_SUBSET,
           WF_RESTRICT, WF_MEASURE_GEN, WF_LEX_DEPENDENT, WF_LEX, WF_POINTWISE, WF_num,
           WF_REC_num, MEASURE, WF_MEASURE, MEASURE_LE, WF_ANTISYM, WF_REFL, WF_FALSE,
           MINIMAL_BAD_SEQUENCE, WF_REC_TAIL, WF_REC_TAIL_GENERAL }

/- ---------------------------------------------------------------------- -/
/- Tactic to apply WF induction on a free "measured" term in the goal.    -/
/- ---------------------------------------------------------------------- -/

/-- The two theorems `WF_INDUCT_TAC` proves when wf.ml defines it (its
    `qqconv`/`eqconv` `pth`s).  Kept out of `setupWf`: proving them there fixes
    their polymorphic type variables under the surrounding parse context, which
    breaks the `GEN_REWRITE_CONV`/`REWR_CONV` matching under a binder. -/
@[nospecialize]
def setupWfInductPths [HolBase] (MESON_TAC : List thm → tactic) :
    ExceptT String IO (thm × thm) := do
  let pth1 ← prove
   r"(!x. P x ==> !y. Q x y) <=> !y x. P x ==> Q x y" (MESON_TAC [])
  let pth2 ← prove
   r"(!m. P m ==> (m = e) ==> Q) <=> (P e ==> Q)" (MESON_TAC [])
  return (pth1, pth2)

/-- `let rec qqconvs tm = try (qqconv THENC BINDER_CONV qqconvs) tm
    with Failure _ -> eqconv tm`. -/
partial def qqconvs (qqconv eqconv : ioconv) : ioconv :=
  fun tm => ((qqconv THENC BINDER_CONV (qqconvs qqconv eqconv)) ORELSEC eqconv) tm

/-- `WF_INDUCT_TAC` (wf.ml): wellfounded induction on a free measured term.
    `qqconv` is `GEN_REWRITE_CONV I [pth1]`, built once by the caller;
    `pth1`/`pth2` are `setupWfInductPths`'s theorems; `num_WF` from arith.ml. -/
def WF_INDUCT_TAC [HolBase] (qqconv : ioconv) (pth2 num_WF : thm) (tm : term) : tactic :=
  fun (asl, w) => ExceptT.run do
    let eqconv := REWR_CONV pth2
    let qqconvs := qqconvs qqconv eqconv
    let fvs := frees tm
    let gv ← liftM (genvar (type_of tm) : IO term)
    let pat ← liftExcept (do list_mk_forall (gv :: fvs) (← HolCore.Bool.mk_imp (safe_mk_eq gv tm) w))
    let th0 ← UNDISCH (← PART_MATCH rand num_WF pat)
    let th1 ← MP (← SPECL (tm :: fvs) th0) (REFL tm)
    let th2 ← CONV_RULE (LAND_CONV qqconvs) (← DISCH_ALL th1)
    ExceptT.mk ((MATCH_MP_TAC th2 THEN MAP_EVERY X_GEN_TAC fvs THEN
      CONV_TAC (LAND_CONV qqconvs) THEN DISCH_THEN ASSUME_TAC) (asl, w))

end HolMath.Wf
