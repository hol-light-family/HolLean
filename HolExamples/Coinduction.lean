/- File: HolExamples/Coinduction.lean
Translation of HOL Light's Examples/coinduction.ml, phrase by phrase.
Drafted by gxwork/h100/ml2lean.py (disclosed; the user agreed to the
scripts, 2026-11-13), then gxwork/ll/coind/fix.py and edits by hand.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolExamples.Common
open HolCore.Kernel Session HolLight.Syntax HolExamples
open scoped HolLight
namespace HolExamples.Coinduction

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
/-- Run an `IO (Except String α)` once, caching under `name` (OCaml's `let`
    evaluates its right-hand side once), for the `let X,Y,Z = e` bindings
    whose result is a tuple. -/
private def keepIO {α : Type} [Inhabited α] (name : String) (f : Unit → IO (Except String α)) : α :=
  keep name fun _ =>
    match runIO (f ()) with
    | .ok (.ok v) => v
    | .ok (.error e) => panic! s!"keepIO {name}: {e}"
    | .error e => panic! s!"keepIO {name}: {e}"
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)

/- ========================================================================= -/
/- Examples of coinductive definitions and proofs by coinduction.            -/
/-                                                                           -/
/- Most of these are classic examples from the literature on coinduction,    -/
/- chosen to exercise new_coinductive_definition (schematic and mutual       -/
/- definitions, nesting of inductive definitions inside coinductive ones,    -/
/- strong coinduction) and to illustrate what it is used for.                -/
/- ========================================================================= -/
/- ------------------------------------------------------------------------- -/
/- The same rules interpreted inductively and coinductively. When applying   -/
/- the rules backwards always terminates, as for these rules on the natural  -/
/- numbers, the least and greatest fixpoints coincide. In general they do    -/
/- not: the coinductive transitive closure of any relation is universal.     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 1
-- let COEVEN_RULES,COEVEN_COINDUCT,COEVEN_CASES = new_coinductive_definition ...
def COEVEN_RULES_defs : thm × thm × thm :=
  keepIO "COEVEN_RULES_defs" fun _ => new_coinductive_definition
  [[COEVEN 0 /\ (!n. COEVEN n ==> COEVEN(SUC(SUC n)))]]
def COEVEN_RULES : thm := COEVEN_RULES_defs.1
def COEVEN_COINDUCT : thm := COEVEN_RULES_defs.2.1
def COEVEN_CASES : thm := COEVEN_RULES_defs.2.2
#eval do IO.println (repr COEVEN_RULES); IO.println (repr COEVEN_COINDUCT); IO.println (repr COEVEN_CASES)

#eval phrase 2
def COEVEN_EVEN : thm := keep "COEVEN_EVEN" fun _ => (do
  let h1 ← tt (← ExceptT.mk [[(p <=> q) <=> (p ==> q) /\ (q ==> p)]])
  prove ([[!n. COEVEN n <=> EVEN n]])
   (REWRITE_TAC [h1, FORALL_AND_THM] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN ([[!n. (COEVEN n ==> EVEN n) /\ (COEVEN(SUC n) ==> EVEN(SUC n))]]) (fun th => REWRITE_TAC [th]) THEN
      INDUCT_TAC THEN ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [COEVEN_CASES] THEN
      ASM_REWRITE_TAC [NOT_SUC, SUC_INJ, (← HolLight.GSYM NOT_SUC), UNWIND_THM1, EVEN],
      MATCH_MP_TAC COEVEN_COINDUCT THEN INDUCT_TAC THEN
      REWRITE_TAC [NOT_SUC, SUC_INJ, EVEN] THEN
      SPEC_TAC (([[n:num]]), ([[n:num]])) THEN INDUCT_TAC THEN
      REWRITE_TAC [EVEN, SUC_INJ, UNWIND_THM1]])
  : ExceptT String IO thm).run
#eval COEVEN_EVEN

#eval phrase 3
-- let CTC_RULES,CTC_COINDUCT,CTC_CASES = new_coinductive_definition ...
def CTC_RULES_defs : thm × thm × thm :=
  keepIO "CTC_RULES_defs" fun _ => new_coinductive_definition
  [[(!x y. R x y ==> CTC R x y) /\
  (!x y z. CTC R x y /\ CTC R y z ==> CTC R (x:A) z)]]
def CTC_RULES : thm := CTC_RULES_defs.1
def CTC_COINDUCT : thm := CTC_RULES_defs.2.1
def CTC_CASES : thm := CTC_RULES_defs.2.2
#eval do IO.println (repr CTC_RULES); IO.println (repr CTC_COINDUCT); IO.println (repr CTC_CASES)

#eval phrase 4
def CTC_UNIV : thm := keep "CTC_UNIV" fun _ => (do
  prove ([[!R (x:A) y. CTC R x y]])
   (GEN_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[R:A->A->bool]]), ([[\x:A y:A. T]])] CTC_COINDUCT) THEN
    REWRITE_TAC [] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval CTC_UNIV

/- ------------------------------------------------------------------------- -/
/- Infinite paths in a relation. These are the same as infinite sequences    -/
/- of successive elements, so their absence is wellfoundedness of the        -/
/- converse relation.                                                        -/
/- ------------------------------------------------------------------------- -/

#eval phrase 5
-- let INFPATH_RULES,INFPATH_COINDUCT,INFPATH_CASES = new_coinductive_definition ...
def INFPATH_RULES_defs : thm × thm × thm :=
  keepIO "INFPATH_RULES_defs" fun _ => new_coinductive_definition
  [[!x y. R x y /\ INFPATH R y ==> INFPATH R (x:A)]]
def INFPATH_RULES : thm := INFPATH_RULES_defs.1
def INFPATH_COINDUCT : thm := INFPATH_RULES_defs.2.1
def INFPATH_CASES : thm := INFPATH_RULES_defs.2.2
#eval do IO.println (repr INFPATH_RULES); IO.println (repr INFPATH_COINDUCT); IO.println (repr INFPATH_CASES)

#eval phrase 6
def INFPATH_SEQ : thm := keep "INFPATH_SEQ" fun _ => (do
  prove ([[!R x:A. INFPATH R x <=> ?s. s 0 = x /\ !n. R (s n) (s(SUC n))]])
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN
      MP_TAC (← ExceptT.mk (prove_recursive_functions_exist num_RECURSION
        [[s 0 = (x:A) /\ (!n. s(SUC n) = @y. R (s n) y /\ INFPATH R y)]])) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[s:num->A]]) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN ([[!n. INFPATH R ((s:num->A) n)
          ==> R (s n) (s(SUC n)) /\ INFPATH R (s(SUC n))]]) ASSUME_TAC THENL
       [GEN_TAC THEN ASM_REWRITE_TAC [] THEN
        DISCH_THEN (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [INFPATH_CASES]) THEN
        DISCH_THEN (fun th => CONV_TAC (fun t => pure (SELECT_CONV t)) THEN ACCEPT_TAC th),
        SUBGOAL_THEN ([[!n. INFPATH R ((s:num->A) n)]]) MP_TAC THENL
         [INDUCT_TAC THEN ASM_SIMP_TAC [], ASM_MESON_TAC []]],
      STRIP_TAC THEN
      MP_TAC (← HolLight.ISPECL [([[R:A->A->bool]]), ([[\a:A. ?s. s 0 = a /\ !n. R (s n) (s(SUC n))]])] INFPATH_COINDUCT) THEN
      REWRITE_TAC [] THEN ANTS_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
      X_GEN_TAC ([[a:A]]) THEN
      DISCH_THEN (X_CHOOSE_THEN ([[t:num->A]]) STRIP_ASSUME_TAC) THEN
      EXISTS_TAC ([[(t:num->A) 1]]) THEN CONJ_TAC THENL
       [ASM_MESON_TAC [ONE],
        EXISTS_TAC ([[\n. (t:num->A)(SUC n)]]) THEN ASM_REWRITE_TAC [ONE]]])
  : ExceptT String IO thm).run
#eval INFPATH_SEQ

#eval phrase 7
def WF_INFPATH : thm := keep "WF_INFPATH" fun _ => (do
  prove ([[!R:A->A->bool. WF(\x y. R y x) <=> !x. ~INFPATH R x]])
   (REWRITE_TAC [WF_DCHAIN, INFPATH_SEQ] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval WF_INFPATH

/- ------------------------------------------------------------------------- -/
/- Koenig's lemma: in a finitely branching relation, if there are paths of   -/
/- all finite lengths from x, then there is an infinite path from x. The     -/
/- proof is by coinduction: by the pigeonhole principle, a point with        -/
/- arbitrarily long paths has a successor with arbitrarily long paths.       -/
/- ------------------------------------------------------------------------- -/

#eval phrase 8
def KOENIG_LEMMA : thm := keep "KOENIG_LEMMA" fun _ => (do
  prove ([[!R x:A.
        (!x. FINITE {y | R x y}) /\
        (!n. ?s. s 0 = x /\ !i. i < n ==> R (s i) (s(SUC i)))
        ==> INFPATH R x]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[R:A->A->bool]]),
      ([[\a:A. !n. ?s. s 0 = a /\ !i. i < n ==> R (s i) (s(SUC i))]])] INFPATH_COINDUCT) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
    X_GEN_TAC ([[a:A]]) THEN DISCH_TAC THEN REFUTE_THEN ASSUME_TAC THEN
    SUBGOAL_THEN ([[!y:A. ?n. R a y ==> ~(?s. s 0 = y /\ !i. i < n ==> R (s i) (s(SUC i)))]]) MP_TAC THENL [ASM_MESON_TAC [], REWRITE_TAC [SKOLEM_THM]] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[f:A->num]]) (LABEL_TAC "f")) THEN
    SUBGOAL_THEN ([[?N. !y:A. R (a:A) y ==> (f:A->num) y <= N]]) STRIP_ASSUME_TAC THENL
     [MP_TAC (← HolLight.ISPEC ([[IMAGE (f:A->num) {y | (R:A->A->bool) a y}]]) num_FINITE) THEN
      ASM_SIMP_TAC [FINITE_IMAGE, FORALL_IN_IMAGE, IN_ELIM_THM],
      ALL_TAC] THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN ([[s:num->A]]) STRIP_ASSUME_TAC o HolLight.SPEC ([[SUC N]])) THEN
    SUBGOAL_THEN ([[(R:A->A->bool) a ((s:num->A)(SUC 0))]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [LT_0], ALL_TAC] THEN
    REMOVE_THEN "f" (MP_TAC o HolLight.SPEC ([[(s:num->A)(SUC 0)]])) THEN
    ASM_REWRITE_TAC [] THEN EXISTS_TAC ([[\i. (s:num->A)(SUC i)]]) THEN
    REWRITE_TAC [] THEN X_GEN_TAC ([[i:num]]) THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [LT_SUC] THEN
    TRANS_TAC LTE_TRANS ([[(f:A->num)((s:num->A)(SUC 0))]]) THEN
    ASM_SIMP_TAC [])
  : ExceptT String IO thm).run
#eval KOENIG_LEMMA

/- ------------------------------------------------------------------------- -/
/- Invariants. "P holds at all states reachable from x" (AG P in CTL) is     -/
/- coinductive, and the usual way of establishing an invariant, by finding   -/
/- a stronger property that holds at x and is preserved by the transitions,  -/
/- is exactly an application of the coinduction principle.                   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 9
-- let REACH_RULES,REACH_INDUCT,REACH_CASES = new_inductive_definition ...
def REACH_RULES_defs : thm × thm × thm :=
  keepIO "REACH_RULES_defs" fun _ => new_inductive_definition
  [[(!x. REACH R x x) /\ (!x y z. R x y /\ REACH R y z ==> REACH R (x:A) z)]]
def REACH_RULES : thm := REACH_RULES_defs.1
def REACH_INDUCT : thm := REACH_RULES_defs.2.1
def REACH_CASES : thm := REACH_RULES_defs.2.2
#eval do IO.println (repr REACH_RULES); IO.println (repr REACH_INDUCT); IO.println (repr REACH_CASES)

#eval phrase 10
-- let AG_RULES,AG_COINDUCT,AG_CASES = new_coinductive_definition ...
def AG_RULES_defs : thm × thm × thm :=
  keepIO "AG_RULES_defs" fun _ => new_coinductive_definition
  [[!x. P x /\ (!y. R x y ==> AG R P y) ==> AG R P (x:A)]]
def AG_RULES : thm := AG_RULES_defs.1
def AG_COINDUCT : thm := AG_RULES_defs.2.1
def AG_CASES : thm := AG_RULES_defs.2.2
#eval do IO.println (repr AG_RULES); IO.println (repr AG_COINDUCT); IO.println (repr AG_CASES)

#eval phrase 11
def AG_REACH : thm := keep "AG_REACH" fun _ => (do
  prove ([[!R P x:A. AG R P x <=> !y. REACH R x y ==> P y]])
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [SPEC_TAC (([[x:A]]), ([[x:A]])) THEN
      SUBGOAL_THEN ([[!x y:A. REACH R x y ==> AG R P x ==> P y]]) (fun th => MESON_TAC [th]) THEN
      MATCH_MP_TAC REACH_INDUCT THEN MESON_TAC [AG_CASES],
      SPEC_TAC (([[x:A]]), ([[x:A]])) THEN MATCH_MP_TAC AG_COINDUCT THEN
      MESON_TAC [REACH_RULES]])
  : ExceptT String IO thm).run
#eval AG_REACH

#eval phrase 12
def AG_EVEN : thm := keep "AG_EVEN" fun _ => (do
  prove ([[AG (\x y. y = x + 2) EVEN 0]])
   (MP_TAC (← HolLight.ISPECL [([[\x y:num. y = x + 2]]), ([[EVEN]]), ([[EVEN]])] AG_COINDUCT) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [SIMP_TAC [EVEN_ADD, ARITH_EVEN], DISCH_THEN MATCH_MP_TAC] THEN
    REWRITE_TAC [ARITH_EVEN])
  : ExceptT String IO thm).run
#eval AG_EVEN

/- ------------------------------------------------------------------------- -/
/- Properties of infinite sequences, i.e. functions num->A: "always" is      -/
/- coinductive, "eventually" inductive, and "infinitely often" nests the     -/
/- inductive "eventually" inside a coinductive definition. That needs the    -/
/- monotonicity of "eventually", which is added to monotonicity_theorems.    -/
/- ------------------------------------------------------------------------- -/

#eval phrase 13
-- let ALWAYS_RULES,ALWAYS_COINDUCT,ALWAYS_CASES = new_coinductive_definition ...
def ALWAYS_RULES_defs : thm × thm × thm :=
  keepIO "ALWAYS_RULES_defs" fun _ => new_coinductive_definition
  [[!s:num->A. P(s 0) /\ ALWAYS P (\n. s(SUC n)) ==> ALWAYS P s]]
def ALWAYS_RULES : thm := ALWAYS_RULES_defs.1
def ALWAYS_COINDUCT : thm := ALWAYS_RULES_defs.2.1
def ALWAYS_CASES : thm := ALWAYS_RULES_defs.2.2
#eval do IO.println (repr ALWAYS_RULES); IO.println (repr ALWAYS_COINDUCT); IO.println (repr ALWAYS_CASES)

#eval phrase 14
def ALWAYS : thm := keep "ALWAYS" fun _ => (do
  prove ([[!P s:num->A. ALWAYS P s <=> !n. P(s n)]])
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [SUBGOAL_THEN ([[!n s:num->A. ALWAYS P s ==> P(s n)]]) (fun th => MESON_TAC [th]) THEN
      INDUCT_TAC THEN GEN_TAC THEN GEN_REWRITE_TAC HolLight.LAND_CONV [ALWAYS_CASES] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[\n. (s:num->A)(SUC n)]])) THEN
      ASM_REWRITE_TAC [],
      SPEC_TAC (([[s:num->A]]), ([[s:num->A]])) THEN MATCH_MP_TAC ALWAYS_COINDUCT THEN
      SIMP_TAC []])
  : ExceptT String IO thm).run
#eval ALWAYS

#eval phrase 15
-- let EV_RULES,EV_INDUCT,EV_CASES = new_inductive_definition ...
def EV_RULES_defs : thm × thm × thm :=
  keepIO "EV_RULES_defs" fun _ => new_inductive_definition
  [[(!s:num->A. Q s ==> EV Q s) /\ (!s. EV Q (\n. s(SUC n)) ==> EV Q s)]]
def EV_RULES : thm := EV_RULES_defs.1
def EV_INDUCT : thm := EV_RULES_defs.2.1
def EV_CASES : thm := EV_RULES_defs.2.2
#eval do IO.println (repr EV_RULES); IO.println (repr EV_INDUCT); IO.println (repr EV_CASES)

#eval phrase 16
def EV : thm := keep "EV" fun _ => (do
  prove ([[!Q s:num->A. EV Q s <=> ?k. Q (\n. s(k + n))]])
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [SPEC_TAC (([[s:num->A]]), ([[s:num->A]])) THEN MATCH_MP_TAC EV_INDUCT THEN
      REWRITE_TAC [] THEN CONJ_TAC THEN X_GEN_TAC ([[s:num->A]]) THENL
       [DISCH_TAC THEN EXISTS_TAC ([[0]]) THEN ASM_REWRITE_TAC [ADD_CLAUSES, ETA_AX],
        DISCH_THEN (X_CHOOSE_TAC ([[k:num]])) THEN EXISTS_TAC ([[SUC k]]) THEN
        ASM_REWRITE_TAC [ADD_CLAUSES]],
      DISCH_THEN (X_CHOOSE_TAC ([[k:num]])) THEN POP_ASSUM MP_TAC THEN
      SPEC_TAC (([[s:num->A]]), ([[s:num->A]])) THEN SPEC_TAC (([[k:num]]), ([[k:num]])) THEN
      INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES, ETA_AX] THEN
      SIMP_TAC [EV_RULES] THEN X_GEN_TAC ([[s:num->A]]) THEN DISCH_TAC THEN
      MATCH_MP_TAC (← HolLight.CONJUNCT2 (← HolLight.SPEC_ALL EV_RULES)) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []])
  : ExceptT String IO thm).run
#eval EV

#eval phrase 17
def MONO_EV : thm := keep "MONO_EV" fun _ => (do
  prove ([[(!s:num->A. Q s ==> Q' s) ==> EV Q s ==> EV Q' s]])
   (REWRITE_TAC [EV] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval MONO_EV

#eval phrase 18
-- monotonicity_theorems := MONO_EV :: !monotonicity_theorems;;
#eval (do set_monotonicity_theorems (MONO_EV :: (← get_monotonicity_theorems)) : IO Unit)

#eval phrase 19
-- let IO_RULES,IO_COINDUCT,IO_CASES = new_coinductive_definition ...
def IO_RULES_defs : thm × thm × thm :=
  keepIO "IO_RULES_defs" fun _ => new_coinductive_definition
  [[!s:num->A. EV (\t. P(t 0) /\ IO P (\n. t(SUC n))) s ==> IO P s]]
def IO_RULES : thm := IO_RULES_defs.1
def IO_COINDUCT : thm := IO_RULES_defs.2.1
def IO_CASES : thm := IO_RULES_defs.2.2
#eval do IO.println (repr IO_RULES); IO.println (repr IO_COINDUCT); IO.println (repr IO_CASES)

#eval phrase 20
-- (OCaml's `IO`; `IO` is Lean's IO monad)
def IO' : thm := keep "IO" fun _ => (do
  prove ([[!P s:num->A. IO P s <=> !m. ?n. m <= n /\ P(s n)]])
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [SUBGOAL_THEN ([[!m s:num->A. IO P s ==> ?n. m <= n /\ P(s n)]]) (fun th => MESON_TAC [th]) THEN
      INDUCT_TAC THEN GEN_TAC THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [IO_CASES] THEN REWRITE_TAC [EV, ADD_CLAUSES] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[k:num]]) STRIP_ASSUME_TAC) THENL
       [EXISTS_TAC ([[k:num]]) THEN ASM_REWRITE_TAC [LE_0],
        FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[\n. (s:num->A)(SUC(k + n))]])) THEN
        ASM_REWRITE_TAC [] THEN
        DISCH_THEN (X_CHOOSE_THEN ([[n:num]]) STRIP_ASSUME_TAC) THEN
        EXISTS_TAC ([[SUC(k + n)]]) THEN ASM_REWRITE_TAC [LE_SUC] THEN
        ASM_ARITH_TAC],
      SPEC_TAC (([[s:num->A]]), ([[s:num->A]])) THEN MATCH_MP_TAC IO_COINDUCT THEN
      X_GEN_TAC ([[s:num->A]]) THEN DISCH_TAC THEN REWRITE_TAC [EV, ADD_CLAUSES] THEN
      FIRST_ASSUM (X_CHOOSE_THEN ([[k:num]]) STRIP_ASSUME_TAC o HolLight.SPEC ([[0]])) THEN
      EXISTS_TAC ([[k:num]]) THEN ASM_REWRITE_TAC [] THEN
      X_GEN_TAC ([[m:num]]) THEN FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[SUC(k + m)]])) THEN
      DISCH_THEN (X_CHOOSE_THEN ([[n:num]]) STRIP_ASSUME_TAC) THEN
      EXISTS_TAC ([[n - SUC k]]) THEN
      SUBGOAL_THEN ([[SUC(k + (n - SUC k)) = n]]) SUBST1_TAC THENL
       [ASM_ARITH_TAC, ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC]])
  : ExceptT String IO thm).run
#eval IO'

/- A mutual coinductive definition: P at all even, or at all odd, places.    -/

#eval phrase 21
-- let EVENPOS_RULES,EVENPOS_COINDUCT,EVENPOS_CASES = new_coinductive_definition ...
def EVENPOS_RULES_defs : thm × thm × thm :=
  keepIO "EVENPOS_RULES_defs" fun _ => new_coinductive_definition
  [[(!s:num->A. P(s 0) /\ ODDPOS P (\n. s(SUC n)) ==> EVENPOS P s) /\
  (!s:num->A. EVENPOS P (\n. s(SUC n)) ==> ODDPOS P s)]]
def EVENPOS_RULES : thm := EVENPOS_RULES_defs.1
def EVENPOS_COINDUCT : thm := EVENPOS_RULES_defs.2.1
def EVENPOS_CASES : thm := EVENPOS_RULES_defs.2.2
#eval do IO.println (repr EVENPOS_RULES); IO.println (repr EVENPOS_COINDUCT); IO.println (repr EVENPOS_CASES)

#eval phrase 22
def EVENPOS_ODDPOS : thm := keep "EVENPOS_ODDPOS" fun _ => (do
  prove ([[!P s:num->A. (EVENPOS P s <=> !n. EVEN n ==> P(s n)) /\
                (ODDPOS P s <=> !n. ODD n ==> P(s n))]])
   (GEN_TAC THEN
    SUBGOAL_THEN ([[!n s:num->A. (EVENPOS P s ==> EVEN n ==> P(s n)) /\
                 (ODDPOS P s ==> ODD n ==> P(s n))]]) ASSUME_TAC THENL
     [INDUCT_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC [EVENPOS_CASES] THEN
      REWRITE_TAC [EVEN, ODD] THEN SIMP_TAC [] THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[\n. (s:num->A)(SUC n)]])) THEN
      REWRITE_TAC [NOT_EVEN, NOT_ODD] THEN MESON_TAC [],
      ALL_TAC] THEN
    MP_TAC (← HolLight.ISPECL [([[P:A->bool]]), ([[\s:num->A. !n. EVEN n ==> P(s n)]]),
                   ([[\s:num->A. !n. ODD n ==> P(s n)]])] EVENPOS_COINDUCT) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [EVEN, ODD, NOT_EVEN, NOT_ODD],
      ASM_MESON_TAC []])
  : ExceptT String IO thm).run
#eval EVENPOS_ODDPOS

/- ------------------------------------------------------------------------- -/
/- The lexicographic order on infinite sequences of numbers. It is a total   -/
/- order: reflexivity, transitivity and totality are proved by coinduction   -/
/- (totality classically) and antisymmetry by induction on the position.     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 23
-- let LEXLE_RULES,LEXLE_COINDUCT,LEXLE_CASES = new_coinductive_definition ...
def LEXLE_RULES_defs : thm × thm × thm :=
  keepIO "LEXLE_RULES_defs" fun _ => new_coinductive_definition
  [[(!s t:num->num. s 0 < t 0 ==> LEXLE s t) /\
  (!s t. s 0 = t 0 /\ LEXLE (\n. s(SUC n)) (\n. t(SUC n)) ==> LEXLE s t)]]
def LEXLE_RULES : thm := LEXLE_RULES_defs.1
def LEXLE_COINDUCT : thm := LEXLE_RULES_defs.2.1
def LEXLE_CASES : thm := LEXLE_RULES_defs.2.2
#eval do IO.println (repr LEXLE_RULES); IO.println (repr LEXLE_COINDUCT); IO.println (repr LEXLE_CASES)

#eval phrase 24
def LEXLE_REFL : thm := keep "LEXLE_REFL" fun _ => (do
  prove ([[!s:num->num. LEXLE s s]])
   (MP_TAC (← HolLight.ISPEC ([[\s t:num->num. s = t]]) LEXLE_COINDUCT) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [],
      MESON_TAC []])
  : ExceptT String IO thm).run
#eval LEXLE_REFL

#eval phrase 25
def LEXLE_TRANS : thm := keep "LEXLE_TRANS" fun _ => (do
  prove ([[!s t u:num->num. LEXLE s t /\ LEXLE t u ==> LEXLE s u]])
   (REPEAT GEN_TAC THEN
    MP_TAC (← HolLight.ISPEC ([[\s u:num->num. ?t. LEXLE s t /\ LEXLE t u]]) LEXLE_COINDUCT) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL [ALL_TAC, MESON_TAC []] THEN
    MAP_EVERY X_GEN_TAC [([[s:num->num]]), ([[u:num->num]])] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[t:num->num]]) MP_TAC) THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.BINOP_CONV) [LEXLE_CASES] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    TRY (DISJ1_TAC THEN ASM_ARITH_TAC THEN HolCore.Tactics.NO_TAC) THEN
    DISJ2_TAC THEN EXISTS_TAC ([[\n. (t:num->num)(SUC n)]]) THEN
    ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval LEXLE_TRANS

#eval phrase 26
def LEXLE_ANTISYM : thm := keep "LEXLE_ANTISYM" fun _ => (do
  prove ([[!s t:num->num. LEXLE s t /\ LEXLE t s ==> s = t]])
   (REWRITE_TAC [FUN_EQ_THM] THEN
    SUBGOAL_THEN ([[!n s t:num->num. LEXLE s t /\ LEXLE t s ==> s n = t n]]) (fun th => MESON_TAC [th]) THEN
    INDUCT_TAC THEN REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.BINOP_CONV) [LEXLE_CASES] THEN
    STRIP_TAC THEN TRY ASM_ARITH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [([[\n. (s:num->num)(SUC n)]]), ([[\n. (t:num->num)(SUC n)]])]) THEN
    ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval LEXLE_ANTISYM

#eval phrase 27
def LEXLE_TOTAL : thm := keep "LEXLE_TOTAL" fun _ => (do
  let h1 ← tt (← ExceptT.mk [[p \/ q <=> ~q ==> p]])
  prove ([[!s t:num->num. LEXLE s t \/ LEXLE t s]])
   (REWRITE_TAC [h1] THEN
    MP_TAC (← HolLight.ISPEC ([[\s t:num->num. ~LEXLE t s]]) LEXLE_COINDUCT) THEN
    REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY X_GEN_TAC [([[s:num->num]]), ([[t:num->num]])] THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV) [LEXLE_CASES] THEN
    ASM_CASES_TAC ([[(s:num->num) 0 = t 0]]) THEN ASM_REWRITE_TAC [LT_REFL] THEN
    ASM_ARITH_TAC)
  : ExceptT String IO thm).run
#eval LEXLE_TOTAL

/- ------------------------------------------------------------------------- -/
/- Bisimilarity for labelled transition systems, where TR p a q means that   -/
/- p can do a transition labelled a to q. It is an equivalence relation, the -/
/- largest bisimulation, and bisimilar states have the same traces.          -/
/- ------------------------------------------------------------------------- -/

#eval phrase 28
-- let BISIM_RULES,BISIM_COINDUCT,BISIM_CASES = new_coinductive_definition ...
def BISIM_RULES_defs : thm × thm × thm :=
  keepIO "BISIM_RULES_defs" fun _ => new_coinductive_definition
  [[!p q. (!a p'. TR p a p' ==> ?q'. TR q a q' /\ BISIM TR p' q') /\
        (!a q'. TR q (a:L) q' ==> ?p'. TR p a p' /\ BISIM TR p' q')
        ==> BISIM TR (p:S) q]]
def BISIM_RULES : thm := BISIM_RULES_defs.1
def BISIM_COINDUCT : thm := BISIM_RULES_defs.2.1
def BISIM_CASES : thm := BISIM_RULES_defs.2.2
#eval do IO.println (repr BISIM_RULES); IO.println (repr BISIM_COINDUCT); IO.println (repr BISIM_CASES)

#eval phrase 29
def BISIM_REFL : thm := keep "BISIM_REFL" fun _ => (do
  prove ([[!(TR:S->L->S->bool) p. BISIM TR p p]])
   (REPEAT GEN_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[TR:S->L->S->bool]]), ([[\p q:S. p = q]])] BISIM_COINDUCT) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN MESON_TAC [],
      MESON_TAC []])
  : ExceptT String IO thm).run
#eval BISIM_REFL

#eval phrase 30
def BISIM_SYM : thm := keep "BISIM_SYM" fun _ => (do
  prove ([[!(TR:S->L->S->bool) p q. BISIM TR p q ==> BISIM TR q p]])
   (GEN_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[TR:S->L->S->bool]]), ([[\p q:S. BISIM (TR:S->L->S->bool) q p]])] BISIM_COINDUCT) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [REPEAT GEN_TAC THEN GEN_REWRITE_TAC HolLight.LAND_CONV [BISIM_CASES] THEN
      MESON_TAC [],
      MESON_TAC []])
  : ExceptT String IO thm).run
#eval BISIM_SYM

#eval phrase 31
def BISIM_TRANS : thm := keep "BISIM_TRANS" fun _ => (do
  prove ([[!(TR:S->L->S->bool) p q r.
        BISIM TR p q /\ BISIM TR q r ==> BISIM TR p r]])
   (GEN_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[TR:S->L->S->bool]]),
      ([[\p r:S. ?q. BISIM (TR:S->L->S->bool) p q /\ BISIM TR q r]])] BISIM_COINDUCT) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL [ALL_TAC, MESON_TAC []] THEN
    MAP_EVERY X_GEN_TAC [([[p:S]]), ([[r:S]])] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[q:S]]) (CONJUNCTS_THEN (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [BISIM_CASES]))) THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval BISIM_TRANS

#eval phrase 32
def bisimulation : thm := keep "bisimulation" fun _ => new_definition
 [[bisimulation (TR:S->L->S->bool) R <=>
    !p q. R p q
          ==> (!a p'. TR p a p' ==> ?q'. TR q a q' /\ R p' q') /\
              (!a q'. TR q a q' ==> ?p'. TR p a p' /\ R p' q')]]
#eval bisimulation

#eval phrase 33
def BISIM_BISIMULATION : thm := keep "BISIM_BISIMULATION" fun _ => (do
  prove ([[!(TR:S->L->S->bool) p q. BISIM TR p q <=> ?R. bisimulation TR R /\ R p q]])
   (REWRITE_TAC [bisimulation] THEN REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN EXISTS_TAC ([[BISIM(TR:S->L->S->bool)]]) THEN
      ASM_REWRITE_TAC [] THEN REPEAT GEN_TAC THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [BISIM_CASES] THEN SIMP_TAC [],
      DISCH_THEN (X_CHOOSE_THEN ([[R:S->S->bool]]) STRIP_ASSUME_TAC) THEN
      MP_TAC (← HolLight.ISPECL [([[TR:S->L->S->bool]]), ([[R:S->S->bool]])] BISIM_COINDUCT) THEN
      ASM_MESON_TAC []])
  : ExceptT String IO thm).run
#eval BISIM_BISIMULATION

/- Coinduction "up to bisimilarity": the derivatives of related states need  -/
/- only be related or bisimilar.                                             -/

#eval phrase 34
def BISIM_STRONG_COINDUCT : thm := keepIO "BISIM_STRONG_COINDUCT" fun _ =>
  derive_strong_coinduction BISIM_CASES BISIM_COINDUCT
#eval BISIM_STRONG_COINDUCT

#eval phrase 35
-- let TRACE_RULES,TRACE_INDUCT,TRACE_CASES = new_inductive_definition ...
def TRACE_RULES_defs : thm × thm × thm :=
  keepIO "TRACE_RULES_defs" fun _ => new_inductive_definition
  [[(!p. TRACE TR p []) /\
  (!p a q l. TR p a q /\ TRACE TR q l ==> TRACE TR (p:S) (CONS (a:L) l))]]
def TRACE_RULES : thm := TRACE_RULES_defs.1
def TRACE_INDUCT : thm := TRACE_RULES_defs.2.1
def TRACE_CASES : thm := TRACE_RULES_defs.2.2
#eval do IO.println (repr TRACE_RULES); IO.println (repr TRACE_INDUCT); IO.println (repr TRACE_CASES)

#eval phrase 36
def TRACE_CLAUSES : thm := keep "TRACE_CLAUSES" fun _ => (do
  prove ([[(!(TR:S->L->S->bool) p. TRACE TR p []) /\
   (!(TR:S->L->S->bool) p a l. TRACE TR p (CONS a l) <=>
                              ?q. TR p a q /\ TRACE TR q l)]])
   (REWRITE_TAC [TRACE_RULES] THEN REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [TRACE_CASES] THEN
    REWRITE_TAC [Session.listThms1.NOT_CONS_NIL, Session.listThms1.CONS_11] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval TRACE_CLAUSES

#eval phrase 37
def BISIM_TRACE : thm := keep "BISIM_TRACE" fun _ => (do
  prove ([[!(TR:S->L->S->bool) p q l.
        BISIM TR p q ==> (TRACE TR p l <=> TRACE TR q l)]])
   (GEN_TAC THEN
    SUBGOAL_THEN ([[!l p q. BISIM (TR:S->L->S->bool) p q ==> (TRACE TR p l <=> TRACE TR q l)]]) (fun th => MESON_TAC [th]) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [TRACE_CLAUSES] THEN
    REPEAT GEN_TAC THEN GEN_REWRITE_TAC HolLight.LAND_CONV [BISIM_CASES] THEN
    ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval BISIM_TRACE

/- An example transition system on numbers, with actions 1, 2 and 3 (a, b    -/
/- and c). States 0-3 are a.(b + c) and 10-14 are a.b + a.c, the classic     -/
/- pair with the same traces that are not bisimilar. State 20 is a one-state -/
/- a-loop, 30 and 31 a two-state a-loop, which is bisimilar to it, and 40 an -/
/- a-step into 20, which is bisimilar to 30 by coinduction up to             -/
/- bisimilarity.                                                             -/

#eval phrase 38
def EXAMPLE_TR : thm := keep "EXAMPLE_TR" fun _ => new_definition
 [[EXAMPLE_TR p (a:num) q <=>
        p = 0 /\ a = 1 /\ q = 1 \/ p = 1 /\ a = 2 /\ q = 2 \/
        p = 1 /\ a = 3 /\ q = 3 \/
        p = 10 /\ a = 1 /\ q = 11 \/ p = 10 /\ a = 1 /\ q = 12 \/
        p = 11 /\ a = 2 /\ q = 13 \/ p = 12 /\ a = 3 /\ q = 14 \/
        p = 20 /\ a = 1 /\ q = 20 \/
        p = 30 /\ a = 1 /\ q = 31 \/ p = 31 /\ a = 1 /\ q = 30 \/
        p = 40 /\ a = 1 /\ q = 20]]
#eval EXAMPLE_TR

#eval phrase 39
def NOT_BISIM_0_10 : thm := keep "NOT_BISIM_0_10" fun _ => (do
  prove ([[~BISIM EXAMPLE_TR 0 10]])
   (SUBGOAL_THEN ([[~BISIM EXAMPLE_TR 1 11 /\ ~BISIM EXAMPLE_TR 1 12]]) STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN GEN_REWRITE_TAC HolLight.RAND_CONV [BISIM_CASES] THENL
       [DISCH_THEN (MP_TAC o HolLight.SPECL [([[3]]), ([[3]])] o HolLight.CONJUNCT1),
        DISCH_THEN (MP_TAC o HolLight.SPECL [([[2]]), ([[2]])] o HolLight.CONJUNCT1)] THEN
      REWRITE_TAC [EXAMPLE_TR, ARITH_EQ],
      GEN_REWRITE_TAC HolLight.RAND_CONV [BISIM_CASES] THEN
      DISCH_THEN (MP_TAC o HolLight.SPECL [([[1]]), ([[1]])] o HolLight.CONJUNCT1) THEN
      REWRITE_TAC [EXAMPLE_TR, ARITH_EQ] THEN ASM_MESON_TAC []])
  : ExceptT String IO thm).run
#eval NOT_BISIM_0_10

#eval phrase 40
def TRACE_TERMINAL : thm := keep "TRACE_TERMINAL" fun _ => (do
  prove ([[!(TR:S->L->S->bool) p. (!a q. ~TR p a q) ==> !l. TRACE TR p l <=> l = [] ]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [TRACE_CLAUSES, Session.listThms1.NOT_CONS_NIL])
  : ExceptT String IO thm).run
#eval TRACE_TERMINAL

#eval phrase 41
def TRACE_0_10 : thm := keep "TRACE_0_10" fun _ => (do
  prove ([[!l. TRACE EXAMPLE_TR 0 l <=> TRACE EXAMPLE_TR 10 l]])
   (SUBGOAL_THEN ([[!p. p = 2 \/ p = 3 \/ p = 13 \/ p = 14
        ==> !l. TRACE EXAMPLE_TR p l <=> l = [] ]]) ASSUME_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC TRACE_TERMINAL THEN
      FIRST_X_ASSUM (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
      REWRITE_TAC [EXAMPLE_TR, ARITH_EQ],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!l. TRACE EXAMPLE_TR 1 l <=>
        TRACE EXAMPLE_TR 11 l \/ TRACE EXAMPLE_TR 12 l]]) ASSUME_TAC THENL
     [LIST_INDUCT_TAC THEN REWRITE_TAC [TRACE_CLAUSES, EXAMPLE_TR, ARITH_EQ] THEN
      ASM_MESON_TAC [],
      ALL_TAC] THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [TRACE_CLAUSES, EXAMPLE_TR, ARITH_EQ] THEN
    ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval TRACE_0_10

#eval phrase 42
def BISIM_20_30 : thm := keep "BISIM_20_30" fun _ => (do
  prove ([[BISIM EXAMPLE_TR 20 30 /\ BISIM EXAMPLE_TR 20 31]])
   (MP_TAC (← HolLight.ISPECL [([[EXAMPLE_TR]]), ([[\p q. p = 20 /\ (q = 30 \/ q = 31)]])] BISIM_COINDUCT) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [EXAMPLE_TR, ARITH_EQ] THEN MESON_TAC [],
      MESON_TAC []])
  : ExceptT String IO thm).run
#eval BISIM_20_30

#eval phrase 43
def BISIM_40_30 : thm := keep "BISIM_40_30" fun _ => (do
  prove ([[BISIM EXAMPLE_TR 40 30]])
   (MP_TAC (← HolLight.ISPECL [([[EXAMPLE_TR]]), ([[\p q. p = 40 /\ q = 30]])] BISIM_STRONG_COINDUCT) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [EXAMPLE_TR, ARITH_EQ] THEN MESON_TAC [BISIM_20_30],
      MESON_TAC []])
  : ExceptT String IO thm).run
#eval BISIM_40_30

/- ------------------------------------------------------------------------- -/
/- Language equivalence of states of a deterministic automaton, given by an  -/
/- acceptance predicate acc and a transition function delta. It coincides    -/
/- with bisimilarity, so two states accept the same words if (and only if)   -/
/- they are related by some bisimulation. That is the basis of algorithms    -/
/- such as Hopcroft and Karp's; see Rutten's "Automata and coinduction".     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 44
def RUN : thm := keep "RUN" fun _ => define
 [[(!s:S. RUN (delta:S->A->S) s [] = s) /\
  (!s a w. RUN delta s (CONS a w) = RUN delta (delta s a) w)]]
#eval RUN

#eval phrase 45
-- let DFA_BISIM_RULES,DFA_BISIM_COINDUCT,DFA_BISIM_CASES = new_coinductive_definition ...
def DFA_BISIM_RULES_defs : thm × thm × thm :=
  keepIO "DFA_BISIM_RULES_defs" fun _ => new_coinductive_definition
  [[!s t:S. (acc s <=> acc t) /\
          (!a:A. DFA_BISIM acc delta (delta s a) (delta t a))
          ==> DFA_BISIM acc delta s t]]
def DFA_BISIM_RULES : thm := DFA_BISIM_RULES_defs.1
def DFA_BISIM_COINDUCT : thm := DFA_BISIM_RULES_defs.2.1
def DFA_BISIM_CASES : thm := DFA_BISIM_RULES_defs.2.2
#eval do IO.println (repr DFA_BISIM_RULES); IO.println (repr DFA_BISIM_COINDUCT); IO.println (repr DFA_BISIM_CASES)

#eval phrase 46
def DFA_BISIM_LANGUAGE : thm := keep "DFA_BISIM_LANGUAGE" fun _ => (do
  prove ([[!acc delta s:S t.
        DFA_BISIM acc delta s t <=>
        !w:A list. acc(RUN delta s w) <=> acc(RUN delta t w)]])
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [SUBGOAL_THEN ([[!w:A list s:S t.
        DFA_BISIM acc delta s t
        ==> (acc(RUN delta s w) <=> acc(RUN delta t w))]]) (fun th => MESON_TAC [th]) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC [RUN] THEN REPEAT GEN_TAC THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [DFA_BISIM_CASES] THEN ASM_MESON_TAC [],
      SPEC_TAC (([[t:S]]), ([[t:S]])) THEN SPEC_TAC (([[s:S]]), ([[s:S]])) THEN
      MATCH_MP_TAC DFA_BISIM_COINDUCT THEN REWRITE_TAC [] THEN
      MAP_EVERY X_GEN_TAC [([[s:S]]), ([[t:S]])] THEN DISCH_TAC THEN CONJ_TAC THENL
       [FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[[]:A list]])) THEN REWRITE_TAC [RUN],
        MAP_EVERY X_GEN_TAC [([[a:A]]), ([[w:A list]])] THEN
        FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[CONS (a:A) w]])) THEN REWRITE_TAC [RUN]]])
  : ExceptT String IO thm).run
#eval DFA_BISIM_LANGUAGE

/- For example, in a counter that accepts at even values, the states 0 and 2 -/
/- are bisimilar, and so accept the same words.                              -/

#eval phrase 47
def DFA_BISIM_EVEN : thm := keep "DFA_BISIM_EVEN" fun _ => (do
  prove ([[DFA_BISIM EVEN (\n (a:A). n + 1) 0 2]])
   (MP_TAC (← HolLight.ISPECL [([[EVEN]]), ([[\n (a:A). n + 1]]), ([[\m n. n = m + 2]])] DFA_BISIM_COINDUCT) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL [ALL_TAC, MESON_TAC [ADD_CLAUSES]] THEN
    REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [EVEN_ADD, ARITH_EVEN] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval DFA_BISIM_EVEN

#eval phrase 48
def RUN_EVEN : thm := keep "RUN_EVEN" fun _ => (do
  prove ([[!w:A list. EVEN(RUN (\n a. n + 1) 0 w) <=> EVEN(RUN (\n a. n + 1) 2 w)]])
   (REWRITE_TAC [(← HolLight.GSYM DFA_BISIM_LANGUAGE), DFA_BISIM_EVEN])
  : ExceptT String IO thm).run
#eval RUN_EVEN

/- ------------------------------------------------------------------------- -/
/- Coinductive big-step semantics for a while-language with states of any    -/
/- type A (Leroy and Grall). The inductive EXEC relates a command and start  -/
/- state to the final state of a terminating execution. The same rules       -/
/- interpreted coinductively do not describe nontermination well, but the    -/
/- coinductive DIVERGES characterizes exactly the nonterminating cases.      -/
/- ------------------------------------------------------------------------- -/

#eval phrase 49
-- let cmd_INDUCT,cmd_RECURSION = define_type ...
def cmd_INDUCT_defs : thm × thm :=
  keepIO "cmd_INDUCT_defs" fun _ => define_type
  "cmd = Cskip
      | Cassign (A->A)
      | Cseq cmd cmd
      | Cif (A->bool) cmd cmd
      | Cwhile (A->bool) cmd"
def cmd_INDUCT : thm := cmd_INDUCT_defs.1
def cmd_RECURSION : thm := cmd_INDUCT_defs.2
#eval do IO.println (repr cmd_INDUCT); IO.println (repr cmd_RECURSION)

#eval phrase 50
-- let EXEC_RULES,EXEC_INDUCT,EXEC_CASES = new_inductive_definition ...
def EXEC_RULES_defs : thm × thm × thm :=
  keepIO "EXEC_RULES_defs" fun _ => new_inductive_definition
  [[(!s. EXEC Cskip s s) /\
  (!f s. EXEC (Cassign f) s (f s)) /\
  (!c1 c2 s t u. EXEC c1 s t /\ EXEC c2 t u ==> EXEC (Cseq c1 c2) s u) /\
  (!b c1 c2 s t. b s /\ EXEC c1 s t ==> EXEC (Cif b c1 c2) s t) /\
  (!b c1 c2 s t. ~b s /\ EXEC c2 s t ==> EXEC (Cif b c1 c2) s t) /\
  (!b c s. ~b s ==> EXEC (Cwhile b c) s s) /\
  (!b c s t u. b s /\ EXEC c s t /\ EXEC (Cwhile b c) t u
               ==> EXEC (Cwhile b c) (s:A) u)]]
def EXEC_RULES : thm := EXEC_RULES_defs.1
def EXEC_INDUCT : thm := EXEC_RULES_defs.2.1
def EXEC_CASES : thm := EXEC_RULES_defs.2.2
#eval do IO.println (repr EXEC_RULES); IO.println (repr EXEC_INDUCT); IO.println (repr EXEC_CASES)

#eval phrase 51
def EXEC_DETERMINISTIC : thm := keep "EXEC_DETERMINISTIC" fun _ => (do
  prove ([[!c s:A t t'. EXEC c s t /\ EXEC c s t' ==> t = t']])
   (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC EXEC_INDUCT THEN REPEAT STRIP_TAC THEN
    POP_ASSUM (MP_TAC o HolLight.ONCE_REWRITE_RULE [EXEC_CASES]) THEN
    REWRITE_TAC [distinctness "cmd", injectivity "cmd"] THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval EXEC_DETERMINISTIC

/- The coinductive interpretation of the same rules contains EXEC, but also  -/
/- makes an infinite loop relate any start state to any final state.         -/

#eval phrase 52
-- let COEXEC_RULES,COEXEC_COINDUCT,COEXEC_CASES = new_coinductive_definition ...
def COEXEC_RULES_defs : thm × thm × thm :=
  keepIO "COEXEC_RULES_defs" fun _ => new_coinductive_definition
  [[(!s. COEXEC Cskip s s) /\
  (!f s. COEXEC (Cassign f) s (f s)) /\
  (!c1 c2 s t u. COEXEC c1 s t /\ COEXEC c2 t u ==> COEXEC (Cseq c1 c2) s u) /\
  (!b c1 c2 s t. b s /\ COEXEC c1 s t ==> COEXEC (Cif b c1 c2) s t) /\
  (!b c1 c2 s t. ~b s /\ COEXEC c2 s t ==> COEXEC (Cif b c1 c2) s t) /\
  (!b c s. ~b s ==> COEXEC (Cwhile b c) s s) /\
  (!b c s t u. b s /\ COEXEC c s t /\ COEXEC (Cwhile b c) t u
               ==> COEXEC (Cwhile b c) (s:A) u)]]
def COEXEC_RULES : thm := COEXEC_RULES_defs.1
def COEXEC_COINDUCT : thm := COEXEC_RULES_defs.2.1
def COEXEC_CASES : thm := COEXEC_RULES_defs.2.2
#eval do IO.println (repr COEXEC_RULES); IO.println (repr COEXEC_COINDUCT); IO.println (repr COEXEC_CASES)

#eval phrase 53
def EXEC_COEXEC : thm := keep "EXEC_COEXEC" fun _ => (do
  prove ([[!c s:A t. EXEC c s t ==> COEXEC c s t]])
   (MATCH_MP_TAC COEXEC_COINDUCT THEN REWRITE_TAC [(← HolLight.GSYM EXEC_CASES)])
  : ExceptT String IO thm).run
#eval EXEC_COEXEC

#eval phrase 54
def COEXEC_WHILE_T : thm := keep "COEXEC_WHILE_T" fun _ => (do
  prove ([[!s t:A. COEXEC (Cwhile (\s. T) Cskip) s t]])
   (MP_TAC (← HolLight.ISPEC ([[\c (s:A) t. c = Cwhile (\s:A. T) Cskip \/ c = Cskip /\ t = s]]) COEXEC_COINDUCT) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL [ALL_TAC, MESON_TAC []] THEN
    MAP_EVERY X_GEN_TAC [([[c:(A)cmd]]), ([[s:A]]), ([[t:A]])] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [distinctness "cmd", injectivity "cmd"] THEN
    DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [([[\s:A. T]]), ([[Cskip:(A)cmd]]), ([[s:A]])] THEN
    REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval COEXEC_WHILE_T

#eval phrase 55
-- let DIVERGES_RULES,DIVERGES_COINDUCT,DIVERGES_CASES = new_coinductive_definition ...
def DIVERGES_RULES_defs : thm × thm × thm :=
  keepIO "DIVERGES_RULES_defs" fun _ => new_coinductive_definition
  [[(!c1 c2 s. DIVERGES c1 s ==> DIVERGES (Cseq c1 c2) s) /\
  (!c1 c2 s t. EXEC c1 s t /\ DIVERGES c2 t ==> DIVERGES (Cseq c1 c2) s) /\
  (!b c1 c2 s. b s /\ DIVERGES c1 s ==> DIVERGES (Cif b c1 c2) s) /\
  (!b c1 c2 s. ~b s /\ DIVERGES c2 s ==> DIVERGES (Cif b c1 c2) s) /\
  (!b c s. b s /\ DIVERGES c s ==> DIVERGES (Cwhile b c) s) /\
  (!b c s t. b s /\ EXEC c s t /\ DIVERGES (Cwhile b c) t
             ==> DIVERGES (Cwhile b c) (s:A))]]
def DIVERGES_RULES : thm := DIVERGES_RULES_defs.1
def DIVERGES_COINDUCT : thm := DIVERGES_RULES_defs.2.1
def DIVERGES_CASES : thm := DIVERGES_RULES_defs.2.2
#eval do IO.println (repr DIVERGES_RULES); IO.println (repr DIVERGES_COINDUCT); IO.println (repr DIVERGES_CASES)

#eval phrase 56
def DIVERGES_WHILE_T : thm := keep "DIVERGES_WHILE_T" fun _ => (do
  prove ([[!c s:A. (!s. ?t. EXEC c s t) ==> DIVERGES (Cwhile (\s. T) c) s]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPEC ([[\d (s:A). d = Cwhile (\s. T) (c:(A)cmd)]]) DIVERGES_COINDUCT) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL [ALL_TAC, MESON_TAC []] THEN
    REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [distinctness "cmd", injectivity "cmd"] THEN
    DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [([[\s:A. T]]), ([[c:(A)cmd]])] THEN
    ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval DIVERGES_WHILE_T

#eval phrase 57
def EXEC_NOT_DIVERGES : thm := keep "EXEC_NOT_DIVERGES" fun _ => (do
  prove ([[!c s:A t. EXEC c s t ==> ~DIVERGES c s]])
   (MATCH_MP_TAC (← ExceptT.mk (derive_strong_induction EXEC_RULES EXEC_INDUCT)) THEN
    REPEAT STRIP_TAC THEN
    POP_ASSUM (MP_TAC o HolLight.ONCE_REWRITE_RULE [DIVERGES_CASES]) THEN
    REWRITE_TAC [distinctness "cmd", injectivity "cmd"] THEN
    ASM_MESON_TAC [EXEC_DETERMINISTIC])
  : ExceptT String IO thm).run
#eval EXEC_NOT_DIVERGES

#eval phrase 58
def EXEC_OR_DIVERGES : thm := keep "EXEC_OR_DIVERGES" fun _ => (do
  let h1 ← tt (← ExceptT.mk [[p \/ q <=> ~p ==> q]])
  prove ([[!c s:A. (?t. EXEC c s t) \/ DIVERGES c s]])
   (REWRITE_TAC [h1] THEN
    MATCH_MP_TAC DIVERGES_COINDUCT THEN REWRITE_TAC [] THEN
    MAP_EVERY X_GEN_TAC [([[c:(A)cmd]]), ([[s:A]])] THEN
    STRUCT_CASES_TAC (← HolLight.ISPEC ([[c:(A)cmd]]) (cases "cmd")) THEN
    REWRITE_TAC [distinctness "cmd", injectivity "cmd"] THEN
    CONV_TAC (HolLight.TOP_DEPTH_CONV UNWIND_CONV) THEN MESON_TAC [EXEC_RULES])
  : ExceptT String IO thm).run
#eval EXEC_OR_DIVERGES

#eval phrase 59
def DIVERGES_EXEC : thm := keep "DIVERGES_EXEC" fun _ => (do
  prove ([[!c s:A. DIVERGES c s <=> !t. ~EXEC c s t]])
   (MESON_TAC [EXEC_NOT_DIVERGES, EXEC_OR_DIVERGES])
  : ExceptT String IO thm).run
#eval DIVERGES_EXEC

/- A loop counting down to zero terminates, and one counting up diverges.    -/

#eval phrase 60
def EXEC_COUNTDOWN : thm := keep "EXEC_COUNTDOWN" fun _ => (do
  prove ([[!n. EXEC (Cwhile (\n. ~(n = 0)) (Cassign PRE)) n 0]])
   (INDUCT_TAC THEN ONCE_REWRITE_TAC [EXEC_CASES] THEN
    REWRITE_TAC [distinctness "cmd", injectivity "cmd"] THEN
    CONV_TAC (HolLight.TOP_DEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC [NOT_SUC] THEN
    EXISTS_TAC ([[n:num]]) THEN ASM_MESON_TAC [EXEC_RULES, PRE])
  : ExceptT String IO thm).run
#eval EXEC_COUNTDOWN

#eval phrase 61
def DIVERGES_COUNTUP : thm := keep "DIVERGES_COUNTUP" fun _ => (do
  prove ([[!n. ~(n = 0) ==> DIVERGES (Cwhile (\n. ~(n = 0)) (Cassign SUC)) n]])
   (MP_TAC (← HolLight.ISPEC ([[\c n. c = Cwhile (\n. ~(n = 0)) (Cassign SUC) /\ ~(n = 0)]]) DIVERGES_COINDUCT) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL [ALL_TAC, MESON_TAC []] THEN
    MAP_EVERY X_GEN_TAC [([[c:(num)cmd]]), ([[n:num]])] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [distinctness "cmd", injectivity "cmd"] THEN
    DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [([[\n. ~(n = 0)]]), ([[Cassign SUC]]), ([[SUC n]])] THEN
    ASM_REWRITE_TAC [NOT_SUC, EXEC_RULES])
  : ExceptT String IO thm).run
#eval DIVERGES_COUNTUP

end HolExamples.Coinduction
