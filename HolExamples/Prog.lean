/- File: HolExamples/Prog.lean
Translation of HOL Light's Examples/prog.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolExamples.Common
open HolCore.Kernel Session HolLight.Syntax HolExamples
open HolLight (q)
open HolCore.Preterm (preterm pretype dpty)
open HolCore.Parser (lexcode ParserM pmapM pseqM porM paM ppossiblyM mkCtx parse_preterm
  install_parser delete_parser PErr)
open scoped HolLight
namespace HolExamples.Prog

/-- The session's IO-valued `prove`, lifted into `ExceptT String IO`. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/-- Run `new_inductive_definition`, panicking with HOL Light's message on
    failure (as the toplevel throws). -/
unsafe def newInductive (tm : term) : thm × thm × thm :=
  match unsafeIO (Session.new_inductive_definition tm) with
  | .ok (.ok t) => t
  | .ok (.error e) => panic! s!"new_inductive_definition: {e}"
  | .error e => panic! s!"new_inductive_definition IO: {e}"

/-- Run `define_type`, panicking with HOL Light's message on failure. -/
unsafe def defType (s : String) : thm × thm :=
  match unsafeIO (define_type s) with
  | .ok (.ok p) => p
  | .ok (.error e) => panic! s!"define_type: {e}"
  | .error e => panic! s!"define_type IO: {e}"

-- ========================================================================= --
-- Simple WHILE-language with relational semantics.                          --
-- ========================================================================= --

#eval phrase 1
#eval (Session.prioritize_num : IO Unit)

#eval phrase 2
#eval (parse_as_infix ("refined", (12, "right")) : IO Unit)

-- ------------------------------------------------------------------------- --
-- Logical operations "lifted" to predicates, for readability.               --
-- ------------------------------------------------------------------------- --

#eval phrase 3
#eval (parse_as_infix ("AND", (20, "right")) : IO Unit)

#eval phrase 4
#eval (parse_as_infix ("OR", (16, "right")) : IO Unit)

#eval phrase 5
#eval (parse_as_infix ("IMP", (13, "right")) : IO Unit)

#eval phrase 6
#eval (parse_as_infix ("IMPLIES", (12, "right")) : IO Unit)

#eval phrase 7
unsafe def FALSE : thm := keep "FALSE" fun _ => new_definition
  [[FALSE = \x:S. F]]
#eval FALSE

#eval phrase 8
unsafe def TRUE : thm := keep "TRUE" fun _ => new_definition
  [[TRUE = \x:S. T]]
#eval TRUE

#eval phrase 9
unsafe def NOT : thm := keep "NOT" fun _ => new_definition
  [[NOT p = \x:S. ~(p x)]]
#eval NOT

#eval phrase 10
unsafe def AND : thm := keep "AND" fun _ => new_definition
  [[p AND q = \x:S. p x /\ q x]]
#eval AND

#eval phrase 11
unsafe def OR : thm := keep "OR" fun _ => new_definition
  [[p OR q = \x:S. p x \/ q x]]
#eval OR

#eval phrase 12
unsafe def ANDS : thm := keep "ANDS" fun _ => new_definition
  [[ANDS P = \x:S. !p. P p ==> p x]]
#eval ANDS

#eval phrase 13
unsafe def ORS : thm := keep "ORS" fun _ => new_definition
  [[ORS P = \x:S. ?p. P p /\ p x]]
#eval ORS

#eval phrase 14
unsafe def IMP : thm := keep "IMP" fun _ => new_definition
  [[p IMP q = \x:S. p x ==> q x]]
#eval IMP

-- ------------------------------------------------------------------------- --
-- This one is different, corresponding to "subset".                         --
-- ------------------------------------------------------------------------- --

#eval phrase 15
unsafe def IMPLIES : thm := keep "IMPLIES" fun _ => new_definition
  [[p IMPLIES q <=> !x:S. p x ==> q x]]
#eval IMPLIES

-- ------------------------------------------------------------------------- --
-- Simple procedure to prove tautologies at the predicate level.             --
-- ------------------------------------------------------------------------- --

#eval phrase 16
-- let PRED_TAUT = let tac = ... in fun tm -> prove(tm,tac);;
unsafe def PRED_TAUT (tm : term) : ExceptT String IO thm :=
  let tac :=
    REWRITE_TAC [FALSE, TRUE, NOT, AND, OR, ANDS, ORS, IMP,
                IMPLIES, FUN_EQ_THM] THEN MESON_TAC []
  prove tm tac
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- Some applications.                                                        --
-- ------------------------------------------------------------------------- --

#eval phrase 17
unsafe def IMPLIES_TRANS : thm := keep "IMPLIES_TRANS" fun _ => (PRED_TAUT
  [[!p q r. p IMPLIES q /\ q IMPLIES r ==> p IMPLIES r]]).run
#eval IMPLIES_TRANS

-- ------------------------------------------------------------------------- --
-- Enumerated type of basic commands, and other derived commands.            --
-- ------------------------------------------------------------------------- --

#eval phrase 18
#eval (parse_as_infix ("Seq", (26, "right")) : IO Unit)

#eval phrase 19
unsafe def command_defs : thm × thm :=
  keep "command_defs" fun _ => defType
    "command = Assign (S->S)
           | Seq command command
           | Ite (S->bool) command command
           | While (S->bool) command"
unsafe def command_INDUCTION : thm := command_defs.1
unsafe def command_RECURSION : thm := command_defs.2
#eval do IO.println (repr command_INDUCTION); IO.println (repr command_RECURSION)

#eval phrase 20
unsafe def SKIP : thm := keep "SKIP" fun _ => new_definition
  [[SKIP = Assign I]]
#eval SKIP

#eval phrase 21
unsafe def ABORT : thm := keep "ABORT" fun _ => new_definition
  [[ABORT = While TRUE SKIP]]
#eval ABORT

#eval phrase 22
unsafe def «IF» : thm := keep "IF" fun _ => new_definition
  [[IF e c = Ite e c SKIP]]
#eval «IF»

#eval phrase 23
unsafe def DO : thm := keep "DO" fun _ => new_definition
  [[DO c e = c Seq (While e c)]]
#eval DO

#eval phrase 24
unsafe def ASSERT : thm := keep "ASSERT" fun _ => new_definition
  [[ASSERT g = Ite g SKIP ABORT]]
#eval ASSERT

-- ------------------------------------------------------------------------- --
-- Annotation commands, to allow insertion of loop (in)variants.             --
-- ------------------------------------------------------------------------- --

#eval phrase 25
unsafe def AWHILE : thm := keep "AWHILE" fun _ => new_definition
  [[AWHILE (i:S->bool) (v:S->S->bool) (e:S->bool) c = While e c]]
#eval AWHILE

#eval phrase 26
unsafe def ADO : thm := keep "ADO" fun _ => new_definition
  [[ADO (i:S->bool) (v:S->S->bool) c (e:S->bool) = DO c e]]
#eval ADO

-- ------------------------------------------------------------------------- --
-- Useful properties of type constructors for commands.                      --
-- ------------------------------------------------------------------------- --

#eval phrase 27
unsafe def command_DISTINCT : thm :=
  keep "command_DISTINCT" fun _ =>
    match distinctness "command" with | .ok t => t | .error e => panic! e
#eval command_DISTINCT

#eval phrase 28
unsafe def command_INJECTIVE : thm :=
  keep "command_INJECTIVE" fun _ =>
    match injectivity "command" with | .ok t => t | .error e => panic! e
#eval command_INJECTIVE

-- ------------------------------------------------------------------------- --
-- Relational semantics of commands.                                         --
-- ------------------------------------------------------------------------- --

#eval phrase 29
unsafe def sem_defs : thm × thm × thm :=
  keep "sem_defs" fun _ => newInductive
  [[(!f s. sem(Assign f) s (f s)) /\
   (!c1 c2 s s' s''. sem(c1) s s' /\ sem(c2) s' s''
                     ==> sem(c1 Seq c2) s s'') /\
   (!e c1 c2 s s'. e s /\ sem(c1) s s' ==> sem(Ite e c1 c2) s s') /\
   (!e c1 c2 s s'. ~(e s) /\ sem(c2) s s' ==> sem(Ite e c1 c2) s s') /\
   (!e c s. ~(e s) ==> sem(While e c) s s) /\
   (!e c s s' s''. e s /\ sem(c) s s' /\ sem(While e c) s' s''
               ==> sem(While e c) s s'')]]
unsafe def sem_RULES : thm := sem_defs.1
unsafe def sem_INDUCT : thm := sem_defs.2.1
unsafe def sem_CASES : thm := sem_defs.2.2
#eval do IO.println (repr sem_RULES); IO.println (repr sem_INDUCT); IO.println (repr sem_CASES)

-- ------------------------------------------------------------------------- --
-- A more "denotational" view of the semantics.                              --
-- ------------------------------------------------------------------------- --

#eval phrase 30
unsafe def SEM_ASSIGN : thm := keep "SEM_ASSIGN" fun _ => (prove
 ([[sem(Assign f) s s' <=> (s' = f s)]])
  (GEN_REWRITE_TAC HolLight.LAND_CONV [sem_CASES] THEN
  REWRITE_TAC [command_DISTINCT, command_INJECTIVE] THEN MESON_TAC [])).run
#eval SEM_ASSIGN

#eval phrase 31
unsafe def SEM_SEQ : thm := keep "SEM_SEQ" fun _ => (prove
 ([[sem(c1 Seq c2) s s' <=> ?s''. sem c1 s s'' /\ sem c2 s'' s']])
  (GEN_REWRITE_TAC HolLight.LAND_CONV [sem_CASES] THEN
  REWRITE_TAC [command_DISTINCT, command_INJECTIVE] THEN MESON_TAC [])).run
#eval SEM_SEQ

#eval phrase 32
unsafe def SEM_ITE : thm := keep "SEM_ITE" fun _ => (prove
 ([[sem(Ite e c1 c2) s s' <=> e s /\ sem c1 s s' \/
                             ~(e s) /\ sem c2 s s']])
  (GEN_REWRITE_TAC HolLight.LAND_CONV [sem_CASES] THEN
  REWRITE_TAC [command_DISTINCT, command_INJECTIVE] THEN MESON_TAC [])).run
#eval SEM_ITE

#eval phrase 33
unsafe def SEM_SKIP : thm := keep "SEM_SKIP" fun _ => (prove
 ([[sem(SKIP) s s' <=> (s' = s)]])
  (REWRITE_TAC [SKIP, SEM_ASSIGN, I_THM])).run
#eval SEM_SKIP

#eval phrase 34
unsafe def SEM_IF : thm := keep "SEM_IF" fun _ => (prove
 ([[sem(IF e c) s s' <=> e s /\ sem c s s' \/ ~(e s) /\ (s = s')]])
  (REWRITE_TAC [«IF», SEM_ITE, SEM_SKIP, EQ_SYM_EQ])).run
#eval SEM_IF

#eval phrase 35
unsafe def SEM_WHILE : thm := keep "SEM_WHILE" fun _ => (prove
 ([[sem(While e c) s s' <=> sem(IF e (c Seq While e c)) s s']])
  (GEN_REWRITE_TAC HolLight.LAND_CONV [sem_CASES] THEN
  REWRITE_TAC [FUN_EQ_THM, SEM_IF, SEM_SEQ] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC [command_DISTINCT, command_INJECTIVE] THEN MESON_TAC [])).run
#eval SEM_WHILE

#eval phrase 36
unsafe def SEM_ABORT : thm := keep "SEM_ABORT" fun _ => (do
  let lemma ← prove
   ([[!c s s'. sem c s s' ==> ~(c = ABORT)]])
    (MATCH_MP_TAC sem_INDUCT THEN
    REWRITE_TAC [command_DISTINCT, command_INJECTIVE, ABORT] THEN
    REWRITE_TAC [FUN_EQ_THM, TRUE] THEN MESON_TAC [])
  prove ([[sem(ABORT) s s' <=> F]]) (MESON_TAC [lemma])
  : ExceptT String IO thm).run
#eval SEM_ABORT

#eval phrase 37
unsafe def SEM_DO : thm := keep "SEM_DO" fun _ => (do
  prove ([[sem(DO c e) s s' <=> sem(c Seq IF e (DO c e)) s s']])
    (REWRITE_TAC [DO, SEM_SEQ, (← ExceptT.mk (HolLight.GSYM SEM_WHILE))])
  : ExceptT String IO thm).run
#eval SEM_DO

#eval phrase 38
unsafe def SEM_ASSERT : thm := keep "SEM_ASSERT" fun _ => (prove
 ([[sem(ASSERT g) s s' <=> g s /\ (s' = s)]])
  (REWRITE_TAC [ASSERT, SEM_ITE, SEM_SKIP, SEM_ABORT])).run
#eval SEM_ASSERT

-- ------------------------------------------------------------------------- --
-- Proofs that all commands are deterministic.                               --
-- ------------------------------------------------------------------------- --

#eval phrase 39
unsafe def deterministic : thm := keep "deterministic" fun _ => new_definition
  [[deterministic r <=> !s s1 s2. r s s1 /\ r s s2 ==> (s1 = s2)]]
#eval deterministic

#eval phrase 40
unsafe def DETERMINISM : thm := keep "DETERMINISM" fun _ => (do
  let g ← q r"!c:(S)command. deterministic(sem c)"
  let sg ← q r"!c s s1. sem c s s1 ==> !s2:S. sem c s s2 ==> (s1 = s2)"
  prove g
    (REWRITE_TAC [deterministic] THEN SUBGOAL_THEN sg
     (fun th => MESON_TAC [th]) THEN
    MATCH_MP_TAC sem_INDUCT THEN CONJ_TAC THENL
     [ALL_TAC, REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC] THEN
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [sem_CASES] THEN
    REWRITE_TAC [command_DISTINCT, command_INJECTIVE] THEN
    ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval DETERMINISM

-- ------------------------------------------------------------------------- --
-- Termination, weakest liberal precondition and weakest precondition.       --
-- ------------------------------------------------------------------------- --

#eval phrase 41
unsafe def terminates : thm := keep "terminates" fun _ => new_definition
  [[terminates c s <=> ?s'. sem c s s']]
#eval terminates

#eval phrase 42
unsafe def wlp : thm := keep "wlp" fun _ => new_definition
  [[wlp c q s <=> !s'. sem c s s' ==> q s']]
#eval wlp

#eval phrase 43
unsafe def wp : thm := keep "wp" fun _ => new_definition
  [[wp c q s <=> terminates c s /\ wlp c q s]]
#eval wp

-- ------------------------------------------------------------------------- --
-- Dijkstra's healthiness conditions (the last because of determinism).      --
-- ------------------------------------------------------------------------- --

#eval phrase 44
unsafe def WP_TOTAL : thm := keep "WP_TOTAL" fun _ => (prove
 ([[!c. (wp c FALSE = FALSE)]])
  (REWRITE_TAC [FUN_EQ_THM, wp, wlp, terminates, FALSE] THEN MESON_TAC [])).run
#eval WP_TOTAL

#eval phrase 45
unsafe def WP_MONOTONIC : thm := keep "WP_MONOTONIC" fun _ => (prove
 ([[q IMPLIES r ==> wp c q IMPLIES wp c r]])
  (REWRITE_TAC [IMPLIES, wp, wlp, terminates] THEN MESON_TAC [])).run
#eval WP_MONOTONIC

#eval phrase 46
unsafe def WP_CONJUNCTIVE : thm := keep "WP_CONJUNCTIVE" fun _ => (prove
 ([[(wp c q) AND (wp c r) = wp c (q AND r)]])
  (REWRITE_TAC [FUN_EQ_THM, wp, wlp, terminates, AND] THEN MESON_TAC [])).run
#eval WP_CONJUNCTIVE

#eval phrase 47
unsafe def WP_DISJUNCTIVE : thm := keep "WP_DISJUNCTIVE" fun _ => (prove
 ([[(wp c p) OR (wp c q) = wp c (p OR q)]])
  (REWRITE_TAC [FUN_EQ_THM, wp, wlp, OR, terminates] THEN
  MESON_TAC [REWRITE_RULE [deterministic] DETERMINISM])).run
#eval WP_DISJUNCTIVE

-- ------------------------------------------------------------------------- --
-- Weakest preconditions for the primitive and derived commands.             --
-- ------------------------------------------------------------------------- --

#eval phrase 48
unsafe def WP_ASSIGN : thm := keep "WP_ASSIGN" fun _ => (prove
 ([[!f q. wp (Assign f) q = q o f]])
  (REWRITE_TAC [wp, wlp, terminates, o_THM, FUN_EQ_THM, SEM_ASSIGN] THEN
  MESON_TAC [])).run
#eval WP_ASSIGN

#eval phrase 49
unsafe def WP_SEQ : thm := keep "WP_SEQ" fun _ => (prove
 ([[!c1 c2 q. wp (c1 Seq c2) q = wp c1 (wp c2 q)]])
  (REWRITE_TAC [wp, wlp, terminates, SEM_SEQ, FUN_EQ_THM] THEN
  MESON_TAC [REWRITE_RULE [deterministic] DETERMINISM])).run
#eval WP_SEQ

#eval phrase 50
unsafe def WP_ITE : thm := keep "WP_ITE" fun _ => (prove
 ([[!e c1 c2 q. wp (Ite e c1 c2) q = (e AND wp c1 q) OR (NOT e AND wp c2 q)]])
  (REWRITE_TAC [wp, wlp, terminates, SEM_ITE, FUN_EQ_THM, AND, OR, NOT] THEN
  MESON_TAC [])).run
#eval WP_ITE

#eval phrase 51
unsafe def WP_WHILE : thm := keep "WP_WHILE" fun _ => (do
  prove ([[!e c. wp (IF e (c Seq While e c)) q = wp (While e c) q]])
    (REWRITE_TAC [FUN_EQ_THM, wp, wlp, terminates, (← ExceptT.mk (HolLight.GSYM SEM_WHILE))])
  : ExceptT String IO thm).run
#eval WP_WHILE

#eval phrase 52
unsafe def WP_SKIP : thm := keep "WP_SKIP" fun _ => (prove
 ([[!q. wp SKIP q = q]])
  (REWRITE_TAC [FUN_EQ_THM, SKIP, WP_ASSIGN, I_THM, o_THM])).run
#eval WP_SKIP

#eval phrase 53
unsafe def WP_ABORT : thm := keep "WP_ABORT" fun _ => (prove
 ([[!q. wp ABORT q = FALSE]])
  (REWRITE_TAC [FUN_EQ_THM, wp, wlp, terminates, SEM_ABORT, FALSE])).run
#eval WP_ABORT

#eval phrase 54
unsafe def WP_IF : thm := keep "WP_IF" fun _ => (prove
 ([[!e c q. wp (IF e c) q = (e AND wp c q) OR (NOT e AND q)]])
  (REWRITE_TAC [«IF», WP_ITE, WP_SKIP])).run
#eval WP_IF

#eval phrase 55
unsafe def WP_DO : thm := keep "WP_DO" fun _ => (do
  prove ([[!e c. wp (c Seq IF e (DO c e)) q = wp (DO c e) q]])
    (REWRITE_TAC [FUN_EQ_THM, wp, wlp, terminates, (← ExceptT.mk (HolLight.GSYM SEM_DO))])
  : ExceptT String IO thm).run
#eval WP_DO

#eval phrase 56
unsafe def WP_ASSERT : thm := keep "WP_ASSERT" fun _ => (prove
 ([[!g q. wp (ASSERT g) q = g AND q]])
  (REWRITE_TAC [wp, wlp, terminates, SEM_ASSERT, FUN_EQ_THM, AND] THEN
  MESON_TAC [])).run
#eval WP_ASSERT

-- ------------------------------------------------------------------------- --
-- Rules for total correctness.                                              --
-- ------------------------------------------------------------------------- --

#eval phrase 57
unsafe def correct : thm := keep "correct" fun _ => new_definition
  [[correct p c q <=> p IMPLIES (wp c q)]]
#eval correct

#eval phrase 58
unsafe def CORRECT_PRESTRENGTH : thm := keep "CORRECT_PRESTRENGTH" fun _ => (prove
 ([[!p p' c q. p IMPLIES p' /\ correct p' c q ==> correct p c q]])
  (REWRITE_TAC [correct, IMPLIES_TRANS])).run
#eval CORRECT_PRESTRENGTH

#eval phrase 59
unsafe def CORRECT_POSTWEAK : thm := keep "CORRECT_POSTWEAK" fun _ => (prove
 ([[!p c q q'. correct p c q' /\ q' IMPLIES q ==> correct p c q]])
  (REWRITE_TAC [correct] THEN MESON_TAC [WP_MONOTONIC, IMPLIES_TRANS])).run
#eval CORRECT_POSTWEAK

#eval phrase 60
unsafe def CORRECT_ASSIGN : thm := keep "CORRECT_ASSIGN" fun _ => (prove
 ([[!p f q. (p IMPLIES (\s. q(f s))) ==> correct p (Assign f) q]])
  (REWRITE_TAC [correct, WP_ASSIGN, IMPLIES, o_THM])).run
#eval CORRECT_ASSIGN

#eval phrase 61
unsafe def CORRECT_SEQ : thm := keep "CORRECT_SEQ" fun _ => (prove
 ([[!p q r c1 c2.
        correct p c1 r /\ correct r c2 q ==> correct p (c1 Seq c2) q]])
  (REWRITE_TAC [correct, WP_SEQ, o_THM] THEN
  MESON_TAC [WP_MONOTONIC, IMPLIES_TRANS])).run
#eval CORRECT_SEQ

#eval phrase 62
unsafe def CORRECT_ITE : thm := keep "CORRECT_ITE" fun _ => (prove
 ([[!p e c1 c2 q.
       correct (p AND e) c1 q /\ correct (p AND (NOT e)) c2 q
       ==> correct p (Ite e c1 c2) q]])
  (REWRITE_TAC [correct, WP_ITE, AND, NOT, IMPLIES, OR] THEN MESON_TAC [])).run
#eval CORRECT_ITE

#eval phrase 63
unsafe def CORRECT_WHILE : thm := keep "CORRECT_WHILE" fun _ => (do
  let g ← q r"! (<<) p c q e invariant.
       WF(<<) /\
       p IMPLIES invariant /\
       (NOT e) AND invariant IMPLIES q /\
       (!X:S. correct
              (invariant AND e AND (\s. X = s)) c (invariant AND (\s. s << X)))
       ==> correct p (While e c) q"
  let sg1 ← q r"!s:S. invariant s ==> wp (While e c) q s"
  let ts ← q r"s:S"
  let gsw ← ExceptT.mk (HolLight.GSYM WP_WHILE)
  let es ← q r"(e:S->bool) s"
  let sg2 ← q r"wp c (\x:S. invariant x /\ x << s) (s:S) :bool"
  let sg3 ← q r"(\x:S. invariant x /\ x << (s:S)) IMPLIES wp (While e c) q"
  prove g
    (REWRITE_TAC [correct, IMPLIES, IN, AND, NOT] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN sg1 MP_TAC THENL
     [ALL_TAC, ASM_MESON_TAC []] THEN
    FIRST_ASSUM (MATCH_MP_TAC o HolLight.REWRITE_RULE [WF_IND]) THEN
    X_GEN_TAC ts THEN REPEAT DISCH_TAC THEN
    ONCE_REWRITE_TAC [gsw] THEN
    REWRITE_TAC [WP_IF, WP_SEQ, AND, OR, NOT, o_THM] THEN
    ASM_CASES_TAC es THEN ASM_REWRITE_TAC [] THENL
     [ALL_TAC, ASM_MESON_TAC []] THEN
    SUBGOAL_THEN sg2 MP_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN sg3
    MP_TAC THENL [REWRITE_TAC [IMPLIES] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    MESON_TAC [WP_MONOTONIC, IMPLIES])
  : ExceptT String IO thm).run
#eval CORRECT_WHILE

#eval phrase 64
unsafe def CORRECT_SKIP : thm := keep "CORRECT_SKIP" fun _ => (prove
 ([[!p q. (p IMPLIES q) ==> correct p SKIP q]])
  (REWRITE_TAC [correct, WP_SKIP])).run
#eval CORRECT_SKIP

#eval phrase 65
unsafe def CORRECT_ABORT : thm := keep "CORRECT_ABORT" fun _ => (prove
 ([[!p q. F ==> correct p ABORT q]])
  (REWRITE_TAC [])).run
#eval CORRECT_ABORT

#eval phrase 66
unsafe def CORRECT_IF : thm := keep "CORRECT_IF" fun _ => (prove
 ([[!p e c q.
        correct (p AND e) c q /\ (p AND (NOT e)) IMPLIES q
        ==> correct p (IF e c) q]])
  (REWRITE_TAC [correct, WP_IF, AND, NOT, IMPLIES, OR] THEN MESON_TAC [])).run
#eval CORRECT_IF

#eval phrase 67
unsafe def CORRECT_DO : thm := keep "CORRECT_DO" fun _ => (do
  let g ← q r"! (<<) p q c invariant.
        WF(<<) /\
        (e AND invariant) IMPLIES p /\
        ((NOT e) AND invariant) IMPLIES q /\
        (!X:S. correct
               (p AND (\s. X = s)) c (invariant AND (\s. s << X)))
        ==> correct p (DO c e) q"
  let inv ← q r"invariant:S->bool"
  let gwc ← ExceptT.mk (HolLight.GSYM WP_CONJUNCTIVE)
  let lt ← q r"(<<) :S->S->bool"
  let xs ← q r"X:S"
  let pax ← q r"p AND (\s:S. X = s)"
  let eai ← q r"(e:S->bool) AND invariant IMPLIES p"
  prove g
    (REPEAT STRIP_TAC THEN REWRITE_TAC [DO] THEN
    MATCH_MP_TAC CORRECT_SEQ THEN EXISTS_TAC inv THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [POP_ASSUM_LIST (fun ths => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.end_itlist HolLight.CONJ ths))) THEN
      REWRITE_TAC [correct, gwc] THEN
      REWRITE_TAC [AND, IMPLIES] THEN MESON_TAC [],
      MATCH_MP_TAC CORRECT_WHILE THEN
      MAP_EVERY EXISTS_TAC [lt, inv] THEN
      ASM_REWRITE_TAC [IMPLIES] THEN X_GEN_TAC xs THEN
      MATCH_MP_TAC CORRECT_PRESTRENGTH THEN
      EXISTS_TAC pax THEN ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC eai THEN
      REWRITE_TAC [AND, IMPLIES] THEN MESON_TAC []])
  : ExceptT String IO thm).run
#eval CORRECT_DO

#eval phrase 68
unsafe def CORRECT_ASSERT : thm := keep "CORRECT_ASSERT" fun _ => (prove
 ([[!p g q. p IMPLIES (g AND q) ==> correct p (ASSERT g) q]])
  (REWRITE_TAC [correct, WP_ASSERT])).run
#eval CORRECT_ASSERT

-- ------------------------------------------------------------------------- --
-- VCs for the basic commands (in fact only assign should be needed).        --
-- ------------------------------------------------------------------------- --

#eval phrase 69
unsafe def VC_ASSIGN : thm := keep "VC_ASSIGN" fun _ => (prove
 ([[p IMPLIES (q o f) ==> correct p (Assign f) q]])
  (REWRITE_TAC [o_DEF, CORRECT_ASSIGN])).run
#eval VC_ASSIGN

#eval phrase 70
unsafe def VC_SKIP : thm := keep "VC_SKIP" fun _ => (prove
 ([[p IMPLIES q ==> correct p SKIP q]])
  (REWRITE_TAC [CORRECT_SKIP])).run
#eval VC_SKIP

#eval phrase 71
unsafe def VC_ABORT : thm := keep "VC_ABORT" fun _ => (prove
 ([[F ==> correct p ABORT q]])
  (MATCH_ACCEPT_TAC CORRECT_ABORT)).run
#eval VC_ABORT

#eval phrase 72
unsafe def VC_ASSERT : thm := keep "VC_ASSERT" fun _ => (prove
 ([[p IMPLIES (b AND q) ==> correct p (ASSERT b) q]])
  (REWRITE_TAC [CORRECT_ASSERT])).run
#eval VC_ASSERT

-- ------------------------------------------------------------------------- --
-- VCs for composite commands other than sequences.                          --
-- ------------------------------------------------------------------------- --

#eval phrase 73
unsafe def VC_ITE : thm := keep "VC_ITE" fun _ => (prove
 ([[correct (p AND e) c1 q /\ correct (p AND NOT e) c2 q
   ==> correct p (Ite e c1 c2) q]])
  (REWRITE_TAC [CORRECT_ITE])).run
#eval VC_ITE

#eval phrase 74
unsafe def VC_IF : thm := keep "VC_IF" fun _ => (prove
 ([[correct (p AND e) c q /\ p AND NOT e IMPLIES q
   ==> correct p (IF e c) q]])
  (REWRITE_TAC [CORRECT_IF])).run
#eval VC_IF

#eval phrase 75
unsafe def VC_AWHILE_VARIANT : thm := keep "VC_AWHILE_VARIANT" fun _ => (do
  let g ← q r"WF(<<) /\
   p IMPLIES invariant /\
   (NOT e) AND invariant IMPLIES q /\
   (!X. correct
        (invariant AND e AND (\s. X = s)) c (invariant AND (\s. s << X)))
   ==> correct p (AWHILE invariant (<<) e c) q"
  prove g
    (REWRITE_TAC [AWHILE, CORRECT_WHILE])
  : ExceptT String IO thm).run
#eval VC_AWHILE_VARIANT

#eval phrase 76
unsafe def VC_AWHILE_MEASURE : thm := keep "VC_AWHILE_MEASURE" fun _ => (do
  let g ← q r"p IMPLIES invariant /\
   (NOT e) AND invariant IMPLIES q /\
   (!X. correct
          (invariant AND e AND (\s:S. X = m(s)))
          c
          (invariant AND (\s. m(s) < X)))
   ==> correct p (AWHILE invariant (MEASURE m) e c) q"
  let xs ← q r"X:S"
  let mx ← q r"(m:S->num) X"
  prove g
    (STRIP_TAC THEN MATCH_MP_TAC VC_AWHILE_VARIANT THEN
    ASM_REWRITE_TAC [WF_MEASURE] THEN
    X_GEN_TAC xs THEN FIRST_ASSUM (MP_TAC o SPEC mx) THEN
    REWRITE_TAC [correct, AND, IMPLIES, MEASURE] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval VC_AWHILE_MEASURE

#eval phrase 77
unsafe def VC_ADO_VARIANT : thm := keep "VC_ADO_VARIANT" fun _ => (do
  let g ← q r"WF(<<) /\
   (e AND invariant) IMPLIES p /\
   ((NOT e) AND invariant) IMPLIES q /\
   (!X. correct
          (p AND (\s. X = s)) c (invariant AND (\s. s << X)))
   ==> correct p (ADO invariant (<<) c e) q"
  prove g
    (REWRITE_TAC [ADO, CORRECT_DO])
  : ExceptT String IO thm).run
#eval VC_ADO_VARIANT

#eval phrase 78
unsafe def VC_ADO_MEASURE : thm := keep "VC_ADO_MEASURE" fun _ => (do
  let g ← q r"(e AND invariant) IMPLIES p /\
   ((NOT e) AND invariant) IMPLIES q /\
   (!X. correct
          (p AND (\s:S. X = m(s))) c (invariant AND (\s. m(s) < X)))
   ==> correct p (ADO invariant (MEASURE m) c e) q"
  let xs ← q r"X:S"
  let mx ← q r"(m:S->num) X"
  prove g
    (STRIP_TAC THEN MATCH_MP_TAC VC_ADO_VARIANT THEN
    ASM_REWRITE_TAC [WF_MEASURE] THEN
    X_GEN_TAC xs THEN FIRST_ASSUM (MP_TAC o SPEC mx) THEN
    REWRITE_TAC [correct, AND, IMPLIES, MEASURE] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval VC_ADO_MEASURE

-- ------------------------------------------------------------------------- --
-- VCs for sequences of commands, using intelligence where possible.         --
-- ------------------------------------------------------------------------- --

#eval phrase 79
unsafe def VC_SEQ_ASSERT_LEFT : thm := keep "VC_SEQ_ASSERT_LEFT" fun _ => (do
  let l1 ← PRED_TAUT [[(p IMPLIES b) ==> (p IMPLIES b AND p)]]
  prove ([[p IMPLIES b /\ correct b c q ==> correct p (ASSERT b Seq c) q]])
    (MESON_TAC [CORRECT_SEQ, CORRECT_ASSERT, CORRECT_PRESTRENGTH, l1])
  : ExceptT String IO thm).run
#eval VC_SEQ_ASSERT_LEFT

#eval phrase 80
unsafe def VC_SEQ_ASSERT_RIGHT : thm := keep "VC_SEQ_ASSERT_RIGHT" fun _ => (do
  let l1 ← PRED_TAUT [[(p IMPLIES b) ==> (p IMPLIES p AND b)]]
  prove ([[correct p c b /\ b IMPLIES q ==> correct p (c Seq (ASSERT b)) q]])
    (MESON_TAC [CORRECT_SEQ, CORRECT_ASSERT, l1])
  : ExceptT String IO thm).run
#eval VC_SEQ_ASSERT_RIGHT

#eval phrase 81
unsafe def VC_SEQ_ASSERT_MIDDLE : thm := keep "VC_SEQ_ASSERT_MIDDLE" fun _ => (do
  let l1 ← PRED_TAUT [[b IMPLIES b AND b]]
  prove ([[correct p c b /\ correct b c' q
   ==> correct p (c Seq (ASSERT b) Seq c') q]])
    (MESON_TAC [CORRECT_SEQ, CORRECT_ASSERT, l1])
  : ExceptT String IO thm).run
#eval VC_SEQ_ASSERT_MIDDLE

#eval phrase 82
unsafe def VC_SEQ_ASSIGN_LEFT : thm := keep "VC_SEQ_ASSIGN_LEFT" fun _ => (prove
 ([[(p o f = p) /\ (f o f = f) /\
   correct (p AND (\s:S. s = f s)) c q
   ==> correct p ((Assign f) Seq c) q]])
  (REWRITE_TAC [FUN_EQ_THM, o_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC CORRECT_SEQ THEN EXISTS_TAC [[p AND (\s:S. s = f s)]] THEN
  ASM_REWRITE_TAC [] THEN MATCH_MP_TAC VC_ASSIGN THEN
  ASM_REWRITE_TAC [IMPLIES, AND, o_THM])).run
#eval VC_SEQ_ASSIGN_LEFT

#eval phrase 83
unsafe def VC_SEQ_ASSIGN_RIGHT : thm := keep "VC_SEQ_ASSIGN_RIGHT" fun _ => (do
  let l1 ← PRED_TAUT [[(p:S->bool) IMPLIES p]]
  prove ([[correct p c (q o f) ==> correct p (c Seq (Assign f)) q]])
    (MESON_TAC [CORRECT_SEQ, VC_ASSIGN, l1])
  : ExceptT String IO thm).run
#eval VC_SEQ_ASSIGN_RIGHT

-- ------------------------------------------------------------------------- --
-- Parser for correctness assertions.                                        --
-- ------------------------------------------------------------------------- --

#eval phrase 84
-- let rec dive_to_var ptm = ...
partial def dive_to_var : preterm → Except String preterm
  | (.Varp n ty)  => .ok (.Varp n ty)
  | (.Typing t _) => dive_to_var t
  | _             => .error "fail"
#eval IO.println "<fun>"

#eval phrase 85
-- let reserve_program_words,unreserve_program_words = ...
unsafe def program_words : List String :=
  ["var", "end", "skip", "abort", ":=", "if", "then", "else", "while", "do"]
unsafe def reserve_program_words : Unit → IO Unit :=
  fun _ => HolCore.Printer.reserve_words program_words
unsafe def unreserve_program_words : Unit → IO Unit :=
  fun _ => HolCore.Printer.unreserve_words program_words
#eval (do IO.println "<fun>"; IO.println "<fun>" : IO Unit)

#eval phrase 86
#eval (reserve_program_words () : IO Unit)

#eval phrase 87
-- let parse_program,parse_program_assertion = ... (parser.ml combinators)
private def pp_varname (ptm : preterm) : Except String String := do
  match ← dive_to_var ptm with
  | .Varp n _ => .ok n
  | _ => .error "fail"
-- `let rec assign s v e = ...`
private partial def pp_assign (s : preterm) (v : String) (e : preterm) :
    Except String preterm := do
  match s with
  | .Combp (.Combp pop lptm) rptm =>
      if (← pp_varname pop) == "," then
        pure (.Combp (.Combp pop (← pp_assign lptm v e)) (← pp_assign rptm v e))
      else .error "fail"
  | _ => do if (← pp_varname s) == v then pure e else pure s
private def pp_lmk_assign (s : preterm) (v : String) (e : preterm) :
    Except String preterm := do
  pure (.Combp (preterm.Varp "Assign" dpty) (.Absp s (← pp_assign s v e)))
private def pp_lmk_seq (c : preterm) (cs : List preterm) : preterm :=
  match cs with | [] => c | h :: _ => .Combp (.Combp (preterm.Varp "Seq" dpty) c) h
private def pp_lmk_ite (e c1 c2 : preterm) : preterm :=
  .Combp (.Combp (.Combp (preterm.Varp "Ite" dpty) e) c1) c2
private def pp_lmk_while (e c : preterm) : preterm :=
  .Combp (.Combp (preterm.Varp "While" dpty) e) c
private def pp_lmk_skip (_ : lexcode) : preterm := preterm.Varp "SKIP" dpty
private def pp_lmk_abort (_ : lexcode) : preterm := preterm.Varp "ABORT" dpty
private def pp_lmk_if (e c : preterm) : preterm :=
  .Combp (.Combp (preterm.Varp "IF" dpty) e) c
private def pp_lmk_do (c e : preterm) : preterm :=
  .Combp (.Combp (preterm.Varp "DO" dpty) c) e
private def pp_lmk_assert (e : preterm) : preterm := .Combp (preterm.Varp "ASSERT" dpty) e
private def pp_lmk_awhile (i v e c : preterm) : preterm :=
  .Combp (.Combp (.Combp (.Combp (preterm.Varp "AWHILE" dpty) i) v) e) c
private def pp_lmk_ado (i v c e : preterm) : preterm :=
  .Combp (.Combp (.Combp (.Combp (preterm.Varp "ADO" dpty) i) v) c) e
private def pp_lmk_gwhile (al : List (preterm × preterm)) (e c : preterm) : preterm :=
  match al with | [] => pp_lmk_while e c | (i, v) :: _ => pp_lmk_awhile i v e c
private def pp_lmk_gdo (al : List (preterm × preterm)) (c e : preterm) : preterm :=
  match al with | [] => pp_lmk_do c e | (i, v) :: _ => pp_lmk_ado i v c e
-- `let expression s = parse_preterm >> (fun p -> Absp(s,p))`
private unsafe def pp_expression (s : preterm) : ParserM preterm :=
  pmapM parse_preterm (fun p => .Absp s p)
-- `let identifier = function (Ident n)::rest -> n,rest | _ -> raise Noparse`
private unsafe def pp_identifier : ParserM String := fun _ inp => do
  match inp with
  | (.Ident n) :: rest => pure (.ok (n, rest))
  | _ => pure (.error .noparse)
-- `let variant s = (a (Ident "variant") ++ parse_preterm >> snd) ||| ...`
private unsafe def pp_variant (s : preterm) : ParserM preterm :=
  porM
    (pmapM (pseqM (paM (.Ident "variant")) parse_preterm) Prod.snd)
    (pmapM (pseqM (paM (.Ident "measure")) (pp_expression s))
      (fun x => .Combp (preterm.Varp "MEASURE" dpty) x.2))
-- `let annotation s = a "[" ++ a "invariant" ++ expression s ++ a ";" ++ variant s ++ a "]" >> ...`
private unsafe def pp_annotation (s : preterm) : ParserM (preterm × preterm) :=
  pmapM
    (pseqM (pseqM (pseqM (pseqM (pseqM
      (paM (.Resword "[")) (paM (.Ident "invariant"))) (pp_expression s))
      (paM (.Resword ";"))) (pp_variant s)) (paM (.Resword "]")))
    (fun x => let ((((( _, _), i), _), v), _) := x; (i, v))
-- `let rec command s i = (...) i and commands s i = (...) i`
mutual
private unsafe def pp_command (s : preterm) : ParserM preterm := fun c i =>
  (HolCore.Parser.pfirstM
   [ pmapM (pseqM (pseqM (paM (.Resword "(")) (pp_commands s)) (paM (.Resword ")")))
       (fun x => x.1.2),
     pmapM (paM (.Resword "skip")) pp_lmk_skip,
     pmapM (paM (.Resword "abort")) pp_lmk_abort,
     pmapM (pseqM (pseqM (pseqM (pseqM (paM (.Resword "if")) (pp_expression s))
       (paM (.Resword "then"))) (pp_command s))
       (ppossiblyM (pmapM (pseqM (paM (.Resword "else")) (pp_command s)) Prod.snd)))
       (fun x =>
         let (((( _, e), _), cc), cs) := x
         match cs with | [] => pp_lmk_if e cc | h :: _ => pp_lmk_ite e cc h),
     pmapM (pseqM (pseqM (pseqM (paM (.Resword "while")) (pp_expression s))
       (paM (.Resword "do"))) (pseqM (ppossiblyM (pp_annotation s)) (pp_command s)))
       (fun x => let (((( _, e), _), (al, cc))) := x; pp_lmk_gwhile al e cc),
     pmapM (pseqM (pseqM (pseqM (paM (.Resword "do")) (ppossiblyM (pp_annotation s)))
       (pp_command s)) (pseqM (paM (.Resword "while")) (pp_expression s)))
       (fun x => let (((( _, al), cc), (_, e))) := x; pp_lmk_gdo al cc e),
     pmapM (pseqM (pseqM (paM (.Resword "{")) (pp_expression s)) (paM (.Resword "}")))
       (fun x => pp_lmk_assert x.1.2),
     HolCore.Parser.pmapME (pseqM (pseqM pp_identifier (paM (.Resword ":="))) parse_preterm)
       (fun x => let ((v, _), e) := x; pp_lmk_assign s v e) ]) c i
private unsafe def pp_commands (s : preterm) : ParserM preterm := fun c i =>
  (pmapM (pseqM (pp_command s)
     (ppossiblyM (pmapM (pseqM (paM (.Resword ";")) (pp_commands s)) Prod.snd)))
     (fun x => pp_lmk_seq x.1 x.2)) c i
end
-- `let program i = let ((_,s),_),r = (a "var" ++ parse_preterm ++ a ";") i in ...`
private unsafe def pp_program : ParserM (preterm × preterm) := fun c i => do
  match ← (pseqM (pseqM (paM (.Resword "var")) parse_preterm) (paM (.Resword ";"))) c i with
  | .error e => pure (.error e)
  | .ok ((((_, s), _), r)) =>
    match ← (pmapM (pseqM (pp_commands s) (paM (.Resword "end"))) Prod.fst) c r with
    | .error e => pure (.error e)
    | .ok (cc, r') => pure (.ok ((s, cc), r'))
-- `let assertion = a "correct" ++ parse_preterm ++ program ++ parse_preterm >> ...`
private unsafe def pp_assertion : ParserM preterm :=
  pmapM (pseqM (pseqM (pseqM (paM (.Ident "correct")) parse_preterm) pp_program) parse_preterm)
    (fun x =>
      let ((( _, p), (s, cc)), qq) := x
      preterm.Combp (.Combp (.Combp (preterm.Varp "correct" dpty) (.Absp s p)) cc) (.Absp s qq))
unsafe def parse_program : HolCore.Parser.UserParser := fun inp => do
  (pmapM pp_program Prod.snd) (← mkCtx) inp
unsafe def parse_program_assertion : HolCore.Parser.UserParser := fun inp => do
  pp_assertion (← mkCtx) inp
#eval (do IO.println "<fun>"; IO.println "<fun>" : IO Unit)

-- ------------------------------------------------------------------------- --
-- Introduce the variables in the VCs.                                       --
-- ------------------------------------------------------------------------- --

/-- `repair` (shared by STATE_GEN_TAC / STATE_GEN_TAC'): `PAIR_CONV` is
    `REWR_CONV(GSYM PAIR)`.  `try ... with Failure _ -> REFL v,((v,vs)::acc)`. -/
private unsafe def stateRepair (PAIR_CONV : term → IO (Except String thm)) :
    term → term → List (term × term) → IO (thm × List (term × term)) :=
  fun vs v acc => do
    let res : Except String (thm × List (term × term)) ← (do
      let (l, r) ← ExceptT.mk (pure (dest_pair vs))
      let th ← ExceptT.mk (PAIR_CONV v)
      let tm ← ExceptT.mk (pure (rand (concl th)))
      let rtm ← ExceptT.mk (pure (rator tm))
      let randrtm ← ExceptT.mk (pure (rand rtm))
      let (lth, acc1) ← ExceptT.mk (do pure (.ok (← stateRepair PAIR_CONV l randrtm acc)))
      let randtm ← ExceptT.mk (pure (rand tm))
      let (rth, acc2) ← ExceptT.mk (do pure (.ok (← stateRepair PAIR_CONV r randtm acc1)))
      let aptm ← ExceptT.mk (pure (HolCore.Equal.AP_TERM (← ExceptT.mk (pure (rator rtm))) lth))
      let mkc ← ExceptT.mk (pure (HolCore.Kernel.MK_COMB aptm rth))
      let trs ← ExceptT.mk (pure (HolCore.Kernel.TRANS th mkc))
      pure (trs, acc2)
      : ExceptT String IO (thm × List (term × term))).run
    match res with
    | .ok out => pure out
    | .error _ => pure (HolCore.Kernel.REFL v, (v, vs) :: acc)

/-- `end_itlist (curry mk_pair)`: right-fold a nonempty list into a pair term. -/
private unsafe def endItlistMkPair : List term → IO (Except String term)
  | [] => pure (.error "end_itlist")
  | [x] => pure (.ok x)
  | x :: xs => do
    match ← endItlistMkPair xs with
    | .error e => pure (.error e)
    | .ok r => Session.mk_pair (x, r)

#eval phrase 88
-- let STATE_GEN_TAC = ...
unsafe def STATE_GEN_TAC : HolCore.Tactics.tactic := fun (asl, w) => do
  match ← (do
    let gp ← HolLight.GSYM PAIR
    let PAIR_CONV := Session.REWR_CONV gp
    let abstm ← liftExcept (HolCore.Basics.find_term (fun t => !(is_abs t) && HolCore.Basics.is_gabs t) w)
    let vs ← liftExcept (Prod.fst <$> HolCore.Basics.dest_gabs abstm)
    let fw ← liftExcept (HolCore.Basics.dest_forall w)
    let v ← (HolCore.Basics.genvar (type_of fw.1) : IO term)
    let (th, gens) ← (stateRepair PAIR_CONV vs v [] : IO (thm × List (term × term)))
    pure ((Session.X_GEN_TAC v THEN Session.SUBST1_TAC th THEN
           Session.MAP_EVERY Session.SPEC_TAC gens THEN Session.REPEAT Session.GEN_TAC) : HolCore.Tactics.tactic)
    : ExceptT String IO HolCore.Tactics.tactic).run with
  | .ok tac => tac (asl, w)
  | .error e => pure (.error e)
#eval IO.println "<fun>"

#eval phrase 89
-- let STATE_GEN_TAC' = ... (variant-renaming version)
unsafe def STATE_GEN_TAC' : HolCore.Tactics.tactic := fun (asl, w) => do
  match ← (do
    let gp ← HolLight.GSYM PAIR
    let PAIR_CONV := Session.REWR_CONV gp
    let abstm ← liftExcept (HolCore.Basics.find_term (fun t => !(is_abs t) && HolCore.Basics.is_gabs t) w)
    let vs0 ← liftExcept (Prod.fst <$> HolCore.Basics.dest_gabs abstm)
    let vl0 := HolCore.Lib.striplist dest_pair vs0
    let conjl ← liftExcept (HolCore.Bool.list_mk_conj (w :: asl.map (fun p => concl p.2)))
    let avoid ← liftExcept (HolCore.Basics.variables conjl)
    let vl ← liftExcept (vl0.mapM (fun x => HolCore.Kernel.variant avoid x))
    let vs ← ExceptT.mk (endItlistMkPair vl)
    let fw ← liftExcept (HolCore.Basics.dest_forall w)
    let v ← (HolCore.Basics.genvar (type_of fw.1) : IO term)
    let (th, gens) ← (stateRepair PAIR_CONV vs v [] : IO (thm × List (term × term)))
    pure ((Session.X_GEN_TAC v THEN Session.SUBST1_TAC th THEN
           Session.MAP_EVERY Session.SPEC_TAC gens THEN Session.REPEAT Session.GEN_TAC) : HolCore.Tactics.tactic)
    : ExceptT String IO HolCore.Tactics.tactic).run with
  | .ok tac => tac (asl, w)
  | .error e => pure (.error e)
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- Tidy up a verification condition.                                         --
-- ------------------------------------------------------------------------- --

#eval phrase 90
-- let VC_UNPACK_TAC = ...
unsafe def VC_UNPACK_TAC : HolCore.Tactics.tactic := fun g => do
  match ← (HolLight.GSYM CONJ_ASSOC).run with
  | .error e => pure (.error e)
  | .ok ca =>
    (REWRITE_TAC [IMPLIES, o_THM, FALSE, TRUE, AND, OR, NOT, IMP] THEN
     STATE_GEN_TAC THEN CONV_TAC (HolLight.REDEPTH_CONV GEN_BETA_CONV) THEN
     REWRITE_TAC [PAIR_EQ, ca]) g
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- Calculate a (pseudo-) weakest precondition for command.                   --
-- ------------------------------------------------------------------------- --

#eval phrase 91
-- let find_pwp = ...
unsafe def find_pwp_wpths : List term := keep "find_pwp_wpths" fun _ =>
  match unsafeIO ((do
    let aw ← q r"wp (AWHILE i v e c) q = i"
    let ad ← q r"wp (ADO i v c e) q = i"
    pure (([WP_ASSIGN, WP_ITE, WP_SKIP, WP_ABORT, WP_IF, WP_ASSERT].map
      (fun th => (HolCore.Basics.strip_forall (concl th)).2)) ++ [aw, ad])
    : ExceptT String IO (List term)).run) with
  | .ok (.ok l) => l
  | .ok (.error e) => panic! e
  | .error e => panic! (toString e)
unsafe def find_pwp (tm : term) (qq : term) : IO (Except String term) := (do
  let wpths := find_pwp_wpths
  let conv (t : term) : ExceptT String IO term :=
    ExceptT.mk (HolCore.Lib.tryfindM (fun tt => (do
      let m ← ExceptT.mk (Session.term_match [] (← liftExcept (HolCore.Equal.lhand tt)) t)
      let it ← liftExcept (Session.instantiate m tt)
      liftExcept (rand it)).run) wpths)
  let wptm ← ExceptT.mk (HolCore.Basics.list_mk_icomb "wp" [tm])
  conv (← liftExcept (mk_comb wptm qq))
  : ExceptT String IO term).run
#eval (IO.println (if find_pwp_wpths.length == 999999 then "" else "<fun>") : IO Unit)

-- ------------------------------------------------------------------------- --
-- Tools for automatic VC generation from annotated program.                 --
-- ------------------------------------------------------------------------- --

#eval phrase 92
-- let VC_SEQ_TAC = ...
private unsafe def vcSeq_is_assert (tm : term) : Bool :=
  match (do pure ((← HolCore.Kernel.dest_const (← rator tm)).1 == "ASSERT")) with
  | .ok b => b | .error _ => false
private unsafe def vcSeq_is_assign (tm : term) : Bool :=
  match (do pure ((← HolCore.Kernel.dest_const (← rator tm)).1 == "Assign")) with
  | .ok b => b | .error _ => false
private unsafe def vcSeq_SIDE_TAC : HolCore.Tactics.tactic :=
  GEN_REWRITE_TAC HolCore.Lib.I [FUN_EQ_THM] THEN STATE_GEN_TAC THEN
  PURE_REWRITE_TAC [IMPLIES, o_THM, FALSE, TRUE, AND, OR, NOT, IMP] THEN
  CONV_TAC (HolLight.REDEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC [PAIR_EQ] THEN Session.NO_TAC
private unsafe def vcSeq_ADJUST_TAC (ptm ptm' : term) : HolCore.Tactics.tactic :=
  fun (asl, w) => do
    match ← (do
      let substFn ← ExceptT.mk (HolCore.Basics.subst [(ptm', ptm)])
      let w' ← ExceptT.mk (substFn w)
      let eqtm := HolCore.Kernel.safe_mk_eq w w'
      let rc ← ExceptT.mk (Session.REWRITE_CONV [correct, WP_SEQ] eqtm)
      let th ← EQT_ELIM rc
      pure (GEN_REWRITE_TAC HolCore.Lib.I [th] : HolCore.Tactics.tactic)
      : ExceptT String IO HolCore.Tactics.tactic).run with
    | .ok tac => tac (asl, w)
    | .error e => pure (.error e)
unsafe def VC_SEQ_TAC : HolCore.Tactics.tactic := fun (asl, w) => do
  -- Set up the common data (dest_comb/striplist/seq); a failure here aborts.
  match ← (do
    let (cptm, qq) ← liftExcept (dest_comb w)
    let (_cpt, ptm) ← liftExcept (dest_comb cptm)
    let ptms := HolCore.Lib.striplist (HolCore.Basics.dest_binary "Seq") ptm
    let seq ← liftExcept (do rator (← rator ptm))
    pure (qq, ptm, ptms, seq)
    : ExceptT String IO (term × term × List term × term)).run with
  | .error e => pure (.error e)
  | .ok (qq, ptm, ptms, seq) =>
    let mkb (a b : term) : ExceptT String IO term := do
      liftExcept ((← liftExcept (HolCore.Basics.mk_binop seq a)) b)
    let lmkb (l : List term) : ExceptT String IO term :=
      liftExcept (HolCore.Basics.list_mk_binop seq l)
    -- The general CORRECT_SEQ branch (final fallback).
    let generalTac : ExceptT String IO HolCore.Tactics.tactic := do
      let ptm' ← mkb (← lmkb (← liftExcept (HolCore.Lib.butlast ptms)))
                     (← liftExcept (HolCore.Lib.last ptms))
      let rptm' ← liftExcept (rand ptm')
      let pwp ← ExceptT.mk (find_pwp rptm' qq)
      pure (vcSeq_ADJUST_TAC ptm ptm' THEN MATCH_MP_TAC CORRECT_SEQ THEN
        EXISTS_TAC pwp THEN CONJ_TAC)
    let runGeneral : IO (Except String HolCore.Tactics.goalstate) := do
      match ← generalTac.run with
      | .ok tac => tac (asl, w)
      | .error e => pure (.error e)
    -- `try ... with Failure "find" -> ...` : the assert block.
    match HolCore.Lib.find vcSeq_is_assert ptms with
    | .ok atm =>
      -- An assert is present: build and APPLY the assert tactic.  Any failure
      -- of construction or application propagates (HOL Light only catches the
      -- "find" failure at this level, not these), so we do NOT fall back.
      match ← (do
        let i ← liftExcept (HolCore.Lib.index atm ptms)
        if i == 0 then
          let ptm' ← mkb ptms.head! (← lmkb ptms.tail!)
          pure (vcSeq_ADJUST_TAC ptm ptm' THEN
            MATCH_MP_TAC VC_SEQ_ASSERT_LEFT THEN CONJ_TAC THENL
              [VC_UNPACK_TAC, Session.ALL_TAC])
        else if i == ptms.length - 1 then
          let ptm' ← mkb (← lmkb (← liftExcept (HolCore.Lib.butlast ptms)))
                         (← liftExcept (HolCore.Lib.last ptms))
          pure (vcSeq_ADJUST_TAC ptm ptm' THEN
            MATCH_MP_TAC VC_SEQ_ASSERT_RIGHT THEN CONJ_TAC THENL
              [Session.ALL_TAC, VC_UNPACK_TAC])
        else
          let (l, mr) ← liftExcept (HolCore.Lib.chop_list i ptms)
          let ptm' ← mkb (← lmkb l) (← mkb mr.head! (← lmkb mr.tail!))
          pure (vcSeq_ADJUST_TAC ptm ptm' THEN
            MATCH_MP_TAC VC_SEQ_ASSERT_MIDDLE THEN CONJ_TAC)
        : ExceptT String IO HolCore.Tactics.tactic).run with
      | .ok tac => tac (asl, w)
      | .error e => pure (.error e)
    | .error _ =>
      -- `with Failure "find" -> try ... with Failure _ -> <general>`.
      -- The assign-left block: build and APPLY it; on ANY failure fall back
      -- to the general CORRECT_SEQ branch (exactly as HOL Light's try/with).
      let assignResult : Except String HolCore.Tactics.goalstate ← (do
        if vcSeq_is_assign ptms.head! then
          match ← (do
            let ptm' ← mkb ptms.head! (← lmkb ptms.tail!)
            pure (vcSeq_ADJUST_TAC ptm ptm' THEN
              MATCH_MP_TAC VC_SEQ_ASSIGN_LEFT THEN REPEAT CONJ_TAC THENL
                [vcSeq_SIDE_TAC, vcSeq_SIDE_TAC, Session.ALL_TAC])
            : ExceptT String IO HolCore.Tactics.tactic).run with
          | .ok tac => tac (asl, w)
          | .error e => pure (.error e)
        else pure (.error "fail"))
      match assignResult with
      | .ok gs => pure (.ok gs)
      | .error _ => runGeneral
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- Tactic to apply a 1-step VC generation.                                   --
-- ------------------------------------------------------------------------- --

#eval phrase 93
-- let VC_STEP_TAC = ... (a term-keyed net of tactics; lookup = those whose
-- key matches the goal, tried by FIRST)
unsafe def vc_step_pats : List term := keep "vc_step_pats" fun _ =>
  match unsafeIO ((do
    pure [(← q r"correct p SKIP q"), (← q r"correct p (ASSERT b) q"),
      (← q r"correct p (Assign f) q"), (← q r"correct p (Ite e c1 c2) q"),
      (← q r"correct p (IF e c) q"), (← q r"correct p (AWHILE i (MEASURE m) e c) q"),
      (← q r"correct p (AWHILE i v e c) q"), (← q r"correct p (ADO i (MEASURE m) c e) q"),
      (← q r"correct p (ADO i v c e) q"), (← q r"correct p (c1 Seq c2) q")]
    : ExceptT String IO (List term)).run) with
  | .ok (.ok l) => l
  | .ok (.error e) => panic! e
  | .error e => panic! (toString e)
unsafe def VC_STEP_TAC : HolCore.Tactics.tactic := fun (asl, w) => do
  let tacs : List HolCore.Tactics.tactic :=
    [MATCH_MP_TAC VC_SKIP THEN VC_UNPACK_TAC,
     MATCH_MP_TAC VC_ASSERT THEN VC_UNPACK_TAC,
     MATCH_MP_TAC VC_ASSIGN THEN VC_UNPACK_TAC,
     MATCH_MP_TAC VC_ITE THEN CONJ_TAC,
     MATCH_MP_TAC VC_IF THEN CONJ_TAC THENL [Session.ALL_TAC, VC_UNPACK_TAC],
     MATCH_MP_TAC VC_AWHILE_MEASURE THEN REPEAT CONJ_TAC THENL
       [VC_UNPACK_TAC, VC_UNPACK_TAC, GEN_TAC],
     MATCH_MP_TAC VC_AWHILE_VARIANT THEN REPEAT CONJ_TAC THENL
       [Session.ALL_TAC, VC_UNPACK_TAC, VC_UNPACK_TAC, STATE_GEN_TAC'],
     MATCH_MP_TAC VC_ADO_MEASURE THEN REPEAT CONJ_TAC THENL
       [VC_UNPACK_TAC, VC_UNPACK_TAC, STATE_GEN_TAC'],
     MATCH_MP_TAC VC_ADO_VARIANT THEN REPEAT CONJ_TAC THENL
       [Session.ALL_TAC, VC_UNPACK_TAC, VC_UNPACK_TAC, STATE_GEN_TAC'],
     VC_SEQ_TAC]
  let entries := vc_step_pats.zip tacs
  match ← (do
    let cand ← (entries.filterMapM (fun (pat, tac) => do
      match ← Session.term_match [] pat w with
      | .ok _ => pure (some tac)
      | .error _ => pure none) : IO (List HolCore.Tactics.tactic))
    pure (FIRST cand : HolCore.Tactics.tactic)
    : ExceptT String IO HolCore.Tactics.tactic).run with
  | .ok tac => tac (asl, w)
  | .error e => pure (.error e)
#eval (IO.println (if vc_step_pats.length == 999999 then "" else "<fun>") : IO Unit)

-- ------------------------------------------------------------------------- --
-- Final packaging to strip away the program completely.                     --
-- ------------------------------------------------------------------------- --

#eval phrase 94
-- let VC_TAC = REPEAT VC_STEP_TAC;;
unsafe def VC_TAC : HolCore.Tactics.tactic := REPEAT VC_STEP_TAC
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- Some examples.                                                            --
-- ------------------------------------------------------------------------- --

#eval phrase 95
#eval (install_parser ("correct", parse_program_assertion) : IO Unit)

#eval phrase 96
unsafe def EXAMPLE_FACTORIAL : thm := keep "EXAMPLE_FACTORIAL" fun _ => (do
  let g ← q r"correct
   T
     var x,y,n;
       x := 0;
       y := 1;
       while x < n do [invariant x <= n /\ (y = FACT x); measure n - x]
        (x := x + 1;
         y := y * x)
     end
   y = FACT n"
  prove g
    (VC_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC [FACT, LE_0],
      REWRITE_TAC [CONJ_ASSOC, NOT_LT, LE_ANTISYM] THEN MESON_TAC [],
      REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM ADD1)), FACT] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [MULT_AC] THEN UNDISCH_TAC (← q r"x < n") THEN ARITH_TAC])
  : ExceptT String IO thm).run
#eval EXAMPLE_FACTORIAL

#eval phrase 97
#eval (delete_parser "correct" : IO Unit)

end HolExamples.Prog
