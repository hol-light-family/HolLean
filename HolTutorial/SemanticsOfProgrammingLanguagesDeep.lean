/- File: HolTutorial/SemanticsOfProgrammingLanguagesDeep.lean
Translation of HOL Light's Tutorial/Semantics_of_programming_languages_deep.ml,
phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolTutorial.Common
open HolCore.Kernel Session HolLight.Syntax HolTutorial
namespace HolTutorial.SemanticsOfProgrammingLanguagesDeep

/-- Run an `IO (Except String α)` once, caching its value under `name` (as
    OCaml's `let x,... = e;;` evaluates `e` once).  Used for the toplevel
    `let` bindings whose right-hand side returns a pair/triple, for which there
    is no `thm` coercion. -/
unsafe def keepIO {α : Type} [Inhabited α] (name : String) (f : Unit → IO (Except String α)) : α :=
  keep name fun _ =>
    match unsafeIO (f ()) with
    | .ok (.ok v) => v
    | .ok (.error e) => panic! s!"keepIO {name}: {e}"
    | .error e => panic! s!"keepIO {name}: {e}"

#eval phrase 1
-- let string_INDUCT,string_RECURSION = define_type "string = String (int list)";;
unsafe def string_defs : thm × thm :=
  keepIO "string_defs" fun _ => define_type "string = String (int list)"
unsafe def string_INDUCT : thm := string_defs.1
unsafe def string_RECURSION : thm := string_defs.2
#eval do IO.println (repr string_INDUCT); IO.println (repr string_RECURSION)

#eval phrase 2
-- let expression_INDUCT,expression_RECURSION = define_type
-- "expression = Literal num
--             | Variable string
--             | Plus expression expression
--             | Times expression expression";;
unsafe def expression_defs : thm × thm :=
  keepIO "expression_defs" fun _ => define_type
    "expression = Literal num
              | Variable string
              | Plus expression expression
              | Times expression expression"
unsafe def expression_INDUCT : thm := expression_defs.1
unsafe def expression_RECURSION : thm := expression_defs.2
#eval do IO.println (repr expression_INDUCT); IO.println (repr expression_RECURSION)

#eval phrase 3
-- let command_INDUCT,command_RECURSION = define_type
--   "command = Assign string expression
--            | Sequence command command
--            | If expression command command
--            | While expression command";;
unsafe def command_defs : thm × thm :=
  keepIO "command_defs" fun _ => define_type
    "command = Assign string expression
             | Sequence command command
             | If expression command command
             | While expression command"
unsafe def command_INDUCT : thm := command_defs.1
unsafe def command_RECURSION : thm := command_defs.2
#eval do IO.println (repr command_INDUCT); IO.println (repr command_RECURSION)

#eval phrase 4
-- parse_as_infix(";;",(18,"right"));;
#eval (parse_as_infix (";;", (18, "right")) : IO Unit)

#eval phrase 5
-- parse_as_infix(":=",(20,"right"));;
#eval (parse_as_infix (":=", (20, "right")) : IO Unit)

#eval phrase 6
-- override_interface(";;",`Sequence`);;
#eval (do discard <| override_interface ";;" [[Sequence]] : IO Unit)

#eval phrase 7
-- override_interface(":=",`Assign`);;
#eval (do discard <| override_interface ":=" [[Assign]] : IO Unit)

#eval phrase 8
-- overload_interface("+",`Plus`);;
#eval (do discard <| overload_interface "+" [[Plus]] : IO Unit)

#eval phrase 9
-- overload_interface("*",`Times`);;
#eval (do discard <| overload_interface "*" [[Times]] : IO Unit)

#eval phrase 10
-- let value = define
--  `(value (Literal n) s = n) /\ ...`;;
unsafe def value : thm := keep "value" fun _ => define
  [[(value (Literal n) s = n) /\
    (value (Variable x) s = s(x)) /\
    (value (e1 + e2) s = value e1 s + value e2 s) /\
    (value (e1 * e2) s = value e1 s * value e2 s)]]
#eval value

#eval phrase 11
-- let sem_RULES,sem_INDUCT,sem_CASES = new_inductive_definition `...`;;
unsafe def sem_defs : thm × thm × thm :=
  keepIO "sem_defs" fun _ => new_inductive_definition
  [[(!x e s s'. s'(x) = value e s /\ (!y. ~(y = x) ==> s'(y) = s(y))
               ==> sem (x := e) s s') /\
   (!c1 c2 s s' s''. sem(c1) s s' /\ sem(c2) s' s'' ==> sem(c1 ;; c2) s s'') /\
   (!e c1 c2 s s'. ~(value e s = 0) /\ sem(c1) s s' ==> sem(If e c1 c2) s s') /\
   (!e c1 c2 s s'. value e s = 0 /\ sem(c2) s s' ==> sem(If e c1 c2) s s') /\
   (!e c s. value e s = 0 ==> sem(While e c) s s) /\
   (!e c s s' s''. ~(value e s = 0) /\ sem(c) s s' /\ sem(While e c) s' s''
                   ==> sem(While e c) s s'')]]
unsafe def sem_RULES : thm := sem_defs.1
unsafe def sem_INDUCT : thm := sem_defs.2.1
unsafe def sem_CASES : thm := sem_defs.2.2
#eval do IO.println (repr sem_RULES); IO.println (repr sem_INDUCT); IO.println (repr sem_CASES)

#eval phrase 12
-- (**** Fails
--   define
--    `sem(While e c) s s' <=> if value e s = 0 then (s' = s)
--                             else ?s''. sem c s s'' /\ sem(While e c) s'' s'`;;
-- ****)
-- let DETERMINISM = prove ...
unsafe def DETERMINISM : thm := keep "DETERMINISM" fun _ => prove
 ([[!c s s' s''. sem c s s' /\ sem c s s'' ==> (s' = s'')]])
  (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC sem_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC [sem_CASES] THEN
  REWRITE_TAC [distinctness "command", injectivity "command"] THEN
  REWRITE_TAC [FUN_EQ_THM] THEN ASM_MESON_TAC [])
#eval DETERMINISM

#eval phrase 13
-- let wlp = new_definition `wlp c q s <=> !s'. sem c s s' ==> q s'`;;
unsafe def wlp : thm := keep "wlp" fun _ => new_definition
  [[wlp c q s <=> !s'. sem c s s' ==> q s']]
#eval wlp

#eval phrase 14
-- let terminates = new_definition `terminates c s <=> ?s'. sem c s s'`;;
unsafe def terminates : thm := keep "terminates" fun _ => new_definition
  [[terminates c s <=> ?s'. sem c s s']]
#eval terminates

#eval phrase 15
-- let wp = new_definition `wp c q s <=> terminates c s /\ wlp c q s`;;
unsafe def wp : thm := keep "wp" fun _ => new_definition
  [[wp c q s <=> terminates c s /\ wlp c q s]]
#eval wp

#eval phrase 16
-- let WP_TOTAL = prove (`!c. (wp c EMPTY = EMPTY)`, ...);;
unsafe def WP_TOTAL : thm := keep "WP_TOTAL" fun _ => prove
 ([[!c. (wp c EMPTY = EMPTY)]])
  (REWRITE_TAC [FUN_EQ_THM, wp, wlp, terminates, EMPTY] THEN MESON_TAC [])
#eval WP_TOTAL

#eval phrase 17
-- let WP_MONOTONIC = prove (`q SUBSET r ==> wp c q SUBSET wp c r`, ...);;
unsafe def WP_MONOTONIC : thm := keep "WP_MONOTONIC" fun _ => prove
 ([[q SUBSET r ==> wp c q SUBSET wp c r]])
  (REWRITE_TAC [SUBSET, IN, wp, wlp, terminates] THEN MESON_TAC [])
#eval WP_MONOTONIC

#eval phrase 18
-- let WP_DISJUNCTIVE = prove (`(wp c p) UNION (wp c q) = wp c (p UNION q)`, ...);;
unsafe def WP_DISJUNCTIVE : thm := keep "WP_DISJUNCTIVE" fun _ => prove
 ([[(wp c p) UNION (wp c q) = wp c (p UNION q)]])
  (REWRITE_TAC [FUN_EQ_THM, IN, wp, wlp, IN_ELIM_THM, UNION, terminates] THEN
  MESON_TAC [DETERMINISM])
#eval WP_DISJUNCTIVE

#eval phrase 19
-- let WP_SEQ = prove (`!c1 c2 q. wp (c1 ;; c2) = wp c1 o wp c2`, ...);;
unsafe def WP_SEQ : thm := keep "WP_SEQ" fun _ => prove
 ([[!c1 c2 q. wp (c1 ;; c2) = wp c1 o wp c2]])
  (REWRITE_TAC [wp, wlp, terminates, FUN_EQ_THM, o_THM] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (fun c => HolLight.LAND_CONV (HolLight.ONCE_DEPTH_CONV c)) [sem_CASES] THEN
  REWRITE_TAC [injectivity "command", distinctness "command"] THEN
  MESON_TAC [DETERMINISM])
#eval WP_SEQ

#eval phrase 20
-- let correct = new_definition `correct p c q <=> p SUBSET (wp c q)`;;
unsafe def correct : thm := keep "correct" fun _ => new_definition
  [[correct p c q <=> p SUBSET (wp c q)]]
#eval correct

#eval phrase 21
-- let CORRECT_PRESTRENGTH = prove (`!p p' c q. ...`, ...);;
unsafe def CORRECT_PRESTRENGTH : thm := keep "CORRECT_PRESTRENGTH" fun _ => prove
 ([[!p p' c q. p SUBSET p' /\ correct p' c q ==> correct p c q]])
  (REWRITE_TAC [correct, SUBSET_TRANS])
#eval CORRECT_PRESTRENGTH

#eval phrase 22
-- let CORRECT_POSTWEAK = prove (`!p c q q'. ...`, ...);;
unsafe def CORRECT_POSTWEAK : thm := keep "CORRECT_POSTWEAK" fun _ => prove
 ([[!p c q q'. correct p c q' /\ q' SUBSET q ==> correct p c q]])
  (REWRITE_TAC [correct] THEN MESON_TAC [WP_MONOTONIC, SUBSET_TRANS])
#eval CORRECT_POSTWEAK

#eval phrase 23
-- let CORRECT_SEQ = prove (`!p q r c1 c2. ...`, ...);;
unsafe def CORRECT_SEQ : thm := keep "CORRECT_SEQ" fun _ => prove
 ([[!p q r c1 c2.
        correct p c1 r /\ correct r c2 q ==> correct p (c1 ;; c2) q]])
  (REWRITE_TAC [correct, WP_SEQ, o_THM] THEN
  MESON_TAC [WP_MONOTONIC, SUBSET_TRANS])
#eval CORRECT_SEQ

end HolTutorial.SemanticsOfProgrammingLanguagesDeep
