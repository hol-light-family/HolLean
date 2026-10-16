/- File: HolTutorial/ChangingProofStyle.lean
Translation of HOL Light's Tutorial/Changing_proof_style.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolTutorial.Common
open HolCore.Kernel HolCore.Tactics Session HolLight.Syntax HolTutorial

namespace HolTutorial.ChangingProofStyle

-- let fix ts = MAP_EVERY X_GEN_TAC ts;;
#eval phrase 1
unsafe def fix (ts : List term) : tactic := MAP_EVERY X_GEN_TAC ts
#eval IO.println "<fun>"

-- let assume lab t =
--   DISCH_THEN(fun th -> if concl th = t then LABEL_TAC lab th
--                        else failwith "assume");;
#eval phrase 2
unsafe def assume (lab : String) (t : term) : tactic :=
  DISCH_THEN (fun th => if concl th = t then LABEL_TAC lab th
                        else (fun _ => pure (.error "assume")))
#eval IO.println "<fun>"

-- let we're finished tac = tac;;
#eval phrase 3
unsafe def «we're» {α : Type} (_finished : α) (tac : tactic) : tactic := tac
#eval IO.println "<fun>"

-- let suffices_to_prove q tac = SUBGOAL_THEN q (fun th -> MP_TAC th THEN tac);;
#eval phrase 4
unsafe def suffices_to_prove (q : term) (tac : tactic) : tactic :=
  SUBGOAL_THEN q (fun th => MP_TAC th THEN tac)
#eval IO.println "<fun>"

-- let note(lab,t) tac =
--   SUBGOAL_THEN t MP_TAC THENL [tac; ALL_TAC] THEN
--   DISCH_THEN(fun th -> LABEL_TAC lab th);;
#eval phrase 5
unsafe def note (lt : String × term) (tac : tactic) : tactic :=
  SUBGOAL_THEN lt.2 MP_TAC THENL [tac, ALL_TAC] THEN
  DISCH_THEN (fun th => LABEL_TAC lt.1 th)
#eval IO.println "<fun>"

-- let have t = note("",t);;
#eval phrase 6
unsafe def «have» (t : term) : tactic → tactic := note ("", t)
#eval IO.println "<fun>"

-- let cases (lab,t) tac =
--   SUBGOAL_THEN t MP_TAC THENL [tac; ALL_TAC] THEN
--   DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (LABEL_TAC lab));;
#eval phrase 7
unsafe def «cases» (lt : String × term) (tac : tactic) : tactic :=
  SUBGOAL_THEN lt.2 MP_TAC THENL [tac, ALL_TAC] THEN
  DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN (LABEL_TAC lt.1))
#eval IO.println "<fun>"

-- let consider (x,lab,t) tac =
--   let tm = mk_exists(x,t) in
--   SUBGOAL_THEN tm (X_CHOOSE_THEN x (LABEL_TAC lab)) THENL [tac; ALL_TAC];;
#eval phrase 8
unsafe def consider (xlt : term × String × term) (tac : tactic) : tactic :=
  let tm : term := match HolCore.Bool.mk_exists xlt.1 xlt.2.2 with
    | .ok t => t | .error e => panic! e
  SUBGOAL_THEN tm (X_CHOOSE_THEN xlt.1 (LABEL_TAC xlt.2.1)) THENL [tac, ALL_TAC]
#eval IO.println "<fun>"

-- let trivial = MESON_TAC[];;
#eval phrase 9
unsafe def trivial : tactic := MESON_TAC []
#eval IO.println "<fun>"

-- let algebra = CONV_TAC NUM_RING;;
#eval phrase 10
unsafe def algebra : tactic := CONV_TAC NUM_RING
#eval IO.println "<fun>"

-- let arithmetic = ARITH_TAC;;
#eval phrase 11
unsafe def arithmetic : tactic := ARITH_TAC
#eval IO.println "<fun>"

-- let by labs tac = MAP_EVERY (fun l -> USE_THEN l MP_TAC) labs THEN tac;;
#eval phrase 12
unsafe def «by» (labs : List String) (tac : tactic) : tactic :=
  MAP_EVERY (fun l => USE_THEN l MP_TAC) labs THEN tac
#eval IO.println "<fun>"

-- let using ths tac = MAP_EVERY MP_TAC ths THEN tac;;
#eval phrase 13
unsafe def «using» (ths : List thm) (tac : tactic) : tactic :=
  MAP_EVERY MP_TAC ths THEN tac
#eval IO.println "<fun>"

-- let so constr arg tac = constr arg (FIRST_ASSUM MP_TAC THEN tac);;
#eval phrase 14
unsafe def so {α β : Type} (constr : α → tactic → β) (arg : α) (tac : tactic) : β :=
  constr arg (FIRST_ASSUM MP_TAC THEN tac)
#eval IO.println "<fun>"

-- A dummy value for the ignored `finished` argument of `we're`, as HOL Light's
-- `so we're finished (...)` passes `finished` to `we're`, which discards it.
private def finished : Unit := ()

-- let NSQRT_2 = prove(...) (print-only)
#eval phrase 15
#eval prove ([[!p q. p * p = 2 * q * q ==> q = 0]])
  (suffices_to_prove
    ([[!p. (!m. m < p ==> (!q. m * m = 2 * q * q ==> q = 0))
          ==> (!q. p * p = 2 * q * q ==> q = 0)]])
    (MATCH_ACCEPT_TAC num_WF) THEN
   fix [([[p:num]])] THEN
   assume "A" [[!m. m < p ==> !q. m * m = 2 * q * q ==> q = 0]] THEN
   fix [([[q:num]])] THEN
   assume "B" [[p * p = 2 * q * q]] THEN
   so «have» ([[EVEN(p * p) <=> EVEN(2 * q * q)]]) trivial THEN
   so «have» ([[EVEN(p)]]) («using» [ARITH, EVEN_MULT] trivial) THEN
   so consider ([[m:num]], "C", [[p = 2 * m]]) («using» [EVEN_EXISTS] trivial) THEN
   «cases» ("D", [[q < p \/ p <= q]]) arithmetic THENL
    [so «have» ([[q * q = 2 * m * m ==> m = 0]]) («by» ["A"] trivial) THEN
     so «we're» finished («by» ["B", "C"] algebra),

     so «have» ([[p * p <= q * q]]) («using» [LE_MULT2] trivial) THEN
     so «have» ([[q * q = 0]]) («by» ["B"] arithmetic) THEN
     so «we're» finished algebra])

end HolTutorial.ChangingProofStyle
