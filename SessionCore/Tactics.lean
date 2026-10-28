/- File: SessionCore/Tactics.lean
tactics.ml: the tactics and tacticals as top-level names, and the
subgoal package (`g`, `e`, `b`, `r`, `p`, ...) over the current goalstack
(`currentGoalstack`).
-/
import SessionCore.Drule
import HolCore.Tactics

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Itab HolCore.Simp HolCore.Theorems HolCore.Classic
open HolCore.Trivia HolCore.Printer

namespace Session

/- Tactics. The core machinery and B-parameterized tactics are closed over `B`
   (and `FALSITY_DEF` where needed); pure combinators are re-exported. -/
def mk_fthm (asl : List term) (c : term) := Tactics.mk_fthm B FALSITY_DEF asl c
def VALID := Tactics.VALID B FALSITY_DEF
def inst_goal := Tactics.inst_goal B
def THEN := Tactics.THEN B
def THENL := Tactics.THENL B
/-- `then1_` (tactics.ml 164): `THEN` that fails unless the first tactic
    leaves exactly one subgoal.  What pa_j turns `THEN` into after
    `unset_then_multiple_subgoals`. -/
def then1_ := Tactics.then1_ B
def TRY := Tactics.TRY B
def REPEAT := Tactics.REPEAT B
def EVERY := Tactics.EVERY B
def FIRST := Tactics.FIRST B
def MAP_EVERY {α} := @Tactics.MAP_EVERY α B
def MAP_FIRST {α} := @Tactics.MAP_FIRST α B
def CHANGED_TAC := Tactics.CHANGED_TAC B
def REPLICATE_TAC := Tactics.REPLICATE_TAC B
def LABEL_TAC := Tactics.LABEL_TAC B
def ASSUME_TAC := Tactics.ASSUME_TAC B
def EVERY_ASSUM := Tactics.EVERY_ASSUM B
def RULE_ASSUM_TAC := Tactics.RULE_ASSUM_TAC B
def ACCEPT_TAC := Tactics.ACCEPT_TAC B
def CONV_TAC := Tactics.CONV_TAC B
def REFL_TAC := Tactics.REFL_TAC B
def ABS_TAC := Tactics.ABS_TAC B
def MK_COMB_TAC := Tactics.MK_COMB_TAC B
def AP_TERM_TAC := Tactics.AP_TERM_TAC B
def AP_THM_TAC := Tactics.AP_THM_TAC B
def BINOP_TAC := Tactics.BINOP_TAC B
def SUBST1_TAC := Tactics.SUBST1_TAC B
def SUBST_ALL_TAC := Tactics.SUBST_ALL_TAC B
def BETA_TAC := Tactics.BETA_TAC B
def SUBST_VAR_TAC := Tactics.SUBST_VAR_TAC B
def DISCH_TAC := Tactics.DISCH_TAC B
def MP_TAC := Tactics.MP_TAC B
def EQ_TAC := Tactics.EQ_TAC B
def UNDISCH_TAC := Tactics.UNDISCH_TAC B
def SPEC_TAC := Tactics.SPEC_TAC B
def X_GEN_TAC := Tactics.X_GEN_TAC B
def X_CHOOSE_TAC := Tactics.X_CHOOSE_TAC B
def EXISTS_TAC := Tactics.EXISTS_TAC B
def GEN_TAC := Tactics.GEN_TAC B
def CHOOSE_TAC := Tactics.CHOOSE_TAC B
def CONJ_TAC := Tactics.CONJ_TAC B
def DISJ1_TAC := Tactics.DISJ1_TAC B
def DISJ2_TAC := Tactics.DISJ2_TAC B
def DISJ_CASES_TAC := Tactics.DISJ_CASES_TAC B
def CONTR_TAC := Tactics.CONTR_TAC B
def MATCH_ACCEPT_TAC := Tactics.MATCH_ACCEPT_TAC B
def MATCH_MP_TAC := Tactics.MATCH_MP_TAC B
def TRANS_TAC := Tactics.TRANS_TAC B
def CONJUNCTS_THEN2 := Tactics.CONJUNCTS_THEN2 B
def CONJUNCTS_THEN := Tactics.CONJUNCTS_THEN B
def DISJ_CASES_THEN2 := Tactics.DISJ_CASES_THEN2 B
def DISJ_CASES_THEN := Tactics.DISJ_CASES_THEN B
def DISCH_THEN := Tactics.DISCH_THEN B
def X_CHOOSE_THEN := Tactics.X_CHOOSE_THEN B
def CHOOSE_THEN := Tactics.CHOOSE_THEN B
def STRIP_THM_THEN := Tactics.STRIP_THM_THEN B
def ANTE_RES_THEN := Tactics.ANTE_RES_THEN B
def IMP_RES_THEN := Tactics.IMP_RES_THEN B
def STRIP_ASSUME_TAC := Tactics.STRIP_ASSUME_TAC B
def STRUCT_CASES_THEN := Tactics.STRUCT_CASES_THEN B
def STRUCT_CASES_TAC := Tactics.STRUCT_CASES_TAC B
def STRIP_GOAL_THEN := Tactics.STRIP_GOAL_THEN B
def STRIP_TAC := Tactics.STRIP_TAC B
def UNDISCH_THEN := Tactics.UNDISCH_THEN B
def FIRST_X_ASSUM := Tactics.FIRST_X_ASSUM B
def SUBGOAL_THEN := Tactics.SUBGOAL_THEN B
def SUBGOAL_TAC := Tactics.SUBGOAL_TAC B
def FREEZE_THEN := Tactics.FREEZE_THEN B
def X_META_EXISTS_TAC := Tactics.X_META_EXISTS_TAC B
def META_EXISTS_TAC := Tactics.META_EXISTS_TAC B
def META_SPEC_TAC := Tactics.META_SPEC_TAC B
def CHEAT_TAC := Tactics.CHEAT_TAC B
def ANTS_TAC := Tactics.ANTS_TAC B
def by_ := Tactics.by_ B
def mk_goalstate := Tactics.mk_goalstate B
def TAC_PROOF := Tactics.TAC_PROOF B
def prove := Tactics.prove B
-- no-B combinators / printing:
export Tactics (null_inst null_meta equals_goal compose_insts
  ORELSE FAIL_TAC NO_TAC ALL_TAC THEN_TCL ORELSE_TCL REPEAT_TCL REPEAT_GTCL
  ALL_THEN NO_THEN EVERY_TCL FIRST_TCL FIND_ASSUM POP_ASSUM ASSUM_LIST
  POP_ASSUM_LIST FIRST_ASSUM USE_THEN REMOVE_THEN NAME_ASSUMS_TAC ASM HYP
  rotate pp_print_goal print_goal pp_print_goalstack print_goalstack
  pp_print_colored_goal pp_print_colored_goalstack print_goal_hyp_max_boxes
  PRINT_GOAL_TAC PRINT_COLORED_GOAL_TAC REMARK_TAC)

/-- hol.ml's `#install_printer pp_print_goal`. -/
instance : Repr goal := ⟨fun g _ =>
  runString (HolCore.Printer.print_to_string_io Tactics.pp_print_goal g) "<goal>"⟩

/- ---------------------------------------------------------------------- -/
/- Interactive "subgoal package": mutable current goalstack + commands.   -/
/- ---------------------------------------------------------------------- -/

/-- The mutable interactive goalstack. -/
initialize currentGoalstack : IO.Ref goalstack ← IO.mkRef []

/-- Apply a refinement to the current goalstack, pushing the new state. -/
def refine (r : refinement) : IO goalstack := do
  let l ← currentGoalstack.get
  match l with
  | [] => throw (IO.userError "No current goal")
  | h :: _ =>
    match ← r h with
    | .error e => throw (IO.userError e)
    | .ok res => currentGoalstack.set (res :: l); currentGoalstack.get

/-- Apply a tactic to the head subgoal (`e tac = refine (by (VALID tac))`). -/
def e (tac : tactic) : IO goalstack := refine (Tactics.by_ B (VALID tac))

/-- Rotate the goalstack by `n`. -/
def r (n : Int) : IO goalstack := refine (Tactics.rotate n)

/-- `flush_goalstack()`: keep only the newest goalstate. -/
def flush_goalstack : IO Unit := do
  match ← currentGoalstack.get with
  | h :: _ => currentGoalstack.set [h]
  | [] => throw (IO.userError "hd")

/-- `er tac`: a sequence of `e tac; r n` where n is the number of subgoals
    after `e tac`.  This command is useful when you want to interactively try
    a list of tactics after THENL, e.g., `TAC THENL [ TAC_A; TAC_B; .. ]`:
    `e TAC;; er TAC_A;;` will execute TAC, execute TAC_A, then switch to the
    second subgoal of `e TAC`, which will be the input goalstate of TAC_B. -/
def er (tac : tactic) : IO goalstack := do
  let e_result ← e tac
  let (n_subgoals_to_rotate, n_subgoals) ←
    match ← currentGoalstack.get with
    | (_, gl, _) :: (_, glprev, _) :: _ =>
      let n_subgoals := gl.length
      if n_subgoals == 0 then pure ((0 : Int), 0)
      else pure (((n_subgoals : Int) - glprev.length + 1), n_subgoals)
    | _ => throw (IO.userError "current_goalstack must have at least 2 items after 'e'")
  if n_subgoals_to_rotate == 0 || n_subgoals == 1 then
    HolCore.Lib.remark "(Rotating zero subgoal)\n\n"
    return e_result
  else
    if ← HolCore.Lib.verbose.get then print_goalstack (← currentGoalstack.get)
    HolCore.Lib.remark s!"\n(Rotating {n_subgoals_to_rotate} subgoal{if n_subgoals_to_rotate == 1 then "" else "s"}...)\n\n"
    let new_g ← r n_subgoals_to_rotate
    -- pop the latest subgoal so that one b() can fully roll back the state
    let cur_gs ← currentGoalstack.get
    currentGoalstack.set (cur_gs.head! :: cur_gs.tail.tail)
    return new_g

/-- Set the current goal from assumptions and a conclusion. -/
def set_goal (asl : List term) (w : term) : IO goalstack := do
  let asl' ← asl.mapM (fun t => match ASSUME t with
    | .ok th => pure ("", th)
    | .error e => throw (IO.userError e))
  match mk_goalstate (asl', w) with
  | .error err => throw (IO.userError err)
  | .ok gs => currentGoalstack.set [gs]; currentGoalstack.get

/-- Start a new goal (no assumptions), warning about its free variables. -/
def g (t : term) : IO goalstack := do
  let fvs := HolCore.Lib.sort (fun a b => a < b) ((frees t).map (fun v => (dest_var v).toOption.map Prod.fst |>.getD ""))
  if fvs != [] then
    HolCore.Lib.warn true ("Free variables in goal: " ++ ", ".intercalate fvs)
  set_goal [] t

/-- Back up one step in the goalstack. -/
def b : IO goalstack := do
  let l ← currentGoalstack.get
  if l.length == 1 then throw (IO.userError "Can't back up any more")
  else currentGoalstack.set l.tail; currentGoalstack.get

/-- The current goalstack. -/
def p : IO goalstack := currentGoalstack.get

/-- The current top subgoal (assumptions as theorems, conclusion). -/
def top_realgoal : IO goal := do
  match ← currentGoalstack.get with
  | (_, (gl :: _), _) :: _ => pure gl
  | _ => throw (IO.userError "top_realgoal: no goal")

/-- The current top goal (assumption conclusions, conclusion). -/
def top_goal : IO (List term × term) := do
  let (asl, w) ← top_realgoal
  pure (asl.map (fun p => concl p.2), w)

/-- Extract the proved theorem once all subgoals are closed. -/
def top_thm : IO thm := do
  match ← currentGoalstack.get with
  | (_, [], f) :: _ =>
    match ← f null_inst [] with
    | .ok th => pure th
    | .error e => throw (IO.userError e)
  | _ => throw (IO.userError "top_thm: unsolved goals")


end Session
