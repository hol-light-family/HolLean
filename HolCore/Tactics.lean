/- File: Tactics.lean
System of tactics (slightly different from any traditional LCF method).
Original       John Harrison, University of Cambridge Computer Laboratory
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Original (c) Copyright, Marco Maggesi 2012
Lean4 translation by Chris Walton 2026
-/

import HolCore.Bool
import HolCore.Basics
import HolCore.Fusion
import HolCore.Equal
import HolCore.Drule
import HolCore.Printer
import HolCore.Parser

open HolCore.Kernel HolCore.Basics HolCore.Lib HolCore.Bool HolCore.Equal HolCore.Drule
open HolCore.System (Fmt)

namespace HolCore.Tactics

/- ---------------------------------------------------------------------- -/
/- The common case of trivial instantiations.                             -/
/- ---------------------------------------------------------------------- -/

/-- The empty instantiation. -/
def null_inst : instantiation := ([], [], [])

/-- The empty metavariable/instantiation pair. -/
def null_meta : List term × instantiation := ([], null_inst)

/- ---------------------------------------------------------------------- -/
/- A goal has labelled assumptions, and the hyps are now thms.            -/
/- ---------------------------------------------------------------------- -/

/-- A goal: labelled assumptions (each a theorem) and a conclusion. -/
abbrev goal := List (String × thm) × term

/-- Structural equality of goals (labels equal, assumption thms `equals_thm`,
    conclusions equal). -/
def equals_goal (g1 g2 : goal) : Bool :=
  let (a, w) := g1
  let (a', w') := g2
  forall2 (fun (p : String × thm) (p' : String × thm) =>
    p.1 == p'.1 && equals_thm p.2 p'.2) a a' && w == w'

/- ---------------------------------------------------------------------- -/
/- A justification function for a goalstate [A1 ?- g1; ...; An ?- gn],     -/
/- starting from an initial goal A ?- g, is a function f such that for any -/
/- instantiation @:                                                       -/
/-                                                                        -/
/-   f(@) [A1@ |- g1@; ...; An@ |- gn@] = A@ |- g@                         -/
/- ---------------------------------------------------------------------- -/

/-- A justification maps an instantiation and the proved subgoal theorems to
    a theorem for the original goal. IO-valued (rules may use IO). -/
abbrev justification := instantiation → List thm → IO (Except String thm)

/- ---------------------------------------------------------------------- -/
/- The goalstate stores the subgoals, justification, current instantiation, -/
/- and a list of metavariables.                                           -/
/- ---------------------------------------------------------------------- -/

/-- The goalstate: (metavars, instantiation), subgoals, justification. -/
abbrev goalstate := (List term × instantiation) × List goal × justification

/- ---------------------------------------------------------------------- -/
/- A goalstack is just a list of goalstates. Could go for more...         -/
/- ---------------------------------------------------------------------- -/

/-- A goalstack is a list of goalstates. -/
abbrev goalstack := List goalstate

/- ---------------------------------------------------------------------- -/
/- A refinement, applied to a goalstate [A1 ?- g1; ...; An ?- gn]         -/
/- yields a new goalstate with updated justification function, to         -/
/- give a possibly-more-instantiated version of the initial goal.         -/
/- ---------------------------------------------------------------------- -/

/-- A refinement transforms a goalstate. -/
abbrev refinement := goalstate → IO (Except String goalstate)

/- ---------------------------------------------------------------------- -/
/- A tactic, applied to a goal A ?- g, returns:                           -/
/-                                                                        -/
/-  o A list of new metavariables introduced                              -/
/-  o An instantiation (%)                                                -/
/-  o A list of subgoals                                                  -/
/-  o A justification f such that for any instantiation @ we have         -/
/-    f(@) [A1@  |- g1@; ...; An@ |- gn@] = A(%;@) |- g(%;@)               -/
/- ---------------------------------------------------------------------- -/

/-- A tactic maps a goal to a goalstate. -/
abbrev tactic := goal → IO (Except String goalstate)

/-- A tactic parameterized by a theorem. -/
abbrev thm_tactic := thm → tactic

/-- A theorem-tactical transforms a `thm_tactic`. -/
abbrev thm_tactical := thm_tactic → thm_tactic

/- ---------------------------------------------------------------------- -/
/- HOL Light's `o` for `thm_tactic o rule` - the dominant composition       -/
/- idiom in the tactic scripts (`MP_TAC o SYM`, `SUBST1_TAC o GSYM`,        -/
/- `MATCH_MP_TAC o MATCH_MP th`, ...).                                     -/
/- ---------------------------------------------------------------------- -/
/-
  This shape CANNOT be plain function composition, nor any of `Lib`'s
  `o`/`oM`/`oIO` family.  In OCaml the rule just returns a theorem (or raises),
  so `ttac o rule` is ordinary composition; here the rule is
  `Except`- or `IO (Except ·)`-valued while the RESULT must still be a
  `thm_tactic`, i.e. `thm → goal → IO (...)`.  The rule's failure therefore has
  to be sequenced INSIDE the produced tactic, once the goal is supplied.

  As everywhere in this family, the RIGHT operand runs FIRST: the rule is
  applied to the theorem, then the resulting theorem is handed to the tactic.

  *** PRECEDENCE: `oT`/`oTIO` are `infixl:89`, DELIBERATELY ONE LOOSER than
  `Lib`'s `o`/`oM`/`oEm`/`oIO`/`oIOm` at 90. *** These operators cross the
  boundary out of "rule world" into "tactic world", and nothing can be composed
  onto a `thm_tactic` afterwards, so `oT` must be the OUTERMOST operator of a
  chain.  Binding it looser makes the rule chain to its right group FIRST, so a
  three-stage OCaml chain transcribes with no parentheses at all:

      MP_TAC o ABS `x:A` o SPEC `x:A`        (class.ml)
      MP_TAC oT ABS xA oM SPEC xA           -- = MP_TAC oT (ABS xA oM SPEC xA)

  At equal precedence this would instead have parsed as
  `(MP_TAC oT ABS xA) oM SPEC xA` and failed to typecheck - which it did, before
  the precedence was lowered.
-/

/-- `ttac oT rule`: HOL Light's `thm_tactic o rule` for an `Except`-valued rule
    (`SYM`, `GSYM`, `SPEC t`, `ABS x`, `end_itlist CONJ`, ...).  The rule runs
    FIRST.  The rule's INPUT is generic, so this also covers sources that are not
    a single theorem - e.g. `POP_ASSUM_LIST(MP_TAC o end_itlist CONJ)`, where the
    rule consumes a `List thm`. -/
def compTT {α : Type} (ttac : thm_tactic) (rule : α → Except String thm) :
    α → tactic :=
  fun a g =>
    match rule a with
    | .ok th' => ttac th' g
    | .error e => return .error e
infixl:89 " oT " => compTT

/-- `ttac oTIO rule`: as `oT`, but for an IO-valued rule (`MATCH_MP th`,
    `REWRITE_RULE thl`, ...).  The rule runs FIRST. -/
def compTTIO {α : Type} (ttac : thm_tactic) (rule : α → IO (Except String thm)) :
    α → tactic :=
  fun a g => do
    match ← rule a with
    | .ok th' => ttac th' g
    | .error e => return .error e
infixl:89 " oTIO " => compTTIO

/- ---------------------------------------------------------------------- -/
/- Apply instantiation to a goal.                                         -/
/- ---------------------------------------------------------------------- -/

/-- Apply an instantiation to a goal: `INSTANTIATE_ALL` each assumption and
    `instantiate` the conclusion. Uses the bool rules (`B`). -/
def inst_goal (B : BoolThms) (p : instantiation) (g : goal) : Except String goal := do
  let (thms, w) := g
  let thms' ← thms.mapM (fun (s, th) => do
    let th' ← INSTANTIATE_ALL B p th
    pure (s, th'))
  let w' ← instantiate p w
  return (thms', w')

/- ---------------------------------------------------------------------- -/
/- Perform a sequential composition (left first) of instantiations.       -/
/- ---------------------------------------------------------------------- -/

/-- Sequential composition (left first) of two instantiations. -/
def compose_insts (i1 i2 : instantiation) : Except String instantiation := do
  let (pats1, tmin1, tyin1) := i1
  let (pats2, tmin2, tyin2) := i2
  -- tmin = map (instantiate i2 F_F inst tyin2) tmin1
  let tmin ← tmin1.mapM (fun (t, x) => do
    let t' ← instantiate i2 t
    return (t', inst tyin2 x))
  let tyin := tyin1.map (fun (ty, a) => (type_subst tyin2 ty, a))
  -- tmin' = filter (fun (_,x) => not (can (rev_assoc x) tmin)) tmin2
  let tmin' := tmin2.filter (fun (_, x) => !(can (rev_assoc x) tmin))
  let tyin' := tyin2.filter (fun (_, a) => !(can (rev_assoc a) tyin))
  return (pats1 ++ pats2, tmin ++ tmin', tyin ++ tyin')

/- ---------------------------------------------------------------------- -/
/- Construct A,_FALSITY_ |- p; contortion so falsity is the last element. -/
/- ---------------------------------------------------------------------- -/

/-- Assert a "fake" theorem `A, _FALSITY_ |- c` for validity checking.
    `falsityDef` is the definitional theorem `|- _FALSITY_ = F`; uses the bool
    rules `EQ_IMP_RULE`/`UNDISCH`/`CONTR`/`ADD_ASSUM`/`PROVE_HYP`. -/
def mk_fthm (B : BoolThms) (falsityDef : thm) (asl : List term) (c : term) :
    Except String thm := do
  let false_const ← lhs (concl falsityDef)
  let pth ← B.UNDISCH (← B.EQ_IMP_RULE falsityDef).1        -- _FALSITY_ |- F
  let qth ← ASSUME false_const                              -- _FALSITY_ |- _FALSITY_
  -- itlist ADD_ASSUM (rev asl) (CONTR c pth)
  PROVE_HYP qth (← itlistM B.ADD_ASSUM asl.reverse (← B.CONTR c pth))
/- ---------------------------------------------------------------------- -/
/- Validity checking of tactics. This cannot be 100% accurate without making -/
/- arbitrary theorems, but "mk_fthm" brings us quite close.               -/
/- ---------------------------------------------------------------------- -/

/-- Wrap a tactic so it fails if its justification does not actually produce
    the claimed goal (up to alpha). Uses `mk_fthm` (hence `B`/`falsityDef`). -/
def VALID (B : BoolThms) (falsityDef : thm) (tac : tactic) : tactic := fun g =>
  ExceptT.run do
    let false_tm ← liftExcept (lhs (concl falsityDef))
    let fake_thm (gl : goal) : Except String thm :=
      let (asl, w) := gl
      let asms := itlist (fun (p : String × thm) acc => union (hyp p.2) acc) asl []
      mk_fthm B falsityDef asms w
    let (asl, w) := g
    let res ← (tac g : IO (Except String goalstate))
    let ((_mvs, i), gls, just) := res
    let ths ← liftExcept (gls.mapM fake_thm)
    let jth ← (just null_inst ths : IO (Except String thm))
    let (asl', w') := dest_thm jth
    let (asl'', w'') ← liftExcept (inst_goal B i (asl, w))
    let maxasms :=
      itlist (fun (p : String × thm) acc =>
                union (insert (concl p.2) (hyp p.2)) acc) asl'' []
    if aconv w' w'' &&
       (subtract asl' [false_tm]).all (fun t => maxasms.any (fun a => aconv t a))
    then return res
    else throw "VALID: Invalid tactic"

/- ---------------------------------------------------------------------- -/
/- Various simple combinators for tactics, identity tactic etc.           -/
/- ---------------------------------------------------------------------- -/

/-- A list-valued justification (internal to `seqapply`). -/
abbrev listjust := instantiation → List thm → IO (Except String (List thm))

/-- `propagate_empty`: the empty list-justification. -/
private def propagate_empty : listjust := fun _ _ => return .ok []

/-- `propagate_thm th`: a (single) justification that just instantiates `th`. -/
private def propagate_thm (B : BoolThms) (th : thm) : justification :=
  fun i _ => return (INSTANTIATE_ALL B i th)

/-- `compose_justs n just1 just2 insts2`: prepend the (single) `just1` result on
    the first `n` theorems to the (list) `just2` result on the rest. -/
private def compose_justs (_B : BoolThms) (n : Nat) (just1 : justification)
    (just2 : listjust) (insts2 : instantiation) : listjust := fun i ths => do
  match chop_list n ths with
  | .error e => return .error e
  | .ok (ths1, ths2) =>
    match compose_insts insts2 i with
    | .error e => return .error e
    | .ok ci =>
      match ← (just1 ci ths1 : IO (Except String thm)) with
      | .error e => return .error e
      | .ok h =>
        match ← (just2 i ths2 : IO (Except String (List thm))) with
        | .error e => return .error e
        | .ok t => return .ok (h :: t)

/-- Sequentially apply a list of tactics to a list of goals, threading
    instantiations and composing justifications. -/
private partial def seqapply (B : BoolThms) :
    List tactic → List goal →
    IO (Except String ((List term × instantiation) × List goal × listjust)) :=
  fun l1 l2 => ExceptT.run do
    match l1, l2 with
    | [], [] => return (null_meta, [], propagate_empty)
    | tac :: tacs, goal :: goals => do
        let gstate ← (tac goal : IO (Except String goalstate))
        let ((mvs1, insts1), gls1, just1) := gstate
        let goals' ← liftExcept (goals.mapM (inst_goal B insts1))
        let r ← (seqapply B tacs goals' : IO (Except String _))
        let ((mvs2, insts2), gls2, just2) := r
        let gls1' ← liftExcept (gls1.mapM (inst_goal B insts2))
        let insts' ← liftExcept (compose_insts insts1 insts2)
        return ((union mvs1 mvs2, insts'),
                gls1' ++ gls2,
                compose_justs B gls1.length just1 just2 insts2)
    | _, _ => throw "seqapply: Length mismatch"

/-- `justsequence just1 just2 insts2`: run the list-just `just2`, then feed its
    results to the single-just `just1` under the composed instantiation. -/
private def justsequence (just1 : justification) (just2 : listjust)
    (insts2 : instantiation) : justification := fun i ths => do
  match ← (just2 i ths : IO (Except String (List thm))) with
  | .error e => return .error e
  | .ok ths2 =>
    match compose_insts insts2 i with
    | .error e => return .error e
    | .ok i' => (just1 i' ths2 : IO (Except String thm))

/-- Compose an initial goalstate with a list of tactics run on its subgoals. -/
private def tacsequence (B : BoolThms) (gstate : goalstate) (tacl : List tactic) :
    IO (Except String goalstate) := ExceptT.run do
  let ((mvs1, insts1), gls1, just1) := gstate
  let r ← (seqapply B tacl gls1 : IO (Except String _))
  let ((mvs2, insts2), gls2, just2) := r
  let jst := justsequence just1 just2 insts2
  let just ←
    if gls2 == [] then do
      let th ← (jst null_inst [] : IO (Except String thm))
      pure (propagate_thm B th)
    else pure jst
  let insts' ← liftExcept (compose_insts insts1 insts2)
  return ((union mvs1 mvs2, insts'), gls2, just)

/-- `THEN tac1 tac2`: apply `tac1`, then `tac2` to every resulting subgoal. -/
def THEN (B : BoolThms) (tac1 tac2 : tactic) : tactic := fun g => ExceptT.run do
  let gstate ← (tac1 g : IO (Except String goalstate))
  let (_, gls, _) := gstate
  (tacsequence B gstate (replicate tac2 gls.length) : IO (Except String goalstate))

/-- `THENL tac1 [t1;...;tn]`: apply `tac1`, then `ti` to the `i`-th subgoal. -/
def THENL (B : BoolThms) (tac1 : tactic) (tac2l : List tactic) : tactic :=
  fun g => ExceptT.run do
    let gstate ← (tac1 g : IO (Except String goalstate))
    let (_, gls, _) := gstate
    if gls == [] then (tacsequence B gstate [] : IO (Except String goalstate))
    else (tacsequence B gstate tac2l : IO (Except String goalstate))

/-- `then1_ tac1 tac2 = THENL tac1 [tac2]`. -/
def then1_ (B : BoolThms) (tac1 tac2 : tactic) : tactic := THENL B tac1 [tac2]

/-- `ORELSE tac1 tac2`: try `tac1`; on failure, run `tac2`. -/
def ORELSE (tac1 tac2 : tactic) : tactic := fun g => do
  match ← (tac1 g : IO (Except String goalstate)) with
  | .ok r => return .ok r
  | .error _ => (tac2 g : IO (Except String goalstate))

/-- `FAIL_TAC tok`: always fails with message `tok`. -/
def FAIL_TAC (tok : String) : tactic := fun _ => return .error tok

/-- A tactic that always fails. -/
def NO_TAC : tactic := FAIL_TAC "NO_TAC"

/-- The identity tactic: leaves the goal unchanged. -/
def ALL_TAC : tactic := fun g =>
  return .ok (null_meta, [g], fun _ ths =>
    return (match ths with | [th] => .ok th | _ => failwith "ALL_TAC"))

/-- `TRY tac`: apply `tac`, or do nothing on failure. -/
def TRY (_B : BoolThms) (tac : tactic) : tactic := ORELSE tac ALL_TAC

/-- Repeatedly apply `tac` until it fails. -/
partial def REPEAT (B : BoolThms) (tac : tactic) : tactic := fun g =>
  (ORELSE (THEN B tac (REPEAT B tac)) ALL_TAC) g

/-- Apply a list of tactics in sequence (`THEN`-folded). -/
def EVERY (B : BoolThms) (tacl : List tactic) : tactic :=
  itlist (fun t1 t2 => THEN B t1 t2) tacl ALL_TAC

/-- Try each tactic in turn until one succeeds. -/
def FIRST (_B : BoolThms) (tacl : List tactic) : tactic := fun g =>
  match end_itlist (fun t1 t2 => ORELSE t1 t2) tacl with
  | .ok tac => (tac g : IO (Except String goalstate))
  | .error e => return .error e

/-- Apply `tacf x` for every `x`, in sequence. -/
def MAP_EVERY (B : BoolThms) (tacf : α → tactic) (lst : List α) : tactic :=
  EVERY B (lst.map tacf)

/-- Try `tacf x` for each `x` until one succeeds. -/
def MAP_FIRST (B : BoolThms) (tacf : α → tactic) (lst : List α) : tactic :=
  FIRST B (lst.map tacf)

/-- Fail unless `tac` changes the goal. -/
def CHANGED_TAC (_B : BoolThms) (tac : tactic) : tactic := fun g => do
  match ← (tac g : IO (Except String goalstate)) with
  | .error e => return .error e
  | .ok gstate =>
    let mvi := gstate.1
    let gl := gstate.2.1
    if (mvi.1 == null_meta.1 && mvi.2 == null_meta.2) && gl.length == 1 &&
       equals_goal (gl.headD ([], g.2)) g
    then return .error "CHANGED_TAC" else return .ok gstate

/-- Apply `tac` exactly `n` times. -/
def REPLICATE_TAC (B : BoolThms) (n : Nat) (tac : tactic) : tactic :=
  match n with
  | 0 => ALL_TAC
  | n + 1 => THEN B tac (REPLICATE_TAC B n tac)

/- ---------------------------------------------------------------------- -/
/- Combinators for theorem continuations / "theorem tacticals".           -/
/- ---------------------------------------------------------------------- -/

/-- Sequence two theorem-tacticals. -/
def THEN_TCL (ttcl1 ttcl2 : thm_tactical) : thm_tactical :=
  fun ttac => ttcl1 (ttcl2 ttac)

/-- `ttcl1 ORELSE_TCL ttcl2` (tactics.ml 213-215).

    ACCEPTED ADAPTATION (reviewed 2026-09-25; do not re-report).  OCaml's
    `try ttcl1 ttac th with Failure _ -> ttcl2 ttac th` catches only failures
    raised while BUILDING the tactic: OCaml's thm-tactics (`CONJUNCTS_THEN2`,
    `DISJ_CASES_TAC`, `CHOOSE_TAC`) take the theorem apart as soon as they are
    given it.  Here thm-tactics are `fun gl => ...`, so the fallback also
    catches a failure of the continuation on the goal.  `REPEAT_TCL` and
    `FIRST_TCL` inherit this.  It differs from OCaml only when `ttcl1` accepts
    the theorem but its continuation then fails on the goal; OCaml fails there,
    and this falls back to `ttcl2`.  Kept deliberately: matching OCaml would
    need thm-tactics to separate construction from application. -/
def ORELSE_TCL (ttcl1 ttcl2 : thm_tactical) : thm_tactical :=
  fun ttac th => ORELSE (ttcl1 ttac th) (ttcl2 ttac th)

/-- Identity theorem-tactical. -/
def ALL_THEN : thm_tactical := id

/-- Always-failing theorem-tactical. -/
def NO_THEN : thm_tactical := fun _ttac _th => FAIL_TAC "NO_THEN"

/-- Apply `ttcl` as many times as possible. -/
partial def REPEAT_TCL (ttcl : thm_tactical) : thm_tactical :=
  fun ttac th =>
    (ORELSE_TCL (THEN_TCL ttcl (REPEAT_TCL ttcl)) ALL_THEN) ttac th

/-- `REPEAT_GTCL`: like `REPEAT_TCL` but re-checks against the goal each step. -/
partial def REPEAT_GTCL (ttcl : thm_tactical) : thm_tactical :=
  fun ttac th g => do
    match ← (ttcl (REPEAT_GTCL ttcl ttac) th g : IO (Except String goalstate)) with
    | .ok r => return .ok r
    | .error _ => (ttac th g : IO (Except String goalstate))

/-- Sequence a list of theorem-tacticals. -/
def EVERY_TCL (ttcll : List thm_tactical) : thm_tactical :=
  itlist (fun t1 t2 => THEN_TCL t1 t2) ttcll ALL_THEN

/-- Try each theorem-tactical in turn. -/
def FIRST_TCL (ttcll : List thm_tactical) : thm_tactical := fun ttac th =>
  match end_itlist (fun t1 t2 => ORELSE_TCL t1 t2) ttcll with
  | .ok ttcl => ttcl ttac th
  | .error e => fun _ => return .error e

/- ---------------------------------------------------------------------- -/
/- Tactics to augment assumption list. Note that to allow "ASSUME p" for  -/
/- any assumption "p", these add a PROVE_HYP in the justification function, -/
/- just in case.                                                          -/
/- ---------------------------------------------------------------------- -/

/-- `LABEL_TAC s th`: add `th` to the assumptions under label `s`. -/
def LABEL_TAC (B : BoolThms) (s : String) (thm : thm) : tactic := fun g =>
  let (asl, w) := g
  return .ok (null_meta, [((s, thm) :: asl, w)],
    fun i ths => do
      match ths with
      | [th] => return (do PROVE_HYP (← INSTANTIATE_ALL B i thm) th)
      | _ => return (failwith "LABEL_TAC"))

/-- `ASSUME_TAC` = `LABEL_TAC ""`. -/
def ASSUME_TAC (B : BoolThms) (thm : thm) : tactic := LABEL_TAC B "" thm

/- ---------------------------------------------------------------------- -/
/- Manipulation of assumption list.                                       -/
/- ---------------------------------------------------------------------- -/

/-- Apply `ttac` to the assumption whose conclusion is `t`. -/
def FIND_ASSUM (ttac : thm_tactic) (t : term) : tactic := fun g =>
  let (asl, _) := g
  match find (fun (p : String × thm) => concl p.2 == t) asl with
  | .ok p => ttac p.2 g
  | .error e => return .error e

/-- Apply `ttac` to the most recent assumption, removing it. -/
def POP_ASSUM (ttac : thm_tactic) : tactic := fun g =>
  match g with
  | ((_, th) :: asl, w) => ttac th (asl, w)
  | _ => return .error "POP_ASSUM: No assumption to pop"

/-- Apply `aslfun` to the list of assumption theorems (goal unchanged). -/
def ASSUM_LIST (aslfun : List thm → tactic) : tactic := fun g =>
  let (asl, w) := g
  aslfun (asl.map Prod.snd) (asl, w)

/-- Apply `asltac` to the assumption theorems, with an empty assumption list. -/
def POP_ASSUM_LIST (asltac : List thm → tactic) : tactic := fun g =>
  let (asl, w) := g
  asltac (asl.map Prod.snd) ([], w)

/-- Apply `ttac` to every assumption, in order. -/
def EVERY_ASSUM (B : BoolThms) (ttac : thm_tactic) : tactic :=
  ASSUM_LIST (MAP_EVERY B ttac)

/-- Try `ttac` on each assumption until one succeeds (IO `tryfind`). -/
def FIRST_ASSUM (ttac : thm_tactic) : tactic := fun g =>
  let (asl, _) := g
  tryfindM (fun (p : String × thm) => ttac p.2 g) asl

/-- Apply a rule (possibly IO-valued) to every assumption. -/
def RULE_ASSUM_TAC (B : BoolThms) (rule : thm → IO (Except String thm)) : tactic := fun g =>
  let (asl, _) := g
  (THEN B (POP_ASSUM_LIST (fun _ => ALL_TAC))
          (MAP_EVERY B (fun (p : String × thm) => fun g' => do
                          match ← (rule p.2 : IO (Except String thm)) with
                          | .ok r => LABEL_TAC B p.1 r g'
                          | .error e => return .error e)
                       asl.reverse)) g

/- ---------------------------------------------------------------------- -/
/- Operate on assumption identified by a label.                           -/
/- ---------------------------------------------------------------------- -/

/-- Apply `ttac` to the assumption labelled `s` (kept in place). -/
def USE_THEN (s : String) (ttac : thm_tactic) : tactic := fun g =>
  let (asl, _) := g
  match assoc s asl with
  | .error _ => return .error s!"USE_TAC: didn't find assumption {s}"
  | .ok th => ttac th g

/-- Apply `ttac` to the assumption labelled `s`, removing it. -/
def REMOVE_THEN (s : String) (ttac : thm_tactic) : tactic := fun g =>
  let (asl, w) := g
  match assoc s asl with
  | .error _ => return .error s!"USE_TAC: didn't find assumption {s}"
  | .ok th =>
    match index s (asl.map Prod.fst) with
    | .error e => return .error e
    | .ok idx =>
      match chop_list idx asl with
      | .error e => return .error e
      | .ok (asl1, asl2) =>
        let asl' := asl1 ++ asl2.tail
        ttac th (asl', w)

/-- Find the next unused `H`-name starting from index `idx`. -/
private partial def nextHypName (used : List String) (idx : Nat) : String :=
  let n := "H" ++ toString idx
  if used.contains n then nextHypName used (idx + 1) else n

/-- Give fresh `H0`, `H1`, … names to unlabeled assumptions. -/
def NAME_ASSUMS_TAC : tactic := fun g =>
  let (asl, w) := g
  let rec relabel (idx : Nat) (used : List String) :
      List (String × thm) → List (String × thm)
    | [] => []
    | (name, a) :: rest =>
        if name == "" then
          let n := nextHypName used idx
          (n, a) :: relabel (idx + 1) (n :: used) rest
        else (name, a) :: relabel idx used rest
  let asl' := relabel 0 (asl.map Prod.fst) asl
  ALL_TAC (asl', w)

/- ---------------------------------------------------------------------- -/
/- General tools to augment a required set of theorems with assumptions.  -/
/- Here ASM uses all current hypotheses of the goal, while HYP uses only   -/
/- those whose labels are given in the string argument.                   -/
/- ---------------------------------------------------------------------- -/

/-- `ASM tltac ths`: run `tltac` with all current assumptions prepended. -/
def ASM (tltac : List thm → tactic) (ths : List thm) : tactic := fun g =>
  let (asl, _) := g
  tltac (asl.map Prod.snd ++ ths) g

/-- `HYP tac s ths` (tactics.ml 321): like `ASM tac` but only for the
    assumptions whose labels appear in `s`, added in front of `ths`.  `s` is
    lexed as a term and must be a sequence of alphanumeric identifiers, else
    "Invalid using pattern". -/
def HYP (tac : List thm → tactic) (s : String) : List thm → tactic := fun ths g => do
  -- HYP_LIST tac l = rev_itlist (fun s k l -> USE_THEN s (fun th -> k (th::l))) l tac
  let hypList (l : List String) : List thm → tactic :=
    rev_itlist (fun (s : String) (k : List thm → tactic) =>
                  fun (l : List thm) => USE_THEN s (fun th => k (th :: l)))
               l tac
  -- `(fix "Using pattern" parse_using o lex o explode) s`, where parse_using =
  -- many ident and `ident = function Ident s::rest when isalnum s -> s,rest`.
  match Parser.lex (← Parser.mkCtx) (explode s) with
  | .error e => return .error (Parser.perrMsg e)
  | .ok toks =>
    let rec idents : List Parser.lexcode → List String × List Parser.lexcode
      | .Ident w :: rest =>
        if Printer.isalnum w then let (l, r) := idents rest; (w :: l, r)
        else ([], .Ident w :: rest)
      | toks => ([], toks)
    let (l, rest) := idents toks
    if rest.isEmpty then hypList l ths g
    else return failwith "Invalid using pattern"

/- ---------------------------------------------------------------------- -/
/- Basic tactic to use a theorem equal to the goal. Does *no* matching.   -/
/- ---------------------------------------------------------------------- -/

/-- Accept a theorem whose conclusion is alpha-equivalent to the goal. -/
def ACCEPT_TAC (B : BoolThms) (th : thm) : tactic := fun g =>
  let (_, w) := g
  if aconv (concl th) w then
    return .ok (null_meta, [], propagate_thm B th)
  else return .error "ACCEPT_TAC"

/- ---------------------------------------------------------------------- -/
/- Create tactic from a conversion. This allows the conversion to return  -/
/- |- p rather than |- p = T on a term "p". It also eliminates any goals of -/
/- the form "T" automatically.                                            -/
/- ---------------------------------------------------------------------- -/

/-- Turn an (IO) conversion into a tactic. The conversion may return `|- p`
    rather than `|- p = T`; goals of the form `T` are eliminated. -/
def CONV_TAC (B : BoolThms) (conv : ioconv) : tactic := fun g => ExceptT.run do
  let (asl, w) := g
  let t_tm := concl B.TRUTH
  let th ← (conv w : IO (Except String thm))
  let tm := concl th
  if aconv tm w then (ACCEPT_TAC B th g : IO (Except String goalstate))
  else
    let (l, r) ← liftExcept (dest_eq tm)
    if !(aconv l w) then throw "CONV_TAC: bad equation"
    else if r == t_tm then
      let eth ← liftExcept (B.EQT_ELIM th)
      (ACCEPT_TAC B eth g : IO (Except String goalstate))
    else do
      let th' ← liftExcept (SYM th)
      return (null_meta, [(asl, r)], fun i ths =>
        return (match ths with
          | [th0] => do EQ_MP (← INSTANTIATE_ALL B i th') th0
          | _ => failwith "CONV_TAC"))

/- ---------------------------------------------------------------------- -/
/- Tactics for equality reasoning.                                        -/
/- ---------------------------------------------------------------------- -/

/-- Prove a reflexive equation `|- t = t`. -/
def REFL_TAC (B : BoolThms) : tactic := fun g => do
  let (_, w) := g
  match rand w with
  | .error _ => return .error "REFL_TAC"
  | .ok r =>
    match ← (ACCEPT_TAC B (REFL r) g : IO (Except String goalstate)) with
    | .ok res => return .ok res
    | .error _ => return .error "REFL_TAC"

/-- Reduce `|- (\x. s) = (\x. t)` to `|- s = t` (with a fresh variable). -/
def ABS_TAC (_B : BoolThms) : tactic := fun g => ExceptT.run do
  let (asl, w) := g
  let (l, r) ← liftExcept (dest_eq w)
  let (lv, lb) ← liftExcept (dest_abs l)
  let (rv, rb) ← liftExcept (dest_abs r)
  let avoids := itlist (fun (p : String × thm) acc => union (thm_frees p.2) acc)
                       asl (frees w)
  let v ← (mk_primed_var avoids lv : IO (Except String term))
  let sub_l ← liftExcept (vsubst [(v, lv)])
  let sub_r ← liftExcept (vsubst [(v, rv)])
  let mkEq ← (mk_eq : IO (Except String ((term × term) → Except String term)))
  let newGoal ← liftExcept (mkEq (sub_l lb, sub_r rb))
  return (null_meta, [(asl, newGoal)], fun i ths =>
    return (match ths with
      | [th] => do
          let ath ← ABS v th
          let iw ← instantiate i w
          EQ_MP (← ALPHA (concl ath) iw) ath
      | _ => failwith "ABS_TAC"))

/-- Reduce `|- f x = g y` to `|- f = g` and `|- x = y`. -/
def MK_COMB_TAC (_B : BoolThms) : tactic := fun g => ExceptT.run do
  let (asl, gl) := g
  let (l, r) ← liftExcept (dest_eq gl)
  let (f, x) ← liftExcept (dest_comb l)
  let (g0, y) ← liftExcept (dest_comb r)
  let mkEq ← (mk_eq : IO (Except String ((term × term) → Except String term)))
  let goal1 ← liftExcept (mkEq (f, g0))
  let goal2 ← liftExcept (mkEq (x, y))
  return (null_meta, [(asl, goal1), (asl, goal2)], fun _ ths =>
    return (match ths with
      | [th1, th2] => MK_COMB th1 th2
      | _ => failwith "MK_COMB_TAC"))

/-- Reduce `|- f x = f y` to `|- x = y`. -/
def AP_TERM_TAC (B : BoolThms) : tactic := fun g => do
  match ← (THENL B (MK_COMB_TAC B) [REFL_TAC B, ALL_TAC] g : IO (Except String goalstate)) with
  | .ok r => return .ok r
  | .error _ => return .error "AP_TERM_TAC"

/-- Reduce `|- f x = g x` to `|- f = g`. -/
def AP_THM_TAC (B : BoolThms) : tactic := fun g => do
  match ← (THENL B (MK_COMB_TAC B) [ALL_TAC, REFL_TAC B] g : IO (Except String goalstate)) with
  | .ok r => return .ok r
  | .error _ => return .error "AP_THM_TAC"

/-- Reduce `|- f a x = f b y` to `|- a = b` and `|- x = y`. -/
def BINOP_TAC (B : BoolThms) : tactic := fun g => do
  match ← (THENL B (MK_COMB_TAC B) [AP_TERM_TAC B, ALL_TAC] g : IO (Except String goalstate)) with
  | .ok r => return .ok r
  | .error _ => return .error "AP_THM_TAC"

/-- Substitute using the equation `th` in the goal. -/
def SUBST1_TAC (B : BoolThms) (th : thm) : tactic := CONV_TAC B (SUBS_CONV [th])

/-- Substitute using `th` in the goal and every assumption. -/
def SUBST_ALL_TAC (B : BoolThms) (rth : thm) : tactic :=
  THEN B (SUBST1_TAC B rth) (RULE_ASSUM_TAC B (fun t => SUBS [rth] t))

/-- Beta-reduce everywhere in the goal. -/
def BETA_TAC (B : BoolThms) : tactic :=
  CONV_TAC B (fun t => return (REDEPTH_CONV BETA_CONV t))

/- ---------------------------------------------------------------------- -/
/- Just use an equation to substitute if possible and uninstantiable.     -/
/- ---------------------------------------------------------------------- -/

/-- Substitute a variable/constant equation into goal and assumptions, if the
    equation is oriented so as to be uninstantiable; else fail. -/
def SUBST_VAR_TAC (B : BoolThms) (th : thm) : tactic := fun g => do
  let handle : Except String (Option (Sum thm thm)) := do
    let (asm, eq) := dest_thm th
    let (l, r) ← dest_eq eq
    if aconv l r then .ok none                          -- ALL_TAC
    else if !(subset (frees eq) (freesl asm)) then failwith "SUBST_VAR_TAC"
    else if (is_const l || is_var l) && !(free_in l r) then .ok (some (.inl th))
    else if (is_const r || is_var r) && !(free_in r l) then
      .ok (some (.inr (← SYM th)))
    else failwith "SUBST_VAR_TAC"
  match handle with
  | .error _ => return .error "SUBST_VAR_TAC"
  | .ok none => (ALL_TAC g : IO (Except String goalstate))
  | .ok (some (.inl t)) => (SUBST_ALL_TAC B t g : IO (Except String goalstate))
  | .ok (some (.inr t)) => (SUBST_ALL_TAC B t g : IO (Except String goalstate))

/- ---------------------------------------------------------------------- -/
/- Basic logical tactics.                                                 -/
/- ---------------------------------------------------------------------- -/

/-- Move the antecedent of an implication (or the body of a negation) into the
    assumptions. -/
def DISCH_TAC (B : BoolThms) : tactic := fun g => ExceptT.run do
  let (asl, w) := g
  match Basics.dest_imp w with
  | .ok (ant, c) =>
      let th1 ← liftExcept (ASSUME ant)
      return (null_meta, [(("", th1) :: asl, c)], fun i ths =>
        return (match ths with
          | [th] => do B.DISCH (← instantiate i ant) th
          | _ => failwith "DISCH_TAC"))
  | .error _ =>
    match dest_neg w with
    | .ok ant =>
        let th1 ← liftExcept (ASSUME ant)
        let f_tm : term := .Const "F" bool_ty
        return (null_meta, [(("", th1) :: asl, f_tm)], fun i ths =>
          return (match ths with
            | [th] => do B.NOT_INTRO (← B.DISCH (← instantiate i ant) th)
            | _ => failwith "DISCH_TAC"))
    | .error _ => throw "DISCH_TAC"

/-- Add `|- concl thm` as a new antecedent of the goal. -/
def MP_TAC (B : BoolThms) (thm : thm) : tactic := fun g => ExceptT.run do
  let (asl, w) := g
  let newGoal ← liftExcept (mk_imp (concl thm) w)
  return (null_meta, [(asl, newGoal)], fun i ths =>
    return (match ths with
      | [th] => do B.MP th (← INSTANTIATE_ALL B i thm)
      | _ => failwith "MP_TAC"))

/-- Split `|- l = r` into `|- l ==> r` and `|- r ==> l`. -/
def EQ_TAC (B : BoolThms) : tactic := fun g => ExceptT.run do
  let (asl, w) := g
  let (l, r) ← liftExcept (dest_eq w)
  let g1 ← liftExcept (mk_imp l r)
  let g2 ← liftExcept (mk_imp r l)
  return (null_meta, [(asl, g1), (asl, g2)], fun _ ths =>
    return (match ths with
      | [th1, th2] => B.IMP_ANTISYM_RULE th1 th2
      | _ => failwith "EQ_TAC"))

/-- Undischarge the assumption alpha-equal to `tm`, making it an antecedent. -/
def UNDISCH_TAC (B : BoolThms) (tm : term) : tactic := fun g => ExceptT.run do
  let (asl, w) := g
  match remove (fun (p : String × thm) => aconv (concl p.2) tm) asl with
  | .error _ => throw "UNDISCH_TAC"
  | .ok (sthm, asl') =>
      let newGoal ← liftExcept (mk_imp tm w)
      return (null_meta, [(asl', newGoal)], fun i ths =>
        return (match ths with
          | [th] => do B.MP th (← INSTANTIATE_ALL B i sthm.2)
          | _ => failwith "UNDISCH_TAC"))

/-- Generalize the goal by abstracting `t` as the bound variable `x`. -/
def SPEC_TAC (B : BoolThms) (p : term × term) : tactic := fun g => ExceptT.run do
  let (t, x) := p
  let (asl, w) := g
  let substFn ← (subst [(x, t)] : IO (Except String (term → IO (Except String term))))
  let wsub ← (substFn w : IO (Except String term))
  let newGoal ← liftExcept (mk_forall x wsub)
  return (null_meta, [(asl, newGoal)], fun i ths =>
    return (match ths with
      | [th] => do B.SPEC (← instantiate i t) th
      | _ => failwith "SPEC_TAC"))

/-- Split a conjunctive goal `|- l /\ r` into `|- l` and `|- r`. -/
def CONJ_TAC (B : BoolThms) : tactic := fun g => ExceptT.run do
  let (asl, w) := g
  let (l, r) ← liftExcept (Basics.dest_conj w)
  return (null_meta, [(asl, l), (asl, r)], fun _ ths =>
    return (match ths with
      | [th1, th2] => B.CONJ th1 th2
      | _ => failwith "CONJ_TAC"))

/-- Reduce disjunctive goal `|- l \/ r` to `|- l`. -/
def DISJ1_TAC (B : BoolThms) : tactic := fun g => ExceptT.run do
  let (asl, w) := g
  let (l, r) ← liftExcept (Basics.dest_disj w)
  return (null_meta, [(asl, l)], fun i ths =>
    return (match ths with
      | [th] => do B.DISJ1 th (← instantiate i r)
      | _ => failwith "DISJ1_TAC"))

/-- Reduce disjunctive goal `|- l \/ r` to `|- r`. -/
def DISJ2_TAC (B : BoolThms) : tactic := fun g => ExceptT.run do
  let (asl, w) := g
  let (l, r) ← liftExcept (Basics.dest_disj w)
  return (null_meta, [(asl, r)], fun i ths =>
    return (match ths with
      | [th] => do B.DISJ2 (← instantiate i l) th
      | _ => failwith "DISJ2_TAC"))

/-- Case-split on a disjunction theorem `dth : |- l \/ r`. -/
def DISJ_CASES_TAC (B : BoolThms) (dth : thm) : tactic := fun g => ExceptT.run do
  let (asl, w) := g
  let (l, r) ← liftExcept (Basics.dest_disj (concl dth))
  let thl ← liftExcept (ASSUME l)
  let thr ← liftExcept (ASSUME r)
  return (null_meta, [(("", thl) :: asl, w), (("", thr) :: asl, w)], fun i ths =>
    return (match ths with
      | [th1, th2] => do B.DISJ_CASES (← INSTANTIATE_ALL B i dth) th1 th2
      | _ => failwith "DISJ_CASES_TAC"))

/-- Close any goal from a contradiction theorem `cth : |- F`. -/
def CONTR_TAC (B : BoolThms) (cth : thm) : tactic := fun g => do
  let (_, w) := g
  match B.CONTR w cth with
  | .ok th => return .ok (null_meta, [], propagate_thm B th)
  | .error _ => return .error "CONTR_TAC"

/- ---------------------------------------------------------------------- -/
/- Quantifier tactics: X_GEN_TAC, X_CHOOSE_TAC, EXISTS_TAC.               -/
/- ---------------------------------------------------------------------- -/

/-- Check that `e` and `g` have the same type.

    tactics.ml 474-478 reports the two types:
        failwith(pfx ^ ": expected type :" ^ string_of_type et ^
                 " but got :" ^ string_of_type gt)
    so this is IO-valued (our `string_of_type` is IO) in order to reproduce that
    text.  A bare "type mismatch" was a diagnostic regression: `X_GEN_TAC`,
    `X_CHOOSE_TAC` and `EXISTS_TAC` are exactly the tactics where the user needs
    to be told WHICH types disagreed. -/
private def tacTypeCheck (pfx : String) (e g : term) : IO (Except String Unit) := do
  let et := type_of e
  let gt := type_of g
  if et == gt then return .ok ()
  else
    return failwith (pfx ++ ": expected type :" ++ (← Printer.string_of_type et)
                     ++ " but got :" ++ (← Printer.string_of_type gt))

/-- Specialize a universally-quantified goal to the given variable `x'`. -/
def X_GEN_TAC (B : BoolThms) (x' : term) : tactic := fun g => ExceptT.run do
  if !(is_var x') then throw "X_GEN_TAC: not a variable"
  else
    let (asl, w) := g
    match dest_forall w with
    | .error _ => throw "X_GEN_TAC: Not universally quantified"
    | .ok (x, bod) =>
        ExceptT.mk (tacTypeCheck "X_GEN_TAC" x x')
        let avoids := itlist (fun (p : String × thm) acc => union (thm_frees p.2) acc)
                             asl (frees w)
        if mem x' avoids then throw "X_GEN_TAC: invalid variable"
        else
          let sub ← liftExcept (vsubst [(x', x)])
          return (null_meta, [(asl, sub bod)], fun _ ths =>
            return (match ths with
              | [th] => do CONV_RULE (GEN_ALPHA_CONV x) (← B.GEN x' th)
              | _ => failwith "X_GEN_TAC"))

/-- Introduce the witness of an existential theorem `xth` as `x'`. -/
def X_CHOOSE_TAC (B : BoolThms) (x' : term) (xth : thm) : tactic := fun g => ExceptT.run do
  let (asl, w) := g
  match dest_exists (concl xth) with
  | .error _ => throw "X_CHOOSE_TAC: not existential"
  | .ok (x, bod) =>
      ExceptT.mk (tacTypeCheck "X_CHOOSE_TAC" x x')
      let sub ← liftExcept (vsubst [(x', x)])
      let pat := sub bod
      let xth' ← liftExcept (ASSUME pat)
      let avoids := itlist (fun (p : String × thm) acc => union (frees (concl p.2)) acc)
                           asl (union (frees w) (thm_frees xth))
      if mem x' avoids then throw "X_CHOOSE_TAC: invalid variable"
      else
        return (null_meta, [(("", xth') :: asl, w)], fun i ths =>
          return (match ths with
            | [th] => do B.CHOOSE (x', ← INSTANTIATE_ALL B i xth) th
            | _ => failwith "X_CHOOSE_TAC"))

/-- Provide the witness `t` for an existential goal. -/
def EXISTS_TAC (B : BoolThms) (t : term) : tactic := fun g => ExceptT.run do
  let (asl, w) := g
  match dest_exists w with
  | .error _ => throw "EXISTS_TAC: Goal not existentially quantified"
  | .ok (v, bod) =>
      ExceptT.mk (tacTypeCheck "EXISTS_TAC" v t)
      let sub ← liftExcept (vsubst [(t, v)])
      return (null_meta, [(asl, sub bod)], fun i ths =>
        return (match ths with
          | [th] => do B.EXISTS (← instantiate i w, ← instantiate i t) th
          | _ => failwith "EXISTS_TAC"))

/-- Strip one universal quantifier from the goal (fresh primed variable). -/
def GEN_TAC (B : BoolThms) : tactic := fun g => ExceptT.run do
  let (asl, w) := g
  match dest_forall w with
  | .error _ => throw "GEN_TAC"
  | .ok (x, _) =>
      let avoids := itlist (fun (p : String × thm) acc => union (thm_frees p.2) acc)
                           asl (frees w)
      let x' ← (mk_primed_var avoids x : IO (Except String term))
      (X_GEN_TAC B x' g : IO (Except String goalstate))

/-- Introduce the witness of an existential theorem (fresh primed variable). -/
def CHOOSE_TAC (B : BoolThms) (xth : thm) : tactic := fun g => ExceptT.run do
  let (asl, w) := g
  match dest_exists (concl xth) with
  | .error _ => throw "CHOOSE_TAC"
  | .ok (x, _) =>
      let avoids := itlist (fun (p : String × thm) acc => union (thm_frees p.2) acc)
                           asl (union (frees w) (thm_frees xth))
      let x' ← (mk_primed_var avoids x : IO (Except String term))
      (X_CHOOSE_TAC B x' xth g : IO (Except String goalstate))

/- ---------------------------------------------------------------------- -/
/- Matching tactics.                                                      -/
/- ---------------------------------------------------------------------- -/

/-- Accept a theorem that matches the goal (after stripping universals). -/
def MATCH_ACCEPT_TAC (B : BoolThms) (th : thm) : tactic :=
  let rawtac (th : thm) : tactic := fun g => do
    let (_, w) := g
    match ← (PART_MATCH B (fun t => .ok t) th w : IO (Except String thm)) with
    | .ok ith => return .ok (null_meta, [], propagate_thm B ith)
    | .error _ => return .error "ACCEPT_TAC"
  THEN B (REPEAT B (GEN_TAC B)) (rawtac th)

/-- Reduce a goal `q'` to `p'` given `th : |- !… . p ==> q` matching `q ~ q'`. -/
def MATCH_MP_TAC (B : BoolThms) (th : thm) : tactic := fun g => ExceptT.run do
  let sthE : Except String thm := do
    let tm := concl th
    let (avs, bod) := strip_forall tm
    let (ant, con) ← Basics.dest_imp bod
    let th1 ← B.SPECL avs (← ASSUME tm)
    let th2 ← B.UNDISCH th1
    let evs := avs.filter (fun v => vfree_in v ant && !(vfree_in v con))
    let th3 ← itlistM B.SIMPLE_CHOOSE evs (← B.DISCH tm th2)
    let tm3 ← (hyp th3).head?.elim (failwith "MATCH_MP_TAC: Bad theorem") .ok
    B.MP (← B.DISCH tm (← B.GEN_ALL (← B.DISCH tm3 (← B.UNDISCH th3)))) th
  match sthE with
  | .error _ => throw "MATCH_MP_TAC: Bad theorem"
  | .ok sth =>
    let (asl, w) := g
    let matchFn := fun t => (do return (← Basics.dest_imp t).2 : Except String term)
    match ← liftM (PART_MATCH B matchFn sth w : IO (Except String thm)) with
    | .error _ => throw "MATCH_MP_TAC: No match"
    | .ok xth =>
        let (lant, _) ← liftExcept (Basics.dest_imp (concl xth))
        return (null_meta, [(asl, lant)], fun i ths =>
          return (match ths with
            | [th0] => do B.MP (← INSTANTIATE_ALL B i xth) th0
            | _ => failwith "MATCH_MP_TAC"))

/-- Transitivity tactic: reduce `x R z` to `x R tm` and `tm R z` via `th`. -/
def TRANS_TAC (B : BoolThms) (th : thm) (tm : term) : tactic := fun g => ExceptT.run do
  let ctm := (strip_forall (concl th)).2
  let cl_cr ← liftExcept (Basics.dest_conj (← liftExcept (lhand ctm)))
  let (cl, cr) := cl_cr
  let x ← liftExcept (lhand cl)
  let y ← liftExcept (rand cl)
  let z ← liftExcept (rand cr)
  let (_, w) := g
  let (lop, r) ← liftExcept (dest_comb w)
  let (_op, l) ← liftExcept (dest_comb lop)
  -- itlist2 type_match (map type_of [x;y;z]) (map type_of [l;tm;r]) []  (right fold)
  let ilist ← liftExcept (do
    let s1 ← type_match (type_of z) (type_of r) []
    let s2 ← type_match (type_of y) (type_of tm) s1
    type_match (type_of x) (type_of l) s2)
  let th' ← liftExcept (INST_TYPE ilist th)
  (THEN B (MATCH_MP_TAC B th') (EXISTS_TAC B tm) g : IO (Except String goalstate))

/- ---------------------------------------------------------------------- -/
/- Theorem continuations.                                                 -/
/- ---------------------------------------------------------------------- -/

/-- Apply `ttac1` to the first conjunct and `ttac2` to the second. -/
def CONJUNCTS_THEN2 (B : BoolThms) (ttac1 ttac2 : thm_tactic) (cth : thm) : tactic :=
  fun gl => ExceptT.run do
    let (c1, c2) ← liftExcept (Basics.dest_conj (concl cth))
    let ath1 ← liftExcept (ASSUME c1)
    let ath2 ← liftExcept (ASSUME c2)
    let r ← (THEN B (ttac1 ath1) (ttac2 ath2) gl : IO (Except String goalstate))
    let (ti, gls, jfn) := r
    let jfn' : justification := fun i ths => do
      match ← (jfn i ths : IO (Except String thm)) with
      | .error e => return .error e
      | .ok base => return (do
          let (th1, th2) ← B.CONJ_PAIR (← INSTANTIATE_ALL B i cth)
          PROVE_HYP th1 (← PROVE_HYP th2 base))
    return (ti, gls, jfn')

/-- `CONJUNCTS_THEN ttac = CONJUNCTS_THEN2 ttac ttac` (the `W` combinator). -/
def CONJUNCTS_THEN (B : BoolThms) (ttac : thm_tactic) : thm_tactic :=
  CONJUNCTS_THEN2 B ttac ttac

/-- Case-split a disjunction, applying `ttac1`/`ttac2` to each branch. -/
def DISJ_CASES_THEN2 (B : BoolThms) (ttac1 ttac2 : thm_tactic) (cth : thm) : tactic :=
  THENL B (DISJ_CASES_TAC B cth) [POP_ASSUM ttac1, POP_ASSUM ttac2]

/-- `DISJ_CASES_THEN ttac = DISJ_CASES_THEN2 ttac ttac`. -/
def DISJ_CASES_THEN (B : BoolThms) (ttac : thm_tactic) : thm_tactic :=
  DISJ_CASES_THEN2 B ttac ttac

/-- Discharge the antecedent, then apply `ttac` to it. -/
def DISCH_THEN (B : BoolThms) (ttac : thm_tactic) : tactic :=
  THEN B (DISCH_TAC B) (POP_ASSUM ttac)

/-- Choose the witness `x` from an existential, then apply `ttac`. -/
def X_CHOOSE_THEN (B : BoolThms) (x : term) (ttac : thm_tactic) (th : thm) : tactic :=
  THEN B (X_CHOOSE_TAC B x th) (POP_ASSUM ttac)

/-- Choose a fresh witness from an existential, then apply `ttac`. -/
def CHOOSE_THEN (B : BoolThms) (ttac : thm_tactic) (th : thm) : tactic :=
  THEN B (CHOOSE_TAC B th) (POP_ASSUM ttac)

/- ---------------------------------------------------------------------- -/
/- Various derived tactics and theorem continuations.                     -/
/- ---------------------------------------------------------------------- -/

/-- Break a theorem apart along conjunction/disjunction/existential structure. -/
def STRIP_THM_THEN (B : BoolThms) : thm_tactical := fun ttac th =>
  FIRST_TCL [CONJUNCTS_THEN B, DISJ_CASES_THEN B, CHOOSE_THEN B] ttac th

/-- Resolve `ante` against every assumption that is an implication it satisfies,
    applying `ttac` to each result. -/
def ANTE_RES_THEN (B : BoolThms) (ttac : thm_tactic) (ante : thm) : tactic :=
  ASSUM_LIST (fun asl => fun g => do
    let tacs ← asl.filterMapM (fun imp => do
      match ← (MATCH_MP B imp ante : IO (Except String thm)) with
      | .ok r => return some (ttac r)
      | .error _ => return none)
    if tacs.isEmpty then return .error "IMP_RES_THEN"
    else (EVERY B tacs g : IO (Except String goalstate)))

/-- Resolve implication `imp` against every assumption it applies to. -/
def IMP_RES_THEN (B : BoolThms) (ttac : thm_tactic) (imp : thm) : tactic :=
  ASSUM_LIST (fun asl => fun g => do
    let tacs ← asl.filterMapM (fun ante => do
      match ← (MATCH_MP B imp ante : IO (Except String thm)) with
      | .ok r => return some (ttac r)
      | .error _ => return none)
    if tacs.isEmpty then return .error "IMP_RES_THEN"
    else (EVERY B tacs g : IO (Except String goalstate)))

/-- Fully break down a theorem and add/accept/discard its parts. -/
def STRIP_ASSUME_TAC (B : BoolThms) : thm_tactic :=
  let DISCARD_TAC (th : thm) : tactic := fun g =>
    let (asl, _) := g
    let tm := concl th
    if asl.any (fun a => aconv tm (concl a.2)) then (ALL_TAC g : IO (Except String goalstate))
    else return .error "DISCARD_TAC: not already present"
  REPEAT_TCL (STRIP_THM_THEN B)
    (fun gth => FIRST B [CONTR_TAC B gth, ACCEPT_TAC B gth, DISCARD_TAC gth, ASSUME_TAC B gth])

/-- Structural case-split continuation. -/
def STRUCT_CASES_THEN (B : BoolThms) (ttac : thm_tactic) : thm_tactic :=
  REPEAT_TCL (STRIP_THM_THEN B) ttac

/-- Structural case-split, substituting or assuming each case. -/
def STRUCT_CASES_TAC (B : BoolThms) : thm_tactic :=
  STRUCT_CASES_THEN B
    (fun th => ORELSE (SUBST1_TAC B th) (ASSUME_TAC B th))

/-- Peel one layer off the goal (GEN/CONJ/DISCH), applying `ttac`. -/
def STRIP_GOAL_THEN (B : BoolThms) (ttac : thm_tactic) : tactic :=
  FIRST B [GEN_TAC B, CONJ_TAC B, DISCH_THEN B ttac]

/-- The main structural stripping tactic. -/
def STRIP_TAC (B : BoolThms) : tactic := fun g => do
  match ← (STRIP_GOAL_THEN B (STRIP_ASSUME_TAC B) g : IO (Except String goalstate)) with
  | .ok r => return .ok r
  | .error _ => return .error "STRIP_TAC"

/-- Undischarge the assumption alpha-equal to `tm`, applying `ttac` to it. -/
def UNDISCH_THEN (_B : BoolThms) (tm : term) (ttac : thm_tactic) : tactic := fun g =>
  let (asl, w) := g
  match remove (fun (p : String × thm) => aconv (concl p.2) tm) asl with
  | .error _ => return .error "UNDISCH_THEN"
  | .ok (thp, asl') => ttac thp.2 (asl', w)

/-- Like `FIRST_ASSUM` but removes the used assumption. -/
def FIRST_X_ASSUM (B : BoolThms) (ttac : thm_tactic) : tactic :=
  FIRST_ASSUM (fun th => UNDISCH_THEN B (concl th) ttac)

/- ---------------------------------------------------------------------- -/
/- Subgoaling and freezing variables (latter is especially useful now).   -/
/- ---------------------------------------------------------------------- -/

/-- Prove `wa` as a lemma (added as a subgoal) and continue with `ttac`. -/
def SUBGOAL_THEN (_B : BoolThms) (wa : term) (ttac : thm_tactic) : tactic :=
  fun g => ExceptT.run do
    let (asl, w) := g
    let ath ← liftExcept (ASSUME wa)
    let r ← (ttac ath (asl, w) : IO (Except String goalstate))
    let mt := r.1
    let gl := r.2.1
    let just := r.2.2
    let just' : justification := fun i l =>
      match l with
      | hd :: tl => do
          match ← (just i tl : IO (Except String thm)) with
          | .error e => return .error e
          | .ok base => return (PROVE_HYP hd base)
      | [] => return (failwith "SUBGOAL_THEN")
    return (mt, (asl, wa) :: gl, just')

/-- `SUBGOAL_TAC s tm [prf]`: prove `tm` (labelled `s`) by `prf`, then continue. -/
def SUBGOAL_TAC (B : BoolThms) (s : String) (tm : term) (prfs : List tactic) : tactic :=
  match prfs with
  | p :: _ => THENL B (SUBGOAL_THEN B tm (LABEL_TAC B s)) [p, ALL_TAC]
  | [] => fun _ => return .error "SUBGOAL_TAC: no subproof given"

/-- Freeze the theorem `th` as an assumption for the continuation `ttac`. -/
def FREEZE_THEN (_B : BoolThms) (ttac : thm_tactic) (th : thm) : tactic :=
  fun g => ExceptT.run do
    let (asl, w) := g
    let ath ← liftExcept (ASSUME (concl th))
    let r ← (ttac ath (asl, w) : IO (Except String goalstate))
    let mt := r.1
    let gl := r.2.1
    let just := r.2.2
    let just' : justification := fun i l => do
      match ← (just i l : IO (Except String thm)) with
      | .error e => return .error e
      | .ok base => return (PROVE_HYP th base)
    return (mt, gl, just')

/- ---------------------------------------------------------------------- -/
/- Metavariable tactics.                                                  -/
/- ---------------------------------------------------------------------- -/

/-- Introduce `t` as a metavariable witness for an existential goal. -/
def X_META_EXISTS_TAC (B : BoolThms) (t : term) : tactic := fun g => ExceptT.run do
  if !(is_var t) then throw "X_META_EXISTS_TAC"
  else
    let (asl, w) := g
    let (v, bod) ← liftExcept (dest_exists w)
    let sub ← liftExcept (vsubst [(t, v)])
    return (([t], null_inst), [(asl, sub bod)], fun i ths =>
      return (match ths with
        | [th] => do B.EXISTS (← instantiate i w, ← instantiate i t) th
        | _ => failwith "X_META_EXISTS_TAC"))

/-- Introduce a fresh metavariable witness for an existential goal. -/
def META_EXISTS_TAC (B : BoolThms) : tactic := fun g => ExceptT.run do
  let (asl, w) := g
  let (v, _) ← liftExcept (dest_exists w)
  let avoids := itlist (fun (p : String × thm) acc => union (frees (concl p.2)) acc)
                       asl (frees w)
  let v' ← (mk_primed_var avoids v : IO (Except String term))
  (X_META_EXISTS_TAC B v' g : IO (Except String goalstate))

/-- Specialize `thm` to a metavariable `t`, adding it as an assumption. -/
def META_SPEC_TAC (B : BoolThms) (t : term) (thm : thm) : tactic := fun g => ExceptT.run do
  let (asl, w) := g
  let sth ← liftExcept (B.SPEC t thm)
  return (([t], null_inst), [(("", sth) :: asl, w)], fun i ths =>
    return (match ths with
      | [th] => do PROVE_HYP (← B.SPEC (← instantiate i t) thm) th
      | _ => failwith "META_SPEC_TAC"))

/- ---------------------------------------------------------------------- -/
/- If all else fails!                                                     -/
/- ---------------------------------------------------------------------- -/

/-- Accept the goal via a fresh axiom (UNSOUND). -/
def CHEAT_TAC (B : BoolThms) : tactic := fun g => ExceptT.run do
  let (_, w) := g
  let th ← (mk_thm B [] w : IO (Except String thm))
  (ACCEPT_TAC B th g : IO (Except String goalstate))

/- ---------------------------------------------------------------------- -/
/- Intended for time-consuming rules; delays evaluation till it sees goal. -/
/- ---------------------------------------------------------------------- -/

/-- Delay a (possibly expensive) rule until the goal is seen, then accept. -/
def RECALL_ACCEPT_TAC (B : BoolThms) (r : α → IO (Except String thm)) (a : α) : tactic :=
  fun g => ExceptT.run do
    let th ← (r a : IO (Except String thm))
    (ACCEPT_TAC B th g : IO (Except String goalstate))

/- ---------------------------------------------------------------------- -/
/- Split off antecedent of antecedent as a subgoal.                       -/
/- ---------------------------------------------------------------------- -/

/-- Split off the antecedent of an antecedent as a subgoal. -/
def ANTS_TAC (B : BoolThms) : tactic := fun g => ExceptT.run do
  -- tm1 = `p /\ (q ==> r)`,  tm2 = `p ==> q`
  let p : term := .Var "p" bool_ty
  let q : term := .Var "q" bool_ty
  let rr : term := .Var "r" bool_ty
  let qimpr ← liftExcept (mk_imp q rr)
  let tm1 ← liftExcept (mk_conj p qimpr)
  let tm2 ← liftExcept (mk_imp p q)
  let th ← liftExcept (do
    let (th1, th2) ← B.CONJ_PAIR (← ASSUME tm1)
    let inner ← B.MP th2 (← B.MP (← ASSUME tm2) th1)
    -- itlist DISCH [tm1;tm2] inner
    B.DISCH tm1 (← B.DISCH tm2 inner))
  (THEN B (MATCH_MP_TAC B th) (CONJ_TAC B) g : IO (Except String goalstate))

/- ---------------------------------------------------------------------- -/
/- A printer for goals etc.                                               -/
/- ---------------------------------------------------------------------- -/

/-- Right-justify a small integer to width 3. -/
private def stringOfInt3 (n : Nat) : String :=
  if n < 10 then "  " ++ toString n
  else if n < 100 then " " ++ toString n
  else toString n

/-- A parameter to prettyprinter's max boxes for printing hypotheses.
    Set to None if the formatter's default max boxes value is to be used. -/
initialize print_goal_hyp_max_boxes : IO.Ref (Option Nat) ← IO.mkRef none

/-- `pp_print_goal` / `pp_print_colored_goal` (tactics.ml `with_color`):
    the hypotheses in reverse order, numbered from 0, each `n [`t`] (label)`,
    then the conclusion. -/
private def goalFmt (color_flag : Bool) (g : goal) : IO (Fmt Unit) := do
  let (asl, w) := g
  let qterm := if color_flag then Printer.pp_print_colored_qterm else Printer.pp_print_qterm
  let hb ← print_goal_hyp_max_boxes.get
  let hyps ← asl.reverse.mapM (fun (s, th) => do return (s, ← qterm (concl th)))
  let wf ← qterm w
  let print_hyp (n : Nat) (s : String) (tf : Fmt Unit) : Fmt Unit := do
    Fmt.openHBox
    Fmt.printString (stringOfInt3 n)
    Fmt.printString " ["
    Fmt.openHvBox 0
    let old_max_boxes ← Fmt.getMaxBoxes
    match hb with
    | none => pure ()
    | some b => Fmt.setMaxBoxes b
    tf
    Fmt.setMaxBoxes old_max_boxes
    Fmt.closeBox
    Fmt.printString "]"
    if s != "" then Fmt.printString (" (" ++ s ++ ")")
    Fmt.closeBox
    Fmt.printNewline
  return do
    Fmt.printNewline
    if !asl.isEmpty then
      for (n, (s, tf)) in (List.range hyps.length).zip hyps do print_hyp n s tf
      Fmt.printNewline
    wf
    Fmt.printNewline

/-- `pp_print_goal`. -/
def pp_print_goal (g : goal) : IO (Fmt Unit) := goalFmt false g
/-- `pp_print_colored_goal`. -/
def pp_print_colored_goal (g : goal) : IO (Fmt Unit) := goalFmt true g

/-- `pp_print_goalstack` / `pp_print_colored_goalstack`: the header, then the
    `k` newest subgoals, last first. -/
private def goalstackFmt (color_flag : Bool) (l : goalstack) : IO (Fmt Unit) := do
  let print_goalstate (k : Nat) (gs : goalstate) : IO (Fmt Unit) := do
    let (_, gl, _) := gs
    let n := gl.length
    let s := if n == 0 then "No subgoals" else
               toString k ++ " subgoal" ++ (if k > 1 then "s" else "") ++
               " (" ++ toString n ++ " total)"
    -- do_list (pp_print_goal fmt o C el gl) (rev(0--(k-1)))
    let goals ← if gl.isEmpty then pure [] else
      (List.range k).reverse.mapM (fun i => do
        match el i gl with
        | .ok g => goalFmt color_flag g
        | .error e => throw (IO.userError e))
    return do
      Fmt.printString s
      Fmt.printNewline
      for gf in goals do gf
  match l with
  | [] => return Fmt.printString "Empty goalstack"
  | [gs] => print_goalstate 1 gs
  | gs :: (_, gl0, _) :: _ =>
    let (_, gl, _) := gs
    let p := (gl.length : Int) - (gl0.length : Int)
    let p' := if p < 1 then 1 else p + 1
    print_goalstate p'.toNat gs

/-- `pp_print_goalstack`. -/
def pp_print_goalstack (l : goalstack) : IO (Fmt Unit) := goalstackFmt false l
/-- `pp_print_colored_goalstack`. -/
def pp_print_colored_goalstack (l : goalstack) : IO (Fmt Unit) := goalstackFmt true l

/-- Render to standard output (`Format.std_formatter`). -/
private def printFmt (f : IO (Fmt Unit)) : IO Unit := do
  IO.print (Fmt.runStd (← Printer.get_margin) (← f))

/-- `print_goal = pp_print_goal Format.std_formatter`. -/
def print_goal (g : goal) : IO Unit := printFmt (pp_print_goal g)
/-- `print_goalstack = pp_print_goalstack Format.std_formatter`. -/
def print_goalstack (l : goalstack) : IO Unit := printFmt (pp_print_goalstack l)

/-- `PRINT_GOAL_TAC`: print the goal, then do nothing. -/
def PRINT_GOAL_TAC : tactic := fun gl => do
  print_goal gl
  (ALL_TAC gl : IO (Except String goalstate))

/-- `PRINT_COLORED_GOAL_TAC`: print the goal in color, then do nothing. -/
def PRINT_COLORED_GOAL_TAC : tactic := fun gl => do
  printFmt (pp_print_colored_goal gl)
  (ALL_TAC gl : IO (Except String goalstate))

/-- Tactic that prints a remark, then does nothing. -/
def REMARK_TAC (s : String) : tactic := fun gl => do
  remark s
  (ALL_TAC gl : IO (Except String goalstate))

/- ---------------------------------------------------------------------- -/
/- Convert a tactic into a refinement on the head subgoal.                -/
/- ---------------------------------------------------------------------- -/

/-- Turn a tactic into a refinement acting on the head subgoal of a state.
    (Named `by_` since `by` is a Lean keyword.) -/
def by_ (B : BoolThms) (tac : tactic) : refinement := fun gstate => ExceptT.run do
  let mvs := gstate.1.1
  let inst := gstate.1.2
  let gls := gstate.2.1
  let just := gstate.2.2
  match gls with
  | [] => throw "No goal set"
  | g :: ogls =>
      let r ← (tac g : IO (Except String goalstate))
      let newmvs := r.1.1
      let newinst := r.1.2
      let subgls := r.2.1
      let subjust := r.2.2
      let n := subgls.length
      let mvs' := union newmvs mvs
      let inst' ← liftExcept (compose_insts inst newinst)
      let ogls' ← liftExcept (ogls.mapM (inst_goal B newinst))
      let gls' := subgls ++ ogls'
      let just' : justification := fun i ths => do
        match compose_insts inst' i with
        | .error e => return .error e
        | .ok i' =>
          match chop_list n ths with
          | .error e => return .error e
          | .ok (cths, oths) =>
            match ← (subjust i cths : IO (Except String thm)) with
            | .error e => return .error e
            | .ok sth => (just i' (sth :: oths) : IO (Except String thm))
      return ((mvs', inst'), gls', just')

/- ---------------------------------------------------------------------- -/
/- Rotate the goalstate either way.                                       -/
/- ---------------------------------------------------------------------- -/

/-- Rotate subgoals forward (`rotate_p`) or backward (`rotate_n`) `n` times.
    As in OCaml, rotating an empty subgoal list fails ("hd" forwards,
    "butlast" backwards), and so does a justification given no theorems. -/
def rotate (n : Int) : refinement :=
  let rotate_p (gs : goalstate) : Except String goalstate := do
    let (mvs, sgs, just) := gs
    match sgs with
    | [] => failwith "hd"
    | h :: t =>
      -- ths' = (last ths)::(butlast ths); OCaml evaluates `butlast` first.
      let just' : justification := fun i ths =>
        match ths.getLast? with
        | none => return failwith "butlast"
        | some l => just i (l :: ths.dropLast)
      return (mvs, t ++ [h], just')
  let rotate_n (gs : goalstate) : Except String goalstate := do
    let (mvs, sgs, just) := gs
    -- sgs' = (last sgs)::(butlast sgs); OCaml evaluates `butlast` first.
    match sgs.getLast? with
    | none => failwith "butlast"
    | some l =>
      -- ths' = (tl ths)@[hd ths]
      let just' : justification := fun i ths =>
        match ths with
        | [] => return failwith "hd"
        | h :: t => just i (t ++ [h])
      return (mvs, l :: sgs.dropLast, just')
  let rec pow (f : goalstate → Except String goalstate) : Nat → goalstate → Except String goalstate
    | 0, gs => .ok gs
    | k + 1, gs => do pow f k (← f gs)
  fun gs =>
    -- `funpow n f x = f (funpow (n-1) f x)`: all steps are the same function.
    if n > 0 then return pow rotate_p n.toNat gs
    else return pow rotate_n (-n).toNat gs

/- ---------------------------------------------------------------------- -/
/- Perform refinement proof, tactic proof etc.                            -/
/- ---------------------------------------------------------------------- -/

/-- Build the initial goalstate for a (boolean) goal. -/
def mk_goalstate (B : BoolThms) (g : goal) : Except String goalstate :=
  let (_, w) := g
  if type_of w == bool_ty then
    .ok (null_meta, [g], fun i ths =>
      return (match ths with
        | [th] => INSTANTIATE_ALL B i th
        | _ => failwith "mk_goalstate"))
  else failwith "mk_goalstate: Non-boolean goal"

/-- Run a tactic proof, returning the proved theorem (fails if goals remain). -/
def TAC_PROOF (B : BoolThms) (g : goal) (tac : tactic) : IO (Except String thm) :=
  ExceptT.run do
    let gstate ← liftExcept (mk_goalstate B g)
    let r ← (by_ B tac gstate : IO (Except String goalstate))
    let sgs := r.2.1
    let just := r.2.2
    if sgs == [] then (just null_inst [] : IO (Except String thm))
    else throw "TAC_PROOF: Unsolved goals"

/-- Prove a term by a tactic, returning `|- t`. -/
def prove (B : BoolThms) (t : term) (tac : tactic) : IO (Except String thm) :=
  ExceptT.run do
    let th ← (TAC_PROOF B ([], t) tac : IO (Except String thm))
    let (asl, t') := dest_thm th
    if asl != [] then throw "prove: additional assumptions in result"
    else if t' == t then return th
    else
      match (do EQ_MP (← ALPHA t' t) th : Except String thm) with
      | .ok r => return r
      | .error _ => throw "prove: justification generated wrong theorem"

end HolCore.Tactics
