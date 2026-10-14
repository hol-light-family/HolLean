/- File: Itab.lean
Intuitionistic theorem prover (complete for propositional fragment).
Original       John Harrison, University of Cambridge Computer Laboratory
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Lean4 translation by Chris Walton 2026
-/

import HolCore.Bool
import HolCore.Basics
import HolCore.Fusion
import HolCore.Equal
import HolCore.Drule
import HolCore.Tactics

open HolCore.Kernel HolCore.Basics HolCore.Lib HolCore.Bool HolCore.Equal
     HolCore.Drule HolCore.Tactics

namespace HolCore.Itab

/- ---------------------------------------------------------------------- -/
/- Accept a theorem modulo unification.                                   -/
/- ---------------------------------------------------------------------- -/

/-- Accept `th` as closing the goal, up to unification of the metavariables
    `mvs`. Uses the IO `term_unify` and the pure `INSTANTIATE`. -/
def UNIFY_ACCEPT_TAC (mvs : List term) (th : thm) : tactic := fun g =>
  ExceptT.run do
    let (_, w) := g
    let insts ← (term_unify mvs (concl th) w : IO (Except String instantiation))
    let th' ← liftExcept (INSTANTIATE insts th)
    return (([], insts), [], fun i ths =>
      return (match ths with
        | [] => INSTANTIATE i th'
        | _  => failwith "UNIFY_ACCEPT_TAC"))

/- ---------------------------------------------------------------------- -/
/- REFL version of UNIFY_ACCEPT_TAC.                                      -/
/- The conclusion ust be `expr = x` where x is a meta variable.           -/
/- It can be `expr = f x y z` where f is a meta variable as well.         -/
/- ---------------------------------------------------------------------- -/

/-- Reflexivity modulo unification: close a goal `expr = x` (or `expr = f …`)
    by taking `x` (or `f`) as the metavariable to unify. Uses `prove`/`genvar`
    (hence `B`). -/
def UNIFY_REFL_TAC (B : BoolThms) : tactic := fun g => ExceptT.run do
  let (asl, w) := g
  let (w_lhs, w_rhs) ← liftExcept (dest_eq w)
  if is_var w_rhs then
    if vfree_in w_rhs w_lhs then
      throw s!"UNIFY_REFL_TAC: failed: `{← liftM (HolCore.Printer.string_of_term w)}`"
    else
      (UNIFY_ACCEPT_TAC [w_rhs] (REFL w_lhs) (asl, w) : IO (Except String goalstate))
  else
    let (constr, rargs) := strip_comb w_rhs
    if !(is_var constr) then throw "UNIFY_REFL_TAC: not variable"
    else if vfree_in constr w_lhs then
      throw s!"UNIFY_REFL_TAC: failed: `{← liftM (HolCore.Printer.string_of_term w)}`"
    else
      -- replace non-variable arguments of the RHS function with temporary
      -- variables.
      let rargs_vars ← rargs.mapM (fun v =>
        if is_var v then pure v else do
          IO.println s!"UNIFY_REFL_TAC: warning: this isn't var: {← HolCore.Printer.string_of_term v}"
          liftM (genvar (type_of v)))
      let f ← liftExcept (list_mk_abs rargs_vars w_lhs)
      let rhs ← liftExcept (list_mk_comb f rargs)
      let mkEq ← (mk_eq : IO (Except String ((term × term) → Except String term)))
      let the_goal ← liftExcept (mkEq (w_lhs, rhs))
      let th ← (prove B the_goal
                  (THEN B
                    (CONV_TAC B (fun t => return (RAND_CONV (DEPTH_CONV BETA_CONV) t)))
                    (REFL_TAC B))
                : IO (Except String thm))
      (UNIFY_ACCEPT_TAC [constr] th (asl, w) : IO (Except String goalstate))

/- ---------------------------------------------------------------------- -/
/- The actual prover, as a tactic.                                        -/
/- ---------------------------------------------------------------------- -/

/-- `CONJUNCTS_THEN' ttac cth`: apply `ttac` to both conjuncts of `cth`. -/
private def CONJUNCTS_THEN' (B : BoolThms) (ttac : thm_tactic) (cth : thm) : tactic :=
  fun g => do
    match B.CONJUNCT1 cth, B.CONJUNCT2 cth with
    | .ok c1, .ok c2 => (THEN B (ttac c1) (ttac c2) g : IO (Except String goalstate))
    -- Propagate CONJUNCT1/CONJUNCT2's OWN failure, as OCaml does (itab.ml 60)
    -- and as the identical copy in Meson.lean does.
    | .error e, _ => return .error e
    | _, .error e => return .error e

/-- `IMPLICATE t`: from `~a` (i.e. `t`), derive `|- ~a = (a ==> F)` via `NOT_DEF`. -/
private def IMPLICATE (B : BoolThms) (t : term) : Except String thm := do
  let a ← dest_neg t
  let th1 ← AP_THM B.NOT_DEF a
  CONV_RULE (RAND_CONV BETA_CONV) th1

/-- Reversible right rules: split /\, strip !, discharge ==>/~, split <=>. -/
private def RIGHT_REVERSIBLE_TAC (B : BoolThms) : tactic :=
  FIRST B [CONJ_TAC B,   -- and
           GEN_TAC B,    -- forall
           DISCH_TAC B,  -- implies; not
           EQ_TAC B]     -- iff

/-- Try a list of tactics on a goal, returning the first success (IO tryfind). -/
private def tryfindTac : List tactic → tactic := fun tacs g =>
  tryfindM (fun t => t g) tacs

/-- Reversible left rules on assumption `th`: break /\, \/, ?, ~, <=>. -/
private def LEFT_REVERSIBLE_TAC (B : BoolThms) (th : thm) : tactic := fun gl =>
  let notTac : tactic := fun g => do
    match IMPLICATE B (concl th) with
    | .error e => return .error e
    | .ok impl =>
      match EQ_MP impl th with
      | .ok r => (ASSUME_TAC B r g : IO (Except String goalstate))
      | .error e => return .error e
  let iffTac : tactic := fun g => do
    match B.EQ_IMP_RULE th with
    | .error e => return .error e
    | .ok (th1, th2) =>
      match B.CONJ th1 th2 with
      | .ok c => (CONJUNCTS_THEN' B (MP_TAC B) c g : IO (Except String goalstate))
      | .error e => return .error e
  tryfindTac
    [ CONJUNCTS_THEN' B (ASSUME_TAC B) th,  -- and
      DISJ_CASES_TAC B th,                  -- or
      CHOOSE_TAC B th,                      -- exists
      notTac,                               -- not
      iffTac ] gl                           -- iff

/-- The core intuitionistic search tactic: `ITAUT_TAC mvs n` searches to
    depth `n` with metavariables `mvs`. -/
private partial def ITAUT_TAC (B : BoolThms) (mvs : List term) (n : Int) : tactic :=
  fun gl => do
    if n <= 0 then return .error "ITAUT_TAC: Too deep"
    else
      let step7 : tactic := fun g => do
        let (_, w) := g
        match dest_exists w with
        | .error e => return .error e
        | .ok (ev, _) => do
            let gv ← genvar (type_of ev)
            -- OCaml `A THEN B THEN C` is `(A THEN B) THEN C`; the grouping
            -- matters on failure (`B` runs on every subgoal before `C` fails).
            (THEN B (THEN B (X_META_EXISTS_TAC B gv) (ITAUT_TAC B (gv :: mvs) (n - 2)))
                NO_TAC g
              : IO (Except String goalstate))
      let allTac : thm_tactic := fun th => fun g => do
        match dest_forall (concl th) with
        | .error e => return .error e
        | .ok (fv, _) => do
            let gv ← genvar (type_of fv)
            (THEN B (ASSUME_TAC B th)
              (THEN B (THEN B (META_SPEC_TAC B gv th) (ITAUT_TAC B (gv :: mvs) (n - 2)))
                NO_TAC) g
              : IO (Except String goalstate))
      let impTac : thm → tactic := fun th => fun g => do
        match Basics.dest_imp (concl th) with
        | .error e => return .error e
        | .ok (ant, _) =>
            (THEN B (THEN B (SUBGOAL_THEN B ant
                      (fun ath => fun g2 => do
                        match B.MP th ath with
                        | .ok m => (ASSUME_TAC B m g2 : IO (Except String goalstate))
                        | .error e => return .error e))
              (ITAUT_TAC B mvs (n - 1))) NO_TAC g
              : IO (Except String goalstate))
      (ORELSE (FIRST_ASSUM (UNIFY_ACCEPT_TAC mvs))
       (ORELSE (ACCEPT_TAC B B.TRUTH)
       (ORELSE (FIRST_ASSUM (CONTR_TAC B))
       (ORELSE (THEN B (RIGHT_REVERSIBLE_TAC B) (TRY B (ITAUT_TAC B mvs n)))
       (ORELSE (THEN B (FIRST_X_ASSUM B (LEFT_REVERSIBLE_TAC B)) (TRY B (ITAUT_TAC B mvs n)))
       (ORELSE (FIRST_X_ASSUM B allTac)
       (ORELSE (THEN B (THEN B (DISJ1_TAC B) (ITAUT_TAC B mvs n)) NO_TAC)
       (ORELSE (THEN B (THEN B (DISJ2_TAC B) (ITAUT_TAC B mvs n)) NO_TAC)
       (ORELSE step7
               (FIRST_ASSUM impTac)))))))))) gl

/-- Iterative-deepening driver: search with increasing depth limit. -/
private partial def ITAUT_ITERDEEP_TAC (B : BoolThms) (n : Int) : tactic := fun gl => do
  remark s!"Searching with limit {n}"
  (ORELSE (THEN B (ITAUT_TAC B [] n) NO_TAC) (ITAUT_ITERDEEP_TAC B (n + 1)) gl
    : IO (Except String goalstate))

/-- The intuitionistic tableau prover as a tactic. -/
def ITAUT_TAC_MAIN (B : BoolThms) : tactic := ITAUT_ITERDEEP_TAC B 0

/- ---------------------------------------------------------------------- -/
/- Alternative interface.                                                 -/
/- ---------------------------------------------------------------------- -/

/-- Prove a (propositional/intuitionistic) tautology `tm`. -/
def ITAUT (B : BoolThms) (tm : term) : IO (Except String thm) :=
  prove B tm (ITAUT_TAC_MAIN B)

end HolCore.Itab
