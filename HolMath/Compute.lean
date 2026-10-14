/- File: Compute.lean
Call-by-value reduction of terms similar to ML computation.
Translated from HOL4 computeLib.
Original (c) Copyright Alexey Solovyev 2018
Original (c) Copyright Bruno Barras 2000
Distributed under the same license as HOL Light.
Lean4 translation by Chris Walton 2026

`compute.ml` is an OCaml module (`module Compute : Compute_sig`) whose exports are
restricted by a signature.  Here it becomes the namespace `HolMath.Compute`; the
pieces the signature hides stay `private`.

Lean rejects an `IO.Ref` inside a mutual inductive, so where OCaml's `dterm` has
`Cst of term * ('a * int option) ref` this `Cst` carries only the constant term
and the cell is reached by looking the constant's name up in the compset.
Consequently `mk_clos` and its callers take the compset as an argument.
-/

import HolCore.Bool
import HolCore.Equal
import HolCore.Drule
import HolCore.Tactics
import HolCore.Simp
import HolCore.Parser
import HolCore.Theorems
import HolCore.IndDefs
import HolCore.Classic
import HolCore.Printer
import HolMath.Pair

open HolCore
open HolCore.Kernel HolCore.Basics HolCore.Lib HolCore.Bool HolCore.Equal
     HolCore.Drule HolCore.Tactics HolCore.Simp HolCore.Parser HolCore.Theorems
     HolCore.IndDefs HolCore.Classic
open HolLight (HolBase)

namespace HolMath.Compute

set_option maxRecDepth 4000

/- ---------------------------------------------------------------------- -/
/- compute_rules.sml : the reduction stack.                               -/
/- ---------------------------------------------------------------------- -/

/-- `('a,'b,'c) stack` — the context of a reduction. -/
inductive stack (α β γ : Type) where
  | Ztop   : stack α β γ
  | Zrator : α → stack α β γ → stack α β γ
  | Zrand  : β → stack α β γ → stack α β γ
  | Zabs   : γ → stack α β γ → stack α β γ
  deriving Inhabited

/-- `exception Dead_code of string` — an invariant violation. -/
def Dead_code (s : String) : String := "Dead_code: " ++ s

/-- `exception No_match` — a rewrite rule did not apply. -/
def No_match : String := "No_match"

/- ---------------------------------------------------------------------- -/
/- clauses.sml : reduction rules we can handle,                           -/
/-         (c p1...pn) = rhs                                              -/
/- with p1...pn either a const applied to patterns or a free variable.    -/
/- ---------------------------------------------------------------------- -/

/-- `pattern` — a constant applied to patterns, or a pattern variable. -/
inductive pattern where
  | Pvar : Int → pattern
  | Papp : term → List pattern → pattern
  deriving Inhabited

/- ---------------------------------------------------------------------- -/
/- The term representations.                                              -/
/-                                                                        -/
/- CLOS denotes a delayed substitution (closure).                         -/
/- CST denotes an applied constant.  Its first argument is the head       -/
/-   constant; the second is the list of its arguments (we keep both the  -/
/-   term and its abstract representation); the last one is the set of    -/
/-   rewrites that still have a chance to be used, ie. those with a lhs   -/
/-   wider than the number of applied args.                               -/
/- NEUTR is a slight improvement of CST with an empty list of rewrites,   -/
/-   so that arguments of a variable are immediatly strongly reduced.     -/
/-                                                                        -/
/- `dterm` is an alternative representation of terms, with all            -/
/- information needed:                                                    -/
/- - they are real de Bruijn terms, so that abstraction destruction is in -/
/-   constant time.                                                       -/
/- - application is n-ary (slight optimization)                           -/
/- - we forget the names of variables                                     -/
/- - constants are tagged with the set of rewrites that apply to it.      -/
/-   It's a reference since dterm is used to represent rhs of rewrites,    -/
/-   and fixpoints equations add rewrites for a constant that appear in    -/
/-   the rhs.                                                             -/
/-                                                                        -/
/- OCaml's `fterm`/`dterm` are polymorphic in the rewrite type `'a` but   -/
/- are only ever instantiated at `'a = db`, so they are monomorphic here  -/
/- and share one mutual block with `db`.                                  -/
/- ---------------------------------------------------------------------- -/

mutual

/-- `'a cst_rec` — an applied constant. -/
structure cst_rec where
  head : term
  args : List (term × fterm)
  rws  : db
  skip : Option Int

/-- `'a clos_rec` — a delayed substitution. -/
structure clos_rec where
  env  : List fterm
  term : dterm

/-- `'a fterm` — the run-time form of a term. -/
inductive fterm where
  | Const : cst_rec → fterm
  | Neutr : fterm
  | Clos  : clos_rec → fterm

/-- `'a dterm` — the de Bruijn form of a term.  `Cst` carries only the constant
    (see the structural note in the file header). -/
inductive dterm where
  | Bv  : Int → dterm
  | Fv  : dterm
  | Cst : term → dterm
  | App : dterm → List dterm → dterm   -- order: outermost ahead
  | Abs : dterm → dterm

/-- `action` — what a database node does: rewrite rules, or a conversion.

    STRUCTURAL ADAPTATION (forced by Lean, as for `dterm.Cst`).  OCaml stores
    `Conv of (term -> thm * db fterm)`, but a function returning one of the
    datatypes being declared (here under `IO`) is not a valid occurrence.  We
    store the underlying conversion instead.  This is faithful: the payload is
    only ever `extern_of_conv rws conv` (built by `add_conv`), whose body is
    `fun tm => let thm = conv tm in (thm, mk_clos ([], from_term (rws,[],rhs (concl thm))))`,
    and its single consumer is `reduce_cst` — which has the compset to hand, so
    it performs that step itself.  The `rws` captured by OCaml's closure always
    coincides with the compset being reduced with, since `add_conv` stores the
    action in the very compset it closes over. -/
inductive action where
  | Rewrite : List rewrite → action
  | Conv    : ioconv → action

/-- `try_rec` — one node of the database. -/
structure try_rec where
  hcst : term
  rws  : action
  tail : db

/-- `db` — rules packed by head constant, then sorted by lhs width. -/
inductive db where
  | End_db   : db
  | Try      : try_rec → db
  | Need_arg : db → db

/-- `rewrite_rec` — a single reduction rule. -/
structure rewrite_rec where
  cst : term            -- constant which the rule applies to
  lhs : List pattern    -- patterns = constant args in lhs of thm
  npv : Int             -- number of distinct pat vars in lhs
  rhs : dterm
  thm : thm             -- thm we use for rewriting

/-- `rewrite` — a reduction rule. -/
inductive rewrite where
  | Rw : rewrite_rec → rewrite

end

instance : Inhabited db := ⟨db.End_db⟩
instance : Inhabited fterm := ⟨fterm.Neutr⟩
instance : Inhabited dterm := ⟨dterm.Fv⟩

/- ---------------------------------------------------------------------- -/
/- Helper rules.                                                          -/
/- ---------------------------------------------------------------------- -/

/-- `with_flag (flag,b) f x`: set `flag := b` around `f x`, restoring it
    afterwards (including when `f` fails). -/
def with_flag {α β : Type} (flag : IO.Ref α) (b : α) (f : β → IO (Except String γ))
    (x : β) : IO (Except String γ) := do
  let fval ← flag.get
  flag.set b
  -- OCaml restores the flag on the exception path too (`with e -> …; raise e`);
  -- `finally` covers both that and the ordinary `Except` error return.
  try
    f x
  finally
    flag.set fval

/-- `RIGHT_BETA th`: beta-reduce the rhs of `th`. -/
def RIGHT_BETA (th : thm) : Except String thm :=
  match (do TRANS th (← BETA_CONV (← Equal.rhs (concl th))) : Except String thm) with
  | .ok r => .ok r
  | .error _ => failwith "RIGHT_BETA"

/-- `RIGHT_ETA thm`: eta-reduce the rhs of `thm`.  `ETA_CONV` needs its `pth`
    and the `t` variable, which Session supplies. -/
def RIGHT_ETA (etaPth : thm) (etaT : term) (th : thm) : Except String thm :=
  match (do TRANS th (← ETA_CONV etaPth etaT (← Equal.rhs (concl th))) : Except String thm) with
  | .ok r => .ok r
  | .error _ => failwith "RIGHT_ETA"

/-- `MK_comb th`: from `|- M = (a b)` produce `(|- a = a, |- b = b, mka)` where
    `mka (|- a = a') (|- b = b') = |- M = (a' b')`. -/
def MK_comb (th : thm) : Except String (thm × thm × (thm → thm → Except String thm)) := do
  let r ← Equal.rhs (concl th)
  let (rtr, rnd) ← dest_comb r
  let mka (th1 th2 : thm) : Except String thm := do TRANS th (← MK_COMB th1 th2)
  return (REFL rtr, REFL rnd, mka)

/-- `MK_abs th`: from `|- M = (\x. b)` produce `(x, |- b = b, mkl)` where
    `mkl (|- b = b') = |- M = (\x. b')`. -/
def MK_abs (th : thm) : Except String (term × thm × (thm → Except String thm)) := do
  let r ← Equal.rhs (concl th)
  let (bvar, body) ← dest_abs r
  return (bvar, REFL body, fun th1 => do TRANS th (← ABS bvar th1))

/-- `BODY_CONJUNCTS th`: strip leading `∀`s and split conjunctions. -/
partial def BODY_CONJUNCTS [HolBase] (th : thm) : List thm :=
  if is_forall (concl th) then
    match HolBase.B.SPEC_ALL th with
    | .ok th' => BODY_CONJUNCTS th'
    | .error _ => [th]
  else if is_conj (concl th) then
    match (do pure (← HolBase.B.CONJUNCT1 th, ← HolBase.B.CONJUNCT2 th) : Except String (thm × thm)) with
    | .ok (c1, c2) => BODY_CONJUNCTS c1 ++ BODY_CONJUNCTS c2
    | .error _ => [th]
  else [th]

/- ---------------------------------------------------------------------- -/
/- compute_rules.sml : building the theorem as we reduce.                 -/
/- ---------------------------------------------------------------------- -/

/-- `rhs_concl = rand o concl` (compute.ml 102). -/
def rhs_concl (th : thm) : Except String term := (rand o concl) th

/-- `refl_thm = REFL`. -/
def refl_thm (t : term) : thm := REFL t

/-- `trans_thm = TRANS`. -/
def trans_thm (th1 th2 : thm) : Except String thm := TRANS th1 th2

/-- `beta_thm = RIGHT_BETA`. -/
def beta_thm (th : thm) : Except String thm := RIGHT_BETA th

/-- `evaluate th = th`. -/
def evaluate (th : thm) : thm := th

/-- `try_eta thm = try RIGHT_ETA thm with _ -> thm`. -/
def try_eta (etaPth : thm) (etaT : term) (th : thm) : thm :=
  match RIGHT_ETA etaPth etaT th with | .ok r => r | .error _ => th

/-- The stack used by the reduction machine (`cbv_stack`):
    * a `Zrator` frame holds `mka` and the argument's `(thm, fterm)`;
    * a `Zrand` frame holds `mka`, the "skip" flag, and the function's pair;
    * a `Zabs` frame holds `mkl`. -/
abbrev cbv_stack :=
  stack ((thm → thm → Except String thm) × (thm × fterm))
        ((thm → thm → Except String thm) × Bool × (thm × fterm))
        (thm → Except String thm)

/-- Precondition: `f arg` is a closure corresponding to `b`.
    Given `(arg, (|- M = (a b), Stk))`, returns
    `(|- a = a, Zrator ((mka, (|- b = b, f arg)), Stk))`
    where `mka (|- a = a', |- b = b') = |- M = (a' b')`.
    (`f` is `IO` here because `mk_clos` reads the compset; `MK_comb` is still
    performed before `f arg`, as in the OCaml.) -/
def push_in_stk {α : Type} (f : α → IO (Except String fterm)) (arg : α)
    (thstk : thm × cbv_stack) : IO (Except String (thm × cbv_stack)) := do
  let (th, stk) := thstk
  match MK_comb th with
  | .error e => return .error e
  | .ok (tha, thb, mka) =>
    match ← f arg with
    | .error e => return .error e
    | .ok ft => return .ok (tha, .Zrator (mka, (thb, ft)) stk)

/-- As `push_in_stk`, but pushing a `Zrand` frame flagged as skipped
    (`C mka` swaps `mka`'s arguments). -/
def push_skip_stk {α : Type} (f : α → IO (Except String fterm)) (arg : α)
    (thstk : thm × cbv_stack) : IO (Except String (thm × cbv_stack)) := do
  let (th, stk) := thstk
  match MK_comb th with
  | .error e => return .error e
  | .ok (tha, thb, mka) =>
    match ← f arg with
    | .error e => return .error e
    | .ok ft => return .ok (tha, .Zrand (fun x y => mka y x, true, (thb, ft)) stk)

/-- Given `(|- M = (\x. b), Stk)`, returns `(|- b = b, Zabs (try_eta o mkl, Stk))`
    (compute.ml 127). -/
def push_lam_in_stk (etaPth : thm) (etaT : term) (thstk : thm × cbv_stack) :
    Except String (thm × cbv_stack) := do
  let (th, stk) := thstk
  let (_, thb, mkl) ← MK_abs th
  return (thb, .Zabs (try_eta etaPth etaT oEm mkl) stk)

/- Does conversions between
                             FUNIFY
   |- (c t_1 .. t_n x) = M    --->   |- (c t_1 .. t_n) = \x. M
                              <---
                            UNFUNIFY
  In UNFUNIFY, we must avoid choosing an x that appears free in t_1..t_n. -/

/-- `FUNIFY thm`. -/
def FUNIFY [HolBase] (ETA_AX : thm) (th : thm) : IO (Except String thm) :=
  ExceptT.run <| HolLight.tryWith (do
    let x ← liftExcept (do rand (← Equal.lhs (concl th)))
    HolLight.CONV_RULE (HolLight.RATOR_CONV (HolLight.RAND_CONV
      (HolLight.CHANGED_CONV (HolLight.PURE_REWRITE_CONV [ETA_AX]))))
      (← liftExcept (ABS x th)))
    (throw "FUNIFY")

/-- `UNFUNIFY thm`. -/
def UNFUNIFY (th : thm) : Except String thm :=
  match (do
    let (l, r) ← dest_eq (concl th)
    let (bv, _) ← dest_abs r
    let x ← variant (frees l) bv
    CONV_RULE (RAND_CONV (fun u => BETA_CONV u)) (← AP_THM th x)
    : Except String thm) with
  | .ok r => .ok r
  | .error _ => failwith "UNFUNIFY"

/-- `repeat_on_conj f thm`: iterate `f` to a fixpoint on each body conjunct. -/
def repeat_on_conj [HolBase] (f : thm → Except String thm) (th : thm) :
    Except String thm :=
  let rec iter (t : thm) (n : Nat) : thm :=
    match n with
    | 0 => t
    | n+1 => match f t with | .ok t' => iter t' n | .error _ => t
  end_itlistM (fun a b => HolBase.B.CONJ a b) ((BODY_CONJUNCTS th).map (fun t => iter t 1000))

/-- `lazyfy_thm = repeat_on_conj FUNIFY`. -/
def lazyfy_thm [HolBase] (ETA_AX : thm) (th : thm) : IO (Except String thm) := do
  -- FUNIFY is IO here (PURE_REWRITE_CONV), so iterate explicitly.
  let iter (t : thm) : IO thm := do
    let mut cur := t
    for _ in [0:1000] do
      match ← FUNIFY ETA_AX cur with
      | .ok t' => cur := t'
      | .error _ => break
    pure cur
  let parts ← (BODY_CONJUNCTS th).mapM iter
  return (end_itlistM (fun a b => HolBase.B.CONJ a b) parts)

/-- `strictify_thm = repeat_on_conj UNFUNIFY`. -/
def strictify_thm [HolBase] (th : thm) : Except String thm :=
  repeat_on_conj UNFUNIFY th

/-- Ensures a theorem is an equality. -/
def eq_intro [HolBase] (th : thm) : Except String thm :=
  if is_eq (concl th) then .ok th
  else if is_neg (concl th) then HolBase.B.EQF_INTRO th
  else HolBase.B.EQT_INTRO th

/-- Checking that a given thm is a reduction rule we can handle:
    `(c p1...pn) = rhs` with `p1...pn` either a const applied to patterns or a
    free variable.  (`IO` because the failure message prints the term.) -/
partial def check_arg_form (trm : term) :
    IO (Except String (List term × term × List pattern)) := do
  let rec chk (t : term) (stk : List pattern) (free : List term) :
      IO (Except String (List term × pattern)) := do
    if is_comb t then
      match dest_comb t with
      | .error e => return .error e
      | .ok (rtr, rnd) =>
        match ← chk rnd [] free with
        | .error e => return .error e
        | .ok (free', pat1) => chk rtr (pat1 :: stk) free'
    else if is_var t then
      if stk.isEmpty then
        let newi : Int := free.length
        match index t free with
        | .ok i => return .ok (free, .Pvar (newi - (i : Int) - 1))
        | .error _ => return .ok (t :: free, .Pvar newi)
      else
        match dest_var t with
        | .ok (n, _) =>
          return (failwith ("check_arg_form: " ++ n ++ " occurs as a variable on lhs"))
        | .error e => return .error e
    else if is_const t then
      return .ok (free, .Papp t stk.reverse)
    else
      let s ← HolCore.Printer.string_of_term trm
      return (failwith ("check_arg_form: lambda abstraction not allowed on lhs: `"
                        ++ s ++ "`"))
  match ← chk trm [] [] with
  | .error e => return .error e
  | .ok (fv, .Papp head args) => return .ok (fv.reverse, head, args)
  | .ok _ => return (failwith "check_arg_form: ill-formed lhs")

/- Invariant: the first arg of `App` never is an `App`. -/

/-- `appl (t, arg)`: apply `t` to `arg`, keeping the `App` invariant. -/
def appl : dterm × dterm → dterm
  | (.App a l1, arg) => .App a (arg :: l1)
  | (t, arg)         => .App t [arg]

/-- Type variable instantiation in `dterm`. Make it tail-recursive ? -/
partial def inst_type_dterm : List (hol_type × hol_type) × dterm → dterm
  | ([], v) => v
  | (tysub, v) =>
    let rec tyi_dt : dterm → dterm
      | .Cst c   => .Cst (inst tysub c)
      | .App h l => .App (tyi_dt h) (l.map tyi_dt)
      | .Abs v'  => .Abs (tyi_dt v')
      | v'       => v'
    tyi_dt v

/- ---------------------------------------------------------------------- -/
/- equation database                                                      -/
/- We should try to factorize the rules (cf discrimination nets)          -/
/- Rules are packed according to their head constant, and then sorted     -/
/- according to the width of their lhs.                                   -/
/- ---------------------------------------------------------------------- -/

/-- `add_in_db (n, cst, act, db)`.  The five cases are matched in the OCaml's
    order, which is significant. -/
partial def add_in_db : Int × term × action × db → db
  | (n, cst, act, .End_db) =>
      funpow n.toNat (fun a => db.Need_arg a) (.Try { hcst := cst, rws := act, tail := .End_db })
  | (0, cst, .Rewrite nrws, .Try { hcst := hcst, rws := .Rewrite rws, tail := tail }) =>
      if cst == hcst then .Try { hcst := hcst, rws := .Rewrite (nrws ++ rws), tail := tail }
      else .Try { hcst := hcst, rws := .Rewrite rws,
                  tail := add_in_db (0, cst, .Rewrite nrws, tail) }
  | (n, cst, act, .Try tr) =>
      .Try { tr with tail := add_in_db (n, cst, act, tr.tail) }
  | (0, cst, act, d) =>
      .Try { hcst := cst, rws := act, tail := d }
  | (n, cst, act, .Need_arg tail) =>
      .Need_arg (add_in_db (n - 1, cst, act, tail))

/-- `key_of (Rw {cst; lhs}) = (name, length lhs, cst)`. -/
def key_of : rewrite → Except String (String × Int × term)
  | .Rw r => do
      let (name, _) ← dest_const r.cst
      return (name, r.lhs.length, r.cst)

/-- `is_skip`: has the constant reached its `skip` arity? -/
def is_skip : thm × fterm → Bool
  | (_, .Const c) => match c.skip with
                     | some n => n <= c.args.length
                     | none => false
  | _ => false

/-- `partition_skip skip args`. -/
def partition_skip (skip : Option Int) (args : List (term × fterm)) :
    Except String (List (term × fterm) × List (term × fterm)) :=
  match skip with
  | some n =>
      let len : Int := args.length
      if n <= len then chop_list (len - n).toNat args
      else pure ([], args)
  | none => pure ([], args)

/-- `compset` — OCaml `Rws of (string, (db * int option) ref) Hashtbl.t`.  The
    hashtable becomes an association list in an `IO.Ref` (matching the style used
    in `Nets.lean`); the inner `IO.Ref`s keep `add_in_db_upd`/`set_skip_name`
    updating entries in place, as the OCaml refs do. -/
structure compset where
  rws : IO.Ref (List (String × IO.Ref (db × Option Int)))

/-- `empty_rws ()`. -/
def empty_rws : IO compset := do
  let r ← IO.mkRef ([] : List (String × IO.Ref (db × Option Int)))
  return { rws := r }

/-- `assoc_clause rws cst`: the entry for `cst`, created empty if absent. -/
def assoc_clause (cs : compset) (cst : String) : IO (IO.Ref (db × Option Int)) := do
  let l ← cs.rws.get
  match (assoc cst l : Except String (IO.Ref (db × Option Int))) with
  | .ok r => return r
  | .error _ => do
      let mt ← IO.mkRef (db.End_db, (none : Option Int))
      cs.rws.set ((cst, mt) :: l)
      return mt

/-- `add_in_db_upd rws (name, arity, hcst) act`. -/
def add_in_db_upd (cs : compset) (key : String × Int × term) (act : action) : IO Unit := do
  let (name, arity, hcst) := key
  let rl ← assoc_clause cs name
  let (d, sk) ← rl.get
  rl.set (add_in_db (arity, hcst, act, d), sk)

/-- `set_skip_name rws p sk`. -/
def set_skip_name (cs : compset) (p : String) (sk : Option Int) : IO Unit := do
  let rl ← assoc_clause cs p
  let (d, _) ← rl.get
  rl.set (d, sk)

/-- `scrub_const rws c`. -/
def scrub_const (cs : compset) (c : term) : IO (Except String Unit) := do
  match dest_const c with
  | .error e => return .error e
  | .ok (name, _) => do
      cs.rws.modify (fun l => l.filter (fun p => p.1 != name))
      return .ok ()

/-- The stack used by `from_term`. -/
abbrev ft_stack := stack (List term × term) dterm Unit

/- `from_term (rws, env, t)`: build the de Bruijn form of `t`.  Constants are
   registered in the compset as a side effect (as OCaml's `assoc_clause` does),
   so the entry a later `mk_clos` looks up already exists. -/
mutual

private partial def from_term_down (cs : compset) (env : List term) (t : term)
    (c : ft_stack) : IO (Except String dterm) := do
  match t with
  | .Var _ _ =>
      let dt : dterm := match index t env with
                        | .ok i => .Bv (i : Int)
                        | .error _ => .Fv
      from_term_up cs dt c
  | .Const name _ => do
      let _ ← assoc_clause cs name
      from_term_up cs (.Cst t) c
  | .Comb rtr rnd => from_term_down cs env rtr (.Zrator (env, rnd) c)
  | .Abs bvar body => from_term_down cs (bvar :: env) body (.Zabs () c)

private partial def from_term_up (cs : compset) (dt : dterm) (c : ft_stack) :
    IO (Except String dterm) := do
  match c with
  | .Ztop => return .ok dt
  | .Zrator (env, arg) c' => from_term_down cs env arg (.Zrand dt c')
  | .Zrand dr c' => from_term_up cs (appl (dr, dt)) c'
  | .Zabs _ c' => from_term_up cs (.Abs dt) c'

end

/-- `from_term (rws, env, t)`. -/
def from_term (cs : compset) (env : List term) (t : term) : IO (Except String dterm) :=
  from_term_down cs env t .Ztop

/- Note: if the list of free variables of the lhs was empty, we could evaluate
   (weak reduction) the rhs now.  This implies that the theorems must be added
   in dependencies order. -/

/-- `mk_rewrite rws eq_thm`. -/
def mk_rewrite [HolBase] (cs : compset) (eq_thm : thm) :
    IO (Except String rewrite) := do
  match dest_eq (concl eq_thm) with
  | .error e => return .error e
  | .ok (l, r) =>
    match ← check_arg_form l with
    | .error e => return .error e
    | .ok (fv, cst, pats) =>
      match itlistM (fun v th => HolBase.B.GEN v th) fv eq_thm with
      | .error e => return .error e
      | .ok gen_thm =>
        match ← from_term cs fv.reverse r with
        | .error e => return .error e
        | .ok rhsc =>
          return .ok (.Rw { cst := cst, lhs := pats, rhs := rhsc,
                            npv := fv.length, thm := gen_thm })

/-- `unsuitable th`: the rhs already matches the lhs. -/
def unsuitable (th : thm) : IO Bool := do
  match dest_eq (concl th) with
  | .error _ => return false
  | .ok (l, r) =>
    match ← (Drule.term_match [] l r : IO (Except String instantiation)) with
    | .ok _ => return true
    | .error _ => return false

/-- `enter_thm rws thm0`. -/
def enter_thm [HolBase] (cs : compset) (thm0 : thm) : IO (Except String Unit) := do
  match eq_intro thm0 with
  | .error e => return .error e
  | .ok th =>
    if ← unsuitable th then return .ok ()
    else
      match ← mk_rewrite cs th with
      | .error e => return .error e
      | .ok rw =>
        match key_of rw with
        | .error e => return .error e
        | .ok k => do add_in_db_upd cs k (.Rewrite [rw]); return .ok ()

/-- `add_thms lthm rws`. -/
def add_thms [HolBase] (lthm : List thm) (cs : compset) : IO (Except String Unit) := do
  for th in lthm do
    for c in BODY_CONJUNCTS th do
      match ← enter_thm cs c with
      | .error e => return .error e
      | .ok _ => pure ()
  return .ok ()

/-- `add_extern (cst, arity, fconv) rws`.  `fconv` is the plain conversion (see
    the note on `action.Conv`). -/
def add_extern (cst : term) (arity : Int) (fconv : ioconv) (cs : compset) :
    IO (Except String Unit) := do
  match dest_const cst with
  | .error e => return .error e
  | .ok (name, _) => do add_in_db_upd cs (name, arity, cst) (.Conv fconv); return .ok ()

/-- `new_rws ()`: a compset seeded with `REFL_CLAUSE`. -/
def new_rws [HolBase] (REFL_CLAUSE : thm) : IO (Except String compset) := do
  let cs ← empty_rws
  match ← add_thms [REFL_CLAUSE] cs with
  | .error e => return .error e
  | .ok _ => return .ok cs

/-- `from_list lthm`. -/
def from_list [HolBase] (REFL_CLAUSE : thm) (lthm : List thm) :
    IO (Except String compset) := do
  match ← new_rws REFL_CLAUSE with
  | .error e => return .error e
  | .ok cs =>
    match ← add_thms lthm cs with
    | .error e => return .error e
    | .ok _ => return .ok cs

/-- `scrub_thms lthm rws`. -/
def scrub_thms [HolBase] (lthm : List thm) (cs : compset) :
    IO (Except String Unit) := do
  match (do
    -- tmlist = map (concl o hd o BODY_CONJUNCTS) lthm (compute.ml 417)
    let tmlist ← lthm.mapM (concl oEm hd o BODY_CONJUNCTS)
    -- clist = map (fst o strip_comb o lhs o snd o strip_forall) tmlist
    -- (compute.ml 418)
    tmlist.mapM (Prod.fst o strip_comb oEm Equal.lhs o Prod.snd o strip_forall)
    : Except String (List term)) with
  | .error e => return .error e
  | .ok clist => do
    for c in clist do
      match ← scrub_const cs c with
      | .error e => return .error e
      | .ok _ => pure ()
    return .ok ()

/- ---------------------------------------------------------------------- -/
/- equations.sml : the first order matching functions.                    -/
/-                                                                        -/
/- We do not consider general non-linear patterns.  We could try          -/
/- (requires a more elaborate conversion algorithm, and it makes matching -/
/- and reduction mutually dependent).                                     -/
/- ---------------------------------------------------------------------- -/

/-- The bindings threaded through matching: the pattern-variable array (OCaml
    mutates it in place and returns the same array; each array is freshly
    allocated per rule attempt in `try_rwn`, so threading it functionally is
    observationally identical) and the type instantiation. -/
abbrev match_bds := Array (Option (term × fterm)) × List (hol_type × hol_type)

/-- `match_const (bds,tbds) pc c`. -/
def match_const (bt : match_bds) (pc c : term) : Except String match_bds := do
  let (bds, tbds) := bt
  let (name, ty) ← dest_const pc
  let (name', ty') ← dest_const c
  if name == name' then
    match type_match ty ty' tbds with
    | .ok r => .ok (bds, r)
    | .error _ => .error No_match
  else .error No_match

/-- Match pattern variable number var with term arg.
    We do not need to match types, because pattern variables appear as argument
    of a constant which has already been matched succesfully. -/
def match_var (bt : match_bds) (var : Int) (arg : term × fterm) :
    Except String match_bds :=
  let (bds, tbds) := bt
  match bds[var.toNat]? with
  | some (some (tm, _)) => if aconv tm arg.1 then .ok (bds, tbds) else .error No_match
  | some none => .ok (bds.set! var.toNat (some arg), tbds)
  | none => .error (Dead_code "match_var")

/- Tries to match a list of pattern to a list of arguments.  We assume that we
   already checked the lengths (probably a good short-cut).
   Returns a list of bindings that extend the ones given as
   argument (bds), or a No_match exception. -/
mutual

partial def match_list (bt : match_bds) : List pattern → List (term × fterm) →
    Except String match_bds
  | pat :: pats, arg :: args => do match_list (← match_solve bt pat arg) pats args
  | [], [] => .ok bt
  | _, _ => .error (Dead_code "match_list")

partial def match_solve (bt : match_bds) : pattern → (term × fterm) →
    Except String match_bds
  | .Pvar var, arg => match_var bt var arg
  | .Papp phead pargs, (_, .Const c) =>
      if pargs.length == c.args.length then
        do match_list (← match_const bt phead c.head) pargs c.args
      else .error No_match
  | _, _ => .error No_match

end

/-- `'a rule_inst` — a rule together with the instantiation that matched it. -/
structure rule_inst where
  rule : rewrite
  inst : match_bds

/-- `try_rwn ibds lt rwn`: try a sequence of rewrite rules.  No attempt to
    factorize patterns!  Only `No_match` is caught, as in the OCaml. -/
partial def try_rwn (ibds : List (hol_type × hol_type)) (lt : List (term × fterm)) :
    List rewrite → Except String rule_inst
  | [] => .error No_match
  | (.Rw r) :: rwn =>
      let env : Array (Option (term × fterm)) := Array.replicate r.npv.toNat none
      match match_list (env, ibds) r.lhs lt with
      | .ok i => .ok { rule := .Rw r, inst := i }
      | .error e => if e == No_match then try_rwn ibds lt rwn else .error e

/- ---------------------------------------------------------------------- -/
/- Instantiating the rule according to the output of the matching.        -/
/- ---------------------------------------------------------------------- -/

/-- `comb_ct cst arg`. -/
def comb_ct (cst : cst_rec) (arg : term × fterm) : Except String fterm :=
  match cst.rws with
  | .Need_arg tail =>
      .ok (.Const { head := cst.head, args := arg :: cst.args, rws := tail, skip := cst.skip })
  | .End_db =>
      .ok (.Const { head := cst.head, args := arg :: cst.args, rws := .End_db, skip := cst.skip })
  | .Try _ => .error (Dead_code "comb_ct: yet rules to try")

/-- `mk_clos (env, t)`.  Takes the compset because `Cst` no longer carries the
    rewrite cell (see the structural note in the file header): the entry is
    fetched by the constant's name, which is what OCaml's ref denotes. -/
def mk_clos (cs : compset) (env : List fterm) (t : dterm) : IO (Except String fterm) := do
  match t with
  | .Cst hc =>
      match dest_const hc with
      | .error e => return .error e
      | .ok (name, _) => do
          let rl ← assoc_clause cs name
          let (d, b) ← rl.get
          return .ok (.Const { head := hc, args := [], rws := d, skip := b })
  | .Bv i =>
      match env[i.toNat]? with
      | some f => return .ok f
      | none => return (failwith "mk_clos")
  | .Fv => return .ok .Neutr
  | _ => return .ok (.Clos { env := env, term := t })

/-- `inst_rw (th, monitoring, rule_inst)`.  It is probably this code that can be
    improved the most. -/
def inst_rw [HolBase] (cs : compset) (th : thm) (monitoring : Bool)
    (ri : rule_inst) : IO (Except String (thm × fterm)) := do
  match ri.rule with
  | .Rw r =>
    let (bds, tysub) := ri.inst
    let tirhs := inst_type_dterm (tysub, r.rhs)
    match INST_TYPE tysub r.thm with
    | .error e => return .error e
    | .ok tithm =>
      -- Array.fold_left inst_one_var (tithm, []) bds
      let mut spec_thm : thm := tithm
      let mut venv : List fterm := []
      for ob in bds do
        match ob with
        | some (tm, v) =>
            match HolBase.B.SPEC tm spec_thm with
            | .ok t => spec_thm := t; venv := v :: venv
            | .error e => return .error e
        | none => return .error (Dead_code "inst_rw")
      if monitoring then
        IO.println (← HolCore.Printer.string_of_term (concl spec_thm))
      match trans_thm th spec_thm with
      | .error e => return .error e
      | .ok tr =>
        match ← mk_clos cs venv tirhs with
        | .error e => return .error e
        | .ok c => return .ok (tr, c)

/-- The module-level mutable flags of `compute.ml` (`monitoring`, `stoppers`),
    supplied by `Session`. -/
structure ComputeFlags where
  monitoring : IO.Ref (Option (term → Bool))
  stoppers   : IO.Ref (Option (term → Bool))

/- ---------------------------------------------------------------------- -/
/- Reducing a constant.                                                   -/
/- ---------------------------------------------------------------------- -/

/-- `reduce_cst (th, cst)`: returns `(reduced?, (thm, fterm))`. -/
partial def reduce_cst [HolBase] (F : ComputeFlags) (cs : compset)
    (th : thm) (cst : cst_rec) : IO (Except String (Bool × (thm × fterm))) := do
  match cst.rws with
  | .Try { hcst := hcst, rws := .Rewrite rls, tail := tail } => do
      let stopped ← (do
        match ← F.stoppers.get with
        | none => pure false
        | some p => pure (p cst.head))
      let res ← (do
        if stopped then return (Except.error No_match : Except String (thm × fterm))
        match ← (Drule.term_match [] hcst cst.head : IO (Except String instantiation)) with
        | .error _ => return .error No_match
        | .ok (_, _, tytheta) =>
          match try_rwn tytheta cst.args rls with
          | .error e => return .error e
          | .ok rule_inst => do
            let mon ← (do match ← F.monitoring.get with
                          | none => pure false
                          | some f => pure (f cst.head))
            inst_rw cs th mon rule_inst)
      match res with
      | .ok insted => return .ok (true, insted)
      | .error e =>
        if e == No_match then
          reduce_cst F cs th { cst with rws := tail }
        else return .error e
  | .Try { hcst := _, rws := .Conv fconv, tail := tail } => do
      let res ← (do
        match rhs_concl th with
        | .error e => return (Except.error e : Except String (thm × fterm))
        | .ok r =>
          match ← fconv r with
          | .error e => return .error e
          | .ok thm0 =>
            -- extern_of_conv's body, inlined (see the note on `action.Conv`):
            -- (thm, mk_clos ([], from_term (rws, [], rhs (concl thm))))
            match ← (do
              match Equal.rhs (concl thm0) with
              | .error e => return (Except.error e : Except String fterm)
              | .ok rr =>
                match ← from_term cs [] rr with
                | .error e => return .error e
                | .ok dt => mk_clos cs [] dt) with
            | .error e => return .error e
            | .ok ft =>
              match trans_thm th thm0 with
              | .error e => return .error e
              | .ok tr => return .ok (tr, ft))
      match res with
      | .ok v => return .ok (true, v)
      | .error _ => reduce_cst F cs th { cst with rws := tail }
  | _ => return .ok (false, (th, .Const cst))

/- ---------------------------------------------------------------------- -/
/- computeLib.sml : the reduction machine.                                -/
/- ---------------------------------------------------------------------- -/

/-- `stack_out (th, stk)`: rebuild the theorem from the remaining context. -/
partial def stack_out : thm × cbv_stack → Except String thm
  | (th, .Ztop) => .ok th
  | (th, .Zrator (mka, (thb, _)) ctx) => do stack_out (← mka th thb, ctx)
  | (th, .Zrand (mka, _, (tha, _)) ctx) => do stack_out (← mka tha th, ctx)
  | (th, .Zabs mkl ctx) => do stack_out (← mkl th, ctx)

/-- `initial_state rws t`. -/
def initial_state (cs : compset) (t : term) :
    IO (Except String ((thm × fterm) × cbv_stack)) := do
  match ← from_term cs [] t with
  | .error e => return .error e
  | .ok dt =>
    match ← mk_clos cs [] dt with
    | .error e => return .error e
    | .ok cl => return .ok ((refl_thm t, cl), .Ztop)

/- [cbv_wk (rws,(th,cl),stk)] puts the closure cl (useful information about
   the rhs of th) in head normal form (weak reduction). It returns either
   a closure which term is an abstraction, in a context other than Zappl,
   a variable applied to strongly reduced arguments, or a constant
   applied to weakly reduced arguments which does not match any rewriting
   rule.

   - substitution is propagated through applications.
   - if the rhs is an abstraction and there is one arg on the stack, this means
     we found a beta redex.  `mka` rebuilds the application of the function to
     its argument, and `beta_thm` does the actual beta step.
   - for an applied constant, we look for a rewrite matching it.  If we found
     one, then we apply the instantiated rule, and go on.  Otherwise, we try to
     rebuild the thm.
   - for an already strongly normalized term or an unapplied abstraction, we try
     to rebuild the thm. -/
mutual

partial def cbv_wk [HolBase] (F : ComputeFlags) (cs : compset) :
    (thm × fterm) × cbv_stack → IO (Except String ((thm × fterm) × cbv_stack))
  | ((th, .Clos { env := env, term := .App a args }), stk) => do
      -- rev_itlist (push_in_stk (curry mk_clos env)) args (th, stk)
      let mut acc : thm × cbv_stack := (th, stk)
      for arg in args do
        match ← push_in_stk (fun t => mk_clos cs env t) arg acc with
        | .error e => return .error e
        | .ok a' => acc := a'
      match ← mk_clos cs env a with
      | .error e => return .error e
      | .ok cl => cbv_wk F cs ((acc.1, cl), acc.2)
  | ((th, .Clos { env := env, term := .Abs body }), .Zrator (mka, (thb, cl)) s') => do
      match (do beta_thm (← mka th thb) : Except String thm) with
      | .error e => return .error e
      | .ok bth =>
        match ← mk_clos cs (cl :: env) body with
        | .error e => return .error e
        | .ok cl' => cbv_wk F cs ((bth, cl'), s')
  | ((th, .Const cargs), stk) => do
      match ← reduce_cst F cs th cargs with
      | .error e => return .error e
      | .ok (reduced, clos) =>
        if reduced then cbv_wk F cs (clos, stk) else cbv_up F cs (clos, stk)
  | (clos, stk) => cbv_up F cs (clos, stk)

/- Tries to rebuild the thm, knowing that the closure has been weakly
   normalized, until it finds term still to reduce, or if a strong reduction
   may be required.
    - if we are done with a Rator, we start reducing the Rand
    - if we are done with the Rand of a const, we rebuild the application
      and look if it created a redex
    - an application to a NEUTR can be rebuilt only if the argument has been
      strongly reduced, which we know for sure only if itself is a NEUTR. -/
partial def cbv_up [HolBase] (F : ComputeFlags) (cs : compset) :
    (thm × fterm) × cbv_stack → IO (Except String ((thm × fterm) × cbv_stack))
  | (hcl, .Zrator (mka, clos) ctx) => do
      let new_state := (clos, stack.Zrand (mka, false, hcl) ctx)
      if is_skip hcl then cbv_up F cs new_state else cbv_wk F cs new_state
  | ((thb, v), .Zrand (mka, false, (th, .Const cargs)) stk) => do
      match (do
        let m ← mka th thb
        let r ← rhs_concl thb
        let c ← comb_ct cargs (r, v)
        pure (m, c) : Except String (thm × fterm)) with
      | .error e => return .error e
      | .ok mc => cbv_wk F cs (mc, stk)
  | ((thb, .Neutr), .Zrand (mka, false, (th, .Neutr)) stk) => do
      match mka th thb with
      | .error e => return .error e
      | .ok m => cbv_up F cs ((m, .Neutr), stk)
  | (clos, stk) => return .ok (clos, stk)

end

/- [strong] continues the reduction of a term in head normal form under
   abstractions, and in the arguments of non reduced constant.
   precondition: the closure should be the output of cbv_wk -/
mutual

partial def strong [HolBase] (F : ComputeFlags) (cs : compset)
    (etaPth : thm) (etaT : term) :
    (thm × fterm) × cbv_stack → IO (Except String thm)
  | ((th, .Clos { env := env, term := .Abs t }), stk) => do
      match push_lam_in_stk etaPth etaT (th, stk) with
      | .error e => return .error e
      | .ok (thb, stk') =>
        match ← mk_clos cs (fterm.Neutr :: env) t with
        | .error e => return .error e
        | .ok cl =>
          match ← cbv_wk F cs ((thb, cl), stk') with
          | .error e => return .error e
          | .ok st => strong F cs etaPth etaT st
  | ((_, .Clos _), _) => return .error (Dead_code "strong")
  | ((th, .Const c), stk) => do
      match partition_skip c.skip c.args with
      | .error e => return .error e
      | .ok (argssk, argsrd) => do
        -- rev_itlist (push_skip_stk snd) argssk (th, stk)
        let mut acc : thm × cbv_stack := (th, stk)
        for a in argssk do
          match ← push_skip_stk (fun p => pure (.ok p.2)) a acc with
          | .error e => return .error e
          | .ok a' => acc := a'
        -- rev_itlist (push_in_stk snd) argsrd (th', stk')
        for a in argsrd do
          match ← push_in_stk (fun p => pure (.ok p.2)) a acc with
          | .error e => return .error e
          | .ok a' => acc := a'
        strong_up F cs etaPth etaT acc
  | ((th, .Neutr), stk) => strong_up F cs etaPth etaT (th, stk)

partial def strong_up [HolBase] (F : ComputeFlags) (cs : compset)
    (etaPth : thm) (etaT : term) :
    thm × cbv_stack → IO (Except String thm)
  | (th, .Ztop) => return .ok th
  | (th, .Zrand (mka, false, (tha, .Neutr)) ctx) => do
      match mka tha th with
      | .error e => return .error e
      | .ok m =>
        match ← cbv_wk F cs ((m, .Neutr), ctx) with
        | .error e => return .error e
        | .ok st => strong F cs etaPth etaT st
  | (_, .Zrand (_, false, _) _) => return .error (Dead_code "strong_up")
  | (th, .Zrator (mka, clos) ctx) => do
      match ← cbv_wk F cs (clos, .Zrand (mka, true, (th, .Neutr)) ctx) with
      | .error e => return .error e
      | .ok st => strong F cs etaPth etaT st
  | (th, .Zrand (mka, true, (tha, _)) ctx) => do
      match mka tha th with
      | .error e => return .error e
      | .ok m => strong_up F cs etaPth etaT (m, ctx)
  | (th, .Zabs mkl ctx) => do
      match mkl th with
      | .error e => return .error e
      | .ok m => strong_up F cs etaPth etaT (m, ctx)

end

/-- [CBV_CONV rws t] is a conversion that does the full normalization of t,
    using rewrites rws. -/
def CBV_CONV [HolBase] (F : ComputeFlags) (etaPth : thm) (etaT : term)
    (cs : compset) (t : term) : IO (Except String thm) := do
  match ← initial_state cs t with
  | .error e => return .error e
  | .ok st0 =>
    match ← cbv_wk F cs st0 with
    | .error e => return .error e
    | .ok st1 =>
      match ← strong F cs etaPth etaT st1 with
      | .error e => return .error e
      | .ok th => return .ok (evaluate th)

/-- `WEAK_CBV_CONV` is the same as `CBV_CONV` except that it does not reduce
    under abstractions, and reduce weakly the arguments of constants.
    Reduction whenever we reach a state where a strong reduction is needed. -/
def WEAK_CBV_CONV [HolBase] (F : ComputeFlags) (cs : compset) (t : term) :
    IO (Except String thm) := do
  match ← initial_state cs t with
  | .error e => return .error e
  | .ok st0 =>
    match ← cbv_wk F cs st0 with
    | .error e => return .error e
    | .ok ((th, _), stk) =>
      match stack_out (th, stk) with
      | .error e => return .error e
      | .ok r => return .ok (evaluate r)

/- ---------------------------------------------------------------------- -/
/- Support for analysis of compsets                                       -/
/- ---------------------------------------------------------------------- -/

/-- `get_actions` of `rws_of`: the `(hcst, action)` pairs of a database. -/
private partial def get_actions_hcst : db → List (term × action)
  | .End_db => []
  | .Need_arg db' => get_actions_hcst db'
  | .Try tr => (tr.hcst, tr.rws) :: get_actions_hcst tr.tail

/-- `get_actions` of `deplist`: the actions of a database. -/
private partial def get_actions_act : db → List action
  | .End_db => []
  | .Need_arg db' => get_actions_act db'
  | .Try tr => tr.rws :: get_actions_act tr.tail

/-- `rws_of rws`: the rewrite theorems of each database node. -/
def rws_of (cs : compset) : IO (List (term × List thm)) := do
  let l ← cs.rws.get
  let mut dblist : List db := []
  for (_, rl) in l do
    let (d, _) ← rl.get
    dblist := d :: dblist
  let actionlist := (dblist.map get_actions_hcst).flatten
  let dest : rewrite → thm | .Rw r => r.thm
  let dest_action : term × action → term × List thm
    | (hcst, .Rewrite rws) => (hcst, rws.map dest)
    | (hcst, .Conv _) => (hcst, [])
  return (actionlist.map dest_action)

/-- `transform` — what is attached to a compset entry. -/
inductive transform where
  | Conversion : ioconv → transform
  | Rrules : List thm → transform

/- Compute the "attachments" for each element of the compset.  Fortunately, it
   seems that the insertion of an attachment into a compset also makes
   insertions for the constants mentioned in the rhs of the rewrite.  Otherwise,
   one would have to do a transitive closure sort of construction to make all
   the dependencies explicit. -/

/- re-exporting types from clauses -/

/-- `deplist rws` (exported as `listItems`). -/
def deplist (cs : compset) : IO (List (String × List transform)) := do
  let l ← cs.rws.get
  let mut dblist : List (String × db) := []
  for (s, rl) in l do
    let (d, _) ← rl.get
    dblist := (s, d) :: dblist
  let actionlist := dblist.map (fun (s, d) => (s, get_actions_act d))
  let dest : rewrite → thm | .Rw r => r.thm
  let dest_action : action → transform
    | .Rewrite rws => .Rrules (rws.map dest)
    | .Conv ecnv => .Conversion ecnv
  return (actionlist.map (fun (s, act) => (s, act.map dest_action)))

/- ---------------------------------------------------------------------- -/
/- Adding an arbitrary conv                                               -/
/- ---------------------------------------------------------------------- -/

/-- `extern_of_conv rws conv tm`.  Kept for reference: `reduce_cst` performs this
    step itself, since `action.Conv` stores the plain conversion (see the note
    there). -/
def extern_of_conv (cs : compset) (conv : ioconv) (tm : term) :
    IO (Except String (thm × fterm)) := do
  match ← conv tm with
  | .error e => return .error e
  | .ok th =>
    match Equal.rhs (concl th) with
    | .error e => return .error e
    | .ok r =>
      match ← from_term cs [] r with
      | .error e => return .error e
      | .ok dt =>
        match ← mk_clos cs [] dt with
        | .error e => return .error e
        | .ok cl => return .ok (th, cl)

/-- `add_conv (cst, arity, conv) rws`. -/
def add_conv (cst : term) (arity : Int) (conv : ioconv) (cs : compset) :
    IO (Except String Unit) :=
  add_extern cst arity conv cs

/-- `set_skip compset c opt`. -/
def set_skip (cs : compset) (c : term) (opt : Option Int) : IO (Except String Unit) := do
  match dest_const c with
  | .error _ => return (failwith "set_skip")
  | .ok (name, _) => do set_skip_name cs name opt; return .ok ()

/- ---------------------------------------------------------------------- -/
/- Support for a global compset.                                          -/
/- ---------------------------------------------------------------------- -/

/-- The boolean reductions seeded into `bool_compset` (`bool_redns`). -/
def bool_redns [HolBase] (ETA_AX : thm)
    (LET_DEF COND_CLAUSES COND_ID NOT_CLAUSES
     AND_CLAUSES OR_CLAUSES IMP_CLAUSES EQ_CLAUSES : thm) :
    IO (Except String (List thm)) := do
  match strictify_thm LET_DEF with
  | .error e => return .error e
  | .ok s => do
    let mut acc : List thm := []
    for th in [COND_CLAUSES, COND_ID, NOT_CLAUSES,
               AND_CLAUSES, OR_CLAUSES, IMP_CLAUSES, EQ_CLAUSES] do
      match ← lazyfy_thm ETA_AX th with
      | .error e => return .error e
      | .ok l => acc := acc ++ [l]
    return .ok (s :: acc)

/-- `bool_compset ()`.  `COND` is registered with `set_skip … None`; invoke
    `set_skip` again with the last parameter `Some 1` to stop `CBV_CONV` looking
    at conditionals' branches before the guard is fully true or false. -/
def bool_compset [HolBase] (ETA_AX REFL_CLAUSE : thm)
    (LET_DEF COND_CLAUSES COND_ID NOT_CLAUSES
     AND_CLAUSES OR_CLAUSES IMP_CLAUSES EQ_CLAUSES : thm)
    (condTm : IO term) : IO (Except String compset) := do
  -- compute.ml parses the `COND` quotation on each call; `condTm` does too.
  match ← bool_redns ETA_AX LET_DEF COND_CLAUSES COND_ID NOT_CLAUSES
                     AND_CLAUSES OR_CLAUSES IMP_CLAUSES EQ_CLAUSES with
  | .error e => return .error e
  | .ok redns =>
    match ← from_list REFL_CLAUSE redns with
    | .error e => return .error e
    | .ok base =>
      match ← set_skip base (← condTm) none with
      | .error e => return .error e
      | .ok _ => return .ok base

/-- `same_const c1 c2`. -/
def same_const (c1 c2 : term) : Bool :=
  match dest_const c1, dest_const c2 with
  | .ok (n1, _), .ok (n2, _) => n1 == n2
  | _, _ => false

/-- `OR clist`: does the term match any constant in `clist`? -/
def OR : List term → term → Bool
  | [] => fun _ => false
  | [x] => same_const x
  | h :: t => fun x => same_const h x || OR t x

/-- `basic_compset ()`.  Rewrite rules that cause the "lambda abstraction not
    allowed in lhs" error are removed, the basic conversions are registered, and
    `let_CONV` is attached to `LET`.  `letConv` and the `LET` constant are passed
    in because `let_CONV` lives in the `pair.ml` layer. -/
def basic_compset [HolBase] (ETA_AX REFL_CLAUSE : thm)
    (SELECT_REFL FORALL_SIMP EXISTS_SIMP : thm)
    (letTm : IO term) (letConv : ioconv) (condTm : IO term) :
    IO (Except String compset) := do
  let basic_rws0 ← Simp.basic_rewrites
  -- Remove rewrite rules that cause the "lambda abstraction not allowed in
  -- lhs" error.
  match (do
    let a ← HolBase.B.SPEC_ALL SELECT_REFL
    let b ← HolBase.B.SPEC_ALL FORALL_SIMP
    let c ← HolBase.B.SPEC_ALL EXISTS_SIMP
    pure [a, b, c] : Except String (List thm)) with
  | .error e => return .error e
  | .ok lhs_lambda_rules =>
    let basic_rws := basic_rws0.filter (fun th => !(mem th lhs_lambda_rules))
    let mut lazies : List thm := []
    for th in basic_rws do
      match ← lazyfy_thm ETA_AX th with
      | .error e => return .error e
      | .ok l => lazies := lazies ++ [l]
    match ← from_list REFL_CLAUSE lazies with
    | .error e => return .error e
    | .ok cs => do
      let convs ← Simp.basic_convs
      for (_, (pat, the_conv)) in convs do
        let (cst, args) := strip_comb pat
        match ← add_conv cst args.length the_conv cs with
        | .error e => return .error e
        | .ok _ => pure ()
      match ← add_conv (← letTm) 2 letConv cs with
      | .error e => return .error e
      | .ok _ =>
        -- Invoke set_skip again with last parameter set to Some 1 to stop
        -- CBV_CONV looking at conditionals' branches before the guard is fully
        -- true or false
        match ← set_skip cs (← condTm) none with
        | .error e => return .error e
        | .ok _ => return .ok cs

end HolMath.Compute
