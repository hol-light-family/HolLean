/- File: TheCops.lean
Proof-producing HOL Light implementations of leanCoP and nanoCoP (`thecops.ml`).

  (c) Copyright, Michael Faerber 2018
  (c) Cezary Kaliszyk 2014

Lean4 translation by Chris Walton 2026.

All mutable state (the leanCoP/nanoCoP databases, the `Substarray` trail, the
fresh-variable counters, verbosity) lives in `Session.lean`.  Lazy streams
(`Strom`) are modelled as `Unit → IO (Option α)` thunks. -/

import HolCore.Bool
import HolCore.Equal
import HolCore.Basics
import HolCore.Meson
import HolCore.FirstOrder
import HolCore.Metis

open HolCore.Kernel HolCore.Basics HolCore.Lib HolCore.Bool HolCore.Equal HolCore.Meson
open HolCore.Tactics HolCore.FirstOrder

namespace HolCore.TheCops

set_option maxRecDepth 8000

/- `copverb` is `HolCore.FirstOrder.copverb` (firstorder.ml 13), the one
   flag OCaml's thecops.ml reads too. -/
open HolCore.FirstOrder (copverb)

/- ---------------------------------------------------------------------- -/
/- Strom: lazy streams (`thecops.ml`: strom.ml).                          -/
/- ---------------------------------------------------------------------- -/

/- OCaml `'a strom = unit -> 'a` raising `End_of_strom`.  We model a stream as
   an effectful thunk `Unit → IO (Option α)`, where `none` is `End_of_strom`.
   `cons`/`append`/`cache`/`cut` use one-shot mutable flags via `IO.Ref`,
   exactly as in OCaml. -/

abbrev Strom (α : Type) := Unit → IO (Option α)

namespace Strom

def nil : Strom α := fun _ => pure none

/-- `cons x l`: yield `x` once, then delegate to `l`.  OCaml allocates the
    one-shot `past` flag when the stream is BUILT (closure capture), so this
    returns `IO (Strom α)`. -/
def cons (x : α) (l : Strom α) : IO (Strom α) := do
  let past ← IO.mkRef false
  return (fun _ => do
    if ← past.get then l ()
    else do past.set true; pure (some x))

def append (xs ys : Strom α) : IO (Strom α) := do
  let past ← IO.mkRef false
  return (fun _ => do
    if ← past.get then ys ()
    else match ← xs () with
         | some x => pure (some x)
         | none => do past.set true; ys ())

def ofList (l : List α) : IO (Strom α) := do
  let r ← IO.mkRef l
  return (fun _ => do
    match ← r.get with
    | [] => pure none
    | x :: xs => do r.set xs; pure (some x))

partial def toList (l : Strom α) : IO (List α) := do
  match ← l () with
  | some x => do return x :: (← toList l)
  | none => return []

partial def iter (f : α → IO Unit) (l : Strom α) : IO Unit := do
  match ← l () with
  | some x => do f x; iter f l
  | none => return ()

def map (f : α → β) (l : Strom α) : Strom β := fun _ => do
  match ← l () with | some x => pure (some (f x)) | none => pure none

def mapiIO (f : Int → α → β) (l : Strom α) : IO (Strom β) := do
  let i ← IO.mkRef (0 : Int)
  return (fun _ => do
    match ← l () with
    | some x => do let h ← i.get; i.set (h + 1); pure (some (f h x))
    | none => pure none)

def takeIO (n : Int) (l : Strom α) : IO (Strom α) := do
  let i ← IO.mkRef n
  return (fun _ => do
    if (← i.get) = 0 then pure none
    else do i.modify (· - 1); l ())

def takeWhile (p : α → Bool) (l : Strom α) : Strom α := fun _ => do
  match ← l () with
  | some x => if p x then pure (some x) else pure none
  | none => pure none

partial def filter (p : α → Bool) (l : Strom α) : Strom α := fun _ => do
  match ← l () with
  | some x => if p x then pure (some x) else filter p l ()
  | none => pure none

partial def filterMap (f : α → IO (Option β)) (l : Strom α) : Strom β := fun _ => do
  match ← l () with
  | some x => (match ← f x with | some y => pure (some y) | none => filterMap f l ())
  | none => pure none

/-- `concat ls`: flatten a stream of streams (OCaml uses a `last` ref). -/
partial def concatLoop (last : IO.Ref (Strom α)) (ls : Strom (Strom α)) (u : Unit) :
    IO (Option α) := do
  match ← (← last.get) () with
  | some x => pure (some x)
  | none => match ← ls () with
            | some l => do last.set l; concatLoop last ls u
            | none => pure none
def concat (ls : Strom (Strom α)) : IO (Strom α) := do
  let last ← IO.mkRef (nil : Strom α)
  return (concatLoop last ls)

partial def concatMapLoop (last : IO.Ref (Strom β)) (f : α → Strom β) (l : Strom α) (u : Unit) :
    IO (Option β) := do
  match ← (← last.get) () with
  | some x => pure (some x)
  | none => match ← l () with
            | some a => do last.set (f a); concatMapLoop last f l u
            | none => pure none
def concatMap (f : α → Strom β) (l : Strom α) : IO (Strom β) := do
  let last ← IO.mkRef (nil : Strom β)
  return (concatMapLoop last f l)

/-- `concatMapM f l`: like `concatMap` but `f : α → IO (Strom β)` builds each
    sub-stream with IO (applied lazily when the previous is exhausted).  This is
    the faithful model of OCaml `concat_map` when `f` performs effects (the CoP
    search's `prove_clause`, which returns a stream value). -/
partial def concatMapMLoop (last : IO.Ref (Strom β)) (f : α → IO (Strom β)) (l : Strom α)
    (u : Unit) : IO (Option β) := do
  match ← (← last.get) () with
  | some x => pure (some x)
  | none => match ← l () with
            | some a => do last.set (← f a); concatMapMLoop last f l u
            | none => pure none
def concatMapM (f : α → IO (Strom β)) (l : Strom α) : IO (Strom β) := do
  let last ← IO.mkRef (nil : Strom β)
  return (concatMapMLoop last f l)

def nextOpt (l : Strom α) : IO (Option α) := l ()

/-- `cache f`: run `f ()` at most once, then serve from the built stream. -/
def cacheIO (f : Unit → IO (Strom α)) : IO (Strom α) := do
  let result ← IO.mkRef (none : Option (Strom α))
  return (fun _ => do
    match ← result.get with
    | none => do let l ← f (); result.set (some l); l ()
    | some l => l ())

/-- `cut xs ys`: yield the FIRST element of `xs` (committing/cutting the rest),
    else fall through to `ys` (OCaml uses `cut`/`past` refs). -/
def cut (xs ys : Strom α) : IO (Strom α) := do
  let cutR ← IO.mkRef false
  let past ← IO.mkRef false
  return (fun _ => do
    if ← past.get then ys ()
    else if ← cutR.get then pure none
    else match ← xs () with
         | some x => do cutR.set true; pure (some x)
         | none => do past.set true; ys ())

def integersFrom (n : Int) : IO (Strom Int) := do
  let i ← IO.mkRef n
  return (fun _ => do let h ← i.get; i.set (h + 1); pure (some h))

end Strom

/- ---------------------------------------------------------------------- -/
/- Fol_term: helpers on the FOL shadow terms (`thecops.ml`: term.ml).     -/
/- ---------------------------------------------------------------------- -/

/- Uses the Meson/FirstOrder `fol_term` (`Fvar`/`Fnapp`) and `fol_atom`. -/
namespace Fol_term

open HolCore.Meson (fol_term fol_atom)

def var (v : Int) : fol_term := .Fvar v

/-- `negate_lit (i,l) = (-i, l)`. -/
def negate_lit (l : fol_atom) : fol_atom := (-l.1, l.2)

partial def term_max_var (acc : Int) : fol_term → Int
  | .Fvar x => max acc x
  | .Fnapp _ l => l.foldl term_max_var acc
def lit_max_var (acc : Int) (a : fol_atom) : Int := a.2.foldl term_max_var acc

partial def map_term_vars (f : Int → fol_term) : fol_term → fol_term
  | .Fvar v => f v
  | .Fnapp p t => .Fnapp p (t.map (map_term_vars f))
def map_lit_vars (f : Int → fol_term) (a : fol_atom) : fol_atom :=
  (a.1, a.2.map (map_term_vars f))

def map_term (fv : Int → β) (fa : fol_atom → β) : fol_term → β
  | .Fvar v => fv v
  | .Fnapp p a => fa (p, a)

partial def term_ground : fol_term → Bool
  | .Fvar _ => false
  | .Fnapp _ a => a.all term_ground
def lit_ground (a : fol_atom) : Bool := a.2.all term_ground

end Fol_term

/- ---------------------------------------------------------------------- -/
/- Print: string rendering of FOL terms/literals                          -/
/- (`thecops.ml`: print.ml).                                              -/
/- ---------------------------------------------------------------------- -/

/- print.ml: the formatter printers used by the `copverb` traces.  OCaml's
   `pp_*` functions print on a formatter; here they build a `Fmt` action, in
   IO because `hol_of_const` reads the stores. -/
namespace Print

open HolCore.Meson (fol_term fol_atom FolStores)
open HolCore.System

/-- `pp_interleave sep fn` (print.ml). -/
def pp_interleave (sep : Fmt Unit) : List (Fmt Unit) → Fmt Unit
  | [] => pure ()
  | [x] => x
  | x :: xs => do x; sep; pp_interleave sep xs

/-- `pp_iter sep`. -/
def pp_iter (sep : String) (xs : List (Fmt Unit)) : Fmt Unit :=
  pp_interleave (Fmt.printString sep) xs

/-- `pp_iter_sp sep`: `' '`, `sep`, then a space break, between elements. -/
def pp_iter_sp (sep : String) (xs : List (Fmt Unit)) : Fmt Unit :=
  pp_interleave (do Fmt.printString " "; Fmt.printString sep; Fmt.printSpace) xs

def pp_enclose (start stop : String) (x : Fmt Unit) : Fmt Unit := do
  Fmt.printString start; x; Fmt.printString stop

def pp_enclose_cut (start stop : String) (x : Fmt Unit) : Fmt Unit :=
  pp_enclose start stop (do x; Fmt.printBreak 0 0)

def pp_enum (sep start stop : String) (xs : List (Fmt Unit)) : Fmt Unit :=
  pp_enclose start stop (pp_iter sep xs)

def pp_with_box (i : Int) (x : Fmt Unit) : Fmt Unit := do
  Fmt.openBox i; x; Fmt.closeBox

/-- `pp_print_var`: `A`..`Z`, then a number for indices over 25. -/
def pp_print_var (i : Int) : Fmt Unit := do
  Fmt.printString (String.singleton (Char.ofNat (65 + (i % 26).toNat)))
  if i > 25 then Fmt.printString (toString (i / 26))

/-- A constant code's term (`Meson.hol_of_const`), printed. -/
private def pp_const (S : FolStores) (i : Int) : IO (Fmt Unit) := do
  match ← Meson.hol_of_const S i with
  | .ok tm => HolCore.Printer.pp_print_term tm
  | .error e => throw (IO.userError e)

partial def pp_print_fterm (S : FolStores) : fol_term → IO (Fmt Unit)
  | .Fvar i => pure (pp_print_var i)
  | .Fnapp i l => do
    let hd ← pp_const S i
    let args ← l.mapM (pp_print_fterm S)
    pure (do hd; if !l.isEmpty then pp_enum "," "(" ")" args)

def pp_print_lit (S : FolStores) (l : fol_atom) : IO (Fmt Unit) := do
  let (i, args) := l
  let hd ← pp_const S i.natAbs
  let as ← args.mapM (pp_print_fterm S)
  pure (do
    if i < 0 then Fmt.printString "~"
    hd
    if !args.isEmpty then pp_enum "," "(" ")" as)

/-- `print_to_string` of a printer built in IO. -/
def render (f : IO (Fmt Unit)) : IO String := do
  return Fmt.run (← HolCore.Printer.get_margin) (← f)

def string_of_fterm (S : FolStores) (t : fol_term) : IO String := render (pp_print_fterm S t)
def string_of_lit (S : FolStores) (l : fol_atom) : IO String := render (pp_print_lit S l)
def string_of_lits (S : FolStores) (ls : List fol_atom) : IO String :=
  render (do pure (pp_iter ", " (← ls.mapM (pp_print_lit S))))

end Print

/- ---------------------------------------------------------------------- -/
/- Cop: iterative-deepening strategy + search options                     -/
/- (`thecops.ml`: cop.ml).                                                -/
/- ---------------------------------------------------------------------- -/
namespace Cop

/-- Search options (leanCoP/nanoCoP flags), OCaml record `search_opts`. -/
structure search_opts where
  cut1 : Bool
  cut2 : Bool
  cut3 : Bool
  comp : Int
  improved_lemmas : Bool
  improved_regularity : Bool
  add_eq_symmetry : Bool

/-- The default options (all cuts on, `comp = 7`, improvements + eq symmetry on). -/
def search_opts_default : search_opts :=
  { cut1 := true, cut2 := true, cut3 := true, comp := 7,
    improved_lemmas := true, improved_regularity := true, add_eq_symmetry := true }

/-- `deepen f i`: run `f` at increasing depths until it succeeds. -/
partial def deepen (f : Int → IO (Option α)) (i : Int) : IO α := do
  match ← f i with | some x => pure x | none => deepen f (i + 1)

/-- `deepen_to n f i`: bounded iterative deepening up to `n`. -/
partial def deepen_to (n : Int) (f : Int → IO (Option α)) (i : Int) : IO (Option α) := do
  if i > n then pure none
  else match ← f i with | none => deepen_to n f (i + 1) | s => pure s

/-- `strategy opt f`: try the cut-restricted search up to `comp`, else fall back
    to full (cut-free) unbounded deepening. -/
def strategy (opt : search_opts) (f : search_opts → Int → IO (Option α)) : IO α := do
  if opt.cut1 || opt.cut2 || opt.cut3 then
    match ← deepen_to opt.comp (f opt) 0 with
    | none => deepen (f { opt with cut1 := false, cut2 := false, cut3 := false }) 0
    | some prf => pure prf
  else deepen (f opt) 0

end Cop

/- ---------------------------------------------------------------------- -/
/- Hashek: the `#` marker constant + goal-marking tactics (`thecops.ml`:  -/
/- hashek.ml).                                                            -/
/- ---------------------------------------------------------------------- -/

/- `hashek = T`.  The theorems are proved once (Session); the `MARK_*` tactics
   reshape the goal so the CoP search sees the `hashek` marker literal.  The
   OCaml `assert`s that check goal shape are sanity checks; we translate them as
   error-returning guards where cheap, else omit (they never fire on well-formed
   goals). -/
namespace Hashek

/-- The Hashek theorems + marker term, proved once in `Session`. -/
structure HashekThms where
  hashek_def  : thm                    -- |- hashek = T
  hashek_tm   : term                   -- `hashek`
  hashek_thm  : thm                    -- |- hashek
  hashek_prop : thm                    -- |- ((x/\hashek) ==> (y/\hashek)) ==> (x ==> y)
  hashek_eq   : thm                    -- |- ~hashek <=> F
  /-- `MARK_ASSUMS`'s own `hashek` (thecops.ml 43 parses it once more). -/
  mark_tm     : term
  deriving Inhabited

/-- `MARK_ASSUMS = RULE_ASSUM_TAC (DISCH `hashek`)`. -/
def MARK_ASSUMS (B : BoolThms) (H : HashekThms) : tactic :=
  Tactics.RULE_ASSUM_TAC B (fun th => pure (B.DISCH H.mark_tm th))

/-- `MARK_CONCL label`: move the `label` assumption to the conclusion, rewrite
    `~t ==> F <=> t`, gather remaining assumptions into one conjunction, apply
    `hashek_prop`, split it back into assumptions, and refute.  `notTFimp` is the
    `TAUT `!t. (~t ==> F <=> t)`` theorem, which thecops.ml proves each time
    `MARK_CONCL label` is built; the caller supplies it. -/
def MARK_CONCL (B : BoolThms) (H : HashekThms) (notTFimp : thm)
    (refuteThen : thm_tactic → tactic) (label : String) : tactic :=
  let assumeTac : thm_tactic := fun th => Tactics.ASSUME_TAC B th
  Tactics.EVERY B [
    Tactics.USE_THEN label (fun th => Tactics.UNDISCH_TAC B (concl th)),
    (fun g => do
      -- assert (is_imp (snd g));
      if !Basics.is_imp g.2 then return .error "Assert_failure"
      -- the first part of the implication *may* be a negation,
      -- but does not necessarily have to be
      -- assert (snd (dest_imp (snd g)) = `F`);
      match ← HolCore.Parser.parse_term "F" with
      | .error e => return .error e
      | .ok f =>
        match Basics.dest_imp g.2 with
        | .ok (_, c) => if c == f then Tactics.ALL_TAC g else return .error "Assert_failure"
        | .error e => return .error e),
    Simp.REWRITE_TAC B [notTFimp],
    Tactics.POP_ASSUM_LIST (fun l =>
      Tactics.ASSUME_TAC B (if l.isEmpty then B.TRUTH
                            else match end_itlistM (fun a b => B.CONJ a b) l with
                                 | .ok c => c | .error _ => B.TRUTH)),
    -- assert (length (fst g) = 1);
    (fun g => if g.1.length == 1 then Tactics.ALL_TAC g else return .error "Assert_failure"),
    (fun (asl, w) =>
      (Tactics.MAP_EVERY B (fun (p : String × thm) => Tactics.UNDISCH_TAC B (concl p.2)) asl (asl, w)
       : IO (Except String goalstate))),
    Tactics.MATCH_MP_TAC B H.hashek_prop,
    Tactics.DISCH_THEN B (fun th =>
      Tactics.EVERY B ((B.CONJUNCTS th).map (fun c => assumeTac c))),
    refuteThen assumeTac ]

end Hashek

/- ---------------------------------------------------------------------- -/
/- Substitution (`thecops.ml`: substitution.ml).                          -/
/- ---------------------------------------------------------------------- -/

/- `type lit = int * fol_term list` (= `fol_atom`), `type iterm = fol_term`.
   Two implementations: `Substlist` (assoc list, pure/`Except`) and `Substarray`
   (mutable array + trail, `IO`).  The CoP search uses `Cop.Subst =
   Substoff(Substarray)` — the array version — so that is the live path;
   `Substlist` is translated for faithfulness but is not on the search path. -/

open HolCore.Meson (fol_term fol_atom)

abbrev lit := fol_atom          -- int × fol_term list
abbrev iterm := fol_term

partial def offset_term (off : Int) : iterm → iterm
  | .Fvar v => .Fvar (v + off)
  | .Fnapp f a => .Fnapp f (a.map (offset_term off))
def offset_lit (off : Int) (l : lit) : lit := (l.1, l.2.map (offset_term off))

/- ---------------------------------------------------------------------- -/
/- Substlist: assoc-list substitution (unused by the live search)         -/
/- (`thecops.ml`: substitution.ml).                                       -/
/- ---------------------------------------------------------------------- -/
namespace Substlist

abbrev t := List (Int × iterm)

/-- `istriv sub x tm`: occurs-check — `x` occurs in `tm` under `sub` (fails hard
    with `Unify` if a proper occurrence is found, mirroring OCaml). -/
partial def istriv (sub : t) (x : Int) : iterm → Except String Bool
  | .Fvar y =>
    if y = x then .ok true
    else match HolCore.Lib.assoc y sub with
         | .ok tm => istriv sub x tm
         | .error _ => .ok false
  | .Fnapp _ a =>
    -- OCaml: List.exists (istriv sub x) a && raise Unify  → any proper subterm hit ⇒ Unify
    (do
      let mut hit := false
      for s in a do
        if ← istriv sub x s then hit := true
      if hit then .error "Unify" else .ok false)

def add_subst (sub : t) (x : Int) (tm : iterm) : Except String t := do
  if ← istriv sub x tm then return sub else return ((x, tm) :: sub)

mutual
partial def unify_tm (sub : t) : iterm → iterm → Except String t
  | .Fnapp f fargs, .Fnapp g gargs =>
    if f ≠ g then .error "Unify" else unify_tms sub fargs gargs
  | tm, .Fvar x | .Fvar x, tm =>
    match HolCore.Lib.assoc x sub with
    | .ok t => unify_tm sub tm t
    | .error _ => add_subst sub x tm
partial def unify_tms (sub : t) : List iterm → List iterm → Except String t
  | [], [] => .ok sub
  | a :: as', b :: bs => do unify_tms (← unify_tm sub a b) as' bs
  | _, _ => .error "unify_tms: length"
end

def unify_lit (env : t) (l1 l2 : lit) : Except String t :=
  if l1.1 ≠ l2.1 then .error "Unify" else unify_tms env l1.2 l2.2

/- Unification with renaming of the second argument. -/
mutual
partial def unify_tm_off (off : Int) (sub : t) : iterm → iterm → Except String t
  | .Fnapp f fargs, .Fnapp g gargs =>
    if f ≠ g then .error "Unify" else unify_tms_off off sub fargs gargs
  | t1, .Fvar x =>
    let x := x + off
    match HolCore.Lib.assoc x sub with
    | .ok t => unify_tm_off 0 sub t1 t
    | .error _ => add_subst sub x t1
  | .Fvar x, t2 =>
    match HolCore.Lib.assoc x sub with
    | .ok t => unify_tm_off off sub t t2
    | .error _ => add_subst sub x (offset_term off t2)
partial def unify_tms_off (off : Int) (sub : t) : List iterm → List iterm → Except String t
  | [], [] => .ok sub
  | a :: as', b :: bs => do unify_tms_off off (← unify_tm_off off sub a b) as' bs
  | _, _ => .error "unify_tms_off: length"
end

partial def eq_var_tm (sub : t) (x : Int) : iterm → Except String Bool
  | .Fvar y =>
    if y = x then .ok true
    else match HolCore.Lib.assoc y sub with | .ok t => eq_var_tm sub x t | .error _ => .ok false
  | .Fnapp _ _ => .ok false

mutual
partial def eq_term (sub : t) : iterm → iterm → Except String Bool
  | .Fnapp f fa, .Fnapp g ga => if f = g then eq_terms sub fa ga else .ok false
  | tm1, .Fvar x =>
    match HolCore.Lib.assoc x sub with | .ok t => eq_term sub tm1 t | .error _ => eq_var_tm sub x tm1
  | .Fvar x, tm2 =>
    match HolCore.Lib.assoc x sub with | .ok t => eq_term sub t tm2 | .error _ => eq_var_tm sub x tm2
partial def eq_terms (sub : t) : List iterm → List iterm → Except String Bool
  | [], [] => .ok true
  | a :: as', b :: bs => do if ← eq_term sub a b then eq_terms sub as' bs else .ok false
  | _, _ => .ok false
end

def eq_lit (sub : t) (l1 l2 : lit) : Except String Bool :=
  if l1.1 = l2.1 then eq_terms sub l1.2 l2.2 else .ok false

-- In leanCoP: only for printing, in resolve is used by unify_rename2
partial def inst_tm (sub : t) : iterm → iterm
  | .Fvar v => match HolCore.Lib.assoc v sub with | .ok t => inst_tm sub t | .error _ => .Fvar v
  | .Fnapp f args => .Fnapp f (args.map (inst_tm sub))
def inst_lit (sub : t) (l : lit) : lit := (l.1, l.2.map (inst_tm sub))

partial def ground_tm (sub : t) : iterm → Bool
  | .Fvar v => match HolCore.Lib.assoc v sub with | .ok t => ground_tm sub t | .error _ => false
  | .Fnapp _ args => args.all (ground_tm sub)
def ground_lit (sub : t) (l : lit) : Bool := l.2.all (ground_tm sub)

def empty (_ : Int) : t := []
def to_list (sub : t) : List (Int × iterm) := sub

end Substlist

/- ---------------------------------------------------------------------- -/
/- Substarray: mutable-array substitution with a restore trail (LIVE)     -/
/- (`thecops.ml`: substitution.ml).                                       -/
/- ---------------------------------------------------------------------- -/

/- OCaml: `((iterm option array × int list ref) × int list)`.  `suba` is the
   assignment array, `env` the trail ref of assigned indices, `subl` the
   snapshot to restore back to.  `restore_subst` pops `env` down to `subl`.  All
   `IO` (shared mutable state). -/
namespace Substarray

/-- The array+trail; the immutable `subl` snapshot travels alongside as `t`. -/
structure Arrays where
  suba : IO.Ref (Array (Option iterm))
  env  : IO.Ref (List Int)

abbrev t := Arrays × List Int

/-- Pop the trail `env` back down to `subl`, un-assigning array entries. -/
partial def restore_subst (sub : t) : IO Unit := do
  let (arrs, subl) := sub
  let rec loop : IO Unit := do
    let e ← arrs.env.get
    -- OCaml tests `!env == subl` (PHYSICAL equality); structural equality is
    -- equivalent here because `subl` is always a suffix of the trail, so a
    -- partially-popped trail is strictly longer than `subl` and first matches
    -- structurally exactly at the physical suffix.
    if e == subl then pure ()
    else match e with
         | h :: tl => do
           let a ← arrs.suba.get; arrs.suba.set (a.set! h.toNat none)
           arrs.env.set tl; loop
         | [] => pure ()        -- OCaml failwith "restore_subst"; unreachable if subl ⊑ env
  loop

partial def istriv (arrs : Arrays) (x : Int) : iterm → IO (Except String Bool)
  | .Fvar y => do
    if y = x then return .ok true
    else match (← arrs.suba.get)[y.toNat]! with
         | some t => istriv arrs x t
         | none => return .ok false
  | .Fnapp _ a => do
    let mut hit := false
    for s in a do
      match ← istriv arrs x s with
      | .ok true => hit := true
      | .ok false => pure ()
      | .error e => return .error e
    if hit then return .error "Unify" else return .ok false

/-- `add_subst sub x tm`: assign `x := tm` (unless trivial), pushing `x` on the
    trail.  Returns the updated `t` (same arrays, new `subl = !env`). -/
def add_subst (sub : t) (x : Int) (tm : iterm) : IO (Except String t) := do
  let (arrs, _) := sub
  match ← istriv arrs x tm with
  | .error e => return .error e
  | .ok true => return .ok sub
  | .ok false => do
    let a ← arrs.suba.get; arrs.suba.set (a.set! x.toNat (some tm))
    arrs.env.modify (x :: ·)
    return .ok (arrs, ← arrs.env.get)

mutual
partial def unify_tm (sub : t) : iterm → iterm → IO (Except String t)
  | .Fnapp f fargs, .Fnapp g gargs => do
    if f ≠ g || fargs.length ≠ gargs.length then return .error "Unify"
    else
      let mut cur := sub
      let pairs := fargs.zip gargs
      for (a, b) in pairs do
        match ← unify_tm cur a b with | .ok s => cur := s | .error e => return .error e
      return .ok cur
  | tm, .Fvar x | .Fvar x, tm => do
    match (← sub.1.suba.get)[x.toNat]! with
    | some t => unify_tm sub tm t
    | none => add_subst sub x tm
end

/-- `unify_tms sub l1 l2`: restore the trail, then fold `unify_tm`. -/
def unify_tms (sub : t) (l1 l2 : List iterm) : IO (Except String t) := do
  restore_subst sub
  if l1.length ≠ l2.length then return .error "Unify"
  let mut cur := sub
  for (a, b) in l1.zip l2 do
    match ← unify_tm cur a b with | .ok s => cur := s | .error e => return .error e
  return .ok cur

def unify_lit (env : t) (l1 l2 : lit) : IO (Except String t) := do
  if l1.1 ≠ l2.1 then return .error "Unify" else unify_tms env l1.2 l2.2

partial def offset_vars (off : Int) : iterm → iterm
  | .Fvar x => .Fvar (x + off)
  | .Fnapp x l => .Fnapp x (l.map (offset_vars off))

mutual
partial def unify_tm_off (off : Int) (sub : t) : iterm → iterm → IO (Except String t)
  | .Fnapp f fargs, .Fnapp g gargs => do
    if f ≠ g || fargs.length ≠ gargs.length then return .error "Unify"
    else
      let mut cur := sub
      for (a, b) in fargs.zip gargs do
        match ← unify_tm_off off cur a b with | .ok s => cur := s | .error e => return .error e
      return .ok cur
  | t1, .Fvar x => do
    let x := x + off
    match (← sub.1.suba.get)[x.toNat]! with
    | some t => unify_tm_off 0 sub t1 t
    | none => add_subst sub x t1
  | .Fvar x, t2 => do
    match (← sub.1.suba.get)[x.toNat]! with
    | some t => unify_tm_off off sub t t2
    | none => add_subst sub x (offset_vars off t2)
end

def unify_tms_off (off : Int) (sub : t) (l1 l2 : List iterm) : IO (Except String t) := do
  restore_subst sub
  if l1.length ≠ l2.length then return .error "Unify"
  let mut cur := sub
  for (a, b) in l1.zip l2 do
    match ← unify_tm_off off cur a b with | .ok s => cur := s | .error e => return .error e
  return .ok cur

partial def eq_var_tm (arrs : Arrays) (x : Int) : iterm → IO Bool
  | .Fvar y => do
    if y = x then return true
    else match (← arrs.suba.get)[y.toNat]! with | some t => eq_var_tm arrs x t | none => return false
  | .Fnapp _ _ => return false

mutual
partial def eq_tm (arrs : Arrays) : iterm → iterm → IO Bool
  | .Fnapp f fargs, .Fnapp g gargs => do
    if f = g then eq_tms arrs fargs gargs else return false
  | tm1, .Fvar x => do
    match (← arrs.suba.get)[x.toNat]! with | some t => eq_tm arrs tm1 t | none => eq_var_tm arrs x tm1
  | .Fvar x, tm2 => do
    match (← arrs.suba.get)[x.toNat]! with | some t => eq_tm arrs t tm2 | none => eq_var_tm arrs x tm2
partial def eq_tms (arrs : Arrays) : List iterm → List iterm → IO Bool
  | [], [] => return true
  | a :: as', b :: bs => do if ← eq_tm arrs a b then eq_tms arrs as' bs else return false
  | _, _ => return false
end

def eq_lit (sub : t) (l1 l2 : lit) : IO Bool := do
  if l1.1 = l2.1 then do restore_subst sub; eq_tms sub.1 l1.2 l2.2 else return false

def empty (n : Int) : IO t := do
  let suba ← IO.mkRef (Array.replicate n.toNat (none : Option iterm))
  let env ← IO.mkRef ([] : List Int)
  return (⟨suba, env⟩, [])

def to_list (sub : t) : IO (List (Int × iterm)) := do
  let (arrs, subl) := sub
  let a ← arrs.suba.get
  let mut out := []
  for v in subl do
    match a[v.toNat]! with
    | some t => out := out ++ [(v, t)]
    | none => pure ()   -- OCaml failwith "convert_subst"; unreachable
  return out

partial def inst_term (arrs : Arrays) : iterm → IO iterm
  | .Fvar x => do match (← arrs.suba.get)[x.toNat]! with | some t => inst_term arrs t | none => return .Fvar x
  | .Fnapp f a => do return .Fnapp f (← a.mapM (inst_term arrs))

def inst_tm (sub : t) (t : iterm) : IO iterm := do restore_subst sub; inst_term sub.1 t
def inst_lit (sub : t) (l : lit) : IO lit := do
  restore_subst sub; return (l.1, ← l.2.mapM (inst_term sub.1))

partial def ground_tm (arrs : Arrays) : iterm → IO Bool
  | .Fvar x => do match (← arrs.suba.get)[x.toNat]! with | some t => ground_tm arrs t | none => return false
  | .Fnapp _ a => do
    for s in a do if !(← ground_tm arrs s) then return false
    return true
def ground_lit (sub : t) (l : lit) : IO Bool := do
  restore_subst sub
  for s in l.2 do if !(← ground_tm sub.1 s) then return false
  return true

end Substarray

/- ---------------------------------------------------------------------- -/
/- Substoff: adds a variable-offset counter to a substitution             -/
/- (`thecops.ml`: substitution.ml).                                       -/
/- ---------------------------------------------------------------------- -/

/- The CoP search uses `Subst = Substoff(Substarray)`; `t = Substarray.t × Int`. -/
namespace Subst

abbrev t := Substarray.t × Int

def empty (n : Int) : IO t := do return (← Substarray.empty n, 0)

def eq (sub : t) (l1 l2 : lit) : IO Bool := Substarray.eq_lit sub.1 l1 l2

def inst_lit (sub : t) (l : lit) : IO lit := Substarray.inst_lit sub.1 l
def inst_tm (sub : t) (tm : iterm) : IO iterm := Substarray.inst_tm sub.1 tm
def ground_lit (sub : t) (l : lit) : IO Bool := Substarray.ground_lit sub.1 l

/-- `unify (sub,off) l1 l2 = try Some (unify_lit sub l1 l2, off) with Unify -> None`. -/
def unify (sub : t) (l1 l2 : lit) : IO (Option t) := do
  match ← Substarray.unify_lit sub.1 l1 l2 with
  | .ok s => return some (s, sub.2)
  | .error _ => return none

/-- `unify_tms sub l1 l2` (used by nanoCoP `unify_vars`). -/
def unify_tms (sub : t) (l1 l2 : List iterm) : IO (Except String t) := do
  match ← Substarray.unify_tms sub.1 l1 l2 with
  | .ok s => return .ok (s, sub.2) | .error e => return .error e

def unify_tms_off (off : Int) (sub : t) (l1 l2 : List iterm) : IO (Except String Substarray.t) :=
  Substarray.unify_tms_off off sub.1 l1 l2

/-- `unify_rename_subst off l1 l2 sub list = (unify_tms_off off sub l1 l2, map (offset_lit off) list)`. -/
def unify_rename_subst (off : Int) (l1 l2 : List iterm) (sub : t) (list : List fol_atom) :
    IO (Except String (Substarray.t × List fol_atom)) := do
  match ← Substarray.unify_tms_off off sub.1 l1 l2 with
  | .ok s => return .ok (s, list.map (offset_lit off))
  | .error e => return .error e

/-- `unify_rename (s,off) args1 (args2, rest, vars, _)`: unify head args, renaming
    the contrapositive's variables by `off` when `vars > 0`, returning the updated
    substitution/offset and the (offset) rest of the clause.  `None` on failure. -/
def unify_rename (sub : t) (args1 : List iterm)
    (contra : List iterm × List fol_atom × Int × (Int × thm)) : IO (Option (t × List fol_atom)) := do
  let (args2, rest, vars, _) := contra
  let off := sub.2
  if vars = 0 then
    match ← Substarray.unify_tms sub.1 args1 args2 with
    | .ok s => return some ((s, off), rest)
    | .error _ => return none
  else
    match ← unify_rename_subst off args1 args2 sub rest with
    | .ok (s, rest') => return some ((s, off + vars), rest')
    | .error _ => return none

end Subst

/- ---------------------------------------------------------------------- -/
/- Database: contrapositive store for leanCoP                             -/
/- (`thecops.ml`: database.ml).                                           -/
/- ---------------------------------------------------------------------- -/

/- OCaml `db : (int, contrapositive list) Hashtbl.t`.  We back it with a
   Session-owned `IO.Ref (List (Int × List contrapositive))` (an assoc list keyed
   by predicate code). -/
namespace Database

open HolCore.Meson (fol_term fol_atom folRule ancestors FolStores)

/-- `contrapositive = (fol_term list * fol_atom list * int * (int * thm))`:
    the head-literal args, the rest of the clause, the clause's variable count,
    and the source contrapositive `(index, thm)`. -/
abbrev contrapositive := List fol_term × List fol_atom × Int × (Int × thm)

/-- for every predicate, store list of possible contrapositives
    (Session-owned): predicate-code → contrapositives. -/
abbrev DB := IO.Ref (List (Int × List contrapositive))

def clause_max_var (cl : List fol_atom) : Int :=
  1 + cl.foldl Fol_term.lit_max_var (-1)

/-- `mapentry ((cl_rest,(p,args)),th) = (args, cl_rest, clause_max_var((p,args)::cl_rest), th)`. -/
def mapentry (r : folRule) : contrapositive :=
  let cl_rest := r.1.1
  let (p, args) := r.1.2
  (args, cl_rest, clause_max_var ((p, args) :: cl_rest), r.2)

/-- Assoc-list `Hashtbl.add`: prepend `(k, v)` (multi-binding, latest first). -/
private def dbAdd (db : DB) (k : Int) (v : List contrapositive) : IO Unit :=
  db.modify (fun l => (k, v) :: l)

/-- `axioms2db ths`: clear the db and populate from the FOL clauses of `ths`. -/
def axioms2db (S : FolStores) (db : DB) (ths : List thm) : IO (Except String Unit) := do
  db.set []
  match ← FirstOrder.Mapping.fol_of_hol_clauses S ths with
  | .error e => return .error e
  | .ok anc =>
    for (p, l) in anc do
      dbAdd db (-p) (l.map mapentry)
    return .ok ()

/-- `db_entries lit = try Hashtbl.find db (fst lit) with Not_found -> []`.
    (OCaml `Hashtbl.find` returns the most recently added binding.) -/
def db_entries (db : DB) (lit : fol_atom) : IO (List contrapositive) := do
  match (← db.get).find? (fun kv => kv.1 = lit.1) with
  | some kv => return kv.2
  | none => return []

end Database

/- ---------------------------------------------------------------------- -/
/- Equality: equality axioms with an added symmetry rule (`thecops.ml`:   -/
/- equality.ml).                                                          -/
/- ---------------------------------------------------------------------- -/

/- OCaml's `Equality.create_equality_axioms` is exactly `Meson.create_equality_axioms`
   but with a THREE-conjunct `eq_thms` (adding the symmetry disjunct
   `~(x=y) \/ y=x`), whereas Meson uses two (reflexivity + transitivity).  Since
   `Meson.create_equality_axioms` already takes the `EqAxPths` bundle as a
   parameter, we reuse it verbatim, supplying a leanCoP-specific `EqAxPths`
   (built in `Session` with the extra symmetry conjunct). -/
namespace Equality

/-- Version of Meson.create_equality_axioms with added symmetry rule
    (uses the symmetry-augmented `EqAxPths` `E`). -/
def create_equality_axioms (B : BoolThms) (E : Meson.EqAxPths) (tms : List term) :
    IO (Except String (List thm)) := Meson.create_equality_axioms B E tms

/-- `create_eq_axs sym`: with symmetry (`E`) if `sym`, else plain Meson (`Emeson`). -/
def create_eq_axs (B : BoolThms) (E Emeson : Meson.EqAxPths) (sym : Bool) (tms : List term) :
    IO (Except String (List thm)) :=
  if sym then create_equality_axioms B E tms
  else Meson.create_equality_axioms B Emeson tms

end Equality

/- ---------------------------------------------------------------------- -/
/- Proof: the leanCoP proof tree (`thecops.ml`: proof.ml).                -/
/- ---------------------------------------------------------------------- -/
namespace Proof

/-- leanCoP proof: `Lemma | Reduction | Extension of 'c * ('l * proof) list`. -/
inductive proof (l c : Type) where
  | Lemma
  | Reduction
  | Extension (contra : c) (subs : List (l × proof l c))

end Proof

/- ---------------------------------------------------------------------- -/
/- Prepare: the CoP goal-preparation tactic (`thecops.ml`: prepare.ml).   -/
/- ---------------------------------------------------------------------- -/

/- `PREPARE_COP_TAC` reuses the Meson conversion/tactic bundle (`MesonTacDeps`)
   plus the Canon convs and the `Hashek.MARK_*` tactics.  Parameterized like the
   Metis `FOL_PREPARE_TAC`. -/
namespace Prepare

/-- `PREPARE_COP_TAC ths`: refute, POLY_ASSUME the lemmas, mark the goal with the
    hashek literal, then run the (unmodified) Meson preprocessing pipeline. -/
def PREPARE_COP_TAC (B : BoolThms) (D : Meson.MesonTacDeps) (H : Hashek.HashekThms)
    (notTFimp' : IO (Except String thm)) (ths : List thm) : tactic := fun g => do
  -- `MARK_CONCL "copconcl"` proves its TAUT when PREPARE_COP_TAC is applied.
  let notTFimp ← match ← notTFimp' with
    | .ok th => pure th
    | .error e => return .error e
  let assumeTac : thm_tactic := fun th => Tactics.ASSUME_TAC B th
  let betaTopDepth : ioconv := HolCore.Simp.topDepthConvIO (fun t => pure (HolCore.Equal.BETA_CONV t))
  let frontConv : ioconv :=
    HolCore.Simp.thencIO D.presimp (HolCore.Simp.thencIO betaTopDepth
      (HolCore.Simp.thencIO D.lambdaElim (HolCore.Simp.thencIO D.condsCelim D.quantBool)))
  let nnfSkolem : thm → IO (Except String thm) :=
    fun th => HolCore.Simp.convRuleIO (HolCore.Simp.thencIO D.nnf D.skolem) th
  let genAllThs ← (do
    let mut acc : List thm := []
    for th in ths do
      match B.GEN_ALL th with | .error e => return (.error e) | .ok g' => acc := acc ++ [g']
    return (.ok acc) : IO (Except String (List thm)))
  match genAllThs with
  | .error e => return .error e
  | .ok gaThs =>
    let undischAll : tactic := fun (asl, w) =>
      (Tactics.MAP_EVERY B (fun (p : String × thm) => Tactics.UNDISCH_TAC B (concl p.2)) asl (asl, w)
       : IO (Except String goalstate))
    let specFrees : tactic := fun (asl, w) =>
      (Tactics.MAP_EVERY B (fun v => Tactics.SPEC_TAC B (v, v)) (frees w) (asl, w)
       : IO (Except String goalstate))
    let tac : tactic := Tactics.EVERY B [
      -- mostly from Meson
      D.refuteThen (fun th => Tactics.LABEL_TAC B "copconcl" th),
      Meson.POLY_ASSUME_TAC B gaThs,
      -- CoP-specific part
      ORELSE (Hashek.MARK_CONCL B H notTFimp D.refuteThen "copconcl") (Hashek.MARK_ASSUMS B H),
      -- unmodified Meson parts start here
      undischAll,
      D.selectElim,
      specFrees,
      Tactics.CONV_TAC B frontConv,
      Tactics.REPEAT B (ORELSE (Tactics.GEN_TAC B) (Tactics.DISCH_TAC B)),
      D.refuteThen assumeTac,
      Tactics.RULE_ASSUM_TAC B nnfSkolem,
      Tactics.REPEAT B (Tactics.FIRST_X_ASSUM B (fun th => Tactics.CHOOSE_TAC B th)),
      D.asmFol ]
    (tac g : IO (Except String goalstate))

end Prepare

/- ---------------------------------------------------------------------- -/
/- Search: the leanCoP connection-search engine                           -/
/- (`thecops.ml`: search.ml).                                             -/
/- ---------------------------------------------------------------------- -/

/- CPS over `Strom` producing `(Subst.t, lemmas, proof)` triples.  `copverb`
   tracing is dropped (non-semantic).  The database is the Session-owned `DB`. -/
namespace Search

open Cop (search_opts)
open Proof

/-- leanCoP proof tree: literals `lit`, contrapositive tag `Int × thm`. -/
abbrev lproof := Proof.proof lit (Int × thm)
/-- A search result: substitution/offset, accumulated lemmas, proof. -/
abbrev sres := Subst.t × List lit × lproof

/-- `cut p xs ys`: `Strom.cut` if `p`, else `Strom.append`. -/
def cut (p : Bool) (xs ys : Strom α) : IO (Strom α) :=
  if p then Strom.cut xs ys else Strom.append xs ys

mutual
/-- `prove_lit opt sub (path, lem, lim) lit`: stream of ways to solve `lit`. -/
partial def prove_lit (S : FolStores) (db : Database.DB) (opt : search_opts) (sub : Subst.t)
    (path lem : List lit) (lim : Int) (lit : lit) : IO (Strom sres) := do
  -- thecops.ml 642-644
  if ← copverb.get then
    stdPrintf s!"Lit: {← Print.string_of_lit S (← Subst.inst_lit sub lit)}\n"
    stdPrintf s!"Path: {← Print.string_of_lits S (← path.mapM (Subst.inst_lit sub))}\n"
    stdPrintf s!"Lemmas: {← Print.string_of_lits S (← lem.mapM (Subst.inst_lit sub))}\n"
  let neglit := Fol_term.negate_lit lit
  -- lemmas
  let lemmas ← (do
    if opt.improved_lemmas then do
      let mut hit := false
      for l in lem do if ← Subst.eq sub lit l then hit := true
      if hit then do
        if ← copverb.get then stdPrintf "lemma\n"
        Strom.cons (sub, lem, .Lemma) Strom.nil
      else pure Strom.nil
    else do
      let ls ← Strom.ofList lem
      -- of_list lem |> filter (Subst.eq sub lit) |> map (fun _ => (sub, lit::lem, Lemma))
      pure (Strom.filterMap (fun l => do
        if ← Subst.eq sub lit l then do
          if ← copverb.get then stdPrintf "lemma\n"
          pure (some (sub, lit :: lem, (.Lemma : lproof)))
        else pure none) ls))
  -- reductions
  let redStream ← Strom.ofList path
  let reductions := Strom.filterMap (fun p => do
    if ← copverb.get then
      stdPrintf s!"Reduction try {← Print.string_of_lit S p} (for lit {← Print.string_of_lit S (← Subst.inst_lit sub lit)}, lim {lim})\n"
    match ← Subst.unify sub neglit p with
    | some sub1 => do
      if ← copverb.get then stdPrintf "Reduction works\n"
      pure (some (sub1, lit :: lem, (.Reduction : lproof)))
    | none => pure none) redStream
  -- extensions
  let entries ← Database.db_entries db neglit
  let entryStream ← Strom.ofList entries
  let extensions ← Strom.concatMapM (fun (contra : Database.contrapositive) => do
    let (_, _, vars, hsh) := contra
    if lim < 0 && vars > 0 then pure Strom.nil
    else
      match ← Subst.unify_rename sub lit.2 contra with
      | some (sub1, cla1) => do
        let clStream ← prove_clause S db opt sub1 (lit :: path) lem (lim - 1) (cla1, hsh)
        pure (Strom.map (fun (r : Subst.t × List (fol_atom × lproof)) =>
          (r.1, lit :: lem, (.Extension hsh r.2 : lproof))) clStream)
      | none => pure Strom.nil)
    entryStream
  -- cut opt.cut1 lemmas (cut opt.cut2 reductions (cut opt.cut3 extensions nil))
  let c3 ← cut opt.cut3 extensions Strom.nil
  let c2 ← cut opt.cut2 reductions c3
  cut opt.cut1 lemmas c2
/-- `prove_clause opt sub (path, lem, lim) (cl, hsh)`: solve every literal. -/
partial def prove_clause (S : FolStores) (db : Database.DB) (opt : search_opts) (sub : Subst.t)
    (path lem : List lit) (lim : Int) (clhsh : List lit × (Int × thm)) :
    IO (Strom (Subst.t × List (fol_atom × lproof))) := do
  let (cl, cl_hsh) := clhsh
  match cl with
  | lit :: lits => do
    -- regularity: some clause literal already occurs (under sub) on the path
    let mut reg := false
    for x in cl do
      for pl in path do
        if ← Subst.eq sub x pl then reg := true
    if reg then do
      if ← copverb.get then stdPrintf "regularity\n"
      pure Strom.nil
    else do
      let litStream ← prove_lit S db opt sub path lem lim lit
      Strom.concatMapM (fun (r : sres) => do
        let (sub1, lem1, prf1) := r
        let clStream ← prove_clause S db opt sub1 path lem1 lim (lits, cl_hsh)
        pure (Strom.map (fun (r2 : Subst.t × List (fol_atom × lproof)) =>
          (r2.1, (lit, prf1) :: r2.2)) clStream))
        litStream
  | [] => Strom.cons (sub, ([] : List (fol_atom × lproof))) Strom.nil
end

end Search

/- ---------------------------------------------------------------------- -/
/- Recon: reconstruct the leanCoP proof into HOL                          -/
/- (`thecops.ml`: recon.ml).                                              -/
/- ---------------------------------------------------------------------- -/

/- `hashek_of_proof sub lem lit prf` builds a HOL theorem from the CoP proof.
   `sub : Substarray.t` (the array substitution, offset dropped).  Reuses
   `Meson.make_hol_contrapos`/`finish_RULE` and `FirstOrder.Mapping.hol_of_literal`. -/
namespace Recon

open Search (lproof)
open Proof

def hol_negate (tm : term) : Except String term :=
  match dest_neg tm with | .ok t => .ok t | .error _ => mk_neg tm

/-- `hashek_of_proof S B P mem sub lem lit prf`.  `P`/`mem` are the Meson pth
    bundle + contrapositive cache (for `make_hol_contrapos`/`finish_RULE`). -/
partial def hashek_of_proof (S : FolStores) (B : BoolThms) (P : Meson.MesonPths)
    (mem : Meson.ContraposCache) (sub : Substarray.t) (lem : List thm) (lit : lit)
    (prf : lproof) : IO (Except String thm) := do
  let ilit ← Substarray.inst_lit sub lit
  match ← FirstOrder.Mapping.hol_of_literal S ilit with
  | .error e => return .error e
  | .ok liti =>
    match prf with
    | .Lemma => return (HolCore.Lib.find (fun x => concl x == liti) lem)
    | .Reduction => return (ASSUME liti)
    | .Extension hsh prfs => do
      -- fold_map hashek_of_proof over prfs, accumulating lemmas
      let mut curLem := lem
      let mut ths : List thm := []
      for (l, p) in prfs do
        match ← hashek_of_proof S B P mem sub curLem l p with
        | .error e => return .error e
        | .ok pth => curLem := pth :: curLem; ths := ths ++ [pth]
      match ← Meson.make_hol_contrapos B P mem hsh.1 hsh.2 with
      | .error e => return .error e
      | .ok cth =>
        let hth ← (if ths.isEmpty then pure (.ok cth)
                   else match end_itlistM (fun a b => B.CONJ a b) ths with
                        | .ok conj => (Drule.MATCH_MP B cth conj : IO (Except String thm))
                        | .error e => pure (.error e))
        match hth with
        | .error e => return .error e
        | .ok hth =>
          match ← Drule.PART_MATCH B (fun x => .ok x) hth liti with
          | .error e => return .error e
          | .ok ith =>
            match hol_negate (concl ith) with
            | .error e => return .error e
            | .ok neg => match B.DISCH neg ith with
                         | .error e => return .error e
                         | .ok d => Meson.finish_RULE B P d

end Recon

/- ---------------------------------------------------------------------- -/
/- Leancop: the leanCoP entry points (`thecops.ml`: leancop.ml).          -/
/- ---------------------------------------------------------------------- -/
/- Some examples that are not provable by MESON or METIS in reasonable time:
   LEANCOP [EXTENSION; IN_INSERT] (concl INSERT_COMM);;
   LEANCOP [EXTENSION; IN_DELETE] (concl DELETE_COMM);;
   LEANCOP [EXTENSION; IN_DELETE; IN_INTER] (concl DELETE_INTER);;
   LEANCOP [SUM_SUPERSET; SUBSET; IN_UNION] (concl SUM_UNION_RZERO);;
   LEANCOP [SUBSET; NSUM_SUPERSET; IN_UNION] (concl NSUM_UNION_RZERO);;
   LEANCOP [EXTENSION; NOT_IN_EMPTY; IN_INTERS; IN_INSERT] (concl INTERS_1);; -/

/- `LEANCOP_DEEPEN` runs the search + reconstruction; the tactics prepare the
   goal.  Bundled dependencies (`LeancopDeps`) keep the signatures manageable;
   `Session` supplies the concrete bundle. -/
namespace Leancop

open Cop (search_opts strategy)

/-- Everything the leanCoP driver needs (Session-supplied). -/
structure LeancopDeps where
  S : FolStores                        -- shared MESON/CoP term↔code stores
  P : Meson.MesonPths                  -- Meson pth bundle (make_hol_contrapos/finish_RULE)
  mem : Meson.ContraposCache           -- contrapositive cache
  db : Database.DB                     -- leanCoP contrapositive database
  E : Meson.EqAxPths                   -- equality axioms WITH symmetry
  Emeson : Meson.EqAxPths              -- plain Meson equality axioms
  hashek : Hashek.HashekThms           -- hashek marker theorems
  D : Meson.MesonTacDeps               -- Canon/Meson conversion + tactic bundle
  notTFimp : IO (Except String thm)    -- TAUT `!t. (~t ==> F <=> t)`, per call

/-- `start opt lim`: search for a refutation of the negated hashek literal. -/
def start (dp : LeancopDeps) (opt : search_opts) (lim : Int) :
    IO (Option (Substarray.t × Search.lproof)) := do
  if ← copverb.get then stdPrintf s!"Start {lim + 1}\n"   -- thecops.ml 738
  let sub0 ← Subst.empty 1000000
  -- thecops.ml 740: plain `let hashek = Mapping.fol_of_literal ..`; a failure
  -- raises out of `start`/`deepen`/`strategy` rather than becoming `none`.
  match ← FirstOrder.Mapping.fol_of_literal dp.S [] [] dp.hashek.hashek_tm with
  | .error e => throw (IO.userError e)
  | .ok hashek =>
    let hashek_neg := Fol_term.negate_lit hashek
    let prfs ← Search.prove_lit dp.S dp.db opt sub0 [] [] lim hashek_neg
    match ← Strom.nextOpt prfs with
    | some (sub, _, prf) => return some (sub.1, prf)
    | none => return none

/-- Possible optimization:
    Reduce variable indexes to reduce used substitution and fit better in cache

    `LEANCOP_DEEPEN opt ths`: prove `F` from clause set `ths` by leanCoP. -/
def LEANCOP_DEEPEN (B : BoolThms) (dp : LeancopDeps) (opt : search_opts) (ths : List thm) :
    IO (Except String thm) := do
  Meson.clear_contrapos_cache dp.mem
  FirstOrder.Mapping.reset_vars dp.S
  -- thecops.ml 750: `Mapping.reset_consts()` runs in sequence; propagate failure.
  match ← FirstOrder.Mapping.reset_consts dp.S with
  | .error e => return .error e
  | .ok _ =>
  match ← Equality.create_eq_axs B dp.E dp.Emeson opt.add_eq_symmetry (ths.map concl) with
  | .error e => return .error e
  | .ok eqAxs =>
    let ths' := ths ++ eqAxs
    match ← Database.axioms2db dp.S dp.db ths' with
    | .error e => return .error e
    | .ok _ =>
      let (sub, prf) ← strategy opt (start dp)
      match ← FirstOrder.Mapping.fol_of_literal dp.S [] [] dp.hashek.hashek_tm with
      | .error e => return .error e
      | .ok hashek =>
        let hashek_neg := Fol_term.negate_lit hashek
        match ← Recon.hashek_of_proof dp.S B dp.P dp.mem sub [] hashek_neg prf with
        | .error e => return .error e
        | .ok th => return (EQ_MP dp.hashek.hashek_eq th)

/-- Repeatedly `SPEC` a genvar under leading universals (for `PREPARE_LEAN_TAC`). -/
private partial def specGenvarLoop (B : BoolThms) (th : thm) : IO thm := do
  match Basics.dest_forall (concl th) with
  | .error _ => return th
  | .ok (v, _) =>
    let gv ← genvar (type_of v)
    match B.SPEC gv th with | .error _ => return th | .ok th' => specGenvarLoop B th'

/-- `PREPARE_LEAN_TAC ths`: `PREPARE_COP_TAC` then leanCoP-specific CNF prep. -/
def PREPARE_LEAN_TAC (B : BoolThms) (dp : LeancopDeps) (ths : List thm) : tactic :=
  let assumeTac : thm_tactic := fun th => Tactics.ASSUME_TAC B th
  let prenexCnf : thm → IO (Except String thm) :=
    fun th => HolCore.Simp.convRuleIO (HolCore.Simp.thencIO dp.D.prenex dp.D.weakCnf) th
  let specGenvarRule : thm → IO (Except String thm) := fun th0 => do return .ok (← specGenvarLoop B th0)
  let assocRule : thm → IO (Except String thm) := fun th => HolCore.Simp.convRuleIO dp.D.assocDisj th
  Tactics.EVERY B [
    Prepare.PREPARE_COP_TAC B dp.D dp.hashek dp.notTFimp ths,
    Tactics.RULE_ASSUM_TAC B prenexCnf,
    Tactics.RULE_ASSUM_TAC B specGenvarRule,
    Tactics.REPEAT B (Tactics.FIRST_X_ASSUM B (fun th => Meson.CONJUNCTS_THEN' B assumeTac th)),
    Tactics.RULE_ASSUM_TAC B assocRule,
    Tactics.REPEAT B (Tactics.FIRST_X_ASSUM B (fun th => Tactics.SUBST_VAR_TAC B th)) ]

/-- `PURE_LEANCOP opt`: accept the leanCoP refutation of the assumptions. -/
def PURE_LEANCOP (B : BoolThms) (dp : LeancopDeps) (opt : search_opts) : tactic := fun g => do
  let refute : tactic := fun (asl, w) => do
    match ← LEANCOP_DEEPEN B dp opt (asl.map (fun p => p.2)) with
    | .error e => return .error e
    | .ok th => Tactics.ACCEPT_TAC B th (asl, w)
  (ORELSE (Tactics.FIRST_ASSUM (fun cth => Tactics.CONTR_TAC B cth)) refute) g

def GEN_LEANCOP_TAC (B : BoolThms) (dp : LeancopDeps) (opt : search_opts) (ths : List thm) :
    tactic := THEN B (PREPARE_LEAN_TAC B dp ths) (PURE_LEANCOP B dp opt)

def LEANCOP_TAC (B : BoolThms) (dp : LeancopDeps) (ths : List thm) : tactic :=
  GEN_LEANCOP_TAC B dp Cop.search_opts_default ths

def LEANCOP (B : BoolThms) (dp : LeancopDeps) (ths : List thm) (tm : term) :
    IO (Except String thm) := Tactics.prove B tm (LEANCOP_TAC B dp ths)

end Leancop

/- ---------------------------------------------------------------------- -/
/- nanoCoP (non-clausal connection prover).                               -/
/- ---------------------------------------------------------------------- -/

/- ---------------------------------------------------------------------- -/
/- Ncmatrix: non-clausal matrices (`thecops.ml`: ncmatrix.ml).            -/
/- ---------------------------------------------------------------------- -/

/- OCaml mutually-recursive family over an index type `'t`:
     litmat  = Lit of lit | Mat of imatrix
     imatrix = 't * matrix
     matrix  = iclause list
     iclause = ('t * int list) * clause
     clause  = litmat list
   We make `litmat` the single nested inductive (through `List`/`×`) and recover
   the other names as `abbrev`s. -/
namespace Ncmatrix

open Fol_term

/-- The core nested inductive: a literal, or an indexed sub-matrix. -/
inductive litmat (t : Type) where
  | Lit (l : lit)
  | Mat (idx : t) (m : List ((t × List Int) × List (litmat t)))
  deriving Inhabited

abbrev clause (t : Type) := List (litmat t)
abbrev iclause (t : Type) := (t × List Int) × clause t
abbrev matrix (t : Type) := List (iclause t)
abbrev imatrix (t : Type) := t × matrix t

def map_litmat (fl : lit → β) (fm : imatrix t → β) : litmat t → β
  | .Lit l => fl l
  | .Mat idx m => fm (idx, m)

def lit_ (x : lit) : litmat t := .Lit x
def mat_ (x : imatrix t) : litmat t := .Mat x.1 x.2

def lit_of_litmat : litmat t → Option lit | .Lit l => some l | .Mat _ _ => none
def clause_lits (c : clause t) : List lit := c.filterMap lit_of_litmat

def clause_of_matrix [Inhabited t] : matrix t → clause t
  | [((_, []), c)] => c
  | lm => [litmat.Mat (default : t) lm]  -- OCaml `Mat ((), lm)`; `()` is the unit index

/- Stripping the FOL formula (`Meson.fol_form`: Atom/Conj/Disj/Forallq). -/
partial def strip_disj : Meson.fol_form → List Meson.fol_form
  | .Disj l r => strip_disj l ++ strip_disj r
  | x => [x]
partial def strip_conj : Meson.fol_form → List Meson.fol_form
  | .Conj l r => strip_conj l ++ strip_conj r
  | x => [x]
partial def strip_forallq (acc : List Int) : Meson.fol_form → List Int × Meson.fol_form
  | .Forallq x t => strip_forallq (x :: acc) t
  | t => (acc.reverse, t)

/- Build a `matrix` from a formula.  Original matrix_of_form from OCaml-nanoCoP
   is below.
   WARNING: Gives different results than version above, reconstruction fails! -/
mutual
partial def litmat_of_form : Meson.fol_form → litmat Unit
  | .Atom t => .Lit t
  | .Conj l r => .Mat () (matrix_of_form (.Conj l r))
  | .Forallq x b => .Mat () (matrix_of_form (.Forallq x b))
  | .Disj _ _ => .Lit (0, [])   -- OCaml failwith "litmat_of_form"; unreachable
partial def matrix_of_form (t : Meson.fol_form) : matrix Unit :=
  (strip_conj t).map iclause_of_form
partial def clause_of_form (t : Meson.fol_form) : clause Unit :=
  (strip_disj t).map litmat_of_form
partial def iclause_of_form (t : Meson.fol_form) : iclause Unit :=
  let (univ, t') := strip_forallq [] t
  (((), univ), clause_of_form t')
end

/- Max-var / offset / groundness. -/
mutual
partial def litmat_max_var (acc : Int) : litmat t → Int
  | .Lit l => lit_max_var acc l
  | .Mat _ m => matrix_max_var acc m
partial def matrix_max_var (acc : Int) : matrix t → Int
  | m => m.foldl iclause_max_var acc
partial def iclause_max_var (acc : Int) : iclause t → Int
  | (_, c) => clause_max_var acc c
partial def clause_max_var (acc : Int) : clause t → Int
  | c => c.foldl litmat_max_var acc
end

def clause_offset (c : clause t) : Int := 1 + clause_max_var (-1) c
def iclause_offset (c : iclause t) : Int := 1 + iclause_max_var (-1) c

def clause_ground (c : clause t) : Bool :=
  c.all (fun lm => match lm with | .Lit l => lit_ground l | .Mat _ _ => false)

/- Indexing: assign a running integer to every (sub)matrix/clause node. -/
mutual
partial def index_imatrix (i : Int) : imatrix t → Int × imatrix Int
  | (_, m) => let (j, m') := index_matrix (i + 1) m; (j, (i, m'))
partial def index_matrix (i : Int) : matrix t → Int × matrix Int
  | m => FirstOrder.Utils.List.fold_map index_iclause i m
partial def index_iclause (i : Int) : iclause t → Int × iclause Int
  | ((_, v), c) => let (j, c') := index_clause (i + 1) c; (j, ((i, v), c'))
partial def index_clause (i : Int) : clause t → Int × clause Int
  | c => FirstOrder.Utils.List.fold_map index_litmat i c
partial def index_litmat (i : Int) : litmat t → Int × litmat Int
  | .Lit l => (i, .Lit l)
  | .Mat idx m => let (j, m') := index_imatrix i (idx, m); (j, .Mat m'.1 m'.2)
end
def index_matrix_top (m : matrix t) : matrix Int := (index_matrix 0 m).2

/- Mapping the index type. -/
mutual
partial def map_imatrix [Inhabited t] [Inhabited β] (f : t → β) : imatrix t → imatrix β
  | (idx, m) => (f idx, map_matrix f m)
partial def map_matrix [Inhabited t] [Inhabited β] (f : t → β) : matrix t → matrix β
  | m => m.map (map_iclause f)
partial def map_iclause [Inhabited t] [Inhabited β] (f : t → β) : iclause t → iclause β
  | ((idx, v), c) => ((f idx, v), map_clause f c)
partial def map_clause [Inhabited t] [Inhabited β] (f : t → β) : clause t → clause β
  | c => c.map (fun lm => match lm with
                          | .Lit l => .Lit l
                          | .Mat idx m => let m' := map_imatrix f (idx, m); .Mat m'.1 m'.2)
end

def copy_matrix [Inhabited t] [Inhabited β] (k : β) (m : matrix t) : matrix (t × β) :=
  map_matrix (fun i => (i, k)) m
def copy_clause [Inhabited t] [Inhabited β] (k : β) (c : clause t) : clause (t × β) :=
  map_clause (fun i => (i, k)) c

/-- `break_map f l = Some [f x1; ...]` if all succeed, else `None` (Option monad). -/
partial def break_map (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | x :: xs => do let y ← f x; let ys ← break_map f xs; some (y :: ys)

/- Positive-literal filtering (keep only negative-code literals / non-empty mats). -/
mutual
partial def litmat_positive : litmat t → Option (litmat t)
  | .Lit (p, a) => if p < 0 then some (.Lit (p, a)) else none
  | .Mat idx m => match matrix_positive m with | [] => none | m' => some (.Mat idx m')
partial def matrix_positive : matrix t → matrix t
  | m => m.filterMap iclause_positive
partial def iclause_positive : iclause t → Option (iclause t)
  | (idx, c) => (clause_positive c).map (fun c' => (idx, c'))
partial def clause_positive : clause t → Option (clause t)
  | c => break_map litmat_positive c
end

/- Mapping / offsetting the term variables. -/
mutual
partial def map_litmat_vars (f : Int → Int) : litmat t → litmat t
  | .Lit l => .Lit (map_lit_vars (fun v => var (f v)) l)
  | .Mat idx m => let m' := map_imatrix_vars f (idx, m); .Mat m'.1 m'.2
partial def map_imatrix_vars (f : Int → Int) : imatrix t → imatrix t
  | (idx, m) => (idx, map_matrix_vars f m)
partial def map_matrix_vars (f : Int → Int) : matrix t → matrix t
  | m => m.map (map_iclause_vars f)
partial def map_iclause_vars (f : Int → Int) : iclause t → iclause t
  | ((idx, v), c) => ((idx, v.map f), map_clause_vars f c)
partial def map_clause_vars (f : Int → Int) : clause t → clause t
  | c => c.map (map_litmat_vars f)
end

def offset_iclause (off : Int) : iclause t → iclause t := map_iclause_vars (· + off)
def offset_clause (off : Int) : clause t → clause t := map_clause_vars (· + off)
def offset_matrix (off : Int) : matrix t → matrix t := map_matrix_vars (· + off)

end Ncmatrix

/- ---------------------------------------------------------------------- -/
/- Ncprint: printing nanoCoP matrices and clauses (`thecops.ml`: ncprint). -/
/- Used only by the `copverb` traces.                                     -/
/- ---------------------------------------------------------------------- -/
namespace Ncprint

open Ncmatrix Print HolCore.System
open HolCore.Meson (FolStores)

mutual
partial def pp_print_litmat {t : Type} (S : FolStores) (fi : t → Fmt Unit) :
    litmat t → IO (Fmt Unit)
  | .Lit l => pp_print_lit S l
  | .Mat i m => do
    let mm ← pp_print_matrix S fi m
    pure (do Fmt.openBox 1; fi i; mm; Fmt.closeBox)
partial def pp_print_matrix {t : Type} (S : FolStores) (fi : t → Fmt Unit) (m : matrix t) :
    IO (Fmt Unit) := do
  let cs ← m.mapM (pp_print_iclause S fi)
  pure (pp_with_box 1 (pp_enclose_cut "[" "]" (pp_iter_sp "&" cs)))
partial def pp_print_iclause {t : Type} (S : FolStores) (fi : t → Fmt Unit) (ic : iclause t) :
    IO (Fmt Unit) := do
  let ((i, v), c) := ic
  let nc ← pp_print_nclause S fi c
  pure (do
    Fmt.openBox 1; fi i
    pp_enum "," "{" "}" (v.map pp_print_var); Fmt.printString ":"; Fmt.printSpace
    nc; Fmt.closeBox)
partial def pp_print_nclause {t : Type} (S : FolStores) (fi : t → Fmt Unit) (c : clause t) :
    IO (Fmt Unit) := do
  let ls ← c.mapM (pp_print_litmat S fi)
  pure (pp_with_box 1 (pp_enclose_cut "[" "]" (pp_iter_sp "|" ls)))
end

def pp_print_null {t : Type} (_ : t) : Fmt Unit := pure ()
def pp_print_index (i : Int) : Fmt Unit := pp_enclose "<" ">" (Fmt.printString (toString i))

def string_of_litmat {t : Type} (S : FolStores) (c : litmat t) : IO String :=
  render (pp_print_litmat S pp_print_null c)
def string_of_nclause {t : Type} (S : FolStores) (c : clause t) : IO String :=
  render (pp_print_nclause S pp_print_null c)

/-- `print_matrix_i`: on the std_formatter, then `pp_print_newline`. -/
def print_matrix_i (S : FolStores) (m : matrix Int) : IO Unit := do
  stdQueue (← pp_print_matrix S pp_print_index m)
  stdQueue Fmt.printNewline

end Ncprint


/- ---------------------------------------------------------------------- -/
/- Ncproof: the nanoCoP proof tree (`thecops.ml`: ncproof.ml).            -/
/- ---------------------------------------------------------------------- -/

/- `Lemma | Reduction | Decomposition of 'c*'rd*subs | Extension of 'c*'re*subs`. -/
namespace Ncproof

inductive proof (l c rd re : Type) where
  | Lemma
  | Reduction
  | Decomposition (cl : c) (rd_ : rd) (subs : List (l × proof l c rd re))
  | Extension (cl : c) (re_ : re) (subs : List (l × proof l c rd re))

end Ncproof

/- ---------------------------------------------------------------------- -/
/- Extclause: extension clauses (`thecops.ml`: extclause.ml).             -/
/- ---------------------------------------------------------------------- -/

/- The "beta clause" (left/right split) machinery used when extending into a
   sub-matrix.  Works over `Ncmatrix` at index type `t`. -/
namespace Extclause

open Ncmatrix
open FirstOrder.Utils.List (list_rest concat_map)

/- `litmat_ext`/`clause_ext`: the extension context around a chosen literal. -/
mutual
inductive litmat_ext (v : Type) where
  -- beta clause (left & right), whole clause
  | Litext (claB : clause v × clause v) (claC : clause v)
  -- matrix index, surrounding clause, path in clause
  | Matext (j : Int) (claLR : clause v × clause v) (clext : clause_ext v)
inductive clause_ext (v : Type) where
  -- clause index, surrounding matrix, path in litmat
  | Mk (iv : Int × List v) (matLR : matrix v × matrix v) (lmext : litmat_ext v)
end

instance [Inhabited v] : Inhabited (litmat_ext v) := ⟨.Litext ([], []) []⟩
instance [Inhabited v] : Inhabited (clause_ext v) := ⟨.Mk (default, []) ([], []) default⟩

def offset_iv (off : Int) (iv : Int × List Int) : Int × List Int := (iv.1, iv.2.map (· + off))

mutual
partial def offset_litmat_ext (off : Int) : litmat_ext Int → litmat_ext Int
  | .Litext (claL, claR) claC =>
    .Litext (offset_clause off claL, offset_clause off claR) (offset_clause off claC)
  | .Matext j claLR clext =>
    .Matext j (offset_clause off claLR.1, offset_clause off claLR.2) (offset_clause_ext off clext)
partial def offset_clause_ext (off : Int) : clause_ext Int → clause_ext Int
  | .Mk iv matLR lmext =>
    .Mk (offset_iv off iv) (offset_matrix off matLR.1, offset_matrix off matLR.2)
      (offset_litmat_ext off lmext)
end

/- `claBC_of_litmat_ext`: the beta-clause `claB` and the whole clause `claC`.
   (Specialised to the indexed matrix `Int`, since `Matext` carries an `Int` index.)
   TODO: Understand why the reconstruction chokes on the
   OCaml-nanoCoP version of these functions. -/
mutual
partial def claBC_of_litmat_ext : litmat_ext Int → clause Int × clause Int
  | .Litext (claL, claR) claC => (claL.reverseAux claR, claC)
  | .Matext j (claL, claR) clext =>
    let (matB, matC) := matBC_of_clause_ext clext
    let claLR := claL.reverseAux claR
    (matB ++ claLR, litmat.Mat j matC :: claLR)
partial def matBC_of_clause_ext : clause_ext Int → clause Int × matrix Int
  | .Mk iv (matL, matR) lmext =>
    let (claB, claC) := claBC_of_litmat_ext lmext
    (claB, (iv, claC) :: matL.reverseAux matR)
end

mutual
partial def litext_of_litmat_ext : litmat_ext Int → (clause Int × clause Int) × clause Int
  | .Litext claB claC => (claB, claC)
  | .Matext _ _ clext => litext_of_clause_ext clext
partial def litext_of_clause_ext : clause_ext Int → (clause Int × clause Int) × clause Int
  | .Mk _ _ lmext => litext_of_litmat_ext lmext
end

/- `assert_iclause` / `assert_imatrix` / `assert_matrix`: enumerate every literal
   of the (indexed) matrix together with its extension context.
   WARNING: slightly less efficient version than in nanoCoP
   for easier reconstruction -/
mutual
partial def assert_iclause (matLR : matrix Int × matrix Int) (ivc : iclause Int) :
    List (lit × clause_ext Int) :=
  let (iv, c) := ivc
  ((list_rest c).flatMap (fun (lmpair) =>
    let (lm, claLR) := lmpair
    map_litmat
      (fun l => [(l, litmat_ext.Litext claLR c)])
      (fun im => assert_imatrix claLR im) lm)).map
    (fun (l_lmext) => (l_lmext.1, clause_ext.Mk iv matLR l_lmext.2))
partial def assert_imatrix (claLR : clause Int × clause Int) (jmat : imatrix Int) :
    List (lit × litmat_ext Int) :=
  let (j, mat) := jmat
  ((list_rest mat).flatMap (fun (clapair) =>
    let (cla, matLR) := clapair
    assert_iclause matLR cla)).map
    (fun (l_claext) => (l_claext.1, litmat_ext.Matext j claLR l_claext.2))
end

def assert_matrix (mat : matrix Int) : List (lit × clause_ext Int) :=
  (list_rest mat).flatMap (fun (clapair) =>
    let (cla, matLR) := clapair
    assert_iclause matLR cla)

end Extclause

/- ---------------------------------------------------------------------- -/
/- Ncdatabase: contrapositive store for nanoCoP (`thecops.ml`:            -/
/- ncdatabase.ml).                                                        -/
/- ---------------------------------------------------------------------- -/

/- `contrapositive = clause_ext × fol_term list × bool × int`.  Session-owned. -/
namespace Ncdatabase

open Ncmatrix
open Extclause

/-- position of the literal in matrix, literal arguments, groundness, variable offset -/
abbrev contrapositive := Extclause.clause_ext Int × List Meson.fol_term × Bool × Int

abbrev DB := IO.Ref (List (Int × List contrapositive))

/-- `insert_db db ((p,a), clext)`: compute offset/groundness and store under `p`. -/
def insert_db (db : DB) (pa_clext : Meson.fol_atom × clause_ext Int) : IO Unit := do
  let ((p, a), clext) := pa_clext
  let matC := (matBC_of_clause_ext clext).2
  let off := 1 + Ncmatrix.matrix_max_var (-1) matC
  let ground := Ncmatrix.clause_ground (litext_of_clause_ext clext).2
  let v : contrapositive := (clext, a, ground, off)
  -- OCaml `Hashtbl.find db p |> (v :: ) |> Hashtbl.replace db p`, else `add db p [v]`.
  db.modify (fun l =>
    match l.find? (fun kv => kv.1 = p) with
    | some kv => (p, v :: kv.2) :: l.filter (fun kv => kv.1 ≠ p)
    | none => (p, [v]) :: l)

def matrix2db (db : DB) (m : matrix Int) : IO Unit := do
  let predb := Extclause.assert_matrix m
  db.set []
  for pc in predb.reverse do
    insert_db db pc

def db_entries (db : DB) (lit : Meson.fol_atom) : IO (List contrapositive) := do
  match (← db.get).find? (fun kv => kv.1 = lit.1) with
  | some kv => return kv.2
  | none => return []

end Ncdatabase

/- ---------------------------------------------------------------------- -/
/- Ncsearch: the nanoCoP non-clausal search (`thecops.ml`: ncsearch.ml).  -/
/- ---------------------------------------------------------------------- -/

/- The matrix is `copy_matrix`'d so its index type is `mindex = Int × Int`
   (original-index × copy-key).  `prove_ec` walks the extension-clause context;
   `prove_lit`/`prove_mat`/`prove_litmat`/`prove_clause` are the mutual search. -/
namespace Ncsearch

open Cop (search_opts)
open Ncmatrix
open Extclause
open Ncproof

/-- Copy-indexed matrix index. -/
abbrev mindex := Int × Int
/-- The reconstruction "position": a prefix path plus the residual clause-ext. -/
abbrev position := List ((Int × List Int) × Int) × clause_ext Int
/-- The nanoCoP proof node type. -/
abbrev ncproof := Ncproof.proof (litmat mindex) (clause mindex) (mindex × List Int) position

/-- `unify_vars (sub,off) l1 l2 = Subst.unify_tms sub (map var l1) (map var l2)`. -/
def unify_vars (sub : Subst.t) (l1 l2 : List Int) : IO (Option Subst.t) := do
  match ← Subst.unify_tms sub (l1.map Fol_term.var) (l2.map Fol_term.var) with
  | .ok s => return some s | .error _ => return none

/-- nanoCoP `unify_rename (sub,off) args1 (clext, args2, _, vars)`. -/
def unify_rename (sub : Subst.t) (args1 : List Meson.fol_term)
    (contra : Ncdatabase.contrapositive) : IO (Option (Subst.t × clause_ext Int)) := do
  let (clext, args2, _, vars) := contra
  let off := sub.2
  if vars = 0 then
    match ← Substarray.unify_tms sub.1 args1 args2 with
    | .ok s => return some ((s, off), clext)
    | .error _ => return none
  else
    match ← Substarray.unify_tms_off off sub.1 args1 args2 with
    | .ok s => return some ((s, off + vars), offset_clause_ext off clext)
    | .error _ => return none

/-- epsilon operator on lists
    (`pick f l`: first `Some (f x)` with a re-insertion continuation). -/
def pick (f : α → Option β) (l : List α) : Except String (β × (α → List α)) :=
  let rec go (acc : List α) : List α → Except String (β × (α → List α))
    | x :: xs => (match f x with
                  | some y => .ok (y, fun z => acc.reverseAux (z :: xs))
                  | none => go (x :: acc) xs)
    | [] => .error "pick: no element found"
  go [] l

def nth_clause (i : Int) (c : iclause mindex) : Option (iclause mindex) :=
  if i = c.1.1.1 then some c else none
def nth_matrix (i : Int) : litmat mindex → Option (imatrix mindex)
  | .Lit _ => none
  | .Mat idx m => if i = idx.1 then some (idx, m) else none

def unique (f : α → Option β) (l : List α) : Bool := (l.filterMap f).length = 1

/-- `prove_ec k sub clext mi pi`: solve the extension clause `clext` against `mi`. -/
partial def prove_ec (opt : search_opts) (k : Int) (sub : Subst.t) (clext : clause_ext Int)
    (mi : matrix mindex) (pi : List mindex) :
    IO (Strom (Subst.t × position × iclause mindex × matrix mindex)) := do
  let .Mk (i, v) _ lmext := clext
  -- thecops.ml 1123/1124: assert exactly-one matching clause, and `List.length pi = k`.
  if !(unique (nth_clause i) mi) then throw (IO.userError "prove_ec: assert unique (nth_clause i) mi")
  if pi.length ≠ k then throw (IO.userError "prove_ec: assert List.length pi = k")
  -- thecops.ml 1130: `pick (nth_clause i) mi` raises `failwith` if no clause.
  match pick (nth_clause i) mi with
  | .error e => throw (IO.userError e)
  | .ok (((⟨⟨_, k1⟩, v1⟩, cla1) : iclause mindex), miAB) =>
    let alt1 : Unit → IO (Strom (Subst.t × position × iclause mindex × matrix mindex)) := fun _ => do
      match lmext with
      | .Matext j _ clext' =>
        if pi.contains (j, k1) then
          match ← unify_vars sub v v1 with
          | none => pure Strom.nil
          | some sub2 =>
            -- thecops.ml 1134: `pick (nth_matrix j) cla1` raises `failwith` if no match.
            match pick (nth_matrix j) cla1 with
            | .error e => throw (IO.userError e)
            | .ok ((((⟨_, k1'⟩, mi2) : imatrix mindex)), claDE) => do
              -- thecops.ml 1135/1136: assert unique (nth_matrix j) cla1 and k1 = k1'.
              if !(unique (nth_matrix j) cla1) then
                throw (IO.userError "prove_ec: assert unique (nth_matrix j) cla1")
              if k1 ≠ k1' then throw (IO.userError "prove_ec: assert k1 = k1'")
              let inner ← prove_ec opt k sub2 clext' mi2 pi
              pure (Strom.map (fun r =>
                let (sub3, pos, claB1, mi3) := r
                let (pfx, pofx) := pos
                (sub3, (((i, v1), j) :: pfx, pofx), claB1,
                 miAB (((i, k1), v1), claDE (litmat.Mat (j, k1) mi3))))
                inner)
        else pure Strom.nil
      | _ => pure Strom.nil
    let alt2 : Unit → IO (Strom (Subst.t × position × iclause mindex × matrix mindex)) := fun _ => do
      if pi.contains (i, k1) && v.isEmpty then pure Strom.nil
      else
        let (claB, claC) := claBC_of_litmat_ext lmext
        let index (cla : clause Int) : iclause mindex := (((i, k), v), copy_clause k cla)
        Strom.cons (sub, ([], clext), index claB, miAB (index claC)) Strom.nil
    let a1 ← Strom.cacheIO alt1
    let a2 ← Strom.cacheIO alt2
    Strom.append a1 a2

def cut (p : Bool) (xs ys : Strom α) : IO (Strom α) :=
  if p then Strom.cut xs ys else Strom.append xs ys

/-- The search state carried through `prove_*`. -/
abbrev nst := matrix mindex × List fol_atom × List mindex × List fol_atom × Int

mutual
partial def prove_lit (S : FolStores) (db : Ncdatabase.DB) (opt : search_opts) (sub : Subst.t)
    (st : nst) (lit : lit) : IO (Strom (Subst.t × List fol_atom × (litmat mindex × ncproof))) := do
  let (mi, path, pi, lem, lim) := st
  -- thecops.ml 1164-1166
  if ← copverb.get then
    stdPrintf s!"Lit: {← Print.string_of_lit S (← Subst.inst_lit sub lit)}\n"
    stdPrintf s!"Path: {← Print.string_of_lits S path}\n"
    stdPrintf s!"Lemmas: {← Print.string_of_lits S lem}\n"
  let neglit := Fol_term.negate_lit lit
  let k := pi.length
  -- lemmas
  let lemmas ← (do
    let mut hit := false
    for l in lem do if ← Subst.eq sub lit l then hit := true
    if hit then do
      if ← copverb.get then stdPrintf "lemma\n"
      Strom.cons (sub, lem, (.Lemma : ncproof)) Strom.nil
    else pure Strom.nil)
  -- reductions
  let pathStream ← Strom.ofList path
  let reductions := Strom.filterMap (fun p => do
    if ← copverb.get then stdPrintf s!"Reduction try {← Print.string_of_lit S p}\n"
    match ← Subst.unify sub neglit p with
    | some sub1 => do
      if ← copverb.get then stdPrintf "Reduction works\n"
      pure (some (sub1, lem, (.Reduction : ncproof)))
    | none => pure none) pathStream
  -- extensions
  let entries ← Ncdatabase.db_entries db neglit
  let entryStream ← Strom.ofList entries
  let extensions ← Strom.concatMapM (fun (contra : Ncdatabase.contrapositive) => do
    let (_, args, ground, vars) := contra
    -- thecops.ml 1180
    if ← copverb.get then
      let argStrs ← args.mapM (Print.string_of_fterm S)
      stdPrintf s!"Extension try (for lit {← Print.string_of_lit S (← Subst.inst_lit sub lit)}, args ({",".intercalate argStrs}), lim {lim}, vars {vars})\n"
    if lim < 0 && !ground then pure Strom.nil
    else
      match ← unify_rename sub lit.2 contra with
      | some (sub1, clext) => do
        if ← copverb.get then
          stdPrintf s!"Extension works (for lit {← Print.string_of_lit S (← Subst.inst_lit sub1 lit)}, lim {lim})\n"
          stdPrintf s!"Old/new offsets: {sub.2}/{sub1.2}\n"
        let ecStream ← prove_ec opt k sub1 clext mi pi
        Strom.concatMapM (fun (r : Subst.t × position × iclause mindex × matrix mindex) => do
          let (sub2, pos, ivc, mi1) := r
          let ((i, _v), claB1) := ivc
          if ← copverb.get then stdPrintf s!"Extension clause {← Ncprint.string_of_nclause S claB1} found\n"
          let clStream ← prove_clause S db opt sub2 (mi1, lit :: path, i :: pi, lem, lim - 1) claB1
          pure (Strom.map (fun (r2 : Subst.t × List (litmat mindex × ncproof)) =>
            (r2.1, lit :: lem, (.Extension (litmat.Lit neglit :: claB1) pos r2.2 : ncproof))) clStream))
          ecStream
      | none => pure Strom.nil)
    entryStream
  let c3 ← cut opt.cut3 extensions Strom.nil
  let c2 ← cut opt.cut2 reductions c3
  let c1 ← cut opt.cut1 lemmas c2
  let guarded ← cut (← Subst.ground_lit sub lit) c1 Strom.nil
  pure (Strom.map (fun (r : Subst.t × List fol_atom × ncproof) =>
    (r.1, r.2.1, (litmat.Lit lit, r.2.2))) guarded)
-- decomposition rule
partial def prove_mat (S : FolStores) (db : Ncdatabase.DB) (opt : search_opts) (sub : Subst.t)
    (st : nst) (jmat : imatrix mindex) :
    IO (Strom (Subst.t × List fol_atom × (litmat mindex × ncproof))) := do
  let (mi, path, pi, lem, lim) := st
  let (j, mat1) := jmat
  if ← copverb.get then stdPrintf "prove_mat\n"   -- thecops.ml 1204
  let matStream ← Strom.ofList mat1
  Strom.concatMapM (fun (idxcla : iclause mindex) => do
    let (idx, cla1) := idxcla
    if ← copverb.get then stdPrintf s!"Decomposition chose: {← Ncprint.string_of_nclause S cla1}\n"
    let i := idx.1
    let clStream ← prove_clause S db opt sub (mi, path, i :: j :: pi, lem, lim) cla1
    pure (Strom.map (fun (r : Subst.t × List (litmat mindex × ncproof)) =>
      (r.1, lem, (litmat.Mat j mat1, (.Decomposition cla1 idx r.2 : ncproof)))) clStream))
    matStream
partial def prove_litmat (S : FolStores) (db : Ncdatabase.DB) (opt : search_opts) (sub : Subst.t) (st : nst) :
    litmat mindex → IO (Strom (Subst.t × List fol_atom × (litmat mindex × ncproof)))
  | .Lit l => prove_lit S db opt sub st l
  | .Mat idx m => prove_mat S db opt sub st (idx, m)
partial def prove_clause (S : FolStores) (db : Ncdatabase.DB) (opt : search_opts) (sub : Subst.t)
    (st : nst) : clause mindex → IO (Strom (Subst.t × List (litmat mindex × ncproof)))
  | lm :: cla => do
    let (mi, path, pi, _lem, lim) := st
    let check (ls : List fol_atom) : IO Bool := do
      for x in ls do for pl in path do if ← Subst.eq sub x pl then return true
      return false
    let regularity ←
      if opt.improved_regularity then check (clause_lits (lm :: cla))
      else (match lm with | .Mat _ _ => pure false | .Lit l => check (l :: clause_lits cla))
    if regularity then do
      if ← copverb.get then stdPrintf "regularity\n"
      pure Strom.nil
    else do
      let lmStream ← prove_litmat S db opt sub st lm
      Strom.concatMapM (fun (r : Subst.t × List fol_atom × (litmat mindex × ncproof)) => do
        let (sub1, lem1, prf1) := r
        let clStream ← prove_clause S db opt sub1 (mi, path, pi, lem1, lim) cla
        pure (Strom.map (fun (r2 : Subst.t × List (litmat mindex × ncproof)) =>
          (r2.1, prf1 :: r2.2)) clStream))
        lmStream
  | [] => do
    if ← copverb.get then stdPrintf "axiom\n"
    Strom.cons (sub, ([] : List (litmat mindex × ncproof))) Strom.nil
end

end Ncsearch

/- ---------------------------------------------------------------------- -/
/- Ncrecon: nanoCoP proof reconstruction into HOL                         -/
/- (`thecops.ml`: ncrecon.ml).                                            -/
/- ---------------------------------------------------------------------- -/

/- `bot_of_proof` turns the nanoCoP proof tree into `... |- F`.  Reuses the HOL
   kernel derived rules and `FirstOrder.Mapping`.  `copverb` traces dropped. -/
namespace Ncrecon

open Ncmatrix
open Ncproof
open Extclause
open Ncsearch (mindex position ncproof)
open FirstOrder.Utils.List (nth_rest)

/-- Given a theorem `|- p1 \/ ... \/ pn` as well as theorems
    `p1 |- c`, ..., `pn |- c`, return `|- c`.
    The conclusion of all proofs has to be the same. -/
partial def DISJ_CASES_LIST (B : BoolThms) (th : thm) : List thm → Except String thm
  | [] => .error "DISJ_CASES_LIST"
  | [p] => do B.MP (← B.DISCH (concl th) p) th
  | [p1, p2] => B.DISJ_CASES th p1 p2
  | p :: ps => do
    let (_, r) ← Basics.dest_disj (concl th)
    let assumed ← ASSUME r
    let rest ← DISJ_CASES_LIST B assumed ps
    B.DISJ_CASES th p rest

/-- `CONTRADICTION x y`: from `~a` and `a` (either order) derive `F`. -/
def CONTRADICTION (B : BoolThms) (x y : thm) : IO (Except String thm) := do
  let xc := concl x; let yc := concl y
  if ← copverb.get then stdPrintf s!"contra: {← HolCore.Printer.string_of_term xc} with {← HolCore.Printer.string_of_term yc}\n"
  return (if is_neg xc && !(is_neg yc) then do B.MP (← B.NOT_ELIM x) y
    else if is_neg yc && !(is_neg xc) then do B.MP (← B.NOT_ELIM y) x
    else .error "no contradiction found")

def flip_neg (tm : term) : Except String term :=
  if is_neg tm then dest_neg tm else mk_neg tm

/-- `nth_disj j th`: assume each disjunct of `concl th`, return the `j`-th plus rest. -/
def nth_disj (j : Int) (th : thm) : IO (Except String (thm × (List thm × List thm))) := do
  if ← copverb.get then stdPrintf s!"nth_disj {j} {← HolCore.Printer.string_of_term (concl th)}\n"
  return nth_disj_core j th
where nth_disj_core (j : Int) (th : thm) : Except String (thm × (List thm × List thm)) := do
  let mut djs : List thm := []
  for d in disjuncts (concl th) do
    djs := djs ++ [← ASSUME d]
  nth_rest j.toNat djs

def nth_conj (B : BoolThms) (i : Int) (th : thm) : IO (Except String thm) := do
  if ← copverb.get then stdPrintf s!"nth_conj {i} {← HolCore.Printer.string_of_term (concl th)}\n"
  return match (B.CONJUNCTS th)[i.toNat]? with | some t => .ok t | none => .error "nth_conj"

def inst_var (S : FolStores) (sub : Substarray.t) (ty : hol_type) (v : Int) :
    IO (Except String term) := do
  let ftm ← Substarray.inst_tm sub (.Fvar v)
  FirstOrder.Mapping.hol_of_term S ty ftm

/-- `spec_vars sub vs th`: `SPEC` the reconstructed HOL witnesses `vs` into `th`. -/
def spec_vars (S : FolStores) (B : BoolThms) (sub : Substarray.t) (vs : List Int) (th : thm) :
    IO (Except String thm) := do
  -- thecops.ml 1291-1293
  if ← copverb.get then
    stdPrintf s!"spec_vars: |vars| = {vs.length}, th = {← HolCore.Printer.string_of_term (concl th)}\n"
  let tys := (strip_forall (concl th)).1.map type_of
  if tys.length ≠ vs.length then return .error "spec_vars: arity"
  else
    let mut cur := th
    for (ty, v) in tys.zip vs do
      match ← inst_var S sub ty v with
      | .error e => return .error e
      | .ok w => match B.SPEC w cur with | .ok t => cur := t | .error e => return .error e
    return .ok cur

structure recon_data where
  problem : thm
  mapping : List (Int × Int)
  sub : Substarray.t

/- Build the `(matrix-index → conjunct/disjunct-position)` mapping. -/
mutual
partial def clause_index_mapping (cl : clause mindex) : List (Int × Int) :=
  ((cl.zipIdx).map (fun (lm, idx) =>
    match lm with
    | .Lit _ => []
    | .Mat jm m => (jm.1, idx) :: matrix_index_mapping m)).flatten
partial def matrix_index_mapping (mat : matrix mindex) : List (Int × Int) :=
  ((mat.zipIdx).map (fun (ivc, idx) =>
    let ((i, _v), cl) := ivc
    (i.1, idx) :: clause_index_mapping cl)).flatten
end

def mk_recon_data (problem : thm) (mat : matrix mindex) (sub : Substarray.t) : recon_data :=
  { problem := problem, mapping := matrix_index_mapping mat, sub := sub }

/-- `prefix_problem data prefix`: descend the problem theorem along the prefix. -/
def prefix_problem (S : FolStores) (B : BoolThms) (data : recon_data)
    (pfx : List ((Int × List Int) × Int)) : IO (Except String thm) := do
  -- thecops.ml 1322: `let rel i = List.assoc i data.mapping` raises Not_found.
  let rel (i : Int) : Except String Int := HolCore.Lib.assoc i data.mapping
  let mut cur := data.problem
  for ((i, v), j) in pfx do
    match rel i with
    | .error e => return .error e
    | .ok ri =>
    match ← nth_conj B ri cur with
    | .error e => return .error e
    | .ok cj => match ← spec_vars S B data.sub v cj with
      | .error e => return .error e
      | .ok sv => match rel j with
        | .error e => return .error e
        | .ok rj => match ← nth_disj rj sv with
          | .error e => return .error e
          | .ok (dj, _) => cur := dj
  return .ok cur

/-- The nanoCoP proof-node pair type carried by the search. -/
abbrev nprfnode := litmat mindex × ncproof

mutual
/-- `eat_proofs data (lem, prfs) ths`: fold the proofs, one per `th` in `ths`. -/
partial def eat_proofs (S : FolStores) (B : BoolThms) (data : recon_data)
    (lempr : List (term × thm) × List nprfnode) (ths : List thm) :
    IO (Except String ((List (term × thm) × List nprfnode) × List thm)) := do
  let mut lem := lempr.1
  let mut prfs := lempr.2
  let mut bots : List thm := []
  for th in ths do
    match prfs with
    | prf :: rest =>
      match ← bot_of_proof S B data lem th prf with
      | .error e => return .error e
      | .ok bot => lem := (concl th, bot) :: lem; prfs := rest; bots := bots ++ [bot]
    | [] => return .error "eat_proofs"
  return .ok ((lem, prfs), bots)
partial def bot_of_clause_ext (S : FolStores) (B : BoolThms) (data : recon_data)
    (clext : clause_ext Int) (acc : List (term × thm) × List nprfnode) (th : thm) :
    IO (Except String ((List (term × thm) × List nprfnode) × thm)) := do
  let .Mk (i, v) (matL, _matR) lmext := clext
  -- thecops.ml 1338: `let i' = List.assoc i data.mapping` raises Not_found.
  match HolCore.Lib.assoc i data.mapping with
  | .error e => return .error e
  | .ok i' =>
  let _ := matL
  match ← nth_conj B i' th with
  | .error e => return .error e
  | .ok cj => match ← spec_vars S B data.sub v cj with
    | .error e => return .error e
    | .ok thi => bot_of_litmat_ext S B data acc thi lmext
partial def bot_of_litmat_ext (S : FolStores) (B : BoolThms) (data : recon_data)
    (acc : List (term × thm) × List nprfnode) (thi : thm) (lmext : litmat_ext Int) :
    IO (Except String ((List (term × thm) × List nprfnode) × thm)) := do
  match lmext with
  | .Litext (claL, _claR) _claC =>
    let j := claL.length
    match ← nth_disj (Int.ofNat j) thi with
    | .error e => return .error e
    | .ok (thj, (thL, thR)) => do
      match ← eat_proofs S B data acc thL with
      | .error e => return .error e
      | .ok (acc1, botsL) =>
        match ← eat_proofs S B data acc1 thR with
        | .error e => return .error e
        | .ok (acc2, botsR) => do
          -- thecops.ml 1348-1349
          if ← copverb.get then
            stdPrintf s!"bot_of_litmat_ext: thi = {← HolCore.Printer.string_of_thm thi}\n"
          match flip_neg (concl thj) with
          | .error e => return .error e
          | .ok fn => match ASSUME fn with
            | .error e => return .error e
            | .ok assumed => match ← CONTRADICTION B thj assumed with
              | .error e => return .error e
              | .ok botj => match DISJ_CASES_LIST B thi (botsL ++ botj :: botsR) with
                | .error e => return .error e
                | .ok r => return .ok (acc2, r)
  | .Matext j (claL, _claR) clext =>
    -- thecops.ml 1354: `let j' = List.assoc j data.mapping` raises Not_found.
    match HolCore.Lib.assoc j data.mapping with
    | .error e => return .error e
    | .ok j' =>
    let _ := claL
    match ← nth_disj j' thi with
    | .error e => return .error e
    | .ok (thj, (thL, thR)) => do
      match ← bot_of_clause_ext S B data clext acc thj with
      | .error e => return .error e
      | .ok (acc1, botj) =>
        match ← eat_proofs S B data acc1 thL with
        | .error e => return .error e
        | .ok (acc2, botsL) =>
          match ← eat_proofs S B data acc2 thR with
          | .error e => return .error e
          | .ok (acc3, botsR) =>
            match DISJ_CASES_LIST B thi (botsL ++ botj :: botsR) with
            | .error e => return .error e
            | .ok r => return .ok (acc3, r)
partial def bot_of_proof (S : FolStores) (B : BoolThms) (data : recon_data)
    (lem : List (term × thm)) (th : thm) (prf : nprfnode) : IO (Except String thm) := do
  match prf with
  | (.Mat j _mat, .Decomposition _cla ⟨⟨i, _k⟩, v⟩ prfs) => do
    -- thecops.ml 1364: `let i' = List.assoc i data.mapping` raises Not_found.
    match HolCore.Lib.assoc i data.mapping with
    | .error e => return .error e
    | .ok i' => do
    let _ := j
    -- thecops.ml 1367-1368
    if ← copverb.get then stdPrintf s!"Decomposition {i'}: {← HolCore.Printer.string_of_term (concl th)}\n"
    match ← nth_conj B i' th with
    | .error e => return .error e
    | .ok cj => match ← spec_vars S B data.sub v cj with
      | .error e => return .error e
      | .ok thi => do
        let djs := disjuncts (concl thi)
        match (djs.mapM ASSUME : Except String (List thm)) with
        | .error e => return .error e
        | .ok djThs =>
          match ← eat_proofs S B data (lem, prfs) djThs with
          | .error e => return .error e
          | .ok (_, bots) => return (DISJ_CASES_LIST B thi bots)
  | (.Lit lit, prf) => do
    let ilit ← Substarray.inst_lit data.sub lit
    match ← FirstOrder.Mapping.hol_of_literal S ilit with
    | .error e => return .error e
    | .ok liti => do
      -- thecops.ml 1376-1377
      if ← copverb.get then stdPrintf s!"bot_of_proof: lit = {← HolCore.Printer.string_of_term liti}\n"
      match prf with
      | .Reduction =>
        (match flip_neg liti with
         | .error e => return .error e
         | .ok fn => match ASSUME fn with
           | .error e => return .error e
           | .ok assumed => CONTRADICTION B th assumed)
      | .Lemma =>
        return (match HolCore.Lib.assoc liti lem with | .ok t => .ok t | .error _ => .error "Lemma: not found")
      | .Extension _ (pfx, pofx) prfs => do
        match ← prefix_problem S B data pfx with
        | .error e => return .error e
        | .ok prefix_th => do
          if ← copverb.get then stdPrintf s!"prefix_th = {← HolCore.Printer.string_of_thm prefix_th}\n"   -- 1384
          match ← bot_of_clause_ext S B data pofx (lem, prfs) prefix_th with
          | .error e => return .error e
          | .ok (_, bot) => return (do B.MP (← B.DISCH (concl th) bot) th)
      | _ => return .error "bot_of_proof: not a well-formed proof"
  | _ => return .error "bot_of_proof: not a well-formed proof"
end

end Ncrecon

/- ---------------------------------------------------------------------- -/
/- Nanocop: the nanoCoP entry points                                      -/
/- (`thecops.ml`: Nanocop entry points).                                  -/
/- ---------------------------------------------------------------------- -/
namespace Nanocop

open Cop (search_opts strategy)
open Ncmatrix
open Ncsearch (mindex ncproof)

/-- Everything the nanoCoP driver needs (Session-supplied). -/
structure NanocopDeps where
  S : FolStores
  P : Meson.MesonPths
  mem : Meson.ContraposCache
  db : Ncdatabase.DB
  E : Meson.EqAxPths
  Emeson : Meson.EqAxPths
  hashek : Hashek.HashekThms
  D : Meson.MesonTacDeps
  notTFimp : IO (Except String thm)
  CONJ_ASSOC : thm                     -- |- a /\ (b /\ c) <=> (a /\ b) /\ c
  DISJ_ASSOC : thm                     -- |- a \/ (b \/ c) <=> (a \/ b) \/ c

/-- `start mat opt lim`: locate the hashek clause and search it. -/
def start (dp : NanocopDeps) (mat : matrix Int) (opt : search_opts) (lim : Int) :
    IO (Option (Substarray.t × (litmat mindex × ncproof))) := do
  if ← copverb.get then stdPrintf s!"Start {lim + 1}\n"   -- thecops.ml 1408
  let mati := copy_matrix 0 mat
  let sub0 ← Subst.empty 1000000
  -- thecops.ml 1411: plain `let hashek = Mapping.fol_of_literal ..`; a failure
  -- raises out of `start`/`deepen`/`strategy` rather than becoming `none`.
  match ← FirstOrder.Mapping.fol_of_literal dp.S [] [] dp.hashek.hashek_tm with
  | .error e => throw (IO.userError e)
  | .ok hashek =>
    let matStream ← Strom.ofList mati
    let picked := Strom.filterMap (fun (ivc : iclause mindex) => do
      let (idx, cla) := ivc
      match cla with
      | [litmat.Lit lit] =>
        if lit == hashek then do
          let clStream ← Ncsearch.prove_clause dp.S dp.db opt sub0
                           (mati, [], [(idx.1.1, 0)], [], lim) cla
          match ← Strom.nextOpt clStream with
          | some (sub, prfs) => pure (some (sub,
              (Ncproof.proof.Decomposition cla idx prfs : ncproof)))
          | none => pure none
        else pure none
      | _ => pure none) matStream
    match ← Strom.nextOpt picked with
    | some (sub, prf) => return some (sub.1, (litmat.Mat (-1, 0) mati, prf))
    | none => return none

/-- `fol_of_thm th = fol_of_form [] (freesl (hyp th)) (concl th)`. -/
def fol_of_thm (dp : NanocopDeps) (th : thm) : IO (Except String Meson.fol_form) :=
  FirstOrder.Mapping.fol_of_form dp.S [] (freesl (hyp th)) (concl th)

/- ncproof.ml: printing a nanoCoP proof (for the `copverb` trace). -/
open HolCore.System in
mutual
partial def pp_print_proof (S : FolStores) (node : litmat mindex × ncproof) : IO (Fmt Unit) := do
  let (lit, prf) := node
  let l ← Ncprint.string_of_litmat S lit       -- string_of_inst_litmat ignores sub
  let p ← pp_print_prf S prf
  pure (do Fmt.openVBox 2; Fmt.printString l; Fmt.printString " "; p; Fmt.closeBox)
partial def pp_print_prf (S : FolStores) : ncproof → IO (Fmt Unit)
  | .Reduction => pure (Fmt.printString "Red")
  | .Lemma => pure (Fmt.printString "Lem")
  | .Decomposition cl _ prfs => do
    let c ← Ncprint.string_of_nclause S cl
    let ps ← pp_print_proofs S prfs
    pure (do Fmt.printString ("Dec " ++ c); ps)
  | .Extension cl _ prfs => do
    let c ← Ncprint.string_of_nclause S cl
    let ps ← pp_print_proofs S prfs
    pure (do Fmt.printString ("Ext " ++ c); ps)
partial def pp_print_proofs (S : FolStores) (prfs : List (litmat mindex × ncproof)) :
    IO (Fmt Unit) := do
  let ps ← prfs.mapM (pp_print_proof S)
  pure (for x in ps do Fmt.printBreak 0 0; x)
end

/-- `Ncproof.print_proof_def sub prf`: on the std_formatter, then a newline. -/
def print_proof_def (S : FolStores) (prf : litmat mindex × ncproof) : IO Unit := do
  stdQueue (← pp_print_proof S prf)
  stdQueue HolCore.System.Fmt.printNewline

/-- `NANOCOP_DEEPEN opt ths`: prove `F` from `ths` by nanoCoP. -/
def NANOCOP_DEEPEN (B : BoolThms) (dp : NanocopDeps) (opt : search_opts) (ths : List thm) :
    IO (Except String thm) := do
  -- thecops.ml 1430-1433
  if ← copverb.get then
    stdPrintf "NANOCOP_DEEPEN with ths:\n"
    for th in ths do stdPrintf s!"  th: {← HolCore.Printer.string_of_thm th}\n"
  FirstOrder.Mapping.reset_vars dp.S
  -- thecops.ml 1434: `Mapping.reset_consts()` runs in sequence; propagate failure.
  match ← FirstOrder.Mapping.reset_consts dp.S with
  | .error e => return .error e
  | .ok _ =>
  -- gen_eq = map GEN_ALL o create_eq_axs sym o map concl
  -- Right-to-left: `map concl` runs FIRST, then `create_eq_axs`, then
  -- `map GEN_ALL`.  The middle stage is IO-valued while `map GEN_ALL` is only
  -- `Except`-valued, so the outer stage is lifted into IO with `pure` to let the
  -- two join with `oIO`; the total innermost stage then rides on plain `o`.
  let genAll : List thm → IO (Except String (List thm)) :=
    fun axs => pure (axs.mapM B.GEN_ALL)
  let gen_eq : List thm → IO (Except String (List thm)) :=
    genAll oIO Equality.create_eq_axs B dp.E dp.Emeson opt.add_eq_symmetry
      o List.map concl
  let ths0 := if ths.any (fun th => concl th == dp.hashek.hashek_tm) then ths
              else dp.hashek.hashek_thm :: ths
  match ← gen_eq ths0 with
  | .error e => return .error e
  | .ok eqs =>
    let ths' := setify (ths0 ++ eqs)
    match end_itlistM (fun a b => B.CONJ a b) ths' with
    | .error e => return .error e
    | .ok th =>
      match ← fol_of_thm dp th with
      | .error e => return .error e
      | .ok fol =>
        let mat := index_matrix_top (matrix_of_form fol)
        if ← copverb.get then
          stdPrintf "Matrix:\n"
          Ncprint.print_matrix_i dp.S mat
        Ncdatabase.matrix2db dp.db mat
        if ← copverb.get then stdPrintf "Matrix loaded.\n"
        let (sub, prfs) ← strategy opt (start dp mat)
        if ← copverb.get then
          stdPrintf "Theorem\n"
          print_proof_def dp.S prfs
        let data := Ncrecon.mk_recon_data th (copy_matrix 0 mat) sub
        match ← Ncrecon.bot_of_proof dp.S B data [] th prfs with
        | .error e => return .error e
        | .ok bot =>
          if ← copverb.get then
            stdPrintf "Reconstruction:\n"
            stdQueue (← HolCore.Printer.pp_print_thm bot)   -- print_thm: unflushed
          -- assert (set_eq (hyp bot) (hyp th)); assert (concl bot = `F`);
          if !(set_eq (hyp bot) (hyp th)) then return .error "Assert_failure"
          match ← HolCore.Parser.parse_term "F" with
          | .error e => return .error e
          | .ok f => if concl bot == f then return .ok bot else return .error "Assert_failure"

/-- Debugging tactic (`PRINT_TAC`, thecops.ml 1462): print the goal (on the
    std_formatter, unflushed, as `print_goal`) when `copverb` is set. -/
def PRINT_TAC : tactic := fun g => do
  if ← copverb.get then stdQueue (← Tactics.pp_print_goal g)
  Tactics.ALL_TAC g

/-- `PRINT_ID_TAC s` (thecops.ml 1463): `print_endline s` (straight to stdout,
    past the formatter), then `PRINT_TAC`. -/
def PRINT_ID_TAC (s : String) : tactic := fun g => do
  if ← copverb.get then IO.println s
  PRINT_TAC g

/-- IO `CHANGED_CONV`: run `c`, failing if it left the term unchanged. -/
def changedConvIO (c : ioconv) : ioconv := fun tm => do
  match ← c tm with
  | .error e => return .error e
  | .ok th => match dest_eq (concl th) with
              | .ok (l, r) => if aconv l r then return .error "CHANGED_CONV" else return .ok th
              | .error _ => return .ok th

/-- `PREPARE_NANOCOP_TAC ths`: `PREPARE_COP_TAC` then nanoCoP-specific assoc prep. -/
def PREPARE_NANOCOP_TAC (B : BoolThms) (dp : NanocopDeps) (ths : List thm) : tactic :=
  let assocDisj : thm → IO (Except String thm) := fun th =>
    match Canon.ASSOC_CONV B dp.DISJ_ASSOC with
    | .ok c => HolCore.Simp.convRuleIO (HolCore.Simp.depthConvIO (changedConvIO c)) th
    | .error e => pure (.error e)
  let assocConj : thm → IO (Except String thm) := fun th =>
    match Canon.ASSOC_CONV B dp.CONJ_ASSOC with
    | .ok c => HolCore.Simp.convRuleIO (HolCore.Simp.depthConvIO (changedConvIO c)) th
    | .error e => pure (.error e)
  Tactics.EVERY B [
    Prepare.PREPARE_COP_TAC B dp.D dp.hashek dp.notTFimp ths,
    Tactics.RULE_ASSUM_TAC B assocDisj,
    Tactics.RULE_ASSUM_TAC B assocConj,
    Tactics.REPEAT B (Tactics.FIRST_X_ASSUM B (fun th => Tactics.SUBST_VAR_TAC B th)) ]

def PURE_NANOCOP (B : BoolThms) (dp : NanocopDeps) (opt : search_opts) : tactic := fun g => do
  let refute : tactic := fun (asl, w) => do
    match ← NANOCOP_DEEPEN B dp opt (asl.map (fun p => p.2)) with
    | .error e => return .error e
    | .ok th => Tactics.ACCEPT_TAC B th (asl, w)
  (ORELSE (Tactics.FIRST_ASSUM (fun cth => Tactics.CONTR_TAC B cth)) refute) g

def GEN_NANOCOP_TAC (B : BoolThms) (dp : NanocopDeps) (opt : search_opts) (ths : List thm) :
    tactic := THEN B (PREPARE_NANOCOP_TAC B dp ths) (PURE_NANOCOP B dp opt)

def NANOCOP_TAC (B : BoolThms) (dp : NanocopDeps) (ths : List thm) : tactic :=
  GEN_NANOCOP_TAC B dp Cop.search_opts_default ths

def NANOCOP (B : BoolThms) (dp : NanocopDeps) (ths : List thm) (tm : term) :
    IO (Except String thm) := Tactics.prove B tm (NANOCOP_TAC B dp ths)

end Nanocop

end HolCore.TheCops
