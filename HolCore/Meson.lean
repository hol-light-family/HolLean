/- File: Meson.lean
Version of the MESON procedure a la PTTP. Various search options.
Original: John Harrison, University of Cambridge Computer Laboratory
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
import HolCore.Theorems
import HolCore.IndDefs
import HolCore.Classic
import HolCore.Trivia
import HolCore.Canon

open HolCore.Kernel HolCore.Basics HolCore.Lib HolCore.Bool HolCore.Equal
     HolCore.Drule HolCore.Tactics HolCore.Itab HolCore.Simp HolCore.Parser
     HolCore.Theorems HolCore.IndDefs HolCore.Classic HolCore.Trivia HolCore.Canon

namespace HolCore.Meson

set_option maxRecDepth 4000

/- ---------------------------------------------------------------------- -/
/- Some parameters controlling MESON behaviour.                           -/
/- ---------------------------------------------------------------------- -/

initialize meson_depth : IO.Ref Bool ← IO.mkRef false   -- Use depth not inference bound.

initialize meson_prefine : IO.Ref Bool ← IO.mkRef true  -- Use Plaisted's positive refinement.

initialize meson_dcutin : IO.Ref Int ← IO.mkRef 1      -- Min size for d-and-c optimization cut-in.

initialize meson_skew : IO.Ref Int ← IO.mkRef 3        -- Skew proof bias (one side is <= n / skew)

initialize meson_brand : IO.Ref Bool ← IO.mkRef false   -- Use Brand transformation

initialize meson_split_limit : IO.Ref Int ← IO.mkRef 8 -- Limit of case splits before MESON proper

initialize meson_chatty : IO.Ref Bool ← IO.mkRef false  -- Old-style verbose MESON output

/-- The values of the parameters above, read when a MESON call starts and
    passed to the search functions. -/
structure MesonConfig where
  depth       : Bool := false
  prefine     : Bool := true
  dcutin      : Int  := 1
  skew        : Int  := 3
  brand       : Bool := false
  splitLimit  : Int  := 8
  chatty      : Bool := false
  deriving Inhabited

/-- Read the current parameter values. -/
def readConfig : IO MesonConfig := do
  return { depth := ← meson_depth.get, prefine := ← meson_prefine.get,
           dcutin := ← meson_dcutin.get, skew := ← meson_skew.get,
           brand := ← meson_brand.get, splitLimit := ← meson_split_limit.get,
           chatty := ← meson_chatty.get }

/- ---------------------------------------------------------------------- -/
/- Prolog exception.                                                      -/
/- ---------------------------------------------------------------------- -/

-- `exception Cut`: the search functions return `.error "Cut"`.

/-- Variable/constant offset increment (`offinc`). -/
def offinc : Int := 10000

/- ---------------------------------------------------------------------- -/
/- Shadow syntax for FOL terms in NNF. Functions and predicates have      -/
/- numeric codes, and negation is done by negating the predicate code.    -/
/- ---------------------------------------------------------------------- -/

/-- Shadow syntax for FOL terms in NNF. Functions and predicates have
    numeric codes, and negation is done by negating the predicate code. -/
inductive fol_term where
  | Fvar (n : Int)
  | Fnapp (f : Int) (args : List fol_term)
  deriving BEq, Inhabited, Repr

/-- A FOL atom: predicate code paired with argument terms. -/
abbrev fol_atom := Int × List fol_term

/-- Shadow syntax for FOL formulas (in NNF). -/
inductive fol_form where
  | Atom (a : fol_atom)
  | Conj (l r : fol_form)
  | Disj (l r : fol_form)
  | Forallq (v : Int) (bod : fol_form)
  deriving BEq, Inhabited, Repr

/- ---------------------------------------------------------------------- -/
/- Type for recording a MESON proof tree.                                 -/
/- ---------------------------------------------------------------------- -/

/-- A recorded MESON proof tree node:
    `Subgoal(atom, subgoals, (rulenumber, thm), offset, localinsts)`. -/
inductive fol_goal where
  | Subgoal (a : fol_atom) (gs : List fol_goal) (rule : Int × thm)
            (offset : Int) (locin : List (fol_term × Int))
  deriving Inhabited

/- ---------------------------------------------------------------------- -/
/- General MESON procedure, using assumptions and with settable limits.   -/
/- ---------------------------------------------------------------------- -/

/-- Negate a clause literal (negate the predicate code). -/
def mk_negated (pa : fol_atom) : fol_atom := (-pa.1, pa.2)

/- ---------------------------------------------------------------------- -/
/- Like partition, but with short-circuiting for special situation.       -/
/- ---------------------------------------------------------------------- -/

/-- `qpartition p m l`: like `partition p`, but short-circuits: returns the
    prefix of `l` up to `m` split by `p`, sharing the tail `m` unchanged.
    OCaml raises `Unchanged` for sharing; we return `Option` (none = unchanged,
    i.e. the whole thing is `([], l)` from the caller's view).

    STRUCTURAL vs PHYSICAL equality - EQUIVALENT HERE, by the following argument.
    meson.ml 80 tests `l == m`, OCaml's POINTER identity; we test structural
    equality, which is true strictly more often, so in principle we could stop
    EARLIER and leave elements unpartitioned.  We cannot, because the sole caller
    (meson.ml 339 / Meson.lean 237) passes `oldinsts` and `newinsts`, and
    `newinsts` is built by CONSING onto `oldinsts` - so `oldinsts` is a genuine
    suffix.  A suffix is determined by its LENGTH, and two lists of different
    lengths are never structurally equal, so the only suffix that can compare
    equal to `oldinsts` is `oldinsts` itself: exactly the boundary pointer
    identity finds.  If `m` were NOT a suffix of `l`, both versions run to `[]`
    and return `([], l)` alike. -/
private partial def qpartitionAux {α : Type} [BEq α] (p : α → Bool) (m : List α) :
    List α → Option (List α × List α)
  | l =>
    if l == m then none
    else match l with
      | [] => none
      | h :: t =>
        if p h then
          match qpartitionAux p m t with
          | some (yes, no) => some (h :: yes, no)
          | none => some ([h], t)
        else
          match qpartitionAux p m t with
          | some (yes, no) => some (yes, h :: no)
          | none => some ([], l)  -- p h false, tail unchanged: yes=[], no=l

/-- `qpartition p m l`. -/
def qpartition {α : Type} [BEq α] (p : α → Bool) (m l : List α) : List α × List α :=
  match qpartitionAux p m l with
  | some res => res
  | none => ([], l)

/- ---------------------------------------------------------------------- -/
/- Versions of shadow syntax operations with variable bumping.            -/
/- ---------------------------------------------------------------------- -/

/-- Is FOL variable `v` free in `tm`? -/
partial def fol_free_in (v : Int) (tm : fol_term) : Bool :=
  match tm with
  | .Fvar x => x == v
  | .Fnapp _ lis => lis.any (fol_free_in v)

/-- Apply a shadow substitution `theta` (a `(term, var)` assoc, reversed). -/
partial def fol_subst (theta : List (fol_term × Int)) (tm : fol_term) : fol_term :=
  match tm with
  | .Fvar v => rev_assocd v theta tm
  | .Fnapp f args =>
      let args' := qmap (fol_subst theta) args
      if args' == args then tm else .Fnapp f args'

/-- Apply a shadow substitution to an atom. -/
def fol_inst (theta : List (fol_term × Int)) (atm : fol_atom) : fol_atom :=
  let args' := qmap (fol_subst theta) atm.2
  if args' == atm.2 then atm else (atm.1, args')

/-- Substitution with variable bumping by `offset`. -/
partial def fol_subst_bump (offset : Int) (theta : List (fol_term × Int)) (tm : fol_term) :
    fol_term :=
  match tm with
  | .Fvar v =>
      if v < offinc then
        let v' := v + offset
        rev_assocd v' theta (.Fvar v')
      else rev_assocd v theta tm
  | .Fnapp f args =>
      let args' := qmap (fol_subst_bump offset theta) args
      if args' == args then tm else .Fnapp f args'

/-- Instantiate an atom with variable bumping. -/
def fol_inst_bump (offset : Int) (theta : List (fol_term × Int)) (atm : fol_atom) : fol_atom :=
  let args' := qmap (fol_subst_bump offset theta) atm.2
  if args' == atm.2 then atm else (atm.1, args')

/- ---------------------------------------------------------------------- -/
/- Main unification function, maintaining a "graph" instantiation.        -/
/- We implicitly apply an offset to variables in the second term, so this -/
/- is not symmetric between the arguments.                                -/
/- ---------------------------------------------------------------------- -/

/-- `istriv env x t`: is `t` (under `env`) trivially the variable `x`?
    Raises "cyclic" on a cyclic occurrence. -/
partial def istriv (env : List (fol_term × Int)) (x : Int) (t : fol_term) :
    Except String Bool :=
  match t with
  | .Fvar y =>
      if y == x then .ok true
      else
        match rev_assoc y env with
        | .ok t' => istriv env x t'
        | .error _ => .ok false
  | .Fnapp _ args =>
      -- exists (istriv env x) args && failwith "cyclic"
      let rec anyTriv : List fol_term → Except String Bool
        | [] => .ok false
        | a :: rest => do
            let b ← istriv env x a
            if b then .ok true else anyTriv rest
      do
        let found ← anyTriv args
        if found then .error "cyclic" else .ok false

/-- Main unification with implicit offset on the second term's variables. -/
partial def fol_unify (offset : Int) (tm1 tm2 : fol_term)
    (sofar : List (fol_term × Int)) : Except String (List (fol_term × Int)) :=
  match tm1, tm2 with
  | .Fnapp f fargs, .Fnapp g gargs =>
      if f != g then .error ""   -- meson.ml 240: `failwith ""`
      else itlist2M (fun a b s => fol_unify offset a b s) fargs gargs sofar
  | _, .Fvar x =>
      let x' := x + offset
      match rev_assoc x' sofar with
      | .ok tm2' => fol_unify 0 tm1 tm2' sofar
      | .error _ => do
          if ← istriv sofar x' tm1 then .ok sofar
          else .ok ((tm1, x') :: sofar)
  | .Fvar x, _ =>
      match rev_assoc x sofar with
      | .ok tm1' => fol_unify offset tm1' tm2 sofar
      | .error _ => do
          let tm2' := fol_subst_bump offset [] tm2
          if ← istriv sofar x tm2' then .ok sofar
          else .ok ((tm2', x) :: sofar)

/- ---------------------------------------------------------------------- -/
/- Test for equality under the pending instantiations.                    -/
/- ---------------------------------------------------------------------- -/

/-- Test equality of shadow terms under the pending instantiation `insts`. -/
partial def fol_eq (insts : List (fol_term × Int)) (tm1 tm2 : fol_term) : Bool :=
  tm1 == tm2 ||
  match tm1, tm2 with
  | .Fnapp f fargs, .Fnapp g gargs =>
      f == g && (fargs.length == gargs.length) &&
        (List.all (fargs.zip gargs) (fun (a, b) => fol_eq insts a b))
  | _, .Fvar x =>
      match rev_assoc x insts with
      | .ok tm2' => fol_eq insts tm1 tm2'
      | .error _ => (istriv insts x tm1).toOption.getD false
  | .Fvar x, _ =>
      match rev_assoc x insts with
      | .ok tm1' => fol_eq insts tm1' tm2
      | .error _ => (istriv insts x tm2).toOption.getD false

/-- Atom equality under `insts`. -/
def fol_atom_eq (insts : List (fol_term × Int)) (a1 a2 : fol_atom) : Bool :=
  a1.1 == a2.1 && a1.2.length == a2.2.length &&
    List.all (a1.2.zip a2.2) (fun (x, y) => fol_eq insts x y)

/-- Apply a multi-level "graph" instantiation. -/
partial def fol_subst_partial (insts : List (fol_term × Int)) (tm : fol_term) : fol_term :=
  match tm with
  | .Fvar v =>
      match rev_assoc v insts with
      | .ok t => fol_subst_partial insts t
      | .error _ => tm
  | .Fnapp f args => .Fnapp f (args.map (fol_subst_partial insts))

/-- Tease apart local and global instantiations.
    At the moment we also force a full evaluation; should eliminate this. -/
def separate_insts (offset : Int) (oldinsts newinsts : List (fol_term × Int)) :
    List (fol_term × Int) × List (fol_term × Int) :=
  let (locins, globins) := qpartition (fun (p : fol_term × Int) => offset <= p.2) oldinsts newinsts
  if globins == oldinsts then
    (locins.map (fun (t, x) => (fol_subst_partial newinsts t, x)), oldinsts)
  else
    (locins.map (fun (t, x) => (fol_subst_partial newinsts t, x)),
     globins.map (fun (t, x) => (fol_subst_partial newinsts t, x)))

/- ---------------------------------------------------------------------- -/
/- Stateful variable / constant stores                                    -/
/- ---------------------------------------------------------------------- -/

/-- Mutable stores for the term↔code translation.  In OCaml these are the
    `ref`s hidden inside `reset_vars`/`fol_of_var`/… ; here the ref handles
    are bundled and owned by `Session`. -/
structure FolStores where
  vstore   : IO.Ref (List (term × Int))   -- variable → code
  gstore   : IO.Ref (List (term × Int))   -- genvar → bumped code
  vcounter : IO.Ref Int
  cstore   : IO.Ref (List (term × Int))   -- constant → code
  ccounter : IO.Ref Int

/-- Reset the variable stores. -/
def reset_vars (S : FolStores) : IO Unit := do
  S.vstore.set []; S.gstore.set []; S.vcounter.set 0

private def inc_vcounter (S : FolStores) : IO (Except String Int) := do
  let n ← S.vcounter.get
  let m := n + 1
  if m >= offinc then return .error "inc_vcounter: too many variables"
  else do S.vcounter.set m; return .ok n

/-- `fol_of_var v`: code for HOL variable `v` (allocating a fresh code). -/
def fol_of_var (S : FolStores) (v : term) : IO (Except String Int) := do
  let currentvars ← S.vstore.get
  match assoc v currentvars with
  | .ok n => return .ok n
  | .error _ =>
    match ← inc_vcounter S with
    | .error e => return .error e
    | .ok n => do S.vstore.set ((v, n) :: currentvars); return .ok n

/-- `hol_of_var v`: the HOL variable for code `v`, with variable-bumping:
    a bumped code (≥ offinc) gets a fresh genvar of the right type. -/
def hol_of_var (S : FolStores) (v : Int) : IO (Except String term) := do
  let vs ← S.vstore.get
  match rev_assoc v vs with
  | .ok t => return .ok t
  | .error _ =>
    let gs ← S.gstore.get
    match rev_assoc v gs with
    | .ok t => return .ok t
    | .error _ =>
      -- bumped var: base var v mod offinc, looked up in vstore then gstore
      -- (OCaml `hol_of_var v'` = try rev_assoc v' vstore with _ -> rev_assoc v' gstore)
      let v' := v % offinc
      match rev_assoc v' vs with
      | .ok hv' => do
          let gv ← genvar (type_of hv')
          S.gstore.set ((gv, v) :: gs)
          return .ok gv
      | .error _ =>
        match rev_assoc v' gs with
        | .error _ => return .error "hol_of_var"
        | .ok hv' => do
            let gv ← genvar (type_of hv')
            S.gstore.set ((gv, v) :: gs)
            return .ok gv

/-- Reset the constant store to `[(F, 1)]`, counter 2. -/
def reset_consts (S : FolStores) : IO (Except String Unit) := do
  match ← (mk_const "F" [] : IO (Except String term)) with
  | .error e => return .error e
  | .ok false_tm => do S.cstore.set [(false_tm, 1)]; S.ccounter.set 2; return .ok ()

/-- `fol_of_const c`: code for HOL constant/term `c` (allocating fresh). -/
def fol_of_const (S : FolStores) (c : term) : IO (Except String Int) := do
  let currentconsts ← S.cstore.get
  match assoc c currentconsts with
  | .ok n => return .ok n
  | .error _ => do
      let n ← S.ccounter.get
      S.ccounter.set (n + 1)
      S.cstore.set ((c, n) :: currentconsts)
      return .ok n

/-- `hol_of_const c`: the HOL term for constant code `c`. -/
def hol_of_const (S : FolStores) (c : Int) : IO (Except String term) := do
  let cs ← S.cstore.get
  return rev_assoc c cs

/- ---------------------------------------------------------------------- -/
/- Translate a term (in NNF) into the shadow syntax.                      -/
/- ---------------------------------------------------------------------- -/

/-- Translate a term (in NNF) into the shadow syntax. -/
partial def fol_of_term (S : FolStores) (env : List term) (consts : List term) (tm : term) :
    IO (Except String fol_term) := do
  if is_var tm && !(mem tm consts) then
    match ← fol_of_var S tm with
    | .ok n => return .ok (.Fvar n)
    | .error e => return .error e
  else
    let (f, args) := strip_comb tm
    if mem f env then return .error "fol_of_term: higher order"
    else
      match ← fol_of_const S f with
      | .error e => return .error e
      | .ok ff => do
          let mut fargs : List fol_term := []
          for a in args do
            match ← fol_of_term S env consts a with
            | .error e => return .error e
            | .ok fa => fargs := fargs ++ [fa]
          return .ok (.Fnapp ff fargs)

/-- Translate an atom into shadow syntax. -/
def fol_of_atom (S : FolStores) (env consts : List term) (tm : term) :
    IO (Except String fol_atom) := do
  let (f, args) := strip_comb tm
  if mem f env then return .error "fol_of_atom: higher order"
  else
    match ← fol_of_const S f with
    | .error e => return .error e
    | .ok ff => do
        let mut fargs : List fol_term := []
        for a in args do
          match ← fol_of_term S env consts a with
          | .error e => return .error e
          | .ok fa => fargs := fargs ++ [fa]
        return .ok (ff, fargs)

/-- Translate a literal (possibly negated atom) into shadow syntax. -/
def fol_of_literal (S : FolStores) (env consts : List term) (tm : term) :
    IO (Except String fol_atom) := do
  match Basics.dest_neg tm with
  | .ok tm' =>
      -- OCaml's `try` spans dest_neg AND fol_of_atom tm'; on either failure
      -- fall back to treating the whole term as an atom.
      match ← fol_of_atom S env consts tm' with
      | .ok (p, a) => return .ok (-p, a)
      | .error _ => fol_of_atom S env consts tm
  | .error _ => fol_of_atom S env consts tm

/-- Translate a formula (in NNF) into shadow syntax. -/
partial def fol_of_form (S : FolStores) (env consts : List term) (tm : term) :
    IO (Except String fol_form) := do
  -- Each `try ... with Failure _ ->` covers its whole branch, recursive
  -- calls included: if the body of a quantifier cannot be translated ("higher
  -- order"), the next alternative is tried, and finally the whole formula is
  -- translated as a literal.
  let forallCase : IO (Except String fol_form) := do
    match Basics.dest_forall tm with
    | .error e => return .error e
    | .ok (v, bod) =>
      match ← fol_of_var S v with
      | .error e => return .error e
      | .ok fv =>
        match ← fol_of_form S (v :: env) (subtract consts [v]) bod with
        | .ok fbod => return .ok (.Forallq fv fbod)
        | .error e => return .error e
  -- `let fl = ... and fr = ...`: OCaml evaluates these left to right.
  let binCase (dest : term → Except String (term × term))
      (mk : fol_form → fol_form → fol_form) : IO (Except String fol_form) := do
    match dest tm with
    | .error e => return .error e
    | .ok (l, r) =>
      match ← fol_of_form S env consts l with
      | .error e => return .error e
      | .ok fl =>
        match ← fol_of_form S env consts r with
        | .ok fr => return .ok (mk fl fr)
        | .error e => return .error e
  match ← forallCase with
  | .ok r => return .ok r
  | .error _ =>
  match ← binCase Basics.dest_conj .Conj with
  | .ok r => return .ok r
  | .error _ =>
  match ← binCase Basics.dest_disj .Disj with
  | .ok r => return .ok r
  | .error _ =>
  match ← fol_of_literal S env consts tm with
  | .ok la => return .ok (.Atom la)
  | .error e => return .error e

/- ---------------------------------------------------------------------- -/
/- Further translation functions for HOL formulas.                        -/
/- ---------------------------------------------------------------------- -/

/-- Translate a shadow term back to HOL. -/
partial def hol_of_term (S : FolStores) (tm : fol_term) : IO (Except String term) := do
  match tm with
  | .Fvar v => hol_of_var S v
  | .Fnapp f args =>
      match ← hol_of_const S f with
      | .error e => return .error e
      | .ok hf => do
          let mut hargs : List term := []
          for a in args do
            match ← hol_of_term S a with
            | .error e => return .error e
            | .ok ha => hargs := hargs ++ [ha]
          return (list_mk_comb hf hargs)

/-- Translate a shadow atom back to HOL. -/
def hol_of_atom (S : FolStores) (p : Int) (args : List fol_term) : IO (Except String term) := do
  match ← hol_of_const S p with
  | .error e => return .error e
  | .ok hp => do
      let mut hargs : List term := []
      for a in args do
        match ← hol_of_term S a with
        | .error e => return .error e
        | .ok ha => hargs := hargs ++ [ha]
      return (list_mk_comb hp hargs)

/-- Translate a shadow literal back to HOL. -/
def hol_of_literal (S : FolStores) (pa : fol_atom) : IO (Except String term) := do
  let (p, args) := pa
  if p < 0 then
    match ← hol_of_atom S (-p) args with
    | .ok a => return (mk_neg a)
    | .error e => return .error e
  else hol_of_atom S p args

/- ---------------------------------------------------------------------- -/
/- MESON search engine                                                    -/
/- ---------------------------------------------------------------------- -/

/-- A tagged contrapositive rule: `((hyps, conc), (rulenum, thm))`. -/
abbrev folRule := (List fol_atom × fol_atom) × (Int × thm)

/-- Ancestor association list: predicate code → applicable rules. -/
abbrev ancestors := List (Int × List folRule)

/-- A goal literal together with its ancestor list. -/
abbrev folState := fol_atom × ancestors

/-- The search "tuple": `(insts, offset, size)`. -/
abbrev tup := List (fol_term × Int) × Int × Int

/-- Check ancestor list for repetition; returns `ancestors` unchanged or fails. -/
def checkan (insts : List (fol_term × Int)) (pa : fol_atom) (anc : ancestors) :
    Except String ancestors :=
  let p' := -pa.1
  let t' : fol_atom := (p', pa.2)
  match assoc p' anc with
  | .error _ => .ok anc   -- Failure "find" → unchanged
  | .ok ours =>
      if ours.any (fun u => fol_atom_eq insts t' u.1.2) then .error "checkan"
      else .ok anc

/- ---------------------------------------------------------------------- -/
/- Insert new goal's negation in ancestor clause, given refinement.       -/
/- ---------------------------------------------------------------------- -/

/-- Insert the new goal's negation into the ancestor clause. -/
def insertan (B : BoolThms) (insts : List (fol_term × Int)) (pa : fol_atom)
    (anc : ancestors) : Except String ancestors := do
  let p' := -pa.1
  let t' : fol_atom := (p', pa.2)
  let (ourancp, otheranc) :=
    match remove (fun (pr : Int × List folRule) => pr.1 == p') anc with
    | .ok (found, rest) => (found, rest)
    | .error _ => ((p', ([] : List folRule)), anc)
  let ouranc := ourancp.2
  if ouranc.any (fun u => fol_atom_eq insts t' u.1.2) then .error "insertan: loop"
  else .ok ((p', (([], t'), (0, B.TRUTH)) :: ouranc) :: otheranc)

/- ---------------------------------------------------------------------- -/
/- Perform basic MESON expansion.                                         -/
/- ---------------------------------------------------------------------- -/

/-- Perform one basic MESON resolution step (bumps `inferences`). -/
def meson_single_expand (inferences : IO.Ref Int) (loffset : Int) (rule : folRule)
    (input : folState × tup) : IO (Except String (List (fol_atom × ancestors) × tup)) := do
  let ((g, ancestorsL), (insts, offset, size)) := input
  let ((hyps, conc), _tag) := rule
  match rev_itlist2M (fun a b s => fol_unify loffset a b s) g.2 conc.2 insts with
  | .error e => return .error e
  | .ok allins =>
    let (locin, globin) := separate_insts offset insts allins
    -- mk_ihyp for each hyp
    let mut newhyps : List (fol_atom × ancestors) := []
    let mut ok := true
    let mut errmsg := ""
    for h in hyps do
      if ok then
        let h' := fol_inst_bump offset locin h
        match checkan insts h' ancestorsL with
        | .error e => ok := false; errmsg := e
        | .ok anc' => newhyps := newhyps ++ [(h', anc')]
    if !ok then return .error errmsg
    else do
      inferences.modify (· + 1)
      return .ok (newhyps, (globin, offset + offinc, size - hyps.length))

/-- The ultimate answer type of the search continuations. -/
abbrev searchResult := fol_goal × tup

/- ---------------------------------------------------------------------- -/
/- Cacheing continuations. Very crude, but it works remarkably well.      -/
/- ---------------------------------------------------------------------- -/

/-- `cacheconts f`: wrap continuation `f` with subsumption caching.  Fails
    (`"cachecont"`) if the incoming `(insts, size)` is subsumed by a cached
    entry; otherwise records it and calls `f`.  `memory` is a per-call ref.
    Polymorphic in the goal payload `γ` (single goal or goal list). -/
def cacheconts {γ : Type} (cfg : MesonConfig) (memory : IO.Ref (List (γ × tup)))
    (f : (γ × tup) → IO (Except String searchResult)) :
    (γ × tup) → IO (Except String searchResult) :=
  fun input => do
    let (_gg, (insts, _offset, size)) := input
    let mem ← memory.get
    if mem.any (fun entry =>
        let (_, (insts', _, size')) := entry
        insts == insts' && (size <= size' || cfg.depth)) then
      return .error "cachecont"
    else do
      memory.set (input :: mem)
      f input

/- ---------------------------------------------------------------------- -/
/- Perform first basic expansion which allows continuation call.          -/
/- ---------------------------------------------------------------------- -/

/-- Try each rule, expanding and calling the continuation `cont`.

    NOTE (control flow): OCaml uses `tryfind`, which catches ONLY `Failure _`;
    a `Cut` exception raised inside `cont` escapes `tryfind` immediately and is
    caught by `meson_expand`'s `with Cut -> ...`.  The generic `tryfindM` catches
    EVERY error, which would swallow a `"Cut"` and wrongly try the next rule,
    defeating the cut.  So we recurse by hand and propagate `.error "Cut"`
    (Prolog's cut) at once, only advancing to the next rule on an ordinary
    failure. -/
partial def meson_expand_cont (inferences : IO.Ref Int) (loffset : Int) (rules : List folRule)
    (state : folState × tup)
    (cont : (Int × thm) → (List (fol_atom × ancestors) × tup) → IO (Except String searchResult)) :
    IO (Except String searchResult) := do
  match rules with
  | [] => return .error "tryfind"
  | r :: rest =>
      match ← (do
        match ← meson_single_expand inferences loffset r state with
        | .error e => return .error e
        | .ok res => cont r.2 res) with
      | .ok y => return .ok y
      | .error "Cut" => return .error "Cut"    -- Cut escapes, like OCaml
      | .error _ => meson_expand_cont inferences loffset rest state cont

/- ---------------------------------------------------------------------- -/
/- Try expansion and continuation call with ancestor or initial rule.     -/
/- ---------------------------------------------------------------------- -/

/-- Try expansion + continuation with either an ancestor rule or an initial
    rule.  Mirrors the OCaml `Cut`/`Failure` control flow: a `Cut` from the
    ancestor path aborts; a plain failure falls through to the clause rules. -/
def meson_expand (B : BoolThms) (cfg : MesonConfig) (inferences : IO.Ref Int)
    (rules : ancestors) (state : folState × tup)
    (cont : (Int × thm) → (List (fol_atom × ancestors) × tup) → IO (Except String searchResult)) :
    IO (Except String searchResult) := do
  let ((g, anc), tupv) := state
  let (insts, offset, size) := tupv
  let pr := g.1
  match insertan B insts g anc with
  | .error e => return .error e
  | .ok newancestors =>
    let newstate : folState × tup := ((g, newancestors), tupv)
    -- ancestor path
    let ancestorPath : IO (Except String searchResult) := do
      if cfg.prefine && pr > 0 then return .error "meson_expand"
      else
        match assoc pr anc with
        | .error _ => return .error "meson_expand"    -- Failure "find"
        | .ok arules => meson_expand_cont inferences 0 arules newstate cont
    match ← ancestorPath with
    | .ok res => return .ok res
    | .error "Cut" => return .error "meson_expand"
    | .error _ =>
      -- clause-rules path
      match assoc pr rules with
      | .error _ => return .error "meson_expand"
      | .ok prules =>
        let crules := prules.filter (fun r => r.1.1.length <= size)
        match ← meson_expand_cont inferences offset crules newstate cont with
        | .ok res => return .ok res
        | .error _ => return .error "meson_expand"   -- Cut or Failure both → fail

/- ---------------------------------------------------------------------- -/
/- Simple Prolog engine organizing search and backtracking.               -/
/- ---------------------------------------------------------------------- -/

/-- Allocate a fresh subsumption cache and wrap a continuation. -/
private def withCache {γ : Type} (cfg : MesonConfig)
    (f : (γ × tup) → IO (Except String searchResult)) :
    IO ((γ × tup) → IO (Except String searchResult)) := do
  let memory ← IO.mkRef ([] : List (γ × tup))
  return cacheconts cfg memory f

mutual
/-- Expand a single goal, threading a continuation (CPS Prolog search). -/
partial def expand_goal (B : BoolThms) (cfg : MesonConfig) (inferences : IO.Ref Int)
    (rules : ancestors) (depth : Int) (state : folState × tup)
    (cont : searchResult → IO (Except String searchResult)) :
    IO (Except String searchResult) := do
  if depth < 0 then return .error "expand_goal: too deep"
  else
    let ((g, _anc), (insts, offset, size)) := state
    meson_expand B cfg inferences rules state
      (fun apprule newstate => do
        let (_newhyps, (pinsts, _, _)) := newstate
        let k ← withCache cfg (fun (gs, (newinsts, newoffset, newsize)) => do
          let (locin, globin) := separate_insts offset pinsts newinsts
          let g' := fol_goal.Subgoal g gs apprule offset locin
          if globin == insts && gs.isEmpty then
            match ← cont (g', (globin, newoffset, size)) with
            | .ok r => return .ok r
            | .error _ => return .error "Cut"        -- try ... with Failure _ -> raise Cut
          else
            match ← cont (g', (globin, newoffset, newsize)) with
            | .ok r => return .ok r
            | .error _ => return .error "expand_goal")  -- Cut | Failure → fail
        expand_goals B cfg inferences rules (depth - 1) newstate k)

/-- Expand a list of goals, with divide-and-conquer for larger goal lists. -/
partial def expand_goals (B : BoolThms) (cfg : MesonConfig) (inferences : IO.Ref Int)
    (rules : ancestors) (depth : Int)
    (input : List (fol_atom × ancestors) × tup)
    (cont : (List fol_goal × tup) → IO (Except String searchResult)) :
    IO (Except String searchResult) := do
  let (gl, (insts, offset, size)) := input
  match gl with
  | [] => cont ([], (insts, offset, size))
  | [g] =>
      expand_goal B cfg inferences rules depth (g, (insts, offset, size))
        (fun (g', stup) => cont ([g'], stup))
  | _ =>
      if size >= cfg.dcutin then
        let lsize := size / cfg.skew
        let rsize := size - lsize
        match chop_list (gl.length / 2) gl with
        | .error e => return .error e
        | .ok (lgoals, rgoals) =>
          -- left-first attempt
          let leftFirst : IO (Except String searchResult) := do
            let k ← withCache cfg (fun (lg', (i, off, n)) => do
              let k2 ← withCache cfg (fun (rg', ztup) => cont (lg' ++ rg', ztup))
              expand_goals B cfg inferences rules depth (rgoals, (i, off, n + rsize)) k2)
            expand_goals B cfg inferences rules depth (lgoals, (insts, offset, lsize)) k
          match ← leftFirst with
          | .ok r => return .ok r
          -- DEFENSIVE, AND PROVABLY UNREACHABLE.  OCaml's handler here is
          -- `with Failure _` (meson.ml 415), so a raw `Cut` would indeed need to
          -- escape it - but no raw `Cut` can ever arrive.  `Cut` is raised only
          -- in `expand_goal`'s inner continuation (meson.ml 402) and is
          -- CONVERTED to a plain failure by the first enclosing handler: either
          -- `meson_expand` (380/384, `with Cut -> failwith "meson_expand"`) or
          -- `expand_goal`'s else-branch (405, `with Cut -> failwith
          -- "expand_goal"`).  Both conversions are mirrored above.  Verified by
          -- mutation: deleting this line leaves all 1303 assertions passing,
          -- because the branch never fires.  Kept for faithfulness to the
          -- OCaml's `Failure`-only handler, NOT because it is load-bearing.
          | .error "Cut" => return .error "Cut"
          | .error _ =>
            -- right-first attempt (with repetition check)
            let k ← withCache cfg (fun (rg', (i, off, n)) => do
              let k2 ← withCache cfg (fun (lg', (i2, off2, fsize)) =>
                if n + rsize <= lsize + fsize then pure (.error "repetition of demigoal pair")
                else cont (lg' ++ rg', (i2, off2, fsize)))
              expand_goals B cfg inferences rules depth (lgoals, (i, off, n + rsize)) k2)
            expand_goals B cfg inferences rules depth (rgoals, (insts, offset, lsize)) k
      else
        match gl with
        | [] => cont ([], (insts, offset, size))   -- unreachable (≥2 handled)
        | g :: gs =>
          let k ← withCache (γ := fol_goal) cfg (fun (gstup) => do
            let (g', stup) := gstup
            let k2 ← withCache (γ := List fol_goal) cfg (fun (gs'ftup) => do
              let (gs', ftup) := gs'ftup
              cont (g' :: gs', ftup))
            expand_goals B cfg inferences rules depth (gs, stup) k2)
          expand_goal B cfg inferences rules depth (g, (insts, offset, size)) k
end

/-- Entry point: expand a top-level goal with a fresh initial tuple.
    `maxdep` bounds recursion depth, `maxinf` the inference count. -/
def expandGoalTop (B : BoolThms) (cfg : MesonConfig) (inferences : IO.Ref Int)
    (rules : ancestors) (g : folState) (maxdep maxinf : Int)
    (cont : searchResult → IO (Except String searchResult)) :
    IO (Except String searchResult) :=
  expand_goal B cfg inferences rules maxdep (g, ([], 2 * offinc, maxinf)) cont

/- ---------------------------------------------------------------------- -/
/- With iterative deepening of inferences or depth.                       -/
/- ---------------------------------------------------------------------- -/

/-- Iterative deepening over inferences or depth (meson.ml 447-467).

    Reproduces HOL Light's three-way progress printing: with `chatty && verbose`
    a full line per iteration; with `verbose` alone the running "N.." counters on
    one line (no newline, explicit flush) ending in "solved at N"; otherwise
    silent. The non-chatty branch avoids `remark`/`report` since those add a
    newline and the counters must share a line. -/
partial def solveGoalAux (B : BoolThms) (cfg : MesonConfig) (inferences : IO.Ref Int)
    (rules : ancestors) (incdepth : Bool) (max incsize : Int) (g : folState) (n : Int) :
    IO (Except String searchResult) := do
  let idFn : searchResult → IO (Except String searchResult) := fun x => pure (.ok x)
  if n > max then return .error "solve_goal: Too deep"
  else
    -- if !meson_chatty && !verbose then ... else if !verbose then ... else ()
    let verb ← HolCore.Lib.verbose.get
    if cfg.chatty && verb then
      HolCore.Lib.report
        s!"{← inferences.get} inferences so far. Searching with maximum size {n}."
    else if verb then
      IO.print s!"{← inferences.get}.."
      (← IO.getStdout).flush
    let attempt ←
      if incdepth then expandGoalTop B cfg inferences rules g n 100000 idFn
      else expandGoalTop B cfg inferences rules g 100000 n idFn
    match attempt with
    | .ok gi =>
        if cfg.chatty && verb then
          HolCore.Lib.report s!"Goal solved with {← inferences.get} inferences."
        else if verb then
          HolCore.Lib.report s!"solved at {← inferences.get}"
        return .ok gi
    | .error _ => solveGoalAux B cfg inferences rules incdepth max incsize g (n + incsize)

/-- `solve_goal rules incdepth min max incsize g`. -/
def solve_goal (B : BoolThms) (cfg : MesonConfig) (inferences : IO.Ref Int)
    (rules : ancestors) (incdepth : Bool) (min max incsize : Int) (g : fol_atom) :
    IO (Except String searchResult) :=
  solveGoalAux B cfg inferences rules incdepth max incsize (g, []) min

/- ---------------------------------------------------------------------- -/
/- Creation of tagged contrapositives from a HOL clause.                  -/
/- This includes any possible support clauses (1 = falsity).              -/
/- The rules are partitioned into association lists.                      -/
/- ---------------------------------------------------------------------- -/

/-- Equality on raw rules for `union'` (compares codes + underlying thm). -/
private def eqtRule (r1 r2 : folRule) : Bool :=
  let ((a1, _), (b1, c1)) := r1
  let ((a2, _), (b2, c2)) := r2
  a1 == a2 && b1 == b2 && equals_thm c1 c2

/-- Build all rotations of a clause into tagged contrapositives. -/
private partial def mk_contraposes (n : Int) (th : thm)
    (used unused : List fol_atom) (sofar : List folRule) : List folRule :=
  match unused with
  | [] => sofar
  | h :: t =>
      let nw : folRule := ((List.map mk_negated (used ++ t), h), (n, th))
      mk_contraposes (n + 1) th (used ++ [h]) t (nw :: sofar)

/-- Translate one HOL clause into its tagged contrapositives (+ support). -/
def fol_of_hol_clause (S : FolStores) (th : thm) : IO (Except String (List folRule)) := do
  let lconsts := freesl (hyp th)
  let tm := concl th
  let hlits := disjuncts tm
  -- flits = map (fol_of_literal [] lconsts) hlits
  let mut flits : List fol_atom := []
  let mut ok := true
  let mut errmsg := ""
  for hl in hlits do
    if ok then
      match ← fol_of_literal S [] lconsts hl with
      | .error e => ok := false; errmsg := e
      | .ok fa => flits := flits ++ [fa]
  if !ok then return .error errmsg
  else
    let basics := mk_contraposes 0 th [] flits []
    if flits.all (fun p => p.1 < 0) then
      return .ok ((((List.map mk_negated flits, (1, [])), (-1, th)) : folRule) :: basics)
    else return .ok basics

/-- Translate a list of HOL clauses into partitioned, sorted rule lists. -/
def fol_of_hol_clauses (S : FolStores) (thms : List thm) :
    IO (Except String ancestors) := do
  -- rawrules = itlist (union' eqt o fol_of_hol_clause) thms []   (meson.ml 496).
  -- Rendered as a STRUCTURAL mirror of `itlist f l b = f h (itlist f t b)`: the
  -- recursive call on the TAIL is evaluated first, then `f` is applied to the
  -- head.  An imperative left-to-right loop would reverse the fold.
  --
  -- WHY THE DIRECTION IS OBSERVABLE, twice over:
  --   * `union'` PREPENDS elements not already present, so the accumulation order
  --     fixes the order of rules within each predicate bucket below, and on
  --     `eqt`-duplicates it fixes WHICH theorem's representative survives.  That
  --     changes the order in which MESON tries rules, hence which proof it finds
  --     within the inference bound.  (Soundness is not at stake either way: every
  --     proof is kernel-checked.)
  --   * `fol_of_hol_clause` MUTATES the shared stores (variable and constant
  --     numbering), so the order in which clauses are translated fixes the codes
  --     they receive.  Folding tail-first reproduces OCaml's assignment.
  let rec rawFold : List thm → IO (Except String (List folRule))
    | [] => return .ok []
    | th :: t => do
        match ← rawFold t with
        | .error e => return .error e
        | .ok acc =>
          match ← fol_of_hol_clause S th with
          | .error e => return .error e
          | .ok rs => return .ok (union' eqtRule rs acc)
  match ← rawFold thms with
  | .error e => return .error e
  | .ok rawrules => do
    -- prs = setify (map (fst o snd o fst) rawrules)   [conc's predicate code]
    -- (meson.ml 497).  All three projections are total, so plain `o`; rightmost
    -- (`fst`) runs FIRST.
    let prs := setify (rawrules.map (Prod.fst o Prod.snd o Prod.fst))
    -- prules = map (fun t -> t, filter ((=) t o fst o snd o fst) rawrules) prs
    -- (meson.ml 499).  The predicate is the same projection chain followed by
    -- the equality test against `t`.
    let prules : ancestors := prs.map (fun t =>
      (t, rawrules.filter ((t == ·) o Prod.fst o Prod.snd o Prod.fst)))
    -- srules = sort (fun (p,_) (q,_) -> abs p <= abs q) prules
    let srules := sort (fun (p : Int × List folRule) (q : Int × List folRule) =>
      p.1.natAbs <= q.1.natAbs) prules
    return .ok srules

/- ---------------------------------------------------------------------- -/
/- Optimize set of clauses; changing literal order complicates HOL stuff. -/
/- ---------------------------------------------------------------------- -/

/-- Optimize clause order (shorter clauses first). -/
def optimize_rules (rules : ancestors) : ancestors :=
  rules.map (fun (a, cls) =>
    (a, sort (fun (r1 r2 : folRule) => r1.1.1.length <= r2.1.1.length) cls))

/- ---------------------------------------------------------------------- -/
/- HOL contrapositive construction (with cache)                           -/
/- ---------------------------------------------------------------------- -/

/-- Auxiliary theorems for `make_hol_contrapos` / `finish_RULE`, proved once. -/
structure MesonPths where
  reflClause : thm       -- REFL_CLAUSE (for AC)
  disjAci    : thm       -- DISJ_ACI (for AC)
  impTaut    : thm       -- a \/ b <=> ~b ==> a
  pushTaut1  : thm       -- ~(a \/ b) <=> ~a /\ ~b
  pushTaut2  : thm       -- ~ ~a <=> a
  pullTaut   : thm       -- ~a \/ ~b <=> ~(a /\ b)
  imfTaut    : thm       -- ~p <=> p ==> F
  finishTaut1 : thm      -- (~p ==> p) <=> p
  finishTaut2 : thm      -- (p ==> ~p) <=> ~p
  deriving Inhabited

/-- Prove the `make_hol_contrapos`/`finish_RULE` auxiliary theorems. -/
def setupMesonPths (B : BoolThms) (T : TheoremThms) (C : ClassThms) :
    ExceptT String IO MesonPths := do
  let TAUT (s : String) : ExceptT String IO thm := do
    (Classic.TAUT B C.BOOL_CASES_AX (← parse_term s) : IO (Except String thm))
  let impTaut ← TAUT "a \\/ b <=> ~b ==> a"
  let pushTaut1 ← TAUT "~(a \\/ b) <=> ~a /\\ ~b"
  let pushTaut2 ← TAUT "~ ~a <=> a"
  let pullTaut ← TAUT "~a \\/ ~b <=> ~(a /\\ b)"
  let imfTaut ← TAUT "~p <=> p ==> F"
  let finishTaut1 ← TAUT "(~p ==> p) <=> p"
  let finishTaut2 ← TAUT "(p ==> ~p) <=> ~p"
  return { reflClause := T.REFL_CLAUSE, disjAci := T.DISJ_ACI,
           impTaut, pushTaut1, pushTaut2, pullTaut, imfTaut, finishTaut1, finishTaut2 }

/-- The contrapositive cache: `(rulenum, concl) → thm`. -/
abbrev ContraposCache := IO.Ref (List ((Int × term) × thm))

def clear_contrapos_cache (mem : ContraposCache) : IO Unit := mem.set []

/- ---------------------------------------------------------------------- -/
/- Create a HOL contrapositive on demand, with a cache.                   -/
/- ---------------------------------------------------------------------- -/

/-- Create (or fetch from cache) the HOL contrapositive for `(n, th)`. -/
def make_hol_contrapos (B : BoolThms) (P : MesonPths) (mem : ContraposCache)
    (n : Int) (th : thm) : IO (Except String thm) := do
  let tm := concl th
  let key := (n, tm)
  let cache ← mem.get
  match assoc key cache with
  | .ok cached => return .ok cached
  | .error _ =>
    let imp_CONV : ioconv := fun t => Simp.REWR_CONV B P.impTaut t
    let imf_CONV : ioconv := fun t => Simp.REWR_CONV B P.imfTaut t
    let result ← (do
      if n < 0 then
        let pullThenImf : ioconv := Simp.thencIO
          (Canon.genRewrite B Simp.depthConvIO [P.pullTaut]) imf_CONV
        (Simp.convRuleIO pullThenImf th : IO (Except String thm))
      else
        let djs := disjuncts tm
        let acthE ← (do
          if n == 0 then return (.ok th : Except String thm)
          else
            match chop_list n.toNat djs with
            | .error e => return (.error e)
            | .ok (ldjs, rdjs) =>
              match rdjs with
              | [] => return (.error "make_hol_contrapos: chop")
              | hd :: tl =>
                let ndjs := hd :: (ldjs ++ tl)
                match list_mk_disj ndjs with
                | .error e => return (.error e)
                | .ok ndisj =>
                  match ← (Canon.mkEq2 tm ndisj : IO (Except String term)) with
                  | .error e => return (.error e)
                  | .ok eqtm =>
                    match ← (Theorems.AC B P.reflClause P.disjAci eqtm : IO (Except String thm)) with
                    | .error e => return (.error e)
                    | .ok acEq => return (EQ_MP acEq th)
          : IO (Except String thm))
        match acthE with
        | .error e => return (.error e)
        | .ok acth =>
          if djs.length == 1 then return (.ok acth)
          else
            let push_CONV : ioconv := Canon.genRewrite B Simp.topSweepConvIO [P.pushTaut1, P.pushTaut2]
            let impThenPush : ioconv := Simp.thencIO imp_CONV push_CONV
            (Simp.convRuleIO impThenPush acth : IO (Except String thm))
      : IO (Except String thm))
    match result with
    | .error e => return .error e
    | .ok fth => do mem.set ((key, fth) :: cache); return .ok fth

/- ---------------------------------------------------------------------- -/
/- Handle trivial start/finish stuff.                                     -/
/- ---------------------------------------------------------------------- -/

/-- `finish_RULE`: tidy up `(~p ==> p) <=> p` / `(p ==> ~p) <=> ~p`. -/
def finish_RULE (B : BoolThms) (P : MesonPths) (th : thm) : IO (Except String thm) :=
  Simp.GEN_REWRITE_RULE B (fun c => c) [P.finishTaut1, P.finishTaut2] th

/- ---------------------------------------------------------------------- -/
/- Translate back the saved proof into HOL.                               -/
/- ---------------------------------------------------------------------- -/

/-- Negate `tm`, stripping an existing negation if present. -/
private def hol_negate (tm : term) : Except String term :=
  match Basics.dest_neg tm with
  | .ok t => .ok t
  | .error _ => mk_neg tm

/-- Merge a local instantiation entry into the running substitution. -/
private def merge_inst (tx : fol_term × Int) (current : List (fol_term × Int)) :
    List (fol_term × Int) :=
  (fol_subst current tx.1, tx.2) :: current

/-- Reconstruct the HOL theorem from a MESON proof tree. -/
partial def meson_to_hol (S : FolStores) (B : BoolThms) (P : MesonPths) (mem : ContraposCache)
    (insts : List (fol_term × Int)) (goal : fol_goal) : IO (Except String thm) := do
  match goal with
  | .Subgoal g gs (n, th) _offset locin =>
    let newins := itlist merge_inst locin insts
    let g' := fol_inst newins g
    match ← (hol_of_literal S g' : IO (Except String term)) with
    | .error e => return .error e
    | .ok hol_g =>
      -- ths = map (meson_to_hol newins) gs
      let mut ths : List thm := []
      let mut ok := true
      let mut errmsg := ""
      for sub in gs do
        if ok then
          match ← meson_to_hol S B P mem newins sub with
          | .error e => ok := false; errmsg := e
          | .ok t => ths := ths ++ [t]
      if !ok then return .error errmsg
      else
        -- hth
        let hthE ← (do
          if equals_thm th B.TRUTH then return (ASSUME hol_g)
          else
            match ← make_hol_contrapos B P mem n th with
            | .error e => return (.error e)
            | .ok cth =>
              if ths.isEmpty then return (.ok cth)
              else
                match end_itlistM (fun a b => B.CONJ a b) ths with
                | .error e => return (.error e)
                | .ok conjs => (Drule.MATCH_MP B cth conjs : IO (Except String thm))
          : IO (Except String thm))
        match hthE with
        | .error e => return .error e
        | .ok hth =>
          match ← (Drule.PART_MATCH B (fun t => .ok t) hth hol_g : IO (Except String thm)) with
          | .error e => return .error e
          | .ok ith =>
            match (do hol_negate (concl ith)) with
            | .error e => return .error e
            | .ok neg =>
              match B.DISCH neg ith with
              | .error e => return .error e
              | .ok dth => finish_RULE B P dth

/- ---------------------------------------------------------------------- -/
/- Create equality axioms for all the function and predicate symbols in   -/
/- a HOL term. Not very efficient (but then neither is throwing them into  -/
/- automated proof search!)                                               -/
/- ---------------------------------------------------------------------- -/

/-- Auxiliary theorems for `create_equality_axioms`, proved once. -/
structure EqAxPths where
  eqThms     : List thm   -- [x=x ; ~(x=y)\/~(x=z)\/(y=z)]
  impElim    : thm        -- (a ==> b) <=> ~a \/ b
  eqElim     : thm        -- (a <=> b) ==> b \/ ~a
  veqTm      : term       -- the `=` head of the first eq_thm
  deriving Inhabited

/-- Prove the equality-axiom auxiliary theorems. -/
def setupEqAx (B : BoolThms) (C : ClassThms) : ExceptT String IO EqAxPths := do
  let prove := Tactics.prove B
  let TAUT (s : String) : ExceptT String IO thm := do
    (Classic.TAUT B C.BOOL_CASES_AX (← parse_term s) : IO (Except String thm))
  let REWRITE_TAC := Simp.REWRITE_TAC B
  let ASM_REWRITE_TAC := Simp.ASM_REWRITE_TAC B
  let ASM_CASES_TAC := Classic.ASM_CASES_TAC B C.EXCLUDED_MIDDLE
  let tautConv : ioconv := fun w => (Classic.TAUT B C.BOOL_CASES_AX w : IO (Except String thm))
  let xeqy ← parse_term "x:A = y"
  let eqConj ← (prove (← parse_term "(x:A = x) /\\ (~(x:A = y) \\/ ~(x = z) \\/ (y = z))")
      (THEN B (REWRITE_TAC [])
        (THEN B (ASM_CASES_TAC xeqy)
          (THEN B (ASM_REWRITE_TAC []) (Tactics.CONV_TAC B tautConv)))) : IO (Except String thm))
  let eqThms := B.CONJUNCTS eqConj
  let impElim ← TAUT "(a ==> b) <=> ~a \\/ b"
  let eqElimTaut ← TAUT "(a <=> b) ==> b \\/ ~a"
  -- veq_tm = rator(rator(concl(hd eq_thms)))
  let veqTm ← liftExcept (do
    match eqThms with
    | e0 :: _ => rator (← rator (concl e0))
    | [] => .error "setupEqAx: no eq_thms")
  return { eqThms, impElim, eqElim := eqElimTaut, veqTm }

/-- `tm_consts tm acc`: collect `(head, arity)` of function applications. -/
private partial def tm_consts (tm : term) (acc : List (term × Nat)) : List (term × Nat) :=
  let (fn, args) := strip_comb tm
  if args.isEmpty then acc
  else itlist tm_consts args (insert (fn, args.length) acc)

/-- `fm_consts tm (preds, funs)`: collect predicate + function `(head, arity)`. -/
private partial def fm_consts (tm : term) (acc : List (term × Nat) × List (term × Nat)) :
    List (term × Nat) × List (term × Nat) :=
  match Basics.dest_forall tm with
  | .ok (_, b) => fm_consts b acc
  | .error _ =>
    match Basics.dest_exists tm with
    | .ok (_, b) => fm_consts b acc
    | .error _ =>
      match Basics.dest_conj tm with
      | .ok (l, r) => fm_consts l (fm_consts r acc)
      | .error _ =>
        match Basics.dest_disj tm with
        | .ok (l, r) => fm_consts l (fm_consts r acc)
        | .error _ =>
          match Basics.dest_imp tm with
          | .ok (l, r) => fm_consts l (fm_consts r acc)
          | .error _ =>
            match Basics.dest_neg tm with
            | .ok t => fm_consts t acc
            | .error _ =>
              -- iff (bool equality) recurses into both sides; otherwise the
              -- term is an atom (atomic equality or predicate application).
              match dest_eq tm with
              | .ok (l, r) =>
                  if type_of l == bool_ty then fm_consts r (fm_consts l acc)
                  else
                    let (pred, args) := strip_comb tm
                    let (preds, funs) := acc
                    if args.isEmpty then acc
                    else (insert (pred, args.length) preds, itlist tm_consts args funs)
              | .error _ =>
                  let (pred, args) := strip_comb tm
                  let (preds, funs) := acc
                  if args.isEmpty then acc
                  else (insert (pred, args.length) preds, itlist tm_consts args funs)

/-- `create_equivalence_axioms (eq, _)`: instantiate the eq_thms for `eq`. -/
def create_equivalence_axioms (E : EqAxPths) (eqp : term × Nat) :
    Except String (List thm) := do
  let tyins ← type_match (type_of E.veqTm) (type_of eqp.1) []
  E.eqThms.mapM (fun th => INST_TYPE tyins th)

/-- Peel function-argument types: `dest_fun_ty ty = (domain, range)`. -/
private def dest_fun_ty (ty : hol_type) : Except String (hol_type × hol_type) := do
  match dest_type ty with
  | .ok ("fun", [a, b]) => .ok (a, b)
  | _ => .error "dest_fun_ty"

/-- `create_congruence_axiom pflag (tm, len)`. -/
def create_congruence_axiom (B : BoolThms) (E : EqAxPths) (pflag : Bool) (tmlen : term × Nat) :
    IO (Except String thm) := do
  let (tm, len) := tmlen
  let (atys, _rty) := splitlist dest_fun_ty (type_of tm)
  match chop_list len atys with
  | .error e => return .error e
  | .ok (ctys, _) => do
    let largs ← ctys.mapM (fun ty => genvar ty)
    let rargs ← ctys.mapM (fun ty => genvar ty)
    return (← (do
      -- th1 = rev_itlist2 (C (curry MK_COMB)) (map (ASSUME o mk_eq)(zip largs rargs)) (REFL tm)
      --     = fold MK_COMB over the assumed equalities, starting from REFL tm.
      let pairs ← liftExcept (zip largs rargs)
      let mut assumps : List thm := []
      for (l, r) in pairs do
        let eqt ← (Canon.mkEq2 l r : IO (Except String term))
        let ath ← liftExcept (ASSUME eqt)
        assumps := assumps ++ [ath]
      let th1 ← liftExcept (assumps.foldlM (fun acc e => MK_COMB acc e) (REFL tm))
      let th2 ← if pflag then (Drule.MATCH_MP B E.eqElim th1 : IO (Except String thm))
                else pure th1
      -- itlist (fun e th => CONV_RULE imp_elim_CONV (DISCH e th)) (hyp th2) th2
      let imp_elim_CONV : ioconv := fun t => Simp.REWR_CONV B E.impElim t
      -- `itlist` is a right fold: the LAST hypothesis is discharged first.
      let mut result := th2
      for e in (hyp th2).reverse do
        let disched ← liftExcept (B.DISCH e result)
        result ← (Simp.convRuleIO imp_elim_CONV disched : IO (Except String thm))
      pure result : ExceptT String IO thm).run)

/-- Create all equality/congruence axioms for the constants in `tms`. -/
def create_equality_axioms (B : BoolThms) (E : EqAxPths) (tms : List term) :
    IO (Except String (List thm)) := do
  let isEqConst (t : term) : Bool :=
    is_const t && (match dest_const t with | .ok (nm, _) => nm == "=" | _ => false)
  let (preds, funs) := itlist fm_consts tms ([], [])
  let (eqs0, noneqs) := preds.partition (fun p => isEqConst p.1)
  if eqs0.isEmpty then return .ok []
  else do
    -- pcongs / fcongs
    let mut pcongs : List thm := []
    let mut ok := true; let mut errmsg := ""
    for tl in noneqs do
      if ok then
        match ← create_congruence_axiom B E true tl with
        | .error e => ok := false; errmsg := e
        | .ok th => pcongs := pcongs ++ [th]
    let mut fcongs : List thm := []
    for tl in funs do
      if ok then
        match ← create_congruence_axiom B E false tl with
        | .error e => ok := false; errmsg := e
        | .ok th => fcongs := fcongs ++ [th]
    if !ok then return .error errmsg
    else do
      let (preds1, _) := itlist fm_consts ((pcongs ++ fcongs).map concl) ([], [])
      let eqs1 := preds1.filter (fun p => isEqConst p.1)
      let eqs := union eqs0 eqs1
      -- equivs = itlist (union' equals_thm o create_equivalence_axioms) eqs []
      -- `itlist` is a RIGHT fold: the LAST `eqs` entry is processed first,
      -- against `[]`, and `union'` PREPENDS, so iterate `eqs.reverse`.  (Same
      -- class as the fol_of_hol_clauses fix.)  Reachable: `eqs` holds one
      -- entry per HOL TYPE at which `=` occurs.
      let mut equivs : List thm := []
      for eqp in eqs.reverse do
        if ok then
          match create_equivalence_axioms E eqp with
          | .error e => ok := false; errmsg := e
          | .ok axs => equivs := union' equals_thm axs equivs
      if !ok then return .error errmsg
      else return .ok (equivs ++ pcongs ++ fcongs)

/- ---------------------------------------------------------------------- -/
/- Push duplicated copies of poly theorems to match existing assumptions. -/
/- ---------------------------------------------------------------------- -/

/-- Deduplicate adjacent elements equal under `eq`. -/
private def uniqBy {α : Type} (eq : α → α → Bool) : List α → List α
  | [] => []
  | [x] => [x]
  | x :: y :: t =>
      let rest := uniqBy eq (y :: t)
      if eq x y then rest else x :: rest

/-- `grab_constants tm acc`: collect the constants of a formula. -/
private partial def grab_constants (tm : term) (acc : List term) : List term :=
  if is_forall tm || is_exists tm then
    (match rand tm with
     | .ok r => match Basics.body r with
                | .ok b => grab_constants b acc
                | .error _ => acc
     | .error _ => acc)
  else if is_iff tm || Basics.is_imp tm || Basics.is_conj tm || Basics.is_disj tm then
    (match rand tm, lhand tm with
     | .ok r, .ok l => grab_constants r (grab_constants l acc)
     | _, _ => acc)
  else if Basics.is_neg tm then
    (match rand tm with
     | .ok r => grab_constants r acc
     | .error _ => acc)
  else union (find_terms is_const tm) acc

/-- Match two constants by name, producing the type instantiation. -/
private def match_consts (tm1 tm2 : term) : Except String (List (hol_type × hol_type)) := do
  let (s1, ty1) ← dest_const tm1
  let (s2, ty2) ← dest_const tm2
  if s1 == s2 then type_match ty1 ty2 [] else .error "match_consts"

/-- `fun th th' -> dest_thm th <= dest_thm th'` (meson.ml 753): OCaml's
    polymorphic compare on the pair `(hyps, concl)` - HYPOTHESES FIRST,
    lexicographically, then the conclusion.  The derived `Ord thm` compares the
    fields in declaration order `hyps` then `concl`, and `term`/`hol_type` list
    their constructors in the same order as fusion.ml, so it agrees with OCaml's
    `compare`. -/
private def thmLe (th th' : thm) : Bool := compare th th' != .gt

/-- Polymorphically instantiate `th` to match constants `mconsts`. -/
def polymorph (mconsts : List term) (th : thm) : IO (List thm) := do
  let tvs := subtract (type_vars_in_term (concl th))
                      (unions ((hyp th).map type_vars_in_term))
  if tvs.isEmpty then return [th]
  else
    let pconsts := grab_constants (concl th) []
    let pairs := allpairs (fun x y => (x, y)) pconsts mconsts
    let tyins := mapfilter (fun (p : term × term) => match_consts p.1 p.2) pairs
    let insted := mapfilter (fun tyin => INST_TYPE tyin th) tyins
    let ths' := uniqBy equals_thm (sort thmLe insted)
    if ths'.isEmpty then do
      warn true "No useful-looking instantiations of lemma"
      return [th]
    else return ths'

/-- Push polymorphic copies of all `ths` to match `mconsts`. -/
partial def polymorph_all (mconsts : List term) (ths : List thm) (acc : List thm) :
    IO (List thm) := do
  match ths with
  | [] => return acc
  | th :: rest =>
      let ths' ← polymorph mconsts th
      let mconsts' := itlist grab_constants (ths'.map concl) mconsts
      polymorph_all mconsts' rest (union' equals_thm ths' acc)

/-- `POLY_ASSUME_TAC ths`: add polymorphic instantiations of `ths` as assumptions. -/
def POLY_ASSUME_TAC (B : BoolThms) (ths : List thm) : tactic := fun (asl, w) => do
  let mconsts := itlist (fun (p : String × thm) acc => grab_constants (concl p.2) acc) asl []
  let ths' ← polymorph_all mconsts ths []
  (Tactics.MAP_EVERY B (fun th => Tactics.ASSUME_TAC B th) ths' (asl, w)
   : IO (Except String goalstate))

/- ---------------------------------------------------------------------- -/
/- Brand's transformation                                                 -/
/- ---------------------------------------------------------------------- -/

/-- Auxiliary theorems for `perform_brand_modification`. -/
structure BrandPths where
  clausifyTaut : thm    -- a ==> b <=> ~a \/ b
  gsymDisjAssoc : thm   -- GSYM DISJ_ASSOC
  deriving Inhabited

def setupBrand (B : BoolThms) (T : TheoremThms) (C : ClassThms) : ExceptT String IO BrandPths := do
  let clausifyTaut ← (Classic.TAUT B C.BOOL_CASES_AX (← parse_term "a ==> b <=> ~a \\/ b")
    : IO (Except String thm))
  let gsymDisjAssoc ← liftExcept (GSYM T.DISJ_ASSOC)
  return { clausifyTaut, gsymDisjAssoc }

mutual
private partial def subterms_irrefl (lconsts : List term) (tm : term) (acc : List term) :
    List term :=
  if is_var tm || is_const tm then acc
  else let (_fn, args) := strip_comb tm
       itlist (subterms_refl lconsts) args acc
private partial def subterms_refl (lconsts : List term) (tm : term) (acc : List term) :
    List term :=
  if is_var tm then (if mem tm lconsts then insert tm acc else acc)
  else if is_const tm then insert tm acc
  else let (_fn, args) := strip_comb tm
       itlist (subterms_refl lconsts) args (insert tm acc)
end

/-- `CLAUSIFY th = CONV_RULE (REWR_CONV (a ==> b <=> ~a \/ b)) th`. -/
private def clausify (B : BoolThms) (P : BrandPths) (th : thm) : IO (Except String thm) :=
  Simp.convRuleIO (fun t => Simp.REWR_CONV B P.clausifyTaut t) th

/-- `BRAND tms th`: introduce fresh names for the terms `tms`. -/
private partial def brand (B : BoolThms) (P : BrandPths) (tms : List term) (th : thm) :
    IO (Except String thm) := do
  match tms with
  | [] => return .ok th
  | tm :: rest =>
    let gv ← genvar (type_of tm)
    return (← (do
      let eq ← (Canon.mkEq2 gv tm : IO (Except String term))
      let symEq ← liftExcept (SYM (← ASSUME eq))
      let subbed ← (Equal.SUBS [symEq] th : IO (Except String thm))
      let disched ← liftExcept (B.DISCH eq subbed)
      let th' ← (clausify B P disched : IO (Except String thm))
      -- tms' = map (subst [gv,tm]) rest  (subst is a two-stage IO builder)
      let substFn ← (Basics.subst [(gv, tm)] : IO (Except String (term → IO (Except String term))))
      let mut tms' : List term := []
      for t in rest do
        let t' ← (substFn t : IO (Except String term))
        tms' := tms' ++ [t']
      (brand B P tms' th' : IO (Except String thm))
      : ExceptT String IO thm).run)

/-- `BRANDE th`: Brand's equality-symmetry step. -/
private def brande (B : BoolThms) (P : BrandPths) (th : thm) : IO (Except String thm) := do
  let tm := concl th
  match dest_eq tm with
  | .error e => return .error e
  | .ok (l, _r) => do
    let gv ← genvar (type_of l)
    return (← (do
      let eq ← (Canon.mkEq2 (← liftExcept (rand tm)) gv : IO (Except String term))
      let rtor ← liftExcept (rator tm)
      let apEq ← liftExcept (AP_TERM rtor (← ASSUME eq))
      let em ← liftExcept (EQ_MP apEq th)
      let disched ← liftExcept (B.DISCH eq em)
      (clausify B P disched : IO (Except String thm))
      : ExceptT String IO thm).run)

/-- `LDISJ_CASES th lth rth`. -/
private def ldisj_cases (B : BoolThms) (th lth rth : thm) : Except String thm := do
  B.DISJ_CASES th (← B.DISJ1 lth (concl rth)) (← B.DISJ2 (concl lth) rth)

/-- `ASSOCIATE = CONV_RULE (REWR_CONV (GSYM DISJ_ASSOC))`. -/
private def associate (B : BoolThms) (P : BrandPths) (th : thm) : IO (Except String thm) :=
  Simp.convRuleIO (fun t => Simp.REWR_CONV B P.gsymDisjAssoc t) th

/-- `BRAND_CONGS th`: brand the congruence subterms of a clause. -/
private def brand_congs (B : BoolThms) (P : BrandPths) (th : thm) : IO (Except String thm) := do
  let lconsts := freesl (hyp th)
  let lits := disjuncts (concl th)
  let atoms := lits.map (fun t => (Basics.dest_neg t).toOption.getD t)
  let isEqAtom (t : term) : Bool :=
    (match dest_const (strip_comb t).1 with | .ok (nm, _) => nm == "=" | _ => false)
  let (eqs, noneqs) := atoms.partition isEqAtom
  let acc := itlist (subterms_irrefl lconsts) noneqs []
  let uts := itlist (fun t a => itlist (subterms_irrefl lconsts) (strip_comb t).2 a) eqs acc
  let sts := sort (fun s t => !(free_in s t)) uts
  brand B P sts th

/-- `BRAND_TRANS th`: expand transitivity/symmetry of equalities in a clause. -/
private partial def brand_trans (B : BoolThms) (P : BrandPths) (th : thm) :
    IO (Except String (List thm)) := do
  let tm := concl th
  match Basics.dest_disj tm with
  | .ok (l, r) =>
    if is_eq l then do
      match ← (do
        let lth ← liftExcept (ASSUME l)
        let lth1 ← (brande B P lth : IO (Except String thm))
        let lth2 ← (brande B P (← liftExcept (SYM lth)) : IO (Except String thm))
        let rth ← (brand_trans B P (← liftExcept (ASSUME r)) : IO (Except String (List thm)))
        -- map (ASSOCIATE o LDISJ_CASES th lth1) rth @ map (... lth2) rth
        let mut out : List thm := []
        for rt in rth do
          let lc ← liftExcept (ldisj_cases B th lth1 rt)
          let a ← (associate B P lc : IO (Except String thm))
          out := out ++ [a]
        for rt in rth do
          let lc ← liftExcept (ldisj_cases B th lth2 rt)
          let a ← (associate B P lc : IO (Except String thm))
          out := out ++ [a]
        pure out : ExceptT String IO (List thm)).run with
      | .error _ => return .ok [th]   -- OCaml: Failure in disj body → [th] (is_eq tm false)
      | .ok res => return .ok res
    else do
      match ← (do
        let rth ← (brand_trans B P (← liftExcept (ASSUME r)) : IO (Except String (List thm)))
        let mut out : List thm := []
        for rt in rth do
          out := out ++ [← liftExcept (ldisj_cases B th (← liftExcept (ASSUME l)) rt)]
        pure out : ExceptT String IO (List thm)).run with
      | .error _ => return .ok [th]   -- OCaml: Failure in disj body → [th]
      | .ok res => return .ok res
  | .error _ =>
    if is_eq tm then do
      match ← brande B P th with
      | .error e => return .error e
      | .ok b1 =>
        match SYM th with
        | .error e => return .error e
        | .ok symth =>
          match ← brande B P symth with
          | .error e => return .error e
          | .ok b2 => return .ok [b1, b2]
    else return .ok [th]

/-- Find `=` constants in a term. -/
private def find_eqs (tm : term) : List term :=
  find_terms (fun t => match dest_const t with | .ok (nm, _) => nm == "=" | _ => false) tm

/-- Add reflexivity facts for the element types of all equalities. -/
private def reflexate (ths : List thm) : IO (Except String (List thm)) := do
  let eqs := itlist (fun th acc => union (find_eqs (concl th)) acc) ths []
  -- tys = map (hd o snd o dest_type o snd o dest_const) eqs  (meson.ml 711).
  -- Read RIGHT-TO-LEFT: dest_const runs FIRST, then snd, dest_type, snd, hd.
  -- The operators are LEFT-associative, so the chain needs NO parentheses and
  -- lines up stage-for-stage with the OCaml; each operator is fixed by the local
  -- effect shape (`o` when the next stage in is total, `oM` when it is also
  -- `Except`-valued).
  let tyOf : term → Except String hol_type :=
    Lib.hd o Prod.snd oM dest_type o Prod.snd oM dest_const
  let mut tys : List hol_type := []
  for eq in eqs do
    match tyOf eq with
    -- Propagate the ACTUAL failure, as the OCaml does: a break anywhere in the
    -- chain raises that function's own `Failure` (`dest_const`, `dest_type` or
    -- `hd`), so the message must not be flattened to a single invented one.
    | .error e => return .error e
    | .ok a => tys := tys ++ [a]
  -- gvs = map genvar tys: lib.ml's `map` is LEFT-TO-RIGHT (`let y = f x in`),
  -- so genvars are drawn in `tys` order.  Then
  -- itlist (fun v acc -> REFL v :: acc) gvs ths = [REFL gv1; ...; REFL gvn] @ ths,
  -- i.e. the REFLs keep `gvs` order in front of `ths`.  Prepending inside the
  -- genvar loop reversed them.
  let gvs ← tys.mapM genvar
  return .ok (gvs.map REFL ++ ths)

/-- Brand's transformation over a clause set (used when `meson_brand`). -/
def perform_brand_modification (B : BoolThms) (P : BrandPths) (ths : List thm) :
    IO (Except String (List thm)) := do
  let hasEq := ths.any (fun th => can (fun t => find_term is_eq t) (concl th))
  if hasEq then do
    -- ths' = map BRAND_CONGS ths
    let mut ths' : List thm := []
    let mut ok := true; let mut errmsg := ""
    for th in ths do
      if ok then
        match ← brand_congs B P th with
        | .error e => ok := false; errmsg := e
        | .ok t => ths' := ths' ++ [t]
    if !ok then return .error errmsg
    else do
      -- ths'' = itlist (union' equals_thm o BRAND_TRANS) ths' []
      -- `itlist` RIGHT fold: last element first (see `equivs` above).
      let mut ths'' : List thm := []
      for th in ths'.reverse do
        if ok then
          match ← brand_trans B P th with
          | .error e => ok := false; errmsg := e
          | .ok ts => ths'' := union' equals_thm ts ths''
      if !ok then return .error errmsg
      else reflexate ths''
  else return .ok ths

/- ---------------------------------------------------------------------- -/
/- Basic HOL MESON procedure.                                             -/
/- ---------------------------------------------------------------------- -/

/-- Full MESON refutation: equality axioms (or Brand) + search + reconstruct. -/
def SIMPLE_MESON_REFUTE (B : BoolThms) (cfg : MesonConfig) (S : FolStores)
    (inferences : IO.Ref Int) (P : MesonPths) (E : EqAxPths) (Br : BrandPths)
    (mem : ContraposCache) (min max inc : Int) (ths : List thm) : IO (Except String thm) := do
  clear_contrapos_cache mem
  inferences.set 0
  let cfg' := if cfg.depth then { cfg with dcutin := 100001 } else cfg
  -- ths' = if brand then perform_brand_modification ths
  --        else ths @ create_equality_axioms (map concl ths)
  match ← (do
      if cfg.brand then perform_brand_modification B Br ths
      else
        match ← create_equality_axioms B E (ths.map concl) with
        | .error e => return (.error e)
        | .ok eqax => return (.ok (ths ++ eqax))
      : IO (Except String (List thm))) with
  | .error e => return .error e
  | .ok ths' =>
    match ← fol_of_hol_clauses S ths' with
    | .error e => return .error e
    | .ok raw =>
      let rules := optimize_rules raw
      match ← solve_goal B cfg' inferences rules cfg.depth min max inc (1, []) with
      | .error e => return .error e
      | .ok (proof, (insts, _, _)) => meson_to_hol S B P mem insts proof

/-- `CONJUNCTS_THEN' ttac cth = ttac (CONJUNCT1 cth) THEN ttac (CONJUNCT2 cth)`. -/
def CONJUNCTS_THEN' (B : BoolThms) (ttac : thm_tactic) (cth : thm) : tactic := fun g => do
  match B.CONJUNCT1 cth, B.CONJUNCT2 cth with
  | .ok c1, .ok c2 => (THEN B (ttac c1) (ttac c2) g : IO (Except String goalstate))
  | .error e, _ => return .error e
  | _, .error e => return .error e

/-- `QUANT_BOOL_CONV`: simplify boolean quantifiers/connectives. -/
def QUANT_BOOL_CONV (B : BoolThms) (T : TheoremThms) (C : ClassThms) : ioconv := fun tm => do
  match ← (Simp.PURE_REWRITE_CONV B
      [C.FORALL_BOOL_THM, C.EXISTS_BOOL_THM, C.COND_CLAUSES, C.NOT_CLAUSES,
       T.IMP_CLAUSES, T.AND_CLAUSES, T.OR_CLAUSES, T.EQ_CLAUSES,
       T.FORALL_SIMP, T.EXISTS_SIMP] : IO (Except String ioconv)) with
  | .error e => return .error e
  | .ok cnv => (cnv tm : IO (Except String thm))

/-- `SPLIT_TAC n`: split conjunctions (and up to `n` disjunctions) in assumptions. -/
partial def SPLIT_TAC (B : BoolThms) (n : Int) : tactic := fun g =>
  (ORELSE
    (THEN B (Tactics.FIRST_X_ASSUM B (fun th => CONJUNCTS_THEN' B (Tactics.ASSUME_TAC B) th))
            (SPLIT_TAC B n))
    (ORELSE
      (if n > 0 then
        THEN B (Tactics.FIRST_X_ASSUM B (fun th => Tactics.DISJ_CASES_TAC B th))
               (SPLIT_TAC B (n - 1))
       else Tactics.NO_TAC)
      Tactics.ALL_TAC)) g

/-- `PURE_MESON_TAC`: reset stores, then refute via `SIMPLE_MESON_REFUTE`. -/
def PURE_MESON_TAC (B : BoolThms) (cfg : MesonConfig) (S : FolStores)
    (inferences : IO.Ref Int) (P : MesonPths) (E : EqAxPths) (Br : BrandPths)
    (mem : ContraposCache) (min max inc : Int) : tactic := fun (asl, w) => do
  Meson.reset_vars S
  match ← Meson.reset_consts S with
  | .error e => return .error e
  | .ok _ =>
    let refuteBranch : tactic := fun (asl', w') => do
      match ← SIMPLE_MESON_REFUTE B cfg S inferences P E Br mem min max inc (asl'.map (·.2)) with
      | .error e => return .error e
      | .ok th => (Tactics.ACCEPT_TAC B th (asl', w') : IO (Except String goalstate))
    (ORELSE (Tactics.FIRST_ASSUM (fun th => Tactics.CONTR_TAC B th)) refuteBranch (asl, w)
     : IO (Except String goalstate))

/-- Pre-built conversions / tactics from Canon that `GEN_MESON_TAC` chains.
    `Session` builds these from the Canon bundle and passes them in, keeping
    `GEN_MESON_TAC` decoupled from Canon internals. -/
structure MesonTacDeps where
  presimp     : ioconv
  nnf         : ioconv
  skolem      : ioconv
  prenex      : ioconv
  condsCelim  : ioconv
  weakCnf     : ioconv
  quantBool   : ioconv
  lambdaElim  : ioconv
  assocDisj   : ioconv                       -- ASSOC_CONV DISJ_ASSOC
  selectElim  : tactic
  asmFol      : tactic
  refuteThen  : thm_tactic → tactic

/-- Repeatedly `SPEC` a genvar under leading universals (for `GEN_MESON_TAC`). -/
private partial def specGenvarLoop (B : BoolThms) (th : thm) : IO thm := do
  match Basics.dest_forall (concl th) with
  | .error _ => return th
  | .ok (v, _) =>
    let gv ← genvar (type_of v)
    match B.SPEC gv th with
    | .error _ => return th
    | .ok th' => specGenvarLoop B th'

/- ---------------------------------------------------------------------- -/
/- Basic MESON tactic with settable parameters.                           -/
/- ---------------------------------------------------------------------- -/

/-- `GEN_MESON_TAC min max step ths`: the full MESON tactic pipeline. -/
def GEN_MESON_TAC (B : BoolThms) (D : MesonTacDeps) (cfg : MesonConfig) (S : FolStores)
    (inferences : IO.Ref Int) (P : MesonPths) (E : EqAxPths) (Br : BrandPths)
    (mem : ContraposCache) (min max step : Int) (ths : List thm) : tactic := fun g => do
  let assumeTac : thm_tactic := fun th => Tactics.ASSUME_TAC B th
  -- TOP_DEPTH_CONV BETA_CONV
  let betaTopDepth : ioconv := Simp.topDepthConvIO (fun t => pure (Equal.BETA_CONV t))
  -- CONV_TAC (PRESIMP THENC BETA THENC LAMBDA_ELIM THENC CONDS_CELIM THENC QUANT_BOOL)
  let frontConv : ioconv :=
    Simp.thencIO D.presimp (Simp.thencIO betaTopDepth
      (Simp.thencIO D.lambdaElim (Simp.thencIO D.condsCelim D.quantBool)))
  -- RULE_ASSUM_TAC(CONV_RULE(NNF THENC SKOLEM))
  let nnfSkolem : thm → IO (Except String thm) :=
    fun th => Simp.convRuleIO (Simp.thencIO D.nnf D.skolem) th
  -- RULE_ASSUM_TAC(CONV_RULE(PRENEX THENC WEAK_CNF))
  let prenexCnf : thm → IO (Except String thm) :=
    fun th => Simp.convRuleIO (Simp.thencIO D.prenex D.weakCnf) th
  -- RULE_ASSUM_TAC(CONV_RULE(ASSOC_CONV DISJ_ASSOC))
  let assocRule : thm → IO (Except String thm) :=
    fun th => Simp.convRuleIO D.assocDisj th
  -- RULE_ASSUM_TAC(repeat (fun th -> SPEC(genvar(type_of(fst(dest_forall(concl th))))) th))
  let specGenvarRule : thm → IO (Except String thm) := fun th0 => do
    let r ← specGenvarLoop B th0
    return .ok r
  -- ths' for POLY_ASSUME_TAC = map GEN_ALL ths
  let genAllThs ← (do
    let mut acc : List thm := []
    for th in ths do
      match B.GEN_ALL th with
      | .error e => return (.error e)
      | .ok g' => acc := acc ++ [g']
    return (.ok acc) : IO (Except String (List thm)))
  match genAllThs with
  | .error e => return .error e
  | .ok gaThs =>
    -- W(MAP_EVERY(UNDISCH_TAC o concl o snd) o fst)   (meson.ml 813).
    -- `snd`, `concl` and `UNDISCH_TAC` are all total, so plain `o`; `snd` runs
    -- FIRST.  The outer `o fst` is the `W`-supplied assumption list, i.e. `asl`.
    let undischAll : tactic := fun (asl, w) =>
      (Tactics.MAP_EVERY B (Tactics.UNDISCH_TAC B o concl o Prod.snd) asl (asl, w)
       : IO (Except String goalstate))
    -- W(fun (asl,w) -> MAP_EVERY (fun v -> SPEC_TAC(v,v)) (frees w))
    let specFrees : tactic := fun (asl, w) =>
      (Tactics.MAP_EVERY B (fun v => Tactics.SPEC_TAC B (v, v)) (frees w) (asl, w)
       : IO (Except String goalstate))
    -- the big tactic pipeline (flattened via EVERY = sequential THEN)
    let tac : tactic := Tactics.EVERY B [
      D.refuteThen assumeTac,
      POLY_ASSUME_TAC B gaThs,
      undischAll,
      D.selectElim,
      specFrees,
      Tactics.CONV_TAC B frontConv,
      Tactics.REPEAT B (ORELSE (Tactics.GEN_TAC B) (Tactics.DISCH_TAC B)),
      D.refuteThen assumeTac,
      Tactics.RULE_ASSUM_TAC B nnfSkolem,
      Tactics.REPEAT B (Tactics.FIRST_X_ASSUM B (fun th => Tactics.CHOOSE_TAC B th)),
      D.asmFol,
      SPLIT_TAC B cfg.splitLimit,
      Tactics.RULE_ASSUM_TAC B prenexCnf,
      Tactics.RULE_ASSUM_TAC B specGenvarRule,
      Tactics.REPEAT B (Tactics.FIRST_X_ASSUM B (fun th => CONJUNCTS_THEN' B assumeTac th)),
      Tactics.RULE_ASSUM_TAC B assocRule,
      Tactics.REPEAT B (Tactics.FIRST_X_ASSUM B (fun th => Tactics.SUBST_VAR_TAC B th)),
      PURE_MESON_TAC B cfg S inferences P E Br mem min max step ]
    (tac g : IO (Except String goalstate))

/- ---------------------------------------------------------------------- -/
/- Common cases.                                                          -/
/- ---------------------------------------------------------------------- -/

/-- `ASM_MESON_TAC = GEN_MESON_TAC 0 50 1`. -/
def ASM_MESON_TAC (B : BoolThms) (D : MesonTacDeps) (cfg : MesonConfig) (S : FolStores)
    (inferences : IO.Ref Int) (P : MesonPths) (E : EqAxPths) (Br : BrandPths)
    (mem : ContraposCache) (ths : List thm) : tactic :=
  GEN_MESON_TAC B D cfg S inferences P E Br mem 0 50 1 ths

/-- `MESON_TAC ths = POP_ASSUM_LIST (K ALL_TAC) THEN ASM_MESON_TAC ths`. -/
def MESON_TAC (B : BoolThms) (D : MesonTacDeps) (cfg : MesonConfig) (S : FolStores)
    (inferences : IO.Ref Int) (P : MesonPths) (E : EqAxPths) (Br : BrandPths)
    (mem : ContraposCache) (ths : List thm) : tactic :=
  THEN B (Tactics.POP_ASSUM_LIST (fun _ => Tactics.ALL_TAC))
         (ASM_MESON_TAC B D cfg S inferences P E Br mem ths)

/- ---------------------------------------------------------------------- -/
/- Also introduce a rule.                                                 -/
/- ---------------------------------------------------------------------- -/

/-- `MESON ths tm`: prove `tm` outright by MESON. -/
def MESON (B : BoolThms) (D : MesonTacDeps) (cfg : MesonConfig) (S : FolStores)
    (inferences : IO.Ref Int) (P : MesonPths) (E : EqAxPths) (Br : BrandPths)
    (mem : ContraposCache) (ths : List thm) (tm : term) : IO (Except String thm) := do
  match ← (Tactics.TAC_PROOF B ([], tm) (MESON_TAC B D cfg S inferences P E Br mem ths)
           : IO (Except String thm)) with
  | .error e => return .error e
  | .ok th =>
    let (asl, tm') := dest_thm th
    if !asl.isEmpty && !(subset asl (unions (ths.map hyp))) then
      return .error "MESON: too many assumptions in result"
    else if tm' == tm then return .ok th
    else
      match ALPHA tm' tm with
      | .error _ => return .error "MESON: the wrong result"
      | .ok alph => return (EQ_MP alph th)

/- ---------------------------------------------------------------------- -/
/- Consolidated setup bundle                                              -/
/- ---------------------------------------------------------------------- -/

/-- All the once-proved MESON auxiliary theorem bundles. -/
structure MesonThms where
  pths  : MesonPths
  eqAx  : EqAxPths
  brand : BrandPths
  deriving Inhabited

/-- Prove all MESON auxiliary theorems (pths + equality axioms + Brand). -/
def setupMeson (B : BoolThms) (T : TheoremThms) (C : ClassThms) :
    ExceptT String IO MesonThms := do
  let pths ← setupMesonPths B T C
  let eqAx ← setupEqAx B C
  let brand ← setupBrand B T C
  return { pths, eqAx, brand }

end HolCore.Meson
