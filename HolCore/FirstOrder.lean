/- File: FirstOrder.lean
General facilities for manipulating first-order shadow terms (`firstorder.ml`).
Original (c) Copyright, Michael Faerber and Cezary Kaliszyk, 2014-2018.
Lean4 translation by Chris Walton 2026 -/

import HolCore.Bool
import HolCore.Equal
import HolCore.Basics
import HolCore.Meson

open HolCore.Kernel HolCore.Basics HolCore.Lib HolCore.Bool HolCore.Equal HolCore.Meson

namespace HolCore.FirstOrder

set_option maxRecDepth 4000

/- ---------------------------------------------------------------------- -/
/- Controls verbosity of these and the main CoP functions.                -/
/- ---------------------------------------------------------------------- -/

/-- Controls output verbosity of the CoPs (`copverb`, firstorder.ml 13).
    Off by default, as in HOL Light; when set, `fol_of_var` and the leanCoP
    and nanoCoP searches and reconstructions print their traces. -/
initialize copverb : IO.Ref Bool ← IO.mkRef false

/- OCaml's tracing prints on `Format.std_formatter`.  `Format.printf "..%!"`
   flushes it; `Thm.print_proof` and `print_thm` print WITHOUT flushing, so
   their output and its line breaking are settled by the next flush.
   `stdPending` holds that unflushed formatter content. -/
initialize stdPending : IO.Ref (List (HolCore.System.Fmt Unit)) ← IO.mkRef []

/-- Queue formatter output on the (emulated) std_formatter, unflushed. -/
def stdQueue (f : HolCore.System.Fmt Unit) : IO Unit := stdPending.modify (· ++ [f])

/-- `Format.printf "<s>%!"`: print `s` after any queued std_formatter
    content, then flush. -/
def stdPrintf (s : String) : IO Unit := do
  let pend ← stdPending.get
  stdPending.set []
  let w ← HolCore.Printer.get_margin
  let act : HolCore.System.Fmt Unit := do
    for f in pend do f
    HolCore.System.Fmt.printString s
    HolCore.System.Fmt.printFlush
  IO.print (HolCore.System.Fmt.runStd w act)
  (← IO.getStdout).flush

/-- Flush the emulated std_formatter (`Format.print_flush ()`, also done by
    OCaml's toplevel at the end of each phrase). -/
def stdFlush : IO Unit := do
  if !(← stdPending.get).isEmpty then stdPrintf ""

/- ---------------------------------------------------------------------- -/
/- Misc utility functions.                                                -/
/- ---------------------------------------------------------------------- -/

namespace Utils

/-- Forward composition `(f %> g) x = g (f x)`. -/
def composeFwd (f : α → β) (g : β → γ) : α → γ := fun x => g (f x)

/-- Backward composition `(f % g) x = f (g x)`. -/
def composeBwd (f : β → γ) (g : α → β) : α → γ := fun x => f (g x)

/-- `const x _ = x`. -/
def const (x : α) : β → α := fun _ => x

/- OCaml's `( >>= )` (Option bind) maps to Lean's built-in `Option.bind` /
   `>>=` on `Option`, so no separate definition is provided. -/

namespace Pair
/-- Map a function over both components of a pair. -/
def mapn (f : α → β) (p : α × α) : β × β := (f p.1, f p.2)
end Pair

namespace List

/-- `cons x l = x :: l`. -/
def cons (x : α) (l : List α) : List α := x :: l

/-- `list_rest l`: for each element, pair it with `(elements-before-reversed,
    elements-after)`.  OCaml `go [] l`. -/
def list_rest (l : List α) : List (α × (List α × List α)) :=
  let rec go (acc : List α) : List α → List (α × (List α × List α))
    | [] => []
    | x :: xs => (x, (acc, xs)) :: go (x :: acc) xs
  go [] l

/-- "nth_rest i l" returns the i-th element of l as well as
    the elements before and after (in order) -/
def nth_rest (n : Nat) (l : List α) : Except String (α × (List α × List α)) :=
  let rec go (acc : List α) (i : Nat) : List α → Except String (α × (List α × List α))
    | x :: xs => if i > 0 then go (x :: acc) (i - 1) xs
                 else .ok (x, (acc.reverse, xs))
    | [] => .error "nth_rest"
  go [] n l

/-- `insert_at i elem l`: insert `elem` at position `i`. -/
def insert_at (i : Nat) (elem : α) (l : List α) : Except String (List α) :=
  let rec go (acc : List α) : Nat × List α → Except String (List α)
    | (0, xs) => .ok (acc.reverse ++ (elem :: xs))
    | (_, []) => .error "insert_at"
    | (n + 1, x :: xs) => go (x :: acc) (n, xs)
  go [] (i, l)

/-- `take_drop n l = (take n l, drop n l)`, failing if `l` too short. -/
def take_drop (n : Nat) (l : List α) : Except String (List α × List α) :=
  let rec go (acc : List α) (i : Nat) : List α → Except String (List α × List α)
    | [] => if i > 0 then .error "take_drop" else .ok (acc.reverse, [])
    | x :: xs => if i > 0 then go (x :: acc) (i - 1) xs
                 else .ok (acc.reverse, x :: xs)
  go [] n l

/-- `take n l = fst (take_drop n l)`. -/
def take (n : Nat) (l : List α) : Except String (List α) :=
  (take_drop n l).map Prod.fst

/-- `findi p l`: first `(index, element)` with `p index element`. -/
def findi (p : Nat → α → Bool) (l : List α) : Except String (Nat × α) :=
  let rec loop (n : Nat) : List α → Except String (Nat × α)
    | [] => .error "findi"
    | h :: t => if p n h then .ok (n, h) else loop (n + 1) t
  loop 0 l

/-- `union1 x y`: `union` preserving order of `x` (structural membership). -/
def union1 [BEq α] (x y : List α) : List α :=
  x.foldr (fun h acc => if mem h y then acc else h :: acc) y
  -- note: OCaml union1 keeps x's elements not in y, prepended to y

/-- tail-recursive version -- reverses first argument
    OCaml: `[] -> y | h::t -> if mem h y then union1 t y else union2 t (h::y)`. -/
def union2 [BEq α] : List α → List α → List α
  | [], y => y
  | h :: t, y => if mem h y then union1 t y else union2 t (h :: y)

/-- Sum of a list of floats (OCaml `fsum = fold_left (+.) 0.`). -/
def fsum (l : List Float) : Float := l.foldl (· + ·) 0.0

/-- `fold_right1 f [x1;..;xn] = f x1 (f x2 (... xn))`. -/
def fold_right1 (f : α → α → α) : List α → Except String α
  | [] => .error "fold_right1"
  | [x] => .ok x
  | x :: xs => do return f x (← fold_right1 f xs)

/-- `fold_left_map f acc xs`: left fold producing `(acc', reversed ys)`. -/
def fold_left_map (f : σ → α → σ × β) (acc : σ) (xs : List α) : σ × List β :=
  xs.foldl (fun (a, ys) x => let (a', y) := f a x; (a', y :: ys)) (acc, [])

/-- `fold_right_map f acc xs`: right fold producing `(acc', ys)`. -/
def fold_right_map (f : σ → α → σ × β) (acc : σ) (xs : List α) : σ × List β :=
  xs.foldr (fun x (a, ys) => let (a', y) := f a x; (a', y :: ys)) (acc, [])

/-- `fold_map f sf l = let (sf, rev) = fold_left_map f sf l in (sf, rev.reverse)`. -/
def fold_map (f : σ → α → σ × β) (sf : σ) (l : List α) : σ × List β :=
  let (sf', rev) := fold_left_map f sf l
  (sf', rev.reverse)

/-- `filter_map` = `List.filterMap`. -/
def filter_map (f : α → Option β) (l : List α) : List β := l.filterMap f

/-- `exists_unique p l`: exactly one element of `l` satisfies `p`. -/
def exists_unique (p : α → Bool) (l : List α) : Bool :=
  let rec go (acc : Bool) : List α → Bool
    | [] => acc
    | x :: xs => if p x then (if acc then false else go true xs) else go acc xs
  go false l

/-- `concat_map f l = concat (map f l)`. -/
def concat_map (f : α → List β) (l : List α) : List β := (l.map f).flatten

end List

end Utils

/- ---------------------------------------------------------------------- -/
/- Adapted from meson.ml. The main change is that creating HOL versions   -/
/- of fresh variables requires HOL types.                                 -/
/- ---------------------------------------------------------------------- -/

namespace Mapping

open HolCore.Meson

/-- The variable/constant stores.  Reuses `Meson.FolStores` (same five refs);
    `fol_of_const`/`hol_of_const` are literally Meson's, while `fol_of_var`/
    `hol_of_var` use this module's variant logic (type-directed genvars). -/
abbrev Stores := Meson.FolStores

/-- Reset the variable stores (OCaml `reset_vars`). -/
def reset_vars (S : Stores) : IO Unit := do
  S.vstore.set []; S.gstore.set []; S.vcounter.set 0

private def inc_vcounter (S : Stores) : IO Int := do
  let n ← S.vcounter.get
  S.vcounter.set (n + 1)
  return n

/-- `fol_of_var v`: code for HOL variable `v` (allocating fresh; no overflow
    check, unlike Meson's). -/
def fol_of_var (S : Stores) (v : term) : IO (Except String Int) := do
  let currentvars ← S.vstore.get
  match assoc v currentvars with
  | .ok n => return .ok n
  | .error _ => do
      let n ← inc_vcounter S
      -- firstorder.ml 150-152
      if ← copverb.get then
        stdPrintf s!"fol_of_var: {← HolCore.Printer.string_of_term v} (ty = {← HolCore.Printer.string_of_type (type_of v)}) <- {n}\n"
      S.vstore.set ((v, n) :: currentvars)
      return .ok n

/-- `hol_of_var v ty`: the HOL variable for code `v` at type `ty`.  Always a
    genvar keyed in `gstore` (no `vstore` lookup — the type-aware variant). -/
def hol_of_var (S : Stores) (v : Int) (ty : hol_type) : IO term := do
  let gs ← S.gstore.get
  match rev_assoc v gs with
  | .ok t => return t
  | .error _ => do
      let gv ← genvar ty
      S.gstore.set ((gv, v) :: gs)
      return gv

/-- `reset_consts`/`fol_of_const`/`hol_of_const` — reused from `Meson`. -/
def reset_consts (S : Stores) : IO (Except String Unit) := Meson.reset_consts S
def fol_of_const (S : Stores) (c : term) : IO (Except String Int) := Meson.fol_of_const S c
def hol_of_const (S : Stores) (c : Int) : IO (Except String term) := Meson.hol_of_const S c

/-- Translate a term (in NNF) into shadow syntax. -/
partial def fol_of_term (S : Stores) (env consts : List term) (tm : term) :
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
def fol_of_atom (S : Stores) (env consts : List term) (tm : term) :
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
def fol_of_literal (S : Stores) (env consts : List term) (tm : term) :
    IO (Except String fol_atom) := do
  match Basics.dest_neg tm with
  | .ok tm' =>
      match ← fol_of_atom S env consts tm' with
      | .ok (p, a) => return .ok (-p, a)
      | .error _ => fol_of_atom S env consts tm
  | .error _ => fol_of_atom S env consts tm

/-- Translate a formula (in NNF) into shadow syntax. -/
partial def fol_of_form (S : Stores) (env consts : List term) (tm : term) :
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

mutual
/-- Translate a shadow term back to HOL at the given HOL type `ty`. -/
partial def hol_of_term (S : Stores) (ty : hol_type) (tm : fol_term) :
    IO (Except String term) := do
  match tm with
  | .Fvar v => do return .ok (← hol_of_var S v ty)
  | .Fnapp f args => hol_of_atom S f args

/-- Functions can be translated to FOF
    without the full number of its arguments (due to partial application).
    Therefore obtain only as many types of arguments
    as present in the FO term. -/
partial def hol_of_atom (S : Stores) (f : Int) (args : List fol_term) :
    IO (Except String term) := do
  match ← hol_of_const S f with
  | .error e => return .error e
  | .ok f' =>
    let (tys, _rty) := splitlist Basics.dest_fun_ty (type_of f')
    if args.length > tys.length then
      return .error "hol_of_atom: too many arguments"
    else
      match Utils.List.take args.length tys with
      | .error e => return .error e
      | .ok tys' =>
        -- list_mk_comb (f', map2 hol_of_term tys' args)
        let mut hargs : List term := []
        let mut ok := true; let mut errmsg := ""
        for (t, a) in tys'.zip args do
          if ok then
            match ← hol_of_term S t a with
            | .error e => ok := false; errmsg := e
            | .ok h => hargs := hargs ++ [h]
        if !ok then return .error errmsg
        else return (list_mk_comb f' hargs)
end

/-- Translate a shadow literal back to HOL. -/
def hol_of_literal (S : Stores) (pa : fol_atom) : IO (Except String term) := do
  let (p, args) := pa
  if p < 0 then
    match ← hol_of_atom S (-p) args with
    | .ok a => return (mk_neg a)
    | .error e => return .error e
  else hol_of_atom S p args

/- ---------------------------------------------------------------------- -/
/- Creation of tagged contrapositives from a HOL clause.                  -/
/- This includes any possible support clauses (1 = falsity).              -/
/- The rules are partitioned into association lists.                      -/
/- ---------------------------------------------------------------------- -/

private def eqtRule (r1 r2 : Meson.folRule) : Bool :=
  let ((a1, _), (b1, c1)) := r1
  let ((a2, _), (b2, c2)) := r2
  a1 == a2 && b1 == b2 && equals_thm c1 c2

private partial def mk_contraposes (n : Int) (th : thm)
    (used unused : List fol_atom) (sofar : List Meson.folRule) : List Meson.folRule :=
  match unused with
  | [] => sofar
  | h :: t =>
      let nw : Meson.folRule := ((List.map Meson.mk_negated (used ++ t), h), (n, th))
      mk_contraposes (n + 1) th (used ++ [h]) t (nw :: sofar)

/-- Translate one HOL clause into its tagged contrapositives (+ support). -/
def fol_of_hol_clause (S : Stores) (th : thm) : IO (Except String (List Meson.folRule)) := do
  let lconsts := freesl (hyp th)
  let hlits := disjuncts (concl th)
  let mut flits : List fol_atom := []
  let mut ok := true; let mut errmsg := ""
  for hl in hlits do
    if ok then
      match ← fol_of_literal S [] lconsts hl with
      | .error e => ok := false; errmsg := e
      | .ok fa => flits := flits ++ [fa]
  if !ok then return .error errmsg
  else
    let basics := mk_contraposes 0 th [] flits []
    if flits.all (fun p => p.1 < 0) then
      return .ok ((((List.map Meson.mk_negated flits, (1, [])), (-1, th)) : Meson.folRule) :: basics)
    else return .ok basics

/-- Translate a list of HOL clauses into partitioned, sorted rule lists. -/
def fol_of_hol_clauses (S : Stores) (thms : List thm) :
    IO (Except String Meson.ancestors) := do
  -- rawrules = itlist (union' eqt o fol_of_hol_clause) thms []   (meson.ml 496,
  -- which firstorder.ml mirrors).  A STRUCTURAL mirror of
  -- `itlist f l b = f h (itlist f t b)`: recurse on the TAIL first, then apply
  -- `f` to the head.  A left-to-right loop would reverse the fold, which is
  -- observable twice - `union'` PREPENDS (so accumulation order fixes both the
  -- rule order within each bucket and which `eqt`-duplicate survives), and
  -- `fol_of_hol_clause` MUTATES the shared stores, so translation order fixes the
  -- assigned variable/constant codes.
  let rec rawFold : List thm → IO (Except String (List Meson.folRule))
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
    let prs := setify (rawrules.map (fun r => r.1.2.1))
    let prules : Meson.ancestors := prs.map (fun t =>
      (t, rawrules.filter (fun r => r.1.2.1 == t)))
    let srules := sort (fun (p : Int × List Meson.folRule) (q : Int × List Meson.folRule) =>
      p.1.natAbs <= q.1.natAbs) prules
    return .ok srules

end Mapping

end HolCore.FirstOrder
