/- File: Equal.lean
Basic equality reasoning including conversionals.
John Harrison, University of Cambridge Computer Laboratory
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Lean4 translation by Chris Walton 2026 -/

import HolCore.Lib
import HolCore.Basics
import HolCore.Fusion
import HolCore.Nets
import HolCore.Printer
import HolCore.Preterm

open HolCore.Kernel HolCore.Basics HolCore.Lib HolCore.Nets
open HolCore.Printer HolCore.System HolCore.Preterm

namespace HolCore.Equal

/- Constant hiding (`hide_constant`/`unhide_constant`/`is_hidden`) is defined
   once in `Preterm` (as in HOL Light's `preterm.ml`, which loads before
   `equal.ml`) and shared here via `open HolCore.Preterm`. -/

/- ---------------------------------------------------------------------- -/
/- Type abbreviation for conversions.                                     -/
/- ---------------------------------------------------------------------- -/

/-- A conversion maps a term `t` to a theorem `|- t = t'`. -/
abbrev conv := term → Except String thm

/-- IO-valued conversions (those needing `genvar`, `subst`, or a mutable net —
    e.g. `SUBS_CONV`, `CACHE_CONV`).  A pure `conv` lifts to an `ioconv` via
    `fun t => return (c t)`. -/
abbrev ioconv := term → IO (Except String thm)

/- ---------------------------------------------------------------------- -/
/- A bit more syntax.                                                     -/
/- ---------------------------------------------------------------------- -/

/-- The left-hand argument of a binary application: `lhand = rand o rator`
    (equal.ml 22).  Both stages are `Except`-valued, so `oM`; `rator` runs FIRST. -/
def lhand : term → Except String term := rand oM rator
/-- The left-hand side of an equation: `lhs = fst o dest_eq` (equal.ml 24).
    `fst` is total over an `Except`-valued `dest_eq`, hence `oEm`. -/
def lhs : term → Except String term := Prod.fst oEm dest_eq
/-- The right-hand side of an equation: `rhs = snd o dest_eq` (equal.ml 26). -/
def rhs : term → Except String term := Prod.snd oEm dest_eq

/- ---------------------------------------------------------------------- -/
/- Similar to variant, but even avoids constants, and ignores types.      -/
/- ---------------------------------------------------------------------- -/

/-- Rename a variable to avoid a list, dodging constants and ignoring types. -/
partial def mk_primed_var (avoid : List term) (v : term) : IO (Except String term) := do
  let rec svariant (avoid : List String) (s : String) : IO String := do
    if mem s avoid || ((← get_const_type s).toOption.isSome && !(← is_hidden s)) then
      svariant avoid (s ++ "'")
    else pure s
  match dest_var v with
  | .error e => return .error e
  | .ok (s, ty) =>
      let s' ← svariant (mapfilter (fun a => (dest_var a).map (·.1)) avoid) s
      return .ok (mk_var s' ty)

/- ---------------------------------------------------------------------- -/
/- General case of beta-conversion.                                       -/
/- ---------------------------------------------------------------------- -/

/-- General case of beta-conversion; fails with "BETA_CONV: Not a beta-redex". -/
def BETA_CONV (tm : term) : Except String thm :=
  match BETA tm with
  | .ok th => .ok th
  | .error _ =>
    match do
      let (f, arg) ← dest_comb tm
      let v ← bndvar f
      let th ← BETA (← mk_comb f v)
      INST [(arg, v)] th
    with
    | .ok th => .ok th
    | .error _ => failwith "BETA_CONV: Not a beta-redex"

/- ---------------------------------------------------------------------- -/
/- A few very basic derived equality rules.                               -/
/- ---------------------------------------------------------------------- -/

/-- Apply a term to both sides of an equation; fails with "AP_TERM". -/
def AP_TERM (tm : term) : thm → Except String thm :=
  let rth := REFL tm
  fun th =>
    match MK_COMB rth th with
    | .ok res  => .ok res
    | .error _ => failwith "AP_TERM"

/-- Apply both sides of an equation to a term; fails with "AP_THM". -/
def AP_THM (th : thm) (tm : term) : Except String thm :=
  match MK_COMB th (REFL tm) with
  | .ok res  => .ok res
  | .error _ => failwith "AP_THM"

/-- Symmetry of equality: from `|- l = r` derive `|- r = l`. -/
def SYM (th : thm) : Except String thm := do
  let tm := concl th
  let (l, _) ← dest_eq tm
  let lth := REFL l
  let apth ← AP_TERM (← rator (← rator tm)) th
  EQ_MP (← MK_COMB apth lth) lth

/-- Prove two alpha-equivalent terms equal; fails with "ALPHA". -/
def ALPHA (tm1 tm2 : term) : Except String thm :=
  match TRANS (REFL tm1) (REFL tm2) with
  | .ok th   => .ok th
  | .error _ => failwith "ALPHA"

/-- Rename the bound variable of an abstraction to `v`. -/
def ALPHA_CONV (v : term) (tm : term) : Except String thm := do
  let res ← alpha v tm
  ALPHA tm res

/-- Rename the bound variable, also under a leading operator. -/
def GEN_ALPHA_CONV (v : term) (tm : term) : Except String thm := do
  if is_abs tm then ALPHA_CONV v tm
  else
    let (b, abs) ← dest_comb tm
    AP_TERM b (← ALPHA_CONV v abs)

/-- Congruence for a binary operator: combine two argument equations. -/
def MK_BINOP (op : term) : thm → thm → Except String thm :=
  let afn := AP_TERM op
  fun lth rth => do
    MK_COMB (← afn lth) rth

/- ---------------------------------------------------------------------- -/
/- Terminal conversion combinators.                                       -/
/- ---------------------------------------------------------------------- -/
/-- The conversion that always fails, with "NO_CONV". -/
def NO_CONV : conv := fun _ => failwith "NO_CONV"
/-- The identity conversion, returning `|- t = t`. -/
def ALL_CONV : conv := fun tm => .ok (REFL tm)

/- ---------------------------------------------------------------------- -/
/- Combinators for sequencing, trying, repeating etc. conversions.        -/
/- ---------------------------------------------------------------------- -/
/-- Sequence two conversions, composing their equations transitively. -/
def THENC (conv1 conv2 : conv) : conv :=
  fun t => do
    let th1 ← conv1 t
    let th2 ← conv2 (← rand (concl th1))
    TRANS th1 th2

/-- Try the first conversion, falling back to the second on failure. -/
def ORELSEC (conv1 conv2 : conv) : conv :=
  fun t =>
    match conv1 t with
    | .ok th   => .ok th
    | .error _ => conv2 t

/-- Apply the first conversion in the list that succeeds; fails with
    "FIRST_CONV" on an empty list. -/
def FIRST_CONV (cs : List conv) : conv :=
  fun tm =>
    match end_itlist (fun c1 c2 => ORELSEC c1 c2) cs with
    | .ok c    => c tm
    | .error e => .error e

/-- Apply every conversion in the list in sequence. -/
def EVERY_CONV (l : List conv) : conv :=
  itlist (fun c1 c2 => THENC c1 c2) l ALL_CONV

/-- Repeatedly apply a conversion until it fails. -/
partial def REPEATC (conv : conv) (t : term) : Except String thm :=
  ORELSEC (THENC conv (REPEATC conv)) ALL_CONV t

/-- Apply a conversion but fail with "CHANGED_CONV" if it changes nothing. -/
def CHANGED_CONV (conv : conv) (tm : term) : Except String thm := do
  let th ← conv tm
  let (l, r) ← dest_eq (concl th)
  if aconv l r then failwith "CHANGED_CONV" else .ok th

/-- Apply a conversion, defaulting to the identity conversion on failure. -/
def TRY_CONV (c : conv) : conv := ORELSEC c ALL_CONV

/- ---------------------------------------------------------------------- -/
/- Subterm conversions.                                                   -/
/- ---------------------------------------------------------------------- -/
/-- Apply a conversion to the operator of an application; fails with
    "RATOR_CONV: Not a combination". -/
def RATOR_CONV (c : conv) (tm : term) : Except String thm :=
  match tm with
  | .Comb l r => do AP_THM (← c l) r
  | _ => failwith "RATOR_CONV: Not a combination"

/-- Apply a conversion to the operand (argument) of an application; fails
    with "RAND_CONV: Not a combination". -/
def RAND_CONV (c : conv) (tm : term) : Except String thm :=
  match tm with
  | .Comb l r => do MK_COMB (REFL l) (← c r)
  | _ => failwith "RAND_CONV: Not a combination"

/-- Apply a conversion to the left argument of a binary application. -/
def LAND_CONV : conv → conv := RATOR_CONV o RAND_CONV

/-- Apply separate conversions to operator and operand of an application;
    fails with "COMB2_CONV: Not a combination". -/
def COMB2_CONV (lconv rconv : conv) (tm : term) : Except String thm :=
  match tm with
  | .Comb l r => do
    -- OCaml evaluates the arguments of `MK_COMB(..., ...)` right to left, so the
    -- right-hand conversion runs (and can fail) first.
    let rth ← rconv r
    let lth ← lconv l
    MK_COMB lth rth
  | _ => failwith "COMB2_CONV: Not a combination"

/-- Apply one conversion to both operator and operand of an application. -/
def COMB_CONV : conv → conv := W COMB2_CONV

/-- Apply a conversion to the body of an abstraction.
    The fallback branch uses a pure `variant (frees bod) (mk_var "_" …)` in
    place of OCaml's `IO` `genvar`, to keep `conv` pure. -/
def ABS_CONV (c : conv) (tm : term) : Except String thm := do
  let (v, bod) ← dest_abs tm
  let th ← c bod
  match ABS v th with
  | .ok res => .ok res
  | .error _ =>
      let gv ← variant (frees bod) (mk_var "_" (type_of v))
      let gbod := (← vsubst [(gv, v)]) bod
      let gth ← ABS gv (← c gbod)
      let gtm := concl gth
      let (l, r) ← dest_eq gtm
      let v' ← variant (frees gtm) v
      let eqth ← ALPHA gtm (safe_mk_eq (← alpha v' l) (← alpha v' r))
      EQ_MP eqth gth

/-- Apply a conversion beneath a binder (or the abstraction directly). -/
def BINDER_CONV (c : conv) (tm : term) : Except String thm :=
  if is_abs tm then ABS_CONV c tm
  else RAND_CONV (ABS_CONV c) tm

/-- Apply a conversion to the immediate subterms of a term. -/
def SUB_CONV (c : conv) (tm : term) : Except String thm :=
  match tm with
  | .Comb _ _ => COMB_CONV c tm
  | .Abs _ _  => ABS_CONV c tm
  | _ => .ok (REFL tm)

/-- Apply a conversion to both arguments of a binary application. -/
def BINOP_CONV (c : conv) (tm : term) : Except String thm := do
  let (lop, r) ← dest_comb tm
  let (op, l) ← dest_comb lop
  -- OCaml evaluates the arguments of `MK_COMB(..., ...)` right to left, so the
  -- right-hand conversion runs (and can fail) first.
  let rth ← c r
  MK_COMB (← AP_TERM op (← c l)) rth

/-- Apply separate conversions to the two arguments of a binary application. -/
def BINOP2_CONV (conv1 conv2 : conv) (tm : term) : Except String thm := do
  let (lop, r) ← dest_comb tm
  let (op, l) ← dest_comb lop
  -- OCaml evaluates the arguments of `MK_COMB(..., ...)` right to left, so the
  -- right-hand conversion runs (and can fail) first.
  let rth ← conv2 r
  MK_COMB (← AP_TERM op (← conv1 l)) rth

/- ---------------------------------------------------------------------- -/
/- Depth conversions; internal use of a failure-propagating `Boultonized' -/
/- version to avoid a great deal of reuilding of terms.                  -/
/- ---------------------------------------------------------------------- -/

private def THENQC (conv1 conv2 : conv) (tm : term) : Except String thm :=
  match conv1 tm with
  | .error _ => conv2 tm
  | .ok th1  =>
      match (do conv2 (← rand (concl th1))) with
      | .ok th2  => TRANS th1 th2
      | .error _ => .ok th1
private def THENCQC (conv1 conv2 : conv) (tm : term) : Except String thm := do
  let th1 ← conv1 tm
  match (do conv2 (← rand (concl th1))) with
  | .ok th2  => TRANS th1 th2
  | .error _ => .ok th1
private def COMB_QCONV (c : conv) (tm : term) : Except String thm :=
  match tm with
  | .Comb l r =>
      match c l with
      | .ok th1  =>
          match c r with
          | .ok th2  => MK_COMB th1 th2
          | .error _ => AP_THM th1 r
      | .error _ => do AP_TERM l (← c r)
  | _ => failwith "COMB_QCONV: Not a combination"
private partial def REPEATQC (c : conv) (tm : term) : Except String thm :=
  THENCQC c (REPEATQC c) tm
private def SUB_QCONV (c : conv) (tm : term) : Except String thm :=
  match tm with
  | .Abs _ _ => ABS_CONV c tm
  | _ => COMB_QCONV c tm
private partial def ONCE_DEPTH_QCONV (c : conv) (tm : term) : Except String thm :=
    ORELSEC c (SUB_QCONV (ONCE_DEPTH_QCONV c)) tm
private partial def DEPTH_QCONV (c : conv) (tm : term) : Except String thm :=
  THENQC (SUB_QCONV (DEPTH_QCONV c)) (REPEATQC c) tm
private partial def REDEPTH_QCONV (c : conv) (tm : term) : Except String thm :=
  THENQC (SUB_QCONV (REDEPTH_QCONV c)) (THENCQC c (REDEPTH_QCONV c)) tm
private partial def TOP_DEPTH_QCONV (c : conv) (tm : term) : Except String thm :=
  THENQC (REPEATQC c)
          (THENCQC (SUB_QCONV (TOP_DEPTH_QCONV c))
                  (THENCQC c (TOP_DEPTH_QCONV c))) tm
private partial def TOP_SWEEP_QCONV (c : conv) (tm : term) : Except String thm :=
  THENQC (REPEATQC c) (SUB_QCONV (TOP_SWEEP_QCONV c)) tm
/-- Apply a conversion to the first (outermost) applicable subterms, going
    top-down and stopping on each branch once it succeeds; results are not
    re-traversed. -/
def ONCE_DEPTH_CONV (c : conv) : conv := TRY_CONV (ONCE_DEPTH_QCONV c)
/-- Apply a conversion bottom-up, repeating it at each node after its
    subterms are done, but never re-descending into a rewritten result. -/
def DEPTH_CONV      (c : conv) : conv := TRY_CONV (DEPTH_QCONV c)
/-- Apply a conversion bottom-up, and after each successful rewrite
    re-traverse the result, so the term is driven to normal form. -/
def REDEPTH_CONV    (c : conv) : conv := TRY_CONV (REDEPTH_QCONV c)
/-- Apply a conversion top-down, repeating at each node before and after
    descending into subterms and re-traversing, reaching normal form. -/
def TOP_DEPTH_CONV  (c : conv) : conv := TRY_CONV (TOP_DEPTH_QCONV c)
/-- Apply a conversion top-down, repeating at each node then descending
    into subterms once, without re-traversing rewritten results. -/
def TOP_SWEEP_CONV  (c : conv) : conv := TRY_CONV (TOP_SWEEP_QCONV c)

/- ---------------------------------------------------------------------- -/
/- Apply at leaves of op-tree; NB any failures at leaves cause failure.   -/
/- ---------------------------------------------------------------------- -/
/-- Apply a conversion at the leaves of a tree of the given binary operator;
    any failure at a leaf causes failure. -/
partial def DEPTH_BINOP_CONV (op : term) (c : conv) (tm : term) : Except String thm :=
  match tm with
  | .Comb (.Comb op' _) _ =>
      if op' == op then do
        let (l, r) ← dest_binop op tm
        let lth ← DEPTH_BINOP_CONV op c l
        let rth ← DEPTH_BINOP_CONV op c r
        MK_COMB (← AP_TERM op' lth) rth
      else c tm
  | _ => c tm

/- ---------------------------------------------------------------------- -/
/- Follow a path.                                                         -/
/- ---------------------------------------------------------------------- -/
/-- Apply a conversion at the subterm reached by following a path string
    of `l` (operator), `r` (operand), and other (abstraction body) steps. -/
def PATH_CONV (s : String) (cnv : conv) : conv :=
  let rec path_conv (s : List String) (cnv : conv) : conv :=
    match s with
    | []        => cnv
    | "l" :: t  => RATOR_CONV (path_conv t cnv)
    | "r" :: t  => RAND_CONV (path_conv t cnv)
    | _ :: t    => ABS_CONV (path_conv t cnv)
  path_conv (explode s) cnv

/- ---------------------------------------------------------------------- -/
/- Follow a pattern.                                                      -/
/- ---------------------------------------------------------------------- -/
/-- Apply a conversion at the subterms matching the variables of a pattern. -/
partial def PAT_CONV (pat : term) : conv → conv :=
  let rec PCONV (xs : List term) (pat : term) (c : conv) : conv :=
    if mem pat xs then c
    else if !(exists' (fun x => free_in x pat) xs) then ALL_CONV
    else match pat with
      | .Comb l r => COMB2_CONV (PCONV xs l c) (PCONV xs r c)
      | .Abs _ b  => ABS_CONV (PCONV xs b c)
      | _ => ALL_CONV -- unreachable
  let (xs, pbod) := strip_abs pat
  PCONV xs pbod

/- ---------------------------------------------------------------------- -/
/- Symmetry conversion.                                                   -/
/- ---------------------------------------------------------------------- -/
/-- Prove `(l = r) <=> (r = l)`; fails with "SYM_CONV". -/
def SYM_CONV (tm : term) : Except String thm :=
  match (do
    let th1 ← SYM (← ASSUME tm)
    let tm' := concl th1
    let th2 ← SYM (← ASSUME tm')
    pure (DEDUCT_ANTISYM_RULE th2 th1)) with
  | .ok th   => .ok th
  | .error _ => failwith "SYM_CONV"

/- ---------------------------------------------------------------------- -/
/- Conversion to a rule.                                                  -/
/- ---------------------------------------------------------------------- -/
/-- Turn a conversion into a rule: rewrite the conclusion of a theorem. -/
def CONV_RULE (c : conv) (th : thm) : Except String thm := do
  EQ_MP (← c (concl th)) th

/-- Eliminate a hypothesis: `PROVE_HYP ath bth` removes `concl ath` from `bth`'s
    hypotheses (up to alpha) if present, else returns `bth` unchanged.  (In HOL
    Light this is a local `let` in `bool.ml`; shared here since it is a generic
    kernel-level derived rule used by `Tactics` and `Simp`.) -/
def PROVE_HYP (ath bth : thm) : Except String thm :=
  if (hyp bth).any (fun h => aconv (concl ath) h) then
    EQ_MP (DEDUCT_ANTISYM_RULE ath bth) ath
  else .ok bth

/- ---------------------------------------------------------------------- -/
/- Substitution conversion.                                               -/
/- ---------------------------------------------------------------------- -/

/-- `SUBS_CONV`.  Uses `genvar` and the `subst` factory, both `IO`, so this is
    an IO-valued conversion (`term → IO (Except String thm)`). -/
def SUBS_CONV (ths : List thm) (tm : term) : IO (Except String thm) := do
  if ths.isEmpty then return .ok (REFL tm)
  else
    let result ← (do
      -- lefts = map (lhand o concl) ths   (equal.ml 308).  `concl` is total and
      -- `lhand` is `Except`-valued, so plain `o`; `concl` runs FIRST.
      let lefts ← liftExcept (ths.mapM (lhand o concl))
      -- gvs = map (genvar o type_of) lefts   (equal.ml 309).  `type_of` is total
      -- and `genvar` is IO, so plain `o` still types (effect at the outer end).
      let gvs ← (lefts.mapM (genvar o type_of) : IO (List term))
      -- pat = subst (zip gvs lefts) tm   (zip is Except; subst is an IO factory)
      let pairs ← liftExcept (zip gvs lefts)
      -- `← (io : IO (Except String X))` in this ExceptT block yields `X`
      -- (the IO is lifted and the Except threaded), so no extra unwrap needed.
      let substFn ← (subst pairs : IO (Except String (term → IO (Except String term))))
      let pat ← (substFn tm : IO (Except String term))
      let abs ← liftExcept (list_mk_abs gvs pat)
      -- th = rev_itlist (fun y x -> CONV_RULE (RAND_CONV BETA_CONV THENC
      --                              LAND_CONV BETA_CONV) (MK_COMB(x,y))) ths (REFL abs)
      let step (y : thm) (x : thm) : Except String thm := do
        CONV_RULE (THENC (RAND_CONV BETA_CONV) (LAND_CONV BETA_CONV)) (← MK_COMB x y)
      let th ← liftExcept (rev_itlistM step ths (REFL abs))
      if (← liftExcept (rand (concl th))) == tm then pure (REFL tm) else pure th
      : ExceptT String IO thm).run
    return (result.mapError (fun _ => "SUBS_CONV"))

/-- Rewrite a theorem's conclusion with a list of equations (via
    `SUBS_CONV`); IO-valued for the same reason. -/
def SUBS (ths : List thm) (th : thm) : IO (Except String thm) := do
  match ← SUBS_CONV ths (concl th) with
  | .error e => return .error e
  | .ok cth  => return (EQ_MP cth th)

/- ---------------------------------------------------------------------- -/
/- Get a few rules.                                                       -/
/- ---------------------------------------------------------------------- -/

/-- Beta-reduce a theorem's conclusion everywhere, repeatedly. -/
def BETA_RULE : thm → Except String thm := CONV_RULE (REDEPTH_CONV BETA_CONV)
/-- Reverse equations in a theorem's conclusion, once at each outermost site. -/
def GSYM : thm → Except String thm := CONV_RULE (ONCE_DEPTH_CONV SYM_CONV)

/- ---------------------------------------------------------------------- -/
/- A cacher for conversions.                                              -/
/- ---------------------------------------------------------------------- -/

/-- `CACHE_CONV`.  Uses a term net (like the OCaml version): the net is keyed on
    the input term's structure and its tips hold the cached theorems.
    `ALPHA_HACK` adjusts a cached theorem to an alpha-variant query term.  The
    net is mutable, so this is IO-valued. -/
def CACHE_CONV (conv : conv) : IO ioconv := do
  -- ALPHA_HACK th tm: if lhand(concl th) = tm then th else TRANS (ALPHA tm tm') th
  let ALPHA_HACK (th : thm) (tm : term) : Except String thm := do
    let tm' ← lhand (concl th)
    if tm' == tm then .ok th
    else TRANS (← ALPHA tm tm') th
  let net ← IO.mkRef (empty_net : net thm)
  return fun tm => do
    -- tryfind (fun th => ALPHA_HACK th tm) (lookup tm !net)
    match tryfind (fun th => ALPHA_HACK th tm) (lookup tm (← net.get)) with
    | .ok th => return .ok th
    | .error _ =>
        match conv tm with
        | .error e => return .error e
        | .ok th =>
            match ← enter [] (tm, th) (← net.get) with
            | .ok net' => net.set net'; return .ok th
            | .error e => return .error e

/- ---------------------------------------------------------------------- -/
/- A printer.                                                             -/
/- ---------------------------------------------------------------------- -/

/-- `PRINT_TERM_CONV`.  Prints the (quoted) term, then acts as `ALL_CONV`.
    Printing is `IO`, so this is an IO-valued conversion. -/
def PRINT_TERM_CONV (t : term) : IO (Except String thm) := do
  let doc ← pp_print_qterm t
  IO.println (Fmt.runStd (← get_margin) doc)
  return .ok (REFL t)
