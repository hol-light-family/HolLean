/- File: Simp.lean
Simplification and rewriting.
Original       John Harrison, University of Cambridge Computer Laboratory
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Lean4 translation by Chris Walton 2026
-/

import HolCore.Bool
import HolCore.Basics
import HolCore.Fusion
import HolCore.Nets
import HolCore.Equal
import HolCore.Drule
import HolCore.Tactics
import HolCore.Itab
import HolCore.Parser

open HolCore.Kernel HolCore.Basics HolCore.Lib HolCore.Bool HolCore.Nets
     HolCore.Equal HolCore.Drule HolCore.Tactics HolCore.Itab HolCore.Parser

namespace HolCore.Simp

/- ---------------------------------------------------------------------- -/
/- Generalized conversion (conversion plus a priority).                   -/
/- ---------------------------------------------------------------------- -/

/-- A generalized conversion: a priority together with an (IO) conversion. -/
abbrev gconv := Int × ioconv

/-- nets.ml's `enter` on `(priority, conv)` pairs: OCaml's `compare` orders
    them by priority and raises on the conversions, so equal priorities keep
    insertion order and an entry is never a duplicate. -/
def enter_gconv (lconsts : List term) (tmelem : term × gconv) (nt : net gconv) :
    IO (Except String (net gconv)) :=
  enterBy (fun _ _ => false) (fun x h => x.1 < h.1) lconsts tmelem nt

/- ---------------------------------------------------------------------- -/
/- Primitive rewriting conversions: unconditional and conditional equations. -/
/- ---------------------------------------------------------------------- -/

/-- Rewrite with an equational theorem by matching its LHS. -/
def REWR_CONV (B : BoolThms) (th : thm) : ioconv :=
  fun tm => PART_MATCH B lhs th tm

/-- Rewrite with a conditional equation `|- c ==> (l = r)` by matching `l`. -/
def IMP_REWR_CONV (B : BoolThms) (th : thm) : ioconv :=
  fun tm => PART_MATCH B (fun t => do lhs (← Basics.dest_imp t).2) th tm

/- ---------------------------------------------------------------------- -/
/- Versions with ordered rewriting. We must have l' > r' for the rewrite  -/
/- |- l = r (or |- c ==> (l = r)) to apply.                               -/
/- ---------------------------------------------------------------------- -/

/-- Ordered rewrite: apply `REWR_CONV th` only if the result `l = r` has
    `ord l r`. -/
def ORDERED_REWR_CONV (B : BoolThms) (ord : term → term → Bool) (th : thm) :
    ioconv := fun tm => do
  match ← (REWR_CONV B th tm : IO (Except String thm)) with
  | .error e => return .error e
  | .ok thm =>
    match dest_eq (concl thm) with
    | .error e => return .error e
    | .ok (l, r) =>
      if ord l r then return .ok thm
      else return .error "ORDERED_REWR_CONV: wrong orientation"

/-- Ordered conditional rewrite (checks the orientation of the equation under
    the antecedent). -/
def ORDERED_IMP_REWR_CONV (B : BoolThms) (ord : term → term → Bool) (th : thm) :
    ioconv := fun tm => do
  match ← (IMP_REWR_CONV B th tm : IO (Except String thm)) with
  | .error e => return .error e
  | .ok thm =>
    match (do dest_eq (← rand (concl thm)) : Except String (term × term)) with
    | .error e => return .error e
    | .ok (l, r) =>
      if ord l r then return .ok thm
      else return .error "ORDERED_IMP_REWR_CONV: wrong orientation"

/- ---------------------------------------------------------------------- -/
/- Standard AC-compatible term ordering: a "dynamic" lexicographic ordering. -/
/-                                                                        -/
/- This is a slight hack to make AC normalization work. However I *think* -/
/- it's properly AC compatible, i.e. monotonic and total, WF on ground terms -/
/- (over necessarily finite signature) and with the properties for any    -/
/- binary operator +:                                                     -/
/-                                                                        -/
/-         (x + y) + z > x + (y + z)                                      -/
/-         x + y > y + x                   iff x > y                       -/
/-         x + (y + z) > y + (x + z)       iff x > y                       -/
/-                                                                        -/
/- The idea is that when invoking lex ordering with identical head operator -/
/- "f", one sticks "f" at the head of an otherwise arbitrary ordering on   -/
/- subterms (the built-in CAML one). This avoids the potentially inefficient -/
/- calculation of term size in the standard orderings.                    -/
/- ---------------------------------------------------------------------- -/

/-- Lexicographic extension of an ordering to argument lists. -/
private def lexify (ord : term → term → Bool) : List term → List term → Bool
  | [], _ => false
  | _, [] => true
  | h1 :: t1, h2 :: t2 => ord h1 h2 || (h1 == h2 && lexify ord t1 t2)

/-- Dynamic lexicographic term ordering with distinguished top constant. -/
private partial def dyn_order (top : term) (tm1 tm2 : term) : Bool :=
  let (f1, args1) := strip_comb tm1
  let (f2, args2) := strip_comb tm2
  if f1 == f2 then lexify (dyn_order f1) args1 args2
  else if f2 == top then false
  else if f1 == top then true
  else compare f1 f2 == Ordering.gt

/-- The AC-compatible dynamic term ordering used for ordered rewriting. -/
def term_order : term → term → Bool := dyn_order (.Const "T" bool_ty)

/- ---------------------------------------------------------------------- -/
/- Create a gconv net for a theorem as a (cond) rewrite. The "rep" flag   -/
/- will cause any trivially looping rewrites to be modified, and any that  -/
/- are permutative to be ordered w.r.t. the standard order. The idea is that -/
/- this flag will be set iff the conversion is going to get repeated.     -/
/- This includes a completely ad hoc but useful special case for ETA_AX,  -/
/- which forces a first order match (otherwise it would loop on a lambda). -/
/- ---------------------------------------------------------------------- -/

/-- Add `th` (as a rewrite, possibly conditional) to a gconv net. -/
def net_of_thm (B : BoolThms) (rep : Bool) (th : thm) (sofar : net gconv) :
    IO (Except String (net gconv)) := do
  let tm := concl th
  let lconsts := freesl (hyp th)
  let matchable (l r : term) : IO Bool := do
    match ← (term_match lconsts l r : IO (Except String instantiation)) with
    | .ok _ => return true | .error _ => return false
  -- `rep && matchable l r && matchable r l`, short-circuiting as in OCaml.
  -- (A `(← ..)` inside a condition runs before the condition is tested, and
  -- `term_match` draws genvars on higher-order patterns.)
  let bothMatch (l r : term) : IO Bool := do
    if !rep then return false
    if ← matchable l r then matchable r l else return false
  match tm with
  -- ETA_AX special case: |- (\x. v x) = v (falls through to plain eq otherwise).
  -- `v` must be a variable: simp.ml 96 patterns `Abs(x,Comb(Var(s,ty) as v,x'))`,
  -- so e.g. `|- (\x. SUC x) = SUC` takes the plain-equation arm instead.
  | .Comb (.Comb (.Const "=" _) (.Abs x (.Comb v x'))) v' =>
      if is_var v && x' == x && v' == v && !(x == v) then
        let conv : ioconv := fun t => do
          match t with
          | .Abs y (.Comb tf y') =>
              if y == y' && !(free_in y tf) then
                match ← (term_match [] v tf : IO (Except String instantiation)) with
                | .ok i => return INSTANTIATE i th
                | .error e => return .error e
              else return .error "REWR_CONV (ETA_AX special case)"
          | _ => return .error "REWR_CONV (ETA_AX special case)"
        enter_gconv lconsts (.Abs x (.Comb v x'), (1, conv)) sofar
      else
        -- LHS is an abstraction but not the eta shape: treat as a plain equation.
        let l := term.Abs x (.Comb v x')
        if rep && free_in l v' then
          match B.EQT_INTRO th with
          | .error e => return .error e
          | .ok th' => enter_gconv lconsts (l, (1, REWR_CONV B th')) sofar
        else if ← bothMatch l v' then
          enter_gconv lconsts (l, (1, ORDERED_REWR_CONV B term_order th)) sofar
        else enter_gconv lconsts (l, (1, REWR_CONV B th)) sofar
  -- plain equation |- l = r
  | .Comb (.Comb (.Const "=" _) l) r =>
      if rep && free_in l r then
        match B.EQT_INTRO th with
        | .error e => return .error e
        | .ok th' => enter_gconv lconsts (l, (1, REWR_CONV B th')) sofar
      else if ← bothMatch l r then
        enter_gconv lconsts (l, (1, ORDERED_REWR_CONV B term_order th)) sofar
      else enter_gconv lconsts (l, (1, REWR_CONV B th)) sofar
  -- conditional |- c ==> (l = r)
  | .Comb (.Comb _ _t) (.Comb (.Comb (.Const "=" _) l) r) =>
      if rep && free_in l r then
        match (do B.DISCH _t (← B.EQT_INTRO (← B.UNDISCH th)) : Except String thm) with
        | .error e => return .error e
        | .ok th' => enter_gconv lconsts (l, (3, IMP_REWR_CONV B th')) sofar
      else if ← bothMatch l r then
        enter_gconv lconsts (l, (3, ORDERED_IMP_REWR_CONV B term_order th)) sofar
      else enter_gconv lconsts (l, (3, IMP_REWR_CONV B th)) sofar
  | _ => return .error "net_of_thm"

/-- Create a gconv net for a conversion with a term index. -/
def net_of_conv (tm : term) (conv : ioconv) (sofar : net gconv) :
    IO (Except String (net gconv)) :=
  enter_gconv [] (tm, (2, conv)) sofar

/-- Create a gconv net for a congruence rule (in canonical form!) -/
def net_of_cong (B : BoolThms) (th : thm) (sofar : net gconv) :
    IO (Except String (net gconv)) := do
  -- repeat (fun (tm,m) => (snd(dest_imp tm), m+1)) (concl th, 0)
  let step (p : term × Nat) : Except String (term × Nat) := do
    return ((← Basics.dest_imp p.1).2, p.2 + 1)
  let (conc, n) := repeat' step (concl th, 0)
  if n == 0 then return .error "net_of_cong: Non-implicational congruence"
  else
    match lhs conc with
    | .error e => return .error e
    | .ok pat =>
        -- conv = GEN_PART_MATCH (lhand o funpow n rand) th   (simp.ml 134).
        -- `funpow n ...` is total here and `lhand` is `Except`-valued, so plain
        -- `o`; the funpow runs FIRST.
        -- NOTE the inner step keeps this file's existing behaviour of stopping at
        -- a failed `rand` (`.toOption.getD x`) rather than propagating, which is
        -- NOT what the OCaml's `funpow n rand` does - left unchanged here because
        -- it is a semantic question, not a composition one.
        let partfn : term → Except String term :=
          lhand o funpow n (fun x => (rand x).toOption.getD x)
        let conv : ioconv := fun t => GEN_PART_MATCH B partfn th t
        enter_gconv [] (pat, (4, conv)) sofar

/- ---------------------------------------------------------------------- -/
/- Rewriting (and application of other conversions) based on a convnet.   -/
/- ---------------------------------------------------------------------- -/

/-- Apply the first applicable conversion found in the net for `tm`. -/
def REWRITES_CONV (net : net gconv) (tm : term) : IO (Except String thm) := do
  let pconvs := lookup tm net
  match ← tryfindM (fun (p : gconv) => p.2 tm) pconvs with
  | .ok r => return .ok r
  | .error _ => return .error "REWRITES_CONV"

/- ---------------------------------------------------------------------- -/
/- IO-conversion combinators (the simp layer's convs are IO-valued).      -/
/- ---------------------------------------------------------------------- -/

/-- Sequencing of IO conversions (`THENC` for `ioconv`). -/
def thencIO (c1 c2 : ioconv) : ioconv := fun tm => do
  match ← (c1 tm : IO (Except String thm)) with
  | .error e => return .error e
  | .ok th1 =>
    match rand (concl th1) with
    | .error e => return .error e
    | .ok r =>
      match ← (c2 r : IO (Except String thm)) with
      | .error e => return .error e
      | .ok th2 => return (TRANS th1 th2)

/-- Alternation of IO conversions (`ORELSEC` for `ioconv`). -/
def orelsecIO (c1 c2 : ioconv) : ioconv := fun tm => do
  match ← (c1 tm : IO (Except String thm)) with
  | .ok r => return .ok r
  | .error _ => (c2 tm : IO (Except String thm))

/-- Identity IO conversion. -/
def allConvIO : ioconv := fun tm => return .ok (REFL tm)

/-- Repeat an IO conversion until it fails (`REPEATC` for `ioconv`). -/
partial def repeatcIO (c : ioconv) : ioconv := fun t =>
  orelsecIO (thencIO c (repeatcIO c)) allConvIO t

/-- `CONV_RULE` for an IO conversion. -/
def convRuleIO (c : ioconv) (th : thm) : IO (Except String thm) := do
  match ← (c (concl th) : IO (Except String thm)) with
  | .error e => return .error e
  | .ok eq => return (EQ_MP eq th)

/- ---------------------------------------------------------------------- -/
/- Rewrite maker for ordinary and conditional rewrites (via "cf" flag).   -/
/-                                                                        -/
/- We follow Don in going from ~(s = t) to (s = t) = F *and* (t = s) = F. -/
/- Well, why not? However, we don't abandon s = t where FV(t) is not a    -/
/- subset of FV(s) in favour of (s = t) = T, as he does.                  -/
/- Note: looping rewrites are not discarded here, only when netted.       -/
/- ---------------------------------------------------------------------- -/

/-- Cache for `mk_rewrites`' two `ITAUT` helper lemmas (computed once). -/
initialize theMkRewritesLemmas : IO.Ref (Option (thm × thm)) ← IO.mkRef none

/-- Get (computing and caching once) the two helper lemmas used by
    `mk_rewrites`: `|- (p ==> q ==> r) <=> (p /\ q ==> r)` and
    `|- (!x. P x ==> Q) <=> ((?x. P x) ==> Q)`. -/
def mkRewritesLemmas (B : BoolThms) : IO (Except String (thm × thm)) := do
  match ← theMkRewritesLemmas.get with
  | some p => return .ok p
  | none => do
    match ← (parse_term "p ==> q ==> r <=> p /\\ q ==> r" : IO (Except String term)) with
    | .error e => return .error e
    | .ok t1 =>
      match ← (parse_term "(!x. P x ==> Q) <=> (?x. P x) ==> Q" : IO (Except String term)) with
      | .error e => return .error e
      | .ok t2 =>
        match ← (ITAUT B t1 : IO (Except String thm)) with
        | .error e => return .error e
        | .ok l1 =>
          match ← (ITAUT B t2 : IO (Except String thm)) with
          | .error e => return .error e
          | .ok l2 => do theMkRewritesLemmas.set (some (l1, l2)); return .ok (l1, l2)

/-- Turn a theorem into a list of rewrite rules (splitting conjunctions,
    stripping universals/implications, handling negations and non-equations).
    `cf` enables conditional-rewrite (context) collection. IO-valued (uses
    `ITAUT` for its helper lemmas and the IO rewriting conversions). -/
partial def mk_rewrites (B : BoolThms) (cf : Bool) (th : thm) (sofar : List thm) :
    IO (Except String (List thm)) := ExceptT.run do
  -- helper lemmas via ITAUT (computed once, cached)
  let (l1, l2) ← (mkRewritesLemmas B : IO (Except String (thm × thm)))
  let IMP_CONJ_CONV : ioconv := REWR_CONV B l1
  let IMP_EXISTS_RULE (v : term) (th : thm) : IO (Except String thm) := do
    match B.GEN v th with
    | .error e => return .error e
    | .ok gth => (convRuleIO (REWR_CONV B l2) gth : IO (Except String thm))
  -- collect_condition
  let collect_condition (oldhyps : List term) (th : thm) : ExceptT String IO thm := do
    let conds := subtract (hyp th) oldhyps
    if conds == [] then return th
    else
      let jth ← liftExcept (itlistM B.DISCH conds th)
      let kth ← (convRuleIO (repeatcIO IMP_CONJ_CONV) jth : IO (Except String thm))
      let (cond, eqn) ← liftExcept (Basics.dest_imp (concl kth))
      let fvs := subtract (subtract (frees cond) (frees eqn)) (freesl oldhyps)
      -- itlist IMP_EXISTS_RULE fvs kth
      let rec go : List term → thm → ExceptT String IO thm
        | [], t => return t
        | v :: vs, t => do
            let t' ← go vs t
            (IMP_EXISTS_RULE v t' : IO (Except String thm))
      go fvs kth
  -- split_rewrites
  let rec split_rewrites (oldhyps : List term) (cf : Bool) (th : thm)
      (sofar : List thm) : ExceptT String IO (List thm) := do
    let tm := concl th
    if is_forall tm then
      split_rewrites oldhyps cf (← liftExcept (B.SPEC_ALL th)) sofar
    else if is_conj tm then do
      let c2 ← liftExcept (B.CONJUNCT2 th)
      let rest ← split_rewrites oldhyps cf c2 sofar
      let c1 ← liftExcept (B.CONJUNCT1 th)
      split_rewrites oldhyps cf c1 rest
    else if is_imp tm && cf then
      split_rewrites oldhyps cf (← liftExcept (B.UNDISCH th)) sofar
    else if is_eq tm then do
      if cf then
        let cth ← collect_condition oldhyps th
        return (cth :: sofar)
      else return (th :: sofar)
    else if is_neg tm then do
      let ths ← split_rewrites oldhyps cf (← liftExcept (B.EQF_INTRO th)) sofar
      if is_eq (← liftExcept (rand tm)) then
        split_rewrites oldhyps cf (← liftExcept (B.EQF_INTRO (← liftExcept (GSYM th)))) ths
      else return ths
    else
      split_rewrites oldhyps cf (← liftExcept (B.EQT_INTRO th)) sofar
  split_rewrites (hyp th) cf th sofar

/- ---------------------------------------------------------------------- -/
/- Decision procedures may accumulate their state in different ways (e.g. -/
/- term nets and predicate-indexed lists of Horn clauses). To allow mixing -/
/- of arbitrary types for state storage, we use a trick due to RJB via DRS. -/
/- ---------------------------------------------------------------------- -/

/-- A prover bundles an (IO) conversion with a way to augment its state with
    new theorems, yielding a new prover. -/
inductive prover where
  | NoProver : prover
  | Prover : ioconv → (List thm → prover) → prover

instance : Inhabited prover := ⟨.NoProver⟩

/-- Build a prover from an applicator and an augmentor over a state. -/
partial def mk_prover {σ : Type} (applicator : σ → ioconv)
    (augmentor : σ → List thm → σ) : σ → prover :=
  fun state =>
    .Prover (applicator state) (fun thms => mk_prover applicator augmentor (augmentor state thms))

/-- Augment a prover with additional theorems. -/
def augment : prover → List thm → prover
  | .NoProver, _ => .NoProver
  | .Prover _ aug, thms => aug thms

/-- Apply a prover's conversion to a term. -/
def apply_prover : prover → ioconv
  | .NoProver, _ => pure (.error "apply_prover")
  | .Prover conv _, tm => conv tm

/- ---------------------------------------------------------------------- -/
/- Type of simpsets. We have a convnet containing rewrites (implicational -/
/- and otherwise), other term-indexed context-free conversions like       -/
/- BETA_CONV, and congruence rules. Then there is a list of provers that   -/
/- have their own way of storing and using context, and finally a rewrite  -/
/- maker function, to allow customization.                                -/
/-                                                                        -/
/- We also have a type of (traversal) strategy, following Konrad.         -/
/- ---------------------------------------------------------------------- -/

/-- A simpset: rewrite/congruence net, subprover list, and a rewrite maker.

    HOL Light's simpset also stores a condition-prover transformer
    (`strategy → strategy`), but that makes the type non-strictly-positive,
    which Lean rejects. Since every library simpset uses the default
    `basic_prover`, we drop the field and call `basic_prover` directly from
    `IMP_REWRITES_CONV`; `ss_of_prover` is kept as a no-op. -/
inductive simpset where
  | Simpset : net gconv →                                         -- Rewrites & congruences
              List prover →                                       -- Subprovers for prover
              (thm → List thm → IO (Except String (List thm))) →  -- Rewrite maker
              simpset

/-- A traversal strategy: given a simpset, a depth level, and a term, produce a
    rewrite theorem (IO-valued). -/
abbrev strategy := simpset → Int → term → IO (Except String thm)

/- ---------------------------------------------------------------------- -/
/- Very simple prover: recursively simplify then try provers.             -/
/- ---------------------------------------------------------------------- -/

/-- The basic condition-prover: simplify with `strat`, then either read off the
    proof (`EQT_ELIM`) or discharge via a subprover. -/
def basic_prover (B : BoolThms) (strat : strategy) (ss : simpset)
    (lev : Int) (tm : term) : IO (Except String thm) := do
  let (.Simpset _ provers _) := ss
  -- sth = try strat ss lev tm with _ -> REFL tm
  let sth ← (do
    match ← (strat ss lev tm : IO (Except String thm)) with
    | .ok r => pure r
    | .error _ => pure (REFL tm))
  match B.EQT_ELIM sth with
  | .ok r => return .ok r
  | .error _ => do
    match rand (concl sth) with
    | .error e => return .error e
    | .ok rhs =>
      -- tth = tryfind (fun pr => apply_prover pr rhs) provers
      let rec tryProvers : List prover → IO (Except String thm)
        | [] => return .error "basic_prover"
        | pr :: rest => do
            match ← (apply_prover pr rhs : IO (Except String thm)) with
            | .ok tth => return (do EQ_MP (← SYM sth) tth)
            | .error _ => tryProvers rest
      tryProvers provers

/- ---------------------------------------------------------------------- -/
/- Functions for changing or augmenting components of simpsets.           -/
/- ---------------------------------------------------------------------- -/

/-- Add rewrite theorems to a simpset's net. -/
def ss_of_thms (B : BoolThms) (thms : List thm) (ss : simpset) :
    IO (Except String simpset) := do
  let (.Simpset nt provers rewmaker) := ss
  -- cthms = itlist rewmaker thms []
  let rec mkAll : List thm → List thm → IO (Except String (List thm))
    | [], acc => return .ok acc
    | t :: ts, acc => do
        match ← (mkAll ts acc : IO (Except String (List thm))) with
        | .error e => return .error e
        | .ok acc' => (rewmaker t acc' : IO (Except String (List thm)))
  match ← (mkAll thms [] : IO (Except String (List thm))) with
  | .error e => return .error e
  | .ok cthms =>
    let rec addAll : List thm → net gconv → IO (Except String (net gconv))
      | [], n => return .ok n
      | t :: ts, n => do
          match ← (net_of_thm B true t n : IO (Except String (net gconv))) with
          | .error e => return .error e
          | .ok n' => addAll ts n'
    match ← (addAll cthms nt : IO (Except String (net gconv))) with
    | .error e => return .error e
    | .ok nt' => return .ok (.Simpset nt' provers rewmaker)

/-- Add a term-indexed conversion to a simpset. -/
def ss_of_conv (keytm : term) (conv : ioconv) (ss : simpset) :
    IO (Except String simpset) := do
  let (.Simpset nt provers rewmaker) := ss
  match ← (net_of_conv keytm conv nt : IO (Except String (net gconv))) with
  | .error e => return .error e
  | .ok nt' => return .ok (.Simpset nt' provers rewmaker)

/-- Add congruence rules to a simpset. -/
def ss_of_congs (B : BoolThms) (thms : List thm) (ss : simpset) :
    IO (Except String simpset) := do
  let (.Simpset nt provers rewmaker) := ss
  let rec addAll : List thm → net gconv → IO (Except String (net gconv))
    | [], n => return .ok n
    | t :: ts, n => do
        match ← (net_of_cong B t n : IO (Except String (net gconv))) with
        | .error e => return .error e
        | .ok n' => addAll ts n'
  match ← (addAll thms nt : IO (Except String (net gconv))) with
  | .error e => return .error e
  | .ok nt' => return .ok (.Simpset nt' provers rewmaker)

/-- Replace the condition-prover of a simpset. A no-op in this port (see the
    `simpset` type comment); the default `basic_prover` is always used. -/
def ss_of_prover (_newprover : strategy → strategy) (ss : simpset) : simpset := ss

/-- Prepend subprovers to a simpset. -/
def ss_of_provers (newprovers : List prover) (ss : simpset) : simpset :=
  let (.Simpset nt provers rewmaker) := ss
  .Simpset nt (newprovers ++ provers) rewmaker

/-- Replace the rewrite maker of a simpset. -/
def ss_of_maker (newmaker : thm → List thm → IO (Except String (List thm)))
    (ss : simpset) : simpset :=
  let (.Simpset nt provers _) := ss
  .Simpset nt provers newmaker

/- ---------------------------------------------------------------------- -/
/- Perform a context-augmentation operation on a simpset.                 -/
/- ---------------------------------------------------------------------- -/

/-- Augment a simpset with a context theorem `cth` (augment subprovers, add
    `cth`'s rewrites to the net). -/
def AUGMENT_SIMPSET (B : BoolThms) (cth : thm) (ss : simpset) :
    IO (Except String simpset) := do
  let (.Simpset nt provers rewmaker) := ss
  let provers' := provers.map (fun pr => augment pr [cth])
  match ← (rewmaker cth [] : IO (Except String (List thm))) with
  | .error e => return .error e
  | .ok cthms =>
    let rec addAll : List thm → net gconv → IO (Except String (net gconv))
      | [], n => return .ok n
      | t :: ts, n => do
          match ← (net_of_thm B true t n : IO (Except String (net gconv))) with
          | .error e => return .error e
          | .ok n' => addAll ts n'
    match ← (addAll cthms nt : IO (Except String (net gconv))) with
    | .error e => return .error e
    | .ok nt' => return .ok (.Simpset nt' provers' rewmaker)

/- ---------------------------------------------------------------------- -/
/- Depth conversions (squash conversions).                                -/
/- ---------------------------------------------------------------------- -/

/-- Apply implicational rewrites from the net, discharging side-conditions via
    the simpset's condition-prover. -/
def IMP_REWRITES_CONV (B : BoolThms) (strat : strategy) (ss : simpset)
    (lev : Int) (pconvs : List gconv) (tm : term) : IO (Except String thm) := do
  -- `tryfind (fun (n,cnv) -> ...) pconvs` (simp.ml 280-287).  EVERY step of
  -- the branch - including the final `MP th cth` - is inside the `tryfind`, so
  -- any Failure moves on to the next conversion, and exhaustion raises
  -- `tryfind`'s own message.  (A branch's specific message, such as
  -- "IMP_REWRITES_CONV: Too deep", is caught by `tryfind` and never escapes.)
  let rec go : List gconv → IO (Except String thm)
    | [] => return .error "tryfind"
    | (n, cnv) :: rest => do
        if n >= 4 then go rest
        else
          match ← (cnv tm : IO (Except String thm)) with
          | .error _ => go rest
          | .ok th =>
            let etm := concl th
            if is_eq etm then return .ok th
            else if lev <= 0 then go rest
            else
              match lhand etm with
              | .error _ => go rest
              | .ok l =>
                -- default condition-prover (see `simpset` note)
                match ← (basic_prover B strat ss (lev - 1) l : IO (Except String thm)) with
                | .error _ => go rest
                | .ok cth =>
                  match B.MP th cth with
                  | .ok r => return .ok r
                  | .error _ => go rest
  go pconvs

/-- Traverse into an implicational congruence, simplifying its premises. -/
partial def RUN_SUB_CONV (B : BoolThms) (strat : strategy) (ss : simpset)
    (lev : Int) (triv : Bool) (th : thm) : IO (Except String thm) := ExceptT.run do
  let tm := concl th
  if is_imp tm then do
    let subtm ← liftExcept (lhand tm)
    let (avs, bod) := strip_forall subtm
    let dat : (term × term × simpset × (thm → Except String thm)) ←
      match dest_eq bod with
      | .ok (t, t') => pure (t, t', ss, (fun x => (Except.ok x : Except String thm)))
      | .error _ => do
          let (cxt, deq) ← liftExcept (Basics.dest_imp bod)
          let (t, t') ← liftExcept (dest_eq deq)
          let ass ← liftExcept (ASSUME cxt)
          let ss' ← (AUGMENT_SIMPSET B ass ss : IO (Except String simpset))
          pure (t, t', ss', (fun x => B.DISCH cxt x))
    let (t, t', ss', mk_fun) := dat
    let ethTriv : (thm × Bool) ←
      match ← liftM (strat ss' lev t : IO (Except String thm)) with
      | .ok e => pure (e, false)
      | .error _ => pure (REFL t, triv)
    let (eth, triv') := ethTriv
    let eth' ← liftExcept (do B.GENL avs (← mk_fun eth))
    let th' ←
      if is_var t' then liftExcept (do INST [((← rand (concl eth)), t')] th)
      else (GEN_PART_MATCH B lhand th (concl eth') : IO (Except String thm))
    let th'' ← liftExcept (B.MP th' eth')
    (RUN_SUB_CONV B strat ss lev triv' th'' : IO (Except String thm))
  else if triv then throw "RUN_SUB_CONV"
  else return th

/-- Congruence-based descent: try congruence rules, else structural descent. -/
def GEN_SUB_CONV (B : BoolThms) (strat : strategy) (ss : simpset)
    (lev : Int) (pconvs : List gconv) (tm : term) : IO (Except String thm) := do
  let rec tryCong : List gconv → IO (Except String thm)
    | [] => return .error "GEN_SUB_CONV"
    | (n, cnv) :: rest => do
        if n < 4 then tryCong rest
        else
          match ← (cnv tm : IO (Except String thm)) with
          | .error _ => tryCong rest
          | .ok th =>
            match ← (RUN_SUB_CONV B strat ss lev true th : IO (Except String thm)) with
            | .ok r => return .ok r
            | .error _ => tryCong rest
  match ← (tryCong pconvs : IO (Except String thm)) with
  | .ok r => return .ok r
  | .error _ =>
    if is_comb tm then
      match dest_comb tm with
      | .error e => return .error e
      | .ok (l, r) =>
        match ← (strat ss lev l : IO (Except String thm)) with
        | .ok th1 =>
            match ← (strat ss lev r : IO (Except String thm)) with
            | .ok th2 => return (MK_COMB th1 th2)
            | .error _ => return (AP_THM th1 r)
        | .error _ =>
            match ← (strat ss lev r : IO (Except String thm)) with
            | .ok th2 => return (AP_TERM l th2)
            | .error e => return .error e
    else if is_abs tm then
      match dest_abs tm with
      | .error e => return .error e
      | .ok (v, bod) => do
        match ← (strat ss lev bod : IO (Except String thm)) with
        | .error e => return .error e
        | .ok th =>
          match ABS v th with
          | .ok r => return .ok r
          | .error _ => do
            let gv ← genvar (type_of v)
            match (vsubst [(gv, v)]) with
            | .error e => return .error e
            | .ok gsub =>
              match ← (strat ss lev (gsub bod) : IO (Except String thm)) with
              | .error e => return .error e
              | .ok gthBody =>
                return (do
                  let gth ← ABS gv gthBody
                  let gtm := concl gth
                  let (l, r) ← dest_eq gtm
                  let v' ← variant (frees gtm) v
                  let l' ← alpha v' l
                  let r' ← alpha v' r
                  EQ_MP (← ALPHA gtm (safe_mk_eq l' r')) gth)
    else return .error "GEN_SUB_CONV"

/- The five traversal strategies. Each passes itself as the sub-strategy. -/

/-- Rewrite once at the outermost applicable position. -/
partial def ONCE_DEPTH_SQCONV (B : BoolThms) : strategy := fun ss lev tm => do
  let (.Simpset nt _ _) := ss
  let pconvs := lookup tm nt
  match ← (IMP_REWRITES_CONV B (ONCE_DEPTH_SQCONV B) ss lev pconvs tm : IO (Except String thm)) with
  | .ok r => return .ok r
  | .error _ => (GEN_SUB_CONV B (ONCE_DEPTH_SQCONV B) ss lev pconvs tm : IO (Except String thm))

/-- Rewrite bottom-up, once at each position. -/
partial def DEPTH_SQCONV (B : BoolThms) : strategy := fun ss lev tm => do
  let (.Simpset nt _ _) := ss
  let pconvs := lookup tm nt
  match ← (GEN_SUB_CONV B (DEPTH_SQCONV B) ss lev pconvs tm : IO (Except String thm)) with
  | .ok th1 =>
    match rand (concl th1) with
    | .error _ => return .ok th1
    | .ok tm1 =>
      let pconvs1 := lookup tm1 nt
      match ← (IMP_REWRITES_CONV B (DEPTH_SQCONV B) ss lev pconvs1 tm1 : IO (Except String thm)) with
      | .ok th2 => return (TRANS th1 th2)
      | .error _ => return .ok th1
  | .error _ =>
    (IMP_REWRITES_CONV B (DEPTH_SQCONV B) ss lev pconvs tm : IO (Except String thm))

/-- Rewrite bottom-up, repeatedly, until no change. -/
partial def REDEPTH_SQCONV (B : BoolThms) : strategy := fun ss lev tm => do
  let (.Simpset nt _ _) := ss
  let pconvs := lookup tm nt
  let thR ← (do
    match ← (GEN_SUB_CONV B (REDEPTH_SQCONV B) ss lev pconvs tm : IO (Except String thm)) with
    | .ok th1 =>
      match rand (concl th1) with
      | .error _ => return (Except.ok th1 : Except String thm)
      | .ok tm1 =>
        let pconvs1 := lookup tm1 nt
        match ← (IMP_REWRITES_CONV B (REDEPTH_SQCONV B) ss lev pconvs1 tm1 : IO (Except String thm)) with
        | .ok th2 => return (TRANS th1 th2)
        | .error _ => return (Except.ok th1)
    | .error _ =>
      (IMP_REWRITES_CONV B (REDEPTH_SQCONV B) ss lev pconvs tm : IO (Except String thm)))
  match thR with
  | .error e => return .error e
  | .ok th =>
    match rand (concl th) with
    | .error _ => return .ok th
    | .ok r =>
      match ← (REDEPTH_SQCONV B ss lev r : IO (Except String thm)) with
      | .ok th' => return (TRANS th th')
      | .error _ => return .ok th

/-- Rewrite top-down, repeatedly. -/
partial def TOP_DEPTH_SQCONV (B : BoolThms) : strategy := fun ss lev tm => do
  let (.Simpset nt _ _) := ss
  let pconvs := lookup tm nt
  let th1R ← (do
    match ← (IMP_REWRITES_CONV B (TOP_DEPTH_SQCONV B) ss lev pconvs tm : IO (Except String thm)) with
    | .ok r => return (Except.ok r : Except String thm)
    | .error _ => (GEN_SUB_CONV B (TOP_DEPTH_SQCONV B) ss lev pconvs tm : IO (Except String thm)))
  match th1R with
  | .error e => return .error e
  | .ok th1 =>
    match rand (concl th1) with
    | .error _ => return .ok th1
    | .ok r =>
      match ← (TOP_DEPTH_SQCONV B ss lev r : IO (Except String thm)) with
      | .ok th2 => return (TRANS th1 th2)
      | .error _ => return .ok th1

/-- Rewrite top-down in a single sweep, recursing on rewritten results. -/
partial def TOP_SWEEP_SQCONV (B : BoolThms) : strategy := fun ss lev tm => do
  let (.Simpset nt _ _) := ss
  let pconvs := lookup tm nt
  match ← (IMP_REWRITES_CONV B (TOP_SWEEP_SQCONV B) ss lev pconvs tm : IO (Except String thm)) with
  | .ok th1 =>
    match rand (concl th1) with
    | .error _ => return .ok th1
    | .ok r =>
      match ← (TOP_SWEEP_SQCONV B ss lev r : IO (Except String thm)) with
      | .ok th2 => return (TRANS th1 th2)
      | .error _ => return .ok th1
  | .error _ =>
    (GEN_SUB_CONV B (TOP_SWEEP_SQCONV B) ss lev pconvs tm : IO (Except String thm))

/- ---------------------------------------------------------------------- -/
/- Maintenence of basic rewrites and conv nets for rewriting.             -/
/- ---------------------------------------------------------------------- -/

/-- The current basic rewrite theorems. -/
initialize theRewrites : IO.Ref (List thm) ← IO.mkRef []
/-- The current basic (named, term-indexed) conversions. -/
initialize theConvs : IO.Ref (List (String × (term × ioconv))) ← IO.mkRef []
/-- The compiled basic conversion net. -/
initialize theConvNet : IO.Ref (net gconv) ← IO.mkRef empty_net
/-- The current basic congruence theorems. -/
initialize theCongs : IO.Ref (List thm) ← IO.mkRef []

/-- Recompute `theConvNet` from `theRewrites` and `theConvs`. -/
def rehash_convnet (B : BoolThms) : IO (Except String Unit) := do
  let rewrites ← theRewrites.get
  let convs ← theConvs.get
  -- itlist (net_of_conv pat cnv) conversions empty_net
  let rec addConvs : List (String × (term × ioconv)) → net gconv →
      IO (Except String (net gconv))
    | [], n => return .ok n
    | (_, (pat, cnv)) :: rest, n => do
        match ← (addConvs rest n : IO (Except String (net gconv))) with
        | .error e => return .error e
        | .ok n' => (net_of_conv pat cnv n' : IO (Except String (net gconv)))
  match ← (addConvs convs empty_net : IO (Except String (net gconv))) with
  | .error e => return .error e
  | .ok net0 =>
    -- itlist (net_of_thm true) rewrites net0
    let rec addThms : List thm → net gconv → IO (Except String (net gconv))
      | [], n => return .ok n
      | t :: rest, n => do
          match ← (addThms rest n : IO (Except String (net gconv))) with
          | .error e => return .error e
          | .ok n' => (net_of_thm B true t n' : IO (Except String (net gconv)))
    match ← (addThms rewrites net0 : IO (Except String (net gconv))) with
    | .error e => return .error e
    | .ok net' => do theConvNet.set net'; return .ok ()

/-- Canonicalize a list of theorems via `mk_rewrites false`. -/
private def canonRewrites (B : BoolThms) (thl : List thm) :
    IO (Except String (List thm)) := do
  let rec go : List thm → List thm → IO (Except String (List thm))
    | [], acc => return .ok acc
    | t :: ts, acc => do
        match ← (go ts acc : IO (Except String (List thm))) with
        | .error e => return .error e
        | .ok acc' => (mk_rewrites B false t acc' : IO (Except String (List thm)))
  go thl []

/-- Replace the basic rewrites. -/
def set_basic_rewrites (B : BoolThms) (thl : List thm) : IO (Except String Unit) := do
  match ← (canonRewrites B thl : IO (Except String (List thm))) with
  | .error e => return .error e
  | .ok canon => do theRewrites.set canon; rehash_convnet B

/-- Extend the basic rewrites. -/
def extend_basic_rewrites (B : BoolThms) (thl : List thm) : IO (Except String Unit) := do
  match ← (canonRewrites B thl : IO (Except String (List thm))) with
  | .error e => return .error e
  | .ok canon => do theRewrites.modify (canon ++ ·); rehash_convnet B

/-- The current basic rewrites. -/
def basic_rewrites : IO (List thm) := theRewrites.get

/-- Replace the basic conversions. -/
def set_basic_convs (B : BoolThms) (cnvs : List (String × (term × ioconv))) :
    IO (Except String Unit) := do
  theConvs.set cnvs; rehash_convnet B

/-- Extend the basic conversions (replacing any with the same name). -/
def extend_basic_convs (B : BoolThms) (name : String) (patcong : term × ioconv) :
    IO (Except String Unit) := do
  theConvs.modify (fun cs => (name, patcong) :: cs.filter (fun (n, _) => n != name))
  rehash_convnet B

/-- The current basic conversions. -/
def basic_convs : IO (List (String × (term × ioconv))) := theConvs.get

/-- The current basic conversion net. -/
def basic_net : IO (net gconv) := theConvNet.get

/- ---------------------------------------------------------------------- -/
/- Same thing for the default congruences.                                -/
/- ---------------------------------------------------------------------- -/

/-- Replace the basic congruences. -/
def set_basic_congs (thl : List thm) : IO Unit := theCongs.set thl

/-- Extend the basic congruences. -/
def extend_basic_congs (thl : List thm) : IO Unit :=
  theCongs.modify (fun cs => union' equals_thm thl cs)

/-- The current basic congruences. -/
def basic_congs : IO (List thm) := theCongs.get

/- ---------------------------------------------------------------------- -/
/- IO depth-conversion combinators (mirror Equal's *_QCONV, for ioconv).  -/
/- ---------------------------------------------------------------------- -/

/-- `THENQC`: sequence, succeeding if either does (IO). -/
def thenqcIO (c1 c2 : ioconv) : ioconv := fun tm => do
  match ← (c1 tm : IO (Except String thm)) with
  | .error _ => (c2 tm : IO (Except String thm))
  | .ok th1 =>
    match rand (concl th1) with
    | .error _ => return .ok th1
    | .ok r =>
      match ← (c2 r : IO (Except String thm)) with
      | .ok th2 => return (TRANS th1 th2)
      | .error _ => return .ok th1

/-- `THENCQC`: sequence requiring the first (IO). -/
def thencqcIO (c1 c2 : ioconv) : ioconv := fun tm => do
  match ← (c1 tm : IO (Except String thm)) with
  | .error e => return .error e
  | .ok th1 =>
    match rand (concl th1) with
    | .error _ => return .ok th1
    | .ok r =>
      match ← (c2 r : IO (Except String thm)) with
      | .ok th2 => return (TRANS th1 th2)
      | .error _ => return .ok th1

/-- `COMB_QCONV` (IO). -/
def combQconvIO (c : ioconv) : ioconv := fun tm => do
  match tm with
  | .Comb l r =>
      -- equal.ml 210-216:
      --   (try let th1 = conv l in
      --        try let th2 = conv r in MK_COMB(th1,th2)
      --        with Failure _ -> AP_THM th1 r
      --    with Failure _ -> AP_TERM l (conv r))
      -- The INNER `try` covers `conv r` AND `MK_COMB`; the OUTER covers
      -- `conv l` AND the whole inner expression, so an `AP_THM` failure also
      -- falls to `AP_TERM l (conv r)` (class #9).
      let outer : IO (Except String thm) := do
        match ← (c l : IO (Except String thm)) with
        | .error e => return .error e
        | .ok th1 =>
          let inner : IO (Except String thm) := do
            match ← (c r : IO (Except String thm)) with
            | .error e => return .error e
            | .ok th2 => return (MK_COMB th1 th2)
          match ← inner with
          | .ok th => return .ok th
          | .error _ => return (AP_THM th1 r)
      match ← outer with
      | .ok th => return .ok th
      | .error _ =>
          match ← (c r : IO (Except String thm)) with
          | .ok th2 => return (AP_TERM l th2)
          | .error e => return .error e
  | _ => return .error "COMB_QCONV: Not a combination"

/-- `ABS_CONV` (IO). -/
def absConvIO (c : ioconv) : ioconv := fun tm => do
  match dest_abs tm with
  | .error e => return .error e
  | .ok (v, bod) =>
    match ← (c bod : IO (Except String thm)) with
    | .error e => return .error e
    | .ok th =>
      match ABS v th with
      | .ok res => return .ok res
      | .error _ =>
        -- `try ABS v th with Failure _ -> let gv = genvar(type_of v) in ...`
        let gv ← genvar (type_of v)
        match (do
          let gbod := (← vsubst [(gv, v)]) bod
          pure (gv, gbod) : Except String (term × term)) with
        | .error e => return .error e
        | .ok (gv, gbod) =>
          match ← (c gbod : IO (Except String thm)) with
          | .error e => return .error e
          | .ok gth' =>
            return (do
              let gth ← ABS gv gth'
              let gtm := concl gth
              let (l, r) ← dest_eq gtm
              let v' ← variant (frees gtm) v
              let eqth ← ALPHA gtm (safe_mk_eq (← alpha v' l) (← alpha v' r))
              EQ_MP eqth gth)

/-- `SUB_QCONV` (IO). -/
def subQconvIO (c : ioconv) : ioconv := fun tm =>
  match tm with
  | .Abs _ _ => absConvIO c tm
  | _ => combQconvIO c tm

/-- `REPEATQC` (IO, equal.ml 218): like `REPEATC`, but fails if the first
    application fails, so the depth conversions below see "no change" as a
    failure, as in OCaml. -/
partial def repeatqcIO (c : ioconv) : ioconv := fun tm =>
  thencqcIO c (repeatqcIO c) tm

/-- `ONCE_DEPTH_QCONV` (IO, may fail on no-change). -/
partial def onceDepthQconvIO (c : ioconv) : ioconv := fun tm =>
  orelsecIO c (subQconvIO (onceDepthQconvIO c)) tm

/-- `ONCE_DEPTH_CONV` (IO): total (TRY-wrapped). -/
def onceDepthConvIO (c : ioconv) : ioconv := orelsecIO (onceDepthQconvIO c) allConvIO

/-- `TOP_DEPTH_QCONV` (IO, may fail on no-change). -/
partial def topDepthQconvIO (c : ioconv) : ioconv := fun tm =>
  thenqcIO (repeatqcIO c)
    (thencqcIO (subQconvIO (topDepthQconvIO c)) (thencqcIO c (topDepthQconvIO c))) tm

/-- `TOP_DEPTH_CONV` (IO): total (TRY-wrapped). -/
def topDepthConvIO (c : ioconv) : ioconv := orelsecIO (topDepthQconvIO c) allConvIO

/-- `DEPTH_QCONV` (IO, bottom-up, may fail on no-change). -/
partial def depthQconvIO (c : ioconv) : ioconv := fun tm =>
  thenqcIO (subQconvIO (depthQconvIO c)) (repeatqcIO c) tm

/-- `DEPTH_CONV` (IO): total (TRY-wrapped). -/
def depthConvIO (c : ioconv) : ioconv := orelsecIO (depthQconvIO c) allConvIO

/-- `REDEPTH_QCONV` (IO, bottom-up repeatedly, may fail on no-change). -/
partial def redepthQconvIO (c : ioconv) : ioconv := fun tm =>
  thenqcIO (subQconvIO (redepthQconvIO c)) (thencqcIO c (redepthQconvIO c)) tm

/-- `REDEPTH_CONV` (IO): total (TRY-wrapped). -/
def redepthConvIO (c : ioconv) : ioconv := orelsecIO (redepthQconvIO c) allConvIO

/-- `TOP_SWEEP_QCONV` (IO, may fail on no-change). -/
partial def topSweepQconvIO (c : ioconv) : ioconv := fun tm =>
  thenqcIO (repeatqcIO c) (subQconvIO (topSweepQconvIO c)) tm

/-- `TOP_SWEEP_CONV` (IO): total (TRY-wrapped). -/
def topSweepConvIO (c : ioconv) : ioconv := orelsecIO (topSweepQconvIO c) allConvIO

/-- `TRY_CONV` (IO): apply `c`, or `REFL` on failure. -/
def tryConvIO (c : ioconv) : ioconv := orelsecIO c allConvIO

/-- `RAND_CONV` (IO): apply `c` to the operand of an application. -/
def randConvIO (c : ioconv) : ioconv := fun tm => do
  match dest_comb tm with
  | .error e => return .error e
  | .ok (l, r) =>
    match ← (c r : IO (Except String thm)) with
    | .error e => return .error e
    | .ok th => return (AP_TERM l th)

/-- `RATOR_CONV` (IO): apply `c` to the operator of an application. -/
def ratorConvIO (c : ioconv) : ioconv := fun tm => do
  match dest_comb tm with
  | .error e => return .error e
  | .ok (l, r) =>
    match ← (c l : IO (Except String thm)) with
    | .error e => return .error e
    | .ok th => return (AP_THM th r)

/-- `LAND_CONV` (IO): apply `c` to the left operand of a binary application. -/
def landConvIO (c : ioconv) : ioconv := ratorConvIO (randConvIO c)

/-- `BINDER_CONV` (IO): apply `c` under a binder (`!x. _`, `?x. _`, …). -/
def binderConvIO (c : ioconv) : ioconv := fun tm =>
  -- equal.ml's BINDER_CONV is CONDITIONAL:
  --   if is_abs tm then ABS_CONV conv tm else RAND_CONV(ABS_CONV conv) tm
  -- A bare abstraction must take the ABS_CONV path; only a quantified term
  -- `!x. _` / `?x. _` (a binder constant applied to an abstraction) takes the
  -- RAND_CONV path, so the conversion reaches the correct subterm.
  if is_abs tm then absConvIO c tm else randConvIO (absConvIO c) tm

/-- `PATH_CONV` (equal.ml) for an `ioconv`. -/
def pathConvIO (s : String) (cnv : ioconv) : ioconv :=
  let rec path_conv : List String → ioconv
    | []       => cnv
    | "l" :: t => ratorConvIO (path_conv t)
    | "r" :: t => randConvIO (path_conv t)
    | _ :: t   => absConvIO (path_conv t)
  path_conv (explode s)

/-- `BINOP_CONV` (IO): apply `c` to both operands of a binary application. -/
def binopConvIO (c : ioconv) : ioconv := fun tm => do
  match dest_comb tm with
  | .error e => return .error e
  | .ok (lop, r) =>
    match dest_comb lop with
    | .error e => return .error e
    | .ok (op, l) =>
      -- OCaml: `MK_COMB(AP_TERM op (conv l),conv r)`, arguments right to left.
      match ← (c r : IO (Except String thm)) with
      | .error e => return .error e
      | .ok rth =>
        match ← (c l : IO (Except String thm)) with
        | .error e => return .error e
        | .ok lth =>
          return (do MK_COMB (← AP_TERM op lth) rth)

/-- `COMB2_CONV` (IO): apply `lconv` to operator, `rconv` to operand. -/
def comb2ConvIO (lconv rconv : ioconv) : ioconv := fun tm => do
  match tm with
  | .Comb l r =>
      -- OCaml: `MK_COMB(lconv l,rconv r)`, arguments right to left.
      match ← (rconv r : IO (Except String thm)) with
      | .error e => return .error e
      | .ok rth =>
        match ← (lconv l : IO (Except String thm)) with
        | .error e => return .error e
        | .ok lth => return (MK_COMB lth rth)
  | _ => return (.error "COMB2_CONV: Not a combination")

/-- `COMB_CONV` (IO): apply `c` to both the operator and operand. -/
def combConvIO (c : ioconv) : ioconv := comb2ConvIO c c

/-- `DEPTH_BINOP_CONV op c` (IO): apply `c` at the leaves of the `op`-tree. -/
partial def depthBinopConvIO (op : term) (c : ioconv) : ioconv := fun tm => do
  match tm with
  | .Comb (.Comb op' _) _ =>
      if op' == op then
        match dest_binop op tm with
        | .error e => return .error e
        | .ok (l, r) =>
          match ← (depthBinopConvIO op c l : IO (Except String thm)) with
          | .error e => return .error e
          | .ok lth =>
            match ← (depthBinopConvIO op c r : IO (Except String thm)) with
            | .error e => return .error e
            | .ok rth => return (do MK_COMB (← AP_TERM op' lth) rth)
      else (c tm : IO (Except String thm))
  | _ => (c tm : IO (Except String thm))

/- ---------------------------------------------------------------------- -/
/- Main rewriting conversions.                                            -/
/- ---------------------------------------------------------------------- -/

/-- The general rewriting conversion: canonicalize `thl`, add to `builtin_net`,
    and traverse with `cnvl`. -/
def GENERAL_REWRITE_CONV (B : BoolThms) (rep : Bool) (cnvl : ioconv → ioconv)
    (builtin_net : net gconv) (thl : List thm) : IO (Except String ioconv) := do
  match ← (canonRewrites B thl : IO (Except String (List thm))) with
  | .error e => return .error e
  | .ok thl_canon =>
    -- itlist (net_of_thm rep) thl_canon builtin_net
    let rec addAll : List thm → net gconv → IO (Except String (net gconv))
      | [], n => return .ok n
      | t :: ts, n => do
          match ← (addAll ts n : IO (Except String (net gconv))) with
          | .error e => return .error e
          | .ok n' => (net_of_thm B rep t n' : IO (Except String (net gconv)))
    match ← (addAll thl_canon builtin_net : IO (Except String (net gconv))) with
    | .error e => return .error e
    | .ok final_net => return .ok (cnvl (fun tm => REWRITES_CONV final_net tm))

/-- `GEN_REWRITE_CONV cnvl thl`. -/
def GEN_REWRITE_CONV (B : BoolThms) (cnvl : ioconv → ioconv) (thl : List thm) :
    IO (Except String ioconv) :=
  GENERAL_REWRITE_CONV B false cnvl empty_net thl

/-- `PURE_REWRITE_CONV thl`. -/
def PURE_REWRITE_CONV (B : BoolThms) (thl : List thm) : IO (Except String ioconv) :=
  GENERAL_REWRITE_CONV B true topDepthConvIO empty_net thl

/-- `REWRITE_CONV thl` (uses the basic net). -/
def REWRITE_CONV (B : BoolThms) (thl : List thm) : IO (Except String ioconv) := do
  GENERAL_REWRITE_CONV B true topDepthConvIO (← basic_net) thl

/-- `PURE_ONCE_REWRITE_CONV thl`. -/
def PURE_ONCE_REWRITE_CONV (B : BoolThms) (thl : List thm) : IO (Except String ioconv) :=
  GENERAL_REWRITE_CONV B false onceDepthConvIO empty_net thl

/-- `ONCE_REWRITE_CONV thl` (uses the basic net). -/
def ONCE_REWRITE_CONV (B : BoolThms) (thl : List thm) : IO (Except String ioconv) := do
  GENERAL_REWRITE_CONV B false onceDepthConvIO (← basic_net) thl

/- ---------------------------------------------------------------------- -/
/- Rewriting rules and tactics.                                           -/
/- ---------------------------------------------------------------------- -/

/-- Apply an (IO) rewrite conversion as a rule. -/
def REWRITE_RULE (B : BoolThms) (thl : List thm) (th : thm) : IO (Except String thm) := do
  match ← (REWRITE_CONV B thl : IO (Except String ioconv)) with
  | .error e => return .error e
  | .ok cnv => (convRuleIO cnv th : IO (Except String thm))

/-- Apply a pure (IO) rewrite conversion as a rule. -/
def PURE_REWRITE_RULE (B : BoolThms) (thl : List thm) (th : thm) : IO (Except String thm) := do
  match ← (PURE_REWRITE_CONV B thl : IO (Except String ioconv)) with
  | .error e => return .error e
  | .ok cnv => (convRuleIO cnv th : IO (Except String thm))

/-- Rewrite tactic (uses the basic net). -/
def REWRITE_TAC (B : BoolThms) (thl : List thm) : tactic := fun g => do
  match ← (REWRITE_CONV B thl : IO (Except String ioconv)) with
  | .error e => return .error e
  | .ok cnv => (Tactics.CONV_TAC B cnv g : IO (Except String goalstate))

/-- Pure rewrite tactic. -/
def PURE_REWRITE_TAC (B : BoolThms) (thl : List thm) : tactic := fun g => do
  match ← (PURE_REWRITE_CONV B thl : IO (Except String ioconv)) with
  | .error e => return .error e
  | .ok cnv => (Tactics.CONV_TAC B cnv g : IO (Except String goalstate))

/-- Once-rewrite tactic (uses the basic net). -/
def ONCE_REWRITE_TAC (B : BoolThms) (thl : List thm) : tactic := fun g => do
  match ← (ONCE_REWRITE_CONV B thl : IO (Except String ioconv)) with
  | .error e => return .error e
  | .ok cnv => (Tactics.CONV_TAC B cnv g : IO (Except String goalstate))

/-- Rewrite tactic including the goal's assumptions. -/
def ASM_REWRITE_TAC (B : BoolThms) (thl : List thm) : tactic :=
  Tactics.ASM (REWRITE_TAC B) thl

/-- Generic rewrite rule with an explicit traversal `cnvl`. -/
def GEN_REWRITE_RULE (B : BoolThms) (cnvl : ioconv → ioconv) (thl : List thm)
    (th : thm) : IO (Except String thm) := do
  match ← (GEN_REWRITE_CONV B cnvl thl : IO (Except String ioconv)) with
  | .error e => return .error e
  | .ok cnv => (convRuleIO cnv th : IO (Except String thm))

/-- Once-rewrite rule (uses the basic net). -/
def ONCE_REWRITE_RULE (B : BoolThms) (thl : List thm) (th : thm) : IO (Except String thm) := do
  match ← (ONCE_REWRITE_CONV B thl : IO (Except String ioconv)) with
  | .error e => return .error e
  | .ok cnv => (convRuleIO cnv th : IO (Except String thm))

/-- `PURE_ONCE_REWRITE_RULE` (simp.ml): rewrite ONCE at each subterm, with
    NO basic rewrites. -/
def PURE_ONCE_REWRITE_RULE (B : BoolThms) (thl : List thm) (th : thm) :
    IO (Except String thm) := do
  match ← (PURE_ONCE_REWRITE_CONV B thl : IO (Except String ioconv)) with
  | .error e => return .error e
  | .ok cnv => (convRuleIO cnv th : IO (Except String thm))

/-- Rewrite rule including the theorem's own hypotheses. -/
def ASM_REWRITE_RULE (B : BoolThms) (thl : List thm) (th : thm) : IO (Except String thm) := do
  match (hyp th).mapM (fun h => ASSUME h) with
  | .error e => return .error e
  | .ok asmThs => (REWRITE_RULE B (asmThs ++ thl) th : IO (Except String thm))

/-- Pure rewrite rule including the theorem's own hypotheses. -/
def PURE_ASM_REWRITE_RULE (B : BoolThms) (thl : List thm) (th : thm) :
    IO (Except String thm) := do
  match (hyp th).mapM (fun h => ASSUME h) with
  | .error e => return .error e
  | .ok asmThs => (PURE_REWRITE_RULE B (asmThs ++ thl) th : IO (Except String thm))

/-- Pure once-rewrite rule including the theorem's own hypotheses. -/
def PURE_ONCE_ASM_REWRITE_RULE (B : BoolThms) (thl : List thm) (th : thm) :
    IO (Except String thm) := do
  match (hyp th).mapM (fun h => ASSUME h) with
  | .error e => return .error e
  | .ok asmThs => (PURE_ONCE_REWRITE_RULE B (asmThs ++ thl) th : IO (Except String thm))

/-- Once-rewrite rule including the theorem's own hypotheses. -/
def ONCE_ASM_REWRITE_RULE (B : BoolThms) (thl : List thm) (th : thm) :
    IO (Except String thm) := do
  match (hyp th).mapM (fun h => ASSUME h) with
  | .error e => return .error e
  | .ok asmThs => (ONCE_REWRITE_RULE B (asmThs ++ thl) th : IO (Except String thm))

/-- Generic rewrite tactic with an explicit traversal `cnvl`. -/
def GEN_REWRITE_TAC (B : BoolThms) (cnvl : ioconv → ioconv) (thl : List thm) :
    tactic := fun g => do
  match ← (GEN_REWRITE_CONV B cnvl thl : IO (Except String ioconv)) with
  | .error e => return .error e
  | .ok cnv => (Tactics.CONV_TAC B cnv g : IO (Except String goalstate))

/-- Pure once-rewrite tactic. -/
def PURE_ONCE_REWRITE_TAC (B : BoolThms) (thl : List thm) : tactic := fun g => do
  match ← (PURE_ONCE_REWRITE_CONV B thl : IO (Except String ioconv)) with
  | .error e => return .error e
  | .ok cnv => (Tactics.CONV_TAC B cnv g : IO (Except String goalstate))

/-- Pure rewrite tactic including assumptions. -/
def PURE_ASM_REWRITE_TAC (B : BoolThms) (thl : List thm) : tactic :=
  Tactics.ASM (PURE_REWRITE_TAC B) thl

/-- Once-rewrite tactic including assumptions. -/
def ONCE_ASM_REWRITE_TAC (B : BoolThms) (thl : List thm) : tactic :=
  Tactics.ASM (ONCE_REWRITE_TAC B) thl

/-- Pure once-rewrite tactic including assumptions. -/
def PURE_ONCE_ASM_REWRITE_TAC (B : BoolThms) (thl : List thm) : tactic :=
  Tactics.ASM (PURE_ONCE_REWRITE_TAC B) thl

/- ---------------------------------------------------------------------- -/
/- Simplification functions.                                              -/
/- ---------------------------------------------------------------------- -/

/-- The general simplification conversion: augment the simpset with `thl`, then
    traverse with `strat` at depth `lev` (wrapped in `TRY_CONV`). -/
def GEN_SIMPLIFY_CONV (B : BoolThms) (strat : strategy) (ss : simpset)
    (lev : Int) (thl : List thm) : IO (Except String ioconv) := do
  -- ss' = itlist AUGMENT_SIMPSET thl ss   (right fold, IO)
  let rec augAll : List thm → simpset → IO (Except String simpset)
    | [], s => return .ok s
    | t :: ts, s => do
        match ← (augAll ts s : IO (Except String simpset)) with
        | .error e => return .error e
        | .ok s' => (AUGMENT_SIMPSET B t s' : IO (Except String simpset))
  match ← (augAll thl ss : IO (Except String simpset)) with
  | .error e => return .error e
  | .ok ss' => return .ok (orelsecIO (fun tm => strat ss' lev tm) allConvIO)

/-- Simplify, rewriting once at each position. -/
def ONCE_SIMPLIFY_CONV (B : BoolThms) (ss : simpset) (thl : List thm) :
    IO (Except String ioconv) :=
  GEN_SIMPLIFY_CONV B (ONCE_DEPTH_SQCONV B) ss 1 thl

/-- Full simplification. -/
def SIMPLIFY_CONV (B : BoolThms) (ss : simpset) (thl : List thm) :
    IO (Except String ioconv) :=
  GEN_SIMPLIFY_CONV B (TOP_DEPTH_SQCONV B) ss 3 thl

/- ---------------------------------------------------------------------- -/
/- Simple but useful default version.                                     -/
/- ---------------------------------------------------------------------- -/

/-- The empty simpset (basic prover, no rewrites/congruences). -/
def empty_ss (B : BoolThms) : simpset :=
  .Simpset empty_net [] (fun th sofar => mk_rewrites B true th sofar)

/-- The default simpset seeded with the basic net/congruences plus `thl`. -/
def basic_ss (B : BoolThms) (thl : List thm) : IO (Except String simpset) := do
  let rewmaker : thm → List thm → IO (Except String (List thm)) :=
    fun th sofar => mk_rewrites B true th sofar
  -- cthms = itlist rewmaker thl []
  let rec mkAll : List thm → List thm → IO (Except String (List thm))
    | [], acc => return .ok acc
    | t :: ts, acc => do
        match ← (mkAll ts acc : IO (Except String (List thm))) with
        | .error e => return .error e
        | .ok acc' => (rewmaker t acc' : IO (Except String (List thm)))
  match ← (mkAll thl [] : IO (Except String (List thm))) with
  | .error e => return .error e
  | .ok cthms =>
    let bnet ← basic_net
    -- net' = itlist (net_of_thm true) cthms bnet
    let rec addThms : List thm → net gconv → IO (Except String (net gconv))
      | [], n => return .ok n
      | t :: ts, n => do
          match ← (addThms ts n : IO (Except String (net gconv))) with
          | .error e => return .error e
          | .ok n' => (net_of_thm B true t n' : IO (Except String (net gconv)))
    match ← (addThms cthms bnet : IO (Except String (net gconv))) with
    | .error e => return .error e
    | .ok net' =>
      let congs ← basic_congs
      -- net'' = itlist net_of_cong congs net'
      let rec addCongs : List thm → net gconv → IO (Except String (net gconv))
        | [], n => return .ok n
        | t :: ts, n => do
            match ← (addCongs ts n : IO (Except String (net gconv))) with
            | .error e => return .error e
            | .ok n' => (net_of_cong B t n' : IO (Except String (net gconv)))
      match ← (addCongs congs net' : IO (Except String (net gconv))) with
      | .error e => return .error e
      | .ok net'' => return .ok (.Simpset net'' [] rewmaker)

/-- Simplify with the basic simpset and extra rewrites `thl`. -/
def SIMP_CONV (B : BoolThms) (thl : List thm) : IO (Except String ioconv) := do
  match ← (basic_ss B [] : IO (Except String simpset)) with
  | .error e => return .error e
  | .ok ss => (SIMPLIFY_CONV B ss thl : IO (Except String ioconv))

/-- Simplify with only the given rewrites (no basic net). -/
def PURE_SIMP_CONV (B : BoolThms) (thl : List thm) : IO (Except String ioconv) :=
  SIMPLIFY_CONV B (empty_ss B) thl

/-- Simplify once with the basic simpset. -/
def ONCE_SIMP_CONV (B : BoolThms) (thl : List thm) : IO (Except String ioconv) := do
  match ← (basic_ss B [] : IO (Except String simpset)) with
  | .error e => return .error e
  | .ok ss => (ONCE_SIMPLIFY_CONV B ss thl : IO (Except String ioconv))

/-- Simplification rule. -/
def SIMP_RULE (B : BoolThms) (thl : List thm) (th : thm) : IO (Except String thm) := do
  match ← (SIMP_CONV B thl : IO (Except String ioconv)) with
  | .error e => return .error e
  | .ok cnv => (convRuleIO cnv th : IO (Except String thm))

/-- Pure simplification rule. -/
def PURE_SIMP_RULE (B : BoolThms) (thl : List thm) (th : thm) : IO (Except String thm) := do
  match ← (PURE_SIMP_CONV B thl : IO (Except String ioconv)) with
  | .error e => return .error e
  | .ok cnv => (convRuleIO cnv th : IO (Except String thm))

/-- Once-simplification rule. -/
def ONCE_SIMP_RULE (B : BoolThms) (thl : List thm) (th : thm) : IO (Except String thm) := do
  match ← (ONCE_SIMP_CONV B thl : IO (Except String ioconv)) with
  | .error e => return .error e
  | .ok cnv => (convRuleIO cnv th : IO (Except String thm))

/-- Simplification tactic. -/
def SIMP_TAC (B : BoolThms) (thl : List thm) : tactic := fun g => do
  match ← (SIMP_CONV B thl : IO (Except String ioconv)) with
  | .error e => return .error e
  | .ok cnv => (Tactics.CONV_TAC B cnv g : IO (Except String goalstate))

/-- Pure simplification tactic. -/
def PURE_SIMP_TAC (B : BoolThms) (thl : List thm) : tactic := fun g => do
  match ← (PURE_SIMP_CONV B thl : IO (Except String ioconv)) with
  | .error e => return .error e
  | .ok cnv => (Tactics.CONV_TAC B cnv g : IO (Except String goalstate))

/-- Once-simplification tactic. -/
def ONCE_SIMP_TAC (B : BoolThms) (thl : List thm) : tactic := fun g => do
  match ← (ONCE_SIMP_CONV B thl : IO (Except String ioconv)) with
  | .error e => return .error e
  | .ok cnv => (Tactics.CONV_TAC B cnv g : IO (Except String goalstate))

/-- Simplification tactic including assumptions. -/
def ASM_SIMP_TAC (B : BoolThms) (thl : List thm) : tactic :=
  Tactics.ASM (SIMP_TAC B) thl

/-- Pure simplification tactic including assumptions. -/
def PURE_ASM_SIMP_TAC (B : BoolThms) (thl : List thm) : tactic :=
  Tactics.ASM (PURE_SIMP_TAC B) thl

/-- Once-simplification tactic including assumptions. -/
def ONCE_ASM_SIMP_TAC (B : BoolThms) (thl : List thm) : tactic :=
  Tactics.ASM (ONCE_SIMP_TAC B) thl

/- ---------------------------------------------------------------------- -/
/- Apply-and-go variants: build the conversion and apply it to a term in  -/
/- one step (HOL Light style, where a *_CONV is directly a conversion).   -/
/- ---------------------------------------------------------------------- -/

/-- Run a conversion-builder and apply the resulting conversion to `tm`. -/
def applyConv (builder : IO (Except String ioconv)) (tm : term) :
    IO (Except String thm) := do
  match ← builder with
  | .error e => return .error e
  | .ok cnv => (cnv tm : IO (Except String thm))

/-- `REWRITE_CONV thl tm` in one step. -/
def REWRITE_CONV' (B : BoolThms) (thl : List thm) (tm : term) : IO (Except String thm) :=
  applyConv (REWRITE_CONV B thl) tm
/-- `PURE_REWRITE_CONV thl tm` in one step. -/
def PURE_REWRITE_CONV' (B : BoolThms) (thl : List thm) (tm : term) : IO (Except String thm) :=
  applyConv (PURE_REWRITE_CONV B thl) tm
/-- `ONCE_REWRITE_CONV thl tm` in one step. -/
def ONCE_REWRITE_CONV' (B : BoolThms) (thl : List thm) (tm : term) : IO (Except String thm) :=
  applyConv (ONCE_REWRITE_CONV B thl) tm
/-- `PURE_ONCE_REWRITE_CONV thl tm` in one step. -/
def PURE_ONCE_REWRITE_CONV' (B : BoolThms) (thl : List thm) (tm : term) : IO (Except String thm) :=
  applyConv (PURE_ONCE_REWRITE_CONV B thl) tm
/-- `GEN_REWRITE_CONV cnvl thl tm` in one step. -/
def GEN_REWRITE_CONV' (B : BoolThms) (cnvl : ioconv → ioconv) (thl : List thm)
    (tm : term) : IO (Except String thm) :=
  applyConv (GEN_REWRITE_CONV B cnvl thl) tm
/-- `SIMP_CONV thl tm` in one step. -/
def SIMP_CONV' (B : BoolThms) (thl : List thm) (tm : term) : IO (Except String thm) :=
  applyConv (SIMP_CONV B thl) tm
/-- `PURE_SIMP_CONV thl tm` in one step. -/
def PURE_SIMP_CONV' (B : BoolThms) (thl : List thm) (tm : term) : IO (Except String thm) :=
  applyConv (PURE_SIMP_CONV B thl) tm
/-- `ONCE_SIMP_CONV thl tm` in one step. -/
def ONCE_SIMP_CONV' (B : BoolThms) (thl : List thm) (tm : term) : IO (Except String thm) :=
  applyConv (ONCE_SIMP_CONV B thl) tm

/- ---------------------------------------------------------------------- -/
/- Abbreviation tactics.                                                  -/
/- ---------------------------------------------------------------------- -/

/-- Introduce an abbreviation `v = t` (with `v` applied to `vs`), rewriting the
    goal and assumptions to use the new variable. -/
def ABBREV_TAC (B : BoolThms) (tm : term) : tactic := fun g => ExceptT.run do
  let (cvs, t) ← liftExcept (dest_eq tm)
  let (v, vs) := strip_comb cvs
  let rs ← liftExcept (list_mk_abs vs t)
  let mkEq ← (mk_eq : IO (Except String ((term × term) → Except String term)))
  let eq ← liftExcept (mkEq (rs, v))
  -- th1 = itlist (fun v th => CONV_RULE(LAND_CONV BETA_CONV)(AP_THM th v)) (rev vs) (ASSUME eq)
  let step (v : term) (th : thm) : Except String thm := do
    CONV_RULE (LAND_CONV BETA_CONV) (← AP_THM th v)
  let th1 ← liftExcept (do itlistM step vs.reverse (← ASSUME eq))
  let th2 ← liftExcept (do B.SIMPLE_CHOOSE v (← B.SIMPLE_EXISTS v (← B.GENL vs th1)))
  let exq ← liftExcept (mk_exists v eq)
  let existsThm ← liftExcept (B.EXISTS (exq, rs) (REFL rs))
  let th3 ← liftExcept (PROVE_HYP existsThm th2)
  let (asl, w) := g
  let avoids := itlist (fun (p : String × thm) acc => union (frees (concl p.2)) acc)
                       asl (frees w)
  if mem v avoids then throw "ABBREV_TAC: variable already used"
  else
    (Tactics.CHOOSE_THEN B
       (fun th => Tactics.THEN B
                    (Tactics.RULE_ASSUM_TAC B (fun a => PURE_ONCE_REWRITE_RULE B [th] a))
                    (Tactics.THEN B
                      (PURE_ONCE_REWRITE_TAC B [th])
                      (Tactics.ASSUME_TAC B th)))
       th3 g
      : IO (Except String goalstate))

/-- Expand an abbreviation named `s` (substitute its definition back and beta). -/
def EXPAND_TAC (B : BoolThms) (s : String) : tactic :=
  Tactics.THEN B
    (Tactics.FIRST_ASSUM (fun th => fun g => do
      -- SUBST1_TAC o SYM o check((=) s o fst o dest_var o rhs o concl)
      match (do
        let r ← rhs (concl th)
        let (nm, _) ← dest_var r
        if nm == s then .ok th else failwith "EXPAND_TAC" : Except String thm) with
      | .error e => return .error e
      | .ok th' =>
        match SYM th' with
        | .error e => return .error e
        | .ok sth => (Tactics.SUBST1_TAC B sth g : IO (Except String goalstate))))
    (Tactics.BETA_TAC B)

end HolCore.Simp
