/- File: Lib.lean
Convenient library functions.
John Harrison, University of Cambridge Computer Laboratory
Original: (c) Copyright, University of Cambridge 1998
Original: (c) Copyright, John Harrison 1998-2007
Lean4 translation by Chris Walton 2026 -/

namespace HolCore.Lib

/-- The HOL Light `failwith`. -/
def failwith (msg : String) : Except String α := Except.error msg

/-- `fail ()` in HOL Light raises `Failure ""`. -/
def fail : Except String α := Except.error ""

/- ---------------------------------------------------------------------- -/
/- Combinators.                                                           -/
/- ---------------------------------------------------------------------- -/

/-- Curry a function on pairs: `curry f x y = f (x, y)`. -/
def curry (f : α × β → γ) (x : α) (y : β) : γ := f (x, y)
/-- Uncurry a two-argument function: `uncurry f (x, y) = f x y`. -/
def uncurry (f : α → β → γ) : α × β → γ
  | (x, y) => f x y
/-- The identity combinator: `I x = x`. -/
def I (x : α) : α := x
/-- The constant combinator: `K x y = x`. -/
def K (x : α) (_ : β) : α := x
/-- Swap the arguments of a two-argument function: `C f x y = f y x`. -/
def C (f : α → β → γ) (x : β) (y : α) : γ := f y x
/-- The duplicating combinator: `W f x = f x x`. -/
def W (f : α → α → β) (x : α) : β := f x x
/-- Function composition: `comp f g x = f (g x)` (HOL Light's `o`). -/
def comp (f : β → γ) (g : α → β) (x : α) : γ := f (g x)
infixl:90 " o " => comp

/- ---------------------------------------------------------------------- -/
/- Effectful variants of HOL Light's `o`.                                  -/
/- ---------------------------------------------------------------------- -/
/-
  HOL Light writes every composition as `f o g`: OCaml failure is a raise, not a
  type.  Our port makes those functions `Except String`- or
  `IO (Except String ·)`-valued, so plain `comp` stops typing as soon as an
  effectful stage sits INNER (to the right) of a total one.  These variants cover
  the remaining shapes.

  *** EVERY ONE RUNS `g` FIRST, like OCaml's `f o g`: the RIGHTMOST stage runs
  FIRST. *** Reversing this order is a subtle bug, so the order is restated at
  each definition.

  *** ALL ARE LEFT-ASSOCIATIVE (`infixl:90`), which is what lets mixed chains go
  unparenthesised. *** Left association accumulates the OUTER end first, so each
  operator need only match "the composite so far" against "the next stage
  inwards".  Pick by that LOCAL shape:

    composite so far    next stage inwards         operator
    total               total                      `o`
    effectful           total                      `o`   (effect outermost)
    effectful           effectful, SAME monad      `oM`
    total               `Except ε`                 `oEm`
    total               `IO (Except ε ·)`          `oIOm`
    `IO (Except ε ·)`   `IO (Except ε ·)`          `oIO`
    `Except ε`          `IO (Except ε ·)`          `oEIO`

  So `hd o snd o dest_type o snd o dest_const` (meson.ml 711) transcribes stage
  for stage as `hd o snd oM dest_type o snd oM dest_const`.  `oEm`/`oIOm` are
  needed only when the OUTERMOST stage is total, as in `snd o dest_forall`
  (impconv.ml 151).  Any grouping that typechecks computes the same function
  (composition and bind are both associative) - verified on a five-stage mixed
  chain against a hand-written reference across all of its error paths.

  TWO FACTS ESTABLISHED BY EXPERIMENT, recorded so they are not re-litigated:
    * `oIO`/`oIOm` are NOT subsumed by `oM` or by Lean's built-in `<=<`.
      `IO (Except ε α)` IS `ExceptT ε IO α`, but Lean resolves the head symbol
      `IO` to `Monad IO` and never tries `Monad (ExceptT ε IO)`, so both demand
      `Except ε β → IO γ` for the outer stage and fail.  A competing `Monad`
      instance on an abbreviation of `IO ∘ Except` was rejected: it would risk
      instance-resolution ambiguity across this monad-heavy codebase.
    * `oM` IS Lean's `<=<`, provided under an `o`-shaped name purely so a
      transcribed chain scans like the OCaml it came from.

  `oT`/`oTIO` (the `thm_tactic o rule` shape, by far the commonest) live in
  `HolCore/Tactics.lean`, where `thm_tactic` is defined; they bind LOOSER (89) so
  a rule chain to their right groups first.
-/

/-- Kleisli composition in an arbitrary monad - HOL Light's `o` for two
    functions effectful in the SAME monad (e.g. both `Except ε`, or both `IO`).
    Runs `g` FIRST, then `f`, matching OCaml's `f o g`. -/
def compM {α β γ : Type} {m : Type → Type} [Monad m]
    (f : β → m γ) (g : α → m β) : α → m γ := fun x => g x >>= f
infixl:90 " oM " => compM

/-- HOL Light's `o` with a TOTAL outer function and an `Except ε`-valued inner
    one: run `g` FIRST, then map the pure `f` over a successful result.  (The
    `Except`-only counterpart of `oIOm`; equals `fun x => f <$> g x`.) -/
def compEmap {α β γ ε : Type} (f : β → γ) (g : α → Except ε β) :
    α → Except ε γ := fun x => f <$> g x
infixl:90 " oEm " => compEmap

/-- HOL Light's `o` with an `Except ε`-valued OUTER function over an
    `IO (Except ε ·)`-valued inner one - e.g. `SYM o MATCH_MP th`,
    `EQT_INTRO o TAUT`, `GSYM o PURE_REWRITE_RULE[...]`, `CONJUNCT2 o
    GEN_REWRITE_RULE ...`.  This is the mirror of `oIO`: there the outer is
    already in IO, here it is pure and must be LIFTED into IO after the inner
    stage has run.  Runs `g` FIRST and short-circuits on its error. -/
def compEIO {α β γ ε : Type} (f : β → Except ε γ) (g : α → IO (Except ε β)) :
    α → IO (Except ε γ) := fun x => do
  match ← g x with
  | .ok b => return f b
  | .error e => return .error e
infixl:90 " oEIO " => compEIO

/-- HOL Light's `o` for the port's dominant effectful shape,
    `α → IO (Except ε β)` - what a raising OCaml function becomes here.
    Runs `g` FIRST and SHORT-CIRCUITS on its error, so the composite fails
    exactly where the OCaml would have raised. -/
def compIOE {α β γ ε : Type} (f : β → IO (Except ε γ)) (g : α → IO (Except ε β)) :
    α → IO (Except ε γ) := fun x => do
  match ← g x with
  | .ok b => f b
  | .error e => return .error e
infixl:90 " oIO " => compIOE

/-- HOL Light's `o` with a TOTAL outer function and an `IO (Except ε ·)`-valued
    inner one: run `g` FIRST, then map the pure `f` over a successful result. -/
def compIOEmap {α β γ ε : Type} (f : β → γ) (g : α → IO (Except ε β)) :
    α → IO (Except ε γ) := fun x => do
  match ← g x with
  | .ok b => return .ok (f b)
  | .error e => return .error e
infixl:90 " oIOm " => compIOEmap
/-- Product of functions: `F_F f g (x, y) = (f x, g y)`. -/
def F_F (f : α → γ) (g : β → δ) : α × β → γ × δ
  | (x, y) => (f x, g y)
infixr:80 " ‖|| " => F_F    -- Lean can't use F_F as a symbol
/-- Reverse application: `revApply x f = f x` (HOL Light's `|>`). -/
def revApply (x : α) (f : α → β) : β := f x
/- infixl:50 " |> " => revApply -- |> already in Lean -/

/- ---------------------------------------------------------------------- -/
/- List basics.                                                           -/
/- ---------------------------------------------------------------------- -/

/-- Head of a list. Fails with `hd` on the empty list. -/
def hd : List α → Except String α
  | h :: _ => pure h
  | _ => failwith "hd"

/-- Tail of a list. Fails with `tl` on the empty list. -/
def tl : List α → Except String (List α)
  | _ :: t => pure t
  | _ => failwith "tl"

/-- Map a function over a list (HOL Light's `map`). -/
def map' (f : α → β) : List α → List β  -- Lean already has List.map
  | [] => []
  | x :: t => f x :: map' f t

/-- Last element of a list. Fails with `last` on the empty list. -/
def last : List α → Except String α
  | [x] => pure x
  | _ :: t => last t
  | [] => failwith "last"

/-- All but the last element of a list. Fails with `butlast` on the
    empty list. -/
def butlast : List α → Except String (List α)
  | [_] => pure []
  | h :: t => do return h :: (← butlast t)
  | [] => failwith "butlast"

/-- The `n`th element of a list, counting from zero. Fails if `n` is out
    of range (via the underlying `hd`/`tl`). -/
partial def el (n : Nat) (l : List α) : Except String α :=
  if n == 0 then hd l
  else do el (n - 1) (← tl l)

/-- Reverse a list. -/
def rev (l : List α) : List α :=          -- Lean has List.reverse
  let rec rev_append (acc : List α) : List α → List α
    | [] => acc
    | h :: t => rev_append (h :: acc) t
  rev_append [] l

/-- Map a binary function over two lists elementwise. Fails with
    `map2: length mismatch` if the lists differ in length. -/
def map2 (f : α → β → γ) : List α → List β → Except String (List γ)
  | [], [] => pure []
  | h1 :: t1, h2 :: t2 => do return f h1 h2 :: (← map2 f t1 t2)
  | _, _ => failwith "map2: length mismatch"

/-- Map a function that also receives each element's index (from zero). -/
def mapi (f : Nat → α → β) (xs : List α) : List β :=
  let rec aux (i : Nat) : List α → List β
    | [] => []
    | h :: t => f i h :: aux (i + 1) t
  aux 0 xs

/- ---------------------------------------------------------------------- -/
/- Attempting function or predicate applications.                         -/
/- ---------------------------------------------------------------------- -/

/-- Test whether applying `f` to `x` succeeds rather than failing. -/
def can {ε α : Type} (f : α → Except ε β) (x : α) : Bool :=
  match f x with
  | .ok _ => true
  | .error _ => false

/-- Return `x` if `p x` holds, else fail with `check`. -/
def check (p : α → Bool) (x : α) : Except String α :=
  if p x then pure x else failwith "check"

/- ---------------------------------------------------------------------- -/
/- Repetition of a function.                                              -/
/- ---------------------------------------------------------------------- -/

/-- Apply `f` to `x` a total of `n` times: `funpow n f x = f (… (f x))`. -/
def funpow (n : Nat) (f : α → α) (x : α) : α :=
  match n with
  | 0 => x
  | n + 1 => funpow n f (f x)

/-- Monadic `funpow`: apply `f` (which may fail) `n` times. -/
def funpowM (n : Nat) (f : α → Except String α) (x : α) : Except String α :=
  match n with
  | 0 => pure x
  | n + 1 => do funpowM n f (← f x)

/-- Apply `f` repeatedly until it fails, returning the last success. -/
partial def repeat' (f : α → Except String α) (x : α) : α :=  -- Lean has repeat
  match f x with
  | .ok y => repeat' f y
  | .error _ => x

/- ---------------------------------------------------------------------- -/
/- To avoid consing in various situations, we propagate this exception.   -/
/- I should probably eliminate this and use pointer EQ tests instead.     -/
/-                                                                        -/
/- lib.ml declares `exception Unchanged` here; this port has no           -/
/- module-wide equivalent.  Each user models it locally:                  -/
/- `ImpConv.unchanged` is an `Except String` sentinel that Failure-only   -/
/- handlers must let through (`ImpConv.failureOnly`), and `Meson`'s       -/
/- `qpartition` uses `Option` (`none` = unchanged).                       -/
/- ---------------------------------------------------------------------- -/

/- ---------------------------------------------------------------------- -/
/- Various versions of list iteration.                                    -/
/- ---------------------------------------------------------------------- -/

/-- Right fold: `itlist f [x1;…;xn] b = f x1 (f x2 (… (f xn b)))`, so `f`
    is applied to the last element first. -/
def itlist (f : α → β → β) : List α → β → β
  | [], b => b
  | h :: t, b => f h (itlist f t b)

/-- Left fold: `rev_itlist f [x1;…;xn] b = f xn (… (f x2 (f x1 b)))`, so
    `f` is applied to the first element first. -/
def rev_itlist (f : α → β → β) : List α → β → β
  | [], b => b
  | h :: t, b => rev_itlist f t (f h b)

/-- Monadic right fold (effectful `itlist`); `f` is applied to the last
    element first. -/
def itlistM (f : α → β → Except String β) : List α → β → Except String β
  | [], b => pure b
  | h :: t, b => do f h (← itlistM f t b)

/-- Monadic left fold (effectful `rev_itlist`); `f` is applied to the
    first element first. -/
def rev_itlistM (f : α → β → Except String β) : List α → β → Except String β
  | [], b => pure b
  | h :: t, b => do rev_itlistM f t (← f h b)

/-- Effectful `itlist2`: monadic right fold over two equal-length lists.
    Fails with `itlist2M: length mismatch` if the lists differ. -/
def itlist2M (f : α → β → γ → Except String γ) :
    List α → List β → γ → Except String γ
  | a :: as', b :: bs', acc => do f a b (← itlist2M f as' bs' acc)
  | [], [], acc => .ok acc
  | _, _, _ => failwith "itlist2M: length mismatch"

/-- Right fold with no base case: `end_itlist f [x1;…;xn] = f x1 (…
    (f x_{n-1} xn))`. Fails with `end_itlist` on the empty list. -/
def end_itlist (f : α → α → α) : List α → Except String α
  | [] => failwith "end_itlist"
  | [x] => pure x
  | h :: t => do return f h (← end_itlist f t)

/-- Monadic `end_itlist`: the combiner may fail (returns `Except`). -/
def end_itlistM (f : α → α → Except String α) : List α → Except String α
  | [] => failwith "end_itlist"
  | [x] => pure x
  | h :: t => do f h (← end_itlistM f t)

/-- Right fold over two equal-length lists; `f` is applied to the last
    pair first. Fails with `itlist2` if the lists differ in length. -/
def itlist2 (f : α → β → γ → γ) : List α → List β → γ → Except String γ
  | [], [], b => pure b
  | h1 :: t1, h2 :: t2, b => do return f h1 h2 (← itlist2 f t1 t2 b)
  | _, _, _ => failwith "itlist2"

/-- Left fold over two equal-length lists; `f` is applied to the first
    pair first. Fails with `rev_itlist2` if the lists differ in length. -/
def rev_itlist2 (f : α → β → γ → γ) : List α → List β → γ → Except String γ
  | [], [], b => pure b
  | h1 :: t1, h2 :: t2, b => rev_itlist2 f t1 t2 (f h1 h2 b)
  | _, _, _ => failwith "rev_itlist2"

/-- Monadic `rev_itlist2`: the combiner `f` is `Except`-valued. -/
def rev_itlist2M (f : α → β → γ → Except String γ) :
    List α → List β → γ → Except String γ
  | [], [], b => pure b
  | h1 :: t1, h2 :: t2, b => do rev_itlist2M f t1 t2 (← f h1 h2 b)
  | _, _, _ => failwith "rev_itlist2"

/- ---------------------------------------------------------------------- -/
/- Iterative splitting (list) and stripping (tree) via destructor.        -/
/- ---------------------------------------------------------------------- -/

/-- Repeatedly apply the destructor `dest` from the left, collecting the
    left components, until it fails; return the list and the remainder. -/
partial def splitlist (dest : γ → Except String (α × γ)) (x : γ) : List α × γ :=
  match dest x with
  | .ok (l, r) =>
    let (ls, res) := splitlist dest r
    (l :: ls, res)
  | .error _ => ([], x)

/-- Like `splitlist` but recurses on the left component, so the result
    list is accumulated in reverse order (returns remainder then list). -/
partial def rev_splitlist (dest : γ → Except String (γ × α)) (x : γ) : γ × List α :=
  let rec rsplist (ls : List α) (x : γ) : γ × List α :=
    match dest x with
    | .ok (l, r) => rsplist (r :: ls) l
    | .error _ => (x, ls)
  rsplist [] x

/-- Recursively strip a binary tree via `dest`, returning the fringe of
    leaves left to right. -/
partial def striplist (dest : α → Except String (α × α)) (x : α) : List α :=
  let rec strip (x : α) (acc : List α) : List α :=
    match dest x with
    | .ok (l, r) => strip l (strip r acc)
    | .error _ => x :: acc
  strip x []

/- ---------------------------------------------------------------------- -/
/- Apply a destructor as many times as elements in list.                  -/
/- ---------------------------------------------------------------------- -/

/-- Apply the destructor `dest` as many times as there are elements in
    the guiding list, returning the collected left components and the
    final remainder. -/
def nsplit (dest : γ → Except String (α × γ)) : List β → γ → Except String (List α × γ)
  | [], x => pure ([], x)
  | _ :: cs, x => do
      let (l, r) ← dest x
      let (ll, y) ← nsplit dest cs r
      return (l :: ll, y)

/- ---------------------------------------------------------------------- -/
/- Replication and sequences.                                             -/
/- ---------------------------------------------------------------------- -/

/-- The list consisting of `n` copies of `x`. -/
def replicate (x : α) (n : Nat) : List α :=
  match n with
  | 0 => []
  | n + 1 => x :: replicate x n

/-- The list of integers from `m` up to `n` inclusive (`m -- n`); empty
    if `m > n`. -/
partial def upto (m n : Int) : List Int :=
  if m > n then [] else m :: upto (m + 1) n
infix:65 " -- " => upto

/- ---------------------------------------------------------------------- -/
/- Various useful list operations.                                        -/
/- ---------------------------------------------------------------------- -/

/-- Does the predicate `p` hold of every element of the list? -/
def forall' (p : α → Bool) : List α → Bool    -- Lean has forall
  | [] => true
  | h :: t => p h && forall' p t

/-- Does `p` hold of every corresponding pair? `false` if the lists
    differ in length. -/
def forall2 (p : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | h1 :: t1, h2 :: t2 => p h1 h2 && forall2 p t1 t2
  | _, _ => false

/-- Does the predicate `p` hold of some element of the list? -/
def exists' (p : α → Bool) : List α → Bool    -- Lean has exists
  | [] => false
  | h :: t => p h || exists' p t

/-- The number of elements in a list. -/
def length (l : List α) : Nat :=
  let rec len (k : Nat) : List α → Nat
    | [] => k
    | _ :: t => len (k + 1) t
  len 0 l

/-- The sublist of elements satisfying the predicate `p`. -/
def filter (p : α → Bool) : List α → List α
  | [] => []
  | h :: t => let t' := filter p t; if p h then h :: t' else t'

/-- Split a list into those elements satisfying `p` and those not. -/
def partition (p : α → Bool) : List α → List α × List α
  | [] => ([], [])
  | h :: t =>
    let (yes, no) := partition p t
    if p h then (h :: yes, no) else (yes, h :: no)

/-- Map `f` over the list, dropping elements on which `f` fails. -/
def mapfilter (f : α → Except String β) : List α → List β
  | [] => []
  | h :: t =>
    let rest := mapfilter f t
    match f h with
    | .ok y => y :: rest
    | .error _ => rest

/-- The first element satisfying `p`. Fails with `find` if there is
    none. -/
def find (p : α → Bool) : List α → Except String α
  | [] => failwith "find"
  | h :: t => if p h then pure h else find p t

/-- The first successful result of `f` over the list. Fails with
    `tryfind` if `f` fails on every element. -/
def tryfind (f : α → Except String β) : List α → Except String β
  | [] => failwith "tryfind"
  | h :: t =>
    match f h with
    | .ok y => pure y
    | .error _ => tryfind f t

/-- Monadic/IO `tryfind`: try `f` on each element, returning the first
    `.ok` result (in `IO (Except …)`), else a "tryfind" error. -/
def tryfindM {α β : Type} (f : α → IO (Except String β)) :
    List α → IO (Except String β)
  | [] => return .error "tryfind"
  | h :: t => do
      match ← f h with
      | .ok y => return .ok y
      | .error _ => tryfindM f t

/-- Concatenate a list of lists into a single list. -/
def flat (l : List (List α)) : List α := itlist (· ++ ·) l []

/-- Remove the first element satisfying `p`, returning it together with
    the remaining list. Fails with `remove` if none matches. -/
def remove (p : α → Bool) : List α → Except String (α × List α)
  | [] => failwith "remove"
  | h :: t =>
    if p h then pure (h, t)
    else do
      let (y, n) ← remove p t
      return (y, h :: n)

/-- Split off the first `n` elements: returns `(take n l, drop n l)`.
    Fails with `chop_list` if the list has fewer than `n` elements. -/
def chop_list (n : Nat) (l : List α) : Except String (List α × List α) :=
  match n with
  | 0 => pure ([], l)
  | n + 1 =>
    -- OCaml wraps the body in `try ... with Failure _ -> failwith "chop_list"`,
    -- normalising every underlying `hd`/`tl` failure to "chop_list" (callers
    -- such as `shareout` match on that exact string).  Destructuring `l` here
    -- gives the same behaviour directly: an exhausted list reports
    -- "chop_list", and a deeper exhaustion propagates the same message.
    match l with
    | [] => failwith "chop_list"
    | h :: t => do
      let (m, l') ← chop_list n t
      return (h :: m, l')

/-- The zero-based position of the first element satisfying `p`, or
    `none` if there is none. -/
def find_index (p : α → Bool) (l : List α) : Option Nat :=
  let rec ind (n : Nat) : List α → Option Nat
    | [] => none
    | h :: t => if p h then some n else ind (n + 1) t
  ind 0 l

/-- The zero-based position of the first occurrence of `x` in the list.
    Fails with `index` if `x` does not occur. -/
def index [Ord α] (x : α) (l : List α) : Except String Nat :=
  match find_index (fun y => compare x y == .eq) l with
  | some n => pure n
  | none => failwith "index"

/- ---------------------------------------------------------------------- -/
/- "Set" operations on lists.                                             -/
/- ---------------------------------------------------------------------- -/

/-- Is `x` a member of the list? -/
def mem [BEq α] (x : α) : List α → Bool
  | [] => false
  | h :: t => x == h || mem x t

/-- Add `x` to the list unless it is already present. -/
def insert [BEq α] (x : α) (l : List α) : List α :=
  if mem x l then l else x :: l

/-- Union of two lists regarded as sets. -/
def union [BEq α] (l1 l2 : List α) : List α := itlist insert l1 l2

/-- Union of a list of lists regarded as sets. -/
def unions [BEq α] (l : List (List α)) : List α := itlist union l []

/-- Intersection of two lists regarded as sets. -/
def intersect [BEq α] (l1 l2 : List α) : List α := filter (fun x => mem x l2) l1

/-- The elements of `l1` that are not members of `l2`. -/
def subtract [BEq α] (l1 l2 : List α) : List α := filter (fun x => !(mem x l2)) l1

/-- Is every element of `l1` a member of `l2`? -/
def subset [BEq α] (l1 l2 : List α) : Bool := forall' (fun t => mem t l2) l1

/-- Do the two lists denote the same set (mutual subset)? -/
def set_eq [BEq α] (l1 l2 : List α) : Bool := subset l1 l2 && subset l2 l1

/- ---------------------------------------------------------------------- -/
/- Association lists.                                                     -/
/- ---------------------------------------------------------------------- -/

/-- Look up the value paired with the key `a` in an association list.
    Fails with `find` if `a` is not present. -/
def assoc [BEq α] (a : α) : List (α × β) → Except String β
  | (x, y) :: t => if x == a then pure y else assoc a t
  | [] => failwith "find"

/-- Look up the key paired with the value `a` in an association list.
    Fails with `find` if `a` is not present. -/
def rev_assoc [BEq β] (a : β) : List (α × β) → Except String α
  | (x, y) :: t => if y == a then pure x else rev_assoc a t
  | [] => failwith "find"

/- ---------------------------------------------------------------------- -/
/- Zipping, unzipping etc.                                                -/
/- ---------------------------------------------------------------------- -/

/-- Combine two equal-length lists into a list of pairs. Fails with
    `zip` if the lists differ in length. -/
def zip : List α → List β → Except String (List (α × β))
  | [], [] => pure []
  | h1 :: t1, h2 :: t2 => do return (h1, h2) :: (← zip t1 t2)
  | _, _ => failwith "zip"

/-- Split a list of pairs into a pair of lists. -/
def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (a, b) :: rest => let (alist, blist) := unzip rest; (a :: alist, b :: blist)

/- ---------------------------------------------------------------------- -/
/- Sharing out a list according to pattern in list-of-lists.              -/
/- ---------------------------------------------------------------------- -/

/-- Share out the elements of `all` into sublists whose lengths match
    the pattern given by the lengths of the lists in `pat`. -/
def shareout (pat : List (List β)) (all : List α) : Except String (List (List α)) :=
  match pat with
  | [] => pure []
  | p :: ps => do
    let (l, r) ← chop_list (length p) all
    return l :: (← shareout ps r)

/- ---------------------------------------------------------------------- -/
/- Iterating functions over lists.                                        -/
/- ---------------------------------------------------------------------- -/

/-- Apply the side-effecting `f` to each element of the list in turn. -/
def do_list (f : α → IO Unit) : List α → IO Unit
  | [] => pure ()
  | h :: t => do f h; do_list f t

/- ---------------------------------------------------------------------- -/
/- Sorting.                                                               -/
/- ---------------------------------------------------------------------- -/

/-- Quicksort a list by the ordering relation `cmp` (`cmp x y` true when
    `x` should come before `y`). -/
partial def sort (cmp : α → α → Bool) : List α → List α
  | [] => []
  | piv :: rest =>
    let (r, l) := partition (cmp piv) rest
    sort cmp l ++ (piv :: sort cmp r)

/- ---------------------------------------------------------------------- -/
/- Removing adjacent (NB!) equal elements from list.                      -/
/- ---------------------------------------------------------------------- -/

/-- Remove adjacent (NB!) equal elements from a list. -/
def uniq [BEq α] : List α → List α
  | x :: y :: t =>
    let t' := uniq (y :: t)
    if x == y then t' else x :: t'
  | l => l

/- ---------------------------------------------------------------------- -/
/- Convert list into set by eliminating duplicates.                       -/
/- ---------------------------------------------------------------------- -/

/-- Convert a list into a set by sorting and eliminating duplicates. -/
def setify [BEq α] [Ord α] (s : List α) : List α :=
  uniq (sort (fun x y => (compare x y).isLE) s)

/- ---------------------------------------------------------------------- -/
/- String operations (surely there is a better way...)                   -/
/- ---------------------------------------------------------------------- -/

/-- Concatenate a list of strings into a single string. -/
def implode (l : List String) : String := itlist (· ++ ·) l ""
/-- Break a string into the list of its one-character substrings. -/
def explode (s : String) : List String :=
  s.toList.map (fun c => String.ofList [c])       -- Use Lean function

/- ---------------------------------------------------------------------- -/
/- Greatest common divisor.                                               -/
/- ---------------------------------------------------------------------- -/

/-- Greatest common divisor of two integers (via their absolute
    values). -/
partial def gcd (x y : Int) : Int :=
  let rec gxd (x y : Int) : Int :=
    if y == 0 then x else gxd y (x % y)
  let (x', y') := ((x.natAbs : Int), (y.natAbs : Int))
  if x' < y' then gxd y' x' else gxd x' y'

/- ---------------------------------------------------------------------- -/
/- Some useful functions on "num" type (modelled by `Rat`).               -/
/- ---------------------------------------------------------------------- -/

/-- The rational number 0. -/
def num_0 : Rat := 0
/-- The rational number 1. -/
def num_1 : Rat := 1
/-- The rational number 2. -/
def num_2 : Rat := 2
/-- The rational number 10. -/
def num_10 : Rat := 10
/-- The rational number 16. -/
def num_16 : Rat := 16

/-- `power_num x (num n)` for an int `n`: negative powers are reciprocals. -/
private def powInt (x : Rat) (n : Int) : Rat :=
  if n ≥ 0 then x ^ n.toNat else 1 / x ^ n.natAbs
/-- `pow` (bignum_zarith.ml 96-111): `x` to an integer power; negative
    powers are reciprocals, and `pow x 0 = 1` (also for `x = 0`). -/
def pow (x : Rat) (n : Int) : Rat := powInt x n
/-- `pow2 n = power_num num_2 (num n)` (lib.ml 400); `n` may be negative. -/
def pow2 (n : Int) : Rat := powInt num_2 n
/-- `pow10 n = power_num num_10 (num n)` (lib.ml 401); `n` may be negative. -/
def pow10 (n : Int) : Rat := powInt num_10 n

/-- `numdom` (bignum_zarith.ml 158): the numerator and denominator of a
    rational in lowest terms. -/
def numdom (x : Rat) : Rat × Rat := (x.num, x.den)

/-- The numerator of a rational (in lowest terms). -/
def numerator (x : Rat) : Int := x.num
/-- The denominator of a rational (in lowest terms). -/
def denominator (x : Rat) : Int := Int.ofNat x.den

/-- Absolute value of a rational. -/
def abs_num (x : Rat) : Rat := if x < 0 then -x else x
/-- Truncation towards zero, matching the `Q.to_bigint` that OCaml's `NumExt`
    applies before taking a GCD or an integer quotient. -/
def truncate_num (x : Rat) : Int := Int.tdiv x.num (Int.ofNat x.den)

/-- `power_num base exponent` (bignum_zarith.ml 114): `pow base (int_of_num
    exponent)`. -/
def power_num (base exponent : Rat) : Rat := powInt base (truncate_num exponent)

/-- `gcd_num` (defined in OCaml's `NumExt` module as
    `Z.gcd (Q.to_bigint x) (Q.to_bigint y)`, i.e. on the truncated values). -/
def gcd_num (x y : Rat) : Rat := Rat.ofInt (gcd (truncate_num x) (truncate_num y))

/-- Exact rational division (OCaml's `//`, i.e. `div_num`). -/
def divide_num (x y : Rat) : Rat := x / y

/- gcd_num x y is defined in the NumExt module. -/
/-- Least common multiple of two rationals (`0` when both are `0`). -/
def lcm_num (x y : Rat) : Rat :=
  if x == num_0 && y == num_0 then num_0
  else abs_num (divide_num (x * y) (gcd_num x y))

/-- Integer quotient, Euclidean (OCaml `quo_num`: `Z.ediv` in
    bignum_zarith.ml, Euclidean in the Num library too). -/
def quo_num (x y : Rat) : Rat :=
  Rat.ofInt (Int.ediv (truncate_num x) (truncate_num y))

/-- Integer remainder, Euclidean, so never negative (OCaml `mod_num`:
    `Z.erem` in bignum_zarith.ml). -/
def mod_num (x y : Rat) : Rat :=
  Rat.ofInt (Int.emod (truncate_num x) (truncate_num y))

/-- Decimal string representation of a rational's numerator. -/
def string_of_num (n : Rat) : String := toString n.num

/-- String representation of `n` in base `b` (2–16), least-significant
    digit computed via `mod_num`/`quo_num`. -/
partial def string_of_num_nary (b : Int) (n : Rat) : Except String String :=
  let digits := ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9",
                  "a", "b", "c", "d", "e", "f"]
  let base : Rat := Rat.ofInt b
  let rec sonum (n : Rat) : Except String String := do
    let n0 := mod_num n base
    let n1 := quo_num n base
    let d0 ← el n0.num.toNat digits
    if n1 == num_0 then pure d0
    else pure ((← sonum n1) ++ d0)
  sonum n

/-- Hexadecimal string representation of `n`, prefixed with `0x`. -/
def string_of_num_hex (n : Rat) : Except String String := do
  return "0x" ++ (← string_of_num_nary 16 n)

/- ---------------------------------------------------------------------- -/
/- All pairs arising from applying a function over two lists.             -/
/- ---------------------------------------------------------------------- -/

/-- All values `f x y` for `x` in `l1` and `y` in `l2`. -/
def allpairs (f : α → β → γ) : List α → List β → List γ
  | [], _ => []
  | h1 :: t1, l2 => itlist (fun x a => f h1 x :: a) l2 (allpairs f t1 l2)

/- ---------------------------------------------------------------------- -/
/- Issue a report with a newline.                                         -/
/- ---------------------------------------------------------------------- -/

/-- Issue a report string followed by a newline. -/
def report (s : String) : IO Unit :=
  IO.println s

/- ---------------------------------------------------------------------- -/
/- Convenient function for issuing a warning.                             -/
/- ---------------------------------------------------------------------- -/

/-- If `cond` holds, report `s` prefixed with `Warning: `. -/
def warn (cond : Bool) (s : String) : IO Unit :=
  if cond then report ("Warning: " ++ s) else pure ()

/- ---------------------------------------------------------------------- -/
/- Flags to switch on verbose mode.                                       -/
/- ---------------------------------------------------------------------- -/

/-- Flag to switch on verbose mode. -/
initialize verbose : IO.Ref Bool ← IO.mkRef true
/-- Flag to switch on timing reports. -/
initialize report_timing : IO.Ref Bool ← IO.mkRef true

/- ---------------------------------------------------------------------- -/
/- Switchable version of "report".                                        -/
/- ---------------------------------------------------------------------- -/

/-- Switchable version of `report`: only reports when `verbose` is set. -/
def remark (s : String) : IO Unit := do
  if ← verbose.get then report s else pure ()

/- ---------------------------------------------------------------------- -/
/- Time a function.                                                       -/
/- ---------------------------------------------------------------------- -/

/-- Time the application of `f` to `x`, reporting CPU time when
    `report_timing` is set (and on failure too). -/
def time (f : α → IO β) (x : α) : IO β := do
  if !(← report_timing.get) then f x
  else
    let startTime ← IO.monoNanosNow
    try
      let result ← f x
      let finishTime ← IO.monoNanosNow
      report s!"CPU time (user): {finishTime - startTime}ns"
      return result
    catch e =>
      let finishTime ← IO.monoNanosNow
      report s!"Failed after (user) CPU time of {finishTime - startTime}ns: {e.toString}"
      throw e

/- ---------------------------------------------------------------------- -/
/- Versions of assoc and rev_assoc with default rather than failure.      -/
/- ---------------------------------------------------------------------- -/

/-- Version of `assoc` returning the default `d` instead of failing. -/
def assocd [BEq α] (a : α) : List (α × β) → β → β
  | [], d => d
  | (x, y) :: t, d => if x == a then y else assocd a t d

/-- Version of `rev_assoc` returning the default `d` instead of
    failing. -/
def rev_assocd [BEq β] (a : β) : List (α × β) → α → α
  | [], d => d
  | (x, y) :: t, d => if y == a then x else rev_assocd a t d

/- ---------------------------------------------------------------------- -/
/- Version of map that avoids rebuilding unchanged subterms.              -/
/- ---------------------------------------------------------------------- -/

/-- Version of `map` that avoids rebuilding unchanged subterms. -/
def qmap [BEq α] (f : α → α) : List α → List α
  | h :: t =>
      let h' := f h
      let t' := qmap f t
      if h' == h && t' == t then h :: t else h' :: t'
  | l => l

/- ---------------------------------------------------------------------- -/
/- Merging and bottom-up mergesort.                                       -/
/- ---------------------------------------------------------------------- -/

/-- Merge two lists already sorted by `ord` into one sorted list. -/
def merge (ord : α → α → Bool) : List α → List α → List α
  | [], l2 => l2
  | l1, [] => l1
  | h1 :: t1, h2 :: t2 =>
    if ord h1 h2 then h1 :: merge ord t1 (h2 :: t2)
    else h2 :: merge ord (h1 :: t1) t2
  termination_by l1 l2 => l1.length + l2.length

/-- Bottom-up mergesort of a list by the ordering relation `ord`. -/
partial def mergesort (ord : α → α → Bool) (l : List α) : List α :=
  let rec mergepairs : List (List α) → List (List α) → List α
    | [s], [] => s
    | l, [] => mergepairs [] l
    | l, [s1] => mergepairs (s1 :: l) []
    | l, s1 :: s2 :: ss => mergepairs (merge ord s1 s2 :: l) ss
  if l.isEmpty then [] else mergepairs [] (map' (fun x => [x]) l)

/- ---------------------------------------------------------------------- -/
/- Common measure predicates to use with "sort".                          -/
/- ---------------------------------------------------------------------- -/

/-- Order by increasing measure `f` (for use with `sort`). -/
def increasing [Ord β] (f : α → β) (x y : α) : Bool := compare (f x) (f y) == .lt
/-- Order by decreasing measure `f` (for use with `sort`). -/
def decreasing [Ord β] (f : α → β) (x y : α) : Bool := compare (f x) (f y) == .gt

/- ---------------------------------------------------------------------- -/
/- Polymorphic finite partial functions via Patricia trees.               -/
/- ---------------------------------------------------------------------- -/

/- The point of this strange representation is that it is canonical (equal  -/
/- functions have the same encoding) yet reasonably efficient on average.   -/
/- Idea due to Diego Olivier Fernandez Pons (OCaml list, 2003/11/10).       -/

/-- Polymorphic finite partial function represented as a Patricia tree. -/
inductive Func (α : Type) (β : Type) where
  | Empty
  | Leaf   (h : Nat) (l : List (α × β))
  | Branch (p : Nat) (b : Nat) (l : Func α β) (r : Func α β)
  /- deriving Repr, Inhabited -/

/-- The everywhere-undefined function. -/
def undefined : Func α β := .Empty

/- ---------------------------------------------------------------------- -/
/- In case of equality comparison worries, better use this.               -/
/- ---------------------------------------------------------------------- -/

/-- Is the function completely undefined? -/
def is_undefined : Func α β → Bool
  | .Empty => true
  | _ => false

/- ---------------------------------------------------------------------- -/
/- Operation analagous to "map" for lists.                                -/
/- ---------------------------------------------------------------------- -/

/-- Map `f` over the range of a finite partial function. -/
def mapf (f : β → γ) : Func α β → Func α γ
  | .Empty => .Empty
  | .Leaf h l => .Leaf h (l.map (fun (x, y) => (x, f y)))
  | .Branch p b l r => .Branch p b (mapf f l) (mapf f r)

/- ---------------------------------------------------------------------- -/
/- Operations analogous to "fold" for lists.                              -/
/- ---------------------------------------------------------------------- -/

/-- Left fold over the argument/value pairs of a finite partial
    function. -/
def foldl (f : δ → α → β → δ) (a : δ) : Func α β → δ
  | .Empty => a
  | .Leaf _ l => l.foldl (fun acc (x, y) => f acc x y) a
  | .Branch _ _ l r => foldl f (foldl f a l) r

/-- Right fold over the argument/value pairs of a finite partial
    function. -/
def foldr (f : α → β → δ → δ) : Func α β → δ → δ
  | .Empty, a => a
  | .Leaf _ l, a => l.foldr (fun (x, y) acc => f x y acc) a
  | .Branch _ _ l r, a => foldr f l (foldr f r a)

/- ---------------------------------------------------------------------- -/
/- Mapping to sorted-list representation of the graph, domain and range.   -/
/- ---------------------------------------------------------------------- -/

/-- Sorted-list representation of the graph (argument/value pairs). -/
def graph [Ord (α × β)] [BEq (α × β)] (f : Func α β) : List (α × β) :=
  setify (foldl (fun a x y => (x, y) :: a) [] f)
/-- Sorted list of the arguments on which `f` is defined. -/
def dom [Ord α] [BEq α] (f : Func α β) : List α :=
  setify (foldl (fun a x _ => x :: a) [] f)
/-- Sorted list of the values in the range of `f`. -/
def ran [Ord β] [BEq β] (f : Func α β) : List β :=
  setify (foldl (fun a _ y => y :: a) [] f)

private def apply_listd [Ord α] (d : α → Except String β) :
    List (α × β) → α → Except String β
  | (a, b) :: t, x =>
    match compare x a with
    | .eq => pure b
    | .gt => apply_listd d t x
    | .lt => d x
  | [], x => d x

/-- Apply the finite partial function `f` to `x`, falling back to the
    default function `d` where `f` is undefined. -/
partial def applyd [Hashable α] [Ord α] (f : Func α β) (d : α → Except String β) (x : α) :
    Except String β :=
  let k := (hash x).toNat
  let rec look : Func α β → Except String β
    | .Leaf h l => if h == k then apply_listd d l x else d x
    | .Branch p b l r =>
        if (k ^^^ p) &&& (b - 1) == 0 then look (if k &&& b == 0 then l else r)
        else d x
    | _ => d x
  look f

/-- Apply the finite partial function `f` to `x`, failing with `apply`
    where `f` is undefined. -/
def apply [Hashable α] [Ord α] (f : Func α β) (x : α) : Except String β :=
  applyd f (fun _ => failwith "apply") x

/-- Apply `f` to `a`, returning the default `d` where `f` is undefined. -/
def tryapplyd [Hashable α] [Ord α] (f : Func α β) (a : α) (d : β) : β :=
  match applyd f (fun _ => pure d) a with
  | .ok b    => b
  | .error _ => d

/-- Is the finite partial function `f` defined at `x`? -/
def defined [Hashable α] [Ord α] (f : Func α β) (x : α) : Bool :=
  match apply f x with
  | .ok _    => true
  | .error _ => false

private def undefine_list [Ord α] (x : α) : List (α × β) → List (α × β)
  | (a, b) :: t =>
    match compare x a with
    | .eq => t
    | .lt => (a, b) :: t
    | .gt => (a, b) :: undefine_list x t
  | [] => []

/-- Remove `x` from the domain of the finite partial function `f`. -/
def undefine [Hashable α] [Ord α] (x : α) (f : Func α β) : Func α β :=
  let k := (hash x).toNat
  let rec und : Func α β → Func α β
    | .Leaf h l =>
        if h == k then (match undefine_list x l with | [] => .Empty | l' => .Leaf h l')
        else .Leaf h l
    | .Branch p b l r =>
        if k &&& (b - 1) == p then
          if k &&& b == 0 then (match und l with | .Empty => r | l' => .Branch p b l' r)
          else (match und r with | .Empty => l | r' => .Branch p b l r')
        else .Branch p b l r
    | t => t
  und f

private def newbranch (p1 : Nat) (t1 : Func α β) (p2 : Nat) (t2 : Func α β) : Func α β :=
  let zp := p1 ^^^ p2
  -- OCaml `zp land (-zp)` isolates the lowest set bit; on Nat use
  -- `zp - (zp land (zp - 1))`.
  let b := zp - (zp &&& (zp - 1))
  let p := p1 &&& (b - 1)
  if p1 &&& b == 0 then .Branch p b t1 t2 else .Branch p b t2 t1

private def define_list [Ord α] (x : α) (y : β) : List (α × β) → List (α × β)
  | (a, b) :: t =>
    match compare x a with
    | .eq => (x, y) :: t
    | .lt => (x, y) :: (a, b) :: t
    | .gt => (a, b) :: define_list x y t
  | [] => [(x, y)]

/-- Extend or redefine the finite partial function `f` so that `x` maps
    to `y` (HOL Light's `x |-> y`). -/
def update [Hashable α] [Ord α] (x : α) (y : β) (f : Func α β) : Func α β :=
  let k := (hash x).toNat
  let rec upd : Func α β → Func α β
    | .Empty => .Leaf k [(x, y)]
    | .Leaf h l =>
        if h == k then .Leaf h (define_list x y l)
        else newbranch h (.Leaf h l) k (.Leaf k [(x, y)])
    | .Branch p b l r =>
        if k &&& (b - 1) != p then newbranch p (.Branch p b l r) k (.Leaf k [(x, y)])
        else if k &&& b == 0 then .Branch p b (upd l) r
        else .Branch p b l (upd r)
  upd f
notation:90 x " |-> " y => fun f => HolCore.Lib.update x y f

/- ---------------------------------------------------------------------- -/
/- Redefinition and combination.                                          -/
/- ---------------------------------------------------------------------- -/

private def combine_list [Ord α] (op : β → β → β) (z : β → Bool) :
    List (α × β) → List (α × β) → List (α × β)
  | [], l2 => l2
  | l1, [] => l1
  | (x1, y1) :: t1, (x2, y2) :: t2 =>
    match compare x1 x2 with
    | .lt => (x1, y1) :: combine_list op z t1 ((x2, y2) :: t2)
    | .gt => (x2, y2) :: combine_list op z ((x1, y1) :: t1) t2
    | .eq =>
        let y := op y1 y2
        let l := combine_list op z t1 t2
        if z y then l else (x1, y) :: l
  termination_by l1 l2 => l1.length + l2.length

/-- Combine two finite partial functions with `op` on values defined in
    both, dropping any result value for which `z` holds. -/
partial def combine [Ord α] (op : β → β → β) (z : β → Bool) :
    Func α β → Func α β → Func α β
  | .Empty, t2 => t2
  | t1, .Empty => t1
  | .Leaf h1 l1, .Leaf h2 l2 =>
      if h1 == h2 then
        match combine_list op z l1 l2 with
        | [] => .Empty
        | l  => .Leaf h1 l
      else newbranch h1 (.Leaf h1 l1) h2 (.Leaf h2 l2)
  | .Leaf k lis, .Branch p b l r =>
      if k &&& (b - 1) == p then
        if k &&& b == 0 then
          (match combine op z (.Leaf k lis) l with | .Empty => r | l' => .Branch p b l' r)
        else
          (match combine op z (.Leaf k lis) r with | .Empty => l | r' => .Branch p b l r')
      else newbranch k (.Leaf k lis) p (.Branch p b l r)
  | .Branch p b l r, .Leaf k lis =>
      if k &&& (b - 1) == p then
        if k &&& b == 0 then
          (match combine op z l (.Leaf k lis) with | .Empty => r | l' => .Branch p b l' r)
        else
          (match combine op z r (.Leaf k lis) with | .Empty => l | r' => .Branch p b l r')
      else newbranch p (.Branch p b l r) k (.Leaf k lis)
  | .Branch p1 bb1 l1 r1, .Branch p2 bb2 l2 r2 =>
      if bb1 < bb2 then
        if p2 &&& (bb1 - 1) != p1 then
          newbranch p1 (.Branch p1 bb1 l1 r1) p2 (.Branch p2 bb2 l2 r2)
        else if p2 &&& bb1 == 0 then
          (match combine op z l1 (.Branch p2 bb2 l2 r2) with
            | .Empty => r1 | l => .Branch p1 bb1 l r1)
        else
          (match combine op z r1 (.Branch p2 bb2 l2 r2) with
            | .Empty => l1 | r => .Branch p1 bb1 l1 r)
      else if bb2 < bb1 then
        if p1 &&& (bb2 - 1) != p2 then
          newbranch p1 (.Branch p1 bb1 l1 r1) p2 (.Branch p2 bb2 l2 r2)
        else if p1 &&& bb2 == 0 then
          (match combine op z (.Branch p1 bb1 l1 r1) l2 with
            | .Empty => r2 | l => .Branch p2 bb2 l r2)
        else
          (match combine op z (.Branch p1 bb1 l1 r1) r2 with
            | .Empty => l2 | r => .Branch p2 bb2 l2 r)
      else if p1 == p2 then
        (match combine op z l1 l2, combine op z r1 r2 with
          | .Empty, r => r
          | l, .Empty => l
          | l, r => .Branch p1 bb1 l r)
      else
        newbranch p1 (.Branch p1 bb1 l1 r1) p2 (.Branch p2 bb2 l2 r2)

/- ---------------------------------------------------------------------- -/
/- Special case of point function.                                        -/
/- ---------------------------------------------------------------------- -/

/-- The one-point function mapping `x` to `y` (HOL Light's `x |=> y`). -/
def pointFun [Hashable α] [Ord α] (x : α) (y : β) : Func α β := update x y undefined
notation:90 x " |=> " y => HolCore.Lib.pointFun x y

/- ---------------------------------------------------------------------- -/
/- Grab an arbitrary element.                                             -/
/- ---------------------------------------------------------------------- -/

/-- Grab an arbitrary argument/value pair from a finite partial
    function. Fails if it is completely undefined. -/
def choose : Func α β → Except String (α × β)
  | .Empty => failwith "choose: completely undefined function"
  | .Leaf _ l => hd l
  | .Branch _ _ t1 _ => choose t1

/- ---------------------------------------------------------------------- -/
/- Install a trivial printer for the general polymorphic case.            -/
/- ---------------------------------------------------------------------- -/

/-- Trivial printer for the general polymorphic finite partial function,
    always yielding `<func>`. -/
def string_of_fpf (_f : Func α β) : String := "<func>"

/- ---------------------------------------------------------------------- -/
/- Set operations parametrized by equality (from Steven Obua).            -/
/- ---------------------------------------------------------------------- -/

/-- Membership test using the explicit equality `eq`. -/
def mem' (eq : α → α → Bool) (x : α) : List α → Bool
  | [] => false
  | h :: t => eq x h || mem' eq x t
/-- Insert `x` (under equality `eq`) unless already present. -/
def insert' (eq : α → α → Bool) (x : α) (l : List α) : List α :=
  if mem' eq x l then l else x :: l
/-- Union of two lists as sets under equality `eq`. -/
def union' (eq : α → α → Bool) (l1 l2 : List α) : List α := itlist (insert' eq) l1 l2
/-- Union of a list of lists as sets under equality `eq`. -/
def unions' (eq : α → α → Bool) (l : List (List α)) : List α := itlist (union' eq) l []
/-- Elements of `l1` not in `l2`, under equality `eq`. -/
def subtract' (eq : α → α → Bool) (l1 l2 : List α) : List α :=
  filter (fun x => !(mem' eq x l2)) l1

/- ---------------------------------------------------------------------- -/
/- Accepts decimal, hex or binary numeral, using C notation 0x... for hex -/
/- and analogous 0b... for binary.                                        -/
/- ---------------------------------------------------------------------- -/

/- Digit → value (0–15), via the `values` assoc list. -/
private def digitValue (s : String) : Except String Nat :=
  assoc s [("0",0),("1",1),("2",2),("3",3),("4",4),("5",5),("6",6),("7",7),
            ("8",8),("9",9),("a",10),("A",10),("b",11),("B",11),("c",12),("C",12),
            ("d",13),("D",13),("e",14),("E",14),("f",15),("F",15)]

/- Value of digit `s` in base `b`, failing if invalid or ≥ base. -/
private def valof (b : Rat) (s : String) : Except String Rat := do
  let v : Rat := Rat.ofInt (Int.ofNat (← digitValue s))
  if v < b then pure v
  else failwith "num_of_string: invalid digit for base"

/- Fold digit-strings (least-significant first) in base `b`. -/
private def num_of_stringlist (b : Rat) : List String → Except String Rat
  | []     => failwith "num_of_string: no digits after base indicator"
  | [h]    => valof b h
  | h :: t => do return (← valof b h) + b * (← num_of_stringlist b t)

/- Parse a decimal, `0x…` hex, or `0b…` binary numeral to a `Rat`. -/
/-- Parse a decimal, `0x…` hex, or `0b…` binary numeral into a `Rat`,
    using C notation for the base prefixes. -/
def num_of_string (s : String) : Except String Rat :=
  match explode s with
  | []                      => failwith "num_of_string: no digits"
  | "0" :: "x" :: hexdigits => num_of_stringlist num_16 (rev hexdigits)
  | "0" :: "b" :: bindigits => num_of_stringlist num_2  (rev bindigits)
  | decdigits               => num_of_stringlist num_10 (rev decdigits)

/- ---------------------------------------------------------------------- -/
/- Convenient conversion between files and (lists of) strings.            -/
/- ---------------------------------------------------------------------- -/

/-- Read a file as the list of its lines. Fails if the file cannot be
    opened (`strings_of_file: can't open …`). -/
def strings_of_file (filename : String) : IO (List String) := do
  let contents ← try IO.FS.readFile filename
    catch _ => throw (IO.userError s!"strings_of_file: can't open {filename}")
  let lines := contents.splitOn "\n"
  return if lines.getLast? == some "" then lines.dropLast else lines

/-- Read the entire contents of a file as a single string. -/
def string_of_file (filename : String) : IO String :=
  IO.FS.readFile filename

/-- Write the string `s` to the file `filename`. -/
def file_of_string (filename : String) (s : String) : IO Unit :=
  IO.FS.writeFile filename s

end HolCore.Lib
