/- File: Metis.lean
Metis first-order theorem proving derived rule/tactic for HOL Light (`metis.ml`).

The original Metis was written by Joe Hurd (see http://www.gilith.com/research/metis/);
this is a port from SML to OCaml and proof-reconstructing integration with HOL Light,
written by Michael Faerber and Cezary Kaliszyk.

  (c) Copyright, Joe Hurd, 2001
  (c) Copyright, Joe Leslie-Hurd, 2004
  (c) Copyright, Michael Faerber and Cezary Kaliszyk, 2014-2018.
Distributed under the same license as HOL Light.

Lean4 translation by Chris Walton 2026.

Structure mirrors `metis.ml`: a self-contained pure first-order prover
(`Metis_prover`, here namespace `HolCore.Metis.Prover`) followed by the HOL Light
integration layer.  All mutable state (fresh-name generator, clause-id counter,
`Random`, `split_limit`, verbosity refs) is confined to `Session.lean`. -/

import HolCore.Bool
import HolCore.Equal
import HolCore.Basics
import HolCore.Meson
import HolCore.FirstOrder

open HolCore.Kernel HolCore.Basics HolCore.Lib HolCore.Bool HolCore.Equal HolCore.Meson
open HolCore.Preterm HolCore.Printer HolCore.Tactics
open HolCore.System

namespace HolCore.Metis

set_option maxRecDepth 8000

/-- Controls output verbosity of METIS's proof reconstruction (`metisverb`,
    metis.ml 21).  Off by default, as in HOL Light. -/
initialize metisverb : IO.Ref Bool ← IO.mkRef false

/-- `Metis_unify.verb` (metis.ml 9647): traces `unify_fo_ho_term`.  Off by
    default, as in HOL Light. -/
initialize metis_unify_verb : IO.Ref Bool ← IO.mkRef false

/- The tracing prints through `FirstOrder.stdPrintf` / `stdQueue`, the
   emulated `Format.std_formatter`. -/
open HolCore.FirstOrder (stdPrintf stdQueue)

/- =========================================================================
   Metis_prover : a self-contained pure first-order theorem prover.
   ========================================================================= -/

namespace Prover

/- ---------------------------------------------------------------------- -/
/- Emulating SML Word type (which is unsigned) and other operations.       -/
/- ---------------------------------------------------------------------- -/

/- -- Word (`module Word`) --------------------------------------------------
   In OCaml these are `int` bit-operations.  Lean's `Int` has the same
   arithmetic/logical ops; the bitwise ones we route through `Int.toNat`/back
   where the Metis Model code (the only client) always uses non-negative
   values.  `shiftLeft/shiftRight/andb/orb/xorb/notb` follow SML semantics
   only in the absence of overflow, matching the OCaml comment. -/
/-- Three-way integer comparison returning `-1/0/1` (OCaml `compare` / `Pervasives.compare`
    on ints).  Metis threads three-way `Int` comparators everywhere. -/
def intCompare (x y : Int) : Int := if x < y then -1 else if x = y then 0 else 1

namespace Word

abbrev word := Int

def compare (x y : word) : Int := intCompare x y

def shiftLeft  (x y : word) : word := x <<< y.toNat
def shiftRight (x y : word) : word := x >>> y.toNat

/-- `minus (x,y) = x - y`.  This is only the same as the SML version, if there
    is no overflow. -/
def minus (x y : word) : word := x - y

/-- Bit width for two's-complement emulation (OCaml native int is 63-bit; Metis
    Model values are far smaller, so 64 bits is more than enough).  Emulating a
    fixed width lets `andb`/`orb`/`xorb` behave like OCaml's `land`/`lor`/`lxor`
    on NEGATIVE operands too (e.g. the `notb`-produced masks in Model's set
    operations), which a naive `Int.toNat` would wrongly collapse to 0. -/
def wordBits : Nat := 64
def wordMask : Nat := (1 <<< wordBits) - 1
/-- Interpret a `wordBits`-wide `Nat` bit pattern back as a signed `word`. -/
private def ofBits (n : Nat) : word :=
  let n := n &&& wordMask
  if n >>> (wordBits - 1) = 1 then (Int.ofNat n) - (1 <<< wordBits) else Int.ofNat n
/-- `wordBits`-wide two's-complement bit pattern of any `Int` (incl. negatives). -/
private def bitsOf (x : word) : Nat :=
  (if x ≥ 0 then x.toNat else ((1 <<< wordBits) + x).toNat) &&& wordMask

def andb (x y : word) : word := ofBits (bitsOf x &&& bitsOf y)
def orb  (x y : word) : word := ofBits (bitsOf x ||| bitsOf y)
def xorb (x y : word) : word := ofBits (bitsOf x ^^^ bitsOf y)
def notb (x : word) : word := -(x + 1)   -- SML `lnot x = -(x+1)`

def toInt   (x : word) : Int := x
def fromInt (x : Int) : word := x

end Word

/- -- Mlist: list helpers (`module Mlist`) ---------------------------------
   Several of these already exist in `Lib`; we provide the Metis-specific
   ones and alias the rest to keep call-sites faithful to the OCaml names. -/
namespace Mlist

/-- `foldl f a l = List.fold_left (fun acc x -> f (x, acc)) a l`. -/
def foldl (f : α × σ → σ) (a : σ) (l : List α) : σ :=
  l.foldl (fun acc x => f (x, acc)) a

/-- `foldr f a l = List.fold_right (fun x acc -> f (x, acc)) l a`. -/
def foldr (f : α × σ → σ) (a : σ) (l : List α) : σ :=
  l.foldr (fun x acc => f (x, acc)) a

def null (l : List α) : Bool := l.isEmpty

/-- `tabulate (n,f) = [f 0; f 1; ...; f (n-1)]`. -/
def tabulate (n : Nat) (f : Nat → α) : List α :=
  (List.range n).map f

/-- `find p l = try Some (List.find p l) with Not_found -> None`. -/
def find (p : α → Bool) (l : List α) : Option α := l.find? p

/-- `first f l`: first `Some`-valued `f x` scanning left to right. -/
def first (f : α → Option β) : List α → Option β
  | [] => none
  | x :: xs => match f x with | none => first f xs | s => s

/-- `enumerate l = mapi (fun i y -> (i, y)) l`. -/
def enumerate (l : List α) : List (Nat × α) :=
  l.zipIdx.map (fun (x, i) => (i, x))

/-- `revDivide n l = (rev (take n l), drop n l)`, failing if `l` too short. -/
def revDivide (l : List α) (n : Nat) : Except String (List α × List α) :=
  let rec revDiv (acc : List α) : List α × Nat → Except String (List α × List α)
    | (l, 0) => .ok (acc, l)
    | ([], _) => .error "Metis_prover.Mlist.revDivide"
    | (h :: t, n + 1) => revDiv (h :: acc) (t, n)
  revDiv [] (l, n)

/-- `updateNth (n,x) l`: replace the `n`-th element of `l` with `x`. -/
def updateNth (n : Nat) (x : α) (l : List α) : Except String (List α) := do
  let (a, b) ← revDivide l n
  match b with
  | [] => .error "Metis_prover.Mlist.updateNth"
  | _ :: t => .ok (a.reverseAux (x :: t))

/-- OCaml's `List.sort cmp` (stdlib), which metis.ml uses: a STABLE merge
    sort, so elements comparing equal keep their order.  (Not HOL Light's
    lib.ml `sort`, a quicksort that puts equal elements before the pivot,
    reversing them; using that here changed which of two equally ranked
    rewrites METIS tried first.) -/
def listSort (cmp : α → α → Int) (l : List α) : List α :=
  l.mergeSort (fun a b => decide (cmp a b ≤ 0))

/-- `sortMap f cmp l` (metis.ml 78): sort `l` by `cmp` on the `f`-images. -/
def sortMap (f : α → β) (cmp : β → β → Int) (l : List α) : List α :=
  match l with
  | [] => []
  | [x] => [x]
  | xs =>
    let nxs := xs.map (fun x => (f x, x))
    let nys := listSort (fun p q => cmp p.1 q.1) nxs
    nys.map Prod.snd

end Mlist

/- -- Useful: ML utility functions (`module Useful`) -----------------------
   The impure parts (`generator`, `newInt`, `newInts`, `critical`) live in
   `Session.lean`; here we provide the pure helpers. -/
namespace Useful

/- ---------------------------------------------------------------------- -/
/- Characters (MF).                                                        -/
/- ---------------------------------------------------------------------- -/

def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/- ---------------------------------------------------------------------- -/
/- Exceptions.                                                             -/
/- ---------------------------------------------------------------------- -/

/-- `total f x = try Some (f x) with Failure _ -> None`, for `Except`-valued `f`. -/
def total (f : α → Except String β) (x : α) : Option β :=
  match f x with | .ok y => some y | .error _ => none

/-- `exp m x y z`: fast exponentiation `x^y` accumulated into `z` under monoid `m`. -/
partial def exp (m : α × α → α) (x : α) (y : Nat) (z : α) : α :=
  match y with
  | 0 => z
  | _ => exp m (m (x, x)) (y / 2) (if y % 2 = 0 then z else m (z, x))

/- ---------------------------------------------------------------------- -/
/- Comparisons.                                                            -/
/- ---------------------------------------------------------------------- -/

def revCompare (cmp : α → α → Int) (x y : α) : Int := cmp y x

def prodCompare (xCmp : α → α → Int) (yCmp : β → β → Int)
    (p1 p2 : α × β) : Int :=
  let c := xCmp p1.1 p2.1
  if c ≠ 0 then c else yCmp p1.2 p2.2

def lexCompare (cmp : α → α → Int) : List α → List α → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | x :: xs, y :: ys =>
    let c := cmp x y
    if c ≠ 0 then c else lexCompare cmp xs ys

def boolCompare (x y : Bool) : Int :=
  match x, y with
  | false, true => -1
  | true, false => 1
  | _, _ => 0

def intCompare (x y : Int) : Int := HolCore.Metis.Prover.intCompare x y

def mkPrefix (p s : String) : String := p ++ s

/-- Drop the maximal trailing run of chars satisfying `pred` (helper). -/
partial def dropSuffixChars (pred : Char → Bool) (cs : List Char) : List Char :=
  match cs.reverse with
  | [] => []
  | c :: rest => if pred c then dropSuffixChars pred rest.reverse else cs

/-- `stripSuffix pred s`: drop the maximal suffix of `s` all satisfying `pred`. -/
def stripSuffix (pred : Char → Bool) (s : String) : String :=
  String.ofList (dropSuffixChars pred s.toList)

/-- `interval m len = [m; m+1; ...; m+len-1]`. -/
def interval (m : Int) : Nat → List Int
  | 0 => []
  | len + 1 => m :: interval (m + 1) len

/-- `divides a b`: does `a` divide `b`? (SML `Useful.divides`). -/
def divides (a b : Int) : Bool :=
  if b = 0 then true
  else if a = 0 then false
  else b % (a.natAbs : Int) = 0

end Useful

/- ---------------------------------------------------------------------- -/
/- FINITE MAPS IMPLEMENTED WITH RANDOMLY BALANCED TREES                     -/
/- ---------------------------------------------------------------------- -/

/- A type of finite maps. -/

/- ---------------------------------------------------------------------- -/
/- More map and set types for Metis.                                      -/
/- ---------------------------------------------------------------------- -/

/- -- Ordered maps (`Mmap.Make`) -------------------------------------------
   Every finite map actually used by Metis (`Name.Map`, `Intmap`,
   `Name_arity.Map`, `Literal.Map`, `Literal.Set_map`) is an `Mmap.Make`
   instance — an ordered map over a key comparison.  We implement one generic
   ordered map backed by an assoc list kept sorted by the key comparator, so
   iteration (`toList`/`foldl`/`foldr`/`bindings`) is in key order exactly as
   OCaml's `Map.Make` guarantees.  A map carries its own comparator so the
   pure operations need no typeclass.  (This replaces the OCaml priority
   search trees; the per-tree helper operations have no separate counterpart.) -/
namespace OrdMap

/-- An ordered map: comparator + assoc list sorted (ascending) by key. -/
structure Map (κ : Type) (α : Type) where
  cmp : κ → κ → Int
  entries : List (κ × α)

instance : Inhabited (Map κ α) := ⟨⟨fun _ _ => 0, []⟩⟩

variable {κ α β : Type}

def newMap (cmp : κ → κ → Int) : Map κ α := ⟨cmp, []⟩

def null (m : Map κ α) : Bool := m.entries.isEmpty

def size (m : Map κ α) : Nat := m.entries.length

def toList (m : Map κ α) : List (κ × α) := m.entries

/-- Insert/overwrite key, keeping entries sorted by `cmp`. -/
def insert (m : Map κ α) (kv : κ × α) : Map κ α :=
  let rec go : List (κ × α) → List (κ × α)
    | [] => [kv]
    | (k, v) :: rest =>
      let c := m.cmp kv.1 k
      if c < 0 then kv :: (k, v) :: rest
      else if c = 0 then kv :: rest
      else (k, v) :: go rest
  ⟨m.cmp, go m.entries⟩

def singleton (cmp : κ → κ → Int) (kv : κ × α) : Map κ α := insert (newMap cmp) kv

def peek (m : Map κ α) (k : κ) : Option α :=
  let rec go : List (κ × α) → Option α
    | [] => none
    | (k', v) :: rest =>
      let c := m.cmp k k'
      if c < 0 then none
      else if c = 0 then some v
      else go rest
  go m.entries

def inDomain (k : κ) (m : Map κ α) : Bool := (peek m k).isSome

def get (m : Map κ α) (k : κ) : Except String α :=
  match peek m k with
  | some v => .ok v
  | none => .error "Mmap.get: element not found"

def delete (m : Map κ α) (k : κ) : Map κ α :=
  ⟨m.cmp, m.entries.filter (fun kv => m.cmp k kv.1 ≠ 0)⟩

def fromList (cmp : κ → κ → Int) (l : List (κ × α)) : Map κ α :=
  l.foldr (fun kv acc => insert acc kv) (newMap cmp)

/-- `foldl f b m = List.fold_left (fun s (k,v) -> f (k,v,s)) b (bindings m)`. -/
def foldl (f : κ × α × σ → σ) (b : σ) (m : Map κ α) : σ :=
  m.entries.foldl (fun s (k, v) => f (k, v, s)) b

/-- OCaml `Mmap.foldr = foldl` (folds over ascending bindings). -/
def foldr (f : κ × α × σ → σ) (b : σ) (m : Map κ α) : σ := foldl f b m

def filter (f : κ × α → Bool) (m : Map κ α) : Map κ α :=
  ⟨m.cmp, m.entries.filter (fun kv => f kv)⟩

/- Mapping and folding. -/

def mapPartial (f : κ × α → Option β) (m : Map κ α) : Map κ β :=
  ⟨m.cmp, m.entries.filterMap (fun (k, v) => (f (k, v)).map (fun y => (k, y)))⟩

def transform (f : α → β) (m : Map κ α) : Map κ β :=
  ⟨m.cmp, m.entries.map (fun (k, v) => (k, f v))⟩

/-- `map f m = Ma.map (fun (k,v) -> (k, f (k,v)))` — value map that sees the key. -/
def mapv (f : κ × α → β) (m : Map κ α) : Map κ β :=
  ⟨m.cmp, m.entries.map (fun (k, v) => (k, f (k, v)))⟩

def existsb (f : κ × α → Bool) (m : Map κ α) : Bool :=
  m.entries.any (fun kv => f kv)

/- Joining (all join operations prefer keys in the second map). -/

/-- `union f m1 m2` (OCaml `Mmap.union`): merge preferring `m2`'s key on clash,
    resolving colliding values with `f ((k,x),(k,y))`; `None` from `f` drops the key. -/
def union (f : (κ × α) × (κ × α) → Option α) (m1 m2 : Map κ α) : Map κ α :=
  -- Collect all keys (m1's keys and m2's), merge per OCaml Ma.merge semantics.
  let cmp := m2.cmp
  let step (acc : Map κ α) (k : κ) : Map κ α :=
    let xo := peek m1 k
    let yo := peek m2 k
    match xo, yo with
    | some x, some y => match f ((k, x), (k, y)) with
                        | some z => insert acc (k, z)
                        | none => acc
    | some x, none => insert acc (k, x)
    | none, some y => insert acc (k, y)
    | none, none => acc
  let keys := (m1.entries.map Prod.fst) ++ (m2.entries.map Prod.fst)
  keys.foldl step (newMap cmp)

/-- `Name_arity.Map.compose m1 m2`: `mapPartial (fun ((_,a),n) -> peek m2 (n,a)) m1`.
    Specialised below where the key type is `Name × Int`; kept generic here via
    the caller supplying the reindex function. -/
def compose (reindex : κ × α → Option β) (m1 : Map κ α) : List (κ × β) :=
  m1.entries.filterMap (fun (k, v) => (reindex (k, v)).map (fun n => (k, n)))

end OrdMap

/- ---------------------------------------------------------------------- -/
/- FINITE SETS IMPLEMENTED WITH RANDOMLY BALANCED TREES                     -/
/- ---------------------------------------------------------------------- -/

/- A type of finite sets. -/

/- -- Ordered sets (`Mset.Make`) -------------------------------------------
   `Name.Set`, `Intset`, `Name_arity.Set`, `Atom.Set`, `Literal.Set` are all
   `Mset.Make` instances: ordered sets over an element comparison, backed here
   by a sorted list.  A set carries its comparator. -/
namespace OrdSet

structure Set (α : Type) where
  cmp : α → α → Int
  elems : List α

instance : Inhabited (Set α) := ⟨⟨fun _ _ => 0, []⟩⟩

variable {α β : Type}

def empty (cmp : α → α → Int) : Set α := ⟨cmp, []⟩

def null (s : Set α) : Bool := s.elems.isEmpty

def size (s : Set α) : Nat := s.elems.length

def toList (s : Set α) : List α := s.elems

def member (x : α) (s : Set α) : Bool := s.elems.any (fun y => s.cmp x y = 0)

def add (s : Set α) (x : α) : Set α :=
  let rec go : List α → List α
    | [] => [x]
    | y :: rest =>
      let c := s.cmp x y
      if c < 0 then x :: y :: rest
      else if c = 0 then y :: rest
      else y :: go rest
  ⟨s.cmp, go s.elems⟩

def singleton (cmp : α → α → Int) (x : α) : Set α := add (empty cmp) x

def delete (s : Set α) (x : α) : Set α :=
  ⟨s.cmp, s.elems.filter (fun y => s.cmp x y ≠ 0)⟩

/- Pmapping and folding. -/

/-- `foldr f a s = Se.fold (fun x acc -> f (x,acc)) s a` (metis.ml 1893).
    OCaml's `Set.fold f s a` computes `f xN (... (f x2 (f x1 a)))` with
    `x1 < ... < xN`: it applies `f` to the SMALLEST element FIRST.  That is a
    LEFT fold over the ascending element list, so `List.foldl`, not
    `List.foldr` (which would apply `f` to the LARGEST element first and reverse
    every non-commutative accumulation).  Metis defines `foldl = foldr` for
    sets, so both use this. -/
def foldr (f : α × σ → σ) (a : σ) (s : Set α) : σ :=
  s.elems.foldl (fun acc x => f (x, acc)) a

def foldl (f : α × σ → σ) (a : σ) (s : Set α) : σ := foldr f a s

def union (s1 s2 : Set α) : Set α := s1.elems.foldl (fun acc x => add acc x) s2

def difference (s1 s2 : Set α) : Set α :=
  ⟨s1.cmp, s1.elems.filter (fun x => !member x s2)⟩

def intersect (s1 s2 : Set α) : Set α :=
  ⟨s1.cmp, s1.elems.filter (fun x => member x s2)⟩

def intersectList : List (Set α) → Set α
  | [] => ⟨fun _ _ => 0, []⟩   -- OCaml returns Se.empty; comparator irrelevant when unused
  | s :: ss => ss.foldr (fun t acc => intersect t acc) s

def fromList (cmp : α → α → Int) (l : List α) : Set α :=
  l.foldr (fun x acc => add acc x) (empty cmp)

def existsb (p : α → Bool) (s : Set α) : Bool := s.elems.any p

def all (p : α → Bool) (s : Set α) : Bool := s.elems.all p

def count (p : α → Bool) (s : Set α) : Nat := (s.elems.filter p).length

def subset (s1 s2 : Set α) : Bool := s1.elems.all (fun x => member x s2)

def equal (s1 s2 : Set α) : Bool := subset s1 s2 && subset s2 s1

def compareSet (s1 s2 : Set α) : Int := Useful.lexCompare s1.cmp s1.elems s2.elems

def pick (s : Set α) : Except String α :=
  match s.elems with | x :: _ => .ok x | [] => .error "Mset.pick: empty"

/-- `findl p s = Se.fold go s None`, keeping the first (ascending) match. -/
def findl (p : α → Bool) (s : Set α) : Option α :=
  let go (acc : Option α) (x : α) : Option α :=
    match acc with | some _ => acc | none => if p x then some x else none
  s.elems.foldl go none

/-- `firstl f s`: first `Some`-valued `f x` in ascending order. -/
def firstl (f : α → Option β) (s : Set α) : Option β :=
  let go (acc : Option β) (x : α) : Option β :=
    match acc with | some _ => acc | none => f x
  s.elems.foldl go none

/- Converting to and from lists. -/

def transform (f : α → β) (s : Set α) : List β :=
  s.elems.foldr (fun x acc => f x :: acc) []

end OrdSet

/- ---------------------------------------------------------------------- -/
/- A HEAP DATATYPE FOR ML                                                  -/
/- ---------------------------------------------------------------------- -/

/- -- Heap (`module Heap`) --------------------------------------------------
   Leftist heaps as in Purely Functional Data Structures, by Chris Okasaki.
   Used by `Waiting`. -/
namespace Heap

inductive Node (α : Type) where
  | Em
  | Tr (rank : Int) (x : α) (a b : Node α)

structure Heap (α : Type) where
  cmp : α → α → Int
  n : Int
  root : Node α

variable {α : Type}

def rank : Node α → Int
  | .Em => 0
  | .Tr r _ _ _ => r

def makeT (x : α) (a b : Node α) : Node α :=
  if rank a ≥ rank b then .Tr (rank b + 1) x a b else .Tr (rank a + 1) x b a

partial def mergeNode (cmp : α → α → Int) : Node α → Node α → Node α
  | h, .Em => h
  | .Em, h => h
  -- `(Tr (_,x,a1,b1) as h1, (Tr (_,y,a2,b2) as h2))` (metis.ml 1966): the
  -- passed-through node is the ORIGINAL `h1`/`h2`, rank intact.  Rebuilding it
  -- with rank 0 breaks the leftist invariant, reshaping the heap and so changing
  -- the removal order of equal-priority elements.
  | h1@(.Tr _ x a1 b1), h2@(.Tr _ y a2 b2) =>
    if cmp x y > 0 then makeT y a2 (mergeNode cmp h1 b2)
    else makeT x a1 (mergeNode cmp b1 h2)

def newHeap (cmp : α → α → Int) : Heap α := ⟨cmp, 0, .Em⟩

def add (h : Heap α) (x : α) : Heap α :=
  ⟨h.cmp, h.n + 1, mergeNode h.cmp (.Tr 1 x .Em .Em) h.root⟩

def size (h : Heap α) : Int := h.n

def null (h : Heap α) : Bool := size h = 0

def top (h : Heap α) : Except String α :=
  match h.root with
  | .Em => .error "Heap.Empty"
  | .Tr _ x _ _ => .ok x

def remove (h : Heap α) : Except String (α × Heap α) :=
  match h.root with
  | .Em => .error "Heap.Empty"
  | .Tr _ x a b => .ok (x, ⟨h.cmp, h.n - 1, mergeNode h.cmp a b⟩)

end Heap

/- -- Name: FOL names (`module Name`) ---------------------------------------
   A type of names.  A name is a string.  Fresh-name generation
   (`newName`/`newNames`, driven by `Useful.generator`) is impure and lives in
   `Session.lean`; the pure ordering, variant, and parsing helpers are here.
   `Name.Map`/`Name.Set` are ordered containers over `Name.compare`. -/
namespace Name

abbrev name := String

/- A total ordering. -/
def compare (n1 n2 : name) : Int :=
  match Ord.compare n1 n2 with | .lt => -1 | .eq => 0 | .gt => 1

def equal (n1 n2 : name) : Bool := n1 = n2

def prefix_ : String := "_"
def numName (i : Int) : name := Useful.mkPrefix prefix_ (toString i)

/-- `variantPrime avoid n`: append primes to `n` until `avoid` is false. -/
partial def variantPrime (avoid : name → Bool) (n : name) : name :=
  if avoid n then variantPrime avoid (n ++ "'") else n

/-- `variantNum avoid n`: append/replace numeric suffix until `avoid` is false. -/
partial def variantNumAux (avoid : name → Bool) (base : String) (i : Nat) : name :=
  let n_i := base ++ toString i
  if avoid n_i then variantNumAux avoid base (i + 1) else n_i

def variantNum (avoid : name → Bool) (n : name) : name :=
  let isDigitOrPrime (c : Char) : Bool := c = '\'' || Useful.isDigit c
  if !avoid n then n
  else
    let base := Useful.stripSuffix isDigitOrPrime n
    variantNumAux avoid base 0

def toStr (s : name) : String := s
def fromString (s : String) : name := s

/-- Comparator used to instantiate `Name.Map`/`Name.Set`. -/
def cmp : name → name → Int := compare

end Name

/- -- Name_arity: name/arity pairs (`module Name_arity`) --------------------
   A type of name/arity pairs. -/
namespace Name_arity

abbrev nameArity := Name.name × Int

def name (na : nameArity) : Name.name := na.1
def arity (na : nameArity) : Int := na.2

/- Testing for different arities. -/
def nary (i : Int) (n_i : nameArity) : Bool := arity n_i = i
def nullary : nameArity → Bool := nary 0
def unary   : nameArity → Bool := nary 1
def binary  : nameArity → Bool := nary 2
def ternary : nameArity → Bool := nary 3

/- A total ordering. -/
def compare (na1 na2 : nameArity) : Int :=
  let c := Name.compare na1.1 na2.1
  if c ≠ 0 then c else Useful.intCompare na1.2 na2.2

def equal (na1 na2 : nameArity) : Bool := na1.2 = na2.2 && Name.equal na1.1 na2.1

def cmp : nameArity → nameArity → Int := compare

end Name_arity

/- -- Concrete container instantiations ------------------------------------
   OCaml writes `Name.Set.add`, `Name_arity.Map.peek`, etc.  Each is an
   `OrdMap`/`OrdSet` fixed at the relevant comparator.  We expose thin
   namespaces mirroring the OCaml module paths so call-sites stay faithful.
   `Name.Map`/`Name.Set` live under `Name`; `Name_arity.Map`/`.Set` under
   `Name_arity`. -/

namespace Name

/- `Name.Set` = ordered set of names. -/
namespace Set
abbrev set := OrdSet.Set Name.name
def empty : set := OrdSet.empty Name.cmp
def add (s : set) (x : Name.name) : set := OrdSet.add s x
def singleton (x : Name.name) : set := OrdSet.singleton Name.cmp x
def member (x : Name.name) (s : set) : Bool := OrdSet.member x s
def delete (s : set) (x : Name.name) : set := OrdSet.delete s x
def union (s1 s2 : set) : set := OrdSet.union s1 s2
def difference (s1 s2 : set) : set := OrdSet.difference s1 s2
def foldl (f : Name.name × σ → σ) (a : σ) (s : set) : σ := OrdSet.foldl f a s
def foldr (f : Name.name × σ → σ) (a : σ) (s : set) : σ := OrdSet.foldr f a s
def toList (s : set) : List Name.name := OrdSet.toList s
def size (s : set) : Nat := OrdSet.size s
def null (s : set) : Bool := OrdSet.null s
def fromList (l : List Name.name) : set := OrdSet.fromList Name.cmp l
def equal (s1 s2 : set) : Bool := OrdSet.equal s1 s2
end Set

/- `Name.Map` = ordered map keyed by names. -/
namespace Map
abbrev map (α : Type) := OrdMap.Map Name.name α
def newMap : map α := OrdMap.newMap Name.cmp
def null (m : map α) : Bool := OrdMap.null m
def size (m : map α) : Nat := OrdMap.size m
def peek (m : map α) (k : Name.name) : Option α := OrdMap.peek m k
def insert (m : map α) (kv : Name.name × α) : map α := OrdMap.insert m kv
def inDomain (k : Name.name) (m : map α) : Bool := OrdMap.inDomain k m
def toList (m : map α) : List (Name.name × α) := OrdMap.toList m
def fromList (l : List (Name.name × α)) : map α := OrdMap.fromList Name.cmp l
def foldl (f : Name.name × α × σ → σ) (b : σ) (m : map α) : σ := OrdMap.foldl f b m
def foldr (f : Name.name × α × σ → σ) (b : σ) (m : map α) : σ := OrdMap.foldr f b m
def filter (f : Name.name × α → Bool) (m : map α) : map α := OrdMap.filter f m
def transform (f : α → β) (m : map α) : map β := OrdMap.transform f m
def existsb (f : Name.name × α → Bool) (m : map α) : Bool := OrdMap.existsb f m
def union (f : (Name.name × α) × (Name.name × α) → Option α) (m1 m2 : map α) : map α :=
  OrdMap.union f m1 m2
end Map

end Name

namespace Name_arity

namespace Set
abbrev set := OrdSet.Set Name_arity.nameArity
def empty : set := OrdSet.empty Name_arity.cmp
def add (s : set) (x : Name_arity.nameArity) : set := OrdSet.add s x
def union (s1 s2 : set) : set := OrdSet.union s1 s2
def all (p : Name_arity.nameArity → Bool) (s : set) : Bool := OrdSet.all p s
def allNullary (s : set) : Bool := OrdSet.all Name_arity.nullary s
def toList (s : set) : List Name_arity.nameArity := OrdSet.toList s
def member (x : Name_arity.nameArity) (s : set) : Bool := OrdSet.member x s
end Set

namespace Map
abbrev map (α : Type) := OrdMap.Map Name_arity.nameArity α
def newMap : map α := OrdMap.newMap Name_arity.cmp
def null (m : map α) : Bool := OrdMap.null m
def peek (m : map α) (k : Name_arity.nameArity) : Option α := OrdMap.peek m k
def insert (m : map α) (kv : Name_arity.nameArity × α) : map α := OrdMap.insert m kv
def singleton (kv : Name_arity.nameArity × α) : map α := OrdMap.singleton Name_arity.cmp kv
def fromList (l : List (Name_arity.nameArity × α)) : map α := OrdMap.fromList Name_arity.cmp l
def foldl (f : Name_arity.nameArity × α × σ → σ) (b : σ) (m : map α) : σ := OrdMap.foldl f b m
def foldr (f : Name_arity.nameArity × α × σ → σ) (b : σ) (m : map α) : σ := OrdMap.foldr f b m
def mapPartial (f : Name_arity.nameArity × α → Option β) (m : map α) : map β := OrdMap.mapPartial f m
def transform (f : α → β) (m : map α) : map β := OrdMap.transform f m
def union (f : (Name_arity.nameArity × α) × (Name_arity.nameArity × α) → Option α)
    (m1 m2 : map α) : map α := OrdMap.union f m1 m2
/-- `compose m1 m2 = mapPartial (fun ((_,a),n) -> peek m2 (n,a)) m1`, where `m1`
    maps `nameArity → Name.name` and `m2` maps `nameArity → α`. -/
def compose (m1 : map Name.name) (m2 : map α) : map α :=
  OrdMap.mapPartial (fun (na, n) => OrdMap.peek m2 (n, na.2)) m1
end Map

end Name_arity

/- -- Pset: the small set used by `Subsume` (`module Pset`) -----------------
   Metis' `Pset` is a full priority-search-tree set, but `Subsume` uses only
   `empty`, `add`, `firstl`, and `intersect` over a fixed comparator, so we
   back it with a sorted list (identical semantics for those operations).  This
   avoids translating the ~700-line `Pmap` randomly-balanced-tree module, which
   is otherwise dead code (`Name.Map`/`Name.Set` are `Mmap`/`Mset`, not Pmap). -/
/- ---------------------------------------------------------------------- -/
/- More map and set modules to support Metis.                             -/
/- ---------------------------------------------------------------------- -/

namespace Pset

abbrev set (α : Type) := OrdSet.Set α

def empty (cmp : α → α → Int) : set α := OrdSet.empty cmp
def add (s : set α) (x : α) : set α := OrdSet.add s x
def firstl (f : α → Option β) (s : set α) : Option β := OrdSet.firstl f s
def intersect (s1 s2 : set α) : set α := OrdSet.intersect s1 s2

end Pset

/- -- Intmap / Intset (`module Intmap` / `module Intset`) --------------------
   Integer-keyed ordered map/set used by nets, Subsume, and Rewrite. -/
namespace Intmap
abbrev map (α : Type) := OrdMap.Map Int α
def newMap : map α := OrdMap.newMap Useful.intCompare
def null (m : map α) : Bool := OrdMap.null m
def size (m : map α) : Nat := OrdMap.size m
def get (m : map α) (k : Int) : Except String α := OrdMap.get m k
def peek (m : map α) (k : Int) : Option α := OrdMap.peek m k
def insert (m : map α) (kv : Int × α) : map α := OrdMap.insert m kv
def delete (m : map α) (k : Int) : map α := OrdMap.delete m k
def inDomain (k : Int) (m : map α) : Bool := OrdMap.inDomain k m
def toList (m : map α) : List (Int × α) := OrdMap.toList m
def foldl (f : Int × α × σ → σ) (b : σ) (m : map α) : σ := OrdMap.foldl f b m
def foldr (f : Int × α × σ → σ) (b : σ) (m : map α) : σ := OrdMap.foldr f b m
def filter (f : Int × α → Bool) (m : map α) : map α := OrdMap.filter f m
def transform (f : α → β) (m : map α) : map β := OrdMap.transform f m
def existsb (f : Int × α → Bool) (m : map α) : Bool := OrdMap.existsb f m
end Intmap

namespace Intset
abbrev set := OrdSet.Set Int
def empty : set := OrdSet.empty Useful.intCompare
def add (s : set) (x : Int) : set := OrdSet.add s x
def delete (s : set) (x : Int) : set := OrdSet.delete s x
def member (x : Int) (s : set) : Bool := OrdSet.member x s
def null (s : set) : Bool := OrdSet.null s
def equal (s1 s2 : set) : Bool := OrdSet.equal s1 s2
def toList (s : set) : List Int := OrdSet.toList s
def foldl (f : Int × σ → σ) (a : σ) (s : set) : σ := OrdSet.foldl f a s
def firstl (f : Int → Option β) (s : set) : Option β := OrdSet.firstl f s
def transform (f : Int → β) (s : set) : List β := OrdSet.transform f s
end Intset

/- -- Term: first-order logic terms (`module Term`) -------------------------
   A type of first order logic terms. -/
namespace Term

abbrev var := Name.name
abbrev functionName := Name.name
abbrev function_t := functionName × Int
abbrev const := functionName

/-- A first-order term. -/
inductive term where
  | Var (v : Name.name)
  | Fn  (f : Name.name) (args : List term)
  deriving Inhabited

/- Constructors and destructors. -/

def destVar : term → Except String Name.name
  | .Var v => .ok v
  | .Fn _ _ => .error "destVar"

def isVar (t : term) : Bool := HolCore.Lib.can destVar t

def equalVar (v : var) : term → Bool
  | .Var v' => Name.equal v v'
  | _ => false

def destFn : term → Except String (Name.name × List term)
  | .Fn f a => .ok (f, a)
  | .Var _ => .error "destFn"

def isFn (t : term) : Bool := HolCore.Lib.can destFn t

def fnName (tm : term) : Except String Name.name := do return (← destFn tm).1
def fnArguments (tm : term) : Except String (List term) := do return (← destFn tm).2
def fnArity (tm : term) : Except String Int := do return Int.ofNat (← fnArguments tm).length
def fnFunction (tm : term) : Except String (Name.name × Int) := do
  return (← fnName tm, ← fnArity tm)

/-- `functions tm`: the set of function name/arity pairs occurring in `tm`. -/
partial def functionsAux : Name_arity.Set.set → List term → Name_arity.Set.set
  | fs, [] => fs
  | fs, .Var _ :: tms => functionsAux fs tms
  | fs, .Fn n l :: tms =>
    functionsAux (Name_arity.Set.add fs (n, Int.ofNat l.length)) (l ++ tms)
def functions (tm : term) : Name_arity.Set.set := functionsAux Name_arity.Set.empty [tm]

partial def functionNamesAux : Name.Set.set → List term → Name.Set.set
  | fs, [] => fs
  | fs, .Var _ :: tms => functionNamesAux fs tms
  | fs, .Fn n l :: tms => functionNamesAux (Name.Set.add fs n) (l ++ tms)
def functionNames (tm : term) : Name.Set.set := functionNamesAux Name.Set.empty [tm]

/- Constants -/

def mkConst (c : const) : term := .Fn c []

def destConst : term → Except String const
  | .Fn c [] => .ok c
  | _ => .error "destConst"

def isConst (t : term) : Bool := HolCore.Lib.can destConst t

/- Binary functions -/

def mkBinop (f : Name.name) (ab : term × term) : term := .Fn f [ab.1, ab.2]

def destBinop (f : Name.name) : term → Except String (term × term)
  | .Fn x [a, b] => if Name.equal x f then .ok (a, b) else .error "Term.destBinop: wrong binop"
  | _ => .error "Term.destBinop: not a binop"

def isBinop (f : Name.name) (t : term) : Bool := HolCore.Lib.can (destBinop f) t

/- The size of a term in symbols. -/

def vAR_SYMBOLS : Int := 1
def fN_SYMBOLS : Int := 1

partial def symbolsAux : Int → List term → Int
  | n, [] => n
  | n, .Var _ :: tms => symbolsAux (n + vAR_SYMBOLS) tms
  | n, .Fn _ args :: tms => symbolsAux (n + fN_SYMBOLS) (args ++ tms)
def symbols (tm : term) : Int := symbolsAux 0 [tm]

/- A total comparison function for terms. -/

partial def compareAux : List (term × term) → Int
  | [] => 0
  | (tm1, tm2) :: rest =>
    match tm1, tm2 with
    | .Var v1, .Var v2 =>
      let c := Name.compare v1 v2
      if c ≠ 0 then c else compareAux rest
    | .Var _, .Fn _ _ => -1
    | .Fn _ _, .Var _ => 1
    | .Fn f1 a1, .Fn f2 a2 =>
      let c := Name.compare f1 f2
      if c ≠ 0 then c
      else
        let c := Useful.intCompare (Int.ofNat a1.length) (Int.ofNat a2.length)
        if c ≠ 0 then c
        else compareAux (a1.zip a2 ++ rest)
def compare (tm1 tm2 : term) : Int := compareAux [(tm1, tm2)]

def equal (tm1 tm2 : term) : Bool := compare tm1 tm2 = 0

/- Subterms. -/

abbrev path := List Int

partial def subterm' : term × path → Except String term
  | (tm, []) => .ok tm
  | (.Var _, _ :: _) => .error "Term.subterm: Var"
  | (.Fn _ tms, h :: t) =>
    if h ≥ Int.ofNat tms.length then .error "Term.replace: Fn"
    else subterm' (tms.getD h.toNat default, t)
def subterm (s : term) (t : path) : Except String term := subterm' (s, t)

/-- `subterms tm`: all `(path, subterm)` pairs. -/
partial def subtermsAux : List (path × term) × List (path × term) → List (path × term)
  | ([], acc) => acc
  | ((p, tm) :: rest, acc) =>
    let acc := (p.reverse, tm) :: acc
    match tm with
    | .Var _ => subtermsAux (rest, acc)
    | .Fn _ args =>
      let mapped := (Mlist.enumerate args).map (fun (n, arg) => (Int.ofNat n :: p, arg))
      subtermsAux (mapped ++ rest, acc)
def subterms (tm : term) : List (path × term) := subtermsAux ([([], tm)], [])

/-- `replace tm (path,res)`: replace the subterm at `path` with `res`. -/
partial def replace (tm : term) : path × term → term
  | ([], res) => if equal res tm then tm else res
  | (h :: t, res) =>
    match tm with
    | .Var _ => tm  -- OCaml fails; only reached on malformed path
    | .Fn f tms =>
      if h ≥ Int.ofNat tms.length then tm
      else
        let arg := tms.getD h.toNat default
        let arg' := replace arg (t, res)
        if equal arg' arg then tm
        else match Mlist.updateNth h.toNat arg' tms with
             | .ok tms' => .Fn f tms'
             | .error _ => tm

/-- `find pred tm`: path to the first subterm satisfying `pred` (pre-order). -/
partial def findAux (pred : term → Bool) : List (path × term) → Option path
  | [] => none
  | (p, tm) :: rest =>
    if pred tm then some p.reverse
    else match tm with
         | .Var _ => findAux pred rest
         | .Fn _ a =>
           let subtms := (Mlist.enumerate a).map (fun (i, t) => (Int.ofNat i :: p, t))
           findAux pred (subtms ++ rest)
def find (pred : term → Bool) (tm : term) : Option path := findAux pred [([], tm)]

/- Free variables. -/

partial def freeInAux (v : var) : List term → Bool
  | [] => false
  | .Var w :: tms => Name.equal v w || freeInAux v tms
  | .Fn _ args :: tms => freeInAux v (args ++ tms)
def freeIn (v : var) (tm : term) : Bool := freeInAux v [tm]

partial def freeVarsListAux : Name.Set.set → List term → Name.Set.set
  | vs, [] => vs
  | vs, .Var v :: tms => freeVarsListAux (Name.Set.add vs v) tms
  | vs, .Fn _ args :: tms => freeVarsListAux vs (args ++ tms)
def freeVarsList (tms : List term) : Name.Set.set := freeVarsListAux Name.Set.empty tms
def freeVars (tm : term) : Name.Set.set := freeVarsList [tm]

/- Fresh variables: `newVar`/`newVars` use `Name.newName`/`newNames` (impure,
   in Session).  `avoid`/`variantPrime`/`variantNum` are pure. -/

def avoid (av : Name.Set.set) (n : Name.name) : Bool := Name.Set.member n av
def variantPrime (av : Name.Set.set) : Name.name → Name.name := Name.variantPrime (avoid av)
def variantNum (av : Name.Set.set) : Name.name → Name.name := Name.variantNum (avoid av)

/- Special support for terms with type annotations. -/

def hasTypeFunctionName : functionName := Name.fromString ":"
def hasTypeFunction : Name_arity.nameArity := (hasTypeFunctionName, 2)

def destFnHasType : functionName × List term → Except String (term × term)
  | (f, a) =>
    if !Name.equal f hasTypeFunctionName then .error "Term.destFnHasType"
    else match a with
         | [tm, ty] => .ok (tm, ty)
         | _ => .error "Term.destFnHasType"

def isFnHasType (fa : functionName × List term) : Bool := HolCore.Lib.can destFnHasType fa

def isTypedVar : term → Bool
  | .Var _ => true
  | .Fn f a => match Useful.total destFnHasType (f, a) with
               | some (.Var _, _) => true
               | _ => false

partial def typedSymbolsAux : Int → List term → Int
  | n, [] => n
  | n, tm :: tms =>
    match tm with
    | .Var _ => typedSymbolsAux (n + 1) tms
    | .Fn f a =>
      match Useful.total destFnHasType (f, a) with
      | some (tm', _) => typedSymbolsAux n (tm' :: tms)
      | none => typedSymbolsAux (n + 1) (a ++ tms)
def typedSymbols (tm : term) : Int := typedSymbolsAux 0 [tm]

partial def nonVarTypedSubtermsAux : List (path × term) × List (path × term) → List (path × term)
  | ([], acc) => acc
  | ((p, tm) :: rest, acc) =>
    match tm with
    | .Var _ => nonVarTypedSubtermsAux (rest, acc)
    | .Fn f a =>
      match Useful.total destFnHasType (f, a) with
      | some (t, _) =>
        match t with
        | .Var _ => nonVarTypedSubtermsAux (rest, acc)
        | .Fn _ _ =>
          let acc := (p.reverse, tm) :: acc
          let rest := (0 :: p, t) :: rest
          nonVarTypedSubtermsAux (rest, acc)
      | none =>
        let acc := (p.reverse, tm) :: acc
        let rest := (Mlist.enumerate a).map (fun (n, arg) => (Int.ofNat n :: p, arg)) ++ rest
        nonVarTypedSubtermsAux (rest, acc)
def nonVarTypedSubterms (tm : term) : List (path × term) :=
  nonVarTypedSubtermsAux ([([], tm)], [])

/- Special support for terms with an explicit function application operator. -/

def appName : Name.name := Name.fromString "."
def mkFnApp (fa : term × term) : Name.name × List term := (appName, [fa.1, fa.2])
def mkApp (fa : term × term) : term := .Fn (mkFnApp fa).1 (mkFnApp fa).2

def destFnApp : Name.name × List term → Except String (term × term)
  | (f, a) =>
    if !Name.equal f appName then .error "Term.destFnApp"
    else match a with
         | [fTm, aTm] => .ok (fTm, aTm)
         | _ => .error "Term.destFnApp"

def isFnApp (fa : Name.name × List term) : Bool := HolCore.Lib.can destFnApp fa

def destApp : term → Except String (term × term)
  | .Var _ => .error "Term.destApp"
  | .Fn f a => destFnApp (f, a)

def isApp (t : term) : Bool := HolCore.Lib.can destApp t

def listMkApp (f : term) (l : List term) : term := l.foldl (fun acc x => mkApp (x, acc)) f

partial def stripAppAux (tms : List term) (tm : term) : term × List term :=
  match Useful.total destApp tm with
  | some (f, a) => stripAppAux (a :: tms) f
  | none => (tm, tms)
def stripApp (tm : term) : term × List term := stripAppAux [] tm

/- Parsing and pretty printing. -/

partial def toString : term → String
  | .Var v => v
  | .Fn n [] => n
  | .Fn n l => n ++ "(" ++ String.intercalate ", " (l.map toString) ++ ")"

/-- Comparator to instantiate `Term.Map`/`Term.Set` (defined but unused by Metis). -/
def cmp : term → term → Int := compare

end Term

/- ---------------------------------------------------------------------- -/
/- FIRST ORDER LOGIC SUBSTITUTIONS                                         -/
/- ---------------------------------------------------------------------- -/

/- -- Substitute: FOL substitutions (`module Substitute`) --------------------/
namespace Substitute

/- A type of first order logic substitutions. -/

/- Basic operations. -/

/-- A substitution: a `Name.Map` from variable names to terms.  (OCaml `type subst`;
    renamed `substT` here because Lean would clash the type name with the
    `subst` application function below — OCaml overloads them freely.) -/
inductive substT where
  | Mk (m : Name.Map.map Term.term)

def empty : substT := .Mk Name.Map.newMap

def null : substT → Bool | .Mk m => Name.Map.null m
def size : substT → Nat | .Mk m => Name.Map.size m
def peek : substT → Name.name → Option Term.term | .Mk m, v => Name.Map.peek m v
def insert : substT → Name.name × Term.term → substT | .Mk m, vtm => .Mk (Name.Map.insert m vtm)
def singleton (vtm : Name.name × Term.term) : substT := insert empty vtm
def toList : substT → List (Name.name × Term.term) | .Mk m => Name.Map.toList m
def fromList (l : List (Name.name × Term.term)) : substT := .Mk (Name.Map.fromList l)
def foldl (f : Name.name × Term.term × σ → σ) (b : σ) : substT → σ | .Mk m => Name.Map.foldl f b m
def foldr (f : Name.name × Term.term × σ → σ) (b : σ) : substT → σ | .Mk m => Name.Map.foldr f b m

/-- Normalizing removes identity substitutions. -/
def normalize (sub : substT) : substT :=
  match sub with
  | .Mk m =>
    let isNotId (vtm : Name.name × Term.term) := !(Term.equalVar vtm.1 vtm.2)
    let m' := Name.Map.filter isNotId m
    if Name.Map.size m = Name.Map.size m' then sub else .Mk m'

/-- Apply a (non-empty) substitution to a Term.term (helper `tmSub`). -/
partial def tmSub (sub : substT) : Term.term → Term.term
  | .Var v => match peek sub v with | some tm' => tm' | none => .Var v
  | .Fn f args => .Fn f (args.map (tmSub sub))

/-- Applying a substitution to a first order logic term.  (`subst sub tm`;
    no-op if `sub` is empty.) -/
def subst (sub : substT) (tm : Term.term) : Term.term :=
  if null sub then tm else tmSub sub tm

/-- Restricting a substitution to a given set of variables. -/
def restrict (sub : substT) (varSet : Name.Set.set) : substT :=
  match sub with
  | .Mk m =>
    let isRestrictedVar (vtm : Name.name × Term.term) := Name.Set.member vtm.1 varSet
    let m' := Name.Map.filter isRestrictedVar m
    if Name.Map.size m = Name.Map.size m' then sub else .Mk m'

def remove (sub : substT) (varSet : Name.Set.set) : substT :=
  match sub with
  | .Mk m =>
    let isRestrictedVar (vtm : Name.name × Term.term) := !(Name.Set.member vtm.1 varSet)
    let m' := Name.Map.filter isRestrictedVar m
    if Name.Map.size m = Name.Map.size m' then sub else .Mk m'

/-- Composing two substitutions so that the following identity holds:

    subst (compose sub1 sub2) tm = subst sub2 (subst sub1 tm) -/
def compose (sub1 sub2 : substT) : substT :=
  match sub1 with
  | .Mk m1 =>
    let f (vtms : Name.name × Term.term × substT) : substT :=
      let (v, tm, s) := vtms; insert s (v, subst sub2 tm)
    if null sub2 then sub1 else Name.Map.foldl f sub2 m1

/-- Creating the union of two compatible substitutions. -/
def union (s1 s2 : substT) : Except String substT :=
  match s1, s2 with
  | .Mk m1, .Mk m2 =>
    let compatible (p : (Name.name × Term.term) × (Name.name × Term.term)) : Option Term.term :=
      if Term.equal p.1.2 p.2.2 then some p.1.2 else none  -- OCaml fails on incompatible
    if Name.Map.null m1 then .ok s2
    else if Name.Map.null m2 then .ok s1
    else
      -- Detect incompatibility explicitly to mirror OCaml's failwith.
      let clash := (Name.Map.toList m1).any (fun (v, t1) =>
        match Name.Map.peek m2 v with | some t2 => !(Term.equal t1 t2) | none => false)
      if clash then .error "Substitute.union: incompatible"
      else .ok (.Mk (Name.Map.union compatible m1 m2))

/-- Substitutions can be inverted iff they are renaming substitutions.
    (Fails if non-injective / non-variable.) -/
def invert (sub : substT) : Except String substT :=
  match sub with
  | .Mk m =>
    let inv (s : Name.Map.map Term.term) (vt : Name.name × Term.term) :
        Except String (Name.Map.map Term.term) :=
      let (v, t) := vt
      match t with
      | .Var w =>
        if Name.Map.inDomain w s then .error "Substitute.invert: non-injective"
        else .ok (Name.Map.insert s (w, Term.term.Var v))
      | .Fn _ _ => .error "Substitute.invert: non-variable"
    (do
      let mut acc := Name.Map.newMap
      for vt in Name.Map.toList m do
        acc ← inv acc vt
      return .Mk acc)

def isRenaming (sub : substT) : Bool := HolCore.Lib.can (fun _ => invert sub) ()

/- Free variables / redexes / functions. -/

def redexes (sub : substT) : Name.Set.set :=
  foldl (fun (v, _, s) => Name.Set.add s v) Name.Set.empty sub

def residueFreeVars (sub : substT) : Name.Set.set :=
  foldl (fun (_, t, s) => Name.Set.union s (Term.freeVars t)) Name.Set.empty sub

def freeVars (sub : substT) : Name.Set.set :=
  foldl (fun (v, t, s) => Name.Set.union (Name.Set.add s v) (Term.freeVars t))
    Name.Set.empty sub

def functions (sub : substT) : Name_arity.Set.set :=
  foldl (fun (_, t, s) => Name_arity.Set.union s (Term.functions t))
    Name_arity.Set.empty sub

/-- Matching for first order logic terms.  (`matchList sub`: extend `sub` so
    `sub(tm1) = tm2`.) -/
partial def matchList (sub : substT) : List (Term.term × Term.term) → Except String substT
  | [] => .ok sub
  | (Term.term.Var v, tm) :: rest =>
    (do
      let sub' ← match peek sub v with
        | none => .ok (insert sub (v, tm))
        | some tm' => if Term.equal tm tm' then .ok sub
                      else .error "Substitute.match: incompatible matches"
      matchList sub' rest)
  | (Term.term.Fn f1 args1, Term.term.Fn f2 args2) :: rest =>
    if Name.equal f1 f2 && args1.length = args2.length then
      matchList sub (args1.zip args2 ++ rest)
    else .error "Substitute.match: different structure"
  | _ => .error "Substitute.match: functions can't match vars"
def matchTerms (sub : substT) (tm1 tm2 : Term.term) : Except String substT :=
  matchList sub [(tm1, tm2)]

/- Unification for first order logic terms. -/
mutual
partial def solve (sub : substT) : List (Term.term × Term.term) → Except String substT
  | [] => .ok sub
  | (tm1, tm2) :: rest =>
    if Term.equal tm1 tm2 then solve sub rest
    else solve' sub (subst sub tm1, subst sub tm2, rest)
partial def solve' (sub : substT) :
    Term.term × Term.term × List (Term.term × Term.term) → Except String substT
  | (Term.term.Var v, tm, rest) =>
    if Term.equalVar v tm then solve sub rest
    else if Term.freeIn v tm then .error "Substitute.unify: occurs check"
    else (match peek sub v with
          | none => solve (compose sub (singleton (v, tm))) rest
          | some tm' => solve' sub (tm', tm, rest))
  | (tm1, Term.term.Var v, rest) => solve' sub (Term.term.Var v, tm1, rest)
  | (Term.term.Fn f1 args1, Term.term.Fn f2 args2, rest) =>
    if Name.equal f1 f2 && args1.length = args2.length then
      solve sub (args1.zip args2 ++ rest)
    else .error "Substitute.unify: different structure"
end
def unify (sub : substT) (tm1 tm2 : Term.term) : Except String substT :=
  solve sub [(tm1, tm2)]

end Substitute

/- -- Atom: first-order logic atoms (`module Atom`) -------------------------
   A type for storing first order logic atoms. -/
namespace Atom

abbrev relationName := Name.name
abbrev relationT := relationName × Int
/-- An atom: relation name applied to argument terms. -/
abbrev atom := relationName × List Term.term

def name (atm : atom) : relationName := atm.1
def arguments (atm : atom) : List Term.term := atm.2
def arity (atm : atom) : Int := Int.ofNat (arguments atm).length
def relation (atm : atom) : relationName × Int := (name atm, arity atm)

def functions (atm : atom) : Name_arity.Set.set :=
  Mlist.foldl (fun (tm, acc) => Name_arity.Set.union (Term.functions tm) acc)
    Name_arity.Set.empty (arguments atm)

def functionNames (atm : atom) : Name.Set.set :=
  Mlist.foldl (fun (tm, acc) => Name.Set.union (Term.functionNames tm) acc)
    Name.Set.empty (arguments atm)

/- Binary relations -/

def mkBinop (p : Name.name) (ab : Term.term × Term.term) : atom := (p, [ab.1, ab.2])

def destBinop (p : Name.name) : atom → Except String (Term.term × Term.term)
  | (x, [a, b]) => if Name.equal x p then .ok (a, b) else .error "Atom.destBinop: wrong binop"
  | _ => .error "Atom.destBinop: not a binop"

def isBinop (p : Name.name) (atm : atom) : Bool := HolCore.Lib.can (destBinop p) atm

/- The size of an atom in symbols. -/

def symbols (atm : atom) : Int :=
  Mlist.foldl (fun (tm, z) => Term.symbols tm + z) 1 (arguments atm)

/- A total comparison function for atoms. -/

def compare : atom → atom → Int
  | (p1, tms1), (p2, tms2) =>
    let c := Name.compare p1 p2
    if c ≠ 0 then c else Useful.lexCompare Term.compare tms1 tms2

def equal (atm1 atm2 : atom) : Bool := compare atm1 atm2 = 0

/- Subterms. -/

def subterm (atm : atom) : Term.path → Except String Term.term
  | [] => .error "Atom.subterm: empty path"    -- OCaml raises Bug
  | h :: t =>
    let tms := atm.2
    if h ≥ Int.ofNat tms.length then .error "Atom.subterm: bad path"
    else Term.subterm (tms.getD h.toNat default) t

def subterms (atm : atom) : List (Term.path × Term.term) :=
  Mlist.foldl
    (fun (ntm, l) =>
      let (n, tm) := ntm
      (Term.subterms tm).map (fun (p, s) => (Int.ofNat n :: p, s)) ++ l)
    [] (Mlist.enumerate atm.2)

def replace (atm : atom) : Term.path × Term.term → Except String atom
  | ([], _) => .error "Atom.replace: empty path"  -- OCaml raises Bug
  | (h :: t, res) =>
    let (rel, tms) := atm
    if h ≥ Int.ofNat tms.length then .error "Atom.replace: bad path"
    else
      let tm := tms.getD h.toNat default
      let tm' := Term.replace tm (t, res)
      if Term.equal tm tm' then .ok atm  -- (OCaml uses physical eq; structural is safe)
      else do return (rel, ← Mlist.updateNth h.toNat tm' tms)

def find (pred : Term.term → Bool) (atm : atom) : Option Term.path :=
  let f (itm : Nat × Term.term) : Option Term.path :=
    match Term.find pred itm.2 with
    | some path => some (Int.ofNat itm.1 :: path)
    | none => none
  Mlist.first f (Mlist.enumerate atm.2)

/- Free variables. -/

def freeIn (v : Term.var) (atm : atom) : Bool := (arguments atm).any (Term.freeIn v)

def freeVars (atm : atom) : Name.Set.set :=
  Mlist.foldl (fun (tm, acc) => Name.Set.union (Term.freeVars tm) acc)
    Name.Set.empty (arguments atm)

/- Substitutions. -/

def subst (sub : Substitute.substT) (atm : atom) : atom :=
  let (p, tms) := atm
  (p, tms.map (Substitute.subst sub))

/- Matching / unification. -/

def matchAtoms (sub : Substitute.substT) : atom → atom → Except String Substitute.substT
  | (p1, tms1), (p2, tms2) => do
    if !(Name.equal p1 p2 && tms1.length = tms2.length) then .error "Atom.match"
    else
      let pairs ← HolCore.Lib.zip tms1 tms2
      let mut s := sub
      for (t1, t2) in pairs do
        s ← Substitute.matchTerms s t1 t2
      return s

def unify (sub : Substitute.substT) : atom → atom → Except String Substitute.substT
  | (p1, tms1), (p2, tms2) => do
    if !(Name.equal p1 p2 && tms1.length = tms2.length) then .error "Atom.unify"
    else
      let pairs ← HolCore.Lib.zip tms1 tms2
      let mut s := sub
      for (t1, t2) in pairs do
        s ← Substitute.unify s t1 t2
      return s

/- The equality relation. -/

def eqRelationName : Name.name := Name.fromString "="
def eqRelationArity : Int := 2
def eqRelation : Name.name × Int := (eqRelationName, eqRelationArity)

def mkEq (ab : Term.term × Term.term) : atom := mkBinop eqRelationName ab
def destEq (atm : atom) : Except String (Term.term × Term.term) := destBinop eqRelationName atm
def isEq (atm : atom) : Bool := isBinop eqRelationName atm

def mkRefl (tm : Term.term) : atom := mkEq (tm, tm)

def destRefl (atm : atom) : Except String Term.term := do
  let (l, r) := ← destEq atm
  if !(Term.equal l r) then .error "Atom.destRefl" else .ok l

def isRefl (atm : atom) : Bool := HolCore.Lib.can destRefl atm

def sym (atm : atom) : Except String atom := do
  let (l, r) := ← destEq atm
  if Term.equal l r then .error "Atom.sym: refl" else .ok (mkEq (r, l))

def lhs (atm : atom) : Except String Term.term := do return (← destEq atm).1
def rhs (atm : atom) : Except String Term.term := do return (← destEq atm).2

/- Terms with type annotations. -/

def typedSymbols (atm : atom) : Int :=
  Mlist.foldl (fun (tm, z) => Term.typedSymbols tm + z) 1 atm.2

def nonVarTypedSubterms (atm : atom) : List (Term.path × Term.term) :=
  let (_, tms) := atm
  let addArg (narg : Nat × Term.term) (acc : List (Term.path × Term.term)) :
      List (Term.path × Term.term) :=
    let (n, arg) := narg
    Mlist.foldl (fun (pt, acc) => (Int.ofNat n :: pt.1, pt.2) :: acc) acc
      (Term.nonVarTypedSubterms arg)
  Mlist.foldl (fun (na, acc) => addArg na acc) [] (Mlist.enumerate tms)

/-- Comparator to instantiate `Atom.Map`/`Atom.Set`. -/
def cmp : atom → atom → Int := compare

/- `Atom.Set` (used by `Thm.isTautology`): ordered set of atoms. -/
namespace Set
abbrev set := OrdSet.Set atom
def empty : set := OrdSet.empty cmp
def add (s : set) (x : atom) : set := OrdSet.add s x
def member (x : atom) (s : set) : Bool := OrdSet.member x s
end Set

end Atom

/- -- Formula: first-order logic formulas (`module Formula`) ----------------
   A type of first order logic formulas. -/
namespace Formula

/-- A first-order formula. -/
inductive formula where
  | True_
  | False_
  | Atom (a : Atom.atom)
  | Not (p : formula)
  | And (p q : formula)
  | Or (p q : formula)
  | Imp (p q : formula)
  | Iff (p q : formula)
  | Forall (v : Term.var) (p : formula)
  | Exists (v : Term.var) (p : formula)
  deriving Inhabited

/- Booleans -/

def mkBoolean : Bool → formula | true => .True_ | false => .False_
def destBoolean : formula → Except String Bool
  | .True_ => .ok true | .False_ => .ok false | _ => .error "destBoolean"
def isBoolean (fm : formula) : Bool := HolCore.Lib.can destBoolean fm
def isTrue : formula → Bool | .True_ => true | _ => false
def isFalse : formula → Bool | .False_ => true | _ => false

/- Functions / relations. -/

partial def functionsAux : Name_arity.Set.set → List formula → Name_arity.Set.set
  | fs, [] => fs
  | fs, .True_ :: fms => functionsAux fs fms
  | fs, .False_ :: fms => functionsAux fs fms
  | fs, .Atom atm :: fms => functionsAux (Name_arity.Set.union (Atom.functions atm) fs) fms
  | fs, .Not p :: fms => functionsAux fs (p :: fms)
  | fs, .And p q :: fms => functionsAux fs (p :: q :: fms)
  | fs, .Or p q :: fms => functionsAux fs (p :: q :: fms)
  | fs, .Imp p q :: fms => functionsAux fs (p :: q :: fms)
  | fs, .Iff p q :: fms => functionsAux fs (p :: q :: fms)
  | fs, .Forall _ p :: fms => functionsAux fs (p :: fms)
  | fs, .Exists _ p :: fms => functionsAux fs (p :: fms)
def functions (fm : formula) : Name_arity.Set.set := functionsAux Name_arity.Set.empty [fm]

partial def functionNamesAux : Name.Set.set → List formula → Name.Set.set
  | fs, [] => fs
  | fs, .True_ :: fms => functionNamesAux fs fms
  | fs, .False_ :: fms => functionNamesAux fs fms
  | fs, .Atom atm :: fms => functionNamesAux (Name.Set.union (Atom.functionNames atm) fs) fms
  | fs, .Not p :: fms => functionNamesAux fs (p :: fms)
  | fs, .And p q :: fms => functionNamesAux fs (p :: q :: fms)
  | fs, .Or p q :: fms => functionNamesAux fs (p :: q :: fms)
  | fs, .Imp p q :: fms => functionNamesAux fs (p :: q :: fms)
  | fs, .Iff p q :: fms => functionNamesAux fs (p :: q :: fms)
  | fs, .Forall _ p :: fms => functionNamesAux fs (p :: fms)
  | fs, .Exists _ p :: fms => functionNamesAux fs (p :: fms)
def functionNames (fm : formula) : Name.Set.set := functionNamesAux Name.Set.empty [fm]

partial def relationsAux : Name_arity.Set.set → List formula → Name_arity.Set.set
  | fs, [] => fs
  | fs, .True_ :: fms => relationsAux fs fms
  | fs, .False_ :: fms => relationsAux fs fms
  | fs, .Atom atm :: fms => relationsAux (Name_arity.Set.add fs (Atom.relation atm)) fms
  | fs, .Not p :: fms => relationsAux fs (p :: fms)
  | fs, .And p q :: fms => relationsAux fs (p :: q :: fms)
  | fs, .Or p q :: fms => relationsAux fs (p :: q :: fms)
  | fs, .Imp p q :: fms => relationsAux fs (p :: q :: fms)
  | fs, .Iff p q :: fms => relationsAux fs (p :: q :: fms)
  | fs, .Forall _ p :: fms => relationsAux fs (p :: fms)
  | fs, .Exists _ p :: fms => relationsAux fs (p :: fms)
def relations (fm : formula) : Name_arity.Set.set := relationsAux Name_arity.Set.empty [fm]

partial def relationNamesAux : Name.Set.set → List formula → Name.Set.set
  | fs, [] => fs
  | fs, .True_ :: fms => relationNamesAux fs fms
  | fs, .False_ :: fms => relationNamesAux fs fms
  | fs, .Atom atm :: fms => relationNamesAux (Name.Set.add fs (Atom.name atm)) fms
  | fs, .Not p :: fms => relationNamesAux fs (p :: fms)
  | fs, .And p q :: fms => relationNamesAux fs (p :: q :: fms)
  | fs, .Or p q :: fms => relationNamesAux fs (p :: q :: fms)
  | fs, .Imp p q :: fms => relationNamesAux fs (p :: q :: fms)
  | fs, .Iff p q :: fms => relationNamesAux fs (p :: q :: fms)
  | fs, .Forall _ p :: fms => relationNamesAux fs (p :: fms)
  | fs, .Exists _ p :: fms => relationNamesAux fs (p :: fms)
def relationNames (fm : formula) : Name.Set.set := relationNamesAux Name.Set.empty [fm]

/- Atoms / negations. -/

def destAtom : formula → Except String Atom.atom
  | .Atom atm => .ok atm | _ => .error "Formula.destAtom"
def isAtom (fm : formula) : Bool := HolCore.Lib.can destAtom fm

def destNeg : formula → Except String formula | .Not p => .ok p | _ => .error "Formula.destNeg"
def isNeg (fm : formula) : Bool := HolCore.Lib.can destNeg fm

partial def stripNegAux (n : Int) : formula → Int × formula
  | .Not fm => stripNegAux (n + 1) fm
  | fm => (n, fm)
def stripNeg (fm : formula) : Int × formula := stripNegAux 0 fm

/- Conjunctions. -/

def listMkConj (fms : List formula) : formula :=
  match fms.reverse with
  | [] => .True_
  | fm :: fms => Mlist.foldl (fun (x, y) => formula.And x y) fm fms

partial def stripConjAux (cs : List formula) : formula → List formula
  | .And p q => stripConjAux (p :: cs) q
  | fm => (fm :: cs).reverse
def stripConj : formula → List formula
  | .True_ => []
  | fm => stripConjAux [] fm

partial def flattenConjAux (acc : List formula) : List formula → List formula
  | [] => acc
  | .And p q :: fms => flattenConjAux acc (q :: p :: fms)
  | .True_ :: fms => flattenConjAux acc fms
  | fm :: fms => flattenConjAux (fm :: acc) fms
def flattenConj (fm : formula) : List formula := flattenConjAux [] [fm]

/- Disjunctions. -/

def listMkDisj (fms : List formula) : formula :=
  match fms.reverse with
  | [] => .False_
  | fm :: fms => Mlist.foldl (fun (x, y) => formula.Or x y) fm fms

partial def stripDisjAux (cs : List formula) : formula → List formula
  | .Or p q => stripDisjAux (p :: cs) q
  | fm => (fm :: cs).reverse
def stripDisj : formula → List formula
  | .False_ => []
  | fm => stripDisjAux [] fm

partial def flattenDisjAux (acc : List formula) : List formula → List formula
  | [] => acc
  | .Or p q :: fms => flattenDisjAux acc (q :: p :: fms)
  | .False_ :: fms => flattenDisjAux acc fms
  | fm :: fms => flattenDisjAux (fm :: acc) fms
def flattenDisj (fm : formula) : List formula := flattenDisjAux [] [fm]

/- Equivalences. -/

def listMkEquiv (fms : List formula) : formula :=
  match fms.reverse with
  | [] => .True_
  | fm :: fms => Mlist.foldl (fun (x, y) => formula.Iff x y) fm fms

partial def stripEquivAux (cs : List formula) : formula → List formula
  | .Iff p q => stripEquivAux (p :: cs) q
  | fm => (fm :: cs).reverse
def stripEquiv : formula → List formula
  | .True_ => []
  | fm => stripEquivAux [] fm

/- Universal quantifiers. -/

def destForall : formula → Except String (Term.var × formula)
  | .Forall v f => .ok (v, f) | _ => .error "destForall"
def isForall (fm : formula) : Bool := HolCore.Lib.can destForall fm

def listMkForall : List Term.var × formula → formula
  | ([], body) => body
  | (v :: vs, body) => .Forall v (listMkForall (vs, body))

def setMkForall (vs : Name.Set.set) (body : formula) : formula :=
  Name.Set.foldr (fun (x, y) => formula.Forall x y) body vs

partial def stripForallAux (vs : List Term.var) : formula → List Term.var × formula
  | .Forall v b => stripForallAux (v :: vs) b
  | tm => (vs.reverse, tm)
def stripForall (fm : formula) : List Term.var × formula := stripForallAux [] fm

/- Existential quantifiers. -/

def destExists : formula → Except String (Term.var × formula)
  | .Exists v f => .ok (v, f) | _ => .error "destExists"
def isExists (fm : formula) : Bool := HolCore.Lib.can destExists fm

def listMkExists : List Term.var × formula → formula
  | ([], body) => body
  | (v :: vs, body) => .Exists v (listMkExists (vs, body))

def setMkExists (vs : Name.Set.set) (body : formula) : formula :=
  Name.Set.foldr (fun (x, y) => formula.Exists x y) body vs

partial def stripExistsAux (vs : List Term.var) : formula → List Term.var × formula
  | .Exists v b => stripExistsAux (v :: vs) b
  | tm => (vs.reverse, tm)
def stripExists (fm : formula) : List Term.var × formula := stripExistsAux [] fm

/- The size of a formula in symbols. -/

partial def symbolsAux : Int → List formula → Int
  | n, [] => n
  | n, .True_ :: fms => symbolsAux (n + 1) fms
  | n, .False_ :: fms => symbolsAux (n + 1) fms
  | n, .Atom atm :: fms => symbolsAux (n + Atom.symbols atm) fms
  | n, .Not p :: fms => symbolsAux (n + 1) (p :: fms)
  | n, .And p q :: fms => symbolsAux (n + 1) (p :: q :: fms)
  | n, .Or p q :: fms => symbolsAux (n + 1) (p :: q :: fms)
  | n, .Imp p q :: fms => symbolsAux (n + 1) (p :: q :: fms)
  | n, .Iff p q :: fms => symbolsAux (n + 1) (p :: q :: fms)
  | n, .Forall _ p :: fms => symbolsAux (n + 1) (p :: fms)
  | n, .Exists _ p :: fms => symbolsAux (n + 1) (p :: fms)
def symbols (fm : formula) : Int := symbolsAux 0 [fm]

/- A total comparison function for formulas. -/

partial def compareAux : List (formula × formula) → Int
  | [] => 0
  | (f1, f2) :: fs =>
    match f1, f2 with
    | .True_, .True_ => compareAux fs
    | .True_, _ => -1
    | _, .True_ => 1
    | .False_, .False_ => compareAux fs
    | .False_, _ => -1
    | _, .False_ => 1
    | .Atom a1, .Atom a2 => let c := Atom.compare a1 a2; if c ≠ 0 then c else compareAux fs
    | .Atom _, _ => -1
    | _, .Atom _ => 1
    | .Not p1, .Not p2 => compareAux ((p1, p2) :: fs)
    | .Not _, _ => -1
    | _, .Not _ => 1
    | .And p1 q1, .And p2 q2 => compareAux ((p1, p2) :: (q1, q2) :: fs)
    | .And _ _, _ => -1
    | _, .And _ _ => 1
    | .Or p1 q1, .Or p2 q2 => compareAux ((p1, p2) :: (q1, q2) :: fs)
    | .Or _ _, _ => -1
    | _, .Or _ _ => 1
    | .Imp p1 q1, .Imp p2 q2 => compareAux ((p1, p2) :: (q1, q2) :: fs)
    | .Imp _ _, _ => -1
    | _, .Imp _ _ => 1
    | .Iff p1 q1, .Iff p2 q2 => compareAux ((p1, p2) :: (q1, q2) :: fs)
    | .Iff _ _, _ => -1
    | _, .Iff _ _ => 1
    | .Forall v1 p1, .Forall v2 p2 =>
      let c := Name.compare v1 v2; if c ≠ 0 then c else compareAux ((p1, p2) :: fs)
    | .Forall _ _, .Exists _ _ => -1
    | .Exists _ _, .Forall _ _ => 1
    | .Exists v1 p1, .Exists v2 p2 =>
      let c := Name.compare v1 v2; if c ≠ 0 then c else compareAux ((p1, p2) :: fs)
def compare (fm1 fm2 : formula) : Int := compareAux [(fm1, fm2)]
def equal (fm1 fm2 : formula) : Bool := compare fm1 fm2 = 0

/- Free variables. -/

partial def freeInAux (v : Term.var) : List formula → Bool
  | [] => false
  | .True_ :: fms => freeInAux v fms
  | .False_ :: fms => freeInAux v fms
  | .Atom atm :: fms => Atom.freeIn v atm || freeInAux v fms
  | .Not p :: fms => freeInAux v (p :: fms)
  | .And p q :: fms => freeInAux v (p :: q :: fms)
  | .Or p q :: fms => freeInAux v (p :: q :: fms)
  | .Imp p q :: fms => freeInAux v (p :: q :: fms)
  | .Iff p q :: fms => freeInAux v (p :: q :: fms)
  | .Forall w p :: fms => if Name.equal v w then freeInAux v fms else freeInAux v (p :: fms)
  | .Exists w p :: fms => if Name.equal v w then freeInAux v fms else freeInAux v (p :: fms)
def freeIn (v : Term.var) (fm : formula) : Bool := freeInAux v [fm]

/-- `add (fm,vs)`: accumulate free vars of `fm` into `vs`, tracking bound sets. -/
partial def fvAux (vs : Name.Set.set) : List (Name.Set.set × formula) → Name.Set.set
  | [] => vs
  | (_, .True_) :: fms => fvAux vs fms
  | (_, .False_) :: fms => fvAux vs fms
  | (bv, .Atom atm) :: fms =>
    fvAux (Name.Set.union vs (Name.Set.difference (Atom.freeVars atm) bv)) fms
  | (bv, .Not p) :: fms => fvAux vs ((bv, p) :: fms)
  | (bv, .And p q) :: fms => fvAux vs ((bv, p) :: (bv, q) :: fms)
  | (bv, .Or p q) :: fms => fvAux vs ((bv, p) :: (bv, q) :: fms)
  | (bv, .Imp p q) :: fms => fvAux vs ((bv, p) :: (bv, q) :: fms)
  | (bv, .Iff p q) :: fms => fvAux vs ((bv, p) :: (bv, q) :: fms)
  | (bv, .Forall v p) :: fms => fvAux vs ((Name.Set.add bv v, p) :: fms)
  | (bv, .Exists v p) :: fms => fvAux vs ((Name.Set.add bv v, p) :: fms)
def add (fm : formula) (vs : Name.Set.set) : Name.Set.set := fvAux vs [(Name.Set.empty, fm)]
def freeVars (fm : formula) : Name.Set.set := add fm Name.Set.empty
def freeVarsList (fms : List formula) : Name.Set.set :=
  Mlist.foldl (fun (fm, acc) => add fm acc) Name.Set.empty fms

def specialize (fm : formula) : formula := (stripForall fm).2
def generalize (fm : formula) : formula :=
  listMkForall (Name.Set.toList (freeVars fm), fm)

/- Substitutions. -/

mutual
partial def substCheck (sub : Substitute.substT) (fm : formula) : formula :=
  if Substitute.null sub then fm else substFm sub fm
partial def substFm (sub : Substitute.substT) (fm : formula) : formula :=
  match fm with
  | .True_ => fm
  | .False_ => fm
  | .Atom (p, tms) =>
    let tms' := tms.map (Substitute.subst sub)
    formula.Atom (p, tms')   -- (OCaml keeps identity on physical eq; harmless)
  | .Not p => let p' := substFm sub p; formula.Not p'
  | .And p q => substConn sub fm (fun (x, y) => formula.And x y) p q
  | .Or p q => substConn sub fm (fun (x, y) => formula.Or x y) p q
  | .Imp p q => substConn sub fm (fun (x, y) => formula.Imp x y) p q
  | .Iff p q => substConn sub fm (fun (x, y) => formula.Iff x y) p q
  | .Forall v p => substQuant sub fm (fun (x, y) => formula.Forall x y) v p
  | .Exists v p => substQuant sub fm (fun (x, y) => formula.Exists x y) v p
partial def substConn (sub : Substitute.substT) (_fm : formula)
    (conn : formula × formula → formula) (p q : formula) : formula :=
  conn (substFm sub p, substFm sub q)
partial def substQuant (sub : Substitute.substT) (_fm : formula)
    (quant : Term.var × formula → formula) (v : Term.var) (p : formula) : formula :=
  let v' :=
    let f (ws : Name.name × Name.Set.set) : Name.Set.set :=
      let (w, s) := ws
      if Name.equal w v then s
      else match Substitute.peek sub w with
           | none => Name.Set.add s w
           | some tm => Name.Set.union s (Term.freeVars tm)
    let vars := freeVars p
    let vars := Name.Set.foldl f Name.Set.empty vars
    Term.variantPrime vars v
  let sub :=
    if Name.equal v v' then Substitute.remove sub (Name.Set.singleton v)
    else Substitute.insert sub (v, Term.term.Var v')
  let p' := substCheck sub p
  quant (v', p')
end
def subst (sub : Substitute.substT) (fm : formula) : formula := substCheck sub fm

/- The equality relation. -/

def mkEq (ab : Term.term × Term.term) : formula := .Atom (Atom.mkEq ab)
def destEq (fm : formula) : Except String (Term.term × Term.term) := do Atom.destEq (← destAtom fm)
def isEq (fm : formula) : Bool := HolCore.Lib.can destEq fm
def mkNeq (ab : Term.term × Term.term) : formula := .Not (mkEq ab)
def destNeq : formula → Except String (Term.term × Term.term)
  | .Not fm => destEq fm | _ => .error "Formula.destNeq"
def isNeq (fm : formula) : Bool := HolCore.Lib.can destNeq fm
def mkRefl (tm : Term.term) : formula := .Atom (Atom.mkRefl tm)
def destRefl (fm : formula) : Except String Term.term := do Atom.destRefl (← destAtom fm)
def isRefl (fm : formula) : Bool := HolCore.Lib.can destRefl fm
def sym (fm : formula) : Except String formula := do return .Atom (← Atom.sym (← destAtom fm))
def lhs (fm : formula) : Except String Term.term := do return (← destEq fm).1
def rhs (fm : formula) : Except String Term.term := do return (← destEq fm).2

/- Splitting goals. -/

def add_asms (asms : List formula) (goal : formula) : formula :=
  if Mlist.null asms then goal else .Imp (listMkConj asms.reverse) goal

def add_var_asms (asms : List formula) (v : Term.var) (goal : formula) : formula :=
  add_asms asms (.Forall v goal)

partial def split (asms : List formula) (pol : Bool) (fm : formula) : List formula :=
  match pol, fm with
  -- Positive splittables
  | true, .True_ => []
  | true, .Not f => split asms false f
  | true, .And f1 f2 => split asms true f1 ++ split (f1 :: asms) true f2
  | true, .Or f1 f2 => split (.Not f1 :: asms) true f2
  | true, .Imp f1 f2 => split (f1 :: asms) true f2
  | true, .Iff f1 f2 => split (f1 :: asms) true f2 ++ split (f2 :: asms) true f1
  | true, .Forall v f => (split [] true f).map (add_var_asms asms v)
  -- Negative splittables
  | false, .False_ => []
  | false, .Not f => split asms true f
  | false, .And f1 f2 => split (f1 :: asms) false f2
  | false, .Or f1 f2 => split asms false f1 ++ split (.Not f1 :: asms) false f2
  | false, .Imp f1 f2 => split asms true f1 ++ split (f1 :: asms) false f2
  | false, .Iff f1 f2 => split (f1 :: asms) false f2 ++ split (.Not f2 :: asms) true f1
  | false, .Exists v f => (split [] false f).map (add_var_asms asms v)
  -- Unsplittables
  | _, _ => [add_asms asms (if pol then fm else .Not fm)]

def splitGoal (fm : formula) : List formula := split [] true fm

/-- Simple pretty-printer (`demote`/`toString`).  Used only in error/trace
    messages in OCaml; kept faithful enough for those. -/
partial def demote : formula → Term.term
  | .True_ => .Fn (Name.fromString "T") []
  | .False_ => .Fn (Name.fromString "F") []
  | .Atom (p, tms) => .Fn p tms
  | .Not p => .Fn (Name.fromString "~") [demote p]
  | .And p q => .Fn (Name.fromString "/\\") [demote p, demote q]
  | .Or p q => .Fn (Name.fromString "\\/") [demote p, demote q]
  | .Imp p q => .Fn (Name.fromString "==>") [demote p, demote q]
  | .Iff p q => .Fn (Name.fromString "<=>") [demote p, demote q]
  | .Forall v b => .Fn (Name.fromString "!") [.Var v, demote b]
  | .Exists v b => .Fn (Name.fromString "?") [.Var v, demote b]
def toString (fm : formula) : String := Term.toString (demote fm)

/-- Comparator to instantiate `Formula.Map`/`Formula.Set`. -/
def cmp : formula → formula → Int := compare

end Formula

/- -- Literal: first-order logic literals (`module Literal`) ----------------
   A type for storing first order logic literals. -/
namespace Literal

abbrev polarityT := Bool
/-- A literal: polarity + atom. -/
abbrev literal := polarityT × Atom.atom

def polarity (lit : literal) : polarityT := lit.1
def atom (lit : literal) : Atom.atom := lit.2
def name (lit : literal) : Name.name := Atom.name (atom lit)
def arguments (lit : literal) : List Term.term := Atom.arguments (atom lit)
def arity (lit : literal) : Int := Atom.arity (atom lit)
def positive (lit : literal) : Bool := polarity lit
def negative (lit : literal) : Bool := !(polarity lit)
def negate (lit : literal) : literal := (!lit.1, lit.2)
def relation (lit : literal) : Name.name × Int := Atom.relation (atom lit)
def functions (lit : literal) : Name_arity.Set.set := Atom.functions (atom lit)
def functionNames (lit : literal) : Name.Set.set := Atom.functionNames (atom lit)

/- Binary relations -/

def mkBinop (rel : Name.name) (pab : polarityT × Term.term × Term.term) : literal :=
  (pab.1, Atom.mkBinop rel (pab.2.1, pab.2.2))

def destBinop (rel : Name.name) (lit : literal) : Except String (polarityT × Term.term × Term.term) :=
  do let (a, b) := ← Atom.destBinop rel lit.2; return (lit.1, a, b)

def isBinop (rel : Name.name) (lit : literal) : Bool := HolCore.Lib.can (destBinop rel) lit

/- Formulas. -/

def toFormula : literal → Formula.formula
  | (true, atm) => .Atom atm
  | (false, atm) => .Not (.Atom atm)

def fromFormula : Formula.formula → Except String literal
  | .Atom atm => .ok (true, atm)
  | .Not (.Atom atm) => .ok (false, atm)
  | _ => .error "Literal.fromFormula"

/- The size of a literal in symbols. -/

def symbols (lit : literal) : Int := Atom.symbols lit.2
/- A total comparison function for literals. -/
def compare : literal → literal → Int := Useful.prodCompare Useful.boolCompare Atom.compare
def equal (l1 l2 : literal) : Bool := l1.1 = l2.1 && Atom.equal l1.2 l2.2

/- Subterms. -/

def subterm (lit : literal) (path : Term.path) : Except String Term.term :=
  Atom.subterm (atom lit) path
def subterms (lit : literal) : List (Term.path × Term.term) := Atom.subterms (atom lit)
def replace (lit : literal) (path_tm : Term.path × Term.term) : Except String literal :=
  do let atm' := ← Atom.replace lit.2 path_tm; return (lit.1, atm')

/- Free variables. -/

def freeIn (v : Term.var) (lit : literal) : Bool := Atom.freeIn v (atom lit)
def freeVars (lit : literal) : Name.Set.set := Atom.freeVars (atom lit)

/- Substitutions. -/

def subst (sub : Substitute.substT) (lit : literal) : literal := (lit.1, Atom.subst sub lit.2)

/- Matching / unification. -/

def matchLiterals (sub : Substitute.substT) (l1 l2 : literal) : Except String Substitute.substT :=
  if l1.1 = l2.1 then Atom.matchAtoms sub l1.2 l2.2 else .error "Literal.match"

def unify (sub : Substitute.substT) (l1 l2 : literal) : Except String Substitute.substT :=
  if l1.1 = l2.1 then Atom.unify sub l1.2 l2.2 else .error "Literal.unify"

/- The equality relation. -/

def mkEq (lr : Term.term × Term.term) : literal := (true, Atom.mkEq lr)
def destEq : literal → Except String (Term.term × Term.term)
  | (true, atm) => Atom.destEq atm | (false, _) => .error "Literal.destEq"
def isEq (lit : literal) : Bool := HolCore.Lib.can destEq lit
def mkNeq (lr : Term.term × Term.term) : literal := (false, Atom.mkEq lr)
def destNeq : literal → Except String (Term.term × Term.term)
  | (false, atm) => Atom.destEq atm | (true, _) => .error "Literal.destNeq"
def isNeq (lit : literal) : Bool := HolCore.Lib.can destNeq lit
def mkRefl (tm : Term.term) : literal := (true, Atom.mkRefl tm)
def destRefl : literal → Except String Term.term
  | (true, atm) => Atom.destRefl atm | (false, _) => .error "Literal.destRefl"
def isRefl (lit : literal) : Bool := HolCore.Lib.can destRefl lit
def mkIrrefl (tm : Term.term) : literal := (false, Atom.mkRefl tm)
def destIrrefl : literal → Except String Term.term
  | (true, _) => .error "Literal.destIrrefl" | (false, atm) => Atom.destRefl atm
def isIrrefl (lit : literal) : Bool := HolCore.Lib.can destIrrefl lit
def sym (lit : literal) : Except String literal := do return (lit.1, ← Atom.sym lit.2)
def lhs (lit : literal) : Except String Term.term := Atom.lhs lit.2
def rhs (lit : literal) : Except String Term.term := Atom.rhs lit.2

/- Terms with type annotations. -/

def typedSymbols (lit : literal) : Int := Atom.typedSymbols lit.2
def nonVarTypedSubterms (lit : literal) : List (Term.path × Term.term) :=
  Atom.nonVarTypedSubterms lit.2

/- Parsing and pretty-printing. -/

def toString (lit : literal) : String := Formula.toString (toFormula lit)

/-- Comparator to instantiate `Literal.Map`/`Literal.Set`. -/
def cmp : literal → literal → Int := compare

/- `Literal.Set`: ordered set of literals with derived operations. -/
namespace Set
abbrev set := OrdSet.Set literal
def empty : set := OrdSet.empty cmp
def add (s : set) (x : literal) : set := OrdSet.add s x
def singleton (x : literal) : set := OrdSet.singleton cmp x
def member (x : literal) (s : set) : Bool := OrdSet.member x s
def delete (s : set) (x : literal) : set := OrdSet.delete s x
def null (s : set) : Bool := OrdSet.null s
def size (s : set) : Nat := OrdSet.size s
def toList (s : set) : List literal := OrdSet.toList s
def fromList (l : List literal) : set := OrdSet.fromList cmp l
def foldl (f : literal × σ → σ) (a : σ) (s : set) : σ := OrdSet.foldl f a s
def foldr (f : literal × σ → σ) (a : σ) (s : set) : σ := OrdSet.foldr f a s
def union (s1 s2 : set) : set := OrdSet.union s1 s2
def difference (s1 s2 : set) : set := OrdSet.difference s1 s2
def intersect (s1 s2 : set) : set := OrdSet.intersect s1 s2
def intersectList (l : List set) : set := OrdSet.intersectList l
def subset (s1 s2 : set) : Bool := OrdSet.subset s1 s2
def equal (s1 s2 : set) : Bool := OrdSet.equal s1 s2
def compareS (s1 s2 : set) : Int := OrdSet.compareSet s1 s2
def pick (s : set) : Except String literal := OrdSet.pick s
def existsb (p : literal → Bool) (s : set) : Bool := OrdSet.existsb p s
def all (p : literal → Bool) (s : set) : Bool := OrdSet.all p s
def findl (p : literal → Bool) (s : set) : Option literal := OrdSet.findl p s
def firstl (f : literal → Option β) (s : set) : Option β := OrdSet.firstl f s

def negateMember (lit : literal) (s : set) : Bool := member (negate lit) s

/-- `Literal.Set.negate`: negate every literal (shadows `Literal.negate`). -/
def negate (s : set) : set :=
  foldl (fun (lit, acc) => add acc (Literal.negate lit)) empty s

def relations (s : set) : Name_arity.Set.set :=
  foldl (fun (lit, acc) => Name_arity.Set.add acc (Literal.relation lit)) Name_arity.Set.empty s

def functions (s : set) : Name_arity.Set.set :=
  foldl (fun (lit, acc) => Name_arity.Set.union acc (Literal.functions lit)) Name_arity.Set.empty s

def freeIn (v : Term.var) (s : set) : Bool := existsb (Literal.freeIn v) s

def freeVars (s : set) : Name.Set.set :=
  foldl (fun (lit, acc) => Name.Set.union acc (Literal.freeVars lit)) Name.Set.empty s

def freeVarsList (l : List set) : Name.Set.set :=
  Mlist.foldl (fun (lits, acc) => Name.Set.union acc (freeVars lits)) Name.Set.empty l

def symbols (s : set) : Int := foldl (fun (lit, z) => Literal.symbols lit + z) 0 s
def typedSymbols (s : set) : Int := foldl (fun (lit, z) => Literal.typedSymbols lit + z) 0 s

/-- `subst sub lits` with OCaml's identity test (metis.ml 3696-3705): the
    flag is `true` when the result is PHYSICALLY the input set.  OCaml's
    `lit == lit'` holds only when `Literal.subst` returned its argument, and
    `Atom.subst` (metis.ml 2812) rebuilds the atom whenever its argument list
    is non-empty (`List.map` always allocates), whatever `sub` is.  So the set
    is kept exactly when every literal's atom has no arguments.  The flag
    decides whether `Thm.subst` records a `Subst` inference, which shapes the
    proof that METIS reconstructs (and prints under `metisverb`). -/
def substPhys (sub : Substitute.substT) (lits : set) : Bool × set :=
  let substLit (arg : literal × (Bool × set)) : Bool × set :=
    let (lit, (eq, lits')) := arg
    let lit' := Literal.subst sub lit
    let eq := eq && lit.2.2.isEmpty
    (eq, add lits' lit')
  let (eq, lits') := foldl substLit (true, empty) lits
  if eq then (true, lits) else (false, lits')

/-- `subst sub lits`: apply `sub` to every literal. -/
def subst (sub : Substitute.substT) (lits : set) : set := (substPhys sub lits).2

def conjoin (s : set) : Formula.formula :=
  Formula.listMkConj ((toList s).map Literal.toFormula)
def disjoin (s : set) : Formula.formula :=
  Formula.listMkDisj ((toList s).map Literal.toFormula)

def toString (cl : set) : String :=
  "{" ++ String.intercalate ", " ((toList cl).map Literal.toString) ++ "}"

def cmpSet : set → set → Int := compareS
end Set

/- `Literal.Map`: ordered map keyed by literals (used by Rewrite.neqConvs). -/
namespace Map
abbrev map (α : Type) := OrdMap.Map literal α
def newMap : map α := OrdMap.newMap cmp
def null (m : map α) : Bool := OrdMap.null m
def insert (m : map α) (kv : literal × α) : map α := OrdMap.insert m kv
def delete (m : map α) (k : literal) : map α := OrdMap.delete m k
def foldl (f : literal × α × σ → σ) (b : σ) (m : map α) : σ := OrdMap.foldl f b m
def foldr (f : literal × α × σ → σ) (b : σ) (m : map α) : σ := OrdMap.foldr f b m
end Map

/- `Literal.Set_map`: ordered map keyed by literal-sets (used by Proof.proof). -/
namespace Set_map
abbrev map (α : Type) := OrdMap.Map Set.set α
def newMap : map α := OrdMap.newMap Set.compareS
def size (m : map α) : Nat := OrdMap.size m
def peek (m : map α) (k : Set.set) : Option α := OrdMap.peek m k
def insert (m : map α) (kv : Set.set × α) : map α := OrdMap.insert m kv
def delete (m : map α) (k : Set.set) : map α := OrdMap.delete m k
def inDomain (k : Set.set) (m : map α) : Bool := OrdMap.inDomain k m
end Set_map

end Literal

/- ---------------------------------------------------------------------- -/
/- A LOGICAL KERNEL FOR FIRST ORDER CLAUSAL THEOREMS                       -/
/- ---------------------------------------------------------------------- -/

/- -- Thm (`module Thm`) ----------------------------------------------------
   An abstract type of first order logic theorems. -/
namespace Thm

abbrev clause := Literal.Set.set

inductive inferenceType where
  | Axiom | Assume | Subst | Factor | Resolve | Refl | Equality
  deriving Inhabited, BEq

/-- A first-order clausal theorem: a clause plus its derivation. -/
inductive thm where
  | Thm (cl : clause) (inf : inferenceType × List thm)

abbrev inferenceT := inferenceType × List thm

instance : Inhabited thm := ⟨.Thm Literal.Set.empty (.Axiom, [])⟩

/- Theorem destructors. -/
def clause_ : thm → clause | .Thm cl _ => cl
def inference : thm → inferenceT | .Thm _ inf => inf

/- Tautologies. -/

def isTautology (th : thm) : Bool :=
  let chk (arg : Literal.literal × Option Atom.Set.set) : Option Atom.Set.set :=
    match arg.2 with
    | none => none
    | some set =>
      let pol := arg.1.1
      let atm := arg.1.2
      if (pol && Atom.isRefl atm) || Atom.Set.member atm set then none
      else some (Atom.Set.add set atm)
  match Literal.Set.foldl chk (some Atom.Set.empty) (clause_ th) with
  | some _ => false
  | none => true

/- Contradictions / unit / literals. -/

def isContradiction (th : thm) : Bool := Literal.Set.null (clause_ th)

def destUnit : thm → Except String Literal.literal
  | .Thm cl _ => if Literal.Set.size cl = 1 then Literal.Set.pick cl else .error "Thm.destUnit"
def isUnit (th : thm) : Bool := HolCore.Lib.can destUnit th

/- Unit equality theorems -/
def destUnitEq (th : thm) : Except String (Term.term × Term.term) := do Literal.destEq (← destUnit th)
def isUnitEq (th : thm) : Bool := HolCore.Lib.can destUnitEq th

def member (lit : Literal.literal) : thm → Bool | .Thm cl _ => Literal.Set.member lit cl
def negateMember (lit : Literal.literal) : thm → Bool | .Thm cl _ => Literal.Set.negateMember lit cl

/- A total order. -/

def compare (th1 th2 : thm) : Int := Literal.Set.compareS (clause_ th1) (clause_ th2)
def equal (th1 th2 : thm) : Bool := Literal.Set.equal (clause_ th1) (clause_ th2)
def freeIn (v : Term.var) : thm → Bool | .Thm cl _ => Literal.Set.freeIn v cl
def freeVars : thm → Name.Set.set | .Thm cl _ => Literal.Set.freeVars cl

/- Pretty-printing (debug). -/

def inferenceTypeToString : inferenceType → String
  | .Axiom => "axiom" | .Assume => "assume" | .Subst => "subst" | .Factor => "factor"
  | .Resolve => "resolve" | .Refl => "refl" | .Equality => "equality"

def toString : thm → String
  | .Thm cl (infType, _) => inferenceTypeToString infType ++ ": " ++ Literal.Set.toString cl

/- Primitive rules of inference. -/

/-- `axiom C ⊢ C`.  (`axiom` is a Lean keyword; escaped as `«axiom»`.) -/
def «axiom» (cl : clause) : thm := .Thm cl (.Axiom, [])

/-- `assume L ⊢ L ∨ ¬L`. -/
def assume (lit : Literal.literal) : thm :=
  .Thm (Literal.Set.fromList [lit, Literal.negate lit]) (.Assume, [])

/-- `subst s`: apply substitution `s` to the clause. -/
def subst (sub : Substitute.substT) (th : thm) : thm :=
  match th with
  | .Thm cl inf =>
    -- `cl == cl'` (metis.ml 3884): physical identity, see `substPhys`.
    let (same, cl') := Literal.Set.substPhys sub cl
    if same then th
    else match inf with
         | (.Subst, _) => .Thm cl' inf
         | _ => .Thm cl' (.Subst, [th])

/-- `resolve L (L∨C) (¬L∨D) ⊢ C∨D`.  The literal L must occur in the first
    theorem, and the literal ~L must occur in the second theorem. -/
def resolve (lit : Literal.literal) (th1 th2 : thm) : thm :=
  match th1, th2 with
  | .Thm cl1 _, .Thm cl2 _ =>
    let cl1' := Literal.Set.delete cl1 lit
    let cl2' := Literal.Set.delete cl2 (Literal.negate lit)
    .Thm (Literal.Set.union cl1' cl2') (.Resolve, [th1, th2])

/-- `refl t ⊢ t = t`. -/
def refl (tm : Term.term) : thm :=
  .Thm (Literal.Set.singleton (true, Atom.mkRefl tm)) (.Refl, [])

/-- `equality L p t`: `¬(s=t) ∨ ¬L ∨ L'`, where s is the subterm of L at path p,
    and L' is L with the subterm at path p being replaced by t. -/
def equality (lit : Literal.literal) (path : Term.path) (t : Term.term) : Except String thm := do
  let s ← Literal.subterm lit path
  let lit' ← Literal.replace lit (path, t)
  let eqLit := Literal.mkNeq (s, t)
  let cl := Literal.Set.fromList [eqLit, Literal.negate lit, lit']
  return .Thm cl (.Equality, [])

end Thm

/- -- Proof: proofs in first order logic (`module Proof`) -------------------
   A type of first order logic proofs. -/
namespace Proof

/-- A single reconstructed inference. -/
inductive inference where
  | Axiom (s : Literal.Set.set)
  | Assume (atm : Atom.atom)
  | Subst (sub : Substitute.substT) (th : Thm.thm)
  | Resolve (atm : Atom.atom) (th th' : Thm.thm)
  | Refl (tm : Term.term)
  | Equality (lit : Literal.literal) (path : Term.path) (tm : Term.term)

abbrev proofT := List (Thm.thm × inference)

def parents : inference → List Thm.thm
  | .Axiom _ => [] | .Assume _ => [] | .Subst _ th => [th]
  | .Resolve _ th th' => [th, th'] | .Refl _ => [] | .Equality _ _ _ => []

/- Reconstructing single inferences. -/

def inferenceToThm : inference → Except String Thm.thm
  | .Axiom cl => .ok (Thm.«axiom» cl)
  | .Assume atm => .ok (Thm.assume (true, atm))
  | .Subst sub th => .ok (Thm.subst sub th)
  | .Resolve atm th th' => .ok (Thm.resolve (true, atm) th th')
  | .Refl tm => .ok (Thm.refl tm)
  | .Equality lit path r => Thm.equality lit path r

/-- Reconstruct the substitution taking `cl` to `cl'`. -/
partial def reconstructSubstRecon (cl cl' : Thm.clause) :
    List (List Literal.literal × Substitute.substT) → Except String Substitute.substT
  | [] => .error "can't reconstruct Subst rule"
  | ([], sub) :: others =>
    if Literal.Set.equal (Literal.Set.subst sub cl) cl' then .ok sub
    else reconstructSubstRecon cl cl' others
  | (lit :: lits, sub) :: others =>
    let checkLit (arg : Literal.literal × List (List Literal.literal × Substitute.substT)) :
        List (List Literal.literal × Substitute.substT) :=
      let lit' := arg.1
      let acc := arg.2
      match Useful.total (fun l => Literal.matchLiterals sub lit l) lit' with
      | none => acc
      | some sub => (lits, sub) :: acc
    reconstructSubstRecon cl cl' (Literal.Set.foldl checkLit others cl')

def reconstructSubst (cl cl' : Thm.clause) : Except String Substitute.substT := do
  return Substitute.normalize
    (← reconstructSubstRecon cl cl' [(Literal.Set.toList cl, Substitute.empty)])

def reconstructResolvant (cl1 cl2 cl : Thm.clause) : Except String Literal.literal :=
  if !(Literal.Set.subset cl1 cl) then Literal.Set.pick (Literal.Set.difference cl1 cl)
  else if !(Literal.Set.subset cl2 cl) then
    do return Literal.negate (← Literal.Set.pick (Literal.Set.difference cl2 cl))
  else
    -- A useless resolution, but we must reconstruct it anyway
    let cl1' := Literal.Set.negate cl1
    let cl2' := Literal.Set.negate cl2
    let lits := Literal.Set.intersectList [cl1, cl1', cl2, cl2']
    if !(Literal.Set.null lits) then Literal.Set.pick lits
    else .error "can't reconstruct Resolve rule"

/-- `sync s t path atm atm'`: find the single differing argument position path. -/
partial def reconstructEqualitySync (s t : Term.term) (path : Term.path)
    (fa fa' : Name.name × List Term.term) : Option Term.path :=
  let (f, a) := fa
  let (f', a') := fa'
  if !(Name.equal f f' && a.length = a'.length) then none
  else
    let itms := Mlist.enumerate (a.zip a')
    match itms.filter (fun x => !(Term.equal x.2.1 x.2.2)) with
    | [(i, (tm, tm'))] =>
      let path := Int.ofNat i :: path
      if Term.equal tm s && Term.equal tm' t then some path.reverse
      else match tm, tm' with
           | .Fn ff aa, .Fn ff' aa' => reconstructEqualitySync s t path (ff, aa) (ff', aa')
           | _, _ => none
    | _ => none

def reconstructEqualityRecon
    (arg : Literal.literal × Literal.literal × Literal.literal) :
    Option (Literal.literal × Term.path × Term.term) :=
  let (neq, lp, lp') := arg
  let (pol, atm) := lp
  let (pol', atm') := lp'
  if pol = pol' then none
  else match Literal.destNeq neq with
       | .error _ => none
       | .ok (s, t) =>
         let path :=
           if !(Term.equal s t) then reconstructEqualitySync s t [] atm atm'
           else if !(Atom.equal atm atm') then none
           else Atom.find (Term.equal s) atm
         match path with
         | some path => some ((pol', atm), path, t)
         | none => none

def reconstructEquality (cl : Thm.clause) :
    Except String (Literal.literal × Term.path × Term.term) := do
  let candidates ←
    match (Literal.Set.toList cl).partition Literal.isNeq with
    | ([l1], [l2, l3]) => Except.ok [(l1, l2, l3), (l1, l3, l2)]
    | ([l1, l2], [l3]) => Except.ok [(l1, l2, l3), (l1, l3, l2), (l2, l1, l3), (l2, l3, l1)]
    | ([l1], [l2]) => Except.ok [(l1, l1, l2), (l1, l2, l1)]
    | _ => Except.error "reconstructEquality: malformed"
  match Mlist.first reconstructEqualityRecon candidates with
  | some info => .ok info
  | none => .error "can't reconstruct Equality rule"

def reconstruct (cl : Thm.clause) : Thm.inferenceT → Except String inference
  | (.Axiom, []) => .ok (.Axiom cl)
  | (.Assume, []) =>
    match Literal.Set.findl Literal.positive cl with
    | some (_, atm) => .ok (.Assume atm)
    | none => .error "malformed Assume inference"
  | (.Subst, [th]) => do return .Subst (← reconstructSubst (Thm.clause_ th) cl) th
  | (.Resolve, [th1, th2]) => do
    let cl1 := Thm.clause_ th1
    let cl2 := Thm.clause_ th2
    let (pol, atm) ← reconstructResolvant cl1 cl2 cl
    return (if pol then .Resolve atm th1 th2 else .Resolve atm th2 th1)
  | (.Refl, []) =>
    match Literal.Set.findl (fun _ => true) cl with
    | some lit => do return .Refl (← Literal.destRefl lit)
    | none => .error "malformed Refl inference"
  | (.Equality, []) => do let (x, y, z) ← reconstructEquality cl; return .Equality x y z
  | _ => .error "malformed inference"

def thmToInference (th : Thm.thm) : Except String inference :=
  reconstruct (Thm.clause_ th) (Thm.inference th)

/- Reconstructing whole proofs. -/

partial def addThms (arg : Thm.thm × Literal.Set_map.map Thm.thm) :
    Literal.Set_map.map Thm.thm :=
  let (th, ths) := arg
  let cl := Thm.clause_ th
  if Literal.Set_map.inDomain cl ths then ths
  else
    let (_, pars) := Thm.inference th
    let ths := Mlist.foldl addThms ths pars
    if Literal.Set_map.inDomain cl ths then ths
    else Literal.Set_map.insert ths (cl, th)

def mkThms (th : Thm.thm) : Literal.Set_map.map Thm.thm :=
  addThms (th, Literal.Set_map.newMap)

partial def addProof
    (arg : Thm.thm × (Literal.Set_map.map Thm.thm × List (Thm.thm × inference))) :
    Except String (Literal.Set_map.map Thm.thm × List (Thm.thm × inference)) := do
  let (th, (ths, acc)) := arg
  let cl := Thm.clause_ th
  match Literal.Set_map.peek ths cl with
  | none => return (ths, acc)
  | some th =>
    let (_, pars) := Thm.inference th
    let mut curThs := ths
    let mut curAcc := acc
    for par in pars do
      let (ths', acc') ← addProof (par, (curThs, curAcc))
      curThs := ths'; curAcc := acc'
    let finalThs := Literal.Set_map.delete curThs cl
    let inf ← thmToInference th
    return (finalThs, (th, inf) :: curAcc)

def proof (th : Thm.thm) : Except String proofT := do
  let ths := mkThms th
  let (_, acc) ← addProof (th, (ths, []))
  return acc.reverse

/- Free variables. -/

def freeIn (v : Term.var) (prf : proofT) : Bool :=
  let free (th_inf : Thm.thm × inference) : Bool :=
    match th_inf.2 with
    | .Axiom lits => Literal.Set.freeIn v lits
    | .Assume atm => Atom.freeIn v atm
    | .Subst _ _ => Thm.freeIn v th_inf.1
    | .Resolve _ _ _ => false
    | .Refl tm => Term.freeIn v tm
    | .Equality lit _ tm => Literal.freeIn v lit || Term.freeIn v tm
  prf.any free

def freeVars (prf : proofT) : Name.Set.set :=
  let inc (arg : (Thm.thm × inference) × Name.Set.set) : Name.Set.set :=
    let th_inf := arg.1
    let set := arg.2
    Name.Set.union set
      (match th_inf.2 with
       | .Axiom lits => Literal.Set.freeVars lits
       | .Assume atm => Atom.freeVars atm
       | .Subst _ _ => Thm.freeVars th_inf.1
       | .Resolve _ _ _ => Name.Set.empty
       | .Refl tm => Term.freeVars tm
       | .Equality lit _ tm => Name.Set.union (Literal.freeVars lit) (Term.freeVars tm))
  Mlist.foldl inc Name.Set.empty prf

end Proof

/- -- Fresh-variable generation (impure) ------------------------------------
   OCaml threads a global `Useful.generator` ref.  We model it as an explicit
   `IO.Ref Int` supplied by `Session.lean`, so the pure prover stays pure and
   only the genuinely stateful search functions become `IO`.  These mirror
   `Name.newName`/`newNames`, `Term.newVar`/`newVars`, `Substitute.freshVars`. -/
namespace Gen

/-- `newInt gen`: read-and-increment the generator (OCaml `Useful.newInt`). -/
def newInt (gen : IO.Ref Int) : IO Int := do
  let n ← gen.get; gen.set (n + 1); return n

/-- `newInts gen k`: `k` fresh consecutive integers (OCaml `Useful.newInts`). -/
def newInts (gen : IO.Ref Int) (k : Int) : IO (List Int) := do
  if k ≤ 0 then return []
  else
    let n ← gen.get; gen.set (n + k); return Useful.interval n k.toNat

def newName (gen : IO.Ref Int) : IO Name.name := do return Name.numName (← newInt gen)
def newNames (gen : IO.Ref Int) (n : Int) : IO (List Name.name) := do
  return (← newInts gen n).map Name.numName

def newVar (gen : IO.Ref Int) : IO Term.term := do return .Var (← newName gen)
def newVars (gen : IO.Ref Int) (n : Int) : IO (List Term.term) := do
  return (← newNames gen n).map Term.term.Var

/-- Creating a substitution to freshen variables.  (`Substitute.freshVars s`:
    a renaming subst sending each var in `s` to a fresh var.) -/
def freshVars (gen : IO.Ref Int) (s : Name.Set.set) : IO Substitute.substT := do
  let mut acc := Substitute.empty
  for v in Name.Set.toList s do
    acc := Substitute.insert acc (v, ← newVar gen)
  return acc

end Gen

/- ---------------------------------------------------------------------- -/
/- DERIVED RULES FOR CREATING FIRST ORDER LOGIC THEOREMS                   -/
/- ---------------------------------------------------------------------- -/

/- -- Rule: derived rules for FOL theorems (`module Rule`) -------------------/
namespace Rule

/- Variable names. -/

def xVarName : Name.name := Name.fromString "x"
def xVar : Term.term := .Var xVarName
def yVarName : Name.name := Name.fromString "y"
def yVar : Term.term := .Var yVarName
def zVarName : Name.name := Name.fromString "z"
def zVar : Term.term := .Var zVarName
def xIVarName (i : Int) : Name.name := Name.fromString ("x" ++ toString i)
def xIVar (i : Int) : Term.term := .Var (xIVarName i)
def yIVarName (i : Int) : Name.name := Name.fromString ("y" ++ toString i)
def yIVar (i : Int) : Term.term := .Var (yIVarName i)

/- reflexivity / symmetry / transitivity. -/

def reflexivityRule (x : Term.term) : Thm.thm := Thm.refl x
def reflexivity : Thm.thm := reflexivityRule xVar

-- ~(x = y) \/ y = x
def symmetryRule (x y : Term.term) : Except String Thm.thm := do
  let reflTh := reflexivityRule x
  let reflLit ← Thm.destUnit reflTh
  let eqTh ← Thm.equality reflLit [0] y
  return Thm.resolve reflLit reflTh eqTh
def symmetry : Except String Thm.thm := symmetryRule xVar yVar

-- ~(x = y) \/ ~(y = z) \/ x = z
def transitivity : Except String Thm.thm := do
  let eqTh ← Thm.equality (Literal.mkEq (yVar, zVar)) [0] xVar
  return Thm.resolve (Literal.mkEq (yVar, xVar)) (← symmetry) eqTh

/-- `symEq (x=y) : x=y∨C ⊢ y=x∨C`. -/
def symEq (lit : Literal.literal) (th : Thm.thm) : Except String Thm.thm := do
  let (x, y) ← Literal.destEq lit
  if Term.equal x y then return th
  else
    let sub := Substitute.fromList [(xVarName, x), (yVarName, y)]
    let symTh := Thm.subst sub (← symmetry)
    return Thm.resolve lit th symTh

/- Equations. -/

-- An equation consists of two terms (t,u) plus a theorem (stronger than)
-- t = u \/ C.
abbrev equation := (Term.term × Term.term) × Thm.thm

def equationLiteral (eqn : equation) : Option Literal.literal :=
  let lit := Literal.mkEq eqn.1
  if Literal.Set.member lit (Thm.clause_ eqn.2) then some lit else none

def reflEqn (t : Term.term) : equation := ((t, t), Thm.refl t)

def symEqn (eqn : equation) : Except String equation := do
  let ((t, u), th) := eqn
  if Term.equal t u then return eqn
  else
    let th' ← match equationLiteral eqn with
      | some t_u => symEq t_u th
      | none => .ok th
    return ((u, t), th')

def transEqn (eqn1 eqn2 : equation) : Except String equation := do
  let ((x, y), th1) := eqn1
  let ((_, z), th2) := eqn2
  if Term.equal x y then return eqn2
  else if Term.equal y z then return eqn1
  else if Term.equal x z then return reflEqn x
  else
    let th ← match equationLiteral eqn1 with
      | none => .ok th1
      | some x_y => match equationLiteral eqn2 with
        | none => .ok th2
        | some y_z =>
          let sub := Substitute.fromList [(xVarName, x), (yVarName, y), (zVarName, z)]
          let th := Thm.subst sub (← transitivity)
          let th := Thm.resolve x_y th1 th
          .ok (Thm.resolve y_z th2 th)
    return ((x, z), th)

/- A conversion takes a term t and either:
   1. Returns a term u together with a theorem (stronger than) t = u \/ C.
   2. Raises an Failure exception.
   (`conv = Term.term -> Except (Term.term * Thm.thm)`.) -/

abbrev conv := Term.term → Except String (Term.term × Thm.thm)

def allConv : conv := fun tm => .ok (tm, Thm.refl tm)
def noConv : conv := fun _ => .error "noConv"

def thenConvTrans (tm : Term.term) (r1 r2 : Term.term × Thm.thm) :
    Except String (Term.term × Thm.thm) := do
  let (tm', th1) := r1
  let (tm'', th2) := r2
  let (_, th) ← transEqn ((tm, tm'), th1) ((tm', tm''), th2)
  return (tm'', th)

def thenConv (conv1 conv2 : conv) : conv := fun tm => do
  let res1 ← conv1 tm
  let res2 ← conv2 res1.1
  thenConvTrans tm res1 res2

def orelseConv (conv1 conv2 : conv) : conv := fun tm =>
  match conv1 tm with | .ok r => .ok r | .error _ => conv2 tm

def tryConv (c : conv) : conv := orelseConv c allConv

def changedConv (c : conv) : conv := fun tm => do
  let res ← c tm
  if Term.equal tm res.1 then .error "changedConv" else .ok res

partial def repeatConv (c : conv) : conv := fun tm =>
  tryConv (thenConv c (repeatConv c)) tm

partial def firstConvAux (tm : Term.term) : List conv → Except String (Term.term × Thm.thm)
  | [] => .error "firstConv"
  | [c] => c tm
  | c :: convs => orelseConv c (fun t => firstConvAux t convs) tm
def firstConv (convs : List conv) (tm : Term.term) : Except String (Term.term × Thm.thm) :=
  firstConvAux tm convs

partial def everyConvAux (tm : Term.term) : List conv → Except String (Term.term × Thm.thm)
  | [] => allConv tm
  | [c] => c tm
  | c :: convs => thenConv c (fun t => everyConvAux t convs) tm
def everyConv (convs : List conv) (tm : Term.term) : Except String (Term.term × Thm.thm) :=
  everyConvAux tm convs

def rewrConv (eqn : equation) (path : Term.path) (tm : Term.term) :
    Except String (Term.term × Thm.thm) := do
  let ((x, y), eqTh) := eqn
  if Term.equal x y then allConv tm
  else if Mlist.null path then .ok (y, eqTh)
  else
    let reflTh := Thm.refl tm
    let reflLit ← Thm.destUnit reflTh
    let th ← Thm.equality reflLit (1 :: path) y
    let th := Thm.resolve reflLit reflTh th
    let th := match equationLiteral eqn with
      | none => th
      | some x_y => Thm.resolve x_y eqTh th
    let tm' := Term.replace tm (path, y)
    return (tm', th)

def pathConv (c : conv) (path : Term.path) (tm : Term.term) :
    Except String (Term.term × Thm.thm) := do
  let x ← Term.subterm tm path
  let (y, th) ← c x
  rewrConv ((x, y), th) path tm

def subtermConv (c : conv) (i : Int) : conv := fun tm => pathConv c [i] tm

def subtermsConv (c : conv) : conv := fun tm =>
  match tm with
  | .Var _ => allConv tm
  | .Fn _ a => everyConv ((Useful.interval 0 a.length).map (subtermConv c)) tm

/- Applying a conversion to every subterm, with some traversal strategy. -/

partial def bottomUpConv (c : conv) : conv := fun tm =>
  thenConv (subtermsConv (bottomUpConv c)) (repeatConv c) tm

partial def topDownConv (c : conv) : conv := fun tm =>
  thenConv (repeatConv c) (subtermsConv (topDownConv c)) tm

mutual
partial def repeatTopDownConvF (c : conv) : conv := fun tm =>
  thenConv (repeatConv c) (repeatTopDownConvG c) tm
partial def repeatTopDownConvG (c : conv) : conv := fun tm =>
  thenConv (subtermsConv (repeatTopDownConvF c)) (repeatTopDownConvH c) tm
partial def repeatTopDownConvH (c : conv) : conv := fun tm =>
  tryConv (thenConv c (repeatTopDownConvF c)) tm
end
def repeatTopDownConv (c : conv) : conv := repeatTopDownConvF c

/- A literule (bad pun) takes a literal L and either:
   1. Returns a literal L' with a theorem (stronger than) ~L \/ L' \/ C.
   2. Raises an Failure exception. -/

abbrev literule := Literal.literal → Except String (Literal.literal × Thm.thm)

def allLiterule : literule := fun lit => .ok (lit, Thm.assume lit)
def noLiterule : literule := fun _ => .error "noLiterule"

def thenLiterule (literule1 literule2 : literule) : literule := fun lit => do
  let res1 ← literule1 lit
  let (lit', th1) := res1
  let res2 ← literule2 lit'
  let (lit'', th2) := res2
  if Literal.equal lit lit' then return res2
  else if Literal.equal lit' lit'' then return res1
  else if Literal.equal lit lit'' then allLiterule lit
  else
    return (lit'',
      if !(Thm.member lit' th1) then th1
      else if !(Thm.negateMember lit' th2) then th2
      else Thm.resolve lit' th1 th2)

def orelseLiterule (literule1 literule2 : literule) : literule := fun lit =>
  match literule1 lit with | .ok r => .ok r | .error _ => literule2 lit

def tryLiterule (l : literule) : literule := orelseLiterule l allLiterule

def changedLiterule (l : literule) : literule := fun lit => do
  let res ← l lit
  if Literal.equal lit res.1 then .error "changedLiterule" else .ok res

partial def repeatLiterule (l : literule) : literule := fun lit =>
  tryLiterule (thenLiterule l (repeatLiterule l)) lit

partial def firstLiteruleAux (lit : Literal.literal) :
    List literule → Except String (Literal.literal × Thm.thm)
  | [] => .error "firstLiterule"
  | [l] => l lit
  | l :: ls => orelseLiterule l (fun x => firstLiteruleAux x ls) lit
def firstLiterule (ls : List literule) (lit : Literal.literal) :
    Except String (Literal.literal × Thm.thm) := firstLiteruleAux lit ls

partial def everyLiteruleAux (lit : Literal.literal) :
    List literule → Except String (Literal.literal × Thm.thm)
  | [] => allLiterule lit
  | [l] => l lit
  | l :: ls => thenLiterule l (fun x => everyLiteruleAux x ls) lit
def everyLiterule (ls : List literule) (lit : Literal.literal) :
    Except String (Literal.literal × Thm.thm) := everyLiteruleAux lit ls

def rewrLiterule (eqn : equation) (path : Term.path) (lit : Literal.literal) :
    Except String (Literal.literal × Thm.thm) := do
  let ((x, y), eqTh) := eqn
  if Term.equal x y then allLiterule lit
  else
    let th ← Thm.equality lit path y
    let th := match equationLiteral eqn with
      | none => th
      | some x_y => Thm.resolve x_y eqTh th
    let lit' ← Literal.replace lit (path, y)
    return (lit', th)

def pathLiterule (c : conv) (path : Term.path) (lit : Literal.literal) :
    Except String (Literal.literal × Thm.thm) := do
  let tm ← Literal.subterm lit path
  let (tm', th) ← c tm
  rewrLiterule ((tm, tm'), th) path lit

def argumentLiterule (c : conv) (i : Int) : literule := fun lit => pathLiterule c [i] lit

def allArgumentsLiterule (c : conv) (lit : Literal.literal) :
    Except String (Literal.literal × Thm.thm) :=
  everyLiterule ((Useful.interval 0 (Literal.arity lit).toNat).map (argumentLiterule c)) lit

/- A rule takes one theorem and either deduces another or raises an Failure
   exception. -/

abbrev rule := Thm.thm → Except String Thm.thm

def allRule : rule := fun th => .ok th
def noRule : rule := fun _ => .error "noRule"
def thenRule (rule1 rule2 : rule) : rule := fun th => do rule1 (← rule2 th)
def orelseRule (rule1 rule2 : rule) : rule := fun th =>
  match rule1 th with | .ok r => .ok r | .error _ => rule2 th
def tryRule (r : rule) : rule := orelseRule r allRule
def changedRule (r : rule) : rule := fun th => do
  let th' ← r th
  if !(Literal.Set.equal (Thm.clause_ th) (Thm.clause_ th')) then .ok th'
  else .error "changedRule"
partial def repeatRule (r : rule) : rule := fun th => tryRule (thenRule r (repeatRule r)) th
partial def firstRuleAux (th : Thm.thm) : List rule → Except String Thm.thm
  | [] => .error "firstRule"
  | [r] => r th
  | r :: rs => orelseRule r (fun x => firstRuleAux x rs) th
def firstRule (rs : List rule) (th : Thm.thm) : Except String Thm.thm := firstRuleAux th rs
partial def everyRuleAux (th : Thm.thm) : List rule → Except String Thm.thm
  | [] => allRule th
  | [r] => r th
  | r :: rs => thenRule r (fun x => everyRuleAux x rs) th
def everyRule (rs : List rule) (th : Thm.thm) : Except String Thm.thm := everyRuleAux th rs

def literalRule (literule : literule) (lit : Literal.literal) (th : Thm.thm) :
    Except String Thm.thm := do
  let (lit', litTh) ← literule lit
  if Literal.equal lit lit' then return th
  else if !(Thm.negateMember lit litTh) then return litTh
  else return Thm.resolve lit th litTh

def rewrRule (eqTh : equation) (lit : Literal.literal) (path : Term.path) : rule :=
  fun th => literalRule (rewrLiterule eqTh path) lit th

def pathRule (c : conv) (lit : Literal.literal) (path : Term.path) : rule :=
  fun th => literalRule (pathLiterule c path) lit th

def literalsRule (literule : literule) (lits : Literal.Set.set) (th : Thm.thm) :
    Except String Thm.thm :=
  -- OCaml folds `f (lit,th)` over `lits`; literalRule is Except so we fold monadically.
  (do
    let mut cur := th
    for lit in Literal.Set.toList lits do
      cur ← (if Thm.member lit cur then literalRule literule lit cur else .ok cur)
    return cur)

def allLiteralsRule (literule : literule) (th : Thm.thm) : Except String Thm.thm :=
  literalsRule literule (Thm.clause_ th) th

def convRule (c : conv) : rule := allLiteralsRule (allArgumentsLiterule c)

/- Congruences. -/

-- ~(x0 = y0) \/ ... \/ ~(x{n-1} = y{n-1}) \/
--   f x0 ... x{n-1} = f y0 ... y{n-1}
-- ---------------------------------------------- functionCongruence (f,n)
def functionCongruence (f : Name.name) (n : Int) : Except String Thm.thm := do
  let xs := Mlist.tabulate n.toNat (fun i => xIVar (Int.ofNat i))
  let ys := Mlist.tabulate n.toNat (fun i => yIVar (Int.ofNat i))
  let reflTh := Thm.refl (Term.term.Fn f xs)
  let reflLit ← Thm.destUnit reflTh
  let cong (arg : (Nat × Term.term) × (Thm.thm × Literal.literal)) :
      Except String (Thm.thm × Literal.literal) := do
    let (i, yi) := arg.1
    let (th, lit) := arg.2
    let path : Term.path := [1, Int.ofNat i]
    let th := Thm.resolve lit th (← Thm.equality lit path yi)
    let lit ← Literal.replace lit (path, yi)
    return (th, lit)
  let mut acc := (reflTh, reflLit)
  for iyi in Mlist.enumerate ys do
    acc ← cong (iyi, acc)
  return acc.1

-- ~(x0 = y0) \/ ... \/ ~(x{n-1} = y{n-1}) \/
--   ~R x0 ... x{n-1} \/ R y0 ... y{n-1}
-- ---------------------------------------------- relationCongruence (R,n)
def relationCongruence (r : Name.name) (n : Int) : Except String Thm.thm := do
  let xs := Mlist.tabulate n.toNat (fun i => xIVar (Int.ofNat i))
  let ys := Mlist.tabulate n.toNat (fun i => yIVar (Int.ofNat i))
  let assumeLit : Literal.literal := (false, (r, xs))
  let assumeTh := Thm.assume assumeLit
  let cong (arg : (Nat × Term.term) × (Thm.thm × Literal.literal)) :
      Except String (Thm.thm × Literal.literal) := do
    let (i, yi) := arg.1
    let (th, lit) := arg.2
    let path : Term.path := [Int.ofNat i]
    let th := Thm.resolve lit th (← Thm.equality lit path yi)
    let lit ← Literal.replace lit (path, yi)
    return (th, lit)
  let mut acc := (assumeTh, assumeLit)
  for iyi in Mlist.enumerate ys do
    acc ← cong (iyi, acc)
  return acc.1

/-- `symNeq ~(x=y) : ~(x=y)∨C ⊢ ~(y=x)∨C`. -/
def symNeq (lit : Literal.literal) (th : Thm.thm) : Except String Thm.thm := do
  let (x, y) ← Literal.destNeq lit
  if Term.equal x y then return th
  else
    let sub := Substitute.fromList [(xVarName, y), (yVarName, x)]
    let symTh := Thm.subst sub (← symmetry)
    return Thm.resolve lit th symTh

-- sym (x = y) = symEq (x = y)  /\  sym ~(x = y) = symNeq ~(x = y)
def sym (lit : Literal.literal) (th : Thm.thm) : Except String Thm.thm :=
  if lit.1 then symEq lit th else symNeq lit th

--   ~(x = x) \/ C
-- ----------------- removeIrrefl
--         C
--
-- where all irreflexive equalities.
def removeIrrefl (th : Thm.thm) : Thm.thm :=
  let irrefl (arg : Literal.literal × Thm.thm) : Thm.thm :=
    let (lit, th) := arg
    match lit with
    | (true, _) => th
    | (false, atm) => match Useful.total Atom.destRefl atm with
                      | some x => Thm.resolve lit th (Thm.refl x)
                      | none => th
  Literal.Set.foldl irrefl th (Thm.clause_ th)

--   x = y \/ y = x \/ C
-- ----------------------- removeSym
--       x = y \/ C
--
-- where all duplicate copies of equalities and disequalities are removed.
def removeSym (th : Thm.thm) : Except String Thm.thm := do
  let rem (arg : Literal.literal × (Literal.Set.set × Thm.thm)) :
      Except String (Literal.Set.set × Thm.thm) := do
    let (lit, (eqs, th)) := arg
    let (pol, atm) := lit
    match Useful.total Atom.sym atm with
    | none => return (eqs, th)
    | some atm' =>
      if Literal.Set.member lit eqs then
        return (eqs, ← (if pol then symEq lit th else symNeq lit th))
      else return (Literal.Set.add eqs (pol, atm'), th)
  let mut acc := (Literal.Set.empty, th)
  for lit in Literal.Set.toList (Thm.clause_ th) do
    acc ← rem (lit, acc)
  return acc.2

--   ~(v = t) \/ C
-- ----------------- expandAbbrevs
--      C[t/v]
--
-- where t must not contain any occurrence of the variable v.
partial def expandAbbrevs (th : Thm.thm) : Except String Thm.thm := do
  let expand (lit : Literal.literal) : Except String Substitute.substT := do
    let (x, y) ← Literal.destNeq lit
    if !(Term.isTypedVar x || Term.isTypedVar y) then .error "Rule.expandAbbrevs: no vars"
    else if !(!(Term.equal x y)) then .error "Rule.expandAbbrevs: equal vars"
    else Substitute.unify Substitute.empty x y
  match Literal.Set.firstl (Useful.total expand) (Thm.clause_ th) with
  | none => return removeIrrefl th
  | some sub => expandAbbrevs (Thm.subst sub th)

/-- `simplify = isTautology + expandAbbrevs + removeSym`. -/
partial def simplify (th : Thm.thm) : Except String (Option Thm.thm) := do
  if Thm.isTautology th then return none
  else
    let th' := th
    let th' ← expandAbbrevs th'
    let th' ← removeSym th'
    if Thm.equal th th' then return some th else simplify th'

--    C
-- -------- freshVars
--   C[s]
--
-- where s is a renaming substitution chosen so that all of the variables in
-- C are replaced by fresh variables.  (Impure.)
def freshVars (gen : IO.Ref Int) (th : Thm.thm) : IO Thm.thm := do
  return Thm.subst (← Gen.freshVars gen (Thm.freeVars th)) th

/- Factoring.

               C
   ---------------------------- factor
     C_s_1, C_s_2, ..., C_s_n

   where each s_i is a substitution that factors C, meaning that the theorem

     C_s_i = (removeIrrefl o removeSym o Thm.subst s_i) C

   has fewer literals than C.

   Also, if s is any substitution that factors C, then one of the s_i will
   result in a theorem C_s_i that strictly subsumes the theorem C_s. -/

inductive edge where
  | Factor_edge (a a' : Atom.atom)
  | Refl_edge (t t' : Term.term)

inductive joinStatus where
  | Joined
  | Joinable (sub : Substitute.substT)
  | Apart

/-- `joinEdge` (metis.ml 4848-4857): `if sub == sub' then Joined else Joinable
    sub'`.  OCaml's `==` is PHYSICAL equality, true exactly when unification
    returned its input untouched - i.e. the edge is ALREADY satisfied by `sub`.
    `Substitute.solve` only ever changes `sub` by `compose sub (singleton
    (v,tm))` with `peek sub v = None`, which adds one binding for a FRESH
    variable, so the size strictly grows at every change.  Hence "same size" is
    exactly "physically unchanged".  Returning `Joinable` unconditionally (as
    this did) made `updateApart` keep an edge OCaml aborts on (`Joined ->
    None`), and let `fact` add a redundant factoring branch. -/
def joinEdge (sub : Substitute.substT) : edge → joinStatus
  | .Factor_edge atm atm' =>
    (match Useful.total (fun x => Atom.unify sub atm x) atm' with
     | none => .Apart
     | some sub' => joinedOr sub sub')
  | .Refl_edge tm tm' =>
    (match Useful.total (fun x => Substitute.unify sub tm x) tm' with
     | none => .Apart
     | some sub' => joinedOr sub sub')
where
  joinedOr (sub sub' : Substitute.substT) : joinStatus :=
    if Substitute.size sub' == Substitute.size sub then .Joined else .Joinable sub'

partial def updateApartAux (sub : Substitute.substT) (acc : List edge) :
    List edge → Option (List edge)
  | [] => some acc
  | e :: edges =>
    match joinEdge sub e with
    | .Joined => none
    | .Joinable _ => updateApartAux sub (e :: acc) edges
    | .Apart => updateApartAux sub acc edges
def updateApart (sub : Substitute.substT) (edges : List edge) : Option (List edge) :=
  updateApartAux sub [] edges

def addFactorEdge (lit : Literal.literal)
    (arg : Literal.literal × List (Substitute.substT × edge)) :
    List (Substitute.substT × edge) :=
  let (pol, atm) := lit
  let (lit', acc) := arg
  let (pol', atm') := lit'
  if pol ≠ pol' then acc
  else
    let e := edge.Factor_edge atm atm'
    match joinEdge Substitute.empty e with
    | .Joined => acc   -- OCaml raises Bug; treat as no-op (unreachable in practice)
    | .Joinable sub => (sub, e) :: acc
    | .Apart => acc

def addReflEdge (arg : Literal.literal × List edge) : List edge :=
  let (lit, acc) := arg
  match lit with
  | (false, _) => acc
  | (true, atm) =>
    match Atom.destEq atm with
    | .error _ => acc
    | .ok (x, y) =>
      let e := edge.Refl_edge x y
      match joinEdge Substitute.empty e with
      | .Joined => acc
      | .Joinable _ => e :: acc
      | .Apart => acc

def addIrreflEdge (arg : Literal.literal × List (Substitute.substT × edge)) :
    List (Substitute.substT × edge) :=
  let (lit, acc) := arg
  match lit with
  | (true, _) => acc
  | (false, atm) =>
    match Atom.destEq atm with
    | .error _ => acc
    | .ok (x, y) =>
      let e := edge.Refl_edge x y
      match joinEdge Substitute.empty e with
      | .Joined => acc
      | .Joinable sub => (sub, e) :: acc
      | .Apart => acc

partial def init_edges (acc : List (List edge × Substitute.substT × edge)) (apart : List edge) :
    List (Substitute.substT × edge) → List (List edge × Substitute.substT × List edge)
  | [] =>
    -- OCaml: fold `init` over acc, threading a growing `edges` list, producing
    -- triples (apart, sub, edges) where `edges` is the list accumulated so far.
    let init (arg : (List edge × Substitute.substT × edge) ×
              (List edge × List (List edge × Substitute.substT × List edge))) :
        List edge × List (List edge × Substitute.substT × List edge) :=
      let (apart, sub, e) := arg.1
      let (edges, acc) := arg.2
      (e :: edges, (apart, sub, edges) :: acc)
    (Mlist.foldl init ([], []) acc).2
  | (sub, e) :: sub_edges =>
    match updateApart sub apart with
    | some apart' => init_edges ((apart', sub, e) :: acc) (e :: apart) sub_edges
    | none => init_edges acc apart sub_edges

partial def mk_edges (apart : List edge) (sub_edges : List (Substitute.substT × edge)) :
    List Literal.literal → List (List edge × Substitute.substT × List edge)
  | [] => init_edges [] apart sub_edges
  | lit :: lits =>
    let sub_edges := Mlist.foldl (addFactorEdge lit) sub_edges lits
    let (apart, sub_edges) :=
      match Useful.total Literal.sym lit with
      | none => (apart, sub_edges)
      | some lit' =>
        let apart := addReflEdge (lit, apart)
        let sub_edges := addIrreflEdge (lit, sub_edges)
        let sub_edges := Mlist.foldl (addFactorEdge lit') sub_edges lits
        (apart, sub_edges)
    mk_edges apart sub_edges lits

partial def fact (acc : List Substitute.substT) :
    List (List edge × Substitute.substT × List edge) → List Substitute.substT
  | [] => acc
  | (_, sub, []) :: others => fact (sub :: acc) others
  | (apart, sub, e :: edges) :: others =>
    let others :=
      match joinEdge sub e with
      | .Joinable sub' =>
        let others := (e :: apart, sub, edges) :: others
        (match updateApart sub' apart with
         | none => others
         | some apart' => (apart', sub', edges) :: others)
      | _ => (apart, sub, edges) :: others
    fact acc others

/-- `factor' cl`: the substitutions that factor clause `cl`. -/
def factor' (cl : Literal.Set.set) : List Substitute.substT :=
  let edges := mk_edges [] [] (Literal.Set.toList cl)
  fact [] edges

/-- `factor th`: factored theorems (applies `factor'` then removeSym/removeIrrefl). -/
def factor (th : Thm.thm) : Except String (List Thm.thm) := do
  let factFn (sub : Substitute.substT) : Except String Thm.thm := do
    return removeIrrefl (← removeSym (Thm.subst sub th))
  let mut acc := []
  for sub in factor' (Thm.clause_ th) do
    acc := (← factFn sub) :: acc
  return acc.reverse

end Rule

/- ---------------------------------------------------------------------- -/
/- MATCHING AND UNIFICATION FOR SETS OF FIRST ORDER LOGIC TERMS            -/
/- ---------------------------------------------------------------------- -/

/- -- Term_net: matching/unification over term sets (`module Term_net`) ------/
namespace Term_net

/- Anonymous variables. -/
def anonymousName : Name.name := Name.fromString "_"
def anonymousVar : Term.term := .Var anonymousName

/-- Quotient terms: variables collapsed. -/
inductive qterm where
  | Var
  | Fn (na : Name_arity.nameArity) (qs : List qterm)
  deriving Inhabited

mutual
partial def cmp : List (qterm × qterm) → Int
  | [] => 0
  | (q1, q2) :: qs =>
    match q1, q2 with
    | .Var, .Var => cmp qs
    | .Var, .Fn _ _ => -1
    | .Fn _ _, .Var => 1
    | .Fn f1 f1', .Fn f2 f2' => fnCmp (f1, f1') (f2, f2') qs
partial def fnCmp (na1 : Name_arity.nameArity × List qterm)
    (na2 : Name_arity.nameArity × List qterm) (qs : List (qterm × qterm)) : Int :=
  let c := Name_arity.compare na1.1 na2.1
  if c ≠ 0 then c else cmp (na1.2.zip na2.2 ++ qs)
end

def compareQterm (q1 q2 : qterm) : Int := cmp [(q1, q2)]
def compareFnQterm (f1 f2 : Name_arity.nameArity × List qterm) : Int := fnCmp f1 f2 []
def equalQterm (q1 q2 : qterm) : Bool := compareQterm q1 q2 = 0
def equalFnQterm (f1 f2 : Name_arity.nameArity × List qterm) : Bool := compareFnQterm f1 f2 = 0

partial def termToQterm : Term.term → qterm
  | .Var _ => .Var
  | .Fn f l => .Fn (f, Int.ofNat l.length) (l.map termToQterm)

/- Matching qterm↔qterm / qterm↔term. -/

partial def matchQtermQtermAux : List (qterm × qterm) → Bool
  | [] => true
  | (.Var, _) :: rest => matchQtermQtermAux rest
  | (.Fn _ _, .Var) :: _ => false
  | (.Fn f a, .Fn g b) :: rest =>
    Name_arity.equal f g && matchQtermQtermAux (a.zip b ++ rest)
def matchQtermQterm (qtm qtm' : qterm) : Bool := matchQtermQtermAux [(qtm, qtm')]

partial def matchQtermTermAux : List (qterm × Term.term) → Bool
  | [] => true
  | (.Var, _) :: rest => matchQtermTermAux rest
  | (.Fn _ _, .Var _) :: _ => false
  | (.Fn (f, n) a, .Fn g b) :: rest =>
    Name.equal f g && n = Int.ofNat b.length && matchQtermTermAux (a.zip b ++ rest)
def matchQtermTerm (qtm : qterm) (tm : Term.term) : Bool := matchQtermTermAux [(qtm, tm)]

partial def matchTermQtermAux (qsub : Name.Map.map qterm) :
    List (Term.term × qterm) → Option (Name.Map.map qterm)
  | [] => some qsub
  | (.Var v, qtm) :: rest =>
    (match Name.Map.peek qsub v with
     | none => matchTermQtermAux (Name.Map.insert qsub (v, qtm)) rest
     | some qtm' => if equalQterm qtm qtm' then matchTermQtermAux qsub rest else none)
  | (.Fn _ _, .Var) :: _ => none
  | (.Fn f a, .Fn (g, n) b) :: rest =>
    if Name.equal f g && a.length = n then matchTermQtermAux qsub (a.zip b ++ rest)
    else none
def matchTermQterm (qsub : Name.Map.map qterm) (tm : Term.term) (qtm : qterm) :
    Option (Name.Map.map qterm) := matchTermQtermAux qsub [(tm, qtm)]

/- Unification qterm↔qterm / qterm↔term. -/

partial def qv : qterm → qterm → qterm
  | .Var, x => x
  | x, .Var => x
  | .Fn f a, .Fn _ b =>
    -- OCaml: assert Name_arity.equal f g; Fn(f, map2 qv a b)
    .Fn f ((a.zip b).map (fun (x, y) => qv x y))

partial def qu (qsub : Name.Map.map qterm) :
    List (qterm × Term.term) → Except String (Name.Map.map qterm)
  | [] => .ok qsub
  | (.Var, _) :: rest => qu qsub rest
  | (qtm, .Var v) :: rest =>
    let qtm := match Name.Map.peek qsub v with | none => qtm | some qtm' => qv qtm qtm'
    qu (Name.Map.insert qsub (v, qtm)) rest
  | (.Fn (f, n) a, .Fn g b) :: rest =>
    if Name.equal f g && n = Int.ofNat b.length then qu qsub (a.zip b ++ rest)
    else .error "Term_net.qu"
def unifyQtermQterm (qtm qtm' : qterm) : Option qterm := Useful.total (fun x => .ok (qv qtm x)) qtm'
def unifyQtermTerm (qsub : Name.Map.map qterm) (qtm : qterm) (tm : Term.term) :
    Option (Name.Map.map qterm) := Useful.total (fun x => qu qsub x) [(qtm, tm)]

partial def qtermToTerm : qterm → Term.term
  | .Var => anonymousVar
  | .Fn (f, _) l => .Fn f (l.map qtermToTerm)

/- Term sets efficiently matched and unified. -/

structure parameters where fifo : Bool

/-- A net over stored values `α`.  The `Multiple` branch's function-indexed
    children are stored as a sorted assoc list `List (nameArity × net α)`
    (rather than `Name_arity.Map`) so that `net` is a valid nested inductive —
    Lean's positivity checker sees through `List`/`×` but not through the
    `OrdMap.Map` structure.  A thin `fs*` API below re-creates the map ops. -/
inductive net (α : Type) where
  | Result (l : List α)
  | Single (qtm : qterm) (n : net α)
  | Multiple (vs : Option (net α)) (fs : List (Name_arity.nameArity × net α))
  deriving Inhabited

/- Assoc-list map ops over the `fs` children (keyed by `Name_arity.compare`). -/
def fsPeek (fs : List (Name_arity.nameArity × net α)) (k : Name_arity.nameArity) : Option (net α) :=
  (OrdMap.Map.mk Name_arity.compare fs |> fun m => OrdMap.peek m k)
def fsInsert (fs : List (Name_arity.nameArity × net α)) (kv : Name_arity.nameArity × net α) :
    List (Name_arity.nameArity × net α) :=
  (OrdMap.insert (OrdMap.Map.mk Name_arity.compare fs) kv).entries
def fsNull (fs : List (Name_arity.nameArity × net α)) : Bool := fs.isEmpty
def fsFoldl (f : Name_arity.nameArity × net α × σ → σ) (b : σ)
    (fs : List (Name_arity.nameArity × net α)) : σ :=
  OrdMap.foldl f b (OrdMap.Map.mk Name_arity.compare fs)
def fsFoldr (f : Name_arity.nameArity × net α × σ → σ) (b : σ)
    (fs : List (Name_arity.nameArity × net α)) : σ :=
  OrdMap.foldr f b (OrdMap.Map.mk Name_arity.compare fs)
def fsMapPartial (f : Name_arity.nameArity × net α → Option β)
    (fs : List (Name_arity.nameArity × net α)) : List (Name_arity.nameArity × β) :=
  (OrdMap.mapPartial f (OrdMap.Map.mk Name_arity.compare fs)).entries
def fsEmpty : List (Name_arity.nameArity × net α) := []

/-- The public term net: parameters, next index, and the indexed net.
    (A type of term sets that can be efficiently matched and unified.) -/
inductive termNet (α : Type) where
  | Net (p : parameters) (k : Int) (n : Option (Int × net (Int × α)))

instance [Inhabited α] : Inhabited (termNet α) :=
  ⟨.Net ⟨false⟩ 0 none⟩

/- Basic operations. -/
def newNet (parm : parameters) : termNet α := .Net parm 0 none

partial def computeSize : net α → Int
  | .Result l => Int.ofNat l.length
  | .Single _ n => computeSize n
  | .Multiple vs fs =>
    fsFoldl (fun (_, n, acc) => acc + computeSize n)
      (match vs with | some n => computeSize n | none => 0) fs

def netSize : Option (net α) → Option (Int × net α)
  | none => none
  | some n => some (computeSize n, n)

def size : termNet α → Int
  | .Net _ _ none => 0
  | .Net _ _ (some (i, _)) => i

def null (net : termNet α) : Bool := size net = 0

def singles (qtms : List qterm) (a : net α) : net α :=
  Mlist.foldr (fun (x, y) => net.Single x y) a qtms

def pre : Option (Int × net α) → Int × Option (net α)
  | none => (0, none)
  | some (i, n) => (i, some n)

mutual
partial def add (a : net α) : List qterm → net α → net α
  | [], .Result l' => (match a with | .Result l => .Result (l ++ l') | _ => .Result l')
  | qtm :: qtms, .Single qtm' n =>
    if equalQterm qtm qtm' then .Single qtm (add a qtms n)
    else add a (qtm :: qtms) (add n [qtm'] (.Multiple none fsEmpty))
  | .Var :: qtms, .Multiple vs fs => .Multiple (some (oadd a qtms vs)) fs
  | .Fn f l :: qtms, .Multiple vs fs =>
    let n := fsPeek fs f
    .Multiple vs (fsInsert fs (f, oadd a (l ++ qtms) n))
  | _, _ => panic! "Term_net.insert: Match"   -- OCaml raises Bug (unreachable)
partial def oadd (a : net α) (qtms : List qterm) : Option (net α) → net α
  | none => singles qtms a
  | some n => add a qtms n
end

def ins (a : α) (qtm : qterm) : Int × Option (net α) → Option (Int × net α)
  | (i, n) => some (i + 1, oadd (.Result [a]) [qtm] n)

def insert (net : termNet α) (tm_a : Term.term × α) : termNet α :=
  match net with
  | .Net p k n =>
    match ins (k, tm_a.2) (termToQterm tm_a.1) (pre n) with
    | some r => .Net p (k + 1) (some r)
    | none => .Net p (k + 1) none   -- OCaml can't fail here

def fromList (parm : parameters) (l : List (Term.term × α)) : termNet α :=
  Mlist.foldl (fun (tm_a, n) => insert n tm_a) (newNet parm) l

partial def filtNet (pred : α → Bool) : net α → Option (net α)
  | .Result l => (match l.filter (fun a => pred a) with | [] => none | l => some (.Result l))
  | .Single qtm n => (match filtNet pred n with | none => none | some n => some (.Single qtm n))
  | .Multiple vs fs =>
    let vs := Option.bind vs (filtNet pred)
    let fs := fsMapPartial (fun (_, n) => filtNet pred n) fs
    if !(vs.isSome) && fsNull fs then none else some (.Multiple vs fs)

def filter (pred : α → Bool) : termNet α → termNet α
  | .Net p k none => .Net p k none
  | .Net p k (some (_, n)) => .Net p k (netSize (filtNet (fun (a : Int × α) => pred a.2) n))

def toString (net : termNet α) : String := "Term_net[" ++ ToString.toString (size net) ++ "]"

/- Specialized fold operations for matching and unification. -/

/-- Stack for reconstructing qterms during net folds. -/
abbrev stackT := List Int × List Name_arity.nameArity × List qterm

mutual
partial def norm : stackT → stackT
  | (0 :: ks, f :: fs, qtms) =>
    match Mlist.revDivide qtms f.2.toNat with
    | .ok (a, qtms) => addQterm (.Fn f a) (ks, fs, qtms)
    | .error _ => (0 :: ks, f :: fs, qtms)
  | stack => stack
partial def addQterm (qtm : qterm) : stackT → stackT
  | (ks, fs, qtms) =>
    let ks := match ks with | [] => [] | k :: ks => (k - 1) :: ks
    norm (ks, fs, qtm :: qtms)
end
def addFn (f : Name_arity.nameArity) : stackT → stackT
  | (ks, fs, qtms) => norm (f.2 :: ks, f :: fs, qtms)

def stackEmpty : stackT := ([], [], [])
def stackAddQterm : qterm → stackT → stackT := addQterm
def stackAddFn : Name_arity.nameArity → stackT → stackT := addFn
def stackValue : stackT → qterm
  | ([], [], [qtm]) => qtm
  | _ => panic! "Term_net.stackValue"

/- Specialized fold operations to support matching and unification. -/

partial def foldEngine (inc : qterm × net α × σ → σ) (acc : σ) :
    List (Int × stackT × net α) → σ
  | [] => acc
  | (0, stack, net) :: rest => foldEngine inc (inc (stackValue stack, net, acc)) rest
  | (n, stack, .Single qtm net) :: rest =>
    foldEngine inc acc ((n - 1, stackAddQterm qtm stack, net) :: rest)
  | (n, stack, .Multiple v fns) :: rest =>
    let n := n - 1
    let rest := match v with
      | none => rest
      | some net => (n, stackAddQterm .Var stack, net) :: rest
    let getFns (arg : Name_arity.nameArity × net α × List (Int × stackT × net α)) :
        List (Int × stackT × net α) :=
      let (f, net, x) := arg
      (f.2 + n, stackAddFn f stack, net) :: x
    foldEngine inc acc (fsFoldr getFns rest fns)
  | (_, _, .Result _) :: rest => foldEngine inc acc rest  -- unreachable when n>0

def foldTerms (inc : qterm × net α × σ → σ) (acc : σ) (net : net α) : σ :=
  foldEngine inc acc [(1, stackEmpty, net)]

partial def foldEqualTermsAux (pat0 : qterm) (inc : qterm × net α × σ → σ) (acc : σ) :
    List qterm × net α → σ
  | ([], net) => inc (pat0, net, acc)
  | (pat :: pats, .Single qtm net) =>
    if equalQterm pat qtm then foldEqualTermsAux pat0 inc acc (pats, net) else acc
  | (.Var :: pats, .Multiple v _) =>
    (match v with | none => acc | some net => foldEqualTermsAux pat0 inc acc (pats, net))
  | (.Fn f a :: pats, .Multiple _ fns) =>
    (match fsPeek fns f with
     | none => acc
     | some net => foldEqualTermsAux pat0 inc acc (a ++ pats, net))
  | _ => acc  -- OCaml raises Bug (unreachable)
def foldEqualTerms (pat : qterm) (inc : qterm × net α × σ → σ) (acc : σ) (net : net α) : σ :=
  foldEqualTermsAux pat inc acc ([pat], net)

/-- Unification fold engine (`foldUnifiableTerms`). -/
partial def foldUnifEngine (inc : qterm × net α × σ → σ) (acc : σ) :
    List (List qterm × stackT × net α) → σ
  | [] => acc
  | ([], stack, net) :: rest => foldUnifEngine inc (inc (stackValue stack, net, acc)) rest
  | (.Var :: pats, stack, nt) :: rest =>
    let harvest (arg : qterm × net α × List (List qterm × stackT × net α)) :
        List (List qterm × stackT × net α) :=
      let (qtm, n, l) := arg
      (pats, stackAddQterm qtm stack, n) :: l
    foldUnifEngine inc acc (foldTerms harvest rest nt)
  | (pat :: pats, stack, .Single qtm net) :: rest =>
    (match unifyQtermQterm pat qtm with
     | none => foldUnifEngine inc acc rest
     | some qtm => foldUnifEngine inc acc ((pats, stackAddQterm qtm stack, net) :: rest))
  | ((.Fn f a) :: pats, stack, .Multiple v fns) :: rest =>
    let pat : qterm := .Fn f a
    let rest := match v with
      | none => rest
      | some net => (pats, stackAddQterm pat stack, net) :: rest
    let rest := match fsPeek fns f with
      | none => rest
      | some net => (a ++ pats, stackAddFn f stack, net) :: rest
    foldUnifEngine inc acc rest
  | _ => acc  -- unreachable
def foldUnifiableTerms (pat : qterm) (inc : qterm × net α × σ → σ) (acc : σ) (net : net α) : σ :=
  foldUnifEngine inc acc [([pat], stackEmpty, net)]

/- ---------------------------------------------------------------------- -/
/- Matching and unification queries.                                      -/
/- ---------------------------------------------------------------------- -/

/- These function return OVER-APPROXIMATIONS!
   Filter afterwards to get the precise set of satisfying values. -/

def idwise (m n : Int × α) : Int := Useful.intCompare m.1 n.1
def fifoize (p : parameters) (l : List (Int × α)) : List (Int × α) :=
  if p.fifo then Mlist.listSort idwise l else l
def finally_ (parm : parameters) (l : List (Int × α)) : List α := (fifoize parm l).map Prod.snd

/-- `matchNet net tm`: over-approximate stored values whose key matches `tm`. -/
partial def matEngine (acc : List (Int × α)) :
    List (net (Int × α) × List Term.term) → List (Int × α)
  | [] => acc
  | (.Result l, []) :: rest => matEngine (l ++ acc) rest
  | (.Single qtm n, tm :: tms) :: rest =>
    matEngine acc (if matchQtermTerm qtm tm then (n, tms) :: rest else rest)
  | (.Multiple vs fs, tm :: tms) :: rest =>
    let rest := match vs with | none => rest | some n => (n, tms) :: rest
    let rest := match tm with
      | .Var _ => rest
      | .Fn f l => match fsPeek fs (f, Int.ofNat l.length) with
                   | none => rest
                   | some n => (n, l ++ tms) :: rest
    matEngine acc rest
  | _ => acc  -- unreachable

def matchNet : termNet α → Term.term → List α
  | .Net _ _ none, _ => []
  | .Net p _ (some (_, n)), tm => finally_ p (matEngine [] [(n, [tm])])

/-- `matched net tm` (matching with a substitution accumulator). -/
def unseenInc (qsub : Name.Map.map qterm) (v : Name.name) (tms : List Term.term)
    (arg : qterm × net (Int × α) × List (Name.Map.map qterm × net (Int × α) × List Term.term)) :
    List (Name.Map.map qterm × net (Int × α) × List Term.term) :=
  let (qtm, net, rest) := arg
  (Name.Map.insert qsub (v, qtm), net, tms) :: rest
def seenInc (qsub : Name.Map.map qterm) (tms : List Term.term)
    (arg : qterm × net (Int × α) × List (Name.Map.map qterm × net (Int × α) × List Term.term)) :
    List (Name.Map.map qterm × net (Int × α) × List Term.term) :=
  let (_, net, rest) := arg
  (qsub, net, tms) :: rest

partial def matchedEngine (acc : List (Int × α)) :
    List (Name.Map.map qterm × net (Int × α) × List Term.term) → List (Int × α)
  | [] => acc
  | (_, .Result l, []) :: rest => matchedEngine (l ++ acc) rest
  | (qsub, .Single qtm net, tm :: tms) :: rest =>
    (match matchTermQterm qsub tm qtm with
     | none => matchedEngine acc rest
     | some qsub => matchedEngine acc ((qsub, net, tms) :: rest))
  | (qsub, .Multiple mv mf, .Var v :: tms) :: rest =>
    let nt : net (Int × α) := .Multiple mv mf
    (match Name.Map.peek qsub v with
     | none => matchedEngine acc (foldTerms (unseenInc qsub v tms) rest nt)
     | some qtm => matchedEngine acc (foldEqualTerms qtm (seenInc qsub tms) rest nt))
  | (qsub, .Multiple _ fns, .Fn f a :: tms) :: rest =>
    let rest := match fsPeek fns (f, Int.ofNat a.length) with
      | none => rest
      | some net => (qsub, net, a ++ tms) :: rest
    matchedEngine acc rest
  | _ => acc

def matched : termNet α → Term.term → List α
  | .Net _ _ none, _ => []
  | .Net parm _ (some (_, net)), tm => finally_ parm (matchedEngine [] [(Name.Map.newMap, net, [tm])])

/-- `unify net tm` (unification query). -/
def unifInc (qsub : Name.Map.map qterm) (v : Name.name) (tms : List Term.term)
    (arg : qterm × net (Int × α) × List (Name.Map.map qterm × net (Int × α) × List Term.term)) :
    List (Name.Map.map qterm × net (Int × α) × List Term.term) :=
  let (qtm, net, rest) := arg
  (Name.Map.insert qsub (v, qtm), net, tms) :: rest

partial def unifyEngine (acc : List (Int × α)) :
    List (Name.Map.map qterm × net (Int × α) × List Term.term) → List (Int × α)
  | [] => acc
  | (_, .Result l, []) :: rest => unifyEngine (l ++ acc) rest
  | (qsub, .Single qtm net, tm :: tms) :: rest =>
    (match unifyQtermTerm qsub qtm tm with
     | none => unifyEngine acc rest
     | some qsub => unifyEngine acc ((qsub, net, tms) :: rest))
  | (qsub, .Multiple mv mf, .Var v :: tms) :: rest =>
    let nt : net (Int × α) := .Multiple mv mf
    (match Name.Map.peek qsub v with
     | none => unifyEngine acc (foldTerms (unifInc qsub v tms) rest nt)
     | some qtm => unifyEngine acc (foldUnifiableTerms qtm (unifInc qsub v tms) rest nt))
  | (qsub, .Multiple v fns, .Fn f a :: tms) :: rest =>
    let rest := match v with | none => rest | some net => (qsub, net, tms) :: rest
    let rest := match fsPeek fns (f, Int.ofNat a.length) with
      | none => rest
      | some net => (qsub, net, a ++ tms) :: rest
    unifyEngine acc rest
  | _ => acc

def unify : termNet α → Term.term → List α
  | .Net _ _ none, _ => []
  | .Net parm _ (some (_, net)), tm => finally_ parm (unifyEngine [] [(Name.Map.newMap, net, [tm])])

end Term_net

/- ---------------------------------------------------------------------- -/
/- MATCHING AND UNIFICATION FOR SETS OF FIRST ORDER LOGIC ATOMS            -/
/- ---------------------------------------------------------------------- -/

/- -- Atom_net: matching/unification over atom sets (`module Atom_net`) ------/
namespace Atom_net

/- Helper functions. -/
def atomToTerm (atom : Atom.atom) : Term.term := .Fn atom.1 atom.2
def termToAtom : Term.term → Except String Atom.atom
  | .Var _ => .error "Atom_net.termToAtom"
  | .Fn f a => .ok (f, a)

/- A type of atom sets that can be efficiently matched and unified. -/
abbrev parameters := Term_net.parameters
abbrev atomNet (α : Type) := Term_net.termNet α

/- Basic operations. -/
def newNet (p : parameters) : atomNet α := Term_net.newNet p
def size (n : atomNet α) : Int := Term_net.size n
def insert (net : atomNet α) (atm_a : Atom.atom × α) : atomNet α :=
  Term_net.insert net (atomToTerm atm_a.1, atm_a.2)
def fromList (parm : parameters) (l : List (Atom.atom × α)) : atomNet α :=
  Mlist.foldl (fun (atm_a, n) => insert n atm_a) (newNet parm) l
def filter (pred : α → Bool) (n : atomNet α) : atomNet α := Term_net.filter pred n
def toString (net : atomNet α) : String := "Atom_net[" ++ ToString.toString (size net) ++ "]"

/- ---------------------------------------------------------------------- -/
/- Matching and unification queries.                                      -/
/- ---------------------------------------------------------------------- -/

/- These function return OVER-APPROXIMATIONS!
   Filter afterwards to get the precise set of satisfying values. -/
def matchNet (net : atomNet α) (atm : Atom.atom) : List α := Term_net.matchNet net (atomToTerm atm)
def matched (net : atomNet α) (atm : Atom.atom) : List α := Term_net.matched net (atomToTerm atm)
def unify (net : atomNet α) (atm : Atom.atom) : List α := Term_net.unify net (atomToTerm atm)

end Atom_net

/- ---------------------------------------------------------------------- -/
/- MATCHING AND UNIFICATION FOR SETS OF FIRST ORDER LOGIC LITERALS         -/
/- ---------------------------------------------------------------------- -/

/- -- Literal_net: matching/unification over literal sets (`module Literal_net`) -/
namespace Literal_net

/- A type of literal sets that can be efficiently matched and unified. -/
abbrev parameters := Atom_net.parameters

structure literalNet (α : Type) where
  positive : Atom_net.atomNet α
  negative : Atom_net.atomNet α

/- Basic operations. -/
def newNet (parm : parameters) : literalNet α :=
  { positive := Atom_net.newNet parm, negative := Atom_net.newNet parm }

def pos (net : literalNet α) : Int := Atom_net.size net.positive
def neg (net : literalNet α) : Int := Atom_net.size net.negative
def size (net : literalNet α) : Int := pos net + neg net

def insert (net : literalNet α) (lit_a : Literal.literal × α) : literalNet α :=
  match lit_a with
  | ((true, atm), a) => { net with positive := Atom_net.insert net.positive (atm, a) }
  | ((false, atm), a) => { net with negative := Atom_net.insert net.negative (atm, a) }

def fromList (parm : parameters) (l : List (Literal.literal × α)) : literalNet α :=
  Mlist.foldl (fun (lit_a, n) => insert n lit_a) (newNet parm) l

def filter (pred : α → Bool) (net : literalNet α) : literalNet α :=
  { positive := Atom_net.filter pred net.positive, negative := Atom_net.filter pred net.negative }

def toString (net : literalNet α) : String := "Literal_net[" ++ ToString.toString (size net) ++ "]"

/- ---------------------------------------------------------------------- -/
/- Matching and unification queries.                                      -/
/- ---------------------------------------------------------------------- -/

/- These function return OVER-APPROXIMATIONS!
   Filter afterwards to get the precise set of satisfying values. -/
def matchNet (net : literalNet α) : Literal.literal → List α
  | (true, atm) => Atom_net.matchNet net.positive atm
  | (false, atm) => Atom_net.matchNet net.negative atm
def matched (net : literalNet α) : Literal.literal → List α
  | (true, atm) => Atom_net.matched net.positive atm
  | (false, atm) => Atom_net.matched net.negative atm
def unify (net : literalNet α) : Literal.literal → List α
  | (true, atm) => Atom_net.unify net.positive atm
  | (false, atm) => Atom_net.unify net.negative atm

instance [Inhabited α] : Inhabited (literalNet α) := ⟨newNet ⟨false⟩⟩

end Literal_net

/- ---------------------------------------------------------------------- -/
/- SUBSUMPTION CHECKING FOR FIRST ORDER LOGIC CLAUSES                      -/
/- ---------------------------------------------------------------------- -/

/- -- Subsume: subsumption checking for FOL clauses (`module Subsume`) -------/
namespace Subsume

/- Helper functions. -/

/-- `findRest pred l`: the first `x` in `l` satisfying `pred`, plus the rest. -/
def findRest (pred : α → Bool) (l : List α) : Option (α × List α) :=
  let rec f (ys : List α) : List α → Option (α × List α)
    | [] => none
    | x :: xs => if pred x then some (x, ys.reverseAux xs) else f (x :: ys) xs
  f [] l

def addSym (arg : Literal.literal × List Literal.literal) : List Literal.literal :=
  match Useful.total Literal.sym arg.1 with | none => arg.2 | some lit => lit :: arg.2
def clauseSym (lits : List Literal.literal) : List Literal.literal := Mlist.foldl addSym lits lits

def sortClause (cl : Thm.clause) : List Literal.literal :=
  let lits := Literal.Set.toList cl
  Mlist.sortMap Literal.typedSymbols (Useful.revCompare Useful.intCompare) lits

def incompatible (lit : Literal.literal) : Literal.literal → Bool :=
  let lits := clauseSym [lit]
  fun lit' => !(lits.any (fun l => HolCore.Lib.can (fun x => Literal.unify Substitute.empty lit' x) l))

/- Clause ids and lengths. -/
abbrev clauseId := Int
abbrev clauseLength := Int

abbrev idSet := Pset.set (clauseId × clauseLength)
def idCompare (a b : clauseId × clauseLength) : Int :=
  let c := Useful.intCompare a.2 b.2
  if c ≠ 0 then c else Useful.intCompare a.1 b.1
def idSetEmpty : idSet := Pset.empty idCompare
def idSetAdd (arg : (clauseId × clauseLength) × idSet) : idSet := Pset.add arg.2 arg.1
def idSetAddMax (max : Int) (arg : (clauseId × clauseLength) × idSet) : idSet :=
  if arg.1.2 ≤ max then Pset.add arg.2 arg.1 else arg.2
def idSetIntersect (s1 s2 : idSet) : idSet := Pset.intersect s1 s2

/-- Non-unit clause store. -/
structure nonunit_t (α : Type) where
  nextId : clauseId
  clauses : Intmap.map (List Literal.literal × Thm.clause × α)
  fstLits : Literal_net.literalNet (clauseId × clauseLength)
  sndLits : Literal_net.literalNet (clauseId × clauseLength)

/- A type of clause sets that supports efficient subsumption checking. -/
structure subsume (α : Type) where
  «empty» : List (Thm.clause × Substitute.substT × α)
  unitn : Literal_net.literalNet (Literal.literal × Thm.clause × α)
  nonunit : nonunit_t α

def newSubsume : subsume α :=
  { «empty» := [],
    unitn := Literal_net.newNet ⟨false⟩,
    nonunit :=
      { nextId := 0, clauses := Intmap.newMap,
        fstLits := Literal_net.newNet ⟨false⟩, sndLits := Literal_net.newNet ⟨false⟩ } }

def size (s : subsume α) : Int :=
  Int.ofNat s.«empty».length + Literal_net.size s.unitn + Int.ofNat (Intmap.size s.nonunit.clauses)

def insert (s : subsume α) (cl'_a : Thm.clause × α) : subsume α :=
  let (cl', a) := cl'_a
  match sortClause cl' with
  | [] => { s with «empty» := (cl', Substitute.empty, a) :: s.«empty» }
  | [lit] => { s with unitn := Literal_net.insert s.unitn (lit, (lit, cl', a)) }
  | fstLit :: (sndLit :: otherLits) =>
    let nonFstLits := sndLit :: otherLits
    let nu := s.nonunit
    let id_length := (nu.nextId, Int.ofNat (Literal.Set.size cl'))
    let fstLits := Literal_net.insert nu.fstLits (fstLit, id_length)
    let (sndLit, otherLits) :=
      match findRest (incompatible fstLit) nonFstLits with
      | some sndLit_otherLits => sndLit_otherLits
      | none => (sndLit, otherLits)
    let sndLits := Literal_net.insert nu.sndLits (sndLit, id_length)
    let lits' := otherLits ++ [fstLit, sndLit]
    let clauses := Intmap.insert nu.clauses (nu.nextId, (lits', cl', a))
    { s with nonunit := { nextId := nu.nextId + 1, clauses := clauses,
                          fstLits := fstLits, sndLits := sndLits } }

def filter (pred : α → Bool) (s : subsume α) : subsume α :=
  let «empty» := s.«empty».filter (fun x => pred x.2.2)
  let unitn := Literal_net.filter (fun x => pred x.2.2) s.unitn
  let nu := s.nonunit
  let clauses' := Intmap.filter (fun x => pred x.2.2.2) nu.clauses
  let nonunit :=
    if Intmap.size nu.clauses = Intmap.size clauses' then nu
    else
      let predId (x : clauseId × clauseLength) : Bool := Intmap.inDomain x.1 clauses'
      { nextId := nu.nextId, clauses := clauses',
        fstLits := Literal_net.filter predId nu.fstLits,
        sndLits := Literal_net.filter predId nu.sndLits }
  { «empty» := «empty», unitn := unitn, nonunit := nonunit }

def toString (s : subsume α) : String := "Subsume{" ++ ToString.toString (size s) ++ "}"

/- Subsumption checking. -/

def matchLit (lit' : Literal.literal) (arg : Literal.literal × List Substitute.substT) :
    List Substitute.substT :=
  match Useful.total (fun x => Literal.matchLiterals Substitute.empty lit' x) arg.1 with
  | some sub => sub :: arg.2
  | none => arg.2

partial def gcsSearch (pred : Thm.clause × Substitute.substT × α → Bool)
    (cl' : Thm.clause) (a : α) :
    List (Substitute.substT × List (List Substitute.substT)) →
    Except String (Option (Thm.clause × Substitute.substT × α))
  | [] => .ok none
  | (sub, []) :: others =>
    let x := (cl', sub, a)
    if pred x then .ok (some x) else gcsSearch pred cl' a others
  | (_, [] :: _) :: others => gcsSearch pred cl' a others
  | (sub, (sub' :: subs) :: subsl) :: others =>
    let others := (sub, subs :: subsl) :: others
    match Useful.total (fun x => Substitute.union sub x) sub' with
    | none => gcsSearch pred cl' a others
    | some sub => gcsSearch pred cl' a ((sub, subsl) :: others)

partial def gcsMkSubsl (cl : List Literal.literal)
    (acc : List (List Substitute.substT)) (sub : Substitute.substT) :
    List Literal.literal → Option (Substitute.substT × List (List Substitute.substT))
  | [] => some (sub, Mlist.sortMap (fun l => Int.ofNat l.length) Useful.intCompare acc)
  | lit' :: lits' =>
    match Mlist.foldl (matchLit lit') [] cl with
    | [] => none
    | [sub'] =>
      (match Useful.total (fun x => Substitute.union sub x) sub' with
       | none => none
       | some sub => gcsMkSubsl cl acc sub lits')
    | subs => gcsMkSubsl cl (subs :: acc) sub lits'

def genClauseSubsumes (pred : Thm.clause × Substitute.substT × α → Bool)
    (cl' : Thm.clause) (lits' : List Literal.literal) (cl : List Literal.literal) (a : α) :
    Except String (Option (Thm.clause × Substitute.substT × α)) :=
  match gcsMkSubsl cl [] Substitute.empty lits' with
  | none => .ok none
  | some sub_subsl => gcsSearch pred cl' a [sub_subsl]

def emptySubsumes (pred : Thm.clause × Substitute.substT × α → Bool)
    («empty» : List (Thm.clause × Substitute.substT × α)) :
    Option (Thm.clause × Substitute.substT × α) := «empty».find? pred

def unitSubsumes (pred : Thm.clause × Substitute.substT × α → Bool)
    (unitn : Literal_net.literalNet (Literal.literal × Thm.clause × α)) :
    List Literal.literal → Option (Thm.clause × Substitute.substT × α) :=
  let subLit (lit : Literal.literal) : Option (Thm.clause × Substitute.substT × α) :=
    let subUnit (arg : Literal.literal × Thm.clause × α) :
        Option (Thm.clause × Substitute.substT × α) :=
      let (lit', cl', a) := arg
      match Useful.total (fun x => Literal.matchLiterals Substitute.empty lit' x) lit with
      | none => none
      | some sub => let x := (cl', sub, a); if pred x then some x else none
    Mlist.first subUnit (Literal_net.matchNet unitn lit)
  Mlist.first subLit

def nonunitSubsumes (pred : Thm.clause × Substitute.substT × α → Bool)
    (nonunit : nonunit_t α) (max : Option Int) (cl : List Literal.literal) :
    Except String (Option (Thm.clause × Substitute.substT × α)) := do
  let addId : (clauseId × clauseLength) × idSet → idSet :=
    match max with | none => idSetAdd | some n => idSetAddMax n
  let subLit (lits : Literal_net.literalNet (clauseId × clauseLength))
      (arg : Literal.literal × idSet) : idSet :=
    Mlist.foldl addId arg.2 (Literal_net.matchNet lits arg.1)
  let fstCands := Mlist.foldl (subLit nonunit.fstLits) idSetEmpty cl
  let sndCands := Mlist.foldl (subLit nonunit.sndLits) idSetEmpty cl
  let cands := idSetIntersect fstCands sndCands
  -- Pset.firstl subCl' cands, where subCl' looks up the clause and runs genClauseSubsumes
  let subCl' (idl : clauseId × clauseLength) :
      Option (Thm.clause × Substitute.substT × α) :=
    match Intmap.get nonunit.clauses idl.1 with
    | .error _ => none
    | .ok (lits', cl', a) =>
      match genClauseSubsumes pred cl' lits' cl a with
      | .ok r => r
      | .error _ => none
  return Pset.firstl subCl' cands

def genSubsumes (pred : Thm.clause × Substitute.substT × α → Bool)
    (s : subsume α) (max : Option Int) (cl : Thm.clause) :
    Except String (Option (Thm.clause × Substitute.substT × α)) := do
  match emptySubsumes pred s.«empty» with
  | some x => return some x
  | none =>
    if max = some 0 then return none
    else
      let cl := clauseSym (Literal.Set.toList cl)
      match unitSubsumes pred s.unitn cl with
      | some x => return some x
      | none =>
        if max = some 1 then return none
        else nonunitSubsumes pred s.nonunit max cl

def subsumes (pred : Thm.clause × Substitute.substT × α → Bool) (s : subsume α) (cl : Thm.clause) :
    Except String (Option (Thm.clause × Substitute.substT × α)) := genSubsumes pred s none cl

def strictlySubsumes (pred : Thm.clause × Substitute.substT × α → Bool)
    (s : subsume α) (cl : Thm.clause) :
    Except String (Option (Thm.clause × Substitute.substT × α)) :=
  genSubsumes pred s (some (Int.ofNat (Literal.Set.size cl))) cl

def isSubsumed (subs : subsume α) (cl : Thm.clause) : Bool :=
  match subsumes (fun _ => true) subs cl with | .ok (some _) => true | _ => false

def isStrictlySubsumed (subs : subsume α) (cl : Thm.clause) : Bool :=
  match strictlySubsumes (fun _ => true) subs cl with | .ok (some _) => true | _ => false

/- Single clause versions. -/

def clauseSubsumes (cl' cl : Thm.clause) : Except String (Option Substitute.substT) := do
  let lits' := sortClause cl'
  let lits := clauseSym (Literal.Set.toList cl)
  match ← genClauseSubsumes (fun _ => true) cl' lits' lits () with
  | some (_, sub, _) => return some sub
  | none => return none

def clauseStrictlySubsumes (cl' cl : Thm.clause) : Except String (Option Substitute.substT) :=
  if Literal.Set.size cl' > Literal.Set.size cl then .ok none else clauseSubsumes cl' cl

end Subsume

/- ---------------------------------------------------------------------- -/
/- KNUTH-BENDIX TERM ORDERING CONSTRAINTS                                  -/
/- ---------------------------------------------------------------------- -/

/- -- Knuth_bendix_order: KBO term-ordering constraints (`module Knuth_bendix_order`) -/
namespace Knuth_bendix_order

/- Helper functions. -/
def notEqualTerm (xy : Term.term × Term.term) : Bool := !(Term.equal xy.1 xy.2)

def firstNotEqualTerm (f : Term.term → Term.term → α) (l : List (Term.term × Term.term)) :
    Except String α :=
  match Mlist.find notEqualTerm l with
  | some (x, y) => .ok (f x y)
  | none => .error "firstNotEqualTerm"

/-- A KBO: a weight and a precedence on `function_t = name × arity`. -/
structure kbo where
  weight : Term.function_t → Int
  precedence : Term.function_t → Term.function_t → Int

-- The weight of all constants must be at least 1, and there must be at most
-- one unary function with weight 0.

-- Default weight = uniform
def uniformWeight : Term.function_t → Int := fun _ => 1
-- Default precedence = by arity
def arityPrecedence : Term.function_t → Term.function_t → Int :=
  fun f1 f2 => let c := Useful.intCompare f1.2 f2.2; if c ≠ 0 then c else Name.compare f1.1 f2.1
-- The default order
def default : kbo := { weight := uniformWeight, precedence := arityPrecedence }

/-- Term weight-1 represented as a linear function of the weight-1 of the
    variables in the term (plus a constant).

    Note that the conditions on weight functions ensure that all weights are
    at least 1, so all weight-1s are at least 0. -/
inductive weight where
  | Weight (m : Name.Map.map Int) (c : Int)
  deriving Inhabited

def weightEmpty : Name.Map.map Int := Name.Map.newMap
def weightZero : weight := .Weight weightEmpty 0
def weightIsZero : weight → Bool | .Weight m c => c = 0 && Name.Map.null m
def weightNeg : weight → weight
  | .Weight m c => .Weight (Name.Map.transform (fun x => -x) m) (-c)

def weightAddCombine (arg : (Name.name × Int) × (Name.name × Int)) : Option Int :=
  let n := arg.1.2 + arg.2.2
  if n = 0 then none else some n
def weightAdd : weight → weight → weight
  | .Weight m1 c1, .Weight m2 c2 => .Weight (Name.Map.union weightAddCombine m1 m2) (c1 + c2)
def weightSubtract (w1 w2 : weight) : weight := weightAdd w1 (weightNeg w2)

partial def weightTermAux (wt : Term.function_t → Int) :
    Name.Map.map Int → Int → List Term.term → weight
  | m, c, [] => .Weight m c
  | m, c, .Var v :: tms =>
    let n := (Name.Map.peek m v).getD 0
    weightTermAux wt (Name.Map.insert m (v, n + 1)) (c + 1) tms
  | m, c, .Fn f a :: tms =>
    weightTermAux wt m (c + wt (f, Int.ofNat a.length)) (a ++ tms)
def weightTerm (wt : Term.function_t → Int) (tm : Term.term) : weight :=
  weightTermAux wt weightEmpty (-1) [tm]

def weightLowerBound : weight → Option Int
  | .Weight m c => if Name.Map.existsb (fun (p : Name.name × Int) => p.2 < 0) m then none else some c

/- The Knuth-Bendix term order. -/

def weightDifference (kbo : kbo) (tm1 tm2 : Term.term) : weight :=
  weightSubtract (weightTerm kbo.weight tm2) (weightTerm kbo.weight tm1)

mutual
partial def weightLess (kbo : kbo) (tm1 tm2 : Term.term) : Bool :=
  let w := weightDifference kbo tm1 tm2
  if weightIsZero w then precedenceLess kbo tm1 tm2 else weightDiffLess kbo w tm1 tm2
partial def weightDiffLess (kbo : kbo) (w : weight) (tm1 tm2 : Term.term) : Bool :=
  match weightLowerBound w with
  | none => false
  | some 0 => precedenceLess kbo tm1 tm2
  | some n => n > 0
partial def precedenceLess (kbo : kbo) : Term.term → Term.term → Bool
  | .Fn f1 a1, .Fn f2 a2 =>
    let c := kbo.precedence (f1, Int.ofNat a1.length) (f2, Int.ofNat a2.length)
    if c < 0 then true
    else if c = 0 then
      (match firstNotEqualTerm (fun x y => weightLess kbo x y) (a1.zip a2) with
       | .ok b => b | .error _ => false)
    else false
  | _, _ => false
end

def weightDiffGreater (kbo : kbo) (w : weight) (tm1 tm2 : Term.term) : Bool :=
  weightDiffLess kbo (weightNeg w) tm2 tm1

mutual
partial def weightCmp (kbo : kbo) (tm1 tm2 : Term.term) : Option Int :=
  let w := weightDifference kbo tm1 tm2
  if weightIsZero w then precedenceCmp kbo tm1 tm2
  else if weightDiffLess kbo w tm1 tm2 then some (-1)
  else if weightDiffGreater kbo w tm1 tm2 then some 1
  else none
partial def precedenceCmp (kbo : kbo) : Term.term → Term.term → Option Int
  | .Fn f1 a1, .Fn f2 a2 =>
    let c := kbo.precedence (f1, Int.ofNat a1.length) (f2, Int.ofNat a2.length)
    if c < 0 then some (-1)
    else if c = 0 then
      (match firstNotEqualTerm (fun x y => weightCmp kbo x y) (a1.zip a2) with
       | .ok r => r | .error _ => none)
    else some 1
  | _, _ => none   -- OCaml raises Bug
end

def compare (kbo : kbo) (tm1 tm2 : Term.term) : Option Int :=
  if Term.equal tm1 tm2 then some 0 else weightCmp kbo tm1 tm2

end Knuth_bendix_order

/- -- Rewrite: ordered rewriting for first-order terms (`module Rewrite`) ----/
namespace Rewrite

/- Orientations of equations. -/

inductive orient where | Left_to_right | Right_to_left
  deriving Inhabited, BEq

def toStringOrient : orient → String
  | .Left_to_right => "-->" | .Right_to_left => "<--"
def toStringOrientOption : Option orient → String
  | some ort => toStringOrient ort | none => "<->"

abbrev reductionOrder := Term.term → Term.term → Option Int
abbrev equationId := Int
abbrev equation := Rule.equation

/- A type of rewrite systems. -/
structure rewrite_t where
  order : reductionOrder
  known : Intmap.map (equation × Option orient)
  redexes : Term_net.termNet (equationId × orient)
  subterms : Term_net.termNet (equationId × Bool × Term.path)
  waiting : Intset.set

inductive rewrite where | Rewrite (r : rewrite_t)

def updateWaiting : rewrite → Intset.set → rewrite
  | .Rewrite r, waiting => .Rewrite { r with waiting := waiting }
def deleteWaiting : rewrite → equationId → rewrite
  | .Rewrite r, id => updateWaiting (.Rewrite r) (Intset.delete r.waiting id)

/- Basic operations -/
def newRewrite (order : reductionOrder) : rewrite :=
  .Rewrite { order := order, known := Intmap.newMap,
             redexes := Term_net.newNet ⟨false⟩, subterms := Term_net.newNet ⟨false⟩,
             waiting := Intset.empty }

def peek : rewrite → equationId → Option (equation × Option orient)
  | .Rewrite r, id => Intmap.peek r.known id
def size : rewrite → Int | .Rewrite r => Int.ofNat (Intmap.size r.known)
def equations : rewrite → List equation
  | .Rewrite r => Intmap.foldr (fun (_, eo, eqns) => eo.1 :: eqns) [] r.known

/- Debug functions. -/

def eqnRed (order : reductionOrder) (eqn : equation) (tm : Term.term) : Bool :=
  let (l, r) := eqn.1
  match Useful.total (fun x => Substitute.matchTerms Substitute.empty l x) tm with
  | none => false
  | some sub => order tm (Substitute.subst (Substitute.normalize sub) r) = some 1

def knownRed (order : reductionOrder) (id : equationId) (tm : Term.term)
    (arg : equationId × (equation × Option orient)) : Bool :=
  let (eqnId, (eqn, ort)) := arg
  eqnId != id &&
    ((ort != some .Right_to_left && eqnRed order eqn tm) ||
     (ort != some .Left_to_right &&
      (match Rule.symEqn eqn with | .ok e => eqnRed order e tm | .error _ => false)))

mutual
partial def termRed (order : reductionOrder) (known : Intmap.map (equation × Option orient))
    (id : equationId) (tm : Term.term) : Bool :=
  Intmap.existsb (fun p => knownRed order id tm p) known || subtermRed order known id tm
partial def subtermRed (order : reductionOrder) (known : Intmap.map (equation × Option orient))
    (id : equationId) : Term.term → Bool
  | .Var _ => false
  | .Fn _ tms => tms.any (termRed order known id)
end

def termReducible (order : reductionOrder) (known : Intmap.map (equation × Option orient))
    (id : equationId) : Term.term → Bool := termRed order known id

def literalReducible (order : reductionOrder) (known : Intmap.map (equation × Option orient))
    (id : equationId) (lit : Literal.literal) : Bool :=
  (Literal.arguments lit).any (termReducible order known id)
def literalsReducible (order : reductionOrder) (known : Intmap.map (equation × Option orient))
    (id : equationId) (lits : Literal.Set.set) : Bool :=
  Literal.Set.existsb (literalReducible order known id) lits
def thmReducible (order : reductionOrder) (known : Intmap.map (equation × Option orient))
    (id : equationId) (th : Thm.thm) : Bool :=
  literalsReducible order known id (Thm.clause_ th)

/- Adding equations. -/

/- Add equations into the system. -/
def orderToOrient : Option Int → Except String (Option orient)
  | some 0 => .error "Rewrite.orient: reflexive"
  | some c => .ok (if c > 0 then some .Left_to_right else some .Right_to_left)
  | none => .ok none

def ins (redexes : Term_net.termNet (equationId × orient)) (redex : Term.term)
    (id : equationId) (ort : orient) : Term_net.termNet (equationId × orient) :=
  Term_net.insert redexes (redex, (id, ort))

def addRedexes (id : equationId) (eqn_ort : equation × Option orient)
    (redexes : Term_net.termNet (equationId × orient)) : Term_net.termNet (equationId × orient) :=
  let (eqn, ort) := eqn_ort
  let (l, r) := eqn.1
  match ort with
  | some .Left_to_right => ins redexes l id .Left_to_right
  | some .Right_to_left => ins redexes r id .Right_to_left
  | none => ins (ins redexes l id .Left_to_right) r id .Right_to_left

def add (rw : rewrite) (id_eqn : equationId × equation) : Except String rewrite := do
  match rw with
  | .Rewrite r =>
    let (id, eqn) := id_eqn
    if Intmap.inDomain id r.known then return rw
    else
      let (l, rr) := eqn.1
      let ort ← orderToOrient (r.order l rr)
      let known := Intmap.insert r.known (id, (eqn, ort))
      let redexes := addRedexes id (eqn, ort) r.redexes
      let waiting := Intset.add r.waiting id
      return .Rewrite { r with known := known, redexes := redexes, waiting := waiting }

def addList (rw : rewrite) (l : List (equationId × equation)) : Except String rewrite := do
  let mut cur := rw
  for id_eqn in l do
    cur ← add cur id_eqn
  return cur

/- Rewriting. -/

def reorder (i j : equationId × orient) : Int := Useful.intCompare j.1 i.1
def matchingRedexes (redexes : Term_net.termNet (equationId × orient)) (tm : Term.term) :
    List (equationId × orient) :=
  Mlist.listSort reorder (Term_net.matchNet redexes tm)

/- Rewriting (the order must be a refinement of the rewrite order). -/
def wellOriented : Option orient → orient → Bool
  | none, _ => true
  | some .Left_to_right, .Left_to_right => true
  | some .Right_to_left, .Right_to_left => true
  | _, _ => false

def redexResidue : orient → equation → Term.term × Term.term
  | .Left_to_right, eqn => eqn.1
  | .Right_to_left, eqn => (eqn.1.2, eqn.1.1)

def orientedEquation : orient → equation → Except String equation
  | .Left_to_right, eqn => .ok eqn
  | .Right_to_left, eqn => Rule.symEqn eqn

def rewrIdConv' (order : reductionOrder) (known : Intmap.map (equation × Option orient))
    (redexes : Term_net.termNet (equationId × orient)) (id : equationId) (tm : Term.term) :
    Except String (Term.term × Thm.thm) :=
  let rewr (idlr : equationId × orient) : Except String (Term.term × Thm.thm) := do
    let (id', lr) := idlr
    if !(id ≠ id') then .error "same theorem"
    else
      let (eqn, ort) ← Intmap.get known id'
      if !(wellOriented ort lr) then .error "orientation"
      else
        let (l, r) := redexResidue lr eqn
        let sub := Substitute.normalize (← Substitute.matchTerms Substitute.empty l tm)
        let tm' := Substitute.subst sub r
        if !(ort.isSome || order tm tm' = some 1) then .error "order"
        else
          let (_, th) ← orientedEquation lr eqn
          return (tm', Thm.subst sub th)
  match Mlist.first (fun x => (rewr x).toOption) (matchingRedexes redexes tm) with
  | none => .error "Rewrite.rewrIdConv: no matching rewrites"
  | some res => .ok res

def rewriteIdConv' (order : reductionOrder) (known : Intmap.map (equation × Option orient))
    (redexes : Term_net.termNet (equationId × orient)) (id : equationId) : Rule.conv :=
  if Intmap.null known then Rule.allConv
  else Rule.repeatTopDownConv (fun tm => rewrIdConv' order known redexes id tm)

def mkNeqConv (order : reductionOrder) (lit : Literal.literal) : Except String Rule.conv := do
  let (l, r) ← Literal.destNeq lit
  match order l r with
  | none => .error "incomparable"
  | some c =>
    if c < 0 then do
      let th ← Rule.symmetryRule l r
      return (fun tm => if Term.equal tm r then .ok (l, th) else .error "mkNeqConv: RL")
    else if c = 0 then .error "irreflexive"
    else
      let th := Thm.assume lit
      return (fun tm => if Term.equal tm l then .ok (r, th) else .error "mkNeqConv: LR")

inductive neqConvs where | Neq_convs (m : Literal.Map.map Rule.conv)
def neqConvsEmpty : neqConvs := .Neq_convs Literal.Map.newMap
def neqConvsNull : neqConvs → Bool | .Neq_convs m => Literal.Map.null m
def neqConvsAdd (order : reductionOrder) : neqConvs → Literal.literal → Option neqConvs
  | .Neq_convs m, lit =>
    match Useful.total (fun x => mkNeqConv order x) lit with
    | none => none
    | some conv => some (.Neq_convs (Literal.Map.insert m (lit, conv)))
def mkNeqConvs (order : reductionOrder) (lits : Literal.Set.set) : neqConvs × Literal.Set.set :=
  let add (arg : Literal.literal × (neqConvs × Literal.Set.set)) : neqConvs × Literal.Set.set :=
    let (lit, (neq, lits)) := arg
    match neqConvsAdd order neq lit with
    | some neq => (neq, lits)
    | none => (neq, Literal.Set.add lits lit)
  Literal.Set.foldl add (neqConvsEmpty, Literal.Set.empty) lits
def neqConvsDelete : neqConvs → Literal.literal → neqConvs
  | .Neq_convs m, lit => .Neq_convs (Literal.Map.delete m lit)
def neqConvsToConv : neqConvs → Rule.conv
  | .Neq_convs m => Rule.firstConv (Literal.Map.foldr (fun (_, c, l) => c :: l) [] m)
def neqConvsFoldl (f : Literal.literal × σ → σ) (b : σ) : neqConvs → σ
  | .Neq_convs m => Literal.Map.foldl (fun (l, _, z) => f (l, z)) b m

def neqConvsRewrIdLiterule (order : reductionOrder)
    (known : Intmap.map (equation × Option orient))
    (redexes : Term_net.termNet (equationId × orient)) (id : equationId) (neq : neqConvs) :
    Rule.literule :=
  if Intmap.null known && neqConvsNull neq then Rule.allLiterule
  else
    let neq_conv := neqConvsToConv neq
    let rewr_conv := fun tm => rewrIdConv' order known redexes id tm
    let conv := Rule.orelseConv neq_conv rewr_conv
    let conv := Rule.repeatTopDownConv conv
    Rule.allArgumentsLiterule conv

def rewriteIdEqn' (order : reductionOrder) (known : Intmap.map (equation × Option orient))
    (redexes : Term_net.termNet (equationId × orient)) (id : equationId) (eqn : equation) :
    Except String equation := do
  let (l_r, th) := eqn
  let (neq, _) := mkNeqConvs order (Thm.clause_ th)
  let literule := neqConvsRewrIdLiterule order known redexes id neq
  let (strongEqn, lit) :=
    match Rule.equationLiteral eqn with
    | none => (true, Literal.mkEq l_r)
    | some lit => (false, lit)
  let (lit', litTh) ← literule lit
  if Literal.equal lit lit' then return eqn
  else
    let dl ← Literal.destEq lit'
    return (dl,
      if strongEqn then th
      else if !(Thm.negateMember lit litTh) then litTh
      else Thm.resolve lit th litTh)

def rewr_neq_lit (order : reductionOrder) (known : Intmap.map (equation × Option orient))
    (redexes : Term_net.termNet (equationId × orient)) (id : equationId)
    (lit : Literal.literal) (acc : Bool × neqConvs × Literal.Set.set × Thm.thm) :
    Except String (Bool × neqConvs × Literal.Set.set × Thm.thm) := do
  let (changed, neq, lits, th) := acc
  let neq := neqConvsDelete neq lit
  let (lit', litTh) ← neqConvsRewrIdLiterule order known redexes id neq lit
  if Literal.equal lit lit' then return acc
  else
    let th := if Thm.member lit th then Thm.resolve lit th litTh else th
    match neqConvsAdd order neq lit' with
    | some neq => return (true, neq, lits, th)
    | none => return (changed, neq, Literal.Set.add lits lit', th)

partial def rewr_neq_lits (order : reductionOrder) (known : Intmap.map (equation × Option orient))
    (redexes : Term_net.termNet (equationId × orient)) (id : equationId)
    (neq : neqConvs) (lits : Literal.Set.set) (th : Thm.thm) :
    Except String (neqConvs × Literal.Set.set × Thm.thm) := do
  let mut acc := (false, neq, lits, th)
  let litKeys := match neq with
    | .Neq_convs m =>
      Literal.Map.foldl (fun (p : Literal.literal × Rule.conv × List Literal.literal) => p.1 :: p.2.2)
        ([] : List Literal.literal) m
  for lit in litKeys do
    acc ← rewr_neq_lit order known redexes id lit acc
  let (changed, neq', lits', th') := acc
  if changed then rewr_neq_lits order known redexes id neq' lits' th'
  else return (neq', lits', th')

def rewriteIdLiteralsRule' (order : reductionOrder) (known : Intmap.map (equation × Option orient))
    (redexes : Term_net.termNet (equationId × orient)) (id : equationId)
    (lits : Literal.Set.set) (th : Thm.thm) : Except String Thm.thm := do
  let (neq, lits) := mkNeqConvs order lits
  let (neq, lits, th) ← rewr_neq_lits order known redexes id neq lits th
  let rewr_literule := neqConvsRewrIdLiterule order known redexes id neq
  let mut cur := th
  for lit in Literal.Set.toList lits do
    cur ← (if Thm.member lit cur then Rule.literalRule rewr_literule lit cur else .ok cur)
  return cur

def rewriteIdRule' (order : reductionOrder) (known : Intmap.map (equation × Option orient))
    (redexes : Term_net.termNet (equationId × orient)) (id : equationId) (th : Thm.thm) :
    Except String Thm.thm :=
  rewriteIdLiteralsRule' order known redexes id (Thm.clause_ th) th

def rewrIdConv : rewrite → reductionOrder → equationId → Rule.conv
  | .Rewrite r, order, id => fun tm => rewrIdConv' order r.known r.redexes id tm
def rewrConv (rw : rewrite) (order : reductionOrder) : Rule.conv := rewrIdConv rw order (-1)
def rewriteIdConv : rewrite → reductionOrder → equationId → Rule.conv
  | .Rewrite r, order, id => rewriteIdConv' order r.known r.redexes id
def rewriteConv (rw : rewrite) (order : reductionOrder) : Rule.conv := rewriteIdConv rw order (-1)
def rewriteIdLiteralsRule : rewrite → reductionOrder → equationId → Literal.Set.set → Thm.thm →
    Except String Thm.thm
  | .Rewrite r, order, id, lits, th => rewriteIdLiteralsRule' order r.known r.redexes id lits th
def rewriteLiteralsRule (rw : rewrite) (order : reductionOrder) :
    Literal.Set.set → Thm.thm → Except String Thm.thm := rewriteIdLiteralsRule rw order (-1)
def rewriteIdRule : rewrite → reductionOrder → equationId → Thm.thm → Except String Thm.thm
  | .Rewrite r, order, id, th => rewriteIdRule' order r.known r.redexes id th
def rewriteRule (rw : rewrite) (order : reductionOrder) : Thm.thm → Except String Thm.thm :=
  rewriteIdRule rw order (-1)

/- Inter-reduce the equations in the system. -/

def addSubterms (id : equationId) (eqn : equation)
    (subterms : Term_net.termNet (equationId × Bool × Term.path)) :
    Term_net.termNet (equationId × Bool × Term.path) :=
  let (l, r) := eqn.1
  let addSubterm (b : Bool) (arg : (Term.path × Term.term) × Term_net.termNet (equationId × Bool × Term.path)) :
      Term_net.termNet (equationId × Bool × Term.path) :=
    let ((path, tm), net) := arg
    Term_net.insert net (tm, (id, b, path))
  let subterms := Mlist.foldl (addSubterm true) subterms (Term.subterms l)
  let subterms := Mlist.foldl (addSubterm false) subterms (Term.subterms r)
  subterms

def sameRedexes : Option orient → (Term.term × Term.term) → (Term.term × Term.term) → Bool
  | none, _, _ => false
  | some .Left_to_right, (l0, _), (l, _) => Term.equal l0 l
  | some .Right_to_left, (_, r0), (_, r) => Term.equal r0 r

def redexResidues : Option orient → (Term.term × Term.term) → List (Term.term × Term.term × Bool)
  | none, (l, r) => [(l, r, false), (r, l, false)]
  | some .Left_to_right, (l, r) => [(l, r, true)]
  | some .Right_to_left, (l, r) => [(r, l, true)]

def findReducibles (order : reductionOrder) (known : Intmap.map (equation × Option orient))
    (subterms : Term_net.termNet (equationId × Bool × Term.path)) (id : equationId)
    (todo : Intset.set) (residues : List (Term.term × Term.term × Bool)) : Intset.set :=
  let checkValidRewr (lrord : Term.term × Term.term × Bool) (id' : equationId) (left : Bool)
      (path : Term.path) : Bool :=
    let (l, r, ord) := lrord
    match Intmap.get known id' with
    | .error _ => false
    | .ok (eqn, _) =>
      let (x, y) := eqn.1
      match Term.subterm (if left then x else y) path with
      | .error _ => false
      | .ok tm =>
        match Substitute.matchTerms Substitute.empty l tm with
        | .error _ => false
        | .ok sub =>
          if ord then true
          else
            let tm' := Substitute.subst (Substitute.normalize sub) r
            order tm tm' = some 1
  let addRed (lr : Term.term × Term.term × Bool)
      (arg : (equationId × Bool × Term.path) × Intset.set) : Intset.set :=
    let ((id', left, path), todo) := arg
    if id != id' && !(Intset.member id' todo) && checkValidRewr lr id' left path
    then Intset.add todo id' else todo
  let findRed (arg : (Term.term × Term.term × Bool) × Intset.set) : Intset.set :=
    let (lr, todo) := arg
    Mlist.foldl (addRed lr) todo (Term_net.matched subterms lr.1)
  Mlist.foldl findRed todo residues

/-- Reduce one equation.  State: (rpl, spl, todo, rw, changed). -/
def reduce1 (newx : Bool) (id : equationId) (eqn_ort : equation × Option orient)
    (st : Intset.set × Intset.set × Intset.set × rewrite × Intset.set) :
    Except String (Intset.set × Intset.set × Intset.set × rewrite × Intset.set) := do
  let (eqn0, ort0) := eqn_ort
  let (rpl, spl, todo, rw, changed) := st
  match rw with
  | .Rewrite r =>
    let eq0 := eqn0.1
    let eqn ← rewriteIdEqn' r.order r.known r.redexes id eqn0
    let eq := eqn.1
    let identical := Term.equal eq.1 eq0.1 && Term.equal eq.2 eq0.2
    let same_redexes := identical || sameRedexes ort0 eq0 eq
    let rpl := if same_redexes then rpl else Intset.add rpl id
    let spl := if newx || identical then spl else Intset.add spl id
    let changed := if !newx && identical then changed else Intset.add changed id
    -- ort : Option (Option orient).  None ⇒ reorder failed (reflexive) ⇒ delete.
    let ort : Option (Option orient) :=
      if same_redexes then some ort0
      else (orderToOrient (r.order eq.1 eq.2)).toOption
    match ort with
    | none =>
      let known := Intmap.delete r.known id
      return (rpl, spl, todo, .Rewrite { r with known := known }, changed)
    | some ort =>
      let todo :=
        if !newx && same_redexes then todo
        else findReducibles r.order r.known r.subterms id todo (redexResidues ort eq)
      let known := if identical then r.known else Intmap.insert r.known (id, (eqn, ort))
      let redexes := if same_redexes then r.redexes else addRedexes id (eqn, ort) r.redexes
      let subterms := if newx || !identical then addSubterms id eqn r.subterms else r.subterms
      return (rpl, spl, todo,
        .Rewrite { r with known := known, redexes := redexes, subterms := subterms }, changed)

def pickOriented (known : Intmap.map (equation × Option orient)) (i : equationId) :
    Option (equationId × (equation × Option orient)) :=
  match Intmap.peek known i with
  | some eo => Option.map (fun ort' => (i, (eo.1, some ort'))) eo.2
  | none => none

def pickAny (known : Intmap.map (equation × Option orient)) (id : equationId) :
    Option (equationId × (equation × Option orient)) :=
  match Intmap.peek known id with
  | some x => some (id, x)
  | none => none

def pick (known : Intmap.map (equation × Option orient)) (set : Intset.set) :
    Option (equationId × (equation × Option orient)) :=
  match Intset.firstl (pickOriented known) set with
  | some x => some x
  | none => Intset.firstl (pickAny known) set

def cleanRedexes (known : Intmap.map (equation × Option orient))
    (redexes : Term_net.termNet (equationId × orient)) (rpl : Intset.set) :
    Term_net.termNet (equationId × orient) :=
  if Intset.null rpl then redexes
  else
    let filt (x : equationId × orient) : Bool := !(Intset.member x.1 rpl)
    let addReds (arg : equationId × Term_net.termNet (equationId × orient)) :
        Term_net.termNet (equationId × orient) :=
      let (id, reds) := arg
      match Intmap.peek known id with
      | none => reds
      | some eqn_ort => addRedexes id eqn_ort reds
    let redexes := Term_net.filter filt redexes
    Intset.foldl addReds redexes rpl

def cleanSubterms (known : Intmap.map (equation × Option orient))
    (subterms : Term_net.termNet (equationId × Bool × Term.path)) (spl : Intset.set) :
    Term_net.termNet (equationId × Bool × Term.path) :=
  if Intset.null spl then subterms
  else
    let filt (x : equationId × Bool × Term.path) : Bool := !(Intset.member x.1 spl)
    let addSubtms (arg : equationId × Term_net.termNet (equationId × Bool × Term.path)) :
        Term_net.termNet (equationId × Bool × Term.path) :=
      let (id, subtms) := arg
      match Intmap.peek known id with
      | none => subtms
      | some (eqn, _) => addSubterms id eqn subtms
    let subterms := Term_net.filter filt subterms
    Intset.foldl addSubtms subterms spl

def rebuild (rpl spl : Intset.set) : rewrite → rewrite
  | .Rewrite r =>
    let redexes := cleanRedexes r.known r.redexes rpl
    let subterms := cleanSubterms r.known r.subterms spl
    .Rewrite { r with redexes := redexes, subterms := subterms }

partial def reduceAcc
    (st : Intset.set × Intset.set × Intset.set × rewrite × Intset.set) :
    Except String (rewrite × List Int) := do
  let (rpl, spl, todo, rw, changed) := st
  match rw with
  | .Rewrite r =>
    match pick r.known todo with
    | some (id, eqn_ort) =>
      let todo := Intset.delete todo id
      reduceAcc (← reduce1 false id eqn_ort (rpl, spl, todo, rw, changed))
    | none =>
      match pick r.known r.waiting with
      | some (id, eqn_ort) =>
        let rw := deleteWaiting rw id
        reduceAcc (← reduce1 true id eqn_ort (rpl, spl, todo, rw, changed))
      | none => return (rebuild rpl spl rw, Intset.toList changed)

def isReduced : rewrite → Bool | .Rewrite r => Intset.null r.waiting

def reduce' (rw : rewrite) : Except String (rewrite × List Int) :=
  if isReduced rw then .ok (rw, [])
  else reduceAcc (Intset.empty, Intset.empty, Intset.empty, rw, Intset.empty)

def reduce (rw : rewrite) : Except String rewrite := do return (← reduce' rw).1

/- Rewriting as a derived rule. -/

/- Rewriting as a derived rule. -/

def addEqn (arg : (equationId × equation) × rewrite) : Except String rewrite :=
  add arg.2 arg.1

def orderedRewrite (order : reductionOrder) (ths : List equation) :
    Except String (Thm.thm → Except String Thm.thm) := do
  let mut rw := newRewrite order
  for id_eqn in Mlist.enumerate ths do
    rw ← add rw (Int.ofNat id_eqn.1, id_eqn.2)
  return rewriteRule rw order

def orderRewrite : reductionOrder := fun _ _ => some 1

/-- `rewrite = orderedRewrite orderRewrite` (the always-`Some 1` order). -/
def rewriteEqns (ths : List equation) : Except String (Thm.thm → Except String Thm.thm) :=
  orderedRewrite orderRewrite ths

end Rewrite

/- -- Units: a store for unit theorems (`module Units`) ----------------------/
namespace Units

/- A type of unit store. -/
abbrev unitThm := Literal.literal × Thm.thm

inductive units where | Units (net : Literal_net.literalNet unitThm)

/- Basic operations. -/
def empty : units := .Units (Literal_net.newNet ⟨false⟩)
def size : units → Int | .Units net => Literal_net.size net
def toString (u : units) : String := "U{" ++ ToString.toString (size u) ++ "}"

/-- Add units into the store.  (Adds a unit theorem and its symmetric variant
    if equality.) -/
def add (u : units) (uTh : unitThm) : Except String units := do
  match u with
  | .Units net =>
    let (lit, th) := uTh
    let net := Literal_net.insert net (lit, uTh)
    match Useful.total Literal.sym lit with
    | none => return .Units net
    | some lit' =>
      let (pol, _) := lit'
      let th' ← (if pol then Rule.symEq lit th else Rule.symNeq lit th)
      let net := Literal_net.insert net (lit', (lit', th'))
      return .Units net

def addList (u : units) (l : List unitThm) : Except String units := do
  let mut cur := u
  for th in l do
    cur ← add cur th
  return cur

/-- Match a literal against the store. -/
def matchUnits : units → Literal.literal → Option (unitThm × Substitute.substT)
  | .Units net, lit =>
    let check (uTh : unitThm) : Option (unitThm × Substitute.substT) :=
      match Useful.total (fun x => Literal.matchLiterals Substitute.empty uTh.1 x) lit with
      | none => none
      | some sub => some (uTh, sub)
    Mlist.first check (Literal_net.matchNet net lit)

/- Reducing by repeated matching and resolution. -/
def red1 (u : units) (lit : Literal.literal) (news_th : Literal.Set.set × Thm.thm) :
    Except String (Literal.Set.set × Thm.thm) := do
  match Useful.total Literal.destIrrefl lit with
  | some tm =>
    let (news, th) := news_th
    return (news, Thm.resolve lit th (Thm.refl tm))
  | none =>
    let lit' := Literal.negate lit
    match matchUnits u lit' with
    | none => return news_th
    | some ((_, rth), sub) =>
      let (news, th) := news_th
      let rth := Thm.subst sub rth
      let th := Thm.resolve lit th rth
      let newLits := Literal.Set.delete (Thm.clause_ rth) lit'
      let news := Literal.Set.union newLits news
      return (news, th)

partial def redLoop (u : units) (news_th : Literal.Set.set × Thm.thm) : Except String Thm.thm := do
  let (news, th) := news_th
  if Literal.Set.null news then return th
  else
    let mut acc := (Literal.Set.empty, th)
    for lit in Literal.Set.toList news do
      acc ← red1 u lit acc
    redLoop u acc

def reduce (u : units) (th : Thm.thm) : Except String Thm.thm := do
  Rule.removeSym (← redLoop u (Thm.clause_ th, th))

end Units

/- -- Random source (models OCaml `Random`) --------------------------------
   Metis uses `Random.init 0` for determinism then `Random.int`.  We model the
   RNG as an `IO.Ref StdGen`, seeded in `Session.lean` with `mkStdGen 0`. -/
namespace Rand

/-- `randInt r n`: uniform in `[0, n)` (OCaml `Random.int n`), advancing `r`. -/
def randInt (r : IO.Ref StdGen) (n : Int) : IO Int := do
  if n ≤ 0 then return 0
  else
    let g ← r.get
    let (v, g') := randNat g 0 (n.toNat - 1)
    r.set g'
    return Int.ofNat v

end Rand

/- -- Clause: id + theorem (`module Clause`) --------------------------------
   `Clause.newId` uses a global counter ref in OCaml; we thread an `IO.Ref Int`
   (the clause-id counter, Session-owned) into the id-allocating functions. -/
namespace Clause

inductive literalOrder where
  | No_literal_order | Unsigned_literal_order | Positive_literal_order

structure parameters where
  ordering : Knuth_bendix_order.kbo
  orderLiterals : literalOrder
  orderTerms : Bool

abbrev clauseId := Int

structure clauseInfo where
  parameters : parameters
  id : clauseId
  thm : Thm.thm

/- A type of clause. -/
inductive clause where | Clause (info : clauseInfo)

instance : Inhabited Clause.parameters :=
  ⟨{ ordering := Knuth_bendix_order.default, orderLiterals := .Positive_literal_order,
     orderTerms := true }⟩
instance : Inhabited clauseInfo := ⟨{ parameters := Inhabited.default, id := 0, thm := default }⟩
instance : Inhabited clause := ⟨.Clause Inhabited.default⟩

/- Basic operations. -/
def default : parameters :=
  { ordering := Knuth_bendix_order.default,
    orderLiterals := .Positive_literal_order, orderTerms := true }

def mk (info : clauseInfo) : clause := .Clause info
def dest : clause → clauseInfo | .Clause info => info
def id : clause → clauseId | .Clause i => i.id
def thm : clause → Thm.thm | .Clause i => i.thm
def clauseParameters : clause → parameters | .Clause i => i.parameters
def equalThms (cl cl' : clause) : Bool := Thm.equal (thm cl) (thm cl')
def literals (cl : clause) : Thm.clause := Thm.clause_ (thm cl)
def isTautology : clause → Bool | .Clause i => Thm.isTautology i.thm
def isContradiction : clause → Bool | .Clause i => Thm.isContradiction i.thm
def toString (cl : clause) : String := Thm.toString (thm cl)

/- Helper functions. -/

/-- `newId`: fresh clause id (impure, via the Session counter ref). -/
def newId (r : IO.Ref clauseId) : IO clauseId := do
  let n ← r.get; r.set (n + 1); return n

def newClause (r : IO.Ref clauseId) (parameters : parameters) (thm : Thm.thm) : IO clause := do
  return .Clause { parameters := parameters, id := ← newId r, thm := thm }

/- The term ordering is used to cut down inferences. -/

def strictlyLess (ordering : Knuth_bendix_order.kbo) (x y : Term.term) : Bool :=
  match Knuth_bendix_order.compare ordering x y with
  | some c => c < 0
  | _ => false

def isLargerTerm (p : parameters) (lr : Term.term × Term.term) : Bool :=
  !p.orderTerms || !(strictlyLess p.ordering lr.1 lr.2)

def atomToTerms (atm : Atom.atom) : List Term.term :=
  match Useful.total Atom.destEq atm with
  | none => [Term.term.Fn atm.1 atm.2]
  | some (l, r) => [l, r]

def notStrictlyLess (ordering : Knuth_bendix_order.kbo) (xs ys : List Term.term) : Bool :=
  let less (x : Term.term) : Bool := ys.any (fun y => strictlyLess ordering x y)
  !(xs.all less)

/-- `isLargerLiteral params lits` : predicate on literals selecting maximal ones. -/
def isLargerLiteral (p : parameters) (lits : Literal.Set.set) : Literal.literal → Bool :=
  match p.orderLiterals with
  | .No_literal_order => fun _ => true
  | .Unsigned_literal_order =>
    let addLit (arg : Literal.literal × List Term.term) : List Term.term :=
      atomToTerms arg.1.2 ++ arg.2
    let tms := Literal.Set.foldl addLit [] lits
    fun lit => notStrictlyLess p.ordering (atomToTerms lit.2) tms
  | .Positive_literal_order =>
    match Literal.Set.findl (fun _ => true) lits with
    | none => fun _ => true
    | some (pol, _) =>
      let addLit (arg : Literal.literal × List Term.term) : List Term.term :=
        if arg.1.1 = pol then atomToTerms arg.1.2 ++ arg.2 else arg.2
      let tms := Literal.Set.foldl addLit [] lits
      fun lit =>
        if pol ≠ lit.1 then pol
        else notStrictlyLess p.ordering (atomToTerms lit.2) tms

def largestLiterals : clause → Literal.Set.set
  | .Clause i =>
    let litSet := Thm.clause_ i.thm
    let isLarger := isLargerLiteral i.parameters litSet
    let addLit (arg : Literal.literal × Literal.Set.set) : Literal.Set.set :=
      if isLarger arg.1 then Literal.Set.add arg.2 arg.1 else arg.2
    Literal.Set.foldr addLit Literal.Set.empty litSet

def largestEquations (cl : clause) : List (Literal.literal × Rewrite.orient × Term.term) :=
  let p := clauseParameters cl
  let addEq (lit : Literal.literal) (ort : Rewrite.orient) (l_r : Term.term × Term.term)
      (acc : List (Literal.literal × Rewrite.orient × Term.term)) :
      List (Literal.literal × Rewrite.orient × Term.term) :=
    if isLargerTerm p l_r then (lit, ort, l_r.1) :: acc else acc
  let addLit (arg : Literal.literal × List (Literal.literal × Rewrite.orient × Term.term)) :
      List (Literal.literal × Rewrite.orient × Term.term) :=
    let (lit, acc) := arg
    match Useful.total Literal.destEq lit with
    | none => acc
    | some (l, r) =>
      let acc := addEq lit .Right_to_left (r, l) acc
      let acc := addEq lit .Left_to_right (l, r) acc
      acc
  Literal.Set.foldr addLit [] (largestLiterals cl)

def clauseAddLit (arg : Literal.literal × List (Literal.literal × Term.path × Term.term)) :
    List (Literal.literal × Term.path × Term.term) :=
  let (lit, acc) := arg
  let addTm (a2 : (Term.path × Term.term) × List (Literal.literal × Term.path × Term.term)) :
      List (Literal.literal × Term.path × Term.term) :=
    (lit, a2.1.1, a2.1.2) :: a2.2
  Mlist.foldl addTm acc (Literal.nonVarTypedSubterms lit)

def largestSubterms (cl : clause) : List (Literal.literal × Term.path × Term.term) :=
  Literal.Set.foldl clauseAddLit [] (largestLiterals cl)
def allSubterms (cl : clause) : List (Literal.literal × Term.path × Term.term) :=
  Literal.Set.foldl clauseAddLit [] (literals cl)

/- Subsumption. -/

def subsumes (subs : Subsume.subsume clause) (cl : clause) : Bool :=
  Subsume.isStrictlySubsumed subs (literals cl)

/- Simplifying rules: these preserve the clause id. -/

def freshVars (gen : IO.Ref Int) : clause → IO clause
  | .Clause i => do return .Clause { i with thm := ← Rule.freshVars gen i.thm }

def simplify : clause → Except String (Option clause)
  | .Clause i => do
    match ← Rule.simplify i.thm with
    | none => return none
    | some thm => return some (.Clause { i with thm := thm })

def reduce (units : Units.units) : clause → Except String clause
  | .Clause i => do return .Clause { i with thm := ← Units.reduce units i.thm }

def rewrite (rewr : Rewrite.rewrite) : clause → Except String clause
  | .Clause i => do
    let simp (th : Thm.thm) : Except String Thm.thm :=
      Rewrite.rewriteIdRule rewr (Knuth_bendix_order.compare i.parameters.ordering) i.id th
    let thm ← match Rewrite.peek rewr i.id with
      | none => simp i.thm
      | some (eqn_thm, _) => if Rewrite.isReduced rewr then .ok eqn_thm.2 else simp i.thm
    return .Clause { i with thm := thm }

/- Inference rules: these generate new clause ids. -/

def factor (r : IO.Ref clauseId) (cl : clause) : IO (Except String (List clause)) := do
  match cl with
  | .Clause i =>
    let lits := largestLiterals cl
    let mut acc := []
    for sub in Rule.factor' lits do
      let c ← newClause r i.parameters (Thm.subst sub i.thm)
      acc := c :: acc
    return .ok acc.reverse

def resolve (r : IO.Ref clauseId) (cl1lit1 : clause × Literal.literal)
    (cl2lit2 : clause × Literal.literal) : IO (Except String clause) := do
  let (cl1, lit1) := cl1lit1
  let (cl2, lit2) := cl2lit2
  match cl1, cl2 with
  | .Clause i1, .Clause i2 =>
    let parameters := i1.parameters
    match (do
      let sub ← Literal.unify Substitute.empty lit1 (Literal.negate lit2)
      let lit1 := Literal.subst sub lit1
      let lit2 := Literal.negate lit1
      let th1 := Thm.subst sub i1.thm
      let th2 := Thm.subst sub i2.thm
      if !(isLargerLiteral parameters (Thm.clause_ th1) lit1) then
        .error "resolve: clause1: ordering constraints"
      else if !(isLargerLiteral parameters (Thm.clause_ th2) lit2) then
        .error "resolve: clause2: ordering constraints"
      else .ok (Thm.resolve lit1 th1 th2) : Except String Thm.thm) with
    | .error e => return .error e
    | .ok th => return .ok (← newClause r parameters th)

def paramodulate (r : IO.Ref clauseId)
    (cl1lit1ort1tm1 : clause × Literal.literal × Rewrite.orient × Term.term)
    (cl2lit2path2tm2 : clause × Literal.literal × Term.path × Term.term) :
    IO (Except String clause) := do
  let (cl1, lit1, ort1, tm1) := cl1lit1ort1tm1
  let (cl2, lit2, path2, tm2) := cl2lit2path2tm2
  match cl1, cl2 with
  | .Clause i1, .Clause i2 =>
    let parameters := i1.parameters
    match (do
      let sub ← Substitute.unify Substitute.empty tm1 tm2
      let lit1 := Literal.subst sub lit1
      let lit2 := Literal.subst sub lit2
      let th1 := Thm.subst sub i1.thm
      let th2 := Thm.subst sub i2.thm
      if !(isLargerLiteral parameters (Thm.clause_ th1) lit1) then
        .error "Clause.paramodulate: with clause: ordering"
      else if !(isLargerLiteral parameters (Thm.clause_ th2) lit2) then
        .error "Clause.paramodulate: into clause: ordering"
      else
        let eqn := (← Literal.destEq lit1, th1)
        let eqn ← match ort1 with
          | .Left_to_right => .ok eqn
          | .Right_to_left => Rule.symEqn eqn
        let l_r := eqn.1
        if !(isLargerTerm parameters l_r) then
          .error "Clause.paramodulate: equation: ordering constraints"
        else Rule.rewrRule eqn lit2 path2 th2 : Except String Thm.thm) with
    | .error e => return .error e
    | .ok th => return .ok (← newClause r parameters th)

end Clause

/- -- Ax_cj: axiom/conjecture bundles (`module Ax_cj`) -----------------------/
namespace Ax_cj
structure ax_cj_thm where
  axioms_thm : List Thm.thm
  conjecture_thm : List Thm.thm
structure ax_cj_cl where
  axioms_cl : List Clause.clause
  conjecture_cl : List Clause.clause
end Ax_cj

/- -- Model: random finite models (`module Model`) --------------------------
   Used only for clause weighting in `Waiting`.  Tables are mutable arrays and
   the interpretation caches random results, so `Model` lives in `IO` and takes
   a `Rand`-style RNG ref (Session-owned).  A `model` bundles `IO.Ref`s. -/
namespace Model

def maxSpace : Int := 1000

/- Helper functions. -/

def multInt (x y : Int) : Option Int :=
  -- OCaml guards against overflow; with arbitrary-precision Int this always succeeds,
  -- but we keep the size guard faithful (m = floor sqrt max_int ≈ big).
  let m : Int := 3037000499   -- floor(sqrt(2^63-1)), the OCaml 63-bit bound
  if x ≤ m && y ≤ m then some (x * y) else none

mutual
partial def iexp (x y acc : Int) : Option Int :=
  if y % 2 = 0 then iexp' x y acc
  else match multInt acc x with | some acc => iexp' x y acc | none => none
partial def iexp' (x y acc : Int) : Option Int :=
  if y = 1 then some acc
  else
    let y := y / 2
    match multInt x x with | some x => iexp x y acc | none => none
end

def expInt (x y : Int) : Option Int :=
  if y ≤ 1 then
    (if y = 0 then some 1 else if y = 1 then some x else none)   -- OCaml raises Bug on negative
  else if x ≤ 1 then (if 0 ≤ x then some x else none)
  else iexp x y 1

def boolToInt : Bool → Int | true => 1 | false => 0
def intToBool : Int → Bool | 1 => true | _ => false   -- OCaml raises on other; 0→false covered
def minMaxInterval (i j : Int) : List Int := Useful.interval i (1 + j - i).toNat

/- Model size.

   A model of size N has integer elements 0...N-1. -/
abbrev element := Int
def zeroElement : element := 0

def incrementElement (n : Int) (i : element) : Option element :=
  let i := i + 1
  if i = n then none else some i

def elementListSpace (n : Int) (arity : Int) : Option Int :=
  match expInt n arity with
  | none => none
  | some m => if m ≤ maxSpace then some m else none

def elementListIndex (n : Int) (elts : List element) : Int :=
  elts.foldl (fun acc elt => n * acc + elt) 0

/- The parts of the model that are fixed. -/

abbrev fixedFunction := Int → List element → Option element
abbrev fixedRelation := Int → List element → Option Bool

structure fixed where
  functions : Name_arity.Map.map fixedFunction
  relations : Name_arity.Map.map fixedRelation

def uselessFixedFunction : fixedFunction := fun _ _ => none
def uselessFixedRelation : fixedRelation := fun _ _ => none
def emptyFunctions : Name_arity.Map.map fixedFunction := Name_arity.Map.newMap
def emptyRelations : Name_arity.Map.map fixedRelation := Name_arity.Map.newMap

def fixed0 (f : Int → Option element) : fixedFunction := fun sz elts =>
  match elts with | [] => f sz | _ => none
def fixed1 (f : Int → element → Option element) : fixedFunction := fun sz elts =>
  match elts with | [x] => f sz x | _ => none
def fixed2 (f : Int → element → element → Option element) : fixedFunction := fun sz elts =>
  match elts with | [x, y] => f sz x y | _ => none
def fixed0R (f : Int → Option Bool) : fixedRelation := fun sz elts =>
  match elts with | [] => f sz | _ => none
def fixed1R (f : Int → element → Option Bool) : fixedRelation := fun sz elts =>
  match elts with | [x] => f sz x | _ => none
def fixed2R (f : Int → element → element → Option Bool) : fixedRelation := fun sz elts =>
  match elts with | [x, y] => f sz x y | _ => none

def emptyFixed : fixed := { functions := emptyFunctions, relations := emptyRelations }

def peekFunctionFixed (fix : fixed) (na : Name_arity.nameArity) : Option fixedFunction :=
  Name_arity.Map.peek fix.functions na
def peekRelationFixed (fix : fixed) (na : Name_arity.nameArity) : Option fixedRelation :=
  Name_arity.Map.peek fix.relations na
def getFunctionFixed (fix : fixed) (na : Name_arity.nameArity) : fixedFunction :=
  (peekFunctionFixed fix na).getD uselessFixedFunction
def getRelationFixed (fix : fixed) (na : Name_arity.nameArity) : fixedRelation :=
  (peekRelationFixed fix na).getD uselessFixedRelation
def insertFunctionFixed (fix : fixed) (naf : Name_arity.nameArity × fixedFunction) : fixed :=
  { fix with functions := Name_arity.Map.insert fix.functions naf }
def insertRelationFixed (fix : fixed) (nar : Name_arity.nameArity × fixedRelation) : fixed :=
  { fix with relations := Name_arity.Map.insert fix.relations nar }

def unionFixed (fix1 fix2 : fixed) : fixed :=
  -- OCaml raises Bug on nameArity clash; union prefers second (rare in practice).
  { functions := Name_arity.Map.union (fun p => some p.2.2) fix1.functions fix2.functions,
    relations := Name_arity.Map.union (fun p => some p.2.2) fix1.relations fix2.relations }
def unionListFixed (l : List fixed) : fixed :=
  Mlist.foldl (fun (fix, acc) => unionFixed acc fix) emptyFixed l

def hasTypeFn : fixedFunction := fun _ elts => match elts with | [x, _] => some x | _ => none
def eqRel : fixedRelation := fun _ elts => match elts with | [x, y] => some (x = y) | _ => none
def basicFixed : fixed :=
  { functions := Name_arity.Map.singleton (Term.hasTypeFunction, hasTypeFn),
    relations := Name_arity.Map.singleton (Atom.eqRelation, eqRel) }

/- Renaming fixed model parts. -/

structure fixedMap where
  functionMap : Name_arity.Map.map Name.name
  relationMap : Name_arity.Map.map Name.name

def mapFixed (fixMap : fixedMap) (fix : fixed) : fixed :=
  { functions := Name_arity.Map.compose fixMap.functionMap fix.functions,
    relations := Name_arity.Map.compose fixMap.relationMap fix.relations }

/- Standard fixed model parts: projections. -/

def projectionMin : Int := 1
def projectionMax : Int := 9
def projectionList : List Int := minMaxInterval projectionMin projectionMax
def projectionName (i : Int) : Name.name := Name.fromString ("project" ++ toString i)
def projectionFn (i : Int) : fixedFunction := fun _ elts => elts[(i - 1).toNat]?

partial def arityProjectionAddProj (arity : Int)
    (mkProj : Int → Name_arity.nameArity × fixedFunction)
    (i : Int) (acc : Name_arity.Map.map fixedFunction) : Name_arity.Map.map fixedFunction :=
  if i > arity then acc
  else arityProjectionAddProj arity mkProj (i + 1) (Name_arity.Map.insert acc (mkProj i))

def arityProjectionFixed (arity : Int) : fixed :=
  let mkProj (i : Int) : Name_arity.nameArity × fixedFunction :=
    ((projectionName i, arity), projectionFn i)
  { functions := arityProjectionAddProj arity mkProj projectionMin emptyFunctions,
    relations := emptyRelations }

def projectionFixed : fixed := unionListFixed (projectionList.map arityProjectionFixed)

/- Arithmetic (modular + overflow variants). -/

def numeralMin : Int := -100
def numeralMax : Int := 100
def numeralList : List Int := minMaxInterval numeralMin numeralMax
def numeralName (i : Int) : Name.name :=
  Name.fromString (if i < 0 then "negative" ++ toString (-i) else toString i)

def addName : Name.name := Name.fromString "+"
def divName : Name.name := Name.fromString "div"
def dividesName : Name.name := Name.fromString "divides"
def evenName : Name.name := Name.fromString "even"
def expName : Name.name := Name.fromString "exp"
def geName : Name.name := Name.fromString ">="
def gtName : Name.name := Name.fromString ">"
def isZeroName : Name.name := Name.fromString "isZero"
def leName : Name.name := Name.fromString "<="
def ltName : Name.name := Name.fromString "<"
def modName : Name.name := Name.fromString "mod"
def multName : Name.name := Name.fromString "*"
def negName : Name.name := Name.fromString "~"
def oddName : Name.name := Name.fromString "odd"
def preName : Name.name := Name.fromString "pre"
def subName : Name.name := Name.fromString "-"
def sucName : Name.name := Name.fromString "suc"

/- Modular arithmetic interpretations. -/
def modN (n x : Int) : Int := x % n
def m_oneN (n : Int) : Int := modN n 1
def m_multN (n : Int) (xy : Int × Int) : Int := modN n (xy.1 * xy.2)
def m_numeralFn (i n : Int) : Option element := some (modN n i)
def m_addFn (n x y : Int) : Option element := some (modN n (x + y))
def m_divFn (n x y : Int) : Option element := let y := if y = 0 then n else y; some (x / y)
def m_expFn (n x y : Int) : Option element := some (Useful.exp (m_multN n) x y.toNat (m_oneN n))
def m_modFn (n x y : Int) : Option element := let y := if y = 0 then n else y; some (x % y)
def m_multFn (n x y : Int) : Option element := some (m_multN n (x, y))
def m_negFn (n x : Int) : Option element := some (if x = 0 then 0 else n - x)
def m_preFn (n x : Int) : Option element := some (if x = 0 then n - 1 else x - 1)
def m_subFn (n x y : Int) : Option element := some (if x < y then n + x - y else x - y)
def m_sucFn (n x : Int) : Option element := some (if x = n - 1 then 0 else x + 1)
def m_dividesRel (_ x y : Int) : Option Bool := some (Useful.divides x y)
def m_evenRel (_ x : Int) : Option Bool := some (x % 2 = 0)
def m_geRel (_ x y : Int) : Option Bool := some (x ≥ y)
def m_gtRel (_ x y : Int) : Option Bool := some (x > y)
def m_isZeroRel (_ x : Int) : Option Bool := some (x = 0)
def m_leRel (_ x y : Int) : Option Bool := some (x ≤ y)
def m_ltRel (_ x y : Int) : Option Bool := some (x < y)
def m_oddRel (_ x : Int) : Option Bool := some (x % 2 = 1)

def modularFixed : fixed :=
  { functions := Name_arity.Map.fromList
      (numeralList.map (fun i => ((numeralName i, 0), fixed0 (m_numeralFn i))) ++
       [((addName, 2), fixed2 m_addFn), ((divName, 2), fixed2 m_divFn),
        ((expName, 2), fixed2 m_expFn), ((modName, 2), fixed2 m_modFn),
        ((multName, 2), fixed2 m_multFn), ((negName, 1), fixed1 m_negFn),
        ((preName, 1), fixed1 m_preFn), ((subName, 2), fixed2 m_subFn),
        ((sucName, 1), fixed1 m_sucFn)]),
    relations := Name_arity.Map.fromList
      [((dividesName, 2), fixed2R m_dividesRel), ((evenName, 1), fixed1R m_evenRel),
       ((geName, 2), fixed2R m_geRel), ((gtName, 2), fixed2R m_gtRel),
       ((isZeroName, 1), fixed1R m_isZeroRel), ((leName, 2), fixed2R m_leRel),
       ((ltName, 2), fixed2R m_ltRel), ((oddName, 1), fixed1R m_oddRel)] }

/- Overflow arithmetic interpretations. -/
def cutN (n x : Int) : Int := if x ≥ n then n - 1 else x
def o_oneN (n : Int) : Int := cutN n 1
def o_multN (n : Int) (xy : Int × Int) : Int := cutN n (xy.1 * xy.2)
def o_numeralFn (i n : Int) : Option element := if i < 0 then none else some (cutN n i)
def o_addFn (n x y : Int) : Option element := some (cutN n (x + y))
def o_divFn (_ x y : Int) : Option element := if y = 0 then none else some (x / y)
def o_expFn (n x y : Int) : Option element := some (Useful.exp (o_multN n) x y.toNat (o_oneN n))
def o_modFn (n x y : Int) : Option element := if y = 0 || x = n - 1 then none else some (x % y)
def o_multFn (n x y : Int) : Option element := some (o_multN n (x, y))
def o_negFn (_ x : Int) : Option element := if x = 0 then some 0 else none
def o_preFn (_ x : Int) : Option element := if x = 0 then none else some (x - 1)
def o_subFn (n x y : Int) : Option element :=
  if y = 0 then some x else if x = n - 1 || x < y then none else some (x - y)
def o_sucFn (n x : Int) : Option element := some (cutN n (x + 1))
def o_dividesRel (n x y : Int) : Option Bool :=
  if x = 1 || y = 0 then some true else if x = 0 then some false
  else if y = n - 1 then none else some (Useful.divides x y)
def o_evenRel (n x : Int) : Option Bool := if x = n - 1 then none else some (x % 2 = 0)
def o_geRel (n y x : Int) : Option Bool :=
  if x = n - 1 then (if y = n - 1 then none else some false)
  else if y = n - 1 then some true else some (x ≤ y)
def o_gtRel (n y x : Int) : Option Bool :=
  if x = n - 1 then (if y = n - 1 then none else some false)
  else if y = n - 1 then some true else some (x < y)
def o_isZeroRel (_ x : Int) : Option Bool := some (x = 0)
def o_leRel (n x y : Int) : Option Bool :=
  if x = n - 1 then (if y = n - 1 then none else some false)
  else if y = n - 1 then some true else some (x ≤ y)
def o_ltRel (n x y : Int) : Option Bool :=
  if x = n - 1 then (if y = n - 1 then none else some false)
  else if y = n - 1 then some true else some (x < y)
def o_oddRel (n x : Int) : Option Bool := if x = n - 1 then none else some (x % 2 = 1)

def overflowFixed : fixed :=
  { functions := Name_arity.Map.fromList
      (numeralList.map (fun i => ((numeralName i, 0), fixed0 (o_numeralFn i))) ++
       [((addName, 2), fixed2 o_addFn), ((divName, 2), fixed2 o_divFn),
        ((expName, 2), fixed2 o_expFn), ((modName, 2), fixed2 o_modFn),
        ((multName, 2), fixed2 o_multFn), ((negName, 1), fixed1 o_negFn),
        ((preName, 1), fixed1 o_preFn), ((subName, 2), fixed2 o_subFn),
        ((sucName, 1), fixed1 o_sucFn)]),
    relations := Name_arity.Map.fromList
      [((dividesName, 2), fixed2R o_dividesRel), ((evenName, 1), fixed1R o_evenRel),
       ((geName, 2), fixed2R o_geRel), ((gtName, 2), fixed2R o_gtRel),
       ((isZeroName, 1), fixed1R o_isZeroRel), ((leName, 2), fixed2R o_leRel),
       ((ltName, 2), fixed2R o_ltRel), ((oddName, 1), fixed1R o_oddRel)] }

/- Sets. -/
def cardName : Name.name := Name.fromString "card"
def complementName : Name.name := Name.fromString "complement"
def differenceName : Name.name := Name.fromString "difference"
def emptyName : Name.name := Name.fromString "empty"
def memberName : Name.name := Name.fromString "member"
def insertName : Name.name := Name.fromString "insert"
def intersectName : Name.name := Name.fromString "intersect"
def singletonName : Name.name := Name.fromString "singleton"
def subsetName : Name.name := Name.fromString "subset"
def symmetricDifferenceName : Name.name := Name.fromString "symmetricDifference"
def unionName : Name.name := Name.fromString "union"
def universeName : Name.name := Name.fromString "universe"

partial def eltNaux (acc x : Int) : Int := if x = 0 then acc else eltNaux (acc + 1) (x / 2)
def eltN (n : Int) : Int := eltNaux (-1) n
def posN (i : Int) : Int := Word.shiftLeft 1 (Word.fromInt i)
def univN (n : Int) : Int := Word.minus (posN (eltN n)) 1
def setN (n x : Int) : Int := Word.andb (Word.fromInt x) (univN n)

partial def cardFaux (acc s : Int) : Int :=
  if s = 0 then acc
  else cardFaux (if Word.andb s 1 = 0 then acc else acc + 1) (Word.shiftRight s 1)
def s_cardFn (n x : Int) : Option element := some (cardFaux 0 (setN n x))
def s_complementFn (n x : Int) : Option element := some (Word.toInt (Word.xorb (univN n) (setN n x)))
def s_differenceFn (n x y : Int) : Option element :=
  some (Word.toInt (Word.andb (setN n x) (Word.notb (setN n y))))
def s_emptyFn (_ : Int) : Option element := some 0
def s_insertFn (n x y : Int) : Option element :=
  some (Word.toInt (Word.orb (posN (x % eltN n)) (setN n y)))
def s_intersectFn (n x y : Int) : Option element := some (Word.toInt (Word.andb (setN n x) (setN n y)))
def s_singletonFn (n x : Int) : Option element := some (Word.toInt (posN (x % eltN n)))
def s_symmetricDifferenceFn (n x y : Int) : Option element :=
  some (Word.toInt (Word.xorb (setN n x) (setN n y)))
def s_unionFn (n x y : Int) : Option element := some (Word.toInt (Word.orb (setN n x) (setN n y)))
def s_universeFn (n : Int) : Option element := some (Word.toInt (univN n))
def s_memberRel (n x y : Int) : Option Bool := some (Word.andb (posN (x % eltN n)) (setN n y) ≠ 0)
def s_subsetRel (n x y : Int) : Option Bool := some (Word.andb (setN n x) (Word.notb (setN n y)) = 0)

def setFixed : fixed :=
  { functions := Name_arity.Map.fromList
      [((cardName, 1), fixed1 s_cardFn), ((complementName, 1), fixed1 s_complementFn),
       ((differenceName, 2), fixed2 s_differenceFn), ((emptyName, 0), fixed0 s_emptyFn),
       ((insertName, 2), fixed2 s_insertFn), ((intersectName, 2), fixed2 s_intersectFn),
       ((singletonName, 1), fixed1 s_singletonFn),
       ((symmetricDifferenceName, 2), fixed2 s_symmetricDifferenceFn),
       ((unionName, 2), fixed2 s_unionFn), ((universeName, 0), fixed0 s_universeFn)],
    relations := Name_arity.Map.fromList
      [((memberName, 2), fixed2R s_memberRel), ((subsetName, 2), fixed2R s_subsetRel)] }

/- Lists. -/
def appendName : Name.name := Name.fromString "@"
def consName : Name.name := Name.fromString "::"
def lengthName : Name.name := Name.fromString "length"
def nilName : Name.name := Name.fromString "nil"
def nullName : Name.name := Name.fromString "null"
def tailName : Name.name := Name.fromString "tail"

def baseFix : fixed :=
  let fix := unionFixed projectionFixed overflowFixed
  let sucFn := getFunctionFixed fix (sucName, 1)
  let suc2Fn : Int → element → element → Option element := fun sz _ x => sucFn sz [x]
  insertFunctionFixed fix ((sucName, 2), fixed2 suc2Fn)

def fixMap : fixedMap :=
  { functionMap := Name_arity.Map.fromList
      [((appendName, 2), addName), ((consName, 2), sucName),
       ((lengthName, 1), projectionName 1), ((nilName, 0), numeralName 0),
       ((tailName, 1), preName)],
    relationMap := Name_arity.Map.fromList [((nullName, 1), isZeroName)] }

def listFixed : fixed := mapFixed fixMap baseFix

/- Valuations. -/
inductive valuation where | Valuation (m : Name.Map.map element)
def emptyValuation : valuation := .Valuation Name.Map.newMap
def insertValuation : valuation → Name.name × element → valuation
  | .Valuation m, vi => .Valuation (Name.Map.insert m vi)
def peekValuation : valuation → Name.name → Option element | .Valuation m, v => Name.Map.peek m v
def constantValuation (i : element) (s : Name.Set.set) : valuation :=
  Name.Set.foldl (fun (v, v') => insertValuation v' (v, i)) emptyValuation s
def zeroValuation (s : Name.Set.set) : valuation := constantValuation zeroElement s
def getValuation (v' : valuation) (v : Name.name) : Except String element :=
  match peekValuation v' v with
  | some i => .ok i
  | none => .error "Model.getValuation: incomplete valuation"

def randomValuation (r : IO.Ref StdGen) (n : Int) (vs : Name.Set.set) : IO valuation := do
  let mut acc := emptyValuation
  for v in Name.Set.toList vs do
    acc := insertValuation acc (v, ← Rand.randInt r n)
  return acc

partial def incrementValuationAux (n : Int) : List Name.name → valuation → Option valuation
  | [], _ => none
  | v :: vs, v' =>
    let (carry, i) := match incrementElement n ((getValuation v' v).toOption.getD 0) with
      | some i => (false, i) | none => (true, zeroElement)
    let v' := insertValuation v' (v, i)
    if carry then incrementValuationAux n vs v' else some v'
def incrementValuation (n : Int) (vars : Name.Set.set) (v' : valuation) : Option valuation :=
  incrementValuationAux n (Name.Set.toList vars) v'

partial def foldValuationAux (n : Int) (vars : Name.Set.set) (f : valuation × σ → σ)
    (v' : valuation) (acc : σ) : σ :=
  let acc := f (v', acc)
  match incrementValuation n vars v' with
  | none => acc
  | some v' => foldValuationAux n vars f v' acc
def foldValuation (n : Int) (vars : Name.Set.set) (f : valuation × σ → σ) (acc : σ) : σ :=
  foldValuationAux n vars f (zeroValuation vars) acc

/- A type of random finite mapping Z^n -> Z. -/

def cUNKNOWN : Int := -1

inductive table where
  | Forgetful_table
  | Array_table (a : IO.Ref (Array Int))

def newTable (n arity : Int) : IO table := do
  match elementListSpace n arity with
  | none => return .Forgetful_table
  | some space => return .Array_table (← IO.mkRef (Array.replicate space.toNat cUNKNOWN))

def randomResult (r : IO.Ref StdGen) (vR : Int) : IO Int := Rand.randInt r vR

def lookupTable (r : IO.Ref StdGen) (n vR : Int) (t : table) (elts : List element) : IO Int := do
  match t with
  | .Forgetful_table => randomResult r vR
  | .Array_table a => do
    let i := (elementListIndex n elts).toNat
    let arr ← a.get
    let res := arr[i]!
    if res ≠ cUNKNOWN then return res
    else
      let res ← randomResult r vR
      a.set (arr.set! i res)
      return res

def updateTable (n : Int) (t : table) (elts_r : List element × Int) : IO Unit := do
  match t with
  | .Forgetful_table => return ()
  | .Array_table a => do
    let i := (elementListIndex n elts_r.1).toNat
    let arr ← a.get
    a.set (arr.set! i elts_r.2)

/-- A type of random finite mappings name * arity -> Z^arity -> Z. -/
structure tables where
  domainSize : Int
  rangeSize : Int
  tableMap : IO.Ref (Name_arity.Map.map table)

def newTables (n vR : Int) : IO tables := do
  return { domainSize := n, rangeSize := vR, tableMap := ← IO.mkRef Name_arity.Map.newMap }

def getTables (tbls : tables) (n_a : Name_arity.nameArity) : IO table := do
  let m ← tbls.tableMap.get
  match Name_arity.Map.peek m n_a with
  | some t => return t
  | none =>
    let t ← newTable tbls.domainSize n_a.2
    tbls.tableMap.set (Name_arity.Map.insert m (n_a, t))
    return t

def lookupTables (r : IO.Ref StdGen) (tbls : tables) (n_elts : Name.name × List element) : IO Int := do
  let a := Int.ofNat n_elts.2.length
  let t ← getTables tbls (n_elts.1, a)
  lookupTable r tbls.domainSize tbls.rangeSize t n_elts.2

def updateTables (tbls : tables) (arg : (Name.name × List element) × Int) : IO Unit := do
  let a := Int.ofNat arg.1.2.length
  let t ← getTables tbls (arg.1.1, a)
  updateTable tbls.domainSize t (arg.1.2, arg.2)

/- A type of random finite models. -/

structure parameters where
  sizep : Int
  fixed : fixed

structure model where
  sizem : Int
  fixedFunctions : Name_arity.Map.map (List element → Option element)
  fixedRelations : Name_arity.Map.map (List element → Option Bool)
  randomFunctions : tables
  randomRelations : tables

def newModel (p : parameters) : IO model := do
  let fixFns := Name_arity.Map.transform (fun f => f p.sizep) p.fixed.functions
  let fixRels := Name_arity.Map.transform (fun rel => rel p.sizep) p.fixed.relations
  let rndFns ← newTables p.sizep p.sizep
  let rndRels ← newTables p.sizep 2
  return { sizem := p.sizep, fixedFunctions := fixFns, fixedRelations := fixRels,
           randomFunctions := rndFns, randomRelations := rndRels }

def msize (vM : model) : Int := vM.sizem
def psize (p : parameters) : Int := p.sizep

def peekFixedFunction (vM : model) (n_elts : Name.name × List element) : Option element :=
  match Name_arity.Map.peek vM.fixedFunctions (n_elts.1, Int.ofNat n_elts.2.length) with
  | none => none | some fixFn => fixFn n_elts.2
def isFixedFunction (vM : model) (n_elts : Name.name × List element) : Bool :=
  (peekFixedFunction vM n_elts).isSome
def peekFixedRelation (vM : model) (n_elts : Name.name × List element) : Option Bool :=
  match Name_arity.Map.peek vM.fixedRelations (n_elts.1, Int.ofNat n_elts.2.length) with
  | none => none | some fixRel => fixRel n_elts.2
def isFixedRelation (vM : model) (n_elts : Name.name × List element) : Bool :=
  (peekFixedRelation vM n_elts).isSome

/- A default model -/
def defaultSize : Int := 8
def defaultFixed : fixed :=
  unionListFixed [basicFixed, projectionFixed, modularFixed, setFixed, listFixed]
def default : parameters := { sizep := defaultSize, fixed := defaultFixed }

/- Taking apart terms to interpret them. -/

def destTerm (tm : Term.term) : Term.term :=
  match tm with
  | .Var _ => tm
  | .Fn _ _ =>
    match Term.stripApp tm with
    | (_, []) => tm
    | (.Var v, tms) => .Fn Term.appName (Term.term.Var v :: tms)
    | (.Fn f tms, tms') => .Fn f (tms ++ tms')

/- Interpreting terms and formulas in the model. -/

def interpretFunction (r : IO.Ref StdGen) (vM : model) (n_elts : Name.name × List element) :
    IO element := do
  match peekFixedFunction vM n_elts with
  | some res => return res
  | none => lookupTables r vM.randomFunctions n_elts

def interpretRelation (r : IO.Ref StdGen) (vM : model) (n_elts : Name.name × List element) :
    IO Bool := do
  match peekFixedRelation vM n_elts with
  | some res => return res
  | none => return intToBool (← lookupTables r vM.randomRelations n_elts)

partial def interpretTerm (r : IO.Ref StdGen) (vM : model) (vV : valuation) (tm : Term.term) :
    IO element := do
  match destTerm tm with
  | .Var v => return (getValuation vV v).toOption.getD 0
  | .Fn f tms =>
    let mut args := []
    for t in tms do
      args := args ++ [← interpretTerm r vM vV t]
    interpretFunction r vM (f, args)

def interpretAtom (r : IO.Ref StdGen) (vM : model) (vV : valuation) (atm : Atom.atom) : IO Bool := do
  let mut args := []
  for t in atm.2 do
    args := args ++ [← interpretTerm r vM vV t]
  interpretRelation r vM (atm.1, args)

mutual
partial def interpretFormulaAux (r : IO.Ref StdGen) (vM : model) (vN : Int)
    (vV : valuation) (fm : Formula.formula) : IO Bool := do
  match fm with
  | .True_ => return true
  | .False_ => return false
  | .Atom atm => interpretAtom r vM vV atm
  | .Not p => return !(← interpretFormulaAux r vM vN vV p)
  | .Or p q => return (← interpretFormulaAux r vM vN vV p) || (← interpretFormulaAux r vM vN vV q)
  | .And p q => return (← interpretFormulaAux r vM vN vV p) && (← interpretFormulaAux r vM vN vV q)
  | .Imp p q => interpretFormulaAux r vM vN vV (.Or (.Not p) q)
  | .Iff p q => return (← interpretFormulaAux r vM vN vV p) == (← interpretFormulaAux r vM vN vV q)
  | .Forall v p => interpretForall r vM vN vV p v vN
  | .Exists v p => interpretFormulaAux r vM vN vV (.Not (.Forall v (.Not p)))
partial def interpretForall (r : IO.Ref StdGen) (vM : model) (vN : Int)
    (vV : valuation) (fm : Formula.formula) (v : Term.var) (i : Int) : IO Bool := do
  if i = 0 then return true
  else
    let i := i - 1
    let vV' := insertValuation vV (v, i)
    return (← interpretFormulaAux r vM vN vV' fm) && (← interpretForall r vM vN vV fm v i)
end

def interpretFormula (r : IO.Ref StdGen) (vM : model) (vV : valuation) (fm : Formula.formula) :
    IO Bool := interpretFormulaAux r vM (msize vM) vV fm

def interpretLiteral (r : IO.Ref StdGen) (vM : model) (vV : valuation) (lit : Literal.literal) :
    IO Bool := do
  let b ← interpretAtom r vM vV lit.2
  return (if lit.1 then b else !b)

def interpretClause (r : IO.Ref StdGen) (vM : model) (vV : valuation) (cl : Literal.Set.set) :
    IO Bool := do
  for lit in Literal.Set.toList cl do
    if ← interpretLiteral r vM vV lit then return true
  return false

/- Check whether random groundings of a formula are true in the model.
   Note: if it's cheaper, a systematic check will be performed instead. -/

def check (r : IO.Ref StdGen)
    (interpret : IO.Ref StdGen → model → valuation → α → IO Bool)
    (maxChecks : Option Int) (vM : model) (fv : Name.Set.set) (x : α) : IO (Int × Int) := do
  let vN := msize vM
  let score (vV : valuation) (acc : Int × Int) : IO (Int × Int) := do
    if ← interpret r vM vV x then return (acc.1 + 1, acc.2) else return (acc.1, acc.2 + 1)
  let maxChecks :=
    match maxChecks with
    | none => maxChecks
    | some m => match expInt vN (Int.ofNat (Name.Set.size fv)) with
                | some n => if n ≤ m then none else maxChecks
                | none => maxChecks
  match maxChecks with
  | some m =>
    let mut acc := (0, 0)
    for _ in [0:m.toNat] do
      let vV ← randomValuation r vN fv
      acc ← score vV acc
    return acc
  | none =>
    -- systematic: fold over all valuations
    let vs := Name.Set.toList fv
    let mut acc := (0, 0)
    -- enumerate valuations via foldValuation, but score is IO → do it imperatively
    let mut cur := some (zeroValuation fv)
    let mut cont := true
    while cont do
      match cur with
      | none => cont := false
      | some vV =>
        acc ← score vV acc
        cur := incrementValuation vN fv vV
    let _ := vs
    return acc

def checkAtom (r : IO.Ref StdGen) (maxChecks : Option Int) (vM : model) (atm : Atom.atom) :
    IO (Int × Int) := check r (fun r m v a => interpretAtom r m v a) maxChecks vM (Atom.freeVars atm) atm
def checkFormula (r : IO.Ref StdGen) (maxChecks : Option Int) (vM : model) (fm : Formula.formula) :
    IO (Int × Int) := check r interpretFormula maxChecks vM (Formula.freeVars fm) fm
def checkLiteral (r : IO.Ref StdGen) (maxChecks : Option Int) (vM : model) (lit : Literal.literal) :
    IO (Int × Int) := check r interpretLiteral maxChecks vM (Literal.freeVars lit) lit
def checkClause (r : IO.Ref StdGen) (maxChecks : Option Int) (vM : model) (cl : Literal.Set.set) :
    IO (Int × Int) := check r interpretClause maxChecks vM (Literal.Set.freeVars cl) cl

/- Updating the model.  (Used to bias random models.) -/

def updateFunction (vM : model) (func_elts_elt : (Name.name × List element) × Int) : IO Unit :=
  updateTables vM.randomFunctions func_elts_elt
def updateRelation (vM : model) (rel_elts_pol : (Name.name × List element) × Bool) : IO Unit :=
  updateTables vM.randomRelations (rel_elts_pol.1, boolToInt rel_elts_pol.2)

/- A type of terms with interpretations embedded in the subterms. -/

inductive modelTerm where
  | Model_var
  | Model_fn (f : Term.functionName) (args : List modelTerm) (xs : List Int)
  deriving Inhabited

partial def modelTmAux (r : IO.Ref StdGen) (vM : model) (vV : valuation) (tm : Term.term) :
    IO (modelTerm × element) := do
  match destTerm tm with
  | .Var v => return (.Model_var, (getValuation vV v).toOption.getD 0)
  | .Fn f tms =>
    let mut tmsAcc := []
    let mut xsAcc := []
    for t in tms do
      let (mt, x) ← modelTmAux r vM vV t
      tmsAcc := tmsAcc ++ [mt]; xsAcc := xsAcc ++ [x]
    return (.Model_fn f tmsAcc xsAcc, ← interpretFunction r vM (f, xsAcc))
def modelTm (r : IO.Ref StdGen) (vM : model) (vV : valuation) (tm : Term.term) :
    IO (modelTerm × element) := modelTmAux r vM vV tm

/- Perturbations. -/

inductive perturbation where
  | Function_perturbation (fe : Term.functionName × List element) (e : element)
  | Relation_perturbation (re : Atom.relationName × List element) (b : Bool)
  deriving Inhabited

/- ---------------------------------------------------------------------- -/
/- Perturbing the model.                                                  -/
/- ---------------------------------------------------------------------- -/

def perturb (vM : model) : perturbation → IO Unit
  | .Function_perturbation fe e => updateFunction vM (fe, e)
  | .Relation_perturbation re b => updateRelation vM (re, b)

mutual
partial def pertTerm (r : IO.Ref StdGen) (vM : model) (target : List element)
    (tm : modelTerm) (acc : List perturbation) : IO (List perturbation) := do
  match target with
  | [] => return acc
  | _ =>
    match tm with
    | .Model_var => return acc
    | .Model_fn func tms xs =>
      let onTarget (ys : List element) : IO Bool := do
        return target.contains (← interpretFunction r vM (func, ys))
      let func_xs := (func, xs)
      let acc ←
        if isFixedFunction vM func_xs then pure acc
        else pure (Mlist.foldl (fun (y, acc) => perturbation.Function_perturbation func_xs y :: acc) acc target)
      pertTerms r vM onTarget tms xs acc
partial def pertTerms (r : IO.Ref StdGen) (vM : model) (onTarget : List element → IO Bool)
    (tms : List modelTerm) (xs : List element) (acc : List perturbation) :
    IO (List perturbation) :=
  pertTermsGo r vM onTarget [] tms xs acc
partial def pertTermsGo (r : IO.Ref StdGen) (vM : model) (onTarget : List element → IO Bool)
    (ys : List element) (tms : List modelTerm) (xs : List element) (acc : List perturbation) :
    IO (List perturbation) := do
  let vN := msize vM
  match tms, xs with
  | [], [] => return acc
  | tm :: tms, x :: xs =>
    -- filterElements pred : descending i in [0,vN) with pred i
    let mut target := []
    let mut i := vN
    while i > 0 do
      i := i - 1
      let ok ← (if i = x then pure false else onTarget (ys.reverseAux (i :: xs)))
      if ok then target := i :: target
    let acc ← pertTerm r vM target tm acc
    pertTermsGo r vM onTarget (x :: ys) tms xs acc
  | _, _ => return acc
end

def pertAtom (r : IO.Ref StdGen) (vM : model) (vV : valuation) (target : Bool)
    (atm : Atom.atom) (acc : List perturbation) : IO (List perturbation) := do
  let (rel, tms) := atm
  let onTarget (ys : List element) : IO Bool := do
    return (← interpretRelation r vM (rel, ys)) == target
  let mut tmsAcc := []
  let mut xsAcc := []
  for t in tms do
    let (mt, x) ← modelTm r vM vV t
    tmsAcc := tmsAcc ++ [mt]; xsAcc := xsAcc ++ [x]
  let rel_xs := (rel, xsAcc)
  let acc ←
    if isFixedRelation vM rel_xs then pure acc
    else pure (perturbation.Relation_perturbation rel_xs target :: acc)
  pertTerms r vM onTarget tmsAcc xsAcc acc

def pertLiteral (r : IO.Ref StdGen) (vM : model) (vV : valuation)
    (arg : Literal.literal × List perturbation) : IO (List perturbation) :=
  pertAtom r vM vV arg.1.1 arg.1.2 arg.2

def pertClause (r : IO.Ref StdGen) (vM : model) (vV : valuation) (cl : Literal.Set.set)
    (acc : List perturbation) : IO (List perturbation) := do
  let mut cur := acc
  for lit in Literal.Set.toList cl do
    cur ← pertLiteral r vM vV (lit, cur)
  return cur

def pickPerturb (r : IO.Ref StdGen) (vM : model) (perts : List perturbation) : IO Unit := do
  if Mlist.null perts then return ()
  else
    let i ← Rand.randInt r (Int.ofNat perts.length)
    perturb vM (perts[i.toNat]!)

def perturbClause (r : IO.Ref StdGen) (vM : model) (vV : valuation) (cl : Literal.Set.set) :
    IO Unit := do
  pickPerturb r vM (← pertClause r vM vV cl [])

end Model

/- -- Active: the active set of clauses (`module Active`) --------------------/
namespace Active

open Ax_cj

/- A type of active clause sets. -/
structure simplifyT where
  subsumes : Bool
  reduce : Bool
  rewrites : Bool

structure parameters where
  clause : Clause.parameters
  prefactor : simplifyT
  postfactor : simplifyT

structure active_t where
  parameters : parameters
  clauses : Intmap.map Clause.clause
  units : Units.units
  rewrite : Rewrite.rewrite
  subsume : Subsume.subsume Clause.clause
  literals : Literal_net.literalNet (Clause.clause × Literal.literal)
  equations : Term_net.termNet (Clause.clause × Literal.literal × Rewrite.orient × Term.term)
  subterms : Term_net.termNet (Clause.clause × Literal.literal × Term.path × Term.term)
  allSubterms : Term_net.termNet (Clause.clause × Term.term)

inductive active where | Active (a : active_t)

def getSubsume : active → Subsume.subsume Clause.clause | .Active a => a.subsume
def setRewrite : active → Rewrite.rewrite → active
  | .Active a, rewrite => .Active { a with rewrite := rewrite }

/- Basic operations. -/
def maxSimplify : simplifyT := { subsumes := true, reduce := true, rewrites := true }
def default : parameters :=
  { clause := Clause.default, prefactor := maxSimplify, postfactor := maxSimplify }

def empty (parameters : parameters) : active :=
  let ordering := parameters.clause.ordering
  .Active
    { parameters := parameters, clauses := Intmap.newMap, units := Units.empty,
      rewrite := Rewrite.newRewrite (Knuth_bendix_order.compare ordering),
      subsume := Subsume.newSubsume,
      literals := Literal_net.newNet ⟨false⟩, equations := Term_net.newNet ⟨false⟩,
      subterms := Term_net.newNet ⟨false⟩, allSubterms := Term_net.newNet ⟨false⟩ }

def size : active → Int | .Active a => Int.ofNat (Intmap.size a.clauses)
def clauses : active → List Clause.clause
  | .Active a => Intmap.foldr (fun (_, cl, acc) => cl :: acc) [] a.clauses
def toString (act : active) : String := "Active{" ++ ToString.toString (size act) ++ "}"

def saturation (act : active) : List Clause.clause :=
  let remove (arg : Clause.clause × (List Clause.clause × Subsume.subsume Unit)) :
      List Clause.clause × Subsume.subsume Unit :=
    let (cl, (cls, subs)) := arg
    let lits := Clause.literals cl
    if Subsume.isStrictlySubsumed subs lits then (cls, subs)
    else (cl :: cls, Subsume.insert subs (lits, ()))
  let cls := clauses act
  let (cls, _) := Mlist.foldl remove ([], (Subsume.newSubsume : Subsume.subsume Unit)) cls
  let (cls, _) := Mlist.foldl remove ([], (Subsume.newSubsume : Subsume.subsume Unit)) cls
  cls

/- Simplify clauses.

   Post-rewrite simplification can enable more rewrites:

    ~(X = f(X)) \/ ~(g(Y) = f(X)) \/ ~(c = f(X))
   ---------------------------------------------- rewrite
    ~(X = f(X)) \/ ~(g(Y) = X) \/ ~(c = X)
   ---------------------------------------------- simplify
    ~(g(Y) = f(g(Y))) \/ ~(c = g(Y))
   ---------------------------------------------- rewrite
    ~(c = f(c)) \/ ~(c = g(Y))

   This was first observed in a bug discovered by Martin
   Desharnais and Jasmin Blanchett -/

partial def simplifyRewrite (rewr : Rewrite.rewrite) (cl : Clause.clause) :
    Except String (Option Clause.clause) := do
  let cl' ← Clause.rewrite rewr cl
  if Clause.equalThms cl cl' then return some cl
  else
    match ← Clause.simplify cl' with
    | none => return none
    | some cl'' =>
      if Clause.equalThms cl' cl'' then return some cl' else simplifyRewrite rewr cl''

def simplify (simp : simplifyT) (units : Units.units) (rewr : Rewrite.rewrite)
    (subs : Subsume.subsume Clause.clause) (cl : Clause.clause) :
    Except String (Option Clause.clause) := do
  match ← Clause.simplify cl with
  | none => return none
  | some cl =>
    match ← (if simp.rewrites then simplifyRewrite rewr cl else .ok (some cl)) with
    | none => return none
    | some cl =>
      let cl ← (if simp.reduce then Clause.reduce units cl else .ok cl)
      if simp.subsumes && Clause.subsumes subs cl then return none else return some cl

def simplifyActive (simp : simplifyT) : active → Clause.clause → Except String (Option Clause.clause)
  | .Active a => simplify simp a.units a.rewrite a.subsume

/- Add a clause into the active set. -/

def addUnit (units : Units.units) (cl : Clause.clause) : Except String Units.units :=
  let th := Clause.thm cl
  match Useful.total Thm.destUnit th with
  | some lit => Units.add units (lit, th)
  | none => .ok units

def addRewrite (rewrite : Rewrite.rewrite) (cl : Clause.clause) : Except String Rewrite.rewrite :=
  let th := Clause.thm cl
  match Useful.total Thm.destUnitEq th with
  | some l_r => Rewrite.add rewrite (Clause.id cl, (l_r, th))
  | none => .ok rewrite

def addSubsume (subsume : Subsume.subsume Clause.clause) (cl : Clause.clause) :
    Subsume.subsume Clause.clause := Subsume.insert subsume (Clause.literals cl, cl)

def addLiterals (literals : Literal_net.literalNet (Clause.clause × Literal.literal))
    (cl : Clause.clause) : Literal_net.literalNet (Clause.clause × Literal.literal) :=
  let add (arg : Literal.literal × Literal_net.literalNet (Clause.clause × Literal.literal)) :
      Literal_net.literalNet (Clause.clause × Literal.literal) :=
    let (lit, literals) := arg
    if Atom.isEq lit.2 then literals else Literal_net.insert literals (lit, (cl, lit))
  Literal.Set.foldl add literals (Clause.largestLiterals cl)

def addEquations
    (equations : Term_net.termNet (Clause.clause × Literal.literal × Rewrite.orient × Term.term))
    (cl : Clause.clause) :
    Term_net.termNet (Clause.clause × Literal.literal × Rewrite.orient × Term.term) :=
  let add (arg : (Literal.literal × Rewrite.orient × Term.term) ×
           Term_net.termNet (Clause.clause × Literal.literal × Rewrite.orient × Term.term)) :=
    let ((lit, ort, tm), equations) := arg
    Term_net.insert equations (tm, (cl, lit, ort, tm))
  Mlist.foldl add equations (Clause.largestEquations cl)

def addSubterms
    (subterms : Term_net.termNet (Clause.clause × Literal.literal × Term.path × Term.term))
    (cl : Clause.clause) :
    Term_net.termNet (Clause.clause × Literal.literal × Term.path × Term.term) :=
  let add (arg : (Literal.literal × Term.path × Term.term) ×
           Term_net.termNet (Clause.clause × Literal.literal × Term.path × Term.term)) :=
    let ((lit, path, tm), subterms) := arg
    Term_net.insert subterms (tm, (cl, lit, path, tm))
  Mlist.foldl add subterms (Clause.largestSubterms cl)

def addAllSubterms (allSubterms : Term_net.termNet (Clause.clause × Term.term)) (cl : Clause.clause) :
    Term_net.termNet (Clause.clause × Term.term) :=
  let add (arg : (Literal.literal × Term.path × Term.term) ×
           Term_net.termNet (Clause.clause × Term.term)) :=
    let ((_, _, tm), allSubterms) := arg
    Term_net.insert allSubterms (tm, (cl, tm))
  Mlist.foldl add allSubterms (Clause.allSubterms cl)

def addClause : active → Clause.clause → active
  | .Active a, cl =>
    .Active { a with
      clauses := Intmap.insert a.clauses (Clause.id cl, cl),
      subsume := addSubsume a.subsume cl,
      literals := addLiterals a.literals cl,
      equations := addEquations a.equations cl,
      subterms := addSubterms a.subterms cl,
      allSubterms := addAllSubterms a.allSubterms cl }

def addFactorClause : active → Clause.clause → Except String active
  | .Active a, cl => do
    let units ← addUnit a.units cl
    let rewrite ← addRewrite a.rewrite cl
    return .Active { a with units := units, rewrite := rewrite }

/- Derive (unfactored) consequences of a clause. -/

def deduceResolution (r : IO.Ref Clause.clauseId)
    (literals : Literal_net.literalNet (Clause.clause × Literal.literal)) (cl : Clause.clause)
    (arg : Literal.literal × List Clause.clause) : IO (List Clause.clause) := do
  let (lit, acc) := arg
  if Atom.isEq lit.2 then return acc
  else
    let mut cur := acc
    for cl_lit in Literal_net.unify literals (Literal.negate lit) do
      match ← Clause.resolve r cl_lit (cl, lit) with
      | .ok cl' => cur := cl' :: cur
      | .error _ => pure ()
    return cur

def deduceParamodulationWith (r : IO.Ref Clause.clauseId)
    (subterms : Term_net.termNet (Clause.clause × Literal.literal × Term.path × Term.term))
    (cl : Clause.clause)
    (arg : (Literal.literal × Rewrite.orient × Term.term) × List Clause.clause) :
    IO (List Clause.clause) := do
  let ((lit, ort, tm), acc) := arg
  let mut cur := acc
  for cl_lit_path_tm in Term_net.unify subterms tm do
    match ← Clause.paramodulate r (cl, lit, ort, tm) cl_lit_path_tm with
    | .ok cl' => cur := cl' :: cur
    | .error _ => pure ()
  return cur

def deduceParamodulationInto (r : IO.Ref Clause.clauseId)
    (equations : Term_net.termNet (Clause.clause × Literal.literal × Rewrite.orient × Term.term))
    (cl : Clause.clause)
    (arg : (Literal.literal × Term.path × Term.term) × List Clause.clause) :
    IO (List Clause.clause) := do
  let ((lit, path, tm), acc) := arg
  let mut cur := acc
  for cl_lit_ort_tm in Term_net.unify equations tm do
    match ← Clause.paramodulate r cl_lit_ort_tm (cl, lit, path, tm) with
    | .ok cl' => cur := cl' :: cur
    | .error _ => pure ()
  return cur

def deduce (r : IO.Ref Clause.clauseId) : active → Clause.clause → IO (List Clause.clause)
  | .Active a, cl => do
    let lits := Clause.largestLiterals cl
    let eqns := Clause.largestEquations cl
    let subtms := if Term_net.null a.equations then [] else Clause.largestSubterms cl
    let mut acc := []
    for lit in Literal.Set.toList lits do
      acc ← deduceResolution r a.literals cl (lit, acc)
    for eqn in eqns do
      acc ← deduceParamodulationWith r a.subterms cl (eqn, acc)
    for subtm in subtms do
      acc ← deduceParamodulationInto r a.equations cl (subtm, acc)
    return acc.reverse

/- Extract clauses from the active set that can be simplified. -/

def clause_rewritables : active → Except String Intset.set
  | .Active a => do
    let mut ids := Intset.empty
    for (id, cl) in Intmap.toList a.clauses do
      let cl' ← Clause.rewrite a.rewrite cl
      if !(Clause.equalThms cl cl') then ids := Intset.add ids id
    return ids

def orderedRedexResidues (arg : Rewrite.equation × Option Rewrite.orient) :
    List (Term.term × Term.term × Bool) :=
  match arg.2 with
  | none => []
  | some .Left_to_right => [(arg.1.1.1, arg.1.1.2, true)]
  | some .Right_to_left => [(arg.1.1.2, arg.1.1.1, true)]

def unorderedRedexResidues (arg : Rewrite.equation × Option Rewrite.orient) :
    List (Term.term × Term.term × Bool) :=
  match arg.2 with
  | none => [(arg.1.1.1, arg.1.1.2, false), (arg.1.1.2, arg.1.1.1, false)]
  | some _ => []

def rewrite_rewritables : active → List Int → Intset.set
  | .Active a, rewr_ids =>
    let ordering := a.parameters.clause.ordering
    let order := Knuth_bendix_order.compare ordering
    let addRewr (arg : Int × Intset.set) : Intset.set :=
      if Intmap.inDomain arg.1 a.clauses then Intset.add arg.2 arg.1 else arg.2
    let addReduce (arg : (Term.term × Term.term × Bool) × Intset.set) : Intset.set :=
      let ((l, rr, ord), acc) := arg
      let isValidRewr (tm : Term.term) : Bool :=
        match Useful.total (fun x => Substitute.matchTerms Substitute.empty l x) tm with
        | none => false
        | some sub =>
          ord || (order tm (Substitute.subst (Substitute.normalize sub) rr) = some 1)
      let addRed (arg2 : (Clause.clause × Term.term) × Intset.set) : Intset.set :=
        let ((cl, tm), acc) := arg2
        let id := Clause.id cl
        if Intset.member id acc then acc
        else if !(isValidRewr tm) then acc
        else Intset.add acc id
      Mlist.foldl addRed acc (Term_net.matched a.allSubterms l)
    let addEquation (redexResidues : (Rewrite.equation × Option Rewrite.orient) →
        List (Term.term × Term.term × Bool)) (arg : Int × Intset.set) : Intset.set :=
      match Rewrite.peek a.rewrite arg.1 with
      | none => arg.2
      | some eqn_ort => Mlist.foldl addReduce arg.2 (redexResidues eqn_ort)
    let ids := Intset.empty
    let ids := Mlist.foldl addRewr ids rewr_ids
    let ids := Mlist.foldl (fun p => addEquation orderedRedexResidues p) ids rewr_ids
    let ids := Mlist.foldl (fun p => addEquation unorderedRedexResidues p) ids rewr_ids
    ids

def choose_clause_rewritables (act : active) (ids : List Int) : Bool := size act ≤ Int.ofNat ids.length

def rewritables (act : active) (ids : List Int) : Except String Intset.set :=
  if choose_clause_rewritables act ids then clause_rewritables act
  else .ok (rewrite_rewritables act ids)

def delete : active → Intset.set → active
  | .Active a, ids =>
    if Intset.null ids then .Active a
    else
      let idPred (id : Int) : Bool := !(Intset.member id ids)
      let clausePred (cl : Clause.clause) : Bool := idPred (Clause.id cl)
      .Active { a with
        clauses := Intmap.filter (fun x => idPred x.1) a.clauses,
        subsume := Subsume.filter clausePred a.subsume,
        literals := Literal_net.filter (fun x => clausePred x.1) a.literals,
        equations := Term_net.filter (fun x => clausePred x.1) a.equations,
        subterms := Term_net.filter (fun x => clausePred x.1) a.subterms,
        allSubterms := Term_net.filter (fun x => clausePred x.1) a.allSubterms }

def extract_rewritables : active → Except String (active × List Clause.clause)
  | .Active a => do
    if Rewrite.isReduced a.rewrite then return (.Active a, [])
    else
      let (rewrite, ids) ← Rewrite.reduce' a.rewrite
      let act := setRewrite (.Active a) rewrite
      let ids ← rewritables act ids
      let cls := Intset.transform (fun id => match Intmap.get a.clauses id with
                                             | .ok c => c | .error _ => panic! "extract") ids
      return (delete act ids, cls)

/- Factor clauses. -/

def prefactor_simplify : active → Subsume.subsume Clause.clause → Clause.clause →
    Except String (Option Clause.clause)
  | .Active a, subsume => simplify a.parameters.prefactor a.units a.rewrite subsume
def postfactor_simplify : active → Subsume.subsume Clause.clause → Clause.clause →
    Except String (Option Clause.clause)
  | .Active a, subsume => simplify a.parameters.postfactor a.units a.rewrite subsume

def sort_utilitywise (l : List Clause.clause) : List Clause.clause :=
  let utility (cl : Clause.clause) : Int :=
    match Literal.Set.size (Clause.literals cl) with
    | 0 => -1
    | 1 => if Thm.isUnitEq (Clause.thm cl) then 0 else 1
    | n => Int.ofNat n
  Mlist.sortMap utility Useful.intCompare l

mutual
partial def post_factor (r : IO.Ref Clause.clauseId) (cl : Clause.clause)
    (asa : active × Subsume.subsume Clause.clause × List Clause.clause) :
    IO (active × Subsume.subsume Clause.clause × List Clause.clause) := do
  let (act, subsume, acc) := asa
  match postfactor_simplify act subsume cl with
  | .error _ => return asa
  | .ok none => return asa
  | .ok (some cl') =>
    if Clause.equalThms cl' cl then
      match addFactorClause act cl with
      | .error _ => return asa
      | .ok act => return (act, addSubsume subsume cl, cl :: acc)
    else
      -- If the clause was changed in the post-factor simplification
      -- step, then it may have altered the set of largest literals
      -- in the clause. The safest thing to do is to factor again.
      factor1 r cl' asa
partial def factor1 (r : IO.Ref Clause.clauseId) (cl : Clause.clause)
    (asa : active × Subsume.subsume Clause.clause × List Clause.clause) :
    IO (active × Subsume.subsume Clause.clause × List Clause.clause) := do
  let facs ← Clause.factor r cl
  let cls := sort_utilitywise (cl :: (facs.toOption.getD []))
  let mut cur := asa
  for c in cls do
    cur ← post_factor r c cur
  return cur
end

def pre_factor (r : IO.Ref Clause.clauseId) (cl : Clause.clause)
    (asa : active × Subsume.subsume Clause.clause × List Clause.clause) :
    IO (active × Subsume.subsume Clause.clause × List Clause.clause) := do
  let (act, subsume, _) := asa
  match prefactor_simplify act subsume cl with
  | .error _ => return asa
  | .ok none => return asa
  | .ok (some cl) => factor1 r cl asa

partial def factor'' (r : IO.Ref Clause.clauseId) (act : active) (acc : List Clause.clause) :
    List Clause.clause → IO (active × List Clause.clause)
  | [] => return (act, acc.reverse)
  | cls => do
    let cls := sort_utilitywise cls
    let subsume := getSubsume act
    let mut cur := (act, subsume, acc)
    for cl in cls do
      cur ← pre_factor r cl cur
    let (act, _, acc) := cur
    match extract_rewritables act with
    | .error _ => return (act, acc.reverse)
    | .ok (act, cls) => factor'' r act acc cls

def factor (r : IO.Ref Clause.clauseId) (act : active) (cls : List Clause.clause) :
    IO (active × List Clause.clause) := factor'' r act [] cls

/- Create a new active clause set and initialize clauses. -/

def mk_clause (r : IO.Ref Clause.clauseId) (params : Clause.parameters) (th : Thm.thm) :
    IO Clause.clause := Clause.newClause r params th

def newActive (r : IO.Ref Clause.clauseId) (parameters : parameters) (ths : ax_cj_thm) :
    IO (active × ax_cj_cl) := do
  let clause := parameters.clause
  let act := empty parameters
  let mkAxioms ← ths.axioms_thm.mapM (mk_clause r clause)
  let (act, axioms) ← factor r act mkAxioms
  let mkConj ← ths.conjecture_thm.mapM (mk_clause r clause)
  let (act, conjecture) ← factor r act mkConj
  return (act, { axioms_cl := axioms, conjecture_cl := conjecture })

/- Add a clause into the active set and deduce all consequences. -/

def add (r : IO.Ref Clause.clauseId) (gen : IO.Ref Int) (act : active) (cl : Clause.clause) :
    IO (active × List Clause.clause) := do
  match simplifyActive maxSimplify act cl with
  | .error _ => return (act, [])
  | .ok none => return (act, [])
  | .ok (some cl') =>
    if Clause.isContradiction cl' then return (act, [cl'])
    else if !(Clause.equalThms cl cl') then factor r act [cl']
    else
      let act := addClause act cl
      let cl ← Clause.freshVars gen cl
      let cls ← deduce r act cl
      factor r act cls

end Active

/- -- Waiting: the waiting set of clauses (`module Waiting`) -----------------/
namespace Waiting

open Ax_cj

/- A type of waiting sets of clauses. -/
abbrev weight := Float

structure modelParameters where
  model : Model.parameters
  initialPerturbations : Int
  maxChecks : Option Int
  perturbations : Int
  weight : weight

structure parameters where
  symbolsWeight : weight
  variablesWeight : weight
  literalsWeight : weight
  modelsP : List modelParameters

abbrev distance := Float

structure waiting_t where
  parameters : parameters
  clauses : Heap.Heap (weight × (distance × Clause.clause))
  models : List Model.model

inductive waiting where | Waiting (w : waiting_t)

/- Basic operations. -/
def defaultModels : List modelParameters :=
  [{ model := Model.default, initialPerturbations := 100, maxChecks := some 20,
     perturbations := 0, weight := 1.0 }]
def default : parameters :=
  { symbolsWeight := 1.0, literalsWeight := 1.0, variablesWeight := 1.0, modelsP := defaultModels }

def size : waiting → Int | .Waiting w => Heap.size w.clauses
def toString (w : waiting) : String := "Waiting{" ++ ToString.toString (size w) ++ "}"

/- Perturbing the models. -/

abbrev modelClause := Name.Set.set × Thm.clause

def mkModelClause (cl : Clause.clause) : modelClause :=
  let lits := Clause.literals cl
  (Literal.Set.freeVars lits, lits)
def mkModelClauses (l : List Clause.clause) : List modelClause := l.map mkModelClause

def perturbModel (r : IO.Ref StdGen) (vM : Model.model) (cls : List modelClause) (n : Int) :
    IO Unit := do
  if Mlist.null cls then return ()
  else
    let vN := Model.msize vM
    for _ in [0:n.toNat] do
      for (fv, cl) in cls do
        let vV ← Model.randomValuation r vN fv
        if ← Model.interpretClause r vM vV cl then pure ()
        else Model.perturbClause r vM vV cl

def initialModel (r : IO.Ref StdGen) (axioms conjecture : List modelClause)
    (parm : modelParameters) : IO Model.model := do
  let m ← Model.newModel parm.model
  perturbModel r m conjecture parm.initialPerturbations
  perturbModel r m axioms parm.initialPerturbations
  return m

def checkModels (r : IO.Ref StdGen) (parms : List modelParameters) (models : List Model.model)
    (fvcl : modelClause) : IO Float := do
  let (fv, cl) := fvcl
  let mut z : Float := 1.0
  for (parm, model) in parms.zip models do
    let (vT, vF) ← Model.check r Model.interpretClause parm.maxChecks model fv cl
    -- OCaml: `1.0 +. float vT /. float (vT+vF) ** weight` — `**` binds tighter than
    -- `/.`, so the exponent applies to the denominator only.
    z := (1.0 + Float.ofInt vT / (Float.ofInt (vT + vF)) ^ parm.weight) * z
  return z

def perturbModels (r : IO.Ref StdGen) (parms : List modelParameters) (models : List Model.model)
    (cls : List modelClause) : IO Unit := do
  for (parm, model) in parms.zip models do
    perturbModel r model cls parm.perturbations

/- Clause weights. -/

def clauseSymbols (cl : Literal.Set.set) : Float := Float.ofInt (Literal.Set.typedSymbols cl)
def clauseVariables (cl : Literal.Set.set) : Float :=
  Float.ofInt (Int.ofNat (Name.Set.size (Literal.Set.freeVars cl)) + 1)
def clauseLiterals (cl : Literal.Set.set) : Float := Float.ofInt (Int.ofNat (Literal.Set.size cl))
def clausePriority (cl : Clause.clause) : Float := 1e-12 * Float.ofInt (Clause.id cl)

def clauseWeight (r : IO.Ref StdGen) (parm : parameters) (mods : List Model.model)
    (dist : distance) (mcl : modelClause) (cl : Clause.clause) : IO weight := do
  let lits := Clause.literals cl
  let symbolsW := clauseSymbols lits ^ parm.symbolsWeight
  let variablesW := clauseVariables lits ^ parm.variablesWeight
  let literalsW := clauseLiterals lits ^ parm.literalsWeight
  let modelsW ← checkModels r parm.modelsP mods mcl
  let weight := dist * symbolsW * variablesW * literalsW * modelsW
  let weight := weight + clausePriority cl
  return weight

/- Adding new clauses. -/

def add' (r : IO.Ref StdGen) : waiting → distance → List modelClause → List Clause.clause →
    IO waiting
  | .Waiting w, dist, mcls, cls => do
    let modelParameters := w.parameters.modelsP
    let dist := dist + Float.log (Float.ofInt (Int.ofNat cls.length))
    let mut clauses := w.clauses
    for (mcl, cl) in mcls.zip cls do
      let weight ← clauseWeight r w.parameters w.models dist mcl cl
      clauses := Heap.add clauses (weight, (dist, cl))
    perturbModels r modelParameters w.models mcls
    return .Waiting { w with clauses := clauses }

def add (r : IO.Ref StdGen) (w : waiting) (dist_cls : distance × List Clause.clause) : IO waiting := do
  if Mlist.null dist_cls.2 then return w
  else add' r w dist_cls.1 (mkModelClauses dist_cls.2) dist_cls.2

def cmp (a b : weight × (distance × Clause.clause)) : Int :=
  if a.1 < b.1 then -1 else if a.1 = b.1 then 0 else 1

def empty (r : IO.Ref StdGen) (parameters : parameters) (axioms conjecture : List modelClause) :
    IO waiting := do
  let clauses := Heap.newHeap cmp
  let models ← parameters.modelsP.mapM (initialModel r axioms conjecture)
  return .Waiting { parameters := parameters, clauses := clauses, models := models }

def newWaiting (r : IO.Ref StdGen) (parameters : parameters) (cls : ax_cj_cl) : IO waiting := do
  let mAxioms := mkModelClauses cls.axioms_cl
  let mConjecture := mkModelClauses cls.conjecture_cl
  let w ← empty r parameters mAxioms mConjecture
  if Mlist.null cls.axioms_cl && Mlist.null cls.conjecture_cl then return w
  else add' r w 0.0 (mAxioms ++ mConjecture) (cls.axioms_cl ++ cls.conjecture_cl)

/- Removing the lightest clause. -/

def remove : waiting → Option ((distance × Clause.clause) × waiting)
  | .Waiting w =>
    if Heap.null w.clauses then none
    else match Heap.remove w.clauses with
         | .ok ((_, dcl), clauses) => some (dcl, .Waiting { w with clauses := clauses })
         | .error _ => none

end Waiting

/- -- Resolution: the resolution proof procedure (`module Resolution`) -------/
namespace Resolution

open Ax_cj

/- A type of resolution proof procedures. -/
structure parameters where
  activeP : Active.parameters
  waitingP : Waiting.parameters

structure resolution_t where
  parameters : parameters
  active : Active.active
  waiting : Waiting.waiting

inductive resolution where | Resolution (r : resolution_t)

/- Basic operations. -/
def default : parameters := { activeP := Active.default, waitingP := Waiting.default }

def newResolution (r : IO.Ref StdGen) (idr : IO.Ref Clause.clauseId)
    (parameters : parameters) (ths : ax_cj_thm) : IO resolution := do
  let (active, cls) ← Active.newActive idr parameters.activeP ths  -- cls = factored ths
  let waiting ← Waiting.newWaiting r parameters.waitingP cls
  return .Resolution { parameters := parameters, active := active, waiting := waiting }

def active : resolution → Active.active | .Resolution r => r.active
def waiting : resolution → Waiting.waiting | .Resolution r => r.waiting

inductive decision where
  | Contradiction (th : Thm.thm)
  | Satisfiable (ths : List Thm.thm)

inductive state where
  | Decided (d : decision)
  | Undecided (res : resolution)

/- The main proof loop. -/

def iterate (r : IO.Ref StdGen) (idr : IO.Ref Clause.clauseId) (gen : IO.Ref Int) :
    resolution → IO state
  | .Resolution res => do
    match Waiting.remove res.waiting with
    | none =>
      let sat := decision.Satisfiable ((Active.saturation res.active).map Clause.thm)
      return .Decided sat
    | some ((d, cl), waiting) =>
      if Clause.isContradiction cl then
        return .Decided (.Contradiction (Clause.thm cl))
      else
        let (active, cls) ← Active.add idr gen res.active cl
        let waiting ← Waiting.add r waiting (d, cls)
        return .Undecided (.Resolution { res with active := active, waiting := waiting })

partial def loop (r : IO.Ref StdGen) (idr : IO.Ref Clause.clauseId) (gen : IO.Ref Int)
    (res : resolution) : IO decision := do
  match ← iterate r idr gen res with
  | .Decided dec => return dec
  | .Undecided res => loop r idr gen res

end Resolution

/- -- Loop: the basic Metis loop (`module Loop`) ----------------------------/
namespace Loop

open Ax_cj

partial def loop (r : IO.Ref StdGen) (idr : IO.Ref Clause.clauseId) (gen : IO.Ref Int)
    (res : Resolution.resolution) : IO (Option Resolution.decision) := do
  match ← Resolution.iterate r idr gen res with
  | .Decided dec => return some dec
  | .Undecided res => loop r idr gen res

/-- `run rules`: run Metis on the given axioms, returning the contradiction thm. -/
def run (r : IO.Ref StdGen) (idr : IO.Ref Clause.clauseId) (gen : IO.Ref Int)
    (rules : List Thm.thm) : IO (Except String Thm.thm) := do
  let ths : ax_cj_thm := { axioms_thm := rules, conjecture_thm := [] }
  let res ← Resolution.newResolution r idr Resolution.default ths
  match ← loop r idr gen res with
  | none => return .error "metis: timeout"
  | some (.Contradiction thm) => return .ok thm
  | some (.Satisfiable _) => return .error "metis: found satisfiable assignment"

end Loop

end Prover

/- =========================================================================
   HOL Light integration layer.
   ========================================================================= -/

open HolCore.Metis.Prover

/- -- Preterm helpers (`module Preterm`) -----------------------------------
   `Metis_debug` (the show/hide-types user printer) is debug-only and dropped. -/
namespace MetisPreterm

open HolCore.Preterm (preterm dpty pretype_of_type preterm_of_term)

/-- `mk_negp pt = ~pt` (as a preterm).  `negp` is `preterm_of_term \`~\``,
    an action: metis.ml parses the quotation on every call. -/
def mk_negp (negp : IO preterm) (pt : preterm) : IO preterm := do
  return .Combp (← negp) pt
/-- `mk_eqp (ps,pt) = (= ps pt)`. -/
def mk_eqp (ps pt : preterm) : preterm := .Combp (.Combp (.Constp "=" dpty) ps) pt
def mk_conjp (conjp ps pt : preterm) : preterm := .Combp (.Combp conjp ps) pt
def mk_disjp (disjp : IO preterm) (ps pt : preterm) : IO preterm := do
  return .Combp (.Combp (← disjp) ps) pt

/-- `list_mk_combp (h, t) = rev_itlist (fun x acc -> Combp (acc, x)) t h`. -/
def list_mk_combp (h : preterm) (t : List preterm) : preterm :=
  HolCore.Lib.rev_itlist (fun x acc => preterm.Combp acc x) t h

/-- `list_mk_disjp`: build a disjunction preterm (falsity for empty).
    `falsityp` and `disjp` parse `F` and `\/` when run, as in metis.ml.
    `itlist (curry mk_disjp) t h`: the innermost disjunction is built first. -/
def list_mk_disjp (falsityp disjp : IO preterm) : List preterm → IO preterm
  | [] => falsityp
  | h :: t => go t h
where
  go : List preterm → preterm → IO preterm
    | [], b => pure b
    | x :: xs, b => do mk_disjp disjp x (← go xs b)

/-- typechecking a preterm with constants fails,
    therefore we convert constants to variables before type checking
    type checking converts the variables back to the corresponding constants -/
partial def unconst_preterm : preterm → Except String preterm
  | .Varp s pty => .ok (.Varp s pty)
  | .Constp s pty => .ok (.Varp s pty)
  | .Combp l r => do return .Combp (← unconst_preterm l) (← unconst_preterm r)
  | .Typing ptm pty => do return .Typing (← unconst_preterm ptm) pty
  | _ => .error "unconst_preterm"

/-- `env_of_preterm`: collect `(name, pretype)` from variable preterms. -/
partial def env_of_preterm : preterm → Except String (List (String × HolCore.Preterm.pretype))
  | .Varp s pty => .ok [(s, pty)]
  | .Constp _ _ => .ok []
  | .Combp l r => do return (← env_of_preterm l) ++ (← env_of_preterm r)
  | .Typing ptm _ => env_of_preterm ptm
  | _ => .error "env_of_preterm"

/-- `env_of_th th = env_of_preterm (preterm_of_term (concl th))`. -/
def env_of_th (th : thm) : Except String (List (String × HolCore.Preterm.pretype)) :=
  env_of_preterm (preterm_of_term (concl th))
def env_of_ths (ths : List thm) : Except String (List (String × HolCore.Preterm.pretype)) := do
  let mut acc := []
  for th in ths do
    acc := acc ++ (← env_of_th th)
  return acc

end MetisPreterm

/- -- Metis_mapping: HOL ↔ Metis FOL via preterms (`module Metis_mapping`) --
   Reuses `Meson.reset_consts/fol_of_const/hol_of_const` (shared `FolStores`).
   Parameterized by the shared store `S` and the HOL constants `~`, `/\`, `\/`,
   `F` (as preterms) plus `bool` pretype — supplied by Session. -/
namespace Metis_mapping

open HolCore.Preterm (preterm dpty pretype_of_type preterm_of_term)

/-- `preterm_of_const S c = preterm_of_term (hol_of_const S (int_of_string c))`. -/
def preterm_of_const (S : FolStores) (c : Name.name) : IO (Except String preterm) := do
  match ← Meson.hol_of_const S c.toInt! with
  | .error e => return .error e
  | .ok tm => return .ok (preterm_of_term tm)

def prefix_ (s : String) : String := "__" ++ s

partial def preterm_of_fol_term (S : FolStores) : Term.term → IO (Except String preterm)
  | .Var x => return .ok (.Varp (prefix_ x) dpty)
  | .Fn f args => do
    match ← preterm_of_const S f with
    | .error e => return .error e
    | .ok pf =>
      let mut pargs := []
      for a in args do
        match ← preterm_of_fol_term S a with
        | .error e => return .error e
        | .ok pa => pargs := pargs ++ [pa]
      return .ok (MetisPreterm.list_mk_combp pf pargs)

def preterm_of_predicate (S : FolStores) : Name.name → IO (Except String preterm)
  | "=" => return .ok (.Constp "=" dpty)
  | p => preterm_of_const S p

/-- `preterm_of_atom`: build a `bool`-typed atom preterm. -/
def preterm_of_atom (S : FolStores) (atm : Atom.atom) : IO (Except String preterm) := do
  match ← preterm_of_predicate S atm.1 with
  | .error e => return .error e
  | .ok pp =>
    let mut pargs := []
    for a in atm.2 do
      match ← preterm_of_fol_term S a with
      | .error e => return .error e
      | .ok pa => pargs := pargs ++ [pa]
    return .ok (.Typing (MetisPreterm.list_mk_combp pp pargs) (pretype_of_type bool_ty))

/-- `preterm_of_literal`: negate the atom preterm if the polarity is false.
    `negp` = `preterm_of_term \`~\`` (supplied). -/
def preterm_of_literal (S : FolStores) (negp : IO preterm) (lit : Literal.literal) :
    IO (Except String preterm) := do
  match ← preterm_of_atom S lit.2 with
  | .error e => return .error e
  | .ok pat => if lit.1 then return .ok pat else return .ok (← MetisPreterm.mk_negp negp pat)

def preterm_of_eq (S : FolStores) (st : Term.term × Term.term) : IO (Except String preterm) := do
  match ← preterm_of_fol_term S st.1, ← preterm_of_fol_term S st.2 with
  | .ok ps, .ok pt => return .ok (MetisPreterm.mk_eqp ps pt)
  | .error e, _ => return .error e
  | _, .error e => return .error e

/-- `typecheck env = term_of_preterm ∘ retypecheck env ∘ unconst_preterm`. -/
def typecheck (env : List (String × HolCore.Preterm.pretype)) (pt : preterm) :
    ExceptT String IO term := do
  let pt ← liftExcept (MetisPreterm.unconst_preterm pt)
  let pt ← HolCore.Preterm.retypecheck env pt
  HolCore.Preterm.term_of_preterm pt

/-- `typecheckl env`: type-check a list by disjoining, checking, and re-splitting.
    Needs the `F`/`\/` preterms for `list_mk_disjp`. -/
def typecheckl (falsityp disjp : IO preterm) (env : List (String × HolCore.Preterm.pretype))
    (xs : List preterm) : ExceptT String IO (List term) := do
  match xs with
  | [] => return []
  | _ =>
    let tm ← typecheck env (← MetisPreterm.list_mk_disjp falsityp disjp xs)
    return disjuncts tm

def hol_of_term (S : FolStores) (env : List (String × HolCore.Preterm.pretype)) (tm : Term.term) :
    ExceptT String IO term := do
  let pt ← (preterm_of_fol_term S tm : IO (Except String preterm))
  typecheck env pt

def hol_of_atom (S : FolStores) (env : List (String × HolCore.Preterm.pretype)) (atm : Atom.atom) :
    ExceptT String IO term := do
  let pt ← (preterm_of_atom S atm : IO (Except String preterm))
  typecheck env pt

def hol_of_literal (S : FolStores) (negp : IO preterm)
    (env : List (String × HolCore.Preterm.pretype)) (lit : Literal.literal) :
    ExceptT String IO term := do
  let pt ← (preterm_of_literal S negp lit : IO (Except String preterm))
  typecheck env pt

def hol_of_clause (S : FolStores) (negp falsityp disjp : IO preterm)
    (env : List (String × HolCore.Preterm.pretype)) (lits : List Literal.literal) :
    ExceptT String IO term := do
  let mut pts := []
  for lit in lits do
    pts := pts ++ [← (preterm_of_literal S negp lit : IO (Except String preterm))]
  typecheck env (← MetisPreterm.list_mk_disjp falsityp disjp pts)

/-- `hol_of_substitution env = map dest_eq ∘ typecheckl env ∘ map preterm_of_eq`. -/
def hol_of_substitution (S : FolStores) (falsityp disjp : IO preterm)
    (env : List (String × HolCore.Preterm.pretype)) (eqs : List (Term.term × Term.term)) :
    ExceptT String IO (List (term × term)) := do
  let mut pts := []
  for e in eqs do
    pts := pts ++ [← (preterm_of_eq S e : IO (Except String preterm))]
  let tms ← typecheckl falsityp disjp env pts
  let mut out := []
  for tm in tms do
    out := out ++ [← liftExcept (dest_eq tm)]
  return out

end Metis_mapping

/- -- Metis_path: FOL term paths ↔ HOL Light path strings (`module Metis_path`) -/
namespace Metis_path

open HolCore.Metis.Prover

/-- The term `f 1 2 3` is encoded in HOL Light as follows:

         @
        / \
       @  3
      / \
     @  2
    / \
   f  1

    `hol_of_term_path tm path`: descend `tm` along the FOL argument-index `path`,
    returning the reached subterm and the HOL Light path-string (`l`/`r` moves). -/
partial def hol_of_term_path : Term.term → Term.path → Except String (Term.term × String)
  | tm, [] => .ok (tm, "")
  | .Fn _ args, i :: is =>
    let arity := args.length
    if !(i < Int.ofNat arity) then .error "hol_of_term_path"
    else do
      let (tm', path') ← hol_of_term_path (args.getD i.toNat default) is
      return (tm', String.ofList (List.replicate (arity - i.toNat - 1) 'l') ++ "r" ++ path')
  | _, _ => .error "hol_of_term_path"

def hol_of_atom_path (atm : Atom.atom) (path : Term.path) : Except String (Term.term × String) :=
  hol_of_term_path (.Fn atm.1 atm.2) path

def hol_of_literal_path (lit : Literal.literal) (path : Term.path) :
    Except String (Term.term × String) := do
  let (s, p) ← hol_of_atom_path lit.2 path
  return (s, if lit.1 then p else "r" ++ p)

end Metis_path

/- -- Metis_unify: FO ↔ HO unification (`module Metis_unify`) ---------------
   `verb` verbosity dropped.  Uses HOL kernel `strip_comb`/`is_var`/`is_const`.
   Parameterized by `S` (for `Meson.hol_of_const`). -/
namespace Metis_unify

open HolCore.Metis.Prover

partial def unify_fo_ho_term (S : FolStores) (vars : List term) (fat : Term.term) (tm : term)
    (m : List (Name.name × term)) : IO (Except String (List (Name.name × term))) := do
  let verb ← metis_unify_verb.get
  -- metis.ml 9652-9653
  if verb then
    stdPrintf s!"unify_fo_ho_term: fat = {Term.toString fat}, tm = {← HolCore.Printer.string_of_term tm}\n"
  match fat, tm, m with
  | .Var v, tm, m =>
    match HolCore.Lib.assoc v m with
    | .ok tm' => do
      if verb then stdPrintf "var_assoc\n"
      (if tm == tm' then pure (.ok m) else pure (.error "Unify"))
    | .error _ => do
      if verb then stdPrintf "var\n"
      if is_var tm && !(HolCore.Lib.mem tm vars) then pure (.ok ((v, tm) :: m))
      else do
        if verb then stdPrintf "Unify!\n"
        pure (.error "Unify")
  | .Fn f args, tm, m => do
    if verb then stdPrintf "fn\n"
    let (hf, hargs) := strip_comb tm
    if verb then
      stdPrintf s!"hf = {← HolCore.Printer.string_of_term hf}\n"
      stdPrintf s!"is_var: {if is_var hf then "true" else "false"}\n"
    -- assert is_const hf || is_var hf (skip assertion, matches OCaml)
    match ← Meson.hol_of_const S f.toInt! with
    | .error e => return .error e
    | .ok hconst =>
      if hf == hconst then
        -- itlist2 (unify_fo_ho_term vars) args hargs m
        if args.length ≠ hargs.length then return .error "Unify"
        else
          -- `itlist2` is a RIGHT fold: the LAST argument pair first.
          let mut cur := m
          for (a, h) in (args.zip hargs).reverse do
            match ← unify_fo_ho_term S vars a h cur with
            | .ok m' => cur := m'
            | .error e => return .error e
          return .ok cur
      else return .error "Unify"

def unify_fo_ho_atom (S : FolStores) (vars : List term) (atm : Atom.atom) (htm : term)
    (m : List (Name.name × term)) : IO (Except String (List (Name.name × term))) := do
  if atm.1 = "=" then
    match dest_eq htm with
    | .error _ => return .error "Unify"
    | .ok (hl, hr) =>
      if atm.2.length ≠ 2 then return .error "Unify"
      else
        -- `itlist2` is a RIGHT fold: `hr` first.
        let mut cur := m
        for (a, h) in (atm.2.zip [hl, hr]).reverse do
          match ← unify_fo_ho_term S vars a h cur with
          | .ok m' => cur := m' | .error e => return .error e
        return .ok cur
  else unify_fo_ho_term S vars (.Fn atm.1 atm.2) htm m

def unify_fo_ho_literal (S : FolStores) (vars : List term) (lit : Literal.literal) (htm : term)
    (m : List (Name.name × term)) : IO (Except String (List (Name.name × term))) := do
  if lit.1 then unify_fo_ho_atom S vars lit.2 htm m
  else match dest_neg htm with
       | .error _ => return .error "Unify"
       | .ok htm' => unify_fo_ho_atom S vars lit.2 htm' m

end Metis_unify

/- ---------------------------------------------------------------------- -/
/- Conversion of HOL to Metis FOL.                                         -/
/- ---------------------------------------------------------------------- -/

/- -- Metis_generate: HOL clause → Metis FOL (`module Metis_generate`) ------
   Uses `Meson.fol_of_var/fol_of_const` (shared store `S`).  `metis_name = string_of_int`. -/
namespace Metis_generate

open HolCore.Metis.Prover

def metis_name (i : Int) : Name.name := toString i

partial def metis_of_term (S : FolStores) (env consts : List term) (tm : term) :
    IO (Except String Term.term) := do
  if is_var tm && !(HolCore.Lib.mem tm consts) then
    match ← Meson.fol_of_var S tm with
    | .error e => return .error e
    | .ok code => return .ok (.Var (metis_name code))
  else
    let (f, args) := strip_comb tm
    if HolCore.Lib.mem f env then return .error "metis_of_term: higher order"
    else
      match ← Meson.fol_of_const S f with
      | .error e => return .error e
      | .ok ff =>
        let mut fargs := []
        for a in args do
          match ← metis_of_term S env consts a with
          | .error e => return .error e
          | .ok fa => fargs := fargs ++ [fa]
        return .ok (.Fn (metis_name ff) fargs)

def metis_of_atom (S : FolStores) (env consts : List term) (tm : term) :
    IO (Except String Atom.atom) := do
  -- metis.ml 9917-9921: ONE `try` covers `dest_eq` AND BOTH `metis_of_term`
  -- calls, so a failure in EITHER argument - not just a non-equation - falls
  -- through to the relation branch below.
  let eqAtom : IO (Option Atom.atom) := do
    match dest_eq tm with
    | .error _ => return none
    | .ok (l, r) =>
      match ← metis_of_term S env consts l, ← metis_of_term S env consts r with
      | .ok l', .ok r' => return some (Atom.mkEq (l', r'))
      | _, _ => return none
  match ← eqAtom with
  | some a => return .ok a
  | none =>
    let (f, args) := strip_comb tm
    if HolCore.Lib.mem f env then return .error "metis_of_atom: higher order"
    else
      match ← Meson.fol_of_const S f with
      | .error e => return .error e
      | .ok ff =>
        let mut fargs := []
        for a in args do
          match ← metis_of_term S env consts a with
          | .error e => return .error e
          | .ok fa => fargs := fargs ++ [fa]
        return .ok (metis_name ff, fargs)

def metis_of_literal (S : FolStores) (env consts : List term) (tm : term) :
    IO (Except String Literal.literal) := do
  let (pol, tm') := match dest_neg tm with | .ok t => (false, t) | .error _ => (true, tm)
  match ← metis_of_atom S env consts tm' with
  | .error e => return .error e
  | .ok atm => return .ok (pol, atm)

def metis_of_clause (S : FolStores) (th : thm) : IO (Except String Thm.thm) := do
  let lconsts := freesl (hyp th)
  let tm := concl th
  let hlits := disjuncts tm
  let mut flits := []
  for hlit in hlits do
    match ← metis_of_literal S [] lconsts hlit with
    | .error e => return .error e
    | .ok fl => flits := flits ++ [fl]
  return .ok (Thm.«axiom» (Literal.Set.fromList flits))

def metis_of_clauses (S : FolStores) (ths : List thm) : IO (Except String (List Thm.thm)) := do
  let mut acc := []
  for th in ths do
    match ← metis_of_clause S th with
    | .error e => return .error e
    | .ok c => acc := acc ++ [c]
  return .ok acc

end Metis_generate

/- -- Metis_rules: HOL derived rules for reconstruction (`module Metis_rules`) -/
namespace Metis_rules

open HolCore.Metis.Prover

/-- The TAUT-proved lemmas + rules `Metis_rules` needs (Session supplies them). -/
structure MetisRulesDeps where
  RESOLVE_1  : thm     -- !a. a ==> ~a ==> F
  RESOLVE_2L : thm     -- !a b. a \/ b ==> ~a ==> b
  RESOLVE_2R : thm     -- !a c. a ==> ~a \/ c ==> c
  RESOLVE_3  : thm     -- !a b c. a \/ b ==> ~a \/ c ==> b \/ c
  IMPL_NOT_L : thm     -- !a b. ~a ==> b <=>  a \/ b
  IMPL_NOT_R : thm     -- !a b.  a ==> b <=> ~a \/ b
  DISJ_ACI_RULE : term → IO (Except String thm)
  PURE_ONCE_REWRITE_RULE : List thm → thm → IO (Except String thm)
  mk_eq : (term × term) → IO (Except String term)

instance : Inhabited MetisRulesDeps :=
  ⟨{ RESOLVE_1 := default, RESOLVE_2L := default, RESOLVE_2R := default, RESOLVE_3 := default,
     IMPL_NOT_L := default, IMPL_NOT_R := default,
     DISJ_ACI_RULE := fun _ => pure (.error "uninit"),
     PURE_ONCE_REWRITE_RULE := fun _ _ => pure (.error "uninit"),
     mk_eq := fun _ => pure (.error "uninit") }⟩

/-- move a literal in the proof of a disjunction to the first position
    may not preserve the order of the other literals -/
def FRONT (_B : BoolThms) (D : MetisRulesDeps) (lit : term) (th : thm) :
    IO (Except String (thm × List term)) := do
  let disj := disjuncts (concl th)
  match (disj.partition (fun l => l == lit)) with
  | ([], _) => return .error "FRONT: literal not in disjunction"
  | (_, rest) =>
    let disj' := lit :: rest
    match list_mk_disj disj' with
    | .error e => return .error e
    | .ok conc' =>
      match ← D.mk_eq (concl th, conc') with
      | .error e => return .error e
      | .ok eqtm =>
        match ← D.DISJ_ACI_RULE eqtm with
        | .error e => return .error e
        | .ok eq =>
          match ← D.PURE_ONCE_REWRITE_RULE [eq] th with
          | .error e => return .error e
          | .ok th' => return .ok (th', rest)

/-- resolve two clauses, where atom has to appear at the first position of
    both clauses: positive in the first and negative in the second clause -/
def RESOLVE_N (B : BoolThms) (D : MetisRulesDeps) (atom : term) :
    List term × List term → Except String thm
  | ([], []) => B.SPEC atom D.RESOLVE_1
  | (r1, []) => do B.SPECL [atom, ← list_mk_disj r1] D.RESOLVE_2L
  | ([], r2) => do B.SPECL [atom, ← list_mk_disj r2] D.RESOLVE_2R
  | (r1, r2) => do B.SPECL [atom, ← list_mk_disj r1, ← list_mk_disj r2] D.RESOLVE_3

/-- resolve two clauses th1 and th2, where atom appears somewhere
    positive in th1 and negative in th2 -/
def RESOLVE (B : BoolThms) (D : MetisRulesDeps) (atom : term) (th1 th2 : thm) :
    IO (Except String thm) := do
  match ← FRONT B D atom th1 with
  | .error _ => return .error "resolve"
  | .ok (th1', r1) =>
    match mk_neg atom with
    | .error _ => return .error "resolve"
    | .ok natom =>
      match ← FRONT B D natom th2 with
      | .error _ => return .error "resolve"
      | .ok (th2', r2) =>
        match RESOLVE_N B D atom (r1, r2) with
        | .error _ => return .error "resolve"
        | .ok res =>
          match B.MP res th1' with
          | .error _ => return .error "resolve"
          | .ok m1 => match B.MP m1 th2' with
                      | .error _ => return .error "resolve"
                      | .ok m2 => return .ok m2

/-- given A,  tm |- C, prove A |- ~tm \/ C or
    given A, ~tm |- C, prove A |-  tm \/ C -/
def DISCH_DISJ (B : BoolThms) (D : MetisRulesDeps) (tm : term) (th : thm) :
    IO (Except String thm) := do
  match B.DISCH tm th with
  | .error e => return .error e
  | .ok impl =>
    let (tm', IMPL_NOT) := match dest_neg tm with
      | .ok t => (t, D.IMPL_NOT_L) | .error _ => (tm, D.IMPL_NOT_R)
    match B.SPECL [tm', concl th] IMPL_NOT with
    | .error e => return .error e
    | .ok eq => D.PURE_ONCE_REWRITE_RULE [eq] impl

/-- given A, tm1, .., tmn |- th, prove A |- ~tm1 \/ .. \/ ~tmn \/ th -/
def DISCH_DISJS (B : BoolThms) (D : MetisRulesDeps) (tms : List term) (th : thm) :
    IO (Except String thm) := do
  let mut cur := th
  for tm in tms.reverse do
    match ← DISCH_DISJ B D tm cur with
    | .error e => return .error e
    | .ok th' => cur := th'
  return .ok cur

end Metis_rules

/- -- Metis_reconstruct2: proof reconstruction into HOL (`module Metis_reconstruct2`) -/
namespace Metis_reconstruct2

open HolCore.Metis.Prover
open HolCore.FirstOrder.Utils.List (concat_map filter_map)

/-- Bundle of HOL primitives needed for reconstruction (Session supplies). -/
structure MetisReconDeps where
  S : FolStores
  negp : IO preterm
  falsityp : IO preterm
  disjp : IO preterm
  rules : Metis_rules.MetisRulesDeps
  EXCLUDED_MIDDLE : thm
  term_type_unify : term → term → HolCore.Drule.instantiation →
                    IO (Except String HolCore.Drule.instantiation)
  type_unify : hol_type → hol_type → List (hol_type × hol_type) →
               IO (Except String (List (hol_type × hol_type)))
  INSTANTIATE : HolCore.Drule.instantiation → thm → IO (Except String thm)
  DISJ_CANON_CONV : term → IO (Except String thm)
  PURE_ONCE_REWRITE_CONV : List thm → IO (Except String ioconv)

/-- `term_eq_mod_type t1 t2 tyinsts`: unify modulo type, requiring no term inst. -/
def term_eq_mod_type (D : MetisReconDeps) (t1 t2 : term)
    (tyinsts : List (hol_type × hol_type)) : IO (Option (List (hol_type × hol_type))) := do
  match ← D.term_type_unify t1 t2 ([], [], tyinsts) with
  | .error _ => return none
  | .ok (_, tminsts, tyinsts) =>
    -- metis.ml 9754-9758
    if ← metisverb.get then
      stdPrintf s!"unified with |tminsts| = {tminsts.length}!\n"
      for (a, b) in tminsts do
        stdPrintf s!"{← HolCore.Printer.string_of_term a} <- {← HolCore.Printer.string_of_term b}\n"
    return (if tminsts.isEmpty then some tyinsts else none)

/-- `match_elems f m (xs,ys)`: all ways of matching each `x` to a distinct `y`. -/
partial def match_elems [BEq β] (f : α → β → σ → IO (Option σ)) (m : σ) :
    List α × List β → IO (List σ)
  | ([], []) => return [m]
  | ([], _) => return []
  | (x :: xs, ys) => do
    let mut out := []
    -- OCaml removes only the CURRENT list cell (physical `!=`), so structural
    -- duplicates each remain matchable; we remove by index (eraseIdx), not by
    -- structural equality, to mirror that exactly.
    for (y, i) in ys.zipIdx do
      match ← f x y m with
      | some m' => out := out ++ (← match_elems f m' (xs, ys.eraseIdx i))
      | none => pure ()
    return out

def match_fo_ho_clause (D : MetisReconDeps) (vars : List term)
    (clausel : List Literal.literal) (disjs : List term) :
    IO (List (List (Name.name × term))) :=
  match_elems
    (fun ft ht m => do
      match ← Metis_unify.unify_fo_ho_literal D.S vars ft ht m with
      | .ok m' => return some m' | .error _ => return none)
    [] (clausel, disjs)

/-- `reorient_tysubst vars sub`. -/
def reorient_tysubst (vars : List hol_type) (sub : List (hol_type × hol_type)) :
    ExceptT String IO (List (hol_type × hol_type)) := do
  let sub' := sub.map (fun (ty, v) =>
    if HolCore.Lib.mem v vars && is_vartype ty then (v, ty) else (ty, v))
  let mut out := []
  for (ty, v) in sub' do
    out := out ++ [(← tysubst sub' ty, v)]
  return out

/-- `string_of_tminst` (metis.ml 9773). -/
def string_of_tminst (l : List (term × term)) : IO String := do
  let mut xs := []
  for (tm, v) in l do
    xs := xs ++ [(← HolCore.Printer.string_of_term tm) ++ " <- " ++ (← HolCore.Printer.string_of_term v)]
  return ", ".intercalate xs

/-- `string_of_tyinst` (metis.ml 9776). -/
def string_of_tyinst (l : List (hol_type × hol_type)) : IO String := do
  let mut xs := []
  for (ty, v) in l do
    xs := xs ++ [(← HolCore.Printer.string_of_type ty) ++ " <- " ++ (← HolCore.Printer.string_of_type v)]
  return ", ".intercalate xs

/-- `string_of_instantiation` (metis.ml 9779). -/
def string_of_instantiation (tminst : List (term × term)) (tyinst : List (hol_type × hol_type)) :
    IO String := do
  return "([" ++ (← string_of_tminst tminst) ++ "], [" ++ (← string_of_tyinst tyinst) ++ "])"

/-- `hol_of_thm axioms fth`: reconstruct the HOL theorem for FOL theorem `fth`. -/
partial def hol_of_thm (B : BoolThms) (D : MetisReconDeps) (axioms : List thm) (fth : Thm.thm) :
    ExceptT String IO thm := do
  let verb ← metisverb.get
  if verb then stdPrintf s!"hol_of_thm: {Thm.toString fth}\n"   -- metis.ml 9789
  let env ← liftExcept (MetisPreterm.env_of_ths axioms)
  let inf ← liftExcept (Proof.thmToInference fth)
  let hth : thm ← (match inf with
    | .Axiom clause => do
      let clausel := Literal.Set.toList clause
      -- maxs : for each axiom, all matchings (m, ax)
      let mut maxs : List ((List (Name.name × term)) × thm) := []
      for ax in axioms do
        let disjs := striplist Basics.dest_disj (concl ax)
        let tmvars := freesl (hyp ax)
        let ms ← (match_fo_ho_clause D tmvars clausel disjs : IO (List (List (Name.name × term))))
        for m in ms do maxs := maxs ++ [(m, ax)]
      if maxs.isEmpty then throw "hol_of_thm: no matching axiom"
      else
        let tminstOf (m : List (Name.name × term)) : List (term × term) :=
          m.map (fun (v, tm) => (mk_var (Metis_mapping.prefix_ v) (type_of tm), tm))
        -- metis.ml 9804-9805
        if verb then
          stdPrintf s!"length maxs = {maxs.length}\n"
          for (m, ax) in maxs do
            stdPrintf s!"max: {← HolCore.Printer.string_of_thm ax} with m = {← string_of_tminst (tminstOf m)}\n"
        let (m, ax) := maxs.head!
        liftExcept (INST (tminstOf m) ax)
    | .Subst fsub fth1 => do
      -- Caution: the substitution can contain elements such as "x -> f(x)"
      let th1 ← hol_of_thm B D axioms fth1
      if verb then stdPrintf s!"subst with th1 = {← HolCore.Printer.string_of_thm th1}\n"
      let fsubl := Substitute.toList fsub
      if verb then stdPrintf "before substitution lifting\n"
      let hsub ← Metis_mapping.hol_of_substitution D.S D.falsityp D.disjp env
                   (fsubl.map (fun (v, t) => (t, Term.term.Var v)))
      if verb then stdPrintf s!"subst: {← string_of_tminst hsub}\n"
      -- tyinst = itlist (fun (t,v) m -> let v' = find (name_of v' = name_of v) (frees concl th1)
      --                                 in type_unify (type_of v) (type_of v') m) hsub []
      -- tyinst = itlist (fun (t,v) m -> ... type_unify ... m) hsub []
      -- (metis.ml 9818-9820).  `itlist` is a RIGHT fold: the LAST `hsub`
      -- entry is unified first, against `[]`.  `type_unify` threads the
      -- accumulator, so the order fixes the resulting instantiation's shape.
      let mut tyinst : List (hol_type × hol_type) := []
      for (_, v) in hsub.reverse do
        match HolCore.Lib.find (fun v' => name_of v' == name_of v) (frees (concl th1)) with
        | .error _ => throw "hol_of_thm: Subst: var not found"
        | .ok v' => tyinst ← D.type_unify (type_of v) (type_of v') tyinst
      -- tminst = map (fun (t,v) -> (inst tyinst t, inst tyinst v)) hsub
      let tminst : List (term × term) :=
        hsub.map (fun (t, v) => (inst tyinst t, inst tyinst v))
      -- metis.ml 9823-9825
      if verb then
        stdPrintf s!"before instantiate of th1 = {← HolCore.Printer.string_of_thm th1} with {← string_of_instantiation tminst tyinst}\n"
      (D.INSTANTIATE ([], tminst, tyinst) th1 : IO (Except String thm))
    | .Resolve atom fth1 fth2 => do
      let th1 ← hol_of_thm B D axioms fth1
      let th2 ← hol_of_thm B D axioms fth2
      let env2 ← liftExcept (MetisPreterm.env_of_ths [th1, th2])
      let env := env2 ++ env
      -- metis.ml 9832-9835
      if verb then
        for (s, pty) in env do
          let ty ← HolCore.Preterm.type_of_pretype pty
          stdPrintf s!"{s} <- {← HolCore.Printer.string_of_type ty}\n"
      if verb then stdPrintf "before resolving\n"
      if verb then stdPrintf s!"th1 = {← HolCore.Printer.string_of_thm th1}\n"
      if verb then stdPrintf s!"th2 = {← HolCore.Printer.string_of_thm th2}\n"
      let tm1 := (striplist Basics.dest_disj (concl th1)).filter
                   (fun x => !(is_neg x))
      let tm2 := ((striplist Basics.dest_disj (concl th2)).filter is_neg).map
                   (fun x => match dest_neg x with | .ok t => t | .error _ => x)
      if verb then
        for t in tm1 do stdPrintf s!"tm1: {← HolCore.Printer.string_of_term t}\n"
        for t in tm2 do stdPrintf s!"tm2: {← HolCore.Printer.string_of_term t}\n"
      let hatom ← Metis_mapping.hol_of_atom D.S env atom
      if verb then stdPrintf s!"hatom: {← HolCore.Printer.string_of_term hatom}\n"
      -- cands = concat_map (fun x -> match term_eq_mod_type hatom x [] with None -> []
      --   | Some m -> filter_map (fun y -> term_eq_mod_type hatom y m) tm2) tm1
      let mut cands : List (List (hol_type × hol_type)) := []
      for x in tm1 do
        match ← (term_eq_mod_type D hatom x [] : IO (Option _)) with
        | none => pure ()
        | some m =>
          for y in tm2 do
            match ← (term_eq_mod_type D hatom y m : IO (Option _)) with
            | some c => cands := cands ++ [c]
            | none => pure ()
      if verb then stdPrintf s!"{cands.length} candidates available\n"
      if cands.isEmpty then throw "hol_of_thm: Resolve: no candidates"
      else if !(cands.all (fun c => c == cands.head!)) then
        throw "hol_of_thm: Resolve: inconsistent type-instantiation candidates"
      else
        let tyinsts := cands.head!
        let tyvars := concat_map type_vars_in_term ((axioms.map hyp).flatten)
        if verb then stdPrintf "Reorienting type substitution ...\n"
        let tyinsts ← reorient_tysubst tyvars tyinsts
        if verb then stdPrintf "Resolving ...\n"
        let hatom' := inst tyinsts hatom
        let th1' ← liftExcept (INST_TYPE tyinsts th1)
        let th2' ← liftExcept (INST_TYPE tyinsts th2)
        (Metis_rules.RESOLVE B D.rules hatom' th1' th2' : IO (Except String thm))
    | .Refl term => do
      let ht ← Metis_mapping.hol_of_term D.S env term
      pure (REFL ht)
    | .Assume atom => do
      let ha ← Metis_mapping.hol_of_atom D.S env atom
      liftExcept (B.SPEC ha D.EXCLUDED_MIDDLE)
    | .Equality flit fpath ft => do
      let hlit ← Metis_mapping.hol_of_literal D.S D.negp env flit
      let (_fs, hpath) ← liftExcept (Metis_path.hol_of_literal_path flit fpath)
      let hs ← liftExcept (follow_path hpath hlit)
      let ht ← Metis_mapping.hol_of_term D.S env ft
      let m ← D.type_unify (type_of ht) (type_of hs) []
      let hlit := inst m hlit
      let hs := inst m hs
      let ht := inst m ht
      -- metis.ml 9869-9874
      if verb then
        stdPrintf s!"Trying to replace {← HolCore.Printer.string_of_term hs} : {← HolCore.Printer.string_of_type (type_of hs)} with {← HolCore.Printer.string_of_term ht} : {← HolCore.Printer.string_of_type (type_of ht)}\n"
        stdPrintf s!"In {← HolCore.Printer.string_of_term hlit}\n"
      let heq ← (D.rules.mk_eq (hs, ht) : IO (Except String term))
      -- conv = PATH_CONV hpath (PURE_ONCE_REWRITE_CONV [ASSUME heq]) — done via ioconv
      let assumeHeq ← liftExcept (ASSUME heq)
      let rwConv ← (D.PURE_ONCE_REWRITE_CONV [assumeHeq]
                     : IO (Except String ioconv))
      let conv : ioconv := HolCore.Simp.pathConvIO hpath rwConv
      let hlitAssume ← liftExcept (ASSUME hlit)
      let hlit' ← (HolCore.Simp.convRuleIO conv hlitAssume : IO (Except String thm))
      if verb then
        stdPrintf s!"hlit = {← HolCore.Printer.string_of_term hlit}, hlit' = {← HolCore.Printer.string_of_thm hlit'}\n"
      -- OCaml asserts: if hs <> ht then the rewrite must have changed the literal.
      if !(hs == ht) && concl hlit' == hlit then
        throw "hol_of_thm: Equality: rewrite did not change the literal"
      -- DISCH_DISJS [heq; hlit] hlit'  (error propagates; OCaml relabels as "equality")
      (Metis_rules.DISCH_DISJS B D.rules [heq, hlit] hlit' : IO (Except String thm)))
  -- eliminate duplicates in clause : CONV_RULE DISJ_CANON_CONV hth
  let canonTh ← (D.DISJ_CANON_CONV (concl hth) : IO (Except String thm))
  let hth ← liftExcept (CONV_RULE (fun _ => Except.ok canonTh) hth)
  -- metis.ml 9888-9893
  if verb then
    stdPrintf "hol_of_thm finished\n"
    let hth' ← Metis_mapping.hol_of_clause D.S D.negp D.falsityp D.disjp env
                 (Literal.Set.toList (Thm.clause_ fth))
    stdPrintf s!"hol_of_thm returned:\n{← HolCore.Printer.string_of_term (concl hth)}\n for\n{← HolCore.Printer.string_of_term hth'}\n"
  return hth

end Metis_reconstruct2

/- -- Metis: the main Metis module (`module Metis`) --------------------------/
namespace Metis

open HolCore.Metis.Prover

/-- Repeatedly `SPEC` a genvar under leading universals (as in GEN_MESON_TAC). -/
private partial def specGenvarLoop (B : BoolThms) (th : thm) : IO thm := do
  match Basics.dest_forall (concl th) with
  | .error _ => return th
  | .ok (v, _) =>
    let gv ← genvar (type_of v)
    match B.SPEC gv th with
    | .error _ => return th
    | .ok th' => specGenvarLoop B th'

/-- Slightly modified tactic from meson.ml.  (`FOL_PREPARE_TAC ths`: the
    goal-preparation pipeline.)  Reuses the shared Meson tactic-dependency
    bundle `D` (identical convs/tactics). `splitLimit` is the `!split_limit`
    ref value. -/
def FOL_PREPARE_TAC (B : BoolThms) (D : Meson.MesonTacDeps) (splitLimit : Int) (ths : List thm) :
    tactic := fun g => do
  let assumeTac : thm_tactic := fun th => Tactics.ASSUME_TAC B th
  let betaTopDepth : ioconv := HolCore.Simp.topDepthConvIO (fun t => pure (HolCore.Equal.BETA_CONV t))
  let frontConv : ioconv :=
    HolCore.Simp.thencIO D.presimp (HolCore.Simp.thencIO betaTopDepth
      (HolCore.Simp.thencIO D.lambdaElim (HolCore.Simp.thencIO D.condsCelim D.quantBool)))
  let nnfSkolem : thm → IO (Except String thm) :=
    fun th => HolCore.Simp.convRuleIO (HolCore.Simp.thencIO D.nnf D.skolem) th
  let prenexCnf : thm → IO (Except String thm) :=
    fun th => HolCore.Simp.convRuleIO (HolCore.Simp.thencIO D.prenex D.weakCnf) th
  let assocRule : thm → IO (Except String thm) := fun th => HolCore.Simp.convRuleIO D.assocDisj th
  let specGenvarRule : thm → IO (Except String thm) := fun th0 => do return .ok (← specGenvarLoop B th0)
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
    let undischAll : tactic := fun (asl, w) =>
      (Tactics.MAP_EVERY B (fun (p : String × thm) => Tactics.UNDISCH_TAC B (concl p.2)) asl (asl, w)
       : IO (Except String goalstate))
    let specFrees : tactic := fun (asl, w) =>
      (Tactics.MAP_EVERY B (fun v => Tactics.SPEC_TAC B (v, v)) (frees w) (asl, w)
       : IO (Except String goalstate))
    -- We start with a single goal: P.
    let tac : tactic := Tactics.EVERY B [
      D.refuteThen assumeTac,
      Meson.POLY_ASSUME_TAC B gaThs,
      undischAll,
      -- `~P ==> th1 ==> ... ==> thn ==> F`
      -- eliminate "select terms", e.g. Hilbert operators
      D.selectElim,
      -- MAP_EVERY is mapM for tactics
      -- I believe that this all-quantifies all free variables in the goal
      specFrees,
      Tactics.CONV_TAC B frontConv,
      -- remove outermost all-quantifiers (GEN_TAC) and implications (DISCH_TAC),
      -- moving them into assumptions
      Tactics.REPEAT B (ORELSE (Tactics.GEN_TAC B) (Tactics.DISCH_TAC B)),
      -- move conclusion negated into assumptions, replace goal by `F`
      D.refuteThen assumeTac,
      -- transform assumptions to NNF and skolemize
      Tactics.RULE_ASSUM_TAC B nnfSkolem,
      -- remove existentials at the front
      Tactics.REPEAT B (Tactics.FIRST_X_ASSUM B (fun th => Tactics.CHOOSE_TAC B th)),
      -- fix function arities, e.g. f(x) and f(x,y) become I f x and I (I f x) y
      D.asmFol,
      Meson.SPLIT_TAC B splitLimit,
      Tactics.RULE_ASSUM_TAC B prenexCnf,
      -- destroy all-quantifiers and replace quantified variables by fresh ones
      Tactics.RULE_ASSUM_TAC B specGenvarRule,
      -- make every conjunction a separate assumption
      Tactics.REPEAT B (Tactics.FIRST_X_ASSUM B (fun th => Meson.CONJUNCTS_THEN' B assumeTac th)),
      -- associate disjunctions to the right
      Tactics.RULE_ASSUM_TAC B assocRule ]
    (tac g : IO (Except String goalstate))

/- Basic Metis refutation procedure and parametrized tactic. -/

/-- `Thm.print_proof` (metis.ml 3834): on the std_formatter, unflushed. -/
partial def print_proof : Thm.thm → Fmt Unit
  | .Thm cl (infType, ths) => do
    Fmt.printString ("Inference: " ++ Thm.inferenceTypeToString infType)
    Fmt.printBreak 0 0
    Fmt.printString ("Clauses: " ++ Literal.Set.toString cl)
    Fmt.printBreak 0 0
    Fmt.printString "Theorems: "
    if ths.isEmpty then Fmt.printString "<none>"
    else do
      Fmt.printBreak 0 0
      Fmt.openVBox 2
      Fmt.printBreak 0 0
      for t in ths do print_proof t
      Fmt.closeBox
    Fmt.printBreak 0 0

/-- `SIMPLE_METIS_REFUTE ths`: convert to FOL, run the Metis loop, reconstruct. -/
def SIMPLE_METIS_REFUTE (B : BoolThms) (S : FolStores) (mem : Meson.ContraposCache)
    (rng : IO.Ref StdGen) (idr : IO.Ref Clause.clauseId) (gen : IO.Ref Int)
    (recon : Metis_reconstruct2.MetisReconDeps)
    (DISJ_CANON_CONV : term → IO (Except String thm)) (ths : List thm) :
    IO (Except String thm) := do
  Meson.clear_contrapos_cache mem
  -- TODO: Metis currently uses randomness to search for proof --
  -- we should make that deterministic for proof reconstruction!
  -- deterministic search: reseed the RNG (OCaml `Random.init 0`)
  rng.set (mkStdGen 0)
  match ← Metis_generate.metis_of_clauses S ths with
  | .error e => return .error e
  | .ok rules =>
    let verb ← metisverb.get
    -- metis.ml 10053-10057
    if verb then
      stdPrintf "Original ths:\n"
      for t in ths do stdPrintf s!"{← HolCore.Printer.string_of_thm t}\n"
    match ← Loop.run rng idr gen rules with
    | .error e => return .error e
    | .ok res =>
      if verb then stdQueue (print_proof res)   -- metis.ml 10059
      -- canonicalize the input theorems, then reconstruct
      let mut cths := []
      for t in ths do
        match ← DISJ_CANON_CONV (concl t) with
        | .ok eq =>
          match EQ_MP eq t with
          | .ok c => cths := cths ++ [c]
          | .error _ => cths := cths ++ [t]
        | .error _ => cths := cths ++ [t]
      -- `without_warnings (fun () -> hol_of_thm ths res)` (metis.ml 10060):
      -- no type-invention warnings during reconstruction.
      let tiv ← HolCore.Preterm.type_invention_warning.get
      HolCore.Preterm.type_invention_warning.set false
      let r ← try (Metis_reconstruct2.hol_of_thm B recon cths res).run
              finally HolCore.Preterm.type_invention_warning.set tiv
      match r with
      | .error e => return .error e
      | .ok proof =>
        -- metis.ml 10062-10069
        if verb then
          stdPrintf "ths:\n"
          for t in cths do
            stdQueue (← HolCore.Printer.pp_print_thm t)
            stdPrintf "\n"
          stdPrintf "Metis theorem:\n"
          stdQueue (← HolCore.Printer.pp_print_thm proof)
          stdPrintf "Metis end.\n"
        -- sanity (OCaml asserts): hyps ⊆ union of input hyps, and concl = F.
        let allhyps := (cths.map hyp).flatten
        if !((hyp proof).all (fun h => HolCore.Lib.mem h allhyps)) then
          return .error "SIMPLE_METIS_REFUTE: extra hypotheses"
        else
          -- `assert (concl proof = \`F\`)`: metis.ml parses `F` on each call.
          match ← HolCore.Parser.parse_term "F" with
          | .error e => return .error e
          | .ok f =>
            if !(concl proof == f) then
              return .error "SIMPLE_METIS_REFUTE: reconstructed conclusion is not F"
            else return .ok proof

/-- `PURE_METIS_TAC` = FIRST_ASSUM CONTR_TAC ORELSE accept the metis refutation. -/
def PURE_METIS_TAC (B : BoolThms) (S : FolStores) (mem : Meson.ContraposCache)
    (rng : IO.Ref StdGen) (idr : IO.Ref Clause.clauseId) (gen : IO.Ref Int)
    (recon : Metis_reconstruct2.MetisReconDeps)
    (DISJ_CANON_CONV : term → IO (Except String thm)) : tactic := fun g => do
  Meson.reset_vars S
  let _ ← Meson.reset_consts S
  let refute : tactic := fun (asl, w) => do
    let ths := asl.map (fun p => p.2)
    match ← SIMPLE_METIS_REFUTE B S mem rng idr gen recon DISJ_CANON_CONV ths with
    | .error e => return .error e
    | .ok th => Tactics.ACCEPT_TAC B th (asl, w)
  (ORELSE (Tactics.FIRST_ASSUM (fun cth => Tactics.CONTR_TAC B cth)) refute) g

/-- `GEN_METIS_TAC ths = FOL_PREPARE_TAC ths THEN PURE_METIS_TAC`. -/
def GEN_METIS_TAC (B : BoolThms) (D : Meson.MesonTacDeps) (S : FolStores)
    (mem : Meson.ContraposCache) (rng : IO.Ref StdGen) (idr : IO.Ref Clause.clauseId)
    (gen : IO.Ref Int) (recon : Metis_reconstruct2.MetisReconDeps)
    (DISJ_CANON_CONV : term → IO (Except String thm)) (splitLimit : Int) (ths : List thm) :
    tactic :=
  THEN B (FOL_PREPARE_TAC B D splitLimit ths)
         (PURE_METIS_TAC B S mem rng idr gen recon DISJ_CANON_CONV)

end Metis

/- -- Top-level ASM_METIS_TAC / METIS_TAC / METIS --------------------------
   These are wired with the concrete Session bundles; the fully-applied bare
   names live in `Session.lean`.  Here we provide the parameterized forms. -/

/-- `ASM_METIS_TAC = GEN_METIS_TAC`. -/
def ASM_METIS_TAC (B : BoolThms) (D : Meson.MesonTacDeps) (S : FolStores)
    (mem : Meson.ContraposCache) (rng : IO.Ref StdGen) (idr : IO.Ref Prover.Clause.clauseId)
    (gen : IO.Ref Int) (recon : Metis_reconstruct2.MetisReconDeps)
    (DISJ_CANON_CONV : term → IO (Except String thm)) (splitLimit : Int) (ths : List thm) :
    tactic := Metis.GEN_METIS_TAC B D S mem rng idr gen recon DISJ_CANON_CONV splitLimit ths

/-- `METIS_TAC ths = POP_ASSUM_LIST (K ALL_TAC) THEN ASM_METIS_TAC ths`. -/
def METIS_TAC (B : BoolThms) (D : Meson.MesonTacDeps) (S : FolStores)
    (mem : Meson.ContraposCache) (rng : IO.Ref StdGen) (idr : IO.Ref Prover.Clause.clauseId)
    (gen : IO.Ref Int) (recon : Metis_reconstruct2.MetisReconDeps)
    (DISJ_CANON_CONV : term → IO (Except String thm)) (splitLimit : Int) (ths : List thm) :
    tactic :=
  THEN B (Tactics.POP_ASSUM_LIST (fun _ => Tactics.ALL_TAC))
         (ASM_METIS_TAC B D S mem rng idr gen recon DISJ_CANON_CONV splitLimit ths)

/-- `METIS ths tm`: prove `tm` outright by Metis. -/
def METIS (B : BoolThms) (D : Meson.MesonTacDeps) (S : FolStores)
    (mem : Meson.ContraposCache) (rng : IO.Ref StdGen) (idr : IO.Ref Prover.Clause.clauseId)
    (gen : IO.Ref Int) (recon : Metis_reconstruct2.MetisReconDeps)
    (DISJ_CANON_CONV : term → IO (Except String thm)) (splitLimit : Int)
    (ths : List thm) (tm : term) : IO (Except String thm) :=
  Tactics.TAC_PROOF B ([], tm) (METIS_TAC B D S mem rng idr gen recon DISJ_CANON_CONV splitLimit ths)

end HolCore.Metis
