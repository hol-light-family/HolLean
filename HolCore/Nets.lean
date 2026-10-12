/- File: Nets.lean
Term nets: reasonably fast lookup based on term matchability.
Original: John Harrison, University of Cambridge Computer Laboratory
Original: (c) Copyright, University of Cambridge 1998
Original: (c) Copyright, John Harrison 1998-2007
Lean4 translation by Chris Walton 2026 -/

import HolCore.Lib
import HolCore.Basics
import HolCore.Fusion

open HolCore.Kernel HolCore.Basics HolCore.Lib

namespace HolCore.Nets

/- ---------------------------------------------------------------------- -/
/- Term nets are a finitely branching tree structure; at each level we    -/
/- have a set of branches and a set of "values". Linearization is         -/
/- performed from the left of a combination; even in iterated             -/
/- combinations we look at the head first. This is probably fastest, and  -/
/- anyway it's useful to allow our restricted second order matches: if    -/
/- the head is a variable then then whole term is treated as a variable.  -/
/- ---------------------------------------------------------------------- -/

inductive term_label where
  | Vnet                          -- variable (instantiable)
  | Lcnet (nk : String × Int)     -- local constant
  | Cnet  (nk : String × Int)     -- constant
  | Lnet  (n : Int)               -- lambda term (abstraction)
  deriving BEq, Repr, Inhabited

/- ---------------------------------------------------------------------- -/
/- Edges out of a net node are split by label kind. The Vnet edge is      -/
/- unique (so it's a direct field, looked up in O(1)); the others are     -/
/- persistent balanced trees keyed by (string * int) or int with          -/
/- monomorphic comparators. This gives O(log n) per-edge lookup.          -/
/- ---------------------------------------------------------------------- -/

@[reducible] def Sikey := String × Int
instance : Ord Sikey := lexOrd
@[reducible] def Intkey := Int
instance : Ord Intkey := (inferInstance : Ord Int)
mutual
  structure netnode_data (α : Type) where
    vnet   : Option (net α)
    cnets  : List (Sikey × net α)
    lcnets : List (Sikey × net α)
    lnets  : List (Intkey × net α)
    tips   : List α
  inductive net (α : Type) where
    | Netnode (data : netnode_data α)
end

/- ---------------------------------------------------------------------- -/
/- The empty net.                                                         -/
/- ---------------------------------------------------------------------- -/

def empty_net : net α :=
  .Netnode {
    vnet   := none
    cnets  := []
    lcnets := []
    lnets  := []
    tips   := [] }

/-- A net is always inhabited by the empty net (needed for `IO.Ref` state). -/
instance : Inhabited (net α) := ⟨empty_net⟩

/- ---------------------------------------------------------------------- -/
/- Insert a new element into a net.                                       -/
/- ---------------------------------------------------------------------- -/

private def amFind [Ord κ] (k : κ) : List (κ × ν) → Option ν
  | [] => none
  | (k', v) :: t =>
    match compare k k' with
    | .eq => some v
    | .lt => none
    | .gt => amFind k t

private def amAdd [Ord κ] (k : κ) (v : ν) : List (κ × ν) → List (κ × ν)
  | [] => [(k, v)]
  | (k', v') :: t =>
    match compare k k' with
    | .eq => (k, v) :: t
    | .lt => (k, v) :: (k', v') :: t
    | .gt => (k', v') :: amAdd k v t

private def label_to_store (lconsts : List term) (tm : term) :
    ExceptT String IO (term_label × List term) := do
  let (op, args) := strip_comb tm
  let n : Int := length args
  if is_const op then
    let (nm, _) ← liftExcept (dest_const op)
    return (.Cnet (nm, n), args)
  else if is_abs op then
    let (bv, bod) ← liftExcept (dest_abs op)
    let bod' ←
      if mem bv lconsts then do
        let g ← genvar (type_of bv)
        let sub ← liftExcept (vsubst [(g, bv)])
        pure (sub bod)
      else pure bod
    return (.Lnet n, bod' :: args)
  else if mem op lconsts then
    let (nm, _) ← liftExcept (dest_var op)
    return (.Lcnet (nm, n), args)
  else
    return (.Vnet, [])

private partial def set_insert [Ord α] (x : α) (l : List α) : List α :=
  let rec go : List α → Option (List α)
    | [] => some [x]
    | h :: t =>
      match compare h x with
      | .eq => none
      | _   => if compare x h == .lt then some (x :: h :: t)
                else (go t).map (h :: ·)
  (go l).getD l

partial def enter [Ord α] (lconsts : List term) (tmelem : term × α) (nt : net α) :
    IO (Except String (net α)) :=
  let (tm, elem) := tmelem
  let rec upd (elem : α) (tms : List term) (nt : net α) : ExceptT String IO (net α) := do
    let (.Netnode r) := nt
    match tms with
    | [] => return .Netnode { r with tips := set_insert elem r.tips }
    | tm :: rtms => do
        let (label, ntms) ← label_to_store lconsts tm
        let rest := ntms ++ rtms
        match label with
        | .Vnet =>
            let child ← upd elem rest ((r.vnet).getD empty_net)
            return .Netnode { r with vnet := some child }
        | .Cnet k =>
            let child ← upd elem rest ((amFind k r.cnets).getD empty_net)
            return .Netnode { r with cnets := amAdd k child r.cnets }
        | .Lcnet k =>
            let child ← upd elem rest ((amFind k r.lcnets).getD empty_net)
            return .Netnode { r with lcnets := amAdd k child r.lcnets }
        | .Lnet k =>
            let child ← upd elem rest ((amFind k r.lnets).getD empty_net)
            return .Netnode { r with lnets := amAdd k child r.lnets }
  (upd elem [tm] nt).run

/-- Insert a new element into a net WITHOUT deduplication (appends to tips).
    Needed for elements that have no `Ord` instance — e.g. `gconv = Int × conv`
    whose conversion component is a function.  Otherwise identical to `enter`. -/
partial def enter' (lconsts : List term) (tmelem : term × α) (nt : net α) :
    IO (Except String (net α)) :=
  let (tm, elem) := tmelem
  let rec upd (elem : α) (tms : List term) (nt : net α) : ExceptT String IO (net α) := do
    let (.Netnode r) := nt
    match tms with
    | [] => return .Netnode { r with tips := r.tips ++ [elem] }
    | tm :: rtms => do
        let (label, ntms) ← label_to_store lconsts tm
        let rest := ntms ++ rtms
        match label with
        | .Vnet =>
            let child ← upd elem rest ((r.vnet).getD empty_net)
            return .Netnode { r with vnet := some child }
        | .Cnet k =>
            let child ← upd elem rest ((amFind k r.cnets).getD empty_net)
            return .Netnode { r with cnets := amAdd k child r.cnets }
        | .Lcnet k =>
            let child ← upd elem rest ((amFind k r.lcnets).getD empty_net)
            return .Netnode { r with lcnets := amAdd k child r.lcnets }
        | .Lnet k =>
            let child ← upd elem rest ((amFind k r.lnets).getD empty_net)
            return .Netnode { r with lnets := amAdd k child r.lnets }
  (upd elem [tm] nt).run

/- ---------------------------------------------------------------------- -/
/- Look up a term in a net and return possible matches.                   -/
/- ---------------------------------------------------------------------- -/

private def label_for_lookup (tm : term) : term_label × List term :=
  let (op, args) := strip_comb tm
  let n : Int := length args
  if is_const op then
    (.Cnet ((dest_const op).toOption.map (·.1) |>.getD "", n), args)
  else if is_abs op then
    (.Lnet n, ((body op).toOption.getD op) :: args)
  else
    (.Lcnet ((dest_var op).toOption.map (·.1) |>.getD "", n), args)

partial def lookup (tm : term) (nt : net α) : List α :=
  let rec follow (tms : List term) (nt : net α) : List α :=
    let (.Netnode r) := nt
    match tms with
    | [] => r.tips
    | tm :: rtms =>
        let (label, ntms) := label_for_lookup tm
        let rest := ntms ++ rtms
        let collection : List α :=
          match label with
          | .Cnet k  => (amFind k r.cnets).elim [] (follow rest)
          | .Lcnet k => (amFind k r.lcnets).elim [] (follow rest)
          | .Lnet k  => (amFind k r.lnets).elim [] (follow rest)
          | .Vnet    => []
        match r.vnet with
        | none => collection
        | some vchild => collection ++ follow rtms vchild
  follow [tm] nt

/- ---------------------------------------------------------------------- -/
/- Function to merge two nets (code from Don Syme's hol-lite).            -/
/- ---------------------------------------------------------------------- -/

private def amUnion [Ord κ] (f : ν → ν → ν) : List (κ × ν) → List (κ × ν) → List (κ × ν)
  | [], m2 => m2
  | m1, [] => m1
  | (k1, v1) :: t1, (k2, v2) :: t2 =>
    match compare k1 k2 with
    | .eq => (k1, f v1 v2) :: amUnion f t1 t2
    | .lt => (k1, v1) :: amUnion f t1 ((k2, v2) :: t2)
    | .gt => (k2, v2) :: amUnion f ((k1, v1) :: t1) t2
  termination_by m1 m2 => m1.length + m2.length

private def set_merge [Ord α] : List α → List α → List α
  | [], l2 => l2
  | l1, [] => l1
  | h1 :: t1, h2 :: t2 =>
    match compare h1 h2 with
    | .eq => h1 :: set_merge t1 t2
    | .lt => h1 :: set_merge t1 (h2 :: t2)
    | .gt => h2 :: set_merge (h1 :: t1) t2
  termination_by l1 l2 => l1.length + l2.length

partial def merge_nets [Ord α] (n1 n2 : net α) : net α :=
  let (.Netnode r1) := n1
  let (.Netnode r2) := n2
  let merge_opt (a b : Option (net α)) : Option (net α) :=
    match a, b with
    | some x, some y => some (merge_nets x y)
    | some _, none   => a
    | none,   _      => b
  .Netnode {
    vnet   := merge_opt r1.vnet r2.vnet
    cnets  := amUnion merge_nets r1.cnets r2.cnets
    lcnets := amUnion merge_nets r1.lcnets r2.lcnets
    lnets  := amUnion merge_nets r1.lnets r2.lnets
    tips   := set_merge r1.tips r2.tips }
