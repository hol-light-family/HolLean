/- File: HolCore/OcamlHash.lean
OCaml's `Hashtbl.hash` on HOL types and terms, for comparison with HOL Light.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

lib.ml's finite partial functions (`|->`, `applyd`, `foldl`, ...) are Patricia
trees keyed on `Hashtbl.hash x`, and folding over one visits the keys in hash
order, so that order is observable (the order of `atoms`, of the linear forms
in realarith.ml).  Normally the Lean translation keys them on Lean's derived
`hash`, which gives the same functions but a different order.

Setting the environment variable HOLLEAN_OCAML_HASH (to anything) before the
process starts makes `Hashable term` and `Hashable hol_type` use OCaml's hash
instead, so orders match HOL Light exactly.  tools/hlpdiff sets it.  This is
not in the OCaml; it exists only for that comparison.

The hash reproduces runtime/hash.c (MurmurHash3 over a breadth-first walk of
the value, at most 10 meaningful values and 100 queued) on the memory layout
of the OCaml constructors: `Tyvar s` is a block of tag 0 and size 1,
`Tyapp (s, l)` tag 1 size 2; `Var`, `Const`, `Comb` and `Abs` tags 0-3, size
2; a list cell tag 0 size 2, `[]` the immediate `Val_int 0`. -/

import HolCore.Fusion
open HolCore.Kernel

namespace HolCore.OcamlHash

private def rotl (x : UInt32) (n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))

private def mix (h d : UInt32) : UInt32 :=
  let d := d * 0xcc9e2d51
  let d := rotl d 15
  let d := d * 0x1b873593
  let h := h ^^^ d
  let h := rotl h 13
  h * 5 + 0xe6546b64

private def finalMix (h : UInt32) : UInt32 :=
  let h := h ^^^ (h >>> 16)
  let h := h * 0x85ebca6b
  let h := h ^^^ (h >>> 13)
  let h := h * 0xc2b2ae35
  h ^^^ (h >>> 16)

/-- `caml_hash_mix_string`: 32-bit little-endian blocks, the 1-3 byte tail,
    then the length. -/
private def mixString (h : UInt32) (s : String) : UInt32 := Id.run do
  let b := s.toUTF8
  let len := b.size
  let mut h := h
  let mut i := 0
  while i + 4 ≤ len do
    let w := b[i]!.toUInt32 ||| (b[i+1]!.toUInt32 <<< 8) ||| (b[i+2]!.toUInt32 <<< 16) |||
             (b[i+3]!.toUInt32 <<< 24)
    h := mix h w
    i := i + 4
  let r := len % 4
  if r > 0 then
    let mut w : UInt32 := 0
    if r == 3 then w := b[i+2]!.toUInt32 <<< 16
    if r ≥ 2 then w := w ||| (b[i+1]!.toUInt32 <<< 8)
    w := w ||| b[i]!.toUInt32
    h := mix h w
  return h ^^^ len.toUInt32

/-- A value in the breadth-first queue. -/
inductive V where
  | ty (t : hol_type) | tm (t : term) | str (s : String) | tys (l : List hol_type)
  deriving Inhabited

/-- A block's header with the colour bits clear: `wosize << 10 | tag`. -/
private def hdr (size tag : Nat) : UInt32 := (size <<< 10 ||| tag).toUInt32

/-- The header and fields of a block, or `none` for the immediate `[]`. -/
def fields : V → Option (UInt32 × List V)
  | .ty (.Tyvar s) => some (hdr 1 0, [.str s])
  | .ty (.Tyapp s l) => some (hdr 2 1, [.str s, .tys l])
  | .tm (.Var s y) => some (hdr 2 0, [.str s, .ty y])
  | .tm (.Const s y) => some (hdr 2 1, [.str s, .ty y])
  | .tm (.Comb f x) => some (hdr 2 2, [.tm f, .tm x])
  | .tm (.Abs v b) => some (hdr 2 3, [.tm v, .tm b])
  | .tys [] => none
  | .tys (a :: l) => some (hdr 2 0, [.ty a, .tys l])
  | .str _ => none

/-- `Hashtbl.hash` = `seeded_hash_param 10 100 0`. -/
def hashV (obj : V) : UInt64 := Id.run do
  let sz := 100
  let mut queue : Array V := #[obj]
  let mut rd := 0
  let mut num : Int := 10
  let mut h : UInt32 := 0
  while rd < queue.size && num > 0 do
    let v : V := queue[rd]!
    rd := rd + 1
    match v with
    | .str s => h := mixString h s; num := num - 1
    | .tys [] => h := mix h 1; num := num - 1       -- the immediate Val_int 0 = 1
    | _ =>
      match fields v with
      | some (hd, fs) =>
        h := mix h hd
        for f in fs do
          if queue.size ≥ sz then break
          queue := queue.push f
      | none => pure ()
  return (finalMix h &&& 0x3FFFFFFF).toUInt64

end HolCore.OcamlHash


namespace HolCore.OcamlHash

/-- OCaml's `Hashtbl.hash` of a type. -/
def hashType (t : hol_type) : UInt64 := hashV (.ty t)
/-- OCaml's `Hashtbl.hash` of a term. -/
def hashTerm (t : term) : UInt64 := hashV (.tm t)
/-- OCaml's `Hashtbl.hash` of an `int` (the immediate value `2n+1`,
    `caml_hash_mix_intnat`). -/
def hashInt (n : Int) : UInt64 :=
  let d : Int64 := Int64.ofInt (2 * n + 1)
  let x : Int64 := (d >>> 32) ^^^ (d >>> 63) ^^^ d
  (finalMix (mix 0 x.toUInt64.toUInt32) &&& 0x3FFFFFFF).toUInt64
/-- OCaml's `Hashtbl.hash` of a `string`. -/
def hashString (s : String) : UInt64 := (finalMix (mixString 0 s) &&& 0x3FFFFFFF).toUInt64

/-- Whether finite partial functions use OCaml's hash (HOLLEAN_OCAML_HASH set
    when the process started). -/
initialize ocaml_hash : Bool ← do return (← IO.getEnv "HOLLEAN_OCAML_HASH").isSome

end HolCore.OcamlHash

namespace HolCore.Kernel

/-- Lean's derived hashes (resolved here, before the instances below). -/
private def leanHashType (t : hol_type) : UInt64 := hash t
private def leanHashTerm (t : term) : UInt64 := hash t

/-- Lean's derived hash, or OCaml's when `ocaml_hash` is set.  Declared at
    high priority so it replaces the derived instance wherever this module is
    imported (HolCore.Basics imports it, so every use of `|->` does). -/
instance (priority := high) : Hashable hol_type :=
  ⟨fun t => if OcamlHash.ocaml_hash then OcamlHash.hashType t else leanHashType t⟩
instance (priority := high) : Hashable term :=
  ⟨fun t => if OcamlHash.ocaml_hash then OcamlHash.hashTerm t else leanHashTerm t⟩

end HolCore.Kernel
