/- File: ImpConv.lean
Implicational conversions, implicational rewriting and target rewriting
(`impconv.ml`).

  (c) Copyright, Vincent Aravantinos, 2012-2013
       Analysis and Design of Dependable Systems
       fortiss GmbH, Munich, Germany
  Formerly:  Hardware Verification Group, Concordia University
  Contact: <vincent.aravantinos@fortiss.org>
  Distributed under the same license as HOL Light.

Lean4 translation by Chris Walton 2026.

`impconv.ml` is written as one large `let ... in` chain returning the tuple
`(IMP_REWRITE_TAC, TARGET_REWRITE_TAC, HINT_EXISTS_TAC, SEQ_IMP_REWRITE_TAC,
CASE_REWRITE_TAC)`.  Here those become top-level definitions in the sub-namespaces
mirroring the OCaml modules (`Tset`, `Annot`, `Fo_nets`, `Variance`, `Impconv`).
It is a parameterized library taking the established `BoolThms` `B` plus the
pre-proved theorems the OCaml uses, bundled in `ImpConvDeps` (`Session` proves
those once and binds the public tactics).

Many HOL Light conversions used here (`REWR_CONV`, `GEN_PART_MATCH`, `MATCH_MP`,
`PURE_REWRITE_RULE`) are `IO`/`ioconv` in HolCore, so functions that chain them
are written in `ExceptT String IO`; purely-kernel helpers stay in `Except`.
-/

import HolCore.Bool
import HolCore.Equal
import HolCore.Drule
import HolCore.Tactics
import HolCore.Simp
import HolCore.Parser
import HolCore.Theorems
import HolCore.Canon

open HolCore.Kernel HolCore.Basics HolCore.Lib HolCore.Bool HolCore.Equal
     HolCore.Drule HolCore.Tactics HolCore.Simp HolCore.Parser HolCore.Theorems

namespace HolCore.ImpConv

/-- Pre-proved theorems the OCaml `impconv.ml` closes over (proved once in
    `Session`).  Names mirror the OCaml `let`-bound constants / `TAUT`s. -/
structure ImpConvDeps where
  /-- `|- A ==> A` (for `IMP_REFL`). -/
  imp_refl : thm
  /-- `|- (p ==> q ==> r) <=> (q ==> p ==> r)` (for `GMATCH_MP`'s `swap`). -/
  imp_swap : thm
  /-- `|- p /\ (p ==> q) ==> q`-style `IMP_CONJ` (`p ==> q ==> r <=> p /\ q ==> r`). -/
  IMP_CONJ : thm
  /-- `|- a ==> b ==> c <=> a /\ b ==> c` (`IMP_IMP`). -/
  IMP_IMP : thm
  /-- `|- (x ==> y /\ z) <=> (x ==> y) /\ (x ==> z)` (`IMPLY_AND_RDISTRIB`). -/
  IMPLY_AND_RDISTRIB : thm
  /-- `|- (!x. P x /\ Q x) <=> (!x. P x) /\ (!x. Q x)` (`AND_FORALL_THM`). -/
  AND_FORALL_THM : thm
  /-- `|- (a ==> !x. P x) <=> (!x. a ==> P x)` (`RIGHT_IMP_FORALL_THM`). -/
  RIGHT_IMP_FORALL_THM : thm
  /-- `|- a /\ (b /\ c) <=> (a /\ b) /\ c` (`CONJ_ASSOC`). -/
  CONJ_ASSOC : thm
  /- Monotonicity theorems (from `theorems.ml`). -/
  MONO_AND : thm
  MONO_OR : thm
  MONO_IMP : thm
  MONO_NOT : thm
  MONO_FORALL : thm
  MONO_EXISTS : thm
  /- The `MKIMP_*` tautologies (proved once in `Session`). -/
  /-- `((A==>B)==>(C==>D)) /\ ((B==>A)==>(D==>C)) ==> (A<=>B) ==> (C<=>D)`. -/
  mkimp_iff : thm
  /-- `((A==>B)==>C) /\ ((B==>A)==>D) ==> (A<=>B) ==> C/\D`. -/
  mkimp_contra_iff : thm
  /-- `((A==>B)==>C) ==> (A<=>B) ==> C/\(B==>A)`. -/
  mkimpl_contra_iff : thm
  /-- `((B==>A)==>D) ==> (A<=>B) ==> (A==>B)/\D`. -/
  mkimpr_contra_iff : thm
  /-- `(C==>A==>B) /\ (D==>B==>A) ==> C/\D ==> (A<=>B)`. -/
  mkimp_co_iff : thm
  /-- `(C==>A==>B) ==> C/\(B==>A) ==> (A<=>B)`. -/
  mkimpl_co_iff : thm
  /-- `(D==>B==>A) ==> (A==>B)/\D ==> (A<=>B)`. -/
  mkimpr_co_iff : thm
  /-- `(B==>A) /\ (A==>B==>C==>D) ==> (A==>C) ==> (B==>D)`. -/
  mkimp_imp_contra_ctxt : thm
  /-- `(A==>B) /\ (A==>B==>D==>C) ==> (B==>D) ==> (A==>C)`. -/
  mkimp_imp_co_ctxt : thm
  /-- `(A==>C==>D) ==> (A==>C) ==> (A==>D)`. -/
  mkimpr_imp_ctxt : thm
  /-- `(C==>A==>B) /\ (A==>B==>C==>D) ==> (A/\C==>B/\D)`. -/
  mkimp_conj_contra_ctxt : thm
  /-- `(C==>A==>B) ==> (A/\C==>B/\C)`. -/
  mkimpl_conj_contra_ctxt : thm
  /-- `(A==>C==>D) ==> (A/\C==>A/\D)`. -/
  mkimpr_conj_contra_ctxt : thm
  /-- `(B==>A) /\ (B==>D==>C) ==> (B/\D==>A/\C)`. -/
  mkimp_conj_co_ctxt : thm
  /-- `(B==>A) ==> (B/\C==>A/\C)`. -/
  mkimpl_conj_co_ctxt : thm
  /-- `(C==>B==>A) ==> (B/\C==>A/\C)`. -/
  mkimpl_conj_co2_ctxt : thm
  /-- `NOT_FORALL_THM` (`~(!x. P x) <=> (?x. ~P x)`), for `extra_basic_rewrites`. -/
  NOT_FORALL_THM : thm
  /-- `NOT_IMP` (`~(p ==> q) <=> p /\ ~q`), for `extra_basic_rewrites`. -/
  NOT_IMP : thm
  /-- `A==>B==>C <=> B==>A==>C` (`IMP_SYM`, for `REWR_IMPCONV_OF_CONV`). -/
  imp_sym : thm
  /-- The same theorem, proved again for `REWR_IMPMCONV_OF_MCONV` (impconv.ml 1716). -/
  imp_sym' : thm
  /-- `LEFT_IMP_EXISTS_THM` (`(?x. P x) ==> Q <=> (!x. P x ==> Q)`); `IMP_EXIST`
      is its `GSYM`. -/
  LEFT_IMP_EXISTS_THM : thm
  /-- `(~P ==> Q = R) ==> (Q <=> (~P ==> R) /\ (P ==> Q))` (`CASE_REWR` lem1). -/
  case_lem1 : thm
  /-- `(P ==> Q = R) ==> (Q <=> (P ==> R) /\ (~P ==> Q))` (`CASE_REWR` lem2). -/
  case_lem2 : thm
  /-- `LEFT_FORALL_IMP_THM` (`(!x. P x ==> Q) <=> ((?x. P x) ==> Q)`), for
      `EXISTS_CTXIMPCONV`. -/
  LEFT_FORALL_IMP_THM : thm
  deriving Inhabited

/- ---------------------------------------------------------------------- -/
/- Preamble helpers (`impconv.ml` 21-213).                                -/
/- ---------------------------------------------------------------------- -/

/-- A few constants.

    The `A:bool`, `B:bool`, `C:bool`, `D:bool`, `T:bool` constants used as
    instantiation targets (parsed once in `Session`, supplied here). -/
structure ImpConvVars where
  /-- `(/\)`, parsed by impconv.ml 41's `strip_conj = binops ...`. -/
  and_tm : term
  A_ : term
  B_ : term
  C_ : term
  D_ : term
  T_ : term
  deriving Inhabited

/-- `thm_lt th1 th2 = th1 < th2` — the derived total order on theorems (mirrors
    OCaml's polymorphic `<`). -/
def thm_lt (th1 th2 : thm) : Bool := compare th1 th2 == Ordering.lt

/-- Same as [UNDISCH] but also returns the undischarged term. -/
def UNDISCH_TERM (B : BoolThms) (th : thm) : Except String (term × thm) := do
  let p ← (do Basics.dest_imp (concl th)).map Prod.fst
  return (p, ← B.UNDISCH th)

/-- Same as [UNDISCH_ALL] but also returns the undischarged terms. -/
partial def UNDISCH_TERMS (B : BoolThms) (th : thm) : List term × thm :=
  match UNDISCH_TERM B th with
  | .ok (t, th') => let (ts, th'') := UNDISCH_TERMS B th'; (t :: ts, th'')
  | .error _ => ([], th)

/-- Comblies the function [f] to the conclusion of an implicational theorem. -/
def MAP_CONCLUSION (B : BoolThms) (f : thm → Except String thm) (th : thm) :
    Except String thm := do
  let (p, th) ← UNDISCH_TERM B th
  B.DISCH p (← f th)

/-- `strip_conj = binops `(/\)``. -/
def strip_conj (andTm : term) : term → List term := binops andTm

/-- For a list [f1;...;fk], returns the first [fi x] that succeeds. -/
def tryfind_fun {α β : Type} (fs : List (α → Except String β)) (x : α) : Except String β :=
  match fs with
  | [] => failwith "tryfind_fun"
  | f :: fs' => match f x with | .ok y => .ok y | .error _ => tryfind_fun fs' x

/-- Same as [mapfilter] but also provides the rank of the iteration as an
    argument to [f]. -/
def mapfilteri {α β : Type} (f : Nat → α → Except String β) (l : List α) : List β :=
  let rec self (i : Nat) : List α → List β
    | [] => []
    | h :: t =>
        let rest := self (i + 1) t
        match f i h with | .ok y => y :: rest | .error _ => rest
  self 0 l

/-- `[]` for `none`, a singleton for `some`. -/
def list_of_option {α : Type} : Option α → List α
  | none => []
  | some x => [x]

/-- `try_list f x = try f x with Failure _ -> []`. -/
def try_list {α β : Type} (f : α → Except String (List β)) (x : α) : List β :=
  match f x with | .ok y => y | .error _ => []

/-- For a term t, builds `t ==> t` (by instantiating the pre-proved `A ==> A`). -/
def IMP_REFL (D : ImpConvDeps) (V : ImpConvVars) (t : term) : Except String thm :=
  INST [(t, V.A_)] D.imp_refl

/-- Conversion version of [variant]: Given variables [v1;...;vk] to avoid and a
    term [t], returns [|- t = t'] where [t'] is the same as [t] without any use
    of the variables [v1;...;vk]. -/
def VARIANT_CONV (av : List term) (t : term) : Except String thm := do
  let vs ← variables t
  let vts ← variants av vs
  let mapping := (List.zip vs vts).filter (fun (x, y) => x != y)
  DEPTH_CONV (fun u => do
    match dest_abs u with
    | .error e => .error e
    | .ok (bv, _) => do ALPHA_CONV (← assoc bv mapping) u) t

/-- Rule version of [VARIANT_CONV]. -/
def VARIANT_RULE (av : List term) : thm → Except String thm :=
  CONV_RULE (VARIANT_CONV av)

/-- Discharges the first hypothesis of a theorem. -/
def DISCH_HD (B : BoolThms) (th : thm) : Except String thm := do
  B.DISCH (← hd (hyp th)) th

/-- Rule version of [REWR_CONV].  (`REWR_CONV` is an `ioconv`, so this is `IO`.) -/
def REWR_RULE (B : BoolThms) (eqth : thm) (th : thm) : IO (Except String thm) :=
  convRuleIO (REWR_CONV B eqth) th

/-- Given a list [A1;...;Ak] and a theorem [th], returns [|- A1 /\ ... /\ Ak ==> th]. -/
def DISCH_IMP_IMP (B : BoolThms) (D : ImpConvDeps) (ts0 : List term) (th : thm) :
    IO (Except String thm) := do
  -- OCaml: f o rev, where f [] = I and f (t::ts) = rev_itlist (fun t -> REWR_RULE IMP_IMP o DISCH t) ts o DISCH t
  match ts0.reverse with
  | [] => return .ok th
  | t :: ts =>
    match ← (B.DISCH t th : Except String thm) |> pure with
    | .error e => return .error e
    | .ok th0 =>
      -- fold: for each t' in ts, th ↦ REWR_RULE IMP_IMP (DISCH t' th)
      let mut cur := th0
      for t' in ts do
        match B.DISCH t' cur with
        | .error e => return .error e
        | .ok d => match ← REWR_RULE B D.IMP_IMP d with
                   | .error e => return .error e
                   | .ok r => cur := r
      return .ok cur

/-- Given a term [A /\ B] and a theorem [th], returns [|- A ==> B ==> th]. -/
partial def DISCH_CONJ (B : BoolThms) (D : ImpConvDeps) (t : term) (th : thm) :
    IO (Except String thm) := ExceptT.run do
  match Basics.dest_conj t with
  | .ok (t1, t2) =>
    let th2 ← ExceptT.mk (DISCH_CONJ B D t2 th)
    let th1 ← ExceptT.mk (DISCH_CONJ B D t1 th2)
    ExceptT.mk (REWR_RULE B D.IMP_IMP th1)
  | .error _ => liftExcept (B.DISCH t th)

/-- Specializes all the universally quantified variables of a theorem, and
    returns both the theorem and the list of variables. -/
partial def SPEC_VARS (B : BoolThms) (th : thm) : List term × thm :=
  match B.SPEC_VAR th with
  | .ok (v, th') => let (vs, th'') := SPEC_VARS B th'; (v :: vs, th'')
  | .error _ => ([], th)

/-- Comblies the function [f] to the body of a universally quantified theorem. -/
def MAP_FORALL_BODY (B : BoolThms) (f : thm → Except String thm) (th : thm) :
    Except String thm := do
  let (vs, th) := SPEC_VARS B th
  B.GENL vs (← f th)

/-- Returns the two operands of a binary combination.  Contrary to
    [dest_binary], does not check what is the operator. -/
def dest_binary_blind : term → Except String (term × term)
  | .Comb (.Comb _ l) r => .ok (l, r)
  | _ => failwith "dest_binary_blind"

/-- `spec_all = repeat (snd o dest_forall)` (impconv.ml 151). -/
def spec_all : term → term :=
  repeat' (Prod.snd oEm Basics.dest_forall)   -- snd o dest_forall (dest_forall first)

/-- Given a theorem of the form [!xyz. P ==> !uvw. C] and a function [f],
    return [!xyz. P ==> !uvw. f C]. -/
def GEN_MAP_CONCLUSION (B : BoolThms) (f : thm → Except String thm) :
    thm → Except String thm :=
  MAP_FORALL_BODY B (MAP_CONCLUSION B (MAP_FORALL_BODY B f))

/-- Turn a theorem of the form [x ==> y /\ z] into [(x==>y) /\ (x==>z)].  Also
    deals with universal quantifications if necessary (e.g., [x ==> !v. y /\ z]
    will be turned into [(x ==> !v. y) /\ (x ==> !v. z)]).

    possible improvement: apply the rewrite more locally -/
def IMPLY_AND (B : BoolThms) (D : ImpConvDeps) (th : thm) : IO (Except String thm) := do
  match GSYM D.AND_FORALL_THM, GSYM D.CONJ_ASSOC with
  | .ok gAndForall, .ok gConjAssoc =>
    PURE_REWRITE_RULE B
      [gAndForall, D.IMP_IMP, D.RIGHT_IMP_FORALL_THM, D.IMPLY_AND_RDISTRIB, gConjAssoc] th
  | .error e, _ => return (.error e : Except String thm)
  | _, .error e => return (.error e : Except String thm)

/-- Insert `y` into a `thm_lt`-sorted, duplicate-free list (`GMATCH_MPS`'s helper). -/
partial def gmatchInsert (y : thm) : List thm → List thm
  | [] => [y]
  | x :: xs =>
      if equals_thm x y then x :: xs
      else if thm_lt x y then x :: gmatchInsert y xs
      else y :: x :: xs

/-- GMATCH_MP (U1 |- !x1...xn. H1 /\ ... /\ Hk ==> C) (U2 |- P)
    = (U1 u U2 |- !y1...ym. G1' /\ ... /\ Gl' ==> C')
    where:
    - P matches some Hi;
    - C' is the result of applying the matching substitution to C;
    - Gj' is the result of applying the matching substitution to Hj;
    - G1',...,Gl' is the list corresponding to H1,...,Hk but without Hi;
    - y1...ym are the variables among x1,...,xn that are not instantiated.

    possible improvement: make a specific conversion,
    define a MATCH_MP that also returns the instantiated variables -/
partial def GMATCH_MP (B : BoolThms) (D : ImpConvDeps) (th1 : thm) (th2 : thm) :
    IO (List thm) := do
  -- swap = CONV_RULE (REWR_CONV `(p==>q==>r) <=> (q==>p==>r)`)
  let swap (th : thm) : IO (Except String thm) := convRuleIO (REWR_CONV B D.imp_swap) th
  let (vs, th1') := SPEC_VARS B th1
  match ← PURE_REWRITE_RULE B [D.IMP_CONJ] th1' with
  | .error _ => return []
  | .ok th1rw =>
    let (hs, th1'') := UNDISCH_TERMS B th1rw
    -- f h hsRest = MATCH_MP (GENL vs (try swap (DISCH_IMP_IMP hsRest (DISCH h th1'')) with _ -> DISCH h th1'')) th2
    let f (h : term) (hsRest : List term) : IO (Except String thm) := do
      match B.DISCH h th1'' with
      | .error e => return .error e
      | .ok th1''' =>
        let th1'''' ← (do
          match ← DISCH_IMP_IMP B D hsRest th1''' with
          | .error _ => pure th1'''
          | .ok d => match ← swap d with | .ok s => pure s | .error _ => pure th1''')
        match B.GENL vs th1'''' with
        | .error e => return .error e
        | .ok g => MATCH_MP B g th2
    let rec loop (acc : List term) (rest : List term) : IO (List thm) := do
      match rest with
      | [] => return []
      | h :: hsTl =>
        -- OCaml: acc is the reversed prefix, f gets acc @ hs; recurse with (h::acc)
        let here ← (match ← f h (acc ++ hsTl) with | .ok t => pure [t] | .error _ => pure [])
        let more ← loop (h :: acc) hsTl
        return here ++ more
    loop [] hs

/-- `GMATCH_MPS ths1 ths2`: closure of `GMATCH_MP` over the two lists, keeping the
    accumulator a sorted, duplicate-free list (ordered by `thm_lt`). -/
partial def GMATCH_MPS (B : BoolThms) (D : ImpConvDeps) (ths1 ths2 : List thm) :
    IO (List thm) := do
  let inserts (ys : List thm) (acc : List thm) : List thm := itlist gmatchInsert ys acc
  match ths1 with
  | [] => return []
  | th1 :: ths1' =>
    let rec self (acc : List thm) (th1 : thm) (ths1 : List thm) (rest2 : List thm) :
        IO (List thm) := do
      match rest2 with
      | [] => match ths1 with
              | [] => return acc
              | th :: ths1'' => self acc th ths1'' ths2
      | th2 :: ths2' =>
        let g ← GMATCH_MP B D th1 th2
        self (inserts g acc) th1 ths1 ths2'
    self [] th1 ths1' ths2

/-- `MP_CLOSURE ths1 ths2`. -/
partial def MP_CLOSURE (B : BoolThms) (D : ImpConvDeps) (ths1 ths2 : List thm) :
    IO (List thm) := do
  let ths1 := ths1.filter (fun th => is_imp (spec_all (concl th)))
  let rec self (rest1 : List thm) : IO (List thm) := do
    match rest1 with
    | [] => return []
    | _ :: _ =>
      let ths1'' ← GMATCH_MPS B D rest1 ths2
      let more ← self ths1''
      return more ++ ths1''
  self ths1

/- ---------------------------------------------------------------------- -/
/- Set of terms.  Implemented as ordered lists (`impconv.ml` 213-275).    -/
/- ---------------------------------------------------------------------- -/
namespace Tset

/-- Term sets are ordered term lists. -/
abbrev t := List term

/-- `lt x y = compare x y < 0` (the derived term order). -/
def lt (x y : term) : Bool := compare x y == Ordering.lt

/-- `of_list = List.sort compare`. -/
def of_list (l : List term) : t := l.mergeSort (fun x y => compare x y != Ordering.gt)

/-- `insert ts t`: ordered insert (skips the literal `T`; `T_` supplied). -/
def insert (T_ : term) (ts : t) (tm : term) : t :=
  let rec self : t → t
    | [] => [tm]
    | x :: xs =>
        if lt x tm then x :: self xs
        else if x == tm then x :: xs
        else tm :: x :: xs
  if tm == T_ then ts else self ts

/-- `remove ts t`: ordered remove. -/
def remove (ts : t) (tm : term) : t :=
  let rec self : t → t
    | [] => []
    | x :: xs =>
        if lt x tm then x :: self xs
        else if x == tm then xs
        else x :: xs
  self ts

/-- `strip_conj`: split a conjunction and insert each leaf. -/
partial def strip_conj (T_ : term) (tm0 : term) : t :=
  let rec self (acc : t) (tm : term) : t :=
    match Basics.dest_conj tm with
    | .ok (t1, t2) => self (self acc t1) t2
    | .error _ => insert T_ acc tm
  self [] tm0

/-- `union l1 l2`: merge of two ordered sets. -/
def union : t → t → t
  | [], l2 => l2
  | l1, [] => l1
  | (h1 :: t1), (h2 :: t2) =>
      if lt h1 h2 then h1 :: union t1 (h2 :: t2)
      else if h1 == h2 then h1 :: union t1 t2
      else h2 :: union (h1 :: t1) t2

/-- `mem x ts`: ordered membership. -/
def mem (x : term) : t → Bool
  | x' :: xs => if x' == x then true else if lt x' x then mem x xs else false
  | [] => false

/-- `subtract l1 l2 = filter (fun x -> not (mem x l2)) l1` (impconv.ml 258).
    NOTE: the OCaml uses an explicit lambda here, NOT an `o`-composition. -/
def subtract (l1 l2 : t) : t := l1.filter (fun x => !(mem x l2))

/-- The empty set. -/
def empty : t := []

/-- `flat_revmap f = self [] where self acc (x::xs) = self (union (f x) acc) xs`. -/
def flat_revmap (f : α → t) (l : List α) : t :=
  let rec self (acc : t) : List α → t
    | [] => acc
    | x :: xs => self (union (f x) acc) xs
  self [] l

/-- `flat_map f = flat_revmap f o rev` (impconv.ml 266). -/
def flat_map (f : α → t) : List α → t :=
  flat_revmap f o List.reverse            -- rev runs FIRST, then flat_revmap f

/-- `frees acc t`: accumulate the free variables of `t` (needs `T_` for `insert`). -/
def freesAcc (T_ : term) : t → term → t
  | acc, (.Var s ty)   => insert T_ acc (.Var s ty)
  | acc, (.Const _ _)  => acc
  | acc, (.Abs v b)    => remove (freesAcc T_ acc b) v
  | acc, (.Comb u v)   => freesAcc T_ (freesAcc T_ acc u) v

/-- `freesl ts = itlist (C frees) ts empty`. -/
def freesl (T_ : term) (ts : List term) : t :=
  itlist (fun tm acc => freesAcc T_ acc tm) ts empty

/-- `frees = frees empty`. -/
def frees (T_ : term) (tm : term) : t := freesAcc T_ empty tm

end Tset

/- ---------------------------------------------------------------------- -/
/- Type-annotated terms (`impconv.ml` 276-322): a term representation     -/
/- caching the type at every node for faster matching.                    -/
/- ---------------------------------------------------------------------- -/
namespace Annot

/-- Type-annotated term. -/
inductive t where
  | Var_   : String → hol_type → t
  | Const_ : String → hol_type → term → t
  | Comb_  : t → t → hol_type → t
  | Abs_   : t → t → hol_type → t
  deriving Inhabited

/-- `type_of`: the cached type at the root. -/
def type_of : t → hol_type
  | .Var_ _ ty     => ty
  | .Const_ _ ty _ => ty
  | .Comb_ _ _ ty  => ty
  | .Abs_ _ _ ty   => ty

/-- `of_term`: annotate a term (IO, via `mk_fun_ty`). -/
partial def of_term : term → IO (Except String t)
  | .Var s ty   => return .ok (.Var_ s ty)
  | .Const s ty => return .ok (.Const_ s ty (.Const s ty))
  | .Comb u v => do
      match ← of_term u with
      | .error e => return .error e
      | .ok u' => match ← of_term v with
                  | .error e => return .error e
                  | .ok v' => match dest_fun_ty (type_of u') with
                              | .error e => return .error e
                              | .ok (_, rty) => return .ok (.Comb_ u' v' rty)
  | .Abs x b => do
      match ← of_term x with
      | .error e => return .error e
      | .ok x' => match ← of_term b with
                  | .error e => return .error e
                  | .ok b' => match ← mk_fun_ty (type_of x') (type_of b') with
                              | .error e => return .error e
                              | .ok fty => return .ok (.Abs_ x' b' fty)

/-- `equal`: structural equality ignoring the cached `Const_` term. -/
def equal : t → t → Bool
  | .Var_ s1 ty1, .Var_ s2 ty2       => s1 == s2 && ty1 == ty2
  | .Const_ s1 ty1 _, .Const_ s2 ty2 _ => s1 == s2 && ty1 == ty2
  | .Comb_ u1 v1 _, .Comb_ u2 v2 _   => equal u1 u2 && equal v1 v2
  | .Abs_ v1 b1 _, .Abs_ v2 b2 _     => equal v1 v2 && equal b1 b2
  | _, _ => false

/-- `to_term`: strip the annotations (Except, via `mk_comb`/`mk_abs`). -/
def to_term : t → Except String term
  | .Var_ s ty     => .ok (mk_var s ty)
  | .Const_ _ _ tm => .ok tm
  | .Comb_ u v _   => do mk_comb (← to_term u) (← to_term v)
  | .Abs_ v b _    => do mk_abs (← to_term v) (← to_term b)

/-- `dummy = Var_("",aty)`. -/
def dummy : t := .Var_ "" aty

/-- `find_term p t`: first subterm (pre-order, `u` before `v`) satisfying `p`. -/
partial def find_term (p : t → Bool) (tm : t) : Except String t :=
  if p tm then .ok tm
  else match tm with
       | .Abs_ _ b _  => find_term p b
       | .Comb_ u v _ => match find_term p u with
                         | .ok r => .ok r
                         | .error _ => find_term p v
       | _ => failwith "Annot.find_term"

end Annot

/- ---------------------------------------------------------------------- -/
/- First-order matching of terms (`impconv.ml` 336-370).                  -/
/-                                                                        -/
/- Same note as in [drule.ml]:                                            -/
/- in the event of spillover patterns, this may return false results;     -/
/- but there's usually an implicit check outside that the match worked    -/
/- anyway. A test could be put in (see if any "env" variables are left in  -/
/- the term after abstracting out the pattern instances) but it'd be slower. -/
/- ---------------------------------------------------------------------- -/

/-- First-order match of a pattern term [p] against a term [t], returning the
    term instantiation list and the type instantiation.  (IO: annotates [t] via
    `Annot.of_term`.) -/
partial def fo_term_match (lcs : List term) (p : term) (tm : term) :
    IO (Except String (List (term × term) × List (hol_type × hol_type))) := do
  -- self bnds (tenv,tyenv) p t   — tenv : (Annot.t × var) list, tyenv : type inst
  let rec self (bnds : List (Annot.t × term))
      (tenv : List (Annot.t × term)) (tyenv : List (hol_type × hol_type))
      (p : term) (t : Annot.t) :
      Except String (List (Annot.t × term) × List (hol_type × hol_type)) :=
    match p, t with
    | .Comb p1 p2, .Comb_ t1 t2 _ => do
        let (tenv1, tyenv1) ← self bnds tenv tyenv p1 t1
        self bnds tenv1 tyenv1 p2 t2
    | .Abs v pbod, .Abs_ v' tbod _ => do
        let tyenv' ← type_match (type_of v) (Annot.type_of v') tyenv
        self ((v', v) :: bnds) tenv tyenv' pbod tbod
    | .Const n ty, .Const_ n' ty' _ =>
        if n != n' then failwith "fo_term_match"
        else do let tyenv' ← type_match ty ty' tyenv; .ok (tenv, tyenv')
    | (.Var n ty), t =>
        let v := (.Var n ty : term)
        -- Is v bound?  (rev_assoc v bnds : the Annot bound to v)
        match rev_assoc v bnds with
        | .ok tb => if Annot.equal t tb then .ok (tenv, tyenv) else failwith "fo_term_match"
        | .error _ =>
            if mem v lcs then
              match t with
              | .Var_ n' ty' => if n' == n && ty' == ty then .ok (tenv, tyenv)
                                else failwith "fo_term_match"
              | _ => failwith "fo_term_match"
            else do
              let tyenv' ← type_match ty (Annot.type_of t) tyenv
              match rev_assoc v tenv with
              | .ok t' => if Annot.equal t t' then .ok (tenv, tyenv') else failwith "fo_term_match"
              | .error _ => .ok ((t, v) :: tenv, tyenv')
    | _, _ => failwith "fo_term_match"
  match ← Annot.of_term tm with
  | .error e => return .error e
  | .ok at' =>
    match self [] [] [] p at' with
    | .error e => return .error e
    | .ok (tenv, tyenv) =>
      let instf := inst tyenv
      match (tenv.reverse.mapM (fun (t, v) => do pure ((← Annot.to_term t), instf v)) :
             Except String (List (term × term))) with
      | .error e => return .error e
      | .ok mapped => return .ok (mapped, tyenv)

/-- `match_bvs t1 t2 acc`: collect bound-variable name renamings (`GEN_PART_MATCH_ALL`). -/
partial def match_bvs (t1 t2 : term) (acc : List (String × String)) : List (String × String) :=
  match dest_abs t1, dest_abs t2 with
  | .ok (v1, b1), .ok (v2, b2) =>
      match dest_var v1, dest_var v2 with
      | .ok (n1, _), .ok (n2, _) =>
          let newacc := if n1 == n2 then acc else insert (n1, n2) acc
          match_bvs b1 b2 newacc
      | _, _ => acc
  | _, _ =>
      match dest_comb t1, dest_comb t2 with
      | .ok (l1, r1), .ok (l2, r2) => match_bvs l1 l2 (match_bvs r1 r2 acc)
      | _, _ => acc

/-- Like [GEN_PART_MATCH] but using the first-order matcher [fo_term_match], so
    more patterns match.  (IO.) -/
def GEN_PART_MATCH_ALL (B : BoolThms) (partfn : term → Except String term)
    (th : thm) (tm : term) : IO (Except String thm) := ExceptT.run do
  let sth ← liftExcept (B.SPEC_ALL th)
  let bod := concl sth
  let pbod ← liftExcept (partfn bod)
  let lcs := intersect (frees (concl th)) (freesl (hyp th))
  let fvs := subtract (subtract (frees bod) (frees pbod)) lcs
  let bvms := match_bvs tm pbod []
  let abod := deep_alpha bvms bod
  let ath ← liftExcept do EQ_MP (← ALPHA bod abod) sth
  let pabod ← liftExcept (partfn abod)
  let (insts, tyinsts) ← ExceptT.mk (fo_term_match lcs pabod tm)
  let eth ← liftExcept do INSTANTIATE_ALL B ([], insts, tyinsts) (← B.GENL fvs ath)
  -- fth = itlist (fun v th -> snd (SPEC_VAR th)) fvs eth   (SPEC_VAR |fvs| times)
  let fth ← liftExcept (itlistM (fun _ th => do pure (← B.SPEC_VAR th).2) fvs eth)
  let tm' ← liftExcept (partfn (concl fth))
  if compare tm' tm == Ordering.eq then pure fth
  else
    match ALPHA tm' tm with
    | .error _ => throw "PART_MATCH: Sanity check failure"
    | .ok a =>
      let sr : Except String thm ← SUBS [a] fth
      match sr with
      | .ok r => pure r
      | .error _ => throw "PART_MATCH: Sanity check failure"

/- ---------------------------------------------------------------------- -/
/- First-order term nets (`impconv.ml` 402-477).                          -/
/- ---------------------------------------------------------------------- -/
namespace Fo_nets

/-- Net edge labels. -/
inductive term_label where
  | Vnet  : Int → term_label
  | Lcnet : String → Int → term_label
  | Cnet  : String → Int → term_label
  | Lnet  : Int → term_label
  deriving BEq, Inhabited

/-- A first-order term net storing `α` values. -/
inductive t (α : Type) where
  | Netnode : List (term_label × t α) → List α → t α
  deriving Inhabited

/-- The empty net. -/
def empty_net {α : Type} : t α := .Netnode [] []

/-- `label_to_store lcs t`: the storing label + child terms for `t`. -/
def label_to_store (lcs : List term) (tm : term) : IO (term_label × List term) := do
  let (op, args) := strip_comb tm
  let nargs : Int := args.length
  match op with
  | .Const n _ => return (.Cnet n nargs, args)
  | .Abs v b =>
      let b' ← if mem v lcs then do
                 let gv ← genvar (type_of v)
                 match (vsubst [(gv, v)]) with
                 | .ok f => pure (f b) | .error _ => pure b
               else pure b
      return (.Lnet nargs, b' :: args)
  | .Var n _ => if mem op lcs then return (.Lcnet n nargs, args)
                else return (.Vnet nargs, args)
  | _ => return (.Vnet nargs, args)   -- OCaml: assert false (unreachable)

/-- `enter lcs (t,elem) net`: insert `elem` keyed by `t`. -/
partial def net_update {α : Type} (lcs : List term) (elem : α) :
    t α → List term → IO (t α)
  | .Netnode edges tips, [] => return .Netnode edges (elem :: tips)
  | .Netnode edges tips, tm :: rts => do
      let (label, nts) ← label_to_store lcs tm
      -- child,others = try (snd F_F I)(remove (fun (x,_) -> x=label) edges) with _ -> empty_net,edges
      let (child, others) :=
        match edges.find? (fun (x, _) => x == label) with
        | some (_, c) => (c, edges.filter (fun (x, _) => !(x == label)))
        | none => (empty_net, edges)
      let new_child ← net_update lcs elem child (nts ++ rts)
      return .Netnode ((label, new_child) :: others) tips

/-- `enter lcs (t,elem) net`. -/
def enter {α : Type} (lcs : List term) (te : term × α) (net : t α) : IO (t α) :=
  net_update lcs te.2 net [te.1]

/-- `label_for_lookup t`. -/
def label_for_lookup (tm : term) : term_label × List term :=
  let (op, args) := strip_comb tm
  let nargs : Int := args.length
  match op with
  | .Const n _ => (.Cnet n nargs, args)
  | .Abs _ b   => (.Lnet nargs, b :: args)
  | .Var n _   => (.Lcnet n nargs, args)
  | _          => (.Lcnet "" nargs, args)   -- OCaml: Comb _ -> assert false (unreachable)

/-- `support`: helper enumerating variable-arity continuations for `lookup`. -/
def support (rts : List term) : List term → List (Int × List term)
  | [] => [(0, rts)]
  | tm :: ts =>
      match support rts ts with
      | (k, nts') :: res' => (k + 1, tm :: nts') :: (k, nts') :: res'
      | [] => [(0, rts)]   -- unreachable (support always nonempty)

/-- `lookup t net`: all stored values whose key first-order-matches `t`. -/
partial def follow {α : Type} : t α → List term → List α
  | .Netnode _ tips, [] => tips
  | (.Netnode edges _tips), tm :: rts =>
      let (label, nts) := label_for_lookup tm
      let collection :=
        match (assoc label edges : Except String (t α)) with
        | .ok child => follow child (nts ++ rts)
        | .error _ => []
      let follows := (support rts nts).map (fun (k, nts') =>
        match (assoc (term_label.Vnet k) edges : Except String (t α)) with
        | .ok child => follow child nts'
        | .error _ => [])
      collection ++ follows.flatten

/-- `lookup t net = follow net [t]`. -/
def lookup {α : Type} (tm : term) (net : t α) : List α := follow net [tm]

/-- `filter p net`: keep only tips satisfying `p`. -/
partial def filter {α : Type} (p : α → Bool) : t α → t α
  | .Netnode edges tips =>
      .Netnode (edges.map (fun (l, n) => (l, filter p n))) (tips.filter p)

/-- All tips stored anywhere in the net (used to collect surviving theorems in
    `IMPREWR_CTXCONV`'s `diminish`). -/
partial def allTips {α : Type} : t α → List α
  | .Netnode edges tips => tips ++ (edges.flatMap (fun (_, n) => allTips n))

end Fo_nets

/- ---------------------------------------------------------------------- -/
/- Variance (`impconv.ml` 478-482).                                       -/
/- ---------------------------------------------------------------------- -/
namespace Variance

/-- Covariant / contravariant. -/
inductive t where | Co | Contra
  deriving BEq, Inhabited

/-- `neg Co = Contra`, `neg Contra = Co`. -/
def neg : t → t | .Co => .Contra | .Contra => .Co

end Variance

/- ---------------------------------------------------------------------- -/
/- IMPLICATIONAL RULES                                                    -/
/- i.e., rules to build propositions based on implications rather than    -/
/- equivalence.                                                           -/
/- (Module Impconv: MKIMP_* implicational rules, `impconv.ml` 490-730.)   -/
/- ---------------------------------------------------------------------- -/

/-- `MKIMP_common lem th1 th2`: instantiate `A,B,C,D` in `lem` from the two
    implications `th1 : A==>B`, `th2 : C==>D` and MP with their conjunction. -/
def MKIMP_common (B : BoolThms) (V : ImpConvVars) (lem th1 th2 : thm) :
    Except String thm := do
  let (a, b) ← Basics.dest_imp (concl th1)
  let (c, d) ← Basics.dest_imp (concl th2)
  B.MP (← INST [(a, V.A_), (b, V.B_), (c, V.C_), (d, V.D_)] lem) (← B.CONJ th1 th2)

/-- Similar to `[MK_CONJ]` but theorems should be implicational instead of
    equational, i.e., conjoin both sides of two implicational theorems.  More
    precisely: given two theorems `[A ==> B]` and `[C ==> D]`, returns
    `[A /\ C ==> B /\ D]`. -/
def MKIMP_CONJ (B : BoolThms) (V : ImpConvVars) (D : ImpConvDeps) :=
  MKIMP_common B V D.MONO_AND

/-- Similar to `[MK_DISJ]` but theorems should be implicational instead of
    equational, i.e., disjoin both sides of two implicational theorems.  More
    precisely: given two theorems `[A ==> B]` and `[C ==> D]`, returns
    `[A \/ C ==> B \/ D]`. -/
def MKIMP_DISJ (B : BoolThms) (V : ImpConvVars) (D : ImpConvDeps) :=
  MKIMP_common B V D.MONO_OR

/-- `MKIMP_IFF`: from `th1 : (A==>B)==>(C==>D)` and `th2 : (B==>A)==>(D==>C)`,
    returns `(A<=>B) ==> (C<=>D)`. -/
def MKIMP_IFF (B : BoolThms) (V : ImpConvVars) (D : ImpConvDeps) (th1 th2 : thm) :
    Except String thm := do
  let (ab, cd) ← Basics.dest_imp (concl th1)
  let (a, b) ← Basics.dest_imp ab
  let (c, d) ← Basics.dest_imp cd
  B.MP (← INST [(a, V.A_), (b, V.B_), (c, V.C_), (d, V.D_)] D.mkimp_iff) (← B.CONJ th1 th2)

/-- `th1 = (A ==> B) ==> C1`; `th2 = (B ==> A) ==> C2`;
    `output = (A <=> B) ==> (C1 /\ C2)`. -/
def MKIMP_CONTRA_IFF (B : BoolThms) (V : ImpConvVars) (D : ImpConvDeps) (th1 th2 : thm) :
    Except String thm := do
  let (ab, c) ← Basics.dest_imp (concl th1)
  let (_, d) ← Basics.dest_imp (concl th2)
  let (a, b) ← Basics.dest_imp ab
  B.MP (← INST [(a, V.A_), (b, V.B_), (c, V.C_), (d, V.D_)] D.mkimp_contra_iff) (← B.CONJ th1 th2)

/-- `MKIMPL_CONTRA_IFF`: `th : (A==>B)==>C` ↦ `(A<=>B)==>C/\(B==>A)`. -/
def MKIMPL_CONTRA_IFF (B : BoolThms) (V : ImpConvVars) (D : ImpConvDeps) (th : thm) :
    Except String thm := do
  let (ab, c) ← Basics.dest_imp (concl th)
  let (a, b) ← Basics.dest_imp ab
  B.MP (← INST [(a, V.A_), (b, V.B_), (c, V.C_)] D.mkimpl_contra_iff) th

/-- `MKIMPR_CONTRA_IFF`: `th : (B==>A)==>D` ↦ `(A<=>B)==>(A==>B)/\D`. -/
def MKIMPR_CONTRA_IFF (B : BoolThms) (V : ImpConvVars) (D : ImpConvDeps) (th : thm) :
    Except String thm := do
  let (ba, d) ← Basics.dest_imp (concl th)
  let (b, a) ← Basics.dest_imp ba
  B.MP (← INST [(a, V.A_), (b, V.B_), (d, V.D_)] D.mkimpr_contra_iff) th

/-- `MKIMP_CO_IFF`: `th1 : C==>A==>B`, `th2 : D==>B==>A` ↦ `C/\D==>(A<=>B)`. -/
def MKIMP_CO_IFF (B : BoolThms) (V : ImpConvVars) (D : ImpConvDeps) (th1 th2 : thm) :
    Except String thm := do
  let (c, ab) ← Basics.dest_imp (concl th1)
  let (d, _) ← Basics.dest_imp (concl th2)
  let (a, b) ← Basics.dest_imp ab
  B.MP (← INST [(a, V.A_), (b, V.B_), (c, V.C_), (d, V.D_)] D.mkimp_co_iff) (← B.CONJ th1 th2)

/-- `MKIMPL_CO_IFF`: `th : C==>A==>B` ↦ `C/\(B==>A)==>(A<=>B)`. -/
def MKIMPL_CO_IFF (B : BoolThms) (V : ImpConvVars) (D : ImpConvDeps) (th : thm) :
    Except String thm := do
  let (c, ab) ← Basics.dest_imp (concl th)
  let (a, b) ← Basics.dest_imp ab
  B.MP (← INST [(a, V.A_), (b, V.B_), (c, V.C_)] D.mkimpl_co_iff) th

/-- `MKIMPR_CO_IFF`: `th : D==>B==>A` ↦ `(A==>B)/\D==>(A<=>B)`. -/
def MKIMPR_CO_IFF (B : BoolThms) (V : ImpConvVars) (D : ImpConvDeps) (th : thm) :
    Except String thm := do
  let (d, ba) ← Basics.dest_imp (concl th)
  let (b, a) ← Basics.dest_imp ba
  B.MP (← INST [(a, V.A_), (b, V.B_), (d, V.D_)] D.mkimpr_co_iff) th

/-- Given two theorems `[A ==> B]` and `[C ==> D]`, returns
    `[(B ==> C) ==> (A ==> D)]`. -/
def MKIMP_IMP (B : BoolThms) (V : ImpConvVars) (D : ImpConvDeps) (th1 th2 : thm) :
    Except String thm := do
  let (b, a) ← Basics.dest_imp (concl th1)
  let (c, d) ← Basics.dest_imp (concl th2)
  B.MP (← INST [(a, V.A_), (b, V.B_), (c, V.C_), (d, V.D_)] D.MONO_IMP) (← B.CONJ th1 th2)

/-- `MKIMPL_common lem`: `lem' = REWRITE_RULE[] (INST [C_,D_] lem)`, then
    `fun th t -> MP (INST [a,A_;b,B_;t,C_] lem') th`. -/
def MKIMPL_common (B : BoolThms) (V : ImpConvVars) (lem : thm) (th : thm) (t : term) :
    IO (Except String thm) := ExceptT.run do
  let lem' ← ExceptT.mk (REWRITE_RULE B [] (← liftExcept (INST [(V.C_, V.D_)] lem)))
  let (a, b) ← liftExcept (Basics.dest_imp (concl th))
  liftExcept do B.MP (← INST [(a, V.A_), (b, V.B_), (t, V.C_)] lem') th

/-- Given a theorem `[A ==> B]` and a term `[C]`, returns `[A /\ C ==> B /\ C]`. -/
def MKIMPL_CONJ (B : BoolThms) (V : ImpConvVars) (D : ImpConvDeps) :=
  MKIMPL_common B V D.MONO_AND

/-- Given a theorem `[A ==> B]` and a term `[C]`, returns `[A \/ C ==> B \/ C]`. -/
def MKIMPL_DISJ (B : BoolThms) (V : ImpConvVars) (D : ImpConvDeps) :=
  MKIMPL_common B V D.MONO_OR

/-- Given a theorem `[A ==> B]` and a term `[C]`, returns
    `[(B ==> C) ==> (A ==> C)]`. -/
def MKIMPL_IMP (B : BoolThms) (V : ImpConvVars) (D : ImpConvDeps) (th : thm) (t : term) :
    IO (Except String thm) := ExceptT.run do
  let monoImp' ← ExceptT.mk (REWRITE_RULE B [] (← liftExcept (INST [(V.C_, V.D_)] D.MONO_IMP)))
  let (b, a) ← liftExcept (Basics.dest_imp (concl th))
  liftExcept do B.MP (← INST [(a, V.A_), (b, V.B_), (t, V.C_)] monoImp') th

/-- `MKIMPR_common lem`: `lem' = REWRITE_RULE[] (INST [A_,B_] lem)`, then
    `fun t th -> MP (INST [c,C_;d,D_;t,A_] lem') th`. -/
def MKIMPR_common (B : BoolThms) (V : ImpConvVars) (lem : thm) (t : term) (th : thm) :
    IO (Except String thm) := ExceptT.run do
  let lem' ← ExceptT.mk (REWRITE_RULE B [] (← liftExcept (INST [(V.A_, V.B_)] lem)))
  let (c, d) ← liftExcept (Basics.dest_imp (concl th))
  liftExcept do B.MP (← INST [(c, V.C_), (d, V.D_), (t, V.A_)] lem') th

/-- Given a term `[A]` and a theorem `[B ==> C]`, returns `[A /\ B ==> A /\ C]`. -/
def MKIMPR_CONJ (B : BoolThms) (V : ImpConvVars) (D : ImpConvDeps) :=
  MKIMPR_common B V D.MONO_AND

/-- Given a term `[A]` and a theorem `[B ==> C]`, returns `[A \/ B ==> A \/ C]`. -/
def MKIMPR_DISJ (B : BoolThms) (V : ImpConvVars) (D : ImpConvDeps) :=
  MKIMPR_common B V D.MONO_OR

/-- Given a term `[A]` and a theorem `[B ==> C]`, returns
    `[(A ==> B) ==> (A ==> C)]`. -/
def MKIMPR_IMP (B : BoolThms) (V : ImpConvVars) (D : ImpConvDeps) :=
  MKIMPR_common B V D.MONO_IMP

/-- Given a theorem `[A ==> B]`, returns `[~B ==> ~A]`. -/
def MKIMP_NOT (B : BoolThms) (V : ImpConvVars) (D : ImpConvDeps) (th : thm) :
    Except String thm := do
  let (b, a) ← Basics.dest_imp (concl th)
  B.MP (← INST [(a, V.A_), (b, V.B_)] D.MONO_NOT) th

/-- `MKIMP_QUANT lem x th`: `[A==>B] ↦ (Qx.A) ==> (Qx.B)` for `lem` one of the
    `MONO_FORALL`/`MONO_EXISTS` monotonicity theorems. -/
def MKIMP_QUANT (B : BoolThms) (lem : thm) (x : term) (th : thm) :
    IO (Except String thm) := ExceptT.run do
  let x_ty := type_of x
  let (p, q) ← liftExcept (Basics.dest_imp (concl th))
  let p' ← liftExcept (mk_abs x p)
  let q' ← liftExcept (mk_abs x q)
  let pty ← ExceptT.mk (mk_fun_ty x_ty bool_ty)
  let P := mk_var "P" pty
  let Q := mk_var "Q" pty
  let lem2 ← liftExcept do INST [(p', P), (q', Q)] (← INST_TYPE [(x_ty, aty)] lem)
  -- c = ONCE_DEPTH_CONV (ALPHA_CONV x) THENC ONCE_DEPTH_CONV BETA_CONV
  let c : conv := THENC (ONCE_DEPTH_CONV (ALPHA_CONV x)) (ONCE_DEPTH_CONV BETA_CONV)
  liftExcept do B.MP (← CONV_RULE c lem2) (← B.GEN x th)

/-- Given a variable `[x]` and a theorem `[A ==> B]`, returns
    `[(!x. A) ==> (!x. B)]`. -/
def MKIMP_FORALL (B : BoolThms) (D : ImpConvDeps) := MKIMP_QUANT B D.MONO_FORALL

/-- Given a variable `[x]` and a theorem `[A ==> B]`, returns
    `[(?x. A) ==> (?x. B)]`. -/
def MKIMP_EXISTS (B : BoolThms) (D : ImpConvDeps) := MKIMP_QUANT B D.MONO_EXISTS

/-- Given two theorems `[A ==> B]` and `[B ==> C ==> D]`, returns
    `[(B ==> C) ==> (A ==> D)]`, i.e., similar to `[MKIMP_IMP]` but allows to
    remove the context `[B]` since it is a consequence of `[A]`. -/
def MKIMP_IMP_CONTRA_CTXT (B : BoolThms) (V : ImpConvVars) (D : ImpConvDeps) (th1 th2 : thm) :
    Except String thm := do
  let (a, bcd) ← Basics.dest_imp (concl th2)
  let (b, cd) ← Basics.dest_imp bcd
  let (c, d) ← Basics.dest_imp cd
  B.MP (← INST [(a, V.A_), (b, V.B_), (c, V.C_), (d, V.D_)] D.mkimp_imp_contra_ctxt)
    (← B.CONJ th1 th2)

/-- Given two theorems `[A ==> B]` and `[B ==> C ==> D]`, returns
    `[(B ==> C) ==> (A ==> D)]`, i.e., similar to `[MKIMP_IMP]` but allows to
    remove the context `[B]` since it is a consequence of `[A]`. -/
def MKIMP_IMP_CO_CTXT (B : BoolThms) (V : ImpConvVars) (D : ImpConvDeps) (th1 th2 : thm) :
    Except String thm := do
  let (a, bdc) ← Basics.dest_imp (concl th2)
  let (b, dc) ← Basics.dest_imp bdc
  let (d, c) ← Basics.dest_imp dc
  B.MP (← INST [(a, V.A_), (b, V.B_), (c, V.C_), (d, V.D_)] D.mkimp_imp_co_ctxt)
    (← B.CONJ th1 th2)

/-- Given a theorem `[B ==> C ==> D]`, returns `[(B ==> C) ==> (B ==> D)]`,
    i.e., similar to `[MKIMP_IMP]` but allows to remove the context `[B]`
    since it is a consequence of `[A]`. -/
def MKIMPR_IMP_CTXT (B : BoolThms) (V : ImpConvVars) (D : ImpConvDeps) (th : thm) :
    Except String thm := do
  let (a, cd) ← Basics.dest_imp (concl th)
  let (c, d) ← Basics.dest_imp cd
  B.MP (← INST [(c, V.C_), (d, V.D_), (a, V.A_)] D.mkimpr_imp_ctxt) th

/-- Given two theorems `[A ==> B]` and `[A ==> B ==> C ==> D]`, returns
    `[(A /\ C) ==> (B /\ D)]`, i.e., similar to `[MKIMP_CONJ]` but allows to
    remove the contexts `[A]` and `[B]`. -/
def MKIMP_CONJ_CONTRA_CTXT (B : BoolThms) (V : ImpConvVars) (D : ImpConvDeps) (th1 th2 : thm) :
    Except String thm := do
  let (a, bcd) ← Basics.dest_imp (concl th2)
  let (b, cd) ← Basics.dest_imp bcd
  let (c, d) ← Basics.dest_imp cd
  B.MP (← INST [(a, V.A_), (b, V.B_), (c, V.C_), (d, V.D_)] D.mkimp_conj_contra_ctxt)
    (← B.CONJ th1 th2)

/-- `MKIMPL_CONJ_CONTRA_CTXT`: `th : C==>A==>B` ↦ `(A/\C==>B/\C)`. -/
def MKIMPL_CONJ_CONTRA_CTXT (B : BoolThms) (V : ImpConvVars) (D : ImpConvDeps) (th : thm) :
    Except String thm := do
  let (c, ab) ← Basics.dest_imp (concl th)
  let (a, b) ← Basics.dest_imp ab
  B.MP (← INST [(a, V.A_), (b, V.B_), (c, V.C_)] D.mkimpl_conj_contra_ctxt) th

/-- `MKIMPR_CONJ_CONTRA_CTXT`: `th : A==>C==>D` ↦ `(A/\C==>A/\D)`. -/
def MKIMPR_CONJ_CONTRA_CTXT (B : BoolThms) (V : ImpConvVars) (D : ImpConvDeps) (th : thm) :
    Except String thm := do
  let (a, cd) ← Basics.dest_imp (concl th)
  let (c, d) ← Basics.dest_imp cd
  B.MP (← INST [(a, V.A_), (c, V.C_), (d, V.D_)] D.mkimpr_conj_contra_ctxt) th

/-- Given two theorems `[A ==> B]` and `[A ==> B ==> C ==> D]`, returns
    `[(A /\ C) ==> (B /\ D)]`, i.e., similar to `[MKIMP_CONJ]` but allows to
    remove the contexts `[A]` and `[B]`. -/
def MKIMP_CONJ_CO_CTXT (B : BoolThms) (V : ImpConvVars) (D : ImpConvDeps) (th1 th2 : thm) :
    Except String thm := do
  let (b, a) ← Basics.dest_imp (concl th1)
  let (_, dc) ← Basics.dest_imp (concl th2)
  let (d, c) ← Basics.dest_imp dc
  B.MP (← INST [(a, V.A_), (b, V.B_), (c, V.C_), (d, V.D_)] D.mkimp_conj_co_ctxt)
    (← B.CONJ th1 th2)

/-- `MKIMPL_CONJ_CO_CTXT`: `th : B==>A` ↦ `fun c -> (B/\C==>A/\C)`. -/
def MKIMPL_CONJ_CO_CTXT (B : BoolThms) (V : ImpConvVars) (D : ImpConvDeps) (th : thm)
    (c : term) : Except String thm := do
  let (b, a) ← Basics.dest_imp (concl th)
  B.MP (← INST [(a, V.A_), (b, V.B_), (c, V.C_)] D.mkimpl_conj_co_ctxt) th

/-- `MKIMPL_CONJ_CO2_CTXT`: `th : C==>B==>A` ↦ `(B/\C==>A/\C)`. -/
def MKIMPL_CONJ_CO2_CTXT (B : BoolThms) (V : ImpConvVars) (D : ImpConvDeps) (th : thm) :
    Except String thm := do
  let (c, ba) ← Basics.dest_imp (concl th)
  let (b, a) ← Basics.dest_imp ba
  B.MP (← INST [(a, V.A_), (b, V.B_), (c, V.C_)] D.mkimpl_conj_co2_ctxt) th

/-- `MKIMPR_CONJ_CO_CTXT = MKIMPR_CONJ_CONTRA_CTXT`. -/
def MKIMPR_CONJ_CO_CTXT := MKIMPR_CONJ_CONTRA_CTXT

/- ---------------------------------------------------------------------- -/
/- Implicational conversions: core type + combinators                     -/
/- (`impconv.ml` 743-833).                                                -/
/- ---------------------------------------------------------------------- -/

open Variance (t)

/-- An implicational conversion maps a term `t` to a theorem of the form:
    `t' ==> t` if covariant, `t ==> t'` if contravariant.  IO because it chains
    `GEN_PART_MATCH`/`IMP_TRANS`. -/
abbrev imp_conv := Variance.t → term → IO (Except String thm)

/-- Trivial embedding of conversions into implicational conversions.  From
    `c t : |- t = t'`, `EQ_IMP_RULE` gives `(t ==> t', t' ==> t)`; return
    `t' ==> t` (Co) or `t ==> t'` (Contra). -/
def imp_conv_of_conv (B : BoolThms) (c : conv) : imp_conv := fun v t => do
  match c t with
  | .error e => return .error e
  | .ok eqth =>
    match B.EQ_IMP_RULE eqth with
    | .error e => return .error e
    | .ok (th1, th2) => match v with | .Co => return .ok th2 | .Contra => return .ok th1

/-- Retrieves the outcome of an implicational conversion, i.e., `t'`. -/
def imp_conv_outcome (th : thm) (v : Variance.t) : Except String term := do
  let (t1, t2) ← dest_binary_blind (concl th)
  match v with | .Co => .ok t1 | .Contra => .ok t2

/-- `[ALL_IMPCONV _ t]` returns `[t ==> t]`. -/
def ALL_IMPCONV (D : ImpConvDeps) (V : ImpConvVars) : imp_conv :=
  fun _ t => return (IMP_REFL D V t)

/-- The implicational conversion which always fails. -/
def NO_IMPCONV : imp_conv := fun _ _ => return (failwith "NO_IMPCONV")

/-- `bind_impconv c v th`: chain `c` into the appropriate side of `th`. -/
def bind_impconv (B : BoolThms) (c : imp_conv) (v : Variance.t) (th : thm) :
    IO (Except String thm) := do
  match Basics.dest_imp (concl th) with
  | .error e => return .error e
  | .ok (t1, t2) =>
    match v with
    | .Co => match ← c v t1 with
             | .ok cth => return (B.IMP_TRANS cth th)
             | .error e => return .error e
    | .Contra => match ← c v t2 with
                 | .ok cth => return (B.IMP_TRANS th cth)
                 | .error e => return .error e

/-- `THEN_IMPCONV c1 c2 v t = bind_impconv c2 v (c1 v t)`. -/
def THEN_IMPCONV (B : BoolThms) (c1 c2 : imp_conv) : imp_conv := fun v t => do
  match ← c1 v t with
  | .error e => return .error e
  | .ok th => bind_impconv B c2 v th

/-- Given a theorem `[p ==> c]`, returns the implicational conversion which:
    in the covariant case, matches the input term `[t]` against `[c]` and
    returns `[s(p) ==> t]`, where `[s]` is the matching substitution; in the
    contravariant case, matches the input term `[t]` against `[p]` and returns
    `[t ==> s(c)]`, where `[s]` is the matching substitution. -/
def MATCH_MP_IMPCONV (B : BoolThms) (th : thm) : imp_conv := fun v t =>
  match v with
  | .Co => GEN_PART_MATCH B rand th t
  | .Contra => GEN_PART_MATCH B lhand th t

/- ---------------------------------------------------------------------- -/
/- INTERFACE                                                              -/
/- ---------------------------------------------------------------------- -/

/-- From an implicational conversion builds a rule, i.e., a function which
    takes a theorem and returns a new theorem.

    `IMPCONV_RULE c th = MATCH_MP (c Contra (concl th)) th`. -/
def IMPCONV_RULE (B : BoolThms) (c : imp_conv) (th : thm) : IO (Except String thm) := do
  let t := concl th
  match ← c .Contra t with
  | .error e => return .error e
  | .ok cth => MATCH_MP B cth th

/-- From an implicational conversion builds a tactic. -/
def IMPCONV_TAC (B : BoolThms) (c : imp_conv) : tactic := fun g => do
  let (_, cgoal) := g
  match ← c .Co cgoal with
  | .error e => return .error e
  | .ok cth =>
    Tactics.THEN B (Tactics.MATCH_MP_TAC B cth)
      (Tactics.TRY B (Tactics.ACCEPT_TAC B B.TRUTH)) g

/- ---------------------------------------------------------------------- -/
/- Context handling (`impconv.ml` 809-833).                               -/
/- ---------------------------------------------------------------------- -/

/-- `[term list]` = terms to add to the context.
    `'a with_context = With_context of 'a * (Tset.t -> 'a with_context) *
    (term -> 'a with_context)`.  A value paired with augment/diminish
    continuations (recursive, pure — `IO` cannot appear under the inductive for
    positivity, so `IMPREWR_CTXCONV` defers its net-building `IO` into `apply`). -/
inductive WithContext (α : Type) where
  | mk : α → (Tset.t → WithContext α) → (term → WithContext α) → WithContext α
  | bot : WithContext α   -- base case so the type is trivially `Inhabited`
  deriving Inhabited

/-- `apply (With_context(c,_,_)) = c`. -/
def WithContext.apply {α : Type} [Inhabited α] : WithContext α → α
  | .mk c _ _ => c
  | .bot => default

/-- `augment (With_context(_,a,_)) = a`.  (Maybe avoid the augment if the input
    list is empty?) -/
def WithContext.augment {α : Type} : WithContext α → (Tset.t → WithContext α)
  | .mk _ a _ => a
  | .bot => fun _ => .bot

/-- `diminish (With_context(_,_,d)) = d`. -/
def WithContext.diminish {α : Type} : WithContext α → (term → WithContext α)
  | .mk _ _ d => d
  | .bot => fun _ => .bot

/-- `apply_with_context c ctx v t =
    DISCH_CONJ ctx (apply (augment c (Tset.strip_conj ctx)) v t)`. -/
def apply_with_context (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars)
    (c : WithContext imp_conv) (ctx : term) (v : Variance.t) (t : term) :
    IO (Except String thm) := do
  match ← (c.augment (Tset.strip_conj V.T_ ctx)).apply v t with
  | .error e => return .error e
  | .ok th => DISCH_CONJ B D ctx th

/-- `imp_conv_of_ctx_imp_conv = apply`. -/
def imp_conv_of_ctx_imp_conv : WithContext imp_conv → imp_conv := WithContext.apply

/- ---------------------------------------------------------------------- -/
/- CTXIMPCONV combinators (`impconv.ml` 835-1145).                        -/
/- ---------------------------------------------------------------------- -/

/-- Sentinel error string modelling HOL Light's `Unchanged` exception (HolCore
    has no dedicated `Unchanged`; see the module note). -/
def unchanged : String := "Unchanged"

/-- Run the handler `h` only for a genuine `Failure`; let the `Unchanged`
    sentinel PROPAGATE.  OCaml's `try E with Failure _ -> H` does NOT catch the
    `Unchanged` exception (impconv.ml 835-1125): it escapes to
    `UNCHANGED_OF_FAIL`/`REPEAT_UNCHANGED`/`fail_if_unchanged`.  A Lean
    catch-all `| .error _ => H` would swallow it and turn "no change" into an
    identity step (class #9).  Only `TRY_CTXIMPCONV`, whose OCaml handler is
    `with Failure _ | Unchanged`, legitimately catches both. -/
@[inline] def failureOnly {α : Type} (e : String) (h : IO (Except String α)) :
    IO (Except String α) :=
  if e == unchanged then return .error e else h

/- The mutually-recursive structural implicational-conversion builders.  Each
   `X_CTXIMPCONV c` returns a `WithContext imp_conv` whose `apply` handles the
   corresponding connective and whose `augment`/`diminish` recurse into `c`. -/
mutual

/- Consider two implicational conversions ic1, ic2.  Suppose `[ic1 Co A]`
   returns `[B ==> A]`, and `[ic2 Co C]` returns `[D ==> C]`, then
   `[CONJ_IMPCONV ic1 ic2 Co (A /\ C)]` returns `[B /\ D ==> A /\ C]`.  Suppose
   `[ic1 Contra A]` returns `[A ==> B]`, and `[ic2 Contra C]` returns
   `[C ==> D]`, then `[CONJ_IMPCONV ic1 ic2 Contra (A /\ B)]` returns
   `[A /\ B ==> C /\ D]`.  Additionally takes the context into account, i.e., if
   `[ic2 Co C]` returns `[A |- D ==> C]`, then
   `[CONJ_IMPCONV ic1 ic2 Co (A /\ B)]` returns `[|- C /\ D ==> A /\ B]` (i.e.,
   `[A]` does not appear in the hypotheses). -/
partial def CONJ_CTXIMPCONV (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars)
    (c : WithContext imp_conv) : WithContext imp_conv :=
  .mk
    (fun v t => do
      match Basics.dest_conj t with
      | .error e => return .error e
      | .ok (t1, t2) =>
        match v with
        | .Co =>
          -- try (th1 = apply c Co t1; try MKIMP_CONJ_CO_CTXT th1 (apply_with_context c t1' Co t2)
          --      with _ -> MKIMPL_CONJ_CO_CTXT th1 t2) with _ -> MKIMPR_CONJ_CO_CTXT (apply_with_context c t1 Co t2)
          match ← c.apply .Co t1 with
          | .ok th1 =>
            match imp_conv_outcome th1 .Co with
            | .ok t1' =>
              match ← apply_with_context B D V c t1' .Co t2 with
              | .ok awc => match MKIMP_CONJ_CO_CTXT B V D th1 awc with
                           | .ok r => return .ok r
                           | .error _ => return (MKIMPL_CONJ_CO_CTXT B V D th1 t2)
              | .error e => failureOnly e (return (MKIMPL_CONJ_CO_CTXT B V D th1 t2))
            | .error _ => return (MKIMPL_CONJ_CO_CTXT B V D th1 t2)  -- inner try: outcome fail → MKIMPL
          | .error e => failureOnly e do
            match ← apply_with_context B D V c t1 .Co t2 with
            | .ok awc => return (MKIMPR_CONJ_CO_CTXT B V D awc)
            | .error e => return .error e
        | .Contra =>
          -- note: we remove t1 in case it appears in t2, since otherwise,
          -- t1 removes t2 and t2 removes t1
          let t2s := Tset.remove (Tset.strip_conj V.T_ t2) t1
          match ← (c.augment t2s).apply .Contra t1 with
          | .ok th1 =>
            match imp_conv_outcome th1 .Contra with
            | .ok t1' =>
              let t1s := Tset.strip_conj V.T_ t1
              let t1s' := Tset.strip_conj V.T_ t1'
              let t1s'' := Tset.union t1s t1s'
              match ← (c.augment t1s'').apply .Contra t2 with
              | .ok th2 =>
                match ← (ExceptT.run do
                  let th2a ← ExceptT.mk (DISCH_CONJ B D t1' th2)
                  let th2' ← ExceptT.mk (DISCH_CONJ B D t1 th2a)
                  let dc ← ExceptT.mk (DISCH_CONJ B D t2 th1)
                  liftExcept (MKIMP_CONJ_CONTRA_CTXT B V D dc th2')) with
                | .ok r => return .ok r
                | .error _ =>
                  match ← DISCH_CONJ B D t2 th1 with
                  | .ok dc => return (MKIMPL_CONJ_CONTRA_CTXT B V D dc)
                  | .error e => return .error e
              | .error e => failureOnly e do
                match ← DISCH_CONJ B D t2 th1 with
                | .ok dc => return (MKIMPL_CONJ_CONTRA_CTXT B V D dc)
                | .error e => return .error e
            | .error _ =>
              match ← DISCH_CONJ B D t2 th1 with
              | .ok dc => return (MKIMPL_CONJ_CONTRA_CTXT B V D dc)
              | .error e => return .error e
          | .error e => failureOnly e do
            match ← apply_with_context B D V c t1 .Contra t2 with
            | .ok awc => return (MKIMPR_CONJ_CONTRA_CTXT B V D awc)
            | .error e => return .error e)
    (fun x => CONJ_CTXIMPCONV B D V (c.augment x))
    (fun x => CONJ_CTXIMPCONV B D V (c.diminish x))

/- Consider two implicational conversions ic1, ic2.  Suppose `[ic1 Co A]`
   returns `[B ==> A]`, and `[ic2 Co C]` returns `[D ==> C]`, then
   `[DISJ_IMPCONV ic1 ic2 Co (A \/ C)]` returns `[B \/ D ==> A \/ C]`.  Suppose
   `[ic1 Contra A]` returns `[A ==> B]`, and `[ic2 Contra C]` returns
   `[C ==> D]`, then `[DISJ_IMPCONV ic1 ic2 Contra (A \/ B)]` returns
   `[A \/ B ==> C \/ D]`. -/
partial def DISJ_CTXIMPCONV (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars)
    (c : WithContext imp_conv) : WithContext imp_conv :=
  .mk
    (fun v t => do
      match Basics.dest_disj t with
      | .error e => return .error e
      | .ok (t1, t2) =>
        match ← c.apply v t1 with
        | .ok th1 =>
          match ← c.apply v t2 with
          | .ok th2 => match MKIMP_DISJ B V D th1 th2 with
                       | .ok r => return .ok r
                       | .error _ => MKIMPL_DISJ B V D th1 t2
          | .error e => failureOnly e (MKIMPL_DISJ B V D th1 t2)
        | .error e => failureOnly e do
          match ← c.apply v t2 with
          | .ok th2 => MKIMPR_DISJ B V D t1 th2
          | .error e => return .error e)
    (fun x => DISJ_CTXIMPCONV B D V (c.augment x))
    (fun x => DISJ_CTXIMPCONV B D V (c.diminish x))

/- Consider two implicational conversions ic1, ic2.  Suppose `[ic1 Contra A]`
   returns `[A ==> B]`, and `[ic2 Co C]` returns `[D ==> C]`, then
   `[IMP_IMPCONV ic1 ic2 Co (A ==> C)]` returns `[(B ==> D) ==> (A ==> C)]`.
   Suppose `[ic1 Co A]` returns `[B ==> A]`, and `[ic2 Contra C]` returns
   `[C ==> D]`, then `[IMP_IMPCONV ic1 ic2 Contra (A ==> C)]` returns
   `[(A ==> C) ==> (B ==> D)]`.  Additionally takes the context into account,
   i.e., if `[ic2 Co C]` returns `[B |- D ==> C]`, then
   `[IMP_IMPCONV ic1 ic2 Co (A ==> C)]` returns `[|- (B ==> D) ==> (A ==> C)]`
   (i.e., `[B]` does not appear in the hypotheses). -/
partial def IMP_CTXIMPCONV (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars)
    (c : WithContext imp_conv) : WithContext imp_conv :=
  .mk
    (fun v t => do
      match Basics.dest_imp t with
      | .error e => return .error e
      | .ok (t1, t2) =>
        let v' := Variance.neg v
        match ← c.apply v' t1 with
        | .ok th1 =>
          match imp_conv_outcome th1 v' with
          | .error _ =>
            -- outer try: outcome failure → MKIMPR_IMP_CTXT (apply_with_context c t1 v t2)
            match ← apply_with_context B D V c t1 v t2 with
            | .ok awc => return (MKIMPR_IMP_CTXT B V D awc)
            | .error e => return .error e
          | .ok t1' =>
            let t1s := Tset.union (Tset.strip_conj V.T_ t1) (Tset.strip_conj V.T_ t1')
            let c' := c.augment t1s
            let mk := match v with | .Co => MKIMP_IMP_CO_CTXT | .Contra => MKIMP_IMP_CONTRA_CTXT
            -- try mk th1 (DISCH_CONJ t1 (DISCH_CONJ t1' (apply c' v t2))) with _ -> MKIMPL_IMP th1 t2
            match ← c'.apply v t2 with
            | .error e => failureOnly e (MKIMPL_IMP B V D th1 t2)
            | .ok th2v =>
              match ← (ExceptT.run do
                let dj ← ExceptT.mk (DISCH_CONJ B D t1' th2v)
                let inner ← ExceptT.mk (DISCH_CONJ B D t1 dj)
                liftExcept (mk B V D th1 inner)) with
              | .ok r => return .ok r
              | .error _ => MKIMPL_IMP B V D th1 t2
        | .error e => failureOnly e do
          match ← apply_with_context B D V c t1 v t2 with
          | .ok awc => return (MKIMPR_IMP_CTXT B V D awc)
          | .error e => return .error e)
    (fun x => IMP_CTXIMPCONV B D V (c.augment x))
    (fun x => IMP_CTXIMPCONV B D V (c.diminish x))

partial def IFF_CTXIMPCONV (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars)
    (c : WithContext imp_conv) : WithContext imp_conv :=
  .mk
    (fun v t => do
      match dest_iff t with
      | .error e => return .error e
      | .ok (t1, t2) =>
        let (lr, l, r) := match v with
          | .Co => (MKIMP_CO_IFF B V D, MKIMPL_CO_IFF B V D, MKIMPR_CO_IFF B V D)
          | .Contra => (MKIMP_CONTRA_IFF B V D, MKIMPL_CONTRA_IFF B V D, MKIMPR_CONTRA_IFF B V D)
        match mk_imp t1 t2 with
        | .error e => return .error e
        | .ok i12 =>
          match ← c.apply v i12 with
          | .ok th1 =>
            match mk_imp t2 t1 with
            | .error e => return .error e
            | .ok i21 =>
              match ← c.apply v i21 with
              | .ok th2 => match MKIMP_IFF B V D th1 th2 with
                           | .ok rr => return .ok rr
                           | .error _ => return (lr th1 th2)
              | .error e => failureOnly e (return (l th1))
          | .error e => failureOnly e do
            match mk_imp t2 t1 with
            | .error e => return .error e
            | .ok i21 => match ← c.apply v i21 with
                         | .ok th2 => return (r th2)
                         | .error e => return .error e)
    (fun x => IFF_CTXIMPCONV B D V (c.augment x))
    (fun x => IFF_CTXIMPCONV B D V (c.diminish x))

/- Consider an implicational conversion ic.  Suppose `[ic Contra A]` returns
   `[A ==> B]` then `[NOT_IMPCONV ic Co ~A]` returns `[~B ==> ~A]`.  Suppose
   `[ic Co A]` returns `[B ==> A]` then `[NOT_IMPCONV ic Contra ~A]` returns
   `[~A ==> ~B]`. -/
partial def NOT_CTXIMPCONV (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars)
    (c : WithContext imp_conv) : WithContext imp_conv :=
  .mk
    (fun v t => do
      match dest_neg t with
      | .error e => return .error e
      | .ok nt => match ← c.apply (Variance.neg v) nt with
                  | .ok th => return (MKIMP_NOT B V D th)
                  | .error e => return .error e)
    (fun x => NOT_CTXIMPCONV B D V (c.augment x))
    (fun x => NOT_CTXIMPCONV B D V (c.diminish x))

partial def QUANT_CTXIMPCONV (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars)
    (mkimp : term → thm → IO (Except String thm))
    (sel : term → Except String (term × term))
    (c : WithContext imp_conv) : WithContext imp_conv :=
  .mk
    (fun v t => do
      match sel t with
      | .error e => return .error e
      | .ok (x, b) =>
        let c' := c.diminish x
        match ← c'.apply v b with
        | .ok ab => mkimp x ab
        | .error e => return .error e)
    (fun y => QUANT_CTXIMPCONV B D V mkimp sel (c.augment y))
    (fun y => QUANT_CTXIMPCONV B D V mkimp sel (c.diminish y))

/- Consider an implicational conversion ic.  Suppose `[ic Co A]` returns
   `[B ==> A]` then `[FORALL_IMPCONV ic Co (!x.A)]` returns
   `[(!x.B) ==> (!x.A)]`.  Suppose `[ic Contra A]` returns `[A ==> B]` then
   `[FORALL_IMPCONV ic Contra (!x.A)]` returns `[(!x.A) ==> (!x.B)]`. -/
partial def FORALL_CTXIMPCONV (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars) :
    WithContext imp_conv → WithContext imp_conv :=
  QUANT_CTXIMPCONV B D V (MKIMP_FORALL B D) Basics.dest_forall

/- Consider an implicational conversion ic.  Suppose `[ic Co A]` returns
   `[B ==> A]` then `[EXISTS_IMPCONV ic Co (?x.A)]` returns
   `[(?x.B) ==> (?x.A)]`.  Suppose `[ic Contra A]` returns `[A ==> B]` then
   `[EXISTS_IMPCONV ic Contra (?x.A)]` returns `[(?x.A) ==> (?x.B)]`. -/
partial def EXISTS_CTXIMPCONV (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars) :
    WithContext imp_conv → WithContext imp_conv :=
  QUANT_CTXIMPCONV B D V (MKIMP_EXISTS B D) Basics.dest_exists

/- Applies an implicational conversion on the subformula(s) of the input term. -/
partial def SUB_CTXIMPCONV (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars)
    (c : WithContext imp_conv) : WithContext imp_conv :=
  .mk
    (fun v t => do
      let iff_ty : hol_type := .Tyapp "fun" [bool_ty, .Tyapp "fun" [bool_ty, bool_ty]]
      match dest_const (Prod.fst (strip_comb t)) with
      | .error _ => return (failwith "dest_const")   -- non-constant head: generic Failure (→ Non_atomic in DEPTH)
      | .ok (n, ty) =>
        let builder : Option (WithContext imp_conv) :=
          if n == "==>" then some (IMP_CTXIMPCONV B D V c)
          else if n == "/\\" then some (CONJ_CTXIMPCONV B D V c)
          else if n == "\\/" then some (DISJ_CTXIMPCONV B D V c)
          else if n == "=" && ty == iff_ty then some (IFF_CTXIMPCONV B D V c)
          else if n == "!" then some (FORALL_CTXIMPCONV B D V c)
          else if n == "?" then some (EXISTS_CTXIMPCONV B D V c)
          else if n == "~" then some (NOT_CTXIMPCONV B D V c)
          else none
        match builder with
        | some wc => wc.apply v t
        | none => return (failwith "SUB_CTXIMPCONV"))
    (fun x => SUB_CTXIMPCONV B D V (c.augment x))
    (fun x => SUB_CTXIMPCONV B D V (c.diminish x))

end

/-- Takes a theorem which results of an implicational conversion and applies
    another implicational conversion on the outcome. -/
def bind_ctximpconv (B : BoolThms) (c : WithContext imp_conv) (v : Variance.t) (th : thm) :
    IO (Except String thm) := do
  match Basics.dest_imp (concl th) with
  | .error e => return .error e
  | .ok (t1, t2) =>
    match v with
    | .Co => match ← c.apply v t1 with
             | .ok a => return (B.IMP_TRANS a th) | .error e => return .error e
    | .Contra => match ← c.apply v t2 with
                 | .ok a => return (B.IMP_TRANS th a) | .error e => return .error e

/-- `BIND_CTXIMPCONV c`.  (Its wrapped function takes a *theorem* — the outcome
    of a previous implicational conversion — so it lives at the type
    `Variance.t → thm → IO (Except thm)`, distinct from `imp_conv`.  Defined for
    faithfulness; unused elsewhere in `impconv.ml`.) -/
partial def BIND_CTXIMPCONV (B : BoolThms)
    (c : WithContext imp_conv) : WithContext (Variance.t → thm → IO (Except String thm)) :=
  .mk (fun v th => bind_ctximpconv B c v th)
    (fun x => BIND_CTXIMPCONV B (c.augment x))
    (fun x => BIND_CTXIMPCONV B (c.diminish x))

/-- Sequential combinator. -/
partial def THEN_CTXIMPCONV (B : BoolThms) (c1 c2 : WithContext imp_conv) :
    WithContext imp_conv :=
  .mk (fun v t => do
        match ← c1.apply v t with
        | .ok th => bind_ctximpconv B c2 v th
        | .error e => return .error e)
    (fun x => THEN_CTXIMPCONV B (c1.augment x) (c2.augment x))
    (fun x => THEN_CTXIMPCONV B (c1.diminish x) (c2.diminish x))

/-- Try combinator.  (On `Failure`/`Unchanged`, falls back to `ALL_IMPCONV`.) -/
partial def TRY_CTXIMPCONV (D : ImpConvDeps) (V : ImpConvVars) (c : WithContext imp_conv) :
    WithContext imp_conv :=
  .mk (fun v t => do
        match ← c.apply v t with
        | .ok th => return .ok th
        | .error _ => ALL_IMPCONV D V v t)
    (fun x => TRY_CTXIMPCONV D V (c.augment x))
    (fun x => TRY_CTXIMPCONV D V (c.diminish x))

/-- Applies the first of two implicational conversions that succeeds. -/
partial def ORELSE_CTXIMPCONV (c1 c2 : WithContext imp_conv) : WithContext imp_conv :=
  .mk (fun v t => do
        match ← c1.apply v t with
        | .ok th => return .ok th
        | .error e => failureOnly e (c2.apply v t))
    (fun x => ORELSE_CTXIMPCONV (c1.augment x) (c2.augment x))
    (fun x => ORELSE_CTXIMPCONV (c1.diminish x) (c2.diminish x))

/-- Makes an implicational conversion fail if applying it leaves a term
    unchanged. -/
partial def CHANGED_CTXIMPCONV (c : WithContext imp_conv) : WithContext imp_conv :=
  .mk (fun v t => do
        match ← c.apply v t with
        | .error e => return .error e
        | .ok th => match Basics.dest_imp (concl th) with
                    | .error e => return .error e
                    | .ok (l, r) => if aconv l r then return (failwith "CHANGED_CTXIMPCONV")
                                    else return .ok th)
    (fun x => CHANGED_CTXIMPCONV (c.augment x))
    (fun x => CHANGED_CTXIMPCONV (c.diminish x))

/-- `UNCHANGED_OF_FAIL_CTXIMPCONV c`: turn a failure into `Unchanged`. -/
partial def UNCHANGED_OF_FAIL_CTXIMPCONV (c : WithContext imp_conv) : WithContext imp_conv :=
  .mk (fun v t => do
        match ← c.apply v t with
        | .ok th => return .ok th
        | .error _ => return (.error unchanged))
    (fun x => UNCHANGED_OF_FAIL_CTXIMPCONV (c.augment x))
    (fun x => UNCHANGED_OF_FAIL_CTXIMPCONV (c.diminish x))

/-- `REPEAT_UNCHANGED_CTXIMPCONV cs`: cycle through `cs`, binding each until a
    full pass makes no change (signalled by `Unchanged`). -/
partial def REPEAT_UNCHANGED_CTXIMPCONV (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars)
    (cs : List (WithContext imp_conv)) : WithContext imp_conv :=
  .mk (fun v t => do
        let rec loop (changed : Bool) (acc : thm) (rest : List (WithContext imp_conv)) :
            IO (Except String thm) := do
          match rest with
          | [] => if changed then loop false acc cs else return .ok acc
          | c :: cs' =>
            match ← bind_ctximpconv B c v acc with
            | .ok acc' => loop true acc' cs'
            | .error e => if e == unchanged then loop changed acc cs'
                          else return .error e   -- OCaml catches only Unchanged; others propagate
        match IMP_REFL D V t with
        | .ok r0 => loop false r0 cs
        | .error e => return .error e)
    (fun x => REPEAT_UNCHANGED_CTXIMPCONV B D V (cs.map (·.augment x)))
    (fun x => REPEAT_UNCHANGED_CTXIMPCONV B D V (cs.map (·.diminish x)))

/-- Whether the current subterm is atomic (for `DEPTH`/`ONCE_DEPTH`). -/
inductive atomic where | Atomic | Non_atomic
  deriving BEq, Inhabited

/-- `DEPTH_CTXIMPCONV`: bottom-up depth conversion over an
    `(atomic -> imp_conv) with_context`. -/
partial def depthSelf (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars)
    (c : WithContext (atomic → imp_conv)) : WithContext imp_conv :=
  let bind (na : atomic) (v : Variance.t) (th : thm) : IO (Except String thm) := do
    match Basics.dest_imp (concl th) with
    | .error e => return .error e
    | .ok (t1, t2) =>
      match v with
      | .Co => match ← c.apply na v t1 with | .ok a => return (B.IMP_TRANS a th) | .error e => return .error e
      | .Contra => match ← c.apply na v t2 with | .ok a => return (B.IMP_TRANS th a) | .error e => return .error e
  .mk
    (fun v t => do
      -- imp_conv view of `self c` for SUB
      let selfCtx : WithContext imp_conv := depthSelf B D V c
      match ← (SUB_CTXIMPCONV B D V selfCtx).apply v t with
      | .ok th1 => match ← bind .Non_atomic v th1 with | .ok r => return .ok r | .error e => failureOnly e (return .ok th1)
      | .error e =>
        if e == unchanged then return .error e
        else if e == "SUB_CTXIMPCONV" then
          match ← c.apply .Atomic v t with
          | .error e2 => return .error e2
          | .ok th1 => match ← bind_ctximpconv B (depthSelf B D V c) v th1 with
                       | .ok r => return .ok r | .error e => failureOnly e (return .ok th1)
        else c.apply .Non_atomic v t)
    (fun x => depthSelf B D V (c.augment x))
    (fun x => depthSelf B D V (c.diminish x))

/-- `DEPTH_CTXIMPCONV = UNCHANGED_OF_FAIL_CTXIMPCONV o self` (impconv.ml 1079). -/
def DEPTH_CTXIMPCONV (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars) :
    WithContext (atomic → imp_conv) → WithContext imp_conv :=
  UNCHANGED_OF_FAIL_CTXIMPCONV o depthSelf B D V    -- self runs FIRST

/-- `TOP_DEPTH_CTXIMPCONV`'s `self`. -/
partial def topDepthSelf (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars)
    (c : WithContext imp_conv) : WithContext imp_conv :=
  .mk
    (fun v t => do
      match ← c.apply v t with
      | .ok th => match ← bind_ctximpconv B (topDepthSelf B D V c) v th with
                  | .ok r => return .ok r | .error e => failureOnly e (return .ok th)
      | .error e => failureOnly e ((SUB_CTXIMPCONV B D V (topDepthSelf B D V c)).apply v t))
    (fun x => topDepthSelf B D V (c.augment x))
    (fun x => topDepthSelf B D V (c.diminish x))

/-- `TOP_DEPTH_CTXIMPCONV = UNCHANGED_OF_FAIL_CTXIMPCONV o self` (impconv.ml 1102). -/
def TOP_DEPTH_CTXIMPCONV (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars) :
    WithContext imp_conv → WithContext imp_conv :=
  UNCHANGED_OF_FAIL_CTXIMPCONV o topDepthSelf B D V  -- self runs FIRST

/-- `ONCE_DEPTH_CTXIMPCONV`'s `self`. -/
partial def onceDepthSelf (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars)
    (c : WithContext (atomic → imp_conv)) : WithContext imp_conv :=
  .mk
    (fun v t => do
      match ← (SUB_CTXIMPCONV B D V (onceDepthSelf B D V c)).apply v t with
      | .ok r => return .ok r
      | .error e =>
        if e == unchanged then return .error e
        else if e == "SUB_CTXIMPCONV" then c.apply .Atomic v t
        else c.apply .Non_atomic v t)
    (fun x => onceDepthSelf B D V (c.augment x))
    (fun x => onceDepthSelf B D V (c.diminish x))

/-- `ONCE_DEPTH_CTXIMPCONV = UNCHANGED_OF_FAIL_CTXIMPCONV o self` (impconv.ml 1115). -/
def ONCE_DEPTH_CTXIMPCONV (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars) :
    WithContext (atomic → imp_conv) → WithContext imp_conv :=
  UNCHANGED_OF_FAIL_CTXIMPCONV o onceDepthSelf B D V  -- self runs FIRST

/-- `CTXIMPCONV_RULE c th = MATCH_MP (apply c Contra (concl th)) th`. -/
def CTXIMPCONV_RULE (B : BoolThms) (c : WithContext imp_conv) (th : thm) :
    IO (Except String thm) := do
  match ← c.apply .Contra (concl th) with
  | .ok cth => MATCH_MP B cth th
  | .error e => return .error e

/-- `CTXIMPCONV_TAC c`: augment with the assumptions, `MATCH_MP_TAC (c Co goal)`. -/
def CTXIMPCONV_TAC (B : BoolThms) (_V : ImpConvVars) (cnv : WithContext imp_conv) : tactic :=
  fun g => do
    let (asms, cgoal) := g
    let cnv' := cnv.augment (asms.map (fun p => concl p.2))
    match ← cnv'.apply .Co cgoal with
    | .error e => return .error e
    | .ok cth =>
      Tactics.THEN B (Tactics.MATCH_MP_TAC B cth)
        (Tactics.TRY B (Tactics.ACCEPT_TAC B B.TRUTH)) g

/- ---------------------------------------------------------------------- -/
/- Rewrite implicational conversion (`impconv.ml` 1147-1345).             -/
/- ---------------------------------------------------------------------- -/

/-- Given a theorem `[H1,...,Hn |- P ==> l = r]`, returns the variables that
    occur in `[P]` and `[r]` but not in the rest.  Basically represents the
    variables that are introduced by the implicational rewrite (similar status
    as variables occurring in the r.h.s. of a rewrite but not in the l.h.s.). -/
def indep_vars (B : BoolThms) (th : thm) : Except String (List term) := do
  let sth ← B.SPEC_ALL th
  let (hs, c) := dest_thm sth
  let (p, c) ← Basics.dest_imp c
  let all_vars := union (frees p) (frees (← rhs c))
  let dep_vars := union (frees (← lhs c)) (freesl hs)
  return subtract all_vars dep_vars

/-- Given a list of variables to avoid `[v1,...,vk]`, a theorem of the form
    `[hs |- !x1...xn. p ==> !y1...ym. l = r]`, and a term `[t]`, matches `[t]`
    with `[l]`, yielding the substitution `[s]`, and returns the theorem
    `[s(hs) |- !z1...zp. s(p) ==> s(l) = s(r)]` where `[z1]`, ..., `[zp]` are the
    variables among `[x1]`, ..., `[xn]`, `[y1]`, ..., `[ym]` that are not
    instantiated by `[s]`, and renamed so as to avoid `[v1]`, ..., `[vk]`. -/
def GEN_IMPREWR_CONV (B : BoolThms) (avs : List term) (th : thm) (t : term) :
    IO (Except String thm) := ExceptT.run do
  -- sel = lhs o snd o strip_forall o snd o dest_imp
  -- Read RIGHT-TO-LEFT: dest_imp runs FIRST, then snd, strip_forall, snd, lhs.
  -- LEFT-associative operators, so no parentheses are needed and the chain lines
  -- up stage-for-stage with the OCaml; `oM` marks the one effect join.
  let sel : term → Except String term :=
    lhs o Prod.snd o strip_forall o Prod.snd oM Basics.dest_imp
  let th' ← ExceptT.mk (GEN_PART_MATCH_ALL B sel th t)
  let iv ← liftExcept (indep_vars B th')
  liftExcept (VARIANT_RULE avs (← B.GENL iv th'))

/-- A conversion which returns not only a theorem but also a list of terms which
    is a sublist of the theorem hypotheses, and a list of terms which are the
    variables newly introduced by the conversion.  See `[IMPREWR_CONV]` for an
    example. -/
abbrev annot_conv := term → IO (Except String (thm × Option term × List term))

/-- Takes a list of variables to avoid `[av]`, a theorem `[th]` of the form
    `[h1,..,hk |- !x1...xn. p ==> !y1...ym. l = r]`, and a term `[t]` and returns
    a conversion with hypotheses defined as follows: for a term `[t]`, if `[t]`
    matches `[l]` with substitution `[s]`, then return the theorem
    `[h1,...,hk,s(p) |- t = s(r)]` and the the list containing only `[s(p)]`.

    The purpose of the conversion with hypothesis is to be able to distinguish
    which hypothesis comes from the input theorem and which is added by the
    conversion itself. -/
def IMPREWR_CONV (B : BoolThms) (avs : Tset.t) (th : thm) : annot_conv := fun t => ExceptT.run do
  let gi ← ExceptT.mk (GEN_IMPREWR_CONV B avs th t)
  let (vs, uh) := SPEC_VARS B gi
  let u ← liftExcept ((do Basics.dest_imp (concl uh)).map Prod.fst)
  let ud ← liftExcept (B.UNDISCH uh)
  pure (ud, some u, Tset.of_list vs)

/-- `REWR_ANNOTCONV avs th t`: plain rewrite; returns `(th', None, new-vars)`. -/
def REWR_ANNOTCONV (B : BoolThms) (V : ImpConvVars) (_avs : Tset.t) (th : thm) : annot_conv :=
  fun t => do
    match ← PART_MATCH B lhs th t with
    | .error e => return .error e
    | .ok th' =>
      match (do let (_, t') ← dest_binary_blind (concl th')
                let new_vars := Tset.frees V.T_ t'
                let old_vars := Tset.union (Tset.frees V.T_ t) (Tset.freesl V.T_ (hyp th'))
                pure (Tset.subtract new_vars old_vars) : Except String (List term)) with
      | .error e => return .error e
      | .ok nv => return .ok (th', none, nv)

/-- `ORDER_ANNOTCONV cnv t`: only succeed if the rewrite is `term_order`-oriented. -/
def ORDER_ANNOTCONV (cnv : annot_conv) : annot_conv := fun t => do
  match ← cnv t with
  | .error e => return .error e
  | .ok (th, ho, vs) =>
    match dest_binary_blind (concl th) with
    | .error e => return .error e
    | .ok (l, r) => if term_order l r then return .ok (th, ho, vs)
                    else return (failwith "ORDER_ANNOTCONV")

/-- Takes a theorem, a net of conversions with hypotheses (which also take
    variables to avoid), and adds to the net the conversion corresponding to the
    theorem.

    Special cases:
    - usual term rewriting is handled with `[REWR_CONV]` instead of introducing
      a fake premise. Might be useful though to introduce a fake premise since
      the conversion would benefit from a better handling of variables occurring
      in the r.h.s. but not in the l.h.s.
    - a theorem of the form `[p ==> c]` where `[c]` is not equational is turned
      into `[p ==> c = T]`
    - a theorem of the form `[p ==> ~c]` is turned into `[p ==> c = F]` -/
def pat_cnv_of_thm (B : BoolThms) (V : ImpConvVars) (th0 : thm) :
    IO (Except String (term × (Tset.t → annot_conv))) := ExceptT.run do
  let th ← liftExcept (B.SPEC_ALL th0)
  let lconsts := freesl (hyp th)
  let c := concl th
  -- matches (eq): can (term_match lconsts l) r  (term_match is IO here)
  let matchesEq (l r : term) : IO Bool := do
    match ← term_match lconsts l r with | .ok _ => pure true | .error _ => pure false
  let matchesFo (l r : term) : IO Bool := do
    match ← fo_term_match lconsts l r with | .ok _ => pure true | .error _ => pure false
  match c with
  | .Comb (.Comb (.Const "=" _) l) r =>
      -- equational
      -- `free_in l r || matches l r && matches r l`, short-circuiting.
      if ← liftIO (do
          if free_in l r then return true
          if ← matchesEq l r then matchesEq r l else return false) then
        let eqti ← liftExcept (MAP_FORALL_BODY B (fun x => B.EQT_INTRO x) th)
        pure (c, fun avs => REWR_ANNOTCONV B V avs eqti)
      else pure (l, fun avs => REWR_ANNOTCONV B V avs th)
  | .Comb (.Comb (.Const "==>" _) p) cc =>
      -- implicational: imprewr_concl f = C IMPREWR_CONV (GEN_MAP_CONCLUSION f th)
      let imprewr_concl (f : thm → Except String thm) : IO (Tset.t → annot_conv) := do
        match GEN_MAP_CONCLUSION B f th with
        | .ok g => pure (fun avs => IMPREWR_CONV B avs g)
        | .error _ => pure (fun avs => IMPREWR_CONV B avs th)  -- unreachable on well-formed th
      match cc with
      | .Comb (.Comb (.Const "=" _) l) r =>
          -- OCaml rebinds `matches` to fo_term_match in the `==>` branch (impconv.ml L1232).
          -- `free_in l r || matches l r && matches r l || is_var l`, short-circuiting.
          if ← liftIO (do
              if free_in l r then return true
              if ← (do if ← matchesFo l r then matchesFo r l else return false) then return true
              return is_var l) then
            if (← liftIO (matchesFo cc p)) then
              let eqti ← liftExcept (B.EQT_INTRO th)
              pure (c, fun avs => REWR_ANNOTCONV B V avs eqti)
            else pure (cc, ← liftIO (imprewr_concl (fun x => B.EQT_INTRO x)))
          else pure (l, fun avs => IMPREWR_CONV B avs th)
      | .Comb (.Const "~" _) l => pure (l, ← liftIO (imprewr_concl (fun x => B.EQF_INTRO x)))
      | l => pure (l, ← liftIO (imprewr_concl (fun x => B.EQT_INTRO x)))
  | .Comb (.Const "~" _) l =>
      let eqfi ← liftExcept (B.EQF_INTRO th)
      pure (l, fun avs => REWR_ANNOTCONV B V avs eqfi)
  | .Const "T" _ => throw "pat_cnv_of_thm"
  | l =>
      let eqti ← liftExcept (B.EQT_INTRO th)
      pure (l, fun avs => REWR_ANNOTCONV B V avs eqti)
where liftIO {α} (x : IO α) : ExceptT String IO α := ExceptT.mk (do return .ok (← x))

/-- `patterns_of_thm = fst o pat_cnv_of_thm` (impconv.ml 1255).  `pat_cnv_of_thm`
    is `IO (Except ...)`-valued here, so the total `fst` is mapped over its
    result with `oIOm`; `pat_cnv_of_thm` still runs FIRST. -/
def patterns_of_thm (B : BoolThms) (V : ImpConvVars) : thm → IO (Except String term) :=
  Prod.fst oIOm pat_cnv_of_thm B V

/-- `impconv_net_of_thm th net`: add `th`'s conversion to the net (or identity on
    failure). -/
def impconv_net_of_thm (B : BoolThms) (V : ImpConvVars) (th : thm)
    (net : Fo_nets.t ((Tset.t → annot_conv) × Tset.t × thm)) :
    IO (Fo_nets.t ((Tset.t → annot_conv) × Tset.t × thm)) := do
  match ← pat_cnv_of_thm B V th with
  | .error _ => return net
  | .ok (p, c) =>
    let vs := Tset.freesl V.T_ (hyp th)
    Fo_nets.enter vs (p, (c, vs, th)) net

/-- Apply a conversion net to the term at the top level, taking avoided
    variables as parameter too. -/
partial def REWRITES_IMPCONV (net : Fo_nets.t ((Tset.t → annot_conv) × Tset.t × thm))
    (avs : Tset.t) (t : term) : IO (Except String (thm × Option term × List term)) := do
  let cands := Fo_nets.lookup t net
  let rec go : List ((Tset.t → annot_conv) × Tset.t × thm) →
      IO (Except String (thm × Option term × List term))
    | [] => return (failwith "REWRITES_IMPCONV")
    | (c, _, _) :: rest => do
        match ← c avs t with | .ok r => return .ok r | .error _ => go rest
  go cands

/-- `extra_basic_rewrites = itlist (mk_rewrites false) [NOT_FORALL_THM; NOT_IMP] []`. -/
def extra_basic_rewrites (B : BoolThms) (D : ImpConvDeps) : IO (Except String (List thm)) :=
  ExceptT.run do
    let r1 ← ExceptT.mk (mk_rewrites B false D.NOT_IMP [])
    ExceptT.mk (mk_rewrites B false D.NOT_FORALL_THM r1)

/-- The `avs`-parameterised annotated conversion type used inside
    `IMPREWR_CTXCONV`'s depth traversal. -/
abbrev acnv := Tset.t → term → IO (Except String (thm × Option term × List term))

/- The depth-traversal operators of `IMPREWR_CTXCONV` (`impconv.ml` 1267–1305),
   faithful to the nested `++`/`+`/`COMB_QCONV`/`SUB_QCONV`/`!`/`top_depth`. -/
mutual

/-- `(c1 ++ c2) avs t`: sequence; if `c1` yields a hypothesis (`Some _`) stop,
    else try `c2` on the rewritten term and `TRANS`. -/
partial def acThen (c1 c2 : acnv) : acnv := fun avs t => do
  match ← c1 avs t with
  | .error e => return .error e
  | .ok (th1, some u, vs1) => return .ok (th1, some u, vs1)
  | .ok (th1, none, vs1) =>
    match rand (concl th1) with
    | .error _ => return .ok (th1, none, vs1)
    | .ok r1 =>
      match ← c2 (Tset.union vs1 avs) r1 with
      | .error _ => return .ok (th1, none, vs1)
      | .ok (th2, ho2, vs2) =>
        match TRANS th1 th2 with
        | .ok tr => return .ok (tr, ho2, Tset.union vs1 vs2)
        | .error _ => return .ok (th1, none, vs1)

/-- `(c1 + c2) avs t = try (c1 ++ c2) avs t with _ -> c2 avs t`. -/
partial def acOr (c1 c2 : acnv) : acnv := fun avs t => do
  match ← acThen c1 c2 avs t with
  | .ok r => return .ok r
  | .error _ => c2 avs t

/-- `COMB_QCONV c avs l r`. -/
partial def acCombQConv (c : acnv) (avs : Tset.t) (l r : term) :
    IO (Except String (thm × Option term × List term)) := do
  match ← c avs l with
  | .ok (th, some ho, vs) =>
    match AP_THM th r with | .ok a => return .ok (a, some ho, vs) | .error e => return .error e
  | .ok (th1, none, vs1) =>
    match ← c (Tset.union vs1 avs) r with
    | .ok (th2, ho2, vs2) =>
      match MK_COMB th1 th2 with
      | .ok m => return .ok (m, ho2, Tset.union vs1 vs2)
      | .error _ => match AP_THM th1 r with | .ok a => return .ok (a, none, vs1) | .error e => return .error e
    | .error _ => match AP_THM th1 r with | .ok a => return .ok (a, none, vs1) | .error e => return .error e
  | .error _ =>
    match ← c avs r with
    | .ok (th2, ho2, vs2) => match AP_TERM l th2 with
                             | .ok a => return .ok (a, ho2, vs2) | .error e => return .error e
    | .error e => return .error e

/-- `SUB_QCONV c avs t` (`T_` supplied for `Tset.insert`). -/
partial def acSubQConv (T_ : term) (c : acnv) (avs : Tset.t) (t : term) :
    IO (Except String (thm × Option term × List term)) := do
  match t with
  | .Comb l r => acCombQConv c avs l r
  | .Abs _ _ =>
    match dest_abs t with
    | .error e => return .error e
    | .ok (v, body) =>
      match ← c (Tset.insert T_ avs v) body with
      | .error e => return .error e
      | .ok (th, ho, vs) =>
        match ABS v th with
        | .ok a => return .ok (a, ho, vs)   -- fast path (OCaml ABS_CONV fast path)
        | .error _ =>
          -- alpha-renaming fallback (OCaml ABS_CONV, equal.ml): rename v to a genvar,
          -- re-run c on the renamed body; ho/vs come from that SECOND call (OCaml c' ref).
          let gv ← genvar (type_of v)
          let gbody := (vsubst [(gv, v)]).toOption.map (fun f => f body) |>.getD body
          match ← c (Tset.insert T_ avs v) gbody with
          | .error e => return .error e
          | .ok (gth0, ho', vs') =>
            match ← (ExceptT.run do
              let gth ← liftExcept (ABS gv gth0)
              let gtm := concl gth
              let (l, r) ← liftExcept (dest_eq gtm)
              let v' ← liftExcept (variant (frees gtm) v)
              let l' ← liftExcept (alpha v' l)
              let r' ← liftExcept (alpha v' r)
              let mkEq ← ExceptT.mk (mk_eq : IO (Except String ((term × term) → Except String term)))
              let eqlr ← liftExcept (mkEq (l', r'))
              let am ← liftExcept (ALPHA gtm eqlr)
              liftExcept (EQ_MP am gth) : IO (Except String thm)) with
            | .ok res => return .ok (res, ho', vs')
            | .error e => return .error e
  | _ => return (failwith "SUB_QCONV")

/-- `(!c) avs t = (c ++ !c) avs t` (repeat). -/
partial def acRepeat (c : acnv) : acnv := fun avs t => acThen c (acRepeat c) avs t

/-- `top_depth c avs t = (!c + (SUB_QCONV (top_depth c) ++ top_depth c)) avs t`. -/
partial def acTopDepth (T_ : term) (c : acnv) : acnv := fun avs t =>
  acOr (acRepeat c)
    (acThen (fun a u => acSubQConv T_ (acTopDepth T_ c) a u) (acTopDepth T_ c)) avs t

end

/-- A recorded context operation for `IMPREWR_CTXCONV` (its OCaml
    `augment`/`diminish` do net-rebuilding `IO`, which cannot live in the pure
    `WithContext` continuations; we record the operations and replay them inside
    `apply`, which is already `IO`, reproducing the OCaml `self net ths`). -/
inductive ImprewrOp where
  | augment : List term → ImprewrOp
  | diminish : term → ImprewrOp
  deriving Inhabited

/-- Replay `baseThs` + `ops` to the current `(net, ths)` of `IMPREWR_CTXCONV`. -/
partial def imprewrBuild (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars)
    (baseThs : List thm) (ops : List ImprewrOp) :
    IO (Except String (Fo_nets.t ((Tset.t → annot_conv) × Tset.t × thm) × List thm)) := do
  let mut net : Fo_nets.t ((Tset.t → annot_conv) × Tset.t × thm) := Fo_nets.empty_net
  -- OCaml `itlist impconv_net_of_thm ths net` enters the LAST element first; since
  -- net_update prepends tips, ths[0] ends up head-of-tips (tried first). Iterate reversed.
  for th in baseThs.reverse do net ← impconv_net_of_thm B V th net
  let mut ths := baseThs
  for op in ops do
    match op with
    | .augment ts =>
      let mut ths' := []
      for t in ts do match ASSUME t with
        -- OCaml `map ASSUME ts` propagates (impconv.ml 1316)
        | .ok th => ths' := ths' ++ [th] | .error e => return .error e
      let mpc1 ← MP_CLOSURE B D ths' ths'
      let mpc2 ← MP_CLOSURE B D ths ths'
      let ths'' := mpc1 ++ ths' ++ mpc2
      for th in ths''.reverse do net ← impconv_net_of_thm B V th net
      ths := ths'' ++ ths
    | .diminish v =>
      let survivors := ((Fo_nets.allTips net).filterMap (fun (_, vs, th) =>
        if Tset.mem v vs then none else some th)).reverse   -- OCaml `th :: !ths` reverses traversal order
      net := Fo_nets.filter (fun (_, vs, _) => !(Tset.mem v vs)) net
      ths := survivors
  pure (.ok (net, ths))

/-- The context-aware annotated rewrite conversion `IMPREWR_CTXCONV`, holding a
    net of the theorems' conversions and applying it top-down (`impconv.ml`
    1267–1332).  Lean note: the OCaml `augment`/`diminish` rebuild the net in
    `IO`, which cannot live in the pure `WithContext` continuations, so we record
    the ops and replay them (`imprewrBuild`) inside `apply`. -/
partial def imprewrCtx (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars)
    (baseThs : List thm) (ops : List ImprewrOp) : WithContext (atomic → annot_conv) :=
  .mk
    (fun a => fun t => do
      match ← imprewrBuild B D V baseThs ops with
      | .error e => return .error e
      | .ok (net, ths) =>
      -- basic_cnv t = (REWRITES_CONV (bigger_net()) t, None, [])
      let basic_cnv (u : term) : IO (Except String (thm × Option term × List term)) := do
        let mut bn ← basic_net
        match ← extra_basic_rewrites B D with
        | .error _ => pure ()
        | .ok extra => for th in extra.reverse do   -- OCaml itlist enters last-first
                         match ← net_of_thm B false th bn with
                         | .ok bn' => bn := bn'
                         | .error _ => pure ()
        match ← REWRITES_CONV bn u with
        | .ok th => return .ok (th, none, [])
        | .error e => return .error e
      let avs := Tset.flat_revmap (fun th => Tset.freesl V.T_ (hyp th)) ths
      let cnv : acnv := fun avs' u => do
        match ← REWRITES_IMPCONV net avs' u with
        | .ok r => return .ok r
        | .error _ => basic_cnv u
      let f : acnv := match a with
        | .Atomic => acTopDepth V.T_ cnv
        | .Non_atomic => cnv
      f (Tset.union (Tset.frees V.T_ t) avs) t)
    (fun ts => imprewrCtx B D V baseThs (ops ++ [.augment ts]))
    (fun v => imprewrCtx B D V baseThs (ops ++ [.diminish v]))

/-- `IMPREWR_CTXCONV ths = self (net-of ths) ths` with no pending ops. -/
def IMPREWR_CTXCONV (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars) (ths : List thm) :
    WithContext (atomic → annot_conv) :=
  imprewrCtx B D V ths []

/- ---------------------------------------------------------------------- -/
/- SOME USEFUL IMPLICATIONAL CONVERSIONS (`impconv.ml` 1345-1437).         -/
/- ---------------------------------------------------------------------- -/

/-- Takes a conversion with hypotheses (with context) and makes an implicational
    conversion out of it.  Basically turns a rewrite with hypotheses into an
    implicational rewrite withouth hypotheses.  Adds existential quantifications
    for variables introduced by the rewrite. -/
partial def REWR_IMPCONV_OF_CONV (B : BoolThms) (D : ImpConvDeps)
    (c : WithContext (atomic → annot_conv)) : WithContext (atomic → imp_conv) :=
  .mk
    (fun a => fun v t => do
      let IMP_SYM (th : thm) : IO (Except String thm) := REWR_RULE B D.imp_sym th
      let TRY_GEN (v : term) (th : thm) : thm := (B.GEN v th).toOption.getD th
      match ← c.apply a t with
      | .error e => return .error e
      | .ok (th, ho, new_vars) =>
        match B.EQ_IMP_RULE th with
        | .error e => return .error e
        | .ok (th1, th2) =>
          match ← (ExceptT.run do
            let res ← (match v with
              | .Co => do
                  let (p, th2') ← liftExcept (UNDISCH_TERM B th2)
                  -- exists_intro: [] -> DISCH_IMP_IMP (p :: list_of_option ho) th2'
                  --   v::vs -> try REWR_RULE IMP_EXIST (GEN v (exists_intro vs)) with _ -> that
                  let IMP_EXIST ← liftExcept (GSYM D.LEFT_IMP_EXISTS_THM)
                  let rec exists_intro (vs : List term) : IO (Except String thm) := do
                    match vs with
                    | [] => DISCH_IMP_IMP B D (p :: list_of_option ho) th2'
                    | vv :: rest =>
                      match ← exists_intro rest with
                      | .error e => return .error e
                      | .ok th =>
                        match B.GEN vv th with
                        | .error _ => return .ok th
                        | .ok gth => match ← REWR_RULE B IMP_EXIST gth with
                                     | .ok r => return .ok r | .error _ => return .ok th
                  ExceptT.mk (exists_intro new_vars)
              | .Contra => do
                  let th1' ← (match ho with
                    | none => liftExcept (Except.ok th1 : Except String thm)
                    | some h => ExceptT.mk (do IMP_SYM (← (match B.DISCH h th1 with
                                                            | .ok d => pure d
                                                            | .error e => throw (IO.userError e)))))
                  match new_vars with
                  | [] => liftExcept (Except.ok th1' : Except String thm)
                  | _ :: _ =>
                    liftExcept (MAP_CONCLUSION B (fun th => itlistM (fun vv t2 => .ok (TRY_GEN vv t2)) new_vars th) th1'))
            let (t1, t2) ← liftExcept (Basics.dest_imp (concl res))
            if t1 == t2 then throw unchanged else pure res) with
          | .ok r => return .ok r
          | .error e => return .error e)
    (fun x => REWR_IMPCONV_OF_CONV B D (c.augment x))
    (fun x => REWR_IMPCONV_OF_CONV B D (c.diminish x))

/-- Applies the implicational rewrite, with context simplifications. -/
def REWRITE_CTXIMPCONV (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars) (ths : List thm) :
    WithContext imp_conv :=
  DEPTH_CTXIMPCONV B D V (REWR_IMPCONV_OF_CONV B D (IMPREWR_CTXCONV B D V ths))

/- ---------------------------------------------------------------------- -/
/- INTERFACE                                                              -/
/- ---------------------------------------------------------------------- -/

/-- Preprocessor. For now takes a theorem of the form `[p ==> c1 /\ ... /\ ck]`
    and returns the list of theorems `[p ==> c1]`, ..., `[p ==> ck]`. -/
def preprocess (B : BoolThms) (D : ImpConvDeps) (th : thm) : IO (Except String (List thm)) := do
  match ← IMPLY_AND B D th with
  | .ok ia => return .ok (B.CONJUNCTS ia)
  | .error e => return .error e

/-- Tactic for implicational rewrite. -/
def IMP_REWRITE_TAC (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars) (ths : List thm) :
    tactic := fun g => do
  let mut pps : List thm := []
  for th in ths do
    match ← preprocess B D th with
    -- OCaml `flat (map preprocess ths)` propagates (impconv.ml 1444)
    | .ok l => pps := pps ++ l | .error e => return .error e
  match ← CTXIMPCONV_TAC B V (REWRITE_CTXIMPCONV B D V pps) g with
  | .ok r => return .ok r
  | .error e => if e == unchanged then return (failwith "Unchanged") else return .error e

/-- `SEQ_IMP_REWRITE_TAC ths`. -/
def SEQ_IMP_REWRITE_TAC (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars) (ths : List thm) :
    tactic := fun g => do
  let cnvE : IO (Except String (WithContext imp_conv)) := (match ths with
    | [] => return .ok (REWRITE_CTXIMPCONV B D V [B.TRUTH])
    | [th] => do match ← preprocess B D th with
                 -- OCaml `REWRITE_CTXIMPCONV (preprocess th)` propagates (impconv.ml 1396)
                 | .ok l => return .ok (REWRITE_CTXIMPCONV B D V l)
                 | .error e => return .error e
    | _ :: _ => do
        let mut cnvs : List (WithContext imp_conv) := []
        for th in ths do
          match ← preprocess B D th with
          -- OCaml `map (REWRITE_CTXIMPCONV o preprocess) ths` propagates (impconv.ml 1396)
          | .ok l => cnvs := cnvs ++ [REWRITE_CTXIMPCONV B D V l]
          | .error e => return .error e
        return .ok (REPEAT_UNCHANGED_CTXIMPCONV B D V cnvs))
  match ← cnvE with
  | .error e => return .error e
  | .ok cnv =>
  match ← CTXIMPCONV_TAC B V cnv g with
  | .ok r => return .ok r
  | .error e => if e == unchanged then return (failwith "Unchanged") else return .error e

/-- Tactic for implicational rewrite with assumptions. -/
def ASM_IMP_REWRITE_TAC (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars) : List thm → tactic :=
  Tactics.ASM (IMP_REWRITE_TAC B D V)

/-- Cases-like conversion for implicational theorems, i.e., for a theorem of the
    form `[h1,..,hk |- !x1...xn. p ==> !y1...ym. l = r]`, and a term `[t]`,
    return `[(p ==> t') /\ (~p ==> t)]`, where `[t']` is the result of rewriting
    `[t]` by `[l=r]`. -/
partial def CASE_REWR_IMPCONV_OF_CONV (B : BoolThms) (D : ImpConvDeps)
    (c : WithContext (atomic → annot_conv)) : WithContext (atomic → imp_conv) :=
  .mk
    (fun a => fun v t => do
      match ← c.apply a t with
      | .error e => return .error e
      | .ok (_, none, _) => return (failwith "CASE_REWR_IMPCONV_OF_CONV")
      | .ok (th, some h, _) =>
        match B.DISCH h th with
        | .error e => return .error e
        | .ok th' =>
          -- th'' = try MP_LEM1 th' with _ -> MP_LEM2 th' ; MP_LEM_i = MATCH_MP case_lem_i
          match ← (do match ← MATCH_MP B D.case_lem1 th' with
                      | .ok r => pure (.ok r : Except String thm)
                      | .error _ => MATCH_MP B D.case_lem2 th') with
          | .error e => return .error e
          | .ok th'' =>
            -- imp_conv_of_conv (REWR_CONV th'') v t, but REWR_CONV is an ioconv here
            match ← REWR_CONV B th'' t with
            | .error e => return .error e
            | .ok eqth => match B.EQ_IMP_RULE eqth with
                          | .error e => return .error e
                          | .ok (ith1, ith2) => match v with
                                                | .Co => return .ok ith2
                                                | .Contra => return .ok ith1)
    (fun x => CASE_REWR_IMPCONV_OF_CONV B D (c.augment x))
    (fun x => CASE_REWR_IMPCONV_OF_CONV B D (c.diminish x))

/-- `CASE_REWRITE_CTXIMPCONV = ONCE_DEPTH_CTXIMPCONV o CASE_REWR_IMPCONV_OF_CONV
    o IMPREWR_CTXCONV` (impconv.ml 1432).  Right-to-left: `IMPREWR_CTXCONV`
    runs FIRST, then `CASE_REWR_IMPCONV_OF_CONV`, then `ONCE_DEPTH_CTXIMPCONV`. -/
def CASE_REWRITE_CTXIMPCONV (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars) :
    List thm → WithContext imp_conv :=
  ONCE_DEPTH_CTXIMPCONV B D V o CASE_REWR_IMPCONV_OF_CONV B D o IMPREWR_CTXCONV B D V

/-- Tactic version of it. -/
def CASE_REWRITE_TAC (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars) (th : thm) :
    tactic := fun g => do
  match ← preprocess B D th with
  | .error e => return .error e
  | .ok pps =>
    match ← CTXIMPCONV_TAC B V (CASE_REWRITE_CTXIMPCONV B D V pps) g with
    | .ok r => return .ok r
    | .error e => if e == unchanged then return (failwith "Unchanged") else return .error e

/- ---------------------------------------------------------------------- -/
/- Implicational conversions with multiple results (`impconv.ml`          -/
/- 1444-1745).                                                            -/
/- ---------------------------------------------------------------------- -/

/-- Multiple implicational conversion. -/
abbrev imp_mconv := Variance.t → term → IO (Except String (List thm))

/-- Multiple implicational conversion with hypotheses. -/
abbrev annot_mconv := term → IO (Except String (List (thm × Option term × List term)))

/-- `mapply_with_context c ctx v t = map (DISCH_CONJ ctx) (apply (augment c
    (Tset.strip_conj ctx)) v t)`. -/
def mapply_with_context (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars)
    (c : WithContext imp_mconv) (ctx : term) (v : Variance.t) (t : term) :
    IO (Except String (List thm)) := do
  match ← (c.augment (Tset.strip_conj V.T_ ctx)).apply v t with
  | .error e => return .error e
  | .ok ths =>
    let mut out := []
    for th in ths do
      match ← DISCH_CONJ B D ctx th with | .ok r => out := out ++ [r] | .error e => return .error e
    return .ok out

/-- Run an `Except`-returning per-element builder over a list, keeping successes
    (`map f` in OCaml, where `f` never fails on well-formed input). -/
private def mapEx (f : thm → Except String thm) (l : List thm) : Except String (List thm) :=
  l.mapM f

/-- Run an `IO (Except _)`-returning per-element builder over a list. -/
private def mapIOEx (f : thm → IO (Except String thm)) (l : List thm) :
    IO (Except String (List thm)) := do
  let mut out := []
  for th in l do match ← f th with | .ok r => out := out ++ [r] | .error e => return .error e
  return .ok out

/- The mutually-recursive multi-valued structural builders. -/
mutual

/- Consider two multiple implicational conversions ic1, ic2.
   Suppose `[ic1 Co A]` returns a list `[B1 ==> A; ...; Bk ==> A]`, and
   `[ic2 Co C]` returns `[D1 ==> C; ...; Dn ==> C]`, then
   `[CONJ_IMPMCONV ic1 ic2 Co (A /\ C)]` returns
   `[B1 /\ C ==> A /\ C; ...; Bk /\ C ==> A /\ C; A /\ D1 ==> A /\ C; ...;
   Dn ==> A /\ C]`.  And similarly for the contravariant case. -/
partial def CONJ_CTXIMPMCONV (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars)
    (c : WithContext imp_mconv) : WithContext imp_mconv :=
  .mk
    (fun v t => do
      match Basics.dest_conj t with
      | .error e => return .error e
      | .ok (t1, t2) =>
        let left  : thm → Except String thm := match v with
          | .Co => MKIMPL_CONJ_CO2_CTXT B V D | .Contra => MKIMPL_CONJ_CONTRA_CTXT B V D
        let right : thm → Except String thm := match v with
          | .Co => MKIMPR_CONJ_CO_CTXT B V D | .Contra => MKIMPR_CONJ_CONTRA_CTXT B V D
        match ← mapply_with_context B D V c t2 v t1 with
        | .error e => return .error e
        | .ok l1 => match mapEx left l1 with
          | .error e => return .error e
          | .ok th1s => match ← mapply_with_context B D V c t1 v t2 with
            | .error e => return .error e
            | .ok l2 => match mapEx right l2 with
              | .error e => return .error e
              | .ok th2s => return .ok (th1s ++ th2s))
    (fun x => CONJ_CTXIMPMCONV B D V (c.augment x))
    (fun x => CONJ_CTXIMPMCONV B D V (c.diminish x))

/- Consider two multiple implicational conversions ic1, ic2.
   Suppose `[ic1 Co A]` returns a list `[B1 ==> A; ...; Bk ==> A]`, and
   `[ic2 Co C]` returns `[D1 ==> C; ...; Dn ==> C]`, then
   `[DISJ_IMPMCONV ic1 ic2 Co (A \/ C)]` returns
   `[B1 \/ C ==> A \/ C; ...; Bk \/ C ==> A \/ C; A \/ D1 ==> A \/ C; ...;
   Dn ==> A \/ C]`.  And similarly for the contravariant case. -/
partial def DISJ_CTXIMPMCONV (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars)
    (c : WithContext imp_mconv) : WithContext imp_mconv :=
  .mk
    (fun v t => do
      match Basics.dest_disj t with
      | .error e => return .error e
      | .ok (t1, t2) =>
        match ← c.apply v t1 with
        | .error e => return .error e
        | .ok l1 => match ← mapIOEx (fun th => MKIMPL_DISJ B V D th t2) l1 with
          | .error e => return .error e
          | .ok th1s => match ← c.apply v t2 with
            | .error e => return .error e
            | .ok l2 => match ← mapIOEx (fun th => MKIMPR_DISJ B V D t1 th) l2 with
              | .error e => return .error e
              | .ok th2s => return .ok (th1s ++ th2s))
    (fun x => DISJ_CTXIMPMCONV B D V (c.augment x))
    (fun x => DISJ_CTXIMPMCONV B D V (c.diminish x))

/- Consider two multiple implicational conversions ic1, ic2.
   Suppose `[ic1 Contra A]` returns a list `[A ==> B1; ...; A ==> Bk]`, and
   `[ic2 Co C]` returns `[D1 ==> C; ...; Dn ==> C]`, then
   `[DISJ_IMPMCONV ic1 ic2 Co (A \/ C)]` returns
   `[(B1 ==> C) ==> (A ==> C); ...; (Bk ==> C) ==> (A ==> C);
   (A ==> D1) ==> (A ==> C); ...; (A ==> Dn) ==> (A ==> C)]`.  And similarly
   for the contravariant case. -/
partial def IMP_CTXIMPMCONV (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars)
    (c : WithContext imp_mconv) : WithContext imp_mconv :=
  .mk
    (fun v t => do
      match Basics.dest_imp t with
      | .error e => return .error e
      | .ok (t1, t2) =>
        match ← c.apply (Variance.neg v) t1 with
        | .error e => return .error e
        | .ok l1 => match ← mapIOEx (fun th => MKIMPL_IMP B V D th t2) l1 with
          | .error e => return .error e
          | .ok th1s => match ← mapply_with_context B D V c t1 v t2 with
            | .error e => return .error e
            | .ok l2 => match mapEx (MKIMPR_IMP_CTXT B V D) l2 with
              | .error e => return .error e
              | .ok th2s => return .ok (th1s ++ th2s))
    (fun x => CONJ_CTXIMPMCONV B D V (c.augment x))   -- faithful to OCaml (uses CONJ here)
    (fun x => CONJ_CTXIMPMCONV B D V (c.diminish x))

partial def IFF_CTXIMPMCONV (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars)
    (c : WithContext imp_mconv) : WithContext imp_mconv :=
  .mk
    (fun v t => do
      match dest_iff t with
      | .error e => return .error e
      | .ok (t1, t2) =>
        let left  : thm → Except String thm := match v with
          | .Co => MKIMPL_CO_IFF B V D | .Contra => MKIMPL_CONTRA_IFF B V D
        let right : thm → Except String thm := match v with
          | .Co => MKIMPR_CO_IFF B V D | .Contra => MKIMPR_CONTRA_IFF B V D
        match mk_imp t1 t2 with
        | .error e => return .error e
        | .ok i12 => match ← c.apply v i12 with
          | .error e => return .error e
          | .ok l1 => match mapEx left l1 with
            | .error e => return .error e
            | .ok th1s => match mk_imp t2 t1 with
              | .error e => return .error e
              | .ok i21 => match ← c.apply v i21 with
                | .error e => return .error e
                | .ok l2 => match mapEx right l2 with
                  | .error e => return .error e
                  | .ok th2s => return .ok (th1s ++ th2s))
    (fun x => IFF_CTXIMPMCONV B D V (c.augment x))
    (fun x => IFF_CTXIMPMCONV B D V (c.diminish x))

/- Consider one multiple implicational conversion ic.
   Suppose `[ic Contra A]` returns a list `[A ==> B1; ...; A ==> Bk]`, then
   `[NOT_IMPMCONV ic Co ~A]` returns `[~B1 ==> ~A; ...; ~Bk ==> ~A]`.  And
   similarly for the contravariant case. -/
partial def NOT_CTXIMPMCONV (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars)
    (c : WithContext imp_mconv) : WithContext imp_mconv :=
  .mk
    (fun v t => do
      match dest_neg t with
      | .error e => return .error e
      | .ok nt =>
        -- map MKIMP_NOT (try_list (apply c (neg v)) nt)
        match ← c.apply (Variance.neg v) nt with
        | .error _ => return .ok []          -- try_list: failure → []
        | .ok l => return (mapEx (MKIMP_NOT B V D) l))
    (fun x => NOT_CTXIMPMCONV B D V (c.augment x))
    (fun x => NOT_CTXIMPMCONV B D V (c.diminish x))

partial def QUANT_CTXIMPMCONV (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars)
    (mkimp : term → thm → IO (Except String thm)) (sel : term → Except String (term × term))
    (c : WithContext imp_mconv) : WithContext imp_mconv :=
  .mk
    (fun v t => do
      match sel t with
      | .error e => return .error e
      | .ok (x, b) =>
        let c' := c.diminish x
        match ← c'.apply v b with
        | .error _ => return .ok []          -- try_list: failure → []
        | .ok l => mapIOEx (fun th => mkimp x th) l)
    (fun y => QUANT_CTXIMPMCONV B D V mkimp sel (c.augment y))
    (fun y => QUANT_CTXIMPMCONV B D V mkimp sel (c.diminish y))

/- Consider one multiple implicational conversion ic.
   Suppose `[ic Co A]` returns a list `[B1 ==> A; ...; Bk ==> A]`, then
   `[FORALL_IMPMCONV ic Co (!x.A)]` returns
   `[(!x.B1) ==> (!x.A); ...; (!x.Bk) ==> (!x.A)]`.  And similarly for the
   contravariant case. -/
partial def FORALL_CTXIMPMCONV (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars) :
    WithContext imp_mconv → WithContext imp_mconv :=
  QUANT_CTXIMPMCONV B D V (MKIMP_FORALL B D) Basics.dest_forall

/- Consider one multiple implicational conversion ic.
   Suppose `[ic Co A]` returns a list `[B1 ==> A; ...; Bk ==> A]`, then
   `[EXISTS_IMPMCONV ic Co (?x.A)]` returns
   `[(?x.B1) ==> (?x.A); ...; (?x.Bk) ==> (?x.A)]`.  And similarly for the
   contravariant case. -/
partial def EXISTS_CTXIMPMCONV (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars) :
    WithContext imp_mconv → WithContext imp_mconv :=
  QUANT_CTXIMPMCONV B D V (MKIMP_EXISTS B D) Basics.dest_exists

/- Applies a multiple implicational conversion on the subformula(s) of the
   input term. -/
partial def SUB_CTXIMPMCONV (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars)
    (c : WithContext imp_mconv) : WithContext imp_mconv :=
  .mk
    (fun v t => do
      let iff_ty : hol_type := .Tyapp "fun" [bool_ty, .Tyapp "fun" [bool_ty, bool_ty]]
      match dest_const (Prod.fst (strip_comb t)) with
      | .error _ => return (failwith "dest_const")   -- non-constant head: generic Failure (→ Non_atomic in DEPTH)
      | .ok (n, ty) =>
        let builder : Option (WithContext imp_mconv) :=
          if n == "==>" then some (IMP_CTXIMPMCONV B D V c)
          else if n == "/\\" then some (CONJ_CTXIMPMCONV B D V c)
          else if n == "\\/" then some (DISJ_CTXIMPMCONV B D V c)
          else if n == "!" then some (FORALL_CTXIMPMCONV B D V c)
          else if n == "?" then some (EXISTS_CTXIMPMCONV B D V c)
          else if n == "~" then some (NOT_CTXIMPMCONV B D V c)
          else if n == "=" && ty == iff_ty then some (IFF_CTXIMPMCONV B D V c)
          else none
        match builder with
        | some wc => wc.apply v t
        | none => return (failwith "SUB_CTXIMPMCONV"))
    (fun x => SUB_CTXIMPMCONV B D V (c.augment x))
    (fun x => SUB_CTXIMPMCONV B D V (c.diminish x))

end

/-- Applies a multiple implicational conversion once to the first suitable
    sub-term(s) encountered in bottom-up order. -/
partial def DEPTH_CTXIMPMCONV (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars)
    (c : WithContext (atomic → imp_mconv)) : WithContext imp_mconv :=
  .mk
    (fun v t => do
      -- self-as-imp_mconv wrapper for SUB
      let selfImp : WithContext imp_mconv := DEPTH_CTXIMPMCONV B D V c
      -- OCaml wraps BOTH the SUB apply and the `apply c Non_atomic @ ths` under
      -- `try ... with Failure "SUB_CTXIMPMCONV" -> apply c Atomic`.
      match ← (SUB_CTXIMPMCONV B D V selfImp).apply v t with
      | .ok ths => match ← c.apply .Non_atomic v t with
                   | .ok na => return .ok (na ++ ths)
                   | .error e => if e == "SUB_CTXIMPMCONV" then c.apply .Atomic v t else return .error e
      | .error e => if e == "SUB_CTXIMPMCONV" then c.apply .Atomic v t else return .error e)
    (fun x => DEPTH_CTXIMPMCONV B D V (c.augment x))
    (fun x => DEPTH_CTXIMPMCONV B D V (c.diminish x))
/- ---------------------------------------------------------------------- -/
/- REWRITE IMPLICATIONAL CONVERSIONS                                      -/
/- ---------------------------------------------------------------------- -/

/-- Takes a theorem, a net of conversions with hypotheses (which also take
    variables to avoid), and adds to the net the conversion corresponding to the
    theorem.

    Special cases:
    - usual term rewriting is handled with `[REWR_CONV]` instead of introducing
      a fake premise. Might be useful though to introduce a fake premise since
      the conversion would benefit from a better handling of variables occurring
      in the r.h.s. but not in the l.h.s.
    - a theorem of the form `[p ==> c]` where `[c]` is not equational is turned
      into `[p ==> c = T]`
    - a theorem of the form `[p ==> ~c]` is turned into `[p ==> c = F]` -/
def target_pat_cnv_of_thm (B : BoolThms) (V : ImpConvVars) (th0 : thm) :
    IO (Except String (term × (Tset.t → annot_conv))) := ExceptT.run do
  let th ← liftExcept (B.SPEC_ALL th0)
  match concl th with
  | .Comb (.Comb (.Const "=" _) l) _ => pure (l, fun avs => REWR_ANNOTCONV B V avs th)
  | .Comb (.Comb (.Const "==>" _) _) cc =>
      match cc with
      | .Comb (.Comb (.Const "=" _) l) _ => pure (l, fun avs => IMPREWR_CONV B avs th)
      | .Comb (.Const "~" _) l =>
          let g ← liftExcept (GEN_MAP_CONCLUSION B (fun x => B.EQF_INTRO x) th)
          pure (l, fun avs => IMPREWR_CONV B avs g)
      | _ =>
          let g ← liftExcept (GEN_MAP_CONCLUSION B (fun x => B.EQT_INTRO x) th)
          pure (cc, fun avs => IMPREWR_CONV B avs g)
  | .Comb (.Const "~" _) l =>
      let eqfi ← liftExcept (B.EQF_INTRO th)
      pure (l, fun avs => REWR_ANNOTCONV B V avs eqfi)
  | .Const "T" _ => throw "target_pat_cnv_of_thm"
  | l =>
      let eqti ← liftExcept (B.EQT_INTRO th)
      pure (l, fun avs => REWR_ANNOTCONV B V avs eqti)

/-- `target_impconv_net_of_thm th net`. -/
def target_impconv_net_of_thm (B : BoolThms) (V : ImpConvVars) (th : thm)
    (net : Fo_nets.t ((Tset.t → annot_conv) × Tset.t × thm)) :
    IO (Fo_nets.t ((Tset.t → annot_conv) × Tset.t × thm)) := do
  match ← target_pat_cnv_of_thm B V th with
  | .error _ => return net
  | .ok (p, c) => let vs := Tset.freesl V.T_ (hyp th); Fo_nets.enter vs (p, (c, vs, th)) net

/-- `target_patterns_of_thm = fst o target_pat_cnv_of_thm` (impconv.ml 1651).
    As `patterns_of_thm`: the inner function is `IO (Except ...)`-valued, so the
    total `fst` is mapped over its result with `oIOm`. -/
def target_patterns_of_thm (B : BoolThms) (V : ImpConvVars) :
    thm → IO (Except String term) :=
  Prod.fst oIOm target_pat_cnv_of_thm B V

/-- `map_fst f (x,y,z) = (f x, y, z)`. -/
private def map_fst (f : thm → Except String thm) (r : thm × Option term × List term) :
    Except String (thm × Option term × List term) := do pure ((← f r.1), r.2.1, r.2.2)

/-- The annotated multi-conversion type used inside `DEEP_IMP_REWR_MCONV`. -/
abbrev amconv := term → IO (Except String (List (thm × Option term × List term)))

/- `COMB_MCONV`/`ABS_MCONV`/`SUB_MCONV`/`top_depth` of `DEEP_IMP_REWR_MCONV`
   (`impconv.ml` 1660–1685). -/
mutual

partial def dmComb (c : amconv) (l r : term) :
    IO (Except String (List (thm × Option term × List term))) := do
  -- `map (...) (c l) @ map (...) (c r)`: OCaml evaluates `@`'s operands right
  -- to left, so `c r` (and its map) runs first.
  match ← c r with
  | .error e => return .error e
  | .ok rr =>
    match rr.mapM (fun x => map_fst (fun th => AP_TERM l th) x) with
    | .error e => return .error e
    | .ok b =>
      match ← c l with
      | .error e => return .error e
      | .ok ll => match ll.mapM (fun x => map_fst (fun th => AP_THM th r) x) with
                  | .ok a => return .ok (a ++ b) | .error e => return .error e

partial def dmAbs (c : amconv) (v b : term) :
    IO (Except String (List (thm × Option term × List term))) := do
  match ← c b with
  | .error e => return .error e
  | .ok ths =>
    match ths.mapM (fun x => map_fst (fun th => ABS v th) x) with
    | .ok r => return .ok r
    | .error _ =>
      -- alpha-renaming fallback with a genvar
      let gv ← genvar (type_of v)
      let b' := (vsubst [(gv, v)]).toOption.map (fun f => f b) |>.getD b
      match ← c b' with
      | .error e => return .error e
      | .ok gths =>
        match gths.mapM (fun x => map_fst (fun th => ABS gv th) x) with
        | .error e => return .error e
        | .ok abst =>
          match ← (mk_eq : IO (Except String ((term × term) → Except String term))) with
          | .error e => return .error e
          | .ok mkEq =>
          match (abst.mapM (fun (gth, ho, vs) => do
              let gtm := concl gth
              let (l, r) ← dest_eq gtm
              let v' ← variant (frees gtm) v
              let l' ← alpha v' l
              let r' ← alpha v' r
              let eqlr ← mkEq (l', r')
              let am ← ALPHA gtm eqlr
              pure ((← EQ_MP am gth), ho, vs)) :
              Except String (List (thm × Option term × List term))) with
          | .ok r => return .ok r | .error e => return .error e

partial def dmSub (c : amconv) (t : term) :
    IO (Except String (List (thm × Option term × List term))) := do
  match t with
  | .Comb l r => dmComb c l r
  | .Abs v b => dmAbs c v b
  | _ => return .ok []

partial def dmTopDepth (c : amconv) : amconv := fun t => do
  -- `SUB_MCONV (top_depth c) t @ c t`: `c t` runs first (right to left).
  match ← c t with
  | .error e => return .error e
  | .ok ct => match ← dmSub (dmTopDepth c) t with
              | .ok subs => return .ok (subs ++ ct) | .error e => return .error e

end

/-- `REWRITES_IMPCONV` (multi): `mapfilter (fun (c,_,_) -> c avs t) (lookup t net)`. -/
def mREWRITES_IMPCONV (net : Fo_nets.t ((Tset.t → annot_conv) × Tset.t × thm))
    (avs : Tset.t) (t : term) : IO (List (thm × Option term × List term)) := do
  let mut out := []
  for (c, _, _) in Fo_nets.lookup t net do
    match ← c avs t with | .ok r => out := out ++ [r] | .error _ => pure ()
  return out

/-- `DEEP_IMP_REWR_MCONV`'s `self net ths`: carries the (already-built) net; its
    `augment` ignores its argument (as in `impconv.ml`), `diminish` filters. -/
partial def deepSelf (V : ImpConvVars)
    (net : Fo_nets.t ((Tset.t → annot_conv) × Tset.t × thm)) (ths : List thm) :
    WithContext (atomic → annot_mconv) :=
  .mk
    (fun a => fun t => do
      let avs := Tset.flat_revmap (fun th => Tset.freesl V.T_ (hyp th)) ths
      let avs' := Tset.union (Tset.frees V.T_ t) avs
      let cnv : amconv := fun u => do return .ok (← mREWRITES_IMPCONV net avs' u)
      match a with
      | .Atomic => dmTopDepth cnv t
      | .Non_atomic => cnv t)
    (fun _ => deepSelf V net ths)      -- augment ignores its argument (faithful)
    (fun v =>
      let survivors := ((Fo_nets.allTips net).filterMap (fun (_, vs, th) =>
        if Tset.mem v vs then none else some th)).reverse   -- OCaml `th :: !ths` reverses traversal order
      deepSelf V (Fo_nets.filter (fun (_, vs, _) => !(Tset.mem v vs)) net) survivors)

/-- Multiple conversion which returns all the possible rewrites (on one subterm
    only) by one theorem.  Builds the net once (`IO`), then wraps. -/
def DEEP_IMP_REWR_MCONV (B : BoolThms) (V : ImpConvVars) (ths : List thm) :
    IO (WithContext (atomic → annot_mconv)) := do
  let mut net := Fo_nets.empty_net
  -- OCaml `itlist target_impconv_net_of_thm ths empty_net` enters last-first; iterate reversed.
  for th in ths.reverse do net ← target_impconv_net_of_thm B V th net
  return deepSelf V net ths

/-- Takes a multiple conversion with hypotheses (which also takes a context as
    parameter) and makes a multiple implicational conversion out of it.
    Basically extends `[GENERAL_REWRITE_IMPCONV]` to the multiple conversion
    case. -/
partial def REWR_IMPMCONV_OF_MCONV (B : BoolThms) (D : ImpConvDeps)
    (c : WithContext (atomic → annot_mconv)) : WithContext (atomic → imp_mconv) :=
  .mk
    (fun a => fun v t => do
      let IMP_SYM (th : thm) : IO (Except String thm) := REWR_RULE B D.imp_sym' th
      let TRY_GEN (v : term) (th : thm) : thm := (B.GEN v th).toOption.getD th
      -- f (th,ho,new_vars) = ... (same as REWR_IMPCONV_OF_CONV, per element)
      let f (r : thm × Option term × List term) : IO (Except String thm) := do
        let (th, ho, new_vars) := r
        match B.EQ_IMP_RULE th with
        | .error e => return .error e
        | .ok (th1, th2) =>
          match v with
          | .Co =>
            match UNDISCH_TERM B th2 with
            | .error e => return .error e
            | .ok (p, th2') =>
              match GSYM D.LEFT_IMP_EXISTS_THM with
              | .error e => return .error e
              | .ok IMP_EXIST =>
                let rec exists_intro (vs : List term) : IO (Except String thm) := do
                  match vs with
                  | [] => DISCH_IMP_IMP B D (p :: list_of_option ho) th2'
                  | vv :: rest =>
                    match ← exists_intro rest with
                    | .error e => return .error e
                    | .ok th => match B.GEN vv th with
                                | .error _ => return .ok th
                                | .ok gth => match ← REWR_RULE B IMP_EXIST gth with
                                             | .ok rr => return .ok rr | .error _ => return .ok th
                exists_intro new_vars
          | .Contra =>
            match ho with
            | none => match new_vars with
                      | [] => return .ok th1
                      | _ :: _ => return (MAP_CONCLUSION B (fun th => itlistM (fun vv t2 => .ok (TRY_GEN vv t2)) new_vars th) th1)
            | some h => match B.DISCH h th1 with
                        | .error e => return .error e
                        | .ok dh => match ← IMP_SYM dh with
                                    | .error e => return .error e
                                    | .ok th1' => match new_vars with
                                                  | [] => return .ok th1'
                                                  | _ :: _ => return (MAP_CONCLUSION B (fun th => itlistM (fun vv t2 => .ok (TRY_GEN vv t2)) new_vars th) th1')
      match ← c.apply a t with
      | .error e => return .error e
      | .ok rs => do
        let mut out := []
        for r in rs do match ← f r with | .ok x => out := out ++ [x] | .error e => return .error e
        return .ok out)
    (fun x => REWR_IMPMCONV_OF_MCONV B D (c.augment x))
    (fun x => REWR_IMPMCONV_OF_MCONV B D (c.diminish x))

/- ---------------------------------------------------------------------- -/
/- Target rewriting (`impconv.ml` 1751-1863).                             -/
/- ---------------------------------------------------------------------- -/

/-- `EXISTSs i p`: introduce a chain of existentials with the given witnesses
    (`impconv.ml` 1752–1756). -/
def EXISTSs (B : BoolThms) (i : List (term × term)) (p : term) : Except String thm := do
  let (codom, dom) := unzip i
  -- f i ps = vsubst [i] (snd (dest_exists (hd ps))) :: ps
  let f (iv : term × term) (ps : List term) : Except String (List term) := do
    let h ← hd ps
    let (_, body) ← dest_exists h
    let vf ← vsubst [iv]
    return (vf body) :: ps
  let lme ← list_mk_exists dom p
  let hps ← rev_itlistM f i [lme]
  match hps with
  | [] => failwith "EXISTSs"
  | h :: ps =>
    -- rev_itlist EXISTS (zip ps (rev codom)) (ASSUME h)
    let pairs ← zip ps codom.reverse
    rev_itlistM (fun (pv : term × term) th => B.EXISTS pv th) pairs (← ASSUME h)

/-- `EXISTS_CTXIMPCONV`: hint existentials by matching the body against context
    theorems (`impconv.ml` 1751–1795). -/
partial def existsSelf (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars) (ts : Tset.t) :
    WithContext imp_conv :=
  .mk
    (fun v t => do
      let LEFT_FORALL_IMP (th : thm) : IO (Except String thm) := REWR_RULE B D.LEFT_FORALL_IMP_THM th
      match v, t with
      | .Co, .Comb (.Const "?" _) _ =>
        let (vs, b) := strip_exists t
        let bs := Basics.conjuncts b   -- OCaml strip_conj = binops `/\`
        -- hmatch (n,b) : the matcher for the n-th conjunct
        let hmatch (nb : Nat × term) : term → IO (Except String (List (term × term) × Nat)) :=
          fun h => do
            let (n, bpat) := nb
            match variables bpat with
            | .error e => return .error e
            | .ok vbs =>
              let (lvs, lcs) := partition (fun x => mem x vs) vbs
              match lvs with
              | [] => return (failwith "EXISTS_CTXIMPCONV")
              | _ :: _ =>
                match ← term_match lcs bpat h with
                | .error _ => return (failwith "EXISTS_CTXIMPCONV")
                | .ok (_, i, j) =>
                    if (j.filter (fun (a, b) => a != b)) == [] then
                      return .ok ((if i == [] then (lvs.zip lvs) else i), n)
                    else return (failwith "EXISTS_CTXIMPCONV")
        -- s,n = tryfind_fun (mapfilteri (curry (tryfind o hmatch)) bs) ts
        -- Build the list of matchers (one per conjunct), each a `thm list → result`
        let matchers : List (Tset.t → IO (Except String (List (term × term) × Nat))) :=
          (bs.zipIdx).map (fun (bpat, n) => fun (tsl : Tset.t) => do
            -- tryfind (hmatch (n,bpat)) tsl   (tsl : context terms)
            let rec tf : Tset.t → IO (Except String (List (term × term) × Nat))
              | [] => return (failwith "tryfind")
              | h :: rest => do match ← hmatch (n, bpat) h with
                                | .ok r => return .ok r | .error _ => tf rest
            tf tsl)
        -- tryfind_fun matchers ts
        let rec tff : List (Tset.t → IO (Except String (List (term × term) × Nat))) →
            IO (Except String (List (term × term) × Nat))
          | [] => return (failwith "tryfind_fun")
          | m :: ms => do match ← m ts with | .ok r => return .ok r | .error _ => tff ms
        match ← tff matchers with
        | .error e => return .error e
        | .ok (s, n) =>
          match ← (ExceptT.run do
            let th ← ExceptT.mk (pure (EXISTSs B (vs.map (fun v => (rev_assocd v s v, v))) b))
            let th' ← liftExcept (DISCH_HD B th)
            let h ← liftExcept ((do Basics.dest_imp (concl th')).map Prod.fst)
            match Basics.conjuncts h with
            | [] => throw "EXISTS_CTXIMPCONV: empty"
            | [_] => ExceptT.mk (pure (B.DISCH V.T_ th))
            | _ :: _ =>
              let hs := Basics.conjuncts h
              let (hs1, hrest) ← liftExcept (chop_list n hs)
              match hrest with
              | [] => throw "EXISTS_CTXIMPCONV"
              | h' :: hs2 =>
                let rhs ← liftExcept (list_mk_conj (h' :: (hs1 ++ hs2)))
                let mkEq ← ExceptT.mk (mk_eq : IO (Except String ((term × term) → Except String term)))
                let eqtm ← liftExcept (mkEq (h, rhs))
                let hs_th ← liftExcept (Canon.CONJ_ACI_RULE B eqtm)
                let th1 ← ExceptT.mk (Simp.convRuleIO
                  (Simp.landConvIO (REWR_CONV B hs_th)) th')
                let th1b ← ExceptT.mk (Simp.convRuleIO (REWR_CONV B D.IMP_CONJ) th1)
                let th2 ← liftExcept (B.UNDISCH th1b)
                let vs' := subtract vs (s.map Prod.snd)
                -- itlist (fun v th -> try LEFT_FORALL_IMP (GEN v th) with _ -> th) vs' th2
                let mut acc := th2
                for v in vs'.reverse do
                  match B.GEN v acc with
                  | .error _ => pure ()
                  | .ok g =>
                    let lfr : Except String thm ← LEFT_FORALL_IMP g
                    match lfr with | .ok r => acc := r | .error _ => pure ()
                pure acc)
          with
          | .ok r => return .ok r
          | .error e => return .error e
      | _, _ => return (failwith "EXISTS_CTXIMPCONV"))
    (fun ts' => existsSelf B D V (Tset.union ts' ts))
    (fun _ => existsSelf B D V ts)

/-- `EXISTS_CTXIMPCONV` (target-rewriting version, `impconv.ml` 1751): the
    existential-hinting conversion.  (Named `existsHintCtx` to avoid clashing
    with the structural `EXISTS_CTXIMPCONV` used by `SUB_CTXIMPCONV`; this is the
    one referenced by `TARGET_REWRITE_IMPCONV`/`HINT_EXISTS_TAC`, exactly as the
    OCaml `let EXISTS_CTXIMPCONV = ...` shadows the earlier definition.) -/
def existsHintCtx (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars) : WithContext imp_conv :=
  existsSelf B D V []

/-- A small IO `find_term`: first subterm satisfying the IO predicate `p`. -/
private partial def findTermIO (p : term → IO Bool) (tm : term) : IO (Option term) := do
  if ← p tm then return (some tm)
  else match tm with
       | .Abs _ b => findTermIO p b
       | .Comb l r => match ← findTermIO p l with
                      | some x => return (some x)
                      | none => findTermIO p r
       | _ => return none

/-- Takes a theorem which results of an implicational conversion and applies a
    multiple implicational conversion on the outcome. -/
def bind_impmconv (B : BoolThms) (c : imp_mconv) (v : Variance.t) (th : thm) :
    IO (Except String (List thm)) := do
  match Basics.dest_imp (concl th) with
  | .error e => return .error e
  | .ok (t1, t2) =>
    match v with
    | .Co => match ← c v t1 with
             | .ok l => return (l.mapM (fun cth => B.IMP_TRANS cth th)) | .error e => return .error e
    | .Contra => match ← c v t2 with
                 | .ok l => return (l.mapM (fun cth => B.IMP_TRANS th cth)) | .error e => return .error e

/-- Target rewrite implicational conversion: `[TARGET_REWRITE_IMPCONV sths ts]`
    is an implicational conversion which applies all the possible implicational
    rewrites on the input term until one of the resulting terms matches one of
    the terms in `[ts]`.

    Note that we allow several target terms and not just one. See
    `TARGET_REWRITE_TAC` for a justification.  (`impconv.ml` 1806–1845.) -/
partial def TARGET_REWRITE_IMPCONV (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars)
    (sths : List thm) (ts : List term) : imp_conv := fun v t => do
  let POST := TRY_CTXIMPCONV D V (TOP_DEPTH_CTXIMPCONV B D V (existsHintCtx B D V))
  -- PRE = apply (TRY_CTXIMPCONV (REWRITE_CTXIMPCONV []))
  let PRE : imp_conv := (TRY_CTXIMPCONV D V (REWRITE_CTXIMPCONV B D V [])).apply
  -- pre v th = try bind_impconv PRE v th with Unchanged -> th
  let pre (v : Variance.t) (th : thm) : IO (Except String thm) := do
    match ← bind_impconv B PRE v th with
    | .ok r => return .ok r
    | .error e => if e == unchanged then return .ok th else return .error e
  -- f = DEPTH_CTXIMPMCONV o REWR_IMPMCONV_OF_MCONV o DEEP_IMP_REWR_MCONV
  -- The outer two stages are TOTAL, so they compose with plain `o` (right-to-
  -- left: REWR_IMPMCONV_OF_MCONV first, then DEPTH_CTXIMPMCONV).  The innermost
  -- stage, DEEP_IMP_REWR_MCONV, is IO-valued here, so it is applied separately.
  let f := DEPTH_CTXIMPMCONV B D V o REWR_IMPMCONV_OF_MCONV B D
  let one_step_sths (v : Variance.t) (uh : thm) : IO (Except String (List thm)) := do
    let deep ← DEEP_IMP_REWR_MCONV B V sths
    let fconv : imp_mconv := (f deep).apply
    match ← pre v uh with
    | .error e => return .error e
    | .ok preuh => match ← bind_impmconv B fconv v preuh with
      | .error e => return .error e
      | .ok l =>
        -- map (post v) l  where post v = bind_ctximpconv POST v
        let mut out := []
        for th in l do match ← bind_ctximpconv B POST v th with
                       -- OCaml `map (post v) l` propagates (impconv.ml 1820)
                       | .ok r => out := out ++ [r] | .error e => return .error e
        return .ok out
  let flat (l : List (List thm)) : List thm := uniq (itlist (merge thm_lt) l [])
  -- is_one_sol g = can (find_term (can (fo_term_match [] g))) o sel
  let is_one_sol (g : term) (outcome : term) : IO Bool := do
    match ← findTermIO (fun sub => do
      match ← fo_term_match [] g sub with | .ok _ => pure true | .error _ => pure false) outcome with
    | some _ => pure true | none => pure false
  let rec self (ths : List thm) : IO (Except String thm) := do
    -- pool = flat (map (mergesort thm_lt o one_step_sths v) ths)
    -- `one_step_sths v` is `IO (Except ...)`-valued and `mergesort thm_lt` is
    -- total, so the composition is an `oIOm`; `one_step_sths` runs FIRST.
    let step := mergesort thm_lt oIOm one_step_sths v
    let mut steps := []
    for th in ths do
      -- OCaml `flat (map (.. o one_step_sths v) ths)` propagates (impconv.ml 1823)
      match ← step th with | .ok l => steps := steps ++ [l] | .error e => return .error e
    let pool := flat steps
    -- OCaml: try bind_ctximpconv POST v (find is_sol pool) with _ -> <recurse>.
    -- is_sol th = tryfind is_one_sol ts (sel th).  sel = imp_conv_outcome th v is OUTSIDE `can`,
    -- so if it fails, is_sol RAISES → find RAISES → the whole attempt fails → recurse deeper.
    -- Likewise tryfind over ts=[] raises.  We thread that as `.error` out of findSol.
    let isSol (th : thm) : IO (Except String Bool) := do
      match imp_conv_outcome th v with
      | .error e => return .error e          -- sel raised → propagate (→ recurse branch)
      | .ok sel =>
        match ts with
        | [] => return (failwith "tryfind")  -- tryfind is_one_sol [] raises
        | g :: _ => return .ok (← is_one_sol g sel)
    -- find is_sol pool: first th where is_sol th is true; a raised is_sol aborts the scan.
    let rec findSol : List thm → IO (Except String (Option thm))
      | [] => return .ok none
      | th :: rest => do
          match ← isSol th with
          | .error e => return .error e      -- propagate (OCaml find re-raises)
          | .ok true => return .ok (some th)
          | .ok false => findSol rest
    let attempt : IO (Except String thm) := do
      match ← findSol pool with
      | .error e => return .error e
      | .ok none => return (failwith "find")           -- find found nothing → raises
      | .ok (some th) => bind_ctximpconv B POST v th
    match ← attempt with
    | .ok r => return .ok r
    | .error _ =>
      match pool with
      | [] => return (failwith "TARGET_REWRITE_IMPCONV: no path found")
      | _ :: _ =>
        -- self (map (bind_ctximpconv POST v) pool)
        let mut nextThs := []
        for th in pool do match ← bind_ctximpconv B POST v th with
                          -- OCaml `map (bind_ctximpconv POST v) pool` propagates (impconv.ml 1831)
                          | .ok r => nextThs := nextThs ++ [r] | .error e => return .error e
        self nextThs
  match IMP_REFL D V t with
  | .ok r0 => self [r0]
  | .error e => return .error e

/-- Tactic version of it.

    Since the target theorem is preprocessed, it can yield several theorems.
    Therefore, there is not just one possible target pattern but several. -/
def TARGET_REWRITE_TAC (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars)
    (sths : List thm) (th : thm) : tactic := fun g => do
  let mut sths' := []
  for s in sths do match ← preprocess B D s with
    -- OCaml `flat (map preprocess sths)` propagates (impconv.ml 1856)
    | .ok l => sths' := sths' ++ l | .error e => return .error e
  match ← preprocess B D th with
  | .error e => return .error e
  | .ok ths =>
    let mut pats := []
    for t in ths do match ← patterns_of_thm B V t with
      -- OCaml `map patterns_of_thm ths` propagates (impconv.ml 1857)
      | .ok p => pats := pats ++ [p] | .error e => return .error e
    -- (TARGET_REWRITE_IMPCONV sths' pats) + imp_conv_of_ctx_imp_conv (REWRITE_CTXIMPCONV ths)
    let c1 : imp_conv := TARGET_REWRITE_IMPCONV B D V sths' pats
    let c2 : imp_conv := imp_conv_of_ctx_imp_conv (REWRITE_CTXIMPCONV B D V ths)
    let cnv : imp_conv := THEN_IMPCONV B c1 c2
    match ← IMPCONV_TAC B cnv g with
    | .ok r => return .ok r
    | .error e => if e == unchanged then return (failwith "Unchanged") else return .error e

/-- `HINT_EXISTS_TAC = fail_if_unchanged (CTXIMPCONV_TAC (TOP_DEPTH_CTXIMPCONV
    EXISTS_CTXIMPCONV))`. -/
def HINT_EXISTS_TAC (B : BoolThms) (D : ImpConvDeps) (V : ImpConvVars) : tactic := fun g => do
  match ← CTXIMPCONV_TAC B V (TOP_DEPTH_CTXIMPCONV B D V (existsHintCtx B D V)) g with
  | .ok r => return .ok r
  | .error e => if e == unchanged then return (failwith "Unchanged") else return .error e

end HolCore.ImpConv
