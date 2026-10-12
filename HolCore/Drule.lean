/- File: Drule.lean
More sophisticated derived rules including definitions and rewriting.
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Original (c) Copyright, Michael Faerber 2018
Lean4 translation by Chris Walton 2026
-/

import HolCore.Bool
import HolCore.Basics
import HolCore.Fusion
import HolCore.Equal
import HolCore.Nets
import HolCore.Printer
import HolCore.Preterm

open HolCore.Kernel
open HolCore.Basics
open HolCore.Lib
open HolCore.Bool
open HolCore.Equal
open HolCore.Nets

namespace HolCore.Drule

/- ---------------------------------------------------------------------- -/
/- Type of instantiations, with terms, types and higher-order data.       -/
/- ---------------------------------------------------------------------- -/

/-- An instantiation: higher-order beta-reduction counts, a term
    substitution, and a type substitution. -/
abbrev instantiation :=
  List (Int × term) × List (term × term) × List (hol_type × hol_type)

/- ---------------------------------------------------------------------- -/
/- The last recourse when all else fails!                                 -/
/- ---------------------------------------------------------------------- -/

/-- Assert an arbitrary sequent as a theorem, via a fresh axiom. Uses the
    bool rule `MP`, so takes the `BoolThms` record `B`. UNSOUND — a last
    recourse only. -/
def mk_thm (B : BoolThms) (asl : List term) (c : term) : IO (Except String thm) := do
  let rec mkImps : List term → term → Except String term
    | [], b => pure b
    | h :: t, b => do mk_imp h (← mkImps t b)
  -- rev_itlist (fun t th => MP th (ASSUME t)) (rev asl) ax  (left fold)
  match mkImps asl.reverse c with
  | .error e => return .error e
  | .ok impTm =>
    match ← new_axiom impTm with
    | .error e => return .error e
    | .ok ax   => return rev_itlistM (fun t th => do B.MP th (← ASSUME t)) asl.reverse ax

/- ---------------------------------------------------------------------- -/
/- Derived congruence rules; very useful things!                          -/
/- ---------------------------------------------------------------------- -/

/-- The `bool → bool → bool` type. -/
private def bbb : hol_type := .Tyapp "fun" [bool_ty, .Tyapp "fun" [bool_ty, bool_ty]]

/-- From `|- p = p'` and `|- q = q'` derive `|- (p /\ q) = (p' /\ q')`. -/
def MK_CONJ (eq1 eq2 : thm) : Except String thm := do
  MK_COMB (← AP_TERM (.Const "/\\" bbb) eq1) eq2

/-- From `|- p = p'` and `|- q = q'` derive `|- (p \/ q) = (p' \/ q')`. -/
def MK_DISJ (eq1 eq2 : thm) : Except String thm := do
  MK_COMB (← AP_TERM (.Const "\\/" bbb) eq1) eq2

/-- From `|- P x = Q x` derive `|- (!x. P x) = (!x. Q x)`. -/
def MK_FORALL (v : term) (th : thm) : IO (Except String thm) := do
  match ← mk_const "!" [] with
  | .error e => return .error e
  | .ok atm  => return (do AP_TERM (inst [(type_of v, aty)] atm) (← ABS v th))

/-- From `|- P x = Q x` derive `|- (?x. P x) = (?x. Q x)`. -/
def MK_EXISTS (v : term) (th : thm) : IO (Except String thm) := do
  match ← mk_const "?" [] with
  | .error e => return .error e
  | .ok atm  => return (do AP_TERM (inst [(type_of v, aty)] atm) (← ABS v th))

/- ---------------------------------------------------------------------- -/
/- Eliminate the antecedent of a theorem using a conversion/proof rule.   -/
/- ---------------------------------------------------------------------- -/

/-- `MP_CONV cnv th`: from `th : |- p ==> q` and a conversion proving `p`
    (either `|- p` or `|- p <=> T`), derive `|- q`. Uses bool `MP`/`EQT_ELIM`. -/
def MP_CONV (B : BoolThms) (cnv : conv) (th : thm) : Except String thm := do
  let (l, _) ← Basics.dest_imp (concl th)
  let ath ← cnv l
  match B.MP th (← B.EQT_ELIM ath) with
  | .ok r    => .ok r
  | .error _ => B.MP th ath

/- ---------------------------------------------------------------------- -/
/- Multiple beta-reduction (we use a slight variant below).               -/
/- ---------------------------------------------------------------------- -/

/-- Repeatedly beta-reduce a (possibly nested) application. -/
partial def BETAS_CONV (tm : term) : Except String thm :=
  match tm with
  | .Comb (.Abs _ _) _  => BETA_CONV tm
  | .Comb (.Comb _ _) _ => (THENC (RATOR_CONV BETAS_CONV) BETA_CONV) tm
  | _ => failwith "BETAS_CONV"

/- ---------------------------------------------------------------------- -/
/- Instantiators.                                                         -/
/- ---------------------------------------------------------------------- -/

/-- Apply an instantiation to a term (types, then terms, then higher-order
    beta-reductions). Pure (`inst`/`vsubst` only). -/
partial def instantiate (i : instantiation) (tm : term) : Except String term :=
  let (bcs, tmin, tyin) := i
  -- betas n tm: peel n arguments off an application and beta-substitute.
  let rec peel (n : Nat) (acc : List term) (t : term) : Except String (List term × term) :=
    match n with
    | 0     => .ok (acc, t)
    | n + 1 => do peel n ((← rand t) :: acc) (← rator t)
  let betas (n : Nat) (tm : term) : Except String term := do
    let (args, lam) ← peel n [] tm
    -- rev_itlist (fun a l => let (v,b) = dest_abs l in vsubst [a,v] b) args lam
    let step (a : term) (l : term) : Except String term := do
      let (v, b) ← dest_abs l
      return (← vsubst [(a, v)]) b
    let rec go : List term → term → Except String term
      | [], l => .ok l
      | a :: as', l => do go as' (← step a l)
    go args lam
  let rec ho_betas (pat tm : term) : Except String term :=
    if is_var pat || is_const pat then fail
    else
      match dest_abs tm with
      | .ok (bv, bod) => do mk_abs bv (← ho_betas (← body pat) bod)
      | .error _ =>
        let (hop, args) := strip_comb pat
        -- Same control-flow point as `HO_BETAS` below (drule.ml 112-114): the
        -- OCaml `try` spans BOTH the `rev_assoc` lookup AND the arity check, so
        -- an arity MISMATCH must fall through to the descent, not abort.
        let direct : Except String term := do
          let n ← rev_assoc hop bcs
          if (args.length : Int) == n then betas n.toNat tm else fail
        match direct with
        | .ok r => .ok r
        | .error _ =>
          match dest_comb pat, dest_comb tm with
          | .ok (lpat, rpat), .ok (ltm, rtm) =>
            match ho_betas lpat ltm with
            | .ok lth =>
                match ho_betas rpat rtm with
                | .ok rth => mk_comb lth rth
                | .error _ => mk_comb lth rtm
            | .error _ => do mk_comb ltm (← ho_betas rpat rtm)
          | _, _ => fail
  let itm := if tyin == [] then tm else inst tyin tm
  if tmin == [] then .ok itm
  else do
    let ttm := (← vsubst tmin) itm
    if bcs == [] then .ok ttm
    else match ho_betas itm ttm with
         | .ok r    => .ok r
         | .error _ => .ok ttm

/-- Instantiate a theorem (types, then terms, then higher-order beta), failing
    if a substituted variable becomes free in the assumptions. Pure.

    `HO_BETAS` must descend when the betacount lookup SUCCEEDS but the arity
    does not match.  drule.ml 112-114 is

        try let n = rev_assoc hop bcs in
            if length args = n then BETAS_CONV n tm else fail()
        with Failure _ -> <descend via dest_comb>

    and the `try` spans BOTH the lookup AND the arity check, so an arity mismatch
    must FALL THROUGH to the descent, not escape.  Both this and the term-level
    `ho_betas` in `instantiate` therefore wrap the lookup and the arity check in
    ONE fallible step and descend on any failure. -/
partial def INSTANTIATE (i : instantiation) (th : thm) : Except String thm :=
  let (bcs, tmin, tyin) := i
  -- conv performing n leading beta-reductions
  let rec betasN (n : Int) : conv := fun tm =>
    if n == 1 then TRY_CONV BETA_CONV tm
    else (THENC (RATOR_CONV (betasN (n - 1))) (TRY_CONV BETA_CONV)) tm
  -- higher-order beta at the theorem level
  let rec HO_BETAS (pat tm : term) : Except String thm :=
    if is_var pat || is_const pat then fail
    else
      match dest_abs tm with
      | .ok (bv, _) => do ABS bv (← HO_BETAS (← body pat) (← body tm))
      | .error _ =>
        let (hop, args) := strip_comb pat
        -- drule.ml 112-114:
        --     try let n = rev_assoc hop bcs in
        --         if length args = n then BETAS_CONV n tm else fail()
        --     with Failure _ -> <descend via dest_comb>
        -- *** THE `try` SPANS BOTH THE LOOKUP AND THE ARITY CHECK. *** An arity
        -- MISMATCH raises `fail()` INSIDE the `try`, so it must fall through to
        -- the descent below - it must NOT abort.  Translating this as a two-way
        -- `match` on `rev_assoc` alone let the arity-mismatch failure escape,
        -- which is why a pattern like `g f x (y f x)` (hop `g`, three args,
        -- betacount two) failed instead of splitting into `g f x` and `y f x`.
        let direct : Except String thm := do
          let n ← rev_assoc hop bcs
          if (args.length : Int) == n then betasN n tm else fail
        match direct with
        | .ok r => .ok r
        | .error _ =>
          match dest_comb pat, dest_comb tm with
          | .ok (lpat, rpat), .ok (ltm, rtm) =>
            match HO_BETAS lpat ltm with
            | .ok lth =>
                match HO_BETAS rpat rtm with
                | .ok rth => MK_COMB lth rth
                | .error _ => AP_THM lth rtm
            | .error _ => do AP_TERM ltm (← HO_BETAS rpat rtm)
          | _, _ => fail
  do
    let ith ← if tyin == [] then .ok th else INST_TYPE tyin th
    if tmin == [] then .ok ith
    else
      let tth ← INST tmin ith
      if hyp tth == hyp th then
        if bcs == [] then .ok tth
        else match HO_BETAS (concl ith) (concl tth) with
             | .ok eth => EQ_MP eth tth
             | .error _ => .ok tth
      else failwith "INSTANTIATE: term or type var free in assumptions"

/-- Like `INSTANTIATE`, but first discharges (and later re-adds) the relevant
    hypotheses so that instantiation is valid even with assumptions. Uses the
    bool rules `DISCH`/`UNDISCH`. -/
def INSTANTIATE_ALL (B : BoolThms) (i : instantiation) (th : thm) : Except String thm :=
  let (_, tmin, tyin) := i
  if tmin == [] && tyin == [] then .ok th
  else
    let hyps := hyp th
    if hyps == [] then INSTANTIATE i th
    else do
      let (tyrel, tyiirel) :=
        if tyin == [] then ([], hyps)
        else
          let tvs := itlist (fun p acc => union (tyvars p.2) acc) tyin []
          hyps.partition (fun tm =>
            !(intersect tvs (type_vars_in_term tm)).isEmpty)
      let (tmrel, _) :=
        if tmin == [] then ([], tyiirel)
        else
          let vs := itlist (fun p acc => union (frees p.2) acc) tmin []
          tyiirel.partition (fun tm => !(intersect vs (frees tm)).isEmpty)
      let rhyps := union tyrel tmrel
      let th1 ← itlistM B.DISCH rhyps th
      let th2 ← INSTANTIATE i th1
      let rec undischN : Nat → thm → Except String thm
        | 0, t => .ok t
        | n + 1, t => do undischN n (← B.UNDISCH t)
      undischN rhyps.length th2

/- ---------------------------------------------------------------------- -/
/- Unification of types.                                                  -/
/- ---------------------------------------------------------------------- -/

/-- First-order unification of two types, extending a substitution. -/
partial def type_unify (ty1 ty2 : hol_type) (sofar : List (hol_type × hol_type)) :
    Except String (List (hol_type × hol_type)) :=
  let augment1 (sofar : List (hol_type × hol_type)) (p : hol_type × hol_type) :
      Except String (hol_type × hol_type) :=
    let s' := type_subst sofar p.1
    if occurs_in p.2 s' && !(p.1 == p.2) then failwith "type_unify: augment1"
    else .ok (s', p.2)
  let raw_augment_insts (p : hol_type × hol_type)
      (insts : List (hol_type × hol_type)) : Except String (List (hol_type × hol_type)) := do
    return p :: (← insts.mapM (augment1 [p]))
  let augment_insts (p : hol_type × hol_type)
      (insts : List (hol_type × hol_type)) : Except String (List (hol_type × hol_type)) :=
    let ty' := type_subst insts p.1
    if ty' == p.2 then .ok insts
    else if occurs_in p.2 ty' then failwith "type_unify: augment_insts"
    else raw_augment_insts (ty', p.2) insts
  let rec unify (ty1 ty2 : hol_type) (sofar : List (hol_type × hol_type)) :
      Except String (List (hol_type × hol_type)) :=
    if ty1 == ty2 then .ok sofar
    else if is_vartype ty1 then
      match rev_assoc ty1 sofar with
      | .ok ty1' => unify ty1' ty2 sofar
      | .error _ => augment_insts (ty2, ty1) sofar
    else if is_vartype ty2 then
      match rev_assoc ty2 sofar with
      | .ok ty2' => unify ty1 ty2' sofar
      | .error _ => augment_insts (ty1, ty2) sofar
    else
      match dest_type ty1, dest_type ty2 with
      | .ok (l1, r1), .ok (l2, r2) =>
          if l1 == l2 then
            (itlist2 (fun a b (acc : Except String (List (hol_type × hol_type))) =>
                        acc.bind (unify a b)) r1 r2 (.ok sofar)).bind id
          else failwith "unify_type"
      | _, _ => failwith "unify_type"
  unify ty1 ty2 sofar

/- ---------------------------------------------------------------------- -/
/- First order unification of terms of the same type.                     -/
/- ---------------------------------------------------------------------- -/

/-- First-order unification of two terms, returning an instantiation. Uses the
    IO `subst`, so is IO-valued. -/
partial def term_unify (vars : List term) (tm1 tm2 : term) :
    IO (Except String instantiation) := ExceptT.run do
  -- apply a term substitution (Basics `subst`, an IO factory) to a term
  let applySubst (theta : List (term × term)) (s : term) : ExceptT String IO term := do
    -- in ExceptT String IO, `← (io : IO (Except String X))` yields `X`
    let f ← (subst theta : IO (Except String (term → IO (Except String term))))
    (f s : IO (Except String term))
  let augment1 (sofar : List (term × term)) (p : term × term) :
      ExceptT String IO (term × term) := do
    let s' ← applySubst sofar p.1
    if vfree_in p.2 s' && !(p.1 == p.2) then throw "term_unify: augment1"
    else return (s', p.2)
  let raw_augment_insts (p : term × term) (insts : List (term × term)) :
      ExceptT String IO (List (term × term)) := do
    return p :: (← insts.mapM (augment1 [p]))
  let augment_insts (p : term × term) (insts : List (term × term)) :
      ExceptT String IO (List (term × term)) := do
    let t' := (← liftExcept (vsubst insts)) p.1
    if t' == p.2 then return insts
    else if vfree_in p.2 t' then throw "augment_insts"
    else raw_augment_insts (t', p.2) insts
  let rec unify (vars : List term) (tm1 tm2 : term) (sofar : List (term × term)) :
      ExceptT String IO (List (term × term)) := do
    if tm1 == tm2 then return sofar
    else if is_var tm1 && mem tm1 vars then
      match rev_assoc tm1 sofar with
      | .ok tm1' => unify vars tm1' tm2 sofar
      | .error _ => augment_insts (tm2, tm1) sofar
    else if is_var tm2 && mem tm2 vars then
      match rev_assoc tm2 sofar with
      | .ok tm2' => unify vars tm1 tm2' sofar
      | .error _ => augment_insts (tm1, tm2) sofar
    else if is_abs tm1 then
      let tm1' ← liftExcept (body tm1)
      let bv1 ← liftExcept (bndvar tm1)
      let bv2 ← liftExcept (bndvar tm2)
      let tm2' ← applySubst [(bv1, bv2)] (← liftExcept (body tm2))
      unify vars tm1' tm2' sofar
    else
      let (l1, r1) ← liftExcept (dest_comb tm1)
      let (l2, r2) ← liftExcept (dest_comb tm2)
      unify vars l1 l2 (← unify vars r1 r2 sofar)
  let insts ← unify vars tm1 tm2 []
  return ([], insts, [])

/- ---------------------------------------------------------------------- -/
/- Unification of terms and their types together.                         -/
/- ---------------------------------------------------------------------- -/

/-- Unify two terms together with their types, extending an instantiation.
    IO-valued (uses `subst`). -/
partial def term_type_unify (tm1 tm2 : term) (i : instantiation) :
    IO (Except String instantiation) := ExceptT.run do
  let (it, tminsts0, tyinsts0) := i
  -- unify the types of s and t under the current tyinsts, and compose
  let augment_tyinsts (s t : term) (tyinsts : List (hol_type × hol_type)) :
      ExceptT String IO (List (hol_type × hol_type)) := do
    let sty := type_of (inst tyinsts s)
    let tty := type_of (inst tyinsts t)
    let tyinsts' ← liftExcept (type_unify sty tty [])
    return tyinsts' ++ tyinsts.map (fun (ty, v) => (type_subst tyinsts' ty, v))
  let applySubst (theta : List (term × term)) (s : term) : ExceptT String IO term := do
    let f ← (subst theta : IO (Except String (term → IO (Except String term))))
    (f s : IO (Except String term))
  let augment1 (sofar : List (term × term)) (p : term × term) :
      ExceptT String IO (term × term) := do
    let s' ← applySubst sofar p.1
    if vfree_in p.2 s' && !(p.1 == p.2) then throw "term_unify: augment1"
    else return (s', p.2)
  let raw_augment_insts (p : term × term)
      (sofar : List (term × term) × List (hol_type × hol_type)) :
      ExceptT String IO (List (term × term) × List (hol_type × hol_type)) := do
    return (p :: (← sofar.1.mapM (augment1 [p])), sofar.2)
  let augment_insts (p : term × term)
      (sofar : List (term × term) × List (hol_type × hol_type)) :
      ExceptT String IO (List (term × term) × List (hol_type × hol_type)) := do
    let (tminsts, tyinsts) := sofar
    let tminsts' := tminsts.map (fun (t, v) => (inst tyinsts t, inst tyinsts v))
    let t' := inst tyinsts ((← liftExcept (vsubst tminsts')) p.1)
    let v' := inst tyinsts p.2
    let sofar' := (tminsts', tyinsts)
    if t' == v' then return sofar'
    else if vfree_in v' t' then throw "term_unify: augment_insts"
    else raw_augment_insts (t', v') sofar'
  let rec unify (tm1 tm2 : term)
      (sofar : List (term × term) × List (hol_type × hol_type)) :
      ExceptT String IO (List (term × term) × List (hol_type × hol_type)) := do
    let (tminsts, tyinsts) := sofar
    if tm1 == tm2 then return sofar
    else if is_var tm1 then
      match rev_assoc tm1 tminsts with
      | .ok tm1' => unify tm1' tm2 sofar
      | .error _ => augment_insts (tm2, tm1) (tminsts, ← augment_tyinsts tm1 tm2 tyinsts)
    else if is_var tm2 then
      match rev_assoc tm2 tminsts with
      | .ok tm2' => unify tm1 tm2' sofar
      | .error _ => augment_insts (tm1, tm2) (tminsts, ← augment_tyinsts tm1 tm2 tyinsts)
    else if is_abs tm1 then
      let bv1 ← liftExcept (bndvar tm1)
      let bv2 ← liftExcept (bndvar tm2)
      let tm1' ← liftExcept (body tm1)
      let tm2' ← applySubst [(bv1, bv2)] (← liftExcept (body tm2))
      unify tm1' tm2' sofar
    else if is_const tm1 then
      if HolCore.Printer.name_of tm1 != HolCore.Printer.name_of tm2 then throw "term_unify"
      else return (tminsts, ← augment_tyinsts tm1 tm2 tyinsts)
    else
      let (l1, r1) ← liftExcept (dest_comb tm1)
      let (l2, r2) ← liftExcept (dest_comb tm2)
      unify l1 l2 (← unify r1 r2 sofar)
  let (tminsts', tyinsts') ← unify tm1 tm2 (tminsts0, tyinsts0)
  return (it, tminsts', tyinsts')

/- ---------------------------------------------------------------------- -/
/- Modify bound variable names at depth. (Not very efficient...)          -/
/- ---------------------------------------------------------------------- -/

/-- Rename bound variables in `tm` according to a name-pair environment.
    Failures fall back to leaving the (sub)term unchanged, as in OCaml. -/
partial def deep_alpha (env : List (String × String)) (tm : term) : term :=
  let tryalpha (v : term) (tm : term) : term :=
    match alpha v tm with
    | .ok r => r
    | .error _ =>
      match variant (frees tm) v with
      | .ok v' => match alpha v' tm with | .ok r => r | .error _ => tm
      | .error _ => tm
  let rec go (env : List (String × String)) (tm : term) : term :=
    if env == [] then tm
    else
      match dest_abs tm with
      | .ok (v, bod) =>
        match dest_var v with
        | .error _ => tm
        | .ok (vn, vty) =>
          match remove (fun p => p.2 == vn) env with
          | .ok ((vn', _), newenv) =>
              let v' := mk_var vn' vty
              let tm' := tryalpha v' tm
              match dest_abs tm' with
              | .ok (iv, ib) => (mk_abs iv (go newenv ib)).toOption.getD tm
              -- OCaml's inner `try` spans `remove`, `tryalpha` and this
              -- `dest_abs`, so a failure here takes the same fallback as a
              -- failed `remove`: descend into the body with `env` unchanged.
              | .error _ => (mk_abs v (go env bod)).toOption.getD tm
          | .error _ => (mk_abs v (go env bod)).toOption.getD tm
      | .error _ =>
        match dest_comb tm with
        | .ok (l, r) => (mk_comb (go env l) (go env r)).toOption.getD tm
        | .error _ => tm
  go env tm

/- ---------------------------------------------------------------------- -/
/- Higher order matching of terms.                                        -/
/- ---------------------------------------------------------------------- -/

/-- Homogeneity obligations from pattern matching: a bound-var environment,
    the concrete term, and the variable pattern. -/
abbrev homDatum := List (term × term) × term × term

/-- Extend `l` with `(y,x)` unless `x` is already bound to an alpha-variant. -/
private def safe_inserta (n : term × term) (l : List (term × term)) :
    Except String (List (term × term)) :=
  match rev_assoc n.2 l with
  | .ok z => if aconv n.1 z then .ok l else failwith "safe_inserta"
  | .error _ => .ok (n :: l)

/-- Like `safe_inserta` but with structural equality. -/
private def safe_insert (n : term × term) (l : List (term × term)) :
    Except String (List (term × term)) :=
  match rev_assoc n.2 l with
  | .ok z => if n.1 == z then .ok l else failwith "safe_insert"
  | .error _ => .ok (n :: l)

/-- Structural-equality safe insert for a type instantiation list. -/
private def safe_insert_ty (n : hol_type × hol_type) (l : List (hol_type × hol_type)) :
    Except String (List (hol_type × hol_type)) :=
  match rev_assoc n.2 l with
  | .ok z => if n.1 == z then .ok l else failwith "safe_insert"
  | .error _ => .ok (n :: l)

/-- Accumulate type instantiations from a term-term inst list (right fold). -/
private def get_type_insts : List (term × term) → List (hol_type × hol_type) →
    Except String (List (hol_type × hol_type))
  | [], b => .ok b
  | p :: t, b => do
      let (_, xty) ← dest_var p.2
      type_match xty (type_of p.1) (← get_type_insts t b)

/-- Pattern-matching phase (pure). `dn` is the dummy-variable name. -/
private partial def term_pmatch (lconsts : List term) (dn : String)
    (env : List (term × term)) (vtm ctm : term)
    (sofar : List (term × term) × List homDatum) :
    Except String (List (term × term) × List homDatum) :=
  let mk_dummy (ty : hol_type) : term := mk_var dn ty
  let (insts, homs) := sofar
  match vtm with
  | .Var _ _ =>
      match rev_assoc vtm env with
      | .ok ctm' => if ctm' == ctm then .ok sofar else failwith "term_pmatch"
      | .error _ =>
          if mem vtm lconsts then
            if ctm == vtm then .ok sofar
            else failwith "term_pmatch: can't instantiate local constant"
          else do return (← safe_inserta (ctm, vtm) insts, homs)
  | .Const vname vty =>
      match ctm with
      | .Const cname cty =>
          if vname == cname then
            if vty == cty then .ok sofar
            else do return (← safe_insert (mk_dummy cty, mk_dummy vty) insts, homs)
          else failwith "term_pmatch"
      | _ => failwith "term_pmatch"
  | .Abs vv vbod =>
      match ctm with
      | .Abs cv cbod => do
          let (_, cvty) ← dest_var cv
          let (_, vvty) ← dest_var vv
          let insts' ← safe_insert (mk_dummy cvty, mk_dummy vvty) insts
          term_pmatch lconsts dn ((cv, vv) :: env) vbod cbod (insts', homs)
      | _ => failwith "term_pmatch"
  | _ =>
      let vhop := repeat' rator vtm
      if is_var vhop && !(mem vhop lconsts) && !(can (rev_assoc vhop) env) then
        let vty := type_of vtm
        let cty := type_of ctm
        do
          let insts' ← if vty == cty then .ok insts
                       else safe_insert (mk_dummy cty, mk_dummy vty) insts
          return (insts', (env, ctm, vtm) :: homs)
      else do
        let (lv, rv) ← dest_comb vtm
        let (lc, rc) ← dest_comb ctm
        term_pmatch lconsts dn env rv rc (← term_pmatch lconsts dn env lv lc sofar)

/-- Turn accumulated insts into an `instantiation` (betacounts, term subst,
    type subst). (The OCaml "inconsistent patterning" warning is dropped.) -/
private def separate_insts (insts : List (term × term)) :
    IO (Except String instantiation) := ExceptT.run do
  let (realinsts, patterns) := insts.partition (fun p => is_var p.2)
  -- betacounts = itlist (fun (_,p) sof -> ... try safe_insert (length args,hop)
  --   sof with Failure _ -> (warn true "..."; sof)) patterns []
  -- (drule.ml 220-227).  `itlist` is a RIGHT fold: the LAST pattern is
  -- inserted first, so on inconsistent patterning it is the LAST pattern's
  -- arity that survives, and each rejected one emits OCaml's warning.
  -- Structural mirror of `itlist f l b = f h (itlist f t b)`.
  let rec go : List (term × term) → IO (List (Int × term))
    | [] => return []
    | p :: ps => do
        let sof ← go ps
        let (hop, args) := strip_comb p.2
        match safe_insert_int ((args.length : Int), hop) sof with
        | .ok sof' => return sof'
        | .error _ => do
            warn true "Inconsistent patterning in higher order match"
            return sof
  let betacounts ← if patterns == [] then pure ([] : List (Int × term))
                   else (go patterns : IO (List (Int × term)))
  let tyins ← liftExcept (get_type_insts realinsts [])
  let tmins := mapfilter (fun p =>
      let x' := match dest_var p.2 with
                | .ok (xn, xty) => mk_var xn (type_subst tyins xty)
                | .error _ => p.2
      if p.1 == x' then failwith "separate_insts" else .ok (p.1, x')) realinsts
  return (betacounts, tmins, tyins)
where
  safe_insert_int (n : Int × term) (l : List (Int × term)) :
      Except String (List (Int × term)) :=
    match rev_assoc n.2 l with
    | .ok z => if n.1 == z then .ok l else failwith "safe_insert"
    | .error _ => .ok (n :: l)

/-- Higher-order term matching entry point. Matches `vtm` (local constants
    `lconsts`) against `ctm`, returning an `instantiation`. IO-valued.

    Note: in the event of spillover patterns, this may return false results;
    but there's usually an implicit check outside that the match worked
    anyway. A test could be put in (see if any "env" variables are left in
    the term after abstracting out the pattern instances) but it'd be slower. -/
partial def term_match (lconsts : List term) (vtm ctm : term) :
    IO (Except String instantiation) := ExceptT.run do
  -- fixed dummy-variable name (from a single genvar), used by term_pmatch
  let gv ← liftM (genvar aty)
  let dn ← liftExcept ((dest_var gv).map Prod.fst)
  -- The higher-order resolution phase (IO: genvar/subst).
  let rec term_homatch (tyins : List (hol_type × hol_type))
      (sofar : List (term × term) × List homDatum) :
      ExceptT String IO (List (term × term)) := do
    let (insts, homs) := sofar
    match homs with
    | [] => return insts
    | (env, ctm, vtm) :: rhoms =>
      if is_var vtm then
        if ctm == vtm then term_homatch tyins (insts, rhoms)
        else do
          let (_, vty) ← liftExcept (dest_var vtm)
          let newtyins ← liftExcept (safe_insert_ty (type_of ctm, vty) tyins)
          term_homatch newtyins ((ctm, vtm) :: insts, rhoms)
      else
        let (vhop, vargs) := strip_comb vtm
        let afvs := freesl vargs
        let inst_fn := inst tyins
        /- Try the pattern-based higher-order step AND ITS CONTINUATION; on any
           failure, split `ctm`/`vtm` and re-`term_pmatch`.

           *** THE `try` MUST WRAP THE RECURSIVE CALL. *** In drule.ml 244-277
           the `try` block ends at `term_homatch lconsts tyins (ni,tl homs)`
           (269), so a failure ANYWHERE DOWNSTREAM backtracks into the
           decompose-and-re-match fallback below.  Wrapping only the computation
           of `ni` would make the first step succeed and then propagate a later
           failure, losing the backtracking that lets higher-order patterns such
           as `ADMISSIBLE_COMB` resolve by splitting an application. -/
        tryCatch (do
            -- tmins: map each free arg var to (its binding, its instance)
            let tmins ← afvs.mapM (fun a => do
              let bound ←
                match rev_assoc a env with
                | .ok b => pure b
                | .error _ =>
                  match rev_assoc a insts with
                  | .ok b => pure b
                  | .error _ => if mem a lconsts then pure a else throw "term_homatch"
              return (bound, inst_fn a))
            let pats0 := vargs.map inst_fn
            let vsub ← liftExcept (vsubst tmins)
            let pats := pats0.map vsub
            let vhop' := inst_fn vhop
            let (chop, cargs) := strip_comb ctm
            let ni ←
              if cargs == pats then
                if chop == vhop then pure insts
                else liftExcept (safe_inserta (chop, vhop) insts)
              else do
                let ginsts ← pats.mapM (fun p => do
                  let g ← if is_var p then pure p else liftM (genvar (type_of p))
                  return (g, p))
                let substFn ← (subst ginsts : IO (Except String (term → IO (Except String term))))
                let ctm' ← (substFn ctm : IO (Except String term))
                let gvs := ginsts.map Prod.fst
                let abstm ← liftExcept (list_mk_abs gvs ctm')
                let vinsts ← liftExcept (safe_inserta (abstm, vhop) insts)
                let icrhs ← liftExcept (list_mk_comb vhop' gvs)
                pure ((ctm', icrhs) :: vinsts)
            term_homatch tyins (ni, rhoms))
          (fun _ => do
            let (lc, rc) ← liftExcept (dest_comb ctm)
            let (lv, rv) ← liftExcept (dest_comb vtm)
            let pinsts_homs' ← liftExcept
              (term_pmatch lconsts dn env rv rc (insts, (env, lc, lv) :: rhoms))
            let tyins' ← liftExcept (get_type_insts pinsts_homs'.1 [])
            term_homatch tyins' pinsts_homs')
  let pinsts_homs ← liftExcept (term_pmatch lconsts dn [] vtm ctm ([], []))
  let tyins ← liftExcept (get_type_insts pinsts_homs.1 [])
  let insts ← term_homatch tyins pinsts_homs
  ExceptT.mk (separate_insts insts)

/- ---------------------------------------------------------------------- -/
/- Instantiate theorem by matching part of it to a term.                  -/
/- The GEN_PART_MATCH version renames free vars to avoid clashes.         -/
/- ---------------------------------------------------------------------- -/

/-- Collect bound-variable name pairs where `t1` and `t2` differ. -/
private partial def match_bvs (t1 t2 : term) (acc : List (String × String)) :
    List (String × String) :=
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

/-- Instantiate `th` by matching `partfn (concl th)` against `tm`. -/
def PART_MATCH (B : BoolThms) (partfn : term → Except String term) (th : thm) (tm : term) :
    IO (Except String thm) := ExceptT.run do
  let sth ← liftExcept (B.SPEC_ALL th)
  let bod := concl sth
  let pbod ← liftExcept (partfn bod)
  let lconsts := intersect (frees (concl th)) (freesl (hyp th))
  let bvms := match_bvs tm pbod []
  let abod := deep_alpha bvms bod
  let ath ← liftExcept (do EQ_MP (← ALPHA bod abod) sth)
  let insts ← (term_match lconsts (← liftExcept (partfn abod)) tm : IO (Except String instantiation))
  let fth ← liftExcept (INSTANTIATE insts ath)
  if hyp fth != hyp ath then throw "PART_MATCH: instantiated hyps"
  else
    let tm' ← liftExcept (partfn (concl fth))
    if tm' == tm then return fth
    else
      match ALPHA tm' tm with
      | .error _ => throw "PART_MATCH: Sanity check failure"
      | .ok a =>
        match ← liftM (Equal.SUBS [a] fth : IO (Except String thm)) with
        | .ok r => return r
        | .error _ => throw "PART_MATCH: Sanity check failure"

/-- Like `PART_MATCH`, but renames free variables to avoid clashes. -/
def GEN_PART_MATCH (B : BoolThms) (partfn : term → Except String term) (th : thm) (tm : term) :
    IO (Except String thm) := ExceptT.run do
  let sth ← liftExcept (B.SPEC_ALL th)
  let bod := concl sth
  let pbod ← liftExcept (partfn bod)
  let lconsts := intersect (frees (concl th)) (freesl (hyp th))
  let fvs := subtract (subtract (frees bod) (frees pbod)) lconsts
  let bvms := match_bvs tm pbod []
  let abod := deep_alpha bvms bod
  let ath ← liftExcept (do EQ_MP (← ALPHA bod abod) sth)
  let insts ← (term_match lconsts (← liftExcept (partfn abod)) tm : IO (Except String instantiation))
  let eth ← liftExcept (do INSTANTIATE insts (← B.GENL fvs ath))
  -- itlist (fun v th => snd(SPEC_VAR th)) fvs eth
  let fth ← liftExcept (itlistM (fun _ t => do return (← B.SPEC_VAR t).2) fvs eth)
  if hyp fth != hyp ath then throw "PART_MATCH: instantiated hyps"
  else
    let tm' ← liftExcept (partfn (concl fth))
    if tm' == tm then return fth
    else
      match ALPHA tm' tm with
      | .error _ => throw "PART_MATCH: Sanity check failure"
      | .ok a =>
        match ← liftM (Equal.SUBS [a] fth : IO (Except String thm)) with
        | .ok r => return r
        | .error _ => throw "PART_MATCH: Sanity check failure"

/- ---------------------------------------------------------------------- -/
/- Matching modus ponens.                                                 -/
/- ---------------------------------------------------------------------- -/

/-- Matching modus ponens: from `ith : |- !… . p ==> q` and `th : |- p'`
    (where `p'` matches `p`), derive the instantiated `|- q'`. -/
def MATCH_MP (B : BoolThms) (ith : thm) (th : thm) : IO (Except String thm) := ExceptT.run do
  -- Massage `ith` so its outer universals suit the match (OCaml `sth`).
  let sthE : Except String thm := do
    let tm := concl ith
    let (avs, bod) := strip_forall tm
    let (ant, _) ← Basics.dest_imp bod
    let (svs, pvs) := avs.partition (fun v => vfree_in v ant)
    if pvs == [] then .ok ith
    else do
      let th1 ← B.SPECL avs (← ASSUME tm)
      let th2 ← B.GENL svs (← B.DISCH ant (← B.GENL pvs (← B.UNDISCH th1)))
      B.MP (← B.DISCH tm th2) ith
  match sthE with
  | .error _ => throw "MATCH_MP: Not an implication"
  | .ok sth =>
    -- `fun th -> try MP (match_fun (concl th)) th with Failure _ ->
    --   failwith "MATCH_MP: No match"` (drule.ml 505-506): ONE `try` covers
    -- BOTH the match AND the `MP`, so either failure becomes "No match"
    -- (class #9).  The underlying PART_MATCH / MP messages must not leak.
    let mth ← tryCatch
      (ExceptT.mk (PART_MATCH B (fun t => do return (← Basics.dest_imp t).1) sth (concl th)))
      (fun _ => throw "MATCH_MP: No match")
    match B.MP mth th with
    | .ok r => return r
    | .error _ => throw "MATCH_MP: No match"

/- ---------------------------------------------------------------------- -/
/- Derived principle of definition justifying |- c x1 .. xn = t[x1,..,xn] -/
/- ---------------------------------------------------------------------- -/

/-- Define `c x1 … xn = t` (curried), returning the generalized theorem.
    Uses the bool rule `GEN`. -/
def new_definition (B : BoolThms) (tm : term) : IO (Except String thm) := ExceptT.run do
  let (avs, bod) := strip_forall tm
  let (l, r) ← liftExcept ((dest_eq bod).mapError (fun _ => "new_definition: Not an equation"))
  let (lv, largs) := strip_comb l
  let rtm ← liftExcept ((list_mk_abs largs r).mapError
              (fun _ => "new_definition: Non-variable in LHS pattern"))
  let mkEq ← (mk_eq : IO (Except String ((term × term) → Except String term)))
  let def_ ← liftExcept (mkEq (lv, rtm))
  let th1 ← (new_basic_definition def_ : IO (Except String thm))
  -- th2 = rev_itlist (fun tm th => TRANS (AP_THM th tm) (BETA_CONV (rand(concl (AP_THM th tm))))) largs th1
  let step (a : term) (th : thm) : Except String thm := do
    let ith ← AP_THM th a
    TRANS ith (← BETA_CONV (← rand (concl ith)))
  let th2 ← liftExcept (rev_itlistM step largs th1)
  let rvs := filter (fun v => !(mem v avs)) largs
  -- itlist GEN rvs (itlist GEN avs th2)
  liftExcept (do itlistM B.GEN rvs (← itlistM B.GEN avs th2))

/- ---------------------------------------------------------------------- -/
/- Useful instance of more general higher order matching.                 -/
/- ---------------------------------------------------------------------- -/

/-- Conversion doing `n` leading beta-reductions. -/
private partial def betaConvs (n : Int) : conv := fun t =>
  if n == 1 then TRY_CONV BETA_CONV t
  else (THENC (RATOR_CONV (betaConvs (n - 1))) (TRY_CONV BETA_CONV)) t

/-- `BETA_VAR v tm`: build a conversion beta-reducing free applications of `v`
    in `tm`. Fails ("unchanged") if `v` has no such applications. -/
private partial def BETA_VAR (v : term) (tm : term) : Except String conv :=
  if is_abs tm then
    match dest_abs tm with
    | .ok (bv, bod) =>
        if v == bv then failwith "unchanged"
        else do return ABS_CONV (← BETA_VAR v bod)
    | .error _ => failwith "unchanged"
  else
    let (op, args) := strip_comb tm
    if args == [] then failwith "unchanged"
    else if op == v then .ok (betaConvs (args.length : Int))
    else
      match dest_comb tm with
      | .error _ => failwith "unchanged"
      | .ok (l, r) =>
        match BETA_VAR v l with
        | .ok lconv =>
            match BETA_VAR v r with
            | .ok rconv => .ok (COMB2_CONV lconv rconv)
            | .error _  => .ok (RATOR_CONV lconv)
        | .error _ => do return RAND_CONV (← BETA_VAR v r)

/-- IO-predicate variant of `find_term`. -/
private partial def find_termM (p : term → IO Bool) (tm : term) : IO (Except String term) := do
  if ← p tm then return .ok tm
  else if is_abs tm then
    match body tm with
    | .ok bod => find_termM p bod
    | .error _ => return failwith "find_term"
  else if is_comb tm then
    match dest_comb tm with
    | .ok (l, r) =>
        match ← find_termM p l with
        | .ok found => return .ok found
        | .error _  => find_termM p r
    | .error _ => return failwith "find_term"
  else return failwith "find_term"

/-- IO-predicate variant of `find_terms`. -/
private partial def find_termsM (p : term → IO Bool) (tm : term) : IO (List term) := do
  let rec accum (tl : List term) (tm : term) : IO (List term) := do
    let tl' := if ← p tm then insert tm tl else tl
    if is_abs tm then
      match body tm with | .ok bod => accum tl' bod | .error _ => return tl'
    else if is_comb tm then
      match rator tm, rand tm with
      | .ok f, .ok x => accum (← accum tl' f) x
      | _, _ => return tl'
    else return tl'
  accum [] tm

/-- Higher-order rewriting conversion. `top` selects outermost-first search.
    Given a list of (equational) rewrite theorems, rewrites the first matching
    subterm of `tm`. Uses the bool rule `SPEC_ALL`. IO-valued. -/
def HIGHER_REWRITE_CONV (B : BoolThms) (ths : List thm) (top : Bool) (tm : term) :
    IO (Except String thm) := ExceptT.run do
  -- GINST: rename the free (non-hypothesis) variables of a theorem to genvars.
  let GINST (th : thm) : ExceptT String IO thm := do
    let fvs := subtract (frees (concl th)) (freesl (hyp th))
    let gvs ← fvs.mapM (fun v => liftM (genvar (type_of v)))
    liftExcept (do INST (← liftExcept (zip gvs fvs)) th)
  let thl ← ths.mapM (fun th => do GINST (← liftExcept (B.SPEC_ALL th)))
  let concs := thl.map concl
  let lefts ← liftExcept (concs.mapM lhs)
  let predpats ← liftExcept (lefts.mapM dest_comb)
  let (preds, pats) := unzip predpats
  let beta_fns ← liftExcept (do
    let paired ← zip preds concs
    paired.mapM (fun (p, c) => BETA_VAR p c))
  let ass_list ← liftExcept (do
    zip pats (← zip preds (← zip thl beta_fns)))
  -- build the term net keyed on patterns
  let mnet ← (do
    let rec build : List term → net term → IO (Except String (net term))
      | [], n => return .ok n
      | p :: ps, n => do
          match ← enter [] (p, p) n with
          | .ok n' => build ps n'
          | .error e => return .error e
    build pats (empty_net : net term)
    : IO (Except String (net term)))
  -- can we term_match p against t?
  let canMatch (p t : term) : IO Bool := do
    match ← term_match [] p t with | .ok _ => return true | .error _ => return false
  -- candidate patterns whose net-lookup and match succeed
  let look_fn (t : term) : IO (List term) := do
    let cands := lookup t mnet
    cands.filterM (fun p => canMatch p t)
  -- the search predicate (IO)
  let predIO (t : term) : IO Bool := do
    let lf ← look_fn t
    return !(lf.isEmpty) && free_in t tm
  let stm ←
    if top then (find_termM predIO tm : IO (Except String term))
    else do
      let ts ← (find_termsM predIO tm : IO (List term))
      match sort free_in ts with
      | s :: _ => pure s
      | []     => throw "HIGHER_REWRITE_CONV: no match"
  let lookStm ← look_fn stm
  let pat ← liftExcept (match lookStm with | p :: _ => .ok p | [] => failwith "no pattern")
  let inst1 ← (term_match [] pat stm : IO (Except String instantiation))
  let (_, tmin, _tyin) := inst1
  let (pred, thBeta) ← liftExcept (assoc pat ass_list)
  let (th, beta_fn) := thBeta
  let gv ← liftM (genvar (type_of stm))
  let sub ← (subst [(gv, stm)] : IO (Except String (term → IO (Except String term))))
  let subTm ← (sub tm : IO (Except String term))
  let abs ← liftExcept (mk_abs gv subTm)
  let inst2 ← (term_match [] pred abs : IO (Except String instantiation))
  let (_, tmin0, tyin0) := inst2
  liftExcept do
    let t0 ← INST_TYPE tyin0 th
    let t1 ← INST tmin0 t0
    let t2 ← INST tmin t1
    CONV_RULE beta_fn t2

end HolCore.Drule
