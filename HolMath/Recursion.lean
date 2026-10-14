/- File: Recursion.lean
Definition by primitive recursion and other tools for inductive types.
John Harrison, University of Cambridge Computer Laboratory
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Lean4 translation by Chris Walton 2026 -/

import HolMath.Nums
import HolMath.Base

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (list_mk_conj list_mk_forall list_mk_exists)
open HolCore.Drule (instantiation)
open HolLight

namespace HolMath.Recursion

set_option maxRecDepth 4000

/- ---------------------------------------------------------------------- -/
/- Prove existence of recursive function. The inner "raw" version requires-/
/- exact correspondence with recursion theorem; "canon" requires the      -/
/- PR argument to come first in the arg list; the outer one is more       -/
/- general.                                                               -/
/- ---------------------------------------------------------------------- -/

/-- OCaml's polymorphic `compare` on pairs is lexicographic; `setify` needs it
    to deduplicate the `(axfn, fn)` pairing below. -/
private instance : Ord (term × term) where
  compare p q := match compare p.1 q.1 with | .eq => compare p.2 q.2 | c => c

/-- `f = fst o dest_const o repeat rator o rand o lhand o snd o strip_forall`
    (recursion.ml 27). -/
private def clauseArgName (t : term) : Except String String :=
  (Prod.fst oEm dest_const o repeat' rator oM rand oM lhand
    o Prod.snd o strip_forall) t

/-- recursion.ml 19-43. -/
def prove_raw_recursive_functions_exist [HolBase] (ax : thm) (tm : term) :
    ExceptT String IO thm := do
  let rawcls := conjuncts tm
  let spcls := rawcls.map (Prod.snd o strip_forall)
  let lpats ← liftExcept (spcls.mapM (strip_comb oEm lhand))
  let ufns := itlist (fun (p : term × List term) l => insert p.1 l) lpats []
  let axth ← SPEC_ALL ax
  let (exvs, axbody) := strip_exists (concl axth)
  let axcls := conjuncts axbody
  let axAlist ← liftExcept (axcls.mapM (fun t => do return (← clauseArgName t, t)))
  let findax (s : String) : Except String term := assoc s axAlist
  let raxs ← liftExcept (lpats.mapM
    (findax o Prod.fst oM dest_const o repeat' rator oM Lib.hd o Prod.snd))
  let axfns ← liftExcept (raxs.mapM
    (repeat' rator oEm lhand o Prod.snd o strip_forall))
  let pairing := setify (α := term × term) (← liftExcept (zip axfns (lpats.map (·.1))))
  let urfns := exvs.map (fun v => assocd v pairing v)
  let axtm ← liftExcept (do list_mk_exists exvs (← list_mk_conj raxs))
  let urtm ← liftExcept (list_mk_exists urfns tm)
  let insts ← term_match [] axtm urtm
  let ixth ← INSTANTIATE insts axth
  let (ixvs, ixbody) := strip_exists (concl ixth)
  let substf ← ExceptT.mk (subst (← liftExcept (zip urfns ixvs)))
  let ixtm ← ExceptT.mk (substf ixbody)
  let ixths := CONJUNCTS (← ASSUME ixtm)
  let rixths ← liftExcept (rawcls.mapM (fun t => find (aconv t o concl) ixths))
  let rixth ← ufns.foldrM SIMPLE_EXISTS (← end_itlist CONJ rixths)
  PROVE_HYP ixth (← urfns.foldrM SIMPLE_CHOOSE rixth)

/-- recursion.ml 44-54. -/
def canonize [HolBase] (t : term) : ExceptT String IO thm := do
  let (avs, bod) := strip_forall t
  let (l, r) ← liftExcept (dest_eq bod)
  let (fn, args) := strip_comb l
  let rarg ← liftExcept (hd args)
  let vargs ← liftExcept (tl args)
  let l' ← liftExcept (mk_comb fn rarg)
  let r' ← liftExcept (list_mk_abs vargs r)
  let fvs := frees rarg
  let def_ ← ASSUME (← liftExcept (list_mk_forall fvs (safe_mk_eq l' r')))
  GENL avs (← RIGHT_BETAS vargs (← SPECL fvs def_))

/-- recursion.ml 55-62. -/
def prove_canon_recursive_functions_exist [HolBase] (ax : thm) (tm : term) :
    ExceptT String IO thm := do
  let ths ← (conjuncts tm).mapM canonize
  let atm ← liftExcept (do list_mk_conj (← ths.mapM (Lib.hd o hyp)))
  let aths := CONJUNCTS (← ASSUME atm)
  let rth ← end_itlist CONJ (← (← liftExcept (map2 PROVE_HYP aths ths)).mapM id)
  let eth ← prove_raw_recursive_functions_exist ax atm
  let evs := (strip_exists (concl eth)).1
  PROVE_HYP eth (← evs.foldrM SIMPLE_CHOOSE (← evs.foldrM SIMPLE_EXISTS rth))

/-- recursion.ml 63-72. -/
def reshuffle (fn : term) (args : List term) (acc : List thm) :
    ExceptT String IO (List thm) := do
  let (vs, nonvs) := partition (fun t => is_var t) args
  let args' := nonvs ++ vs
  if args == args' then return acc
  let gvs ← args.mapM (fun a => (genvar (type_of a) : IO term))
  let gvs' ← liftExcept (do
    let z ← zip args gvs
    args'.mapM (fun a => assoc a z))
  let base ← liftExcept (funpowM gvs.length
    (fun ty => do hd (← tl (← dest_type ty).2)) (type_of fn))
  let lty ← gvs'.foldrM (fun g ty => ExceptT.mk (mk_fun_ty (type_of g) ty)) base
  let fn' ← (genvar lty : IO term)
  let def_ := safe_mk_eq fn (← liftExcept (do list_mk_abs gvs (← list_mk_comb fn' gvs')))
  return (← liftExcept (HolCore.Kernel.ASSUME def_)) :: acc

/-- recursion.ml 73-75. -/
def scrub_def [HolBase] (t : term) (th : thm) : ExceptT String IO thm := do
  let (l, r) ← liftExcept (dest_eq t)
  MP (← INST [(r, l)] (← DISCH t th)) (REFL r)

/-- recursion.ml 18-87: `prove_recursive_functions_exist ax tm`. -/
def prove_recursive_functions_exist [HolBase] (BETA_THM : thm)
    (ax : thm) (tm : term) : ExceptT String IO thm := do
  let rawcls := conjuncts tm
  let spcls := rawcls.map (Prod.snd o strip_forall)
  let lpats ← liftExcept (spcls.mapM (strip_comb oEm lhand))
  let ufns := itlist (fun (p : term × List term) l => insert p.1 l) lpats []
  let uxargs ← liftExcept (ufns.mapM (fun f => assoc f lpats))
  let trths ← (← liftExcept (zip ufns uxargs)).foldrM (fun (f, a) acc => reshuffle f a acc) []
  let tth ← ExceptT.mk (GEN_REWRITE_CONV REDEPTH_CONV (BETA_THM :: trths) tm)
  let eth ← prove_canon_recursive_functions_exist ax (← liftExcept (rand (concl tth)))
  let (evs, ebod) := strip_exists (concl eth)
  let fth ← ufns.foldrM SIMPLE_EXISTS (← EQ_MP (← SYM tth) (← ASSUME ebod))
  let gth ← (trths.map concl).foldrM scrub_def fth
  PROVE_HYP eth (← evs.foldrM SIMPLE_CHOOSE gth)

/- ---------------------------------------------------------------------- -/
/- Version that defines function(s).                                      -/
/- ---------------------------------------------------------------------- -/

/-- recursion.ml 96-98. -/
def find_redefinition [HolBase] (tm : term) (th : thm) : ExceptT String IO thm := do
  let th' ← PART_MATCH (fun t => .ok t) th tm
  let _ ← PART_MATCH (fun t => .ok t) th' (concl th)
  return th'

/-- `new_recursive_definition ax tm` (recursion.ml 94-116).  The mutable
    `the_recursive_definitions` list lives in Session, so the current list is
    passed in and the theorem to store is returned alongside;
    `new_specification` needs session state, so it is passed in too. -/
def new_recursive_definition_core [HolBase] (BETA_THM : thm)
    (new_specification : List String → thm → IO (Except String thm))
    (existing : List thm) (ax : thm) (tm : term) :
    ExceptT String IO (thm × Option thm) := do
  let rec tryRedef : List thm → IO (Option thm)
    | [] => return none
    | th :: ts => do
      match ← (find_redefinition tm th).run with
      | .ok r => return some r
      | .error _ => tryRedef ts
  match ← (tryRedef existing : IO (Option thm)) with
  | some th =>
      (warn true "Benign redefinition of recursive function" : IO Unit)
      return (th, none)
  | none =>
    let rawcls := conjuncts tm
    let spcls := rawcls.map (Prod.snd o strip_forall)
    let lpats ← liftExcept (spcls.mapM (strip_comb oEm lhand))
    let ufns := itlist (fun (p : term × List term) l => insert p.1 l) lpats []
    let fvs := rawcls.map (fun t => subtract (frees t) ufns)
    let gcls ← liftExcept (do (← map2 (fun f c => list_mk_forall f c) fvs rawcls).mapM id)
    let eth ← prove_recursive_functions_exist BETA_THM ax (← liftExcept (list_mk_conj gcls))
    let (evs, _bod) := strip_exists (concl eth)
    let names ← liftExcept (evs.mapM (Prod.fst oEm dest_var))
    let dth ← ExceptT.mk (new_specification names eth)
    let dths ← (← liftExcept (map2 SPECL fvs (CONJUNCTS dth))).mapM id
    let th ← end_itlist CONJ dths
    return (th, some th)

end HolMath.Recursion
