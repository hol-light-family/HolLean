/- ========================================================================= -/
/- Definition of record types, defining standard components for the fields.  -/
/-                                                                           -/
/- Ported from s2n-bignum (common/records.ml).                               -/
/- ========================================================================= -/
/- File: HolLibrary/Records.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/records.ml`, in the style of
  HolLibrary/Prime.lean.  records.ml is procedure code: it defines no
  theorems of its own at load time apart from `tweak` inside
  `define_record_type`.  `setupRecords` is that load: it proves `tweak` once
  and returns `define_record_type`; the other functions are plain
  definitions.

  `needs "Library/components.ml"` (records.ml 7): the components.ml bundle
  comes in as `C`.  The state `the_record_types` (records.ml 31) and the
  `add_..._thms` functions of components.ml live in SessionLibrary and come
  in through `RecordsDeps`.
-/

import HolMath
import HolLibrary.Components

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST
open HolCore.Equal (ioconv lhs lhand)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)
open HolCore.Parser (lexcode)
open HolCore.Bool (list_mk_forall)
open HolLight HolLight.Syntax

namespace HolLibrary.Records

/-- The type of `the_record_types` (records.ml 31-32): for each record type
    name, its fields and the `(induction, recursion, components)` theorems. -/
abbrev RecordTypes := List (String × (List (String × hol_type) × (thm × thm × thm)))

/-- What records.ml uses from the core library and components.ml. -/
structure RecordsDeps where
  define_type_raw : List (hol_type × List (String × List hol_type)) → ExceptT String IO (thm × thm)
  prove_recursive_functions_exist : thm → term → ExceptT String IO thm
  new_specification : List String → thm → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  /-- `the_record_types` (records.ml 31). -/
  the_record_types : IO.Ref RecordTypes
  -- components.ml's theorem lists
  add_component_read_write_thms : List thm → IO Unit
  add_valid_component_thms : List thm → IO Unit
  add_weakly_valid_component_thms : List thm → IO Unit
  add_strongly_valid_component_thms : List thm → IO Unit
  add_extensionally_valid_component_thms : List thm → IO Unit
  add_component_orthogonality_thms : List thm → IO Unit
  -- components.ml's theorems
  C : HolLibrary.Components.Components

private def perrString : HolCore.Parser.PErr → String
  | .noparse  => "Noparse"
  | .fail msg => msg

/-- `prove(tm, tac)` on a term. -/
private def proveT [HolBase] (tm : term) (tac : tactic) : ExceptT String IO thm :=
  ExceptT.mk (HolCore.Tactics.prove HolBase.B tm tac)

open HolCore.Parser in
/-- `parse_record_specification s` (records.ml 9-29): read
    `"tyname = { f1: ty1; ...; fn: tyn }"`.  As in ind_types.ml's
    `parse_inductive_type_specification`, `ptype` calls `type_of_pretype`,
    which is IO here, so the parsers are in `ParserM`.  OCaml's `raise
    Noparse` is the failure "Noparse". -/
def parse_record_specification (s : String) :
    ExceptT String IO (String × List (String × hol_type)) := do
  let ptype : ParserM hol_type := fun c src => do
    match parse_pretype c src with
    | .error e => return .error e
    | .ok (pty, rst) =>
      match ← (HolCore.Preterm.type_of_pretype pty).run with
      | .error m => return .error (.fail m)
      | .ok ty => return .ok (ty, rst)
  let recordelement : ParserM (String × hol_type) := fun c src =>
    match src with
    | .Ident t :: .Resword ":" :: rst => do
        match ← ptype c rst with
        | .error e => return .error e
        | .ok (ty, ors) => return .ok ((t, ty), ors)
    | _ => return .error .noparse
  let recordelements :=
    plistofM recordelement (liftP (pa (lexcode.Resword ";"))) "';' or '}'"
  let recspec : ParserM (List (String × hol_type)) :=
    pmapM (pseqM (pseqM (liftP (pa (lexcode.Resword "{"))) recordelements)
                 (liftP (pa (lexcode.Resword "}"))))
      (fun ((_, s), _) => s)
  let c ← mkCtx
  match lex c (explode s) with
  | .error e => throw (perrString e)
  | .ok (.Ident tyname :: .Ident "=" :: rst) =>
    match ← recspec c rst with
    | .error e => throw (perrString e)
    | .ok (rs, er) =>
      if er != [] then throw "Stuff after record spec"
      else return (tyname, rs)
  | .ok _ => throw "Noparse"

/-- `define_record_type` (records.ml 34-74): `tweak` is proved once, here;
    the result is the function. -/
@[nospecialize]
def setupRecords [HolBase] (D : RecordsDeps) :
    ExceptT String IO (String → ExceptT String IO (thm × thm × thm)) := do
  let { EXISTS_COMPONENT, read, write, .. } := D.C
  let mkEq ← ExceptT.mk mk_eq
  let tweak := MATCH_MP (← prove
   r"(?r. P r) /\ (?w. Q w) ==> ?c. P(read c) /\ Q(write c)"
   (REWRITE_TAC [EXISTS_COMPONENT, read, write] THEN D.MESON_TAC []))
  let define_record_type (s : String) : ExceptT String IO (thm × thm × thm) := do
    let (tyname, fields) ← parse_record_specification s
    match assoc tyname (← D.the_record_types.get) with
    | .ok (ofields, othms) =>
      if ofields == fields then do
        monadLift (warn true "Benign redefinition of record type")
        return othms
      else throw ("define_record_type: type " ++ tyname ++
                  " already defined with different fields")
    | .error _ => pure ()
    let tyname_rec := tyname ++ "_RECORD"
    let (ith, rth) ←
      D.define_type_raw [(mk_vartype tyname, [(tyname_rec, fields.map Prod.snd)])]
    let (_f, ebod) ← liftExcept (dest_forall (concl rth))
    let (_fn, abod) ← liftExcept (dest_exists ebod)
    let (avs, eqn) := strip_forall abod
    let left ← liftExcept (do rand (← lhand eqn))
    let leftys ← ExceptT.mk (mk_fun_ty (type_of left) (type_of left))
    let fnms := fields.map Prod.fst
    let defs ← (← liftExcept (map2 (fun fnm v => (fnm, v)) fnms avs)).mapM
      (fun (fnm, v) => do
        let (vn, vty) ← liftExcept (dest_var v)
        let v' := mk_var (vn ++ "'") vty
        let right ← ExceptT.mk ((← ExceptT.mk (subst [(v', v)])) left)
        let wfn := mk_var "writer" (← ExceptT.mk (mk_fun_ty (type_of v) leftys))
        let wdef ← liftExcept (do mkEq (← mk_comb (← mk_comb wfn v') left, right))
        let wcdef ← liftExcept (list_mk_forall (v' :: avs) wdef)
        let wethm ← D.prove_recursive_functions_exist rth wcdef
        let rfn := mk_var "reader" (← ExceptT.mk (mk_fun_ty (type_of left) (type_of v)))
        let rdef ← liftExcept (do mkEq (← mk_comb rfn left, v))
        let rcdef ← liftExcept (list_mk_forall avs rdef)
        let rethm ← D.prove_recursive_functions_exist rth rcdef
        D.new_specification [fnm] (← tweak (← CONJ rethm wethm)))
    let result := (ith, rth, ← end_itlist CONJ defs)
    D.the_record_types.set ((tyname, (fields, result)) :: (← D.the_record_types.get))
    return result
  return define_record_type

/- ------------------------------------------------------------------------- -/
/- Get the components out of a record definition                             -/
/- ------------------------------------------------------------------------- -/

/-- `get_record_components cth` (records.ml 80-84). -/
def get_record_components (cth : thm) : Except String (List term) := do
  let cjs := conjuncts (concl cth)
  let n : Int := cjs.length / 2
  let rcjs ← (upto 0 (n - 1)).mapM (fun i => el (2 * i).toNat cjs)
  rcjs.mapM (fun c => do lhand (← lhand (strip_forall c).2))

/- ------------------------------------------------------------------------- -/
/- Construct "read and write same component" theorems for all fields.        -/
/- ------------------------------------------------------------------------- -/

/-- `record_read_write_thms (ith,cth)` (records.ml 90-97). -/
def record_read_write_thms [HolBase] (ith cth : thm) : ExceptT String IO (List thm) := do
  let pat ← q r"!(y:B) (s:A). read c (write c y s) = y"
  let ctm ← q "c:(A,B)component"
  let rule (tm : term) : ExceptT String IO thm := do
    proveT (← liftExcept (Drule.instantiate (← term_match [] ctm tm) pat))
      (REPEAT (MATCH_MP_TAC ith ORELSE GEN_TAC) THEN
       REWRITE_TAC [cth] THEN HolCore.Tactics.NO_TAC)
  (← liftExcept (get_record_components cth)).mapM rule

/- ------------------------------------------------------------------------- -/
/- Construct "valid component" for all fields.                               -/
/- ------------------------------------------------------------------------- -/

/-- `record_strongly_valid_component_thms (ith,cth)` (records.ml 103-110). -/
def record_strongly_valid_component_thms [HolBase] (C : HolLibrary.Components.Components)
    (ith cth : thm) : ExceptT String IO (List thm) := do
  let rule (tm : term) : ExceptT String IO thm := do
    proveT (← ExceptT.mk (list_mk_icomb "strongly_valid_component" [tm]))
      (GEN_REWRITE_TAC id [C.strongly_valid_component] THEN
       REPEAT CONJ_TAC THEN
       REPEAT (MATCH_MP_TAC ith ORELSE GEN_TAC) THEN
       REWRITE_TAC [cth] THEN HolCore.Tactics.NO_TAC)
  (← liftExcept (get_record_components cth)).mapM rule

/-- `record_valid_component_thms (ith,cth)` (records.ml 112-114). -/
def record_valid_component_thms [HolBase] (C : HolLibrary.Components.Components)
    (ith cth : thm) : ExceptT String IO (List thm) := do
  (← record_strongly_valid_component_thms C ith cth).mapM
    (MATCH_MP C.STRONGLY_VALID_IMP_VALID_COMPONENT)

/-- `record_extensionally_valid_component_thms (ith,cth)` (records.ml 116-118). -/
def record_extensionally_valid_component_thms [HolBase] (C : HolLibrary.Components.Components)
    (ith cth : thm) : ExceptT String IO (List thm) := do
  (← record_strongly_valid_component_thms C ith cth).mapM
    (MATCH_MP C.STRONGLY_VALID_IMP_EXTENSIONALLY_VALID_COMPONENT)

/-- `record_weakly_valid_component_thms (ith,cth)` (records.ml 120-122). -/
def record_weakly_valid_component_thms [HolBase] (C : HolLibrary.Components.Components)
    (ith cth : thm) : ExceptT String IO (List thm) := do
  (← record_valid_component_thms C ith cth).mapM
    (MATCH_MP C.VALID_IMP_WEAKLY_VALID_COMPONENT)

/- ------------------------------------------------------------------------- -/
/- Create orthogonality theorems for all distinct pairs.                     -/
/- ------------------------------------------------------------------------- -/

/-- `record_orthogonality_thms (ith,cth)` (records.ml 128-138). -/
def record_orthogonality_thms [HolBase] (C : HolLibrary.Components.Components)
    (ith cth : thm) : ExceptT String IO (List thm) := do
  let cmps ← liftExcept (get_record_components cth)
  let dps := (allpairs (fun a b => (a, b)) cmps cmps).filter (fun (a, b) => a != b)
  let cjs ← dps.mapM (fun (a, b) =>
    ExceptT.mk (list_mk_icomb "orthogonal_components" [a, b]))
  let tac :=
    REWRITE_TAC [C.orthogonal_components] THEN
    REPEAT (CONJ_TAC ORELSE MATCH_MP_TAC ith ORELSE GEN_TAC) THEN
    REWRITE_TAC [cth]
  cjs.mapM (fun tm => proveT tm tac)

/- ------------------------------------------------------------------------- -/
/- Combined function that does the definition and adds all the theorems.     -/
/- ------------------------------------------------------------------------- -/

/-- `define_auto_record_type def` (records.ml 144-155). -/
def define_auto_record_type [HolBase] (D : RecordsDeps)
    (define_record_type : String → ExceptT String IO (thm × thm × thm))
    (def_ : String) : ExceptT String IO (thm × thm × thm) := do
  let (ith, rth, cth) ← define_record_type def_
  D.add_component_read_write_thms (← record_read_write_thms ith cth)
  D.add_strongly_valid_component_thms
    (← record_strongly_valid_component_thms D.C ith cth)
  D.add_valid_component_thms (← record_valid_component_thms D.C ith cth)
  D.add_extensionally_valid_component_thms
    (← record_extensionally_valid_component_thms D.C ith cth)
  D.add_weakly_valid_component_thms
    (← record_weakly_valid_component_thms D.C ith cth)
  D.add_component_orthogonality_thms (← record_orthogonality_thms D.C ith cth)
  return (ith, rth, cth)

end HolLibrary.Records
