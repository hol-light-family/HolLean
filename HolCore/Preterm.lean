/- File: Preterm.lean
Preterms and pretypes; typechecking; translation to types and terms.
Original: John Harrison, University of Cambridge Computer Laboratory
Original: (c) Copyright, University of Cambridge 1998
Original: (c) Copyright, John Harrison 1998-2007
Original: (c) Copyright, Marco Maggesi 2012
Original: (c) Copyright, Vincent Aravantinos 2012
Lean4 translation by Chris Walton 2026 -/

import HolCore.Lib
import HolCore.Basics
import HolCore.Fusion
import HolCore.Printer

open HolCore.Kernel HolCore.Basics HolCore.Lib HolCore.Printer

namespace HolCore.Preterm

/- Lexer classifier `isnum` (from `charClassifiers`), applied to the first
   character of a token — matching HOL Light's `isnum` on a string, where the
   underlying `charcode` reads the leading character. -/
private def isnum (s : String) : Bool :=
  match s.toList.head? with
  | some c => charClassifiers.2.2.2.2.2.1 (String.singleton c)
  | none   => false

/- Flag to say whether to treat varstruct "\const. bod" as variable. -/
initialize ignore_constant_varstruct : IO.Ref Bool ← IO.mkRef true

/- Flags controlling the treatment of invented type variables in quotations.
It can be treated as an error, result in a warning, or neither of those. -/
initialize type_invention_warning : IO.Ref Bool ← IO.mkRef true
initialize type_invention_error : IO.Ref Bool ← IO.mkRef false

/- Implicit types or type schemes for non-constants. -/
initialize the_implicit_types : IO.Ref (List (String × hol_type)) ←
  IO.mkRef ([] : List (String × hol_type))

/- Overloading and interface mapping. -/

/-- Register `s` as an overloadable symbol with generic type `gty`; fails
    with "make_overloadable: differs from existing skeleton" on a clash. -/
def make_overloadable (s : String) (gty : hol_type) : IO (Except String Unit) := do
  let skels ← the_overload_skeletons.get
  match assoc s skels with
  | .ok existing =>
      if existing == gty then return .ok ()
      else return failwith "make_overloadable: differs from existing skeleton"
  | .error _ =>
      the_overload_skeletons.set ((s, gty) :: skels)
      return .ok ()

/-- Remove all interface mappings for the symbol `sym`. -/
def remove_interface (sym : String) : IO Unit := do
  let interface := filter (fun p => p.1 != sym) (← the_interface.get)
  the_interface.set interface

/-- Remove the single interface mapping `sym` -> `tm`. -/
def reduce_interface (sym : String) (tm : term) : IO (Except String Unit) := do
  let namty : Except String (String × hol_type) :=
    match dest_const tm with
    | .ok r    => .ok r
    | .error _ => dest_var tm
  match namty with
  | .error e  => return .error e
  | .ok namty =>
      the_interface.modify (filter (fun p => p != (sym, namty)))
      return .ok ()

/-- Map `sym` to `tm`, discarding any existing mappings for `sym`. -/
def override_interface (sym : String) (tm : term) : IO (Except String Unit) := do
  let namty : Except String (String × hol_type) :=
    match dest_const tm with
    | .ok r    => .ok r
    | .error _ => dest_var tm
  match namty with
  | .error e  => return .error e
  | .ok namty =>
      the_interface.modify (fun iface =>
        (sym, namty) :: filter (fun p => p.1 != sym) iface)
      return .ok ()

/-- Add an overloading of `sym` to `tm`, requiring `tm`'s type to be an
    instance of `sym`'s overload skeleton. -/
def overload_interface (sym : String) (tm : term) : IO (Except String Unit) := do
  let skels ← the_overload_skeletons.get
  match assoc sym skels with
  | .error _ => return failwith s!"symbol \"{sym}\" is not overloadable"
  | .ok gty =>
    let namtyE : Except String (String × hol_type) :=
      match dest_const tm with
      | .ok r    => .ok r
      | .error _ => dest_var tm
    match namtyE with
    | .error e => return .error e
    | .ok namty =>
      let (_, ty) := namty
      if !(can (type_match gty ty) []) then
        return failwith "Not an instance of type skeleton"
      else
        the_interface.modify (fun iface =>
          (sym, namty) :: filter (fun p => p != (sym, namty)) iface)
        return .ok ()

/-- Give overloadings whose instance type contains `ty` priority for
    each overloadable symbol. -/
def prioritize_overload (ty : hol_type) : IO Unit := do
  let rec findE {α : Type} (p : α → Except String Bool) : List α → Except String α
    | []     => failwith "find"
    | h :: t => do if ← p h then pure h else findE p t
  do_list (fun (s, gty) => do
    let matchesTy (t : hol_type) : Except String Bool := do
      return mem ty ((← type_match gty t []).map (·.1))
    match findE (fun (s', (_, t)) => if s' == s then matchesTy t else pure false)
                (← the_interface.get) with
    | .ok (_, (n, t)) => discard <| overload_interface s (mk_var n t)
    | .error _        => pure ())
    (← the_overload_skeletons.get)

/- Type abbreviations. -/
private initialize the_type_abbreviations : IO.Ref (List (String × hol_type)) ←
  IO.mkRef ([] : List (String × hol_type))
/-- Remove any type abbreviation named `s`. -/
def remove_type_abbrev (s : String) : IO Unit :=
  the_type_abbreviations.modify (filter (fun (s', _) => s' != s))
/-- Install `s` as an abbreviation for the type `ty`. -/
def new_type_abbrev (s : String) (ty : hol_type) : IO Unit := do
  remove_type_abbrev s
  -- OCaml `merge (<) [s,ty] ...`: structural `<` on the (name, type) pair is
  -- lexicographic by name first. Since `remove_type_abbrev s` guarantees the
  -- new name is unique, strict comparison on the name reproduces it.
  the_type_abbreviations.modify (fun l =>
    merge (fun a b => (compare a.1 b.1).isLT) [(s, ty)] l)
/-- The current list of type abbreviations. -/
def type_abbrevs : IO (List (String × hol_type)) :=
  the_type_abbreviations.get

/- Handle constant hiding. -/
private initialize theHiddenConstants : IO.Ref (List String) ←
  IO.mkRef ([] : List String)
/-- Hide the constant `c`, so it parses as a variable. -/
def hide_constant (c : String) : IO Unit :=
  theHiddenConstants.modify (fun hcs => union [c] hcs)
/-- Reveal the constant `c`, undoing `hide_constant`. -/
def unhide_constant (c : String) : IO Unit :=
  theHiddenConstants.modify (fun hcs => subtract hcs [c])
/-- Is the constant `c` currently hidden? -/
def is_hidden (c : String) : IO Bool := do
  return mem c (← theHiddenConstants.get)

/- The type of pretypes. -/
/-- The type of pretypes: user type variables, type constructor
    applications, and system (unification) type variables. -/
inductive pretype where
  | Utv   (v : String)                          -- User type variable
  | Ptycon (c : String) (args : List pretype)   -- Type constructor
  | Stv   (n : Int)                             -- System type variable
  deriving BEq, Repr, Inhabited

/- Dummy pretype for the parser to stick in before a proper typing pass. -/
/-- Dummy pretype the parser sticks in before a proper typing pass. -/
def dpty : pretype := .Ptycon "" []

/- Convert type to pretype. -/
/-- Convert a type to the corresponding pretype. -/
def pretype_of_type : hol_type → pretype
  | .Tyvar s        => .Utv s
  | .Tyapp con args => .Ptycon con (args.map pretype_of_type)

/- Preterm syntax. -/
/-- Preterm syntax: variables, constants, combinations, lambda-
    abstractions, and type constraints. -/
inductive preterm where
  | Varp   (v : String) (ty : pretype)    -- Variable           - v
  | Constp (c : String) (ty : pretype)    -- Constant           - c
  | Combp  (f : preterm) (x : preterm)    -- Combination        - f x
  | Absp   (v : preterm) (t : preterm)    -- Lambda-abstraction - \x. t
  | Typing (t : preterm) (ty : pretype)   -- Type constraint    - t : ty
  deriving BEq, Repr, Inhabited

/- Convert term to preterm. -/
/-- Convert a term to the corresponding preterm. -/
def preterm_of_term : term → preterm
  | .Var n ty   => .Varp n (pretype_of_type ty)
  | .Const n ty => .Constp n (pretype_of_type ty)
  | .Abs v bod  => .Absp (preterm_of_term v) (preterm_of_term bod)
  | .Comb l r   => .Combp (preterm_of_term l) (preterm_of_term r)

/- Main pretype->type, preterm->term and retypechecking functions. -/
private initialize tyv_num : IO.Ref Int ← IO.mkRef 0

private def new_type_var : IO pretype := do
  let n ← tyv_num.get
  tyv_num.set (n + 1)
  return .Stv n

private def pmk_cv (s : String) (pty : pretype) : IO preterm := do
  match ← get_const_type s with
  | .ok _    => return .Constp s pty
  | .error _ => return .Varp s pty

private partial def pmk_numeral (n : Rat) : preterm :=
  let num_pty := pretype.Ptycon "num" []
  let NUMERAL := preterm.Constp "NUMERAL" (.Ptycon "fun" [num_pty, num_pty])
  let BIT0    := preterm.Constp "BIT0"    (.Ptycon "fun" [num_pty, num_pty])
  let BIT1    := preterm.Constp "BIT1"    (.Ptycon "fun" [num_pty, num_pty])
  let t_0     := preterm.Constp "_0" num_pty
  let rec build (n : Rat) : preterm :=
    if n == num_0 then t_0
    else
      let m := quo_num n num_2
      let b := mod_num n num_2
      let op := if b == num_0 then BIT0 else BIT1
      .Combp op (build m)
  .Combp NUMERAL (build n)

/- Pretype substitution for a pretype resulting from translation of type. -/
private partial def pretype_subst (th : List (pretype × pretype)) (ty : pretype) : pretype :=
  match ty with
  | .Ptycon tycon args => .Ptycon tycon (args.map (pretype_subst th))
  | .Utv _             => rev_assocd ty th ty
  | _                  => panic! "pretype_subst: Unexpected form of pretype"

/- Convert type to pretype with new Stvs for all type variables. -/
private def pretype_instance (ty : hol_type) : IO pretype := do
  let gty := pretype_of_type ty
  let tyvs := (tyvars ty).map pretype_of_type
  let subs ← tyvs.mapM (fun tv => do return (← new_type_var, tv))
  return pretype_subst subs gty

/- Get a new instance of a constant's generic type modulo interface. -/
private def get_generic_type (cname : String) : IO (Except String hol_type) := do
  match filter (fun p => p.1 == cname) (← the_interface.get) with
  | [(_, (_, ty))] => return .ok ty
  | _ :: _ :: _ => do return assoc cname (← the_overload_skeletons.get)
  | [] => get_const_type cname

/- Get the implicit generic type of a variable. -/
private def get_var_type (vname : String) : IO (Except String hol_type) := do
  return assoc vname (← the_implicit_types.get)

/- Unravel unifications and apply them to a type. -/
private partial def solve (env : List (Int × pretype)) (pty : pretype) : pretype :=
  match pty with
  | .Ptycon f args => .Ptycon f (args.map (solve env))
  | .Stv i =>
    match assoc i env with
    | .ok t    => solve env t
    | .error _ => pty
  | _ => pty

/- Functions for display of preterms and pretypes, by converting them
to terms and types then re-using standard printing functions. -/
private def free_stvs (pty : pretype) : List Int :=
  let rec go : pretype → List Int
    | .Stv n        => [n]
    | .Utv _        => []
    | .Ptycon _ args => flat (args.map go)
  setify (go pty)

private partial def string_of_pretype (stvs : List Int) (pty : pretype) : IO (Except String String) := do
  let rec toTy (ns : List Int) (pty : pretype) : ExceptT String IO hol_type := do
    match pty with
    | .Stv n        => pure (mk_vartype (if mem n ns then "?" ++ toString n else "_"))
    | .Utv v        => pure (mk_vartype v)
    | .Ptycon con args =>
        let args' ← args.mapM (toTy ns)
        mk_type con args'
  let tyRes : Except String hol_type ← (toTy stvs pty).run
  match tyRes with
  | .error e => return .error e
  | .ok ty   => return .ok (← string_of_type ty)

private partial def string_of_preterm (ptm : preterm) : IO (Except String String) := do
  let rec toTm : preterm → ExceptT String IO term
    | .Varp s _     => pure (mk_var s aty)
    | .Constp s _   => do mk_mconst s (← get_const_type s)
    | .Combp l r    => do liftExcept (mk_comb (← toTm l) (← toTm r))
    | .Absp v bod   => do mk_gabs (← toTm v) (← toTm bod)
    | .Typing ptm _ => toTm ptm
  let tmRes : Except String term ← (toTm ptm).run
  match tmRes with
  | .error e => return .error e
  | .ok tm   => return .ok (← string_of_term tm)

private def string_of_ty_error (env : List (Int × pretype))
    (err : Option (preterm × pretype × pretype)) : IO (Except String String) :=
  (do
    match err with
    | none =>
        return "unify: types cannot be unified "
          ++ "(you should not see this message, please report)"
    | some (t, ty1, ty2) =>
        let ty1 := solve env ty1
        let ty2 := solve env ty2
        let sty1 ← string_of_pretype (free_stvs ty2) ty1
        let sty2 ← string_of_pretype (free_stvs ty1) ty2
        let default_msg (s : String) : String :=
          " " ++ s ++ " cannot have type " ++ sty1 ++ " and " ++ sty2
            ++ " simultaneously"
        match t with
        | .Constp s _ =>
            let cty ← string_of_type (← get_const_type s)
            return " " ++ s ++ " has type " ++ cty ++ ", "
              ++ "it cannot be used with type " ++ sty2
        | .Varp s _ => return default_msg s
        | t         => return default_msg (← string_of_preterm t)
    : ExceptT String IO String).run

/- Unification of types -/
private partial def istrivial (ptm : Option (preterm × pretype × pretype))
    (env : List (Int × pretype)) (x : Int) (ty : pretype) : ExceptT String IO Bool := do
  match ty with
  | .Stv y =>
      if y == x then return true
      else match assoc y env with
            | .ok t    => istrivial ptm env x t
            | .error _ => return false
  | .Ptycon _ args =>
      let rec anyT : List pretype → ExceptT String IO Bool
        | []        => return false
        | a :: rest => do if ← istrivial ptm env x a then return true else anyT rest
      if ← anyT args then throw (← string_of_ty_error env ptm)
      else return false
  | .Utv _ => return false

private partial def unify (ptm : Option preterm)
    (env : List (Int × pretype)) (ty1 ty2 : pretype) :
    ExceptT String IO (List (Int × pretype)) := do
  let rec go (env : List (Int × pretype)) :
      List (pretype × pretype × Option (preterm × pretype × pretype)) →
      ExceptT String IO (List (Int × pretype))
    | [] => return env
    | (ty1, ty2, ptm) :: oth => do
      if ty1 == ty2 then go env oth
      else match ty1, ty2 with
      | .Ptycon f fargs, .Ptycon g gargs =>
          if f == g && length fargs == length gargs then do
            let pairs ← liftExcept (map2 (fun x y => (x, y, ptm)) fargs gargs)
            go env (pairs ++ oth)
          else throw (← string_of_ty_error env ptm)
      | .Stv x, t =>
          match assoc x env with
          | .ok bx   => go env ((bx, t, ptm) :: oth)
          | .error _ => do
              if ← istrivial ptm env x t then go env oth
              else go ((x, t) :: env) oth
      | t, .Stv x => go env ((.Stv x, t, ptm) :: oth)
      | _, _ => throw (← string_of_ty_error env ptm)
  go env [(ty1, ty2, ptm.map (fun t => (t, ty1, ty2)))]

/- Attempt to attach a given type to a term, performing unifications. -/
private partial def typify (ty : pretype)
    (arg : preterm × List (String × pretype) × List (Int × pretype)) :
    ExceptT String IO (preterm × List (String × pretype) × List (Int × pretype)) := do
  let (ptm, venv, uenv) := arg
  -- unify `a`/`b`, returning `(result, vadds, uenv')`
  let unified (result : preterm) (vadds : List (String × pretype)) (a b : pretype) :
      ExceptT String IO (preterm × List (String × pretype) × List (Int × pretype)) := do
    return (result, vadds, ← unify (some ptm) uenv a b)
  match ptm with
    | .Varp s _ =>
      if let .ok ty' := assoc s venv then
        unified (.Varp s ty') [] ty' ty                    -- bound in venv
      else if let .ok v := num_of_string s then
        unified (pmk_numeral v) [] (.Ptycon "num" []) ty   -- numeral
      else do
        warn (s != "" && isnum s) "Non-numeral begins with a digit"
        let hidden ← is_hidden s
        let genRes : Except String hol_type ←
          if hidden then pure (.error "") else get_generic_type s
        match genRes with
        | .ok gty =>                                        -- constant with generic type
            let pty ← pretype_instance gty
            -- OCaml rebinds `ptm = Constp(s,pty)` and passes THAT to `unify`
            -- (preterm.ml 320-322), so a unify failure here reports the
            -- constant-specific "has type ... cannot be used with type ..."
            -- message via `string_of_ty_error`, not the Varp `default_msg`.
            let cptm := preterm.Constp s pty
            return (cptm, [], ← unify (some cptm) uenv pty ty)
        | .error _ =>                                       -- variable
            let varRes : Except String hol_type ← get_var_type s
            match varRes with
            | .error _  => return (.Varp s ty, [(s, ty)], uenv)
            | .ok vty   => let pty ← pretype_instance vty
                            return (.Varp s ty, [(s, ty)], ← unify (some ptm) uenv pty ty)
    | .Combp f x =>
        let ty'' ← new_type_var
        let (f', venv1, uenv1) ← typify (.Ptycon "fun" [ty'', ty]) (f, venv, uenv)
        let (x', venv2, uenv2) ← typify ty'' (x, venv1 ++ venv, uenv1)
        return (.Combp f' x', venv1 ++ venv2, uenv2)
    | .Typing tm pty =>
        typify ty (tm, venv, ← unify (some tm) uenv ty pty)
    | .Absp v bod =>
        let (ty', ty'') ←
          match ty with
          | .Ptycon "fun" [a, b] => pure (a, b)
          -- `new_type_var(),new_type_var()`: OCaml evaluates the pair right to
          -- left, so the range type gets the earlier number.
          | _                    => do
              let b ← new_type_var
              let a ← new_type_var
              pure (a, b)
        let uenv0 ← unify (some ptm) uenv (.Ptycon "fun" [ty', ty'']) ty
        let (v', venv1, uenv1) ← do
          let res ← typify ty' (v, [], uenv0)
          match res with
          | (.Constp s _, _, _) =>
              if ← ignore_constant_varstruct.get then pure (.Varp s ty', [(s, ty')], uenv0)
              else pure res
          | _ => pure res
        let (bod', venv2, uenv2) ← typify ty'' (bod, venv1 ++ venv, uenv1)
        return (.Absp v' bod', venv2, uenv2)
    | _ => throw "typify: unexpected constant at this stage"

/- Further specialize type constraints by resolving overloadings. -/
private partial def resolve_interface (ptm : preterm)
  (cont : List (Int × pretype) → ExceptT String IO α)
  (env : List (Int × pretype)) : ExceptT String IO α := do
let rec tryfind (f : (String × (String × hol_type)) → ExceptT String IO α) :
    List (String × (String × hol_type)) → ExceptT String IO α
  | []      => throw "tryfind"
  | x :: xs => tryCatch (f x) (fun _ => tryfind f xs)
match ptm with
| .Combp f x   => resolve_interface f (resolve_interface x cont) env
| .Absp v bod  => resolve_interface v (resolve_interface bod cont) env
| .Varp _ _    => cont env
| .Typing _ _  => throw "resolve_interface: unexpected Typing"
| .Constp s ty =>
    let maps := filter (fun (s', _) => s' == s) (← the_interface.get)
    if maps == [] then cont env
    else
      tryfind (fun (_, (_, gty)) => do
        let pty ← pretype_instance gty
        cont (← unify (some ptm) env pty ty)) maps

/- Hence apply throughout a preterm. -/
private partial def solve_preterm (env : List (Int × pretype)) (ptm : preterm) :
    ExceptT String IO preterm := do
  let unifies (ty' : hol_type) (ty : pretype) : ExceptT String IO Bool :=
    tryCatch (do let _ ← unify none env (← pretype_instance ty') ty; pure true)
              (fun _ => pure false)
  match ptm with
  | .Varp s ty   => return .Varp s (solve env ty)
  | .Combp f x   => return .Combp (← solve_preterm env f) (← solve_preterm env x)
  | .Absp v bod  => return .Absp (← solve_preterm env v) (← solve_preterm env bod)
  | .Typing _ _  => throw "solve_preterm: unexpected Typing"
  | .Constp s ty =>
      let tys := solve env ty
      let rec findMap : List (String × (String × hol_type)) → ExceptT String IO (Option String)
        | [] => return none
        | (s', (c', ty')) :: rest => do
            -- OCaml `s = s' && can (unify ...) ty` SHORT-CIRCUITS (preterm.ml
            -- 389): the unify probe - and the `new_type_var` calls inside
            -- `pretype_instance` - run ONLY for same-name entries.  Writing
            -- `s == s' && (← unifies ..)` would hoist the bind above the `if`,
            -- advancing the global `tyv_num` once per interface entry and so
            -- shifting every later invented `?N` label.
            if s == s' then
              if (← unifies ty' ty) then return (some c') else findMap rest
            else findMap rest
      match ← findMap (← the_interface.get) with
      | some c' => pmk_cv c' tys
      | none    => return (.Constp s tys)

/- Pretype -> type conversion. The base function returns a flag if a
system type variable was translated to real type variable. -/
private partial def type_of_pretype_base (ty : pretype) :
    ExceptT String IO (hol_type × Bool) := do
  match ty with
  | .Stv n =>
      let s := "?" ++ toString n
      return (mk_vartype s, true)
  | .Utv v =>
      return (mk_vartype v, false)
  | .Ptycon con args =>
      let results ← args.mapM type_of_pretype_base
      let (args', translated) := unzip results
      let anyTranslated := translated.foldl (· || ·) false
      let ty' ← mk_type con args'
      return (ty', anyTranslated)

/-- Convert a pretype to a type, discarding the invented-variable flag. -/
def type_of_pretype (ty : pretype) : ExceptT String IO hol_type :=
  Prod.fst <$> type_of_pretype_base ty

/- Maps preterms to terms. -/
/-- Map a preterm to a term, warning or erroring on invented type
    variables per the `type_invention_*` flags. -/
partial def term_of_preterm (ptm : preterm) : ExceptT String IO term := do
  let stvs_translated_terms ← IO.mkRef ([] : List String)
  let record (s : String) (translated : Bool) : ExceptT String IO Unit := do
    if translated && !(mem s (← stvs_translated_terms.get)) then
      stvs_translated_terms.modify (s :: ·)
  let rec worker (ptm : preterm) : ExceptT String IO term := do
    match ptm with
    | .Varp s pty =>
        let (ty, translated) ← type_of_pretype_base pty
        record s translated
        return mk_var s ty
    | .Constp s pty =>
        let (ty, translated) ← type_of_pretype_base pty
        let c ← mk_mconst s ty
        record s translated
        return c
    -- OCaml evaluates the tuple `(term_of_preterm l, term_of_preterm r)`
    -- right to left, and that order decides the order of the names in the
    -- "cannot infer type of variables" message.
    | .Combp l r  => do
        let r' ← worker r
        let l' ← worker l
        liftExcept (mk_comb l' r')
    | .Absp v bod => do
        let bod' ← worker bod
        let v' ← worker v
        mk_gabs v' bod'
    | .Typing ptm _ => worker ptm
  let tm ← worker ptm
  -- report_type_invention
  let stvs ← stvs_translated_terms.get
  if stvs != [] then
    if ← type_invention_error.get then
      throw ("typechecking error (cannot infer type of variables): "
        ++ String.intercalate ", " stvs)
    else
      warn (← type_invention_warning.get) "inventing type variables"
  return tm

/- Overall typechecker: initial typecheck plus overload resolution pass. -/
/-- Typecheck a preterm: initial type assignment via `typify`, then an
    overload-resolution pass. -/
def retypecheck (venv : List (String × pretype)) (ptm : preterm) :
    ExceptT String IO preterm := do
  let ty ← new_type_var
  let (ptm', _, env) ← tryCatch (typify ty (ptm, venv, []))
    (fun e => throw s!"typechecking error (initial type assignment):{e}")
  let env' ← tryCatch (resolve_interface ptm' pure env)
    (fun _ => throw "typechecking error (overload resolution)")
  solve_preterm env' ptm'
