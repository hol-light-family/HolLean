/- File: Fusion.lean
Complete HOL kernel of types, terms, and theorems.
John Harrison, University of Cambridge Computer Laboratory
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Lean4 translation by Chris Walton 2026
-/

import HolCore.Lib
open HolCore.Lib

namespace HolCore.Kernel

/- This is the implementation of those primitives. -/

/- ---------------------------------------------------------------------- -/
/- The types of HOL types, terms, and theorems.                           -/
/- ---------------------------------------------------------------------- -/

/-- HOL types: type variables and (applied) type constructors. -/
inductive hol_type where
  | Tyvar (v : String)
  | Tyapp (v : String) (args : List hol_type)
  deriving Ord, Repr, Inhabited, Hashable

/- Equality of types and terms.  OCaml's `compare` and `orda`'s `tm1 == tm2`
   (fusion.ml 442) stop at once when both sides are the same object; a derived
   `BEq` would walk the whole structure every time.  Each node first asks
   `withPtrEqDecEq` (Lean core, safe) whether the two sides are the same
   object.  The answer is the same relation as structural equality: the
   shortcut can only say "equal" for values that are equal, and the type
   checker verifies that. -/
mutual
/-- Decidable equality on types, with the same-object shortcut at each node. -/
def hol_type.decEq (a b : hol_type) : Decidable (a = b) :=
  withPtrEqDecEq a b fun _ =>
    match a, b with
    | .Tyvar x, .Tyvar y =>
      if h : x = y then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
    | .Tyapp x l1, .Tyapp y l2 =>
      if h : x = y then
        match hol_type.decEqList l1 l2 with
        | isTrue h2 => isTrue (by subst h; subst h2; rfl)
        | isFalse h2 => isFalse (fun e => by cases e; exact h2 rfl)
      else isFalse (fun e => by cases e; exact h rfl)
    | .Tyvar _, .Tyapp _ _ => isFalse (fun e => by cases e)
    | .Tyapp _ _, .Tyvar _ => isFalse (fun e => by cases e)
/-- `hol_type.decEq` on argument lists. -/
def hol_type.decEqList (l1 l2 : List hol_type) : Decidable (l1 = l2) :=
  match l1, l2 with
  | [], [] => isTrue rfl
  | a :: as, b :: bs =>
    match hol_type.decEq a b with
    | isTrue h1 =>
      match hol_type.decEqList as bs with
      | isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h2 => isFalse (fun e => by cases e; exact h2 rfl)
    | isFalse h1 => isFalse (fun e => by cases e; exact h1 rfl)
  | [], _ :: _ => isFalse (fun e => by cases e)
  | _ :: _, [] => isFalse (fun e => by cases e)
end

instance : DecidableEq hol_type := hol_type.decEq

/-- HOL terms: variables, constants, applications, abstractions. -/
inductive term where
  | Var (v : String) (t : hol_type)
  | Const (c : String) (t : hol_type)
  | Comb (t1 : term) (t2 : term)
  | Abs (t1 : term) (t2 : term)
  deriving Ord, Repr, Inhabited, Hashable

/-- Decidable equality on terms, with the same-object shortcut at each node
    (see `hol_type.decEq`). -/
def term.decEq (a b : term) : Decidable (a = b) :=
  withPtrEqDecEq a b fun _ =>
    match a, b with
    | .Var x t, .Var y u =>
      if h : x = y then
        if h2 : t = u then isTrue (by subst h; subst h2; rfl)
        else isFalse (fun e => by cases e; exact h2 rfl)
      else isFalse (fun e => by cases e; exact h rfl)
    | .Const x t, .Const y u =>
      if h : x = y then
        if h2 : t = u then isTrue (by subst h; subst h2; rfl)
        else isFalse (fun e => by cases e; exact h2 rfl)
      else isFalse (fun e => by cases e; exact h rfl)
    | .Comb f x, .Comb g y =>
      match term.decEq f g with
      | isTrue h1 =>
        match term.decEq x y with
        | isTrue h2 => isTrue (by subst h1; subst h2; rfl)
        | isFalse h2 => isFalse (fun e => by cases e; exact h2 rfl)
      | isFalse h1 => isFalse (fun e => by cases e; exact h1 rfl)
    | .Abs v x, .Abs w y =>
      match term.decEq v w with
      | isTrue h1 =>
        match term.decEq x y with
        | isTrue h2 => isTrue (by subst h1; subst h2; rfl)
        | isFalse h2 => isFalse (fun e => by cases e; exact h2 rfl)
      | isFalse h1 => isFalse (fun e => by cases e; exact h1 rfl)
    | .Var _ _, .Const _ _ | .Var _ _, .Comb _ _ | .Var _ _, .Abs _ _
    | .Const _ _, .Var _ _ | .Const _ _, .Comb _ _ | .Const _ _, .Abs _ _
    | .Comb _ _, .Var _ _ | .Comb _ _, .Const _ _ | .Comb _ _, .Abs _ _
    | .Abs _ _, .Var _ _ | .Abs _ _, .Const _ _ | .Abs _ _, .Comb _ _ =>
      isFalse (fun e => by cases e)

instance : DecidableEq term := term.decEq

/-- A theorem is a sequent `hyps ⊢ concl`. The constructor `mk` and fields are
    `private`, so the ONLY way to obtain a `thm` outside this file is via the
    exported inference rules. -/
structure thm where
  private mk ::
    private hyps : List term
    private concl : term
  deriving Repr, BEq, Ord

/- ---------------------------------------------------------------------- -/
/- Type constants.                                                        -/
/- ---------------------------------------------------------------------- -/

/-- List of current type constants with their arities.

    Initially we just have the boolean type and the function space
    constructor. Later on we add as primitive the type of individuals.
    All other new types result from definitional extension. -/
private initialize theTypeConstants : IO.Ref (List (String × Int)) ←
  IO.mkRef [("bool", 0), ("fun", 2)]

/-- Return all the defined types. -/
def types : IO (List (String × Int)) := theTypeConstants.get

/-- Lookup function for type constants. Returns arity if it succeeds. -/
def get_type_arity (s : String) : IO (Except String Int) := do
  let tbl ← theTypeConstants.get
  return assoc s tbl

/-- Declare a new type. -/
def new_type (name : String) (arity : Int) : IO (Except String Unit) := do
  let tbl ← theTypeConstants.get
  if tbl.any (fun (n, _) => n == name) then
    return failwith s!"new_type: type {name} has already been declared"
  else
    theTypeConstants.set ((name, arity) :: tbl)
    return .ok ()

/- ---------------------------------------------------------------------- -/
/- Basic type constructors.                                               -/
/- ---------------------------------------------------------------------- -/

/-- Construct a type from a type operator name and argument list. -/
def mk_type (tyop : String) (args : List hol_type) : IO (Except String hol_type) := do
  match ← get_type_arity tyop with
  | .error _ =>
      return failwith s!"mk_type: type {tyop} has not been defined"
  | .ok arity =>
      if arity == (length args : Int) then
        return .ok (.Tyapp tyop args)
      else
        return failwith s!"mk_type: wrong number of arguments to {tyop}"

/-- Construct a type variable. -/
def mk_vartype (v :String) : hol_type := .Tyvar v

/- ---------------------------------------------------------------------- -/
/- Basic type destructors.                                                -/
/- ---------------------------------------------------------------------- -/

/-- Break apart a type constructor into its name and arguments. -/
def dest_type : hol_type → Except String (String × List hol_type)
  | .Tyapp v args => .ok (v, args)
  | .Tyvar _ => failwith "dest_type: type variable not a constructor"

/-- Break apart a type variable, returning its name. -/
def dest_vartype : hol_type → Except String String
  | .Tyapp _ _ => failwith "dest_vartype: type constructor not a variable"
  | .Tyvar v => .ok v

/- ---------------------------------------------------------------------- -/
/- Basic type discriminators.                                             -/
/- ---------------------------------------------------------------------- -/

/-- Is this a type constructor application? -/
def is_type := can dest_type
/-- Is this a type variable? -/
def is_vartype := can dest_vartype

/- ---------------------------------------------------------------------- -/
/- Return the type variables in a type and in a list of types.            -/
/- ---------------------------------------------------------------------- -/

/-- Return the type variables in a type. -/
def tyvars : hol_type → List hol_type
  | .Tyapp _ args => args.foldr (fun a acc => union (tyvars a) acc) []
  | .Tyvar v => [.Tyvar v]

/-- Substitute types for type variables.
    NB: non-variables in subst list are just ignored (a check would be
    repeated many times), as are repetitions (first possibility is taken). -/
def type_subst (i : List (hol_type × hol_type)) : hol_type → hol_type
  | .Tyapp tycon args => .Tyapp tycon (args.map (type_subst i))
  | ty => rev_assocd ty i ty

/-- The boolean type. -/
def bool_ty := hol_type.Tyapp "bool" []
/-- The generic type variable `A`. -/
def aty := hol_type.Tyvar "A"

/- ---------------------------------------------------------------------- -/
/- Term constants.                                                        -/
/- ---------------------------------------------------------------------- -/

/-- List of term constants and their types.

    We begin with just equality (over all types). Later, the Hilbert choice
    operator is added. All other new constants are defined. -/
private initialize theTermConstants : IO.Ref (List (String × hol_type)) ←
  IO.mkRef [("=", .Tyapp "fun" [aty, .Tyapp "fun" [aty, bool_ty]])]

/-- Return all the defined constants with generic types. -/
def constants : IO (List (String × hol_type)) := theTermConstants.get

/-- Gets type of constant if it succeeds. -/
def get_const_type (s : String) : IO (Except String hol_type) := do
  let tbl ← theTermConstants.get
  return assoc s tbl

/-- Declare a new constant. -/
def new_constant (name : String) (ty : hol_type) : IO (Except String Unit) := do
  match ← get_const_type name with
  | .ok _ =>
      return failwith s!"new_constant: constant {name} has already been declared"
  | .error _ => do
      theTermConstants.modify (fun tbl => (name, ty) :: tbl)
      return .ok ()

/- ---------------------------------------------------------------------- -/
/- Type of a term, and primitive term discriminators.                     -/
/- ---------------------------------------------------------------------- -/

/-- Finds the type of a term (assumes it is well-typed). -/
def type_of (tm : term) : hol_type :=
  match tm with
  | .Var _ ty   => ty
  | .Const _ ty => ty
  | .Comb s _ =>
      match type_of s with
      | .Tyapp "fun" [_, rty] => rty
      | _ => panic! "type_of: Comb of non-function"
  | .Abs (.Var _ ty) t => .Tyapp "fun" [ty, type_of t]
  | .Abs _ _ => panic! "type_of: Abs with non-variable bound var"

/- ---------------------------------------------------------------------- -/
/- Primitive discriminators.                                              -/
/- ---------------------------------------------------------------------- -/

/-- Is this a variable? -/
def is_var : term → Bool
  | .Var _ _ => true
  | _ => false
/-- Is this a constant? -/
def is_const : term → Bool
  | .Const _ _ => true
  | _ => false
/-- Is this an abstraction? -/
def is_abs : term → Bool
  | .Abs _ _ => true
  | _ => false
/-- Is this a combination (application)? -/
def is_comb : term → Bool
  | .Comb _ _ => true
  | _ => false

/- ---------------------------------------------------------------------- -/
/- Primitive constructors.                                                -/
/- ---------------------------------------------------------------------- -/

/-- Construct a variable term. -/
def mk_var v t := term.Var v t

/-- Construct a constant, instantiating its generic type. -/
def mk_const (name : String) (theta : List (hol_type × hol_type)) :
      IO (Except String term) := do
  match ← get_const_type name with
  | .error _ => return failwith "mk_const: not a constant name"
  | .ok uty  => return .ok (.Const name (type_subst theta uty))

/-- Construct an abstraction `\bvar. bod`. -/
def mk_abs (bvar : term) (bod : term) : Except String term :=
  match bvar with
  | .Var _ _ => .ok (term.Abs bvar bod)
  | _ => failwith "mk_abs: not a variable"

/-- Construct an application `f a`, checking types agree. -/
def mk_comb (f a : term) : Except String term :=
  match type_of f with
  | .Tyapp "fun" [ty, _] =>
      if ty == type_of a then pure (.Comb f a)
      else failwith "mk_comb: types do not agree"
  | _ => failwith "mk_comb: types do not agree"

/- ---------------------------------------------------------------------- -/
/- Primitive destructors.                                                 -/
/- ---------------------------------------------------------------------- -/

/-- Break apart a variable into its name and type. -/
def dest_var : term → Except String (String × hol_type)
| .Var s ty => .ok (s, ty)
| _ => failwith "dest_var: not a variable"
/-- Break apart a constant into its name and type. -/
def dest_const : term → Except String (String × hol_type)
| .Const s ty => .ok (s, ty)
| _ => failwith "dest_const: not a constant"
/-- Break apart an application into function and argument. -/
def dest_comb : term → Except String (term × term)
| .Comb f x => .ok (f, x)
| _ => failwith "dest_comb: not a combination"
/-- Break apart an abstraction into bound variable and body. -/
def dest_abs : term → Except String (term × term)
| .Abs v b => .ok (v, b)
| _ => failwith "dest_abs: not an abstraction"

/- ---------------------------------------------------------------------- -/
/- Finds the variables free in a term (list of terms).                    -/
/- ---------------------------------------------------------------------- -/

/-- Finds the variables free in a term. -/
def frees (tm:term) : List term :=
  match tm with
  | .Var _ _ => [tm]
  | .Const _ _ => []
  | .Abs bv bod => subtract (frees bod) [bv]
  | .Comb s t => union (frees s) (frees t)
/-- Finds the variables free in a list of terms. -/
def freesl (tml : List term) := itlist (union o frees) tml []

/-- Whether all free variables in a term appear in a list. -/
def freesin (acc : List term) (tm : term) : Bool :=
  match tm with
  | .Var _ _ => mem tm acc
  | .Const _ _ => true
  | .Abs bv bod => freesin (bv::acc) bod
  | .Comb s t => freesin acc s && freesin acc t

/-- Whether a variable (or constant in fact) is free in a term. -/
def vfree_in (v : term) (tm : term) : Bool :=
  match tm with
  | .Abs bv bod => v != bv && vfree_in v bod
  | .Comb s t => vfree_in v s || vfree_in v t
  | _ => tm == v

/-- Finds the type variables (free) in a term. -/
def type_vars_in_term : term → List hol_type
  | .Var _ ty => tyvars ty
  | .Const _ ty => tyvars ty
  | .Comb s t => union (type_vars_in_term s) (type_vars_in_term t)
  | .Abs (.Var _ ty) t => union (tyvars ty) (type_vars_in_term t)
  | .Abs _ t => type_vars_in_term t  -- unreachable for well-formed terms

/- ---------------------------------------------------------------------- -/
/- Variant renaming, and the substitution / instantiation primitives.     -/
/- ---------------------------------------------------------------------- -/

/-- Rename a variable (appending primes) to avoid clashing with a term list.
    For name-carrying syntax, we need this early. -/
partial def variant (avoid : List term) (v : term) : Except String term :=
  if !(exists' (fun t => vfree_in v t) avoid) then pure v
  else
    match v with
    | .Var s ty => variant avoid (.Var (s ++ "'") ty)
    | _ => failwith "variant: not a variable"

/-- Substitution primitive (substitution for variables only!). -/
partial def vsubst (theta : List (term × term)) : Except String (term → term) :=
  let rec vsubst' (ilist : List (term × term)) (tm : term) : term :=
    match tm with
    | .Var _ _ => rev_assocd tm ilist tm
    | .Const _ _ => tm
    | .Comb s t =>
        let s' := vsubst' ilist s
        let t' := vsubst' ilist t
        if s' == s && t' == t then tm else .Comb s' t'
    | .Abs v s =>
        let ilist' := filter (fun (_, x) => x != v) ilist
        if ilist' == [] then tm
        else
          let s' := vsubst' ilist' s
          let captures := exists' (fun (t, x) => vfree_in v t && vfree_in x s) ilist'
          if s' == s then tm
          else if !captures then .Abs v s'
          else match variant [s'] v with
                | .ok v' => .Abs v' (vsubst' ((v', v) :: ilist') s)
                | .error _ => .Abs v s' -- unreachable
  let wellTyped : term × term → Bool
    | (t, .Var _ y) => type_of t == y
    | _             => false
  if theta == [] then .ok id
  else if forall' wellTyped theta then .ok (vsubst' theta)
  else failwith "vsubst: Bad substitution list"

/-- Result of type instantiation: either a value, a hard failure, or a variable
    capture clash to be resolved by renaming. -/
inductive InstErr where
  | fail  (msg : String)
  | clash (tm : term)
abbrev InstResult (α : Type) := Except InstErr α

/-- Type instantiation primitive. -/
partial def inst (tyin : List (hol_type × hol_type)) (tm : term) : term :=
  let rec inst' (env : List (term × term)) (tm : term) : InstResult term :=
    match tm with
    | .Var n ty =>
        let ty' := type_subst tyin ty
        let tm' := if ty' == ty then tm else .Var n ty'
        if rev_assocd tm' env tm == tm then .ok tm'
        else .error (.clash tm')
    | .Const c ty =>
        let ty' := type_subst tyin ty
        .ok (if ty' == ty then tm else .Const c ty')
    | .Comb f x => do
        let f' ← inst' env f
        let x' ← inst' env x
        if f' == f && x' == x then .ok tm else .ok (.Comb f' x')
    | .Abs y t => do
        let y' ← inst' [] y
        let env' := (y, y') :: env
        match inst' env' t with
        | .ok t' => .ok (if y' == y && t' == t then tm else .Abs y' t')
        | .error (.fail msg) => .error (.fail msg)
        | .error (.clash w') =>
            if w' != y' then .error (.clash w')
            else
              match (frees t).mapM (inst' []) with
              | .error e => .error e
              | .ok ifrees =>
                match variant ifrees y' with
                | .error _ => .error (.fail "inst: variant failed")
                | .ok y'' =>
                  match dest_var y'', dest_var y with
                  | .ok (nm, _), .ok (_, ty0) =>
                      let z := term.Var nm ty0
                      match vsubst [(z, y)] with
                      | .ok sub => inst' env (.Abs z (sub t))
                      | .error _ => .error (.fail "inst: vsubst failed")
                  | _, _ => .error (.fail "inst: dest_var failed")
  if tyin == [] then tm
  else
    match inst' [] tm with
    | .ok t              => t
    | .error (.fail msg) => panic! s!"inst: {msg}"
    | .error (.clash _)  => panic! "inst: unexpected clash"

/- ---------------------------------------------------------------------- -/
/- A few bits of general derived syntax.                                  -/
/- ---------------------------------------------------------------------- -/

/-- The operator (function) of a combination. -/
def rator (tm : term) : Except String term :=
  match tm with
  | .Comb l _ => .ok l
  | _ => failwith "rator: Not a combination"
/-- The operand (argument) of a combination. -/
def rand (tm : term) : Except String term :=
  match tm with
  | .Comb _ r => .ok r
  | _ => failwith "rand: Not a combination"

/- ---------------------------------------------------------------------- -/
/- Syntax operations for equations.                                       -/
/- ---------------------------------------------------------------------- -/

/-- Build an equation `l = r` (assuming `l`, `r` well-typed and same type). -/
def safe_mk_eq (l : term) (r : term) : term :=
  let ty := type_of l
  let inner := .Tyapp "fun" [ty, bool_ty]
  let outer := .Tyapp "fun" [ty, inner]
  let equalc := .Const "=" outer
  .Comb (.Comb equalc l) r
/-- Break apart an equation into its two sides. -/
def dest_eq (tm: term) : Except String (term × term) :=
  match tm with
  | .Comb (.Comb (.Const "=" _) l) r => .ok (l, r)
  | _ => failwith "dest_eq"

/- ---------------------------------------------------------------------- -/
/- Useful to have term union modulo alpha-conversion for assumption lists.-/
/- ---------------------------------------------------------------------- -/

/-- Order two variables in the context of a bound-variable environment. -/
def ordav (env : List (term × term)) (x1 x2 : term) : Ordering :=
  match env with
  | [] => if x1 == x2 then .eq else compare x1 x2
  | (t1, t2) :: oenv =>
      if x1 == t1 then
        if x2 == t2 then .eq else .lt
      else if x2 == t2 then .gt
      else ordav oenv x1 x2
/-- Alpha-respecting order on terms, relative to a bound-variable environment. -/
def orda (env : List (term × term)) (tm1 tm2 : term) : Ordering :=
  if tm1 == tm2 && forall' (fun p => p.1 == p.2) env then .eq
  else
    match tm1, tm2 with
    | .Var _ _, .Var _ _ => ordav env tm1 tm2
    | .Const _ _, .Const _ _ => if tm1 == tm2 then .eq else compare tm1 tm2
    | .Comb s1 t1, .Comb s2 t2 =>
        let c := orda env s1 s2
        if c != .eq then c else orda env t1 t2
    | .Abs (x1@(.Var _ ty1)) t1, .Abs (x2@(.Var _ ty2)) t2 =>
        let c := if ty1 == ty2 then .eq else compare ty1 ty2
        if c != .eq then c else orda ((x1, x2) :: env) t1 t2
    | .Abs _ _, .Abs _ _ => panic! "orda: Abs with non-variable bound variable"
    | .Const _ _, _ => .lt
    | _, .Const _ _ => .gt
    | .Var _ _, _ => .lt
    | _, .Var _ _ => .gt
    | .Comb _ _, _ => .lt
    | _, .Comb _ _ => .gt
/-- Alpha-respecting order on closed terms. -/
def alphaorder : term → term → Ordering := orda []
/-- Union of two (alpha-sorted) term lists, modulo alpha-conversion. -/
def term_union : List term → List term → List term
  | [], l2 => l2
  | l1, [] => l1
  | h1 :: t1, h2 :: t2 =>
      match alphaorder h1 h2 with
      | .eq => h1 :: term_union t1 t2
      | .lt => h1 :: term_union t1 (h2 :: t2)
      | .gt => h2 :: term_union (h1 :: t1) t2
  termination_by l1 l2 => l1.length + l2.length
/-- Remove a term from a list, modulo alpha-conversion. -/
def term_remove (t : term) : List term → List term
  | s :: ss =>
      match alphaorder t s with
      | .gt =>
          let ss' := term_remove t ss
          if ss' == ss then s :: ss else s :: ss'
      | .eq => ss
      | .lt => s :: ss
  | [] => []
/-- Apply a function to each term of a list, unioning results (modulo alpha). -/
def term_image (f : term → term) : List term → List term
  | h :: t =>
      let h' := f h
      let t' := term_image f t
      if h' == h && t' == t then h :: t else term_union [h'] t'
  | [] => []

/- ---------------------------------------------------------------------- -/
/- Basic theorem destructors.                                             -/
/- ---------------------------------------------------------------------- -/

/-- The hypotheses and conclusion of a theorem. -/
def dest_thm (th : thm) : List term × term := (th.hyps, th.concl)
/-- The hypotheses of a theorem. -/
def hyp (th : thm) : List term := th.hyps
/-- The conclusion of a theorem. -/
def concl (th : thm) : term := th.concl

/- ---------------------------------------------------------------------- -/
/- Basic equality properties; TRANS is derivable but included for         -/
/- efficiency                                                             -/
/- ---------------------------------------------------------------------- -/

/-- Reflexivity: `|- t = t`. -/
def REFL tm :=
  thm.mk [] (safe_mk_eq tm tm)

/-- `thm` does not `deriving Inhabited`: a derived instance would let code
    outside the kernel fabricate `thm.mk default default`, a "theorem" with an
    arbitrary conclusion.  Downstream code needs an instance (theorem-bundle
    records derive `Inhabited` for `Session`'s lazy bootstrap), so we supply the
    genuine theorem `|- x = x` by `REFL`, keeping every fabricable theorem true. -/
instance : Inhabited thm := ⟨REFL default⟩

/-- Transitivity (derivable, but primitive for efficiency). -/
def TRANS (th1 th2 : thm) : Except String thm :=
  match th1.concl, th2.concl with
  | .Comb (eql@(.Comb (.Const "=" _) _)) m1, .Comb (.Comb (.Const "=" _) m2) r =>
      if alphaorder m1 m2 == .eq then
        pure (thm.mk (term_union th1.hyps th2.hyps) (.Comb eql r))
      else failwith "TRANS"
  | _, _ => failwith "TRANS"
/- ---------------------------------------------------------------------- -/
/- Congruence properties of equality.                                     -/
/- ---------------------------------------------------------------------- -/

/-- Congruence: from `|- f = g` and `|- x = y` derive `|- f x = g y`. -/
def MK_COMB (th1 th2 : thm) : Except String thm :=
  match th1.concl, th2.concl with
  | .Comb (.Comb (.Const "=" _) l1) r1, .Comb (.Comb (.Const "=" _) l2) r2 =>
      match type_of r1 with
      | .Tyapp "fun" [ty, _] =>
          if ty == type_of r2 then
            pure (thm.mk (term_union th1.hyps th2.hyps)
                    (safe_mk_eq (.Comb l1 l2) (.Comb r1 r2)))
          else failwith "MK_COMB: types do not agree"
      | _ => failwith "MK_COMB: types do not agree"
  | _, _ => failwith "MK_COMB: not both equations"
/-- Abstraction: from `|- l = r` derive `|- (\v. l) = (\v. r)`. -/
def ABS (v : term) (th : thm) : Except String thm :=
  match v, th.concl with
  | .Var _ _, .Comb (.Comb (.Const "=" _) l) r =>
      if !(exists' (fun a => vfree_in v a) th.hyps) then
        pure (thm.mk th.hyps (safe_mk_eq (.Abs v l) (.Abs v r)))
      else failwith "ABS"
  | _, _ => failwith "ABS"
/- ---------------------------------------------------------------------- -/
/- Trivial case of lambda calculus beta-conversion.                       -/
/- ---------------------------------------------------------------------- -/

/-- Beta-conversion (trivial case): `|- (\v. bod) v = bod`. -/
def BETA (tm : term) : Except String thm :=
  match tm with
  | .Comb (.Abs v bod) arg =>
      if arg == v then pure (thm.mk [] (safe_mk_eq tm bod))
      else failwith "BETA: not a trivial beta-redex"
  | _ => failwith "BETA: not a trivial beta-redex"

/- ---------------------------------------------------------------------- -/
/- Rules connected with deduction.                                        -/
/- ---------------------------------------------------------------------- -/

/-- Assume a proposition: `p |- p`. -/
def ASSUME (tm : term) : Except String thm :=
  if (type_of tm) == bool_ty then pure (thm.mk [tm] tm)
  else failwith "ASSUME: not a proposition"
/-- Equality modus ponens: from `|- p = q` and `|- p` derive `|- q`. -/
def EQ_MP (th1 th2 : thm) : Except String thm :=
  match th1.concl with
  | .Comb (.Comb (.Const "=" _) l) r =>
      if alphaorder l th2.concl == .eq then pure (thm.mk (term_union th1.hyps th2.hyps) r)
      else failwith "EQ_MP"
  | _ => failwith "EQ_MP"
/-- Deduction antisymmetry: mutual assumption gives `|- p = q`. -/
def DEDUCT_ANTISYM_RULE (th1 th2 : thm) : thm :=
  let asl1' := term_remove th2.concl th1.hyps
  let asl2' := term_remove th1.concl th2.hyps
  thm.mk (term_union asl1' asl2') (safe_mk_eq th1.concl th2.concl)

/- ---------------------------------------------------------------------- -/
/- Type and term instantiation.                                           -/
/- ---------------------------------------------------------------------- -/

/-- Instantiate type variables throughout a theorem. -/
def INST_TYPE (theta : List (hol_type × hol_type)) (th : thm) : Except String thm :=
  let inst_fn := inst theta
  .ok (thm.mk (term_image inst_fn th.hyps) (inst_fn th.concl))
/-- Instantiate (term) variables throughout a theorem. -/
def INST (theta : List (term × term)) (th : thm) : Except String thm :=
  match vsubst theta with
  | .ok inst_fun => .ok (thm.mk (term_image inst_fun th.hyps) (inst_fun th.concl))
  | .error e     => .error e

/- ---------------------------------------------------------------------- -/
/- Handling of axioms.                                                    -/
/- ---------------------------------------------------------------------- -/

private initialize theAxioms : IO.Ref (List thm) ← IO.mkRef []
/-- Return the current axioms. -/
def axioms : IO (List thm) := theAxioms.get
/-- Assert a new axiom. -/
def new_axiom (tm : term) : IO (Except String thm) := do
  if type_of tm == bool_ty then
    let th := thm.mk [] tm
    theAxioms.modify (fun axs => th :: axs)
    return .ok th
  else
    return failwith "new_axiom: Not a proposition"

/- ---------------------------------------------------------------------- -/
/- Handling of (term) definitions.                                        -/
/- ---------------------------------------------------------------------- -/

private initialize theDefinitions : IO.Ref (List thm) ← IO.mkRef []
/-- Return the current definitions. -/
def definitions : IO (List thm) := theDefinitions.get

/-- Introduce a new defined constant from an equation `c = r`. -/
def new_basic_definition (tm : term) : IO (Except String thm) := do
    match tm with
    | .Comb (.Comb (.Const "=" _) (.Var cname ty)) r =>
        if !(freesin [] r) then
          let names := (frees r).map (fun v =>
            match v with | .Var name _ => name | _ => "?")
          let nameStr := String.intercalate ", " names
          return failwith s!"new_definition: term not closed: {nameStr}"
        else if !(subset (type_vars_in_term r) (tyvars ty)) then
          return failwith "new_definition: Type variables not reflected in constant"
        else
          match ← new_constant cname ty with
          | .error e => return failwith e
          | .ok () =>
              let c := term.Const cname ty
              let dth := thm.mk [] (safe_mk_eq c r)
              theDefinitions.modify (fun defs => dth :: defs)
              return .ok dth
    | .Comb (.Comb (.Const "=" _) (.Const cname _)) _ =>
        return failwith s!"new_basic_definition: '{cname}' is already defined"
    | _ =>
        return failwith "new_basic_definition"

/- ---------------------------------------------------------------------- -/
/- Handling of type definitions.                                          -/
/-                                                                        -/
/- This function now involves no logical constants beyond equality.       -/
/-                                                                        -/
/-             |- P t                                                     -/
/-    ---------------------------                                         -/
/-        |- abs(rep a) = a                                               -/
/-     |- P r = (rep(abs r) = r)                                          -/
/-                                                                        -/
/- Where "abs" and "rep" are new constants with the nominated names.      -/
/- ---------------------------------------------------------------------- -/

/-- Introduce a new type defined by a predicate. From `|- P t` obtain the
    abstraction/representation bijection theorems:
      `|- abs (rep a) = a`  and  `|- P r = (rep (abs r) = r)`. -/
def new_basic_type_definition (tyname : String) (absname repname : String)
      (th : thm) : IO (Except String (thm × thm)) := do
    let absUsed  := (← get_const_type absname).toOption.isSome
    let repUsed  := (← get_const_type repname).toOption.isSome
    if absUsed || repUsed then
      return failwith "new_basic_type_definition: Constant(s) already in use"
    else if !th.hyps.isEmpty then
      return failwith "new_basic_type_definition: Assumptions in theorem"
    else
      match dest_comb th.concl with
      | .error _ => return failwith "new_basic_type_definition: Not a combination"
      | .ok (P, x) =>
          if !(freesin [] P) then
            return failwith "new_basic_type_definition: Predicate is not closed"
          else
            let tyvars := sort (fun a b => (compare a b).isLE) (type_vars_in_term P)
            match ← new_type tyname (tyvars.length : Int) with
            | .error _ =>
                return failwith "new_basic_type_definition: Type already defined"
            | .ok () =>
                let aty := hol_type.Tyapp tyname tyvars
                let rty := type_of x
                let absty := hol_type.Tyapp "fun" [rty, aty]
                let repty := hol_type.Tyapp "fun" [aty, rty]
                -- `let abs = (new_constant(absname,absty); Const(absname,absty))
                --  and rep = (new_constant(repname,repty); Const(repname,repty))`
                -- (fusion.ml 634-635): `new_constant` raises if the name is
                -- taken, so its failure must end the definition here.  The
                -- guard above checks each name against the existing constants
                -- but not against the other, so with `absname = repname` the
                -- second `new_constant` is what rejects it, as in HOL Light
                -- (which also leaves the type and the first constant declared).
                match ← new_constant absname absty with
                | .error e => return .error e
                | .ok () =>
                let abs := term.Const absname absty
                match ← new_constant repname repty with
                | .error e => return .error e
                | .ok () =>
                let rep := term.Const repname repty
                let a := term.Var "a" aty
                let r := term.Var "r" rty
                match mk_comb rep a with
                | .error e => return .error e
                | .ok repA =>
                    let th1 := thm.mk [] (safe_mk_eq (.Comb abs repA) a)
                    match mk_comb abs r with
                    | .error e => return .error e
                    | .ok absR =>
                        match mk_comb rep absR with
                        | .error e => return .error e
                        | .ok repAbsR =>
                            let th2 := thm.mk []
                              (safe_mk_eq (.Comb P r) (safe_mk_eq repAbsR r))
                            return .ok (th1, th2)

end HolCore.Kernel

open HolCore.Kernel

/- ---------------------------------------------------------------------- -/
/- Stuff that didn't seem worth putting in.                               -/
/- (Placed outside the kernel namespace.)                                 -/
/- ---------------------------------------------------------------------- -/

/-- Construct a function type `ty1 -> ty2`. -/
def mk_fun_ty (ty1 ty2 : hol_type) := mk_type "fun" [ty1, ty2]
/-- The generic type variable `B`. -/
def bty := mk_vartype "B"
/-- Is this term an equation? -/
def is_eq (tm : term) : Bool :=
  match tm with
  | (.Comb (.Comb (.Const "=" _) _) _) => true
  | _ => false
/-- Build an equation `l = r` via the `=` constant (IO factory form). -/
def mk_eq : IO (Except String ((term × term) → Except String term)) := do
  match ← mk_const "=" [] with
  | .error e => return .error e
  | .ok eq =>
    return .ok fun (l, r) =>
      let ty := type_of l
      let eq_tm := inst [(ty, aty)] eq
      match mk_comb eq_tm l with
      | .error _ => failwith "mk_eq"
      | .ok inner =>
        match mk_comb inner r with
        | .error _ => failwith "mk_eq"
        | .ok res => .ok res

/- ---------------------------------------------------------------------- -/
/- Tests for alpha-convertibility (equality ignoring names in             -/
/- abstractions).                                                         -/
/- ---------------------------------------------------------------------- -/

/-- Alpha-convertibility (equality ignoring bound-variable names). -/
def aconv (s t : term) : Bool := alphaorder s t == .eq

/-- Comparison function on theorems. Currently the same as equality, but
    it's useful to separate because in the proof-recording version it isn't. -/
def equals_thm (th th' : thm) : Bool := dest_thm th == dest_thm th'
