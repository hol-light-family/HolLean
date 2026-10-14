/- File: Basics.lean
More syntax constructors, and prelogical utilities like matching.
John Harrison, University of Cambridge Computer Laboratory
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Original (c) Copyright, Andrea Gabrielli, Marco Maggesi 2017-2018
Lean4 translation by Chris Walton 2026 -/

import HolCore.Lib
import HolCore.Fusion
import HolCore.OcamlHash
open HolCore.Kernel HolCore.Lib

namespace HolCore.Basics

/- ---------------------------------------------------------------------- -/
/- Create probably-fresh variable.                                        -/
/- ---------------------------------------------------------------------- -/

/-- Global counter backing `genvar`. -/
initialize gcounter : IO.Ref Nat ← IO.mkRef 0

/-- Create a probably-fresh variable of the given type. -/
def genvar (ty : hol_type) : IO term := do
  let count ← gcounter.get
  gcounter.set (count + 1)
  return mk_var ("_" ++ toString count) ty

/- ---------------------------------------------------------------------- -/
/- Convenient functions for manipulating types.                           -/
/- ---------------------------------------------------------------------- -/

/-- Break apart a function type `ty1 -> ty2`. -/
def dest_fun_ty (ty : hol_type) : Except String (hol_type × hol_type):=
  match ty with
  | .Tyapp "fun" [ty1, ty2] => .ok (ty1, ty2)
  | _ => failwith "dest_fun_ty"

/-- Does `ty` occur in `bigty`? -/
partial def occurs_in (ty bigty : hol_type) : Bool :=
  bigty == ty ||
  (is_type bigty &&
    (match dest_type bigty with
      | .ok (_, args) => exists' (occurs_in ty) args
      | .error _      => false))

/-- Substitute types for types throughout a type (checking definedness). -/
partial def tysubst (alist : List (hol_type × hol_type)) (ty : hol_type) : ExceptT String IO hol_type := do
  match rev_assoc ty alist with
  | .ok t => return t
  | .error _ =>
    if is_vartype ty then
      return ty
    else
      let (tycon, tyvars) ← dest_type ty
      let subst ← tyvars.mapM (tysubst alist)
      mk_type tycon subst

/- ---------------------------------------------------------------------- -/
/- A bit more syntax.                                                     -/
/- ---------------------------------------------------------------------- -/

/-- The bound variable of an abstraction. -/
def bndvar (tm : term) : Except String term :=
  match dest_abs tm with
  | .ok (v, _) => .ok v
  | .error _   => failwith "bndvar: Not an abstraction"

/-- The body of an abstraction. -/
def body (tm : term) : Except String term :=
  match dest_abs tm with
  | .ok (_, v) => .ok v
  | .error _   => failwith "body: Not an abstraction"

/-- Iteratively apply `h` to a list of arguments. -/
def list_mk_comb (h : term) (t : List term) : Except String term :=
  rev_itlist (fun arg acc => acc.bind (fun f => mk_comb f arg)) t (.ok h)

/-- Iteratively abstract a body over a list of variables. -/
def list_mk_abs (vs : List term) (bod : term) : Except String term :=
  itlist (fun v acc => acc.bind (fun b => mk_abs v b)) vs (.ok bod)

/-- Split a term into its head operator and argument list. -/
def strip_comb : term → term × List term := rev_splitlist dest_comb
/-- Split off the leading abstractions of a term. -/
def strip_abs : term → List term × term := splitlist dest_abs

/- ---------------------------------------------------------------------- -/
/- Generic syntax to deal with some binary operators.                     -/
/-   Note that `mk_binary` only works for monomorphic functions.          -/
/- ---------------------------------------------------------------------- -/

/-- Is `tm` an application of the binary operator named `s`? -/
def is_binary (s : String) (tm : term) : Bool :=
  match tm with
  | .Comb (.Comb (.Const s' _) _) _ => s' == s
  | _ => false

/-- Destruct an application of the binary operator named `s`. -/
def dest_binary (s : String) (tm : term) : Except String (term × term) :=
  match tm with
  | .Comb (.Comb (.Const s' _) l) r =>
    if s' == s then .ok (l, r)
    else failwith "dest_binary"
  | _ => failwith "dest_binary"

/-- Build a binary-operator constructor (IO factory; monomorphic only). -/
def mk_binary (s : String) : IO (Except String ((term × term) → Except String term)) := do
  match ← mk_const s [] with
  | .error e => return failwith e
  | .ok c =>
    return .ok fun (l, r) =>
      match mk_comb c l with
      | .error _ => failwith "mk_binary"
      | .ok cl =>
        match mk_comb cl r with
        | .error _ => failwith "mk_binary"
        | .ok res => .ok res

/- ---------------------------------------------------------------------- -/
/- Produces a sequence of variants, considering previous inventions.      -/
/- ---------------------------------------------------------------------- -/

/-- Produce a sequence of variants, considering previous inventions. -/
partial def variants (av : List term) (vs : List term) : Except String (List term) :=
  if vs == [] then .ok []
  else do
    let vh ← variant av (← hd vs)
    let rest ← variants (vh :: av) (← tl vs)
    return vh :: rest

/- ---------------------------------------------------------------------- -/
/- Gets all variables (free and/or bound) in a term.                      -/
/- ---------------------------------------------------------------------- -/

/-- Gets all variables (free and/or bound) in a term. -/
partial def variables (tm : term) : Except String (List term) :=
  let rec vars (acc : List term) (tm : term) : Except String (List term) :=
    if is_var tm then .ok (insert tm acc)
    else if is_const tm then .ok acc
    else if is_abs tm then
      match dest_abs tm with
      | .error e => .error e
      | .ok (v, bod) => vars (insert v acc) bod
    else
      match dest_comb tm with
      | .error e => .error e
      | .ok (l, r) =>
        match vars acc l with
        | .error e => .error e
        | .ok acc' => vars acc' r
  vars [] tm

/- ---------------------------------------------------------------------- -/
/- General substitution (for any free expression).                        -/
/- ---------------------------------------------------------------------- -/

/-- General substitution (for any free expression). -/
partial def subst (ilist : List (term × term)) :
    IO (Except String (term → IO (Except String term))) := do
  let rec ssubst (ilist : List (term × term)) (tm : term) : Except String term :=
    if ilist == [] then .ok tm
    else match find (fun (_, b) => aconv tm b) ilist with
      | .ok (a, _) => .ok a
      | .error _   => match tm with
        | .Comb f x => do
            let f' ← ssubst ilist f
            let x' ← ssubst ilist x
            if f' == f && x' == x then .ok tm else mk_comb f' x'
        | .Abs v bod => do
            let ilist' := filter (fun (_, b) => !(vfree_in v b)) ilist
            mk_abs v (← ssubst ilist' bod)
        | _ => .ok tm
  let theta := filter (fun (s, t) => compare s t != .eq) ilist
  if theta == [] then
    return .ok (fun tm => return .ok tm)
  let (ts, xs) := unzip theta
  return .ok fun tm => do
    let freshVars ← xs.mapM (fun x => genvar (type_of x))
    return do
      let vtm  ← variables tm
      let gs   ← variants vtm freshVars
      let gsxs ← zip gs xs
      let tm'  ← ssubst gsxs tm
      if tm' == tm then .ok tm
      else
        let tsgs ← zip ts gs
        let f ← vsubst tsgs
        .ok (f tm')

/- ---------------------------------------------------------------------- -/
/- Alpha conversion term operation.                                       -/
/- ---------------------------------------------------------------------- -/

/-- Alpha conversion term operation (rename the bound variable). -/
def alpha (v : term) (tm : term) : Except String term :=
  match dest_abs tm with
  | .error _ => failwith "alpha: Not an abstraction"
  | .ok (v0, bod) =>
    if v == v0 then .ok tm
    else if type_of v == type_of v0 && !(vfree_in v bod) then
      match vsubst [(v, v0)] with
      | .error e => .error e
      | .ok sub => mk_abs v (sub bod)
    else failwith "alpha: Invalid new variable"

/- ---------------------------------------------------------------------- -/
/- Type matching.                                                         -/
/- ---------------------------------------------------------------------- -/

/-- Match a (pattern) type against a concrete type, accumulating a subst. -/
partial def type_match (vty cty : hol_type)
    (sofar : List (hol_type × hol_type)) : Except String (List (hol_type × hol_type)) :=
  if is_vartype vty then
    match rev_assoc vty sofar with
    | .ok bound => if bound == cty then .ok sofar else failwith "type_match"
    | .error _  => .ok ((cty, vty) :: sofar)
  else
    match dest_type vty, dest_type cty with
    | .ok (vop, vargs), .ok (cop, cargs) =>
      if vop == cop then
        (itlist2
          (fun v c (acc : Except String (List (hol_type × hol_type))) =>
            acc.bind (type_match v c))
          vargs cargs (.ok sofar)).bind id
      else failwith "type_match"
    | _, _ => failwith "type_match"

/- ---------------------------------------------------------------------- -/
/- Conventional matching version of mk_const (but with a sanity test).    -/
/- ---------------------------------------------------------------------- -/

/-- Matching version of `mk_const` (with a sanity test on the result type). -/
def mk_mconst (c : String) (ty : hol_type) : IO (Except String term) := do
  match ← get_const_type c with
  | .error _ => return failwith "mk_const: generic type cannot be instantiated"
  | .ok uty =>
    match type_match uty ty [] with
    | .error _ => return failwith "mk_const: generic type cannot be instantiated"
    | .ok mat =>
      match ← mk_const c mat with
      | .error _ => return failwith "mk_const: generic type cannot be instantiated"
      | .ok con =>
        if type_of con == ty then return .ok con
        else return failwith "mk_const: generic type cannot be instantiated"

/- ---------------------------------------------------------------------- -/
/- Like mk_comb, but instantiates type variables in rator if necessary.   -/
/- ---------------------------------------------------------------------- -/

/-- Like `mk_comb`, but instantiates type variables in the rator if needed.

    Where OCaml (basics.ml 171-174) uses an irrefutable `let "fun",[ty;_] = ...`
    that crashes uncatchably on a non-function `tm1`, we return a catchable
    `failwith`. On every input where OCaml succeeds this returns the same term. -/
def mk_icomb (tm1 tm2 : term) : Except String term :=
  match dest_type (type_of tm1) with
  | .ok ("fun", [ty, _]) =>
    match type_match ty (type_of tm2) [] with
    | .error e => .error e
    | .ok tyins => mk_comb (inst tyins tm1) tm2
  | .ok _   => failwith "mk_icomb: not a function type"
  | .error e => failwith e

/- ---------------------------------------------------------------------- -/
/- Instantiates types for constant c and iteratively makes combination.   -/
/- ---------------------------------------------------------------------- -/

/-- Instantiate a constant's types and iteratively apply it to arguments. -/
def list_mk_icomb (cname : String) (args : List term) : IO (Except String term) := do
  match ← get_const_type cname with
  | .error e => return failwith e
  | .ok cty =>
    match nsplit dest_fun_ty args cty with
    | .error e => return failwith e
    | .ok (atys, _) =>
      match
        (itlist2
          (fun g a (acc : Except String (List (hol_type × hol_type))) =>
            acc.bind (type_match g (type_of a)))
          atys args (.ok [])).bind id
      with
      | .error e => return failwith e
      | .ok tyin =>
        match ← mk_const cname tyin with
        | .error e => return failwith e
        | .ok c => return list_mk_comb c args

/- ---------------------------------------------------------------------- -/
/- Free variables in assumption list and conclusion of a theorem.         -/
/- ---------------------------------------------------------------------- -/

/-- Free variables in the assumptions and conclusion of a theorem. -/
def thm_frees (th : thm) : List term :=
  let (asl, c) := dest_thm th
  itlist (union o frees) asl (frees c)

/- ---------------------------------------------------------------------- -/
/- Is one term free in another?                                           -/
/- ---------------------------------------------------------------------- -/

/-- Is one term free in another? -/
partial def free_in (tm1 tm2 : term) : Bool :=
  if aconv tm1 tm2 then true
  else if is_comb tm2 then
    match dest_comb tm2 with
    | .ok (l, r) => free_in tm1 l || free_in tm1 r
    | .error _ => false
  else if is_abs tm2 then
    match dest_abs tm2 with
    | .ok (bv, bod) => !(vfree_in bv tm1) && free_in tm1 bod
    | .error _ => false
  else false

/- ---------------------------------------------------------------------- -/
/- Searching for terms.                                                   -/
/- ---------------------------------------------------------------------- -/

/-- Find the first subterm satisfying a predicate. -/
partial def find_term (p : term → Bool) (tm : term) : Except String term :=
  if p tm then .ok tm
  else if is_abs tm then
    match body tm with
    | .error _  => failwith "find_term"
    | .ok bod   => find_term p bod
  else if is_comb tm then
    match dest_comb tm with
    | .error _ => failwith "find_term"
    | .ok (l, r) =>
      match find_term p l with
      | .ok found => .ok found
      | .error _  => find_term p r
  else failwith "find_term"

/-- Find all subterms satisfying a predicate. -/
partial def find_terms (p : term → Bool) (tm : term) : List term :=
  let rec accum (tl : List term) (p : term → Bool) (tm : term) : List term :=
    let tl' := if p tm then insert tm tl else tl
    if is_abs tm then
      match body tm with
      | .ok bod => accum tl' p bod
      | .error _ => tl'
    else if is_comb tm then
      match rator tm, rand tm with
      | .ok f, .ok x => accum (accum tl' p f) p x
      | _, _ => tl'
    else tl'
  accum [] p tm

/- ---------------------------------------------------------------------- -/
/- General syntax for binders.                                            -/
/-   NB! The "mk_binder" function expects polytype "A", which is the      -/
/-   domain.                                                              -/
/- ---------------------------------------------------------------------- -/

/-- Is `tm` an application of the binder named `s`? -/
def is_binder (s : String) (tm : term) : Bool :=
  match tm with
  | .Comb (.Const s' _) (.Abs _ _) => s' == s
  | _ => false

/-- Destruct an application of the binder named `s`. -/
def dest_binder (s : String) (tm : term) : Except String (term × term) :=
  match tm with
  | .Comb (.Const s' _) (.Abs x t) =>
    if s' == s then .ok (x, t)
    else failwith "dest_binder"
  | _ => failwith "dest_binder"

/-- Build a binder constructor (IO factory). -/
def mk_binder (op : String) :
    IO (Except String ((term × term) → Except String term)) := do
  match ← mk_const op [] with
  | .error e => return failwith e
  | .ok c =>
    return .ok fun (v, tm) => do
      let abs ← mk_abs v tm
      mk_comb (inst [(type_of v, aty)] c) abs

/- ---------------------------------------------------------------------- -/
/- Syntax for binary operators.                                           -/
/- ---------------------------------------------------------------------- -/

/-- Is `tm` an application of the binary operator term `op`? -/
def is_binop (op : term) (tm : term) : Bool :=
  match tm with
  | .Comb (.Comb op' _) _ => op' == op
  | _ => false

/-- Destruct an application of the binary operator term `op`. -/
def dest_binop (op : term) (tm : term) : Except String (term × term) :=
  match tm with
  | .Comb (.Comb op' l) r =>
    if op' == op then .ok (l, r)
    else failwith "dest_binop"
  | _ => failwith "dest_binop"

/-- Partially apply a binary operator term to its first argument. -/
def mk_binop (op tm1 : term) : Except String (term → Except String term) := do
  let f ← mk_comb op tm1
  return fun tm2 => mk_comb f tm2

/-- Right-fold a list of terms with a binary operator term. -/
def list_mk_binop (op : term) (tms : List term) : Except String term :=
  (end_itlist
    (fun (a b : Except String term) => do
      let x ← a
      let y ← b
      let g ← mk_binop op x
      g y)
    (tms.map .ok)).bind id

/-- Split a term into the arguments of an iterated binary operator. -/
def binops (op : term) : term → List term := striplist (dest_binop op)

/- ---------------------------------------------------------------------- -/
/- Some common special cases.                                             -/
/- ---------------------------------------------------------------------- -/

def is_conj : term → Bool := is_binary "/\\"
def dest_conj : term → Except String (term × term) := dest_binary "/\\"
def conjuncts : term → List term := striplist dest_conj

def is_imp : term → Bool := is_binary "==>"
def dest_imp : term → Except String (term × term) := dest_binary "==>"

def is_forall : term → Bool := is_binder "!"
def dest_forall : term → Except String (term × term) := dest_binder "!"
def strip_forall : term → List term × term := splitlist dest_forall

def is_exists : term → Bool := is_binder "?"
def dest_exists : term → Except String (term × term) := dest_binder "?"
def strip_exists : term → List term × term := splitlist dest_exists

def is_disj : term → Bool := is_binary "\\/"
def dest_disj : term → Except String (term × term) := dest_binary "\\/"
def disjuncts : term → List term := striplist dest_disj

/-- Is `tm` a negation `~p`? -/
def is_neg (tm : term) : Bool :=
  match rator tm with
  | .error _ => false
  | .ok r =>
    match dest_const r with
    | .error _ => false
    | .ok (name, _) => name == "~"

/-- Destruct a negation `~p`, returning `p`. -/
def dest_neg (tm : term) : Except String term :=
  match dest_comb tm with
  | .error _ => failwith "dest_neg"
  | .ok (n, p) =>
    match dest_const n with
    | .error _ => failwith "dest_neg"
    | .ok (name, _) =>
      if name == "~" then .ok p
      else failwith "dest_neg"

def is_uexists : term → Bool := is_binder "?!"
def dest_uexists : term → Except String (term × term) := dest_binder "?!"

def dest_cons : term → Except String (term × term) := dest_binary "CONS"
def is_cons : term → Bool := is_binary "CONS"

/-- Destruct a list term `CONS x1 (… (CONS xn NIL))` into `[x1,…,xn]`. -/
def dest_list (tm : term) : Except String (List term) :=
  let (tms, nil) := splitlist dest_cons tm
  match dest_const nil with
  | .error _ => failwith "dest_list"
  | .ok (name, _) =>
    if name == "NIL" then .ok tms
    else failwith "dest_list"
def is_list : term → Bool := can dest_list

/- ---------------------------------------------------------------------- -/
/- Syntax for numerals.                                                   -/
/- ---------------------------------------------------------------------- -/

/-- Extract the `Rat` value denoted by a `NUMERAL`/`BIT0`/`BIT1`/`_0` term. -/
partial def dest_numeral (tm : term) : Except String Rat :=
  let constName (t : term) : Except String String := do
    let (c, _) ← dest_const t
    return c
  let rec dest_num (t : term) : Except String Rat := do
    match constName t with
    | .ok "_0" => return num_0
    | _ =>
      let (l, r) ← dest_comb t
      let nr ← dest_num r
      let n := num_2 * nr
      match ← constName l with
      | "BIT0" => return n
      | "BIT1" => return n + num_1
      | _      => fail
  (do
    let (l, r) ← dest_comb tm
    if (← constName l) == "NUMERAL" then dest_num r else fail
  ).mapError (fun _ => "dest_numeral")

/- ---------------------------------------------------------------------- -/
/- Syntax for generalized abstractions.                                   -/
/-   These are here because they are used by the preterm->term            -/
/-   translator; preterms regard generalized abstractions as an atomic    -/
/-   notion. This is slightly unclean --- for example we need locally     -/
/-   some operations on universal quantifiers --- but probably simplest.  -/
/-   It has to go somewhere!                                              -/
/- ---------------------------------------------------------------------- -/

/-- Destruct a generalized abstraction. -/
def dest_gabs (tm : term) : Except String (term × term) :=
  let dest_geq := dest_binary "GEQ"
  (do
    if is_abs tm then
      dest_abs tm
    else
      let (l, r) ← dest_comb tm
      let (cn, _) ← dest_const l
      if cn != "GABS" then fail
      else
        let bodyR ← body r
        let (ltm, rtm) ← dest_geq (strip_forall bodyR).snd
        let l' ← rand ltm
        return (l', rtm)
  ).mapError (fun _ => "dest_gabs: Not a generalized abstraction")

def is_gabs : term → Bool := can dest_gabs

/-- Construct a generalized abstraction `\tm1. tm2`. -/
def mk_gabs (tm1 tm2 : term) : IO (Except String term) := ExceptT.run do
  let mk_forall (v t : term) : ExceptT String IO term := do
    let cop ← mk_const "!" [(type_of v, aty)]
    liftExcept (do mk_comb cop (← mk_abs v t))
  let rec list_mk_forall : List term → term → ExceptT String IO term
    | [],      bod => return bod
    | v :: vs, bod => do mk_forall v (← list_mk_forall vs bod)
  let mk_geq (a b : term) : ExceptT String IO term := do
    let p ← mk_const "GEQ" [(type_of a, aty)]
    liftExcept (do mk_comb (← mk_comb p a) b)
  if is_var tm1 then
    liftExcept (mk_abs tm1 tm2)
  else
    let fty ← mk_fun_ty (type_of tm1) (type_of tm2)
    let f ← liftExcept (variant (frees tm1 ++ frees tm2) (mk_var "f" fty))
    let geq ← mk_geq (← liftExcept (mk_comb f tm1)) tm2
    let bod ← liftExcept (mk_abs f (← list_mk_forall (frees tm1) geq))
    let gabs ← mk_const "GABS" [(fty, aty)]
    liftExcept (mk_comb gabs bod)

/-- Iteratively construct a generalized abstraction. -/
def list_mk_gabs (vs : List term) (bod : term) : IO (Except String term) :=
  (itlist (fun v acc => do mk_gabs v (← acc)) vs (pure bod) : ExceptT String IO term).run

def strip_gabs : term → List term × term := splitlist dest_gabs

/- ---------------------------------------------------------------------- -/
/- Syntax for let terms.                                                  -/
/- ---------------------------------------------------------------------- -/

/-- Destruct a let-term into its bindings and body. -/
def dest_let (tm : term) : Except String (List (term × term) × term) :=
  (do
    let (l, aargs) := strip_comb tm
    let (cn, _) ← dest_const l
    if cn != "LET" then fail
    else
      let (vars, lebod) := strip_gabs (← hd aargs)
      let eqs ← zip vars (← tl aargs)
      let (le, bod) ← dest_comb lebod
      let (cn2, _) ← dest_const le
      if cn2 == "LET_END" then return (eqs, bod)
      else fail
  ).mapError (fun _ => "dest_let: not a let-term")

def is_let : term → Bool := can dest_let

/-- Construct a let-term from bindings and a body. -/
def mk_let (assigs : List (term × term)) (bod : term) : IO (Except String term) := ExceptT.run do
  let (lefts, rights) := unzip assigs
  let lend ← liftExcept (mk_comb (← mk_const "LET_END" [(type_of bod, aty)]) bod)
  let lbod ← list_mk_gabs lefts lend
  let (ty1, ty2) ← liftExcept (dest_fun_ty (type_of lbod))
  let ltm ← mk_const "LET" [(ty1, aty), (ty2, bty)]
  liftExcept (list_mk_comb ltm (lbod :: rights))

/- ---------------------------------------------------------------------- -/
/- Constructors and destructors for finite types.                         -/
/- ---------------------------------------------------------------------- -/

/-- Is `n` a non-negative integer (denominator 1)? -/
def is_integer_num (n : Rat) : Bool := n.den == 1
/-- Integer quotient by 2. -/
def quo_num2 (n : Rat) : Rat := Rat.ofInt (n.num / 2)
/-- Integer remainder mod 2. -/
def mod_num2 (n : Rat) : Rat := Rat.ofInt (n.num % 2)

/-- Build the finite type of size `n` (via `1`/`tybit0`/`tybit1`). Only usable
    once those type constants are declared. -/
partial def mk_finty (n : Rat) : IO (Except String hol_type) := do
  let rec finty (n : Rat) : IO (Except String hol_type) := do
    if n == num_1 then
      mk_type "1" []
    else
      let sub ← finty (quo_num2 n)
      match sub with
      | .error e => return .error e
      | .ok subTy =>
        let tycon := if mod_num2 n == num_0 then "tybit0" else "tybit1"
        mk_type tycon [subTy]
  if !(is_integer_num n) || n < num_1 then
    return failwith "mk_finty"
  else
    finty n

/-- The size denoted by a finite type. -/
def dest_finty : hol_type → Except String Rat
  | .Tyapp "1" _        => .ok num_1
  | .Tyapp "tybit0" [ty] => do return (← dest_finty ty) * num_2
  | .Tyapp "tybit1" [ty] => do return ((← dest_finty ty) * num_2) + num_1
  | _                    => failwith "dest_finty"

/- ---------------------------------------------------------------------- -/
/- Useful function to create stylized arguments using numbers.            -/
/- ---------------------------------------------------------------------- -/

/-- Create stylized arguments `s0, s1, …` of the given types, avoiding a list. -/
partial def make_args (s : String) (avoid : List term) (tys : List hol_type) :
    Except String (List term) :=
  let rec margs (n : Nat) (s : String) (avoid : List term) (tys : List hol_type) :
      Except String (List term) := do
    if tys == [] then
      return []
    else
      let v ← variant avoid (mk_var (s ++ toString n) (← hd tys))
      let rest ← margs (n + 1) s (v :: avoid) (← tl tys)
      return v :: rest
  if length tys == 1 then do
    let v ← variant avoid (mk_var s (← hd tys))
    return [v]
  else
    margs 0 s avoid tys

/- ---------------------------------------------------------------------- -/
/- Director strings down a term.                                          -/
/- ---------------------------------------------------------------------- -/

/-- Director string ("l"/"r"/"b") to the first subterm satisfying `p`. -/
partial def find_path (p : term → Bool) (tm : term) : Except String String :=
  let rec fp (tm : term) : Except String (List String) :=
    if p tm then .ok []
    else if is_abs tm then
      match body tm with
      | .error _ => .error "find_path"
      | .ok bod  => do return "b" :: (← fp bod)
    else
      match (do let r ← rand tm; let path ← fp r; return "r" :: path) with
      | .ok rpath => .ok rpath
      | .error _  => do let l ← rator tm; let path ← fp l; return "l" :: path
  do return implode (← fp tm)

/-- Follow a director string down a term. -/
partial def follow_path (s : String) (tm : term) : Except String term :=
  let rec fp (s : List String) (tm : term) : Except String term :=
    match s with
    | []        => .ok tm
    | "l" :: t  => do fp t (← rator tm)
    | "r" :: t  => do fp t (← rand tm)
    | _ :: t    => do fp t (← body tm)
  fp (explode s) tm

/- ---------------------------------------------------------------------- -/
/- Considering a term as a propositional formula and returning atoms.     -/
/- ---------------------------------------------------------------------- -/

/-- The atoms of a Boolean term - the leaves under the logical connectives.
    The result is a set; callers must not depend on its order. -/
def atoms (tm : term) : Except String (List term) :=
  let rec go (acc : Lib.Func term Unit) (tm : term) : Lib.Func term Unit :=
    match tm with
    | .Comb (.Comb (.Const "/\\" _) l) r         => go (go acc l) r
    | .Comb (.Comb (.Const "\\/" _) l) r         => go (go acc l) r
    | .Comb (.Comb (.Const "==>" _) l) r         => go (go acc l) r
    | .Comb (.Comb (.Const "=" (.Tyapp "fun" [.Tyapp "bool" [], _])) l) r
                                                  => go (go acc l) r
    | .Comb (.Const "~" _) l                     => go acc l
    | _ => (tm |-> ()) acc
  if type_of tm != bool_ty then
    failwith "atoms: not Boolean"
  else
    .ok (Lib.foldl (fun a x _ => x :: a) [] (go Lib.undefined tm))
