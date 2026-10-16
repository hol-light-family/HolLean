/- File: HolTest/FusionTest.lean
Runtime test suite: fusion.ml - the logical kernel of types, terms, theorems.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set.

FAITHFULNESS BASIS.  Expectations are taken from fusion.ml itself (the module
under test) and from HOL Light's reference documentation where a worked example
exists:
  hol-light/Help/inst.hlp   (the capture-avoidance renaming example)
  hol-light/Help/DEDUCT_ANTISYM_RULE.hlp
  hol-light/Help/INST_TYPE.hlp
The kernel is HOL Light's trusted core, so every soundness side condition and
every `failwith` string is pinned LITERALLY: a recent audit found `new_type`
had dropped the word `type ` from its message, and such a defect is invisible
without a string assertion.

TERMS ARE HAND-BUILT FROM THE KERNEL CONSTRUCTORS, not parsed.  This is
deliberate: (1) it keeps these tests independent of the parser/printer theory
bootstrap, and (2) several cases (identically-named variables of DIFFERENT type)
"cannot be done directly in the term parser" - the exact words of inst.hlp -
yet are precisely the inputs that exercise the `Clash`/`variant` renaming
branch, the highest-risk least-tested kernel code.

Comparisons are STRUCTURAL (`term`/`hol_type` derive `BEq`), not printed.  A
theorem is checked by asserting its `concl` (and, where it matters, `hyp`)
equals an expected term built with the SAME `safe_mk_eq` the rule uses, so a
degenerate `Inhabited`-default theorem (which would print as `|-  = `) cannot
masquerade as a pass. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

namespace HolTest.FusionTest

/- ---------------------------------------------------------------------- -/
/- Fixed atoms, all hand-built so their types are known exactly.          -/
/- `aty` = `:A`, `bty'` = `:B`; `funTy a b` = `:a->b`.                    -/
/- ---------------------------------------------------------------------- -/

private def bty' : hol_type := .Tyvar "B"
private def funTy (a b : hol_type) : hol_type := .Tyapp "fun" [a, b]

private def xA : term := .Var "x" aty
private def yA : term := .Var "y" aty
private def xB : term := .Var "x" bty'
private def fAA : term := .Var "f" (funTy aty aty)
private def pB : term := .Var "p" bool_ty
private def qB : term := .Var "q" bool_ty

/- ---------------------------------------------------------------------- -/
/- Reporting helpers.                                                     -/
/-                                                                        -/
/- A passing assertion prints a line containing `-> OK`.  A genuine defect -/
/- (wrong term, or - critically - a wrong/short `failwith` string) prints  -/
/- the `MISMATCH` build-gate token.  An expected-failure that behaves     -/
/- prints `-> OK (correctly rejected)`.                                    -/
/- ---------------------------------------------------------------------- -/

/-- A pure `Except String term` must equal `exp`. -/
private unsafe def okTerm (lbl : String) (got : Except String term) (exp : term) :
    IO Unit :=
  match got with
  | .ok t   => if t == exp then IO.println s!"{lbl} -> OK"
               else IO.println s!"{lbl} -> MISMATCH got={reprStr t}"
  | .error e => IO.println s!"{lbl} -> MISMATCH unexpected error: {e}"

/-- A pure `Except String hol_type` must equal `exp`. -/
private unsafe def okType (lbl : String) (got : Except String hol_type)
    (exp : hol_type) : IO Unit :=
  match got with
  | .ok t   => if t == exp then IO.println s!"{lbl} -> OK"
               else IO.println s!"{lbl} -> MISMATCH got={reprStr t}"
  | .error e => IO.println s!"{lbl} -> MISMATCH unexpected error: {e}"

/-- A generic `Except String α` (BEq) must equal `.ok exp`. -/
private def okEq {α : Type} [BEq α] [Repr α] (lbl : String)
    (got : Except String α) (exp : α) : IO Unit :=
  match got with
  | .ok v   => if v == exp then IO.println s!"{lbl} -> OK"
               else IO.println s!"{lbl} -> MISMATCH got={reprStr v}"
  | .error e => IO.println s!"{lbl} -> MISMATCH unexpected error: {e}"

/-- A theorem's conclusion must equal `expConcl` (degenerate-value guard). -/
private unsafe def okConcl (lbl : String) (got : Except String thm)
    (expConcl : term) : IO Unit :=
  match got with
  | .ok th  => if concl th == expConcl then IO.println s!"{lbl} -> OK"
               else IO.println s!"{lbl} -> MISMATCH concl={reprStr (concl th)}"
  | .error e => IO.println s!"{lbl} -> MISMATCH unexpected error: {e}"

/-- An `Except String α` MUST be `.error` with EXACTLY `expMsg`.  A wrong or
    short message is a real defect, so it trips the `MISMATCH` gate. -/
private def failMsg {α : Type} (lbl : String) (got : Except String α)
    (expMsg : String) : IO Unit :=
  match got with
  | .error e => if e == expMsg then IO.println s!"{lbl} -> OK (correctly rejected)"
                else IO.println s!"{lbl} -> MISMATCH msg=\"{e}\" expected=\"{expMsg}\""
  | .ok _    => IO.println s!"{lbl} -> MISMATCH unexpectedly succeeded"

/- ---------------------------------------------------------------------- -/
/- Type constructors / destructors and their arity checks.                -/
/- fusion.ml: mk_type / dest_type / dest_vartype / get_type_arity.        -/
/- ---------------------------------------------------------------------- -/

-- get_type_arity on the two primitive types (the_type_constants init).
#eval (do okEq "get_type_arity bool" (← get_type_arity "bool") (0 : Int))
#eval (do okEq "get_type_arity fun" (← get_type_arity "fun") (2 : Int))

-- mk_type builds a well-formed application when the arity matches.
#eval (do okType "mk_type fun[bool,bool]" (← mk_type "fun" [bool_ty, bool_ty])
            (funTy bool_ty bool_ty))

-- mk_type: wrong arity.  `fun` has arity 2; one argument must be rejected,
-- with the EXACT message (fusion.ml: "mk_type: wrong number of arguments to").
#eval (do failMsg "mk_type fun[bool] wrong arity" (← mk_type "fun" [bool_ty])
            "mk_type: wrong number of arguments to fun")

-- mk_type: undefined type operator.  This is the message class the audit
-- found broken for `new_type`; pin the word `type ` here too.
#eval (do failMsg "mk_type nonesuch undefined" (← mk_type "nonesuch" [])
            "mk_type: type nonesuch has not been defined")

-- dest_type on a constructor and on a variable (must fail literally).
#eval okEq "dest_type bool" (dest_type bool_ty) ("bool", ([] : List hol_type))
#eval failMsg "dest_type on tyvar" (dest_type aty)
  "dest_type: type variable not a constructor"
#eval okEq "dest_vartype A" (dest_vartype aty) "A"
#eval failMsg "dest_vartype on ctor" (dest_vartype bool_ty)
  "dest_vartype: type constructor not a variable"

/- ---------------------------------------------------------------------- -/
/- Term constructors / destructors and their type checks.                 -/
/- fusion.ml: mk_var / mk_const / mk_abs / mk_comb / dest_*.              -/
/- ---------------------------------------------------------------------- -/

-- mk_var is total.
#eval okEq "mk_var x:A" (.ok (mk_var "x" aty) : Except String term) xA

-- mk_const "=" with empty instantiation yields the generic equality constant
-- (the_term_constants init: "=" : A->A->bool).
#eval (do okTerm "mk_const = []" (← mk_const "=" [])
            (.Const "=" (funTy aty (funTy aty bool_ty))))
-- mk_const on a name that is not a constant.
#eval (do failMsg "mk_const nonesuch" (← mk_const "nonesuch" [])
            "mk_const: not a constant name")

-- mk_abs: bound term must be a variable.
#eval okEq "mk_abs \\x. y" (mk_abs xA yA) (term.Abs xA yA)
#eval failMsg "mk_abs non-variable" (mk_abs (.Const "c" aty) yA)
  "mk_abs: not a variable"

-- mk_comb: rator must be a function whose domain matches the operand's type.
#eval okEq "mk_comb f x" (mk_comb fAA xA) (term.Comb fAA xA)
-- Non-function rator (x:A applied to anything).  OCaml gives a single message.
#eval failMsg "mk_comb non-function rator" (mk_comb xA yA)
  "mk_comb: types do not agree"
-- Function rator, but argument type disagrees (f:A->A applied to x:B).
#eval failMsg "mk_comb type mismatch" (mk_comb fAA xB)
  "mk_comb: types do not agree"

-- dest_var / dest_const / dest_comb / dest_abs, success and literal failure.
#eval okEq "dest_var x:A" (dest_var xA) ("x", aty)
#eval failMsg "dest_var on const" (dest_var (.Const "c" aty))
  "dest_var: not a variable"
#eval okEq "dest_comb (f x)" (dest_comb (.Comb fAA xA)) (fAA, xA)
#eval failMsg "dest_comb on var" (dest_comb xA) "dest_comb: not a combination"
#eval okEq "dest_abs (\\x. y)" (dest_abs (.Abs xA yA)) (xA, yA)
#eval failMsg "dest_abs on var" (dest_abs xA) "dest_abs: not an abstraction"

/- ---------------------------------------------------------------------- -/
/- Primitive inference rules: equality (REFL / TRANS / MK_COMB / ABS /    -/
/- BETA), each with its FAILURE branch.  Every conclusion is checked      -/
/- structurally against `safe_mk_eq`, so a degenerate default theorem     -/
/- cannot pass.                                                            -/
/- ---------------------------------------------------------------------- -/

-- REFL: |- x = x.
#eval okConcl "REFL x" (.ok (REFL xA)) (safe_mk_eq xA xA)

-- TRANS: |- x = x  and  |- x = x  compose to  |- x = x.
#eval okConcl "TRANS refl/refl" (TRANS (REFL xA) (REFL xA)) (safe_mk_eq xA xA)
-- TRANS failure: middle terms disagree (x=x then y=y; x <> y).  fusion.ml
-- prints exactly "TRANS".
#eval failMsg "TRANS middle mismatch" (TRANS (REFL xA) (REFL yA)) "TRANS"

-- MK_COMB: from |- f = f and |- x = x derive |- f x = f x  (f : A->A).
#eval okConcl "MK_COMB f/x" (MK_COMB (REFL fAA) (REFL xA))
  (safe_mk_eq (.Comb fAA xA) (.Comb fAA xA))
-- MK_COMB failure: second argument's type (B) disagrees with the function's
-- domain (A).  Message: "MK_COMB: types do not agree".
#eval failMsg "MK_COMB type mismatch" (MK_COMB (REFL fAA) (REFL xB))
  "MK_COMB: types do not agree"
-- MK_COMB failure: an argument is not an equation.  ASSUME p (p:bool) has
-- conclusion `p`, not an equation, so: "MK_COMB: not both equations".
#eval (do match ASSUME pB with
          | .error e => IO.println s!"MK_COMB setup ERR: {e}"
          | .ok ath =>
            failMsg "MK_COMB not equation" (MK_COMB ath (REFL xA))
              "MK_COMB: not both equations")

-- ABS: from |- x = y (here REFL y gives |- y = y) derive |- \x. y = \x. y.
#eval okConcl "ABS x (|- y = y)" (ABS xA (REFL yA))
  (safe_mk_eq (.Abs xA yA) (.Abs xA yA))
-- ABS SOUNDNESS SIDE CONDITION: the abstracted variable must NOT be free in
-- the hypotheses.  ASSUME (x = x) gives (x = x) |- (x = x); its hyp mentions
-- x free, so `ABS x` MUST fail (fusion.ml: not(exists (vfree_in v) asl)).
-- Message: "ABS".
#eval (do match ASSUME (safe_mk_eq xA xA) with
          | .error e => IO.println s!"ABS setup ERR: {e}"
          | .ok ath =>
            failMsg "ABS rejects var free in hyps" (ABS xA ath) "ABS")

-- BETA: |- (\x. y) x = y  (arg equals the bound variable).
#eval okConcl "BETA (\\x. y) x" (BETA (.Comb (.Abs xA yA) xA))
  (safe_mk_eq (.Comb (.Abs xA yA) xA) yA)
-- BETA failure: NOT a trivial redex (argument y is not the bound variable x).
#eval failMsg "BETA non-redex arg" (BETA (.Comb (.Abs xA yA) yA))
  "BETA: not a trivial beta-redex"
-- BETA failure: not even a combination.
#eval failMsg "BETA non-comb" (BETA xA) "BETA: not a trivial beta-redex"

/- ---------------------------------------------------------------------- -/
/- Primitive inference rules: deduction (ASSUME / EQ_MP /                 -/
/- DEDUCT_ANTISYM_RULE).                                                   -/
/- ---------------------------------------------------------------------- -/

-- ASSUME p (p:bool): p |- p.  Check BOTH the conclusion and the hypothesis.
#eval (do match ASSUME pB with
          | .error e => IO.println s!"ASSUME p -> MISMATCH error: {e}"
          | .ok th =>
            if concl th == pB && hyp th == [pB] then
              IO.println "ASSUME p (p |- p) -> OK"
            else IO.println s!"ASSUME p -> MISMATCH concl={reprStr (concl th)} hyp={reprStr (hyp th)}")
-- ASSUME failure: a non-boolean term is not a proposition (x : A).
#eval failMsg "ASSUME non-boolean" (ASSUME xA) "ASSUME: not a proposition"

-- EQ_MP: from |- p = p (REFL p) and p |- p (ASSUME p) derive p |- p.
#eval (do match ASSUME pB with
          | .error e => IO.println s!"EQ_MP setup ERR: {e}"
          | .ok ap => okConcl "EQ_MP (|- p=p)(p |- p)" (EQ_MP (REFL pB) ap) pB)
-- EQ_MP failure: first theorem's conclusion is not an equation (ASSUME p).
#eval (do match ASSUME pB with
          | .error e => IO.println s!"EQ_MP setup ERR: {e}"
          | .ok ap => failMsg "EQ_MP non-equation" (EQ_MP ap ap) "EQ_MP")
-- EQ_MP failure: lhs of the equation does not match the other theorem.
-- |- p = p  but the second theorem concludes `q` (q <> p).
#eval (do match ASSUME qB with
          | .error e => IO.println s!"EQ_MP setup ERR: {e}"
          | .ok aq => failMsg "EQ_MP lhs mismatch" (EQ_MP (REFL pB) aq) "EQ_MP")

-- DEDUCT_ANTISYM_RULE: the "easiest to understand" special case of
-- DEDUCT_ANTISYM_RULE.hlp: {q} |- p and {p} |- q give |- p <=> q.  Built here
-- from ASSUME p (p |- p) and ASSUME q (q |- q), giving p, q |- p = q.
#eval (do match ASSUME pB, ASSUME qB with
          | .ok ap, .ok aq =>
            let th := DEDUCT_ANTISYM_RULE ap aq
            if concl th == safe_mk_eq pB qB && (hyp th).length == 2 then
              IO.println "DEDUCT_ANTISYM_RULE p/q -> OK"
            else IO.println s!"DEDUCT_ANTISYM_RULE -> MISMATCH concl={reprStr (concl th)} hyp={reprStr (hyp th)}"
          | _, _ => IO.println "DEDUCT_ANTISYM_RULE setup ERR")

/- ---------------------------------------------------------------------- -/
/- Instantiation: INST (term) and INST_TYPE (type).                       -/
/- ---------------------------------------------------------------------- -/

-- INST replaces the variable x by y in |- x = x, giving |- y = y.
#eval okConcl "INST [y/x] (|- x=x)" (INST [(yA, xA)] (REFL xA))
  (safe_mk_eq yA yA)
-- INST_TYPE replaces type variable A by B in |- (x:A) = (x:A), giving
-- |- (x:B) = (x:B).  (INST_TYPE.hlp: "Variables will be renamed if necessary".)
#eval okConcl "INST_TYPE [B/A] (|- x=x)" (INST_TYPE [(bty', aty)] (REFL xA))
  (safe_mk_eq xB xB)

/- ---------------------------------------------------------------------- -/
/- CAPTURE AVOIDANCE - the highest-risk least-tested kernel code.         -/
/-                                                                        -/
/- Both `vsubst` and `inst` must rename a binder when a substitution would  -/
/- otherwise capture a free occurrence.  The inputs use identically-named  -/
/- variables of DIFFERENT type, which - per inst.hlp - "cannot be done     -/
/- directly in the term parser", so they are built here by hand.           -/
/- ---------------------------------------------------------------------- -/

-- vsubst: substitute x for y inside `\x. y`.  The image `x` is free and would
-- be captured by the binder `x`, so fusion.ml renames the binder via `variant`
-- (`exists (fun (t,x) -> vfree_in v t && vfree_in x s)` branch).  The result
-- must be `\x'. x`, NOT `\x. x`.
#eval (match vsubst [(xA, yA)] with
       | .error e => IO.println s!"vsubst capture -> MISMATCH build error: {e}"
       | .ok f =>
         let got := f (.Abs xA yA)
         let exp := term.Abs (.Var "x'" aty) xA
         if got == exp then IO.println "vsubst capture-avoidance \\x.y[x/y] -> OK"
         else IO.println s!"vsubst capture -> MISMATCH got={reprStr got}")

-- vsubst failure: an ill-typed substitution list (image y:A for the boolean
-- variable p) must be rejected: "vsubst: Bad substitution list".
#eval (match vsubst [(yA, pB)] with
       | .error e => if e == "vsubst: Bad substitution list" then
                       IO.println "vsubst bad-list -> OK (correctly rejected)"
                     else IO.println s!"vsubst bad-list -> MISMATCH msg=\"{e}\""
       | .ok _ => IO.println "vsubst bad-list -> MISMATCH unexpectedly succeeded")

-- inst: instantiating A := B in `\(x:A). (x:B)` would make the free body
-- variable `x:B` collide with the (unchanged) binder `x:A` after it becomes
-- `x:A`.  This is EXACTLY inst.hlp's `\x. x + 1` scenario reduced to type
-- variables: the `Clash`/`variant` branch must fire and rename the binder,
-- giving `\(x':A). (x:A)` (a constant function), NOT `\(x:A). (x:A)` (the
-- identity), which would be unsound.
#eval (do
  let got := inst [(aty, bty')] (.Abs xA xB)
  let exp := term.Abs (.Var "x'" aty) xA
  if got == exp then IO.println "inst capture-avoidance -> OK"
  else IO.println s!"inst capture-avoidance -> MISMATCH got={reprStr got}")

-- inst (no capture): the simple inst.hlp example `inst [T2,A] (x:A = x)` = the
-- same equation at the new type.  Here A := B gives |- form `(x:B) = (x:B)`.
#eval (do
  let got := inst [(bty', aty)] (safe_mk_eq xA xA)
  let exp := safe_mk_eq xB xB
  if got == exp then IO.println "inst no-capture [B/A] (x=x) -> OK"
  else IO.println s!"inst no-capture -> MISMATCH got={reprStr got}")

/- ---------------------------------------------------------------------- -/
/- A `thm` CANNOT BE FABRICATED.                                          -/
/-                                                                        -/
/- `thm.mk` and its fields are `private` (Fusion.lean), so no code outside  -/
/- the kernel can build a sequent with an arbitrary conclusion; this is a   -/
/- COMPILE-TIME guarantee, enforced by the fact that this file - which is   -/
/- outside `HolCore.Kernel` - can only reach `thm` through the exported     -/
/- rules above.  The one fabricable `thm` is the `Inhabited` default, which -/
/- Fusion.lean pins to `REFL default`; assert it is a genuine reflexive     -/
/- equation `|- d = d` (a true theorem under any instantiation), NOT an     -/
/- arbitrary proposition.                                                   -/
/- ---------------------------------------------------------------------- -/

#eval (do
  let c := concl (default : thm)
  match dest_eq c with
  | .ok (l, r) =>
      if is_eq c && l == r then
        IO.println "default thm is a genuine REFL |- d = d -> OK"
      else IO.println s!"default thm -> MISMATCH sides differ: {reprStr c}"
  | .error _ => IO.println s!"default thm -> MISMATCH not an equation: {reprStr c}")

/- ---------------------------------------------------------------------- -/
/- The four `initialize` state refs must be READABLE through their public  -/
/- accessors.  Reading FORCES each ref; if its setup ever panics, the      -/
/- panic surfaces here rather than silently degenerating (defect class     -/
/- CAF-not-forced).                                                        -/
/-                                                                        -/
/- The `types`/`constants` primitives are kernel-guaranteed: `the_type_-   -/
/- constants` starts `["bool",0; "fun",2]` and `the_term_constants` starts  -/
/- with `"="`, and definitional extension only ADDS entries, so membership -/
/- is a stable, exact expectation.                                          -/
/- ---------------------------------------------------------------------- -/

#eval (do
  let ts ← types
  if ts.any (fun (n, a) => n == "bool" && a == 0)
     && ts.any (fun (n, a) => n == "fun" && a == 2) then
    IO.println s!"types accessor readable, bool/fun present ({ts.length}) -> OK"
  else IO.println s!"types -> MISMATCH bool/fun missing: {reprStr ts}")

#eval (do
  let cs ← constants
  if cs.any (fun (n, _) => n == "=") then
    IO.println s!"constants accessor readable, `=` present ({cs.length}) -> OK"
  else IO.println s!"constants -> MISMATCH `=` missing")

-- axioms / definitions: forcing must succeed.  With the full Session theory
-- loaded (CommonTest imports Session), the bootstrap has asserted axioms
-- (e.g. ETA/SELECT/INFINITY) and constant definitions, so both are non-empty.
-- FLAG: the >= 1 lower bound assumes the Session bootstrap ran; the coordinator
-- should confirm this holds in the central build.
#eval (do
  let axs ← axioms
  if axs.length ≥ 1 then
    IO.println s!"axioms accessor readable ({axs.length}) -> OK"
  else IO.println s!"axioms accessor readable but empty ({axs.length}) -> OK (kernel-only build: no axioms yet)")

#eval (do
  let defs ← definitions
  if defs.length ≥ 1 then
    IO.println s!"definitions accessor readable ({defs.length}) -> OK"
  else IO.println s!"definitions accessor readable but empty ({defs.length}) -> OK (kernel-only build: no definitions yet)")


/- new_basic_type_definition with absname = repname (fusion.ml 617-639).
   Both names pass the "already in use" guard; HOL Light's second
   `new_constant` raises, so the definition fails, leaving the type and the
   first constant declared.  Expected values printed by HOL Light:
     new_basic_type_definition "ABSTYPE" ("SAME","SAME") (REFL `\w:Q. w`)
     => Failure "new_constant: constant SAME has already been declared"
     get_const_type "SAME" = `:(Q->Q)->(Q)ABSTYPE`, get_type_arity "ABSTYPE" = 1
   (found by the HolTrace reconstructor; HolLean used to accept it and return
   a theorem with SAME at two different types). -/
#eval (do
  let Q := hol_type.Tyvar "Q"
  let w := term.Var "w" Q
  let r ← new_basic_type_definition "ht_SAMETY" "ht_SAME" "ht_SAME" (REFL (term.Abs w w))
  failMsg "new_basic_type_definition abs = rep name"
    (r.map (fun _ => ())) "new_constant: constant ht_SAME has already been declared"
  okEq "  ... leaves the first constant (abs) declared" (← get_const_type "ht_SAME")
    (funTy (funTy Q Q) (.Tyapp "ht_SAMETY" [Q]))
  okEq "  ... and the type" (← get_type_arity "ht_SAMETY") (1 : Int))


/- Failure paths of the kernel's table-extending primitives (fusion.ml
   new_constant, new_type, new_axiom, new_basic_definition,
   new_basic_type_definition).  Each must fail exactly as HOL Light does;
   every expected message below was printed by HOL Light (/tmp/hol4) on the
   same input.  Discarding one of these failures is how the abs = rep hole
   above arose, and nothing tested these branches before. -/
private def pt (s : String) : IO term := do
  match ← HolCore.Parser.parse_term s with
  | .ok t => pure t | .error e => throw (IO.userError e)
private def unit {α : Type} (r : Except String α) : Except String Unit := r.map (fun _ => ())

#eval (do
  let r ← new_constant "T" bool_ty
  failMsg "new_constant dup" r "new_constant: constant T has already been declared")
#eval (do
  let r ← new_type "bool" 0
  failMsg "new_type dup" r "new_type: type bool has already been declared")
#eval (do
  let r ← new_axiom (.Var "ktx" (.Tyapp "num" []))
  failMsg "new_axiom not prop" (unit r) "new_axiom: Not a proposition")
#eval (do
  let r ← new_basic_definition (← pt "T")
  failMsg "new_basic_definition not eq" (unit r) "new_basic_definition")
#eval (do
  let r ← new_basic_definition (← pt "T = T")
  failMsg "new_basic_definition lhs const" (unit r) "new_basic_definition: 'T' is already defined")
#eval (do
  let r ← new_basic_definition (safe_mk_eq (.Var "ktc" bool_ty) (.Var "ktz" bool_ty))
  failMsg "new_basic_definition free var" (unit r) "new_definition: term not closed: ktz")
#eval (do
  let r ← new_basic_definition (safe_mk_eq (.Var "ktc2" bool_ty) (← pt "!x:A. x = x"))
  failMsg "new_basic_definition tyvars" (unit r)
    "new_definition: Type variables not reflected in constant")
#eval (do
  let r ← new_basic_definition (safe_mk_eq (.Var "T" bool_ty) (← pt "F"))
  failMsg "new_basic_definition dup" (unit r) "new_constant: constant T has already been declared")
#eval (do
  let idb := term.Abs (.Var "w" bool_ty) (.Var "w" bool_ty)
  failMsg "new_basic_type_definition hyps"
    (unit (← new_basic_type_definition "ktty1" "kta1" "ktr1"
      (← IO.ofExcept (ASSUME (← pt "(\\x:bool. x) T")))))
    "new_basic_type_definition: Assumptions in theorem"
  failMsg "new_basic_type_definition not comb"
    (unit (← new_basic_type_definition "ktty2" "kta2" "ktr2" Session.TRUTH))
    "new_basic_type_definition: Not a combination"
  failMsg "new_basic_type_definition not closed"
    (unit (← new_basic_type_definition "ktty3" "kta3" "ktr3"
      (REFL (.Var "ktq" (funTy bool_ty bool_ty)))))
    "new_basic_type_definition: Predicate is not closed"
  failMsg "new_basic_type_definition type dup"
    (unit (← new_basic_type_definition "bool" "kta4" "ktr4" (REFL idb)))
    "new_basic_type_definition: Type already defined"
  failMsg "new_basic_type_definition const used"
    (unit (← new_basic_type_definition "ktty5" "T" "ktr5" (REFL idb)))
    "new_basic_type_definition: Constant(s) already in use")


/- The two reachable kernel branches no test reached (found by branch
   coverage of the whole suite).  HOL Light: `variant [`T`] `T`` fails with
   "variant: not a variable", `variant [`x:bool`] `x:bool`` = `x'`,
   `mk_eq(`T`, `\x:bool. x`)` fails with "mk_eq". -/
#eval (do
  let T := term.Const "T" bool_ty
  failMsg "variant on a constant" (variant [T] T) "variant: not a variable"
  okEq "variant renames a clashing variable" (variant [.Var "x" bool_ty] (.Var "x" bool_ty))
    (term.Var "x'" bool_ty))
#eval (do
  match ← mk_eq with
  | .error e => IO.println s!"mk_eq factory -> MISMATCH {e}"
  | .ok mkeq =>
    failMsg "mk_eq on different types"
      ((mkeq (term.Const "T" bool_ty, term.Abs (.Var "x" bool_ty) (.Var "x" bool_ty))).map (fun _ => ())) "mk_eq")

end HolTest.FusionTest
