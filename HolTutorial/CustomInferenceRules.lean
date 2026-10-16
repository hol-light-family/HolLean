/- File: HolTutorial/CustomInferenceRules.lean
Translation of HOL Light's Tutorial/Custom_inference_rules.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

This tutorial implements Knuth-Bendix completion (unification, a lexicographic
path order, critical pairs, `complete_equations`) and a `COMPLETE_TAC` built on
it.  The OCaml functions are ported with the same algorithm and names; HOL
Light's kernel rules (`REFL`, `MK_COMB`, `TRANS`, `SYM`, `INST`, ...) are
`Except String`-valued here, so OCaml's `failwith`/`try ... with Failure _`
control flow becomes `Except`/`tryWith`.  The functions that print or call the
rewriting conversions (`status`, `normalize_and_orient`, `left_reducible`,
`complete`, `complete_equations`) live in `ExceptT String IO`.
-/
import HolTutorial.Common
open HolCore.Kernel HolCore.Lib HolCore.Basics Session HolLight.Syntax
     HolTutorial
open HolCore.Tactics (tactic thm_tactic)
open HolLight (tactic_of tryWith)
namespace HolTutorial.CustomInferenceRules

/-- The kernel's `Except String`-valued rules, named unambiguously (the open
    `Session` also exports `ExceptT String IO` versions of some of these). -/
abbrev kREFL := HolCore.Kernel.REFL
abbrev kTRANS := HolCore.Kernel.TRANS
abbrev kMK_COMB := HolCore.Kernel.MK_COMB
abbrev kINST := HolCore.Kernel.INST
abbrev kSYM := HolCore.Equal.SYM

/-- Apply an `ioconv` and ask (as OCaml's `can`) whether it succeeded. -/
unsafe def canIO (c : term → IO (Except String thm)) (tm : term) : IO Bool := do
  match ← c tm with
  | .ok _ => pure true
  | .error _ => pure false

#eval phrase 1
unsafe def near_ring_axioms : term :=
  keep "near_ring_axioms" fun _ =>
    [[(!x. 0 + x = x) /\
      (!x. neg x + x = 0) /\
      (!x y z. (x + y) + z = x + y + z) /\
      (!x y z. (x * y) * z = x * y * z) /\
      (!x y z. (x + y) * z = (x * z) + (y * z))]]
#eval (do IO.println s!"`{← HolCore.Printer.string_of_term near_ring_axioms}`" : IO Unit)

#eval phrase 2
-- (**** Works eventually but takes a very long time
--  MESON[] `... ==> !a. 0 * a = 0`;;  ****)  (commented out in HOL Light too)
-- let is_realvar w x = is_var x && not(mem x w);;
unsafe def is_realvar (w : List term) (x : term) : Bool := is_var x && !(mem x w)
#eval IO.println "<fun>"

#eval phrase 3
-- let rec real_strip w tm = ...
unsafe def real_strip (w : List term) (tm : term) : Except String (term × List term) :=
  if mem tm w then .ok (tm, []) else do
    let (l, r) ← dest_comb tm
    let (f, args) ← real_strip w l
    .ok (f, args ++ [r])
#eval IO.println "<fun>"

#eval phrase 4
-- let weight lis (f,n) (g,m) = ...
unsafe def weight (lis : List term) : (term × Nat) → (term × Nat) → Except String Bool :=
  fun (f, n) (g, m) => do
    let i ← index f lis
    let j ← index g lis
    .ok (i > j || i == j && n > m)
#eval IO.println "<fun>"

#eval phrase 5
-- let rec lexord ord l1 l2 = ...
unsafe def lexord {α : Type} [BEq α] (ord : α → α → Except String Bool) :
    List α → List α → Except String Bool
  | h1 :: t1, h2 :: t2 => do
      if ← ord h1 h2 then .ok (length t1 == length t2)
      else if h1 == h2 then lexord ord t1 t2 else .ok false
  | _, _ => .ok false
#eval IO.println "<fun>"

/-- OCaml's `exists`/`forall` over `Except`-valued predicates (short-circuit). -/
unsafe def existsE {α : Type} (p : α → Except String Bool) :
    List α → Except String Bool
  | [] => .ok false
  | h :: t => do if ← p h then .ok true else existsE p t
unsafe def forallE {α : Type} (p : α → Except String Bool) :
    List α → Except String Bool
  | [] => .ok true
  | h :: t => do if ← p h then forallE p t else .ok false

#eval phrase 6
-- let rec lpo_gt w s t = ... and lpo_ge w s t = (s = t) || lpo_gt w s t;;
mutual
unsafe def lpo_gt (w : List term) (s t : term) : Except String Bool :=
  if is_realvar w t then .ok (!(s == t) && mem t (frees s))
  else if is_realvar w s || is_abs s || is_abs t then .ok false else do
    let (f, fargs) ← real_strip w s
    let (g, gargs) ← real_strip w t
    if ← existsE (fun si => lpo_ge w si t) fargs then .ok true
    else do
      if ← forallE (lpo_gt w s) gargs then
        if ← (do if f == g then lexord (lpo_gt w) fargs gargs else .ok false) then
          .ok true
        else weight w (f, length fargs) (g, length gargs)
      else .ok false
unsafe def lpo_ge (w : List term) (s t : term) : Except String Bool := do
  if s == t then .ok true else lpo_gt w s t
end
#eval IO.println "<fun>"
#eval IO.println "<fun>"

#eval phrase 7
-- let rec istriv w env x t = ...
unsafe def istriv (w : List term) (env : Func term term) (x : term) (t : term) :
    Except String Bool :=
  if is_realvar w t then
    if t == x then .ok true
    else if defined env t then do istriv w env x (← apply env t)
    else .ok false
  else if is_const t then .ok false else do
    let (_f, args) := strip_comb t
    if ← existsE (istriv w env x) args then failwith "cyclic" else .ok false
#eval IO.println "<fun>"

#eval phrase 8
-- let rec unify w env tp = ...
unsafe def unify (w : List term) (env : Func term term) :
    term × term → Except String (Func term term)
  | (x, t) =>
    -- ((Var(_,_) as x),t) | (t,(Var(_,_) as x)) when not(mem x w)
    let tryVar (x t : term) : Option (Except String (Func term term)) :=
      if is_var x && !(mem x w) then
        some (do
          if defined env x then unify w env (← apply env x, t)
          else if ← istriv w env x t then .ok env else .ok ((x |-> t) env))
      else none
    match tryVar x t with
    | some r => r
    | none =>
      match tryVar t x with
      | some r => r
      | none =>
        match x, t with
        | .Comb f a, .Comb g b => do unify w (← unify w env (a, b)) (f, g)
        | s, t => if s == t then .ok env else failwith "unify: not unifiable"
#eval IO.println "<fun>"

#eval phrase 9
-- let fullunify w (s,t) = ...
unsafe def fullunify (w : List term) : term × term →
    Except String (List (term × term))
  | (s, t) => do
    let env ← unify w undefined (s, t)
    let th := (graph env).map (fun (x, t) => (t, x))
    let rec subs (tm : term) : Except String term := do
      let vs ← vsubst th
      let tm' := vs tm
      if tm' == tm then .ok tm else subs tm'
    (th.mapM (fun (t, x) => do pure ((← subs t), x)) : Except String _)
#eval IO.println "<fun>"

#eval phrase 10
-- let rec listcases fn rfn lis acc = ...
unsafe def listcases {α β : Type}
    (fn : term → (α → thm → Except String β) → Except String (List β))
    (rfn : α → List thm → Except String β) :
    List term → List β → Except String (List β)
  | [], acc => .ok acc
  | h :: t, acc => do
      let left ← fn h (fun i h' => rfn i (h' :: t.map kREFL))
      let right ← listcases fn (fun i t' => rfn i (kREFL h :: t')) t acc
      .ok (left ++ right)
#eval IO.println "<fun>"

#eval phrase 11
-- let LIST_MK_COMB f ths = rev_itlist (fun s t -> MK_COMB(t,s)) ths (REFL f);;
unsafe def LIST_MK_COMB (f : term) (ths : List thm) : Except String thm :=
  ths.foldl (fun acc s => do kMK_COMB (← acc) s) (.ok (kREFL f))
#eval IO.println "<fun>"

#eval phrase 12
-- let rec overlaps w th tm rfn = ...
unsafe def overlaps {α : Type} (w : List term) (th : thm) (tm : term)
    (rfn : List (term × term) → thm → Except String α) :
    Except String (List α) := do
  let (l, _r) ← dest_eq (concl th)
  if !(is_comb tm) then .ok [] else
    let (f, args) := strip_comb tm
    listcases (fun tm2 r => overlaps w th tm2 r)
      (fun i a => do rfn i (← LIST_MK_COMB f a)) args
      (match (do rfn (← fullunify w (l, tm)) th : Except String α) with
       | .ok v => [v]
       | .error _ => [])
#eval IO.println "<fun>"

#eval phrase 13
-- let crit1 w eq1 eq2 = ...
unsafe def crit1 (w : List term) (eq1 eq2 : thm) : Except String (List thm) := do
  let (_l1, _r1) ← dest_eq (concl eq1)
  let (l2, _r2) ← dest_eq (concl eq2)
  overlaps w eq1 l2 (fun i th => do kTRANS (← kSYM (← kINST i th)) (← kINST i eq2))
#eval IO.println "<fun>"

#eval phrase 14
-- let fixvariables s th = ...
unsafe def fixvariables (s : String) (th : thm) : Except String thm := do
  let fvs := subtract (frees (concl th)) (freesl (hyp th))
  let gvs ← map2 (fun v n => mk_var (s ++ toString n) (type_of v))
                 fvs (HolCore.Lib.upto 1 (length fvs : Int))
  kINST (← zip gvs fvs) th
#eval IO.println "<fun>"

#eval phrase 15
-- let renamepair (th1,th2) = fixvariables "x" th1,fixvariables "y" th2;;
unsafe def renamepair : thm × thm → Except String (thm × thm)
  | (th1, th2) => do pure ((← fixvariables "x" th1), (← fixvariables "y" th2))
#eval IO.println "<fun>"

#eval phrase 16
-- let critical_pairs w tha thb = ...
unsafe def critical_pairs (w : List term) (tha thb : thm) :
    Except String (List thm) := do
  let (th1, th2) ← renamepair (tha, thb)
  pure ((← crit1 w th1 th2) ++ (← crit1 w th2 th1))
#eval IO.println "<fun>"

#eval phrase 17
-- let normalize_and_orient w eqs th = ...
unsafe def normalize_and_orient (w : List term) (eqs : List thm) (th : thm) :
    ExceptT String IO thm := do
  let th' ← ExceptT.mk (Session.GEN_REWRITE_RULE HolLight.TOP_DEPTH_CONV eqs th)
  let (s', t') ← liftExcept (dest_eq (concl th'))
  if ← liftExcept (lpo_ge w s' t') then pure th'
  else if ← liftExcept (lpo_ge w t' s') then liftExcept (kSYM th')
  else throw "Can't orient equation"
#eval IO.println "<fun>"

#eval phrase 18
-- let status(eqs,crs) eqs0 = ...
unsafe def status (p : List thm × List thm) (eqs0 : List thm) : IO Unit := do
  let (eqs, crs) := p
  if eqs == eqs0 && (length crs) % 1000 != 0 then pure () else do
    IO.print (toString (length eqs) ++ " equations and " ++
              toString (length crs) ++ " pending critical pairs")
    IO.println ""
#eval IO.println "<fun>"

#eval phrase 19
-- let left_reducible eqs eq = ...
unsafe def left_reducible (eqs : List thm) (eq : thm) : IO Bool :=
  canIO (HolLight.CHANGED_CONV (Session.GEN_REWRITE_CONV (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) eqs))
        (concl eq)
#eval IO.println "<fun>"

#eval phrase 20
-- let rec complete w (eqs,crits) = ...
unsafe def complete (w : List term) :
    List thm × List thm → ExceptT String IO (List thm)
  | (eqs, crits) =>
    match crits with
    | eq :: ocrits => do
        let trip ← tryWith
          (do
            let eq' ← normalize_and_orient w eqs eq
            let (s', t') ← liftExcept (dest_eq (concl eq'))
            if s' == t' then pure (eqs, ocrits) else do
              let (crits', eqs') := partition (fun e =>
                match unsafeIO (left_reducible [eq'] e) with
                | .ok b => b | .error _ => false) eqs
              let eqs'' := eq' :: eqs'
              let cps ← (eqs''.foldrM
                (fun e acc => do pure ((← critical_pairs w eq' e) ++ acc))
                ([] : List thm) : ExceptT String IO (List thm))
              pure (eqs'', ocrits ++ crits' ++ cps))
          (do
            let anyOrient ← (ocrits.anyM (fun c => do
              match ← (normalize_and_orient w eqs c : ExceptT String IO thm).run with
              | .ok _ => pure true | .error _ => pure false) : IO Bool)
            if anyOrient then pure (eqs, ocrits ++ [eq])
            else throw "complete: no orientable equations")
        liftM (status trip eqs)
        complete w trip
    | [] => pure eqs
#eval IO.println "<fun>"

#eval phrase 21
-- let complete_equations wts eqs = ...
unsafe def complete_equations (wts : List term) (eqs : List thm) :
    ExceptT String IO (List thm) := do
  let eqs' ← eqs.mapM (normalize_and_orient wts [])
  complete wts ([], eqs')
#eval IO.println "<fun>"

/-- Print a `thm list` as the OCaml toplevel does: `[th1; th2; ...]`
    (whitespace is normalised away by the comparison). -/
unsafe def printThmList (ths : List thm) : IO Unit :=
  IO.println ("[" ++ "; ".intercalate (ths.map toString) ++ "]")

/-- Print a `term list` as the OCaml toplevel does: `` [`t1`; `t2`; ...] ``. -/
unsafe def printTermList (tms : List term) : IO Unit := do
  let parts ← tms.mapM (fun t => do pure ("`" ++ (← HolCore.Printer.string_of_term t) ++ "`"))
  IO.println ("[" ++ "; ".intercalate parts ++ "]")

/-- Run an `ExceptT String IO (List thm)` and print the result, or the
    `Exception: Failure "msg".` the toplevel would show on failure. -/
unsafe def runThmList (m : ExceptT String IO (List thm)) : IO Unit := do
  match ← m.run with
  | .ok ths => printThmList ths
  | .error e => failure e

#eval phrase 22
#eval runThmList (do
  complete_equations [([[(1:num)]]), ([[( * ):num->num->num]]), ([[i:num->num]])]
    [(← liftExcept (SPEC_ALL (← liftExcept (HolCore.Kernel.ASSUME
       [[!a b. i(a) * a * b = b]]))))])

#eval phrase 23
#eval runThmList (do
  complete_equations [([[c:A]]), ([[f:A->A]])]
    (← liftExcept ((CONJUNCTS (← liftExcept (HolCore.Kernel.ASSUME
       [[((f(f(f(f(f c))))) = c:A) /\ (f(f(f c)) = c)]]))).mapM SPEC_ALL)))

#eval phrase 24
#eval (do
  let eqs ← match (do
      let a ← HolCore.Kernel.ASSUME
        [[(!x. 1 * x = x) /\ (!x. i(x) * x = 1) /\
          (!x y z. (x * y) * z = x * y * z)]]
      (CONJUNCTS a).mapM SPEC_ALL : Except String (List thm)) with
    | .ok v => pure v
    | .error e => failure e; pure []
  match ← (complete_equations
            [([[(1:num)]]), ([[( * ):num->num->num]]), ([[i:num->num]])] eqs).run with
  | .ok ths => printTermList (ths.map concl)
  | .error e => failure e : IO Unit)

#eval phrase 25
-- let COMPLETE_TAC w th = ...
unsafe def COMPLETE_TAC (w : List term) (th : thm) : tactic := tactic_of do
  let eqs ← liftExcept ((CONJUNCTS (← liftExcept (SPEC_ALL th))).mapM SPEC_ALL)
  let eqs' ← complete_equations w eqs
  pure (MAP_EVERY (ASSUME_TAC o GEN_ALL) eqs')
#eval IO.println "<fun>"

#eval phrase 26
#eval g ([[(!x. 1 * x = x) /\
   (!x. i(x) * x = 1) /\
   (!x y z. (x * y) * z = x * y * z)
   ==> !x y. i(y) * i(i(i(x * i(y)))) * x = 1]])

#eval phrase 27
#eval e (DISCH_THEN (COMPLETE_TAC [([[(1:num)]]), ([[( * ):num->num->num]]), ([[i:num->num]])]))

#eval phrase 28
#eval e (ASM_REWRITE_TAC [])

#eval phrase 29
#eval g ([[(!x. 0 + x = x) /\
     (!x. neg x + x = 0) /\
     (!x y z. (x + y) + z = x + y + z) /\
     (!x y z. (x * y) * z = x * y * z) /\
     (!x y z. (x + y) * z = (x * z) + (y * z))
     ==> (neg 0  * (x * y + z + neg(neg(w + z))) + neg(neg b + neg a) =
          a + b)]])

#eval phrase 30
#eval e (DISCH_THEN (COMPLETE_TAC
     [([[(0:num)]]), ([[(+):num->num->num]]), ([[neg:num->num]]), ([[( * ):num->num->num]])]))

#eval phrase 31
#eval e (ASM_REWRITE_TAC [])

/- All 31 phrases are translated; `sh tools/tutorialdiff/check.sh
   Custom_inference_rules` reports "27 same, 4 differ".  The 4 remaining
   differences are irreducible OCaml-toplevel artifacts, NOT translation
   errors; the algorithm-exact completion traces and final goalstacks (P22-P31)
   all match:
   - P8, P13: HOL Light's OCaml type-checker WARNINGS (Warning 57
     ambiguous-or-pattern-guard on `unify`; Warning 26 unused variables l1/r1
     in `crit1`) are printed before `<fun>`.  A Lean port neither emits nor
     should emit OCaml compiler warnings.
   - P10, P12: OCaml prints the function's inferred type (`val listcases : ...`,
     `val overlaps : ...`) wrapped over several lines, so the `:` ends a line.
     compare.py's `val name : type =` prefix stripper only fires when the `: `
     has a trailing space on the same line, so the wrapped signature is left in
     and differs from the faithful `<fun>`.
-/

end HolTutorial.CustomInferenceRules
