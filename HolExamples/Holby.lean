/- File: HolExamples/Holby.lean
Translation of HOL Light's Examples/holby.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

A HOL "by" tactic doing Mizar-like things: congruence closure (with lazy
equations in a union-find), a first-order "unifier", and fallbacks to
arithmetic and `MESON`.  The OCaml code is ported with the same names and
algorithm.  HOL Light's kernel/derived rules are `Except String`-valued here,
so OCaml's `failwith`/`try ... with Failure _` becomes `Except`/`tryWith`;
the net stores function-valued elements so `enter'` is used (OCaml's `enter`
falls back to appending for values `compare` cannot order).
-/
import HolExamples.Common
open HolCore.Kernel HolCore.Lib HolCore.Basics Session HolLight.Syntax HolExamples
open HolCore.Tactics (tactic thm_tactic)
open HolLight (tactic_of tryWith)
open scoped HolLight
namespace HolExamples.Holby

/-- The kernel's `Except String`-valued rules, named unambiguously. -/
abbrev kREFL := HolCore.Kernel.REFL
abbrev kTRANS := HolCore.Kernel.TRANS
abbrev kMK_COMB := HolCore.Kernel.MK_COMB
abbrev kINST := HolCore.Kernel.INST
abbrev kSYM := HolCore.Equal.SYM
abbrev kABS := HolCore.Kernel.ABS

#eval phrase 1
-- let matching_enter tm y net = enter [] (tm,((fun tm' -> can (term_match [] tm) tm'),y)) net;;
unsafe def matching_enter {α : Type} (tm : term) (y : α)
    (net : HolCore.Nets.net ((term → Bool) × α)) :
    IO (Except String (HolCore.Nets.net ((term → Bool) × α))) :=
  HolCore.Nets.enter' [] (tm, ((fun tm' =>
    match unsafeIO (HolCore.Drule.term_match [] tm tm') with
    | .ok (.ok _) => true | _ => false), y)) net
#eval IO.println "<fun>"

#eval phrase 2
-- let unconditional_enter (tm,y) net = enter [] (tm,((fun t -> true),y)) net;;
unsafe def unconditional_enter {α β : Type} (p : term × α)
    (net : HolCore.Nets.net ((β → Bool) × α)) :
    IO (Except String (HolCore.Nets.net ((β → Bool) × α))) :=
  let (tm, y) := p
  HolCore.Nets.enter' [] (tm, ((fun _ => true), y)) net
#eval IO.println "<fun>"

#eval phrase 3
-- let conditional_enter (tm,condy) net = enter [] (tm,condy) net;;
unsafe def conditional_enter {α : Type} (p : term × α)
    (net : HolCore.Nets.net α) : IO (Except String (HolCore.Nets.net α)) :=
  let (tm, condy) := p
  HolCore.Nets.enter' [] (tm, condy) net
#eval IO.println "<fun>"

#eval phrase 4
-- let careful_lookup tm net = map snd (filter (fun (c,y) -> c tm) (lookup tm net));;
unsafe def careful_lookup {α : Type} (tm : term)
    (net : HolCore.Nets.net ((term → Bool) × α)) : List α :=
  ((HolCore.Nets.lookup tm net).filter (fun (c, _y) => c tm)).map Prod.snd
#eval IO.println "<fun>"

/- The kernel/derived rules, named unambiguously (the `Session` open also
   exports some of these under the same names). -/
abbrev kEQ_MP := HolCore.Kernel.EQ_MP
abbrev kALPHA := HolCore.Equal.ALPHA
abbrev kPROVE_HYP := HolCore.Equal.PROVE_HYP
abbrev kGSYM := HolLight.GSYM
abbrev lhand := HolCore.Equal.lhand
abbrev lhs := HolCore.Equal.lhs
abbrev mk_neg := HolCore.Bool.mk_neg
abbrev PINST := HolCore.Bool.PINST

/-- Run an `Except String α` or panic with HOL Light's message (as a coerced
    call that fails would). -/
unsafe def runE {α : Type} [Inhabited α] (x : Except String α) : α :=
  match x with | .ok v => v | .error e => panic! e
/-- Run an `IO (Except String α)` or panic. -/
unsafe def runIE {α : Type} [Inhabited α] (x : IO (Except String α)) : α :=
  match unsafeIO x with
  | .ok (.ok v) => v | .ok (.error e) => panic! e | .error e => panic! e.toString
/-- Run an `IO α` or panic (for `genvar` etc.). -/
unsafe def runIO {α : Type} [Inhabited α] (x : IO α) : α :=
  match unsafeIO x with | .ok v => v | .error e => panic! e.toString
/-- `mk_eq` applied (the factory lives in `IO (Except ...)`). -/
unsafe def mkEq (s t : term) : Except String term :=
  (runIE (mk_eq : IO (Except String ((term × term) → Except String term)))) (s, t)

/-- Persist a value across `#eval` phases, keyed by name (uses `Common`'s
    `keepCell`, which — unlike a module-local `IO.Ref` — survives between the
    separate `#eval` elaborations). -/
unsafe def putKeep {α : Type} (name : String) (v : α) : IO Unit :=
  keepCell.modify (·.insert name (unsafeCast v))
unsafe def getKeep {α : Type} [Inhabited α] (name : String) : α :=
  match unsafeIO (do return (← keepCell.get).get? name) with
  | .ok (some v) => unsafeCast v
  | _ => panic! s!"{name} not set"

/-- `can` for an `IO (Except String _)` action, as OCaml's `can`. -/
unsafe def canIE {α β : Type} (f : α → IO (Except String β)) (x : α) : Bool :=
  match unsafeIO (f x) with | .ok (.ok _) => true | _ => false
/-- `can` for an `Except String _` function. -/
unsafe def canE {α β : Type} (f : α → Except String β) (x : α) : Bool :=
  match f x with | .ok _ => true | .error _ => false

/-- Pure wrappers around the IO-valued net enters (as OCaml's pure `enter`
    on function-valued elements). -/
unsafe def uenter {α β : Type} (p : term × α)
    (net : HolCore.Nets.net ((β → Bool) × α)) : HolCore.Nets.net ((β → Bool) × α) :=
  runIE (unconditional_enter p net)
unsafe def center {α : Type} (p : term × α)
    (net : HolCore.Nets.net α) : HolCore.Nets.net α :=
  runIE (conditional_enter p net)

/-- A `SPLIT_THEN`-style action: `thm -> (thm list -> thm) -> thm list -> thm`. -/
abbrev splitAction := thm → (List thm → Except String thm) → List thm → Except String thm

/-- The recursive `splitthen` of `SPLIT_THEN`, taking the net and prover as
    parameters (OCaml has them closed over). -/
unsafe def splitThenGo (enet : HolCore.Nets.net ((term → Bool) × splitAction))
    (prover : List thm → Except String thm) : List thm → List thm → Except String thm
  | splat, [] => prover (rev splat)
  | splat, th :: oths =>
      let funs := careful_lookup (concl th) enet
      if funs.isEmpty then splitThenGo enet prover (th :: splat) oths
      else (runE (hd funs)) th (splitThenGo enet prover splat) oths

#eval phrase 5
/- let SPLIT_THEN = ... (see holby.ml).  The local `action_*` are given as
   top-level defs; `enet` is built in the same order as OCaml. -/
private unsafe def st_action_false (th : thm) (_f : List thm → Except String thm) (_oths : List thm) : Except String thm := .ok th
private unsafe def st_action_true (_th : thm) (f : List thm → Except String thm) (oths : List thm) : Except String thm := f oths
private unsafe def st_action_conj (th : thm) (f : List thm → Except String thm) (oths : List thm) : Except String thm :=
  f (runE (CONJUNCT1 th) :: runE (CONJUNCT2 th) :: oths)
private unsafe def st_action_disj (th : thm) (f : List thm → Except String thm) (oths : List thm) : Except String thm := do
  let th1 ← f (runE (ASSUME (runE (lhand (concl th)))) :: oths)
  let th2 ← f (runE (ASSUME (runE (rand (concl th)))) :: oths)
  DISJ_CASES th th1 th2
private unsafe def st_action_taut (tm : term) : term × splitAction :=
  let pfun := PART_MATCH lhs (runIE (TAUT tm))
  (runE (lhand tm), (fun th f oths => f (runE (kEQ_MP (runIE (pfun (concl th))) th) :: oths)))
private unsafe def st_cnet0 : HolCore.Nets.net ((term → Bool) × splitAction) := Id.run do
  let p := st_action_taut [[(p <=> q) <=> p /\ q \/ ~p /\ ~q]]
  return center (p.1, ((fun tm => type_of (runE (rand tm)) == HolCore.Kernel.bool_ty), p.2)) HolCore.Nets.empty_net
private unsafe def st_cnet1 : HolCore.Nets.net ((term → Bool) × splitAction) := Id.run do
  let p := st_action_taut [[~(p <=> q) <=> p /\ ~q \/ ~p /\ q]]
  return center (p.1, ((fun tm => type_of (runE (rand (runE (rand tm)))) == HolCore.Kernel.bool_ty), p.2)) st_cnet0
private unsafe def st_enet : HolCore.Nets.net ((term → Bool) × splitAction) :=
  itlist uenter
    [([[F]], st_action_false),
     ([[T]], st_action_true),
     ([[p /\ q]], st_action_conj),
     ([[p \/ q]], st_action_disj),
     st_action_taut [[(p ==> q) <=> ~p \/ q]],
     st_action_taut [[~F <=> T]],
     st_action_taut [[~T <=> F]],
     st_action_taut [[~(~p) <=> p]],
     st_action_taut [[~(p /\ q) <=> ~p \/ ~q]],
     st_action_taut [[~(p \/ q) <=> ~p /\ ~q]],
     st_action_taut [[~(p ==> q) <=> p /\ ~q]],
     st_action_taut [[p /\ F <=> F]],
     st_action_taut [[F /\ p <=> F]],
     st_action_taut [[p /\ T <=> p]],
     st_action_taut [[T /\ p <=> p]],
     st_action_taut [[p \/ F <=> p]],
     st_action_taut [[F \/ p <=> p]],
     st_action_taut [[p \/ T <=> T]],
     st_action_taut [[T \/ p <=> T]]]
    st_cnet1
unsafe def SPLIT_THEN (prover : List thm → Except String thm) : List thm → Except String thm :=
  splitThenGo st_enet prover []
#eval IO.println "<fun>"

/-- A `SPLIT_FOL_THEN` action. -/
abbrev folAction := thm → (List thm → Except String thm) → List thm → List thm → Except String thm

unsafe def splitFolGo (enet : HolCore.Nets.net ((term → Bool) × folAction))
    (prover : List thm → Except String thm) : List thm → List thm → Except String thm
  | splat, [] => prover (rev splat)
  | splat, th :: oths =>
      let funs := careful_lookup (concl th) enet
      if funs.isEmpty then splitFolGo enet prover (th :: splat) oths
      else (runE (hd funs)) th (splitFolGo enet prover splat) splat oths

private unsafe def sf_action_false (th : thm) (_f : List thm → Except String thm) (_splat _oths : List thm) : Except String thm := .ok th
private unsafe def sf_action_true (_th : thm) (f : List thm → Except String thm) (_splat oths : List thm) : Except String thm := f oths
private unsafe def sf_action_conj (th : thm) (f : List thm → Except String thm) (_splat oths : List thm) : Except String thm :=
  f (runE (CONJUNCT1 th) :: runE (CONJUNCT2 th) :: oths)
private unsafe def sf_action_disj (th : thm) (f : List thm → Except String thm) (_splat oths : List thm) : Except String thm := do
  let th1 ← f (runE (ASSUME (runE (lhand (concl th)))) :: oths)
  let th2 ← f (runE (ASSUME (runE (rand (concl th)))) :: oths)
  DISJ_CASES th th1 th2
private unsafe def sf_action_exists (th : thm) (f : List thm → Except String thm) (splat oths : List thm) : Except String thm := do
  let vb := runE (dest_exists (concl th))
  let v := vb.1; let bod := vb.2
  let vars := itlist (fun x acc => union (thm_frees x) acc) (oths ++ splat) (thm_frees th)
  let v' := runE (variant vars v)
  let sub := runE (vsubst [(v', v)])
  let th' := runE (ASSUME (sub bod))
  CHOOSE (v', th) (← f (th' :: oths))
private unsafe def sf_action_taut (tm : term) : term × folAction :=
  let pfun := PART_MATCH lhs (runIE (TAUT tm))
  (runE (lhand tm), (fun th f _splat oths => f (runE (kEQ_MP (runIE (pfun (concl th))) th) :: oths)))

/-- `action_fol tm` given the already-proved theorem `pth` (= prove(tm,MESON)).
    The MESON is run (and traced) by the caller, in OCaml's order. -/
private unsafe def sf_action_fol_of (tm : term) (pth : thm) : term × folAction :=
  let pfun := PART_MATCH lhs pth
  (runE (lhand tm), (fun th f _splat oths => f (runE (kEQ_MP (runIE (pfun (concl th))) th) :: oths)))

/-- The `SPLIT_FOL_THEN` net, built once at phrase 6 (so the two `action_fol`
    MESON proofs trace there).  `none` until then. -/
unsafe def sfEnetRef : IO.Ref (Option (HolCore.Nets.net ((term → Bool) × folAction))) := unsafeBaseIO (IO.mkRef none)

#eval phrase 6
unsafe def SPLIT_FOL_THEN (prover : List thm → Except String thm) : List thm → Except String thm :=
  splitFolGo (getKeep "holbySfEnet") prover []
#eval (do
  -- OCaml `::` is right-to-left: prove fol2 (the longer one) before fol1.
  let fol2tm : term := [[(!x. P x /\ Q x) <=> (!x. P x) /\ (!x. Q x)]]
  let pth2 ← Session.prove fol2tm (MESON_TAC [])
  let fol1tm : term := [[~(!x. P x) <=> (?x. ~(P x))]]
  let pth1 ← Session.prove fol1tm (MESON_TAC [])
  let e2 := sf_action_fol_of fol2tm (runE pth2)
  let e1 := sf_action_fol_of fol1tm (runE pth1)
  let net : HolCore.Nets.net ((term → Bool) × folAction) := itlist uenter
    [([[F]], sf_action_false),
     ([[T]], sf_action_true),
     ([[p /\ q]], sf_action_conj),
     ([[p \/ q]], sf_action_disj),
     ([[?x. P x]], sf_action_exists),
     sf_action_taut [[~(~p) <=> p]],
     sf_action_taut [[~(p /\ q) <=> ~p \/ ~q]],
     sf_action_taut [[~(p \/ q) <=> ~p /\ ~q]],
     e1, e2]
    HolCore.Nets.empty_net
  putKeep "holbySfEnet" net
  IO.println "<fun>")

#eval phrase 7
/- let CORRELATE_RULE = PURE_REWRITE_RULE [...].  OCaml builds the rewrite list
   at definition time; `::` is right-to-left so `prove(...,MESON_TAC[])` (the
   last element) is evaluated first, tracing here. -/
unsafe def CORRELATE_RULE (th : thm) : IO (Except String thm) :=
  PURE_REWRITE_RULE (getKeep "holbyCorrelate") th
#eval (do
  let r17 ← Session.prove ([[(?x. P x) <=> ~(!x. ~(P x))]]) (MESON_TAC [])
  let r16 ← (kGSYM DISJ_ASSOC).run
  let r15 ← (kGSYM CONJ_ASSOC).run
  let r14 ← TAUT [[p \/ F <=> p]]
  let r13 ← TAUT [[F \/ p <=> p]]
  let r12 ← TAUT [[p \/ T <=> T]]
  let r11 ← TAUT [[T \/ p <=> T]]
  let r10 ← TAUT [[p /\ F <=> F]]
  let r9 ← TAUT [[F /\ p <=> F]]
  let r8 ← TAUT [[p /\ T <=> p]]
  let r7 ← TAUT [[T /\ p <=> p]]
  let r6 ← TAUT [[~F <=> T]]
  let r5 ← TAUT [[~T <=> F]]
  let r4 ← TAUT [[~(~a) <=> a]]
  let r2 ← TAUT [[(a ==> b) <=> ~a \/ b]]
  let r1 ← TAUT [[(a <=> b) <=> (a ==> b) /\ (b ==> a)]]
  let r3 := DE_MORGAN_THM
  putKeep "holbyCorrelate" ([runE r1, runE r2, r3, runE r4, runE r5, runE r6,
    runE r7, runE r8, runE r9, runE r10, runE r11, runE r12, runE r13, runE r14,
    runE r15, runE r16, runE r17] : List thm)
  IO.println "<fun>")

#eval phrase 8
/- let THMLIST_CONTR_RULE = ... -/
unsafe def THMLIST_CONTR_RULE (ths : List thm) : Except String thm := do
  let CONTR_PAIR_THM := runE (UNDISCH_ALL (runIE (TAUT [[p ==> ~p ==> F]])))
  let p_tm : term := [[p:bool]]
  let (ths_n, ths_p) := partition (fun t => is_neg (concl t)) ths
  let th_n ← find (fun thn => let tm := runE (rand (concl thn))
                              exists' (fun t => aconv tm (concl t)) ths_p) ths_n
  let tm := runE (rand (concl th_n))
  let th_p ← find (fun t => aconv tm (concl t)) ths_p
  pure (itlist (fun x acc => runE (kPROVE_HYP x acc)) [th_p, th_n] (runE (kINST [(tm, p_tm)] CONTR_PAIR_THM)))
#eval IO.println "<fun>"

/-- `THMLIST_CONTR_RULE` as an `Except` (catchable, for PRECHECKER's `try`). -/
unsafe def thmlistContr (ths : List thm) : Except String thm := THMLIST_CONTR_RULE ths

/-- `CORRELATE_RULE` as a pure `thm → thm` (for `map`). -/
unsafe def correlateRule (th : thm) : thm := runIE (CORRELATE_RULE th)

#eval phrase 9
/- let PRECHECKER_THEN prover = SPLIT_THEN (fun ths -> try ...) -/
unsafe def PRECHECKER_THEN (prover : List thm → Except String thm) : List thm → Except String thm :=
  SPLIT_THEN (fun ths =>
    match thmlistContr ths with
    | .ok t => .ok t
    | .error _ => SPLIT_FOL_THEN prover (ths.map correlateRule))
#eval IO.println "<fun>"

#eval phrase 10
-- type lazyeq = Lazy of (term * term) * (unit -> thm);;
inductive lazyeq where
  | Lazy : (term × term) → (Unit → thm) → lazyeq
unsafe instance : Inhabited lazyeq := ⟨.Lazy (default, default) (fun () => default)⟩
#eval IO.println "type lazyeq = Lazy of (term * term) * (unit -> thm)"

#eval phrase 11
/- let cache f = let store = ref TRUTH in fun () -> ... -/
unsafe def cache (f : Unit → thm) : Unit → thm :=
  let store : IO.Ref thm := unsafeBaseIO (IO.mkRef TRUTH)
  fun () =>
    let th := unsafeBaseIO store.get
    if is_eq (concl th) then th
    else
      let th' := f ()
      let _ := unsafeBaseIO (store.set th')
      th'
#eval IO.println "<fun>"

#eval phrase 12
-- let lazy_eq th = Lazy((dest_eq(concl th)),(fun () -> th));;
unsafe def lazy_eq (th : thm) : lazyeq := .Lazy (runE (dest_eq (concl th))) (fun () => th)
#eval IO.println "<fun>"

#eval phrase 13
-- let lazy_eval (Lazy(_,f)) = f();;
unsafe def lazy_eval : lazyeq → thm | .Lazy _ f => f ()
#eval IO.println "<fun>"

#eval phrase 14
-- let REFL' t = Lazy((t,t),cache(fun () -> REFL t));;
unsafe def REFL' (t : term) : lazyeq := .Lazy (t, t) (cache (fun () => kREFL t))
#eval IO.println "<fun>"

#eval phrase 15
-- let SYM' = fun (Lazy((t,t'),f)) -> Lazy((t',t),cache(fun () -> SYM(f ())));;
unsafe def SYM' : lazyeq → lazyeq | .Lazy (t, t') f => .Lazy (t', t) (cache (fun () => runE (kSYM (f ()))))
#eval IO.println "<fun>"

#eval phrase 16
-- let TRANS' = fun (Lazy((s,s'),f)) (Lazy((t,t'),g)) -> ...
unsafe def TRANS' : lazyeq → lazyeq → Except String lazyeq
  | .Lazy (s, s') f, .Lazy (t, t') g =>
    if !(aconv s' t) then failwith "TRANS'"
    else .ok (.Lazy (s, t') (cache (fun () => runE (kTRANS (f ()) (g ())))))
#eval IO.println "<fun>"

#eval phrase 17
-- let MK_COMB' = fun (Lazy((s,s'),f),Lazy((t,t'),g)) -> ...
unsafe def MK_COMB' : lazyeq × lazyeq → lazyeq
  | (.Lazy (s, s') f, .Lazy (t, t') g) =>
    .Lazy (runE (mk_comb s t), runE (mk_comb s' t'))
      (cache (fun () => runE (kMK_COMB (f ()) (g ()))))
#eval IO.println "<fun>"

#eval phrase 18
-- let concl' = fun (Lazy(tmp,g)) -> tmp;;
unsafe def concl' : lazyeq → term × term | .Lazy tmp _g => tmp
#eval IO.println "<fun>"

#eval phrase 19
-- let successors tm = try let f,x = dest_comb tm in [f;x] with Failure _ -> [];;
unsafe def successors (tm : term) : List term :=
  match dest_comb tm with | .ok (f, x) => [f, x] | .error _ => []
#eval IO.println "<fun>"

#eval phrase 20
-- let predecessor_function tms = itlist (fun x -> itlist (fun y f -> (y |-> insert x (tryapplyd f y [])) f) (successors x)) tms undefined;;
unsafe def predecessor_function (tms : List term) : Func term (List term) :=
  itlist (fun x acc => itlist (fun y f => (y |-> insert x (tryapplyd f y [])) f) (successors x) acc)
         tms undefined
#eval IO.println "<fun>"

#eval phrase 21
-- type termnode = Nonterminal of lazyeq | Terminal of term * term list;;
inductive termnode where
  | Nonterminal : lazyeq → termnode
  | Terminal : term → List term → termnode
#eval IO.println "type termnode = Nonterminal of lazyeq | Terminal of term * term list"

#eval phrase 22
-- type termequivalence = Equivalence of (term,termnode)func;;
inductive termequivalence where
  | Equivalence : Func term termnode → termequivalence
#eval IO.println "type termequivalence = Equivalence of (term, termnode) func"

#eval phrase 23
-- let rec terminus (Equivalence f as eqv) a = ...
unsafe def terminus : termequivalence → term → Except String (lazyeq × List term)
  | eqv@(.Equivalence f), a => do
    match ← apply f a with
    | .Nonterminal th =>
        let b := (concl' th).2
        let (th', n) ← terminus eqv b
        pure (← TRANS' th th', n)
    | .Terminal t n => pure (REFL' t, n)
#eval IO.println "<fun>"

#eval phrase 24
-- let tryterminus eqv a = try terminus eqv a with Failure _ -> (REFL' a,[a]);;
unsafe def tryterminus (eqv : termequivalence) (a : term) : lazyeq × List term :=
  match terminus eqv a with | .ok p => p | .error _ => (REFL' a, [a])
#eval IO.println "<fun>"

#eval phrase 25
-- let canonize eqv a = fst(tryterminus eqv a);;
unsafe def canonize (eqv : termequivalence) (a : term) : lazyeq := (tryterminus eqv a).1
#eval IO.println "<fun>"

#eval phrase 26
-- let equate th (Equivalence f as eqv) = ...
unsafe def equate (th : lazyeq) : termequivalence → termequivalence
  | eqv@(.Equivalence f) =>
    let ab := concl' th
    let a := ab.1; let b := ab.2
    let (ath, na) := tryterminus eqv a
    let (bth, nb) := tryterminus eqv b
    let a' := (concl' ath).2; let b' := (concl' bth).2
    .Equivalence
      (if a' == b' then f
       else if length na <= length nb then
         let th' := runE (TRANS' (runE (TRANS' (SYM' ath) th)) bth)
         (a' |-> .Nonterminal th') ((b' |-> .Terminal b' (na ++ nb)) f)
       else
         let th' := runE (TRANS' (SYM' (runE (TRANS' th bth))) ath)
         (b' |-> .Nonterminal th') ((a' |-> .Terminal a' (na ++ nb)) f))
#eval IO.println "<fun>"

#eval phrase 27
-- let unequal = Equivalence undefined;;
unsafe def unequal : termequivalence := .Equivalence undefined
#eval IO.println "val unequal : termequivalence = Equivalence <func>"

#eval phrase 28
-- let equated (Equivalence f) = dom f;;
unsafe def equated : termequivalence → List term | .Equivalence f => dom f
#eval IO.println "<fun>"

#eval phrase 29
-- let prove_equal eqv (s,t) = ... (sth, tth unused warnings in OCaml)
unsafe def prove_equal (eqv : termequivalence) : term × term → Except String lazyeq
  | (s, t) =>
    let _sth := canonize eqv s
    let _tth := canonize eqv t
    TRANS' (canonize eqv s) (SYM' (canonize eqv t))
#eval IO.println "<fun>"

#eval phrase 30
-- let equivalence_class eqv a = snd(tryterminus eqv a);;
unsafe def equivalence_class (eqv : termequivalence) (a : term) : List term := (tryterminus eqv a).2
#eval IO.println "<fun>"

#eval phrase 31
-- let provecongruent eqv (tm1,tm2) = ...
unsafe def provecongruent (eqv : termequivalence) : term × term → Except String lazyeq
  | (tm1, tm2) => do
    let (f1, x1) ← dest_comb tm1
    let (f2, x2) ← dest_comb tm2
    pure (MK_COMB' (← prove_equal eqv (f1, f2), ← prove_equal eqv (x1, x2)))
#eval IO.println "<fun>"

#eval phrase 32
-- let rec emerge th (eqv,pfn) = ...
unsafe def emerge (th : lazyeq) : termequivalence × Func term (List term) →
    termequivalence × Func term (List term)
  | (eqv, pfn) =>
    let st := concl' th
    let s := st.1; let t := st.2
    let sth := canonize eqv s; let tth := canonize eqv t
    let s' := (concl' sth).2; let t' := (concl' tth).2
    if s' == t' then (eqv, pfn) else
    let sp := tryapplyd pfn s' []; let tp := tryapplyd pfn t' []
    let eqv' := equate th eqv
    let stth := canonize eqv' s'
    let sttm := (concl' stth).2
    let pfn' := (sttm |-> union sp tp) pfn
    itlist (fun (uv : term × term) (eqp : termequivalence × Func term (List term)) =>
             match provecongruent eqp.1 (uv.1, uv.2) with
             | .ok thuv => emerge thuv eqp
             | .error _ => eqp)
           (allpairs (fun u v => (u, v)) sp tp) (eqv', pfn')
#eval IO.println "<fun>"

#eval phrase 33
-- let rec supersubterms tms tm = ...
unsafe def supersubterms (tms : List term) (tm : term) : List term :=
  let p := if mem tm tms then ([tm], tms.filter (fun t => t != tm)) else ([], tms)
  let ltms := p.1; let tms' := p.2
  if tms'.isEmpty then ltms else
  let stms := match dest_comb tm with
    | .ok (l, r) => union (supersubterms tms' l) (supersubterms tms' r)
    | .error _ => []
  if stms.isEmpty then ltms else tm :: stms
#eval IO.println "<fun>"

#eval phrase 34
-- let term_universe tms = setify (itlist ((@) o supersubterms tms) tms []);;
unsafe def term_universe (tms : List term) : List term :=
  setify (itlist (fun x acc => supersubterms tms x ++ acc) tms [])
#eval IO.println "<fun>"

#eval phrase 35
-- let congruence_closure tms eqs = let pfn = ... in let eqv,_ = itlist emerge eqs (unequal,pfn) in eqv;;
unsafe def congruence_closure (tms : List term) (eqs : List lazyeq) : termequivalence :=
  let pfn := predecessor_function tms
  (itlist emerge eqs (unequal, pfn)).1
#eval IO.println "<fun>"

#eval phrase 36
-- let CCPROVE eqs eq = ...
unsafe def CCPROVE (eqs : List lazyeq) (eq : term) : Except String lazyeq :=
  let tps := runE (dest_eq eq) :: eqs.map concl'
  let otms := itlist (fun (xy : term × term) l => xy.1 :: xy.2 :: l) tps []
  let tms := term_universe (setify otms)
  let eqv := congruence_closure tms eqs
  prove_equal eqv (runE (dest_eq eq))
#eval IO.println "<fun>"

#eval phrase 37
-- let CONGRUENCE_CLOSURE tm = ...
unsafe def CONGRUENCE_CLOSURE (tm : term) : Except String thm :=
  if is_imp tm then do
    let (eqs, eq) ← dest_imp tm
    DISCH eqs (lazy_eval (← CCPROVE ((CONJUNCTS (runE (ASSUME eqs))).map lazy_eq) eq))
  else do pure (lazy_eval (← CCPROVE [] tm))
#eval IO.println "<fun>"

#eval phrase 38
-- let CONGRUENCE_CLOSURE_CONTR ths = ...
unsafe def CONGRUENCE_CLOSURE_CONTR (ths : List thm) : Except String thm := do
  let (nths, pths) := partition (fun t => is_neg (concl t)) ths
  let peqs := pths.filter (fun t => is_eq (concl t))
  let neqs := nths.filter (fun t => is_eq (runE (rand (concl t))))
  let tps := peqs.map (fun t => runE (dest_eq (concl t))) ++
             neqs.map (fun t => runE (dest_eq (runE (rand (concl t)))))
  let otms := itlist (fun (xy : term × term) l => xy.1 :: xy.2 :: l) tps []
  let tms := term_universe (setify otms)
  let eqv := congruence_closure tms (peqs.map lazy_eq)
  let prover (th : thm) : Except String thm := do
    let eq ← dest_eq (runE (rand (concl th)))
    let lth ← prove_equal eqv eq
    kEQ_MP (runE (EQF_INTRO th)) (lazy_eval lth)
  tryfind prover neqs
#eval IO.println "<fun>"

#eval phrase 39
-- let ABS' v = fun (Lazy((s,t),f)) -> Lazy((mk_abs(v,s),mk_abs(v,t)),cache(fun () -> ABS v (f ())));;
unsafe def ABS' (v : term) : lazyeq → lazyeq
  | .Lazy (s, t) f => .Lazy (runE (mk_abs v s), runE (mk_abs v t)) (cache (fun () => runE (kABS v (f ()))))
#eval IO.println "<fun>"

#eval phrase 40
-- let ALPHA_EQ' s' t' = fun (Lazy((s,t),f) as inp) -> ...
unsafe def ALPHA_EQ' (s' t' : term) : lazyeq → lazyeq
  | inp@(.Lazy (s, t) f) =>
    if s' == s && t' == t then inp else
    .Lazy (s', t')
      (cache (fun () => runE (kEQ_MP (runE (kALPHA (runE (mkEq s t)) (runE (mkEq s' t')))) (f ()))))
#eval IO.println "<fun>"

#eval phrase 41
-- let rec PROVE_EQUAL eqv (tm1,tm2 as tmp) = ...
unsafe def PROVE_EQUAL (eqv : termequivalence) : term × term → Except String lazyeq
  | tmp@(tm1, tm2) =>
    if tm1 == tm2 then .ok (REFL' tm1) else
    match prove_equal eqv tmp with
    | .ok le => .ok le
    | .error _ =>
      if is_comb tm1 && is_comb tm2 then do
        let (f1, x1) ← dest_comb tm1
        let (f2, x2) ← dest_comb tm2
        pure (MK_COMB' (← PROVE_EQUAL eqv (f1, f2), ← PROVE_EQUAL eqv (x1, x2)))
      else if is_abs tm1 && is_abs tm2 then do
        let (x1, bod1) ← dest_abs tm1
        let (x2, bod2) ← dest_abs tm2
        let gv := runIO (genvar (type_of x1))
        let sub1 ← vsubst [(gv, x1)]
        let sub2 ← vsubst [(gv, x2)]
        pure (ALPHA_EQ' tm1 tm2 (ABS' x1 (← PROVE_EQUAL eqv (sub1 bod1, sub2 bod2))))
      else failwith "PROVE_EQUAL"
#eval IO.println "<fun>"

#eval phrase 42
-- let PROVE_EQUIVALENT eqv tm1 tm2 = lazy_eval (PROVE_EQUAL eqv (tm1,tm2));;
unsafe def PROVE_EQUIVALENT (eqv : termequivalence) (tm1 tm2 : term) : Except String thm := do
  pure (lazy_eval (← PROVE_EQUAL eqv (tm1, tm2)))
#eval IO.println "<fun>"

#eval phrase 43
-- let PROVE_COMPLEMENTARY eqv th1 th2 = ...
unsafe def PROVE_COMPLEMENTARY (eqv : termequivalence) (th1 th2 : thm) : Except String thm := do
  let tm1 := concl th1; let tm2 := concl th2
  if is_neg tm1 then do
    let th ← PROVE_EQUIVALENT eqv (← rand tm1) tm2
    kEQ_MP (runE (EQF_INTRO th1)) (← kEQ_MP (← kSYM th) th2)
  else if is_neg tm2 then do
    let th ← PROVE_EQUIVALENT eqv (← rand tm2) tm1
    kEQ_MP (runE (EQF_INTRO th2)) (← kEQ_MP (← kSYM th) th1)
  else failwith "PROVE_COMPLEMENTARY"
#eval IO.println "<fun>"

#eval phrase 44
-- let rec test_eq eqv (tm1,tm2) env = ...
unsafe def test_eq (eqv : termequivalence) : term × term → List (term × term) → Bool
  | (tm1, tm2), env =>
    if is_comb tm1 && is_comb tm2 then
      let (f1, x1) := runE (dest_comb tm1)
      let (f2, x2) := runE (dest_comb tm2)
      test_eq eqv (f1, f2) env && test_eq eqv (x1, x2) env
    else if is_abs tm1 && is_abs tm2 then
      let (x1, bod1) := runE (dest_abs tm1)
      let (x2, bod2) := runE (dest_abs tm2)
      let gv := runIO (genvar (type_of x1))
      test_eq eqv (runE (vsubst [(gv, x1)]) bod1, runE (vsubst [(gv, x2)]) bod2) env
    else if is_var tm1 && canE (fun a => rev_assoc a env) tm1 then
      test_eq eqv (runE (rev_assoc tm1 env), tm2) []
    else canE (fun p => prove_equal eqv p) (tm1, tm2)
#eval IO.println "<fun>"

#eval phrase 45
-- let rec term_equivs eqv tm = ...
unsafe def term_equivs (eqv : termequivalence) (tm : term) : List term :=
  let l := equivalence_class eqv tm
  if l != [tm] then l
  else if is_comb tm then
    let (f, x) := runE (dest_comb tm)
    allpairs (fun a b => runE (mk_comb a b)) (term_equivs eqv f) (term_equivs eqv x)
  else if is_abs tm then
    let (v, bod) := runE (dest_abs tm)
    let gv := runIO (genvar (type_of v))
    (term_equivs eqv (runE (vsubst [(gv, v)]) bod)).map (fun t => runE (alpha v (runE (mk_abs gv t))))
  else [tm]
#eval IO.println "<fun>"

#eval phrase 46
-- let rec GENSPEC th = ...
unsafe def GENSPEC (th : thm) : thm :=
  let tm := concl th
  if is_forall tm then
    let v := runE (bndvar (runE (rand tm)))
    let gv := runIO (genvar (type_of v))
    GENSPEC (runE (SPEC gv th))
  else if is_conj tm then
    let (th1, th2) := runE (CONJ_PAIR th)
    runE (CONJ (GENSPEC th1) (GENSPEC th2))
  else if is_disj tm then
    let th1 := GENSPEC (runE (ASSUME (runE (lhand tm))))
    let th2 := GENSPEC (runE (ASSUME (runE (rand tm))))
    let th3 := runE (DISJ1 th1 (concl th2))
    let th4 := runE (DISJ2 (concl th1) th2)
    runE (DISJ_CASES th th3 th4)
  else th
#eval IO.println "<fun>"

#eval phrase 47
-- let rec term_fmatch vars vtm ctm env = ...
unsafe def term_fmatch (vars : List term) : term → term → List (term × term) → Except String (List (term × term))
  | vtm, ctm, env =>
    if mem vtm vars then
      if canE (fun a => rev_assoc a env) vtm then
        term_fmatch vars (runE (rev_assoc vtm env)) ctm env
      else if aconv vtm ctm then .ok env else .ok ((ctm, vtm) :: env)
    else if is_comb vtm && is_comb ctm then do
      let (fv, xv) ← dest_comb vtm
      let (fc, xc) ← dest_comb ctm
      term_fmatch vars fv fc (← term_fmatch vars xv xc env)
    else if is_abs vtm && is_abs ctm then do
      let (xv, bodv) ← dest_abs vtm
      let (xc, bodc) ← dest_abs ctm
      let gv := runIO (genvar (type_of xv)); let gc := runIO (genvar (type_of xc))
      let gbodv := (← vsubst [(gv, xv)]) bodv
      let gbodc := (← vsubst [(gc, xc)]) bodc
      term_fmatch (gv :: vars) gbodv gbodc ((gc, gv) :: env)
    else if vtm == ctm then .ok env
    else failwith "term_fmatch"
#eval IO.println "<fun>"

#eval phrase 48
-- let rec check_consistency env = ...
unsafe def check_consistency : List (term × term) → Bool
  | [] => true
  | (_c, v) :: es => forall' (fun (cv : term × term) => cv.2 != v || cv.1 == _c) es && check_consistency es
#eval IO.println "<fun>"

#eval phrase 49
-- let separate_insts env = ...
unsafe def separate_insts (env : List (term × term)) :
    Except String (List (term × term) × List (hol_type × hol_type)) := do
  let tyin ← itlist (fun (cv : term × term) acc =>
      acc.bind (type_match (type_of cv.2) (type_of cv.1))) env (.ok [])
  let ifn := fun (cv : term × term) => (inst tyin cv.1, inst tyin cv.2)
  let tmin := setify (env.map ifn)
  if check_consistency tmin then pure (tmin, tyin)
  else failwith "separate_insts"
#eval IO.println "<fun>"

#eval phrase 50
-- let first_order_match vars vtm ctm env = ...
unsafe def first_order_match (vars : List term) (vtm ctm : term) (env : List (term × term)) :
    Except String (List (term × term)) := do
  let env' ← term_fmatch vars vtm ctm env
  if canE separate_insts env' then .ok env' else failwith "first_order_match"
#eval IO.println "<fun>"

#eval phrase 51
-- let matchleaves = let rec matchleaves vars vtm ctms env cont = ... in fun ...
unsafe def matchleavesGo (vars : List term) :
    term → List term → List (term × term) → (List (term × term) → Except String (List (term × term))) →
    Except String (List (term × term))
  | vtm, ctms, env, cont =>
    if is_conj vtm then
      match matchleavesGo vars (runE (rand vtm)) ctms env cont with
      | .ok r => pure r
      | .error _ => matchleavesGo vars (runE (lhand vtm)) ctms env cont
    else if is_disj vtm then
      matchleavesGo vars (runE (lhand vtm)) ctms env
        (fun e => matchleavesGo vars (runE (rand vtm)) ctms e cont)
    else
      tryfind (fun ctm => do cont (← first_order_match vars vtm ctm env)) ctms
unsafe def matchleaves (vars : List term) (vtm : term) (ctms : List term) (env : List (term × term)) :
    Except String (List (term × term)) :=
  matchleavesGo vars vtm ctms env (fun e => .ok e)
#eval IO.println "<fun>"

#eval phrase 52
-- let rec REFUTE_LEAVES eqv cths th = ...
unsafe def REFUTE_LEAVES (eqv : termequivalence) (cths : List thm) (th : thm) : Except String thm :=
  let tm := concl th
  if is_conj tm then
    match REFUTE_LEAVES eqv cths (runE (CONJUNCT1 th)) with
    | .ok r => pure r
    | .error _ => REFUTE_LEAVES eqv cths (runE (CONJUNCT2 th))
  else if is_disj tm then do
    let th1 ← REFUTE_LEAVES eqv cths (runE (ASSUME (runE (lhand tm))))
    let th2 ← REFUTE_LEAVES eqv cths (runE (ASSUME (runE (rand tm))))
    DISJ_CASES th th1 th2
  else
    tryfind (fun cth => PROVE_COMPLEMENTARY eqv th cth) cths
#eval IO.println "<fun>"

#eval phrase 53
-- let negate tm = if is_neg tm then rand tm else mk_neg tm;;
unsafe def negate (tm : term) : term := if is_neg tm then runE (rand tm) else runE (mk_neg tm)
#eval IO.println "<fun>"

#eval phrase 54
-- let MIZAR_UNIFIER eqv ths th = ...
unsafe def MIZAR_UNIFIER (eqv : termequivalence) (ths : List thm) (th : thm) : Except String thm := do
  let gth := GENSPEC th
  let vtm := concl gth
  let vars := subtract (frees vtm) (frees (concl th))
  let ctms := ths.map (fun t => negate (concl t))
  let allctms := itlist (fun c acc => union (term_equivs eqv c) acc) ctms []
  let env ← matchleaves vars vtm allctms []
  let (tmin, tyin) ← separate_insts env
  REFUTE_LEAVES eqv ths (runE (PINST tyin tmin gth))
#eval IO.println "<fun>"

#eval phrase 55
-- let rec DISEQUALITIES ths = ...
unsafe def DISEQUALITIES : List thm → List thm
  | [] => []
  | th :: oths =>
    let (t1, t2) := runE (dest_eq (runE (rand (concl th))))
    let (f1, args1) := strip_comb t1
    let (f2, args2) := strip_comb t2
    if f1 != f2 || length args1 != length args2 then
      th :: runIE (kGSYM th) :: DISEQUALITIES oths else
    let zargs := runE (zip args1 args2)
    let diffs := zargs.filter (fun (a : term × term) => a.1 != a.2)
    if length diffs != 1 then th :: runIE (kGSYM th) :: DISEQUALITIES oths else
    let eths := zargs.map (fun (a : term × term) =>
      if a.1 == a.2 then kREFL a.1 else runE (ASSUME (runE (mkEq a.1 a.2))))
    let th1 := rev_itlist (fun x y => runE (kMK_COMB y x)) eths (kREFL f1)
    let th2 := runE (MP (runIE (GEN_REWRITE_RULE HolCore.Lib.I [runIE (kGSYM CONTRAPOS_THM)] (runE (DISCH_ALL th1)))) th)
    th :: runIE (kGSYM th) :: DISEQUALITIES (th2 :: oths)
#eval IO.println "<fun>"

#eval phrase 56
-- let ATOMINEQUALITIES th1 th2 = ...
unsafe def ATOMINEQUALITIES (th1 th2 : thm) : List thm :=
  let t1 := concl th1; let t2' := concl th2
  let t2 := runE (dest_neg t2')
  let (f1, args1) := strip_comb t1
  let (f2, args2) := strip_comb t2
  if f1 != f2 || length args1 != length args2 then [] else
  let zargs := runE (zip args1 args2)
  let diffs := zargs.filter (fun (a : term × term) => a.1 != a.2)
  if length diffs != 1 then [] else
  let eths := zargs.map (fun (a : term × term) =>
    if a.1 == a.2 then kREFL a.1 else runE (ASSUME (runE (mkEq a.1 a.2))))
  let th3 := rev_itlist (fun x y => runE (kMK_COMB y x)) eths (kREFL f1)
  let th4 := runE (kEQ_MP (runE (kTRANS th3 (runE (EQF_INTRO th2)))) th1)
  let th5 := runE (NOT_INTRO (itlist (fun (d : term × term) acc => runE (DISCH (runE (mkEq d.1 d.2)) acc)) diffs th4))
  [itlist (fun x acc => runE (kPROVE_HYP x acc)) [th1, th2] th5]
#eval IO.println "<fun>"

#eval phrase 57
-- let BASIC_MIZARBY ths = try ... with Failure _ -> failwith "BASIC_MIZARBY";;
unsafe def BASIC_MIZARBY (ths : List thm) : Except String thm :=
  (do
    let (nths, pths) := partition (fun t => is_neg (concl t)) ths
    let (peqs, pneqs) := partition (fun t => is_eq (concl t)) pths
    let (neqs, nneqs) := partition (fun t => is_eq (runE (rand (concl t)))) nths
    let tps := peqs.map (fun t => runE (dest_eq (concl t))) ++
               neqs.map (fun t => runE (dest_eq (runE (rand (concl t)))))
    let otms := itlist (fun (xy : term × term) l => xy.1 :: xy.2 :: l) tps []
    let tms := term_universe (setify otms)
    let eqv := congruence_closure tms (peqs.map lazy_eq)
    let eqprover (th : thm) : Except String thm := do
      let (s, t) ← dest_eq (runE (rand (concl th)))
      let th' ← PROVE_EQUIVALENT eqv s t
      kEQ_MP (runE (EQF_INTRO th)) th'
    let contrprover (thp thn : thm) : Except String thm := do
      let th ← PROVE_EQUIVALENT eqv (concl thp) (runE (rand (concl thn)))
      kEQ_MP (runE (kTRANS th (runE (EQF_INTRO thn)))) thp
    match tryfind eqprover neqs with
    | .ok r => pure r
    | .error _ =>
    match tryfind (fun thp => tryfind (fun thn => contrprover thp thn) nneqs) pneqs with
    | .ok r => pure r
    | .error _ =>
      let new_neqs := unions (allpairs ATOMINEQUALITIES pneqs nneqs)
      let allths := pneqs ++ nneqs ++ peqs ++ DISEQUALITIES (neqs ++ new_neqs)
      tryfind (fun th => MIZAR_UNIFIER eqv allths th) (allths.filter (fun t => is_forall (concl t)))
  ).mapError (fun _ => "BASIC_MIZARBY")
#eval IO.println "<fun>"

#eval phrase 58
-- let MIZAR_REFUTER ths = PRECHECKER_THEN BASIC_MIZARBY ths;;
unsafe def MIZAR_REFUTER (ths : List thm) : Except String thm := PRECHECKER_THEN BASIC_MIZARBY ths
#eval IO.println "<fun>"

#eval phrase 59
-- let MIZAR_BY = let pth = TAUT `(~p ==> F) <=> p` and p_tm = `p:bool` in fun ths tm -> ...
unsafe def mizarByPth : thm := runIE (TAUT [[(~p ==> F) <=> p]])
unsafe def MIZAR_BY (ths : List thm) (tm : term) : Except String thm := do
  let p_tm : term := [[p:bool]]
  let tm' ← mk_neg tm
  let th0 ← ASSUME tm'
  let th1 ← MIZAR_REFUTER (th0 :: ths)
  kEQ_MP (runE (kINST [(tm, p_tm)] mizarByPth)) (← DISCH tm' th1)
#eval IO.println "<fun>"

#eval phrase 60
-- let MIZAR_RULE tm = MIZAR_BY [] tm;;
unsafe def MIZAR_RULE (tm : term) : Except String thm := MIZAR_BY [] tm
#eval IO.println "<fun>"

#eval phrase 61
-- let HOL_BY = let BETASET_CONV = ... and BUILTIN_CONV tm = ... in fun ths tm -> ...
unsafe def hb_BETASET_CONV : HolCore.Equal.ioconv :=
  (HolLight.TOP_DEPTH_CONV GEN_BETA_CONV) THENC (REWRITE_CONV [IN_ELIM_THM])
unsafe def hb_BUILTIN_CONV (tm : term) : IO (Except String thm) := do
  match ← NUM_REDUCE_CONV tm with
  | .ok c => match EQT_ELIM c with | .ok r => return (Except.ok r) | .error _ => pure ()
  | .error _ => pure ()
  match ← REAL_RAT_REDUCE_CONV tm with
  | .ok c => match EQT_ELIM c with | .ok r => return (Except.ok r) | .error _ => pure ()
  | .error _ => pure ()
  match ← ARITH_RULE tm with | .ok r => return (Except.ok r) | .error _ => pure ()
  match ← REAL_ARITH3 tm with | .ok r => return (Except.ok r) | .error _ => pure ()
  return (Except.error "BUILTIN_CONV")
unsafe def HOL_BY (ths : List thm) (tm : term) : IO (Except String thm) := do
  -- try MIZAR_BY ths tm
  match MIZAR_BY ths tm with | .ok r => return (Except.ok r) | .error _ => pure ()
  -- try tryfind (fun th -> PART_MATCH I th tm) ths
  match ← tryfindM (fun th => PART_MATCH (fun t => Except.ok t) th tm) ths with
  | .ok r => return (Except.ok r) | .error _ => pure ()
  -- try let avs,bod = strip_forall tm in ...
  match ← (do
      let (avs, bod) := strip_forall tm
      let gvs := avs.map (fun v => runIO (genvar (type_of v)))
      let gtm := (runE (vsubst (runE (zip gvs avs)))) bod
      match ← tryfindM (fun th => PART_MATCH (fun t => Except.ok t) th gtm) ths with
      | .error e => return (Except.error e)
      | .ok th =>
        match GENL gvs th with
        | .error e => return (Except.error e)
        | .ok gth => return (kEQ_MP (runE (kALPHA (concl gth) tm)) gth) : IO (Except String thm)) with
  | .ok r => return (Except.ok r) | .error _ => pure ()
  -- the BETA/BUILTIN/MESON branch; any failure -> "HOL_BY"
  let branch : IO (Except String thm) := do
    let ths' := ths.map (fun th => runE (HolCore.Equal.BETA_RULE th))
    let th' := runE (HolCore.Equal.TOP_DEPTH_CONV HolCore.Equal.BETA_CONV tm)
    let tm' := runE (rand (concl th'))
    match ← tryfindM (fun th => PART_MATCH (fun t => Except.ok t) th tm') ths with
    | .ok r => return (kEQ_MP (runE (kSYM th')) r)
    | .error _ => pure ()
    match ← hb_BUILTIN_CONV tm' with
    | .ok r => return (kEQ_MP (runE (kSYM th')) r)
    | .error _ => pure ()
    let ths'' := ths'.map (fun th => runIE (HolLight.CONV_RULE hb_BETASET_CONV th).run)
    let th'' := runE (kTRANS th' (runIE (hb_BETASET_CONV tm')))
    match ← MESON ths'' (runE (rand (concl th''))) with
    | .ok m => return kEQ_MP (runE (kSYM th'')) m
    | .error e => return .error e
  match ← branch with | .ok r => return (Except.ok r) | .error _ => return (Except.error "HOL_BY")
#eval IO.println "<fun>"

#eval phrase 62
-- let HOL_RULE tm = try let l,r = dest_imp tm in DISCH l (HOL_BY (CONJUNCTS(ASSUME l)) r) with Failure _ -> HOL_BY [] tm;;
unsafe def HOL_RULE (tm : term) : IO (Except String thm) := do
  match dest_imp tm with
  | .ok (l, r) =>
      match ← HOL_BY (CONJUNCTS (runE (ASSUME l))) r with
      | .ok hb => return DISCH l hb
      | .error _ => HOL_BY [] tm
  | .error _ => HOL_BY [] tm
#eval IO.println "<fun>"

/-- Run `time HOL_RULE tm` and print the resulting theorem as the toplevel. -/
unsafe def timeRule (tm : term) : IO Unit := do
  match ← HolCore.Lib.time HOL_RULE tm with
  | .ok th => IO.println (← HolCore.Printer.string_of_thm th)
  | .error e => failure e
/-- Run `time (HOL_BY ths) tm` and print the result. -/
unsafe def timeBy (ths : List thm) (tm : term) : IO Unit := do
  match ← HolCore.Lib.time (fun t => HOL_BY ths t) tm with
  | .ok th => IO.println (← HolCore.Printer.string_of_thm th)
  | .error e => failure e

/- ------------------------------------------------------------------------- -/
/- Tautology examples (Pelletier problems).                                  -/
/- ------------------------------------------------------------------------- -/

#eval phrase 63
#eval timeRule [[p ==> q <=> ~q ==> ~p]]

#eval phrase 64
#eval timeRule [[~ ~p <=> p]]

#eval phrase 65
#eval timeRule [[~(p ==> q) ==> q ==> p]]

#eval phrase 66
#eval timeRule [[~p ==> q <=> ~q ==> p]]

#eval phrase 67
#eval timeRule [[(p \/ q ==> p \/ r) ==> p \/ (q ==> r)]]

#eval phrase 68
#eval timeRule [[p \/ ~p]]

#eval phrase 69
#eval timeRule [[p \/ ~ ~ ~p]]

#eval phrase 70
#eval timeRule [[((p ==> q) ==> p) ==> p]]

#eval phrase 71
#eval timeRule [[(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)]]

#eval phrase 72
#eval timeRule [[(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)]]

#eval phrase 73
#eval timeRule [[p <=> p]]

#eval phrase 74
#eval timeRule [[((p <=> q) <=> r) <=> (p <=> (q <=> r))]]

#eval phrase 75
#eval timeRule [[p \/ q /\ r <=> (p \/ q) /\ (p \/ r)]]

#eval phrase 76
#eval timeRule [[(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)]]

#eval phrase 77
#eval timeRule [[p ==> q <=> ~p \/ q]]

#eval phrase 78
#eval timeRule [[(p ==> q) \/ (q ==> p)]]

#eval phrase 79
#eval timeRule [[p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)]]

/- ------------------------------------------------------------------------- -/
/- Congruence closure examples.                                              -/
/- ------------------------------------------------------------------------- -/

#eval phrase 80
#eval timeRule [[(f(f(f(f(f(x))))) = x) /\ (f(f(f(x))) = x) ==> (f(x) = x)]]

#eval phrase 81
#eval timeRule [[(f(f(f(f(f(f(x)))))) = x) /\ (f(f(f(f(x)))) = x) ==> (f(f(x)) = x)]]

#eval phrase 82
#eval timeRule [[(f a = a) ==> (f(f a) = a)]]

#eval phrase 83
#eval timeRule [[(a = f a) /\ ((g b (f a))=(f (f a))) /\ ((g a b)=(f (g b a)))
   ==> (g a b = a)]]

#eval phrase 84
#eval timeRule [[((s(s(s(s(s(s(s(s(s(s(s(s(s(s(s a)))))))))))))))=a) /\
   ((s (s (s (s (s (s (s (s (s (s a))))))))))=a) /\
   ((s (s (s (s (s (s a))))))=a)
   ==> (a = s a)]]

#eval phrase 85
#eval timeRule [[(u = v) ==> (P u <=> P v)]]

#eval phrase 86
#eval timeRule [[(b + c + d + e + f + g + h + i + j + k + l + m =
    m + l + k + j + i + h + g + f + e + d + c + b)
   ==> (a + b + c + d + e + f + g + h + i + j + k + l + m =
        a + m + l + k + j + i + h + g + f + e + d + c + b)]]

#eval phrase 87
#eval timeRule [[(f(f(f(f(a)))) = a) /\ (f(f(f(f(f(f(a)))))) = a) /\
   something(irrelevant) /\ (11 + 12 = 23) /\
   (f(f(f(f(b)))) = f(f(f(f(f(f(f(f(f(f(c))))))))))) /\
   ~(otherthing) /\ ~(f(a) = a) /\ ~(f(b) = b) /\
   P(f(f(f(a)))) ==> P(f(a))]]

#eval phrase 88
#eval timeRule [[((a = b) \/ (c = d)) /\ ((a = c) \/ (b = d)) ==> (a = d) \/ (b = c)]]

/- ------------------------------------------------------------------------- -/
/- Various combined examples.                                                -/
/- ------------------------------------------------------------------------- -/

#eval phrase 89
#eval timeRule [[(f(f(f(f(a:A)))) = a) /\ (f(f(f(f(f(f(a)))))) = a) /\
   something(irrelevant) /\ (11 + 12 = 23) /\
   (f(f(f(f(b:A)))) = f(f(f(f(f(f(f(f(f(f(c))))))))))) /\
   ~(otherthing) /\ ~(f(a) = a) /\ ~(f(b) = b) /\
   P(f(a)) /\ ~(f(f(f(a))) = f(a)) ==> ?x. P(f(f(f(x))))]]

#eval phrase 90
#eval timeRule [[(f(f(f(f(a:A)))) = a) /\ (f(f(f(f(f(f(a)))))) = a) /\
   something(irrelevant) /\ (11 + 12 = 23) /\
   (f(f(f(f(b:A)))) = f(f(f(f(f(f(f(f(f(f(c))))))))))) /\
   ~(otherthing) /\ ~(f(a) = a) /\ ~(f(b) = b) /\
   P(f(a))
   ==> P(f(f(f(a))))]]

#eval phrase 91
#eval timeRule [[(f(f(f(f(a:A)))) = a) /\ (f(f(f(f(f(f(a)))))) = a) /\
   something(irrelevant) /\ (11 + 12 = 23) /\
   (f(f(f(f(b:A)))) = f(f(f(f(f(f(f(f(f(f(c))))))))))) /\
   ~(otherthing) /\ ~(f(a) = a) /\ ~(f(b) = b) /\
   P(f(a))
   ==> ?x. P(f(f(f(x))))]]

#eval phrase 92
#eval timeRule [[(a = f a) /\ ((g b (f a))=(f (f a))) /\ ((g a b)=(f (g b a))) /\
   (!x y. ~P (g x y))
   ==> ~P(a)]]

#eval phrase 93
#eval timeRule [[(!x y. x + y = y + x) /\ (1 + 2 = x) /\ (x = 3) ==> (3 = 2 + 1)]]

#eval phrase 94
#eval timeRule [[(!x:num y. x + y = y + x) ==> (1 + 2 = 2 + 1)]]

#eval phrase 95
#eval timeRule [[(!x:num y. ~(x + y = y + x)) ==> ~(1 + 2 = 2 + 1)]]

#eval phrase 96
#eval timeRule [[(1 + 2 = 2 + 1) ==> ?x:num y. x + y = y + x]]

#eval phrase 97
#eval timeRule [[(1 + x = x + 1) ==> ?x:num y. x + y = y + x]]

#eval phrase 98
#eval timeBy [] [[?x. P x ==> !y. P y]]

/- ------------------------------------------------------------------------- -/
/- Testing the HOL extensions.                                               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 99
#eval timeRule [[1 + 1 = 2]]

#eval phrase 100
#eval timeRule [[(\x. x + 1) 2 = 2 + 1]]

#eval phrase 101
#eval timeRule [[!x. x < 2 ==> 2 * x <= 3]]

#eval phrase 102
#eval timeRule [[y IN {x | x < 2} <=> y < 2]]

#eval phrase 103
#eval timeRule [[(!x. (x = a) \/ x > a) ==> (1 + x = a) \/ 1 + x > a]]

#eval phrase 104
#eval timeRule [[(\(x,y). x + y)(1,2) + 5 = (1 + 2) + 5]]

/- ------------------------------------------------------------------------- -/
/- These and only these should go to MESON.                                  -/
/- ------------------------------------------------------------------------- -/

#eval phrase 105
#eval (do IO.print "***** Now the following (only) should use MESON"; IO.println "")

#eval phrase 106
#eval timeRule [[?x y. x = y]]

#eval phrase 107
#eval timeRule [[(!Y X Z. p(X,Y) /\ p(Y,Z) ==> p(X,Z)) /\
               (!Y X Z. q(X,Y) /\ q(Y,Z) ==> q(X,Z)) /\
               (!Y X. q(X,Y) ==> q(Y,X)) /\
               (!X Y. p(X,Y) \/ q(X,Y))
               ==> p(a,b) \/ q(c,d)]]

#eval phrase 108
-- `time HOL_BY [PAIR_EQ] tm` is `(time HOL_BY [PAIR_EQ]) tm`: only the
-- partial application is timed, and the proof runs after the time report.
#eval show IO Unit from do
  let f ← HolCore.Lib.time (fun ths => pure (HOL_BY ths)) [PAIR_EQ]
  match ← f [[(1,2) IN {(x,y) | x < y} <=> 1 < 2]] with
  | .ok th => IO.println (← HolCore.Printer.string_of_thm th)
  | .error e => failure e

#eval phrase 109
#eval (do
  match ← HOL_BY [] [[?x. !y. P x ==> P y]] with
  | .ok th => IO.println (← HolCore.Printer.string_of_thm th)
  | .error e => failure e)

end HolExamples.Holby
