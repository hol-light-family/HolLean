/- File: HolExamples/Hol88.lean
Translation of HOL Light's Examples/hol88.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolExamples.Common
open HolCore.Kernel HolCore.Basics Session HolLight.Syntax HolExamples
open HolCore.Lib (zip unzip partition can)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)
open HolLight (tryWith tactic_of)
open scoped HolLight
namespace HolExamples.Hol88

/- The session's IO-valued `prove` lifted into `ExceptT String IO`, so tactic
   scripts read as in OCaml. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/- Local `ioconv` wrappers around the pure (Except-valued) kernel conversions,
   and a `TAUT` usable inside an `ExceptT String IO` do-block. -/
private unsafe def ALPHA_CONV_io (v : term) : HolCore.Equal.ioconv :=
  fun t => pure (HolCore.Equal.ALPHA_CONV v t)
private unsafe def GEN_ALPHA_CONV_io (v : term) : HolCore.Equal.ioconv :=
  fun t => pure (HolCore.Equal.GEN_ALPHA_CONV v t)
private unsafe def ETA_CONV_io : HolCore.Equal.ioconv :=
  fun t => pure (Session.ETA_CONV t)
private unsafe def BINOP_CONV_io (c : HolCore.Equal.ioconv) : HolCore.Equal.ioconv :=
  HolLight.BINOP_CONV c
private unsafe def TAUT_io (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.TAUT tm)
private unsafe def mkEqP (pr : term × term) : IO (Except String term) := do
  match ← (mk_eq : IO _) with | .ok f => pure (f pr) | .error e => pure (.error e)

/- ========================================================================= -/
/- HOL88 compatibility: various things missing or different in HOL Light.    -/
/- ========================================================================= -/

/- let (upto) = (--);; -/
#eval phrase 1
unsafe def upto : Int → Int → List Int := HolCore.Lib.upto
#eval IO.println "<fun>"

/- let is_neg_imp tm = is_neg tm || is_imp tm;; -/
#eval phrase 2
unsafe def is_neg_imp (tm : term) : Bool := is_neg tm || is_imp tm
#eval IO.println "<fun>"

/- let dest_neg_imp tm = try dest_imp tm with Failure _ ->
   try (dest_neg tm,mk_const("F",[])) with Failure _ -> failwith "dest_neg_imp";; -/
#eval phrase 3
unsafe def dest_neg_imp (tm : term) : IO (Except String (term × term)) := (do
  match dest_imp tm with
  | .ok p => pure p
  | .error _ =>
    HolLight.tryWith (do
      let f ← ExceptT.mk (mk_const "F" [])
      let n ← liftExcept (dest_neg tm)
      pure (n, f))
      (throw "dest_neg_imp")
  : ExceptT String IO (term × term)).run
#eval IO.println "<fun>"

/- let CONTRAPOS = ... ;;   (the ITAUT runs when CONTRAPOS is defined, so its
   "Searching with limit" traces print at phrase 4, then `<fun>`). -/
#eval phrase 4
unsafe def contraposPth : thm := keep "contraposPth" fun _ =>
  (((HolLight.ITAUT [[(a ==> b) ==> (~b ==> ~a)]]).run : IO (Except String thm)) : thm)
unsafe def CONTRAPOS (th : thm) : IO (Except String thm) := (do
  let a : term := [[a:bool]]
  let b : term := [[b:bool]]
  let pth := contraposPth
  HolLight.tryWith (do
    let (P, Q) ← liftExcept (dest_imp (concl th))
    MP (← INST [(P, a), (Q, b)] pth) th)
    (throw "CONTRAPOS")
  : ExceptT String IO thm).run
#eval do
  -- Force `contraposPth` (runs ITAUT, whose search traces print here).
  forceValue contraposPth
  IO.println "<fun>"

/- let NEG_DISCH = ... ;; -/
#eval phrase 5
unsafe def NEG_DISCH (t : term) (th : thm) : IO (Except String thm) := (do
  let falsity : term := [[F]]
  HolLight.tryWith (do
    if concl th == falsity then NOT_INTRO (← DISCH t th) else DISCH t th)
    (throw "NEG_DISCH")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let SELECT_ELIM th1 (v,th2) = ... ;; -/
#eval phrase 6
unsafe def SELECT_ELIM (th1 : thm) : term × thm → IO (Except String thm)
  | (v, th2) => (do
    HolLight.tryWith (do
      let (P, SP) ← liftExcept (dest_comb (concl th1))
      let th3 ← DISCH (← liftExcept (mk_comb P v)) th2
      MP (← INST [(SP, v)] th3) th1)
      (throw "SELECT_ELIM")
    : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let SELECT_INTRO = ... ;; -/
#eval phrase 7
unsafe def SELECT_INTRO (th : thm) : IO (Except String thm) := (do
  let P : term := [[P:A->bool]]
  let x : term := [[x:A]]
  let pth ← SPECL [P, x] SELECT_AX
  HolLight.tryWith (do
    let (f, arg) ← liftExcept (dest_comb (concl th))
    MP (← HolLight.PINST [(type_of x, aty)] [(f, P), (arg, x)] pth) th)
    (throw "SELECT_INTRO")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let EXT = ... ;; -/
#eval phrase 8
unsafe def EXT (th : thm) : IO (Except String thm) := (do
  let f : term := [[f:A->B]]
  let g : term := [[g:A->B]]
  let pth ← prove ([[(!x. (f:A->B) x = g x) ==> (f = g)]])
    (MATCH_ACCEPT_TAC EQ_EXT)
  HolLight.tryWith (do
    let (x, bod) ← liftExcept (dest_forall (concl th))
    let (l, r) ← liftExcept (dest_eq bod)
    let l' ← liftExcept (rator l)
    let r' ← liftExcept (rator r)
    let th1 ← HolLight.PINST [(type_of x, aty), (type_of l, bty)] [(l', f), (r', g)] pth
    MP th1 th)
    (throw "EXT")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let PROVE = prove;; -/
#eval phrase 9
unsafe def PROVE : term × HolCore.Tactics.tactic → IO (Except String thm)
  | (g, t) => Session.prove g t
#eval IO.println "<fun>"

/- let prove_thm((s:string),g,t) = prove(g,t);; -/
#eval phrase 10
unsafe def prove_thm : String × term × HolCore.Tactics.tactic → IO (Except String thm)
  | (_s, g, t) => Session.prove g t
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- The quantifier movement conversions.                                      -/
/- These are HOL Light's analysis.ml (= hol88) definitions, already ported   -/
/- in SessionLibrary.Analysis; we reuse them (same algorithm, prints <fun>). -/
/- ------------------------------------------------------------------------- -/

/- let (CONV_OF_RCONV: conv -> conv) = ... ;; -/
#eval phrase 11
unsafe def CONV_OF_RCONV : HolCore.Equal.ioconv → HolCore.Equal.ioconv :=
  SessionLibrary.Analysis.CONV_OF_RCONV
#eval IO.println "<fun>"

/- let (CONV_OF_THM: thm -> conv) = CONV_OF_RCONV o REWR_CONV;; -/
#eval phrase 12
unsafe def CONV_OF_THM : thm → HolCore.Equal.ioconv :=
  SessionLibrary.Analysis.CONV_OF_THM
#eval IO.println "<fun>"

/- let (X_FUN_EQ_CONV:term->conv) = ... ;; -/
#eval phrase 13
unsafe def X_FUN_EQ_CONV : term → HolCore.Equal.ioconv :=
  SessionLibrary.Analysis.X_FUN_EQ_CONV
#eval IO.println "<fun>"

/- let (FUN_EQ_CONV:conv) = ... ;; -/
#eval phrase 14
unsafe def FUN_EQ_CONV : HolCore.Equal.ioconv :=
  SessionLibrary.Analysis.FUN_EQ_CONV
#eval IO.println "<fun>"

/- let (SINGLE_DEPTH_CONV:conv->conv) = ... ;; -/
#eval phrase 15
unsafe def SINGLE_DEPTH_CONV : HolCore.Equal.ioconv → HolCore.Equal.ioconv :=
  SessionLibrary.Analysis.SINGLE_DEPTH_CONV
#eval IO.println "<fun>"

/- let (SKOLEM_CONV:conv) = SINGLE_DEPTH_CONV (REWR_CONV SKOLEM_THM);; -/
#eval phrase 16
unsafe def SKOLEM_CONV : HolCore.Equal.ioconv :=
  SINGLE_DEPTH_CONV (REWR_CONV SKOLEM_THM)
#eval IO.println "<fun>"

/- let (X_SKOLEM_CONV:term->conv) = fun v -> SKOLEM_CONV THENC GEN_ALPHA_CONV v;; -/
#eval phrase 17
unsafe def X_SKOLEM_CONV : term → HolCore.Equal.ioconv :=
  SessionLibrary.Analysis.X_SKOLEM_CONV
#eval IO.println "<fun>"

/- let EXISTS_UNIQUE_CONV tm = ... ;; -/
#eval phrase 18
unsafe def EXISTS_UNIQUE_CONV : HolCore.Equal.ioconv :=
  SessionLibrary.Analysis.EXISTS_UNIQUE_CONV
#eval IO.println "<fun>"

/- let NOT_FORALL_CONV = CONV_OF_THM NOT_FORALL_THM;; -/
#eval phrase 19
unsafe def NOT_FORALL_CONV : HolCore.Equal.ioconv := CONV_OF_THM NOT_FORALL_THM
#eval IO.println "<fun>"

/- let NOT_EXISTS_CONV = CONV_OF_THM NOT_EXISTS_THM;; -/
#eval phrase 20
unsafe def NOT_EXISTS_CONV : HolCore.Equal.ioconv := CONV_OF_THM NOT_EXISTS_THM
#eval IO.println "<fun>"

/- let RIGHT_IMP_EXISTS_CONV = CONV_OF_THM RIGHT_IMP_EXISTS_THM;; -/
#eval phrase 21
unsafe def RIGHT_IMP_EXISTS_CONV : HolCore.Equal.ioconv := CONV_OF_THM RIGHT_IMP_EXISTS_THM
#eval IO.println "<fun>"

/- let FORALL_IMP_CONV = CONV_OF_RCONV (...);; -/
#eval phrase 22
unsafe def FORALL_IMP_CONV : HolCore.Equal.ioconv := CONV_OF_RCONV
  (REWR_CONV TRIV_FORALL_IMP_THM ORELSEC
   REWR_CONV RIGHT_FORALL_IMP_THM ORELSEC
   REWR_CONV LEFT_FORALL_IMP_THM)
#eval IO.println "<fun>"

/- let EXISTS_AND_CONV = CONV_OF_RCONV (...);; -/
#eval phrase 23
unsafe def EXISTS_AND_CONV : HolCore.Equal.ioconv := CONV_OF_RCONV
  (REWR_CONV TRIV_EXISTS_AND_THM ORELSEC
   REWR_CONV LEFT_EXISTS_AND_THM ORELSEC
   REWR_CONV RIGHT_EXISTS_AND_THM)
#eval IO.println "<fun>"

/- let LEFT_IMP_EXISTS_CONV = CONV_OF_THM LEFT_IMP_EXISTS_THM;; -/
#eval phrase 24
unsafe def LEFT_IMP_EXISTS_CONV : HolCore.Equal.ioconv := CONV_OF_THM LEFT_IMP_EXISTS_THM
#eval IO.println "<fun>"

/- let LEFT_AND_EXISTS_CONV tm = ... ;; -/
#eval phrase 25
unsafe def LEFT_AND_EXISTS_CONV : HolCore.Equal.ioconv :=
  SessionLibrary.Analysis.LEFT_AND_EXISTS_CONV
#eval IO.println "<fun>"

/- let RIGHT_AND_EXISTS_CONV = CONV_OF_THM RIGHT_AND_EXISTS_THM;; -/
#eval phrase 26
unsafe def RIGHT_AND_EXISTS_CONV : HolCore.Equal.ioconv := CONV_OF_THM RIGHT_AND_EXISTS_THM
#eval IO.println "<fun>"

/- let AND_FORALL_CONV = CONV_OF_THM AND_FORALL_THM;; -/
#eval phrase 27
unsafe def AND_FORALL_CONV : HolCore.Equal.ioconv := CONV_OF_THM AND_FORALL_THM
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- Paired beta conversion (now just a special case of GEN_BETA_CONV).        -/
/- The OCaml body re-derives GEN_BETA_CONV's result; the toplevel prints     -/
/- only <fun>.  We reuse the ported GEN_BETA_CONV (same value).              -/
/- ------------------------------------------------------------------------- -/
#eval phrase 28
unsafe def PAIRED_BETA_CONV : term → IO (Except String thm) := Session.GEN_BETA_CONV
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- The slew of named tautologies.                                            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 29
unsafe def AND1_THM : thm := keep "AND1_THM" fun _ => (TAUT [[!t1 t2. t1 /\ t2 ==> t1]] : thm)
#eval AND1_THM

#eval phrase 30
unsafe def AND2_THM : thm := keep "AND2_THM" fun _ => (TAUT [[!t1 t2. t1 /\ t2 ==> t2]] : thm)
#eval AND2_THM

#eval phrase 31
unsafe def AND_IMP_INTRO : thm := keep "AND_IMP_INTRO" fun _ =>
  (TAUT [[!t1 t2 t3. t1 ==> t2 ==> t3 <=> t1 /\ t2 ==> t3]] : thm)
#eval AND_IMP_INTRO

#eval phrase 32
unsafe def AND_INTRO_THM : thm := keep "AND_INTRO_THM" fun _ =>
  (TAUT [[!t1 t2. t1 ==> t2 ==> t1 /\ t2]] : thm)
#eval AND_INTRO_THM

#eval phrase 33
unsafe def BOOL_EQ_DISTINCT : thm := keep "BOOL_EQ_DISTINCT" fun _ =>
  (TAUT [[~(T <=> F) /\ ~(F <=> T)]] : thm)
#eval BOOL_EQ_DISTINCT

#eval phrase 34
unsafe def EQ_EXPAND : thm := keep "EQ_EXPAND" fun _ =>
  (TAUT [[!t1 t2. (t1 <=> t2) <=> t1 /\ t2 \/ ~t1 /\ ~t2]] : thm)
#eval EQ_EXPAND

#eval phrase 35
unsafe def EQ_IMP_THM : thm := keep "EQ_IMP_THM" fun _ =>
  (TAUT [[!t1 t2. (t1 <=> t2) <=> (t1 ==> t2) /\ (t2 ==> t1)]] : thm)
#eval EQ_IMP_THM

#eval phrase 36
unsafe def FALSITY : thm := keep "FALSITY" fun _ => (TAUT [[!t. F ==> t]] : thm)
#eval FALSITY

#eval phrase 37
unsafe def F_IMP : thm := keep "F_IMP" fun _ => (TAUT [[!t. ~t ==> t ==> F]] : thm)
#eval F_IMP

#eval phrase 38
unsafe def IMP_DISJ_THM : thm := keep "IMP_DISJ_THM" fun _ =>
  (TAUT [[!t1 t2. t1 ==> t2 <=> ~t1 \/ t2]] : thm)
#eval IMP_DISJ_THM

#eval phrase 39
unsafe def IMP_F : thm := keep "IMP_F" fun _ => (TAUT [[!t. (t ==> F) ==> ~t]] : thm)
#eval IMP_F

#eval phrase 40
unsafe def IMP_F_EQ_F : thm := keep "IMP_F_EQ_F" fun _ =>
  (TAUT [[!t. t ==> F <=> (t <=> F)]] : thm)
#eval IMP_F_EQ_F

#eval phrase 41
unsafe def LEFT_AND_OVER_OR : thm := keep "LEFT_AND_OVER_OR" fun _ =>
  (TAUT [[!t1 t2 t3. t1 /\ (t2 \/ t3) <=> t1 /\ t2 \/ t1 /\ t3]] : thm)
#eval LEFT_AND_OVER_OR

#eval phrase 42
unsafe def LEFT_OR_OVER_AND : thm := keep "LEFT_OR_OVER_AND" fun _ =>
  (TAUT [[!t1 t2 t3. t1 \/ t2 /\ t3 <=> (t1 \/ t2) /\ (t1 \/ t3)]] : thm)
#eval LEFT_OR_OVER_AND

#eval phrase 43
unsafe def NOT_AND : thm := keep "NOT_AND" fun _ => (TAUT [[~(t /\ ~t)]] : thm)
#eval NOT_AND

#eval phrase 44
unsafe def NOT_F : thm := keep "NOT_F" fun _ => (TAUT [[!t. ~t ==> (t <=> F)]] : thm)
#eval NOT_F

#eval phrase 45
unsafe def OR_ELIM_THM : thm := keep "OR_ELIM_THM" fun _ =>
  (TAUT [[!t t1 t2. t1 \/ t2 ==> (t1 ==> t) ==> (t2 ==> t) ==> t]] : thm)
#eval OR_ELIM_THM

#eval phrase 46
unsafe def OR_IMP_THM : thm := keep "OR_IMP_THM" fun _ =>
  (TAUT [[!t1 t2. (t1 <=> t2 \/ t1) <=> t2 ==> t1]] : thm)
#eval OR_IMP_THM

#eval phrase 47
unsafe def OR_INTRO_THM1 : thm := keep "OR_INTRO_THM1" fun _ =>
  (TAUT [[!t1 t2. t1 ==> t1 \/ t2]] : thm)
#eval OR_INTRO_THM1

#eval phrase 48
unsafe def OR_INTRO_THM2 : thm := keep "OR_INTRO_THM2" fun _ =>
  (TAUT [[!t1 t2. t2 ==> t1 \/ t2]] : thm)
#eval OR_INTRO_THM2

#eval phrase 49
unsafe def RIGHT_AND_OVER_OR : thm := keep "RIGHT_AND_OVER_OR" fun _ =>
  (TAUT [[!t1 t2 t3. (t2 \/ t3) /\ t1 <=> t2 /\ t1 \/ t3 /\ t1]] : thm)
#eval RIGHT_AND_OVER_OR

#eval phrase 50
unsafe def RIGHT_OR_OVER_AND : thm := keep "RIGHT_OR_OVER_AND" fun _ =>
  (TAUT [[!t1 t2 t3. t2 /\ t3 \/ t1 <=> (t2 \/ t1) /\ (t3 \/ t1)]] : thm)
#eval RIGHT_OR_OVER_AND

/- ------------------------------------------------------------------------- -/
/- is_type / is_constant.                                                    -/
/- ------------------------------------------------------------------------- -/

/- let is_type = can get_type_arity;; -/
#eval phrase 51
unsafe def is_type (s : String) : IO Bool := do
  match ← get_type_arity s with | .ok _ => pure true | .error _ => pure false
#eval IO.println "<fun>"

/- let is_constant = can get_const_type;; -/
#eval phrase 52
unsafe def is_constant (s : String) : IO Bool := do
  match ← get_const_type s with | .ok _ => pure true | .error _ => pure false
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- Misc.                                                                     -/
/- ------------------------------------------------------------------------- -/

/- let null l = l = [];; -/
#eval phrase 53
unsafe def null {α : Type} (l : List α) : Bool := l.isEmpty
#eval IO.println "<fun>"

/- let combine(a,b) = zip a b;; -/
#eval phrase 54
unsafe def combine {α β : Type} : List α × List β → Except String (List (α × β))
  | (a, b) => zip a b
#eval IO.println "<fun>"

/- let split = unzip;; -/
#eval phrase 55
unsafe def split {α β : Type} : List (α × β) → List α × List β := unzip
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- Syntax.                                                                   -/
/- ------------------------------------------------------------------------- -/

/- let type_tyvars = type_vars_in_term o curry mk_var "x";; -/
#eval phrase 56
unsafe def type_tyvars (ty : hol_type) : List hol_type :=
  type_vars_in_term (mk_var "x" ty)
#eval IO.println "<fun>"

/- let find_match u = ... ;; -/
#eval phrase 57
unsafe def find_match (u : term) (t : term) :
    IO (Except String (List (term × term) × List (hol_type × hol_type))) := (do
  let rec find_mt (t : term) : ExceptT String IO HolCore.Drule.instantiation :=
    tryWith (HolLight.term_match [] u t)
    (tryWith (do find_mt (← liftExcept (rator t)))
    (tryWith (do find_mt (← liftExcept (rand t)))
    (tryWith (do find_mt (← liftExcept (do pure (← dest_abs t).2)))
    (throw "find_match"))))
  let (_, tmin, tyin) ← find_mt t
  pure (tmin, tyin)
  : ExceptT String IO _).run
#eval IO.println "<fun>"

/- let rec mk_primed_var(name,ty) = ... ;; -/
#eval phrase 58
unsafe def mk_primed_var : String × hol_type → IO (Except String term)
  | (name, ty) => do
    match ← get_const_type name with
    | .ok _ => mk_primed_var (name ++ "'", ty)
    | .error _ => pure (.ok (mk_var name ty))
#eval IO.println "<fun>"

/- let subst_occs = ... ;; -/
#eval phrase 59
unsafe def subst_occs (ilist : List (List Int)) (slist : List (term × term)) (tm : term) :
    IO (Except String term) := (do
  let rec so (slist : List (List Int × (term × term))) (tm : term) :
      ExceptT String IO (term × List (List Int × (term × term))) := do
    let (applic, noway) := partition (fun (p : List Int × (term × term)) =>
      aconv tm p.2.2) slist
    let sposs := applic.map (fun (l, z) =>
      let (l1, l2) := partition (fun (n : Int) => n == 1) l
      ((l1, z), (l2, z)))
    let (racts, rrest) := unzip sposs
    let acts := racts.filter (fun t => !(t.1 == []))
    let trest := rrest.map (fun (n, t) => (n.map (fun (i : Int) => i - 1), t))
    let urest := trest.filter (fun t => !(t.1 == []))
    let tlist := urest ++ noway
    if acts == [] then
      if is_comb tm then do
        let (l, r) ← liftExcept (dest_comb tm)
        let (l', s') ← so tlist l
        let (r', s'') ← so s' r
        pure (← liftExcept (mk_comb l' r'), s'')
      else if is_abs tm then do
        let (bv, bod) ← liftExcept (dest_abs tm)
        let gv ← (genvar (type_of bv) : ExceptT String IO term)
        let vs ← liftExcept (vsubst [(gv, bv)])
        let nbod := vs bod
        let (tm', s') ← so tlist nbod
        pure (← liftExcept (alpha bv (← liftExcept (mk_abs gv tm'))), s')
      else pure (tm, tlist)
    else do
      let (_, (t, x)) := acts.head!
      let sb ← ExceptT.mk (HolCore.Basics.subst [(t, x)])
      pure (← ExceptT.mk (sb tm), tlist)
  let z ← liftExcept (zip ilist slist)
  pure (← so z tm).1
  : ExceptT String IO term).run
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- Note that the all-instantiating INST and INST_TYPE are not overwritten.   -/
/- ------------------------------------------------------------------------- -/

/- let INST_TY_TERM(substl,insttyl) th = ... ;; -/
#eval phrase 60
unsafe def INST_TY_TERM :
    List (term × term) × List (hol_type × hol_type) → thm → IO (Except String thm)
  | (substl, insttyl), th => (do
    let th' ← INST substl (← HolLight.INST_TYPE insttyl th)
    if hyp th' == hyp th then pure th'
    else throw "INST_TY_TERM: Free term and/or type variables in hypotheses"
    : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- Conversions stuff.                                                        -/
/- ------------------------------------------------------------------------- -/

/- let RIGHT_CONV_RULE (conv:conv) th = TRANS th (conv(rhs(concl th)));; -/
#eval phrase 61
unsafe def RIGHT_CONV_RULE (conv : HolCore.Equal.ioconv) (th : thm) : IO (Except String thm) := (do
  TRANS th (← ExceptT.mk (conv (← liftExcept (HolCore.Equal.rhs (concl th)))))
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- Derived rules.                                                            -/
/- ------------------------------------------------------------------------- -/

/- let NOT_EQ_SYM = ... ;; -/
#eval phrase 62
unsafe def NOT_EQ_SYM (th : thm) : IO (Except String thm) := (do
  -- aty
  let pth ← GENL [([[a:A]]), ([[b:A]])]
    (← CONTRAPOS (← DISCH_ALL (← HolLight.SYM (← ASSUME [[a:A = b]]))))
  tryWith (do
    let (l, r) ← liftExcept (dest_eq (← liftExcept (dest_neg (concl th))))
    MP (← SPECL [r, l] (← HolLight.INST_TYPE [(type_of l, aty)] pth)) th)
    (throw "NOT_EQ_SYM")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let NOT_MP thi th = ... ;; -/
#eval phrase 63
unsafe def NOT_MP (thi : thm) (th : thm) : IO (Except String thm) := (do
  tryWith (MP thi th)
    (tryWith (do
      let t ← liftExcept (dest_neg (concl thi))
      MP (← MP (← SPEC t F_IMP) thi) th)
      (throw "NOT_MP"))
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let FORALL_EQ x = ... ;; -/
#eval phrase 64
unsafe def FORALL_EQ (x : term) (th : thm) : IO (Except String thm) := (do
  let c ← ExceptT.mk (mk_const "!" [(type_of x, mk_vartype "A")])
  tryWith (HolLight.AP_TERM c (← ABS x th)) (throw "FORALL_EQ")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let EXISTS_EQ x = ... ;; -/
#eval phrase 65
unsafe def EXISTS_EQ (x : term) (th : thm) : IO (Except String thm) := (do
  let c ← ExceptT.mk (mk_const "?" [(type_of x, mk_vartype "A")])
  tryWith (HolLight.AP_TERM c (← ABS x th)) (throw "EXISTS_EQ")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let SELECT_EQ x = ... ;; -/
#eval phrase 66
unsafe def SELECT_EQ (x : term) (th : thm) : IO (Except String thm) := (do
  let c ← ExceptT.mk (mk_const "@" [(type_of x, mk_vartype "A")])
  tryWith (HolLight.AP_TERM c (← ABS x th)) (throw "SELECT_EQ")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let RIGHT_BETA th = ... ;; -/
#eval phrase 67
unsafe def RIGHT_BETA (th : thm) : IO (Except String thm) := (do
  tryWith (TRANS th (← liftExcept (HolCore.Equal.BETA_CONV (← liftExcept (HolCore.Equal.rhs (concl th))))))
    (throw "RIGHT_BETA")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let rec LIST_BETA_CONV tm = ... ;; -/
#eval phrase 68
unsafe def LIST_BETA_CONV (tm : term) : IO (Except String thm) := (do
  tryWith (do
    let (rat, rnd) ← liftExcept (dest_comb tm)
    RIGHT_BETA (← HolLight.AP_THM (← ExceptT.mk (LIST_BETA_CONV rat)) rnd))
    (pure (REFL tm))
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let RIGHT_LIST_BETA th = TRANS th (LIST_BETA_CONV(snd(dest_eq(concl th))));; -/
#eval phrase 69
unsafe def RIGHT_LIST_BETA (th : thm) : IO (Except String thm) := (do
  TRANS th (← ExceptT.mk (LIST_BETA_CONV (← liftExcept (do pure (← dest_eq (concl th)).2))))
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let LIST_CONJ = end_itlist CONJ;; -/
#eval phrase 70
unsafe def LIST_CONJ (l : List thm) : IO (Except String thm) := (do
  match l with
  | [] => throw "end_itlist"
  | h :: t => t.foldr (fun x acc => do CONJ x (← acc)) (pure h)
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let rec CONJ_LIST n th = ... ;; -/
#eval phrase 71
unsafe def CONJ_LIST (n : Int) (th : thm) : IO (Except String (List thm)) := (do
  tryWith (do
    if n == 1 then pure [th]
    else pure ((← CONJUNCT1 th) :: (← ExceptT.mk (CONJ_LIST (n - 1) (← CONJUNCT2 th)))))
    (throw "CONJ_LIST")
  : ExceptT String IO (List thm)).run
#eval IO.println "<fun>"

/- let rec BODY_CONJUNCTS th = ... ;; -/
#eval phrase 72
unsafe def BODY_CONJUNCTS (th : thm) : IO (Except String (List thm)) := (do
  if is_forall (concl th) then
    ExceptT.mk (BODY_CONJUNCTS (← SPEC_ALL th))
  else if is_conj (concl th) then do
    pure ((← ExceptT.mk (BODY_CONJUNCTS (← CONJUNCT1 th))) ++
          (← ExceptT.mk (BODY_CONJUNCTS (← CONJUNCT2 th))))
  else pure [th]
  : ExceptT String IO (List thm)).run
#eval IO.println "<fun>"

/- let rec IMP_CANON th = ... ;; -/
#eval phrase 73
unsafe def IMP_CANON (th : thm) : IO (Except String (List thm)) := (do
  let w := concl th
  if is_conj w then
    pure ((← ExceptT.mk (IMP_CANON (← CONJUNCT1 th))) ++
          (← ExceptT.mk (IMP_CANON (← CONJUNCT2 th))))
  else if is_imp w then do
    let (ante, _conc) ← ExceptT.mk (dest_neg_imp w)
    if is_conj ante then do
      let (a, b) ← liftExcept (dest_conj ante)
      ExceptT.mk (IMP_CANON
        (← DISCH a (← DISCH b (← NOT_MP th (← CONJ (← ASSUME a) (← ASSUME b))))))
    else if is_disj ante then do
      let (a, b) ← liftExcept (dest_disj ante)
      pure ((← ExceptT.mk (IMP_CANON (← DISCH a (← NOT_MP th (← DISJ1 (← ASSUME a) b))))) ++
            (← ExceptT.mk (IMP_CANON (← DISCH b (← NOT_MP th (← DISJ2 a (← ASSUME b)))))))
    else if is_exists ante then do
      let (x, body) ← liftExcept (dest_exists ante)
      let x' ← liftExcept (variant (thm_frees th) x)
      let sb ← ExceptT.mk (HolCore.Basics.subst [(x', x)])
      let body' ← ExceptT.mk (sb body)
      ExceptT.mk (IMP_CANON
        (← DISCH body' (← NOT_MP th (← EXISTS (ante, x') (← ASSUME body')))))
    else do
      let l ← ExceptT.mk (IMP_CANON (← UNDISCH th))
      l.mapM (fun t => DISCH ante t)
  else if is_forall w then
    ExceptT.mk (IMP_CANON (← SPEC_ALL th))
  else pure [th]
  : ExceptT String IO (List thm)).run
#eval IO.println "<fun>"

/- let LIST_MP = rev_itlist (fun x y -> MP y x);; -/
#eval phrase 74
unsafe def LIST_MP (l : List thm) (th : thm) : IO (Except String thm) := (do
  l.foldlM (fun y x => MP y x) th
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let DISJ_IMP = ... ;; -/
#eval phrase 75
unsafe def DISJ_IMP (th : thm) : IO (Except String thm) := (do
  let pth ← TAUT_io [[!t1 t2. t1 \/ t2 ==> ~t1 ==> t2]]
  tryWith (do
    let (a, b) ← liftExcept (dest_disj (concl th))
    MP (← SPECL [a, b] pth) th)
    (throw "DISJ_IMP")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let IMP_ELIM = ... ;; -/
#eval phrase 76
unsafe def IMP_ELIM (th : thm) : IO (Except String thm) := (do
  let pth ← TAUT_io [[!t1 t2. (t1 ==> t2) ==> ~t1 \/ t2]]
  tryWith (do
    let (a, b) ← liftExcept (dest_imp (concl th))
    MP (← SPECL [a, b] pth) th)
    (throw "IMP_ELIM")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let DISJ_CASES_UNION dth ath bth = ... ;; -/
#eval phrase 77
unsafe def DISJ_CASES_UNION (dth ath bth : thm) : IO (Except String thm) := (do
  DISJ_CASES dth (← DISJ1 ath (concl bth)) (← DISJ2 (concl ath) bth)
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let MK_ABS qth = ... ;; -/
#eval phrase 78
unsafe def MK_ABS (qth : thm) : IO (Except String thm) := (do
  tryWith (do
    let ov ← liftExcept (do bndvar (← rand (concl qth)))
    let (bv, rth) ← SPEC_VAR qth
    let sth ← ABS bv rth
    let cnv := ALPHA_CONV_io ov
    HolLight.CONV_RULE (BINOP_CONV_io cnv) sth)
    (throw "MK_ABS")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let HALF_MK_ABS th = ... ;; -/
#eval phrase 79
unsafe def HALF_MK_ABS (th : thm) : IO (Except String thm) := (do
  tryWith (do
    let th1 ← ExceptT.mk (MK_ABS th)
    HolLight.CONV_RULE (HolLight.LAND_CONV ETA_CONV_io) th1)
    (throw "HALF_MK_ABS")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let MK_EXISTS qth = ... ;; -/
#eval phrase 80
unsafe def MK_EXISTS (qth : thm) : IO (Except String thm) := (do
  tryWith (do
    let ov ← liftExcept (do bndvar (← rand (concl qth)))
    let (bv, rth) ← SPEC_VAR qth
    let sth ← ExceptT.mk (EXISTS_EQ bv rth)
    let cnv := GEN_ALPHA_CONV_io ov
    HolLight.CONV_RULE (BINOP_CONV_io cnv) sth)
    (throw "MK_EXISTS")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let LIST_MK_EXISTS l th = itlist (fun x th -> MK_EXISTS(GEN x th)) l th;; -/
#eval phrase 81
unsafe def LIST_MK_EXISTS (l : List term) (th : thm) : IO (Except String thm) := (do
  l.foldr (fun x acc => do ExceptT.mk (MK_EXISTS (← GEN x (← acc)))) (pure th)
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let IMP_CONJ th1 th2 = ... ;; -/
#eval phrase 82
unsafe def IMP_CONJ (th1 th2 : thm) : IO (Except String thm) := (do
  let (A1, _C1) ← liftExcept (dest_imp (concl th1))
  let (A2, _C2) ← liftExcept (dest_imp (concl th2))
  let conj ← liftExcept (HolCore.Bool.mk_conj A1 A2)
  let (a1, a2) ← CONJ_PAIR (← ASSUME conj)
  DISCH conj (← CONJ (← MP th1 a1) (← MP th2 a2))
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let EXISTS_IMP x = ... ;; -/
#eval phrase 83
unsafe def EXISTS_IMP (x : term) (th : thm) : IO (Except String thm) := (do
  if !(is_var x) then throw "EXISTS_IMP: first argument not a variable"
  else
    tryWith (do
      let (ante, cncl) ← liftExcept (dest_imp (concl th))
      let th1 ← EXISTS (← liftExcept (HolCore.Bool.mk_exists x cncl), x) (← UNDISCH th)
      let asm ← liftExcept (HolCore.Bool.mk_exists x ante)
      DISCH asm (← CHOOSE (x, ← ASSUME asm) th1))
      (throw "EXISTS_IMP: variable free in assumptions")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let CONJUNCTS_CONV (t1,t2) = ... ;; -/
#eval phrase 84
unsafe def CONJUNCTS_CONV : term × term → IO (Except String thm)
  | (t1, t2) => (do
    let rec build_conj (thl : List thm) (t : term) : ExceptT String IO thm :=
      tryWith (do
        let (l, r) ← liftExcept (dest_conj t)
        CONJ (← build_conj thl l) (← build_conj thl r))
        (liftExcept (HolCore.Lib.find (fun th => concl th == t) thl))
    tryWith (do
      IMP_ANTISYM_RULE
        (← DISCH t1 (← build_conj (CONJUNCTS (← ASSUME t1)) t2))
        (← DISCH t2 (← build_conj (CONJUNCTS (← ASSUME t2)) t1)))
      (throw "CONJUNCTS_CONV")
    : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let CONJ_SET_CONV l1 l2 = ... ;; -/
#eval phrase 85
unsafe def CONJ_SET_CONV (l1 l2 : List term) : IO (Except String thm) := (do
  tryWith (do
    ExceptT.mk (CONJUNCTS_CONV (← liftExcept (HolCore.Bool.list_mk_conj l1), ← liftExcept (HolCore.Bool.list_mk_conj l2))))
    (throw "CONJ_SET_CONV")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let FRONT_CONJ_CONV tml t = ... ;; -/
#eval phrase 86
unsafe def FRONT_CONJ_CONV (tml : List term) (t : term) : IO (Except String thm) := (do
  let rec remove (x : term) (l : List term) : List term :=
    match l with
    | [] => []
    | h :: tl => if h == x then tl else h :: remove x tl
  tryWith (ExceptT.mk (CONJ_SET_CONV tml (t :: remove t tml)))
    (throw "FRONT_CONJ_CONV")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let CONJ_DISCH = ... ;; -/
#eval phrase 87
unsafe def CONJ_DISCH (t : term) (th : thm) : IO (Except String thm) := (do
  let pth ← TAUT_io [[!t t1 t2. (t ==> (t1 = t2)) ==> (t /\ t1 <=> t /\ t2)]]
  tryWith (do
    let (t1, t2) ← liftExcept (dest_eq (concl th))
    MP (← SPECL [t, t1, t2] pth) (← DISCH t th))
    (throw "CONJ_DISCH")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let rec CONJ_DISCHL l th = ... ;; -/
#eval phrase 88
unsafe def CONJ_DISCHL (l : List term) (th : thm) : IO (Except String thm) := (do
  match l with
  | [] => pure th
  | h :: tl => CONJ_DISCH h (← ExceptT.mk (CONJ_DISCHL tl th))
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let rec GSPEC th = ... ;; -/
#eval phrase 89
unsafe def GSPEC (th : thm) : IO (Except String thm) := (do
  let (_wl, w) := dest_thm th
  if is_forall w then do
    let v ← (genvar (type_of (← liftExcept (do pure (← dest_forall w).1)))
      : ExceptT String IO term)
    ExceptT.mk (GSPEC (← SPEC v th))
  else pure th
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let ANTE_CONJ_CONV tm = ... ;; -/
#eval phrase 90
unsafe def ANTE_CONJ_CONV (tm : term) : IO (Except String thm) := (do
  tryWith (do
    let (conj, c) ← liftExcept (dest_imp tm)
    let (a1, a2) ← liftExcept (dest_conj conj)
    let imp1 ← MP (← ASSUME tm) (← CONJ (← ASSUME a1) (← ASSUME a2))
    let ca ← liftExcept (HolCore.Bool.mk_conj a1 a2)
    let imp2 ← LIST_MP [(← CONJUNCT1 (← ASSUME ca)), (← CONJUNCT2 (← ASSUME ca))]
      (← ASSUME (← liftExcept (HolCore.Bool.mk_imp a1 (← liftExcept (HolCore.Bool.mk_imp a2 c)))))
    IMP_ANTISYM_RULE (← DISCH_ALL (← DISCH a1 (← DISCH a2 imp1)))
                     (← DISCH_ALL (← DISCH ca imp2)))
    (throw "ANTE_CONJ_CONV")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let bool_EQ_CONV = ... ;; -/
#eval phrase 91
unsafe def bool_EQ_CONV (tm : term) : IO (Except String thm) := (do
  let boolty : hol_type := bool_ty
  let bb : term := [[b:bool]]
  let clist ← (CONJUNCTS (← SPEC bb EQ_CLAUSES)).mapM (fun th => GEN bb th)
  let tb := clist.head!
  let bt := clist.tail!.head!
  let T : term := [[T]]
  tryWith (do
    let (l, r) ← liftExcept (dest_eq tm)
    if !(type_of l == boolty) then throw "check"
    if !(type_of r == boolty) then throw "check"
    if l == r then EQT_INTRO (← pure (REFL l))
    else if l == T then SPEC r tb
    else if r == T then SPEC l bt
    else throw "fail")
    (throw "bool_EQ_CONV")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let COND_CONV = ... ;; -/
#eval phrase 92
unsafe def COND_CONV (tm : term) : IO (Except String thm) := (do
  let T : term := [[T]]
  let F : term := [[F]]
  let vt ← (genvar aty : ExceptT String IO term)
  let vf ← (genvar aty : ExceptT String IO term)
  let gen (th : thm) : ExceptT String IO thm := GENL [vt, vf] th
  let (ct0, cf0) ← CONJ_PAIR (← SPECL [vt, vf] COND_CLAUSES)
  let CT ← gen ct0
  let CF ← gen cf0
  let (P, u, v) ← tryWith (do
      let (P, uv) ← liftExcept (dest_cond tm)
      pure (P, uv.1, uv.2))
    (throw "COND_CONV: not a conditional")
  let ty := type_of u
  if P == T then SPEC v (← SPEC u (← HolLight.INST_TYPE [(ty, aty)] CT))
  else if P == F then SPEC v (← SPEC u (← HolLight.INST_TYPE [(ty, aty)] CF))
  else if u == v then SPEC u (← SPEC P (← HolLight.INST_TYPE [(ty, aty)] COND_ID))
  else if aconv u v then do
    let cnd ← HolLight.AP_TERM (← liftExcept (rator tm)) (← liftExcept (HolCore.Equal.ALPHA v u))
    let thm' ← SPEC u (← SPEC P (← HolLight.INST_TYPE [(ty, aty)] COND_ID))
    TRANS cnd thm'
  else throw "COND_CONV: can't simplify conditional"
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let SUBST_MATCH eqth th = ... ;; -/
#eval phrase 93
unsafe def SUBST_MATCH (eqth : thm) (th : thm) : IO (Except String thm) := (do
  let (tm_inst, ty_inst) ← ExceptT.mk (find_match (← liftExcept (HolCore.Equal.lhs (concl eqth))) (concl th))
  HolLight.SUBS [(← INST tm_inst (← HolLight.INST_TYPE ty_inst eqth))] th
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let SUBST thl pat th = ... ;; -/
#eval phrase 94
unsafe def SUBST (thl : List (thm × term)) (pat : term) (th : thm) : IO (Except String thm) := (do
  let (eqs, vs) := unzip thl
  let mut gvs : List term := []
  for v in vs do gvs := gvs ++ [← (genvar (type_of v) : ExceptT String IO term)]
  let sb ← ExceptT.mk (HolCore.Basics.subst (← liftExcept (zip gvs vs)))
  let gpat ← ExceptT.mk (sb pat)
  let (ls, rs) := unzip (← liftExcept (eqs.mapM (fun e => dest_eq (concl e))))
  let mkEq ← ExceptT.mk (mk_eq : IO _)
  let ths ← (← liftExcept (zip gvs rs)).mapM (fun p => do ASSUME (← liftExcept (mkEq p)))
  let th1 ← ASSUME gpat
  let th2 ← HolLight.SUBS ths th1
  let th3 ← (ths.map concl).foldr (fun t acc => do DISCH t (← acc)) (DISCH gpat th2)
  let th4 ← INST (← liftExcept (zip ls gvs)) th3
  let th5 ← eqs.foldl (fun acc e => do MP (← acc) e) (pure th4)
  MP th5 th
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- let SUBST_CONV thvars template tm = ... ;; -/
#eval phrase 95
unsafe def SUBST_CONV (thvars : List (thm × term)) (template tm : term) :
    IO (Except String thm) := (do
  let (thms, vars) := unzip thvars
  let mut gvs : List term := []
  for v in vars do gvs := gvs ++ [← (genvar (type_of v) : ExceptT String IO term)]
  let sb ← ExceptT.mk (HolCore.Basics.subst (← liftExcept (zip gvs vars)))
  let gtemplate ← ExceptT.mk (sb template)
  let mkEq ← ExceptT.mk (mk_eq : IO _)
  ExceptT.mk (SUBST (← liftExcept (zip thms gvs)) (← liftExcept (mkEq (template, gtemplate)))
    (REFL tm))
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- Filtering rewrites.                                                       -/
/- ------------------------------------------------------------------------- -/

#eval phrase 96
unsafe def FILTER_PURE_ASM_REWRITE_RULE (f : term → Bool) (thl : List thm) (th : thm) :
    IO (Except String thm) := (do
  PURE_REWRITE_RULE ((← (HolCore.Lib.filter f (hyp th)).mapM (fun t => (liftExcept (ASSUME t) : ExceptT String IO thm))) ++ thl) th
  : ExceptT String IO thm).run
unsafe def FILTER_ASM_REWRITE_RULE (f : term → Bool) (thl : List thm) (th : thm) :
    IO (Except String thm) := (do
  REWRITE_RULE ((← (HolCore.Lib.filter f (hyp th)).mapM (fun t => (liftExcept (ASSUME t) : ExceptT String IO thm))) ++ thl) th
  : ExceptT String IO thm).run
unsafe def FILTER_PURE_ONCE_ASM_REWRITE_RULE (f : term → Bool) (thl : List thm) (th : thm) :
    IO (Except String thm) := (do
  PURE_ONCE_REWRITE_RULE ((← (HolCore.Lib.filter f (hyp th)).mapM (fun t => (liftExcept (ASSUME t) : ExceptT String IO thm))) ++ thl) th
  : ExceptT String IO thm).run
unsafe def FILTER_ONCE_ASM_REWRITE_RULE (f : term → Bool) (thl : List thm) (th : thm) :
    IO (Except String thm) := (do
  ONCE_REWRITE_RULE ((← (HolCore.Lib.filter f (hyp th)).mapM (fun t => (liftExcept (ASSUME t) : ExceptT String IO thm))) ++ thl) th
  : ExceptT String IO thm).run
#eval do IO.println "<fun>"; IO.println "<fun>"; IO.println "<fun>"; IO.println "<fun>"

#eval phrase 97
unsafe def FILTER_PURE_ASM_REWRITE_TAC (f : term → Bool) (thl : List thm) : tactic :=
  fun g => (PURE_REWRITE_TAC (HolCore.Lib.filter (fun th => f (concl th)) (g.1.map (fun p => p.2)) ++ thl)) g
unsafe def FILTER_ASM_REWRITE_TAC (f : term → Bool) (thl : List thm) : tactic :=
  fun g => (REWRITE_TAC (HolCore.Lib.filter (fun th => f (concl th)) (g.1.map (fun p => p.2)) ++ thl)) g
unsafe def FILTER_PURE_ONCE_ASM_REWRITE_TAC (f : term → Bool) (thl : List thm) : tactic :=
  fun g => (PURE_ONCE_REWRITE_TAC (HolCore.Lib.filter (fun th => f (concl th)) (g.1.map (fun p => p.2)) ++ thl)) g
unsafe def FILTER_ONCE_ASM_REWRITE_TAC (f : term → Bool) (thl : List thm) : tactic :=
  fun g => (ONCE_REWRITE_TAC (HolCore.Lib.filter (fun th => f (concl th)) (g.1.map (fun p => p.2)) ++ thl)) g
#eval do IO.println "<fun>"; IO.println "<fun>"; IO.println "<fun>"; IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- Tacticals.                                                                -/
/- ------------------------------------------------------------------------- -/

#eval phrase 98
unsafe def DISJ_CASES_THENL (l : List thm_tactic) : thm_tactic :=
  fun th => match l with
    | [] => fun _g => (pure (.error "end_itlist") : IO (Except String HolCore.Tactics.goalstate))
    | h :: t => (t.foldr (fun x acc => DISJ_CASES_THEN2 x acc) h) th
#eval IO.println "<fun>"

#eval phrase 99
unsafe def X_CASES_THENL (varsl : List (List term)) (ttacl : List thm_tactic) : thm_tactic :=
  fun th =>
    match (List.zip varsl ttacl).map (fun (vars, ttac) =>
      HolCore.Tactics.EVERY_TCL (vars.map (fun v => HolLight.X_CHOOSE_THEN v)) ttac) with
    | [] => fun _g => (pure (.error "end_itlist") : IO (Except String HolCore.Tactics.goalstate))
    | h :: t => (t.foldr (fun x acc => DISJ_CASES_THEN2 x acc) h) th
#eval IO.println "<fun>"

#eval phrase 100
unsafe def X_CASES_THEN (varsl : List (List term)) (ttac : thm_tactic) : thm_tactic :=
  fun th =>
    match varsl.map (fun vars =>
      HolCore.Tactics.EVERY_TCL (vars.map (fun v => HolLight.X_CHOOSE_THEN v)) ttac) with
    | [] => fun _g => (pure (.error "end_itlist") : IO (Except String HolCore.Tactics.goalstate))
    | h :: t => (t.foldr (fun x acc => DISJ_CASES_THEN2 x acc) h) th
#eval IO.println "<fun>"

#eval phrase 101
unsafe def CASES_THENL (ttacl : List thm_tactic) : thm_tactic :=
  fun th =>
    match ttacl.map (fun ttac => HolLight.REPEAT_TCL CHOOSE_THEN ttac) with
    | [] => fun _g => (pure (.error "end_itlist") : IO (Except String HolCore.Tactics.goalstate))
    | h :: t => (t.foldr (fun x acc => DISJ_CASES_THEN2 x acc) h) th
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- Tactics.                                                                  -/
/- ------------------------------------------------------------------------- -/

#eval phrase 102
unsafe def DISCARD_TAC : thm_tactic :=
  fun th g => do
    let truth : term := [[T]]
    if (truth :: g.1.map (fun p => concl p.2)).any (fun t => aconv (concl th) t)
    then ALL_TAC g
    else pure (Except.error "DISCARD_TAC")
#eval IO.println "<fun>"

#eval phrase 103
unsafe def GSUBST_TAC (substfn : List (term × term) → term → term) (ths : List thm) : tactic :=
  fun (asl, w) => ExceptT.run do
    let (ls, rs) := split (← liftExcept (ths.mapM (fun th => dest_eq (concl th))))
    let mut vars : List term := []
    for l in ls do vars := vars ++ [← (genvar (type_of l) : ExceptT String IO term)]
    let base := substfn (← liftExcept (combine (vars, ls))) w
    let syms ← ths.mapM (fun t => HolLight.SYM t)
    let symvars ← liftExcept (combine (syms, vars))
    let sb ← ExceptT.mk (HolCore.Basics.subst (← liftExcept (combine (rs, vars))))
    let newg ← ExceptT.mk (sb base)
    let just : HolCore.Tactics.justification := fun _i thl =>
      match thl with
      | [th] => SUBST symvars base th
      | _ => pure (.error "")
    pure (HolCore.Tactics.null_meta, [(asl, newg)], just)
#eval IO.println "<fun>"

#eval phrase 104
unsafe def SUBST_TAC (ths : List thm) : tactic :=
  GSUBST_TAC (fun ss t => match unsafeIO (do
    match ← HolCore.Basics.subst ss with
    | .ok f => f t
    | .error e => pure (.error e)) with | .ok (.ok r) => r | _ => t) ths
#eval IO.println "<fun>"

#eval phrase 105
unsafe def SUBST_OCCS_TAC (nlths : List (List Int × thm)) : tactic :=
  let (nll, ths) := split nlths
  GSUBST_TAC (fun ss t => match unsafeIO (subst_occs nll ss t) with
    | .ok (.ok r) => r | _ => t) ths
#eval IO.println "<fun>"

#eval phrase 106
unsafe def CHECK_ASSUME_TAC : thm_tactic :=
  fun gth => FIRST [CONTR_TAC gth, ACCEPT_TAC gth, DISCARD_TAC gth, ASSUME_TAC gth]
#eval IO.println "<fun>"

#eval phrase 107
unsafe def FILTER_GEN_TAC (tm : term) : tactic :=
  fun (asl, w) =>
    if is_forall w && !(tm == (match dest_forall w with | .ok p => p.1 | _ => tm))
    then GEN_TAC (asl, w)
    else (pure (.error "FILTER_GEN_TAC") : IO (Except String HolCore.Tactics.goalstate))
#eval IO.println "<fun>"

#eval phrase 108
unsafe def FILTER_DISCH_THEN (ttac : thm_tactic) (tm : term) : tactic :=
  fun (asl, w) =>
    if is_neg_imp w && !(free_in tm (match unsafeIO (dest_neg_imp w) with
        | .ok (.ok p) => p.1 | _ => w))
    then DISCH_THEN ttac (asl, w)
    else (pure (.error "FILTER_DISCH_THEN") : IO (Except String HolCore.Tactics.goalstate))
#eval IO.println "<fun>"

#eval phrase 109
unsafe def FILTER_STRIP_THEN (ttac : thm_tactic) (tm : term) : tactic :=
  FIRST [FILTER_GEN_TAC tm, FILTER_DISCH_THEN ttac tm, CONJ_TAC]
#eval IO.println "<fun>"

#eval phrase 110
unsafe def FILTER_DISCH_TAC (tm : term) : tactic := FILTER_DISCH_THEN STRIP_ASSUME_TAC tm
#eval IO.println "<fun>"

#eval phrase 111
unsafe def FILTER_STRIP_TAC (tm : term) : tactic := FILTER_STRIP_THEN STRIP_ASSUME_TAC tm
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- Resolution stuff.  (RES_CANON / IMP_RES_THEN / RES_THEN are hol88          -/
/- specific; IMP_RES_THEN here is the session's.)                            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 112
unsafe def RES_CANON (th : thm) : IO (Except String (List thm)) := (do
  let not_elim (th : thm) : ExceptT String IO (Bool × thm) :=
    if is_neg (concl th) then do pure (true, (← NOT_ELIM th)) else pure (false, th)
  let rec canon (fl : Bool) (th : thm) : ExceptT String IO (List thm) := do
    let w := concl th
    if is_conj w then do
      let (th1, th2) ← CONJ_PAIR th
      pure ((← canon fl th1) ++ (← canon fl th2))
    else if is_imp w && !(is_neg w) then do
      let (ante, _conc) ← ExceptT.mk (dest_neg_imp w)
      if is_conj ante then do
        let (a, b) ← liftExcept (dest_conj ante)
        let cth ← NOT_MP th (← CONJ (← ASSUME a) (← ASSUME b))
        let th1 ← DISCH b cth
        let th2 ← DISCH a cth
        pure ((← canon true (← DISCH a th1)) ++ (← canon true (← DISCH b th2)))
      else if is_disj ante then do
        let (a, b) ← liftExcept (dest_disj ante)
        let ath ← DISJ1 (← ASSUME a) b
        let bth ← DISJ2 a (← ASSUME b)
        let th1 ← DISCH a (← NOT_MP th ath)
        let th2 ← DISCH b (← NOT_MP th bth)
        pure ((← canon true th1) ++ (← canon true th2))
      else if is_exists ante then do
        let (v, body) ← liftExcept (dest_exists ante)
        let newv ← liftExcept (variant (thm_frees th) v)
        let sb ← ExceptT.mk (HolCore.Basics.subst [(newv, v)])
        let newa ← ExceptT.mk (sb body)
        let th1 ← NOT_MP th (← EXISTS (ante, newv) (← ASSUME newa))
        canon true (← DISCH newa th1)
      else do
        let l ← canon true (← UNDISCH th)
        l.mapM (fun t => do GEN_ALL (← DISCH ante t))
    else if is_eq w && (type_of (← liftExcept (rand w)) == bool_ty) then do
      let (th1, th2) ← EQ_IMP_RULE th
      let pre ← if fl then do pure [(← GEN_ALL th)] else pure []
      pure (pre ++ (← canon true th1) ++ (← canon true th2))
    else if is_forall w then do
      let (vs, _body) := strip_forall w
      let fvs := thm_frees th
      let nvs ← vs.foldr (fun v acc => do
        let nv ← acc
        pure ((← liftExcept (variant (nv ++ fvs) v)) :: nv)) (pure ([] : List term))
      canon fl (← SPECL nvs th)
    else if fl then do pure [(← GEN_ALL th)] else pure []
  tryWith (do
    let args ← (CONJUNCTS (← SPEC_ALL th)).mapM (fun c => do not_elim (← SPEC_ALL c))
    let imps ← args.foldr (fun (p : Bool × thm) acc => do
      pure ((← (← canon p.1 p.2).mapM (fun t => GEN_ALL t)) ++ (← acc))) (pure ([] : List thm))
    liftExcept (HolCore.Lib.check (fun l => !(l == [])) imps))
    (throw "RES_CANON: no implication is derivable from input thm.")
  : ExceptT String IO (List thm)).run
#eval IO.println "<fun>"

#eval phrase 113
-- let IMP_RES_THEN,RES_THEN = ... ;;  (two <fun>s)
unsafe def IMP_RES_THEN : thm_tactic → thm → tactic := Session.IMP_RES_THEN
unsafe def RES_THEN (ttac : thm_tactic) : tactic :=
  fun (asl, g) => do
    let MATCH_MP_ (impth : thm) (th : thm) : IO (Except String thm) := (do
      let sth ← SPEC_ALL impth
      let (ante, _) ← ExceptT.mk (dest_neg_imp (concl sth))
      let (_, b, c) ← HolLight.term_match [] ante (concl th)
      NOT_MP (← ExceptT.mk (INST_TY_TERM (b, c) sth)) th
      : ExceptT String IO thm).run
    let asm := asl.map (fun p => p.2)
    -- itlist (@) (mapfilter RES_CANON asm) []
    let mut ths : List thm := []
    for a in asm do
      match ← RES_CANON a with
      | .ok l => ths := ths ++ l
      | .error _ => pure ()
    if ths == [] then pure (Except.error "RES_THEN: no implication") else do
      -- itlist (fun th -> (@) (mapfilter (MATCH_MP th) asm)) imps []
      let mut l : List thm := []
      for th in ths do
        for a in asm do
          match ← MATCH_MP_ th a with
          | .ok r => l := l ++ [r]
          | .error _ => pure ()
      if l == [] then pure (Except.error "RES_THEN: no resolvents ") else do
        let tacs := l.map (fun r => ttac r)
        EVERY tacs (asl, g)
#eval do IO.println "<fun>"; IO.println "<fun>"

#eval phrase 114
unsafe def IMP_RES_TAC (th : thm) : tactic :=
  fun g => do
    match ← IMP_RES_THEN (HolCore.Tactics.REPEAT_GTCL IMP_RES_THEN STRIP_ASSUME_TAC) th g with
    | .ok r => pure (Except.ok r)
    | .error _ => ALL_TAC g
#eval IO.println "<fun>"

#eval phrase 115
unsafe def RES_TAC : tactic :=
  fun g => do
    match ← RES_THEN (HolCore.Tactics.REPEAT_GTCL IMP_RES_THEN STRIP_ASSUME_TAC) g with
    | .ok r => pure (Except.ok r)
    | .error _ => ALL_TAC g
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- Stuff for handling type definitions.                                      -/
/- ------------------------------------------------------------------------- -/

#eval phrase 116
unsafe def prove_rep_fn_one_one (th : thm) : IO (Except String thm) := (do
  tryWith (do
    let thm' ← CONJUNCT1 th
    let (A, R) ← (do
      let (c, rA) ← liftExcept (dest_comb (← liftExcept (HolCore.Equal.lhs (← liftExcept (do pure (← dest_forall (concl thm')).2)))))
      pure (c, ← liftExcept (rator rA)))
    let (_, tys) ← liftExcept (dest_type (type_of R))
    let aty0 := tys.head!
    let a ← ExceptT.mk (mk_primed_var ("a", aty0))
    let a' ← liftExcept (variant [a] a)
    let a_eq_a' ← ExceptT.mk (mkEqP (a, a'))
    let Ra_eq_Ra' ← ExceptT.mk (mkEqP ((← liftExcept (mk_comb R a)), (← liftExcept (mk_comb R a'))))
    let th1 ← HolLight.AP_TERM A (← ASSUME Ra_eq_Ra')
    let ga1 ← (genvar aty0 : ExceptT String IO term)
    let ga2 ← (genvar aty0 : ExceptT String IO term)
    let th2 ← ExceptT.mk (SUBST [((← SPEC a thm'), ga1), ((← SPEC a' thm'), ga2)]
      (← ExceptT.mk (mkEqP (ga1, ga2))) th1)
    let th3 ← DISCH a_eq_a' (← HolLight.AP_TERM R (← ASSUME a_eq_a'))
    GEN a (← GEN a' (← IMP_ANTISYM_RULE (← DISCH Ra_eq_Ra' th2) th3)))
    (throw "prove_rep_fn_one_one")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 117
unsafe def prove_rep_fn_onto (th : thm) : IO (Except String thm) := (do
  tryWith (do
    let cs := CONJUNCTS th
    let th1 := cs.head!
    let th2 := cs.tail!.head!
    let (r, eq) ← (do
      let (r, b) ← liftExcept (dest_forall (concl th2))
      pure (r, ← liftExcept (HolCore.Equal.rhs b)))
    let (RE, ar) ← liftExcept (dest_comb (← liftExcept (HolCore.Equal.lhs eq)))
    let a ← ExceptT.mk (mk_primed_var ("a", type_of ar))
    let sra ← ExceptT.mk (mkEqP (r, (← liftExcept (mk_comb RE a))))
    let ex ← liftExcept (HolCore.Bool.mk_exists a sra)
    let imp1 ← EXISTS (ex, ar) (← HolLight.SYM (← ASSUME eq))
    let v ← (genvar (type_of r) : ExceptT String IO term)
    let A ← liftExcept (rator ar)
    let s' ← HolLight.AP_TERM RE (← SPEC a th1)
    let th ← ExceptT.mk (SUBST [((← HolLight.SYM (← ASSUME sra)), v)]
      (← ExceptT.mk (mkEqP ((← liftExcept (mk_comb RE (← liftExcept (mk_comb A v)))), v))) s')
    let imp2 ← CHOOSE (a, ← ASSUME ex) th
    let swap ← IMP_ANTISYM_RULE (← DISCH eq imp1) (← DISCH ex imp2)
    GEN r (← TRANS (← SPEC r th2) swap))
    (throw "prove_rep_fn_onto")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 118
unsafe def prove_abs_fn_onto (th : thm) : IO (Except String thm) := (do
  tryWith (do
    let cs := CONJUNCTS th
    let th1 := cs.head!
    let th2 := cs.tail!.head!
    let (a, A, R) ← (do
      let (a, b) ← liftExcept (dest_forall (concl th1))
      let (c, rA) ← liftExcept (dest_comb (← liftExcept (HolCore.Equal.lhs b)))
      pure (a, c, ← liftExcept (rator rA)))
    let thm1 ← EQT_ELIM (← TRANS (← SPEC (← liftExcept (mk_comb R a)) th2)
      (← EQT_INTRO (← HolLight.AP_TERM R (← SPEC a th1))))
    let thm2 ← HolLight.SYM (← SPEC a th1)
    let (r, P) ← (do
      let (r, b) ← liftExcept (dest_forall (concl th2))
      pure (r, ← liftExcept (rator (← liftExcept (HolCore.Equal.lhs b)))))
    let ex ← liftExcept (HolCore.Bool.mk_exists r
      (← liftExcept (HolCore.Bool.mk_conj (← ExceptT.mk (mkEqP (a, (← liftExcept (mk_comb A r)))))
        (← liftExcept (mk_comb P r)))))
    GEN a (← EXISTS (ex, (← liftExcept (mk_comb R a))) (← CONJ thm2 thm1)))
    (throw "prove_abs_fn_onto")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 119
unsafe def prove_abs_fn_one_one (th : thm) : IO (Except String thm) := (do
  tryWith (do
    let cs := CONJUNCTS th
    let th1 := cs.head!
    let th2 := cs.tail!.head!
    let (r, P) ← (do
      let (r, b) ← liftExcept (dest_forall (concl th2))
      pure (r, ← liftExcept (rator (← liftExcept (HolCore.Equal.lhs b)))))
    let (A, R) ← (do
      let (c, rA) ← liftExcept (dest_comb (← liftExcept (HolCore.Equal.lhs (← liftExcept (do pure (← dest_forall (concl th1)).2)))))
      pure (c, ← liftExcept (rator rA)))
    let r' ← liftExcept (variant [r] r)
    let as1 ← ASSUME (← liftExcept (mk_comb P r))
    let as2 ← ASSUME (← liftExcept (mk_comb P r'))
    let t1 ← EQ_MP (← SPEC r th2) as1
    let t2 ← EQ_MP (← SPEC r' th2) as2
    let eq ← ExceptT.mk (mkEqP ((← liftExcept (mk_comb A r)), (← liftExcept (mk_comb A r'))))
    let v1 ← (genvar (type_of r) : ExceptT String IO term)
    let v2 ← (genvar (type_of r) : ExceptT String IO term)
    let i1 ← DISCH eq (← ExceptT.mk (SUBST [(t1, v1), (t2, v2)]
      (← ExceptT.mk (mkEqP (v1, v2))) (← HolLight.AP_TERM R (← ASSUME eq))))
    let rr' ← ExceptT.mk (mkEqP (r, r'))
    let i2 ← DISCH rr' (← HolLight.AP_TERM A (← ASSUME rr'))
    let thm' ← IMP_ANTISYM_RULE i1 i2
    let disch ← DISCH (← liftExcept (mk_comb P r)) (← DISCH (← liftExcept (mk_comb P r')) thm')
    GEN r (← GEN r' disch))
    (throw "prove_abs_fn_one_one")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- AC rewriting.  (We reuse the session's AC conversion; same value.)        -/
/- ------------------------------------------------------------------------- -/

#eval phrase 120
unsafe def AC_CONV : thm × thm → term → IO (Except String thm)
  | (_associative, commutative), tm => Session.AC commutative tm
#eval IO.println "<fun>"

#eval phrase 121
unsafe def AC_RULE (ths : thm × thm) (tm : term) : IO (Except String thm) := (do
  EQT_ELIM (← ExceptT.mk (AC_CONV ths tm))
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- The order of picking conditionals is different!                           -/
/- ------------------------------------------------------------------------- -/

#eval phrase 122
unsafe def COND_CASES_TAC : tactic := Session.COND_CASES_TAC
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- MATCH_MP_TAC allows universals on the right of implication.               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 123
unsafe def MATCH_MP_TAC (th : thm) : tactic :=
  fun g => do
    match ← Session.MATCH_MP_TAC th g with
    | .ok r => pure (Except.ok r)
    | .error _ =>
      match ← (PURE_REWRITE_RULE [RIGHT_IMP_FORALL_THM] th : IO (Except String thm)) with
      | .ok th' => Session.MATCH_MP_TAC th' g
      | .error e => pure (.error e)
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- Various theorems have different names.                                    -/
/- ------------------------------------------------------------------------- -/

#eval phrase 124
unsafe def ZERO_LESS_EQ : thm := keep "ZERO_LESS_EQ" fun _ => LE_0
#eval ZERO_LESS_EQ

#eval phrase 125
unsafe def LESS_EQ_MONO : thm := keep "LESS_EQ_MONO" fun _ => LE_SUC
#eval LESS_EQ_MONO

#eval phrase 126
unsafe def NOT_LESS : thm := keep "NOT_LESS" fun _ => NOT_LT
#eval NOT_LESS

#eval phrase 127
unsafe def LESS_0 : thm := keep "LESS_0" fun _ => LT_0
#eval LESS_0

#eval phrase 128
unsafe def LESS_EQ_REFL : thm := keep "LESS_EQ_REFL" fun _ => LE_REFL
#eval LESS_EQ_REFL

#eval phrase 129
unsafe def LESS_EQUAL_ANTISYM : thm := keep "LESS_EQUAL_ANTISYM" fun _ =>
  ((do GEN_ALL (← EQ_IMP_RULE (← SPEC_ALL LE_ANTISYM)).1 : ExceptT String IO thm).run : thm)
#eval LESS_EQUAL_ANTISYM

#eval phrase 130
unsafe def NOT_LESS_0 : thm := keep "NOT_LESS_0" fun _ =>
  ((do GEN_ALL (← EQF_ELIM (← SPEC_ALL (← CONJUNCT1 LT))) : ExceptT String IO thm).run : thm)
#eval NOT_LESS_0

#eval phrase 131
unsafe def LESS_TRANS : thm := keep "LESS_TRANS" fun _ => LT_TRANS
#eval LESS_TRANS

#eval phrase 132
unsafe def LESS_LEMMA1 : thm := keep "LESS_LEMMA1" fun _ =>
  ((do GEN_ALL (← EQ_IMP_RULE (← SPEC_ALL (← CONJUNCT2 LT))).1 : ExceptT String IO thm).run : thm)
#eval LESS_LEMMA1

#eval phrase 133
unsafe def LESS_SUC_REFL : thm := keep "LESS_SUC_REFL" fun _ =>
  ((do prove ([[!n. n < SUC n]]) (REWRITE_TAC [LT]) : ExceptT String IO thm).run : thm)
#eval LESS_SUC_REFL

#eval phrase 134
unsafe def FACT_LESS : thm := keep "FACT_LESS" fun _ => FACT_LT
#eval FACT_LESS

#eval phrase 135
unsafe def LESS_EQ_SUC_REFL : thm := keep "LESS_EQ_SUC_REFL" fun _ =>
  ((do prove ([[!n. n <= SUC n]]) (REWRITE_TAC [LE, LE_REFL]) : ExceptT String IO thm).run : thm)
#eval LESS_EQ_SUC_REFL

#eval phrase 136
unsafe def LESS_EQ_ADD : thm := keep "LESS_EQ_ADD" fun _ => LE_ADD
#eval LESS_EQ_ADD

#eval phrase 137
unsafe def GREATER_EQ : thm := keep "GREATER_EQ" fun _ => GE
#eval GREATER_EQ

#eval phrase 138
unsafe def LESS_EQUAL_ADD : thm := keep "LESS_EQUAL_ADD" fun _ =>
  ((do GEN_ALL (← EQ_IMP_RULE (← SPEC_ALL LE_EXISTS)).1 : ExceptT String IO thm).run : thm)
#eval LESS_EQUAL_ADD

#eval phrase 139
unsafe def LESS_EQ_IMP_LESS_SUC : thm := keep "LESS_EQ_IMP_LESS_SUC" fun _ =>
  ((do GEN_ALL (← EQ_IMP_RULE (← SPEC_ALL LT_SUC_LE)).2 : ExceptT String IO thm).run : thm)
#eval LESS_EQ_IMP_LESS_SUC

#eval phrase 140
unsafe def LESS_IMP_LESS_OR_EQ : thm := keep "LESS_IMP_LESS_OR_EQ" fun _ => LT_IMP_LE
#eval LESS_IMP_LESS_OR_EQ

#eval phrase 141
unsafe def LESS_MONO_ADD : thm := keep "LESS_MONO_ADD" fun _ =>
  ((do GEN_ALL (← EQ_IMP_RULE (← SPEC_ALL LT_ADD_RCANCEL)).2 : ExceptT String IO thm).run : thm)
#eval LESS_MONO_ADD

#eval phrase 142
unsafe def LESS_SUC : thm := keep "LESS_SUC" fun _ =>
  ((do prove ([[!m n. m < n ==> m < (SUC n)]]) (MESON_TAC [LT]) : ExceptT String IO thm).run : thm)
#eval LESS_SUC

#eval phrase 143
unsafe def LESS_CASES : thm := keep "LESS_CASES" fun _ => LTE_CASES
#eval LESS_CASES

#eval phrase 144
unsafe def LESS_EQ : thm := keep "LESS_EQ" fun _ =>
  ((do HolLight.GSYM LE_SUC_LT : ExceptT String IO thm).run : thm)
#eval LESS_EQ

#eval phrase 145
unsafe def LESS_OR_EQ : thm := keep "LESS_OR_EQ" fun _ => LE_LT
#eval LESS_OR_EQ

#eval phrase 146
unsafe def LESS_ADD_1 : thm := keep "LESS_ADD_1" fun _ =>
  ((do GEN_ALL (← EQ_IMP_RULE (← SPEC_ALL (← REWRITE_RULE [ADD1] LT_EXISTS))).1
    : ExceptT String IO thm).run : thm)
#eval LESS_ADD_1

#eval phrase 147
unsafe def SUC_SUB1 : thm := keep "SUC_SUB1" fun _ => (ARITH_RULE [[!m. SUC m - 1 = m]] : thm)
#eval SUC_SUB1

#eval phrase 148
unsafe def LESS_MONO_EQ : thm := keep "LESS_MONO_EQ" fun _ => LT_SUC
#eval LESS_MONO_EQ

#eval phrase 149
unsafe def LESS_ADD_SUC : thm := keep "LESS_ADD_SUC" fun _ =>
  (ARITH_RULE [[!m n. m < m + SUC n]] : thm)
#eval LESS_ADD_SUC

#eval phrase 150
unsafe def LESS_REFL : thm := keep "LESS_REFL" fun _ => LT_REFL
#eval LESS_REFL

#eval phrase 151
unsafe def INV_SUC_EQ : thm := keep "INV_SUC_EQ" fun _ => SUC_INJ
#eval INV_SUC_EQ

#eval phrase 152
unsafe def LESS_EQ_CASES : thm := keep "LESS_EQ_CASES" fun _ => LE_CASES
#eval LESS_EQ_CASES

#eval phrase 153
unsafe def LESS_EQ_TRANS : thm := keep "LESS_EQ_TRANS" fun _ => LE_TRANS
#eval LESS_EQ_TRANS

#eval phrase 154
unsafe def LESS_THM : thm := keep "LESS_THM" fun _ =>
  ((do CONJUNCT2 LT : ExceptT String IO thm).run : thm)
#eval LESS_THM

#eval phrase 155
unsafe def GREATER : thm := keep "GREATER" fun _ => GT
#eval GREATER

#eval phrase 156
unsafe def LESS_EQ_0 : thm := keep "LESS_EQ_0" fun _ =>
  ((do CONJUNCT1 LE : ExceptT String IO thm).run : thm)
#eval LESS_EQ_0

#eval phrase 157
unsafe def OR_LESS : thm := keep "OR_LESS" fun _ =>
  ((do GEN_ALL (← EQ_IMP_RULE (← SPEC_ALL LE_SUC_LT)).1 : ExceptT String IO thm).run : thm)
#eval OR_LESS

#eval phrase 158
unsafe def SUB_EQUAL_0 : thm := keep "SUB_EQUAL_0" fun _ => SUB_REFL
#eval SUB_EQUAL_0

#eval phrase 159
unsafe def SUB_MONO_EQ : thm := keep "SUB_MONO_EQ" fun _ => SUB_SUC
#eval SUB_MONO_EQ

#eval phrase 160
unsafe def NOT_SUC_LESS_EQ : thm := keep "NOT_SUC_LESS_EQ" fun _ =>
  (ARITH_RULE [[!n m. ~(SUC n <= m) <=> m <= n]] : thm)
#eval NOT_SUC_LESS_EQ

#eval phrase 161
unsafe def SUC_NOT : thm := keep "SUC_NOT" fun _ =>
  ((do HolLight.GSYM NOT_SUC : ExceptT String IO thm).run : thm)
#eval SUC_NOT

#eval phrase 162
unsafe def LESS_LESS_CASES : thm := keep "LESS_LESS_CASES" fun _ =>
  (ARITH_RULE [[!m n:num. (m = n) \/ m < n \/ n < m]] : thm)
#eval LESS_LESS_CASES

#eval phrase 163
unsafe def NOT_LESS_EQUAL : thm := keep "NOT_LESS_EQUAL" fun _ => NOT_LE
#eval NOT_LESS_EQUAL

#eval phrase 164
unsafe def LESS_EQ_EXISTS : thm := keep "LESS_EQ_EXISTS" fun _ => LE_EXISTS
#eval LESS_EQ_EXISTS

#eval phrase 165
unsafe def LESS_MONO_ADD_EQ : thm := keep "LESS_MONO_ADD_EQ" fun _ => LT_ADD_RCANCEL
#eval LESS_MONO_ADD_EQ

#eval phrase 166
unsafe def LESS_LESS_EQ_TRANS : thm := keep "LESS_LESS_EQ_TRANS" fun _ => LTE_TRANS
#eval LESS_LESS_EQ_TRANS

#eval phrase 167
unsafe def SUB_SUB : thm := keep "SUB_SUB" fun _ =>
  (ARITH_RULE [[!b c. c <= b ==> (!a:num. a - (b - c) = (a + c) - b)]] : thm)
#eval SUB_SUB

#eval phrase 168
unsafe def LESS_CASES_IMP : thm := keep "LESS_CASES_IMP" fun _ =>
  (ARITH_RULE [[!m n:num. ~(m < n) /\ ~(m = n) ==> n < m]] : thm)
#eval LESS_CASES_IMP

#eval phrase 169
unsafe def SUB_LESS_EQ : thm := keep "SUB_LESS_EQ" fun _ =>
  (ARITH_RULE [[!n m:num. (n - m) <= n]] : thm)
#eval SUB_LESS_EQ

#eval phrase 170
unsafe def SUB_EQ_EQ_0 : thm := keep "SUB_EQ_EQ_0" fun _ =>
  (ARITH_RULE [[!m n:num. (m - n = m) = (m = 0) \/ (n = 0)]] : thm)
#eval SUB_EQ_EQ_0

#eval phrase 171
unsafe def SUB_LEFT_LESS_EQ : thm := keep "SUB_LEFT_LESS_EQ" fun _ =>
  (ARITH_RULE [[!m n p:num. m <= (n - p) <=> (m + p) <= n \/ m <= 0]] : thm)
#eval SUB_LEFT_LESS_EQ

#eval phrase 172
unsafe def SUB_LEFT_GREATER_EQ : thm := keep "SUB_LEFT_GREATER_EQ" fun _ =>
  (ARITH_RULE [[!m n p:num. m >= (n - p) <=> (m + p) >= n]] : thm)
#eval SUB_LEFT_GREATER_EQ

#eval phrase 173
unsafe def LESS_EQ_LESS_TRANS : thm := keep "LESS_EQ_LESS_TRANS" fun _ => LET_TRANS
#eval LESS_EQ_LESS_TRANS

#eval phrase 174
unsafe def LESS_0_CASES : thm := keep "LESS_0_CASES" fun _ =>
  (ARITH_RULE [[!m. (0 = m) \/ 0 < m]] : thm)
#eval LESS_0_CASES

#eval phrase 175
unsafe def LESS_OR : thm := keep "LESS_OR" fun _ =>
  (ARITH_RULE [[!m n. m < n ==> (SUC m) <= n]] : thm)
#eval LESS_OR

#eval phrase 176
unsafe def SUB : thm := keep "SUB" fun _ =>
  (ARITH_RULE [[(!m. 0 - m = 0) /\
    (!m n. (SUC m) - n = (if m < n then 0 else SUC(m - n)))]] : thm)
#eval SUB

#eval phrase 177
unsafe def LESS_MULT_MONO : thm := keep "LESS_MULT_MONO" fun _ =>
  ((do prove ([[!m i n. ((SUC n) * m) < ((SUC n) * i) <=> m < i]]) (REWRITE_TAC [LT_MULT_LCANCEL, NOT_SUC]) : ExceptT String IO thm).run : thm)
#eval LESS_MULT_MONO

#eval phrase 178
unsafe def LESS_MONO_MULT : thm := keep "LESS_MONO_MULT" fun _ =>
  ((do prove ([[!m n p. m <= n ==> (m * p) <= (n * p)]]) (SIMP_TAC [LE_MULT_RCANCEL]) : ExceptT String IO thm).run : thm)
#eval LESS_MONO_MULT

#eval phrase 179
unsafe def LESS_MULT2 : thm := keep "LESS_MULT2" fun _ =>
  ((do prove ([[!m n. 0 < m /\ 0 < n ==> 0 < (m * n)]]) (REWRITE_TAC [LT_MULT]) : ExceptT String IO thm).run : thm)
#eval LESS_MULT2

#eval phrase 180
unsafe def SUBSET_FINITE : thm := keep "SUBSET_FINITE" fun _ =>
  ((do prove ([[!s. FINITE s ==> (!t. t SUBSET s ==> FINITE t)]]) (MESON_TAC [FINITE_SUBSET]) : ExceptT String IO thm).run : thm)
#eval SUBSET_FINITE

#eval phrase 181
unsafe def LESS_EQ_SUC : thm := keep "LESS_EQ_SUC" fun _ =>
  ((do prove ([[!n. m <= SUC n <=> (m = SUC n) \/ m <= n]]) (REWRITE_TAC [LE]) : ExceptT String IO thm).run : thm)
#eval LESS_EQ_SUC

/- ------------------------------------------------------------------------- -/
/- Restore traditional (low) parse status of "=".                            -/
/- ------------------------------------------------------------------------- -/
#eval phrase 182
#eval Session.parse_as_infix ("=", (2, "right"))

end HolExamples.Hol88
