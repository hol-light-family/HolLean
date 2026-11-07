/- File: Hol100/Ramsey.lean
Translation of HOL Light's 100/ramsey.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

ramsey.ml begins with most of Examples/hol88.ml (the HOL88 compatibility
layer); those phrases are translated as in HolExamples/Hol88.lean.
-/
import Hol100.Common
import HolExamples.Common
import HolLibrary.Analysis
open HolCore.Kernel HolCore.Basics Session HolLight.Syntax HolExamples
open HolCore.Lib (zip unzip partition can)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)
open HolLight (tryWith tactic_of)
open scoped HolLight
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
namespace Hol100.Ramsey


/- The session's IO-valued `prove` lifted into `ExceptT String IO`, so tactic
   scripts read as in OCaml. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/- Local `ioconv` wrappers around the pure (Except-valued) kernel conversions,
   and a `TAUT` usable inside an `ExceptT String IO` do-block. -/
private def ALPHA_CONV_io (v : term) : HolCore.Equal.ioconv :=
  fun t => pure (HolCore.Equal.ALPHA_CONV v t)
private def GEN_ALPHA_CONV_io (v : term) : HolCore.Equal.ioconv :=
  fun t => pure (HolCore.Equal.GEN_ALPHA_CONV v t)
private def ETA_CONV_io : HolCore.Equal.ioconv :=
  fun t => pure (Session.ETA_CONV t)
private def BINOP_CONV_io (c : HolCore.Equal.ioconv) : HolCore.Equal.ioconv :=
  HolLight.BINOP_CONV c
private def TAUT_io (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.TAUT tm)
private def mkEqP (pr : term × term) : IO (Except String term) := do
  match ← (mk_eq : IO _) with | .ok f => pure (f pr) | .error e => pure (.error e)

/- ========================================================================= -/
/- HOL88 compatibility: various things missing or different in HOL Light.    -/
/- ========================================================================= -/

/- let (upto) = (--);; -/
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def nc (tm : term) : ExceptT String IO thm := ExceptT.mk (num_CONV tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)

#eval phrase 1
def is_neg_imp (tm : term) : Bool := is_neg tm || is_imp tm
#eval IO.println "<fun>"

#eval phrase 2
def dest_neg_imp (tm : term) : IO (Except String (term × term)) := (do
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

/- ------------------------------------------------------------------------- -/
/- These get overwritten by the subgoal stuff.                               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 3
def PROVE : term × HolCore.Tactics.tactic → IO (Except String thm)
  | (g, t) => Session.prove g t
#eval IO.println "<fun>"

#eval phrase 4
def prove_thm : String × term × HolCore.Tactics.tactic → IO (Except String thm)
  | (_s, g, t) => Session.prove g t
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- The quantifier movement conversions.                                      -/
/- These are written here as hol88.ml does (analysis.ml has the same      -/
/- definitions, but loading it would change the parser state).          -/
/- ------------------------------------------------------------------------- -/

/-- `GEN_ALPHA_CONV` (equal.ml) as a conversion. -/
private def GEN_ALPHA_CONV (v : term) : HolCore.Equal.ioconv :=
  HolLibrary.Analysis.GEN_ALPHA_CONV v

/- ------------------------------------------------------------------------- -/
/- The quantifier movement conversions.                                      -/
/- ------------------------------------------------------------------------- -/

#eval phrase 5
def CONV_OF_RCONV : HolCore.Equal.ioconv → HolCore.Equal.ioconv :=
  fun conv tm => ExceptT.run do
    let v ← liftExcept (HolLibrary.Analysis.getBv tm)
    let th1 ← ExceptT.mk (conv tm)
    let th2 ← ExceptT.mk (HolLight.ONCE_DEPTH_CONV (GEN_ALPHA_CONV v)
      (← liftExcept (HolCore.Equal.rhs (concl th1))))
    liftExcept (HolCore.Kernel.TRANS th1 th2)
#eval IO.println "<fun>"

#eval phrase 6
def CONV_OF_THM : thm → HolCore.Equal.ioconv :=
  fun th => CONV_OF_RCONV (REWR_CONV th)
#eval IO.println "<fun>"

#eval phrase 7
def X_FUN_EQ_CONV : term → HolCore.Equal.ioconv :=
  fun v => REWR_CONV FUN_EQ_THM THENC GEN_ALPHA_CONV v
#eval IO.println "<fun>"

#eval phrase 8
def FUN_EQ_CONV : HolCore.Equal.ioconv := fun tm => ExceptT.run do
  let vars := frees tm
  let (op, tys) ← liftExcept (do dest_type (type_of (← HolCore.Equal.lhs tm)))
  let (ty1, _ty2) ← match tys with
    | [a, b] => pure (a, b)
    | _ => throw "Match_failure"
  if op == "fun" then
    let varnm ← if is_vartype ty1 then pure "x" else do
      let (c, _) ← liftExcept (dest_type ty1)
      match HolCore.Lib.explode c with
      | h :: _ => pure h
      | [] => throw "hd"
    let x ← liftExcept (variant vars (mk_var varnm ty1))
    ExceptT.mk (X_FUN_EQ_CONV x tm)
  else throw "FUN_EQ_CONV"
#eval IO.println "<fun>"

#eval phrase 9
def SINGLE_DEPTH_CONV : HolCore.Equal.ioconv → HolCore.Equal.ioconv :=
  HolLibrary.Analysis.singleDepthConv
#eval IO.println "<fun>"

#eval phrase 10
def SKOLEM_CONV : HolCore.Equal.ioconv :=
  SINGLE_DEPTH_CONV (REWR_CONV SKOLEM_THM)
#eval IO.println "<fun>"

#eval phrase 11
def X_SKOLEM_CONV : term → HolCore.Equal.ioconv :=
  fun v => SKOLEM_CONV THENC GEN_ALPHA_CONV v
#eval IO.println "<fun>"

#eval phrase 12
def EXISTS_UNIQUE_CONV : HolCore.Equal.ioconv := fun tm => ExceptT.run do
  let v ← liftExcept (do bndvar (← rand tm))
  let th1 ← ExceptT.mk (REWR_CONV EXISTS_UNIQUE_THM tm)
  let tm1 ← liftExcept (HolCore.Equal.rhs (concl th1))
  let vars := frees tm1
  let v ← liftExcept (variant vars v)
  let v' ← liftExcept (variant (v :: vars) v)
  let th2 ← ExceptT.mk ((HolLight.LAND_CONV (GEN_ALPHA_CONV v) THENC
     HolLight.RAND_CONV (HolLight.BINDER_CONV (GEN_ALPHA_CONV v') THENC
                GEN_ALPHA_CONV v)) tm1)
  liftExcept (HolCore.Kernel.TRANS th1 th2)
#eval IO.println "<fun>"

#eval phrase 13
def NOT_FORALL_CONV : HolCore.Equal.ioconv := CONV_OF_THM NOT_FORALL_THM
#eval IO.println "<fun>"

#eval phrase 14
def NOT_EXISTS_CONV : HolCore.Equal.ioconv := CONV_OF_THM NOT_EXISTS_THM
#eval IO.println "<fun>"

#eval phrase 15
def RIGHT_IMP_EXISTS_CONV : HolCore.Equal.ioconv := CONV_OF_THM RIGHT_IMP_EXISTS_THM
#eval IO.println "<fun>"

#eval phrase 16
def FORALL_IMP_CONV : HolCore.Equal.ioconv := CONV_OF_RCONV
  (REWR_CONV TRIV_FORALL_IMP_THM ORELSEC
   REWR_CONV RIGHT_FORALL_IMP_THM ORELSEC
   REWR_CONV LEFT_FORALL_IMP_THM)
#eval IO.println "<fun>"

#eval phrase 17
def EXISTS_AND_CONV : HolCore.Equal.ioconv := CONV_OF_RCONV
  (REWR_CONV TRIV_EXISTS_AND_THM ORELSEC
   REWR_CONV LEFT_EXISTS_AND_THM ORELSEC
   REWR_CONV RIGHT_EXISTS_AND_THM)
#eval IO.println "<fun>"

#eval phrase 18
def LEFT_IMP_EXISTS_CONV : HolCore.Equal.ioconv := CONV_OF_THM LEFT_IMP_EXISTS_THM
#eval IO.println "<fun>"

#eval phrase 19
def LEFT_AND_EXISTS_CONV : HolCore.Equal.ioconv := fun tm => ExceptT.run do
  let v ← liftExcept (do bndvar (← rand (← rand (← rator tm))))
  ExceptT.mk ((REWR_CONV LEFT_AND_EXISTS_THM THENC HolLight.TRY_CONV (GEN_ALPHA_CONV v)) tm)
#eval IO.println "<fun>"

#eval phrase 20
def RIGHT_AND_EXISTS_CONV : HolCore.Equal.ioconv := CONV_OF_THM RIGHT_AND_EXISTS_THM
#eval IO.println "<fun>"

#eval phrase 21
def AND_FORALL_CONV : HolCore.Equal.ioconv := CONV_OF_THM AND_FORALL_THM
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- The slew of named tautologies.                                            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 22
def AND1_THM : thm := keep "AND1_THM" fun _ => (TAUT [[!t1 t2. t1 /\ t2 ==> t1]] : thm)
#eval AND1_THM

#eval phrase 23
def AND2_THM : thm := keep "AND2_THM" fun _ => (TAUT [[!t1 t2. t1 /\ t2 ==> t2]] : thm)
#eval AND2_THM

#eval phrase 24
def AND_IMP_INTRO : thm := keep "AND_IMP_INTRO" fun _ => (do
  tt (← ExceptT.mk [[!t1 t2 t3. t1 ==> t2 ==> t3 = t1 /\ t2 ==> t3]])
  : ExceptT String IO thm).run
#eval AND_IMP_INTRO

#eval phrase 25
def AND_INTRO_THM : thm := keep "AND_INTRO_THM" fun _ =>
  (TAUT [[!t1 t2. t1 ==> t2 ==> t1 /\ t2]] : thm)
#eval AND_INTRO_THM

#eval phrase 26
def BOOL_EQ_DISTINCT : thm := keep "BOOL_EQ_DISTINCT" fun _ =>
  (TAUT [[~(T <=> F) /\ ~(F <=> T)]] : thm)
#eval BOOL_EQ_DISTINCT

#eval phrase 27
def EQ_EXPAND : thm := keep "EQ_EXPAND" fun _ =>
  (TAUT [[!t1 t2. (t1 <=> t2) <=> t1 /\ t2 \/ ~t1 /\ ~t2]] : thm)
#eval EQ_EXPAND

#eval phrase 28
def EQ_IMP_THM : thm := keep "EQ_IMP_THM" fun _ =>
  (TAUT [[!t1 t2. (t1 <=> t2) <=> (t1 ==> t2) /\ (t2 ==> t1)]] : thm)
#eval EQ_IMP_THM

#eval phrase 29
def FALSITY : thm := keep "FALSITY" fun _ => (TAUT [[!t. F ==> t]] : thm)
#eval FALSITY

#eval phrase 30
def F_IMP : thm := keep "F_IMP" fun _ => (TAUT [[!t. ~t ==> t ==> F]] : thm)
#eval F_IMP

#eval phrase 31
def IMP_DISJ_THM : thm := keep "IMP_DISJ_THM" fun _ =>
  (TAUT [[!t1 t2. t1 ==> t2 <=> ~t1 \/ t2]] : thm)
#eval IMP_DISJ_THM

#eval phrase 32
def IMP_F : thm := keep "IMP_F" fun _ => (TAUT [[!t. (t ==> F) ==> ~t]] : thm)
#eval IMP_F

#eval phrase 33
def IMP_F_EQ_F : thm := keep "IMP_F_EQ_F" fun _ =>
  (TAUT [[!t. t ==> F <=> (t <=> F)]] : thm)
#eval IMP_F_EQ_F

#eval phrase 34
def LEFT_AND_OVER_OR : thm := keep "LEFT_AND_OVER_OR" fun _ =>
  (TAUT [[!t1 t2 t3. t1 /\ (t2 \/ t3) <=> t1 /\ t2 \/ t1 /\ t3]] : thm)
#eval LEFT_AND_OVER_OR

#eval phrase 35
def LEFT_OR_OVER_AND : thm := keep "LEFT_OR_OVER_AND" fun _ =>
  (TAUT [[!t1 t2 t3. t1 \/ t2 /\ t3 <=> (t1 \/ t2) /\ (t1 \/ t3)]] : thm)
#eval LEFT_OR_OVER_AND

#eval phrase 36
def NOT_AND : thm := keep "NOT_AND" fun _ => (TAUT [[~(t /\ ~t)]] : thm)
#eval NOT_AND

#eval phrase 37
def NOT_F : thm := keep "NOT_F" fun _ => (TAUT [[!t. ~t ==> (t <=> F)]] : thm)
#eval NOT_F

#eval phrase 38
def OR_ELIM_THM : thm := keep "OR_ELIM_THM" fun _ =>
  (TAUT [[!t t1 t2. t1 \/ t2 ==> (t1 ==> t) ==> (t2 ==> t) ==> t]] : thm)
#eval OR_ELIM_THM

#eval phrase 39
def OR_IMP_THM : thm := keep "OR_IMP_THM" fun _ =>
  (TAUT [[!t1 t2. (t1 <=> t2 \/ t1) <=> t2 ==> t1]] : thm)
#eval OR_IMP_THM

#eval phrase 40
def OR_INTRO_THM1 : thm := keep "OR_INTRO_THM1" fun _ =>
  (TAUT [[!t1 t2. t1 ==> t1 \/ t2]] : thm)
#eval OR_INTRO_THM1

#eval phrase 41
def OR_INTRO_THM2 : thm := keep "OR_INTRO_THM2" fun _ =>
  (TAUT [[!t1 t2. t2 ==> t1 \/ t2]] : thm)
#eval OR_INTRO_THM2

#eval phrase 42
def RIGHT_AND_OVER_OR : thm := keep "RIGHT_AND_OVER_OR" fun _ =>
  (TAUT [[!t1 t2 t3. (t2 \/ t3) /\ t1 <=> t2 /\ t1 \/ t3 /\ t1]] : thm)
#eval RIGHT_AND_OVER_OR

#eval phrase 43
def RIGHT_OR_OVER_AND : thm := keep "RIGHT_OR_OVER_AND" fun _ =>
  (TAUT [[!t1 t2 t3. t2 /\ t3 \/ t1 <=> (t2 \/ t1) /\ (t3 \/ t1)]] : thm)
#eval RIGHT_OR_OVER_AND

/- ------------------------------------------------------------------------- -/
/- This is an overwrite -- is there any point in what I have?                -/
/- ------------------------------------------------------------------------- -/

#eval phrase 44
def is_type (s : String) : IO Bool := do
  match ← get_type_arity s with | .ok _ => pure true | .error _ => pure false
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- I suppose this is also useful.                                            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 45
def is_constant (s : String) : IO Bool := do
  match ← get_const_type s with | .ok _ => pure true | .error _ => pure false
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- Misc.                                                                     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 46
def null {α : Type} (l : List α) : Bool := l.isEmpty
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- Syntax.                                                                   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 47
def type_tyvars (ty : hol_type) : List hol_type :=
  type_vars_in_term (mk_var "x" ty)
#eval IO.println "<fun>"

#eval phrase 48
partial def find_match (u : term) (t : term) :
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

#eval phrase 49
partial def mk_primed_var : String × hol_type → IO (Except String term)
  | (name, ty) => do
    match ← get_const_type name with
    | .ok _ => mk_primed_var (name ++ "'", ty)
    | .error _ => pure (.ok (mk_var name ty))
#eval IO.println "<fun>"

#eval phrase 50
partial def subst_occs (ilist : List (List Int)) (slist : List (term × term)) (tm : term) :
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

#eval phrase 51
def INST_TY_TERM :
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

#eval phrase 52
def RIGHT_CONV_RULE (conv : HolCore.Equal.ioconv) (th : thm) : IO (Except String thm) := (do
  TRANS th (← ExceptT.mk (conv (← liftExcept (HolCore.Equal.rhs (concl th)))))
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- Derived rules.                                                            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 53
def NOT_EQ_SYM (th : thm) : IO (Except String thm) := (do
  -- aty
  let pth ← GENL [([[a:A]]), ([[b:A]])]
    (← HolLight.GEN_REWRITE_RULE HolCore.Lib.I [(← HolLight.GSYM CONTRAPOS_THM)]
         (← DISCH_ALL (← HolLight.SYM (← ASSUME [[a:A = b]]))))
  tryWith (do
    let (l, r) ← liftExcept (dest_eq (← liftExcept (dest_neg (concl th))))
    MP (← SPECL [r, l] (← HolLight.INST_TYPE [(type_of l, aty)] pth)) th)
    (throw "NOT_EQ_SYM")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 54
def NOT_MP (thi : thm) (th : thm) : IO (Except String thm) := (do
  tryWith (MP thi th)
    (tryWith (do
      let t ← liftExcept (dest_neg (concl thi))
      MP (← MP (← SPEC t F_IMP) thi) th)
      (throw "NOT_MP"))
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 55
def FORALL_EQ (x : term) (th : thm) : IO (Except String thm) := (do
  let c ← ExceptT.mk (mk_const "!" [(type_of x, mk_vartype "A")])
  tryWith (HolLight.AP_TERM c (← ABS x th)) (throw "FORALL_EQ")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 56
def EXISTS_EQ (x : term) (th : thm) : IO (Except String thm) := (do
  let c ← ExceptT.mk (mk_const "?" [(type_of x, mk_vartype "A")])
  tryWith (HolLight.AP_TERM c (← ABS x th)) (throw "EXISTS_EQ")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 57
def SELECT_EQ (x : term) (th : thm) : IO (Except String thm) := (do
  let c ← ExceptT.mk (mk_const "@" [(type_of x, mk_vartype "A")])
  tryWith (HolLight.AP_TERM c (← ABS x th)) (throw "SELECT_EQ")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 58
def RIGHT_BETA (th : thm) : IO (Except String thm) := (do
  tryWith (TRANS th (← liftExcept (HolCore.Equal.BETA_CONV (← liftExcept (HolCore.Equal.rhs (concl th))))))
    (throw "RIGHT_BETA")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 59
partial def LIST_BETA_CONV (tm : term) : IO (Except String thm) := (do
  tryWith (do
    let (rat, rnd) ← liftExcept (dest_comb tm)
    RIGHT_BETA (← HolLight.AP_THM (← ExceptT.mk (LIST_BETA_CONV rat)) rnd))
    (pure (REFL tm))
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 60
def RIGHT_LIST_BETA (th : thm) : IO (Except String thm) := (do
  TRANS th (← ExceptT.mk (LIST_BETA_CONV (← liftExcept (do pure (← dest_eq (concl th)).2))))
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 61
def LIST_CONJ (l : List thm) : IO (Except String thm) := (do
  match l with
  | [] => throw "end_itlist"
  | h :: t => t.foldr (fun x acc => do CONJ x (← acc)) (pure h)
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 62
partial def CONJ_LIST (n : Int) (th : thm) : IO (Except String (List thm)) := (do
  tryWith (do
    if n == 1 then pure [th]
    else pure ((← CONJUNCT1 th) :: (← ExceptT.mk (CONJ_LIST (n - 1) (← CONJUNCT2 th)))))
    (throw "CONJ_LIST")
  : ExceptT String IO (List thm)).run
#eval IO.println "<fun>"

#eval phrase 63
partial def BODY_CONJUNCTS (th : thm) : IO (Except String (List thm)) := (do
  if is_forall (concl th) then
    ExceptT.mk (BODY_CONJUNCTS (← SPEC_ALL th))
  else if is_conj (concl th) then do
    pure ((← ExceptT.mk (BODY_CONJUNCTS (← CONJUNCT1 th))) ++
          (← ExceptT.mk (BODY_CONJUNCTS (← CONJUNCT2 th))))
  else pure [th]
  : ExceptT String IO (List thm)).run
#eval IO.println "<fun>"

#eval phrase 64
partial def IMP_CANON (th : thm) : IO (Except String (List thm)) := (do
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

#eval phrase 65
def LIST_MP (l : List thm) (th : thm) : IO (Except String thm) := (do
  l.foldlM (fun y x => MP y x) th
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 66
def DISJ_IMP (th : thm) : IO (Except String thm) := (do
  let pth ← TAUT_io [[!t1 t2. t1 \/ t2 ==> ~t1 ==> t2]]
  tryWith (do
    let (a, b) ← liftExcept (dest_disj (concl th))
    MP (← SPECL [a, b] pth) th)
    (throw "DISJ_IMP")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 67
def IMP_ELIM (th : thm) : IO (Except String thm) := (do
  let pth ← TAUT_io [[!t1 t2. (t1 ==> t2) ==> ~t1 \/ t2]]
  tryWith (do
    let (a, b) ← liftExcept (dest_imp (concl th))
    MP (← SPECL [a, b] pth) th)
    (throw "IMP_ELIM")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 68
def DISJ_CASES_UNION (dth ath bth : thm) : IO (Except String thm) := (do
  DISJ_CASES dth (← DISJ1 ath (concl bth)) (← DISJ2 (concl ath) bth)
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 69
def MK_ABS (qth : thm) : IO (Except String thm) := (do
  tryWith (do
    let ov ← liftExcept (do bndvar (← rand (concl qth)))
    let (bv, rth) ← SPEC_VAR qth
    let sth ← ABS bv rth
    let cnv := ALPHA_CONV_io ov
    HolLight.CONV_RULE (BINOP_CONV_io cnv) sth)
    (throw "MK_ABS")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 70
def HALF_MK_ABS (th : thm) : IO (Except String thm) := (do
  tryWith (do
    let th1 ← ExceptT.mk (MK_ABS th)
    HolLight.CONV_RULE (HolLight.LAND_CONV ETA_CONV_io) th1)
    (throw "HALF_MK_ABS")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 71
def MK_EXISTS (qth : thm) : IO (Except String thm) := (do
  tryWith (do
    let ov ← liftExcept (do bndvar (← rand (concl qth)))
    let (bv, rth) ← SPEC_VAR qth
    let sth ← ExceptT.mk (EXISTS_EQ bv rth)
    let cnv := GEN_ALPHA_CONV_io ov
    HolLight.CONV_RULE (BINOP_CONV_io cnv) sth)
    (throw "MK_EXISTS")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 72
def LIST_MK_EXISTS (l : List term) (th : thm) : IO (Except String thm) := (do
  l.foldr (fun x acc => do ExceptT.mk (MK_EXISTS (← GEN x (← acc)))) (pure th)
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 73
def IMP_CONJ (th1 th2 : thm) : IO (Except String thm) := (do
  let (A1, _C1) ← liftExcept (dest_imp (concl th1))
  let (A2, _C2) ← liftExcept (dest_imp (concl th2))
  let conj ← liftExcept (HolCore.Bool.mk_conj A1 A2)
  let (a1, a2) ← CONJ_PAIR (← ASSUME conj)
  DISCH conj (← CONJ (← MP th1 a1) (← MP th2 a2))
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 74
def EXISTS_IMP (x : term) (th : thm) : IO (Except String thm) := (do
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

#eval phrase 75
partial def CONJUNCTS_CONV : term × term → IO (Except String thm)
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

#eval phrase 76
def CONJ_SET_CONV (l1 l2 : List term) : IO (Except String thm) := (do
  tryWith (do
    ExceptT.mk (CONJUNCTS_CONV (← liftExcept (HolCore.Bool.list_mk_conj l1), ← liftExcept (HolCore.Bool.list_mk_conj l2))))
    (throw "CONJ_SET_CONV")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 77
def FRONT_CONJ_CONV (tml : List term) (t : term) : IO (Except String thm) := (do
  let rec remove (x : term) (l : List term) : List term :=
    match l with
    | [] => []
    | h :: tl => if h == x then tl else h :: remove x tl
  tryWith (ExceptT.mk (CONJ_SET_CONV tml (t :: remove t tml)))
    (throw "FRONT_CONJ_CONV")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 78
def CONJ_DISCH (t : term) (th : thm) : IO (Except String thm) := (do
  let pth ← TAUT_io [[!t t1 t2. (t ==> (t1 <=> t2)) ==> (t /\ t1 <=> t /\ t2)]]
  tryWith (do
    let (t1, t2) ← liftExcept (dest_eq (concl th))
    MP (← SPECL [t, t1, t2] pth) (← DISCH t th))
    (throw "CONJ_DISCH")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 79
def CONJ_DISCHL (l : List term) (th : thm) : IO (Except String thm) := (do
  match l with
  | [] => pure th
  | h :: tl => CONJ_DISCH h (← ExceptT.mk (CONJ_DISCHL tl th))
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 80
partial def GSPEC (th : thm) : IO (Except String thm) := (do
  let (_wl, w) := dest_thm th
  if is_forall w then do
    let v ← (genvar (type_of (← liftExcept (do pure (← dest_forall w).1)))
      : ExceptT String IO term)
    ExceptT.mk (GSPEC (← SPEC v th))
  else pure th
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 81
def ANTE_CONJ_CONV (tm : term) : IO (Except String thm) := (do
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

#eval phrase 82
def bool_EQ_CONV (tm : term) : IO (Except String thm) := (do
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

#eval phrase 83
def COND_CONV (tm : term) : IO (Except String thm) := (do
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

#eval phrase 84
def SUBST_MATCH (eqth : thm) (th : thm) : IO (Except String thm) := (do
  let (tm_inst, ty_inst) ← ExceptT.mk (find_match (← liftExcept (HolCore.Equal.lhs (concl eqth))) (concl th))
  HolLight.SUBS [(← INST tm_inst (← HolLight.INST_TYPE ty_inst eqth))] th
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 85
def SUBST (thl : List (thm × term)) (pat : term) (th : thm) : IO (Except String thm) := (do
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

/- let GSUBS = ...                                                           -/
/- let SUBS_OCCS = ...                                                       -/
/- A poor thing but mine own. The old ones use mk_thm and the commented
   out functions are bogus. -/

#eval phrase 86
def SUBST_CONV (thvars : List (thm × term)) (template tm : term) :
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

#eval phrase 87
def FILTER_PURE_ASM_REWRITE_RULE (f : term → Bool) (thl : List thm) (th : thm) :
    IO (Except String thm) := (do
  PURE_REWRITE_RULE ((← (HolCore.Lib.filter f (hyp th)).mapM (fun t => (liftExcept (ASSUME t) : ExceptT String IO thm))) ++ thl) th
  : ExceptT String IO thm).run
def FILTER_ASM_REWRITE_RULE (f : term → Bool) (thl : List thm) (th : thm) :
    IO (Except String thm) := (do
  REWRITE_RULE ((← (HolCore.Lib.filter f (hyp th)).mapM (fun t => (liftExcept (ASSUME t) : ExceptT String IO thm))) ++ thl) th
  : ExceptT String IO thm).run
def FILTER_PURE_ONCE_ASM_REWRITE_RULE (f : term → Bool) (thl : List thm) (th : thm) :
    IO (Except String thm) := (do
  PURE_ONCE_REWRITE_RULE ((← (HolCore.Lib.filter f (hyp th)).mapM (fun t => (liftExcept (ASSUME t) : ExceptT String IO thm))) ++ thl) th
  : ExceptT String IO thm).run
def FILTER_ONCE_ASM_REWRITE_RULE (f : term → Bool) (thl : List thm) (th : thm) :
    IO (Except String thm) := (do
  ONCE_REWRITE_RULE ((← (HolCore.Lib.filter f (hyp th)).mapM (fun t => (liftExcept (ASSUME t) : ExceptT String IO thm))) ++ thl) th
  : ExceptT String IO thm).run
#eval do IO.println "<fun>"; IO.println "<fun>"; IO.println "<fun>"; IO.println "<fun>"

#eval phrase 88
def FILTER_PURE_ASM_REWRITE_TAC (f : term → Bool) (thl : List thm) : tactic :=
  fun g => (PURE_REWRITE_TAC (HolCore.Lib.filter (fun th => f (concl th)) (g.1.map (fun p => p.2)) ++ thl)) g
def FILTER_ASM_REWRITE_TAC (f : term → Bool) (thl : List thm) : tactic :=
  fun g => (REWRITE_TAC (HolCore.Lib.filter (fun th => f (concl th)) (g.1.map (fun p => p.2)) ++ thl)) g
def FILTER_PURE_ONCE_ASM_REWRITE_TAC (f : term → Bool) (thl : List thm) : tactic :=
  fun g => (PURE_ONCE_REWRITE_TAC (HolCore.Lib.filter (fun th => f (concl th)) (g.1.map (fun p => p.2)) ++ thl)) g
def FILTER_ONCE_ASM_REWRITE_TAC (f : term → Bool) (thl : List thm) : tactic :=
  fun g => (ONCE_REWRITE_TAC (HolCore.Lib.filter (fun th => f (concl th)) (g.1.map (fun p => p.2)) ++ thl)) g
#eval do IO.println "<fun>"; IO.println "<fun>"; IO.println "<fun>"; IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- Tacticals.                                                                -/
/- ------------------------------------------------------------------------- -/

#eval phrase 89
def X_CASES_THENL (varsl : List (List term)) (ttacl : List thm_tactic) : thm_tactic :=
  fun th =>
    match (List.zip varsl ttacl).map (fun (vars, ttac) =>
      HolCore.Tactics.EVERY_TCL (vars.map (fun v => HolLight.X_CHOOSE_THEN v)) ttac) with
    | [] => fun _g => (pure (.error "end_itlist") : IO (Except String HolCore.Tactics.goalstate))
    | h :: t => (t.foldr (fun x acc => DISJ_CASES_THEN2 x acc) h) th
#eval IO.println "<fun>"

#eval phrase 90
def X_CASES_THEN (varsl : List (List term)) (ttac : thm_tactic) : thm_tactic :=
  fun th =>
    match varsl.map (fun vars =>
      HolCore.Tactics.EVERY_TCL (vars.map (fun v => HolLight.X_CHOOSE_THEN v)) ttac) with
    | [] => fun _g => (pure (.error "end_itlist") : IO (Except String HolCore.Tactics.goalstate))
    | h :: t => (t.foldr (fun x acc => DISJ_CASES_THEN2 x acc) h) th
#eval IO.println "<fun>"

#eval phrase 91
def CASES_THENL (ttacl : List thm_tactic) : thm_tactic :=
  fun th =>
    match ttacl.map (fun ttac => HolLight.REPEAT_TCL CHOOSE_THEN ttac) with
    | [] => fun _g => (pure (.error "end_itlist") : IO (Except String HolCore.Tactics.goalstate))
    | h :: t => (t.foldr (fun x acc => DISJ_CASES_THEN2 x acc) h) th
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- Tactics.                                                                  -/
/- ------------------------------------------------------------------------- -/

#eval phrase 92
def DISCARD_TAC : thm_tactic :=
  fun th g => do
    let truth : term := [[T]]
    if (truth :: g.1.map (fun p => concl p.2)).any (fun t => aconv (concl th) t)
    then ALL_TAC g
    else pure (Except.error "DISCARD_TAC")
#eval IO.println "<fun>"

#eval phrase 93
def CHECK_ASSUME_TAC : thm_tactic :=
  fun gth => FIRST [CONTR_TAC gth, ACCEPT_TAC gth, DISCARD_TAC gth, ASSUME_TAC gth]
#eval IO.println "<fun>"

#eval phrase 94
def FILTER_GEN_TAC (tm : term) : tactic :=
  fun (asl, w) =>
    if is_forall w && !(tm == (match dest_forall w with | .ok p => p.1 | _ => tm))
    then GEN_TAC (asl, w)
    else (pure (.error "FILTER_GEN_TAC") : IO (Except String HolCore.Tactics.goalstate))
#eval IO.println "<fun>"

#eval phrase 95
def FILTER_DISCH_THEN (ttac : thm_tactic) (tm : term) : tactic :=
  fun (asl, w) =>
    if is_neg_imp w && !(free_in tm (match runIO (dest_neg_imp w) with
        | .ok (.ok p) => p.1 | _ => w))
    then DISCH_THEN ttac (asl, w)
    else (pure (.error "FILTER_DISCH_THEN") : IO (Except String HolCore.Tactics.goalstate))
#eval IO.println "<fun>"

#eval phrase 96
def FILTER_STRIP_THEN (ttac : thm_tactic) (tm : term) : tactic :=
  FIRST [FILTER_GEN_TAC tm, FILTER_DISCH_THEN ttac tm, CONJ_TAC]
#eval IO.println "<fun>"

#eval phrase 97
def FILTER_DISCH_TAC (tm : term) : tactic := FILTER_DISCH_THEN STRIP_ASSUME_TAC tm
#eval IO.println "<fun>"

#eval phrase 98
def FILTER_STRIP_TAC (tm : term) : tactic := FILTER_STRIP_THEN STRIP_ASSUME_TAC tm
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- Conversions for quantifier movement using proforma theorems.              -/
/- ------------------------------------------------------------------------- -/
/- let ....... -/
/- ------------------------------------------------------------------------- -/
/- Resolution stuff.                                                         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 99
partial def RES_CANON (th : thm) : IO (Except String (List thm)) := (do
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

#eval phrase 100
-- let IMP_RES_THEN,RES_THEN = ... ;;  (two <fun>s)
def IMP_RES_THEN : thm_tactic → thm → tactic := Session.IMP_RES_THEN
def RES_THEN (ttac : thm_tactic) : tactic :=
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

#eval phrase 101
def IMP_RES_TAC (th : thm) : tactic :=
  fun g => do
    match ← IMP_RES_THEN (HolCore.Tactics.REPEAT_GTCL IMP_RES_THEN STRIP_ASSUME_TAC) th g with
    | .ok r => pure (Except.ok r)
    | .error _ => ALL_TAC g
#eval IO.println "<fun>"

#eval phrase 102
def RES_TAC : tactic :=
  fun g => do
    match ← RES_THEN (HolCore.Tactics.REPEAT_GTCL IMP_RES_THEN STRIP_ASSUME_TAC) g with
    | .ok r => pure (Except.ok r)
    | .error _ => ALL_TAC g
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- Stuff for handling type definitions.                                      -/
/- ------------------------------------------------------------------------- -/

#eval phrase 103
def prove_rep_fn_one_one (th : thm) : IO (Except String thm) := (do
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

#eval phrase 104
def prove_rep_fn_onto (th : thm) : IO (Except String thm) := (do
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

#eval phrase 105
def prove_abs_fn_onto (th : thm) : IO (Except String thm) := (do
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

#eval phrase 106
def prove_abs_fn_one_one (th : thm) : IO (Except String thm) := (do
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
/- AC rewriting needs to be wrapped up as a special conversion.              -/
/- ------------------------------------------------------------------------- -/

#eval phrase 107
def AC_CONV : thm × thm → term → IO (Except String thm) := fun (assoc, sym) tm => (do
  let th1 ← HolLight.SPEC_ALL assoc
  let th2 ← HolLight.SPEC_ALL sym
  let th3 ← HolLight.GEN_REWRITE_RULE (HolLight.RAND_CONV o HolLight.LAND_CONV) [th2] th1
  let th4 ← HolLight.SYM th1
  let th5 ← HolLight.GEN_REWRITE_RULE HolLight.RAND_CONV [th4] th3
  HolLight.EQT_INTRO (← HolLight.AC (← HolLight.end_itlist HolLight.CONJ [th2, th4, th5]) tm)
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 108
def AC_RULE (ths : thm × thm) (tm : term) : IO (Except String thm) := (do
  EQT_ELIM (← ExceptT.mk (AC_CONV ths tm))
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- The order of picking conditionals is different!                           -/
/- ------------------------------------------------------------------------- -/

#eval phrase 109
def COND_CASES_TAC : tactic := Session.COND_CASES_TAC
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- MATCH_MP_TAC allows universals on the right of implication.               -/
/- Here's a crude hack to allow it.                                          -/
/- ------------------------------------------------------------------------- -/

#eval phrase 110
def MATCH_MP_TAC (th : thm) : tactic :=
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

#eval phrase 111
def ZERO_LESS_EQ : thm := keep "ZERO_LESS_EQ" fun _ => LE_0
#eval ZERO_LESS_EQ

#eval phrase 112
def LESS_EQ_MONO : thm := keep "LESS_EQ_MONO" fun _ => LE_SUC
#eval LESS_EQ_MONO

#eval phrase 113
def NOT_LESS : thm := keep "NOT_LESS" fun _ => NOT_LT
#eval NOT_LESS

#eval phrase 114
def LESS_0 : thm := keep "LESS_0" fun _ => LT_0
#eval LESS_0

#eval phrase 115
def LESS_EQ_REFL : thm := keep "LESS_EQ_REFL" fun _ => LE_REFL
#eval LESS_EQ_REFL

#eval phrase 116
def LESS_EQUAL_ANTISYM : thm := keep "LESS_EQUAL_ANTISYM" fun _ =>
  ((do GEN_ALL (← EQ_IMP_RULE (← SPEC_ALL LE_ANTISYM)).1 : ExceptT String IO thm).run : thm)
#eval LESS_EQUAL_ANTISYM

#eval phrase 117
def NOT_LESS_0 : thm := keep "NOT_LESS_0" fun _ =>
  ((do GEN_ALL (← EQF_ELIM (← SPEC_ALL (← CONJUNCT1 LT))) : ExceptT String IO thm).run : thm)
#eval NOT_LESS_0

#eval phrase 118
def LESS_TRANS : thm := keep "LESS_TRANS" fun _ => LT_TRANS
#eval LESS_TRANS

#eval phrase 119
def LESS_LEMMA1 : thm := keep "LESS_LEMMA1" fun _ =>
  ((do GEN_ALL (← EQ_IMP_RULE (← SPEC_ALL (← CONJUNCT2 LT))).1 : ExceptT String IO thm).run : thm)
#eval LESS_LEMMA1

#eval phrase 120
def LESS_SUC_REFL : thm := keep "LESS_SUC_REFL" fun _ =>
  ((do prove ([[!n. n < SUC n]]) (REWRITE_TAC [LT]) : ExceptT String IO thm).run : thm)
#eval LESS_SUC_REFL

#eval phrase 121
def FACT_LESS : thm := keep "FACT_LESS" fun _ => FACT_LT
#eval FACT_LESS

#eval phrase 122
def LESS_EQ_SUC_REFL : thm := keep "LESS_EQ_SUC_REFL" fun _ =>
  ((do prove ([[!n. n <= SUC n]]) (REWRITE_TAC [LE, LE_REFL]) : ExceptT String IO thm).run : thm)
#eval LESS_EQ_SUC_REFL

#eval phrase 123
def LESS_EQ_ADD : thm := keep "LESS_EQ_ADD" fun _ => LE_ADD
#eval LESS_EQ_ADD

#eval phrase 124
def GREATER_EQ : thm := keep "GREATER_EQ" fun _ => GE
#eval GREATER_EQ

#eval phrase 125
def LESS_EQUAL_ADD : thm := keep "LESS_EQUAL_ADD" fun _ =>
  ((do GEN_ALL (← EQ_IMP_RULE (← SPEC_ALL LE_EXISTS)).1 : ExceptT String IO thm).run : thm)
#eval LESS_EQUAL_ADD

#eval phrase 126
def LESS_EQ_IMP_LESS_SUC : thm := keep "LESS_EQ_IMP_LESS_SUC" fun _ =>
  ((do GEN_ALL (← EQ_IMP_RULE (← SPEC_ALL LT_SUC_LE)).2 : ExceptT String IO thm).run : thm)
#eval LESS_EQ_IMP_LESS_SUC

#eval phrase 127
def LESS_IMP_LESS_OR_EQ : thm := keep "LESS_IMP_LESS_OR_EQ" fun _ => LT_IMP_LE
#eval LESS_IMP_LESS_OR_EQ

#eval phrase 128
def LESS_MONO_ADD : thm := keep "LESS_MONO_ADD" fun _ =>
  ((do GEN_ALL (← EQ_IMP_RULE (← SPEC_ALL LT_ADD_RCANCEL)).2 : ExceptT String IO thm).run : thm)
#eval LESS_MONO_ADD

#eval phrase 129
def LESS_SUC : thm := keep "LESS_SUC" fun _ =>
  ((do prove ([[!m n. m < n ==> m < (SUC n)]]) (MESON_TAC [LT]) : ExceptT String IO thm).run : thm)
#eval LESS_SUC

#eval phrase 130
def LESS_CASES : thm := keep "LESS_CASES" fun _ => LTE_CASES
#eval LESS_CASES

#eval phrase 131
def LESS_EQ : thm := keep "LESS_EQ" fun _ =>
  ((do HolLight.GSYM LE_SUC_LT : ExceptT String IO thm).run : thm)
#eval LESS_EQ

#eval phrase 132
def LESS_OR_EQ : thm := keep "LESS_OR_EQ" fun _ => LE_LT
#eval LESS_OR_EQ

#eval phrase 133
def LESS_ADD_1 : thm := keep "LESS_ADD_1" fun _ =>
  ((do GEN_ALL (← EQ_IMP_RULE (← SPEC_ALL (← REWRITE_RULE [ADD1] LT_EXISTS))).1
    : ExceptT String IO thm).run : thm)
#eval LESS_ADD_1

#eval phrase 134
def SUC_SUB1 : thm := keep "SUC_SUB1" fun _ => (do
  let h1 ← nc (← ExceptT.mk [[1]])
  prove ([[!m. SUC m - 1 = m]])
   (REWRITE_TAC [h1, SUB_SUC, SUB_0])
  : ExceptT String IO thm).run
#eval SUC_SUB1

#eval phrase 135
def LESS_MONO_EQ : thm := keep "LESS_MONO_EQ" fun _ => LT_SUC
#eval LESS_MONO_EQ

#eval phrase 136
def LESS_ADD_SUC : thm := keep "LESS_ADD_SUC" fun _ => (do
  prove ([[!m n. m < m + SUC n]])
   (REWRITE_TAC [ADD_CLAUSES, LT_SUC_LE, LE_ADD])
  : ExceptT String IO thm).run
#eval LESS_ADD_SUC

#eval phrase 137
def LESS_REFL : thm := keep "LESS_REFL" fun _ => LT_REFL
#eval LESS_REFL

#eval phrase 138
def INV_SUC_EQ : thm := keep "INV_SUC_EQ" fun _ => SUC_INJ
#eval INV_SUC_EQ

#eval phrase 139
def LESS_EQ_CASES : thm := keep "LESS_EQ_CASES" fun _ => LE_CASES
#eval LESS_EQ_CASES

#eval phrase 140
def LESS_EQ_TRANS : thm := keep "LESS_EQ_TRANS" fun _ => LE_TRANS
#eval LESS_EQ_TRANS

#eval phrase 141
def LESS_THM : thm := keep "LESS_THM" fun _ =>
  ((do CONJUNCT2 LT : ExceptT String IO thm).run : thm)
#eval LESS_THM

#eval phrase 142
def GREATER : thm := keep "GREATER" fun _ => GT
#eval GREATER

#eval phrase 143
def LESS_EQ_0 : thm := keep "LESS_EQ_0" fun _ =>
  ((do CONJUNCT1 LE : ExceptT String IO thm).run : thm)
#eval LESS_EQ_0

#eval phrase 144
def OR_LESS : thm := keep "OR_LESS" fun _ =>
  ((do GEN_ALL (← EQ_IMP_RULE (← SPEC_ALL LE_SUC_LT)).1 : ExceptT String IO thm).run : thm)
#eval OR_LESS

#eval phrase 145
def SUB_EQUAL_0 : thm := keep "SUB_EQUAL_0" fun _ => SUB_REFL
#eval SUB_EQUAL_0

#eval phrase 146
def SUB_MONO_EQ : thm := keep "SUB_MONO_EQ" fun _ => SUB_SUC
#eval SUB_MONO_EQ

#eval phrase 147
def NOT_SUC_LESS_EQ : thm := keep "NOT_SUC_LESS_EQ" fun _ => (do
  prove ([[!n m. ~(SUC n <= m) <=> m <= n]])
   (REWRITE_TAC [NOT_LE, LT] THEN
                               MESON_TAC [LE_LT])
  : ExceptT String IO thm).run
#eval NOT_SUC_LESS_EQ

#eval phrase 148
def SUC_NOT : thm := keep "SUC_NOT" fun _ =>
  ((do HolLight.GSYM NOT_SUC : ExceptT String IO thm).run : thm)
#eval SUC_NOT

#eval phrase 149
def LESS_LESS_CASES : thm := keep "LESS_LESS_CASES" fun _ => (do
  prove ([[!m n:num. (m = n) \/ m < n \/ n < m]])
   (MESON_TAC [LT_CASES])
  : ExceptT String IO thm).run
#eval LESS_LESS_CASES

#eval phrase 150
def NOT_LESS_EQUAL : thm := keep "NOT_LESS_EQUAL" fun _ => NOT_LE
#eval NOT_LESS_EQUAL

#eval phrase 151
def LESS_EQ_EXISTS : thm := keep "LESS_EQ_EXISTS" fun _ => LE_EXISTS
#eval LESS_EQ_EXISTS

#eval phrase 152
def LESS_MONO_ADD_EQ : thm := keep "LESS_MONO_ADD_EQ" fun _ => LT_ADD_RCANCEL
#eval LESS_MONO_ADD_EQ

#eval phrase 153
def LESS_LESS_EQ_TRANS : thm := keep "LESS_LESS_EQ_TRANS" fun _ => LTE_TRANS
#eval LESS_LESS_EQ_TRANS

#eval phrase 154
def SUB_SUB : thm := keep "SUB_SUB" fun _ =>
  (ARITH_RULE [[!b c. c <= b ==> (!a:num. a - (b - c) = (a + c) - b)]] : thm)
#eval SUB_SUB

#eval phrase 155
def LESS_CASES_IMP : thm := keep "LESS_CASES_IMP" fun _ =>
  (ARITH_RULE [[!m n:num. ~(m < n) /\ ~(m = n) ==> n < m]] : thm)
#eval LESS_CASES_IMP

#eval phrase 156
def SUB_LESS_EQ : thm := keep "SUB_LESS_EQ" fun _ =>
  (ARITH_RULE [[!n m:num. (n - m) <= n]] : thm)
#eval SUB_LESS_EQ

#eval phrase 157
def SUB_EQ_EQ_0 : thm := keep "SUB_EQ_EQ_0" fun _ => (do
  ar (← ExceptT.mk [[!m n:num. (m - n = m) <=> (m = 0) \/ (n = 0)]])
  : ExceptT String IO thm).run
#eval SUB_EQ_EQ_0

#eval phrase 158
def SUB_LEFT_LESS_EQ : thm := keep "SUB_LEFT_LESS_EQ" fun _ =>
  (ARITH_RULE [[!m n p:num. m <= (n - p) <=> (m + p) <= n \/ m <= 0]] : thm)
#eval SUB_LEFT_LESS_EQ

#eval phrase 159
def SUB_LEFT_GREATER_EQ : thm := keep "SUB_LEFT_GREATER_EQ" fun _ =>
  (ARITH_RULE [[!m n p:num. m >= (n - p) <=> (m + p) >= n]] : thm)
#eval SUB_LEFT_GREATER_EQ

#eval phrase 160
def LESS_EQ_LESS_TRANS : thm := keep "LESS_EQ_LESS_TRANS" fun _ => LET_TRANS
#eval LESS_EQ_LESS_TRANS

#eval phrase 161
def LESS_0_CASES : thm := keep "LESS_0_CASES" fun _ =>
  (ARITH_RULE [[!m. (0 = m) \/ 0 < m]] : thm)
#eval LESS_0_CASES

#eval phrase 162
def LESS_OR : thm := keep "LESS_OR" fun _ =>
  (ARITH_RULE [[!m n. m < n ==> (SUC m) <= n]] : thm)
#eval LESS_OR

#eval phrase 163
def SUB : thm := keep "SUB" fun _ =>
  (ARITH_RULE [[(!m. 0 - m = 0) /\
    (!m n. (SUC m) - n = (if m < n then 0 else SUC(m - n)))]] : thm)
#eval SUB

#eval phrase 164
def LESS_MULT_MONO : thm := keep "LESS_MULT_MONO" fun _ =>
  ((do prove ([[!m i n. ((SUC n) * m) < ((SUC n) * i) <=> m < i]]) (REWRITE_TAC [LT_MULT_LCANCEL, NOT_SUC]) : ExceptT String IO thm).run : thm)
#eval LESS_MULT_MONO

#eval phrase 165
def LESS_MONO_MULT : thm := keep "LESS_MONO_MULT" fun _ =>
  ((do prove ([[!m n p. m <= n ==> (m * p) <= (n * p)]]) (SIMP_TAC [LE_MULT_RCANCEL]) : ExceptT String IO thm).run : thm)
#eval LESS_MONO_MULT

#eval phrase 166
def LESS_MULT2 : thm := keep "LESS_MULT2" fun _ =>
  ((do prove ([[!m n. 0 < m /\ 0 < n ==> 0 < (m * n)]]) (REWRITE_TAC [LT_MULT]) : ExceptT String IO thm).run : thm)
#eval LESS_MULT2

#eval phrase 167
def SUBSET_FINITE : thm := keep "SUBSET_FINITE" fun _ =>
  ((do prove ([[!s. FINITE s ==> (!t. t SUBSET s ==> FINITE t)]]) (MESON_TAC [FINITE_SUBSET]) : ExceptT String IO thm).run : thm)
#eval SUBSET_FINITE

#eval phrase 168
def LESS_EQ_SUC : thm := keep "LESS_EQ_SUC" fun _ =>
  ((do prove ([[!n. m <= SUC n <=> (m = SUC n) \/ m <= n]]) (REWRITE_TAC [LE]) : ExceptT String IO thm).run : thm)
#eval LESS_EQ_SUC

#eval phrase 169
def ANTE_RES_THEN (ttac : thm_tactic) (th : thm) : tactic :=
  FIRST_ASSUM (fun t => HolLight.tactic_of do pure (ttac (← HolLight.MATCH_MP t th)))
#eval IO.println "<fun>"

#eval phrase 170
-- (rebinds IMP_RES_THEN, defined in the hol88.ml part)
def IMP_RES_THEN_2 (ttac : thm_tactic) (th : thm) : tactic :=
  FIRST_ASSUM (fun t => HolLight.tactic_of do pure (ttac (← HolLight.MATCH_MP th t)))
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------ -/
/- Set theory lemmas.                                                       -/
/- ------------------------------------------------------------------------ -/

#eval phrase 171
def INFINITE_MEMBER : thm := keep "INFINITE_MEMBER" fun _ => (do
  prove ([[!s. INFINITE(s:A->bool) ==> ?x. x IN s]])
   (GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[~(s:A->bool = {})]]) MP_TAC THENL
     [UNDISCH_TAC ([[INFINITE (s:A->bool)]]) THEN
      CONV_TAC HolLight.CONTRAPOS_CONV THEN REWRITE_TAC [] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [INFINITE, FINITE_EMPTY],
      REWRITE_TAC [EXTENSION, NOT_IN_EMPTY] THEN
      PURE_ONCE_REWRITE_TAC [NOT_FORALL_THM] THEN
      REWRITE_TAC []])
  : ExceptT String IO thm).run
#eval INFINITE_MEMBER

#eval phrase 172
def INFINITE_CHOOSE : thm := keep "INFINITE_CHOOSE" fun _ => (do
  prove ([[!s:A->bool. INFINITE(s) ==> ((@) s) IN s]])
   (GEN_TAC THEN DISCH_THEN (MP_TAC o HolLight.MATCH_MP INFINITE_MEMBER) THEN
    DISCH_THEN (MP_TAC o HolLight.SELECT_RULE) THEN REWRITE_TAC [IN] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV (pureC Session.ETA_CONV)) THEN REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval INFINITE_CHOOSE

#eval phrase 173
def INFINITE_DELETE : thm := keep "INFINITE_DELETE" fun _ => (do
  prove ([[!(t:A->bool) x. INFINITE (t DELETE x) = INFINITE(t)]])
   (REWRITE_TAC [INFINITE, FINITE_DELETE])
  : ExceptT String IO thm).run
#eval INFINITE_DELETE

#eval phrase 174
def INFINITE_INSERT : thm := keep "INFINITE_INSERT" fun _ => (do
  prove ([[!(x:A) t. INFINITE(x INSERT t) = INFINITE(t)]])
   (REWRITE_TAC [INFINITE, FINITE_INSERT])
  : ExceptT String IO thm).run
#eval INFINITE_INSERT

#eval phrase 175
def SIZE_INSERT : thm := keep "SIZE_INSERT" fun _ => (do
  prove ([[!(x:A) t. ~(x IN t) /\ t HAS_SIZE n ==> (x INSERT t) HAS_SIZE (SUC n)]])
   (SIMP_TAC [HAS_SIZE, CARD_CLAUSES, FINITE_RULES])
  : ExceptT String IO thm).run
#eval SIZE_INSERT

#eval phrase 176
def SIZE_DELETE : thm := keep "SIZE_DELETE" fun _ => (do
  prove ([[!(x:A) t. x IN t /\ t HAS_SIZE (SUC n) ==> (t DELETE x) HAS_SIZE n]])
   (SIMP_TAC [HAS_SIZE_SUC])
  : ExceptT String IO thm).run
#eval SIZE_DELETE

#eval phrase 177
def SIZE_EXISTS : thm := keep "SIZE_EXISTS" fun _ => (do
  prove ([[!s N. s HAS_SIZE (SUC N) ==> ?x:A. x IN s]])
   (SIMP_TAC [HAS_SIZE_SUC, (← HolLight.GSYM MEMBER_NOT_EMPTY)])
  : ExceptT String IO thm).run
#eval SIZE_EXISTS

#eval phrase 178
def SUBSET_DELETE : thm := keep "SUBSET_DELETE" fun _ => (do
  prove ([[!s t (x:A). s SUBSET t ==> (s DELETE x) SUBSET t]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC ([[s:A->bool]]) THEN ASM_REWRITE_TAC [DELETE_SUBSET])
  : ExceptT String IO thm).run
#eval SUBSET_DELETE

#eval phrase 179
def INFINITE_FINITE_CHOICE : thm := keep "INFINITE_FINITE_CHOICE" fun _ => (do
  prove ([[!n (s:A->bool). INFINITE(s) ==> ?t. t SUBSET s /\ t HAS_SIZE n]])
   (INDUCT_TAC THEN GEN_TAC THEN DISCH_TAC THENL
     [EXISTS_TAC ([[{}:A->bool]]) THEN
      REWRITE_TAC [HAS_SIZE, EMPTY_SUBSET, HAS_SIZE_0],
      FIRST_ASSUM (UNDISCH_TAC o check HolCore.Basics.is_forall o concl) THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC ([[s DELETE ((@) s :A)]])) THEN
      ASM_REWRITE_TAC [INFINITE_DELETE] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[t:A->bool]]) STRIP_ASSUME_TAC) THEN
      EXISTS_TAC ([[((@) s :A) INSERT t]]) THEN CONJ_TAC THENL
       [REWRITE_TAC [INSERT_SUBSET] THEN CONJ_TAC THENL
         [MATCH_MP_TAC INFINITE_CHOOSE THEN ASM_REWRITE_TAC [],
          REWRITE_TAC [SUBSET] THEN
          RULE_ASSUM_TAC (HolLight.REWRITE_RULE [SUBSET]) THEN
          GEN_TAC THEN DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN
          REWRITE_TAC [IN_DELETE] THEN CONV_TAC (HolLight.EQT_INTRO o HolLight.TAUT)],
          MATCH_MP_TAC SIZE_INSERT THEN ASM_REWRITE_TAC [] THEN
          DISCH_TAC THEN UNDISCH_TAC ([[t SUBSET (s DELETE ((@) s:A))]]) THEN
          REWRITE_TAC [SUBSET, IN_DELETE] THEN
          DISCH_THEN (IMP_RES_THEN_2 MP_TAC) THEN REWRITE_TAC []]])
  : ExceptT String IO thm).run
#eval INFINITE_FINITE_CHOICE

#eval phrase 180
def IMAGE_WOP_LEMMA : thm := keep "IMAGE_WOP_LEMMA" fun _ => (do
  prove ([[!N (t:num->bool) (u:A->bool).
        u SUBSET (IMAGE f t) /\ u HAS_SIZE (SUC N) ==>
        ?n v. (u = (f n) INSERT v) /\
              !y. y IN v ==> ?m. (y = f m) /\ n < m]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPEC ([[\n:num. ?y:A. y IN u /\ (y = f n)]]) num_WOP) THEN BETA_TAC THEN
    DISCH_THEN (fun th => HolLight.tactic_of do pure (MP_TAC (← HolLight.EQ_IMP_RULE th).1)) THEN
    FIRST_ASSUM (X_CHOOSE_TAC ([[y:A]]) o HolLight.MATCH_MP SIZE_EXISTS) THEN
    FIRST_ASSUM (MP_TAC o HolLight.SPEC ([[y:A]]) o HolLight.REWRITE_RULE [SUBSET]) THEN
    ASM_REWRITE_TAC [IN_IMAGE] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[n:num]]) STRIP_ASSUME_TAC) THEN
    HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
        pure (SUBGOAL_THEN (← ec (HolCore.Equal.lhand (← ec (HolCore.Equal.lhand w)))) (fun t => REWRITE_TAC [t]))) THENL
     [MAP_EVERY EXISTS_TAC [([[n:num]]), ([[y:A]])] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[m:num]]) (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[x:A]]) STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [([[m:num]]), ([[u DELETE (x:A)]])] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC [] THEN CONV_TAC HolLight.SYM_CONV THEN
      MATCH_MP_TAC INSERT_DELETE THEN FIRST_ASSUM (SUBST1_TAC o HolLight.SYM) THEN
      FIRST_ASSUM MATCH_ACCEPT_TAC,
      X_GEN_TAC ([[z:A]]) THEN REWRITE_TAC [IN_DELETE] THEN STRIP_TAC THEN
      FIRST_ASSUM (MP_TAC o HolLight.SPEC ([[z:A]]) o HolLight.REWRITE_RULE [SUBSET]) THEN
      ASM_REWRITE_TAC [IN_IMAGE] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[k:num]]) STRIP_ASSUME_TAC) THEN
      EXISTS_TAC ([[k:num]]) THEN ASM_REWRITE_TAC [(← HolLight.GSYM NOT_LESS_EQUAL)] THEN
      REWRITE_TAC [LESS_OR_EQ, DE_MORGAN_THM] THEN CONJ_TAC THENL
       [DISCH_THEN (ANTE_RES_THEN (MP_TAC o HolLight.CONV_RULE NOT_EXISTS_CONV)) THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[z:A]])) THEN REWRITE_TAC [] THEN
        CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC,
        DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC ([[~(z:A = x)]]) THEN ASM_REWRITE_TAC []]])
  : ExceptT String IO thm).run
#eval IMAGE_WOP_LEMMA

/- ------------------------------------------------------------------------ -/
/- Lemma about finite colouring of natural numbers.                         -/
/- ------------------------------------------------------------------------ -/

#eval phrase 181
def COLOURING_LEMMA : thm := keep "COLOURING_LEMMA" fun _ => (do
  let h1 ← tt (← ExceptT.mk [[(c ==> d) ==> (b ==> c) ==> b ==> d]])
  prove ([[!M col s. (INFINITE(s) /\ !n:A. n IN s ==> col(n) <= M) ==>
          ?c t. t SUBSET s /\ INFINITE(t) /\ !n:A. n IN t ==> (col(n) = c)]])
   (INDUCT_TAC THENL
     [REWRITE_TAC [LESS_EQ_0] THEN REPEAT STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [([[0]]), ([[s:A->bool]])] THEN
      ASM_REWRITE_TAC [SUBSET_REFL],
      REPEAT STRIP_TAC THEN SUBGOAL_THEN ([[INFINITE { x:A | x IN s /\ (col x = SUC M) } \/
      INFINITE { x:A | x IN s /\ col x <= M}]]) DISJ_CASES_TAC THENL
       [UNDISCH_TAC ([[INFINITE(s:A->bool)]]) THEN
        REWRITE_TAC [INFINITE, (← HolLight.GSYM DE_MORGAN_THM), (← HolLight.GSYM FINITE_UNION)] THEN
        CONV_TAC HolLight.CONTRAPOS_CONV THEN REWRITE_TAC [] THEN
        DISCH_THEN (MATCH_MP_TAC o HolLight.MATCH_MP SUBSET_FINITE) THEN
        REWRITE_TAC [SUBSET, IN_UNION] THEN
        REWRITE_TAC [IN_ELIM_THM] THEN
        GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [(← HolLight.GSYM LESS_EQ_SUC)] THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
        MAP_EVERY EXISTS_TAC [([[SUC M]]), ([[{ x:A | x IN s /\ (col x = SUC M)}]])] THEN
        ASM_REWRITE_TAC [SUBSET] THEN REWRITE_TAC [IN_ELIM_THM] THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
        SUBGOAL_THEN ([[!n:A. n IN { x | x IN s /\ col x <= M } ==> col(n) <= M]]) MP_TAC THENL
         [GEN_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN
          DISCH_THEN (MATCH_ACCEPT_TAC o HolLight.CONJUNCT2),
          FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [([[col:A->num]]),
                                          ([[{ x:A | x IN s /\ col x <= M}]])]) THEN
          ASM_SIMP_TAC [] THEN
          MATCH_MP_TAC h1 THEN
          DISCH_THEN (X_CHOOSE_THEN ([[c:num]]) (X_CHOOSE_TAC ([[t:A->bool]]))) THEN
          MAP_EVERY EXISTS_TAC [([[c:num]]), ([[t:A->bool]])] THEN
          ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC ([[{ x:A | x IN s /\ col x <= M }]]) THEN ASM_REWRITE_TAC [] THEN
          REWRITE_TAC [SUBSET] THEN REWRITE_TAC [IN_ELIM_THM] THEN
          REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []]]])
  : ExceptT String IO thm).run
#eval COLOURING_LEMMA

#eval phrase 182
def COLOURING_THM : thm := keep "COLOURING_THM" fun _ => (do
  prove ([[!M col. (!n. col n <= M) ==>
           ?c s. INFINITE(s) /\ !n:num. n IN s ==> (col(n) = c)]])
   (REPEAT STRIP_TAC THEN MP_TAC (← HolLight.ISPECL [([[M:num]]), ([[col:num->num]]), ([[UNIV:num->bool]])] COLOURING_LEMMA) THEN
    ASM_REWRITE_TAC [num_INFINITE] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[c:num]]) (X_CHOOSE_TAC ([[t:num->bool]]))) THEN
    MAP_EVERY EXISTS_TAC [([[c:num]]), ([[t:num->bool]])] THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval COLOURING_THM

/- ------------------------------------------------------------------------ -/
/- Simple approach via lemmas then induction over size of coloured sets.    -/
/- ------------------------------------------------------------------------ -/

#eval phrase 183
def RAMSEY_LEMMA1 : thm := keep "RAMSEY_LEMMA1" fun _ => (do
  prove ([[(!C s. INFINITE(s:A->bool) /\
         (!t. t SUBSET s /\ t HAS_SIZE N ==> C(t) <= M)
         ==> ?t c. INFINITE(t) /\ t SUBSET s /\
                   (!u. u SUBSET t /\ u HAS_SIZE N ==> (C(u) = c)))
  ==> !C s. INFINITE(s:A->bool) /\
            (!t. t SUBSET s /\ t HAS_SIZE (SUC N) ==> C(t) <= M)
            ==> ?t c. INFINITE(t) /\ t SUBSET s /\ ~(((@) s) IN t) /\
                      (!u. u SUBSET t /\ u HAS_SIZE N
                           ==> (C(((@) s) INSERT u) = c))]])
   (DISCH_THEN ((fun t => REPEAT STRIP_TAC THEN t) o MP_TAC) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[\u. C (((@) s :A) INSERT u):num]])) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[s DELETE ((@)s:A)]])) THEN BETA_TAC THEN
    ASM_REWRITE_TAC [INFINITE_DELETE] THEN
    HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
        pure (SUBGOAL_THEN (← ec (HolCore.Equal.lhand (← ec (HolCore.Equal.lhand w)))) (fun t => REWRITE_TAC [t]))) THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
       [UNDISCH_TAC ([[t SUBSET (s DELETE ((@) s :A))]]) THEN
        REWRITE_TAC [SUBSET, IN_INSERT, IN_DELETE, NOT_IN_EMPTY] THEN
        DISCH_TAC THEN GEN_TAC THEN DISCH_THEN DISJ_CASES_TAC THEN
        ASM_REWRITE_TAC [] THENL
         [MATCH_MP_TAC INFINITE_CHOOSE,
          FIRST_ASSUM (ANTE_RES_THEN ASSUME_TAC)] THEN
        ASM_REWRITE_TAC [],
        MATCH_MP_TAC SIZE_INSERT THEN ASM_REWRITE_TAC [] THEN
        DISCH_TAC THEN UNDISCH_TAC ([[t SUBSET (s DELETE ((@) s :A))]]) THEN
        ASM_REWRITE_TAC [SUBSET, IN_DELETE] THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[(@)s:A]])) THEN ASM_REWRITE_TAC []],
      DISCH_THEN (X_CHOOSE_THEN ([[t:A->bool]]) MP_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN ([[c:num]]) STRIP_ASSUME_TAC) THEN
      MAP_EVERY EXISTS_TAC [([[t:A->bool]]), ([[c:num]])] THEN ASM_REWRITE_TAC [] THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [SUBSET, IN_DELETE]) THEN CONJ_TAC THENL
       [REWRITE_TAC [SUBSET] THEN
        GEN_TAC THEN DISCH_THEN (ANTE_RES_THEN (fun th => REWRITE_TAC [th])),
        DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN REWRITE_TAC []]])
  : ExceptT String IO thm).run
#eval RAMSEY_LEMMA1

#eval phrase 184
def RAMSEY_LEMMA2 : thm := keep "RAMSEY_LEMMA2" fun _ => (do
  prove ([[(!C s. INFINITE(s:A->bool) /\
         (!t. t SUBSET s /\ t HAS_SIZE (SUC N) ==> C(t) <= M)
        ==> ?t c. INFINITE(t) /\ t SUBSET s /\ ~(((@) s) IN t) /\
                  (!u. u SUBSET t /\ u HAS_SIZE N
                       ==> (C(((@) s) INSERT u) = c)))
  ==> !C s. INFINITE(s:A->bool) /\
            (!t. t SUBSET s /\ t HAS_SIZE (SUC N) ==> C(t) <= M)
            ==> ?t x col. (!n. col n <= M) /\
                          (!n. (t n) SUBSET s) /\
                          (!n. t(SUC n) SUBSET (t n)) /\
                          (!n. ~((x n) IN (t n))) /\
                          (!n. x(SUC n) IN (t n)) /\
                          (!n. (x n) IN s) /\
                          (!n u. u SUBSET (t n) /\ u HAS_SIZE N
                                 ==> (C((x n) INSERT u) = col n))]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[s:A->bool]]), ([[\s (n:num). @t:A->bool. ?c:num.
      INFINITE(t) /\
      t SUBSET s /\
      ~(((@) s) IN t) /\
      !u. u SUBSET t /\ u HAS_SIZE N ==> (C(((@) s) INSERT u) = c)]])] num_Axiom) THEN DISCH_THEN (MP_TAC o HolLight.BETA_RULE o HolLight.EXISTENCE) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[f:num->(A->bool)]]) STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN ([[!n:num. (f n) SUBSET (s:A->bool) /\
    ?c. INFINITE(f(SUC n)) /\ f(SUC n) SUBSET (f n) /\
        ~(((@)(f n)) IN (f(SUC n))) /\
        !u. u SUBSET (f(SUC n)) /\ u HAS_SIZE N ==>
          (C(((@)(f n)) INSERT u) = c:num)]]) MP_TAC THENL
     [MATCH_MP_TAC num_INDUCTION THEN REPEAT STRIP_TAC THENL
       [ASM_REWRITE_TAC [SUBSET_REFL],
        FIRST_ASSUM (SUBST1_TAC o HolLight.SPEC ([[0]])) THEN CONV_TAC (pureC SELECT_CONV) THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC ([[f(n:num):A->bool]]) THEN
        CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC,
        FIRST_ASSUM (SUBST1_TAC o HolLight.SPEC ([[SUC n]])) THEN CONV_TAC (pureC SELECT_CONV) THEN
        FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THEN
        TRY (FIRST_ASSUM MATCH_ACCEPT_TAC) THEN REPEAT STRIP_TAC THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
        REPEAT (MATCH_MP_TAC SUBSET_TRANS THEN
          FIRST_ASSUM (fun th => HolLight.tactic_of do
        pure (EXISTS_TAC (← ec (HolCore.Kernel.rand (concl th))) THEN
          CONJ_TAC THENL [FIRST_ASSUM MATCH_ACCEPT_TAC, ALL_TAC]))) THEN
        MATCH_ACCEPT_TAC SUBSET_REFL],
      PURE_REWRITE_TAC [LEFT_EXISTS_AND_THM, RIGHT_EXISTS_AND_THM,
                       FORALL_AND_THM] THEN
      DISCH_THEN (REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) MP_TAC) THEN
      DISCH_THEN (X_CHOOSE_TAC ([[col:num->num]]) o HolLight.CONV_RULE SKOLEM_CONV) THEN
      MAP_EVERY EXISTS_TAC [([[\n:num. f(SUC n):A->bool]]), ([[\n:num. (@)(f n):A]])] THEN
      BETA_TAC THEN EXISTS_TAC ([[col:num->num]]) THEN CONJ_TAC THENL
       [X_GEN_TAC ([[n:num]]) THEN
        FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP INFINITE_FINITE_CHOICE o HolLight.SPEC ([[n:num]])) THEN
        DISCH_THEN (CHOOSE_THEN MP_TAC o HolLight.SPEC ([[N:num]])) THEN
        DISCH_THEN (fun th => STRIP_ASSUME_TAC th THEN
            ANTE_RES_THEN MP_TAC th) THEN
        DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN FIRST_ASSUM MATCH_MP_TAC THEN
        CONJ_TAC THENL
         [REWRITE_TAC [INSERT_SUBSET] THEN CONJ_TAC THENL
           [FIRST_ASSUM (MATCH_MP_TAC o HolLight.REWRITE_RULE [SUBSET]) THEN
            EXISTS_TAC ([[n:num]]) THEN MATCH_MP_TAC INFINITE_CHOOSE THEN
            SPEC_TAC (([[n:num]]), ([[n:num]])) THEN INDUCT_TAC THEN
            TRY (FIRST_ASSUM MATCH_ACCEPT_TAC) THEN ASM_REWRITE_TAC [],
            MATCH_MP_TAC SUBSET_TRANS THEN
            EXISTS_TAC ([[f(SUC n):A->bool]]) THEN ASM_REWRITE_TAC []],
          MATCH_MP_TAC SIZE_INSERT THEN ASM_REWRITE_TAC [] THEN
          UNDISCH_TAC ([[!n:num. ~(((@)(f n):A) IN (f(SUC n)))]]) THEN
          DISCH_THEN (MP_TAC o HolLight.SPEC ([[n:num]])) THEN CONV_TAC HolLight.CONTRAPOS_CONV THEN
          REWRITE_TAC [] THEN
          FIRST_ASSUM (MATCH_ACCEPT_TAC o HolLight.REWRITE_RULE [SUBSET])],
        REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM MATCH_ACCEPT_TAC) THENL
         [GEN_TAC, INDUCT_TAC THENL
           [ASM_REWRITE_TAC [],
            FIRST_ASSUM (MATCH_MP_TAC o HolLight.REWRITE_RULE [SUBSET]) THEN
            EXISTS_TAC ([[SUC n]])]] THEN
        MATCH_MP_TAC INFINITE_CHOOSE THEN ASM_REWRITE_TAC []]])
  : ExceptT String IO thm).run
#eval RAMSEY_LEMMA2

#eval phrase 185
def RAMSEY_LEMMA3 : thm := keep "RAMSEY_LEMMA3" fun _ => (do
  let h1 ← tt (← ExceptT.mk [[(a <=> a /\ b) <=> a ==> b]])
  prove ([[(!C s. INFINITE(s:A->bool) /\
             (!t. t SUBSET s /\ t HAS_SIZE (SUC N) ==> C(t) <= M)
             ==> ?t x col. (!n. col n <= M) /\
                           (!n. (t n) SUBSET s) /\
                           (!n. t(SUC n) SUBSET (t n)) /\
                           (!n. ~((x n) IN (t n))) /\
                           (!n. x(SUC n) IN (t n)) /\
                           (!n. (x n) IN s) /\
                           (!n u. u SUBSET (t n) /\ u HAS_SIZE N
                                  ==> (C((x n) INSERT u) = col n)))
  ==> !C s. INFINITE(s:A->bool) /\
            (!t. t SUBSET s /\ t HAS_SIZE (SUC N) ==> C(t) <= M)
            ==> ?t c. INFINITE(t) /\ t SUBSET s /\
                      (!u. u SUBSET t /\ u HAS_SIZE (SUC N) ==> (C(u) = c))]])
   (DISCH_THEN ((fun t => REPEAT STRIP_TAC THEN t) o MP_TAC) THEN
    DISCH_THEN (MP_TAC o HolLight.SPECL [([[C:(A->bool)->num]]), ([[s:A->bool]])]) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[t:num->(A->bool)]]) MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[x:num->A]]) MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[col:num->num]]) STRIP_ASSUME_TAC) THEN
    MP_TAC (← HolLight.ISPECL [([[M:num]]), ([[col:num->num]]), ([[UNIV:num->bool]])] COLOURING_LEMMA) THEN ASM_REWRITE_TAC [num_INFINITE] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[c:num]]) MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[t:num->bool]]) STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [([[IMAGE (x:num->A) t]]), ([[c:num]])] THEN
    SUBGOAL_THEN ([[!m n. m <= n ==> (t n:A->bool) SUBSET (t m)]]) ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC [LESS_EQ_EXISTS] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[d:num]]) SUBST1_TAC) THEN
      SPEC_TAC (([[d:num]]), ([[d:num]])) THEN INDUCT_TAC THEN
      ASM_REWRITE_TAC [ADD_CLAUSES, SUBSET_REFL] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC ([[t(m + d):A->bool]]) THEN
      ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN ([[!m n. m < n ==> (x n:A) IN (t m)]]) ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN
      DISCH_THEN (X_CHOOSE_THEN ([[d:num]]) SUBST1_TAC o HolLight.MATCH_MP LESS_ADD_1) THEN
      FIRST_ASSUM (MP_TAC o HolLight.SPECL [([[m:num]]), ([[m + d]])]) THEN
      REWRITE_TAC [LESS_EQ_ADD, SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [(← HolLight.GSYM ADD1), ADD_CLAUSES], ALL_TAC] THEN
    SUBGOAL_THEN ([[!m n. ((x:num->A) m = x n) <=> (m = n)]]) ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN EQ_TAC THENL
       [REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (← HolLight.SPECL [([[m:num]]), ([[n:num]])] LESS_LESS_CASES) THEN
        ASM_REWRITE_TAC [] THEN REPEAT DISCH_TAC THEN
        FIRST_ASSUM (ANTE_RES_THEN MP_TAC) THEN ASM_REWRITE_TAC [] THEN
        FIRST_ASSUM (UNDISCH_TAC o check is_eq o concl) THEN
        DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN ASM_REWRITE_TAC [],
        DISCH_THEN SUBST1_TAC THEN REFL_TAC], ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC ([[INFINITE(t:num->bool)]]) THEN
      MATCH_MP_TAC INFINITE_IMAGE_INJ THEN ASM_REWRITE_TAC [],
      REWRITE_TAC [SUBSET, IN_IMAGE] THEN GEN_TAC THEN
      DISCH_THEN (CHOOSE_THEN (SUBST1_TAC o HolLight.CONJUNCT1)) THEN ASM_REWRITE_TAC [],
      GEN_TAC THEN DISCH_THEN (fun th => STRIP_ASSUME_TAC th THEN MP_TAC th) THEN
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP IMAGE_WOP_LEMMA) THEN
      DISCH_THEN (X_CHOOSE_THEN ([[n:num]]) (X_CHOOSE_THEN ([[v:A->bool]]) MP_TAC)) THEN
      DISCH_THEN STRIP_ASSUME_TAC THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN ([[c = (col:num->num) n]]) SUBST1_TAC THENL
       [CONV_TAC HolLight.SYM_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC ([[u SUBSET (IMAGE (x:num->A) t)]]) THEN
        REWRITE_TAC [SUBSET, IN_IMAGE] THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[(x:num->A) n]])) THEN
        ASM_REWRITE_TAC [IN_INSERT] THEN
        DISCH_THEN (CHOOSE_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC [],
        FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
         [REWRITE_TAC [SUBSET] THEN GEN_TAC THEN
          DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN
          DISCH_THEN (X_CHOOSE_THEN ([[m:num]]) STRIP_ASSUME_TAC) THEN
          ASM_REWRITE_TAC [] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
          SUBGOAL_THEN ([[v = u DELETE ((x:num->A) n)]]) SUBST1_TAC THENL
           [ASM_REWRITE_TAC [] THEN REWRITE_TAC [DELETE_INSERT] THEN
            REWRITE_TAC [EXTENSION, IN_DELETE,
              h1] THEN
            GEN_TAC THEN CONV_TAC HolLight.CONTRAPOS_CONV THEN REWRITE_TAC [] THEN
            DISCH_THEN SUBST1_TAC THEN DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN
            ASM_REWRITE_TAC [] THEN
            DISCH_THEN (CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
            ASM_REWRITE_TAC [LESS_REFL],
            MATCH_MP_TAC SIZE_DELETE THEN CONJ_TAC THENL
             [ASM_REWRITE_TAC [IN_INSERT], FIRST_ASSUM MATCH_ACCEPT_TAC]]]]])
  : ExceptT String IO thm).run
#eval RAMSEY_LEMMA3

#eval phrase 186
def RAMSEY : thm := keep "RAMSEY" fun _ => (do
  prove ([[!M N C s.
        INFINITE(s:A->bool) /\
        (!t. t SUBSET s /\ t HAS_SIZE N ==> C(t) <= M)
        ==> ?t c. INFINITE(t) /\ t SUBSET s /\
                  (!u. u SUBSET t /\ u HAS_SIZE N ==> (C(u) = c))]])
   (GEN_TAC THEN INDUCT_TAC THENL
     [REPEAT STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [([[s:A->bool]]), ([[(C:(A->bool)->num) {}]])] THEN
      ASM_REWRITE_TAC [HAS_SIZE_0] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [SUBSET_REFL],
      MAP_EVERY MATCH_MP_TAC [RAMSEY_LEMMA3, RAMSEY_LEMMA2, RAMSEY_LEMMA1] THEN
      POP_ASSUM MATCH_ACCEPT_TAC])
  : ExceptT String IO thm).run
#eval RAMSEY

end Hol100.Ramsey
