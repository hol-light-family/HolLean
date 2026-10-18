/- File: HolExamples/DLO.lean
Translation of HOL Light's Examples/dlo.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Dense linear order decision procedure for reals, by Sean McLaughlin.  The
OCaml conversions and quantifier-elimination functions are ported with the
same names and algorithm; HOL Light's kernel rules and term operations
(`TAUT`, `ISPEC`, `dest_neg`, `MK_COMB`, `TRANS`, ...) are `Except`/IO-valued
here, so OCaml's exception control flow becomes `Except`/`tryWith`.
-/
import HolExamples.Common
open HolCore.Kernel HolCore.Lib HolCore.Basics HolCore.Bool Session HolLight.Syntax HolExamples
open HolLight (tactic_of tryWith)
namespace HolExamples.DLO

/- The session's `prove` lifted into `ExceptT String IO`. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/-- Cache a value built by an `ExceptT String IO` computation (a toplevel
    `let` whose right-hand side builds a conversion from proved theorems,
    so OCaml's definition-time traces fire at the defining phrase). -/
private unsafe def keepE {α : Type} [Inhabited α] (name : String)
    (m : ExceptT String IO α) : α :=
  keep name fun _ =>
    match unsafeIO m.run with
    | .ok (.ok v) => v
    | .ok (.error e) => panic! e
    | .error e => panic! (toString e)

/- ========================================================================= -/
/- Dense linear order decision procedure for reals, by Sean McLaughlin.      -/
/- ========================================================================= -/

#eval phrase 1
#eval Session.prioritize_real

#eval phrase 2
/- ---------------------------------------------------------------------- -/
/-  Util                                                                  -/
/- ---------------------------------------------------------------------- -/
unsafe def eitConj : List term → Except String term
  | [] => Except.error "end_itlist"
  | [x] => Except.ok x
  | h :: t => do mk_conj h (← eitConj t)

unsafe def list_conj (l : List term) : Except String term :=
  let t_tm : term := ([[T]])
  if l == [] then Except.ok t_tm else eitConj l
#eval IO.println "<fun>"

#eval phrase 3
-- OCaml's `let mk_lt = mk_binop `(<)`` parses `(<)` once, at this phrase.
-- Keep the operator term so it is not re-parsed (and re-warned) on every call.
unsafe def lt_op : term := keep "lt_op" fun _ => ([[(<)]])
unsafe def mk_lt (l r : term) : Except String term := do
  let f ← mk_binop lt_op l
  f r
#eval (do let _ ← HolCore.Printer.string_of_term lt_op; IO.println "<fun>")

#eval phrase 4
/- ---------------------------------------------------------------------- -/
/-  cnnf                                                                  -/
/- ---------------------------------------------------------------------- -/
unsafe def DOUBLE_NEG_CONV (tm : term) : IO (Except String thm) := (do
  let dn_thm ← ExceptT.mk (TAUT [[!x. ~(~ x) <=> x]])
  let tm' ← liftExcept (do dest_neg (← dest_neg tm))
  liftExcept (ISPEC tm' dn_thm) : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 5
unsafe def IMP_CONV (tm : term) : IO (Except String thm) := (do
  let i_thm ← ExceptT.mk (TAUT [[!a b. (a ==> b) <=> (~a \/ b)]])
  let (a, b) ← liftExcept (HolCore.Basics.dest_imp tm)
  liftExcept (ISPECL [a, b] i_thm) : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 6
unsafe def BEQ_CONV (tm : term) : IO (Except String thm) := (do
  let beq_thm ← ExceptT.mk (TAUT [[!a b. (a = b) <=> (a /\ b \/ ~a /\ ~b)]])
  let (a, b) ← liftExcept (dest_eq tm)
  liftExcept (ISPECL [a, b] beq_thm) : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 7
unsafe def NEG_AND_CONV (tm : term) : IO (Except String thm) := (do
  let na_thm ← ExceptT.mk (TAUT [[!a b. ~(a /\ b) <=> (~a \/ ~b)]])
  let (a, b) ← liftExcept (do HolCore.Basics.dest_conj (← dest_neg tm))
  liftExcept (ISPECL [a, b] na_thm) : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 8
unsafe def NEG_OR_CONV (tm : term) : IO (Except String thm) := (do
  let no_thm ← ExceptT.mk (TAUT [[!a b. ~(a \/ b) <=> (~a /\ ~b)]])
  let (a, b) ← liftExcept (do HolCore.Basics.dest_disj (← dest_neg tm))
  liftExcept (ISPECL [a, b] no_thm) : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 9
unsafe def NEG_IMP_CONV (tm : term) : IO (Except String thm) := (do
  let ni_thm ← ExceptT.mk (TAUT [[!a b. ~(a ==> b) <=> (a /\ ~b)]])
  let (a, b) ← liftExcept (do HolCore.Basics.dest_imp (← dest_neg tm))
  liftExcept (ISPECL [a, b] ni_thm) : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 10
unsafe def NEG_BEQ_CONV (tm : term) : IO (Except String thm) := (do
  let nbeq_thm ← ExceptT.mk (TAUT [[!a b. ~(a = b) <=> (a /\ ~b \/ ~a /\ b)]])
  let (a, b) ← liftExcept (do dest_eq (← dest_neg tm))
  liftExcept (ISPECL [a, b] nbeq_thm) : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 11
-- tm = (p /\ q0) \/ (~p /\ q1)
unsafe def dest_cases (tm : term) : Except String (term × term × term) :=
  match (do
    let (l, r) ← HolCore.Basics.dest_disj tm
    let (p, q0) ← HolCore.Basics.dest_conj l
    let (np, q1) ← HolCore.Basics.dest_conj r
    if (← mk_neg p) == np then Except.ok (p, q0, q1)
    else Except.error "not a cases term" : Except String (term × term × term)) with
  | .ok v => .ok v
  | .error _ => .error "not a cases term"
#eval IO.println "<fun>"

#eval phrase 12
unsafe def is_cases (tm : term) : Bool := can dest_cases tm
#eval IO.println "<fun>"

#eval phrase 13
unsafe def CASES_CONV (tm : term) : IO (Except String thm) := (do
  let c_thm ← ExceptT.mk (TAUT [[!p q0 q1. ~(p /\ q0 \/ ~p /\ q1) <=> (p /\ ~q0 \/ ~p /\ ~q1)]])
  let (p, q0, q1) ← liftExcept (dest_cases tm)
  liftExcept (ISPECL [p, q0, q1] c_thm) : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 14
unsafe def QE_SIMPLIFY_CONV : term → IO (Except String thm) :=
  keepE "QE_SIMPLIFY_CONV" (do
  -- parsed here, inside the cached block: a coerced `[[ ]]` is a pure value
  -- to the compiler, which may lift it out and parse it at every call
  let neu_tm ← ExceptT.mk (HolCore.Parser.parse_term
    "~(?!x. P x) <=> (!x. ~P x) \\/ ?x x'. P x /\\ P x' /\\ ~(x = x')")
  let NOT_EXISTS_UNIQUE_THM ← prove neu_tm
    (REWRITE_TAC [EXISTS_UNIQUE_THM, DE_MORGAN_THM, NOT_EXISTS_THM] THEN
     REWRITE_TAC [NOT_FORALL_THM, NOT_IMP, CONJ_ASSOC])
  let t1 ← ExceptT.mk (TAUT [[~(~p) <=> p]])
  let t2 ← ExceptT.mk (TAUT [[~(p /\ q) <=> ~p \/ ~q]])
  let t3 ← ExceptT.mk (TAUT [[~(p \/ q) <=> ~p /\ ~q]])
  let t4 ← ExceptT.mk (TAUT [[~(p ==> q) <=> p /\ ~q]])
  let t5 ← ExceptT.mk (TAUT [[p ==> q <=> ~p \/ q]])
  let nft ← ExceptT.mk (pure (Except.ok NOT_FORALL_THM))
  let net_ ← ExceptT.mk (pure (Except.ok NOT_EXISTS_THM))
  let eut ← ExceptT.mk (pure (Except.ok EXISTS_UNIQUE_THM))
  let t10 ← ExceptT.mk (TAUT [[~(p = q) <=> (p /\ ~q) \/ (~p /\ q)]])
  let t11 ← ExceptT.mk (TAUT [[(p = q) <=> (p /\ q) \/ (~p /\ ~q)]])
  let t12 ← ExceptT.mk (TAUT [[~(p /\ q \/ ~p /\ r) <=> p /\ ~q \/ ~p /\ ~r]])
  let tauts := [t1, t2, t3, t4, t5, nft, net_, eut, NOT_EXISTS_UNIQUE_THM, t10, t11, t12]
  pure (fun tm => Session.GEN_REWRITE_CONV HolLight.TOP_SWEEP_CONV tauts tm))
#eval (do let _ ← QE_SIMPLIFY_CONV [[T]]; IO.println "<fun>")

#eval phrase 15
unsafe def CNNF_CONV (lfn_conv : term → IO (Except String thm)) (tm0 : term) :
    IO (Except String thm) := (do
  let refl_conj := HolCore.Kernel.REFL [[(/\)]]
  let refl_disj := HolCore.Kernel.REFL [[(\/)]]
  let rec cnnf_conv (tm : term) : ExceptT String IO thm := do
    if is_conj tm then
      let (p, q) ← liftExcept (HolCore.Basics.dest_conj tm)
      let thm1 ← cnnf_conv p
      let thm2 ← cnnf_conv q
      HolLight.MK_COMB (← HolLight.MK_COMB (refl_conj, thm1), thm2)
    else if is_disj tm then
      let (p, q) ← liftExcept (HolCore.Basics.dest_disj tm)
      let thm1 ← cnnf_conv p
      let thm2 ← cnnf_conv q
      HolLight.MK_COMB (← HolLight.MK_COMB (refl_disj, thm1), thm2)
    else if is_imp tm then
      let (p, q) ← liftExcept (HolCore.Basics.dest_imp tm)
      let thm1 ← cnnf_conv (← liftExcept (mk_neg p))
      let thm2 ← cnnf_conv q
      HolLight.TRANS (← ExceptT.mk (IMP_CONV tm))
        (← HolLight.MK_COMB (← HolLight.MK_COMB (refl_disj, thm1), thm2))
    else if is_iff tm then
      let (p, q) ← liftExcept (dest_eq tm)
      let pthm ← cnnf_conv p
      let qthm ← cnnf_conv q
      let npthm ← cnnf_conv (← liftExcept (mk_neg p))
      let nqthm ← cnnf_conv (← liftExcept (mk_neg q))
      let thm1 ← HolLight.MK_COMB (← HolLight.MK_COMB (refl_conj, pthm), qthm)
      let thm2 ← HolLight.MK_COMB (← HolLight.MK_COMB (refl_conj, npthm), nqthm)
      HolLight.TRANS (← ExceptT.mk (BEQ_CONV tm))
        (← HolLight.MK_COMB (← HolLight.MK_COMB (refl_disj, thm1), thm2))
    else if is_neg tm then
      let tm' ← liftExcept (dest_neg tm)
      if is_neg tm' then
        let tm'' ← liftExcept (dest_neg tm')
        let thm ← cnnf_conv tm
        HolLight.TRANS (← ExceptT.mk (DOUBLE_NEG_CONV tm'')) thm
      else if is_conj tm' then
        let (p, q) ← liftExcept (HolCore.Basics.dest_conj tm')
        let thm1 ← cnnf_conv (← liftExcept (mk_neg p))
        let thm2 ← cnnf_conv (← liftExcept (mk_neg q))
        HolLight.TRANS (← ExceptT.mk (NEG_AND_CONV tm))
          (← HolLight.MK_COMB (← HolLight.MK_COMB (refl_disj, thm1), thm2))
      else if is_cases tm' then
        let (p, q0, q1) ← liftExcept (dest_cases tm)
        let thm1 ← cnnf_conv (← liftExcept (mk_conj p (← liftExcept (mk_neg q0))))
        let thm2 ← cnnf_conv (← liftExcept (mk_conj (← liftExcept (mk_neg p)) (← liftExcept (mk_neg q1))))
        HolLight.TRANS (← ExceptT.mk (CASES_CONV tm))
          (← HolLight.MK_COMB (← HolLight.MK_COMB (refl_disj, thm1), thm2))
      else if is_disj tm' then
        let (p, q) ← liftExcept (HolCore.Basics.dest_disj tm')
        let thm1 ← cnnf_conv (← liftExcept (mk_neg p))
        let thm2 ← cnnf_conv (← liftExcept (mk_neg q))
        HolLight.TRANS (← ExceptT.mk (NEG_OR_CONV tm))
          (← HolLight.MK_COMB (← HolLight.MK_COMB (refl_conj, thm1), thm2))
      else if is_imp tm' then
        let (p, q) ← liftExcept (HolCore.Basics.dest_imp tm')
        let thm1 ← cnnf_conv p
        let thm2 ← cnnf_conv (← liftExcept (mk_neg q))
        HolLight.TRANS (← ExceptT.mk (NEG_IMP_CONV tm))
          (← HolLight.MK_COMB (← HolLight.MK_COMB (refl_conj, thm1), thm2))
      else if is_iff tm' then
        let (p, q) ← liftExcept (dest_eq tm')
        let pthm ← cnnf_conv p
        let qthm ← cnnf_conv q
        let npthm ← cnnf_conv (← liftExcept (mk_neg p))
        let nqthm ← cnnf_conv (← liftExcept (mk_neg q))
        let thm1 ← HolLight.MK_COMB (← HolLight.MK_COMB (refl_conj, pthm), nqthm)
        let thm2 ← HolLight.MK_COMB (← HolLight.MK_COMB (refl_conj, npthm), qthm)
        HolLight.TRANS (← ExceptT.mk (NEG_BEQ_CONV tm))
          (← HolLight.MK_COMB (← HolLight.MK_COMB (refl_disj, thm1), thm2))
      else ExceptT.mk (lfn_conv tm)
    else ExceptT.mk (lfn_conv tm)
  ExceptT.mk ((QE_SIMPLIFY_CONV THENC (fun t => (cnnf_conv t).run) THENC QE_SIMPLIFY_CONV) tm0)
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 16
/-

let tests = [
`~(a /\ b)`;
`~(a \/ b)`;
`~(a ==> b)`;
`~(a:bool <=> b)`;
`~ ~ a`;
];;

map (CNNF_CONV (fun x -> REFL x)) tests;;
-/

/- ---------------------------------------------------------------------- -/
/-  Real Lists                                                            -/
/- ---------------------------------------------------------------------- -/
unsafe def MINL : thm := keep "MINL" fun _ => (do
  ExceptT.mk (new_recursive_definition list_RECURSION
   [[(MINL [] default = default) /\
     (MINL (CONS h t) default = min h (MINL t default))]])
  : ExceptT String IO thm).run
#eval MINL

#eval phrase 17
unsafe def MAXL : thm := keep "MAXL" fun _ => (do
  ExceptT.mk (new_recursive_definition list_RECURSION
   [[(MAXL [] default = default) /\
     (MAXL (CONS h t) default = max h (MAXL t default))]])
  : ExceptT String IO thm).run
#eval MAXL

#eval phrase 18
unsafe def MAX_LT : thm := keep "MAX_LT" fun _ => (do
  prove ([[!x y z. max x y < z <=> x < z /\ y < z]])
   (REWRITE_TAC [real_max] THEN MESON_TAC [REAL_LET_TRANS, REAL_LE_TOTAL])
  : ExceptT String IO thm).run
#eval MAX_LT

#eval phrase 19
unsafe def MIN_GT : thm := keep "MIN_GT" fun _ => (do
  prove ([[!x y z. x < real_min y z <=> x < y /\ x < z]])
   (REWRITE_TAC [real_min] THEN MESON_TAC [REAL_LTE_TRANS, REAL_LE_TOTAL])
  : ExceptT String IO thm).run
#eval MIN_GT

#eval phrase 20
unsafe def ALL_LT_LEMMA : thm := keep "ALL_LT_LEMMA" fun _ => (do
  prove ([[!left x lefts. ALL (\l. l < x) (CONS left lefts) <=> MAXL lefts left < x]])
   (GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [MAXL, listDefs.ALL] THEN
    SPEC_TAC ([[t:real list]], [[t:real list]]) THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC [listDefs.ALL, MAXL, MAX_LT] THEN ASM_MESON_TAC [MAX_LT])
  : ExceptT String IO thm).run
#eval ALL_LT_LEMMA

#eval phrase 21
unsafe def ALL_GT_LEMMA : thm := keep "ALL_GT_LEMMA" fun _ => (do
  prove ([[!right x rights.
        ALL (\r. x < r) (CONS right rights) <=> x < MINL rights right]])
   (GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [MINL, listDefs.ALL] THEN
    SPEC_TAC ([[t:real list]], [[t:real list]]) THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC [listDefs.ALL, MINL, MIN_GT] THEN ASM_MESON_TAC [MIN_GT])
  : ExceptT String IO thm).run
#eval ALL_GT_LEMMA

#eval phrase 22
/- ---------------------------------------------------------------------- -/
/-  Axioms                                                                -/
/- ---------------------------------------------------------------------- -/
unsafe def REAL_DENSE : thm := keep "REAL_DENSE" fun _ => (do
  prove ([[!x y. x < y ==> ?z. x < z /\ z < y]])
   (REPEAT STRIP_TAC THEN EXISTS_TAC [[(x + y) / &2]] THEN
    SIMP_TAC [REAL_LT_LDIV_EQ, REAL_LT_RDIV_EQ, REAL_OF_NUM_LT, ARITH] THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC)
  : ExceptT String IO thm).run
#eval REAL_DENSE

#eval phrase 23
unsafe def REAL_LT_EXISTS : thm := keep "REAL_LT_EXISTS" fun _ => (do
  prove ([[!x. ?y. x < y]])
   (GEN_TAC THEN
    EXISTS_TAC [[x + &1]] THEN
    REAL_ARITH_TAC)
  : ExceptT String IO thm).run
#eval REAL_LT_EXISTS

#eval phrase 24
unsafe def REAL_GT_EXISTS : thm := keep "REAL_GT_EXISTS" fun _ => (do
  prove ([[!x. ?y. y < x]])
   (GEN_TAC THEN
    EXISTS_TAC [[x - &1]] THEN
    REAL_ARITH_TAC)
  : ExceptT String IO thm).run
#eval REAL_GT_EXISTS

#eval phrase 25
/- ---------------------------------------------------------------------- -/
/-  lfn_dlo                                                               -/
/- ---------------------------------------------------------------------- -/
unsafe def LFN_DLO_CONV (tm : term) : IO (Except String thm) := (do
  let r1 ← ExceptT.mk (Session.REAL_ARITH2 [[~(s < t) <=> ((s = t) \/ (t < s))]])
  let r2 ← ExceptT.mk (Session.REAL_ARITH2 [[~(s = t) <=> (s < t \/ t < s)]])
  ExceptT.mk (Session.PURE_REWRITE_CONV [r1, r2] tm)
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 26
/- ------------------------------------------------------------------------- -/
/- Proforma theorems to support the main inference step.                     -/
/- ------------------------------------------------------------------------- -/
unsafe def PROFORMA_LEFT : thm := keep "PROFORMA_LEFT" fun _ => (do
  prove ([[!l ls. (?x. ALL (\l. l < x) (CONS l ls)) <=> T]])
   (REWRITE_TAC [ALL_LT_LEMMA] THEN MESON_TAC [REAL_LT_EXISTS])
  : ExceptT String IO thm).run
#eval PROFORMA_LEFT

#eval phrase 27
unsafe def PROFORMA_RIGHT : thm := keep "PROFORMA_RIGHT" fun _ => (do
  prove ([[!r rs. (?x. ALL (\r. x < r) (CONS r rs)) <=> T]])
   (REWRITE_TAC [ALL_GT_LEMMA] THEN MESON_TAC [REAL_GT_EXISTS])
  : ExceptT String IO thm).run
#eval PROFORMA_RIGHT

#eval phrase 28
unsafe def PROFORMA_BOTH : thm := keep "PROFORMA_BOTH" fun _ => (do
  prove ([[!l ls r rs.
        (?x. ALL (\l. l < x) (CONS l ls) /\ ALL (\r. x < r) (CONS r rs)) <=>
        ALL (\l. ALL (\r. l < r) (CONS r rs)) (CONS l ls)]])
   (REWRITE_TAC [ALL_LT_LEMMA, ALL_GT_LEMMA] THEN
    MESON_TAC [REAL_DENSE, REAL_LT_TRANS])
  : ExceptT String IO thm).run
#eval PROFORMA_BOTH

#eval phrase 29
/- ------------------------------------------------------------------------- -/
/- Deal with ?x. <conjunction of strict inequalities all involving x>        -/
/- ------------------------------------------------------------------------- -/
unsafe def mk_rlist (x : List term) : IO (Except String term) := (do
  let ty ← ExceptT.mk (HolCore.Parser.parse_type "real")
  ExceptT.mk (Session.mk_list x ty) : ExceptT String IO term).run
#eval IO.println "<fun>"

#eval phrase 30
unsafe def expand_all (th : thm) : IO (Except String thm) := (do
  let t1 ← ExceptT.mk (TAUT [[a /\ T <=> a]])
  ExceptT.mk (Session.PURE_REWRITE_RULE
    [listDefs.ALL, BETA_THM, (← ExceptT.mk (HolLight.GSYM CONJ_ASSOC)), t1] th)
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 31
unsafe def DLO_EQ_CONV (fm : term) : IO (Except String thm) := (do
  let mkEq ← ExceptT.mk (mk_eq : IO _)
  let (x, p) ← liftExcept (dest_exists fm)
  let (xl, xr) := partition (fun t => (match (do rand t : Except String term) with
                                        | .ok r => r == x | .error _ => false))
                            (conjuncts p)
  let lefts ← liftExcept (xl.mapM HolCore.Equal.lhand)
  let rights ← liftExcept (xr.mapM rand)
  let th1 ←
    if lefts == [] then
      ExceptT.mk (HolLight.SPECL [(← liftExcept (HolCore.Lib.hd rights)),
        (← ExceptT.mk (mk_rlist (← liftExcept (HolCore.Lib.tl rights))))] PROFORMA_RIGHT)
    else if rights == [] then
      ExceptT.mk (HolLight.SPECL [(← liftExcept (HolCore.Lib.hd lefts)),
        (← ExceptT.mk (mk_rlist (← liftExcept (HolCore.Lib.tl lefts))))] PROFORMA_LEFT)
    else
      ExceptT.mk (HolLight.SPECL [(← liftExcept (HolCore.Lib.hd lefts)),
        (← ExceptT.mk (mk_rlist (← liftExcept (HolCore.Lib.tl lefts)))),
        (← liftExcept (HolCore.Lib.hd rights)),
        (← ExceptT.mk (mk_rlist (← liftExcept (HolCore.Lib.tl rights))))] PROFORMA_BOTH)
  let th2 ← ExceptT.mk (HolLight.CONV_RULE
    (HolLight.LAND_CONV (fun t => pure (HolCore.Equal.GEN_ALPHA_CONV x t)))
    (← ExceptT.mk (expand_all th1)))
  let p' ← liftExcept (do pure (← dest_exists (← HolCore.Equal.lhand (concl th2))).2)
  let th3 ← HolLight.MK_EXISTS x (← HolLight.CONJ_ACI_RULE (← liftExcept (mkEq (p, p'))))
  HolLight.TRANS th3 th2
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 32
unsafe def pth_triv : thm := keep "pth_triv" fun _ => (do
  prove
   ([[((?x. x = x) <=> T) /\
     ((?x. x = t) <=> T) /\
     ((?x. t = x) <=> T) /\
     ((?x. (x = t) /\ P x) <=> P t) /\
     ((?x. (t = x) /\ P x) <=> P t)]])
    (MESON_TAC [])
  : ExceptT String IO thm).run
unsafe def pth_refl : thm := keep "pth_refl" fun _ => (do
  prove
   ([[(?x. (x = x) /\ P x) <=> (?x. P x)]])
    (MESON_TAC [])
  : ExceptT String IO thm).run

unsafe def eq_triv_conv (tm : term) : IO (Except String thm) :=
  Session.GEN_REWRITE_CONV HolCore.Lib.I [pth_triv] tm
unsafe def eq_refl_conv (tm : term) : IO (Except String thm) :=
  Session.GEN_REWRITE_CONV HolCore.Lib.I [pth_refl] tm
unsafe def lt_refl_conv (tm : term) : IO (Except String thm) :=
  Session.GEN_REWRITE_CONV HolLight.DEPTH_CONV
   [REAL_LT_REFL, AND_CLAUSES, EXISTS_SIMP] tm
#eval (do
  let _ ← HolCore.Printer.string_of_thm pth_triv
  let _ ← HolCore.Printer.string_of_thm pth_refl
  IO.println "<fun>"
  IO.println "<fun>"
  IO.println "<fun>" : IO Unit)

#eval phrase 33
unsafe def DLOBASIC_CONV (fm0 : term) : IO (Except String thm) :=
  let rec go (fm : term) : ExceptT String IO thm :=
    tryWith (do
      let (x, p) ← liftExcept (dest_exists fm)
      let cjs := conjuncts p
      tryWith (do
        let eq ← liftExcept (find (fun e => is_eq e &&
                   ((match HolCore.Equal.lhs e with | .ok l => l == x | _ => false) ||
                    (match HolCore.Equal.rhs e with | .ok r => r == x | _ => false))) cjs)
        let cjs' := eq :: setify (HolCore.Lib.subtract cjs [eq])
        let p' ← liftExcept (list_mk_conj cjs')
        let mkEq ← ExceptT.mk (mk_eq : IO _)
        let th1 ← HolLight.MK_EXISTS x (← HolLight.CONJ_ACI_RULE (← liftExcept (mkEq (p, p'))))
        let fm' ← liftExcept (rand (concl th1))
        tryWith (do HolLight.TRANS th1 (← ExceptT.mk (eq_triv_conv fm')))
          (do HolLight.TRANS th1 (← ExceptT.mk ((eq_refl_conv THENC (fun t => (go t).run)) fm'))))
        (do
          if HolCore.Lib.mem (← liftExcept (mk_lt x x)) cjs then ExceptT.mk (lt_refl_conv fm)
          else ExceptT.mk (DLO_EQ_CONV fm)))
      (do
        liftM (HolCore.Printer.print_qterm fm)
        throw "dlobasic")
  (go fm0).run
#eval IO.println "<fun>"

#eval phrase 34
/- ------------------------------------------------------------------------- -/
/- Overall quantifier elimination.                                           -/
/- ------------------------------------------------------------------------- -/
unsafe def AFN_DLO_CONV (_vars : List term) (tm : term) : IO (Except String thm) := (do
  let r1 ← ExceptT.mk (Session.REAL_ARITH2 [[s <= t <=> ~(t < s)]])
  let r2 ← ExceptT.mk (Session.REAL_ARITH2 [[s >= t <=> ~(s < t)]])
  let r3 ← ExceptT.mk (Session.REAL_ARITH2 [[s > t <=> t < s]])
  ExceptT.mk (Session.PURE_REWRITE_CONV [r1, r2, r3] tm)
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 35
unsafe def dest_binop_op (tm : term) : Except String (term × term × term) :=
  match (do
    let (f, r) ← dest_comb tm
    let (op, l) ← dest_comb f
    Except.ok (l, r, op) : Except String (term × term × term)) with
  | .ok v => .ok v
  | .error _ => .error "dest_binop_op"
#eval IO.println "<fun>"

#eval phrase 36
unsafe def forall_thm : thm := keep "forall_thm" fun _ => (do
  prove ([[!P. (!x. P x) <=> ~ (?x. ~ P x)]]) (MESON_TAC [])
  : ExceptT String IO thm).run
unsafe def or_exists_conv (tm : term) : IO (Except String thm) :=
  Session.PURE_REWRITE_CONV [OR_EXISTS_THM] tm
unsafe def triv_exists_conv (tm : term) : IO (Except String thm) :=
  Session.REWR_CONV EXISTS_SIMP tm
unsafe def push_exists_conv (tm : term) : IO (Except String thm) :=
  Session.REWR_CONV RIGHT_EXISTS_AND_THM tm
unsafe def not_tm : term := [[(~)]]
unsafe def or_tm : term := [[(\/)]]
unsafe def t_tm : term := [[T]]
unsafe def f_tm : term := [[F]]
#eval (do IO.println (← HolCore.Printer.string_of_thm forall_thm)
          IO.println "<fun>"
          IO.println "<fun>"
          IO.println "<fun>"
          IO.println s!"`{← HolCore.Printer.string_of_term not_tm}`"
          IO.println s!"`{← HolCore.Printer.string_of_term or_tm}`"
          IO.println s!"`{← HolCore.Printer.string_of_term t_tm}`"
          IO.println s!"`{← HolCore.Printer.string_of_term f_tm}`" : IO Unit)

#eval phrase 37
unsafe def LIFT_QELIM_CONV
    (afn_conv : List term → term → IO (Except String thm))
    (nfn_conv : term → IO (Except String thm))
    (qfn_conv : List term → term → IO (Except String thm))
    (fm0 : term) : IO (Except String thm) :=
  ((fun fm => ((fun t => (qelift_conv (HolCore.Kernel.frees fm) t).run) THENC QE_SIMPLIFY_CONV) fm) fm0)
where
  qelift_conv (vars : List term) (fm : term) : ExceptT String IO thm := do
    if fm == t_tm || fm == f_tm then pure (HolCore.Kernel.REFL fm)
    else if is_neg fm then
      let thm1 ← qelift_conv vars (← liftExcept (dest_neg fm))
      HolLight.MK_COMB (HolCore.Kernel.REFL not_tm, thm1)
    else if is_conj fm || is_disj fm || is_imp fm || is_iff fm then
      let (p, q, op) ← liftExcept (dest_binop_op fm)
      let thm1 ← qelift_conv vars p
      let thm2 ← qelift_conv vars q
      HolLight.MK_COMB (← HolLight.MK_COMB (HolCore.Kernel.REFL op, thm1), thm2)
    else if is_forall fm then
      let (x, p) ← liftExcept (dest_forall fm)
      let nex_thm ← HolLight.BETA_RULE (← liftExcept (ISPEC (← liftExcept (mk_abs x p)) forall_thm))
      let elim_thm ← qelift_conv vars (← liftExcept (mk_exists x (← liftExcept (mk_neg p))))
      HolLight.TRANS nex_thm (← HolLight.MK_COMB (HolCore.Kernel.REFL not_tm, elim_thm))
    else if is_exists fm then
      let (x, p) ← liftExcept (dest_exists fm)
      let thm1 ← qelift_conv (x :: vars) p
      let thm1a ← HolLight.MK_EXISTS x thm1
      let thm2 ← ExceptT.mk (nfn_conv (← liftExcept (HolCore.Equal.rhs (concl thm1))))
      let thm2a ← HolLight.MK_EXISTS x thm2
      let djs := disjuncts (← liftExcept (HolCore.Equal.rhs (concl thm2)))
      let djthms ← djs.mapM (fun d => qelim x vars d)
      let thm3 ← eitOr djthms
      let split_ex_thm ← HolLight.GSYM (← ExceptT.mk (or_exists_conv (← liftExcept (HolCore.Equal.lhs (concl thm3)))))
      let thm3a ← HolLight.TRANS split_ex_thm thm3
      HolLight.TRANS (← HolLight.TRANS thm1a thm2a) thm3a
    else
      ExceptT.mk (afn_conv vars fm)
  eitOr : List thm → ExceptT String IO thm
    | [] => throw "end_itlist"
    | [t] => pure t
    | h :: t => do HolLight.MK_COMB (← HolLight.MK_COMB (HolCore.Kernel.REFL or_tm, h), (← eitOr t))
  qelim (x : term) (vars : List term) (p : term) : ExceptT String IO thm := do
    let cjs := conjuncts p
    let (ycjs, ncjs) := partition (fun c => HolCore.Lib.mem x (HolCore.Kernel.frees c)) cjs
    if ycjs == [] then ExceptT.mk (triv_exists_conv (← liftExcept (mk_exists x p)))
    else if ncjs == [] then ExceptT.mk (qfn_conv vars (← liftExcept (mk_exists x p)))
    else
      let mkEq ← ExceptT.mk (mk_eq : IO _)
      let th1 ← HolLight.CONJ_ACI_RULE (← liftExcept (mkEq (p,
                  (← liftExcept (mk_conj (← liftExcept (list_mk_conj ncjs)) (← liftExcept (list_mk_conj ycjs)))))))
      let th2 ← HolLight.CONV_RULE (HolLight.RAND_CONV (fun t => push_exists_conv t)) (← HolLight.MK_EXISTS x th1)
      let (t1, t2) ← liftExcept (dest_comb (← liftExcept (rand (concl th2))))
      HolLight.TRANS th2 (← HolLight.AP_TERM t1 (← ExceptT.mk (qfn_conv vars t2)))
#eval IO.println "<fun>"

#eval phrase 38
unsafe def QELIM_DLO_CONV (tm : term) : IO (Except String thm) :=
  ((LIFT_QELIM_CONV AFN_DLO_CONV
      ((fun t => (CNNF_CONV LFN_DLO_CONV) t) THENC Session.DNF_CONV)
      (fun _v => DLOBASIC_CONV)) THENC (Session.REWRITE_CONV [])) tm
#eval IO.println "<fun>"

#eval phrase 39
/- ---------------------------------------------------------------------- -/
/-  Test                                                                  -/
/- ---------------------------------------------------------------------- -/
unsafe def tests : List term := keep "tests" fun _ => [
  [[!x y. ?z. z < x /\ z < y]],
  [[?z. x < x /\ z < y]],
  [[?z. x < z /\ z < y]],
  [[!x. x < a ==> x < b]],
  [[!a b. (!x. (x < a) <=> (x < b)) <=> (a = b)]], -- long time
  [[!x. ?y. x < y]],
  [[!x y z. x < y /\ y < z ==> x < z]],
  [[!x y. x < y \/ (x = y) \/ y < x]],
  [[!x y. x < y \/ (x = y) \/ y < x]],
  [[?x y. x < y /\ y < x]],
  [[!x y. ?z. z < x /\ x < y]],
  [[!x y. ?z. z < x /\ z < y]],
  [[!x y. x < y ==> ?z. x < z /\ z < y]],
  [[!x y. ~(x = y) ==> ?u. u < x /\ (y < u \/ x < y)]],
  [[?x. x = x:real]],
  [[?x.(x = x) /\ (x = y)]],
  [[?z. x < z /\ z < y]],
  [[?z. x <= z /\ z <= y]],
  [[?z. x < z /\ z <= y]],
  [[!x y z. ?u. u < x /\ u < y /\ u < z]],
  [[!y. x < y /\ y < z ==> w < z]],
  [[!x y . x < y]],
  [[?z. z < x /\ x < y]],
  [[!a b. (!x. x < a ==> x < b) <=> (a <= b)]],
  [[!x. x < a ==> x < b]],
  [[!x. x < a ==> x <= b]],
  [[!a b. ?x. ~(x = a) \/ ~(x = b) \/ (a = b:real)]],
  [[!x y. x <= y \/ x > y]],
  [[!x y. x <= y \/ x < y]]
]
#eval (do
  let parts ← tests.mapM (fun t => do pure ("`" ++ (← HolCore.Printer.string_of_term t) ++ "`"))
  IO.println ("[" ++ "; ".intercalate parts ++ "]") : IO Unit)

#eval phrase 40
#eval (do
  let results ← tests.mapM (fun t => do
    match ← HolCore.Lib.time QELIM_DLO_CONV t with
    | .ok th => pure (toString th)
    | .error e => pure s!"ERR: {e}")
  IO.println ("[" ++ "; ".intercalate results ++ "]") : IO Unit)

end HolExamples.DLO
