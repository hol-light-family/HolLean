/- File: HolExamples/Mizar.lean
Translation of HOL Light's Examples/mizar.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolExamples.Common
open HolCore.Kernel Session HolLight.Syntax HolExamples
open HolCore.Preterm (preterm pretype dpty)
open HolCore.Parser (lexcode ParserM pmapM pseqM porM paM ppossiblyM mkCtx parse_preterm
  parse_pretype install_parser pfirstM plistofM pelistofM pnothingM pmapME liftP PErr lex)
open scoped HolLight
namespace HolExamples.Mizar

-- ========================================================================= --
-- Mizar-style proofs integrated with the HOL goalstack.                     --
--                                                                           --
--       John Harrison, University of Cambridge Computer Laboratory          --
--                                                                           --
--            (c) Copyright, University of Cambridge 1998                    --
-- ========================================================================= --

#eval phrase 1
unsafe def old_parse_term : String → term := keep "old_parse_term" fun _ =>
  fun s => match unsafeIO (HolCore.Parser.parse_term s) with
           | .ok (.ok t) => t
           | _ => panic! "old_parse_term"
#eval IO.println "<fun>"

/-- The kernel's `Except String`-valued rules, named unambiguously. -/
abbrev kEQ_MP := HolCore.Kernel.EQ_MP
abbrev kSYM := HolCore.Equal.SYM
abbrev kGSYM := HolCore.Equal.GSYM
abbrev kAP_TERM := HolCore.Equal.AP_TERM
abbrev kAP_THM := HolCore.Equal.AP_THM
abbrev kBETA_CONV := HolCore.Equal.BETA_CONV
unsafe def kGEN := Session.GEN
unsafe def kMP := Session.MP
abbrev kmk_abs := HolCore.Kernel.mk_abs
abbrev kPINST := HolCore.Bool.PINST

-- ------------------------------------------------------------------------- --
-- This version of CHOOSE is more convenient to "itlist".                    --
-- ------------------------------------------------------------------------- --

#eval phrase 2
unsafe def IMP_CHOOSE_RULE_pth : thm := keep "IMP_CHOOSE_RULE_pth" fun _ =>
  match unsafeIO ((do
      let tac := Session.GEN_REWRITE_TAC
          (HolLight.RAND_CONV o HolLight.LAND_CONV o HolLight.RAND_CONV)
          [(← ExceptT.mk (HolLight.GSYM Session.ETA_AX))] THEN
        Session.REWRITE_TAC [Session.LEFT_IMP_EXISTS_THM]
      let goal ← ExceptT.mk (HolCore.Parser.parse_term "(!x:A. P x ==> Q) ==> ((?) P ==> Q)")
      ExceptT.mk (Session.prove goal tac)
      : ExceptT String IO thm).run) with
    | .ok (.ok t) => t
    | _ => panic! "IMP_CHOOSE_RULE: pth"
unsafe def IMP_CHOOSE_RULE (v : term) (th : thm) : Except String thm := do
  let P : term := [[P:A->bool]]
  let Q : term := [[Q:bool]]
  let pth := IMP_CHOOSE_RULE_pth
  let (ant, _con) ← HolCore.Basics.dest_imp (concl th)
  let pred ← kmk_abs v ant
  let tm := concl th
  let q ← rand tm
  let th1 ← kBETA_CONV (← mk_comb pred v)
  let th2 ← kPINST [(type_of v, aty)] [(pred, P), (q, Q)] pth
  let rr ← rator (← rator tm)
  let th3 ← kAP_THM (← kAP_TERM rr th1) q
  let th4 ← kGEN v (← kEQ_MP (← kSYM th3) th)
  kMP th2 th4
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- Some preterm operations we need.                                          --
-- ------------------------------------------------------------------------- --

#eval phrase 3
unsafe def split_ppair : preterm → List preterm
  | .Combp (.Combp (.Varp "," _) ptm1) ptm2 => ptm1 :: (split_ppair ptm2)
  | ptm => [ptm]
#eval IO.println "<fun>"

#eval phrase 4
unsafe def pmk_conj : preterm × preterm → preterm
  | (ptm1, ptm2) => .Combp (.Combp (.Varp "/\\" dpty) ptm1) ptm2
#eval IO.println "<fun>"

#eval phrase 5
unsafe def pmk_exists : preterm × preterm → preterm
  | (v, ptm) => .Combp (.Varp "?" dpty) (.Absp v ptm)
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- Typecheck a preterm into a term in an environment of (typed) variables.   --
-- ------------------------------------------------------------------------- --

#eval phrase 6
unsafe def typecheck_in_env (env : List term) (ptm : preterm) : Except String term :=
  let penv := HolCore.Lib.itlist
    (fun v acc => match HolCore.Kernel.dest_var v with
                  | .ok (n, ty) => (n, HolCore.Preterm.pretype_of_type ty) :: acc
                  | .error _ => acc)
    env []
  match unsafeIO ((do HolCore.Preterm.term_of_preterm (← HolCore.Preterm.retypecheck penv ptm)).run) with
  | .ok r => r
  | .error e => .error (toString e)
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- Converts a labelled preterm (using "and"s) into a single conjunction.     --
-- ------------------------------------------------------------------------- --

#eval phrase 7
unsafe def delabel {α : Type} (lfs : List (α × preterm)) : preterm :=
  (HolCore.Lib.end_itlist (fun a b => pmk_conj (a, b)) (List.map Prod.snd lfs)).toOption.getD
    (.Varp "" dpty)
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- These special constants are replaced by useful bits when encountered:     --
-- ------------------------------------------------------------------------- --

#eval phrase 8
unsafe def thesis : thm := keep "thesis" fun _ => new_definition [[thesis = F]]
#eval thesis

#eval phrase 9
unsafe def antecedent : thm := keep "antecedent" fun _ => new_definition [[antecedent = F]]
#eval antecedent

#eval phrase 10
unsafe def contradiction : thm := keep "contradiction" fun _ => new_definition [[contradiction = F]]
#eval contradiction

#eval phrase 11
unsafe def iter_rhs : thm := keep "iter_rhs" fun _ => new_definition [[... = @x:A. F]]
#eval iter_rhs

-- ------------------------------------------------------------------------- --
-- This function performs the replacement, and typechecks in current env.    --
--                                                                           --
-- The replacement of "..." is done specially, since it also adds a "then".  --
-- ------------------------------------------------------------------------- --

#eval phrase 12
unsafe def mizarate_atm : term := keep "mizarate_atm" fun _ => old_parse_term "antecedent"
unsafe def mizarate_ttm : term := keep "mizarate_ttm" fun _ => old_parse_term "thesis"
unsafe def mizarate_ctm : term := keep "mizarate_ctm" fun _ => old_parse_term "contradiction"
unsafe def mizarate_ftm : term := keep "mizarate_ftm" fun _ => old_parse_term "F"
unsafe def mizarate_filter_env (fvs : List term) : List term :=
  let env1 := (fvs.map (fun v => (dest_var v).toOption)).filterMap id
  let sizes := env1.map
    (fun (v, _) => (v, (env1.filter (fun (w, _) => w == v)).length))
  let env2 := env1.filter (fun (v, _) => (HolCore.Lib.assoc v sizes).toOption == some 1)
  env2.map (fun (n, ty) => mk_var n ty)
unsafe def mizarate_goal_lconsts (gl : HolCore.Tactics.goal) : List term :=
  let (asl, w) := gl
  HolCore.Lib.itlist (fun p acc => HolCore.Lib.union (frees (concl p.2)) acc) asl (frees w)
unsafe def mizarate_term (gl : HolCore.Tactics.goal) (ptm : preterm) : Except String term := do
  let (_asl, w) := gl
  let lconsts := mizarate_goal_lconsts gl
  let tm ← typecheck_in_env (mizarate_filter_env lconsts) ptm
  let ant := match HolCore.Basics.dest_imp w with
             | .ok (a, _) => a
             | .error _ => mizarate_atm
  match unsafeIO ((do
      let f ← ExceptT.mk (HolCore.Basics.subst
        [(w, mizarate_ttm), (ant, mizarate_atm), (mizarate_ftm, mizarate_ctm)])
      ExceptT.mk (f tm) : ExceptT String IO term).run) with
  | .ok r => r
  | .error e => .error (toString e)
#eval do
  let _ := mizarate_atm; let _ := mizarate_ttm; let _ := mizarate_ctm; let _ := mizarate_ftm
  IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- The following is occasionally useful as a hack.                           --
-- ------------------------------------------------------------------------- --

#eval phrase 13
/-- `GEN_REWRITE_CONV ONCE_DEPTH_CONV ths THENC
    GENERAL_REWRITE_CONV true TOP_DEPTH_CONV (basic_net()) []` -/
unsafe def LIMITED_ONCE_REWRITE_CONV (ths : List thm) : HolCore.Equal.ioconv :=
  let c1 : HolCore.Equal.ioconv := Session.GEN_REWRITE_CONV HolLight.ONCE_DEPTH_CONV ths
  let c2 : HolCore.Equal.ioconv := fun tm => do
    match ← (HolCore.Simp.GENERAL_REWRITE_CONV Session.sessionB true HolLight.TOP_DEPTH_CONV
             (← Session.basic_net) [] : IO (Except String HolCore.Equal.ioconv)) with
    | .error e => return .error e
    | .ok c => c tm
  HolLight.thenc_ c1 c2
unsafe def LIMITED_REWRITE_CONV (n : Nat) (ths : List thm) (tm : term) : IO (Except String thm) := do
  let lorc := LIMITED_ONCE_REWRITE_CONV ths
  let step (th : thm) : IO (Except String thm) :=
    (HolCore.Simp.convRuleIO (HolLight.RAND_CONV lorc) th : IO (Except String thm))
  -- funpow n (CONV_RULE(RAND_CONV(LIMITED_ONCE_REWRITE_CONV ths))) (REFL tm)
  let rec fp (k : Nat) (th : thm) : IO (Except String thm) := do
    match k with
    | 0 => return .ok th
    | k+1 => match ← step th with
             | .error e => return .error e
             | .ok th' => fp k th'
  fp n (HolCore.Kernel.REFL tm)
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- The default prover.                                                       --
-- ------------------------------------------------------------------------- --

#eval phrase 14
unsafe def DEFAULT_PROVER (ths : List thm) (tm : term) : IO (Except String thm) := ExceptT.run do
  -- FREEZE_THENL fn ths x
  let FREEZE_THENL (fn : List thm → term → IO (Except String thm)) (ths : List thm) (x : term) :
      ExceptT String IO thm := do
    let ths' := ths.map (fun th => (HolCore.Kernel.ASSUME (concl th)).toOption.getD th)
    let th ← ExceptT.mk (fn ths' x)
    liftExcept (HolCore.Lib.itlistM (fun a b => HolCore.Equal.PROVE_HYP a b) ths th)
  -- REWRITE_PROVER ths tm
  let REWRITE_PROVER (ths : List thm) (tm : term) : IO (Except String thm) := ExceptT.run do
    if ths.length < 2 then
      liftExcept (Session.EQT_ELIM (← ExceptT.mk (LIMITED_REWRITE_CONV 3 ths tm)))
    else
      let ths' := ths.tail
      let th' ← ExceptT.mk (HolCore.Simp.convRuleIO (fun t => LIMITED_REWRITE_CONV 4 ths' t) ths.head!)
      liftExcept (Session.EQT_ELIM (← ExceptT.mk (LIMITED_REWRITE_CONV 4 (th' :: ths') tm)))
  let sths := HolCore.Lib.itlist (fun th acc => HolCore.Lib.union (Session.CONJUNCTS th) acc) ths []
  HolLight.tryWith
    (ExceptT.mk (Session.TAC_PROOF (((([] : List (String × thm)), tm))) (Session.MAP_FIRST Session.MATCH_ACCEPT_TAC sths)))
    (HolLight.tryWith
      (ExceptT.mk (FREEZE_THENL REWRITE_PROVER ths tm))
      (ExceptT.mk (Session.TAC_PROOF (((([] : List (String × thm)), tm))) (Session.GEN_MESON_TAC 0 30 1 ths))))
#eval IO.println "<fun>"

#eval phrase 15
unsafe def default_prover : IO.Ref (List thm → term → IO (Except String thm)) :=
  keep "default_prover" fun _ => unsafeBaseIO (IO.mkRef DEFAULT_PROVER)
#eval IO.println "{contents = <fun>}"

#eval phrase 16
unsafe def prover_list : IO.Ref (List (String × (List thm → term → IO (Except String thm)))) :=
  keep "prover_list" fun _ => unsafeBaseIO (IO.mkRef [("rewriting",
    (fun (ths : List thm) (tm : term) => ExceptT.run (do
      liftExcept (Session.EQT_ELIM (← ExceptT.mk (Session.REWRITE_CONV ths tm))))))])
#eval do
  let l ← prover_list.get
  let body := ", ".intercalate (l.map (fun (p : String × _) => s!"(\"{p.1}\", <fun>)"))
  IO.println ("{contents = [" ++ body ++ "]}")

-- ------------------------------------------------------------------------- --
--    "arithmetic",(fun ths tm ->                                            --
--                    let tm' = itlist (curry mk_imp o concl) ths tm in      --
--                    let th = REAL_ARITH tm' in                             --
--                    rev_itlist (C MP) ths th);;                            --
-- ------------------------------------------------------------------------- --

-- ------------------------------------------------------------------------- --
-- Produce a "default" label for various constructs where applicable.        --
-- ------------------------------------------------------------------------- --

#eval phrase 17
unsafe def default_assumptions : IO.Ref Bool :=
  keep "default_assumptions" fun _ => unsafeBaseIO (IO.mkRef false)
#eval do
  let b ← default_assumptions.get
  IO.println ("{contents = " ++ (if b then "true" else "false") ++ "}")

#eval phrase 18
unsafe def mklabel (s : String) : IO String := do
  if s == "" && (← default_assumptions.get) then pure "*" else pure s
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- Augment assumptions, throwing away an *unnamed* previous step.            --
-- ------------------------------------------------------------------------- --

#eval phrase 19
unsafe def augments (labs : List String) (th : thm) (asl : List (String × thm)) :
    IO (Except String (List (String × thm))) := ExceptT.run do
  let augment (nw : String × thm) (asl : List (String × thm)) : List (String × thm) :=
    if asl == [] then [nw]
    else if asl.head!.1 == "" then nw :: asl.tail
    else nw :: asl
  let (ths, thl) ← liftExcept (HolCore.Lib.nsplit (fun t => Session.CONJ_PAIR t) labs.tail th)
  let labs' ← labs.mapM (fun s => mklabel s)
  let zipped ← liftExcept (HolCore.Lib.zip labs' (ths ++ [thl]))
  pure (HolCore.Lib.itlist augment zipped asl)
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- Wrapper for labels in justification list (use K for preproved theorems).  --
-- ------------------------------------------------------------------------- --

#eval phrase 20
unsafe def L (s : String) (asl : List (String × thm)) : Except String thm :=
  if s == "" then .ok asl.head!.2 else HolCore.Lib.assoc s asl
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- Perform justification, given asl and target.                              --
-- ------------------------------------------------------------------------- --

#eval phrase 21
unsafe def JUSTIFY (jdata : String × List (List (String × thm) → Except String thm))
    (asl : List (String × thm)) (tm : term) : IO (Except String thm) := ExceptT.run do
  let (prover, tlist) := jdata
  let xthms ← liftExcept (tlist.mapM (fun f => f asl))
  let proof_fn : List thm → term → IO (Except String thm) ←
    if prover == "" then default_prover.get
    else do
      let pl ← prover_list.get
      liftExcept (HolCore.Lib.assoc prover pl)
  let ithms := (asl.filter (fun p => p.1 == "*")).map Prod.snd
  ExceptT.mk (proof_fn (xthms ++ ithms) tm)
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- Either do justification or split off subproof then call ttac with result. --
-- ------------------------------------------------------------------------- --

#eval phrase 22
unsafe def JUSTIFY_THEN (wtm : term)
    (jdata : String × List (List (String × thm) → Except String thm))
    (ttac : HolCore.Tactics.thm_tactic) (gl : HolCore.Tactics.goal) :
    IO (Except String HolCore.Tactics.goalstate) := do
  let (pr, _tls) := jdata
  let (asl, _w) := gl
  if pr == "proof" then
    Session.SUBGOAL_THEN wtm ttac gl
  else
    match ← JUSTIFY jdata asl wtm with
    | .error e => return .error e
    | .ok wth => ttac wth gl
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- Utilise a conclusion.                                                     --
-- ------------------------------------------------------------------------- --

#eval phrase 23
unsafe def MIZAR_CONCLUSION_TAC : HolCore.Tactics.thm_tactic :=
  fun th gl => ExceptT.run do
    let t_tm ← ExceptT.mk (HolCore.Parser.parse_term "T")
    -- CONJ_ASSOC_RULE = EQT_ELIM o GEN_REWRITE_RULE RAND_CONV [EQT_INTRO(SPEC_ALL EQ_REFL)]
    --                   o PURE_REWRITE_CONV[GSYM CONJ_ASSOC]
    let CONJ_ASSOC_RULE (tm : term) : ExceptT String IO thm := do
      let gca ← HolLight.GSYM Session.CONJ_ASSOC
      let th1 ← ExceptT.mk (Session.PURE_REWRITE_CONV [gca] tm)
      let sae ← HolLight.SPEC_ALL Session.EQ_REFL
      let eqi ← HolLight.EQT_INTRO sae
      let th2 ← HolLight.GEN_REWRITE_RULE HolLight.RAND_CONV [eqi] th1
      HolLight.EQT_ELIM th2
    let (asl, w) := gl
    let cjs := HolCore.Basics.conjuncts (concl th)
    let (cjs1, cjs2) ← liftExcept (HolCore.Lib.chop_list cjs.length (HolCore.Basics.conjuncts w))
    if cjs2 == [] then
      let eqtm := HolCore.Kernel.safe_mk_eq (concl th) w
      let th' ← liftExcept (HolCore.Kernel.EQ_MP (← CONJ_ASSOC_RULE eqtm) th)
      let just : HolCore.Tactics.justification := fun i _ =>
        pure (HolCore.Drule.INSTANTIATE i th')
      pure (Session.null_meta, [(asl, t_tm)], just)
    else
      let w1 ← liftExcept (HolCore.Bool.list_mk_conj cjs1)
      let w2 ← liftExcept (HolCore.Bool.list_mk_conj cjs2)
      let w12 ← liftExcept (HolCore.Bool.mk_conj w1 w2)
      let eqtm1 := HolCore.Kernel.safe_mk_eq (concl th) w1
      let th' ← liftExcept (HolCore.Kernel.EQ_MP (← CONJ_ASSOC_RULE eqtm1) th)
      let eqtmw := HolCore.Kernel.safe_mk_eq w w12
      let wth ← CONJ_ASSOC_RULE eqtmw
      ExceptT.mk ((Session.SUBST1_TAC wth THEN Session.CONJ_TAC THENL
        [Session.ACCEPT_TAC th', Session.ALL_TAC]) gl)
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- Transitivity chain stuff; store a list of useful transitivity theorems.   --
-- ------------------------------------------------------------------------- --

#eval phrase 24
unsafe def mizar_transitivity_net : IO.Ref (HolCore.Nets.net (thm → IO (Except String thm))) :=
  keep "mizar_transitivity_net" fun _ => unsafeBaseIO (IO.mkRef HolCore.Nets.empty_net)
/-- Render the ref as OCaml's toplevel prints `ref empty_net`. -/
unsafe def renderNetRef (nt : HolCore.Nets.net (thm → IO (Except String thm))) : String :=
  let (.Netnode r) := nt
  let vnet := match r.vnet with | none => "None" | some _ => "Some(...)"
  let tips := if r.tips.isEmpty then "[]" else "[...]"
  "{contents = Netnode {vnet = " ++ vnet ++ "; cnets = <abstr>; lcnets = <abstr>; " ++
    "lnets = <abstr>; tips = " ++ tips ++ "}}"
#eval do
  let nt ← mizar_transitivity_net.get
  IO.println (renderNetRef nt)

#eval phrase 25
unsafe def add_mizar_transitivity_theorem (th : thm) : IO (Except String Unit) := ExceptT.run do
  let (_vs, bod) := HolCore.Basics.strip_forall (concl th)
  let (pat, _con) ← liftExcept (HolCore.Basics.dest_imp bod)
  let nt ← mizar_transitivity_net.get
  let nt' ← ExceptT.mk (HolCore.Nets.enter' [] (pat, Session.MATCH_MP th) nt)
  mizar_transitivity_net.set nt'
#eval IO.println "<fun>"

#eval phrase 26
unsafe def TRANSITIVITY_CHAIN {α : Type} (th1 th2 : thm) (ttac : thm → IO (Except String α)) :
    IO (Except String α) := ExceptT.run do
  let tm1 := concl th1
  let tm2 := concl th2
  let th ←
    if is_eq tm1 then do
      -- EQ_MP (SYM (AP_THM (AP_TERM (rator(rator tm2)) th1) (rand tm2))) th2
      let rr ← liftExcept (rator (← liftExcept (rator tm2)))
      let apt ← liftExcept (kAP_TERM rr th1)
      let apthm ← liftExcept (kAP_THM apt (← liftExcept (rand tm2)))
      liftExcept (kEQ_MP (← liftExcept (kSYM apthm)) th2)
    else if is_eq tm2 then do
      -- EQ_MP (AP_TERM (rator tm1) th2) th1
      let apt ← liftExcept (kAP_TERM (← liftExcept (rator tm1)) th2)
      liftExcept (kEQ_MP apt th1)
    else do
      let th12 ← liftExcept (Session.CONJ th1 th2)
      let nt ← mizar_transitivity_net.get
      let rules : List (thm → IO (Except String thm)) := HolCore.Nets.lookup (concl th12) nt
      ExceptT.mk (HolCore.Lib.tryfindM (fun rule => rule th12) rules)
  ExceptT.mk (ttac th)
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- Perform terminal or initial step.                                         --
-- ------------------------------------------------------------------------- --

#eval phrase 27
unsafe def MIZAR_SUBSTEP_TAC (labs : List String) (thm_ : thm) : HolCore.Tactics.tactic :=
  fun (asl, w) => do
    match ← augments labs thm_ asl with
    | .error e => return .error e
    | .ok asl' =>
      let just : HolCore.Tactics.justification := fun _ ths =>
        match ths with
        | [th] => pure (HolCore.Equal.PROVE_HYP thm_ th)
        | _ => pure (.error "")
      return .ok (Session.null_meta, [(asl', w)], just)
#eval IO.println "<fun>"

#eval phrase 28
unsafe def MIZAR_BISTEP_TAC (termflag : Bool) (labs : List String) (jth : thm) :
    HolCore.Tactics.tactic :=
  if termflag then
    MIZAR_SUBSTEP_TAC labs jth THEN MIZAR_CONCLUSION_TAC jth
  else
    MIZAR_SUBSTEP_TAC labs jth
#eval IO.println "<fun>"

#eval phrase 29
unsafe def MIZAR_STEP_TAC (termflag : Bool) (lfs : List (String × preterm))
    (jdata : String × List (List (String × thm) → Except String thm)) :
    HolCore.Tactics.tactic := fun (asl, w) => do
  let (pr, tls) := jdata
  match mizarate_term (asl, w) (delabel lfs) with
  | .error e => return .error e
  | .ok tm =>
    let isDots : Bool :=
      match (do pure ((← HolCore.Kernel.dest_const (← HolCore.Equal.lhand tm)).1 == "...")) with
      | .ok b => b | .error _ => false
    if isDots then
      match ← (do
        let thp := asl.head!.2
        let lhd ← liftExcept (rand (concl thp))
        let rr ← liftExcept (rator (← liftExcept (rator tm)))
        let c1 ← liftExcept (mk_comb rr lhd)
        let tm' ← liftExcept (mk_comb c1 (← liftExcept (rand tm)))
        pure (thp, tm') : ExceptT String IO (thm × term)).run with
      | .error e => return .error e
      | .ok (thp, tm') =>
        JUSTIFY_THEN tm' (pr, tls)
          (fun th gl' => TRANSITIVITY_CHAIN thp th
            (fun cth => MIZAR_BISTEP_TAC termflag (lfs.map Prod.fst) cth gl'))
          (asl, w)
    else
      JUSTIFY_THEN tm (pr, tls)
        (MIZAR_BISTEP_TAC termflag (lfs.map Prod.fst)) (asl, w)
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- Perform an "end": finish the trivial goal.                                --
-- ------------------------------------------------------------------------- --

#eval phrase 30
unsafe def MIZAR_END_TAC : HolCore.Tactics.tactic := Session.ACCEPT_TAC Session.TRUTH
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- Perform "assume <lform>"                                                  --
-- ------------------------------------------------------------------------- --

#eval phrase 31
unsafe def MIZAR_ASSUME_f_tm : term := keep "MIZAR_ASSUME_f_tm" fun _ => old_parse_term "F"
unsafe def MIZAR_ASSUME_CONTRA_HACK (th : thm) : IO (Except String thm) := ExceptT.run do
  let taut ← ExceptT.mk (Session.TAUT (← HolCore.Parser.parse_term "(~p ==> F) <=> p"))
  ExceptT.mk (HolCore.Simp.convRuleIO (Session.REWR_CONV taut) th)
unsafe def MIZAR_ASSUME_TAC (lfs : List (String × preterm)) : HolCore.Tactics.tactic :=
  fun (asl, w) => do
    let f_tm := MIZAR_ASSUME_f_tm
    match mizarate_term (asl, w) (delabel lfs) with
    | .error e => return .error e
    | .ok tm =>
      let isNeg : Bool :=
        match (do pure (aconv (← HolCore.Basics.dest_neg tm) w)) with
        | .ok b => b | .error _ => false
      if isNeg then
        match ← (augments (lfs.map Prod.fst) ((HolCore.Kernel.ASSUME tm).toOption.getD Session.TRUTH) asl) with
        | .error e => return .error e
        | .ok asl' =>
          let just : HolCore.Tactics.justification := fun i ths =>
            match ths with
            | [th] => do
              match HolCore.Drule.instantiate i tm with
              | .error e => pure (.error e)
              | .ok itm => match Session.DISCH itm th with
                           | .error e => pure (.error e)
                           | .ok dth => MIZAR_ASSUME_CONTRA_HACK dth
            | _ => pure (.error "")
          return .ok (Session.null_meta, [(asl', f_tm)], just)
      else
        let isImpAnt : Bool :=
          match (do pure (aconv tm (← HolCore.Basics.dest_imp w).1)) with
          | .ok b => b | .error _ => false
        if isImpAnt then
          match ← (augments (lfs.map Prod.fst) ((HolCore.Kernel.ASSUME tm).toOption.getD Session.TRUTH) asl) with
          | .error e => return .error e
          | .ok asl' =>
            match rand w with
            | .error e => return .error e
            | .ok rw =>
              let just : HolCore.Tactics.justification := fun i ths =>
                match ths with
                | [th] => match HolCore.Drule.instantiate i tm with
                          | .error e => pure (.error e)
                          | .ok itm => pure (Session.DISCH itm th)
                | _ => pure (.error "")
              return .ok (Session.null_meta, [(asl', rw)], just)
        else return .error "MIZAR_ASSUME_REF: Bad thesis"
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- Perform "let <v1>,...,<vn> [be <type>]"                                   --
-- ------------------------------------------------------------------------- --

#eval phrase 32
unsafe def MIZAR_LET_TAC (vtys : List preterm × List hol_type) : HolCore.Tactics.tactic :=
  fun (asl, w) => do
    let (vlist, tys) := vtys
    match ← (do
      let ty ← if tys == [] then
                 do pure (type_of (← liftExcept (HolCore.Basics.dest_forall w)).1)
               else pure tys.head!
      let pty := HolCore.Preterm.pretype_of_type ty
      let mk_varb (v : preterm) : ExceptT String IO term := do
        HolCore.Preterm.term_of_preterm (← ExceptT.mk (HolCore.Preterm.retypecheck [] (.Typing v pty)))
      let vs ← vlist.mapM mk_varb
      pure vs : ExceptT String IO (List term)).run with
    | .error e => return .error e
    | .ok vs => (Session.MAP_EVERY Session.X_GEN_TAC vs) (asl, w)
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- Perform "take <tm>"                                                       --
-- ------------------------------------------------------------------------- --

#eval phrase 33
unsafe def MIZAR_TAKE_TAC (ptm : preterm) : HolCore.Tactics.tactic :=
  fun (asl, w) => do
    match ← (do
      let dw ← liftExcept (HolCore.Basics.dest_exists w)
      let ptm' : preterm := .Typing ptm (HolCore.Preterm.pretype_of_type (type_of dw.1))
      liftExcept (mizarate_term (asl, w) ptm') : ExceptT String IO term).run with
    | .error e => return .error e
    | .ok tm => (Session.EXISTS_TAC tm) (asl, w)
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- Perform "suffices to prove <form> by <just>".                             --
-- ------------------------------------------------------------------------- --

#eval phrase 34
unsafe def MIZAR_SUFFICES_TAC (new0 : List preterm)
    (jdata : String × List (List (String × thm) → Except String thm)) :
    HolCore.Tactics.tactic := fun (asl, w) => do
  match ← (do
    let conj ← liftExcept (HolCore.Lib.end_itlist (fun a b => pmk_conj (a, b)) new0)
    let nw ← liftExcept (mizarate_term (asl, w) conj)
    let imp ← liftExcept (HolCore.Bool.mk_imp nw w)
    pure (nw, imp) : ExceptT String IO (term × term)).run with
  | .error e => return .error e
  | .ok (nw, imp) =>
    JUSTIFY_THEN imp jdata
      (fun jth gl' => do
        let (asl', _w') := gl'
        let just : HolCore.Tactics.justification := fun i ths =>
          match ths with
          | [th] => do
            match Session.INSTANTIATE_ALL i jth with
            | .error e => pure (.error e)
            | .ok ijth => pure (Session.MP ijth th)
          | _ => pure (.error "")
        pure (.ok (Session.null_meta, [(asl', nw)], just)))
      (asl, w)
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- Perform "set <lform>"                                                     --
-- ------------------------------------------------------------------------- --

#eval phrase 35
unsafe def MIZAR_SET_TAC (labptm : String × preterm) : HolCore.Tactics.tactic :=
  fun (asl, w) => do
    let (lab, ptm) := labptm
    match ← (do
      let tm ← liftExcept (mizarate_term (asl, w) ptm)
      let (v, t) ← liftExcept (dest_eq tm)
      let mkex ← liftExcept (HolCore.Bool.mk_exists v (HolCore.Kernel.safe_mk_eq t v))
      let ex ← liftExcept (Session.EXISTS (mkex, t) (HolCore.Kernel.REFL t))
      let lb ← mklabel lab
      pure (v, t, ex, lb) : ExceptT String IO (term × term × thm × String)).run with
    | .error e => return .error e
    | .ok (_v, _t, ex, lb) =>
      (Session.CHOOSE_THEN (fun th =>
        Session.SUBST_ALL_TAC th THEN
        (Session.LABEL_TAC lb oT kSYM) th) ex) (asl, w)
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- Perform "consider <vars> such that <lform> by <just>".                    --
-- ------------------------------------------------------------------------- --

#eval phrase 36
unsafe def MIZAR_CONSIDER_TAC (vars0 : List preterm) (lfs : List (String × preterm))
    (jdata : String × List (List (String × thm) → Except String thm)) :
    HolCore.Tactics.tactic := fun (asl, w) => do
  match ← (do
    let ptm := HolCore.Lib.itlist (fun v acc => pmk_exists (v, acc)) vars0 (delabel lfs)
    let etm ← liftExcept (mizarate_term (asl, w) ptm)
    let (vars, tm) ← liftExcept (HolCore.Lib.nsplit (fun t => HolCore.Basics.dest_exists t) vars0 etm)
    pure (etm, vars, tm) : ExceptT String IO (term × List term × term)).run with
  | .error e => return .error e
  | .ok (etm, vars, tm) =>
    JUSTIFY_THEN etm jdata
      (fun jth gl' => do
        let (asl0, _w0) := gl'
        match ← (augments (lfs.map Prod.fst) ((HolCore.Kernel.ASSUME tm).toOption.getD Session.TRUTH) asl0) with
        | .error e => pure (.error e)
        | .ok asl' =>
          let just : HolCore.Tactics.justification := fun i ths =>
            match ths with
            | [th] => ExceptT.run do
              let itm ← liftExcept (HolCore.Drule.instantiate i tm)
              let dth ← liftExcept (Session.DISCH itm th)
              let chained ← liftExcept (HolCore.Lib.itlistM (fun v t => IMP_CHOOSE_RULE v t) vars dth)
              liftExcept (Session.MP chained jth)
            | _ => pure (.error "")
          pure (.ok (Session.null_meta, [(asl', _w0)], just)))
      (asl, w)
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- Perform "given <terms> such that <lform>".                                --
-- ------------------------------------------------------------------------- --

#eval phrase 37
unsafe def MIZAR_GIVEN_TAC (vars0 : List preterm) (lfs : List (String × preterm)) :
    HolCore.Tactics.tactic := fun (asl, w) => do
  match ← (do
    let ant ← liftExcept (Prod.fst <$> HolCore.Basics.dest_imp w)
    let (gvars, _gbod) ← liftExcept (HolCore.Lib.nsplit (fun t => HolCore.Basics.dest_exists t) vars0 ant)
    let tvars ← liftExcept (do
      let pairs ← HolCore.Lib.zip vars0 gvars
      pairs.mapM (fun (p, v) =>
        do pure (preterm.Typing p (HolCore.Preterm.pretype_of_type (← HolCore.Kernel.dest_var v).2))))
    let ptm := HolCore.Lib.itlist (fun v acc => pmk_exists (v, acc)) tvars (delabel lfs)
    let etm ← liftExcept (mizarate_term (asl, w) ptm)
    let (vars, tm) ← liftExcept (HolCore.Lib.nsplit (fun t => HolCore.Basics.dest_exists t) vars0 etm)
    pure (ant, etm, vars, tm) : ExceptT String IO (term × term × List term × term)).run with
  | .error e => return .error e
  | .ok (ant, etm, vars, tm) =>
    let okThesis : Bool := aconv ant etm
    if okThesis then do
      match ← (augments (lfs.map Prod.fst) ((HolCore.Kernel.ASSUME tm).toOption.getD Session.TRUTH) asl) with
      | .error e => return .error e
      | .ok asl' =>
        match rand w with
        | .error e => return .error e
        | .ok rw =>
          let just : HolCore.Tactics.justification := fun i ths =>
            match ths with
            | [th] => ExceptT.run do
              let itm ← liftExcept (HolCore.Drule.instantiate i tm)
              let dth ← liftExcept (Session.DISCH itm th)
              let chained ← liftExcept (HolCore.Lib.itlistM (fun v t => IMP_CHOOSE_RULE v t) vars dth)
              let aant ← liftExcept (HolCore.Kernel.ASSUME ant)
              let mpd ← liftExcept (Session.MP chained aant)
              liftExcept (Session.DISCH ant mpd)
            | _ => pure (.error "")
          return .ok (Session.null_meta, [(asl', rw)], just)
    else return .error "MIZAR_GIVEN_TAC: Bad thesis"
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- Initialize a case split.                                                  --
-- ------------------------------------------------------------------------- --

#eval phrase 38
unsafe def MIZAR_PER_CASES_TAC
    (jdata : String × List (List (String × thm) → Except String thm)) :
    HolCore.Tactics.tactic := fun (asl, w) => do
  let just : HolCore.Tactics.justification := fun _ ths =>
    match ths with
    | [th] => ExceptT.run do
      let ghyps := HolCore.Lib.itlist (fun p acc => HolCore.Lib.union (hyp p.2) acc) asl []
      let rogues := HolCore.Lib.subtract (hyp th) ghyps
      if rogues == [] then pure th
      else if rogues.tail == [] then do
        let thm_ ← ExceptT.mk (JUSTIFY jdata asl rogues.head!)
        liftExcept (HolCore.Equal.PROVE_HYP thm_ th)
      else throw "MIZAR_PER_CASES_ATAC: Too many suppositions"
    | _ => pure (.error "")
  return .ok (Session.null_meta, [(asl, w)], just)
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- Perform a case split. NB! This tactic is not "valid" in the LCF sense.    --
-- We could make it so, but that would force classical logic!                --
-- ------------------------------------------------------------------------- --

#eval phrase 39
unsafe def MIZAR_SUPPOSE_TAC (lfs : List (String × preterm)) : HolCore.Tactics.tactic :=
  fun (asl, w) => do
    match mizarate_term (asl, w) (delabel lfs) with
    | .error e => return .error e
    | .ok asm =>
      let ghyps := HolCore.Lib.itlist (fun p acc => HolCore.Lib.union (hyp p.2) acc) asl []
      match ← (augments (lfs.map Prod.fst) ((HolCore.Kernel.ASSUME asm).toOption.getD Session.TRUTH) asl) with
      | .error e => return .error e
      | .ok asl' =>
        let just : HolCore.Tactics.justification := fun _ ths =>
          match ths with
          | [th1, th2] => ExceptT.run do
            let hyp1 := hyp th1
            let hyp2 := hyp th2
            let asm1 := HolCore.Lib.subtract hyp1 ghyps
            let asm2 := HolCore.Lib.subtract hyp2 ghyps
            if asm1 == [] then pure th1 else if asm2 == [] then pure th2
            else if asm1.tail == [] && asm2.tail == [] then do
              let d ← liftExcept (HolCore.Bool.mk_disj asm1.head! asm2.head!)
              let ad ← liftExcept (HolCore.Kernel.ASSUME d)
              liftExcept (Session.DISJ_CASES ad th1 th2)
            else throw "MIZAR_SUPPOSE_TAC: Too many suppositions"
          | _ => pure (.error "")
        return .ok (Session.null_meta, [(asl', w), (asl, w)], just)
#eval IO.println "<fun>"

#eval phrase 40
unsafe def MIZAR_SUPPOSE_REF (lfs : List (String × preterm)) : HolCore.Tactics.refinement :=
  fun gs => do
    match ← Session.by_ (Session.TRY MIZAR_END_TAC) gs with
    | .error e => return .error e
    | .ok gs' => Session.by_ (MIZAR_SUPPOSE_TAC lfs) gs'
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- Terminate a case split.                                                   --
-- ------------------------------------------------------------------------- --

#eval phrase 41
unsafe def MIZAR_RAW_ENDCASE_pthRef : IO.Ref thm :=
  keep "MIZAR_RAW_ENDCASE_pthRef" fun _ => unsafeBaseIO (IO.mkRef Session.TRUTH)
unsafe def MIZAR_RAW_ENDCASE_p : term := keep "MIZAR_RAW_ENDCASE_p" fun _ => old_parse_term "p:bool"
unsafe def MIZAR_RAW_ENDCASE_TAC : HolCore.Tactics.tactic := fun (_asl, w) => do
  let pth ← MIZAR_RAW_ENDCASE_pthRef.get
  match ← (do
    let ith ← liftExcept (HolCore.Kernel.INST [(w, MIZAR_RAW_ENDCASE_p)] pth)
    liftExcept (Session.UNDISCH ith) : ExceptT String IO thm).run with
  | .error e => return .error e
  | .ok th =>
    let just : HolCore.Tactics.justification := fun _ _ => pure (.ok th)
    return .ok (Session.null_meta, [], just)
#eval do
  -- let pth = ITAUT `F ==> p` : the search traces print here, as in HOL Light.
  let fimp ← (HolCore.Parser.parse_term "F ==> p" : IO (Except String term))
  match fimp with
  | .error e => IO.println e
  | .ok fimp =>
    match ← (Session.ITAUT fimp : IO (Except String thm)) with
    | .error e => IO.println e
    | .ok pth => MIZAR_RAW_ENDCASE_pthRef.set pth
  IO.println "<fun>"


#eval phrase 42
unsafe def MIZAR_ENDCASE_REF : HolCore.Tactics.refinement := fun gs => do
  match ← Session.by_ (Session.TRY MIZAR_END_TAC) gs with
  | .error e => return .error e
  | .ok gs' => Session.by_ MIZAR_RAW_ENDCASE_TAC gs'
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- Parser-processor for textual version of Mizar proofs.                     --
-- ------------------------------------------------------------------------- --

/-- `by tac`, as a refinement (parse_step treatments build these). -/
unsafe def byR (t : HolCore.Tactics.tactic) : HolCore.Tactics.refinement := Session.by_ t

#eval phrase 43
unsafe def mizar_word_list : List String :=
  ["assume", "take", "set", "given", "such", "that",
   "proof", "end", "consider", "suffices", "to", "show",
   "per", "cases", "endcase", "suppose", "be",
   "then", "thus", "hence", "by", "so"]
unsafe def add_mizar_words : Unit → IO Unit := fun _ => HolCore.Printer.reserve_words mizar_word_list
unsafe def subtract_mizar_words : Unit → IO Unit := fun _ => HolCore.Printer.unreserve_words mizar_word_list
#eval (do IO.println "<fun>"; IO.println "<fun>" : IO Unit)

#eval phrase 44
unsafe def parse_preform : ParserM preterm :=
  pmapM parse_preterm (fun ptm => .Typing ptm (.Ptycon "bool" []))
#eval IO.println "<fun>"

#eval phrase 45
unsafe def parse_fulltype : ParserM hol_type :=
  fun c inp => do
    match ← (liftP parse_pretype) c inp with
    | .error e => return .error e
    | .ok (pty, rst) =>
      match ← (HolCore.Preterm.type_of_pretype pty).run with
      | .error _ => return .error .noparse
      | .ok ty => return .ok (ty, rst)
#eval IO.println "<fun>"

#eval phrase 46
unsafe def parse_ident : ParserM String := fun _ inp => do
  match inp with
  | (.Ident n) :: rst => return .ok (n, rst)
  | _ => return .error .noparse
#eval IO.println "<fun>"

#eval phrase 47
unsafe def parse_string : ParserM String := fun _ inp => do
  match inp with
  | (.Ident n) :: rst => return .ok (n, rst)
  | (.Resword n) :: rst => return .ok (n, rst)
  | _ => return .error (.fail "Match_failure")
#eval IO.println "<fun>"

#eval phrase 48
unsafe def parse_lform : String → ParserM (String × preterm) := fun oldlab => fun c inp => do
  match inp with
  | (.Ident n) :: (.Resword ":") :: rst =>
      if oldlab == "" then parse_lform n c rst
      else return .error (.fail "Too many labels")
  | _ =>
      match ← parse_preform c inp with
      | .error e => return .error e
      | .ok (fm, rst) => return .ok ((oldlab, fm), rst)
#eval IO.println "<fun>"

#eval phrase 49
unsafe def parse_lforms (oldlab : String) : ParserM (List (String × preterm)) :=
  plistofM (parse_lform oldlab) (paM (.Resword "and")) "labelled formula"
#eval IO.println "<fun>"

#eval phrase 50
unsafe def parse_just (tlink : Bool) :
    ParserM (String × List (List (String × thm) → Except String thm)) := fun c inp => do
  if inp == [] then
    if tlink then return .ok (("", [L ""]), inp)
    else return .ok (("", []), inp)
  else
    match inp with
    | (.Resword "by") :: rest0 =>
      match ← parse_string c rest0 with
      | .error e => return .error e
      | .ok (pot, rem) =>
        if rem == [] || (rem.head? != some (.Ident ",") && rem.head? != some (.Ident "with")) then
          let pl ← prover_list.get
          if HolCore.Lib.can (fun k => HolCore.Lib.assoc k pl) pot then
            return .ok ((pot, if tlink then [L ""] else []), rem)
          else
            return .ok (("", if tlink then [L "", L pot] else [L pot]), rem)
        else if rem.head? == some (.Ident ",") then
          match ← (plistofM parse_string (paM (.Ident ",")) "theorem name") c rem.tail with
          | .error e => return .error e
          | .ok (oths, rst) =>
            let ths := if tlink then "" :: pot :: oths else pot :: oths
            return .ok (("", ths.map L), rst)
        else
          match ← (plistofM parse_string (paM (.Ident ",")) "theorem name") c rem.tail with
          | .error e => return .error e
          | .ok (oths, rst) =>
            let ths := if tlink then "" :: oths else oths
            return .ok ((pot, ths.map L), rst)
    | (.Resword "proof") :: rest0 => return .ok (("proof", []), rest0)
    | _ =>
      if tlink then return .ok (("", [L ""]), inp)
      else return .ok (("", []), inp)
#eval IO.println "<fun>"

#eval phrase 51
unsafe def parse_step : Bool → ParserM HolCore.Tactics.refinement := fun tlink => fun c inp =>
  (pfirstM [
    -- assume
    pmapM (pseqM (paM (.Resword "assume")) (parse_lforms ""))
      (fun x => byR (MIZAR_ASSUME_TAC x.2)),
    -- let <v..> [be <ty>]
    pmapM (pseqM (pseqM (paM (.Resword "let")) (pmapM parse_preterm split_ppair))
            (ppossiblyM (pmapM (pseqM (paM (.Resword "be")) parse_fulltype) Prod.snd)))
      (fun x => let ((_, vnames), ty) := x; byR (MIZAR_LET_TAC (vnames, ty))),
    -- take <tm>
    pmapM (pseqM (paM (.Resword "take")) parse_preterm)
      (fun x => byR (MIZAR_TAKE_TAC x.2)),
    -- set <lform>
    pmapM (pseqM (paM (.Resword "set")) (parse_lforms ""))
      (fun x => HolCore.Lib.itlist (fun lf acc => fun gs => do
                   match ← byR (MIZAR_SET_TAC lf) gs with
                   | .error e => return .error e
                   | .ok gs' => acc gs')
                 x.2 (fun gs => pure (.ok gs))),
    -- consider <vars> such that <lforms> by <just>
    pmapM (pseqM (pseqM (pseqM (pseqM (pseqM (paM (.Resword "consider"))
            (pmapM parse_preterm split_ppair)) (paM (.Resword "such")))
            (paM (.Resword "that"))) (parse_lforms "")) (parse_just tlink))
      (fun x => let (((((_, vars), _), _), lf), jst) := x; byR (MIZAR_CONSIDER_TAC vars lf jst)),
    -- given <vars> such that <lforms>
    pmapM (pseqM (pseqM (pseqM (pseqM (paM (.Resword "given"))
            (pmapM parse_preterm split_ppair)) (paM (.Resword "such")))
            (paM (.Resword "that"))) (parse_lforms ""))
      (fun x => let ((((_, vars), _), _), lf) := x; byR (MIZAR_GIVEN_TAC vars lf)),
    -- suffices to show <lforms> by <just>
    pmapM (pseqM (pseqM (pseqM (pseqM (paM (.Resword "suffices"))
            (paM (.Resword "to"))) (paM (.Resword "show"))) (parse_lforms "")) (parse_just tlink))
      (fun x => let ((((_, _), _), lf), jst) := x; byR (MIZAR_SUFFICES_TAC (lf.map Prod.snd) jst)),
    -- per cases by <just>
    pmapM (pseqM (pseqM (paM (.Resword "per")) (paM (.Resword "cases"))) (parse_just tlink))
      (fun x => let ((_, _), jst) := x; byR (MIZAR_PER_CASES_TAC jst)),
    -- suppose <lforms>
    pmapM (pseqM (paM (.Resword "suppose")) (parse_lforms ""))
      (fun x => MIZAR_SUPPOSE_REF x.2),
    -- endcase
    pmapM (paM (.Resword "endcase")) (fun _ => MIZAR_ENDCASE_REF),
    -- end
    pmapM (paM (.Resword "end")) (fun _ => byR MIZAR_END_TAC),
    -- then <step>
    pmapM (pseqM (paM (.Resword "then")) (parse_step true)) Prod.snd,
    -- so <step>
    pmapM (pseqM (paM (.Resword "so")) (parse_step true)) Prod.snd,
    -- hence <lforms> by <just>
    pmapM (pseqM (pseqM (paM (.Resword "hence")) (parse_lforms "")) (parse_just true))
      (fun x => let ((_, lf), jst) := x; byR (MIZAR_STEP_TAC true lf jst)),
    -- thus <lforms> by <just>
    pmapM (pseqM (pseqM (paM (.Resword "thus")) (parse_lforms "")) (parse_just tlink))
      (fun x => let ((_, lf), jst) := x; byR (MIZAR_STEP_TAC true lf jst)),
    -- <lforms> by <just>
    pmapM (pseqM (parse_lforms "") (parse_just tlink))
      (fun x => let (lf, jst) := x; byR (MIZAR_STEP_TAC false lf jst))
  ]) c inp
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- From now on, quotations evaluate to preterms.                             --
-- ------------------------------------------------------------------------- --

#eval phrase 52
unsafe def run_steps (lexemes : List lexcode) : IO HolCore.Tactics.goalstack := do
  -- compose_steps : builds the composite refinement.
  let rec compose_steps (lexemes : List lexcode) (gs : HolCore.Tactics.goalstate) :
      IO (Except String HolCore.Tactics.goalstate) := do
    if lexemes == [] then return .ok gs
    else
      let c ← mkCtx
      match ← parse_step false c lexemes with
      | .error e => return .error (HolCore.Parser.perrMsg e)
      | .ok (rf, rest) =>
        match ← rf gs with
        | .error e => return .error e
        | .ok gs' =>
          if rest != [] && rest.head? == some (.Resword ";") then compose_steps rest.tail gs'
          else compose_steps rest gs'
  Session.refine (fun gs => compose_steps lexemes gs)
#eval IO.println "<fun>"

-- ------------------------------------------------------------------------- --
-- Include some theorems.                                                    --
-- ------------------------------------------------------------------------- --

unsafe def do_add_mizar_trans (ths : List thm) : IO Unit := do
  for th in ths do
    match ← add_mizar_transitivity_theorem th with
    | .ok _ => pure ()
    | .error e => throw (IO.userError e)

#eval phrase 53
#eval do_add_mizar_trans [Session.LE_TRANS, Session.LT_TRANS, Session.LET_TRANS, Session.LTE_TRANS]

#eval phrase 54
#eval do_add_mizar_trans [Session.INT_LE_TRANS, Session.INT_LT_TRANS, Session.INT_LET_TRANS, Session.INT_LTE_TRANS]

#eval phrase 55
#eval do_add_mizar_trans [Session.REAL_LE_TRANS, Session.REAL_LT_TRANS, Session.REAL_LET_TRANS, Session.REAL_LTE_TRANS]

#eval phrase 56
#eval do_add_mizar_trans [Session.SUBSET_TRANS, Session.PSUBSET_TRANS, Session.PSUBSET_SUBSET_TRANS, Session.SUBSET_PSUBSET_TRANS]

-- ------------------------------------------------------------------------- --
-- Simple example: Knaster-Tarski fixpoint theorem.                          --
-- ------------------------------------------------------------------------- --

#eval phrase 57
#eval (add_mizar_words () : IO Unit)

#eval phrase 58
#eval (HolCore.Preterm.hide_constant "<=" : IO Unit)

-- (*** Set up goal ***)

#eval phrase 59
#eval Session.g [[!f. (!x y. x <= y /\ y <= x ==> (x = y)) /\
     (!x y z. x <= y /\ y <= z ==> x <= z) /\
     (!x y. x <= y ==> f x <= f y) /\
     (!X. ?s:A. (!x. x IN X ==> s <= x) /\
                (!s'. (!x. x IN X ==> s' <= x) ==> s' <= s))
     ==> ?x. f x = x]]

-- (*** Start parsing quotations as Mizar directives ***)

#eval phrase 60
unsafe def parse_term_mizar (s : String) : IO HolCore.Tactics.goalstack := do
  let c ← mkCtx
  match lex c (HolCore.Lib.explode s) with
  | .error e => throw (IO.userError (HolCore.Parser.perrMsg e))
  | .ok toks => run_steps toks
#eval IO.println "<fun>"

-- (*** Label the external facts needed ***)

#eval phrase 61
#eval Session.e (Session.LABEL_TAC "IN_ELIM_THM" Session.IN_ELIM_THM)

#eval phrase 62
#eval Session.e (Session.LABEL_TAC "BETA_THM" Session.BETA_THM)

-- (*** The proof itself ***)

#eval phrase 63
#eval parse_term_mizar "let f be A->A;
  assume L:antecedent;
  antisymmetry: (!x y. x <= y /\\ y <= x ==> (x = y)) by L;
  transitivity: (!x y z. x <= y /\\ y <= z ==> x <= z) by L;
  monotonicity: (!x y. x <= y ==> f x <= f y) by L;
  least_upper_bound:
      (!X. ?s:A. (!x. x IN X ==> s <= x) /\\
                 (!s'. (!x. x IN X ==> s' <= x) ==> s' <= s)) by L;
  set Y_def: Y = {b | f b <= b};
  Y_thm: !b. b IN Y <=> f b <= b by Y_def,IN_ELIM_THM,BETA_THM;
  consider a such that
      lub: (!x. x IN Y ==> a <= x) /\\
           (!a'. (!x. x IN Y ==> a' <= x) ==> a' <= a)
      by least_upper_bound;
  take a;
  !b. b IN Y ==> f a <= b
  proof
    let b be A;
    assume b_in_Y: b IN Y;
    then L0: f b <= b by Y_thm;
    a <= b by b_in_Y, lub;
    so f a <= f b by monotonicity;
    hence f a <= b by L0, transitivity;
    end;
  so Part1: f(a) <= a by lub;
  so f(f(a)) <= f(a) by monotonicity;
  so f(a) IN Y by Y_thm;
  so a <= f(a) by lub;
  hence thesis by Part1, antisymmetry;
end"

-- (*** Get the theorem ***)

#eval phrase 64
#eval Session.top_thm

-- ------------------------------------------------------------------------- --
-- Back to normal.                                                           --
-- ------------------------------------------------------------------------- --

#eval phrase 65
unsafe def parse_term_restored : String → term := old_parse_term
#eval IO.println "<fun>"

end HolExamples.Mizar
