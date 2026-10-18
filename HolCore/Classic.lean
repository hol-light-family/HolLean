/- File: Classic.lean
Extensional, classical reasoning with AC starts now!
Original       John Harrison, University of Cambridge Computer Laboratory
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Lean4 translation by Chris Walton 2026
-/

import HolCore.Bool
import HolCore.Equal
import HolCore.Drule
import HolCore.Tactics
import HolCore.Itab
import HolCore.Simp
import HolCore.Parser
import HolCore.Theorems
import HolCore.IndDefs

open HolCore.Kernel HolCore.Basics HolCore.Lib HolCore.Bool HolCore.Equal
     HolCore.Drule HolCore.Tactics HolCore.Itab HolCore.Simp HolCore.Parser
     HolCore.Theorems HolCore.IndDefs

namespace HolCore.Classic

/- ---------------------------------------------------------------------- -/
/- Indefinite descriptor (giving AC).                                     -/
/- ---------------------------------------------------------------------- -/

/-- `is_select`: is `tm` a `@`-binder term? -/
def is_select : term → Bool := is_binder "@"

/-- `dest_select`: destruct a `@`-binder term into `(var, body)`. -/
def dest_select : term → Except String (term × term) := dest_binder "@"

/-- `mk_select`: build a `@`-binder term (applied to the pair `(var, body)`). -/
def mk_select : IO (Except String ((term × term) → Except String term)) := mk_binder "@"

/-- Parse a term in the `ExceptT String IO` monad. -/
private def pt (s : String) : ExceptT String IO term := parse_term s

/- ---------------------------------------------------------------------- -/
/- Conditional (`COND` / if-then-else) term operations.                   -/
/- ---------------------------------------------------------------------- -/

/-- `is_cond tm`: is `tm` a `COND` application `COND b x y`? -/
def is_cond (tm : term) : Bool :=
  match (do dest_const (← rator (← rator (← rator tm))) : Except String (String × hol_type)) with
  | .ok (nm, _) => nm == "COND"
  | .error _ => false

/-- `mk_cond (b, x, y)` = `if b then x else y`. -/
def mk_cond (b x y : term) : IO (Except String term) := do
  match ← mk_const "COND" [(type_of x, aty)] with
  | .error _ => return failwith "mk_cond"
  | .ok c => return (do mk_comb (← mk_comb (← mk_comb c b) x) y)

/-- `dest_cond tm` = `(b, (x, y))` for `if b then x else y`. -/
def dest_cond (tm : term) : Except String (term × (term × term)) := do
  let (tm1, y) ← dest_comb tm
  let (tm2, x) ← dest_comb tm1
  let (c, b) ← dest_comb tm2
  match dest_const c with
  | .ok (nm, _) => if nm == "COND" then .ok (b, (x, y)) else failwith "dest_cond"
  | .error _ => failwith "dest_cond"

/- ---------------------------------------------------------------------- -/
/- The `class.ml` theorem bundle (proved once by `setupClass`).           -/
/- ---------------------------------------------------------------------- -/

/-- Theorems established by `class.ml`. (Grown stage by stage.) -/
structure ClassThms where
  etaPth        : thm  -- `|- (\x. t x) = t` (for ETA_CONV)
  etaT : term             -- ETA_CONV's `t:A->B` (class.ml 20)
  EQ_EXT        : thm
  FUN_EQ_THM    : thm
  EXISTS_THM    : thm
  selectRulePth : thm  -- `|- (?) P ==> P ((@) P)` (for SELECT_RULE)
  selectConvPth : thm  -- `|- P ((@) P) = (?) P` (for SELECT_CONV)
  SELECT_REFL   : thm
  SELECT_UNIQUE : thm
  EXCLUDED_MIDDLE : thm
  BOOL_CASES_AX : thm
  DE_MORGAN_THM : thm
  NOT_CLAUSES   : thm
  NOT_IMP       : thm
  CONTRAPOS_THM : thm
  ccontrPth     : thm  -- `|- (~P ==> F) ==> P`
  contraposConvPth : thm  -- `|- (a ==> b) <=> (~b ==> ~a)`
  refuteF : term          -- REFUTE_THEN's `f_tm = \`F\`` (class.ml 222)
  contraposA : term       -- CONTRAPOS_CONV's `a:bool`
  contraposB : term       -- CONTRAPOS_CONV's `b:bool`
  refuteThenPth : thm  -- `|- p <=> ~p ==> F`
  NOT_EXISTS_THM : thm
  EXISTS_NOT_THM : thm
  NOT_FORALL_THM : thm
  FORALL_NOT_THM : thm
  FORALL_BOOL_THM : thm
  EXISTS_BOOL_THM : thm
  LEFT_FORALL_OR_THM : thm
  RIGHT_FORALL_OR_THM : thm
  LEFT_OR_FORALL_THM : thm
  RIGHT_OR_FORALL_THM : thm
  LEFT_IMP_FORALL_THM : thm
  LEFT_EXISTS_IMP_THM : thm
  RIGHT_IMP_EXISTS_THM : thm
  RIGHT_EXISTS_IMP_THM : thm
  COND_CLAUSES : thm
  COND_EXPAND  : thm
  COND_ID      : thm
  COND_RAND    : thm
  COND_RATOR   : thm
  COND_ABS     : thm
  COND_SWAP    : thm
  MONO_COND    : thm
  COND_ELIM_THM : thm
  denegPth     : thm  -- `|- ~ ~p <=> p`  (for COND_CASES_TAC's DENEG_RULE)
  SKOLEM_THM   : thm
  SKOLEM_THM_GEN : thm
  UNIQUE_SKOLEM_ALT : thm
  UNIQUE_SKOLEM_THM : thm
  COND_CONG    : thm
  COND_EQ_CLAUSE : thm
  bool_INDUCT  : thm
  bool_RECURSION : thm
  deriving Inhabited

/-- `ETA_CONV`: eta-reduce `\x. t x` to `t`. `etaPth = |- (\x. t x) = t`,
    `t = \`t:A->B\``. -/
def ETA_CONV (etaPth : thm) (t : term) (tm : term) : Except String thm := do
  match dest_abs tm with
  | .error _ => failwith "ETA_CONV"
  | .ok (bv, bod) =>
    match dest_comb bod with
    | .error _ => failwith "ETA_CONV"
    | .ok (l, r) =>
      if r == bv && !(vfree_in bv l) then
        TRANS (REFL tm) (← PINST [(type_of bv, aty), (type_of bod, bty)] [(l, t)] etaPth)
      else failwith "ETA_CONV"

/-- `SELECT_RULE`: from `|- ?x. P x` derive `|- P((@) P)`.
    `pth = |- (?) P ==> P((@) P)`, `P = \`P:A->bool\``. -/
def SELECT_RULE (B : BoolThms) (pth : thm) (P : term) (th : thm) : Except String thm :=
  (do let abs ← rand (concl th)
      let ty := type_of (← bndvar abs)
      CONV_RULE BETA_CONV (← B.MP (← PINST [(ty, aty)] [(abs, P)] pth) th)
  ).mapError (fun _ => "SELECT_RULE")

/-- `SELECT_CONV`: rewrite `P((@) P)` to `?x. P x`.
    `pth = |- P((@) P) = (?) P`, `P = \`P:A->bool\``. -/
def SELECT_CONV (pth : thm) (P : term) (tm : term) : Except String thm :=
  (do
  let is_epsok (t : term) : Bool :=
    is_select t &&
      (match dest_select t with
       | .ok (bv, bod) =>
         (match vsubst [(t, bv)] with
          | .ok f => aconv tm (f bod)
          | .error _ => false)
       | .error _ => false)
  let pickeps ← find_term is_epsok tm
  let abs ← rand pickeps
  let ty := type_of (← bndvar abs)
  CONV_RULE (LAND_CONV BETA_CONV) (← PINST [(ty, aty)] [(abs, P)] pth)
  ).mapError (fun _ => "SELECT_CONV")

/- ---------------------------------------------------------------------- -/
/- Classically based tactics. (See also COND_CASES_TAC later on.)         -/
/- ---------------------------------------------------------------------- -/

/-- `BOOL_CASES_TAC p`: case-split on the boolean term `p` (`p<=>T` / `p<=>F`).
    `BOOL_CASES_AX = |- !t. (t<=>T) \/ (t<=>F)`. -/
def BOOL_CASES_TAC (B : BoolThms) (BOOL_CASES_AX : thm) (p : term) : tactic := fun g => do
  match B.SPEC p BOOL_CASES_AX with
  | .error e => return .error e
  | .ok sth => (Tactics.STRUCT_CASES_TAC B sth g : IO (Except String goalstate))

/-- `ASM_CASES_TAC t`: case-split on `t \/ ~t`.
    `EXCLUDED_MIDDLE = |- !t. t \/ ~t`. -/
def ASM_CASES_TAC (B : BoolThms) (EXCLUDED_MIDDLE : thm) (t : term) : tactic := fun g => do
  match B.SPEC t EXCLUDED_MIDDLE with
  | .error e => return .error e
  | .ok sth => (Tactics.DISJ_CASES_TAC B sth g : IO (Except String goalstate))

/- ---------------------------------------------------------------------- -/
/- Set up a reasonable tautology checker for classical logic.             -/
/- ---------------------------------------------------------------------- -/

/- ---------------------------------------------------------------------- -/
/- Redefine TAUT to freeze in the rewrites including COND.                -/
/- ---------------------------------------------------------------------- -/

/-- `TAUT tm`: classical tautology checker. Repeatedly propositional-rewrites,
    then boolean-case-splits on a chosen boolean variable-subterm of the goal. -/
def TAUT (B : BoolThms) (BOOL_CASES_AX : thm) (tm : term) : IO (Except String thm) := do
  let PROP_REWRITE_TAC := Simp.REWRITE_TAC B []
  let REWRITE_TAC := Simp.REWRITE_TAC B
  -- RTAUT_TAC = PROP_REWRITE_TAC THEN W(... BOOL_CASES_TAC o hd o sort free_in
  --   o find_terms ok o snd); the pick reads the goal *after* PROP_REWRITE.
  let pickTac : tactic := fun (asl, w) => do
    let ok (t : term) : Bool :=
      type_of t == bool_ty && can (find_term is_var) t && free_in t w
    match sort free_in (find_terms ok w) with
    | [] => return .error "RTAUT_TAC: no candidate"
    | p :: _ =>
      -- OCaml: `(fun t1 t2 -> t1 THEN t2) (REWRITE_TAC[]) o BOOL_CASES_TAC o ...`
      -- builds `REWRITE_TAC[] THEN BOOL_CASES_TAC p` (REWRITE_TAC runs FIRST).
      (THEN B (REWRITE_TAC []) (BOOL_CASES_TAC B BOOL_CASES_AX p) (asl, w)
        : IO (Except String goalstate))
  let RTAUT_TAC : tactic := THEN B PROP_REWRITE_TAC pickTac
  let TAUT_TAC : tactic :=
    THEN B (REPEAT B (ORELSE (Tactics.GEN_TAC B) (Tactics.CONJ_TAC B)))
      (REPEAT B RTAUT_TAC)
  -- `try prove(tm,TAUT_TAC) with Failure _ -> failwith "TAUT `...`: cannot solve"`
  match ← (Tactics.prove B tm TAUT_TAC : IO (Except String thm)) with
  | .ok th => return .ok th
  | .error _ =>
    let s ← HolCore.Printer.string_of_term tm
    return .error s!"TAUT `{s}`: cannot solve"

/- ---------------------------------------------------------------------- -/
/- Some classically based rules.                                          -/
/- ---------------------------------------------------------------------- -/

/-- `CCONTR tm th`: classical contradiction. `pth = |- (~P ==> F) ==> P`,
    `Pv = \`P:bool\``. From `th = A, ~tm |- F` derive `A |- tm`. -/
def CCONTR (B : BoolThms) (pth : thm) (Pv : term) (tm : term) (th : thm) : Except String thm :=
  (do let tm' ← mk_neg tm
      B.MP (← INST [(tm, Pv)] pth) (← B.DISCH tm' th)
  ).mapError (fun _ => "CCONTR")

/-- `CONTRAPOS_CONV tm`: `(P ==> Q) <=> (~Q ==> ~P)`. `pth = |- (a==>b)<=>(~b==>~a)`. -/
def CONTRAPOS_CONV (pth : thm) (av bv : term) (tm : term) : Except String thm :=
  (do let (P, Q) ← Basics.dest_imp tm
      INST [(P, av), (Q, bv)] pth
  ).mapError (fun _ => "CONTRAPOS_CONV")

/- ---------------------------------------------------------------------- -/
/- A classicalal "refutation" tactic.                                     -/
/- ---------------------------------------------------------------------- -/

/-- `REFUTE_THEN ttac`: classical refutation. `conv = REWR_CONV (|- p <=> ~p ==> F)`,
    `f_tm = \`F\``. -/
def REFUTE_THEN (B : BoolThms) (conv : ioconv) (f_tm : term) (ttac : thm_tactic) : tactic :=
  fun (asl, w) => do
    if w == f_tm then (Tactics.ALL_TAC (asl, w) : IO (Except String goalstate))
    else if is_neg w then (Tactics.DISCH_THEN B ttac (asl, w) : IO (Except String goalstate))
    else (THEN B (Tactics.CONV_TAC B conv) (Tactics.DISCH_THEN B ttac) (asl, w)
           : IO (Except String goalstate))

/- ---------------------------------------------------------------------- -/
/- Tactic for splitting over an arbitrarily chosen conditional.           -/
/- ---------------------------------------------------------------------- -/

/-- The prepared `COND_ELIM_CONV`, built on first use. -/
initialize condElimCache : IO.Ref (Option (thm × ioconv)) ← IO.mkRef none

/-- `COND_ELIM_CONV`: `P (if c then x else y) <=> (c ==> P x) /\ (~c ==> P y)`.
    `COND_ELIM_THM` is the corresponding theorem. -/
def COND_ELIM_CONV (B : BoolThms) (COND_ELIM_THM : thm) : ioconv := fun tm => do
  -- class.ml 403 builds `HIGHER_REWRITE_CONV[COND_ELIM_THM] true` once; the
  -- prepared conversion is cached here, keyed on the theorem.
  match ← condElimCache.get with
  | some (th, c) => if th == COND_ELIM_THM then c tm else build tm
  | none => build tm
where
  build (tm : term) : IO (Except String thm) := do
    match ← Drule.HIGHER_REWRITE_CONV_ths B [COND_ELIM_THM] with
    | .error e => return .error e
    | .ok c => do condElimCache.set (some (COND_ELIM_THM, c true)); c true tm

/-- `COND_CASES_TAC`: split the goal over an arbitrary conditional.
    `denegPth = |- ~ ~p <=> p`. -/
def COND_CASES_TAC (B : BoolThms) (COND_ELIM_THM : thm) (denegPth : thm) : tactic :=
  let DENEG_RULE (th : thm) : IO (Except String thm) :=
    Simp.GEN_REWRITE_RULE B id [denegPth] th
  let br1 : thm_tactic := fun th => fun g => do
    match B.EQT_INTRO th with
    | .error e => return .error e
    | .ok eth => (THEN B (Tactics.ASSUME_TAC B th) (Tactics.SUBST1_TAC B eth) g
                   : IO (Except String goalstate))
  let br2 : thm_tactic := fun th => fun g => do
    match ← (DENEG_RULE th : IO (Except String thm)) with
    | .ok th' =>
      match B.EQT_INTRO th' with
      | .error e => return .error e
      | .ok eth' => (THEN B (Tactics.ASSUME_TAC B th') (Tactics.SUBST1_TAC B eth') g
                      : IO (Except String goalstate))
    | .error _ =>
      match B.EQF_INTRO th with
      | .error e => return .error e
      | .ok fth => (THEN B (Tactics.ASSUME_TAC B th) (Tactics.SUBST1_TAC B fth) g
                     : IO (Except String goalstate))
  THEN B (Tactics.CONV_TAC B (COND_ELIM_CONV B COND_ELIM_THM))
    (THENL B (Tactics.CONJ_TAC B) [Tactics.DISCH_THEN B br1, Tactics.DISCH_THEN B br2])

/-- Establish the `class.ml` theorem layer. -/
def setupClass (B : BoolThms) (T : TheoremThms)
    (ETA_AX SELECT_AX COND_DEF : thm) : ExceptT String IO ClassThms := do
  let prove := Tactics.prove B
  let REWRITE_TAC := Simp.REWRITE_TAC B
  let GEN_TAC := Tactics.GEN_TAC B
  let EQ_TAC := Tactics.EQ_TAC B
  let REFL_TAC := Tactics.REFL_TAC B
  let DISCH_THEN := Tactics.DISCH_THEN B
  let SUBST1_TAC := Tactics.SUBST1_TAC B
  let MATCH_ACCEPT_TAC := Tactics.MATCH_ACCEPT_TAC B
  let MP_TAC := Tactics.MP_TAC B
  let SPEC := B.SPEC
  let MATCH_MP_TAC := Tactics.MATCH_MP_TAC B
  let BETA_TAC := Tactics.BETA_TAC B
  let X_GEN_TAC := Tactics.X_GEN_TAC B
  let GEN_REWRITE_TAC := Simp.GEN_REWRITE_TAC B
  let CHOOSE_THEN := Tactics.CHOOSE_THEN B
  let DISCH_TAC := Tactics.DISCH_TAC B
  let EXISTS_TAC := Tactics.EXISTS_TAC B
  let ACCEPT_TAC := Tactics.ACCEPT_TAC B
  let SIMP_TAC := Simp.SIMP_TAC B
  let CONV_TAC := Tactics.CONV_TAC B
  let STRIP_TAC := Tactics.STRIP_TAC B
  let ASM_REWRITE_TAC := Simp.ASM_REWRITE_TAC B
  -- LAND_CONV o RAND_CONV as an IO conv-combinator: both are total functions on
  -- `ioconv`, so plain `o`; RAND_CONV runs FIRST (innermost).
  let landRand : ioconv → ioconv := Simp.landConvIO o Simp.randConvIO

  -- Eta-axiom, corresponding conversion, and extensionality.
  let etaT ← pt "t:A->B"
  let etaPth ← (prove (← pt "(\\x. (t:A->B) x) = t") (MATCH_ACCEPT_TAC ETA_AX)
                : IO (Except String thm))
  -- EQ_EXT : !(f:A->B) g. (!x. f x = g x) ==> f = g
  let xA ← pt "x:A"
  let xA' ← pt "x:A"
  let EQ_EXT ← (prove (← pt "!(f:A->B) g. (!x. f x = g x) ==> f = g")
      (THEN B (REPEAT B GEN_TAC)
        -- MP_TAC o ABS `x:A` o SPEC `x:A` : SPEC runs FIRST, then ABS, then
        -- MP_TAC.  The two rules are both `Except`-valued so they join with
        -- `oM`; `oT` then hands the result to the thm-tactic.  Each `x:A` is
        -- its own quotation (SPEC's parsed first).
        (THEN B (DISCH_THEN (MP_TAC oT ABS xA' oM SPEC xA))
          (REWRITE_TAC [ETA_AX]))) : IO (Except String thm))
  -- FUN_EQ_THM : !(f:A->B) g. f = g <=> (!x. f x = g x)
  let FUN_EQ_THM ← (prove (← pt "!(f:A->B) g. f = g <=> (!x. f x = g x)")
      (THEN B (REPEAT B GEN_TAC) (THENL B EQ_TAC
        [THEN B (DISCH_THEN SUBST1_TAC) (THEN B GEN_TAC REFL_TAC),
         MATCH_ACCEPT_TAC EQ_EXT])) : IO (Except String thm))

  -- Useful for compatibility. (The old EXISTS_DEF.)
  -- EXISTS_THM : (?) = \P:A->bool. P ((@) P)
  let PAb ← pt "P:A->bool"
  let atP ← pt "((@) P):A"
  let EXISTS_THM ← (prove (← pt "(?) = \\P:A->bool. P ((@) P)")
      (THEN B (MATCH_MP_TAC EQ_EXT) (THEN B BETA_TAC (THEN B (X_GEN_TAC PAb)
        (THEN B (GEN_REWRITE_TAC (fun c => landRand c) [(← liftExcept (GSYM ETA_AX))])
          (THENL B EQ_TAC
            [THEN B (DISCH_THEN (CHOOSE_THEN MP_TAC)) (MATCH_ACCEPT_TAC SELECT_AX),
             THEN B DISCH_TAC (THEN B (EXISTS_TAC atP) (POP_ASSUM ACCEPT_TAC))]))))) : IO (Except String thm))
  -- Rules and so on for the select operator.
  -- SELECT_RULE pth : (?) (P:A->bool) ==> P ((@) P)
  let selectRulePth ← (prove (← pt "(?) (P:A->bool) ==> P ((@) P)")
      (SIMP_TAC [SELECT_AX, ETA_AX]) : IO (Except String thm))
  -- SELECT_CONV pth : (P:A->bool) ((@) P) = (?) P
  let selectConvPth ← (prove (← pt "(P:A->bool) ((@) P) = (?) P")
      (THEN B (REWRITE_TAC [EXISTS_THM]) (THEN B BETA_TAC REFL_TAC)) : IO (Except String thm))
  -- SELECT_CONV as an IO conv (for CONV_TAC): lift the pure conv.
  let SELECT_CONV_io : ioconv := fun t => pure (SELECT_CONV selectConvPth PAb t)
  -- Some basic theorems.
  -- SELECT_REFL : !x:A. (@y. y = x) = x
  let SELECT_REFL ← (prove (← pt "!x:A. (@y. y = x) = x")
      (THEN B GEN_TAC (THEN B (CONV_TAC SELECT_CONV_io)
        (THEN B (EXISTS_TAC (← pt "x:A")) REFL_TAC))) : IO (Except String thm))
  -- SELECT_UNIQUE : !P x. (!y:A. P y = (y = x)) ==> ((@) P = x)
  let SELECT_UNIQUE ← (prove (← pt "!P x. (!y:A. P y = (y = x)) ==> ((@) P = x)")
      (THEN B (REPEAT B STRIP_TAC)
        (THEN B (GEN_REWRITE_TAC (fun c => landRand c) [(← liftExcept (GSYM ETA_AX))])
          (ASM_REWRITE_TAC [SELECT_REFL]))) : IO (Except String thm))
  let _ ← (Simp.extend_basic_rewrites B [SELECT_REFL] : IO (Except String Unit))

  -- Excluded middle & boolean cases
  let SUBGOAL_THEN := Tactics.SUBGOAL_THEN B
  let CONJ_TAC := Tactics.CONJ_TAC B
  let DISJ1_TAC := Tactics.DISJ1_TAC B
  let DISJ2_TAC := Tactics.DISJ2_TAC B
  let STRIP_ASSUME_TAC := Tactics.STRIP_ASSUME_TAC B
  let TRY := Tactics.TRY B
  let FIRST_ASSUM := Tactics.FIRST_ASSUM
  let PURE_ONCE_ASM_REWRITE_TAC := Simp.PURE_ONCE_ASM_REWRITE_TAC B
  let DISJ_CASES_TAC := Tactics.DISJ_CASES_TAC B
  let ITAUT (s : String) : ExceptT String IO thm := do (Itab.ITAUT B (← pt s) : IO (Except String thm))
  -- STRIP_ASSUME_TAC o GSYM   (GSYM runs FIRST; its failure is sequenced inside
  -- the produced tactic, which is what `oT` does).
  let STRIP_ASSUME_GSYM : thm_tactic := STRIP_ASSUME_TAC oT GSYM
  let notTF ← ITAUT "~(T <=> F)"
  let pOrT ← ITAUT "p \\/ T <=> T"
  let fTm ← pt "F"
  let tTm ← pt "T"
  -- Derive excluded middle. The proof is an optimization due to Mark Adams of
  -- the original Diaconescu proof as presented in Beeson's book.
  let EXCLUDED_MIDDLE ← (prove (← pt "!t. t \\/ ~t")
      (THEN B GEN_TAC
        (THENL B (SUBGOAL_THEN
            (← pt "(((@x. (x <=> F) \\/ t) <=> F) \\/ t) /\\ (((@x. (x <=> T) \\/ t) <=> T) \\/ t)")
            (fun mpth => MP_TAC mpth))
          [ -- branch 1: prove the conjunction subgoal
            THEN B (THENL B (THEN B CONJ_TAC (CONV_TAC SELECT_CONV_io))
                            [EXISTS_TAC fTm, EXISTS_TAC tTm])
                   (THEN B DISJ1_TAC REFL_TAC),
            -- branch 2: use it to derive `t \/ ~t`
            THEN B (DISCH_THEN STRIP_ASSUME_GSYM)
              (THEN B (TRY (THEN B DISJ1_TAC (FIRST_ASSUM ACCEPT_TAC)))
                (THEN B DISJ2_TAC (THEN B DISCH_TAC (THEN B (MP_TAC notTF)
                  (THEN B (PURE_ONCE_ASM_REWRITE_TAC [])
                    (ASM_REWRITE_TAC [pOrT]))))) ) ])) : IO (Except String thm))
  let BOOL_CASES_AX ← (prove (← pt "!t. (t <=> T) \\/ (t <=> F)")
      (THEN B GEN_TAC (THEN B (DISJ_CASES_TAC (← liftExcept (B.SPEC (← pt "t:bool") EXCLUDED_MIDDLE)))
        (ASM_REWRITE_TAC []))) : IO (Except String thm))

  -- Classical tautologies + rules
  let TAUT (s : String) : ExceptT String IO thm := do (Classic.TAUT B BOOL_CASES_AX (← pt s) : IO (Except String thm))
  let ONCE_REWRITE_TAC := Simp.ONCE_REWRITE_TAC B
  let UNDISCH_TAC := Tactics.UNDISCH_TAC B
  let POP_ASSUM := Tactics.POP_ASSUM
  -- A few useful classical tautologies.
  let DE_MORGAN_THM ← TAUT "!t1 t2. (~(t1 /\\ t2) <=> ~t1 \\/ ~t2) /\\ (~(t1 \\/ t2) <=> ~t1 /\\ ~t2)"
  let NOT_CLAUSES ← TAUT "(!t. ~ ~t <=> t) /\\ (~T <=> F) /\\ (~F <=> T)"
  let NOT_IMP ← TAUT "!t1 t2. ~(t1 ==> t2) <=> t1 /\\ ~t2"
  let CONTRAPOS_THM ← TAUT "!t1 t2. (~t1 ==> ~t2) <=> (t2 ==> t1)"
  let _ ← (Simp.extend_basic_rewrites B [(← liftExcept (B.CONJUNCT1 NOT_CLAUSES))] : IO (Except String Unit))
  -- rule pths
  let ccontrPth ← TAUT "(~P ==> F) ==> P"
  let contraposA ← pt "a:bool"
  let contraposB ← pt "b:bool"
  let contraposConvPth ← TAUT "(a ==> b) <=> (~b ==> ~a)"
  let refuteF ← pt "F"
  let refuteThenPth ← TAUT "p <=> ~p ==> F"
  -- Infinite de Morgan laws
  let notExP ← pt "~(?x:A. P x)"
  let iffNegLemma ← TAUT "(a <=> ~b) <=> (~a <=> b)"
  let NOT_EXISTS_THM ← (prove (← pt "!P. ~(?x:A. P x) <=> (!x. ~(P x))")
      (THEN B GEN_TAC (THENL B (THEN B EQ_TAC DISCH_TAC)
        [THEN B GEN_TAC (THEN B DISCH_TAC (THEN B (UNDISCH_TAC notExP)
          (THEN B (REWRITE_TAC []) (THEN B (EXISTS_TAC (← pt "x:A")) (POP_ASSUM ACCEPT_TAC))))),
         THEN B (DISCH_THEN (CHOOSE_THEN MP_TAC)) (ASM_REWRITE_TAC [])])) : IO (Except String thm))
  let EXISTS_NOT_THM ← (prove (← pt "!P. (?x:A. ~(P x)) <=> ~(!x. P x)")
      (THEN B (ONCE_REWRITE_TAC [iffNegLemma]) (REWRITE_TAC [NOT_EXISTS_THM])) : IO (Except String thm))
  let NOT_FORALL_THM ← (prove (← pt "!P. ~(!x. P x) <=> (?x:A. ~(P x))")
      (MATCH_ACCEPT_TAC (← liftExcept (GSYM EXISTS_NOT_THM))) : IO (Except String thm))
  let FORALL_NOT_THM ← (prove (← pt "!P. (!x. ~(P x)) <=> ~(?x:A. P x)")
      (MATCH_ACCEPT_TAC (← liftExcept (GSYM NOT_EXISTS_THM))) : IO (Except String thm))
  -- Expand quantification over Booleans.
  let FORALL_BOOL_THM ← (prove (← pt "(!b. P b) <=> P T /\\ P F")
      (THEN B EQ_TAC (THEN B DISCH_TAC (THEN B (ASM_REWRITE_TAC [])
        (THEN B GEN_TAC (THEN B (BOOL_CASES_TAC B BOOL_CASES_AX (← pt "b:bool")) (ASM_REWRITE_TAC [])))))) : IO (Except String thm))
  let boolIffLemma ← TAUT "(~p <=> ~q) ==> (p <=> q)"
  let EXISTS_BOOL_THM ← (prove (← pt "(?b. P b) <=> P T \\/ P F")
      (THEN B (MATCH_MP_TAC boolIffLemma)
        (REWRITE_TAC [DE_MORGAN_THM, NOT_EXISTS_THM, FORALL_BOOL_THM])) : IO (Except String thm))
  -- Universal quantifier and disjunction
  let LEFT_FORALL_OR_THM ← (prove (← pt "!P Q. (!x:A. P x \\/ Q) <=> (!x. P x) \\/ Q")
      (THEN B (REPEAT B GEN_TAC) (THEN B (ONCE_REWRITE_TAC [← TAUT "(a <=> b) <=> (~a <=> ~b)"])
        (REWRITE_TAC [NOT_FORALL_THM, DE_MORGAN_THM, T.LEFT_EXISTS_AND_THM]))) : IO (Except String thm))
  let RIGHT_FORALL_OR_THM ← (prove (← pt "!P Q. (!x:A. P \\/ Q x) <=> P \\/ (!x. Q x)")
      (THEN B (REPEAT B GEN_TAC) (THEN B (ONCE_REWRITE_TAC [← TAUT "(a <=> b) <=> (~a <=> ~b)"])
        (REWRITE_TAC [NOT_FORALL_THM, DE_MORGAN_THM, T.RIGHT_EXISTS_AND_THM]))) : IO (Except String thm))
  let LEFT_OR_FORALL_THM ← (prove (← pt "!P Q. (!x:A. P x) \\/ Q <=> (!x. P x \\/ Q)")
      (MATCH_ACCEPT_TAC (← liftExcept (GSYM LEFT_FORALL_OR_THM))) : IO (Except String thm))
  let RIGHT_OR_FORALL_THM ← (prove (← pt "!P Q. P \\/ (!x:A. Q x) <=> (!x. P \\/ Q x)")
      (MATCH_ACCEPT_TAC (← liftExcept (GSYM RIGHT_FORALL_OR_THM))) : IO (Except String thm))
  -- Implication and quantifiers.
  let LEFT_IMP_FORALL_THM ← (prove (← pt "!P Q. ((!x:A. P x) ==> Q) <=> (?x. P x ==> Q)")
      (THEN B (REPEAT B GEN_TAC) (THEN B (ONCE_REWRITE_TAC [← TAUT "(a <=> b) <=> (~a <=> ~b)"])
        (REWRITE_TAC [NOT_EXISTS_THM, NOT_IMP, T.LEFT_AND_FORALL_THM]))) : IO (Except String thm))
  let LEFT_EXISTS_IMP_THM ← (prove (← pt "!P Q. (?x. P x ==> Q) <=> ((!x:A. P x) ==> Q)")
      (MATCH_ACCEPT_TAC (← liftExcept (GSYM LEFT_IMP_FORALL_THM))) : IO (Except String thm))
  let RIGHT_IMP_EXISTS_THM ← (prove (← pt "!P Q. (P ==> ?x:A. Q x) <=> (?x:A. P ==> Q x)")
      (THEN B (REPEAT B GEN_TAC) (THEN B (ONCE_REWRITE_TAC [← TAUT "(a <=> b) <=> (~a <=> ~b)"])
        (REWRITE_TAC [NOT_EXISTS_THM, NOT_IMP, T.RIGHT_AND_FORALL_THM]))) : IO (Except String thm))
  let RIGHT_EXISTS_IMP_THM ← (prove (← pt "!P Q. (?x:A. P ==> Q x) <=> (P ==> ?x:A. Q x)")
      (MATCH_ACCEPT_TAC (← liftExcept (GSYM RIGHT_IMP_EXISTS_THM))) : IO (Except String thm))
  -- The conditional
  let COND_CLAUSES ← (prove (← pt "!(t1:A) t2. ((if T then t1 else t2) = t1) /\\ ((if F then t1 else t2) = t2)")
      (REWRITE_TAC [COND_DEF]) : IO (Except String thm))
  let _ ← (Simp.extend_basic_rewrites B [COND_CLAUSES] : IO (Except String Unit))
  let cBool ← pt "c:bool"
  let COND_EXPAND ← (prove (← pt "!b t1 t2. (if b then t1 else t2) <=> (~b \\/ t1) /\\ (b \\/ t2)")
      (THEN B (REPEAT B GEN_TAC) (THEN B (BOOL_CASES_TAC B BOOL_CASES_AX (← pt "b:bool")) (REWRITE_TAC []))) : IO (Except String thm))
  let COND_ID ← (prove (← pt "!b (t:A). (if b then t else t) = t")
      (THEN B (REPEAT B GEN_TAC) (THEN B (BOOL_CASES_TAC B BOOL_CASES_AX (← pt "b:bool")) (REWRITE_TAC []))) : IO (Except String thm))
  let COND_RAND ← (prove (← pt "!b (f:A->B) x y. f (if b then x else y) = (if b then f x else f y)")
      (THEN B (REPEAT B GEN_TAC) (THEN B (BOOL_CASES_TAC B BOOL_CASES_AX (← pt "b:bool")) (REWRITE_TAC []))) : IO (Except String thm))
  let COND_RATOR ← (prove (← pt "!b (f:A->B) g x. (if b then f else g) x = (if b then f x else g x)")
      (THEN B (REPEAT B GEN_TAC) (THEN B (BOOL_CASES_TAC B BOOL_CASES_AX (← pt "b:bool")) (REWRITE_TAC []))) : IO (Except String thm))
  let COND_ABS ← (prove (← pt "!b (f:A->B) g. (\\x. if b then f x else g x) = (if b then f else g)")
      (THEN B (REPEAT B GEN_TAC) (THEN B (BOOL_CASES_TAC B BOOL_CASES_AX (← pt "b:bool")) (REWRITE_TAC [ETA_AX]))) : IO (Except String thm))
  let COND_SWAP ← (prove (← pt "!p x y:A. (if ~p then x else y) = (if p then y else x)")
      (THEN B (REPEAT B GEN_TAC) (THEN B (BOOL_CASES_TAC B BOOL_CASES_AX (← pt "p:bool")) (REWRITE_TAC []))) : IO (Except String thm))
  -- Throw monotonicity in.
  let MONO_COND ← (prove (← pt "(A ==> B) /\\ (C ==> D) ==> (if b then A else C) ==> (if b then B else D)")
      (THEN B STRIP_TAC (THEN B (BOOL_CASES_TAC B BOOL_CASES_AX (← pt "b:bool")) (ASM_REWRITE_TAC []))) : IO (Except String thm))
  let COND_ELIM_THM ← (prove (← pt "(P:A->bool) (if c then x else y) <=> (c ==> P x) /\\ (~c ==> P y)")
      (THEN B (BOOL_CASES_TAC B BOOL_CASES_AX cBool) (REWRITE_TAC [])) : IO (Except String thm))
  let denegPth ← TAUT "~ ~ p <=> p"
  -- Skolemization
  let MAP_EVERY := Tactics.MAP_EVERY B
  let CONJUNCTS_THEN := Tactics.CONJUNCTS_THEN B
  let ASSUME_TAC := Tactics.ASSUME_TAC B
  let X_CHOOSE_TAC := Tactics.X_CHOOSE_TAC B
  let COND_CASES_TAC := Classic.COND_CASES_TAC B COND_ELIM_THM denegPth
  let skolemWit ← pt "\\x:A. @y:B. P x y"
  let yx ← pt "(y:A->B) x"
  let SKOLEM_THM ← (prove (← pt "!P. (!x:A. ?y:B. P x y) <=> (?y. !x. P x (y x))")
      (THEN B (THENL B (REPEAT B (ORELSE STRIP_TAC EQ_TAC))
          [THEN B (EXISTS_TAC skolemWit) (THEN B GEN_TAC (THEN B BETA_TAC (CONV_TAC SELECT_CONV_io))),
           EXISTS_TAC yx])
        (POP_ASSUM MATCH_ACCEPT_TAC)) : IO (Except String thm))
  let SKOLEM_THM_GEN ← (prove (← pt "!P R. (!x:A. P x ==> ?y:B. R x y) <=> (?f. !x. P x ==> R x (f x))")
      (REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM]) : IO (Except String thm))
  -- NB: this one is true intutionistically and intensionally.
  let UNIQUE_SKOLEM_ALT ← (prove (← pt "!P:A->B->bool. (!x. ?!y. P x y) <=> ?f. !x y. P x y <=> (f x = y)")
      (THEN B GEN_TAC (REWRITE_TAC [T.EXISTS_UNIQUE_ALT, SKOLEM_THM])) : IO (Except String thm))
  -- UNIQUE_SKOLEM_THM (the big one)
  -- and this one intuitionistically and extensionally.
  -- class.ml 445-457 parses its quotations right to left: `x:A` (457),
  -- the SUBGOAL_THEN term, `f:A->B`, `[x; y1; y2]` (450, right to left),
  -- then the `x:A` of 449 and of 448.
  let uX457 ← pt "x:A"
  let uFunEq ← pt "(\\z. if z = x then y1 else (f:A->B) z) = (\\z. if z = x then y2 else (f:A->B) z)"
  let uF ← pt "f:A->B"
  let uY2 ← pt "y2:B"
  let uY1 ← pt "y1:B"
  let uX450 ← pt "x:A"
  let uX449 ← pt "x:A"
  let uX448 ← pt "x:A"
  -- MP_TAC o C AP_THM `x:A`   (`C AP_THM uX` is `fun th => AP_THM th uX`, and it
  -- runs FIRST).
  let mpApThmX : thm_tactic := MP_TAC oT Lib.C AP_THM uX457
  let UNIQUE_SKOLEM_THM ← (prove (← pt "!P. (!x:A. ?!y:B. P x y) <=> (?!f. !x. P x (f x))")
      (THEN B GEN_TAC (THEN B (REWRITE_TAC [T.EXISTS_UNIQUE_THM, SKOLEM_THM, T.FORALL_AND_THM])
        (THENL B (THEN B EQ_TAC (THEN B (DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC)) (ASM_REWRITE_TAC [])))
            [THEN B (REPEAT B STRIP_TAC) (THEN B (ONCE_REWRITE_TAC [FUN_EQ_THM])
              (THEN B (X_GEN_TAC uX448) (THEN B (FIRST_ASSUM MATCH_MP_TAC)
                (THEN B (EXISTS_TAC uX449) (ASM_REWRITE_TAC []))))),
             THEN B (MAP_EVERY X_GEN_TAC [uX450, uY1, uY2]) (THEN B STRIP_TAC
               (THEN B (FIRST_ASSUM (X_CHOOSE_TAC uF))
                 (THENL B (SUBGOAL_THEN uFunEq MP_TAC)
                   [THEN B (FIRST_ASSUM MATCH_MP_TAC) (THEN B (REPEAT B STRIP_TAC)
                     (THEN B BETA_TAC (THEN B COND_CASES_TAC (ASM_REWRITE_TAC [])))),
                    THEN B (DISCH_THEN mpApThmX) (REWRITE_TAC [])])))]))) : IO (Except String thm))
  -- Extend default congruences for contextual rewriting.
  let COND_CONG ← TAUT "(g = g') ==> (g' ==> (t = t')) ==> (~g' ==> (e = e')) ==> ((if g then t else e) = (if g' then t' else e'))"
  Simp.extend_basic_congs [COND_CONG]
  let COND_EQ_CLAUSE ← (prove (← pt "(if x = x then y else z) = y") (REWRITE_TAC []) : IO (Except String thm))
  let _ ← (Simp.extend_basic_rewrites B [COND_EQ_CLAUSE] : IO (Except String Unit))
  let xBool ← pt "x:bool"
  let boolRecWit ← pt "\\x. if x then b:A else a"
  -- We can now treat "bool" as an enumerated type for some purposes.
  let bool_INDUCT ← (prove (← pt "!P. P F /\\ P T ==> !x. P x")
      (THEN B (REPEAT B STRIP_TAC) (THEN B (DISJ_CASES_TAC (← liftExcept (B.SPEC xBool BOOL_CASES_AX)))
        (ASM_REWRITE_TAC []))) : IO (Except String thm))
  let bool_RECURSION ← (prove (← pt "!a b:A. ?f. f F = a /\\ f T = b")
      (THEN B (REPEAT B GEN_TAC) (THEN B (EXISTS_TAC boolRecWit) (REWRITE_TAC []))) : IO (Except String thm))
  return { etaPth, etaT, EQ_EXT, FUN_EQ_THM,
           EXISTS_THM, selectRulePth, selectConvPth, SELECT_REFL, SELECT_UNIQUE,
           EXCLUDED_MIDDLE, BOOL_CASES_AX,
           DE_MORGAN_THM, NOT_CLAUSES, NOT_IMP, CONTRAPOS_THM,
           ccontrPth, contraposConvPth, contraposA, contraposB, refuteF, refuteThenPth,
           NOT_EXISTS_THM, EXISTS_NOT_THM, NOT_FORALL_THM, FORALL_NOT_THM,
           FORALL_BOOL_THM, EXISTS_BOOL_THM,
           LEFT_FORALL_OR_THM, RIGHT_FORALL_OR_THM, LEFT_OR_FORALL_THM, RIGHT_OR_FORALL_THM,
           LEFT_IMP_FORALL_THM, LEFT_EXISTS_IMP_THM, RIGHT_IMP_EXISTS_THM, RIGHT_EXISTS_IMP_THM,
           COND_CLAUSES, COND_EXPAND, COND_ID, COND_RAND, COND_RATOR, COND_ABS, COND_SWAP,
           MONO_COND, COND_ELIM_THM, denegPth,
           SKOLEM_THM, SKOLEM_THM_GEN, UNIQUE_SKOLEM_ALT, UNIQUE_SKOLEM_THM,
           COND_CONG, COND_EQ_CLAUSE, bool_INDUCT, bool_RECURSION }

end HolCore.Classic
