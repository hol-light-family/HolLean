/- ---------------------------------------------------------------------- -/
/- The HOL Light surface for the pure translations (HolMath, HolLibrary). -/
/- ---------------------------------------------------------------------- -/
/- File: HolMath/Base.lean
  Lean4 translation by Chris Walton 2026

  The pure translations (HolMath, and HolLibrary for HOL Light's `Library/`
  files) have no `unsafe`: every theorem and tactic that comes from Session
  reaches them as a parameter.  This module lets their proofs read like the
  OCaml.  It needs only HolCore, so HolMath files can use it too:

  * `HolBase` carries the Bool, Class and Theorem bundles (`B`, `C`, `T`).
    It is a class, so the core tactics below can be used under their HOL
    Light names (`REWRITE_TAC [...]`, not `Simp.REWRITE_TAC B [...]`): a
    setup function takes `[HolBase]` and they find it.

  * `THEN`, `THENL`, `ORELSE`, `THENC`, `ORELSEC` are infix, all at one
    level and left associative, as in HOL Light's camlp5 grammar (pa_j:
    `a THEN b` is `then_ a b`).  Open `HolLight.Syntax` to use them.

  * `o` is also the composition of a theorem-tactic with a rule
    (`MP_TAC o MATCH_MP th`): the rule runs when the theorem-tactic is
    applied, and its failure is the tactic's failure, as in OCaml.

  * Rules that can fail (`SPEC`, `GSYM`, `MATCH_MP`, ...) run in
    `ExceptT String IO`, so a proof writes `(← GSYM ADD_SYM)` where OCaml
    writes `GSYM ADD_SYM`: evaluated while the proof is built, as in OCaml.

  * `q r"..."` parses a quotation; raw strings keep the OCaml text verbatim.
    `prove` takes the goal as a string and parses it AFTER the tactic is
    built, which is OCaml's order (a tuple is evaluated right to left).

  * Inside `fun th -> ...`, a rule's failure must make the TACTIC fail (so
    `FIRST_ASSUM`, `ORELSE`, ... can try the next option).  `tactic_of do
    ...` builds the tactic when it is applied.
-/

import HolCore

open HolCore HolCore.Kernel HolCore.Bool HolCore.Equal
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)

namespace HolLight

/-- The core bundles, passed by instance. -/
class HolBase where
  B : BoolThms
  C : HolCore.Classic.ClassThms
  T : HolCore.Theorems.TheoremThms

section
variable [HolBase]
open HolBase

/- -- Building blocks ------------------------------------------------------ -/

/-- Parse a quotation (OCaml's backquotes). -/
def q (s : String) : ExceptT String IO term := HolCore.Parser.parse_term s

/-- Parse a type quotation (`` `:ty` ``). -/
def qty (s : String) : ExceptT String IO hol_type := ExceptT.mk (HolCore.Parser.parse_type s)

/-- A tactic built when it is applied: for `fun th -> ...` bodies whose
    rules can fail. -/
def tactic_of (m : ExceptT String IO tactic) : tactic := fun g => do
  match ← m.run with
  | .error e => return .error e
  | .ok t => t g

private def ex {α : Type} (x : Except String α) : ExceptT String IO α := liftExcept x
/-- OCaml's `try a with Failure _ -> b`, for nesting where `try`/`catch`
    syntax would attach a `catch` to the wrong `try`. -/
def tryWith {α : Type} (a : ExceptT String IO α) (b : ExceptT String IO α) : ExceptT String IO α :=
  tryCatch a (fun _ => b)
private def io {α : Type} (x : IO (Except String α)) : ExceptT String IO α := ExceptT.mk x

/-- OCaml's `snd` as proofs use it, on a goal inside `W(... o snd)`: the
    conclusion.  (Monomorphic, so that `o` can find its type.) -/
def snd (g : goal) : term := g.2

/-- lib.ml's `F_F` (`(f F_F g) (x,y) = (f x, g y)`), for rules that can fail. -/
def F_F {α β γ δ : Type} (f : α → ExceptT String IO γ) (g : β → ExceptT String IO δ)
    (p : α × β) : ExceptT String IO (γ × δ) := do
  let y ← g p.2
  let x ← f p.1
  pure (x, y)

/-- OCaml's `rev` as proofs use it, on a theorem list (`... o rev`). -/
def rev (l : List thm) : List thm := l.reverse

/-- `prove(`goal`, tac)`: the goal is parsed after the tactic is built. -/
def prove (goal : String) (tac : tactic) : ExceptT String IO thm := do
  io (Tactics.prove B (← q goal) tac)

/- -- Combinators (pa_j: one level, left associative) ---------------------- -/

def then_ (t1 t2 : tactic) : tactic := Tactics.THEN B t1 t2
def thenl_ (t : tactic) (ts : List tactic) : tactic := Tactics.THENL B t ts
def orelse_ (t1 t2 : tactic) : tactic := Tactics.ORELSE t1 t2
def thenc_ (c1 c2 : ioconv) : ioconv := Simp.thencIO c1 c2
def orelsec_ (c1 c2 : ioconv) : ioconv := Simp.orelsecIO c1 c2

end

/-- OCaml's `o`, for the kinds of function a proof composes: plain
    functions, a theorem-tactic after a rule (`MP_TAC o SPEC t`: the rule
    runs when the theorem-tactic is applied, and its failure is the
    tactic's), a rule after a rule, and syntax functions that can fail
    (`lhs o rand`).  One class, so that `o` is ONE notation: two notations
    for one token make Lean elaborate both, and then `(← ...)` inside an
    operand is lifted wrongly. -/
class OComp (F G : Type) (R : outParam Type) where
  comp : F → G → R

instance (priority := high) oRuleTac [HolBase] {α β : Type} :
    OComp (β → tactic) (α → ExceptT String IO β) (α → tactic) where
  comp ttac rule := fun a => tactic_of do return ttac (← rule a)

instance (priority := high) oRuleRule {α β γ : Type} :
    OComp (β → ExceptT String IO γ) (α → ExceptT String IO β) (α → ExceptT String IO γ) where
  comp r1 r2 := fun a => do r1 (← r2 a)

/-- A tactic-valued function after a syntax function that can fail
    (`... o lhand o snd` inside `W`). -/
instance (priority := high) oExceptTac {α β : Type} :
    OComp (β → tactic) (α → Except String β) (α → tactic) where
  comp f g := fun a gl => match g a with
    | .ok b => f b gl
    | .error e => return .error e

instance oExcept {α β γ : Type} :
    OComp (β → Except String γ) (α → Except String β) (α → Except String γ) where
  comp f g := fun a => g a >>= f

instance (priority := low) oPure {α β γ : Type} : OComp (β → γ) (α → β) (α → γ) where
  comp f g := fun a => f (g a)

section
variable [HolBase]
open HolBase

/- -- Tactics ------------------------------------------------------------ -/

def ABBREV_TAC (t : term) : tactic := Simp.ABBREV_TAC B t
def ACCEPT_TAC : thm_tactic := Tactics.ACCEPT_TAC B
def ABS_TAC : tactic := Tactics.ABS_TAC B
def ALL_TAC : tactic := Tactics.ALL_TAC
def ANTE_RES_THEN : thm_tactical := Tactics.ANTE_RES_THEN B
def ANTS_TAC : tactic := Tactics.ANTS_TAC B
def BETA_TAC : tactic := Tactics.BETA_TAC B
def AP_TERM_TAC : tactic := Tactics.AP_TERM_TAC B
def AP_THM_TAC : tactic := Tactics.AP_THM_TAC B
def ASM (tl : List thm → tactic) (ths : List thm) : tactic := Tactics.ASM tl ths
def ASM_CASES_TAC (t : term) : tactic := Classic.ASM_CASES_TAC B C.EXCLUDED_MIDDLE t
def BOOL_CASES_TAC (t : term) : tactic := Classic.BOOL_CASES_TAC B C.BOOL_CASES_AX t
def ASM_REWRITE_TAC (ths : List thm) : tactic := Simp.ASM_REWRITE_TAC B ths
def ASM_SIMP_TAC (ths : List thm) : tactic := Simp.ASM_SIMP_TAC B ths
def PURE_REWRITE_TAC (ths : List thm) : tactic := Simp.PURE_REWRITE_TAC B ths
def PURE_ONCE_REWRITE_TAC (ths : List thm) : tactic := Simp.PURE_ONCE_REWRITE_TAC B ths
def PURE_ASM_REWRITE_TAC (ths : List thm) : tactic := Simp.PURE_ASM_REWRITE_TAC B ths
def PURE_ONCE_ASM_REWRITE_TAC (ths : List thm) : tactic := Simp.PURE_ONCE_ASM_REWRITE_TAC B ths
def PURE_SIMP_TAC (ths : List thm) : tactic := Simp.PURE_SIMP_TAC B ths
def ONCE_SIMP_TAC (ths : List thm) : tactic := Simp.ONCE_SIMP_TAC B ths
def PURE_ASM_SIMP_TAC (ths : List thm) : tactic := Simp.PURE_ASM_SIMP_TAC B ths
def ASSUME_TAC : thm_tactic := Tactics.ASSUME_TAC B
def ASSUM_LIST (f : List thm → tactic) : tactic := Tactics.ASSUM_LIST f
def BINOP_TAC : tactic := Tactics.BINOP_TAC B
def CHANGED_TAC (t : tactic) : tactic := Tactics.CHANGED_TAC B t
def CHOOSE_TAC : thm_tactic := Tactics.CHOOSE_TAC B
def CHOOSE_THEN : thm_tactical := Tactics.CHOOSE_THEN B
def COND_CASES_TAC : tactic := Classic.COND_CASES_TAC B C.COND_ELIM_THM C.denegPth
def CONJ_TAC : tactic := Tactics.CONJ_TAC B
def CONJUNCTS_THEN : thm_tactical := Tactics.CONJUNCTS_THEN B
def CONJUNCTS_THEN2 (t1 t2 : thm_tactic) : thm_tactic := Tactics.CONJUNCTS_THEN2 B t1 t2
def CONV_TAC (c : ioconv) : tactic := Tactics.CONV_TAC B c
def DISCH_TAC : tactic := Tactics.DISCH_TAC B
def DISCH_THEN (ttac : thm_tactic) : tactic := Tactics.DISCH_THEN B ttac
def DISJ1_TAC : tactic := Tactics.DISJ1_TAC B
def DISJ2_TAC : tactic := Tactics.DISJ2_TAC B
def DISJ_CASES_TAC : thm_tactic := Tactics.DISJ_CASES_TAC B
def DISJ_CASES_THEN : thm_tactical := Tactics.DISJ_CASES_THEN B
def DISJ_CASES_THEN2 (t1 t2 : thm_tactic) : thm_tactic := Tactics.DISJ_CASES_THEN2 B t1 t2
def EQ_TAC : tactic := Tactics.EQ_TAC B
def IMP_RES_THEN : thm_tactical := Tactics.IMP_RES_THEN B
def EVERY (ts : List tactic) : tactic := Tactics.EVERY B ts
def EVERY_ASSUM (ttac : thm_tactic) : tactic := Tactics.EVERY_ASSUM B ttac
def EXISTS_TAC (t : term) : tactic := Tactics.EXISTS_TAC B t
def EXPAND_TAC (s : String) : tactic := Simp.EXPAND_TAC B s
def FIRST (ts : List tactic) : tactic := Tactics.FIRST B ts
def FIRST_ASSUM (ttac : thm_tactic) : tactic := Tactics.FIRST_ASSUM ttac
def FIRST_X_ASSUM (ttac : thm_tactic) : tactic := Tactics.FIRST_X_ASSUM B ttac
def GEN_REWRITE_TAC (c : ioconv → ioconv) (ths : List thm) : tactic := Simp.GEN_REWRITE_TAC B c ths
def GEN_TAC : tactic := Tactics.GEN_TAC B
def HYP (tac : List thm → tactic) (s : String) : List thm → tactic := Tactics.HYP tac s
def LABEL_TAC (s : String) : thm_tactic := Tactics.LABEL_TAC B s
def MAP_EVERY {α : Type} (f : α → tactic) (l : List α) : tactic := Tactics.MAP_EVERY B f l
def MAP_FIRST {α : Type} (f : α → tactic) (l : List α) : tactic := Tactics.MAP_FIRST B f l
def MATCH_ACCEPT_TAC : thm_tactic := Tactics.MATCH_ACCEPT_TAC B
def MATCH_MP_TAC : thm_tactic := Tactics.MATCH_MP_TAC B
def MP_TAC : thm_tactic := Tactics.MP_TAC B
def ONCE_ASM_REWRITE_TAC (ths : List thm) : tactic := Simp.ONCE_ASM_REWRITE_TAC B ths
def ONCE_REWRITE_TAC (ths : List thm) : tactic := Simp.ONCE_REWRITE_TAC B ths
def POP_ASSUM (ttac : thm_tactic) : tactic := Tactics.POP_ASSUM ttac
def POP_ASSUM_LIST (tl : List thm → tactic) : tactic := Tactics.POP_ASSUM_LIST tl
def REFL_TAC : tactic := Tactics.REFL_TAC B
def REMOVE_THEN (s : String) (ttac : thm_tactic) : tactic := Tactics.REMOVE_THEN s ttac
def USE_THEN (s : String) (ttac : thm_tactic) : tactic := Tactics.USE_THEN s ttac
def REPEAT (t : tactic) : tactic := Tactics.REPEAT B t
def REPEAT_TCL (ttcl : thm_tactical) : thm_tactical := Tactics.REPEAT_TCL ttcl
def REPLICATE_TAC (n : Nat) (t : tactic) : tactic := Tactics.REPLICATE_TAC B n t
def REWRITE_TAC (ths : List thm) : tactic := Simp.REWRITE_TAC B ths
def RULE_ASSUM_TAC (r : thm → ExceptT String IO thm) : tactic :=
  Tactics.RULE_ASSUM_TAC B (fun th => (r th).run)
def SIMP_TAC (ths : List thm) : tactic := Simp.SIMP_TAC B ths
def SPEC_TAC (p : term × term) : tactic := Tactics.SPEC_TAC B p
def STRIP_ASSUME_TAC : thm_tactic := Tactics.STRIP_ASSUME_TAC B
def STRIP_TAC : tactic := Tactics.STRIP_TAC B
def STRUCT_CASES_TAC : thm_tactic := Tactics.STRUCT_CASES_TAC B
def SUBGOAL_THEN (t : term) (ttac : thm_tactic) : tactic := Tactics.SUBGOAL_THEN B t ttac
def SUBST1_TAC : thm_tactic := Tactics.SUBST1_TAC B
def SUBST_ALL_TAC : thm_tactic := Tactics.SUBST_ALL_TAC B
def TRANS_TAC (th : thm) (t : term) : tactic := Tactics.TRANS_TAC B th t
def TRY (t : tactic) : tactic := Tactics.TRY B t
def UNDISCH_TAC (t : term) : tactic := Tactics.UNDISCH_TAC B t
def UNDISCH_THEN (t : term) (ttac : thm_tactic) : tactic := Tactics.UNDISCH_THEN B t ttac
def X_CHOOSE_TAC (t : term) : thm_tactic := Tactics.X_CHOOSE_TAC B t
def X_CHOOSE_THEN (t : term) (ttac : thm_tactic) : thm_tactic := Tactics.X_CHOOSE_THEN B t ttac
def X_GEN_TAC (t : term) : tactic := Tactics.X_GEN_TAC B t

/- -- Rules (they can fail, so they run in `ExceptT String IO`) ------------ -/

def AP_TERM (t : term) (th : thm) : ExceptT String IO thm := ex (Equal.AP_TERM t th)
def AP_THM (th : thm) (t : term) : ExceptT String IO thm := ex (Equal.AP_THM th t)
def AC (acsuite : thm) (t : term) : ExceptT String IO thm :=
  io (HolCore.Theorems.AC B T.REFL_CLAUSE acsuite t)
def ASSUME (t : term) : ExceptT String IO thm := ex (HolCore.Kernel.ASSUME t)
def CONJ (th1 th2 : thm) : ExceptT String IO thm := ex (B.CONJ th1 th2)
def MK_COMB (p : thm × thm) : ExceptT String IO thm := ex (HolCore.Kernel.MK_COMB p.1 p.2)
def TRANS (th1 th2 : thm) : ExceptT String IO thm := ex (HolCore.Kernel.TRANS th1 th2)
def EQ_MP (th1 th2 : thm) : ExceptT String IO thm := ex (HolCore.Kernel.EQ_MP th1 th2)
def DISCH (t : term) (th : thm) : ExceptT String IO thm := ex (B.DISCH t th)
def EXISTS (p : term × term) (th : thm) : ExceptT String IO thm := ex (B.EXISTS p th)
def SIMPLE_EXISTS (v : term) (th : thm) : ExceptT String IO thm := ex (B.SIMPLE_EXISTS v th)
def CHOOSE (p : term × thm) (th : thm) : ExceptT String IO thm := ex (B.CHOOSE p th)
def SIMPLE_CHOOSE (v : term) (th : thm) : ExceptT String IO thm := ex (B.SIMPLE_CHOOSE v th)
def DISJ1 (th : thm) (t : term) : ExceptT String IO thm := ex (B.DISJ1 th t)
def DISJ2 (t : term) (th : thm) : ExceptT String IO thm := ex (B.DISJ2 t th)
def DISJ_CASES (th1 th2 th3 : thm) : ExceptT String IO thm := ex (B.DISJ_CASES th1 th2 th3)
def NOT_ELIM (th : thm) : ExceptT String IO thm := ex (B.NOT_ELIM th)
def NOT_INTRO (th : thm) : ExceptT String IO thm := ex (B.NOT_INTRO th)
def EQF_INTRO (th : thm) : ExceptT String IO thm := ex (B.EQF_INTRO th)
def CONTR (t : term) (th : thm) : ExceptT String IO thm := ex (B.CONTR t th)
def EXISTENCE (th : thm) : ExceptT String IO thm := ex (B.EXISTENCE th)
def IMP_ANTISYM_RULE (th1 th2 : thm) : ExceptT String IO thm := ex (B.IMP_ANTISYM_RULE th1 th2)
def IMP_TRANS (th1 th2 : thm) : ExceptT String IO thm := ex (B.IMP_TRANS th1 th2)
def EQ_IMP_RULE (th : thm) : ExceptT String IO (thm × thm) := ex (B.EQ_IMP_RULE th)
def ADD_ASSUM (t : term) (th : thm) : ExceptT String IO thm := ex (B.ADD_ASSUM t th)
def UNDISCH_ALL (th : thm) : ExceptT String IO thm := ex (B.UNDISCH_ALL th)
def BETA_RULE (th : thm) : ExceptT String IO thm := ex (Equal.BETA_RULE th)
def PROVE_HYP (th1 th2 : thm) : ExceptT String IO thm := ex (Equal.PROVE_HYP th1 th2)
def INSTANTIATE (i : Drule.instantiation) (th : thm) : ExceptT String IO thm :=
  ex (Drule.INSTANTIATE i th)
def term_match (lconsts : List term) (vtm ctm : term) : ExceptT String IO Drule.instantiation :=
  io (Drule.term_match lconsts vtm ctm)
def RIGHT_BETAS (args : List term) (th : thm) : ExceptT String IO thm :=
  ex (HolCore.IndDefs.RIGHT_BETAS args th)
def MK_FORALL (v : term) (th : thm) : ExceptT String IO thm := io (Drule.MK_FORALL v th)
def MK_EXISTS (v : term) (th : thm) : ExceptT String IO thm := io (Drule.MK_EXISTS v th)
def CONJ_ACI_RULE (t : term) : ExceptT String IO thm := ex (HolCore.Canon.CONJ_ACI_RULE B t)
def PINST (tyin : List (hol_type × hol_type)) (tmin : List (term × term)) (th : thm) :
    ExceptT String IO thm := ex (HolCore.Bool.PINST tyin tmin th)
def SUBS (ths : List thm) (th : thm) : ExceptT String IO thm := io (Equal.SUBS ths th)
def SUBS_CONV (ths : List thm) : ioconv := Equal.SUBS_CONV ths

/-- lib.ml's `end_itlist`, for a rule that can fail (`end_itlist CONJ`). -/
def end_itlist {α : Type} (f : α → α → ExceptT String IO α) : List α → ExceptT String IO α
  | [] => throw "end_itlist"
  | [x] => pure x
  | x :: xs => do f x (← end_itlist f xs)
def CONJUNCT1 (th : thm) : ExceptT String IO thm := ex (B.CONJUNCT1 th)
def CONJUNCT2 (th : thm) : ExceptT String IO thm := ex (B.CONJUNCT2 th)
def CONJUNCTS (th : thm) : List thm := B.CONJUNCTS th
def CONJ_PAIR (th : thm) : ExceptT String IO (thm × thm) := ex (B.CONJ_PAIR th)
def CONV_RULE (c : ioconv) (th : thm) : ExceptT String IO thm := io (Simp.convRuleIO c th)
def DISCH_ALL (th : thm) : ExceptT String IO thm := ex (B.DISCH_ALL th)
def EQF_ELIM (th : thm) : ExceptT String IO thm := ex (B.EQF_ELIM th)
def EQT_INTRO (th : thm) : ExceptT String IO thm := ex (B.EQT_INTRO th)
def EQT_ELIM (th : thm) : ExceptT String IO thm := ex (B.EQT_ELIM th)
def GEN (t : term) (th : thm) : ExceptT String IO thm := ex (B.GEN t th)
def GENL (ts : List term) (th : thm) : ExceptT String IO thm := ex (B.GENL ts th)
def GEN_ALL (th : thm) : ExceptT String IO thm := ex (B.GEN_ALL th)
def GEN_REWRITE_RULE (c : ioconv → ioconv) (ths : List thm) (th : thm) : ExceptT String IO thm :=
  io (Simp.GEN_REWRITE_RULE B c ths th)
def GSYM (th : thm) : ExceptT String IO thm := ex (Equal.GSYM th)
def INST (l : List (term × term)) (th : thm) : ExceptT String IO thm := ex (HolCore.Kernel.INST l th)
def INST_TYPE (l : List (hol_type × hol_type)) (th : thm) : ExceptT String IO thm :=
  ex (HolCore.Kernel.INST_TYPE l th)
def ISPEC (t : term) (th : thm) : ExceptT String IO thm := ex (B.ISPEC t th)
def ISPECL (ts : List term) (th : thm) : ExceptT String IO thm := ex (B.ISPECL ts th)
def MATCH_MP (ith th : thm) : ExceptT String IO thm := io (Drule.MATCH_MP B ith th)
def MP (ith th : thm) : ExceptT String IO thm := ex (B.MP ith th)
/-- drule.ml's `MP_CONV`. -/
def MP_CONV (cnv : ioconv) (th : thm) : ExceptT String IO thm := do
  let (l, _r) ← ex (dest_imp (concl th))
  let ath ← io (cnv l)
  match B.EQT_ELIM ath >>= B.MP th with
  | .ok r => pure r
  | .error _ => ex (B.MP th ath)
def ONCE_REWRITE_RULE (ths : List thm) (th : thm) : ExceptT String IO thm :=
  io (Simp.ONCE_REWRITE_RULE B ths th)
def PURE_ONCE_REWRITE_RULE (ths : List thm) (th : thm) : ExceptT String IO thm :=
  io (Simp.PURE_ONCE_REWRITE_RULE B ths th)
def PURE_REWRITE_RULE (ths : List thm) (th : thm) : ExceptT String IO thm :=
  io (Simp.PURE_REWRITE_RULE B ths th)
def PART_MATCH (f : term → Except String term) (th : thm) (t : term) : ExceptT String IO thm :=
  io (Drule.PART_MATCH B f th t)
def REWRITE_RULE (ths : List thm) (th : thm) : ExceptT String IO thm :=
  io (Simp.REWRITE_RULE B ths th)
def SPEC (t : term) (th : thm) : ExceptT String IO thm := ex (B.SPEC t th)
def SPECL (ts : List term) (th : thm) : ExceptT String IO thm := ex (B.SPECL ts th)
def SPEC_VAR (th : thm) : ExceptT String IO (term × thm) := ex (B.SPEC_VAR th)
def SPEC_ALL (th : thm) : ExceptT String IO thm := ex (B.SPEC_ALL th)
def SYM (th : thm) : ExceptT String IO thm := ex (HolCore.Equal.SYM th)
def UNDISCH (th : thm) : ExceptT String IO thm := ex (B.UNDISCH th)
def TAUT (t : term) : ExceptT String IO thm := io (Classic.TAUT B C.BOOL_CASES_AX t)
def ITAUT (t : term) : ExceptT String IO thm := io (Itab.ITAUT B t)
/-- class.ml's `SELECT_RULE`: from `|- ?x. P x` derive `|- P(@x. P x)`. -/
def SELECT_RULE (th : thm) : ExceptT String IO thm :=
  ex (Classic.SELECT_RULE B C.selectRulePth
        (mk_var "P" (hol_type.Tyapp "fun" [aty, bool_ty])) th)

/- -- Conversions (as `ioconv`, which CONV_TAC takes) --------------------- -/

def LAND_CONV (c : ioconv) : ioconv := Simp.landConvIO c
def RAND_CONV (c : ioconv) : ioconv := Simp.randConvIO c
def RATOR_CONV (c : ioconv) : ioconv := Simp.ratorConvIO c
def BINDER_CONV (c : ioconv) : ioconv := Simp.binderConvIO c
def ONCE_DEPTH_CONV (c : ioconv) : ioconv := Simp.onceDepthConvIO c
def DEPTH_CONV (c : ioconv) : ioconv := Simp.depthConvIO c
def REDEPTH_CONV (c : ioconv) : ioconv := Simp.redepthConvIO c
def TOP_DEPTH_CONV (c : ioconv) : ioconv := Simp.topDepthConvIO c
def TOP_SWEEP_CONV (c : ioconv) : ioconv := Simp.topSweepConvIO c
def TRY_CONV (c : ioconv) : ioconv := Simp.tryConvIO c
def REPEATC (c : ioconv) : ioconv := Simp.repeatcIO c
def ALL_CONV : ioconv := Simp.allConvIO
/-- equal.ml's `FIRST_CONV`. -/
def FIRST_CONV : List ioconv → ioconv
  | [] => fun _ => pure (.error "FIRST_CONV")
  | [c] => c
  | c :: cs => Simp.orelsecIO c (FIRST_CONV cs)
def ABS_CONV (c : ioconv) : ioconv := Simp.absConvIO c
def BINOP_CONV (c : ioconv) : ioconv := Simp.binopConvIO c
def COMB_CONV (c : ioconv) : ioconv := Simp.combConvIO c
/-- equal.ml's `SUB_CONV`. -/
def SUB_CONV (c : ioconv) : ioconv := fun tm =>
  match tm with
  | .Comb _ _ => COMB_CONV c tm
  | .Abs _ _ => ABS_CONV c tm
  | _ => pure (.ok (REFL tm))
/-- equal.ml's `CHANGED_CONV`. -/
def CHANGED_CONV (c : ioconv) : ioconv := fun tm => ExceptT.run do
  let th ← (c tm : ExceptT String IO thm)
  let (l, r) ← dest_eq (concl th)
  if aconv l r then throw "CHANGED_CONV" else pure th
def DEPTH_BINOP_CONV (op : term) (c : ioconv) : ioconv := Simp.depthBinopConvIO op c
def COMB2_CONV (c1 c2 : ioconv) : ioconv := Simp.comb2ConvIO c1 c2
def SYM_CONV : ioconv := fun t => pure (Equal.SYM_CONV t)
def CONTRAPOS_CONV : ioconv := fun t =>
  pure (Classic.CONTRAPOS_CONV C.contraposConvPth (mk_var "a" bool_ty) (mk_var "b" bool_ty) t)
def BETA_CONV : ioconv := fun t => pure (Equal.BETA_CONV t)
def BETAS_CONV : ioconv := fun t => pure (Drule.BETAS_CONV t)
def REWRITE_CONV (ths : List thm) : ioconv := Simp.REWRITE_CONV' B ths
def PURE_REWRITE_CONV (ths : List thm) : ioconv := Simp.PURE_REWRITE_CONV' B ths
def ONCE_REWRITE_CONV (ths : List thm) : ioconv := Simp.ONCE_REWRITE_CONV' B ths
def SIMP_CONV (ths : List thm) : ioconv := Simp.SIMP_CONV' B ths
def GEN_REWRITE_CONV (c : ioconv → ioconv) (ths : List thm) : ioconv := Simp.GEN_REWRITE_CONV' B c ths
def REWR_CONV (th : thm) : ioconv := Simp.REWR_CONV B th
/-- `GEN_REWRITE_CONV c ths` with its net built NOW, for OCaml's partial
    application `let conv = GEN_REWRITE_CONV c ths in fun tm -> ...`.
    (`GEN_REWRITE_CONV` above rebuilds the net at every application.) -/
def GEN_REWRITE_CONV_NET (c : ioconv → ioconv) (ths : List thm) :
    ExceptT String IO ioconv :=
  io (Simp.GEN_REWRITE_CONV B c ths)
/-- `REWRITE_CONV ths` with its net built now (with the basic rewrites
    current now), for OCaml's partial application. -/
def REWRITE_CONV_NET (ths : List thm) : ExceptT String IO ioconv :=
  io (Simp.REWRITE_CONV B ths)
/-- `PURE_REWRITE_CONV ths` with its net built now. -/
def PURE_REWRITE_CONV_NET (ths : List thm) : ExceptT String IO ioconv :=
  io (Simp.PURE_REWRITE_CONV B ths)
/-- `PURE_ONCE_REWRITE_CONV ths` with its net built now. -/
def PURE_ONCE_REWRITE_CONV_NET (ths : List thm) : ExceptT String IO ioconv :=
  io (Simp.PURE_ONCE_REWRITE_CONV B ths)
/-- canon.ml's `ASSOC_CONV th`, built now. -/
def ASSOC_CONV (th : thm) : ExceptT String IO ioconv := ex (HolCore.Canon.ASSOC_CONV B th)
def REWRITES_CONV (net : HolCore.Nets.net Simp.gconv) : ioconv := Simp.REWRITES_CONV net

end

/- -- Syntax --------------------------------------------------------------- -/

namespace Syntax
scoped infixl:30 " THEN " => HolLight.then_
scoped infixl:30 " THENL " => HolLight.thenl_
scoped infixl:30 " ORELSE " => HolLight.orelse_
scoped infixl:30 " THENC " => HolLight.thenc_
scoped infixl:30 " ORELSEC " => HolLight.orelsec_
/- Higher priority than HolCore.Lib's `o` (plain composition), so that it
   alone is used here; it covers plain composition too. -/
scoped infixl:90 (priority := high) " o " => HolLight.OComp.comp
end Syntax

end HolLight
