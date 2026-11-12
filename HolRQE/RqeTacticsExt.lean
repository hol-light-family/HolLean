/- ========================================================================= -/
/- Rqe: labels, refinement proofs, term type inference and tactics.        -/
/- ========================================================================= -/
/- File: HolRQE/RqeTacticsExt.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Rqe/rqe_tactics_ext.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/analysis.ml, Library/poly.ml, Rqe/rqe_lib.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionRQE.RqeTacticsExt fills them).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, INT_ARITH, TAUT, SET_RULE, ...) they are
  bound first, in OCaml's order.
-/

import HolLibrary.Analysis
import HolLibrary.Poly
import HolRQE.RqeLib

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolRQE.RqeLib

namespace HolRQE.RqeTacticsExt

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (EXCLUDED_MIDDLE num_CASES : thm)
  deriving Inhabited

/-- What rqe_tactics_ext.ml uses from Session besides theorems. -/
structure RqeTacticsExtDeps where
  new_definition : String → ExceptT String IO thm
  define : String → ExceptT String IO thm
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_ARITH_TAC : tactic
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  ASM_MESON_TAC : List thm → tactic
  METIS_TAC : List thm → tactic
  ASM_METIS_TAC : List thm → tactic
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  TAUT : term → ExceptT String IO thm
  ITAUT : term → ExceptT String IO thm
  REAL_ARITH : term → ExceptT String IO thm
  REAL_FIELD : term → ExceptT String IO thm
  REAL_ARITH_TAC : tactic
  ASM_REAL_ARITH_TAC : tactic
  INDUCT_TAC : tactic
  INT_ARITH : term → ExceptT String IO thm
  INT_ARITH_TAC : tactic
  ASM_INT_ARITH_TAC : tactic
  INTEGER_RULE : term → ExceptT String IO thm  -- ints.ml's INTEGER_RULE
  INTEGER_TAC : tactic
  NUMBER_RULE : ioconv  -- ints.ml's NUMBER_RULE
  NUM_REDUCE_CONV : ioconv
  INT_REDUCE_CONV : ioconv
  INT_RED_CONV : ioconv
  INT_REM_DOWN_CONV : ioconv
  HAS_SIZE_CONV : ioconv  -- card.ml's HAS_SIZE_CONV
  let_CONV : ioconv
  num_CONV : ioconv
  mk_numeral : Rat → Except String term
  LET_TAC : tactic
  basic_ss : List thm → IO (Except String HolCore.Simp.simpset)
  NUM_SUB_CONV : ioconv
  REAL_RAT_REDUCE_CONV : ioconv
  NUM_EQ_CONV : ioconv
  NUM_DIV_CONV : ioconv
  EXP_MOD_CONV : ioconv
  EXPAND_CASES_CONV : ioconv
  refine : HolCore.Tactics.refinement → IO HolCore.Tactics.goalstack  -- tactics.ml's refine (the current goalstack)
  current_goalstack : IO.Ref HolCore.Tactics.goalstack  -- tactics.ml's current_goalstack
  FALSITY_DEF : thm  -- VALID's falsity (class.ml)
  core1 : CoreThms1

/-- RingTheory's `wPart` (copied verbatim).  `W(MP_TAC o PART_MATCH f th o g
    o snd)`: match `th`'s part `f` against the part `g` of the goal, and
    MP_TAC the instance. -/
def wPart [HolBase] (g : term → Except String term) (f : term → Except String term)
    (th : thm) : tactic := fun gl =>
  ExceptT.run do
    let t ← liftExcept (g gl.2)
    ExceptT.mk (MP_TAC (← PART_MATCH f th t) gl)

/-- tactics.ml's NO_TAC. -/
def NO_TAC : tactic := HolCore.Tactics.NO_TAC

/- The functions of rqe_tactics_ext.ml that are plain functions of their
   arguments (no refs, no theorems, no session state) are top-level
   definitions here, as in HolRQE/RqeLib.lean; the rest are the bundle below.
   OCaml's failures are `Except String` with the same messages. -/

/- ---------------------------------------------------------------------- -/
/-  Labels (rqe_tactics_ext.ml 7-25)                                      -/
/- ---------------------------------------------------------------------- -/

/-- LABEL_ALL_TAC's local `mk_one_label`. -/
partial def LABEL_ALL_TAC.mk_one_label (i : Int) (avoid : List String) : String :=
  let label := "Z-" ++ toString i
  if !(mem label avoid) then label else LABEL_ALL_TAC.mk_one_label (i + 1) avoid

/-- LABEL_ALL_TAC's local `mk_label`. -/
def LABEL_ALL_TAC.mk_label (avoid : List String) : String :=
  LABEL_ALL_TAC.mk_one_label 0 avoid

/-- update_label's local `f_at_i`. -/
def LABEL_ALL_TAC.f_at_i {α : Type} (f : α → α) : Int → List α → List α
  | _, [] => []
  | j, a :: b => if j = 0 then f a :: b else a :: LABEL_ALL_TAC.f_at_i f (j - 1) b

/-- LABEL_ALL_TAC's local `update_label`. -/
def LABEL_ALL_TAC.update_label (i : Nat) (asl : List (String × thm)) :
    Except String (List (String × thm)) := do
  let avoid := asl.map Prod.fst
  let current ← el i avoid
  let new_label := LABEL_ALL_TAC.mk_label avoid
  if current.length > 0 then pure asl else
    pure (LABEL_ALL_TAC.f_at_i (fun (_, y) => (new_label, y)) i asl)

/-- Give every unlabelled assumption a fresh label "Z-n". -/
def LABEL_ALL_TAC : tactic := fun (asl, w) => ExceptT.run do
  let aslp ← IO.mkRef asl
  for i in [0:asl.length] do
    aslp.set (← liftExcept (LABEL_ALL_TAC.update_label i (← aslp.get)))
  ExceptT.mk (ALL_TAC ((← aslp.get), w))

/- ---------------------------------------------------------------------- -/
/-  Term type inference (rqe_tactics_ext.ml 57-97)                        -/
/- ---------------------------------------------------------------------- -/

/-- get_var_list's local `get_var_list`: the names and types of all the
    variables and constants of a term. -/
def get_var_list.go : term → List (String × hol_type)
  | .Var name ty => [(name, ty)]
  | .Const name ty => [(name, ty)]
  | .Abs bv bod => union (get_var_list.go bv) (get_var_list.go bod)
  | .Comb s t => union (get_var_list.go s) (get_var_list.go t)

partial def auto_theta (new_type old_type : hol_type) :
    Except String (List (hol_type × hol_type)) :=
  let tyvar_prefix := "?"
  let is_generated (ty_name : String) : Except String Bool := do
    let first_char ← hd (explode ty_name)
    pure (if first_char == tyvar_prefix then true else false)
  match new_type with
  | .Tyvar ns =>
    (match old_type with
     | .Tyvar _ => do if ← is_generated ns then pure [(old_type, new_type)] else pure []
     | .Tyapp _ _ => pure [(old_type, new_type)])
  | .Tyapp new_ty_op new_ty_list =>
    (match old_type with
     | .Tyvar _ => pure []
     | .Tyapp old_ty_op old_ty_list =>
       if new_ty_op == old_ty_op then
         itlist2M (fun newt oldt b => do return union (← auto_theta newt oldt) b)
           new_ty_list old_ty_list []
       else pure [])

def auto_theta_list (newl : List (String × hol_type)) (oldl : List (String × hol_type)) :
    List (hol_type × hol_type) :=
  match newl with
  | [] => []
  | h :: t =>
    let head_list :=
      (match (do
          let (new_name, new_type) := h
          let old_type ← assoc new_name oldl
          auto_theta new_type old_type : Except String _) with
       | .ok v => v
       | .error _ => [])
    union head_list (auto_theta_list t oldl)

/-- auto_type_list's recursion, given `auto_type` (which reads a ref). -/
def auto_type_list.go (auto_type : term → term → IO term) (tm : term) :
    List term → IO term
  | [] => pure tm
  | h :: t => do auto_type_list.go auto_type (← auto_type tm h) t

/- ---------------------------------------------------------------------- -/
/-  Unfiled (rqe_tactics_ext.ml 142-263)                                  -/
/- ---------------------------------------------------------------------- -/

section
variable [HolBase]

def MATCH_EQ_MP_TAC (th : thm) : tactic := tactic_of do
  let (t1, t2) ← EQ_IMP_RULE (← SPEC_ALL th)
  pure (MATCH_MP_TAC t1 ORELSE MATCH_MP_TAC t2)

partial def REPEAT_N_CONV (n : Int) (conv : ioconv) : ioconv :=
  if n = 0 then ALL_CONV else conv THENC (REPEAT_N_CONV (n - 1) conv)

partial def REPEAT_N (n : Int) (tac : tactic) : tactic :=
  if n = 0 then ALL_TAC else tac THEN REPEAT_N (n - 1) tac

def dest_goal (g : goal) : List (String × thm) × term :=
  let (asms, conc) := g
  (asms, conc)

/-- rqe_tactics_ext.ml defines REWRITE_ASSUMS and ONCE_REWRITE_ASSUMS twice
    (192-193 and, identically, 210-211); one definition here. -/
def REWRITE_ASSUMS (thl : List thm) : tactic := RULE_ASSUM_TAC (REWRITE_RULE thl)
def ONCE_REWRITE_ASSUMS (thl : List thm) : tactic := RULE_ASSUM_TAC (ONCE_REWRITE_RULE thl)
def REWRITE_ALL (thl : List thm) : tactic := REWRITE_ASSUMS thl THEN REWRITE_TAC thl
def USE_IASSUM (n : Int) : thm_tactic → tactic :=
  USE_THEN ("Z-" ++ toString n)

def PROVE_ASSUM_ANTECEDENT_TAC (n : Int) : tactic := fun g => ExceptT.run do
  let (asl, _w) := g
  let assum ← liftExcept (assoc ("Z-" ++ toString n) asl)
  let (ant, _) ← liftExcept (dest_imp (concl assum))
  ExceptT.mk (SUBGOAL_THEN ant (fun x => USE_IASSUM n (fun y => tactic_of do
    pure (ASSUME_TAC (← MATCH_MP y x)))) g)

def FALSE_ANTECEDENT_TAC : tactic := fun g => ExceptT.run do
  let (_asl, w) := g
  let (l, _r) ← liftExcept (dest_imp w)
  ExceptT.mk ((SUBGOAL_THEN (← liftExcept (HolCore.Bool.mk_neg l)) (fun x => REWRITE_TAC [x])) g)

def REWRITE_ALL_TAC (l : List thm) : tactic := REWRITE_ASSUMS l THEN REWRITE_TAC l

partial def MATCH_MPL (thms : List thm) : ExceptT String IO thm :=
  match thms with
  | [th] => pure th
  | impl :: ant :: rest => do MATCH_MPL ((← MATCH_MP impl ant) :: rest)
  | _ => throw "Match_failure"

/-- MATCH_EQ_MPL's recursion, given MATCH_EQ_MP (a bundle field). -/
partial def MATCH_EQ_MPL.go (MATCH_EQ_MP : thm → thm → ExceptT String IO thm)
    (thms : List thm) : ExceptT String IO thm :=
  match thms with
  | [th] => pure th
  | impl :: ant :: rest => do MATCH_EQ_MPL.go MATCH_EQ_MP ((← MATCH_EQ_MP impl ant) :: rest)
  | _ => throw "Match_failure"

def USE_ASSUM_LIST (l : List String) (ttac : thm_tactic) : tactic := fun g => do
  let (asl, _w) := g
  let r ← (ExceptT.run (do
    let l' ← liftExcept (assoc_list l asl)
    let l'' := l'.map ttac
    ExceptT.mk ((EVERY l'') g)) : IO (Except String goalstate))
  match r with
  | .ok v => pure (.ok v)
  | .error _ => pure (.error "USE_ASSUM_LIST")

def KEEP (l : List String) : tactic := fun (asl, w) => do
  let r ← (ExceptT.run (do
    let asl' := filter (fun x => mem x.1 l) asl
    ExceptT.mk (ALL_TAC (asl', w))) : IO (Except String goalstate))
  match r with
  | .ok v => pure (.ok v)
  | .error _ => pure (.error "USE_ASSUM_LIST")

def PROVE_THM_ANTECEDENT_TAC (th : thm) : tactic := tactic_of do
  let (ant, _cons) ← liftExcept (dest_imp (concl th))
  pure (SUBGOAL_THEN ant (fun x => tactic_of do pure (MP_TAC (← MATCH_MP th x))))

def MOVE_TO_FRONT (s : String) : tactic := fun (asl, w) => ExceptT.run do
  let (k, asl') ← liftExcept (remove (fun x => x.1 == s) asl)
  ExceptT.mk (ALL_TAC (k :: asl', w))

def IGNORE {α : Type} (_x : α) : tactic := ALL_TAC

def DISCH_ASS : tactic := DISCH_THEN (fun x => ASSUME_TAC x THEN MP_TAC x)

end



/- ---------------------------------------------------------------------- -/
/-  Labels, refinement, term type inference and the tactics over them     -/
/-  (rqe_tactics_ext.ml 5-266: the bindings that use a ref, a theorem or  -/
/-  the session; the plain functions are above).                          -/
/- ---------------------------------------------------------------------- -/

structure RqeTacticsExtTactics where
  -- @@FIELDS
  labels_flag : Option (IO.Ref Bool)
  e : tactic → IO HolCore.Tactics.goalstack
  prove_by_refinement : term × List tactic → ExceptT String IO thm
  exclude_list : Option (IO.Ref (List String))
  get_var_list : term → IO (List (String × hol_type))
  auto_type : term → term → IO term
  auto_type_list : term → List term → IO term
  auto_type_goal : term → HolCore.Tactics.goal → IO term
  TYPE_TAC : (term → tactic) → term → tactic
  TYPE_TACL : (List term → tactic) → List term → tactic
  CLAIM : term → tactic
  lem : thm
  MATCH_EQ_MP : thm → thm → ExceptT String IO thm
  DISJ_LCASE : tactic
  DISJ_RCASE : tactic
  CASES_ON : term → tactic
  EXISTS_TAC : term → tactic
  MATCH_EQ_MPL : List thm → ExceptT String IO thm
  CCONTR_TAC : tactic
  pgoal : Unit → IO HolCore.Tactics.goalstack
  deriving Inhabited

@[nospecialize]
def setupRqeTacticsExtTactics [HolBase] (D : RqeTacticsExtDeps) :
    ExceptT String IO RqeTacticsExtTactics := do
  -- @@SCOPE BEGIN
  let { FALSITY_DEF, TAUT, refine, .. } := D
  let { EXCLUDED_MIDDLE, num_CASES, .. } := D.core1
  -- @@SCOPE END

  -- `let labels_flag = ref false` and `let exclude_list = ref [..]`: created
  -- once, when this (cached) setup runs at load, and closed over by the
  -- functions below.  Exported as `some ref`: a structure with an `IO.Ref`
  -- field cannot derive `Inhabited` computably, so the fields are `Option`s.
  let loc_labels_flag : IO.Ref Bool ← IO.mkRef false
  let labels_flag : Option (IO.Ref Bool) ← pure (some loc_labels_flag)

  let e : tactic → IO HolCore.Tactics.goalstack ← pure (fun tac => do
    let lf ← loc_labels_flag.get
    refine (HolCore.Tactics.by_ HolBase.B (HolCore.Tactics.VALID HolBase.B FALSITY_DEF
      (if lf then (tac THEN LABEL_ALL_TAC) else tac))))

  -- Refinement
  let prove_by_refinement : term × List tactic → ExceptT String IO thm ← pure (fun (t, tacl) => do
    let gstate ← liftExcept (HolCore.Tactics.mk_goalstate HolBase.B ([], t))
    let (_, sgs, just) ← tacl.foldlM (fun gs tac => do
        let lf ← loc_labels_flag.get
        ExceptT.mk (HolCore.Tactics.by_ HolBase.B
          (if lf then (tac THEN LABEL_ALL_TAC) else tac) gs)) gstate
    let th ← if sgs.isEmpty then ExceptT.mk (just HolCore.Tactics.null_inst [])
      else throw "BY_REFINEMENT_PROOF: Unsolved goals"
    let t' := concl th
    if t' == t then pure th else
    tryCatch (do EQ_MP (← liftExcept (HolCore.Equal.ALPHA t' t)) th)
      (fun _ => throw "prove_by_refinement: generated wrong theorem"))

  -- Term type inference
  let loc_exclude_list : IO.Ref (List String) ←
    IO.mkRef ["=", "FINITE", "COND", "@", "!", "?", "UNION", "DELETE", "CARD", "swap", "IN"]
  let exclude_list : Option (IO.Ref (List String)) ← pure (some loc_exclude_list)

  let get_var_list : term → IO (List (String × hol_type)) ← pure (fun tm => do
    let excl ← loc_exclude_list.get
    return filter (fun x => !(mem x.1 excl)) (get_var_list.go tm))

  let auto_type : term → term → IO term ← pure (fun new_tm old_tm => do
    let old_list ← get_var_list old_tm
    let new_list ← get_var_list new_tm
    let theta := auto_theta_list new_list old_list
    return inst theta new_tm)

  let auto_type_list : term → List term → IO term ← pure (auto_type_list.go auto_type)

  let auto_type_goal : term → HolCore.Tactics.goal → IO term ← pure (fun tm (asl, w) => do
    let thm_list := (unzip asl).2
    let term_list := thm_list.map (fun x => (dest_thm x).2)
    auto_type_list tm ([w] ++ term_list))

  let TYPE_TAC : (term → tactic) → term → tactic ← pure (fun f tm => fun g => do
    let typed_term ← auto_type_goal tm g
    f typed_term g)

  let TYPE_TACL : (List term → tactic) → List term → tactic ← pure (fun f tml => fun g => do
    let typed_terms ← tml.mapM (fun t => auto_type_goal t g)
    f typed_terms g)

  -- Unfiled
  let CLAIM : term → tactic ← pure (fun t =>
    TYPE_TAC (fun tm => SUBGOAL_THEN tm MP_TAC) t)

  let lem ← TAUT (← q r"(a = b) <=> (a ==> b) /\ (b ==> a)")
  let MATCH_EQ_MP : thm → thm → ExceptT String IO thm ← pure (fun t1 t2 =>
    tryCatch (EQ_MP t1 t2) (fun _ => do
      let k1 ← SPEC_ALL (← PURE_REWRITE_RULE [lem] t1)
      -- `left,right = CONJUNCT1 k1,CONJUNCT2 k1`, right to left
      let right ← CONJUNCT2 k1
      let left ← CONJUNCT1 k1
      tryCatch (MATCH_MP left t2) (fun _ =>
      tryCatch (MATCH_MP right t2) (fun _ =>
        throw "MATCH_EQ_MP"))))

  let DISJ_LCASE : tactic ← pure (fun g => ExceptT.run do
    let (_, c) := dest_goal g
    let (l, _r) ← liftExcept (dest_disj c)
    let th ← ISPEC l EXCLUDED_MIDDLE
    ExceptT.mk ((DISJ_CASES_TAC th THENL [
      DISJ1_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC,
      DISJ2_TAC
    ]) g))

  let DISJ_RCASE : tactic ← pure (fun g => ExceptT.run do
    let (_, c) := dest_goal g
    let (_l, r) ← liftExcept (dest_disj c)
    let th ← ISPEC r EXCLUDED_MIDDLE
    ExceptT.mk ((DISJ_CASES_TAC th THENL [
      DISJ2_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC,
      DISJ1_TAC
    ]) g))

  -- the first `CASES_ON`, which the second (TYPE_TAC-wrapped) rebinds
  let loc_CASES_ON : term → tactic ← pure (fun tm => tactic_of do
    let (ty, _) ← liftExcept (dest_type (type_of tm))
    match ty with
    | "num" =>
      pure (DISJ_CASES_TAC (← SPEC tm num_CASES) THENL
      [
        POP_ASSUM SUBST1_TAC,
        POP_ASSUM STRIP_ASSUME_TAC THEN POP_ASSUM SUBST1_TAC
      ])
    | "bool" =>
      pure (DISJ_CASES_TAC (← SPEC tm EXCLUDED_MIDDLE))
    | _ => throw "not a case type")

  let CASES_ON : term → tactic ← pure (fun t => TYPE_TAC loc_CASES_ON t)

  let EXISTS_TAC : term → tactic ← pure (fun t => TYPE_TAC EXISTS_TAC t)

  let MATCH_EQ_MPL : List thm → ExceptT String IO thm ← pure (MATCH_EQ_MPL.go MATCH_EQ_MP)

  let CCONTR_TAC : tactic ← do
    let t1 ← TAUT (← q r"(~x ==> F) ==> x")
    pure (MATCH_MP_TAC t1 THEN STRIP_TAC)

  let pgoal : Unit → IO HolCore.Tactics.goalstack ← pure (fun () =>
    D.current_goalstack.get)

  -- @@RETURN BEGIN
  return { labels_flag, e, prove_by_refinement, exclude_list, get_var_list, auto_type,
           auto_type_list, auto_type_goal, TYPE_TAC, TYPE_TACL, CLAIM, lem, MATCH_EQ_MP,
           DISJ_LCASE, DISJ_RCASE, CASES_ON, EXISTS_TAC, MATCH_EQ_MPL, CCONTR_TAC, pgoal }
  -- @@RETURN END

end HolRQE.RqeTacticsExt
