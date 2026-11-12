/- ========================================================================= -/
/- Rqe: conversions on list elements, REMOVE, CHOP_LIST and list lemmas.   -/
/- ========================================================================= -/
/- File: HolRQE/RqeList.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Rqe/rqe_list.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/analysis.ml, Library/poly.ml, Rqe/rqe_lib.ml, Rqe/rqe_tactics_ext.ml, Rqe/util.ml, Rqe/rewrites.ml, Rqe/basic.ml, Rqe/rqe_num.ml, Rqe/rqe_real.ml, Rqe/list_rewrites.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionRQE.RqeList fills them).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, INT_ARITH, TAUT, SET_RULE, ...) they are
  bound first, in OCaml's order.
-/

import HolLibrary.Analysis
import HolLibrary.Poly
import HolRQE.RqeLib
import HolRQE.RqeTacticsExt
import HolRQE.Util
import HolRQE.Rewrites
import HolRQE.Basic
import HolRQE.RqeNum
import HolRQE.RqeReal
import HolRQE.ListRewrites

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolRQE.RqeLib
open HolRQE.RqeTacticsExt
open HolRQE.Util
open HolRQE.Rewrites
open HolRQE.Basic
open HolRQE.RqeNum
open HolRQE.RqeReal
open HolRQE.ListRewrites

namespace HolRQE.RqeList

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (APPEND COND_CLAUSES HD LAST LENGTH LET_DEF LET_END_DEF LT_REFL MEM
   NOT_CONS_NIL NOT_NIL ONE TL list_CASES list_RECURSION num_RECURSION : thm)
  deriving Inhabited

/-- What rqe_list.ml uses from Session besides theorems. -/
structure RqeListDeps where
  new_definition : String → ExceptT String IO thm
  define : String → ExceptT String IO thm
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  new_recursive_definition : thm → String → ExceptT String IO thm
  LIST_INDUCT_TAC : tactic
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
  labels_flag : Option (IO.Ref Bool)
  prove_by_refinement : term × List tactic → ExceptT String IO thm
  exclude_list : Option (IO.Ref (List String))
  get_var_list : term → IO (List (String × hol_type))
  auto_type : term → term → IO term
  auto_type_list : term → List term → IO term
  auto_type_goal : term → HolCore.Tactics.goal → IO term
  TYPE_TAC : (term → tactic) → term → tactic
  TYPE_TACL : (List term → tactic) → List term → tactic
  CLAIM : term → tactic
  MATCH_EQ_MP : thm → thm → ExceptT String IO thm
  DISJ_LCASE : tactic
  DISJ_RCASE : tactic
  CASES_ON : term → tactic
  EXISTS_TAC : term → tactic
  MATCH_EQ_MPL : List thm → ExceptT String IO thm
  CCONTR_TAC : tactic
  pgoal : Unit → IO HolCore.Tactics.goalstack
  suppress : Option (IO.Ref (List String))
  get_type_list : term → IO (List (String × hol_type))
  set_types : term → IO (List (String × hol_type))
  print_term_types : term → IO Unit
  print_thm_types : thm → IO Unit
  goal_types : Unit → IO Unit
  assum : Int → ExceptT String IO term
  assum_types : Int → ExceptT String IO Unit
  get_type : String → thm → ExceptT String IO hol_type
  proof_stack : Option (IO.Ref (List HolCore.Tactics.goalstack))
  push_proof : term → IO HolCore.Tactics.goalstack
  pop_proof : Unit → ExceptT String IO HolCore.Tactics.goalstack
  NUM_REWRITES : Option (IO.Ref (List thm))
  NUM_SIMP_TAC : tactic
  extend_num_rewrites : List thm → IO Unit
  REAL_REWRITES : Option (IO.Ref (List thm))
  REAL_ELIM : Option (IO.Ref (List thm))
  REAL_SIMP_TAC : tactic
  REAL_SOLVE_TAC : tactic
  extend_real_rewrites : List thm → IO Unit
  BASIC_REWRITES : Option (IO.Ref (List thm))
  dest_beq : term → Except String (term × term)
  t_tm : term
  f_tm : term
  nqt : term
  mk_neq : term × term → Except String term
  neq : term
  nlt : term
  ngt : term
  nle : term
  nge : term
  nm : term
  np : term
  nzero : term
  even_tm : term
  odd_tm : term
  PARITY_CONV : term → ExceptT String IO thm
  real_ty : hol_type
  rx : term
  ry : term
  rz : term
  req : term
  rneq : term
  rlt : term
  rgt : term
  rle : term
  rge : term
  rm : term
  rs : term
  rn : term
  rd : term
  rp : term
  rzero : term
  rone : term
  rlast : term
  rappend : term
  mk_rlist : List term → IO (Except String term)
  diffl_tm : term
  dest_diffl : term → Except String (term × term)
  dest_mult : term → Except String (term × term)
  mk_mult : term → Except String (term → Except String term)
  pow_tm : term
  dest_pow : term → Except String (term × term)
  mk_plus : term → Except String (term → Except String term)
  mk_negative : term → Except String term
  dest_plus : term → Except String (term × term)
  LIST_REWRITES : Option (IO.Ref (List thm))
  LIST_SIMP_TAC : tactic
  extend_list_rewrites : List thm → IO Unit
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

/-- EL_CONV's recursion, given rqe_list.ml's `aacons_tm` and `HD_CONV`
    (bundle fields). -/
partial def EL_CONV.go [HolBase] (aacons_tm : term) (HD_CONV : ioconv → ioconv)
    (conv : ioconv) (i : Int) : ioconv := fun tm =>
  if i = 0 then HD_CONV conv tm
  else ExceptT.run do
    let (h, t) ← match ← liftExcept (dest_list tm) with
      | h :: t => pure (h, t)
      | [] => throw "Match_failure"
    let lty := type_of h
    let cs := inst [(lty, aty)] aacons_tm
    -- `MK_COMB ((AP_TERM ..), (EL_CONV ..))`: the pair right to left
    let th2 ← ExceptT.mk (EL_CONV.go aacons_tm HD_CONV conv (i - 1)
      (← ExceptT.mk (HolMath.Lists.mk_list t lty)))
    MK_COMB ((← AP_TERM cs (REFL h)), th2)



/- ---------------------------------------------------------------------- -/
/-  Lists (rqe_list.ml 1-313)                                             -/
/- ---------------------------------------------------------------------- -/

structure RqeListThms where
  -- @@FIELDS
  aacons_tm : term
  HD_CONV : ioconv → ioconv
  TL_CONV : ioconv → ioconv
  EL_CONV : ioconv → Int → ioconv
  NOT_CONS : thm
  REMOVE : thm
  CHOP_LIST : thm
  REM_NIL : thm
  REM_FALSE : thm
  MEM_REMOVE : thm
  REM_NEQ : thm
  LAST_SING : thm
  LAST_CONS : thm
  LAST_CONS_CONS : thm
  HD_APPEND : thm
  LENGTH_0 : thm
  LENGTH_1 : thm
  LIST_TRI : thm
  LENGTH_PAIR : thm
  LENGTH_SING : thm
  TL_NIL : thm
  LAST_TL : thm
  LENGTH_TL : thm
  LENGTH_NZ : thm
  deriving Inhabited

@[nospecialize]
def setupRqeListThms [HolBase] (D : RqeListDeps) :
    ExceptT String IO RqeListThms := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, CASES_ON, CLAIM, EXISTS_TAC,
        LIST_INDUCT_TAC, LIST_REWRITES, LIST_SIMP_TAC, MESON_TAC, NUM_SIMP_TAC,
        new_recursive_definition, prove_by_refinement, .. } := D
  let { APPEND, COND_CLAUSES, HD, LAST, LENGTH, LET_DEF, LET_END_DEF, LT_REFL, MEM,
        NOT_CONS_NIL, NOT_NIL, ONE, TL, list_CASES, list_RECURSION, num_RECURSION, .. } := D.core1
  -- @@SCOPE END

  let aacons_tm : term ← q r"CONS:A -> A list -> A list"
  -- `let h::rest = dest_list tm`: an empty list is OCaml's Match_failure
  let HD_CONV : ioconv → ioconv ← pure (fun conv tm => ExceptT.run do
    let (h, rest) ← match ← liftExcept (dest_list tm) with
      | h :: rest => pure (h, rest)
      | [] => throw "Match_failure"
    let ty := type_of h
    let thm ← ExceptT.mk (conv h)
    let thm2 := REFL (← ExceptT.mk (HolMath.Lists.mk_list rest ty))
    let cs := inst [(ty, aty)] aacons_tm
    MK_COMB ((← AP_TERM cs thm), thm2))

  let TL_CONV : ioconv → ioconv ← pure (fun conv tm => ExceptT.run do
  /-   try -/
    let (h, t) ← match ← liftExcept (dest_list tm) with
      | h :: t => pure (h, t)
      | [] => throw "Match_failure"
    let lty := type_of h
    let cs := inst [(lty, aty)] aacons_tm
    -- the pair right to left
    let th2 ← ExceptT.mk (HolMath.Lists.LIST_CONV_IO conv
      (← ExceptT.mk (HolMath.Lists.mk_list t lty)))
    MK_COMB ((← AP_TERM cs (REFL h)), th2))
  /-   with _ -> failwith "TL_CONV" -/

  let EL_CONV : ioconv → Int → ioconv ← pure (EL_CONV.go aacons_tm HD_CONV)


  /-

    let conv = (REWRITE_CONV[ARITH_RULE `x + x = &2 * x`])
    let tm = `[&5 + &5; &6 + &6; &7 + &7]`
    HD_CONV conv tm
    TL_CONV conv tm
    HD_CONV(TL_CONV conv) tm
    CONS_CONV conv tm
    EL_CONV conv 0 tm
    EL_CONV conv 1 tm
    EL_CONV conv 2 tm

  -/

  let NOT_CONS ← prove_by_refinement (
    (← q r"!l. (~ ?(h:A) t. (l = CONS h t)) ==> (l = [])"),
  /- {{{ Proof -/

  [
    MESON_TAC [list_CASES]
  ])

  /- }}} -/

  let REMOVE ← new_recursive_definition list_RECURSION
    r"(REMOVE x [] = []) /\
     (REMOVE x (CONS (h:A) t) =
       let rest = REMOVE x t in
         if x = h then rest else CONS h rest)"

  let CHOP_LIST ← new_recursive_definition num_RECURSION
    r"(CHOP_LIST 0 l = [],l) /\
     (CHOP_LIST (SUC n) l =
       let a,b = CHOP_LIST n (TL l) in
        CONS (HD l) a,b)"

  let REM_NIL ← prove
   r"REMOVE x [] = []"
   (MESON_TAC [REMOVE])

  let REM_FALSE ← prove_by_refinement (
   (← q r"!x l. ~(MEM x (REMOVE x l))"),
  /- {{{ Proof -/
  [
   STRIP_TAC,
   LIST_INDUCT_TAC,
   ASM_MESON_TAC [MEM, REM_NIL],
   CASES_ON (← q r"x = h"),
   ASM_REWRITE_TAC [],
   ASM_REWRITE_TAC [REMOVE, LET_DEF, LET_END_DEF],
   ASM_MESON_TAC [],
   ASM_REWRITE_TAC [REMOVE, LET_DEF, LET_END_DEF],
   ASM_MESON_TAC [MEM]
  ])
  /- }}} -/

  let MEM_REMOVE ← prove_by_refinement (
    (← q r"!x y z l. MEM x (REMOVE y l) ==> MEM x (REMOVE y (CONS z l))"),
  /- {{{ Proof -/
  [
    REPEAT_N 3 STRIP_TAC,
    CASES_ON (← q r"y = z"),
    ASM_REWRITE_TAC [REMOVE, LET_DEF, LET_END_DEF],
    ASM_REWRITE_TAC [REMOVE, LET_DEF, LET_END_DEF],
    ASM_MESON_TAC [MEM]
  ])
  /- }}} -/

  let REM_NEQ ← prove_by_refinement (
    (← q r"!x x1 l. MEM x l /\ ~(x = x1) ==> MEM x (REMOVE x1 l)"),
  /- {{{ Proof -/
  [
    STRIP_TAC THEN STRIP_TAC,
    LIST_INDUCT_TAC,
    MESON_TAC [MEM],
    CASES_ON (← q r"x = h"),
    POP_ASSUM SUBST1_TAC,
    STRIP_TAC,
    ASM_REWRITE_TAC [REMOVE, LET_DEF, LET_END_DEF, COND_CLAUSES, MEM],
    STRIP_TAC,
    CLAIM (← q r"MEM x t"),
    ASM_MESON_TAC [MEM],
    STRIP_TAC,
    CLAIM (← q r"MEM x (REMOVE x1 t)"),
    ASM_MESON_TAC [],
    STRIP_TAC,
    MATCH_MP_TAC MEM_REMOVE,
    FIRST_ASSUM MATCH_ACCEPT_TAC
  ])
  /- }}} -/


  let LAST_SING ← prove_by_refinement (
    (← q r"!h. LAST [h] = h"),
  /- {{{ Proof -/

  [
    MESON_TAC [LAST]
  ])

  /- }}} -/

  let LAST_CONS ← prove_by_refinement (
    (← q r"!h t. ~(t = []) ==> (LAST (CONS h t) = LAST t)"),
  /- {{{ Proof -/
  [
    ASM_MESON_TAC [LAST]
  ])
  /- }}} -/


  let LAST_CONS_CONS ← prove_by_refinement (
    (← q r"!h1 h2 t. ~(t = []) ==> (LAST (CONS h1 (CONS h2 t)) = LAST (CONS h1 t))"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [LAST, NOT_CONS_NIL],
    MESON_TAC [LAST, NOT_CONS_NIL, COND_CLAUSES]
  ])
  /- }}} -/

  let HD_APPEND ← prove_by_refinement (
    (← q r"!h t l. HD (APPEND (CONS h t) l) = h"),
  /- {{{ Proof -/
  [
    ASM_MESON_TAC [HD, APPEND]
  ])
  /- }}} -/

  let LENGTH_0 ← do
    let a1 ← ARITH_RULE (← q r"~(0 = SUC n)")
    prove_by_refinement (
    (← q r"!l. (LENGTH l = 0) <=> (l = [])"),
  /- {{{ Proof -/
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [LENGTH],
    ASM_MESON_TAC [LENGTH, NOT_CONS_NIL, a1]
  ])
  /- }}} -/

  let LENGTH_1 ← do
    -- the ARITH_RULEs of the tactic list, right to left
    let a2 ← ARITH_RULE (← q r"~(0 = 1)")
    let a1 ← ARITH_RULE (← q r"~(1 = 0)")
    prove_by_refinement (
    (← q r"!l. (LENGTH l = 1) <=> ?x. l = [x]"),
  /- {{{ Proof -/
  [
    LIST_INDUCT_TAC,
    EQ_TAC,
    MESON_TAC [LENGTH, a1],
    MESON_TAC [NOT_CONS_NIL],
    EQ_TAC,
    REWRITE_TAC [LENGTH, a2],
    REWRITE_TAC [LENGTH],
    STRIP_TAC,
    CLAIM (← q r"LENGTH t = 0"),
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    STRIP_TAC,
    CLAIM (← q r"t = []"),
    ASM_MESON_TAC [LENGTH_0],
    STRIP_TAC,
    ASM_REWRITE_TAC [],
    ASM_MESON_TAC [],
    STRIP_TAC,
    ASM_MESON_TAC [LENGTH, ONE]
  ])
  /- }}} -/

  let LIST_TRI ← prove_by_refinement (
    (← q r"!p. (p = []) \/ (?x. p = [x:A]) \/ (?x y t. p = CONS x (CONS y t))"),
  /- {{{ Proof -/
  [
    STRIP_TAC,
    DISJ_CASES_TAC (← ISPEC (← q r"p:A list") list_CASES),
    ASM_REWRITE_TAC [],
    POP_ASSUM MP_TAC THEN STRIP_TAC,
    DISJ_CASES_TAC (← ISPEC (← q r"t:A list") list_CASES),
    ASM_MESON_TAC [],
    ASM_MESON_TAC []
  ])
  /- }}} -/

  let LENGTH_PAIR ← do
    -- the ARITH_RULEs of the tactic list, right to left
    let a2 ← ARITH_RULE (← q r"~(1 = 2)")
    let a1 ← ARITH_RULE (← q r"~(2 = 0)")
    prove_by_refinement (
    (← q r"!p. (LENGTH p = 2) <=> ?h t. p = [h:A; t]"),
  /- {{{ Proof -/
  [
    STRIP_TAC THEN EQ_TAC,
    STRIP_TAC,
    MP_TAC (← ISPEC (← q r"p:A list") list_CASES),
    STRIP_TAC,
    ASM_MESON_TAC [LENGTH_0, a1],
    MP_TAC (← ISPEC (← q r"t:A list") list_CASES),
    STRIP_TAC,
    ASM_MESON_TAC [LENGTH_1, a2],
    MP_TAC (← ISPEC (← q r"t':A list") list_CASES),
    STRIP_TAC,
    EXISTS_TAC (← q r"h:A"),
    EXISTS_TAC (← q r"h':A"),
    ASM_MESON_TAC [],
    CLAIM (← q r"p = CONS h (CONS h' (CONS h'' t''))"),
    ASM_MESON_TAC [],
    STRIP_TAC,
    CLAIM (← q r"2 < LENGTH p"),
    POP_ASSUM SUBST1_TAC,
    REWRITE_TAC [LENGTH],
    ARITH_TAC,
    ASM_MESON_TAC [LT_REFL],
    STRIP_TAC,
    ASM_REWRITE_TAC [LENGTH],
    ARITH_TAC
  ])
  /- }}} -/

  let LENGTH_SING ← do
    let a1 ← ARITH_RULE (← q r"~(1 = 0)")
    prove_by_refinement (
    (← q r"!p. (LENGTH p = 1) <=> ?h. p = [h:A]"),
  /- {{{ Proof -/
  [
    STRIP_TAC THEN EQ_TAC,
    STRIP_TAC,
    MP_TAC (← ISPEC (← q r"p:A list") list_CASES),
    STRIP_TAC,
    ASM_MESON_TAC [LENGTH_0, a1],
    MP_TAC (← ISPEC (← q r"t:A list") list_CASES),
    STRIP_TAC,
    EXISTS_TAC (← q r"h:A"),
    ASM_MESON_TAC [],
    CLAIM (← q r"p = CONS h (CONS h' t')"),
    ASM_MESON_TAC [],
    STRIP_TAC,
    CLAIM (← q r"1 < LENGTH p"),
    POP_ASSUM SUBST1_TAC,
    REWRITE_TAC [LENGTH],
    ARITH_TAC,
    ASM_REWRITE_TAC [],
    ARITH_TAC,
    STRIP_TAC,
    ASM_REWRITE_TAC [LENGTH],
    ARITH_TAC
  ])
  /- }}} -/

  let TL_NIL ← prove_by_refinement (
    (← q r"!l. ~(l = []) ==> ((TL l = []) <=> ?x. l = [x])"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC THEN EQ_TAC,
    CLAIM (← q r"?h t. l = CONS h t"),
    ASM_MESON_TAC [list_CASES],
    STRIP_TAC,
    ASM_REWRITE_TAC [TL],
    ASM_MESON_TAC (← deref LIST_REWRITES),
    ASM_MESON_TAC (← deref LIST_REWRITES)
  ])
  /- }}} -/

  let LAST_TL ← prove_by_refinement (
    (← q r"!l. ~(l = []) /\  ~(TL l = []) ==> (LAST (TL l) = LAST l)"),
  /- {{{ Proof -/
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [],
    REWRITE_TAC [TL, LAST],
    ASM_MESON_TAC [NOT_CONS_NIL]
  ])
  /- }}} -/

  let LENGTH_TL ← prove_by_refinement (
    (← q r"!l. ~(l = []) /\  ~(TL l = []) ==> (LENGTH (TL l) = PRE(LENGTH l))"),
  /- {{{ Proof -/
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [],
    REPEAT STRIP_TAC,
    LIST_SIMP_TAC,
    NUM_SIMP_TAC
  ])
  /- }}} -/

  let LENGTH_NZ ← prove_by_refinement (
   (← q r"!p. 0 < LENGTH p <=> ~(p = [])"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    EQ_TAC,
    ASM_MESON_TAC [LENGTH, NOT_CONS_NIL, LT_REFL],
    REWRITE_TAC [LENGTH, NOT_CONS_NIL, LT_REFL, NOT_NIL],
    STRIP_TAC THEN ASM_REWRITE_TAC [],
    REWRITE_TAC [LENGTH],
    ARITH_TAC
  ])
  /- }}} -/

  -- @@RETURN BEGIN
  return { aacons_tm, HD_CONV, TL_CONV, EL_CONV, NOT_CONS, REMOVE, CHOP_LIST, REM_NIL,
           REM_FALSE, MEM_REMOVE, REM_NEQ, LAST_SING, LAST_CONS, LAST_CONS_CONS,
           HD_APPEND, LENGTH_0, LENGTH_1, LIST_TRI, LENGTH_PAIR, LENGTH_SING, TL_NIL,
           LAST_TL, LENGTH_TL, LENGTH_NZ }
  -- @@RETURN END

end HolRQE.RqeList
