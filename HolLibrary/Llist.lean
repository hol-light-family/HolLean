/- ========================================================================= -/
/- Lazy lists (finite or infinite sequences) as a datatype, with coinductive -/
/- definitions and proofs by coinduction and bisimulation.                   -/
/- ========================================================================= -/
/- File: HolLibrary/Llist.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/llist.ml` (e5236a5), in file order,
  one Lean `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ll/ml2lean.py (disclosed; the user agreed to the scripts,
  2026-11-13) and checked against the .ml (quotations and tokens) and by
  tools/llistdiff; the tactics LLIST_REP_CASES_TAC, LLIST_CASES_TAC,
  LLIST_COINDUCT_UNFOLD_TAC, LLIST_COINDUCT_TAC and LLIST_BISIM_TAC and the
  `monotonicity_theorems` updates are by hand.  llist.ml begins with
  `needs "Library/iter.ml"` (HolLibrary.Iter); the theorems it uses from it
  and from the core library are supplied via the CoreThms structures
  (SessionLibrary.Llist fills them).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left.  The `do` macro of HolCore/OcamlOrder.lean
  (HolLight.Syntax) binds each statement's `(← ...)` actions in that order,
  so quotations and rules (MESON, ARITH_RULE, ...) run as in HOL Light;
  where a rule is bound by a `let` before the proof, it is bound in OCaml's
  order.
-/

import HolLibrary.Iter

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolLibrary.Llist

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD_CLAUSES ALL2 APPEND APPEND_NIL CONS_11 EL EL_APPEND EL_LIST_OF_SEQ EL_MAP
   EQ_IMP ETA_AX EXISTS_IN_IMAGE EXISTS_IN_INSERT EXTENSION FILTER
   FORALL_IN_IMAGE FORALL_IN_INSERT FST FUN_EQ_THM HD IMP_CONJ INSERT_UNION_EQ
   IN_ELIM_THM IN_IMAGE IN_INSERT IN_UNIV ITER ITER_ALT LEFT_IMP_EXISTS_THM
   LENGTH LENGTH_APPEND LENGTH_LIST_OF_SEQ LENGTH_MAP LE_ANTISYM LE_REFL LIST_EQ
   LIST_OF_SEQ LT LT_0 LT_NZ LT_REFL LT_SUC MAP MAP_ID MAP_o MINIMAL
   NOT_CONS_NIL NOT_FORALL_THM NOT_IN_EMPTY NOT_LT NOT_SUC PAIR_EQ
   RIGHT_FORALL_IMP_THM SELECT_UNIQUE SND SUBSET SUBSET_REFL SUB_0 SUB_SUC
   SUC_INJ SUC_SUB1 SWAP_FORALL_THM TL UNION_EMPTY list_CASES list_of_seq
   num_CASES o_ASSOC o_DEF o_THM option_DISTINCT option_INDUCT option_INJ
   option_RECURSION set_of_list : thm)
  deriving Inhabited

/-- What llist.ml uses from Session besides theorems. -/
structure LlistDeps where
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
  define_type : String → ExceptT String IO (thm × thm)
  new_inductive_definition : String → ExceptT String IO (thm × thm × thm)
  get_monotonicity_theorems : IO (List thm)  -- !monotonicity_theorems
  set_monotonicity_theorems : List thm → IO Unit  -- monotonicity_theorems := ..
  GEN_BETA_CONV : ioconv
  SELECT_CONV : ioconv
  cases : String → ExceptT String IO thm
  distinctness : String → ExceptT String IO thm
  injectivity : String → ExceptT String IO thm
  core1 : CoreThms1

/-- RingTheory's `wPart` (copied verbatim).  `W(MP_TAC o PART_MATCH f th o g
    o snd)`: match `th`'s part `f` against the part `g` of the goal, and
    MP_TAC the instance. -/
def wPart [HolBase] (g : term → Except String term) (f : term → Except String term)
    (th : thm) : tactic := fun gl =>
  ExceptT.run do
    let t ← liftExcept (g gl.2)
    ExceptT.mk (MP_TAC (← PART_MATCH f th t) gl)

/-- llist.ml's `LLIST_COINDUCT_UNFOLD_TAC thl` (llist.ml 366-400), by hand,
    with the file's LLIST_STRONG_COINDUCT passed in (the bundle binds
    `LLIST_COINDUCT_UNFOLD_TAC` to this at its place in the file).  The goal
    `!vs. [hyps ==>] l = r` is proved by strong coinduction with the relation
    `\l1 l2. ?vs. [hyps /\] l1 = l /\ l2 = r`; the hypotheses `l1 = ..` and
    `l2 = ..` are substituted, each first rewritten once with `thl` (on its
    right) when `thl` is not empty.  `PURE_ONCE_REWRITE_CONV thl` is built
    when the tactic runs (OCaml builds it at the partial application; with no
    basic rewrites the result is the same). -/
def LLIST_COINDUCT_UNFOLD_TAC_with [HolBase] (LLIST_STRONG_COINDUCT : thm)
    (thl : List thm) : tactic := fun (asl, w) => ExceptT.run do
  let galpha (v : term) : ioconv := fun t => pure (HolCore.Equal.GEN_ALPHA_CONV v t)
  let unfold : thm → ExceptT String IO thm := fun th =>
    if thl.isEmpty then pure th
    else do CONV_RULE (RAND_CONV (← PURE_ONCE_REWRITE_CONV_NET thl)) th
  -- `prove_exists tm wits th`
  let rec prove_exists (tm : term) (wits : List term) (th : thm) : ExceptT String IO thm :=
    match wits with
    | [] => pure th
    | w :: ws => do
      let (x, b) ← liftExcept (dest_exists tm)
      let b' := (← liftExcept (vsubst [(w, x)])) b
      EXISTS (tm, w) (← prove_exists b' ws th)
  let (vs, bod) := strip_forall w
  let (hyps, eqn) ← if is_imp bod then liftExcept (dest_imp bod) else pure ((← q "T"), bod)
  let (l, r) ← liftExcept (dest_eq eqn)
  let ty := type_of l
  let avoids := HolCore.Lib.itlist (fun (a : String × thm) acc =>
    HolCore.Lib.union (frees (concl a.2)) acc) asl (← liftExcept (variables w))
  let names ← avoids.mapM (fun v => liftExcept (do pure (← dest_var v).1))
  let rec fresh (s : String) (fuel : Nat) : String :=
    match fuel with
    | 0 => s
    | fuel + 1 => if names.contains s then fresh (s ++ "'") fuel else s
  let l1 := mk_var (fresh "l1" (names.length + 1)) ty
  let l2 := mk_var (fresh "l2" (names.length + 1)) ty
  -- mk_eq cannot fail here: l1 and l2 have the types of l and r
  let eqs ← liftExcept (HolCore.Bool.mk_conj (safe_mk_eq l1 l) (safe_mk_eq l2 r))
  let body ← if is_imp bod then liftExcept (HolCore.Bool.mk_conj hyps eqs) else pure eqs
  let rel ← liftExcept (list_mk_abs [l1, l2] (← liftExcept (HolCore.Bool.list_mk_exists vs body)))
  let th ← CONV_RULE
    (LAND_CONV (galpha l1 THENC BINDER_CONV (galpha l2)) THENC
     TOP_DEPTH_CONV BETA_CONV) (← ISPEC rel LLIST_STRONG_COINDUCT)
  let ant ← liftExcept (lhand (concl th))
  let th2 ← SPECL [l, r] (← UNDISCH th)
  let rth ← CONJ (REFL l) (REFL r)
  let bth ← if is_imp bod then CONJ (← ASSUME hyps) rth else pure rth
  let th3 ← MP th2 (← prove_exists (← liftExcept (lhand (concl th2))) vs bth)
  let th4 ← GENL vs (← if is_imp bod then DISCH hyps th3 else pure th3)
  let is_sub (th : thm) : Bool :=
    let c := concl th
    is_eq c && (match lhs c with | .ok x => x == l1 || x == l2 | .error _ => false)
  ExceptT.mk ((MATCH_MP_TAC (← DISCH ant th4) THEN X_GEN_TAC l1 THEN X_GEN_TAC l2 THEN
    DISCH_THEN (REPEAT_TCL CHOOSE_THEN
      (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
    REPEAT (FIRST_X_ASSUM (fun th => tactic_of do
      if !(is_sub th) then throw "check"
      pure (SUBST_ALL_TAC (← unfold th))))) (asl, w))

/- ---------------------------------------------------------------------- -/
/- llist.ml phrases from line 22 to 917                                   -/
/- ---------------------------------------------------------------------- -/

structure Llist01 where
  -- @@FIELDS
  THE : thm
  OPTION_MAP : thm
  option_CASES : thm
  OPTION_MAP_EQ_NONE : thm
  OPTION_MAP_EQ_SOME : thm
  OPTION_MAP_ID : thm
  OPTION_MAP_o : thm
  llist_INDUCT : thm
  llist_RECURSION : thm
  LLIST_OF_LIST_11 : thm
  LLIST_OF_SEQ_11 : thm
  LLIST_OF_LIST_NEQ_SEQ : thm
  LLIST_LIST_OR_SEQ : thm
  LLIST_REP_EQ : thm
  LLIST_REP_CASES_TAC : term → tactic
  LNIL_DEF : thm
  LCONS_DEF : thm
  LLIST_OF_LIST : thm
  LNTH_DEF : thm
  LNTH : thm
  LLIST_EQ : thm
  LLIST_OF_SEQ : thm
  LLIST_CASES : thm
  NOT_LCONS_LNIL : thm
  LCONS_11 : thm
  LHD_DEF : thm
  LHD : thm
  LTL_DEF : thm
  LTL : thm
  LCONS_LHD_LTL : thm
  LNTH_NONE_MONO : thm
  LAPPEND_DEF : thm
  LAPPEND : thm
  LCOREC_DEF : thm
  LCOREC : thm
  LCOREC_UNIQUE : thm
  LUNFOLD_DEF : thm
  LUNFOLD : thm
  LUNFOLD_UNIQUE : thm
  LLIST_COINDUCT : thm
  LLIST_STRONG_COINDUCT : thm
  LLIST_CASES_TAC : term → tactic
  LLIST_COINDUCT_UNFOLD_TAC : List thm → tactic
  LLIST_COINDUCT_TAC : tactic
  LLIST_BISIM_REFL : thm
  LLIST_BISIM_LCONS : thm
  LLIST_BISIM_TAC : tactic
  LNTH_LLIST_OF_LIST : thm
  LNTH_LLIST_OF_SEQ : thm
  list_of_llist : thm
  LFINITE_DEF : thm
  LFINITE_LCONS : thm
  LFINITE_RULES : thm
  LFINITE_INDUCT : thm
  LFINITE_CASES : thm
  LFINITE_LTL : thm
  LFINITE_LLIST_OF_LIST : thm
  NOT_LFINITE_LLIST_OF_SEQ : thm
  LFINITE_LNTH : thm
  LLIST_OF_LIST_OF_LLIST : thm
  NOT_LFINITE_COINDUCT : thm
  LLENGTH_DEF : thm
  LLENGTH : thm
  LLENGTH_EQ_NONE : thm
  LLENGTH_LLIST_OF_LIST : thm
  LMAP_DEF : thm
  LMAP : thm
  LMAP_LLIST_OF_LIST : thm
  LMAP_LLIST_OF_SEQ : thm
  LMAP_ID : thm
  LMAP_o : thm
  LMAP_EQ_LNIL : thm
  LNTH_LMAP : thm
  LFINITE_LMAP : thm
  LLENGTH_LMAP : thm
  LAPPEND_LLIST_OF_LIST : thm
  LAPPEND_LNIL : thm
  LAPPEND_ASSOC : thm
  LAPPEND_INFINITE : thm
  LFINITE_LAPPEND : thm
  LMAP_LAPPEND : thm
  LNTH_LAPPEND : thm
  LAPPEND_EQ_LNIL : thm
  LTAKE_DEF : thm
  LTAKE : thm
  LDROP_DEF : thm
  LDROP_LNIL : thm
  LDROP : thm
  LTAKE_LDROP : thm
  LNTH_LDROP : thm
  LDROP_ADD : thm
  LNTH_LTAKE : thm
  LLIST_EQ_LTAKE : thm
  LTAKE_LLIST_OF_SEQ : thm
  LDROP_LLIST_OF_SEQ : thm
  set_of_llist : thm
  IN_SET_OF_LLIST : thm
  LNTH_LCONS_EXISTS : thm
  SET_OF_LLIST : thm
  SET_OF_LLIST_LLIST_OF_LIST : thm
  SET_OF_LLIST_LLIST_OF_SEQ : thm
  SET_OF_LLIST_LMAP : thm
  SET_OF_LLIST_LAPPEND : thm
  LALL_DEF : thm
  LEXISTS_DEF : thm
  LALL_SET_OF_LLIST : thm
  LEXISTS_SET_OF_LLIST : thm
  LALL : thm
  LEXISTS : thm
  LEXISTS_LALL : thm
  LALL_LMAP : thm
  LEXISTS_LMAP : thm
  LALL_COINDUCT : thm
  LEXISTS_INDUCT : thm
  MONO_LALL : thm
  MONO_LEXISTS : thm
  LFIRST_RULES : thm
  LFIRST_INDUCT : thm
  LFIRST_CASES : thm
  LFIRST_UNIQUE : thm
  LFIRST_EXISTS : thm
  LFIRST_LCONS : thm
  LFIRST_SUBSET : thm
  LFIRST_LEXISTS : thm
  lfirst : thm
  LFIRST_LFIRST : thm
  LFIRST_EQ : thm
  LFIRST_LCONS_P : thm
  LFIRST_LCONS_NOTP : thm
  LFILTER_DEF : thm
  LFILTER_UNFOLD : thm
  LFILTER : thm
  LFILTER_EQ_LNIL : thm
  LFILTER_LAPPEND : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupLlist01 [HolBase] (D : LlistDeps) :
    ExceptT String IO Llist01 := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, LIST_INDUCT_TAC, MESON, MESON_TAC,
        SET_TAC, cases, define, define_type, distinctness, get_monotonicity_theorems,
        injectivity, new_definition, new_inductive_definition,
        new_recursive_definition, set_monotonicity_theorems, .. } := D
  let { ADD_CLAUSES, APPEND, APPEND_NIL, EL, EL_APPEND, EL_MAP, ETA_AX,
        EXISTS_IN_IMAGE, EXISTS_IN_INSERT, EXTENSION, FORALL_IN_IMAGE,
        FORALL_IN_INSERT, FUN_EQ_THM, HD, IMP_CONJ, INSERT_UNION_EQ, IN_ELIM_THM,
        IN_IMAGE, IN_INSERT, IN_UNIV, ITER, ITER_ALT, LENGTH, LENGTH_APPEND,
        LENGTH_MAP, LE_ANTISYM, LIST_EQ, LIST_OF_SEQ, LT, LT_0, LT_NZ, LT_REFL, LT_SUC,
        MAP, MAP_ID, MAP_o, MINIMAL, NOT_CONS_NIL, NOT_FORALL_THM, NOT_IN_EMPTY,
        NOT_LT, NOT_SUC, RIGHT_FORALL_IMP_THM, SUBSET_REFL, SUB_0, SUB_SUC, SUC_INJ,
        SUC_SUB1, SWAP_FORALL_THM, TL, UNION_EMPTY, list_CASES, list_of_seq, num_CASES,
        o_ASSOC, o_DEF, o_THM, option_DISTINCT, option_INDUCT, option_INJ,
        option_RECURSION, set_of_list, .. } := D.core1
  -- @@SCOPE END

  let THE ← new_recursive_definition option_RECURSION
    r"THE(SOME (x:A)) = x"

  let OPTION_MAP ← new_recursive_definition option_RECURSION
    r"(!f. OPTION_MAP (f:A->B) NONE = NONE) /\
  (!f x. OPTION_MAP (f:A->B) (SOME x) = SOME (f x))"

  let option_CASES ← prove
    r"!x:A option. x = NONE \/ ?a. x = SOME a"
    (MATCH_MP_TAC option_INDUCT THEN MESON_TAC [])

  let OPTION_MAP_EQ_NONE ← prove
    r"!(f:A->B) x. OPTION_MAP f x = NONE <=> x = NONE"
    (GEN_TAC THEN MATCH_MP_TAC option_INDUCT THEN REWRITE_TAC [OPTION_MAP, option_DISTINCT])

  let OPTION_MAP_EQ_SOME ← prove
    r"!(f:A->B) x y. OPTION_MAP f x = SOME y <=> ?a. x = SOME a /\ y = f a"
    (GEN_TAC THEN MATCH_MP_TAC option_INDUCT THEN REWRITE_TAC [OPTION_MAP, option_DISTINCT, option_INJ] THEN MESON_TAC [])

  let OPTION_MAP_ID ← prove
    r"!x:A option. OPTION_MAP (\a. a) x = x"
    (MATCH_MP_TAC option_INDUCT THEN REWRITE_TAC [OPTION_MAP])

  let OPTION_MAP_o ← prove
    r"!(f:B->C) (g:A->B) x.
        OPTION_MAP f (OPTION_MAP g x) = OPTION_MAP (f o g) x"
    (GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC option_INDUCT THEN REWRITE_TAC [OPTION_MAP, o_THM])

  let (llist_INDUCT, llist_RECURSION) ← define_type
    "llist = llist_of_list (A list) | llist_of_seq (num->A)"

  let LLIST_OF_LIST_11 ← prove
    r"!l1 l2:A list. llist_of_list l1 = llist_of_list l2 <=> l1 = l2"
    (REWRITE_TAC [(← injectivity "llist")])

  let LLIST_OF_SEQ_11 ← prove
    r"!f g:num->A. llist_of_seq f = llist_of_seq g <=> f = g"
    (REWRITE_TAC [(← injectivity "llist")])

  let LLIST_OF_LIST_NEQ_SEQ ← prove
    r"!(l:A list) f. ~(llist_of_list l = llist_of_seq f)"
    (REWRITE_TAC [(← distinctness "llist")])

  let LLIST_LIST_OR_SEQ ← prove
    r"!l:A llist. (?xs. l = llist_of_list xs) \/ (?f. l = llist_of_seq f)"
    (ACCEPT_TAC (← cases "llist"))

  let LLIST_REP_EQ ← CONJ (← injectivity "llist") (← CONJ (← distinctness "llist") (← GSYM (← distinctness "llist")))

  let LLIST_REP_CASES_TAC : term → tactic ← pure (fun tm => tactic_of do
    pure (DISJ_CASES_THEN2 (CHOOSE_THEN SUBST_ALL_TAC) (CHOOSE_THEN SUBST_ALL_TAC)
      (← ISPEC tm LLIST_LIST_OR_SEQ)))

  let LNIL_DEF ← new_definition
    r"LNIL = llist_of_list ([]:A list)"

  let LCONS_DEF ← define
    r"(LCONS (h:A) (llist_of_list l) = llist_of_list (CONS h l)) /\
  (LCONS h (llist_of_seq f) =
   llist_of_seq (\n. if n = 0 then h else f(n - 1)))"

  let LLIST_OF_LIST ← prove
    r"llist_of_list [] = (LNIL:A llist) /\
   !h:A t. llist_of_list (CONS h t) = LCONS h (llist_of_list t)"
    (REWRITE_TAC [LNIL_DEF, LCONS_DEF])

  let LNTH_DEF ← define
    r"(LNTH n (llist_of_list l) =
   if n < LENGTH l then SOME (EL n l:A) else NONE) /\
  (LNTH n (llist_of_seq f) = SOME (f n))"

  let LNTH ← prove
    r"(!n. LNTH n (LNIL:A llist) = NONE) /\
   (!h:A t. LNTH 0 (LCONS h t) = SOME h) /\
   (!n h:A t. LNTH (SUC n) (LCONS h t) = LNTH n t)"
    (REWRITE_TAC [LNIL_DEF, LNTH_DEF, LENGTH, (← CONJUNCT1 LT)] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC (← q r"t:A llist") THEN REWRITE_TAC [LCONS_DEF, LNTH_DEF, LENGTH, LT_0, LT_SUC, EL, HD, TL, NOT_SUC, SUC_SUB1])

  let LLIST_EQ ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let lemma := (← prove r"!l1 l2:A list.
        (!n. LNTH n (llist_of_list l1) = LNTH n (llist_of_list l2)) <=>
        l1 = l2" (REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC [] THEN REWRITE_TAC [LNTH_DEF] THEN DISCH_TAC THEN REWRITE_TAC [LIST_EQ] THEN SUBGOAL_THEN (← q r"LENGTH(l1:A list) = LENGTH(l2:A list)") ASSUME_TAC THENL [FIRST_X_ASSUM (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"LENGTH(l1:A list)") th) THEN MP_TAC (← SPEC (← q r"LENGTH(l2:A list)") th))) THEN REWRITE_TAC [LT_REFL] THEN REPEAT (COND_CASES_TAC THEN REWRITE_TAC [option_DISTINCT, (← GSYM option_DISTINCT)]) THEN ASM_ARITH_TAC, ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"n:num") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"n:num"))) THEN ASM_REWRITE_TAC [option_INJ]]))
    let lemma' := (← prove r"!(xs:A list) f.
        ~(!n. LNTH n (llist_of_list xs) = LNTH n (llist_of_seq f)) /\
        ~(!n. LNTH n (llist_of_seq f) = LNTH n (llist_of_list xs))" (REPEAT GEN_TAC THEN REWRITE_TAC [NOT_FORALL_THM] THEN CONJ_TAC THEN EXISTS_TAC (← q r"LENGTH(xs:A list)") THEN REWRITE_TAC [LNTH_DEF, LT_REFL, option_DISTINCT, (← GSYM option_DISTINCT)]))
    prove
      r"!l1 l2:A llist. l1 = l2 <=> !n. LNTH n l1 = LNTH n l2"
      (REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC (← q r"l1:A llist") THEN LLIST_REP_CASES_TAC (← q r"l2:A llist") THEN REWRITE_TAC [lemma, LLIST_REP_EQ, lemma'] THEN REWRITE_TAC [LNTH_DEF, option_INJ, FUN_EQ_THM])

  let LLIST_OF_SEQ ← prove
    r"!f:num->A. llist_of_seq f = LCONS (f 0) (llist_of_seq (\n. f (SUC n)))"
    (REWRITE_TAC [LCONS_DEF, LLIST_OF_SEQ_11, FUN_EQ_THM] THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC [NOT_SUC, SUC_SUB1])

  let LLIST_CASES ← prove
    r"!l:A llist. l = LNIL \/ ?h t. l = LCONS h t"
    (GEN_TAC THEN LLIST_REP_CASES_TAC (← q r"l:A llist") THENL [STRUCT_CASES_TAC (← ISPEC (← q r"xs:A list") list_CASES) THEN REWRITE_TAC [LNIL_DEF] THEN MESON_TAC [LCONS_DEF], MESON_TAC [LLIST_OF_SEQ]])

  let NOT_LCONS_LNIL ← prove
    r"!h:A t. ~(LCONS h t = LNIL)"
    (REWRITE_TAC [LLIST_EQ] THEN REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o (SPEC (← q r"0"))) THEN REWRITE_TAC [LNTH, option_DISTINCT])

  let LCONS_11 ← prove
    r"!(h1:A) h2 t1 t2. LCONS h1 t1 = LCONS h2 t2 <=> h1 = h2 /\ t1 = t2"
    (REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC [] THEN REWRITE_TAC [LLIST_EQ] THEN DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"0") th) THEN MP_TAC (← GEN (← q r"n:num") (← SPEC (← q r"SUC n") th)))) THEN REWRITE_TAC [LNTH, option_INJ] THEN SIMP_TAC [])

  let LHD_DEF ← new_definition
    r"LHD (l:A llist) = THE(LNTH 0 l)"

  let LHD ← prove
    r"!h:A t. LHD(LCONS h t) = h"
    (REWRITE_TAC [LHD_DEF, LNTH, THE])

  let LTL_DEF ← define
    r"(LTL (llist_of_list l) =
   llist_of_list (if l = [] then [] else TL l:A list)) /\
  (LTL (llist_of_seq f) = llist_of_seq (\n. f (SUC n)))"

  let LTL ← prove
    r"LTL(LNIL:A llist) = LNIL /\ !h:A t. LTL(LCONS h t) = t"
    (REWRITE_TAC [LNIL_DEF, LTL_DEF] THEN REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC (← q r"t:A llist") THEN REWRITE_TAC [LCONS_DEF, LTL_DEF, NOT_CONS_NIL, TL, NOT_SUC, SUC_SUB1, ETA_AX])

  let LCONS_LHD_LTL ← prove
    r"!l:A llist. ~(l = LNIL) ==> LCONS (LHD l) (LTL l) = l"
    (GEN_TAC THEN STRUCT_CASES_TAC (← ISPEC (← q r"l:A llist") LLIST_CASES) THEN REWRITE_TAC [LHD, LTL])

  let LNTH_NONE_MONO ← prove
    r"!(l:A llist) m n. LNTH m l = NONE /\ m <= n ==> LNTH n l = NONE"
    (REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC (← q r"l:A llist") THEN REWRITE_TAC [LNTH_DEF, option_DISTINCT] THEN REPEAT COND_CASES_TAC THEN REWRITE_TAC [option_DISTINCT] THEN ASM_ARITH_TAC)

  let LAPPEND_DEF ← define
    r"(LAPPEND (llist_of_list l1) (llist_of_list l2) =
   llist_of_list (APPEND l1 l2)) /\
  (LAPPEND (llist_of_list l1) (llist_of_seq f) =
   llist_of_seq (\n. if n < LENGTH l1 then EL n l1
                     else f (n - LENGTH l1):A)) /\
  (LAPPEND (llist_of_seq f) l = llist_of_seq f)"

  let LAPPEND ← prove
    r"(!l:A llist. LAPPEND LNIL l = l) /\
   (!h:A t l. LAPPEND (LCONS h t) l = LCONS h (LAPPEND t l))"
    (CONJ_TAC THEN REPEAT GEN_TAC THENL [LLIST_REP_CASES_TAC (← q r"l:A llist") THEN REWRITE_TAC [LNIL_DEF, LAPPEND_DEF, APPEND, LENGTH, (← CONJUNCT1 LT), SUB_0, ETA_AX], LLIST_REP_CASES_TAC (← q r"t:A llist") THEN REWRITE_TAC [LCONS_DEF, LAPPEND_DEF] THEN LLIST_REP_CASES_TAC (← q r"l:A llist") THEN REWRITE_TAC [LAPPEND_DEF, LCONS_DEF, APPEND, LLIST_REP_EQ, FUN_EQ_THM] THEN INDUCT_TAC THEN REWRITE_TAC [LENGTH, LT_0, LT_SUC, EL, HD, TL, SUB_SUC, NOT_SUC, SUC_SUB1]])

  let LCOREC_DEF ← new_definition
    r"LCOREC p e h t (x:B) =
  if ?n. p (ITER n t x)
  then LAPPEND
        (llist_of_list
          (list_of_seq (\i. h (ITER i t x)) ((minimal) (\n. p (ITER n t x)))))
        (e (ITER ((minimal) (\n. p (ITER n t x))) t x))
  else llist_of_seq (\i. h (ITER i t x)):A llist"

  let LCOREC ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let MINIMAL_SUC := (← prove r"!P. ~P 0 /\ (?n. P n) ==> (minimal) P = SUC((minimal) (\n. P(SUC n)))" (GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"?n. P(SUC n)") ASSUME_TAC THENL [ASM_MESON_TAC [num_CASES], ALL_TAC] THEN MP_TAC (← SPEC (← q r"P:num->bool") MINIMAL) THEN MP_TAC (← SPEC (← q r"\n. (P:num->bool)(SUC n)") MINIMAL) THEN ASM_REWRITE_TAC [] THEN SPEC_TAC ((← q r"(minimal) P"), (← q r"m:num")) THEN SPEC_TAC ((← q r"(minimal) (\n. (P:num->bool)(SUC n))"), (← q r"k:num")) THEN REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN MP_TAC (← SPEC (← q r"m:num") num_CASES) THEN STRIP_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC [SUC_INJ] THEN REWRITE_TAC [(← GSYM LE_ANTISYM), (← GSYM NOT_LT)] THEN ASM_MESON_TAC [LT_SUC]))
    prove
      r"!p e h t (x:B).
          LCOREC p e h t x:A llist =
          if p x then e x else LCONS (h x) (LCOREC p e h t (t x))"
      (REPEAT GEN_TAC THEN REWRITE_TAC [LCOREC_DEF] THEN ASM_CASES_TAC (← q r"(p:B->bool) x") THEN ASM_REWRITE_TAC [] THENL [SUBGOAL_THEN (← q r"?n. (p:B->bool) (ITER n t x)") (fun th => REWRITE_TAC [th]) THENL [EXISTS_TAC (← q r"0") THEN ASM_REWRITE_TAC [ITER], ALL_TAC] THEN SUBGOAL_THEN (← q r"(minimal) (\n. (p:B->bool) (ITER n t x)) = 0") SUBST1_TAC THENL [MATCH_MP_TAC (← MESON [MINIMAL, LT_NZ] (← q r"!P. P 0 ==> (minimal) P = 0")) THEN ASM_REWRITE_TAC [ITER], ALL_TAC] THEN REWRITE_TAC [list_of_seq, ITER, LLIST_OF_LIST, LAPPEND], ALL_TAC] THEN SUBGOAL_THEN (← q r"(?n. (p:B->bool) (ITER n t x)) <=> (?n. p (ITER n t (t x)))") SUBST1_TAC THENL [EQ_TAC THENL [DISCH_THEN (X_CHOOSE_THEN (← q r"n:num") MP_TAC) THEN STRUCT_CASES_TAC (← SPEC (← q r"n:num") num_CASES) THEN ASM_REWRITE_TAC [ITER_ALT] THEN MESON_TAC [], MESON_TAC [ITER_ALT]], ALL_TAC] THEN COND_CASES_TAC THENL [ALL_TAC, GEN_REWRITE_TAC LAND_CONV [LLIST_OF_SEQ] THEN REWRITE_TAC [ITER_ALT]] THEN MP_TAC (← ISPEC (← q r"\n. (p:B->bool) (ITER n t x)") MINIMAL_SUC) THEN REWRITE_TAC [ITER_ALT] THEN ANTS_TAC THENL [ASM_MESON_TAC [ITER_ALT], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [LIST_OF_SEQ, o_DEF, ITER_ALT, LLIST_OF_LIST, LAPPEND])

  let LCOREC_UNIQUE ← prove
    r"!p e h t (g:B->A llist).
        (!x. g x = if p x then e x else LCONS (h x) (g (t x)))
        ==> g = LCOREC p e h t"
    (REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [FUN_EQ_THM, LLIST_EQ] THEN ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN INDUCT_TAC THEN X_GEN_TAC (← q r"x:B") THEN FIRST_ASSUM (fun th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [LCOREC] THEN COND_CASES_TAC THEN REWRITE_TAC [LNTH] THEN FIRST_ASSUM MATCH_ACCEPT_TAC)

  let LUNFOLD_DEF ← new_definition
    r"LUNFOLD p h t = LCOREC p (\x:B. LNIL:A llist) h t"

  let LUNFOLD ← prove
    r"!p h t (x:B).
        LUNFOLD p h t x:A llist =
        if p x then LNIL else LCONS (h x) (LUNFOLD p h t (t x))"
    (REPEAT GEN_TAC THEN REWRITE_TAC [LUNFOLD_DEF] THEN GEN_REWRITE_TAC LAND_CONV [LCOREC] THEN REWRITE_TAC [])

  let LUNFOLD_UNIQUE ← prove
    r"!p h t (g:B->A llist).
        (!x. g x = if p x then LNIL else LCONS (h x) (g (t x)))
        ==> g = LUNFOLD p h t"
    (REWRITE_TAC [LUNFOLD_DEF] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC LCOREC_UNIQUE THEN REWRITE_TAC [] THEN FIRST_ASSUM ACCEPT_TAC)

  let LLIST_COINDUCT ← prove
    r"!R:A llist->A llist->bool.
        (!l1 l2. R l1 l2
                 ==> l1 = LNIL /\ l2 = LNIL \/
                     ?h t1 t2. l1 = LCONS h t1 /\ l2 = LCONS h t2 /\ R t1 t2)
        ==> !l1 l2. R l1 l2 ==> l1 = l2"
    (GEN_TAC THEN DISCH_THEN (fun bisim => tactic_of do pure (SUBGOAL_THEN (← q r"!n l1 l2:A llist. R l1 l2 ==> LNTH n l1 = LNTH n l2") (fun th => MESON_TAC [th, LLIST_EQ]) THEN INDUCT_TAC THEN REPEAT GEN_TAC THEN DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP bisim)) THEN ASM_REWRITE_TAC [LNTH] THEN ASM_MESON_TAC [])))

  let LLIST_STRONG_COINDUCT ← prove
    r"!R:A llist->A llist->bool.
        (!l1 l2. R l1 l2
                 ==> l1 = LNIL /\ l2 = LNIL \/
                     ?h t1 t2. l1 = LCONS h t1 /\ l2 = LCONS h t2 /\
                               (R t1 t2 \/ t1 = t2))
        ==> !l1 l2. R l1 l2 ==> l1 = l2"
    (GEN_TAC THEN DISCH_TAC THEN MP_TAC (← ISPEC (← q r"\l1 l2:A llist. R l1 l2 \/ l1 = l2") LLIST_COINDUCT) THEN REWRITE_TAC [] THEN ANTS_TAC THENL [ALL_TAC, MESON_TAC []] THEN REPEAT GEN_TAC THEN STRIP_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC, ASM_REWRITE_TAC [] THEN MESON_TAC [LLIST_CASES]])

  let LLIST_CASES_TAC : term → tactic ← pure (fun tm => tactic_of do
    pure (DISJ_CASES_THEN2 SUBST_ALL_TAC (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
      (← ISPEC tm LLIST_CASES)))

  -- the tactic itself is LLIST_COINDUCT_UNFOLD_TAC_with, before the bundles
  let LLIST_COINDUCT_UNFOLD_TAC : List thm → tactic ←
    pure (LLIST_COINDUCT_UNFOLD_TAC_with LLIST_STRONG_COINDUCT)

  let LLIST_COINDUCT_TAC : tactic ← pure (LLIST_COINDUCT_UNFOLD_TAC [])

  let LLIST_BISIM_REFL ← prove
    r"!(R:A llist->A llist->bool) l.
        l = LNIL \/
        ?h t1 t2. l = LCONS h t1 /\ l = LCONS h t2 /\ (R t1 t2 \/ t1 = t2)"
    (REPEAT GEN_TAC THEN LLIST_CASES_TAC (← q r"l:A llist") THEN REWRITE_TAC [NOT_LCONS_LNIL, LCONS_11] THEN MESON_TAC [])

  let LLIST_BISIM_LCONS ← prove
    r"!(a:A) x b y P.
        (?h t1 t2. LCONS a x = LCONS h t1 /\ LCONS b y = LCONS h t2 /\
                   P t1 t2) <=> a = b /\ P x y"
    (REWRITE_TAC [LCONS_11] THEN MESON_TAC [])

  let LLIST_BISIM_TAC : tactic ← pure (
    REWRITE_TAC [LLIST_BISIM_LCONS, LLIST_BISIM_REFL, NOT_LCONS_LNIL,
                 ← GSYM NOT_LCONS_LNIL])

  let LNTH_LLIST_OF_LIST ← prove
    r"!(l:A list) n.
        LNTH n (llist_of_list l) =
        if n < LENGTH l then SOME (EL n l) else NONE"
    (REWRITE_TAC [LNTH_DEF])

  let LNTH_LLIST_OF_SEQ ← prove
    r"!(f:num->A) n. LNTH n (llist_of_seq f) = SOME (f n)"
    (REWRITE_TAC [LNTH_DEF])

  let list_of_llist ← new_recursive_definition llist_RECURSION
    r"!l. list_of_llist (llist_of_list l) = l:A list"

  let LFINITE_DEF ← define
    r"(LFINITE (llist_of_list (l:A list)) <=> T) /\
  (LFINITE (llist_of_seq (f:num->A)) <=> F)"

  let LFINITE_LCONS ← prove
    r"!h:A t. LFINITE (LCONS h t) <=> LFINITE t"
    (REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC (← q r"t:A llist") THEN REWRITE_TAC [LCONS_DEF, LFINITE_DEF])

  let LFINITE_RULES ← prove
    r"LFINITE (LNIL:A llist) /\ (!h:A t. LFINITE t ==> LFINITE (LCONS h t))"
    (REWRITE_TAC [LNIL_DEF, LFINITE_DEF, LFINITE_LCONS])

  let LFINITE_INDUCT ← prove
    r"!LFINITE':A llist->bool.
        LFINITE' LNIL /\ (!h t. LFINITE' t ==> LFINITE' (LCONS h t))
        ==> (!a. LFINITE a ==> LFINITE' a)"
    (GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN LLIST_REP_CASES_TAC (← q r"a:A llist") THEN REWRITE_TAC [LFINITE_DEF] THEN SPEC_TAC ((← q r"xs:A list"), (← q r"xs:A list")) THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [(← GSYM LNIL_DEF)] THEN REWRITE_TAC [(← GSYM (← CONJUNCT1 LCONS_DEF))] THEN ASM_MESON_TAC [])

  let LFINITE_CASES ← prove
    r"!a:A llist. LFINITE a <=> a = LNIL \/ (?h t. a = LCONS h t /\ LFINITE t)"
    (GEN_TAC THEN STRUCT_CASES_TAC (← ISPEC (← q r"a:A llist") LLIST_CASES) THEN REWRITE_TAC [LFINITE_RULES, LFINITE_LCONS, NOT_LCONS_LNIL, LCONS_11] THEN MESON_TAC [])

  let LFINITE_LTL ← prove
    r"!l:A llist. LFINITE (LTL l) <=> LFINITE l"
    (GEN_TAC THEN STRUCT_CASES_TAC (← ISPEC (← q r"l:A llist") LLIST_CASES) THEN REWRITE_TAC [LTL, LFINITE_LCONS])

  let LFINITE_LLIST_OF_LIST ← prove
    r"!l:A llist. LFINITE l <=> ?xs. l = llist_of_list xs"
    (GEN_TAC THEN LLIST_REP_CASES_TAC (← q r"l:A llist") THEN REWRITE_TAC [LFINITE_DEF, LLIST_REP_EQ] THEN MESON_TAC [])

  let NOT_LFINITE_LLIST_OF_SEQ ← prove
    r"!l:A llist. ~LFINITE l <=> ?f. l = llist_of_seq f"
    (GEN_TAC THEN LLIST_REP_CASES_TAC (← q r"l:A llist") THEN REWRITE_TAC [LFINITE_DEF, LLIST_REP_EQ] THEN MESON_TAC [])

  let LFINITE_LNTH ← prove
    r"!l:A llist. LFINITE l <=> ?n. LNTH n l = NONE"
    (GEN_TAC THEN LLIST_REP_CASES_TAC (← q r"l:A llist") THEN REWRITE_TAC [LFINITE_DEF, LNTH_DEF, option_DISTINCT] THEN EXISTS_TAC (← q r"LENGTH(xs:A list)") THEN REWRITE_TAC [LT_REFL])

  let LLIST_OF_LIST_OF_LLIST ← prove
    r"!l:A llist. LFINITE l ==> llist_of_list (list_of_llist l) = l"
    (GEN_TAC THEN LLIST_REP_CASES_TAC (← q r"l:A llist") THEN REWRITE_TAC [LFINITE_DEF, list_of_llist])

  let NOT_LFINITE_COINDUCT ← prove
    r"!P:A llist->bool.
        (!l. P l ==> ?h t. l = LCONS h t /\ P t)
        ==> !l. P l ==> ~LFINITE l"
    (GEN_TAC THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"!l:A llist. LFINITE l ==> ~P l") (fun th => MESON_TAC [th]) THEN MATCH_MP_TAC LFINITE_INDUCT THEN ASM_MESON_TAC [NOT_LCONS_LNIL, LCONS_11])

  let LLENGTH_DEF ← define
    r"(LLENGTH (llist_of_list (l:A list)) = SOME (LENGTH l)) /\
  (LLENGTH (llist_of_seq (f:num->A)) = NONE)"

  let LLENGTH ← prove
    r"LLENGTH (LNIL:A llist) = SOME 0 /\
   !h:A t. LLENGTH (LCONS h t) = OPTION_MAP SUC (LLENGTH t)"
    (REWRITE_TAC [LNIL_DEF, LLENGTH_DEF, LENGTH] THEN REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC (← q r"t:A llist") THEN REWRITE_TAC [LCONS_DEF, LLENGTH_DEF, LENGTH, OPTION_MAP])

  let LLENGTH_EQ_NONE ← prove
    r"!l:A llist. LLENGTH l = NONE <=> ~LFINITE l"
    (GEN_TAC THEN LLIST_REP_CASES_TAC (← q r"l:A llist") THEN REWRITE_TAC [LLENGTH_DEF, LFINITE_DEF, option_DISTINCT])

  let LLENGTH_LLIST_OF_LIST ← prove
    r"!l:A list. LLENGTH (llist_of_list l) = SOME (LENGTH l)"
    (REWRITE_TAC [LLENGTH_DEF])

  let LMAP_DEF ← define
    r"(LMAP (f:A->B) (llist_of_list l) = llist_of_list (MAP f l)) /\
  (LMAP f (llist_of_seq s) = llist_of_seq (f o s))"

  let LMAP ← prove
    r"(!f:A->B. LMAP f LNIL = LNIL) /\
   (!(f:A->B) h t. LMAP f (LCONS h t) = LCONS (f h) (LMAP f t))"
    (REWRITE_TAC [LNIL_DEF, LMAP_DEF, MAP] THEN REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC (← q r"t:A llist") THEN REWRITE_TAC [LCONS_DEF, LMAP_DEF, MAP, LLIST_OF_SEQ_11, FUN_EQ_THM, o_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [])

  let LMAP_LLIST_OF_LIST ← prove
    r"!(f:A->B) l. LMAP f (llist_of_list l) = llist_of_list (MAP f l)"
    (REWRITE_TAC [LMAP_DEF])

  let LMAP_LLIST_OF_SEQ ← prove
    r"!(f:A->B) s. LMAP f (llist_of_seq s) = llist_of_seq (f o s)"
    (REWRITE_TAC [LMAP_DEF])

  let LMAP_ID ← prove
    r"!l:A llist. LMAP (\x. x) l = l"
    (GEN_TAC THEN LLIST_REP_CASES_TAC (← q r"l:A llist") THEN REWRITE_TAC [LMAP_DEF, MAP_ID, o_DEF, ETA_AX])

  let LMAP_o ← prove
    r"!(f:B->C) (g:A->B) l. LMAP f (LMAP g l) = LMAP (f o g) l"
    (REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC (← q r"l:A llist") THEN REWRITE_TAC [LMAP_DEF, MAP_o, o_ASSOC])

  let LMAP_EQ_LNIL ← prove
    r"!(f:A->B) l. LMAP f l = LNIL <=> l = LNIL"
    (GEN_TAC THEN GEN_TAC THEN LLIST_CASES_TAC (← q r"l:A llist") THEN REWRITE_TAC [LMAP, NOT_LCONS_LNIL])

  let LNTH_LMAP ← prove
    r"!(f:A->B) n l. LNTH n (LMAP f l) = OPTION_MAP f (LNTH n l)"
    (REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC (← q r"l:A llist") THEN REWRITE_TAC [LMAP_DEF, LNTH_DEF, LENGTH_MAP, o_THM, OPTION_MAP] THEN COND_CASES_TAC THEN ASM_SIMP_TAC [EL_MAP, OPTION_MAP])

  let LFINITE_LMAP ← prove
    r"!(f:A->B) l. LFINITE (LMAP f l) <=> LFINITE l"
    (REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC (← q r"l:A llist") THEN REWRITE_TAC [LMAP_DEF, LFINITE_DEF])

  let LLENGTH_LMAP ← prove
    r"!(f:A->B) l. LLENGTH (LMAP f l) = LLENGTH l"
    (REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC (← q r"l:A llist") THEN REWRITE_TAC [LMAP_DEF, LLENGTH_DEF, LENGTH_MAP])

  let LAPPEND_LLIST_OF_LIST ← prove
    r"!l1 l2:A list.
        LAPPEND (llist_of_list l1) (llist_of_list l2) =
        llist_of_list (APPEND l1 l2)"
    (REWRITE_TAC [LAPPEND_DEF])

  let LAPPEND_LNIL ← prove
    r"!l:A llist. LAPPEND l LNIL = l"
    (GEN_TAC THEN LLIST_REP_CASES_TAC (← q r"l:A llist") THEN REWRITE_TAC [LNIL_DEF, LAPPEND_DEF, APPEND_NIL])

  let LAPPEND_ASSOC ← prove
    r"!l1 l2 l3:A llist.
        LAPPEND l1 (LAPPEND l2 l3) = LAPPEND (LAPPEND l1 l2) l3"
    (LLIST_COINDUCT_TAC THEN LLIST_CASES_TAC (← q r"l1:A llist") THEN REWRITE_TAC [LAPPEND] THEN LLIST_BISIM_TAC THEN MESON_TAC [])

  let LAPPEND_INFINITE ← prove
    r"!l1 l2:A llist. ~LFINITE l1 ==> LAPPEND l1 l2 = l1"
    (REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC (← q r"l1:A llist") THEN REWRITE_TAC [LFINITE_DEF, LAPPEND_DEF])

  let LFINITE_LAPPEND ← prove
    r"!l1 l2:A llist. LFINITE (LAPPEND l1 l2) <=> LFINITE l1 /\ LFINITE l2"
    (REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC (← q r"l1:A llist") THEN LLIST_REP_CASES_TAC (← q r"l2:A llist") THEN REWRITE_TAC [LFINITE_DEF, LAPPEND_DEF])

  let LMAP_LAPPEND ← prove
    r"!(f:A->B) l1 l2.
        LMAP f (LAPPEND l1 l2) = LAPPEND (LMAP f l1) (LMAP f l2)"
    (LLIST_COINDUCT_TAC THEN LLIST_CASES_TAC (← q r"l1:A llist") THEN REWRITE_TAC [LAPPEND, LMAP] THEN LLIST_BISIM_TAC THEN MESON_TAC [])

  let LNTH_LAPPEND ← prove
    r"!(l1:A list) l2 n.
        LNTH n (LAPPEND (llist_of_list l1) l2) =
        if n < LENGTH l1 then SOME (EL n l1) else LNTH (n - LENGTH l1) l2"
    (REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC (← q r"l2:A llist") THEN REWRITE_TAC [LAPPEND_DEF, LNTH_DEF, LENGTH_APPEND, EL_APPEND] THEN REPEAT COND_CASES_TAC THEN REWRITE_TAC [] THEN ASM_ARITH_TAC)

  let LAPPEND_EQ_LNIL ← prove
    r"!l1 l2:A llist. LAPPEND l1 l2 = LNIL <=> l1 = LNIL /\ l2 = LNIL"
    (REPEAT GEN_TAC THEN LLIST_CASES_TAC (← q r"l1:A llist") THEN REWRITE_TAC [LAPPEND, NOT_LCONS_LNIL])

  let LTAKE_DEF ← define
    r"(LTAKE 0 (l:A llist) = []) /\
  (LTAKE (SUC n) l =
   if l = LNIL then [] else CONS (LHD l) (LTAKE n (LTL l)))"

  let LTAKE ← prove
    r"(!l:A llist. LTAKE 0 l = []) /\
   (!n. LTAKE (SUC n) (LNIL:A llist) = []) /\
   (!n h:A t. LTAKE (SUC n) (LCONS h t) = CONS h (LTAKE n t))"
    (REWRITE_TAC [LTAKE_DEF, NOT_LCONS_LNIL, LHD, LTL])

  let LDROP_DEF ← define
    r"(LDROP 0 (l:A llist) = l) /\ (LDROP (SUC n) l = LDROP n (LTL l))"

  let LDROP_LNIL ← prove
    r"!n. LDROP n (LNIL:A llist) = LNIL"
    (INDUCT_TAC THEN ASM_REWRITE_TAC [LDROP_DEF, LTL])

  let LDROP ← prove
    r"(!l:A llist. LDROP 0 l = l) /\
   (!n. LDROP (SUC n) (LNIL:A llist) = LNIL) /\
   (!n h:A t. LDROP (SUC n) (LCONS h t) = LDROP n t)"
    (REWRITE_TAC [LDROP_DEF, LDROP_LNIL, LTL])

  let LTAKE_LDROP ← prove
    r"!n (l:A llist). LAPPEND (llist_of_list (LTAKE n l)) (LDROP n l) = l"
    (INDUCT_TAC THEN GEN_TAC THEN LLIST_CASES_TAC (← q r"l:A llist") THEN ASM_REWRITE_TAC [LTAKE, LDROP, LLIST_OF_LIST, LAPPEND])

  let LNTH_LDROP ← prove
    r"!m n (l:A llist). LNTH m (LDROP n l) = LNTH (m + n) l"
    (GEN_TAC THEN INDUCT_TAC THEN GEN_TAC THEN LLIST_CASES_TAC (← q r"l:A llist") THEN ASM_REWRITE_TAC [LDROP, LNTH, ADD_CLAUSES])

  let LDROP_ADD ← prove
    r"!m n (l:A llist). LDROP (m + n) l = LDROP m (LDROP n l)"
    (GEN_TAC THEN INDUCT_TAC THEN GEN_TAC THEN LLIST_CASES_TAC (← q r"l:A llist") THEN ASM_REWRITE_TAC [LDROP, LDROP_LNIL, ADD_CLAUSES])

  let LNTH_LTAKE ← prove
    r"!n (l:A llist). LNTH n (llist_of_list (LTAKE (SUC n) l)) = LNTH n l"
    (INDUCT_TAC THEN GEN_TAC THEN LLIST_CASES_TAC (← q r"l:A llist") THEN ASM_REWRITE_TAC [LTAKE, LLIST_OF_LIST, LNTH])

  let LLIST_EQ_LTAKE ← prove
    r"!l1 l2:A llist. l1 = l2 <=> !n. LTAKE n l1 = LTAKE n l2"
    (REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC [] THEN DISCH_TAC THEN ONCE_REWRITE_TAC [LLIST_EQ] THEN ONCE_REWRITE_TAC [(← GSYM LNTH_LTAKE)] THEN ASM_REWRITE_TAC [])

  let LTAKE_LLIST_OF_SEQ ← prove
    r"!n (f:num->A). LTAKE n (llist_of_seq f) = list_of_seq f n"
    (INDUCT_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC [LLIST_OF_SEQ] THEN ASM_REWRITE_TAC [LTAKE, LIST_OF_SEQ, o_DEF])

  let LDROP_LLIST_OF_SEQ ← prove
    r"!n (f:num->A). LDROP n (llist_of_seq f) = llist_of_seq (\i. f(i + n))"
    (REWRITE_TAC [LLIST_EQ, LNTH_LDROP, LNTH_LLIST_OF_SEQ])

  let set_of_llist ← new_definition
    r"set_of_llist (l:A llist) = {x | ?n. LNTH n l = SOME x}"

  let IN_SET_OF_LLIST ← prove
    r"!(x:A) l. x IN set_of_llist l <=> ?n. LNTH n l = SOME x"
    (REWRITE_TAC [set_of_llist, IN_ELIM_THM])

  let LNTH_LCONS_EXISTS ← prove
    r"!h:A t x. (?n. LNTH n (LCONS h t) = SOME x) <=>
             x = h \/ ?n. LNTH n t = SOME x"
    (REPEAT GEN_TAC THEN EQ_TAC THENL [DISCH_THEN (X_CHOOSE_THEN (← q r"n:num") MP_TAC) THEN STRUCT_CASES_TAC (← SPEC (← q r"n:num") num_CASES) THEN REWRITE_TAC [LNTH, option_INJ] THEN MESON_TAC [], STRIP_TAC THENL [EXISTS_TAC (← q r"0") THEN ASM_REWRITE_TAC [LNTH], EXISTS_TAC (← q r"SUC n") THEN ASM_REWRITE_TAC [LNTH]]])

  let SET_OF_LLIST ← prove
    r"set_of_llist (LNIL:A llist) = {} /\
   !h:A t. set_of_llist (LCONS h t) = h INSERT set_of_llist t"
    (REWRITE_TAC [EXTENSION, IN_SET_OF_LLIST, NOT_IN_EMPTY, IN_INSERT, LNTH, option_DISTINCT, (← GSYM option_DISTINCT), LNTH_LCONS_EXISTS])

  let SET_OF_LLIST_LLIST_OF_LIST ← prove
    r"!l:A list. set_of_llist (llist_of_list l) = set_of_list l"
    (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [LLIST_OF_LIST, SET_OF_LLIST, set_of_list])

  let SET_OF_LLIST_LLIST_OF_SEQ ← prove
    r"!f:num->A. set_of_llist (llist_of_seq f) = IMAGE f (:num)"
    (REWRITE_TAC [EXTENSION, IN_SET_OF_LLIST, LNTH_LLIST_OF_SEQ, option_INJ, IN_IMAGE, IN_UNIV] THEN MESON_TAC [])

  let SET_OF_LLIST_LMAP ← prove
    r"!(f:A->B) l. set_of_llist (LMAP f l) = IMAGE f (set_of_llist l)"
    (REWRITE_TAC [EXTENSION, IN_IMAGE, IN_SET_OF_LLIST, LNTH_LMAP, OPTION_MAP_EQ_SOME] THEN MESON_TAC [])

  let SET_OF_LLIST_LAPPEND ← prove
    r"!l1 l2:A llist.
        set_of_llist (LAPPEND l1 l2) =
        if LFINITE l1 then set_of_llist l1 UNION set_of_llist l2
        else set_of_llist l1"
    (REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [LAPPEND_INFINITE] THEN FIRST_X_ASSUM (MP_TAC o (GEN_REWRITE_RULE id [LFINITE_LLIST_OF_LIST])) THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN SPEC_TAC ((← q r"xs:A list"), (← q r"xs:A list")) THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [LLIST_OF_LIST, LAPPEND, SET_OF_LLIST, UNION_EMPTY, INSERT_UNION_EQ])

  let LALL_DEF ← new_definition
    r"LALL P (l:A llist) <=> !x. x IN set_of_llist l ==> P x"

  let LEXISTS_DEF ← new_definition
    r"LEXISTS P (l:A llist) <=> ?x. x IN set_of_llist l /\ P x"

  let LALL_SET_OF_LLIST ← prove
    r"!P (l:A llist). LALL P l <=> !x. x IN set_of_llist l ==> P x"
    (REWRITE_TAC [LALL_DEF])

  let LEXISTS_SET_OF_LLIST ← prove
    r"!P (l:A llist). LEXISTS P l <=> ?x. x IN set_of_llist l /\ P x"
    (REWRITE_TAC [LEXISTS_DEF])

  let LALL ← prove
    r"(!P:A->bool. LALL P LNIL) /\
   (!P h:A t. LALL P (LCONS h t) <=> P h /\ LALL P t)"
    (REWRITE_TAC [LALL_DEF, SET_OF_LLIST, FORALL_IN_INSERT, NOT_IN_EMPTY])

  let LEXISTS ← prove
    r"(!P:A->bool. ~LEXISTS P LNIL) /\
   (!P h:A t. LEXISTS P (LCONS h t) <=> P h \/ LEXISTS P t)"
    (REWRITE_TAC [LEXISTS_DEF, SET_OF_LLIST, EXISTS_IN_INSERT, NOT_IN_EMPTY])

  let LEXISTS_LALL ← prove
    r"!P (l:A llist). LEXISTS P l <=> ~LALL (\x. ~P x) l"
    (REWRITE_TAC [LEXISTS_DEF, LALL_DEF] THEN MESON_TAC [])

  let LALL_LMAP ← prove
    r"!P (f:A->B) l. LALL P (LMAP f l) <=> LALL (P o f) l"
    (REWRITE_TAC [LALL_DEF, SET_OF_LLIST_LMAP, FORALL_IN_IMAGE, o_THM])

  let LEXISTS_LMAP ← prove
    r"!P (f:A->B) l. LEXISTS P (LMAP f l) <=> LEXISTS (P o f) l"
    (REWRITE_TAC [LEXISTS_DEF, SET_OF_LLIST_LMAP, EXISTS_IN_IMAGE, o_THM])

  let LALL_COINDUCT ← prove
    r"!P (Q:A llist->bool).
        (!l. Q l ==> l = LNIL \/ ?h t. l = LCONS h t /\ P h /\ Q t)
        ==> !l. Q l ==> LALL P l"
    (REPEAT GEN_TAC THEN DISCH_THEN (fun coind => tactic_of do pure (REWRITE_TAC [LALL_DEF] THEN SUBGOAL_THEN (← q r"!n l (x:A). Q l /\ LNTH n l = SOME x ==> P x") (fun th => MESON_TAC [th, IN_SET_OF_LLIST]) THEN INDUCT_TAC THEN REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o (MATCH_MP coind)) MP_TAC) THEN ASM_REWRITE_TAC [LNTH, (← GSYM option_DISTINCT), option_INJ] THEN ASM_MESON_TAC [])))

  let LEXISTS_INDUCT ← prove
    r"!P LEXISTS'.
        (!h:A t. P h ==> LEXISTS' (LCONS h t)) /\
        (!h t. LEXISTS' t ==> LEXISTS' (LCONS h t))
        ==> (!a. LEXISTS P a ==> LEXISTS' a)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!n (l:A llist) x. LNTH n l = SOME x /\ P x ==> LEXISTS' l") (fun th => REWRITE_TAC [LEXISTS_DEF, IN_SET_OF_LLIST] THEN MESON_TAC [th]) THEN INDUCT_TAC THEN REPEAT GEN_TAC THEN LLIST_CASES_TAC (← q r"l:A llist") THEN REWRITE_TAC [LNTH, option_DISTINCT, option_INJ] THEN ASM_MESON_TAC [])

  let MONO_LALL ← prove
    r"(!x:A. P x ==> Q x) ==> LALL P l ==> LALL Q l"
    (REWRITE_TAC [LALL_DEF] THEN MESON_TAC [])

  let MONO_LEXISTS ← prove
    r"(!x:A. P x ==> Q x) ==> LEXISTS P l ==> LEXISTS Q l"
    (REWRITE_TAC [LEXISTS_DEF] THEN MESON_TAC [])

  -- monotonicity_theorems := [MONO_LALL; MONO_LEXISTS] @ !monotonicity_theorems
  set_monotonicity_theorems ([MONO_LALL, MONO_LEXISTS] ++ (← get_monotonicity_theorems))

  let (LFIRST_RULES, LFIRST_INDUCT, LFIRST_CASES) ← new_inductive_definition
    r"(!h:A t. P h ==> LFIRST P (LCONS h t) (LCONS h t)) /\
  (!h t l. ~P h /\ LFIRST P t l ==> LFIRST P (LCONS h t) l)"

  let LFIRST_UNIQUE ← prove
    r"!P (l:A llist) l1 l2. LFIRST P l l1 /\ LFIRST P l l2 ==> l1 = l2"
    (GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN MATCH_MP_TAC LFIRST_INDUCT THEN REPEAT STRIP_TAC THEN POP_ASSUM (MP_TAC o (ONCE_REWRITE_RULE [LFIRST_CASES])) THEN REWRITE_TAC [LCONS_11] THEN ASM_MESON_TAC [])

  let LFIRST_EXISTS ← prove
    r"!P (l:A llist). LEXISTS P l ==> ?l'. LFIRST P l l'"
    (GEN_TAC THEN MATCH_MP_TAC LEXISTS_INDUCT THEN MESON_TAC [LFIRST_RULES])

  let LFIRST_LCONS ← prove
    r"!P (l:A llist) l'. LFIRST P l l' ==> ?h t. l' = LCONS h t /\ P h"
    (GEN_TAC THEN MATCH_MP_TAC LFIRST_INDUCT THEN MESON_TAC [])

  let LFIRST_SUBSET ← prove
    r"!P (l:A llist) l'. LFIRST P l l' ==> set_of_llist l' SUBSET set_of_llist l"
    (GEN_TAC THEN MATCH_MP_TAC LFIRST_INDUCT THEN REWRITE_TAC [SET_OF_LLIST, SUBSET_REFL] THEN SET_TAC [])

  let LFIRST_LEXISTS ← prove
    r"!P (l:A llist) l'. LFIRST P l l' ==> LEXISTS P l"
    (GEN_TAC THEN MATCH_MP_TAC LFIRST_INDUCT THEN SIMP_TAC [LEXISTS])

  let lfirst ← new_definition
    r"lfirst P (l:A llist) = @l'. LFIRST P l l'"

  let LFIRST_LFIRST ← prove
    r"!P (l:A llist). LEXISTS P l ==> LFIRST P l (lfirst P l)"
    (REWRITE_TAC [lfirst] THEN MESON_TAC [LFIRST_EXISTS])

  let LFIRST_EQ ← prove
    r"!P (l:A llist) l'. LFIRST P l l' ==> lfirst P l = l'"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC LFIRST_UNIQUE THEN MAP_EVERY EXISTS_TAC [(← q r"P:A->bool"), (← q r"l:A llist")] THEN ASM_MESON_TAC [LFIRST_LFIRST, LFIRST_LEXISTS])

  let LFIRST_LCONS_P ← prove
    r"!P (h:A) t. P h ==> lfirst P (LCONS h t) = LCONS h t"
    (MESON_TAC [LFIRST_EQ, LFIRST_RULES])

  let LFIRST_LCONS_NOTP ← prove
    r"!P (h:A) t. ~P h /\ LEXISTS P t ==> lfirst P (LCONS h t) = lfirst P t"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC LFIRST_EQ THEN MATCH_MP_TAC (← CONJUNCT2 (← SPEC_ALL LFIRST_RULES)) THEN ASM_SIMP_TAC [LFIRST_LFIRST])

  let LFILTER_DEF ← new_definition
    r"LFILTER P = LUNFOLD (\l:A llist. ~LEXISTS P l) (\l. LHD (lfirst P l))
                      (\l. LTL (lfirst P l))"

  let LFILTER_UNFOLD ← prove
    r"!P (l:A llist).
        LFILTER P l =
        if ~LEXISTS P l then LNIL
        else LCONS (LHD (lfirst P l)) (LFILTER P (LTL (lfirst P l)))"
    (REWRITE_TAC [LFILTER_DEF] THEN REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [LUNFOLD] THEN REWRITE_TAC [])

  let LFILTER ← prove
    r"(!P:A->bool. LFILTER P LNIL = LNIL) /\
   (!P h:A t. LFILTER P (LCONS h t) =
              if P h then LCONS h (LFILTER P t) else LFILTER P t)"
    (CONJ_TAC THEN REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [LFILTER_UNFOLD] THEN REWRITE_TAC [LEXISTS] THEN ASM_CASES_TAC (← q r"(P:A->bool) h") THEN ASM_SIMP_TAC [LFIRST_LCONS_P, LHD, LTL] THEN ASM_CASES_TAC (← q r"LEXISTS (P:A->bool) t") THEN ASM_SIMP_TAC [LFIRST_LCONS_NOTP] THEN GEN_REWRITE_TAC RAND_CONV [LFILTER_UNFOLD] THEN ASM_REWRITE_TAC [])

  let LFILTER_EQ_LNIL ← prove
    r"!P (l:A llist). LFILTER P l = LNIL <=> LALL (\x. ~P x) l"
    (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [LFILTER_UNFOLD] THEN REWRITE_TAC [LEXISTS_LALL] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [NOT_LCONS_LNIL])

  let LFILTER_LAPPEND ← prove
    r"!P (l1:A llist) l2.
        LFINITE l1
        ==> LFILTER P (LAPPEND l1 l2) = LAPPEND (LFILTER P l1) (LFILTER P l2)"
    (GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN MATCH_MP_TAC LFINITE_INDUCT THEN REWRITE_TAC [LAPPEND, LFILTER] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [LAPPEND])

  -- @@RETURN BEGIN
  return { THE, OPTION_MAP, option_CASES, OPTION_MAP_EQ_NONE, OPTION_MAP_EQ_SOME,
           OPTION_MAP_ID, OPTION_MAP_o, llist_INDUCT, llist_RECURSION, LLIST_OF_LIST_11,
           LLIST_OF_SEQ_11, LLIST_OF_LIST_NEQ_SEQ, LLIST_LIST_OR_SEQ, LLIST_REP_EQ,
           LLIST_REP_CASES_TAC, LNIL_DEF, LCONS_DEF, LLIST_OF_LIST, LNTH_DEF, LNTH,
           LLIST_EQ, LLIST_OF_SEQ, LLIST_CASES, NOT_LCONS_LNIL, LCONS_11, LHD_DEF, LHD,
           LTL_DEF, LTL, LCONS_LHD_LTL, LNTH_NONE_MONO, LAPPEND_DEF, LAPPEND, LCOREC_DEF,
           LCOREC, LCOREC_UNIQUE, LUNFOLD_DEF, LUNFOLD, LUNFOLD_UNIQUE, LLIST_COINDUCT,
           LLIST_STRONG_COINDUCT, LLIST_CASES_TAC, LLIST_COINDUCT_UNFOLD_TAC,
           LLIST_COINDUCT_TAC, LLIST_BISIM_REFL, LLIST_BISIM_LCONS, LLIST_BISIM_TAC,
           LNTH_LLIST_OF_LIST, LNTH_LLIST_OF_SEQ, list_of_llist, LFINITE_DEF,
           LFINITE_LCONS, LFINITE_RULES, LFINITE_INDUCT, LFINITE_CASES, LFINITE_LTL,
           LFINITE_LLIST_OF_LIST, NOT_LFINITE_LLIST_OF_SEQ, LFINITE_LNTH,
           LLIST_OF_LIST_OF_LLIST, NOT_LFINITE_COINDUCT, LLENGTH_DEF, LLENGTH,
           LLENGTH_EQ_NONE, LLENGTH_LLIST_OF_LIST, LMAP_DEF, LMAP, LMAP_LLIST_OF_LIST,
           LMAP_LLIST_OF_SEQ, LMAP_ID, LMAP_o, LMAP_EQ_LNIL, LNTH_LMAP, LFINITE_LMAP,
           LLENGTH_LMAP, LAPPEND_LLIST_OF_LIST, LAPPEND_LNIL, LAPPEND_ASSOC,
           LAPPEND_INFINITE, LFINITE_LAPPEND, LMAP_LAPPEND, LNTH_LAPPEND,
           LAPPEND_EQ_LNIL, LTAKE_DEF, LTAKE, LDROP_DEF, LDROP_LNIL, LDROP, LTAKE_LDROP,
           LNTH_LDROP, LDROP_ADD, LNTH_LTAKE, LLIST_EQ_LTAKE, LTAKE_LLIST_OF_SEQ,
           LDROP_LLIST_OF_SEQ, set_of_llist, IN_SET_OF_LLIST, LNTH_LCONS_EXISTS,
           SET_OF_LLIST, SET_OF_LLIST_LLIST_OF_LIST, SET_OF_LLIST_LLIST_OF_SEQ,
           SET_OF_LLIST_LMAP, SET_OF_LLIST_LAPPEND, LALL_DEF, LEXISTS_DEF,
           LALL_SET_OF_LLIST, LEXISTS_SET_OF_LLIST, LALL, LEXISTS, LEXISTS_LALL,
           LALL_LMAP, LEXISTS_LMAP, LALL_COINDUCT, LEXISTS_INDUCT, MONO_LALL,
           MONO_LEXISTS, LFIRST_RULES, LFIRST_INDUCT, LFIRST_CASES, LFIRST_UNIQUE,
           LFIRST_EXISTS, LFIRST_LCONS, LFIRST_SUBSET, LFIRST_LEXISTS, lfirst,
           LFIRST_LFIRST, LFIRST_EQ, LFIRST_LCONS_P, LFIRST_LCONS_NOTP, LFILTER_DEF,
           LFILTER_UNFOLD, LFILTER, LFILTER_EQ_LNIL, LFILTER_LAPPEND }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- llist.ml phrases from line 925 to 1346                                 -/
/- ---------------------------------------------------------------------- -/

structure Llist02 where
  -- @@FIELDS
  LFILTER_LLIST_OF_LIST : thm
  SET_OF_LLIST_LFILTER : thm
  LALL_LFILTER : thm
  LFILTER_LFILTER : thm
  LFLATTEN_DEF : thm
  LFLATTEN_UNFOLD : thm
  LFLATTEN : thm
  LFLATTEN_EQ_LNIL : thm
  LFLATTEN_INFINITE : thm
  LFLATTEN_LCONS : thm
  LMAP_LFLATTEN : thm
  LZIP_DEF : thm
  LZIP : thm
  LNTH_LZIP : thm
  LZIP_LMAP : thm
  LALL2_DEF : thm
  LALL2 : thm
  LALL2_EQ : thm
  LALL2_LNTH : thm
  LLENGTH_EQ : thm
  LALL2_COINDUCT : thm
  MONO_LALL2 : thm
  LPREFIX_DEF : thm
  LPREFIX : thm
  LPREFIX_LAPPEND : thm
  LPREFIX_REFL : thm
  LPREFIX_TRANS : thm
  LPREFIX_LTAKE : thm
  LPREFIX_LNTH : thm
  LPREFIX_ANTISYM : thm
  LPREFIX_COINDUCT : thm
  LLIST_OF_LNTH : thm
  LPREFIX_CHAIN_LUB : thm
  LPREFIX_LTAKE_LUB : thm
  LITERATE_DEF : thm
  LITERATE : thm
  LFINITE_LITERATE : thm
  LMAP_LITERATE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupLlist02 [HolBase] (D : LlistDeps) (BLlist01 : Llist01) :
    ExceptT String IO Llist02 := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, ASM_MESON_TAC, GEN_BETA_CONV, INDUCT_TAC, LIST_INDUCT_TAC,
        MESON, MESON_TAC, SELECT_CONV, TAUT, define, get_monotonicity_theorems,
        new_definition, set_monotonicity_theorems, .. } := D
  let { ALL2, CONS_11, EL, EL_LIST_OF_SEQ, EQ_IMP, EXTENSION, FILTER, FST, FUN_EQ_THM,
        HD, IN_ELIM_THM, IN_INSERT, ITER, ITER_ALT, LEFT_IMP_EXISTS_THM, LENGTH,
        LENGTH_LIST_OF_SEQ, LE_ANTISYM, LE_REFL, LT, LT_0, LT_SUC, MINIMAL,
        NOT_CONS_NIL, NOT_LT, NOT_SUC, PAIR_EQ, SELECT_UNIQUE, SND, SUBSET, SUC_INJ,
        SUC_SUB1, SWAP_FORALL_THM, TL, num_CASES, o_DEF, o_THM, option_DISTINCT,
        option_INJ, .. } := D.core1
  let { IN_SET_OF_LLIST, LALL_DEF, LALL_LMAP, LAPPEND, LAPPEND_ASSOC, LAPPEND_DEF,
        LAPPEND_INFINITE, LAPPEND_LNIL, LCONS_DEF, LEXISTS, LEXISTS_DEF,
        LEXISTS_INDUCT, LEXISTS_LALL, LFILTER, LFILTER_EQ_LNIL, LFILTER_UNFOLD,
        LFINITE_DEF, LFINITE_INDUCT, LFINITE_LCONS, LFINITE_RULES, LFIRST_LCONS,
        LFIRST_LCONS_NOTP, LFIRST_LCONS_P, LFIRST_LFIRST, LFIRST_SUBSET, LHD,
        LLENGTH_DEF, LLIST_BISIM_TAC, LLIST_CASES_TAC, LLIST_COINDUCT_TAC, LLIST_EQ,
        LLIST_OF_LIST, LLIST_OF_SEQ, LLIST_REP_CASES_TAC, LLIST_REP_EQ, LMAP, LMAP_DEF,
        LMAP_EQ_LNIL, LNIL_DEF, LNTH, LNTH_DEF, LNTH_LAPPEND, LNTH_LCONS_EXISTS,
        LNTH_LDROP, LNTH_LTAKE, LNTH_NONE_MONO, LTAKE_LDROP, LTL, LUNFOLD,
        NOT_LCONS_LNIL, SET_OF_LLIST, THE, option_CASES, .. } := BLlist01
  -- @@SCOPE END

  let LFILTER_LLIST_OF_LIST ← prove
    r"!P (l:A list). LFILTER P (llist_of_list l) = llist_of_list (FILTER P l)"
    (GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [LLIST_OF_LIST, LFILTER, FILTER] THEN COND_CASES_TAC THEN REWRITE_TAC [LLIST_OF_LIST])

  let SET_OF_LLIST_LFILTER ← prove
    r"!P (l:A llist).
        set_of_llist (LFILTER P l) = {x | x IN set_of_llist l /\ P x}"
    (REPEAT GEN_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:A") THEN EQ_TAC THENL [REWRITE_TAC [IN_SET_OF_LLIST, LEFT_IMP_EXISTS_THM] THEN SPEC_TAC ((← q r"l:A llist"), (← q r"l:A llist")) THEN ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN INDUCT_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC [LFILTER_UNFOLD] THEN COND_CASES_TAC THEN REWRITE_TAC [LNTH, option_DISTINCT, option_INJ] THEN FIRST_ASSUM (MP_TAC o ((MATCH_MP LFIRST_LFIRST) o (REWRITE_RULE []))) THEN DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← MATCH_MP LFIRST_SUBSET th) THEN MP_TAC (← MATCH_MP LFIRST_LCONS th))) THEN STRIP_TAC THEN ASM_REWRITE_TAC [LHD, LTL, SUBSET, SET_OF_LLIST, IN_INSERT, (← GSYM IN_SET_OF_LLIST)] THEN REWRITE_TAC [IN_SET_OF_LLIST] THEN ASM_MESON_TAC [], REWRITE_TAC [IN_SET_OF_LLIST] THEN DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q r"n:num")) ASSUME_TAC) THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN SPEC_TAC ((← q r"l:A llist"), (← q r"l:A llist")) THEN SPEC_TAC ((← q r"n:num"), (← q r"n:num")) THEN INDUCT_TAC THEN GEN_TAC THEN LLIST_CASES_TAC (← q r"l:A llist") THEN REWRITE_TAC [LNTH, LFILTER, option_DISTINCT, option_INJ] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [LNTH_LCONS_EXISTS] THEN ASM_MESON_TAC []])

  let LALL_LFILTER ← prove
    r"!P (l:A llist). LALL P (LFILTER P l)"
    (REWRITE_TAC [LALL_DEF, SET_OF_LLIST_LFILTER, IN_ELIM_THM] THEN MESON_TAC [])

  let LFILTER_LFILTER ← prove
    r"!P Q (l:A llist). LFILTER P (LFILTER Q l) = LFILTER (\x. P x /\ Q x) l"
    (LLIST_COINDUCT_TAC THEN ASM_CASES_TAC (← q r"LEXISTS (\x:A. P x /\ Q x) l") THENL [ALL_TAC, DISJ1_TAC THEN REWRITE_TAC [LFILTER_EQ_LNIL, LALL_DEF] THEN REWRITE_TAC [SET_OF_LLIST_LFILTER, IN_ELIM_THM] THEN RULE_ASSUM_TAC (REWRITE_RULE [LEXISTS_DEF]) THEN ASM_MESON_TAC []] THEN POP_ASSUM MP_TAC THEN SPEC_TAC ((← q r"l:A llist"), (← q r"l:A llist")) THEN MATCH_MP_TAC LEXISTS_INDUCT THEN REWRITE_TAC [] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"(P:A->bool) h") THEN ASM_CASES_TAC (← q r"(Q:A->bool) h") THEN ASM_REWRITE_TAC [LFILTER] THEN LLIST_BISIM_TAC THEN MESON_TAC [])

  let LFLATTEN_DEF ← new_definition
    r"LFLATTEN =
  LUNFOLD (\ls:(A llist) llist. ~LEXISTS (\l. ~(l = LNIL)) ls)
          (\ls. LHD (LHD (lfirst (\l. ~(l = LNIL)) ls)))
          (\ls. LCONS (LTL (LHD (lfirst (\l. ~(l = LNIL)) ls)))
                      (LTL (lfirst (\l. ~(l = LNIL)) ls)))"

  let LFLATTEN_UNFOLD ← prove
    r"!ls:(A llist) llist.
        LFLATTEN ls =
        if ~LEXISTS (\l. ~(l = LNIL)) ls then LNIL
        else LCONS (LHD (LHD (lfirst (\l. ~(l = LNIL)) ls)))
                   (LFLATTEN (LCONS (LTL (LHD (lfirst (\l. ~(l = LNIL)) ls)))
                                    (LTL (lfirst (\l. ~(l = LNIL)) ls))))"
    (REWRITE_TAC [LFLATTEN_DEF] THEN GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [LUNFOLD] THEN REWRITE_TAC [])

  let LFLATTEN ← prove
    r"LFLATTEN (LNIL:(A llist) llist) = LNIL /\
   (!ls:(A llist) llist. LFLATTEN (LCONS LNIL ls) = LFLATTEN ls) /\
   (!(h:A) t ls. LFLATTEN (LCONS (LCONS h t) ls) =
                 LCONS h (LFLATTEN (LCONS t ls)))"
    (REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [LFLATTEN_UNFOLD] THEN REWRITE_TAC [LEXISTS, NOT_LCONS_LNIL] THEN SIMP_TAC [LFIRST_LCONS_P, NOT_LCONS_LNIL, LHD, LTL] THEN ASM_CASES_TAC (← q r"LEXISTS (\l:A llist. ~(l = LNIL)) ls") THEN ASM_SIMP_TAC [LFIRST_LCONS_NOTP] THEN GEN_REWRITE_TAC RAND_CONV [LFLATTEN_UNFOLD] THEN ASM_REWRITE_TAC [])

  let LFLATTEN_EQ_LNIL ← prove
    r"!ls:(A llist) llist. LFLATTEN ls = LNIL <=> LALL (\l. l = LNIL) ls"
    (GEN_TAC THEN ONCE_REWRITE_TAC [LFLATTEN_UNFOLD] THEN REWRITE_TAC [LEXISTS_LALL] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [NOT_LCONS_LNIL] THEN POP_ASSUM MP_TAC THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM])

  let LFLATTEN_INFINITE ← prove
    r"!(l:A llist) ls. ~LFINITE l ==> LFLATTEN (LCONS l ls) = l"
    (LLIST_COINDUCT_TAC THEN LLIST_CASES_TAC (← q r"l:A llist") THEN RULE_ASSUM_TAC (REWRITE_RULE [LFINITE_RULES, LFINITE_LCONS]) THEN ASM_REWRITE_TAC [LFLATTEN] THEN LLIST_BISIM_TAC THEN ASM_MESON_TAC [])

  let LFLATTEN_LCONS ← prove
    r"!(l:A llist) ls. LFLATTEN (LCONS l ls) = LAPPEND l (LFLATTEN ls)"
    (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"LFINITE (l:A llist)") THEN ASM_SIMP_TAC [LFLATTEN_INFINITE, LAPPEND_INFINITE] THEN POP_ASSUM MP_TAC THEN SPEC_TAC ((← q r"l:A llist"), (← q r"l:A llist")) THEN MATCH_MP_TAC LFINITE_INDUCT THEN ASM_SIMP_TAC [LFLATTEN, LAPPEND])

  let LMAP_LFLATTEN ← prove
    r"!(f:A->B) ls. LMAP f (LFLATTEN ls) = LFLATTEN (LMAP (LMAP f) ls)"
    (LLIST_COINDUCT_TAC THEN ASM_CASES_TAC (← q r"LEXISTS (\l:A llist. ~(l = LNIL)) ls") THENL [ALL_TAC, DISJ1_TAC THEN REWRITE_TAC [LMAP_EQ_LNIL, LFLATTEN_EQ_LNIL] THEN RULE_ASSUM_TAC (REWRITE_RULE [LEXISTS_LALL]) THEN ASM_REWRITE_TAC [LALL_LMAP, o_DEF, LMAP_EQ_LNIL]] THEN POP_ASSUM MP_TAC THEN SPEC_TAC ((← q r"ls:(A llist) llist"), (← q r"ls:(A llist) llist")) THEN MATCH_MP_TAC LEXISTS_INDUCT THEN REWRITE_TAC [] THEN CONJ_TAC THEN MAP_EVERY X_GEN_TAC [(← q r"l:A llist"), (← q r"ls:(A llist) llist")] THEN LLIST_CASES_TAC (← q r"l:A llist") THEN REWRITE_TAC [LMAP, LFLATTEN, NOT_LCONS_LNIL] THEN LLIST_BISIM_TAC THEN MESON_TAC [LMAP])

  let LZIP_DEF ← new_definition
    r"LZIP (l1:A llist) (l2:B llist) =
  LUNFOLD (\p:A llist#B llist. FST p = LNIL \/ SND p = LNIL)
          (\p. LHD (FST p),LHD (SND p)) (\p. LTL (FST p),LTL (SND p))
          (l1,l2)"

  let LZIP ← prove
    r"(!l:B llist. LZIP (LNIL:A llist) l = LNIL) /\
   (!(h:A) t. LZIP (LCONS h t) (LNIL:B llist) = LNIL) /\
   (!(h1:A) t1 (h2:B) t2.
        LZIP (LCONS h1 t1) (LCONS h2 t2) = LCONS (h1,h2) (LZIP t1 t2))"
    (REWRITE_TAC [LZIP_DEF] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [LUNFOLD] THEN REWRITE_TAC [FST, SND, NOT_LCONS_LNIL, LHD, LTL])

  let LNTH_LZIP ← prove
    r"!(l1:A llist) (l2:B llist) n x y.
        LNTH n (LZIP l1 l2) = SOME (x,y) <=>
        LNTH n l1 = SOME x /\ LNTH n l2 = SOME y"
    (SUBGOAL_THEN (← q r"!n (l1:A llist) (l2:B llist) x y.
        LNTH n (LZIP l1 l2) = SOME (x,y) <=>
        LNTH n l1 = SOME x /\ LNTH n l2 = SOME y") (fun th => REWRITE_TAC [th]) THEN INDUCT_TAC THEN REPEAT GEN_TAC THEN LLIST_CASES_TAC (← q r"l1:A llist") THEN LLIST_CASES_TAC (← q r"l2:B llist") THEN ASM_REWRITE_TAC [LZIP, LNTH, option_DISTINCT, (← GSYM option_DISTINCT), option_INJ, PAIR_EQ])

  let LZIP_LMAP ← prove
    r"!(f:A->C) (g:B->D) l1 l2.
        LZIP (LMAP f l1) (LMAP g l2) = LMAP (\(x,y). (f x,g y)) (LZIP l1 l2)"
    (LLIST_COINDUCT_TAC THEN LLIST_CASES_TAC (← q r"l1:A llist") THEN LLIST_CASES_TAC (← q r"l2:B llist") THEN REWRITE_TAC [LZIP, LMAP] THEN CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV) THEN LLIST_BISIM_TAC THEN MESON_TAC [])

  let LALL2_DEF ← define
    r"(LALL2 R (llist_of_list l1) (llist_of_list l2) <=>
   ALL2 R (l1:A list) (l2:B list)) /\
  (LALL2 R (llist_of_list l1) (llist_of_seq (g:num->B)) <=> F) /\
  (LALL2 R (llist_of_seq (f:num->A)) (llist_of_list l2) <=> F) /\
  (LALL2 R (llist_of_seq f) (llist_of_seq g) <=> !n. R (f n) (g n))"

  let LALL2 ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    prove
      r"(!R:A->B->bool. LALL2 R LNIL LNIL) /\
     (!R:A->B->bool h1 t1. ~LALL2 R (LCONS h1 t1) LNIL) /\
     (!R:A->B->bool h2 t2. ~LALL2 R LNIL (LCONS h2 t2)) /\
     (!R:A->B->bool h1 t1 h2 t2.
          LALL2 R (LCONS h1 t1) (LCONS h2 t2) <=> R h1 h2 /\ LALL2 R t1 t2)"
      (REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL [REWRITE_TAC [LNIL_DEF, LALL2_DEF, ALL2], LLIST_REP_CASES_TAC (← q r"t1:A llist") THEN REWRITE_TAC [LNIL_DEF, LCONS_DEF, LALL2_DEF, ALL2], LLIST_REP_CASES_TAC (← q r"t2:B llist") THEN REWRITE_TAC [LNIL_DEF, LCONS_DEF, LALL2_DEF, ALL2], LLIST_REP_CASES_TAC (← q r"t1:A llist") THEN LLIST_REP_CASES_TAC (← q r"t2:B llist") THEN REWRITE_TAC [LCONS_DEF, LALL2_DEF, ALL2] THEN GEN_REWRITE_TAC LAND_CONV [(← MESON [num_CASES] (← q r"(!n. P n) <=> P 0 /\ !n. P(SUC n)"))] THEN REWRITE_TAC [NOT_SUC, SUC_SUB1]])

  let LALL2_EQ ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let lemma := (← prove r"!l1 l2:A list. ALL2 (=) l1 l2 <=> l1 = l2" (LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [ALL2, CONS_11, NOT_CONS_NIL, (← GSYM NOT_CONS_NIL)]))
    prove
      r"!l1 l2:A llist. LALL2 (=) l1 l2 <=> l1 = l2"
      (REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC (← q r"l1:A llist") THEN LLIST_REP_CASES_TAC (← q r"l2:A llist") THEN REWRITE_TAC [LALL2_DEF, LLIST_REP_EQ, lemma, FUN_EQ_THM])

  let LALL2_LNTH ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let lemma := (← prove r"!R (l1:A list) (l2:B list).
        ALL2 R l1 l2 <=>
        LENGTH l1 = LENGTH l2 /\
        !n. n < LENGTH l1 ==> R (EL n l1) (EL n l2)" (GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [ALL2, LENGTH, NOT_SUC, (← GSYM NOT_SUC), SUC_INJ, (← CONJUNCT1 LT), LT_0] THEN GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [(← MESON [num_CASES] (← q r"(!n. P n) <=> P 0 /\ !n. P(SUC n)"))] THEN REWRITE_TAC [LT_0, LT_SUC, EL, HD, TL] THEN CONV_TAC TAUT))
    let lemma' := (← prove r"!b (a:A) c. (if b then SOME a else NONE) = SOME c <=> b /\ a = c" (REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [option_INJ, (← GSYM option_DISTINCT)]))
    prove
      r"!R (l1:A llist) (l2:B llist).
          LALL2 R l1 l2 <=>
          LLENGTH l1 = LLENGTH l2 /\
          !n x y. LNTH n l1 = SOME x /\ LNTH n l2 = SOME y ==> R x y"
      (REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC (← q r"l1:A llist") THEN LLIST_REP_CASES_TAC (← q r"l2:B llist") THEN REWRITE_TAC [LALL2_DEF, LLENGTH_DEF, LNTH_DEF, lemma', option_INJ, option_DISTINCT, (← GSYM option_DISTINCT), lemma] THEN MESON_TAC [])

  let LLENGTH_EQ ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let lemma := (← prove r"!(l:A list) n. LNTH n (llist_of_list l) = NONE <=> LENGTH l <= n" (REWRITE_TAC [LNTH_DEF, (← GSYM NOT_LT)] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [option_DISTINCT]))
    prove
      r"!(l1:A llist) (l2:B llist).
          LLENGTH l1 = LLENGTH l2 <=> !n. LNTH n l1 = NONE <=> LNTH n l2 = NONE"
      (REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC (← q r"l1:A llist") THEN LLIST_REP_CASES_TAC (← q r"l2:B llist") THEN REWRITE_TAC [LLENGTH_DEF, lemma, LNTH_DEF, option_INJ, option_DISTINCT, (← GSYM option_DISTINCT)] THEN MESON_TAC [LE_REFL, LE_ANTISYM])

  let LALL2_COINDUCT ← prove
    r"!R (R':A llist->B llist->bool).
        (!l1 l2. R' l1 l2
                 ==> l1 = LNIL /\ l2 = LNIL \/
                     ?h1 t1 h2 t2. l1 = LCONS h1 t1 /\ l2 = LCONS h2 t2 /\
                                   R h1 h2 /\ R' t1 t2)
        ==> !l1 l2. R' l1 l2 ==> LALL2 R l1 l2"
    (REPEAT GEN_TAC THEN DISCH_THEN (fun bisim => tactic_of do pure (REWRITE_TAC [LALL2_LNTH, LLENGTH_EQ] THEN SUBGOAL_THEN (← q r"!n (l1:A llist) (l2:B llist).
        R' l1 l2
        ==> (LNTH n l1 = NONE <=> LNTH n l2 = NONE) /\
            (!x y. LNTH n l1 = SOME x /\ LNTH n l2 = SOME y ==> R x y)") (fun th => MESON_TAC [th]) THEN INDUCT_TAC THEN REPEAT GEN_TAC THEN DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP bisim)) THEN ASM_REWRITE_TAC [LNTH, option_DISTINCT, (← GSYM option_DISTINCT), option_INJ] THEN ASM_MESON_TAC [])))

  let MONO_LALL2 ← prove
    r"(!x y. (P:A->B->bool) x y ==> Q x y) ==> LALL2 P l l' ==> LALL2 Q l l'"
    (REWRITE_TAC [LALL2_LNTH] THEN MESON_TAC [])

  -- monotonicity_theorems := MONO_LALL2 :: !monotonicity_theorems
  set_monotonicity_theorems (MONO_LALL2 :: (← get_monotonicity_theorems))

  let LPREFIX_DEF ← new_definition
    r"LPREFIX (l1:A llist) l2 <=> ?l3. l2 = LAPPEND l1 l3"

  let LPREFIX ← prove
    r"(!l:A llist. LPREFIX LNIL l) /\
   (!(h:A) t l.
        LPREFIX (LCONS h t) l <=> ?t'. l = LCONS h t' /\ LPREFIX t t')"
    (REWRITE_TAC [LPREFIX_DEF, LAPPEND] THEN MESON_TAC [])

  let LPREFIX_LAPPEND ← prove
    r"!l1 l2:A llist. LPREFIX l1 l2 <=> ?l3. l2 = LAPPEND l1 l3"
    (REWRITE_TAC [LPREFIX_DEF])

  let LPREFIX_REFL ← prove
    r"!l:A llist. LPREFIX l l"
    (MESON_TAC [LPREFIX_DEF, LAPPEND_LNIL])

  let LPREFIX_TRANS ← prove
    r"!l1 l2 l3:A llist. LPREFIX l1 l2 /\ LPREFIX l2 l3 ==> LPREFIX l1 l3"
    (MESON_TAC [LPREFIX_DEF, LAPPEND_ASSOC])

  let LPREFIX_LTAKE ← prove
    r"!n (l:A llist). LPREFIX (llist_of_list (LTAKE n l)) l"
    (MESON_TAC [LPREFIX_DEF, LTAKE_LDROP])

  let LPREFIX_LNTH ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let lemma := (← prove r"!b (a:A) c. (if b then SOME a else NONE) = SOME c <=> b /\ a = c" (REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [option_INJ, (← GSYM option_DISTINCT)]))
    prove
      r"!l1 l2:A llist.
          LPREFIX l1 l2 <=> !n x. LNTH n l1 = SOME x ==> LNTH n l2 = SOME x"
      (REPEAT GEN_TAC THEN LLIST_REP_CASES_TAC (← q r"l1:A llist") THEN REWRITE_TAC [LPREFIX_DEF, LAPPEND_DEF] THENL [EQ_TAC THENL [STRIP_TAC THEN ASM_REWRITE_TAC [LNTH_LAPPEND] THEN REWRITE_TAC [LNTH_DEF, lemma] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [], DISCH_TAC THEN EXISTS_TAC (← q r"LDROP (LENGTH (xs:A list)) (l2:A llist)") THEN REWRITE_TAC [LLIST_EQ, LNTH_LAPPEND, LNTH_LDROP] THEN X_GEN_TAC (← q r"n:num") THEN COND_CASES_TAC THENL [FIRST_X_ASSUM (MP_TAC o (SPECL [(← q r"n:num"), (← q r"EL n (xs:A list)")])) THEN ASM_REWRITE_TAC [LNTH_DEF], AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC]], EQ_TAC THENL [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [LNTH_DEF, option_INJ], REWRITE_TAC [LNTH_DEF, option_INJ] THEN DISCH_TAC THEN ASM_REWRITE_TAC [LLIST_EQ, LNTH_DEF] THEN ASM_MESON_TAC []]])

  let LPREFIX_ANTISYM ← prove
    r"!l1 l2:A llist. LPREFIX l1 l2 /\ LPREFIX l2 l1 ==> l1 = l2"
    (REWRITE_TAC [LPREFIX_LNTH, LLIST_EQ] THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"LNTH n (l1:A llist)") option_CASES) THEN MP_TAC (← ISPEC (← q r"LNTH n (l2:A llist)") option_CASES) THEN ASM_MESON_TAC [])

  let LPREFIX_COINDUCT ← prove
    r"!R:A llist->A llist->bool.
        (!l1 l2. R l1 l2
                 ==> l1 = LNIL \/
                     ?h t1 t2. l1 = LCONS h t1 /\ l2 = LCONS h t2 /\ R t1 t2)
        ==> !l1 l2. R l1 l2 ==> LPREFIX l1 l2"
    (GEN_TAC THEN DISCH_THEN (fun bisim => tactic_of do pure (REWRITE_TAC [LPREFIX_LNTH] THEN SUBGOAL_THEN (← q r"!n (l1:A llist) l2 x.
        R l1 l2 /\ LNTH n l1 = SOME x ==> LNTH n l2 = SOME x") (fun th => MESON_TAC [th]) THEN INDUCT_TAC THEN REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o (MATCH_MP bisim)) MP_TAC) THEN ASM_REWRITE_TAC [LNTH, option_DISTINCT] THEN ASM_MESON_TAC [])))

  let LLIST_OF_LNTH ← prove
    r"!f:num->A option.
        (!m n. f m = NONE /\ m <= n ==> f n = NONE)
        ==> ?l. !n. LNTH n l = f n"
    (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"?n. (f:num->A option) n = NONE") THENL [EXISTS_TAC (← q r"llist_of_list (list_of_seq (\i. THE((f:num->A option) i))
                                ((minimal) (\n. f n = NONE)))") THEN FIRST_ASSUM (MP_TAC o (GEN_REWRITE_RULE id [MINIMAL])) THEN SPEC_TAC ((← q r"(minimal) (\n. (f:num->A option) n = NONE)"), (← q r"k:num")) THEN REPEAT STRIP_TAC THEN REWRITE_TAC [LNTH_DEF, LENGTH_LIST_OF_SEQ] THEN COND_CASES_TAC THEN ASM_SIMP_TAC [EL_LIST_OF_SEQ] THENL [MP_TAC (← ISPEC (← q r"(f:num->A option) n") option_CASES) THEN ASM_MESON_TAC [THE], ASM_MESON_TAC [NOT_LT]], EXISTS_TAC (← q r"llist_of_seq (\i. THE((f:num->A option) i))") THEN REWRITE_TAC [LNTH_DEF] THEN X_GEN_TAC (← q r"n:num") THEN MP_TAC (← ISPEC (← q r"(f:num->A option) n") option_CASES) THEN ASM_MESON_TAC [THE]])

  let LPREFIX_CHAIN_LUB ← prove
    r"!s:A llist->bool.
        (!l1 l2. l1 IN s /\ l2 IN s ==> LPREFIX l1 l2 \/ LPREFIX l2 l1)
        ==> ?u. (!l. l IN s ==> LPREFIX l u) /\
                (!u'. (!l. l IN s ==> LPREFIX l u') ==> LPREFIX u u')"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"!n l1 l2 (x1:A) x2. l1 IN s /\ l2 IN s /\
                        LNTH n l1 = SOME x1 /\ LNTH n l2 = SOME x2 ==> x1 = x2") ASSUME_TAC THENL [ASM_MESON_TAC [LPREFIX_LNTH, option_INJ], ALL_TAC] THEN MP_TAC (← ISPEC (← q r"\n. if ?l (x:A). l IN s /\ LNTH n l = SOME x
        then SOME (@x. ?l. l IN s /\ LNTH n l = SOME x) else NONE") LLIST_OF_LNTH) THEN REWRITE_TAC [] THEN ANTS_TAC THENL [MAP_EVERY X_GEN_TAC [(← q r"m:num"), (← q r"n:num")] THEN COND_CASES_TAC THEN REWRITE_TAC [option_DISTINCT] THEN COND_CASES_TAC THEN REWRITE_TAC [] THEN ASM_MESON_TAC [LNTH_NONE_MONO, option_CASES, option_DISTINCT], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"u:A llist")) THEN EXISTS_TAC (← q r"u:A llist") THEN ASM_REWRITE_TAC [LPREFIX_LNTH] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"l:A llist") THEN DISCH_TAC THEN MAP_EVERY X_GEN_TAC [(← q r"n:num"), (← q r"x:A")] THEN DISCH_TAC THEN COND_CASES_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN REWRITE_TAC [option_INJ] THEN MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC [], X_GEN_TAC (← q r"u':A llist") THEN DISCH_TAC THEN MAP_EVERY X_GEN_TAC [(← q r"n:num"), (← q r"x:A")] THEN COND_CASES_TAC THEN REWRITE_TAC [(← GSYM option_DISTINCT), option_INJ] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN SUBGOAL_THEN (← q r"?l. l IN s /\ LNTH n l = SOME (@x:A. ?l. l IN s /\ LNTH n l = SOME x)") MP_TAC THENL [CONV_TAC SELECT_CONV THEN ASM_MESON_TAC [], ALL_TAC] THEN ASM_MESON_TAC []])

  let LPREFIX_LTAKE_LUB ← prove
    r"!(l:A llist) u.
        (!n. LPREFIX (llist_of_list (LTAKE n l)) u) ==> LPREFIX l u"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [LPREFIX_LNTH] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o ((GEN_REWRITE_RULE id [LPREFIX_LNTH]) o (SPEC (← q r"SUC n")))) THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [LNTH_LTAKE])

  let LITERATE_DEF ← new_definition
    r"LITERATE (f:A->A) x = llist_of_seq (\n. ITER n f x)"

  let LITERATE ← prove
    r"!(f:A->A) x. LITERATE f x = LCONS x (LITERATE f (f x))"
    (REWRITE_TAC [LITERATE_DEF] THEN REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [LLIST_OF_SEQ] THEN REWRITE_TAC [ITER_ALT])

  let LFINITE_LITERATE ← prove
    r"!(f:A->A) x. ~LFINITE (LITERATE f x)"
    (REWRITE_TAC [LITERATE_DEF, LFINITE_DEF])

  let LMAP_LITERATE ← prove
    r"!(f:A->A) x. LMAP f (LITERATE f x) = LITERATE f (f x)"
    (REWRITE_TAC [LITERATE_DEF, LMAP_DEF, LLIST_REP_EQ, FUN_EQ_THM, o_THM] THEN REWRITE_TAC [(← GSYM (← CONJUNCT2 ITER)), ITER_ALT])

  -- @@RETURN BEGIN
  return { LFILTER_LLIST_OF_LIST, SET_OF_LLIST_LFILTER, LALL_LFILTER, LFILTER_LFILTER,
           LFLATTEN_DEF, LFLATTEN_UNFOLD, LFLATTEN, LFLATTEN_EQ_LNIL, LFLATTEN_INFINITE,
           LFLATTEN_LCONS, LMAP_LFLATTEN, LZIP_DEF, LZIP, LNTH_LZIP, LZIP_LMAP,
           LALL2_DEF, LALL2, LALL2_EQ, LALL2_LNTH, LLENGTH_EQ, LALL2_COINDUCT,
           MONO_LALL2, LPREFIX_DEF, LPREFIX, LPREFIX_LAPPEND, LPREFIX_REFL,
           LPREFIX_TRANS, LPREFIX_LTAKE, LPREFIX_LNTH, LPREFIX_ANTISYM, LPREFIX_COINDUCT,
           LLIST_OF_LNTH, LPREFIX_CHAIN_LUB, LPREFIX_LTAKE_LUB, LITERATE_DEF, LITERATE,
           LFINITE_LITERATE, LMAP_LITERATE }
  -- @@RETURN END

end HolLibrary.Llist
