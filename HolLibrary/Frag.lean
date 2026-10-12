/- ========================================================================= -/
/- A formulation of free Abelian groups on :A using a type :(A)frag.         -/
/- ========================================================================= -/
/- File: HolLibrary/Frag.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/frag.ml`, by hand, in file order, in
  the style of HolLibrary/Products.lean and HolLibrary/BitMatch.lean (see
  there and HolMath/Base.lean for the conventions).  frag.ml has no `needs`:
  it runs on the core library.  The whole file is a single bundle (a
  `structure`) built by a `setup` function; SessionLibrary/Frag.lean builds
  the bundle and exports every name under its HOL Light name.

  frag.ml begins with `new_type_definition "frag"`, defines the free Abelian
  group operations, and includes a tactic-valued rule `FRAG_MODULE`
  (`fun tm -> prove (tm, tac)`); its `tac` is built once, so `FRAG_MODULE` is
  a `term -> ExceptT String IO thm` closing over the fixed tactic.

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  INT_ARITH, INT_RING and INT_REDUCE_CONV come from Session.
-/

import HolMath
import HolLibrary.Products

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

set_option maxRecDepth 8000

namespace HolLibrary.Frag

/- ------------------------------------------------------------------------- -/
/- What frag.ml uses from the core library (supplied by Session).            -/
/- ------------------------------------------------------------------------- -/

/-- Theorems frag.ml uses from the core library (part 1 of 2). -/
structure CoreThms1 where
  (AND_FORALL_THM BETA_THM COND_RAND COND_RATOR CONJ_ASSOC CONTRAPOS_THM
   DE_MORGAN_THM EMPTY_GSPEC EMPTY_SUBSET ETA_AX EXTENSION FINITE_EMPTY
   FINITE_INDUCT_STRONG FINITE_SING FINITE_SUBSET FINITE_UNION
   FORALL_IN_GSPEC FUN_EQ_THM IMAGE_CLAUSES IMAGE_SUBSET IMP_CONJ
   IMP_CONJ_ALT INSERT_SUBSET INT_ADD_LID INT_ENTIRE INT_FORALL_POS
   INT_MUL_LZERO INT_MUL_RZERO INT_NEG_EQ_0 INT_OF_NUM_SUC INT_SUB_RZERO
   IN_ELIM_THM IN_INSERT IN_UNION IN_UNIV : thm)
  deriving Inhabited

/-- Theorems frag.ml uses from the core library (part 2 of 2). -/
structure CoreThms2 where
  (ITERATE_CLAUSES ITERATE_EQ ITERATE_EQ_NEUTRAL ITERATE_EXPAND_CASES
   ITERATE_OP_GEN ITERATE_UNIV I_THM LEFT_OR_FORALL_THM MONO_FORALL
   NOT_IN_EMPTY RIGHT_FORALL_IMP_THM RIGHT_OR_FORALL_THM SIMPLE_IMAGE
   SING_GSPEC SUBSET SUBSET_TRANS SUBSET_UNIONS SUBSET_UNIV SUPPORT_SUBSET
   SWAP_FORALL_THM UNIONS_MONO_IMAGE UNIONS_SUBSET monoidal neutral o_THM
   support : thm)
  deriving Inhabited

/-- What frag.ml uses from Session besides theorems. -/
structure FragDeps where
  -- definitions, type definitions and parser state
  new_definition : String → ExceptT String IO thm
  new_type_definition : String → String × String → thm → ExceptT String IO thm
  -- decision procedures and tactics
  INT_ARITH : term → ExceptT String IO thm
  INT_ARITH_TAC : tactic
  INT_RING : term → ExceptT String IO thm
  INT_REDUCE_CONV : ioconv
  INDUCT_TAC : tactic
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  core1 : CoreThms1
  core2 : CoreThms2

/- ------------------------------------------------------------------------- -/
/- The type :(A)frag, its operations, support, extension and induction.      -/
/- (the whole of frag.ml)                                                    -/
/- ------------------------------------------------------------------------- -/

structure Frag where
  -- @@FIELDS
  frag_tybij : thm
  frag_support : thm
  frag_0 : thm
  frag_of : thm
  frag_neg : thm
  frag_cmul : thm
  frag_add : thm
  frag_sub : thm
  FRAG_EQ : thm
  DEST_FRAG_0 : thm
  DEST_FRAG_OF : thm
  DEST_FRAG_NEG : thm
  DEST_FRAG_CMUL : thm
  DEST_FRAG_ADD : thm
  DEST_FRAG_SUB : thm
  FRAG_OF_NONZERO : thm
  FRAG_MODULE : term → ExceptT String IO thm
  FINITE_FRAG_SUPPORT : thm
  FRAG_SUPPORT_0 : thm
  FRAG_SUPPORT_OF : thm
  FRAG_SUPPORT_NEG : thm
  FRAG_SUPPORT_CMUL : thm
  FRAG_SUPPORT_ADD : thm
  FRAG_SUPPORT_SUB : thm
  FRAG_SUPPORT_EQ_EMPTY : thm
  FRAG_OF_EQ : thm
  FRAG_ADD_EQ_0 : thm
  NEUTRAL_FRAG_ADD : thm
  MONOIDAL_FRAG_ADD : thm
  FRAG_CMUL_SUM : thm
  FRAG_SUPPORT_SUM : thm
  frag_extend : thm
  FRAG_EXTEND : thm
  FRAG_EXTEND_0 : thm
  FRAG_EXTEND_OF : thm
  FRAG_EXTEND_CMUL : thm
  FRAG_EXTEND_NEG : thm
  FRAG_EXTEND_ADD : thm
  FRAG_EXTEND_SUB : thm
  FRAG_EXTEND_SUM : thm
  FRAG_EXTEND_EQ : thm
  FRAG_EXTEND_EQ_0 : thm
  FRAG_SUPPORT_FRAG_EXTEND : thm
  FRAG_EXPANSION : thm
  FRAG_CLOSURE_SUB_CMUL : thm
  FRAG_INDUCTION : thm
  FRAG_EXTEND_COMPOSE : thm
  FRAG_SPLIT : thm
  deriving Inhabited

@[nospecialize]
def setupFrag [HolBase] (D : FragDeps) :
    ExceptT String IO Frag := do
  -- @@SCOPE BEGIN
  let { INDUCT_TAC, INT_ARITH, INT_ARITH_TAC, INT_REDUCE_CONV, INT_RING, MESON,
        MESON_TAC, SET_RULE, SET_TAC, new_definition, new_type_definition, .. } := D
  let { AND_FORALL_THM, BETA_THM, COND_RAND, COND_RATOR, CONJ_ASSOC, CONTRAPOS_THM,
        DE_MORGAN_THM, EMPTY_GSPEC, EMPTY_SUBSET, ETA_AX, EXTENSION, FINITE_EMPTY,
        FINITE_INDUCT_STRONG, FINITE_SING, FINITE_SUBSET, FINITE_UNION,
        FORALL_IN_GSPEC, FUN_EQ_THM, IMAGE_CLAUSES, IMAGE_SUBSET, IMP_CONJ,
        IMP_CONJ_ALT, INSERT_SUBSET, INT_ADD_LID, INT_ENTIRE, INT_FORALL_POS,
        INT_MUL_LZERO, INT_MUL_RZERO, INT_NEG_EQ_0, INT_OF_NUM_SUC, INT_SUB_RZERO,
        IN_ELIM_THM, IN_INSERT, IN_UNION, IN_UNIV, .. } := D.core1
  let { ITERATE_CLAUSES, ITERATE_EQ, ITERATE_EQ_NEUTRAL, ITERATE_EXPAND_CASES,
        ITERATE_OP_GEN, ITERATE_UNIV, I_THM, LEFT_OR_FORALL_THM, MONO_FORALL,
        NOT_IN_EMPTY, RIGHT_FORALL_IMP_THM, RIGHT_OR_FORALL_THM, SIMPLE_IMAGE,
        SING_GSPEC, SUBSET, SUBSET_TRANS, SUBSET_UNIONS, SUBSET_UNIV, SUPPORT_SUBSET,
        SWAP_FORALL_THM, UNIONS_MONO_IMAGE, UNIONS_SUBSET, monoidal, neutral, o_THM,
        support, .. } := D.core2
  -- @@SCOPE END

  let frag_tybij ← do
    let th ← prove
     r"?f:A->int. FINITE {x | ~(f x = &0)}"
     (EXISTS_TAC (← q r"(\x. &0):A->int") THEN
      REWRITE_TAC [EMPTY_GSPEC, FINITE_EMPTY])
    new_type_definition "frag" ("mk_frag", "dest_frag") th

  let frag_support ← new_definition
   r"frag_support (x:A frag) = {a | ~(dest_frag x a = &0)}"

  let frag_0 ← new_definition
   r"frag_0:A frag = mk_frag (\x. &0)"

  let frag_of ← new_definition
   r"frag_of (c:A) = mk_frag (\a. if a = c then &1 else &0)"

  let frag_neg ← new_definition
   r"frag_neg (x:A frag) = mk_frag (\a. --(dest_frag x a))"

  let frag_cmul ← new_definition
   r"frag_cmul c (x:A frag) = mk_frag (\a. c * dest_frag x a)"

  let frag_add ← new_definition
   r"frag_add (x:A frag) y = mk_frag (\a. dest_frag x a + dest_frag y a)"

  let frag_sub ← new_definition
   r"frag_sub (x:A frag) y = mk_frag (\a. dest_frag x a - dest_frag y a)"

  let FRAG_EQ ← prove
   r"!c1 c2:A frag. c1 = c2 <=> dest_frag c1 = dest_frag c2"
   (MESON_TAC [frag_tybij])

  let DEST_FRAG_0 ← prove
   r"dest_frag(frag_0:A frag) = \x. &0"
   (REWRITE_TAC [frag_0, ← GSYM (← CONJUNCT2 frag_tybij)] THEN
    REWRITE_TAC [EMPTY_GSPEC, FINITE_EMPTY])

  let DEST_FRAG_OF ← prove
   r"!c:A. dest_frag(frag_of c) = \a. if a = c then &1 else &0"
   (← do
    let m ← MESON [] (← q r"~(if p then F else T) <=> p")
    pure (REWRITE_TAC [frag_of, ← GSYM (← CONJUNCT2 frag_tybij)] THEN
      ONCE_REWRITE_TAC [COND_RAND] THEN ONCE_REWRITE_TAC [COND_RATOR] THEN
      CONV_TAC INT_REDUCE_CONV THEN
      REWRITE_TAC [m] THEN
      REWRITE_TAC [SING_GSPEC, FINITE_SING]))

  let DEST_FRAG_NEG ← prove
   r"!x:A frag. dest_frag(frag_neg x) = \a. --(dest_frag x a)"
   (REWRITE_TAC [frag_neg, ← GSYM (← CONJUNCT2 frag_tybij)] THEN
    REWRITE_TAC [INT_NEG_EQ_0] THEN REWRITE_TAC [frag_tybij, ETA_AX])

  let DEST_FRAG_CMUL ← prove
   r"!c x:A frag. dest_frag(frag_cmul c x) = \a. c * dest_frag x a"
   (REPEAT GEN_TAC THEN REWRITE_TAC [frag_cmul, ← GSYM (← CONJUNCT2 frag_tybij)] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC (← q r"{a:A | ~(dest_frag x a = &0)}") THEN
    SIMP_TAC [SUBSET, IN_ELIM_THM, CONTRAPOS_THM, INT_MUL_RZERO] THEN
    REWRITE_TAC [frag_tybij, ETA_AX])

  let DEST_FRAG_ADD ← prove
   r"!x y:A frag. dest_frag(frag_add x y) = \a. dest_frag x a + dest_frag y a"
   (REPEAT GEN_TAC THEN REWRITE_TAC [frag_add, ← GSYM (← CONJUNCT2 frag_tybij)] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
     (← q r"{a:A | ~(dest_frag x a = &0)} UNION {a | ~(dest_frag y a = &0)}") THEN
    SIMP_TAC [SUBSET, IN_ELIM_THM, IN_UNION] THEN
    SIMP_TAC [← GSYM DE_MORGAN_THM, CONTRAPOS_THM, INT_ADD_LID] THEN
    REWRITE_TAC [FINITE_UNION, frag_tybij, ETA_AX])

  let DEST_FRAG_SUB ← prove
   r"!x y:A frag. dest_frag(frag_sub x y) = \a. dest_frag x a - dest_frag y a"
   (REPEAT GEN_TAC THEN REWRITE_TAC [frag_sub, ← GSYM (← CONJUNCT2 frag_tybij)] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
     (← q r"{a:A | ~(dest_frag x a = &0)} UNION {a | ~(dest_frag y a = &0)}") THEN
    SIMP_TAC [SUBSET, IN_ELIM_THM, IN_UNION] THEN
    SIMP_TAC [← GSYM DE_MORGAN_THM, CONTRAPOS_THM, INT_SUB_RZERO] THEN
    REWRITE_TAC [FINITE_UNION, frag_tybij, ETA_AX])

  let FRAG_OF_NONZERO ← prove
   r"!a:A. ~(frag_of a = frag_0)"
   (← do
    let m ← MESON [] (← q r"c = d ==> !a:A. dest_frag c a = dest_frag d a")
    pure (GEN_TAC THEN DISCH_THEN (MP_TAC o SPEC (← q "a:A") o MATCH_MP m) THEN
      REWRITE_TAC [DEST_FRAG_OF, DEST_FRAG_0] THEN
      CONV_TAC INT_REDUCE_CONV))

  -- `let FRAG_MODULE = let tac = ... in fun tm -> prove(tm,tac)`: the tactic
  -- `tac` is built once at setup time, so FRAG_MODULE is a rule closing over
  -- it.
  let FRAG_MODULE : term → ExceptT String IO thm ← do
    let m ← MESON [← CONJUNCT1 frag_tybij, FUN_EQ_THM]
      (← q r"!x y:A frag. x = y <=> !a. dest_frag x a = dest_frag y a")
    let tac :=
      REPEAT (CONJ_TAC ORELSE GEN_TAC) THEN
      GEN_REWRITE_TAC ONCE_DEPTH_CONV [m] THEN
      GEN_REWRITE_TAC TOP_DEPTH_CONV
        [DEST_FRAG_0, DEST_FRAG_NEG, DEST_FRAG_CMUL,
         DEST_FRAG_ADD, DEST_FRAG_SUB, BETA_THM] THEN
      GEN_REWRITE_TAC DEPTH_CONV
        [AND_FORALL_THM, LEFT_OR_FORALL_THM, RIGHT_OR_FORALL_THM] THEN
      ((MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) ORELSE
       TRY (AP_TERM_TAC THEN ABS_TAC)) THEN
      CONV_TAC INT_RING
    pure (fun tm => ExceptT.mk (HolCore.Tactics.prove HolBase.B tm tac))

  let FINITE_FRAG_SUPPORT ← prove
   r"!x:A frag. FINITE(frag_support (x:A frag))"
   (REWRITE_TAC [frag_support, frag_tybij, ETA_AX])

  let FRAG_SUPPORT_0 ← prove
   r"frag_support frag_0 = {}"
   (REWRITE_TAC [frag_support, DEST_FRAG_0, EMPTY_GSPEC])

  let FRAG_SUPPORT_OF ← prove
   r"!a:A. frag_support(frag_of a) = {a}"
   (← do
    let m ← MESON [] (← q r"~(if p then F else T) <=> p")
    pure (REWRITE_TAC [frag_support, DEST_FRAG_OF] THEN
      ONCE_REWRITE_TAC [COND_RAND] THEN ONCE_REWRITE_TAC [COND_RATOR] THEN
      CONV_TAC INT_REDUCE_CONV THEN
      REWRITE_TAC [m] THEN
      REWRITE_TAC [SING_GSPEC]))

  let FRAG_SUPPORT_NEG ← prove
   r"!x:A frag. frag_support(frag_neg x) = frag_support x"
   (REWRITE_TAC [frag_support, DEST_FRAG_NEG, INT_NEG_EQ_0])

  let FRAG_SUPPORT_CMUL ← prove
   r"!a x:A frag. frag_support(frag_cmul a x) SUBSET frag_support x"
   (REWRITE_TAC [frag_support, DEST_FRAG_CMUL] THEN
    SIMP_TAC [SUBSET, IN_ELIM_THM, CONTRAPOS_THM, INT_MUL_RZERO] THEN
    REWRITE_TAC [frag_tybij, ETA_AX])

  let FRAG_SUPPORT_ADD ← prove
   r"!x y:A frag. frag_support(frag_add x y) SUBSET
                frag_support x UNION frag_support y"
   (REWRITE_TAC [frag_support, DEST_FRAG_ADD] THEN
    SIMP_TAC [SUBSET, IN_ELIM_THM, IN_UNION] THEN
    SIMP_TAC [← GSYM DE_MORGAN_THM, CONTRAPOS_THM, INT_ADD_LID])

  let FRAG_SUPPORT_SUB ← prove
   r"!x y:A frag. frag_support(frag_sub x y) SUBSET
                frag_support x UNION frag_support y"
   (REWRITE_TAC [frag_support, DEST_FRAG_SUB] THEN
    SIMP_TAC [SUBSET, IN_ELIM_THM, IN_UNION] THEN
    SIMP_TAC [← GSYM DE_MORGAN_THM, CONTRAPOS_THM, INT_SUB_RZERO])

  let FRAG_SUPPORT_EQ_EMPTY ← prove
   r"!c:A frag. frag_support c = {} <=> c = frag_0"
   (← do
    let m ← MESON [frag_tybij] (← q r"c = d <=> dest_frag c = dest_frag d")
    pure (REWRITE_TAC [EXTENSION, NOT_IN_EMPTY] THEN
      REWRITE_TAC [m] THEN
      REWRITE_TAC [DEST_FRAG_0, FUN_EQ_THM, frag_support, IN_ELIM_THM]))

  let FRAG_OF_EQ ← prove
   r"!x y:A. frag_of x = frag_of y <=> x = y"
   (← do
    let s ← SET_RULE (← q r"{x} = {y} <=> x = y")
    pure (MESON_TAC [FRAG_SUPPORT_OF, s]))

  let FRAG_ADD_EQ_0 ← prove
   r"!c1 c2:A frag.
        DISJOINT (frag_support c1) (frag_support c2) /\
        frag_add c1 c2 = frag_0
        ==> c1 = frag_0 /\ c2 = frag_0"
   (← do
    let a ← INT_ARITH
     (← q r"~(~(x:int = &0) /\ ~(y = &0)) ==> x + y = &0 ==> x = &0 /\ y = &0")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [frag_support, FRAG_EQ] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      REWRITE_TAC [DEST_FRAG_ADD, DEST_FRAG_0, FUN_EQ_THM, AND_FORALL_THM] THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC a THEN
      ASM SET_TAC []))

  let NEUTRAL_FRAG_ADD ← prove
   r"neutral frag_add :A frag = frag_0"
   (← do
    let f ← FRAG_MODULE
     (← q r"(frag_add x y = y <=> x = frag_0) /\
            (frag_add y x = y <=> x = frag_0)")
    pure (REWRITE_TAC [neutral, f]))

  let MONOIDAL_FRAG_ADD ← prove
   r"monoidal frag_add"
   (REWRITE_TAC [monoidal, NEUTRAL_FRAG_ADD] THEN CONV_TAC FRAG_MODULE)

  let FRAG_CMUL_SUM ← prove
   r"!f:B->A frag k a.
        frag_cmul a (iterate frag_add k f) =
        iterate frag_add k (\b. frag_cmul a (f b))"
   (← do
    let f3 ← FRAG_MODULE
     (← q r"frag_cmul a (frag_add x y) =
            frag_add (frag_cmul a x) (frag_cmul a y)")
    -- frag.ml calls `FRAG_MODULE \`frag_cmul a frag_0 = frag_0\`` twice
    -- (lines 193 and 188); both calls are made, the later one first.
    let f2b ← FRAG_MODULE (← q r"frag_cmul a frag_0 = frag_0")
    let f2 ← FRAG_MODULE (← q r"frag_cmul a frag_0 = frag_0")
    let f1 ← FRAG_MODULE (← q r"frag_cmul a c = frag_0 <=> a = &0 \/ c = frag_0")
    let r0 ← REWRITE_RULE [NEUTRAL_FRAG_ADD]
      (← MATCH_MP ITERATE_EQ_NEUTRAL MONOIDAL_FRAG_ADD)
    let f0 ← FRAG_MODULE (← q r"frag_cmul (&0) x = frag_0")
    pure (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "a:int = &0") THEN
      ASM_SIMP_TAC [INT_MUL_LZERO, f0, r0] THEN
      ONCE_REWRITE_TAC [ITERATE_EXPAND_CASES] THEN
      ASM_REWRITE_TAC [support, NEUTRAL_FRAG_ADD, f1] THEN
      COND_CASES_TAC THEN
      ASM_REWRITE_TAC [f2] THEN
      UNDISCH_TAC (← q r"FINITE {x | x IN k /\ ~((f:B->A frag) x = frag_0)}") THEN
      SPEC_TAC (← q r"{x | x IN k /\ ~((f:B->A frag) x = frag_0)}", ← q r"k:B->bool") THEN
      MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
      SIMP_TAC [← MATCH_MP ITERATE_CLAUSES MONOIDAL_FRAG_ADD] THEN
      REWRITE_TAC [NEUTRAL_FRAG_ADD, f2b] THEN
      SIMP_TAC [f3]))

  let FRAG_SUPPORT_SUM ← prove
   r"!f:B->A frag k.
        frag_support(iterate frag_add k f) SUBSET
        UNIONS {frag_support(f i) | i IN k}"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [ITERATE_EXPAND_CASES] THEN
    REWRITE_TAC [NEUTRAL_FRAG_ADD] THEN COND_CASES_TAC THEN
    REWRITE_TAC [FRAG_SUPPORT_0, EMPTY_SUBSET] THEN
    TRANS_TAC SUBSET_TRANS
     (← q r"UNIONS {frag_support (f i) |i| i IN support frag_add (f:B->A frag) k}") THEN
    CONJ_TAC THENL
     [POP_ASSUM MP_TAC THEN
      SPEC_TAC (← q r"support frag_add (f:B->A frag) k", ← q r"k:B->bool") THEN
      MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
      SIMP_TAC [← MATCH_MP ITERATE_CLAUSES MONOIDAL_FRAG_ADD] THEN
      REWRITE_TAC [SIMPLE_IMAGE, IMAGE_CLAUSES, NEUTRAL_FRAG_ADD] THEN
      REWRITE_TAC [FRAG_SUPPORT_0, EMPTY_SUBSET] THEN
      REPEAT STRIP_TAC THEN
      W (MP_TAC o PART_MATCH lhand FRAG_SUPPORT_ADD o lhand o snd) THEN
      ASM SET_TAC [],
      REWRITE_TAC [SIMPLE_IMAGE] THEN MATCH_MP_TAC SUBSET_UNIONS THEN
      SIMP_TAC [SUPPORT_SUBSET, IMAGE_SUBSET]])

  let frag_extend ← new_definition
   r"frag_extend (f:A->B frag) x =
        iterate frag_add (frag_support x)
            (\a. frag_cmul (dest_frag x a) (f a))"

  let FRAG_EXTEND ← prove
   r"!f:A->B frag x.
        frag_extend f x =
        iterate frag_add UNIV (\a. frag_cmul (dest_frag x a) (f a))"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [frag_extend] THEN
    MATCH_MP_TAC (← MATCH_MP ITERATE_UNIV MONOIDAL_FRAG_ADD) THEN
    REWRITE_TAC [support, NEUTRAL_FRAG_ADD, frag_support, IN_UNIV] THEN
    SIMP_TAC [SUBSET, IN_ELIM_THM, CONTRAPOS_THM] THEN
    REPEAT STRIP_TAC THEN CONV_TAC FRAG_MODULE)

  let FRAG_EXTEND_0 ← prove
   r"!f:A->B frag. frag_extend f frag_0 = frag_0"
   (REWRITE_TAC [frag_extend, FRAG_SUPPORT_0] THEN
    REWRITE_TAC [← MATCH_MP ITERATE_CLAUSES MONOIDAL_FRAG_ADD] THEN
    REWRITE_TAC [NEUTRAL_FRAG_ADD])

  let FRAG_EXTEND_OF ← prove
   r"!f:A->B frag a. frag_extend f (frag_of a) = f a"
   (REWRITE_TAC [frag_extend, FRAG_SUPPORT_OF] THEN
    SIMP_TAC [← MATCH_MP ITERATE_CLAUSES MONOIDAL_FRAG_ADD, FINITE_EMPTY] THEN
    REWRITE_TAC [NOT_IN_EMPTY, NEUTRAL_FRAG_ADD, DEST_FRAG_OF] THEN
    CONV_TAC FRAG_MODULE)

  let FRAG_EXTEND_CMUL ← prove
   r"!f:A->B frag c x.
        frag_extend f (frag_cmul c x) = frag_cmul c (frag_extend f x)"
   (← do
    let f1 ← FRAG_MODULE
      (← q r"frag_cmul (a * b) c = frag_cmul a (frag_cmul b c)")
    let f0 ← FRAG_MODULE (← q r"frag_cmul (&0) x = frag_0")
    pure (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q "c:int = &0") THEN
      ASM_REWRITE_TAC [f0, FRAG_EXTEND_0] THEN
      REWRITE_TAC [frag_extend, frag_support, DEST_FRAG_CMUL] THEN
      ASM_REWRITE_TAC [INT_ENTIRE, FRAG_CMUL_SUM, f1]))

  let FRAG_EXTEND_NEG ← prove
   r"!f:A->B frag x.
        frag_extend f (frag_neg x) = frag_neg(frag_extend f x)"
   (← do
    let f ← FRAG_MODULE (← q r"frag_neg x = frag_cmul (-- &1) x")
    pure (REWRITE_TAC [f] THEN
      REWRITE_TAC [FRAG_EXTEND_CMUL]))

  let FRAG_EXTEND_ADD ← prove
   r"!f:A->B frag x y.
        frag_extend f (frag_add x y) =
        frag_add (frag_extend f x) (frag_extend f y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [FRAG_EXTEND] THEN
      W (MP_TAC o PART_MATCH (rand o rand)
          (← MATCH_MP ITERATE_OP_GEN MONOIDAL_FRAG_ADD) o rand o snd) THEN
      REWRITE_TAC [] THEN ANTS_TAC THENL
       [REWRITE_TAC [support, NEUTRAL_FRAG_ADD, IN_UNIV] THEN
        CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THENL
         [EXISTS_TAC (← q r"frag_support (x:A frag)"),
          EXISTS_TAC (← q r"frag_support (y:A frag)")] THEN
        REWRITE_TAC [FINITE_FRAG_SUPPORT] THEN
        SIMP_TAC [SUBSET, IN_ELIM_THM, CONTRAPOS_THM, frag_support] THEN
        REPEAT STRIP_TAC THEN CONV_TAC FRAG_MODULE,
        DISCH_THEN (SUBST1_TAC o SYM) THEN
        MATCH_MP_TAC (← MATCH_MP ITERATE_EQ MONOIDAL_FRAG_ADD) THEN
        REWRITE_TAC [IN_UNIV] THEN CONV_TAC FRAG_MODULE])

  let FRAG_EXTEND_SUB ← prove
   r"!f:A->B frag x y.
        frag_extend f (frag_sub x y) =
        frag_sub (frag_extend f x) (frag_extend f y)"
   (← do
    let f ← FRAG_MODULE
     (← q r"frag_sub x y = frag_add x (frag_cmul (-- &1) y)")
    pure (REWRITE_TAC [f] THEN
      REWRITE_TAC [FRAG_EXTEND_CMUL, FRAG_EXTEND_ADD]))

  let FRAG_EXTEND_SUM ← prove
   r"!f:A->B frag g k:C->bool.
        FINITE k
        ==> frag_extend f (iterate frag_add k g) =
            iterate frag_add k (frag_extend f o g)"
   (GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [← MATCH_MP ITERATE_CLAUSES MONOIDAL_FRAG_ADD] THEN
    SIMP_TAC [NEUTRAL_FRAG_ADD, FRAG_EXTEND_0, FRAG_EXTEND_ADD, o_THM])

  let FRAG_EXTEND_EQ ← prove
   r"!(g:A->B frag) h c.
        (!f. f IN frag_support c ==> g f = h f)
        ==> frag_extend g c = frag_extend h c"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [frag_extend] THEN
    MATCH_MP_TAC (← MATCH_MP ITERATE_EQ MONOIDAL_FRAG_ADD) THEN
    ASM_SIMP_TAC [])

  let FRAG_EXTEND_EQ_0 ← prove
   r"!(f:A->B frag) c.
        (!a. a IN frag_support c ==> f a = frag_0)
        ==> frag_extend f c = frag_0"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [frag_extend] THEN
    REWRITE_TAC [← GSYM NEUTRAL_FRAG_ADD] THEN
    MATCH_MP_TAC (← MATCH_MP ITERATE_EQ_NEUTRAL MONOIDAL_FRAG_ADD) THEN
    ASM_SIMP_TAC [NEUTRAL_FRAG_ADD] THEN REPEAT STRIP_TAC THEN
    CONV_TAC FRAG_MODULE)

  let FRAG_SUPPORT_FRAG_EXTEND ← prove
   r"!f:A->B frag c.
        frag_support(frag_extend f c) SUBSET
        UNIONS {frag_support(f a) | a IN frag_support c}"
   (REPEAT GEN_TAC THEN REWRITE_TAC [frag_extend] THEN
    W (MP_TAC o PART_MATCH lhand FRAG_SUPPORT_SUM o lhand o snd) THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] SUBSET_TRANS) THEN
    REWRITE_TAC [SIMPLE_IMAGE] THEN MATCH_MP_TAC UNIONS_MONO_IMAGE THEN
    REWRITE_TAC [FRAG_SUPPORT_CMUL])

  let FRAG_EXPANSION ← prove
   r"!x:A frag. x = frag_extend frag_of x"
   (← do
    let m ← MESON [frag_tybij]
     (← q r"dest_frag x = dest_frag y ==> x = y")
    pure (GEN_TAC THEN REWRITE_TAC [frag_extend] THEN MATCH_MP_TAC m THEN
      REWRITE_TAC [o_THM, FUN_EQ_THM, I_THM] THEN X_GEN_TAC (← q "b:A") THEN
      SUBGOAL_THEN
       (← q r"!k. FINITE k
            ==> dest_frag(iterate frag_add k
                            (\a:A. frag_cmul (dest_frag x a) (frag_of a))) b =
                if b IN k then dest_frag x b else &0")
       (fun th => SIMP_TAC [th, FINITE_FRAG_SUPPORT])
      THENL
       [MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
        SIMP_TAC [← MATCH_MP ITERATE_CLAUSES MONOIDAL_FRAG_ADD] THEN
        REWRITE_TAC [NOT_IN_EMPTY, NEUTRAL_FRAG_ADD, DEST_FRAG_0] THEN
        SIMP_TAC [DEST_FRAG_ADD, DEST_FRAG_CMUL, DEST_FRAG_OF] THEN
        MAP_EVERY X_GEN_TAC [← q "a:A", ← q r"k:A->bool"] THEN
        ASM_CASES_TAC (← q "b:A = a") THEN ASM_SIMP_TAC [IN_INSERT] THEN INT_ARITH_TAC,
        REWRITE_TAC [frag_support, IN_ELIM_THM] THEN MESON_TAC []]))

  let FRAG_CLOSURE_SUB_CMUL ← prove
   r"!P:A frag->bool.
        P frag_0 /\
        (!c1 c2. P c1 /\ P c2 ==> P(frag_sub c1 c2))
        ==> !a c. P c ==> P(frag_cmul a c)"
   (← do
    -- right to left: the second THENL branch (fsub, then f2), the
    -- INT_ARITH, then the first branch (f0, then f1)
    let fsub ← FRAG_MODULE (← q r"frag_sub x y = frag_sub x z <=> y = z")
    let f2 ← FRAG_MODULE
     (← q r"frag_cmul a x = frag_sub frag_0 (frag_cmul (--a) x)")
    let a1 ← INT_ARITH (← q r"&0:int <= a \/ &0 <= --a")
    let f0 ← FRAG_MODULE (← q r"frag_cmul (&0) x = frag_0")
    let f1 ← FRAG_MODULE
     (← q r"frag_cmul (a + &1) x = frag_sub (frag_cmul a x) (frag_sub frag_0 x)")
    pure (GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
      REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"!n. (P:(A frag)->bool) (frag_cmul (&n) c)") ASSUME_TAC THENL
       [INDUCT_TAC THEN REWRITE_TAC [← GSYM INT_OF_NUM_SUC, f1] THEN
        ASM_SIMP_TAC [DEST_FRAG_0, f0],
        ALL_TAC] THEN
      X_GEN_TAC (← q "a:int") THEN
      DISJ_CASES_TAC a1 THENL
       [UNDISCH_TAC (← q "&0:int <= a") THEN SPEC_TAC (← q "a:int", ← q "a:int"),
        ONCE_REWRITE_TAC [f2] THEN
        ASM_SIMP_TAC [DEST_FRAG_CMUL, DEST_FRAG_0, fsub] THEN
        UNDISCH_TAC (← q "&0:int <= --a") THEN SPEC_TAC (← q "--a:int", ← q "a:int")] THEN
      ASM_SIMP_TAC [← GSYM INT_FORALL_POS]))

  let FRAG_INDUCTION ← prove
   r"!P:A frag->bool s.
        P frag_0 /\
        (!a. a IN s ==> P(frag_of a)) /\
        (!c1 c2. P c1 /\ P c2 ==> P(frag_sub c1 c2))
        ==> !c. frag_support c SUBSET s ==> P c"
   (← do
    let f ← FRAG_MODULE
     (← q r"frag_add x y = frag_sub x (frag_sub frag_0 y)")
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
      MP_TAC (← ISPEC (← q r"P:A frag->bool") FRAG_CLOSURE_SUB_CMUL) THEN
      ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
      GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV o RAND_CONV) [FRAG_EXPANSION] THEN
      REWRITE_TAC [frag_extend, o_THM] THEN X_GEN_TAC (← q "c:A frag") THEN
      MP_TAC (← ISPEC (← q "c:A frag") FINITE_FRAG_SUPPORT) THEN
      SPEC_TAC (← q r"frag_support(c:A frag)", ← q r"k:A->bool") THEN
      MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
      SIMP_TAC [← MATCH_MP ITERATE_CLAUSES MONOIDAL_FRAG_ADD] THEN
      ASM_REWRITE_TAC [NEUTRAL_FRAG_ADD, INSERT_SUBSET] THEN
      REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [f] THEN
      REPEAT (FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM SET_TAC []))

  let FRAG_EXTEND_COMPOSE ← prove
   r"!(f:B->C frag) (g:A->B) c.
        frag_extend f (frag_extend (frag_of o g) c) = frag_extend (f o g) c"
   (← do
    let m ← MESON [SUBSET_UNIV]
     (← q r"(!c. frag_support c SUBSET UNIV ==> P c) ==> (!c. P c)")
    pure (GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC m THEN
      MATCH_MP_TAC FRAG_INDUCTION THEN
      SIMP_TAC [FRAG_EXTEND_0, FRAG_EXTEND_SUB, FRAG_EXTEND_OF, o_THM]))

  let FRAG_SPLIT ← prove
   r"!c s t:A->bool.
        frag_support c SUBSET s UNION t
        ==> ?d e. frag_support d SUBSET s /\ frag_support e SUBSET t /\
                  frag_add d e = c"
   (REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [← q r"frag_extend (\f. if f IN s then frag_of f else frag_0) c:A frag",
      ← q r"frag_extend (\f. if f IN s then frag_0 else frag_of f) c:A frag"] THEN
    REWRITE_TAC [CONJ_ASSOC] THEN CONJ_TAC THENL
     [CONJ_TAC THEN
      W (MP_TAC o PART_MATCH lhand FRAG_SUPPORT_FRAG_EXTEND o lhand o snd) THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] SUBSET_TRANS) THEN
      REWRITE_TAC [UNIONS_SUBSET, FORALL_IN_GSPEC] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC [FRAG_SUPPORT_0, EMPTY_SUBSET, FRAG_SUPPORT_OF] THEN
      ASM SET_TAC [],
      POP_ASSUM MP_TAC THEN SPEC_TAC (← q "c:A frag", ← q "c:A frag") THEN
      MATCH_MP_TAC FRAG_INDUCTION THEN
      REWRITE_TAC [FRAG_EXTEND_0, FRAG_EXTEND_SUB, FRAG_EXTEND_OF] THEN
      CONJ_TAC THENL [CONV_TAC FRAG_MODULE, ALL_TAC] THEN
      CONJ_TAC THENL [ALL_TAC, CONV_TAC FRAG_MODULE] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
      CONV_TAC FRAG_MODULE])

  -- @@RETURN BEGIN
  return { frag_tybij, frag_support, frag_0, frag_of, frag_neg, frag_cmul, frag_add,
           frag_sub, FRAG_EQ, DEST_FRAG_0, DEST_FRAG_OF, DEST_FRAG_NEG, DEST_FRAG_CMUL,
           DEST_FRAG_ADD, DEST_FRAG_SUB, FRAG_OF_NONZERO, FRAG_MODULE,
           FINITE_FRAG_SUPPORT, FRAG_SUPPORT_0, FRAG_SUPPORT_OF, FRAG_SUPPORT_NEG,
           FRAG_SUPPORT_CMUL, FRAG_SUPPORT_ADD, FRAG_SUPPORT_SUB, FRAG_SUPPORT_EQ_EMPTY,
           FRAG_OF_EQ, FRAG_ADD_EQ_0, NEUTRAL_FRAG_ADD, MONOIDAL_FRAG_ADD, FRAG_CMUL_SUM,
           FRAG_SUPPORT_SUM, frag_extend, FRAG_EXTEND, FRAG_EXTEND_0, FRAG_EXTEND_OF,
           FRAG_EXTEND_CMUL, FRAG_EXTEND_NEG, FRAG_EXTEND_ADD, FRAG_EXTEND_SUB,
           FRAG_EXTEND_SUM, FRAG_EXTEND_EQ, FRAG_EXTEND_EQ_0, FRAG_SUPPORT_FRAG_EXTEND,
           FRAG_EXPANSION, FRAG_CLOSURE_SUB_CMUL, FRAG_INDUCTION, FRAG_EXTEND_COMPOSE,
           FRAG_SPLIT }
  -- @@RETURN END

end HolLibrary.Frag
