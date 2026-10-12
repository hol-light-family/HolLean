/- ========================================================================= -/
/- Define integer sums, with most theorems derived automatically.            -/
/- ========================================================================= -/
/- File: HolLibrary/Isum.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/isum.ml`, by hand, in file order, in
  the style of HolLibrary/Products.lean and HolLibrary/Card.lean (see there
  and HolMath/Base.lean for the conventions).  isum.ml has no `needs`: it
  runs on the core library.

  THE ORGANISING IDEA.  isum.ml defines its OWN rule `INT_OF_REAL_THM`
  (isum.ml 30-69), which SHADOWS core int.ml's `INT_OF_REAL_THM`.  It is a
  stronger version that also handles `isum`, beta/eta and composition
  (`int_isum`, `GSYM BETA_THM`, `GSYM ETA_AX`, `compose_th`), rewrites with
  `REDEPTH_CONV` rather than `DEPTH_CONV`, and lifts function-valued (not
  only real-valued) universally quantified variables.  Just over seventy of
  the file's bindings are then MECHANICAL LIFTS of real theorems that
  iterate.ml already proved, performed by this rule
  (`let ISUM_X = INT_OF_REAL_THM SUM_X`).  The rule's local proofs
  (`cond_th`, `compose_th`) are proved once at setup time; so are
  `EXPAND_ISUM_CONV`'s `pth_0`/`pth_1`/`pth_2`.

  This rule is exported under its HOL Light name `INT_OF_REAL_THM`, which is
  the same name core int.ml uses for its (weaker) rule; users qualify the
  clash (`SessionLibrary.Isum.INT_OF_REAL_THM`).  The idioms for term
  manipulation come from HolMath/Int.lean's translation of int.ml's
  `setupIntOfRealThm` and from HolMath/Iterate.lean's `EXPAND_NSUM_CONV`.

  The file ends with `extend_basic_congs` adding three `isum` congruences.

  EVALUATION ORDER.  OCaml evaluates function arguments right to left; none
  of the proofs here binds two printing/counter rules, so each stays inline.
-/

import HolMath

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

set_option maxRecDepth 8000

namespace HolLibrary.Isum

/- ------------------------------------------------------------------------- -/
/- What isum.ml uses from the core library (supplied by Session).            -/
/- ------------------------------------------------------------------------- -/

/-- Theorems isum.ml uses from the core library (part 1 of 3). -/
structure CoreThms1 where
  (BETA_THM CARD_EQ_SUM ETA_AX FINITE_INDUCT_STRONG FORALL_PAIR_THM IMP_CONJ
   IN_ELIM_THM IN_NUMSEG ITERATE_CLAUSES ITERATE_CLOSED ITERATE_CLOSED_NONEMPTY
   ITERATE_EXPAND_CASES ITERATE_ITERATE_PRODUCT ITERATE_RELATED
   ITERATE_RELATED_NONEMPTY ITERATE_SUPPORT ITERATE_UNIV MONOIDAL_INT_ADD
   MONOIDAL_REAL_ADD NEUTRAL_INT_ADD NEUTRAL_REAL_ADD REAL_OF_NUM_SUM
   REAL_OF_NUM_SUM_NUMSEG REAL_SUB_POW REAL_SUB_POW_L1 REAL_SUB_POW_R1
   RIGHT_FORALL_IMP_THM SUM_0 SUM_ABS SUM_ABS_BOUND SUM_ABS_LE SUM_ABS_NUMSEG
   SUM_ADD SUM_ADD_NUMSEG SUM_ADD_SPLIT SUM_BIJECTION SUM_BOUND SUM_BOUND_LT
   SUM_BOUND_LT_ALL SUM_CASES SUM_CLAUSES_LEFT SUM_CLAUSES_NUMSEG : thm)
  deriving Inhabited

/-- Theorems isum.ml uses from the core library (part 2 of 3). -/
structure CoreThms2 where
  (SUM_CLAUSES_RIGHT SUM_COMBINE_L SUM_COMBINE_R SUM_CONST SUM_CONST_NUMSEG
   SUM_DELETE SUM_DELETE_CASES SUM_DELTA SUM_DIFF SUM_DIFFS SUM_EQ SUM_EQ_0
   SUM_EQ_0_NUMSEG SUM_EQ_GENERAL SUM_EQ_GENERAL_INVERSES SUM_EQ_NUMSEG
   SUM_EQ_SUPERSET SUM_GROUP SUM_IMAGE SUM_IMAGE_GEN SUM_IMAGE_LE
   SUM_IMAGE_NONZERO SUM_INCL_EXCL SUM_INJECTION SUM_LE SUM_LE_INCLUDED
   SUM_LE_NUMSEG SUM_LMUL SUM_LT SUM_LT_ALL SUM_MULTICOUNT SUM_MULTICOUNT_GEN
   SUM_NEG SUM_OFFSET SUM_OFFSET_0 SUM_PARTIAL_PRE SUM_PARTIAL_SUC
   SUM_POS_BOUND SUM_POS_EQ_0 SUM_POS_EQ_0_NUMSEG SUM_POS_LE
   SUM_POS_LE_NUMSEG : thm)
  deriving Inhabited

/-- Theorems isum.ml uses from the core library (part 3 of 3). -/
structure CoreThms3 where
  (SUM_RESTRICT SUM_RESTRICT_SET SUM_RMUL SUM_SING SUM_SING_NUMSEG SUM_SUB
   SUM_SUBSET SUM_SUBSET_SIMPLE SUM_SUB_NUMSEG SUM_SUM_RESTRICT SUM_SUPERSET
   SUM_SWAP SUM_SWAP_NUMSEG SUM_TRIV_NUMSEG SUM_UNION SUM_UNIONS_NONZERO
   SUM_UNION_EQ SUM_UNION_LZERO SUM_UNION_NONZERO SUM_UNION_RZERO
   SUM_ZERO_EXISTS admissible int_abs_th int_add_th int_eq int_ge int_gt
   int_le int_lt int_max_th int_min_th int_mul_th int_neg_th int_of_num_th
   int_pow_th int_sub_th isum o_DEF sum support : thm)
  deriving Inhabited

/-- What isum.ml uses from Session besides theorems. -/
structure IsumDeps where
  -- parser state and the simplifier's congruences
  extend_basic_congs : List thm → IO Unit
  -- decision procedures and tactics
  ARITH_RULE : term → ExceptT String IO thm
  ASM_MESON_TAC : List thm → tactic
  MESON_TAC : List thm → tactic
  -- the numeral conversions EXPAND_ISUM_CONV uses
  NUM_LT_CONV : ioconv
  NUM_LE_CONV : ioconv
  NUM_ADD_CONV : ioconv
  core1 : CoreThms1
  core2 : CoreThms2
  core3 : CoreThms3

/- ------------------------------------------------------------------------- -/
/- `let rec INT_OF_REAL_THM th = ...` (isum.ml 65-68).                       -/
/-                                                                           -/
/- The top-level recursion of isum.ml's `INT_OF_REAL_THM`: a conjunction is -/
/- lifted conjunct by conjunct.  Note isum.ml maps over `INT_OF_REAL_THM1`  -/
/- here, not the recursive `INT_OF_REAL_THM`, so the recursion is only one  -/
/- level deep.                                                              -/
/- ------------------------------------------------------------------------- -/

/-- `let rec INT_OF_REAL_THM th = if is_conj(concl th) then CONJ
    (INT_OF_REAL_THM1 (CONJUNCT1 th)) (INT_OF_REAL_THM1 (CONJUNCT2 th))
    else INT_OF_REAL_THM1 th` (isum.ml 65-68). -/
private partial def intOfRealThmRec [HolBase]
    (INT_OF_REAL_THM1 : thm → ExceptT String IO thm) (th : thm) :
    ExceptT String IO thm :=
  if is_conj (concl th) then do
    CONJ (← INT_OF_REAL_THM1 (← CONJUNCT1 th))
         (← INT_OF_REAL_THM1 (← CONJUNCT2 th))
  else INT_OF_REAL_THM1 th

/- ------------------------------------------------------------------------- -/
/- `let rec conv tm = ...` inside EXPAND_ISUM_CONV (isum.ml 227).            -/
/- Mirrors HolMath/Iterate.lean's `expandNsumConvImpl`.                      -/
/- ------------------------------------------------------------------------- -/

/-- `let rec conv tm = ...` inside EXPAND_ISUM_CONV (isum.ml 227-242). -/
partial def expandIsumConvImpl [HolBase]
    (NUM_LT_CONV NUM_LE_CONV NUM_ADD_CONV : ioconv)
    (pth_0 pth_1 pth_2 : thm) (ns_tm f_tm m_tm n_tm : term) : ioconv :=
  fun tm => ExceptT.run do
  let conv := expandIsumConvImpl NUM_LT_CONV NUM_LE_CONV NUM_ADD_CONV
    pth_0 pth_1 pth_2 ns_tm f_tm m_tm n_tm
  let (smn, ftm) ← dest_comb tm
  let (s, mn) ← dest_comb smn
  if !(is_const s && (match dest_const s with | .ok (c, _) => c == "isum" | _ => false))
  then throw "EXPAND_ISUM_CONV" else
  let (mtm, ntm) ← dest_binop ns_tm mn
  let m ← dest_numeral mtm
  let n ← dest_numeral ntm
  if n < m then
    let th1 ← INST [(ftm, f_tm), (mtm, m_tm), (ntm, n_tm)] pth_0
    MP th1 (← EQT_ELIM (← NUM_LT_CONV (← lhand (concl th1))))
  else if n == m then CONV_RULE (RAND_CONV (TRY_CONV BETA_CONV))
                                 (← INST [(ftm, f_tm), (mtm, m_tm)] pth_1)
  else
    let th1 ← INST [(ftm, f_tm), (mtm, m_tm), (ntm, n_tm)] pth_2
    let th2 ← MP th1 (← EQT_ELIM (← NUM_LE_CONV (← lhand (concl th1))))
    CONV_RULE (RAND_CONV (COMB2_CONV (RAND_CONV (TRY_CONV BETA_CONV))
     (LAND_CONV (LAND_CONV NUM_ADD_CONV) THENC conv))) th2

/- ------------------------------------------------------------------------- -/
/- The whole file is one bundle.  (isum.ml 1-287.)                           -/
/- ------------------------------------------------------------------------- -/

structure Isum where
  -- @@FIELDS
  ISUM_SUPPORT : thm
  int_isum : thm
  INT_OF_REAL_THM : (thm → IO (Except String thm))
  CARD_EQ_ISUM : thm
  INT_SUB_POW : thm
  ISUM_0 : thm
  ISUM_ABS : thm
  ISUM_ABS_BOUND : thm
  ISUM_ABS_LE : thm
  ISUM_ABS_NUMSEG : thm
  ISUM_ADD : thm
  ISUM_ADD_NUMSEG : thm
  ISUM_ADD_SPLIT : thm
  ISUM_BIJECTION : thm
  ISUM_BOUND : thm
  ISUM_BOUND_LT : thm
  ISUM_BOUND_LT_ALL : thm
  ISUM_CASES : thm
  ISUM_CLAUSES_LEFT : thm
  ISUM_CLAUSES_NUMSEG : thm
  ISUM_CLAUSES_RIGHT : thm
  ISUM_COMBINE_L : thm
  ISUM_COMBINE_R : thm
  ISUM_CONST : thm
  ISUM_CONST_NUMSEG : thm
  ISUM_DELETE : thm
  ISUM_DELETE_CASES : thm
  ISUM_DELTA : thm
  ISUM_DIFF : thm
  ISUM_DIFFS : thm
  ISUM_EQ : thm
  ISUM_EQ_0 : thm
  ISUM_EQ_0_NUMSEG : thm
  ISUM_EQ_GENERAL : thm
  ISUM_EQ_GENERAL_INVERSES : thm
  ISUM_EQ_NUMSEG : thm
  ISUM_EQ_SUPERSET : thm
  ISUM_GROUP : thm
  ISUM_IMAGE : thm
  ISUM_IMAGE_GEN : thm
  ISUM_IMAGE_LE : thm
  ISUM_IMAGE_NONZERO : thm
  ISUM_INCL_EXCL : thm
  ISUM_INJECTION : thm
  ISUM_LE : thm
  ISUM_LE_INCLUDED : thm
  ISUM_LE_NUMSEG : thm
  ISUM_LMUL : thm
  ISUM_LT : thm
  ISUM_LT_ALL : thm
  ISUM_MULTICOUNT : thm
  ISUM_MULTICOUNT_GEN : thm
  ISUM_NEG : thm
  ISUM_OFFSET : thm
  ISUM_OFFSET_0 : thm
  ISUM_PARTIAL_PRE : thm
  ISUM_PARTIAL_SUC : thm
  ISUM_POS_BOUND : thm
  ISUM_POS_EQ_0 : thm
  ISUM_POS_EQ_0_NUMSEG : thm
  ISUM_POS_LE : thm
  ISUM_POS_LE_NUMSEG : thm
  ISUM_RESTRICT : thm
  ISUM_RESTRICT_SET : thm
  ISUM_RMUL : thm
  ISUM_SING : thm
  ISUM_SING_NUMSEG : thm
  ISUM_SUB : thm
  ISUM_SUBSET : thm
  ISUM_SUBSET_SIMPLE : thm
  ISUM_SUB_NUMSEG : thm
  ISUM_ISUM_RESTRICT : thm
  ISUM_SUPERSET : thm
  ISUM_SWAP : thm
  ISUM_SWAP_NUMSEG : thm
  ISUM_TRIV_NUMSEG : thm
  ISUM_UNION : thm
  ISUM_UNIONS_NONZERO : thm
  ISUM_UNION_EQ : thm
  ISUM_UNION_LZERO : thm
  ISUM_UNION_NONZERO : thm
  ISUM_UNION_RZERO : thm
  ISUM_ZERO_EXISTS : thm
  REAL_OF_NUM_ISUM : thm
  REAL_OF_NUM_ISUM_NUMSEG : thm
  ISUM_ISUM_PRODUCT : thm
  ADMISSIBLE_ISUM : thm
  INT_SUB_POW_L1 : thm
  INT_SUB_POW_R1 : thm
  ISUM_UNIV : thm
  ISUM_CLOSED : thm
  ISUM_RELATED : thm
  ISUM_CLOSED_NONEMPTY : thm
  ISUM_RELATED_NONEMPTY : thm
  EXPAND_ISUM_CONV : ioconv
  deriving Inhabited

@[nospecialize]
def setupIsum [HolBase] (D : IsumDeps) :
    ExceptT String IO Isum := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, NUM_ADD_CONV, NUM_LE_CONV, NUM_LT_CONV, .. } := D
  let { BETA_THM, CARD_EQ_SUM, ETA_AX, FINITE_INDUCT_STRONG, FORALL_PAIR_THM, IMP_CONJ,
        IN_ELIM_THM, IN_NUMSEG, ITERATE_CLAUSES, ITERATE_CLOSED,
        ITERATE_CLOSED_NONEMPTY, ITERATE_EXPAND_CASES, ITERATE_ITERATE_PRODUCT,
        ITERATE_RELATED, ITERATE_RELATED_NONEMPTY, ITERATE_SUPPORT, ITERATE_UNIV,
        MONOIDAL_INT_ADD, MONOIDAL_REAL_ADD, NEUTRAL_INT_ADD, NEUTRAL_REAL_ADD,
        REAL_OF_NUM_SUM, REAL_OF_NUM_SUM_NUMSEG, REAL_SUB_POW, REAL_SUB_POW_L1,
        REAL_SUB_POW_R1, RIGHT_FORALL_IMP_THM, SUM_0, SUM_ABS, SUM_ABS_BOUND,
        SUM_ABS_LE, SUM_ABS_NUMSEG, SUM_ADD, SUM_ADD_NUMSEG, SUM_ADD_SPLIT,
        SUM_BIJECTION, SUM_BOUND, SUM_BOUND_LT, SUM_BOUND_LT_ALL, SUM_CASES,
        SUM_CLAUSES_LEFT, SUM_CLAUSES_NUMSEG, .. } := D.core1
  let { SUM_CLAUSES_RIGHT, SUM_COMBINE_L, SUM_COMBINE_R, SUM_CONST, SUM_CONST_NUMSEG,
        SUM_DELETE, SUM_DELETE_CASES, SUM_DELTA, SUM_DIFF, SUM_DIFFS, SUM_EQ, SUM_EQ_0,
        SUM_EQ_0_NUMSEG, SUM_EQ_GENERAL, SUM_EQ_GENERAL_INVERSES, SUM_EQ_NUMSEG,
        SUM_EQ_SUPERSET, SUM_GROUP, SUM_IMAGE, SUM_IMAGE_GEN, SUM_IMAGE_LE,
        SUM_IMAGE_NONZERO, SUM_INCL_EXCL, SUM_INJECTION, SUM_LE, SUM_LE_INCLUDED,
        SUM_LE_NUMSEG, SUM_LMUL, SUM_LT, SUM_LT_ALL, SUM_MULTICOUNT,
        SUM_MULTICOUNT_GEN, SUM_NEG, SUM_OFFSET, SUM_OFFSET_0, SUM_PARTIAL_PRE,
        SUM_PARTIAL_SUC, SUM_POS_BOUND, SUM_POS_EQ_0, SUM_POS_EQ_0_NUMSEG, SUM_POS_LE,
        SUM_POS_LE_NUMSEG, .. } := D.core2
  let { SUM_RESTRICT, SUM_RESTRICT_SET, SUM_RMUL, SUM_SING, SUM_SING_NUMSEG, SUM_SUB,
        SUM_SUBSET, SUM_SUBSET_SIMPLE, SUM_SUB_NUMSEG, SUM_SUM_RESTRICT, SUM_SUPERSET,
        SUM_SWAP, SUM_SWAP_NUMSEG, SUM_TRIV_NUMSEG, SUM_UNION, SUM_UNIONS_NONZERO,
        SUM_UNION_EQ, SUM_UNION_LZERO, SUM_UNION_NONZERO, SUM_UNION_RZERO,
        SUM_ZERO_EXISTS, admissible, int_abs_th, int_add_th, int_eq, int_ge, int_gt,
        int_le, int_lt, int_max_th, int_min_th, int_mul_th, int_neg_th, int_of_num_th,
        int_pow_th, int_sub_th, isum, o_DEF, sum, support, .. } := D.core3
  -- @@SCOPE END

  let ISUM_SUPPORT ← prove
   r"!f s. isum (support (+) f s) f = isum s f"
   (REWRITE_TAC [isum, ITERATE_SUPPORT])

  let int_isum ← prove
   r"!f:A->int s. real_of_int(isum s f) = sum s (\x. real_of_int(f x))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [sum, isum] THEN
    ONCE_REWRITE_TAC [ITERATE_EXPAND_CASES] THEN
    SUBGOAL_THEN
     (← q r"support(+) (\x:A. real_of_int(f x)) s = support(+) f s")
    SUBST1_TAC THENL
     [REWRITE_TAC [support, NEUTRAL_REAL_ADD, NEUTRAL_INT_ADD] THEN
      REWRITE_TAC [← GSYM int_of_num_th, ← GSYM int_eq],
      ALL_TAC] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC [NEUTRAL_REAL_ADD, NEUTRAL_INT_ADD, int_of_num_th] THEN
    POP_ASSUM MP_TAC THEN SPEC_TAC (← q r"support(+) (f:A->int) s", ← q r"s:A->bool") THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [ITERATE_CLAUSES, MONOIDAL_INT_ADD, MONOIDAL_REAL_ADD] THEN
    SIMP_TAC [NEUTRAL_INT_ADD, NEUTRAL_REAL_ADD, int_of_num_th, int_add_th])

  /- --------------------------------------------------------------------- -/
  /- Generalize INT_OF_REAL_THM for most common sum patterns.  (isum.ml    -/
  /- 30-69.)  Built ONCE here, like int.ml's rule in HolMath/Int.lean.     -/
  /- --------------------------------------------------------------------- -/

  let INT_OF_REAL_THM : (thm → IO (Except String thm)) ← do
    let dest ← q r"real_of_int"
    let real_ty ← qty r"real"
    let int_ty ← qty r"int"
    let loc_cond_th ← prove
     r"real_of_int(if b then x else y) =
         if b then real_of_int x else real_of_int y"
     (COND_CASES_TAC THEN REWRITE_TAC [])
    let loc_compose_th ← prove
     r"(\x. real_of_int((f o g) x)) = (\x. real_of_int(f x)) o g"
     (REWRITE_TAC [o_DEF])
    let thlist ← [int_eq, int_le, int_lt, int_ge, int_gt,
      int_of_num_th, int_neg_th, int_add_th, int_mul_th,
      int_sub_th, int_abs_th, int_max_th, int_min_th, int_pow_th,
      int_isum, (← GSYM BETA_THM), (← GSYM ETA_AX), loc_compose_th,
      loc_cond_th].mapM GSYM
    let REW_RULE := GEN_REWRITE_RULE REDEPTH_CONV thlist
    -- `int_tm_of_real_var` (isum.ml 51-58): a function `s : t1->..->real` is
    -- mapped to `\vs. real_of_int(s' vs)` with `s' : t1->..->int`.
    -- `itlist mk_fun_ty tys int_ty`, lifting `mk_fun_ty : IO (Except ...)`.
    let mkIntFunTy (tys : List hol_type) : ExceptT String IO hol_type :=
      itlist (fun ty acc => do ExceptT.mk (mk_fun_ty ty (← acc))) tys (pure int_ty)
    let int_tm_of_real_var (v : term) : ExceptT String IO term := do
      let (s, ty) ← liftExcept (dest_var v)
      let (tys, rty) := splitlist dest_fun_ty ty
      if rty != real_ty then pure v else do
        let ity ← mkIntFunTy tys
        let vs ← tys.mapM (fun t => (ExceptT.lift (genvar t) : ExceptT String IO term))
        let app ← liftExcept (list_mk_comb (mk_var s ity) vs)
        let body ← liftExcept (mk_comb dest app)
        liftExcept (list_mk_abs vs body)
    -- `int_of_real_var` (isum.ml 59-64): the same variable retyped to `int`.
    let int_of_real_var (v : term) : ExceptT String IO term := do
      let (s, ty) ← liftExcept (dest_var v)
      let (tys, rty) := splitlist dest_fun_ty ty
      if rty != real_ty then pure v else do
        let ity ← mkIntFunTy tys
        pure (mk_var s ity)
    let INT_OF_REAL_THM1 (th : thm) : ExceptT String IO thm := do
      let newavs := subtract (frees (concl th)) (freesl (hyp th))
      let (avs, _bod) := strip_forall (concl th)
      let allavs := newavs ++ avs
      let avs' ← allavs.mapM int_tm_of_real_var
      let avs'' ← avs.mapM int_of_real_var
      GENL avs'' (← REW_RULE (← SPECL avs' (← GENL newavs th)))
    pure (fun th => (intOfRealThmRec INT_OF_REAL_THM1 th).run)

  -- A `thm → ExceptT ...` wrapper so the lifts below read like the OCaml.
  let IORT (th : thm) : ExceptT String IO thm := ExceptT.mk (INT_OF_REAL_THM th)

  /- --------------------------------------------------------------------- -/
  /- Apply it in all the cases where it works.  (isum.ml 75-154.)          -/
  /- --------------------------------------------------------------------- -/

  let CARD_EQ_ISUM ← IORT CARD_EQ_SUM
  let INT_SUB_POW ← IORT REAL_SUB_POW
  let ISUM_0 ← IORT SUM_0
  let ISUM_ABS ← IORT SUM_ABS
  let ISUM_ABS_BOUND ← IORT SUM_ABS_BOUND
  let ISUM_ABS_LE ← IORT SUM_ABS_LE
  let ISUM_ABS_NUMSEG ← IORT SUM_ABS_NUMSEG
  let ISUM_ADD ← IORT SUM_ADD
  let ISUM_ADD_NUMSEG ← IORT SUM_ADD_NUMSEG
  let ISUM_ADD_SPLIT ← IORT SUM_ADD_SPLIT
  let ISUM_BIJECTION ← IORT SUM_BIJECTION
  let ISUM_BOUND ← IORT SUM_BOUND
  let ISUM_BOUND_LT ← IORT SUM_BOUND_LT
  let ISUM_BOUND_LT_ALL ← IORT SUM_BOUND_LT_ALL
  let ISUM_CASES ← IORT SUM_CASES
  let ISUM_CLAUSES_LEFT ← IORT SUM_CLAUSES_LEFT
  let ISUM_CLAUSES_NUMSEG ← IORT SUM_CLAUSES_NUMSEG
  let ISUM_CLAUSES_RIGHT ← IORT SUM_CLAUSES_RIGHT
  let ISUM_COMBINE_L ← IORT SUM_COMBINE_L
  let ISUM_COMBINE_R ← IORT SUM_COMBINE_R
  let ISUM_CONST ← IORT SUM_CONST
  let ISUM_CONST_NUMSEG ← IORT SUM_CONST_NUMSEG
  let ISUM_DELETE ← IORT SUM_DELETE
  let ISUM_DELETE_CASES ← IORT SUM_DELETE_CASES
  let ISUM_DELTA ← IORT SUM_DELTA
  let ISUM_DIFF ← IORT SUM_DIFF
  let ISUM_DIFFS ← IORT SUM_DIFFS
  let ISUM_EQ ← IORT SUM_EQ
  let ISUM_EQ_0 ← IORT SUM_EQ_0
  let ISUM_EQ_0_NUMSEG ← IORT SUM_EQ_0_NUMSEG
  let ISUM_EQ_GENERAL ← IORT SUM_EQ_GENERAL
  let ISUM_EQ_GENERAL_INVERSES ← IORT SUM_EQ_GENERAL_INVERSES
  let ISUM_EQ_NUMSEG ← IORT SUM_EQ_NUMSEG
  let ISUM_EQ_SUPERSET ← IORT SUM_EQ_SUPERSET
  let ISUM_GROUP ← IORT SUM_GROUP
  let ISUM_IMAGE ← IORT SUM_IMAGE
  let ISUM_IMAGE_GEN ← IORT SUM_IMAGE_GEN
  let ISUM_IMAGE_LE ← IORT SUM_IMAGE_LE
  let ISUM_IMAGE_NONZERO ← IORT SUM_IMAGE_NONZERO
  let ISUM_INCL_EXCL ← IORT SUM_INCL_EXCL
  let ISUM_INJECTION ← IORT SUM_INJECTION
  let ISUM_LE ← IORT SUM_LE
  let ISUM_LE_INCLUDED ← IORT SUM_LE_INCLUDED
  let ISUM_LE_NUMSEG ← IORT SUM_LE_NUMSEG
  let ISUM_LMUL ← IORT SUM_LMUL
  let ISUM_LT ← IORT SUM_LT
  let ISUM_LT_ALL ← IORT SUM_LT_ALL
  let ISUM_MULTICOUNT ← IORT SUM_MULTICOUNT
  let ISUM_MULTICOUNT_GEN ← IORT SUM_MULTICOUNT_GEN
  let ISUM_NEG ← IORT SUM_NEG
  let ISUM_OFFSET ← IORT SUM_OFFSET
  let ISUM_OFFSET_0 ← IORT SUM_OFFSET_0
  let ISUM_PARTIAL_PRE ← IORT SUM_PARTIAL_PRE
  let ISUM_PARTIAL_SUC ← IORT SUM_PARTIAL_SUC
  let ISUM_POS_BOUND ← IORT SUM_POS_BOUND
  let ISUM_POS_EQ_0 ← IORT SUM_POS_EQ_0
  let ISUM_POS_EQ_0_NUMSEG ← IORT SUM_POS_EQ_0_NUMSEG
  let ISUM_POS_LE ← IORT SUM_POS_LE
  let ISUM_POS_LE_NUMSEG ← IORT SUM_POS_LE_NUMSEG
  let ISUM_RESTRICT ← IORT SUM_RESTRICT
  let ISUM_RESTRICT_SET ← IORT SUM_RESTRICT_SET
  let ISUM_RMUL ← IORT SUM_RMUL
  let ISUM_SING ← IORT SUM_SING
  let ISUM_SING_NUMSEG ← IORT SUM_SING_NUMSEG
  let ISUM_SUB ← IORT SUM_SUB
  let ISUM_SUBSET ← IORT SUM_SUBSET
  let ISUM_SUBSET_SIMPLE ← IORT SUM_SUBSET_SIMPLE
  let ISUM_SUB_NUMSEG ← IORT SUM_SUB_NUMSEG
  let ISUM_ISUM_RESTRICT ← IORT SUM_SUM_RESTRICT
  let ISUM_SUPERSET ← IORT SUM_SUPERSET
  let ISUM_SWAP ← IORT SUM_SWAP
  let ISUM_SWAP_NUMSEG ← IORT SUM_SWAP_NUMSEG
  let ISUM_TRIV_NUMSEG ← IORT SUM_TRIV_NUMSEG
  let ISUM_UNION ← IORT SUM_UNION
  let ISUM_UNIONS_NONZERO ← IORT SUM_UNIONS_NONZERO
  let ISUM_UNION_EQ ← IORT SUM_UNION_EQ
  let ISUM_UNION_LZERO ← IORT SUM_UNION_LZERO
  let ISUM_UNION_NONZERO ← IORT SUM_UNION_NONZERO
  let ISUM_UNION_RZERO ← IORT SUM_UNION_RZERO
  let ISUM_ZERO_EXISTS ← IORT SUM_ZERO_EXISTS
  let REAL_OF_NUM_ISUM ← IORT REAL_OF_NUM_SUM
  let REAL_OF_NUM_ISUM_NUMSEG ← IORT REAL_OF_NUM_SUM_NUMSEG

  /- --------------------------------------------------------------------- -/
  /- Manually derive the few cases where it doesn't.  (isum.ml 166-235.)   -/
  /- --------------------------------------------------------------------- -/

  let ISUM_ISUM_PRODUCT ← prove
   r"!s:A->bool t:A->B->bool x.
        FINITE s /\ (!i. i IN s ==> FINITE(t i))
        ==> isum s (\i. isum (t i) (x i)) =
            isum {i,j | i IN s /\ j IN t i} (\(i,j). x i j)"
   (REWRITE_TAC [isum] THEN MATCH_MP_TAC ITERATE_ITERATE_PRODUCT THEN
    REWRITE_TAC [MONOIDAL_INT_ADD])

  let ADMISSIBLE_ISUM ← prove
   r"!(<<) p:(B->C)->P->bool s:P->A h a b.
        admissible(<<) (\f (k,x). a(x) <= k /\ k <= b(x) /\ p f x)
                       (\(k,x). s x) (\f (k,x). h f x k)
   ==> admissible(<<) p s (\f x. isum(a(x)..b(x)) (h f x))"
   (REWRITE_TAC [admissible, FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ISUM_EQ_NUMSEG THEN ASM_MESON_TAC [])

  let INT_SUB_POW_L1 ← prove
   r"!x n. 1 <= n ==> &1 - x pow n = (&1 - x) * isum (0..n - 1) (\i. x pow i)"
   (SIMP_TAC [(← IORT REAL_SUB_POW_L1), ETA_AX])

  let INT_SUB_POW_R1 ← prove
   r"!x n. 1 <= n ==> x pow n - &1 = (x - &1) * isum (0..n - 1) (\i. x pow i)"
   (SIMP_TAC [(← IORT REAL_SUB_POW_R1), ETA_AX])

  let ISUM_UNIV ← prove
   r"!f:A->int s. support (+) f (:A) SUBSET s ==> isum s f = isum (:A) f"
   (REWRITE_TAC [isum] THEN MATCH_MP_TAC ITERATE_UNIV THEN
    REWRITE_TAC [MONOIDAL_INT_ADD])

  let ISUM_CLOSED ← prove
   r"!P f:A->int s.
        P(&0) /\ (!x y. P x /\ P y ==> P(x + y)) /\ (!a. a IN s ==> P(f a))
        ==> P(isum s f)"
   (REPEAT STRIP_TAC THEN MP_TAC (← MATCH_MP ITERATE_CLOSED MONOIDAL_INT_ADD) THEN
    DISCH_THEN (MP_TAC o SPEC (← q "P:int->bool")) THEN
    ASM_SIMP_TAC [NEUTRAL_INT_ADD, ← GSYM isum])

  let ISUM_RELATED ← prove
   r"!R (f:A->int) g s.
        R (&0) (&0) /\
        (!m n m' n'. R m n /\ R m' n' ==> R (m + m') (n + n')) /\
        FINITE s /\ (!x. x IN s ==> R (f x) (g x))
        ==> R (isum s f) (isum s g)"
   (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    GEN_TAC THEN REPEAT DISCH_TAC THEN
    MP_TAC (← ISPEC (← q "R:int->int->bool")
      (← MATCH_MP ITERATE_RELATED MONOIDAL_INT_ADD)) THEN
    ASM_REWRITE_TAC [← GSYM isum, NEUTRAL_INT_ADD] THEN ASM_MESON_TAC [])

  let ISUM_CLOSED_NONEMPTY ← prove
   r"!P f:A->int s.
        FINITE s /\ ~(s = {}) /\
        (!x y. P x /\ P y ==> P(x + y)) /\ (!a. a IN s ==> P(f a))
        ==> P(isum s f)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← MATCH_MP ITERATE_CLOSED_NONEMPTY MONOIDAL_INT_ADD) THEN
    DISCH_THEN (MP_TAC o SPEC (← q "P:int->bool")) THEN
    ASM_SIMP_TAC [NEUTRAL_INT_ADD, ← GSYM isum])

  let ISUM_RELATED_NONEMPTY ← prove
   r"!R (f:A->int) g s.
        (!m n m' n'. R m n /\ R m' n' ==> R (m + m') (n + n')) /\
        FINITE s /\ ~(s = {}) /\ (!x. x IN s ==> R (f x) (g x))
        ==> R (isum s f) (isum s g)"
   (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    GEN_TAC THEN REPEAT DISCH_TAC THEN
    MP_TAC (← ISPEC (← q "R:int->int->bool")
      (← MATCH_MP ITERATE_RELATED_NONEMPTY MONOIDAL_INT_ADD)) THEN
    ASM_REWRITE_TAC [← GSYM isum, NEUTRAL_INT_ADD] THEN ASM_MESON_TAC [])

  /- --------------------------------------------------------------------- -/
  /- Expand "isum (m..n) f" where m and n are numerals.  (isum.ml 241-266.)-/
  /- `pth_0`/`pth_1`/`pth_2` are proved once here.                         -/
  /- --------------------------------------------------------------------- -/

  let EXPAND_ISUM_CONV : ioconv ← do
    let loc_pths := CONJUNCTS (← prove
     r"(n < m ==> isum(m..n) f = &0) /\
       isum(m..m) f = f m /\
       (m <= n ==> isum (m..n) f = f m + isum (m + 1..n) f)"
      (REWRITE_TAC [ISUM_CLAUSES_LEFT, ISUM_SING_NUMSEG, ISUM_TRIV_NUMSEG]))
    let (pth_0, pth_1, pth_2) ← match loc_pths with
      | [a, b, c] => pure (a, b, c)
      | _ => throw "EXPAND_ISUM_CONV"
    let ns_tm ← q r".."
    let f_tm ← q r"f:num->int"
    let m_tm ← q r"m:num"
    let n_tm ← q r"n:num"
    pure (expandIsumConvImpl NUM_LT_CONV NUM_LE_CONV NUM_ADD_CONV
      pth_0 pth_1 pth_2 ns_tm f_tm m_tm n_tm)

  /- --------------------------------------------------------------------- -/
  /- Extend the congruences.  (isum.ml 272-287.)                           -/
  /- `let th = prove (...) in extend_basic_congs (map SPEC_ALL ...)`.      -/
  /- --------------------------------------------------------------------- -/

  do
    let th ← prove
     r"(!f g s.   (!x. x IN s ==> f(x) = g(x))
                  ==> isum s (\i. f(i)) = isum s g) /\
       (!f g a b. (!i. a <= i /\ i <= b ==> f(i) = g(i))
                  ==> isum(a..b) (\i. f(i)) = isum(a..b) g) /\
       (!f g p.   (!x. p x ==> f x = g x)
                  ==> isum {y | p y} (\i. f(i)) = isum {y | p y} g)"
     (REPEAT STRIP_TAC THEN MATCH_MP_TAC ISUM_EQ THEN
      ASM_SIMP_TAC [IN_ELIM_THM, IN_NUMSEG])
    D.extend_basic_congs (← (CONJUNCTS th).mapM SPEC_ALL)

  -- @@RETURN BEGIN
  return { ISUM_SUPPORT, int_isum, INT_OF_REAL_THM, CARD_EQ_ISUM, INT_SUB_POW, ISUM_0,
           ISUM_ABS, ISUM_ABS_BOUND, ISUM_ABS_LE, ISUM_ABS_NUMSEG, ISUM_ADD,
           ISUM_ADD_NUMSEG, ISUM_ADD_SPLIT, ISUM_BIJECTION, ISUM_BOUND, ISUM_BOUND_LT,
           ISUM_BOUND_LT_ALL, ISUM_CASES, ISUM_CLAUSES_LEFT, ISUM_CLAUSES_NUMSEG,
           ISUM_CLAUSES_RIGHT, ISUM_COMBINE_L, ISUM_COMBINE_R, ISUM_CONST,
           ISUM_CONST_NUMSEG, ISUM_DELETE, ISUM_DELETE_CASES, ISUM_DELTA, ISUM_DIFF,
           ISUM_DIFFS, ISUM_EQ, ISUM_EQ_0, ISUM_EQ_0_NUMSEG, ISUM_EQ_GENERAL,
           ISUM_EQ_GENERAL_INVERSES, ISUM_EQ_NUMSEG, ISUM_EQ_SUPERSET, ISUM_GROUP,
           ISUM_IMAGE, ISUM_IMAGE_GEN, ISUM_IMAGE_LE, ISUM_IMAGE_NONZERO, ISUM_INCL_EXCL,
           ISUM_INJECTION, ISUM_LE, ISUM_LE_INCLUDED, ISUM_LE_NUMSEG, ISUM_LMUL, ISUM_LT,
           ISUM_LT_ALL, ISUM_MULTICOUNT, ISUM_MULTICOUNT_GEN, ISUM_NEG, ISUM_OFFSET,
           ISUM_OFFSET_0, ISUM_PARTIAL_PRE, ISUM_PARTIAL_SUC, ISUM_POS_BOUND,
           ISUM_POS_EQ_0, ISUM_POS_EQ_0_NUMSEG, ISUM_POS_LE, ISUM_POS_LE_NUMSEG,
           ISUM_RESTRICT, ISUM_RESTRICT_SET, ISUM_RMUL, ISUM_SING, ISUM_SING_NUMSEG,
           ISUM_SUB, ISUM_SUBSET, ISUM_SUBSET_SIMPLE, ISUM_SUB_NUMSEG,
           ISUM_ISUM_RESTRICT, ISUM_SUPERSET, ISUM_SWAP, ISUM_SWAP_NUMSEG,
           ISUM_TRIV_NUMSEG, ISUM_UNION, ISUM_UNIONS_NONZERO, ISUM_UNION_EQ,
           ISUM_UNION_LZERO, ISUM_UNION_NONZERO, ISUM_UNION_RZERO, ISUM_ZERO_EXISTS,
           REAL_OF_NUM_ISUM, REAL_OF_NUM_ISUM_NUMSEG, ISUM_ISUM_PRODUCT, ADMISSIBLE_ISUM,
           INT_SUB_POW_L1, INT_SUB_POW_R1, ISUM_UNIV, ISUM_CLOSED, ISUM_RELATED,
           ISUM_CLOSED_NONEMPTY, ISUM_RELATED_NONEMPTY, EXPAND_ISUM_CONV }
  -- @@RETURN END

end HolLibrary.Isum
