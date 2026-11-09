/- ========================================================================= -/
/- Szemeredi's theorem and related results of Ramsey theory: Hales-Jewett,   -/
/- Folkman, Graham-Rothschild (for lines), density Hales-Jewett, van der     -/
/- Waerden, Roth and Szemeredi, multidimensional Szemeredi, Gallai-Witt and  -/
/- the corners theorem.                                                      -/
/- ========================================================================= -/
/- File: HolLibrary/Szemeredi.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/szemeredi.ml` (078839e), by hand, in
  file order, in the style of HolLibrary/Galois.lean (see there and
  HolMath/Base.lean for the conventions).  szemeredi.ml begins with `needs`
  of prime.ml, products.ml and 100/bertrand.ml (HolLibrary.Bertrand), then
  `prioritize_real()` (run at the start of the first bundle); the theorems it
  uses from them and from the core library are supplied via the CoreThms
  structures (SessionLibrary.Szemeredi fills them).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, REAL_ARITH, TAUT, SET_RULE, ...) they are
  bound first, in OCaml's order.
-/

import HolLibrary.Bertrand

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolLibrary.Szemeredi

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD1 ADD_ASSOC ADD_CLAUSES ADD_EQ_0 ADD_SUB ADD_SUB2 ADD_SYM ARITH ARITH_EQ
   BERTRAND CARD_CLAUSES CARD_DELETE CARD_DIFF CARD_EQ_0 CARD_EQ_SUM
   CARD_IMAGE_INJ CARD_LE_INJ CARD_NUMSEG CARD_NUMSEG_1 CARD_NUMSEG_LT
   CARD_SUBSET CARD_SUBSET_EQ CARD_UNION_EQ CARD_UNION_LE COND_ID CONG CONG_LMOD
   CONG_MULT_RCANCEL_IFF CONJ_ASSOC CONTRAPOS_THM CROSS DE_MORGAN_THM
   DIVIDES_NSUM DIVIDES_RMUL DIVMOD_UNIQ DIV_LT DIV_MULT_ADD EMPTY_GSPEC
   EQ_ADD_RCANCEL EQ_IMP EQ_IMP_LE EQ_MULT_LCANCEL EQ_TRANS ETA_AX
   EXISTS_PAIR_THM EXP_1 EXP_ADD EXP_EQ_0 EXP_MONO_LE EXTENSION FINITE_CROSS
   FINITE_DELETE FINITE_EMPTY FINITE_HAS_SIZE FINITE_IMAGE FINITE_NUMSEG
   FINITE_NUMSEG_LE FINITE_NUMSEG_LT FINITE_PRODUCT FINITE_RESTRICT FINITE_SING
   FINITE_SUBSET FINITE_UNION FORALL_IN_IMAGE FORALL_PAIR_THM FORALL_UNWIND_THM2
   FST FUN_EQ_THM HAS_SIZE HAS_SIZE_0 HAS_SIZE_CARD HAS_SIZE_FUNSPACE
   HAS_SIZE_NUMSEG_LT INTER_SUBSET INT_ADD_RID INT_CONG_IMP_EQ INT_MUL_LZERO
   INT_OF_NUM_ADD INT_OF_NUM_EQ INT_OF_NUM_LT INT_OF_NUM_MUL INT_OF_NUM_SUB
   INT_POS INT_SUB_REFL IN_CROSS IN_DELETE IN_DIFF IN_ELIM_PAIR_THM IN_ELIM_THM
   IN_IMAGE IN_INTER IN_NUMSEG IN_SING IN_UNION LEFT_IMP_EXISTS_THM LET_TRANS
   LE_0 LE_ANTISYM LE_EXP LE_LT LE_MULT2 LE_MULT_LCANCEL LE_MULT_RCANCEL LE_REFL
   LE_TRANS LT LTE_TRANS LT_ADD_LCANCEL LT_IMP_LE LT_MULT LT_NZ LT_REFL LT_TRANS
   MEMBER_NOT_EMPTY MINIMAL MINIMAL_UNIQUE MOD_LT MOD_LT_EQ MOD_MOD_REFL
   MOD_MULT_ADD MONO_EXISTS MULT_CLAUSES MULT_EQ_0 MULT_SYM NOT_EXISTS_THM
   NOT_FORALL_THM NOT_IMP NOT_IN_EMPTY : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (NOT_LE NOT_LT NOT_SUC NSUM_ADD NSUM_CLAUSES_NUMSEG NSUM_CLAUSES_NUMSEG_LT
   NSUM_CONST NSUM_DIGITS_BOUND NSUM_DIGITS_UNIQUE NSUM_EQ NSUM_RESTRICT_SET
   NSUM_SING NSUM_UNION_NONZERO PAIR PAIR_EQ PRIME_0 PRIME_COPRIME_LT
   PRODUCT_CONST PRODUCT_EQ PRODUCT_EQ_0 PRODUCT_EQ_1 PRODUCT_LE PRODUCT_MUL
   PRODUCT_POS_LE REAL_ABS_DIV REAL_ABS_NUM REAL_ADD_LID REAL_ADD_RDISTRIB
   REAL_ADD_RID REAL_ARCH REAL_ARCH_POW_INV REAL_ARCH_SIMPLE REAL_DIV_RMUL
   REAL_EQ_IMP_LE REAL_INV_0 REAL_INV_MUL REAL_LE_ADD2 REAL_LE_ANTISYM
   REAL_LE_DIV REAL_LE_INV2 REAL_LE_INV_EQ REAL_LE_LADD REAL_LE_LDIV_EQ
   REAL_LE_LMUL REAL_LE_LMUL_EQ REAL_LE_MUL REAL_LE_RDIV_EQ REAL_LE_REFL
   REAL_LE_RMUL REAL_LE_TRANS REAL_LT_DIV REAL_LT_IMP_LE REAL_LT_IMP_NZ
   REAL_LT_INV_EQ REAL_LT_LDIV_EQ REAL_LT_MUL REAL_LT_REFL REAL_LT_RMUL
   REAL_MUL_AC REAL_MUL_ASSOC REAL_MUL_LID REAL_MUL_LINV REAL_MUL_LZERO
   REAL_MUL_RID REAL_MUL_RZERO REAL_MUL_SYM REAL_NOT_LE REAL_NOT_LT
   REAL_OF_NUM_ADD REAL_OF_NUM_EQ REAL_OF_NUM_LE REAL_OF_NUM_LT REAL_OF_NUM_MUL
   REAL_OF_NUM_POW REAL_OF_NUM_SUB REAL_OF_NUM_SUC REAL_POS REAL_POW_2
   REAL_POW_ADD REAL_POW_DIV REAL_POW_LE REAL_POW_LE2 REAL_POW_LT
   REAL_POW_MONO_INV REAL_POW_MUL REAL_POW_ONE RIGHT_ADD_DISTRIB
   RIGHT_IMP_EXISTS_THM SELECT_UNIQUE SKOLEM_THM SND SUBSET SUBSET_TRANS SUB_0
   SUB_ADD SUB_REFL SUC_SUB1 SUM_0 SUM_ABS SUM_ADD SUM_BOUND SUM_CASES
   SUM_CLAUSES SUM_CONST SUM_DELETE SUM_DELTA SUM_EQ SUM_EQ_0
   SUM_EQ_GENERAL_INVERSES SUM_GROUP SUM_IMAGE SUM_INJECTION SUM_LE SUM_LMUL
   SUM_LT_ALL SUM_POS_LE SUM_RESTRICT_SET SUM_RMUL SUM_SUB SUM_SUM_PRODUCT
   SUM_SWAP divides num_FINITE num_RECURSION num_congruent o_DEF real_div : thm)
  deriving Inhabited

/-- What szemeredi.ml uses from Session besides theorems. -/
structure SzemerediDeps where
  new_definition : String → ExceptT String IO thm
  prioritize_real : IO Unit  -- prioritize_real ()
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_ARITH_TAC : tactic
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  ASM_MESON_TAC : List thm → tactic
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  TAUT : term → ExceptT String IO thm
  INDUCT_TAC : tactic
  REAL_ARITH : term → ExceptT String IO thm  -- calc_rat.ml's final REAL_ARITH
  REAL_ARITH_TAC : tactic
  ASM_REAL_ARITH_TAC : tactic
  REAL_FIELD : term → ExceptT String IO thm
  REAL_RING : term → ExceptT String IO thm
  NUM_RING : ioconv  -- grobner.ml's NUM_RING
  INT_ARITH_TAC : tactic
  MOD_DOWN_CONV : ioconv
  NUMBER_RULE : ioconv  -- ints.ml's NUMBER_RULE
  INTEGER_RULE : term → ExceptT String IO thm  -- ints.ml's INTEGER_RULE
  NUM_REDUCE_CONV : ioconv  -- calc_num.ml's NUM_REDUCE_CONV
  SELECT_CONV : ioconv  -- class.ml's SELECT_CONV
  core1 : CoreThms1
  core2 : CoreThms2

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

/- ------------------------------------------------------------------------- -/
/- Finite means: fmean s f = sum s f / &(CARD s), with linearity and         -/
/- monotonicity, and the invariance of means over Z_N under translation.     -/
/- (szemeredi.ml 63-162)                                                     -/
/- ------------------------------------------------------------------------- -/

structure FiniteMeans where
  -- @@FIELDS
  fmean : thm
  FMEAN_ADD : thm
  FMEAN_SUB : thm
  FMEAN_LMUL : thm
  FMEAN_CONST : thm
  FMEAN_EQ : thm
  FMEAN_LE : thm
  FMEAN_ABS_LE : thm
  FMEAN_SUM : thm
  FMEAN_POS : thm
  SUM_SHIFT_MOD : thm
  FMEAN_SHIFT_MOD : thm
  deriving Inhabited

@[nospecialize]
def setupFiniteMeans [HolBase] (D : SzemerediDeps) :
    ExceptT String IO FiniteMeans := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, ASM_MESON_TAC, MOD_DOWN_CONV, NUMBER_RULE, REAL_ARITH_TAC,
        REAL_FIELD, new_definition, prioritize_real, .. } := D
  let { ADD_SYM, CARD_EQ_0, CONG, EMPTY_GSPEC, ETA_AX, IN_ELIM_THM, LT, MOD_LT,
        MOD_LT_EQ, .. } := D.core1
  let { REAL_ABS_DIV, REAL_ABS_NUM, REAL_LE_DIV, REAL_LE_INV_EQ, REAL_LE_RMUL,
        REAL_OF_NUM_EQ, REAL_POS, SUM_ABS, SUM_ADD, SUM_CLAUSES, SUM_CONST, SUM_EQ,
        SUM_EQ_GENERAL_INVERSES, SUM_LE, SUM_LMUL, SUM_POS_LE, SUM_RMUL, SUM_SUB,
        SUM_SWAP, real_div, .. } := D.core2
  -- @@SCOPE END
  prioritize_real

  let fmean ← new_definition
   r"fmean (X:A->bool) (g:A->real) = sum X g / &(CARD X)"

  let FMEAN_ADD ← prove
   r"!(X:A->bool) f g. FINITE X
        ==> fmean X (\x. f x + g x) = fmean X f + fmean X g"
   (SIMP_TAC [fmean, SUM_ADD] THEN REAL_ARITH_TAC)

  let FMEAN_SUB ← prove
   r"!(X:A->bool) f g. FINITE X
        ==> fmean X (\x. f x - g x) = fmean X f - fmean X g"
   (SIMP_TAC [fmean, SUM_SUB] THEN REAL_ARITH_TAC)

  let FMEAN_LMUL ← prove
   r"!(X:A->bool) c f. fmean X (\x. c * f x) = c * fmean X f"
   (REWRITE_TAC [fmean, SUM_LMUL] THEN REAL_ARITH_TAC)

  let FMEAN_CONST ← prove
   r"!(X:A->bool) c. FINITE X /\ ~(X = {}) ==> fmean X (\x. c) = c"
   (← do
    pure (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [fmean, SUM_CONST] THEN
    SUBGOAL_THEN (← q r"~(&(CARD(X:A->bool)) = &0)") MP_TAC THENL
     [REWRITE_TAC [REAL_OF_NUM_EQ] THEN ASM_MESON_TAC [CARD_EQ_0],
      CONV_TAC REAL_FIELD]))

  let FMEAN_EQ ← prove
   r"!(X:A->bool) f g. (!x. x IN X ==> f x = g x) ==> fmean X f = fmean X g"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [fmean] THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ THEN ASM_REWRITE_TAC [])

  let FMEAN_LE ← prove
   r"!(X:A->bool) f g. FINITE X /\ (!x. x IN X ==> f x <= g x)
        ==> fmean X f <= fmean X g"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [fmean, real_div] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC [REAL_LE_INV_EQ, REAL_POS] THEN
    MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC [])

  let FMEAN_ABS_LE ← prove
   r"!(X:A->bool) f. FINITE X ==> abs(fmean X f) <= fmean X (\x. abs(f x))"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [fmean, REAL_ABS_DIV, REAL_ABS_NUM] THEN
    REWRITE_TAC [real_div] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC [REAL_LE_INV_EQ, REAL_POS] THEN
    MATCH_MP_TAC SUM_ABS THEN ASM_REWRITE_TAC [])

  let FMEAN_SUM ← prove
   r"!(X:A->bool) (Ix:B->bool) f. FINITE X /\ FINITE Ix
        ==> fmean X (\x. sum Ix (\i. f i x)) = sum Ix (\i. fmean X (f i))"
   (← do
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [fmean, real_div, ← GSYM SUM_RMUL] THEN
    wPart lhand (fun t => do lhand (← rand t)) SUM_SWAP THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [ETA_AX]))

  let FMEAN_POS ← prove
   r"!(X:A->bool) f. FINITE X /\ (!x. x IN X ==> &0 <= f x) ==> &0 <= fmean X f"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [fmean] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC [SUM_POS_LE, REAL_POS])

  /- Means over Z_N are invariant under translation. -/

  let SUM_SHIFT_MOD ← prove
   r"!(f:num->real) n t.
     ~(n = 0)
     ==> sum {m | m < n} (\m. f((m + t) MOD n)) = sum {m | m < n} f"
   (← do
    pure (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
    EXISTS_TAC (← q r"\m. (m + t) MOD n") THEN
    EXISTS_TAC (← q r"\m. (m + (n - 1) * t) MOD n") THEN
    ASM_SIMP_TAC [IN_ELIM_THM, MOD_LT_EQ] THEN
    SUBGOAL_THEN (← q r"(n - 1) + 1 = n") MP_TAC THENL
     [ASM_ARITH_TAC, ALL_TAC] THEN
    SPEC_TAC (← q r"n - 1", ← q r"e:num") THEN GEN_TAC THEN DISCH_TAC THEN
    CONJ_TAC THEN X_GEN_TAC (← q r"y:num") THEN DISCH_TAC THEN
    CONV_TAC (LAND_CONV MOD_DOWN_CONV) THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (GEN_REWRITE_TAC RAND_CONV [← GSYM (← MATCH_MP MOD_LT th)])) THEN
    REWRITE_TAC [← GSYM CONG] THEN UNDISCH_TAC (← q r"e + 1 = n") THEN
    CONV_TAC NUMBER_RULE))

  let FMEAN_SHIFT_MOD ← prove
   r"!N c (g:num->real).
        fmean {r | r < N} (\r. g((c + r) MOD N)) = fmean {r | r < N} g"
   (← do
    pure (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"N = 0") THEN
    ASM_REWRITE_TAC [LT, EMPTY_GSPEC, fmean, SUM_CLAUSES] THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN ASM_SIMP_TAC [SUM_SHIFT_MOD]))

  -- @@RETURN BEGIN
  return { fmean, FMEAN_ADD, FMEAN_SUB, FMEAN_LMUL, FMEAN_CONST, FMEAN_EQ, FMEAN_LE,
           FMEAN_ABS_LE, FMEAN_SUM, FMEAN_POS, SUM_SHIFT_MOD, FMEAN_SHIFT_MOD }
  -- @@RETURN END


/- ------------------------------------------------------------------------- -/
/- Words: functions num->num that are 0 outside their length; variable      -/
/- words and substitution.  (szemeredi.ml 182-410)                           -/
/- ------------------------------------------------------------------------- -/

structure Words where
  -- @@FIELDS
  hj_cube : thm
  IN_HJ_CUBE : thm
  HAS_SIZE_HJ_CUBE : thm
  FINITE_HJ_CUBE : thm
  CARD_HJ_CUBE : thm
  HJ_CUBE_NONEMPTY : thm
  HJ_CUBE_MONO : thm
  HJ_CUBE_0 : thm
  hj_concat : thm
  hj_take : thm
  hj_drop : thm
  HJ_CONCAT_CUBE : thm
  HJ_TAKE_CUBE : thm
  HJ_DROP_CUBE : thm
  HJ_CONCAT_SPLIT : thm
  HJ_TAKE_CONCAT : thm
  HJ_DROP_CONCAT : thm
  HJ_CONCAT_INJ : thm
  HJ_CUBE_CONCAT_IMAGE : thm
  SUM_HJ_CONCAT : thm
  hj_subspace : thm
  hj_subst : thm
  HJ_SUBSPACE_0 : thm
  HJ_SUBSPACE_CUBE : thm
  HJ_SUBST_SUBST : thm
  HJ_SUBSPACE_SUBST : thm
  HJ_SUBST_CUBE : thm
  HJ_SUBST_INJ : thm
  HJ_SUBST_WORD : thm
  hj_identity : thm
  HJ_SUBSPACE_IDENTITY : thm
  HJ_SUBST_IDENTITY : thm
  HJ_SUBST_RID : thm
  deriving Inhabited

@[nospecialize]
def setupWords [HolBase] (D : SzemerediDeps) :
    ExceptT String IO Words := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, new_definition, .. } := D
  let { ADD_CLAUSES, ADD_SUB, ADD_SUB2, CROSS, EQ_IMP, EXISTS_PAIR_THM, EXTENSION,
        FORALL_PAIR_THM, FUN_EQ_THM, HAS_SIZE, HAS_SIZE_FUNSPACE, HAS_SIZE_NUMSEG_LT,
        IN_CROSS, IN_ELIM_THM, IN_IMAGE, IN_SING, LE_0, LT, LTE_TRANS, LT_ADD_LCANCEL,
        MEMBER_NOT_EMPTY, .. } := D.core1
  let { NOT_LE, NOT_LT, PAIR_EQ, SUBSET, SUM_EQ, SUM_IMAGE, SUM_SUM_PRODUCT, o_DEF, .. } := D.core2
  -- @@SCOPE END

  let hj_cube ← new_definition
   r"hj_cube k n = {x:num->num | (!i. i < n ==> x i < k) /\
                            (!i. n <= i ==> x i = 0)}"

  let IN_HJ_CUBE ← prove
   r"!k n x. x IN hj_cube k n <=>
           (!i. i < n ==> x i < k) /\ (!i. n <= i ==> x i = 0)"
   (REWRITE_TAC [hj_cube, IN_ELIM_THM])

  let HAS_SIZE_HJ_CUBE ← prove
   r"!k n. hj_cube k n HAS_SIZE k EXP n"
   (← do
    pure (REPEAT GEN_TAC THEN
    MP_TAC (← ISPECL [← q r"0", ← q r"k:num", ← q r"{a:num | a < k}", ← q r"n:num",
                      ← q r"{i:num | i < n}"] HAS_SIZE_FUNSPACE) THEN
    REWRITE_TAC [HAS_SIZE_NUMSEG_LT] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION, IN_HJ_CUBE, IN_ELIM_THM, NOT_LT]))

  let FINITE_HJ_CUBE ← prove
   r"!k n. FINITE(hj_cube k n)"
   (MESON_TAC [HAS_SIZE_HJ_CUBE, HAS_SIZE])

  let CARD_HJ_CUBE ← prove
   r"!k n. CARD(hj_cube k n) = k EXP n"
   (MESON_TAC [HAS_SIZE_HJ_CUBE, HAS_SIZE])

  let HJ_CUBE_NONEMPTY ← prove
   r"!k n. 1 <= k ==> ~(hj_cube k n = {})"
   (← do
    pure (REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC (← q r"\i:num. 0") THEN REWRITE_TAC [IN_HJ_CUBE] THEN ASM_ARITH_TAC))

  let HJ_CUBE_MONO ← prove
   r"!k k' n. k <= k' ==> hj_cube k n SUBSET hj_cube k' n"
   (REWRITE_TAC [SUBSET, IN_HJ_CUBE] THEN MESON_TAC [LTE_TRANS])

  let HJ_CUBE_0 ← prove
   r"!k. hj_cube k 0 = {(\i. 0)}"
   (REWRITE_TAC [EXTENSION, IN_HJ_CUBE, IN_SING, LT, LE_0] THEN
    REWRITE_TAC [FUN_EQ_THM])

  let hj_concat ← new_definition
   r"hj_concat l (x:num->num) (y:num->num) =
  \i. if i < l then x i else y (i - l)"

  let hj_take ← new_definition
   r"hj_take l (w:num->num) = \i. if i < l then w i else 0"

  let hj_drop ← new_definition
   r"hj_drop l (w:num->num) = \i. w (i + l)"

  let HJ_CONCAT_CUBE ← prove
   r"!k l m x y. x IN hj_cube k l /\ y IN hj_cube k m
               ==> hj_concat l x y IN hj_cube k (l + m)"
   (REWRITE_TAC [IN_HJ_CUBE, hj_concat] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC)

  let HJ_TAKE_CUBE ← prove
   r"!k l m w. w IN hj_cube k (l + m) ==> hj_take l w IN hj_cube k l"
   (REWRITE_TAC [IN_HJ_CUBE, hj_take] THEN REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC,
      ASM_REWRITE_TAC [← GSYM NOT_LE]])

  let HJ_DROP_CUBE ← prove
   r"!k l m w. w IN hj_cube k (l + m) ==> hj_drop l w IN hj_cube k m"
   (REWRITE_TAC [IN_HJ_CUBE, hj_drop] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC)

  let HJ_CONCAT_SPLIT ← prove
   r"!l w. hj_concat l (hj_take l w) (hj_drop l w) = w"
   (REWRITE_TAC [hj_concat, hj_take, hj_drop, FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC)

  let HJ_TAKE_CONCAT ← prove
   r"!k l x y. x IN hj_cube k l ==> hj_take l (hj_concat l x y) = x"
   (REWRITE_TAC [IN_HJ_CUBE, hj_concat, hj_take, FUN_EQ_THM] THEN
    REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC)

  let HJ_DROP_CONCAT ← prove
   r"!l x y. hj_drop l (hj_concat l x y) = y"
   (← do
    pure (REWRITE_TAC [hj_concat, hj_drop, FUN_EQ_THM, ← ARITH_RULE (← q r"~(i + l < l:num)"),
                       ADD_SUB]))

  let HJ_CONCAT_INJ ← prove
   r"!k l x y x' y'. x IN hj_cube k l /\ x' IN hj_cube k l /\
                   hj_concat l x y = hj_concat l x' y'
                   ==> x = x' /\ y = y'"
   (MESON_TAC [HJ_TAKE_CONCAT, HJ_DROP_CONCAT])

  let HJ_CUBE_CONCAT_IMAGE ← prove
   r"!k l m. hj_cube k (l + m) =
           IMAGE (\(x,y). hj_concat l x y) (hj_cube k l CROSS hj_cube k m)"
   (← do
    pure (REPEAT GEN_TAC THEN
    REWRITE_TAC [EXTENSION, IN_IMAGE, EXISTS_PAIR_THM, IN_CROSS] THEN
    X_GEN_TAC (← q r"w:num->num") THEN EQ_TAC THENL
     [DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC
        [← q r"hj_take l (w:num->num)", ← q r"hj_drop l (w:num->num)"] THEN
      REWRITE_TAC [HJ_CONCAT_SPLIT] THEN
      ASM_MESON_TAC [HJ_TAKE_CUBE, HJ_DROP_CUBE],
      MESON_TAC [HJ_CONCAT_CUBE]]))

  let SUM_HJ_CONCAT ← prove
   r"!k l m f. sum (hj_cube k (l + m)) f =
             sum (hj_cube k l)
               (\x. sum (hj_cube k m) (\y. f (hj_concat l x y)))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [HJ_CUBE_CONCAT_IMAGE] THEN
    wPart lhand (fun t => do lhand (← rand t)) SUM_IMAGE THEN
    ANTS_TAC THENL
     [REWRITE_TAC [FORALL_PAIR_THM, IN_CROSS, PAIR_EQ] THEN
      MESON_TAC [HJ_CONCAT_INJ],
      DISCH_THEN SUBST1_TAC] THEN
    SIMP_TAC [SUM_SUM_PRODUCT, FINITE_HJ_CUBE] THEN
    REWRITE_TAC [CROSS] THEN MATCH_MP_TAC SUM_EQ THEN
    REWRITE_TAC [FORALL_PAIR_THM, o_DEF])

  /- Variable words and substitution. -/

  let hj_subspace ← new_definition
   r"hj_subspace k m n (z:num->num) <=>
    z IN hj_cube (k + m) n /\ !j. j < m ==> ?i. i < n /\ z i = k + j"

  let hj_subst ← new_definition
   r"hj_subst k (z:num->num) (a:num->num) =
    \i. if z i < k then z i else a (z i - k)"

  let HJ_SUBSPACE_0 ← prove
   r"!k n z. hj_subspace k 0 n z <=> z IN hj_cube k n"
   (REWRITE_TAC [hj_subspace, ADD_CLAUSES, LT])

  let HJ_SUBSPACE_CUBE ← prove
   r"!k m n z. hj_subspace k m n z ==> z IN hj_cube (k + m) n"
   (SIMP_TAC [hj_subspace])

  let HJ_SUBST_SUBST ← prove
   r"!k z w a. hj_subst k (hj_subst k z w) a = hj_subst k z (hj_subst k w a)"
   (← do
    pure (REWRITE_TAC [hj_subst, FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"(z:num->num) x < k") THEN ASM_REWRITE_TAC []))

  let HJ_SUBSPACE_SUBST ← prove
   r"!k m m' n z w. 1 <= k /\ hj_subspace k m n z /\ hj_subspace k m' m w
                  ==> hj_subspace k m' n (hj_subst k z w)"
   (← do
    -- right to left: the third ARITH_RULE, then the second, then the first
    let a3 ← ARITH_RULE (← q r"~(k + p < k:num)")
    let a2 ← ARITH_RULE (← q r"1 <= k ==> 0 < k")
    let a1 ← ARITH_RULE (← q r"~(z < k) /\ z < k + m ==> z - k < m:num")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [hj_subspace, IN_HJ_CUBE, hj_subst] THEN
    STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN COND_CASES_TAC THENL
       [ASM_ARITH_TAC, ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC a1 THEN
      ASM_SIMP_TAC [],
      X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN
      ASM_SIMP_TAC [a2],
      X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"j:num")) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"p:num") STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN (← q r"?i. i < n /\ (z:num->num) i = k + p")
       (X_CHOOSE_THEN (← q r"q:num") STRIP_ASSUME_TAC) THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN
      EXISTS_TAC (← q r"q:num") THEN
      ASM_REWRITE_TAC [a3, ADD_SUB2]]))

  let HJ_SUBST_CUBE ← prove
   r"!k m n z a. 1 <= k /\ hj_subspace k m n z /\ a IN hj_cube k m
               ==> hj_subst k z a IN hj_cube k n"
   (← do
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM HJ_SUBSPACE_0] THEN
    MATCH_MP_TAC HJ_SUBSPACE_SUBST THEN EXISTS_TAC (← q r"m:num") THEN
    ASM_REWRITE_TAC [HJ_SUBSPACE_0]))

  let HJ_SUBST_INJ ← prove
   r"!k k' m n z a b.
        hj_subspace k m n z /\ a IN hj_cube k' m /\ b IN hj_cube k' m /\
        hj_subst k z a = hj_subst k z b
        ==> a = b"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [hj_subspace, IN_HJ_CUBE] THEN STRIP_TAC THEN
    REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"j:num") THEN
    ASM_CASES_TAC (← q r"j:num < m") THENL
     [SUBGOAL_THEN (← q r"?i. i < n /\ (z:num->num) i = k + j")
       (X_CHOOSE_THEN (← q r"i:num") STRIP_ASSUME_TAC) THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN
      UNDISCH_TAC (← q r"hj_subst k z a = hj_subst k z b") THEN
      REWRITE_TAC [hj_subst, FUN_EQ_THM] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"i:num")) THEN
      ASM_REWRITE_TAC [← ARITH_RULE (← q r"~(k + j < k:num)"), ADD_SUB2],
      ASM_MESON_TAC [NOT_LT]]))

  let HJ_SUBST_WORD ← prove
   r"!k n y a. 1 <= k /\ y IN hj_cube k n ==> hj_subst k y a = y"
   (← do
    pure (REWRITE_TAC [IN_HJ_CUBE, hj_subst, FUN_EQ_THM] THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"x:num < n") THEN ASM_SIMP_TAC [] THEN
    ASM_MESON_TAC [NOT_LT, ← ARITH_RULE (← q r"1 <= k ==> 0 < k")]))

  let hj_identity ← new_definition
   r"hj_identity k m = \i. if i < m then k + i else 0"

  let HJ_SUBSPACE_IDENTITY ← prove
   r"!k m. 1 <= k ==> hj_subspace k m m (hj_identity k m)"
   (← do
    pure (REWRITE_TAC [hj_subspace, IN_HJ_CUBE, hj_identity] THEN REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC [LT_ADD_LCANCEL],
      ASM_REWRITE_TAC [← GSYM NOT_LE],
      EXISTS_TAC (← q r"j:num") THEN ASM_REWRITE_TAC []]))

  let HJ_SUBST_IDENTITY ← prove
   r"!k k' m a. 1 <= k /\ a IN hj_cube k' m
              ==> hj_subst k (hj_identity k m) a = a"
   (← do
    -- right to left: the second ARITH_RULE, then the first
    let a2 ← ARITH_RULE (← q r"1 <= k ==> 0 < k")
    let a1 ← ARITH_RULE (← q r"~(k + x < k:num)")
    pure (REWRITE_TAC [IN_HJ_CUBE, hj_subst, hj_identity, FUN_EQ_THM] THEN
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"x:num < m") THEN
    ASM_REWRITE_TAC [a1, ADD_SUB2] THEN
    ASM_SIMP_TAC [a2] THEN
    ASM_MESON_TAC [NOT_LT]))

  let HJ_SUBST_RID ← prove
   r"!k m n z. hj_subspace k m n z ==> hj_subst k z (hj_identity k m) = z"
   (← do
    -- right to left: the third ARITH_RULE, then the second, then the first
    let a3 ← ARITH_RULE (← q r"~(z < k) ==> k + z - k = z:num")
    let a2 ← ARITH_RULE (← q r"~(0 < k) ==> k = 0")
    let a1 ← ARITH_RULE (← q r"~(z < k) /\ z < k + m ==> z - k < m:num")
    pure (REWRITE_TAC [hj_subspace, IN_HJ_CUBE, hj_subst, hj_identity, FUN_EQ_THM] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q r"x:num < n") THENL
     [SUBGOAL_THEN (← q r"(z:num->num) x - k < m") (fun th => REWRITE_TAC [th]) THENL
       [MATCH_MP_TAC a1 THEN
        ASM_SIMP_TAC [],
        ASM_ARITH_TAC],
      ASM_MESON_TAC [NOT_LT, a2, a3]]))

  -- @@RETURN BEGIN
  return { hj_cube, IN_HJ_CUBE, HAS_SIZE_HJ_CUBE, FINITE_HJ_CUBE, CARD_HJ_CUBE,
           HJ_CUBE_NONEMPTY, HJ_CUBE_MONO, HJ_CUBE_0, hj_concat, hj_take, hj_drop,
           HJ_CONCAT_CUBE, HJ_TAKE_CUBE, HJ_DROP_CUBE, HJ_CONCAT_SPLIT, HJ_TAKE_CONCAT,
           HJ_DROP_CONCAT, HJ_CONCAT_INJ, HJ_CUBE_CONCAT_IMAGE, SUM_HJ_CONCAT,
           hj_subspace, hj_subst, HJ_SUBSPACE_0, HJ_SUBSPACE_CUBE, HJ_SUBST_SUBST,
           HJ_SUBSPACE_SUBST, HJ_SUBST_CUBE, HJ_SUBST_INJ, HJ_SUBST_WORD, hj_identity,
           HJ_SUBSPACE_IDENTITY, HJ_SUBST_IDENTITY, HJ_SUBST_RID }
  -- @@RETURN END


/- ------------------------------------------------------------------------- -/
/- Combinatorial lines; concatenating and lifting variable words.            -/
/- (szemeredi.ml 413-543)                                                    -/
/- ------------------------------------------------------------------------- -/

structure Lines where
  -- @@FIELDS
  hj_line : thm
  hj_line_point : thm
  hj_has_line : thm
  HJ_LETTER_IN_CUBE : thm
  HJ_LINE_CUBE : thm
  HJ_LINE_VAR : thm
  HJ_LINE_POINT_CUBE : thm
  HJ_LINE_SUBST : thm
  HJ_LINE_POINT_SUBST : thm
  HJ_HAS_LINE_PULLBACK : thm
  hj_join : thm
  HJ_SUBST_JOIN : thm
  HJ_SUBSPACE_JOIN : thm
  hj_lift : thm
  HJ_SUBST_LIFT : thm
  HJ_SUBSPACE_LIFT : thm
  deriving Inhabited

@[nospecialize]
def setupLines [HolBase] (D : SzemerediDeps) (BWords : Words) :
    ExceptT String IO Lines := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, new_definition, .. } := D
  let { ADD_SUB2, FUN_EQ_THM, IN_ELIM_THM, .. } := D.core1
  let { HJ_SUBSPACE_SUBST, HJ_SUBST_CUBE, HJ_SUBST_SUBST, IN_HJ_CUBE, hj_concat,
        hj_drop, hj_subspace, hj_subst, .. } := BWords
  -- @@SCOPE END

  let hj_line ← new_definition
   r"hj_line k n (l:num->num) <=> hj_subspace k 1 n l"

  let hj_line_point ← new_definition
   r"hj_line_point k (l:num->num) a = hj_subst k l (\i. if i = 0 then a else 0)"

  let hj_has_line ← new_definition
   r"hj_has_line k n (A:(num->num)->bool) <=>
    ?l. hj_line k n l /\ !a. a < k ==> hj_line_point k l a IN A"

  let HJ_LETTER_IN_CUBE ← prove
   r"!k a. a < k ==> (\i. if i = 0 then a else 0) IN hj_cube k 1"
   (← do
    -- right to left: the third ARITH_RULE, then the second, then the first
    let a3 ← ARITH_RULE (← q r"1 <= i ==> ~(i = 0)")
    let a2 ← ARITH_RULE (← q r"i < 1 <=> i = 0")
    let a1 ← ARITH_RULE (← q r"i < 1 <=> i = 0")
    pure (REWRITE_TAC [IN_HJ_CUBE] THEN REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC [a1] THEN
      ASM_MESON_TAC [a2],
      ASM_SIMP_TAC [a3]]))

  let HJ_LINE_CUBE ← prove
   r"!k n l. hj_line k n l ==> l IN hj_cube (k + 1) n"
   (SIMP_TAC [hj_line, hj_subspace])

  let HJ_LINE_VAR ← prove
   r"!k n l. hj_line k n l ==> ?i. i < n /\ l i = k"
   (← do
    pure (REWRITE_TAC [hj_line, hj_subspace] THEN
    MESON_TAC [← ARITH_RULE (← q r"0 < 1 /\ k + 0 = k")]))

  let HJ_LINE_POINT_CUBE ← prove
   r"!k n l a. 1 <= k /\ hj_line k n l /\ a < k
             ==> hj_line_point k l a IN hj_cube k n"
   (← do
    pure (REWRITE_TAC [hj_line, hj_line_point] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HJ_SUBST_CUBE THEN EXISTS_TAC (← q r"1") THEN
    ASM_SIMP_TAC [HJ_LETTER_IN_CUBE]))

  let HJ_LINE_SUBST ← prove
   r"!k m n z u. 1 <= k /\ hj_subspace k m n z /\ hj_line k m u
               ==> hj_line k n (hj_subst k z u)"
   (REWRITE_TAC [hj_line] THEN MESON_TAC [HJ_SUBSPACE_SUBST])

  let HJ_LINE_POINT_SUBST ← prove
   r"!k z u a. hj_line_point k (hj_subst k z u) a =
             hj_subst k z (hj_line_point k u a)"
   (REWRITE_TAC [hj_line_point, HJ_SUBST_SUBST])

  let HJ_HAS_LINE_PULLBACK ← prove
   r"!k m n z A. 1 <= k /\ hj_subspace k m n z /\
               hj_has_line k m {a | hj_subst k z a IN A}
               ==> hj_has_line k n A"
   (← do
    pure (REWRITE_TAC [hj_has_line, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC (← q r"hj_subst k z (l:num->num)") THEN CONJ_TAC THENL
     [ASM_MESON_TAC [HJ_LINE_SUBST], ASM_SIMP_TAC [HJ_LINE_POINT_SUBST]]))

  let hj_join ← new_definition
   r"hj_join k l m1 (z1:num->num) (z2:num->num) =
    \i. if i < l then z1 i
        else if z2 (i - l) < k then z2 (i - l) else z2 (i - l) + m1"

  let HJ_SUBST_JOIN ← prove
   r"!k l m1 z1 z2 a.
        hj_subst k (hj_join k l m1 z1 z2) a =
        hj_concat l (hj_subst k z1 a) (hj_subst k z2 (hj_drop m1 a))"
   (← do
    pure (REWRITE_TAC [hj_subst, hj_join, hj_concat, hj_drop, FUN_EQ_THM] THEN
    REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"x:num < l") THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q r"(z2:num->num) (x - l) < k") THEN ASM_REWRITE_TAC [] THEN
    ASM_SIMP_TAC [← ARITH_RULE (← q r"~(z < k) ==> ~(z + m < k:num)")] THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC))

  let HJ_SUBSPACE_JOIN ← prove
   r"!k l m1 m2 n2 z1 z2.
        1 <= k /\ hj_subspace k m1 l z1 /\ hj_subspace k m2 n2 z2
        ==> hj_subspace k (m1 + m2) (l + n2) (hj_join k l m1 z1 z2)"
   (← do
    -- right to left: the ARITH_RULEs from the fifth to the first
    let a5 ← ARITH_RULE (← q r"~(k + j < k:num)")
    let a4 ← ARITH_RULE (← q r"~(l + i < l:num)")
    let a3 ← ARITH_RULE (← q r"1 <= k ==> 0 < k")
    let a2 ← ARITH_RULE (← q r"~(i < l) /\ i < l + n2 ==> i - l < n2:num")
    let a1 ← ARITH_RULE (← q r"x < k + m1 ==> x < k + m1 + m2:num")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [hj_subspace, IN_HJ_CUBE, hj_join] THEN
    STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN
      ASM_CASES_TAC (← q r"i:num < l") THEN ASM_REWRITE_TAC [] THENL
       [MATCH_MP_TAC a1 THEN
        ASM_SIMP_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"(z2:num->num)(i - l) < k + m2") MP_TAC THENL
       [ASM_MESON_TAC [a2],
        ARITH_TAC],
      X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"~(i:num < l) /\ (z2:num->num)(i - l) = 0")
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC,
        ASM_SIMP_TAC [a3]],
      X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"j:num < m1") THENL
       [SUBGOAL_THEN (← q r"?i. i < l /\ (z1:num->num) i = k + j")
         (X_CHOOSE_THEN (← q r"i:num") STRIP_ASSUME_TAC) THENL
         [ASM_MESON_TAC [], ALL_TAC] THEN
        EXISTS_TAC (← q r"i:num") THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC,
        SUBGOAL_THEN (← q r"?i. i < n2 /\ (z2:num->num) i = k + (j - m1)")
         (X_CHOOSE_THEN (← q r"i:num") STRIP_ASSUME_TAC) THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN
        EXISTS_TAC (← q r"l + i:num") THEN
        ASM_REWRITE_TAC [a4, ADD_SUB2, a5] THEN
        ASM_ARITH_TAC]]))

  let hj_lift ← new_definition
   r"hj_lift k (z:num->num) = \i. if z i < k then z i else z i + 1"

  let HJ_SUBST_LIFT ← prove
   r"!k z a. hj_subst (k + 1) (hj_lift k z) a = hj_subst k z a"
   (← do
    -- right to left: the second ARITH_RULE, then the first
    let a2 ← ARITH_RULE (← q r"~(z < k) ==> ~(z + 1 < k + 1)")
    let a1 ← ARITH_RULE (← q r"z < k ==> z < k + 1")
    pure (REWRITE_TAC [hj_subst, hj_lift, FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"(z:num->num) x < k") THEN
    ASM_SIMP_TAC [a1, a2] THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC))

  let HJ_SUBSPACE_LIFT ← prove
   r"!k m n z. 1 <= k /\ hj_subspace k m n z
             ==> hj_subspace (k + 1) m n (hj_lift k z)"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [hj_subspace, IN_HJ_CUBE, hj_lift] THEN
    STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"(z:num->num) i < k + m") MP_TAC THENL
       [ASM_SIMP_TAC [], ARITH_TAC],
      ASM_SIMP_TAC [← ARITH_RULE (← q r"1 <= k ==> 0 < k")],
      X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"?i. i < n /\ (z:num->num) i = k + j")
       (X_CHOOSE_THEN (← q r"i:num") STRIP_ASSUME_TAC) THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN
      EXISTS_TAC (← q r"i:num") THEN ASM_REWRITE_TAC [] THEN ARITH_TAC]))

  -- @@RETURN BEGIN
  return { hj_line, hj_line_point, hj_has_line, HJ_LETTER_IN_CUBE, HJ_LINE_CUBE,
           HJ_LINE_VAR, HJ_LINE_POINT_CUBE, HJ_LINE_SUBST, HJ_LINE_POINT_SUBST,
           HJ_HAS_LINE_PULLBACK, hj_join, HJ_SUBST_JOIN, HJ_SUBSPACE_JOIN, hj_lift,
           HJ_SUBST_LIFT, HJ_SUBSPACE_LIFT }
  -- @@RETURN END


/- ------------------------------------------------------------------------- -/
/- Densities of sets of words; sections, Markov and pigeonhole.              -/
/- (szemeredi.ml 546-727)                                                    -/
/- ------------------------------------------------------------------------- -/

structure Densities where
  -- @@FIELDS
  hj_density : thm
  FMEAN_HJ_CONCAT : thm
  HJ_DENSITY_SECTIONS : thm
  HJ_DENSITY_CARD : thm
  HJ_DENSITY_POS : thm
  HJ_DENSITY_LE_1 : thm
  HJ_DENSITY_MONO : thm
  HJ_DENSITY_EQ : thm
  FMEAN_MARKOV : thm
  HJ_DENSITY_MARKOV : thm
  CARD_PIGEONHOLE : thm
  FMEAN_EXISTS_GE : thm
  deriving Inhabited

@[nospecialize]
def setupDensities [HolBase] (D : SzemerediDeps) (BFiniteMeans : FiniteMeans) (BWords : Words) :
    ExceptT String IO Densities := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON_TAC, REAL_ARITH,
        REAL_ARITH_TAC, SET_TAC, TAUT, new_definition, .. } := D
  let { CARD_CLAUSES, CARD_EQ_0, CARD_SUBSET, CONTRAPOS_THM, EXP_ADD, EXP_EQ_0,
        FINITE_SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM, LT_NZ, NOT_EXISTS_THM, .. } := D.core1
  let { REAL_INV_0, REAL_INV_MUL, REAL_LE_ANTISYM, REAL_LE_DIV, REAL_LE_LDIV_EQ,
        REAL_LE_RDIV_EQ, REAL_LE_REFL, REAL_LE_RMUL, REAL_LE_TRANS, REAL_MUL_AC,
        REAL_MUL_LID, REAL_MUL_RID, REAL_MUL_RZERO, REAL_NOT_LE, REAL_NOT_LT,
        REAL_OF_NUM_LE, REAL_OF_NUM_LT, REAL_OF_NUM_MUL, REAL_POS, SUBSET, SUM_CASES,
        SUM_CONST, SUM_GROUP, SUM_LE, SUM_LMUL, SUM_LT_ALL, SUM_RESTRICT_SET, SUM_RMUL,
        real_div, .. } := D.core2
  let { FMEAN_LE, fmean, .. } := BFiniteMeans
  let { CARD_HJ_CUBE, FINITE_HJ_CUBE, SUM_HJ_CONCAT, .. } := BWords
  -- @@SCOPE END

  let hj_density ← new_definition
   r"hj_density k n (A:(num->num)->bool) =
    fmean (hj_cube k n) (\x. if x IN A then &1 else &0)"

  let FMEAN_HJ_CONCAT ← prove
   r"!k l m f. fmean (hj_cube k (l + m)) f =
             fmean (hj_cube k l)
               (\x. fmean (hj_cube k m) (\y. f (hj_concat l x y)))"
   (REWRITE_TAC [fmean, CARD_HJ_CUBE, SUM_HJ_CONCAT, EXP_ADD,
                 ← GSYM REAL_OF_NUM_MUL] THEN
    REWRITE_TAC [real_div, SUM_RMUL, REAL_INV_MUL] THEN
    REWRITE_TAC [REAL_MUL_AC])

  let HJ_DENSITY_SECTIONS ← prove
   r"!k l m A. hj_density k (l + m) A =
             fmean (hj_cube k l)
               (\x. hj_density k m {y | hj_concat l x y IN A})"
   (REWRITE_TAC [hj_density, FMEAN_HJ_CONCAT, IN_ELIM_THM])

  let HJ_DENSITY_CARD ← prove
   r"!k n A. hj_density k n A =
           &(CARD {x | x IN hj_cube k n /\ x IN A}) / &(k EXP n)"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [hj_density, fmean, CARD_HJ_CUBE] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [← GSYM SUM_RESTRICT_SET] THEN
    SUBGOAL_THEN (← q r"FINITE {x | x IN hj_cube k n /\ x IN A}") ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"hj_cube k n") THEN
      REWRITE_TAC [FINITE_HJ_CUBE] THEN SET_TAC [],
      ASM_SIMP_TAC [SUM_CONST, REAL_MUL_RID]]))

  let HJ_DENSITY_POS ← prove
   r"!k n A. &0 <= hj_density k n A"
   (REWRITE_TAC [HJ_DENSITY_CARD] THEN SIMP_TAC [REAL_LE_DIV, REAL_POS])

  let HJ_DENSITY_LE_1 ← prove
   r"!k n A. hj_density k n A <= &1"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [HJ_DENSITY_CARD] THEN
    ASM_CASES_TAC (← q r"k EXP n = 0") THEN
    ASM_REWRITE_TAC [real_div, REAL_INV_0, REAL_MUL_RZERO, REAL_POS] THEN
    REWRITE_TAC [← GSYM real_div] THEN
    ASM_SIMP_TAC [REAL_LE_LDIV_EQ, REAL_OF_NUM_LT, LT_NZ, REAL_MUL_LID] THEN
    REWRITE_TAC [REAL_OF_NUM_LE, ← GSYM CARD_HJ_CUBE] THEN
    MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC [FINITE_HJ_CUBE] THEN SET_TAC []))

  let HJ_DENSITY_MONO ← prove
   r"!k n A B. (!x. x IN hj_cube k n /\ x IN A ==> x IN B)
             ==> hj_density k n A <= hj_density k n B"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [hj_density] THEN MATCH_MP_TAC FMEAN_LE THEN
    REWRITE_TAC [FINITE_HJ_CUBE] THEN REPEAT STRIP_TAC THEN
    REPEAT COND_CASES_TAC THEN ASM_MESON_TAC [REAL_LE_REFL, REAL_POS])

  let HJ_DENSITY_EQ ← prove
   r"!k n A B. (!x. x IN hj_cube k n ==> (x IN A <=> x IN B))
             ==> hj_density k n A = hj_density k n B"
   (MESON_TAC [HJ_DENSITY_MONO, REAL_LE_ANTISYM])

  let FMEAN_MARKOV ← prove
   r"!(X:A->bool) f a b.
        FINITE X /\ (!x. x IN X ==> f x <= &1) /\ &0 <= b /\
        a <= fmean X f
        ==> (a - b) * &(CARD X) <= &(CARD {x | x IN X /\ b <= f x})"
   (← do
    -- right to left: the second REAL_ARITH, then the first
    let r2 ← REAL_ARITH
     (← q r"!a b c s y. a * c <= s /\ s <= y + b * c ==> (a - b) * c <= y:real")
    let r1 ← REAL_ARITH
     (← q r"c2 * b <= cx * b ==> x + c2 * b <= x + b * cx:real")
    pure (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"X:A->bool = {}") THENL
     [ASM_REWRITE_TAC [CARD_CLAUSES, REAL_MUL_RZERO, REAL_POS], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"&0 < &(CARD(X:A->bool))") ASSUME_TAC THENL
     [REWRITE_TAC [REAL_OF_NUM_LT, LT_NZ] THEN ASM_MESON_TAC [CARD_EQ_0],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"a * &(CARD(X:A->bool)) <= sum X f") ASSUME_TAC THENL
     [UNDISCH_TAC (← q r"a <= fmean (X:A->bool) f") THEN
      ASM_SIMP_TAC [fmean, REAL_LE_RDIV_EQ],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"sum (X:A->bool) f <=
      &(CARD {x | x IN X /\ b <= f x}) + b * &(CARD X)")
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"sum (X:A->bool) (\x. if b <= f x then &1 else b)") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
        COND_CASES_TAC THEN ASM_SIMP_TAC [] THEN ASM_REAL_ARITH_TAC,
        ALL_TAC] THEN
      ASM_SIMP_TAC [SUM_CASES] THEN
      SUBGOAL_THEN (← q r"FINITE {x:A | x IN X /\ b <= f x} /\
                    FINITE {x:A | x IN X /\ ~(b <= f x)}")
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC (← q r"X:A->bool") THEN ASM_REWRITE_TAC [] THEN SET_TAC [],
        ALL_TAC] THEN
      ASM_SIMP_TAC [SUM_CONST, REAL_MUL_RID] THEN
      MATCH_MP_TAC r1 THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC [REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
      ASM_REWRITE_TAC [] THEN SET_TAC [],
      DISCH_TAC] THEN
    MATCH_MP_TAC r2 THEN
    EXISTS_TAC (← q r"sum (X:A->bool) f") THEN ASM_REWRITE_TAC []))

  let HJ_DENSITY_MARKOV ← prove
   r"!k l f a b.
        1 <= k /\ (!x. x IN hj_cube k l ==> f x <= &1) /\ &0 <= b /\
        a <= fmean (hj_cube k l) f
        ==> a - b <= hj_density k l {x | b <= f x}"
   (← do
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [HJ_DENSITY_CARD, IN_ELIM_THM] THEN
    SUBGOAL_THEN (← q r"&0 < &(k EXP l)") ASSUME_TAC THENL
     [REWRITE_TAC [REAL_OF_NUM_LT, LT_NZ, EXP_EQ_0] THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    ASM_SIMP_TAC [REAL_LE_RDIV_EQ] THEN REWRITE_TAC [← GSYM CARD_HJ_CUBE] THEN
    MATCH_MP_TAC FMEAN_MARKOV THEN ASM_REWRITE_TAC [FINITE_HJ_CUBE]))

  let CARD_PIGEONHOLE ← prove
   r"!(g:A->B) X S.
        FINITE X /\ FINITE S /\ ~(S = {}) /\ (!x. x IN X ==> g x IN S)
        ==> ?s. s IN S /\
                &(CARD X) <= &(CARD S) * &(CARD {x | x IN X /\ g x = s})"
   (← do
    pure (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"sum (S:B->bool) (\s. &(CARD {x:A | x IN X /\ g x = s})) =
      &(CARD(X:A->bool))")
    ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q r"g:A->B", ← q r"(\x. &1):A->real", ← q r"X:A->bool", ← q r"S:B->bool"]
        SUM_GROUP) THEN
      ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
      SUBGOAL_THEN (← q r"!s:B. FINITE {x:A | x IN X /\ g x = s}") ASSUME_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC (← q r"X:A->bool") THEN ASM_REWRITE_TAC [] THEN SET_TAC [],
        ASM_SIMP_TAC [SUM_CONST, REAL_MUL_RID]],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"~(!s:B. s IN S
             ==> &(CARD(S:B->bool)) * &(CARD {x:A | x IN X /\ g x = s}) <
                 &(CARD(X:A->bool)))")
    MP_TAC THENL
     [DISCH_TAC THEN
      MP_TAC (← ISPECL
       [← q r"\s:B. &(CARD(S:B->bool)) * &(CARD {x:A | x IN X /\ g x = s})",
        ← q r"\s:B. &(CARD(X:A->bool))", ← q r"S:B->bool"] SUM_LT_ALL) THEN
      ASM_SIMP_TAC [SUM_LMUL, SUM_CONST] THEN REAL_ARITH_TAC,
      MESON_TAC [REAL_NOT_LT]]))

  let FMEAN_EXISTS_GE ← prove
   r"!(X:A->bool) f c. FINITE X /\ ~(X = {}) /\ c <= fmean X f
                     ==> ?x. x IN X /\ c <= f x"
   (← do
    pure (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"&0 < &(CARD(X:A->bool))") ASSUME_TAC THENL
     [REWRITE_TAC [REAL_OF_NUM_LT, LT_NZ] THEN ASM_MESON_TAC [CARD_EQ_0],
      ALL_TAC] THEN
    UNDISCH_TAC (← q r"c <= fmean (X:A->bool) f") THEN
    ASM_SIMP_TAC [fmean, REAL_LE_RDIV_EQ] THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC [NOT_EXISTS_THM, REAL_NOT_LE, ← TAUT (← q r"~(p /\ q) <=> p ==> ~q")] THEN
    DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"f:A->real", ← q r"\x:A. (c:real)", ← q r"X:A->bool"] SUM_LT_ALL) THEN
    ASM_SIMP_TAC [SUM_CONST] THEN REAL_ARITH_TAC))

  -- @@RETURN BEGIN
  return { hj_density, FMEAN_HJ_CONCAT, HJ_DENSITY_SECTIONS, HJ_DENSITY_CARD,
           HJ_DENSITY_POS, HJ_DENSITY_LE_1, HJ_DENSITY_MONO, HJ_DENSITY_EQ, FMEAN_MARKOV,
           HJ_DENSITY_MARKOV, CARD_PIGEONHOLE, FMEAN_EXISTS_GE }
  -- @@RETURN END


/- ------------------------------------------------------------------------- -/
/- Templates, combinatorial lines and monochromatic lines; products of       -/
/- templates, recolourings by patterns, and the fixed line.                  -/
/- (szemeredi.ml 729-1198)                                                   -/
/- ------------------------------------------------------------------------- -/

structure Templates where
  -- @@FIELDS
  hjt_subst : thm
  hjt_line : thm
  hjt_mono : thm
  hales_jewett_template : thm
  HJT_1 : thm
  HJT_MONO_N : thm
  hjt_prod : thm
  HJT_SUBST_PROD : thm
  hjt_almost_mono : thm
  hjt_focused : thm
  HJT_ALMOST_MONO_LT : thm
  HJT_COLLAPSE : thm
  hjt_lift : thm
  NSUM_NUMSEG_LT_SHIFT : thm
  HJT_NSUM_DIGIT_SPLIT : thm
  HJT_DIGIT_RECOVER : thm
  HJT_RECOLOUR : thm
  HJT_LIFT_SUBST_LE : thm
  HJT_PROD_LIFT_SUBST_LE : thm
  HJT_SUBST_FIXED : thm
  HJT_GEN_ALMOST_MONO : thm
  HJT_PROD_LINE : thm
  HJT_FIXED_LINE_MONO : thm
  deriving Inhabited

@[nospecialize]
def setupTemplates [HolBase] (D : SzemerediDeps) :
    ExceptT String IO Templates := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC,
        new_definition, .. } := D
  let { ADD_CLAUSES, ADD_SUB, ARITH, ARITH_EQ, CARD_IMAGE_INJ, CARD_NUMSEG,
        CARD_SUBSET_EQ, DIVIDES_NSUM, DIVIDES_RMUL, DIV_LT, DIV_MULT_ADD, EXP_1,
        EXP_ADD, EXP_EQ_0, EXTENSION, FINITE_NUMSEG, FINITE_NUMSEG_LT, FINITE_SING,
        FINITE_SUBSET, FINITE_UNION, FUN_EQ_THM, IN_ELIM_THM, IN_IMAGE, IN_INTER,
        IN_NUMSEG, IN_SING, IN_UNION, MOD_LT, MOD_MULT_ADD, .. } := D.core1
  let { NSUM_CLAUSES_NUMSEG, NSUM_CLAUSES_NUMSEG_LT, NSUM_DIGITS_BOUND,
        NSUM_DIGITS_UNIQUE, NSUM_SING, NSUM_UNION_NONZERO, SUBSET, SUC_SUB1, divides, .. } := D.core2
  -- @@SCOPE END

  let hjt_subst ← new_definition
   r"hjt_subst t N (tw:num->num) a =
    \i. if i < N then (if tw i = t then a else tw i) else 0"

  let hjt_line ← new_definition
   r"hjt_line t N (tw:num->num) <=>
    (!i. i < N ==> tw i <= t) /\ (?i. i < N /\ tw i = t)"

  let hjt_mono ← new_definition
   r"hjt_mono t N (chi:(num->num)->num) tw <=>
    !a a'. a < t /\ a' < t
           ==> chi(hjt_subst t N tw a) = chi(hjt_subst t N tw a')"

  let hales_jewett_template ← new_definition
   r"hales_jewett_template t r N <=>
    !chi:(num->num)->num. (!x. chi x < r)
        ==> ?tw. hjt_line t N tw /\ hjt_mono t N chi tw"

  let HJT_1 ← prove
   r"!r. 1 <= r ==> hales_jewett_template 1 r 1"
   (← do
    pure (REWRITE_TAC [hales_jewett_template] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC (← q r"\i:num. if i = 0 then 1 else 0") THEN
    REWRITE_TAC [hjt_line, hjt_mono] THEN CONJ_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN COND_CASES_TAC THEN ARITH_TAC,
        EXISTS_TAC (← q r"0") THEN REWRITE_TAC [ARITH]],
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN (← q r"a = 0 /\ a' = 0") (fun th => REWRITE_TAC [th]) THEN
        ASM_ARITH_TAC]))

  let HJT_MONO_N ← prove
   r"!t r N N'. 1 <= t /\ hales_jewett_template t r N /\ N <= N'
              ==> hales_jewett_template t r N'"
   (← do
    pure (REWRITE_TAC [hales_jewett_template] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"chi:(num->num)->num")) THEN
      ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"tw:num->num") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"\i:num. if i < N then tw i else 0") THEN
    SUBGOAL_THEN
     (← q r"!a. hjt_subst t N' (\i. if i < N then tw i else 0) a = hjt_subst t N tw a")
     ASSUME_TAC THENL
     [GEN_TAC THEN REWRITE_TAC [hjt_subst, FUN_EQ_THM] THEN X_GEN_TAC (← q r"j:num") THEN
      REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC (← q r"hjt_line t N tw") THEN REWRITE_TAC [hjt_line] THEN
      STRIP_TAC THEN
      CONJ_TAC THENL
       [X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN COND_CASES_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ARITH_TAC],
        EXISTS_TAC (← q r"i:num") THEN ASM_REWRITE_TAC [] THEN
        SUBGOAL_THEN (← q r"i:num < N'") ASSUME_TAC THENL
         [ASM_ARITH_TAC, ASM_REWRITE_TAC []]],
      REWRITE_TAC [hjt_mono] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC (← q r"hjt_mono t N chi tw") THEN REWRITE_TAC [hjt_mono] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC []]))

  let hjt_prod ← new_definition
   r"hjt_prod D (sg:num->num) (rho:num->num) =
    \i. if i < D then sg i else rho (i - D)"

  let HJT_SUBST_PROD ← prove
   r"!u D M sg rho a.
      hjt_subst u (D + M) (hjt_prod D sg rho) a =
      hjt_prod D (hjt_subst u D sg a) (hjt_subst u M rho a)"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [hjt_subst, hjt_prod, FUN_EQ_THM] THEN
    X_GEN_TAC (← q r"i:num") THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN ASM_ARITH_TAC))

  let hjt_almost_mono ← new_definition
   r"hjt_almost_mono (chi:(num->num)->num) t N (L:num->num) (c:num) <=>
    hjt_line (t+1) N L /\ (!a. a < t ==> chi(hjt_subst (t+1) N L a) = c)"

  let hjt_focused ← new_definition
   r"hjt_focused (chi:(num->num)->num) t N (Lf:num->num->num) (cf:num->num)
             (focus:num->num) s <=>
    (!i. i < s ==> hjt_almost_mono chi t N (Lf i) (cf i)) /\
    (!i j. i < s /\ j < s /\ cf i = cf j ==> i = j) /\
    (!i:num. i < s ==> hjt_subst (t+1) N (Lf i) t = focus)"

  let HJT_ALMOST_MONO_LT ← prove
   r"!chi t r N (Lf:num->num->num) cf i.
     1 <= t /\ (!x. chi x < r) /\ hjt_almost_mono chi t N (Lf i) (cf i)
     ==> cf i < r"
   (← do
    pure (REWRITE_TAC [hjt_almost_mono] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"0")) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC []))

  let HJT_COLLAPSE ← prove
   r"!chi t r N Lf cf focus.
      1 <= t /\ (!x. chi x < r) /\ hjt_focused chi t N Lf cf focus r
      ==> ?tw. hjt_line (t+1) N tw /\ hjt_mono (t+1) N chi tw"
   (← do
    pure (REWRITE_TAC [hjt_focused] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"1 <= r") ASSUME_TAC THENL
     [FIRST_ASSUM (MP_TAC o SPEC (← q r"focus:num->num")) THEN ARITH_TAC, ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!i:num. i < r ==> cf i < r") ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"chi:(num->num)->num", ← q r"t:num", ← q r"r:num", ← q r"N:num",
                        ← q r"Lf:num->num->num", ← q r"cf:num->num", ← q r"i:num"]
                       HJT_ALMOST_MONO_LT) THEN
      ASM_SIMP_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"?i:num. i < r /\
      cf i = (chi:(num->num)->num) focus") STRIP_ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q r"cf:num->num",
       ← q r"0..r-1"] (← HolLight.INST_TYPE [(← qty "num", ← qty "B")] CARD_IMAGE_INJ)) THEN
      ANTS_TAC THENL
       [REWRITE_TAC [IN_NUMSEG, FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
          ASM_ARITH_TAC, ALL_TAC] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN (← q r"IMAGE (cf:num->num) (0..r-1) = 0..r-1") ASSUME_TAC THENL
       [MATCH_MP_TAC CARD_SUBSET_EQ THEN REWRITE_TAC [FINITE_NUMSEG] THEN
        REPEAT CONJ_TAC THENL
         [REWRITE_TAC [SUBSET, IN_IMAGE, IN_NUMSEG] THEN X_GEN_TAC (← q r"y:num") THEN
          DISCH_THEN (X_CHOOSE_THEN (← q r"x':num") STRIP_ASSUME_TAC) THEN
          SUBGOAL_THEN (← q r"(cf:num->num) x' < r") MP_TAC THENL
           [FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x':num")) THEN
             ASM_ARITH_TAC, ASM_ARITH_TAC],
          ASM_REWRITE_TAC [CARD_NUMSEG] THEN ARITH_TAC],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"(chi:(num->num)->num) focus IN IMAGE cf
        (0..r-1)") MP_TAC THENL
       [ASM_REWRITE_TAC [IN_NUMSEG] THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"focus:num->num")) THEN ARITH_TAC,
        REWRITE_TAC [IN_IMAGE, IN_NUMSEG] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"i:num") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q r"i:num") THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC],
      ALL_TAC] THEN
    EXISTS_TAC (← q r"(Lf:num->num->num) i") THEN
    SUBGOAL_THEN (← q r"hjt_almost_mono chi t N ((Lf:num->num->num) i) (cf i)")
    MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    REWRITE_TAC [hjt_almost_mono] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [hjt_mono] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:num", ← q r"a':num"] THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"!b. b < t + 1 ==>
      chi(hjt_subst (t+1) N ((Lf:num->num->num) i) b) = (cf:num->num) i")
     (fun th => ASM_MESON_TAC [th]) THEN
    X_GEN_TAC (← q r"b:num") THEN DISCH_TAC THEN
    ASM_CASES_TAC (← q r"b:num = t") THENL
     [ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"hjt_subst (t+1) N ((Lf:num->num->num) i) t = focus")
        SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ASM_REWRITE_TAC []],
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]))

  let hjt_lift ← new_definition
   r"hjt_lift t M (l:num->num) = \i. if i < M /\ l i = t then t + 1 else l i"

  let NSUM_NUMSEG_LT_SHIFT ← prove
   r"!f n. nsum {i | i < n} f = nsum(1..n) (\i. f(i - 1))"
   (← do
    pure (GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [NSUM_CLAUSES_NUMSEG_LT, NSUM_CLAUSES_NUMSEG, ARITH_EQ,
                     ← ARITH_RULE (← q r"1 <= SUC n"), SUC_SUB1]))

  let HJT_NSUM_DIGIT_SPLIT ← prove
   r"!b (x:num->num) Ns i0. i0 < Ns ==>
    nsum {i:num | i < Ns} (\i. b EXP i * x i) =
    b EXP i0 * x i0 +
    (nsum {i:num | i < i0} (\i. b EXP i * x i) +
     nsum {i:num | i0 < i /\ i < Ns} (\i. b EXP i * x i))"
   (← do
    pure (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"{i:num | i < Ns} = {i0} UNION ({i:num | i < i0} UNION {i:num | i0 <
       i /\ i < Ns})")
     SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_UNION, IN_SING, IN_ELIM_THM] THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"FINITE {i:num | i < i0} /\ FINITE {i:num | i0 < i /\ i < Ns}")
     STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC (← q r"{i:num | i < Ns}") THEN
      REWRITE_TAC [FINITE_NUMSEG_LT, SUBSET, IN_ELIM_THM] THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"nsum ({i0} UNION {i:num | i < i0} UNION {i:num | i0 < i /\ i < Ns})
           (\i. b EXP i * (x:num->num) i) =
      nsum {i0} (\i. b EXP i * x i) +
      nsum ({i:num | i < i0} UNION {i:num | i0 < i /\
        i < Ns}) (\i. b EXP i * x i)")
     SUBST1_TAC THENL
     [MATCH_MP_TAC NSUM_UNION_NONZERO THEN
      ASM_REWRITE_TAC [FINITE_SING, FINITE_UNION] THEN
      REWRITE_TAC [IN_INTER, IN_SING, IN_UNION, IN_ELIM_THM] THEN ARITH_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [NSUM_SING] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC NSUM_UNION_NONZERO THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [IN_INTER, IN_UNION, IN_ELIM_THM] THEN ARITH_TAC))

  let HJT_DIGIT_RECOVER ← prove
   r"!b Ns x i0.
    2 <= b /\ (!i. i < Ns ==> x i < b) /\ i0 < Ns
    ==> (nsum {i:num | i < Ns} (\i. b EXP i * x i) DIV (b EXP i0))
      MOD b = x i0"
   (← do
    pure (REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [HJT_NSUM_DIGIT_SPLIT] THEN
    SUBGOAL_THEN (← q r"nsum {i:num | i < i0} (\i. b EXP i * (x:num->num)
      i) < b EXP i0")
     ASSUME_TAC THENL
     [REWRITE_TAC [NSUM_NUMSEG_LT_SHIFT] THEN MATCH_MP_TAC NSUM_DIGITS_BOUND THEN
      REWRITE_TAC [IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"?H. nsum {i:num | i0 < i /\ i < Ns} (\i. b EXP i * (x:num->num) i) =
          (b EXP i0 * b) * H") STRIP_ASSUME_TAC THENL
     [REWRITE_TAC [← GSYM divides] THEN MATCH_MP_TAC DIVIDES_NSUM THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{i:num | i < Ns}") THEN
        REWRITE_TAC [FINITE_NUMSEG_LT, SUBSET, IN_ELIM_THM] THEN ARITH_TAC,
        X_GEN_TAC (← q r"i:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN
        MATCH_MP_TAC DIVIDES_RMUL THEN
        SUBGOAL_THEN (← q r"b EXP i0 * b = b EXP (i0 + 1)") SUBST1_TAC THENL
         [REWRITE_TAC [EXP_ADD, EXP_1], ALL_TAC] THEN
        REWRITE_TAC [divides] THEN EXISTS_TAC (← q r"b EXP (i - (i0 + 1))") THEN
        REWRITE_TAC [← GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN
     (← q r"b EXP i0 * x i0 +
      nsum {i:num | i < i0} (\i. b EXP i * (x:num->num) i) + (b EXP i0 * b) * H =
      b EXP i0 * (x i0 + b * H) + nsum {i:num | i < i0} (\i. b EXP i * x i)")
     SUBST1_TAC THENL [ARITH_TAC, ALL_TAC] THEN
    SUBGOAL_THEN (← q r"~(b EXP i0 = 0)") ASSUME_TAC THENL
     [REWRITE_TAC [EXP_EQ_0] THEN ASM_ARITH_TAC, ALL_TAC] THEN
    ASM_SIMP_TAC [DIV_MULT_ADD, DIV_LT, ADD_CLAUSES] THEN
    SUBGOAL_THEN (← q r"(x:num->num) i0 < b") ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN
    ASM_SIMP_TAC [MOD_MULT_ADD, MOD_LT]))

  let HJT_RECOLOUR ← prove
   r"!chi t Ns M r.
    1 <= t /\ (!x. chi x < r)
    ==> ?psi.
          (!y. psi y < r EXP ((t+2) EXP Ns)) /\
          (!l'. hjt_mono t M psi l'
           ==> !x a a'.
                 (!i. i < Ns ==> x i <= t + 1) /\ (!i. Ns <= i ==> x i = 0) /\
                 a < t /\ a' < t
                 ==> chi(hjt_prod Ns x (hjt_subst t M l' a)) =
                     chi(hjt_prod Ns x (hjt_subst t M l' a')))"
   (← do
    pure (REPEAT STRIP_TAC THEN
    EXISTS_TAC
     (← q r"\y. nsum {j:num | j < (t+2) EXP Ns}
               (\j. r EXP j *
                    (chi:(num->num)->num)
                      (hjt_prod Ns
                         (\i. if i < Ns then (j DIV ((t+2) EXP i))
                           MOD (t+2) else 0)
                         y))") THEN
    BETA_TAC THEN
    SUBGOAL_THEN (← q r"1 <= r") ASSUME_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o SPEC (← q r"(\i:num. 0):num->num")) THEN ARITH_TAC,
      ALL_TAC] THEN
    CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC [NSUM_NUMSEG_LT_SHIFT] THEN
      MATCH_MP_TAC NSUM_DIGITS_BOUND THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    X_GEN_TAC (← q r"l':num->num") THEN
    REWRITE_TAC [hjt_mono] THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [← q r"x:num->num", ← q r"a:num", ← q r"a':num"] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"a:num", ← q r"a':num"]) THEN
    ASM_REWRITE_TAC [] THEN BETA_TAC THEN DISCH_TAC THEN
    MP_TAC (← ISPECL
     [← q r"r:num", ← q r"(t+2) EXP Ns",
      ← q r"\j. (chi:(num->num)->num)
             (hjt_prod Ns
                (\i. if i < Ns then ((j - 1) DIV ((t+2) EXP i)) MOD (t+2)
                     else 0)
                (hjt_subst t M l' a))",
      ← q r"\j. (chi:(num->num)->num)
             (hjt_prod Ns
                (\i. if i < Ns then ((j - 1) DIV ((t+2) EXP i)) MOD (t+2)
                     else 0)
                (hjt_subst t M l' a'))"]
     NSUM_DIGITS_UNIQUE) THEN
    ANTS_TAC THENL
     [BETA_TAC THEN ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (MP_TAC o REWRITE_RULE [NSUM_NUMSEG_LT_SHIFT]) THEN
      REWRITE_TAC [],
      ALL_TAC] THEN
    BETA_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN
     (← q r"(\i. if i < Ns
           then (nsum {k | k < Ns} (\k. (t+2) EXP k * (x:num->num) k) DIV
                 ((t+2) EXP i)) MOD (t+2)
           else 0) = x") ASSUME_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"i:num") THEN COND_CASES_TAC THENL
       [MATCH_MP_TAC HJT_DIGIT_RECOVER THEN ASM_REWRITE_TAC [] THEN
        CONJ_TAC THENL
         [ARITH_TAC,
          X_GEN_TAC (← q r"i2:num") THEN DISCH_TAC THEN
          SUBGOAL_THEN (← q r"(x:num->num) i2 <= t + 1") MP_TAC THENL
           [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ARITH_TAC]],
        SUBGOAL_THEN (← q r"(x:num->num) i = 0") (fun th => REWRITE_TAC [th]) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"nsum {k | k < Ns} (\k. (t+2) EXP k * (x:num->num) k) < (t+2) EXP Ns")
     ASSUME_TAC THENL
     [REWRITE_TAC [NSUM_NUMSEG_LT_SHIFT] THEN MATCH_MP_TAC NSUM_DIGITS_BOUND THEN
      REWRITE_TAC [IN_NUMSEG] THEN X_GEN_TAC (← q r"i2:num") THEN STRIP_TAC THEN
      SUBGOAL_THEN (← q r"(x:num->num) (i2 - 1) <= t + 1") MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC, ARITH_TAC],
      ALL_TAC] THEN
    FIRST_X_ASSUM (fun th => tactic_of do
      if is_forall (concl th) && is_imp (strip_forall (concl th)).2
      then pure (MP_TAC (← SPEC
        (← q r"nsum {k | k < Ns} (\k. (t+2) EXP k * (x:num->num) k) + 1") th))
      else pure NO_TAC) THEN
    ANTS_TAC THENL
     [REWRITE_TAC [IN_NUMSEG,
                   ← ARITH_RULE (← q r"1 <= c + 1 /\ c + 1 <= n <=> c < n")] THEN
      FIRST_X_ASSUM ACCEPT_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [ADD_SUB] THEN DISCH_TAC THEN
    FIRST_X_ASSUM (fun th => tactic_of do
      if is_eq (concl th) && (match lhs (concl th) with
                              | .ok l => is_abs l | .error _ => false)
      then pure (RULE_ASSUM_TAC (REWRITE_RULE [th]))
      else pure NO_TAC) THEN
    FIRST_X_ASSUM ACCEPT_TAC))

  let HJT_LIFT_SUBST_LE ← prove
   r"!t M l a. hjt_line t M l /\ a <= t
      ==> hjt_subst (t+1) M (hjt_lift t M l) a = hjt_subst t M l a"
   (← do
    pure (REWRITE_TAC [hjt_line] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [hjt_subst, hjt_lift, FUN_EQ_THM] THEN X_GEN_TAC (← q r"k:num") THEN
    ASM_CASES_TAC (← q r"k:num < M") THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"k:num") th))) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_TAC THEN
    ASM_CASES_TAC (← q r"(l:num->num) k = t") THEN ASM_REWRITE_TAC [] THEN
      ASM_ARITH_TAC))

  let HJT_PROD_LIFT_SUBST_LE ← prove
   r"!t M l Ns p a.
     hjt_line t M l /\ a <= t
     ==> hjt_subst (t+1) (Ns+M) (hjt_prod Ns p (hjt_lift t M l)) a =
         hjt_prod Ns (hjt_subst (t+1) Ns p a) (hjt_subst t M l a)"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [HJT_SUBST_PROD] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC HJT_LIFT_SUBST_LE THEN ASM_REWRITE_TAC [])

  let HJT_SUBST_FIXED ← prove
   r"!u M rho a. (!i. i < M ==> rho i <= u) /\ (!i. M <= i ==> rho i = 0)
      ==> hjt_subst (u+1) M rho a = rho"
   (← do
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [hjt_subst, FUN_EQ_THM] THEN
      X_GEN_TAC (← q r"i:num") THEN
    COND_CASES_TAC THENL
     [SUBGOAL_THEN (← q r"(rho:num->num) i <= u") ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
      COND_CASES_TAC THENL [ASM_ARITH_TAC, REFL_TAC],
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]))

  let HJT_GEN_ALMOST_MONO ← prove
   r"!chi:(num->num)->num.
   !t Ns M l0 p a.
    1 <= t /\ hjt_line t M l0 /\ a < t /\
    (!x a a'. (!i. i < Ns ==> x i <= t + 1) /\ (!i. Ns <= i ==> x i = 0) /\
              a < t /\ a' < t
              ==> chi(hjt_prod Ns x (hjt_subst t M l0 a)) =
                  chi(hjt_prod Ns x (hjt_subst t M l0 a'))) /\
    (!i. i < Ns ==> p i <= t + 1)
    ==> chi(hjt_subst (t+1) (Ns+M) (hjt_prod Ns p (hjt_lift t M l0)) a) =
        chi(hjt_prod Ns (hjt_subst (t+1) Ns p a) (hjt_subst t M l0 0))"
   (← do
    pure (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"hjt_subst (t+1) (Ns+M) (hjt_prod Ns p (hjt_lift t M l0)) a =
      hjt_prod Ns (hjt_subst (t+1) Ns p a) (hjt_subst t M l0 a)") SUBST1_TAC THENL
     [MATCH_MP_TAC HJT_PROD_LIFT_SUBST_LE THEN ASM_REWRITE_TAC [] THEN
      ASM_ARITH_TAC,
      ALL_TAC] THEN
    FIRST_X_ASSUM (fun th => tactic_of do
      let bd := (strip_forall (concl th)).2
      if is_forall (concl th) && is_imp bd &&
         (match dest_imp bd with
          | .ok (ant, _) => (conjuncts ant).length >= 4 | .error _ => false)
      then pure (MATCH_MP_TAC th) else pure NO_TAC) THEN
    REWRITE_TAC [hjt_subst] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
      COND_CASES_TAC THENL [ASM_ARITH_TAC, ASM_SIMP_TAC []],
      X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN
      COND_CASES_TAC THENL [ASM_ARITH_TAC, REFL_TAC],
      ASM_REWRITE_TAC [],
      ASM_ARITH_TAC]))

  let HJT_PROD_LINE ← prove
   r"!t Ns M l0 p.
    hjt_line t M l0 /\ (!i. i < Ns ==> p i <= t + 1)
    ==> hjt_line (t+1) (Ns+M) (hjt_prod Ns p (hjt_lift t M l0))"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [hjt_line] THEN
    DISCH_THEN (CONJUNCTS_THEN2
      (CONJUNCTS_THEN2 (LABEL_TAC "l0b") (X_CHOOSE_THEN
        (← q r"iw:num") STRIP_ASSUME_TAC))
      ASSUME_TAC) THEN
    REWRITE_TAC [hjt_line, hjt_prod, hjt_lift] THEN CONJ_TAC THENL
     [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN COND_CASES_TAC THENL
       [ASM_SIMP_TAC [],
        SUBGOAL_THEN (← q r"i - Ns < M:num") ASSUME_TAC THENL
          [ASM_ARITH_TAC, ALL_TAC] THEN
        ASM_REWRITE_TAC [] THEN COND_CASES_TAC THENL [ARITH_TAC, ALL_TAC] THEN
        REMOVE_THEN "l0b" (MP_TAC o SPEC (← q r"i - Ns:num")) THEN
        ASM_REWRITE_TAC [] THEN ARITH_TAC],
      EXISTS_TAC (← q r"Ns + iw:num") THEN
      SUBGOAL_THEN (← q r"~(Ns + iw < Ns:num)") ASSUME_TAC THENL
        [ARITH_TAC, ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"(Ns + iw) - Ns = iw:num") SUBST1_TAC THENL
        [ARITH_TAC, ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC]))

  let HJT_FIXED_LINE_MONO ← prove
   r"!chi:(num->num)->num.
   !t Ns M l0 sig.
    hjt_line (t+1) Ns sig /\ hjt_line t M l0 /\
    (!a. a < t + 1
         ==> chi (hjt_prod Ns (hjt_subst (t+1) Ns sig a)
                    (hjt_subst t M l0 0)) =
             chi (hjt_prod Ns (hjt_subst (t+1) Ns sig 0) (hjt_subst t M l0 0)))
    ==> hjt_line (t+1) (Ns+M) (hjt_prod Ns sig (hjt_subst t M l0 0)) /\
        hjt_mono (t+1) (Ns+M) chi (hjt_prod Ns sig (hjt_subst t M l0 0))"
   (← do
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"(!i. i < M ==> hjt_subst t M l0 0 i <= t) /\
                  (!i. M <= i ==> hjt_subst t M l0 0 i = 0)")
                  STRIP_ASSUME_TAC THENL
     [REWRITE_TAC [hjt_subst] THEN CONJ_TAC THEN X_GEN_TAC (← q r"i:num") THEN
       DISCH_TAC THENL
       [ASM_REWRITE_TAC [] THEN COND_CASES_TAC THENL
         [ARITH_TAC,
          UNDISCH_TAC (← q r"hjt_line t M l0") THEN REWRITE_TAC [hjt_line] THEN
            STRIP_TAC THEN
          FIRST_X_ASSUM (MP_TAC o SPEC (← q r"i:num") o
            check (fun th => is_forall (concl th))) THEN ASM_REWRITE_TAC []],
        SUBGOAL_THEN (← q r"~(i < M:num)") (fun th => REWRITE_TAC [th]) THEN
          ASM_ARITH_TAC],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!a. hjt_subst (t+1) (Ns+M) (hjt_prod Ns sig (hjt_subst t M l0 0)) a =
          hjt_prod Ns (hjt_subst (t+1) Ns sig a) (hjt_subst t M l0 0)")
          ASSUME_TAC THENL
     [GEN_TAC THEN REWRITE_TAC [HJT_SUBST_PROD] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC HJT_SUBST_FIXED THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [hjt_line, hjt_prod] THEN CONJ_TAC THENL
       [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN COND_CASES_TAC THENL
         [UNDISCH_TAC (← q r"hjt_line (t + 1) Ns sig") THEN REWRITE_TAC [hjt_line] THEN
          STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
          -- `check (fun th -> concl th = `..`)`, the quotation parsed at
          -- each call of the test, as in OCaml.
          FIRST_X_ASSUM (fun th => tactic_of do
            let t ← q r"!i. i < M ==>
              hjt_subst t M l0 0 i <= t"
            pure (MP_TAC (← SPEC (← q r"i - Ns:num")
              (← liftExcept (check (fun th => concl th == t) th))))) THEN
          ANTS_TAC THENL [ASM_ARITH_TAC, ARITH_TAC]],
        UNDISCH_TAC (← q r"hjt_line (t + 1) Ns sig") THEN REWRITE_TAC [hjt_line] THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
          (X_CHOOSE_THEN (← q r"iw:num") STRIP_ASSUME_TAC)) THEN
        EXISTS_TAC (← q r"iw:num") THEN
        SUBGOAL_THEN (← q r"iw < Ns:num") ASSUME_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
        ASM_SIMP_TAC [] THEN ASM_ARITH_TAC],
      REWRITE_TAC [hjt_mono] THEN MAP_EVERY X_GEN_TAC [← q r"a:num", ← q r"a':num"] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (fun th => tactic_of do
        let c := concl th
        let bd := (strip_forall c).2
        let ok ← if is_forall c && is_imp bd then
            match dest_imp bd with
            | .ok (_, cc) =>
              if is_eq cc then do
                let z ← q r"hjt_subst (t+1)
               Ns sig 0"
                pure (can (find_term (fun tm => tm == z)) cc)
              else pure false
            | .error _ => pure false
          else pure false
        if ok then pure (MP_TAC (← SPEC (← q r"a:num") th) THEN
                         MP_TAC (← SPEC (← q r"a':num") th))
        else pure NO_TAC) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC]))

  -- @@RETURN BEGIN
  return { hjt_subst, hjt_line, hjt_mono, hales_jewett_template, HJT_1, HJT_MONO_N,
           hjt_prod, HJT_SUBST_PROD, hjt_almost_mono, hjt_focused, HJT_ALMOST_MONO_LT,
           HJT_COLLAPSE, hjt_lift, NSUM_NUMSEG_LT_SHIFT, HJT_NSUM_DIGIT_SPLIT,
           HJT_DIGIT_RECOVER, HJT_RECOLOUR, HJT_LIFT_SUBST_LE, HJT_PROD_LIFT_SUBST_LE,
           HJT_SUBST_FIXED, HJT_GEN_ALMOST_MONO, HJT_PROD_LINE, HJT_FIXED_LINE_MONO }
  -- @@RETURN END


/- ------------------------------------------------------------------------- -/
/- Colour focusing: HJT_KEY.  (szemeredi.ml 1200-1543)                       -/
/- ------------------------------------------------------------------------- -/

structure HJTKey where
  -- @@FIELDS
  HJT_KEY : thm
  deriving Inhabited

@[nospecialize]
def setupHJTKey [HolBase] (D : SzemerediDeps) (BTemplates : Templates) :
    ExceptT String IO HJTKey := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, .. } := D
  let { ARITH, EXP_EQ_0, FUN_EQ_THM, LE_0, LE_REFL, LT, .. } := D.core1
  let { HJT_FIXED_LINE_MONO, HJT_GEN_ALMOST_MONO, HJT_PROD_LIFT_SUBST_LE,
        HJT_PROD_LINE, HJT_RECOLOUR, HJT_SUBST_FIXED, HJT_SUBST_PROD,
        hales_jewett_template, hjt_almost_mono, hjt_focused, hjt_line, hjt_mono,
        hjt_prod, hjt_subst, .. } := BTemplates
  -- @@SCOPE END
  -- `let bd = snd(strip_forall c) in is_imp bd && P (fst(dest_imp bd))`
  let antOf : term → Option term := fun c =>
    match dest_imp (strip_forall c).2 with
    | .ok (a, _) => some a | .error _ => none
  let headIs : term → term → Bool := fun h t => is_comb t && (strip_comb t).1 == h

  let HJT_KEY ← prove
   r"!t r.
  1 <= t /\ (!r'. 1 <= r' ==> ?N. hales_jewett_template t r' N)
  ==> !s. ?N. !chi:(num->num)->num. (!x. chi x < r)
              ==> (?tw. hjt_line (t+1) N tw /\ hjt_mono (t+1) N chi tw) \/
                  (?Lf cf focus. hjt_focused chi t N Lf cf focus s)"
   (← do
    -- right to left: the ARITH_RULEs from the last to the first
    let a6 ← ARITH_RULE (← q r"n < SUC s <=> n < s \/ n = s")
    let a5 ← ARITH_RULE (← q r"~(s=0) ==> 0 < s")
    let a4 ← ARITH_RULE (← q r"i < 1 <=> i = 0")
    let a3 ← ARITH_RULE (← q r"i < 1 <=> i = 0")
    let a2 ← ARITH_RULE (← q r"i < 1 <=> i = 0")
    let a1 ← ARITH_RULE (← q r"~(n = 0) ==> 1 <= n")
    pure ((REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
     [EXISTS_TAC (← q r"1") THEN REPEAT STRIP_TAC THEN DISJ2_TAC THEN
      MAP_EVERY EXISTS_TAC
       [← q r"(\i j:num. 0):num->num->num", ← q r"(\i:num. 0):num->num",
        ← q r"(\j:num. 0):num->num"] THEN
      REWRITE_TAC [hjt_focused, LT],
      ALL_TAC]) THEN
  (ASM_CASES_TAC (← q r"r = 0") THENL
     [EXISTS_TAC (← q r"1") THEN ASM_REWRITE_TAC [] THEN GEN_TAC THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"(\i:num. 0):num->num")) THEN ARITH_TAC,
      ALL_TAC]) THEN
  (SUBGOAL_THEN (← q r"1 <= r") ASSUME_TAC THENL [ASM_ARITH_TAC, ALL_TAC]) THEN
  (FIRST_X_ASSUM (X_CHOOSE_TAC (← q r"Ns:num"))) THEN
  (SUBGOAL_THEN (← q r"?M. hales_jewett_template t (r EXP ((t+2) EXP Ns)) M")
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM (fun th => tactic_of do
        let ok ← if is_forall (concl th) then
            match antOf (concl th) with
            | some a => do let z ← q r"1 <= r'"; pure (a == z)
            | none => pure false
          else pure false
        if ok then pure (MATCH_MP_TAC th) else pure NO_TAC) THEN
      MATCH_MP_TAC a1 THEN
      REWRITE_TAC [EXP_EQ_0] THEN ASM_ARITH_TAC,
      ALL_TAC]) THEN
  (EXISTS_TAC (← q r"Ns + M:num") THEN X_GEN_TAC (← q r"chi:(num->num)->num") THEN
    DISCH_TAC) THEN
  (MP_TAC (← ISPECL [← q r"chi:(num->num)->num", ← q r"t:num", ← q r"Ns:num", ← q r"M:num", ← q r"r:num"]
     HJT_RECOLOUR)) THEN
  (ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"psi:(num->num)->num") STRIP_ASSUME_TAC)) THEN
  (FIRST_X_ASSUM (fun th => tactic_of do
     let h ← q r"hales_jewett_template"
     if headIs h (concl th) then
       pure (MP_TAC (← REWRITE_RULE [hales_jewett_template] th)) else pure NO_TAC)) THEN
  (DISCH_THEN (MP_TAC o SPEC (← q r"psi:(num->num)->num"))) THEN
  (ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"l0:num->num") STRIP_ASSUME_TAC)) THEN
  (FIRST_X_ASSUM (fun th => tactic_of do
     let ok ← if is_forall (concl th) then
         match antOf (concl th) with
         | some ant => do let h ← q r"hjt_mono"; pure (headIs h ant)
         | none => pure false
       else pure false
     if ok then pure (MP_TAC (← SPEC (← q r"l0:num->num") th)) else pure NO_TAC)) THEN
  (ASM_REWRITE_TAC [] THEN DISCH_TAC) THEN
  (FIRST_X_ASSUM (fun th => tactic_of do
     if is_forall (concl th) && (match antOf (concl th) with
                                 | some ant => is_forall ant | none => false)
     then pure (MP_TAC (← SPEC (← q r"\x. (chi:(num->num)->num)(hjt_prod Ns x (hjt_subst
       t M l0 0))") th))
     else pure NO_TAC)) THEN
  (BETA_TAC) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC]) THEN
  (DISCH_THEN DISJ_CASES_TAC) THENL
  [ ((FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"sg:num->num") STRIP_ASSUME_TAC)) THEN
  (DISJ1_TAC THEN EXISTS_TAC (← q r"hjt_prod Ns sg (hjt_subst t M l0 0)")) THEN
  (SUBGOAL_THEN (← q r"!i. hjt_subst t M l0 0 i <= t") ASSUME_TAC THENL
     [X_GEN_TAC (← q r"i:num") THEN REWRITE_TAC [hjt_subst] THEN
      COND_CASES_TAC THENL
       [COND_CASES_TAC THENL
         [ARITH_TAC,
          UNDISCH_TAC (← q r"hjt_line t M l0") THEN REWRITE_TAC [hjt_line] THEN
          STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []],
        ARITH_TAC],
      ALL_TAC]) THEN
  (SUBGOAL_THEN (← q r"!i. M <= i ==> hjt_subst t M l0 0 i = 0") ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC [hjt_subst] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC, ALL_TAC]) THEN
  (SUBGOAL_THEN
     (← q r"!a. hjt_subst (t+1) (Ns+M) (hjt_prod Ns sg (hjt_subst t M l0 0)) a =
          hjt_prod Ns (hjt_subst (t+1) Ns sg a) (hjt_subst t M l0 0)")
          ASSUME_TAC THENL
     [GEN_TAC THEN REWRITE_TAC [HJT_SUBST_PROD] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC HJT_SUBST_FIXED THEN ASM_REWRITE_TAC [] THEN
      X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN ASM_REWRITE_TAC [],
      ALL_TAC]) THEN
  (CONJ_TAC THENL
     [REWRITE_TAC [hjt_line, hjt_prod] THEN CONJ_TAC THENL
       [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN COND_CASES_TAC THENL
         [UNDISCH_TAC (← q r"hjt_line (t + 1) Ns sg") THEN REWRITE_TAC [hjt_line] THEN
          STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
          FIRST_X_ASSUM (fun th => tactic_of do
            let z ← q r"!i. hjt_subst t M l0 0 i <= t"
            if concl th == z then
              pure (MP_TAC (← SPEC (← q r"i - Ns:num") th)) else pure NO_TAC) THEN ARITH_TAC],
        UNDISCH_TAC (← q r"hjt_line (t + 1) Ns sg") THEN REWRITE_TAC [hjt_line] THEN
        STRIP_TAC THEN EXISTS_TAC (← q r"i:num") THEN ASM_SIMP_TAC [] THEN
          ASM_ARITH_TAC],
      REWRITE_TAC [hjt_mono] THEN MAP_EVERY X_GEN_TAC [← q r"a:num", ← q r"a':num"] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC
       (← q r"hjt_mono (t + 1) Ns
          (\x. chi (hjt_prod Ns x (hjt_subst t M l0 0))) sg") THEN
      REWRITE_TAC [hjt_mono] THEN BETA_TAC THEN
      DISCH_THEN (MP_TAC o SPECL [← q r"a:num", ← q r"a':num"]) THEN ASM_REWRITE_TAC []])),
    ((FIRST_X_ASSUM (fun th => tactic_of do
     if is_exists (concl th) then
       pure (X_CHOOSE_THEN (← q r"Lf:num->num->num")
        (X_CHOOSE_THEN (← q r"cf:num->num")
          (X_CHOOSE_THEN (← q r"focus:num->num") STRIP_ASSUME_TAC)) th)
     else pure NO_TAC)) THEN
  (FIRST_X_ASSUM (MP_TAC o REWRITE_RULE [hjt_focused]) THEN STRIP_TAC) THEN
  (ASM_CASES_TAC (← q r"s = 0")) THENL
  [ ((ASM_REWRITE_TAC [ARITH] THEN DISJ2_TAC) THEN
  (MAP_EVERY EXISTS_TAC
     [← q r"\i:num. hjt_prod Ns (\j:num. 0) (hjt_lift t M l0)",
      ← q r"\i:num. (chi:(num->num)->num)(hjt_prod Ns
                                       (\j:num. 0)(hjt_subst t M l0 0))",
      ← q r"hjt_prod Ns (\j:num. 0)(hjt_subst t M l0 t)"]) THEN
  (SUBGOAL_THEN (← q r"!a. hjt_subst (t+1) Ns (\j:num. 0) a = (\j:num. 0)")
    ASSUME_TAC THENL
     [GEN_TAC THEN REWRITE_TAC [hjt_subst, FUN_EQ_THM] THEN X_GEN_TAC (← q r"i:num") THEN
      COND_CASES_TAC THEN REWRITE_TAC [] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC,
      ALL_TAC]) THEN
  (REWRITE_TAC [hjt_focused] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC [a2] THEN GEN_TAC THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [hjt_almost_mono] THEN CONJ_TAC THENL
       [MATCH_MP_TAC HJT_PROD_LINE THEN ASM_REWRITE_TAC [] THEN
        REPEAT STRIP_TAC THEN ARITH_TAC,
        X_GEN_TAC (← q r"a:num") THEN DISCH_TAC THEN
        MP_TAC (← ISPECL [← q r"chi:(num->num)->num", ← q r"t:num", ← q r"Ns:num", ← q r"M:num",
                          ← q r"l0:num->num", ← q r"(\j:num. 0):num->num",
                          ← q r"a:num"] HJT_GEN_ALMOST_MONO) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC [] THEN REWRITE_TAC [LE_0] THEN
          REPEAT STRIP_TAC THEN ARITH_TAC,
          ALL_TAC] THEN
        ASM_REWRITE_TAC []],
      REWRITE_TAC [a3] THEN MESON_TAC [],
      REWRITE_TAC [a4] THEN GEN_TAC THEN
      DISCH_THEN SUBST1_TAC THEN
      MP_TAC (← ISPECL [← q r"t:num", ← q r"M:num", ← q r"l0:num->num", ← q r"Ns:num",
                        ← q r"(\j:num. 0):num->num",
                        ← q r"t:num"] HJT_PROD_LIFT_SUBST_LE) THEN
      ASM_REWRITE_TAC [LE_REFL] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC []])),
    ((SUBGOAL_THEN (← q r"hjt_line (t+1) Ns (Lf(0:num))") MP_TAC THENL
     [UNDISCH_TAC (← q r"forall i:num. i < s ==> hjt_almost_mono
        (\x. chi (hjt_prod Ns x (hjt_subst t M l0 0))) t Ns (Lf i) (cf i)") THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"0")) THEN
      ASM_SIMP_TAC [a5, hjt_almost_mono] THEN
      MESON_TAC [],
      ALL_TAC]) THEN
  (DISCH_THEN (fun th => tactic_of do
      pure (STRIP_ASSUME_TAC (← REWRITE_RULE [hjt_line] th)))) THEN
  (SUBGOAL_THEN (← q r"hjt_subst (t+1) Ns (Lf(0:num)) t = focus") ASSUME_TAC THENL
     [FIRST_X_ASSUM (fun th => tactic_of do
        let z ← q r"!i:num. i < s ==> hjt_subst (t + 1) Ns (Lf i) t = focus"
        if concl th == z then pure (MATCH_MP_TAC th) else pure NO_TAC) THEN ASM_ARITH_TAC,
      ALL_TAC]) THEN
  (SUBGOAL_THEN
     (← q r"(!i. i < Ns ==> (focus:num->num) i <= t) /\ (!i. Ns <= i ==> focus i = 0)")
     STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC (← q r"hjt_subst (t+1) Ns (Lf(0:num)) t = focus") THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [hjt_subst] THEN
      CONJ_TAC THEN X_GEN_TAC (← q r"k:num") THEN DISCH_TAC THENL
       [SUBGOAL_THEN (← q r"k < Ns:num") (fun th => REWRITE_TAC [th]) THENL
         [ASM_REWRITE_TAC [], ALL_TAC] THEN
        COND_CASES_TAC THENL [ARITH_TAC, ALL_TAC] THEN
        FIRST_X_ASSUM (fun th => tactic_of do
          let z ← q r"!i:num. i < Ns ==> Lf 0 i <= t + 1"
          pure (MP_TAC (← SPEC (← q r"k:num")
            (← liftExcept (check (fun th => concl th == z) th))))) THEN
        ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC,
        SUBGOAL_THEN (← q r"~(k < Ns:num)") (fun th => REWRITE_TAC [th]) THEN
          ASM_ARITH_TAC],
      ALL_TAC]) THEN
  (SUBGOAL_THEN (← q r"!a. hjt_subst (t+1) Ns focus a = focus") ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC HJT_SUBST_FIXED THEN ASM_REWRITE_TAC [],
      ALL_TAC]) THEN
  (ASM_CASES_TAC
     (← q r"?i:num. i < s /\
              cf i = (chi:(num->num)->num)(hjt_prod Ns focus (hjt_subst t M
       l0 0))")) THENL
  [ ((FIRST_X_ASSUM (fun th => tactic_of do
     let ok ← if is_exists (concl th) then
         match dest_exists (concl th) with
         | .ok (v, _) => do let z ← q r"i:num"; pure (v == z)
         | .error _ => pure false
       else pure false
     pure (X_CHOOSE_THEN (← q r"i0:num") STRIP_ASSUME_TAC
       (← liftExcept (check (fun _ => ok) th))))) THEN
  (SUBGOAL_THEN (← q r"hjt_subst (t+1) Ns (Lf(i0:num)) t = focus") ASSUME_TAC THENL
     [FIRST_X_ASSUM (fun th => tactic_of do
        let z ← q r"!i:num. i < s ==> hjt_subst (t + 1) Ns (Lf i) t = focus"
        if concl th == z then pure (MATCH_MP_TAC th) else pure NO_TAC) THEN ASM_REWRITE_TAC [],
      ALL_TAC]) THEN
  (SUBGOAL_THEN
     (← q r"hjt_almost_mono (\x. chi (hjt_prod Ns x (hjt_subst t M l0 0))) t Ns
       (Lf(i0:num)) (cf i0)")
     MP_TAC THENL
     [FIRST_X_ASSUM (fun th => tactic_of do
        let z ← q r"forall i:num. i < s ==> hjt_almost_mono
            (\x. chi (hjt_prod Ns x (hjt_subst t M l0 0))) t Ns (Lf i) (cf i)"
        if concl th == z then pure (MATCH_MP_TAC th) else pure NO_TAC) THEN ASM_REWRITE_TAC [],
      ALL_TAC]) THEN
  (REWRITE_TAC [hjt_almost_mono] THEN BETA_TAC THEN STRIP_TAC) THEN
  (SUBGOAL_THEN
     (← q r"!a. a <= t ==>
          chi (hjt_prod Ns (hjt_subst (t + 1) Ns (Lf(i0:num)) a)
                 (hjt_subst t M l0 0)) =
          (cf:num->num) i0") ASSUME_TAC THENL
     [X_GEN_TAC (← q r"a:num") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"a:num < t") THENL
       [FIRST_X_ASSUM (fun th => tactic_of do
          let ok ← if is_forall (concl th) then
              match antOf (concl th) with
              | some a => do let z ← q r"a:num < t"; pure (a == z)
              | none => pure false
            else pure false
          if ok then pure (MATCH_MP_TAC th) else pure NO_TAC) THEN ASM_REWRITE_TAC [],
        SUBGOAL_THEN (← q r"a:num = t") SUBST1_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
        ASM_REWRITE_TAC [] THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM ACCEPT_TAC],
      ALL_TAC]) THEN
  (DISJ1_TAC THEN
   EXISTS_TAC (← q r"hjt_prod Ns (Lf(i0:num)) (hjt_subst t M l0 0)")) THEN
  (REWRITE_TAC [← GSYM hjt_line] THEN
    MATCH_MP_TAC (← ISPEC (← q r"chi:(num->num)->num") HJT_FIXED_LINE_MONO) THEN
    ASM_REWRITE_TAC [] THEN
    X_GEN_TAC (← q r"a:num") THEN DISCH_TAC THEN
    SUBGOAL_THEN
     (← q r"chi (hjt_prod Ns (hjt_subst (t + 1) Ns (Lf(i0:num)) a)
             (hjt_subst t M l0 0)) =
      (cf:num->num) i0 /\
      chi (hjt_prod Ns (hjt_subst (t + 1) Ns (Lf i0) 0)
             (hjt_subst t M l0 0)) = cf i0")
     (fun th => tactic_of do pure (REWRITE_TAC [← CONJUNCT1 th, ← CONJUNCT2 th])) THEN
    CONJ_TAC THEN FIRST_X_ASSUM (fun th => tactic_of do
      let ok ← if is_forall (concl th) then
          match antOf (concl th) with
          | some a => do let z ← q r"a:num <= t"; pure (a == z)
          | none => pure false
        else pure false
      if ok then pure (MATCH_MP_TAC th) else pure NO_TAC) THEN ASM_ARITH_TAC)),
    ((DISJ2_TAC) THEN
  (MAP_EVERY EXISTS_TAC
     [← q r"\i:num. hjt_prod Ns (if i < s then Lf i else focus) (hjt_lift t M l0)",
      ← q r"\i:num. if i < s then cf i
               else (chi:(num->num)->num)(hjt_prod Ns focus
                                            (hjt_subst t M l0 0))",
      ← q r"hjt_prod Ns focus (hjt_subst t M l0 t)"]) THEN
  (SUBGOAL_THEN
     (← q r"!p k. k < Ns ==> (if p:num < s then Lf p else focus) (k:num) <= t + 1")
     ASSUME_TAC THENL
     [GEN_TAC THEN COND_CASES_TAC THENL
       [X_GEN_TAC (← q r"k:num") THEN DISCH_TAC THEN
        UNDISCH_TAC (← q r"forall i:num. i < s ==> hjt_almost_mono
          (\x. chi (hjt_prod Ns x (hjt_subst t M l0 0))) t Ns (Lf i) (cf i)") THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"p:num")) THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [hjt_almost_mono, hjt_line] THEN STRIP_TAC THEN
        ASM_SIMP_TAC [],
        X_GEN_TAC (← q r"k:num") THEN DISCH_TAC THEN
        FIRST_X_ASSUM (fun th => tactic_of do
          let z ← q r"!i:num. i < Ns ==>
            (focus:num->num) i <= t"
          pure (MP_TAC (← SPEC (← q r"k:num")
            (← liftExcept (check (fun th => concl th == z) th))))) THEN
        ASM_REWRITE_TAC [] THEN ARITH_TAC],
      ALL_TAC]) THEN
  (SUBGOAL_THEN
     (← q r"!p. hjt_subst (t+1) (Ns+M)
            (hjt_prod Ns (if p:num < s then Lf p else focus)
               (hjt_lift t M l0)) t =
          hjt_prod Ns (hjt_subst (t+1) Ns (if p:num < s then Lf p else focus) t)
                     (hjt_subst t M l0 t)") ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC HJT_PROD_LIFT_SUBST_LE THEN
      ASM_REWRITE_TAC [LE_REFL],
      ALL_TAC]) THEN
  (SUBGOAL_THEN
     (← q r"!p. p < SUC s ==> hjt_subst (t+1) Ns (if p:num < s then Lf p else
       focus) t = focus")
     ASSUME_TAC THENL
     [X_GEN_TAC (← q r"p:num") THEN DISCH_TAC THEN COND_CASES_TAC THENL
       [FIRST_X_ASSUM (fun th => tactic_of do
          let z ← q r"!i:num. i < s ==> hjt_subst (t + 1) Ns (Lf i) t = focus"
          if concl th == z then pure (MATCH_MP_TAC th) else pure NO_TAC) THEN ASM_REWRITE_TAC [],
        ASM_REWRITE_TAC []],
      ALL_TAC]) THEN
  (REWRITE_TAC [hjt_focused] THEN REPEAT CONJ_TAC THENL
    [ ((X_GEN_TAC (← q r"p:num") THEN DISCH_TAC THEN REWRITE_TAC [hjt_almost_mono] THEN
    BETA_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HJT_PROD_LINE THEN ASM_REWRITE_TAC [],
      ALL_TAC]) THEN
  (X_GEN_TAC (← q r"a:num") THEN DISCH_TAC) THEN
  (MP_TAC (← ISPECL [← q r"chi:(num->num)->num", ← q r"t:num", ← q r"Ns:num", ← q r"M:num",
                     ← q r"l0:num->num",
                     ← q r"if p:num < s then Lf p else (focus:num->num)",
                     ← q r"a:num"] HJT_GEN_ALMOST_MONO) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM (fun th => tactic_of do
          let c := concl th
          let ok ← if is_forall c then
              match dest_imp (strip_forall c).2 with
              | .ok (_, cc) =>
                if is_eq cc then do
                  let z ← q r"hjt_prod Ns x (hjt_subst t
                M l0 a)"
                  pure (can (find_term (fun tm => tm == z)) cc)
                else pure false
              | .error _ => pure false
            else pure false
          if ok then pure (MATCH_ACCEPT_TAC th) else pure NO_TAC),
        REPEAT STRIP_TAC THEN ASM_SIMP_TAC []],
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC) THEN
  (COND_CASES_TAC THENL
     [REWRITE_TAC [] THEN
      UNDISCH_TAC (← q r"forall i:num. i < s ==> hjt_almost_mono
        (\x. chi (hjt_prod Ns x (hjt_subst t M l0 0))) t Ns (Lf i) (cf i)") THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"p:num")) THEN
      ASM_REWRITE_TAC [hjt_almost_mono] THEN
      BETA_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC [],
      REWRITE_TAC [] THEN
      FIRST_X_ASSUM (fun th => tactic_of do
        let z ← q r"forall a. hjt_subst (t + 1) Ns focus a = focus"
        if concl th == z then pure (REWRITE_TAC [th]) else pure NO_TAC)])),
      ((MAP_EVERY X_GEN_TAC [← q r"p:num", ← q r"q:num"] THEN
    REWRITE_TAC [a6] THEN STRIP_TAC THENL
     [FIRST_X_ASSUM (fun th => tactic_of do
        let ok ← if is_forall (concl th) then
            match dest_imp (strip_forall (concl th)).2 with
            | .ok (_, b) => do let z ← q r"i:num = j"; pure (b == z)
            | .error _ => pure false
          else pure false
        if ok then pure (MATCH_MP_TAC th) else pure NO_TAC) THEN
      REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM ACCEPT_TAC, FIRST_X_ASSUM ACCEPT_TAC,
        FIRST_X_ASSUM (MP_TAC o
          check (fun th => is_eq (concl th) &&
            (match lhs (concl th) with | .ok l => HolCore.Classic.is_cond l | .error _ => false))) THEN
        ASM_SIMP_TAC []],
      SUBGOAL_THEN (← q r"~(q < s:num)") ASSUME_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o
        check (fun th => is_eq (concl th) &&
          (match lhs (concl th) with | .ok l => HolCore.Classic.is_cond l | .error _ => false))) THEN
      ASM_SIMP_TAC [] THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"?i. i < s /\
        (cf:num->num) i = chi (hjt_prod Ns focus (hjt_subst t M l0 0))")
       (fun th => ASM_MESON_TAC [th]) THEN
      EXISTS_TAC (← q r"p:num") THEN ASM_REWRITE_TAC [],
      SUBGOAL_THEN (← q r"~(p < s:num)") ASSUME_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o
        check (fun th => is_eq (concl th) &&
          (match lhs (concl th) with | .ok l => HolCore.Classic.is_cond l | .error _ => false))) THEN
      ASM_SIMP_TAC [] THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"?i. i < s /\
        (cf:num->num) i = chi (hjt_prod Ns focus (hjt_subst t M l0 0))")
       (fun th => ASM_MESON_TAC [th]) THEN
      EXISTS_TAC (← q r"q:num") THEN ASM_REWRITE_TAC [] THEN
      CONV_TAC SYM_CONV THEN ASM_REWRITE_TAC [],
      ASM_REWRITE_TAC []])),
      ((X_GEN_TAC (← q r"p:num") THEN DISCH_TAC) THEN
  (FIRST_X_ASSUM (fun th => tactic_of do
      let c := concl th
      let b := (strip_forall c).2
      let ok ← if is_forall c then
          match dest_forall c with
          | .ok (v, _) => do
            let pv ← q r"p:num"
            if v == pv && is_eq b then do
              let z ← q r"hjt_lift t M l0"
              pure (match lhs b with
                    | .ok l => can (find_term (fun tm => tm == z)) l
                    | .error _ => false)
            else pure false
          | .error _ => pure false
        else pure false
      if ok then pure (REWRITE_TAC [← SPEC (← q r"p:num") th]) else pure NO_TAC)) THEN
  (SUBGOAL_THEN
     (← q r"hjt_subst (t+1) Ns (if p:num < s then Lf p else focus) t = focus")
     SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
      REFL_TAC])) ])) ]) ]) ]))

  -- @@RETURN BEGIN
  return { HJT_KEY }
  -- @@RETURN END


/- ------------------------------------------------------------------------- -/
/- The Hales-Jewett theorem for templates; lines of words.                   -/
/- (szemeredi.ml 1545-1614)                                                  -/
/- ------------------------------------------------------------------------- -/

structure HJTemplate where
  -- @@FIELDS
  HJT_STEP : thm
  HALES_JEWETT_TEMPLATE : thm
  HJ_FINITE_INDEX : thm
  HJ_LINE_POINT_TEMPLATE : thm
  deriving Inhabited

@[nospecialize]
def setupHJTemplate [HolBase] (D : SzemerediDeps) (BWords : Words) (BLines : Lines) (BTemplates : Templates) (BHJTKey : HJTKey) :
    ExceptT String IO HJTemplate := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, .. } := D
  let { ADD1, ARITH, CARD_LE_INJ, CARD_NUMSEG_LT, FINITE_NUMSEG_LT, FORALL_IN_IMAGE,
        FUN_EQ_THM, IN_ELIM_THM, LE_LT, LE_REFL, LT_REFL, .. } := D.core1
  let { SUBSET, SUB_REFL, .. } := D.core2
  let { hj_subst, .. } := BWords
  let { hj_line_point, .. } := BLines
  let { HJT_1, HJT_COLLAPSE, hales_jewett_template, hjt_subst, .. } := BTemplates
  let { HJT_KEY, .. } := BHJTKey
  -- @@SCOPE END

  let HJT_STEP ← prove
   r"!t. 1 <= t /\ (!r'. 1 <= r' ==> ?N. hales_jewett_template t r' N)
       ==> !r. 1 <= r ==> ?N. hales_jewett_template (t + 1) r N"
   (← do
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"t:num", ← q r"r:num"] HJT_KEY) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"r:num")) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"N:num")) THEN
    EXISTS_TAC (← q r"N:num") THEN REWRITE_TAC [hales_jewett_template] THEN
    X_GEN_TAC (← q r"chi:(num->num)->num") THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"chi:(num->num)->num")) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (DISJ_CASES_THEN2 (fun th => ACCEPT_TAC th) MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"Lf:num->num->num")
     (X_CHOOSE_THEN (← q r"cf:num->num")
       (X_CHOOSE_THEN (← q r"focus:num->num") ASSUME_TAC))) THEN
    MATCH_MP_TAC (← ISPECL [← q r"chi:(num->num)->num", ← q r"t:num", ← q r"r:num", ← q r"N:num",
                            ← q r"Lf:num->num->num", ← q r"cf:num->num", ← q r"focus:num->num"]
     HJT_COLLAPSE) THEN ASM_REWRITE_TAC []))

  let HALES_JEWETT_TEMPLATE ← prove
   r"!t r. 1 <= t /\ 1 <= r ==> ?N. hales_jewett_template t r N"
   (← do
    pure (INDUCT_TAC THEN REPEAT STRIP_TAC THENL
     [ASM_ARITH_TAC,
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"t = 0") THENL
     [ASM_REWRITE_TAC [ARITH] THEN ASM_MESON_TAC [HJT_1],
      REWRITE_TAC [ADD1] THEN
      MP_TAC (← ISPEC (← q r"t:num") HJT_STEP) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [ASM_ARITH_TAC,
          X_GEN_TAC (← q r"r':num") THEN DISCH_TAC THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC],
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC []]]))

  /- Hales-Jewett for lines of words and finite colour sets. -/

  let HJ_FINITE_INDEX ← prove
   r"!s:A->bool. FINITE s
               ==> ?f. (!x. x IN s ==> f x < CARD s) /\
                       (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)"
   (← do
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"s:A->bool", ← q r"{i:num | i < CARD(s:A->bool)}"]
      CARD_LE_INJ) THEN
    ASM_REWRITE_TAC [FINITE_NUMSEG_LT, CARD_NUMSEG_LT, LE_REFL] THEN
    REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM]))

  let HJ_LINE_POINT_TEMPLATE ← prove
   r"!k n tw a. 1 <= k /\ (!i. i < n ==> tw i <= k)
              ==> hj_line_point k (\i. if i < n then tw i else 0) a =
                  hjt_subst k n tw a"
   (← do
    pure (REPEAT STRIP_TAC THEN
    REWRITE_TAC [hj_line_point, hj_subst, hjt_subst, FUN_EQ_THM] THEN
    X_GEN_TAC (← q r"i:num") THEN ASM_CASES_TAC (← q r"i:num < n") THEN
    ASM_REWRITE_TAC [] THENL
     [ASM_CASES_TAC (← q r"(tw:num->num) i = k") THEN
      ASM_REWRITE_TAC [LT_REFL, SUB_REFL] THEN
      SUBGOAL_THEN (← q r"(tw:num->num) i < k") (fun th => REWRITE_TAC [th]) THEN
      ASM_MESON_TAC [LE_LT],
      ASM_SIMP_TAC [← ARITH_RULE (← q r"1 <= k ==> 0 < k")]]))

  -- @@RETURN BEGIN
  return { HJT_STEP, HALES_JEWETT_TEMPLATE, HJ_FINITE_INDEX, HJ_LINE_POINT_TEMPLATE }
  -- @@RETURN END


/- ------------------------------------------------------------------------- -/
/- Hales-Jewett for lines of words and finite colour sets; multidimensional  -/
/- Hales-Jewett.  (szemeredi.ml 1615-1840)                                   -/
/- ------------------------------------------------------------------------- -/

structure HalesJewett where
  -- @@FIELDS
  HALES_JEWETT : thm
  HALES_JEWETT_FINITE : thm
  HJ_SUBST_LINE : thm
  HJ_SUBST_TAKE : thm
  HJ_PATTERN_INDEX : thm
  MULTIDIM_HALES_JEWETT : thm
  deriving Inhabited

@[nospecialize]
def setupHalesJewett [HolBase] (D : SzemerediDeps) (BWords : Words) (BLines : Lines) (BTemplates : Templates) (BHJTemplate : HJTemplate) :
    ExceptT String IO HalesJewett := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, .. } := D
  let { ADD1, ADD_CLAUSES, CARD_EQ_0, FINITE_HAS_SIZE, FUN_EQ_THM, HAS_SIZE,
        HAS_SIZE_FUNSPACE, HAS_SIZE_NUMSEG_LT, IN_ELIM_THM, IN_SING, LE_REFL, LT,
        LT_NZ, MONO_EXISTS, .. } := D.core1
  let { NOT_LT, SUB_0, .. } := D.core2
  let { FINITE_HJ_CUBE, HJ_CUBE_0, HJ_SUBSPACE_0, HJ_SUBST_CUBE, HJ_TAKE_CUBE,
        IN_HJ_CUBE, hj_drop, hj_subspace, hj_subst, hj_take, .. } := BWords
  let { HJ_LINE_POINT_CUBE, HJ_SUBSPACE_JOIN, HJ_SUBST_JOIN, hj_line, hj_line_point, .. } := BLines
  let { HJT_MONO_N, hales_jewett_template, hjt_line, hjt_mono, .. } := BTemplates
  let { HALES_JEWETT_TEMPLATE, HJ_FINITE_INDEX, HJ_LINE_POINT_TEMPLATE, .. } := BHJTemplate
  -- @@SCOPE END

  let HALES_JEWETT ← prove
   r"!k r. 1 <= k /\ 1 <= r
         ==> ?N. !n c. N <= n /\ (!x. c x < r)
                       ==> ?l. hj_line k n l /\
                               !a b. a < k /\ b < k
                                     ==> c(hj_line_point k l a) =
                                         c(hj_line_point k l b)"
   (← do
    -- right to left: the second ARITH_RULE, then the first
    let a2 ← ARITH_RULE (← q r"j < 1 <=> j = 0")
    let a1 ← ARITH_RULE (← q r"t <= k ==> t < k + 1")
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"k:num", ← q r"r:num"] HALES_JEWETT_TEMPLATE) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"N:num")) THEN EXISTS_TAC (← q r"N:num") THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"hales_jewett_template k r n") MP_TAC THENL
     [MATCH_MP_TAC HJT_MONO_N THEN EXISTS_TAC (← q r"N:num") THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    REWRITE_TAC [hales_jewett_template] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"c:(num->num)->num")) THEN
    ASM_REWRITE_TAC [hjt_line, hjt_mono] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"tw:num->num") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"\i. if i < n then (tw:num->num) i else 0") THEN
    ASM_SIMP_TAC [HJ_LINE_POINT_TEMPLATE] THEN
    REWRITE_TAC [hj_line, hj_subspace, IN_HJ_CUBE] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC a1 THEN ASM_SIMP_TAC [],
      SIMP_TAC [← GSYM NOT_LT],
      REWRITE_TAC [a2, ADD_CLAUSES] THEN
      X_GEN_TAC (← q r"j:num") THEN DISCH_THEN SUBST1_TAC THEN
      EXISTS_TAC (← q r"i:num") THEN ASM_REWRITE_TAC [ADD_CLAUSES],
      ASM_REWRITE_TAC []]))

  let HALES_JEWETT_FINITE ← prove
   r"!k (S:A->bool).
        1 <= k /\ FINITE S /\ ~(S = {})
        ==> ?N. !n c. N <= n /\ (!x. x IN hj_cube k n ==> c x IN S)
                      ==> ?l. hj_line k n l /\
                              !a b. a < k /\ b < k
                                    ==> c(hj_line_point k l a) =
                                        c(hj_line_point k l b)"
   (← do
    pure (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (X_CHOOSE_THEN (← q r"f:A->num") STRIP_ASSUME_TAC o
      MATCH_MP HJ_FINITE_INDEX) THEN
    MP_TAC (← SPECL [← q r"k:num", ← q r"CARD(S:A->bool)"] HALES_JEWETT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [← ARITH_RULE (← q r"1 <= n <=> ~(n = 0)")] THEN
      ASM_MESON_TAC [CARD_EQ_0],
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"N:num")) THEN EXISTS_TAC (← q r"N:num") THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL
     [← q r"n:num", ← q r"\x. if x IN hj_cube k n then (f:A->num)((c:(num->num)->A) x)
                    else 0"]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN GEN_TAC THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC [] THEN ASM_MESON_TAC [CARD_EQ_0, LT_NZ],
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"l:num->num") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"a:num", ← q r"b:num"]) THEN
    ASM_SIMP_TAC [HJ_LINE_POINT_CUBE] THEN ASM_MESON_TAC [HJ_LINE_POINT_CUBE]))

  let HJ_SUBST_LINE ← prove
   r"!k n l w. hj_line k n l ==> hj_subst k l w = hj_line_point k l (w 0)"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [hj_line, hj_subspace, IN_HJ_CUBE] THEN
    STRIP_TAC THEN
    REWRITE_TAC [hj_line_point, hj_subst, FUN_EQ_THM] THEN X_GEN_TAC (← q r"i:num") THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q r"(l:num->num) i - k = 0") (fun th => REWRITE_TAC [th]) THEN
    ASM_CASES_TAC (← q r"i:num < n") THENL
     [SUBGOAL_THEN (← q r"(l:num->num) i < k + 1") MP_TAC THENL
       [ASM_SIMP_TAC [], ARITH_TAC],
      SUBGOAL_THEN (← q r"(l:num->num) i = 0") (fun th => REWRITE_TAC [th, SUB_0]) THEN
      ASM_MESON_TAC [NOT_LT]]))

  let HJ_SUBST_TAKE ← prove
   r"!k m n z a. 1 <= k /\ hj_subspace k m n z
               ==> hj_subst k z (hj_take m a) = hj_subst k z a"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [hj_subspace, IN_HJ_CUBE] THEN STRIP_TAC THEN
    REWRITE_TAC [hj_subst, hj_take, FUN_EQ_THM] THEN X_GEN_TAC (← q r"i:num") THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q r"(z:num->num) i - k < m") (fun th => REWRITE_TAC [th]) THEN
    ASM_CASES_TAC (← q r"i:num < n") THENL
     [SUBGOAL_THEN (← q r"(z:num->num) i < k + m") MP_TAC THENL
       [ASM_SIMP_TAC [], ASM_ARITH_TAC],
      SUBGOAL_THEN (← q r"(z:num->num) i = 0") SUBST_ALL_TAC THENL
       [ASM_MESON_TAC [NOT_LT], ASM_ARITH_TAC]]))

  /- Multidimensional Hales-Jewett. -/

  let HJ_PATTERN_INDEX ← prove
   r"!(D:B->bool) r.
        FINITE D
        ==> ?R idx. 1 <= R /\
                    (!f:B->num. (!w. w IN D ==> f w < r) ==> idx f < R) /\
                    (!f g:B->num. (!w. w IN D ==> f w < r) /\
                           (!w. w IN D ==> g w < r) /\ idx f = idx g
                           ==> !w. w IN D ==> f w = g w)"
   (← do
    -- right to left: the second ARITH_RULE, then the first
    let a2 ← ARITH_RULE (← q r"x < n ==> x < n + 1")
    let a1 ← ARITH_RULE (← q r"1 <= n + 1")
    pure (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"FINITE {f:B->num | (!w. w IN D ==> f w < r) /\
                         (!w. ~(w IN D) ==> f w = 0)}")
    MP_TAC THENL
     [MP_TAC (← ISPECL [← q r"0", ← q r"r:num", ← q r"{i:num | i < r}", ← q r"CARD(D:B->bool)",
                        ← q r"D:B->bool"] HAS_SIZE_FUNSPACE) THEN
      ASM_REWRITE_TAC [HAS_SIZE_NUMSEG_LT, ← GSYM FINITE_HAS_SIZE] THEN
      REWRITE_TAC [IN_ELIM_THM] THEN SIMP_TAC [HAS_SIZE],
      ALL_TAC] THEN
    ABBREV_TAC
     (← q r"PS = {f:B->num | (!w. w IN D ==> f w < r) /\
                       (!w. ~(w IN D) ==> f w = 0)}") THEN
    DISCH_TAC THEN
    FIRST_ASSUM (X_CHOOSE_THEN (← q r"ind:(B->num)->num") STRIP_ASSUME_TAC o
      MATCH_MP HJ_FINITE_INDEX) THEN
    SUBGOAL_THEN
     (← q r"!f:B->num. (!w. w IN D ==> f w < r)
                 ==> (\w. if w IN D then f w else 0) IN PS")
    ASSUME_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "PS" THEN
      REWRITE_TAC [IN_ELIM_THM] THEN ASM_SIMP_TAC [],
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [← q r"CARD(PS:(B->num)->bool) + 1",
      ← q r"\f:B->num. (ind:(B->num)->num)(\w. if w IN D then f w else 0)"] THEN
    REWRITE_TAC [a1] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      MATCH_MP_TAC a2 THEN ASM_SIMP_TAC [],
      ALL_TAC] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"(\w. if w IN D then (f:B->num) w else 0) =
      (\w. if w IN D then g w else 0)")
    MP_TAC THENL
     [FIRST_X_ASSUM (MATCH_MP_TAC o
        check (fun th => (strip_forall (concl th)).1.length == 2)) THEN
      ASM_SIMP_TAC [],
      REWRITE_TAC [FUN_EQ_THM] THEN MESON_TAC []]))

  let MULTIDIM_HALES_JEWETT ← prove
   r"!k m r. 1 <= k /\ 1 <= r
           ==> ?N. !n c. N <= n /\ (!x. c x < r)
                         ==> ?z. hj_subspace k m n z /\
                                 !a b. a IN hj_cube k m /\ b IN hj_cube k m
                                       ==> c(hj_subst k z a) =
                                           c(hj_subst k z b)"
   (← do
    pure (GEN_TAC THEN INDUCT_TAC THENL
     [REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"0") THEN REPEAT STRIP_TAC THEN
      EXISTS_TAC (← q r"(\i. 0):num->num") THEN
      REWRITE_TAC [HJ_SUBSPACE_0, HJ_CUBE_0] THEN
      REWRITE_TAC [IN_SING, IN_HJ_CUBE] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC, SIMP_TAC []],
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"r:num")) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"N1:num") (LABEL_TAC "ih")) THEN
    MP_TAC (← ISPECL [← q r"hj_cube k N1", ← q r"r:num"] HJ_PATTERN_INDEX) THEN
    REWRITE_TAC [FINITE_HJ_CUBE] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"R:num")
     (X_CHOOSE_THEN (← q r"idx:((num->num)->num)->num") STRIP_ASSUME_TAC)) THEN
    MP_TAC (← SPECL [← q r"k:num", ← q r"R:num"] HALES_JEWETT) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"N2:num") (LABEL_TAC "hj")) THEN
    EXISTS_TAC (← q r"N1 + N2:num") THEN REPEAT STRIP_TAC THEN
    REMOVE_THEN "hj" (MP_TAC o SPECL
     [← q r"n - N1:num",
      ← q r"\y. (idx:((num->num)->num)->num)
             (\w. (c:(num->num)->num)(hj_concat N1 w y))"]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC [] THEN ASM_ARITH_TAC, ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"l:num->num") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     (← q r"!w a. w IN hj_cube k N1 /\ a < k
            ==> (c:(num->num)->num)(hj_concat N1 w (hj_line_point k l a)) =
                c(hj_concat N1 w (hj_line_point k l 0))")
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [← q r"a:num", ← q r"0"]) THEN
      ASM_SIMP_TAC [← ARITH_RULE (← q r"1 <= k ==> 0 < k")] THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL
       [← q r"\w. (c:(num->num)->num)(hj_concat N1 w (hj_line_point k l a))",
        ← q r"\w. (c:(num->num)->num)(hj_concat N1 w (hj_line_point k l 0))"] o
       check (fun th => (strip_forall (concl th)).1.length == 2)) THEN
      ASM_SIMP_TAC [],
      ALL_TAC] THEN
    REMOVE_THEN "ih" (MP_TAC o SPECL
     [← q r"N1:num",
      ← q r"\w. (c:(num->num)->num)(hj_concat N1 w (hj_line_point k l 0))"]) THEN
    ASM_REWRITE_TAC [LE_REFL] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"z1:num->num") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"hj_join k N1 m z1 l") THEN CONJ_TAC THENL
     [SUBGOAL_THEN (← q r"n = N1 + (n - N1):num") SUBST1_TAC THENL
       [ASM_ARITH_TAC, ALL_TAC] THEN
      REWRITE_TAC [ADD1] THEN MATCH_MP_TAC HJ_SUBSPACE_JOIN THEN
      ASM_REWRITE_TAC [← GSYM hj_line],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!a. a IN hj_cube k (SUC m)
          ==> (c:(num->num)->num)(hj_subst k (hj_join k N1 m z1 l) a) =
              c(hj_concat N1 (hj_subst k z1 (hj_take m a))
                  (hj_line_point k l 0))")
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      REWRITE_TAC [HJ_SUBST_JOIN] THEN ASM_SIMP_TAC [HJ_SUBST_TAKE] THEN
      FIRST_ASSUM (fun th => tactic_of do
        pure (REWRITE_TAC [← MATCH_MP HJ_SUBST_LINE th])) THEN
      REWRITE_TAC [hj_drop, ADD_CLAUSES] THEN
      MP_TAC (← ISPECL [← q r"k:num", ← q r"m:num", ← q r"N1:num", ← q r"z1:num->num",
                        ← q r"a:num->num"] HJ_SUBST_TAKE) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC HJ_SUBST_CUBE THEN EXISTS_TAC (← q r"m:num") THEN
        ASM_REWRITE_TAC [] THEN MATCH_MP_TAC HJ_TAKE_CUBE THEN
        EXISTS_TAC (← q r"1") THEN ASM_REWRITE_TAC [← GSYM ADD1],
        UNDISCH_TAC (← q r"(a:num->num) IN hj_cube k (SUC m)") THEN
        REWRITE_TAC [IN_HJ_CUBE] THEN MESON_TAC [LT]],
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC [] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC HJ_TAKE_CUBE THEN EXISTS_TAC (← q r"1") THEN
    ASM_REWRITE_TAC [← GSYM ADD1]))

  -- @@RETURN BEGIN
  return { HALES_JEWETT, HALES_JEWETT_FINITE, HJ_SUBST_LINE, HJ_SUBST_TAKE,
           HJ_PATTERN_INDEX, MULTIDIM_HALES_JEWETT }
  -- @@RETURN END


/- ------------------------------------------------------------------------- -/
/- The first wildcard of a line of [1]^m; alphabet-2 words as variable      -/
/- words over the alphabet 1.  (szemeredi.ml 1860-1996)                      -/
/- ------------------------------------------------------------------------- -/

structure FirstWildcard where
  -- @@FIELDS
  hj_first_wildcard : thm
  HJ_FIRST_WILDCARD : thm
  HJ_FIRST_WILDCARD_UNIQUE : thm
  HJ_LINE_1_DROP : thm
  HJ_FIRST_WILDCARD_DROP : thm
  HJ_SUBST_IN_CUBE : thm
  HJ_SUBSPACE_HEAD1 : thm
  HJ_SUBST_HEAD1 : thm
  HJ_SUBST_HEAD0 : thm
  HJ_SUBST_HEAD1E : thm
  HJ_SUBSPACE_1_UNIT : thm
  deriving Inhabited

@[nospecialize]
def setupFirstWildcard [HolBase] (D : SzemerediDeps) (BWords : Words) (BLines : Lines) :
    ExceptT String IO FirstWildcard := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, new_definition, .. } := D
  let { ADD_CLAUSES, ADD_SUB, ARITH, FUN_EQ_THM, LET_TRANS, MINIMAL, MINIMAL_UNIQUE, .. } := D.core1
  let { NOT_LT, SUB_REFL, .. } := D.core2
  let { IN_HJ_CUBE, hj_concat, hj_drop, hj_subspace, hj_subst, .. } := BWords
  let { HJ_SUBST_JOIN, hj_line, .. } := BLines
  -- @@SCOPE END

  let hj_first_wildcard ← new_definition
   r"hj_first_wildcard (u:num->num) = minimal i. u i = 1"

  let HJ_FIRST_WILDCARD ← prove
   r"!n u. hj_line 1 n u
         ==> hj_first_wildcard u < n /\ u (hj_first_wildcard u) = 1 /\
             !i. i < hj_first_wildcard u ==> ~(u i = 1)"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [hj_line, hj_subspace] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"0")) THEN REWRITE_TAC [ARITH, ADD_CLAUSES] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"i:num") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"?j. (u:num->num) j = 1") MP_TAC THENL
     [ASM_MESON_TAC [], ALL_TAC] THEN
    ONCE_REWRITE_TAC [MINIMAL] THEN REWRITE_TAC [← GSYM hj_first_wildcard] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [NOT_LT, LET_TRANS]))

  let HJ_FIRST_WILDCARD_UNIQUE ← prove
   r"!u i. u i = 1 /\ (!j. j < i ==> ~(u j = 1)) ==> hj_first_wildcard u = i"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [hj_first_wildcard] THEN
    MATCH_MP_TAC MINIMAL_UNIQUE THEN ASM_REWRITE_TAC [])

  let HJ_LINE_1_DROP ← prove
   r"!n u. hj_line 1 (n + 1) u /\ u 0 = 0 ==> hj_line 1 n (hj_drop 1 u)"
   (← do
    pure (REPEAT GEN_TAC THEN
    REWRITE_TAC [hj_line, hj_subspace, IN_HJ_CUBE, hj_drop] THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC,
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC,
      X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"j:num")) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"i:num") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"i - 1") THEN
      SUBGOAL_THEN (← q r"~(i = 0)") ASSUME_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC (← q r"(u:num->num) i = 1 + j") THEN
        ASM_REWRITE_TAC [] THEN ARITH_TAC,
        ASM_SIMP_TAC [← ARITH_RULE (← q r"~(i = 0) ==> i - 1 + 1 = i")] THEN
        ASM_ARITH_TAC]]))

  let HJ_FIRST_WILDCARD_DROP ← prove
   r"!n u. hj_line 1 (n + 1) u /\ u 0 = 0
         ==> hj_first_wildcard u = hj_first_wildcard (hj_drop 1 u) + 1"
   (← do
    pure (REPEAT STRIP_TAC THEN MATCH_MP_TAC HJ_FIRST_WILDCARD_UNIQUE THEN
    MP_TAC (← SPECL [← q r"n:num", ← q r"u:num->num"] HJ_LINE_1_DROP) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o MATCH_MP HJ_FIRST_WILDCARD) THEN
    REWRITE_TAC [hj_drop] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"j = 0") THEN
    ASM_REWRITE_TAC [ARITH] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"j - 1")) THEN
    ASM_SIMP_TAC [← ARITH_RULE (← q r"~(j = 0) ==> j - 1 + 1 = j")] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC))

  /- Alphabet-2 words as variable words over the alphabet 1. -/

  let HJ_SUBST_IN_CUBE ← prove
   r"!k k' m n z a. 1 <= k /\ k <= k' /\ hj_subspace k m n z /\ a IN hj_cube k' m
                  ==> hj_subst k z a IN hj_cube k' n"
   (← do
    -- right to left: the second ARITH_RULE, then the first
    let a2 ← ARITH_RULE (← q r"1 <= k ==> 0 < k")
    let a1 ← ARITH_RULE (← q r"~(z < k) /\ z < k + m ==> z - k < m:num")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [hj_subspace, IN_HJ_CUBE, hj_subst] THEN
    STRIP_TAC THEN
    CONJ_TAC THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THENL
     [COND_CASES_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC a1 THEN
      ASM_SIMP_TAC [],
      ASM_SIMP_TAC [a2]]))

  let HJ_SUBSPACE_HEAD1 ← prove
   r"!m n Y. hj_subspace 2 m n Y
           ==> hj_subspace 1 (m + 1) (1 + n)
                     (hj_concat 1 (\i. if i = 0 then 1 else 0) Y)"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [hj_subspace, IN_HJ_CUBE, hj_concat] THEN
    STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN
      ASM_CASES_TAC (← q r"i < 1") THEN ASM_REWRITE_TAC [] THENL
       [COND_CASES_TAC THEN ARITH_TAC,
        SUBGOAL_THEN (← q r"(Y:num->num)(i - 1) < 2 + m") MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC, ARITH_TAC]],
      X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"~(i < 1)") (fun th => REWRITE_TAC [th]) THENL
       [ASM_ARITH_TAC, FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC],
      X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"j = 0") THENL
       [EXISTS_TAC (← q r"0") THEN ASM_REWRITE_TAC [] THEN ARITH_TAC, ALL_TAC] THEN
      SUBGOAL_THEN (← q r"?p. p < n /\ (Y:num->num) p = 2 + (j - 1)")
       (X_CHOOSE_THEN (← q r"p:num") STRIP_ASSUME_TAC) THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN
      EXISTS_TAC (← q r"p + 1") THEN
      ASM_REWRITE_TAC [← ARITH_RULE (← q r"~(p + 1 < 1)"), ADD_SUB] THEN
      ASM_ARITH_TAC]))

  let HJ_SUBST_HEAD1 ← prove
   r"!Y u. u 0 = 1
         ==> hj_subst 1 (hj_concat 1 (\i. if i = 0 then 1 else 0) Y) u =
             hj_concat 1 (\i. if i = 0 then 1 else 0)
               (hj_subst 2 Y (hj_drop 1 u))"
   (← do
    -- right to left: the second ARITH_RULE, then the first
    let a2 ← ARITH_RULE (← q r"~(y < 1) /\ ~(y = 1) ==> ~(y < 2)")
    let a1 ← ARITH_RULE (← q r"y < 1 ==> y < 2")
    pure (REPEAT STRIP_TAC THEN
    REWRITE_TAC [hj_subst, hj_concat, hj_drop, FUN_EQ_THM] THEN
    X_GEN_TAC (← q r"i:num") THEN ASM_CASES_TAC (← q r"i < 1") THEN ASM_REWRITE_TAC [] THENL
     [SUBGOAL_THEN (← q r"i = 0") SUBST1_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      ASM_REWRITE_TAC [ARITH, SUB_REFL],
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"(Y:num->num)(i - 1) < 1") THEN ASM_REWRITE_TAC [] THENL
     [ASM_SIMP_TAC [a1], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"(Y:num->num)(i - 1) = 1") THENL
     [ASM_REWRITE_TAC [ARITH, SUB_REFL], ALL_TAC] THEN
    ASM_SIMP_TAC [a2] THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC))

  let HJ_SUBST_HEAD0 ← prove
   r"!d u. u 0 = 0
           ==> hj_subst 1 (hj_join 1 1 1 (\i. if i = 0 then 1 else 0) d) u =
               hj_concat 1 (\i. 0) (hj_subst 1 d (hj_drop 1 u))"
   (← do
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [HJ_SUBST_JOIN] THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC [hj_subst, FUN_EQ_THM] THEN
    X_GEN_TAC (← q r"x:num") THEN
    ASM_CASES_TAC (← q r"x = 0") THEN ASM_REWRITE_TAC [ARITH, SUB_REFL]))

  let HJ_SUBST_HEAD1E ← prove
   r"!d u. u 0 = 1
           ==> hj_subst 1 (hj_join 1 1 1 (\i. if i = 0 then 1 else 0) d) u =
               hj_concat 1 (\i. if i = 0 then 1 else 0)
                 (hj_subst 1 d (hj_drop 1 u))"
   (← do
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [HJ_SUBST_JOIN] THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC [hj_subst, FUN_EQ_THM] THEN
    X_GEN_TAC (← q r"x:num") THEN
    ASM_CASES_TAC (← q r"x = 0") THEN ASM_REWRITE_TAC [ARITH, SUB_REFL]))

  /- Folkman's theorem. -/

  let HJ_SUBSPACE_1_UNIT ← prove
   r"hj_subspace 1 1 1 (\i. if i = 0 then 1 else 0)"
   (← do
    pure (REWRITE_TAC [hj_subspace, IN_HJ_CUBE] THEN REPEAT STRIP_TAC THENL
     [COND_CASES_TAC THEN ARITH_TAC,
      ASM_SIMP_TAC [← ARITH_RULE (← q r"1 <= i ==> ~(i = 0)")],
      EXISTS_TAC (← q r"0") THEN ASM_ARITH_TAC]))

  -- @@RETURN BEGIN
  return { hj_first_wildcard, HJ_FIRST_WILDCARD, HJ_FIRST_WILDCARD_UNIQUE,
           HJ_LINE_1_DROP, HJ_FIRST_WILDCARD_DROP, HJ_SUBST_IN_CUBE, HJ_SUBSPACE_HEAD1,
           HJ_SUBST_HEAD1, HJ_SUBST_HEAD0, HJ_SUBST_HEAD1E, HJ_SUBSPACE_1_UNIT }
  -- @@RETURN END


/- ------------------------------------------------------------------------- -/
/- Folkman's theorem.  (szemeredi.ml 1996-2219)                              -/
/- ------------------------------------------------------------------------- -/

structure Folkman where
  -- @@FIELDS
  FOLKMAN_FOCUS : thm
  HJ_LINE_1_UNIT : thm
  FOLKMAN : thm
  deriving Inhabited

@[nospecialize]
def setupFolkman [HolBase] (D : SzemerediDeps) (BWords : Words) (BLines : Lines) (BDensities : Densities) (BHalesJewett : HalesJewett) (BFirstWildcard : FirstWildcard) :
    ExceptT String IO Folkman := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC,
        SET_TAC, .. } := D
  let { ADD1, ADD_SYM, ARITH, CARD_LE_INJ, CARD_NUMSEG_LT, FINITE_NUMSEG_LT,
        FINITE_SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM, LE_MULT_LCANCEL, LE_REFL, LT,
        MEMBER_NOT_EMPTY, MONO_EXISTS, .. } := D.core1
  let { NOT_LT, NOT_SUC, REAL_OF_NUM_LE, REAL_OF_NUM_MUL, SELECT_UNIQUE, SUBSET,
        SUC_SUB1, .. } := D.core2
  let { HJ_DROP_CONCAT, HJ_DROP_CUBE, HJ_SUBSPACE_0, HJ_SUBSPACE_SUBST, HJ_SUBST_SUBST,
        IN_HJ_CUBE, hj_concat, hj_subspace, hj_subst, .. } := BWords
  let { HJ_LINE_CUBE, HJ_LINE_SUBST, HJ_SUBSPACE_JOIN, hj_line, .. } := BLines
  let { CARD_PIGEONHOLE, .. } := BDensities
  let { MULTIDIM_HALES_JEWETT, .. } := BHalesJewett
  let { HJ_FIRST_WILDCARD, HJ_FIRST_WILDCARD_DROP, HJ_FIRST_WILDCARD_UNIQUE,
        HJ_LINE_1_DROP, HJ_SUBSPACE_1_UNIT, HJ_SUBSPACE_HEAD1, HJ_SUBST_HEAD0,
        HJ_SUBST_HEAD1, HJ_SUBST_HEAD1E, HJ_SUBST_IN_CUBE, .. } := BFirstWildcard
  -- @@SCOPE END

  let FOLKMAN_FOCUS ← prove
   r"!m r. 1 <= r
         ==> ?N. !n c. N <= n /\ (!x. c x < r)
                       ==> ?d (ph:num->num).
                              hj_subspace 1 m n d /\
                              !u. hj_line 1 m u
                                  ==> c(hj_subst 1 d u) =
                                      ph(hj_first_wildcard u)"
   (← do
    -- right to left: the second ARITH_RULE, then the first
    let a2 ← ARITH_RULE (← q r"SUC m = 1 + m /\ N1 + 1 = 1 + N1")
    let a1 ← ARITH_RULE (← q r"0 < 1")
    pure (INDUCT_TAC THENL
     [REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"0") THEN REPEAT STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [← q r"(\i. 0):num->num", ← q r"(\i. 0):num->num"] THEN
      REWRITE_TAC [HJ_SUBSPACE_0, IN_HJ_CUBE] THEN CONJ_TAC THENL
       [ARITH_TAC,
        REWRITE_TAC [hj_line, hj_subspace, LT] THEN
        MESON_TAC [a1]],
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"r:num")) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"N1:num") (LABEL_TAC "ih")) THEN
    MP_TAC (← SPECL [← q r"2", ← q r"N1:num", ← q r"r:num"] MULTIDIM_HALES_JEWETT) THEN
    ASM_REWRITE_TAC [ARITH] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"N2:num") (LABEL_TAC "mhj")) THEN
    EXISTS_TAC (← q r"N2 + 1") THEN REPEAT STRIP_TAC THEN
    REMOVE_THEN "mhj" (MP_TAC o SPECL
     [← q r"n - 1",
      ← q r"\y. (c:(num->num)->num)(hj_concat 1
                                 (\i. if i = 0 then 1 else 0) y)"]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC [] THEN ASM_ARITH_TAC, ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"Y:num->num") (STRIP_ASSUME_TAC o BETA_RULE)) THEN
    SUBGOAL_THEN
     (← q r"hj_subspace 1 (N1 + 1) n (hj_concat 1 (\i. if i = 0 then 1 else 0) Y)")
    ASSUME_TAC THENL
     [SUBGOAL_THEN (← q r"n = 1 + (n - 1)") SUBST1_TAC THENL
       [ASM_ARITH_TAC, MATCH_MP_TAC HJ_SUBSPACE_HEAD1 THEN ASM_REWRITE_TAC []],
      ALL_TAC] THEN
    REMOVE_THEN "ih" (MP_TAC o SPECL
     [← q r"N1:num",
      ← q r"\v. (c:(num->num)->num)
             (hj_subst 1 (hj_concat 1 (\i. if i = 0 then 1 else 0) Y)
                     (hj_concat 1 (\i. 0) v))"]) THEN
    ASM_REWRITE_TAC [LE_REFL] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"d:num->num")
     (X_CHOOSE_THEN (← q r"ph:num->num") STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN
     (← q r"hj_subspace 1 (SUC m) (N1 + 1)
        (hj_join 1 1 1 (\i. if i = 0 then 1 else 0) d)")
    ASSUME_TAC THENL
     [ONCE_REWRITE_TAC [a2] THEN
      MATCH_MP_TAC HJ_SUBSPACE_JOIN THEN
      ASM_REWRITE_TAC [HJ_SUBSPACE_1_UNIT, LE_REFL],
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [← q r"hj_subst 1 (hj_concat 1 (\i. if i = 0 then 1 else 0) Y)
              (hj_join 1 1 1 (\i. if i = 0 then 1 else 0) d)",
      ← q r"\t. if t = 0
           then (c:(num->num)->num)
                  (hj_concat 1 (\i. if i = 0 then 1 else 0)
                     (hj_subst 2 Y (\i. 0)))
           else (ph:num->num)(t - 1)"] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HJ_SUBSPACE_SUBST THEN EXISTS_TAC (← q r"N1 + 1") THEN
      ASM_REWRITE_TAC [LE_REFL],
      ALL_TAC] THEN
    X_GEN_TAC (← q r"u:num->num") THEN DISCH_TAC THEN REWRITE_TAC [HJ_SUBST_SUBST] THEN
    SUBGOAL_THEN (← q r"(u:num->num) 0 = 0 \/ u 0 = 1") STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC (← q r"hj_line 1 (SUC m) u") THEN
      REWRITE_TAC [hj_line, hj_subspace, IN_HJ_CUBE] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"0") o CONJUNCT1 o CONJUNCT1) THEN
      ARITH_TAC,
      ASM_SIMP_TAC [HJ_SUBST_HEAD0] THEN
      SUBGOAL_THEN (← q r"hj_line 1 m (hj_drop 1 u)") ASSUME_TAC THENL
       [MATCH_MP_TAC HJ_LINE_1_DROP THEN ASM_REWRITE_TAC [← GSYM ADD1],
        ALL_TAC] THEN
      MP_TAC (← SPECL [← q r"m:num", ← q r"u:num->num"] HJ_FIRST_WILDCARD_DROP) THEN
      ASM_REWRITE_TAC [← GSYM ADD1] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC [NOT_SUC, SUC_SUB1] THEN ASM_SIMP_TAC [],
      ASM_SIMP_TAC [HJ_SUBST_HEAD1E] THEN
      W (fun (_asl, w) => tactic_of do
        let mkEq ← ExceptT.mk (mk_eq : IO _)
        let lw ← liftExcept (lhand w)
        let e ← liftExcept (mkEq (lw, ← q r"(c:(num->num)->num)
            (hj_concat 1 (\i. if i = 0 then 1 else 0) (hj_subst 2 Y (\i. 0)))"))
        pure (SUBGOAL_THEN e SUBST1_TAC)) THENL
       [MP_TAC (← ISPECL [← q r"Y:num->num",
                          ← q r"hj_concat 1 (\i. if i = 0 then 1 else 0)
                             (hj_subst 1 d (hj_drop 1 u))"] HJ_SUBST_HEAD1) THEN
        ANTS_TAC
        THENL [REWRITE_TAC [hj_concat, ARITH], DISCH_THEN SUBST1_TAC] THEN
        REWRITE_TAC [HJ_DROP_CONCAT] THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o
          check (fun th => (strip_forall (concl th)).1.length == 2)) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC HJ_SUBST_IN_CUBE THEN
          EXISTS_TAC (← q r"m:num") THEN ASM_REWRITE_TAC [ARITH] THEN
          MATCH_MP_TAC HJ_DROP_CUBE THEN
          ONCE_REWRITE_TAC [ADD_SYM] THEN REWRITE_TAC [← GSYM ADD1] THEN
          MP_TAC (← MATCH_MP HJ_LINE_CUBE (← ASSUME (← q r"hj_line 1 (SUC m) u"))) THEN
          REWRITE_TAC [ARITH],
          REWRITE_TAC [IN_HJ_CUBE] THEN ARITH_TAC],
        SUBGOAL_THEN (← q r"hj_first_wildcard u = 0") SUBST1_TAC THENL
         [MATCH_MP_TAC HJ_FIRST_WILDCARD_UNIQUE THEN ASM_REWRITE_TAC [LT],
          REWRITE_TAC []]]]))

  let HJ_LINE_1_UNIT ← prove
   r"!n i. i < n ==> hj_line 1 n (\j. if j = i then 1 else 0) /\
                   hj_first_wildcard (\j. if j = i then 1 else 0) = i"
   (← do
    pure (REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC [hj_line, hj_subspace, IN_HJ_CUBE] THEN REPEAT STRIP_TAC THENL
       [COND_CASES_TAC THEN ARITH_TAC,
        COND_CASES_TAC THEN ASM_ARITH_TAC,
        EXISTS_TAC (← q r"i:num") THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC],
      MATCH_MP_TAC HJ_FIRST_WILDCARD_UNIQUE THEN REWRITE_TAC [] THEN ARITH_TAC]))

  let FOLKMAN ← prove
   r"!m r. 1 <= r
         ==> ?N. !n c. N <= n /\ (!x. c x < r)
                       ==> ?d. hj_subspace 1 m n d /\
                               !u v. hj_line 1 m u /\ hj_line 1 m v
                                     ==> c(hj_subst 1 d u) =
                                         c(hj_subst 1 d v)"
   (← do
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"r * m:num", ← q r"r:num"] FOLKMAN_FOCUS) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC (← q r"N:num") THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [← q r"n:num", ← q r"c:(num->num)->num"] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"n:num", ← q r"c:(num->num)->num"]) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"d0:num->num")
     (X_CHOOSE_THEN (← q r"ph:num->num") STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN (← q r"!i. i < r * m ==> (ph:num->num) i < r") ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP HJ_LINE_1_UNIT) THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"\j:num. if j = i then 1 else 0")) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"ph:num->num", ← q r"{i:num | i < r * m}", ← q r"{j:num | j < r}"]
      CARD_PIGEONHOLE) THEN
    ASM_SIMP_TAC [FINITE_NUMSEG_LT, CARD_NUMSEG_LT, IN_ELIM_THM] THEN
    ANTS_TAC THENL
     [REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, IN_ELIM_THM] THEN
      EXISTS_TAC (← q r"0") THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"s:num") STRIP_ASSUME_TAC) THEN
    ABBREV_TAC (← q r"J = {i:num | i < r * m /\ (ph:num->num) i = s}") THEN
    SUBGOAL_THEN (← q r"FINITE(J:num->bool) /\ m <= CARD J") STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [EXPAND_TAC "J" THEN MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC (← q r"{i:num | i < r * m}") THEN
        REWRITE_TAC [FINITE_NUMSEG_LT] THEN SET_TAC [],
        ALL_TAC] THEN
      UNDISCH_TAC (← q r"&(r * m) <= &r * &(CARD(J:num->bool))") THEN
      REWRITE_TAC [REAL_OF_NUM_MUL, REAL_OF_NUM_LE, LE_MULT_LCANCEL] THEN
      ASM_ARITH_TAC,
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"{j:num | j < m}", ← q r"J:num->bool"] CARD_LE_INJ) THEN
    ASM_REWRITE_TAC [FINITE_NUMSEG_LT, CARD_NUMSEG_LT] THEN
    REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"h:num->num") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"!j. j < m ==> (h:num->num) j < r * m /\ (ph:num->num)(h j) = s")
    ASSUME_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"(h:num->num) j IN J") MP_TAC THENL
       [ASM_SIMP_TAC [], EXPAND_TAC "J" THEN REWRITE_TAC [IN_ELIM_THM]],
      ALL_TAC] THEN
    ABBREV_TAC
     (← q r"sel = \i. if ?j. j < m /\ (h:num->num) j = i
                then 1 + (@j. j < m /\ h j = i) else 0") THEN
    SUBGOAL_THEN (← q r"!j. j < m ==> (sel:num->num)(h j) = 1 + j") ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "sel" THEN
      COND_CASES_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
      ASM_MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!i. 1 <= (sel:num->num) i ==> ?j. j < m /\ (h:num->num) j = i")
    ASSUME_TAC THENL
     [GEN_TAC THEN EXPAND_TAC "sel" THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC [] THEN ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"hj_subspace 1 m (r * m) sel") ASSUME_TAC THENL
     [REWRITE_TAC [hj_subspace, IN_HJ_CUBE] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN
        ASM_CASES_TAC (← q r"1 <= (sel:num->num) i") THENL
         [FIRST_X_ASSUM (MP_TAC o SPEC (← q r"i:num")) THEN ASM_REWRITE_TAC [] THEN
          DISCH_THEN (X_CHOOSE_THEN (← q r"j:num") STRIP_ASSUME_TAC) THEN
          FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN ASM_SIMP_TAC [] THEN
          ASM_ARITH_TAC,
          ASM_ARITH_TAC],
        X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN
        ASM_CASES_TAC (← q r"1 <= (sel:num->num) i") THENL
         [FIRST_X_ASSUM (MP_TAC o SPEC (← q r"i:num")) THEN ASM_REWRITE_TAC [] THEN
          ASM_MESON_TAC [NOT_LT],
          ASM_ARITH_TAC],
        X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN EXISTS_TAC (← q r"(h:num->num) j") THEN
        ASM_SIMP_TAC []],
      ALL_TAC] THEN
    EXISTS_TAC (← q r"hj_subst 1 d0 sel") THEN CONJ_TAC THENL
     [MATCH_MP_TAC HJ_SUBSPACE_SUBST THEN EXISTS_TAC (← q r"r * m:num") THEN
      ASM_REWRITE_TAC [LE_REFL],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!u. hj_line 1 m u ==>
      (c:(num->num)->num)(hj_subst 1 (hj_subst 1 d0 sel) u) = s")
     (fun th => ASM_MESON_TAC [th]) THEN
    X_GEN_TAC (← q r"u:num->num") THEN DISCH_TAC THEN REWRITE_TAC [HJ_SUBST_SUBST] THEN
    SUBGOAL_THEN (← q r"hj_line 1 (r * m) (hj_subst 1 sel u)") ASSUME_TAC THENL
     [MATCH_MP_TAC HJ_LINE_SUBST THEN EXISTS_TAC (← q r"m:num") THEN
      ASM_REWRITE_TAC [LE_REFL],
      ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP HJ_FIRST_WILDCARD) THEN
    ABBREV_TAC (← q r"p = hj_first_wildcard(hj_subst 1 sel u)") THEN
    SUBGOAL_THEN (← q r"1 <= (sel:num->num) p") MP_TAC THENL
     [UNDISCH_TAC (← q r"hj_subst 1 sel u p = 1") THEN REWRITE_TAC [hj_subst] THEN
      COND_CASES_TAC THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    DISCH_THEN (fun th => FIRST_X_ASSUM (MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"j:num") STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC []))

  -- @@RETURN BEGIN
  return { FOLKMAN_FOCUS, HJ_LINE_1_UNIT, FOLKMAN }
  -- @@RETURN END


/- ------------------------------------------------------------------------- -/
/- Wildcard sets and their lifts.  (szemeredi.ml 2222-2391)                  -/
/- ------------------------------------------------------------------------- -/

structure Wildcards where
  -- @@FIELDS
  hj_wildcards : thm
  hj_wlift : thm
  hj_dlift : thm
  HJ_LINE_EQ : thm
  HJ_WILDCARDS_LINE : thm
  HJ_WLIFT_LINE : thm
  HJ_WILDCARDS_WLIFT : thm
  HJ_SUBSPACE_DLIFT : thm
  HJ_WILDCARDS_DLIFT : thm
  HJ_LINE_POINT_K : thm
  HJ_WILDCARDS_TAKE : thm
  HJ_PAIR_CODE : thm
  HJ_PAIR_DECODE : thm
  HJ_LINE_SUC_CASES : thm
  HJ_WILDCARDS_EQ_VAR : thm
  deriving Inhabited

@[nospecialize]
def setupWildcards [HolBase] (D : SzemerediDeps) (BWords : Words) (BLines : Lines) :
    ExceptT String IO Wildcards := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, TAUT,
        new_definition, .. } := D
  let { ADD_CLAUSES, ARITH, DIVMOD_UNIQ, FUN_EQ_THM, LE_MULT_LCANCEL, LT, LTE_TRANS,
        LT_ADD_LCANCEL, NOT_EXISTS_THM, .. } := D.core1
  let { NOT_LE, NOT_LT, SUB_0, SUB_REFL, .. } := D.core2
  let { IN_HJ_CUBE, hj_subspace, hj_subst, hj_take, .. } := BWords
  let { hj_line, hj_line_point, .. } := BLines
  -- @@SCOPE END

  let hj_wildcards ← new_definition
   r"hj_wildcards k (u:num->num) = \i. if u i = k then 1 else 0"

  let hj_wlift ← new_definition
   r"hj_wlift k (w:num->num) = \i. if w i = 1 then k else 0"

  let hj_dlift ← new_definition
   r"hj_dlift k (d:num->num) = \i. if d i = 0 then 0 else k + (d i - 1)"

  let HJ_LINE_EQ ← prove
   r"!k n u. hj_line k n u <=> u IN hj_cube (k + 1) n /\ ?i. i < n /\ u i = k"
   (← do
    pure (REWRITE_TAC [hj_line, hj_subspace, ← ARITH_RULE (← q r"j < 1 <=> j = 0")] THEN
    MESON_TAC [ADD_CLAUSES]))

  let HJ_WILDCARDS_LINE ← prove
   r"!k n u. 1 <= k /\ hj_line k n u ==> hj_line 1 n (hj_wildcards k u)"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [HJ_LINE_EQ, IN_HJ_CUBE, hj_wildcards] THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ARITH_TAC,
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC [] THEN ASM_ARITH_TAC,
      EXISTS_TAC (← q r"i:num") THEN ASM_REWRITE_TAC [] THEN ARITH_TAC]))

  let HJ_WLIFT_LINE ← prove
   r"!k n w. 1 <= k /\ hj_line 1 n w ==> hj_line k n (hj_wlift k w)"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [HJ_LINE_EQ, IN_HJ_CUBE, hj_wlift] THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_ARITH_TAC,
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC [] THEN ARITH_TAC,
      EXISTS_TAC (← q r"i:num") THEN ASM_REWRITE_TAC []]))

  let HJ_WILDCARDS_WLIFT ← prove
   r"!k n w. 1 <= k /\ w IN hj_cube 2 n ==> hj_wildcards k (hj_wlift k w) = w"
   (← do
    pure (REPEAT GEN_TAC THEN
    REWRITE_TAC [IN_HJ_CUBE, hj_wildcards, hj_wlift, FUN_EQ_THM] THEN
    STRIP_TAC THEN X_GEN_TAC (← q r"i:num") THEN
    ASM_CASES_TAC (← q r"(w:num->num) i = 1") THEN ASM_REWRITE_TAC [] THEN
    ASM_SIMP_TAC [← ARITH_RULE (← q r"1 <= k ==> ~(0 = k)")] THEN
    ASM_CASES_TAC (← q r"i:num < n") THENL
     [SUBGOAL_THEN (← q r"(w:num->num) i < 2") MP_TAC THENL
       [ASM_SIMP_TAC [], ASM_ARITH_TAC],
      ASM_MESON_TAC [NOT_LT]]))

  let HJ_SUBSPACE_DLIFT ← prove
   r"!k m n d. 1 <= k /\ hj_subspace 1 m n d
             ==> hj_subspace k m n (hj_dlift k d)"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [hj_subspace, IN_HJ_CUBE, hj_dlift] THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN COND_CASES_TAC THENL
       [ASM_ARITH_TAC, ALL_TAC] THEN
      SUBGOAL_THEN (← q r"(d:num->num) i < 1 + m") MP_TAC THENL
       [ASM_SIMP_TAC [], ASM_ARITH_TAC],
      ASM_SIMP_TAC [],
      X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"?i. i < n /\ (d:num->num) i = 1 + j")
       (X_CHOOSE_THEN (← q r"i:num") STRIP_ASSUME_TAC) THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN
      EXISTS_TAC (← q r"i:num") THEN ASM_REWRITE_TAC [] THEN ARITH_TAC]))

  let HJ_WILDCARDS_DLIFT ← prove
   r"!k d u. 1 <= k
           ==> hj_wildcards k (hj_subst k (hj_dlift k d) u) =
               hj_subst 1 d (hj_wildcards k u)"
   (← do
    -- right to left: the ARITH_RULEs from the third to the first
    let a3 ← ARITH_RULE (← q r"(k + d - 1) - k = d - 1")
    let a2 ← ARITH_RULE (← q r"~(d = 0) ==> ~(k + d - 1 < k) /\ ~(d < 1)")
    let a1 ← ARITH_RULE (← q r"1 <= k ==> 0 < k /\ ~(0 = k)")
    pure (REPEAT STRIP_TAC THEN
    REWRITE_TAC [hj_wildcards, hj_subst, hj_dlift, FUN_EQ_THM] THEN
    X_GEN_TAC (← q r"i:num") THEN ASM_CASES_TAC (← q r"(d:num->num) i = 0") THEN
    ASM_REWRITE_TAC [ARITH] THENL
     [ASM_SIMP_TAC [a1], ALL_TAC] THEN
    ASM_SIMP_TAC [a2, a3]))

  let HJ_LINE_POINT_K ← prove
   r"!k n x. hj_line k n x ==> hj_line_point k x k = x"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [HJ_LINE_EQ, IN_HJ_CUBE] THEN STRIP_TAC THEN
    REWRITE_TAC [hj_line_point, hj_subst, FUN_EQ_THM] THEN X_GEN_TAC (← q r"j:num") THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q r"j:num < n") THENL
     [SUBGOAL_THEN (← q r"(x:num->num) j = k") (fun th => REWRITE_TAC [th,
       SUB_REFL]) THEN
      SUBGOAL_THEN (← q r"(x:num->num) j < k + 1") MP_TAC THENL
       [ASM_SIMP_TAC [], ASM_ARITH_TAC],
      SUBGOAL_THEN (← q r"(x:num->num) j = 0") SUBST_ALL_TAC THENL
       [ASM_MESON_TAC [NOT_LT], ALL_TAC] THEN
      REWRITE_TAC [SUB_0] THEN ASM_ARITH_TAC]))

  let HJ_WILDCARDS_TAKE ← prove
   r"!k M u. 1 <= k
           ==> hj_wildcards k (hj_take M u) = hj_take M (hj_wildcards k u)"
   (← do
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [hj_wildcards, hj_take, FUN_EQ_THM] THEN
    X_GEN_TAC (← q r"x:num") THEN ASM_CASES_TAC (← q r"x:num < M") THEN
    ASM_SIMP_TAC [← ARITH_RULE (← q r"1 <= k ==> ~(0 = k)")]))

  let HJ_PAIR_CODE ← prove
   r"!r a b. a < r /\ b < r ==> r * a + b < r * (r:num)"
   (← do
    pure (REPEAT STRIP_TAC THEN MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC (← q r"r * a + r:num") THEN ASM_REWRITE_TAC [LT_ADD_LCANCEL] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"r * a + r = r * (a + 1)"), LE_MULT_LCANCEL] THEN
    ASM_ARITH_TAC))

  let HJ_PAIR_DECODE ← prove
   r"!r a b a' b'. b < r /\ b' < r /\ r * a + b = r * a' + (b':num)
                 ==> a = a' /\ b = b'"
   (← do
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"r * a + b:num", ← q r"r:num", ← q r"a:num", ← q r"b:num"] DIVMOD_UNIQ) THEN
    ANTS_TAC THENL [CONJ_TAC THENL [ARITH_TAC, ASM_REWRITE_TAC []], ALL_TAC] THEN
    MP_TAC (← SPECL [← q r"r * a' + b':num", ← q r"r:num", ← q r"a':num", ← q r"b':num"]
      DIVMOD_UNIQ) THEN
    ANTS_TAC THENL [CONJ_TAC THENL [ARITH_TAC, ASM_REWRITE_TAC []], ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN MESON_TAC []))

  let HJ_LINE_SUC_CASES ← prove
   r"!k M u. 1 <= k /\ hj_line k (SUC M) u
           ==> u M <= k /\
               ((?i. i < M /\ u i = k) ==> hj_line k M (hj_take M u)) /\
               (~(?i. i < M /\ u i = k) ==> hj_take M u IN hj_cube k M) /\
               (~(u M = k) ==> ?i. i < M /\ u i = k)"
   (← do
    -- right to left: the second ARITH_RULE, the TAUT, the first ARITH_RULE
    let a2 ← ARITH_RULE (← q r"j < M ==> j < SUC M")
    let t1 ← TAUT (← q r"~(p /\ q) <=> p ==> ~q")
    let a1 ← ARITH_RULE (← q r"x < k + 1 ==> x <= k")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [HJ_LINE_EQ, IN_HJ_CUBE] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC a1 THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC,
      DISCH_THEN (X_CHOOSE_THEN (← q r"j:num") STRIP_ASSUME_TAC) THEN
      REWRITE_TAC [hj_take] THEN REPEAT CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC,
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [← GSYM NOT_LE],
        EXISTS_TAC (← q r"j:num") THEN ASM_REWRITE_TAC []],
      REWRITE_TAC [NOT_EXISTS_THM, t1] THEN
      DISCH_TAC THEN REWRITE_TAC [hj_take] THEN CONJ_TAC THEN
      X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THENL
       [ASM_REWRITE_TAC [] THEN
        SUBGOAL_THEN (← q r"(u:num->num) j < k + 1 /\ ~(u j = k)") MP_TAC THENL
         [ASM_SIMP_TAC [a2], ARITH_TAC],
        ASM_REWRITE_TAC [← GSYM NOT_LE]],
      DISCH_TAC THEN EXISTS_TAC (← q r"i:num") THEN ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC (← q r"i < SUC M") THEN REWRITE_TAC [LT] THEN
      ASM_MESON_TAC []]))

  let HJ_WILDCARDS_EQ_VAR ← prove
   r"!k u u' i. hj_wildcards k u = hj_wildcards k u' ==> (u i = k <=> u' i = k)"
   (← do
    pure (REWRITE_TAC [hj_wildcards, FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"i:num")) THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC [ARITH]))

  -- @@RETURN BEGIN
  return { hj_wildcards, hj_wlift, hj_dlift, HJ_LINE_EQ, HJ_WILDCARDS_LINE,
           HJ_WLIFT_LINE, HJ_WILDCARDS_WLIFT, HJ_SUBSPACE_DLIFT, HJ_WILDCARDS_DLIFT,
           HJ_LINE_POINT_K, HJ_WILDCARDS_TAKE, HJ_PAIR_CODE, HJ_PAIR_DECODE,
           HJ_LINE_SUC_CASES, HJ_WILDCARDS_EQ_VAR }
  -- @@RETURN END


/- ------------------------------------------------------------------------- -/
/- Letter independence and Graham-Rothschild for lines.                      -/
/- (szemeredi.ml 2367-2589)                                                  -/
/- ------------------------------------------------------------------------- -/

structure GrahamRothschild where
  -- @@FIELDS
  HJ_LETTER_INDEP : thm
  GRAHAM_ROTHSCHILD_LINES : thm
  deriving Inhabited

@[nospecialize]
def setupGrahamRothschild [HolBase] (D : SzemerediDeps) (BWords : Words) (BLines : Lines) (BHalesJewett : HalesJewett) (BFolkman : Folkman) (BWildcards : Wildcards) :
    ExceptT String IO GrahamRothschild := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, .. } := D
  let { ADD1, ADD_CLAUSES, ARITH, FINITE_SUBSET, IN_ELIM_THM, LE_REFL, LT, MONO_EXISTS,
        MULT_EQ_0, .. } := D.core1
  let { SUBSET, .. } := D.core2
  let { FINITE_HJ_CUBE, HJ_SUBSPACE_0, HJ_SUBSPACE_SUBST, HJ_SUBST_CUBE,
        HJ_SUBST_SUBST, IN_HJ_CUBE, hj_drop, .. } := BWords
  let { HJ_LINE_CUBE, HJ_LINE_SUBST, HJ_SUBSPACE_JOIN, HJ_SUBST_JOIN, hj_line, .. } := BLines
  let { HALES_JEWETT, HJ_PATTERN_INDEX, HJ_SUBST_LINE, HJ_SUBST_TAKE,
        MULTIDIM_HALES_JEWETT, .. } := BHalesJewett
  let { FOLKMAN, .. } := BFolkman
  let { HJ_LINE_EQ, HJ_LINE_POINT_K, HJ_LINE_SUC_CASES, HJ_PAIR_CODE, HJ_PAIR_DECODE,
        HJ_SUBSPACE_DLIFT, HJ_WILDCARDS_DLIFT, HJ_WILDCARDS_EQ_VAR, HJ_WILDCARDS_LINE,
        HJ_WILDCARDS_TAKE, HJ_WILDCARDS_WLIFT, HJ_WLIFT_LINE, .. } := BWildcards
  -- @@SCOPE END
  -- `length(fst(strip_forall(concl th))) = 2`
  let twoVars : thm → Bool := fun th => (strip_forall (concl th)).1.length == 2
  -- `can (find_term ((=) t)) (concl th)`
  let mentions : term → thm → Bool := fun t th =>
    can (find_term (fun u => u == t)) (concl th)

  let HJ_LETTER_INDEP ← prove
   r"!k M r. 1 <= k /\ 1 <= r
           ==> ?N. !n c. N <= n /\ (!x. c x < r)
                         ==> ?z. hj_subspace k M n z /\
                                 !u u'. hj_line k M u /\ hj_line k M u' /\
                                        hj_wildcards k u = hj_wildcards k u'
                                        ==> c(hj_subst k z u) =
                                            c(hj_subst k z u')"
   (← do
    -- right to left: the second ARITH_RULE, then the first
    let a2 ← ARITH_RULE (← q r"1 <= k ==> 0 < k")
    let a1 ← ARITH_RULE (← q r"1 <= x <=> ~(x = 0)")
    -- `DISCH_THEN(MP_TAC o MATCH_MP HJ_PAIR_DECODE o (fun th -> CONJ (SPEC ..
    -- (ASSUME ..)) (CONJ (SPEC .. (ASSUME ..)) th)))`, built when applied
    let pairDecode : thm_tactic := fun th => tactic_of do
      let cr ← q r"!x. (c:(num->num)->num) x < r"
      let c2 ← SPEC (← q r"hj_concat n1
                                (hj_subst k Y
                                   (hj_subst k z2 (hj_take M u'))) x") (← ASSUME cr)
      let c1 ← SPEC (← q r"hj_concat n1 (hj_subst k Y (hj_subst k z2 (hj_take M u))) x")
        (← ASSUME cr)
      pure (MP_TAC (← MATCH_MP HJ_PAIR_DECODE (← CONJ c1 (← CONJ c2 th))))
    -- `check (fun th -> length(..) = 2 && can (find_term ((=) `r:num`)) ..)`
    let withR : thm → ExceptT String IO thm := fun th => do
      let ok ← if twoVars th then do pure (mentions (← q r"r:num") th) else pure false
      liftExcept (check (fun _ => ok) th)
    pure (GEN_TAC THEN INDUCT_TAC THENL
     [REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"0") THEN REPEAT STRIP_TAC THEN
      EXISTS_TAC (← q r"(\i. 0):num->num") THEN
      REWRITE_TAC [HJ_SUBSPACE_0, IN_HJ_CUBE, HJ_LINE_EQ, LT] THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"r * r:num")) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC [a1, MULT_EQ_0] THEN
      ASM_ARITH_TAC,
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"Ni:num") (LABEL_TAC "ih")) THEN
    MP_TAC (← SPECL [← q r"k:num", ← q r"Ni:num", ← q r"r:num"] MULTIDIM_HALES_JEWETT) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"n1:num") (LABEL_TAC "mhj")) THEN
    MP_TAC (← ISPECL [← q r"{w:num->num | hj_line k n1 w}", ← q r"r:num"]
             HJ_PATTERN_INDEX) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"hj_cube (k + 1) n1") THEN
      REWRITE_TAC [FINITE_HJ_CUBE, SUBSET, IN_ELIM_THM, HJ_LINE_CUBE],
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"R:num")
     (X_CHOOSE_THEN (← q r"idx:((num->num)->num)->num") STRIP_ASSUME_TAC)) THEN
    MP_TAC (← SPECL [← q r"k:num", ← q r"R:num"] HALES_JEWETT) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"N2:num") (LABEL_TAC "hj")) THEN
    EXISTS_TAC (← q r"n1 + N2:num") THEN REPEAT STRIP_TAC THEN
    REMOVE_THEN "hj" (MP_TAC o SPECL
     [← q r"n - n1:num",
      ← q r"\y. (idx:((num->num)->num)->num)
             (\w. (c:(num->num)->num)(hj_concat n1 w y))"]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC [IN_ELIM_THM] THEN ASM_ARITH_TAC, ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"x:num->num") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     (← q r"!w a. hj_line k n1 w /\ a < k
            ==> (c:(num->num)->num)(hj_concat n1 w (hj_line_point k x a)) =
                c(hj_concat n1 w (hj_line_point k x 0))")
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [← q r"a:num", ← q r"0"]) THEN
      ASM_SIMP_TAC [a2] THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL
       [← q r"\w. (c:(num->num)->num)(hj_concat n1 w (hj_line_point k x a))",
        ← q r"\w. (c:(num->num)->num)(hj_concat n1 w (hj_line_point k x 0))"] o
       check twoVars) THEN
      ASM_SIMP_TAC [IN_ELIM_THM],
      ALL_TAC] THEN
    REMOVE_THEN "mhj" (MP_TAC o SPECL
     [← q r"n1:num", ← q r"\p. (c:(num->num)->num)(hj_concat n1 p x)"]) THEN
    ASM_REWRITE_TAC [LE_REFL] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"Y:num->num") (STRIP_ASSUME_TAC o BETA_RULE)) THEN
    REMOVE_THEN "ih" (MP_TAC o SPECL
     [← q r"Ni:num",
      ← q r"\v. r *
           (c:(num->num)->num)(hj_concat n1 (hj_subst k Y v)
                                 (hj_line_point k x 0)) +
           c(hj_concat n1 (hj_subst k Y v) x)"]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC [LE_REFL] THEN GEN_TAC THEN MATCH_MP_TAC HJ_PAIR_CODE THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"z2:num->num") (STRIP_ASSUME_TAC o BETA_RULE)) THEN
    EXISTS_TAC (← q r"hj_join k n1 M (hj_subst k Y z2) x") THEN CONJ_TAC THENL
     [SUBGOAL_THEN (← q r"n = n1 + (n - n1):num") SUBST1_TAC THENL
       [ASM_ARITH_TAC, ALL_TAC] THEN
      REWRITE_TAC [ADD1] THEN MATCH_MP_TAC HJ_SUBSPACE_JOIN THEN
      ASM_REWRITE_TAC [← GSYM hj_line] THEN MATCH_MP_TAC HJ_SUBSPACE_SUBST THEN
      EXISTS_TAC (← q r"Ni:num") THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!u. hj_subst k (hj_join k n1 M (hj_subst k Y z2) x) u =
          hj_concat n1 (hj_subst k Y (hj_subst k z2 (hj_take M u)))
            (hj_line_point k x (u M))")
    (fun th => REWRITE_TAC [th]) THENL
     [GEN_TAC THEN REWRITE_TAC [HJ_SUBST_JOIN, HJ_SUBST_SUBST] THEN
      MP_TAC (← ISPECL [← q r"k:num", ← q r"M:num", ← q r"Ni:num", ← q r"z2:num->num",
                        ← q r"u:num->num"] HJ_SUBST_TAKE) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
      FIRST_ASSUM (fun th => tactic_of do
        pure (REWRITE_TAC [← MATCH_MP HJ_SUBST_LINE th])) THEN
      REWRITE_TAC [hj_drop, ADD_CLAUSES],
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [← q r"u:num->num", ← q r"u':num->num"] THEN STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"k:num", ← q r"M:num", ← q r"u:num->num"] HJ_LINE_SUC_CASES) THEN
    MP_TAC (← SPECL [← q r"k:num", ← q r"M:num", ← q r"u':num->num"] HJ_LINE_SUC_CASES) THEN
    ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"(u:num->num) M = k <=> (u':num->num) M = k") ASSUME_TAC THENL
     [ASM_MESON_TAC [HJ_WILDCARDS_EQ_VAR], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"(?i. i < M /\ (u:num->num) i = k) <=> (?i. i < M /\ (u':num->num) i = k)")
    ASSUME_TAC THENL
     [ASM_MESON_TAC [HJ_WILDCARDS_EQ_VAR], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"hj_wildcards k (hj_take M u) = hj_wildcards k (hj_take M u')")
    ASSUME_TAC THENL
     [ASM_SIMP_TAC [HJ_WILDCARDS_TAKE], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"(u:num->num) M = k") THENL
     [SUBGOAL_THEN (← q r"(u':num->num) M = k") ASSUME_TAC THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [← MATCH_MP HJ_LINE_POINT_K (← ASSUME (← q r"hj_line k (n - n1) x"))] THEN
      ASM_CASES_TAC (← q r"?i. i < M /\ (u:num->num) i = k") THENL
       [SUBGOAL_THEN (← q r"hj_line k M (hj_take M u) /\ hj_line k M (hj_take M u')")
        STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
        FIRST_X_ASSUM (MP_TAC o SPECL [← q r"hj_take M (u:num->num)",
                                       ← q r"hj_take M (u':num->num)"] o withR) THEN
        ASM_REWRITE_TAC [] THEN
        DISCH_THEN pairDecode THEN
        SIMP_TAC [],
        SUBGOAL_THEN (← q r"hj_take M (u:num->num) IN hj_cube k M /\
                      hj_take M (u':num->num) IN hj_cube k M")
        STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
        FIRST_X_ASSUM (fun th => tactic_of do
          let ok ← if twoVars th then do
              if mentions (← q r"Y:num->num") th then do
                pure (!(mentions (← q r"r:num") th))
              else pure false
            else pure false
          pure (MATCH_MP_TAC (← liftExcept (check (fun _ => ok) th)))) THEN
        CONJ_TAC THEN MATCH_MP_TAC HJ_SUBST_CUBE THEN EXISTS_TAC (← q r"M:num") THEN
        ASM_REWRITE_TAC []],
      SUBGOAL_THEN (← q r"~((u':num->num) M = k)") ASSUME_TAC THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"hj_line k M (hj_take M u) /\ hj_line k M (hj_take M u')")
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"!v. hj_line k M v
                        ==> hj_line k n1 (hj_subst k Y (hj_subst k z2 v))")
      ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN MATCH_MP_TAC HJ_LINE_SUBST THEN
        EXISTS_TAC (← q r"Ni:num") THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC HJ_LINE_SUBST THEN EXISTS_TAC (← q r"M:num") THEN
        ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"(u:num->num) M < k /\ (u':num->num) M < k")
      STRIP_ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [← q r"(u:num->num) M <= k", ← q r"(u':num->num) M <= k",
          ← q r"~((u:num->num) M = k)", ← q r"~((u':num->num) M = k)"] THEN
        ARITH_TAC,
        ALL_TAC] THEN
      ASM_SIMP_TAC [] THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [← q r"hj_take M (u:num->num)",
                                     ← q r"hj_take M (u':num->num)"] o withR) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN pairDecode THEN
      SIMP_TAC []]))

  let GRAHAM_ROTHSCHILD_LINES ← prove
   r"!k m r. 1 <= k /\ 1 <= r
           ==> ?N. !n c. N <= n /\ (!x. c x < r)
                         ==> ?z. hj_subspace k m n z /\
                                 !u v. hj_line k m u /\ hj_line k m v
                                       ==> c(hj_subst k z u) =
                                           c(hj_subst k z v)"
   (← do
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"m:num", ← q r"r:num"] FOLKMAN) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"M:num") (LABEL_TAC "fk")) THEN
    MP_TAC (← SPECL [← q r"k:num", ← q r"M:num", ← q r"r:num"] HJ_LETTER_INDEP) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC (← q r"N:num") THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [← q r"n:num", ← q r"c:(num->num)->num"] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"n:num", ← q r"c:(num->num)->num"]) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"z:num->num") STRIP_ASSUME_TAC) THEN
    REMOVE_THEN "fk" (MP_TAC o SPECL
     [← q r"M:num", ← q r"\w. (c:(num->num)->num)(hj_subst k z (hj_wlift k w))"]) THEN
    ASM_REWRITE_TAC [LE_REFL] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"d:num->num") (STRIP_ASSUME_TAC o BETA_RULE)) THEN
    EXISTS_TAC (← q r"hj_subst k z (hj_dlift k d)") THEN CONJ_TAC THENL
     [MATCH_MP_TAC HJ_SUBSPACE_SUBST THEN EXISTS_TAC (← q r"M:num") THEN
      ASM_SIMP_TAC [HJ_SUBSPACE_DLIFT],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!u. hj_line k m u
          ==> (c:(num->num)->num)(hj_subst k (hj_subst k z (hj_dlift k d)) u) =
              c(hj_subst k z (hj_wlift k (hj_subst 1 d (hj_wildcards k u))))")
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC [HJ_SUBST_SUBST] THEN
      SUBGOAL_THEN (← q r"hj_line 1 M (hj_subst 1 d (hj_wildcards k u))")
      ASSUME_TAC THENL
       [MATCH_MP_TAC HJ_LINE_SUBST THEN EXISTS_TAC (← q r"m:num") THEN
        ASM_SIMP_TAC [HJ_WILDCARDS_LINE, LE_REFL],
        ALL_TAC] THEN
      FIRST_X_ASSUM (fun th => tactic_of do
        let z ← q r"hj_wildcards"
        pure (MATCH_MP_TAC (← liftExcept
          (check (fun th => can (find_term (fun u => u == z)) (concl th)) th)))) THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC HJ_LINE_SUBST THEN EXISTS_TAC (← q r"m:num") THEN
        ASM_SIMP_TAC [HJ_SUBSPACE_DLIFT],
        ASM_SIMP_TAC [HJ_WLIFT_LINE],
        ASM_SIMP_TAC [HJ_WILDCARDS_DLIFT] THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC HJ_WILDCARDS_WLIFT THEN EXISTS_TAC (← q r"M:num") THEN
        ASM_REWRITE_TAC [] THEN
        MP_TAC (← ISPECL [← q r"1", ← q r"M:num", ← q r"hj_subst 1 d (hj_wildcards k u)"]
                 HJ_LINE_CUBE) THEN
        ASM_REWRITE_TAC [ARITH]],
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC [] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC [HJ_WILDCARDS_LINE]))

  -- @@RETURN BEGIN
  return { HJ_LETTER_INDEP, GRAHAM_ROTHSCHILD_LINES }
  -- @@RETURN END


/- ------------------------------------------------------------------------- -/
/- The density Hales-Jewett property; pigeonhole for densities;              -/
/- multidimensional density Hales-Jewett.  (szemeredi.ml 2611-2800)          -/
/- ------------------------------------------------------------------------- -/

structure DensityHJ where
  -- @@FIELDS
  density_hales_jewett : thm
  HJ_DENSITY_POS_EXISTS : thm
  FINITE_HJ_LINES : thm
  HJ_LINES_NONEMPTY : thm
  HJ_DENSITY_PIGEONHOLE : thm
  MULTIDIM_DENSITY_HALES_JEWETT : thm
  deriving Inhabited

@[nospecialize]
def setupDensityHJ [HolBase] (D : SzemerediDeps) (BWords : Words) (BLines : Lines) (BDensities : Densities) (BHalesJewett : HalesJewett) (BWildcards : Wildcards) :
    ExceptT String IO DensityHJ := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC,
        INDUCT_TAC, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, SET_TAC, new_definition, .. } := D
  let { ADD1, ADD_CLAUSES, CARD_CLAUSES, CARD_EQ_0, CARD_SUBSET, CONTRAPOS_THM,
        EXP_EQ_0, EXTENSION, FINITE_SUBSET, IN_ELIM_THM, IN_SING, LT, LT_NZ,
        MEMBER_NOT_EMPTY, MONO_EXISTS, NOT_EXISTS_THM, .. } := D.core1
  let { NOT_LT, REAL_LE_INV2, REAL_LE_INV_EQ, REAL_LE_LDIV_EQ, REAL_LE_LMUL,
        REAL_LE_RMUL, REAL_LE_TRANS, REAL_LT_DIV, REAL_MUL_ASSOC, REAL_MUL_LZERO,
        REAL_OF_NUM_LE, REAL_OF_NUM_LT, REAL_POS, SUBSET, real_div, .. } := D.core2
  let { CARD_HJ_CUBE, FINITE_HJ_CUBE, HJ_CUBE_0, HJ_SUBSPACE_0, HJ_SUBST_WORD,
        HJ_TAKE_CUBE, IN_HJ_CUBE, hj_drop, .. } := BWords
  let { HJ_LINE_CUBE, HJ_SUBSPACE_JOIN, HJ_SUBST_JOIN, hj_has_line, hj_line, .. } := BLines
  let { CARD_PIGEONHOLE, HJ_DENSITY_CARD, HJ_DENSITY_LE_1, HJ_DENSITY_MARKOV,
        HJ_DENSITY_SECTIONS, .. } := BDensities
  let { HJ_SUBST_LINE, HJ_SUBST_TAKE, .. } := BHalesJewett
  let { HJ_LINE_EQ, .. } := BWildcards
  -- @@SCOPE END

  let density_hales_jewett ← new_definition
   r"density_hales_jewett k <=> !delta. &0 < delta
                    ==> ?N. !n A. N <= n /\ delta <= hj_density k n A
                                  ==> hj_has_line k n A"

  let HJ_DENSITY_POS_EXISTS ← prove
   r"!k n A. &0 < hj_density k n A ==> ?x. x IN hj_cube k n /\ x IN A"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [HJ_DENSITY_CARD] THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC [NOT_EXISTS_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"{x | x IN hj_cube k n /\ x IN A} = {}") SUBST1_TAC THENL
     [ASM SET_TAC [], REWRITE_TAC [CARD_CLAUSES, real_div, REAL_MUL_LZERO]] THEN
    REAL_ARITH_TAC))

  let FINITE_HJ_LINES ← prove
   r"!k n. FINITE {l | hj_line k n l} /\
         CARD {l | hj_line k n l} <= (k + 1) EXP n"
   (← do
    pure (REPEAT GEN_TAC THEN
    SUBGOAL_THEN (← q r"{l | hj_line k n l} SUBSET hj_cube (k + 1) n") ASSUME_TAC THENL
     [REWRITE_TAC [SUBSET, IN_ELIM_THM, HJ_LINE_CUBE], ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC [FINITE_SUBSET, FINITE_HJ_CUBE],
      REWRITE_TAC [← GSYM CARD_HJ_CUBE] THEN MATCH_MP_TAC CARD_SUBSET THEN
      ASM_REWRITE_TAC [FINITE_HJ_CUBE]]))

  let HJ_LINES_NONEMPTY ← prove
   r"!k n. 1 <= n ==> ~({l | hj_line k n l} = {})"
   (← do
    pure (REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, IN_ELIM_THM] THEN
    EXISTS_TAC (← q r"\i:num. if i < n then k else 0") THEN
    REWRITE_TAC [HJ_LINE_EQ, IN_HJ_CUBE] THEN REPEAT CONJ_TAC THENL
     [SIMP_TAC [] THEN ARITH_TAC,
      SIMP_TAC [← GSYM NOT_LT],
      EXISTS_TAC (← q r"0") THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC]))

  let HJ_DENSITY_PIGEONHOLE ← prove
   r"!k l B (g:(num->num)->A) S.
        FINITE S /\ ~(S = {}) /\ (!x. x IN hj_cube k l /\ x IN B ==> g x IN S)
        ==> ?s. s IN S /\
                hj_density k l B <= &(CARD S) *
                hj_density k l {x | x IN B /\ g x = s}"
   (← do
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"g:(num->num)->A", ← q r"{x | x IN hj_cube k l /\ x IN B}",
                      ← q r"S:A->bool"] CARD_PIGEONHOLE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [IN_ELIM_THM] THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC (← q r"hj_cube k l") THEN REWRITE_TAC [FINITE_HJ_CUBE] THEN SET_TAC [],
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"s:A") THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [HJ_DENSITY_CARD] THEN
    SUBGOAL_THEN
     (← q r"{x | x IN hj_cube k l /\ x IN {x | x IN B /\ (g:(num->num)->A) x = s}} =
      {x | x IN {x | x IN hj_cube k l /\ x IN B} /\ g x = s}")
    SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN MESON_TAC [], ALL_TAC] THEN
    REWRITE_TAC [real_div, REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC [REAL_LE_INV_EQ, REAL_POS]))

  /- Multidimensional density Hales-Jewett (DKT Proposition 3). -/

  let MULTIDIM_DENSITY_HALES_JEWETT ← prove
   r"!k. 1 <= k /\ density_hales_jewett k
       ==> !m delta.
             &0 < delta
             ==> ?N. !n A. N <= n /\ delta <= hj_density k n A
                           ==> ?z. hj_subspace k m n z /\
                                   !a. a IN hj_cube k m
                                       ==> hj_subst k z a IN A"
   (← do
    -- right to left: the REAL_ARITH, then the second ARITH_RULE, then the first
    let r1 ← REAL_ARITH (← q r"!a b c d:real. a <= b /\ b <= c * d ==> a <= d * c")
    let a2 ← ARITH_RULE (← q r"1 <= N + 1")
    let a1 ← ARITH_RULE (← q r"1 <= N + 1")
    pure (GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
     [REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"0") THEN REPEAT STRIP_TAC THEN
      MP_TAC (← SPECL [← q r"k:num", ← q r"n:num",
        ← q r"A:(num->num)->bool"] HJ_DENSITY_POS_EXISTS) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"x:num->num") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"x:num->num") THEN
      ASM_REWRITE_TAC [HJ_SUBSPACE_0, HJ_CUBE_0, IN_SING] THEN
      X_GEN_TAC (← q r"a:num->num") THEN DISCH_THEN SUBST1_TAC THEN
      MP_TAC (← ISPECL [← q r"k:num", ← q r"n:num", ← q r"x:num->num", ← q r"\i:num. 0"]
        HJ_SUBST_WORD) THEN
      ASM_SIMP_TAC [],
      ALL_TAC] THEN
    X_GEN_TAC (← q r"delta:real") THEN DISCH_TAC THEN
    MP_TAC (← SPEC (← q r"delta / &2")
           (← REWRITE_RULE [density_hales_jewett]
              (← ASSUME (← q r"density_hales_jewett k")))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"N0:num") (LABEL_TAC "density_hales_jewett")) THEN
    ABBREV_TAC (← q r"M = N0 + 1") THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"delta / &2 / &((k + 1) EXP M)")) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN
      REWRITE_TAC [REAL_OF_NUM_LT, LT_NZ, EXP_EQ_0] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ARITH_TAC],
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"Nm:num") (LABEL_TAC "ih")) THEN
    EXISTS_TAC (← q r"Nm + M:num") THEN
    MAP_EVERY X_GEN_TAC [← q r"n:num", ← q r"A:(num->num)->bool"] THEN STRIP_TAC THEN
    ABBREV_TAC (← q r"l = n - M:num") THEN
    SUBGOAL_THEN (← q r"n = l + M:num") SUBST_ALL_TAC THENL
      [ASM_ARITH_TAC, ALL_TAC] THEN
    ABBREV_TAC
      (← q r"B = {x | delta / &2 <= hj_density k M {y | hj_concat l x y IN A}}") THEN
    SUBGOAL_THEN (← q r"delta / &2 <= hj_density k l B") ASSUME_TAC THENL
     [EXPAND_TAC "B" THEN
      MP_TAC (← ISPECL [← q r"k:num", ← q r"l:num",
                        ← q r"\x. hj_density k M {y | hj_concat l x y IN A}",
                        ← q r"delta:real", ← q r"delta / &2"] HJ_DENSITY_MARKOV) THEN
      ASM_REWRITE_TAC [HJ_DENSITY_LE_1, ← GSYM HJ_DENSITY_SECTIONS] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC, REAL_ARITH_TAC],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!x. x IN B ==> hj_has_line k M {y | hj_concat l x y IN A}")
    ASSUME_TAC THENL
     [EXPAND_TAC "B" THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      REMOVE_THEN "density_hales_jewett" MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
      EXPAND_TAC "M" THEN ARITH_TAC,
      ALL_TAC] THEN
    ABBREV_TAC
     (← q r"lx = \x. @l'. hj_line k M l' /\
                    !a. a < k
                        ==> hj_line_point k l' a IN
                              {y | hj_concat l x y IN A}") THEN
    SUBGOAL_THEN
     (← q r"!x. x IN B ==> hj_line k M (lx x) /\
                     !a. a < k ==> hj_concat l x (hj_line_point k (lx x) a) IN A")
    ASSUME_TAC THENL
     [X_GEN_TAC (← q r"x:num->num") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:num->num")) THEN
      ASM_REWRITE_TAC [hj_has_line] THEN
      DISCH_THEN (MP_TAC o SELECT_RULE) THEN EXPAND_TAC "lx" THEN
      REWRITE_TAC [IN_ELIM_THM],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"k:num", ← q r"l:num", ← q r"B:(num->num)->bool",
                      ← q r"lx:(num->num)->(num->num)", ← q r"{l' | hj_line k M l'}"]
      HJ_DENSITY_PIGEONHOLE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC [FINITE_HJ_LINES, IN_ELIM_THM] THEN
      ASM_SIMP_TAC [HJ_LINES_NONEMPTY] THEN
      EXPAND_TAC "M" THEN SIMP_TAC [HJ_LINES_NONEMPTY, a1],
      ALL_TAC] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"l0:num->num") STRIP_ASSUME_TAC) THEN
    ABBREV_TAC (← q r"C = {x | x IN B /\ (lx:(num->num)->(num->num)) x = l0}") THEN
    SUBGOAL_THEN (← q r"delta / &2 / &((k + 1) EXP M) <= hj_density k l C")
    ASSUME_TAC THENL
     [MP_TAC (← SPECL [← q r"k:num", ← q r"M:num"] FINITE_HJ_LINES) THEN STRIP_TAC THEN
      SUBGOAL_THEN (← q r"&0 < &(CARD {l' | hj_line k M l'})") ASSUME_TAC THENL
       [REWRITE_TAC [REAL_OF_NUM_LT, LT_NZ] THEN
        ASM_MESON_TAC [CARD_EQ_0, HJ_LINES_NONEMPTY, a2],
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"delta / &2 / &(CARD {l' | hj_line k M l'})") THEN CONJ_TAC THENL
       [REWRITE_TAC [real_div] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC [REAL_OF_NUM_LE],
        ASM_SIMP_TAC [REAL_LE_LDIV_EQ] THEN
        MATCH_MP_TAC r1 THEN
        EXISTS_TAC (← q r"hj_density k l B") THEN ASM_REWRITE_TAC []],
      ALL_TAC] THEN
    REMOVE_THEN "ih" (MP_TAC o SPECL [← q r"l:num", ← q r"C:(num->num)->bool"]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC, ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"w:num->num") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"hj_join k l m w l0") THEN CONJ_TAC THENL
     [REWRITE_TAC [ADD1] THEN MATCH_MP_TAC HJ_SUBSPACE_JOIN THEN
      ASM_REWRITE_TAC [← GSYM hj_line],
      ALL_TAC] THEN
    X_GEN_TAC (← q r"a:num->num") THEN DISCH_TAC THEN
    REWRITE_TAC [HJ_SUBST_JOIN] THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (REWRITE_TAC [← MATCH_MP HJ_SUBST_LINE th])) THEN
    MP_TAC (← ISPECL [← q r"k:num", ← q r"m:num", ← q r"l:num", ← q r"w:num->num", ← q r"a:num->num"]
      HJ_SUBST_TAKE) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [hj_drop, ADD_CLAUSES] THEN
    SUBGOAL_THEN (← q r"hj_subst k w (hj_take m a) IN C") MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC HJ_TAKE_CUBE THEN
      EXISTS_TAC (← q r"1") THEN ASM_REWRITE_TAC [← GSYM ADD1],
      ALL_TAC] THEN
    EXPAND_TAC "C" THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (fun th => tactic_of do
      let z ← q r"lx:(num->num)->(num->num)"
      pure (MP_TAC (← SPEC (← q r"hj_subst k w (hj_take m a)") (← liftExcept
        (check (fun th => can (find_term (fun u => u == z)) (concl th) &&
                          is_forall (concl th)) th))))) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC (← q r"(a:num->num) IN hj_cube k (SUC m)") THEN
    REWRITE_TAC [IN_HJ_CUBE] THEN MESON_TAC [LT]))

  -- @@RETURN BEGIN
  return { density_hales_jewett, HJ_DENSITY_POS_EXISTS, FINITE_HJ_LINES,
           HJ_LINES_NONEMPTY, HJ_DENSITY_PIGEONHOLE, MULTIDIM_DENSITY_HALES_JEWETT }
  -- @@RETURN END


/- ------------------------------------------------------------------------- -/
/- Uniform subspaces (DKT Lemma 4).  (szemeredi.ml 2804-3068)                -/
/- ------------------------------------------------------------------------- -/

structure UniformSubspaces where
  -- @@FIELDS
  HJ_CONCAT_ASSOC : thm
  HJ_CONCAT_0 : thm
  FMEAN_SPREAD : thm
  HJ_SECTION_CONCAT : thm
  HJ_SUBSPACE_JOIN_POINT : thm
  HJ_SUBST_JOIN_POINT : thm
  DKT_UNIFORM_STEP : thm
  DKT_LEMMA4 : thm
  deriving Inhabited

@[nospecialize]
def setupUniformSubspaces [HolBase] (D : SzemerediDeps) (BFiniteMeans : FiniteMeans) (BWords : Words) (BLines : Lines) (BDensities : Densities) :
    ExceptT String IO UniformSubspaces := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC,
        INDUCT_TAC, REAL_ARITH, SET_RULE, TAUT, .. } := D
  let { ADD_CLAUSES, CARD_DELETE, ETA_AX, EXP_1, FINITE_DELETE, FUN_EQ_THM, HAS_SIZE_0,
        HAS_SIZE_CARD, IN_DELETE, IN_ELIM_THM, IN_SING, LE_EXP, LE_REFL, LE_TRANS, LT,
        MONO_EXISTS, MULT_CLAUSES, NOT_FORALL_THM, NOT_IMP, .. } := D.core1
  let { REAL_ADD_RDISTRIB, REAL_ADD_RID, REAL_ARCH_SIMPLE, REAL_DIV_RMUL, REAL_LE_MUL,
        REAL_LE_RDIV_EQ, REAL_LE_REFL, REAL_LE_RMUL, REAL_LE_TRANS, REAL_LT_DIV,
        REAL_LT_IMP_LE, REAL_LT_IMP_NZ, REAL_MUL_LID, REAL_MUL_LINV, REAL_MUL_LZERO,
        REAL_NOT_LE, REAL_OF_NUM_ADD, REAL_OF_NUM_LE, REAL_OF_NUM_LT, REAL_OF_NUM_POW,
        REAL_OF_NUM_SUB, REAL_OF_NUM_SUC, REAL_POS, SUB_0, SUM_DELETE, .. } := D.core2
  let { fmean, .. } := BFiniteMeans
  let { CARD_HJ_CUBE, FINITE_HJ_CUBE, HJ_CONCAT_CUBE, HJ_CUBE_0, HJ_SUBSPACE_0,
        HJ_SUBSPACE_IDENTITY, HJ_SUBST_IDENTITY, HJ_SUBST_WORD, hj_concat, hj_drop, .. } := BWords
  let { HJ_SUBSPACE_JOIN, HJ_SUBST_JOIN, .. } := BLines
  let { FMEAN_EXISTS_GE, HJ_DENSITY_LE_1, HJ_DENSITY_POS, HJ_DENSITY_SECTIONS, .. } := BDensities
  -- @@SCOPE END

  let HJ_CONCAT_ASSOC ← prove
   r"!L m x a y. hj_concat L x (hj_concat m a y) =
               hj_concat (L + m) (hj_concat L x a) y"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [hj_concat, FUN_EQ_THM] THEN
    X_GEN_TAC (← q r"i:num") THEN
    ASM_CASES_TAC (← q r"i:num < L") THEN
      ASM_SIMP_TAC [← ARITH_RULE (← q r"i < L ==> i < L + m:num")] THEN
    ASM_CASES_TAC (← q r"i:num < L + m") THEN ASM_REWRITE_TAC [] THENL
     [COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC,
      COND_CASES_TAC THENL [ASM_ARITH_TAC, AP_TERM_TAC THEN ASM_ARITH_TAC]]))

  let HJ_CONCAT_0 ← prove
   r"!x y. hj_concat 0 x y = y"
   (REWRITE_TAC [hj_concat, LT, SUB_0, ETA_AX])

  let FMEAN_SPREAD ← prove
   r"!(X:A->bool) f mu e y0.
        FINITE X /\ y0 IN X /\ 2 <= CARD X /\ mu <= fmean X f /\
        f y0 < mu - e /\ &0 <= e
        ==> ?y1. y1 IN X /\ mu + e / (&(CARD X) - &1) <= f y1"
   (← do
    -- right to left: the second REAL_ARITH, the ARITH_RULE, the first REAL_ARITH
    let r2 ← REAL_ARITH
     (← q r"!m s c f0 e. m * c <= s /\ f0 < m - e
                     ==> m * (c - &1) + e <= s - f0")
    let a1 ← ARITH_RULE (← q r"2 <= n ==> 1 <= n")
    let r1 ← REAL_ARITH (← q r"&1 < x ==> &0 < x")
    pure (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"&1 < &(CARD(X:A->bool))") ASSUME_TAC THENL
     [REWRITE_TAC [REAL_OF_NUM_LT] THEN ASM_ARITH_TAC, ALL_TAC] THEN
    SUBGOAL_THEN (← q r"mu * &(CARD(X:A->bool)) <= sum X f") ASSUME_TAC THENL
     [UNDISCH_TAC (← q r"mu <= fmean (X:A->bool) f") THEN
      REWRITE_TAC [fmean] THEN
      ASM_SIMP_TAC [REAL_LE_RDIV_EQ, r1],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"sum (X DELETE (y0:A)) f = sum X f - f y0 /\
      CARD(X DELETE (y0:A)) = CARD X - 1")
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC [SUM_DELETE, CARD_DELETE], ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"X DELETE (y0:A)", ← q r"f:A->real",
                      ← q r"mu + e / (&(CARD(X:A->bool)) - &1)"] FMEAN_EXISTS_GE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC [FINITE_DELETE] THEN CONJ_TAC THENL
       [REWRITE_TAC [← GSYM HAS_SIZE_0] THEN
        DISCH_THEN (MP_TAC o MATCH_MP HAS_SIZE_CARD) THEN
        ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC,
        ALL_TAC] THEN
      ASM_REWRITE_TAC [fmean] THEN
      SUBGOAL_THEN (← q r"&(CARD(X:A->bool) - 1) = &(CARD X) - &1") SUBST1_TAC THENL
       [ASM_SIMP_TAC [REAL_OF_NUM_SUB, a1],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"&0 < &(CARD(X:A->bool)) - &1") ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      ASM_SIMP_TAC [REAL_LE_RDIV_EQ] THEN REWRITE_TAC [REAL_ADD_RDISTRIB] THEN
      ASM_SIMP_TAC [REAL_DIV_RMUL, REAL_LT_IMP_NZ] THEN
      MATCH_MP_TAC r2 THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC [IN_DELETE]))

  let HJ_SECTION_CONCAT ← prove
   r"!L m x a A. {y | hj_concat m a y IN {y | hj_concat L x y IN A}} =
               {y | hj_concat (L + m) (hj_concat L x a) y IN A}"
   (REWRITE_TAC [IN_ELIM_THM, HJ_CONCAT_ASSOC])

  let HJ_SUBSPACE_JOIN_POINT ← prove
   r"!k m L x. 1 <= k /\ x IN hj_cube k L
             ==> hj_subspace k m (L + m) (hj_join k L 0 x (hj_identity k m))"
   (← do
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"k:num", ← q r"L:num", ← q r"0", ← q r"m:num", ← q r"m:num", ← q r"x:num->num",
                      ← q r"hj_identity k m"] HJ_SUBSPACE_JOIN) THEN
    ASM_SIMP_TAC [HJ_SUBSPACE_0, HJ_SUBSPACE_IDENTITY, ADD_CLAUSES]))

  let HJ_SUBST_JOIN_POINT ← prove
   r"!k m L x a. 1 <= k /\ x IN hj_cube k L /\ a IN hj_cube k m
               ==> hj_subst k (hj_join k L 0 x (hj_identity k m)) a =
                   hj_concat L x a"
   (← do
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [HJ_SUBST_JOIN] THEN
    SUBGOAL_THEN (← q r"hj_drop 0 (a:num->num) = a") SUBST1_TAC THENL
     [REWRITE_TAC [hj_drop, ADD_CLAUSES, ETA_AX], ALL_TAC] THEN
    ASM_MESON_TAC [HJ_SUBST_WORD, HJ_SUBST_IDENTITY]))

  let DKT_UNIFORM_STEP ← prove
   r"!k m n L x A e.
        2 <= k /\ 1 <= m /\ L + m <= n /\ x IN hj_cube k L /\ &0 <= e /\
        hj_density k n A <= hj_density k (n - L) {y | hj_concat L x y IN A}
        ==> (!a. a IN hj_cube k m
                 ==> hj_density k n A - e <=
                     hj_density k (n - (L + m))
                          {y | hj_concat (L + m) (hj_concat L x a) y IN A}) \/
            (?a. a IN hj_cube k m /\
                 hj_density k (n - L) {y | hj_concat L x y IN A} +
                 e / (&(k EXP m) - &1) <=
                 hj_density k (n - (L + m))
                      {y | hj_concat (L + m) (hj_concat L x a) y IN A})"
   (← do
    pure (REPEAT STRIP_TAC THEN
    ABBREV_TAC (← q r"mu = hj_density k (n - L) {y | hj_concat L x y IN A}") THEN
    SUBGOAL_THEN
     (← q r"mu = fmean (hj_cube k m)
            (\a. hj_density k (n - (L + m))
                   {y | hj_concat (L + m) (hj_concat L x a) y IN A})")
    ASSUME_TAC THENL
     [EXPAND_TAC "mu" THEN
      SUBGOAL_THEN (← q r"n - L = m + (n - (L + m)):num") SUBST1_TAC THENL
       [ASM_ARITH_TAC, REWRITE_TAC [HJ_DENSITY_SECTIONS, HJ_SECTION_CONCAT]],
      ALL_TAC] THEN
    ASM_CASES_TAC
     (← q r"!a. a IN hj_cube k m
          ==> hj_density k n A - e <=
              hj_density k (n - (L + m))
                {y | hj_concat (L + m) (hj_concat L x a) y IN A}") THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o REWRITE_RULE [NOT_FORALL_THM, NOT_IMP,
      REAL_NOT_LE]) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"a0:num->num") STRIP_ASSUME_TAC) THEN
    MP_TAC (← ISPECL
     [← q r"hj_cube k m",
      ← q r"\a. hj_density k (n - (L + m))
             {y | hj_concat (L + m) (hj_concat L x a) y IN A}",
      ← q r"mu:real", ← q r"e:real", ← q r"a0:num->num"] FMEAN_SPREAD) THEN
    ASM_REWRITE_TAC [FINITE_HJ_CUBE, CARD_HJ_CUBE, REAL_LE_REFL] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"k EXP 1") THEN
        ASM_REWRITE_TAC [EXP_1, LE_EXP] THEN ASM_ARITH_TAC,
        BETA_TAC THEN MATCH_MP_TAC (← REAL_ARITH
         (← q r"!x y z e. x < y - e /\ y <= z ==> x < z - e")) THEN
        EXISTS_TAC (← q r"hj_density k n A") THEN CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC,
          UNDISCH_TAC (← q r"hj_density k n A <= mu") THEN ASM_REWRITE_TAC []]],
      REWRITE_TAC [REAL_OF_NUM_POW]]))

  let DKT_LEMMA4 ← prove
   r"!k m e. 2 <= k /\ 1 <= m /\ &0 < e
           ==> ?N. !n A. N <= n
                         ==> ?l z. l < n /\ hj_subspace k m l z /\
                                   !a. a IN hj_cube k m
                                       ==> hj_density k n A - e <=
                                           hj_density k (n - l)
                                                {y | hj_concat l (hj_subst k
                                                  z a) y IN A}"
   (← do
    -- right to left: from the last rule (REAL_ARITH) to the first
    let r4 ← REAL_ARITH
     (← q r"!a b c. &0 <= a /\ b <= &1 /\ &1 < c ==> ~(a + c <= b)")
    let t1 ← TAUT (← q r"~p ==> p ==> q")
    let r3 ← REAL_ARITH
     (← q r"!d0 s1 s2 tr r. d0 + tr <= s1 /\ s1 + r <= s2
                          ==> d0 + (tr + r) <= s2")
    let a1 ← ARITH_RULE (← q r"SUC t * m = t * m + m")
    let r2 ← REAL_ARITH (← q r"!a b c. &0 <= b /\ a + b <= c ==> a <= c")
    let s1 ← SET_RULE (← q r"!A:(num->num)->bool. {y | y IN A} = A")
    let r1 ← REAL_ARITH (← q r"&2 <= x ==> &0 < x - &1")
    -- `check (fun th -> can (find_term ((=) `rho:real`)) (concl th) &&
    -- is_binary "real_le" (concl th) && can (find_term ((=) `x:num->num`))
    -- (concl th))`, the quotations parsed as `&&` reaches them
    let rhoX : thm → ExceptT String IO thm := fun th => do
      let rho ← q r"rho:real"
      let ok ← if can (find_term (fun u => u == rho)) (concl th) &&
                  is_binary "real_le" (concl th) then do
          let x ← q r"x:num->num"
          pure (can (find_term (fun u => u == x)) (concl th))
        else pure false
      liftExcept (check (fun _ => ok) th)
    pure (REPEAT STRIP_TAC THEN
    ABBREV_TAC (← q r"rho = e / (&(k EXP m) - &1)") THEN
    SUBGOAL_THEN (← q r"&0 < rho") ASSUME_TAC THENL
     [EXPAND_TAC "rho" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC r1 THEN
      REWRITE_TAC [REAL_OF_NUM_LE] THEN MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC (← q r"k EXP 1") THEN ASM_REWRITE_TAC [EXP_1, LE_EXP] THEN
        ASM_ARITH_TAC,
      ALL_TAC] THEN
    X_CHOOSE_TAC (← q r"NT:num") (← SPEC (← q r"inv(rho:real)") REAL_ARCH_SIMPLE) THEN
    EXISTS_TAC (← q r"(NT + 1) * m + 1") THEN
    MAP_EVERY X_GEN_TAC [← q r"n:num", ← q r"A:(num->num)->bool"] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     (← q r"!t. t * m <= n
          ==> (?l z. l <= t * m /\ hj_subspace k m l z /\
                     !a. a IN hj_cube k m
                         ==> hj_density k n A - e <=
                             hj_density k (n - l)
                               {y | hj_concat l (hj_subst k z a) y IN A}) \/
              (?x. x IN hj_cube k (t * m) /\
                   hj_density k n A + &t * rho <=
                   hj_density k (n - t * m) {y | hj_concat (t * m) x y IN A})")
    MP_TAC THENL
     [INDUCT_TAC THENL
       [DISCH_TAC THEN DISJ2_TAC THEN EXISTS_TAC (← q r"(\i. 0):num->num") THEN
        REWRITE_TAC [MULT_CLAUSES, HJ_CUBE_0, IN_SING, HJ_CONCAT_0, SUB_0] THEN
        REWRITE_TAC [REAL_MUL_LZERO, REAL_ADD_RID,
          s1,
                    REAL_LE_REFL],
        ALL_TAC] THEN
      DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o check (fun th => is_imp (concl th))) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC (← q r"SUC t * m <= n") THEN REWRITE_TAC [MULT_CLAUSES] THEN
        ARITH_TAC,
        ALL_TAC] THEN
      STRIP_TAC THENL
       [DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [← q r"l:num", ← q r"z:num->num"] THEN
        ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"l <= t * m:num") THEN
        REWRITE_TAC [MULT_CLAUSES] THEN ARITH_TAC,
        ALL_TAC] THEN
      MP_TAC (← ISPECL [← q r"k:num", ← q r"m:num", ← q r"n:num", ← q r"t * m:num", ← q r"x:num->num",
                        ← q r"A:(num->num)->bool", ← q r"e:real"] DKT_UNIFORM_STEP) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
         [UNDISCH_TAC (← q r"SUC t * m <= n") THEN REWRITE_TAC [MULT_CLAUSES] THEN
          ARITH_TAC,
          ASM_REAL_ARITH_TAC,
          MATCH_MP_TAC r2 THEN
          EXISTS_TAC (← q r"&t * (rho:real)") THEN ASM_SIMP_TAC [REAL_LE_MUL, REAL_POS,
                                                   REAL_LT_IMP_LE]],
        ALL_TAC] THEN
      REWRITE_TAC [a1] THEN STRIP_TAC THENL
       [DISJ1_TAC THEN
        MAP_EVERY EXISTS_TAC [← q r"t * m + m:num",
          ← q r"hj_join k (t * m) 0 x (hj_identity k m)"] THEN
        REWRITE_TAC [LE_REFL] THEN CONJ_TAC THENL
         [MATCH_MP_TAC HJ_SUBSPACE_JOIN_POINT THEN ASM_REWRITE_TAC [] THEN
           ASM_ARITH_TAC,
          X_GEN_TAC (← q r"a:num->num") THEN DISCH_TAC THEN
          MP_TAC (← ISPECL [← q r"k:num", ← q r"m:num", ← q r"t * m:num", ← q r"x:num->num",
                            ← q r"a:num->num"] HJ_SUBST_JOIN_POINT) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC, ALL_TAC] THEN
          DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC []],
        DISJ2_TAC THEN EXISTS_TAC (← q r"hj_concat (t * m) x a") THEN CONJ_TAC THENL
         [MATCH_MP_TAC HJ_CONCAT_CUBE THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
        REWRITE_TAC [← GSYM REAL_OF_NUM_SUC, REAL_ADD_RDISTRIB, REAL_MUL_LID] THEN
        MATCH_MP_TAC r3 THEN
        EXISTS_TAC
          (← q r"hj_density k (n - t * m) {y | hj_concat (t * m) x y IN A}") THEN
        EXPAND_TAC "rho" THEN ASM_REWRITE_TAC []],
      ALL_TAC] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"NT + 1")) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [← q r"l:num", ← q r"z:num->num"] THEN ASM_REWRITE_TAC [] THEN
      ASM_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"&1 <= &NT * (rho:real)") ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"inv(rho:real) * rho") THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC [REAL_MUL_LINV, REAL_LT_IMP_NZ, REAL_LE_REFL],
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC [REAL_LT_IMP_LE]],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o rhoX) THEN
    MATCH_MP_TAC t1 THEN
    MATCH_MP_TAC r4 THEN
    REWRITE_TAC [HJ_DENSITY_POS, HJ_DENSITY_LE_1] THEN
    REWRITE_TAC [← GSYM REAL_OF_NUM_ADD, REAL_ADD_RDISTRIB, REAL_MUL_LID] THEN
    ASM_REAL_ARITH_TAC))

  -- @@RETURN BEGIN
  return { HJ_CONCAT_ASSOC, HJ_CONCAT_0, FMEAN_SPREAD, HJ_SECTION_CONCAT,
           HJ_SUBSPACE_JOIN_POINT, HJ_SUBST_JOIN_POINT, DKT_UNIFORM_STEP, DKT_LEMMA4 }
  -- @@RETURN END


/- ------------------------------------------------------------------------- -/
/- Subspaces with all small points in A (DKT Corollary 5).                   -/
/- (szemeredi.ml 3074-3199)                                                  -/
/- ------------------------------------------------------------------------- -/

structure DKTCor5 where
  -- @@FIELDS
  FMEAN_SWAP2 : thm
  HJ_CUBE_MONO_IN : thm
  DKT_COR5 : thm
  deriving Inhabited

@[nospecialize]
def setupDKTCor5 [HolBase] (D : SzemerediDeps) (BFiniteMeans : FiniteMeans) (BWords : Words) (BLines : Lines) (BDensities : Densities) (BDensityHJ : DensityHJ) (BUniformSubspaces : UniformSubspaces) :
    ExceptT String IO DKTCor5 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_REAL_ARITH_TAC, MESON_TAC, REAL_RING, .. } := D
  let { ETA_AX, IN_ELIM_THM, MONO_EXISTS, .. } := D.core1
  let { REAL_EQ_IMP_LE, REAL_LE_TRANS, SUBSET, SUM_RMUL, SUM_SWAP, real_div, .. } := D.core2
  let { FMEAN_CONST, FMEAN_LE, fmean, .. } := BFiniteMeans
  let { FINITE_HJ_CUBE, HJ_CUBE_MONO, HJ_CUBE_NONEMPTY, HJ_SUBSPACE_0,
        HJ_SUBSPACE_SUBST, HJ_SUBST_SUBST, HJ_SUBST_WORD, .. } := BWords
  let { HJ_SUBSPACE_JOIN, HJ_SUBSPACE_LIFT, HJ_SUBST_JOIN, HJ_SUBST_LIFT, .. } := BLines
  let { FMEAN_EXISTS_GE, hj_density, .. } := BDensities
  let { MULTIDIM_DENSITY_HALES_JEWETT, .. } := BDensityHJ
  let { DKT_LEMMA4, .. } := BUniformSubspaces
  -- @@SCOPE END

  let FMEAN_SWAP2 ← prove
   r"!(X:A->bool) (Y:B->bool) f.
        FINITE X /\ FINITE Y
        ==> fmean X (\x. fmean Y (\y. f x y)) =
            fmean Y (\y. fmean X (\x. f x y))"
   (← do
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [fmean, real_div, SUM_RMUL] THEN
    MATCH_MP_TAC (← REAL_RING
     (← q r"!S S' a b:real. S = S' ==> (S * a) * b = (S' * b) * a")) THEN
    MP_TAC (← ISPECL [← q r"f:A->B->real", ← q r"X:A->bool", ← q r"Y:B->bool"] SUM_SWAP) THEN
    ASM_REWRITE_TAC [] THEN REWRITE_TAC [ETA_AX]))

  let HJ_CUBE_MONO_IN ← prove
   r"!k k' n x. k <= k' /\ x IN hj_cube k n ==> x IN hj_cube k' n"
   (MESON_TAC [HJ_CUBE_MONO, SUBSET])

  let DKT_COR5 ← prove
   r"!k. 1 <= k /\ density_hales_jewett k
       ==> !m delta.
             1 <= m /\ &0 < delta
             ==> ?N. !n A. N <= n /\ delta <= hj_density (k + 1) n A
                           ==> ?z. hj_subspace (k + 1) m n z /\
                                   !a. a IN hj_cube k m
                                       ==> hj_subst (k + 1) z a IN A"
   (← do
    -- right to left: the ARITH_RULEs from the sixth to the first
    let a6 ← ARITH_RULE (← q r"1 <= k + 1")
    let a5 ← ARITH_RULE (← q r"1 <= k + 1")
    let a4 ← ARITH_RULE (← q r"1 <= k + 1")
    let a3 ← ARITH_RULE (← q r"m = m + 0")
    let a2 ← ARITH_RULE (← q r"M0 <= M0 + 1")
    let a1 ← ARITH_RULE (← q r"1 <= k ==> 1 <= k + 1")
    pure (GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
    MP_TAC (← SPEC (← q r"k:num") MULTIDIM_DENSITY_HALES_JEWETT) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o SPECL [← q r"m:num", ← q r"delta / &2"]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"M0:num") (LABEL_TAC "mdhj")) THEN
    MP_TAC (← SPECL [← q r"k + 1", ← q r"M0 + 1", ← q r"delta / &2"] DKT_LEMMA4) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL [ASM_ARITH_TAC, ARITH_TAC, ASM_REAL_ARITH_TAC],
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"N:num") THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [← q r"n:num", ← q r"A:(num->num)->bool"] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"n:num", ← q r"A:(num->num)->bool"]) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"l:num") (X_CHOOSE_THEN (← q r"w:num->num")
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN
     (← q r"?y0. y0 IN hj_cube (k + 1) (n - l) /\
           delta / &2 <=
           hj_density k (M0 + 1)
             {b | hj_concat l (hj_subst (k + 1) w b) y0 IN A}")
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC FMEAN_EXISTS_GE THEN
      REWRITE_TAC [FINITE_HJ_CUBE] THEN
      ASM_SIMP_TAC [HJ_CUBE_NONEMPTY, a1] THEN
      REWRITE_TAC [hj_density, IN_ELIM_THM] THEN
      MP_TAC (← BETA_RULE (← ISPECL
       [← q r"hj_cube k (M0 + 1)", ← q r"hj_cube (k + 1) (n - l)",
        ← q r"\b y. if hj_concat l (hj_subst (k + 1) w b) y IN A then &1 else &0"]
       FMEAN_SWAP2)) THEN
      REWRITE_TAC [FINITE_HJ_CUBE] THEN
      DISCH_THEN (fun th => tactic_of do pure (ONCE_REWRITE_TAC [← GSYM th])) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"fmean (hj_cube k (M0 + 1)) (\b. delta / &2)") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC FMEAN_CONST THEN
        ASM_SIMP_TAC [FINITE_HJ_CUBE, HJ_CUBE_NONEMPTY],
        ALL_TAC] THEN
      MATCH_MP_TAC FMEAN_LE THEN REWRITE_TAC [FINITE_HJ_CUBE] THEN
      X_GEN_TAC (← q r"b:num->num") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"b:num->num")) THEN ANTS_TAC THENL
       [MATCH_MP_TAC HJ_CUBE_MONO_IN THEN
        EXISTS_TAC (← q r"k:num") THEN ASM_REWRITE_TAC [] THEN ARITH_TAC,
        ALL_TAC] THEN
      DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"hj_density (k + 1) n A - delta / &2") THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC,
        UNDISCH_TAC
         (← q r"hj_density (k + 1) n A - delta / &2 <=
          hj_density (k + 1) (n - l)
            {y | hj_concat l (hj_subst (k + 1) w b) y IN A}") THEN
        REWRITE_TAC [hj_density, IN_ELIM_THM]],
      ALL_TAC] THEN
    REMOVE_THEN "mdhj" (MP_TAC o SPECL
     [← q r"M0 + 1", ← q r"{b | hj_concat l (hj_subst (k + 1) w b) y0 IN A}"]) THEN
    ASM_REWRITE_TAC [a2, IN_ELIM_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"u:num->num") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"hj_join (k + 1) l m (hj_subst (k + 1) w (hj_lift k u)) y0") THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN (← q r"n = l + (n - l):num") SUBST1_TAC THENL
       [ASM_ARITH_TAC, ALL_TAC] THEN
      GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV o RAND_CONV)
       [a3] THEN
      MATCH_MP_TAC HJ_SUBSPACE_JOIN THEN
      ASM_REWRITE_TAC [HJ_SUBSPACE_0, a4] THEN
      MATCH_MP_TAC HJ_SUBSPACE_SUBST THEN EXISTS_TAC (← q r"M0 + 1") THEN
      ASM_SIMP_TAC [HJ_SUBSPACE_LIFT, a5],
      ALL_TAC] THEN
    X_GEN_TAC (← q r"a:num->num") THEN DISCH_TAC THEN
    REWRITE_TAC [HJ_SUBST_JOIN, HJ_SUBST_SUBST, HJ_SUBST_LIFT] THEN
    MP_TAC (← ISPECL [← q r"k + 1", ← q r"n - l:num", ← q r"y0:num->num", ← q r"hj_drop m a"]
      HJ_SUBST_WORD) THEN
    ASM_REWRITE_TAC [a6] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC []))

  -- @@RETURN BEGIN
  return { FMEAN_SWAP2, HJ_CUBE_MONO_IN, DKT_COR5 }
  -- @@RETURN END


/- ------------------------------------------------------------------------- -/
/- Good lines (DKT Lemma 7).  (szemeredi.ml 3175-3450)                       -/
/- ------------------------------------------------------------------------- -/

structure GoodLines where
  -- @@FIELDS
  DKT_GOOD_LINE : thm
  HJ_SUBSPACE_MONO_LENGTH : thm
  DKT_LEMMA7 : thm
  deriving Inhabited

@[nospecialize]
def setupGoodLines [HolBase] (D : SzemerediDeps) (BFiniteMeans : FiniteMeans) (BWords : Words) (BLines : Lines) (BDensities : Densities) (BFirstWildcard : FirstWildcard) (BGrahamRothschild : GrahamRothschild) (BDensityHJ : DensityHJ) (BUniformSubspaces : UniformSubspaces) (BDKTCor5 : DKTCor5) :
    ExceptT String IO GoodLines := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC,
        REAL_ARITH, .. } := D
  let { ARITH, ARITH_EQ, CARD_EQ_0, EXP_EQ_0, IN_ELIM_THM, LTE_TRANS, LT_NZ,
        MONO_EXISTS, .. } := D.core1
  let { NOT_LT, REAL_EQ_IMP_LE, REAL_LE_INV2, REAL_LE_LDIV_EQ, REAL_LE_LMUL,
        REAL_LE_TRANS, REAL_LT_DIV, REAL_OF_NUM_LE, REAL_OF_NUM_LT, real_div, .. } := D.core2
  let { FMEAN_CONST, FMEAN_LE, .. } := BFiniteMeans
  let { FINITE_HJ_CUBE, HJ_CUBE_NONEMPTY, HJ_SUBSPACE_IDENTITY, HJ_SUBSPACE_SUBST,
        HJ_SUBST_CUBE, HJ_SUBST_SUBST, IN_HJ_CUBE, hj_subspace, .. } := BWords
  let { HJ_LINE_POINT_SUBST, HJ_LINE_SUBST, HJ_SUBSPACE_LIFT, HJ_SUBST_LIFT,
        hj_has_line, .. } := BLines
  let { HJ_DENSITY_LE_1, HJ_DENSITY_MARKOV, HJ_DENSITY_MONO, hj_density, .. } := BDensities
  let { HJ_SUBST_IN_CUBE, .. } := BFirstWildcard
  let { GRAHAM_ROTHSCHILD_LINES, .. } := BGrahamRothschild
  let { FINITE_HJ_LINES, HJ_DENSITY_PIGEONHOLE, HJ_LINES_NONEMPTY,
        density_hales_jewett, .. } := BDensityHJ
  let { DKT_LEMMA4, .. } := BUniformSubspaces
  let { FMEAN_SWAP2, HJ_CUBE_MONO_IN, .. } := BDKTCor5
  -- @@SCOPE END
  -- `check (fun th -> can (find_term ((=) `v`)) (concl th) && is_forall (concl th))`
  let mentionsAll : term → thm → Bool := fun v th =>
    can (find_term (fun u => u == v)) (concl th) && is_forall (concl th)

  let DKT_GOOD_LINE ← prove
   r"!k m0 N0 delta l n' A (g:(num->num)->(num->num)).
        1 <= k /\ N0 <= m0 /\ 1 <= m0 /\ &0 < delta /\
        (!n B. N0 <= n /\ delta / &4 <= hj_density k n B
               ==> hj_has_line k n B) /\
        (!b. b IN hj_cube k m0
             ==> delta / &2 <=
                 hj_density (k + 1) n' {y | hj_concat l (g b) y IN A})
        ==> ?u. hj_line k m0 u /\
                delta / &4 / &((k + 1) EXP m0) <=
                hj_density (k + 1) n'
                     {y | !a. a < k
                              ==> hj_concat l
                                    (g (hj_line_point k u a)) y IN A}"
   (← do
    -- right to left: the second REAL_ARITH, then the first
    let r2 ← REAL_ARITH (← q r"!a b c d:real. a <= b /\ b <= c * d ==> a <= d * c")
    let r1 ← REAL_ARITH (← q r"!d x. d / &2 - d / &4 <= x ==> d / &4 <= x")
    pure (REPEAT STRIP_TAC THEN
    ABBREV_TAC
     (← q r"B = {y | delta / &4 <=
           hj_density k m0 {b | hj_concat l ((g:(num->num)->(num->num))
       b) y IN A}}") THEN
    SUBGOAL_THEN (← q r"delta / &4 <= hj_density (k + 1) n' B") ASSUME_TAC THENL
     [EXPAND_TAC "B" THEN
      MP_TAC (← ISPECL [← q r"k + 1", ← q r"n':num",
                        ← q r"\y. hj_density k m0 {b | hj_concat l
                          ((g:(num->num)->(num->num)) b) y IN A}",
                        ← q r"delta / &2", ← q r"delta / &4"] HJ_DENSITY_MARKOV) THEN
      REWRITE_TAC [HJ_DENSITY_LE_1] THEN ANTS_TAC THENL
       [CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
        REWRITE_TAC [hj_density, IN_ELIM_THM] THEN
        MP_TAC (← BETA_RULE (← ISPECL
         [← q r"hj_cube k m0", ← q r"hj_cube (k + 1) n'",
          ← q r"\b y. if hj_concat l ((g:(num->num)->(num->num)) b) y IN A
                 then &1 else &0"] FMEAN_SWAP2)) THEN
        REWRITE_TAC [FINITE_HJ_CUBE] THEN
        DISCH_THEN (fun th => tactic_of do pure (ONCE_REWRITE_TAC [← GSYM th])) THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC (← q r"fmean (hj_cube k m0) (\b. delta / &2)") THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
          MATCH_MP_TAC FMEAN_CONST THEN
            ASM_SIMP_TAC [FINITE_HJ_CUBE, HJ_CUBE_NONEMPTY],
          ALL_TAC] THEN
        MATCH_MP_TAC FMEAN_LE THEN REWRITE_TAC [FINITE_HJ_CUBE] THEN
        X_GEN_TAC (← q r"b:num->num") THEN DISCH_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"b:num->num")) THEN
        ASM_REWRITE_TAC [hj_density, IN_ELIM_THM],
        DISCH_TAC THEN MATCH_MP_TAC r1 THEN
        FIRST_ASSUM ACCEPT_TAC],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!y. y IN B ==> hj_has_line k m0 {b | hj_concat l
       ((g:(num->num)->(num->num)) b) y IN A}")
    ASSUME_TAC THENL
     [EXPAND_TAC "B" THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    ABBREV_TAC
     (← q r"ly = \y. @u. hj_line k m0 u /\
                   !a. a < k ==> hj_line_point k u a IN
                       {b | hj_concat l ((g:(num->num)->(num->num)) b)
                          y IN A}") THEN
    SUBGOAL_THEN
     (← q r"!y. y IN B ==> hj_line k m0 (ly y) /\
                     !a. a < k ==> hj_concat l ((g:(num->num)->(num->num))
                                            (hj_line_point k (ly y) a)) y IN A")
    ASSUME_TAC THENL
     [X_GEN_TAC (← q r"y:num->num") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"y:num->num")) THEN
      ASM_REWRITE_TAC [hj_has_line] THEN
      DISCH_THEN (MP_TAC o SELECT_RULE) THEN EXPAND_TAC "ly" THEN
      REWRITE_TAC [IN_ELIM_THM],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"k + 1", ← q r"n':num", ← q r"B:(num->num)->bool",
                      ← q r"ly:(num->num)->(num->num)", ← q r"{u | hj_line k m0 u}"]
      HJ_DENSITY_PIGEONHOLE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC [FINITE_HJ_LINES, HJ_LINES_NONEMPTY, IN_ELIM_THM],
      ALL_TAC] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"u0:num->num") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"u0:num->num") THEN ASM_REWRITE_TAC [] THEN
    MP_TAC (← SPECL [← q r"k:num", ← q r"m0:num"] FINITE_HJ_LINES) THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"&0 < &(CARD {u | hj_line k m0 u})") ASSUME_TAC THENL
     [REWRITE_TAC [REAL_OF_NUM_LT, LT_NZ] THEN
      ASM_MESON_TAC [CARD_EQ_0, HJ_LINES_NONEMPTY],
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"hj_density (k + 1) n' {y | y IN B /\ ly y = (u0:num->num)}") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"delta / &4 / &(CARD {u | hj_line k m0 u})") THEN CONJ_TAC THENL
       [REWRITE_TAC [real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC [REAL_OF_NUM_LE],
        ASM_SIMP_TAC [REAL_LE_LDIV_EQ] THEN
        MATCH_MP_TAC r2 THEN
        EXISTS_TAC (← q r"hj_density (k + 1) n' B") THEN ASM_REWRITE_TAC []],
      MATCH_MP_TAC HJ_DENSITY_MONO THEN REWRITE_TAC [IN_ELIM_THM] THEN
      X_GEN_TAC (← q r"y:num->num") THEN STRIP_TAC THEN
      FIRST_X_ASSUM (fun th => tactic_of do
        let v ← q r"ly:(num->num)->(num->num)"
        pure (MP_TAC (← SPEC (← q r"y:num->num")
          (← liftExcept (check (mentionsAll v) th))))) THEN
      ASM_REWRITE_TAC [] THEN SIMP_TAC []]))

  let HJ_SUBSPACE_MONO_LENGTH ← prove
   r"!k m n n' z. 1 <= k /\ n <= n' /\ hj_subspace k m n z
                ==> hj_subspace k m n' z"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [hj_subspace, IN_HJ_CUBE] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"i:num < n") THEN
      ASM_SIMP_TAC [] THEN
      SUBGOAL_THEN (← q r"(z:num->num) i = 0") SUBST1_TAC THENL
       [ASM_MESON_TAC [NOT_LT], ASM_ARITH_TAC],
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC,
      ASM_MESON_TAC [LTE_TRANS]]))

  let DKT_LEMMA7 ← prove
   r"!k delta.
        1 <= k /\ density_hales_jewett k /\ &0 < delta
        ==> ?m0 theta.
              1 <= m0 /\ &0 < theta /\
              !m eps.
                m0 <= m /\ &0 < eps /\ eps <= delta / &2
                ==> ?N. !n A rho.
                      N <= n /\ delta <= rho /\ rho <= hj_density (k + 1) n A
                      ==> ?l U.
                            l < n /\ hj_subspace (k + 1) m l U /\
                            (!a. a IN hj_cube (k + 1) m
                                 ==> rho - eps <=
                                     hj_density (k + 1) (n - l)
                                       {y | hj_concat l (hj_subst (k + 1) U
                                         a) y IN A}) /\
                            (!u. hj_line k m u
                                 ==> theta <=
                                     hj_density (k + 1) (n - l)
                                       {y | !a. a < k
                                                ==> hj_concat l
                                                     (hj_subst (k + 1)
                                                       U (hj_line_point k u a))
                                                     y IN A})"
   (← do
    -- right to left: the ARITH_RULEs from the fifth to the first
    let a5 ← ARITH_RULE (← q r"1 <= k + 1")
    let a4 ← ARITH_RULE (← q r"1 <= k + 1")
    let a3 ← ARITH_RULE (← q r"k <= k + 1")
    let a2 ← ARITH_RULE (← q r"N0 <= N0 + 1 /\ 1 <= N0 + 1")
    let a1 ← ARITH_RULE (← q r"Ng <= Ng + 1")
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← SPEC (← q r"delta / &4")
           (← REWRITE_RULE [density_hales_jewett]
              (← ASSUME (← q r"density_hales_jewett k")))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"N0:num") (LABEL_TAC "density_hales_jewett")) THEN
    ABBREV_TAC (← q r"theta = delta / &4 / &((k + 1) EXP (N0 + 1))") THEN
    MAP_EVERY EXISTS_TAC [← q r"N0 + 1", ← q r"theta:real"] THEN
    REPEAT CONJ_TAC THENL
     [ARITH_TAC,
      EXPAND_TAC "theta" THEN MATCH_MP_TAC REAL_LT_DIV THEN
      REWRITE_TAC [REAL_OF_NUM_LT, LT_NZ, EXP_EQ_0] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ARITH_TAC],
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"k:num", ← q r"m:num", ← q r"2"] GRAHAM_ROTHSCHILD_LINES) THEN
    ASM_REWRITE_TAC [ARITH] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"Ng:num") (LABEL_TAC "gr")) THEN
    MP_TAC (← SPECL [← q r"k + 1", ← q r"Ng + 1", ← q r"eps:real"] DKT_LEMMA4) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL [ASM_ARITH_TAC, ARITH_TAC, ASM_REAL_ARITH_TAC],
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"N:num") THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [← q r"n:num", ← q r"A:(num->num)->bool", ← q r"rho:real"] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"n:num", ← q r"A:(num->num)->bool"]) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"l:num") (X_CHOOSE_THEN (← q r"V:num->num")
      STRIP_ASSUME_TAC)) THEN
    REMOVE_THEN "gr" (MP_TAC o SPECL
     [← q r"Ng + 1",
      ← q r"\u. if theta <= hj_density (k + 1) (n - l)
                         {y | !a. a < k
                                  ==> hj_concat l
                                        (hj_subst (k + 1) V
                                           (hj_line_point k u a)) y
                                      IN A}
           then 1 else 0"]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC [a1] THEN GEN_TAC THEN
      COND_CASES_TAC THEN ARITH_TAC,
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"Y:num->num") (STRIP_ASSUME_TAC o BETA_RULE)) THEN
    SUBGOAL_THEN (← q r"hj_subspace k (N0 + 1) m (hj_identity k (N0 + 1))")
    ASSUME_TAC THENL
     [MATCH_MP_TAC HJ_SUBSPACE_MONO_LENGTH THEN EXISTS_TAC (← q r"N0 + 1") THEN
      ASM_SIMP_TAC [HJ_SUBSPACE_IDENTITY],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"k:num", ← q r"N0 + 1", ← q r"N0:num", ← q r"delta:real", ← q r"l:num",
                      ← q r"n - l:num", ← q r"A:(num->num)->bool",
                      ← q r"\b. hj_subst (k + 1) V
                          (hj_subst k
                             (hj_subst k Y (hj_identity k (N0 + 1))) b)"]
      DKT_GOOD_LINE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [a2] THEN
      X_GEN_TAC (← q r"b:num->num") THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"hj_density (k + 1) n A - eps") THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      FIRST_X_ASSUM (fun th => tactic_of do
        let v ← q r"V:num->num"
        pure (MATCH_MP_TAC (← liftExcept (check (mentionsAll v) th)))) THEN
      MATCH_MP_TAC HJ_SUBST_IN_CUBE THEN EXISTS_TAC (← q r"N0 + 1") THEN
      ASM_REWRITE_TAC [a3] THEN CONJ_TAC THENL
       [MATCH_MP_TAC HJ_SUBSPACE_SUBST THEN EXISTS_TAC (← q r"m:num") THEN
        ASM_REWRITE_TAC [],
        MATCH_MP_TAC HJ_CUBE_MONO_IN THEN EXISTS_TAC (← q r"k:num") THEN
        ASM_REWRITE_TAC [] THEN ARITH_TAC],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"u0:num->num")
     (STRIP_ASSUME_TAC o REWRITE_RULE [HJ_SUBST_SUBST])) THEN
    SUBGOAL_THEN
     (← q r"!u. hj_line k m u
          ==> theta <= hj_density (k + 1) (n - l)
                         {y | !a. a < k
                                  ==> hj_concat l (hj_subst (k + 1) V
                                               (hj_line_point k (hj_subst k Y u)
                                                  a)) y IN A}")
    ASSUME_TAC THENL
     [X_GEN_TAC (← q r"u:num->num") THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"hj_line k m (hj_subst k (hj_identity k (N0 + 1)) u0)")
      ASSUME_TAC THENL
       [MATCH_MP_TAC HJ_LINE_SUBST THEN EXISTS_TAC (← q r"N0 + 1") THEN
        ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      FIRST_X_ASSUM (fun th => tactic_of do
        let v ← q r"Y:num->num"
        pure (MP_TAC (← SPECL [← q r"u:num->num",
                               ← q r"hj_subst k (hj_identity k (N0 + 1)) u0"]
          (← liftExcept (check (mentionsAll v) th))))) THEN
      ASM_REWRITE_TAC [HJ_LINE_POINT_SUBST, HJ_SUBST_SUBST] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [ARITH_EQ],
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [← q r"l:num", ← q r"hj_subst (k + 1) V (hj_lift k Y)"] THEN
    ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HJ_SUBSPACE_SUBST THEN EXISTS_TAC (← q r"Ng + 1") THEN
      ASM_SIMP_TAC [HJ_SUBSPACE_LIFT, a4],
      X_GEN_TAC (← q r"a:num->num") THEN DISCH_TAC THEN REWRITE_TAC [HJ_SUBST_SUBST] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"hj_density (k + 1) n A - eps") THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      FIRST_X_ASSUM (fun th => tactic_of do
        let v ← q r"V:num->num"
        let ok ← if mentionsAll v th then do
            let y ← q r"Y:num->num"
            pure (!(can (find_term (fun u => u == y)) (concl th)))
          else pure false
        pure (MATCH_MP_TAC (← liftExcept (check (fun _ => ok) th)))) THEN
      MATCH_MP_TAC HJ_SUBST_CUBE THEN EXISTS_TAC (← q r"m:num") THEN
      ASM_SIMP_TAC [HJ_SUBSPACE_LIFT, a5],
      X_GEN_TAC (← q r"u:num->num") THEN DISCH_TAC THEN
      REWRITE_TAC [HJ_SUBST_SUBST, HJ_SUBST_LIFT] THEN
      REWRITE_TAC [← GSYM HJ_LINE_POINT_SUBST] THEN ASM_SIMP_TAC []]))

  -- @@RETURN BEGIN
  return { DKT_GOOD_LINE, HJ_SUBSPACE_MONO_LENGTH, DKT_LEMMA7 }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- Increment or many lines (DKT Lemma 8).  (szemeredi.ml 3426-3794)          -/
/- ------------------------------------------------------------------------- -/

structure Lemma8 where
  -- @@FIELDS
  FMEAN_REVERSE_MARKOV : thm
  HJ_JOIN_POINT_RIGHT : thm
  HJ_DENSITY_COMMON : thm
  HJ_DENSITY_COMPL : thm
  CARD_RESTRICT_SUM : thm
  DKT_ETA_BOUND : thm
  DKT_LEMMA8 : thm
  deriving Inhabited

@[nospecialize]
def setupLemma8 [HolBase] (D : SzemerediDeps) (BFiniteMeans : FiniteMeans) (BWords : Words) (BLines : Lines) (BDensities : Densities) (BDensityHJ : DensityHJ) (BDKTCor5 : DKTCor5) (BGoodLines : GoodLines) :
    ExceptT String IO Lemma8 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC,
        MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, SET_TAC, .. } := D
  let { ADD_CLAUSES, ARITH, CARD_EQ_0, CARD_SUBSET, CARD_UNION_EQ, DE_MORGAN_THM,
        EQ_TRANS, ETA_AX, EXP_EQ_0, FINITE_SUBSET, FUN_EQ_THM, HAS_SIZE_0,
        HAS_SIZE_CARD, IN_ELIM_THM, IN_INTER, LT_NZ, MONO_EXISTS, NOT_EXISTS_THM, .. } := D.core1
  let { REAL_ADD_RDISTRIB, REAL_EQ_IMP_LE, REAL_INV_0, REAL_LE_DIV, REAL_LE_INV_EQ,
        REAL_LE_LDIV_EQ, REAL_LE_LMUL, REAL_LE_LMUL_EQ, REAL_LE_MUL, REAL_LE_RDIV_EQ,
        REAL_LE_REFL, REAL_LE_TRANS, REAL_LT_DIV, REAL_LT_IMP_LE, REAL_LT_IMP_NZ,
        REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LINV, REAL_MUL_RID, REAL_MUL_RZERO,
        REAL_MUL_SYM, REAL_NOT_LE, REAL_OF_NUM_ADD, REAL_OF_NUM_LE, REAL_OF_NUM_LT,
        REAL_POS, REAL_POW_2, REAL_POW_LE, REAL_POW_LT, SUM_CASES, SUM_CONST, SUM_LE,
        SUM_RESTRICT_SET, real_div, .. } := D.core2
  let { FMEAN_ADD, FMEAN_CONST, FMEAN_LE, FMEAN_LMUL, FMEAN_SUM, fmean, .. } := BFiniteMeans
  let { CARD_HJ_CUBE, FINITE_HJ_CUBE, HJ_CUBE_NONEMPTY, HJ_SUBSPACE_0, HJ_SUBST_WORD, .. } := BWords
  let { HJ_SUBSPACE_JOIN, HJ_SUBST_JOIN, .. } := BLines
  let { HJ_DENSITY_CARD, HJ_DENSITY_MARKOV, HJ_DENSITY_POS, hj_density, .. } := BDensities
  let { FINITE_HJ_LINES, HJ_DENSITY_POS_EXISTS, HJ_LINES_NONEMPTY, .. } := BDensityHJ
  let { FMEAN_SWAP2, .. } := BDKTCor5
  let { DKT_LEMMA7, .. } := BGoodLines
  -- @@SCOPE END
  -- `check (fun th -> can (find_term ((=) `v`)) (concl th) && is_forall (concl th))`
  let mentionsAll : term → thm → Bool := fun v th =>
    can (find_term (fun u => u == v)) (concl th) && is_forall (concl th)
  let mentions : term → thm → Bool := fun v th =>
    can (find_term (fun u => u == v)) (concl th)

  let FMEAN_REVERSE_MARKOV ← prove
   r"!(X:A->bool) f c d t.
        FINITE X /\ ~(X = {}) /\ (!x. x IN X ==> f x <= c) /\
        c - d <= fmean X f /\ t < c
        ==> (c - t) * &(CARD {x | x IN X /\ f x < t}) <= d * &(CARD X)"
   (← do
    -- right to left: the second REAL_ARITH, then the first
    let r2 ← REAL_ARITH (← q r"!c d t s a b. (c - d) * a <= s /\ s <= c * a - (c - t) * b
                  ==> (c - t) * b <= d * a")
    let r1 ← REAL_ARITH (← q r"!a b c t:real. a * t + b * c <= c * (a + b) - (c - t) * a")
    pure (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"&0 < &(CARD(X:A->bool))") ASSUME_TAC THENL
     [REWRITE_TAC [REAL_OF_NUM_LT, LT_NZ] THEN ASM_MESON_TAC [CARD_EQ_0],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(c - d) * &(CARD(X:A->bool)) <= sum X f") ASSUME_TAC THENL
     [UNDISCH_TAC (← q r"c - d <= fmean (X:A->bool) f") THEN
      ASM_SIMP_TAC [fmean, REAL_LE_RDIV_EQ],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"sum (X:A->bool) f <=
      c * &(CARD X) - (c - t) * &(CARD {x | x IN X /\ f x < t})")
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"sum (X:A->bool) (\x. if f x < t then t else c)") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
        COND_CASES_TAC THEN ASM_SIMP_TAC [REAL_LT_IMP_LE],
        ALL_TAC] THEN
      ASM_SIMP_TAC [SUM_CASES] THEN
      SUBGOAL_THEN (← q r"FINITE {x:A | x IN X /\ f x < t} /\
                    FINITE {x:A | x IN X /\ ~(f x < t)}")
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC (← q r"X:A->bool") THEN ASM_REWRITE_TAC [] THEN SET_TAC [],
        ALL_TAC] THEN
      ASM_SIMP_TAC [SUM_CONST] THEN
      SUBGOAL_THEN
       (← q r"&(CARD (X:A->bool)) =
        &(CARD {x | x IN X /\ f x < t}) + &(CARD {x | x IN X /\ ~(f x < t)})")
      SUBST1_TAC THENL
       [REWRITE_TAC [REAL_OF_NUM_ADD] THEN AP_TERM_TAC THEN
        MATCH_MP_TAC (← GSYM CARD_UNION_EQ) THEN ASM_REWRITE_TAC [] THEN SET_TAC [],
        MATCH_ACCEPT_TAC r1],
      ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC r2 THEN
    EXISTS_TAC (← q r"sum (X:A->bool) f") THEN ASM_REWRITE_TAC []))

  let HJ_JOIN_POINT_RIGHT ← prove
   r"!k m l n2 U y. 1 <= k /\ hj_subspace k m l U /\ y IN hj_cube k n2
                  ==> hj_subspace k m (l + n2) (hj_join k l m U y) /\
                      !a. hj_subst k (hj_join k l m U y) a =
                          hj_concat l (hj_subst k U a) y"
   (← do
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [MP_TAC (← ISPECL [← q r"k:num", ← q r"l:num", ← q r"m:num", ← q r"0", ← q r"n2:num",
                        ← q r"U:num->num", ← q r"y:num->num"] HJ_SUBSPACE_JOIN) THEN
      ASM_REWRITE_TAC [HJ_SUBSPACE_0, ADD_CLAUSES],
      GEN_TAC THEN REWRITE_TAC [HJ_SUBST_JOIN] THEN AP_TERM_TAC THEN
      ASM_MESON_TAC [HJ_SUBST_WORD]]))

  let HJ_DENSITY_COMMON ← prove
   r"!k n A B. &1 < hj_density k n A + hj_density k n B
             ==> ?x. x IN hj_cube k n /\ x IN A /\ x IN B"
   (← do
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"k:num", ← q r"n:num", ← q r"A INTER B:(num->num)->bool"]
      HJ_DENSITY_POS_EXISTS) THEN
    REWRITE_TAC [IN_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN
     (← q r"hj_density k n A + hj_density k n B <= &1 +
      hj_density k n (A INTER B:(num->num)->bool)")
    MP_TAC THENL [ALL_TAC, ASM_REAL_ARITH_TAC] THEN
    ASM_CASES_TAC (← q r"k EXP n = 0") THENL
     [ASM_REWRITE_TAC [HJ_DENSITY_CARD, real_div, REAL_INV_0, REAL_MUL_RZERO] THEN
      REAL_ARITH_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [hj_density] THEN
    SUBGOAL_THEN
     (← q r"&1 + fmean (hj_cube k n)
             (\x. if x IN A INTER B then &1 else &0) =
      fmean (hj_cube k n) (\x. &1 + (if x IN A INTER B then &1 else &0))")
    SUBST1_TAC THENL
     [SIMP_TAC [FMEAN_ADD, FINITE_HJ_CUBE] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC FMEAN_CONST THEN
      REWRITE_TAC [FINITE_HJ_CUBE, ← GSYM HAS_SIZE_0] THEN
      DISCH_THEN (MP_TAC o MATCH_MP HAS_SIZE_CARD) THEN
      ASM_REWRITE_TAC [CARD_HJ_CUBE],
      ALL_TAC] THEN
    SIMP_TAC [← GSYM FMEAN_ADD, FINITE_HJ_CUBE] THEN MATCH_MP_TAC FMEAN_LE THEN
    REWRITE_TAC [FINITE_HJ_CUBE, IN_INTER] THEN X_GEN_TAC (← q r"x:num->num") THEN
    DISCH_TAC THEN ASM_CASES_TAC (← q r"(x:num->num) IN A") THEN
    ASM_CASES_TAC (← q r"(x:num->num) IN B") THEN ASM_REWRITE_TAC [] THEN
    REAL_ARITH_TAC))

  let HJ_DENSITY_COMPL ← prove
   r"!k n P. 1 <= k
           ==> hj_density k n {x | ~P x} = &1 - hj_density k n {x | P x}"
   (← do
    let r1 ← REAL_ARITH (← q r"a + b = &1 ==> b = &1 - a")
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [hj_density, IN_ELIM_THM] THEN
    MATCH_MP_TAC r1 THEN
    SIMP_TAC [← GSYM FMEAN_ADD, FINITE_HJ_CUBE] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (← q r"fmean (hj_cube k n) (\x. &1)") THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC,
      MATCH_MP_TAC FMEAN_CONST THEN
        ASM_SIMP_TAC [FINITE_HJ_CUBE, HJ_CUBE_NONEMPTY]]))

  let CARD_RESTRICT_SUM ← prove
   r"!(L:A->bool) P. FINITE L
                   ==> &(CARD {u | u IN L /\ P u}) =
                       sum L (\u. if P u then &1 else &0)"
   (← do
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM SUM_RESTRICT_SET] THEN
    SUBGOAL_THEN (← q r"FINITE {u:A | u IN L /\ P u}") ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"L:A->bool") THEN
      ASM_REWRITE_TAC [] THEN SET_TAC [],
      ASM_SIMP_TAC [SUM_CONST, REAL_MUL_RID]]))

  let DKT_ETA_BOUND ← prove
   r"!e p. &0 < e /\ &0 <= p /\ (&2 * e + e pow 2 / &2) * p <= e pow 2
         ==> p <= e / &2"
   (← do
    let r1 ← REAL_ARITH (← q r"a = b /\ &0 <= c ==> a <= b + c")
    pure (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"e * (&2 * p) <= e * e") MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"(&2 * e + e pow 2 / &2) * p") THEN CONJ_TAC THENL
       [REWRITE_TAC [REAL_ADD_RDISTRIB] THEN
        MATCH_MP_TAC r1 THEN
        CONJ_TAC THENL [REAL_ARITH_TAC, ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC [REAL_POS] THEN
        ASM_SIMP_TAC [REAL_POW_LE, REAL_LT_IMP_LE],
        ASM_REWRITE_TAC [← GSYM REAL_POW_2]],
      ASM_SIMP_TAC [REAL_LE_LMUL_EQ] THEN REAL_ARITH_TAC]))

  let DKT_LEMMA8 ← prove
   r"!k delta.
        1 <= k /\ density_hales_jewett k /\ &0 < delta
        ==> ?m0 theta.
              1 <= m0 /\ &0 < theta /\
              !m eta.
                m0 <= m /\ &0 < eta /\ eta <= &1 /\ eta pow 2 <= delta /\
                eta < theta
                ==> ?N. !n A rho.
                      N <= n /\ delta <= rho /\ rho <= hj_density (k + 1) n A
                      ==> (?X. hj_subspace (k + 1) m n X /\
                               rho + eta pow 2 / &2 <=
                               hj_density (k + 1) m
                                 {a | hj_subst (k + 1) X a IN A}) \/
                          (?W. hj_subspace (k + 1) m n W /\
                               rho - &2 * eta <=
                               hj_density (k + 1) m
                                 {a | hj_subst (k + 1) W a IN A} /\
                               theta / &2 * &(CARD {u | hj_line k m u}) <=
                               &(CARD {u | hj_line k m u /\
                                           !a. a < k
                                               ==> hj_subst (k + 1) W
                                                     (hj_line_point k u a)
                                                   IN A}))"
   (← do
    -- right to left: the eleven rules from the last to the first
    let r11 ← REAL_ARITH
      (← q r"!a b e t. &1 - e / &2 <= a /\ t / &2 <= b /\ e < t ==> &1 < a + b")
    let r10 ← REAL_ARITH (← q r"!d x. d - d / &2 <= x ==> d / &2 <= x")
    let a9 ← ARITH_RULE (← q r"1 <= k + 1")
    let r8 ← REAL_ARITH
      (← q r"!r e c w. ((r + e pow 2 / &2) - (r - &2 * e)) * c <= e pow 2 * w
                ==> (&2 * e + e pow 2 / &2) * c <= e pow 2 * w")
    let r7 ← REAL_ARITH
      (← q r"!p q e. p <= e / &2 ==> &1 - q = p ==> &1 - e / &2 <= q")
    let a6 ← ARITH_RULE (← q r"1 <= k + 1")
    let r5 ← REAL_ARITH (← q r"!r e s. &0 < e /\ &0 <= s ==> r - &2 * e < r + s")
    let a4 ← ARITH_RULE (← q r"1 <= k + 1")
    let a3 ← ARITH_RULE (← q r"1 <= k + 1")
    let a2 ← ARITH_RULE (← q r"l < n ==> l + (n - l) = n:num")
    let a1 ← ARITH_RULE (← q r"1 <= k + 1")
    pure (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP DKT_LEMMA7) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"m0:num") THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"theta:real") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MAP_EVERY X_GEN_TAC [← q r"m:num", ← q r"eta:real"] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"m:num", ← q r"(eta:real) pow 2 / &2"]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC [REAL_OF_NUM_LT, ARITH] THEN
        ASM_SIMP_TAC [REAL_POW_LT],
        ASM_REAL_ARITH_TAC],
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"N:num") THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [← q r"n:num", ← q r"A:(num->num)->bool", ← q r"rho:real"] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"n:num", ← q r"A:(num->num)->bool",
      ← q r"rho:real"]) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"l:num") (X_CHOOSE_THEN (← q r"U:num->num")
      STRIP_ASSUME_TAC)) THEN
    ASM_CASES_TAC
     (← q r"?X. hj_subspace (k + 1) m n X /\
          rho + eta pow 2 / &2 <= hj_density (k + 1) m {a | hj_subst (k + 1)
            X a IN A}") THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o REWRITE_RULE [NOT_EXISTS_THM, DE_MORGAN_THM,
                                          REAL_NOT_LE]) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     (← q r"!y. y IN hj_cube (k + 1) (n - l)
          ==> hj_subspace (k + 1) m n (hj_join (k + 1) l m U y) /\
              !a. hj_subst (k + 1) (hj_join (k + 1) l m U y) a =
                  hj_concat l (hj_subst (k + 1) U a) y")
    ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN DISCH_TAC THEN
      MP_TAC (← ISPECL [← q r"k + 1", ← q r"m:num", ← q r"l:num", ← q r"n - l:num",
                        ← q r"U:num->num", ← q r"y:num->num"] HJ_JOIN_POINT_RIGHT) THEN
      ASM_REWRITE_TAC [a1] THEN
      ASM_SIMP_TAC [a2],
      ALL_TAC] THEN
    ABBREV_TAC
     (← q r"f = \y. hj_density (k + 1) m
                {a | hj_concat l (hj_subst (k + 1) U a) y IN A}") THEN
    SUBGOAL_THEN
     (← q r"!y. y IN hj_cube (k + 1) (n - l) ==>
       (f:(num->num)->real) y < rho + eta pow 2 / &2")
    ASSUME_TAC THENL
     [X_GEN_TAC (← q r"y:num->num") THEN DISCH_TAC THEN EXPAND_TAC "f" THEN
      FIRST_X_ASSUM (fun th => tactic_of do
        let v ← q r"eta:real"
        pure (MP_TAC (← SPEC (← q r"hj_join (k + 1) l m U y")
          (← liftExcept (check (mentionsAll v) th))))) THEN
      ASM_SIMP_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"rho - eta pow 2 / &2 <= fmean (hj_cube (k + 1) (n - l)) f")
    ASSUME_TAC THENL
     [EXPAND_TAC "f" THEN REWRITE_TAC [hj_density, IN_ELIM_THM] THEN
      MP_TAC (← BETA_RULE (← ISPECL
       [← q r"hj_cube (k + 1) (n - l)", ← q r"hj_cube (k + 1) m",
        ← q r"\y a. if hj_concat l (hj_subst (k + 1) U a) y IN A then &1 else &0"]
       FMEAN_SWAP2)) THEN
      REWRITE_TAC [FINITE_HJ_CUBE] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"fmean (hj_cube (k + 1) m) (\a. rho - eta pow 2 / &2)") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC FMEAN_CONST THEN
        ASM_SIMP_TAC [FINITE_HJ_CUBE, HJ_CUBE_NONEMPTY, a3],
        ALL_TAC] THEN
      MATCH_MP_TAC FMEAN_LE THEN REWRITE_TAC [FINITE_HJ_CUBE] THEN
      X_GEN_TAC (← q r"a:num->num") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (fun th => tactic_of do
        let v ← q r"U:num->num"
        let ok ← if mentionsAll v th then do
            let lp ← q r"hj_line_point"
            if !(mentions lp th) then do
              let hj ← q r"hj_join"
              pure (!(mentions hj th))
            else pure false
          else pure false
        pure (MP_TAC (← SPEC (← q r"a:num->num")
          (← liftExcept (check (fun _ => ok) th))))) THEN
      ASM_REWRITE_TAC [hj_density, IN_ELIM_THM],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"&1 - eta / &2 <=
      hj_density (k + 1) (n - l) {y | rho - &2 * eta <= (f:(num->num)->real) y}")
    ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q r"hj_cube (k + 1) (n - l)", ← q r"f:(num->num)->real",
                        ← q r"rho + (eta:real) pow 2 / &2", ← q r"(eta:real) pow 2",
                        ← q r"rho - &2 * eta"]
        FMEAN_REVERSE_MARKOV) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC [FINITE_HJ_CUBE, HJ_CUBE_NONEMPTY, a4,
                      REAL_LT_IMP_LE] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
        MATCH_MP_TAC r5 THEN
        ASM_SIMP_TAC [REAL_LE_DIV, REAL_POW_LE, REAL_LT_IMP_LE, REAL_POS],
        ALL_TAC] THEN
      DISCH_TAC THEN
      MP_TAC (← SPECL [← q r"k + 1", ← q r"n - l:num",
                       ← q r"\y. rho - &2 * eta <= (f:(num->num)->real) y"]
                        HJ_DENSITY_COMPL) THEN
      REWRITE_TAC [a6, REAL_NOT_LE] THEN
      DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← SYM th))) THEN
      MATCH_MP_TAC r7 THEN
      MATCH_MP_TAC DKT_ETA_BOUND THEN REWRITE_TAC [HJ_DENSITY_POS] THEN
      ASM_REWRITE_TAC [HJ_DENSITY_CARD, ← GSYM CARD_HJ_CUBE] THEN
      SUBGOAL_THEN (← q r"&0 < &(CARD(hj_cube (k + 1) (n - l)))") ASSUME_TAC THENL
       [REWRITE_TAC [REAL_OF_NUM_LT, LT_NZ, CARD_HJ_CUBE, EXP_EQ_0]
          THEN ARITH_TAC,
        ALL_TAC] THEN
      REWRITE_TAC [real_div, REAL_MUL_ASSOC] THEN
      ASM_SIMP_TAC [← GSYM real_div, REAL_LE_LDIV_EQ] THEN
      SUBGOAL_THEN
       (← q r"{x | x IN hj_cube (k + 1) (n - l) /\
             x IN {x | (f:(num->num)->real) x < rho - &2 * eta}} =
        {x | x IN hj_cube (k + 1) (n - l) /\ f x < rho - &2 * eta}")
      SUBST1_TAC THENL [SET_TAC [], ALL_TAC] THEN
      MATCH_MP_TAC r8 THEN
      EXISTS_TAC (← q r"rho:real") THEN FIRST_ASSUM ACCEPT_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"&0 < &(CARD {u | hj_line k m u})") ASSUME_TAC THENL
     [REWRITE_TAC [REAL_OF_NUM_LT, LT_NZ] THEN
      MP_TAC (← SPECL [← q r"k:num", ← q r"m:num"] FINITE_HJ_LINES) THEN
      MP_TAC (← SPECL [← q r"k:num", ← q r"m:num"] HJ_LINES_NONEMPTY) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC, MESON_TAC [CARD_EQ_0]],
      ALL_TAC] THEN
    ABBREV_TAC
     (← q r"g = \y. &(CARD {u | hj_line k m u /\
                         !a. a < k
                             ==> hj_concat l
                                   (hj_subst (k + 1) U
                                      (hj_line_point k u a)) y IN A}) /
              &(CARD {u | hj_line k m u})") THEN
    SUBGOAL_THEN
     (← q r"!y. (g:(num->num)->real) y =
          inv(&(CARD {u | hj_line k m u})) *
          sum {u | hj_line k m u}
            (\u. if !a. a < k
                        ==> hj_concat l
                              (hj_subst (k + 1) U (hj_line_point k u a)) y IN A
                 then &1 else &0)")
    ASSUME_TAC THENL
     [GEN_TAC THEN EXPAND_TAC "g" THEN
      ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN REWRITE_TAC [← GSYM real_div] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      MP_TAC (← ISPECL [← q r"{u | hj_line k m u}",
                        ← q r"\u. !a. a < k
                          ==> hj_concat l
                                (hj_subst (k + 1) U
                                   (hj_line_point k u a)) y IN A"]
        CARD_RESTRICT_SUM) THEN
      REWRITE_TAC [FINITE_HJ_LINES, IN_ELIM_THM],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"theta / &2 <= hj_density (k + 1) (n - l) {y | theta / &2 <=
       (g:(num->num)->real) y}")
    ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q r"k + 1", ← q r"n - l:num", ← q r"g:(num->num)->real",
                        ← q r"theta:real", ← q r"theta / &2"] HJ_DENSITY_MARKOV) THEN
      ANTS_TAC THENL
       [REWRITE_TAC [a9] THEN REPEAT CONJ_TAC THENL
         [X_GEN_TAC (← q r"y:num->num") THEN DISCH_TAC THEN EXPAND_TAC "g" THEN
          ASM_SIMP_TAC [REAL_LE_LDIV_EQ, REAL_MUL_LID, REAL_OF_NUM_LE] THEN
          MATCH_MP_TAC CARD_SUBSET THEN
          REWRITE_TAC [FINITE_HJ_LINES] THEN SET_TAC [],
          ASM_REAL_ARITH_TAC,
          GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [← GSYM ETA_AX] THEN
          ASM_REWRITE_TAC [FMEAN_LMUL] THEN
          SIMP_TAC [FMEAN_SUM, FINITE_HJ_CUBE, FINITE_HJ_LINES] THEN
          MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC (← q r"inv(&(CARD {u | hj_line k m u})) *
                      sum {u | hj_line k m u} (\u. theta)") THEN CONJ_TAC THENL
           [SIMP_TAC [SUM_CONST, FINITE_HJ_LINES] THEN
            ASM_SIMP_TAC [REAL_MUL_ASSOC, REAL_MUL_LINV, REAL_LT_IMP_NZ,
                          REAL_MUL_LID, REAL_LE_REFL],
            ALL_TAC] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN
          ASM_SIMP_TAC [REAL_LE_INV_EQ, REAL_LT_IMP_LE] THEN
          MATCH_MP_TAC SUM_LE THEN REWRITE_TAC [FINITE_HJ_LINES, IN_ELIM_THM] THEN
          X_GEN_TAC (← q r"u:num->num") THEN DISCH_TAC THEN
          FIRST_X_ASSUM (fun th => tactic_of do
            let lp ← q r"hj_line_point"
            let ok ← if mentionsAll lp th then do
                let t ← q r"theta:real"
                pure (mentions t th)
              else pure false
            pure (MP_TAC (← SPEC (← q r"u:num->num")
              (← liftExcept (check (fun _ => ok) th))))) THEN
          ASM_REWRITE_TAC [hj_density, IN_ELIM_THM]],
        DISCH_TAC THEN MATCH_MP_TAC r10 THEN
        FIRST_ASSUM ACCEPT_TAC],
      ALL_TAC] THEN
    MP_TAC (← SPECL [← q r"k + 1", ← q r"n - l:num",
                     ← q r"{y | rho - &2 * eta <= (f:(num->num)->real) y}",
                     ← q r"{y | theta / &2 <= (g:(num->num)->real) y}"]
                      HJ_DENSITY_COMMON) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC r11 THEN
      MAP_EVERY EXISTS_TAC [← q r"eta:real", ← q r"theta:real"] THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"y0:num->num") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"hj_join (k + 1) l m U y0") THEN
    FIRST_X_ASSUM (fun th => tactic_of do
      let v ← q r"hj_join"
      pure (MP_TAC (← SPEC (← q r"y0:num->num")
        (← liftExcept (check (mentionsAll v) th))))) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC (← q r"rho - &2 * eta <= (f:(num->num)->real) y0") THEN
      EXPAND_TAC "f" THEN REWRITE_TAC [],
      UNDISCH_TAC (← q r"theta / &2 <= (g:(num->num)->real) y0") THEN
      EXPAND_TAC "g" THEN ASM_SIMP_TAC [REAL_LE_RDIV_EQ]]))

  -- @@RETURN BEGIN
  return { FMEAN_REVERSE_MARKOV, HJ_JOIN_POINT_RIGHT, HJ_DENSITY_COMMON,
           HJ_DENSITY_COMPL, CARD_RESTRICT_SUM, DKT_ETA_BOUND, DKT_LEMMA8 }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- Insensitive sets; line-free sets with many lines below (DKT Lemma 10,     -/
/- first part).  (szemeredi.ml 3795-3988)                                    -/
/- ------------------------------------------------------------------------- -/

structure Insensitive where
  -- @@FIELDS
  hj_replace : thm
  hj_insensitive : thm
  HJ_INSENSITIVE_COMPL : thm
  HJ_INSENSITIVE_UNIV : thm
  HJ_INSENSITIVE_REPLACE : thm
  HJ_REPLACE_WORD : thm
  HJ_REPLACE_LINE : thm
  HJ_CUBE_SUC_CASES : thm
  HJ_LINE_NOT_WORD : thm
  HJ_LINES_EQ_DIFF : thm
  CARD_HJ_LINES : thm
  HJ_LINE_EXTEND : thm
  HJ_LINE_FREE_POINTS : thm
  HJ_DENSITY_SMALL_CUBE : thm
  DKT_POW_RATIO_SMALL : thm
  DKT_PARTITION_SUM : thm
  HJ_DENSITY_PARTITION : thm
  deriving Inhabited

@[nospecialize]
def setupInsensitive [HolBase] (D : SzemerediDeps) (BFiniteMeans : FiniteMeans) (BWords : Words) (BLines : Lines) (BDensities : Densities) (BWildcards : Wildcards) :
    ExceptT String IO Insensitive := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, SET_TAC, TAUT,
        new_definition, .. } := D
  let { CARD_DIFF, EQ_TRANS, EXTENSION, FINITE_NUMSEG_LT, FUN_EQ_THM, IN_DIFF,
        IN_ELIM_THM, LE_ANTISYM, LT_REFL, LT_TRANS, MINIMAL, MONO_EXISTS, .. } := D.core1
  let { NOT_LT, REAL_ARCH_POW_INV, REAL_LE_DIV, REAL_LE_LDIV_EQ, REAL_LE_TRANS,
        REAL_LT_IMP_LE, REAL_LT_LDIV_EQ, REAL_MUL_LID, REAL_OF_NUM_LE, REAL_OF_NUM_LT,
        REAL_OF_NUM_POW, REAL_POS, REAL_POW_DIV, REAL_POW_MONO_INV, SUB_REFL, SUM_0,
        SUM_DELTA, SUM_EQ, SUM_EQ_0, .. } := D.core2
  let { FMEAN_SUM, .. } := BFiniteMeans
  let { CARD_HJ_CUBE, FINITE_HJ_CUBE, HJ_CUBE_MONO, IN_HJ_CUBE, hj_subst, .. } := BWords
  let { HJ_LINE_CUBE, hj_has_line, hj_line_point, .. } := BLines
  let { HJ_DENSITY_CARD, hj_density, .. } := BDensities
  let { HJ_LINE_EQ, .. } := BWildcards
  -- @@SCOPE END

  let hj_replace ← new_definition
   r"hj_replace j i (x:num->num) = \r. if x r = j then i else x r"

  let hj_insensitive ← new_definition
   r"hj_insensitive q n i j (D:(num->num)->bool) <=>
    !x y. x IN hj_cube q n /\ y IN hj_cube q n /\
          hj_replace j i x = hj_replace j i y
          ==> (x IN D <=> y IN D)"

  let HJ_INSENSITIVE_COMPL ← prove
   r"!q n i j D. hj_insensitive q n i j D
               ==> hj_insensitive q n i j {x | ~(x IN D)}"
   (← do
    pure (REWRITE_TAC [hj_insensitive, IN_ELIM_THM] THEN MESON_TAC []))

  let HJ_INSENSITIVE_UNIV ← prove
   r"!q n i j. hj_insensitive q n i j {x | T}"
   (← do
    pure (REWRITE_TAC [hj_insensitive, IN_ELIM_THM]))

  let HJ_INSENSITIVE_REPLACE ← prove
   r"!q n i j A. hj_insensitive q n i j {x | hj_replace j i x IN A}"
   (← do
    pure (REWRITE_TAC [hj_insensitive, IN_ELIM_THM] THEN MESON_TAC []))

  let HJ_REPLACE_WORD ← prove
   r"!k m x i. 1 <= k /\ x IN hj_cube k m ==> hj_replace k i x = x"
   (← do
    pure (REWRITE_TAC [IN_HJ_CUBE, hj_replace, FUN_EQ_THM] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q r"x':num < m") THENL
     [SUBGOAL_THEN (← q r"(x:num->num) x' < k") MP_TAC THENL
       [ASM_SIMP_TAC [], ASM_ARITH_TAC],
      SUBGOAL_THEN (← q r"(x:num->num) x' = 0") MP_TAC THENL
       [ASM_MESON_TAC [NOT_LT], ASM_ARITH_TAC]]))

  let HJ_REPLACE_LINE ← prove
   r"!k m u i. hj_line k m u ==> hj_replace k i u = hj_line_point k u i"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [HJ_LINE_EQ, IN_HJ_CUBE] THEN STRIP_TAC THEN
    REWRITE_TAC [hj_replace, hj_line_point, hj_subst, FUN_EQ_THM] THEN
    X_GEN_TAC (← q r"r:num") THEN
    ASM_CASES_TAC (← q r"(u:num->num) r = k") THEN
    ASM_REWRITE_TAC [LT_REFL, SUB_REFL] THEN
    ASM_CASES_TAC (← q r"r:num < m") THENL
     [SUBGOAL_THEN (← q r"(u:num->num) r < k + 1") MP_TAC THENL
       [ASM_SIMP_TAC [], ASM_ARITH_TAC],
      SUBGOAL_THEN (← q r"(u:num->num) r = 0") SUBST_ALL_TAC THENL
       [ASM_MESON_TAC [NOT_LT], ALL_TAC] THEN
      ASM_CASES_TAC (← q r"k = 0") THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC]))

  let HJ_CUBE_SUC_CASES ← prove
   r"!k m x. x IN hj_cube (k + 1) m ==> x IN hj_cube k m \/ hj_line k m x"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [HJ_LINE_EQ] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q r"?i. i < m /\ (x:num->num) i = k") THEN ASM_REWRITE_TAC [] THEN
    UNDISCH_TAC (← q r"(x:num->num) IN hj_cube (k + 1) m") THEN
    REWRITE_TAC [IN_HJ_CUBE] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"(x:num->num) i < k + 1 /\ ~(x i = k)") MP_TAC THENL
     [ASM_MESON_TAC [], ARITH_TAC]))

  let HJ_LINE_NOT_WORD ← prove
   r"!k m x. hj_line k m x ==> ~(x IN hj_cube k m)"
   (← do
    pure (REWRITE_TAC [HJ_LINE_EQ, IN_HJ_CUBE] THEN MESON_TAC [LT_REFL]))

  let HJ_LINES_EQ_DIFF ← prove
   r"!k m. 1 <= k ==> {u | hj_line k m u} = hj_cube (k + 1) m DIFF hj_cube k m"
   (← do
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [EXTENSION, IN_DIFF, IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"x:num->num") THEN EQ_TAC THENL
     [MESON_TAC [HJ_LINE_CUBE, HJ_LINE_NOT_WORD],
      MESON_TAC [HJ_CUBE_SUC_CASES]]))

  let CARD_HJ_LINES ← prove
   r"!k m. 1 <= k ==> CARD {u | hj_line k m u} = (k + 1) EXP m - k EXP m"
   (← do
    let a1 ← ARITH_RULE (← q r"k <= k + 1")
    pure (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [HJ_LINES_EQ_DIFF] THEN
    SIMP_TAC [CARD_DIFF, FINITE_HJ_CUBE, HJ_CUBE_MONO, a1] THEN
    REWRITE_TAC [CARD_HJ_CUBE]))

  let HJ_LINE_EXTEND ← prove
   r"!k m u. 1 <= k /\ hj_line k m u
           ==> hj_line (k + 1) m (\r. if u r = k then k + 1 else u r) /\
               !a. hj_line_point (k + 1)
                     (\r. if u r = k then k + 1 else u r) a =
                   hj_replace k a u"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [HJ_LINE_EQ, IN_HJ_CUBE] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC (← q r"r:num") THEN DISCH_TAC THEN COND_CASES_TAC THENL
       [ARITH_TAC, ALL_TAC] THEN
      SUBGOAL_THEN (← q r"(u:num->num) r < k + 1") MP_TAC THENL
       [ASM_SIMP_TAC [], ARITH_TAC],
      X_GEN_TAC (← q r"r:num") THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"(u:num->num) r = 0") SUBST1_TAC THENL
       [ASM_SIMP_TAC [], ASM_ARITH_TAC],
      EXISTS_TAC (← q r"i:num") THEN ASM_REWRITE_TAC [],
      X_GEN_TAC (← q r"a:num") THEN
      REWRITE_TAC [hj_line_point, hj_subst, hj_replace, FUN_EQ_THM] THEN
      X_GEN_TAC (← q r"r:num") THEN ASM_CASES_TAC (← q r"(u:num->num) r = k") THEN
      ASM_REWRITE_TAC [LT_REFL, SUB_REFL] THEN
      SUBGOAL_THEN (← q r"(u:num->num) r < k + 1") (fun th => REWRITE_TAC [th]) THEN
      ASM_CASES_TAC (← q r"r:num < m") THEN ASM_SIMP_TAC [] THEN
      SUBGOAL_THEN (← q r"(u:num->num) r = 0") SUBST1_TAC THENL
       [ASM_MESON_TAC [NOT_LT], ARITH_TAC]]))

  let HJ_LINE_FREE_POINTS ← prove
   r"!k m A x.
        1 <= k /\ ~hj_has_line (k + 1) m A /\
        x IN hj_cube (k + 1) m /\ x IN A /\
        (!i. i < k ==> hj_replace k i x IN A)
        ==> x IN hj_cube k m"
   (← do
    pure (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (DISJ_CASES_TAC o MATCH_MP HJ_CUBE_SUC_CASES) THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o check (fun th => is_neg (concl th))) THEN
    REWRITE_TAC [hj_has_line] THEN MATCH_MP_TAC (← TAUT (← q r"p ==> ~p ==> q")) THEN
    EXISTS_TAC (← q r"\r. if (x:num->num) r = k then k + 1 else x r") THEN
    MP_TAC (← SPECL [← q r"k:num", ← q r"m:num", ← q r"x:num->num"] HJ_LINE_EXTEND) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC (← q r"a:num") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"a:num < k") THEN
    ASM_SIMP_TAC [] THEN
    SUBGOAL_THEN (← q r"a = k:num") SUBST1_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
    SUBGOAL_THEN (← q r"hj_replace k k (x:num->num) = x")
    (fun th => ASM_REWRITE_TAC [th]) THEN
    REWRITE_TAC [hj_replace, FUN_EQ_THM] THEN MESON_TAC []))

  let HJ_DENSITY_SMALL_CUBE ← prove
   r"!k m. hj_density (k + 1) m (hj_cube k m) = &(k EXP m) / &((k + 1) EXP m)"
   (← do
    let a1 ← ARITH_RULE (← q r"k <= k + 1")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [HJ_DENSITY_CARD] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [← GSYM CARD_HJ_CUBE] THEN AP_TERM_TAC THEN
    MP_TAC (← SPECL [← q r"k:num", ← q r"k + 1", ← q r"m:num"] HJ_CUBE_MONO) THEN
    REWRITE_TAC [a1] THEN SET_TAC []))

  let DKT_POW_RATIO_SMALL ← prove
   r"!k e. 1 <= k /\ &0 < e
         ==> ?M0. !m. M0 <= m ==> &(k EXP m) / &((k + 1) EXP m) <= e"
   (← do
    -- right to left: the second ARITH_RULE, then the first
    let a2 ← ARITH_RULE (← q r"0 < k + 1")
    let a1 ← ARITH_RULE (← q r"0 < k + 1")
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"&k / &(k + 1)", ← q r"e:real"] REAL_ARCH_POW_INV) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC [REAL_LT_LDIV_EQ, REAL_OF_NUM_LT, a1] THEN
      REWRITE_TAC [REAL_MUL_LID, REAL_OF_NUM_LT] THEN ARITH_TAC,
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"M0:num") THEN DISCH_TAC THEN
    X_GEN_TAC (← q r"m:num") THEN DISCH_TAC THEN
    REWRITE_TAC [← GSYM REAL_OF_NUM_POW, ← GSYM REAL_POW_DIV] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"(&k / &(k + 1)) pow M0") THEN
    ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_POW_MONO_INV THEN
    ASM_REWRITE_TAC [] THEN
    SIMP_TAC [REAL_LE_DIV, REAL_POS] THEN
    SIMP_TAC [REAL_LE_LDIV_EQ, REAL_OF_NUM_LT, a2] THEN
    REWRITE_TAC [REAL_MUL_LID, REAL_OF_NUM_LE] THEN ARITH_TAC))

  let DKT_PARTITION_SUM ← prove
   r"!k (P:num->bool).
        sum {i | i < k}
            (\i. if ~P i /\ (!j. j < i ==> P j) then &1 else &0) =
        if ?i. i < k /\ ~P i then &1 else &0"
   (← do
    pure (REPEAT GEN_TAC THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o ONCE_REWRITE_RULE [MINIMAL]) THEN
      ABBREV_TAC (← q r"i0 = minimal i. i < k /\ ~(P:num->bool) i") THEN STRIP_TAC THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC (← q r"sum {i:num | i < k} (\i. if i = i0 then &1 else &0)") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN
        X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN
        SUBGOAL_THEN (← q r"(~(P:num->bool) i /\ (!j. j < i ==> P j)) <=> i = i0")
         (fun th => REWRITE_TAC [th]) THEN
        EQ_TAC THENL
         [STRIP_TAC THEN REWRITE_TAC [← GSYM LE_ANTISYM, ← GSYM NOT_LT] THEN
          ASM_MESON_TAC [],
          DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [] THEN
          ASM_MESON_TAC [LT_TRANS]],
        REWRITE_TAC [SUM_DELTA, IN_ELIM_THM] THEN ASM_REWRITE_TAC []],
      MATCH_MP_TAC SUM_EQ_0 THEN REWRITE_TAC [IN_ELIM_THM] THEN
      ASM_MESON_TAC []]))

  let HJ_DENSITY_PARTITION ← prove
   r"!q n k S (C:num->(num->num)->bool).
        sum {i | i < k}
            (\i. hj_density q n {x | x IN S /\ ~(x IN C i) /\
                               !j. j < i ==> x IN C j}) =
        hj_density q n {x | x IN S /\ ?i. i < k /\ ~(x IN C i)}"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [hj_density, IN_ELIM_THM] THEN
    SIMP_TAC [← GSYM FMEAN_SUM, FINITE_HJ_CUBE, FINITE_NUMSEG_LT] THEN
    AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"x:num->num") THEN
    ASM_CASES_TAC (← q r"(x:num->num) IN S") THEN ASM_REWRITE_TAC [SUM_0] THEN
    MP_TAC (← SPECL [← q r"k:num", ← q r"\i:num. (x:num->num) IN (C:num->(num->num)->bool)
      i"] DKT_PARTITION_SUM) THEN
    REWRITE_TAC []))

  -- @@RETURN BEGIN
  return { hj_replace, hj_insensitive, HJ_INSENSITIVE_COMPL, HJ_INSENSITIVE_UNIV,
           HJ_INSENSITIVE_REPLACE, HJ_REPLACE_WORD, HJ_REPLACE_LINE, HJ_CUBE_SUC_CASES,
           HJ_LINE_NOT_WORD, HJ_LINES_EQ_DIFF, CARD_HJ_LINES, HJ_LINE_EXTEND,
           HJ_LINE_FREE_POINTS, HJ_DENSITY_SMALL_CUBE, DKT_POW_RATIO_SMALL,
           DKT_PARTITION_SUM, HJ_DENSITY_PARTITION }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- DKT Lemma 10.  (szemeredi.ml 3989-4171)                                   -/
/- ------------------------------------------------------------------------- -/

structure Lemma10 where
  -- @@FIELDS
  DKT_PARTITION_INCREMENT : thm
  DKT_LEMMA10 : thm
  deriving Inhabited

@[nospecialize]
def setupLemma10 [HolBase] (D : SzemerediDeps) (BFiniteMeans : FiniteMeans) (BWords : Words) (BLines : Lines) (BDensities : Densities) (BInsensitive : Insensitive) :
    ExceptT String IO Lemma10 := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON_TAC,
        REAL_ARITH, REAL_ARITH_TAC, REAL_FIELD, SET_TAC, TAUT, .. } := D
  let { CARD_NUMSEG_LT, CARD_SUBSET, EXP_EQ_0, EXP_MONO_LE, FINITE_NUMSEG_LT,
        FINITE_SUBSET, IN_ELIM_THM, LT_NZ, MEMBER_NOT_EMPTY, NOT_EXISTS_THM, .. } := D.core1
  let { REAL_LE_DIV, REAL_LE_LDIV_EQ, REAL_LE_LMUL, REAL_LE_MUL, REAL_LE_RDIV_EQ,
        REAL_LE_TRANS, REAL_NOT_LE, REAL_OF_NUM_LE, REAL_OF_NUM_LT, REAL_OF_NUM_SUB,
        REAL_POS, SUBSET, SUM_ADD, SUM_CONST, SUM_LMUL, SUM_LT_ALL, SUM_POS_LE, .. } := D.core2
  let { FMEAN_ADD, FMEAN_LE, .. } := BFiniteMeans
  let { FINITE_HJ_CUBE, .. } := BWords
  let { HJ_LINE_CUBE, .. } := BLines
  let { HJ_DENSITY_CARD, HJ_DENSITY_MONO, HJ_DENSITY_POS, hj_density, .. } := BDensities
  let { CARD_HJ_LINES, HJ_DENSITY_PARTITION, HJ_DENSITY_SMALL_CUBE,
        HJ_LINE_FREE_POINTS, HJ_REPLACE_LINE, .. } := BInsensitive
  -- @@SCOPE END

  let DKT_PARTITION_INCREMENT ← prove
   r"!k q n (C:num->(num->num)->bool) A rho eta.
        1 <= k /\ &0 < eta /\ &0 <= rho /\
        (rho + &6 * eta) * hj_density q n {x | x IN hj_cube q n /\ ?i. i < k /\
          ~(x IN C i)} <=
        hj_density q n {x | x IN A /\ ?i. i < k /\ ~(x IN C i)}
        ==> ?i0. i0 < k /\
                 &3 * eta / &k *
                 hj_density q n
                   {x | x IN hj_cube q n /\ ?i. i < k /\ ~(x IN C i)} <=
                 hj_density q n {x | x IN hj_cube q n /\ ~(x IN C i0) /\
                               !j. j < i0 ==> x IN C j} /\
                 (rho + &3 * eta) *
                 hj_density q n {x | x IN hj_cube q n /\ ~(x IN C i0) /\
                               !j. j < i0 ==> x IN C j} <=
                 hj_density q n {x | x IN A /\ ~(x IN C i0) /\
                               !j. j < i0 ==> x IN C j}"
   (← do
    let r1 ← REAL_ARITH
      (← q r"!X r e d t. t = &3 * e * d
                ==> (r + &6 * e) * d <= X ==>
                  ~(X < (r + &3 * e) * d + t)")
    pure (REPEAT STRIP_TAC THEN
    ABBREV_TAC (← q r"d = hj_density q n {x | x IN hj_cube q n /\ ?i. i < k /\
      ~(x IN (C:num->(num->num)->bool) i)}") THEN
    ABBREV_TAC (← q r"p = \i. hj_density q n {x | x IN hj_cube q n /\
      ~(x IN (C:num->(num->num)->bool) i) /\
                                      !j. j < i ==> x IN C j}") THEN
    ABBREV_TAC (← q r"a = \i. hj_density q n {x | x IN A /\
      ~(x IN (C:num->(num->num)->bool) i) /\
                                      !j. j < i ==> x IN C j}") THEN
    SUBGOAL_THEN (← q r"sum {i:num | i < k} p = d /\
                  sum {i:num | i < k} a =
                  hj_density q n {x | x IN A /\ ?i. i < k /\
                    ~(x IN (C:num->(num->num)->bool) i)}")
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["p", "a", "d"] THEN
      REWRITE_TAC [HJ_DENSITY_PARTITION],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!i. (a:num->real) i <= p i") ASSUME_TAC THENL
     [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["a", "p"] THEN
      REWRITE_TAC [] THEN MATCH_MP_TAC HJ_DENSITY_MONO THEN
      SIMP_TAC [IN_ELIM_THM],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"?i0. i0 < k /\ &3 * eta / &k * d <= (p:num->real) i0 /\
           (rho + &3 * eta) * p i0 <= (a:num->real) i0")
    MP_TAC THENL
     [ALL_TAC, MAP_EVERY EXPAND_TAC ["p", "a"] THEN REWRITE_TAC []] THEN
    MATCH_MP_TAC (← TAUT (← q r"(~p ==> F) ==> p")) THEN
    DISCH_THEN (ASSUME_TAC o REWRITE_RULE
     [NOT_EXISTS_THM, ← TAUT (← q r"~(a /\ b /\ c) <=> a /\ b ==> ~c"),
      REAL_NOT_LE]) THEN
    SUBGOAL_THEN (← q r"!i. &0 <= (p:num->real) i") ASSUME_TAC THENL
     [EXPAND_TAC "p" THEN REWRITE_TAC [HJ_DENSITY_POS], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"&0 <= d") ASSUME_TAC THENL
     [UNDISCH_TAC (← q r"sum {i:num | i < k} p = d") THEN
      DISCH_THEN (fun th => tactic_of do pure (SUBST1_TAC (← SYM th))) THEN
      MATCH_MP_TAC SUM_POS_LE THEN
      ASM_REWRITE_TAC [FINITE_NUMSEG_LT],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"&0 <= &3 * eta / &k * d") ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC [REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC [REAL_POS] THEN
      ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!i. i < k
          ==> (a:num->real) i < (rho + &3 * eta) * p i + &3 * eta / &k * d")
    ASSUME_TAC THENL
     [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"&0 <= (rho + &3 * eta) * (p:num->real) i") ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC [] THEN
        ASM_REAL_ARITH_TAC,
        ALL_TAC] THEN
      MP_TAC (← SPEC (← q r"i:num") (← ASSUME (← q r"!i. (a:num->real) i <= p i"))) THEN
      ASM_CASES_TAC (← q r"&3 * eta / &k * d <= (p:num->real) i") THENL
       [FIRST_X_ASSUM (fun th => tactic_of do
          let v ← q r"rho:real"
          let ok ← if is_forall (concl th) then
              pure (can (find_term (fun u => u == v)) (concl th))
            else pure false
          pure (MP_TAC (← SPEC (← q r"i:num")
            (← liftExcept (check (fun _ => ok) th))))) THEN
        ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC,
        ASM_REAL_ARITH_TAC],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"a:num->real",
                      ← q r"\i. (rho + &3 * eta) * (p:num->real) i + &3 * eta / &k * d",
                      ← q r"{i:num | i < k}"] SUM_LT_ALL) THEN
    ANTS_TAC THENL
     [REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, ← GSYM MEMBER_NOT_EMPTY] THEN
      ASM_SIMP_TAC [] THEN EXISTS_TAC (← q r"0") THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    SIMP_TAC [SUM_ADD, SUM_LMUL, SUM_CONST, FINITE_NUMSEG_LT, CARD_NUMSEG_LT] THEN
    ASM_REWRITE_TAC [] THEN
    UNDISCH_TAC
     (← q r"(rho + &6 * eta) * d <=
      hj_density q n {x | x IN A /\ ?i. i < k /\
                              ~(x IN (C:num->(num->num)->bool) i)}") THEN
    MATCH_MP_TAC r1 THEN
    UNDISCH_TAC (← q r"1 <= k") THEN REWRITE_TAC [← GSYM REAL_OF_NUM_LE] THEN
    CONV_TAC REAL_FIELD))

  let DKT_LEMMA10 ← prove
   r"!k m A theta eta rho.
        1 <= k /\ ~hj_has_line (k + 1) m A /\ &0 < eta /\ eta <= &1 / &2 /\
        &(k EXP m) / &((k + 1) EXP m) <= eta /\ &0 <= theta /\
        rho - &2 * eta <= hj_density (k + 1) m A /\
        theta / &2 * &(CARD {u | hj_line k m u}) <=
        &(CARD {u | hj_line k m u /\ !a. a < k ==> hj_line_point k u a IN A})
        ==> theta / &4 <=
            hj_density (k + 1) m {x | x IN hj_cube (k + 1) m /\
                                !i. i < k ==> hj_replace k i x IN A} /\
            rho - &3 * eta <=
            hj_density (k + 1) m
              {x | x IN A /\ ?i. i < k /\ ~(hj_replace k i x IN A)}"
   (← do
    -- right to left: the second REAL_ARITH, then the first
    let r2 ← REAL_ARITH
      (← q r"!t p q. t * (p / &4) <= t * ((p - q) / &2)
              ==> t / &4 * p <= t / &2 * (p - q)")
    let r1 ← REAL_ARITH (← q r"!e p. &0 <= (&1 / &2 - e) * p ==> e * p <= p / &2")
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
    ABBREV_TAC (← q r"C = {x | x IN hj_cube (k + 1) m /\ !i. i < k ==>
      hj_replace k i x IN A}") THEN
    SUBGOAL_THEN
     (← q r"{u | hj_line k m u /\ !a. a < k ==> hj_line_point k u a IN A} SUBSET C")
    ASSUME_TAC THENL
     [EXPAND_TAC "C" THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN
      MESON_TAC [HJ_LINE_CUBE, HJ_REPLACE_LINE],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"C SUBSET hj_cube (k + 1) m") ASSUME_TAC THENL
     [EXPAND_TAC "C" THEN SET_TAC [], ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [HJ_DENSITY_CARD] THEN
      SUBGOAL_THEN (← q r"{x | x IN hj_cube (k + 1) m /\ x IN C} = C") SUBST1_TAC THENL
       [ASM SET_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"&0 < &((k + 1) EXP m)") ASSUME_TAC THENL
       [REWRITE_TAC [REAL_OF_NUM_LT, LT_NZ, EXP_EQ_0] THEN ARITH_TAC,
        ALL_TAC] THEN
      ASM_SIMP_TAC [REAL_LE_RDIV_EQ] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
        (← q r"&(CARD {u | hj_line k m u /\
                 !a. a < k ==> hj_line_point k u a IN A})") THEN
      CONJ_TAC THENL
       [ALL_TAC,
        REWRITE_TAC [REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
        ASM_MESON_TAC [FINITE_SUBSET, FINITE_HJ_CUBE]] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"theta / &2 * &(CARD {u | hj_line k m u})") THEN
      CONJ_TAC THENL [ALL_TAC, FIRST_ASSUM ACCEPT_TAC] THEN
      ASM_SIMP_TAC [CARD_HJ_LINES] THEN
      SUBGOAL_THEN (← q r"k EXP m <= (k + 1) EXP m") ASSUME_TAC THENL
       [REWRITE_TAC [EXP_MONO_LE] THEN ARITH_TAC, ALL_TAC] THEN
      ASM_SIMP_TAC [← GSYM REAL_OF_NUM_SUB] THEN
      SUBGOAL_THEN (← q r"&(k EXP m) <= &((k + 1) EXP m) / &2") ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"eta * &((k + 1) EXP m)") THEN
        CONJ_TAC THENL
         [UNDISCH_TAC (← q r"&(k EXP m) / &((k + 1) EXP m) <= eta") THEN
          ASM_SIMP_TAC [REAL_LE_LDIV_EQ],
          MATCH_MP_TAC r1 THEN
          MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC [REAL_POS] THEN
          ASM_REAL_ARITH_TAC],
        ALL_TAC] THEN
      MATCH_MP_TAC r2 THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC [] THEN
      ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    ABBREV_TAC (← q r"S1 = {x | x IN A /\ ?i. i < k /\ ~(hj_replace k i x IN A)}") THEN
    SUBGOAL_THEN
     (← q r"hj_density (k + 1) m A <= hj_density (k + 1) m (hj_cube k m) +
      hj_density (k + 1) m S1")
    MP_TAC THENL
     [EXPAND_TAC "S1" THEN
      REWRITE_TAC [hj_density] THEN SIMP_TAC [← GSYM FMEAN_ADD, FINITE_HJ_CUBE] THEN
      MATCH_MP_TAC FMEAN_LE THEN REWRITE_TAC [FINITE_HJ_CUBE, IN_ELIM_THM] THEN
      X_GEN_TAC (← q r"x:num->num") THEN DISCH_TAC THEN
      ASM_CASES_TAC (← q r"(x:num->num) IN A") THEN ASM_REWRITE_TAC [] THENL
       [ALL_TAC,
        REPEAT COND_CASES_TAC THEN REAL_ARITH_TAC] THEN
      ASM_CASES_TAC (← q r"?i. i < k /\ ~(hj_replace k i (x:num->num) IN A)") THEN
      ASM_REWRITE_TAC [] THENL
       [COND_CASES_TAC THEN REAL_ARITH_TAC, ALL_TAC] THEN
      SUBGOAL_THEN (← q r"(x:num->num) IN hj_cube k m")
      (fun th => REWRITE_TAC [th]) THENL
       [MATCH_MP_TAC HJ_LINE_FREE_POINTS THEN ASM_MESON_TAC [],
        REAL_ARITH_TAC],
      ALL_TAC] THEN
    REWRITE_TAC [HJ_DENSITY_SMALL_CUBE] THEN ASM_REAL_ARITH_TAC))

  -- @@RETURN BEGIN
  return { DKT_PARTITION_INCREMENT, DKT_LEMMA10 }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- Increment on an intersection of insensitive sets (DKT Corollary 11).      -/
/- (szemeredi.ml 4172-4442)                                                  -/
/- ------------------------------------------------------------------------- -/

structure Cor11 where
  -- @@FIELDS
  HJ_DENSITY_CUBE : thm
  HJ_DENSITY_COMPL_CUBE : thm
  DKT_COR11 : thm
  deriving Inhabited

@[nospecialize]
def setupCor11 [HolBase] (D : SzemerediDeps) (BFiniteMeans : FiniteMeans) (BWords : Words) (BLines : Lines) (BDensities : Densities) (BLemma8 : Lemma8) (BInsensitive : Insensitive) (BLemma10 : Lemma10) :
    ExceptT String IO Cor11 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_REAL_ARITH_TAC, REAL_ARITH, REAL_ARITH_TAC,
        REAL_FIELD, SET_RULE, .. } := D
  let { ARITH, EQ_TRANS, IN_ELIM_THM, LT_REFL, MONO_EXISTS, NOT_FORALL_THM, NOT_IMP, .. } := D.core1
  let { REAL_INV_MUL, REAL_LE_DIV, REAL_LE_LDIV_EQ, REAL_LE_LMUL, REAL_LE_MUL,
        REAL_LE_RMUL, REAL_LE_TRANS, REAL_LT_DIV, REAL_LT_IMP_LE, REAL_LT_MUL,
        REAL_MUL_AC, REAL_MUL_LID, REAL_MUL_RID, REAL_OF_NUM_LE, REAL_OF_NUM_LT,
        REAL_OF_NUM_MUL, REAL_POS, REAL_POW_2, REAL_POW_LT, real_div, .. } := D.core2
  let { FMEAN_CONST, FMEAN_EQ, .. } := BFiniteMeans
  let { FINITE_HJ_CUBE, HJ_CUBE_NONEMPTY, .. } := BWords
  let { HJ_HAS_LINE_PULLBACK, .. } := BLines
  let { HJ_DENSITY_EQ, HJ_DENSITY_MONO, HJ_DENSITY_POS, hj_density, .. } := BDensities
  let { DKT_LEMMA8, HJ_DENSITY_COMPL, .. } := BLemma8
  let { DKT_POW_RATIO_SMALL, HJ_INSENSITIVE_COMPL, HJ_INSENSITIVE_REPLACE,
        HJ_INSENSITIVE_UNIV, .. } := BInsensitive
  let { DKT_LEMMA10, DKT_PARTITION_INCREMENT, .. } := BLemma10
  -- @@SCOPE END

  let HJ_DENSITY_CUBE ← prove
   r"!q n. 1 <= q ==> hj_density q n (hj_cube q n) = &1"
   (← do
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [hj_density] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (← q r"fmean (hj_cube q n) (\x. &1)") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FMEAN_EQ THEN SIMP_TAC [],
      MATCH_MP_TAC FMEAN_CONST THEN
        ASM_SIMP_TAC [FINITE_HJ_CUBE, HJ_CUBE_NONEMPTY]]))

  let HJ_DENSITY_COMPL_CUBE ← prove
   r"!q n (P:(num->num)->bool).
        1 <= q
        ==> hj_density q n {x | x IN hj_cube q n /\ ~P x} =
            &1 - hj_density q n {x | x IN hj_cube q n /\ P x}"
   (← do
    pure (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"hj_density q n {x | x IN hj_cube q n /\ ~P x} =
      hj_density q n {x | ~P x} /\
      hj_density q n {x | x IN hj_cube q n /\ P x} = hj_density q n {x | P x}")
    (fun th => REWRITE_TAC [th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC HJ_DENSITY_EQ THEN SIMP_TAC [IN_ELIM_THM],
      ASM_SIMP_TAC [HJ_DENSITY_COMPL]]))

  let DKT_COR11 ← prove
   r"!k delta.
        1 <= k /\ density_hales_jewett k /\ &0 < delta /\ delta <= &1
        ==> ?gamma M0.
              &0 < gamma /\
              !m. M0 <= m
                  ==> ?N. !n A rho.
                        N <= n /\ delta <= rho /\
                        rho <= hj_density (k + 1) n A /\
                        ~hj_has_line (k + 1) n A
                        ==> ?W D.
                              hj_subspace (k + 1) m n W /\
                              (!i. i < k
                                   ==> hj_insensitive (k + 1) m i k (D i)) /\
                              gamma <=
                              hj_density (k + 1) m
                                {x | x IN hj_cube (k + 1) m /\
                                     !i. i < k ==> x IN D i} /\
                              (rho + gamma) *
                              hj_density (k + 1) m
                                {x | x IN hj_cube (k + 1) m /\
                                     !i. i < k ==> x IN D i} <=
                              hj_density (k + 1) m
                                {x | hj_subst (k + 1) W x IN A /\
                                     !i. i < k ==> x IN D i}"
   (← do
    -- right to left: the seven rules from the last to the first
    let a7 ← ARITH_RULE (← q r"1 <= k + 1")
    let a6 ← ARITH_RULE (← q r"1 <= k + 1")
    let a5 ← ARITH_RULE (← q r"1 <= k + 1")
    let s4 ← SET_RULE (← q r"!s:(num->num)->bool. {x | x IN s} = s")
    let a3 ← ARITH_RULE (← q r"1 <= k ==> 0 < k")
    let r2 ← REAL_ARITH (← q r"!a b. a <= b ==> a / &48 <= b / &48")
    let r1 ← REAL_ARITH (← q r"!a b. a <= b ==> a / &48 <= b / &48")
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"k:num", ← q r"delta:real"] DKT_LEMMA8) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"m0:num") (X_CHOOSE_THEN (← q r"theta:real")
      STRIP_ASSUME_TAC)) THEN
    ABBREV_TAC (← q r"th = min theta (&1)") THEN
    SUBGOAL_THEN (← q r"&0 < th /\ th <= theta /\ th <= &1") STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "th" THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    ABBREV_TAC (← q r"eta = (delta * th) / &48") THEN
    SUBGOAL_THEN (← q r"&0 < eta /\ eta <= delta / &48 /\ eta <= th / &48 /\
                  delta * th = &48 * eta")
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "eta" THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC [REAL_OF_NUM_LT, ARITH] THEN
        ASM_SIMP_TAC [REAL_LT_MUL],
        MATCH_MP_TAC r1 THEN
        GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC,
        MATCH_MP_TAC r2 THEN
        GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC,
        REAL_ARITH_TAC],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"eta pow 2 <= eta") ASSUME_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_RID] THEN
      REWRITE_TAC [REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    MP_TAC (← SPECL [← q r"k:num", ← q r"eta:real"] DKT_POW_RATIO_SMALL) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"M1:num")) THEN
    EXISTS_TAC (← q r"delta * eta pow 2 / (&2 * &k)") THEN
    EXISTS_TAC (← q r"m0 + M1:num") THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC [REAL_POW_LT] THEN
      REWRITE_TAC [REAL_OF_NUM_MUL, REAL_OF_NUM_LT] THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    X_GEN_TAC (← q r"m:num") THEN DISCH_TAC THEN
    FIRST_X_ASSUM (fun th => tactic_of do
      let v ← q r"theta:real"
      let ok ← if is_forall (concl th) then
          pure (can (find_term (fun u => u == v)) (concl th))
        else pure false
      pure (MP_TAC (← SPECL [← q r"m:num", ← q r"eta:real"]
        (← liftExcept (check (fun _ => ok) th))))) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_ARITH_TAC, ASM_REWRITE_TAC [], ASM_REAL_ARITH_TAC,
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"eta:real") THEN
        CONJ_TAC THENL
         [GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_RID] THEN
          REWRITE_TAC [REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
          ASM_REAL_ARITH_TAC,
          ASM_REAL_ARITH_TAC],
        ASM_REAL_ARITH_TAC],
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"N:num") THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [← q r"n:num", ← q r"A:(num->num)->bool", ← q r"rho:real"] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"n:num", ← q r"A:(num->num)->bool",
      ← q r"rho:real"]) THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q r"delta * eta pow 2 / (&2 * &k) <= eta pow 2 / &2")
    ASSUME_TAC THENL
     [SUBGOAL_THEN
       (← q r"delta * eta pow 2 / (&2 * &k) = (eta pow 2 / &2) * (delta / &k)")
      SUBST1_TAC THENL
       [REWRITE_TAC [real_div, REAL_INV_MUL, REAL_MUL_AC], ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC [REAL_POS, REAL_POW_2] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC,
        ASM_SIMP_TAC [REAL_LE_LDIV_EQ, REAL_OF_NUM_LT, a3] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"&1") THEN
        ASM_REWRITE_TAC [REAL_MUL_LID, REAL_OF_NUM_LE]],
      ALL_TAC] THEN
    STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [← q r"X:num->num", ← q r"\i:num. {x:num->num | T}"] THEN
      ASM_REWRITE_TAC [HJ_INSENSITIVE_UNIV, IN_ELIM_THM] THEN
      REWRITE_TAC [s4] THEN
      ASM_SIMP_TAC [HJ_DENSITY_CUBE, a5, REAL_MUL_RID] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"rho + eta pow 2 / &2") THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC, FIRST_ASSUM ACCEPT_TAC],
      ALL_TAC] THEN
    ABBREV_TAC (← q r"A' = {a | hj_subst (k + 1) W a IN A}") THEN
    SUBGOAL_THEN (← q r"~hj_has_line (k + 1) m A'") ASSUME_TAC THENL
     [EXPAND_TAC "A'" THEN DISCH_TAC THEN
      UNDISCH_TAC (← q r"~hj_has_line (k + 1) n A") THEN REWRITE_TAC [] THEN
      MATCH_MP_TAC HJ_HAS_LINE_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [← q r"m:num", ← q r"W:num->num"] THEN
      ASM_REWRITE_TAC [a6],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"k:num", ← q r"m:num", ← q r"A':(num->num)->bool",
                      ← q r"th:real", ← q r"eta:real", ← q r"rho:real"] DKT_LEMMA10) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC,
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC,
        ASM_REAL_ARITH_TAC,
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC (← q r"theta / &2 * &(CARD {u | hj_line k m u})") THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC [REAL_POS] THEN
          ASM_REAL_ARITH_TAC,
          EXPAND_TAC "A'" THEN REWRITE_TAC [IN_ELIM_THM] THEN
          FIRST_ASSUM ACCEPT_TAC]],
      ALL_TAC] THEN
    STRIP_TAC THEN
    ABBREV_TAC
     (← q r"Cs = {x | x IN hj_cube (k + 1) m /\
            !i. i < k ==> hj_replace k i x IN A'}") THEN
    ABBREV_TAC
     (← q r"NCs = {x | x IN hj_cube (k + 1) m /\
             ?i. i < k /\ ~(hj_replace k i x IN A')}") THEN
    ABBREV_TAC
      (← q r"ANC = {x | x IN A' /\ ?i. i < k /\ ~(hj_replace k i x IN A')}") THEN
    SUBGOAL_THEN (← q r"hj_density (k + 1) m NCs = &1 - hj_density (k + 1) m Cs")
    ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["NCs", "Cs"] THEN
      MP_TAC (← ISPECL [← q r"k + 1", ← q r"m:num",
                        ← q r"\x. !i. i < k
                              ==> hj_replace k i x IN (A':(num->num)->bool)"]
        HJ_DENSITY_COMPL_CUBE) THEN
      REWRITE_TAC [a7, NOT_FORALL_THM, NOT_IMP],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"hj_density (k + 1) m ANC <= hj_density (k + 1) m NCs")
    ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["ANC", "NCs"] THEN MATCH_MP_TAC HJ_DENSITY_MONO THEN
      SIMP_TAC [IN_ELIM_THM],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"k:num", ← q r"k + 1", ← q r"m:num",
                      ← q r"\i:num. {x:num->num | hj_replace k i x IN A'}",
                      ← q r"A':(num->num)->bool", ← q r"rho:real", ← q r"eta:real"]
      DKT_PARTITION_INCREMENT) THEN
    REWRITE_TAC [IN_ELIM_THM] THEN ASM_REWRITE_TAC [] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"rho - &3 * eta") THEN
      ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"(rho + &6 * eta) * (&1 - th / &4)") THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      SUBGOAL_THEN (← q r"delta * th <= rho * th /\ &0 <= eta * th") MP_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC,
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC],
        ASM_REAL_ARITH_TAC],
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"i0:num") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"W:num->num") THEN
    EXISTS_TAC (← q r"\i. if i < i0 then {x | hj_replace k i x IN A'}
                    else if i = i0 then {x:num->num | ~(hj_replace k i0 x IN A')}
                    else {x | T}") THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN
      ASM_CASES_TAC (← q r"i:num < i0") THEN
      ASM_REWRITE_TAC [HJ_INSENSITIVE_REPLACE] THEN
      ASM_CASES_TAC (← q r"i:num = i0") THEN ASM_REWRITE_TAC [HJ_INSENSITIVE_UNIV] THEN
      MP_TAC (← ISPECL [← q r"k + 1", ← q r"m:num", ← q r"i0:num", ← q r"k:num",
                        ← q r"{x:num->num | hj_replace k i0 x IN A'}"]
                         HJ_INSENSITIVE_COMPL) THEN
      REWRITE_TAC [HJ_INSENSITIVE_REPLACE, IN_ELIM_THM],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!x. (!i. i < k
               ==> x IN (if i < i0 then {x | hj_replace k i x IN A'}
                         else if i =
                         i0 then {x:num->num | ~(hj_replace k i0 x IN A')}
                         else {x | T})) <=>
          ~(hj_replace k i0 x IN A') /\ (!j. j < i0 ==> hj_replace k j x IN A')")
    (fun th => REWRITE_TAC [th]) THENL
     [X_GEN_TAC (← q r"x:num->num") THEN EQ_TAC THENL
       [DISCH_TAC THEN CONJ_TAC THENL
         [FIRST_X_ASSUM (MP_TAC o SPEC (← q r"i0:num")) THEN
          ASM_REWRITE_TAC [LT_REFL, IN_ELIM_THM],
          X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN
          FIRST_X_ASSUM (MP_TAC o SPEC (← q r"j:num")) THEN
          ASM_SIMP_TAC [IN_ELIM_THM] THEN ANTS_TAC THENL
           [ASM_ARITH_TAC, SIMP_TAC []]],
        STRIP_TAC THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN
        ASM_CASES_TAC (← q r"i:num < i0") THEN ASM_SIMP_TAC [IN_ELIM_THM] THEN
        ASM_CASES_TAC (← q r"i:num = i0") THEN ASM_REWRITE_TAC [IN_ELIM_THM]],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"{x | hj_subst (k + 1) W x IN A /\ ~(hj_replace k i0 x IN A') /\
           (!j. j < i0 ==> hj_replace k j x IN A')} =
      {x | x IN A' /\ ~(hj_replace k i0 x IN A') /\
           (!j. j < i0 ==> hj_replace k j x IN A')}")
    SUBST1_TAC THENL
     [EXPAND_TAC "A'" THEN REWRITE_TAC [IN_ELIM_THM], ALL_TAC] THEN
    ABBREV_TAC
     (← q r"P0 = {x | x IN hj_cube (k + 1) m /\ ~(hj_replace k i0 x IN A') /\
                (!j. j < i0 ==> hj_replace k j x IN A')}") THEN
    ABBREV_TAC
     (← q r"AP0 = {x | x IN A' /\ ~(hj_replace k i0 x IN A') /\
                 (!j. j < i0 ==> hj_replace k j x IN A')}") THEN
    SUBGOAL_THEN (← q r"&0 <= hj_density (k + 1) m P0") ASSUME_TAC THENL
     [REWRITE_TAC [HJ_DENSITY_POS], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"delta * eta <= delta") ASSUME_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"&0 < eta / &k") ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC [REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"eta / &k * (delta * eta / &6) <= eta / &k * (&1 - hj_density (k + 1) m Cs)")
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN
      ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"delta * eta pow 2 / (&2 * &k) = &3 * (eta / &k * (delta * eta / &6))")
    ASSUME_TAC THENL
     [UNDISCH_TAC (← q r"1 <= k") THEN REWRITE_TAC [← GSYM REAL_OF_NUM_LE] THEN
      CONV_TAC REAL_FIELD,
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"(rho + &3 * eta) * hj_density (k + 1) m P0") THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC))

  -- @@RETURN BEGIN
  return { HJ_DENSITY_CUBE, HJ_DENSITY_COMPL_CUBE, DKT_COR11 }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- Tilings by subspaces.  (szemeredi.ml 4443-4651)                           -/
/- ------------------------------------------------------------------------- -/

structure Tilings where
  -- @@FIELDS
  hj_tiling : thm
  hj_tiling_union : thm
  HJ_TILING_EMPTY : thm
  HJ_TILING_UNION_EMPTY : thm
  HJ_TILING_UNION_SUBSET : thm
  HJ_TILING_UNION_CUBE : thm
  HJ_TILING_INJ : thm
  CARD_HJ_TILING_UNION_RESTRICT : thm
  HJ_DENSITY_TILING_UNION_RESTRICT : thm
  HJ_TILING_AVERAGE : thm
  deriving Inhabited

@[nospecialize]
def setupTilings [HolBase] (D : SzemerediDeps) (BWords : Words) (BDensities : Densities) (BCor11 : Cor11) :
    ExceptT String IO Tilings := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, REAL_ARITH, REAL_FIELD, SET_RULE,
        SET_TAC, TAUT, new_definition, .. } := D
  let { CARD_IMAGE_INJ, EQ_TRANS, EXISTS_PAIR_THM, EXP_EQ_0, EXTENSION, FINITE_CROSS,
        FINITE_EMPTY, FINITE_RESTRICT, FINITE_SUBSET, FORALL_PAIR_THM, FUN_EQ_THM,
        IN_CROSS, IN_ELIM_PAIR_THM, IN_ELIM_THM, IN_IMAGE, LT_NZ, NOT_EXISTS_THM,
        NOT_IN_EMPTY, .. } := D.core1
  let { PAIR_EQ, REAL_LT_DIV, REAL_LT_RMUL, REAL_MUL_ASSOC, REAL_MUL_RID, REAL_NOT_LE,
        REAL_OF_NUM_EQ, REAL_OF_NUM_LT, SUBSET, SUM_CONST, SUM_EQ, SUM_LT_ALL,
        SUM_RMUL, SUM_SUM_PRODUCT, real_div, .. } := D.core2
  let { FINITE_HJ_CUBE, HJ_SUBST_CUBE, HJ_SUBST_INJ, .. } := BWords
  let { HJ_DENSITY_CARD, HJ_DENSITY_EQ, .. } := BDensities
  let { HJ_DENSITY_CUBE, .. } := BCor11
  -- @@SCOPE END

  let hj_tiling ← new_definition
   r"hj_tiling q m n Fs E <=>
    FINITE Fs /\
    (!z. z IN Fs ==> hj_subspace q m n z /\ !a. a IN hj_cube q m ==>
      hj_subst q z a IN E) /\
    (!z z' a a'. z IN Fs /\ z' IN Fs /\ a IN hj_cube q m /\
                 a' IN hj_cube q m /\
                 hj_subst q z a = hj_subst q z' a' ==> z = z')"

  let hj_tiling_union ← new_definition
   r"hj_tiling_union q m Fs =
  {x | ?z a. z IN Fs /\ a IN hj_cube q m /\ x = hj_subst q z a}"

  let HJ_TILING_EMPTY ← prove
   r"!q m n E. hj_tiling q m n {} E"
   (← do
    pure (REWRITE_TAC [hj_tiling, FINITE_EMPTY, NOT_IN_EMPTY]))

  let HJ_TILING_UNION_EMPTY ← prove
   r"!q m. hj_tiling_union q m {} = {}"
   (← do
    pure (REWRITE_TAC [hj_tiling_union, NOT_IN_EMPTY, EXTENSION, IN_ELIM_THM]))

  let HJ_TILING_UNION_SUBSET ← prove
   r"!q m n Fs E. hj_tiling q m n Fs E ==> hj_tiling_union q m Fs SUBSET E"
   (← do
    pure (REWRITE_TAC [hj_tiling, hj_tiling_union, SUBSET, IN_ELIM_THM] THEN
    MESON_TAC []))

  let HJ_TILING_UNION_CUBE ← prove
   r"!q m n Fs E. 1 <= q /\ hj_tiling q m n Fs E ==>
   hj_tiling_union q m Fs SUBSET hj_cube q n"
   (← do
    pure (REWRITE_TAC [hj_tiling, hj_tiling_union, SUBSET, IN_ELIM_THM] THEN
    MESON_TAC [HJ_SUBST_CUBE]))

  let HJ_TILING_INJ ← prove
   r"!q m n Fs E z z' a a'.
        hj_tiling q m n Fs E /\ z IN Fs /\ z' IN Fs /\
        a IN hj_cube q m /\ a' IN hj_cube q m /\
        hj_subst q z a = hj_subst q z' a'
        ==> z = z' /\ a = a'"
   (← do
    pure (REWRITE_TAC [hj_tiling] THEN REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"z:num->num = z'") SUBST_ALL_TAC THENL
     [ASM_MESON_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC HJ_SUBST_INJ THEN
    MAP_EVERY EXISTS_TAC [← q r"q:num", ← q r"q:num", ← q r"m:num", ← q r"n:num",
                          ← q r"z':num->num"] THEN
    ASM_MESON_TAC []))

  let CARD_HJ_TILING_UNION_RESTRICT ← prove
   r"!q m n Fs E (P:(num->num)->bool).
        hj_tiling q m n Fs E
        ==> &(CARD {x | x IN hj_tiling_union q m Fs /\ P x}) =
            sum Fs (\z. &(CARD {a | a IN hj_cube q m /\ P (hj_subst q z a)}))"
   (← do
    pure (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [hj_tiling]) THEN
    SUBGOAL_THEN
     (← q r"{x | x IN hj_tiling_union q m Fs /\ P x} =
      IMAGE (\(z,a). hj_subst q z a)
            {(z,a) | z IN Fs /\ a IN hj_cube q m /\ P (hj_subst q z a)}")
    SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, hj_tiling_union, IN_ELIM_THM, IN_IMAGE,
                   EXISTS_PAIR_THM] THEN
      REWRITE_TAC [IN_ELIM_PAIR_THM, PAIR_EQ] THEN MESON_TAC [],
      ALL_TAC] THEN
    wPart (fun t => do rand (← lhand t)) (fun t => do lhand (← rand t)) CARD_IMAGE_INJ THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC [FORALL_PAIR_THM, IN_ELIM_PAIR_THM, PAIR_EQ] THEN
        ASM_MESON_TAC [HJ_TILING_INJ],
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC (← q r"(Fs:(num->num)->bool) CROSS hj_cube q m") THEN
        ASM_SIMP_TAC [FINITE_CROSS, FINITE_HJ_CUBE] THEN
        REWRITE_TAC [SUBSET, FORALL_PAIR_THM, IN_ELIM_PAIR_THM, IN_CROSS] THEN
        MESON_TAC []],
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC (← ISPECL [← q r"Fs:(num->num)->bool",
      ← q r"\z. {a | a IN hj_cube q m /\ (P:(num->num)->bool) (hj_subst q z a)}",
      ← q r"\z:num->num a:num->num. &1"] SUM_SUM_PRODUCT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN GEN_TAC THEN DISCH_TAC THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"hj_cube q m") THEN
      REWRITE_TAC [FINITE_HJ_CUBE] THEN SET_TAC [],
      ALL_TAC] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN
    SUBGOAL_THEN (← q r"(\(i:num->num,j:num->num). &1) =
                  (\p:(num->num)#(num->num). &1)") SUBST1_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM, FORALL_PAIR_THM], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"FINITE {i,j | i IN Fs /\ j IN hj_cube q m /\
                    (P:(num->num)->bool) (hj_subst q i j)}")
    ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC (← q r"(Fs:(num->num)->bool) CROSS hj_cube q m") THEN
      ASM_SIMP_TAC [FINITE_CROSS, FINITE_HJ_CUBE] THEN
      REWRITE_TAC [SUBSET, FORALL_PAIR_THM, IN_ELIM_PAIR_THM, IN_CROSS] THEN
      MESON_TAC [],
      ALL_TAC] THEN
    ASM_SIMP_TAC [SUM_CONST, REAL_MUL_RID, FINITE_RESTRICT, FINITE_HJ_CUBE] THEN
    DISCH_THEN (fun th => tactic_of do pure (SUBST1_TAC (← SYM th))) THEN
    REWRITE_TAC []))

  let HJ_DENSITY_TILING_UNION_RESTRICT ← prove
   r"!q m n Fs E (P:(num->num)->bool).
        1 <= q /\ hj_tiling q m n Fs E
        ==> hj_density q n {x | x IN hj_tiling_union q m Fs /\ P x} =
            sum Fs (\z. hj_density q m {a | P (hj_subst q z a)}) *
            &(q EXP m) / &(q EXP n)"
   (← do
    let f1 ← REAL_FIELD
      (← q r"!c p r. ~(p = &0) ==> c * inv r = ((c * inv p) * p) * inv r")
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [HJ_DENSITY_CARD, IN_ELIM_THM] THEN
    SUBGOAL_THEN
     (← q r"{x | x IN hj_cube q n /\ x IN hj_tiling_union q m Fs /\ P x} =
      {x | x IN hj_tiling_union q m Fs /\ P x}")
    SUBST1_TAC THENL
     [MP_TAC (← SPEC_ALL HJ_TILING_UNION_CUBE) THEN
      ASM_REWRITE_TAC [] THEN SET_TAC [],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"q:num", ← q r"m:num", ← q r"n:num", ← q r"Fs:(num->num)->bool",
                      ← q r"E:(num->num)->bool", ← q r"P:(num->num)->bool"]
      CARD_HJ_TILING_UNION_RESTRICT) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [real_div, ← GSYM SUM_RMUL] THEN
    REWRITE_TAC [REAL_MUL_ASSOC] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC (← q r"z:num->num") THEN DISCH_TAC THEN REWRITE_TAC [] THEN
    MATCH_MP_TAC f1 THEN
    REWRITE_TAC [REAL_OF_NUM_EQ, EXP_EQ_0] THEN ASM_ARITH_TAC))

  let HJ_TILING_AVERAGE ← prove
   r"!q m n Fs E A c.
        1 <= q /\ hj_tiling q m n Fs E /\ ~(Fs = {}) /\
        c * hj_density q n (hj_tiling_union q m Fs) <=
        hj_density q n {x | x IN hj_tiling_union q m Fs /\ x IN A}
        ==> ?z. z IN Fs /\ c <= hj_density q m {a | hj_subst q z a IN A}"
   (← do
    -- right to left: the REAL_ARITH, then the SET_RULE
    let r2 ← REAL_ARITH
      (← q r"!s n c r. s * r < (n * c) * r ==> ~(c * n * r <= s * r)")
    let s1 ← SET_RULE (← q r"!s:(num->num)->bool. {x | x IN s} = s")
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"q:num", ← q r"m:num", ← q r"n:num", ← q r"Fs:(num->num)->bool",
                      ← q r"E:(num->num)->bool",
                      ← q r"\x:num->num. T"] HJ_DENSITY_TILING_UNION_RESTRICT) THEN
    MP_TAC (← ISPECL [← q r"q:num", ← q r"m:num", ← q r"n:num", ← q r"Fs:(num->num)->bool",
                      ← q r"E:(num->num)->bool", ← q r"\x:num->num. x IN A"]
      HJ_DENSITY_TILING_UNION_RESTRICT) THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [s1] THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN (← q r"&0 < &(q EXP m) / &(q EXP n)") ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN
       REWRITE_TAC [REAL_OF_NUM_LT, LT_NZ, EXP_EQ_0] THEN
      ASM_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"hj_density q m {a:num->num | T} = &1") ASSUME_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (← q r"hj_density q m (hj_cube q m)") THEN
      CONJ_TAC THENL [MATCH_MP_TAC HJ_DENSITY_EQ THEN SIMP_TAC [IN_ELIM_THM],
                      ASM_SIMP_TAC [HJ_DENSITY_CUBE]],
      ALL_TAC] THEN
    MATCH_MP_TAC (← TAUT (← q r"(~p ==> F) ==> p")) THEN
    DISCH_THEN (ASSUME_TAC o REWRITE_RULE
     [NOT_EXISTS_THM, ← TAUT (← q r"~(a /\ b) <=> a ==> ~b"), REAL_NOT_LE]) THEN
    SUBGOAL_THEN (← q r"FINITE(Fs:(num->num)->bool)") ASSUME_TAC THENL
     [ASM_MESON_TAC [hj_tiling], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"sum Fs (\z. hj_density q m {a | hj_subst q z a IN A}) <
      &(CARD(Fs:(num->num)->bool)) * c")
    ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q r"\z. hj_density q m {a | hj_subst q z a IN A}",
                        ← q r"\z:num->num. c:real", ← q r"Fs:(num->num)->bool"]
        SUM_LT_ALL) THEN
      ASM_SIMP_TAC [SUM_CONST],
      ALL_TAC] THEN
    UNDISCH_TAC
     (← q r"c * hj_density q n (hj_tiling_union q m Fs) <=
      hj_density q n {x | x IN hj_tiling_union q m Fs /\ x IN A}") THEN
    ASM_SIMP_TAC [SUM_CONST, REAL_MUL_RID] THEN
    MP_TAC (← ISPECL [← q r"sum Fs (\z. hj_density q m {a | hj_subst q z a IN A})",
                      ← q r"&(CARD(Fs:(num->num)->bool)) * c",
                      ← q r"&(q EXP m) / &(q EXP n)"] REAL_LT_RMUL) THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_ACCEPT_TAC r2))

  -- @@RETURN BEGIN
  return { hj_tiling, hj_tiling_union, HJ_TILING_EMPTY, HJ_TILING_UNION_EMPTY,
           HJ_TILING_UNION_SUBSET, HJ_TILING_UNION_CUBE, HJ_TILING_INJ,
           CARD_HJ_TILING_UNION_RESTRICT, HJ_DENSITY_TILING_UNION_RESTRICT,
           HJ_TILING_AVERAGE }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- Insensitivity under sections, pullbacks and intersections; block          -/
/- insertion.  (szemeredi.ml 4652-4846)                                      -/
/- ------------------------------------------------------------------------- -/

structure BlockInsert where
  -- @@FIELDS
  HJ_REPLACE_CONCAT : thm
  HJ_INSENSITIVE_SECTION_PREFIX : thm
  HJ_INSENSITIVE_SECTION_SUFFIX : thm
  HJ_INSENSITIVE_FORALL : thm
  HJ_INSENSITIVE_DIFF : thm
  HJ_INSENSITIVE_PULLBACK : thm
  HJ_INSENSITIVE_TRANSFER : thm
  hj_insert : thm
  HJ_INSERT_CUBE : thm
  HJ_INSERT_CONCAT : thm
  HJ_INSERT_INJ : thm
  SUM_HJ_INSERT : thm
  HJ_DENSITY_INSERT : thm
  FINITE_HJ_SUBSPACES : thm
  HJ_DROP_ZERO : thm
  HJ_SUBST_TILE : thm
  deriving Inhabited

@[nospecialize]
def setupBlockInsert [HolBase] (D : SzemerediDeps) (BFiniteMeans : FiniteMeans) (BWords : Words) (BLines : Lines) (BDensities : Densities) (BDKTCor5 : DKTCor5) (BInsensitive : Insensitive) :
    ExceptT String IO BlockInsert := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, new_definition, .. } := D
  let { ADD_CLAUSES, CARD_SUBSET, ETA_AX, FINITE_SUBSET, FUN_EQ_THM, IN_ELIM_THM, .. } := D.core1
  let { REAL_INV_MUL, REAL_MUL_AC, REAL_OF_NUM_POW, REAL_POW_ADD, SUBSET, SUM_EQ,
        SUM_RMUL, SUM_SWAP, real_div, .. } := D.core2
  let { fmean, .. } := BFiniteMeans
  let { CARD_HJ_CUBE, FINITE_HJ_CUBE, HJ_CONCAT_CUBE, HJ_CONCAT_INJ, HJ_CONCAT_SPLIT,
        HJ_DROP_CONCAT, HJ_DROP_CUBE, HJ_SUBSPACE_CUBE, HJ_SUBST_CUBE, HJ_SUBST_WORD,
        HJ_TAKE_CONCAT, HJ_TAKE_CUBE, IN_HJ_CUBE, SUM_HJ_CONCAT, hj_concat, hj_drop,
        hj_subst, .. } := BWords
  let { HJ_SUBST_JOIN, .. } := BLines
  let { hj_density, .. } := BDensities
  let { HJ_CUBE_MONO_IN, .. } := BDKTCor5
  let { hj_insensitive, hj_replace, .. } := BInsensitive
  -- @@SCOPE END

  let HJ_REPLACE_CONCAT ← prove
   r"!j i l x y. hj_replace j i (hj_concat l x y) =
               hj_concat l (hj_replace j i x) (hj_replace j i y)"
   (← do
    pure (REWRITE_TAC [hj_replace, hj_concat, FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"x':num < l") THEN ASM_REWRITE_TAC []))

  let HJ_INSENSITIVE_SECTION_PREFIX ← prove
   r"!q l r i j D y.
        hj_insensitive q (l + r) i j D /\ y IN hj_cube q l
        ==> hj_insensitive q r i j {x | hj_concat l y x IN D}"
   (← do
    pure (REWRITE_TAC [hj_insensitive, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC [HJ_CONCAT_CUBE, HJ_REPLACE_CONCAT]))

  let HJ_INSENSITIVE_SECTION_SUFFIX ← prove
   r"!q l r i j D x'.
        hj_insensitive q (l + r) i j D /\ x' IN hj_cube q r
        ==> hj_insensitive q l i j {z | hj_concat l z x' IN D}"
   (← do
    pure (REWRITE_TAC [hj_insensitive, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC [HJ_CONCAT_CUBE, HJ_REPLACE_CONCAT]))

  let HJ_INSENSITIVE_FORALL ← prove
   r"!q n i j (X:A->bool) D.
        (!a. a IN X ==> hj_insensitive q n i j (D a))
        ==> hj_insensitive q n i j {x | !a. a IN X ==> x IN D a}"
   (← do
    pure (REWRITE_TAC [hj_insensitive, IN_ELIM_THM] THEN MESON_TAC []))

  let HJ_INSENSITIVE_DIFF ← prove
   r"!q n i j D1 D2.
        hj_insensitive q n i j D1 /\ hj_insensitive q n i j D2
        ==> hj_insensitive q n i j {x | x IN D1 /\ ~(x IN D2)}"
   (← do
    pure (REWRITE_TAC [hj_insensitive, IN_ELIM_THM] THEN MESON_TAC []))

  let HJ_INSENSITIVE_PULLBACK ← prove
   r"!k m n i z D.
        1 <= k /\ hj_insensitive (k + 1) n i k D /\ hj_subspace (k + 1) m n z
        ==> hj_insensitive (k + 1) m i k {a | hj_subst (k + 1) z a IN D}"
   (← do
    -- right to left: the second ARITH_RULE, then the first
    let a2 ← ARITH_RULE (← q r"1 <= k + 1")
    let a1 ← ARITH_RULE (← q r"1 <= k + 1")
    pure (REWRITE_TAC [hj_insensitive, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC [HJ_SUBST_CUBE, a1],
      ASM_MESON_TAC [HJ_SUBST_CUBE, a2],
      ALL_TAC] THEN
    UNDISCH_TAC (← q r"hj_replace k i x = hj_replace k i (y:num->num)") THEN
    REWRITE_TAC [hj_replace, hj_subst, FUN_EQ_THM] THEN DISCH_TAC THEN
    X_GEN_TAC (← q r"r:num") THEN ASM_CASES_TAC (← q r"(z:num->num) r < k + 1") THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"(z:num->num) r - (k + 1)")) THEN
    REWRITE_TAC []))

  let HJ_INSENSITIVE_TRANSFER ← prove
   r"!k m M1 i V D.
        1 <= k /\ i < k /\ hj_subspace (k + 1) m M1 V /\
        hj_insensitive (k + 1) M1 i k D /\
        (!a. a IN hj_cube k m ==> hj_subst (k + 1) V a IN D)
        ==> !a. a IN hj_cube (k + 1) m ==> hj_subst (k + 1) V a IN D"
   (← do
    -- right to left: the three ARITH_RULEs from the last to the first
    let a3 ← ARITH_RULE (← q r"1 <= k + 1")
    let a2 ← ARITH_RULE (← q r"k <= k + 1")
    let a1 ← ARITH_RULE (← q r"1 <= k + 1")
    pure (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"hj_replace k i (a:num->num) IN hj_cube k m") ASSUME_TAC THENL
     [UNDISCH_TAC (← q r"(a:num->num) IN hj_cube (k + 1) m") THEN
      REWRITE_TAC [IN_HJ_CUBE, hj_replace] THEN STRIP_TAC THEN CONJ_TAC THEN
      X_GEN_TAC (← q r"r:num") THEN DISCH_TAC THENL
       [COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
        SUBGOAL_THEN (← q r"(a:num->num) r < k + 1") MP_TAC THENL
         [ASM_SIMP_TAC [], ASM_ARITH_TAC],
        SUBGOAL_THEN (← q r"(a:num->num) r = 0") SUBST1_TAC THENL
         [ASM_SIMP_TAC [], ASM_ARITH_TAC]],
      ALL_TAC] THEN
    UNDISCH_TAC (← q r"hj_insensitive (k + 1) M1 i k D") THEN
    REWRITE_TAC [hj_insensitive] THEN
    DISCH_THEN (MP_TAC o SPECL [← q r"hj_subst (k + 1) V (hj_replace k i a)",
                                ← q r"hj_subst (k + 1) V a"]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC HJ_SUBST_CUBE THEN EXISTS_TAC (← q r"m:num") THEN
        ASM_REWRITE_TAC [a1] THEN
        ASM_MESON_TAC [HJ_CUBE_MONO_IN, a2],
        MATCH_MP_TAC HJ_SUBST_CUBE THEN EXISTS_TAC (← q r"m:num") THEN
        ASM_REWRITE_TAC [a3],
        REWRITE_TAC [hj_replace, hj_subst, FUN_EQ_THM] THEN X_GEN_TAC (← q r"r:num") THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
        ASM_CASES_TAC (← q r"(a:num->num) ((V:num->num) r - (k + 1)) = k") THEN
        ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC],
      ASM_SIMP_TAC []]))

  let hj_insert ← new_definition
   r"hj_insert p M1 (w:num->num) (z:num->num) =
    hj_concat p (hj_take p w) (hj_concat M1 z (hj_drop p w))"

  let HJ_INSERT_CUBE ← prove
   r"!q p M1 r w z. w IN hj_cube q (p + r) /\ z IN hj_cube q M1
                  ==> hj_insert p M1 w z IN hj_cube q (p + (M1 + r))"
   (← do
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [hj_insert] THEN
    MATCH_MP_TAC HJ_CONCAT_CUBE THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HJ_TAKE_CUBE THEN EXISTS_TAC (← q r"r:num") THEN ASM_REWRITE_TAC [],
      MATCH_MP_TAC HJ_CONCAT_CUBE THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC HJ_DROP_CUBE THEN ASM_REWRITE_TAC []]))

  let HJ_INSERT_CONCAT ← prove
   r"!q p M1 y x z. y IN hj_cube q p
                  ==> hj_insert p M1 (hj_concat p y x) z =
                      hj_concat p y (hj_concat M1 z x)"
   (← do
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [hj_insert, HJ_DROP_CONCAT] THEN
    ASM_MESON_TAC [HJ_TAKE_CONCAT]))

  let HJ_INSERT_INJ ← prove
   r"!q p M1 r w w' z z'.
        w IN hj_cube q (p + r) /\ w' IN hj_cube q (p + r) /\
        z IN hj_cube q M1 /\ z' IN hj_cube q M1 /\
        hj_insert p M1 w z = hj_insert p M1 w' z'
        ==> w = w' /\ z = z'"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [hj_insert] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"hj_take p (w:num->num) IN hj_cube q p /\
      hj_take p (w':num->num) IN hj_cube q p")
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC HJ_TAKE_CUBE THEN EXISTS_TAC (← q r"r:num") THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"q:num", ← q r"p:num", ← q r"hj_take p (w:num->num)",
                      ← q r"hj_concat M1 z (hj_drop p (w:num->num))",
                      ← q r"hj_take p (w':num->num)",
                      ← q r"hj_concat M1 z' (hj_drop p (w':num->num))"]
                       HJ_CONCAT_INJ) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"q:num", ← q r"M1:num", ← q r"z:num->num",
                      ← q r"hj_drop p (w:num->num)",
                      ← q r"z':num->num", ← q r"hj_drop p (w':num->num)"] HJ_CONCAT_INJ) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [← GSYM HJ_CONCAT_SPLIT] THEN ASM_MESON_TAC [HJ_CONCAT_SPLIT]))

  let SUM_HJ_INSERT ← prove
   r"!q p M1 r f.
        sum (hj_cube q (p + (M1 + r))) f =
        sum (hj_cube q (p + r))
            (\w. sum (hj_cube q M1) (\z. f (hj_insert p M1 w z)))"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [SUM_HJ_CONCAT] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC (← q r"y:num->num") THEN DISCH_TAC THEN
    REWRITE_TAC [← MATCH_MP HJ_INSERT_CONCAT
                  (← ASSUME (← q r"(y:num->num) IN hj_cube q p"))] THEN
    MP_TAC (← ISPECL
             [← q r"\z x. (f:(num->num)->real) (hj_concat p y (hj_concat M1 z x))",
              ← q r"hj_cube q M1", ← q r"hj_cube q r"] SUM_SWAP) THEN
    REWRITE_TAC [FINITE_HJ_CUBE]))

  let HJ_DENSITY_INSERT ← prove
   r"!q p M1 r E.
        hj_density q (p + (M1 + r)) E =
        fmean (hj_cube q (p + r))
          (\w. hj_density q M1 {z | hj_insert p M1 w z IN E})"
   (← do
    pure (REPEAT GEN_TAC THEN
    REWRITE_TAC [hj_density, fmean, IN_ELIM_THM, CARD_HJ_CUBE] THEN
    REWRITE_TAC [SUM_HJ_INSERT] THEN REWRITE_TAC [real_div, SUM_RMUL] THEN
    REWRITE_TAC [← GSYM REAL_OF_NUM_POW] THEN
    REWRITE_TAC [REAL_POW_ADD, REAL_INV_MUL] THEN REWRITE_TAC [REAL_MUL_AC]))

  let FINITE_HJ_SUBSPACES ← prove
   r"!q m n. FINITE {V | hj_subspace q m n V} /\
           CARD {V | hj_subspace q m n V} <= (q + m) EXP n"
   (← do
    pure (REPEAT GEN_TAC THEN
    SUBGOAL_THEN (← q r"{V | hj_subspace q m n V} SUBSET hj_cube (q + m) n")
    ASSUME_TAC THENL
     [REWRITE_TAC [SUBSET, IN_ELIM_THM, HJ_SUBSPACE_CUBE], ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC [FINITE_SUBSET, FINITE_HJ_CUBE],
      REWRITE_TAC [← GSYM CARD_HJ_CUBE] THEN MATCH_MP_TAC CARD_SUBSET THEN
      ASM_REWRITE_TAC [FINITE_HJ_CUBE]]))

  let HJ_DROP_ZERO ← prove
   r"!a. hj_drop 0 a = a"
   (← do
    pure (REWRITE_TAC [hj_drop, ADD_CLAUSES, ETA_AX]))

  let HJ_SUBST_TILE ← prove
   r"!q p M1 r m V w a.
        1 <= q /\ w IN hj_cube q (p + r)
        ==> hj_subst q
              (hj_join q p 0 (hj_take p w)
                 (hj_join q M1 m V (hj_drop p w))) a =
            hj_insert p M1 w (hj_subst q V a)"
   (← do
    pure (REPEAT STRIP_TAC THEN
    REWRITE_TAC [HJ_SUBST_JOIN, hj_insert, HJ_DROP_ZERO] THEN
    SUBGOAL_THEN (← q r"hj_take p (w:num->num) IN hj_cube q p /\
                  hj_drop p (w:num->num) IN hj_cube q r")
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC HJ_TAKE_CUBE THEN EXISTS_TAC (← q r"r:num") THEN ASM_REWRITE_TAC [],
        MATCH_MP_TAC HJ_DROP_CUBE THEN ASM_REWRITE_TAC []],
      ALL_TAC] THEN
    ASM_MESON_TAC [HJ_SUBST_WORD]))

  -- @@RETURN BEGIN
  return { HJ_REPLACE_CONCAT, HJ_INSENSITIVE_SECTION_PREFIX,
           HJ_INSENSITIVE_SECTION_SUFFIX, HJ_INSENSITIVE_FORALL, HJ_INSENSITIVE_DIFF,
           HJ_INSENSITIVE_PULLBACK, HJ_INSENSITIVE_TRANSFER, hj_insert, HJ_INSERT_CUBE,
           HJ_INSERT_CONCAT, HJ_INSERT_INJ, SUM_HJ_INSERT, HJ_DENSITY_INSERT,
           FINITE_HJ_SUBSPACES, HJ_DROP_ZERO, HJ_SUBST_TILE }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- One greedy tiling step.  (szemeredi.ml 4847-5228)                         -/
/- ------------------------------------------------------------------------- -/

structure TileStep where
  -- @@FIELDS
  HJ_INSENSITIVE_EQ : thm
  HJ_INSENSITIVE_LEFTOVER : thm
  DKT_TILE_STEP : thm
  deriving Inhabited

@[nospecialize]
def setupTileStep [HolBase] (D : SzemerediDeps) (BWords : Words) (BLines : Lines) (BDensities : Densities) (BDensityHJ : DensityHJ) (BUniformSubspaces : UniformSubspaces) (BDKTCor5 : DKTCor5) (BInsensitive : Insensitive) (BCor11 : Cor11) (BTilings : Tilings) (BBlockInsert : BlockInsert) :
    ExceptT String IO TileStep := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON_TAC,
        REAL_ARITH, REAL_FIELD, SELECT_CONV, SET_RULE, SET_TAC, .. } := D
  let { ADD_CLAUSES, CARD_EQ_0, CARD_IMAGE_INJ, EQ_TRANS, EXP_ADD, EXP_EQ_0,
        FINITE_IMAGE, FINITE_SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM, IN_IMAGE,
        LEFT_IMP_EXISTS_THM, LE_REFL, LT_NZ, MEMBER_NOT_EMPTY, MONO_EXISTS, .. } := D.core1
  let { REAL_EQ_IMP_LE, REAL_LE_DIV, REAL_LE_INV2, REAL_LE_LDIV_EQ, REAL_LE_LMUL,
        REAL_LE_RMUL, REAL_LE_TRANS, REAL_LT_DIV, REAL_LT_IMP_LE, REAL_LT_MUL,
        REAL_MUL_RID, REAL_OF_NUM_EQ, REAL_OF_NUM_LE, REAL_OF_NUM_LT, REAL_OF_NUM_MUL,
        REAL_POS, SUBSET, SUM_CONST, real_div, .. } := D.core2
  let { FINITE_HJ_CUBE, HJ_CONCAT_CUBE, HJ_CONCAT_SPLIT, HJ_DROP_CUBE, HJ_SUBSPACE_0,
        HJ_SUBST_CUBE, HJ_TAKE_CUBE, IN_HJ_CUBE, .. } := BWords
  let { HJ_SUBSPACE_JOIN, .. } := BLines
  let { HJ_DENSITY_CARD, HJ_DENSITY_EQ, HJ_DENSITY_LE_1, HJ_DENSITY_MARKOV,
        HJ_DENSITY_MONO, .. } := BDensities
  let { HJ_DENSITY_PIGEONHOLE, HJ_DENSITY_POS_EXISTS, .. } := BDensityHJ
  let { HJ_CONCAT_ASSOC, .. } := BUniformSubspaces
  let { DKT_COR5, .. } := BDKTCor5
  let { hj_insensitive, .. } := BInsensitive
  let { HJ_DENSITY_CUBE, .. } := BCor11
  let { HJ_DENSITY_TILING_UNION_RESTRICT, hj_tiling, hj_tiling_union, .. } := BTilings
  let { FINITE_HJ_SUBSPACES, HJ_DENSITY_INSERT, HJ_INSENSITIVE_DIFF,
        HJ_INSENSITIVE_FORALL, HJ_INSENSITIVE_SECTION_PREFIX,
        HJ_INSENSITIVE_SECTION_SUFFIX, HJ_INSENSITIVE_TRANSFER, HJ_INSERT_CONCAT,
        HJ_INSERT_INJ, HJ_SUBST_TILE, hj_insert, .. } := BBlockInsert
  -- @@SCOPE END

  let HJ_INSENSITIVE_EQ ← prove
   r"!q n i j D D'.
        hj_insensitive q n i j D /\
        (!x. x IN hj_cube q n ==> (x IN D <=> x IN D'))
        ==> hj_insensitive q n i j D'"
   (← do
    pure (REWRITE_TAC [hj_insensitive] THEN MESON_TAC []))

  let HJ_INSENSITIVE_LEFTOVER ← prove
   r"!q p M1 r i j E Z y.
        (!y0. y0 IN hj_cube q p
              ==> hj_insensitive q (M1 + r) i j {x | hj_concat p y0 x IN E}) /\
        Z SUBSET hj_cube q M1 /\ y IN hj_cube q (p + M1)
        ==> hj_insensitive q r i j
              {x | hj_concat (p + M1) y x IN E /\
                   ~(?w z. w IN hj_cube q (p + r) /\
                           (!z'. z' IN Z ==> hj_insert p M1 w z' IN E) /\
                           z IN Z /\
                           hj_concat (p + M1) y x = hj_insert p M1 w z)}"
   (← do
    pure (REPEAT STRIP_TAC THEN
    ABBREV_TAC (← q r"y0 = hj_take p (y:num->num)") THEN
    ABBREV_TAC (← q r"z0 = hj_drop p (y:num->num)") THEN
    SUBGOAL_THEN (← q r"(y0:num->num) IN hj_cube q p /\ (z0:num->num) IN hj_cube q M1")
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["y0", "z0"] THEN CONJ_TAC THENL
       [MATCH_MP_TAC HJ_TAKE_CUBE THEN EXISTS_TAC (← q r"M1:num") THEN
        ASM_REWRITE_TAC [],
        MATCH_MP_TAC HJ_DROP_CUBE THEN ASM_REWRITE_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN
      (← q r"!x. hj_concat (p + M1) y x = hj_concat p y0 (hj_concat M1 z0 x)")
    ASSUME_TAC THENL
     [GEN_TAC THEN REWRITE_TAC [HJ_CONCAT_ASSOC] THEN
      MAP_EVERY EXPAND_TAC ["y0", "z0"] THEN REWRITE_TAC [HJ_CONCAT_SPLIT],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!x. x IN hj_cube q r
          ==> ((?w z. w IN hj_cube q (p + r) /\
                      (!z'. z' IN Z ==> hj_insert p M1 w z' IN E) /\
                      z IN Z /\ hj_concat (p + M1) y x = hj_insert p M1 w z) <=>
               (z0:num->num) IN Z /\
               !z'. z' IN Z ==> hj_concat p y0 (hj_concat M1 z' x) IN E)")
    ASSUME_TAC THENL
     [X_GEN_TAC (← q r"x:num->num") THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"hj_concat p y0 (x:num->num) IN hj_cube q (p + r)") ASSUME_TAC
      THENL [MATCH_MP_TAC HJ_CONCAT_CUBE THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"!z'. hj_insert p M1 (hj_concat p y0 x) z' =
                         hj_concat p y0 (hj_concat M1 z' (x:num->num))")
      ASSUME_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC HJ_INSERT_CONCAT THEN EXISTS_TAC (← q r"q:num") THEN
        ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN EQ_TAC THENL
       [REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
        MAP_EVERY X_GEN_TAC [← q r"w:num->num", ← q r"z:num->num"] THEN STRIP_TAC THEN
        MP_TAC (← ISPECL [← q r"q:num", ← q r"p:num", ← q r"M1:num", ← q r"r:num",
                          ← q r"hj_concat p y0 (x:num->num)", ← q r"w:num->num",
                          ← q r"z0:num->num", ← q r"z:num->num"] HJ_INSERT_INJ) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM SET_TAC [], ALL_TAC] THEN
        DISCH_THEN (CONJUNCTS_THEN (fun th => tactic_of do
          pure (SUBST_ALL_TAC (← SYM th)))) THEN
        ASM_MESON_TAC [],
        STRIP_TAC THEN MAP_EVERY EXISTS_TAC
         [← q r"hj_concat p y0 (x:num->num)", ← q r"z0:num->num"] THEN
        ASM_REWRITE_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!z'. z' IN hj_cube q M1
           ==> hj_insensitive q r i j
                 {x | hj_concat M1 z' x IN {u | hj_concat p y0 u IN E}}")
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC HJ_INSENSITIVE_SECTION_PREFIX THEN
      ASM_SIMP_TAC [],
      ALL_TAC] THEN
    MATCH_MP_TAC HJ_INSENSITIVE_EQ THEN ASM_CASES_TAC (← q r"(z0:num->num) IN Z") THENL
     [EXISTS_TAC
       (← q r"{x | x IN {x | hj_concat M1 z0 x IN {u | hj_concat p y0 u IN E}} /\
             ~(x IN {x | !z'. z' IN Z ==>
                         x IN {x | hj_concat M1 z' x IN
                                 {u | hj_concat p y0 u IN E}}})}")
      THEN CONJ_TAC THENL
       [MATCH_MP_TAC HJ_INSENSITIVE_DIFF THEN ASM_SIMP_TAC [] THEN
        MATCH_MP_TAC HJ_INSENSITIVE_FORALL THEN ASM SET_TAC [],
        ASM_SIMP_TAC [IN_ELIM_THM]],
      EXISTS_TAC (← q r"{x | hj_concat M1 z0 x IN {u | hj_concat p y0 u IN E}}") THEN
      ASM_SIMP_TAC [IN_ELIM_THM]]))

  let DKT_TILE_STEP ← prove
   r"!k m beta i.
        1 <= k /\ density_hales_jewett k /\ 1 <= m /\ &0 < beta /\ i < k
        ==> ?M1 Theta.
              &0 < Theta /\
              !p r E.
                (!y. y IN hj_cube (k + 1) p
                     ==> hj_insensitive (k + 1) (M1 + r) i k
                           {x | hj_concat p y x IN E}) /\
                &2 * beta <= hj_density (k + 1) (p + (M1 + r)) E
                ==> ?Fs. hj_tiling (k + 1) m (p + (M1 + r)) Fs E /\
                         Theta <=
                         hj_density (k + 1) (p + (M1 + r))
                           (hj_tiling_union (k + 1) m Fs) /\
                         !y. y IN hj_cube (k + 1) (p + M1)
                             ==> hj_insensitive (k + 1) r i k
                                   {x | hj_concat (p + M1) y x IN E /\
                                        ~(hj_concat (p + M1) y x IN
                                          hj_tiling_union (k + 1) m Fs)}"
   (← do
    -- right to left: the thirteen rules from the last to the first
    let a13 ← ARITH_RULE (← q r"1 <= k + 1")
    let f12 ← REAL_FIELD (← q r"~(b = &0) ==> a = a / b * b")
    let a11 ← ARITH_RULE (← q r"1 <= k + 1")
    let s10 ← SET_RULE (← q r"!s:(num->num)->bool. {x | x IN s} = s")
    let a9 ← ARITH_RULE (← q r"1 <= k + 1")
    let a8 ← ARITH_RULE (← q r"1 <= k + 1")
    let a7 ← ARITH_RULE (← q r"1 <= k + 1")
    let a6 ← ARITH_RULE (← q r"1 <= k + 1")
    let a5 ← ARITH_RULE (← q r"1 <= k + 1")
    let r4 ← REAL_ARITH (← q r"!a b c d:real. a <= b /\ b <= c * d ==> a <= d * c")
    let a3 ← ARITH_RULE (← q r"(k + 1) + m = k + 1 + m")
    let r2 ← REAL_ARITH (← q r"!b x. &2 * b - b <= x ==> b <= x")
    let a1 ← ARITH_RULE (← q r"1 <= k + 1")
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← SPEC (← q r"k:num") DKT_COR5) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o SPECL [← q r"m:num", ← q r"beta:real"]) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"M1:num") (LABEL_TAC "mdhj")) THEN
    EXISTS_TAC (← q r"M1:num") THEN
    EXISTS_TAC (← q r"beta / &((k + 1 + m) EXP M1) * &((k + 1) EXP m) /
                &((k + 1) EXP M1)") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_REWRITE_TAC [REAL_OF_NUM_LT, LT_NZ, EXP_EQ_0] THEN ARITH_TAC,
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [← q r"p:num", ← q r"r:num", ← q r"E:(num->num)->bool"] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"!w. w IN hj_cube (k + 1) (p + r)
          ==> hj_insensitive (k + 1) M1 i k {z | hj_insert p M1 w z IN E}")
    ASSUME_TAC THENL
     [X_GEN_TAC (← q r"w:num->num") THEN DISCH_TAC THEN REWRITE_TAC [hj_insert] THEN
      MP_TAC (← ISPECL [← q r"k + 1", ← q r"M1:num", ← q r"r:num", ← q r"i:num",
                        ← q r"k:num",
                        ← q r"{u | hj_concat p (hj_take p w) u IN E}",
                        ← q r"hj_drop p (w:num->num)"]
        HJ_INSENSITIVE_SECTION_SUFFIX) THEN
      REWRITE_TAC [IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC HJ_TAKE_CUBE THEN
        EXISTS_TAC (← q r"r:num") THEN ASM_REWRITE_TAC [],
        MATCH_MP_TAC HJ_DROP_CUBE THEN ASM_REWRITE_TAC []],
      ALL_TAC] THEN
    ABBREV_TAC
     (← q r"G = {w | beta <= hj_density (k + 1) M1 {z | hj_insert p M1 w z IN E}}") THEN
    SUBGOAL_THEN (← q r"beta <= hj_density (k + 1) (p + r) G") ASSUME_TAC THENL
     [EXPAND_TAC "G" THEN
      MP_TAC (← ISPECL [← q r"k + 1", ← q r"p + r:num",
                        ← q r"\w. hj_density (k + 1) M1 {z | hj_insert p M1 w z IN E}",
                        ← q r"&2 * beta", ← q r"beta:real"] HJ_DENSITY_MARKOV) THEN
      REWRITE_TAC [HJ_DENSITY_LE_1, a1] THEN
      ASM_SIMP_TAC [REAL_LT_IMP_LE, ← GSYM HJ_DENSITY_INSERT] THEN
      DISCH_TAC THEN MATCH_MP_TAC r2 THEN FIRST_ASSUM ACCEPT_TAC,
      ALL_TAC] THEN
    ABBREV_TAC
     (← q r"Vw = \w. @V. hj_subspace (k + 1) m M1 V /\
                   !a. a IN hj_cube (k + 1) m ==>
                     hj_insert p M1 w (hj_subst (k + 1) V a) IN E") THEN
    SUBGOAL_THEN
     (← q r"!w. w IN hj_cube (k + 1) (p + r) /\ w IN G
          ==> hj_subspace (k + 1) m M1 ((Vw:(num->num)->(num->num)) w) /\
              !a. a IN hj_cube (k + 1) m
                  ==> hj_insert p M1 w (hj_subst (k + 1) (Vw w) a) IN E")
    ASSUME_TAC THENL
     [X_GEN_TAC (← q r"w:num->num") THEN STRIP_TAC THEN EXPAND_TAC "Vw" THEN
      CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN CONV_TAC SELECT_CONV THEN
      REMOVE_THEN "mdhj" (MP_TAC o SPECL
       [← q r"M1:num", ← q r"{z | hj_insert p M1 w z IN E}"]) THEN
      ANTS_TAC THENL
       [REWRITE_TAC [LE_REFL] THEN UNDISCH_TAC (← q r"(w:num->num) IN G") THEN
        EXPAND_TAC "G" THEN REWRITE_TAC [IN_ELIM_THM],
        ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"V:num->num") THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [] THEN
      MP_TAC (← ISPECL [← q r"k:num", ← q r"m:num", ← q r"M1:num", ← q r"i:num",
                        ← q r"V:num->num",
                        ← q r"{z | hj_insert p M1 w z IN E}"]
                         HJ_INSENSITIVE_TRANSFER) THEN
      ASM_SIMP_TAC [IN_ELIM_THM],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"k + 1", ← q r"p + r:num", ← q r"G:(num->num)->bool",
                      ← q r"Vw:(num->num)->(num->num)",
                      ← q r"{V | hj_subspace (k + 1) m M1 V}"]
      HJ_DENSITY_PIGEONHOLE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC [FINITE_HJ_SUBSPACES, IN_ELIM_THM] THEN ASM_SIMP_TAC [] THEN
      REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, IN_ELIM_THM] THEN
      MP_TAC (← SPECL [← q r"k + 1", ← q r"p + r:num", ← q r"G:(num->num)->bool"]
        HJ_DENSITY_POS_EXISTS) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC, ASM_MESON_TAC []],
      ALL_TAC] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"V0:num->num") STRIP_ASSUME_TAC) THEN
    ABBREV_TAC
     (← q r"S0 = {w | w IN hj_cube (k + 1) (p + r) /\
                !a. a IN hj_cube (k + 1) m
                    ==> hj_insert p M1 w (hj_subst (k + 1) V0 a) IN E}") THEN
    SUBGOAL_THEN
     (← q r"beta / &((k + 1 + m) EXP M1) <= hj_density (k + 1) (p + r) S0")
    ASSUME_TAC THENL
     [MP_TAC (← SPECL [← q r"k + 1", ← q r"m:num", ← q r"M1:num"] FINITE_HJ_SUBSPACES) THEN
      REWRITE_TAC [a3] THEN STRIP_TAC THEN
      SUBGOAL_THEN (← q r"&0 < &(CARD {V | hj_subspace (k + 1) m M1 V})")
      ASSUME_TAC THENL
       [REWRITE_TAC [REAL_OF_NUM_LT, LT_NZ] THEN ASM_SIMP_TAC [CARD_EQ_0] THEN
        REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, IN_ELIM_THM] THEN
        EXISTS_TAC (← q r"V0:num->num") THEN ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
       (← q r"hj_density (k + 1) (p + r) {w | w IN G /\
         (Vw:(num->num)->(num->num)) w = V0}") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC (← q r"beta / &(CARD {V | hj_subspace (k + 1) m M1 V})") THEN
        CONJ_TAC THENL
         [REWRITE_TAC [real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
          CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
          MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC [REAL_OF_NUM_LE],
          ASM_SIMP_TAC [REAL_LE_LDIV_EQ] THEN
          MATCH_MP_TAC r4 THEN
          EXISTS_TAC (← q r"hj_density (k + 1) (p + r) G") THEN ASM_REWRITE_TAC []],
        MATCH_MP_TAC HJ_DENSITY_MONO THEN EXPAND_TAC "S0" THEN
        REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"w:num->num") THEN STRIP_TAC THEN
        ASM_REWRITE_TAC [] THEN
        FIRST_X_ASSUM (fun th => tactic_of do
          let ok ← if is_forall (concl th) then do
              let v ← q r"Vw:(num->num)->(num->num)"
              pure (can (find_term (fun u => u == v)) (concl th))
            else pure false
          pure (MP_TAC (← SPEC (← q r"w:num->num")
            (← liftExcept (check (fun _ => ok) th))))) THEN
        ASM_REWRITE_TAC [] THEN SIMP_TAC []],
      ALL_TAC] THEN
    ABBREV_TAC
     (← q r"tile = \w. hj_join (k + 1) p 0 (hj_take p w)
                     (hj_join (k + 1) M1 m V0 (hj_drop p (w:num->num)))") THEN
    SUBGOAL_THEN
     (← q r"!w a. w IN hj_cube (k + 1) (p + r)
            ==> hj_subst (k + 1) ((tile:(num->num)->(num->num)) w) a =
                hj_insert p M1 w (hj_subst (k + 1) V0 a)")
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "tile" THEN REWRITE_TAC [] THEN
      MATCH_MP_TAC HJ_SUBST_TILE THEN EXISTS_TAC (← q r"r:num") THEN
      ASM_REWRITE_TAC [a5],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!w. w IN hj_cube (k + 1) (p + r)
          ==> hj_subspace (k + 1) m (p + (M1 + r))
                ((tile:(num->num)->(num->num)) w)")
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "tile" THEN REWRITE_TAC [] THEN
      MP_TAC (← ISPECL [← q r"k + 1", ← q r"M1:num", ← q r"m:num", ← q r"0", ← q r"r:num",
                        ← q r"V0:num->num",
                        ← q r"hj_drop p (w:num->num)"] HJ_SUBSPACE_JOIN) THEN
      MP_TAC (← ISPECL [← q r"k + 1", ← q r"p:num", ← q r"0", ← q r"m + 0", ← q r"M1 + r:num",
                        ← q r"hj_take p (w:num->num)",
                        ← q r"hj_join (k + 1) M1 m V0 (hj_drop p (w:num->num))"]
                         HJ_SUBSPACE_JOIN) THEN
      REWRITE_TAC [ADD_CLAUSES, HJ_SUBSPACE_0] THEN
      SUBGOAL_THEN (← q r"hj_take p (w:num->num) IN hj_cube (k + 1) p /\
                    hj_drop p (w:num->num) IN hj_cube (k + 1) r")
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC HJ_TAKE_CUBE THEN EXISTS_TAC (← q r"r:num") THEN
          ASM_REWRITE_TAC [],
          MATCH_MP_TAC HJ_DROP_CUBE THEN ASM_REWRITE_TAC []],
        ASM_SIMP_TAC [a6]],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!w w'. w IN hj_cube (k + 1) (p + r) /\
                         w' IN hj_cube (k + 1) (p + r) /\
                         ((tile:(num->num)->(num->num)) w = tile w')
                         ==> w = w'")
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o AP_TERM (← q r"\z. hj_subst (k + 1) z (\i:num. 0)") o
        check (fun th => is_eq (concl th))) THEN
      ASM_SIMP_TAC [] THEN DISCH_TAC THEN
      MP_TAC (← ISPECL [← q r"k + 1", ← q r"p:num", ← q r"M1:num", ← q r"r:num",
                        ← q r"w:num->num",
                        ← q r"w':num->num", ← q r"hj_subst (k + 1) V0 (\i:num. 0)",
                        ← q r"hj_subst (k + 1) V0 (\i:num. 0)"] HJ_INSERT_INJ) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC HJ_SUBST_CUBE THEN EXISTS_TAC (← q r"m:num") THEN
      ASM_REWRITE_TAC [a7, IN_HJ_CUBE] THEN ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"S0 SUBSET hj_cube (k + 1) (p + r)") ASSUME_TAC THENL
     [EXPAND_TAC "S0" THEN SET_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"hj_tiling (k + 1) m (p + (M1 + r))
             (IMAGE (tile:(num->num)->(num->num)) S0) E")
    ASSUME_TAC THENL
     [REWRITE_TAC [hj_tiling, FORALL_IN_IMAGE] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_IMAGE THEN
        ASM_MESON_TAC [FINITE_SUBSET, FINITE_HJ_CUBE],
        X_GEN_TAC (← q r"w:num->num") THEN DISCH_TAC THEN
        SUBGOAL_THEN (← q r"(w:num->num) IN hj_cube (k + 1) (p + r)") ASSUME_TAC THENL
         [ASM SET_TAC [], ALL_TAC] THEN
        ASM_SIMP_TAC [] THEN UNDISCH_TAC (← q r"(w:num->num) IN S0") THEN
        EXPAND_TAC "S0" THEN SIMP_TAC [IN_ELIM_THM],
        REWRITE_TAC [IN_IMAGE] THEN REPEAT STRIP_TAC THEN
        ASM_REWRITE_TAC [] THEN AP_TERM_TAC THEN
        SUBGOAL_THEN (← q r"(x:num->num) IN hj_cube (k + 1) (p + r) /\
                      (x':num->num) IN hj_cube (k + 1) (p + r)")
        STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
        UNDISCH_TAC (← q r"hj_subst (k + 1) z a = hj_subst (k + 1) z' a'") THEN
        ASM_SIMP_TAC [] THEN DISCH_TAC THEN
        MP_TAC (← ISPECL [← q r"k + 1", ← q r"p:num", ← q r"M1:num", ← q r"r:num",
                          ← q r"x:num->num",
                          ← q r"x':num->num", ← q r"hj_subst (k + 1) V0 a",
                          ← q r"hj_subst (k + 1) V0 a'"] HJ_INSERT_INJ) THEN
        ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
         [CONJ_TAC THEN MATCH_MP_TAC HJ_SUBST_CUBE THEN EXISTS_TAC (← q r"m:num") THEN
          ASM_REWRITE_TAC [a8],
          SIMP_TAC []]],
      ALL_TAC] THEN
    EXISTS_TAC (← q r"IMAGE (tile:(num->num)->(num->num)) S0") THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [MP_TAC (← ISPECL [← q r"k + 1", ← q r"m:num", ← q r"p + (M1 + r):num",
                        ← q r"IMAGE (tile:(num->num)->(num->num)) S0",
                        ← q r"E:(num->num)->bool", ← q r"\x:num->num. T"]
        HJ_DENSITY_TILING_UNION_RESTRICT) THEN
      ASM_REWRITE_TAC [a9] THEN
      REWRITE_TAC [s10] THEN
      DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN (← q r"hj_density (k + 1) m {a:num->num | T} = &1") SUBST1_TAC THENL
       [MATCH_MP_TAC EQ_TRANS THEN
         EXISTS_TAC (← q r"hj_density (k + 1) m (hj_cube (k + 1) m)") THEN
        CONJ_TAC THENL [MATCH_MP_TAC HJ_DENSITY_EQ THEN SIMP_TAC [IN_ELIM_THM],
                        SIMP_TAC [HJ_DENSITY_CUBE, a11]],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"FINITE(S0:(num->num)->bool)") ASSUME_TAC THENL
       [ASM_MESON_TAC [FINITE_SUBSET, FINITE_HJ_CUBE], ALL_TAC] THEN
      ASM_SIMP_TAC [SUM_CONST, FINITE_IMAGE, REAL_MUL_RID] THEN
      SUBGOAL_THEN (← q r"CARD (IMAGE (tile:(num->num)->(num->num)) S0) = CARD S0")
      SUBST1_TAC THENL
       [MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC [] THEN
        ASM_MESON_TAC [SUBSET],
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"&(CARD(S0:(num->num)->bool)) =
        hj_density (k + 1) (p + r) S0 * &((k + 1) EXP (p + r))")
      SUBST1_TAC THENL
       [REWRITE_TAC [HJ_DENSITY_CARD] THEN
        SUBGOAL_THEN (← q r"{x | x IN hj_cube (k + 1) (p + r) /\ x IN S0} = S0")
        SUBST1_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
        MATCH_MP_TAC f12 THEN
        REWRITE_TAC [REAL_OF_NUM_EQ, EXP_EQ_0] THEN ARITH_TAC,
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"p + M1 + r = (p + r) + M1:num") SUBST1_TAC THENL
       [ARITH_TAC, ALL_TAC] THEN
      SUBST1_TAC (← SPECL [← q r"k + 1", ← q r"p + r:num", ← q r"M1:num"] EXP_ADD) THEN
      REWRITE_TAC [← GSYM REAL_OF_NUM_MUL] THEN
      SUBGOAL_THEN (← q r"&0 < &((k + 1) EXP (p + r)) /\ &0 < &((k + 1) EXP M1)")
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC [REAL_OF_NUM_LT, LT_NZ, EXP_EQ_0] THEN
         ARITH_TAC, ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"hj_density (k + 1) (p + r) S0 *
                  &((k + 1) EXP m) / &((k + 1) EXP M1)") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC [REAL_POS],
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        UNDISCH_TAC (← q r"&0 < &((k + 1) EXP M1)") THEN
        UNDISCH_TAC (← q r"&0 < &((k + 1) EXP (p + r))") THEN CONV_TAC REAL_FIELD],
      ALL_TAC] THEN
    X_GEN_TAC (← q r"y:num->num") THEN DISCH_TAC THEN
    SUBGOAL_THEN
     (← q r"!u. u IN hj_tiling_union (k + 1) m
            (IMAGE (tile:(num->num)->(num->num)) S0) <=>
          ?w z. w IN hj_cube (k + 1) (p + r) /\
                (!z'. z' IN IMAGE (hj_subst (k + 1) V0) (hj_cube (k + 1) m)
                      ==> hj_insert p M1 w z' IN E) /\
                z IN IMAGE (hj_subst (k + 1) V0) (hj_cube (k + 1) m) /\
                u = hj_insert p M1 w z")
    (fun th => REWRITE_TAC [th]) THENL
     [X_GEN_TAC (← q r"u:num->num") THEN
      REWRITE_TAC [hj_tiling_union, IN_ELIM_THM, FORALL_IN_IMAGE, IN_IMAGE] THEN
      SUBGOAL_THEN
       (← q r"!w. w IN S0 <=>
            w IN hj_cube (k + 1) (p + r) /\
            !a. a IN hj_cube (k + 1) m
                ==> hj_insert p M1 w (hj_subst (k + 1) V0 a) IN E")
      ASSUME_TAC THENL
       [EXPAND_TAC "S0" THEN REWRITE_TAC [IN_ELIM_THM], ALL_TAC] THEN
      ASM_MESON_TAC [],
      ALL_TAC] THEN
    MATCH_MP_TAC HJ_INSENSITIVE_LEFTOVER THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HJ_SUBST_CUBE THEN EXISTS_TAC (← q r"m:num") THEN
    ASM_REWRITE_TAC [a13]))

  -- @@RETURN BEGIN
  return { HJ_INSENSITIVE_EQ, HJ_INSENSITIVE_LEFTOVER, DKT_TILE_STEP }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- Tiling an insensitive set (DKT Lemma 12).  (szemeredi.ml 5229-5367)       -/
/- ------------------------------------------------------------------------- -/

structure Lemma12 where
  -- @@FIELDS
  HJ_DENSITY_SPLIT : thm
  HJ_TILING_UNION_UNION : thm
  HJ_TILING_APPEND : thm
  HJ_TILING_ITER : thm
  HJ_TILING_INSENSITIVE : thm
  deriving Inhabited

@[nospecialize]
def setupLemma12 [HolBase] (D : SzemerediDeps) (BFiniteMeans : FiniteMeans) (BWords : Words) (BDensities : Densities) (BUniformSubspaces : UniformSubspaces) (BTilings : Tilings) (BTileStep : TileStep) :
    ExceptT String IO Lemma12 := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_REAL_ARITH_TAC, INDUCT_TAC, MESON_TAC, REAL_ARITH_TAC, SET_RULE,
        SET_TAC, .. } := D
  let { ADD_ASSOC, ADD_CLAUSES, EXTENSION, FINITE_UNION, IN_ELIM_THM, IN_UNION,
        LEFT_IMP_EXISTS_THM, MONO_EXISTS, MULT_CLAUSES, NOT_IN_EMPTY, .. } := D.core1
  let { REAL_ADD_RID, REAL_ARCH, REAL_MUL_LZERO, REAL_OF_NUM_SUC, .. } := D.core2
  let { FMEAN_ADD, FMEAN_EQ, .. } := BFiniteMeans
  let { FINITE_HJ_CUBE, .. } := BWords
  let { HJ_DENSITY_LE_1, hj_density, .. } := BDensities
  let { HJ_CONCAT_0, .. } := BUniformSubspaces
  let { HJ_TILING_EMPTY, HJ_TILING_UNION_EMPTY, HJ_TILING_UNION_SUBSET, hj_tiling,
        hj_tiling_union, .. } := BTilings
  let { DKT_TILE_STEP, .. } := BTileStep
  -- @@SCOPE END

  let HJ_DENSITY_SPLIT ← prove
   r"!q n A B. hj_density q n A =
             hj_density q n {x | x IN A /\ x IN B} +
             hj_density q n {x | x IN A /\ ~(x IN B)}"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [hj_density, IN_ELIM_THM] THEN
    SIMP_TAC [← GSYM FMEAN_ADD, FINITE_HJ_CUBE] THEN
    MATCH_MP_TAC FMEAN_EQ THEN X_GEN_TAC (← q r"x:num->num") THEN DISCH_TAC THEN
    ASM_CASES_TAC (← q r"(x:num->num) IN A") THEN
    ASM_CASES_TAC (← q r"(x:num->num) IN B") THEN ASM_REWRITE_TAC [] THEN
    REAL_ARITH_TAC))

  let HJ_TILING_UNION_UNION ← prove
   r"!q m Fs1 Fs2. hj_tiling_union q m (Fs1 UNION Fs2) =
                 hj_tiling_union q m Fs1 UNION hj_tiling_union q m Fs2"
   (← do
    pure (REWRITE_TAC [hj_tiling_union, EXTENSION, IN_UNION, IN_ELIM_THM] THEN
    MESON_TAC []))

  let HJ_TILING_APPEND ← prove
   r"!q m n Fs1 Fs2 E.
        hj_tiling q m n Fs1 E /\
        hj_tiling q m n Fs2 {x | x IN E /\ ~(x IN hj_tiling_union q m Fs1)}
        ==> hj_tiling q m n (Fs1 UNION Fs2) E"
   (← do
    pure (REWRITE_TAC [hj_tiling, FINITE_UNION, IN_UNION, IN_ELIM_THM,
                hj_tiling_union] THEN
    MESON_TAC []))

  let HJ_TILING_ITER ← prove
   r"!k m beta i.
        1 <= k /\ density_hales_jewett k /\ 1 <= m /\ &0 < beta /\ i < k
        ==> ?M1 Theta.
              &0 < Theta /\
              !s p r E.
                (!y. y IN hj_cube (k + 1) p
                     ==> hj_insensitive (k + 1) (s * M1 + r) i k
                               {x | hj_concat p y x IN E}) /\
                hj_density (k + 1) (p + (s * M1 + r)) E < &2 *
                beta + &s * Theta
                ==> ?Fs. hj_tiling (k + 1) m (p + (s * M1 + r)) Fs E /\
                         hj_density (k + 1) (p + (s * M1 + r))
                              {x | x IN E /\
                               ~(x IN hj_tiling_union (k + 1) m Fs)}
                         < &2 * beta"
   (← do
    let s1 ← SET_RULE (← q r"!s:(num->num)->bool. {x | x IN s} = s")
    pure (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP DKT_TILE_STEP) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"M1:num") THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"Theta:real") THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "step")) THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN
     (← q r"!n E. hj_density (k + 1) n E < &2 * beta
            ==> ?Fs. hj_tiling (k + 1) m n Fs E /\
                     hj_density (k + 1) n
                       {x | x IN E /\ ~(x IN hj_tiling_union (k + 1) m Fs)}
                     < &2 * beta")
    (LABEL_TAC "small") THENL
     [REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"{}:(num->num)->bool") THEN
      ASM_REWRITE_TAC [HJ_TILING_EMPTY, HJ_TILING_UNION_EMPTY, NOT_IN_EMPTY, s1],
      ALL_TAC] THEN
    INDUCT_TAC THENL
     [REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES, REAL_MUL_LZERO, REAL_ADD_RID] THEN
      REPEAT STRIP_TAC THEN REMOVE_THEN "small" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [← q r"p:num", ← q r"r:num", ← q r"E:(num->num)->bool"] THEN
    SUBGOAL_THEN (← q r"SUC s * M1 + r = M1 + (s * M1 + r)") SUBST1_TAC THENL
     [REWRITE_TAC [MULT_CLAUSES] THEN ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [← GSYM REAL_OF_NUM_SUC] THEN STRIP_TAC THEN
    ASM_CASES_TAC
     (← q r"hj_density (k + 1) (p + (M1 + (s * M1 + r))) E < &2 * beta") THENL
     [REMOVE_THEN "small" MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    REMOVE_THEN "step" (MP_TAC o SPECL
     [← q r"p:num", ← q r"s * M1 + r:num", ← q r"E:(num->num)->bool"]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"Fs1:(num->num)->bool") STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o SPECL
     [← q r"p + M1:num", ← q r"r:num",
      ← q r"{x | x IN E /\ ~(x IN hj_tiling_union (k + 1) m Fs1)}"]) THEN
    REWRITE_TAC [IN_ELIM_THM, ← GSYM ADD_ASSOC] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN
      MP_TAC (← ISPECL [← q r"k + 1", ← q r"p + (M1 + (s * M1 + r)):num",
        ← q r"E:(num->num)->bool",
                        ← q r"hj_tiling_union (k + 1) m Fs1"] HJ_DENSITY_SPLIT) THEN
      SUBGOAL_THEN (← q r"{x | x IN E /\ x IN hj_tiling_union (k + 1) m Fs1} =
                    hj_tiling_union (k + 1) m Fs1")
      SUBST1_TAC THENL
       [MP_TAC (← ISPECL [← q r"k + 1", ← q r"m:num", ← q r"p + (M1 + (s * M1 + r)):num",
                          ← q r"Fs1:(num->num)->bool", ← q r"E:(num->num)->bool"]
          HJ_TILING_UNION_SUBSET) THEN
        ASM_REWRITE_TAC [] THEN SET_TAC [],
        ALL_TAC] THEN
      ABBREV_TAC (← q r"dleft = hj_density (k + 1) (p + (M1 + (s * M1 + r)))
                            {x | x IN E /\
                             ~(x IN hj_tiling_union (k + 1) m Fs1)}") THEN
      ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"Fs2:(num->num)->bool") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"Fs1 UNION Fs2:(num->num)->bool") THEN CONJ_TAC THENL
     [MATCH_MP_TAC HJ_TILING_APPEND THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"{x | x IN E /\ ~(x IN hj_tiling_union (k + 1) m (Fs1 UNION Fs2))} =
      {x | (x IN E /\ ~(x IN hj_tiling_union (k + 1) m Fs1)) /\
           ~(x IN hj_tiling_union (k + 1) m Fs2)}")
    SUBST1_TAC THENL
     [REWRITE_TAC [HJ_TILING_UNION_UNION] THEN SET_TAC [], ASM_REWRITE_TAC []]))

  let HJ_TILING_INSENSITIVE ← prove
   r"!k m beta i.
        1 <= k /\ density_hales_jewett k /\ 1 <= m /\ &0 < beta /\ i < k
        ==> ?N. !n D. N <= n /\ hj_insensitive (k + 1) n i k D
                      ==> ?Fs. hj_tiling (k + 1) m n Fs D /\
                               hj_density (k + 1) n
                                 {x | x IN D /\
                                  ~(x IN hj_tiling_union (k + 1) m Fs)}
                               < &2 * beta"
   (← do
    let s1 ← SET_RULE (← q r"!s:(num->num)->bool. {x | x IN s} = s")
    pure (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP HJ_TILING_ITER) THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"M1:num", ← q r"Theta:real"] THEN STRIP_TAC THEN
    MP_TAC (← SPEC (← q r"Theta:real") REAL_ARCH) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"s:num") o SPEC (← q r"&1")) THEN
    EXISTS_TAC (← q r"s * M1:num") THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL
     [← q r"s:num", ← q r"0", ← q r"n - s * M1:num", ← q r"D:(num->num)->bool"]) THEN
    SUBGOAL_THEN (← q r"0 + (s * M1 + (n - s * M1)) = n") SUBST1_TAC THENL
     [UNDISCH_TAC (← q r"s * M1 <= n:num") THEN ARITH_TAC, ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC [HJ_CONCAT_0, s1] THEN
    SUBGOAL_THEN (← q r"s * M1 + (n - s * M1) = n:num") SUBST1_TAC THENL
     [UNDISCH_TAC (← q r"s * M1 <= n:num") THEN ARITH_TAC, ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    MP_TAC (← SPECL [← q r"k + 1", ← q r"n:num", ← q r"D:(num->num)->bool"] HJ_DENSITY_LE_1) THEN
    ASM_REAL_ARITH_TAC))

  -- @@RETURN BEGIN
  return { HJ_DENSITY_SPLIT, HJ_TILING_UNION_UNION, HJ_TILING_APPEND, HJ_TILING_ITER,
           HJ_TILING_INSENSITIVE }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- Tiling an intersection of insensitive sets (DKT Corollary 13).            -/
/- (szemeredi.ml 5368-5621)                                                  -/
/- ------------------------------------------------------------------------- -/

structure Cor13 where
  -- @@FIELDS
  HJ_DENSITY_SUBADD : thm
  HJ_TILING_COMPOSE : thm
  HJ_TILING_COMPOSE_DENS : thm
  HJ_TILING_STRUCTURED : thm
  deriving Inhabited

@[nospecialize]
def setupCor13 [HolBase] (D : SzemerediDeps) (BWords : Words) (BDensities : Densities) (BCor11 : Cor11) (BTilings : Tilings) (BBlockInsert : BlockInsert) (BLemma12 : Lemma12) :
    ExceptT String IO Cor13 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, INDUCT_TAC,
        MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, SET_RULE, .. } := D
  let { EQ_TRANS, FINITE_SUBSET, FORALL_UNWIND_THM2, IN_ELIM_THM, LEFT_IMP_EXISTS_THM,
        LT, MONO_EXISTS, .. } := D.core1
  let { REAL_LE_ADD2, REAL_LE_DIV, REAL_LE_LADD, REAL_LE_LMUL, REAL_LE_RMUL,
        REAL_LE_TRANS, REAL_LT_IMP_LE, REAL_MUL_RID, REAL_OF_NUM_SUC, REAL_POS,
        RIGHT_IMP_EXISTS_THM, SKOLEM_THM, SUBSET, SUM_BOUND, SUM_CONST, .. } := D.core2
  let { HJ_SUBSPACE_SUBST, HJ_SUBST_CUBE, HJ_SUBST_SUBST, .. } := BWords
  let { HJ_DENSITY_EQ, HJ_DENSITY_LE_1, HJ_DENSITY_MONO, .. } := BDensities
  let { HJ_DENSITY_CUBE, .. } := BCor11
  let { HJ_DENSITY_TILING_UNION_RESTRICT, HJ_TILING_INJ, hj_tiling, hj_tiling_union, .. } := BTilings
  let { FINITE_HJ_SUBSPACES, HJ_INSENSITIVE_PULLBACK, .. } := BBlockInsert
  let { HJ_DENSITY_SPLIT, HJ_TILING_INSENSITIVE, .. } := BLemma12
  -- @@SCOPE END

  let HJ_DENSITY_SUBADD ← prove
   r"!q n A B C.
        (!x. x IN hj_cube q n /\ x IN A ==> x IN B \/ x IN C)
        ==> hj_density q n A <= hj_density q n B + hj_density q n C"
   (← do
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"q:num", ← q r"n:num", ← q r"A:(num->num)->bool",
                     ← q r"B:(num->num)->bool"] HJ_DENSITY_SPLIT) THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
    CONJ_TAC THEN MATCH_MP_TAC HJ_DENSITY_MONO THEN REWRITE_TAC [IN_ELIM_THM] THEN
    ASM_MESON_TAC []))

  let HJ_TILING_COMPOSE ← prove
   r"!q m M n V1 B E P.
        1 <= q /\ hj_tiling q M n V1 E /\
        (!V. V IN V1 ==> hj_tiling q m M (B V) {a | hj_subst q V a IN P})
        ==> hj_tiling q m n {hj_subst q V W | V,W | V IN V1 /\ W IN B V}
                   {x | x IN E /\ x IN P}"
   (← do
    pure (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"!V W. V IN V1 /\ W IN B V
            ==> hj_subspace q M n V /\ hj_subspace q m M W /\
                hj_subspace q m n (hj_subst q V W) /\
                !a. a IN hj_cube q m
                    ==> hj_subst q W a IN hj_cube q M /\
                        hj_subst q V (hj_subst q W a) IN E /\
                        hj_subst q V (hj_subst q W a) IN P")
    ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"V:num->num")) THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [hj_tiling, IN_ELIM_THM] THEN STRIP_TAC THEN
      UNDISCH_TAC (← q r"hj_tiling q M n V1 E") THEN REWRITE_TAC [hj_tiling] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN (← q r"hj_subspace q M n V /\ hj_subspace q m M (W:num->num)")
      STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [MATCH_MP_TAC HJ_SUBSPACE_SUBST THEN EXISTS_TAC (← q r"M:num") THEN
        ASM_REWRITE_TAC [],
        X_GEN_TAC (← q r"a:num->num") THEN DISCH_TAC THEN
        SUBGOAL_THEN (← q r"hj_subst q W a IN hj_cube q M") ASSUME_TAC THENL
         [MATCH_MP_TAC HJ_SUBST_CUBE THEN EXISTS_TAC (← q r"m:num") THEN
          ASM_REWRITE_TAC [],
          ASM_SIMP_TAC []]],
      ALL_TAC] THEN
    REWRITE_TAC [hj_tiling, IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{z | hj_subspace q m n z}") THEN
      REWRITE_TAC [FINITE_HJ_SUBSPACES, SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC [],
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"z:num->num", ← q r"V:num->num", ← q r"W:num->num"] THEN
      STRIP_TAC THEN ASM_SIMP_TAC [HJ_SUBST_SUBST],
      SUBGOAL_THEN
       (← q r"!V W V' W' a a'. V IN V1 /\ W IN B V /\ V' IN V1 /\ W' IN B V' /\
                         a IN hj_cube q m /\ a' IN hj_cube q m /\
                         hj_subst q V (hj_subst q W a) =
                         hj_subst q V' (hj_subst q W' a')
                         ==> V = V' /\ W = W'")
      ASSUME_TAC THENL
       [REPEAT GEN_TAC THEN STRIP_TAC THEN
        SUBGOAL_THEN
          (← q r"hj_subst q W a IN hj_cube q M /\ hj_subst q W' a' IN hj_cube q M")
        STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
        MP_TAC (← ISPECL [← q r"q:num", ← q r"M:num", ← q r"n:num",
                          ← q r"V1:(num->num)->bool",
                          ← q r"E:(num->num)->bool", ← q r"V:num->num", ← q r"V':num->num",
                          ← q r"hj_subst q W a", ← q r"hj_subst q W' a'"] HJ_TILING_INJ) THEN
        ASM_REWRITE_TAC [] THEN
        DISCH_THEN (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
        REWRITE_TAC [] THEN
        MP_TAC (← ISPECL [← q r"q:num", ← q r"m:num", ← q r"M:num",
                          ← q r"(B:(num->num)->(num->num)->bool) V'",
                          ← q r"{a | hj_subst q V' a IN P}", ← q r"W:num->num",
                          ← q r"W':num->num",
                          ← q r"a:num->num", ← q r"a':num->num"] HJ_TILING_INJ) THEN
        ASM_SIMP_TAC [],
        ALL_TAC] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC (← q r"hj_subst q z a = hj_subst q z' a'") THEN
      ASM_REWRITE_TAC [HJ_SUBST_SUBST] THEN ASM_MESON_TAC []]))

  let HJ_TILING_COMPOSE_DENS ← prove
   r"!q m M n V1 B E P c.
        1 <= q /\ hj_tiling q M n V1 E /\ &0 <= c /\
        (!V. V IN V1
             ==> hj_density q M {a | hj_subst q V a IN P /\
                               ~(a IN hj_tiling_union q m (B V))} <= c)
        ==> hj_density q n {x | (x IN E /\ x IN P) /\
                          ~(x IN hj_tiling_union q m
                                 {hj_subst q V W | V,W | V IN V1 /\ W IN B V})}
            <= hj_density q n
              {x | x IN E /\ ~(x IN hj_tiling_union q M V1)} + c"
   (← do
    pure (REPEAT STRIP_TAC THEN
    ABBREV_TAC (← q r"Fc = {hj_subst q V W | V,W | V IN V1 /\ W IN B V}") THEN
    ABBREV_TAC
      (← q r"L = {x | (x IN E /\ x IN P) /\ ~(x IN hj_tiling_union q m Fc)}") THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"hj_density q n {x | x IN E /\ ~(x IN hj_tiling_union q M V1)} +
                hj_density q n {x | x IN hj_tiling_union q M V1 /\ x IN L}") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HJ_DENSITY_SUBADD THEN EXPAND_TAC "L" THEN
      REWRITE_TAC [IN_ELIM_THM] THEN MESON_TAC [],
      REWRITE_TAC [REAL_LE_LADD]] THEN
    MP_TAC (← ISPECL [← q r"q:num", ← q r"M:num", ← q r"n:num", ← q r"V1:(num->num)->bool",
                      ← q r"E:(num->num)->bool", ← q r"\x:num->num. x IN L"]
      HJ_DENSITY_TILING_UNION_RESTRICT) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN (← q r"FINITE(V1:(num->num)->bool)") ASSUME_TAC THENL
     [ASM_MESON_TAC [hj_tiling], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"&(CARD(V1:(num->num)->bool)) * &(q EXP M) / &(q EXP n) <= &1")
    ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q r"q:num", ← q r"M:num", ← q r"n:num",
                        ← q r"V1:(num->num)->bool",
                        ← q r"E:(num->num)->bool", ← q r"\x:num->num. T"]
        HJ_DENSITY_TILING_UNION_RESTRICT) THEN
      ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"hj_density q M {a:num->num | T} = &1") SUBST1_TAC THENL
       [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (← q r"hj_density q M (hj_cube q M)") THEN
        CONJ_TAC THENL [MATCH_MP_TAC HJ_DENSITY_EQ THEN SIMP_TAC [IN_ELIM_THM],
                        ASM_SIMP_TAC [HJ_DENSITY_CUBE]],
        ALL_TAC] THEN
      ASM_SIMP_TAC [SUM_CONST, REAL_MUL_RID] THEN
        DISCH_THEN (fun th => tactic_of do pure (SUBST1_TAC (← SYM th))) THEN
      REWRITE_TAC [HJ_DENSITY_LE_1],
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"(&(CARD(V1:(num->num)->bool)) * c) *
                &(q EXP M) / &(q EXP n)") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN
      SIMP_TAC [REAL_LE_DIV, REAL_POS] THEN
      MATCH_MP_TAC SUM_BOUND THEN ASM_REWRITE_TAC [] THEN
      X_GEN_TAC (← q r"V:num->num") THEN DISCH_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"hj_density q M {a | hj_subst q V a IN P /\
        ~(a IN hj_tiling_union q m (B V))}") THEN
      CONJ_TAC THENL [ALL_TAC, ASM_SIMP_TAC []] THEN
      MATCH_MP_TAC HJ_DENSITY_MONO THEN X_GEN_TAC (← q r"a:num->num") THEN
      EXPAND_TAC "L" THEN EXPAND_TAC "Fc" THEN
      REWRITE_TAC [hj_tiling_union, IN_ELIM_THM] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o check (fun th => is_neg (concl th))) THEN
      REWRITE_TAC [] THEN
      MAP_EVERY EXISTS_TAC [← q r"hj_subst q V z", ← q r"a':num->num"] THEN
      ASM_REWRITE_TAC [HJ_SUBST_SUBST] THEN
      MAP_EVERY EXISTS_TAC [← q r"V:num->num", ← q r"z:num->num"] THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"(&(CARD(V1:(num->num)->bool)) * c) * &(q EXP M) / &(q EXP n) =
      c * (&(CARD V1) * &(q EXP M) / &(q EXP n))")
    SUBST1_TAC THENL [REAL_ARITH_TAC, ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC []))

  let HJ_TILING_STRUCTURED ← prove
   r"!k beta r m.
        1 <= k /\ density_hales_jewett k /\ &0 < beta /\ 1 <= r /\
        r <= k /\ 1 <= m
        ==> ?N. !n D.
                  N <= n /\ (!j. j < r ==> hj_insensitive (k + 1) n j k (D j))
                  ==> ?Fs. hj_tiling (k + 1) m n Fs {x | !j. j < r
                    ==> x IN D j} /\
                           hj_density (k + 1) n
                             {x | (!j. j < r ==> x IN D j) /\
                                  ~(x IN hj_tiling_union (k + 1) m Fs)}
                           <= &2 * &r * beta"
   (← do
    -- right to left: the nine rules from the last to the first
    let r9 ← REAL_ARITH
      (← q r"!a. a <= &2 * &r * beta ==> a + &2 * beta <= &2 * (&r + &1) * beta")
    let a8 ← ARITH_RULE (← q r"1 <= k + 1")
    let a7 ← ARITH_RULE (← q r"1 <= k + 1")
    let a6 ← ARITH_RULE (← q r"N1 <= N1 + 1")
    let r5 ← REAL_ARITH (← q r"!a. a < &2 * beta ==> a <= &2 * &1 * beta")
    let s4 ← SET_RULE (← q r"!s:(num->num)->bool. {x | x IN s} = s")
    let a3 ← ARITH_RULE (← q r"SUC 0 = 1")
    let a2 ← ARITH_RULE (← q r"j < 1 <=> j = 0")
    let a1 ← ARITH_RULE (← q r"j < SUC 0 <=> j = 0")
    pure (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
     [ARITH_TAC, POP_ASSUM (LABEL_TAC "ih")] THEN
    X_GEN_TAC (← q r"m:num") THEN STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"k:num", ← q r"m:num", ← q r"beta:real", ← q r"r:num"]
             HJ_TILING_INSENSITIVE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"SUC r <= k") THEN ARITH_TAC,
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"N1:num")) THEN
    ASM_CASES_TAC (← q r"r = 0") THENL
     [EXISTS_TAC (← q r"N1:num") THEN
      MAP_EVERY X_GEN_TAC [← q r"n:num", ← q r"D:num->(num->num)->bool"] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [← q r"n:num", ← q r"(D:num->(num->num)->bool) r"]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC [] THEN ARITH_TAC,
        ALL_TAC] THEN
      ASM_REWRITE_TAC [a1, FORALL_UNWIND_THM2, a2, a3, s4] THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC [] THEN
      DISCH_TAC THEN
      MATCH_MP_TAC r5 THEN
      FIRST_ASSUM ACCEPT_TAC,
      ALL_TAC] THEN
    REMOVE_THEN "ih" (MP_TAC o SPEC (← q r"N1 + 1")) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN
      MAP_EVERY UNDISCH_TAC [← q r"SUC r <= k", ← q r"~(r = 0)"] THEN ARITH_TAC,
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"N2:num") THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [← q r"n:num", ← q r"D:num->(num->num)->bool"] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"n:num", ← q r"D:num->(num->num)->bool"]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC (← q r"j < r:num") THEN ARITH_TAC,
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"V1:(num->num)->bool") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     (← q r"!V. V IN V1
          ==> ?Fs. hj_tiling (k + 1) m (N1 + 1) Fs
                     {a | hj_subst (k + 1) V a IN (D:num->(num->num)->bool) r} /\
                   hj_density (k + 1) (N1 + 1)
                     {a | hj_subst (k + 1) V a IN D r /\
                          ~(a IN hj_tiling_union (k + 1) m Fs)} < &2 * beta")
    MP_TAC THENL
     [X_GEN_TAC (← q r"V:num->num") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL
       [← q r"N1 + 1",
        ← q r"{a | hj_subst (k + 1) V a IN (D:num->(num->num)->bool) r}"]) THEN
      ANTS_TAC THENL
       [REWRITE_TAC [a6] THEN
        MATCH_MP_TAC HJ_INSENSITIVE_PULLBACK THEN EXISTS_TAC (← q r"n:num") THEN
        ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC,
          ASM_MESON_TAC [hj_tiling]],
        REWRITE_TAC [IN_ELIM_THM]],
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"B:(num->num)->(num->num)->bool") o
               REWRITE_RULE [RIGHT_IMP_EXISTS_THM, SKOLEM_THM]) THEN
    EXISTS_TAC
     (← q r"{hj_subst (k + 1) V W | V,W | V IN V1 /\ W IN B V}") THEN
    SUBGOAL_THEN
     (← q r"!x. (!j. j < SUC r ==> x IN (D:num->(num->num)->bool) j) <=>
          x IN {x | !j. j < r ==> x IN D j} /\ x IN D r")
    (fun th => REWRITE_TAC [th]) THENL
     [REWRITE_TAC [IN_ELIM_THM, LT] THEN MESON_TAC [], ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HJ_TILING_COMPOSE THEN EXISTS_TAC (← q r"N1 + 1") THEN
      ASM_SIMP_TAC [a7],
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     (← q r"hj_density (k + 1) n {x | x IN {x | !j. j < r:num ==> x IN D j} /\
                          ~(x IN hj_tiling_union (k + 1) (N1 + 1) V1)} +
                          &2 * beta") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HJ_TILING_COMPOSE_DENS THEN
      ASM_SIMP_TAC [a8, REAL_LT_IMP_LE] THEN
      ASM_REAL_ARITH_TAC,
      REWRITE_TAC [IN_ELIM_THM, ← GSYM REAL_OF_NUM_SUC] THEN
      MATCH_MP_TAC r9 THEN
      FIRST_ASSUM ACCEPT_TAC]))

  -- @@RETURN BEGIN
  return { HJ_DENSITY_SUBADD, HJ_TILING_COMPOSE, HJ_TILING_COMPOSE_DENS,
           HJ_TILING_STRUCTURED }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- The density increment (DKT Proposition 6) and the density Hales-Jewett    -/
/- theorem.  (szemeredi.ml 5622-5880)                                        -/
/- ------------------------------------------------------------------------- -/

structure DensityHJThm where
  -- @@FIELDS
  DKT_PROP6 : thm
  DENSITY_HALES_JEWETT_STEP : thm
  DENSITY_HALES_JEWETT_1 : thm
  DENSITY_HALES_JEWETT : thm
  deriving Inhabited

@[nospecialize]
def setupDensityHJThm [HolBase] (D : SzemerediDeps) (BWords : Words) (BLines : Lines) (BDensities : Densities) (BDensityHJ : DensityHJ) (BCor11 : Cor11) (BTilings : Tilings) (BCor13 : Cor13) :
    ExceptT String IO DensityHJThm := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC,
        INDUCT_TAC, MESON_TAC, NUM_REDUCE_CONV, REAL_ARITH, REAL_ARITH_TAC, REAL_FIELD, .. } := D
  let { ADD1, ADD_CLAUSES, COND_ID, EMPTY_GSPEC, FORALL_UNWIND_THM2, FUN_EQ_THM,
        IN_ELIM_THM, LE_REFL, MONO_EXISTS, NOT_IN_EMPTY, .. } := D.core1
  let { NOT_LE, REAL_ADD_RID, REAL_ARCH, REAL_LE_LMUL, REAL_LE_MUL, REAL_LE_REFL,
        REAL_LT_DIV, REAL_LT_MUL, REAL_MUL_LZERO, REAL_OF_NUM_LE, REAL_OF_NUM_SUC,
        REAL_POW_2, REAL_POW_LT, RIGHT_IMP_EXISTS_THM, SKOLEM_THM, SUBSET,
        num_RECURSION, .. } := D.core2
  let { HJ_SUBSPACE_SUBST, HJ_SUBST_SUBST, IN_HJ_CUBE, hj_subspace, hj_subst, .. } := BWords
  let { HJ_HAS_LINE_PULLBACK, hj_has_line, hj_line, hj_line_point, .. } := BLines
  let { HJ_DENSITY_LE_1, HJ_DENSITY_MONO, .. } := BDensities
  let { HJ_DENSITY_POS_EXISTS, density_hales_jewett, .. } := BDensityHJ
  let { DKT_COR11, .. } := BCor11
  let { HJ_TILING_AVERAGE, HJ_TILING_UNION_EMPTY, HJ_TILING_UNION_SUBSET, hj_tiling, .. } := BTilings
  let { HJ_DENSITY_SUBADD, HJ_TILING_STRUCTURED, .. } := BCor13
  -- @@SCOPE END

  let DKT_PROP6 ← prove
   r"!k delta.
        1 <= k /\ density_hales_jewett k /\ &0 < delta /\ delta <= &1
        ==> ?gam. &0 < gam /\
                  !d. 1 <= d
                      ==> ?N. !n A rho.
                                N <= n /\ delta <= rho /\
                                rho <= hj_density (k + 1) n A /\
                                ~hj_has_line (k + 1) n A
                                ==> ?z. hj_subspace (k + 1) d n z /\
                                        rho + gam <=
                                        hj_density (k + 1) d
                                          {a | hj_subst (k + 1) z a IN A}"
   (← do
    -- right to left: the four rules from the last to the first
    let a4 ← ARITH_RULE (← q r"1 <= k + 1")
    let a3 ← ARITH_RULE (← q r"1 <= k + 1")
    let a2 ← ARITH_RULE (← q r"M0 <= MAX M0 N13")
    let r1 ← REAL_ARITH (← q r"!x. &0 < x / &2 <=> &0 < x")
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"k:num", ← q r"delta:real"] DKT_COR11) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"gamma0:real") (X_CHOOSE_THEN (← q r"M0:num")
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cor11")))) THEN
    EXISTS_TAC (← q r"gamma0 / &2") THEN
    ASM_REWRITE_TAC [r1] THEN
    X_GEN_TAC (← q r"d:num") THEN DISCH_TAC THEN
    MP_TAC (← SPECL [← q r"k:num", ← q r"gamma0 pow 2 / (&4 * &k)", ← q r"k:num", ← q r"d:num"]
      HJ_TILING_STRUCTURED) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [LE_REFL] THEN MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_SIMP_TAC [REAL_POW_LT] THEN
      UNDISCH_TAC (← q r"1 <= k") THEN REWRITE_TAC [← GSYM REAL_OF_NUM_LE] THEN
      REAL_ARITH_TAC,
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"N13:num")) THEN
    REMOVE_THEN "cor11" (MP_TAC o SPEC (← q r"MAX M0 N13")) THEN
    REWRITE_TAC [a2] THEN
    ABBREV_TAC (← q r"m = MAX M0 N13") THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"N:num") THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [← q r"n:num", ← q r"A:(num->num)->bool", ← q r"rho:real"] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"n:num", ← q r"A:(num->num)->bool",
      ← q r"rho:real"]) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"W:num->num")
     (X_CHOOSE_THEN (← q r"D:num->(num->num)->bool") STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"m:num", ← q r"D:num->(num->num)->bool"]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN EXPAND_TAC "m" THEN ARITH_TAC, ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"Fs:(num->num)->bool") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     (← q r"hj_density (k + 1) m (hj_tiling_union (k + 1) d Fs) <=
      hj_density (k + 1) m
        {x | x IN hj_cube (k + 1) m /\ !i. i < k ==> x IN D i}")
    ASSUME_TAC THENL
     [MATCH_MP_TAC HJ_DENSITY_MONO THEN
      MP_TAC (← ISPECL [← q r"k + 1", ← q r"d:num", ← q r"m:num",
                        ← q r"Fs:(num->num)->bool",
                        ← q r"{x:num->num | !j. j < k ==>
                          x IN (D:num->(num->num)->bool) j}"]
                         HJ_TILING_UNION_SUBSET) THEN
      ASM_REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"hj_density (k + 1) m
        {x | hj_subst (k + 1) W x IN A /\ !i. i < k ==> x IN D i} <=
      hj_density (k + 1) m {x | x IN hj_tiling_union (k + 1) d Fs /\
                          x IN {x | hj_subst (k + 1) W x IN A}} +
      hj_density (k + 1) m {x | (!j. j < k ==> x IN D j) /\
                          ~(x IN hj_tiling_union (k + 1) d Fs)}")
    ASSUME_TAC THENL
     [MATCH_MP_TAC HJ_DENSITY_SUBADD THEN REWRITE_TAC [IN_ELIM_THM] THEN
      MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"&2 * &k * gamma0 pow 2 / (&4 * &k) = gamma0 pow 2 / &2")
    ASSUME_TAC THENL
     [UNDISCH_TAC (← q r"1 <= k") THEN REWRITE_TAC [← GSYM REAL_OF_NUM_LE] THEN
      CONV_TAC REAL_FIELD,
      ALL_TAC] THEN
    ABBREV_TAC
     (← q r"dD = hj_density (k + 1) m {x | x IN hj_cube (k + 1) m /\ !i. i < k ==>
       x IN D i}") THEN
    ABBREV_TAC
     (← q r"dAD = hj_density (k + 1) m {x | hj_subst (k + 1) W x IN A /\
                                !i. i < k ==> x IN D i}") THEN
    ABBREV_TAC
     (← q r"dL = hj_density (k + 1) m {x | (!j. j < k ==> x IN D j) /\
                               ~(x IN hj_tiling_union (k + 1) d Fs)}") THEN
    ABBREV_TAC (← q r"dT = hj_density (k + 1) m (hj_tiling_union (k + 1) d Fs)") THEN
    ABBREV_TAC
     (← q r"dTA = hj_density (k + 1) m {x | x IN hj_tiling_union (k + 1) d Fs /\
                                x IN {x | hj_subst (k + 1) W x IN A}}") THEN
    SUBGOAL_THEN (← q r"&0 <= rho") ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"(rho + gamma0 / &2) * dT <= (rho + gamma0 / &2) * dD /\
      (rho + gamma0) * gamma0 <= (rho + gamma0) * dD /\
      gamma0 * gamma0 <= gamma0 * dD /\ &0 < gamma0 * gamma0 /\ &0 <= rho * gamma0")
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC,
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC,
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC,
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC [],
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(rho + gamma0 / &2) * dT <= dTA /\ &0 < dTA")
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC (← q r"&2 * &k * gamma0 pow 2 / (&4 * &k) = gamma0 pow 2 / &2") THEN
      REWRITE_TAC [REAL_POW_2] THEN DISCH_TAC THEN ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"k + 1", ← q r"d:num", ← q r"m:num", ← q r"Fs:(num->num)->bool",
                      ← q r"{x:num->num | !j. j < k ==>
                        x IN (D:num->(num->num)->bool) j}",
                      ← q r"{x | hj_subst (k + 1) W x IN A}", ← q r"rho + gamma0 / &2"]
      HJ_TILING_AVERAGE) THEN
    ASM_REWRITE_TAC [a3] THEN ANTS_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC (← q r"&0 < dTA") THEN EXPAND_TAC "dTA" THEN
      REWRITE_TAC [HJ_TILING_UNION_EMPTY, NOT_IN_EMPTY, EMPTY_GSPEC] THEN
      MP_TAC (← SPECL [← q r"k + 1", ← q r"m:num",
        ← q r"{}:(num->num)->bool"] HJ_DENSITY_POS_EXISTS) THEN
      REWRITE_TAC [NOT_IN_EMPTY] THEN MESON_TAC [],
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"z:num->num") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"hj_subst (k + 1) W z") THEN CONJ_TAC THENL
     [MATCH_MP_TAC HJ_SUBSPACE_SUBST THEN EXISTS_TAC (← q r"m:num") THEN
      ASM_REWRITE_TAC [a4] THEN ASM_MESON_TAC [hj_tiling],
      UNDISCH_TAC (← q r"rho + gamma0 / &2 <=
                   hj_density (k + 1) d {a | hj_subst (k + 1) z a IN
                                       {x | hj_subst (k + 1) W x IN A}}") THEN
      REWRITE_TAC [IN_ELIM_THM, HJ_SUBST_SUBST]]))

  let DENSITY_HALES_JEWETT_STEP ← prove
   r"!k. 1 <= k /\ density_hales_jewett k ==> density_hales_jewett (k + 1)"
   (← do
    let a1 ← ARITH_RULE (← q r"1 <= k + 1")
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [density_hales_jewett] THEN
    X_GEN_TAC (← q r"delta:real") THEN DISCH_TAC THEN
    ASM_CASES_TAC (← q r"delta <= &1") THENL
     [ALL_TAC,
      EXISTS_TAC (← q r"0") THEN REPEAT STRIP_TAC THEN
      MP_TAC (← SPECL [← q r"k + 1", ← q r"n:num", ← q r"A:(num->num)->bool"]
        HJ_DENSITY_LE_1) THEN
      ASM_REAL_ARITH_TAC] THEN
    MP_TAC (← SPECL [← q r"k:num", ← q r"delta:real"] DKT_PROP6) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"gam:real") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"Nf:num->num") (LABEL_TAC "prop6") o
               GEN_REWRITE_RULE I [SKOLEM_THM] o
               GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM]) THEN
    MP_TAC (← ISPECL [← q r"1", ← q r"\(d:num) (j:num). (Nf:num->num) d + 1"]
      num_RECURSION) THEN
    REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"f:num->num") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"!j. 1 <= (f:num->num) j") ASSUME_TAC THENL
     [INDUCT_TAC THEN ASM_REWRITE_TAC [] THEN ARITH_TAC, ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!j n A rho. (f:num->num) j <= n /\ delta <= rho /\
                  rho <= hj_density (k + 1) n A
                  ==> hj_has_line (k + 1) n A \/ rho + &j * gam <= &1")
    ASSUME_TAC THENL
     [INDUCT_TAC THENL
       [REPEAT STRIP_TAC THEN DISJ2_TAC THEN
        MP_TAC (← SPECL [← q r"k + 1", ← q r"n:num", ← q r"A:(num->num)->bool"]
                 HJ_DENSITY_LE_1) THEN
        REWRITE_TAC [REAL_MUL_LZERO, REAL_ADD_RID] THEN ASM_REAL_ARITH_TAC,
        POP_ASSUM (LABEL_TAC "ih")] THEN
      MAP_EVERY X_GEN_TAC [← q r"n:num", ← q r"A:(num->num)->bool", ← q r"rho:real"] THEN
      STRIP_TAC THEN ASM_CASES_TAC (← q r"hj_has_line (k + 1) n A") THEN
      ASM_REWRITE_TAC [] THEN
      USE_THEN "prop6" (MP_TAC o SPEC (← q r"(f:num->num) j")) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
      DISCH_THEN (MP_TAC o SPECL [← q r"n:num", ← q r"A:(num->num)->bool",
                                  ← q r"rho:real"]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"(f:num->num) (SUC j) <= n") THEN
        ASM_REWRITE_TAC [] THEN ARITH_TAC,
        ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"z:num->num") STRIP_ASSUME_TAC) THEN
      REMOVE_THEN "ih" (MP_TAC o SPECL
       [← q r"(f:num->num) j", ← q r"{a | hj_subst (k + 1) z a IN A}",
        ← q r"rho + gam:real"]) THEN
      ASM_REWRITE_TAC [LE_REFL] THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      STRIP_TAC THENL
       [MP_TAC (← ISPECL [← q r"k + 1", ← q r"(f:num->num) j", ← q r"n:num",
                          ← q r"z:num->num",
                          ← q r"A:(num->num)->bool"] HJ_HAS_LINE_PULLBACK) THEN
        ASM_REWRITE_TAC [a1],
        REWRITE_TAC [← GSYM REAL_OF_NUM_SUC] THEN ASM_REAL_ARITH_TAC],
      ALL_TAC] THEN
    MP_TAC (← SPEC (← q r"gam:real") REAL_ARCH) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"j:num") o SPEC (← q r"&1")) THEN
    EXISTS_TAC (← q r"(f:num->num) j") THEN
    MAP_EVERY X_GEN_TAC [← q r"n:num", ← q r"A:(num->num)->bool"] THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"~(delta + &j * gam <= &1)") ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPECL
     [← q r"j:num", ← q r"n:num", ← q r"A:(num->num)->bool", ← q r"delta:real"]) THEN
    ASM_REWRITE_TAC [REAL_LE_REFL]))

  let DENSITY_HALES_JEWETT_1 ← prove
   r"density_hales_jewett 1"
   (← do
    -- right to left: the three ARITH_RULEs from the last to the first
    let a3 ← ARITH_RULE (← q r"a < 1 <=> a = 0")
    let a2 ← ARITH_RULE (← q r"j < 1 <=> j = 0")
    let a1 ← ARITH_RULE (← q r"a < 1 <=> a = 0")
    pure (REWRITE_TAC [density_hales_jewett] THEN X_GEN_TAC (← q r"delta:real") THEN
    DISCH_TAC THEN
    EXISTS_TAC (← q r"1") THEN
    MAP_EVERY X_GEN_TAC [← q r"n:num", ← q r"A:(num->num)->bool"] THEN
    STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"1", ← q r"n:num", ← q r"A:(num->num)->bool"]
      HJ_DENSITY_POS_EXISTS) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"x:num->num") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"x = (\i:num. 0)") SUBST_ALL_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM] THEN UNDISCH_TAC (← q r"(x:num->num) IN hj_cube 1 n") THEN
      REWRITE_TAC [IN_HJ_CUBE] THEN
      MESON_TAC [a1, NOT_LE],
      ALL_TAC] THEN
    REWRITE_TAC [hj_has_line] THEN
    EXISTS_TAC (← q r"\i:num. if i < n then 1 else 0") THEN
    CONJ_TAC THENL
     [REWRITE_TAC [hj_line, hj_subspace, IN_HJ_CUBE, a2] THEN
      REWRITE_TAC [FORALL_UNWIND_THM2, ADD_CLAUSES] THEN REPEAT CONJ_TAC THENL
       [GEN_TAC THEN COND_CASES_TAC THEN ARITH_TAC,
        GEN_TAC THEN COND_CASES_TAC THEN ASM_ARITH_TAC,
        EXISTS_TAC (← q r"0") THEN ASM_ARITH_TAC],
      REWRITE_TAC [a3, FORALL_UNWIND_THM2] THEN
      SUBGOAL_THEN
        (← q r"hj_line_point 1 (\i:num. if i < n then 1 else 0) 0 = (\i:num. 0)")
      SUBST1_TAC THENL
       [REWRITE_TAC [hj_line_point, hj_subst, FUN_EQ_THM, COND_ID] THEN
        X_GEN_TAC (← q r"i:num") THEN ASM_CASES_TAC (← q r"i < n:num") THEN
        ASM_REWRITE_TAC [] THEN CONV_TAC NUM_REDUCE_CONV,
        ASM_REWRITE_TAC []]]))

  let DENSITY_HALES_JEWETT ← prove
   r"!k. 1 <= k ==> density_hales_jewett k"
   (← do
    -- right to left: the second ARITH_RULE, then the first
    let a2 ← ARITH_RULE (← q r"SUC 0 = 1")
    let a1 ← ARITH_RULE (← q r"~(1 <= 0)")
    pure (INDUCT_TAC THEN REWRITE_TAC [a1] THEN
    ASM_CASES_TAC (← q r"k = 0") THEN
    ASM_REWRITE_TAC [a2, DENSITY_HALES_JEWETT_1] THEN
    DISCH_TAC THEN
    REWRITE_TAC [ADD1] THEN MATCH_MP_TAC DENSITY_HALES_JEWETT_STEP THEN
    CONJ_TAC THENL [ASM_ARITH_TAC, FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_ARITH_TAC]))

  -- @@RETURN BEGIN
  return { DKT_PROP6, DENSITY_HALES_JEWETT_STEP, DENSITY_HALES_JEWETT_1,
           DENSITY_HALES_JEWETT }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- The weighted Szemeredi property; affine changes of variables in means     -/
/- over Z_N; lines of [k]^n along progressions.  (szemeredi.ml 5881-6073)    -/
/- ------------------------------------------------------------------------- -/

structure WeightedDefs where
  -- @@FIELDS
  weighted_szemeredi : thm
  MOD_AFFINE_MOD : thm
  FMEAN_DIL_MOD : thm
  FMEAN_AP_AFFINE : thm
  NSUM_HJ_LINE_POINT_GEN : thm
  HJ_LINE_WILDCARDS : thm
  NSUM_HJ_LINE_POINT : thm
  deriving Inhabited

@[nospecialize]
def setupWeightedDefs [HolBase] (D : SzemerediDeps) (BFiniteMeans : FiniteMeans) (BWords : Words) (BLines : Lines) (BDKTCor5 : DKTCor5) :
    ExceptT String IO WeightedDefs := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, MESON, MESON_TAC, MOD_DOWN_CONV,
        NUM_RING, new_definition, .. } := D
  let { ADD_CLAUSES, CARD_EQ_0, CARD_NUMSEG_LT, CARD_SUBSET, CONG,
        CONG_MULT_RCANCEL_IFF, EQ_TRANS, ETA_AX, FINITE_NUMSEG_LT, FINITE_RESTRICT,
        FINITE_SUBSET, IN_ELIM_THM, LT_NZ, MEMBER_NOT_EMPTY, MOD_LT, MOD_LT_EQ,
        MULT_SYM, .. } := D.core1
  let { NSUM_ADD, NSUM_CONST, NSUM_EQ, NSUM_RESTRICT_SET, PRODUCT_EQ, SUBSET, SUB_REFL,
        SUM_INJECTION, o_DEF, .. } := D.core2
  let { FMEAN_EQ, FMEAN_SHIFT_MOD, fmean, .. } := BFiniteMeans
  let { IN_HJ_CUBE, hj_subst, .. } := BWords
  let { HJ_LINE_CUBE, HJ_LINE_VAR, hj_line_point, .. } := BLines
  let { FMEAN_SWAP2, .. } := BDKTCor5
  -- @@SCOPE END

  let weighted_szemeredi ← new_definition
   r"weighted_szemeredi k <=>
    !delta. &0 < delta
            ==> ?c N0. &0 < c /\
                !N f. N0 <= N /\ prime N /\
                      (!y. y < N ==> &0 <= f y /\ f y <= &1) /\
                      delta <= fmean {y | y < N} f
                      ==> c <= fmean {a | a < N}
                                 (\a. fmean {d | d < N}
                                        (\d. product {j | j < k}
                                               (\j. f((a + j * d) MOD N))))"

  let MOD_AFFINE_MOD ← prove
   r"!N a b j. (a MOD N + j * (b MOD N)) MOD N = (a + j * b) MOD N"
   (← do
    pure (REPEAT GEN_TAC THEN CONV_TAC (LAND_CONV MOD_DOWN_CONV) THEN REFL_TAC))

  let FMEAN_DIL_MOD ← prove
   r"!N s (g:num->real).
        ~(N = 0) /\ coprime(s,N)
        ==> fmean {d | d < N} (\d. g((d * s) MOD N)) = fmean {d | d < N} g"
   (← do
    let m1 ← MESON [CONG, MOD_LT]
      (← q r"!x y n:num. x < n /\ y < n /\ (x == y) (mod n) ==> x = y")
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [fmean] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC (← ISPECL [← q r"g:num->real", ← q r"\d. (d * s) MOD N", ← q r"{d:num | d < N}"]
      SUM_INJECTION) THEN
    REWRITE_TAC [o_DEF, IN_ELIM_THM, FINITE_NUMSEG_LT] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [MOD_LT_EQ] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:num", ← q r"y:num"] THEN STRIP_TAC THEN
    MATCH_MP_TAC m1 THEN
    EXISTS_TAC (← q r"N:num") THEN ASM_REWRITE_TAC [] THEN
    MP_TAC (← SPECL [← q r"s:num", ← q r"N:num"] CONG_MULT_RCANCEL_IFF) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [CONG]))

  let FMEAN_AP_AFFINE ← prove
   r"!N k s s0 (h:num->real).
        ~(N = 0) /\ coprime(s,N)
        ==> fmean {t | t < N}
              (\t. fmean {d | d < N}
                     (\d. product {j | j < k}
                            (\j. h((t + d * (s0 + j * s)) MOD N)))) =
            fmean {a | a < N}
              (\a. fmean {e | e < N}
                     (\e. product {j | j < k} (\j. h((a + j * e) MOD N))))"
   (← do
    pure (REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     (← q r"fmean {d | d < N}
        (\d. fmean {t | t < N}
               (\t. product {j | j < k}
                      (\j. (h:num->real)((t + d * (s0 + j * s)) MOD N))))") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FMEAN_SWAP2 THEN REWRITE_TAC [FINITE_NUMSEG_LT], ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     (← q r"fmean {d | d < N}
        (\d. fmean {a | a < N}
               (\a. product {j | j < k}
                      (\j. (h:num->real)((a + j * ((d * s) MOD N))
                        MOD N))))") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FMEAN_EQ THEN X_GEN_TAC (← q r"d:num") THEN DISCH_TAC THEN
      REWRITE_TAC [] THEN
      MP_TAC (← ISPECL [← q r"N:num", ← q r"d * s0:num",
                        ← q r"\a. product {j | j < k}
                            (\j. (h:num->real)((a + j * ((d * s)
                              MOD N)) MOD N))"]
        FMEAN_SHIFT_MOD) THEN
      REWRITE_TAC [] THEN
      DISCH_THEN (fun th => tactic_of do pure (SUBST1_TAC (← SYM th))) THEN
      MATCH_MP_TAC FMEAN_EQ THEN X_GEN_TAC (← q r"t:num") THEN DISCH_TAC THEN
      REWRITE_TAC [] THEN MATCH_MP_TAC PRODUCT_EQ THEN
      X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN REWRITE_TAC [MOD_AFFINE_MOD] THEN
      AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC NUM_RING,
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     (← q r"fmean {a | a < N}
        (\a. fmean {d | d < N}
               (\d. product {j | j < k}
                      (\j. (h:num->real)((a + j * ((d * s) MOD N))
                        MOD N))))") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FMEAN_SWAP2 THEN REWRITE_TAC [FINITE_NUMSEG_LT], ALL_TAC] THEN
    MATCH_MP_TAC FMEAN_EQ THEN X_GEN_TAC (← q r"a:num") THEN DISCH_TAC THEN
    REWRITE_TAC [] THEN
    MATCH_MP_TAC (← BETA_RULE (← ISPECL
     [← q r"N:num", ← q r"s:num",
      ← q r"\e. product {j | j < k} (\j. (h:num->real)((a + j * e) MOD N))"]
     FMEAN_DIL_MOD)) THEN
    ASM_REWRITE_TAC []))

  let NSUM_HJ_LINE_POINT_GEN ← prove
   r"!k n l (g:num->num) a.
        hj_line k n l
        ==> nsum {r | r < n} (\r. g(hj_line_point k l a r)) =
            nsum {r | r < n} (\r. if l r < k then g(l r) else 0) +
            CARD {r | r < n /\ l r = k} * g a"
   (← do
    -- right to left: the second ARITH_RULE, then the first
    let a2 ← ARITH_RULE (← q r"x < k:num ==> ~(x = k)")
    let a1 ← ARITH_RULE (← q r"x < k + 1 <=> x <= k")
    pure (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"!i. i < n ==> (l:num->num) i <= k") ASSUME_TAC THENL
     [FIRST_ASSUM (MP_TAC o MATCH_MP HJ_LINE_CUBE) THEN
      REWRITE_TAC [IN_HJ_CUBE] THEN
      MESON_TAC [a1],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"nsum {r | r < n} (\r. (g:num->num)(hj_line_point k l a r)) =
      nsum {r | r < n} (\r. (if (l:num->num) r < k then g(l r) else 0) +
                            (if l r = k then g a else 0))")
    SUBST1_TAC THENL
     [MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC (← q r"i:num") THEN
      REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN
      REWRITE_TAC [hj_line_point, hj_subst] THEN
      ASM_CASES_TAC (← q r"(l:num->num) i < k") THEN
      ASM_SIMP_TAC [a2, ADD_CLAUSES] THEN
      SUBGOAL_THEN (← q r"(l:num->num) i = k") SUBST1_TAC THENL
       [FIRST_X_ASSUM (MP_TAC o SPEC (← q r"i:num")) THEN ASM_REWRITE_TAC [] THEN
        ASM_ARITH_TAC,
        REWRITE_TAC [SUB_REFL, ADD_CLAUSES]],
      ALL_TAC] THEN
    SIMP_TAC [NSUM_ADD, FINITE_NUMSEG_LT] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN
     (← q r"nsum {r | r < n} (\r. if (l:num->num) r = k then (g:num->num) a else 0) =
      nsum {r | r IN {r | r < n} /\ l r = k} (\r. g a)")
    SUBST1_TAC THENL [REWRITE_TAC [NSUM_RESTRICT_SET], ALL_TAC] THEN
    SIMP_TAC [NSUM_CONST, FINITE_RESTRICT, FINITE_NUMSEG_LT] THEN
    REWRITE_TAC [IN_ELIM_THM]))

  let HJ_LINE_WILDCARDS ← prove
   r"!k n l. hj_line k n l
           ==> 0 < CARD {r | r < n /\ l r = k} /\
               CARD {r | r < n /\ l r = k} <= n"
   (← do
    pure (REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"FINITE {r | r < n /\ (l:num->num) r = k}") ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{r:num | r < n}") THEN
      REWRITE_TAC [FINITE_NUMSEG_LT, SUBSET, IN_ELIM_THM] THEN MESON_TAC [],
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC [LT_NZ, CARD_EQ_0] THEN
      REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, IN_ELIM_THM] THEN
      ASM_MESON_TAC [HJ_LINE_VAR],
      GEN_REWRITE_TAC RAND_CONV [← GSYM CARD_NUMSEG_LT] THEN
      MATCH_MP_TAC CARD_SUBSET THEN
      REWRITE_TAC [FINITE_NUMSEG_LT, SUBSET, IN_ELIM_THM] THEN MESON_TAC []]))

  let NSUM_HJ_LINE_POINT ← prove
   r"!k n l. hj_line k n l
           ==> ?s0 w. 0 < w /\ w <= n /\
                      !a. nsum {i | i < n} (hj_line_point k l a) = s0 + a * w"
   (← do
    pure (REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [← q r"nsum {r | r < n} (\r. if (l:num->num) r < k then l r else 0)",
      ← q r"CARD {r | r < n /\ (l:num->num) r = k}"] THEN
    ASM_SIMP_TAC [HJ_LINE_WILDCARDS] THEN X_GEN_TAC (← q r"a:num") THEN
    MP_TAC (← ISPECL [← q r"k:num", ← q r"n:num", ← q r"l:num->num", ← q r"\x:num. x",
                      ← q r"a:num"]
      NSUM_HJ_LINE_POINT_GEN) THEN
    ASM_REWRITE_TAC [ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [MULT_SYM]))

  -- @@RETURN BEGIN
  return { weighted_szemeredi, MOD_AFFINE_MOD, FMEAN_DIL_MOD, FMEAN_AP_AFFINE,
           NSUM_HJ_LINE_POINT_GEN, HJ_LINE_WILDCARDS, NSUM_HJ_LINE_POINT }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- Densities along affine maps; progressions in a dense subset of Z_N from   -/
/- density Hales-Jewett.  (szemeredi.ml 6074-6333)                           -/
/- ------------------------------------------------------------------------- -/

structure APBound where
  -- @@FIELDS
  FMEAN_HJ_DENSITY_AFFINE : thm
  FMEAN_HJ_LINE_AP : thm
  HJ_LINE_COUNT_BOUND : thm
  SZEMEREDI_AP_INDICATOR_BOUND : thm
  deriving Inhabited

@[nospecialize]
def setupAPBound [HolBase] (D : SzemerediDeps) (BFiniteMeans : FiniteMeans) (BWords : Words) (BLines : Lines) (BDensities : Densities) (BDensityHJ : DensityHJ) (BDKTCor5 : DKTCor5) (BWeightedDefs : WeightedDefs) :
    ExceptT String IO APBound := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON_TAC,
        REAL_ARITH, REAL_ARITH_TAC, .. } := D
  let { ADD_SYM, CARD_SUBSET, EQ_TRANS, EXP_EQ_0, FINITE_DELETE, FINITE_NUMSEG_LT,
        FINITE_SUBSET, IN_ELIM_THM, LE_REFL, LT_NZ, MEMBER_NOT_EMPTY, .. } := D.core1
  let { PRIME_0, PRIME_COPRIME_LT, PRODUCT_EQ_1, PRODUCT_POS_LE, REAL_EQ_IMP_LE,
        REAL_LE_LDIV_EQ, REAL_LE_RMUL, REAL_LE_TRANS, REAL_MUL_SYM, REAL_OF_NUM_LE,
        REAL_OF_NUM_LT, SUBSET, SUM_CONST, SUM_DELETE, SUM_EQ, SUM_POS_LE, .. } := D.core2
  let { FMEAN_CONST, FMEAN_EQ, FMEAN_LE, FMEAN_POS, FMEAN_SHIFT_MOD, FMEAN_SUB,
        FMEAN_SUM, .. } := BFiniteMeans
  let { CARD_HJ_CUBE, FINITE_HJ_CUBE, HJ_CUBE_NONEMPTY, .. } := BWords
  let { HJ_LINE_CUBE, hj_has_line, .. } := BLines
  let { HJ_DENSITY_LE_1, hj_density, .. } := BDensities
  let { density_hales_jewett, .. } := BDensityHJ
  let { FMEAN_SWAP2, .. } := BDKTCor5
  let { FMEAN_AP_AFFINE, NSUM_HJ_LINE_POINT, .. } := BWeightedDefs
  -- @@SCOPE END

  let FMEAN_HJ_DENSITY_AFFINE ← prove
   r"!k n N (A:num->bool).
        1 <= k /\ ~(N = 0)
        ==> fmean {t | t < N}
              (\t. fmean {d | d < N}
                     (\d. hj_density k n
                            {x | (t + d * nsum {i | i < n} x) MOD N IN A})) =
            fmean {y:num | y < N} (\y. if y IN A then &1 else &0)"
   (← do
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [hj_density, IN_ELIM_THM] THEN
    SUBGOAL_THEN (← q r"FINITE {y:num | y < N} /\ ~({y:num | y < N} = {})")
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC [FINITE_NUMSEG_LT, ← GSYM MEMBER_NOT_EMPTY, IN_ELIM_THM] THEN
      EXISTS_TAC (← q r"0") THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     (← q r"fmean {d | d < N}
        (\d. fmean {t | t < N}
               (\t. fmean (hj_cube k n)
                      (\x. if (t + d * nsum {i | i < n} x) MOD N IN A
                           then &1 else &0)))") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FMEAN_SWAP2 THEN REWRITE_TAC [FINITE_NUMSEG_LT], ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     (← q r"fmean {d | d < N}
        (\d:num. fmean {y:num | y < N} (\y. if y IN A then &1 else &0))") THEN
    CONJ_TAC THENL
     [ALL_TAC, MATCH_MP_TAC FMEAN_CONST THEN ASM_REWRITE_TAC []] THEN
    MATCH_MP_TAC FMEAN_EQ THEN X_GEN_TAC (← q r"d:num") THEN DISCH_TAC THEN
    REWRITE_TAC [] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     (← q r"fmean (hj_cube k n)
        (\x. fmean {t | t < N}
               (\t. if (t + d * nsum {i | i < n} x) MOD N IN A
                    then &1 else &0))") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FMEAN_SWAP2 THEN
      REWRITE_TAC [FINITE_NUMSEG_LT, FINITE_HJ_CUBE],
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     (← q r"fmean (hj_cube k n)
        (\x:num->num. fmean {y:num | y < N} (\y. if y IN A then &1
          else &0))") THEN
    CONJ_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC FMEAN_CONST THEN
        ASM_SIMP_TAC [FINITE_HJ_CUBE, HJ_CUBE_NONEMPTY]] THEN
    MATCH_MP_TAC FMEAN_EQ THEN X_GEN_TAC (← q r"x:num->num") THEN DISCH_TAC THEN
    REWRITE_TAC [] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     (← q r"fmean {t | t < N}
        (\t. (\y. if y IN A then &1 else &0)
             ((d * nsum {i | i < n} (x:num->num) + t) MOD N))") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FMEAN_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC [ADD_SYM],
      ACCEPT_TAC (← ISPECL [← q r"N:num", ← q r"d * nsum {i | i < n} (x:num->num)",
                            ← q r"\y:num. if y IN A then &1 else &0"]
                             FMEAN_SHIFT_MOD)]))

  let FMEAN_HJ_LINE_AP ← prove
   r"!k n N l (A:num->bool).
        prime N /\ n < N /\ hj_line k n l
        ==> fmean {t | t < N}
              (\t. fmean {d | d < N}
                     (\d. product {j | j < k}
                            (\j. if (t + d *
                                     nsum {i | i < n} (hj_line_point k l j))
                                    MOD N IN A then &1 else &0))) =
            fmean {a | a < N}
              (\a. fmean {e | e < N}
                     (\e. product {j | j < k}
                            (\j. if (a + j * e) MOD N IN A
                                 then &1 else &0)))"
   (← do
    pure (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP NSUM_HJ_LINE_POINT) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"s0:num") (X_CHOOSE_THEN (← q r"w:num")
      STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC (← BETA_RULE (← ISPECL
     [← q r"N:num", ← q r"k:num", ← q r"w:num", ← q r"s0:num",
      ← q r"\y:num. if y IN A then &1 else &0"]
     FMEAN_AP_AFFINE)) THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC [PRIME_0],
      MATCH_MP_TAC PRIME_COPRIME_LT THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC]))

  let HJ_LINE_COUNT_BOUND ← prove
   r"!k n N (A:num->bool) t d delta.
        (!B. delta <= hj_density k n B ==> hj_has_line k n B) /\ &0 <= delta
        ==> hj_density k n
              {x | (t + d * nsum {i | i < n} x) MOD N IN A} - delta <=
            sum {l | hj_line k n l}
              (\l. product {j | j < k}
                     (\j. if (t + d *
                              nsum {i | i < n}
                                (hj_line_point k l j)) MOD N IN A
                          then &1 else &0))"
   (← do
    let r1 ← REAL_ARITH (← q r"!a b c. &0 <= a ==> a = b - c ==> c <= b")
    pure (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"FINITE {l | hj_line k n l}") ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"hj_cube (k + 1) n") THEN
      REWRITE_TAC [FINITE_HJ_CUBE, SUBSET, IN_ELIM_THM] THEN
      MESON_TAC [HJ_LINE_CUBE],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!l. &0 <= product {j | j < k}
                  (\j. if (t + d *
                           nsum {i | i < n} (hj_line_point k l j)) MOD N IN A
                       then &1 else &0)")
    ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC PRODUCT_POS_LE THEN
      REWRITE_TAC [FINITE_NUMSEG_LT] THEN REPEAT STRIP_TAC THEN
      COND_CASES_TAC THEN REAL_ARITH_TAC,
      ALL_TAC] THEN
    ABBREV_TAC
     (← q r"B = {x:num->num | (t + d * nsum {i:num | i < n} x) MOD N IN A}") THEN
    ASM_CASES_TAC (← q r"delta <= hj_density k n B") THENL
     [ALL_TAC,
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"&0") THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC, MATCH_MP_TAC SUM_POS_LE] THEN
      ASM_REWRITE_TAC []] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"B:(num->num)->bool")) THEN
    ASM_REWRITE_TAC [hj_has_line] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"l:num->num") STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"&1") THEN CONJ_TAC THENL
     [MP_TAC (← SPECL [← q r"k:num", ← q r"n:num", ← q r"B:(num->num)->bool"]
        HJ_DENSITY_LE_1) THEN
      ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     (← q r"product {j | j < k}
        (\j. if (t + d * nsum {i | i < n} (hj_line_point k l j)) MOD N IN A
             then &1 else &0)") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC PRODUCT_EQ_1 THEN X_GEN_TAC (← q r"j:num") THEN
      REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"j:num")) THEN ASM_REWRITE_TAC [] THEN
      EXPAND_TAC "B" THEN SIMP_TAC [IN_ELIM_THM],
      ALL_TAC] THEN
    MP_TAC (← ISPECL
     [← q r"\l. product {j | j < k}
             (\j. if (t + d * nsum {i | i < n} (hj_line_point k l j)) MOD N IN A
                  then &1 else &0)",
      ← q r"{l | hj_line k n l}", ← q r"l:num->num"] SUM_DELETE) THEN
    ASM_REWRITE_TAC [IN_ELIM_THM] THEN
    MATCH_MP_TAC r1 THEN
    MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC [FINITE_DELETE]))

  let SZEMEREDI_AP_INDICATOR_BOUND ← prove
   r"!k delta.
        1 <= k /\ density_hales_jewett k /\ &0 < delta
        ==> ?n. !N (A:num->bool).
                  prime N /\ n < N /\
                  delta <= fmean {y | y < N} (\y. if y IN A then &1 else &0)
                  ==> delta / &2 / &((k + 1) EXP n) <=
                      fmean {a | a < N}
                        (\a. fmean {e | e < N}
                               (\e. product {j | j < k}
                                      (\j. if (a + j * e) MOD N IN A
                                           then &1 else &0)))"
   (← do
    let r1 ← REAL_ARITH (← q r"!x. &0 < x / &2 <=> &0 < x")
    pure (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"delta / &2")
                  o REWRITE_RULE [density_hales_jewett]) THEN
    ASM_REWRITE_TAC [r1] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"n0:num")) THEN EXISTS_TAC (← q r"n0:num") THEN
    MAP_EVERY X_GEN_TAC [← q r"N:num", ← q r"A:num->bool"] THEN STRIP_TAC THEN
    ABBREV_TAC (← q r"aA = fmean {y:num | y < N} (\y. if y IN A then &1 else &0)") THEN
    SUBGOAL_THEN (← q r"~(N = 0)") ASSUME_TAC THENL
     [ASM_MESON_TAC [PRIME_0], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"FINITE {y:num | y < N} /\ ~({y:num | y < N} = {})")
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC [FINITE_NUMSEG_LT, ← GSYM MEMBER_NOT_EMPTY, IN_ELIM_THM] THEN
      EXISTS_TAC (← q r"0") THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"FINITE {l | hj_line k n0 l} /\
      &(CARD {l | hj_line k n0 l}) <= &((k + 1) EXP n0)")
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC [REAL_OF_NUM_LE] THEN
      SUBGOAL_THEN (← q r"{l | hj_line k n0 l} SUBSET hj_cube (k + 1) n0")
      ASSUME_TAC THENL
       [REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN MESON_TAC [HJ_LINE_CUBE],
        ALL_TAC] THEN
      CONJ_TAC THENL [ASM_MESON_TAC [FINITE_SUBSET, FINITE_HJ_CUBE], ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [← GSYM CARD_HJ_CUBE] THEN
      MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC [FINITE_HJ_CUBE],
      ALL_TAC] THEN
    ABBREV_TAC
     (← q r"ap = fmean {a | a < N}
             (\a. fmean {e | e < N}
                    (\e. product {j | j < k}
                           (\j. if (a + j * e) MOD N IN A then &1
                             else &0)))") THEN
    SUBGOAL_THEN (← q r"&0 <= ap") ASSUME_TAC THENL
     [EXPAND_TAC "ap" THEN MATCH_MP_TAC FMEAN_POS THEN
      REWRITE_TAC [FINITE_NUMSEG_LT] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC FMEAN_POS THEN REWRITE_TAC [FINITE_NUMSEG_LT] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC PRODUCT_POS_LE THEN
      REWRITE_TAC [FINITE_NUMSEG_LT] THEN REPEAT STRIP_TAC THEN
      COND_CASES_TAC THEN REAL_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"aA - delta / &2 <=
      &(CARD {l | hj_line k n0 l}) * ap")
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
       (← q r"fmean {t | t < N}
          (\t. fmean {d | d < N}
                 (\d. hj_density k n0
                        {x | (t + d * nsum {i | i < n0} x) MOD N IN A} -
                      delta / &2))") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        ASM_SIMP_TAC [FMEAN_SUB, FINITE_NUMSEG_LT, FMEAN_CONST,
                      FMEAN_HJ_DENSITY_AFFINE],
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
       (← q r"fmean {t | t < N}
          (\t. fmean {d | d < N}
                 (\d. sum {l | hj_line k n0 l}
                        (\l. product {j | j < k}
                               (\j. if (t + d *
                                        nsum {i | i < n0} (hj_line_point k l j))
                                       MOD N IN A then &1 else &0))))") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FMEAN_LE THEN REWRITE_TAC [FINITE_NUMSEG_LT] THEN
        X_GEN_TAC (← q r"t:num") THEN DISCH_TAC THEN
        MATCH_MP_TAC FMEAN_LE THEN REWRITE_TAC [FINITE_NUMSEG_LT] THEN
        X_GEN_TAC (← q r"d:num") THEN DISCH_TAC THEN
        MATCH_MP_TAC HJ_LINE_COUNT_BOUND THEN
        CONJ_TAC THENL [ASM_MESON_TAC [LE_REFL], ASM_REAL_ARITH_TAC],
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      ASM_SIMP_TAC [FMEAN_SUM, FINITE_NUMSEG_LT] THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC (← q r"sum {l | hj_line k n0 l} (\l. ap)") THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC (← q r"l:num->num") THEN
        REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN EXPAND_TAC "ap" THEN
        MATCH_MP_TAC FMEAN_HJ_LINE_AP THEN ASM_REWRITE_TAC [],
        ASM_SIMP_TAC [SUM_CONST]],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"&0 < &((k + 1) EXP n0)") ASSUME_TAC THENL
     [REWRITE_TAC [REAL_OF_NUM_LT, LT_NZ, EXP_EQ_0] THEN ARITH_TAC, ALL_TAC] THEN
    MP_TAC (← SPECL [← q r"delta / &2", ← q r"ap:real", ← q r"&((k + 1) EXP n0)"]
      REAL_LE_LDIV_EQ) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
    ABBREV_TAC (← q r"cL = &(CARD {l | hj_line k n0 l})") THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"cL * ap:real") THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC,
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC []]))

  -- @@RETURN BEGIN
  return { FMEAN_HJ_DENSITY_AFFINE, FMEAN_HJ_LINE_AP, HJ_LINE_COUNT_BOUND,
           SZEMEREDI_AP_INDICATOR_BOUND }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- The weighted Szemeredi theorem.  (szemeredi.ml 6334-6415)                 -/
/- ------------------------------------------------------------------------- -/

structure WeightedThm where
  -- @@FIELDS
  WEIGHTED_SZEMEREDI_DHJ : thm
  WEIGHTED_SZEMEREDI : thm
  deriving Inhabited

@[nospecialize]
def setupWeightedThm [HolBase] (D : SzemerediDeps) (BFiniteMeans : FiniteMeans) (BDensityHJThm : DensityHJThm) (BWeightedDefs : WeightedDefs) (BAPBound : APBound) :
    ExceptT String IO WeightedThm := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_ARITH_TAC, ASM_REAL_ARITH_TAC, MESON_TAC, REAL_ARITH, .. } := D
  let { CARD_NUMSEG_LT, EXP_EQ_0, FINITE_NUMSEG_LT, IN_ELIM_THM, LT_NZ,
        MEMBER_NOT_EMPTY, MOD_LT_EQ, .. } := D.core1
  let { PRODUCT_CONST, PRODUCT_LE, PRODUCT_MUL, REAL_LE_LMUL, REAL_LE_REFL,
        REAL_LE_TRANS, REAL_LT_DIV, REAL_LT_MUL, REAL_OF_NUM_LT, REAL_POW_LE,
        REAL_POW_LT, .. } := D.core2
  let { FMEAN_ADD, FMEAN_CONST, FMEAN_LE, FMEAN_LMUL, .. } := BFiniteMeans
  let { DENSITY_HALES_JEWETT, .. } := BDensityHJThm
  let { weighted_szemeredi, .. } := BWeightedDefs
  let { SZEMEREDI_AP_INDICATOR_BOUND, .. } := BAPBound
  -- @@SCOPE END

  let WEIGHTED_SZEMEREDI_DHJ ← prove
   r"!k. 1 <= k /\ density_hales_jewett k ==> weighted_szemeredi k"
   (← do
    -- right to left: the second REAL_ARITH, then the first
    let r2 ← REAL_ARITH
      (← q r"!a b. delta <= b /\ b <= a + delta / &2 ==> delta / &2 <= a")
    let r1 ← REAL_ARITH (← q r"!x. &0 < x / &2 <=> &0 < x")
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [weighted_szemeredi] THEN
    X_GEN_TAC (← q r"delta:real") THEN DISCH_TAC THEN
    MP_TAC (← SPECL [← q r"k:num", ← q r"delta / &2"] SZEMEREDI_AP_INDICATOR_BOUND) THEN
    ASM_REWRITE_TAC [r1] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"n:num")) THEN
    EXISTS_TAC (← q r"(delta / &2) pow k * (delta / &2 / &2 / &((k + 1) EXP n))") THEN
    EXISTS_TAC (← q r"n + 1") THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC,
        MATCH_MP_TAC REAL_LT_DIV THEN
        REWRITE_TAC [REAL_OF_NUM_LT, LT_NZ, EXP_EQ_0] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ARITH_TAC]],
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [← q r"N:num", ← q r"f:num->real"] THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"~(N = 0)") ASSUME_TAC THENL
     [UNDISCH_TAC (← q r"n + 1 <= N") THEN ARITH_TAC, ALL_TAC] THEN
    SUBGOAL_THEN (← q r"FINITE {y:num | y < N} /\ ~({y:num | y < N} = {})")
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC [FINITE_NUMSEG_LT, ← GSYM MEMBER_NOT_EMPTY, IN_ELIM_THM] THEN
      EXISTS_TAC (← q r"0") THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    ABBREV_TAC (← q r"A = {y | delta / &2 <= (f:num->real) y}") THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"N:num", ← q r"A:num->bool"]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      MATCH_MP_TAC r2 THEN
      EXISTS_TAC (← q r"fmean {y:num | y < N} (f:num->real)") THEN
        ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"fmean {y:num | y < N}
                    (\y. (if y IN A then &1 else &0) + delta / &2)") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FMEAN_LE THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN
        X_GEN_TAC (← q r"y:num") THEN DISCH_TAC THEN EXPAND_TAC "A" THEN
        REWRITE_TAC [IN_ELIM_THM] THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"y:num")) THEN ASM_REWRITE_TAC [] THEN
        COND_CASES_TAC THEN ASM_REAL_ARITH_TAC,
        ASM_SIMP_TAC [FMEAN_ADD, FMEAN_CONST, REAL_LE_REFL]],
      ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     (← q r"(delta / &2) pow k *
      fmean {a | a < N}
        (\a. fmean {e | e < N}
               (\e. product {j | j < k}
                      (\j. if (a + j * e) MOD N IN A then &1 else &0)))") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [← GSYM FMEAN_LMUL] THEN
    MATCH_MP_TAC FMEAN_LE THEN REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"a:num") THEN DISCH_TAC THEN
    MATCH_MP_TAC FMEAN_LE THEN REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"e:num") THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     (← q r"product {j | j < k}
        (\j. delta / &2 * (if (a + j * e) MOD N IN A then &1 else &0))") THEN
    CONJ_TAC THENL
     [SIMP_TAC [PRODUCT_MUL, PRODUCT_CONST, FINITE_NUMSEG_LT, CARD_NUMSEG_LT] THEN
      REWRITE_TAC [REAL_LE_REFL],
      ALL_TAC] THEN
    MATCH_MP_TAC PRODUCT_LE THEN REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN
    FIRST_X_ASSUM (fun th => tactic_of do
      let ok ← if is_forall (concl th) then do
          let v ← q r"f:num->real"
          pure (can (find_term (fun u => u == v)) (concl th))
        else pure false
      pure (MP_TAC (← SPEC (← q r"(a + j * e) MOD N")
        (← liftExcept (check (fun _ => ok) th))))) THEN
    ASM_REWRITE_TAC [MOD_LT_EQ] THEN EXPAND_TAC "A" THEN
    REWRITE_TAC [IN_ELIM_THM] THEN
    COND_CASES_TAC THEN ASM_REAL_ARITH_TAC))

  let WEIGHTED_SZEMEREDI ← prove
   r"!k. 1 <= k ==> weighted_szemeredi k"
   (← do
    pure (MESON_TAC [WEIGHTED_SZEMEREDI_DHJ, DENSITY_HALES_JEWETT]))

  -- @@RETURN BEGIN
  return { WEIGHTED_SZEMEREDI_DHJ, WEIGHTED_SZEMEREDI }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- Progressions mod N and genuine progressions.  (szemeredi.ml 6416-6647)    -/
/- ------------------------------------------------------------------------- -/

structure ModAP where
  -- @@FIELDS
  CARD_PAIRS_SUM : thm
  AP_COUNT_NONTRIVIAL : thm
  MOD_AP_LINEAR : thm
  MOD_AP_CASES : thm
  MOD_ADD_LCANCEL : thm
  deriving Inhabited

@[nospecialize]
def setupModAP [HolBase] (D : SzemerediDeps) (BFiniteMeans : FiniteMeans) :
    ExceptT String IO ModAP := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, INDUCT_TAC,
        INTEGER_RULE, INT_ARITH_TAC, MESON, MESON_TAC, NUMBER_RULE, REAL_ARITH,
        REAL_FIELD, .. } := D
  let { ADD1, ADD_CLAUSES, CARD_EQ_SUM, CARD_NUMSEG_LT, CONG, CONG_LMOD, CONJ_ASSOC,
        EXTENSION, FINITE_NUMSEG_LT, FINITE_PRODUCT, FINITE_RESTRICT, FORALL_PAIR_THM,
        FST, INT_ADD_RID, INT_CONG_IMP_EQ, INT_MUL_LZERO, INT_OF_NUM_ADD,
        INT_OF_NUM_EQ, INT_OF_NUM_LT, INT_OF_NUM_MUL, INT_OF_NUM_SUB, INT_POS,
        INT_SUB_REFL, IN_ELIM_PAIR_THM, IN_ELIM_THM, LT_IMP_LE, LT_NZ, LT_REFL, MOD_LT,
        MOD_LT_EQ, MOD_MOD_REFL, MONO_EXISTS, MULT_CLAUSES, NOT_FORALL_THM, NOT_IMP, .. } := D.core1
  let { PRODUCT_CONST, PRODUCT_EQ_0, PRODUCT_LE, REAL_ADD_LID, REAL_EQ_IMP_LE,
        REAL_LE_REFL, REAL_LE_TRANS, REAL_MUL_LID, REAL_MUL_LZERO, REAL_OF_NUM_EQ, SND,
        SUM_ADD, SUM_CONST, SUM_DELTA, SUM_EQ, SUM_LE, SUM_RESTRICT_SET, SUM_RMUL,
        SUM_SUM_PRODUCT, num_congruent, real_div, .. } := D.core2
  let { fmean, .. } := BFiniteMeans
  -- @@SCOPE END

  let CARD_PAIRS_SUM ← prove
   r"!N (P:num->num->bool).
        &(CARD {(a,d) | a < N /\ d < N /\ P a d}) =
        sum {a | a < N} (\a. sum {d | d < N} (\d. if P a d then &1 else &0))"
   (← do
    pure (REPEAT GEN_TAC THEN SIMP_TAC [SUM_SUM_PRODUCT, FINITE_NUMSEG_LT] THEN
    SUBGOAL_THEN
     (← q r"{(a,d) | a < N /\ d < N /\ (P:num->num->bool) a d} =
      {x | x IN {i,j | i IN {a:num | a < N} /\ j IN {d:num | d < N}} /\
           P (FST x) (SND x)}")
    SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, FORALL_PAIR_THM, IN_ELIM_PAIR_THM, IN_ELIM_THM] THEN
      REWRITE_TAC [FST, SND, CONJ_ASSOC],
      ALL_TAC] THEN
    SIMP_TAC [CARD_EQ_SUM, FINITE_RESTRICT, FINITE_PRODUCT, FINITE_NUMSEG_LT] THEN
    REWRITE_TAC [SUM_RESTRICT_SET] THEN MATCH_MP_TAC SUM_EQ THEN
    REWRITE_TAC [FORALL_PAIR_THM]))

  let AP_COUNT_NONTRIVIAL ← prove
   r"!k N (f:num->real) B.
        1 <= N /\ (!y. y < N ==> &0 <= f y /\ f y <= B)
        ==> &N pow 2 *
            fmean {a | a < N}
              (\a. fmean {d | d < N}
                     (\d. product {j | j < k} (\j. f((a + j * d) MOD N))))
            <= &N * B pow k +
               &(CARD {(a,d) | a < N /\ 0 < d /\ d < N /\
                               !j. j < k ==> &0 < f((a + j * d) MOD N)}) *
               B pow k"
   (← do
    -- right to left: the four rules from the last to the first
    let r4 ← REAL_ARITH (← q r"&0 <= x /\ ~(&0 < x) ==> x = &0")
    let a3 ← ARITH_RULE (← q r"1 <= N ==> 0 < N")
    let f2 ← REAL_FIELD
      (← q r"!n x. ~(n = &0) ==> n pow 2 * (x * inv n) * inv n = x")
    let a1 ← ARITH_RULE (← q r"1 <= N ==> ~(N = 0)")
    pure (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"!y. &0 <= (f:num->real)(y MOD N) /\ f(y MOD N) <= B")
    ASSUME_TAC THENL
     [GEN_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC (← q r"y MOD N")) THEN
      ASM_SIMP_TAC [MOD_LT_EQ, a1],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"&0 <= B") ASSUME_TAC THENL
     [ASM_MESON_TAC [REAL_LE_TRANS], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"{(a,d) | a < N /\ 0 < d /\ d < N /\
               !j. j < k ==> &0 < (f:num->real)((a + j * d) MOD N)} =
      {(a,d) | a < N /\ d < N /\
               (0 < d /\ !j. j < k ==> &0 < f((a + j * d) MOD N))}")
    SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, FORALL_PAIR_THM, IN_ELIM_PAIR_THM] THEN
      MESON_TAC [],
      ALL_TAC] THEN
    REWRITE_TAC [CARD_PAIRS_SUM] THEN
    SUBGOAL_THEN
     (← q r"&N pow 2 *
      fmean {a | a < N}
        (\a. fmean {d | d < N}
               (\d. product {j | j < k} (\j. (f:num->real)((a + j *
                 d) MOD N)))) =
      sum {a | a < N}
        (\a. sum {d | d < N}
               (\d. product {j | j < k} (\j. f((a + j * d) MOD N))))")
    SUBST1_TAC THENL
     [REWRITE_TAC [fmean, CARD_NUMSEG_LT, real_div, SUM_RMUL] THEN
      MATCH_MP_TAC f2 THEN
      REWRITE_TAC [REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"&N * B pow k = sum {a | a < N}
                       (\a. sum {d | d < N} (\d. if d = 0 then B pow k else &0))")
    SUBST1_TAC THENL
     [REWRITE_TAC [SUM_DELTA, IN_ELIM_THM] THEN
      ASM_SIMP_TAC [a3, SUM_CONST, FINITE_NUMSEG_LT,
                    CARD_NUMSEG_LT],
      ALL_TAC] THEN
    REWRITE_TAC [← GSYM SUM_RMUL] THEN
    SIMP_TAC [← GSYM SUM_ADD, FINITE_NUMSEG_LT] THEN
    MATCH_MP_TAC SUM_LE THEN REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"a:num") THEN DISCH_TAC THEN
    MATCH_MP_TAC SUM_LE THEN REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"d:num") THEN DISCH_TAC THEN
    ABBREV_TAC
     (← q r"P = product {j | j < k} (\j. (f:num->real)((a + j * d) MOD N))") THEN
    SUBGOAL_THEN (← q r"P <= B pow k") ASSUME_TAC THENL
     [EXPAND_TAC "P" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"product {j:num | j < k} (\j. B)") THEN CONJ_TAC THENL
       [MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT],
        SIMP_TAC [PRODUCT_CONST, FINITE_NUMSEG_LT, CARD_NUMSEG_LT,
                  REAL_LE_REFL]],
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"d = 0") THENL
     [ASM_REWRITE_TAC [LT_REFL] THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    ASM_REWRITE_TAC [LT_NZ] THEN
    ASM_CASES_TAC (← q r"!j. j < k ==> &0 < (f:num->real)((a + j * d) MOD N)") THEN
    ASM_REWRITE_TAC [REAL_ADD_LID, REAL_MUL_LID, REAL_MUL_LZERO] THEN
    EXPAND_TAC "P" THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    SIMP_TAC [PRODUCT_EQ_0, FINITE_NUMSEG_LT, IN_ELIM_THM] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"j:num") THEN
    REWRITE_TAC [NOT_IMP] THEN
    ASM_MESON_TAC [r4]))

  let MOD_AP_LINEAR ← prove
   r"!k N a d (n:num->num).
        2 <= k /\ 0 < d /\ d < N /\
        (!j. j < k ==> n j = (a + j * d) MOD N /\ 2 * n j < N)
        ==> ~(n 1 = n 0) /\
            !j. j < k ==> &(n j):int = &(n 0) + &j * (&(n 1) - &(n 0))"
   (← do
    -- right to left: the MESON, the INTEGER_RULE, then the ARITH_RULE
    let m3 ← MESON [CONG, MOD_LT]
      (← q r"!x y n:num. x < n /\ y < n /\ (x == y) (mod n) ==> x = y")
    let i2 ← INTEGER_RULE
      (← q r"!x y d n:int. (x == d) (mod n) /\ (y == d) (mod n)
                      ==> (x == y) (mod n)")
    let a1 ← ARITH_RULE (← q r"j + 1 < k ==> j < k")
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"!j. j + 1 < k ==> (&(n (j + 1)) - &(n j) == &d:int) (mod &N)")
    ASSUME_TAC THENL
     [X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN
      SUBGOAL_THEN
       (← q r"(&(n (j + 1)) == &(a + (j + 1) * d):int) (mod &N) /\
        (&(n j) == &(a + j * d):int) (mod &N)")
      MP_TAC THENL
       [REWRITE_TAC [← GSYM num_congruent] THEN
        ASM_SIMP_TAC [a1, CONG_LMOD, CONG,
                      MOD_MOD_REFL],
        REWRITE_TAC [← GSYM INT_OF_NUM_ADD, ← GSYM INT_OF_NUM_MUL] THEN
        CONV_TAC INTEGER_RULE],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!j. j < k ==> 2 * (n:num->num) j < N") ASSUME_TAC THENL
     [ASM_SIMP_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(&(n 1) - &(n 0) == &d:int) (mod &N)") ASSUME_TAC THENL
     [MP_TAC (← SPEC (← q r"0") (← ASSUME
       (← q r"!j. j + 1 < k ==> (&((n:num->num) (j + 1)) - &(n j) == &d:int)
                          (mod &N)"))) THEN
      REWRITE_TAC [ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    ABBREV_TAC (← q r"e0:int = &(n 1) - &(n 0)") THEN
    SUBGOAL_THEN (← q r"!j. j + 1 < k ==> &(n (j + 1)) - &(n j):int = e0")
    ASSUME_TAC THENL
     [X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN EXPAND_TAC "e0" THEN
      MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC (← q r"&N:int") THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN (← q r"2 * (n:num->num) j < N /\ 2 * n (j + 1) < N /\
                      2 * n 0 < N /\ 2 * n 1 < N") MP_TAC THENL
         [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC,
          ALL_TAC] THEN
        REWRITE_TAC [← GSYM INT_OF_NUM_LT, ← GSYM INT_OF_NUM_MUL] THEN
        MP_TAC (← SPEC (← q r"n (j:num):num") INT_POS) THEN
        MP_TAC (← SPEC (← q r"n (j + 1):num") INT_POS) THEN
        MP_TAC (← SPEC (← q r"n 0:num") INT_POS) THEN
        MP_TAC (← SPEC (← q r"n 1:num") INT_POS) THEN INT_ARITH_TAC,
        MATCH_MP_TAC i2 THEN
        EXISTS_TAC (← q r"&d:int") THEN ASM_SIMP_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"~(e0:int = &0)") ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC (← q r"(e0 == &d:int) (mod &N)") THEN
      ASM_REWRITE_TAC [← GSYM num_congruent] THEN DISCH_TAC THEN
      MP_TAC (← SPECL [← q r"0", ← q r"d:num", ← q r"N:num"] m3) THEN
      ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC (← q r"~(e0:int = &0)") THEN EXPAND_TAC "e0" THEN
      UNDISCH_TAC (← q r"(n:num->num) 1 = n 0") THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC [INT_SUB_REFL],
      ALL_TAC] THEN
    INDUCT_TAC THENL [REWRITE_TAC [INT_MUL_LZERO, INT_ADD_RID], ALL_TAC] THEN
    DISCH_TAC THEN
    UNDISCH_TAC (← q r"j:num < k ==> &(n j):int = &(n 0) + &j * e0") THEN
    ANTS_TAC THENL [ASM_ARITH_TAC, DISCH_TAC] THEN
    MP_TAC (← SPEC (← q r"j:num")
     (← ASSUME (← q r"!j. j + 1 < k
                  ==> &((n:num->num) (j + 1)) - &(n j):int = e0"))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
    ASM_REWRITE_TAC [ADD1, ← GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC))

  let MOD_AP_CASES ← prove
   r"!k N a d.
        2 <= k /\ a < N /\ 0 < d /\ d < N /\
        (!j. j < k ==> 2 * ((a + j * d) MOD N) < N)
        ==> ~((a + d) MOD N = a) /\
            (a < (a + d) MOD N
             ==> !j. j < k
                     ==> (a + j * d) MOD N = a + j * ((a + d) MOD N - a)) /\
            ((a + d) MOD N < a
             ==> !j. j < k
                     ==> (a + j * d) MOD N + j * (a - (a + d) MOD N) = a)"
   (← do
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"k:num", ← q r"N:num", ← q r"a:num", ← q r"d:num",
                      ← q r"\j. (a + j * d) MOD N"] MOD_AP_LINEAR) THEN
    ASM_SIMP_TAC [MULT_CLAUSES, ADD_CLAUSES, MOD_LT] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THEN DISCH_TAC THEN
    X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"j:num")) THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [← GSYM INT_OF_NUM_EQ, ← GSYM INT_OF_NUM_ADD,
                 ← GSYM INT_OF_NUM_MUL] THEN
    ASM_SIMP_TAC [← GSYM INT_OF_NUM_SUB, LT_IMP_LE] THEN INT_ARITH_TAC))

  let MOD_ADD_LCANCEL ← prove
   r"!N a d d'. d < N /\ d' < N /\ (a + d) MOD N = (a + d') MOD N ==> d = d'"
   (← do
    let n1 ← ExceptT.mk (NUMBER_RULE
      (← q r"!a n x y:num. (a + x == a + y) (mod n) <=> (x == y) (mod n)"))
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM CONG] THEN
    REWRITE_TAC [n1] THEN
    MESON_TAC [CONG, MOD_LT]))

  -- @@RETURN BEGIN
  return { CARD_PAIRS_SUM, AP_COUNT_NONTRIVIAL, MOD_AP_LINEAR, MOD_AP_CASES,
           MOD_ADD_LCANCEL }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- Increasing and decreasing progressions from progressions mod N.           -/
/- (szemeredi.ml 6648-6741)                                                  -/
/- ------------------------------------------------------------------------- -/

structure UpDown where
  -- @@FIELDS
  SZEMEREDI_UP_PROGRESSION : thm
  SZEMEREDI_DOWN_PROGRESSION : thm
  deriving Inhabited

@[nospecialize]
def setupUpDown [HolBase] (D : SzemerediDeps) (BModAP : ModAP) :
    ExceptT String IO UpDown := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, NUM_RING, .. } := D
  let { ADD_CLAUSES, LT_MULT, MOD_LT, MULT_CLAUSES, .. } := D.core1
  let { RIGHT_ADD_DISTRIB, .. } := D.core2
  let { MOD_AP_CASES, .. } := BModAP
  -- @@SCOPE END
  -- `check (is_forall o concl) o check (fun th -> can (find_term ((=) `ok`)) (concl th) &&
  --                                           can (find_term ((=) `Q`)) (concl th))`
  let okQ : thm → ExceptT String IO Bool := fun th => do
    let okv ← q r"ok:num->bool"
    let ok1 ← if can (find_term (fun u => u == okv)) (concl th) then do
        let qv ← q r"Q:num->bool"
        pure (can (find_term (fun u => u == qv)) (concl th))
      else pure false
    pure (ok1 && is_forall (concl th))

  let SZEMEREDI_UP_PROGRESSION ← prove
   r"!k N W b X a d (ok:num->bool) (Q:num->bool).
        2 <= k /\ 1 <= W /\
        (!y. ok y ==> 2 * y < N /\ Q(W * y + b) /\ W * y + b <= X) /\
        a < N /\ 0 < d /\ d < N /\ (!j. j < k ==> ok((a + j * d) MOD N)) /\
        a < (a + d) MOD N
        ==> 0 < W * ((a + d) MOD N - a) /\
            (W * a + b) + (k - 1) * (W * ((a + d) MOD N - a)) <= X /\
            !j. j < k
                ==> Q((W * a + b) + j * (W * ((a + d) MOD N - a)))"
   (← do
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"k:num", ← q r"N:num", ← q r"a:num", ← q r"d:num"] MOD_AP_CASES) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o CONJUNCT1 o CONJUNCT2) THEN ASM_REWRITE_TAC [] THEN
    ABBREV_TAC (← q r"e = (a + d) MOD N - a") THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"!j. (W * a + b) + j * (W * e) = W * (a + j * e) + b:num")
    (fun th => REWRITE_TAC [th]) THENL
     [GEN_TAC THEN CONV_TAC NUM_RING, ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC [LT_MULT] THEN ASM_ARITH_TAC,
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"k - 1")) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC,
        DISCH_THEN (fun th => tactic_of do pure (SUBST1_TAC (← SYM th)))] THEN
      FIRST_X_ASSUM (fun th => tactic_of do
        let ok ← okQ th
        pure (MP_TAC (← SPEC (← q r"(a + (k - 1) * d) MOD N")
          (← liftExcept (check (fun _ => ok) th))))) THEN
      ANTS_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC, SIMP_TAC []],
      X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"j:num")) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (fun th => tactic_of do pure (SUBST1_TAC (← SYM th))) THEN
      FIRST_X_ASSUM (fun th => tactic_of do
        let ok ← okQ th
        pure (MP_TAC (← SPEC (← q r"(a + j * d) MOD N")
          (← liftExcept (check (fun _ => ok) th))))) THEN
      ANTS_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_ARITH_TAC, SIMP_TAC []]]))

  let SZEMEREDI_DOWN_PROGRESSION ← prove
   r"!k N W b X a d (ok:num->bool) (Q:num->bool).
        2 <= k /\ 1 <= W /\
        (!y. ok y ==> 2 * y < N /\ Q(W * y + b) /\ W * y + b <= X) /\
        a < N /\ 0 < d /\ d < N /\ (!j. j < k ==> ok((a + j * d) MOD N)) /\
        (a + d) MOD N < a
        ==> (a + (k - 1) * d) MOD N + (k - 1) * (a - (a + d) MOD N) = a /\
            0 < W * (a - (a + d) MOD N) /\
            (W * ((a + (k - 1) * d) MOD N) + b) +
            (k - 1) * (W * (a - (a + d) MOD N)) <= X /\
            !j. j < k
                ==> Q((W * ((a + (k - 1) * d) MOD N) + b) +
                          j * (W * (a - (a + d) MOD N)))"
   (← do
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"k:num", ← q r"N:num", ← q r"a:num", ← q r"d:num"] MOD_AP_CASES) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC [] THEN
    ABBREV_TAC (← q r"e = a - (a + d) MOD N") THEN
    ABBREV_TAC (← q r"u = (a + (k - 1) * d) MOD N") THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"u + (k - 1) * e = a") ASSUME_TAC THENL
     [EXPAND_TAC "u" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q r"!j. (W * u + b) + j * (W * e) = W * (u + j * e) + b:num")
    (fun th => REWRITE_TAC [th]) THENL
     [GEN_TAC THEN CONV_TAC NUM_RING, ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!y. ok y ==> W * y + b <= X /\ (Q:num->bool)(W * y + b)")
    ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(ok:num->bool) a") ASSUME_TAC THENL
     [FIRST_X_ASSUM (fun th => tactic_of do
        let ajd ← q r"(a + j * d) MOD N"
        let ok ← if can (find_term (fun u => u == ajd)) (concl th) then do
            let okv ← q r"ok:num->bool"
            pure (can (find_term (fun u => u == okv)) (concl th))
          else pure false
        pure (MP_TAC (← SPEC (← q r"0") (← liftExcept (check (fun _ => ok) th))))) THEN
      ASM_SIMP_TAC [MULT_CLAUSES, ADD_CLAUSES, MOD_LT] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC [LT_MULT] THEN ASM_ARITH_TAC,
      ASM_MESON_TAC [],
      X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"u + j * e = (a + (k - 1 - j) * d) MOD N") SUBST1_TAC THENL
       [FIRST_X_ASSUM (fun th => tactic_of do
          let ajd ← q r"(a + j * d) MOD N"
          let ok ← if can (find_term (fun u => u == ajd)) (concl th) then do
              let ev ← q r"e:num"
              pure (can (find_term (fun u => u == ev)) (concl th))
            else pure false
          pure (MP_TAC (← SPEC (← q r"k - 1 - j")
            (← liftExcept (check (fun _ => ok) th))))) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
        SUBGOAL_THEN (← q r"(k - 1) * e = (k - 1 - j) * e + j * e") MP_TAC THENL
         [REWRITE_TAC [← GSYM RIGHT_ADD_DISTRIB] THEN AP_THM_TAC THEN
          AP_TERM_TAC THEN ASM_ARITH_TAC,
          ALL_TAC] THEN
        UNDISCH_TAC (← q r"u + (k - 1) * e = a") THEN ARITH_TAC,
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"(ok:num->bool) ((a + (k - 1 - j) * d) MOD N)") MP_TAC THENL
       [FIRST_X_ASSUM (fun th => tactic_of do
          let ajd ← q r"(a + j * d) MOD N"
          let ok ← if can (find_term (fun u => u == ajd)) (concl th) then do
              let ev ← q r"e:num"
              pure (!(can (find_term (fun u => u == ev)) (concl th)))
            else pure false
          pure (MATCH_MP_TAC (← liftExcept (check (fun _ => ok) th)))) THEN
        ASM_ARITH_TAC,
        ASM_MESON_TAC []]]))

  -- @@RETURN BEGIN
  return { SZEMEREDI_UP_PROGRESSION, SZEMEREDI_DOWN_PROGRESSION }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- Genuine progressions from pairs mod N.  (szemeredi.ml 6742-6883)          -/
/- ------------------------------------------------------------------------- -/

structure Pairs where
  -- @@FIELDS
  PROGRESSIONS_FROM_PAIRS : thm
  deriving Inhabited

@[nospecialize]
def setupPairs [HolBase] (D : SzemerediDeps) (BModAP : ModAP) (BUpDown : UpDown) :
    ExceptT String IO Pairs := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, SET_TAC, .. } := D
  let { CARD_IMAGE_INJ, CARD_SUBSET, CARD_UNION_LE, EQ_ADD_RCANCEL, EQ_IMP_LE,
        EQ_MULT_LCANCEL, FINITE_NUMSEG_LE, FINITE_NUMSEG_LT, FINITE_PRODUCT,
        FINITE_SUBSET, FINITE_UNION, FORALL_IN_IMAGE, FORALL_PAIR_THM, FST,
        IN_ELIM_PAIR_THM, IN_ELIM_THM, IN_UNION, LE_MULT_RCANCEL, LE_TRANS, .. } := D.core1
  let { PAIR_EQ, SND, SUBSET, .. } := D.core2
  let { MOD_ADD_LCANCEL, MOD_AP_CASES, .. } := BModAP
  let { SZEMEREDI_DOWN_PROGRESSION, SZEMEREDI_UP_PROGRESSION, .. } := BUpDown
  -- @@SCOPE END

  let PROGRESSIONS_FROM_PAIRS ← prove
   r"!k N W b X (ok:num->bool) (Q:num->bool).
        2 <= k /\ 1 <= W /\
        (!y. ok y ==> 2 * y < N /\ Q(W * y + b) /\ W * y + b <= X)
        ==> CARD {(a,d) | a < N /\ 0 < d /\ d < N /\
                          !j. j < k ==> ok((a + j * d) MOD N)} <=
            2 * CARD {(a,d) | 0 < d /\ a + (k - 1) * d <= X /\
                              !j. j < k ==> Q(a + j * d)}"
   (← do
    -- right to left: the three ARITH_RULEs from the last to the first
    let a3 ← ARITH_RULE (← q r"1 <= W ==> ~(W = 0)")
    let a2 ← ARITH_RULE (← q r"a <= t /\ b <= t ==> a + b <= 2 * t")
    let a1 ← ARITH_RULE (← q r"d = 1 * d")
    pure (REPEAT STRIP_TAC THEN
    ABBREV_TAC
     (← q r"S = {(a,d) | a < N /\ 0 < d /\ d < N /\
                   !j. j < k ==> (ok:num->bool)((a + j * d) MOD N)}") THEN
    ABBREV_TAC
     (← q r"Tp = {(a,d) | 0 < d /\ a + (k - 1) * d <= X /\
                    !j. j < k ==> Q(a + j * d)}") THEN
    SUBGOAL_THEN (← q r"FINITE(S:num#num->bool)") ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC (← q r"{x,y | x IN {a:num | a < N} /\ y IN {d:num | d < N}}") THEN
      SIMP_TAC [FINITE_PRODUCT, FINITE_NUMSEG_LT] THEN EXPAND_TAC "S" THEN
      REWRITE_TAC [SUBSET, FORALL_PAIR_THM, IN_ELIM_PAIR_THM, IN_ELIM_THM] THEN
      SIMP_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"FINITE(Tp:num#num->bool)") ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC (← q r"{x,y | x IN {a:num | a <= X} /\ y IN {d:num | d <= X}}") THEN
      SIMP_TAC [FINITE_PRODUCT, FINITE_NUMSEG_LE] THEN EXPAND_TAC "Tp" THEN
      REWRITE_TAC [SUBSET, FORALL_PAIR_THM, IN_ELIM_PAIR_THM, IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"a:num", ← q r"d:num"] THEN STRIP_TAC THEN
      SUBGOAL_THEN (← q r"d <= (k - 1) * d") MP_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [a1] THEN
        REWRITE_TAC [LE_MULT_RCANCEL] THEN ASM_ARITH_TAC,
        ASM_ARITH_TAC],
      ALL_TAC] THEN
    ABBREV_TAC (← q r"S1 = {p | p IN S /\ FST p < (FST p + SND p) MOD N}") THEN
    ABBREV_TAC (← q r"S2 = {p | p IN S /\ (FST p + SND p) MOD N < FST p}") THEN
    SUBGOAL_THEN (← q r"FINITE(S1:num#num->bool) /\ FINITE(S2:num#num->bool)")
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC (← q r"S:num#num->bool") THEN ASM_REWRITE_TAC [] THEN
      MAP_EVERY EXPAND_TAC ["S1", "S2"] THEN SET_TAC [],
      ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC (← q r"CARD(S1:num#num->bool) + CARD(S2:num#num->bool)") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC (← q r"CARD(S1 UNION S2:num#num->bool)") THEN
      ASM_SIMP_TAC [CARD_UNION_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
      ASM_REWRITE_TAC [FINITE_UNION] THEN
      MAP_EVERY EXPAND_TAC ["S1", "S2"] THEN
      REWRITE_TAC [SUBSET, IN_UNION, IN_ELIM_THM, FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"a:num", ← q r"d:num"] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC [FST, SND] THEN
      UNDISCH_TAC (← q r"(a:num,d:num) IN S") THEN EXPAND_TAC "S" THEN
      REWRITE_TAC [IN_ELIM_PAIR_THM] THEN STRIP_TAC THEN
      MP_TAC (← SPECL [← q r"k:num", ← q r"N:num", ← q r"a:num", ← q r"d:num"]
        MOD_AP_CASES) THEN
      ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      DISCH_THEN (MP_TAC o CONJUNCT1) THEN ARITH_TAC,
      ALL_TAC] THEN
    MATCH_MP_TAC a2 THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC
       (← q r"CARD(IMAGE (\p. W * FST p + b, W * ((FST p + SND p) MOD N - FST p))
                   (S1:num#num->bool))") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC [] THEN
        EXPAND_TAC "S1" THEN EXPAND_TAC "S" THEN
        REWRITE_TAC [FORALL_PAIR_THM, IN_ELIM_THM, IN_ELIM_PAIR_THM, FST, SND,
                     PAIR_EQ] THEN
        MAP_EVERY X_GEN_TAC [← q r"a:num", ← q r"d:num", ← q r"a':num", ← q r"d':num"] THEN
        STRIP_TAC THEN
        SUBGOAL_THEN (← q r"a:num = a'") SUBST_ALL_TAC THENL
         [UNDISCH_TAC (← q r"W * a + b = W * a' + b:num") THEN
          REWRITE_TAC [EQ_ADD_RCANCEL, EQ_MULT_LCANCEL] THEN ASM_ARITH_TAC,
          ALL_TAC] THEN
        REWRITE_TAC [] THEN MATCH_MP_TAC MOD_ADD_LCANCEL THEN
        MAP_EVERY EXISTS_TAC [← q r"N:num", ← q r"a':num"] THEN ASM_REWRITE_TAC [] THEN
        UNDISCH_TAC
         (← q r"W * ((a' + d) MOD N - a') = W * ((a' + d') MOD N - a')") THEN
        REWRITE_TAC [EQ_MULT_LCANCEL] THEN ASM_ARITH_TAC,
        MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, FORALL_PAIR_THM] THEN
        EXPAND_TAC "S1" THEN EXPAND_TAC "S" THEN EXPAND_TAC "Tp" THEN
        REWRITE_TAC [IN_ELIM_THM, IN_ELIM_PAIR_THM, FST, SND] THEN
        MAP_EVERY X_GEN_TAC [← q r"a:num", ← q r"d:num"] THEN STRIP_TAC THEN
        MP_TAC (← SPECL [← q r"k:num", ← q r"N:num", ← q r"W:num", ← q r"b:num",
                         ← q r"X:num", ← q r"a:num",
                         ← q r"d:num", ← q r"ok:num->bool", ← q r"Q:num->bool"]
          SZEMEREDI_UP_PROGRESSION) THEN
        ASM_REWRITE_TAC []],
      MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC
       (← q r"CARD(IMAGE (\p. W * ((FST p + (k - 1) * SND p) MOD N) + b,
                        W * (FST p - (FST p + SND p) MOD N))
                   (S2:num#num->bool))") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC [] THEN
        EXPAND_TAC "S2" THEN EXPAND_TAC "S" THEN
        REWRITE_TAC [FORALL_PAIR_THM, IN_ELIM_THM, IN_ELIM_PAIR_THM, FST, SND,
                     PAIR_EQ] THEN
        MAP_EVERY X_GEN_TAC [← q r"a:num", ← q r"d:num", ← q r"a':num", ← q r"d':num"] THEN
        STRIP_TAC THEN
        MP_TAC (← SPECL [← q r"k:num", ← q r"N:num", ← q r"W:num", ← q r"b:num",
                         ← q r"X:num", ← q r"a:num",
                         ← q r"d:num", ← q r"ok:num->bool", ← q r"Q:num->bool"]
          SZEMEREDI_DOWN_PROGRESSION) THEN
        MP_TAC (← SPECL [← q r"k:num", ← q r"N:num", ← q r"W:num", ← q r"b:num",
                         ← q r"X:num", ← q r"a':num",
                         ← q r"d':num", ← q r"ok:num->bool", ← q r"Q:num->bool"]
          SZEMEREDI_DOWN_PROGRESSION) THEN
        ASM_REWRITE_TAC [] THEN
        DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN
        DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN
        SUBGOAL_THEN
         (← q r"(a + (k - 1) * d) MOD N = (a' + (k - 1) * d') MOD N /\
          a - (a + d) MOD N = a' - (a' + d') MOD N")
        STRIP_ASSUME_TAC THENL
         [MAP_EVERY UNDISCH_TAC
           [← q r"W * (a + (k - 1) * d) MOD N + b =
             W * (a' + (k - 1) * d') MOD N + b",
            ← q r"W * (a - (a + d) MOD N) = W * (a' - (a' + d') MOD N)"] THEN
          REWRITE_TAC [EQ_ADD_RCANCEL, EQ_MULT_LCANCEL] THEN
          ASM_SIMP_TAC [a3],
          ALL_TAC] THEN
        SUBGOAL_THEN (← q r"a:num = a'") SUBST_ALL_TAC THENL
         [MAP_EVERY UNDISCH_TAC
           [← q r"(a + (k - 1) * d) MOD N + (k - 1) * (a - (a + d) MOD N) = a",
            ← q r"(a' + (k - 1) * d') MOD N + (k - 1) * (a' - (a' + d') MOD N) =
             a'"] THEN
          ASM_REWRITE_TAC [] THEN ARITH_TAC,
          ALL_TAC] THEN
        REWRITE_TAC [] THEN MATCH_MP_TAC MOD_ADD_LCANCEL THEN
        MAP_EVERY EXISTS_TAC [← q r"N:num", ← q r"a':num"] THEN ASM_REWRITE_TAC [] THEN
        ASM_ARITH_TAC,
        MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, FORALL_PAIR_THM] THEN
        EXPAND_TAC "S2" THEN EXPAND_TAC "S" THEN EXPAND_TAC "Tp" THEN
        REWRITE_TAC [IN_ELIM_THM, IN_ELIM_PAIR_THM, FST, SND] THEN
        MAP_EVERY X_GEN_TAC [← q r"a:num", ← q r"d:num"] THEN STRIP_TAC THEN
        MP_TAC (← SPECL [← q r"k:num", ← q r"N:num", ← q r"W:num", ← q r"b:num",
                         ← q r"X:num", ← q r"a:num",
                         ← q r"d:num", ← q r"ok:num->bool", ← q r"Q:num->bool"]
          SZEMEREDI_DOWN_PROGRESSION) THEN
        ASM_SIMP_TAC []]]))

  -- @@RETURN BEGIN
  return { PROGRESSIONS_FROM_PAIRS }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- Szemeredi's theorem: counting, finite and density forms; Roth.            -/
/- (szemeredi.ml 6884-7092)                                                  -/
/- ------------------------------------------------------------------------- -/

structure SzemerediThm where
  -- @@FIELDS
  SZEMEREDI_COUNT : thm
  SZEMEREDI : thm
  ROTH : thm
  SZEMEREDI_DENSITY : thm
  deriving Inhabited

@[nospecialize]
def setupSzemerediThm [HolBase] (D : SzemerediDeps) (BFiniteMeans : FiniteMeans) (BLemma8 : Lemma8) (BWeightedDefs : WeightedDefs) (BWeightedThm : WeightedThm) (BModAP : ModAP) (BPairs : Pairs) :
    ExceptT String IO SzemerediThm := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, REAL_ARITH,
        REAL_ARITH_TAC, SET_TAC, TAUT, .. } := D
  let { ADD_CLAUSES, ARITH, BERTRAND, CARD_CLAUSES, CARD_IMAGE_INJ, CARD_NUMSEG_LT,
        EQ_TRANS, EXISTS_PAIR_THM, EXTENSION, FINITE_NUMSEG, FINITE_NUMSEG_LT,
        FINITE_SUBSET, FORALL_PAIR_THM, INTER_SUBSET, IN_ELIM_PAIR_THM, IN_ELIM_THM,
        IN_IMAGE, IN_INTER, IN_NUMSEG, LE_REFL, MEMBER_NOT_EMPTY, MONO_EXISTS,
        MULT_CLAUSES, .. } := D.core1
  let { REAL_ARCH_SIMPLE, REAL_LE_LDIV_EQ, REAL_LE_LMUL, REAL_LE_RDIV_EQ, REAL_LE_RMUL,
        REAL_LE_TRANS, REAL_LT_IMP_LE, REAL_LT_MUL, REAL_LT_REFL, REAL_MUL_ASSOC,
        REAL_MUL_RID, REAL_MUL_SYM, REAL_NOT_LE, REAL_OF_NUM_LE, REAL_OF_NUM_LT,
        REAL_OF_NUM_MUL, REAL_POS, REAL_POW_2, REAL_POW_LE, REAL_POW_LE2, REAL_POW_LT,
        REAL_POW_ONE, SUBSET, SUB_ADD, .. } := D.core2
  let { fmean, .. } := BFiniteMeans
  let { CARD_RESTRICT_SUM, .. } := BLemma8
  let { weighted_szemeredi, .. } := BWeightedDefs
  let { WEIGHTED_SZEMEREDI, .. } := BWeightedThm
  let { AP_COUNT_NONTRIVIAL, .. } := BModAP
  let { PROGRESSIONS_FROM_PAIRS, .. } := BPairs
  -- @@SCOPE END

  let SZEMEREDI_COUNT ← prove
   r"!k delta.
        2 <= k /\ &0 < delta
        ==> ?c N0. &0 < c /\
                   !N A. N0 <= N /\ A SUBSET 1..N /\ delta * &N <= &(CARD A)
                         ==> c * &N pow 2 <=
                             &(CARD {(a,d) | 0 < d /\
                                             !j. j < k ==> a + j * d IN A})"
   (← do
    let r1 ← REAL_ARITH (← q r"&4 * x pow 2 = (&2 * x) pow 2")
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← SPEC (← q r"k:num") WEIGHTED_SZEMEREDI) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [weighted_szemeredi] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"delta / &4")) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"csz:real") (X_CHOOSE_THEN (← q r"P1:num")
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "wsz")))) THEN
    X_CHOOSE_TAC (← q r"R1:num") (← SPEC (← q r"&2 / csz") REAL_ARCH_SIMPLE) THEN
    EXISTS_TAC (← q r"csz:real") THEN EXISTS_TAC (← q r"P1 + R1 + 1") THEN
    ASM_REWRITE_TAC [] THEN
    MAP_EVERY X_GEN_TAC [← q r"N:num", ← q r"A:num->bool"] THEN STRIP_TAC THEN
    MP_TAC (← SPEC (← q r"2 * N") BERTRAND) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"P:num") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"!x. x IN A ==> 1 <= x /\ x <= N") (LABEL_TAC "Ab") THENL
     [UNDISCH_TAC (← q r"A SUBSET 1..N") THEN SIMP_TAC [SUBSET, IN_NUMSEG],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"FINITE(A:num->bool)") ASSUME_TAC THENL
     [ASM_MESON_TAC [FINITE_SUBSET, FINITE_NUMSEG], ALL_TAC] THEN
    ABBREV_TAC (← q r"f = \y. if y + 1 IN A then &1 else &0") THEN
    SUBGOAL_THEN (← q r"!y. y < P ==> &0 <= (f:num->real) y /\
      f y <= &1") ASSUME_TAC THENL
     [EXPAND_TAC "f" THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
      REAL_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"sum {y:num | y < P} f = &(CARD(A:num->bool))") ASSUME_TAC THENL
     [EXPAND_TAC "f" THEN
      SIMP_TAC [← GSYM CARD_RESTRICT_SUM, FINITE_NUMSEG_LT] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC
       (← q r"CARD (IMAGE (\y. y + 1) {y | y IN {y:num | y < P} /\ y + 1 IN A})") THEN
      CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
        CONJ_TAC THENL [ARITH_TAC, ALL_TAC] THEN
        MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{y:num | y < P}") THEN
        REWRITE_TAC [FINITE_NUMSEG_LT] THEN SET_TAC [],
        AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN
        X_GEN_TAC (← q r"x:num") THEN EQ_TAC THENL
         [STRIP_TAC THEN ASM_REWRITE_TAC [],
          DISCH_TAC THEN EXISTS_TAC (← q r"x - 1") THEN
          SUBGOAL_THEN (← q r"1 <= x /\ x <= N") STRIP_ASSUME_TAC THENL
           [ASM_MESON_TAC [], ALL_TAC] THEN
          ASM_SIMP_TAC [SUB_ADD] THEN ASM_ARITH_TAC]],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"delta / &4 <= fmean {y:num | y < P} f") ASSUME_TAC THENL
     [ASM_REWRITE_TAC [fmean, CARD_NUMSEG_LT] THEN
      SUBGOAL_THEN (← q r"&0 < &P") ASSUME_TAC THENL
       [REWRITE_TAC [REAL_OF_NUM_LT] THEN ASM_ARITH_TAC, ALL_TAC] THEN
      ASM_SIMP_TAC [REAL_LE_RDIV_EQ] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"delta * &N") THEN
      ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"&P <= &4 * &N") MP_TAC THENL
       [REWRITE_TAC [REAL_OF_NUM_MUL, REAL_OF_NUM_LE] THEN ASM_ARITH_TAC,
        ALL_TAC] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN (← q r"delta * &P <= delta * (&4 * &N)") MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC [REAL_LT_IMP_LE],
        REAL_ARITH_TAC],
      ALL_TAC] THEN
    REMOVE_THEN "wsz" (MP_TAC o SPECL [← q r"P:num", ← q r"f:num->real"]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC, DISCH_TAC] THEN
    MP_TAC (← SPECL [← q r"k:num", ← q r"P:num", ← q r"f:num->real", ← q r"&1"]
      AP_COUNT_NONTRIVIAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [REAL_POW_ONE, REAL_MUL_RID] THEN DISCH_TAC THEN
    MP_TAC (← SPECL [← q r"k:num", ← q r"P:num", ← q r"1", ← q r"1", ← q r"N:num",
                     ← q r"\y. &0 < (f:num->real) y",
                     ← q r"\x:num. x IN A"] PROGRESSIONS_FROM_PAIRS) THEN
    REWRITE_TAC [MULT_CLAUSES] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC [LE_REFL] THEN X_GEN_TAC (← q r"y:num") THEN EXPAND_TAC "f" THEN
      COND_CASES_TAC THEN REWRITE_TAC [REAL_LT_REFL] THEN
      SUBGOAL_THEN (← q r"1 <= y + 1 /\ y + 1 <= N") MP_TAC THENL
       [ASM_MESON_TAC [], ASM_ARITH_TAC],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"{(a,d) | 0 < d /\ a + (k - 1) * d <= N /\ !j. j < k ==> a + j * d IN A} =
      {(a,d) | 0 < d /\ !j. j < k ==> a + j * d IN A}")
    SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, FORALL_PAIR_THM, IN_ELIM_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"a:num", ← q r"d:num"] THEN EQ_TAC THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"k - 1")) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      DISCH_THEN (fun th => FIRST_X_ASSUM (MP_TAC o C MATCH_MP th)) THEN
      SIMP_TAC [],
      ALL_TAC] THEN
    DISCH_THEN (ASSUME_TAC o GEN_REWRITE_RULE RAND_CONV [← GSYM REAL_OF_NUM_MUL] o
               GEN_REWRITE_RULE I [← GSYM REAL_OF_NUM_LE]) THEN
    ABBREV_TAC
     (← q r"ap = fmean {a | a < P}
             (\a. fmean {d | d < P}
                    (\d. product {j | j < k} (\j. f((a + j * d) MOD P))))") THEN
    ABBREV_TAC
     (← q r"sp = &(CARD {(a,d) | a < P /\ 0 < d /\ d < P /\
                           !j. j < k ==>
                             &0 < (f:num->real)((a + j * d) MOD P)})") THEN
    ABBREV_TAC
     (← q r"tc = &(CARD {(a,d) | 0 < d /\ !j. j < k ==> a + j * d IN A})") THEN
    SUBGOAL_THEN (← q r"csz * &P pow 2 <= &P pow 2 * ap") ASSUME_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC [REAL_POW_LE, REAL_POS],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"&2 * &P <= csz * &P pow 2") ASSUME_TAC THENL
     [REWRITE_TAC [REAL_POW_2, REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC [REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"csz * &R1") THEN
      CONJ_TAC THENL
       [ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
        ASM_SIMP_TAC [← GSYM REAL_LE_LDIV_EQ],
        MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_SIMP_TAC [REAL_LT_IMP_LE, REAL_OF_NUM_LE] THEN ASM_ARITH_TAC],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"&4 * &N pow 2 <= &P pow 2") ASSUME_TAC THENL
     [REWRITE_TAC [r1] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN
      REWRITE_TAC [REAL_OF_NUM_MUL, REAL_OF_NUM_LE, REAL_POS] THEN
      ASM_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"csz * (&4 * &N pow 2) <= csz * &P pow 2") ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC [REAL_LT_IMP_LE], ALL_TAC] THEN
    ASM_REAL_ARITH_TAC))

  let SZEMEREDI ← prove
   r"!k delta.
        &0 < delta
        ==> ?N0. !N A. N0 <= N /\ A SUBSET 1..N /\ delta * &N <= &(CARD A)
                       ==> ?a d. 0 < d /\ !j. j < k ==> a + j * d IN A"
   (← do
    pure (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"2 <= k") THENL
     [MP_TAC (← SPECL [← q r"k:num", ← q r"delta:real"] SZEMEREDI_COUNT) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"c:real") (X_CHOOSE_THEN (← q r"N0:num")
        STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC (← q r"N0 + 1") THEN
      MAP_EVERY X_GEN_TAC [← q r"N:num", ← q r"A:num->bool"] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [← q r"N:num", ← q r"A:num->bool"]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC, ALL_TAC] THEN
      ABBREV_TAC (← q r"Z = {(a,d) | 0 < d /\ !j. j < k ==> a + j * d IN A}") THEN
      ASM_CASES_TAC (← q r"Z:num#num->bool = {}") THENL
       [ASM_REWRITE_TAC [CARD_CLAUSES] THEN
        MATCH_MP_TAC (← TAUT (← q r"~p ==> p ==> q")) THEN REWRITE_TAC [REAL_NOT_LE] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC [REAL_OF_NUM_LT] THEN
        ASM_ARITH_TAC,
        DISCH_THEN (K ALL_TAC : thm → tactic) THEN
        UNDISCH_TAC (← q r"~(Z:num#num->bool = {})") THEN
        EXPAND_TAC "Z" THEN
        REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, EXISTS_PAIR_THM, IN_ELIM_PAIR_THM]],
      EXISTS_TAC (← q r"1") THEN MAP_EVERY X_GEN_TAC [← q r"N:num", ← q r"A:num->bool"] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN (← q r"~(A:num->bool = {})") MP_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC (← q r"delta * &N <= &(CARD({}:num->bool))") THEN
        REWRITE_TAC [CARD_CLAUSES, REAL_NOT_LE] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC [REAL_OF_NUM_LT] THEN
        ASM_ARITH_TAC,
        ALL_TAC] THEN
      REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"a:num")) THEN
      MAP_EVERY EXISTS_TAC [← q r"a:num", ← q r"1"] THEN REWRITE_TAC [ARITH] THEN
      X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"j = 0") SUBST1_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      ASM_REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES]]))

  let ROTH ← prove
   r"!delta.
        &0 < delta
        ==> ?N0. !N A. N0 <= N /\ A SUBSET 1..N /\ delta * &N <= &(CARD A)
                       ==> ?a d. 0 < d /\ a IN A /\ a + d IN A /\
                                 a + 2 * d IN A"
   (← do
    pure (GEN_TAC THEN DISCH_TAC THEN
    MP_TAC (← SPECL [← q r"3", ← q r"delta:real"] SZEMEREDI) THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"N0:num") THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPECL [← q r"N:num",
      ← q r"A:num->bool"]) THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"a:num") THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"d:num") THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (fun th => tactic_of do
      pure (MP_TAC (← SPEC (← q r"0") th) THEN MP_TAC (← SPEC (← q r"1") th) THEN
        MP_TAC (← SPEC (← q r"2") th)))) THEN
    ASM_REWRITE_TAC [ARITH, MULT_CLAUSES, ADD_CLAUSES] THEN SIMP_TAC []))

  let SZEMEREDI_DENSITY ← prove
   r"!A k delta.
        &0 < delta /\
        (!N0. ?N. N0 <= N /\ delta * &N <= &(CARD(A INTER (1..N))))
        ==> ?a d. 0 < d /\ !j. j < k ==> a + j * d IN A"
   (← do
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"k:num", ← q r"delta:real"] SZEMEREDI) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"N0:num")) THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"N:num") STRIP_ASSUME_TAC o SPEC (← q r"N0:num")) THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"N:num", ← q r"A INTER (1..N)"]) THEN
    ASM_REWRITE_TAC [INTER_SUBSET] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN SIMP_TAC [IN_INTER]))

  -- @@RETURN BEGIN
  return { SZEMEREDI_COUNT, SZEMEREDI, ROTH, SZEMEREDI_DENSITY }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- Van der Waerden's theorem; shifts of cubes.  (szemeredi.ml 7093-7205)     -/
/- ------------------------------------------------------------------------- -/

structure VdW where
  -- @@FIELDS
  VAN_DER_WAERDEN : thm
  FMEAN_SHIFT_HJ_CUBE : thm
  HJ_DENSITY_SHIFT_MEAN : thm
  deriving Inhabited

@[nospecialize]
def setupVdW [HolBase] (D : SzemerediDeps) (BFiniteMeans : FiniteMeans) (BWords : Words) (BDensities : Densities) (BDKTCor5 : DKTCor5) (BModAP : ModAP) (BSzemerediThm : SzemerediThm) :
    ExceptT String IO VdW := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, SET_TAC, .. } := D
  let { ADD_CLAUSES, ADD_SYM, CARD_NUMSEG_1, CARD_NUMSEG_LT, EQ_TRANS, FINITE_NUMSEG,
        FINITE_NUMSEG_LT, FUN_EQ_THM, IN_ELIM_THM, LE_REFL, MEMBER_NOT_EMPTY,
        MOD_LT_EQ, MONO_EXISTS, MULT_CLAUSES, .. } := D.core1
  let { NOT_LT, REAL_LE_LDIV_EQ, REAL_LT_INV_EQ, REAL_MUL_SYM, REAL_OF_NUM_LT, SUBSET,
        SUM_INJECTION, o_DEF, real_div, .. } := D.core2
  let { FMEAN_CONST, FMEAN_EQ, fmean, .. } := BFiniteMeans
  let { FINITE_HJ_CUBE, HJ_CUBE_NONEMPTY, IN_HJ_CUBE, .. } := BWords
  let { CARD_PIGEONHOLE, HJ_DENSITY_CARD, hj_density, .. } := BDensities
  let { FMEAN_SWAP2, .. } := BDKTCor5
  let { MOD_ADD_LCANCEL, .. } := BModAP
  let { SZEMEREDI, .. } := BSzemerediThm
  -- @@SCOPE END

  let VAN_DER_WAERDEN ← prove
   r"!k r. 1 <= r
         ==> ?N. !col. (!n. col n < r)
                       ==> ?a d. 0 < d /\
                                 !j. j < k ==> a + j * d IN 1..N /\
                                               col(a + j * d) = col a"
   (← do
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"k:num", ← q r"inv(&r)"] SZEMEREDI) THEN
    ANTS_TAC THENL
     [REWRITE_TAC [REAL_LT_INV_EQ, REAL_OF_NUM_LT] THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"N0:num")) THEN EXISTS_TAC (← q r"N0:num") THEN
    X_GEN_TAC (← q r"col:num->num") THEN DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"col:num->num", ← q r"1..N0", ← q r"{c:num | c < r}"]
      CARD_PIGEONHOLE) THEN
    REWRITE_TAC [FINITE_NUMSEG, FINITE_NUMSEG_LT, IN_ELIM_THM, CARD_NUMSEG_LT,
                 CARD_NUMSEG_1] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, IN_ELIM_THM] THEN
      EXISTS_TAC (← q r"0") THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"c:num") STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o SPECL
     [← q r"N0:num", ← q r"{x | x IN 1..N0 /\ (col:num->num) x = c}"]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC [LE_REFL, SUBSET, IN_ELIM_THM] THEN
      CONJ_TAC THENL [SIMP_TAC [], ALL_TAC] THEN
      ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN REWRITE_TAC [← GSYM real_div] THEN
      SUBGOAL_THEN (← q r"&0 < &r") ASSUME_TAC THENL
       [REWRITE_TAC [REAL_OF_NUM_LT] THEN ASM_ARITH_TAC, ALL_TAC] THEN
      ASM_SIMP_TAC [REAL_LE_LDIV_EQ] THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"a:num") THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"d:num") THEN
    REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"0 < k") ASSUME_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q r"j:num")) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"0")) THEN
    ASM_SIMP_TAC [MULT_CLAUSES, ADD_CLAUSES]))

  let FMEAN_SHIFT_HJ_CUBE ← prove
   r"!Q d (s:num->num) (g:(num->num)->real).
        1 <= Q
        ==> fmean (hj_cube Q d)
              (\t. g(\i. if i < d then (t i + s i) MOD Q else 0)) =
            fmean (hj_cube Q d) g"
   (← do
    -- right to left: the second ARITH_RULE, then the first
    let a2 ← ARITH_RULE (← q r"d <= i ==> ~(i < d:num)")
    let a1 ← ARITH_RULE (← q r"1 <= Q ==> ~(Q = 0)")
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [fmean] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC (← ISPECL
     [← q r"g:(num->num)->real",
      ← q r"\t:num->num. \i. if i < d then (t i + (s:num->num) i) MOD Q else 0",
      ← q r"hj_cube Q d"] SUM_INJECTION) THEN
    REWRITE_TAC [o_DEF, FINITE_HJ_CUBE] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC [IN_HJ_CUBE] THEN CONJ_TAC THENL
     [X_GEN_TAC (← q r"t:num->num") THEN STRIP_TAC THEN CONJ_TAC THEN
      X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THENL
       [ASM_SIMP_TAC [MOD_LT_EQ, a1],
        ASM_SIMP_TAC [a2]],
      MAP_EVERY X_GEN_TAC [← q r"t:num->num", ← q r"t':num->num"] THEN STRIP_TAC THEN
      REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"i:num") THEN
      ASM_CASES_TAC (← q r"i < d:num") THENL
       [FIRST_X_ASSUM (MP_TAC o C AP_THM (← q r"i:num")) THEN ASM_REWRITE_TAC [] THEN
        ONCE_REWRITE_TAC [ADD_SYM] THEN DISCH_TAC THEN
        MATCH_MP_TAC MOD_ADD_LCANCEL THEN
        MAP_EVERY EXISTS_TAC [← q r"Q:num", ← q r"(s:num->num) i"] THEN
        ASM_SIMP_TAC [],
        RULE_ASSUM_TAC (REWRITE_RULE [NOT_LT]) THEN ASM_SIMP_TAC []]]))

  let HJ_DENSITY_SHIFT_MEAN ← prove
   r"!K n Q d (s:(num->num)->num->num) (A:(num->num)->bool).
        1 <= K /\ 1 <= Q /\ A SUBSET hj_cube Q d
        ==> fmean (hj_cube Q d)
              (\t. hj_density K n
                     {x | (\i. if i < d then (t i + s x i) MOD Q else 0)
                          IN A}) =
            &(CARD A) / &(Q EXP d)"
   (← do
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [hj_density, IN_ELIM_THM] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     (← q r"fmean (hj_cube K n)
        (\x. fmean (hj_cube Q d)
               (\t. if (\i. if i < d then (t i + s x i) MOD Q else 0) IN A
                    then &1 else &0))") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FMEAN_SWAP2 THEN REWRITE_TAC [FINITE_HJ_CUBE], ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     (← q r"fmean (hj_cube K n)
        (\x:num->num. &(CARD(A:(num->num)->bool)) / &(Q EXP d))") THEN
    CONJ_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC FMEAN_CONST THEN
        ASM_SIMP_TAC [FINITE_HJ_CUBE, HJ_CUBE_NONEMPTY]] THEN
    MATCH_MP_TAC FMEAN_EQ THEN X_GEN_TAC (← q r"x:num->num") THEN DISCH_TAC THEN
    REWRITE_TAC [] THEN
    MP_TAC (← ISPECL [← q r"Q:num", ← q r"d:num", ← q r"(s:(num->num)->num->num) x",
                      ← q r"\y:num->num. if y IN A then &1 else &0"]
                       FMEAN_SHIFT_HJ_CUBE) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [← GSYM hj_density, HJ_DENSITY_CARD] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM SET_TAC []))

  -- @@RETURN BEGIN
  return { VAN_DER_WAERDEN, FMEAN_SHIFT_HJ_CUBE, HJ_DENSITY_SHIFT_MEAN }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- Multidimensional Szemeredi, Gallai-Witt and corners.                      -/
/- (szemeredi.ml 7206-7466)                                                  -/
/- ------------------------------------------------------------------------- -/

structure Multidim where
  -- @@FIELDS
  MULTIDIM_SZEMEREDI : thm
  GALLAI_WITT : thm
  CORNERS : thm
  deriving Inhabited

@[nospecialize]
def setupMultidim [HolBase] (D : SzemerediDeps) (BWords : Words) (BLines : Lines) (BDensities : Densities) (BDensityHJ : DensityHJ) (BDensityHJThm : DensityHJThm) (BWeightedDefs : WeightedDefs) (BVdW : VdW) :
    ExceptT String IO Multidim := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON, MOD_DOWN_CONV,
        REAL_ARITH, REAL_FIELD, SET_TAC, .. } := D
  let { ADD_ASSOC, ADD_CLAUSES, ADD_EQ_0, ADD_SUB, ARITH, CARD_IMAGE_INJ,
        CARD_NUMSEG_LT, EQ_TRANS, FINITE_IMAGE, FINITE_NUMSEG_LT, FINITE_PRODUCT,
        FINITE_SUBSET, FORALL_IN_IMAGE, FORALL_PAIR_THM, FUN_EQ_THM, IN_ELIM_PAIR_THM,
        IN_ELIM_THM, IN_IMAGE, LET_TRANS, LE_MULT2, LE_REFL, MEMBER_NOT_EMPTY, MOD_LT,
        MONO_EXISTS, MULT_CLAUSES, .. } := D.core1
  let { NOT_LT, PAIR, REAL_EQ_IMP_LE, REAL_LE_LDIV_EQ, REAL_LE_RDIV_EQ, REAL_LE_TRANS,
        REAL_LT_DIV, REAL_LT_INV_EQ, REAL_LT_MUL, REAL_MUL_SYM, REAL_OF_NUM_LT,
        REAL_OF_NUM_MUL, REAL_OF_NUM_POW, REAL_POW_LT, REAL_POW_MUL, SUBSET,
        SUBSET_TRANS, num_FINITE, real_div, .. } := D.core2
  let { CARD_HJ_CUBE, FINITE_HJ_CUBE, HJ_CUBE_MONO, HJ_CUBE_NONEMPTY, IN_HJ_CUBE, .. } := BWords
  let { hj_has_line, .. } := BLines
  let { CARD_PIGEONHOLE, FMEAN_EXISTS_GE, .. } := BDensities
  let { density_hales_jewett, .. } := BDensityHJ
  let { DENSITY_HALES_JEWETT, .. } := BDensityHJThm
  let { HJ_LINE_WILDCARDS, NSUM_HJ_LINE_POINT_GEN, .. } := BWeightedDefs
  let { HJ_DENSITY_SHIFT_MEAN, .. } := BVdW
  -- @@SCOPE END

  let MULTIDIM_SZEMEREDI ← prove
   r"!d k (v:num->num->num) delta.
        &0 < delta /\ (!j i. j < k /\ d <= i ==> v j i = 0)
        ==> ?M0. !M A. M0 <= M /\ A SUBSET hj_cube M d /\
                       delta * &(M EXP d) <= &(CARD A)
                       ==> ?a lm. 0 < lm /\
                                   !j. j < k ==> (\i. a i + lm * v j i) IN A"
   (← do
    -- right to left: the seven rules (one an inline prove) from the last
    -- to the first
    let m7 ← MESON []
      (← q r"!x y:num->num. x = y ==> x IN (A:(num->num)->bool) ==> y IN A")
    let a6 ← ARITH_RULE (← q r"j + 1 < k + 1 <=> j < k")
    let a5 ← ARITH_RULE (← q r"0 < k + 1")
    let a4 ← ARITH_RULE (← q r"1 <= k + 1")
    let p3 ← prove
      r"!f:A->num s. FINITE s ==> ?a. !x. x IN s ==> f x <= a"
      (← do
       pure (REPEAT STRIP_TAC THEN
       MP_TAC (← ISPECL [← q r"f:A->num", ← q r"s:A->bool"] FINITE_IMAGE) THEN
       ASM_REWRITE_TAC [num_FINITE, FORALL_IN_IMAGE]))
    let r2 ← REAL_ARITH (← q r"&0 < &2")
    let a1 ← ARITH_RULE (← q r"1 <= k + 1")
    pure (REPEAT STRIP_TAC THEN
    ABBREV_TAC
     (← q r"u = \j:num. if j = 0 then (\i:num. 0) else (v:num->num->num) (j - 1)") THEN
    MP_TAC (← SPEC (← q r"k + 1") DENSITY_HALES_JEWETT) THEN
    REWRITE_TAC [a1, density_hales_jewett] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"delta / &2 pow d")) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_SIMP_TAC [REAL_POW_LT, r2],
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"n:num") (LABEL_TAC "density_hales_jewett")) THEN
    MP_TAC (← ISPECL [← q r"\p:num#num. (v:num->num->num) (FST p) (SND p)",
                      ← q r"{j,i | j IN {j:num | j < k} /\ i IN {i:num | i < d}}"]
      p3) THEN
    SIMP_TAC [FINITE_PRODUCT, FINITE_NUMSEG_LT, FORALL_PAIR_THM,
              IN_ELIM_PAIR_THM, IN_ELIM_THM] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"V:num")) THEN
    EXISTS_TAC (← q r"n * V + 1") THEN
    MAP_EVERY X_GEN_TAC [← q r"M:num", ← q r"A:(num->num)->bool"] THEN STRIP_TAC THEN
    ABBREV_TAC (← q r"Q = 2 * M") THEN
    SUBGOAL_THEN (← q r"1 <= M /\ 1 <= Q /\ M <= Q") STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "Q" THEN ASM_ARITH_TAC, ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(A:(num->num)->bool) SUBSET hj_cube Q d") ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC (← q r"hj_cube M d") THEN
      ASM_SIMP_TAC [HJ_CUBE_MONO],
      ALL_TAC] THEN
    ABBREV_TAC
     (← q r"s = \x:num->num. \i. nsum {r | r < n} (\r. (u:num->num->num) (x r) i)") THEN
    MP_TAC (← ISPECL [← q r"k + 1", ← q r"n:num", ← q r"Q:num", ← q r"d:num",
                      ← q r"s:(num->num)->num->num", ← q r"A:(num->num)->bool"]
      HJ_DENSITY_SHIFT_MEAN) THEN
    ASM_REWRITE_TAC [a4] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     (← q r"delta / &2 pow d <= &(CARD(A:(num->num)->bool)) / &(Q EXP d)")
    ASSUME_TAC THENL
     [EXPAND_TAC "Q" THEN
      REWRITE_TAC [← GSYM REAL_OF_NUM_MUL, ← GSYM REAL_OF_NUM_POW, REAL_POW_MUL] THEN
      SUBGOAL_THEN (← q r"&0 < &2 pow d /\ &0 < &M pow d") STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN
        REWRITE_TAC [REAL_OF_NUM_LT] THEN ASM_ARITH_TAC,
        ALL_TAC] THEN
      ASM_SIMP_TAC [REAL_LE_RDIV_EQ, REAL_LT_MUL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"delta * &(M EXP d)") THEN
      ASM_REWRITE_TAC [← GSYM REAL_OF_NUM_POW] THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      UNDISCH_TAC (← q r"&0 < &2 pow d") THEN CONV_TAC REAL_FIELD,
      ALL_TAC] THEN
    MP_TAC (← ISPECL
     [← q r"hj_cube Q d",
      ← q r"\t. hj_density (k + 1) n
             {x | (\i. if i < d
                        then ((t:num->num) i +
                          (s:(num->num)->num->num) x i) MOD Q
                        else 0) IN (A:(num->num)->bool)}",
      ← q r"delta / &2 pow d"] FMEAN_EXISTS_GE) THEN
    ASM_SIMP_TAC [FINITE_HJ_CUBE, HJ_CUBE_NONEMPTY] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"t:num->num") STRIP_ASSUME_TAC) THEN
    REMOVE_THEN "density_hales_jewett" (MP_TAC o SPECL
     [← q r"n:num",
      ← q r"{x | (\i. if i < d
                 then ((t:num->num) i + (s:(num->num)->num->num) x i) MOD Q
                 else 0) IN (A:(num->num)->bool)}"]) THEN
    ASM_REWRITE_TAC [LE_REFL, hj_has_line, IN_ELIM_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"l:num->num") (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "pts"))) THEN
    ABBREV_TAC (← q r"w = CARD {r | r < n /\ (l:num->num) r = k + 1}") THEN
    SUBGOAL_THEN (← q r"0 < w /\ w <= n") STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "w" THEN MATCH_MP_TAC HJ_LINE_WILDCARDS THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    ABBREV_TAC
     (← q r"s0 = \i. nsum {r | r < n}
                 (\r. if (l:num->num) r < k + 1
                      then (u:num->num->num) (l r) i else 0)") THEN
    SUBGOAL_THEN
     (← q r"!a i. (s:(num->num)->num->num) (hj_line_point (k + 1) l a) i =
            (s0:num->num) i + w * (u:num->num->num) a i")
    ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN MAP_EVERY EXPAND_TAC ["s", "s0", "w"] THEN
      REWRITE_TAC [] THEN
      MP_TAC (← ISPECL [← q r"k + 1", ← q r"n:num", ← q r"l:num->num",
                        ← q r"\x. (u:num->num->num) x i",
                        ← q r"a:num"] NSUM_HJ_LINE_POINT_GEN) THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(u:num->num->num) 0 = (\i. 0) /\ !j. u (j + 1) = v j")
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "u" THEN REWRITE_TAC [ADD_EQ_0, ARITH, ADD_SUB], ALL_TAC] THEN
    USE_THEN "pts" (MP_TAC o REWRITE_RULE [a5] o
      SPEC (← q r"0")) THEN
    ASM_REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     (← q r"!i. i < d ==> ((t:num->num) i + (s0:num->num) i) MOD Q < M")
    ASSUME_TAC THENL
     [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN
      SUBGOAL_THEN
       (← q r"(\i. if i < d then ((t:num->num) i + (s0:num->num) i) MOD Q else 0)
        IN hj_cube M d")
      MP_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
      REWRITE_TAC [IN_HJ_CUBE] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"i:num") o CONJUNCT1) THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    EXISTS_TAC
     (← q r"\i. if i < d then ((t:num->num) i + (s0:num->num) i) MOD Q else 0") THEN
    EXISTS_TAC (← q r"w:num") THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN
    USE_THEN "pts" (MP_TAC o
      REWRITE_RULE [a6] o SPEC (← q r"j + 1")) THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC m7 THEN
    REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"i:num") THEN
    ASM_CASES_TAC (← q r"i < d:num") THEN ASM_REWRITE_TAC [] THENL
     [ALL_TAC,
      FIRST_X_ASSUM (fun th => tactic_of do
        let vv ← q r"v:num->num->num"
        let ok ← if can (find_term (fun u => u == vv)) (concl th) then do
            let dv ← q r"d:num"
            if can (find_term (fun u => u == dv)) (concl th) && is_forall (concl th) then do
              let bigV ← q r"V:num"
              pure (!(can (find_term (fun u => u == bigV)) (concl th)))
            else pure false
          else pure false
        pure (MP_TAC (← SPECL [← q r"j:num", ← q r"i:num"]
          (← liftExcept (check (fun _ => ok) th))))) THEN
      ASM_REWRITE_TAC [← GSYM NOT_LT] THEN SIMP_TAC [MULT_CLAUSES, ADD_CLAUSES]] THEN
    SUBGOAL_THEN (← q r"w * (v:num->num->num) j i < M") ASSUME_TAC THENL
     [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC (← q r"n * V:num") THEN
      CONJ_TAC THENL [MATCH_MP_TAC LE_MULT2 THEN ASM_SIMP_TAC [], ASM_ARITH_TAC],
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     (← q r"(((t:num->num) i + (s0:num->num) i) MOD Q + w * (v:num->num->num) j i)
      MOD Q") THEN
    CONJ_TAC THENL
     [CONV_TAC (BINOP_CONV MOD_DOWN_CONV) THEN REWRITE_TAC [ADD_ASSOC],
      MATCH_MP_TAC MOD_LT THEN
      FIRST_X_ASSUM (fun th => tactic_of do
        let s0v ← q r"s0:num->num"
        let ok ← if can (find_term (fun u => u == s0v)) (concl th) && is_forall (concl th)
          then do
            let mv ← q r"M:num"
            pure (can (find_term (fun u => u == mv)) (concl th))
          else pure false
        pure (MP_TAC (← SPEC (← q r"i:num") (← liftExcept (check (fun _ => ok) th))))) THEN
      ASM_REWRITE_TAC [] THEN EXPAND_TAC "Q" THEN ASM_ARITH_TAC]))

  let GALLAI_WITT ← prove
   r"!d k (v:num->num->num) r.
        1 <= r /\ (!j i. j < k /\ d <= i ==> v j i = 0)
        ==> ?M. !col. (!x. col x < r)
                      ==> ?a lm c.
                            0 < lm /\
                            !j. j < k
                                ==> (\i. a i + lm * v j i) IN hj_cube M d /\
                                    col(\i. a i + lm * v j i) = c"
   (← do
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"d:num", ← q r"k:num", ← q r"v:num->num->num", ← q r"inv(&r)"]
      MULTIDIM_SZEMEREDI) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [REAL_LT_INV_EQ, REAL_OF_NUM_LT] THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"M0:num")) THEN EXISTS_TAC (← q r"M0:num") THEN
    X_GEN_TAC (← q r"col:(num->num)->num") THEN DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"col:(num->num)->num", ← q r"hj_cube M0 d",
                      ← q r"{c:num | c < r}"]
      CARD_PIGEONHOLE) THEN
    REWRITE_TAC [FINITE_HJ_CUBE, FINITE_NUMSEG_LT, IN_ELIM_THM, CARD_NUMSEG_LT,
                 CARD_HJ_CUBE] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, IN_ELIM_THM] THEN
      EXISTS_TAC (← q r"0") THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"c:num") STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o SPECL
     [← q r"M0:num", ← q r"{x | x IN hj_cube M0 d /\ (col:(num->num)->num) x = c}"]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC [LE_REFL, SUBSET, IN_ELIM_THM] THEN
      CONJ_TAC THENL [SIMP_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"&0 < &r") ASSUME_TAC THENL
       [REWRITE_TAC [REAL_OF_NUM_LT] THEN ASM_ARITH_TAC, ALL_TAC] THEN
      ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN REWRITE_TAC [← GSYM real_div] THEN
      ASM_SIMP_TAC [REAL_LE_LDIV_EQ] THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"a:num->num") (X_CHOOSE_THEN (← q r"lm:num")
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [← q r"a:num->num", ← q r"lm:num", ← q r"c:num"] THEN
    ASM_SIMP_TAC []))

  let CORNERS ← prove
   r"!delta.
        &0 < delta
        ==> ?M0. !M A. M0 <= M /\ A SUBSET {(x,y) | x < M /\ y < M} /\
                       delta * &M pow 2 <= &(CARD A)
                       ==> ?x y lm. 0 < lm /\ (x,y) IN A /\
                                     (x + lm,y) IN A /\ (x,y + lm) IN A"
   (← do
    let a1 ← ARITH_RULE (← q r"~(1 = 0)")
    pure (GEN_TAC THEN DISCH_TAC THEN
    MP_TAC (← SPECL
     [← q r"2", ← q r"3",
      ← q r"\j i. if (j = 1 /\ i = 0) \/ (j = 2 /\ i = 1) then 1 else 0",
      ← q r"delta:real"] MULTIDIM_SZEMEREDI) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ARITH_TAC, ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"M0:num") THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [← q r"M:num", ← q r"A:num#num->bool"] THEN STRIP_TAC THEN
    ABBREV_TAC
     (← q r"emb = \p:num#num. \i:num. if i = 0 then FST p
                                 else if i = 1 then SND p else 0") THEN
    SUBGOAL_THEN
     (← q r"!p f. f = (emb:num#num->num->num) p ==> p = (f 0,f 1)")
    ASSUME_TAC THENL
     [EXPAND_TAC "emb" THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [a1, PAIR],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"FINITE(A:num#num->bool)") ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC (← q r"{x,y | x IN {x:num | x < M} /\ y IN {y:num | y < M}}") THEN
      SIMP_TAC [FINITE_PRODUCT, FINITE_NUMSEG_LT] THEN
      UNDISCH_TAC (← q r"(A:num#num->bool) SUBSET {(x,y) | x < M /\ y < M:num}") THEN
      REWRITE_TAC [SUBSET, FORALL_PAIR_THM, IN_ELIM_PAIR_THM, IN_ELIM_THM],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"M:num",
      ← q r"IMAGE (emb:num#num->num->num) A"]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC [],
        REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, FORALL_PAIR_THM] THEN
        MAP_EVERY X_GEN_TAC [← q r"x:num", ← q r"y:num"] THEN DISCH_TAC THEN
        SUBGOAL_THEN (← q r"x < M /\ y < M:num") STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC (← q r"(A:num#num->bool) SUBSET {(x,y) | x < M /\
           y < M:num}") THEN
          REWRITE_TAC [SUBSET, FORALL_PAIR_THM, IN_ELIM_PAIR_THM] THEN
          ASM_MESON_TAC [],
          ALL_TAC] THEN
        EXPAND_TAC "emb" THEN REWRITE_TAC [IN_HJ_CUBE] THEN CONJ_TAC THEN
        X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN
        ASM_CASES_TAC (← q r"i = 0") THEN ASM_REWRITE_TAC [] THEN
        ASM_CASES_TAC (← q r"i = 1") THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC,
        SUBGOAL_THEN (← q r"CARD(IMAGE (emb:num#num->num->num) A) = CARD A")
        SUBST1_TAC THENL
         [MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_MESON_TAC [], ALL_TAC] THEN
        ASM_REWRITE_TAC [← GSYM REAL_OF_NUM_POW]],
      ALL_TAC] THEN
    REWRITE_TAC [IN_IMAGE] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"a:num->num") (X_CHOOSE_THEN (← q r"lm:num")
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pts")))) THEN
    MAP_EVERY EXISTS_TAC [← q r"(a:num->num) 0", ← q r"(a:num->num) 1", ← q r"lm:num"] THEN
    ASM_REWRITE_TAC [] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "pts" (MP_TAC o SPEC (← q r"0")),
      USE_THEN "pts" (MP_TAC o SPEC (← q r"1")),
      USE_THEN "pts" (MP_TAC o SPEC (← q r"2"))] THEN
    REWRITE_TAC [ARITH] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"p:num#num") STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP (← ASSUME
     (← q r"!p f. f = (emb:num#num->num->num) p ==> p = (f 0,f 1)"))) THEN
    REWRITE_TAC [ARITH, MULT_CLAUSES, ADD_CLAUSES] THEN
    DISCH_THEN (fun th => tactic_of do pure (SUBST_ALL_TAC (← SYM th))) THEN
    ASM_REWRITE_TAC []))

  -- @@RETURN BEGIN
  return { MULTIDIM_SZEMEREDI, GALLAI_WITT, CORNERS }
  -- @@RETURN END

end HolLibrary.Szemeredi
