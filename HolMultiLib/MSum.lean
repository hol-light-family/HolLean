/- ========================================================================= -/
/- Sums of matrices over an indexing set.                                    -/
/- ========================================================================= -/
/- File: HolMultiLib/MSum.lean

  Original (c) Copyright, Andrea Gabrielli, Marco Maggesi 2016-2017
  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Multivariate/msum.ml`, in the style of
  HolMultiLib/Vectors.lean: pure, the proofs translated by hand, one `let` per
  OCaml `let`, in file order.  What msum.ml uses from the core library and
  from Multivariate/vectors.ml (with misc.ml) is passed in `MsumDeps`;
  SessionMultiLib/MSum.lean supplies it.

  msum.ml's `needs "Multivariate/vectors.ml"` is the wiring's import.  Its
  load-time effects (`prioritize_vector`, `prioritize_real` and the `norm`
  overload for `matrix_norm`) are made inside the first bundle at their file
  positions.
-/

import HolMath

open HolCore HolCore.Lib
open HolCore.Kernel hiding ASSUME INST
open HolCore.Equal (ioconv lhs rhs lhand)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)
open HolLight HolLight.Syntax

namespace HolMultiLib.MSum

set_option maxHeartbeats 4000000

/-- The core theorems msum.ml uses (supplied by Session). -/
structure CoreThms where
  (ADD1 ADD_0 ADD_CLAUSES ADD_SUB ADD_SUC ARITH CARD_NUMSEG CART_EQ CART_EQ_FULL
   CONTRAPOS_THM DELETE DE_MORGAN_THM DIMINDEX_FINITE_PROD ETA_AX FINITE_DELETE
   FINITE_IMAGE FINITE_INDEX_INRANGE FINITE_INDUCT_STRONG FINITE_NUMSEG FINITE_RULES
   FINITE_SUBSET FINITE_UNIONS FORALL_PAIR_THM FUN_EQ_THM IMAGE_CLAUSES IMP_CONJ
   IMP_CONJ_ALT IN_DELETE IN_ELIM_THM IN_IMAGE IN_INSERT IN_INTER IN_NUMSEG IN_UNIONS
   ITERATE_CLAUSES ITERATE_REFLECT LAMBDA_BETA LE LT_REFL MONO_AND NOT_IN_EMPTY NOT_LE
   NOT_LT NUMSEG_CLAUSES NUMSEG_EMPTY NUMSEG_OFFSET_IMAGE NUMSEG_SING ONE REAL_ADD_ASSOC
   REAL_LE_TRANS SELECT_UNIQUE SUBSET SUC_INJ SUC_SUB1 SUM_ADD SUM_ADD_GEN SUM_ADD_SPLIT
   SUM_CASES SUM_CLAUSES SUM_CLAUSES_LEFT SUM_COMBINE_L SUM_COMBINE_R SUM_CONST
   SUM_DELETE SUM_DELTA SUM_DIFF SUM_EQ SUM_EQ_0 SUM_EQ_GENERAL SUM_EQ_GENERAL_INVERSES
   SUM_GROUP SUM_GROUP_RELATION SUM_IMAGE SUM_IMAGE_GEN SUM_INCL_EXCL SUM_INJECTION
   SUM_LE SUM_LMUL SUM_NEG SUM_OFFSET SUM_OFFSET_0 SUM_PAIR SUM_RESTRICT_SET SUM_RMUL
   SUM_SUB SUM_SUM_PRODUCT SUM_SUPERSET SUM_SWAP SUM_UNION SUM_UNION_NONZERO UNIONS_0
   UNIONS_INSERT monoidal neutral o_DEF o_THM support : thm)
  deriving Inhabited

/-- What msum.ml uses from Multivariate/vectors.ml and misc.ml. -/
structure VecThms where
  (COND_COMPONENT MATRIX_ADD_AC MATRIX_ADD_ASSOC MATRIX_ADD_COMPONENT
   MATRIX_ADD_LDISTRIB MATRIX_ADD_LID MATRIX_ADD_RDISTRIB MATRIX_ADD_RID
   MATRIX_CMUL_COMPONENT MATRIX_MUL_LZERO MATRIX_MUL_RZERO MATRIX_NEG_0
   MATRIX_NEG_COMPONENT MATRIX_NEG_SUB MATRIX_SUB_COMPONENT MAT_0_COMPONENT
   VEC_COMPONENT VSUM_COMPONENT VSUM_NORM VECTORIZE_COMPONENT : thm)
  deriving Inhabited

/-- What msum.ml uses from the core library's and vectors.ml's procedures. -/
structure MsumDeps where
  -- definitions and parser state
  new_definition : String → ExceptT String IO thm
  overload_interface : String → term → ExceptT String IO Unit
  prioritize_real : IO Unit
  prioritize_vector : IO Unit
  -- decision procedures
  ARITH_RULE : term → ExceptT String IO thm
  ASM_ARITH_TAC : tactic
  ASM_MESON_TAC : List thm → tactic
  INDUCT_TAC : tactic
  MATRIX_ARITH : term → ExceptT String IO thm
  MATRIX_ARITH_TAC : tactic
  MESON_TAC : List thm → tactic
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  -- conversions
  num_CONV : ioconv
  -- theorems
  core : CoreThms
  vec : VecThms

/- ------------------------------------------------------------------------- -/
/- Matrix norm (vector norm of "flattened" form); sums over matrices.       -/
/- (msum.ml 9-245)                                                            -/
/- ------------------------------------------------------------------------- -/

structure Msum1 where
  matrix_norm : thm
  NEUTRAL_MATRIX_ADD : thm
  MONOIDAL_MATRIX_ADD : thm
  msum : thm
  MSUM_COMPONENT : thm
  MSUM_ROW : thm
  MSUM_CLAUSES : thm
  MSUM : thm
  MSUM_EQ_0 : thm
  MSUM_0 : thm
  MSUM_LMUL : thm
  MSUM_RMUL : thm
  MSUM_ADD : thm
  MSUM_SUB : thm
  MSUM_CONST : thm
  MSUM_MATRIX_RMUL : thm
  MSUM_MATRIX_LMUL : thm
  MSUM_IMAGE : thm
  MSUM_UNION : thm
  MSUM_DIFF : thm
  MSUM_DELETE : thm
  MSUM_INCL_EXCL : thm
  MSUM_NEG : thm
  MSUM_EQ : thm
  MSUM_SUPERSET : thm
  MSUM_SUPPORT_EXPLICIT : thm
  MSUM_SUPPORT : thm
  MSUM_UNIV : thm
  MSUM_EQ_SUPERSET : thm
  MSUM_UNION_RZERO : thm
  MSUM_UNION_LZERO : thm
  MSUM_RESTRICT : thm
  MSUM_RESTRICT_SET : thm
  MSUM_CASES : thm
  MSUM_SING : thm
  VECTORIZE_MSUM : thm
  MSUM_NORM : thm
  MSUM_NORM_LE : thm
  MSUM_NORM_TRIANGLE : thm
  MSUM_NORM_BOUND : thm
  deriving Inhabited

@[nospecialize]
def setupMsum1 [HolBase] (D : MsumDeps) : ExceptT String IO Msum1 := do
  -- @@SCOPE BEGIN
  let { MATRIX_ARITH, MATRIX_ARITH_TAC, MESON_TAC, SET_TAC, new_definition,
        overload_interface, prioritize_real, prioritize_vector, .. } := D
  let { CART_EQ, CART_EQ_FULL, DIMINDEX_FINITE_PROD, FINITE_INDEX_INRANGE,
        FINITE_INDUCT_STRONG, FINITE_RULES, ITERATE_CLAUSES, LAMBDA_BETA, NOT_IN_EMPTY,
        REAL_LE_TRANS, SELECT_UNIQUE, SUM_ADD, SUM_CASES, SUM_CLAUSES, SUM_CONST, SUM_DELETE,
        SUM_DIFF, SUM_EQ, SUM_EQ_0, SUM_IMAGE, SUM_INCL_EXCL, SUM_LE, SUM_LMUL, SUM_NEG,
        SUM_RESTRICT_SET, SUM_RMUL, SUM_SUB, SUM_SUPERSET, SUM_UNION, monoidal, neutral,
        o_DEF, support, .. } := D.core
  let { COND_COMPONENT, MATRIX_ADD_COMPONENT, MATRIX_ADD_LDISTRIB, MATRIX_ADD_RDISTRIB,
        MATRIX_ADD_RID, MATRIX_CMUL_COMPONENT, MATRIX_MUL_LZERO, MATRIX_MUL_RZERO,
        MATRIX_NEG_COMPONENT, MATRIX_SUB_COMPONENT, MAT_0_COMPONENT, VSUM_COMPONENT,
        VSUM_NORM, VECTORIZE_COMPONENT, .. } := D.vec
  -- @@SCOPE END
  let ma (s : String) : ExceptT String IO thm := do MATRIX_ARITH (← q s)

  prioritize_vector
  prioritize_real

  overload_interface "norm" (← q r"matrix_norm:real^M^N->real")

  let matrix_norm ← new_definition
   r"matrix_norm (m:real^M^N) = norm(vectorize m)"

  let NEUTRAL_MATRIX_ADD ← prove
   r"neutral(+) = mat 0:real^M^N"
   (REWRITE_TAC [neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    REWRITE_TAC [← ma r"x + y = y <=> x = mat 0:real^M^N",
                 ← ma r"x + y = x <=> y = mat 0:real^M^N"])

  let MONOIDAL_MATRIX_ADD ← prove
   r"monoidal((+):real^M^N->real^M^N->real^M^N)"
   (REWRITE_TAC [monoidal, NEUTRAL_MATRIX_ADD] THEN
    REPEAT CONJ_TAC THEN MATRIX_ARITH_TAC)

  let msum ← new_definition
   r"msum s (f:A->real^M^N):real^M^N = (lambda i j. sum s (\x. f x$i$j))"

  let MSUM_COMPONENT ← prove
   r"!s (f:A->real^M^N) i j. msum s f$i$j = sum s (\x. f x$i$j)"
   (REPEAT GEN_TAC THEN SUBGOAL_THEN
     (← q r"(?h. 1 <= h /\ h <= dimindex(:N) /\ !z:real^M^N. z$i = z$h) /\
     (?k. 1 <= k /\ k <= dimindex(:M) /\ !z:real^M. z$j = z$k)")
     (CONJUNCTS_THEN CHOOSE_TAC) THENL
    [REWRITE_TAC [FINITE_INDEX_INRANGE],
     ASM_SIMP_TAC [msum, LAMBDA_BETA]])

  let MSUM_ROW ← prove
   r"!s f:A->real^M^N i. msum s f$i = vsum s (\x. f x$i)"
   (REWRITE_TAC [CART_EQ_FULL, MSUM_COMPONENT, VSUM_COMPONENT])

  let MSUM_CLAUSES ← prove
   r"(!f:A->real^M^N. msum {} f = mat 0) /\
   (!x:A f s. FINITE s
            ==> msum (x INSERT s) f : real^M^N=
                if x IN s then msum s f else f(x) + msum s f)"
   (SIMP_TAC [msum, CART_EQ, LAMBDA_BETA, MATRIX_ADD_COMPONENT, SUM_CLAUSES] THEN
    SIMP_TAC [MAT_0_COMPONENT] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [LAMBDA_BETA, MATRIX_ADD_COMPONENT])

  let MSUM ← prove
   r"!f:A->real^M^N s. FINITE s ==> msum s f = iterate (+) s f"
   (GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC [MSUM_CLAUSES, ITERATE_CLAUSES, MONOIDAL_MATRIX_ADD] THEN
    REWRITE_TAC [NEUTRAL_MATRIX_ADD])

  let MSUM_EQ_0 ← prove
   r"!f:A->real^M^N s. (!x. x IN s ==> (f(x) = mat 0)) ==> (msum s f = mat 0)"
   (REWRITE_TAC [CART_EQ_FULL, MSUM_COMPONENT, MAT_0_COMPONENT] THEN
    SIMP_TAC [SUM_EQ_0])

  let MSUM_0 ← prove
   r"msum s (\x:A. mat 0) = mat 0:real^M^N"
   (SIMP_TAC [MSUM_EQ_0])

  let MSUM_LMUL ← prove
   r"!f:A->real^M^N c s.  msum s (\x. c %% f(x)) = c %% msum s f"
   (REWRITE_TAC [CART_EQ_FULL, MSUM_COMPONENT, MATRIX_CMUL_COMPONENT, SUM_LMUL])

  let MSUM_RMUL ← prove
   r"!c:A->real s v:real^M^N. msum s (\x. c x %% v) = (sum s c) %% v"
   (REWRITE_TAC [CART_EQ_FULL, MSUM_COMPONENT, MATRIX_CMUL_COMPONENT, SUM_RMUL])

  let MSUM_ADD ← prove
   r"!f g:A->real^M^N s.
     FINITE s ==> (msum s (\x. f x + g x) = msum s f + msum s g)"
   (REWRITE_TAC [CART_EQ_FULL, MSUM_COMPONENT, MATRIX_ADD_COMPONENT] THEN
    SIMP_TAC [SUM_ADD])

  let MSUM_SUB ← prove
   r"!f g:A->real^M^N s.
     FINITE s ==> (msum s (\x. f x - g x) = msum s f - msum s g)"
   (REWRITE_TAC [CART_EQ_FULL, MSUM_COMPONENT, MATRIX_SUB_COMPONENT] THEN
    SIMP_TAC [SUM_SUB])

  let MSUM_CONST ← prove
   r"!c:real^M^N s. FINITE s ==> (msum s (\n:A. c) = &(CARD s) %% c)"
   (REWRITE_TAC [CART_EQ_FULL, MSUM_COMPONENT, MATRIX_CMUL_COMPONENT] THEN
    SIMP_TAC [SUM_CONST])

  let MSUM_MATRIX_RMUL ← prove
   r"!(f:A->real^N^M) (A:real^P^N) s.
        FINITE s ==> msum s (\i. f(i) ** A) = msum s f ** A"
   (GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [MSUM_CLAUSES, MATRIX_MUL_LZERO, MATRIX_ADD_RDISTRIB])

  let MSUM_MATRIX_LMUL ← prove
   r"!(f:A->real^P^N) (A:real^N^M) s.
        FINITE s ==> msum s (\i. A ** f(i)) = A ** msum s f"
   (GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [MSUM_CLAUSES, MATRIX_MUL_RZERO, MATRIX_ADD_LDISTRIB])

  let MSUM_IMAGE ← prove
   r"!(f:A->B) (g:B->real^M^N) s.
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> msum (IMAGE f s) g = msum s (g o f)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [CART_EQ_FULL, MSUM_COMPONENT] THEN
    REPEAT GEN_TAC THEN
    W (MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o lhand o snd) THEN
    ASM_REWRITE_TAC [o_DEF])

  let MSUM_UNION ← prove
   r"!f:A->real^M^N s t.
     FINITE s /\ FINITE t /\ DISJOINT s t
     ==> (msum (s UNION t) f = msum s f + msum t f)"
   (REWRITE_TAC [CART_EQ_FULL, MATRIX_ADD_COMPONENT, MSUM_COMPONENT] THEN
    SIMP_TAC [SUM_UNION])

  let MSUM_DIFF ← prove
   r"!f:A->real^M^N s t. FINITE s /\ t SUBSET s
           ==> (msum (s DIFF t) f = msum s f - msum t f)"
   (REWRITE_TAC [CART_EQ_FULL, MATRIX_SUB_COMPONENT, MSUM_COMPONENT] THEN
    SIMP_TAC [SUM_DIFF])

  let MSUM_DELETE ← prove
   r"!f:A->real^M^N s a.
     FINITE s /\ a IN s
     ==> msum (s DELETE a) f = msum s f - f a"
   (REWRITE_TAC [CART_EQ_FULL, MATRIX_SUB_COMPONENT, MSUM_COMPONENT] THEN
    SIMP_TAC [SUM_DELETE])

  let MSUM_INCL_EXCL ← prove
   r"!s t (f:A->real^M^N).
     FINITE s /\ FINITE t
     ==> msum s f + msum t f = msum (s UNION t) f + msum (s INTER t) f"
   (REWRITE_TAC [CART_EQ_FULL, MSUM_COMPONENT, MATRIX_ADD_COMPONENT] THEN
    SIMP_TAC [SUM_INCL_EXCL])

  let MSUM_NEG ← prove
   r"!f:A->real^M^N s. msum s (\x. --f x) = --msum s f"
   (REWRITE_TAC [CART_EQ_FULL, MSUM_COMPONENT, MATRIX_NEG_COMPONENT, SUM_NEG])

  let MSUM_EQ ← prove
   r"!f g:A->real^M^N s. (!x. x IN s ==> (f x = g x)) ==> (msum s f = msum s g)"
   (REWRITE_TAC [CART_EQ_FULL, MSUM_COMPONENT] THEN SIMP_TAC [SUM_EQ])

  let MSUM_SUPERSET ← prove
   r"!f:A->real^M^N u v.
        u SUBSET v /\ (!x. x IN v /\ ~(x IN u) ==> (f(x) = mat 0))
        ==> (msum v f = msum u f)"
   (REWRITE_TAC [CART_EQ_FULL, MSUM_COMPONENT, MAT_0_COMPONENT] THEN
    SIMP_TAC [SUM_SUPERSET])

  let MSUM_SUPPORT_EXPLICIT ← prove
   r"!f:A->real^M^N s. msum {x | x IN s /\ ~(f x = mat 0)} f = msum s f"
   (REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MSUM_SUPERSET THEN
    SET_TAC [])

  let MSUM_SUPPORT ← prove
   r"!f s. msum (support (+) f s) f = msum s f"
   (SIMP_TAC [support, NEUTRAL_MATRIX_ADD, MSUM_SUPPORT_EXPLICIT])

  let MSUM_UNIV ← prove
   r"!f:A->real^M^N s.
     support (+) f (:A) SUBSET s ==> msum s f = msum (:A) f"
   (REWRITE_TAC [support, NEUTRAL_MATRIX_ADD] THEN REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [← GSYM MSUM_SUPPORT_EXPLICIT] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC [])

  let MSUM_EQ_SUPERSET ← prove
   r"!(f:A->real^M^N) s t.
        FINITE t /\ t SUBSET s /\
        (!x. x IN t ==> (f x = g x)) /\
        (!x. x IN s /\ ~(x IN t) ==> f(x) = mat 0)
        ==> msum s f = msum t g"
   (MESON_TAC [MSUM_SUPERSET, MSUM_EQ])

  let MSUM_UNION_RZERO ← prove
   r"!f:A->real^M^N u v.
        (!x. x IN v /\ ~(x IN u) ==> (f(x) = mat 0))
        ==> (msum (u UNION v) f = msum u f)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC MSUM_SUPERSET THEN ASM SET_TAC [])

  let MSUM_UNION_LZERO ← prove
   r"!f:A->real^M^N u v.
        (!x. x IN u /\ ~(x IN v) ==> (f(x) = mat 0))
        ==> (msum (u UNION v) f = msum v f)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC MSUM_SUPERSET THEN ASM SET_TAC [])

  let MSUM_RESTRICT ← prove
   r"!f:A->real^M^N s. msum s (\x. if x IN s then f(x) else mat 0) = msum s f"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC MSUM_EQ THEN SIMP_TAC [])

  let MSUM_RESTRICT_SET ← prove
   r"!P s f:A->real^M^N. msum {x | x IN s /\ P x} f =
                       msum s (\x. if P x then f x else mat 0)"
   (REWRITE_TAC [CART_EQ_FULL, MSUM_COMPONENT, MAT_0_COMPONENT,
                 COND_COMPONENT] THEN
    SIMP_TAC [SUM_RESTRICT_SET, COND_COMPONENT])

  let MSUM_CASES ← prove
   r"!s P f g. FINITE s
             ==> msum s (\x:A. if P x then (f x):real^M^N else g x) =
                 msum {x | x IN s /\ P x} f + msum {x | x IN s /\ ~P x} g"
   (REWRITE_TAC [CART_EQ_FULL, MSUM_COMPONENT, MATRIX_ADD_COMPONENT,
                 COND_COMPONENT] THEN
    SIMP_TAC [SUM_CASES])

  let MSUM_SING ← prove
   r"!f:A->real^M^N x. msum {x} f = f(x)"
   (SIMP_TAC [MSUM_CLAUSES, FINITE_RULES, NOT_IN_EMPTY, MATRIX_ADD_RID])

  let VECTORIZE_MSUM ← prove
   r"!s f:A->real^M^N. vectorize (msum s f) = vsum s (\x. vectorize (f x))"
   (SIMP_TAC [CART_EQ, VECTORIZE_COMPONENT, DIMINDEX_FINITE_PROD,
              VSUM_COMPONENT, MSUM_COMPONENT])

  let MSUM_NORM ← prove
   r"!s f:A->real^M^N. FINITE s ==> norm(msum s f) <= sum s (\x. norm(f x))"
   (REWRITE_TAC [matrix_norm, VECTORIZE_MSUM] THEN SIMP_TAC [VSUM_NORM])

  let MSUM_NORM_LE ← prove
   r"!s f:A->real^M^N g. FINITE s /\ (!x. x IN s ==> norm(f x) <= g(x))
                       ==> norm(msum s f) <= sum s g"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"sum s (\x:A. norm(f x:real^M^N))") THEN
    ASM_SIMP_TAC [MSUM_NORM, SUM_LE])

  let MSUM_NORM_TRIANGLE ← prove
   r"!s f:A->real^M^N b. FINITE s /\ sum s (\a. norm(f a)) <= b
                       ==> norm(msum s f) <= b"
   (MESON_TAC [MSUM_NORM, REAL_LE_TRANS])

  let MSUM_NORM_BOUND ← prove
   r"!s f:A->real^M^N b. FINITE s /\ (!x. x IN s ==> norm(f(x)) <= b)
                       ==> norm(msum s f) <= &(CARD s) * b"
   (SIMP_TAC [← GSYM SUM_CONST, MSUM_NORM_LE])

  return { matrix_norm, NEUTRAL_MATRIX_ADD, MONOIDAL_MATRIX_ADD, msum, MSUM_COMPONENT,
           MSUM_ROW, MSUM_CLAUSES, MSUM, MSUM_EQ_0, MSUM_0, MSUM_LMUL, MSUM_RMUL, MSUM_ADD,
           MSUM_SUB, MSUM_CONST, MSUM_MATRIX_RMUL, MSUM_MATRIX_LMUL, MSUM_IMAGE, MSUM_UNION,
           MSUM_DIFF, MSUM_DELETE, MSUM_INCL_EXCL, MSUM_NEG, MSUM_EQ, MSUM_SUPERSET,
           MSUM_SUPPORT_EXPLICIT, MSUM_SUPPORT, MSUM_UNIV, MSUM_EQ_SUPERSET, MSUM_UNION_RZERO,
           MSUM_UNION_LZERO, MSUM_RESTRICT, MSUM_RESTRICT_SET, MSUM_CASES, MSUM_SING,
           VECTORIZE_MSUM, MSUM_NORM, MSUM_NORM_LE, MSUM_NORM_TRIANGLE, MSUM_NORM_BOUND }

/- ------------------------------------------------------------------------- -/
/- Sums over numeric segments, reindexing, grouping and swapping.            -/
/- (msum.ml 248-581)                                                          -/
/- ------------------------------------------------------------------------- -/

structure Msum2 where
  MSUM_CLAUSES_NUMSEG : thm
  MSUM_CLAUSES_RIGHT : thm
  MSUM_CMUL_NUMSEG : thm
  MSUM_EQ_NUMSEG : thm
  MSUM_IMAGE_GEN : thm
  MSUM_GROUP : thm
  MSUM_GROUP_RELATION : thm
  MSUM_VMUL : thm
  MSUM_DELTA : thm
  MSUM_ADD_NUMSEG : thm
  MSUM_SUB_NUMSEG : thm
  MSUM_ADD_SPLIT : thm
  MSUM_MSUM_PRODUCT : thm
  MSUM_IMAGE_NONZERO : thm
  MSUM_UNION_NONZERO : thm
  MSUM_UNIONS_NONZERO : thm
  MSUM_CLAUSES_LEFT : thm
  MSUM_DIFFS : thm
  MSUM_DIFFS_ALT : thm
  MSUM_DELETE_CASES : thm
  MSUM_EQ_GENERAL : thm
  MSUM_EQ_GENERAL_INVERSES : thm
  MSUM_OFFSET : thm
  MSUM_OFFSET_0 : thm
  MSUM_TRIV_NUMSEG : thm
  MSUM_CONST_NUMSEG : thm
  MSUM_SUC : thm
  MSUM_BIJECTION : thm
  MSUM_PARTIAL_SUC : thm
  MSUM_PARTIAL_PRE : thm
  MSUM_COMBINE_L : thm
  MSUM_COMBINE_R : thm
  MSUM_INJECTION : thm
  MSUM_SWAP : thm
  MSUM_SWAP_NUMSEG : thm
  MSUM_ADD_GEN : thm
  MSUM_CASES_1 : thm
  MSUM_SING_NUMSEG : thm
  MSUM_1 : thm
  MSUM_2 : thm
  MSUM_3 : thm
  MSUM_4 : thm
  MSUM_PAIR : thm
  MSUM_PAIR_0 : thm
  MSUM_REFLECT : thm
  deriving Inhabited

@[nospecialize]
def setupMsum2 [HolBase] (D : MsumDeps) (BMsum1 : Msum1) : ExceptT String IO Msum2 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MATRIX_ARITH,
        MATRIX_ARITH_TAC, SET_RULE, num_CONV, .. } := D
  let { ADD1, ADD_0, ADD_CLAUSES, ADD_SUB, ADD_SUC, ARITH, CARD_NUMSEG, CART_EQ,
        CART_EQ_FULL, CONTRAPOS_THM, DELETE, DE_MORGAN_THM, ETA_AX, FINITE_DELETE,
        FINITE_IMAGE, FINITE_INDUCT_STRONG, FINITE_NUMSEG, FINITE_SUBSET, FINITE_UNIONS,
        FORALL_PAIR_THM, FUN_EQ_THM, IMAGE_CLAUSES, IMP_CONJ, IMP_CONJ_ALT, IN_DELETE,
        IN_ELIM_THM, IN_IMAGE, IN_INSERT, IN_INTER, IN_NUMSEG, IN_UNIONS, ITERATE_REFLECT,
        LAMBDA_BETA, LE, LT_REFL, MONO_AND, NOT_LE, NOT_LT, NUMSEG_CLAUSES, NUMSEG_EMPTY,
        NUMSEG_OFFSET_IMAGE, NUMSEG_SING, ONE, REAL_ADD_ASSOC, SUBSET, SUC_INJ, SUC_SUB1,
        SUM_ADD_GEN, SUM_ADD_SPLIT, SUM_CLAUSES_LEFT, SUM_COMBINE_L, SUM_COMBINE_R,
        SUM_DELTA, SUM_EQ_GENERAL, SUM_EQ_GENERAL_INVERSES, SUM_GROUP, SUM_GROUP_RELATION,
        SUM_IMAGE_GEN, SUM_INJECTION, SUM_OFFSET, SUM_OFFSET_0, SUM_PAIR, SUM_SUM_PRODUCT,
        SUM_SWAP, SUM_UNION_NONZERO, UNIONS_0, UNIONS_INSERT, o_DEF, o_THM, .. } := D.core
  let { COND_COMPONENT, MATRIX_ADD_AC, MATRIX_ADD_ASSOC, MATRIX_ADD_COMPONENT,
        MATRIX_ADD_LID, MATRIX_NEG_0, MATRIX_NEG_SUB, MAT_0_COMPONENT, VEC_COMPONENT,
        .. } := D.vec
  let { MONOIDAL_MATRIX_ADD, MSUM, MSUM_ADD, MSUM_CASES, MSUM_CLAUSES, MSUM_COMPONENT,
        MSUM_CONST, MSUM_DELETE, MSUM_EQ, MSUM_IMAGE, MSUM_LMUL, MSUM_NEG, MSUM_RMUL,
        MSUM_SING, MSUM_SUB, NEUTRAL_MATRIX_ADD, msum, .. } := BMsum1
  -- @@SCOPE END
  let ma (s : String) : ExceptT String IO thm := do MATRIX_ARITH (← q s)
  let numc (s : String) : ExceptT String IO thm := do ExceptT.mk (num_CONV (← q s))

  let MSUM_CLAUSES_NUMSEG ← prove
   r"(!m. msum(m..0) f = if m = 0 then f(0) else mat 0:real^M^N) /\
   (!m n. msum(m..SUC n) f = if m <= SUC n then msum(m..n) f + f(SUC n)
                             else msum(m..n) f)"
   (REWRITE_TAC [NUMSEG_CLAUSES] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC [MSUM_SING, MSUM_CLAUSES, FINITE_NUMSEG, IN_NUMSEG] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"~(SUC n <= n)"), MATRIX_ADD_AC])

  let MSUM_CLAUSES_RIGHT ← prove
   r"!f m n. 0 < n /\ m <= n ==> msum(m..n) f = msum(m..n-1) f + (f n):real^M^N"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    SIMP_TAC [LT_REFL, MSUM_CLAUSES_NUMSEG, SUC_SUB1])

  let MSUM_CMUL_NUMSEG ← prove
   r"!f c m n. msum (m..n) (\x. c %% f x) = c %% msum (m..n) f:real^M^N"
   (SIMP_TAC [MSUM_LMUL, FINITE_NUMSEG])

  let MSUM_EQ_NUMSEG ← prove
   r"!f g m n.
         (!x. m <= x /\ x <= n ==> (f x = g x:real^M^N))
         ==> (msum(m .. n) f = msum(m .. n) g)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC MSUM_EQ THEN
    ASM_SIMP_TAC [FINITE_NUMSEG, IN_NUMSEG])

  let MSUM_IMAGE_GEN ← prove
   r"!f:A->B (g:A->real^M^N) s.
        FINITE s
        ==> (msum s g =
             msum (IMAGE f s) (\y. msum {x | x IN s /\ (f(x) = y)} g))"
   (REWRITE_TAC [CART_EQ_FULL, MSUM_COMPONENT] THEN SIMP_TAC [SUM_IMAGE_GEN])

  let MSUM_GROUP ← prove
   r"!f:A->B (g:A->real^M^N) s t.
        FINITE s /\ IMAGE f s SUBSET t
        ==> msum t (\y. msum {x | x IN s /\ f(x) = y} g) = msum s g"
   (REWRITE_TAC [CART_EQ_FULL, MSUM_COMPONENT] THEN SIMP_TAC [SUM_GROUP])

  let MSUM_GROUP_RELATION ← prove
   r"!R:A->B->bool (g:A->real^M^N) s t.
         FINITE s /\
         (!x. x IN s ==> ?!y. y IN t /\ R x y)
         ==> msum t (\y. msum {x | x IN s /\ R x y} g) = msum s g"
   (REWRITE_TAC [CART_EQ_FULL, MSUM_COMPONENT] THEN
    SIMP_TAC [SUM_GROUP_RELATION])

  let MSUM_VMUL ← prove
   r"!f v:real^M^N s. (sum s f) %% v = msum s (\x:A. f(x) %% v)"
   (REWRITE_TAC [MSUM_RMUL])

  let MSUM_DELTA ← prove
   r"!s a. msum s (\x:A. if x = a then b else mat 0:real^M^N) =
         if a IN s then b else mat 0"
   (REWRITE_TAC [CART_EQ_FULL, MSUM_COMPONENT, COND_COMPONENT] THEN
    SIMP_TAC [MAT_0_COMPONENT, SUM_DELTA])

  let MSUM_ADD_NUMSEG ← prove
   r"!f g m n.
     msum(m..n) (\i. f i + g i) = msum(m..n) f + msum(m..n) g:real^M^N"
   (SIMP_TAC [MSUM_ADD, FINITE_NUMSEG])

  let MSUM_SUB_NUMSEG ← prove
   r"!f g m n.
     msum(m..n) (\i. f i - g i) = msum(m..n) f - msum(m..n) g:real^M^N"
   (SIMP_TAC [MSUM_SUB, FINITE_NUMSEG])

  let MSUM_ADD_SPLIT ← prove
   r"!f m n p.
       m <= n + 1
       ==> msum(m..n + p) f = msum(m..n) f + msum(n + 1..n + p) f:real^M^N"
   (REWRITE_TAC [CART_EQ_FULL, MSUM_COMPONENT, MATRIX_ADD_COMPONENT] THEN
    SIMP_TAC [SUM_ADD_SPLIT])

  let MSUM_MSUM_PRODUCT ← prove
   r"!s:A->bool t:A->B->bool x.
        FINITE s /\ (!i. i IN s ==> FINITE(t i))
        ==> msum s (\i. msum (t i) (x i)) =
            msum {i,j | i IN s /\ j IN t i} (\(i,j). x i j):real^M^N"
   (REWRITE_TAC [CART_EQ_FULL, MSUM_COMPONENT, COND_COMPONENT] THEN
    SIMP_TAC [SUM_SUM_PRODUCT] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [FUN_EQ_THM, FORALL_PAIR_THM])

  let MSUM_IMAGE_NONZERO ← prove
   r"!d:B->real^M^N i:A->B s.
     FINITE s /\
     (!x y. x IN s /\ y IN s /\ ~(x = y) /\ i x = i y ==> d(i x) = mat 0)
     ==> msum (IMAGE i s) d = msum s (d o i):real^M^N"
   (GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [IMAGE_CLAUSES, MSUM_CLAUSES, FINITE_IMAGE] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:A", ← q r"s:A->bool"] THEN
    REWRITE_TAC [IN_INSERT] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"msum s ((d:B->real^M^N) o (i:A->B)) = msum (IMAGE i s) d")
      SUBST1_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [o_THM] THEN
    REWRITE_TAC [← ma r"a = x + a <=> x = mat 0:real^M^N"] THEN
    ASM_MESON_TAC [IN_IMAGE])

  let MSUM_UNION_NONZERO ← prove
   r"!f:A->real^M^N s t.
     FINITE s /\ FINITE t /\ (!x. x IN s INTER t ==> f(x) = mat 0)
     ==> msum (s UNION t) f = msum s f + msum t f"
   (REWRITE_TAC [CART_EQ_FULL, MSUM_COMPONENT, MATRIX_ADD_COMPONENT,
                 MAT_0_COMPONENT] THEN
    SIMP_TAC [SUM_UNION_NONZERO])

  let MSUM_UNIONS_NONZERO ← prove
   r"!f:A->real^M^N s.
     FINITE s /\ (!t. t IN s ==> FINITE t) /\
     (!t1 t2 x. t1 IN s /\ t2 IN s /\ ~(t1 = t2) /\ x IN t1 /\ x IN t2
                ==> f x = mat 0)
     ==> msum (UNIONS s) f = msum s (\t. msum t f)"
   (GEN_TAC THEN ONCE_REWRITE_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC [UNIONS_0, UNIONS_INSERT, MSUM_CLAUSES, IN_INSERT] THEN
    MAP_EVERY X_GEN_TAC [← q r"t:A->bool", ← q r"s:(A->bool)->bool"] THEN
    DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN
    ONCE_REWRITE_TAC [IMP_CONJ] THEN ASM_SIMP_TAC [MSUM_CLAUSES] THEN
    ANTS_TAC THENL [ASM_MESON_TAC [], DISCH_THEN (SUBST_ALL_TAC o SYM)] THEN
    STRIP_TAC THEN MATCH_MP_TAC MSUM_UNION_NONZERO THEN
    ASM_SIMP_TAC [FINITE_UNIONS, IN_INTER, IN_UNIONS] THEN ASM_MESON_TAC [])

  let MSUM_CLAUSES_LEFT ← prove
   r"!f m n. m <= n ==> msum(m..n) f = f m + msum(m + 1..n) f:real^M^N"
   (SIMP_TAC [msum, CART_EQ, LAMBDA_BETA, MATRIX_ADD_COMPONENT] THEN
    SIMP_TAC [VEC_COMPONENT, SUM_CLAUSES_LEFT])

  let MSUM_DIFFS ← prove
   r"!m n. msum(m..n) (\k. f(k) - f(k + 1)) =
          if m <= n then f(m) - f(n + 1) else mat 0:real^M^N"
   (GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC [MSUM_CLAUSES_NUMSEG, LE] THEN
    ASM_CASES_TAC (← q r"m = SUC n") THEN
    ASM_REWRITE_TAC [← ARITH_RULE (← q r"~(SUC n <= n)"), MATRIX_ADD_LID] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [← GSYM ADD1] THEN MATRIX_ARITH_TAC)

  let MSUM_DIFFS_ALT ← prove
   r"!m n. msum(m..n) (\k. f(k + 1) - f(k)) =
         if m <= n then f(n + 1) - f(m) else mat 0:real^M^N"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [← GSYM MATRIX_NEG_SUB] THEN
    SIMP_TAC [MSUM_NEG, MSUM_DIFFS] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [MATRIX_NEG_SUB, MATRIX_NEG_0])

  let MSUM_DELETE_CASES ← prove
   r"!x f:A->real^M^N s.
        FINITE s
        ==> msum(s DELETE x) f = if x IN s then msum s f - f x else msum s f"
   (REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [← SET_RULE (← q r"~(x:A IN s) ==> s DELETE x = s")] THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
        [← MATCH_MP (← SET_RULE (← q r"x:A IN s ==> s = x INSERT (s DELETE x)")) th])) THEN
    ASM_SIMP_TAC [MSUM_CLAUSES, FINITE_DELETE, IN_DELETE] THEN MATRIX_ARITH_TAC)

  let MSUM_EQ_GENERAL ← prove
   r"!s:A->bool t:B->bool (f:A->real^M^N) g h.
        (!y. y IN t ==> ?!x. x IN s /\ h x = y) /\
        (!x. x IN s ==> h x IN t /\ g(h x) = f x)
        ==> msum s f = msum t g"
   (SIMP_TAC [msum, CART_EQ, LAMBDA_BETA] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_GENERAL THEN
    EXISTS_TAC (← q r"h:A->B") THEN ASM_MESON_TAC [])

  let MSUM_EQ_GENERAL_INVERSES ← prove
   r"!s t (f:A->real^M^N) (g:B->real^M^N) h k.
        (!y. y IN t ==> k y IN s /\ h (k y) = y) /\
        (!x. x IN s ==> h x IN t /\ k (h x) = x /\ g (h x) = f x)
        ==> msum s f = msum t g"
   (SIMP_TAC [msum, CART_EQ, LAMBDA_BETA] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
    MAP_EVERY EXISTS_TAC [← q r"h:A->B", ← q r"k:B->A"] THEN ASM_MESON_TAC [])

  let MSUM_OFFSET ← prove
   r"!p f m n. msum(m + p..n + p) f = msum(m..n) (\i. f (i + p)):real^M^N"
   (REWRITE_TAC [CART_EQ_FULL, MSUM_COMPONENT] THEN SIMP_TAC [SUM_OFFSET])

  let MSUM_OFFSET_0 ← prove
   r"!f m n. m <= n ==> msum(m..n) f = msum(0..n - m) (\i. f (i + m)):real^M^N"
   (REWRITE_TAC [CART_EQ_FULL, MSUM_COMPONENT] THEN SIMP_TAC [SUM_OFFSET_0])

  let MSUM_TRIV_NUMSEG ← prove
   r"!f m n. n < m ==> msum(m..n) f = mat 0:real^M^N"
   (SIMP_TAC [← GSYM NUMSEG_EMPTY, MSUM_CLAUSES])

  let MSUM_CONST_NUMSEG ← prove
   r"!c m n. msum(m..n) (\n. c) = &((n + 1) - m) %% c:real^M^N"
   (SIMP_TAC [MSUM_CONST, FINITE_NUMSEG, CARD_NUMSEG])

  let MSUM_SUC ← prove
   r"!f m n. msum (SUC n..SUC m) f = msum (n..m) (f o SUC):real^M^N"
   (REPEAT GEN_TAC THEN
    SUBGOAL_THEN (← q r"SUC n..SUC m = IMAGE SUC (n..m)") SUBST1_TAC THENL
     [REWRITE_TAC [ADD1, NUMSEG_OFFSET_IMAGE] THEN
      REWRITE_TAC [ONE, ADD_SUC, ADD_0, ETA_AX],
      SIMP_TAC [MSUM_IMAGE, FINITE_NUMSEG, SUC_INJ]])

  let MSUM_BIJECTION ← prove
   r"!f:A->real^M^N p s:A->bool.
                (!x. x IN s ==> p(x) IN s) /\
                (!y. y IN s ==> ?!x. x IN s /\ p(x) = y)
                ==> msum s f = msum s (f o p)"
   (REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC MSUM_EQ_GENERAL THEN EXISTS_TAC (← q r"p:A->A") THEN
    ASM_REWRITE_TAC [o_THM])

  let MSUM_PARTIAL_SUC ← prove
   r"!f g:num->real^M^N m n.
        msum (m..n) (\k. f(k) %% (g(k + 1) - g(k))) =
            if m <= n then f(n + 1) %% g(n + 1) - f(m) %% g(m) -
                           msum (m..n) (\k. (f(k + 1) - f(k)) %% g(k + 1))
            else mat 0"
   (GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [MSUM_TRIV_NUMSEG, ← GSYM NOT_LE] THEN
    ASM_REWRITE_TAC [MSUM_CLAUSES_NUMSEG] THENL
     [COND_CASES_TAC THEN ASM_SIMP_TAC [ARITH] THENL
       [MATRIX_ARITH_TAC, ASM_ARITH_TAC],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [LE]) THEN
    DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
    ASM_SIMP_TAC [← GSYM NOT_LT, MSUM_TRIV_NUMSEG, ← ARITH_RULE (← q r"n < SUC n")] THEN
    ASM_SIMP_TAC [← GSYM ADD1, ADD_CLAUSES] THEN MATRIX_ARITH_TAC)

  let MSUM_PARTIAL_PRE ← prove
   r"!f g:num->real^M^N m n.
        msum (m..n) (\k. f(k) %% (g(k) - g(k - 1))) =
            if m <= n then f(n + 1) %% g(n) - f(m) %% g(m - 1) -
                           msum (m..n) (\k. (f(k + 1) - f(k)) %% g(k))
            else mat 0"
   (REPEAT GEN_TAC THEN
    MP_TAC (← ISPECL [← q r"f:num->real", ← q r"\k. (g:num->real^M^N)(k - 1)",
                      ← q r"m:num", ← q r"n:num"] MSUM_PARTIAL_SUC) THEN
    REWRITE_TAC [ADD_SUB] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC [])

  let MSUM_COMBINE_L ← prove
   r"!f m n p.
        0 < n /\ m <= n /\ n <= p + 1
        ==> msum(m..n - 1) f + msum(n..p) f = msum(m..p) f:real^M^N"
   (REWRITE_TAC [CART_EQ_FULL, MSUM_COMPONENT, MATRIX_ADD_COMPONENT] THEN
    SIMP_TAC [SUM_COMBINE_L])

  let MSUM_COMBINE_R ← prove
   r"!f m n p.
        m <= n + 1 /\ n <= p
        ==> msum(m..n) f + msum(n + 1..p) f = msum(m..p) f:real^M^N"
   (REWRITE_TAC [CART_EQ_FULL, MSUM_COMPONENT, MATRIX_ADD_COMPONENT] THEN
    SIMP_TAC [SUM_COMBINE_R])

  let MSUM_INJECTION ← prove
   r"!f:A->real^M^N p:A->A s.
     FINITE s /\
     (!x. x IN s ==> p x IN s) /\
     (!x y. x IN s /\ y IN s /\ p x = p y ==> x = y)
     ==> msum s (f o p) = msum s f"
   (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP SUM_INJECTION) THEN
    REWRITE_TAC [CART_EQ_FULL, MSUM_COMPONENT, o_DEF] THEN SIMP_TAC [])

  let MSUM_SWAP ← prove
   r"!f:A->B->real^M^N s t.
     FINITE s /\ FINITE t
     ==> msum s (\i. msum t (f i)) = msum t (\j. msum s (\i. f i j))"
   (REWRITE_TAC [CART_EQ_FULL, MSUM_COMPONENT] THEN REPEAT STRIP_TAC THEN
    W (MP_TAC o PART_MATCH (lhs o rand) SUM_SWAP o lhs o snd) THEN
    ASM_REWRITE_TAC [])

  let MSUM_SWAP_NUMSEG ← prove
   r"!a b c d f.
         msum (a..b) (\i. msum (c..d) (f i)) =
         msum (c..d) (\j. msum (a..b) (\i. f i j)):real^M^N"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC MSUM_SWAP THEN REWRITE_TAC [FINITE_NUMSEG])

  let MSUM_ADD_GEN ← prove
   r"!f g:A->real^M^N s.
       FINITE {x | x IN s /\ ~(f x = mat 0)} /\
       FINITE {x | x IN s /\ ~(g x = mat 0)}
       ==> msum s (\x. f x + g x) = msum s f + msum s g"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [CART_EQ_FULL, MSUM_COMPONENT, MATRIX_ADD_COMPONENT] THEN
    SIMP_TAC [CART_EQ, msum, LAMBDA_BETA, MATRIX_ADD_COMPONENT] THEN
    REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_ADD_GEN THEN
    POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_AND THEN
    CONJ_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] FINITE_SUBSET) THEN
    REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN GEN_TAC THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN REWRITE_TAC [DE_MORGAN_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [MAT_0_COMPONENT])

  let MSUM_CASES_1 ← prove
   r"!s a:A. FINITE s /\ a IN s
           ==> msum s (\x. if x = a then y else f(x)) =
               msum s f + (y - f a):real^M^N"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [MSUM_CASES] THEN
    ASM_SIMP_TAC [← GSYM DELETE, MSUM_DELETE] THEN
    ASM_SIMP_TAC [← SET_RULE (← q r"a:A IN s ==> {x | x IN s /\ x = a} = {a}")] THEN
    REWRITE_TAC [MSUM_SING] THEN MATRIX_ARITH_TAC)

  let MSUM_SING_NUMSEG ← prove
   r"msum(n..n) f = f n:real^M^N"
   (REWRITE_TAC [NUMSEG_SING, MSUM_SING])

  let MSUM_1 ← prove
   r"msum(1..1) f = f(1):real^M^N"
   (REWRITE_TAC [MSUM_SING_NUMSEG])

  let MSUM_2 ← prove
   r"!t. msum(1..2) t = t(1) + t(2):real^M^N"
   (REWRITE_TAC [← numc "2", MSUM_CLAUSES_NUMSEG] THEN
    REWRITE_TAC [MSUM_SING_NUMSEG, ARITH, REAL_ADD_ASSOC])

  let MSUM_3 ← prove
   r"!t. msum(1..3) t = t(1) + t(2) + t(3):real^M^N"
   (REWRITE_TAC [← numc "3", ← numc "2", MSUM_CLAUSES_NUMSEG] THEN
    REWRITE_TAC [MSUM_SING_NUMSEG, ARITH, MATRIX_ADD_ASSOC])

  let MSUM_4 ← prove
   r"!t. msum(1..4) t = t(1) + t(2) + t(3) + t(4):real^M^N"
   (SIMP_TAC [← numc "4", ← numc "3", ← numc "2", MSUM_CLAUSES_NUMSEG] THEN
    REWRITE_TAC [MSUM_SING_NUMSEG, ARITH, MATRIX_ADD_ASSOC])

  let MSUM_PAIR ← prove
   r"!f:num->real^M^N m n.
        msum(2*m..2*n+1) f = msum(m..n) (\i. f(2*i) + f(2*i+1))"
   (REWRITE_TAC [CART_EQ_FULL, MSUM_COMPONENT, MATRIX_ADD_COMPONENT, SUM_PAIR])

  let MSUM_PAIR_0 ← prove
   r"!f:num->real^M^N n. msum(0..2*n+1) f = msum(0..n) (\i. f(2*i) + f(2*i+1))"
   (REPEAT GEN_TAC THEN
    MP_TAC (← ISPECL [← q r"f:num->real^M^N", ← q r"0", ← q r"n:num"] MSUM_PAIR) THEN
    ASM_REWRITE_TAC [ARITH])

  let MSUM_REFLECT ← prove
   r"!x m n. msum(m..n) x =
           if n < m then mat 0 else msum(0..n-m) (\i. x(n - i)):real^M^N"
   (REPEAT GEN_TAC THEN SIMP_TAC [MSUM, FINITE_NUMSEG] THEN
    GEN_REWRITE_TAC LAND_CONV [← MATCH_MP ITERATE_REFLECT MONOIDAL_MATRIX_ADD] THEN
    REWRITE_TAC [NEUTRAL_MATRIX_ADD])

  return { MSUM_CLAUSES_NUMSEG, MSUM_CLAUSES_RIGHT, MSUM_CMUL_NUMSEG, MSUM_EQ_NUMSEG,
           MSUM_IMAGE_GEN, MSUM_GROUP, MSUM_GROUP_RELATION, MSUM_VMUL, MSUM_DELTA,
           MSUM_ADD_NUMSEG, MSUM_SUB_NUMSEG, MSUM_ADD_SPLIT, MSUM_MSUM_PRODUCT,
           MSUM_IMAGE_NONZERO, MSUM_UNION_NONZERO, MSUM_UNIONS_NONZERO, MSUM_CLAUSES_LEFT,
           MSUM_DIFFS, MSUM_DIFFS_ALT, MSUM_DELETE_CASES, MSUM_EQ_GENERAL,
           MSUM_EQ_GENERAL_INVERSES, MSUM_OFFSET, MSUM_OFFSET_0, MSUM_TRIV_NUMSEG,
           MSUM_CONST_NUMSEG, MSUM_SUC, MSUM_BIJECTION, MSUM_PARTIAL_SUC, MSUM_PARTIAL_PRE,
           MSUM_COMBINE_L, MSUM_COMBINE_R, MSUM_INJECTION, MSUM_SWAP, MSUM_SWAP_NUMSEG,
           MSUM_ADD_GEN, MSUM_CASES_1, MSUM_SING_NUMSEG, MSUM_1, MSUM_2, MSUM_3, MSUM_4,
           MSUM_PAIR, MSUM_PAIR_0, MSUM_REFLECT }

end HolMultiLib.MSum
