/- ========================================================================= -/
/- ANT: The Minkowski linear forms theorem for real matrices, type-free    -/
/- ========================================================================= -/
/- File: HolANT/LinearForms.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/linear_forms.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antlinearformsdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/permutations.ml, Library/isum.ml, Library/products.ml, Library/floor.ml, ANT/algmisc.ml, Library/ring_det.ml, ANT/zlattice.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.LinearForms fills them).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left; where a proof applies rules that print or use
  counters (MESON, ARITH_RULE, ...) they are bound first, in OCaml's order.
-/

import HolANT.Prelude
import HolLibrary.Binomial
import HolLibrary.Iter
import HolLibrary.Prime
import HolLibrary.Pocklington
import HolLibrary.Wo
import HolLibrary.Card
import HolLibrary.RingTheory
import HolLibrary.Permutations
import HolLibrary.Isum
import HolLibrary.Products
import HolLibrary.Floor
import HolANT.Algmisc
import HolLibrary.RingDet
import HolANT.Zlattice

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.Algmisc
open HolANT.Zlattice

namespace HolANT.LinearForms

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (CARD_CLAUSES CARD_EQ_0 CARD_PERMUTATIONS CARD_SUBSET EQ_SYM_EQ EQ_TRANS
   EXTENSION FINITE_FUNSPACE FINITE_IMAGE FINITE_INDUCT_STRONG FINITE_INSERT
   FINITE_INT_SEG FINITE_PERMUTATIONS FINITE_SING FINITE_SUBSET FLOOR
   FORALL_IN_IMAGE FORALL_IN_INSERT FUN_EQ_THM HAS_SIZE HAS_SIZE_FUNSPACE
   HAS_SIZE_IMAGE_INJ HAS_SIZE_INT_SEG_LT IMP_CONJ INTEGER_RING
   INTEGRAL_DOMAIN_REAL_RING INT_ABS_BOUNDS INT_ABS_POS INT_COSETS_MATRIX_IMAGE
   INT_ENTIRE INT_LATTICE_0 INT_LATTICE_INT_MATRIX_IMAGE INT_MATRIX_IMAGE_IN
   INT_MUL_RZERO INT_OF_NUM_LT INT_OF_NUM_OF_INT INT_SUB_0 INT_SUB_REFL
   IN_ELIM_THM IN_INSERT IN_SING IN_UNIV ISUM_EQ ISUM_EQ_0 LEFT_IMP_EXISTS_THM
   LE_1 LE_REFL LT_IMP_LE MEMBER_NOT_EMPTY MONO_EXISTS NOT_EXISTS_THM
   NOT_FORALL_THM NOT_IMP NOT_LE PERMUTES_IN_IMAGE PRODUCT_ABS PRODUCT_CLAUSES
   PRODUCT_CONST PRODUCT_INV PRODUCT_LE PRODUCT_MUL PRODUCT_POS_LT REAL_ABS_INV
   REAL_ABS_MUL REAL_ABS_NUM REAL_ABS_NZ REAL_ABS_POS REAL_ADD_RDISTRIB
   REAL_ADD_RID REAL_ARCH REAL_ARCH_INV REAL_ARCH_SIMPLE REAL_DIV_LMUL
   REAL_ENTIRE REAL_EQ_IMP_LE REAL_FIELD_CLAUSES REAL_INV_EQ_0 REAL_INV_LE_1
   REAL_LET_TRANS REAL_LE_INV2 REAL_LE_LADD REAL_LE_LMUL REAL_LE_LMUL_EQ
   REAL_LE_MUL REAL_LE_MUL2 REAL_LE_REFL REAL_LE_RMUL REAL_LE_SQUARE_ABS : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (REAL_LE_TRANS REAL_LT_ADDR REAL_LT_DIV REAL_LT_IMP_LE REAL_LT_IMP_NZ
   REAL_LT_INV_EQ REAL_LT_LDIV_EQ REAL_LT_LMUL REAL_LT_LMUL_EQ REAL_LT_MIN
   REAL_LT_MUL REAL_LT_RDIV_EQ REAL_LT_RMUL REAL_MIN_MIN REAL_MUL_ASSOC
   REAL_MUL_LID REAL_MUL_LZERO REAL_MUL_RID REAL_MUL_RZERO REAL_MUL_SYM
   REAL_NOT_LE REAL_NOT_LT REAL_OF_INT_OF_REAL REAL_OF_NUM_ADD REAL_OF_NUM_LE
   REAL_OF_NUM_LT REAL_OF_NUM_POW REAL_OF_NUM_SUB REAL_POS REAL_POW_EQ_0
   REAL_POW_LE REAL_POW_LT REAL_POW_LT_1 REAL_POW_MUL REAL_RING_CLAUSES
   REAL_RING_OF_INT REAL_RING_PRODUCT REAL_RING_SUM REAL_SUB_LDISTRIB
   REAL_SUB_LT RIGHT_IMP_EXISTS_THM RING_DET_ADJUGATE_COLUMNS
   RING_DET_BLOCK_TRIANGULAR RING_DET_CMUL RING_DET_DEPENDENT_COLUMNS
   RING_DET_EMPTY RING_DET_EQ RING_DET_HOMOMORPHISM RING_DET_I RING_DET_MUL
   RING_DET_ROWS_MUL RING_DET_SING RING_DET_TRANSP
   RING_HOMOMORPHISM_INTEGER_RING_OF_INT SKOLEM_THM SUBSET SUC_SUB1
   SUM_ABS_BOUND SUM_ABS_LE SUM_ADD SUM_BOUND SUM_CLAUSES SUM_CONST SUM_DELTA
   SUM_EQ SUM_EQ_0 SUM_LE SUM_LMUL SUM_POS_BOUND SUM_POS_LE SUM_RMUL SUM_SUB
   SUM_SWAP int_abs_th int_cosets int_divides int_eq int_isum int_le int_lt
   int_mul_th int_of_num_th num_FINITE real_div real_pow ring_det ring_sign : thm)
  deriving Inhabited

/-- What linear_forms.ml uses from Session besides theorems. -/
structure LinearFormsDeps where
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
  PRIME_CONV : term → ExceptT String IO thm  -- pocklington.ml's PRIME_CONV
  PRIME_RULE : List String → term → ExceptT String IO thm  -- pocklington.ml's PRIME_RULE
  RING_RULE : term → ExceptT String IO thm  -- ringtheory.ml's RING_RULE
  INTEGRAL_DOMAIN_RULE : term → ExceptT String IO thm
  FIELD_TAC : tactic  -- ringtheory.ml's FIELD_TAC
  RING_CARRIER_TAC : tactic
  RING_TAC : tactic
  RING_PULL_DIV_TAC : tactic
  LET_TAC : tactic
  basic_ss : List thm → IO (Except String HolCore.Simp.simpset)
  INTEGER_MOD_RING_RED_CONV : ioconv
  NUM_SUB_CONV : ioconv
  REAL_RAT_REDUCE_CONV : ioconv
  NUM_EQ_CONV : ioconv
  NUM_DIV_CONV : ioconv
  EXP_MOD_CONV : ioconv
  EXPAND_CASES_CONV : ioconv
  DIVIDES_CONV : ioconv  -- prime.ml's DIVIDES_CONV
  COPRIME_CONV : ioconv
  REAL_RING : term → ExceptT String IO thm
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



/- ---------------------------------------------------------------------- -/
/- linear_forms.ml phrases from line 50 to 689                            -/
/- ---------------------------------------------------------------------- -/

structure LinearForms01 where
  -- @@FIELDS
  PRODUCT_SUB_BOUND : thm
  REAL_DET_SUB_BOUND : thm
  REAL_MATRIX_LEFT_INVERSE : thm
  INT_MATRIX_PIGEONHOLE : thm
  REAL_DET_ROUNDING : thm
  MINKOWSKI_LINEAR_FORMS_STRICT : thm
  MINKOWSKI_LINEAR_FORMS : thm
  QUADRATIC_FORM_COMPLETE_SQUARE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupLinearForms01 [HolBase] (D : LinearFormsDeps) :
    ExceptT String IO LinearForms01 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_REAL_ARITH_TAC, INT_ARITH, REAL_ARITH,
        REAL_ARITH_TAC, REAL_FIELD, REAL_RING, TAUT, .. } := D
  let { CARD_CLAUSES, CARD_EQ_0, CARD_PERMUTATIONS, CARD_SUBSET, EQ_SYM_EQ, EQ_TRANS,
        EXTENSION, FINITE_FUNSPACE, FINITE_IMAGE, FINITE_INDUCT_STRONG, FINITE_INT_SEG,
        FINITE_PERMUTATIONS, FINITE_SUBSET, FLOOR, FORALL_IN_IMAGE, FORALL_IN_INSERT,
        FUN_EQ_THM, HAS_SIZE, HAS_SIZE_FUNSPACE, HAS_SIZE_IMAGE_INJ,
        HAS_SIZE_INT_SEG_LT, IMP_CONJ, INTEGER_RING, INT_ABS_BOUNDS, INT_ABS_POS,
        INT_COSETS_MATRIX_IMAGE, INT_LATTICE_0, INT_LATTICE_INT_MATRIX_IMAGE,
        INT_MATRIX_IMAGE_IN, INT_MUL_RZERO, INT_OF_NUM_LT, INT_OF_NUM_OF_INT,
        INT_SUB_0, INT_SUB_REFL, IN_ELIM_THM, IN_UNIV, ISUM_EQ, ISUM_EQ_0,
        LEFT_IMP_EXISTS_THM, LE_1, LE_REFL, LT_IMP_LE, MEMBER_NOT_EMPTY, MONO_EXISTS,
        NOT_EXISTS_THM, NOT_FORALL_THM, NOT_IMP, NOT_LE, PERMUTES_IN_IMAGE,
        PRODUCT_ABS, PRODUCT_CLAUSES, PRODUCT_CONST, PRODUCT_INV, PRODUCT_LE,
        PRODUCT_MUL, PRODUCT_POS_LT, REAL_ABS_INV, REAL_ABS_MUL, REAL_ABS_NUM,
        REAL_ABS_NZ, REAL_ABS_POS, REAL_ARCH, REAL_ARCH_INV, REAL_ARCH_SIMPLE,
        REAL_DIV_LMUL, REAL_ENTIRE, REAL_FIELD_CLAUSES, REAL_INV_EQ_0, REAL_INV_LE_1,
        REAL_LET_TRANS, REAL_LE_INV2, REAL_LE_LADD, REAL_LE_LMUL, REAL_LE_LMUL_EQ,
        REAL_LE_MUL, REAL_LE_MUL2, REAL_LE_REFL, REAL_LE_RMUL, .. } := D.core1
  let { REAL_LE_TRANS, REAL_LT_ADDR, REAL_LT_DIV, REAL_LT_IMP_LE, REAL_LT_IMP_NZ,
        REAL_LT_INV_EQ, REAL_LT_LDIV_EQ, REAL_LT_LMUL, REAL_LT_LMUL_EQ, REAL_LT_MIN,
        REAL_LT_MUL, REAL_LT_RDIV_EQ, REAL_MIN_MIN, REAL_MUL_ASSOC, REAL_MUL_LID,
        REAL_MUL_LZERO, REAL_MUL_RID, REAL_MUL_RZERO, REAL_MUL_SYM, REAL_NOT_LE,
        REAL_OF_INT_OF_REAL, REAL_OF_NUM_ADD, REAL_OF_NUM_LE, REAL_OF_NUM_LT,
        REAL_OF_NUM_POW, REAL_OF_NUM_SUB, REAL_POS, REAL_POW_LE, REAL_POW_LT,
        REAL_POW_LT_1, REAL_POW_MUL, REAL_RING_CLAUSES, REAL_RING_OF_INT,
        REAL_RING_PRODUCT, REAL_RING_SUM, REAL_SUB_LDISTRIB, REAL_SUB_LT,
        RIGHT_IMP_EXISTS_THM, RING_DET_ADJUGATE_COLUMNS, RING_DET_CMUL, RING_DET_EMPTY,
        RING_DET_HOMOMORPHISM, RING_DET_ROWS_MUL,
        RING_HOMOMORPHISM_INTEGER_RING_OF_INT, SKOLEM_THM, SUBSET, SUC_SUB1,
        SUM_ABS_BOUND, SUM_ABS_LE, SUM_ADD, SUM_BOUND, SUM_CLAUSES, SUM_CONST,
        SUM_DELTA, SUM_EQ, SUM_LE, SUM_LMUL, SUM_POS_BOUND, SUM_POS_LE, SUM_RMUL,
        SUM_SUB, SUM_SWAP, int_abs_th, int_cosets, int_eq, int_isum, int_le, int_lt,
        int_mul_th, int_of_num_th, num_FINITE, real_div, real_pow, ring_det, ring_sign, .. } := D.core2
  -- @@SCOPE END

  let PRODUCT_SUB_BOUND ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"abs(x * p - y * q) <= abs((x - y) * p) + abs(y * (p - q)) /\
      abs((x - y) * p) <= u /\ abs(y * (p - q)) <= v
      ==> abs(x * p - y * q:real) <= u + v")
    let r2 ← ARITH_RULE (← q r"~(n = 0) ==> SUC(n - 1) = n")
    prove
      r"!s (f:A->real) g B.
          FINITE s /\ (!i. i IN s ==> abs(f i) <= B /\ abs(g i) <= B)
          ==> abs(product s f - product s g) <=
              B pow (CARD s - 1) * sum s (\i. abs(f i - g i))"
      (GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [IMP_CONJ] THEN SPEC_TAC ((← q r"s:A->bool"), (← q r"s:A->bool")) THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN SIMP_TAC [PRODUCT_CLAUSES, SUM_CLAUSES, CARD_CLAUSES, FORALL_IN_INSERT] THEN CONJ_TAC THENL [REAL_ARITH_TAC, ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"t:A->bool")] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun z3 => (do let z4 ← (do let z5 ← (pure z3); pure (concl z5)); pure (is_imp z4))))) THEN ASM_REWRITE_TAC [SUC_SUB1] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"abs(product t (f:A->real)) <= B pow CARD(t:A->bool)") ASSUME_TAC THENL [ASM_SIMP_TAC [(← GSYM PRODUCT_ABS), (← GSYM PRODUCT_CONST)] THEN MATCH_MP_TAC PRODUCT_LE THEN ASM_SIMP_TAC [REAL_ABS_POS], ALL_TAC] THEN SUBGOAL_THEN (← q r"B * B pow (CARD(t:A->bool) - 1) * sum t (\i. abs(f i - g i)) =
      B pow CARD t * sum t (\i. abs((f:A->real) i - g i))") ASSUME_TAC THENL [ASM_CASES_TAC (← q r"t:A->bool = {}") THEN ASM_REWRITE_TAC [SUM_CLAUSES, REAL_MUL_RZERO] THEN ASM_SIMP_TAC [REAL_MUL_ASSOC, (← GSYM (← CONJUNCT2 real_pow)), CARD_EQ_0, r2], ALL_TAC] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"abs((f:A->real) a - g a) * B pow CARD(t:A->bool) +
                B * B pow (CARD t - 1) * sum t (\i. abs(f i - g i))") THEN CONJ_TAC THENL [MATCH_MP_TAC r1 THEN REPEAT CONJ_TAC THENL [REAL_ARITH_TAC, REWRITE_TAC [REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC [REAL_ABS_POS], REWRITE_TAC [REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC [REAL_ABS_POS]], ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC])

  let REAL_DET_SUB_BOUND ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"n * b * d:real = b * n * d")
    let r2 ← REAL_ARITH (← q r"(a:real) <= b ==> x <= a ==> x <= b")
    prove
      r"!s (f:A->A->real) g B d.
          FINITE s /\
          (!i j. i IN s /\ j IN s
                 ==> abs(f i j) <= B /\ abs(g i j) <= B /\
                     abs(f i j - g i j) <= d)
          ==> abs(ring_det real_ring s f - ring_det real_ring s g) <=
              &(FACT(CARD s)) * &(CARD s) * B pow (CARD s - 1) * d"
      (REPEAT STRIP_TAC THEN REWRITE_TAC [ring_det, ring_sign, REAL_RING_CLAUSES, REAL_RING_SUM, REAL_RING_PRODUCT] THEN ASM_SIMP_TAC [(← GSYM SUM_SUB), FINITE_PERMUTATIONS, (← GSYM CARD_PERMUTATIONS)] THEN MATCH_MP_TAC SUM_ABS_BOUND THEN ASM_SIMP_TAC [FINITE_PERMUTATIONS, IN_ELIM_THM] THEN X_GEN_TAC (← q r"p:A->A") THEN DISCH_TAC THEN REWRITE_TAC [(← GSYM REAL_SUB_LDISTRIB), REAL_ABS_MUL] THEN SUBGOAL_THEN (← q r"abs(if evenperm(p:A->A) then &1 else -- &1) = &1:real") SUBST1_TAC THENL [COND_CASES_TAC THEN REAL_ARITH_TAC, REWRITE_TAC [REAL_MUL_LID]] THEN MP_TAC (← ISPECL [(← q r"s:A->bool"), (← q r"\i. (f:A->A->real) i (p i)"), (← q r"\i. (g:A->A->real) i (p i)"), (← q r"B:real")] PRODUCT_SUB_BOUND) THEN ASM_SIMP_TAC [PERMUTES_IN_IMAGE] THEN MATCH_MP_TAC r2 THEN ONCE_REWRITE_TAC [r1] THEN ASM_CASES_TAC (← q r"s:A->bool = {}") THEN ASM_REWRITE_TAC [SUM_CLAUSES, CARD_CLAUSES, REAL_MUL_RZERO, REAL_MUL_LZERO, REAL_LE_REFL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE THEN FIRST_X_ASSUM ((X_CHOOSE_TAC (← q r"a:A")) o (GEN_REWRITE_RULE id [(← GSYM MEMBER_NOT_EMPTY)])) THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"abs((f:A->A->real) a a)") THEN ASM_SIMP_TAC [REAL_ABS_POS], MATCH_MP_TAC SUM_BOUND THEN ASM_SIMP_TAC [PERMUTES_IN_IMAGE]])

  let REAL_MATRIX_LEFT_INVERSE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"c / d * a * z:real = (c * a) * z / d")
    prove
      r"!s (A:K->K->real).
          FINITE s /\ ~(ring_det real_ring s A = &0)
          ==> ?C. !z i. i IN s
                        ==> sum s (\j. C i j * sum s (\k. A j k * z k)) = z i"
      (REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"\i j. ring_cofactor real_ring s (A:K->K->real) j i /
                      ring_det real_ring s A") THEN MAP_EVERY X_GEN_TAC [(← q r"z:K->real"), (← q r"i:K")] THEN DISCH_TAC THEN REWRITE_TAC [(← GSYM SUM_LMUL)] THEN wPart lhand (lhand o rand) SUM_SWAP THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"real_ring"), (← q r"s:K->bool"), (← q r"A:K->K->real"), (← q r"i:K")] RING_DET_ADJUGATE_COLUMNS) THEN ASM_REWRITE_TAC [REAL_RING_CLAUSES, REAL_RING_SUM, IN_UNIV] THEN DISCH_TAC THEN TRANS_TAC EQ_TRANS (← q r"sum s (\k. if k = i then (z:K->real) i else &0)") THEN CONJ_TAC THENL [ALL_TAC, ASM_REWRITE_TAC [SUM_DELTA]] THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC (← q r"k:K") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"k:K"))) THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [r1] THEN REWRITE_TAC [SUM_RMUL] THEN DISCH_THEN SUBST1_TAC THEN ASM_CASES_TAC (← q r"k:K = i") THENL [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC [REAL_DIV_LMUL], ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"~(i:K = k)") (fun th => REWRITE_TAC [th, REAL_MUL_LZERO]) THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN ASM_REWRITE_TAC []])

  let INT_MATRIX_PIGEONHOLE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"~(a /\ ~b) <=> a ==> b")
    let r2 ← TAUT (← q r"(~q ==> p) ==> ~p ==> q")
    let r3 ← INT_ARITH (← q r"&0 <= x /\ x < n /\ &0 <= y /\ y < n ==> abs(x - y:int) < n")
    let r4 ← TAUT (← q r"~(a /\ b /\ ~c /\ d) <=> a /\ b /\ d ==> c")
    let r5 ← TAUT (← q r"(~p ==> F) ==> p")
    prove
      r"!s (M:K->K->int) N.
          FINITE s /\ ~(ring_det integer_ring s M = &0) /\
          num_of_int(abs(ring_det integer_ring s M)) < N EXP CARD s
          ==> ?x. (!j. ~(j IN s) ==> x j = &0) /\
                  (?j. j IN s /\ ~(x j = &0)) /\
                  !i. i IN s ==> abs(isum s (\j. M i j * x j)) < &N"
      (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"L = int_matrix_image s (M:K->K->int)") THEN ABBREV_TAC (← q r"G = {g:K->int | (!i. i IN s ==> g i IN {k | &0 <= k /\ k < &N}) /\
                      (!i. ~(i IN s) ==> g i = &0)}") THEN SUBGOAL_THEN (← q r"(G:(K->int)->bool) HAS_SIZE N EXP CARD(s:K->bool)") ASSUME_TAC THENL [EXPAND_TAC "G" THEN MATCH_MP_TAC HAS_SIZE_FUNSPACE THEN ASM_REWRITE_TAC [HAS_SIZE_INT_SEG_LT, HAS_SIZE], ALL_TAC] THEN SUBGOAL_THEN (← q r"(\i:K. &0:int) IN L") ASSUME_TAC THENL [EXPAND_TAC "L" THEN MATCH_MP_TAC INT_LATTICE_0 THEN EXISTS_TAC (← q r"s:K->bool") THEN ASM_SIMP_TAC [INT_LATTICE_INT_MATRIX_IMAGE], ALL_TAC] THEN SUBGOAL_THEN (← q r"!g:K->int. g IN G <=>
                 (!i. i IN s ==> &0 <= g i /\ g i < &N) /\
                 (!i. ~(i IN s) ==> g i = &0)") ASSUME_TAC THENL [EXPAND_TAC "G" THEN REWRITE_TAC [IN_ELIM_THM], ALL_TAC] THEN SUBGOAL_THEN (← q r"?g g'. g IN G /\ g' IN G /\ ~(g = g') /\
             (\i. (g:K->int) i - g' i) IN L") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r5 THEN DISCH_THEN ((LABEL_TAC "inj") o (REWRITE_RULE [NOT_EXISTS_THM, r4])) THEN MP_TAC (← ISPECL [(← q r"s:K->bool"), (← q r"M:K->K->int")] INT_COSETS_MATRIX_IMAGE) THEN MP_TAC (← ISPECL [(← q r"\g:K->int. {y | (!i. ~(i IN s) ==> y i = &0) /\
                         (\i. y i - g i) IN L}"), (← q r"G:(K->int)->bool"), (← q r"N EXP CARD(s:K->bool)")] HAS_SIZE_IMAGE_INJ) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [MAP_EVERY X_GEN_TAC [(← q r"g:K->int"), (← q r"g':K->int")] THEN REWRITE_TAC [] THEN STRIP_TAC THEN REMOVE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"g:K->int")) o (REWRITE_RULE [EXTENSION]))) THEN ASM_REWRITE_TAC [IN_ELIM_THM, INT_SUB_REFL], ALL_TAC] THEN REWRITE_TAC [HAS_SIZE] THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"IMAGE (\g:K->int. {y | (!i. ~(i IN s) ==> y i = &0) /\
                               (\i. y i - g i) IN L}) G"), (← q r"int_cosets s (L:(K->int)->bool)")] CARD_SUBSET) THEN ASM_REWRITE_TAC [NOT_IMP, NOT_LE] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, int_cosets, IN_ELIM_THM] THEN X_GEN_TAC (← q r"g:K->int") THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN EXISTS_TAC (← q r"g:K->int") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(!i. i IN s ==> abs((g:K->int) i - g' i) < &N) /\
      (!i. ~(i IN s) ==> g i = g' i)") STRIP_ASSUME_TAC THENL [MAP_EVERY UNDISCH_TAC [(← q r"(g:K->int) IN G"), (← q r"(g':K->int) IN G")] THEN ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [] THEN MATCH_MP_TAC r3 THEN ASM_SIMP_TAC [], ALL_TAC] THEN UNDISCH_TAC (← q r"(\i. (g:K->int) i - g' i) IN L") THEN EXPAND_TAC "L" THEN REWRITE_TAC [INT_MATRIX_IMAGE_IN, FUN_EQ_THM] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"z:K->int")) THEN EXISTS_TAC (← q r"\j. if j IN s then (z:K->int) j else &0") THEN SUBGOAL_THEN (← q r"!i. isum s (\j. (M:K->K->int) i j * (if j IN s then z j else &0)) =
          isum s (\j. M i j * z j)") (fun th => REWRITE_TAC [th]) THENL [GEN_TAC THEN MATCH_MP_TAC ISUM_EQ THEN SIMP_TAC [], ALL_TAC] THEN REPEAT CONJ_TAC THENL [SIMP_TAC [], UNDISCH_TAC (← q r"~(g:K->int = g')") THEN MATCH_MP_TAC r2 THEN REWRITE_TAC [NOT_EXISTS_THM, r1] THEN DISCH_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"i:K") THEN ASM_CASES_TAC (← q r"(i:K) IN s") THEN ASM_SIMP_TAC [] THEN ONCE_REWRITE_TAC [(← GSYM INT_SUB_0)] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC ISUM_EQ_0 THEN X_GEN_TAC (← q r"j:K") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"j:K"))) THEN ASM_SIMP_TAC [INT_MUL_RZERO], X_GEN_TAC (← q r"i:K") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"i:K"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC []])

  let REAL_DET_ROUNDING ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"&0 < p ==> abs p = p:real")
    let r2 ← REAL_ARITH (← q r"&D <= q ==> abs(q - &D) <= q /\ abs(q - (q - &D)) = &D:real")
    let r3 ← ARITH_RULE (← q r"~(n = 0) ==> SUC(n - 1) = n")
    let r4 ← ARITH_RULE (← q r"1 <= Q <=> 0 < Q")
    prove
      r"!s (A:K->K->real) D.
          FINITE s /\ ~(ring_det real_ring s A = &0) /\
          abs(ring_det real_ring s A) < &1
          ==> ?Q M:K->K->int.
                  D < Q /\
                  (!i j. real_of_int(M i j) <= &Q * A i j /\
                         &Q * A i j < real_of_int(M i j) + &1) /\
                  ~(ring_det integer_ring s M = &0) /\
                  num_of_int(abs(ring_det integer_ring s M)) <
                  (Q - D) EXP CARD s"
      (REPEAT GEN_TAC THEN ABBREV_TAC (← q r"n = CARD(s:K->bool)") THEN ABBREV_TAC (← q r"a = ring_det real_ring s (A:K->K->real)") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"~(n = 0)") ASSUME_TAC THENL [EXPAND_TAC "n" THEN ASM_SIMP_TAC [CARD_EQ_0] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"ring_det real_ring s (A:K->K->real) = a") THEN ASM_REWRITE_TAC [RING_DET_EMPTY, REAL_RING_CLAUSES] THEN UNDISCH_TAC (← q r"abs(a:real) < &1") THEN REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"?R. &0 <= R /\ !i j. i IN s /\ j IN s ==> abs((A:K->K->real) i j) <= R") STRIP_ASSUME_TAC THENL [EXISTS_TAC (← q r"sum s (\i. sum s (\j. abs((A:K->K->real) i j)))") THEN SIMP_TAC [SUM_POS_LE, REAL_ABS_POS] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"sum s (\j. abs((A:K->K->real) i j))") THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"\j. abs((A:K->K->real) i j)"), (← q r"sum s (\j. abs((A:K->K->real) i j))"), (← q r"s:K->bool")] SUM_POS_BOUND), MP_TAC (← ISPECL [(← q r"\i. sum s (\j. abs((A:K->K->real) i j))"), (← q r"sum s (\i. sum s (\j. abs((A:K->K->real) i j)))"), (← q r"s:K->bool")] SUM_POS_BOUND)] THEN ASM_SIMP_TAC [REAL_LE_REFL, REAL_ABS_POS, SUM_POS_LE], ALL_TAC] THEN ABBREV_TAC (← q r"L = &(FACT n) * &n * (R + &1:real) pow (n - 1)") THEN SUBGOAL_THEN (← q r"&0 <= L:real") ASSUME_TAC THENL [EXPAND_TAC "L" THEN REPEAT (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN REWRITE_TAC [REAL_POS] THEN MATCH_MP_TAC REAL_POW_LE THEN UNDISCH_TAC (← q r"&0 <= R:real") THEN REAL_ARITH_TAC, ALL_TAC] THEN MP_TAC (← SPEC (← q r"min (abs a) (&1 - abs(a:real))") REAL_ARCH) THEN ASM_SIMP_TAC [REAL_LT_MIN, (← GSYM REAL_ABS_NZ), REAL_SUB_LT] THEN DISCH_THEN ((X_CHOOSE_TAC (← q r"Q:num")) o (SPEC (← q r"&n * &D + L:real"))) THEN SUBGOAL_THEN (← q r"L < &Q * abs a /\ &n * &D + L < &Q * (&1 - abs(a:real))") STRIP_ASSUME_TAC THENL [SUBGOAL_THEN (← q r"&0 <= &n * &D:real /\ &Q * min (abs a) (&1 - abs a) <= &Q * abs a /\
        &Q * min (abs a) (&1 - abs a) <= &Q * (&1 - abs(a:real))") MP_TAC THENL [SIMP_TAC [REAL_LE_MUL, REAL_POS] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [REAL_POS, REAL_MIN_MIN], UNDISCH_TAC (← q r"&n * &D + L < &Q * min (abs a) (&1 - abs(a:real))") THEN REAL_ARITH_TAC], ALL_TAC] THEN SUBGOAL_THEN (← q r"D < Q /\ &1 <= &Q:real") STRIP_ASSUME_TAC THENL [REWRITE_TAC [(← GSYM REAL_OF_NUM_LT), REAL_OF_NUM_LE, r4, (← GSYM REAL_OF_NUM_LT)] THEN SUBGOAL_THEN (← q r"&0 <= &Q * abs(a:real) /\ &D <= &n * &D:real") MP_TAC THENL [SIMP_TAC [REAL_LE_MUL, REAL_POS, REAL_ABS_POS] THEN GEN_REWRITE_TAC LAND_CONV [(← GSYM REAL_MUL_LID)] THEN MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC [REAL_OF_NUM_LE, REAL_POS] THEN UNDISCH_TAC (← q r"~(n = 0)") THEN ARITH_TAC, MAP_EVERY UNDISCH_TAC [(← q r"&0 <= L:real"), (← q r"&n * &D + L < &Q * (&1 - abs(a:real))")] THEN REAL_ARITH_TAC], ALL_TAC] THEN SUBGOAL_THEN (← q r"?M:K->K->int. !i j. real_of_int(M i j) <= &Q * A i j /\
                          &Q * A i j < real_of_int(M i j) + &1") (X_CHOOSE_TAC (← q r"M:K->K->int")) THENL [REWRITE_TAC [(← GSYM SKOLEM_THM)] THEN REPEAT GEN_TAC THEN EXISTS_TAC (← q r"int_of_real(floor(&Q * (A:K->K->real) i j))") THEN SIMP_TAC [REAL_OF_INT_OF_REAL, FLOOR], ALL_TAC] THEN MAP_EVERY EXISTS_TAC [(← q r"Q:num"), (← q r"M:K->K->int")] THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"P = (&Q:real) pow (n - 1)") THEN SUBGOAL_THEN (← q r"&0 < P /\ (&Q:real) pow n = &Q * P") STRIP_ASSUME_TAC THENL [EXPAND_TAC "P" THEN CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN UNDISCH_TAC (← q r"&1 <= &Q:real") THEN REAL_ARITH_TAC, ASM_SIMP_TAC [(← GSYM (← CONJUNCT2 real_pow)), r3]], ALL_TAC] THEN ABBREV_TAC (← q r"m = ring_det real_ring s (\i j. real_of_int((M:K->K->int) i j))") THEN SUBGOAL_THEN (← q r"abs(&Q * P * a - m:real) <= P * L") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"s:K->bool"), (← q r"\i j. &Q * (A:K->K->real) i j"), (← q r"\i j. real_of_int((M:K->K->int) i j)"), (← q r"&Q * (R + &1):real"), (← q r"&1:real")] REAL_DET_SUB_BOUND) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN MAP_EVERY X_GEN_TAC [(← q r"i:K"), (← q r"j:K")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"abs(&Q * (A:K->K->real) i j) <= &Q * R") MP_TAC THENL [ASM_SIMP_TAC [REAL_ABS_MUL, REAL_ABS_NUM, REAL_LE_LMUL, REAL_POS], ALL_TAC] THEN UNDISCH_TAC (← q r"&1 <= &Q:real") THEN FIRST_X_ASSUM (MP_TAC o (SPECL [(← q r"i:K"), (← q r"j:K")])) THEN REAL_ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"real_ring"), (← q r"s:K->bool"), (← q r"A:K->K->real"), (← q r"&Q:real")] RING_DET_CMUL) THEN ASM_REWRITE_TAC [REAL_FIELD_CLAUSES, IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [REAL_POW_MUL, REAL_MUL_RID] THEN EXPAND_TAC "L" THEN REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"abs(&Q * P - (&Q - &D) pow n) <= P * &n * &D:real") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"s:K->bool"), (← q r"\i:K. (&Q:real)"), (← q r"\i:K. &Q - &D:real"), (← q r"&Q:real")] PRODUCT_SUB_BOUND) THEN ASM_SIMP_TAC [PRODUCT_CONST, SUM_CONST, REAL_OF_NUM_LE, REAL_ABS_NUM, LE_REFL, REAL_LE_REFL, LT_IMP_LE, r2] THEN REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"abs(&Q * P * a:real) = &Q * P * abs a") ASSUME_TAC THENL [SIMP_TAC [REAL_ABS_MUL, REAL_ABS_NUM, (← ASSUME (← q r"&0 < P:real")), r1], ALL_TAC] THEN SUBGOAL_THEN (← q r"&0 < P * (&Q * abs a - L) /\
                  &0 < P * (&Q * (&1 - abs a) - (&n * &D + L:real))") STRIP_ASSUME_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC [REAL_SUB_LT], ALL_TAC] THEN SUBGOAL_THEN (← q r"real_of_int(ring_det integer_ring s (M:K->K->int)) = m") ASSUME_TAC THENL [EXPAND_TAC "m" THEN MATCH_MP_TAC RING_DET_HOMOMORPHISM THEN ASM_REWRITE_TAC [INTEGER_RING, IN_UNIV, (← REWRITE_RULE [REAL_RING_OF_INT] (← ISPEC (← q r"real_ring") RING_HOMOMORPHISM_INTEGER_RING_OF_INT))], ALL_TAC] THEN ASM_REWRITE_TAC [(← GSYM INT_OF_NUM_LT), int_eq, int_of_num_th] THEN SIMP_TAC [INT_OF_NUM_OF_INT, INT_ABS_POS] THEN ASM_REWRITE_TAC [int_lt, int_abs_th, int_of_num_th] THEN ASM_SIMP_TAC [(← GSYM REAL_OF_NUM_POW), (← GSYM REAL_OF_NUM_SUB), LT_IMP_LE] THEN MAP_EVERY UNDISCH_TAC [(← q r"abs(&Q * P * a - m:real) <= P * L"), (← q r"abs(&Q * P - (&Q - &D) pow n) <= P * &n * &D:real"), (← q r"abs(&Q * P * a:real) = &Q * P * abs a"), (← q r"&0 < P * (&Q * abs a - L:real)"), (← q r"&0 < P * (&Q * (&1 - abs a) - (&n * &D + L:real))")] THEN REAL_ARITH_TAC)

  let MINKOWSKI_LINEAR_FORMS_STRICT ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let v1 ← GSYM real_div
    let v2 ← ONCE_REWRITE_RULE [REAL_MUL_SYM] v1
    let q3 ← q r"&0 < c ==> abs c = c:real"
    let r4 ← REAL_ARITH q3
    let p5 ← prove r"!c y. &0 < c ==> (abs(inv c * y) < &1 <=> abs y < c)" (SIMP_TAC [REAL_ABS_MUL, REAL_ABS_INV, r4, v2, REAL_LT_LDIV_EQ, REAL_MUL_LID])
    let scale := p5
    let q6 ← q r"(&Q * y < &Q * &1 ==> y < &1) /\ w <= &2 * b /\ &2 * b <= &D:real
      ==> &Q * y < (&Q - &D) + w ==> y < &1"
    let r7 ← REAL_ARITH q6
    let q8 ← q r"i:K"
    let q9 ← q r"i:K"
    let q10 ← q r"(&Q * w <= &Q * (&2 * b) ==> w <= &2 * b:real)
        ==> &Q * w <= b * (&Q + w) ==> (&2 * b) * w <= &Q * w
            ==> w <= &2 * b"
    let r11 ← REAL_ARITH q10
    let q12 ← q r"&Q * w <= b * (&Q + w:real)"
    let q13 ← q r"&D:real"
    let q14 ← q r"(&2 * b) * w <= &Q * w:real"
    let q15 ← q r"w <= &2 * b:real"
    let q16 ← q r"abs y < q - &D + w ==> abs y <= q + w:real"
    let r17 ← REAL_ARITH q16
    let q18 ← q r"j:K"
    let q19 ← q r"sum s (\j. &Q * ((C:K->K->real) r j *
                      sum s (\k. A j k * real_of_int((x:K->int) k))))"
    let q20 ← q r"sum s (\j. (C:K->K->real) r j *
                     (&Q * sum s (\k. A j k * real_of_int((x:K->int) k)))) =
          &Q * sum s (\j. C r j * sum s (\k. A j k * real_of_int(x k)))"
    let q21 ← q r"abs(sum s (\j. (C:K->K->real) r j *
                       (&Q * sum s (\k. A j k * real_of_int((x:K->int) k)))))"
    let v22 ← GSYM SUM_RMUL
    let q23 ← q r"r:K"
    let q24 ← q r"\j. real_of_int((x:K->int) j)"
    let q25 ← q r"r:K"
    let q26 ← q r"&Q * w = sum s (\r. &Q * abs(real_of_int((x:K->int) r))) /\
        b * (&Q + w) =
        sum s (\r. sum s (\j. abs((C:K->K->real) r j)) * (&Q + w))"
    let q27 ← q r"&Q * w <= b * (&Q + w:real)"
    let q28 ← q r"j:K"
    let q29 ← q r"i:K"
    let v30 ← GSYM REAL_MUL_LID
    let q31 ← q r"q * a * x - m * x:real = (q * a - m) * x"
    let r32 ← REAL_ARITH q31
    let q33 ← q r"j:K"
    let q34 ← q r"FINITE(s:K->bool)"
    let v35 ← ASSUME q34
    let v36 ← GSYM SUM_SUB
    let v37 ← GSYM SUM_LMUL
    let q38 ← q r"abs(v - u) <= w ==> abs u < q ==> abs v < q + w:real"
    let r39 ← REAL_ARITH q38
    let v40 ← GSYM REAL_OF_NUM_SUB
    let q41 ← q r"i:K"
    let q42 ← q r"i:K"
    let q43 ← q r"!i. i IN s
          ==> abs(&Q * sum s (\j. (A:K->K->real) i j * real_of_int(x j))) <
              (&Q - &D) + w"
    let q44 ← q r"&0 <= w:real"
    let q45 ← q r"w = sum s (\j. abs(real_of_int((x:K->int) j)))"
    let q46 ← q r"x:K->int"
    let q47 ← q r"Q:num - D"
    let q48 ← q r"M:K->K->int"
    let q49 ← q r"s:K->bool"
    let v50 ← ISPECL [q49, q48, q47] INT_MATRIX_PIGEONHOLE
    let q51 ← q r"D:num < Q"
    let q52 ← q r"&0 < &Q:real /\ &D <= &Q:real"
    let q53 ← q r"M:K->K->int"
    let q54 ← q r"Q:num"
    let q55 ← q r"D:num"
    let q56 ← q r"A:K->K->real"
    let q57 ← q r"s:K->bool"
    let v58 ← ISPECL [q57, q56, q55] REAL_DET_ROUNDING
    let q59 ← q r"&2 * b:real"
    let v60 ← SPEC q59 REAL_ARCH_SIMPLE
    let q61 ← q r"D:num"
    let q62 ← q r"b = sum s (\i. sum s (\j. abs((C:K->K->real) i j)))"
    let q63 ← q r"C:K->K->real"
    let q64 ← q r"A:K->K->real"
    let q65 ← q r"s:K->bool"
    let v66 ← ISPECL [q65, q64] REAL_MATRIX_LEFT_INVERSE
    let p67 ← prove r"!s (A:K->K->real).
        FINITE s /\ ~(ring_det real_ring s A = &0) /\
        abs(ring_det real_ring s A) < &1
        ==> ?x:K->int.
                (!j. ~(j IN s) ==> x j = &0) /\
                (?j. j IN s /\ ~(x j = &0)) /\
                !i. i IN s
                    ==> abs(sum s (\j. A i j * real_of_int(x j))) < &1" (REPEAT STRIP_TAC THEN MP_TAC v66 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN q63 (LABEL_TAC "inv")) THEN ABBREV_TAC q62 THEN X_CHOOSE_TAC q61 v60 THEN MP_TAC v58 THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [q54, q53] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "fl") STRIP_ASSUME_TAC)) THEN SUBGOAL_THEN q52 STRIP_ASSUME_TAC THENL [REWRITE_TAC [REAL_OF_NUM_LT, REAL_OF_NUM_LE] THEN UNDISCH_TAC q51 THEN ARITH_TAC, ALL_TAC] THEN MP_TAC v50 THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC q46 THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "small"))) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC q45 THEN SUBGOAL_THEN q44 ASSUME_TAC THENL [EXPAND_TAC "w" THEN MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC [REAL_ABS_POS], ALL_TAC] THEN SUBGOAL_THEN q43 (LABEL_TAC "Ax") THENL [X_GEN_TAC q42 THEN DISCH_TAC THEN REMOVE_THEN "small" (MP_TAC o (SPEC q41)) THEN ASM_REWRITE_TAC [int_lt, int_abs_th, int_isum, int_mul_th, int_of_num_th] THEN ASM_SIMP_TAC [v40, LT_IMP_LE] THEN MATCH_MP_TAC r39 THEN EXPAND_TAC "w" THEN SIMP_TAC [v37, v36, v35] THEN MATCH_MP_TAC SUM_ABS_LE THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC q33 THEN DISCH_TAC THEN REWRITE_TAC [r32, REAL_ABS_MUL] THEN GEN_REWRITE_TAC RAND_CONV [v30] THEN MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC [REAL_ABS_POS] THEN USE_THEN "fl" (MP_TAC o (SPECL [q29, q28])) THEN REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN q27 ASSUME_TAC THENL [SUBGOAL_THEN q26 (fun th => REWRITE_TAC [th]) THENL [MAP_EVERY EXPAND_TAC ["w", "b"] THEN REWRITE_TAC [SUM_LMUL, SUM_RMUL], ALL_TAC] THEN MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC q25 THEN DISCH_TAC THEN REMOVE_THEN "inv" (MP_TAC o (SPECL [q24, q23])) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [v22] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC q21 THEN CONJ_TAC THENL [SUBGOAL_THEN q20 SUBST1_TAC THENL [TRANS_TAC EQ_TRANS q19 THEN CONJ_TAC THENL [ALL_TAC, REWRITE_TAC [SUM_LMUL]] THEN MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC [] THEN REAL_ARITH_TAC, REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_NUM, REAL_LE_REFL]], MATCH_MP_TAC SUM_ABS_LE THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC q18 THEN DISCH_TAC THEN ONCE_REWRITE_TAC [REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [REAL_ABS_POS] THEN MATCH_MP_TAC r17 THEN USE_THEN "Ax" MATCH_MP_TAC THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN q15 ASSUME_TAC THENL [SUBGOAL_THEN q14 MP_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC q13 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN UNDISCH_TAC q12 THEN MATCH_MP_TAC r11 THEN ASM_SIMP_TAC [REAL_LE_LMUL_EQ], ALL_TAC] THEN X_GEN_TAC q9 THEN DISCH_TAC THEN REMOVE_THEN "Ax" (MP_TAC o (SPEC q8)) THEN ASM_REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_NUM] THEN MATCH_MP_TAC r7 THEN ASM_SIMP_TAC [REAL_LT_LMUL_EQ])
    let lemma := p67
    let v68 ← GSYM REAL_MUL_ASSOC
    let q69 ← q r"i:K"
    let q70 ← q r"i:K"
    let q71 ← q r"(c ==> d) ==> a /\ b /\ c ==> a /\ b /\ d"
    let r72 ← TAUT q71
    let q73 ← q r"x:K->int"
    let q74 ← q r"A:K->K->real"
    let q75 ← q r"\i. inv((c:K->real) i)"
    let q76 ← q r"s:K->bool"
    let q77 ← q r"real_ring"
    let v78 ← ISPECL [q77, q76, q75, q74] RING_DET_ROWS_MUL
    let q79 ← q r"\i j. inv((c:K->real) i) * (A:K->K->real) i j"
    let q80 ← q r"s:K->bool"
    let v81 ← ISPECL [q80, q79] lemma
    prove
      r"!s (A:K->K->real) c.
          FINITE s /\ ~(ring_det real_ring s A = &0) /\
          (!i. i IN s ==> &0 < c i) /\
          abs(ring_det real_ring s A) < product s c
          ==> ?x:K->int.
                  (!j. ~(j IN s) ==> x j = &0) /\
                  (?j. j IN s /\ ~(x j = &0)) /\
                  !i. i IN s
                      ==> abs(sum s (\j. A i j * real_of_int(x j))) < c i"
      (REPEAT STRIP_TAC THEN MP_TAC v81 THEN MP_TAC v78 THEN ASM_REWRITE_TAC [REAL_RING_CLAUSES, IN_UNIV, REAL_RING_PRODUCT] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [PRODUCT_INV, REAL_ENTIRE, REAL_INV_EQ_0, scale, PRODUCT_POS_LT, REAL_LT_IMP_NZ] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC q73 THEN MATCH_MP_TAC r72 THEN DISCH_TAC THEN X_GEN_TAC q70 THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC q69)) THEN ASM_SIMP_TAC [v68, SUM_LMUL, scale])

  let MINKOWSKI_LINEAR_FORMS ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"s:K->bool"
    let q2 ← q r"sum s (\k. sum s (\i. abs((C:K->K->real) k i) * abs(b i)))"
    let q3 ← q r"\k. sum s (\i. abs((C:K->K->real) k i) * abs(b i))"
    let v4 ← ISPECL [q3, q2, q1] SUM_POS_BOUND
    let q5 ← q r"sum s (\k. sum s (\i. abs((C:K->K->real) k i) * abs(b i)))"
    let q6 ← q r"x <= b ==> x <= abs b:real"
    let r7 ← REAL_ARITH q6
    let q8 ← q r"i:K"
    let q9 ← q r"sum s (\i. abs((C:K->K->real) k i) * abs(b i))"
    let q13 ← q r"k:K"
    let q14 ← q r"\j. real_of_int((x:K->int) j)"
    let v15 ← GSYM INT_ABS_BOUNDS
    let q16 ← q r"k:K"
    let q17 ← q r"x:K->int"
    let q18 ← q r"{x:K->int | (!j. j IN s ==> x j IN {k | --(&N) <= k /\ k <= &N}) /\
                  (!j. ~(j IN s) ==> x j = &0)}"
    let q19 ← q r"sum s (\k. sum s (\i. abs((C:K->K->real) k i) * abs(b i)))"
    let v20 ← SPEC q19 REAL_ARCH_SIMPLE
    let q21 ← q r"N:num"
    let q22 ← q r"C:K->K->real"
    let q23 ← q r"A:K->K->real"
    let q24 ← q r"s:K->bool"
    let v25 ← ISPECL [q24, q23] REAL_MATRIX_LEFT_INVERSE
    let p26 ← prove r"!s (A:K->K->real) b.
        FINITE s /\ ~(ring_det real_ring s A = &0)
        ==> FINITE {x:K->int | (!j. ~(j IN s) ==> x j = &0) /\
                               !i. i IN s
                                   ==> abs(sum s (\j. A i j *
                                                      real_of_int(x j)))
                                       <= b i}" (REPEAT STRIP_TAC THEN MP_TAC v25 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC q22) THEN X_CHOOSE_TAC q21 v20 THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC q18 THEN ASM_SIMP_TAC [FINITE_FUNSPACE, FINITE_INT_SEG] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC q17 THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC q16 THEN DISCH_TAC THEN REWRITE_TAC [v15, int_le, int_abs_th, int_of_num_th] THEN FIRST_X_ASSUM (MP_TAC o ((SPECL [q14, q13]) o (checkM (fun z10 => (do let z11 ← (do let z12 ← (pure z10); pure (concl z12)); pure (is_forall z11)))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC q9 THEN CONJ_TAC THENL [MATCH_MP_TAC SUM_ABS_LE THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC q8 THEN DISCH_TAC THEN REWRITE_TAC [REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [REAL_ABS_POS] THEN MATCH_MP_TAC r7 THEN ASM_SIMP_TAC [], MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC q5 THEN ASM_REWRITE_TAC [] THEN MP_TAC v4 THEN ASM_SIMP_TAC [REAL_LE_REFL, SUM_POS_LE, REAL_LE_MUL, REAL_ABS_POS]])
    let finite := p26
    let q27 ← q r"m <= N ==> m <= N + 1"
    let r28 ← ARITH_RULE q27
    let q29 ← q r"c * (&1 + t) <= c * (&1 + inv(&((m:(K->int)->num) x))) /\
    c * (&1 + inv(&(m x))) < y
    ==> y < c * (&1 + t) ==> F"
    let r30 ← REAL_ARITH q29
    let q31 ← q r"(i:K) IN s"
    let v32 ← ASSUME q31
    let q33 ← q r"i:K"
    let q34 ← q r"x:K->int"
    let q35 ← q r"(x:K->int) IN S"
    let v36 ← ASSUME q35
    let q37 ← q r"&0 < c /\ c * t <= c * &1 ==> y < c * (&1 + t) ==> y <= &2 * c:real"
    let r38 ← REAL_ARITH q37
    let q39 ← q r"(i:K) IN s"
    let v40 ← ASSUME q39
    let q41 ← q r"i:K"
    let q42 ← q r"(x:K->int) IN S"
    let q43 ← q r"x:K->int"
    let v44 ← GSYM REAL_MUL_RID
    let q45 ← q r"product s (c:K->real)"
    let q46 ← q r"&1 < &1 + inv(&N + &1)"
    let q47 ← q r"\i. (c:K->real) i * (&1 + inv(&N + &1))"
    let q48 ← q r"A:K->K->real"
    let q49 ← q r"s:K->bool"
    let v50 ← ISPECL [q49, q48, q47] MINKOWSKI_LINEAR_FORMS_STRICT
    let q51 ← q r"N:num"
    let q52 ← q r"IMAGE (m:(K->int)->num) S"
    let v53 ← ISPEC q52 num_FINITE
    let q54 ← q r"m:(K->int)->num"
    let q55 ← q r"i:K"
    let q56 ← q r"n:num"
    let q57 ← q r"(abs(sum s (\j. (A:K->K->real) i j * real_of_int((x:K->int) j))) -
       c i) / c i"
    let v58 ← SPEC q57 REAL_ARCH_INV
    let q59 ← q r"i:K"
    let q60 ← q r"x:K->int"
    let q61 ← q r"x:K->int"
    let q62 ← q r"!x. x IN S /\ (?j. j IN s /\ ~(x j = &0))
        ==> ?n. ~(n = 0) /\
                ?i. i IN s /\
                    (c:K->real) i * (&1 + inv(&n)) <
                    abs(sum s (\j. (A:K->K->real) i j * real_of_int(x j)))"
    let q63 ← q r"(~p ==> F) ==> p"
    let r64 ← TAUT q63
    let q65 ← q r"S = {x:K->int | (!j. ~(j IN s) ==> x j = &0) /\
                    !i. i IN s
                        ==> abs(sum s (\j. (A:K->K->real) i j *
                                           real_of_int(x j))) <= &2 * c i}"
    let q66 ← q r"\i. &2 * (c:K->real) i"
    let q67 ← q r"A:K->K->real"
    let q68 ← q r"s:K->bool"
    let v69 ← ISPECL [q68, q67, q66] finite
    prove
      r"!s (A:K->K->real) c.
          FINITE s /\ ~(s = {}) /\ ~(ring_det real_ring s A = &0) /\
          (!i. i IN s ==> &0 < c i) /\
          abs(ring_det real_ring s A) <= product s c
          ==> ?x:K->int.
                  (!j. ~(j IN s) ==> x j = &0) /\
                  (?j. j IN s /\ ~(x j = &0)) /\
                  !i. i IN s
                      ==> abs(sum s (\j. A i j * real_of_int(x j))) <= c i"
      (REPEAT STRIP_TAC THEN MP_TAC v69 THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC q65 THEN DISCH_TAC THEN MATCH_MP_TAC r64 THEN DISCH_THEN (ASSUME_TAC o (REWRITE_RULE [NOT_EXISTS_THM])) THEN SUBGOAL_THEN q62 MP_TAC THENL [X_GEN_TAC q61 THEN EXPAND_TAC "S" THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) THEN FIRST_X_ASSUM (MP_TAC o (SPEC q60)) THEN ASM_REWRITE_TAC [NOT_FORALL_THM, NOT_IMP, REAL_NOT_LE] THEN DISCH_THEN (X_CHOOSE_THEN q59 STRIP_ASSUME_TAC) THEN MP_TAC v58 THEN ASM_SIMP_TAC [REAL_LT_DIV, REAL_SUB_LT, REAL_LT_RDIV_EQ] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC q56 THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC q55 THEN ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN DISCH_THEN (X_CHOOSE_THEN q54 (LABEL_TAC "m")) THEN MP_TAC v53 THEN ASM_SIMP_TAC [FINITE_IMAGE, FORALL_IN_IMAGE] THEN DISCH_THEN (X_CHOOSE_THEN q51 (LABEL_TAC "N")) THEN MP_TAC v50 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN SUBGOAL_THEN q46 ASSUME_TAC THENL [REWRITE_TAC [REAL_LT_ADDR, REAL_LT_INV_EQ] THEN REAL_ARITH_TAC, ALL_TAC] THEN CONJ_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC [] THEN ASM_REAL_ARITH_TAC, ASM_SIMP_TAC [PRODUCT_MUL, PRODUCT_CONST] THEN MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC q45 THEN ASM_REWRITE_TAC [] THEN GEN_REWRITE_TAC LAND_CONV [v44] THEN MATCH_MP_TAC REAL_LT_LMUL THEN ASM_SIMP_TAC [PRODUCT_POS_LT, REAL_POW_LT_1, CARD_EQ_0]], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN q43 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ((LABEL_TAC "lt") o BETA_RULE)))) THEN SUBGOAL_THEN q42 ASSUME_TAC THENL [EXPAND_TAC "S" THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC q41 THEN DISCH_TAC THEN USE_THEN "lt" (MP_TAC o (← do let c := v40; pure (fun th => MATCH_MP th c))) THEN MATCH_MP_TAC r38 THEN ASM_SIMP_TAC [] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN REAL_ARITH_TAC, ALL_TAC] THEN REMOVE_THEN "N" (MP_TAC o (← do let c := v36; pure (fun th => MATCH_MP th c))) THEN REMOVE_THEN "m" (MP_TAC o (SPEC q34)) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN q33 STRIP_ASSUME_TAC)) THEN DISCH_TAC THEN USE_THEN "lt" (MP_TAC o (← do let c := v32; pure (fun th => MATCH_MP th c))) THEN MATCH_MP_TAC r30 THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC [REAL_LT_IMP_LE, REAL_LE_LADD] THEN MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC [REAL_OF_NUM_LT, LE_1, REAL_OF_NUM_ADD, REAL_OF_NUM_LE, r28])

  let QUADRATIC_FORM_COMPLETE_SQUARE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"(a - b * c / d) * x * y:real = a * x * y - (b * x / d) * (c * y)")
    prove
      r"!a t (A:K->K->real) (x:K->real).
          FINITE t /\ ~(a IN t) /\ ~(A a a = &0) /\
          (!i. i IN t ==> A i a = A a i)
          ==> sum (a INSERT t) (\i. sum (a INSERT t) (\j. A i j * x i * x j)) =
              A a a * (x a + sum t (\j. A a j * x j) / A a a) pow 2 +
              sum t (\i. sum t (\j. (A i j - A i a * A a j / A a a) *
                                     x i * x j))"
      (REPEAT STRIP_TAC THEN SIMP_TAC [SUM_CLAUSES, (← ASSUME (← q r"FINITE(t:K->bool)"))] THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"u = sum t (\j. (A:K->K->real) a j * x j)") THEN SUBGOAL_THEN (← q r"sum t (\j. (A:K->K->real) a j * x a * x j) = x a * u") SUBST1_TAC THENL [EXPAND_TAC "u" THEN REWRITE_TAC [(← GSYM SUM_LMUL)] THEN MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC [] THEN REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"sum t (\i. (A:K->K->real) i a * x i * x a +
                 sum t (\j. A i j * x i * x j)) =
      x a * u + sum t (\i. sum t (\j. A i j * x i * x j))") SUBST1_TAC THENL [ASM_SIMP_TAC [SUM_ADD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "u" THEN REWRITE_TAC [(← GSYM SUM_LMUL)] THEN MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC [] THEN REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"sum t (\i. sum t (\j. ((A:K->K->real) i j - A i a * A a j / A a a) *
                            x i * x j)) =
      sum t (\i. sum t (\j. A i j * x i * x j)) - u pow 2 / A a a") SUBST1_TAC THENL [REWRITE_TAC [r1] THEN ASM_SIMP_TAC [SUM_SUB, SUM_LMUL] THEN AP_TERM_TAC THEN REWRITE_TAC [SUM_RMUL] THEN SUBGOAL_THEN (← q r"sum t (\i. (A:K->K->real) i a * x i / A a a) = u / A a a") SUBST1_TAC THENL [REWRITE_TAC [real_div, REAL_MUL_ASSOC, SUM_RMUL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "u" THEN MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC [], REWRITE_TAC [real_div] THEN CONV_TAC REAL_RING], ALL_TAC] THEN UNDISCH_TAC (← q r"~((A:K->K->real) a a = &0)") THEN CONV_TAC REAL_FIELD)

  -- @@RETURN BEGIN
  return { PRODUCT_SUB_BOUND, REAL_DET_SUB_BOUND, REAL_MATRIX_LEFT_INVERSE,
           INT_MATRIX_PIGEONHOLE, REAL_DET_ROUNDING, MINKOWSKI_LINEAR_FORMS_STRICT,
           MINKOWSKI_LINEAR_FORMS, QUADRATIC_FORM_COMPLETE_SQUARE }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- linear_forms.ml phrases from line 732 to 1024                          -/
/- ---------------------------------------------------------------------- -/

structure LinearForms02 where
  -- @@FIELDS
  REAL_DET_SCHUR_COMPLEMENT : thm
  QUADRATIC_FORM_BASIS_VECTOR : thm
  QUADRATIC_FORM_SCHUR_POSITIVE : thm
  QUADRATIC_FORM_POS_LE : thm
  QUADRATIC_FORM_MINIMAL_PRIMITIVE : thm
  QUADRATIC_FORM_CHANGE_BASIS : thm
  REAL_DET_CONGRUENT_MATRIX : thm
  QUADRATIC_FORM_CONGRUENT_POSITIVE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupLinearForms02 [HolBase] (D : LinearFormsDeps) (BLinearForms01 : LinearForms01) :
    ExceptT String IO LinearForms02 := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_INT_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, INTEGER_RULE,
        MESON, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, REAL_FIELD, REAL_RING, SET_RULE,
        SET_TAC, TAUT, .. } := D
  let { EQ_TRANS, FINITE_INSERT, FINITE_SING, INTEGRAL_DOMAIN_REAL_RING, INT_ENTIRE,
        INT_MUL_RZERO, IN_INSERT, IN_SING, IN_UNIV, NOT_EXISTS_THM, REAL_ABS_NUM,
        REAL_ADD_RDISTRIB, REAL_ADD_RID, REAL_ENTIRE, REAL_EQ_IMP_LE,
        REAL_LE_SQUARE_ABS, .. } := D.core1
  let { REAL_LT_IMP_LE, REAL_LT_IMP_NZ, REAL_LT_RMUL, REAL_MUL_LID, REAL_MUL_LZERO,
        REAL_MUL_RZERO, REAL_NOT_LT, REAL_POW_EQ_0, REAL_RING_CLAUSES, REAL_RING_SUM,
        RING_DET_BLOCK_TRIANGULAR, RING_DET_DEPENDENT_COLUMNS, RING_DET_EQ, RING_DET_I,
        RING_DET_MUL, RING_DET_SING, RING_DET_TRANSP, SKOLEM_THM, SUM_ADD, SUM_DELTA,
        SUM_EQ, SUM_EQ_0, SUM_LMUL, SUM_RMUL, SUM_SWAP, int_abs_th, int_divides,
        int_eq, int_le, int_mul_th, int_of_num_th, real_div, .. } := D.core2
  let { QUADRATIC_FORM_COMPLETE_SQUARE, .. } := BLinearForms01
  -- @@SCOPE END

  let REAL_DET_SCHUR_COMPLEMENT ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let p1 ← prove r"!p (c:real) x. (if p then c else &0) * x = if p then c * x else &0" (REPEAT GEN_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC)
    let lemma := p1
    let q2 ← q r"x = y ==> a * x = y * a:real"
    let r3 ← REAL_RING q2
    let q4 ← q r"~((A:K->K->real) a a = &0)"
    let q5 ← q r"j:K"
    let q6 ← q r"i:K"
    let q7 ← q r"(a:K) INSERT t = t UNION {a}"
    let r8 ← SET_RULE q7
    let q9 ← q r"t:K->bool"
    let q10 ← q r"real_ring"
    let v11 ← ISPECL [q10, q9] RING_DET_I
    let q12 ← q r"(j:K = i) <=> (i = j)"
    let q13 ← q r"~(j:K = a)"
    let q14 ← q r"j:K"
    let q15 ← q r"i:K"
    let q16 ← q r"ring_det real_ring t (\i j:K. if i = j then &1 else &0)"
    let q17 ← q r"~(j:K = a)"
    let q18 ← q r"j:K"
    let q19 ← q r"i:K"
    let q20 ← q r"(a:K) INSERT t = {a} UNION t"
    let r21 ← SET_RULE q20
    let q22 ← q r"ring_det real_ring ((a:K) INSERT t)
     (\i k. (if k = i then &1 else &0) +
            (if k = a then (if i IN t then (A:K->K->real) i a / A a a else &0)
             else &0)) = &1"
    let q23 ← q r"j:K"
    let q24 ← q r"i:K"
    let q25 ← q r"x = x' /\ y = y' ==> x' = y' ==> (x:real) = y"
    let r26 ← MESON [] q25
    let q27 ← q r"\i j. if i IN t then (A:K->K->real) i j - A i a * A a j / A a a
           else A i j"
    let q28 ← q r"\i k. (if k = i then &1 else &0) +
           (if k = a then (if i IN t then (A:K->K->real) i a / A a a else &0)
            else &0)"
    let q29 ← q r"(a:K) INSERT t"
    let q30 ← q r"real_ring"
    let v31 ← ISPECL [q30, q29, q28, q27] RING_DET_MUL
    prove
      r"!a t (A:K->K->real).
          FINITE t /\ ~(a IN t) /\ ~(A a a = &0)
          ==> ring_det real_ring (a INSERT t) A =
              A a a *
              ring_det real_ring t (\i j. A i j - A i a * A a j / A a a)"
      (REPEAT STRIP_TAC THEN MP_TAC v31 THEN REWRITE_TAC [REAL_RING_CLAUSES, IN_UNIV, REAL_RING_SUM, FINITE_INSERT] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r26 THEN CONJ_TAC THENL [MATCH_MP_TAC RING_DET_EQ THEN MAP_EVERY X_GEN_TAC [q24, q23] THEN STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC [REAL_ADD_RDISTRIB, lemma, REAL_MUL_LID] THEN ASM_SIMP_TAC [SUM_ADD, FINITE_INSERT, SUM_DELTA, IN_INSERT, REAL_MUL_LID] THEN COND_CASES_TAC THEN REWRITE_TAC [REAL_ADD_RID] THEN REWRITE_TAC [real_div] THEN CONV_TAC REAL_RING, ALL_TAC] THEN SUBGOAL_THEN q22 SUBST1_TAC THENL [SUBST1_TAC r21 THEN wPart lhand (lhand o rand) RING_DET_BLOCK_TRIANGULAR THEN ASM_REWRITE_TAC [FINITE_SING, REAL_RING_CLAUSES, IN_UNIV, IN_SING] THEN ANTS_TAC THENL [CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [q19, q18] THEN STRIP_TAC THEN SUBGOAL_THEN q17 ASSUME_TAC THENL [ASM SET_TAC [], ASM_REWRITE_TAC [REAL_ADD_RID]], DISCH_THEN SUBST1_TAC] THEN SIMP_TAC [RING_DET_SING, REAL_RING_CLAUSES, IN_UNIV] THEN ASM_REWRITE_TAC [REAL_ADD_RID, REAL_MUL_LID] THEN TRANS_TAC EQ_TRANS q16 THEN CONJ_TAC THENL [MATCH_MP_TAC RING_DET_EQ THEN MAP_EVERY X_GEN_TAC [q15, q14] THEN STRIP_TAC THEN SUBGOAL_THEN q13 ASSUME_TAC THENL [ASM SET_TAC [], ASM_REWRITE_TAC [REAL_ADD_RID]] THEN SUBGOAL_THEN q12 SUBST1_TAC THENL [MESON_TAC [], REWRITE_TAC []], MP_TAC v11 THEN ASM_REWRITE_TAC [REAL_RING_CLAUSES]], ALL_TAC] THEN REWRITE_TAC [REAL_MUL_LID] THEN SUBST1_TAC r8 THEN wPart rand (lhand o rand) RING_DET_BLOCK_TRIANGULAR THEN ASM_REWRITE_TAC [FINITE_SING, REAL_RING_CLAUSES, IN_UNIV, IN_SING] THEN ANTS_TAC THENL [CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [q6, q5] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC q4 THEN CONV_TAC REAL_FIELD, DISCH_THEN SUBST1_TAC] THEN SIMP_TAC [RING_DET_SING, REAL_RING_CLAUSES, IN_UNIV] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r3 THEN MATCH_MP_TAC RING_DET_EQ THEN SIMP_TAC [])

  let QUADRATIC_FORM_BASIS_VECTOR ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"(a:real) * (if p then &1 else &0) * (if q then &1 else &0) =
                          if q then if p then a else &0 else &0")
    prove
      r"!s (A:K->K->real) a.
          FINITE s /\ a IN s
          ==> sum s (\i. sum s (\j. A i j * (if i = a then &1 else &0) *
                                            (if j = a then &1 else &0))) =
              A a a"
      (REPEAT STRIP_TAC THEN REWRITE_TAC [r1] THEN ASM_SIMP_TAC [SUM_DELTA])

  let QUADRATIC_FORM_SCHUR_POSITIVE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"(x:real) = &0 ==> &0 < x + y ==> &0 < y")
    let r2 ← TAUT (← q r"p /\ (p ==> q /\ r) ==> p /\ q /\ r")
    prove
      r"!a t (A:K->K->real).
          FINITE t /\ ~(a IN t) /\
          (!i j. i IN a INSERT t /\ j IN a INSERT t ==> A i j = A j i) /\
          (!x. (?i. i IN a INSERT t /\ ~(x i = &0))
               ==> &0 < sum (a INSERT t) (\i. sum (a INSERT t)
                                                (\j. A i j * x i * x j)))
          ==> &0 < A a a /\
              (!i j. i IN t /\ j IN t
                     ==> A i j - A i a * A a j / A a a =
                         A j i - A j a * A a i / A a a) /\
              (!y. (?i. i IN t /\ ~(y i = &0))
                   ==> &0 < sum t (\i. sum t
                                   (\j. (A i j - A i a * A a j / A a a) *
                                                  y i * y j)))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC r2 THEN CONJ_TAC THENL [FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"\i:K. if i = a then &1:real else &0"))) THEN REWRITE_TAC [] THEN ANTS_TAC THENL [EXISTS_TAC (← q r"a:K") THEN REWRITE_TAC [IN_INSERT] THEN REAL_ARITH_TAC, ASM_SIMP_TAC [QUADRATIC_FORM_BASIS_VECTOR, FINITE_INSERT, IN_INSERT]], DISCH_TAC] THEN CONJ_TAC THENL [REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"(A:K->K->real) i j = A j i /\ A i a = A a i /\ A a j = A j a") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [IN_INSERT], ASM_REWRITE_TAC []] THEN REWRITE_TAC [real_div] THEN CONV_TAC REAL_RING, ALL_TAC] THEN X_GEN_TAC (← q r"y:K->real") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"\i:K. if i = a then --(sum t (\j. (A:K->K->real) a j * y j)) / A a a
            else y i"))) THEN REWRITE_TAC [] THEN ANTS_TAC THENL [EXISTS_TAC (← q r"i:K") THEN ASM_REWRITE_TAC [IN_INSERT] THEN COND_CASES_TAC THEN ASM_MESON_TAC [], ALL_TAC] THEN MP_TAC (← BETA_RULE (← ISPECL [(← q r"a:K"), (← q r"t:K->bool"), (← q r"A:K->K->real"), (← q r"\i:K. if i = a then --(sum t (\j. (A:K->K->real) a j * y j)) / A a a
             else y i")] QUADRATIC_FORM_COMPLETE_SQUARE)) THEN ANTS_TAC THENL [ASM_SIMP_TAC [REAL_LT_IMP_NZ] THEN ASM_MESON_TAC [IN_INSERT], DISCH_THEN SUBST1_TAC] THEN SUBGOAL_THEN (← q r"!j. j IN t
          ==> (if j = a then --(sum t (\j. (A:K->K->real) a j * y j)) / A a a
               else y j) = y j") ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"sum t (\j. (A:K->K->real) a j *
                 (if j = a then --(sum t (\j. A a j * y j)) / A a a else y j)) =
      sum t (\j. A a j * y j)") SUBST1_TAC THENL [MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"sum t (\i. sum t (\j. ((A:K->K->real) i j - A i a * A a j / A a a) *
       (if i = a then --(sum t (\j. A a j * y j)) / A a a else y i) *
       (if j = a then --(sum t (\j. A a j * y j)) / A a a else y j))) =
      sum t (\i. sum t (\j. (A i j - A i a * A a j / A a a) * y i * y j))") SUBST1_TAC THENL [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC (← q r"k:K") THEN DISCH_TAC THEN REWRITE_TAC [] THEN MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC [], REWRITE_TAC [] THEN MATCH_MP_TAC r1 THEN REWRITE_TAC [REAL_ENTIRE, REAL_POW_EQ_0] THEN DISJ2_TAC THEN CONJ_TAC THENL [ALL_TAC, ARITH_TAC] THEN REWRITE_TAC [real_div] THEN CONV_TAC REAL_RING])

  let QUADRATIC_FORM_POS_LE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"~(p /\ ~q) <=> p ==> q")
    prove
      r"!s (A:K->K->real) x.
          (!x. (?i. i IN s /\ ~(x i = &0))
               ==> &0 < sum s (\i. sum s (\j. A i j * x i * x j)))
          ==> &0 <= sum s (\i. sum s (\j. A i j * x i * x j))"
      (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"?i:K. i IN s /\ ~((x:K->real) i = &0)") THENL [ASM_SIMP_TAC [REAL_LT_IMP_LE], RULE_ASSUM_TAC (REWRITE_RULE [NOT_EXISTS_THM, r1]) THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC (← q r"i:K") THEN DISCH_TAC THEN REWRITE_TAC [] THEN MATCH_MP_TAC SUM_EQ_0 THEN ASM_SIMP_TAC [REAL_MUL_LZERO, REAL_MUL_RZERO]])

  let QUADRATIC_FORM_MINIMAL_PRIMITIVE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r6 ← REAL_ARITH (← q r"a * (d * x) * d * y:real = (d pow 2) * (a * x * y)")
    let r7 ← INTEGER_RULE (← q r"(&0:int) divides x <=> x = &0")
    prove
      r"!s (A:K->K->real) (x:K->int).
          FINITE s /\
          (!x. (?i. i IN s /\ ~(x i = &0))
               ==> &0 < sum s (\i. sum s (\j. A i j * x i * x j))) /\
          (!i. ~(i IN s) ==> x i = &0) /\ (?i. i IN s /\ ~(x i = &0)) /\
          (!y:K->int.
             (!i. ~(i IN s) ==> y i = &0) /\ (?i. i IN s /\ ~(y i = &0))
             ==> sum s (\i. sum s (\j. A i j * real_of_int(x i) *
                                      real_of_int(x j))) <=
                 sum s (\i. sum s (\j. A i j * real_of_int(y i) *
                                      real_of_int(y j))))
          ==> !d. (!i. i IN s ==> d divides x i) ==> d divides &1"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC (← q r"d:int") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"~(d:int = &0)") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"!i:K. i IN s ==> &0 divides (x:K->int) i") THEN REWRITE_TAC [r7] THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"?w:K->int. !i. (x:K->int) i = d * w i") STRIP_ASSUME_TAC THENL [REWRITE_TAC [(← GSYM SKOLEM_THM)] THEN X_GEN_TAC (← q r"k:K") THEN ASM_CASES_TAC (← q r"(k:K) IN s") THENL [ASM_MESON_TAC [int_divides], EXISTS_TAC (← q r"&0:int")] THEN ASM_SIMP_TAC [INT_MUL_RZERO], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"w:K->int"))) THEN ANTS_TAC THENL [CONJ_TAC THENL [X_GEN_TAC (← q r"k:K") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(d:int) * (w:K->int) k = &0") MP_TAC THENL [ASM_MESON_TAC [], ASM_REWRITE_TAC [INT_ENTIRE]], EXISTS_TAC (← q r"i:K") THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"~((x:K->int) i = &0)") THEN ASM_REWRITE_TAC [INT_MUL_RZERO]], ALL_TAC] THEN ASM_REWRITE_TAC [int_mul_th] THEN REWRITE_TAC [r6] THEN REWRITE_TAC [SUM_LMUL] THEN SUBGOAL_THEN (← q r"&0 < sum s (\i. sum s (\j. (A:K->K->real) i j * real_of_int(w i) *
                                 real_of_int((w:K->int) j)))") ASSUME_TAC THENL [FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"\i. real_of_int((w:K->int) i)")) o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_forall z1)) then (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); let z3 ← (q r"A:K->K->real"); pure (free_in z3 z4)) else pure false))))) THEN REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC (← q r"i:K") THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [(← GSYM int_of_num_th), (← GSYM int_eq)] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"~((x:K->int) i = &0)") THEN ASM_REWRITE_TAC [INT_MUL_RZERO], ALL_TAC] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"abs(real_of_int d) <= &1") MP_TAC THENL [ONCE_REWRITE_TAC [(← GSYM REAL_ABS_NUM)] THEN REWRITE_TAC [REAL_LE_SQUARE_ABS] THEN REWRITE_TAC [(← GSYM REAL_NOT_LT)] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"(&1:real) pow 2"), (← q r"real_of_int d pow 2"), (← q r"sum s (\i. sum s (\j. (A:K->K->real) i j * real_of_int(w i) *
                               real_of_int((w:K->int) j)))")] REAL_LT_RMUL) THEN ASM_REAL_ARITH_TAC, REWRITE_TAC [(← GSYM int_abs_th), (← GSYM int_of_num_th), (← GSYM int_le)] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"d:int = &1 \/ d = -- &1") MP_TAC THENL [ASM_INT_ARITH_TAC, STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONV_TAC INTEGER_RULE]])

  let QUADRATIC_FORM_CHANGE_BASIS ← prove
    r"!s (A:K->K->real) (U:K->K->real) (y:K->real).
        FINITE s
        ==> sum s (\i. sum s
                   (\j. sum s (\k. sum s (\l. U k i * A k l * U l j)) *
                                  y i * y j)) =
            sum s (\k. sum s (\l. A k l * sum s (\i. U k i * y i) *
                                          sum s (\j. U l j * y j)))"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [(← GSYM SUM_LMUL), (← GSYM SUM_RMUL)] THEN SUBGOAL_THEN (← q r"!f:K->K->real. sum s (\i. sum s (f i)) = sum s (\j. sum s (\i. f i j))") ASSUME_TAC THENL [GEN_TAC THEN MATCH_MP_TAC SUM_SWAP THEN ASM_REWRITE_TAC [], ALL_TAC] THEN FIRST_ASSUM (fun th => GEN_REWRITE_TAC (LAND_CONV o (RAND_CONV o ABS_CONV)) [th]) THEN BETA_TAC THEN FIRST_ASSUM (fun th => GEN_REWRITE_TAC LAND_CONV [th]) THEN BETA_TAC THEN FIRST_ASSUM (fun th => GEN_REWRITE_TAC (LAND_CONV o (RAND_CONV o (ABS_CONV o (RAND_CONV o ABS_CONV)))) [th]) THEN BETA_TAC THEN FIRST_ASSUM (fun th => GEN_REWRITE_TAC (LAND_CONV o (RAND_CONV o ABS_CONV)) [th]) THEN BETA_TAC THEN REPEAT (MATCH_MP_TAC SUM_EQ THEN GEN_TAC THEN DISCH_TAC THEN BETA_TAC) THEN REAL_ARITH_TAC)

  let REAL_DET_CONGRUENT_MATRIX ← prove
    r"!s (A:K->K->real) (U:K->K->real).
        FINITE s
        ==> ring_det real_ring s
              (\i j. sum s (\k. sum s (\l. U k i * A k l * U l j))) =
            ring_det real_ring s U pow 2 * ring_det real_ring s A"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"real_ring"), (← q r"s:K->bool"), (← q r"\i k:K. (U:K->K->real) k i"), (← q r"\k j:K. sum s (\l. (A:K->K->real) k l * U l j)")] RING_DET_MUL) THEN MP_TAC (← ISPECL [(← q r"real_ring"), (← q r"s:K->bool"), (← q r"A:K->K->real"), (← q r"U:K->K->real")] RING_DET_MUL) THEN REWRITE_TAC [REAL_RING_CLAUSES, IN_UNIV, REAL_RING_SUM] THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [(← GSYM SUM_LMUL)] THEN MP_TAC (← ISPECL [(← q r"real_ring"), (← q r"s:K->bool"), (← q r"U:K->K->real")] RING_DET_TRANSP) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC REAL_RING)

  let QUADRATIC_FORM_CONGRUENT_POSITIVE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"~(p /\ ~q) <=> p ==> q")
    let r2 ← TAUT (← q r"(~p ==> F) ==> p")
    prove
      r"!s (A:K->K->real) (U:K->K->real).
          FINITE s /\ (!i j. i IN s /\ j IN s ==> A i j = A j i) /\
          (!x. (?i. i IN s /\ ~(x i = &0))
               ==> &0 < sum s (\i. sum s (\j. A i j * x i * x j))) /\
          ~(ring_det real_ring s U = &0)
          ==> (!i j. i IN s /\ j IN s
                     ==> sum s (\k. sum s (\l. U k i * A k l * U l j)) =
                         sum s (\k. sum s (\l. U k j * A k l * U l i))) /\
              (!y. (?i. i IN s /\ ~(y i = &0))
                   ==> &0 < sum s (\i. sum s (\j.
                              sum s (\k. sum s (\l. U k i * A k l * U l j)) *
                              y i * y j)))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL [MAP_EVERY X_GEN_TAC [(← q r"i:K"), (← q r"j:K")] THEN STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [(← MATCH_MP SUM_SWAP (← CONJ (← ASSUME (← q r"FINITE(s:K->bool)")) (← ASSUME (← q r"FINITE(s:K->bool)"))))] THEN BETA_TAC THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC (← q r"k:K") THEN DISCH_TAC THEN BETA_TAC THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC (← q r"l:K") THEN DISCH_TAC THEN BETA_TAC THEN SUBGOAL_THEN (← q r"(A:K->K->real) k l = A l k") SUBST1_TAC THENL [ASM_MESON_TAC [], REAL_ARITH_TAC], ALL_TAC] THEN X_GEN_TAC (← q r"y:K->real") THEN STRIP_TAC THEN ASM_SIMP_TAC [QUADRATIC_FORM_CHANGE_BASIS] THEN FIRST_X_ASSUM (MATCH_MP_TAC o (checkM (fun th => (do if ← (do if ← (do if ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); pure (is_forall z3)) then (do let z6 ← (do let z7 ← (pure th); pure (concl z7)); let z5 ← (q r"A:K->K->real"); pure (free_in z5 z6)) else pure false) then (do let z8 ← (do pure (Prod.snd (← (do let z9 ← (do let z10 ← (pure th); pure (concl z10)); liftExcept (dest_forall z9))))); pure (is_imp z8)) else pure false) then (do let z11 ← (do let z12 ← (do pure (Prod.snd (← (do let z13 ← (do let z14 ← (pure th); pure (concl z14)); liftExcept (dest_forall z13))))); liftExcept (lhand z12)); pure (is_exists z11)) else pure false)))) THEN REWRITE_TAC [] THEN MATCH_MP_TAC r2 THEN DISCH_THEN (ASSUME_TAC o (REWRITE_RULE [NOT_EXISTS_THM, r1])) THEN UNDISCH_TAC (← q r"~(ring_det real_ring s (U:K->K->real) = &0)") THEN REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"real_ring"), (← q r"s:K->bool"), (← q r"U:K->K->real"), (← q r"y:K->real")] RING_DET_DEPENDENT_COLUMNS) THEN REWRITE_TAC [INTEGRAL_DOMAIN_REAL_RING, REAL_RING_CLAUSES, IN_UNIV, REAL_RING_SUM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC [])

  -- @@RETURN BEGIN
  return { REAL_DET_SCHUR_COMPLEMENT, QUADRATIC_FORM_BASIS_VECTOR,
           QUADRATIC_FORM_SCHUR_POSITIVE, QUADRATIC_FORM_POS_LE,
           QUADRATIC_FORM_MINIMAL_PRIMITIVE, QUADRATIC_FORM_CHANGE_BASIS,
           REAL_DET_CONGRUENT_MATRIX, QUADRATIC_FORM_CONGRUENT_POSITIVE }
  -- @@RETURN END

end HolANT.LinearForms
