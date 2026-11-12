/- ========================================================================= -/
/- ANT: Integer lattices                                                   -/
/- ========================================================================= -/
/- File: HolANT/Zlattice.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/zlattice.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antzlatticediff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/permutations.ml, Library/isum.ml, Library/products.ml, ANT/algmisc.ml, Library/ring_det.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.Zlattice fills them).

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
import HolANT.Algmisc
import HolLibrary.RingDet

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.Algmisc

namespace HolANT.Zlattice

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (CARD_IMAGE_LE CARD_PERMUTATIONS CARD_SING COND_ID COND_RAND DE_MORGAN_THM
   EQ_IMP EQ_TRANS ETA_AX EXISTS_IN_IMAGE EXISTS_PAIR_THM EXTENSION FINITE_IMAGE
   FINITE_INDUCT_STRONG FINITE_INSERT FINITE_PERMUTATIONS FINITE_SING
   FORALL_IN_IMAGE FORALL_IN_INSERT FORALL_PAIR_THM FUN_EQ_THM HAS_SIZE
   HAS_SIZE_FUNSPACE HAS_SIZE_IMAGE_INJ HAS_SIZE_INT_SEG_LT HAS_SIZE_NUMSEG_LT
   HAS_SIZE_PRODUCT IMP_CONJ INTEGER_RING INTEGER_RING_POW INTEGER_RING_PRODUCT
   INTEGER_RING_SUM INTEGRAL_DOMAIN_INTEGER_RING INT_ABS_MUL INT_ABS_NEG
   INT_ABS_NUM INT_ABS_POS INT_ABS_ZERO INT_ADD_RDISTRIB INT_ADD_RID
   INT_DIVIDES_LE INT_DIVISION INT_ENTIRE INT_EQ_IMP_LE INT_IMAGE INT_LET_TRANS
   INT_LT_IMP_LE INT_MUL_AC INT_MUL_ASSOC INT_MUL_EQ_1 INT_MUL_LID INT_MUL_LNEG
   INT_MUL_LZERO INT_MUL_RID INT_MUL_RZERO INT_OF_NUM_EQ INT_OF_NUM_LT
   INT_OF_NUM_OF_INT INT_OF_NUM_SUC INT_POW_EQ_0 INT_REM_EQ_0 INT_SUB_0
   INT_SUB_LDISTRIB INT_SUB_LZERO INT_SUB_REFL INT_SUB_RNEG INT_SUB_RZERO
   IN_ELIM_PAIR_THM IN_ELIM_THM IN_IMAGE IN_INSERT IN_SING IN_UNIV
   IPRODUCT_ABS_BOUND IPRODUCT_DELTA ISUM_0 ISUM_ABS_BOUND ISUM_CLAUSES
   ISUM_DELTA ISUM_DELTA_GEN ISUM_EQ ISUM_LMUL ISUM_POS_LE ISUM_RMUL ISUM_SUB
   ISUM_SWAP I_THM LEFT_AND_EXISTS_THM LEFT_IMP_EXISTS_THM LE_TRANS MONO_EXISTS
   NOT_FORALL_THM NOT_IMP NOT_IN_EMPTY NUM_OF_INT_MUL NUM_OF_INT_OF_NUM PAIR_EQ
   PERMUTES_IN_IMAGE RIGHT_AND_EXISTS_THM RIGHT_FORALL_IMP_THM
   RIGHT_IMP_EXISTS_THM RING_DET_CMUL RING_DET_DEPENDENT_COLUMNS
   RING_DET_DIAGONAL RING_DET_EMPTY RING_DET_EQ RING_DET_I
   RING_DET_LAPLACE_INSERT RING_DET_MUL RING_DET_ROW_OPERATION
   RING_DET_SWAP_ROWS RING_SIGN_I SKOLEM_THM SUBSET SWAP_REFL int_divides
   num_WOP ring_det ring_sign swap : thm)
  deriving Inhabited

/-- What zlattice.ml uses from Session besides theorems. -/
structure ZlatticeDeps where
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
  WF_INDUCT_TAC : term → tactic
  core1 : CoreThms1

/-- RingTheory's `wPart` (copied verbatim).  `W(MP_TAC o PART_MATCH f th o g
    o snd)`: match `th`'s part `f` against the part `g` of the goal, and
    MP_TAC the instance. -/
def wPart [HolBase] (g : term → Except String term) (f : term → Except String term)
    (th : thm) : tactic := fun gl =>
  ExceptT.run do
    let t ← liftExcept (g gl.2)
    ExceptT.mk (MP_TAC (← PART_MATCH f th t) gl)



/- ---------------------------------------------------------------------- -/
/- zlattice.ml phrases from line 43 to 718                                -/
/- ---------------------------------------------------------------------- -/

structure Zlattice01 where
  -- @@FIELDS
  int_lattice : thm
  int_matrix_image : thm
  int_cosets : thm
  INT_LATTICE_0 : thm
  INT_LATTICE_SUB : thm
  INT_LATTICE_SUPPORT : thm
  INT_LATTICE_NEG : thm
  INT_LATTICE_ADD : thm
  INT_LATTICE_CMUL : thm
  INT_LATTICE_CLOSED : thm
  INT_LATTICE_ISUM : thm
  INT_MATRIX_IMAGE_IN : thm
  INT_LATTICE_INT_MATRIX_IMAGE : thm
  INT_MATRIX_IMAGE_COLUMN : thm
  INT_MATRIX_IMAGE_SUBSET : thm
  INT_MATRIX_IMAGE_FACTOR : thm
  INT_DET_MUL : thm
  INT_DET_INSERT_ROW : thm
  INT_MATRIX_MUL_ASSOC : thm
  INT_MATRIX_IMAGE_INJECTIVE : thm
  INT_LATTICE_FULL_RANK : thm
  INT_MATRIX_IMAGE_EQ_DET : thm
  INT_PRIMITIVE_UNIMODULAR_COLUMN : thm
  INT_DET_BOUND : thm
  INT_LATTICE_CONG_SYM : thm
  INT_LATTICE_CONG_TRANS : thm
  INT_LATTICE_COSET_EQ : thm
  INT_COSETS_COVER : thm
  INT_COSETS_TRANSVERSAL : thm
  INT_COSETS_FINITE : thm
  INT_LATTICE_COORDINATE_GENERATOR : thm
  INT_LATTICE_SPLIT : thm
  INT_MATRIX_IMAGE_INSERT : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupZlattice01 [HolBase] (D : ZlatticeDeps) :
    ExceptT String IO Zlattice01 := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, ASM_INT_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, INTEGER_RULE,
        INT_ARITH, INT_ARITH_TAC, INT_REDUCE_CONV, MESON, MESON_TAC, WF_INDUCT_TAC,
        new_definition, .. } := D
  let { CARD_IMAGE_LE, CARD_PERMUTATIONS, COND_ID, COND_RAND, EQ_IMP, EQ_TRANS, ETA_AX,
        EXTENSION, FINITE_IMAGE, FINITE_INDUCT_STRONG, FINITE_PERMUTATIONS,
        FORALL_IN_INSERT, FUN_EQ_THM, HAS_SIZE, HAS_SIZE_FUNSPACE, HAS_SIZE_IMAGE_INJ,
        HAS_SIZE_INT_SEG_LT, IMP_CONJ, INTEGER_RING, INTEGER_RING_POW,
        INTEGER_RING_PRODUCT, INTEGER_RING_SUM, INTEGRAL_DOMAIN_INTEGER_RING,
        INT_ABS_MUL, INT_ABS_NEG, INT_ABS_NUM, INT_ABS_POS, INT_ADD_RDISTRIB,
        INT_ADD_RID, INT_DIVIDES_LE, INT_DIVISION, INT_EQ_IMP_LE, INT_IMAGE,
        INT_LET_TRANS, INT_LT_IMP_LE, INT_MUL_AC, INT_MUL_ASSOC, INT_MUL_EQ_1,
        INT_MUL_LID, INT_MUL_LNEG, INT_MUL_LZERO, INT_MUL_RID, INT_MUL_RZERO,
        INT_OF_NUM_EQ, INT_OF_NUM_LT, INT_OF_NUM_OF_INT, INT_OF_NUM_SUC, INT_POW_EQ_0,
        INT_REM_EQ_0, INT_SUB_0, INT_SUB_LDISTRIB, INT_SUB_LZERO, INT_SUB_REFL,
        INT_SUB_RNEG, INT_SUB_RZERO, IN_ELIM_THM, IN_IMAGE, IN_INSERT, IN_UNIV,
        IPRODUCT_ABS_BOUND, IPRODUCT_DELTA, ISUM_0, ISUM_ABS_BOUND, ISUM_CLAUSES,
        ISUM_DELTA, ISUM_DELTA_GEN, ISUM_EQ, ISUM_LMUL, ISUM_POS_LE, ISUM_RMUL,
        ISUM_SUB, ISUM_SWAP, I_THM, LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM, LE_TRANS,
        MONO_EXISTS, NOT_FORALL_THM, NOT_IMP, PERMUTES_IN_IMAGE, RIGHT_AND_EXISTS_THM,
        RIGHT_FORALL_IMP_THM, RIGHT_IMP_EXISTS_THM, RING_DET_CMUL,
        RING_DET_DEPENDENT_COLUMNS, RING_DET_DIAGONAL, RING_DET_EQ, RING_DET_I,
        RING_DET_LAPLACE_INSERT, RING_DET_MUL, RING_DET_ROW_OPERATION,
        RING_DET_SWAP_ROWS, RING_SIGN_I, SKOLEM_THM, SUBSET, SWAP_REFL, num_WOP,
        ring_det, ring_sign, swap, .. } := D.core1
  -- @@SCOPE END

  let int_lattice ← new_definition
    r"int_lattice (s:K->bool) (L:(K->int)->bool) <=>
  L SUBSET {x | !i. ~(i IN s) ==> x i = &0} /\
  (\i. &0) IN L /\
  (!x y. x IN L /\ y IN L ==> (\i. x i - y i) IN L)"

  let int_matrix_image ← new_definition
    r"int_matrix_image (s:K->bool) (M:K->K->int) =
  IMAGE (\z i. if i IN s then isum s (\j. M i j * z j) else &0)
        (:K->int)"

  let int_cosets ← new_definition
    r"int_cosets (s:K->bool) (L:(K->int)->bool) =
  {{y | (!i. ~(i IN s) ==> y i = &0) /\ (\i. y i - x i) IN L} | x |
   !i. ~(i IN s) ==> x i = &0}"

  let INT_LATTICE_0 ← prove
    r"!s (L:(K->int)->bool). int_lattice s L ==> (\i. &0) IN L"
    (SIMP_TAC [int_lattice])

  let INT_LATTICE_SUB ← prove
    r"!s (L:(K->int)->bool) x y.
        int_lattice s L /\ x IN L /\ y IN L ==> (\i. x i - y i) IN L"
    (SIMP_TAC [int_lattice])

  let INT_LATTICE_SUPPORT ← prove
    r"!s (L:(K->int)->bool) x i.
        int_lattice s L /\ x IN L /\ ~(i IN s) ==> x i = &0"
    (REWRITE_TAC [int_lattice, SUBSET, IN_ELIM_THM] THEN MESON_TAC [])

  let INT_LATTICE_NEG ← prove
    r"!s (L:(K->int)->bool) x.
        int_lattice s L /\ x IN L ==> (\i. --(x i)) IN L"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP INT_LATTICE_0)) THEN MP_TAC (← ISPECL [(← q r"s:K->bool"), (← q r"L:(K->int)->bool"), (← q r"(\i. &0):K->int"), (← q r"x:K->int")] INT_LATTICE_SUB) THEN ASM_REWRITE_TAC [INT_SUB_LZERO])

  let INT_LATTICE_ADD ← prove
    r"!s (L:(K->int)->bool) x y.
        int_lattice s L /\ x IN L /\ y IN L ==> (\i. x i + y i) IN L"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"s:K->bool"), (← q r"L:(K->int)->bool"), (← q r"y:K->int")] INT_LATTICE_NEG) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"s:K->bool"), (← q r"L:(K->int)->bool"), (← q r"x:K->int"), (← q r"(\i. --((y:K->int) i))")] INT_LATTICE_SUB) THEN ASM_REWRITE_TAC [INT_SUB_RNEG])

  let INT_LATTICE_CMUL ← prove
    r"!s (L:(K->int)->bool) c x.
        int_lattice s L /\ x IN L ==> (\i. c * x i) IN L"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"!n. (\i. &n * (x:K->int) i) IN L") ASSUME_TAC THENL [INDUCT_TAC THENL [REWRITE_TAC [INT_MUL_LZERO] THEN ASM_MESON_TAC [INT_LATTICE_0], REWRITE_TAC [(← GSYM INT_OF_NUM_SUC), INT_ADD_RDISTRIB, INT_MUL_LID] THEN MP_TAC (← ISPECL [(← q r"s:K->bool"), (← q r"L:(K->int)->bool"), (← q r"(\i. &n * (x:K->int) i)"), (← q r"x:K->int")] INT_LATTICE_ADD) THEN ASM_REWRITE_TAC []], DISJ_CASES_THEN (X_CHOOSE_THEN (← q r"n:num") SUBST1_TAC) (← SPEC (← q r"c:int") INT_IMAGE) THEN ASM_REWRITE_TAC [INT_MUL_LNEG] THEN MP_TAC (← ISPECL [(← q r"s:K->bool"), (← q r"L:(K->int)->bool"), (← q r"(\i. &n * (x:K->int) i)")] INT_LATTICE_NEG) THEN ASM_REWRITE_TAC []])

  let INT_LATTICE_CLOSED ← prove
    r"!s (L:(K->int)->bool).
        int_lattice s L
        ==> (\i. &0) IN L /\
            (!x y. x IN L /\ y IN L ==> (\i. x i - y i) IN L) /\
            (!x y. x IN L /\ y IN L ==> (\i. x i + y i) IN L) /\
            (!x. x IN L ==> (\i. --(x i)) IN L) /\
            (!c x. x IN L ==> (\i. c * x i) IN L)"
    (MESON_TAC [INT_LATTICE_0, INT_LATTICE_SUB, INT_LATTICE_ADD, INT_LATTICE_NEG, INT_LATTICE_CMUL])

  let INT_LATTICE_ISUM ← prove
    r"!s (L:(K->int)->bool) t (c:A->int) v.
        int_lattice s L /\ FINITE t /\ (!k. k IN t ==> v k IN L)
        ==> (\i. isum t (\k. c k * v k i)) IN L"
    (GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP INT_LATTICE_CLOSED)) THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN ASM_SIMP_TAC [ISUM_CLAUSES, FORALL_IN_INSERT] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [ETA_AX])

  let INT_MATRIX_IMAGE_IN ← prove
    r"!s (M:K->K->int) x.
        x IN int_matrix_image s M <=>
        ?z. x = (\i. if i IN s then isum s (\j. M i j * z j) else &0)"
    (REWRITE_TAC [int_matrix_image, IN_IMAGE, IN_UNIV])

  let INT_LATTICE_INT_MATRIX_IMAGE ← prove
    r"!s (M:K->K->int). FINITE s ==> int_lattice s (int_matrix_image s M)"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [int_lattice, SUBSET, IN_ELIM_THM, INT_MATRIX_IMAGE_IN] THEN REPEAT CONJ_TAC THENL [REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN SIMP_TAC [], EXISTS_TAC (← q r"(\j. &0):K->int") THEN REWRITE_TAC [INT_MUL_RZERO, ISUM_0, COND_ID], REWRITE_TAC [LEFT_AND_EXISTS_THM, RIGHT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"x:K->int"), (← q r"y:K->int"), (← q r"z:K->int"), (← q r"w:K->int")] THEN DISCH_THEN (CONJUNCTS_THEN SUBST1_TAC) THEN EXISTS_TAC (← q r"\j. (z:K->int) j - w j") THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"i:K") THEN COND_CASES_TAC THEN ASM_SIMP_TAC [INT_SUB_LDISTRIB, ISUM_SUB, INT_SUB_REFL]])

  let INT_MATRIX_IMAGE_COLUMN ← prove
    r"!s (M:K->K->int) j.
        j IN s
        ==> (\i. if i IN s then M i j else &0) IN int_matrix_image s M"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [INT_MATRIX_IMAGE_IN] THEN EXISTS_TAC (← q r"\k:K. if k = j then (&1:int) else &0") THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"i:K") THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [COND_RAND, INT_MUL_RID, INT_MUL_RZERO, ISUM_DELTA_GEN])

  let INT_MATRIX_IMAGE_SUBSET ← prove
    r"!s (L:(K->int)->bool) M.
        FINITE s /\ int_lattice s L /\
        (!j. j IN s ==> (\i. if i IN s then M i j else &0) IN L)
        ==> int_matrix_image s M SUBSET L"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [SUBSET, INT_MATRIX_IMAGE_IN, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"x:K->int") THEN X_GEN_TAC (← q r"z:K->int") THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"s:K->bool"), (← q r"L:(K->int)->bool"), (← q r"s:K->bool"), (← q r"z:K->int"), (← q r"\j i. if i IN s then (M:K->K->int) i j else &0")] INT_LATTICE_ISUM) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"i:K") THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [INT_MUL_RZERO, ISUM_0] THEN MATCH_MP_TAC ISUM_EQ THEN REWRITE_TAC [INT_MUL_AC])

  let INT_MATRIX_IMAGE_FACTOR ← prove
    r"!s (A:K->K->int) N.
        (!j. j IN s
             ==> (\i. if i IN s then A i j else &0) IN int_matrix_image s N)
        ==> ?U. !i j. i IN s /\ j IN s ==> A i j = isum s (\k. N i k * U k j)"
    (REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o ((REWRITE_RULE [RIGHT_IMP_EXISTS_THM, SKOLEM_THM]) o (REWRITE_RULE [INT_MATRIX_IMAGE_IN]))) THEN DISCH_THEN (X_CHOOSE_TAC (← q r"u:K->K->int")) THEN EXISTS_TAC (← q r"\k j. (u:K->K->int) j k") THEN REWRITE_TAC [] THEN MAP_EVERY X_GEN_TAC [(← q r"i:K"), (← q r"j:K")] THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"j:K"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (← do let c := (← q r"i:K"); pure (fun th => AP_THM th c))) THEN ASM_REWRITE_TAC [])

  let INT_DET_MUL ← prove
    r"!s (A:K->K->int) B.
        FINITE s
        ==> ring_det integer_ring s (\i j. isum s (\k. A i k * B k j)) =
            ring_det integer_ring s A * ring_det integer_ring s B"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"s:K->bool"), (← q r"A:K->K->int"), (← q r"B:K->K->int")] RING_DET_MUL) THEN ASM_REWRITE_TAC [INTEGER_RING, IN_UNIV, INTEGER_RING_SUM])

  let INT_DET_INSERT_ROW ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← INT_ARITH (← q r"(y:int) = &0 ==> x * &1 * z + y = x * z")
    prove
      r"!a t (N:K->K->int).
          FINITE t /\ ~(a IN t) /\ (!j. j IN t ==> N a j = &0)
          ==> ring_det integer_ring (a INSERT t) N =
              N a a * ring_det integer_ring t N"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"t:K->bool"), (← q r"N:K->K->int"), (← q r"a:K")] RING_DET_LAPLACE_INSERT) THEN ASM_REWRITE_TAC [INTEGER_RING, IN_UNIV, INTEGER_RING_SUM] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [ISUM_CLAUSES, SWAP_REFL, RING_SIGN_I, I_THM, INTEGER_RING, ETA_AX] THEN MATCH_MP_TAC r1 THEN TRANS_TAC EQ_TRANS (← q r"isum t (\b:K. &0)") THEN CONJ_TAC THENL [MATCH_MP_TAC ISUM_EQ THEN ASM_SIMP_TAC [INT_MUL_LZERO], REWRITE_TAC [ISUM_0]])

  let INT_MATRIX_MUL_ASSOC ← prove
    r"!s (A:K->K->int) (B:K->K->int) (C:K->K->int) i j.
        FINITE s
        ==> isum s (\k. A i k * isum s (\l. B k l * C l j)) =
            isum s (\l. isum s (\k. A i k * B k l) * C l j)"
    (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [(← GSYM ISUM_LMUL), (← GSYM ISUM_RMUL)] THEN REWRITE_TAC [INT_MUL_ASSOC] THEN MP_TAC (← ISPECL [(← q r"\k l. ((A:K->K->int) i k * B k l) * (C:K->K->int) l j"), (← q r"s:K->bool"), (← q r"s:K->bool")] ISUM_SWAP) THEN ASM_REWRITE_TAC [])

  let INT_MATRIX_IMAGE_INJECTIVE ← prove
    r"!s (M:K->K->int) z z'.
        FINITE s /\ ~(ring_det integer_ring s M = &0) /\
        (!i. i IN s ==> isum s (\j. M i j * z j) = isum s (\j. M i j * z' j))
        ==> !j. j IN s ==> z j = z' j"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC (← q r"k:K") THEN DISCH_TAC THEN ONCE_REWRITE_TAC [(← GSYM INT_SUB_0)] THEN ASM_CASES_TAC (← q r"(z:K->int) k - z' k = &0") THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"~(ring_det integer_ring s (M:K->K->int) = &0)") THEN REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"s:K->bool"), (← q r"M:K->K->int"), (← q r"\j. (z:K->int) j - z' j")] RING_DET_DEPENDENT_COLUMNS) THEN REWRITE_TAC [INTEGRAL_DOMAIN_INTEGER_RING, INTEGER_RING, IN_UNIV, INTEGER_RING_SUM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [EXISTS_TAC (← q r"k:K") THEN ASM_REWRITE_TAC [], ASM_SIMP_TAC [INT_SUB_LDISTRIB, ISUM_SUB, INT_SUB_REFL]])

  let INT_LATTICE_FULL_RANK ← prove
    r"!s (L:(K->int)->bool) M d.
        FINITE s /\ L = int_matrix_image s M /\ ~(d = &0) /\
        (!x. (!i. ~(i IN s) ==> x i = &0) ==> (\i. d * x i) IN L)
        ==> ~(ring_det integer_ring s M = &0)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"s:K->bool"), (← q r"\i j:K. (d:int) * (if i = j then &1 else &0)"), (← q r"M:K->K->int")] INT_MATRIX_IMAGE_FACTOR) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"j:K") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"\i:K. if i = j then (&1:int) else &0"))) THEN ANTS_TAC THENL [REPEAT STRIP_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"i:K") THEN ASM_CASES_TAC (← q r"i:K = j") THEN ASM_REWRITE_TAC [INT_MUL_RID, INT_MUL_RZERO, COND_ID], DISCH_THEN (X_CHOOSE_THEN (← q r"U:K->K->int") (ASSUME_TAC o BETA_RULE))] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_det integer_ring s (\i j:K. (d:int) * (if i = j then &1 else &0)) =
    ring_det integer_ring s M * ring_det integer_ring s U") MP_TAC THENL [SIMP_TAC [(← GSYM INT_DET_MUL), (← ASSUME (← q r"FINITE(s:K->bool)"))] THEN MATCH_MP_TAC RING_DET_EQ THEN REPEAT STRIP_TAC THEN BETA_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"s:K->bool"), (← q r"\i j:K. if i = j then (&1:int) else &0"), (← q r"d:int")] RING_DET_CMUL) THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"s:K->bool")] RING_DET_I) THEN ASM_SIMP_TAC [INTEGER_RING, IN_UNIV, INTEGER_RING_POW, INT_MUL_RID] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [INT_MUL_LZERO, INT_POW_EQ_0]])

  let INT_MATRIX_IMAGE_EQ_DET ← prove
    r"!s (M:K->K->int) N.
        FINITE s /\ int_matrix_image s M = int_matrix_image s N /\
        ~(ring_det integer_ring s M = &0)
        ==> abs(ring_det integer_ring s N) = abs(ring_det integer_ring s M)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"s:K->bool"), (← q r"M:K->K->int"), (← q r"N:K->K->int")] INT_MATRIX_IMAGE_FACTOR) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"j:K") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"s:K->bool"), (← q r"M:K->K->int"), (← q r"j:K")] INT_MATRIX_IMAGE_COLUMN) THEN ASM_REWRITE_TAC [], DISCH_THEN (X_CHOOSE_THEN (← q r"U:K->K->int") (LABEL_TAC "U"))] THEN MP_TAC (← ISPECL [(← q r"s:K->bool"), (← q r"N:K->K->int"), (← q r"M:K->K->int")] INT_MATRIX_IMAGE_FACTOR) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"j:K") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"s:K->bool"), (← q r"N:K->K->int"), (← q r"j:K")] INT_MATRIX_IMAGE_COLUMN) THEN ASM_REWRITE_TAC [], DISCH_THEN (X_CHOOSE_THEN (← q r"V:K->K->int") (LABEL_TAC "V"))] THEN SUBGOAL_THEN (← q r"ring_det integer_ring s (M:K->K->int) =
    ring_det integer_ring s N * ring_det integer_ring s U") SUBST1_TAC THENL [SIMP_TAC [(← GSYM INT_DET_MUL), (← ASSUME (← q r"FINITE(s:K->bool)"))] THEN MATCH_MP_TAC RING_DET_EQ THEN REPEAT STRIP_TAC THEN BETA_TAC THEN USE_THEN "U" MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!j. j IN s
        ==> !l. l IN s
                ==> isum s (\k. (V:K->K->int) l k * U k j) =
                    (\l:K. if l = j then &1 else &0) l") ASSUME_TAC THENL [X_GEN_TAC (← q r"j:K") THEN DISCH_TAC THEN MATCH_MP_TAC INT_MATRIX_IMAGE_INJECTIVE THEN EXISTS_TAC (← q r"M:K->K->int") THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"i:K") THEN DISCH_TAC THEN ASM_REWRITE_TAC [COND_RAND, INT_MUL_RID, INT_MUL_RZERO, ISUM_DELTA_GEN] THEN SIMP_TAC [INT_MATRIX_MUL_ASSOC, (← ASSUME (← q r"FINITE(s:K->bool)"))] THEN TRANS_TAC EQ_TRANS (← q r"isum s (\k. (N:K->K->int) i k * (U:K->K->int) k j)") THEN CONJ_TAC THENL [MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC (← q r"k:K") THEN DISCH_TAC THEN BETA_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN USE_THEN "V" MATCH_MP_TAC THEN ASM_REWRITE_TAC [], CONV_TAC SYM_CONV THEN USE_THEN "U" MATCH_MP_TAC THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_det integer_ring s (V:K->K->int) * ring_det integer_ring s U = &1") MP_TAC THENL [SIMP_TAC [(← GSYM INT_DET_MUL), (← ASSUME (← q r"FINITE(s:K->bool)"))] THEN TRANS_TAC EQ_TRANS (← q r"ring_det integer_ring s (\i j:K. if i = j then &1 else &0)") THEN CONJ_TAC THENL [ALL_TAC, MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"s:K->bool")] RING_DET_I) THEN ASM_REWRITE_TAC [INTEGER_RING]] THEN MATCH_MP_TAC RING_DET_EQ THEN ASM_SIMP_TAC [], REWRITE_TAC [INT_MUL_EQ_1] THEN STRIP_TAC THEN ASM_REWRITE_TAC [INT_ABS_MUL, INT_ABS_NEG, INT_ABS_NUM, INT_MUL_RID]])

  let INT_PRIMITIVE_UNIMODULAR_COLUMN ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r9 ← INTEGER_RULE (← q r"(&0:int) divides x <=> x = &0")
    let r28 ← INT_ARITH (← q r"&0 < abs x <=> ~(x:int = &0)")
    let r29 ← INT_ARITH (← q r"&0 < b ==> a - b < a:int")
    let r30 ← INT_ARITH (← q r"abs((v:K->int) p) <= abs(v q) \/
                                abs(v q) <= abs(v p)")
    prove
      r"!s (v:K->int) a.
          FINITE s /\ a IN s /\
          (!d. (!i. i IN s ==> d divides v i) ==> d divides &1)
          ==> ?U. (!i. i IN s ==> U i a = v i) /\
                  abs(ring_det integer_ring s U) = &1"
      (REPEAT GEN_TAC THEN WF_INDUCT_TAC (← q r"num_of_int(isum s (\i. abs((v:K->int) i)))") THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"?i j. i IN s /\ j IN s /\ ~(i = j) /\ ~((v:K->int) i = &0) /\
            ~(v j = &0)") THENL [SUBGOAL_THEN (← q r"?i j. i IN s /\ j IN s /\ ~(i = j) /\ ~((v:K->int) i = &0) /\
              ~(v j = &0) /\ abs(v i) <= abs(v j)") STRIP_ASSUME_TAC THENL [FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"p:K") (X_CHOOSE_THEN (← q r"q:K") STRIP_ASSUME_TAC)) THEN DISJ_CASES_TAC r30 THENL [MAP_EVERY EXISTS_TAC [(← q r"p:K"), (← q r"q:K")], MAP_EVERY EXISTS_TAC [(← q r"q:K"), (← q r"p:K")]] THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"?c:int. abs((v:K->int) j - c * v i) = abs(v j) - abs(v i)") STRIP_ASSUME_TAC THENL [ASM_CASES_TAC (← q r"&0 <= (v:K->int) i") THEN ASM_CASES_TAC (← q r"&0 <= (v:K->int) j") THENL [EXISTS_TAC (← q r"&1:int"), EXISTS_TAC (← q r"-- &1:int"), EXISTS_TAC (← q r"-- &1:int"), EXISTS_TAC (← q r"&1:int")] THEN ASM_INT_ARITH_TAC, ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (SPECL [(← q r"s:K->bool"), (← q r"\k. if k = j then (v:K->int) j - c * v i else v k")])) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [REWRITE_TAC [(← GSYM INT_OF_NUM_LT)] THEN wPart lhand (lhand o rand) INT_OF_NUM_OF_INT THEN ANTS_TAC THENL [MATCH_MP_TAC ISUM_POS_LE THEN REWRITE_TAC [INT_ABS_POS], DISCH_THEN SUBST1_TAC] THEN wPart rand (lhand o rand) INT_OF_NUM_OF_INT THEN ANTS_TAC THENL [MATCH_MP_TAC ISUM_POS_LE THEN REWRITE_TAC [INT_ABS_POS], DISCH_THEN SUBST1_TAC] THEN TRANS_TAC INT_LET_TRANS (← q r"isum s (\k. abs((v:K->int) k) - (if k = j then abs(v i) else &0))") THEN CONJ_TAC THENL [MATCH_MP_TAC INT_EQ_IMP_LE THEN MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC (← q r"k:K") THEN DISCH_TAC THEN REWRITE_TAC [] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [INT_SUB_RZERO], ASM_SIMP_TAC [ISUM_SUB, ISUM_DELTA] THEN MATCH_MP_TAC r29 THEN ASM_REWRITE_TAC [r28]], ALL_TAC] THEN ANTS_TAC THENL [X_GEN_TAC (← q r"d:int") THEN DISCH_TAC THEN FIRST_X_ASSUM (MATCH_MP_TAC o (checkM (fun th => (do if ← (do if ← (do let z22 ← (pure false); let z21 ← (do let z19 ← (do let z20 ← (pure th); pure (concl z20)); let z18 ← (q r"d:int"); pure (free_in z18 z19)); pure (z21 == z22)) then (do let z23 ← (do let z24 ← (pure th); pure (concl z24)); pure (is_forall z23)) else pure false) then (do let z26 ← (do let z27 ← (pure th); pure (concl z27)); let z25 ← (q r"(&1:int)"); pure (free_in z25 z26)) else pure false)))) THEN X_GEN_TAC (← q r"k:K") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"k:K = j") THENL [FIRST_X_ASSUM (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"i:K") th) THEN MP_TAC (← SPEC (← q r"j:K") th))) THEN ASM_REWRITE_TAC [] THEN CONV_TAC INTEGER_RULE, FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"k:K"))) THEN ASM_REWRITE_TAC []], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"U:K->K->int") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"\k l. if k = j then (U:K->K->int) j l + c * U i l
                        else U k l") THEN CONJ_TAC THENL [X_GEN_TAC (← q r"k:K") THEN DISCH_TAC THEN REWRITE_TAC [] THEN COND_CASES_TAC THEN ASM_SIMP_TAC [] THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN INT_ARITH_TAC, MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"s:K->bool"), (← q r"U:K->K->int"), (← q r"j:K"), (← q r"i:K"), (← q r"c:int")] RING_DET_ROW_OPERATION) THEN ASM_REWRITE_TAC [INTEGER_RING, IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"?i0:K. i0 IN s /\ ~((v:K->int) i0 = &0)") STRIP_ASSUME_TAC THENL [FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"&0:int")) o (checkM (fun th => (do if ← (do if ← (do let z10 ← (do let z11 ← (pure th); pure (concl z11)); pure (is_forall z10)) then (do let z13 ← (do let z14 ← (pure th); pure (concl z14)); let z12 ← (q r"(&1:int)"); pure (free_in z12 z13)) else pure false) then (do pure !(← (do let z16 ← (do let z17 ← (pure th); pure (concl z17)); let z15 ← (q r"U:K->K->int"); pure (free_in z15 z16)))) else pure false))))) THEN REWRITE_TAC [r9] THEN CONV_TAC INT_REDUCE_CONV THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!k. k IN s /\ ~(k = i0) ==> (v:K->int) k = &0") ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"abs((v:K->int) i0) = &1") ASSUME_TAC THENL [FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"(v:K->int) i0")) o (checkM (fun th => (do if ← (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_forall z1)) then (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); let z3 ← (q r"(&1:int)"); pure (free_in z3 z4)) else pure false) then (do pure !(← (do let z7 ← (do let z8 ← (pure th); pure (concl z8)); let z6 ← (q r"U:K->K->int"); pure (free_in z6 z7)))) else pure false))))) THEN ANTS_TAC THENL [X_GEN_TAC (← q r"k:K") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"k:K = i0") THEN ASM_SIMP_TAC [] THEN CONV_TAC INTEGER_RULE, DISCH_THEN (MP_TAC o (MATCH_MP INT_DIVIDES_LE)) THEN ASM_INT_ARITH_TAC], ALL_TAC] THEN EXISTS_TAC (← q r"\k l. if swap(a,i0) k = l then (if l = a then (v:K->int) i0 else &1)
            else &0") THEN CONJ_TAC THENL [X_GEN_TAC (← q r"k:K") THEN DISCH_TAC THEN REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"swap(a,i0) (k:K) = a <=> k = i0") SUBST1_TAC THENL [REWRITE_TAC [swap] THEN MESON_TAC [], REWRITE_TAC []] THEN ASM_CASES_TAC (← q r"k:K = i0") THEN ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"s:K->bool"), (← q r"\k l:K. if k = l then (if l = a then (v:K->int) i0 else &1) else &0")] RING_DET_DIAGONAL) THEN ANTS_TAC THENL [ASM_SIMP_TAC [INTEGER_RING], ALL_TAC] THEN REWRITE_TAC [INTEGER_RING_PRODUCT] THEN ASM_SIMP_TAC [IPRODUCT_DELTA] THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"a:K = i0") THENL [FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC [SWAP_REFL, I_THM], MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"s:K->bool"), (← q r"\k l:K. if k = l then (if l = a then (v:K->int) i0 else &1) else &0"), (← q r"a:K"), (← q r"i0:K")] RING_DET_SWAP_ROWS) THEN ASM_REWRITE_TAC [INTEGER_RING] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [INT_ABS_NEG]])

  let INT_DET_BOUND ← prove
    r"!s (M:K->K->int) B.
        FINITE s /\ (!i j. i IN s /\ j IN s ==> abs(M i j) <= B)
        ==> abs(ring_det integer_ring s M) <=
            &(FACT(CARD s)) * B pow (CARD s)"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [ring_det, INTEGER_RING, INTEGER_RING_SUM, INTEGER_RING_PRODUCT] THEN ASM_SIMP_TAC [(← GSYM CARD_PERMUTATIONS)] THEN MATCH_MP_TAC ISUM_ABS_BOUND THEN ASM_SIMP_TAC [FINITE_PERMUTATIONS, IN_ELIM_THM] THEN X_GEN_TAC (← q r"p:K->K") THEN DISCH_TAC THEN REWRITE_TAC [INT_ABS_MUL] THEN SUBGOAL_THEN (← q r"abs(ring_sign integer_ring (p:K->K)) = &1") SUBST1_TAC THENL [REWRITE_TAC [ring_sign, INTEGER_RING] THEN COND_CASES_TAC THEN REWRITE_TAC [INT_ABS_NEG, INT_ABS_NUM], REWRITE_TAC [INT_MUL_LID]] THEN MATCH_MP_TAC IPRODUCT_ABS_BOUND THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"i:K") THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC [PERMUTES_IN_IMAGE])

  let INT_LATTICE_CONG_SYM ← prove
    r"!s (L:(K->int)->bool) x y.
        int_lattice s L /\ (\i. x i - y i) IN L ==> (\i. y i - x i) IN L"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP INT_LATTICE_CLOSED)) THEN SUBGOAL_THEN (← q r"(\i. (y:K->int) i - x i) = (\i. --(x i - y i))") SUBST1_TAC THENL [REWRITE_TAC [FUN_EQ_THM] THEN INT_ARITH_TAC, ASM_SIMP_TAC [ETA_AX]])

  let INT_LATTICE_CONG_TRANS ← prove
    r"!s (L:(K->int)->bool) x y z.
        int_lattice s L /\ (\i. x i - y i) IN L /\ (\i. y i - z i) IN L
        ==> (\i. x i - z i) IN L"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP INT_LATTICE_CLOSED)) THEN SUBGOAL_THEN (← q r"(\i. (x:K->int) i - z i) = (\i. (x i - y i) + (y i - z i))") SUBST1_TAC THENL [REWRITE_TAC [FUN_EQ_THM] THEN INT_ARITH_TAC, ASM_SIMP_TAC [ETA_AX]])

  let INT_LATTICE_COSET_EQ ← prove
    r"!s (L:(K->int)->bool) x x'.
        int_lattice s L /\ (\i. x i - x' i) IN L
        ==> {y | (!i. ~(i IN s) ==> y i = &0) /\ (\i. y i - x i) IN L} =
            {y | (!i. ~(i IN s) ==> y i = &0) /\ (\i. y i - x' i) IN L}"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC (← q r"y:K->int") THEN AP_TERM_TAC THEN EQ_TAC THEN DISCH_TAC THENL [MP_TAC (← ISPECL [(← q r"s:K->bool"), (← q r"L:(K->int)->bool"), (← q r"y:K->int"), (← q r"x:K->int"), (← q r"x':K->int")] INT_LATTICE_CONG_TRANS) THEN ASM_REWRITE_TAC [], MP_TAC (← ISPECL [(← q r"s:K->bool"), (← q r"L:(K->int)->bool"), (← q r"x:K->int"), (← q r"x':K->int")] INT_LATTICE_CONG_SYM) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"s:K->bool"), (← q r"L:(K->int)->bool"), (← q r"y:K->int"), (← q r"x':K->int"), (← q r"x:K->int")] INT_LATTICE_CONG_TRANS) THEN ASM_REWRITE_TAC []])

  let INT_COSETS_COVER ← prove
    r"!s (L:(K->int)->bool) R.
        int_lattice s L /\
        R SUBSET {x | !i. ~(i IN s) ==> x i = &0} /\
        (!x. (!i. ~(i IN s) ==> x i = &0)
             ==> ?r. r IN R /\ (\i. x i - r i) IN L)
        ==> int_cosets s L =
            IMAGE (\x. {y | (!i. ~(i IN s) ==> y i = &0) /\
                            (\i. y i - x i) IN L}) R"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [int_cosets] THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN X_GEN_TAC (← q r"C:(K->int)->bool") THEN EQ_TAC THENL [DISCH_THEN (X_CHOOSE_THEN (← q r"x:K->int") (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"x:K->int"))) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"r:K->int") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC INT_LATTICE_COSET_EQ THEN ASM_REWRITE_TAC [], DISCH_THEN (X_CHOOSE_THEN (← q r"r:K->int") (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN EXISTS_TAC (← q r"r:K->int") THEN REWRITE_TAC [] THEN UNDISCH_TAC (← q r"(R:(K->int)->bool) SUBSET {x | !i. ~(i IN s) ==> x i = &0}") THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC []])

  let INT_COSETS_TRANSVERSAL ← prove
    r"!s (L:(K->int)->bool) R n.
        int_lattice s L /\
        R SUBSET {x | !i. ~(i IN s) ==> x i = &0} /\
        (!x. (!i. ~(i IN s) ==> x i = &0)
             ==> ?r. r IN R /\ (\i. x i - r i) IN L) /\
        (!r r'. r IN R /\ r' IN R /\ (\i. r i - r' i) IN L ==> r = r') /\
        R HAS_SIZE n
        ==> int_cosets s L HAS_SIZE n"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP INT_LATTICE_0)) THEN MP_TAC (← ISPECL [(← q r"s:K->bool"), (← q r"L:(K->int)->bool"), (← q r"R:(K->int)->bool")] INT_COSETS_COVER) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_REWRITE_TAC [] THEN MAP_EVERY X_GEN_TAC [(← q r"r:K->int"), (← q r"r':K->int")] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"r:K->int")) o (REWRITE_RULE [EXTENSION]))) THEN REWRITE_TAC [IN_ELIM_THM, INT_SUB_REFL] THEN SUBGOAL_THEN (← q r"!i. ~(i IN s) ==> (r:K->int) i = &0") (fun th => REWRITE_TAC [th]) THENL [UNDISCH_TAC (← q r"(R:(K->int)->bool) SUBSET {x | !i. ~(i IN s) ==> x i = &0}") THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC [], ASM_REWRITE_TAC []])

  let INT_COSETS_FINITE ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"num_of_int(abs d)"
    let v2 ← SPEC q1 HAS_SIZE_INT_SEG_LT
    let q3 ← q r"(s:A->bool) HAS_SIZE n
    ==> FINITE(IMAGE (f:A->B) s) /\ CARD(IMAGE f s) <= n"
    let r4 ← MESON [FINITE_IMAGE, CARD_IMAGE_LE, HAS_SIZE, LE_TRANS] q3
    let q5 ← q r"d:int"
    let q6 ← q r"(x:K->int) i"
    let v7 ← SPECL [q6, q5] INT_DIVISION
    let q8 ← q r"i:K"
    let q9 ← q r"\i. if i IN s then (x:K->int) i div d else &0"
    let q10 ← q r"d:int"
    let q11 ← q r"(x:K->int) i"
    let v12 ← SPECL [q11, q10] INT_DIVISION
    let q13 ← q r"i:K"
    let q14 ← q r"\i. if i IN s then (x:K->int) i rem d else &0"
    let q15 ← q r"x:K->int"
    let q16 ← q r"{x:K->int | (!i. i IN s ==> x i IN {k | &0 <= k /\ k < abs d}) /\
                 (!i. ~(i IN s) ==> x i = &0)}"
    let q17 ← q r"L:(K->int)->bool"
    let q18 ← q r"s:K->bool"
    let v19 ← ISPECL [q18, q17, q16] INT_COSETS_COVER
    prove
      r"!s (L:(K->int)->bool) d.
          FINITE s /\ int_lattice s L /\ ~(d = &0) /\
          (!x. (!i. ~(i IN s) ==> x i = &0) ==> (\i. d * x i) IN L)
          ==> FINITE(int_cosets s L) /\
              CARD(int_cosets s L) <= num_of_int(abs d) EXP CARD s"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC v19 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN MESON_TAC [], X_GEN_TAC q15 THEN DISCH_TAC THEN EXISTS_TAC q14 THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL [X_GEN_TAC q13 THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC v12 THEN ASM_REWRITE_TAC [] THEN INT_ARITH_TAC, SIMP_TAC [], FIRST_X_ASSUM (MP_TAC o (SPEC q9)) THEN ANTS_TAC THENL [SIMP_TAC [], ALL_TAC] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC q8 THEN COND_CASES_TAC THEN ASM_SIMP_TAC [INT_MUL_RZERO, INT_SUB_RZERO] THEN MP_TAC v7 THEN ASM_REWRITE_TAC [] THEN INT_ARITH_TAC]], DISCH_THEN SUBST1_TAC] THEN MATCH_MP_TAC r4 THEN MATCH_MP_TAC HAS_SIZE_FUNSPACE THEN ASM_REWRITE_TAC [HAS_SIZE] THEN MP_TAC v2 THEN SIMP_TAC [INT_OF_NUM_OF_INT, INT_ABS_POS, HAS_SIZE])

  let INT_LATTICE_COORDINATE_GENERATOR ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← INTEGER_RULE (← q r"!d:int. d divides d")
    prove
      r"!s (L:(K->int)->bool) a.
          int_lattice s L ==> ?w. w IN L /\ !x. x IN L ==> (w a) divides (x a)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP INT_LATTICE_CLOSED)) THEN ASM_CASES_TAC (← q r"!x:K->int. x IN L ==> x a = &0") THENL [EXISTS_TAC (← q r"(\i. &0):K->int") THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"x:K->int") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"x:K->int"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [r1], ALL_TAC] THEN FIRST_X_ASSUM ((X_CHOOSE_THEN (← q r"x0:K->int") STRIP_ASSUME_TAC) o (REWRITE_RULE [NOT_FORALL_THM, NOT_IMP])) THEN SUBGOAL_THEN (← q r"?n. 0 < n /\ ?x:K->int. x IN L /\ x a = &n") MP_TAC THENL [ASM_CASES_TAC (← q r"&0 < (x0:K->int) a") THENL [EXISTS_TAC (← q r"num_of_int((x0:K->int) a)") THEN ASM_SIMP_TAC [(← GSYM INT_OF_NUM_LT), INT_OF_NUM_OF_INT, INT_LT_IMP_LE] THEN EXISTS_TAC (← q r"x0:K->int") THEN ASM_SIMP_TAC [INT_OF_NUM_OF_INT, INT_LT_IMP_LE], SUBGOAL_THEN (← q r"&0 < --((x0:K->int) a)") ASSUME_TAC THENL [ASM_INT_ARITH_TAC, ALL_TAC] THEN EXISTS_TAC (← q r"num_of_int(--((x0:K->int) a))") THEN ASM_SIMP_TAC [(← GSYM INT_OF_NUM_LT), INT_OF_NUM_OF_INT, INT_LT_IMP_LE] THEN EXISTS_TAC (← q r"\i. --((x0:K->int) i)") THEN ASM_SIMP_TAC [INT_OF_NUM_OF_INT, INT_LT_IMP_LE, ETA_AX]], ALL_TAC] THEN GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"n:num") (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"w:K->int") STRIP_ASSUME_TAC)) (LABEL_TAC "min"))) THEN EXISTS_TAC (← q r"w:K->int") THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"x:K->int") THEN DISCH_TAC THEN REWRITE_TAC [(← GSYM INT_REM_EQ_0)] THEN SUBGOAL_THEN (← q r"~(&n:int = &0)") ASSUME_TAC THENL [REWRITE_TAC [INT_OF_NUM_EQ] THEN ASM_ARITH_TAC, ALL_TAC] THEN MP_TAC (← SPECL [(← q r"(x:K->int) a"), (← q r"&n:int")] INT_DIVISION) THEN ASM_REWRITE_TAC [INT_ABS_NUM] THEN ABBREV_TAC (← q r"q = (x:K->int) a div &n") THEN ABBREV_TAC (← q r"r = (x:K->int) a rem &n") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"?y:K->int. y IN L /\ y a = r") ASSUME_TAC THENL [EXISTS_TAC (← q r"\i. (x:K->int) i - q * w i") THEN CONJ_TAC THENL [ASM_SIMP_TAC [ETA_AX], ASM_REWRITE_TAC [] THEN ASM_INT_ARITH_TAC], ALL_TAC] THEN REMOVE_THEN "min" (MP_TAC o (SPEC (← q r"num_of_int r"))) THEN ASM_SIMP_TAC [(← GSYM INT_OF_NUM_LT), INT_OF_NUM_OF_INT] THEN ASM_INT_ARITH_TAC)

  let INT_LATTICE_SPLIT ← prove
    r"!a t (L:(K->int)->bool).
        int_lattice (a INSERT t) L
        ==> int_lattice t {x | x IN L /\ x a = &0} /\
            ?w. w IN L /\ !x. x IN L ==> (w a) divides (x a)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC [INT_LATTICE_COORDINATE_GENERATOR]] THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP INT_LATTICE_CLOSED)) THEN REWRITE_TAC [int_lattice, SUBSET, IN_ELIM_THM] THEN ASM_SIMP_TAC [INT_SUB_REFL] THEN X_GEN_TAC (← q r"x:K->int") THEN STRIP_TAC THEN X_GEN_TAC (← q r"i:K") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"i:K = a") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"a INSERT t:K->bool"), (← q r"L:(K->int)->bool"), (← q r"x:K->int"), (← q r"i:K")] INT_LATTICE_SUPPORT) THEN ASM_REWRITE_TAC [IN_INSERT])

  let INT_MATRIX_IMAGE_INSERT ← prove
    r"!a t (w:K->int) M x.
        FINITE t /\ ~(a IN t) /\ (!i. ~(i IN a INSERT t) ==> w i = &0)
        ==> (x IN int_matrix_image (a INSERT t)
                (\i j. if j = a then w i else if i IN t then M i j else &0) <=>
             ?q y. y IN int_matrix_image t M /\ x = (\i. q * w i + y i))"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"!z. (\i. if i IN a INSERT t
             then isum (a INSERT t)
                    (\j. (if j = a then (w:K->int) i
                          else if i IN t then (M:K->K->int) i j else &0) *
                         z j)
             else &0) =
        (\i. z a * w i + (if i IN t then isum t (\j. M i j * z j) else &0))") ASSUME_TAC THENL [X_GEN_TAC (← q r"z:K->int") THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"i:K") THEN ASM_SIMP_TAC [ISUM_CLAUSES] THEN SUBGOAL_THEN (← q r"isum t (\j. (if j = a then (w:K->int) i
                   else if i IN t then (M:K->K->int) i j else &0) * z j) =
      isum t (\j. (if i IN t then M i j else &0) * z j)") SUBST1_TAC THENL [MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC (← q r"j:K") THEN DISCH_TAC THEN BETA_TAC THEN SUBGOAL_THEN (← q r"~(j:K = a)") (fun th => REWRITE_TAC [th]) THEN ASM_MESON_TAC [], ALL_TAC] THEN REWRITE_TAC [IN_INSERT] THEN ASM_CASES_TAC (← q r"(i:K) IN t") THEN ASM_REWRITE_TAC [] THENL [INT_ARITH_TAC, REWRITE_TAC [INT_MUL_LZERO, ISUM_0, INT_ADD_RID] THEN ASM_CASES_TAC (← q r"i:K = a") THEN ASM_REWRITE_TAC [] THENL [INT_ARITH_TAC, FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"i:K"))) THEN ASM_REWRITE_TAC [IN_INSERT] THEN DISCH_THEN SUBST1_TAC THEN INT_ARITH_TAC]], ALL_TAC] THEN ASM_REWRITE_TAC [INT_MATRIX_IMAGE_IN] THEN EQ_TAC THENL [DISCH_THEN (X_CHOOSE_THEN (← q r"z:K->int") SUBST1_TAC) THEN MAP_EVERY EXISTS_TAC [(← q r"(z:K->int) a"), (← q r"\i. if i IN t then isum t (\j. (M:K->K->int) i j * z j) else &0")] THEN CONJ_TAC THENL [EXISTS_TAC (← q r"z:K->int") THEN REWRITE_TAC [], REWRITE_TAC []], REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"q:int"), (← q r"y:K->int")] THEN DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"z:K->int") ASSUME_TAC) SUBST1_TAC) THEN FIRST_X_ASSUM SUBST1_TAC THEN EXISTS_TAC (← q r"\j. if j = a then q else (z:K->int) j") THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"i:K") THEN COND_CASES_TAC THEN REWRITE_TAC [] THEN AP_TERM_TAC THEN MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC (← q r"j:K") THEN DISCH_TAC THEN BETA_TAC THEN SUBGOAL_THEN (← q r"~(j:K = a)") (fun th => REWRITE_TAC [th]) THEN ASM_MESON_TAC []])

  -- @@RETURN BEGIN
  return { int_lattice, int_matrix_image, int_cosets, INT_LATTICE_0, INT_LATTICE_SUB,
           INT_LATTICE_SUPPORT, INT_LATTICE_NEG, INT_LATTICE_ADD, INT_LATTICE_CMUL,
           INT_LATTICE_CLOSED, INT_LATTICE_ISUM, INT_MATRIX_IMAGE_IN,
           INT_LATTICE_INT_MATRIX_IMAGE, INT_MATRIX_IMAGE_COLUMN,
           INT_MATRIX_IMAGE_SUBSET, INT_MATRIX_IMAGE_FACTOR, INT_DET_MUL,
           INT_DET_INSERT_ROW, INT_MATRIX_MUL_ASSOC, INT_MATRIX_IMAGE_INJECTIVE,
           INT_LATTICE_FULL_RANK, INT_MATRIX_IMAGE_EQ_DET,
           INT_PRIMITIVE_UNIMODULAR_COLUMN, INT_DET_BOUND, INT_LATTICE_CONG_SYM,
           INT_LATTICE_CONG_TRANS, INT_LATTICE_COSET_EQ, INT_COSETS_COVER,
           INT_COSETS_TRANSVERSAL, INT_COSETS_FINITE, INT_LATTICE_COORDINATE_GENERATOR,
           INT_LATTICE_SPLIT, INT_MATRIX_IMAGE_INSERT }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- zlattice.ml phrases from line 773 to 1057                              -/
/- ---------------------------------------------------------------------- -/

structure Zlattice02 where
  -- @@FIELDS
  INT_LATTICE_INSERT_IMAGE : thm
  INT_LATTICE_MATRIX_IMAGE : thm
  INT_LATTICE_TRANSVERSAL_INSERT : thm
  INT_MATRIX_IMAGE_TRANSVERSAL : thm
  INT_COSETS_MATRIX_IMAGE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupZlattice02 [HolBase] (D : ZlatticeDeps) (BZlattice01 : Zlattice01) :
    ExceptT String IO Zlattice02 := do
  -- @@SCOPE BEGIN
  let { ASM_INT_ARITH_TAC, ASM_MESON_TAC, INT_ARITH_TAC, MESON, MESON_TAC, SET_RULE, .. } := D
  let { CARD_SING, DE_MORGAN_THM, EQ_TRANS, ETA_AX, EXISTS_IN_IMAGE, EXISTS_PAIR_THM,
        EXTENSION, FINITE_INDUCT_STRONG, FINITE_INSERT, FINITE_SING, FORALL_IN_IMAGE,
        FORALL_PAIR_THM, FUN_EQ_THM, HAS_SIZE, HAS_SIZE_IMAGE_INJ, HAS_SIZE_NUMSEG_LT,
        HAS_SIZE_PRODUCT, IMP_CONJ, INTEGER_RING, INT_ABS_MUL, INT_ABS_NUM,
        INT_ABS_POS, INT_ABS_ZERO, INT_DIVIDES_LE, INT_DIVISION, INT_ENTIRE,
        INT_OF_NUM_EQ, INT_OF_NUM_LT, INT_OF_NUM_OF_INT, INT_SUB_REFL,
        IN_ELIM_PAIR_THM, IN_ELIM_THM, IN_INSERT, IN_SING, LEFT_IMP_EXISTS_THM,
        NOT_IN_EMPTY, NUM_OF_INT_MUL, NUM_OF_INT_OF_NUM, PAIR_EQ, RIGHT_FORALL_IMP_THM,
        RING_DET_EMPTY, RING_DET_EQ, SUBSET, int_divides, .. } := D.core1
  let { INT_COSETS_TRANSVERSAL, INT_DET_INSERT_ROW, INT_LATTICE_0, INT_LATTICE_CLOSED,
        INT_LATTICE_INT_MATRIX_IMAGE, INT_LATTICE_SPLIT, INT_LATTICE_SUPPORT,
        INT_MATRIX_IMAGE_EQ_DET, INT_MATRIX_IMAGE_IN, INT_MATRIX_IMAGE_INSERT, .. } := BZlattice01
  -- @@SCOPE END

  let INT_LATTICE_INSERT_IMAGE ← prove
    r"!a t (L:(K->int)->bool) w M0.
        FINITE t /\ ~(a IN t) /\ int_lattice (a INSERT t) L /\
        w IN L /\ (!x. x IN L ==> (w a) divides (x a)) /\
        {x | x IN L /\ x a = &0} = int_matrix_image t M0
        ==> L = int_matrix_image (a INSERT t)
                  (\i j. if j = a then w i else if i IN t then M0 i j else &0)"
    (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "div") (LABEL_TAC "M0")))))) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP INT_LATTICE_CLOSED)) THEN REWRITE_TAC [EXTENSION] THEN X_GEN_TAC (← q r"x:K->int") THEN MP_TAC (← ISPECL [(← q r"a:K"), (← q r"t:K->bool"), (← q r"w:K->int"), (← q r"M0:K->K->int"), (← q r"x:K->int")] INT_MATRIX_IMAGE_INSERT) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"i:K") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"a INSERT t:K->bool"), (← q r"L:(K->int)->bool"), (← q r"w:K->int"), (← q r"i:K")] INT_LATTICE_SUPPORT) THEN ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN REMOVE_THEN "M0" (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM th)])) THEN REWRITE_TAC [IN_ELIM_THM] THEN EQ_TAC THENL [DISCH_TAC THEN REMOVE_THEN "div" (MP_TAC o (SPEC (← q r"x:K->int"))) THEN ASM_REWRITE_TAC [int_divides] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"k:int")) THEN MAP_EVERY EXISTS_TAC [(← q r"k:int"), (← q r"\i. (x:K->int) i - k * w i")] THEN REPEAT CONJ_TAC THENL [ASM_SIMP_TAC [ETA_AX], ASM_REWRITE_TAC [] THEN INT_ARITH_TAC, REWRITE_TAC [FUN_EQ_THM] THEN INT_ARITH_TAC], REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"q:int"), (← q r"y:K->int")] THEN DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST1_TAC) THEN ASM_SIMP_TAC [ETA_AX]])

  let INT_LATTICE_MATRIX_IMAGE ← prove
    r"!s (L:(K->int)->bool).
        FINITE s /\ int_lattice s L ==> ?M. L = int_matrix_image s M"
    (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL [X_GEN_TAC (← q r"L:(K->int)->bool") THEN DISCH_TAC THEN EXISTS_TAC (← q r"(\i j. &0):K->K->int") THEN REWRITE_TAC [EXTENSION, INT_MATRIX_IMAGE_IN, NOT_IN_EMPTY] THEN X_GEN_TAC (← q r"x:K->int") THEN EQ_TAC THENL [DISCH_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"i:K") THEN MP_TAC (← ISPECL [(← q r"{}:K->bool"), (← q r"L:(K->int)->bool"), (← q r"x:K->int"), (← q r"i:K")] INT_LATTICE_SUPPORT) THEN ASM_REWRITE_TAC [NOT_IN_EMPTY], DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC [INT_LATTICE_0]], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"a:K"), (← q r"t:K->bool")] THEN STRIP_TAC THEN X_GEN_TAC (← q r"L:(K->int)->bool") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"a:K"), (← q r"t:K->bool"), (← q r"L:(K->int)->bool")] INT_LATTICE_SPLIT) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"w:K->int") STRIP_ASSUME_TAC)) THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"{x | x IN L /\ (x:K->int) a = &0}"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"M0:K->K->int")) THEN EXISTS_TAC (← q r"\i j. if j = a then (w:K->int) i
                    else if i IN t then (M0:K->K->int) i j else &0") THEN MATCH_MP_TAC INT_LATTICE_INSERT_IMAGE THEN ASM_REWRITE_TAC [])

  let INT_LATTICE_TRANSVERSAL_INSERT ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"{(m:num,r:K->int) | m < N /\ r IN R0} =
        {(m,r) | m IN {m | m < N} /\ r IN R0}"
    let r2 ← SET_RULE q1
    let q3 ← q r"i:K = a"
    let q4 ← q r"i:K"
    let q5 ← q r"i:K"
    let q6 ← q r"a:K"
    let q7 ← q r"~((a:K) IN t)"
    let q8 ← q r"(r2:K->int) IN R0"
    let q9 ← q r"(r1:K->int) IN R0"
    let q10 ← q r"(r1:K->int) a = &0 /\ (r2:K->int) a = &0"
    let q11 ← q r"r2:K->int"
    let q12 ← q r"m2:num"
    let q13 ← q r"r1:K->int"
    let q14 ← q r"m1:num"
    let q15 ← q r"i:K"
    let q16 ← q r"(x:K->int) IN L ==> y = x ==> y IN L"
    let r17 ← MESON [] q16
    let q18 ← q r"r1:K->int = r2"
    let v19 ← GSYM INT_OF_NUM_EQ
    let v20 ← GSYM INT_OF_NUM_LT
    let q21 ← q r"m2:num < N"
    let q22 ← q r"m1:num < N"
    let q23 ← q r"\i. (if i = a then &m1 else (r1:K->int) i) -
            (if i = a then &m2 else r2 i)"
    let q24 ← q r"m1:num = m2"
    let q25 ← q r"~((a:K) IN t)"
    let q26 ← q r"(r2:K->int) IN R0"
    let q27 ← q r"(r1:K->int) IN R0"
    let q28 ← q r"(r1:K->int) a = &0 /\ (r2:K->int) a = &0"
    let q29 ← q r"r2:K->int"
    let q30 ← q r"m2:num"
    let q31 ← q r"r1:K->int"
    let q32 ← q r"m1:num"
    let q33 ← q r"i:K"
    let q34 ← q r"(\i. (x:K->int) i - (if i = a then rho else r0 i)) =
      (\i. q * w i + ((if i = a then &0 else x i - q * w i) - r0 i))"
    let v35 ← GSYM INT_OF_NUM_LT
    let q36 ← q r"r0:K->int"
    let q37 ← q r"num_of_int rho"
    let q38 ← q r"r0:K->int"
    let q39 ← q r"i:K"
    let q40 ← q r"w:K->int"
    let q41 ← q r"L:(K->int)->bool"
    let q42 ← q r"a INSERT t:K->bool"
    let v43 ← ISPECL [q42, q41, q40, q39] INT_LATTICE_SUPPORT
    let q44 ← q r"i:K"
    let q45 ← q r"\i. if i = a then &0 else (x:K->int) i - q * w i"
    let q46 ← q r"rho = (x:K->int) a rem w a"
    let q47 ← q r"q = (x:K->int) a div w a"
    let q48 ← q r"(w:K->int) a"
    let q49 ← q r"(x:K->int) a"
    let v50 ← SPECL [q49, q48] INT_DIVISION
    let q51 ← q r"x:K->int"
    let q52 ← q r"~((i:K) IN t)"
    let q53 ← q r"(r:K->int) IN R0"
    let q54 ← q r"r:K->int"
    let q55 ← q r"m:num"
    let q56 ← q r"IMAGE (\p. (\i. if i = a then &(FST p) else SND p i):K->int)
                    {(m:num,r:K->int) | m < N /\ r IN R0}"
    let q57 ← q r"&N:int = abs((w:K->int) a)"
    let q58 ← q r"N = num_of_int(abs((w:K->int) a))"
    prove
      r"!a t (L:(K->int)->bool) w R0 n.
          FINITE t /\ ~(a IN t) /\ int_lattice (a INSERT t) L /\
          w IN L /\ ~(w a = &0) /\
          R0 SUBSET {x | !i. ~(i IN t) ==> x i = &0} /\ R0 HAS_SIZE n /\
          (!x. x IN L ==> (w a) divides (x a)) /\
          (!x. (!i. ~(i IN t) ==> x i = &0)
               ==> ?r. r IN R0 /\ (\i. x i - r i) IN {x | x IN L /\ x a = &0}) /\
          (!r r'. r IN R0 /\ r' IN R0 /\
                  (\i. r i - r' i) IN {x | x IN L /\ x a = &0} ==> r = r')
          ==> ?R. R SUBSET {x | !i. ~(i IN a INSERT t) ==> x i = &0} /\
                  (!x. (!i. ~(i IN a INSERT t) ==> x i = &0)
                       ==> ?r. r IN R /\ (\i. x i - r i) IN L) /\
                  (!r r'. r IN R /\ r' IN R /\ (\i. r i - r' i) IN L
                          ==> r = r') /\
                  R HAS_SIZE (num_of_int(abs(w a)) * n)"
      (REPEAT GEN_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "supp") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "div") (CONJUNCTS_THEN2 (LABEL_TAC "cover") (LABEL_TAC "unique")))))))))) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP INT_LATTICE_CLOSED)) THEN ABBREV_TAC q58 THEN SUBGOAL_THEN q57 ASSUME_TAC THENL [EXPAND_TAC "N" THEN SIMP_TAC [INT_OF_NUM_OF_INT, INT_ABS_POS], ALL_TAC] THEN EXISTS_TAC q56 THEN REWRITE_TAC [SUBSET, IN_ELIM_THM, IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_IMAGE, EXISTS_IN_IMAGE, FORALL_PAIR_THM, EXISTS_PAIR_THM, IN_ELIM_PAIR_THM, IN_INSERT, DE_MORGAN_THM] THEN REPEAT CONJ_TAC THENL [REMOVE_THEN "unique" (fun (_ : thm) => ALL_TAC) THEN X_GEN_TAC q55 THEN DISCH_TAC THEN X_GEN_TAC q54 THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MAP_EVERY UNDISCH_TAC [q53, q52] THEN USE_THEN "supp" (fun th => tactic_of do pure (MESON_TAC [(← REWRITE_RULE [SUBSET, IN_ELIM_THM] th)])), REMOVE_THEN "unique" (fun (_ : thm) => ALL_TAC) THEN REMOVE_THEN "supp" (fun (_ : thm) => ALL_TAC) THEN X_GEN_TAC q51 THEN DISCH_TAC THEN MP_TAC v50 THEN ASM_REWRITE_TAC [] THEN MAP_EVERY ABBREV_TAC [q47, q46] THEN STRIP_TAC THEN REMOVE_THEN "cover" (MP_TAC o (SPEC q45)) THEN ANTS_TAC THENL [X_GEN_TAC q44 THEN DISCH_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [] THEN MP_TAC v43 THEN ASM_SIMP_TAC [IN_INSERT] THEN INT_ARITH_TAC, DISCH_THEN ((X_CHOOSE_THEN q38 STRIP_ASSUME_TAC) o BETA_RULE)] THEN MAP_EVERY EXISTS_TAC [q37, q36] THEN ASM_SIMP_TAC [v35, INT_OF_NUM_OF_INT] THEN SUBGOAL_THEN q34 SUBST1_TAC THENL [REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC q33 THEN COND_CASES_TAC THEN ASM_SIMP_TAC [] THEN ASM_INT_ARITH_TAC, ASM_SIMP_TAC [ETA_AX]], X_GEN_TAC q32 THEN DISCH_TAC THEN X_GEN_TAC q31 THEN DISCH_TAC THEN X_GEN_TAC q30 THEN DISCH_TAC THEN X_GEN_TAC q29 THEN REPEAT DISCH_TAC THEN SUBGOAL_THEN q28 STRIP_ASSUME_TAC THENL [MAP_EVERY UNDISCH_TAC [q27, q26, q25] THEN USE_THEN "supp" (fun th => tactic_of do pure (MESON_TAC [(← REWRITE_RULE [SUBSET, IN_ELIM_THM] th)])), ALL_TAC] THEN SUBGOAL_THEN q24 SUBST_ALL_TAC THENL [REMOVE_THEN "div" (MP_TAC o (SPEC q23)) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (MATCH_MP INT_DIVIDES_LE)) THEN UNDISCH_TAC q22 THEN UNDISCH_TAC q21 THEN ASM_REWRITE_TAC [v20, v19] THEN INT_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN q18 (fun th => REWRITE_TAC [th]) THEN REMOVE_THEN "unique" MATCH_MP_TAC THEN ASM_SIMP_TAC [INT_SUB_REFL] THEN FIRST_X_ASSUM (MATCH_MP_TAC o (MATCH_MP r17)) THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC q15 THEN COND_CASES_TAC THEN ASM_SIMP_TAC [INT_SUB_REFL], REMOVE_THEN "unique" (fun (_ : thm) => ALL_TAC) THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL [REWRITE_TAC [FORALL_PAIR_THM, IN_ELIM_PAIR_THM, PAIR_EQ, FUN_EQ_THM] THEN MAP_EVERY X_GEN_TAC [q14, q13, q12, q11] THEN STRIP_TAC THEN SUBGOAL_THEN q10 STRIP_ASSUME_TAC THENL [MAP_EVERY UNDISCH_TAC [q9, q8, q7] THEN USE_THEN "supp" (fun th => tactic_of do pure (MESON_TAC [(← REWRITE_RULE [SUBSET, IN_ELIM_THM] th)])), ALL_TAC] THEN CONJ_TAC THENL [FIRST_X_ASSUM (MP_TAC o (SPEC q6)) THEN REWRITE_TAC [INT_OF_NUM_EQ], X_GEN_TAC q5 THEN FIRST_X_ASSUM (MP_TAC o (SPEC q4)) THEN ASM_CASES_TAC q3 THEN ASM_SIMP_TAC []], REWRITE_TAC [r2] THEN MATCH_MP_TAC HAS_SIZE_PRODUCT THEN ASM_REWRITE_TAC [HAS_SIZE_NUMSEG_LT]]])

  let INT_MATRIX_IMAGE_TRANSVERSAL ← prove
    r"!s (M:K->K->int).
        FINITE s /\ ~(ring_det integer_ring s M = &0)
        ==> ?R. R SUBSET {x | !i. ~(i IN s) ==> x i = &0} /\
                (!x. (!i. ~(i IN s) ==> x i = &0)
                     ==> ?r. r IN R /\
                             (\i. x i - r i) IN int_matrix_image s M) /\
                (!r r'. r IN R /\ r' IN R /\
                        (\i. r i - r' i) IN int_matrix_image s M ==> r = r') /\
                R HAS_SIZE num_of_int(abs(ring_det integer_ring s M))"
    (ONCE_REWRITE_TAC [IMP_CONJ] THEN ONCE_REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL [X_GEN_TAC (← q r"M:K->K->int") THEN DISCH_TAC THEN EXISTS_TAC (← q r"{(\i. &0):K->int}") THEN REWRITE_TAC [RING_DET_EMPTY, INTEGER_RING, INT_ABS_NUM, NUM_OF_INT_OF_NUM, HAS_SIZE, FINITE_SING, CARD_SING, NOT_IN_EMPTY, SUBSET, IN_SING, IN_ELIM_THM, INT_MATRIX_IMAGE_IN] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"(\i. &0):K->int") THEN ASM_REWRITE_TAC [FUN_EQ_THM] THEN INT_ARITH_TAC, ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"a:K"), (← q r"t:K->bool")] THEN STRIP_TAC THEN X_GEN_TAC (← q r"M:K->K->int") THEN DISCH_TAC THEN ABBREV_TAC (← q r"L = int_matrix_image (a INSERT t) (M:K->K->int)") THEN SUBGOAL_THEN (← q r"int_lattice (a INSERT t) (L:(K->int)->bool)") ASSUME_TAC THENL [EXPAND_TAC "L" THEN MATCH_MP_TAC INT_LATTICE_INT_MATRIX_IMAGE THEN ASM_REWRITE_TAC [FINITE_INSERT], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"a:K"), (← q r"t:K->bool"), (← q r"L:(K->int)->bool")] INT_LATTICE_SPLIT) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"w:K->int") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "div")))) THEN MP_TAC (← ISPECL [(← q r"t:K->bool"), (← q r"{x | x IN L /\ (x:K->int) a = &0}")] INT_LATTICE_MATRIX_IMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"M0:K->K->int") (LABEL_TAC "M0")) THEN ABBREV_TAC (← q r"N = \i j. if j = a then (w:K->int) i
                        else if i IN t then (M0:K->K->int) i j else &0") THEN SUBGOAL_THEN (← q r"L = int_matrix_image (a INSERT t) (N:K->K->int)") ASSUME_TAC THENL [EXPAND_TAC "N" THEN MATCH_MP_TAC INT_LATTICE_INSERT_IMAGE THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_det integer_ring (a INSERT t) (N:K->K->int) =
    w a * ring_det integer_ring t M0") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"a:K"), (← q r"t:K->bool"), (← q r"N:K->K->int")] INT_DET_INSERT_ROW) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"j:K") THEN DISCH_TAC THEN EXPAND_TAC "N" THEN SUBGOAL_THEN (← q r"~(j:K = a)") (fun th => REWRITE_TAC [th]) THENL [ASM_MESON_TAC [], ASM_REWRITE_TAC []], DISCH_THEN SUBST1_TAC] THEN EXPAND_TAC "N" THEN REWRITE_TAC [] THEN AP_TERM_TAC THEN MATCH_MP_TAC RING_DET_EQ THEN MAP_EVERY X_GEN_TAC [(← q r"i:K"), (← q r"j:K")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"~(j:K = a)") (fun th => REWRITE_TAC [th]) THENL [ASM_MESON_TAC [], ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"abs(ring_det integer_ring (a INSERT t) (N:K->K->int)) =
    abs(ring_det integer_ring (a INSERT t) (M:K->K->int))") ASSUME_TAC THENL [MATCH_MP_TAC INT_MATRIX_IMAGE_EQ_DET THEN ASM_REWRITE_TAC [FINITE_INSERT], ALL_TAC] THEN SUBGOAL_THEN (← q r"~((w:K->int) a = &0) /\ ~(ring_det integer_ring t (M0:K->K->int) = &0)") STRIP_ASSUME_TAC THENL [MAP_EVERY UNDISCH_TAC [(← q r"ring_det integer_ring (a INSERT t) (N:K->K->int) =
       w a * ring_det integer_ring t M0"), (← q r"abs(ring_det integer_ring (a INSERT t) (N:K->K->int)) =
       abs(ring_det integer_ring (a INSERT t) (M:K->K->int))"), (← q r"~(ring_det integer_ring (a INSERT t) (M:K->K->int) = &0)")] THEN REWRITE_TAC [(← GSYM DE_MORGAN_THM), (← GSYM INT_ENTIRE)] THEN MESON_TAC [INT_ABS_ZERO], ALL_TAC] THEN SUBGOAL_THEN (← q r"num_of_int(abs((w:K->int) a)) *
    num_of_int(abs(ring_det integer_ring t (M0:K->K->int))) =
    num_of_int(abs(ring_det integer_ring (a INSERT t) (M:K->K->int)))") (LABEL_TAC "size") THENL [SIMP_TAC [(← GSYM NUM_OF_INT_MUL), INT_ABS_POS, (← GSYM INT_ABS_MUL)] THEN AP_TERM_TAC THEN TRANS_TAC EQ_TRANS (← q r"abs(ring_det integer_ring (a INSERT t) (N:K->K->int))") THEN CONJ_TAC THENL [AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC, FIRST_ASSUM ACCEPT_TAC], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"M0:K->K->int"))) THEN ASM_REWRITE_TAC [] THEN USE_THEN "M0" (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM th)])) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"R0:(K->int)->bool") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"a:K"), (← q r"t:K->bool"), (← q r"L:(K->int)->bool"), (← q r"w:K->int"), (← q r"R0:(K->int)->bool"), (← q r"num_of_int(abs(ring_det integer_ring t (M0:K->K->int)))")] INT_LATTICE_TRANSVERSAL_INSERT) THEN ASM_REWRITE_TAC [])

  let INT_COSETS_MATRIX_IMAGE ← prove
    r"!s (M:K->K->int).
        FINITE s /\ ~(ring_det integer_ring s M = &0)
        ==> int_cosets s (int_matrix_image s M) HAS_SIZE
            num_of_int(abs(ring_det integer_ring s M))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"s:K->bool"), (← q r"M:K->K->int")] INT_MATRIX_IMAGE_TRANSVERSAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"R:(K->int)->bool") STRIP_ASSUME_TAC) THEN MATCH_MP_TAC INT_COSETS_TRANSVERSAL THEN EXISTS_TAC (← q r"R:(K->int)->bool") THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC INT_LATTICE_INT_MATRIX_IMAGE THEN ASM_REWRITE_TAC [])

  -- @@RETURN BEGIN
  return { INT_LATTICE_INSERT_IMAGE, INT_LATTICE_MATRIX_IMAGE,
           INT_LATTICE_TRANSVERSAL_INSERT, INT_MATRIX_IMAGE_TRANSVERSAL,
           INT_COSETS_MATRIX_IMAGE }
  -- @@RETURN END

end HolANT.Zlattice
