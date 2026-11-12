/- ========================================================================= -/
/- ANT: Hermite inequality for positive definite real quadratic ...        -/
/- ========================================================================= -/
/- File: HolANT/HermiteInequality.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/hermite_inequality.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/anthermiteinequalitydiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/isum.ml, Library/floor.ml, Library/permutations.ml, Library/ring_det.ml, Library/products.ml, ANT/algmisc.ml, ANT/zlattice.ml, ANT/linear_forms.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.HermiteInequality fills them).

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
import HolLibrary.Isum
import HolLibrary.Floor
import HolLibrary.Permutations
import HolLibrary.RingDet
import HolLibrary.Products
import HolANT.Algmisc
import HolANT.Zlattice
import HolANT.LinearForms

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.Algmisc
open HolANT.Zlattice
open HolANT.LinearForms

namespace HolANT.HermiteInequality

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD1 CARD_CLAUSES CARD_EQ_0 EXISTS_IN_IMAGE FINITE_IMAGE FINITE_INDUCT_STRONG
   FINITE_INSERT FINITE_INT_SEG FINITE_PRODUCT_DEPENDENT FINITE_SING
   FINITE_SUBSET FORALL_IN_IMAGE FUN_EQ_THM IMAGE_EQ_EMPTY IMP_CONJ
   INF_FINITE_LEMMA INTEGER_RING INTEGER_RING_SUM INTEGER_ROUND
   INTEGRAL_DOMAIN_INTEGER_RING INT_ABS_BOUNDS INT_POW2_ABS INT_POW_ONE
   INT_PRIMITIVE_UNIMODULAR_COLUMN IN_ELIM_THM IN_INSERT IN_SING IN_UNIV
   LE_EXISTS MEMBER_NOT_EMPTY MONO_EXISTS NOT_EXISTS_THM NOT_INSERT_EMPTY
   NOT_IN_EMPTY QUADRATIC_FORM_BASIS_VECTOR QUADRATIC_FORM_CHANGE_BASIS
   QUADRATIC_FORM_COMPLETE_SQUARE QUADRATIC_FORM_CONGRUENT_POSITIVE
   QUADRATIC_FORM_MINIMAL_PRIMITIVE QUADRATIC_FORM_POS_LE
   QUADRATIC_FORM_SCHUR_POSITIVE REAL_ARCH_SIMPLE REAL_DET_CONGRUENT_MATRIX
   REAL_DET_SCHUR_COMPLEMENT REAL_EQ_IMP_LE REAL_LE_LMUL REAL_LE_MAX REAL_LE_MUL
   REAL_LE_MUL2 REAL_LE_POW_2 REAL_LE_RDIV_EQ REAL_LE_REFL REAL_LE_RMUL
   REAL_LE_SQUARE_ABS REAL_LE_TOTAL REAL_LE_TRANS REAL_LT_01 REAL_LT_IMP_LE
   REAL_LT_IMP_NZ REAL_LT_MUL REAL_MUL_ASSOC REAL_MUL_LID REAL_MUL_RID
   REAL_OF_INT_OF_REAL REAL_POW2_ABS REAL_POW_2 REAL_POW_ADD REAL_POW_LE2
   REAL_POW_LT REAL_POW_MUL REAL_POW_ONE REAL_RING_CLAUSES REAL_RING_OF_INT
   RING_DET_DEPENDENT_COLUMNS RING_DET_EMPTY RING_DET_HOMOMORPHISM RING_DET_SING
   RING_HOMOMORPHISM_INTEGER_RING_OF_INT SUBSET SUC_SUB1 SUM_EQ int_abs_th
   int_eq int_isum int_le int_mul_th int_of_num_th int_pow_th real_div real_pow : thm)
  deriving Inhabited

/-- What hermite_inequality.ml uses from Session besides theorems. -/
structure HermiteInequalityDeps where
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
  NUM_RING : ioconv
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
/- hermite_inequality.ml phrases from line 58 to 291                      -/
/- ---------------------------------------------------------------------- -/

structure HermiteInequality where
  -- @@FIELDS
  QUADRATIC_FORM_DET_POS : thm
  QUADRATIC_FORM_FINITE_INTEGER_POINTS : thm
  QUADRATIC_FORM_MINIMAL_VECTOR : thm
  HERMITE_INEQUALITY : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupHermiteInequality [HolBase] (D : HermiteInequalityDeps) :
    ExceptT String IO HermiteInequality := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, INT_ARITH_TAC,
        INT_REDUCE_CONV, MESON, MESON_TAC, NUM_REDUCE_CONV, NUM_RING, REAL_ARITH,
        REAL_ARITH_TAC, REAL_RAT_REDUCE_CONV, SET_TAC, TAUT, .. } := D
  let { ADD1, CARD_CLAUSES, CARD_EQ_0, EXISTS_IN_IMAGE, FINITE_IMAGE,
        FINITE_INDUCT_STRONG, FINITE_INSERT, FINITE_INT_SEG, FINITE_PRODUCT_DEPENDENT,
        FINITE_SING, FINITE_SUBSET, FORALL_IN_IMAGE, FUN_EQ_THM, IMAGE_EQ_EMPTY,
        IMP_CONJ, INF_FINITE_LEMMA, INTEGER_RING, INTEGER_RING_SUM, INTEGER_ROUND,
        INTEGRAL_DOMAIN_INTEGER_RING, INT_ABS_BOUNDS, INT_POW2_ABS, INT_POW_ONE,
        INT_PRIMITIVE_UNIMODULAR_COLUMN, IN_ELIM_THM, IN_INSERT, IN_SING, IN_UNIV,
        LE_EXISTS, MEMBER_NOT_EMPTY, MONO_EXISTS, NOT_EXISTS_THM, NOT_INSERT_EMPTY,
        NOT_IN_EMPTY, QUADRATIC_FORM_BASIS_VECTOR, QUADRATIC_FORM_CHANGE_BASIS,
        QUADRATIC_FORM_COMPLETE_SQUARE, QUADRATIC_FORM_CONGRUENT_POSITIVE,
        QUADRATIC_FORM_MINIMAL_PRIMITIVE, QUADRATIC_FORM_POS_LE,
        QUADRATIC_FORM_SCHUR_POSITIVE, REAL_ARCH_SIMPLE, REAL_DET_CONGRUENT_MATRIX,
        REAL_DET_SCHUR_COMPLEMENT, REAL_EQ_IMP_LE, REAL_LE_LMUL, REAL_LE_MAX,
        REAL_LE_MUL, REAL_LE_MUL2, REAL_LE_POW_2, REAL_LE_RDIV_EQ, REAL_LE_REFL,
        REAL_LE_RMUL, REAL_LE_SQUARE_ABS, REAL_LE_TOTAL, REAL_LE_TRANS, REAL_LT_01,
        REAL_LT_IMP_LE, REAL_LT_IMP_NZ, REAL_LT_MUL, REAL_MUL_ASSOC, REAL_MUL_LID,
        REAL_MUL_RID, REAL_OF_INT_OF_REAL, REAL_POW2_ABS, REAL_POW_2, REAL_POW_ADD,
        REAL_POW_LE2, REAL_POW_LT, REAL_POW_MUL, REAL_POW_ONE, REAL_RING_CLAUSES,
        REAL_RING_OF_INT, RING_DET_DEPENDENT_COLUMNS, RING_DET_EMPTY,
        RING_DET_HOMOMORPHISM, RING_DET_SING, RING_HOMOMORPHISM_INTEGER_RING_OF_INT,
        SUBSET, SUC_SUB1, SUM_EQ, int_abs_th, int_eq, int_isum, int_le, int_mul_th,
        int_of_num_th, int_pow_th, real_div, real_pow, .. } := D.core1
  -- @@SCOPE END

  let QUADRATIC_FORM_DET_POS ← prove
    r"!s (A:K->K->real).
        FINITE s /\ (!i j. i IN s /\ j IN s ==> A i j = A j i) /\
        (!x. (?i. i IN s /\ ~(x i = &0))
             ==> &0 < sum s (\i. sum s (\j. A i j * x i * x j)))
        ==> &0 < ring_det real_ring s A"
    (SUBGOAL_THEN (← q r"!s. FINITE s
        ==> !A:K->K->real.
              (!i j. i IN s /\ j IN s ==> A i j = A j i) /\
              (!x. (?i. i IN s /\ ~(x i = &0))
                   ==> &0 < sum s (\i. sum s (\j. A i j * x i * x j)))
              ==> &0 < ring_det real_ring s A") (fun th => tactic_of do pure (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC (← MP (← SPEC (← q r"s:K->bool") th) (← ASSUME (← q r"FINITE(s:K->bool)"))) THEN ASM_REWRITE_TAC [])) THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC [RING_DET_EMPTY, REAL_RING_CLAUSES, REAL_LT_01] THEN MAP_EVERY X_GEN_TAC [(← q r"a:K"), (← q r"t:K->bool")] THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN X_GEN_TAC (← q r"A:K->K->real") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"a:K"), (← q r"t:K->bool"), (← q r"A:K->K->real")] QUADRATIC_FORM_SCHUR_POSITIVE) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"a:K"), (← q r"t:K->bool"), (← q r"A:K->K->real")] REAL_DET_SCHUR_COMPLEMENT) THEN ASM_SIMP_TAC [REAL_LT_IMP_NZ] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC [] THEN REMOVE_THEN "ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC [])

  let QUADRATIC_FORM_FINITE_INTEGER_POINTS ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let v1 ← GSYM INT_ABS_BOUNDS
    let q2 ← q r"{u:int | --(&N) <= u /\ u <= &N}"
    let q3 ← q r"N:num"
    let q4 ← q r"b:real"
    let v5 ← SPEC q4 REAL_ARCH_SIMPLE
    let p6 ← prove r"!b. FINITE {u:int | abs(real_of_int u) <= b}" (GEN_TAC THEN MP_TAC v5 THEN DISCH_THEN (X_CHOOSE_TAC q3) THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC q2 THEN REWRITE_TAC [FINITE_INT_SEG, SUBSET, IN_ELIM_THM, v1] THEN REWRITE_TAC [int_le, int_abs_th, int_of_num_th] THEN ASM_MESON_TAC [REAL_LE_TRANS])
    let lemma := p6
    let q7 ← q r"i:K"
    let q14 ← q r"real_of_int((x:K->int) a) + c / A a a = z"
    let v15 ← GSYM REAL_MUL_RID
    let q16 ← q r"abs(z:real) <= &1"
    let v17 ← GSYM REAL_POW2_ABS
    let q18 ← q r"abs(z:real) <= max (&1) (z pow 2)"
    let q25 ← q r"z pow 2 <= C / (A:K->K->real) a a"
    let q26 ← q r"z = real_of_int((x:K->int) a) + c / A a a"
    let q27 ← q r"&0 <= u ==> u + q <= C ==> q <= C:real"
    let r28 ← REAL_ARITH q27
    let q35 ← q r"q:real"
    let q36 ← q r"q = sum t (\i. sum t (\j. ((A:K->K->real) i j - A i a * A a j / A a a) *
                              real_of_int((x:K->int) i) *
                              real_of_int(x j)))"
    let q37 ← q r"c = sum t
              (\j. (A:K->K->real) a j * real_of_int((x:K->int) j))"
    let q38 ← q r"\i. real_of_int((x:K->int) i)"
    let q39 ← q r"\i j. (A:K->K->real) i j - A i a * A a j / A a a"
    let q40 ← q r"t:K->bool"
    let v41 ← ISPECL [q40, q39, q38] QUADRATIC_FORM_POS_LE
    let q42 ← q r"sum t (\j. (A:K->K->real) a j *
               real_of_int(if j IN t then (x:K->int) j else &0)) =
    sum t (\j. A a j * real_of_int(x j)) /\
    sum t (\i. sum t (\j. (A i j - A i a * A a j / A a a) *
                          real_of_int(if i IN t then (x:K->int) i else &0) *
                          real_of_int(if j IN t then x j else &0))) =
    sum t (\i. sum t (\j. (A i j - A i a * A a j / A a a) *
                          real_of_int(x i) * real_of_int(x j)))"
    let q43 ← q r"!j. j IN t
        ==> real_of_int((if j IN t then (x:K->int) j else &0)) =
            real_of_int(x j)"
    let q44 ← q r"\i. real_of_int((x:K->int) i)"
    let q45 ← q r"A:K->K->real"
    let q46 ← q r"t:K->bool"
    let q47 ← q r"a:K"
    let v48 ← ISPECL [q47, q46, q45, q44] QUADRATIC_FORM_COMPLETE_SQUARE
    let v49 ← BETA_RULE v48
    let q50 ← q r"(x:K->int) a"
    let q51 ← q r"\i. if i IN t then (x:K->int) i else &0"
    let q52 ← q r"x:K->int"
    let q53 ← q r"{(\y u i. if i = a then u else (y:K->int) i) y u | y,u |
     y IN Y /\
     u IN (\y. {u:int | abs(real_of_int u) <=
                        abs(sum t (\j. (A:K->K->real) a j * real_of_int(y j)) /
                            A a a) + max (&1) (C / A a a)}) y}"
    let q54 ← q r"Y = {y:K->int | (!i. ~(i IN t) ==> y i = &0) /\
                    sum t (\i. sum t (\j. ((A:K->K->real) i j -
                                            A i a * A a j / A a a) *
                                          real_of_int(y i) *
                                          real_of_int(y j))) <= C}"
    let q55 ← q r"C:real"
    let q56 ← q r"\i j. (A:K->K->real) i j - A i a * A a j / A a a"
    let q57 ← q r"A:K->K->real"
    let q58 ← q r"t:K->bool"
    let q59 ← q r"a:K"
    let v60 ← ISPECL [q59, q58, q57] QUADRATIC_FORM_SCHUR_POSITIVE
    let q61 ← q r"C:real"
    let q62 ← q r"A:K->K->real"
    let q63 ← q r"t:K->bool"
    let q64 ← q r"a:K"
    let q65 ← q r"{(\i. &0):K->int}"
    let q66 ← q r"!s. FINITE s
        ==> !(A:K->K->real) C.
              (!i j. i IN s /\ j IN s ==> A i j = A j i) /\
              (!x. (?i. i IN s /\ ~(x i = &0))
                   ==> &0 < sum s (\i. sum s (\j. A i j * x i * x j)))
              ==> FINITE
                   {x:K->int | (!i. ~(i IN s) ==> x i = &0) /\
                               sum s (\i. sum s (\j. A i j * real_of_int(x i) *
                                                    real_of_int(x j))) <= C}"
    prove
      r"!s (A:K->K->real) C.
          FINITE s /\ (!i j. i IN s /\ j IN s ==> A i j = A j i) /\
          (!x. (?i. i IN s /\ ~(x i = &0))
               ==> &0 < sum s (\i. sum s (\j. A i j * x i * x j)))
          ==> FINITE {x:K->int | (!i. ~(i IN s) ==> x i = &0) /\
                                 sum s (\i. sum s (\j. A i j * real_of_int(x i) *
                                                      real_of_int(x j))) <= C}"
      (SUBGOAL_THEN q66 (fun th => tactic_of do pure (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC (← MP (← SPEC (← q r"s:K->bool") th) (← ASSUME (← q r"FINITE(s:K->bool)"))) THEN ASM_REWRITE_TAC [])) THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC q65 THEN REWRITE_TAC [FINITE_SING, SUBSET, IN_ELIM_THM, IN_SING, NOT_IN_EMPTY] THEN REWRITE_TAC [FUN_EQ_THM] THEN MESON_TAC [], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [q64, q63] THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN MAP_EVERY X_GEN_TAC [q62, q61] THEN STRIP_TAC THEN MP_TAC v60 THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN REMOVE_THEN "ih" (MP_TAC o (SPEC q56)) THEN DISCH_THEN (MP_TAC o (SPEC q55)) THEN REWRITE_TAC [] THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC q54 THEN DISCH_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC q53 THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC [lemma], ALL_TAC] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC q52 THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC [q51, q50] THEN REWRITE_TAC [] THEN MP_TAC v49 THEN ANTS_TAC THENL [ASM_SIMP_TAC [REAL_LT_IMP_NZ] THEN ASM_MESON_TAC [IN_INSERT], DISCH_THEN (fun th => RULE_ASSUM_TAC (REWRITE_RULE [th]))] THEN SUBGOAL_THEN q43 ASSUME_TAC THENL [SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN q42 (CONJUNCTS_THEN SUBST1_TAC) THENL [CONJ_TAC THEN MATCH_MP_TAC SUM_EQ THEN SIMP_TAC [] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN SIMP_TAC [], ALL_TAC] THEN MP_TAC v41 THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ABBREV_TAC q37 THEN ABBREV_TAC q36 THEN REPEAT CONJ_TAC THENL [EXPAND_TAC "Y" THEN REWRITE_TAC [IN_ELIM_THM] THEN CONJ_TAC THENL [MESON_TAC [], ALL_TAC] THEN TRANS_TAC REAL_LE_TRANS q35 THEN CONJ_TAC THENL [EXPAND_TAC "q" THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN SIMP_TAC [] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN SIMP_TAC [], FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do if ← (do let z30 ← (do let z31 ← (pure th); pure (concl z31)); let z29 ← (q r"C:real"); pure (free_in z29 z30)) then (do let z33 ← (do let z34 ← (pure th); pure (concl z34)); let z32 ← (q r"q:real"); pure (free_in z32 z33)) else pure false)))) THEN MATCH_MP_TAC r28 THEN ASM_SIMP_TAC [REAL_LE_MUL, REAL_LT_IMP_LE, REAL_LE_POW_2]], ABBREV_TAC q26 THEN SUBGOAL_THEN q25 ASSUME_TAC THENL [ASM_SIMP_TAC [REAL_LE_RDIV_EQ] THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do if ← (do let z20 ← (do let z21 ← (pure th); pure (concl z21)); let z19 ← (q r"z:real"); pure (free_in z19 z20)) then (do let z23 ← (do let z24 ← (pure th); pure (concl z24)); let z22 ← (q r"C:real"); pure (free_in z22 z23)) else pure false)))) THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN q18 MP_TAC THENL [ONCE_REWRITE_TAC [v17] THEN ASM_CASES_TAC q16 THEN ASM_REWRITE_TAC [REAL_LE_MAX] THEN REWRITE_TAC [REAL_POW_2] THEN GEN_REWRITE_TAC LAND_CONV [v15] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN UNDISCH_TAC q14 THEN POP_ASSUM_LIST (MP_TAC o ((HolLight.end_itlist CONJ) o (filterM (fun th => (do if ← (do let z9 ← (do let z10 ← (pure th); pure (concl z10)); let z8 ← (q r"z:real"); pure (free_in z8 z9)) then (do pure !(← (do let z12 ← (do let z13 ← (pure th); pure (concl z13)); let z11 ← (q r"x:K->int"); pure (free_in z11 z12)))) else pure false))))) THEN REWRITE_TAC [REAL_LE_MAX] THEN REAL_ARITH_TAC, REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC q7 THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [IN_INSERT]])

  let QUADRATIC_FORM_MINIMAL_VECTOR ← prove
    r"!s (A:K->K->real).
        FINITE s /\ ~(s = {}) /\ (!i j. i IN s /\ j IN s ==> A i j = A j i) /\
        (!x. (?i. i IN s /\ ~(x i = &0))
             ==> &0 < sum s (\i. sum s (\j. A i j * x i * x j)))
        ==> ?x:K->int.
              (!i. ~(i IN s) ==> x i = &0) /\ (?i. i IN s /\ ~(x i = &0)) /\
              !y:K->int.
                (!i. ~(i IN s) ==> y i = &0) /\ (?i. i IN s /\ ~(y i = &0))
                ==> sum s (\i. sum s (\j. A i j * real_of_int(x i) *
                                         real_of_int(x j))) <=
                    sum s (\i. sum s (\j. A i j * real_of_int(y i) *
                                         real_of_int(y j)))"
    (REPEAT STRIP_TAC THEN FIRST_X_ASSUM ((X_CHOOSE_TAC (← q r"a:K")) o (GEN_REWRITE_RULE id [(← GSYM MEMBER_NOT_EMPTY)])) THEN MP_TAC (← ISPECL [(← q r"s:K->bool"), (← q r"A:K->K->real"), (← q r"sum s (\i. sum s (\j. (A:K->K->real) i j *
       real_of_int(if i = a then &1 else &0) *
       real_of_int(if j = a then &1 else &0)))")] QUADRATIC_FORM_FINITE_INTEGER_POINTS) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPEC (← q r"IMAGE (\x:K->int. sum s (\i. sum s (\j. (A:K->K->real) i j *
                       real_of_int(x i) * real_of_int(x j))))
          {x:K->int | ((!i. ~(i IN s) ==> x i = &0) /\
                       (?i. i IN s /\ ~(x i = &0))) /\
                      sum s (\i. sum s (\j. A i j * real_of_int(x i) *
                                            real_of_int(x j))) <=
                      sum s (\i. sum s (\j. A i j *
                         real_of_int(if i = a then &1 else &0) *
                         real_of_int(if j = a then &1 else &0)))}") INF_FINITE_LEMMA) THEN ANTS_TAC THENL [CONJ_TAC THENL [MATCH_MP_TAC FINITE_IMAGE THEN FIRST_X_ASSUM (MATCH_MP_TAC o (MATCH_MP (← REWRITE_RULE [IMP_CONJ] FINITE_SUBSET))) THEN SET_TAC [], REWRITE_TAC [IMAGE_EQ_EMPTY] THEN REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY), IN_ELIM_THM] THEN EXISTS_TAC (← q r"\i:K. if i = a then &1:int else &0") THEN REWRITE_TAC [REAL_LE_REFL] THEN CONJ_TAC THENL [ASM_MESON_TAC [], EXISTS_TAC (← q r"a:K") THEN ASM_REWRITE_TAC [] THEN CONV_TAC INT_REDUCE_CONV]], ALL_TAC] THEN REWRITE_TAC [EXISTS_IN_IMAGE, FORALL_IN_IMAGE, IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"x:K->int") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN X_GEN_TAC (← q r"y:K->int") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"y:K->int"))) THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [REAL_LE_TOTAL, REAL_LE_TRANS])

  let HERMITE_INEQUALITY ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"((a:real) * c * S pow 2) * m pow 2"
    let q2 ← q r"(u:real) = a * (b * u)"
    let q3 ← q r"(u:real) <= a * c * S pow 2"
    let q4 ← q r"v:real"
    let q5 ← q r"(q:real) pow (2 * p)"
    let q6 ← q r"u:real"
    let q7 ← q r"(m:real) pow (2 * p)"
    let q8 ← q r"c:real"
    let q9 ← q r"(&4 / &3) pow (p * (p - 1))"
    let q10 ← q r"b:real"
    let q11 ← q r"(&3 / &4) pow (2 * p)"
    let q12 ← q r"a:real"
    let q13 ← q r"(&4 / &3) pow (2 * p)"
    let q17 ← q r"&0 < (m:real) pow 2 /\ &0 < (&4 / &3:real) pow (2 * p)"
    let v18 ← GSYM REAL_POW_MUL
    let q19 ← q r"(&4 / &3) pow (2 * p) * (&3 / &4) pow (2 * p) = &1"
    let q20 ← q r"(&3 / &4 * m) pow (2 * p) <= q pow (2 * p)"
    let q21 ← q r"(1 + d) - 1 = d:num"
    let r22 ← ARITH_RULE q21
    let q23 ← q r"d:num"
    let q24 ← q r"2 * (p + 1) = 2 * p + 2 /\ (p + 1) * p = 2 * p + p * (p - 1)"
    let p25 ← prove r"!m q D S p.
          &0 < m /\ &3 / &4 * m <= q /\
          q pow (2 * p) <= (&4 / &3) pow (p * (p - 1)) * S pow 2 /\
          D = m * S /\ 1 <= p
          ==> m pow (2 * (p + 1)) <= (&4 / &3) pow ((p + 1) * p) * D pow 2" (REPEAT STRIP_TAC THEN SUBGOAL_THEN q24 (CONJUNCTS_THEN SUBST1_TAC) THENL [CONJ_TAC THENL [ARITH_TAC, ALL_TAC] THEN FIRST_X_ASSUM ((X_CHOOSE_THEN q23 SUBST1_TAC) o (GEN_REWRITE_RULE id [LE_EXISTS])) THEN REWRITE_TAC [r22] THEN CONV_TAC NUM_RING, ALL_TAC] THEN ASM_REWRITE_TAC [REAL_POW_ADD, REAL_POW_MUL] THEN SUBGOAL_THEN q20 MP_TAC THENL [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [REAL_POW_MUL] THEN SUBGOAL_THEN q19 ASSUME_TAC THENL [REWRITE_TAC [v18] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC [REAL_POW_ONE], ALL_TAC] THEN SUBGOAL_THEN q17 STRIP_ASSUME_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do let z15 ← (do let z16 ← (pure th); pure (concl z16)); let z14 ← (q r"S:real"); pure (free_in z14 z15))))) THEN POP_ASSUM_LIST (MP_TAC o (HolLight.end_itlist CONJ)) THEN SPEC_TAC (q13, q12) THEN SPEC_TAC (q11, q10) THEN SPEC_TAC (q9, q8) THEN SPEC_TAC (q7, q6) THEN SPEC_TAC (q5, q4) THEN REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT DISCH_TAC THEN SUBGOAL_THEN q3 ASSUME_TAC THENL [SUBGOAL_THEN q2 SUBST1_TAC THENL [ASM_REWRITE_TAC [REAL_MUL_ASSOC, REAL_MUL_LID], ALL_TAC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN TRANS_TAC REAL_LE_TRANS q1 THEN CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC [REAL_LT_IMP_LE], MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC])
    let step := p25
    let q26 ← q r"int_of_real m"
    let q27 ← q r"m:real"
    let q28 ← q r"--c:real"
    let v29 ← SPEC q28 INTEGER_ROUND
    let p30 ← prove r"!c. ?n:int. abs(real_of_int n + c) <= &1 / &2" (GEN_TAC THEN MP_TAC v29 THEN DISCH_THEN (X_CHOOSE_THEN q27 STRIP_ASSUME_TAC) THEN EXISTS_TAC q26 THEN ASM_SIMP_TAC [REAL_OF_INT_OF_REAL] THEN ASM_REAL_ARITH_TAC)
    let round := p30
    let q31 ← q r"1 <= n <=> ~(n = 0)"
    let r32 ← ARITH_RULE q31
    let q33 ← q r"ring_det real_ring t (\i j. (B:K->K->real) i j - B i a * B a j / m)"
    let q34 ← q r"q:real"
    let v35 ← GSYM real_div
    let v36 ← GSYM REAL_MUL_ASSOC
    let q37 ← q r"m * (real_of_int n + c) pow 2 <= m * &1 / &4"
    let q38 ← q r"abs(&1 / &2) = &1 / &2"
    let r39 ← REAL_ARITH q38
    let q40 ← q r"&1 / &2"
    let q41 ← q r"real_of_int n + c"
    let v42 ← SPECL [q41, q40] REAL_LE_SQUARE_ABS
    let q43 ← q r"(real_of_int n + c) pow 2 <= &1 / &4"
    let q44 ← q r"q = sum t (\i. sum t (\j. ((B:K->K->real) i j - B i a * B a j / m) *
                              real_of_int((z:K->int) i) *
                              real_of_int(z j)))"
    let q45 ← q r"c = sum t (\j. (B:K->K->real) a j * real_of_int((z:K->int) j))
                  / m"
    let q46 ← q r"sum t (\j. (B:K->K->real) a j *
               real_of_int(if j = a then n else (z:K->int) j)) =
    sum t (\j. B a j * real_of_int(z j)) /\
    sum t (\i. sum t (\j. (B i j - B i a * B a j / m) *
                          real_of_int(if i = a then n else (z:K->int) i) *
                          real_of_int(if j = a then n else z j))) =
    sum t (\i. sum t (\j. (B i j - B i a * B a j / m) *
                          real_of_int(z i) * real_of_int(z j)))"
    let q47 ← q r"!j. j IN t ==> (if j = a then n else (z:K->int) j) = z j"
    let q48 ← q r"\i. real_of_int(if i = a then n else (z:K->int) i)"
    let q49 ← q r"B:K->K->real"
    let q50 ← q r"t:K->bool"
    let q51 ← q r"a:K"
    let v52 ← ISPECL [q51, q50, q49, q48] QUADRATIC_FORM_COMPLETE_SQUARE
    let v53 ← BETA_RULE v52
    let q54 ← q r"i:K"
    let q63 ← q r"\i. if i = a then n else (z:K->int) i"
    let q64 ← q r"n:int"
    let q65 ← q r"sum t (\j. (B:K->K->real) a j * real_of_int((z:K->int) j)) / m"
    let v66 ← SPEC q65 round
    let q67 ← q r"B:K->K->real"
    let q68 ← q r"t:K->bool"
    let q69 ← q r"a:K"
    let v70 ← ISPECL [q69, q68, q67] REAL_DET_SCHUR_COMPLEMENT
    let q71 ← q r"z:K->int"
    let q72 ← q r"\i j. (B:K->K->real) i j - B i a * B a j / B a a"
    let q73 ← q r"B:K->K->real"
    let q74 ← q r"t:K->bool"
    let q75 ← q r"a:K"
    let v76 ← ISPECL [q75, q74, q73] QUADRATIC_FORM_SCHUR_POSITIVE
    let q77 ← q r"(!i j. i IN a INSERT t /\ j IN a INSERT t
           ==> (B:K->K->real) i j = B j i) /\
    (!y. (?i. i IN a INSERT t /\ ~(y i = &0))
         ==> &0 < sum (a INSERT t) (\i. sum (a INSERT t)
                    (\j. B i j * y i * y j)))"
    let q78 ← q r"l:K"
    let q79 ← q r"k:K"
    let q80 ← q r"(x:real) = y ==> m <= x ==> m <= y"
    let r81 ← REAL_ARITH q80
    let q82 ← q r"abs(ring_det integer_ring (a INSERT t) (U:K->K->int)) =
                     &1"
    let q88 ← q r"k:K"
    let q89 ← q r"k:K"
    let q90 ← q r"p /\ ~q ==> ~(p ==> q)"
    let r91 ← TAUT q90
    let q92 ← q r"y:K->int"
    let q93 ← q r"U:K->K->int"
    let q94 ← q r"(a:K) INSERT t"
    let q95 ← q r"integer_ring"
    let v96 ← ISPECL [q95, q94, q93, q92] RING_DET_DEPENDENT_COLUMNS
    let q97 ← q r"~(p /\ ~q) <=> p ==> q"
    let r98 ← TAUT q97
    let q99 ← q r"(~p ==> F) ==> p"
    let r100 ← TAUT q99
    let q101 ← q r"p /\ (q ==> r) ==> (p ==> q) ==> r"
    let r102 ← TAUT q101
    let q103 ← q r"\k. if k IN a INSERT t
          then isum (a INSERT t) (\i. (U:K->K->int) k i * y i) else &0"
    let q104 ← q r"\i. real_of_int((y:K->int) i)"
    let q105 ← q r"\k i. real_of_int((U:K->K->int) k i)"
    let q106 ← q r"A:K->K->real"
    let q107 ← q r"(a:K) INSERT t"
    let v108 ← ISPECL [q107, q106, q105, q104] QUADRATIC_FORM_CHANGE_BASIS
    let v109 ← BETA_RULE v108
    let q110 ← q r"y:K->int"
    let q111 ← q r"!y:K->int.
      (!i. ~(i IN a INSERT t) ==> y i = &0) /\
      (?i. i IN a INSERT t /\ ~(y i = &0))
      ==> m <= sum (a INSERT t) (\i. sum (a INSERT t) (\j.
                 (B:K->K->real) i j * real_of_int(y i) * real_of_int(y j)))"
    let q112 ← q r"(U:K->K->int) k a = x k /\ U l a = x l"
    let q113 ← q r"l:K"
    let q114 ← q r"k:K"
    let q115 ← q r"(B:K->K->real) a a = m"
    let q116 ← q r"B = \i j. sum (a INSERT t) (\k. sum (a INSERT t) (\l.
                real_of_int((U:K->K->int) k i) * (A:K->K->real) k l *
                real_of_int(U l j)))"
    let q117 ← q r"\k i. real_of_int((U:K->K->int) k i)"
    let q118 ← q r"A:K->K->real"
    let q119 ← q r"(a:K) INSERT t"
    let v120 ← ISPECL [q119, q118, q117] REAL_DET_CONGRUENT_MATRIX
    let q121 ← q r"ring_det real_ring (a INSERT t) (\k i. real_of_int((U:K->K->int) k i))
      pow 2 = &1"
    let q122 ← q r"\k i. real_of_int((U:K->K->int) k i)"
    let q123 ← q r"A:K->K->real"
    let q124 ← q r"(a:K) INSERT t"
    let v125 ← ISPECL [q124, q123, q122] QUADRATIC_FORM_CONGRUENT_POSITIVE
    let v126 ← GSYM INT_POW2_ABS
    let v127 ← GSYM int_eq
    let v128 ← GSYM int_of_num_th
    let v129 ← GSYM int_pow_th
    let q130 ← q r"U:K->K->int"
    let q131 ← q r"(a:K) INSERT t"
    let q132 ← q r"ring_of_int real_ring"
    let q133 ← q r"real_ring"
    let q134 ← q r"integer_ring"
    let v135 ← ISPECL [q134, q133, q132, q131, q130] RING_DET_HOMOMORPHISM
    let q136 ← q r"ring_det real_ring (a INSERT t) (\k i. real_of_int((U:K->K->int) k i))
    pow 2 = &1"
    let q137 ← q r"U:K->K->int"
    let q138 ← q r"a:K"
    let q139 ← q r"x:K->int"
    let q140 ← q r"(a:K) INSERT t"
    let v141 ← ISPECL [q140, q139, q138] INT_PRIMITIVE_UNIMODULAR_COLUMN
    let q142 ← q r"x:K->int"
    let q143 ← q r"A:K->K->real"
    let q144 ← q r"(a:K) INSERT t"
    let v145 ← ISPECL [q144, q143, q142] QUADRATIC_FORM_MINIMAL_PRIMITIVE
    let q146 ← q r"t:K->bool = {}"
    let q147 ← q r"!p. real_of_int(if p then &1 else &0) = if p then &1 else &0"
    let r148 ← MESON [int_of_num_th] q147
    let q149 ← q r"a:K"
    let q150 ← q r"\i:K. if i = a then &1:int else &0"
    let q151 ← q r"m <= sum (a INSERT t) (\i. sum (a INSERT t) (\j. (A:K->K->real) i j *
          real_of_int(if i = a then &1 else &0) *
          real_of_int(if j = a then &1 else &0)))"
    let v152 ← GSYM int_eq
    let v153 ← GSYM int_of_num_th
    let q154 ← q r"i:K"
    let q158 ← q r"i:K"
    let q167 ← q r"&0 < (m:real)"
    let q168 ← q r"m = sum (a INSERT t) (\i. sum (a INSERT t) (\j. (A:K->K->real) i j *
          real_of_int((x:K->int) i) * real_of_int(x j)))"
    let q169 ← q r"x:K->int"
    let q170 ← q r"x:K->int"
    let q171 ← q r"A:K->K->real"
    let q172 ← q r"(a:K) INSERT t"
    let v173 ← ISPECL [q172, q171] QUADRATIC_FORM_MINIMAL_VECTOR
    let q174 ← q r"A:K->K->real"
    let q175 ← q r"t:K->bool"
    let q176 ← q r"a:K"
    let q177 ← q r"!s. FINITE s
        ==> !A:K->K->real.
              ~(s = {}) /\ (!i j. i IN s /\ j IN s ==> A i j = A j i) /\
              (!x. (?i. i IN s /\ ~(x i = &0))
                   ==> &0 < sum s (\i. sum s (\j. A i j * x i * x j)))
              ==> ?x:K->int.
                    (!i. ~(i IN s) ==> x i = &0) /\
                    (?i. i IN s /\ ~(x i = &0)) /\
                    sum s (\i. sum s (\j. A i j * real_of_int(x i) *
                                         real_of_int(x j))) pow (2 * CARD s) <=
                    (&4 / &3) pow (CARD s * (CARD s - 1)) *
                    ring_det real_ring s A pow 2"
    prove
      r"!s (A:K->K->real).
          FINITE s /\ ~(s = {}) /\
          (!i j. i IN s /\ j IN s ==> A i j = A j i) /\
          (!x. (?i. i IN s /\ ~(x i = &0))
               ==> &0 < sum s (\i. sum s (\j. A i j * x i * x j)))
          ==> ?x:K->int.
                (!i. ~(i IN s) ==> x i = &0) /\ (?i. i IN s /\ ~(x i = &0)) /\
                sum s (\i. sum s (\j. A i j * real_of_int(x i) *
                                     real_of_int(x j))) pow (2 * CARD s) <=
                (&4 / &3) pow (CARD s * (CARD s - 1)) *
                ring_det real_ring s A pow 2"
      (SUBGOAL_THEN q177 (fun th => tactic_of do pure (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC (← MP (← SPEC (← q r"s:K->bool") th) (← ASSUME (← q r"FINITE(s:K->bool)"))) THEN ASM_REWRITE_TAC [])) THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC [] THEN MAP_EVERY X_GEN_TAC [q176, q175] THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN X_GEN_TAC q174 THEN STRIP_TAC THEN MP_TAC v173 THEN ASM_REWRITE_TAC [FINITE_INSERT, NOT_INSERT_EMPTY] THEN DISCH_THEN (X_CHOOSE_THEN q170 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "min")))) THEN EXISTS_TAC q169 THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC q168 THEN SUBGOAL_THEN q167 ASSUME_TAC THENL [EXPAND_TAC "m" THEN FIRST_X_ASSUM (MATCH_MP_TAC o (checkM (fun th => (do if ← (do if ← (do let z159 ← (do let z160 ← (pure th); pure (concl z160)); pure (is_forall z159)) then (do let z162 ← (do let z163 ← (pure th); pure (concl z163)); let z161 ← (q r"A:K->K->real"); pure (free_in z161 z162)) else pure false) then (do let z164 ← (do pure (Prod.snd (← (do let z165 ← (do let z166 ← (pure th); pure (concl z166)); liftExcept (dest_forall z165))))); pure (is_imp z164)) else pure false)))) THEN FIRST_X_ASSUM ((X_CHOOSE_THEN q158 STRIP_ASSUME_TAC) o (checkM (fun z155 => (do let z156 ← (do let z157 ← (pure z155); pure (concl z157)); pure (is_exists z156))))) THEN EXISTS_TAC q154 THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [v153, v152] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN q151 MP_TAC THENL [USE_THEN "min" (MP_TAC o (SPEC q150)) THEN REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC [IN_INSERT], ALL_TAC] THEN EXISTS_TAC q149 THEN REWRITE_TAC [IN_INSERT] THEN CONV_TAC INT_REDUCE_CONV, ALL_TAC] THEN REWRITE_TAC [r148] THEN ASM_SIMP_TAC [QUADRATIC_FORM_BASIS_VECTOR, FINITE_INSERT, IN_INSERT] THEN DISCH_TAC THEN ASM_SIMP_TAC [CARD_CLAUSES, SUC_SUB1] THEN ASM_CASES_TAC q146 THENL [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC [CARD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [real_pow, REAL_MUL_LID] THEN SIMP_TAC [RING_DET_SING, REAL_RING_CLAUSES, IN_UNIV] THEN REWRITE_TAC [REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN MP_TAC v145 THEN ASM_REWRITE_TAC [FINITE_INSERT] THEN DISCH_TAC THEN MP_TAC v141 THEN ASM_REWRITE_TAC [FINITE_INSERT, IN_INSERT] THEN DISCH_THEN (X_CHOOSE_THEN q137 STRIP_ASSUME_TAC) THEN SUBGOAL_THEN q136 ASSUME_TAC THENL [MP_TAC v135 THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, FINITE_INSERT, INTEGER_RING, IN_UNIV, REAL_RING_OF_INT] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [v129, v128, v127] THEN ONCE_REWRITE_TAC [v126] THEN ASM_REWRITE_TAC [INT_POW_ONE], ALL_TAC] THEN MP_TAC v125 THEN ASM_REWRITE_TAC [FINITE_INSERT] THEN ANTS_TAC THENL [DISCH_TAC THEN UNDISCH_TAC q121 THEN ASM_REWRITE_TAC [] THEN CONV_TAC REAL_RAT_REDUCE_CONV, REWRITE_TAC [] THEN STRIP_TAC] THEN MP_TAC v120 THEN ASM_REWRITE_TAC [FINITE_INSERT, REAL_MUL_LID] THEN DISCH_TAC THEN ABBREV_TAC q116 THEN SUBGOAL_THEN q115 ASSUME_TAC THENL [EXPAND_TAC "B" THEN EXPAND_TAC "m" THEN REWRITE_TAC [] THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC q114 THEN DISCH_TAC THEN REWRITE_TAC [] THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC q113 THEN DISCH_TAC THEN REWRITE_TAC [] THEN SUBGOAL_THEN q112 (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_MESON_TAC [IN_INSERT], REAL_ARITH_TAC], ALL_TAC] THEN SUBGOAL_THEN q111 ASSUME_TAC THENL [X_GEN_TAC q110 THEN STRIP_TAC THEN EXPAND_TAC "B" THEN MP_TAC v109 THEN ASM_REWRITE_TAC [FINITE_INSERT] THEN DISCH_THEN SUBST1_TAC THEN REMOVE_THEN "min" (MP_TAC o (SPEC q103)) THEN REWRITE_TAC [] THEN MATCH_MP_TAC r102 THEN CONJ_TAC THENL [CONJ_TAC THENL [MESON_TAC [], ALL_TAC] THEN MATCH_MP_TAC r100 THEN DISCH_THEN (ASSUME_TAC o (REWRITE_RULE [NOT_EXISTS_THM, r98])) THEN MP_TAC v96 THEN ASM_REWRITE_TAC [INTEGRAL_DOMAIN_INTEGER_RING, FINITE_INSERT, INTEGER_RING, IN_UNIV, INTEGER_RING_SUM] THEN MATCH_MP_TAC r91 THEN REPEAT CONJ_TAC THENL [ASM_MESON_TAC [], X_GEN_TAC q89 THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC q88) o (checkM (fun th => (do if ← (do let z83 ← (do let z84 ← (pure th); pure (concl z84)); pure (is_forall z83)) then (do let z86 ← (do let z87 ← (pure th); pure (concl z87)); let z85 ← (q r"U:K->K->int"); pure (free_in z85 z86)) else pure false))))) THEN ASM_REWRITE_TAC [], UNDISCH_TAC q82 THEN INT_ARITH_TAC], MATCH_MP_TAC r81 THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC q79 THEN DISCH_TAC THEN REWRITE_TAC [] THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC q78 THEN DISCH_TAC THEN ASM_REWRITE_TAC [int_isum, int_mul_th]], ALL_TAC] THEN SUBGOAL_THEN q77 STRIP_ASSUME_TAC THENL [EXPAND_TAC "B" THEN REWRITE_TAC [] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC v76 THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN REMOVE_THEN "ih" (MP_TAC o (SPEC q72)) THEN REWRITE_TAC [] THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN q71 STRIP_ASSUME_TAC) THEN MP_TAC v70 THEN ASM_SIMP_TAC [REAL_LT_IMP_NZ] THEN DISCH_TAC THEN MP_TAC v66 THEN DISCH_THEN (X_CHOOSE_TAC q64) THEN FIRST_X_ASSUM (MP_TAC o ((SPEC q63) o (checkM (fun th => (do if ← (do if ← (do let z55 ← (do let z56 ← (pure th); pure (concl z56)); pure (is_forall z55)) then (do let z58 ← (do let z59 ← (pure th); pure (concl z59)); let z57 ← (q r"B:K->K->real"); pure (free_in z57 z58)) else pure false) then (do let z61 ← (do let z62 ← (pure th); pure (concl z62)); let z60 ← (q r"m:real"); pure (free_in z60 z61)) else pure false))))) THEN REWRITE_TAC [] THEN ANTS_TAC THENL [CONJ_TAC THENL [ASM_MESON_TAC [IN_INSERT], ALL_TAC] THEN EXISTS_TAC q54 THEN ASM_REWRITE_TAC [IN_INSERT] THEN COND_CASES_TAC THEN ASM_MESON_TAC [], ALL_TAC] THEN MP_TAC v53 THEN ANTS_TAC THENL [ASM_SIMP_TAC [REAL_LT_IMP_NZ] THEN ASM_MESON_TAC [IN_INSERT], DISCH_THEN SUBST1_TAC] THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN q47 ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN q46 (CONJUNCTS_THEN SUBST1_TAC) THENL [CONJ_TAC THEN MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC [] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC [], ALL_TAC] THEN ABBREV_TAC q45 THEN ABBREV_TAC q44 THEN DISCH_TAC THEN SUBGOAL_THEN q43 ASSUME_TAC THENL [MP_TAC v42 THEN ASM_REWRITE_TAC [r39] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN q37 ASSUME_TAC THENL [REWRITE_TAC [real_div, v36] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC [v35] THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [ADD1] THEN MATCH_MP_TAC step THEN MAP_EVERY EXISTS_TAC [q34, q33] THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ASM_SIMP_TAC [r32, CARD_EQ_0]])

  -- @@RETURN BEGIN
  return { QUADRATIC_FORM_DET_POS, QUADRATIC_FORM_FINITE_INTEGER_POINTS,
           QUADRATIC_FORM_MINIMAL_VECTOR, HERMITE_INEQUALITY }
  -- @@RETURN END

end HolANT.HermiteInequality
