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
  literals right to left.  The `do` macro of HolCore/OcamlOrder.lean
  (HolLight.Syntax) binds each statement's `(← ...)` actions in that order,
  so quotations and rules (MESON, ARITH_RULE, ...) run as in HOL Light;
  where a rule is bound by a `let` before the proof, it is bound in OCaml's
  order.
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
    let lemma := (← prove r"!b. FINITE {u:int | abs(real_of_int u) <= b}" (GEN_TAC THEN MP_TAC (← SPEC (← q r"b:real") REAL_ARCH_SIMPLE) THEN DISCH_THEN (X_CHOOSE_TAC (← q r"N:num")) THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{u:int | --(&N) <= u /\ u <= &N}") THEN REWRITE_TAC [FINITE_INT_SEG, SUBSET, IN_ELIM_THM, (← GSYM INT_ABS_BOUNDS)] THEN REWRITE_TAC [int_le, int_abs_th, int_of_num_th] THEN ASM_MESON_TAC [REAL_LE_TRANS]))
    prove
      r"!s (A:K->K->real) C.
          FINITE s /\ (!i j. i IN s /\ j IN s ==> A i j = A j i) /\
          (!x. (?i. i IN s /\ ~(x i = &0))
               ==> &0 < sum s (\i. sum s (\j. A i j * x i * x j)))
          ==> FINITE {x:K->int | (!i. ~(i IN s) ==> x i = &0) /\
                                 sum s (\i. sum s (\j. A i j * real_of_int(x i) *
                                                      real_of_int(x j))) <= C}"
      (SUBGOAL_THEN (← q r"!s. FINITE s
        ==> !(A:K->K->real) C.
              (!i j. i IN s /\ j IN s ==> A i j = A j i) /\
              (!x. (?i. i IN s /\ ~(x i = &0))
                   ==> &0 < sum s (\i. sum s (\j. A i j * x i * x j)))
              ==> FINITE
                   {x:K->int | (!i. ~(i IN s) ==> x i = &0) /\
                               sum s (\i. sum s (\j. A i j * real_of_int(x i) *
                                                    real_of_int(x j))) <= C}") (fun th => tactic_of do pure (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC (← MP (← SPEC (← q r"s:K->bool") th) (← ASSUME (← q r"FINITE(s:K->bool)"))) THEN ASM_REWRITE_TAC [])) THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{(\i. &0):K->int}") THEN REWRITE_TAC [FINITE_SING, SUBSET, IN_ELIM_THM, IN_SING, NOT_IN_EMPTY] THEN REWRITE_TAC [FUN_EQ_THM] THEN MESON_TAC [], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"a:K"), (← q r"t:K->bool")] THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN MAP_EVERY X_GEN_TAC [(← q r"A:K->K->real"), (← q r"C:real")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"a:K"), (← q r"t:K->bool"), (← q r"A:K->K->real")] QUADRATIC_FORM_SCHUR_POSITIVE) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN REMOVE_THEN "ih" (MP_TAC o (SPEC (← q r"\i j. (A:K->K->real) i j - A i a * A a j / A a a"))) THEN DISCH_THEN (MP_TAC o (SPEC (← q r"C:real"))) THEN REWRITE_TAC [] THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"Y = {y:K->int | (!i. ~(i IN t) ==> y i = &0) /\
                    sum t (\i. sum t (\j. ((A:K->K->real) i j -
                                            A i a * A a j / A a a) *
                                          real_of_int(y i) *
                                          real_of_int(y j))) <= C}") THEN DISCH_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{(\y u i. if i = a then u else (y:K->int) i) y u | y,u |
     y IN Y /\
     u IN (\y. {u:int | abs(real_of_int u) <=
                        abs(sum t (\j. (A:K->K->real) a j * real_of_int(y j)) /
                            A a a) + max (&1) (C / A a a)}) y}") THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC [lemma], ALL_TAC] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:K->int") THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"\i. if i IN t then (x:K->int) i else &0"), (← q r"(x:K->int) a")] THEN REWRITE_TAC [] THEN MP_TAC (← BETA_RULE (← ISPECL [(← q r"a:K"), (← q r"t:K->bool"), (← q r"A:K->K->real"), (← q r"\i. real_of_int((x:K->int) i)")] QUADRATIC_FORM_COMPLETE_SQUARE)) THEN ANTS_TAC THENL [ASM_SIMP_TAC [REAL_LT_IMP_NZ] THEN ASM_MESON_TAC [IN_INSERT], DISCH_THEN (fun th => RULE_ASSUM_TAC (REWRITE_RULE [th]))] THEN SUBGOAL_THEN (← q r"!j. j IN t
        ==> real_of_int((if j IN t then (x:K->int) j else &0)) =
            real_of_int(x j)") ASSUME_TAC THENL [SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"sum t (\j. (A:K->K->real) a j *
               real_of_int(if j IN t then (x:K->int) j else &0)) =
    sum t (\j. A a j * real_of_int(x j)) /\
    sum t (\i. sum t (\j. (A i j - A i a * A a j / A a a) *
                          real_of_int(if i IN t then (x:K->int) i else &0) *
                          real_of_int(if j IN t then x j else &0))) =
    sum t (\i. sum t (\j. (A i j - A i a * A a j / A a a) *
                          real_of_int(x i) * real_of_int(x j)))") (CONJUNCTS_THEN SUBST1_TAC) THENL [CONJ_TAC THEN MATCH_MP_TAC SUM_EQ THEN SIMP_TAC [] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"t:K->bool"), (← q r"\i j. (A:K->K->real) i j - A i a * A a j / A a a"), (← q r"\i. real_of_int((x:K->int) i)")] QUADRATIC_FORM_POS_LE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ABBREV_TAC (← q r"c = sum t
              (\j. (A:K->K->real) a j * real_of_int((x:K->int) j))") THEN ABBREV_TAC (← q r"q = sum t (\i. sum t (\j. ((A:K->K->real) i j - A i a * A a j / A a a) *
                              real_of_int((x:K->int) i) *
                              real_of_int(x j)))") THEN REPEAT CONJ_TAC THENL [EXPAND_TAC "Y" THEN REWRITE_TAC [IN_ELIM_THM] THEN CONJ_TAC THENL [MESON_TAC [], ALL_TAC] THEN TRANS_TAC REAL_LE_TRANS (← q r"q:real") THEN CONJ_TAC THENL [EXPAND_TAC "q" THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN SIMP_TAC [] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN SIMP_TAC [], FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do if ← (do let z30 ← (do let z31 ← (pure th); pure (concl z31)); let z29 ← (q r"C:real"); pure (free_in z29 z30)) then (do let z33 ← (do let z34 ← (pure th); pure (concl z34)); let z32 ← (q r"q:real"); pure (free_in z32 z33)) else pure false)))) THEN MATCH_MP_TAC (← REAL_ARITH (← q r"&0 <= u ==> u + q <= C ==> q <= C:real")) THEN ASM_SIMP_TAC [REAL_LE_MUL, REAL_LT_IMP_LE, REAL_LE_POW_2]], ABBREV_TAC (← q r"z = real_of_int((x:K->int) a) + c / A a a") THEN SUBGOAL_THEN (← q r"z pow 2 <= C / (A:K->K->real) a a") ASSUME_TAC THENL [ASM_SIMP_TAC [REAL_LE_RDIV_EQ] THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do if ← (do let z20 ← (do let z21 ← (pure th); pure (concl z21)); let z19 ← (q r"z:real"); pure (free_in z19 z20)) then (do let z23 ← (do let z24 ← (pure th); pure (concl z24)); let z22 ← (q r"C:real"); pure (free_in z22 z23)) else pure false)))) THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"abs(z:real) <= max (&1) (z pow 2)") MP_TAC THENL [ONCE_REWRITE_TAC [(← GSYM REAL_POW2_ABS)] THEN ASM_CASES_TAC (← q r"abs(z:real) <= &1") THEN ASM_REWRITE_TAC [REAL_LE_MAX] THEN REWRITE_TAC [REAL_POW_2] THEN GEN_REWRITE_TAC LAND_CONV [(← GSYM REAL_MUL_RID)] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN UNDISCH_TAC (← q r"real_of_int((x:K->int) a) + c / A a a = z") THEN POP_ASSUM_LIST (MP_TAC o ((HolLight.end_itlist CONJ) o (filterM (fun th => (do if ← (do let z9 ← (do let z10 ← (pure th); pure (concl z10)); let z8 ← (q r"z:real"); pure (free_in z8 z9)) then (do pure !(← (do let z12 ← (do let z13 ← (pure th); pure (concl z13)); let z11 ← (q r"x:K->int"); pure (free_in z11 z12)))) else pure false))))) THEN REWRITE_TAC [REAL_LE_MAX] THEN REAL_ARITH_TAC, REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"i:K") THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [IN_INSERT]])

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
    let step := (← prove r"!m q D S p.
          &0 < m /\ &3 / &4 * m <= q /\
          q pow (2 * p) <= (&4 / &3) pow (p * (p - 1)) * S pow 2 /\
          D = m * S /\ 1 <= p
          ==> m pow (2 * (p + 1)) <= (&4 / &3) pow ((p + 1) * p) * D pow 2" (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"2 * (p + 1) = 2 * p + 2 /\ (p + 1) * p = 2 * p + p * (p - 1)") (CONJUNCTS_THEN SUBST1_TAC) THENL [CONJ_TAC THENL [ARITH_TAC, ALL_TAC] THEN FIRST_X_ASSUM ((X_CHOOSE_THEN (← q r"d:num") SUBST1_TAC) o (GEN_REWRITE_RULE id [LE_EXISTS])) THEN REWRITE_TAC [(← ARITH_RULE (← q r"(1 + d) - 1 = d:num"))] THEN CONV_TAC NUM_RING, ALL_TAC] THEN ASM_REWRITE_TAC [REAL_POW_ADD, REAL_POW_MUL] THEN SUBGOAL_THEN (← q r"(&3 / &4 * m) pow (2 * p) <= q pow (2 * p)") MP_TAC THENL [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [REAL_POW_MUL] THEN SUBGOAL_THEN (← q r"(&4 / &3) pow (2 * p) * (&3 / &4) pow (2 * p) = &1") ASSUME_TAC THENL [REWRITE_TAC [(← GSYM REAL_POW_MUL)] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC [REAL_POW_ONE], ALL_TAC] THEN SUBGOAL_THEN (← q r"&0 < (m:real) pow 2 /\ &0 < (&4 / &3:real) pow (2 * p)") STRIP_ASSUME_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do let z15 ← (do let z16 ← (pure th); pure (concl z16)); let z14 ← (q r"S:real"); pure (free_in z14 z15))))) THEN POP_ASSUM_LIST (MP_TAC o (HolLight.end_itlist CONJ)) THEN SPEC_TAC ((← q r"(&4 / &3) pow (2 * p)"), (← q r"a:real")) THEN SPEC_TAC ((← q r"(&3 / &4) pow (2 * p)"), (← q r"b:real")) THEN SPEC_TAC ((← q r"(&4 / &3) pow (p * (p - 1))"), (← q r"c:real")) THEN SPEC_TAC ((← q r"(m:real) pow (2 * p)"), (← q r"u:real")) THEN SPEC_TAC ((← q r"(q:real) pow (2 * p)"), (← q r"v:real")) THEN REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT DISCH_TAC THEN SUBGOAL_THEN (← q r"(u:real) <= a * c * S pow 2") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"(u:real) = a * (b * u)") SUBST1_TAC THENL [ASM_REWRITE_TAC [REAL_MUL_ASSOC, REAL_MUL_LID], ALL_TAC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN TRANS_TAC REAL_LE_TRANS (← q r"((a:real) * c * S pow 2) * m pow 2") THEN CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC [REAL_LT_IMP_LE], MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC]))
    let round := (← prove r"!c. ?n:int. abs(real_of_int n + c) <= &1 / &2" (GEN_TAC THEN MP_TAC (← SPEC (← q r"--c:real") INTEGER_ROUND) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"m:real") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"int_of_real m") THEN ASM_SIMP_TAC [REAL_OF_INT_OF_REAL] THEN ASM_REAL_ARITH_TAC))
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
      (SUBGOAL_THEN (← q r"!s. FINITE s
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
                    ring_det real_ring s A pow 2") (fun th => tactic_of do pure (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC (← MP (← SPEC (← q r"s:K->bool") th) (← ASSUME (← q r"FINITE(s:K->bool)"))) THEN ASM_REWRITE_TAC [])) THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC [] THEN MAP_EVERY X_GEN_TAC [(← q r"a:K"), (← q r"t:K->bool")] THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN X_GEN_TAC (← q r"A:K->K->real") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"(a:K) INSERT t"), (← q r"A:K->K->real")] QUADRATIC_FORM_MINIMAL_VECTOR) THEN ASM_REWRITE_TAC [FINITE_INSERT, NOT_INSERT_EMPTY] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"x:K->int") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "min")))) THEN EXISTS_TAC (← q r"x:K->int") THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"m = sum (a INSERT t) (\i. sum (a INSERT t) (\j. (A:K->K->real) i j *
          real_of_int((x:K->int) i) * real_of_int(x j)))") THEN SUBGOAL_THEN (← q r"&0 < (m:real)") ASSUME_TAC THENL [EXPAND_TAC "m" THEN FIRST_X_ASSUM (MATCH_MP_TAC o (checkM (fun th => (do if ← (do if ← (do let z159 ← (do let z160 ← (pure th); pure (concl z160)); pure (is_forall z159)) then (do let z162 ← (do let z163 ← (pure th); pure (concl z163)); let z161 ← (q r"A:K->K->real"); pure (free_in z161 z162)) else pure false) then (do let z164 ← (do pure (Prod.snd (← (do let z165 ← (do let z166 ← (pure th); pure (concl z166)); liftExcept (dest_forall z165))))); pure (is_imp z164)) else pure false)))) THEN FIRST_X_ASSUM ((X_CHOOSE_THEN (← q r"i:K") STRIP_ASSUME_TAC) o (checkM (fun z155 => (do let z156 ← (do let z157 ← (pure z155); pure (concl z157)); pure (is_exists z156))))) THEN EXISTS_TAC (← q r"i:K") THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [(← GSYM int_of_num_th), (← GSYM int_eq)] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"m <= sum (a INSERT t) (\i. sum (a INSERT t) (\j. (A:K->K->real) i j *
          real_of_int(if i = a then &1 else &0) *
          real_of_int(if j = a then &1 else &0)))") MP_TAC THENL [USE_THEN "min" (MP_TAC o (SPEC (← q r"\i:K. if i = a then &1:int else &0"))) THEN REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC [IN_INSERT], ALL_TAC] THEN EXISTS_TAC (← q r"a:K") THEN REWRITE_TAC [IN_INSERT] THEN CONV_TAC INT_REDUCE_CONV, ALL_TAC] THEN REWRITE_TAC [(← MESON [int_of_num_th] (← q r"!p. real_of_int(if p then &1 else &0) = if p then &1 else &0"))] THEN ASM_SIMP_TAC [QUADRATIC_FORM_BASIS_VECTOR, FINITE_INSERT, IN_INSERT] THEN DISCH_TAC THEN ASM_SIMP_TAC [CARD_CLAUSES, SUC_SUB1] THEN ASM_CASES_TAC (← q r"t:K->bool = {}") THENL [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC [CARD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [real_pow, REAL_MUL_LID] THEN SIMP_TAC [RING_DET_SING, REAL_RING_CLAUSES, IN_UNIV] THEN REWRITE_TAC [REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"(a:K) INSERT t"), (← q r"A:K->K->real"), (← q r"x:K->int")] QUADRATIC_FORM_MINIMAL_PRIMITIVE) THEN ASM_REWRITE_TAC [FINITE_INSERT] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"(a:K) INSERT t"), (← q r"x:K->int"), (← q r"a:K")] INT_PRIMITIVE_UNIMODULAR_COLUMN) THEN ASM_REWRITE_TAC [FINITE_INSERT, IN_INSERT] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"U:K->K->int") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"ring_det real_ring (a INSERT t) (\k i. real_of_int((U:K->K->int) k i))
    pow 2 = &1") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"real_ring"), (← q r"ring_of_int real_ring"), (← q r"(a:K) INSERT t"), (← q r"U:K->K->int")] RING_DET_HOMOMORPHISM) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, FINITE_INSERT, INTEGER_RING, IN_UNIV, REAL_RING_OF_INT] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [(← GSYM int_pow_th), (← GSYM int_of_num_th), (← GSYM int_eq)] THEN ONCE_REWRITE_TAC [(← GSYM INT_POW2_ABS)] THEN ASM_REWRITE_TAC [INT_POW_ONE], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"(a:K) INSERT t"), (← q r"A:K->K->real"), (← q r"\k i. real_of_int((U:K->K->int) k i)")] QUADRATIC_FORM_CONGRUENT_POSITIVE) THEN ASM_REWRITE_TAC [FINITE_INSERT] THEN ANTS_TAC THENL [DISCH_TAC THEN UNDISCH_TAC (← q r"ring_det real_ring (a INSERT t) (\k i. real_of_int((U:K->K->int) k i))
      pow 2 = &1") THEN ASM_REWRITE_TAC [] THEN CONV_TAC REAL_RAT_REDUCE_CONV, REWRITE_TAC [] THEN STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"(a:K) INSERT t"), (← q r"A:K->K->real"), (← q r"\k i. real_of_int((U:K->K->int) k i)")] REAL_DET_CONGRUENT_MATRIX) THEN ASM_REWRITE_TAC [FINITE_INSERT, REAL_MUL_LID] THEN DISCH_TAC THEN ABBREV_TAC (← q r"B = \i j. sum (a INSERT t) (\k. sum (a INSERT t) (\l.
                real_of_int((U:K->K->int) k i) * (A:K->K->real) k l *
                real_of_int(U l j)))") THEN SUBGOAL_THEN (← q r"(B:K->K->real) a a = m") ASSUME_TAC THENL [EXPAND_TAC "B" THEN EXPAND_TAC "m" THEN REWRITE_TAC [] THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC (← q r"k:K") THEN DISCH_TAC THEN REWRITE_TAC [] THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC (← q r"l:K") THEN DISCH_TAC THEN REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(U:K->K->int) k a = x k /\ U l a = x l") (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_MESON_TAC [IN_INSERT], REAL_ARITH_TAC], ALL_TAC] THEN SUBGOAL_THEN (← q r"!y:K->int.
      (!i. ~(i IN a INSERT t) ==> y i = &0) /\
      (?i. i IN a INSERT t /\ ~(y i = &0))
      ==> m <= sum (a INSERT t) (\i. sum (a INSERT t) (\j.
                 (B:K->K->real) i j * real_of_int(y i) * real_of_int(y j)))") ASSUME_TAC THENL [X_GEN_TAC (← q r"y:K->int") THEN STRIP_TAC THEN EXPAND_TAC "B" THEN MP_TAC (← BETA_RULE (← ISPECL [(← q r"(a:K) INSERT t"), (← q r"A:K->K->real"), (← q r"\k i. real_of_int((U:K->K->int) k i)"), (← q r"\i. real_of_int((y:K->int) i)")] QUADRATIC_FORM_CHANGE_BASIS)) THEN ASM_REWRITE_TAC [FINITE_INSERT] THEN DISCH_THEN SUBST1_TAC THEN REMOVE_THEN "min" (MP_TAC o (SPEC (← q r"\k. if k IN a INSERT t
          then isum (a INSERT t) (\i. (U:K->K->int) k i * y i) else &0"))) THEN REWRITE_TAC [] THEN MATCH_MP_TAC (← TAUT (← q r"p /\ (q ==> r) ==> (p ==> q) ==> r")) THEN CONJ_TAC THENL [CONJ_TAC THENL [MESON_TAC [], ALL_TAC] THEN MATCH_MP_TAC (← TAUT (← q r"(~p ==> F) ==> p")) THEN DISCH_THEN (ASSUME_TAC o (REWRITE_RULE [NOT_EXISTS_THM, (← TAUT (← q r"~(p /\ ~q) <=> p ==> q"))])) THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"(a:K) INSERT t"), (← q r"U:K->K->int"), (← q r"y:K->int")] RING_DET_DEPENDENT_COLUMNS) THEN ASM_REWRITE_TAC [INTEGRAL_DOMAIN_INTEGER_RING, FINITE_INSERT, INTEGER_RING, IN_UNIV, INTEGER_RING_SUM] THEN MATCH_MP_TAC (← TAUT (← q r"p /\ ~q ==> ~(p ==> q)")) THEN REPEAT CONJ_TAC THENL [ASM_MESON_TAC [], X_GEN_TAC (← q r"k:K") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"k:K")) o (checkM (fun th => (do if ← (do let z83 ← (do let z84 ← (pure th); pure (concl z84)); pure (is_forall z83)) then (do let z86 ← (do let z87 ← (pure th); pure (concl z87)); let z85 ← (q r"U:K->K->int"); pure (free_in z85 z86)) else pure false))))) THEN ASM_REWRITE_TAC [], UNDISCH_TAC (← q r"abs(ring_det integer_ring (a INSERT t) (U:K->K->int)) =
                     &1") THEN INT_ARITH_TAC], MATCH_MP_TAC (← REAL_ARITH (← q r"(x:real) = y ==> m <= x ==> m <= y")) THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC (← q r"k:K") THEN DISCH_TAC THEN REWRITE_TAC [] THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC (← q r"l:K") THEN DISCH_TAC THEN ASM_REWRITE_TAC [int_isum, int_mul_th]], ALL_TAC] THEN SUBGOAL_THEN (← q r"(!i j. i IN a INSERT t /\ j IN a INSERT t
           ==> (B:K->K->real) i j = B j i) /\
    (!y. (?i. i IN a INSERT t /\ ~(y i = &0))
         ==> &0 < sum (a INSERT t) (\i. sum (a INSERT t)
                    (\j. B i j * y i * y j)))") STRIP_ASSUME_TAC THENL [EXPAND_TAC "B" THEN REWRITE_TAC [] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"a:K"), (← q r"t:K->bool"), (← q r"B:K->K->real")] QUADRATIC_FORM_SCHUR_POSITIVE) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN REMOVE_THEN "ih" (MP_TAC o (SPEC (← q r"\i j. (B:K->K->real) i j - B i a * B a j / B a a"))) THEN REWRITE_TAC [] THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"z:K->int") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"a:K"), (← q r"t:K->bool"), (← q r"B:K->K->real")] REAL_DET_SCHUR_COMPLEMENT) THEN ASM_SIMP_TAC [REAL_LT_IMP_NZ] THEN DISCH_TAC THEN MP_TAC (← SPEC (← q r"sum t (\j. (B:K->K->real) a j * real_of_int((z:K->int) j)) / m") round) THEN DISCH_THEN (X_CHOOSE_TAC (← q r"n:int")) THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"\i. if i = a then n else (z:K->int) i")) o (checkM (fun th => (do if ← (do if ← (do let z55 ← (do let z56 ← (pure th); pure (concl z56)); pure (is_forall z55)) then (do let z58 ← (do let z59 ← (pure th); pure (concl z59)); let z57 ← (q r"B:K->K->real"); pure (free_in z57 z58)) else pure false) then (do let z61 ← (do let z62 ← (pure th); pure (concl z62)); let z60 ← (q r"m:real"); pure (free_in z60 z61)) else pure false))))) THEN REWRITE_TAC [] THEN ANTS_TAC THENL [CONJ_TAC THENL [ASM_MESON_TAC [IN_INSERT], ALL_TAC] THEN EXISTS_TAC (← q r"i:K") THEN ASM_REWRITE_TAC [IN_INSERT] THEN COND_CASES_TAC THEN ASM_MESON_TAC [], ALL_TAC] THEN MP_TAC (← BETA_RULE (← ISPECL [(← q r"a:K"), (← q r"t:K->bool"), (← q r"B:K->K->real"), (← q r"\i. real_of_int(if i = a then n else (z:K->int) i)")] QUADRATIC_FORM_COMPLETE_SQUARE)) THEN ANTS_TAC THENL [ASM_SIMP_TAC [REAL_LT_IMP_NZ] THEN ASM_MESON_TAC [IN_INSERT], DISCH_THEN SUBST1_TAC] THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"!j. j IN t ==> (if j = a then n else (z:K->int) j) = z j") ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"sum t (\j. (B:K->K->real) a j *
               real_of_int(if j = a then n else (z:K->int) j)) =
    sum t (\j. B a j * real_of_int(z j)) /\
    sum t (\i. sum t (\j. (B i j - B i a * B a j / m) *
                          real_of_int(if i = a then n else (z:K->int) i) *
                          real_of_int(if j = a then n else z j))) =
    sum t (\i. sum t (\j. (B i j - B i a * B a j / m) *
                          real_of_int(z i) * real_of_int(z j)))") (CONJUNCTS_THEN SUBST1_TAC) THENL [CONJ_TAC THEN MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC [] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"c = sum t (\j. (B:K->K->real) a j * real_of_int((z:K->int) j))
                  / m") THEN ABBREV_TAC (← q r"q = sum t (\i. sum t (\j. ((B:K->K->real) i j - B i a * B a j / m) *
                              real_of_int((z:K->int) i) *
                              real_of_int(z j)))") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(real_of_int n + c) pow 2 <= &1 / &4") ASSUME_TAC THENL [MP_TAC (← SPECL [(← q r"real_of_int n + c"), (← q r"&1 / &2")] REAL_LE_SQUARE_ABS) THEN ASM_REWRITE_TAC [(← REAL_ARITH (← q r"abs(&1 / &2) = &1 / &2"))] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"m * (real_of_int n + c) pow 2 <= m * &1 / &4") ASSUME_TAC THENL [REWRITE_TAC [real_div, (← GSYM REAL_MUL_ASSOC)] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC [(← GSYM real_div)] THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [ADD1] THEN MATCH_MP_TAC step THEN MAP_EVERY EXISTS_TAC [(← q r"q:real"), (← q r"ring_det real_ring t (\i j. (B:K->K->real) i j - B i a * B a j / m)")] THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ASM_SIMP_TAC [(← ARITH_RULE (← q r"1 <= n <=> ~(n = 0)")), CARD_EQ_0]])

  -- @@RETURN BEGIN
  return { QUADRATIC_FORM_DET_POS, QUADRATIC_FORM_FINITE_INTEGER_POINTS,
           QUADRATIC_FORM_MINIMAL_VECTOR, HERMITE_INEQUALITY }
  -- @@RETURN END

end HolANT.HermiteInequality
