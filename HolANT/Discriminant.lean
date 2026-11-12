/- ========================================================================= -/
/- ANT: The discriminant of a number field k with ring of integers O ...   -/
/- ========================================================================= -/
/- File: HolANT/Discriminant.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/discriminant.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antdiscriminantdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/isum.ml, Library/products.ml, ANT/algmisc.ml, ANT/zlattice.ml, ANT/integral.ml, Library/floor.ml, ANT/numfield.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.Discriminant fills them).

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
import HolLibrary.Matroids
import HolLibrary.Permutations
import HolLibrary.RingDet
import HolLibrary.FieldTheory
import HolLibrary.Isum
import HolLibrary.Products
import HolANT.Algmisc
import HolANT.Zlattice
import HolANT.Integral
import HolLibrary.Floor
import HolANT.Numfield
import HolANT.IdealArith
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.IdealNorm
import HolANT.RingOfIntegers
import HolANT.NormIndex

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.Algmisc
open HolANT.Zlattice
open HolANT.Integral
open HolANT.Numfield
open HolANT.IdealArith
open HolANT.Dedekind
open HolANT.DedekindStruct
open HolANT.IdealNorm
open HolANT.RingOfIntegers
open HolANT.NormIndex

namespace HolANT.Discriminant

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ARITH_EQ BASIS_COORDINATES_CHANGE_OF_BASIS_INVERSE BASIS_COORDINATES_EXPAND
   BASIS_COORDINATES_UNIQUE BASIS_DISCRIMINANT_CHANGE_OF_BASIS
   BASIS_DISCRIMINANT_NONZERO CARD_IMAGE_EQ_INJ COND_RAND COND_RATOR
   CONTRAPOS_THM DIVIDES_ONE EQ_TRANS EXP_MONO_EQ EXTENSION
   EXTENSION_LINCOMB_ADD EXTENSION_LINCOMB_LMUL EXTENSION_LINCOMB_SUM
   FIELD_SUBFIELD_GENERATED FINITE_NUMSEG_LT FORALL_INT_CASES FORALL_IN_GSPEC
   FREE_BASIS_INTEGER_RING_COORDINATES FREE_BASIS_INTEGER_RING_SUBRING_GENERATED
   FREE_BASIS_IN_CARRIER FREE_BASIS_SCALE FUN_EQ_THM HAS_SIZE HAS_SIZE_0
   HAS_SIZE_CLAUSES HAS_SIZE_IMAGE_INJ IDEAL_GENERATED_SING_ALT
   IDEAL_GENERATED_SUBSET IMAGE_EQ IMAGE_o INTEGER_MOD_RING_CHAR INTEGER_RING
   INTEGER_RING_POW INTEGER_RING_SUM INT_ABS_POS INT_ADD_SUB
   INT_COSETS_MATRIX_IMAGE INT_DET_MUL INT_DIVIDES_RABS INT_EQ_MUL_RCANCEL
   INT_MATRIX_IMAGE_IN INT_MATRIX_MUL_ASSOC INT_MUL_EQ_1 INT_MUL_LZERO
   INT_MUL_SYM INT_OF_NUM_EQ INT_OF_NUM_OF_INT INT_OF_NUM_POW INT_POW2_ABS
   INT_POW_EQ_1_IMP INT_SUB_REFL IN_ELIM_THM IN_IMAGE IN_RING_IDEAL_LMUL
   IN_RING_IDEAL_RMUL IN_RING_IDEAL_SUB IN_RING_IDEAL_SUM IN_SING IN_UNIV
   ISUM_DELTA_GEN ISUM_EQ I_THM LEFT_AND_EXISTS_THM LEFT_IMP_EXISTS_THM LE_1
   NOT_IN_EMPTY NUMBER_FIELD_DEGREE_POS NUMBER_FIELD_FREE_BASIS_DEGREE
   NUMBER_FIELD_IMP_FIELD NUMBER_FIELD_INT_LINCOMB_SANDWICH
   NUMBER_FIELD_TRACE_INTEGRAL_BASIS ONE PRIME_1 PRIME_COPRIME_EQ QUOTIENT_RING
   RIGHT_AND_EXISTS_THM RING_0 RING_ADD_RZERO RING_COSET_0 RING_COSET_EQ_IDEAL
   RING_COSET_SETADD RING_DET_ADJUGATE_ROWS RING_DET_EQ RING_DET_HOMOMORPHISM
   RING_DET_I RING_DET_MUL RING_DET_TRANSP RING_HOMOMORPHISM_INTEGER_RING_OF_INT
   RING_HOMOMORPHISM_SUBFIELD_INCLUSION RING_IDEAL_IMP_SUBSET RING_MUL
   RING_MUL_LID RING_MUL_LZERO RING_OF_INT RING_OF_INTEGERS
   RING_OF_INTEGERS_FINITE_QUOTIENT RING_OF_INTEGERS_FREE
   RING_OF_INTEGERS_FREE_BASIS_FIELD RING_OF_INTEGERS_IDEAL_INTEGER
   RING_OF_INTEGERS_RING_OF_INT_MUL RING_OF_INTEGERS_SUBRING
   RING_OF_INTEGERS_SUBSET RING_OF_INT_0 RING_OF_INT_1 RING_OF_INT_EQ
   RING_OF_INT_EQ_0_CHAR_0 RING_OF_INT_EQ_CHAR_0 RING_OF_INT_IN_RING_OF_INTEGERS
   RING_OF_INT_IN_SUBFIELD_GENERATED RING_OF_INT_MUL RING_OF_INT_OF_NUM
   RING_OF_INT_POW RING_OF_INT_SUBFIELD_GENERATED RING_OF_NUM
   RING_POW_SUBFIELD_GENERATED RING_SETADD RING_SETADD_ASSOC RING_SETADD_LSUBSET
   RING_SUM RING_SUM_0 RING_SUM_DELTA RING_SUM_EQ RING_SUM_EQ_0 RING_SUM_LMUL
   RING_SUM_RING_OF_INTEGERS SELECT_UNIQUE SIMPLE_IMAGE SING_SUBSET SKOLEM_THM
   SUBFIELD_GENERATED SUBSET SUBSET_ANTISYM SUBSET_ANTISYM_EQ SUBSET_TRANS
   UNWIND_THM2 basis_discriminant free_basis ideal_norm int_coprime int_cosets
   num_coprime num_divides number_field o_THM ring_coset ring_setadd : thm)
  deriving Inhabited

/-- What discriminant.ml uses from Session besides theorems. -/
structure DiscriminantDeps where
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
  INT_RING : term → ExceptT String IO thm
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
/- discriminant.ml phrases from line 47 to 735                            -/
/- ---------------------------------------------------------------------- -/

structure Discriminant01 where
  -- @@FIELDS
  number_field_discriminant : thm
  NUMBER_FIELD_DISCRIMINANT_BASIS : thm
  NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD : thm
  NUMBER_FIELD_DISCRIMINANT_NONZERO : thm
  FREE_BASIS_INTEGER_RING_LINCOMB : thm
  INT_MATRIX_SURJECTIVE_MOD_PRIME : thm
  FREE_BASIS_INTEGER_RING_SPAN_INDEX : thm
  FREE_BASIS_INTEGER_RING_SPAN_COPRIME : thm
  NUMBER_FIELD_DISCRIMINANT_CHANGE_OF_BASIS : thm
  NUMBER_FIELD_INDEX_DETERMINANT : thm
  NUMBER_FIELD_DISCRIMINANT_INDEX : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDiscriminant01 [HolBase] (D : DiscriminantDeps) :
    ExceptT String IO Discriminant01 := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_MESON_TAC, INTEGER_RULE, INT_ARITH, INT_REDUCE_CONV, INT_RING,
        MESON_TAC, SET_RULE, SET_TAC, TAUT, new_definition, .. } := D
  let { BASIS_COORDINATES_CHANGE_OF_BASIS_INVERSE, BASIS_COORDINATES_EXPAND,
        BASIS_COORDINATES_UNIQUE, BASIS_DISCRIMINANT_CHANGE_OF_BASIS,
        BASIS_DISCRIMINANT_NONZERO, DIVIDES_ONE, EQ_TRANS, EXTENSION,
        EXTENSION_LINCOMB_ADD, EXTENSION_LINCOMB_LMUL, EXTENSION_LINCOMB_SUM,
        FIELD_SUBFIELD_GENERATED, FINITE_NUMSEG_LT, FORALL_INT_CASES, FORALL_IN_GSPEC,
        FREE_BASIS_INTEGER_RING_COORDINATES, FREE_BASIS_IN_CARRIER, FUN_EQ_THM,
        HAS_SIZE_IMAGE_INJ, IDEAL_GENERATED_SING_ALT, IDEAL_GENERATED_SUBSET,
        INTEGER_MOD_RING_CHAR, INTEGER_RING, INTEGER_RING_POW, INTEGER_RING_SUM,
        INT_ABS_POS, INT_ADD_SUB, INT_COSETS_MATRIX_IMAGE, INT_DET_MUL,
        INT_MATRIX_IMAGE_IN, INT_MATRIX_MUL_ASSOC, INT_MUL_EQ_1, INT_MUL_LZERO,
        INT_MUL_SYM, INT_OF_NUM_EQ, INT_OF_NUM_OF_INT, INT_POW2_ABS, INT_SUB_REFL,
        IN_ELIM_THM, IN_IMAGE, IN_UNIV, ISUM_DELTA_GEN, ISUM_EQ, I_THM,
        LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM, LE_1, NUMBER_FIELD_DEGREE_POS,
        NUMBER_FIELD_FREE_BASIS_DEGREE, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_TRACE_INTEGRAL_BASIS, PRIME_1, PRIME_COPRIME_EQ,
        RIGHT_AND_EXISTS_THM, RING_DET_ADJUGATE_ROWS, RING_DET_EQ,
        RING_DET_HOMOMORPHISM, RING_DET_I, RING_DET_MUL, RING_DET_TRANSP,
        RING_HOMOMORPHISM_INTEGER_RING_OF_INT, RING_HOMOMORPHISM_SUBFIELD_INCLUSION,
        RING_MUL, RING_OF_INTEGERS, RING_OF_INTEGERS_FREE,
        RING_OF_INTEGERS_FREE_BASIS_FIELD, RING_OF_INT_0, RING_OF_INT_EQ,
        RING_OF_INT_EQ_0_CHAR_0, RING_OF_INT_IN_RING_OF_INTEGERS,
        RING_OF_INT_IN_SUBFIELD_GENERATED, RING_OF_INT_MUL, RING_OF_INT_OF_NUM,
        RING_OF_INT_POW, RING_OF_INT_SUBFIELD_GENERATED, RING_OF_NUM,
        RING_POW_SUBFIELD_GENERATED, RING_SETADD, RING_SUM_EQ,
        RING_SUM_RING_OF_INTEGERS, SELECT_UNIQUE, SKOLEM_THM, SUBFIELD_GENERATED,
        SUBSET, SUBSET_ANTISYM_EQ, basis_discriminant, int_coprime, int_cosets,
        num_coprime, num_divides, number_field, ring_coset, ring_setadd, .. } := D.core1
  -- @@SCOPE END

  let number_field_discriminant ← new_definition
    r"number_field_discriminant (k:A ring) =
  @d. !n w. free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w
            ==> basis_discriminant (integer_ring,ring_of_integers k)
                                       (ring_of_int k) n w = d"

  let NUMBER_FIELD_DISCRIMINANT_BASIS ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"ring_det integer_ring {i:num | i < n}
          (\i j. if i = j then ring_1 integer_ring
                 else ring_0 integer_ring)"
    let q2 ← q r"w:num->A"
    let q3 ← q r"w':num->A"
    let q4 ← q r"n:num"
    let q5 ← q r"n:num"
    let q6 ← q r"r:A ring"
    let q7 ← q r"integer_ring"
    let q8 ← q r"ring_of_int r:int->A"
    let v9 ← ISPECL [q8, q7, q6, q5, q4, q3, q2] BASIS_COORDINATES_CHANGE_OF_BASIS_INVERSE
    let q10 ← q r"ring_det integer_ring {i:num | i < n}
       (\i j. ring_sum integer_ring {m | m < n}
                (\m. basis_coordinates (integer_ring,r) (ring_of_int r) n w
                       ((w':num->A) m) i *
                     basis_coordinates (integer_ring,r) (ring_of_int r) n w'
                       ((w:num->A) j) m)) = &1"
    let q11 ← q r"\m j. basis_coordinates (integer_ring,r) (ring_of_int r) n w'
               ((w:num->A) j) m"
    let q12 ← q r"\i m. basis_coordinates (integer_ring,r) (ring_of_int r) n w
               ((w':num->A) m) i"
    let q13 ← q r"{i:num | i < n}"
    let q14 ← q r"integer_ring"
    let v15 ← ISPECL [q14, q13, q12, q11] RING_DET_MUL
    let q16 ← q r"\i m. basis_coordinates (integer_ring,r) (ring_of_int r) n w
               ((w':num->A) m) i"
    let q17 ← q r"{i:num | i < n}"
    let q18 ← q r"integer_ring"
    let v19 ← ISPECL [q18, q17, q16] RING_DET_TRANSP
    let q20 ← q r"(x:int) pow 2 = &1 ==> x pow 2 * d = d"
    let r21 ← INT_RING q20
    let q22 ← q r"i:num"
    let q23 ← q r"\i j. basis_coordinates (integer_ring,r) (ring_of_int r) n w
                            ((w':num->A) i) j"
    let q24 ← q r"w':num->A"
    let q25 ← q r"w:num->A"
    let q26 ← q r"n:num"
    let q27 ← q r"r:A ring"
    let q28 ← q r"integer_ring"
    let q29 ← q r"ring_of_int r:int->A"
    let v30 ← ISPECL [q29, q28, q27, q26, q25, q24, q23] BASIS_DISCRIMINANT_CHANGE_OF_BASIS
    let p31 ← prove r"!r:A ring n w w'.
        free_basis (integer_ring,r) (ring_of_int r) n w /\
        free_basis (integer_ring,r) (ring_of_int r) n w'
        ==> basis_discriminant (integer_ring,r) (ring_of_int r) n w' =
            basis_discriminant (integer_ring,r) (ring_of_int r) n w" (REPEAT STRIP_TAC THEN MP_TAC v30 THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, INTEGER_RING, IN_UNIV, INTEGER_RING_POW] THEN ANTS_TAC THENL [X_GEN_TAC q22 THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC BASIS_COORDINATES_EXPAND THEN ASM_MESON_TAC [FREE_BASIS_IN_CARRIER], DISCH_THEN SUBST1_TAC] THEN MATCH_MP_TAC r21 THEN MP_TAC v19 THEN MP_TAC v15 THEN REWRITE_TAC [FINITE_NUMSEG_LT, INTEGER_RING, IN_UNIV] THEN SUBGOAL_THEN q10 SUBST1_TAC THENL [MP_TAC v9 THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, INTEGER_RING] THEN DISCH_TAC THEN TRANS_TAC EQ_TRANS q1 THEN CONJ_TAC THENL [MATCH_MP_TAC RING_DET_EQ THEN ASM_SIMP_TAC [IN_ELIM_THM, INTEGER_RING], SIMP_TAC [RING_DET_I, FINITE_NUMSEG_LT, INTEGER_RING]], ALL_TAC] THEN DISCH_THEN (MP_TAC o SYM) THEN REWRITE_TAC [INT_MUL_EQ_1] THEN DISCH_THEN (fun th => DISCH_THEN SUBST1_TAC THEN STRIP_ASSUME_TAC th) THEN ASM_REWRITE_TAC [] THEN CONV_TAC INT_REDUCE_CONV)
    let lemma := p31
    let q32 ← q r"v:num->A"
    let q33 ← q r"w:num->A"
    let q34 ← q r"n:num"
    let q35 ← q r"ring_of_integers k:A ring"
    let v36 ← ISPECL [q35, q34, q33, q32] lemma
    let q37 ← q r"m:num = n"
    let q38 ← q r"v:num->A"
    let q39 ← q r"m:num"
    let q40 ← q r"w:num->A"
    let q41 ← q r"n:num"
    let q42 ← q r"d:int"
    prove
      r"!k:A ring n w.
          number_field k /\
          free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w
          ==> number_field_discriminant k =
              basis_discriminant (integer_ring,ring_of_integers k)
                                     (ring_of_int k) n w"
      (REPEAT STRIP_TAC THEN REWRITE_TAC [number_field_discriminant] THEN MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC q42 THEN REWRITE_TAC [] THEN EQ_TAC THENL [DISCH_THEN (MP_TAC o (SPECL [q41, q40])) THEN ASM_REWRITE_TAC [] THEN MESON_TAC [], DISCH_THEN SUBST1_TAC THEN MAP_EVERY X_GEN_TAC [q39, q38] THEN DISCH_TAC THEN SUBGOAL_THEN q37 SUBST_ALL_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_FREE_BASIS_FIELD], ALL_TAC] THEN MP_TAC v36 THEN ASM_REWRITE_TAC [RING_OF_INTEGERS]])

  let NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD ← prove
    r"!k:A ring n w.
        number_field k /\
        free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w
        ==> ring_of_int k (number_field_discriminant k) =
            basis_discriminant (subfield_generated k {ring_0 k},k) I n w"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A")] NUMBER_FIELD_DISCRIMINANT_BASIS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPEC (← q r"subfield_generated k {ring_0 k}:A ring") RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN REWRITE_TAC [RING_OF_INT_SUBFIELD_GENERATED] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_int k:int->A"), (← q r"integer_ring"), (← q r"ring_of_integers k:A ring"), (← q r"n:num"), (← q r"w:num->A")] FREE_BASIS_IN_CARRIER) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN REWRITE_TAC [basis_discriminant] THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"subfield_generated k {ring_0 k}:A ring"), (← q r"ring_of_int k:int->A"), (← q r"{i:num | i < n}"), (← q r"\i j. algebra_trace (integer_ring,ring_of_integers k) (ring_of_int k)
             (ring_mul (ring_of_integers k) ((w:num->A) i) (w j))")] RING_DET_HOMOMORPHISM) THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT, INTEGER_RING, IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC [IN_ELIM_THM, RING_OF_INTEGERS] THEN MAP_EVERY X_GEN_TAC [(← q r"i:num"), (← q r"j:num")] THEN STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC NUMBER_FIELD_TRACE_INTEGRAL_BASIS THEN MAP_EVERY EXISTS_TAC [(← q r"n:num"), (← q r"w:num->A")] THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"(w:num->A) i"), (← q r"(w:num->A) j")] RING_MUL) THEN ASM_SIMP_TAC [RING_OF_INTEGERS])

  let NUMBER_FIELD_DISCRIMINANT_NONZERO ← prove
    r"!k:A ring. number_field k ==> ~(number_field_discriminant k = &0)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM ((X_CHOOSE_TAC (← q r"w:num->A")) o (MATCH_MP RING_OF_INTEGERS_FREE)) THEN ABBREV_TAC (← q r"n = extension_degree (subfield_generated k {ring_0 k},k:A ring) I") THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A")] NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A")] RING_OF_INTEGERS_FREE_BASIS_FIELD) THEN ASM_REWRITE_TAC [RING_OF_INT_0] THEN STRIP_TAC THEN CONV_TAC (RAND_CONV SYM_CONV) THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k}:A ring"), (← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A")] BASIS_DISCRIMINANT_NONZERO) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (MP_TAC o (MATCH_MP NUMBER_FIELD_DEGREE_POS)) THEN RULE_ASSUM_TAC (REWRITE_RULE [number_field]) THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, SUBFIELD_GENERATED, (← GSYM RING_OF_INT_OF_NUM), RING_OF_INT_SUBFIELD_GENERATED, RING_OF_INT_EQ_0_CHAR_0, INT_OF_NUM_EQ, LE_1])

  let FREE_BASIS_INTEGER_RING_LINCOMB ← prove
    r"!r:A ring n w psi.
        free_basis (integer_ring,r) (ring_of_int r) n w /\
        (!z. psi z = ring_sum r {i | i < n}
                       (\i. ring_mul r (ring_of_int r (z i)) (w i)))
        ==> (!z. psi z IN ring_carrier r) /\
            (!x. x IN ring_carrier r
                 ==> ?z. (!i. ~(i < n) ==> z i = &0) /\ psi z = x) /\
            (!z z'. psi z = psi z' <=> !i. i < n ==> z i = z' i) /\
            (!z z'. psi(\i. z i + z' i) = ring_add r (psi z) (psi z')) /\
            (!m z. psi(\i. m * z i) = ring_mul r (ring_of_int r m) (psi z)) /\
            (!g C. (!i. i < n
                        ==> g i = ring_sum r {j | j < n}
                                    (\j. ring_mul r (ring_of_int r (C i j))
                                                    (w j)))
                   ==> !c. ring_sum r {i | i < n}
                             (\i. ring_mul r (ring_of_int r (c i)) (g i)) =
                           psi(\i. isum {j | j < n} (\j. C j i * c j)))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"n:num"), (← q r"w:num->A")] FREE_BASIS_INTEGER_RING_COORDINATES) THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FREE_BASIS_IN_CARRIER)) THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPEC (← q r"r:A ring") RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL [REPEAT GEN_TAC THEN EQ_TAC THENL [DISCH_TAC THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_int r:int->A"), (← q r"integer_ring"), (← q r"r:A ring"), (← q r"n:num"), (← q r"w:num->A")] BASIS_COORDINATES_UNIQUE) THEN ASM_REWRITE_TAC [INTEGER_RING, IN_UNIV] THEN DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← SPECL [(← q r"ring_sum r {i | i < n}
           (\i. ring_mul r (ring_of_int r ((z':num->int) i)) ((w:num->A) i))"), (← q r"z:num->int")] th) THEN MP_TAC (← SPECL [(← q r"ring_sum r {i | i < n}
           (\i. ring_mul r (ring_of_int r ((z':num->int) i)) ((w:num->A) i))"), (← q r"z':num->int")] th))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th1 => tactic_of do pure (DISCH_THEN (fun th2 => tactic_of do pure (MP_TAC (← CONJ (← SPEC (← q r"i:num") th1) (← SPEC (← q r"i:num") th2)))))) THEN ASM_REWRITE_TAC [] THEN MESON_TAC [], DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC], REPEAT GEN_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_int r:int->A"), (← q r"integer_ring"), (← q r"r:A ring"), (← q r"{i:num | i < n}")] EXTENSION_LINCOMB_ADD) THEN ASM_REWRITE_TAC [INTEGER_RING, IN_UNIV, FINITE_NUMSEG_LT] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [IN_ELIM_THM], REPEAT GEN_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_int r:int->A"), (← q r"integer_ring"), (← q r"r:A ring"), (← q r"{i:num | i < n}")] EXTENSION_LINCOMB_LMUL) THEN ASM_REWRITE_TAC [INTEGER_RING, IN_UNIV, FINITE_NUMSEG_LT] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [IN_ELIM_THM], MAP_EVERY X_GEN_TAC [(← q r"g:num->A"), (← q r"C:num->num->int")] THEN DISCH_TAC THEN X_GEN_TAC (← q r"c:num->int") THEN TRANS_TAC EQ_TRANS (← q r"ring_sum r {m | m < n}
        (\m. ring_mul r (ring_of_int r ((c:num->int) m))
               (ring_sum r {i | i < n}
                 (\i. ring_mul r (ring_of_int r (C m i)) ((w:num->A) i))))") THEN CONJ_TAC THENL [MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_int r:int->A"), (← q r"integer_ring"), (← q r"r:A ring"), (← q r"{i:num | i < n}"), (← q r"{i:num | i < n}"), (← q r"c:num->int"), (← q r"C:num->num->int"), (← q r"w:num->A")] EXTENSION_LINCOMB_SUM) THEN ASM_REWRITE_TAC [INTEGER_RING, IN_UNIV, FINITE_NUMSEG_LT, IN_ELIM_THM, INTEGER_RING_SUM] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC ISUM_EQ THEN REWRITE_TAC [INT_MUL_SYM]])

  let INT_MATRIX_SURJECTIVE_MOD_PRIME ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"s:K->bool"
    let q2 ← q r"ring_of_int(integer_mod_ring p)"
    let q3 ← q r"integer_mod_ring p"
    let q4 ← q r"integer_ring"
    let v5 ← ISPECL [q4, q3, q2, q1] RING_DET_HOMOMORPHISM
    let q6 ← q r"ring_det integer_ring s (g:K->K->int)"
    let q7 ← q r"ring_det integer_ring s (f:K->K->int)"
    let q8 ← q r"integer_mod_ring p"
    let v9 ← ISPECL [q8, q7, q6] RING_OF_INT_EQ
    let p10 ← prove r"!s (f:K->K->int) g p.
        FINITE s /\ (!i j. i IN s /\ j IN s ==> (f i j == g i j) (mod &p))
        ==> (ring_det integer_ring s f == ring_det integer_ring s g)
            (mod &p)" (REPEAT STRIP_TAC THEN MP_TAC v9 THEN REWRITE_TAC [INTEGER_MOD_RING_CHAR] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC v5 THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, INTEGER_RING, IN_UNIV] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN MATCH_MP_TAC RING_DET_EQ THEN ASM_SIMP_TAC [RING_OF_INT_EQ, INTEGER_MOD_RING_CHAR])
    let lemma := p10
    let q11 ← q r"&p * u + ring_det integer_ring s (A:K->K->int) * v = &1"
    let q12 ← q r"l:K = i"
    let q13 ← q r"l:K"
    let q14 ← q r"i:K"
    let q15 ← q r"A:K->K->int"
    let q16 ← q r"s:K->bool"
    let q17 ← q r"integer_ring"
    let v18 ← ISPECL [q17, q16, q15, q14, q13] RING_DET_ADJUGATE_ROWS
    let q19 ← q r"l:K"
    let q20 ← q r"isum s (\l. isum s (\k. (A:K->K->int) i k *
                              ring_cofactor integer_ring s A l k) *
                  (v * (z:K->int) l)) =
      isum s (\l. if l = i then ring_det integer_ring s A * (v * z l)
                  else &0)"
    let q21 ← q r"i:K"
    let q22 ← q r"i:K"
    let q23 ← q r"\l j:K. v * (z:K->int) l"
    let q24 ← q r"\j k. ring_cofactor integer_ring s (A:K->K->int) k j"
    let q25 ← q r"A:K->K->int"
    let q26 ← q r"s:K->bool"
    let v27 ← ISPECL [q26, q25, q24, q23, q22, q21] INT_MATRIX_MUL_ASSOC
    let v28 ← BETA_RULE v27
    let q29 ← q r"i:K"
    let q30 ← q r"\i. u * (z:K->int) i"
    let q31 ← q r"\j. isum s (\k. ring_cofactor integer_ring s A k j *
                                (v * (z:K->int) k))"
    let q32 ← q r"z:K->int"
    let v33 ← GSYM num_divides
    let v34 ← GSYM num_coprime
    let q35 ← q r"(a:int) divides --b <=> a divides b"
    let r36 ← INTEGER_RULE q35
    let q37 ← q r"coprime(a:int,--b) <=> coprime(a,b)"
    let r38 ← INTEGER_RULE q37
    let q39 ← q r"d:int"
    let q40 ← q r"ring_det integer_ring s (A:K->K->int)"
    let q41 ← q r"~(&p divides ring_det integer_ring s (A:K->K->int))"
    let v42 ← GSYM int_coprime
    let q43 ← q r"?u v. &p * u + ring_det integer_ring s (A:K->K->int) * v = &1"
    let v44 ← GSYM num_divides
    let q45 ← q r"!a b p:int. p divides a /\ (&1 == a * b) (mod p) ==> p divides &1"
    let r46 ← INTEGER_RULE q45
    let q47 ← q r"p ==> ~q <=> ~(p /\ q)"
    let r48 ← TAUT q47
    let q49 ← q r"&p divides ring_det integer_ring s (A:K->K->int)"
    let q50 ← q r"s:K->bool"
    let q51 ← q r"integer_ring"
    let v52 ← ISPECL [q51, q50] RING_DET_I
    let q53 ← q r"!x a b p:int. x = a + p * b ==> (x == a) (mod p)"
    let r54 ← INTEGER_RULE q53
    let q55 ← q r"i:K"
    let q56 ← q r"j:K"
    let q57 ← q r"j:K"
    let q58 ← q r"i:K"
    let q59 ← q r"p:num"
    let q60 ← q r"\i j:K. isum s (\m. (A:K->K->int) i m *
                            (c:(K->int)->K->int)
                              (\i:K. if i = j then &1:int else &0) m)"
    let q61 ← q r"\i j:K. if i = j then &1:int else &0"
    let q62 ← q r"s:K->bool"
    let v63 ← ISPECL [q62, q61, q60, q59] lemma
    let q64 ← q r"\i:K. if i = j then &1:int else &0"
    let q65 ← q r"j:K"
    let q66 ← q r"y:(K->int)->K->int"
    let q67 ← q r"c:(K->int)->K->int"
    prove
      r"!s (A:K->K->int) p.
          FINITE s /\ prime p
          ==> ((!z. ?c y. !i. i IN s
                            ==> z i = isum s (\j. A i j * c j) + &p * y i) <=>
               ~(&p divides ring_det integer_ring s A))"
      (REPEAT STRIP_TAC THEN EQ_TAC THENL [REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [q67, q66] THEN DISCH_THEN (ASSUME_TAC o (BETA_RULE o ((GEN q65) o (SPEC q64)))) THEN DISCH_TAC THEN MP_TAC v63 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN MAP_EVERY X_GEN_TAC [q58, q57] THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPECL [q56, q55])) THEN ASM_REWRITE_TAC [] THEN MATCH_ACCEPT_TAC r54, ALL_TAC] THEN MP_TAC v52 THEN ASM_SIMP_TAC [INTEGER_RING, INT_DET_MUL] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN UNDISCH_TAC q49 THEN REWRITE_TAC [r48] THEN DISCH_THEN (MP_TAC o (MATCH_MP r46)) THEN REWRITE_TAC [v44, DIVIDES_ONE] THEN ASM_MESON_TAC [PRIME_1], DISCH_TAC THEN SUBGOAL_THEN q43 STRIP_ASSUME_TAC THENL [REWRITE_TAC [v42] THEN UNDISCH_TAC q41 THEN SPEC_TAC (q40, q39) THEN REWRITE_TAC [FORALL_INT_CASES, r38, r36] THEN ASM_SIMP_TAC [v34, v33, PRIME_COPRIME_EQ], ALL_TAC] THEN X_GEN_TAC q32 THEN EXISTS_TAC q31 THEN EXISTS_TAC q30 THEN X_GEN_TAC q29 THEN DISCH_TAC THEN MP_TAC v28 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN SUBGOAL_THEN q20 SUBST1_TAC THENL [MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC q19 THEN DISCH_TAC THEN MP_TAC v18 THEN ASM_REWRITE_TAC [INTEGER_RING, INTEGER_RING_SUM, IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN ASM_CASES_TAC q12 THEN ASM_REWRITE_TAC [INT_MUL_LZERO], ASM_REWRITE_TAC [ISUM_DELTA_GEN] THEN UNDISCH_TAC q11 THEN CONV_TAC INT_RING]])

  let FREE_BASIS_INTEGER_RING_SPAN_INDEX ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!S V (f:B->C).
       (!s. s IN S ==> s SUBSET V) /\
       (!a b. a IN V /\ b IN V /\ f a = f b ==> a = b)
       ==> !x y. x IN S /\ y IN S /\ IMAGE f x = IMAGE f y ==> x = y")
    let r2 ← INT_ARITH (← q r"!a b c:int. a - b = c ==> a = b + c")
    prove
      r"!r:A ring n w g C.
          free_basis (integer_ring,r) (ring_of_int r) n w /\
          (!i. i < n
               ==> g i = ring_sum r {j | j < n}
                           (\j. ring_mul r (ring_of_int r (C i j)) (w j))) /\
          ~(ring_det integer_ring {i | i < n} C = &0)
          ==> {ring_coset r
                {ring_sum r {i | i < n}
                   (\i. ring_mul r (ring_of_int r (c i)) (g i)) |
                 c IN (:num->int)} x |
               x | x IN ring_carrier r}
              HAS_SIZE num_of_int(abs(ring_det integer_ring {i | i < n} C))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN ABBREV_TAC (← q r"psi = \z:num->int. ring_sum r {i | i < n}
              (\i. ring_mul r (ring_of_int r (z i)) ((w:num->A) i))") THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"psi:(num->int)->A")] FREE_BASIS_INTEGER_RING_LINCOMB) THEN ANTS_TAC THENL [EXPAND_TAC "psi" THEN ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "car") (CONJUNCTS_THEN2 (LABEL_TAC "onto") (CONJUNCTS_THEN2 (LABEL_TAC "inj") (CONJUNCTS_THEN2 (LABEL_TAC "add") (MP_TAC o ((SPECL [(← q r"g:num->A"), (← q r"C:num->num->int")]) o CONJUNCT2)))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN ABBREV_TAC (← q r"M = {(psi:(num->int)->A) (\i. isum {j | j < n} (\j. C j i * c j)) |
           c IN (:num->int)}") THEN ABBREV_TAC (← q r"L = int_matrix_image {i:num | i < n} (\i j. (C:num->num->int) j i)") THEN SUBGOAL_THEN (← q r"!z:num->int. (!i. ~(i < n) ==> z i = &0)
           ==> ring_coset (r:A ring) M ((psi:(num->int)->A) z) =
               IMAGE psi {y | (!i. ~(i < n) ==> y i = &0) /\
                              (\i. y i - z i) IN L}") ASSUME_TAC THENL [X_GEN_TAC (← q r"z:num->int") THEN DISCH_TAC THEN EXPAND_TAC "M" THEN EXPAND_TAC "L" THEN REWRITE_TAC [ring_coset, EXTENSION, IN_ELIM_THM, IN_IMAGE, IN_UNIV, INT_MATRIX_IMAGE_IN] THEN X_GEN_TAC (← q r"b:A") THEN EQ_TAC THENL [REWRITE_TAC [LEFT_IMP_EXISTS_THM, LEFT_AND_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"c:num->int")] THEN DISCH_THEN (fun th => tactic_of do pure (SUBST1_TAC (← CONJUNCT2 th) THEN SUBST1_TAC (← CONJUNCT1 th))) THEN EXISTS_TAC (← q r"\i:num. if i < n then z i + isum {j | j < n} (\j. C j i * c j)
                        else &0") THEN REPEAT CONJ_TAC THENL [USE_THEN "add" (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM th)])) THEN USE_THEN "inj" (fun th => SIMP_TAC [th]), SIMP_TAC [], EXISTS_TAC (← q r"c:num->int") THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"i:num") THEN ASM_CASES_TAC (← q r"i:num < n") THEN ASM_SIMP_TAC [INT_ADD_SUB, INT_SUB_REFL]], REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"y:num->int") THEN DISCH_THEN (CONJUNCTS_THEN2 SUBST1_TAC (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC (← q r"c:num->int")))) THEN EXISTS_TAC (← q r"(psi:(num->int)->A) (\i. isum {j | j < n} (\j:num. C j i * c j))") THEN CONJ_TAC THENL [EXISTS_TAC (← q r"c:num->int") THEN REFL_TAC, ALL_TAC] THEN USE_THEN "add" (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM th)])) THEN USE_THEN "inj" (fun th => REWRITE_TAC [th]) THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (← do let c := (← q r"i:num"); pure (fun th => AP_THM th c))) THEN ASM_REWRITE_TAC [] THEN MATCH_ACCEPT_TAC r2], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"{i:num | i < n}"), (← q r"\i j. (C:num->num->int) j i")] INT_COSETS_MATRIX_IMAGE) THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"{i:num | i < n}"), (← q r"C:num->num->int")] RING_DET_TRANSP) THEN REWRITE_TAC [FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"{ring_coset r M x | x | x IN ring_carrier r} =
      IMAGE (IMAGE (psi:(num->int)->A)) (int_cosets {i:num | i < n} L)") SUBST1_TAC THENL [GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"t:A->bool") THEN REWRITE_TAC [IN_ELIM_THM, IN_IMAGE, int_cosets] THEN EQ_TAC THENL [DISCH_THEN (X_CHOOSE_THEN (← q r"a:A") (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN USE_THEN "onto" (MP_TAC o (SPEC (← q r"a:A"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"z:num->int") (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM))) THEN EXISTS_TAC (← q r"{y | (!i. ~(i < n) ==> y i = &0) /\
                         (\i. y i - (z:num->int) i) IN L}") THEN ASM_SIMP_TAC [] THEN EXISTS_TAC (← q r"z:num->int") THEN ASM_REWRITE_TAC [], DISCH_THEN (X_CHOOSE_THEN (← q r"u:(num->int)->bool") (CONJUNCTS_THEN2 SUBST1_TAC (X_CHOOSE_THEN (← q r"z:num->int") (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)))) THEN EXISTS_TAC (← q r"(psi:(num->int)->A) z") THEN ASM_SIMP_TAC []], ALL_TAC] THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"int_cosets {i:num | i < n} L"), (← q r"{z:num->int | !i. ~(i < n) ==> z i = &0}"), (← q r"psi:(num->int)->A")] r1) THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL [REWRITE_TAC [int_cosets, FORALL_IN_GSPEC, IN_ELIM_THM] THEN SET_TAC [], REWRITE_TAC [IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:num->int"), (← q r"b:num->int")] THEN USE_THEN "inj" (fun th => REWRITE_TAC [th]) THEN STRIP_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"i:num") THEN ASM_CASES_TAC (← q r"i:num < n") THEN ASM_SIMP_TAC []])

  let FREE_BASIS_INTEGER_RING_SPAN_COPRIME ← prove
    r"!r:A ring n w g C p.
        free_basis (integer_ring,r) (ring_of_int r) n w /\
        (!i. i < n
             ==> g i = ring_sum r {j | j < n}
                         (\j. ring_mul r (ring_of_int r (C i j)) (w j))) /\
        prime p
        ==> (ring_setadd r
               {ring_sum r {i | i < n}
                  (\i. ring_mul r (ring_of_int r (c i)) (g i)) |
                c IN (:num->int)}
               (ideal_generated r {ring_of_num r p}) =
             ring_carrier r <=>
             ~(&p divides ring_det integer_ring {i | i < n} C))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN ABBREV_TAC (← q r"psi = \z:num->int. ring_sum r {i | i < n}
            (\i. ring_mul r (ring_of_int r (z i)) ((w:num->A) i))") THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"psi:(num->int)->A")] FREE_BASIS_INTEGER_RING_LINCOMB) THEN ANTS_TAC THENL [EXPAND_TAC "psi" THEN ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "car") (CONJUNCTS_THEN2 (LABEL_TAC "onto") (CONJUNCTS_THEN2 (LABEL_TAC "inj") (CONJUNCTS_THEN2 (LABEL_TAC "add") (CONJUNCTS_THEN2 (LABEL_TAC "mul") (MP_TAC o (SPECL [(← q r"g:num->A"), (← q r"C:num->num->int")]))))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN MP_TAC (← ISPECL [(← q r"{i:num | i < n}"), (← q r"\i j. (C:num->num->int) j i"), (← q r"p:num")] INT_MATRIX_SURJECTIVE_MOD_PRIME) THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"{i:num | i < n}"), (← q r"C:num->num->int")] RING_DET_TRANSP) THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [IN_ELIM_THM] THEN ABBREV_TAC (← q r"M = {(psi:(num->int)->A) (\i. isum {j | j < n} (\j. C j i * c j)) |
         c IN (:num->int)}") THEN SUBGOAL_THEN (← q r"ring_setadd r M (ideal_generated r {ring_of_num r p}) SUBSET
    ring_carrier (r:A ring)") (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM SUBSET_ANTISYM_EQ), th])) THENL [MATCH_MP_TAC RING_SETADD THEN REWRITE_TAC [IDEAL_GENERATED_SUBSET] THEN EXPAND_TAC "M" THEN REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN USE_THEN "car" (fun th => REWRITE_TAC [th]), ALL_TAC] THEN SIMP_TAC [IDEAL_GENERATED_SING_ALT, RING_OF_NUM] THEN EXPAND_TAC "M" THEN REWRITE_TAC [SUBSET, ring_setadd, IN_ELIM_THM, IN_UNIV] THEN EQ_TAC THENL [DISCH_TAC THEN X_GEN_TAC (← q r"z:num->int") THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"(psi:(num->int)->A) z"))) THEN USE_THEN "car" (fun th => REWRITE_TAC [th]) THEN REWRITE_TAC [LEFT_AND_EXISTS_THM, RIGHT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"y:A"), (← q r"c:num->int"), (← q r"u:A")] THEN STRIP_TAC THEN USE_THEN "onto" (MP_TAC o (SPEC (← q r"u:A"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"v:num->int") STRIP_ASSUME_TAC) THEN MAP_EVERY EXISTS_TAC [(← q r"c:num->int"), (← q r"v:num->int")] THEN USE_THEN "inj" (MP_TAC o (SPECL [(← q r"z:num->int"), (← q r"\i. isum {j | j < n} (\j. (C:num->num->int) j i * c j) +
           &p * (v:num->int) i")])) THEN REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN USE_THEN "add" (fun th => tactic_of do pure (REWRITE_TAC [(← BETA_RULE (← SPECL [(← q r"\i. isum {j | j < n} (\j. (C:num->num->int) j i * c j)"), (← q r"\i. &p * (v:num->int) i")] th))])) THEN USE_THEN "mul" (fun th => REWRITE_TAC [th]) THEN ASM_REWRITE_TAC [RING_OF_INT_OF_NUM], DISCH_TAC THEN X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN USE_THEN "onto" (MP_TAC o (SPEC (← q r"a:A"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"z:num->int") (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM))) THEN FIRST_X_ASSUM ((X_CHOOSE_THEN (← q r"c:num->int") (X_CHOOSE_TAC (← q r"y:num->int"))) o (SPEC (← q r"z:num->int"))) THEN MAP_EVERY EXISTS_TAC [(← q r"(psi:(num->int)->A) (\i. isum {j | j < n} (\j:num. C j i * c j))"), (← q r"ring_mul r (ring_of_num r p) ((psi:(num->int)->A) y)")] THEN REPEAT CONJ_TAC THENL [EXISTS_TAC (← q r"c:num->int") THEN REFL_TAC, EXISTS_TAC (← q r"(psi:(num->int)->A) y") THEN USE_THEN "car" (fun th => REWRITE_TAC [th]), REWRITE_TAC [(← GSYM RING_OF_INT_OF_NUM)] THEN USE_THEN "mul" (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM th)])) THEN USE_THEN "add" (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM th)])) THEN USE_THEN "inj" (fun th => REWRITE_TAC [th]) THEN FIRST_ASSUM ACCEPT_TAC]])

  let NUMBER_FIELD_DISCRIMINANT_CHANGE_OF_BASIS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ r /\ (r ==> q) ==> p /\ q /\ r")
    prove
      r"!k:A ring n g.
          number_field k /\
          free_basis (subfield_generated k {ring_0 k},k) I n g /\
          (!i. i < n ==> g i IN ring_carrier(ring_of_integers k))
          ==> ?w C. free_basis (integer_ring,ring_of_integers k) (ring_of_int k)
                      n w /\
                    (!i. i < n
                         ==> g i = ring_sum (ring_of_integers k) {j | j < n}
                                     (\j. ring_mul k (ring_of_int k (C i j))
                                                     (w j))) /\
                    ~(ring_det integer_ring {i | i < n} C = &0) /\
                    basis_discriminant (subfield_generated k {ring_0 k},k)
                                           I n g =
                    ring_of_int k (ring_det integer_ring {i | i < n} C pow 2 *
                                   number_field_discriminant k)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM ((X_CHOOSE_TAC (← q r"w:num->A")) o (MATCH_MP RING_OF_INTEGERS_FREE)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"g:num->A")] NUMBER_FIELD_FREE_BASIS_DEGREE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST_ALL_TAC o SYM) THEN MAP_EVERY EXISTS_TAC [(← q r"w:num->A"), (← q r"\i j. basis_coordinates (integer_ring,ring_of_integers k) (ring_of_int k)
               n w ((g:num->A) i) j")] THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"ring_of_int k:int->A"), (← q r"integer_ring"), (← q r"ring_of_integers k:A ring"), (← q r"n:num"), (← q r"w:num->A")] FREE_BASIS_IN_CARRIER) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"!i. i < n
          ==> (g:num->A) i =
              ring_sum (ring_of_integers k) {j | j < n}
                (\j. ring_mul k (ring_of_int k
                       (basis_coordinates (integer_ring,ring_of_integers k)
                          (ring_of_int k) n w (g i) j)) (w j))") (LABEL_TAC "gO") THENL [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MP_TAC (← ISPECL [(← q r"ring_of_int k:int->A"), (← q r"integer_ring"), (← q r"ring_of_integers k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"(g:num->A) i")] BASIS_COORDINATES_EXPAND) THEN ASM_SIMP_TAC [RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. i < n
          ==> (g:num->A) i =
              ring_sum k {j | j < n}
                (\j. ring_mul k (ring_of_int k
                       (basis_coordinates (integer_ring,ring_of_integers k)
                          (ring_of_int k) n w (g i) j)) (w j))") (LABEL_TAC "gk") THENL [REPEAT STRIP_TAC THEN USE_THEN "gO" (fun th => tactic_of do pure (GEN_REWRITE_TAC LAND_CONV [(← MATCH_MP th (← ASSUME (← q r"i:num < n")))])) THEN MATCH_MP_TAC RING_SUM_RING_OF_INTEGERS THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring")] RING_MUL) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_OF_INT_IN_RING_OF_INTEGERS], ALL_TAC] THEN MATCH_MP_TAC r1 THEN REPEAT CONJ_TAC THENL [USE_THEN "gO" ACCEPT_TAC, MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k}:A ring"), (← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"g:num->A"), (← q r"\i j. ring_of_int k
                            (basis_coordinates (integer_ring,ring_of_integers k)
                               (ring_of_int k) n w ((g:num->A) i) j):A")] BASIS_DISCRIMINANT_CHANGE_OF_BASIS) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A")] NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A")] RING_OF_INTEGERS_FREE_BASIS_FIELD) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT2) THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION, I_THM, RING_OF_INT_IN_SUBFIELD_GENERATED], DISCH_THEN SUBST1_TAC] THEN MP_TAC (← ISPEC (← q r"subfield_generated k {ring_0 k}:A ring") RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN REWRITE_TAC [RING_OF_INT_SUBFIELD_GENERATED] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"subfield_generated k {ring_0 k}:A ring"), (← q r"ring_of_int k:int->A"), (← q r"{i:num | i < n}"), (← q r"\i j. basis_coordinates (integer_ring,ring_of_integers k)
                 (ring_of_int k) n w ((g:num->A) i) j")] RING_DET_HOMOMORPHISM) THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT, INTEGER_RING, IN_UNIV] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [RING_OF_INT_MUL, RING_OF_INT_POW, SUBFIELD_GENERATED, RING_POW_SUBFIELD_GENERATED], REMOVE_THEN "gO" (fun (_ : thm) => ALL_TAC) THEN REMOVE_THEN "gk" (fun (_ : thm) => ALL_TAC) THEN DISCH_THEN (fun th => tactic_of do pure (DISCH_THEN (fun th' => tactic_of do pure (MP_TAC (← REWRITE_RULE [th'] th))))) THEN CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC [INT_MUL_LZERO, RING_OF_INT_0] THEN SUBGOAL_THEN (← q r"~(n = 0)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"g:num->A")] NUMBER_FIELD_FREE_BASIS_DEGREE) THEN FIRST_ASSUM (MP_TAC o (MATCH_MP NUMBER_FIELD_DEGREE_POS)) THEN ASM_REWRITE_TAC [] THEN ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k}:A ring"), (← q r"k:A ring"), (← q r"n:num"), (← q r"g:num->A")] BASIS_DISCRIMINANT_NONZERO) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [number_field])) THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, (← CONJUNCT1 (← CONJUNCT2 SUBFIELD_GENERATED)), (← GSYM RING_OF_INT_OF_NUM), RING_OF_INT_SUBFIELD_GENERATED, RING_OF_INT_EQ_0_CHAR_0, INT_OF_NUM_EQ]])

  let NUMBER_FIELD_INDEX_DETERMINANT ← prove
    r"!k:A ring n g.
        number_field k /\
        free_basis (subfield_generated k {ring_0 k},k) I n g /\
        (!i. i < n ==> g i IN ring_carrier(ring_of_integers k))
        ==> ?d. ~(d = &0) /\
                basis_discriminant (subfield_generated k {ring_0 k},k) I
                                       n g =
                ring_of_int k (d pow 2 * number_field_discriminant k) /\
                {ring_coset (ring_of_integers k)
                   {ring_sum k {i | i < n}
                      (\i. ring_mul k (ring_of_int k (c i)) (g i)) |
                    c IN (:num->int)} x |
                 x | x IN ring_carrier(ring_of_integers k)}
                HAS_SIZE num_of_int(abs d) /\
                !p. prime p
                    ==> (ring_setadd (ring_of_integers k)
                           {ring_sum k {i | i < n}
                              (\i. ring_mul k (ring_of_int k (c i)) (g i)) |
                            c IN (:num->int)}
                           (ideal_generated (ring_of_integers k)
                              {ring_of_num k p}) =
                         ring_carrier(ring_of_integers k) <=>
                         ~(&p divides d))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"g:num->A")] NUMBER_FIELD_DISCRIMINANT_CHANGE_OF_BASIS) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"w:num->A"), (← q r"C:num->num->int")] THEN STRIP_TAC THEN EXISTS_TAC (← q r"ring_det integer_ring {i | i < n} (C:num->num->int)") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"!c. ring_sum k {i | i < n}
          (\i. ring_mul k (ring_of_int k (c i)) ((g:num->A) i)) =
        ring_sum (ring_of_integers k) {i | i < n}
          (\i. ring_mul k (ring_of_int k (c i)) (g i))") (fun th => REWRITE_TAC [th]) THENL [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_RING_OF_INTEGERS THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_MUL) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC [RING_OF_INT_IN_RING_OF_INTEGERS] THEN FIRST_X_ASSUM (MATCH_MP_TAC o (checkM (fun z1 => (do let z2 ← (do let z3 ← (pure z1); pure (concl z3)); pure (is_forall z2))))) THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"g:num->A"), (← q r"C:num->num->int")] FREE_BASIS_INTEGER_RING_SPAN_INDEX) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"g:num->A"), (← q r"C:num->num->int")] FREE_BASIS_INTEGER_RING_SPAN_COPRIME) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN SIMP_TAC [])

  let NUMBER_FIELD_DISCRIMINANT_INDEX ← prove
    r"!k:A ring n g M.
        number_field k /\
        free_basis (subfield_generated k {ring_0 k},k) I n g /\
        (!i. i < n ==> g i IN ring_carrier(ring_of_integers k)) /\
        M = {ring_sum k {i | i < n}
                     (\i. ring_mul k (ring_of_int k (c i)) (g i)) |
             c IN (:num->int)}
        ==> ?N. {ring_coset (ring_of_integers k) M x |
                 x | x IN ring_carrier(ring_of_integers k)} HAS_SIZE N /\
                basis_discriminant (subfield_generated k {ring_0 k},k) I
                                       n g =
                ring_of_int k (&N pow 2 * number_field_discriminant k)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"g:num->A")] NUMBER_FIELD_INDEX_DETERMINANT) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"d:int") THEN STRIP_TAC THEN EXISTS_TAC (← q r"num_of_int(abs d)") THEN ASM_SIMP_TAC [INT_OF_NUM_OF_INT, INT_ABS_POS, INT_POW2_ABS])

  -- @@RETURN BEGIN
  return { number_field_discriminant, NUMBER_FIELD_DISCRIMINANT_BASIS,
           NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD, NUMBER_FIELD_DISCRIMINANT_NONZERO,
           FREE_BASIS_INTEGER_RING_LINCOMB, INT_MATRIX_SURJECTIVE_MOD_PRIME,
           FREE_BASIS_INTEGER_RING_SPAN_INDEX, FREE_BASIS_INTEGER_RING_SPAN_COPRIME,
           NUMBER_FIELD_DISCRIMINANT_CHANGE_OF_BASIS, NUMBER_FIELD_INDEX_DETERMINANT,
           NUMBER_FIELD_DISCRIMINANT_INDEX }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- discriminant.ml phrases from line 755 to 1074                          -/
/- ---------------------------------------------------------------------- -/

structure Discriminant02 where
  -- @@FIELDS
  NUMBER_FIELD_INTEGRAL_BASIS_DISCRIMINANT : thm
  NUMBER_FIELD_INDEX_COPRIME : thm
  NUMBER_FIELD_INDEX_COPRIME_DISCRIMINANT : thm
  RING_OF_INTEGERS_IDEAL_INT_LINCOMB : thm
  NUMBER_FIELD_IDEAL_INTEGRAL_BASIS : thm
  NUMBER_FIELD_IDEAL_DISCRIMINANT : thm
  NUMBER_FIELD_IDEAL_INTEGRAL_BASIS_DISCRIMINANT : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDiscriminant02 [HolBase] (D : DiscriminantDeps) (BDiscriminant01 : Discriminant01) :
    ExceptT String IO Discriminant02 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, INTEGER_RULE, INT_RING, RING_RULE, SET_RULE, SET_TAC, .. } := D
  let { ARITH_EQ, CARD_IMAGE_EQ_INJ, COND_RAND, COND_RATOR, CONTRAPOS_THM, EQ_TRANS,
        EXP_MONO_EQ, EXTENSION, FIELD_SUBFIELD_GENERATED, FINITE_NUMSEG_LT,
        FORALL_IN_GSPEC, FREE_BASIS_INTEGER_RING_COORDINATES,
        FREE_BASIS_INTEGER_RING_SUBRING_GENERATED, FREE_BASIS_SCALE, HAS_SIZE,
        HAS_SIZE_0, HAS_SIZE_CLAUSES, IMAGE_EQ, IMAGE_o, INT_ABS_POS, INT_DIVIDES_RABS,
        INT_EQ_MUL_RCANCEL, INT_OF_NUM_EQ, INT_OF_NUM_OF_INT, INT_OF_NUM_POW,
        INT_POW_EQ_1_IMP, IN_ELIM_THM, IN_RING_IDEAL_LMUL, IN_RING_IDEAL_RMUL,
        IN_RING_IDEAL_SUB, IN_RING_IDEAL_SUM, IN_SING, IN_UNIV, I_THM,
        LEFT_IMP_EXISTS_THM, NOT_IN_EMPTY, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_INT_LINCOMB_SANDWICH, ONE, QUOTIENT_RING, RING_0, RING_ADD_RZERO,
        RING_COSET_0, RING_COSET_EQ_IDEAL, RING_COSET_SETADD,
        RING_HOMOMORPHISM_SUBFIELD_INCLUSION, RING_IDEAL_IMP_SUBSET, RING_MUL,
        RING_MUL_LID, RING_MUL_LZERO, RING_OF_INT, RING_OF_INTEGERS,
        RING_OF_INTEGERS_FINITE_QUOTIENT, RING_OF_INTEGERS_FREE,
        RING_OF_INTEGERS_FREE_BASIS_FIELD, RING_OF_INTEGERS_IDEAL_INTEGER,
        RING_OF_INTEGERS_RING_OF_INT_MUL, RING_OF_INTEGERS_SUBRING,
        RING_OF_INTEGERS_SUBSET, RING_OF_INT_0, RING_OF_INT_1, RING_OF_INT_EQ_0_CHAR_0,
        RING_OF_INT_EQ_CHAR_0, RING_OF_INT_IN_RING_OF_INTEGERS,
        RING_OF_INT_IN_SUBFIELD_GENERATED, RING_SETADD_ASSOC, RING_SETADD_LSUBSET,
        RING_SUM, RING_SUM_0, RING_SUM_DELTA, RING_SUM_EQ, RING_SUM_EQ_0,
        RING_SUM_LMUL, RING_SUM_RING_OF_INTEGERS, SIMPLE_IMAGE, SING_SUBSET,
        SUBFIELD_GENERATED, SUBSET, SUBSET_ANTISYM, SUBSET_TRANS, UNWIND_THM2,
        free_basis, ideal_norm, num_divides, number_field, o_THM, ring_coset, .. } := D.core1
  let { NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD, NUMBER_FIELD_DISCRIMINANT_INDEX,
        NUMBER_FIELD_DISCRIMINANT_NONZERO, NUMBER_FIELD_INDEX_DETERMINANT, .. } := BDiscriminant01
  -- @@SCOPE END

  let NUMBER_FIELD_INTEGRAL_BASIS_DISCRIMINANT ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"ring_0 r:A"
    let q2 ← q r"M:A->bool"
    let q3 ← q r"r:A ring"
    let v4 ← ISPECL [q3, q2] RING_COSET_0
    let q5 ← q r"ring_coset r M (x:A) = M"
    let q6 ← q r"x:A"
    let q7 ← q r"y:A"
    let q8 ← q r"ring_coset r M (y:A)"
    let q9 ← q r"y:A"
    let q10 ← q r"!y:A. y IN ring_carrier r ==> ring_coset r M y = a"
    let q11 ← q r"a:A->bool"
    let p12 ← prove r"!r M:A->bool.
        M SUBSET ring_carrier r /\ ring_0 r IN M /\
        {ring_coset r M x | x | x IN ring_carrier r} HAS_SIZE 1
        ==> ring_carrier r SUBSET M" (REPEAT GEN_TAC THEN REWRITE_TAC [ONE, HAS_SIZE_CLAUSES, HAS_SIZE_0, UNWIND_THM2, NOT_IN_EMPTY] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC q11))) THEN SUBGOAL_THEN q10 ASSUME_TAC THENL [X_GEN_TAC q9 THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC q8) o (GEN_REWRITE_RULE id [EXTENSION]))) THEN REWRITE_TAC [IN_ELIM_THM, IN_SING] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN EXISTS_TAC q7 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN REWRITE_TAC [SUBSET] THEN X_GEN_TAC q6 THEN DISCH_TAC THEN SUBGOAL_THEN q5 MP_TAC THENL [MP_TAC v4 THEN ASM_SIMP_TAC [RING_0], DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [ring_coset, IN_ELIM_THM] THEN EXISTS_TAC q1 THEN ASM_SIMP_TAC [RING_ADD_RZERO]])
    let lemma := p12
    let v13 ← CONJUNCT2 SUBFIELD_GENERATED
    let v14 ← CONJUNCT1 v13
    let q15 ← q r"\i. ring_of_int k ((c:num->int) i):A"
    let q16 ← q r"c:num->int"
    let q17 ← q r"x:A"
    let q18 ← q r"x:A"
    let q19 ← q r"g:num->A"
    let q20 ← q r"n:num"
    let q21 ← q r"ring_carrier(ring_of_integers k):A->bool"
    let q22 ← q r"k:A ring"
    let v23 ← ISPECL [q22, q21, q20, q19] FREE_BASIS_INTEGER_RING_SUBRING_GENERATED
    let q24 ← q r"k:A ring"
    let v25 ← ISPEC q24 RING_OF_INTEGERS_SUBSET
    let q26 ← q r"ring_sum (k:A ring) {i:num | i < n} (\i. ring_0 k)"
    let q27 ← q r"\i:num. &0:int"
    let q28 ← q r"{ring_sum k {i | i < n}
                     (\i. ring_mul k (ring_of_int k (c i)) ((g:num->A) i)) |
                   c IN (:num->int)}"
    let q29 ← q r"ring_of_integers k:A ring"
    let v30 ← ISPECL [q29, q28] lemma
    let q31 ← q r"ring_of_integers k:A ring"
    let v32 ← ISPEC q31 RING_MUL
    let q33 ← q r"\i. ring_mul k (ring_of_int k ((c:num->int) i)) ((g:num->A) i)"
    let q34 ← q r"{i:num | i < n}"
    let q35 ← q r"k:A ring"
    let v36 ← ISPECL [q35, q34, q33] RING_SUM_RING_OF_INTEGERS
    let q37 ← q r"!c. ring_sum k {i | i < n}
          (\i. ring_mul k (ring_of_int k (c i)) ((g:num->A) i)) IN
        ring_carrier(ring_of_integers k)"
    let v38 ← GSYM RING_OF_INT_EQ_CHAR_0
    let q39 ← q r"number_field_discriminant (k:A ring)"
    let q40 ← q r"!d e:int. e = d pow 2 * e /\ ~(e = &0) ==> d pow 2 = &1"
    let r41 ← INT_RING q40
    let q42 ← q r"2"
    let v43 ← GSYM INT_OF_NUM_EQ
    let q44 ← q r"num_of_int(abs(d:int)) = 1"
    let q45 ← q r"d:int"
    let q46 ← q r"g:num->A"
    let q47 ← q r"n:num"
    let q48 ← q r"k:A ring"
    let v49 ← ISPECL [q48, q47, q46] NUMBER_FIELD_INDEX_DETERMINANT
    prove
      r"!k:A ring n g.
          number_field k /\
          free_basis (subfield_generated k {ring_0 k},k) I n g /\
          (!i. i < n ==> g i IN ring_carrier(ring_of_integers k))
          ==> (free_basis (integer_ring,ring_of_integers k) (ring_of_int k)
                          n g <=>
               basis_discriminant (subfield_generated k {ring_0 k},k) I n g =
               ring_of_int k (number_field_discriminant k))"
      (REPEAT STRIP_TAC THEN EQ_TAC THENL [DISCH_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD THEN ASM_REWRITE_TAC [], DISCH_TAC] THEN MP_TAC v49 THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC q45 THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [number_field])) THEN SUBGOAL_THEN q44 SUBST_ALL_TAC THENL [REWRITE_TAC [v43] THEN SIMP_TAC [INT_OF_NUM_OF_INT, INT_ABS_POS] THEN MATCH_MP_TAC INT_POW_EQ_1_IMP THEN EXISTS_TAC q42 THEN REWRITE_TAC [ARITH_EQ] THEN MATCH_MP_TAC r41 THEN EXISTS_TAC q39 THEN ASM_SIMP_TAC [NUMBER_FIELD_DISCRIMINANT_NONZERO, v38], ALL_TAC] THEN SUBGOAL_THEN q37 ASSUME_TAC THENL [GEN_TAC THEN MP_TAC v36 THEN ANTS_TAC THENL [REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MP_TAC v32 THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_OF_INT_IN_RING_OF_INTEGERS], DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [RING_SUM]], ALL_TAC] THEN MP_TAC v30 THEN ASM_REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN ANTS_TAC THENL [REWRITE_TAC [IN_ELIM_THM, IN_UNIV, RING_OF_INTEGERS] THEN EXISTS_TAC q27 THEN BETA_TAC THEN REWRITE_TAC [RING_OF_INT_0] THEN CONV_TAC SYM_CONV THEN TRANS_TAC EQ_TRANS q26 THEN CONJ_TAC THENL [ALL_TAC, REWRITE_TAC [RING_SUM_0]] THEN MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL_LZERO THEN MP_TAC v25 THEN ASM SET_TAC [], DISCH_TAC] THEN MP_TAC v23 THEN REWRITE_TAC [RING_OF_INTEGERS_SUBRING] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [X_GEN_TAC q18 THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC q17)) THEN ASM_REWRITE_TAC [IN_ELIM_THM, IN_UNIV], X_GEN_TAC q16 THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o (BETA_RULE o ((SPEC q15) o (CONJUNCT2 o (CONJUNCT2 o (GEN_REWRITE_RULE id [free_basis])))))) THEN ASM_SIMP_TAC [I_THM, RING_OF_INT_IN_SUBFIELD_GENERATED, v14, RING_OF_INT_EQ_0_CHAR_0]])

  let NUMBER_FIELD_INDEX_COPRIME ← prove
    r"!k:A ring n g M p N.
        number_field k /\ prime p /\
        free_basis (subfield_generated k {ring_0 k},k) I n g /\
        (!i. i < n ==> g i IN ring_carrier(ring_of_integers k)) /\
        M = {ring_sum k {i | i < n}
                     (\i. ring_mul k (ring_of_int k (c i)) (g i)) |
             c IN (:num->int)} /\
        {ring_coset (ring_of_integers k) M x |
         x | x IN ring_carrier(ring_of_integers k)} HAS_SIZE N
        ==> (ring_setadd (ring_of_integers k) M
               (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
             ring_carrier(ring_of_integers k) <=>
             ~(p divides N))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"g:num->A")] NUMBER_FIELD_INDEX_DETERMINANT) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"d:int") THEN STRIP_TAC THEN ASM_SIMP_TAC [] THEN SUBGOAL_THEN (← q r"N = num_of_int(abs d)") SUBST1_TAC THENL [ASM_MESON_TAC [HAS_SIZE], SIMP_TAC [num_divides, INT_OF_NUM_OF_INT, INT_ABS_POS, INT_DIVIDES_RABS]])

  let NUMBER_FIELD_INDEX_COPRIME_DISCRIMINANT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← INTEGER_RULE (← q r"!p d e:int. p divides d ==> p pow 2 divides d pow 2 * e")
    prove
      r"!k:A ring n g M p D.
          number_field k /\ prime p /\
          free_basis (subfield_generated k {ring_0 k},k) I n g /\
          (!i. i < n ==> g i IN ring_carrier(ring_of_integers k)) /\
          M = {ring_sum k {i | i < n}
                       (\i. ring_mul k (ring_of_int k (c i)) (g i)) |
               c IN (:num->int)} /\
          basis_discriminant (subfield_generated k {ring_0 k},k) I n g =
          ring_of_int k D /\
          ~(&p pow 2 divides D)
          ==> ring_setadd (ring_of_integers k) M
                (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
              ring_carrier(ring_of_integers k)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"g:num->A")] NUMBER_FIELD_INDEX_DETERMINANT) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"d:int") THEN STRIP_TAC THEN ASM_SIMP_TAC [] THEN UNDISCH_TAC (← q r"~(&p pow 2 divides D)") THEN SUBGOAL_THEN (← q r"D = d pow 2 * number_field_discriminant(k:A ring)") SUBST1_TAC THENL [FIRST_ASSUM (MP_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM (← MATCH_MP RING_OF_INT_EQ_CHAR_0 th))])) THEN ASM_MESON_TAC [], REWRITE_TAC [CONTRAPOS_THM] THEN MATCH_ACCEPT_TAC r1])

  let RING_OF_INTEGERS_IDEAL_INT_LINCOMB ← prove
    r"!k:A ring j s (c:K->int) w.
        ring_ideal (ring_of_integers k) j /\ (!i. i IN s ==> w i IN j)
        ==> ring_sum k s (\i. ring_mul k (ring_of_int k (c i)) (w i)) IN j"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_IDEAL_IMP_SUBSET)) THEN SUBGOAL_THEN (← q r"!i. i IN s
        ==> ring_mul k (ring_of_int k ((c:K->int) i)) ((w:K->A) i) IN j") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"j:A->bool"), (← q r"ring_of_int k ((c:K->int) i):A"), (← q r"(w:K->A) i")] IN_RING_IDEAL_LMUL) THEN ASM_SIMP_TAC [RING_OF_INTEGERS, RING_OF_INT_IN_RING_OF_INTEGERS], ALL_TAC] THEN wPart lhand (rand o rand) RING_SUM_RING_OF_INTEGERS THEN ANTS_TAC THENL [ASM SET_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC IN_RING_IDEAL_SUM THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_IDEAL_INTEGRAL_BASIS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul (k:A ring) a (ring_mul k b c) =
        ring_mul k b (ring_mul k a c)")
    prove
      r"!k j:A->bool.
          number_field k /\ ring_ideal (ring_of_integers k) j /\
          ~(j = {ring_0 k})
          ==> ?w. free_basis (subfield_generated k {ring_0 k},k) I
                    (extension_degree (subfield_generated k {ring_0 k},k) I) w /\
                  {ring_sum k
                     {i | i < extension_degree
                                (subfield_generated k {ring_0 k},k) I}
                     (\i. ring_mul k (ring_of_int k (c i)) (w i)) |
                   c IN (:num->int)} = j"
      (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"n = extension_degree (subfield_generated k {ring_0 k},k:A ring) I") THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_IDEAL_IMP_SUBSET)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"j:A->bool")] RING_OF_INTEGERS_IDEAL_INTEGER) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"m:int") THEN STRIP_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_FREE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"v:num->A")) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"v:num->A")] RING_OF_INTEGERS_FREE_BASIS_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"n:num"), (← q r"v:num->A")] FREE_BASIS_INTEGER_RING_COORDINATES) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS, IN_ELIM_THM] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "coord") ASSUME_TAC))) THEN SUBGOAL_THEN (← q r"!i. i < n ==> (v:num->A) i IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [ASM_MESON_TAC [free_basis], ALL_TAC] THEN SUBGOAL_THEN (← q r"!z. ring_sum k {i | i < n} (\i. ring_mul k (ring_of_int k (z i)) (v i)) =
          ring_sum (ring_of_integers k) {i | i < n}
            (\i. ring_mul k (ring_of_int k (z i)) ((v:num->A) i))") ASSUME_TAC THENL [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_RING_OF_INTEGERS THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_OF_INTEGERS_RING_OF_INT_MUL THEN ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"\i. ring_mul k (ring_of_int k m) ((v:num->A) i)"), (← q r"j:A->bool"), (← q r"m:int")] NUMBER_FIELD_INT_LINCOMB_SANDWICH) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"n:num"), (← q r"v:num->A"), (← q r"\i:num. ring_of_int k m:A")] FREE_BASIS_SCALE) THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, I_THM] THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC [RING_OF_INT_IN_SUBFIELD_GENERATED, SUBFIELD_GENERATED] THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN ASM_SIMP_TAC [RING_OF_INT_EQ_0_CHAR_0], MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC (← q r"ring_carrier(ring_of_integers k:A ring)") THEN ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBSET], REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"j:A->bool"), (← q r"x:A"), (← q r"y:A")] IN_RING_IDEAL_SUB) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], X_GEN_TAC (← q r"c:num->int") THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"j:A->bool"), (← q r"{i:num | i < n}"), (← q r"c:num->int"), (← q r"\i. ring_mul k (ring_of_int k m) ((v:num->A) i)")] RING_OF_INTEGERS_IDEAL_INT_LINCOMB) THEN REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"j:A->bool"), (← q r"ring_of_int k m:A"), (← q r"(v:num->A) i")] IN_RING_IDEAL_RMUL) THEN ASM_SIMP_TAC [RING_OF_INTEGERS], X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN USE_THEN "coord" (MP_TAC o (SPEC (← q r"x:A"))) THEN ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"z:num->int") (SUBST1_TAC o (SYM o CONJUNCT2))) THEN EXISTS_TAC (← q r"z:num->int") THEN FIRST_X_ASSUM ((fun th => tactic_of do pure (REWRITE_TAC [(← GSYM th)])) o (checkM (fun th => (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); pure (is_forall z2)) then (do let z4 ← (do pure (Prod.snd (← (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); liftExcept (dest_forall z5))))); pure (is_eq z4)) else pure false)))) THEN SUBGOAL_THEN (← q r"!i. i < n ==> (v:num->A) i IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [(← GSYM RING_SUM_LMUL), FINITE_NUMSEG_LT, IN_ELIM_THM, RING_OF_INT, RING_MUL] THEN MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [RING_OF_INT]], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"w:num->A") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"w:num->A") THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_UNIV] THEN X_GEN_TAC (← q r"x:A") THEN EQ_TAC THENL [DISCH_THEN (X_CHOOSE_THEN (← q r"c:num->int") SUBST1_TAC) THEN MATCH_MP_TAC RING_OF_INTEGERS_IDEAL_INT_LINCOMB THEN ASM_SIMP_TAC [IN_ELIM_THM], ASM_MESON_TAC []])

  let NUMBER_FIELD_IDEAL_DISCRIMINANT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!x:A s t. x IN s /\ s SUBSET t ==> x IN t")
    prove
      r"!k j:A->bool n w.
          number_field k /\ ring_ideal (ring_of_integers k) j /\
          free_basis (subfield_generated k {ring_0 k},k) I n w /\
          {ring_sum k {i | i < n} (\i. ring_mul k (ring_of_int k (c i)) (w i)) |
           c IN (:num->int)} = j
          ==> basis_discriminant (subfield_generated k {ring_0 k},k) I n w =
              ring_of_int k (&(ideal_norm (ring_of_integers k) j) pow 2 *
                             number_field_discriminant k)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_IDEAL_IMP_SUBSET)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [free_basis]))) THEN SUBGOAL_THEN (← q r"!i. i < n ==> (w:num->A) i IN j") ASSUME_TAC THENL [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z5 ← (q r"j:A->bool"); let z4 ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); liftExcept (rand z2)); pure (z4 == z5)))))) THEN REWRITE_TAC [IN_ELIM_THM, IN_UNIV] THEN EXISTS_TAC (← q r"\m:num. if m = i then &1 else &0:int") THEN REWRITE_TAC [COND_RAND, COND_RATOR, RING_OF_INT_1, RING_OF_INT_0] THEN TRANS_TAC EQ_TRANS (← q r"ring_sum k {m | m < n} (\m. if m = i then (w:num->A) i else ring_0 k)") THEN CONJ_TAC THENL [ASM_SIMP_TAC [RING_SUM_DELTA, IN_ELIM_THM], MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"m:num") THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [RING_MUL_LID, RING_MUL_LZERO]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"j:A->bool")] NUMBER_FIELD_DISCRIMINANT_INDEX) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN MATCH_MP_TAC r1 THEN EXISTS_TAC (← q r"j:A->bool") THEN ASM_SIMP_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"N:num") (CONJUNCTS_THEN2 MP_TAC SUBST1_TAC)) THEN ASM_SIMP_TAC [ideal_norm, QUOTIENT_RING, HAS_SIZE])

  let NUMBER_FIELD_IDEAL_INTEGRAL_BASIS_DISCRIMINANT ← prove
    r"!k j:A->bool n w.
        number_field k /\ ring_ideal (ring_of_integers k) j /\
        ~(j = {ring_0 k}) /\
        free_basis (subfield_generated k {ring_0 k},k) I n w /\
        (!i. i < n ==> w i IN j)
        ==> ({ring_sum k {i | i < n}
                (\i. ring_mul k (ring_of_int k (c i)) (w i)) |
              c IN (:num->int)} = j <=>
             basis_discriminant (subfield_generated k {ring_0 k},k) I n w =
             ring_of_int k (&(ideal_norm (ring_of_integers k) j) pow 2 *
                            number_field_discriminant k))"
    (REPEAT STRIP_TAC THEN EQ_TAC THENL [DISCH_TAC THEN MATCH_MP_TAC NUMBER_FIELD_IDEAL_DISCRIMINANT THEN ASM_REWRITE_TAC [], DISCH_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_IDEAL_IMP_SUBSET)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN ABBREV_TAC (← q r"M = {ring_sum k {i | i < n}
           (\i. ring_mul k (ring_of_int k (c i)) ((w:num->A) i)) |
         c IN (:num->int)}") THEN SUBGOAL_THEN (← q r"(M:A->bool) SUBSET j") ASSUME_TAC THENL [EXPAND_TAC "M" THEN REWRITE_TAC [SUBSET, FORALL_IN_GSPEC, IN_UNIV] THEN X_GEN_TAC (← q r"c:num->int") THEN MATCH_MP_TAC RING_OF_INTEGERS_IDEAL_INT_LINCOMB THEN ASM_SIMP_TAC [IN_ELIM_THM], ALL_TAC] THEN SUBGOAL_THEN (← q r"(M:A->bool) SUBSET ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_0 k IN (M:A->bool)") ASSUME_TAC THENL [EXPAND_TAC "M" THEN REWRITE_TAC [IN_ELIM_THM, IN_UNIV] THEN EXISTS_TAC (← q r"\i:num. &0:int") THEN CONV_TAC SYM_CONV THEN REWRITE_TAC [RING_OF_INT_0] THEN MATCH_MP_TAC RING_SUM_EQ_0 THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL_LZERO THEN ASM_MESON_TAC [free_basis], ALL_TAC] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"M:A->bool")] NUMBER_FIELD_DISCRIMINANT_INDEX) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM SET_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"N:num") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN ASM_SIMP_TAC [RING_OF_INT_EQ_CHAR_0, INT_EQ_MUL_RCANCEL, NUMBER_FIELD_DISCRIMINANT_NONZERO, INT_OF_NUM_POW, INT_OF_NUM_EQ, EXP_MONO_EQ, ARITH_EQ] THEN DISCH_THEN (SUBST_ALL_TAC o SYM) THEN SUBGOAL_THEN (← q r"{ring_coset (ring_of_integers k) j x | x | x IN
     ring_carrier(ring_of_integers k)} HAS_SIZE
    ideal_norm (ring_of_integers k) (j:A->bool)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"j:A->bool")] (← CONJUNCT1 QUOTIENT_RING)) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [HAS_SIZE, ideal_norm] THEN MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x. x IN ring_carrier(ring_of_integers k)
        ==> ring_setadd (ring_of_integers k)
              (ring_coset (ring_of_integers k) M x) j =
            ring_coset (ring_of_integers k) j (x:A)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN REWRITE_TAC [RING_COSET_SETADD] THEN wPart lhand (rand o rand) RING_SETADD_ASSOC THEN ASM_REWRITE_TAC [SING_SUBSET] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN MATCH_MP_TAC RING_SETADD_LSUBSET THEN ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"{ring_coset (ring_of_integers k) j x | x | x IN
     ring_carrier(ring_of_integers k)} =
    IMAGE (\s. ring_setadd (ring_of_integers k) s j)
          {ring_coset (ring_of_integers k) M (x:A) | x | x IN
           ring_carrier(ring_of_integers k)}") (LABEL_TAC "img") THENL [REWRITE_TAC [SIMPLE_IMAGE, (← GSYM IMAGE_o)] THEN MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC [o_THM], ALL_TAC] THEN SUBGOAL_THEN (← q r"!s t. s IN {ring_coset (ring_of_integers k) M (x:A) | x | x IN
                ring_carrier(ring_of_integers k)} /\
          t IN {ring_coset (ring_of_integers k) M x | x | x IN
                ring_carrier(ring_of_integers k)} /\
          ring_setadd (ring_of_integers k) s j =
          ring_setadd (ring_of_integers k) t j
          ==> s = t") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"\s. ring_setadd (ring_of_integers k) s (j:A->bool)"), (← q r"{ring_coset (ring_of_integers k) M (x:A) | x | x IN
                     ring_carrier(ring_of_integers k)}")] CARD_IMAGE_EQ_INJ) THEN REWRITE_TAC [] THEN RULE_ASSUM_TAC (REWRITE_RULE [HAS_SIZE]) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REMOVE_THEN "img" (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(y:A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_coset (ring_of_integers k) M (y:A) = M") MP_TAC THENL [TRANS_TAC EQ_TRANS (← q r"ring_coset (ring_of_integers k) M (ring_0 (ring_of_integers k):A)") THEN CONJ_TAC THENL [ALL_TAC, ASM_SIMP_TAC [RING_COSET_0]] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL [EXISTS_TAC (← q r"y:A") THEN ASM_REWRITE_TAC [], EXISTS_TAC (← q r"ring_0 (ring_of_integers k):A") THEN REWRITE_TAC [RING_0], ASM_SIMP_TAC [RING_0] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"j:A->bool"), (← q r"y:A")] RING_COSET_EQ_IDEAL) THEN ASM_SIMP_TAC [RING_COSET_0]], ALL_TAC] THEN DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [(← SYM th)])) THEN REWRITE_TAC [ring_coset, IN_ELIM_THM] THEN EXISTS_TAC (← q r"ring_0 k:A") THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_ADD_RZERO THEN ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_INTEGRAL_BASIS_DISCRIMINANT, NUMBER_FIELD_INDEX_COPRIME,
           NUMBER_FIELD_INDEX_COPRIME_DISCRIMINANT, RING_OF_INTEGERS_IDEAL_INT_LINCOMB,
           NUMBER_FIELD_IDEAL_INTEGRAL_BASIS, NUMBER_FIELD_IDEAL_DISCRIMINANT,
           NUMBER_FIELD_IDEAL_INTEGRAL_BASIS_DISCRIMINANT }
  -- @@RETURN END

end HolANT.Discriminant
