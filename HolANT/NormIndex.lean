/- ========================================================================= -/
/- ANT: The index of a principal ideal in a ring free over Z is the ...    -/
/- ========================================================================= -/
/- File: HolANT/NormIndex.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/norm_index.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antnormindexdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/isum.ml, Library/products.ml, ANT/algmisc.ml, ANT/ideal_arith.ml, ANT/integral.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ring_of_integers.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.NormIndex fills them).

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
import HolANT.IdealArith
import HolANT.Integral
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.IdealNorm
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolANT.RingOfIntegers

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.Algmisc
open HolANT.IdealArith
open HolANT.Integral
open HolANT.Dedekind
open HolANT.DedekindStruct
open HolANT.IdealNorm
open HolANT.Zlattice
open HolANT.Numfield
open HolANT.RingOfIntegers

namespace HolANT.NormIndex

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ALGEBRA_NORM_FREE_BASIS ALGEBRA_TRACE_FREE_BASIS BASIS_COORDINATES
   BASIS_COORDINATES_EXPAND BASIS_COORDINATES_LINCOMB BASIS_COORDINATES_MUL
   BASIS_COORDINATES_UNIQUE DEDEKIND_RING_OF_INTEGERS EQ_SYM_EQ EQ_TRANS
   EXTENSION FINITE_NUMSEG_LT FREE_BASIS_IN_CARRIER
   FREE_BASIS_QUOTIENT_RING_HAS_SIZE FUN_EQ_THM HAS_SIZE IDEAL_GENERATED_EQ_0
   IDEAL_GENERATED_SING_ALT IDEAL_GENERATED_SUBSET IDEAL_NORM_MUL
   IDEAL_NORM_PRIME_IMP_MAXIMAL INTEGER_RING INTEGER_RING_SUM INT_ABS_POS
   INT_COSETS_MATRIX_IMAGE INT_NEG_EQ_0 INT_OF_NUM_EQ INT_OF_NUM_OF_INT
   IN_ELIM_THM IN_IMAGE IN_UNIV ISUM_EQ I_THM LEFT_IMP_EXISTS_THM
   MAXIMAL_IMP_PRIME_IDEAL NUMBER_FIELD_NORM_EQ_0 PRIME_0 PRIME_IDEAL_SING
   RING_0 RING_DET_EQ RING_DET_HOMOMORPHISM
   RING_HOMOMORPHISM_INTEGER_RING_OF_INT RING_HOMOMORPHISM_SUBFIELD_INCLUSION
   RING_HOMOMORPHISM_SUM RING_IDEAL_IDEAL_GENERATED RING_MUL RING_OF_INTEGERS
   RING_OF_INTEGERS_FINITE_QUOTIENT RING_OF_INTEGERS_FREE
   RING_OF_INTEGERS_FREE_BASIS_FIELD RING_OF_INTEGERS_SUBSET RING_OF_INT_0
   RING_OF_INT_EQ_0_CHAR_0 RING_OF_INT_EQ_CHAR_0 RING_OF_INT_IN_RING_OF_INTEGERS
   RING_OF_INT_IN_SUBFIELD_GENERATED RING_OF_INT_NEG RING_OF_INT_OF_NUM
   RING_OF_INT_SUBFIELD_GENERATED RING_SUM RING_SUM_EQ RING_SUM_RING_OF_INTEGERS
   SUBSET ideal_norm int_matrix_image mul_matrix number_field o_THM : thm)
  deriving Inhabited

/-- What norm_index.ml uses from Session besides theorems. -/
structure NormIndexDeps where
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
/- norm_index.ml phrases from line 55 to 387                              -/
/- ---------------------------------------------------------------------- -/

structure NormIndex where
  -- @@FIELDS
  FREE_BASIS_IDEAL_NORM_COORD_MUL : thm
  FREE_BASIS_IDEAL_NORM_IMAGE : thm
  FREE_BASIS_IDEAL_NORM_PRINCIPAL : thm
  MUL_MATRIX_RING_OF_INTEGERS : thm
  NUMBER_FIELD_NORM_INTEGRAL_BASIS : thm
  NUMBER_FIELD_TRACE_INTEGRAL_BASIS : thm
  NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_Q : thm
  NUMBER_FIELD_IDEAL_NORM_MUL_Q : thm
  NUMBER_FIELD_IDEAL_NORM_PRIME_IMP_PRIME : thm
  NUMBER_FIELD_NORM_PRIME_IMP_RING_PRIME : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupNormIndex [HolBase] (D : NormIndexDeps) :
    ExceptT String IO NormIndex := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, INT_ARITH_TAC, TAUT, .. } := D
  let { ALGEBRA_NORM_FREE_BASIS, ALGEBRA_TRACE_FREE_BASIS, BASIS_COORDINATES,
        BASIS_COORDINATES_EXPAND, BASIS_COORDINATES_LINCOMB, BASIS_COORDINATES_MUL,
        BASIS_COORDINATES_UNIQUE, DEDEKIND_RING_OF_INTEGERS, EQ_SYM_EQ, EQ_TRANS,
        EXTENSION, FINITE_NUMSEG_LT, FREE_BASIS_IN_CARRIER,
        FREE_BASIS_QUOTIENT_RING_HAS_SIZE, FUN_EQ_THM, HAS_SIZE, IDEAL_GENERATED_EQ_0,
        IDEAL_GENERATED_SING_ALT, IDEAL_GENERATED_SUBSET, IDEAL_NORM_MUL,
        IDEAL_NORM_PRIME_IMP_MAXIMAL, INTEGER_RING, INTEGER_RING_SUM, INT_ABS_POS,
        INT_COSETS_MATRIX_IMAGE, INT_NEG_EQ_0, INT_OF_NUM_EQ, INT_OF_NUM_OF_INT,
        IN_ELIM_THM, IN_IMAGE, IN_UNIV, ISUM_EQ, I_THM, LEFT_IMP_EXISTS_THM,
        MAXIMAL_IMP_PRIME_IDEAL, NUMBER_FIELD_NORM_EQ_0, PRIME_0, PRIME_IDEAL_SING,
        RING_0, RING_DET_EQ, RING_DET_HOMOMORPHISM,
        RING_HOMOMORPHISM_INTEGER_RING_OF_INT, RING_HOMOMORPHISM_SUBFIELD_INCLUSION,
        RING_HOMOMORPHISM_SUM, RING_IDEAL_IDEAL_GENERATED, RING_MUL, RING_OF_INTEGERS,
        RING_OF_INTEGERS_FINITE_QUOTIENT, RING_OF_INTEGERS_FREE,
        RING_OF_INTEGERS_FREE_BASIS_FIELD, RING_OF_INTEGERS_SUBSET, RING_OF_INT_0,
        RING_OF_INT_EQ_0_CHAR_0, RING_OF_INT_EQ_CHAR_0,
        RING_OF_INT_IN_RING_OF_INTEGERS, RING_OF_INT_IN_SUBFIELD_GENERATED,
        RING_OF_INT_NEG, RING_OF_INT_OF_NUM, RING_OF_INT_SUBFIELD_GENERATED, RING_SUM,
        RING_SUM_EQ, RING_SUM_RING_OF_INTEGERS, SUBSET, ideal_norm, int_matrix_image,
        mul_matrix, number_field, o_THM, .. } := D.core1
  -- @@SCOPE END

  let FREE_BASIS_IDEAL_NORM_COORD_MUL ← prove
    r"!r:A ring n w (f:A->num->int) a x.
        free_basis (integer_ring,r) (ring_of_int r) n w /\
        (!x i. f x i =
               if i < n
               then basis_coordinates (integer_ring,r) (ring_of_int r) n w x i
               else &0) /\
        a IN ring_carrier r /\ x IN ring_carrier r
        ==> f(ring_mul r a x) =
            (\i. if i < n
                 then isum {i | i < n}
                        (\j. mul_matrix (integer_ring,r)
                               (ring_of_int r) n w a i j * f x j)
                 else &0)"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"i:num") THEN ASM_REWRITE_TAC [] THEN COND_CASES_TAC THEN REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"ring_of_int r:int->A"), (← q r"integer_ring"), (← q r"r:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"a:A"), (← q r"x:A"), (← q r"i:num")] BASIS_COORDINATES_MUL) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, INTEGER_RING, INTEGER_RING_SUM] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC ISUM_EQ THEN SIMP_TAC [IN_ELIM_THM])

  let FREE_BASIS_IDEAL_NORM_IMAGE ← prove
    r"!r:A ring n w (f:A->num->int) a.
        free_basis (integer_ring,r) (ring_of_int r) n w /\
        (!x i. f x i =
               if i < n
               then basis_coordinates (integer_ring,r) (ring_of_int r) n w x i
               else &0) /\
        a IN ring_carrier r
        ==> IMAGE f (ideal_generated r {a}) =
            int_matrix_image {i | i < n}
              (mul_matrix (integer_ring,r) (ring_of_int r) n w a)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FREE_BASIS_IN_CARRIER)) THEN ASM_SIMP_TAC [IDEAL_GENERATED_SING_ALT, int_matrix_image] THEN REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM, IN_UNIV] THEN X_GEN_TAC (← q r"y:num->int") THEN EQ_TAC THENL [DISCH_THEN (X_CHOOSE_THEN (← q r"b:A") (CONJUNCTS_THEN2 SUBST1_TAC (X_CHOOSE_THEN (← q r"x:A") (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)))) THEN EXISTS_TAC (← q r"(f:A->num->int) x") THEN MATCH_MP_TAC FREE_BASIS_IDEAL_NORM_COORD_MUL THEN ASM_REWRITE_TAC [], DISCH_THEN (X_CHOOSE_THEN (← q r"z:num->int") SUBST1_TAC) THEN ABBREV_TAC (← q r"x = ring_sum r {i | i < n}
            (\i. ring_mul r (ring_of_int r ((z:num->int) i))
                            ((w:num->A) i))") THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier r") ASSUME_TAC THENL [EXPAND_TAC "x" THEN REWRITE_TAC [RING_SUM], ALL_TAC] THEN EXISTS_TAC (← q r"ring_mul r a x:A") THEN CONJ_TAC THENL [ALL_TAC, EXISTS_TAC (← q r"x:A") THEN ASM_REWRITE_TAC []] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"f:A->num->int"), (← q r"a:A"), (← q r"x:A")] FREE_BASIS_IDEAL_NORM_COORD_MUL) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"i:num") THEN COND_CASES_TAC THEN REWRITE_TAC [] THEN REWRITE_TAC [(← GSYM INTEGER_RING_SUM)] THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"j:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "x" THEN ASM_SIMP_TAC [BASIS_COORDINATES_LINCOMB, INTEGER_RING, IN_UNIV, RING_HOMOMORPHISM_INTEGER_RING_OF_INT]])

  let FREE_BASIS_IDEAL_NORM_PRINCIPAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"q /\ (p ==> r) ==> (p <=> q) ==> r")
    prove
      r"!r:A ring n w a.
          free_basis (integer_ring,r) (ring_of_int r) n w /\
          a IN ring_carrier r /\
          ~(algebra_norm (integer_ring,r) (ring_of_int r) a = &0)
          ==> FINITE(ring_carrier(quotient_ring r (ideal_generated r {a}))) /\
              &(ideal_norm r (ideal_generated r {a})) =
              abs(algebra_norm (integer_ring,r) (ring_of_int r) a)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_int r:int->A"), (← q r"integer_ring"), (← q r"r:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"a:A")] ALGEBRA_NORM_FREE_BASIS) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN DISCH_THEN SUBST_ALL_TAC THEN SUBGOAL_THEN (← q r"?f:A->num->int.
        !x i. f x i =
              if i < n
              then basis_coordinates (integer_ring,r) (ring_of_int r) n w x i
              else &0") STRIP_ASSUME_TAC THENL [EXISTS_TAC (← q r"\x:A i. if i < n
                          then basis_coordinates (integer_ring,r) (ring_of_int r)
                                 n w x i
                          else &0") THEN REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"f:A->num->int"), (← q r"a:A")] FREE_BASIS_IDEAL_NORM_IMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (LABEL_TAC "im")] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"ideal_generated r {a:A}"), (← q r"num_of_int(abs(ring_det integer_ring {i | i < n}
                     (mul_matrix (integer_ring,r) (ring_of_int r) n w (a:A))))")] FREE_BASIS_QUOTIENT_RING_HAS_SIZE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"{z | (!i. ~(i < n) ==> z i = &0) /\
           ring_sum r {i | i < n} (\i. ring_mul r (ring_of_int r (z i)) (w i))
           IN ideal_generated r {a:A}} =
      IMAGE (f:A->num->int) (ideal_generated r {a})") SUBST1_TAC THENL [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_IMAGE] THEN X_GEN_TAC (← q r"z:num->int") THEN EQ_TAC THENL [STRIP_TAC THEN EXISTS_TAC (← q r"ring_sum r {i | i < n}
                      (\i. ring_mul r (ring_of_int r ((z:num->int) i))
                                      ((w:num->A) i))") THEN ASM_REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"i:num") THEN COND_CASES_TAC THEN ASM_SIMP_TAC [BASIS_COORDINATES_LINCOMB, INTEGER_RING, IN_UNIV, RING_HOMOMORPHISM_INTEGER_RING_OF_INT], DISCH_THEN (X_CHOOSE_THEN (← q r"x:A") (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier r") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"{a:A}")] IDEAL_GENERATED_SUBSET) THEN REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN CONJ_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sum r {i | i < n}
            (\i. ring_mul r (ring_of_int r ((f:A->num->int) x i))
                            ((w:num->A) i)) = x") (fun th => ASM_REWRITE_TAC [th]) THEN TRANS_TAC EQ_TRANS (← q r"ring_sum r {i | i < n}
            (\i. ring_mul r
                   (ring_of_int r
                     (basis_coordinates (integer_ring,r) (ring_of_int r) n w x i))
                   ((w:num->A) i))") THEN CONJ_TAC THENL [MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC [IN_ELIM_THM], MATCH_MP_TAC BASIS_COORDINATES_EXPAND THEN ASM_REWRITE_TAC []]], ALL_TAC] THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [REMOVE_THEN "im" SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"{i:num | i < n}"), (← q r"mul_matrix (integer_ring,r) (ring_of_int r) n w (a:A)")] INT_COSETS_MATRIX_IMAGE) THEN REWRITE_TAC [FINITE_NUMSEG_LT] THEN DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC, REWRITE_TAC [HAS_SIZE, ideal_norm] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC INT_OF_NUM_OF_INT THEN REWRITE_TAC [INT_ABS_POS]])

  let MUL_MATRIX_RING_OF_INTEGERS ← prove
    r"!k:A ring n w a i j.
        free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w /\
        free_basis (subfield_generated k {ring_0 k},k) I n w /\
        a IN ring_carrier(ring_of_integers k) /\ i < n /\ j < n
        ==> mul_matrix (subfield_generated k {ring_0 k},k) I n w a i j =
            ring_of_int k
             (mul_matrix (integer_ring,ring_of_integers k)
                (ring_of_int k) n w a i j)"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [mul_matrix] THEN MP_TAC (← ISPECL [(← q r"ring_of_int k:int->A"), (← q r"integer_ring"), (← q r"ring_of_integers k:A ring"), (← q r"n:num"), (← q r"w:num->A")] FREE_BASIS_IN_CARRIER) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_mul (ring_of_integers k) a ((w:num->A) j) IN
    ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_MUL], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_int k:int->A"), (← q r"integer_ring"), (← q r"ring_of_integers k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"ring_mul (ring_of_integers k) a ((w:num->A) j)")] BASIS_COORDINATES) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o CONJUNCT2) THEN ABBREV_TAC (← q r"z = basis_coordinates (integer_ring,ring_of_integers k) (ring_of_int k)
          n w (ring_mul (ring_of_integers k) a ((w:num->A) j))") THEN wPart (lhand o lhand) (lhand o rand) RING_SUM_RING_OF_INTEGERS THEN ANTS_TAC THENL [REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL THEN ASM_SIMP_TAC [RING_OF_INT_IN_RING_OF_INTEGERS], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k}:A ring"), (← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"ring_mul k a ((w:num->A) j)"), (← q r"\i. ring_of_int k ((z:num->int) i):A")] BASIS_COORDINATES_UNIQUE) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION, I_THM, RING_OF_INT_IN_SUBFIELD_GENERATED] THEN DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC)

  let NUMBER_FIELD_NORM_INTEGRAL_BASIS ← prove
    r"!k:A ring n w a.
        number_field k /\
        free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w /\
        a IN ring_carrier(ring_of_integers k)
        ==> algebra_norm (subfield_generated k {ring_0 k},k) I a =
            ring_of_int k
              (algebra_norm (integer_ring,ring_of_integers k)
                            (ring_of_int k) a)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A")] RING_OF_INTEGERS_FREE_BASIS_FIELD) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT2) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP (← REWRITE_RULE [SUBSET] (← SPEC (← q r"k:A ring") RING_OF_INTEGERS_SUBSET)))) THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"a:A")] ALGEBRA_NORM_FREE_BASIS) THEN MP_TAC (← ISPECL [(← q r"ring_of_int k:int->A"), (← q r"integer_ring"), (← q r"ring_of_integers k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"a:A")] ALGEBRA_NORM_FREE_BASIS) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION] THEN ANTS_TAC THENL [MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN REWRITE_TAC [RING_OF_INTEGERS], REPEAT (DISCH_THEN SUBST1_TAC)] THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"subfield_generated k {ring_0 k}:A ring"), (← q r"ring_of_int k:int->A"), (← q r"{i:num | i < n}"), (← q r"mul_matrix (integer_ring,ring_of_integers k) (ring_of_int k)
       n w (a:A)")] RING_DET_HOMOMORPHISM) THEN REWRITE_TAC [FINITE_NUMSEG_LT, INTEGER_RING, IN_UNIV] THEN ANTS_TAC THENL [MP_TAC (← ISPEC (← q r"subfield_generated k {ring_0 k}:A ring") RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN REWRITE_TAC [RING_OF_INT_SUBFIELD_GENERATED], DISCH_THEN SUBST1_TAC] THEN MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"i:num"), (← q r"j:num")] THEN STRIP_TAC THEN MATCH_MP_TAC MUL_MATRIX_RING_OF_INTEGERS THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_TRACE_INTEGRAL_BASIS ← prove
    r"!k:A ring n w x.
        number_field k /\
        free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w /\
        x IN ring_carrier(ring_of_integers k)
        ==> algebra_trace (subfield_generated k {ring_0 k},k) I x =
            ring_of_int k
              (algebra_trace (integer_ring,ring_of_integers k)
                             (ring_of_int k) x)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A")] RING_OF_INTEGERS_FREE_BASIS_FIELD) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT2) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP (← REWRITE_RULE [SUBSET] (← SPEC (← q r"k:A ring") RING_OF_INTEGERS_SUBSET)))) THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"x:A")] ALGEBRA_TRACE_FREE_BASIS) THEN MP_TAC (← ISPECL [(← q r"ring_of_int k:int->A"), (← q r"integer_ring"), (← q r"ring_of_integers k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"x:A")] ALGEBRA_TRACE_FREE_BASIS) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION] THEN ANTS_TAC THENL [MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN REWRITE_TAC [RING_OF_INTEGERS], REPEAT (DISCH_THEN SUBST1_TAC)] THEN MP_TAC (← ISPEC (← q r"subfield_generated k {ring_0 k}:A ring") RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN REWRITE_TAC [RING_OF_INT_SUBFIELD_GENERATED] THEN DISCH_THEN (fun th => tactic_of do pure (wPart rand (lhand o rand) (← MATCH_MP RING_HOMOMORPHISM_SUM th))) THEN REWRITE_TAC [FINITE_NUMSEG_LT, INTEGER_RING, IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC [IN_ELIM_THM, o_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC MUL_MATRIX_RING_OF_INTEGERS THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_Q ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!k:A ring a.
          number_field k /\ a IN ring_carrier(ring_of_integers k) /\
          ~(a = ring_0 k)
          ==> ?m. algebra_norm (subfield_generated k {ring_0 k},k) I a =
                  ring_of_int k m /\
                  &(ideal_norm (ring_of_integers k)
                      (ideal_generated (ring_of_integers k) {a})) = abs m"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM ((X_CHOOSE_TAC (← q r"w:num->A")) o (MATCH_MP RING_OF_INTEGERS_FREE)) THEN ABBREV_TAC (← q r"n = extension_degree (subfield_generated k {ring_0 k},k:A ring) I") THEN EXISTS_TAC (← q r"algebra_norm (integer_ring,ring_of_integers k)
                  (ring_of_int k) (a:A)") THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [MATCH_MP_TAC NUMBER_FIELD_NORM_INTEGRAL_BASIS THEN MAP_EVERY EXISTS_TAC [(← q r"n:num"), (← q r"w:num->A")] THEN ASM_REWRITE_TAC [], DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"a:A")] FREE_BASIS_IDEAL_NORM_PRINCIPAL) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [ALL_TAC, SIMP_TAC []] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"~(a:A = ring_0 k)") THEN REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A")] NUMBER_FIELD_NORM_EQ_0) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN FIRST_ASSUM (ACCEPT_TAC o (MATCH_MP (← REWRITE_RULE [SUBSET] (← SPEC (← q r"k:A ring") RING_OF_INTEGERS_SUBSET)))), DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC [RING_OF_INT_0]])

  let NUMBER_FIELD_IDEAL_NORM_MUL_Q ← prove
    r"!k:A ring j j'.
        number_field k /\
        ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
        ring_ideal (ring_of_integers k) j' /\ ~(j' = {ring_0 k})
        ==> ideal_norm (ring_of_integers k)
              (ideal_prod (ring_of_integers k) j j') =
            ideal_norm (ring_of_integers k) j *
            ideal_norm (ring_of_integers k) j'"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC IDEAL_NORM_MUL THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_OF_INTEGERS_FINITE_QUOTIENT, RING_OF_INTEGERS])

  let NUMBER_FIELD_IDEAL_NORM_PRIME_IMP_PRIME ← prove
    r"!k j:A->bool.
        number_field k /\ ring_ideal (ring_of_integers k) j /\
        ~(j = {ring_0 k}) /\ prime(ideal_norm (ring_of_integers k) j)
        ==> prime_ideal (ring_of_integers k) j"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC MAXIMAL_IMP_PRIME_IDEAL THEN MATCH_MP_TAC IDEAL_NORM_PRIME_IMP_MAXIMAL THEN ASM_SIMP_TAC [RING_OF_INTEGERS_FINITE_QUOTIENT])

  let NUMBER_FIELD_NORM_PRIME_IMP_RING_PRIME ← prove
    r"!k x:A p.
        number_field k /\ x IN ring_carrier(ring_of_integers k) /\ prime p /\
        (algebra_norm (subfield_generated k {ring_0 k},k) I x =
         ring_of_num k p \/
         algebra_norm (subfield_generated k {ring_0 k},k) I x =
         ring_neg k (ring_of_num k p))
        ==> ring_prime (ring_of_integers k) x"
    (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN REWRITE_TAC [(← GSYM RING_OF_INT_OF_NUM), (← GSYM RING_OF_INT_NEG)] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"~(x:A = ring_0 k)") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun z4 => (do let z5 ← (do let z6 ← (pure z4); pure (concl z6)); pure (is_disj z5))))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_0 k:A")] NUMBER_FIELD_NORM_EQ_0) THEN ASM_REWRITE_TAC [RING_0] THEN DISCH_THEN SUBST1_TAC THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN ASM_SIMP_TAC [RING_OF_INT_EQ_0_CHAR_0] THEN REWRITE_TAC [INT_NEG_EQ_0, INT_OF_NUM_EQ] THEN ASM_MESON_TAC [PRIME_0], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A")] NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_Q) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"m:int") THEN DISCH_THEN (CONJUNCTS_THEN2 (fun th => RULE_ASSUM_TAC (REWRITE_RULE [th])) ASSUME_TAC) THEN RULE_ASSUM_TAC (REWRITE_RULE [(← MATCH_MP RING_OF_INT_EQ_CHAR_0 (← ASSUME (← q r"ring_char(k:A ring) = 0")))]) THEN SUBGOAL_THEN (← q r"ideal_norm (ring_of_integers k)
               (ideal_generated (ring_of_integers k) {x:A}) = p") ASSUME_TAC THENL [REWRITE_TAC [(← GSYM INT_OF_NUM_EQ)] THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM ((DISJ_CASES_THEN SUBST1_TAC) o (checkM (fun z1 => (do let z2 ← (do let z3 ← (pure z1); pure (concl z3)); pure (is_disj z2))))) THEN INT_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"prime_ideal (ring_of_integers k)
                (ideal_generated (ring_of_integers k) {x:A})") MP_TAC THENL [MATCH_MP_TAC NUMBER_FIELD_IDEAL_NORM_PRIME_IMP_PRIME THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"x:A")] IDEAL_GENERATED_EQ_0) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], ASM_REWRITE_TAC [PRIME_IDEAL_SING, RING_OF_INTEGERS]])

  -- @@RETURN BEGIN
  return { FREE_BASIS_IDEAL_NORM_COORD_MUL, FREE_BASIS_IDEAL_NORM_IMAGE,
           FREE_BASIS_IDEAL_NORM_PRINCIPAL, MUL_MATRIX_RING_OF_INTEGERS,
           NUMBER_FIELD_NORM_INTEGRAL_BASIS, NUMBER_FIELD_TRACE_INTEGRAL_BASIS,
           NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_Q, NUMBER_FIELD_IDEAL_NORM_MUL_Q,
           NUMBER_FIELD_IDEAL_NORM_PRIME_IMP_PRIME,
           NUMBER_FIELD_NORM_PRIME_IMP_RING_PRIME }
  -- @@RETURN END

end HolANT.NormIndex
