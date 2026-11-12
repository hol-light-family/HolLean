/- ========================================================================= -/
/- ANT: The ring of integers O_K of a number field K: free of rank n ...   -/
/- ========================================================================= -/
/- File: HolANT/RingOfIntegers.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/ring_of_integers.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antringofintegersdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/products.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.RingOfIntegers fills them).

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
import HolLibrary.Products
import HolANT.Algmisc
import HolANT.Integral
import HolANT.IdealArith
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.IdealNorm
import HolLibrary.Isum
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.Algmisc
open HolANT.Integral
open HolANT.IdealArith
open HolANT.Dedekind
open HolANT.DedekindStruct
open HolANT.IdealNorm
open HolANT.Zlattice
open HolANT.Numfield

namespace HolANT.RingOfIntegers

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (BASIS_COORDINATES BASIS_DISCRIMINANT_NONZERO BASIS_DISCRIMINANT_TIMES_COORD
   CARD_EQ_IMAGES CARD_HAS_SIZE_CONG CARD_NUMSEG_LT
   CARRIER_SUBRING_GENERATED_SUBRING COND_RAND COUNTABLE_IMAGE
   COUNTABLE_RESTRICTED_FUNSPACE COUNTABLE_SUBSET EMPTY_GSPEC EQ_IMP EQ_TRANS
   EXTENSION FIELD_IMP_INTEGRAL_DOMAIN FIELD_NONTRIVIAL FIELD_QUOTIENT_RING
   FIELD_SUBFIELD_GENERATED FINITE_IMAGE FINITE_IMP_COUNTABLE
   FINITE_INTEGRAL_DOMAIN_IMP_FIELD FINITE_NUMSEG_LT FINITE_QUOTIENT_RING_MONO
   FINITE_SUBSET FORALL_IN_IMAGE FREE_BASIS_PRIME_SUBFIELD_INT_LINCOMB
   FUN_EQ_THM HAS_SIZE IDEAL_GENERATED_INC IDEAL_GENERATED_MINIMAL
   IDEAL_GENERATED_SING_ALT IMAGE_EQ INTEGER_RING INTEGER_RING_POW
   INTEGRALLY_CLOSED_INTEGRAL_CLOSURE INTEGRAL_DOMAIN_MUL_EQ_0
   INTEGRAL_DOMAIN_QUOTIENT_RING INTEGRAL_DOMAIN_RING_OF_INTEGERS
   INTEGRAL_ELEMENT_EXPLICIT INT_ABS_POS INT_ABS_POW INT_COSETS_MATRIX_IMAGE
   INT_COUNTABLE INT_LATTICE_MATRIX_IMAGE INT_MUL_LZERO INT_MUL_RID
   INT_MUL_RZERO INT_POW_EQ_0 INT_SUB_REFL IN_ELIM_THM IN_IMAGE IN_INSERT
   IN_RING_IDEAL_0 IN_RING_IDEAL_ADD IN_RING_IDEAL_LMUL IN_RING_IDEAL_RMUL
   IN_RING_IDEAL_SUB IN_RING_IDEAL_SUM IN_SUBRING_ADD IN_SUBRING_INT
   IN_SUBRING_MUL IN_SUBRING_NEG IN_SUBRING_POW IN_SUBRING_SUB IN_SUBRING_SUM
   IN_UNIV ISUM_DELTA_GEN I_THM LT LT_0 LT_REFL LT_SUC MONO_EXISTS NOT_SUC
   NUMBER_FIELD_DEGREE_POS NUMBER_FIELD_FREE_BASIS_DEGREE NUMBER_FIELD_IMP_FIELD
   NUMBER_FIELD_INTEGRAL_FREE_BASIS NUMBER_FIELD_INTEGRAL_MULTIPLE
   NUMBER_FIELD_TRACE_INTEGRAL_Q NUM_OF_INT_POW PRIME_IMP_RING_IDEAL
   PRIME_SUBRING QUOTIENT_RING_CARRIER RIGHT_IMP_EXISTS_THM RING_1
   RING_ADD_LZERO RING_ADD_RZERO RING_CARRIER_SUBFIELD_GENERATED_SUBSET
   RING_CHAR_EQ_0 RING_COSET_EQ RING_DET_DIAGONAL RING_DET_SUBRING
   RING_HOMOMORPHISM_INTEGER_RING_OF_INT RING_HOMOMORPHISM_SUBFIELD_INCLUSION
   RING_IDEAL_IDEAL_GENERATED RING_IDEAL_IMP_SUBSET RING_INT_LINCOMB
   RING_INT_LINCOMB_SANDWICH RING_MUL RING_MUL_ASSOC RING_OF_INT
   RING_OF_INTEGERS RING_OF_INTEGERS_CARRIER RING_OF_INTEGERS_SUBRING
   RING_OF_INTEGERS_SUBSET RING_OF_INT_0 RING_OF_INT_EQ_0_CHAR_0
   RING_OF_INT_IN_SUBFIELD_GENERATED RING_OF_INT_SUBFIELD_GENERATED
   RING_OF_NUM_SUBFIELD_GENERATED RING_POW RING_PRODUCT_CONST RING_SUB_REFL
   RING_SUM RING_SUM_CLAUSES RING_SUM_EQ RING_SUM_IMAGE RING_SUM_LMUL
   RING_SUM_SUBRING_GENERATED SIMPLE_IMAGE_GEN SING_SUBSET SKOLEM_THM
   SUBFIELD_GENERATED SUBRING_GENERATED SUBSET SUBSET_ANTISYM SUBSET_UNIV
   SUC_INJ basis_discriminant dedekind_domain finitely_generated_ideal
   free_basis ideal_norm int_cosets int_lattice int_matrix_image noetherian_ring
   number_field o_DEF ring_of_integers ring_pow subring_of : thm)
  deriving Inhabited

/-- What ring_of_integers.ml uses from Session besides theorems. -/
structure RingOfIntegersDeps where
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
/- ring_of_integers.ml phrases from line 51 to 776                        -/
/- ---------------------------------------------------------------------- -/

structure RingOfIntegers01 where
  -- @@FIELDS
  QUOTIENT_RING_HAS_SIZE_INT_LINEAR : thm
  NOETHERIAN_RING_INT_LINEAR : thm
  QUOTIENT_RING_INTEGER_INT_LINEAR : thm
  FREE_BASIS_INTEGER_RING_SUBRING_GENERATED : thm
  FREE_BASIS_QUOTIENT_RING_HAS_SIZE : thm
  FREE_BASIS_INTEGER_RING_COORDINATES : thm
  FREE_BASIS_IMP_NOETHERIAN_RING : thm
  FREE_BASIS_QUOTIENT_RING_INTEGER : thm
  RING_OF_INTEGERS_DISCRIMINANT : thm
  RING_OF_INTEGERS_FREE : thm
  COUNTABLE_RING_OF_INTEGERS : thm
  RING_OF_INTEGERS_FREE_BASIS_FIELD : thm
  NOETHERIAN_RING_OF_INTEGERS : thm
  INTEGRALLY_CLOSED_RING_OF_INTEGERS : thm
  RING_OF_INTEGERS_IDEAL_INTEGER : thm
  RING_OF_INTEGERS_FINITE_QUOTIENT : thm
  RING_OF_INTEGERS_FINITE_RESIDUE_FIELDS : thm
  RING_OF_INTEGERS_IDEAL_NORM_INTEGER : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupRingOfIntegers01 [HolBase] (D : RingOfIntegersDeps) :
    ExceptT String IO RingOfIntegers01 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, INT_ARITH_TAC,
        MESON_TAC, RING_RULE, SET_TAC, TAUT, .. } := D
  let { BASIS_COORDINATES, BASIS_DISCRIMINANT_NONZERO, BASIS_DISCRIMINANT_TIMES_COORD,
        CARD_EQ_IMAGES, CARD_HAS_SIZE_CONG, CARD_NUMSEG_LT,
        CARRIER_SUBRING_GENERATED_SUBRING, COND_RAND, COUNTABLE_IMAGE,
        COUNTABLE_RESTRICTED_FUNSPACE, COUNTABLE_SUBSET, EMPTY_GSPEC, EQ_IMP, EQ_TRANS,
        EXTENSION, FIELD_IMP_INTEGRAL_DOMAIN, FIELD_NONTRIVIAL,
        FIELD_SUBFIELD_GENERATED, FINITE_IMAGE, FINITE_IMP_COUNTABLE, FINITE_NUMSEG_LT,
        FINITE_QUOTIENT_RING_MONO, FINITE_SUBSET, FORALL_IN_IMAGE,
        FREE_BASIS_PRIME_SUBFIELD_INT_LINCOMB, FUN_EQ_THM, HAS_SIZE,
        IDEAL_GENERATED_INC, IDEAL_GENERATED_MINIMAL, IDEAL_GENERATED_SING_ALT,
        IMAGE_EQ, INTEGER_RING, INTEGER_RING_POW, INTEGRALLY_CLOSED_INTEGRAL_CLOSURE,
        INTEGRAL_DOMAIN_MUL_EQ_0, INTEGRAL_ELEMENT_EXPLICIT, INT_ABS_POS, INT_ABS_POW,
        INT_COSETS_MATRIX_IMAGE, INT_COUNTABLE, INT_LATTICE_MATRIX_IMAGE,
        INT_MUL_LZERO, INT_MUL_RID, INT_MUL_RZERO, INT_POW_EQ_0, INT_SUB_REFL,
        IN_ELIM_THM, IN_IMAGE, IN_INSERT, IN_RING_IDEAL_0, IN_RING_IDEAL_ADD,
        IN_RING_IDEAL_LMUL, IN_RING_IDEAL_RMUL, IN_RING_IDEAL_SUB, IN_RING_IDEAL_SUM,
        IN_SUBRING_ADD, IN_SUBRING_INT, IN_SUBRING_MUL, IN_SUBRING_NEG, IN_SUBRING_POW,
        IN_SUBRING_SUB, IN_SUBRING_SUM, IN_UNIV, ISUM_DELTA_GEN, I_THM, LT, LT_0,
        LT_REFL, LT_SUC, MONO_EXISTS, NOT_SUC, NUMBER_FIELD_DEGREE_POS,
        NUMBER_FIELD_FREE_BASIS_DEGREE, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_INTEGRAL_FREE_BASIS, NUMBER_FIELD_INTEGRAL_MULTIPLE,
        NUMBER_FIELD_TRACE_INTEGRAL_Q, NUM_OF_INT_POW, PRIME_IMP_RING_IDEAL,
        PRIME_SUBRING, QUOTIENT_RING_CARRIER, RIGHT_IMP_EXISTS_THM, RING_1,
        RING_ADD_LZERO, RING_ADD_RZERO, RING_CARRIER_SUBFIELD_GENERATED_SUBSET,
        RING_CHAR_EQ_0, RING_COSET_EQ, RING_DET_DIAGONAL, RING_DET_SUBRING,
        RING_HOMOMORPHISM_INTEGER_RING_OF_INT, RING_HOMOMORPHISM_SUBFIELD_INCLUSION,
        RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IMP_SUBSET, RING_INT_LINCOMB,
        RING_INT_LINCOMB_SANDWICH, RING_MUL, RING_MUL_ASSOC, RING_OF_INT,
        RING_OF_INTEGERS, RING_OF_INTEGERS_CARRIER, RING_OF_INTEGERS_SUBRING,
        RING_OF_INTEGERS_SUBSET, RING_OF_INT_0, RING_OF_INT_EQ_0_CHAR_0,
        RING_OF_INT_IN_SUBFIELD_GENERATED, RING_OF_INT_SUBFIELD_GENERATED,
        RING_OF_NUM_SUBFIELD_GENERATED, RING_POW, RING_PRODUCT_CONST, RING_SUB_REFL,
        RING_SUM, RING_SUM_CLAUSES, RING_SUM_EQ, RING_SUM_IMAGE, RING_SUM_LMUL,
        RING_SUM_SUBRING_GENERATED, SIMPLE_IMAGE_GEN, SING_SUBSET, SKOLEM_THM,
        SUBFIELD_GENERATED, SUBRING_GENERATED, SUBSET, SUBSET_ANTISYM, SUBSET_UNIV,
        SUC_INJ, basis_discriminant, finitely_generated_ideal, free_basis, ideal_norm,
        int_cosets, int_lattice, int_matrix_image, noetherian_ring, number_field,
        o_DEF, ring_of_integers, ring_pow, subring_of, .. } := D.core1
  -- @@SCOPE END

  let QUOTIENT_RING_HAS_SIZE_INT_LINEAR ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!r a b c:A.
         a IN ring_carrier r /\ b IN ring_carrier r /\ c IN ring_carrier r
         ==> ring_sub r a c = ring_add r (ring_sub r a b) (ring_sub r b c) /\
             ring_sub r a b =
             ring_sub r (ring_sub r a c) (ring_sub r b c)")
    prove
      r"!r:A ring j (psi:(K->int)->A) s N.
          ring_ideal r j /\
          (!z. psi z IN ring_carrier r) /\
          (!x y. psi (\i. x i - y i) = ring_sub r (psi x) (psi y)) /\
          (!x. x IN ring_carrier r
               ==> ?z. (!i. ~(i IN s) ==> z i = &0) /\ psi z = x)
          ==> (ring_carrier(quotient_ring r j) HAS_SIZE N <=>
               int_cosets s {z | (!i. ~(i IN s) ==> z i = &0) /\ psi z IN j}
               HAS_SIZE N)"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_carrier(quotient_ring r j) =
      IMAGE (\z. ring_coset r j ((psi:(K->int)->A) z))
            {z | !i. ~(i IN s) ==> z i = &0}") SUBST1_TAC THENL [ASM_SIMP_TAC [QUOTIENT_RING_CARRIER] THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM, IN_IMAGE] THEN X_GEN_TAC (← q r"c:A->bool") THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THENL [FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"a:A"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"z:K->int") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"z:K->int") THEN ASM_REWRITE_TAC [], EXISTS_TAC (← q r"(psi:(K->int)->A) x") THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"int_cosets s
        {z | (!i. ~(i IN s) ==> z i = &0) /\ (psi:(K->int)->A) z IN j} =
      IMAGE (\x. {y | (!i. ~(i IN s) ==> y i = &0) /\
                      ring_sub r (psi y) (psi x) IN j})
            {z | !i. ~(i IN s) ==> z i = &0}") SUBST1_TAC THENL [REWRITE_TAC [int_cosets] THEN GEN_REWRITE_TAC LAND_CONV [SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC IMAGE_EQ THEN X_GEN_TAC (← q r"x:K->int") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC (← q r"y:K->int") THEN ASM_CASES_TAC (← q r"!i. ~(i IN s) ==> (y:K->int) i = &0") THEN ASM_SIMP_TAC [INT_SUB_REFL], ALL_TAC] THEN MATCH_MP_TAC CARD_HAS_SIZE_CONG THEN MATCH_MP_TAC CARD_EQ_IMAGES THEN REWRITE_TAC [IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"x:K->int"), (← q r"y:K->int")] THEN STRIP_TAC THEN ASM_SIMP_TAC [RING_COSET_EQ, EXTENSION, IN_ELIM_THM] THEN EQ_TAC THENL [DISCH_TAC THEN X_GEN_TAC (← q r"z:K->int") THEN ASM_CASES_TAC (← q r"!i. ~(i IN s) ==> (z:K->int) i = &0") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"(psi:(K->int)->A) z"), (← q r"(psi:(K->int)->A) x"), (← q r"(psi:(K->int)->A) y")] r1) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => EQ_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC [th]) THENL [MATCH_MP_TAC IN_RING_IDEAL_ADD, MATCH_MP_TAC IN_RING_IDEAL_SUB] THEN ASM_REWRITE_TAC [], DISCH_THEN (MP_TAC o (SPEC (← q r"x:K->int"))) THEN ASM_SIMP_TAC [RING_SUB_REFL, IN_RING_IDEAL_0]])

  let NOETHERIAN_RING_INT_LINEAR ← prove
    r"!r:A ring (psi:(K->int)->A) s.
        FINITE s /\
        (!z. psi z IN ring_carrier r) /\
        (!x y. psi (\i. x i - y i) = ring_sub r (psi x) (psi y)) /\
        (!M z. psi (\i. isum s (\j. M i j * z j)) =
               ring_sum r s
                 (\j. ring_mul r (ring_of_int r (z j)) (psi (\i. M i j)))) /\
        (!z z'. (!i. i IN s ==> z i = z' i) ==> psi z = psi z') /\
        (!x. x IN ring_carrier r
             ==> ?z. (!i. ~(i IN s) ==> z i = &0) /\ psi z = x)
        ==> noetherian_ring r"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"(psi:(K->int)->A) (\i. &0) = ring_0 r") ASSUME_TAC THENL [MP_TAC (← SPECL [(← q r"\i:K. (&0:int)"), (← q r"\i:K. (&0:int)")] (← ASSUME (← q r"!x y. (psi:(K->int)->A) (\i. x i - y i) =
            ring_sub r (psi x) (psi y)"))) THEN REWRITE_TAC [INT_SUB_REFL] THEN ASM_SIMP_TAC [RING_SUB_REFL], ALL_TAC] THEN REWRITE_TAC [noetherian_ring, finitely_generated_ideal] THEN X_GEN_TAC (← q r"j:A->bool") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"s:K->bool"), (← q r"{z | (!i. ~(i IN s) ==> z i = &0) /\ (psi:(K->int)->A) z IN j}")] INT_LATTICE_MATRIX_IMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [int_lattice, SUBSET, IN_ELIM_THM] THEN ASM_SIMP_TAC [IN_RING_IDEAL_0, IN_RING_IDEAL_SUB, INT_SUB_REFL], DISCH_THEN (X_CHOOSE_TAC (← q r"M:K->K->int"))] THEN EXISTS_TAC (← q r"IMAGE (\l:K. (psi:(K->int)->A) (\i. (M:K->K->int) i l))
                    (s:K->bool)") THEN ASM_SIMP_TAC [FINITE_IMAGE, SUBSET, FORALL_IN_IMAGE] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"l:K") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(\i. if i IN s then (M:K->K->int) i l else &0) IN int_matrix_image s M") MP_TAC THENL [REWRITE_TAC [int_matrix_image, IN_IMAGE, IN_UNIV] THEN EXISTS_TAC (← q r"\j:K. if j = l then (&1:int) else &0") THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"i:K") THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [COND_RAND, INT_MUL_RID, INT_MUL_RZERO, ISUM_DELTA_GEN], FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_THEN (MP_TAC o CONJUNCT2) THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN SIMP_TAC []], REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"x:A"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:K->int") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(c:K->int) IN
      {z | (!i. ~(i IN s) ==> z i = &0) /\ (psi:(K->int)->A) z IN j}") MP_TAC THENL [ASM_REWRITE_TAC [IN_ELIM_THM], ASM_REWRITE_TAC []] THEN REWRITE_TAC [int_matrix_image, IN_IMAGE, IN_UNIV] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"z:K->int") ASSUME_TAC) THEN SUBGOAL_THEN (← q r"x = (psi:(K->int)->A) (\i. isum s (\j. (M:K->K->int) i j * z j))") SUBST1_TAC THENL [TRANS_TAC EQ_TRANS (← q r"(psi:(K->int)->A) c") THEN CONJ_TAC THENL [ASM_REWRITE_TAC [], FIRST_ASSUM MATCH_MP_TAC] THEN ASM_SIMP_TAC [], ASM_REWRITE_TAC []] THEN MATCH_MP_TAC IN_RING_IDEAL_SUM THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN X_GEN_TAC (← q r"l:K") THEN DISCH_TAC THEN MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, RING_OF_INT] THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC (← q r"l:K") THEN ASM_REWRITE_TAC []])

  let QUOTIENT_RING_INTEGER_INT_LINEAR ← prove
    r"!r:A ring (psi:(K->int)->A) s m.
        FINITE s /\ ~(m = &0) /\
        (!z. psi z IN ring_carrier r) /\
        (!x y. psi (\i. x i - y i) = ring_sub r (psi x) (psi y)) /\
        (!c x. psi (\i. c * x i) = ring_mul r (ring_of_int r c) (psi x)) /\
        (!z z'. (!i. i IN s ==> z i = z' i) ==> psi z = psi z') /\
        (!x. x IN ring_carrier r
             ==> ?z. (!i. ~(i IN s) ==> z i = &0) /\ psi z = x) /\
        (!z. psi z = ring_0 r ==> !i. i IN s ==> z i = &0)
        ==> ring_carrier(quotient_ring r (ideal_generated r {ring_of_int r m}))
            HAS_SIZE (num_of_int(abs m) EXP CARD s)"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"!x y. (!i. ~(i IN s) ==> x i = &0) /\ (!i. ~(i IN s) ==> y i = &0) /\
          (psi:(K->int)->A) x = psi y
          ==> x = y") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"i:K") THEN ASM_CASES_TAC (← q r"(i:K) IN s") THEN ASM_SIMP_TAC [] THEN MP_TAC (← SPEC (← q r"\i:K. (x:K->int) i - y i") (← ASSUME (← q r"!z. (psi:(K->int)->A) z = ring_0 r ==> !i. i IN s ==> z i = &0"))) THEN ASM_SIMP_TAC [RING_SUB_REFL] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"i:K"))) THEN ASM_REWRITE_TAC [] THEN INT_ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_generated (r:A ring) {ring_of_int r (m:int)}"), (← q r"psi:(K->int)->A"), (← q r"s:K->bool"), (← q r"num_of_int(abs m) EXP CARD(s:K->bool)")] QUOTIENT_RING_HAS_SIZE_INT_LINEAR) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN DISCH_THEN SUBST1_TAC THEN SUBGOAL_THEN (← q r"{z | (!i. ~(i IN s) ==> z i = &0) /\
         (psi:(K->int)->A) z IN ideal_generated r {ring_of_int r m}} =
    int_matrix_image s (\i j:K. if i = j then m else &0)") SUBST1_TAC THENL [SIMP_TAC [IDEAL_GENERATED_SING_ALT, RING_OF_INT] THEN SUBGOAL_THEN (← q r"int_matrix_image s (\i j:K. if i = j then m else &0) =
      IMAGE (\z i. if i IN s then m * z i else &0) (:K->int)") SUBST1_TAC THENL [REWRITE_TAC [int_matrix_image] THEN MATCH_MP_TAC IMAGE_EQ THEN X_GEN_TAC (← q r"z:K->int") THEN DISCH_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"i:K") THEN COND_CASES_TAC THEN REWRITE_TAC [] THEN TRANS_TAC EQ_TRANS (← q r"isum s (\j. if j = i then m * (z:K->int) j else &0)") THEN CONJ_TAC THENL [AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"j:K") THEN ASM_CASES_TAC (← q r"j:K = i") THEN ASM_REWRITE_TAC [INT_MUL_LZERO], ASM_REWRITE_TAC [ISUM_DELTA_GEN]], ALL_TAC] THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_IMAGE, IN_UNIV] THEN X_GEN_TAC (← q r"z:K->int") THEN EQ_TAC THENL [DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"x:A") STRIP_ASSUME_TAC)) THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"x:A"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:K->int") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"c:K->int") THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC [] THEN TRANS_TAC EQ_TRANS (← q r"(psi:(K->int)->A) (\i. m * c i)") THEN CONJ_TAC THENL [ASM_REWRITE_TAC [], FIRST_ASSUM MATCH_MP_TAC] THEN SIMP_TAC [], DISCH_THEN (X_CHOOSE_THEN (← q r"c:K->int") SUBST1_TAC) THEN CONJ_TAC THENL [SIMP_TAC [], ALL_TAC] THEN EXISTS_TAC (← q r"(psi:(K->int)->A) c") THEN ASM_REWRITE_TAC [] THEN TRANS_TAC EQ_TRANS (← q r"(psi:(K->int)->A) (\i. m * c i)") THEN CONJ_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN SIMP_TAC [], ASM_REWRITE_TAC []]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"s:K->bool"), (← q r"\i j:K. if i = j then (m:int) else &0")] INT_COSETS_MATRIX_IMAGE) THEN SUBGOAL_THEN (← q r"ring_det integer_ring s (\i j:K. if i = j then m else &0) = m pow CARD s") SUBST1_TAC THENL [wPart lhand (lhand o rand) RING_DET_DIAGONAL THEN ASM_REWRITE_TAC [INTEGER_RING] THEN ANTS_TAC THENL [SIMP_TAC [], DISCH_THEN SUBST1_TAC] THEN ASM_SIMP_TAC [RING_PRODUCT_CONST, INTEGER_RING, IN_UNIV, INTEGER_RING_POW], ALL_TAC] THEN ASM_REWRITE_TAC [INT_POW_EQ_0] THEN SIMP_TAC [INT_ABS_POW, NUM_OF_INT_POW, INT_ABS_POS])

  let FREE_BASIS_INTEGER_RING_SUBRING_GENERATED ← prove
    r"!k:A ring t n w.
        t subring_of k
        ==> (free_basis (integer_ring,subring_generated k t) (ring_of_int k)
                        n w <=>
             (!i. i < n ==> w i IN t) /\
             (!x. x IN t
                  ==> ?c. x = ring_sum k {i | i < n}
                               (\i. ring_mul k (ring_of_int k (c i)) (w i))) /\
             (!c. ring_sum k {i | i < n}
                    (\i. ring_mul k (ring_of_int k (c i)) (w i)) = ring_0 k
                  ==> !i. i < n ==> c i = &0))"
    (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [free_basis, INTEGER_RING, IN_UNIV, CARRIER_SUBRING_GENERATED_SUBRING, (← CONJUNCT2 SUBRING_GENERATED), RING_SUM_SUBRING_GENERATED] THEN ASM_CASES_TAC (← q r"!i. i < n ==> (w:num->A) i IN t") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"!c. {i | i IN {i | i < n} /\
             ring_mul k (ring_of_int k (c i)) ((w:num->A) i) IN t} =
        {i | i < n}") (fun th => REWRITE_TAC [th]) THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN ASM_MESON_TAC [IN_SUBRING_MUL, IN_SUBRING_INT])

  let FREE_BASIS_QUOTIENT_RING_HAS_SIZE ← prove
    r"!r:A ring n w j N.
        free_basis (integer_ring,r) (ring_of_int r) n w /\ ring_ideal r j
        ==> (ring_carrier(quotient_ring r j) HAS_SIZE N <=>
             int_cosets {i | i < n}
              {z | (!i. ~(i < n) ==> z i = &0) /\
                   ring_sum r {i | i < n}
                     (\i. ring_mul r (ring_of_int r (z i)) (w i)) IN j}
             HAS_SIZE N)"
    (REPEAT GEN_TAC THEN REWRITE_TAC [free_basis, INTEGER_RING, IN_UNIV] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"{i:num | i < n}"), (← q r"w:num->A")] RING_INT_LINCOMB) THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"\z:num->int. ring_sum r {i | i < n}
                    (\i. ring_mul r (ring_of_int r (z i)) ((w:num->A) i))"), (← q r"{i:num | i < n}"), (← q r"N:num")] QUOTIENT_RING_HAS_SIZE_INT_LINEAR) THEN ASM_REWRITE_TAC [IN_ELIM_THM, RING_SUM] THEN DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"x:A")) o (checkM (fun z1 => (do let z2 ← (do pure (Prod.snd (← (do let z3 ← (do let z4 ← (pure z1); pure (concl z4)); pure (strip_forall z3))))); pure (is_imp z2)))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:num->int") SUBST1_TAC) THEN EXISTS_TAC (← q r"\i. if i < n then (c:num->int) i else &0") THEN SIMP_TAC [] THEN MATCH_MP_TAC RING_SUM_EQ THEN SIMP_TAC [IN_ELIM_THM])

  let FREE_BASIS_INTEGER_RING_COORDINATES ← prove
    r"!r:A ring n w.
        free_basis (integer_ring,r) (ring_of_int r) n w
        ==> (!z. ring_sum r {i | i < n}
                   (\i. ring_mul r (ring_of_int r (z i)) (w i))
                 IN ring_carrier r) /\
            (!z z'. (!i. i IN {i | i < n} ==> z i = z' i)
                    ==> ring_sum r {i | i < n}
                          (\i. ring_mul r (ring_of_int r (z i)) (w i)) =
                        ring_sum r {i | i < n}
                          (\i. ring_mul r (ring_of_int r (z' i)) (w i))) /\
            (!x. x IN ring_carrier r
                 ==> ?z. (!i. ~(i IN {i | i < n}) ==> z i = &0) /\
                         ring_sum r {i | i < n}
                           (\i. ring_mul r (ring_of_int r (z i)) (w i)) = x) /\
            (!z. ring_sum r {i | i < n}
                   (\i. ring_mul r (ring_of_int r (z i)) (w i)) = ring_0 r
                 ==> !i. i IN {i | i < n} ==> z i = &0)"
    (REPEAT GEN_TAC THEN REWRITE_TAC [free_basis, INTEGER_RING, IN_UNIV, IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC [RING_SUM] THEN CONJ_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC [IN_ELIM_THM], X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"x:A")) o (checkM (fun z1 => (do let z2 ← (do pure (Prod.snd (← (do let z3 ← (do let z4 ← (pure z1); pure (concl z4)); pure (strip_forall z3))))); pure (is_imp z2)))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:num->int") SUBST1_TAC) THEN EXISTS_TAC (← q r"\i. if i < n then (c:num->int) i else &0") THEN SIMP_TAC [] THEN MATCH_MP_TAC RING_SUM_EQ THEN SIMP_TAC [IN_ELIM_THM]])

  let FREE_BASIS_IMP_NOETHERIAN_RING ← prove
    r"!r:A ring n w.
        free_basis (integer_ring,r) (ring_of_int r) n w ==> noetherian_ring r"
    (REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FREE_BASIS_INTEGER_RING_COORDINATES)) THEN FIRST_X_ASSUM (MP_TAC o (CONJUNCT1 o (REWRITE_RULE [free_basis, INTEGER_RING, IN_UNIV]))) THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"{i:num | i < n}"), (← q r"w:num->A")] RING_INT_LINCOMB) THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"\z:num->int. ring_sum r {i | i < n}
                    (\i. ring_mul r (ring_of_int r (z i)) ((w:num->A) i))"), (← q r"{i:num | i < n}")] NOETHERIAN_RING_INT_LINEAR) THEN REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT])

  let FREE_BASIS_QUOTIENT_RING_INTEGER ← prove
    r"!r:A ring n w m.
        free_basis (integer_ring,r) (ring_of_int r) n w /\ ~(m = &0)
        ==> ring_carrier(quotient_ring r (ideal_generated r {ring_of_int r m}))
            HAS_SIZE (num_of_int(abs m) EXP n)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FREE_BASIS_INTEGER_RING_COORDINATES)) THEN FIRST_X_ASSUM (MP_TAC o (CONJUNCT1 o (REWRITE_RULE [free_basis, INTEGER_RING, IN_UNIV]))) THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"{i:num | i < n}"), (← q r"w:num->A")] RING_INT_LINCOMB) THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"\z:num->int. ring_sum r {i | i < n}
                    (\i. ring_mul r (ring_of_int r (z i)) ((w:num->A) i))"), (← q r"{i:num | i < n}"), (← q r"m:int")] QUOTIENT_RING_INTEGER_INT_LINEAR) THEN REWRITE_TAC [CARD_NUMSEG_LT] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT])

  let RING_OF_INTEGERS_DISCRIMINANT ← prove
    r"!k:A ring n g.
        number_field k /\
        free_basis (subfield_generated k {ring_0 k},k) I n g /\
        (!i. i < n ==> g i IN ring_carrier(ring_of_integers k))
        ==> ?D. ~(ring_of_int k D = ring_0 k) /\
                !x. x IN ring_carrier(ring_of_integers k)
                    ==> ?c. ring_mul k (ring_of_int k D) x =
                            ring_sum k {i | i < n}
                              (\i. ring_mul k (ring_of_int k (c i)) (g i))"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN SUBGOAL_THEN (← q r"field(subfield_generated k {ring_0 k:A}) /\
    ring_homomorphism(subfield_generated k {ring_0 k},k) (I:A->A) /\
    {ring_of_int k m:A | m IN (:int)} subring_of
    subfield_generated k {ring_0 k} /\
    ring_0(subfield_generated k {ring_0 k}) = ring_0 k /\
    ring_mul(subfield_generated k {ring_0 k}) = ring_mul k /\
    (!x. x IN ring_carrier(subfield_generated k {ring_0 k})
         ==> x IN ring_carrier k)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, (← CONJUNCT2 SUBFIELD_GENERATED)] THEN MP_TAC (← ISPEC (← q r"subfield_generated k {ring_0 k:A}") PRIME_SUBRING) THEN SIMP_TAC [RING_OF_INT_SUBFIELD_GENERATED, (← GSYM SUBSET), RING_CARRIER_SUBFIELD_GENERATED_SUBSET], ALL_TAC] THEN ABBREV_TAC (← q r"Q = subfield_generated k {ring_0 k:A}") THEN ABBREV_TAC (← q r"Z = {ring_of_int k m:A | m IN (:int)}") THEN SUBGOAL_THEN (← q r"!x y. x IN ring_carrier(ring_of_integers k) /\
          y IN ring_carrier(ring_of_integers k)
          ==> algebra_trace (Q,k) I (ring_mul k x y) IN (Z:A->bool)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["Q", "Z"] THEN REWRITE_TAC [IN_ELIM_THM, IN_UNIV] THEN MATCH_MP_TAC NUMBER_FIELD_TRACE_INTEGRAL_Q THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBRING], ALL_TAC] THEN SUBGOAL_THEN (← q r"basis_discriminant (Q,k) I n (g:num->A) IN Z") MP_TAC THENL [REWRITE_TAC [basis_discriminant] THEN MATCH_MP_TAC RING_DET_SUBRING THEN ASM_SIMP_TAC [IN_ELIM_THM], EXPAND_TAC "Z" THEN REWRITE_TAC [IN_ELIM_THM, IN_UNIV] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"D:int") THEN DISCH_TAC] THEN CONJ_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"Q:A ring"), (← q r"k:A ring"), (← q r"n:num"), (← q r"g:num->A")] BASIS_DISCRIMINANT_NONZERO) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN EXPAND_TAC "Q" THEN REWRITE_TAC [(← CONJUNCT2 SUBFIELD_GENERATED), RING_OF_NUM_SUBFIELD_GENERATED] THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_CHAR_EQ_0) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"g:num->A")] NUMBER_FIELD_FREE_BASIS_DEGREE) THEN MP_TAC (← ISPEC (← q r"k:A ring") NUMBER_FIELD_DEGREE_POS) THEN ASM_REWRITE_TAC [] THEN ARITH_TAC, X_GEN_TAC (← q r"x:A") THEN DISCH_TAC] THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_SIMP_TAC [(← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET)], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"Q:A ring"), (← q r"k:A ring"), (← q r"n:num"), (← q r"g:num->A"), (← q r"Z:A->bool"), (← q r"x:A")] BASIS_DISCRIMINANT_TIMES_COORD) THEN ASM_SIMP_TAC [I_THM] THEN EXPAND_TAC "Z" THEN REWRITE_TAC [IN_ELIM_THM, IN_UNIV] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"c:num->int") (LABEL_TAC "c")) o (REWRITE_RULE [RIGHT_IMP_EXISTS_THM, SKOLEM_THM])) THEN EXISTS_TAC (← q r"c:num->int") THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"Q:A ring"), (← q r"k:A ring"), (← q r"n:num"), (← q r"g:num->A"), (← q r"x:A")] BASIS_COORDINATES) THEN ASM_REWRITE_TAC [I_THM] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (fun th => tactic_of do pure (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [(← SYM th)]))) THEN wPart lhand (rand o rand) RING_SUM_LMUL THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_OF_INT, FINITE_NUMSEG_LT, IN_ELIM_THM, RING_MUL, (← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET)], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN REMOVE_THEN "c" (MP_TAC o (SPEC (← q r"i:num"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_MUL_ASSOC THEN ASM_SIMP_TAC [RING_OF_INT, (← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET)])

  let RING_OF_INTEGERS_FREE ← prove
    r"!k:A ring.
        number_field k
        ==> ?w. free_basis (integer_ring,ring_of_integers k) (ring_of_int k)
                  (extension_degree (subfield_generated k {ring_0 k},k) I) w"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN FIRST_ASSUM ((X_CHOOSE_THEN (← q r"g:num->A") STRIP_ASSUME_TAC) o (MATCH_MP NUMBER_FIELD_INTEGRAL_FREE_BASIS)) THEN ABBREV_TAC (← q r"n = extension_degree (subfield_generated k {ring_0 k:A},k) I") THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"g:num->A")] RING_OF_INTEGERS_DISCRIMINANT) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"D:int") STRIP_ASSUME_TAC) THEN ONCE_REWRITE_TAC [(← GSYM (← CONJUNCT2 RING_OF_INTEGERS_SUBRING))] THEN SIMP_TAC [FREE_BASIS_INTEGER_RING_SUBRING_GENERATED, RING_OF_INTEGERS_SUBRING] THEN MATCH_MP_TAC RING_INT_LINCOMB_SANDWICH THEN MAP_EVERY EXISTS_TAC [(← q r"g:num->A"), (← q r"D:int")] THEN ASM_SIMP_TAC [RING_OF_INTEGERS_SUBSET, (← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET)] THEN REPEAT CONJ_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_SUBRING_SUB THEN ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBRING], GEN_TAC THEN MATCH_MP_TAC IN_SUBRING_SUM THEN ASM_SIMP_TAC [RING_OF_INTEGERS_SUBRING, IN_ELIM_THM, IN_SUBRING_MUL, IN_SUBRING_INT], X_GEN_TAC (← q r"c:num->int") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"\i:num. ring_of_int (k:A ring) (c i)")) o (CONJUNCT2 o (CONJUNCT2 o (GEN_REWRITE_RULE id [free_basis]))))) THEN ASM_REWRITE_TAC [I_THM, RING_OF_INT_IN_SUBFIELD_GENERATED, (← CONJUNCT2 SUBFIELD_GENERATED)] THEN ASM_SIMP_TAC [RING_OF_INT_EQ_0_CHAR_0]])

  let COUNTABLE_RING_OF_INTEGERS ← prove
    r"!k:A ring.
        number_field k ==> COUNTABLE(ring_carrier(ring_of_integers k))"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM ((X_CHOOSE_TAC (← q r"w:num->A")) o (MATCH_MP RING_OF_INTEGERS_FREE)) THEN ABBREV_TAC (← q r"n = extension_degree (subfield_generated k {ring_0 k},k:A ring) I") THEN MATCH_MP_TAC COUNTABLE_SUBSET THEN EXISTS_TAC (← q r"IMAGE (\c:num->int.
             ring_sum (ring_of_integers k) {i | i < n}
              (\i. ring_mul (ring_of_integers k) (ring_of_int k (c i))
                            ((w:num->A) i)))
          {c | IMAGE c {i | i < n} SUBSET (:int) /\
               {i | ~(c i = (\i. &0) i)} SUBSET {i | i < n} /\
               FINITE {i | ~(c i = (\i. &0) i)}}") THEN CONJ_TAC THENL [MATCH_MP_TAC COUNTABLE_IMAGE THEN MATCH_MP_TAC COUNTABLE_RESTRICTED_FUNSPACE THEN SIMP_TAC [INT_COUNTABLE, FINITE_IMP_COUNTABLE, FINITE_NUMSEG_LT], ALL_TAC] THEN REWRITE_TAC [SUBSET, IN_IMAGE, IN_ELIM_THM, SUBSET_UNIV] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"x:A")) o (CONJUNCT1 o (CONJUNCT2 o (GEN_REWRITE_RULE id [free_basis]))))) THEN ASM_REWRITE_TAC [INTEGER_RING, IN_UNIV] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:num->int") SUBST1_TAC) THEN EXISTS_TAC (← q r"\i. if i < n then (c:num->int) i else &0") THEN CONJ_TAC THENL [MATCH_MP_TAC RING_SUM_EQ THEN SIMP_TAC [IN_ELIM_THM], CONJ_TAC THENL [REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN MESON_TAC [], MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{i:num | i < n}") THEN REWRITE_TAC [FINITE_NUMSEG_LT, SUBSET, IN_ELIM_THM] THEN MESON_TAC []]])

  let RING_OF_INTEGERS_FREE_BASIS_FIELD ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"q /\ (q ==> p) ==> p /\ q")
    prove
      r"!k:A ring n w.
          number_field k /\
          free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w
          ==> n = extension_degree (subfield_generated k {ring_0 k},k) I /\
              free_basis (subfield_generated k {ring_0 k},k) I n w"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC [NUMBER_FIELD_FREE_BASIS_DEGREE]] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN UNDISCH_TAC (← q r"free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n
                 (w:num->A)") THEN ONCE_REWRITE_TAC [(← GSYM (← CONJUNCT2 RING_OF_INTEGERS_SUBRING))] THEN SIMP_TAC [FREE_BASIS_INTEGER_RING_SUBRING_GENERATED, RING_OF_INTEGERS_SUBRING, RING_OF_INTEGERS] THEN STRIP_TAC THEN MATCH_MP_TAC FREE_BASIS_PRIME_SUBFIELD_INT_LINCOMB THEN ASM_SIMP_TAC [(← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET)] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A")] NUMBER_FIELD_INTEGRAL_MULTIPLE) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"d:int") THEN STRIP_TAC THEN ASM_SIMP_TAC [])

  let NOETHERIAN_RING_OF_INTEGERS ← prove
    r"!k:A ring. number_field k ==> noetherian_ring(ring_of_integers k)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM ((X_CHOOSE_TAC (← q r"w:num->A")) o (MATCH_MP RING_OF_INTEGERS_FREE)) THEN MATCH_MP_TAC FREE_BASIS_IMP_NOETHERIAN_RING THEN MAP_EVERY EXISTS_TAC [(← q r"extension_degree (subfield_generated (k:A ring) {ring_0 k},k) I"), (← q r"w:num->A")] THEN ASM_REWRITE_TAC [RING_OF_INTEGERS, RING_OF_INTEGERS_SUBRING])

  let INTEGRALLY_CLOSED_RING_OF_INTEGERS ← prove
    r"!k:A ring. field k ==> integrally_closed(ring_of_integers k)"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [ring_of_integers] THEN MATCH_MP_TAC INTEGRALLY_CLOSED_INTEGRAL_CLOSURE THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT])

  let RING_OF_INTEGERS_IDEAL_INTEGER ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"ring_add r (ring_mul r x y) (ring_add r (ring_mul r c (ring_1 r))
                                              (ring_mul r x s)) =
      ring_add r c (ring_mul r x (ring_add r y (s:A)))"
    let r2 ← RING_RULE q1
    let q3 ← q r"ring_mul r a (ring_mul r b c) =
          ring_mul r b (ring_mul r (a:A) c)"
    let r4 ← RING_RULE q3
    let q5 ← q r"ring_sum r {i | i < p}
          (\i. ring_mul r x (ring_mul r (c(SUC i)) (ring_pow r (x:A) i)))"
    let q6 ← q r"ring_sum r {i | i < p}
        (\i. ring_mul r (c(SUC i)) (ring_mul r x (ring_pow r x i))) =
      ring_mul r x (ring_sum r {i | i < p}
                     (\i. ring_mul r (c(SUC i)) (ring_pow r (x:A) i)))"
    let q7 ← q r"~(0 = SUC n)"
    let r8 ← ARITH_RULE q7
    let q9 ← q r"{i | i < SUC p} = 0 INSERT IMAGE SUC {i | i < p}"
    let p10 ← prove r"!r:A ring x p c.
        x IN ring_carrier r /\ (!i. c i IN ring_carrier r)
        ==> ring_add r (ring_pow r x (SUC p))
                       (ring_sum r {i | i < SUC p}
                          (\i. ring_mul r (c i) (ring_pow r x i))) =
            ring_add r (c 0)
              (ring_mul r x
                 (ring_add r (ring_pow r x p)
                    (ring_sum r {i | i < p}
                       (\i. ring_mul r (c(SUC i)) (ring_pow r x i)))))" (REPEAT STRIP_TAC THEN SUBGOAL_THEN q9 SUBST1_TAC THENL [REWRITE_TAC [EXTENSION, IN_INSERT, IN_IMAGE, IN_ELIM_THM] THEN INDUCT_TAC THEN REWRITE_TAC [NOT_SUC, SUC_INJ, LT_0, LT_SUC] THEN MESON_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [RING_SUM_CLAUSES, FINITE_IMAGE, FINITE_NUMSEG_LT, RING_MUL, RING_POW, IN_IMAGE, r8] THEN SIMP_TAC [RING_SUM_IMAGE, SUC_INJ] THEN REWRITE_TAC [o_DEF, ring_pow] THEN SUBGOAL_THEN q6 SUBST1_TAC THENL [TRANS_TAC EQ_TRANS q5 THEN CONJ_TAC THENL [MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN REWRITE_TAC [] THEN MATCH_MP_TAC r4 THEN ASM_SIMP_TAC [RING_POW], MATCH_MP_TAC RING_SUM_LMUL THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, RING_MUL, RING_POW]], ALL_TAC] THEN MATCH_MP_TAC r2 THEN ASM_SIMP_TAC [RING_POW, RING_SUM])
    let lemma := p10
    let q11 ← q r"y:A"
    let q12 ← q r"x:A"
    let q13 ← q r"j:A->bool"
    let q14 ← q r"ring_of_integers k:A ring"
    let v15 ← ISPECL [q14, q13, q12, q11] IN_RING_IDEAL_RMUL
    let q16 ← q r"m:int"
    let q17 ← q r"y:A"
    let q18 ← q r"m:int"
    let q19 ← q r"c:num->int"
    let q20 ← q r"n:num"
    let q21 ← q r"c:num->int"
    let q22 ← q r"n:num"
    let q23 ← q r"(x:A) IN ok"
    let q25 ← q r"x:A"
    let q26 ← q r"ring_of_int k:int->A"
    let q27 ← q r"k:A ring"
    let q28 ← q r"integer_ring"
    let v29 ← ISPECL [q28, q27, q26, q25] INTEGRAL_ELEMENT_EXPLICIT
    let q30 ← q r"ring_add r a (ring_mul r x y) = ring_0 r
        ==> a = ring_mul r x (ring_neg r (y:A))"
    let r31 ← RING_RULE q30
    let q35 ← q r"ring_neg k (ring_add k (ring_pow k x n)
          (ring_sum k {i | i < n}
             (\i. ring_mul k (ring_of_int k ((c:num->int) (SUC i)))
                             (ring_pow k (x:A) i))))"
    let q36 ← q r"(c:num->int) 0"
    let q37 ← q r"\i. (c:num->int) (SUC i)"
    let q38 ← q r"n = 0"
    let q39 ← q r"(c:num->int) 0 = &0"
    let q40 ← q r"!y:A. y IN ok ==> y IN ring_carrier k"
    let q41 ← q r"ring_add k (ring_pow k x n)
        (ring_sum k {i | i < n}
           (\i. ring_mul k (ring_of_int k ((c:num->int) (SUC i)))
                           (ring_pow k x i))) IN (ok:A->bool)"
    let q42 ← q r"\i. ring_of_int (k:A ring) ((c:num->int) i)"
    let q43 ← q r"n:num"
    let q44 ← q r"x:A"
    let q45 ← q r"k:A ring"
    let v46 ← ISPECL [q45, q44, q43, q42] lemma
    let q47 ← q r"c:num->int"
    let q48 ← q r"!n c. 0 < n /\
          ring_add k (ring_pow k x n)
            (ring_sum k {i | i < n}
               (\i. ring_mul k (ring_of_int k (c i)) (ring_pow k x i))) =
          ring_0 k
          ==> ?m y. ~(m = &0) /\ (y:A) IN ok /\
                    ring_of_int k m = ring_mul k x y"
    let q49 ← q r"(ok:A->bool) subring_of k /\ (x:A) IN ok"
    let q50 ← q r"ok = ring_carrier(ring_of_integers(k:A ring))"
    let q51 ← q r"?x:A. x IN j /\ ~(x = ring_0 k)"
    prove
      r"!k:A ring j.
          field k /\ ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
          ==> ?m. ~(m = &0) /\ ring_of_int k m IN j"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN q51 STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP IN_RING_IDEAL_0)) THEN REWRITE_TAC [RING_OF_INTEGERS, RING_OF_INTEGERS_SUBRING] THEN ASM SET_TAC [], ALL_TAC] THEN ABBREV_TAC q50 THEN SUBGOAL_THEN q49 STRIP_ASSUME_TAC THENL [EXPAND_TAC "ok" THEN REWRITE_TAC [RING_OF_INTEGERS, RING_OF_INTEGERS_SUBRING] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP RING_IDEAL_IMP_SUBSET)) THEN ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN q48 ASSUME_TAC THENL [INDUCT_TAC THEN REWRITE_TAC [LT_REFL, LT_0] THEN X_GEN_TAC q47 THEN MP_TAC v46 THEN ANTS_TAC THENL [REWRITE_TAC [RING_OF_INT] THEN ASM_MESON_TAC [subring_of, SUBSET], REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC] THEN SUBGOAL_THEN q41 ASSUME_TAC THENL [MATCH_MP_TAC IN_SUBRING_ADD THEN ASM_SIMP_TAC [IN_SUBRING_POW, IN_SUBRING_SUM, IN_SUBRING_MUL, IN_SUBRING_INT], ALL_TAC] THEN SUBGOAL_THEN q40 ASSUME_TAC THENL [ASM_MESON_TAC [subring_of, SUBSET], ALL_TAC] THEN ASM_CASES_TAC q39 THEN ASM_REWRITE_TAC [RING_OF_INT_0] THENL [ASM_SIMP_TAC [RING_ADD_LZERO, RING_MUL, FIELD_IMP_INTEGRAL_DOMAIN, INTEGRAL_DOMAIN_MUL_EQ_0] THEN ASM_CASES_TAC q38 THENL [ASM_REWRITE_TAC [LT, EMPTY_GSPEC, RING_SUM_CLAUSES, ring_pow] THEN ASM_SIMP_TAC [RING_ADD_RZERO, RING_1, FIELD_NONTRIVIAL], DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC q37)) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC], DISCH_TAC THEN EXISTS_TAC q36 THEN EXISTS_TAC q35 THEN ASM_SIMP_TAC [IN_SUBRING_NEG] THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun z32 => (do let z33 ← (do let z34 ← (pure z32); pure (concl z34)); pure (is_eq z33))))) THEN MATCH_MP_TAC r31 THEN ASM_SIMP_TAC [RING_OF_INT]], ALL_TAC] THEN MP_TAC v29 THEN REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, INTEGER_RING, IN_UNIV] THEN DISCH_THEN (fun z24 => tactic_of do pure (MP_TAC (← (do pure (Prod.fst (← (do pure (← EQ_IMP_RULE z24)))))))) THEN ANTS_TAC THENL [UNDISCH_TAC q23 THEN EXPAND_TAC "ok" THEN REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM], DISCH_THEN ((X_CHOOSE_THEN q22 (X_CHOOSE_THEN q21 STRIP_ASSUME_TAC)) o CONJUNCT2)] THEN FIRST_X_ASSUM (MP_TAC o (SPECL [q20, q19])) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN q18 (X_CHOOSE_THEN q17 STRIP_ASSUME_TAC)) THEN EXISTS_TAC q16 THEN ASM_REWRITE_TAC [] THEN MP_TAC v15 THEN ASM_REWRITE_TAC [RING_OF_INTEGERS, RING_OF_INTEGERS_SUBRING])

  let RING_OF_INTEGERS_FINITE_QUOTIENT ← prove
    r"!k:A ring j.
        number_field k /\ ring_ideal (ring_of_integers k) j /\
        ~(j = {ring_0 k})
        ==> FINITE(ring_carrier(quotient_ring (ring_of_integers k) j))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"j:A->bool")] RING_OF_INTEGERS_IDEAL_INTEGER) THEN ASM_SIMP_TAC [NUMBER_FIELD_IMP_FIELD] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"m:int") STRIP_ASSUME_TAC) THEN FIRST_ASSUM ((X_CHOOSE_TAC (← q r"w:num->A")) o (MATCH_MP RING_OF_INTEGERS_FREE)) THEN MATCH_MP_TAC FINITE_QUOTIENT_RING_MONO THEN EXISTS_TAC (← q r"ideal_generated (ring_of_integers k) {ring_of_int (k:A ring) m}") THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET], MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"extension_degree (subfield_generated (k:A ring) {ring_0 k},k) I"), (← q r"w:num->A"), (← q r"m:int")] FREE_BASIS_QUOTIENT_RING_INTEGER) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS, RING_OF_INTEGERS_SUBRING] THEN SIMP_TAC [HAS_SIZE]])

  let RING_OF_INTEGERS_FINITE_RESIDUE_FIELDS ← prove
    r"!k:A ring.
        number_field k
        ==> !P. prime_ideal (ring_of_integers k) P /\
                ~(P = {ring_0(ring_of_integers k)})
                ==> FINITE(ring_carrier(quotient_ring (ring_of_integers k) P))"
    (REWRITE_TAC [RING_OF_INTEGERS] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL])

  let RING_OF_INTEGERS_IDEAL_NORM_INTEGER ← prove
    r"!k:A ring m.
        number_field k /\ ~(m = &0)
        ==> ideal_norm (ring_of_integers k)
              (ideal_generated (ring_of_integers k) {ring_of_int k m}) =
            num_of_int(abs m) EXP
            extension_degree (subfield_generated k {ring_0 k},k) I"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM ((X_CHOOSE_TAC (← q r"w:num->A")) o (MATCH_MP RING_OF_INTEGERS_FREE)) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"extension_degree (subfield_generated (k:A ring) {ring_0 k},k) I"), (← q r"w:num->A"), (← q r"m:int")] FREE_BASIS_QUOTIENT_RING_INTEGER) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS, RING_OF_INTEGERS_SUBRING] THEN SIMP_TAC [HAS_SIZE, ideal_norm])

  -- @@RETURN BEGIN
  return { QUOTIENT_RING_HAS_SIZE_INT_LINEAR, NOETHERIAN_RING_INT_LINEAR,
           QUOTIENT_RING_INTEGER_INT_LINEAR, FREE_BASIS_INTEGER_RING_SUBRING_GENERATED,
           FREE_BASIS_QUOTIENT_RING_HAS_SIZE, FREE_BASIS_INTEGER_RING_COORDINATES,
           FREE_BASIS_IMP_NOETHERIAN_RING, FREE_BASIS_QUOTIENT_RING_INTEGER,
           RING_OF_INTEGERS_DISCRIMINANT, RING_OF_INTEGERS_FREE,
           COUNTABLE_RING_OF_INTEGERS, RING_OF_INTEGERS_FREE_BASIS_FIELD,
           NOETHERIAN_RING_OF_INTEGERS, INTEGRALLY_CLOSED_RING_OF_INTEGERS,
           RING_OF_INTEGERS_IDEAL_INTEGER, RING_OF_INTEGERS_FINITE_QUOTIENT,
           RING_OF_INTEGERS_FINITE_RESIDUE_FIELDS, RING_OF_INTEGERS_IDEAL_NORM_INTEGER }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- ring_of_integers.ml phrases from line 792 to 792                       -/
/- ---------------------------------------------------------------------- -/

structure RingOfIntegers02 where
  -- @@FIELDS
  DEDEKIND_RING_OF_INTEGERS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupRingOfIntegers02 [HolBase] (D : RingOfIntegersDeps) (BRingOfIntegers01 : RingOfIntegers01) :
    ExceptT String IO RingOfIntegers02 := do
  -- @@SCOPE BEGIN
  let { FIELD_QUOTIENT_RING, FINITE_INTEGRAL_DOMAIN_IMP_FIELD,
        INTEGRAL_DOMAIN_QUOTIENT_RING, INTEGRAL_DOMAIN_RING_OF_INTEGERS,
        NUMBER_FIELD_IMP_FIELD, PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS,
        RING_OF_INTEGERS_SUBRING, dedekind_domain, .. } := D.core1
  let { INTEGRALLY_CLOSED_RING_OF_INTEGERS, NOETHERIAN_RING_OF_INTEGERS,
        RING_OF_INTEGERS_FINITE_QUOTIENT, .. } := BRingOfIntegers01
  -- @@SCOPE END

  let DEDEKIND_RING_OF_INTEGERS ← prove
    r"!k:A ring. number_field k ==> dedekind_domain(ring_of_integers k)"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [dedekind_domain] THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_RING_OF_INTEGERS, NUMBER_FIELD_IMP_FIELD, NOETHERIAN_RING_OF_INTEGERS, INTEGRALLY_CLOSED_RING_OF_INTEGERS] THEN X_GEN_TAC (← q r"p:A->bool") THEN REWRITE_TAC [RING_OF_INTEGERS, RING_OF_INTEGERS_SUBRING] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers k) (p:A->bool)") ASSUME_TAC THENL [ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], ALL_TAC] THEN ASM_SIMP_TAC [(← GSYM FIELD_QUOTIENT_RING)] THEN MATCH_MP_TAC FINITE_INTEGRAL_DOMAIN_IMP_FIELD THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_QUOTIENT_RING, RING_OF_INTEGERS_FINITE_QUOTIENT])

  -- @@RETURN BEGIN
  return { DEDEKIND_RING_OF_INTEGERS }
  -- @@RETURN END

end HolANT.RingOfIntegers
