/- ========================================================================= -/
/- ANT: Ideal classes of a domain, their invariance under ring ...         -/
/- ========================================================================= -/
/- File: HolANT/Classgroup.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/classgroup.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antclassgroupdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/isum.ml, Library/products.ml, ANT/algmisc.ml, ANT/ideal_arith.ml, ANT/integral.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.Classgroup fills them).

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
import HolANT.NormIndex

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
open HolANT.NormIndex

namespace HolANT.Classgroup

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ALGEBRA_NORM_FREE_BASIS CARD_EQ_0 CARD_EQ_CARD_IMP CARD_FINITE_CONG
   CARD_NUMSEG_LT CARD_SUBSET DEDEKIND_IDEAL_CLASS_COPRIME
   DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES
   DEDEKIND_IMP_INTEGRAL_DOMAIN DEDEKIND_RING_OF_INTEGERS EQ_C_BIJECTIONS EQ_IMP
   EXISTS_IN_IMAGE EXTENSION FINITE_CROSS FINITE_IDEALS_SUPERSET FINITE_IMAGE
   FINITE_NUMSEG FINITE_NUMSEG_LT FINITE_SUBSET FINITE_UNIONS FORALL_IN_GSPEC
   FORALL_IN_IMAGE FORALL_PAIR_THM FREE_BASIS_IN_CARRIER FUN_EQ_THM HAS_SIZE
   HAS_SIZE_FUNSPACE HAS_SIZE_IMAGE_INJ HAS_SIZE_NUMSEG_LE HAS_SIZE_NUMSEG_LT
   IDEAL_CLASS_PRINCIPAL IDEAL_CLASS_REFL IDEAL_CLASS_SYM IDEAL_CLASS_TRANS
   IDEAL_GENERATED_MINIMAL IDEAL_NORM_GT_1 IDEAL_NORM_IN_IDEAL IDEAL_NORM_POS
   IDEAL_PROD_ASSOC IDEAL_PROD_COMM IDEAL_PROD_EQ_ZERO INTEGER_RING
   INTEGER_RING_SUM INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING
   INTEGRAL_DOMAIN_RING_OF_INTEGERS INT_ABS_MUL INT_ABS_POS INT_DET_BOUND
   INT_LE_LMUL INT_LE_LMUL_EQ INT_LE_MUL INT_LE_MUL2 INT_LE_TRANS INT_MUL_ASSOC
   INT_MUL_SYM INT_OF_NUM_EQ INT_OF_NUM_LE INT_OF_NUM_LT INT_OF_NUM_MUL
   INT_OF_NUM_OF_INT INT_OF_NUM_POW INT_POS INT_POW_LE INT_POW_MUL INT_SUB_0
   IN_CROSS IN_ELIM_THM IN_IDEAL_CLASS IN_IDEAL_CLASS_ISOMORPHIC_IMAGE
   IN_IDEAL_GENERATED_SELF IN_IMAGE IN_NUMSEG IN_SING IN_UNIONS IN_UNIV
   ISOMORPHIC_RING_RING_OF_INTEGERS ISUM_ABS_BOUND LEFT_IMP_EXISTS_THM
   MEMBER_NOT_EMPTY MONO_EXISTS MUL_MATRIX_RING_SUM NOT_FORALL_THM NOT_IMP
   NUMBER_FIELD_DEGREE_POS NUMBER_FIELD_IDEAL_NORM_MUL_Q
   NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_Q NUMBER_FIELD_IMP_FIELD
   NUMBER_FIELD_NORM_INTEGRAL_BASIS NUM_ROOT_FLOOR PID PRIME_IMP_RING_IDEAL
   PRINCIPAL_IDEAL_0 PRINCIPAL_IDEAL_CLASS PSUBSET QUOTIENT_RING_CARRIER
   RING_CHAR_EQ_0 RING_COSET_EQ RING_HOMOMORPHISM_INTEGER_RING_OF_INT
   RING_IDEAL_CARRIER RING_IDEAL_IDEAL_GENERATED RING_IDEAL_IDEAL_PROD
   RING_IDEAL_IMP_SUBSET RING_INT_LINCOMB RING_ISOMORPHISMS_ISOMORPHISM
   RING_ISOMORPHISMS_SYM RING_MONOMORPHISM_INTEGER_RING_OF_INT RING_OF_INTEGERS
   RING_OF_INTEGERS_FINITE_QUOTIENT RING_OF_INTEGERS_FREE
   RING_OF_INTEGERS_FREE_BASIS_FIELD RING_OF_INT_IN_RING_OF_INTEGERS
   RING_OF_INT_OF_NUM RING_SUM SING_SUBSET SUBSET UPPER_BOUND_FINITE_SET_INT
   free_basis ideal_norm isomorphic_ring number_field prime_ideal proper_ideal
   ring_isomorphism ring_monomorphism trivial_ring : thm)
  deriving Inhabited

/-- What classgroup.ml uses from Session besides theorems. -/
structure ClassgroupDeps where
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
/- classgroup.ml phrases from line 73 to 670                              -/
/- ---------------------------------------------------------------------- -/

structure Classgroup where
  -- @@FIELDS
  ideal_classes : thm
  class_number : thm
  IDEAL_CLASS_EQ : thm
  INTEGRAL_DOMAIN_UNIT_IDEAL : thm
  DEDEKIND_PID_EQ_CLASS_NUMBER_1 : thm
  FREE_BASIS_IDEAL_BOX_PRINCIPLE : thm
  NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM : thm
  NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM : thm
  NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2 : thm
  FREE_BASIS_NORM_BOUND : thm
  NUMBER_FIELD_IDEAL_SMALL_ELEMENT : thm
  NUMBER_FIELD_IDEAL_CLASS_BOUND_EXPLICIT : thm
  NUMBER_FIELD_IDEAL_CLASS_BOUND : thm
  NUMBER_FIELD_CLASS_GROUP_FINITE : thm
  NUMBER_FIELD_CLASS_NUMBER_POS : thm
  NUMBER_FIELD_PID_EQ_CLASS_NUMBER_1 : thm
  NUMBER_FIELD_IDEAL_CLASS_COPRIME : thm
  IDEAL_CLASS_ISOMORPHIC_IMAGE : thm
  ISOMORPHIC_RING_IDEAL_CLASSES : thm
  ISOMORPHIC_RING_CLASS_NUMBER : thm
  NUMBER_FIELD_CLASS_NUMBER_ISOMORPHIC : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupClassgroup [HolBase] (D : ClassgroupDeps) :
    ExceptT String IO Classgroup := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, HAS_SIZE_CONV, INT_ARITH,
        INT_ARITH_TAC, MESON_TAC, SET_RULE, SET_TAC, TAUT, new_definition, .. } := D
  let { ALGEBRA_NORM_FREE_BASIS, CARD_EQ_0, CARD_EQ_CARD_IMP, CARD_FINITE_CONG,
        CARD_NUMSEG_LT, CARD_SUBSET, DEDEKIND_IDEAL_CLASS_COPRIME,
        DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE, DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES,
        DEDEKIND_IMP_INTEGRAL_DOMAIN, DEDEKIND_RING_OF_INTEGERS, EQ_C_BIJECTIONS,
        EQ_IMP, EXISTS_IN_IMAGE, EXTENSION, FINITE_CROSS, FINITE_IDEALS_SUPERSET,
        FINITE_IMAGE, FINITE_NUMSEG, FINITE_NUMSEG_LT, FINITE_SUBSET, FINITE_UNIONS,
        FORALL_IN_GSPEC, FORALL_IN_IMAGE, FORALL_PAIR_THM, FREE_BASIS_IN_CARRIER,
        FUN_EQ_THM, HAS_SIZE, HAS_SIZE_FUNSPACE, HAS_SIZE_IMAGE_INJ,
        HAS_SIZE_NUMSEG_LE, HAS_SIZE_NUMSEG_LT, IDEAL_CLASS_PRINCIPAL,
        IDEAL_CLASS_REFL, IDEAL_CLASS_SYM, IDEAL_CLASS_TRANS, IDEAL_GENERATED_MINIMAL,
        IDEAL_NORM_GT_1, IDEAL_NORM_IN_IDEAL, IDEAL_NORM_POS, IDEAL_PROD_ASSOC,
        IDEAL_PROD_COMM, IDEAL_PROD_EQ_ZERO, INTEGER_RING, INTEGER_RING_SUM,
        INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING, INTEGRAL_DOMAIN_RING_OF_INTEGERS,
        INT_ABS_MUL, INT_ABS_POS, INT_DET_BOUND, INT_LE_LMUL, INT_LE_LMUL_EQ,
        INT_LE_MUL, INT_LE_MUL2, INT_LE_TRANS, INT_MUL_ASSOC, INT_MUL_SYM,
        INT_OF_NUM_EQ, INT_OF_NUM_LE, INT_OF_NUM_LT, INT_OF_NUM_MUL, INT_OF_NUM_OF_INT,
        INT_OF_NUM_POW, INT_POS, INT_POW_LE, INT_POW_MUL, INT_SUB_0, IN_CROSS,
        IN_ELIM_THM, IN_IDEAL_CLASS, IN_IDEAL_CLASS_ISOMORPHIC_IMAGE,
        IN_IDEAL_GENERATED_SELF, IN_IMAGE, IN_NUMSEG, IN_SING, IN_UNIONS, IN_UNIV,
        ISOMORPHIC_RING_RING_OF_INTEGERS, ISUM_ABS_BOUND, LEFT_IMP_EXISTS_THM,
        MEMBER_NOT_EMPTY, MONO_EXISTS, MUL_MATRIX_RING_SUM, NOT_FORALL_THM, NOT_IMP,
        NUMBER_FIELD_DEGREE_POS, NUMBER_FIELD_IDEAL_NORM_MUL_Q,
        NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_Q, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_NORM_INTEGRAL_BASIS, NUM_ROOT_FLOOR, PID, PRIME_IMP_RING_IDEAL,
        PRINCIPAL_IDEAL_0, PRINCIPAL_IDEAL_CLASS, PSUBSET, QUOTIENT_RING_CARRIER,
        RING_CHAR_EQ_0, RING_COSET_EQ, RING_HOMOMORPHISM_INTEGER_RING_OF_INT,
        RING_IDEAL_CARRIER, RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_PROD,
        RING_IDEAL_IMP_SUBSET, RING_INT_LINCOMB, RING_ISOMORPHISMS_ISOMORPHISM,
        RING_ISOMORPHISMS_SYM, RING_MONOMORPHISM_INTEGER_RING_OF_INT, RING_OF_INTEGERS,
        RING_OF_INTEGERS_FINITE_QUOTIENT, RING_OF_INTEGERS_FREE,
        RING_OF_INTEGERS_FREE_BASIS_FIELD, RING_OF_INT_IN_RING_OF_INTEGERS,
        RING_OF_INT_OF_NUM, RING_SUM, SING_SUBSET, SUBSET, UPPER_BOUND_FINITE_SET_INT,
        free_basis, ideal_norm, isomorphic_ring, number_field, prime_ideal,
        proper_ideal, ring_isomorphism, ring_monomorphism, trivial_ring, .. } := D.core1
  -- @@SCOPE END

  let ideal_classes ← new_definition
    r"ideal_classes (r:A ring) =
  {ideal_class r j | j | ring_ideal r j /\ ~(j = {ring_0 r})}"

  let class_number ← new_definition
    r"class_number (r:A ring) = CARD(ideal_classes r)"

  let IDEAL_CLASS_EQ ← prove
    r"!r j k:A->bool.
        integral_domain r /\ ring_ideal r k /\ ~(k = {ring_0 r})
        ==> (ideal_class r j = ideal_class r k <=> k IN ideal_class r j)"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [EXTENSION] THEN EQ_TAC THENL [DISCH_THEN (MP_TAC o (SPEC (← q r"k:A->bool"))) THEN ASM_SIMP_TAC [IDEAL_CLASS_REFL], ASM_MESON_TAC [IDEAL_CLASS_SYM, IDEAL_CLASS_TRANS]])

  let INTEGRAL_DOMAIN_UNIT_IDEAL ← prove
    r"!r:A ring.
        integral_domain r
        ==> ring_ideal r (ring_carrier r) /\
            ~(ring_carrier r = {ring_0 r})"
    (GEN_TAC THEN DISCH_THEN (MP_TAC o (MATCH_MP INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING)) THEN SIMP_TAC [trivial_ring, RING_IDEAL_CARRIER])

  let DEDEKIND_PID_EQ_CLASS_NUMBER_1 ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"s = {c:B} ==> !x y. x IN s /\ y IN s ==> x = y")
    prove
      r"!r:A ring. dedekind_domain r ==> (PID r <=> ideal_classes r HAS_SIZE 1)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP INTEGRAL_DOMAIN_UNIT_IDEAL)) THEN CONV_TAC (RAND_CONV HAS_SIZE_CONV) THEN EQ_TAC THENL [DISCH_TAC THEN EXISTS_TAC (← q r"ideal_class r (ring_carrier r):(A->bool)->bool") THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [ideal_classes, IN_SING, IN_ELIM_THM] THEN X_GEN_TAC (← q r"c:(A->bool)->bool") THEN EQ_TAC THENL [DISCH_THEN (X_CHOOSE_THEN (← q r"j:A->bool") STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC [IDEAL_CLASS_EQ] THEN MATCH_MP_TAC PRINCIPAL_IDEAL_CLASS THEN ASM_MESON_TAC [PID], DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC []], DISCH_THEN (X_CHOOSE_TAC (← q r"c:(A->bool)->bool")) THEN ASM_REWRITE_TAC [PID] THEN X_GEN_TAC (← q r"j:A->bool") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"j = {ring_0 r:A}") THEN ASM_REWRITE_TAC [PRINCIPAL_IDEAL_0] THEN MATCH_MP_TAC IDEAL_CLASS_PRINCIPAL THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"ring_carrier r:A->bool")] IDEAL_CLASS_EQ) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN FIRST_X_ASSUM (MP_TAC o (MATCH_MP r1)) THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC [ideal_classes, IN_ELIM_THM] THEN ASM_MESON_TAC []])

  let FREE_BASIS_IDEAL_BOX_PRINCIPLE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(a:A) = b ==> b IN s ==> a IN s")
    let r2 ← INT_ARITH (← q r"&0 <= x /\ x <= t /\ &0 <= y /\ y <= t ==> abs(x - y:int) <= t")
    prove
      r"!r:A ring n w i t.
          free_basis (integer_ring,r) (ring_of_int r) n w /\
          ring_ideal r i /\ FINITE(ring_carrier(quotient_ring r i)) /\
          ideal_norm r i < (t + 1) EXP n
          ==> ?c. (!m. m < n ==> abs(c m) <= &t) /\
                  (?m. m < n /\ ~(c m = &0)) /\
                  ring_sum r {m | m < n}
                    (\m. ring_mul r (ring_of_int r (c m)) (w m)) IN i"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [free_basis]))) THEN ABBREV_TAC (← q r"x = \f:num->num. ring_sum r {m | m < n}
                         (\m. ring_mul r (ring_of_int r (&(f m))) (w m)):A") THEN SUBGOAL_THEN (← q r"!f:num->num. (x:(num->num)->A) f IN ring_carrier r") ASSUME_TAC THENL [EXPAND_TAC "x" THEN REWRITE_TAC [RING_SUM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"0"), (← q r"t + 1"), (← q r"{j:num | j <= t}"), (← q r"n:num"), (← q r"{m:num | m < n}")] HAS_SIZE_FUNSPACE) THEN REWRITE_TAC [HAS_SIZE_NUMSEG_LT, HAS_SIZE_NUMSEG_LE] THEN ABBREV_TAC (← q r"S = {f:num->num | (!m. m IN {m | m < n} ==> f m IN {j | j <= t}) /\
                        (!m. ~(m IN {m | m < n}) ==> f m = 0)}") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"~(!f g. f IN S /\ g IN S /\
              ring_coset r i ((x:(num->num)->A) f) = ring_coset r i (x g)
              ==> f = g)") MP_TAC THENL [DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"\f. ring_coset r i ((x:(num->num)->A) f)"), (← q r"S:(num->num)->bool"), (← q r"(t + 1) EXP n")] HAS_SIZE_IMAGE_INJ) THEN ASM_REWRITE_TAC [HAS_SIZE] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"IMAGE (\f. ring_coset r i ((x:(num->num)->A) f)) S"), (← q r"ring_carrier(quotient_ring r (i:A->bool))")] CARD_SUBSET) THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER] THEN UNDISCH_TAC (← q r"ideal_norm r (i:A->bool) < (t + 1) EXP n") THEN ASM_SIMP_TAC [ideal_norm, QUOTIENT_RING_CARRIER] THEN REWRITE_TAC [NOT_IMP] THEN DISCH_TAC THEN CONJ_TAC THENL [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN X_GEN_TAC (← q r"f:num->num") THEN DISCH_TAC THEN EXISTS_TAC (← q r"(x:(num->num)->A) f") THEN ASM_REWRITE_TAC [], ASM_ARITH_TAC], REWRITE_TAC [NOT_FORALL_THM, NOT_IMP, LEFT_IMP_EXISTS_THM]] THEN MAP_EVERY X_GEN_TAC [(← q r"f:num->num"), (← q r"g:num->num")] THEN EXPAND_TAC "S" THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN EXISTS_TAC (← q r"\m. &((f:num->num) m) - &((g:num->num) m):int") THEN REPEAT CONJ_TAC THENL [REPEAT STRIP_TAC THEN REWRITE_TAC [] THEN MATCH_MP_TAC r2 THEN ASM_SIMP_TAC [INT_POS, INT_OF_NUM_LE], UNDISCH_TAC (← q r"~(f:num->num = g)") THEN REWRITE_TAC [FUN_EQ_THM, NOT_FORALL_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"m:num") THEN DISCH_TAC THEN ASM_REWRITE_TAC [INT_SUB_0, INT_OF_NUM_EQ] THEN ASM_CASES_TAC (← q r"m:num < n") THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"~((f:num->num) m = g m)") THEN ASM_SIMP_TAC [], UNDISCH_TAC (← q r"ring_coset r i ((x:(num->num)->A) f) = ring_coset r i (x g)") THEN ASM_SIMP_TAC [RING_COSET_EQ] THEN MATCH_MP_TAC r1 THEN EXPAND_TAC "x" THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"{m:num | m < n}"), (← q r"w:num->A")] RING_INT_LINCOMB) THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [(← CONJUNCT1 (← CONJUNCT2 th))]))])

  let NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!x:A s a. x IN s /\ ~(x = a) ==> ~(s = {a})")
    prove
      r"!k:A ring c.
          number_field k
          ==> FINITE {j | ring_ideal (ring_of_integers k) j /\
                          ~(j = {ring_0 k}) /\
                          ideal_norm (ring_of_integers k) j <= c}"
      (REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"UNIONS (IMAGE (\m. {j | ring_ideal (ring_of_integers k) j /\
                              ideal_generated (ring_of_integers k)
                                {ring_of_num k m} SUBSET j})
                    (1..c)):(A->bool)->bool") THEN CONJ_TAC THENL [REWRITE_TAC [FINITE_UNIONS, FORALL_IN_IMAGE] THEN SIMP_TAC [FINITE_IMAGE, FINITE_NUMSEG, IN_NUMSEG] THEN X_GEN_TAC (← q r"m:num") THEN STRIP_TAC THEN MATCH_MP_TAC FINITE_IDEALS_SUPERSET THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN MATCH_MP_TAC r1 THEN EXISTS_TAC (← q r"ring_of_num k m:A") THEN REWRITE_TAC [IN_IDEAL_GENERATED_SELF] THEN REWRITE_TAC [(← GSYM RING_OF_INT_OF_NUM), RING_OF_INT_IN_RING_OF_INTEGERS] THEN REWRITE_TAC [RING_OF_INT_OF_NUM] THEN FIRST_ASSUM (MP_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN REWRITE_TAC [RING_CHAR_EQ_0] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN ASM_ARITH_TAC, GEN_REWRITE_TAC id [SUBSET] THEN X_GEN_TAC (← q r"j:A->bool") THEN REWRITE_TAC [IN_ELIM_THM, IN_UNIONS, EXISTS_IN_IMAGE] THEN STRIP_TAC THEN EXISTS_TAC (← q r"ideal_norm (ring_of_integers k) (j:A->bool)") THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"j:A->bool")] RING_OF_INTEGERS_FINITE_QUOTIENT) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_SIMP_TAC [IN_NUMSEG, IDEAL_NORM_POS, IN_ELIM_THM] THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"j:A->bool")] IDEAL_NORM_IN_IDEAL) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS]])

  let NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM ← prove
    r"!k:A ring c.
        number_field k
        ==> FINITE {P | prime_ideal (ring_of_integers k) P /\
                        ~(P = {ring_0 k}) /\
                        ideal_norm (ring_of_integers k) P <= c}"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
         ideal_norm (ring_of_integers k) (j:A->bool) <= c}") THEN ASM_SIMP_TAC [NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN MESON_TAC [PRIME_IMP_RING_IDEAL])

  let NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2 ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"2 <= n <=> 1 < n")
    let r2 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!k:A ring P.
          number_field k /\ prime_ideal (ring_of_integers k) P /\
          ~(P = {ring_0 k})
          ==> FINITE(ring_carrier(quotient_ring (ring_of_integers k) P)) /\
              2 <= ideal_norm (ring_of_integers k) P"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC r2 THEN CONJ_TAC THENL [MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], DISCH_TAC THEN REWRITE_TAC [r1] THEN MATCH_MP_TAC IDEAL_NORM_GT_1 THEN RULE_ASSUM_TAC (REWRITE_RULE [prime_ideal, proper_ideal, PSUBSET]) THEN ASM_REWRITE_TAC []])

  let FREE_BASIS_NORM_BOUND ← prove
    r"!r:A ring n w B c t.
        free_basis (integer_ring,r) (ring_of_int r) n w /\
        (!i l m. i < n /\ l < n /\ m < n
                 ==> abs(mul_matrix (integer_ring,r) (ring_of_int r)
                           n w (w i) m l) <= B) /\
        (!m. m < n ==> abs(c m) <= &t)
        ==> abs(algebra_norm (integer_ring,r) (ring_of_int r)
                 (ring_sum r {m | m < n}
                    (\m. ring_mul r (ring_of_int r (c m)) (w m)))) <=
            &(FACT n) * ((&n * B) * &t) pow n"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_int r:int->A"), (← q r"integer_ring"), (← q r"r:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"ring_sum r {m | m < n}
      (\m. ring_mul r (ring_of_int r ((c:num->int) m)) ((w:num->A) m))")] ALGEBRA_NORM_FREE_BASIS) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, RING_SUM] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"{i:num | i < n}"), (← q r"mul_matrix (integer_ring,r) (ring_of_int r) n w
       (ring_sum r {m | m < n}
          (\m. ring_mul r (ring_of_int r ((c:num->int) m)) ((w:num->A) m)))"), (← q r"(&n * (B:int)) * &t")] INT_DET_BOUND) THEN REWRITE_TAC [CARD_NUMSEG_LT, FINITE_NUMSEG_LT, IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN MAP_EVERY X_GEN_TAC [(← q r"p:num"), (← q r"q:num")] THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FREE_BASIS_IN_CARRIER)) THEN MP_TAC (← ISPECL [(← q r"ring_of_int r:int->A"), (← q r"integer_ring"), (← q r"r:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"{m:num | m < n}"), (← q r"c:num->int"), (← q r"w:num->A"), (← q r"p:num"), (← q r"q:num")] MUL_MATRIX_RING_SUM) THEN ASM_REWRITE_TAC [INTEGER_RING, IN_UNIV, FINITE_NUMSEG_LT, IN_ELIM_THM, RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC (← q r"&(CARD {m:num | m < n}) * (&t * B):int") THEN CONJ_TAC THENL [ALL_TAC, REWRITE_TAC [CARD_NUMSEG_LT] THEN INT_ARITH_TAC] THEN REWRITE_TAC [INTEGER_RING_SUM] THEN MATCH_MP_TAC ISUM_ABS_BOUND THEN REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN X_GEN_TAC (← q r"m:num") THEN DISCH_TAC THEN REWRITE_TAC [INT_ABS_MUL] THEN MATCH_MP_TAC INT_LE_MUL2 THEN ASM_SIMP_TAC [INT_ABS_POS])

  let NUMBER_FIELD_IDEAL_SMALL_ELEMENT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r3 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!k:A ring n w B j.
          number_field k /\
          free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w /\
          (!i l m. i < n /\ l < n /\ m < n
                   ==> abs(mul_matrix (integer_ring,ring_of_integers k)
                             (ring_of_int k) n w (w i) m l)
                       <= B) /\
          ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
          ==> ?a. a IN j /\ ~(a = ring_0 k) /\
                  &(ideal_norm (ring_of_integers k)
                      (ideal_generated (ring_of_integers k) {a})) <=
                  (&(FACT n) * (&n * B) pow n) *
                  &(ideal_norm (ring_of_integers k) j)"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_char(k:A ring) = 0") ASSUME_TAC THENL [ASM_MESON_TAC [number_field], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_homomorphism(integer_ring,ring_of_integers k) (ring_of_int k:int->A)") ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(n = 0)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A")] RING_OF_INTEGERS_FREE_BASIS_FIELD) THEN MP_TAC (← ISPEC (← q r"k:A ring") NUMBER_FIELD_DEGREE_POS) THEN ASM_SIMP_TAC [] THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"&0 <= (B:int)") ASSUME_TAC THENL [MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC (← q r"abs(mul_matrix (integer_ring,ring_of_integers k)
                        (ring_of_int k) n w ((w:num->A) 0) 0 0)") THEN REWRITE_TAC [INT_ABS_POS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"FINITE(ring_carrier(quotient_ring (ring_of_integers k) (j:A->bool)))") ASSUME_TAC THENL [MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"n:num"), (← q r"ideal_norm (ring_of_integers k) (j:A->bool)")] NUM_ROOT_FLOOR) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"t:num") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"j:A->bool"), (← q r"t:num")] FREE_BASIS_IDEAL_BOX_PRINCIPLE) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:num->int") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q r"m0:num")) ASSUME_TAC))) THEN ABBREV_TAC (← q r"a = ring_sum (ring_of_integers k) {m | m < n}
        (\m. ring_mul k (ring_of_int k ((c:num->int) m)) ((w:num->A) m))") THEN EXISTS_TAC (← q r"a:A") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [EXPAND_TAC "a" THEN REWRITE_TAC [RING_SUM], ALL_TAC] THEN MATCH_MP_TAC r3 THEN CONJ_TAC THENL [DISCH_TAC THEN FIRST_ASSUM (fun z1 => tactic_of do pure (MP_TAC (← SPEC (← q r"c:num->int") (← (do let z2 ← (do pure (CONJUNCTS (← GEN_REWRITE_RULE id [free_basis] z1))); liftExcept (last z2)))))) THEN ASM_REWRITE_TAC [INTEGER_RING, IN_UNIV, RING_OF_INTEGERS] THEN ASM_MESON_TAC [], DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A")] NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_Q) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"z:int") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"a:A")] NUMBER_FIELD_NORM_INTEGRAL_BASIS) THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (MP_TAC o (CONJUNCT2 o ((REWRITE_RULE [ring_monomorphism]) o (GEN_REWRITE_RULE id [(← GSYM RING_MONOMORPHISM_INTEGER_RING_OF_INT)])))) THEN REWRITE_TAC [INTEGER_RING, IN_UNIV] THEN DISCH_THEN (fun th => DISCH_THEN (SUBST_ALL_TAC o (MATCH_MP th))) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC (← q r"&(FACT n) * ((&n * (B:int)) * &t) pow n") THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"B:int"), (← q r"c:num->int"), (← q r"t:num")] FREE_BASIS_NORM_BOUND) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [INT_POW_MUL] THEN REWRITE_TAC [(← GSYM INT_MUL_ASSOC)] THEN MATCH_MP_TAC INT_LE_LMUL THEN REWRITE_TAC [INT_POS] THEN MATCH_MP_TAC INT_LE_LMUL THEN ASM_SIMP_TAC [INT_POW_LE, INT_LE_MUL, INT_POS] THEN ASM_REWRITE_TAC [INT_OF_NUM_POW, INT_OF_NUM_LE]])

  let NUMBER_FIELD_IDEAL_CLASS_BOUND_EXPLICIT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"0 < n <=> 1 <= n")
    let r2 ← SET_RULE (← q r"!x:A s z. x IN s /\ ~(x = z) ==> ~(s = {z})")
    let r3 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!k:A ring n w B.
          number_field k /\
          free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w /\
          (!i l m. i < n /\ l < n /\ m < n
                   ==> abs(mul_matrix (integer_ring,ring_of_integers k)
                             (ring_of_int k) n w (w i) m l)
                       <= B)
          ==> !j. ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
                  ==> ?j'. j' IN ideal_class (ring_of_integers k) j /\
                           &(ideal_norm (ring_of_integers k) j') <=
                           &(FACT n) * (&n * B) pow n"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC (← q r"j:A->bool") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"dedekind_domain(ring_of_integers k:A ring)") ASSUME_TAC THENL [ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN)) THEN SUBGOAL_THEN (← q r"?i b. ring_ideal (ring_of_integers k) i /\ ~(i = {ring_0 k}) /\
            b IN ring_carrier(ring_of_integers k) /\ ~(b = ring_0 k) /\
            ideal_prod (ring_of_integers k) j i =
            ideal_generated (ring_of_integers k) {b:A}") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"j:A->bool")] DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"B:int"), (← q r"i:A->bool")] NUMBER_FIELD_IDEAL_SMALL_ELEMENT) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:A") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier(ring_of_integers k) /\
      ~(ideal_generated (ring_of_integers k) {a:A} = {ring_0 k})") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r3 THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], DISCH_TAC] THEN MATCH_MP_TAC r2 THEN EXISTS_TAC (← q r"a:A") THEN ASM_REWRITE_TAC [IN_IDEAL_GENERATED_SELF], ALL_TAC] THEN SUBGOAL_THEN (← q r"?j'. ring_ideal (ring_of_integers k) j' /\
           ideal_prod (ring_of_integers k) i j' =
           ideal_generated (ring_of_integers k) {a:A}") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ideal_generated (ring_of_integers k) {a:A}"), (← q r"i:A->bool")] DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(j' = {ring_0 k:A})") ASSUME_TAC THENL [DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"i:A->bool"), (← q r"j':A->bool")] IDEAL_PROD_EQ_ZERO) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN EXISTS_TAC (← q r"j':A->bool") THEN CONJ_TAC THENL [REWRITE_TAC [IN_IDEAL_CLASS, RING_OF_INTEGERS] THEN ASM_REWRITE_TAC [] THEN MAP_EVERY EXISTS_TAC [(← q r"a:A"), (← q r"b:A")] THEN ASM_REWRITE_TAC [] THEN SUBST1_TAC (← SYM (← ASSUME (← q r"ideal_prod (ring_of_integers k) i j' =
        ideal_generated (ring_of_integers k) {a:A}"))) THEN SUBST1_TAC (← SYM (← ASSUME (← q r"ideal_prod (ring_of_integers k) j i =
        ideal_generated (ring_of_integers k) {b:A}"))) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"j:A->bool"), (← q r"i:A->bool"), (← q r"j':A->bool")] IDEAL_PROD_ASSOC) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC IDEAL_PROD_COMM THEN CONJ_TAC THEN MATCH_MP_TAC RING_IDEAL_IMP_SUBSET THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_PROD], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"&(ideal_norm (ring_of_integers k) (j':A->bool)):int"), (← q r"&(FACT n) * (&n * (B:int)) pow n"), (← q r"&(ideal_norm (ring_of_integers k) (i:A->bool)):int")] INT_LE_LMUL_EQ) THEN ANTS_TAC THENL [REWRITE_TAC [INT_OF_NUM_LT, r1] THEN MATCH_MP_TAC IDEAL_NORM_POS THEN MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_REWRITE_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"i:A->bool"), (← q r"j':A->bool")] NUMBER_FIELD_IDEAL_NORM_MUL_Q) THEN ASM_REWRITE_TAC [INT_OF_NUM_MUL] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ONCE_REWRITE_TAC [INT_MUL_SYM] THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_IDEAL_CLASS_BOUND ← prove
    r"!k:A ring.
        number_field k
        ==> ?c. !j. ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
                    ==> ?j'. j' IN ideal_class (ring_of_integers k) j /\
                             ideal_norm (ring_of_integers k) j' <= c"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM ((X_CHOOSE_TAC (← q r"w:num->A")) o (MATCH_MP RING_OF_INTEGERS_FREE)) THEN ABBREV_TAC (← q r"n = extension_degree (subfield_generated k {ring_0 k},k) (I:A->A)") THEN MP_TAC (← ISPECL [(← q r"\p. abs(mul_matrix (integer_ring,ring_of_integers k)
               (ring_of_int k) n w ((w:num->A)(FST p)) (SND(SND p))
               (FST(SND p)))"), (← q r"{i:num | i < n} CROSS ({l:num | l < n} CROSS {m:num | m < n})")] UPPER_BOUND_FINITE_SET_INT) THEN SIMP_TAC [FINITE_CROSS, FINITE_NUMSEG_LT] THEN REWRITE_TAC [FORALL_PAIR_THM, IN_CROSS, IN_ELIM_THM] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"B:int")) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"B:int")] NUMBER_FIELD_IDEAL_CLASS_BOUND_EXPLICIT) THEN ANTS_TAC THENL [ASM_MESON_TAC [], DISCH_TAC] THEN EXISTS_TAC (← q r"num_of_int(&(FACT n) * (&n * (B:int)) pow n)") THEN X_GEN_TAC (← q r"j:A->bool") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"j:A->bool"))) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"j':A->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [(← GSYM INT_OF_NUM_LE)] THEN MP_TAC (← ISPEC (← q r"&(FACT n) * (&n * (B:int)) pow n") INT_OF_NUM_OF_INT) THEN ANTS_TAC THENL [ASM_MESON_TAC [INT_POS, INT_LE_TRANS], DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC []])

  let NUMBER_FIELD_CLASS_GROUP_FINITE ← prove
    r"!k:A ring. number_field k ==> FINITE(ideal_classes(ring_of_integers k))"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"integral_domain(ring_of_integers k:A ring)") ASSUME_TAC THENL [ASM_SIMP_TAC [INTEGRAL_DOMAIN_RING_OF_INTEGERS, NUMBER_FIELD_IMP_FIELD], ALL_TAC] THEN FIRST_ASSUM ((X_CHOOSE_TAC (← q r"c:num")) o (MATCH_MP NUMBER_FIELD_IDEAL_CLASS_BOUND)) THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"IMAGE (ideal_class (ring_of_integers k))
                {j:A->bool | ring_ideal (ring_of_integers k) j /\
                             ~(j = {ring_0 k}) /\
                             ideal_norm (ring_of_integers k) j <= c}") THEN ASM_SIMP_TAC [FINITE_IMAGE, NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM] THEN REWRITE_TAC [ideal_classes, RING_OF_INTEGERS] THEN GEN_REWRITE_TAC id [SUBSET] THEN REWRITE_TAC [IN_ELIM_THM, IN_IMAGE] THEN X_GEN_TAC (← q r"x:(A->bool)->bool") THEN DISCH_THEN (X_CHOOSE_THEN (← q r"j:A->bool") STRIP_ASSUME_TAC) THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"j:A->bool"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"j':A->bool") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"j':A->bool") THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [IN_IDEAL_CLASS])) THEN RULE_ASSUM_TAC (REWRITE_RULE [RING_OF_INTEGERS]) THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"j:A->bool"), (← q r"j':A->bool")] IDEAL_CLASS_EQ) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS])

  let NUMBER_FIELD_CLASS_NUMBER_POS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"1 <= n <=> ~(n = 0)")
    prove
      r"!k:A ring. number_field k ==> 1 <= class_number(ring_of_integers k)"
      (REPEAT STRIP_TAC THEN REWRITE_TAC [class_number, r1] THEN ASM_SIMP_TAC [CARD_EQ_0, NUMBER_FIELD_CLASS_GROUP_FINITE] THEN REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY)] THEN EXISTS_TAC (← q r"ideal_class (ring_of_integers k)
                  (ring_carrier(ring_of_integers k:A ring))") THEN REWRITE_TAC [ideal_classes, IN_ELIM_THM] THEN EXISTS_TAC (← q r"ring_carrier(ring_of_integers k:A ring)") THEN REWRITE_TAC [] THEN MATCH_MP_TAC INTEGRAL_DOMAIN_UNIT_IDEAL THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_RING_OF_INTEGERS, NUMBER_FIELD_IMP_FIELD])

  let NUMBER_FIELD_PID_EQ_CLASS_NUMBER_1 ← prove
    r"!k:A ring.
        number_field k
        ==> (PID(ring_of_integers k) <=>
             class_number(ring_of_integers k) = 1)"
    (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [DEDEKIND_PID_EQ_CLASS_NUMBER_1, DEDEKIND_RING_OF_INTEGERS] THEN ASM_SIMP_TAC [HAS_SIZE, class_number, NUMBER_FIELD_CLASS_GROUP_FINITE])

  let NUMBER_FIELD_IDEAL_CLASS_COPRIME ← prove
    r"!k i j:A->bool.
        number_field k /\
        ring_ideal (ring_of_integers k) i /\ ~(i = {ring_0 k}) /\
        ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
        ==> ?l. l IN ideal_class (ring_of_integers k) i /\
                ring_setadd (ring_of_integers k) l j =
                ring_carrier(ring_of_integers k)"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC DEDEKIND_IDEAL_CLASS_COPRIME THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_OF_INTEGERS])

  let IDEAL_CLASS_ISOMORPHIC_IMAGE ← prove
    r"!r s (h:A->B) j.
        ring_isomorphism(r,s) h /\ ring_ideal r j
        ==> ideal_class s (IMAGE h j) = IMAGE (IMAGE h) (ideal_class r j)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o (GEN_REWRITE_RULE id [ring_isomorphism])) THEN REWRITE_TAC [RING_ISOMORPHISMS_ISOMORPHISM, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"g:B->A") THEN STRIP_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"k':B->bool") THEN REWRITE_TAC [IN_IMAGE] THEN EQ_TAC THENL [DISCH_TAC THEN EXISTS_TAC (← q r"IMAGE (g:B->A) k'") THEN SUBGOAL_THEN (← q r"k' SUBSET ring_carrier(s:B ring) /\ j SUBSET ring_carrier(r:A ring)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [IN_IDEAL_CLASS, RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"r:A ring"), (← q r"g:B->A"), (← q r"IMAGE (h:A->B) j"), (← q r"k':B->bool")] IN_IDEAL_CLASS_ISOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC [], DISCH_THEN (X_CHOOSE_THEN (← q r"k:A->bool") (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN MATCH_MP_TAC IN_IDEAL_CLASS_ISOMORPHIC_IMAGE THEN EXISTS_TAC (← q r"r:A ring") THEN ASM_REWRITE_TAC []])

  let ISOMORPHIC_RING_IDEAL_CLASSES ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"ring_carrier r:A->bool"
    let q2 ← q r"!s. (!x. x IN s ==> (g:B->A) ((f:A->B) x) = x) /\ t SUBSET s
          ==> IMAGE g (IMAGE f t) = t"
    let r3 ← SET_RULE q2
    let q4 ← q r"j:A->bool"
    let q5 ← q r"f:A->B"
    let q6 ← q r"s:B ring"
    let q7 ← q r"r:A ring"
    let v8 ← ISPECL [q7, q6, q5, q4] IDEAL_CLASS_ISOMORPHIC_IMAGE
    let q9 ← q r"IMAGE (f:A->B) j"
    let q10 ← q r"g:B->A"
    let q11 ← q r"r:A ring"
    let q12 ← q r"s:B ring"
    let v13 ← ISPECL [q12, q11, q10, q9] IDEAL_CLASS_ISOMORPHIC_IMAGE
    let q14 ← q r"j:A->bool"
    let q15 ← q r"j:A->bool"
    let q16 ← q r"f:A->B"
    let q17 ← q r"s:B ring"
    let q18 ← q r"r:A ring"
    let v19 ← ISPECL [q18, q17, q16, q15, q14] IN_IDEAL_CLASS_ISOMORPHIC_IMAGE
    let q20 ← q r"ring_ideal s (IMAGE (f:A->B) j) /\ ~(IMAGE f j = {ring_0 s})"
    let q21 ← q r"j:A->bool"
    let p22 ← prove r"!r:A ring s:B ring f g.
        ring_isomorphisms(r,s) (f,g)
        ==> !c. c IN ideal_classes r
                ==> IMAGE (IMAGE f) c IN ideal_classes s /\
                    IMAGE (IMAGE g) (IMAGE (IMAGE f) c) = c" (REPEAT GEN_TAC THEN REWRITE_TAC [RING_ISOMORPHISMS_ISOMORPHISM] THEN STRIP_TAC THEN REWRITE_TAC [ideal_classes, FORALL_IN_GSPEC] THEN X_GEN_TAC q21 THEN STRIP_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN SUBGOAL_THEN q20 STRIP_ASSUME_TAC THENL [MP_TAC v19 THEN ASM_SIMP_TAC [IDEAL_CLASS_REFL] THEN SIMP_TAC [IN_IDEAL_CLASS], ALL_TAC] THEN MP_TAC v13 THEN MP_TAC v8 THEN ASM_REWRITE_TAC [] THEN REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN CONJ_TAC THENL [ASM_MESON_TAC [], AP_TERM_TAC] THEN MATCH_MP_TAC r3 THEN EXISTS_TAC q1 THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET])
    let lemma := p22
    let q23 ← q r"IMAGE (IMAGE (g:B->A))"
    let q24 ← q r"IMAGE (IMAGE (f:A->B))"
    let q25 ← q r"g:B->A"
    let q26 ← q r"f:A->B"
    prove
      r"!r:A ring s:B ring.
          r isomorphic_ring s ==> ideal_classes r =_c ideal_classes s"
      (REPEAT GEN_TAC THEN REWRITE_TAC [isomorphic_ring, ring_isomorphism, LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [q26, q25] THEN DISCH_TAC THEN REWRITE_TAC [EQ_C_BIJECTIONS] THEN MAP_EVERY EXISTS_TAC [q24, q23] THEN CONJ_TAC THEN MATCH_MP_TAC lemma THEN ASM_MESON_TAC [RING_ISOMORPHISMS_SYM])

  let ISOMORPHIC_RING_CLASS_NUMBER ← prove
    r"!r:A ring s:B ring.
        r isomorphic_ring s /\
        (FINITE(ideal_classes r) \/ FINITE(ideal_classes s))
        ==> class_number r = class_number s"
    (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 (ASSUME_TAC o (MATCH_MP ISOMORPHIC_RING_IDEAL_CLASSES)) MP_TAC) THEN FIRST_ASSUM (SUBST1_TAC o (MATCH_MP CARD_FINITE_CONG)) THEN REWRITE_TAC [class_number] THEN DISCH_TAC THEN MATCH_MP_TAC CARD_EQ_CARD_IMP THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_CLASS_NUMBER_ISOMORPHIC ← prove
    r"!k:A ring l:B ring.
        number_field k /\ k isomorphic_ring l
        ==> class_number(ring_of_integers k) =
            class_number(ring_of_integers l)"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC ISOMORPHIC_RING_CLASS_NUMBER THEN ASM_SIMP_TAC [ISOMORPHIC_RING_RING_OF_INTEGERS, NUMBER_FIELD_CLASS_GROUP_FINITE])

  -- @@RETURN BEGIN
  return { ideal_classes, class_number, IDEAL_CLASS_EQ, INTEGRAL_DOMAIN_UNIT_IDEAL,
           DEDEKIND_PID_EQ_CLASS_NUMBER_1, FREE_BASIS_IDEAL_BOX_PRINCIPLE,
           NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM,
           NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM,
           NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2, FREE_BASIS_NORM_BOUND,
           NUMBER_FIELD_IDEAL_SMALL_ELEMENT, NUMBER_FIELD_IDEAL_CLASS_BOUND_EXPLICIT,
           NUMBER_FIELD_IDEAL_CLASS_BOUND, NUMBER_FIELD_CLASS_GROUP_FINITE,
           NUMBER_FIELD_CLASS_NUMBER_POS, NUMBER_FIELD_PID_EQ_CLASS_NUMBER_1,
           NUMBER_FIELD_IDEAL_CLASS_COPRIME, IDEAL_CLASS_ISOMORPHIC_IMAGE,
           ISOMORPHIC_RING_IDEAL_CLASSES, ISOMORPHIC_RING_CLASS_NUMBER,
           NUMBER_FIELD_CLASS_NUMBER_ISOMORPHIC }
  -- @@RETURN END

end HolANT.Classgroup
