/- ========================================================================= -/
/- ANT: Number fields, abstractly                                          -/
/- ========================================================================= -/
/- File: HolANT/Numfield.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/numfield.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antnumfielddiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/isum.ml, Library/products.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/zlattice.ml, Library/floor.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.Numfield fills them).

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
import HolANT.Integral
import HolANT.Zlattice
import HolLibrary.Floor

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.Algmisc
open HolANT.Integral
open HolANT.Zlattice

namespace HolANT.Numfield

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ALGEBRA_NORM_EQ_0 ALGEBRA_NORM_MUL ALGEBRA_NORM_SUBRING
   ALGEBRA_NORM_SUB_CHARPOLY ALGEBRA_TRACE_ADD ALGEBRA_TRACE_MUL_LINCOMB
   ALGEBRA_TRACE_NORM_BASE ALGEBRA_TRACE_NORM_IN_CARRIER ALGEBRA_TRACE_SCALAR
   ALGEBRA_TRACE_SUBRING BASIS_COORDINATES CARRIER_SUBRING_GENERATED_SUBRING
   COND_RAND COND_RATOR DIVIDES_ZERO EMPTY_GSPEC EQ_IMP EQ_MULT_LCANCEL EQ_TRANS
   ETA_AX EXTENSION EXTENSION_DEGREE_REFL EXTENSION_DEGREE_TOWER_LAW
   EXTENSION_LINCOMB_LMUL EXTENSION_LINCOMB_MUL EXTENSION_LINCOMB_SUM
   EXTENSION_MUL_LINCOMB FIELD_CHARPOLY_MINIMAL_POLYNOMIAL
   FIELD_EXTENSION_SUBFIELD_GENERATED FIELD_IMP_INTEGRAL_DOMAIN
   FIELD_IMP_NONTRIVIAL_RING FIELD_MUL_LINV FIELD_MUL_RINV FIELD_NONTRIVIAL
   FIELD_REAL_RING FIELD_SUBFIELD_GENERATED FIELD_UNIT FINITE_CROSS
   FINITE_EXTENSION_BASIS FINITE_EXTENSION_FREE_BASIS
   FINITE_EXTENSION_ISOMORPHISM FINITE_FINITELY_GENERATED_ALGEBRAIC_EXTENSION
   FINITE_IMAGE FINITE_IMP_ALGEBRAIC_EXTENSION FINITE_IMP_FIELD_EXTENSION
   FINITE_INDUCT_STRONG FINITE_INSERT FINITE_NUMSEG_LT FINITE_SING
   FINITE_SUBSET_SUBFIELD_GENERATED_DENOMINATOR FORALL_IN_GSPEC FORALL_IN_IMAGE
   FORALL_IN_INSERT FORALL_PAIR_THM FORALL_UNWIND_THM2
   FREE_BASIS_EXTENSION_DEGREE FREE_BASIS_FIELD FREE_BASIS_FROM_RING_BASIS
   FREE_BASIS_IN_CARRIER FREE_BASIS_SCALE FUN_EQ_THM IDEAL_GENERATED_EQ_0
   IMAGE_I IMP_CONJ IMP_IMP IN INSERT_SUBSET INTEGER_REAL_OF_INT INTEGER_RING
   INTEGER_RING_SUM INTEGRAL_CLOSURE_SUBRING INTEGRAL_CLOSURE_SUPSET_IMAGE
   INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING INTEGRAL_DOMAIN_MUL_EQ_0
   INTEGRAL_DOMAIN_SUBRING_GENERATED INTEGRAL_ELEMENT_EXPLICIT
   INTEGRAL_ELEMENT_FINITE_MODULE INTEGRAL_ELEMENT_HOMOMORPHIC_IMAGE
   INTEGRAL_ELEMENT_IMAGE INTEGRAL_ELEMENT_MUL INTEGRAL_ELEMENT_OVER_SUBRING
   INTEGRAL_ELEMENT_PRIME_SUBFIELD INTEGRAL_OVER_FIELD_EQ_ALGEBRAIC
   INT_LATTICE_FULL_RANK INT_LATTICE_MATRIX_IMAGE INT_MATRIX_IMAGE_INJECTIVE
   INT_MUL_RID INT_MUL_RZERO INT_MUL_SYM INT_SUB_REFL IN_CROSS IN_ELIM_THM
   IN_IDEAL_GENERATED_SING_EQ IN_IMAGE IN_INTER IN_SING IN_SUBFIELD_0
   IN_SUBRING_MUL IN_UNIV ISUM_0 ISUM_DELTA_GEN I_O_ID I_THM LEFT_IMP_EXISTS_THM
   LT LT_NZ MINIMAL_POLYNOMIAL MONO_EXISTS MONO_FORALL NOT_EXISTS_THM : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (NOT_IN_EMPTY POLY_EVAL_SUBFIELD_GENERATED POLY_POW_ALT
   PRIME_SUBFIELD_SUBFIELD_GENERATED PRIME_SUBRING REAL_RING_CHAR
   REAL_RING_CLAUSES REAL_RING_DIV REAL_RING_OF_INT RIGHT_FORALL_IMP_THM
   RIGHT_IMP_EXISTS_THM RING_1 RING_ADD_EQ_RIGHT RING_ADD_RNEG
   RING_CARRIER_SUBFIELD_GENERATED_SUBRING_QUOTIENTS
   RING_CARRIER_SUBFIELD_GENERATED_SUBSET RING_CARRIER_SUBRING_GENERATED_0
   RING_CARRIER_SUBRING_GENERATED_SUBSET RING_CHAR_SUBFIELD_GENERATED
   RING_HOMOMORPHISM_BETWEEN_SUBRINGS RING_HOMOMORPHISM_INTEGER_RING_OF_INT
   RING_HOMOMORPHISM_RING_OF_INT RING_HOMOMORPHISM_SUBFIELD_INCLUSION
   RING_HOMOMORPHISM_SUM RING_INV RING_INV_IN_SUBFIELD_GENERATED
   RING_ISOMORPHISM_I RING_MUL RING_MUL_ASSOC RING_MUL_IN_SUBFIELD_GENERATED
   RING_MUL_LID RING_MUL_LINV RING_MUL_LNEG RING_MUL_LZERO RING_MUL_RID
   RING_MUL_RINV RING_MUL_RZERO RING_MUL_SYM RING_NEG RING_OF_INT RING_OF_INT_0
   RING_OF_INT_1 RING_OF_INT_EQ_0_CHAR_0 RING_OF_INT_IN_SUBFIELD_GENERATED
   RING_OF_INT_NEG RING_OF_INT_OF_NUM RING_OF_INT_SUB
   RING_OF_INT_SUBFIELD_GENERATED RING_OF_INT_SUBRING_GENERATED RING_OF_NUM_0
   RING_OF_NUM_1 RING_OF_NUM_EQ_0 RING_OF_NUM_SUBFIELD_GENERATED
   RING_OF_NUM_SUBRING_GENERATED RING_POW RING_POW_1 RING_POW_SUBFIELD_GENERATED
   RING_POW_SUBRING_GENERATED RING_PRODUCT_SUBRING_GENERATED RING_RINV_UNIQUE
   RING_SUB RING_SUB_EQ_0 RING_SUB_LDISTRIB RING_SUB_RDISTRIB
   RING_SUB_SUBRING_GENERATED RING_SUM RING_SUM_0 RING_SUM_CLAUSES
   RING_SUM_DELTA RING_SUM_EQ RING_SUM_EQ_0 RING_SUM_LMUL RING_SUM_NEG
   RING_SUM_SING RING_SUM_SUB RING_SUM_SUBRING_GENERATED_GEN RING_UNIT_0
   RING_UNIT_IN_CARRIER SING_GSPEC SING_SUBSET SKOLEM_THM SUBFIELDS_GENERATED_EQ
   SUBFIELD_GENERATED SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC
   SUBFIELD_GENERATED_UNION_LEFT SUBRING_EQ_SUBFIELD_GENERATED SUBRING_GENERATED
   SUBRING_GENERATED_BY_SUBFIELD_GENERATED SUBSET SUBSET_ANTISYM_EQ
   TRACE_FORM_NONDEGENERATE algebraic_extension field_extension finite_extension
   free_basis int_eq int_lattice int_matrix_image int_of_num_th int_tybij
   isomorphic_ring o_THM rational ring_divides ring_isomorphism
   ring_isomorphisms ring_monomorphism ring_pow ring_unit : thm)
  deriving Inhabited

/-- What numfield.ml uses from Session besides theorems. -/
structure NumfieldDeps where
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
/- numfield.ml phrases from line 81 to 816                                -/
/- ---------------------------------------------------------------------- -/

structure Numfield01 where
  -- @@FIELDS
  number_field : thm
  ring_of_integers : thm
  RING_INT_LINCOMB_SWAP : thm
  RING_INT_LINCOMB : thm
  RING_MUL_INT_LINCOMB : thm
  RING_INT_LINCOMB_LINCOMB : thm
  RING_INT_LINCOMB_SANDWICH : thm
  NUMBER_FIELD_IMP_FIELD : thm
  NUMBER_FIELD_RING_OF_NUM_EQ_0 : thm
  NUMBER_FIELD_ALT : thm
  NUMBER_FIELD_FREE_BASIS_DEGREE : thm
  NUMBER_FIELD_FREE_BASIS : thm
  NUMBER_FIELD_DEGREE_POS : thm
  NUMBER_FIELD_DEGREE_EQ_1 : thm
  NUMBER_FIELD_ALGEBRAIC : thm
  NUMBER_FIELD_PRIME_SUBFIELD : thm
  NUMBER_FIELD_RATIONAL_FIELD : thm
  NUMBER_FIELD_SUBFIELD_GENERATED_ALGEBRAIC : thm
  PRIME_SUBFIELD_CHAR_0 : thm
  REAL_PRIME_SUBFIELD : thm
  PRIME_SUBFIELD_COMMON_DENOMINATOR : thm
  FREE_BASIS_PRIME_SUBFIELD_DENOMINATOR : thm
  FREE_BASIS_PRIME_SUBFIELD_INT_LINCOMB : thm
  NUMBER_FIELD_INT_LINCOMB_SANDWICH : thm
  RING_OF_INTEGERS_CARRIER : thm
  RING_OF_INTEGERS_SUBSET : thm
  RING_OF_INTEGERS_SUBRING : thm
  RING_OF_INTEGERS : thm
  RING_SUM_RING_OF_INTEGERS : thm
  RING_PRODUCT_RING_OF_INTEGERS : thm
  RING_OF_INT_IN_RING_OF_INTEGERS : thm
  ROOT_OF_UNITY_IN_RING_OF_INTEGERS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupNumfield01 [HolBase] (D : NumfieldDeps) :
    ExceptT String IO Numfield01 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, MESON_TAC, NUMBER_RULE, RING_RULE, SET_TAC, TAUT,
        new_definition, .. } := D
  let { BASIS_COORDINATES, CARRIER_SUBRING_GENERATED_SUBRING, COND_RAND, EMPTY_GSPEC,
        EQ_IMP, EQ_TRANS, EXTENSION, EXTENSION_DEGREE_REFL, EXTENSION_LINCOMB_LMUL,
        EXTENSION_LINCOMB_MUL, EXTENSION_LINCOMB_SUM, EXTENSION_MUL_LINCOMB,
        FIELD_EXTENSION_SUBFIELD_GENERATED, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_IMP_NONTRIVIAL_RING, FIELD_MUL_LINV, FIELD_MUL_RINV, FIELD_NONTRIVIAL,
        FIELD_REAL_RING, FIELD_SUBFIELD_GENERATED, FIELD_UNIT, FINITE_CROSS,
        FINITE_EXTENSION_BASIS, FINITE_EXTENSION_FREE_BASIS,
        FINITE_EXTENSION_ISOMORPHISM, FINITE_FINITELY_GENERATED_ALGEBRAIC_EXTENSION,
        FINITE_IMAGE, FINITE_IMP_ALGEBRAIC_EXTENSION, FINITE_IMP_FIELD_EXTENSION,
        FINITE_NUMSEG_LT, FINITE_SING, FINITE_SUBSET_SUBFIELD_GENERATED_DENOMINATOR,
        FORALL_IN_GSPEC, FORALL_IN_IMAGE, FORALL_PAIR_THM, FORALL_UNWIND_THM2,
        FREE_BASIS_EXTENSION_DEGREE, FREE_BASIS_FIELD, FREE_BASIS_FROM_RING_BASIS,
        FUN_EQ_THM, IMAGE_I, IMP_CONJ, IN, INTEGER_REAL_OF_INT, INTEGER_RING,
        INTEGER_RING_SUM, INTEGRAL_CLOSURE_SUBRING, INTEGRAL_CLOSURE_SUPSET_IMAGE,
        INTEGRAL_DOMAIN_MUL_EQ_0, INTEGRAL_ELEMENT_EXPLICIT, INT_LATTICE_FULL_RANK,
        INT_LATTICE_MATRIX_IMAGE, INT_MATRIX_IMAGE_INJECTIVE, INT_MUL_RID,
        INT_MUL_RZERO, INT_MUL_SYM, INT_SUB_REFL, IN_CROSS, IN_ELIM_THM, IN_IMAGE,
        IN_SING, IN_SUBFIELD_0, IN_UNIV, ISUM_0, ISUM_DELTA_GEN, I_THM,
        LEFT_IMP_EXISTS_THM, LT, LT_NZ, MONO_EXISTS, MONO_FORALL, .. } := D.core1
  let { PRIME_SUBFIELD_SUBFIELD_GENERATED, REAL_RING_CHAR, REAL_RING_CLAUSES,
        REAL_RING_DIV, REAL_RING_OF_INT, RIGHT_IMP_EXISTS_THM, RING_1, RING_ADD_RNEG,
        RING_CARRIER_SUBFIELD_GENERATED_SUBRING_QUOTIENTS,
        RING_CARRIER_SUBFIELD_GENERATED_SUBSET, RING_CARRIER_SUBRING_GENERATED_0,
        RING_CARRIER_SUBRING_GENERATED_SUBSET, RING_CHAR_SUBFIELD_GENERATED,
        RING_HOMOMORPHISM_INTEGER_RING_OF_INT, RING_HOMOMORPHISM_SUBFIELD_INCLUSION,
        RING_INV, RING_INV_IN_SUBFIELD_GENERATED, RING_ISOMORPHISM_I, RING_MUL,
        RING_MUL_ASSOC, RING_MUL_IN_SUBFIELD_GENERATED, RING_MUL_LID, RING_MUL_LZERO,
        RING_MUL_RID, RING_MUL_RZERO, RING_NEG, RING_OF_INT, RING_OF_INT_0,
        RING_OF_INT_EQ_0_CHAR_0, RING_OF_INT_IN_SUBFIELD_GENERATED, RING_OF_INT_NEG,
        RING_OF_INT_OF_NUM, RING_OF_INT_SUB, RING_OF_INT_SUBRING_GENERATED,
        RING_OF_NUM_0, RING_OF_NUM_1, RING_OF_NUM_EQ_0, RING_OF_NUM_SUBRING_GENERATED,
        RING_POW, RING_POW_SUBRING_GENERATED, RING_PRODUCT_SUBRING_GENERATED,
        RING_RINV_UNIQUE, RING_SUB_LDISTRIB, RING_SUB_RDISTRIB,
        RING_SUB_SUBRING_GENERATED, RING_SUM, RING_SUM_0, RING_SUM_CLAUSES,
        RING_SUM_DELTA, RING_SUM_EQ, RING_SUM_EQ_0, RING_SUM_LMUL, RING_SUM_SING,
        RING_SUM_SUB, RING_SUM_SUBRING_GENERATED_GEN, SING_GSPEC, SING_SUBSET,
        SKOLEM_THM, SUBFIELDS_GENERATED_EQ, SUBFIELD_GENERATED,
        SUBFIELD_GENERATED_UNION_LEFT, SUBRING_EQ_SUBFIELD_GENERATED,
        SUBRING_GENERATED, SUBSET, SUBSET_ANTISYM_EQ, algebraic_extension,
        field_extension, finite_extension, free_basis, int_eq, int_lattice,
        int_matrix_image, int_of_num_th, int_tybij, rational, ring_monomorphism,
        ring_pow, .. } := D.core2
  -- @@SCOPE END

  let number_field ← new_definition
    r"number_field (k:A ring) <=>
  ring_char k = 0 /\ finite_extension (subfield_generated k {ring_0 k},k) I"

  let ring_of_integers ← new_definition
    r"ring_of_integers (k:A ring) =
  subring_generated k
   {x | integral_element (integer_ring,k) (ring_of_int k) x}"

  let RING_INT_LINCOMB_SWAP ← prove
    r"!r:A ring (s:K->bool) (t:L->bool) w M z.
        FINITE s /\ FINITE t /\ (!i. i IN s ==> w i IN ring_carrier r)
        ==> ring_sum r s
              (\i. ring_mul r (ring_of_int r (isum t (\j. M i j * z j)))
                              (w i)) =
            ring_sum r t
              (\j. ring_mul r (ring_of_int r (z j))
                     (ring_sum r s
                        (\i. ring_mul r (ring_of_int r (M i j)) (w i))))"
    (REPEAT STRIP_TAC THEN MP_TAC (← BETA_RULE (← ISPECL [(← q r"ring_of_int r:int->A"), (← q r"integer_ring"), (← q r"r:A ring"), (← q r"t:L->bool"), (← q r"s:K->bool"), (← q r"z:L->int"), (← q r"\j i. (M:K->L->int) i j"), (← q r"w:K->A")] EXTENSION_LINCOMB_SUM)) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, INTEGER_RING, IN_UNIV, INTEGER_RING_SUM] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [INT_MUL_SYM])

  let RING_INT_LINCOMB ← prove
    r"!r:A ring s (w:K->A).
        FINITE s /\ (!i. i IN s ==> w i IN ring_carrier r)
        ==> ring_sum r s (\i. ring_mul r (ring_of_int r (&0)) (w i)) =
            ring_0 r /\
            (!x y. ring_sum r s
                     (\i. ring_mul r (ring_of_int r (x i - y i)) (w i)) =
                   ring_sub r
                    (ring_sum r s
                       (\i. ring_mul r (ring_of_int r (x i)) (w i)))
                    (ring_sum r s
                       (\i. ring_mul r (ring_of_int r (y i)) (w i)))) /\
            (!m x. ring_sum r s
                     (\i. ring_mul r (ring_of_int r (m * x i)) (w i)) =
                   ring_mul r (ring_of_int r m)
                    (ring_sum r s
                       (\i. ring_mul r (ring_of_int r (x i)) (w i)))) /\
            (!M z. ring_sum r s
                     (\i. ring_mul r (ring_of_int r (isum s (\j. M i j * z j)))
                                     (w i)) =
                   ring_sum r s
                     (\j. ring_mul r (ring_of_int r (z j))
                           (ring_sum r s
                             (\i. ring_mul r (ring_of_int r (M i j))
                                             (w i)))))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL [ASM_SIMP_TAC [RING_OF_INT_0, RING_MUL_LZERO, RING_SUM_0], ASM_SIMP_TAC [(← GSYM RING_SUM_SUB), RING_MUL, RING_OF_INT] THEN MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC [RING_OF_INT_SUB, RING_SUB_RDISTRIB, RING_OF_INT], MP_TAC (← ISPECL [(← q r"ring_of_int r:int->A"), (← q r"integer_ring"), (← q r"r:A ring"), (← q r"s:K->bool"), (← q r"m:int"), (← q r"x:K->int"), (← q r"w:K->A")] EXTENSION_LINCOMB_LMUL) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, INTEGER_RING, IN_UNIV], MATCH_MP_TAC RING_INT_LINCOMB_SWAP THEN ASM_REWRITE_TAC []])

  let RING_MUL_INT_LINCOMB ← prove
    r"!r:A ring s a c (w:K->A).
        FINITE s /\ a IN ring_carrier r /\
        (!i. i IN s ==> w i IN ring_carrier r)
        ==> ring_mul r a
              (ring_sum r s (\i. ring_mul r (ring_of_int r (c i)) (w i))) =
            ring_sum r s
              (\i. ring_mul r (ring_of_int r (c i)) (ring_mul r a (w i))) /\
            ring_mul r
              (ring_sum r s (\i. ring_mul r (ring_of_int r (c i)) (w i))) a =
            ring_sum r s
              (\i. ring_mul r (ring_of_int r (c i)) (ring_mul r (w i) a))"
    (REPEAT STRIP_TAC THEN MAP_EVERY (fun th => tactic_of do pure (MP_TAC (← ISPECL [(← q r"ring_of_int r:int->A"), (← q r"integer_ring"), (← q r"r:A ring"), (← q r"s:K->bool"), (← q r"c:K->int"), (← q r"w:K->A"), (← q r"a:A")] th))) [EXTENSION_MUL_LINCOMB, EXTENSION_LINCOMB_MUL] THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, INTEGER_RING, IN_UNIV])

  let RING_INT_LINCOMB_LINCOMB ← prove
    r"!r:A ring (s:K->bool) (t:L->bool) (e:L->A) (y:K->A) a.
        FINITE s /\ FINITE t /\ (!p. p IN t ==> e p IN ring_carrier r) /\
        (!i. i IN s
             ==> ?b. y i = ring_sum r t
                             (\p. ring_mul r (ring_of_int r (b p)) (e p)))
        ==> ?b. ring_sum r s (\i. ring_mul r (ring_of_int r (a i)) (y i)) =
                ring_sum r t (\p. ring_mul r (ring_of_int r (b p)) (e p))"
    (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ((X_CHOOSE_TAC (← q r"b:K->L->int")) o (REWRITE_RULE [RIGHT_IMP_EXISTS_THM, SKOLEM_THM]))))) THEN EXISTS_TAC (← q r"\p. isum s (\i. (b:K->L->int) i p * a i)") THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"t:L->bool"), (← q r"s:K->bool"), (← q r"e:L->A"), (← q r"\p i. (b:K->L->int) i p"), (← q r"a:K->int")] RING_INT_LINCOMB_SWAP) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC [])

  let RING_INT_LINCOMB_SANDWICH ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (r ==> s) ==> (p <=> q /\ r) ==> s")
    let r2 ← RING_RULE (← q r"ring_mul r a (ring_mul r b c) = ring_mul r b (ring_mul r (a:A) c)")
    prove
      r"!k:A ring t n (g:num->A) D.
          field k /\ ~(ring_of_int k D = ring_0 k) /\ t SUBSET ring_carrier k /\
          (!x y. x IN t /\ y IN t ==> ring_sub k x y IN t) /\
          (!i. i < n ==> g i IN ring_carrier k) /\
          (!c. ring_sum k {i | i < n}
                 (\i. ring_mul k (ring_of_int k (c i)) (g i)) IN t) /\
          (!c. ring_sum k {i | i < n}
                 (\i. ring_mul k (ring_of_int k (c i)) (g i)) = ring_0 k
               ==> !i. i < n ==> c i = &0) /\
          (!x. x IN t
               ==> ?c. ring_mul k (ring_of_int k D) x =
                       ring_sum k {i | i < n}
                         (\i. ring_mul k (ring_of_int k (c i)) (g i)))
          ==> ?w. (!i. i < n ==> w i IN t) /\
                  (!x. x IN t
                       ==> ?c. x = ring_sum k {i | i < n}
                                     (\i. ring_mul k (ring_of_int k (c i))
                                                     (w i))) /\
                  (!c. ring_sum k {i | i < n}
                         (\i. ring_mul k (ring_of_int k (c i)) (w i)) = ring_0 k
                       ==> !i. i < n ==> c i = &0)"
      (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (ASSUME_TAC o (REWRITE_RULE [SUBSET])) (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "span") (CONJUNCTS_THEN2 (LABEL_TAC "indep") (LABEL_TAC "den")))))))) THEN SUBGOAL_THEN (← q r"ring_0 (k:A ring) IN t") ASSUME_TAC THENL [USE_THEN "span" (MP_TAC o (SPEC (← q r"\i:num. &0:int"))) THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC RING_SUM_EQ_0 THEN ASM_SIMP_TAC [IN_ELIM_THM, RING_OF_INT_0, RING_MUL_LZERO], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{i:num | i < n}"), (← q r"g:num->A")] RING_INT_LINCOMB) THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN STRIP_TAC THEN ABBREV_TAC (← q r"e = ring_inv k (ring_of_int k D):A") THEN SUBGOAL_THEN (← q r"(e:A) IN ring_carrier k /\ ring_mul k e (ring_of_int k D) = ring_1 k /\
      ring_mul k (ring_of_int k D) e = ring_1 k") STRIP_ASSUME_TAC THENL [EXPAND_TAC "e" THEN ASM_SIMP_TAC [RING_INV, RING_OF_INT, FIELD_MUL_LINV, FIELD_MUL_RINV], ALL_TAC] THEN ABBREV_TAC (← q r"lc = \z. ring_sum k {i | i < n}
                 (\i. ring_mul k (ring_of_int k (z i)) ((g:num->A) i))") THEN MP_TAC (← ISPECL [(← q r"{i:num | i < n}"), (← q r"{z | (!i. ~(i IN {i:num | i < n}) ==> z i = &0) /\
            ring_mul k e ((lc:(num->int)->A) z) IN t}")] INT_LATTICE_MATRIX_IMAGE) THEN ANTS_TAC THENL [REWRITE_TAC [FINITE_NUMSEG_LT, int_lattice, SUBSET, IN_ELIM_THM] THEN EXPAND_TAC "lc" THEN ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL [SIMP_TAC [], ASM_SIMP_TAC [RING_MUL_RZERO], REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [INT_SUB_REFL] THEN ASM_SIMP_TAC [RING_SUB_LDISTRIB, RING_SUM]], DISCH_THEN (X_CHOOSE_THEN (← q r"M:num->num->int") ((LABEL_TAC "L") o ((REWRITE_RULE [EXTENSION, IN_ELIM_THM]) o SYM)))] THEN SUBGOAL_THEN (← q r"!z. (lc:(num->int)->A) z IN ring_carrier k") ASSUME_TAC THENL [EXPAND_TAC "lc" THEN REWRITE_TAC [RING_SUM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"{i:num | i < n}"), (← q r"int_matrix_image {i:num | i < n} M"), (← q r"M:num->num->int"), (← q r"D:int")] INT_LATTICE_FULL_RANK) THEN USE_THEN "L" (fun th => REWRITE_TAC [th]) THEN REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN ANTS_TAC THENL [CONJ_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC [RING_OF_INT_0], ALL_TAC] THEN X_GEN_TAC (← q r"x:num->int") THEN DISCH_TAC THEN ASM_SIMP_TAC [INT_MUL_RZERO] THEN EXPAND_TAC "lc" THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [RING_MUL_ASSOC, RING_OF_INT, RING_SUM, RING_MUL_LID], DISCH_TAC] THEN SUBGOAL_THEN (← q r"!z. ring_sum k {j | j < n}
            (\j:num. ring_mul k (ring_of_int k (z j))
                   (ring_mul k e ((lc:(num->int)->A) (\i. M i j)))) =
          ring_mul k e (lc (\i. isum {j | j < n} (\j. M i j * z j)))") (LABEL_TAC "key") THENL [GEN_TAC THEN EXPAND_TAC "lc" THEN ASM_REWRITE_TAC [] THEN wPart rand (rand o rand) RING_SUM_LMUL THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_NUMSEG_LT, RING_MUL, RING_OF_INT, RING_SUM], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC RING_SUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC [] THEN MATCH_MP_TAC r2 THEN ASM_REWRITE_TAC [RING_OF_INT, RING_SUM], ALL_TAC] THEN EXISTS_TAC (← q r"\j:num. ring_mul k e ((lc:(num->int)->A) (\i. (M:num->num->int) i j))") THEN REWRITE_TAC [] THEN USE_THEN "key" (fun th => REWRITE_TAC [th]) THEN REPEAT CONJ_TAC THENL [X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN USE_THEN "L" (MP_TAC o (SPEC (← q r"\i. if i < n then (M:num->num->int) i j
                                       else &0"))) THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [REWRITE_TAC [int_matrix_image, IN_IMAGE, IN_UNIV, IN_ELIM_THM] THEN EXISTS_TAC (← q r"\l:num. if l = j then (&1:int) else &0") THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"i:num") THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [COND_RAND, INT_MUL_RID, INT_MUL_RZERO, ISUM_DELTA_GEN, IN_ELIM_THM], MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "lc" THEN MATCH_MP_TAC RING_SUM_EQ THEN SIMP_TAC [IN_ELIM_THM]], X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN REMOVE_THEN "den" (MP_TAC o (SPEC (← q r"x:A"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"c:num->int")) THEN SUBGOAL_THEN (← q r"ring_mul k e (ring_mul k (ring_of_int k D) x) = x:A") (LABEL_TAC "ex") THENL [ASM_SIMP_TAC [RING_MUL_ASSOC, RING_OF_INT, RING_MUL_LID], ALL_TAC] THEN SUBGOAL_THEN (← q r"(lc:(num->int)->A) (\i. if i < n then c i else &0) =
        ring_mul k (ring_of_int k D) x") (LABEL_TAC "Dx") THENL [EXPAND_TAC "lc" THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC RING_SUM_EQ THEN SIMP_TAC [IN_ELIM_THM], ALL_TAC] THEN SUBGOAL_THEN (← q r"(\i. if i < n then (c:num->int) i else &0) IN
        int_matrix_image {i | i < n} M") MP_TAC THENL [USE_THEN "L" (fun th => REWRITE_TAC [th]) THEN USE_THEN "Dx" SUBST1_TAC THEN USE_THEN "ex" SUBST1_TAC THEN ASM_SIMP_TAC [], REWRITE_TAC [int_matrix_image, IN_IMAGE, IN_UNIV]] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"z:num->int") THEN DISCH_THEN (MP_TAC o (AP_TERM (← q r"\v:num->int. ring_mul k e (lc v):A"))) THEN REWRITE_TAC [] THEN USE_THEN "Dx" SUBST1_TAC THEN USE_THEN "ex" SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "lc" THEN MATCH_MP_TAC RING_SUM_EQ THEN SIMP_TAC [IN_ELIM_THM], X_GEN_TAC (← q r"c:num->int") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"{i:num | i < n}"), (← q r"M:num->num->int"), (← q r"c:num->int"), (← q r"\j:num. (&0:int)")] INT_MATRIX_IMAGE_INJECTIVE) THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, INT_MUL_RZERO, ISUM_0] THEN DISCH_THEN MATCH_MP_TAC THEN REMOVE_THEN "indep" MATCH_MP_TAC THEN FIRST_X_ASSUM (MP_TAC o (AP_TERM (← q r"ring_mul k (ring_of_int k D):A->A"))) THEN ASM_SIMP_TAC [RING_MUL_ASSOC, RING_OF_INT, RING_MUL_LID, RING_MUL_RZERO] THEN EXPAND_TAC "lc" THEN ASM_REWRITE_TAC []])

  let NUMBER_FIELD_IMP_FIELD ← prove
    r"!k:A ring. number_field k ==> field k"
    (SIMP_TAC [number_field, finite_extension, field_extension])

  let NUMBER_FIELD_RING_OF_NUM_EQ_0 ← prove
    r"!k:A ring n. number_field k ==> (ring_of_num k n = ring_0 k <=> n = 0)"
    (REPEAT STRIP_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE [number_field]) THEN ASM_REWRITE_TAC [RING_OF_NUM_EQ_0] THEN CONV_TAC NUMBER_RULE)

  let NUMBER_FIELD_ALT ← prove
    r"!k:A ring.
        number_field k <=>
        field k /\ ring_char k = 0 /\
        ?n g. free_basis (subfield_generated k {ring_0 k},k) I n g"
    (GEN_TAC THEN REWRITE_TAC [number_field, FINITE_EXTENSION_BASIS] THEN ASM_CASES_TAC (← q r"field(k:A ring)") THENL [ALL_TAC, ASM_MESON_TAC [field_extension]] THEN ASM_SIMP_TAC [FIELD_EXTENSION_SUBFIELD_GENERATED] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{ring_0 k:A}")] FIELD_EXTENSION_SUBFIELD_GENERATED) THEN ASM_REWRITE_TAC [field_extension] THEN REWRITE_TAC [ring_monomorphism] THEN STRIP_TAC THEN AP_TERM_TAC THEN EQ_TAC THENL [REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"b:A->bool") THEN STRIP_TAC THEN EXISTS_TAC (← q r"CARD(b:A->bool)") THEN MATCH_MP_TAC FREE_BASIS_FROM_RING_BASIS THEN ASM_REWRITE_TAC [], REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"n:num"), (← q r"g:num->A")] THEN DISCH_TAC THEN EXISTS_TAC (← q r"IMAGE (g:num->A) {i | i < n}") THEN SIMP_TAC [FINITE_IMAGE, FINITE_NUMSEG_LT] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"n:num"), (← q r"g:num->A")] FREE_BASIS_FIELD) THEN ASM_REWRITE_TAC [] THEN SIMP_TAC []])

  let NUMBER_FIELD_FREE_BASIS_DEGREE ← prove
    r"!k:A ring n g.
        number_field k /\
        free_basis (subfield_generated k {ring_0 k},k) I n g
        ==> n = extension_degree (subfield_generated k {ring_0 k},k) I"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC FREE_BASIS_EXTENSION_DEGREE THEN EXISTS_TAC (← q r"g:num->A") THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, NUMBER_FIELD_IMP_FIELD, RING_HOMOMORPHISM_SUBFIELD_INCLUSION])

  let NUMBER_FIELD_FREE_BASIS ← prove
    r"!k:A ring.
        number_field k
        ==> ?g. free_basis (subfield_generated k {ring_0 k},k) I
                  (extension_degree (subfield_generated k {ring_0 k},k) I) g"
    (MESON_TAC [number_field, FINITE_EXTENSION_FREE_BASIS])

  let NUMBER_FIELD_DEGREE_POS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"1 <= n <=> ~(n = 0)")
    prove
      r"!k:A ring.
          number_field k
          ==> 1 <= extension_degree (subfield_generated k {ring_0 k},k) I"
      (GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM ((X_CHOOSE_TAC (← q r"g:num->A")) o (MATCH_MP NUMBER_FIELD_FREE_BASIS)) THEN REWRITE_TAC [r1] THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (CONJUNCT1 o (CONJUNCT2 o (GEN_REWRITE_RULE id [free_basis])))) THEN ASM_REWRITE_TAC [LT, EMPTY_GSPEC, RING_SUM_CLAUSES] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"ring_1 k:A"))) THEN ASM_SIMP_TAC [RING_1, FIELD_NONTRIVIAL, NUMBER_FIELD_IMP_FIELD])

  let NUMBER_FIELD_DEGREE_EQ_1 ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"i < 1 <=> i = 0")
    let r2 ← ARITH_RULE (← q r"1 = n ==> n = 1")
    let r7 ← ARITH_RULE (← q r"i < 1 <=> i = 0")
    prove
      r"!k:A ring.
          number_field k
          ==> (extension_degree (subfield_generated k {ring_0 k},k) I = 1 <=>
               ring_carrier(subfield_generated k {ring_0 k}) = ring_carrier k)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{ring_0 k:A}")] RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN DISCH_TAC THEN EQ_TAC THEN DISCH_TAC THENL [FIRST_ASSUM ((X_CHOOSE_TAC (← q r"g:num->A")) o (MATCH_MP NUMBER_FIELD_FREE_BASIS)) THEN FIRST_X_ASSUM (MP_TAC o (GEN_REWRITE_RULE id [free_basis])) THEN ASM_REWRITE_TAC [r7, FORALL_UNWIND_THM2, SING_GSPEC, RING_SUM_SING, I_THM] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o CONJUNCT1)) THEN ASM_REWRITE_TAC [(← GSYM SUBSET_ANTISYM_EQ), SUBSET] THEN FIRST_ASSUM (MP_TAC o (SPEC (← q r"ring_1 k:A"))) THEN REWRITE_TAC [RING_1, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"c:num->A") THEN STRIP_TAC THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"x:A"))) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"d:num->A") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(c:num->A) 0 IN ring_carrier k /\ (d:num->A) 0 IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN REPEAT (FIRST_X_ASSUM (MP_TAC o (checkM (fun z3 => (do let z4 ← (do let z5 ← (do let z6 ← (pure z3); pure (concl z6)); liftExcept (rand z5)); pure (HolCore.Classic.is_cond z4)))))) THEN ASM_SIMP_TAC [RING_MUL] THEN REPEAT DISCH_TAC THEN SUBGOAL_THEN (← q r"(g:num->A) 0 = ring_inv k (c 0)") SUBST1_TAC THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_RINV_UNIQUE THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MATCH_MP_TAC RING_MUL_IN_SUBFIELD_GENERATED THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC RING_INV_IN_SUBFIELD_GENERATED THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED], MATCH_MP_TAC r2 THEN MATCH_MP_TAC NUMBER_FIELD_FREE_BASIS_DEGREE THEN EXISTS_TAC (← q r"(\i. ring_1 k):num->A") THEN ASM_REWRITE_TAC [free_basis, r1, FORALL_UNWIND_THM2, SING_GSPEC, RING_SUM_SING, I_THM, RING_1] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN EXISTS_TAC (← q r"(\i. x):num->A") THEN ASM_SIMP_TAC [RING_MUL, RING_1, RING_MUL_RID], X_GEN_TAC (← q r"c:num->A") THEN REWRITE_TAC [IMP_CONJ] THEN DISCH_TAC THEN ASM_SIMP_TAC [RING_MUL, RING_1, RING_MUL_RID, SUBFIELD_GENERATED]]])

  let NUMBER_FIELD_ALGEBRAIC ← prove
    r"!k:A ring x.
        number_field k /\ x IN ring_carrier k
        ==> algebraic_over (subfield_generated k {ring_0 k},k) I x"
    (REWRITE_TAC [number_field] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (MATCH_MP FINITE_IMP_ALGEBRAIC_EXTENSION)) THEN ASM_SIMP_TAC [algebraic_extension])

  let NUMBER_FIELD_PRIME_SUBFIELD ← prove
    r"!k:A ring.
        field k /\ ring_char k = 0
        ==> number_field (subfield_generated k {ring_0 k}) /\
            extension_degree (subfield_generated k {ring_0 k},
                              subfield_generated k {ring_0 k}) I = 1"
    (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [EXTENSION_DEGREE_REFL, FIELD_SUBFIELD_GENERATED] THEN ASM_REWRITE_TAC [number_field, RING_CHAR_SUBFIELD_GENERATED, PRIME_SUBFIELD_SUBFIELD_GENERATED] THEN MATCH_MP_TAC FINITE_EXTENSION_ISOMORPHISM THEN ASM_SIMP_TAC [RING_ISOMORPHISM_I, FIELD_SUBFIELD_GENERATED])

  let NUMBER_FIELD_RATIONAL_FIELD ← prove
    r"number_field (subfield_generated real_ring {&0})"
    (MP_TAC (← ISPEC (← q r"real_ring") NUMBER_FIELD_PRIME_SUBFIELD) THEN SIMP_TAC [FIELD_REAL_RING, REAL_RING_CHAR, REAL_RING_CLAUSES])

  let NUMBER_FIELD_SUBFIELD_GENERATED_ALGEBRAIC ← prove
    r"!(k:A ring) s.
        field k /\ ring_char k = 0 /\ FINITE s /\
        (!x. x IN s ==> algebraic_over (subfield_generated k {ring_0 k},k) I x)
        ==> number_field(subfield_generated k s)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"s:A->bool")] FINITE_FINITELY_GENERATED_ALGEBRAIC_EXTENSION) THEN ASM_REWRITE_TAC [FIELD_EXTENSION_SUBFIELD_GENERATED, IMAGE_I] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"subring_generated k
      (ring_carrier(subfield_generated k {ring_0 k}) UNION s) =
    subfield_generated k (s:A->bool)") ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP FINITE_IMP_FIELD_EXTENSION)) THEN REWRITE_TAC [field_extension] THEN STRIP_TAC THEN FIRST_ASSUM (SUBST1_TAC o (MATCH_MP SUBRING_EQ_SUBFIELD_GENERATED)) THEN REWRITE_TAC [SUBFIELD_GENERATED_UNION_LEFT] THEN MATCH_MP_TAC SUBFIELDS_GENERATED_EQ THEN X_GEN_TAC (← q r"j:A->bool") THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP IN_SUBFIELD_0)) THEN SET_TAC [], REWRITE_TAC [number_field, RING_CHAR_SUBFIELD_GENERATED, PRIME_SUBFIELD_SUBFIELD_GENERATED] THEN ASM_MESON_TAC []])

  let PRIME_SUBFIELD_CHAR_0 ← prove
    r"!k:A ring.
        field k /\ ring_char k = 0
        ==> ring_carrier(subfield_generated k {ring_0 k}) =
            {ring_div k (ring_of_int k a) (ring_of_int k b) | a,b |
             ~(b = &0)}"
    (REPEAT STRIP_TAC THEN wPart lhand (lhand o rand) RING_CARRIER_SUBFIELD_GENERATED_SUBRING_QUOTIENTS THEN REWRITE_TAC [RING_CARRIER_SUBRING_GENERATED_0] THEN ANTS_TAC THENL [ASM_SIMP_TAC [FIELD_IMP_NONTRIVIAL_RING, FIELD_UNIT, IN_ELIM_THM, IN_UNIV] THEN MESON_TAC [RING_OF_INT], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_UNIV] THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INT_EQ_0_CHAR_0) THEN ASM_REWRITE_TAC [] THEN MESON_TAC [])

  let REAL_PRIME_SUBFIELD ← prove
    r"ring_carrier(subfield_generated real_ring {&0}) = rational"
    (MP_TAC (← ISPEC (← q r"real_ring") PRIME_SUBFIELD_CHAR_0) THEN REWRITE_TAC [FIELD_REAL_RING, REAL_RING_CHAR, REAL_RING_CLAUSES, REAL_RING_DIV, REAL_RING_OF_INT] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN REWRITE_TAC [IN, rational, int_eq, int_of_num_th] THEN MESON_TAC [int_tybij, INTEGER_REAL_OF_INT])

  let PRIME_SUBFIELD_COMMON_DENOMINATOR ← prove
    r"!k:A ring (s:K->bool) f.
        field k /\ FINITE s /\
        (!i. i IN s ==> f i IN ring_carrier(subfield_generated k {ring_0 k}))
        ==> ?d. ~(d = &0) /\
                !i. i IN s
                    ==> ?m. ring_mul k (ring_of_int k d) (f i) =
                            ring_of_int k m"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{ring_0 k:A}"), (← q r"IMAGE (f:K->A) s")] FINITE_SUBSET_SUBFIELD_GENERATED_DENOMINATOR) THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, FINITE_IMAGE, SUBSET, FORALL_IN_IMAGE, RING_CARRIER_SUBRING_GENERATED_0, IMP_CONJ, FORALL_IN_GSPEC, IN_UNIV, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"d:int") THEN REWRITE_TAC [IN_ELIM_THM, IN_UNIV] THEN REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"d:int") THEN ASM_SIMP_TAC [] THEN ASM_MESON_TAC [RING_OF_INT_0])

  let FREE_BASIS_PRIME_SUBFIELD_DENOMINATOR ← prove
    r"!k:A ring n g s.
        field k /\ free_basis (subfield_generated k {ring_0 k},k) I n g /\
        FINITE s /\ s SUBSET ring_carrier k
        ==> ?d. ~(d = &0) /\
                !y. y IN s
                    ==> ?c. ring_mul k (ring_of_int k d) y =
                            ring_sum k {i | i < n}
                              (\i. ring_mul k (ring_of_int k (c i)) (g i))"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [free_basis]))) THEN ABBREV_TAC (← q r"C = basis_coordinates (subfield_generated k {ring_0 k},k) I n
          (g:num->A)") THEN SUBGOAL_THEN (← q r"!y. y IN s
        ==> (!i. i < n
                 ==> (C:A->num->A) y i IN
                     ring_carrier(subfield_generated k {ring_0 k})) /\
            ring_sum k {i | i < n} (\i. ring_mul k (C y i) ((g:num->A) i)) = y") ASSUME_TAC THENL [X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"n:num"), (← q r"g:num->A"), (← q r"y:A")] BASIS_COORDINATES) THEN ANTS_TAC THENL [ASM SET_TAC [], ASM_REWRITE_TAC [I_THM]] THEN MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"(s:A->bool) CROSS {i:num | i < n}"), (← q r"\(y,i). (C:A->num->A) y i")] PRIME_SUBFIELD_COMMON_DENOMINATOR) THEN ASM_SIMP_TAC [FINITE_CROSS, FINITE_NUMSEG_LT, FORALL_PAIR_THM, IN_CROSS, IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"d:int") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN ((X_CHOOSE_TAC (← q r"V:A->num->int")) o (REWRITE_RULE [RIGHT_IMP_EXISTS_THM, SKOLEM_THM])) THEN X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN EXISTS_TAC (← q r"(V:A->num->int) y") THEN FIRST_ASSUM (MP_TAC o (← do let c := (← ASSUME (← q r"(y:A) IN s")); pure (fun th => MATCH_MP th c))) THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (fun th => tactic_of do pure (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [(← SYM th)]))) THEN SUBGOAL_THEN (← q r"!i. i < n ==> (C:A->num->A) y i IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBSET], ALL_TAC] THEN wPart lhand (rand o rand) RING_SUM_LMUL THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_OF_INT, FINITE_NUMSEG_LT, IN_ELIM_THM, RING_MUL], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [RING_MUL_ASSOC, RING_OF_INT])

  let FREE_BASIS_PRIME_SUBFIELD_INT_LINCOMB ← prove
    r"!k:A ring n w.
        field k /\ ring_char k = 0 /\
        (!i. i < n ==> w i IN ring_carrier k) /\
        (!c. ring_sum k {i | i < n}
               (\i. ring_mul k (ring_of_int k (c i)) (w i)) = ring_0 k
             ==> !i. i < n ==> c i = &0) /\
        (!x. x IN ring_carrier k
             ==> ?d c. ~(d = &0) /\
                       ring_mul k (ring_of_int k d) x =
                       ring_sum k {i | i < n}
                         (\i. ring_mul k (ring_of_int k (c i)) (w i)))
        ==> free_basis (subfield_generated k {ring_0 k},k) I n w"
    (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "indep") (LABEL_TAC "span"))))) THEN SUBGOAL_THEN (← q r"!x:A. x IN ring_carrier(subfield_generated k {ring_0 k})
          ==> x IN ring_carrier k") ASSUME_TAC THENL [MESON_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBSET], ALL_TAC] THEN REWRITE_TAC [free_basis, I_THM, (← CONJUNCT1 (← CONJUNCT2 SUBFIELD_GENERATED))] THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN REMOVE_THEN "span" (MP_TAC o (SPEC (← q r"x:A"))) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"d:int"), (← q r"c:num->int")] THEN STRIP_TAC THEN EXISTS_TAC (← q r"\i:num. ring_mul k (ring_inv k (ring_of_int k d))
                        (ring_of_int k ((c:num->int) i)):A") THEN ASM_SIMP_TAC [RING_MUL_IN_SUBFIELD_GENERATED, RING_INV_IN_SUBFIELD_GENERATED, RING_OF_INT_IN_SUBFIELD_GENERATED, FIELD_SUBFIELD_GENERATED] THEN SUBGOAL_THEN (← q r"ring_inv k (ring_of_int k d) IN ring_carrier k /\
      ring_mul k (ring_inv k (ring_of_int k d)) (ring_of_int k d) = ring_1 k:A") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_INV, RING_OF_INT, FIELD_MUL_LINV, RING_OF_INT_EQ_0_CHAR_0], ALL_TAC] THEN TRANS_TAC EQ_TRANS (← q r"ring_mul k (ring_inv k (ring_of_int k d))
        (ring_mul k (ring_of_int k d) x):A") THEN CONJ_TAC THENL [ASM_SIMP_TAC [RING_MUL_ASSOC, RING_OF_INT, RING_MUL_LID], ALL_TAC] THEN ASM_SIMP_TAC [(← GSYM RING_SUM_LMUL), FINITE_NUMSEG_LT, IN_ELIM_THM, RING_MUL, RING_OF_INT, RING_INV] THEN MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL_ASSOC THEN ASM_SIMP_TAC [RING_INV, RING_OF_INT], X_GEN_TAC (← q r"q:num->A") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!i. i < n ==> (q:num->A) i IN ring_carrier k") ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{i:num | i < n}"), (← q r"q:num->A")] PRIME_SUBFIELD_COMMON_DENOMINATOR) THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"d:int") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"m:num->int") (LABEL_TAC "m")) THEN REMOVE_THEN "indep" (MP_TAC o (SPEC (← q r"m:num->int"))) THEN ANTS_TAC THENL [TRANS_TAC EQ_TRANS (← q r"ring_sum k {i | i < n}
          (\i. ring_mul k (ring_of_int k d)
                 (ring_mul k (q i) ((w:num->A) i)))") THEN CONJ_TAC THENL [MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [RING_MUL_ASSOC, RING_OF_INT], ASM_SIMP_TAC [RING_SUM_LMUL, FINITE_NUMSEG_LT, IN_ELIM_THM, RING_MUL, RING_OF_INT, RING_MUL_RZERO]], MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC (← q r"i:num") THEN ASM_CASES_TAC (← q r"i:num < n") THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN REMOVE_THEN "m" (MP_TAC o (SPEC (← q r"i:num"))) THEN ASM_SIMP_TAC [RING_OF_INT_0, INTEGRAL_DOMAIN_MUL_EQ_0, FIELD_IMP_INTEGRAL_DOMAIN, RING_OF_INT, RING_OF_INT_EQ_0_CHAR_0]]])

  let NUMBER_FIELD_INT_LINCOMB_SANDWICH ← prove
    r"!k:A ring n g t D.
        number_field k /\
        free_basis (subfield_generated k {ring_0 k},k) I n g /\
        ~(D = &0) /\ t SUBSET ring_carrier k /\
        (!x y. x IN t /\ y IN t ==> ring_sub k x y IN t) /\
        (!c. ring_sum k {i | i < n}
               (\i. ring_mul k (ring_of_int k (c i)) (g i)) IN t) /\
        (!x. x IN t
             ==> ?c. ring_mul k (ring_of_int k D) x =
                     ring_sum k {i | i < n}
                       (\i. ring_mul k (ring_of_int k (c i)) (g i)))
        ==> ?w. free_basis (subfield_generated k {ring_0 k},k) I n w /\
                (!i. i < n ==> w i IN t) /\
                (!x. x IN t
                     ==> ?c. x = ring_sum k {i | i < n}
                                   (\i. ring_mul k (ring_of_int k (c i))
                                                   (w i)))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [free_basis]))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"t:A->bool"), (← q r"n:num"), (← q r"g:num->A"), (← q r"D:int")] RING_INT_LINCOMB_SANDWICH) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_OF_INT_EQ_0_CHAR_0] THEN X_GEN_TAC (← q r"a:num->int") THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o ((SPEC (← q r"\i. ring_of_int k ((a:num->int) i):A")) o (CONJUNCT2 o (CONJUNCT2 o (GEN_REWRITE_RULE id [free_basis]))))) THEN ASM_REWRITE_TAC [I_THM, RING_OF_INT_IN_SUBFIELD_GENERATED, (← CONJUNCT1 (← CONJUNCT2 SUBFIELD_GENERATED))] THEN ASM_SIMP_TAC [RING_OF_INT_EQ_0_CHAR_0], MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"w:num->A") THEN STRIP_TAC THEN ASM_REWRITE_TAC []] THEN MATCH_MP_TAC FREE_BASIS_PRIME_SUBFIELD_INT_LINCOMB THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"g:num->A"), (← q r"{y:A}")] FREE_BASIS_PRIME_SUBFIELD_DENOMINATOR) THEN ASM_REWRITE_TAC [FINITE_SING, SING_SUBSET, IN_SING, FORALL_UNWIND_THM2] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"d:int") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC (← q r"a:num->int"))) THEN ASM_SIMP_TAC [])

  let RING_OF_INTEGERS_CARRIER ← prove
    r"!k:A ring.
        ring_carrier(ring_of_integers k) =
        {x | integral_element (integer_ring,k) (ring_of_int k) x}"
    (GEN_TAC THEN REWRITE_TAC [ring_of_integers] THEN MATCH_MP_TAC CARRIER_SUBRING_GENERATED_SUBRING THEN MATCH_MP_TAC INTEGRAL_CLOSURE_SUBRING THEN REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT])

  let RING_OF_INTEGERS_SUBSET ← prove
    r"!k:A ring. ring_carrier(ring_of_integers k) SUBSET ring_carrier k"
    (REWRITE_TAC [ring_of_integers, RING_CARRIER_SUBRING_GENERATED_SUBSET])

  let RING_OF_INTEGERS_SUBRING ← prove
    r"(!k:A ring. ring_carrier(ring_of_integers k) subring_of k) /\
   (!k:A ring. subring_generated k (ring_carrier(ring_of_integers k)) =
               ring_of_integers k)"
    (REWRITE_TAC [RING_OF_INTEGERS_CARRIER] THEN REWRITE_TAC [ring_of_integers] THEN SIMP_TAC [INTEGRAL_CLOSURE_SUBRING, RING_HOMOMORPHISM_INTEGER_RING_OF_INT])

  let RING_OF_INTEGERS ← prove
    r"(!k:A ring. ring_0(ring_of_integers k) = ring_0 k) /\
   (!k:A ring. ring_1(ring_of_integers k) = ring_1 k) /\
   (!k:A ring. ring_neg(ring_of_integers k) = ring_neg k) /\
   (!k:A ring. ring_add(ring_of_integers k) = ring_add k) /\
   (!k:A ring. ring_mul(ring_of_integers k) = ring_mul k) /\
   (!k:A ring. ring_sub(ring_of_integers k) = ring_sub k) /\
   (!k:A ring. ring_pow(ring_of_integers k) = ring_pow k) /\
   (!k:A ring. ring_of_num(ring_of_integers k) = ring_of_num k) /\
   (!k:A ring. ring_of_int(ring_of_integers k) = ring_of_int k)"
    (REWRITE_TAC [ring_of_integers, SUBRING_GENERATED, RING_SUB_SUBRING_GENERATED, RING_POW_SUBRING_GENERATED, RING_OF_NUM_SUBRING_GENERATED, RING_OF_INT_SUBRING_GENERATED])

  let RING_SUM_RING_OF_INTEGERS ← prove
    r"!k:A ring s (f:K->A).
        (!i. i IN s ==> f i IN ring_carrier(ring_of_integers k))
        ==> ring_sum (ring_of_integers k) s f = ring_sum k s f"
    (REPEAT GEN_TAC THEN REWRITE_TAC [ring_of_integers, RING_SUM_SUBRING_GENERATED_GEN] THEN DISCH_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC [])

  let RING_PRODUCT_RING_OF_INTEGERS ← prove
    r"!k:A ring s (f:K->A).
        (!i. i IN s ==> f i IN ring_carrier(ring_of_integers k))
        ==> ring_product (ring_of_integers k) s f = ring_product k s f"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_carrier(ring_of_integers k:A ring)"), (← q r"s:K->bool"), (← q r"f:K->A")] RING_PRODUCT_SUBRING_GENERATED) THEN REWRITE_TAC [RING_OF_INTEGERS_SUBRING] THEN DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC [])

  let RING_OF_INT_IN_RING_OF_INTEGERS ← prove
    r"!k:A ring n. ring_of_int k n IN ring_carrier(ring_of_integers k)"
    (REWRITE_TAC [RING_OF_INTEGERS_CARRIER] THEN REPEAT GEN_TAC THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"k:A ring"), (← q r"ring_of_int k:int->A")] INTEGRAL_CLOSURE_SUPSET_IMAGE) THEN REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, SUBSET, FORALL_IN_IMAGE, INTEGER_RING, IN_UNIV] THEN SIMP_TAC [])

  let ROOT_OF_UNITY_IN_RING_OF_INTEGERS ← prove
    r"!(k:A ring) x n.
        x IN ring_carrier k /\ ~(n = 0) /\ ring_pow k x n = ring_1 k
        ==> x IN ring_carrier(ring_of_integers k)"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM] THEN SIMP_TAC [INTEGRAL_ELEMENT_EXPLICIT, RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN ASM_REWRITE_TAC [] THEN MAP_EVERY EXISTS_TAC [(← q r"n:num"), (← q r"\i:num. if i = 0 then --(&1):int else &0")] THEN ASM_REWRITE_TAC [LT_NZ, INTEGER_RING, IN_UNIV] THEN SUBGOAL_THEN (← q r"ring_sum k {i | i < n}
      (\i. ring_mul k (ring_of_int k (if i = 0 then --(&1) else &0))
                    (ring_pow k (x:A) i)) =
    ring_sum k {i | i < n}
      (\i. if i = 0 then ring_neg k (ring_1 k) else ring_0 k)") SUBST1_TAC THENL [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN REWRITE_TAC [] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [ring_pow, RING_OF_INT_NEG, RING_OF_INT_OF_NUM, RING_OF_NUM_1, RING_OF_NUM_0] THEN ASM_SIMP_TAC [RING_MUL_RID, RING_MUL_LZERO, RING_NEG, RING_1, RING_POW], REWRITE_TAC [RING_SUM_DELTA, IN_ELIM_THM] THEN ASM_SIMP_TAC [LT_NZ, RING_NEG, RING_1, RING_ADD_RNEG]])

  -- @@RETURN BEGIN
  return { number_field, ring_of_integers, RING_INT_LINCOMB_SWAP, RING_INT_LINCOMB,
           RING_MUL_INT_LINCOMB, RING_INT_LINCOMB_LINCOMB, RING_INT_LINCOMB_SANDWICH,
           NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_RING_OF_NUM_EQ_0, NUMBER_FIELD_ALT,
           NUMBER_FIELD_FREE_BASIS_DEGREE, NUMBER_FIELD_FREE_BASIS,
           NUMBER_FIELD_DEGREE_POS, NUMBER_FIELD_DEGREE_EQ_1, NUMBER_FIELD_ALGEBRAIC,
           NUMBER_FIELD_PRIME_SUBFIELD, NUMBER_FIELD_RATIONAL_FIELD,
           NUMBER_FIELD_SUBFIELD_GENERATED_ALGEBRAIC, PRIME_SUBFIELD_CHAR_0,
           REAL_PRIME_SUBFIELD, PRIME_SUBFIELD_COMMON_DENOMINATOR,
           FREE_BASIS_PRIME_SUBFIELD_DENOMINATOR, FREE_BASIS_PRIME_SUBFIELD_INT_LINCOMB,
           NUMBER_FIELD_INT_LINCOMB_SANDWICH, RING_OF_INTEGERS_CARRIER,
           RING_OF_INTEGERS_SUBSET, RING_OF_INTEGERS_SUBRING, RING_OF_INTEGERS,
           RING_SUM_RING_OF_INTEGERS, RING_PRODUCT_RING_OF_INTEGERS,
           RING_OF_INT_IN_RING_OF_INTEGERS, ROOT_OF_UNITY_IN_RING_OF_INTEGERS }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- numfield.ml phrases from line 843 to 1567                              -/
/- ---------------------------------------------------------------------- -/

structure Numfield02 where
  -- @@FIELDS
  RING_OF_INTEGERS_ROOT_OF_UNITY_UNIT : thm
  INTEGRAL_DOMAIN_RING_OF_INTEGERS : thm
  RING_OF_INTEGERS_UNIT_NONZERO : thm
  RING_OF_INTEGERS_PRIME_SUBFIELD : thm
  RING_OF_INTEGERS_ALGEBRAIC : thm
  RING_OF_INTEGERS_RING_OF_INT_MUL : thm
  RING_HOMOMORPHISM_RING_OF_INTEGERS : thm
  RING_MONOMORPHISM_RING_OF_INTEGERS : thm
  RING_ISOMORPHISM_RING_OF_INTEGERS : thm
  ISOMORPHIC_RING_RING_OF_INTEGERS : thm
  NUMBER_FIELD_INTEGRAL_MULTIPLE : thm
  RING_OF_INTEGERS_DENOMINATOR : thm
  RING_OF_INTEGERS_COMMON_DENOMINATOR : thm
  RING_OF_INTEGERS_IN_IDEAL_GENERATED_SING : thm
  RING_OF_INTEGERS_IDEAL_GENERATED_SING_EQ_0 : thm
  NUMBER_FIELD_INTEGRAL_FREE_BASIS : thm
  NUMBER_FIELD_TRACE_ADD : thm
  NUMBER_FIELD_NORM_MUL : thm
  NUMBER_FIELD_NORM_EQ_0 : thm
  NUMBER_FIELD_NORM_RATIONAL : thm
  NUMBER_FIELD_NORM_SUB_MINIMAL_POLYNOMIAL : thm
  NUMBER_FIELD_TRACE_RATIONAL : thm
  NUMBER_FIELD_TRACE_SCALAR_MUL : thm
  NUMBER_FIELD_TRACE_MUL_LINCOMB : thm
  NUMBER_FIELD_TRACE_FORM_INJECTIVE : thm
  RING_OF_INTEGERS_INTEGER_MATRIX : thm
  NUMBER_FIELD_TRACE_INTEGRAL_Q : thm
  NUMBER_FIELD_TRACE_IN_RING_OF_INTEGERS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupNumfield02 [HolBase] (D : NumfieldDeps) (BNumfield01 : Numfield01) :
    ExceptT String IO Numfield02 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, RING_RULE,
        SET_TAC, TAUT, .. } := D
  let { ALGEBRA_NORM_EQ_0, ALGEBRA_NORM_MUL, ALGEBRA_NORM_SUB_CHARPOLY,
        ALGEBRA_TRACE_ADD, ALGEBRA_TRACE_MUL_LINCOMB, ALGEBRA_TRACE_NORM_BASE,
        ALGEBRA_TRACE_NORM_IN_CARRIER, ALGEBRA_TRACE_SCALAR, ALGEBRA_TRACE_SUBRING,
        COND_RAND, COND_RATOR, DIVIDES_ZERO, EQ_MULT_LCANCEL, EQ_TRANS, ETA_AX,
        EXTENSION_DEGREE_TOWER_LAW, FIELD_CHARPOLY_MINIMAL_POLYNOMIAL,
        FIELD_EXTENSION_SUBFIELD_GENERATED, FIELD_IMP_INTEGRAL_DOMAIN, FIELD_MUL_LINV,
        FIELD_NONTRIVIAL, FIELD_SUBFIELD_GENERATED, FIELD_UNIT, FINITE_CROSS,
        FINITE_IMAGE, FINITE_IMP_FIELD_EXTENSION, FINITE_INDUCT_STRONG, FINITE_INSERT,
        FINITE_NUMSEG_LT, FORALL_IN_GSPEC, FORALL_IN_IMAGE, FORALL_IN_INSERT,
        FORALL_PAIR_THM, FREE_BASIS_IN_CARRIER, FREE_BASIS_SCALE, FUN_EQ_THM,
        IDEAL_GENERATED_EQ_0, IMP_CONJ, IMP_IMP, INSERT_SUBSET, INTEGER_RING,
        INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING, INTEGRAL_DOMAIN_MUL_EQ_0,
        INTEGRAL_DOMAIN_SUBRING_GENERATED, INTEGRAL_ELEMENT_EXPLICIT,
        INTEGRAL_ELEMENT_FINITE_MODULE, INTEGRAL_ELEMENT_HOMOMORPHIC_IMAGE,
        INTEGRAL_ELEMENT_IMAGE, INTEGRAL_ELEMENT_MUL, INTEGRAL_ELEMENT_OVER_SUBRING,
        INTEGRAL_ELEMENT_PRIME_SUBFIELD, INTEGRAL_OVER_FIELD_EQ_ALGEBRAIC, IN_CROSS,
        IN_ELIM_THM, IN_IDEAL_GENERATED_SING_EQ, IN_INTER, IN_SUBRING_MUL, IN_UNIV,
        I_O_ID, I_THM, LEFT_IMP_EXISTS_THM, MINIMAL_POLYNOMIAL, MONO_EXISTS,
        NOT_EXISTS_THM, .. } := D.core1
  let { NOT_IN_EMPTY, POLY_EVAL_SUBFIELD_GENERATED, POLY_POW_ALT, PRIME_SUBRING,
        RIGHT_FORALL_IMP_THM, RIGHT_IMP_EXISTS_THM, RING_1, RING_ADD_EQ_RIGHT,
        RING_CARRIER_SUBFIELD_GENERATED_SUBSET, RING_HOMOMORPHISM_BETWEEN_SUBRINGS,
        RING_HOMOMORPHISM_INTEGER_RING_OF_INT, RING_HOMOMORPHISM_RING_OF_INT,
        RING_HOMOMORPHISM_SUBFIELD_INCLUSION, RING_HOMOMORPHISM_SUM, RING_INV,
        RING_MUL, RING_MUL_ASSOC, RING_MUL_IN_SUBFIELD_GENERATED, RING_MUL_LID,
        RING_MUL_LINV, RING_MUL_LNEG, RING_MUL_LZERO, RING_MUL_RINV, RING_MUL_RZERO,
        RING_MUL_SYM, RING_OF_INT, RING_OF_INT_0, RING_OF_INT_1,
        RING_OF_INT_EQ_0_CHAR_0, RING_OF_INT_IN_SUBFIELD_GENERATED, RING_OF_INT_NEG,
        RING_OF_INT_SUBFIELD_GENERATED, RING_OF_NUM_EQ_0,
        RING_OF_NUM_SUBFIELD_GENERATED, RING_POW, RING_POW_1,
        RING_POW_SUBFIELD_GENERATED, RING_SUB, RING_SUB_EQ_0, RING_SUB_LDISTRIB,
        RING_SUM, RING_SUM_DELTA, RING_SUM_EQ_0, RING_SUM_NEG, RING_UNIT_0,
        RING_UNIT_IN_CARRIER, SKOLEM_THM, SUBFIELD_GENERATED,
        SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC, SUBRING_GENERATED_BY_SUBFIELD_GENERATED,
        SUBSET, SUBSET_ANTISYM_EQ, TRACE_FORM_NONDEGENERATE, field_extension,
        free_basis, isomorphic_ring, o_THM, ring_divides, ring_isomorphism,
        ring_isomorphisms, ring_monomorphism, ring_pow, ring_unit, .. } := D.core2
  let { FREE_BASIS_PRIME_SUBFIELD_DENOMINATOR, NUMBER_FIELD_ALGEBRAIC,
        NUMBER_FIELD_DEGREE_POS, NUMBER_FIELD_FREE_BASIS,
        NUMBER_FIELD_FREE_BASIS_DEGREE, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_INT_LINCOMB_SANDWICH, RING_INT_LINCOMB, RING_INT_LINCOMB_LINCOMB,
        RING_MUL_INT_LINCOMB, RING_OF_INTEGERS, RING_OF_INTEGERS_CARRIER,
        RING_OF_INTEGERS_SUBRING, RING_OF_INTEGERS_SUBSET,
        RING_OF_INT_IN_RING_OF_INTEGERS, ROOT_OF_UNITY_IN_RING_OF_INTEGERS,
        number_field, ring_of_integers, .. } := BNumfield01
  -- @@SCOPE END

  let RING_OF_INTEGERS_ROOT_OF_UNITY_UNIT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"1 <= n ==> SUC(n - 1) = n")
    prove
      r"!(k:A ring) x n.
          x IN ring_carrier k /\ 1 <= n /\ ring_pow k x n = ring_1 k
          ==> ring_unit (ring_of_integers k) x"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [MATCH_MP_TAC ROOT_OF_UNITY_IN_RING_OF_INTEGERS THEN EXISTS_TAC (← q r"n:num") THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [ring_unit] THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"ring_pow k x (n - 1):A") THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"x:A"), (← q r"n - 1")] RING_POW) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], REWRITE_TAC [RING_OF_INTEGERS] THEN REWRITE_TAC [(← GSYM (← CONJUNCT2 ring_pow))] THEN ASM_SIMP_TAC [r1]])

  let INTEGRAL_DOMAIN_RING_OF_INTEGERS ← prove
    r"!k:A ring. field k ==> integral_domain(ring_of_integers k)"
    (SIMP_TAC [ring_of_integers, INTEGRAL_DOMAIN_SUBRING_GENERATED, FIELD_IMP_INTEGRAL_DOMAIN])

  let RING_OF_INTEGERS_UNIT_NONZERO ← prove
    r"!k x:A.
        field k /\ ring_unit (ring_of_integers k) x
        ==> x IN ring_carrier k /\ ~(x = ring_0 k)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_UNIT_IN_CARRIER)) THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], DISCH_TAC] THEN UNDISCH_TAC (← q r"ring_unit (ring_of_integers k) (x:A)") THEN ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [(← GSYM (← CONJUNCT1 RING_OF_INTEGERS))] THEN ASM_SIMP_TAC [RING_UNIT_0, INTEGRAL_DOMAIN_RING_OF_INTEGERS, INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING])

  let RING_OF_INTEGERS_PRIME_SUBFIELD ← prove
    r"!k:A ring.
        field k /\ ring_char k = 0
        ==> ring_carrier(ring_of_integers k) INTER
            ring_carrier(subfield_generated k {ring_0 k}) =
            {ring_of_int k n | n IN (:int)}"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [(← GSYM SUBSET_ANTISYM_EQ), SUBSET, IN_INTER] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"x:A") THEN REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM, IN_UNIV] THEN STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_ELEMENT_PRIME_SUBFIELD THEN ASM_REWRITE_TAC [], REWRITE_TAC [FORALL_IN_GSPEC, IN_UNIV, RING_OF_INT_IN_RING_OF_INTEGERS, RING_OF_INT_IN_SUBFIELD_GENERATED]])

  let RING_OF_INTEGERS_ALGEBRAIC ← prove
    r"!(k:A ring) x.
        field k /\ x IN ring_carrier(ring_of_integers k)
        ==> algebraic_over (subfield_generated k {ring_0 k},k) I x"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"x:A")] INTEGRAL_OVER_FIELD_EQ_ALGEBRAIC) THEN ASM_REWRITE_TAC [FIELD_EXTENSION_SUBFIELD_GENERATED] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"k:A ring"), (← q r"ring_of_int k:int->A"), (← q r"ring_carrier(subfield_generated k {ring_0 k:A})"), (← q r"x:A")] INTEGRAL_ELEMENT_OVER_SUBRING) THEN REWRITE_TAC [SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN DISCH_THEN MATCH_MP_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM]) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"n:int") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_0 k:A}"), (← q r"n:int")] RING_OF_INT) THEN REWRITE_TAC [RING_OF_INT_SUBFIELD_GENERATED])

  let RING_OF_INTEGERS_RING_OF_INT_MUL ← prove
    r"!(k:A ring) c z.
        z IN ring_carrier(ring_of_integers k)
        ==> ring_mul k (ring_of_int k c) z IN ring_carrier(ring_of_integers k)"
    (REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_ELEMENT_MUL THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN MATCH_MP_TAC INTEGRAL_ELEMENT_IMAGE THEN REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, INTEGER_RING, IN_UNIV])

  let RING_HOMOMORPHISM_RING_OF_INTEGERS ← prove
    r"!k:A ring l:B ring h.
        ring_homomorphism(k,l) h
        ==> ring_homomorphism(ring_of_integers k,ring_of_integers l) h"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [ring_of_integers] THEN MATCH_MP_TAC RING_HOMOMORPHISM_BETWEEN_SUBRINGS THEN ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN SUBGOAL_THEN (← q r"ring_of_int l = (h:A->B) o ring_of_int k") SUBST1_TAC THENL [REWRITE_TAC [FUN_EQ_THM, o_THM] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_RING_OF_INT], REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_ELEMENT_HOMOMORPHIC_IMAGE THEN EXISTS_TAC (← q r"k:A ring") THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT]])

  let RING_MONOMORPHISM_RING_OF_INTEGERS ← prove
    r"!k:A ring l:B ring h.
        ring_monomorphism(k,l) h
        ==> ring_monomorphism(ring_of_integers k,ring_of_integers l) h"
    (REPEAT GEN_TAC THEN REWRITE_TAC [ring_monomorphism] THEN SIMP_TAC [RING_HOMOMORPHISM_RING_OF_INTEGERS] THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_SUBSET) THEN SET_TAC [])

  let RING_ISOMORPHISM_RING_OF_INTEGERS ← prove
    r"!k:A ring l:B ring h.
        ring_isomorphism(k,l) h
        ==> ring_isomorphism(ring_of_integers k,ring_of_integers l) h"
    (REPEAT GEN_TAC THEN REWRITE_TAC [ring_isomorphism, ring_isomorphisms] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN SIMP_TAC [RING_HOMOMORPHISM_RING_OF_INTEGERS] THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_SUBSET) THEN MP_TAC (← ISPEC (← q r"l:B ring") RING_OF_INTEGERS_SUBSET) THEN SET_TAC [])

  let ISOMORPHIC_RING_RING_OF_INTEGERS ← prove
    r"!k:A ring l:B ring.
        k isomorphic_ring l
        ==> ring_of_integers k isomorphic_ring ring_of_integers l"
    (REWRITE_TAC [isomorphic_ring] THEN MESON_TAC [RING_ISOMORPHISM_RING_OF_INTEGERS])

  let NUMBER_FIELD_INTEGRAL_MULTIPLE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul (r:A ring) (ring_mul r d x) (ring_mul r e g) =
        ring_mul r e (ring_mul r d (ring_mul r x g))")
    prove
      r"!k:A ring x.
          number_field k /\ x IN ring_carrier k
          ==> ?d. ~(d = &0) /\
                  ring_mul k (ring_of_int k d) x IN
                  ring_carrier(ring_of_integers k)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN FIRST_ASSUM ((X_CHOOSE_TAC (← q r"g:num->A")) o (MATCH_MP NUMBER_FIELD_FREE_BASIS)) THEN ABBREV_TAC (← q r"n = extension_degree (subfield_generated k {ring_0 k:A},k) I") THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [free_basis]))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"g:num->A"), (← q r"ring_1 k INSERT IMAGE (\j. ring_mul k (x:A) ((g:num->A) j))
                                          {j | j < n}")] FREE_BASIS_PRIME_SUBFIELD_DENOMINATOR) THEN ASM_SIMP_TAC [FINITE_INSERT, FINITE_IMAGE, FINITE_NUMSEG_LT, INSERT_SUBSET, SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM, RING_1, RING_MUL, FORALL_IN_INSERT] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"D:int") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q r"a:num->int")) ((X_CHOOSE_TAC (← q r"b:num->num->int")) o (REWRITE_RULE [RIGHT_IMP_EXISTS_THM, SKOLEM_THM])))) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM] THEN ABBREV_TAC (← q r"e = ring_inv k (ring_of_int k D):A") THEN SUBGOAL_THEN (← q r"(e:A) IN ring_carrier k /\ ring_mul k e (ring_of_int k D) = ring_1 k") STRIP_ASSUME_TAC THENL [EXPAND_TAC "e" THEN ASM_SIMP_TAC [RING_INV, RING_OF_INT, FIELD_MUL_LINV, RING_OF_INT_EQ_0_CHAR_0], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"k:A ring"), (← q r"ring_of_int k:int->A"), (← q r"ring_mul k (ring_of_int k D) x:A"), (← q r"{i:num | i < n}"), (← q r"\i. ring_mul k e ((g:num->A) i)")] INTEGRAL_ELEMENT_FINITE_MODULE) THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, FINITE_NUMSEG_LT, RING_MUL, RING_OF_INT, IN_ELIM_THM, INTEGER_RING, IN_UNIV] THEN CONJ_TAC THENL [EXISTS_TAC (← q r"a:num->int") THEN TRANS_TAC EQ_TRANS (← q r"ring_mul k e (ring_mul k (ring_of_int k D) (ring_1 k)):A") THEN CONJ_TAC THENL [ASM_SIMP_TAC [RING_MUL_ASSOC, RING_OF_INT, RING_1, RING_MUL_LID], ASM_SIMP_TAC [RING_MUL_INT_LINCOMB, FINITE_NUMSEG_LT, IN_ELIM_THM]], X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN EXISTS_TAC (← q r"(b:num->num->int) j") THEN TRANS_TAC EQ_TRANS (← q r"ring_mul k e (ring_mul k (ring_of_int k D)
          (ring_mul k x ((g:num->A) j)))") THEN CONJ_TAC THENL [MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [RING_OF_INT], ASM_SIMP_TAC [RING_MUL_INT_LINCOMB, FINITE_NUMSEG_LT, IN_ELIM_THM]]])

  let RING_OF_INTEGERS_DENOMINATOR ← prove
    r"!k x:A.
        number_field k /\ x IN ring_carrier k
        ==> ?b. b IN ring_carrier(ring_of_integers k) /\ ~(b = ring_0 k) /\
                ring_mul k b x IN ring_carrier(ring_of_integers k)"
    (REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP NUMBER_FIELD_INTEGRAL_MULTIPLE)) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"d:int") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"ring_of_int k d:A") THEN ASM_REWRITE_TAC [RING_OF_INT_IN_RING_OF_INTEGERS] THEN ASM_MESON_TAC [number_field, RING_OF_INT_EQ_0_CHAR_0])

  let RING_OF_INTEGERS_COMMON_DENOMINATOR ← prove
    r"!k:A ring s (c:K->A).
        number_field k /\ FINITE s /\ (!i. i IN s ==> c i IN ring_carrier k)
        ==> ?d. d IN ring_carrier(ring_of_integers k) /\ ~(d = ring_0 k) /\
                !i. i IN s
                    ==> ring_mul k d (c i) IN ring_carrier(ring_of_integers k)"
    (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC [NOT_IN_EMPTY, FORALL_IN_INSERT] THEN CONJ_TAC THENL [REPEAT GEN_TAC THEN EXISTS_TAC (← q r"ring_1 k:A") THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_1) THEN ASM_SIMP_TAC [RING_OF_INTEGERS, FIELD_NONTRIVIAL], MAP_EVERY X_GEN_TAC [(← q r"x:K"), (← q r"s:K->bool")] THEN STRIP_TAC THEN X_GEN_TAC (← q r"c:K->A") THEN STRIP_TAC] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"c:K->A"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"d:A") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"(c:K->A) x")] RING_OF_INTEGERS_DENOMINATOR) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"b:A") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"ring_mul k d b:A") THEN MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") RING_MUL)) THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_SUBSET) THEN REWRITE_TAC [SUBSET] THEN REPEAT DISCH_TAC THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_MUL_EQ_0, FIELD_IMP_INTEGRAL_DOMAIN] THEN CONJ_TAC THENL [ASM_SIMP_TAC [(← GSYM RING_MUL_ASSOC)], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul k d b:A = ring_mul k b d") SUBST1_TAC THENL [MATCH_MP_TAC RING_MUL_SYM, ALL_TAC] THEN ASM_SIMP_TAC [(← GSYM RING_MUL_ASSOC)])

  let RING_OF_INTEGERS_IN_IDEAL_GENERATED_SING ← prove
    r"!k:A ring a x.
        field k /\ a IN ring_carrier(ring_of_integers k) /\
        ~(a = ring_0 k) /\ x IN ring_carrier k
        ==> (x IN ideal_generated (ring_of_integers k) {a} <=>
             ring_mul k (ring_inv k a) x IN ring_carrier(ring_of_integers k))"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [IN_IDEAL_GENERATED_SING_EQ, ring_divides, RING_OF_INTEGERS] THEN EQ_TAC THENL [DISCH_THEN ((X_CHOOSE_THEN (← q r"y:A") STRIP_ASSUME_TAC) o CONJUNCT2) THEN ASM_SIMP_TAC [RING_MUL_ASSOC, RING_INV, RING_MUL_LINV, FIELD_UNIT, RING_MUL_LID, (← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET)], DISCH_TAC] THEN SUBGOAL_THEN (← q r"x = ring_mul k a (ring_mul k (ring_inv k a) x:A)") MP_TAC THENL [ASM_SIMP_TAC [RING_MUL_ASSOC, RING_INV, RING_MUL_RINV, FIELD_UNIT, RING_MUL_LID], DISCH_THEN (fun th => tactic_of do pure (CONJ_TAC THENL [ONCE_REWRITE_TAC [th] THEN MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBRING], EXISTS_TAC (← q r"ring_mul k (ring_inv k a) x:A") THEN ASM_REWRITE_TAC [] THEN ACCEPT_TAC th]))])

  let RING_OF_INTEGERS_IDEAL_GENERATED_SING_EQ_0 ← prove
    r"!k (a:A).
        a IN ring_carrier(ring_of_integers k)
        ==> (ideal_generated (ring_of_integers k) {a} = {ring_0 k} <=>
             a = ring_0 k)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"a:A")] IDEAL_GENERATED_EQ_0) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS])

  let NUMBER_FIELD_INTEGRAL_FREE_BASIS ← prove
    r"!k:A ring.
        number_field k
        ==> ?g. free_basis (subfield_generated k {ring_0 k},k) I
                  (extension_degree (subfield_generated k {ring_0 k},k) I) g /\
                (!i. i < extension_degree (subfield_generated k {ring_0 k},k) I
                     ==> g i IN ring_carrier(ring_of_integers k))"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN FIRST_ASSUM ((X_CHOOSE_TAC (← q r"g:num->A")) o (MATCH_MP NUMBER_FIELD_FREE_BASIS)) THEN ABBREV_TAC (← q r"n = extension_degree (subfield_generated k {ring_0 k:A},k) I") THEN SUBGOAL_THEN (← q r"!i. i < n ==> ?d. ~(d = &0) /\
                      ring_mul k (ring_of_int k d) ((g:num->A) i) IN
                      ring_carrier(ring_of_integers k)") MP_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC NUMBER_FIELD_INTEGRAL_MULTIPLE THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (MATCH_MP_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [free_basis]))) THEN ASM_REWRITE_TAC [], DISCH_THEN ((X_CHOOSE_TAC (← q r"d:num->int")) o (REWRITE_RULE [RIGHT_IMP_EXISTS_THM, SKOLEM_THM]))] THEN EXISTS_TAC (← q r"\i. ring_mul k (ring_of_int k ((d:num->int) i)) ((g:num->A) i)") THEN ASM_SIMP_TAC [] THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"n:num"), (← q r"g:num->A"), (← q r"\i. ring_of_int k ((d:num->int) i):A")] FREE_BASIS_SCALE) THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, RING_OF_INT_IN_SUBFIELD_GENERATED, (← CONJUNCT1 (← CONJUNCT2 SUBFIELD_GENERATED)), RING_OF_INT_EQ_0_CHAR_0, I_THM] THEN ANTS_TAC THENL [ALL_TAC, REWRITE_TAC [ETA_AX]] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{ring_0 k:A}")] FIELD_EXTENSION_SUBFIELD_GENERATED) THEN ASM_SIMP_TAC [field_extension, ring_monomorphism])

  let NUMBER_FIELD_TRACE_ADD ← prove
    r"!k:A ring x y.
        number_field k /\ x IN ring_carrier k /\ y IN ring_carrier k
        ==> algebra_trace (subfield_generated k {ring_0 k},k) I
              (ring_add k x y) =
            ring_add k (algebra_trace (subfield_generated k {ring_0 k},k) I x)
                       (algebra_trace (subfield_generated k {ring_0 k},k) I y)"
    (SIMP_TAC [ALGEBRA_TRACE_ADD, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, (← CONJUNCT2 SUBFIELD_GENERATED)])

  let NUMBER_FIELD_NORM_MUL ← prove
    r"!k:A ring x y.
        number_field k /\ x IN ring_carrier k /\ y IN ring_carrier k
        ==> algebra_norm (subfield_generated k {ring_0 k},k) I
              (ring_mul k x y) =
            ring_mul k (algebra_norm (subfield_generated k {ring_0 k},k) I x)
                       (algebra_norm (subfield_generated k {ring_0 k},k) I y)"
    (SIMP_TAC [ALGEBRA_NORM_MUL, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, (← CONJUNCT2 SUBFIELD_GENERATED)])

  let NUMBER_FIELD_NORM_EQ_0 ← prove
    r"!k:A ring x.
        number_field k /\ x IN ring_carrier k
        ==> (algebra_norm (subfield_generated k {ring_0 k},k) I x =
             ring_0 k <=>
             x = ring_0 k)"
    (REWRITE_TAC [number_field] THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"x:A")] ALGEBRA_NORM_EQ_0) THEN ASM_REWRITE_TAC [(← CONJUNCT2 SUBFIELD_GENERATED)])

  let NUMBER_FIELD_NORM_RATIONAL ← prove
    r"!k:A ring a.
        number_field k /\ a IN ring_carrier(subfield_generated k {ring_0 k})
        ==> algebra_norm (subfield_generated k {ring_0 k},k) I a =
            ring_pow k a
              (extension_degree (subfield_generated k {ring_0 k},k) I)"
    (REWRITE_TAC [number_field] THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"a:A")] ALGEBRA_TRACE_NORM_BASE) THEN ASM_SIMP_TAC [FINITE_IMP_FIELD_EXTENSION, I_THM, RING_POW_SUBFIELD_GENERATED])

  let NUMBER_FIELD_NORM_SUB_MINIMAL_POLYNOMIAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"(m:num) = m * d <=> m * 1 = m * d")
    prove
      r"!(k:A ring) a c.
          number_field k /\ a IN ring_carrier k /\
          c IN ring_carrier(subfield_generated k {ring_0 k}) /\
          poly_deg (subfield_generated k {ring_0 k})
            (minimal_polynomial (subfield_generated k {ring_0 k},k) I a) =
          extension_degree (subfield_generated k {ring_0 k},k) I
          ==> algebra_norm (subfield_generated k {ring_0 k},k) I
                (ring_sub k c a) =
              poly_eval k
                (minimal_polynomial (subfield_generated k {ring_0 k},k) I a) c"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (MP_TAC o (MATCH_MP NUMBER_FIELD_DEGREE_POS)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [number_field])) THEN FIRST_ASSUM ((X_CHOOSE_TAC (← q r"g:num->A")) o (MATCH_MP NUMBER_FIELD_FREE_BASIS)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A")] NUMBER_FIELD_ALGEBRAIC) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{ring_0 k:A}")] FIELD_EXTENSION_SUBFIELD_GENERATED) THEN ASM_REWRITE_TAC [] THEN REPEAT DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"extension_degree (subfield_generated k {ring_0 k:A},k) I"), (← q r"g:num->A"), (← q r"c:A"), (← q r"a:A")] ALGEBRA_NORM_SUB_CHARPOLY) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION, I_THM] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"extension_degree (subfield_generated k {ring_0 k:A},k) I"), (← q r"g:num->A"), (← q r"a:A")] FIELD_CHARPOLY_MINIMAL_POLYNOMIAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"a:A")] SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"extension_degree
       (subfield_generated k
         (a INSERT IMAGE I (ring_carrier(subfield_generated k {ring_0 k}))),k)
       (I:A->A) = 1") SUBST1_TAC THENL [MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"subfield_generated k
          (a INSERT IMAGE I (ring_carrier(subfield_generated k {ring_0 k:A})))"), (← q r"k:A ring")] EXTENSION_DEGREE_TOWER_LAW) THEN ASM_SIMP_TAC [FINITE_IMP_FIELD_EXTENSION, FIELD_EXTENSION_SUBFIELD_GENERATED, I_O_ID] THEN REWRITE_TAC [r1, EQ_MULT_LCANCEL] THEN ASM_ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"a:A")] MINIMAL_POLYNOMIAL) THEN ASM_SIMP_TAC [POLY_POW_ALT, RING_POW_1, POLY_EVAL_SUBFIELD_GENERATED])

  let NUMBER_FIELD_TRACE_RATIONAL ← prove
    r"!k:A ring a.
        number_field k /\ a IN ring_carrier(subfield_generated k {ring_0 k})
        ==> algebra_trace (subfield_generated k {ring_0 k},k) I a =
            ring_mul k (ring_of_num k
              (extension_degree (subfield_generated k {ring_0 k},k) I)) a"
    (REWRITE_TAC [number_field] THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"a:A")] ALGEBRA_TRACE_NORM_BASE) THEN ASM_SIMP_TAC [FINITE_IMP_FIELD_EXTENSION, I_THM, RING_OF_NUM_SUBFIELD_GENERATED, (← CONJUNCT2 SUBFIELD_GENERATED)])

  let NUMBER_FIELD_TRACE_SCALAR_MUL ← prove
    r"!k:A ring a x.
        number_field k /\
        a IN ring_carrier(subfield_generated k {ring_0 k}) /\
        x IN ring_carrier k
        ==> algebra_trace (subfield_generated k {ring_0 k},k) I
              (ring_mul k a x) =
            ring_mul k a
              (algebra_trace (subfield_generated k {ring_0 k},k) I x)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"a:A"), (← q r"x:A")] ALGEBRA_TRACE_SCALAR) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION, I_THM, (← CONJUNCT2 SUBFIELD_GENERATED)])

  let NUMBER_FIELD_TRACE_MUL_LINCOMB ← prove
    r"!k:A ring (s:K->bool) c y x.
        number_field k /\ FINITE s /\
        (!i. i IN s ==> c i IN ring_carrier(subfield_generated k {ring_0 k})) /\
        (!i. i IN s ==> y i IN ring_carrier k) /\ x IN ring_carrier k
        ==> algebra_trace (subfield_generated k {ring_0 k},k) I
              (ring_mul k x (ring_sum k s (\i. ring_mul k (c i) (y i)))) =
            ring_sum k s
              (\i. ring_mul k (c i)
                     (algebra_trace (subfield_generated k {ring_0 k},k) I
                        (ring_mul k x (y i))))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"s:K->bool"), (← q r"c:K->A"), (← q r"y:K->A"), (← q r"x:A")] ALGEBRA_TRACE_MUL_LINCOMB) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION, (← CONJUNCT2 SUBFIELD_GENERATED), I_THM] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"I:A->A")] RING_HOMOMORPHISM_SUM) THEN REWRITE_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION, I_THM, I_O_ID] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_MUL_IN_SUBFIELD_GENERATED, ALGEBRA_TRACE_NORM_IN_CARRIER])

  let NUMBER_FIELD_TRACE_FORM_INJECTIVE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"(~p ==> F) ==> p")
    let r2 ← RING_RULE (← q r"ring_mul (r:A ring) a b =
        ring_add r (ring_mul r (ring_sub r b c) a) (ring_mul r a c)")
    prove
      r"!k:A ring n w x y.
          number_field k /\
          free_basis (subfield_generated k {ring_0 k},k) I n w /\
          x IN ring_carrier k /\ y IN ring_carrier k /\
          (!i. i < n
               ==> algebra_trace (subfield_generated k {ring_0 k},k) I
                     (ring_mul k (w i) x) =
                   algebra_trace (subfield_generated k {ring_0 k},k) I
                     (ring_mul k (w i) y))
          ==> x = y"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FREE_BASIS_IN_CARRIER)) THEN SUBGOAL_THEN (← q r"!x:A. x IN ring_carrier k
            ==> algebra_trace (subfield_generated k {ring_0 k},k) I x IN
                ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [ALGEBRA_TRACE_NORM_IN_CARRIER, RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"y:A")] RING_SUB_EQ_0) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ABBREV_TAC (← q r"z = ring_sub k x y:A") THEN SUBGOAL_THEN (← q r"(z:A) IN ring_carrier k") ASSUME_TAC THENL [EXPAND_TAC "z" THEN ASM_SIMP_TAC [RING_SUB], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. i < n
          ==> algebra_trace (subfield_generated k {ring_0 k},k) I
                (ring_mul k z ((w:num->A) i)) = ring_0 k") ASSUME_TAC THENL [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((← do let c := (← ASSUME (← q r"i:num < n")); pure (fun th => MATCH_MP th c)) o (checkM (fun z3 => (do let z4 ← (do let z5 ← (pure z3); pure (concl z5)); canM (fun z6 => (do let z7 ← (pure z6); find_termM (fun z8 => (do let z10 ← (pure z8); let z9 ← (q r"algebra_trace (subfield_generated k {ring_0 k},k)                                          (I:A->A)"); pure (z9 == z10))) z7)) z4))))) THEN SUBGOAL_THEN (← q r"(w:num->A) i IN ring_carrier k") ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul k (w i) x = ring_add k (ring_mul k z ((w:num->A) i))
                                        (ring_mul k (w i) y)") SUBST1_TAC THENL [EXPAND_TAC "z" THEN MATCH_MP_TAC r2 THEN ASM_REWRITE_TAC [], ASM_SIMP_TAC [NUMBER_FIELD_TRACE_ADD, RING_MUL, RING_ADD_EQ_RIGHT]], ALL_TAC] THEN MATCH_MP_TAC r1 THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"z:A")] TRACE_FORM_NONDEGENERATE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION, RING_OF_NUM_SUBFIELD_GENERATED, SUBFIELD_GENERATED] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP NUMBER_FIELD_DEGREE_POS)) THEN FIRST_ASSUM (MP_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN ASM_SIMP_TAC [RING_OF_NUM_EQ_0, DIVIDES_ZERO, (← GSYM (← MATCH_MP NUMBER_FIELD_FREE_BASIS_DEGREE (← CONJ (← ASSUME (← q r"number_field (k:A ring)")) (← ASSUME (← q r"free_basis (subfield_generated k {ring_0 k},k) I n
                     (w:num->A)")))))] THEN ARITH_TAC, REWRITE_TAC [NOT_EXISTS_THM]] THEN X_GEN_TAC (← q r"u:A") THEN ASM_CASES_TAC (← q r"(u:A) IN ring_carrier k") THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (MP_TAC o ((SPEC (← q r"u:A")) o (CONJUNCT1 o (CONJUNCT2 o (GEN_REWRITE_RULE id [free_basis]))))) THEN ASM_REWRITE_TAC [I_THM, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"c:num->A") THEN STRIP_TAC THEN ASM_SIMP_TAC [RING_MUL, SUBFIELD_GENERATED] THEN ASM_SIMP_TAC [NUMBER_FIELD_TRACE_MUL_LINCOMB, FINITE_NUMSEG_LT, IN_ELIM_THM, RING_MUL_RZERO] THEN MATCH_MP_TAC RING_SUM_EQ_0 THEN ASM_SIMP_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL_RZERO THEN ASM_MESON_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBSET])

  let RING_OF_INTEGERS_INTEGER_MATRIX ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul (r:A ring) p (ring_mul r x y) =
        ring_mul r (ring_mul r x p) y")
    let r2 ← RING_RULE (← q r"ring_add r (p:A) s = ring_0 r ==> p = ring_neg r s")
    prove
      r"!k:A ring x.
          number_field k /\ x IN ring_carrier(ring_of_integers k)
          ==> ?n w. free_basis (subfield_generated k {ring_0 k},k) I n w /\
                    !j. j < n
                        ==> ?c. (!i. i < n
                                     ==> c i IN
                                         {ring_of_int k m | m IN (:int)}) /\
                                ring_mul k x (w j) =
                                ring_sum k {i | i < n}
                                  (\i. ring_mul k (c i) (w i))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN UNDISCH_TAC (← q r"(x:A) IN ring_carrier(ring_of_integers k)") THEN REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM] THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"k:A ring"), (← q r"ring_of_int k:int->A"), (← q r"x:A")] INTEGRAL_ELEMENT_EXPLICIT) THEN REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, INTEGER_RING, IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"m:num"), (← q r"c:num->int")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!i. i < m
          ==> ?b. ring_pow k (x:A) (SUC i) =
                  ring_sum k {l | l < m}
                    (\l. ring_mul k (ring_of_int k (b l)) (ring_pow k x l))") (LABEL_TAC "pow") THENL [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"SUC i < m") THENL [EXISTS_TAC (← q r"\l:num. if l = SUC i then &1:int else &0") THEN REWRITE_TAC [COND_RAND, COND_RATOR, RING_OF_INT_1, RING_OF_INT_0] THEN ASM_SIMP_TAC [RING_MUL_LID, RING_MUL_LZERO, RING_POW, RING_SUM_DELTA, IN_ELIM_THM], SUBGOAL_THEN (← q r"SUC i = m") SUBST1_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN EXISTS_TAC (← q r"\l. --((c:num->int) l)") THEN REWRITE_TAC [RING_OF_INT_NEG] THEN ASM_SIMP_TAC [RING_MUL_LNEG, RING_OF_INT, RING_POW, RING_SUM_NEG, FINITE_NUMSEG_LT, RING_MUL, IN_ELIM_THM] THEN MATCH_MP_TAC (← REWRITE_RULE [IMP_IMP] r2) THEN ASM_SIMP_TAC [RING_POW, RING_SUM]], ALL_TAC] THEN FIRST_ASSUM ((X_CHOOSE_TAC (← q r"g:num->A")) o (MATCH_MP NUMBER_FIELD_FREE_BASIS)) THEN ABBREV_TAC (← q r"n = extension_degree (subfield_generated k {ring_0 k:A},k) I") THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [free_basis]))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{i:num | i < n}"), (← q r"g:num->A")] RING_INT_LINCOMB) THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN DISCH_THEN (ASSUME_TAC o (CONJUNCT1 o CONJUNCT2)) THEN ABBREV_TAC (← q r"N = {y:A | ?c. y = ring_sum k {j | j < n}
                           (\j. ring_mul k (ring_of_int k (c j))
                                           ((g:num->A) j))}") THEN SUBGOAL_THEN (← q r"!(s:num->bool) (y:num->A) b.
          FINITE s /\ (!i. i IN s ==> y i IN N)
          ==> ring_sum k s (\i. ring_mul k (ring_of_int k (b i)) (y i)) IN N") (LABEL_TAC "Ncomb") THENL [EXPAND_TAC "N" THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_INT_LINCOMB_LINCOMB THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"g:num->A"), (← q r"IMAGE (\(i,j). ring_mul k (ring_pow k x i) ((g:num->A) j))
             ({i:num | i < m} CROSS {j:num | j < n})")] FREE_BASIS_PRIME_SUBFIELD_DENOMINATOR) THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_IMAGE, FINITE_CROSS, FINITE_NUMSEG_LT, SUBSET, FORALL_IN_IMAGE, FORALL_PAIR_THM, IN_CROSS, IN_ELIM_THM, RING_MUL, RING_POW], REWRITE_TAC [FORALL_IN_IMAGE, FORALL_PAIR_THM, IN_CROSS, IN_ELIM_THM]] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"D:int") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D"))) THEN ABBREV_TAC (← q r"t = {y:A | y IN ring_carrier k /\
                 !i. i < m
                     ==> ring_mul k (ring_of_int k D)
                           (ring_mul k (ring_pow k x i) y)
                         IN N}") THEN SUBGOAL_THEN (← q r"(!y. y IN N ==> y IN ring_carrier k) /\
      (!y y'. y IN N /\ y' IN N ==> ring_sub k y y' IN (N:A->bool))") STRIP_ASSUME_TAC THENL [EXPAND_TAC "N" THEN REWRITE_TAC [IN_ELIM_THM] THEN CONJ_TAC THENL [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [RING_SUM], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"y:A"), (← q r"y':A")] THEN DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"a:num->int") SUBST1_TAC) (X_CHOOSE_THEN (← q r"b:num->int") SUBST1_TAC)) THEN EXISTS_TAC (← q r"\j. (a:num->int) j - b j") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!c. ring_sum k {j | j < n}
            (\j. ring_mul k (ring_of_int k (c j)) ((g:num->A) j)) IN t") ASSUME_TAC THENL [X_GEN_TAC (← q r"a:num->int") THEN EXPAND_TAC "t" THEN REWRITE_TAC [IN_ELIM_THM, RING_SUM] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN ASM_SIMP_TAC [RING_MUL_INT_LINCOMB, FINITE_NUMSEG_LT, IN_ELIM_THM, RING_MUL, RING_OF_INT, RING_POW] THEN USE_THEN "Ncomb" MATCH_MP_TAC THEN REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN EXPAND_TAC "N" THEN REWRITE_TAC [IN_ELIM_THM] THEN USE_THEN "D" MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!y. y IN t ==> ring_mul k x y IN (t:A->bool)") ASSUME_TAC THENL [EXPAND_TAC "t" THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"y:A") THEN STRIP_TAC THEN ASM_SIMP_TAC [RING_MUL] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN USE_THEN "pow" ((X_CHOOSE_TAC (← q r"b:num->int")) o (← do let c := (← ASSUME (← q r"i:num < m")); pure (fun th => MATCH_MP th c))) THEN SUBGOAL_THEN (← q r"ring_mul k (ring_pow k x i) (ring_mul k x y) =
        ring_mul k (ring_pow k x (SUC i)) (y:A)") SUBST1_TAC THENL [REWRITE_TAC [ring_pow] THEN MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [RING_POW], ASM_SIMP_TAC [RING_MUL_INT_LINCOMB, FINITE_NUMSEG_LT, IN_ELIM_THM, RING_MUL, RING_OF_INT, RING_POW]] THEN USE_THEN "Ncomb" MATCH_MP_TAC THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"g:num->A"), (← q r"t:A->bool"), (← q r"D:int")] NUMBER_FIELD_INT_LINCOMB_SANDWICH) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN EXPAND_TAC "t" THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL [SIMP_TAC [], MAP_EVERY X_GEN_TAC [(← q r"y:A"), (← q r"z:A")] THEN STRIP_TAC THEN ASM_SIMP_TAC [RING_SUB, RING_SUB_LDISTRIB, RING_MUL, RING_POW, RING_OF_INT], X_GEN_TAC (← q r"y:A") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"0"))) THEN ASM_SIMP_TAC [ring_pow, RING_MUL_LID] THEN EXPAND_TAC "N" THEN REWRITE_TAC [IN_ELIM_THM]], DISCH_THEN (X_CHOOSE_THEN (← q r"w:num->A") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "wt") (LABEL_TAC "tw"))))] THEN MAP_EVERY EXISTS_TAC [(← q r"n:num"), (← q r"w:num->A")] THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN USE_THEN "tw" (MP_TAC o (SPEC (← q r"ring_mul k x ((w:num->A) j)"))) THEN ANTS_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN USE_THEN "wt" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC, DISCH_THEN (X_CHOOSE_THEN (← q r"z:num->int") SUBST1_TAC)] THEN EXISTS_TAC (← q r"\i. ring_of_int k ((z:num->int) i):A") THEN REWRITE_TAC [IN_ELIM_THM, IN_UNIV] THEN MESON_TAC [])

  let NUMBER_FIELD_TRACE_INTEGRAL_Q ← prove
    r"!k:A ring x.
        number_field k /\ x IN ring_carrier(ring_of_integers k)
        ==> ?m. algebra_trace (subfield_generated k {ring_0 k},k) I x =
                ring_of_int k m"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A")] RING_OF_INTEGERS_INTEGER_MATRIX) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"n:num"), (← q r"w:num->A")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"{ring_of_int k m:A | m IN (:int)}"), (← q r"x:A")] ALGEBRA_TRACE_SUBRING) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION, NUMBER_FIELD_IMP_FIELD, I_THM] THEN MP_TAC (← ISPEC (← q r"subfield_generated k {ring_0 k:A}") PRIME_SUBRING) THEN REWRITE_TAC [RING_OF_INT_SUBFIELD_GENERATED], REWRITE_TAC [IN_ELIM_THM, IN_UNIV] THEN MESON_TAC []])

  let NUMBER_FIELD_TRACE_IN_RING_OF_INTEGERS ← prove
    r"!k:A ring x.
        number_field k /\ x IN ring_carrier k
        ==> (algebra_trace (subfield_generated k {ring_0 k},k) I x IN
             ring_carrier(ring_of_integers k) <=>
             ?m. algebra_trace (subfield_generated k {ring_0 k},k) I x =
                 ring_of_int k m)"
    (REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [RING_OF_INT_IN_RING_OF_INTEGERS] THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_PRIME_SUBFIELD) THEN MP_TAC (← CONJUNCT1 (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"x:A")] ALGEBRA_TRACE_NORM_IN_CARRIER)) THEN FIRST_ASSUM (MP_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN ASM_SIMP_TAC [NUMBER_FIELD_IMP_FIELD] THEN ASM SET_TAC [])

  -- @@RETURN BEGIN
  return { RING_OF_INTEGERS_ROOT_OF_UNITY_UNIT, INTEGRAL_DOMAIN_RING_OF_INTEGERS,
           RING_OF_INTEGERS_UNIT_NONZERO, RING_OF_INTEGERS_PRIME_SUBFIELD,
           RING_OF_INTEGERS_ALGEBRAIC, RING_OF_INTEGERS_RING_OF_INT_MUL,
           RING_HOMOMORPHISM_RING_OF_INTEGERS, RING_MONOMORPHISM_RING_OF_INTEGERS,
           RING_ISOMORPHISM_RING_OF_INTEGERS, ISOMORPHIC_RING_RING_OF_INTEGERS,
           NUMBER_FIELD_INTEGRAL_MULTIPLE, RING_OF_INTEGERS_DENOMINATOR,
           RING_OF_INTEGERS_COMMON_DENOMINATOR, RING_OF_INTEGERS_IN_IDEAL_GENERATED_SING,
           RING_OF_INTEGERS_IDEAL_GENERATED_SING_EQ_0, NUMBER_FIELD_INTEGRAL_FREE_BASIS,
           NUMBER_FIELD_TRACE_ADD, NUMBER_FIELD_NORM_MUL, NUMBER_FIELD_NORM_EQ_0,
           NUMBER_FIELD_NORM_RATIONAL, NUMBER_FIELD_NORM_SUB_MINIMAL_POLYNOMIAL,
           NUMBER_FIELD_TRACE_RATIONAL, NUMBER_FIELD_TRACE_SCALAR_MUL,
           NUMBER_FIELD_TRACE_MUL_LINCOMB, NUMBER_FIELD_TRACE_FORM_INJECTIVE,
           RING_OF_INTEGERS_INTEGER_MATRIX, NUMBER_FIELD_TRACE_INTEGRAL_Q,
           NUMBER_FIELD_TRACE_IN_RING_OF_INTEGERS }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- numfield.ml phrases from line 1582 to 1582                             -/
/- ---------------------------------------------------------------------- -/

structure Numfield03 where
  -- @@FIELDS
  NUMBER_FIELD_NORM_INTEGRAL_Q : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupNumfield03 [HolBase] (D : NumfieldDeps) (BNumfield01 : Numfield01) (BNumfield02 : Numfield02) :
    ExceptT String IO Numfield03 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, .. } := D
  let { ALGEBRA_NORM_SUBRING, IN_ELIM_THM, IN_UNIV, I_THM, LEFT_IMP_EXISTS_THM, .. } := D.core1
  let { PRIME_SUBRING, RING_HOMOMORPHISM_SUBFIELD_INCLUSION,
        RING_OF_INT_SUBFIELD_GENERATED, SUBSET, .. } := D.core2
  let { NUMBER_FIELD_IMP_FIELD, RING_OF_INTEGERS_SUBSET, .. } := BNumfield01
  let { RING_OF_INTEGERS_INTEGER_MATRIX, .. } := BNumfield02
  -- @@SCOPE END

  let NUMBER_FIELD_NORM_INTEGRAL_Q ← prove
    r"!k:A ring x.
        number_field k /\ x IN ring_carrier(ring_of_integers k)
        ==> ?m. algebra_norm (subfield_generated k {ring_0 k},k) I x =
                ring_of_int k m"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A")] RING_OF_INTEGERS_INTEGER_MATRIX) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"n:num"), (← q r"w:num->A")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"{ring_of_int k m:A | m IN (:int)}"), (← q r"x:A")] ALGEBRA_NORM_SUBRING) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION, NUMBER_FIELD_IMP_FIELD, I_THM] THEN MP_TAC (← ISPEC (← q r"subfield_generated k {ring_0 k:A}") PRIME_SUBRING) THEN REWRITE_TAC [RING_OF_INT_SUBFIELD_GENERATED], REWRITE_TAC [IN_ELIM_THM, IN_UNIV] THEN MESON_TAC []])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_NORM_INTEGRAL_Q }
  -- @@RETURN END

end HolANT.Numfield
