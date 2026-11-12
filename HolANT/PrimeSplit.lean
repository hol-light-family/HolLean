/- ========================================================================= -/
/- ANT: Ramification index and residue degree of a prime over its ...      -/
/- ========================================================================= -/
/- File: HolANT/PrimeSplit.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/prime_split.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antprimesplitdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/products.ml, ANT/ideal_arith.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ring_of_integers.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.PrimeSplit fills them).

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
import HolANT.IdealArith
import HolANT.Algmisc
import HolANT.Integral
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.IdealNorm
import HolLibrary.Isum
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
open HolANT.IdealArith
open HolANT.Algmisc
open HolANT.Integral
open HolANT.Dedekind
open HolANT.DedekindStruct
open HolANT.IdealNorm
open HolANT.Zlattice
open HolANT.Numfield
open HolANT.RingOfIntegers

namespace HolANT.PrimeSplit

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (CARD_EQ_NSUM CARD_EXTENSION_DEGREE CARD_PRIME_SUBRING CONTRAPOS_THM
   DEDEKIND_IDEAL_FACTORIZATION DEDEKIND_IDEAL_PRODUCT_PRIME_POW_UNIQUE
   DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL DEDEKIND_RING_OF_INTEGERS DIVIDES_ZERO
   EQ_EXP EQ_TRANS ETA_AX EXISTS_UNIQUE EXISTS_UNIQUE_THM EXP EXP_ADD EXP_EXP
   EXP_NSUM EXTENSION FIELD_EXTENSION_SUBFIELD_GENERATED FINITE_IMAGE
   FINITE_INDUCT_STRONG FINITE_INTEGRAL_DOMAIN_CHAR
   FINITE_INTEGRAL_DOMAIN_IMP_FIELD FORALL_IN_IMAGE IDEAL_GENERATED_INC_GEN
   IDEAL_GENERATED_MINIMAL IDEAL_GENERATED_MINIMAL_EQ IDEAL_GENERATED_MONO
   IDEAL_NORM_FACTORIZATION IDEAL_NORM_GT_1 IDEAL_NORM_IDEAL_POW
   IDEAL_NORM_IDEAL_PRODUCT IDEAL_NORM_SUBSET_EQ IDEAL_POW_EQ_ZERO
   IDEAL_PRODUCT_EQ IDEAL_PRODUCT_IMAGE IDEAL_PROD_SUBSET_LEFT
   IDEAL_PROD_SUBSET_RIGHT IDEAL_VALUATION_EQ_0 INTEGER_RING
   INTEGRAL_DOMAIN_CHAR INTEGRAL_DOMAIN_QUOTIENT_RING
   INTEGRAL_DOMAIN_RING_OF_INTEGERS INT_ABS_NUM INT_OF_NUM_EQ IN_ELIM_THM
   IN_IDEAL_GENERATED_SELF IN_IDEAL_GENERATED_SING IN_IMAGE IN_SING IN_UNIV
   ITERATE_EQ LE_REFL LT_REFL MONOIDAL_MUL MULT_EQ_0 MULT_SYM NOT_EXISTS_THM
   NPRODUCT_CLAUSES NPRODUCT_EQ NSUM_CLAUSES NSUM_LE NSUM_POS_BOUND
   NUMBER_FIELD_DEGREE_POS NUMBER_FIELD_IMP_FIELD NUM_OF_INT_OF_NUM PAIR_EQ
   PRIME_EXP PRIME_GE_2 PRIME_IDEAL_IMP_PSUBSET PRIME_IMP_NZ
   PRIME_IMP_RING_IDEAL PRIME_SUBFIELD_EQ_SUBRING QUOTIENT_RING_0
   RING_CHAR_DIVIDES_PRIME RING_COSET_EQ_IDEAL RING_HOMOMORPHISM_RING_COSET
   RING_HOMOMORPHISM_RING_OF_INT RING_HOMOMORPHISM_RING_OF_NUM
   RING_IDEAL_IDEAL_GENERATED RING_IDEAL_IDEAL_POW RING_IDEAL_IDEAL_PRODUCT
   RING_IDEAL_IMP_SUBSET RING_MUL RING_OF_INT RING_OF_INTEGERS
   RING_OF_INTEGERS_FINITE_QUOTIENT RING_OF_INTEGERS_IDEAL_NORM_INTEGER
   RING_OF_INT_EQ_0 RING_OF_INT_IN_RING_OF_INTEGERS RING_OF_INT_MUL
   RING_OF_INT_OF_NUM RING_OF_NUM RING_OF_NUM_EQ_0 SELECT_UNIQUE SIMPLE_IMAGE
   SING_SUBSET SUBRING_GENERATED_BY_SUBFIELD_GENERATED SUBSET SUBSET_ANTISYM
   ideal_norm int_divides maximal_ideal nproduct number_field o_DEF o_THM
   prime_ideal proper_ideal ring_divides : thm)
  deriving Inhabited

/-- What prime_split.ml uses from Session besides theorems. -/
structure PrimeSplitDeps where
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
/- prime_split.ml phrases from line 59 to 646                             -/
/- ---------------------------------------------------------------------- -/

structure PrimeSplit where
  -- @@FIELDS
  ramification_index : thm
  residue_degree : thm
  RAMIFICATION_INDEX_INTEGER_RING : thm
  RESIDUE_DEGREE_INTEGER_RING : thm
  RING_OF_NUM_IN_PRIME_IDEAL : thm
  RING_OF_INT_IN_PRIME_IDEAL : thm
  RAMIFICATION_INDEX_PRIME : thm
  IDEAL_NORM_RESIDUE_DEGREE_Q : thm
  RING_OF_INTEGERS_PRIME_IDEAL_ABOVE : thm
  RING_OF_INTEGERS_RESIDUE_FIELD : thm
  RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q : thm
  NUMBER_FIELD_PRIME_IDEAL_DEGREE_ONE : thm
  RING_OF_INTEGERS_IDEAL_GENERATED_PRIME : thm
  NUMBER_FIELD_PRIME_FACTORIZATION_Q : thm
  NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE_Q : thm
  NUMBER_FIELD_FUNDAMENTAL_IDENTITY_Q : thm
  NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q : thm
  NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q : thm
  NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE_IMAGE : thm
  NUMBER_FIELD_IDEAL_NORM_PRIME_PRODUCT : thm
  NUMBER_FIELD_PRIME_FACTORIZATION_SUBSET_EQ : thm
  NUMBER_FIELD_PRIME_IDEAL_PROD_EQ : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupPrimeSplit [HolBase] (D : PrimeSplitDeps) :
    ExceptT String IO PrimeSplit := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INTEGER_RULE, MESON_TAC,
        SET_RULE, SET_TAC, TAUT, new_definition, .. } := D
  let { CARD_EQ_NSUM, CARD_EXTENSION_DEGREE, CARD_PRIME_SUBRING, CONTRAPOS_THM,
        DEDEKIND_IDEAL_FACTORIZATION, DEDEKIND_IDEAL_PRODUCT_PRIME_POW_UNIQUE,
        DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL, DEDEKIND_RING_OF_INTEGERS, DIVIDES_ZERO,
        EQ_EXP, EQ_TRANS, ETA_AX, EXISTS_UNIQUE, EXISTS_UNIQUE_THM, EXP, EXP_ADD,
        EXP_EXP, EXP_NSUM, EXTENSION, FIELD_EXTENSION_SUBFIELD_GENERATED, FINITE_IMAGE,
        FINITE_INDUCT_STRONG, FINITE_INTEGRAL_DOMAIN_CHAR,
        FINITE_INTEGRAL_DOMAIN_IMP_FIELD, FORALL_IN_IMAGE, IDEAL_GENERATED_INC_GEN,
        IDEAL_GENERATED_MINIMAL, IDEAL_GENERATED_MINIMAL_EQ, IDEAL_GENERATED_MONO,
        IDEAL_NORM_FACTORIZATION, IDEAL_NORM_GT_1, IDEAL_NORM_IDEAL_POW,
        IDEAL_NORM_IDEAL_PRODUCT, IDEAL_NORM_SUBSET_EQ, IDEAL_POW_EQ_ZERO,
        IDEAL_PRODUCT_EQ, IDEAL_PRODUCT_IMAGE, IDEAL_PROD_SUBSET_LEFT,
        IDEAL_PROD_SUBSET_RIGHT, IDEAL_VALUATION_EQ_0, INTEGER_RING,
        INTEGRAL_DOMAIN_CHAR, INTEGRAL_DOMAIN_QUOTIENT_RING,
        INTEGRAL_DOMAIN_RING_OF_INTEGERS, INT_ABS_NUM, INT_OF_NUM_EQ, IN_ELIM_THM,
        IN_IDEAL_GENERATED_SELF, IN_IDEAL_GENERATED_SING, IN_IMAGE, IN_SING, IN_UNIV,
        ITERATE_EQ, LE_REFL, LT_REFL, MONOIDAL_MUL, MULT_EQ_0, MULT_SYM,
        NOT_EXISTS_THM, NPRODUCT_CLAUSES, NPRODUCT_EQ, NSUM_CLAUSES, NSUM_LE,
        NSUM_POS_BOUND, NUMBER_FIELD_DEGREE_POS, NUMBER_FIELD_IMP_FIELD,
        NUM_OF_INT_OF_NUM, PAIR_EQ, PRIME_EXP, PRIME_GE_2, PRIME_IDEAL_IMP_PSUBSET,
        PRIME_IMP_NZ, PRIME_IMP_RING_IDEAL, PRIME_SUBFIELD_EQ_SUBRING, QUOTIENT_RING_0,
        RING_CHAR_DIVIDES_PRIME, RING_COSET_EQ_IDEAL, RING_HOMOMORPHISM_RING_COSET,
        RING_HOMOMORPHISM_RING_OF_INT, RING_HOMOMORPHISM_RING_OF_NUM,
        RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_POW, RING_IDEAL_IDEAL_PRODUCT,
        RING_IDEAL_IMP_SUBSET, RING_MUL, RING_OF_INT, RING_OF_INTEGERS,
        RING_OF_INTEGERS_FINITE_QUOTIENT, RING_OF_INTEGERS_IDEAL_NORM_INTEGER,
        RING_OF_INT_EQ_0, RING_OF_INT_IN_RING_OF_INTEGERS, RING_OF_INT_MUL,
        RING_OF_INT_OF_NUM, RING_OF_NUM, RING_OF_NUM_EQ_0, SELECT_UNIQUE, SIMPLE_IMAGE,
        SING_SUBSET, SUBRING_GENERATED_BY_SUBFIELD_GENERATED, SUBSET, SUBSET_ANTISYM,
        ideal_norm, int_divides, maximal_ideal, nproduct, number_field, o_DEF, o_THM,
        prime_ideal, proper_ideal, ring_divides, .. } := D.core1
  -- @@SCOPE END

  let ramification_index ← new_definition
    r"ramification_index (r:A ring,s:B ring) (h:A->B) (P:B->bool) =
  ideal_valuation s P
   (ideal_generated s (IMAGE h {x | x IN ring_carrier r /\ h x IN P}))"

  let residue_degree ← new_definition
    r"residue_degree (r:A ring,s:B ring) (h:A->B) (P:B->bool) =
  extension_degree
   (subring_generated (quotient_ring s P)
                      (IMAGE (ring_coset s P o h) (ring_carrier r)),
    quotient_ring s P) I"

  let RAMIFICATION_INDEX_INTEGER_RING ← prove
    r"!r:A ring P.
        ring_ideal r P
        ==> ramification_index (integer_ring,r) (ring_of_int r) P =
            ideal_valuation r P
             (ideal_generated r
                {ring_of_num r (ring_char(quotient_ring r P))})"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [ramification_index] THEN AP_TERM_TAC THEN ABBREV_TAC (← q r"c = ring_char(quotient_ring r (P:A->bool))") THEN SUBGOAL_THEN (← q r"!x. ring_of_int r x IN (P:A->bool) <=> &c divides x") ASSUME_TAC THENL [X_GEN_TAC (← q r"x:int") THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"quotient_ring r (P:A->bool)"), (← q r"ring_coset r (P:A->bool)")] RING_HOMOMORPHISM_RING_OF_INT) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_COSET] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"x:int"))) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"ring_of_int r x:A")] RING_COSET_EQ_IDEAL) THEN ASM_REWRITE_TAC [RING_OF_INT] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool")] QUOTIENT_RING_0) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [(← SYM th)])) THEN EXPAND_TAC "c" THEN REWRITE_TAC [RING_OF_INT_EQ_0], ALL_TAC] THEN ASM_REWRITE_TAC [INTEGER_RING, IN_UNIV] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM, int_divides] THEN X_GEN_TAC (← q r"x:int") THEN DISCH_THEN (X_CHOOSE_THEN (← q r"t:int") SUBST1_TAC) THEN REWRITE_TAC [RING_OF_INT_MUL, RING_OF_INT_OF_NUM] THEN MATCH_MP_TAC IN_IDEAL_GENERATED_SING THEN REWRITE_TAC [ring_divides] THEN SIMP_TAC [RING_MUL, RING_OF_NUM, RING_OF_INT] THEN MESON_TAC [RING_OF_INT], MATCH_MP_TAC IDEAL_GENERATED_MONO THEN REWRITE_TAC [SING_SUBSET, IN_IMAGE, IN_ELIM_THM] THEN EXISTS_TAC (← q r"&c:int") THEN REWRITE_TAC [RING_OF_INT_OF_NUM] THEN CONV_TAC INTEGER_RULE])

  let RESIDUE_DEGREE_INTEGER_RING ← prove
    r"!r:A ring P.
        prime_ideal r P /\ ~(ring_char(quotient_ring r P) = 0)
        ==> residue_degree (integer_ring,r) (ring_of_int r) P =
            extension_degree
             (subfield_generated (quotient_ring r P)
                {ring_0(quotient_ring r P)},
              quotient_ring r P) I"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [residue_degree] THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [PAIR_EQ] THEN GEN_REWRITE_TAC RAND_CONV [(← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED)] THEN AP_TERM_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"prime(ring_char(quotient_ring r (P:A->bool)))") ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"quotient_ring r (P:A->bool)") INTEGRAL_DOMAIN_CHAR) THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_QUOTIENT_RING], ALL_TAC] THEN ASM_SIMP_TAC [PRIME_SUBFIELD_EQ_SUBRING] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"quotient_ring r (P:A->bool)"), (← q r"ring_coset r (P:A->bool)")] RING_HOMOMORPHISM_RING_OF_INT) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_COSET] THEN DISCH_TAC THEN ASM_REWRITE_TAC [INTEGER_RING, o_DEF, SIMPLE_IMAGE, ETA_AX])

  let RING_OF_NUM_IN_PRIME_IDEAL ← prove
    r"!r:A ring P p.
        prime_ideal r P /\ prime p
        ==> (ring_of_num r p IN P <=> ring_char(quotient_ring r P) = p)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN MP_TAC (← ISPECL [(← q r"quotient_ring r (P:A->bool)"), (← q r"p:num")] RING_CHAR_DIVIDES_PRIME) THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_QUOTIENT_RING] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [(← GSYM RING_OF_NUM_EQ_0)] THEN FIRST_ASSUM (SUBST1_TAC o (SYM o ((SPEC (← q r"p:num")) o ((MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM) o (MATCH_MP RING_HOMOMORPHISM_RING_COSET))))) THEN ASM_SIMP_TAC [QUOTIENT_RING_0, RING_COSET_EQ_IDEAL, RING_OF_NUM])

  let RING_OF_INT_IN_PRIME_IDEAL ← prove
    r"!r:A ring P p.
        prime_ideal r P /\ prime p /\ ring_of_num r p IN P
        ==> !m. ring_of_int r m IN P <=> &p divides m"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"ring_char(quotient_ring r (P:A->bool)) = p") (SUBST1_TAC o SYM) THENL [ASM_MESON_TAC [RING_OF_NUM_IN_PRIME_IDEAL], ALL_TAC] THEN REWRITE_TAC [(← GSYM RING_OF_INT_EQ_0)] THEN FIRST_ASSUM (SUBST1_TAC o (SYM o ((SPEC (← q r"m:int")) o ((MATCH_MP RING_HOMOMORPHISM_RING_OF_INT) o (MATCH_MP RING_HOMOMORPHISM_RING_COSET))))) THEN ASM_SIMP_TAC [QUOTIENT_RING_0, RING_COSET_EQ_IDEAL, RING_OF_INT])

  let RAMIFICATION_INDEX_PRIME ← prove
    r"!r:A ring P p.
        prime_ideal r P /\ prime p /\ ring_of_num r p IN P
        ==> ramification_index (integer_ring,r) (ring_of_int r) P =
            ideal_valuation r P (ideal_generated r {ring_of_num r p})"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_char(quotient_ring r (P:A->bool)) = p") MP_TAC THENL [ASM_MESON_TAC [RING_OF_NUM_IN_PRIME_IDEAL], ASM_SIMP_TAC [RAMIFICATION_INDEX_INTEGER_RING, PRIME_IMP_RING_IDEAL]])

  let IDEAL_NORM_RESIDUE_DEGREE_Q ← prove
    r"!r:A ring P.
        prime_ideal r P /\ FINITE(ring_carrier(quotient_ring r P))
        ==> ideal_norm r P =
            ring_char(quotient_ring r P) EXP
            residue_degree (integer_ring,r) (ring_of_int r) P"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"integral_domain(quotient_ring r (P:A->bool))") ASSUME_TAC THENL [ASM_SIMP_TAC [INTEGRAL_DOMAIN_QUOTIENT_RING, PRIME_IMP_RING_IDEAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(ring_char(quotient_ring r (P:A->bool)) = 0)") ASSUME_TAC THENL [ASM_MESON_TAC [FINITE_INTEGRAL_DOMAIN_CHAR, PRIME_IMP_NZ], ALL_TAC] THEN ASM_SIMP_TAC [RESIDUE_DEGREE_INTEGER_RING, ideal_norm] THEN ABBREV_TAC (← q r"R = quotient_ring r (P:A->bool)") THEN MP_TAC (← ISPECL [(← q r"I:(A->bool)->(A->bool)"), (← q r"subfield_generated R {ring_0 R:A->bool}"), (← q r"R:(A->bool)ring")] CARD_EXTENSION_DEGREE) THEN ASM_SIMP_TAC [FIELD_EXTENSION_SUBFIELD_GENERATED, PRIME_SUBFIELD_EQ_SUBRING, CARD_PRIME_SUBRING, PRIME_IMP_NZ, FINITE_INTEGRAL_DOMAIN_CHAR, FINITE_INTEGRAL_DOMAIN_IMP_FIELD])

  let RING_OF_INTEGERS_PRIME_IDEAL_ABOVE ← prove
    r"!k:A ring P.
        number_field k /\ prime_ideal (ring_of_integers k) P /\
        ~(P = {ring_0 k})
        ==> ?!p. prime p /\ ring_of_num k p IN P"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"prime(ring_char(quotient_ring (ring_of_integers k) (P:A->bool)))") ASSUME_TAC THENL [MATCH_MP_TAC FINITE_INTEGRAL_DOMAIN_CHAR THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_QUOTIENT_RING, RING_OF_INTEGERS_FINITE_QUOTIENT], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool")] RING_OF_NUM_IN_PRIME_IDEAL) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_TAC THEN ASM_REWRITE_TAC [EXISTS_UNIQUE_THM] THEN ASM_MESON_TAC [])

  let RING_OF_INTEGERS_RESIDUE_FIELD ← prove
    r"!k:A ring P.
        number_field k /\ prime_ideal (ring_of_integers k) P /\
        ~(P = {ring_0 k})
        ==> field(quotient_ring (ring_of_integers k) P) /\
            FINITE(ring_carrier(quotient_ring (ring_of_integers k) P))"
    (MESON_TAC [RING_OF_INTEGERS_FINITE_QUOTIENT, PRIME_IMP_RING_IDEAL, INTEGRAL_DOMAIN_QUOTIENT_RING, FINITE_INTEGRAL_DOMAIN_IMP_FIELD])

  let RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q ← prove
    r"!k:A ring P p.
        number_field k /\ prime_ideal (ring_of_integers k) P /\ prime p /\
        ring_of_num k p IN P
        ==> ideal_norm (ring_of_integers k) P =
            p EXP residue_degree (integer_ring,ring_of_integers k)
                    (ring_of_int k) P"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"p:num")] RING_OF_NUM_IN_PRIME_IDEAL) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool")] IDEAL_NORM_RESIDUE_DEGREE_Q) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"ring_of_num k p IN (P:A->bool)") THEN ASM_REWRITE_TAC [IN_SING, RING_OF_NUM_EQ_0] THEN RULE_ASSUM_TAC (REWRITE_RULE [number_field]) THEN ASM_SIMP_TAC [DIVIDES_ZERO, PRIME_IMP_NZ])

  let NUMBER_FIELD_PRIME_IDEAL_DEGREE_ONE ← prove
    r"!k:A ring P.
        number_field k /\ prime_ideal (ring_of_integers k) P /\
        ~(P = {ring_0 k})
        ==> (residue_degree (integer_ring,ring_of_integers k)
               (ring_of_int k) P = 1 <=>
             prime(ideal_norm (ring_of_integers k) P))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"P:A->bool")] RING_OF_INTEGERS_PRIME_IDEAL_ABOVE) THEN ASM_REWRITE_TAC [EXISTS_UNIQUE] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"p:num") (STRIP_ASSUME_TAC o CONJUNCT1)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"P:A->bool"), (← q r"p:num")] RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [PRIME_EXP])

  let RING_OF_INTEGERS_IDEAL_GENERATED_PRIME ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ q /\ (q ==> r) ==> p /\ q /\ r")
    prove
      r"!k:A ring p.
          number_field k /\ prime p
          ==> ~(ideal_generated (ring_of_integers k) {ring_of_num k p} =
                {ring_0 k}) /\
              {P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
                   ideal_generated (ring_of_integers k) {ring_of_num k p}
                   SUBSET P} =
              {P | prime_ideal (ring_of_integers k) P /\ ring_of_num k p IN P} /\
              FINITE {P | prime_ideal (ring_of_integers k) P /\
                          ring_of_num k p IN P}"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_of_num k p IN ring_carrier(ring_of_integers k) /\
                  ~(ring_of_num k p = ring_0 k:A)") STRIP_ASSUME_TAC THENL [FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [number_field])) THEN ASM_SIMP_TAC [RING_OF_NUM_EQ_0, DIVIDES_ZERO, PRIME_IMP_NZ] THEN MESON_TAC [RING_OF_NUM, RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(ideal_generated (ring_of_integers k) {ring_of_num k p} = {ring_0 k:A})") ASSUME_TAC THENL [ASM_MESON_TAC [IN_IDEAL_GENERATED_SELF, IN_SING], ALL_TAC] THEN MATCH_MP_TAC r1 THEN REPEAT CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC, REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC (← q r"P:A->bool") THEN ASM_CASES_TAC (← q r"prime_ideal (ring_of_integers k) (P:A->bool)") THEN ASM_SIMP_TAC [IDEAL_GENERATED_MINIMAL_EQ, PRIME_IMP_RING_IDEAL] THEN ASM SET_TAC [], DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ideal_generated (ring_of_integers k) {ring_of_num k p:A}")] DEDEKIND_IDEAL_FACTORIZATION) THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED, RING_OF_INTEGERS]])

  let NUMBER_FIELD_PRIME_FACTORIZATION_Q ← prove
    r"!k:A ring p.
        number_field k /\ prime p
        ==> ideal_generated (ring_of_integers k) {ring_of_num k p} =
            ideal_product (ring_of_integers k)
              {P | prime_ideal (ring_of_integers k) P /\
                   ring_of_num k p IN P}
              (\P. ideal_pow (ring_of_integers k) P
                     (ramification_index (integer_ring,ring_of_integers k)
                        (ring_of_int k) P))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"p:num")] RING_OF_INTEGERS_IDEAL_GENERATED_PRIME) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ideal_generated (ring_of_integers k) {ring_of_num k p:A}")] DEDEKIND_IDEAL_FACTORIZATION) THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED, RING_OF_INTEGERS] THEN DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC LAND_CONV [(← GSYM th)])) THEN MATCH_MP_TAC IDEAL_PRODUCT_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"p:num")] RAMIFICATION_INDEX_PRIME) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS])

  let NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE_Q ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(x:A) IN j ==> j SUBSET P ==> x IN P")
    prove
      r"!k:A ring p s e.
          number_field k /\ prime p /\ FINITE s /\
          (!P. P IN s ==> prime_ideal (ring_of_integers k) P /\ ~(e P = 0)) /\
          ideal_generated (ring_of_integers k) {ring_of_num k p} =
          ideal_product (ring_of_integers k) s
            (\P. ideal_pow (ring_of_integers k) P (e P))
          ==> s = {P | prime_ideal (ring_of_integers k) P /\
                       ring_of_num k p IN P} /\
              !P. P IN s ==> ramification_index (integer_ring,ring_of_integers k)
                               (ring_of_int k) P = e P"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"s:(A->bool)->bool"), (← q r"e:(A->bool)->num")] DEDEKIND_IDEAL_PRODUCT_PRIME_POW_UNIQUE) THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun z2 => (do let z3 ← (do let z4 ← (pure z2); pure (concl z4)); pure (is_eq z3)))))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"p:num")] RING_OF_INTEGERS_IDEAL_GENERATED_PRIME) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o (SYM o CONJUNCT1))) THEN ANTS_TAC THENL [ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_OF_INTEGERS], REWRITE_TAC [RING_OF_INTEGERS] THEN STRIP_TAC] THEN CONJ_TAC THENL [ASM_REWRITE_TAC [EXTENSION, IN_ELIM_THM], ALL_TAC] THEN X_GEN_TAC (← q r"P:A->bool") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"p:num")] RAMIFICATION_INDEX_PRIME) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"ideal_generated (ring_of_integers k) {ring_of_num k p}
                 SUBSET (P:A->bool)") THEN MATCH_MP_TAC r1 THEN REWRITE_TAC [IN_IDEAL_GENERATED_SELF] THEN MESON_TAC [RING_OF_NUM, RING_OF_INTEGERS])

  let NUMBER_FIELD_FUNDAMENTAL_IDENTITY_Q ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"2 <= p ==> ~(p = 1)")
    prove
      r"!k:A ring p.
          number_field k /\ prime p
          ==> nsum {P | prime_ideal (ring_of_integers k) P /\
                        ring_of_num k p IN P}
                   (\P. ramification_index (integer_ring,ring_of_integers k)
                          (ring_of_int k) P *
                        residue_degree (integer_ring,ring_of_integers k)
                          (ring_of_int k) P) =
              extension_degree (subfield_generated k {ring_0 k},k) I"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"p:num")] RING_OF_INTEGERS_IDEAL_GENERATED_PRIME) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ideal_generated (ring_of_integers k) {ring_of_num k p:A}")] IDEAL_NORM_FACTORIZATION) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"&p:int")] RING_OF_INTEGERS_IDEAL_NORM_INTEGER) THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED, RING_OF_INTEGERS, RING_OF_INTEGERS_FINITE_QUOTIENT, INT_OF_NUM_EQ, PRIME_IMP_NZ, RING_OF_INT_OF_NUM, INT_ABS_NUM, NUM_OF_INT_OF_NUM] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN SUBGOAL_THEN (← q r"!P. P IN {P | prime_ideal (ring_of_integers k) P /\
                     ring_of_num (k:A ring) p IN P}
          ==> ideal_norm (ring_of_integers k) P EXP
              ideal_valuation (ring_of_integers k) P
                (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
              p EXP (ramification_index (integer_ring,ring_of_integers k)
                       (ring_of_int k) P *
                     residue_degree (integer_ring,ring_of_integers k)
                       (ring_of_int k) P)") (MP_TAC o (MATCH_MP NPRODUCT_EQ)) THENL [REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"p:num")] RAMIFICATION_INDEX_PRIME) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"P:A->bool"), (← q r"p:num")] RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN REPEAT (DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC [EXP_EXP, MULT_SYM], ASM_SIMP_TAC [(← GSYM EXP_NSUM)] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [EQ_EXP, PRIME_IMP_NZ, PRIME_GE_2, r1] THEN MESON_TAC []])

  let NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"~(1 <= f) <=> f = 0")
    prove
      r"!k:A ring P p.
          number_field k /\ prime_ideal (ring_of_integers k) P /\ prime p /\
          ring_of_num k p IN P
          ==> 1 <= ramification_index (integer_ring,ring_of_integers k)
                     (ring_of_int k) P /\
              1 <= residue_degree (integer_ring,ring_of_integers k)
                     (ring_of_int k) P /\
              ramification_index (integer_ring,ring_of_integers k)
                (ring_of_int k) P *
              residue_degree (integer_ring,ring_of_integers k) (ring_of_int k) P
              <= extension_degree (subfield_generated k {ring_0 k},k) I"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"p:num")] RING_OF_INTEGERS_IDEAL_GENERATED_PRIME) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"P:A->bool")) o (GEN_REWRITE_RULE id [EXTENSION]))) THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"p:num")] RAMIFICATION_INDEX_PRIME) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"ideal_generated (ring_of_integers k) {ring_of_num k p:A}")] IDEAL_VALUATION_EQ_0) THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED, RING_OF_INTEGERS] THEN ARITH_TAC, MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool")] IDEAL_NORM_GT_1) THEN ASM_SIMP_TAC [RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q, RING_OF_INTEGERS_FINITE_QUOTIENT, PRIME_IMP_RING_IDEAL] THEN ANTS_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP PRIME_IDEAL_IMP_PSUBSET)) THEN SET_TAC [], ALL_TAC] THEN ONCE_REWRITE_TAC [(← GSYM CONTRAPOS_THM)] THEN REWRITE_TAC [r1] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [EXP, LT_REFL], MP_TAC (← ISPECL [(← q r"\P. ramification_index (integer_ring,ring_of_integers k)
               (ring_of_int k) P *
             residue_degree (integer_ring,ring_of_integers (k:A ring))
               (ring_of_int (k:A ring)) P"), (← q r"extension_degree (subfield_generated k {ring_0 k},k) (I:A->A)"), (← q r"{P | prime_ideal (ring_of_integers k) P /\
              ring_of_num k p IN (P:A->bool)}")] NSUM_POS_BOUND) THEN ASM_SIMP_TAC [NUMBER_FIELD_FUNDAMENTAL_IDENTITY_Q, LE_REFL] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN ASM_REWRITE_TAC [IN_ELIM_THM]])

  let NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"1 <= n <=> ~(n = 0)")
    prove
      r"!k:A ring p.
          number_field k /\ prime p
          ==> FINITE {P | prime_ideal (ring_of_integers k) P /\
                          ring_of_num k p IN P} /\
              ~({P | prime_ideal (ring_of_integers k) P /\
                     ring_of_num k p IN P} = {}) /\
              CARD {P | prime_ideal (ring_of_integers k) P /\
                        ring_of_num k p IN P}
              <= extension_degree (subfield_generated k {ring_0 k},k) I"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"p:num")] RING_OF_INTEGERS_IDEAL_GENERATED_PRIME) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o (CONJUNCT2 o CONJUNCT2)) THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"p:num")] NUMBER_FIELD_FUNDAMENTAL_IDENTITY_Q) THEN MP_TAC (← ISPEC (← q r"k:A ring") NUMBER_FIELD_DEGREE_POS) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN DISCH_THEN (SUBST_ALL_TAC o SYM) THEN CONJ_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE [NSUM_CLAUSES]) THEN ASM_ARITH_TAC, ASM_SIMP_TAC [CARD_EQ_NSUM] THEN MATCH_MP_TAC NSUM_LE THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"P:A->bool"), (← q r"p:num")] NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q) THEN ASM_REWRITE_TAC [r1, MULT_EQ_0] THEN ARITH_TAC])

  let NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE_IMAGE ← prove
    r"!k:A ring p s (P:K->A->bool) e.
        number_field k /\ prime p /\ FINITE s /\
        (!i. i IN s ==> prime_ideal (ring_of_integers k) (P i) /\ ~(e i = 0)) /\
        (!i j. i IN s /\ j IN s /\ P i = P j ==> i = j) /\
        ideal_generated (ring_of_integers k) {ring_of_num k p} =
        ideal_product (ring_of_integers k) s
          (\i. ideal_pow (ring_of_integers k) (P i) (e i))
        ==> {q | prime_ideal (ring_of_integers k) q /\ ring_of_num k p IN q} =
            IMAGE P s /\
            !i. i IN s ==> ramification_index (integer_ring,ring_of_integers k)
                             (ring_of_int k) (P i) = e i"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!i. i IN s ==> (@j. j IN s /\ (P:K->A->bool) j = P i) = i") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"p:num"), (← q r"IMAGE (P:K->A->bool) s"), (← q r"\q. (e:K->num) (@i. i IN s /\ (P:K->A->bool) i = q)")] NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE_Q) THEN FIRST_X_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP IDEAL_PRODUCT_IMAGE th)])) THEN ASM_SIMP_TAC [FORALL_IN_IMAGE, FINITE_IMAGE] THEN ANTS_TAC THENL [MATCH_MP_TAC IDEAL_PRODUCT_EQ THEN ASM_SIMP_TAC [o_THM], SIMP_TAC []])

  let NUMBER_FIELD_IDEAL_NORM_PRIME_PRODUCT ← prove
    r"!k:A ring p s (P:K->A->bool) e.
        number_field k /\ prime p /\ FINITE s /\
        (!i. i IN s
             ==> prime_ideal (ring_of_integers k) (P i) /\
                 ring_of_num k p IN P i)
        ==> FINITE(ring_carrier(quotient_ring (ring_of_integers k)
                    (ideal_product (ring_of_integers k) s
                      (\i. ideal_pow (ring_of_integers k) (P i) (e i))))) /\
            ideal_norm (ring_of_integers k)
              (ideal_product (ring_of_integers k) s
                (\i. ideal_pow (ring_of_integers k) (P i) (e i))) =
            p EXP nsum s (\i. residue_degree (integer_ring,ring_of_integers k)
                                (ring_of_int k) (P i) * e i)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"~(ring_of_num k p = ring_0 (k:A ring))") ASSUME_TAC THENL [REWRITE_TAC [RING_OF_NUM_EQ_0] THEN FIRST_ASSUM (MP_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN SIMP_TAC [DIVIDES_ZERO] THEN ASM_MESON_TAC [PRIME_IMP_NZ], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. i IN s
        ==> ring_ideal (ring_of_integers k) ((P:K->A->bool) i) /\
            ~(P i = {ring_0 k}) /\
            FINITE(ring_carrier(quotient_ring (ring_of_integers k) (P i))) /\
            ideal_norm (ring_of_integers k) (P i) =
            p EXP residue_degree (integer_ring,ring_of_integers k)
                    (ring_of_int k) (P i)") ASSUME_TAC THENL [X_GEN_TAC (← q r"i:K") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"i:K"))) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"~((P:K->A->bool) i = {ring_0 k})") ASSUME_TAC THENL [ASM_MESON_TAC [IN_SING], ALL_TAC] THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS_FINITE_QUOTIENT, RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"s:K->bool"), (← q r"\i. ideal_pow (ring_of_integers k) ((P:K->A->bool) i)
                                ((e:K->num) i)")] IDEAL_NORM_IDEAL_PRODUCT) THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_IDEAL_IDEAL_POW, INTEGRAL_DOMAIN_RING_OF_INTEGERS, NUMBER_FIELD_IMP_FIELD, IDEAL_NORM_IDEAL_POW, RING_OF_INTEGERS, (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") IDEAL_POW_EQ_ZERO))] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN TRANS_TAC EQ_TRANS (← q r"nproduct s (\i. p EXP (residue_degree (integer_ring,ring_of_integers k)
                             (ring_of_int k)
                             ((P:K->A->bool) i) * (e:K->num) i))") THEN CONJ_TAC THENL [REWRITE_TAC [nproduct] THEN MATCH_MP_TAC (← MATCH_MP ITERATE_EQ MONOIDAL_MUL) THEN ASM_SIMP_TAC [IDEAL_NORM_IDEAL_POW, DEDEKIND_RING_OF_INTEGERS, RING_OF_INTEGERS, EXP_EXP], UNDISCH_TAC (← q r"FINITE(s:K->bool)") THEN SPEC_TAC ((← q r"s:K->bool"), (← q r"s:K->bool")) THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN SIMP_TAC [NSUM_CLAUSES, NPRODUCT_CLAUSES, EXP, EXP_ADD]])

  let NUMBER_FIELD_PRIME_FACTORIZATION_SUBSET_EQ ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r3 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!k:A ring p s (P:K->A->bool) e.
          number_field k /\ prime p /\ FINITE s /\
          (!i. i IN s
               ==> prime_ideal (ring_of_integers k) (P i) /\
                   ring_of_num k p IN P i /\ ~(e i = 0)) /\
          (!i j. i IN s /\ j IN s /\ P i = P j ==> i = j) /\
          ideal_product (ring_of_integers k) s
            (\i. ideal_pow (ring_of_integers k) (P i) (e i)) SUBSET
          ideal_generated (ring_of_integers k) {ring_of_num k p} /\
          nsum s (\i. residue_degree (integer_ring,ring_of_integers k)
                        (ring_of_int k) (P i) * e i) =
          extension_degree (subfield_generated k {ring_0 k},k) I
          ==> ideal_generated (ring_of_integers k) {ring_of_num k p} =
              ideal_product (ring_of_integers k) s
                (\i. ideal_pow (ring_of_integers k) (P i) (e i)) /\
              {q | prime_ideal (ring_of_integers k) q /\ ring_of_num k p IN q} =
              IMAGE P s /\
              !i. i IN s ==> ramification_index (integer_ring,ring_of_integers k)
                               (ring_of_int k) (P i) = e i"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"p:num"), (← q r"s:K->bool"), (← q r"P:K->A->bool"), (← q r"e:K->num")] NUMBER_FIELD_IDEAL_NORM_PRIME_PRODUCT) THEN ASM_SIMP_TAC [] THEN STRIP_TAC THEN MATCH_MP_TAC r3 THEN CONJ_TAC THENL [W (fun (_, w) => tactic_of do pure (MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← (do let z2 ← (pure w); liftExcept (rand z2))), (← (do let z1 ← (pure w); liftExcept (lhs z1)))] IDEAL_NORM_SUBSET_EQ))) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_PRODUCT] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"&p:int")] RING_OF_INTEGERS_IDEAL_NORM_INTEGER) THEN ASM_REWRITE_TAC [RING_OF_INT_OF_NUM, INT_ABS_NUM, NUM_OF_INT_OF_NUM, INT_OF_NUM_EQ] THEN ASM_MESON_TAC [PRIME_IMP_NZ], DISCH_TAC THEN MATCH_MP_TAC NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE_IMAGE THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC []])

  let NUMBER_FIELD_PRIME_IDEAL_PROD_EQ ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!j k:A->bool. j SUBSET k /\ ~(j PSUBSET k) ==> j = k")
    prove
      r"!k:A ring p P Q.
          number_field k /\ prime p /\
          prime_ideal (ring_of_integers k)
            (ideal_generated (ring_of_integers k) {ring_of_num k p}) /\
          prime_ideal (ring_of_integers k) P /\
          prime_ideal (ring_of_integers k) Q /\
          ideal_generated (ring_of_integers k) {ring_of_num k p} =
          ideal_prod (ring_of_integers k) P Q
          ==> P = Q"
      (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"j = ideal_generated (ring_of_integers k) {ring_of_num k p:A}") THEN SUBGOAL_THEN (← q r"maximal_ideal (ring_of_integers k) (j:A->bool)") MP_TAC THENL [MATCH_MP_TAC DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_OF_INTEGERS] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_of_num k p IN (j:A->bool)") MP_TAC THENL [EXPAND_TAC "j" THEN MATCH_MP_TAC IDEAL_GENERATED_INC_GEN THEN REWRITE_TAC [IN_SING, RING_OF_INTEGERS] THEN REWRITE_TAC [(← GSYM RING_OF_INT_OF_NUM), RING_OF_INT_IN_RING_OF_INTEGERS], ASM_REWRITE_TAC [IN_SING] THEN RULE_ASSUM_TAC (REWRITE_RULE [number_field]) THEN ASM_REWRITE_TAC [RING_OF_NUM_EQ_0, DIVIDES_ZERO] THEN ASM_MESON_TAC [PRIME_IMP_NZ]], ALL_TAC] THEN REWRITE_TAC [maximal_ideal, NOT_EXISTS_THM] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT2) THEN SUBGOAL_THEN (← q r"proper_ideal (ring_of_integers k) (P:A->bool) /\
      proper_ideal (ring_of_integers k) (Q:A->bool)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [prime_ideal], ALL_TAC] THEN SUBGOAL_THEN (← q r"(j:A->bool) SUBSET P /\ j SUBSET Q") STRIP_ASSUME_TAC THENL [RULE_ASSUM_TAC (REWRITE_RULE [proper_ideal]) THEN ASM_SIMP_TAC [IDEAL_PROD_SUBSET_LEFT, IDEAL_PROD_SUBSET_RIGHT, RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"j:A->bool = P /\ j = Q") (fun th => MESON_TAC [th]) THEN CONJ_TAC THEN MATCH_MP_TAC r1 THEN ASM_MESON_TAC [])

  -- @@RETURN BEGIN
  return { ramification_index, residue_degree, RAMIFICATION_INDEX_INTEGER_RING,
           RESIDUE_DEGREE_INTEGER_RING, RING_OF_NUM_IN_PRIME_IDEAL,
           RING_OF_INT_IN_PRIME_IDEAL, RAMIFICATION_INDEX_PRIME,
           IDEAL_NORM_RESIDUE_DEGREE_Q, RING_OF_INTEGERS_PRIME_IDEAL_ABOVE,
           RING_OF_INTEGERS_RESIDUE_FIELD, RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q,
           NUMBER_FIELD_PRIME_IDEAL_DEGREE_ONE, RING_OF_INTEGERS_IDEAL_GENERATED_PRIME,
           NUMBER_FIELD_PRIME_FACTORIZATION_Q, NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE_Q,
           NUMBER_FIELD_FUNDAMENTAL_IDENTITY_Q,
           NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q, NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q,
           NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE_IMAGE,
           NUMBER_FIELD_IDEAL_NORM_PRIME_PRODUCT,
           NUMBER_FIELD_PRIME_FACTORIZATION_SUBSET_EQ, NUMBER_FIELD_PRIME_IDEAL_PROD_EQ }
  -- @@RETURN END

end HolANT.PrimeSplit
