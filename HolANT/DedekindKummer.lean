/- ========================================================================= -/
/- ANT: The Dedekind-Kummer theorem, for extensions of number fields ...   -/
/- ========================================================================= -/
/- File: HolANT/DedekindKummer.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/dedekind_kummer.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antdedekindkummerdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/products.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/prime_split.ml, ANT/norm_index.ml, ANT/discriminant.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/classgroup.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/relative_degree.ml, ANT/nf_valuation.ml, ANT/integrality.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.DedekindKummer fills them).

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
import HolANT.RingOfIntegers
import HolANT.PrimeSplit
import HolANT.NormIndex
import HolANT.Discriminant
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.Classgroup
import HolANT.TraceForm
import HolANT.RelativeSplit
import HolANT.RelativeDegree
import HolANT.NfValuation
import HolANT.Integrality

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
open HolANT.RingOfIntegers
open HolANT.PrimeSplit
open HolANT.NormIndex
open HolANT.Discriminant
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.Classgroup
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.RelativeDegree
open HolANT.NfValuation
open HolANT.Integrality

namespace HolANT.DedekindKummer

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (CARD_CLAUSES CARD_INTEGER_MOD_RING CARD_SUBSET COEFF_ABOVE_DEG COEFF_COMPOSE
   DEDEKIND_IDEAL_PRODUCT_PRIME_POW_UNIQUE DEDEKIND_IMP_INTEGRAL_DOMAIN
   DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL DEDEKIND_RING_OF_INTEGERS DIVIDES_ZERO
   EMPTY_SUBSET EQ_EXP EQ_TRANS EXISTS_IN_IMAGE EXP_EXP EXP_NSUM EXTENSION
   FIELD_EXTENSION_SUBFIELD_GENERATED FIELD_IMP_INTEGRAL_DOMAIN
   FIELD_IMP_NONTRIVIAL_RING FIELD_INTEGER_MOD_RING FIELD_QUOTIENT_RING
   FINITE_EMPTY FINITE_IMAGE FINITE_IMAGE_INJ_EQ FINITE_INSERT
   FINITE_INTEGER_MOD_RING FINITE_NUMSEG_LT FINITE_QUOTIENT_RING_MONO
   FINITE_SUBSET FIRST_RING_EPIMORPHISM_THEOREM FORALL_IN_GSPEC FORALL_IN_IMAGE
   FREE_BASIS_PRIME_SUBFIELD_INT_LINCOMB FUN_EQ_COEFF FUN_EQ_THM HAS_SIZE
   IDEAL_GENERATED_IMAGE_IDEAL_GENERATED IDEAL_GENERATED_INC
   IDEAL_GENERATED_INSERT IDEAL_GENERATED_INSERT_EQ IDEAL_GENERATED_MINIMAL
   IDEAL_GENERATED_MINIMAL_EQ IDEAL_GENERATED_MONO IDEAL_GENERATED_PAIR_EQ
   IDEAL_GENERATED_SING IDEAL_NORM_IDEAL_POW IDEAL_NORM_IDEAL_PRODUCT
   IDEAL_NORM_RESIDUE_DEGREE IDEAL_NORM_SUBSET_EQ IDEAL_POW_EQ_ZERO
   IDEAL_PRODUCT_EQ IDEAL_PRODUCT_IMAGE IDEAL_PRODUCT_POW_SETADD_SUBSET
   IMAGE_CLAUSES IMAGE_POLY_EXTEND_1 IMP_CONJ INFINITE INSERT_COMM INSERT_SUBSET
   INTEGER_MOD_RING_CLAUSES INTEGER_MOD_RING_OF_INT INTEGER_RING INT_ABS_NUM
   INT_ENTIRE INT_OF_NUM_EQ INT_REM_ZERO INT_SUB_0 IN_ELIM_THM IN_IMAGE
   IN_INSERT IN_NUMSEG IN_RING_IDEAL_0 IN_RING_POLYNOMIAL_CARRIER_COMPOSE
   IN_SING IN_UNIV ISOMORPHIC_RING_CARD ISOMORPHIC_RING_SYM I_O_ID I_THM
   LEFT_IMP_EXISTS_THM LE_0 LE_TRANS MAXIMAL_IDEAL_EPIMORPHISM_KERNEL
   MAXIMAL_IDEAL_POLY_RING_EPIMORPHISM MAXIMAL_IMP_PRIME_IDEAL
   MAXIMAL_IMP_PROPER_IDEAL MINIMAL_POLYNOMIAL
   MINIMAL_POLYNOMIAL_POWERS_INDEPENDENT MONIC_ASSOCIATES_EQ
   MONIC_HOMOMORPHIC_IMAGE MONO_EXISTS MULT_SYM NOT_EXISTS_THM NOT_IN_EMPTY
   NPRODUCT_EQ NSUM_EQ NUMBER_FIELD_ALGEBRAIC NUMBER_FIELD_HOMOMORPHIC_PREIMAGE
   NUMBER_FIELD_IDEAL_NORM_EXTENSION_Q NUMBER_FIELD_IMP_FIELD
   NUMBER_FIELD_INDEX_COPRIME NUMBER_FIELD_INTEGRAL_MULTIPLE NUM_OF_INT_OF_NUM
   POLY_0 POLY_COMPOSE_HOMOMORPHISM_CONST POLY_COMPOSE_HOMOMORPHISM_VAR
   POLY_CONST POLY_DEG_MONOMORPHIC_IMAGE POLY_DEG_PRODUCT_POW_MONIC POLY_DEG_REM
   POLY_DIV POLY_DIV_REM_SIMP POLY_EXTEND POLY_EXTEND_COMPOSE_COEFFS
   POLY_EXTEND_CONST POLY_EXTEND_EQ POLY_EXTEND_EVALUATE
   POLY_EXTEND_HOMOMORPHIC_IMAGE POLY_EXTEND_INTO_SUBRING_GENERATED
   POLY_EXTEND_SUB POLY_EXTEND_SUPERSET POLY_EXTEND_UNIVARIATE POLY_EXTEND_VAR
   POLY_REM POLY_RING_CLAUSES POLY_RING_INTEGER_MOD_RING_OF_INT POLY_VAR_UNIV : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (PRIME_IMP_NZ PRIME_IMP_RING_IDEAL PROPER_IDEAL_HOMOMORPHIC_PREIMAGE PSUBSET
   QUOTIENT_POLY_RING_HAS_SIZE QUOTIENT_RING_0 QUOTIENT_RING_CARRIER
   QUOTIENT_RING_PREIMAGE_IDEAL_GENERATED RING_0 RING_1 RING_ADD RING_ADD_LZERO
   RING_CARRIER_POLY_RING RING_CARRIER_SUBRING_GENERATED_0
   RING_CARRIER_SUBRING_GENERATED_SUBSET RING_CHAR_SUBFIELD_GENERATED RING_COSET
   RING_COSET_EQ RING_COSET_EQ_IDEAL RING_DIVIDES_PRODUCT_POW RING_DIVIDES_REFL
   RING_EPIMORPHISM_EQ RING_EPIMORPHISM_IMP_HOMOMORPHISM
   RING_EPIMORPHISM_INTEGER_MOD_RING RING_EPIMORPHISM_POLY_RINGS
   RING_EPIMORPHISM_PREIMAGE_IDEAL_GENERATED RING_EPIMORPHISM_RING_COSET
   RING_HOMOMORPHISM RING_HOMOMORPHISM_0 RING_HOMOMORPHISM_ADD
   RING_HOMOMORPHISM_COMPOSE RING_HOMOMORPHISM_EPIMORPHISM_FACTOR
   RING_HOMOMORPHISM_INTEGER_MOD_RING_OF_INT
   RING_HOMOMORPHISM_INTEGER_RING_OF_INT RING_HOMOMORPHISM_IN_CARRIER
   RING_HOMOMORPHISM_MUL RING_HOMOMORPHISM_POLY_EXTEND
   RING_HOMOMORPHISM_POLY_RINGS RING_HOMOMORPHISM_PRODUCT_POW
   RING_HOMOMORPHISM_RING_COSET RING_HOMOMORPHISM_RING_OF_INT
   RING_HOMOMORPHISM_RING_OF_INTEGERS RING_HOMOMORPHISM_RING_OF_NUM
   RING_HOMOMORPHISM_SUB RING_HOMOMORPHISM_SUBFIELD_INCLUSION RING_IDEAL_0
   RING_IDEAL_IDEAL_GENERATED RING_IDEAL_IDEAL_POW RING_IDEAL_IDEAL_PRODUCT
   RING_IDEAL_IMP_SUBSET RING_IDEAL_RING_KERNEL RING_KERNEL_INTEGER_MOD_RING
   RING_KERNEL_RING_COSET RING_MONOMORPHISM_INTEGER_RING_OF_INT RING_MUL
   RING_MUL_ASSOC RING_MUL_LZERO RING_MUL_RZERO RING_OF_INT RING_OF_INTEGERS
   RING_OF_INTEGERS_CARRIER RING_OF_INTEGERS_FINITE_QUOTIENT
   RING_OF_INTEGERS_IDEAL_EXTENSION RING_OF_INTEGERS_IDEAL_NORM_INTEGER
   RING_OF_INTEGERS_INTEGRAL_ELEMENT RING_OF_INTEGERS_MINIMAL_POLYNOMIAL_Q
   RING_OF_INTEGERS_SUBRING RING_OF_INTEGERS_SUBSET RING_OF_INT_1
   RING_OF_INT_EQ_0_CHAR_0 RING_OF_INT_EQ_CHAR_0 RING_OF_INT_IN_RING_OF_INTEGERS
   RING_OF_INT_IN_SUBFIELD_GENERATED RING_OF_INT_MUL RING_OF_INT_OF_NUM
   RING_OF_INT_SUB RING_OF_INT_SUBFIELD_GENERATED RING_OF_NUM RING_OF_NUM_EQ_0
   RING_POLYNOMIAL RING_POLYNOMIAL_COEFF RING_POLYNOMIAL_CONST
   RING_POLYNOMIAL_VAR RING_POW RING_PRODUCT RING_SETADD RING_SETADD_MONO
   RING_SETADD_SYM RING_SUB RING_SUB_RDISTRIB RING_SUM_EQ RING_SUM_SUPERSET
   RING_UNIT_1 SELECT_UNIQUE SIMPLE_IMAGE SING_SUBSET SKOLEM_THM
   SUBFIELD_GENERATED SUBRING_GENERATED_IDEMPOT_GEN SUBRING_GENERATED_INSERT
   SUBRING_GENERATED_INSERT_ZERO SUBRING_GENERATED_MINIMAL
   SUBRING_SUBRING_GENERATED SUBSET SUBSET_ANTISYM SUBSET_REFL SUBSET_UNIV
   TRIVIAL_RING_10 coeff ideal_norm integral_element maximal_ideal monic
   num_INFINITE number_field o_THM one poly_extend ramification_index
   ring_associates ring_divides ring_epimorphism ring_homomorphism ring_kernel
   ring_of_integers ring_setadd subring_of : thm)
  deriving Inhabited

/-- What dedekind_kummer.ml uses from Session besides theorems. -/
structure DedekindKummerDeps where
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
/- dedekind_kummer.ml phrases from line 88 to 769                         -/
/- ---------------------------------------------------------------------- -/

structure DedekindKummer01 where
  -- @@FIELDS
  RING_EPIMORPHISM_KERNEL_EQ : thm
  POLY_RING_INTEGER_MOD_RING_SUBSET : thm
  POLY_EXTEND_INTEGER_MOD_RING : thm
  RING_HOMOMORPHISM_POLY_EXTEND_INTEGER_MOD_RING : thm
  POLY_EXTEND_INTEGER_MOD_RING_OF_INT : thm
  POLY_EXTEND_FROM_COEFFS : thm
  IMAGE_POLY_EXTEND_INTEGER_RING : thm
  SUBRING_GENERATED_INT_LINCOMB : thm
  RING_EPIMORPHISM_POLY_EXTEND_QUOTIENT_RING : thm
  POLY_EXTEND_RING_OF_INTEGERS : thm
  RING_OF_INTEGERS_INTEGER_MINIMAL_POLYNOMIAL : thm
  NUMBER_FIELD_FINITE_INDEX_MULTIPLE : thm
  SUBRING_GENERATED_INDEX_COPRIME : thm
  DEDEKIND_KUMMER_EPIMORPHISM : thm
  DEDEKIND_KUMMER_KERNEL : thm
  DEDEKIND_KUMMER_QUOTIENT_RING : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDedekindKummer01 [HolBase] (D : DedekindKummerDeps) :
    ExceptT String IO DedekindKummer01 := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, RING_RULE, SET_TAC, TAUT, .. } := D
  let { COEFF_ABOVE_DEG, COEFF_COMPOSE, EQ_TRANS, EXISTS_IN_IMAGE, EXTENSION,
        FIELD_EXTENSION_SUBFIELD_GENERATED, FIELD_IMP_NONTRIVIAL_RING,
        FINITE_IMAGE_INJ_EQ, FINITE_NUMSEG_LT, FINITE_QUOTIENT_RING_MONO,
        FINITE_SUBSET, FIRST_RING_EPIMORPHISM_THEOREM, FORALL_IN_GSPEC,
        FORALL_IN_IMAGE, FREE_BASIS_PRIME_SUBFIELD_INT_LINCOMB, FUN_EQ_COEFF,
        FUN_EQ_THM, HAS_SIZE, IDEAL_GENERATED_INC, IDEAL_GENERATED_MINIMAL,
        IDEAL_GENERATED_SING, IDEAL_NORM_SUBSET_EQ, IMAGE_POLY_EXTEND_1, IMP_CONJ,
        INFINITE, INSERT_COMM, INTEGER_MOD_RING_CLAUSES, INTEGER_MOD_RING_OF_INT,
        INTEGER_RING, INT_ENTIRE, INT_OF_NUM_EQ, INT_REM_ZERO, INT_SUB_0, IN_ELIM_THM,
        IN_IMAGE, IN_NUMSEG, IN_RING_IDEAL_0, IN_RING_POLYNOMIAL_CARRIER_COMPOSE,
        IN_UNIV, ISOMORPHIC_RING_CARD, ISOMORPHIC_RING_SYM, I_O_ID, I_THM,
        LEFT_IMP_EXISTS_THM, LE_0, MINIMAL_POLYNOMIAL,
        MINIMAL_POLYNOMIAL_POWERS_INDEPENDENT, MONIC_HOMOMORPHIC_IMAGE, MONO_EXISTS,
        NUMBER_FIELD_ALGEBRAIC, NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_INDEX_COPRIME,
        NUMBER_FIELD_INTEGRAL_MULTIPLE, POLY_0, POLY_DEG_MONOMORPHIC_IMAGE,
        POLY_DEG_REM, POLY_DIV, POLY_DIV_REM_SIMP, POLY_EXTEND,
        POLY_EXTEND_COMPOSE_COEFFS, POLY_EXTEND_EQ, POLY_EXTEND_EVALUATE,
        POLY_EXTEND_HOMOMORPHIC_IMAGE, POLY_EXTEND_INTO_SUBRING_GENERATED,
        POLY_EXTEND_SUPERSET, POLY_EXTEND_UNIVARIATE, POLY_REM, POLY_RING_CLAUSES, .. } := D.core1
  let { QUOTIENT_POLY_RING_HAS_SIZE, QUOTIENT_RING_0, QUOTIENT_RING_CARRIER, RING_0,
        RING_ADD, RING_ADD_LZERO, RING_CARRIER_POLY_RING,
        RING_CARRIER_SUBRING_GENERATED_0, RING_CHAR_SUBFIELD_GENERATED, RING_COSET,
        RING_COSET_EQ, RING_COSET_EQ_IDEAL, RING_EPIMORPHISM_IMP_HOMOMORPHISM,
        RING_HOMOMORPHISM, RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_ADD,
        RING_HOMOMORPHISM_COMPOSE, RING_HOMOMORPHISM_EPIMORPHISM_FACTOR,
        RING_HOMOMORPHISM_INTEGER_MOD_RING_OF_INT,
        RING_HOMOMORPHISM_INTEGER_RING_OF_INT, RING_HOMOMORPHISM_IN_CARRIER,
        RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_POLY_EXTEND,
        RING_HOMOMORPHISM_RING_COSET, RING_HOMOMORPHISM_RING_OF_INT,
        RING_HOMOMORPHISM_RING_OF_NUM, RING_HOMOMORPHISM_SUBFIELD_INCLUSION,
        RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IMP_SUBSET, RING_IDEAL_RING_KERNEL,
        RING_MONOMORPHISM_INTEGER_RING_OF_INT, RING_MUL, RING_MUL_ASSOC,
        RING_MUL_LZERO, RING_MUL_RZERO, RING_OF_INT, RING_OF_INTEGERS,
        RING_OF_INTEGERS_MINIMAL_POLYNOMIAL_Q, RING_OF_INTEGERS_SUBRING,
        RING_OF_INTEGERS_SUBSET, RING_OF_INT_1, RING_OF_INT_EQ_0_CHAR_0,
        RING_OF_INT_EQ_CHAR_0, RING_OF_INT_IN_RING_OF_INTEGERS,
        RING_OF_INT_IN_SUBFIELD_GENERATED, RING_OF_INT_MUL, RING_OF_INT_SUB,
        RING_OF_INT_SUBFIELD_GENERATED, RING_OF_NUM, RING_OF_NUM_EQ_0, RING_POLYNOMIAL,
        RING_POLYNOMIAL_COEFF, RING_POW, RING_SUB_RDISTRIB, RING_SUM_EQ,
        RING_SUM_SUPERSET, RING_UNIT_1, SIMPLE_IMAGE, SING_SUBSET, SKOLEM_THM,
        SUBFIELD_GENERATED, SUBRING_GENERATED_INSERT, SUBRING_GENERATED_INSERT_ZERO,
        SUBRING_GENERATED_MINIMAL, SUBRING_SUBRING_GENERATED, SUBSET, SUBSET_ANTISYM,
        SUBSET_REFL, coeff, ideal_norm, monic, num_INFINITE, number_field, o_THM, one,
        poly_extend, ring_epimorphism, ring_kernel, ring_of_integers, ring_setadd,
        subring_of, .. } := D.core2
  -- @@SCOPE END

  let RING_EPIMORPHISM_KERNEL_EQ ← prove
    r"!r r' (f:A->B) j.
        ring_epimorphism(r,r') f /\ ring_ideal r j /\
        j SUBSET ring_kernel(r,r') f /\
        FINITE(ring_carrier(quotient_ring r j)) /\
        CARD(ring_carrier(quotient_ring r j)) = CARD(ring_carrier r')
        ==> ring_kernel(r,r') f = j"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_EPIMORPHISM_IMP_HOMOMORPHISM)) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"ring_kernel(r,r') (f:A->B)")] IDEAL_NORM_SUBSET_EQ) THEN ASM_SIMP_TAC [RING_IDEAL_RING_KERNEL] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC [ideal_norm] THEN MATCH_MP_TAC ISOMORPHIC_RING_CARD THEN ASM_SIMP_TAC [FIRST_RING_EPIMORPHISM_THEOREM] THEN DISJ1_TAC THEN MATCH_MP_TAC FINITE_QUOTIENT_RING_MONO THEN EXISTS_TAC (← q r"j:A->bool") THEN ASM_SIMP_TAC [RING_IDEAL_RING_KERNEL])

  let POLY_RING_INTEGER_MOD_RING_SUBSET ← prove
    r"!n (v:V->bool).
        ring_carrier(poly_ring (integer_mod_ring n) v) SUBSET
        ring_carrier(poly_ring integer_ring v)"
    (REWRITE_TAC [SUBSET, RING_CARRIER_POLY_RING, IN_ELIM_THM, INTEGER_RING, INTEGER_MOD_RING_CLAUSES, IN_UNIV] THEN MESON_TAC [])

  let POLY_EXTEND_INTEGER_MOD_RING ← prove
    r"!n (s:B ring).
        poly_extend (integer_mod_ring n,s):
          (int->B)->(V->B)->((V->num)->int)->B =
        poly_extend (integer_ring,s)"
    (REWRITE_TAC [FUN_EQ_THM, poly_extend, INTEGER_MOD_RING_CLAUSES, INTEGER_RING])

  let RING_HOMOMORPHISM_POLY_EXTEND_INTEGER_MOD_RING ← prove
    r"!(s:B ring) n v (x:V->B).
        ring_char s divides n /\ (!i. i IN v ==> x i IN ring_carrier s)
        ==> ring_homomorphism (poly_ring (integer_mod_ring n) v,s)
                              (poly_extend (integer_ring,s) (ring_of_int s) x)"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [(← GSYM POLY_EXTEND_INTEGER_MOD_RING)] THEN MATCH_MP_TAC RING_HOMOMORPHISM_POLY_EXTEND THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_MOD_RING_OF_INT])

  let POLY_EXTEND_INTEGER_MOD_RING_OF_INT ← prove
    r"!(s:B ring) n (x:V->B) p.
        ring_char s divides n
        ==> poly_extend (integer_ring,s) (ring_of_int s) x
              (ring_of_int (integer_mod_ring n) o p) =
            poly_extend (integer_ring,s) (ring_of_int s) x p"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"!z. ring_of_int s (ring_of_int (integer_mod_ring n) z) =
        ring_of_int (s:B ring) z") ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_RING_OF_INT, RING_HOMOMORPHISM_INTEGER_MOD_RING_OF_INT], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"{m | ~((p:(V->num)->int) m = &0)}"), (← q r"integer_ring"), (← q r"s:B ring"), (← q r"ring_of_int s:int->B")] POLY_EXTEND_SUPERSET) THEN REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← ISPECL [(← q r"p:(V->num)->int"), (← q r"x:V->B")] th) THEN MP_TAC (← ISPECL [(← q r"ring_of_int (integer_mod_ring n) o (p:(V->num)->int)"), (← q r"x:V->B")] th))) THEN REWRITE_TAC [INTEGER_RING, SUBSET_REFL, o_THM] THEN ANTS_TAC THENL [REWRITE_TAC [SUBSET, IN_ELIM_THM, INTEGER_MOD_RING_OF_INT] THEN MESON_TAC [INT_REM_ZERO], REPEAT (DISCH_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC []])

  let POLY_EXTEND_FROM_COEFFS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!r r' (h:A->B) x c d.
          ring_homomorphism(r,r') h /\ x IN ring_carrier r' /\
          (!i. i < d ==> c i IN ring_carrier r)
          ==> (\u:1->num. if u one < d then c(u one) else ring_0 r) IN
              ring_carrier(poly_ring r (:1)) /\
              poly_extend (r,r') h (\v. x)
                (\u:1->num. if u one < d then c(u one) else ring_0 r) =
              ring_sum r' {i | i < d}
                (\i. ring_mul r' (h(c i)) (ring_pow r' x i))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN ABBREV_TAC (← q r"q = \u:1->num. if u one < d then (c:num->A)(u one) else ring_0 r") THEN SUBGOAL_THEN (← q r"!i. coeff i q = if i < d then (c:num->A) i else ring_0 r") ASSUME_TAC THENL [EXPAND_TAC "q" THEN REWRITE_TAC [coeff], ALL_TAC] THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [REWRITE_TAC [(← GSYM RING_POLYNOMIAL), RING_POLYNOMIAL_COEFF] THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [RING_0], MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{i:num | i < d}") THEN REWRITE_TAC [FINITE_NUMSEG_LT, SUBSET, IN_ELIM_THM] THEN MESON_TAC []], DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"r':B ring"), (← q r"h:A->B"), (← q r"\v:1. (x:B)"), (← q r"q:(1->num)->A")] POLY_EXTEND_UNIVARIATE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC THEN REWRITE_TAC []] THEN SUBGOAL_THEN (← q r"!i. ~(i < d /\ i <= poly_deg r q)
          ==> ring_mul r' ((h:A->B)(coeff i q)) (ring_pow r' x i) = ring_0 r'") ASSUME_TAC THENL [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"coeff i (q:(1->num)->A) = ring_0 r") SUBST1_TAC THENL [ASM_CASES_TAC (← q r"i:num < d") THENL [ALL_TAC, ASM_REWRITE_TAC []] THEN MATCH_MP_TAC COEFF_ABOVE_DEG THEN ASM_REWRITE_TAC [RING_POLYNOMIAL] THEN ASM_ARITH_TAC, FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_0 th)])) THEN ASM_SIMP_TAC [RING_MUL_LZERO, RING_POW]], ALL_TAC] THEN TRANS_TAC EQ_TRANS (← q r"ring_sum r' {i | i < d /\ i <= poly_deg r q}
        (\i. ring_mul r' ((h:A->B)(coeff i q)) (ring_pow r' x i))") THEN CONJ_TAC THENL [MATCH_MP_TAC RING_SUM_SUPERSET THEN ASM_SIMP_TAC [SUBSET, IN_ELIM_THM, IN_NUMSEG, LE_0], CONV_TAC SYM_CONV THEN TRANS_TAC EQ_TRANS (← q r"ring_sum r' {i | i < d}
          (\i. ring_mul r' ((h:A->B)(coeff i q)) (ring_pow r' x i))") THEN CONJ_TAC THENL [MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC [IN_ELIM_THM], MATCH_MP_TAC RING_SUM_SUPERSET THEN ASM_SIMP_TAC [SUBSET, IN_ELIM_THM]]])

  let IMAGE_POLY_EXTEND_INTEGER_RING ← prove
    r"!k:A ring a.
        a IN ring_carrier k
        ==> IMAGE (poly_extend (integer_ring,k) (ring_of_int k) (\v. a))
                  (ring_carrier(poly_ring integer_ring (:1))) =
            ring_carrier(subring_generated k {a})"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_int k:int->A"), (← q r"integer_ring"), (← q r"k:A ring"), (← q r"a:A")] IMAGE_POLY_EXTEND_1) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [INTEGER_RING, (← GSYM SIMPLE_IMAGE), (← GSYM RING_CARRIER_SUBRING_GENERATED_0), SUBRING_GENERATED_INSERT] THEN ONCE_REWRITE_TAC [INSERT_COMM] THEN REWRITE_TAC [SUBRING_GENERATED_INSERT_ZERO])

  let SUBRING_GENERATED_INT_LINCOMB ← prove
    r"!k:A ring a q.
        a IN ring_carrier k /\
        q IN ring_carrier(poly_ring integer_ring (:1)) /\
        monic integer_ring q /\
        poly_extend (integer_ring,k) (ring_of_int k) (\v. a) q = ring_0 k
        ==> ring_carrier(subring_generated k {a}) =
            {ring_sum k {i | i < poly_deg integer_ring q}
               (\i. ring_mul k (ring_of_int k (c i)) (ring_pow k a i)) |
             c IN (:num->int)}"
    (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [(← GSYM IMAGE_POLY_EXTEND_INTEGER_RING)] THEN ABBREV_TAC (← q r"d = poly_deg integer_ring (q:(1->num)->int)") THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"k:A ring"), (← q r"ring_of_int k:int->A"), (← q r"a:A")] POLY_EXTEND_FROM_COEFFS) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, INTEGER_RING, IN_UNIV] THEN DISCH_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN X_GEN_TAC (← q r"z:A") THEN EQ_TAC THENL [ALL_TAC, DISCH_THEN (X_CHOOSE_THEN (← q r"c:num->int") SUBST1_TAC) THEN EXISTS_TAC (← q r"\u:1->num. if u one < d then (c:num->int)(u one) else &0") THEN ASM_REWRITE_TAC []] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"h:(1->num)->int") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"\i. coeff i (poly_rem integer_ring h q)") THEN FIRST_X_ASSUM (MP_TAC o (SPECL [(← q r"\i. coeff i (poly_rem integer_ring h q)"), (← q r"d:num")])) THEN DISCH_THEN (SUBST1_TAC o (SYM o CONJUNCT2)) THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"poly_rem integer_ring h q IN ring_carrier(poly_ring integer_ring (:1)) /\
    (poly_deg integer_ring (poly_rem integer_ring h q) < d \/
     poly_rem integer_ring h q = ring_0(poly_ring integer_ring (:1)))") (CONJUNCTS_THEN ASSUME_TAC) THENL [ASM_SIMP_TAC [POLY_REM] THEN EXPAND_TAC "d" THEN MATCH_MP_TAC POLY_DEG_REM THEN RULE_ASSUM_TAC (REWRITE_RULE [monic]) THEN ASM_REWRITE_TAC [RING_UNIT_1], ALL_TAC] THEN SUBGOAL_THEN (← q r"(\u:1->num. if u one < d then coeff (u one) (poly_rem integer_ring h q)
                else &0) = poly_rem integer_ring h q") SUBST1_TAC THENL [REWRITE_TAC [FUN_EQ_THM, coeff] THEN X_GEN_TAC (← q r"u:1->num") THEN SUBGOAL_THEN (← q r"(\v:1. (u:1->num) one) = u") SUBST1_TAC THENL [REWRITE_TAC [FUN_EQ_THM] THEN MESON_TAC [one], ALL_TAC] THEN COND_CASES_TAC THEN REWRITE_TAC [] THEN FIRST_X_ASSUM ((DISJ_CASES_THEN ASSUME_TAC) o (checkM (fun z1 => (do let z2 ← (do let z3 ← (pure z1); pure (concl z3)); pure (is_disj z2))))) THENL [MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"poly_rem integer_ring h q"), (← q r"(u:1->num) one")] COEFF_ABOVE_DEG) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_POLYNOMIAL] THEN ASM_ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [coeff, INTEGER_RING] THEN SUBGOAL_THEN (← q r"(\v:1. (u:1->num) one) = u") SUBST1_TAC THENL [REWRITE_TAC [FUN_EQ_THM] THEN MESON_TAC [one], SIMP_TAC []], ASM_REWRITE_TAC [POLY_RING_CLAUSES, POLY_0, INTEGER_RING]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"h:(1->num)->int"), (← q r"q:(1->num)->int")] POLY_DIV_REM_SIMP) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [(← SYM th)])) THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"k:A ring"), (← q r"(:1)"), (← q r"ring_of_int k:int->A"), (← q r"\v:1. (a:A)")] RING_HOMOMORPHISM_POLY_EXTEND) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN DISCH_THEN (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_ADD th), (← MATCH_MP RING_HOMOMORPHISM_MUL th), RING_MUL, POLY_DIV])) THEN ASM_SIMP_TAC [RING_MUL_RZERO, POLY_EXTEND, RING_ADD_LZERO])

  let RING_EPIMORPHISM_POLY_EXTEND_QUOTIENT_RING ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_sub r (ring_add r x y) x:A = y")
    let r2 ← TAUT (← q r"q /\ (q ==> p) ==> p /\ q")
    prove
      r"!r:A ring a n j.
          a IN ring_carrier r /\ ring_ideal r j /\ ring_of_num r n IN j /\
          ring_setadd r (ring_carrier(subring_generated r {a})) j =
          ring_carrier r
          ==> ring_epimorphism
               (poly_ring (integer_mod_ring n) (:1),quotient_ring r j)
               (poly_extend (integer_ring,quotient_ring r j)
                  (ring_of_int (quotient_ring r j)) (\v. ring_coset r j a)) /\
              (!g. poly_extend (integer_ring,quotient_ring r j)
                     (ring_of_int (quotient_ring r j)) (\v:1. ring_coset r j a)
                     (ring_of_int (integer_mod_ring n) o g) =
                   poly_extend (integer_ring,quotient_ring r j)
                     (ring_of_int (quotient_ring r j)) (\v. ring_coset r j a)
                     g) /\
              (!g. g IN ring_carrier(poly_ring integer_ring (:1))
                   ==> ring_coset r j
                         (poly_extend (integer_ring,r) (ring_of_int r) (\v. a)
                            g) =
                       poly_extend (integer_ring,quotient_ring r j)
                         (ring_of_int (quotient_ring r j)) (\v. ring_coset r j a)
                         g)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_HOMOMORPHISM_RING_COSET)) THEN SUBGOAL_THEN (← q r"ring_char(quotient_ring r (j:A->bool)) divides n") ASSUME_TAC THENL [REWRITE_TAC [(← GSYM RING_OF_NUM_EQ_0)] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM (← MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM th))])) THEN ASM_SIMP_TAC [QUOTIENT_RING_0, RING_COSET_EQ_IDEAL, RING_OF_NUM], ALL_TAC] THEN ASM_SIMP_TAC [POLY_EXTEND_INTEGER_MOD_RING_OF_INT] THEN MATCH_MP_TAC r2 THEN CONJ_TAC THENL [X_GEN_TAC (← q r"g:(1->num)->int") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"r:A ring"), (← q r"quotient_ring r (j:A->bool)"), (← q r"ring_of_int r:int->A"), (← q r"(:1)"), (← q r"\v:1. (a:A)"), (← q r"ring_coset r (j:A->bool)"), (← q r"g:(1->num)->int")] POLY_EXTEND_HOMOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, SUBSET, FORALL_IN_IMAGE] THEN DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN BINOP_TAC THEN REWRITE_TAC [FUN_EQ_THM, o_THM] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_RING_OF_INT], DISCH_TAC] THEN REWRITE_TAC [ring_epimorphism] THEN MP_TAC (← ISPECL [(← q r"quotient_ring r (j:A->bool)"), (← q r"n:num"), (← q r"(:1)"), (← q r"\v:1. ring_coset r j (a:A)")] RING_HOMOMORPHISM_POLY_EXTEND_INTEGER_MOD_RING) THEN ANTS_TAC THENL [ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, IN_ELIM_THM] THEN ASM_MESON_TAC [], DISCH_TAC] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [FIRST_ASSUM (ACCEPT_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [RING_HOMOMORPHISM]))), ALL_TAC] THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, SUBSET, FORALL_IN_GSPEC] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:A) IN ring_setadd r (ring_carrier(subring_generated r {a})) j") MP_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN REWRITE_TAC [ring_setadd, IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"z:A"), (← q r"w:A")] THEN STRIP_TAC THEN UNDISCH_TAC (← q r"(z:A) IN ring_carrier(subring_generated r {a})") THEN ASM_SIMP_TAC [(← GSYM IMAGE_POLY_EXTEND_INTEGER_RING), IN_IMAGE] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"h:(1->num)->int") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"ring_of_int (integer_mod_ring n) o (h:(1->num)->int)") THEN CONJ_TAC THENL [ALL_TAC, MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN EXISTS_TAC (← q r"integer_ring") THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT]] THEN ASM_SIMP_TAC [POLY_EXTEND_INTEGER_MOD_RING_OF_INT] THEN TRANS_TAC EQ_TRANS (← q r"ring_coset r j
        (poly_extend (integer_ring,r) (ring_of_int r) (\v:1. a:A) h)") THEN CONJ_TAC THENL [ALL_TAC, ASM_SIMP_TAC []] THEN SUBGOAL_THEN (← q r"(z:A) IN ring_carrier r /\ w IN ring_carrier r") MP_TAC THENL [ASM_MESON_TAC [POLY_EXTEND, RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [RING_COSET_EQ, RING_ADD] THEN ASM_SIMP_TAC [r1])

  let POLY_EXTEND_RING_OF_INTEGERS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!k:A ring (x:V->A) p.
          (!i. x i IN ring_carrier(ring_of_integers k)) /\
          p IN ring_carrier(poly_ring integer_ring (:V))
          ==> poly_extend (integer_ring,ring_of_integers k) (ring_of_int k) x p =
              poly_extend (integer_ring,k) (ring_of_int k) x p /\
              poly_extend (integer_ring,k) (ring_of_int k) x p IN
              ring_carrier(ring_of_integers k)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [REWRITE_TAC [ring_of_integers] THEN MATCH_MP_TAC POLY_EXTEND_INTO_SUBRING_GENERATED THEN EXISTS_TAC (← q r"(:V)") THEN ASM_REWRITE_TAC [(← GSYM ring_of_integers)] THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN REWRITE_TAC [RING_OF_INTEGERS], DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [POLY_EXTEND]])

  let RING_OF_INTEGERS_INTEGER_MINIMAL_POLYNOMIAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ q /\ (q ==> r) /\ s ==> p /\ r /\ q /\ s")
    prove
      r"!k:A ring a.
          number_field k /\ a IN ring_carrier(ring_of_integers k)
          ==> ?q. q IN ring_carrier(poly_ring integer_ring (:1)) /\
                  monic integer_ring q /\
                  poly_deg integer_ring q =
                  poly_deg (subfield_generated k {ring_0 k})
                    (minimal_polynomial
                       (subfield_generated k {ring_0 k},k) I a) /\
                  poly_extend (integer_ring,k) (ring_of_int k) (\v. a) q =
                  ring_0 k"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A")] RING_OF_INTEGERS_MINIMAL_POLYNOMIAL_Q) THEN ASM_REWRITE_TAC [SKOLEM_THM] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"c0:num->int")) THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"a:A")] MINIMAL_POLYNOMIAL) THEN ASM_SIMP_TAC [FIELD_EXTENSION_SUBFIELD_GENERATED, NUMBER_FIELD_ALGEBRAIC] THEN ABBREV_TAC (← q r"mu = minimal_polynomial (subfield_generated k {ring_0 k},k)
                       (I:A->A) a") THEN STRIP_TAC THEN EXISTS_TAC (← q r"\u:1->num. (c0:num->int)(u one)") THEN ABBREV_TAC (← q r"q = \u:1->num. (c0:num->int)(u one)") THEN SUBGOAL_THEN (← q r"!i. coeff i q = (c0:num->int) i") ASSUME_TAC THENL [EXPAND_TAC "q" THEN REWRITE_TAC [coeff], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_of_int (k:A ring) o (q:(1->num)->int) = mu") ASSUME_TAC THENL [ASM_REWRITE_TAC [(← GSYM FUN_EQ_COEFF), COEFF_COMPOSE], ALL_TAC] THEN SUBGOAL_THEN (← q r"(q:(1->num)->int) IN ring_carrier(poly_ring integer_ring (:1))") ASSUME_TAC THENL [REWRITE_TAC [(← GSYM RING_POLYNOMIAL), RING_POLYNOMIAL_COEFF] THEN REWRITE_TAC [INTEGER_RING, IN_UNIV] THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{d | ~(coeff d (mu:(1->num)->A) = ring_0 k)}") THEN CONJ_TAC THENL [UNDISCH_TAC (← q r"(mu:(1->num)->A) IN
          ring_carrier (poly_ring (subfield_generated k {ring_0 k}) (:1))") THEN REWRITE_TAC [(← GSYM RING_POLYNOMIAL), RING_POLYNOMIAL_COEFF] THEN SIMP_TAC [SUBFIELD_GENERATED], ASM_SIMP_TAC [SUBSET, IN_ELIM_THM, RING_OF_INT_EQ_0_CHAR_0]], ALL_TAC] THEN MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL [FIRST_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [(← SYM th)])) THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC POLY_DEG_MONOMORPHIC_IMAGE THEN REWRITE_TAC [RING_POLYNOMIAL] THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPEC (← q r"subfield_generated k {ring_0 k:A}") RING_MONOMORPHISM_INTEGER_RING_OF_INT) THEN ASM_REWRITE_TAC [RING_OF_INT_SUBFIELD_GENERATED, RING_CHAR_SUBFIELD_GENERATED], DISCH_TAC THEN UNDISCH_TAC (← q r"monic (subfield_generated k {ring_0 k}) (mu:(1->num)->A)") THEN ASM_REWRITE_TAC [monic, INTEGER_RING, SUBFIELD_GENERATED] THEN REWRITE_TAC [(← GSYM RING_OF_INT_1)] THEN ASM_SIMP_TAC [RING_OF_INT_EQ_CHAR_0], UNDISCH_TAC (← q r"poly_extend (subfield_generated k {ring_0 k},k) I (\v:1. a:A) mu =
        ring_0 k") THEN SIMP_TAC [POLY_EXTEND_EVALUATE, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, RING_HOMOMORPHISM_INTEGER_RING_OF_INT, I_O_ID] THEN ASM_REWRITE_TAC []])

  let NUMBER_FIELD_FINITE_INDEX_MULTIPLE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r4 ← TAUT (← q r"q /\ (~p ==> r) ==> (p ==> ~q) ==> r")
    prove
      r"!k:A ring M.
          number_field k /\ M subring_of ring_of_integers k /\
          FINITE {ring_coset (ring_of_integers k) M x |
                  x | x IN ring_carrier(ring_of_integers k)}
          ==> !x. x IN ring_carrier k
                  ==> ?d. ~(d = &0) /\ ring_mul k (ring_of_int k d) x IN M"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A")] NUMBER_FIELD_INTEGRAL_MULTIPLE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"d:int") STRIP_ASSUME_TAC) THEN ABBREV_TAC (← q r"y = ring_mul k (ring_of_int k d) (x:A)") THEN SUBGOAL_THEN (← q r"!j. ring_mul k (ring_of_int k (&j)) (y:A) IN
          ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [GEN_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_int k (&j):A"), (← q r"y:A")] RING_MUL) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS, RING_OF_INT_IN_RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"?j1 j2. ~(j1 = j2) /\
              ring_coset (ring_of_integers k) M
                (ring_mul k (ring_of_int k (&j1)) y) =
              ring_coset (ring_of_integers k) M
                (ring_mul k (ring_of_int k (&j2)) (y:A))") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"\j:num. ring_coset (ring_of_integers k) M
                   (ring_mul k (ring_of_int k (&j)) (y:A))"), (← q r"(:num)")] FINITE_IMAGE_INJ_EQ) THEN REWRITE_TAC [IN_UNIV, (← REWRITE_RULE [INFINITE] num_INFINITE)] THEN MATCH_MP_TAC r4 THEN CONJ_TAC THENL [ALL_TAC, MESON_TAC []] THEN FIRST_X_ASSUM (MATCH_MP_TAC o (MATCH_MP (← REWRITE_RULE [IMP_CONJ] FINITE_SUBSET))) THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_UNIV, IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun z1 => (do let z2 ← (do let z3 ← (pure z1); pure (concl z3)); pure (is_eq z2))))) THEN ASM_SIMP_TAC [RING_COSET_EQ] THEN REWRITE_TAC [RING_OF_INTEGERS] THEN SUBGOAL_THEN (← q r"ring_sub k (ring_mul k (ring_of_int k (&j1)) y)
                 (ring_mul k (ring_of_int k (&j2)) y) =
      ring_mul k (ring_of_int k (&j1 - &j2)) (ring_mul k (ring_of_int k d) x) /\
      ring_mul k (ring_of_int k (&j1 - &j2)) (ring_mul k (ring_of_int k d) x) =
      ring_mul k (ring_of_int k ((&j1 - &j2) * d)) (x:A)") (fun th => REWRITE_TAC [th]) THENL [EXPAND_TAC "y" THEN ASM_SIMP_TAC [RING_OF_INT_SUB, RING_OF_INT_MUL, RING_MUL_ASSOC, RING_OF_INT, RING_SUB_RDISTRIB, RING_MUL], DISCH_TAC THEN EXISTS_TAC (← q r"(&j1 - &j2) * d:int") THEN ASM_REWRITE_TAC [INT_ENTIRE, INT_SUB_0, INT_OF_NUM_EQ]])

  let SUBRING_GENERATED_INDEX_COPRIME ← prove
    r"!k:A ring a p N.
        number_field k /\ prime p /\ a IN ring_carrier(ring_of_integers k) /\
        {ring_coset (ring_of_integers k) (ring_carrier(subring_generated k {a}))
                    x | x | x IN ring_carrier(ring_of_integers k)} HAS_SIZE N
        ==> (ring_setadd (ring_of_integers k)
               (ring_carrier(subring_generated k {a}))
               (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
             ring_carrier(ring_of_integers k) <=>
             ~(p divides N))"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A")] RING_OF_INTEGERS_INTEGER_MINIMAL_POLYNOMIAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"q:(1->num)->int") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"q:(1->num)->int")] SUBRING_GENERATED_INT_LINCOMB) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_carrier(subring_generated k {a:A}) subring_of ring_of_integers k") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{a:A}")] SUBRING_SUBRING_GENERATED) THEN REWRITE_TAC [subring_of, RING_OF_INTEGERS] THEN SIMP_TAC [] THEN DISCH_TAC THEN MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET, RING_OF_INTEGERS_SUBRING], ALL_TAC] THEN MP_TAC (← BETA_RULE (← ISPECL [(← q r"k:A ring"), (← q r"poly_deg integer_ring (q:(1->num)->int)"), (← q r"\i. ring_pow k (a:A) i"), (← q r"ring_carrier(subring_generated k {a:A})"), (← q r"p:num"), (← q r"N:num")] NUMBER_FIELD_INDEX_COPRIME)) THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ALL_TAC, MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"a:A")] RING_POW) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN SIMP_TAC []] THEN MATCH_MP_TAC FREE_BASIS_PRIME_SUBFIELD_INT_LINCOMB THEN ASM_SIMP_TAC [RING_POW] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"c:num->int") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"a:A"), (← q r"\i. ring_of_int k ((c:num->int) i):A")] MINIMAL_POLYNOMIAL_POWERS_INDEPENDENT) THEN ASM_SIMP_TAC [FIELD_EXTENSION_SUBFIELD_GENERATED, NUMBER_FIELD_ALGEBRAIC, RING_OF_INT_IN_SUBFIELD_GENERATED, I_THM, (← CONJUNCT2 SUBFIELD_GENERATED), RING_OF_INT_EQ_0_CHAR_0], MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_carrier(subring_generated k {a:A})")] NUMBER_FIELD_FINITE_INDEX_MULTIPLE) THEN ANTS_TAC THENL [ASM_MESON_TAC [HAS_SIZE], ALL_TAC] THEN ASM_REWRITE_TAC [IN_ELIM_THM, IN_UNIV] THEN MESON_TAC []])

  let DEDEKIND_KUMMER_EPIMORPHISM ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_sub r (ring_add r x y) x:A = y")
    let r2 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!r s (h:A->B) k (f:A->C) p x j.
          ring_homomorphism(r,s) h /\ ring_epimorphism(r,k) f /\
          ring_kernel(r,k) f = p /\ x IN ring_carrier s /\
          ring_ideal s j /\ IMAGE h p SUBSET j /\
          ring_setadd s
            (ring_carrier
              (subring_generated s (x INSERT IMAGE h (ring_carrier r))))
            j = ring_carrier s
          ==> ?ph. ring_epimorphism(poly_ring k (:1),quotient_ring s j) ph /\
                    !g. g IN ring_carrier(poly_ring r (:1))
                        ==> ph(f o g) =
                            ring_coset s j (poly_extend (r,s) h (\v. x) g)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_EPIMORPHISM_IMP_HOMOMORPHISM)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_HOMOMORPHISM_RING_COSET)) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:C ring"), (← q r"quotient_ring s (j:B->bool)"), (← q r"f:A->C"), (← q r"ring_coset s (j:B->bool) o (h:A->B)")] RING_HOMOMORPHISM_EPIMORPHISM_FACTOR) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC (← q r"s:B ring") THEN ASM_REWRITE_TAC [], REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"y:A") THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(y:A) IN ring_carrier r") ASSUME_TAC THENL [UNDISCH_TAC (← q r"(y:A) IN p") THEN FIRST_X_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [(← SYM th)])) THEN SIMP_TAC [ring_kernel, IN_ELIM_THM], ALL_TAC] THEN ASM_SIMP_TAC [ring_kernel, IN_ELIM_THM, o_THM, QUOTIENT_RING_0] THEN wPart Except.ok (lhand o rand) RING_COSET_EQ_IDEAL THEN ANTS_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], DISCH_THEN SUBST1_TAC] THEN ASM SET_TAC []], DISCH_THEN (X_CHOOSE_THEN (← q r"hb:C->B->bool") STRIP_ASSUME_TAC)] THEN EXISTS_TAC (← q r"poly_extend (k,quotient_ring s j) (hb:C->B->bool)
                  (\v:1. ring_coset s j (x:B))") THEN SUBGOAL_THEN (← q r"!g. g IN ring_carrier(poly_ring r (:1))
          ==> poly_extend (k,quotient_ring s j) (hb:C->B->bool)
                (\v:1. ring_coset s j (x:B)) (f o g) =
              ring_coset s j (poly_extend (r,s) (h:A->B) (\v. x) g)") ASSUME_TAC THENL [X_GEN_TAC (← q r"g:(1->num)->A") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:C ring"), (← q r"quotient_ring s (j:B->bool)"), (← q r"f:A->C"), (← q r"hb:C->B->bool"), (← q r"\v:1. ring_coset s j (x:B)"), (← q r"g:(1->num)->A")] POLY_EXTEND_COMPOSE_COEFFS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"quotient_ring s (j:B->bool)"), (← q r"h:A->B"), (← q r"(:1)"), (← q r"\v:1. (x:B)"), (← q r"ring_coset s (j:B->bool)"), (← q r"g:(1->num)->A")] POLY_EXTEND_HOMOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC POLY_EXTEND_EQ THEN EXISTS_TAC (← q r"(:1)") THEN ASM_SIMP_TAC [o_THM, RING_COSET] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ASM_REWRITE_TAC []] THEN REWRITE_TAC [ring_epimorphism] THEN MATCH_MP_TAC r2 THEN CONJ_TAC THENL [MATCH_MP_TAC RING_HOMOMORPHISM_POLY_EXTEND THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, IN_ELIM_THM] THEN ASM_MESON_TAC [], DISCH_TAC] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [FIRST_ASSUM (ACCEPT_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [RING_HOMOMORPHISM]))), ALL_TAC] THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, SUBSET, FORALL_IN_GSPEC] THEN X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(y:B) IN ring_setadd s
        (ring_carrier
          (subring_generated s (x INSERT IMAGE (h:A->B) (ring_carrier r)))) j") MP_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"r:A ring"), (← q r"s:B ring"), (← q r"x:B")] IMAGE_POLY_EXTEND_1) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN REWRITE_TAC [ring_setadd, IN_ELIM_THM, EXISTS_IN_IMAGE] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM, IMP_CONJ] THEN X_GEN_TAC (← q r"z:B") THEN X_GEN_TAC (← q r"w:B") THEN REWRITE_TAC [IN_IMAGE] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"g:(1->num)->A") (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN DISCH_TAC THEN DISCH_THEN SUBST1_TAC THEN EXISTS_TAC (← q r"(f:A->C) o (g:(1->num)->A)") THEN CONJ_TAC THENL [ALL_TAC, MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN EXISTS_TAC (← q r"r:A ring") THEN ASM_REWRITE_TAC []] THEN ASM_SIMP_TAC [] THEN SUBGOAL_THEN (← q r"(w:B) IN ring_carrier s") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [RING_COSET_EQ, RING_ADD, POLY_EXTEND] THEN ASM_SIMP_TAC [r1, POLY_EXTEND])

  let DEDEKIND_KUMMER_KERNEL ← prove
    r"!r s (h:A->B) k (f:A->C) p x m.
        ring_homomorphism(r,s) h /\ field k /\ FINITE(ring_carrier k) /\
        ring_epimorphism(r,k) f /\ ring_kernel(r,k) f = p /\
        x IN ring_carrier s /\
        m IN ring_carrier(poly_ring r (:1)) /\ monic r m /\
        poly_extend (r,s) h (\v. x) m = ring_0 s /\
        ideal_norm s (ideal_generated s (IMAGE h p)) =
        CARD(ring_carrier k) EXP poly_deg r m /\
        ring_setadd s
          (ring_carrier
            (subring_generated s (x INSERT IMAGE h (ring_carrier r))))
          (ideal_generated s (IMAGE h p)) = ring_carrier s
        ==> ?ph. ring_epimorphism
                   (poly_ring k (:1),
                    quotient_ring s (ideal_generated s (IMAGE h p))) ph /\
                  (!g. g IN ring_carrier(poly_ring r (:1))
                       ==> ph(f o g) =
                           ring_coset s (ideal_generated s (IMAGE h p))
                             (poly_extend (r,s) h (\v. x) g)) /\
                  ring_kernel
                   (poly_ring k (:1),
                    quotient_ring s (ideal_generated s (IMAGE h p))) ph =
                  ideal_generated (poly_ring k (:1)) {f o m}"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN ABBREV_TAC (← q r"J = ideal_generated s (IMAGE (h:A->B) p)") THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_EPIMORPHISM_IMP_HOMOMORPHISM)) THEN SUBGOAL_THEN (← q r"p SUBSET ring_carrier(r:A ring)") ASSUME_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); pure (is_eq z4)) then (do let z9 ← (q r"p:A->bool"); let z8 ← (do let z6 ← (do let z7 ← (pure th); pure (concl z7)); liftExcept (rhs z6)); pure (z8 == z9)) else pure false))))) THEN REWRITE_TAC [ring_kernel, SUBSET, IN_ELIM_THM] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_ideal s (J:B->bool) /\ IMAGE (h:A->B) p SUBSET J") STRIP_ASSUME_TAC THENL [EXPAND_TAC "J" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN REWRITE_TAC [SUBSET] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"h:A->B"), (← q r"k:C ring"), (← q r"f:A->C"), (← q r"p:A->bool"), (← q r"x:B"), (← q r"J:B->bool")] DEDEKIND_KUMMER_EPIMORPHISM) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"ph:((1->num)->C)->B->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:C ring"), (← q r"f:A->C"), (← q r"m:(1->num)->A")] MONIC_HOMOMORPHIC_IMAGE) THEN ASM_SIMP_TAC [FIELD_IMP_NONTRIVIAL_RING] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(f:A->C) o (m:(1->num)->A) IN ring_carrier(poly_ring k (:1))") ASSUME_TAC THENL [MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN EXISTS_TAC (← q r"r:A ring") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:C ring"), (← q r"(f:A->C) o (m:(1->num)->A)")] QUOTIENT_POLY_RING_HAS_SIZE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do let z3 ← (q r"monic k ((f:A->C) o (m:(1->num)->A))"); let z2 ← (do let z1 ← (pure th); pure (concl z1)); pure (z2 == z3))))) THEN ASM_SIMP_TAC [monic, RING_UNIT_1], ASM_REWRITE_TAC [HAS_SIZE] THEN STRIP_TAC] THEN MATCH_MP_TAC RING_EPIMORPHISM_KERNEL_EQ THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_SIMP_TAC [RING_IDEAL_RING_KERNEL, RING_EPIMORPHISM_IMP_HOMOMORPHISM] THEN ASM_SIMP_TAC [ring_kernel, SING_SUBSET, IN_ELIM_THM] THEN ASM_SIMP_TAC [QUOTIENT_RING_0] THEN wPart Except.ok (lhand o rand) RING_COSET_EQ_IDEAL THEN ASM_REWRITE_TAC [RING_0] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [IN_RING_IDEAL_0], ASM_REWRITE_TAC [(← GSYM ideal_norm)]])

  let DEDEKIND_KUMMER_QUOTIENT_RING ← prove
    r"!r s (h:A->B) k (f:A->C) p x m.
        ring_homomorphism(r,s) h /\ field k /\ FINITE(ring_carrier k) /\
        ring_epimorphism(r,k) f /\ ring_kernel(r,k) f = p /\
        x IN ring_carrier s /\
        m IN ring_carrier(poly_ring r (:1)) /\ monic r m /\
        poly_extend (r,s) h (\v. x) m = ring_0 s /\
        ideal_norm s (ideal_generated s (IMAGE h p)) =
        CARD(ring_carrier k) EXP poly_deg r m /\
        ring_setadd s
          (ring_carrier
            (subring_generated s (x INSERT IMAGE h (ring_carrier r))))
          (ideal_generated s (IMAGE h p)) = ring_carrier s
        ==> (!g. g IN ring_carrier(poly_ring r (:1))
                 ==> (poly_extend (r,s) h (\v. x) g IN
                      ideal_generated s (IMAGE h p) <=>
                      ring_divides (poly_ring k (:1)) (f o m) (f o g))) /\
            quotient_ring s (ideal_generated s (IMAGE h p)) isomorphic_ring
            quotient_ring (poly_ring k (:1))
              (ideal_generated (poly_ring k (:1)) {f o m})"
    (REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP DEDEKIND_KUMMER_KERNEL)) THEN POP_ASSUM STRIP_ASSUME_TAC THEN ABBREV_TAC (← q r"J = ideal_generated s (IMAGE (h:A->B) p)") THEN DISCH_THEN (X_CHOOSE_THEN (← q r"ph:((1->num)->C)->B->bool") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ker")))) THEN CONJ_TAC THENL [ALL_TAC, FIRST_ASSUM (MP_TAC o (MATCH_MP FIRST_RING_EPIMORPHISM_THEOREM)) THEN USE_THEN "ker" SUBST1_TAC THEN MESON_TAC [ISOMORPHIC_RING_SYM]] THEN X_GEN_TAC (← q r"g:(1->num)->A") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"f:A->C"), (← q r"r:A ring"), (← q r"k:C ring")] RING_EPIMORPHISM_IMP_HOMOMORPHISM) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_ideal s (J:B->bool)") ASSUME_TAC THENL [EXPAND_TAC "J" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"(f:A->C) o (g:(1->num)->A) IN ring_carrier(poly_ring k (:1)) /\
    (f:A->C) o (m:(1->num)->A) IN ring_carrier(poly_ring k (:1))") STRIP_ASSUME_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN EXISTS_TAC (← q r"r:A ring") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_divides (poly_ring k (:1)) ((f:A->C) o (m:(1->num)->A))
                 ((f:A->C) o (g:(1->num)->A)) <=>
    (f:A->C) o g IN ideal_generated (poly_ring k (:1)) {f o m}") SUBST1_TAC THENL [ASM_SIMP_TAC [IDEAL_GENERATED_SING, IN_ELIM_THM], ALL_TAC] THEN REMOVE_THEN "ker" (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [ring_kernel, IN_ELIM_THM, QUOTIENT_RING_0] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_COSET_EQ_IDEAL THEN ASM_REWRITE_TAC [POLY_EXTEND])

  -- @@RETURN BEGIN
  return { RING_EPIMORPHISM_KERNEL_EQ, POLY_RING_INTEGER_MOD_RING_SUBSET,
           POLY_EXTEND_INTEGER_MOD_RING, RING_HOMOMORPHISM_POLY_EXTEND_INTEGER_MOD_RING,
           POLY_EXTEND_INTEGER_MOD_RING_OF_INT, POLY_EXTEND_FROM_COEFFS,
           IMAGE_POLY_EXTEND_INTEGER_RING, SUBRING_GENERATED_INT_LINCOMB,
           RING_EPIMORPHISM_POLY_EXTEND_QUOTIENT_RING, POLY_EXTEND_RING_OF_INTEGERS,
           RING_OF_INTEGERS_INTEGER_MINIMAL_POLYNOMIAL,
           NUMBER_FIELD_FINITE_INDEX_MULTIPLE, SUBRING_GENERATED_INDEX_COPRIME,
           DEDEKIND_KUMMER_EPIMORPHISM, DEDEKIND_KUMMER_KERNEL,
           DEDEKIND_KUMMER_QUOTIENT_RING }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- dedekind_kummer.ml phrases from line 824 to 1475                       -/
/- ---------------------------------------------------------------------- -/

structure DedekindKummer02 where
  -- @@FIELDS
  DEDEKIND_KUMMER_FACTOR : thm
  DEDEKIND_KUMMER : thm
  NUMBER_FIELD_DEDEKIND_KUMMER_DATA : thm
  NUMBER_FIELD_DEDEKIND_KUMMER_QUOTIENT_RING : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDedekindKummer02 [HolBase] (D : DedekindKummerDeps) (BDedekindKummer01 : DedekindKummer01) :
    ExceptT String IO DedekindKummer02 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, MESON_TAC, NUM_REDUCE_CONV, SET_RULE, SET_TAC, TAUT, .. } := D
  let { CARD_CLAUSES, CARD_SUBSET, DEDEKIND_IDEAL_PRODUCT_PRIME_POW_UNIQUE,
        DEDEKIND_IMP_INTEGRAL_DOMAIN, DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL,
        DEDEKIND_RING_OF_INTEGERS, EMPTY_SUBSET, EQ_EXP, EQ_TRANS, EXP_EXP, EXP_NSUM,
        EXTENSION, FIELD_IMP_INTEGRAL_DOMAIN, FIELD_IMP_NONTRIVIAL_RING,
        FIELD_QUOTIENT_RING, FINITE_EMPTY, FINITE_IMAGE, FINITE_INSERT,
        FIRST_RING_EPIMORPHISM_THEOREM, FORALL_IN_IMAGE, HAS_SIZE, IDEAL_GENERATED_INC,
        IDEAL_GENERATED_INSERT, IDEAL_GENERATED_MINIMAL, IDEAL_GENERATED_MINIMAL_EQ,
        IDEAL_GENERATED_MONO, IDEAL_GENERATED_SING, IDEAL_NORM_IDEAL_POW,
        IDEAL_NORM_IDEAL_PRODUCT, IDEAL_NORM_RESIDUE_DEGREE, IDEAL_NORM_SUBSET_EQ,
        IDEAL_POW_EQ_ZERO, IDEAL_PRODUCT_EQ, IDEAL_PRODUCT_IMAGE,
        IDEAL_PRODUCT_POW_SETADD_SUBSET, IMAGE_CLAUSES, INSERT_SUBSET, IN_ELIM_THM,
        IN_IMAGE, IN_INSERT, IN_RING_IDEAL_0, IN_RING_POLYNOMIAL_CARRIER_COMPOSE,
        ISOMORPHIC_RING_CARD, LE_TRANS, MAXIMAL_IDEAL_EPIMORPHISM_KERNEL,
        MAXIMAL_IDEAL_POLY_RING_EPIMORPHISM, MAXIMAL_IMP_PRIME_IDEAL,
        MAXIMAL_IMP_PROPER_IDEAL, MONIC_ASSOCIATES_EQ, MONIC_HOMOMORPHIC_IMAGE,
        MULT_SYM, NOT_EXISTS_THM, NOT_IN_EMPTY, NPRODUCT_EQ, NSUM_EQ,
        NUMBER_FIELD_HOMOMORPHIC_PREIMAGE, NUMBER_FIELD_IDEAL_NORM_EXTENSION_Q,
        POLY_DEG_PRODUCT_POW_MONIC, POLY_EXTEND, POLY_EXTEND_INTO_SUBRING_GENERATED, .. } := D.core1
  let { PRIME_IMP_RING_IDEAL, PROPER_IDEAL_HOMOMORPHIC_PREIMAGE, PSUBSET,
        QUOTIENT_RING_0, QUOTIENT_RING_PREIMAGE_IDEAL_GENERATED, RING_0, RING_1,
        RING_CARRIER_SUBRING_GENERATED_SUBSET, RING_COSET_EQ_IDEAL,
        RING_DIVIDES_PRODUCT_POW, RING_DIVIDES_REFL, RING_EPIMORPHISM_IMP_HOMOMORPHISM,
        RING_EPIMORPHISM_POLY_RINGS, RING_EPIMORPHISM_PREIMAGE_IDEAL_GENERATED,
        RING_EPIMORPHISM_RING_COSET, RING_HOMOMORPHISM_IN_CARRIER,
        RING_HOMOMORPHISM_POLY_EXTEND, RING_HOMOMORPHISM_POLY_RINGS,
        RING_HOMOMORPHISM_PRODUCT_POW, RING_HOMOMORPHISM_RING_OF_INTEGERS,
        RING_IDEAL_0, RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_POW,
        RING_IDEAL_IDEAL_PRODUCT, RING_IDEAL_IMP_SUBSET, RING_KERNEL_RING_COSET,
        RING_OF_INTEGERS, RING_OF_INTEGERS_FINITE_QUOTIENT,
        RING_OF_INTEGERS_IDEAL_EXTENSION, RING_OF_INTEGERS_INTEGRAL_ELEMENT,
        RING_POLYNOMIAL, RING_PRODUCT, RING_SETADD, RING_SETADD_MONO, RING_SETADD_SYM,
        SELECT_UNIQUE, SING_SUBSET, SUBRING_GENERATED_IDEMPOT_GEN, SUBSET,
        SUBSET_ANTISYM, SUBSET_REFL, TRIVIAL_RING_10, ideal_norm, integral_element,
        maximal_ideal, o_THM, ramification_index, ring_associates, ring_divides,
        ring_epimorphism, ring_kernel, ring_of_integers, .. } := D.core2
  let { DEDEKIND_KUMMER_EPIMORPHISM, DEDEKIND_KUMMER_KERNEL,
        DEDEKIND_KUMMER_QUOTIENT_RING, .. } := BDedekindKummer01
  -- @@SCOPE END

  let DEDEKIND_KUMMER_FACTOR ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"2 <= c ==> ~(c = 0) /\ ~(c = 1)")
    let r5 ← TAUT (← q r"a /\ (a ==> b) ==> a /\ b")
    prove
      r"!r s (h:A->B) k (f:A->C) p x m g P.
          ring_homomorphism(r,s) h /\ field k /\ FINITE(ring_carrier k) /\
          ring_epimorphism(r,k) f /\ ring_kernel(r,k) f = p /\
          x IN ring_carrier s /\
          m IN ring_carrier(poly_ring r (:1)) /\ monic r m /\
          poly_extend (r,s) h (\v. x) m = ring_0 s /\
          ideal_norm s (ideal_generated s (IMAGE h p)) =
          CARD(ring_carrier k) EXP poly_deg r m /\
          ring_setadd s
            (ring_carrier
              (subring_generated s (x INSERT IMAGE h (ring_carrier r))))
            (ideal_generated s (IMAGE h p)) = ring_carrier s /\
          g IN ring_carrier(poly_ring r (:1)) /\
          ring_irreducible (poly_ring k (:1)) (f o g) /\
          ring_divides (poly_ring k (:1)) (f o g) (f o m) /\
          P = ideal_generated s (poly_extend (r,s) h (\v. x) g INSERT IMAGE h p)
          ==> maximal_ideal s P /\ IMAGE h p SUBSET P /\
              {y | y IN ring_carrier r /\ h y IN P} = p /\
              ring_carrier(quotient_ring s P) HAS_SIZE
              CARD(ring_carrier k) EXP poly_deg k (f o g) /\
              residue_degree (r,s) h P = poly_deg k (f o g) /\
              (!g'. g' IN ring_carrier(poly_ring r (:1))
                    ==> (poly_extend (r,s) h (\v. x) g' IN P <=>
                         ring_divides (poly_ring k (:1)) (f o g) (f o g')))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM (ASSUME_TAC o (SYM o (checkM (fun th => (do if ← (do let z75 ← (do let z76 ← (pure th); pure (concl z76)); pure (is_eq z75)) then (do let z80 ← (q r"P:B->bool"); let z79 ← (do let z77 ← (do let z78 ← (pure th); pure (concl z78)); liftExcept (lhs z77)); pure (z79 == z80)) else pure false))))) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"h:A->B"), (← q r"k:C ring"), (← q r"f:A->C"), (← q r"p:A->bool"), (← q r"x:B"), (← q r"m:(1->num)->A")] DEDEKIND_KUMMER_KERNEL) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"J = ideal_generated s (IMAGE (h:A->B) p)") THEN DISCH_THEN (X_CHOOSE_THEN (← q r"ph:((1->num)->C)->B->bool") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ker")))) THEN MP_TAC (← ISPECL [(← q r"f:A->C"), (← q r"r:A ring"), (← q r"k:C ring")] RING_EPIMORPHISM_IMP_HOMOMORPHISM) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"p SUBSET ring_carrier(r:A ring)") ASSUME_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z69 ← (do let z70 ← (pure th); pure (concl z70)); pure (is_eq z69)) then (do let z74 ← (q r"p:A->bool"); let z73 ← (do let z71 ← (do let z72 ← (pure th); pure (concl z72)); liftExcept (rhs z71)); pure (z73 == z74)) else pure false))))) THEN REWRITE_TAC [ring_kernel, SUBSET, IN_ELIM_THM] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"IMAGE (h:A->B) p SUBSET ring_carrier s") ASSUME_TAC THENL [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_ideal s (J:B->bool) /\ IMAGE (h:A->B) p SUBSET J") STRIP_ASSUME_TAC THENL [EXPAND_TAC "J" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN REWRITE_TAC [SUBSET] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(f:A->C) o (g:(1->num)->A) IN ring_carrier(poly_ring k (:1)) /\
      (f:A->C) o (m:(1->num)->A) IN ring_carrier(poly_ring k (:1))") STRIP_ASSUME_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN EXISTS_TAC (← q r"r:A ring") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"a = poly_extend (r,s) (h:A->B) (\v:1. x) g") THEN SUBGOAL_THEN (← q r"(a:B) IN ring_carrier s") ASSUME_TAC THENL [EXPAND_TAC "a" THEN REWRITE_TAC [POLY_EXTEND], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_ideal s (P:B->bool) /\ J SUBSET P /\ (a:B) IN P") STRIP_ASSUME_TAC THENL [EXPAND_TAC "P" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN CONJ_TAC THENL [EXPAND_TAC "J" THEN MATCH_MP_TAC IDEAL_GENERATED_MONO THEN SET_TAC [], MATCH_MP_TAC IDEAL_GENERATED_INC THEN ASM_REWRITE_TAC [INSERT_SUBSET] THEN SET_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"P = {y | y IN ring_carrier s /\
               ring_coset s J y IN
               ideal_generated (quotient_ring s J)
                 {ph((f:A->C) o (g:(1->num)->A)):B->bool}}") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"J:B->bool"), (← q r"{a:B}")] QUOTIENT_RING_PREIMAGE_IDEAL_GENERATED) THEN ASM_REWRITE_TAC [SING_SUBSET, IMAGE_CLAUSES] THEN ASM_SIMP_TAC [] THEN DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "P" THEN GEN_REWRITE_TAC LAND_CONV [IDEAL_GENERATED_INSERT] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC RING_SETADD_SYM THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_generated (poly_ring k (:1)) {(f:A->C) o (g:(1->num)->A)} =
      {G | G IN ring_carrier(poly_ring k (:1)) /\
           ph G IN ideal_generated (quotient_ring s J)
                     {ph((f:A->C) o (g:(1->num)->A)):B->bool}}") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"poly_ring k (:1):((1->num)->C)ring"), (← q r"quotient_ring s (J:B->bool)"), (← q r"ph:((1->num)->C)->B->bool"), (← q r"{(f:A->C) o (g:(1->num)->A)}")] RING_EPIMORPHISM_PREIMAGE_IDEAL_GENERATED) THEN ASM_REWRITE_TAC [SING_SUBSET, IMAGE_CLAUSES] THEN ANTS_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, SING_SUBSET] THEN ASM_SIMP_TAC [IDEAL_GENERATED_SING, IN_ELIM_THM], DISCH_THEN (SUBST1_TAC o SYM) THEN REFL_TAC], ALL_TAC] THEN SUBGOAL_THEN (← q r"!g':(1->num)->A. g' IN ring_carrier(poly_ring r (:1))
           ==> (poly_extend (r,s) (h:A->B) (\v. x) g' IN P <=>
                ring_divides (poly_ring k (:1)) ((f:A->C) o (g:(1->num)->A))
                  (f o g'))") (LABEL_TAC "crit") THENL [X_GEN_TAC (← q r"q:(1->num)->A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(f:A->C) o (q:(1->num)->A) IN ring_carrier(poly_ring k (:1))") ASSUME_TAC THENL [MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN EXISTS_TAC (← q r"r:A ring") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN TRANS_TAC EQ_TRANS (← q r"(f:A->C) o (q:(1->num)->A) IN
        ideal_generated (poly_ring k (:1)) {f o (g:(1->num)->A)}") THEN CONJ_TAC THENL [ALL_TAC, MP_TAC (← ISPECL [(← q r"poly_ring k (:1):((1->num)->C)ring"), (← q r"(f:A->C) o (g:(1->num)->A)")] IDEAL_GENERATED_SING) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [IN_ELIM_THM]] THEN FIRST_ASSUM ((fun th => GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) o (checkM (fun th => (do if ← (do let z63 ← (do let z64 ← (pure th); pure (concl z64)); pure (is_eq z63)) then (do let z68 ← (q r"ideal_generated (poly_ring k (:1))                                 {(f:A->C) o (g:(1->num)->A)}"); let z67 ← (do let z65 ← (do let z66 ← (pure th); pure (concl z66)); liftExcept (lhs z65)); pure (z67 == z68)) else pure false)))) THEN FIRST_ASSUM ((fun th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) o (checkM (fun th => (do if ← (do if ← (do let z53 ← (do let z54 ← (pure th); pure (concl z54)); pure (is_eq z53)) then (do let z58 ← (q r"P:B->bool"); let z57 ← (do let z55 ← (do let z56 ← (pure th); pure (concl z56)); liftExcept (lhs z55)); pure (z57 == z58)) else pure false) then (do let z59 ← (do let z60 ← (do let z61 ← (do let z62 ← (pure th); pure (concl z62)); liftExcept (rhs z61)); liftExcept (rand z60)); pure (is_abs z59)) else pure false)))) THEN REWRITE_TAC [IN_ELIM_THM, POLY_EXTEND] THEN FIRST_ASSUM (MP_TAC o ((SPEC (← q r"q:(1->num)->A")) o (checkM (fun th => (do if ← (do let z44 ← (do let z45 ← (pure th); pure (concl z45)); pure (is_forall z44)) then (do let z46 ← (do let z47 ← (pure th); pure (concl z47)); canM (fun z48 => (do let z49 ← (pure z48); find_termM (fun z50 => (do let z52 ← (pure z50); let z51 ← (q r"ph:((1->num)->C)->B->bool"); pure (z51 == z52))) z49)) z46) else pure false))))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN REPEAT (FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o (checkM (fun th => (do if ← (do if ← (do if ← (do let z29 ← (do let z30 ← (pure th); pure (concl z30)); pure (is_eq z29)) then (do let z31 ← (do let z32 ← (do let z33 ← (pure th); pure (concl z33)); liftExcept (rhs z32)); pure (is_comb z31)) else pure false) then (do let z34 ← (do pure (Prod.fst (← (do let z35 ← (do let z36 ← (do let z37 ← (pure th); pure (concl z37)); liftExcept (rhs z36)); pure (strip_comb z35))))); pure (is_const z34)) else pure false) then (do let z43 ← (pure "GSPEC"); let z42 ← (do pure (Prod.fst (← (do let z38 ← (do pure (Prod.fst (← (do let z39 ← (do let z40 ← (do let z41 ← (pure th); pure (concl z41)); liftExcept (rhs z40)); pure (strip_comb z39))))); liftExcept (dest_const z38))))); pure (z42 == z43)) else pure false))))) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"h:A->B"), (← q r"k:C ring"), (← q r"f:A->C"), (← q r"p:A->bool"), (← q r"x:B"), (← q r"P:B->bool")] DEDEKIND_KUMMER_EPIMORPHISM) THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THENL [ASM SET_TAC [], ALL_TAC] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [MATCH_MP_TAC RING_SETADD THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, RING_CARRIER_SUBRING_GENERATED_SUBSET], FIRST_ASSUM ((fun th => tactic_of do pure (GEN_REWRITE_TAC LAND_CONV [(← SYM th)])) o (checkM (fun th => (do if ← (do if ← (do let z15 ← (do let z16 ← (pure th); pure (concl z16)); pure (is_eq z15)) then (do let z20 ← (q r"ring_carrier(s:B ring)"); let z19 ← (do let z17 ← (do let z18 ← (pure th); pure (concl z18)); liftExcept (rhs z17)); pure (z19 == z20)) else pure false) then (do let z21 ← (do let z22 ← (do let z23 ← (pure th); pure (concl z23)); liftExcept (lhs z22)); canM (fun z24 => (do let z25 ← (pure z24); find_termM (fun z26 => (do let z28 ← (pure z26); let z27 ← (q r"J:B->bool"); pure (z27 == z28))) z25)) z21) else pure false)))) THEN MATCH_MP_TAC RING_SETADD_MONO THEN ASM_REWRITE_TAC [SUBSET_REFL]], DISCH_THEN (X_CHOOSE_THEN (← q r"pp:((1->num)->C)->B->bool") STRIP_ASSUME_TAC)] THEN SUBGOAL_THEN (← q r"ring_kernel(poly_ring k (:1),quotient_ring (s:B ring) P) pp =
      ideal_generated (poly_ring k (:1)) {(f:A->C) o (g:(1->num)->A)}") ASSUME_TAC THENL [ASM_SIMP_TAC [IDEAL_GENERATED_SING] THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [ring_kernel, IN_ELIM_THM] THEN X_GEN_TAC (← q r"G:(1->num)->C") THEN ASM_CASES_TAC (← q r"(G:(1->num)->C) IN ring_carrier(poly_ring k (:1))") THEN ASM_REWRITE_TAC [] THENL [ALL_TAC, ASM_MESON_TAC [ring_divides]] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:C ring"), (← q r"f:A->C"), (← q r"(:1)")] RING_EPIMORPHISM_POLY_RINGS) THEN ASM_REWRITE_TAC [ring_epimorphism] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"G:(1->num)->C")) o ((REWRITE_RULE [EXTENSION, IN_IMAGE]) o CONJUNCT2))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"q:(1->num)->A") STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"q:(1->num)->A")) o (checkM (fun th => (do if ← (do let z6 ← (do let z7 ← (pure th); pure (concl z7)); pure (is_forall z6)) then (do let z8 ← (do let z9 ← (pure th); pure (concl z9)); canM (fun z10 => (do let z11 ← (pure z10); find_termM (fun z12 => (do let z14 ← (pure z12); let z13 ← (q r"pp:((1->num)->C)->B->bool"); pure (z13 == z14))) z11)) z8) else pure false))))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN ASM_SIMP_TAC [QUOTIENT_RING_0] THEN wPart lhand (lhand o rand) RING_COSET_EQ_IDEAL THEN ASM_REWRITE_TAC [POLY_EXTEND] THEN DISCH_THEN SUBST1_TAC THEN REMOVE_THEN "crit" (MP_TAC o (SPEC (← q r"q:(1->num)->A"))) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:C ring"), (← q r"s:B ring"), (← q r"P:B->bool"), (← q r"pp:((1->num)->C)->B->bool"), (← q r"(f:A->C) o (g:(1->num)->A)")] MAXIMAL_IDEAL_POLY_RING_EPIMORPHISM) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r5 THEN CONJ_TAC THENL [ASM SET_TAC [], DISCH_TAC] THEN SUBGOAL_THEN (← q r"{y | y IN ring_carrier r /\ (h:A->B) y IN P} = p") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:C ring"), (← q r"f:A->C")] MAXIMAL_IDEAL_EPIMORPHISM_KERNEL) THEN ASM_REWRITE_TAC [maximal_ideal] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"{y | y IN ring_carrier r /\ (h:A->B) y IN P}")) o ((REWRITE_RULE [NOT_EXISTS_THM]) o CONJUNCT2))) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"h:A->B"), (← q r"P:B->bool")] PROPER_IDEAL_HOMOMORPHIC_PREIMAGE) THEN ASM_SIMP_TAC [MAXIMAL_IMP_PROPER_IDEAL] THEN DISCH_TAC THEN REWRITE_TAC [PSUBSET] THEN ASM SET_TAC [], ASM_REWRITE_TAC []] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"h:A->B"), (← q r"P:B->bool")] IDEAL_NORM_RESIDUE_DEGREE) THEN ASM_SIMP_TAC [MAXIMAL_IMP_PRIME_IDEAL] THEN ANTS_TAC THENL [ASM_MESON_TAC [HAS_SIZE], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_norm (r:A ring) p = CARD(ring_carrier(k:C ring))") SUBST1_TAC THENL [REWRITE_TAC [ideal_norm] THEN MATCH_MP_TAC ISOMORPHIC_RING_CARD THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"ring_kernel(r,k) (f:A->C) = p") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC FIRST_RING_EPIMORPHISM_THEOREM THEN ASM_REWRITE_TAC [], ALL_TAC] THEN REWRITE_TAC [ideal_norm] THEN FIRST_ASSUM (SUBST1_TAC o (CONJUNCT2 o ((GEN_REWRITE_RULE id [HAS_SIZE]) o (checkM (fun th => (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); let z2 ← (pure "HAS_SIZE"); pure (is_binary z2 z3))))))) THEN REWRITE_TAC [EQ_EXP] THEN SUBGOAL_THEN (← q r"~(CARD(ring_carrier(k:C ring)) = 0) /\
                  ~(CARD(ring_carrier(k:C ring)) = 1)") (fun th => REWRITE_TAC [th]) THENL [MATCH_MP_TAC r1 THEN TRANS_TAC LE_TRANS (← q r"CARD{ring_0 k:C,ring_1 k}") THEN CONJ_TAC THENL [SIMP_TAC [CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY, IN_INSERT, NOT_IN_EMPTY] THEN MP_TAC (← ISPEC (← q r"k:C ring") TRIVIAL_RING_10) THEN ASM_SIMP_TAC [FIELD_IMP_NONTRIVIAL_RING] THEN CONV_TAC NUM_REDUCE_CONV, MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC [INSERT_SUBSET, EMPTY_SUBSET, RING_0, RING_1]], DISCH_THEN (ACCEPT_TAC o SYM)])

  let DEDEKIND_KUMMER ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(t:B->bool) SUBSET s ==> (s INTER t SUBSET q <=> t SUBSET q)")
    let r35 ← SET_RULE (← q r"(s:B->bool) = t ==> s SUBSET u ==> t SUBSET u")
    let r36 ← TAUT (← q r"a /\ (a ==> b) ==> a /\ b")
    prove
      r"!r s (h:A->B) k (f:A->C) p x m (t:K->bool) g e P.
          dedekind_domain s /\ ring_homomorphism(r,s) h /\
          field k /\ FINITE(ring_carrier k) /\
          ring_epimorphism(r,k) f /\ ring_kernel(r,k) f = p /\
          x IN ring_carrier s /\
          m IN ring_carrier(poly_ring r (:1)) /\ monic r m /\
          poly_extend (r,s) h (\v. x) m = ring_0 s /\
          ~(ideal_generated s (IMAGE h p) = {ring_0 s}) /\
          ideal_norm s (ideal_generated s (IMAGE h p)) =
          CARD(ring_carrier k) EXP poly_deg r m /\
          ring_setadd s
            (ring_carrier
              (subring_generated s (x INSERT IMAGE h (ring_carrier r))))
            (ideal_generated s (IMAGE h p)) = ring_carrier s /\
          FINITE t /\
          (!i. i IN t
               ==> g i IN ring_carrier(poly_ring r (:1)) /\
                   monic k (f o g i) /\
                   ring_irreducible (poly_ring k (:1)) (f o g i) /\
                   ~(e i = 0)) /\
          (!i j. i IN t /\ j IN t /\ f o g i = f o g j ==> i = j) /\
          f o m = ring_product (poly_ring k (:1)) t
                    (\i. ring_pow (poly_ring k (:1)) (f o g i) (e i)) /\
          (!i. i IN t
               ==> P i = ideal_generated s
                           (poly_extend (r,s) h (\v. x) (g i) INSERT IMAGE h p))
          ==> ideal_generated s (IMAGE h p) =
              ideal_product s t (\i. ideal_pow s (P i) (e i)) /\
              {Q | prime_ideal s Q /\ IMAGE h p SUBSET Q} = IMAGE P t /\
              (!i j. i IN t /\ j IN t /\ P i = P j ==> i = j) /\
              (!i. i IN t
                   ==> prime_ideal s (P i) /\
                       residue_degree (r,s) h (P i) = poly_deg k (f o g i) /\
                       ramification_index (r,s) h (P i) = e i)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM ((LABEL_TAC "Pdef") o (GSYM o (checkM (fun th => (do if ← (do if ← (do if ← (do let z37 ← (do let z38 ← (pure th); pure (concl z38)); pure (is_forall z37)) then (do let z39 ← (do pure (Prod.snd (← (do let z40 ← (do let z41 ← (pure th); pure (concl z41)); liftExcept (dest_forall z40))))); pure (is_imp z39)) else pure false) then (do let z42 ← (do let z43 ← (do pure (Prod.snd (← (do let z44 ← (do let z45 ← (pure th); pure (concl z45)); liftExcept (dest_forall z44))))); liftExcept (rand z43)); pure (is_eq z42)) else pure false) then (do let z51 ← (q r"(P:K->B->bool) i"); let z50 ← (do let z46 ← (do let z47 ← (do pure (Prod.snd (← (do let z48 ← (do let z49 ← (pure th); pure (concl z49)); liftExcept (dest_forall z48))))); liftExcept (rand z47)); liftExcept (lhand z46)); pure (z50 == z51)) else pure false))))) THEN MP_TAC (← ISPECL [(← q r"f:A->C"), (← q r"r:A ring"), (← q r"k:C ring")] RING_EPIMORPHISM_IMP_HOMOMORPHISM) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, DISCH_TAC] THEN SUBGOAL_THEN (← q r"!i. i IN t
          ==> ring_polynomial k ((f:A->C) o (g:K->(1->num)->A) i) /\
              (f:A->C) o g i IN ring_carrier(poly_ring k (:1))") ASSUME_TAC THENL [REWRITE_TAC [RING_POLYNOMIAL] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN EXISTS_TAC (← q r"r:A ring") THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. i IN t
          ==> maximal_ideal s ((P:K->B->bool) i) /\
              IMAGE (h:A->B) p SUBSET P i /\
              {y | y IN ring_carrier r /\ h y IN P i} = p /\
              ring_carrier(quotient_ring s (P i)) HAS_SIZE
              CARD(ring_carrier(k:C ring)) EXP
              poly_deg k ((f:A->C) o (g:K->(1->num)->A) i) /\
              residue_degree (r,s) h (P i) = poly_deg k (f o g i) /\
              (!g'. g' IN ring_carrier(poly_ring r (:1))
                    ==> (poly_extend (r,s) h (\v. x) g' IN P i <=>
                         ring_divides (poly_ring k (:1)) (f o g i) (f o g')))") (LABEL_TAC "fac") THENL [X_GEN_TAC (← q r"i:K") THEN DISCH_TAC THEN MATCH_MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"h:A->B"), (← q r"k:C ring"), (← q r"f:A->C"), (← q r"p:A->bool"), (← q r"x:B"), (← q r"m:(1->num)->A"), (← q r"(g:K->(1->num)->A) i"), (← q r"(P:K->B->bool) i")] DEDEKIND_KUMMER_FACTOR) THEN ASM_SIMP_TAC [] THEN MP_TAC (← BETA_RULE (← ISPECL [(← q r"poly_ring k (:1):((1->num)->C)ring"), (← q r"t:K->bool"), (← q r"\i. (f:A->C) o (g:K->(1->num)->A) i"), (← q r"e:K->num"), (← q r"i:K")] RING_DIVIDES_PRODUCT_POW)) THEN ASM_SIMP_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"J = ideal_generated s (IMAGE (h:A->B) p)") THEN SUBGOAL_THEN (← q r"p SUBSET ring_carrier(r:A ring)") ASSUME_TAC THENL [UNDISCH_TAC (← q r"ring_kernel(r,k) (f:A->C) = p") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [ring_kernel, SUBSET, IN_ELIM_THM] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"IMAGE (h:A->B) p SUBSET ring_carrier s") ASSUME_TAC THENL [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_ideal s (J:B->bool)") ASSUME_TAC THENL [EXPAND_TAC "J" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. i IN t
          ==> poly_extend (r,s) (h:A->B) (\v. x) ((g:K->(1->num)->A) i) IN
              ring_carrier s /\
              poly_extend (r,s) h (\v. x) (g i) IN P i /\
              J SUBSET P i /\
              ring_setadd s J
                (ideal_generated s {poly_extend (r,s) h (\v. x) (g i)}) = P i") (LABEL_TAC "Pi") THENL [X_GEN_TAC (← q r"i:K") THEN DISCH_TAC THEN MATCH_MP_TAC r36 THEN CONJ_TAC THENL [REWRITE_TAC [POLY_EXTEND], DISCH_TAC] THEN USE_THEN "Pdef" (MP_TAC o (SPEC (← q r"i:K"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, DISCH_THEN (SUBST1_TAC o SYM)] THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_INC THEN ASM_REWRITE_TAC [INSERT_SUBSET, IN_INSERT], EXPAND_TAC "J" THEN MATCH_MP_TAC IDEAL_GENERATED_MONO THEN SET_TAC [], GEN_REWRITE_TAC RAND_CONV [IDEAL_GENERATED_INSERT] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC RING_SETADD_SYM THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_GENERATED]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. i IN t ==> ~((P:K->B->bool) i = {ring_0 s})") ASSUME_TAC THENL [X_GEN_TAC (← q r"i:K") THEN DISCH_TAC THEN USE_THEN "Pi" (MP_TAC o (SPEC (← q r"i:K"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, STRIP_TAC] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"~(J = {ring_0(s:B ring)})") THEN REWRITE_TAC [] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [ASM SET_TAC [], ASM_SIMP_TAC [SING_SUBSET, IN_RING_IDEAL_0]], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_product s t (\i. ideal_pow s ((P:K->B->bool) i) (e i)) SUBSET J") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"J:B->bool"), (← q r"t:K->bool"), (← q r"\i. poly_extend (r,s) (h:A->B) (\v. x)
                            ((g:K->(1->num)->A) i)"), (← q r"e:K->num")] IDEAL_PRODUCT_POW_SETADD_SUBSET) THEN ASM_SIMP_TAC [] THEN ANTS_TAC THENL [ALL_TAC, MATCH_MP_TAC r35 THEN MATCH_MP_TAC IDEAL_PRODUCT_EQ THEN ASM_SIMP_TAC []] THEN MP_TAC (← ISPECL [(← q r"poly_ring r (:1):((1->num)->A)ring"), (← q r"s:B ring"), (← q r"poly_extend (r,s) (h:A->B) (\v:1. x)"), (← q r"t:K->bool"), (← q r"g:K->(1->num)->A"), (← q r"e:K->num")] RING_HOMOMORPHISM_PRODUCT_POW) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_HOMOMORPHISM_POLY_EXTEND], DISCH_THEN (SUBST1_TAC o SYM)] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"h:A->B"), (← q r"k:C ring"), (← q r"f:A->C"), (← q r"p:A->bool"), (← q r"x:B"), (← q r"m:(1->num)->A")] DEDEKIND_KUMMER_QUOTIENT_RING) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"ring_product (poly_ring r (:1)) t
          (\i. ring_pow (poly_ring r (:1)) ((g:K->(1->num)->A) i) (e i))")) o (CONJUNCT1 o (REWRITE_RULE [(← ASSUME (← q r"ideal_generated s (IMAGE (h:A->B) p) = J"))])))) THEN ANTS_TAC THENL [REWRITE_TAC [RING_PRODUCT], DISCH_THEN SUBST1_TAC] THEN MP_TAC (← BETA_RULE (← ISPECL [(← q r"poly_ring r (:1):((1->num)->A)ring"), (← q r"poly_ring k (:1):((1->num)->C)ring"), (← q r"\q:(1->num)->A. (f:A->C) o q"), (← q r"t:K->bool"), (← q r"g:K->(1->num)->A"), (← q r"e:K->num")] RING_HOMOMORPHISM_PRODUCT_POW)) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_HOMOMORPHISM_POLY_RINGS], DISCH_THEN SUBST1_TAC] THEN FIRST_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z29 ← (do let z30 ← (pure th); pure (concl z30)); pure (is_eq z29)) then (do let z34 ← (q r"(f:A->C) o (m:(1->num)->A)"); let z33 ← (do let z31 ← (do let z32 ← (pure th); pure (concl z32)); liftExcept (lhs z31)); pure (z33 == z34)) else pure false))))) THEN REWRITE_TAC [RING_DIVIDES_REFL] THEN MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN EXISTS_TAC (← q r"r:A ring") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"FINITE(ring_carrier(quotient_ring s
        (ideal_product s t (\i. ideal_pow s ((P:K->B->bool) i) (e i))))) /\
      ideal_norm s (ideal_product s t (\i. ideal_pow s (P i) (e i))) =
      ideal_norm s (J:B->bool)") STRIP_ASSUME_TAC THENL [SUBGOAL_THEN (← q r"!i. i IN t
            ==> ring_ideal s (ideal_pow s ((P:K->B->bool) i) (e i)) /\
                ~(ideal_pow s (P i) (e i) = {ring_0 s}) /\
                FINITE(ring_carrier(quotient_ring s (ideal_pow s (P i) (e i)))) /\
                ideal_norm s (ideal_pow s (P i) (e i)) =
                CARD(ring_carrier(k:C ring)) EXP
                (poly_deg k ((f:A->C) o (g:K->(1->num)->A) i) * e i)") ASSUME_TAC THENL [X_GEN_TAC (← q r"i:K") THEN DISCH_TAC THEN USE_THEN "fac" (MP_TAC o (SPEC (← q r"i:K"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, STRIP_TAC] THEN SUBGOAL_THEN (← q r"ring_ideal s ((P:K->B->bool) i)") ASSUME_TAC THENL [ASM_MESON_TAC [MAXIMAL_IMP_PRIME_IDEAL, PRIME_IMP_RING_IDEAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"~((P:K->B->bool) i = {ring_0 s})") ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"(P:K->B->bool) i"), (← q r"(e:K->num) i")] IDEAL_NORM_IDEAL_POW) THEN ANTS_TAC THENL [ASM_MESON_TAC [HAS_SIZE], STRIP_TAC] THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"(P:K->B->bool) i"), (← q r"(e:K->num) i")] IDEAL_POW_EQ_ZERO) THEN ASM_SIMP_TAC [DEDEKIND_IMP_INTEGRAL_DOMAIN], SUBGOAL_THEN (← q r"ideal_norm s ((P:K->B->bool) i) =
            CARD(ring_carrier(k:C ring)) EXP
            poly_deg k ((f:A->C) o (g:K->(1->num)->A) i)") SUBST1_TAC THENL [REWRITE_TAC [ideal_norm] THEN ASM_MESON_TAC [HAS_SIZE], REWRITE_TAC [EXP_EXP]]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"t:K->bool"), (← q r"\i. ideal_pow s ((P:K->B->bool) i) (e i)")] IDEAL_NORM_IDEAL_PRODUCT) THEN ANTS_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN ASM_REWRITE_TAC [] THEN TRANS_TAC EQ_TRANS (← q r"nproduct t (\i. CARD(ring_carrier(k:C ring)) EXP
                        (poly_deg k ((f:A->C) o (g:K->(1->num)->A) i) * e i))") THEN CONJ_TAC THENL [MATCH_MP_TAC NPRODUCT_EQ THEN ASM_SIMP_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [(← GSYM EXP_NSUM)] THEN AP_TERM_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:C ring"), (← q r"f:A->C"), (← q r"m:(1->num)->A")] MONIC_HOMOMORPHIC_IMAGE) THEN ASM_SIMP_TAC [FIELD_IMP_NONTRIVIAL_RING] THEN DISCH_THEN (SUBST1_TAC o (SYM o CONJUNCT2)) THEN FIRST_ASSUM (SUBST1_TAC o (checkM (fun th => (do if ← (do let z23 ← (do let z24 ← (pure th); pure (concl z24)); pure (is_eq z23)) then (do let z28 ← (q r"(f:A->C) o (m:(1->num)->A)"); let z27 ← (do let z25 ← (do let z26 ← (pure th); pure (concl z26)); liftExcept (lhs z25)); pure (z27 == z28)) else pure false)))) THEN MP_TAC (← ISPECL [(← q r"k:C ring"), (← q r"\i. (f:A->C) o (g:K->(1->num)->A) i"), (← q r"e:K->num"), (← q r"t:K->bool")] POLY_DEG_PRODUCT_POW_MONIC) THEN ASM_SIMP_TAC [] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN MATCH_MP_TAC NSUM_EQ THEN SIMP_TAC [MULT_SYM], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_product s t (\i. ideal_pow s ((P:K->B->bool) i) (e i)) = J") ASSUME_TAC THENL [CONV_TAC SYM_CONV THEN MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"ideal_product s t (\i. ideal_pow s ((P:K->B->bool) i) (e i))"), (← q r"J:B->bool")] IDEAL_NORM_SUBSET_EQ) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_PRODUCT], ALL_TAC] THEN SUBGOAL_THEN (← q r"!a b. a IN t /\ b IN t /\ (P:K->B->bool) a = P b
            ==> ring_divides (poly_ring k (:1))
                  ((f:A->C) o (g:K->(1->num)->A) b) (f o g a)") ASSUME_TAC THENL [MAP_EVERY X_GEN_TAC [(← q r"a:K"), (← q r"b:K")] THEN STRIP_TAC THEN USE_THEN "fac" (MP_TAC o (SPEC (← q r"b:K"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN DISCH_THEN (fun z21 => tactic_of do pure (MP_TAC (← SPEC (← q r"(g:K->(1->num)->A) a") (← (do let z22 ← (pure (CONJUNCTS z21)); liftExcept (last z22)))))) THEN ANTS_TAC THENL [ASM_SIMP_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z20 ← (q r"(P:K->B->bool) a = P b"); let z19 ← (do let z18 ← (pure th); pure (concl z18)); pure (z19 == z20)))))) THEN USE_THEN "Pi" (MP_TAC o (SPEC (← q r"a:K"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, SIMP_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i j. i IN t /\ j IN t /\ (P:K->B->bool) i = P j ==> i = j") ASSUME_TAC THENL [MAP_EVERY X_GEN_TAC [(← q r"i:K"), (← q r"j:K")] THEN STRIP_TAC THEN FIRST_X_ASSUM (MATCH_MP_TAC o (checkM (fun th => (do if ← (do if ← (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); pure (is_forall z2)) then (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); canM (fun z6 => (do let z7 ← (pure z6); find_termM (fun z8 => (do let z10 ← (pure z8); let z9 ← (q r"(f:A->C) o (g:K->(1->num)->A) i"); pure (z9 == z10))) z7)) z4) else pure false) then (do let z11 ← (do pure (Prod.snd (← (do let z12 ← (do let z13 ← (pure th); pure (concl z13)); pure (strip_forall z12))))); pure (is_imp z11)) else pure false) then (do let z14 ← (do let z15 ← (do pure (Prod.snd (← (do let z16 ← (do let z17 ← (pure th); pure (concl z17)); pure (strip_forall z16))))); liftExcept (rand z15)); pure (is_eq z14)) else pure false)))) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONIC_ASSOCIATES_EQ THEN EXISTS_TAC (← q r"k:C ring") THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, ring_associates], ALL_TAC] THEN ABBREV_TAC (← q r"ee = \Q:B->bool. (e:K->num) (@i. i IN t /\ P i = Q)") THEN SUBGOAL_THEN (← q r"!i. i IN t ==> ee((P:K->B->bool) i) = (e:K->num) i") ASSUME_TAC THENL [X_GEN_TAC (← q r"i:K") THEN DISCH_TAC THEN EXPAND_TAC "ee" THEN REWRITE_TAC [] THEN AP_TERM_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_product s t (\i. ideal_pow s ((P:K->B->bool) i) (e i)) =
      ideal_product s (IMAGE P t) (\Q. ideal_pow s Q (ee Q))") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"P:K->B->bool"), (← q r"t:K->bool"), (← q r"\Q. ideal_pow s Q ((ee:(B->bool)->num) Q)")] IDEAL_PRODUCT_IMAGE) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, DISCH_THEN SUBST1_TAC] THEN MATCH_MP_TAC IDEAL_PRODUCT_EQ THEN ASM_SIMP_TAC [o_THM], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_product s (IMAGE (P:K->B->bool) t) (\Q. ideal_pow s Q (ee Q)) = J") ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"IMAGE (P:K->B->bool) t"), (← q r"ee:(B->bool)->num")] DEDEKIND_IDEAL_PRODUCT_PRIME_POW_UNIQUE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [FINITE_IMAGE, FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"i:K") THEN DISCH_TAC THEN USE_THEN "fac" (MP_TAC o (SPEC (← q r"i:K"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, STRIP_TAC] THEN ASM_SIMP_TAC [MAXIMAL_IMP_PRIME_IDEAL], ASM_REWRITE_TAC [] THEN STRIP_TAC] THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"Q:B->bool") THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"prime_ideal s (Q:B->bool)") THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"J SUBSET Q <=> IMAGE (h:A->B) p SUBSET Q") SUBST1_TAC THENL [SUBST1_TAC (← SYM (← ASSUME (← q r"ideal_generated s (IMAGE (h:A->B) p) = J"))) THEN MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"Q:B->bool"), (← q r"IMAGE (h:A->B) p")] IDEAL_GENERATED_MINIMAL_EQ) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, DISCH_THEN SUBST1_TAC] THEN MATCH_MP_TAC r1 THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN EQ_TAC THEN SIMP_TAC [] THEN DISCH_TAC THEN DISCH_TAC THEN UNDISCH_TAC (← q r"~(J = {ring_0(s:B ring)})") THEN REWRITE_TAC [] THEN SUBST1_TAC (← SYM (← ASSUME (← q r"ideal_generated s (IMAGE (h:A->B) p) = J"))) THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN REWRITE_TAC [RING_IDEAL_0] THEN UNDISCH_TAC (← q r"Q = {ring_0(s:B ring)}") THEN UNDISCH_TAC (← q r"IMAGE (h:A->B) p SUBSET Q") THEN SET_TAC [], REWRITE_TAC [SING_SUBSET] THEN MATCH_MP_TAC IN_RING_IDEAL_0 THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED]], X_GEN_TAC (← q r"i:K") THEN DISCH_TAC THEN USE_THEN "fac" (MP_TAC o (SPEC (← q r"i:K"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, STRIP_TAC] THEN ASM_SIMP_TAC [MAXIMAL_IMP_PRIME_IDEAL, ramification_index]])

  let NUMBER_FIELD_DEDEKIND_KUMMER_DATA ← prove
    r"!k:A ring l:B ring h x m p.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        x IN ring_carrier l /\
        m IN ring_carrier(poly_ring (ring_of_integers k) (:1)) /\
        monic (ring_of_integers k) m /\
        poly_deg (ring_of_integers k) m = extension_degree(k,l) h /\
        poly_extend (ring_of_integers k,l) h (\v. x) m = ring_0 l /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        ring_setadd (ring_of_integers l)
          (ring_carrier(subring_generated l
             (x INSERT IMAGE h (ring_carrier(ring_of_integers k)))))
          (ideal_generated (ring_of_integers l) (IMAGE h p)) =
        ring_carrier(ring_of_integers l)
        ==> dedekind_domain(ring_of_integers l) /\
            ring_homomorphism(ring_of_integers k,ring_of_integers l) h /\
            field(quotient_ring (ring_of_integers k) p) /\
            FINITE(ring_carrier(quotient_ring (ring_of_integers k) p)) /\
            ring_epimorphism(ring_of_integers k,
                             quotient_ring (ring_of_integers k) p)
              (ring_coset (ring_of_integers k) p) /\
            ring_kernel(ring_of_integers k,
                        quotient_ring (ring_of_integers k) p)
              (ring_coset (ring_of_integers k) p) = p /\
            x IN ring_carrier(ring_of_integers l) /\
            poly_extend (ring_of_integers k,ring_of_integers l) h (\v. x) m =
            ring_0(ring_of_integers l) /\
            ~(ideal_generated (ring_of_integers l) (IMAGE h p) =
              {ring_0(ring_of_integers l)}) /\
            ideal_norm (ring_of_integers l)
              (ideal_generated (ring_of_integers l) (IMAGE h p)) =
            CARD(ring_carrier(quotient_ring (ring_of_integers k) p)) EXP
            poly_deg (ring_of_integers k) m /\
            ring_setadd (ring_of_integers l)
              (ring_carrier(subring_generated (ring_of_integers l)
                 (x INSERT IMAGE h (ring_carrier(ring_of_integers k)))))
              (ideal_generated (ring_of_integers l) (IMAGE h p)) =
            ring_carrier(ring_of_integers l) /\
            (!g. g IN ring_carrier(poly_ring (ring_of_integers k) (:1))
                 ==> poly_extend (ring_of_integers k,ring_of_integers l) h
                       (\v. x) g =
                     poly_extend (ring_of_integers k,l) h (\v. x) g)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"number_field(k:A ring)") ASSUME_TAC THENL [ASM_MESON_TAC [NUMBER_FIELD_HOMOMORPHIC_PREIMAGE], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"ring_homomorphism(ring_of_integers k,ring_of_integers l) (h:A->B)") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"x:B")] RING_OF_INTEGERS_INTEGRAL_ELEMENT) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [integral_element] THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"m:(1->num)->A") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!g. g IN ring_carrier(poly_ring (ring_of_integers k) (:1))
        ==> poly_extend (ring_of_integers k,ring_of_integers l) (h:A->B)
              (\v:1. x) g =
            poly_extend (ring_of_integers k,l) h (\v. x) g") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"l:B ring"), (← q r"{y:B | integral_element (integer_ring,l)
                                          (ring_of_int l) y}"), (← q r"h:A->B"), (← q r"(:1)"), (← q r"\v:1. (x:B)"), (← q r"g:(1->num)->A")] POLY_EXTEND_INTO_SUBRING_GENERATED) THEN ASM_REWRITE_TAC [(← GSYM ring_of_integers)], ALL_TAC] THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, FIELD_QUOTIENT_RING, RING_EPIMORPHISM_RING_COSET, RING_KERNEL_RING_COSET] THEN ASM_SIMP_TAC [RING_OF_INTEGERS, RING_OF_INTEGERS_IDEAL_EXTENSION] THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_OF_INTEGERS], MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_REWRITE_TAC [], MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_IDEAL_NORM_EXTENSION_Q) THEN ASM_REWRITE_TAC [ideal_norm], FIRST_X_ASSUM ((fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [(← SYM th)])) o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_eq z1)) then (do let z6 ← (q r"ring_carrier(ring_of_integers l:B ring)"); let z5 ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); liftExcept (rhs z3)); pure (z5 == z6)) else pure false)))) THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"(x:B) INSERT IMAGE (h:A->B) (ring_carrier(ring_of_integers k))"), (← q r"{y:B | integral_element (integer_ring,l) (ring_of_int l) y}")] SUBRING_GENERATED_IDEMPOT_GEN) THEN REWRITE_TAC [(← GSYM ring_of_integers)] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [INSERT_SUBSET, SUBSET, FORALL_IN_IMAGE] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER]])

  let NUMBER_FIELD_DEDEKIND_KUMMER_QUOTIENT_RING ← prove
    r"!k:A ring l:B ring h x m p.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        x IN ring_carrier l /\
        m IN ring_carrier(poly_ring (ring_of_integers k) (:1)) /\
        monic (ring_of_integers k) m /\
        poly_deg (ring_of_integers k) m = extension_degree(k,l) h /\
        poly_extend (ring_of_integers k,l) h (\v. x) m = ring_0 l /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        ring_setadd (ring_of_integers l)
          (ring_carrier(subring_generated l
             (x INSERT IMAGE h (ring_carrier(ring_of_integers k)))))
          (ideal_generated (ring_of_integers l) (IMAGE h p)) =
        ring_carrier(ring_of_integers l)
        ==> quotient_ring (ring_of_integers l)
              (ideal_generated (ring_of_integers l) (IMAGE h p))
            isomorphic_ring
            quotient_ring
              (poly_ring (quotient_ring (ring_of_integers k) p) (:1))
              (ideal_generated
                 (poly_ring (quotient_ring (ring_of_integers k) p) (:1))
                 {ring_coset (ring_of_integers k) p o m})"
    (REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP NUMBER_FIELD_DEDEKIND_KUMMER_DATA)) THEN FIRST_X_ASSUM STRIP_ASSUME_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring"), (← q r"h:A->B"), (← q r"quotient_ring (ring_of_integers k) (p:A->bool)"), (← q r"ring_coset (ring_of_integers k) (p:A->bool)"), (← q r"p:A->bool"), (← q r"x:B"), (← q r"m:(1->num)->A")] DEDEKIND_KUMMER_QUOTIENT_RING) THEN ASM_REWRITE_TAC [] THEN SIMP_TAC [])

  -- @@RETURN BEGIN
  return { DEDEKIND_KUMMER_FACTOR, DEDEKIND_KUMMER, NUMBER_FIELD_DEDEKIND_KUMMER_DATA,
           NUMBER_FIELD_DEDEKIND_KUMMER_QUOTIENT_RING }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- dedekind_kummer.ml phrases from line 1508 to 2027                      -/
/- ---------------------------------------------------------------------- -/

structure DedekindKummer03 where
  -- @@FIELDS
  NUMBER_FIELD_DEDEKIND_KUMMER_FACTOR : thm
  NUMBER_FIELD_DEDEKIND_KUMMER : thm
  DEDEKIND_KUMMER_EPIMORPHISM_Q : thm
  DEDEKIND_KUMMER_INTEGER_DATA : thm
  DEDEKIND_KUMMER_QUOTIENT_RING_Q : thm
  DEDEKIND_KUMMER_FACTOR_Q : thm
  DEDEKIND_KUMMER_Q : thm
  DEDEKIND_KUMMER_LINEAR_IDEAL : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDedekindKummer03 [HolBase] (D : DedekindKummerDeps) (BDedekindKummer01 : DedekindKummer01) (BDedekindKummer02 : DedekindKummer02) :
    ExceptT String IO DedekindKummer03 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, .. } := D
  let { CARD_INTEGER_MOD_RING, DEDEKIND_RING_OF_INTEGERS, DIVIDES_ZERO, EQ_TRANS,
        EXTENSION, FIELD_INTEGER_MOD_RING, FINITE_INTEGER_MOD_RING, FORALL_IN_IMAGE,
        IDEAL_GENERATED_IMAGE_IDEAL_GENERATED, IDEAL_GENERATED_INC,
        IDEAL_GENERATED_INSERT_EQ, IDEAL_GENERATED_MINIMAL, IDEAL_GENERATED_MINIMAL_EQ,
        IDEAL_GENERATED_PAIR_EQ, IMAGE_CLAUSES, IMAGE_POLY_EXTEND_1, INSERT_COMM,
        INTEGER_RING, INT_ABS_NUM, INT_OF_NUM_EQ, IN_ELIM_THM,
        IN_RING_POLYNOMIAL_CARRIER_COMPOSE, IN_SING, IN_UNIV, MAXIMAL_IMP_PRIME_IDEAL,
        NUM_OF_INT_OF_NUM, POLY_COMPOSE_HOMOMORPHISM_CONST,
        POLY_COMPOSE_HOMOMORPHISM_VAR, POLY_CONST, POLY_EXTEND_CONST, POLY_EXTEND_SUB,
        POLY_EXTEND_VAR, POLY_RING_CLAUSES, POLY_RING_INTEGER_MOD_RING_OF_INT,
        POLY_VAR_UNIV, .. } := D.core1
  let { PRIME_IMP_NZ, PRIME_IMP_RING_IDEAL, RING_COSET_EQ_IDEAL, RING_EPIMORPHISM_EQ,
        RING_EPIMORPHISM_INTEGER_MOD_RING, RING_HOMOMORPHISM_INTEGER_RING_OF_INT,
        RING_HOMOMORPHISM_IN_CARRIER, RING_HOMOMORPHISM_POLY_RINGS,
        RING_HOMOMORPHISM_SUB, RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IMP_SUBSET,
        RING_KERNEL_INTEGER_MOD_RING, RING_OF_INT, RING_OF_INTEGERS,
        RING_OF_INTEGERS_CARRIER, RING_OF_INTEGERS_IDEAL_NORM_INTEGER,
        RING_OF_INTEGERS_SUBRING, RING_OF_INTEGERS_SUBSET, RING_OF_INT_OF_NUM,
        RING_OF_NUM, RING_OF_NUM_EQ_0, RING_POLYNOMIAL_CONST, RING_POLYNOMIAL_VAR,
        RING_SETADD, RING_SETADD_MONO, RING_SUB, SING_SUBSET,
        SUBRING_GENERATED_IDEMPOT_GEN, SUBRING_GENERATED_MINIMAL, SUBSET,
        SUBSET_ANTISYM, SUBSET_REFL, SUBSET_UNIV, integral_element, number_field,
        ring_divides, ring_homomorphism, ring_of_integers, .. } := D.core2
  let { DEDEKIND_KUMMER_QUOTIENT_RING, IMAGE_POLY_EXTEND_INTEGER_RING,
        POLY_EXTEND_RING_OF_INTEGERS, POLY_RING_INTEGER_MOD_RING_SUBSET,
        RING_EPIMORPHISM_POLY_EXTEND_QUOTIENT_RING, .. } := BDedekindKummer01
  let { DEDEKIND_KUMMER, DEDEKIND_KUMMER_FACTOR, NUMBER_FIELD_DEDEKIND_KUMMER_DATA, .. } := BDedekindKummer02
  -- @@SCOPE END

  let NUMBER_FIELD_DEDEKIND_KUMMER_FACTOR ← prove
    r"!k:A ring l:B ring h x m p g.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        x IN ring_carrier l /\
        m IN ring_carrier(poly_ring (ring_of_integers k) (:1)) /\
        monic (ring_of_integers k) m /\
        poly_deg (ring_of_integers k) m = extension_degree(k,l) h /\
        poly_extend (ring_of_integers k,l) h (\v. x) m = ring_0 l /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        ring_setadd (ring_of_integers l)
          (ring_carrier(subring_generated l
             (x INSERT IMAGE h (ring_carrier(ring_of_integers k)))))
          (ideal_generated (ring_of_integers l) (IMAGE h p)) =
        ring_carrier(ring_of_integers l) /\
        g IN ring_carrier(poly_ring (ring_of_integers k) (:1)) /\
        ring_irreducible (poly_ring (quotient_ring (ring_of_integers k) p) (:1))
          (ring_coset (ring_of_integers k) p o g) /\
        ring_divides (poly_ring (quotient_ring (ring_of_integers k) p) (:1))
          (ring_coset (ring_of_integers k) p o g)
          (ring_coset (ring_of_integers k) p o m)
        ==> maximal_ideal (ring_of_integers l)
              (ideal_generated (ring_of_integers l)
                 (poly_extend (ring_of_integers k,l) h (\v. x) g INSERT
                  IMAGE h p)) /\
            IMAGE h p SUBSET
              ideal_generated (ring_of_integers l)
                 (poly_extend (ring_of_integers k,l) h (\v. x) g INSERT
                  IMAGE h p) /\
            residue_degree (ring_of_integers k,ring_of_integers l) h
              (ideal_generated (ring_of_integers l)
                 (poly_extend (ring_of_integers k,l) h (\v. x) g INSERT
                  IMAGE h p)) =
            poly_deg (quotient_ring (ring_of_integers k) p)
              (ring_coset (ring_of_integers k) p o g)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"x:B"), (← q r"m:(1->num)->A"), (← q r"p:A->bool")] NUMBER_FIELD_DEDEKIND_KUMMER_DATA) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring"), (← q r"h:A->B"), (← q r"quotient_ring (ring_of_integers k) (p:A->bool)"), (← q r"ring_coset (ring_of_integers k) (p:A->bool)"), (← q r"p:A->bool"), (← q r"x:B"), (← q r"m:(1->num)->A"), (← q r"g:(1->num)->A"), (← q r"ideal_generated (ring_of_integers l)
       (poly_extend (ring_of_integers k,l) (h:A->B) (\v:1. x) g INSERT
        IMAGE h p)")] DEDEKIND_KUMMER_FACTOR) THEN ASM_SIMP_TAC [])

  let NUMBER_FIELD_DEDEKIND_KUMMER ← prove
    r"!k:A ring l:B ring h x m p (t:K->bool) g e P.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        x IN ring_carrier l /\
        m IN ring_carrier(poly_ring (ring_of_integers k) (:1)) /\
        monic (ring_of_integers k) m /\
        poly_deg (ring_of_integers k) m = extension_degree(k,l) h /\
        poly_extend (ring_of_integers k,l) h (\v. x) m = ring_0 l /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        ring_setadd (ring_of_integers l)
          (ring_carrier(subring_generated l
             (x INSERT IMAGE h (ring_carrier(ring_of_integers k)))))
          (ideal_generated (ring_of_integers l) (IMAGE h p)) =
        ring_carrier(ring_of_integers l) /\
        FINITE t /\
        (!i. i IN t
             ==> g i IN ring_carrier(poly_ring (ring_of_integers k) (:1)) /\
                 monic (quotient_ring (ring_of_integers k) p)
                   (ring_coset (ring_of_integers k) p o g i) /\
                 ring_irreducible
                   (poly_ring (quotient_ring (ring_of_integers k) p) (:1))
                   (ring_coset (ring_of_integers k) p o g i) /\
                 ~(e i = 0)) /\
        (!i j. i IN t /\ j IN t /\
               ring_coset (ring_of_integers k) p o g i =
               ring_coset (ring_of_integers k) p o g j
               ==> i = j) /\
        ring_coset (ring_of_integers k) p o m =
        ring_product (poly_ring (quotient_ring (ring_of_integers k) p) (:1)) t
          (\i. ring_pow (poly_ring (quotient_ring (ring_of_integers k) p) (:1))
                 (ring_coset (ring_of_integers k) p o g i) (e i)) /\
        (!i. P i =
             ideal_generated (ring_of_integers l)
               (poly_extend (ring_of_integers k,l) h (\v. x) (g i) INSERT
                IMAGE h p))
        ==> ideal_generated (ring_of_integers l) (IMAGE h p) =
            ideal_product (ring_of_integers l) t
              (\i. ideal_pow (ring_of_integers l) (P i) (e i)) /\
            {Q | prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q} =
            IMAGE P t /\
            (!i j. i IN t /\ j IN t /\ P i = P j ==> i = j) /\
            (!i. i IN t
                 ==> prime_ideal (ring_of_integers l) (P i) /\
                     residue_degree (ring_of_integers k,ring_of_integers l) h
                       (P i) =
                     poly_deg (quotient_ring (ring_of_integers k) p)
                       (ring_coset (ring_of_integers k) p o g i) /\
                     ramification_index (ring_of_integers k,ring_of_integers l)
                       h (P i) = e i)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"x:B"), (← q r"m:(1->num)->A"), (← q r"p:A->bool")] NUMBER_FIELD_DEDEKIND_KUMMER_DATA) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN MATCH_MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring"), (← q r"h:A->B"), (← q r"quotient_ring (ring_of_integers k) (p:A->bool)"), (← q r"ring_coset (ring_of_integers k) (p:A->bool)"), (← q r"p:A->bool"), (← q r"x:B"), (← q r"m:(1->num)->A"), (← q r"t:K->bool"), (← q r"g:K->(1->num)->A"), (← q r"e:K->num"), (← q r"P:K->B->bool")] DEDEKIND_KUMMER) THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [])

  let DEDEKIND_KUMMER_EPIMORPHISM_Q ← prove
    r"!k:A ring a p j.
        a IN ring_carrier(ring_of_integers k) /\
        ring_setadd (ring_of_integers k) (ring_carrier(subring_generated k {a}))
          (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
        ring_carrier(ring_of_integers k) /\
        ring_ideal (ring_of_integers k) j /\ ring_of_num k p IN j
        ==> ring_epimorphism
             (poly_ring (integer_mod_ring p) (:1),
              quotient_ring (ring_of_integers k) j)
             (\g. ring_coset (ring_of_integers k) j
                    (poly_extend (integer_ring,k) (ring_of_int k) (\v. a) g)) /\
            !g. g IN ring_carrier(poly_ring integer_ring (:1))
                ==> ring_coset (ring_of_integers k) j
                      (poly_extend (integer_ring,k) (ring_of_int k) (\v. a)
                         (ring_of_int (integer_mod_ring p) o g)) =
                    ring_coset (ring_of_integers k) j
                      (poly_extend (integer_ring,k) (ring_of_int k) (\v. a) g)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"a:A"), (← q r"p:num"), (← q r"j:A->bool")] RING_EPIMORPHISM_POLY_EXTEND_QUOTIENT_RING) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN SUBGOAL_THEN (← q r"subring_generated (ring_of_integers k) {a:A} = subring_generated k {a}") SUBST1_TAC THENL [REWRITE_TAC [ring_of_integers] THEN MATCH_MP_TAC SUBRING_GENERATED_IDEMPOT_GEN THEN ASM_REWRITE_TAC [SING_SUBSET, (← GSYM ring_of_integers)], ALL_TAC] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [MATCH_MP_TAC RING_SETADD THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET] THEN MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET, RING_OF_INTEGERS_SUBRING], FIRST_X_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC LAND_CONV [(← SYM th)])) THEN MATCH_MP_TAC RING_SETADD_MONO THEN REWRITE_TAC [SUBSET_REFL] THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET]], REWRITE_TAC [RING_OF_INTEGERS] THEN STRIP_TAC] THEN SUBGOAL_THEN (← q r"!g. g IN ring_carrier(poly_ring integer_ring (:1))
        ==> ring_coset (ring_of_integers k) j
              (poly_extend (integer_ring,k) (ring_of_int k) (\v:1. a:A) g) =
            poly_extend (integer_ring,quotient_ring (ring_of_integers k) j)
              (ring_of_int (quotient_ring (ring_of_integers k) j))
              (\v. ring_coset (ring_of_integers k) j a) g") ASSUME_TAC THENL [ASM_SIMP_TAC [(← GSYM POLY_EXTEND_RING_OF_INTEGERS)], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"p:num"), (← q r"(:1)")] POLY_RING_INTEGER_MOD_RING_SUBSET) THEN REWRITE_TAC [SUBSET] THEN DISCH_TAC THEN CONJ_TAC THENL [MATCH_MP_TAC RING_EPIMORPHISM_EQ THEN EXISTS_TAC (← q r"poly_extend (integer_ring,quotient_ring (ring_of_integers k) j)
       (ring_of_int (quotient_ring (ring_of_integers k) j))
       (\v:1. ring_coset (ring_of_integers k) j (a:A))") THEN ASM_SIMP_TAC [], X_GEN_TAC (← q r"g:(1->num)->int") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_of_int (integer_mod_ring p) o g IN
      ring_carrier(poly_ring integer_ring (:1))") ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN EXISTS_TAC (← q r"integer_ring") THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT], ASM_SIMP_TAC []]])

  let DEDEKIND_KUMMER_INTEGER_DATA ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(t:A->bool) SUBSET s ==> (t SUBSET q <=> s INTER t SUBSET q)")
    let r2 ← SET_RULE (← q r"(!x. x IN s ==> (f:((1->num)->int)->A) x = g x)
      ==> IMAGE f s = IMAGE g s")
    prove
      r"!k:A ring a p m.
          number_field k /\ prime p /\ a IN ring_carrier k /\
          m IN ring_carrier(poly_ring integer_ring (:1)) /\
          monic integer_ring m /\
          poly_deg integer_ring m =
          extension_degree (subfield_generated k {ring_0 k},k) I /\
          poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m = ring_0 k /\
          ring_setadd (ring_of_integers k) (ring_carrier(subring_generated k {a}))
            (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
          ring_carrier(ring_of_integers k)
          ==> ring_homomorphism(integer_ring,ring_of_integers k)
                (ring_of_int k) /\
              field(integer_mod_ring p) /\
              FINITE(ring_carrier(integer_mod_ring p)) /\
              ring_epimorphism(integer_ring,integer_mod_ring p)
                (ring_of_int(integer_mod_ring p)) /\
              ring_kernel(integer_ring,integer_mod_ring p)
                (ring_of_int(integer_mod_ring p)) =
              ideal_generated integer_ring {&p} /\
              a IN ring_carrier(ring_of_integers k) /\
              poly_extend (integer_ring,ring_of_integers k) (ring_of_int k)
                (\v. a) m = ring_0(ring_of_integers k) /\
              ideal_generated (ring_of_integers k)
                (IMAGE (ring_of_int k) (ideal_generated integer_ring {&p})) =
              ideal_generated (ring_of_integers k) {ring_of_num k p} /\
              ~(ideal_generated (ring_of_integers k) {ring_of_num k p} =
                {ring_0(ring_of_integers k)}) /\
              ideal_norm (ring_of_integers k)
                (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
              CARD(ring_carrier(integer_mod_ring p)) EXP
              poly_deg integer_ring m /\
              ring_setadd (ring_of_integers k)
                (ring_carrier
                  (subring_generated (ring_of_integers k)
                    (a INSERT IMAGE (ring_of_int k)
                                    (ring_carrier integer_ring))))
                (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
              ring_carrier(ring_of_integers k) /\
              (!q. ring_ideal (ring_of_integers k) q
                   ==> (IMAGE (ring_of_int k)
                          (ideal_generated integer_ring {&p}) SUBSET q <=>
                        ring_of_num k p IN q)) /\
              (!g. g IN ring_carrier(poly_ring integer_ring (:1))
                   ==> poly_extend (integer_ring,ring_of_integers k)
                         (ring_of_int k) (\v. a) g =
                       poly_extend (integer_ring,k) (ring_of_int k) (\v. a) g)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_NZ)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN SUBGOAL_THEN (← q r"ring_homomorphism(integer_ring,ring_of_integers k) (ring_of_int k:int->A)") ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM, integral_element] THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"m:(1->num)->int") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!g. g IN ring_carrier(poly_ring integer_ring (:1))
          ==> poly_extend (integer_ring,ring_of_integers k) (ring_of_int k)
                (\v:1. a:A) g =
              poly_extend (integer_ring,k) (ring_of_int k) (\v. a) g") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"\v:1. (a:A)"), (← q r"g:(1->num)->int")] POLY_EXTEND_RING_OF_INTEGERS) THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_generated (ring_of_integers k)
        (IMAGE (ring_of_int k) (ideal_generated integer_ring {&p})) =
      ideal_generated (ring_of_integers k) {ring_of_num k p:A}") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"ring_of_integers k:A ring"), (← q r"ring_of_int k:int->A"), (← q r"{&p:int}")] IDEAL_GENERATED_IMAGE_IDEAL_GENERATED) THEN ASM_REWRITE_TAC [INTEGER_RING, SUBSET_UNIV, IMAGE_CLAUSES, RING_OF_INT_OF_NUM], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_of_num k p IN ring_carrier(ring_of_integers k:A ring)") ASSUME_TAC THENL [MESON_TAC [RING_OF_NUM, RING_OF_INTEGERS], ALL_TAC] THEN ASM_SIMP_TAC [FIELD_INTEGER_MOD_RING, FINITE_INTEGER_MOD_RING, RING_EPIMORPHISM_INTEGER_MOD_RING, RING_KERNEL_INTEGER_MOD_RING, CARD_INTEGER_MOD_RING] THEN REPEAT CONJ_TAC THENL [ASM_SIMP_TAC [RING_OF_INTEGERS], DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"{ring_of_num k p:A}"), (← q r"ring_of_num k p:A")] IDEAL_GENERATED_INC) THEN ASM_REWRITE_TAC [SING_SUBSET, IN_SING, RING_OF_INTEGERS] THEN REWRITE_TAC [RING_OF_NUM_EQ_0] THEN ASM_SIMP_TAC [DIVIDES_ZERO], MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"&p:int")] RING_OF_INTEGERS_IDEAL_NORM_INTEGER) THEN ASM_REWRITE_TAC [RING_OF_INT_OF_NUM, INT_ABS_NUM, NUM_OF_INT_OF_NUM, INT_OF_NUM_EQ], FIRST_X_ASSUM ((fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [(← SYM th)])) o (checkM (fun th => (do if ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); pure (is_eq z3)) then (do let z8 ← (q r"ring_carrier(ring_of_integers k:A ring)"); let z7 ← (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); liftExcept (rhs z5)); pure (z7 == z8)) else pure false)))) THEN AP_THM_TAC THEN AP_TERM_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_int k:int->A"), (← q r"integer_ring"), (← q r"ring_of_integers k:A ring"), (← q r"a:A")] IMAGE_POLY_EXTEND_1) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [(← GSYM IMAGE_POLY_EXTEND_INTEGER_RING)] THEN MATCH_MP_TAC r2 THEN ASM_SIMP_TAC [], X_GEN_TAC (← q r"q:A->bool") THEN DISCH_TAC THEN TRANS_TAC EQ_TRANS (← q r"ideal_generated (ring_of_integers k)
          (IMAGE (ring_of_int k) (ideal_generated integer_ring {&p})) SUBSET
        (q:A->bool)") THEN CONJ_TAC THENL [ASM_SIMP_TAC [IDEAL_GENERATED_MINIMAL_EQ] THEN MATCH_MP_TAC r1 THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, INTEGER_RING, IN_UNIV], ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [IDEAL_GENERATED_MINIMAL_EQ] THEN ASM SET_TAC []]])

  let DEDEKIND_KUMMER_QUOTIENT_RING_Q ← prove
    r"!k:A ring a p m.
        number_field k /\ prime p /\ a IN ring_carrier k /\
        m IN ring_carrier(poly_ring integer_ring (:1)) /\
        monic integer_ring m /\
        poly_deg integer_ring m =
        extension_degree (subfield_generated k {ring_0 k},k) I /\
        poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m = ring_0 k /\
        ring_setadd (ring_of_integers k) (ring_carrier(subring_generated k {a}))
          (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
        ring_carrier(ring_of_integers k)
        ==> quotient_ring (ring_of_integers k)
              (ideal_generated (ring_of_integers k) {ring_of_num k p})
            isomorphic_ring
            quotient_ring (poly_ring (integer_mod_ring p) (:1))
              (ideal_generated (poly_ring (integer_mod_ring p) (:1))
                 {ring_of_int (integer_mod_ring p) o m})"
    (REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP DEDEKIND_KUMMER_INTEGER_DATA)) THEN FIRST_X_ASSUM STRIP_ASSUME_TAC THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"ring_of_integers k:A ring"), (← q r"ring_of_int k:int->A"), (← q r"integer_mod_ring p"), (← q r"ring_of_int(integer_mod_ring p)"), (← q r"ideal_generated integer_ring {&p}"), (← q r"a:A"), (← q r"m:(1->num)->int")] DEDEKIND_KUMMER_QUOTIENT_RING) THEN ASM_REWRITE_TAC [] THEN SIMP_TAC [])

  let DEDEKIND_KUMMER_FACTOR_Q ← prove
    r"!k:A ring a p m g.
        number_field k /\ prime p /\ a IN ring_carrier k /\
        m IN ring_carrier(poly_ring integer_ring (:1)) /\
        monic integer_ring m /\
        poly_deg integer_ring m =
        extension_degree (subfield_generated k {ring_0 k},k) I /\
        poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m = ring_0 k /\
        ring_setadd (ring_of_integers k) (ring_carrier(subring_generated k {a}))
          (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
        ring_carrier(ring_of_integers k) /\
        ring_irreducible (poly_ring (integer_mod_ring p) (:1)) g /\
        ring_divides (poly_ring (integer_mod_ring p) (:1)) g
          (ring_of_int (integer_mod_ring p) o m)
        ==> prime_ideal (ring_of_integers k)
              (ideal_generated (ring_of_integers k)
                 {ring_of_num k p,
                  poly_extend (integer_ring,k) (ring_of_int k) (\v. a) g}) /\
            ring_of_num k p IN
              ideal_generated (ring_of_integers k)
                 {ring_of_num k p,
                  poly_extend (integer_ring,k) (ring_of_int k) (\v. a) g} /\
            residue_degree (integer_ring,ring_of_integers k) (ring_of_int k)
              (ideal_generated (ring_of_integers k)
                 {ring_of_num k p,
                  poly_extend (integer_ring,k) (ring_of_int k) (\v. a) g}) =
            poly_deg (integer_mod_ring p) g"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"p:num"), (← q r"m:(1->num)->int")] DEDEKIND_KUMMER_INTEGER_DATA) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [ring_divides]))) THEN SUBGOAL_THEN (← q r"(g:(1->num)->int) IN ring_carrier(poly_ring integer_ring (:1)) /\
    ring_of_int (integer_mod_ring p) o g = g") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [MATCH_MP_TAC (← REWRITE_RULE [SUBSET] POLY_RING_INTEGER_MOD_RING_SUBSET) THEN EXISTS_TAC (← q r"p:num") THEN ASM_REWRITE_TAC [], MATCH_MP_TAC POLY_RING_INTEGER_MOD_RING_OF_INT THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_generated (ring_of_integers k)
      {ring_of_num k p,
       poly_extend (integer_ring,k) (ring_of_int k) (\v. a) g} =
    ideal_generated (ring_of_integers k)
      (poly_extend (integer_ring,ring_of_integers k) (ring_of_int k)
         (\v:1. a:A) g INSERT
       IMAGE (ring_of_int k) (ideal_generated integer_ring {&p}))") SUBST1_TAC THENL [SUBGOAL_THEN (← q r"poly_extend (integer_ring,ring_of_integers k) (ring_of_int k)
        (\v:1. a:A) g =
      poly_extend (integer_ring,k) (ring_of_int k) (\v. a) g") SUBST1_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [INSERT_COMM] THEN MATCH_MP_TAC IDEAL_GENERATED_INSERT_EQ THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"ring_of_integers k:A ring"), (← q r"ring_of_int k:int->A"), (← q r"integer_mod_ring p"), (← q r"ring_of_int(integer_mod_ring p)"), (← q r"ideal_generated integer_ring {&p}"), (← q r"a:A"), (← q r"m:(1->num)->int"), (← q r"g:(1->num)->int"), (← q r"ideal_generated (ring_of_integers k)
      (poly_extend (integer_ring,ring_of_integers k) (ring_of_int k)
         (\v:1. a:A) g INSERT
       IMAGE (ring_of_int k) (ideal_generated integer_ring {&p}))")] DEDEKIND_KUMMER_FACTOR) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_SIMP_TAC [MAXIMAL_IMP_PRIME_IDEAL] THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"ideal_generated (ring_of_integers k)
      (poly_extend (integer_ring,ring_of_integers k) (ring_of_int k)
         (\v:1. a:A) g INSERT
       IMAGE (ring_of_int k) (ideal_generated integer_ring {&p}))")) o (checkM (fun th => (do if ← (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_forall z1)) then (do let z3 ← (do pure (Prod.snd (← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); liftExcept (dest_forall z4))))); pure (is_imp z3)) else pure false) then (do let z6 ← (do let z7 ← (do pure (Prod.snd (← (do let z8 ← (do let z9 ← (pure th); pure (concl z9)); liftExcept (dest_forall z8))))); liftExcept (rand z7)); pure (HolCore.Bool.is_iff z6)) else pure false))))) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED])

  let DEDEKIND_KUMMER_Q ← prove
    r"!k:A ring a p m (s:K->bool) g e P.
        number_field k /\ prime p /\ a IN ring_carrier k /\
        m IN ring_carrier(poly_ring integer_ring (:1)) /\
        monic integer_ring m /\
        poly_deg integer_ring m =
        extension_degree (subfield_generated k {ring_0 k},k) I /\
        poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m = ring_0 k /\
        ring_setadd (ring_of_integers k) (ring_carrier(subring_generated k {a}))
          (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
        ring_carrier(ring_of_integers k) /\
        FINITE s /\
        (!i. i IN s
             ==> g i IN ring_carrier(poly_ring (integer_mod_ring p) (:1)) /\
                 monic (integer_mod_ring p) (g i) /\
                 ring_irreducible (poly_ring (integer_mod_ring p) (:1)) (g i) /\
                 ~(e i = 0)) /\
        (!i j. i IN s /\ j IN s /\ g i = g j ==> i = j) /\
        ring_of_int (integer_mod_ring p) o m =
        ring_product (poly_ring (integer_mod_ring p) (:1)) s
          (\i. ring_pow (poly_ring (integer_mod_ring p) (:1)) (g i) (e i)) /\
        (!i. P i =
             ideal_generated (ring_of_integers k)
               {ring_of_num k p,
                poly_extend (integer_ring,k) (ring_of_int k) (\v. a) (g i)})
        ==> ideal_generated (ring_of_integers k) {ring_of_num k p} =
            ideal_product (ring_of_integers k) s
              (\i. ideal_pow (ring_of_integers k) (P i) (e i)) /\
            {q | prime_ideal (ring_of_integers k) q /\ ring_of_num k p IN q} =
            IMAGE P s /\
            (!i j. i IN s /\ j IN s /\ P i = P j ==> i = j) /\
            (!i. i IN s
                 ==> prime_ideal (ring_of_integers k) (P i) /\
                     residue_degree (integer_ring,ring_of_integers k)
                       (ring_of_int k) (P i) =
                     poly_deg (integer_mod_ring p) (g i) /\
                     ramification_index (integer_ring,ring_of_integers k)
                       (ring_of_int k) (P i) = e i)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"p:num"), (← q r"m:(1->num)->int")] DEDEKIND_KUMMER_INTEGER_DATA) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN SUBGOAL_THEN (← q r"!i. i IN s
        ==> (g:K->(1->num)->int) i IN
            ring_carrier(poly_ring integer_ring (:1)) /\
            ring_of_int (integer_mod_ring p) o g i = g i") ASSUME_TAC THENL [REPEAT STRIP_TAC THENL [MATCH_MP_TAC (← REWRITE_RULE [SUBSET] POLY_RING_INTEGER_MOD_RING_SUBSET) THEN EXISTS_TAC (← q r"p:num") THEN ASM_SIMP_TAC [], MATCH_MP_TAC POLY_RING_INTEGER_MOD_RING_OF_INT THEN ASM_SIMP_TAC []], ALL_TAC] THEN FIRST_X_ASSUM ((fun pdef => tactic_of do pure (SUBGOAL_THEN (← q r"!i. i IN s
          ==> (P:K->A->bool) i =
              ideal_generated (ring_of_integers k)
                (poly_extend (integer_ring,ring_of_integers k) (ring_of_int k)
                   (\v:1. a) ((g:K->(1->num)->int) i) INSERT
                 IMAGE (ring_of_int k) (ideal_generated integer_ring {&p}))") ASSUME_TAC THENL [X_GEN_TAC (← q r"i:K") THEN DISCH_TAC THEN REWRITE_TAC [pdef] THEN SUBGOAL_THEN (← q r"poly_extend (integer_ring,ring_of_integers k) (ring_of_int k)
          (\v:1. a:A) ((g:K->(1->num)->int) i) =
        poly_extend (integer_ring,k) (ring_of_int k) (\v. a) (g i)") SUBST1_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [INSERT_COMM] THEN MATCH_MP_TAC IDEAL_GENERATED_INSERT_EQ THEN ASM_REWRITE_TAC [], ALL_TAC])) o (checkM (fun th => (do if ← (do if ← (do let z14 ← (do let z15 ← (pure th); pure (concl z15)); pure (is_forall z14)) then (do let z16 ← (do pure (Prod.snd (← (do let z17 ← (do let z18 ← (pure th); pure (concl z18)); liftExcept (dest_forall z17))))); pure (is_eq z16)) else pure false) then (do let z23 ← (q r"(P:K->A->bool) i"); let z22 ← (do let z19 ← (do pure (Prod.snd (← (do let z20 ← (do let z21 ← (pure th); pure (concl z21)); liftExcept (dest_forall z20))))); liftExcept (lhs z19)); pure (z22 == z23)) else pure false)))) THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"ring_of_integers k:A ring"), (← q r"ring_of_int k:int->A"), (← q r"integer_mod_ring p"), (← q r"ring_of_int(integer_mod_ring p)"), (← q r"ideal_generated integer_ring {&p}"), (← q r"a:A"), (← q r"m:(1->num)->int"), (← q r"s:K->bool"), (← q r"g:K->(1->num)->int"), (← q r"e:K->num"), (← q r"P:K->A->bool")] DEDEKIND_KUMMER) THEN ANTS_TAC THENL [ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MATCH_MP_TAC o (checkM (fun th => (do if ← (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_forall z1)) then (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); canM (fun z5 => (do let z6 ← (pure z5); find_termM (fun z7 => (do let z9 ← (pure z7); let z8 ← (q r"(g:K->(1->num)->int) i"); pure (z8 == z9))) z6)) z3) else pure false) then (do let z10 ← (do let z11 ← (do pure (Prod.snd (← (do let z12 ← (do let z13 ← (pure th); pure (concl z13)); pure (strip_forall z12))))); liftExcept (rand z11)); pure (is_eq z10)) else pure false)))) THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"ring_of_int (integer_mod_ring p) o (g:K->(1->num)->int) i =
                 ring_of_int (integer_mod_ring p) o g j") THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"{Q | prime_ideal (ring_of_integers k) Q /\
         IMAGE (ring_of_int k) (ideal_generated integer_ring {&p}) SUBSET Q} =
    {q | prime_ideal (ring_of_integers k) q /\ ring_of_num k p IN (q:A->bool)}") SUBST1_TAC THENL [GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"q:A->bool") THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [PRIME_IMP_RING_IDEAL], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [])

  let DEDEKIND_KUMMER_LINEAR_IDEAL ← prove
    r"!k:A ring a p y.
        number_field k /\ prime p /\ a IN ring_carrier(ring_of_integers k) /\
        ring_setadd (ring_of_integers k) (ring_carrier(subring_generated k {a}))
          (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
        ring_carrier(ring_of_integers k)
        ==> ideal_generated (ring_of_integers k)
              {ring_of_num k p,
               poly_extend (integer_ring,k) (ring_of_int k) (\v. a)
                 (poly_sub (integer_mod_ring p)
                    (poly_var (integer_mod_ring p) one)
                    (poly_const (integer_mod_ring p)
                       (ring_of_int (integer_mod_ring p) y)))} =
            ideal_generated (ring_of_integers k)
              {ring_of_num k p, ring_sub k a (ring_of_int k y)}"
    (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"g = poly_sub integer_ring (poly_var integer_ring one)
                    (poly_const integer_ring y)") THEN SUBGOAL_THEN (← q r"g IN ring_carrier(poly_ring integer_ring (:1))") ASSUME_TAC THENL [EXPAND_TAC "g" THEN REWRITE_TAC [(← GSYM (← ISPECL [(← q r"integer_ring"), (← q r"(:1)")] (← (do let z3 ← (pure (CONJUNCTS POLY_RING_CLAUSES)); let z4 ← (pure 5); liftExcept (el z4 z3)))))] THEN SIMP_TAC [RING_SUB, POLY_VAR_UNIV, POLY_CONST, INTEGER_RING, IN_UNIV], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_of_int (integer_mod_ring p) o g =
    poly_sub (integer_mod_ring p) (poly_var (integer_mod_ring p) one)
      (poly_const (integer_mod_ring p) (ring_of_int (integer_mod_ring p) y))") (SUBST1_TAC o SYM) THENL [EXPAND_TAC "g" THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"integer_mod_ring p"), (← q r"ring_of_int (integer_mod_ring p)"), (← q r"(:1)")] RING_HOMOMORPHISM_POLY_RINGS) THEN REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN DISCH_THEN (MP_TAC o (BETA_RULE o (MATCH_MP RING_HOMOMORPHISM_SUB))) THEN REWRITE_TAC [(← (do let z1 ← (pure (CONJUNCTS POLY_RING_CLAUSES)); let z2 ← (pure 5); liftExcept (el z2 z1)))] THEN DISCH_THEN (fun th => SIMP_TAC [th, POLY_VAR_UNIV, POLY_CONST, INTEGER_RING, IN_UNIV]) THEN SIMP_TAC [(← ISPECL [(← q r"integer_ring"), (← q r"integer_mod_ring p"), (← q r"ring_of_int (integer_mod_ring p)")] POLY_COMPOSE_HOMOMORPHISM_VAR), (← ISPECL [(← q r"integer_ring"), (← q r"integer_mod_ring p"), (← q r"ring_of_int (integer_mod_ring p)")] POLY_COMPOSE_HOMOMORPHISM_CONST), RING_HOMOMORPHISM_INTEGER_RING_OF_INT, INTEGER_RING, IN_UNIV], ALL_TAC] THEN SUBGOAL_THEN (← q r"poly_extend (integer_ring,k) (ring_of_int k) (\v:1. a) g =
    ring_sub k a (ring_of_int k y:A)") ASSUME_TAC THENL [EXPAND_TAC "g" THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SIMP_TAC [POLY_EXTEND_SUB, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_CONST, RING_HOMOMORPHISM_INTEGER_RING_OF_INT, INTEGER_RING, IN_UNIV] THEN ASM_SIMP_TAC [POLY_EXTEND_VAR, POLY_EXTEND_CONST, INTEGER_RING, IN_UNIV, RING_HOMOMORPHISM_INTEGER_RING_OF_INT], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_of_int (integer_mod_ring p) o g IN
    ring_carrier(poly_ring integer_ring (:1))") ASSUME_TAC THENL [MATCH_MP_TAC (← REWRITE_RULE [SUBSET] POLY_RING_INTEGER_MOD_RING_SUBSET) THEN EXISTS_TAC (← q r"p:num") THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"integer_mod_ring p"), (← q r"ring_of_int (integer_mod_ring p)"), (← q r"(:1)")] RING_HOMOMORPHISM_POLY_RINGS) THEN REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, ring_homomorphism, SUBSET, FORALL_IN_IMAGE] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"g:(1->num)->int")) o CONJUNCT1)) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"\v:1. (a:A)"), (← q r"ring_of_int (integer_mod_ring p) o (g:(1->num)->int)")] POLY_EXTEND_RING_OF_INTEGERS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT2) THEN SUBGOAL_THEN (← q r"ring_sub k a (ring_of_int k y) IN ring_carrier(ring_of_integers k) /\
    ring_of_num k p IN ring_carrier(ring_of_integers (k:A ring))") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"a:A"), (← q r"ring_of_int (ring_of_integers k) y:A")] RING_SUB) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:num")] RING_OF_NUM) THEN REWRITE_TAC [RING_OF_INTEGERS, RING_OF_INT] THEN ASM_SIMP_TAC [], ALL_TAC] THEN MATCH_MP_TAC IDEAL_GENERATED_PAIR_EQ THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"j:A->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"p:num"), (← q r"j:A->bool")] DEDEKIND_KUMMER_EPIMORPHISM_Q) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"g:(1->num)->int")) o CONJUNCT2)) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"j:A->bool"), (← q r"ring_sub k a (ring_of_int k y):A")] RING_COSET_EQ_IDEAL) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"j:A->bool"), (← q r"poly_extend (integer_ring,k) (ring_of_int k) (\v:1. a)
                    (ring_of_int (integer_mod_ring p) o g):A")] RING_COSET_EQ_IDEAL) THEN ASM_REWRITE_TAC [] THEN MESON_TAC [])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_DEDEKIND_KUMMER_FACTOR, NUMBER_FIELD_DEDEKIND_KUMMER,
           DEDEKIND_KUMMER_EPIMORPHISM_Q, DEDEKIND_KUMMER_INTEGER_DATA,
           DEDEKIND_KUMMER_QUOTIENT_RING_Q, DEDEKIND_KUMMER_FACTOR_Q, DEDEKIND_KUMMER_Q,
           DEDEKIND_KUMMER_LINEAR_IDEAL }
  -- @@RETURN END

end HolANT.DedekindKummer
