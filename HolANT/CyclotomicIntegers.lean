/- ========================================================================= -/
/- ANT: The ring of integers of a cyclotomic field                         -/
/- ========================================================================= -/
/- File: HolANT/CyclotomicIntegers.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/cyclotomic_integers.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antcyclotomicintegersdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/products.ml, Library/integer.ml, Library/isum.ml, Library/multiplicative.ml, Library/primitive.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/discriminant.ml, ANT/prime_split.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/classgroup.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/relative_degree.ml, ANT/nf_valuation.ml, ANT/integrality.ml, ANT/dedekind_kummer.ml, Library/frag.ml, Library/grouptheory.ml, Library/symmetric_group.ml, Library/galois.ml, Library/ring_groups.ml, Library/finite_fields.ml, ANT/cyclotomic_poly.ml, ANT/power_basis.ml, ANT/cyclotomic_field.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.CyclotomicIntegers fills them).

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
import HolLibrary.Integer
import HolLibrary.Isum
import HolLibrary.Multiplicative
import HolLibrary.Primitive
import HolANT.Algmisc
import HolANT.Integral
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolANT.IdealArith
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.IdealNorm
import HolANT.RingOfIntegers
import HolANT.NormIndex
import HolANT.Discriminant
import HolANT.PrimeSplit
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.Classgroup
import HolANT.TraceForm
import HolANT.RelativeSplit
import HolANT.RelativeDegree
import HolANT.NfValuation
import HolANT.Integrality
import HolANT.DedekindKummer
import HolLibrary.Frag
import HolLibrary.GroupTheory
import HolLibrary.SymmetricGroup
import HolLibrary.Galois
import HolLibrary.RingGroups
import HolLibrary.FiniteFields
import HolANT.CyclotomicPoly
import HolANT.PowerBasis
import HolANT.CyclotomicField

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.Algmisc
open HolANT.Integral
open HolANT.Zlattice
open HolANT.Numfield
open HolANT.IdealArith
open HolANT.Dedekind
open HolANT.DedekindStruct
open HolANT.IdealNorm
open HolANT.RingOfIntegers
open HolANT.NormIndex
open HolANT.Discriminant
open HolANT.PrimeSplit
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.Classgroup
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.RelativeDegree
open HolANT.NfValuation
open HolANT.Integrality
open HolANT.DedekindKummer
open HolANT.CyclotomicPoly
open HolANT.PowerBasis
open HolANT.CyclotomicField

namespace HolANT.CyclotomicIntegers

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD_CLAUSES ADD_EQ_0 ADD_SUB ALGEBRA_TRACE_NORM_IN_CARRIER
   ALGEBRA_TRACE_PRODUCT_BASIS ARITH ARITH_EQ CONG_SOLVE COPRIME_0 COPRIME_1
   COPRIME_BEZOUT_STRONG COPRIME_LEXP COPRIME_PRIMEPOW COPRIME_SYM
   CYCLOTOMIC_FIELD_DEGREE CYCLOTOMIC_FIELD_FREE_BASIS CYCLOTOMIC_POLY_DEG
   CYCLOTOMIC_POLY_EVAL_0 CYCLOTOMIC_POLY_EVAL_1_PRIME_POWER
   CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE CYCLOTOMIC_POLY_IN_CARRIER
   CYCLOTOMIC_POLY_MINIMAL_POLYNOMIAL CYCLOTOMIC_POLY_MONIC
   CYCLOTOMIC_POLY_PRODUCT CYCLOTOMIC_POLY_ROOT CYCLOTOMIC_POLY_SPLITS
   CYCLOTOMIC_POLY_SQUAREFREE DE_MORGAN_THM DISJOINT DIVIDES_0 DIVIDES_LMUL
   DIVIDES_ONE DIVIDES_PRIMEPOW DIVIDES_PRIME_PRIME DIVIDES_REFL DIVIDES_RMUL
   DIVIDES_ZERO DIV_MULT DIV_UNIQ EQ_EXP EVEN EVEN_ADD EVEN_EXISTS EVEN_MULT
   EVEN_OR_ODD EVEN_SUB EXISTS_IN_IMAGE EXP EXP_1 EXP_ADD EXP_EQ_0 EXP_EQ_1
   EXP_MULT EXP_ONE EXTENSION EXTENSION_LINCOMB_SUM
   FIELD_EXTENSION_SUBFIELD_GENERATED FIELD_IMP_INTEGRAL_DOMAIN
   FIELD_INTEGER_MOD_RING FIELD_MUL_LINV FIELD_NONTRIVIAL
   FIELD_SUBFIELD_GENERATED FINITE_DIVISORS FINITE_INDUCT_STRONG
   FINITE_NUMSEG_LT FINITE_SING FINITE_SPECIAL_DIVISORS FINITE_SUBSET
   FORALL_IN_GSPEC FORALL_IN_IMAGE FORALL_IN_INSERT FREE_BASIS_INDEPENDENT
   FREE_BASIS_INTEGER_RING_SUBRING_GENERATED
   FREE_BASIS_PRIME_SUBFIELD_DENOMINATOR FREE_BASIS_SPANNING_DEGREE FUN_EQ_THM
   IMAGE_POLY_EXTEND_INTEGER_RING IMP_CONJ IMP_IMP INDEX_DECOMPOSITION
   INDEX_DECOMPOSITION_PRIME INTEGER_MOD_RING_CHAR INTEGER_MOD_RING_CLAUSES
   INTEGER_MOD_RING_OF_INT INTEGER_RING INTEGER_RING_DIVIDES INTEGER_RING_OF_NUM
   INTEGRAL_DOMAIN_MUL_LCANCEL INTEGRAL_DOMAIN_POW_EQ_0
   INTEGRAL_DOMAIN_SUBRING_GENERATED INT_ABS_NUM INT_ENTIRE INT_EQ_MUL_RCANCEL
   INT_LE_SQUARE INT_MUL_ASSOC INT_OF_NUM_EQ INT_OF_NUM_MUL INT_OF_NUM_OF_INT
   INT_OF_NUM_POW INT_POW_1 INT_POW_ADD INT_POW_MUL INT_POW_NEG INT_POW_ONE
   INT_POW_POW INT_REM_EQ_0 INT_REM_EQ_SELF IN_ELIM_THM IN_IMAGE IN_INSERT
   IN_INTEGER_MOD_RING_CARRIER IN_INTER IN_POLY_RING_CARRIER : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (IN_RING_POLYNOMIAL_CARRIER_COMPOSE IN_SING IN_SUBRING_0 IN_SUBRING_1
   IN_SUBRING_ADD IN_SUBRING_INT IN_SUBRING_MUL IN_SUBRING_NEG IN_SUBRING_NUM
   IN_SUBRING_POW IN_SUBRING_SUB IN_UNION IN_UNIV I_O_ID I_THM LEFT_ADD_DISTRIB
   LEFT_IMP_EXISTS_THM LE_1 LE_EXP LE_REFL LE_TRANS LT_MULT_LCANCEL
   LT_MULT_RCANCEL MULT_AC MULT_ASSOC MULT_CLAUSES MULT_EQ_0 MULT_EXP MULT_SYM
   NOT_IN_EMPTY NOT_ODD NPRODUCT_CLAUSES NPRODUCT_DELETE NPRODUCT_EQ
   NPRODUCT_SING NPRODUCT_UNION NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD
   NUMBER_FIELD_DISCRIMINANT_NONZERO NUMBER_FIELD_DISCRIMINANT_POWER_BASIS
   NUMBER_FIELD_IMP_FIELD NUMBER_FIELD_INTEGER_MINIMAL_POLYNOMIAL_DIVIDES
   NUMBER_FIELD_NORM_MUL NUMBER_FIELD_NORM_RATIONAL
   NUMBER_FIELD_NORM_SUB_MINIMAL_POLYNOMIAL NUMBER_FIELD_NORM_TOWER
   NUMBER_FIELD_SUBFIELD_GENERATED NUMBER_FIELD_TOWER_LAW ODD_EXISTS ODD_PHI_EQ
   PHI_1 PHI_2 PHI_ALT PHI_EQ_0 PHI_EXPAND PHI_MULTIPLICATIVE PHI_PRIME
   PHI_PRIMEPOW_ALT PID_IMP_UFD PID_POLY_RING POLY_0 POLY_CONST_DIVIDES_COEFFS
   POLY_DERIV_1 POLY_DERIV_MUL POLY_DERIV_SUB POLY_DERIV_VAR_POW POLY_EVAL
   POLY_EVAL_0 POLY_EVAL_1 POLY_EVAL_ADD POLY_EVAL_CONST
   POLY_EVAL_HOMOMORPHIC_IMAGE POLY_EVAL_MUL POLY_EVAL_POW
   POLY_EVAL_RING_PRODUCT POLY_EVAL_SUB POLY_EVAL_VAR POLY_EXTEND
   POLY_EXTEND_EVALUATE POLY_RING_CLAUSES POLY_RING_INTEGER_MOD_RING_SUBSET
   PRIME_1 PRIME_COPRIME_EQ PRIME_DIVEXP PRIME_DIVPROD_EQ PRIME_FACTOR
   PRIME_GE_2 PRIME_IMP_NZ PRIME_SUBFIELD_SUBFIELD_GENERATED RIGHT_ADD_DISTRIB
   RINGS_EQ RING_0 RING_1 RING_ADD RING_ADD_LZERO RING_ADD_RZERO
   RING_CARRIER_SUBFIELD_GENERATED_SUBSET RING_CARRIER_SUBRING_GENERATED_SUBSET
   RING_CHAR_POLY_RING RING_DET_EQ RING_DET_KRONECKER_MOD_DIV
   RING_DIVIDES_HOMOMORPHIC_IMAGE RING_DIVIDES_PRODUCTS RING_DIVIDES_SUB_POW
   RING_HOMOMORPHISM RING_HOMOMORPHISM_ADD RING_HOMOMORPHISM_INTEGER_RING_OF_INT
   RING_HOMOMORPHISM_MUL RING_HOMOMORPHISM_POLY_EXTEND
   RING_HOMOMORPHISM_POLY_RINGS RING_HOMOMORPHISM_POW
   RING_HOMOMORPHISM_RING_OF_NUM RING_HOMOMORPHISM_SUB
   RING_HOMOMORPHISM_SUBFIELD_INCLUSION : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms3 where
  (RING_INV RING_INV_IN_SUBFIELD_GENERATED RING_MUL RING_MUL_ASSOC
   RING_MUL_IN_SUBFIELD_GENERATED RING_MUL_LID RING_MUL_LZERO RING_MUL_POW
   RING_MUL_RID RING_MUL_RZERO RING_MUL_SYM RING_NEG RING_OF_INT
   RING_OF_INTEGERS RING_OF_INTEGERS_CARRIER RING_OF_INTEGERS_DISCRIMINANT
   RING_OF_INTEGERS_FREE_BASIS_FIELD RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE
   RING_OF_INTEGERS_SUBRING RING_OF_INTEGERS_SUBSET RING_OF_INT_0 RING_OF_INT_1
   RING_OF_INT_ADD RING_OF_INT_EQ RING_OF_INT_EQ_0_CHAR_0
   RING_OF_INT_IN_SUBFIELD_GENERATED RING_OF_INT_MUL RING_OF_INT_NEG
   RING_OF_INT_OF_NUM RING_OF_INT_POW RING_OF_INT_SUBFIELD_GENERATED RING_OF_NUM
   RING_OF_NUM_1 RING_OF_NUM_EQ_0 RING_OF_NUM_EXP RING_OF_NUM_MUL
   RING_OF_NUM_POLY_RING RING_OF_NUM_SUBFIELD_GENERATED
   RING_OF_NUM_SUBRING_GENERATED RING_ORDER_1 RING_ORDER_POW
   RING_ORDER_SUBFIELD_GENERATED RING_ORDER_UNIQUE RING_POLYNOMIAL
   RING_POLYNOMIAL_0 RING_POLYNOMIAL_1 RING_POLYNOMIAL_CONST
   RING_POLYNOMIAL_IMP_POWERSERIES RING_POLYNOMIAL_MUL
   RING_POLYNOMIAL_POLY_DERIV RING_POLYNOMIAL_POW RING_POLYNOMIAL_SUB
   RING_POLYNOMIAL_VAR RING_POW RING_POW_1 RING_POW_ADD RING_POW_EQ_1
   RING_POW_EQ_GEN RING_POW_IN_SUBFIELD_GENERATED RING_POW_MUL RING_POW_ONE
   RING_POW_POW RING_POW_SUBFIELD_GENERATED RING_POW_SUBRING_GENERATED
   RING_PRODUCT_CLAUSES RING_PRODUCT_CONST RING_PRODUCT_EQ
   RING_SQUAREFREE_DIVPOW RING_SUB RING_SUB_EQ_0 RING_SUB_REFL RING_SUB_RZERO
   RING_SUB_SUBFIELD_GENERATED RING_SUB_SUBRING_GENERATED RING_SUM RING_SUM_EQ
   RING_SUM_MUL_MOD_DIV SING_SUBSET SKOLEM_THM SUBFIELD_GENERATED
   SUBFIELD_GENERATED_IDEMPOT SUBFIELD_GENERATED_INC
   SUBFIELD_GENERATED_SUBSET_CARRIER SUBRING_GENERATED
   SUBRING_GENERATED_BY_SUBRING_GENERATED SUBRING_GENERATED_INC
   SUBRING_GENERATED_INT_LINCOMB SUBRING_GENERATED_MINIMAL
   SUBRING_GENERATED_SUBFIELD_GENERATED SUBRING_SUBRING_GENERATED SUBSET
   SUBSET_ANTISYM SUC_SUB1 basis_discriminant divides field_extension free_basis
   integral_element num_CASES num_WF num_coprime number_field o_THM poly_deriv
   poly_eval ring_associates ring_divides ring_polynomial ring_pow
   ring_powerseries subring_of : thm)
  deriving Inhabited

/-- What cyclotomic_integers.ml uses from Session besides theorems. -/
structure CyclotomicIntegersDeps where
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
  GROUP_RULE : term → ExceptT String IO thm  -- grouptheory.ml's GROUP_RULE
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
  NUMBER_TAC : tactic
  NUM_RING : ioconv
  core1 : CoreThms1
  core2 : CoreThms2
  core3 : CoreThms3

/-- RingTheory's `wPart` (copied verbatim).  `W(MP_TAC o PART_MATCH f th o g
    o snd)`: match `th`'s part `f` against the part `g` of the goal, and
    MP_TAC the instance. -/
def wPart [HolBase] (g : term → Except String term) (f : term → Except String term)
    (th : thm) : tactic := fun gl =>
  ExceptT.run do
    let t ← liftExcept (g gl.2)
    ExceptT.mk (MP_TAC (← PART_MATCH f th t) gl)



/- ---------------------------------------------------------------------- -/
/- cyclotomic_integers.ml phrases from line 104 to 648                    -/
/- ---------------------------------------------------------------------- -/

structure CyclotomicIntegers01 where
  -- @@FIELDS
  CYCLOTOMIC_POLY_INTEGER_ROOT : thm
  SUBRING_GENERATED_ROOT_OF_UNITY_LINCOMB : thm
  CYCLOTOMIC_POLY_DIVIDES_INTEGER_POLY : thm
  POLY_RING_INTEGER_MOD_RING_DIVIDES_LIFT : thm
  SUBRING_GENERATED_ROOT_OF_UNITY_REDUCED : thm
  SUBRING_GENERATED_ROOT_OF_UNITY_DENOMINATOR : thm
  SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL_COPRIME : thm
  SUBRING_GENERATED_ROOT_OF_UNITY_RADICAL : thm
  RING_ASSOCIATES_PRIME_POWER_ORDER : thm
  SUBRING_GENERATED_POW_DECOMPOSE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupCyclotomicIntegers01 [HolBase] (D : CyclotomicIntegersDeps) :
    ExceptT String IO CyclotomicIntegers01 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INTEGER_RULE, MESON,
        MESON_TAC, NUMBER_RULE, NUM_RING, RING_RULE, SET_TAC, TAUT, .. } := D
  let { ARITH_EQ, CONG_SOLVE, COPRIME_0, COPRIME_BEZOUT_STRONG, COPRIME_SYM,
        CYCLOTOMIC_FIELD_FREE_BASIS, CYCLOTOMIC_POLY_DEG,
        CYCLOTOMIC_POLY_EVAL_1_PRIME_POWER, CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE,
        CYCLOTOMIC_POLY_IN_CARRIER, CYCLOTOMIC_POLY_MINIMAL_POLYNOMIAL,
        CYCLOTOMIC_POLY_MONIC, CYCLOTOMIC_POLY_ROOT, CYCLOTOMIC_POLY_SPLITS,
        CYCLOTOMIC_POLY_SQUAREFREE, DIVIDES_REFL, DIVIDES_ZERO, EXISTS_IN_IMAGE, EXP_1,
        EXP_ADD, EXP_EQ_0, FIELD_EXTENSION_SUBFIELD_GENERATED,
        FIELD_IMP_INTEGRAL_DOMAIN, FIELD_INTEGER_MOD_RING, FIELD_MUL_LINV,
        FIELD_NONTRIVIAL, FIELD_SUBFIELD_GENERATED, FINITE_NUMSEG_LT, FINITE_SUBSET,
        FORALL_IN_IMAGE, FUN_EQ_THM, IMAGE_POLY_EXTEND_INTEGER_RING, IMP_CONJ, IMP_IMP,
        INDEX_DECOMPOSITION, INTEGER_MOD_RING_CHAR, INTEGER_MOD_RING_CLAUSES,
        INTEGER_MOD_RING_OF_INT, INTEGER_RING, INTEGER_RING_DIVIDES,
        INTEGER_RING_OF_NUM, INTEGRAL_DOMAIN_MUL_LCANCEL, INT_ABS_NUM, INT_ENTIRE,
        INT_LE_SQUARE, INT_OF_NUM_EQ, INT_OF_NUM_OF_INT, INT_REM_EQ_0, INT_REM_EQ_SELF,
        IN_ELIM_THM, IN_IMAGE, IN_INTEGER_MOD_RING_CARRIER, IN_POLY_RING_CARRIER, .. } := D.core1
  let { IN_RING_POLYNOMIAL_CARRIER_COMPOSE, IN_SING, IN_SUBRING_0, IN_SUBRING_1,
        IN_SUBRING_ADD, IN_SUBRING_INT, IN_SUBRING_MUL, IN_SUBRING_NEG, IN_SUBRING_NUM,
        IN_SUBRING_POW, IN_SUBRING_SUB, IN_UNIV, I_THM, LEFT_IMP_EXISTS_THM, LE_1,
        LE_EXP, MULT_AC, MULT_CLAUSES, MULT_EXP, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_INTEGER_MINIMAL_POLYNOMIAL_DIVIDES,
        NUMBER_FIELD_SUBFIELD_GENERATED, PHI_ALT, PID_IMP_UFD, PID_POLY_RING, POLY_0,
        POLY_CONST_DIVIDES_COEFFS, POLY_EVAL_CONST, POLY_EVAL_RING_PRODUCT,
        POLY_EVAL_SUB, POLY_EVAL_VAR, POLY_EXTEND, POLY_EXTEND_EVALUATE,
        POLY_RING_CLAUSES, POLY_RING_INTEGER_MOD_RING_SUBSET, PRIME_1,
        PRIME_COPRIME_EQ, PRIME_GE_2, PRIME_IMP_NZ, RING_0, RING_1, RING_ADD,
        RING_ADD_LZERO, RING_ADD_RZERO, RING_CARRIER_SUBFIELD_GENERATED_SUBSET,
        RING_CARRIER_SUBRING_GENERATED_SUBSET, RING_CHAR_POLY_RING,
        RING_DIVIDES_HOMOMORPHIC_IMAGE, RING_DIVIDES_PRODUCTS, RING_DIVIDES_SUB_POW,
        RING_HOMOMORPHISM, RING_HOMOMORPHISM_ADD,
        RING_HOMOMORPHISM_INTEGER_RING_OF_INT, RING_HOMOMORPHISM_MUL,
        RING_HOMOMORPHISM_POLY_EXTEND, RING_HOMOMORPHISM_POLY_RINGS,
        RING_HOMOMORPHISM_POW, RING_HOMOMORPHISM_RING_OF_NUM, RING_HOMOMORPHISM_SUB, .. } := D.core2
  let { RING_INV, RING_INV_IN_SUBFIELD_GENERATED, RING_MUL, RING_MUL_ASSOC,
        RING_MUL_IN_SUBFIELD_GENERATED, RING_MUL_LID, RING_MUL_LZERO, RING_MUL_POW,
        RING_MUL_RID, RING_MUL_RZERO, RING_MUL_SYM, RING_OF_INT, RING_OF_INTEGERS,
        RING_OF_INTEGERS_CARRIER, RING_OF_INTEGERS_DISCRIMINANT,
        RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE, RING_OF_INTEGERS_SUBSET, RING_OF_INT_0,
        RING_OF_INT_1, RING_OF_INT_ADD, RING_OF_INT_MUL, RING_OF_INT_OF_NUM,
        RING_OF_INT_SUBFIELD_GENERATED, RING_OF_NUM, RING_OF_NUM_EQ_0, RING_OF_NUM_EXP,
        RING_OF_NUM_MUL, RING_OF_NUM_POLY_RING, RING_OF_NUM_SUBFIELD_GENERATED,
        RING_ORDER_SUBFIELD_GENERATED, RING_POLYNOMIAL, RING_POLYNOMIAL_CONST,
        RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_VAR, RING_POW, RING_POW_1, RING_POW_ADD,
        RING_POW_EQ_GEN, RING_POW_IN_SUBFIELD_GENERATED, RING_POW_MUL, RING_POW_ONE,
        RING_POW_POW, RING_PRODUCT_CONST, RING_PRODUCT_EQ, RING_SQUAREFREE_DIVPOW,
        RING_SUB, RING_SUB_REFL, RING_SUB_RZERO, SING_SUBSET, SUBFIELD_GENERATED,
        SUBFIELD_GENERATED_IDEMPOT, SUBFIELD_GENERATED_INC, SUBRING_GENERATED_INC,
        SUBRING_GENERATED_INT_LINCOMB, SUBRING_GENERATED_MINIMAL,
        SUBRING_GENERATED_SUBFIELD_GENERATED, SUBRING_SUBRING_GENERATED, SUBSET,
        SUC_SUB1, field_extension, integral_element, num_CASES, num_coprime,
        number_field, o_THM, poly_eval, ring_associates, ring_divides, ring_polynomial,
        ring_powerseries, subring_of, .. } := D.core3
  -- @@SCOPE END

  let CYCLOTOMIC_POLY_INTEGER_ROOT ← prove
    r"!k:A ring w n.
        integral_domain k /\ w IN ring_carrier k /\
        ring_order k w = n /\ ~(n = 0)
        ==> poly_extend (integer_ring,k) (ring_of_int k) (\v. w)
              (cyclotomic_poly integer_ring n) = ring_0 k"
    (REPEAT STRIP_TAC THEN SIMP_TAC [POLY_EXTEND_EVALUATE, RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN REWRITE_TAC [(← GSYM poly_eval)] THEN REWRITE_TAC [(← MATCH_MP CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE (← ISPEC (← q r"k:A ring") RING_HOMOMORPHISM_INTEGER_RING_OF_INT))] THEN MATCH_MP_TAC CYCLOTOMIC_POLY_ROOT THEN ASM_REWRITE_TAC [])

  let SUBRING_GENERATED_ROOT_OF_UNITY_LINCOMB ← prove
    r"!k:A ring w n.
        integral_domain k /\ w IN ring_carrier k /\
        ring_order k w = n /\ ~(n = 0)
        ==> ring_carrier(subring_generated k {w}) =
            {ring_sum k {i | i < phi n}
               (\i. ring_mul k (ring_of_int k (c i)) (ring_pow k w i)) |
             c IN (:num->int)}"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"w:A"), (← q r"cyclotomic_poly integer_ring n")] SUBRING_GENERATED_INT_LINCOMB) THEN ASM_SIMP_TAC [CYCLOTOMIC_POLY_IN_CARRIER, CYCLOTOMIC_POLY_MONIC, CYCLOTOMIC_POLY_DEG, CYCLOTOMIC_POLY_INTEGER_ROOT] THEN REWRITE_TAC [INTEGER_RING, INT_OF_NUM_EQ, ARITH_EQ])

  let CYCLOTOMIC_POLY_DIVIDES_INTEGER_POLY ← prove
    r"!k:A ring w n q.
        number_field k /\ w IN ring_carrier k /\
        ring_order k w = n /\ ~(n = 0) /\
        q IN ring_carrier(poly_ring integer_ring (:1))
        ==> (ring_divides (poly_ring integer_ring (:1))
               (cyclotomic_poly integer_ring n) q <=>
             poly_extend (integer_ring,k) (ring_of_int k) (\v. w) q =
             ring_0 k)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"w:A"), (← q r"n:num")] CYCLOTOMIC_POLY_INTEGER_ROOT) THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN] THEN DISCH_TAC THEN EQ_TAC THENL [REWRITE_TAC [ring_divides] THEN DISCH_THEN (fun z1 => tactic_of do pure (X_CHOOSE_THEN (← q r"d:(1->num)->int") STRIP_ASSUME_TAC (← (do let z2 ← (pure (CONJUNCTS z1)); liftExcept (last z2))))) THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"k:A ring"), (← q r"(:1)"), (← q r"ring_of_int k:int->A"), (← q r"\v:1. (w:A)")] RING_HOMOMORPHISM_POLY_EXTEND) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN DISCH_THEN (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL th), CYCLOTOMIC_POLY_IN_CARRIER])) THEN MATCH_MP_TAC RING_MUL_LZERO THEN REWRITE_TAC [POLY_EXTEND], DISCH_TAC THEN MATCH_MP_TAC NUMBER_FIELD_INTEGER_MINIMAL_POLYNOMIAL_DIVIDES THEN MAP_EVERY EXISTS_TAC [(← q r"k:A ring"), (← q r"w:A")] THEN ASM_SIMP_TAC [CYCLOTOMIC_POLY_IN_CARRIER, CYCLOTOMIC_POLY_MONIC, CYCLOTOMIC_POLY_MINIMAL_POLYNOMIAL, CYCLOTOMIC_POLY_DEG, SUBFIELD_GENERATED, FIELD_NONTRIVIAL] THEN REWRITE_TAC [INTEGER_RING, INT_OF_NUM_EQ, ARITH_EQ]])

  let POLY_RING_INTEGER_MOD_RING_DIVIDES_LIFT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_sub r h a = b ==> (h:A) = ring_add r a b")
    prove
      r"!n f h.
          f IN ring_carrier(poly_ring integer_ring (:1)) /\
          h IN ring_carrier(poly_ring integer_ring (:1)) /\
          ring_divides (poly_ring (integer_mod_ring n) (:1))
            (ring_of_int (integer_mod_ring n) o f)
            (ring_of_int (integer_mod_ring n) o h)
          ==> ?u d. u IN ring_carrier(poly_ring integer_ring (:1)) /\
                    d IN ring_carrier(poly_ring integer_ring (:1)) /\
                    h = ring_add (poly_ring integer_ring (:1))
                          (ring_mul (poly_ring integer_ring (:1)) f u)
                          (ring_mul (poly_ring integer_ring (:1))
                             (ring_of_num (poly_ring integer_ring (:1)) n) d)"
      (REPEAT GEN_TAC THEN REWRITE_TAC [ring_divides] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"u:(1->num)->int") STRIP_ASSUME_TAC))))) THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"integer_mod_ring n"), (← q r"ring_of_int(integer_mod_ring n)"), (← q r"(:1)")] RING_HOMOMORPHISM_POLY_RINGS) THEN REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(u:(1->num)->int) IN ring_carrier(poly_ring integer_ring (:1)) /\
      ring_of_int (integer_mod_ring n) o u = u") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [ASM_MESON_TAC [POLY_RING_INTEGER_MOD_RING_SUBSET, SUBSET], ALL_TAC] THEN REWRITE_TAC [FUN_EQ_THM, o_THM, INTEGER_MOD_RING_OF_INT, INT_REM_EQ_SELF, INT_ABS_NUM] THEN X_GEN_TAC (← q r"m:1->num") THEN UNDISCH_TAC (← q r"(u:(1->num)->int) IN
        ring_carrier(poly_ring (integer_mod_ring n) (:1))") THEN REWRITE_TAC [IN_POLY_RING_CARRIER, ring_polynomial, ring_powerseries] THEN DISCH_THEN (fun z7 => tactic_of do pure (MP_TAC (← SPEC (← q r"m:1->num") (← (do let z8 ← (pure (CONJUNCTS z7)); liftExcept (hd z8)))))) THEN REWRITE_TAC [IN_INTEGER_MOD_RING_CARRIER], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"(:1)"), (← q r"&n:int"), (← q r"ring_sub (poly_ring integer_ring (:1)) h
         (ring_mul (poly_ring integer_ring (:1)) f u)")] POLY_CONST_DIVIDES_COEFFS) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_SUB, RING_MUL, INTEGER_RING_DIVIDES] THEN SUBGOAL_THEN (← q r"ring_of_int (integer_mod_ring n) o
        ring_sub (poly_ring integer_ring (:1)) h
          (ring_mul (poly_ring integer_ring (:1)) f u) =
        ring_0(poly_ring (integer_mod_ring n) (:1))") MP_TAC THENL [FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← BETA_RULE (← MATCH_MP RING_HOMOMORPHISM_SUB th)), (← BETA_RULE (← MATCH_MP RING_HOMOMORPHISM_MUL th)), RING_MUL, RING_SUB_REFL])), REWRITE_TAC [FUN_EQ_THM, o_THM, INTEGER_MOD_RING_OF_INT, INT_REM_EQ_0, POLY_RING_CLAUSES, POLY_0, INTEGER_MOD_RING_CLAUSES]], ALL_TAC] THEN REWRITE_TAC [ring_divides, (← GSYM INTEGER_RING_OF_NUM), (← GSYM (← ISPECL [(← q r"integer_ring"), (← q r"(:1)")] RING_OF_NUM_POLY_RING))] THEN DISCH_THEN (fun z5 => tactic_of do pure (X_CHOOSE_THEN (← q r"d:(1->num)->int") STRIP_ASSUME_TAC (← (do let z6 ← (pure (CONJUNCTS z5)); liftExcept (last z6))))) THEN MAP_EVERY EXISTS_TAC [(← q r"u:(1->num)->int"), (← q r"d:(1->num)->int")] THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun z2 => (do let z3 ← (do let z4 ← (pure z2); pure (concl z4)); pure (is_eq z3))))) THEN MATCH_MP_TAC (← GEN_ALL r1) THEN ASM_SIMP_TAC [RING_MUL, RING_OF_NUM])

  let SUBRING_GENERATED_ROOT_OF_UNITY_REDUCED ← prove
    r"!k:A ring w n p c j.
        number_field k /\ w IN ring_carrier k /\
        ring_order k w = n /\ ~(n = 0) /\ prime p /\ ~(p divides n) /\
        c IN ring_carrier(subring_generated k {w}) /\
        (?y. y IN ring_carrier(subring_generated k {w}) /\
             ring_pow k c j = ring_mul k (ring_of_num k p) y)
        ==> ?y. y IN ring_carrier(subring_generated k {w}) /\
                c = ring_mul k (ring_of_num k p) y"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"w:A")] IMAGE_POLY_EXTEND_INTEGER_RING) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"w:A"), (← q r"n:num")] CYCLOTOMIC_POLY_INTEGER_ROOT) THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"k:A ring"), (← q r"(:1)"), (← q r"ring_of_int k:int->A"), (← q r"\v:1. w:A")] RING_HOMOMORPHISM_POLY_EXTEND) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN DISCH_TAC THEN ABBREV_TAC (← q r"E = poly_extend (integer_ring,k) (ring_of_int k) (\v:1. w:A)") THEN FIRST_ASSUM (ASSUME_TAC o ((REWRITE_RULE [SUBSET, FORALL_IN_IMAGE]) o (CONJUNCT1 o (GEN_REWRITE_RULE id [RING_HOMOMORPHISM])))) THEN UNDISCH_TAC (← q r"(y:A) IN ring_carrier(subring_generated k {w})") THEN UNDISCH_TAC (← q r"(c:A) IN ring_carrier(subring_generated k {w})") THEN ASM_REWRITE_TAC [IN_IMAGE, EXISTS_IN_IMAGE] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"h:(1->num)->int") (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"g:(1->num)->int") (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"w:A"), (← q r"n:num"), (← q r"ring_sub (poly_ring integer_ring (:1))
       (ring_pow (poly_ring integer_ring (:1)) h j)
       (ring_mul (poly_ring integer_ring (:1))
          (ring_of_num (poly_ring integer_ring (:1)) p) g)")] CYCLOTOMIC_POLY_DIVIDES_INTEGER_POLY) THEN ASM_SIMP_TAC [RING_SUB, RING_POW, RING_MUL, RING_OF_NUM] THEN MP_TAC (← ASSUME (← q r"ring_homomorphism(poly_ring integer_ring (:1),k)
                     (E:((1->num)->int)->A)")) THEN DISCH_THEN (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_SUB th), (← MATCH_MP RING_HOMOMORPHISM_MUL th), (← MATCH_MP RING_HOMOMORPHISM_POW th), (← MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM th), RING_POW, RING_OF_NUM, RING_MUL, RING_SUB_REFL])) THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"integer_mod_ring p"), (← q r"ring_of_int(integer_mod_ring p)"), (← q r"(:1)")] RING_HOMOMORPHISM_POLY_RINGS) THEN REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN DISCH_THEN (fun th => tactic_of do pure (DISCH_THEN (MP_TAC o (MATCH_MP (← MATCH_MP (← REWRITE_RULE [IMP_CONJ] RING_DIVIDES_HOMOMORPHIC_IMAGE) th))) THEN ASSUME_TAC th)) THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← BETA_RULE (← MATCH_MP RING_HOMOMORPHISM_SUB th)), (← BETA_RULE (← MATCH_MP RING_HOMOMORPHISM_MUL th)), (← BETA_RULE (← MATCH_MP RING_HOMOMORPHISM_POW th)), (← BETA_RULE (← MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM th)), RING_POW, RING_MUL, RING_OF_NUM])) THEN SUBGOAL_THEN (← q r"ring_of_int (integer_mod_ring p) o (g:(1->num)->int) IN
    ring_carrier(poly_ring (integer_mod_ring p) (:1)) /\
    ring_of_int (integer_mod_ring p) o (h:(1->num)->int) IN
    ring_carrier(poly_ring (integer_mod_ring p) (:1))") STRIP_ASSUME_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN EXISTS_TAC (← q r"integer_ring") THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_of_num (poly_ring (integer_mod_ring p) (:1)) p =
    ring_0 (poly_ring (integer_mod_ring p) (:1))") SUBST1_TAC THENL [REWRITE_TAC [RING_OF_NUM_EQ_0, RING_CHAR_POLY_RING, INTEGER_MOD_RING_CHAR, DIVIDES_REFL], ASM_SIMP_TAC [RING_MUL_LZERO, RING_SUB_RZERO, RING_POW]] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"p:num"), (← q r"cyclotomic_poly integer_ring n"), (← q r"h:(1->num)->int")] POLY_RING_INTEGER_MOD_RING_DIVIDES_LIFT) THEN ASM_REWRITE_TAC [CYCLOTOMIC_POLY_IN_CARRIER] THEN ANTS_TAC THENL [MATCH_MP_TAC RING_SQUAREFREE_DIVPOW THEN EXISTS_TAC (← q r"j:num") THEN ASM_REWRITE_TAC [(← MATCH_MP CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE (← ISPEC (← q r"integer_mod_ring p") RING_HOMOMORPHISM_INTEGER_RING_OF_INT))] THEN ASM_SIMP_TAC [PID_IMP_UFD, PID_POLY_RING, FIELD_INTEGER_MOD_RING, FIELD_IMP_INTEGRAL_DOMAIN, CYCLOTOMIC_POLY_SQUAREFREE, RING_OF_NUM_EQ_0, INTEGER_MOD_RING_CHAR], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"u:(1->num)->int") (X_CHOOSE_THEN (← q r"d:(1->num)->int") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)))) THEN EXISTS_TAC (← q r"d:(1->num)->int") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ASSUME (← q r"ring_homomorphism(poly_ring integer_ring (:1),k)
                     (E:((1->num)->int)->A)")) THEN DISCH_THEN (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_ADD th), (← MATCH_MP RING_HOMOMORPHISM_MUL th), (← MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM th), RING_OF_NUM, RING_MUL, CYCLOTOMIC_POLY_IN_CARRIER])) THEN ASM_SIMP_TAC [RING_MUL_LZERO, RING_ADD_LZERO, RING_MUL, RING_OF_NUM])

  let SUBRING_GENERATED_ROOT_OF_UNITY_DENOMINATOR ← prove
    r"!k:A ring w n.
        number_field k /\ w IN ring_carrier k /\
        ring_order k w = n /\ ~(n = 0)
        ==> ?d. ~(d = 0) /\
                !y. y IN ring_carrier(ring_of_integers k) /\
                    y IN ring_carrier(subfield_generated k {w})
                    ==> ring_mul k (ring_of_num k d) y IN
                        ring_carrier(subring_generated k {w})"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN SUBGOAL_THEN (← q r"(w:A) IN ring_carrier(subfield_generated k {w})") ASSUME_TAC THENL [MATCH_MP_TAC SUBFIELD_GENERATED_INC THEN ASM_REWRITE_TAC [SING_SUBSET, IN_SING], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {w:A}"), (← q r"phi n"), (← q r"\i. ring_pow (subfield_generated k {w:A}) w i")] RING_OF_INTEGERS_DISCRIMINANT) THEN ANTS_TAC THENL [ASM_SIMP_TAC [NUMBER_FIELD_SUBFIELD_GENERATED] THEN CONJ_TAC THENL [MATCH_MP_TAC CYCLOTOMIC_FIELD_FREE_BASIS THEN ASM_SIMP_TAC [NUMBER_FIELD_SUBFIELD_GENERATED, RING_ORDER_SUBFIELD_GENERATED, SUBFIELD_GENERATED_IDEMPOT], ALL_TAC] THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"ring_of_integers(subfield_generated k {w:A})") RING_POW) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM, integral_element] THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"cyclotomic_poly integer_ring n") THEN REWRITE_TAC [CYCLOTOMIC_POLY_IN_CARRIER, CYCLOTOMIC_POLY_MONIC] THEN MATCH_MP_TAC CYCLOTOMIC_POLY_INTEGER_ROOT THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, FIELD_SUBFIELD_GENERATED, RING_ORDER_SUBFIELD_GENERATED], ALL_TAC] THEN REWRITE_TAC [RING_OF_INT_SUBFIELD_GENERATED, (← CONJUNCT2 SUBFIELD_GENERATED)] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"D:int") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D"))) THEN SUBGOAL_THEN (← q r"&0 <= D * D /\ ~(D * D = &0:int)") STRIP_ASSUME_TAC THENL [REWRITE_TAC [INT_LE_SQUARE, INT_ENTIRE] THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC [RING_OF_INT_0], ALL_TAC] THEN EXISTS_TAC (← q r"num_of_int(D * D)") THEN ASM_SIMP_TAC [(← GSYM INT_OF_NUM_EQ), INT_OF_NUM_OF_INT, (← GSYM RING_OF_INT_OF_NUM)] THEN X_GEN_TAC (← q r"y:A") THEN STRIP_TAC THEN REMOVE_THEN "D" (MP_TAC o (SPEC (← q r"y:A"))) THEN ANTS_TAC THENL [MP_TAC (← ISPECL [(← q r"subfield_generated k {w:A}"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"y:A")] RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE) THEN ASM_SIMP_TAC [I_THM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC [FIELD_EXTENSION_SUBFIELD_GENERATED, field_extension], DISCH_THEN (X_CHOOSE_TAC (← q r"c:num->int"))] THEN SUBGOAL_THEN (← q r"ring_mul k (ring_of_int k D) y IN ring_carrier(subring_generated k {w:A})") MP_TAC THENL [ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [(← GSYM SUBRING_GENERATED_SUBFIELD_GENERATED)] THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {w:A}"), (← q r"w:A"), (← q r"n:num")] SUBRING_GENERATED_ROOT_OF_UNITY_LINCOMB) THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, FIELD_SUBFIELD_GENERATED, RING_ORDER_SUBFIELD_GENERATED] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [IN_ELIM_THM, IN_UNIV] THEN EXISTS_TAC (← q r"c:num->int") THEN REWRITE_TAC [RING_OF_INT_SUBFIELD_GENERATED, (← CONJUNCT2 SUBFIELD_GENERATED)], DISCH_TAC] THEN SUBGOAL_THEN (← q r"(y:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul k (ring_of_int k (D * D)) y =
    ring_mul k (ring_of_int k D) (ring_mul k (ring_of_int k D) y:A)") SUBST1_TAC THENL [SIMP_TAC [RING_OF_INT_MUL, RING_MUL_ASSOC, RING_OF_INT, (← ASSUME (← q r"(y:A) IN ring_carrier k"))], MATCH_MP_TAC IN_SUBRING_MUL THEN SIMP_TAC [SUBRING_SUBRING_GENERATED, IN_SUBRING_INT] THEN FIRST_ASSUM ACCEPT_TAC])

  let SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL_COPRIME ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"ring_add r (ring_mul r u a) (ring_mul r v b) = ring_1 r
        ==> (x:A) = ring_add r (ring_mul r u (ring_mul r a x))
                               (ring_mul r v (ring_mul r b x))"
    let r2 ← RING_RULE q1
    let v3 ← REWRITE_RULE [IMP_IMP] r2
    let v4 ← GEN_ALL v3
    let q5 ← q r"x = ring_add k
            (ring_mul k (ring_of_int k u) (ring_mul k (ring_of_num k a) x))
            (ring_mul k (ring_of_int k v) (ring_mul k (ring_of_num k b) x)):A"
    let q6 ← q r"ring_of_int (k:A ring)"
    let q7 ← q r"v:int"
    let q8 ← q r"u:int"
    let q9 ← q r"!a b:int. coprime(a,b) ==> ?u v. u * a + v * b = &1"
    let r10 ← INTEGER_RULE q9
    let p11 ← prove r"!k:A ring s a b x.
        s subring_of k /\ x IN ring_carrier k /\ coprime(a,b) /\
        ring_mul k (ring_of_num k a) x IN s /\
        ring_mul k (ring_of_num k b) x IN s
        ==> x IN s" (REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o ((MATCH_MP r10) o (GEN_REWRITE_RULE id [num_coprime]))) THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [q8, q7] THEN DISCH_THEN (MP_TAC o (AP_TERM q6)) THEN REWRITE_TAC [RING_OF_INT_ADD, RING_OF_INT_MUL, RING_OF_INT_OF_NUM, RING_OF_INT_1] THEN DISCH_TAC THEN SUBGOAL_THEN q5 SUBST1_TAC THENL [MATCH_MP_TAC v4 THEN ASM_REWRITE_TAC [RING_OF_INT, RING_OF_NUM], ASM_SIMP_TAC [IN_SUBRING_ADD, IN_SUBRING_MUL, IN_SUBRING_INT]])
    let lemma := p11
    let q15 ← q r"ring_of_num k p:A"
    let q16 ← q r"k:A ring"
    let q17 ← q r"ring_mul k (ring_of_num k t) x = v:A"
    let q18 ← q r"v:A"
    let v26 ← GSYM RING_OF_NUM_MUL
    let v27 ← GSYM RING_OF_NUM_EXP
    let q28 ← q r"ring_mul k (ring_of_num k t) (ring_mul k (ring_of_num k p) x) =
      ring_mul k (ring_of_num k (t * p)) (x:A)"
    let q29 ← q r"ring_of_integers k:A ring"
    let v30 ← ISPEC q29 RING_POW
    let q31 ← q r"ring_mul k (ring_of_num k (t EXP s))
        (ring_mul k (ring_of_num k d) (ring_pow k x (s + 1))):A"
    let q32 ← q r"s + 1"
    let q33 ← q r"ring_mul k (ring_of_num k t) (ring_mul k (ring_of_num k p) x:A)"
    let q34 ← q r"p:num"
    let q35 ← q r"n:num"
    let q36 ← q r"w:A"
    let q37 ← q r"k:A ring"
    let v38 ← ISPECL [q37, q36, q35, q34, q33, q32] SUBRING_GENERATED_ROOT_OF_UNITY_REDUCED
    let q39 ← q r"p:num"
    let q40 ← q r"t:num"
    let q41 ← q r"k:A ring"
    let q42 ← q r"(R:A->bool) subring_of k"
    let q43 ← q r"R = ring_carrier(subring_generated k {w:A})"
    let q44 ← q r"t:num"
    let q45 ← q r"s = index p d"
    let q46 ← q r"prime p ==> ~(p = 1)"
    let r47 ← MESON [PRIME_1] q46
    let q48 ← q r"p:num"
    let q49 ← q r"d:num"
    let v50 ← SPECL [q49, q48] INDEX_DECOMPOSITION
    let q51 ← q r"d:num"
    let q52 ← q r"n:num"
    let q53 ← q r"w:A"
    let q54 ← q r"k:A ring"
    let v55 ← ISPECL [q54, q53, q52] SUBRING_GENERATED_ROOT_OF_UNITY_DENOMINATOR
    let q56 ← q r"p:num"
    let q57 ← q r"subfield_generated k {w:A}"
    let v58 ← ISPECL [q57, q56] RING_OF_NUM
    let q59 ← q r"x = ring_mul k (ring_inv k (ring_of_num k p))
                     (ring_mul k (ring_of_num k p) x):A"
    let q60 ← q r"(x:A) IN ring_carrier(subfield_generated k {w})"
    let q61 ← q r"(x:A) IN ring_carrier k /\ ~(ring_of_num k p = ring_0 k) /\
    ring_carrier(subring_generated k {w}) SUBSET
    ring_carrier(subfield_generated k {w:A})"
    prove
      r"!k:A ring w n p x.
          number_field k /\ w IN ring_carrier k /\
          ring_order k w = n /\ ~(n = 0) /\ prime p /\ ~(p divides n) /\
          x IN ring_carrier(ring_of_integers k) /\
          ring_mul k (ring_of_num k p) x IN ring_carrier(subring_generated k {w})
          ==> x IN ring_carrier(subring_generated k {w})"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_NZ)) THEN SUBGOAL_THEN q61 STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_OF_NUM_EQ_0, DIVIDES_ZERO] THEN ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET, SUBRING_GENERATED_SUBFIELD_GENERATED, RING_CARRIER_SUBRING_GENERATED_SUBSET], ALL_TAC] THEN SUBGOAL_THEN q60 ASSUME_TAC THENL [SUBGOAL_THEN q59 SUBST1_TAC THENL [ASM_SIMP_TAC [RING_MUL_ASSOC, RING_INV, RING_OF_NUM, FIELD_MUL_LINV, RING_MUL_LID], MATCH_MP_TAC RING_MUL_IN_SUBFIELD_GENERATED THEN CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC [SUBSET]] THEN MATCH_MP_TAC RING_INV_IN_SUBFIELD_GENERATED THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED] THEN MP_TAC v58 THEN REWRITE_TAC [RING_OF_NUM_SUBFIELD_GENERATED]], ALL_TAC] THEN MP_TAC v55 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN q51 (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d"))) THEN MP_TAC v50 THEN ASM_SIMP_TAC [r47] THEN ABBREV_TAC q45 THEN DISCH_THEN (X_CHOOSE_THEN q44 STRIP_ASSUME_TAC) THEN ABBREV_TAC q43 THEN SUBGOAL_THEN q42 ASSUME_TAC THENL [EXPAND_TAC "R" THEN REWRITE_TAC [SUBRING_SUBRING_GENERATED], ALL_TAC] THEN MATCH_MP_TAC lemma THEN MAP_EVERY EXISTS_TAC [q41, q40, q39] THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ONCE_REWRITE_TAC [COPRIME_SYM] THEN ASM_SIMP_TAC [PRIME_COPRIME_EQ], ALL_TAC] THEN MP_TAC v38 THEN ASM_SIMP_TAC [IN_SUBRING_MUL, IN_SUBRING_NUM] THEN ANTS_TAC THENL [EXISTS_TAC q31 THEN CONJ_TAC THENL [MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_SIMP_TAC [IN_SUBRING_NUM] THEN REMOVE_THEN "d" MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_POW_IN_SUBFIELD_GENERATED] THEN MP_TAC v30 THEN ASM_SIMP_TAC [RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN q28 SUBST1_TAC THENL [ASM_SIMP_TAC [RING_OF_NUM_MUL, RING_MUL_ASSOC, RING_OF_NUM], ALL_TAC] THEN ASM_SIMP_TAC [RING_MUL_POW, RING_OF_NUM, v27, RING_MUL_ASSOC, v26, RING_POW] THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o ((checkM (fun z23 => (do let z24 ← (do let z25 ← (pure z23); pure (concl z25)); pure (is_eq z24)))) o (checkM (fun th => (do let z22 ← (q r"d:num"); let z21 ← (do let z19 ← (do let z20 ← (pure th); pure (concl z20)); liftExcept (rand z19)); pure (z21 == z22))))))) THEN REWRITE_TAC [EXP_ADD, EXP_1, MULT_EXP, MULT_AC], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN q18 STRIP_ASSUME_TAC) THEN SUBGOAL_THEN q17 (fun th => ASM_REWRITE_TAC [th]) THEN MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN MAP_EVERY EXISTS_TAC [q16, q15] THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, RING_OF_NUM, RING_MUL] THEN CONJ_TAC THENL [ASM_MESON_TAC [subring_of, SUBSET], ALL_TAC] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun z12 => (do let z13 ← (do let z14 ← (pure z12); pure (concl z14)); pure (is_eq z13)))))) THEN ASM_SIMP_TAC [RING_MUL_ASSOC, RING_OF_NUM] THEN AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC RING_MUL_SYM THEN REWRITE_TAC [RING_OF_NUM])

  let SUBRING_GENERATED_ROOT_OF_UNITY_RADICAL ← prove
    r"!k:A ring w n p c y j.
        number_field k /\ w IN ring_carrier k /\
        ring_order k w = n /\ ~(n = 0) /\ prime p /\ ~(p divides n) /\
        c IN ring_carrier(subring_generated k {w}) /\
        y IN ring_carrier(ring_of_integers k) /\
        ring_pow k c j = ring_mul k (ring_of_num k p) y
        ==> ?b. b IN ring_carrier(subring_generated k {w}) /\
                c = ring_mul k (ring_of_num k p) b"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBRING_GENERATED_ROOT_OF_UNITY_REDUCED THEN MAP_EVERY EXISTS_TAC [(← q r"n:num"), (← q r"j:num")] THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"y:A") THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL_COPRIME THEN MAP_EVERY EXISTS_TAC [(← q r"n:num"), (← q r"p:num")] THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [IN_SUBRING_POW, SUBRING_SUBRING_GENERATED])

  let RING_ASSOCIATES_PRIME_POWER_ORDER ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"2 <= p /\ p <= q ==> 2 <= q")
    prove
      r"!r:A ring x p a.
          integral_domain r /\ x IN ring_carrier r /\ prime p /\ ~(a = 0) /\
          ring_order r x = p EXP a
          ==> ring_associates r
                (ring_pow r (ring_sub r (ring_1 r) x) (phi(p EXP a)))
                (ring_of_num r p)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_NZ)) THEN ABBREV_TAC (← q r"U = {j | j < p EXP a /\ coprime(j,p EXP a)}") THEN SUBGOAL_THEN (← q r"FINITE(U:num->bool) /\ CARD U = phi(p EXP a)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "U" THEN REWRITE_TAC [PHI_ALT] THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{j:num | j < p EXP a}") THEN REWRITE_TAC [FINITE_NUMSEG_LT] THEN SET_TAC [], AP_TERM_TAC THEN SET_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"2 <= p EXP a") ASSUME_TAC THENL [MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [PRIME_GE_2] THEN GEN_REWRITE_TAC LAND_CONV [(← GSYM EXP_1)] THEN ASM_SIMP_TAC [LE_EXP, LE_1] THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_of_num r p =
      ring_product r U (\j. ring_sub r (ring_1 r) (ring_pow r (x:A) j))") SUBST1_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:num"), (← q r"a:num")] CYCLOTOMIC_POLY_EVAL_1_PRIME_POWER) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"x:A"), (← q r"p EXP a")] CYCLOTOMIC_POLY_SPLITS) THEN ASM_REWRITE_TAC [EXP_EQ_0] THEN DISCH_THEN SUBST1_TAC THEN wPart lhand (lhand o rand) POLY_EVAL_RING_PRODUCT THEN ANTS_TAC THENL [ASM_SIMP_TAC [(← GSYM RING_POLYNOMIAL), RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_CONST, RING_POW, RING_1], DISCH_THEN SUBST1_TAC] THEN MATCH_MP_TAC RING_PRODUCT_EQ THEN ASM_SIMP_TAC [POLY_EVAL_SUB, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_CONST, RING_POW, POLY_EVAL_VAR, POLY_EVAL_CONST, RING_1], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_pow r (ring_sub r (ring_1 r) x) (phi(p EXP a)) =
      ring_product r (U:num->bool) (\j. ring_sub r (ring_1 r) (x:A))") SUBST1_TAC THENL [ASM_SIMP_TAC [RING_PRODUCT_CONST, RING_SUB, RING_1], ALL_TAC] THEN SUBGOAL_THEN (← q r"!j. j IN U ==> ~(j = 0) /\ coprime(j,p EXP a)") ASSUME_TAC THENL [EXPAND_TAC "U" THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"j:num") THEN ASM_CASES_TAC (← q r"j = 0") THEN ASM_REWRITE_TAC [COPRIME_0] THENL [ASM_ARITH_TAC, MESON_TAC []], ALL_TAC] THEN REWRITE_TAC [ring_associates] THEN CONJ_TAC THEN MATCH_MP_TAC RING_DIVIDES_PRODUCTS THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"j:num") THEN DISCH_THEN (fun th => tactic_of do pure (FIRST_X_ASSUM (STRIP_ASSUME_TAC o (← do let c := th; pure (fun th => MATCH_MP th c))))) THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ring_1 r:A"), (← q r"x:A"), (← q r"j:num")] RING_DIVIDES_SUB_POW) THEN ASM_REWRITE_TAC [RING_1, RING_POW_ONE], ALL_TAC] THEN MP_TAC (← SPECL [(← q r"j:num"), (← q r"1"), (← q r"p EXP a")] CONG_SOLVE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"i:num")) THEN SUBGOAL_THEN (← q r"~(i = 0)") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE [MULT_CLAUSES, (← ExceptT.mk (NUMBER_RULE (← q r"(0 == 1) (mod n) <=> n = 1")))]) THEN ASM_ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ring_1 r:A"), (← q r"ring_pow r x j:A"), (← q r"i:num")] RING_DIVIDES_SUB_POW) THEN ASM_SIMP_TAC [RING_1, RING_POW_ONE, RING_POW, RING_POW_POW] THEN SUBGOAL_THEN (← q r"ring_pow r x (j * i) = ring_pow r (x:A) 1") MP_TAC THENL [ASM_SIMP_TAC [RING_POW_EQ_GEN, EXP_EQ_0], ASM_SIMP_TAC [RING_POW_1]])

  let SUBRING_GENERATED_POW_DECOMPOSE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r8 ← TAUT (← q r"p /\ (p ==> q /\ r) ==> p /\ q /\ r")
    prove
      r"!k:A ring z q m s.
          z IN ring_carrier k /\ ring_pow k z (q * m) = ring_1 k /\
          coprime(q,m) /\ s IN ring_carrier(subring_generated k {z})
          ==> ?c t. c IN ring_carrier(subring_generated k {ring_pow k z q}) /\
                    t IN ring_carrier(subring_generated k {z}) /\
                    s = ring_add k c (ring_mul k
                          (ring_sub k (ring_1 k) (ring_pow k z m)) t)"
      (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"R = ring_carrier(subring_generated k {z:A})") THEN ABBREV_TAC (← q r"W = ring_carrier(subring_generated k {ring_pow k z q:A})") THEN ABBREV_TAC (← q r"l = ring_sub k (ring_1 k) (ring_pow k z m:A)") THEN SUBGOAL_THEN (← q r"(R:A->bool) subring_of k /\ (W:A->bool) subring_of k /\ z IN R /\
      W SUBSET R /\ (l:A) IN R") STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["R", "W", "l"] THEN REWRITE_TAC [SUBRING_SUBRING_GENERATED] THEN MATCH_MP_TAC r8 THEN CONJ_TAC THENL [MATCH_MP_TAC SUBRING_GENERATED_INC THEN ASM_REWRITE_TAC [SING_SUBSET, IN_SING], DISCH_TAC] THEN CONJ_TAC THENL [MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN REWRITE_TAC [SING_SUBSET, SUBRING_SUBRING_GENERATED], MATCH_MP_TAC IN_SUBRING_SUB] THEN ASM_SIMP_TAC [SUBRING_SUBRING_GENERATED, IN_SUBRING_1, IN_SUBRING_POW], ALL_TAC] THEN SUBGOAL_THEN (← q r"(!x:A. x IN W ==> x IN R) /\ (!x:A. x IN R ==> x IN ring_carrier k) /\
      (!x:A. x IN W ==> x IN ring_carrier k) /\ (l:A) IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [subring_of, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"{y:A | ?c t. c IN W /\ t IN R /\ y = ring_add k c (ring_mul k l t)}
      subring_of k") ASSUME_TAC THENL [REWRITE_TAC [subring_of, SUBSET, IN_ELIM_THM] THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN REPEAT (FIRST_X_ASSUM (SUBST_ALL_TAC o ((checkM (fun z4 => (do let z5 ← (do let z6 ← (do let z7 ← (pure z4); pure (concl z7)); liftExcept (lhand z6)); pure (is_var z5)))) o (checkM (fun z1 => (do let z2 ← (do let z3 ← (pure z1); pure (concl z3)); pure (is_eq z2))))))) THENL [ASM_SIMP_TAC [RING_ADD, RING_MUL], MAP_EVERY EXISTS_TAC [(← q r"ring_0 k:A"), (← q r"ring_0 k:A")] THEN ASM_SIMP_TAC [IN_SUBRING_0, RING_MUL_RZERO, RING_ADD_LZERO, RING_0], MAP_EVERY EXISTS_TAC [(← q r"ring_1 k:A"), (← q r"ring_0 k:A")] THEN ASM_SIMP_TAC [IN_SUBRING_0, IN_SUBRING_1, RING_MUL_RZERO, RING_ADD_RZERO, RING_1], MAP_EVERY EXISTS_TAC [(← q r"ring_neg k c:A"), (← q r"ring_neg k t:A")], MAP_EVERY EXISTS_TAC [(← q r"ring_add k c c':A"), (← q r"ring_add k t t':A")], MAP_EVERY EXISTS_TAC [(← q r"ring_mul k c c':A"), (← q r"ring_add k (ring_mul k c t')
             (ring_add k (ring_mul k t c') (ring_mul k l (ring_mul k t t'))):A")] THEN CONJ_TAC THENL [ASM_SIMP_TAC [IN_SUBRING_MUL], ALL_TAC] THEN CONJ_TAC THENL [MATCH_MP_TAC IN_SUBRING_ADD THEN ASM_SIMP_TAC [IN_SUBRING_MUL, IN_SUBRING_ADD], ALL_TAC]] THEN ASM_SIMP_TAC [IN_SUBRING_NEG, IN_SUBRING_ADD, IN_SUBRING_MUL] THEN W (fun (_, w) => tactic_of do pure (MP_TAC (← RING_RULE w))) THEN ASM_SIMP_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"U = {y:A | ?c t. c IN W /\ t IN R /\
                       y = ring_add k c (ring_mul k l t)}") THEN SUBGOAL_THEN (← q r"ring_pow k z m IN U /\ ring_pow k (z:A) q IN U") STRIP_ASSUME_TAC THENL [EXPAND_TAC "U" THEN REWRITE_TAC [IN_ELIM_THM] THEN CONJ_TAC THENL [MAP_EVERY EXISTS_TAC [(← q r"ring_1 k:A"), (← q r"ring_neg k (ring_1 k):A")] THEN ASM_SIMP_TAC [IN_SUBRING_1, IN_SUBRING_NEG] THEN EXPAND_TAC "l" THEN W (fun (_, w) => tactic_of do pure (MP_TAC (← RING_RULE w))) THEN ASM_SIMP_TAC [RING_POW], MAP_EVERY EXISTS_TAC [(← q r"ring_pow k z q:A"), (← q r"ring_0 k:A")] THEN ASM_SIMP_TAC [IN_SUBRING_0, RING_MUL_RZERO, RING_ADD_RZERO, RING_POW] THEN EXPAND_TAC "W" THEN MATCH_MP_TAC SUBRING_GENERATED_INC THEN ASM_SIMP_TAC [SING_SUBSET, RING_POW, IN_SING]], ALL_TAC] THEN SUBGOAL_THEN (← q r"(z:A) IN U") ASSUME_TAC THENL [ASM_CASES_TAC (← q r"q = 1") THENL [UNDISCH_TAC (← q r"ring_pow k (z:A) q IN U") THEN ASM_SIMP_TAC [RING_POW_1], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(m = 0)") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"coprime(q,0)") THEN ASM_REWRITE_TAC [COPRIME_0], ALL_TAC] THEN MP_TAC (← SPECL [(← q r"m:num"), (← q r"q:num")] COPRIME_BEZOUT_STRONG) THEN ANTS_TAC THENL [ONCE_REWRITE_TAC [COPRIME_SYM] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:num") (X_CHOOSE_TAC (← q r"b:num"))) THEN SUBGOAL_THEN (← q r"z = ring_mul k (ring_pow k (ring_pow k z m) a)
                       (ring_pow k (ring_pow k z q) (b * (m - 1))):A") SUBST1_TAC THENL [SIMP_TAC [RING_POW_POW, (← GSYM RING_POW_ADD), (← ASSUME (← q r"(z:A) IN ring_carrier k"))] THEN SUBGOAL_THEN (← q r"m * a + q * b * (m - 1) = 1 + (q * m) * b") SUBST1_TAC THENL [UNDISCH_TAC (← q r"m * a = q * b + 1") THEN MP_TAC (← SPEC (← q r"m:num") num_CASES) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CHOOSE_THEN SUBST1_TAC) THEN REWRITE_TAC [SUC_SUB1] THEN CONV_TAC NUM_RING, ASM_SIMP_TAC [RING_POW_ADD, RING_POW_MUL, RING_POW_1, RING_POW_ONE, RING_MUL_RID]], ASM_SIMP_TAC [IN_SUBRING_MUL, IN_SUBRING_POW]], ALL_TAC] THEN SUBGOAL_THEN (← q r"(R:A->bool) SUBSET U") MP_TAC THENL [EXPAND_TAC "R" THEN MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET], REWRITE_TAC [SUBSET] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"s:A"))) THEN EXPAND_TAC "U" THEN ASM_REWRITE_TAC [IN_ELIM_THM]])

  -- @@RETURN BEGIN
  return { CYCLOTOMIC_POLY_INTEGER_ROOT, SUBRING_GENERATED_ROOT_OF_UNITY_LINCOMB,
           CYCLOTOMIC_POLY_DIVIDES_INTEGER_POLY, POLY_RING_INTEGER_MOD_RING_DIVIDES_LIFT,
           SUBRING_GENERATED_ROOT_OF_UNITY_REDUCED,
           SUBRING_GENERATED_ROOT_OF_UNITY_DENOMINATOR,
           SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL_COPRIME,
           SUBRING_GENERATED_ROOT_OF_UNITY_RADICAL, RING_ASSOCIATES_PRIME_POWER_ORDER,
           SUBRING_GENERATED_POW_DECOMPOSE }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- cyclotomic_integers.ml phrases from line 759 to 1278                   -/
/- ---------------------------------------------------------------------- -/

structure CyclotomicIntegers02 where
  -- @@FIELDS
  SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL_DIVIDES : thm
  SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL : thm
  CYCLOTOMIC_FIELD_RING_OF_INTEGERS : thm
  CYCLOTOMIC_FIELD_INTEGRAL_BASIS : thm
  CYCLOTOMIC_FIELD_SUBFIELD_POW : thm
  CYCLOTOMIC_FIELD_NORM_SUB : thm
  CYCLOTOMIC_FIELD_NORM_SUB_POW : thm
  CYCLOTOMIC_FIELD_DISCRIMINANT_DERIV : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupCyclotomicIntegers02 [HolBase] (D : CyclotomicIntegersDeps) (BCyclotomicIntegers01 : CyclotomicIntegers01) :
    ExceptT String IO CyclotomicIntegers02 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, NUMBER_RULE,
        RING_RULE, SET_RULE, TAUT, .. } := D
  let { COPRIME_PRIMEPOW, COPRIME_SYM, CYCLOTOMIC_FIELD_DEGREE,
        CYCLOTOMIC_FIELD_FREE_BASIS, CYCLOTOMIC_POLY_DEG,
        CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE, CYCLOTOMIC_POLY_IN_CARRIER,
        CYCLOTOMIC_POLY_MINIMAL_POLYNOMIAL, CYCLOTOMIC_POLY_MONIC, DE_MORGAN_THM,
        DIVIDES_0, DIVIDES_REFL, DIVIDES_RMUL, DIVIDES_ZERO, DIV_MULT, EXP, EXP_EQ_0,
        EXP_EQ_1, FIELD_EXTENSION_SUBFIELD_GENERATED, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_NONTRIVIAL, FIELD_SUBFIELD_GENERATED, FINITE_SING, FORALL_IN_GSPEC,
        FORALL_IN_INSERT, FREE_BASIS_INTEGER_RING_SUBRING_GENERATED,
        FREE_BASIS_PRIME_SUBFIELD_DENOMINATOR, INDEX_DECOMPOSITION,
        INTEGRAL_DOMAIN_MUL_LCANCEL, INTEGRAL_DOMAIN_POW_EQ_0,
        INTEGRAL_DOMAIN_SUBRING_GENERATED, INT_ENTIRE, INT_LE_SQUARE, INT_OF_NUM_EQ,
        INT_OF_NUM_OF_INT, IN_ELIM_THM, .. } := D.core1
  let { IN_SING, IN_SUBRING_0, IN_SUBRING_1, IN_SUBRING_ADD, IN_SUBRING_INT,
        IN_SUBRING_MUL, IN_SUBRING_POW, IN_SUBRING_SUB, IN_UNIV, I_O_ID, I_THM,
        LE_REFL, LT_MULT_RCANCEL, MULT_CLAUSES, MULT_EQ_0, MULT_SYM, NOT_IN_EMPTY,
        NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD, NUMBER_FIELD_DISCRIMINANT_POWER_BASIS,
        NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_NORM_SUB_MINIMAL_POLYNOMIAL,
        NUMBER_FIELD_NORM_TOWER, NUMBER_FIELD_SUBFIELD_GENERATED,
        NUMBER_FIELD_TOWER_LAW, PHI_EQ_0, POLY_EVAL_HOMOMORPHIC_IMAGE,
        POLY_EXTEND_EVALUATE, PRIME_FACTOR, PRIME_GE_2, PRIME_IMP_NZ,
        PRIME_SUBFIELD_SUBFIELD_GENERATED, RINGS_EQ, RING_1, RING_ADD, RING_ADD_LZERO,
        RING_CARRIER_SUBFIELD_GENERATED_SUBSET, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, .. } := D.core2
  let { RING_MUL, RING_MUL_ASSOC, RING_MUL_LID, RING_MUL_POW, RING_MUL_RZERO,
        RING_OF_INT, RING_OF_INTEGERS, RING_OF_INTEGERS_CARRIER,
        RING_OF_INTEGERS_SUBRING, RING_OF_INTEGERS_SUBSET, RING_OF_INT_EQ_0_CHAR_0,
        RING_OF_INT_IN_SUBFIELD_GENERATED, RING_OF_INT_MUL, RING_OF_INT_OF_NUM,
        RING_OF_NUM, RING_OF_NUM_1, RING_OF_NUM_EQ_0, RING_OF_NUM_MUL,
        RING_OF_NUM_SUBFIELD_GENERATED, RING_OF_NUM_SUBRING_GENERATED, RING_ORDER_1,
        RING_ORDER_POW, RING_ORDER_SUBFIELD_GENERATED, RING_ORDER_UNIQUE, RING_POW,
        RING_POW_1, RING_POW_ADD, RING_POW_EQ_1, RING_POW_SUBRING_GENERATED, RING_SUB,
        RING_SUB_EQ_0, RING_SUB_SUBFIELD_GENERATED, RING_SUB_SUBRING_GENERATED,
        SING_SUBSET, SUBFIELD_GENERATED, SUBFIELD_GENERATED_IDEMPOT,
        SUBFIELD_GENERATED_SUBSET_CARRIER, SUBRING_GENERATED,
        SUBRING_GENERATED_BY_SUBRING_GENERATED, SUBRING_GENERATED_INC,
        SUBRING_GENERATED_MINIMAL, SUBRING_SUBRING_GENERATED, SUBSET, SUBSET_ANTISYM,
        divides, free_basis, integral_element, num_WF, number_field, poly_deriv,
        poly_eval, ring_associates, ring_divides, ring_pow, subring_of, .. } := D.core3
  let { CYCLOTOMIC_POLY_INTEGER_ROOT, RING_ASSOCIATES_PRIME_POWER_ORDER,
        SUBRING_GENERATED_POW_DECOMPOSE, SUBRING_GENERATED_ROOT_OF_UNITY_LINCOMB,
        SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL_COPRIME,
        SUBRING_GENERATED_ROOT_OF_UNITY_RADICAL, .. } := BCyclotomicIntegers01
  -- @@SCOPE END

  let SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL_DIVIDES ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"ring_mul k q x =
        ring_add k (ring_mul k q r) (ring_mul k (ring_pow k l e) s) /\
        ring_pow k l e = ring_mul k q u
        ==> ring_mul k q x = ring_mul k q (ring_add k r (ring_mul k u (s:A)))"
    let r2 ← RING_RULE q1
    let q3 ← q r"q:A"
    let q4 ← q r"k:A ring"
    let q5 ← q r"x = ring_add k r (ring_mul k u s):A"
    let q6 ← q r"s:A"
    let q7 ← q r"r:A"
    let v12 ← CONJUNCT2 ring_pow
    let q13 ← q r"t:A"
    let q14 ← q r"ring_add k r (ring_mul k (ring_pow k l i) b):A"
    let q15 ← q r"b:A"
    let q16 ← q r"ring_mul k q x =
          ring_add k (ring_mul k q r)
            (ring_mul k (ring_pow k l i) (ring_add k c (ring_mul k l t))) /\
          ring_mul k (ring_pow k l e) v = q /\
          ring_pow k l e =
          ring_mul k (ring_pow k l i) (ring_mul k l (ring_pow k l (e - SUC i)))
          ==> ring_mul k (ring_pow k l i) c =
              ring_mul k (ring_pow k l i)
               (ring_mul k l (ring_sub k (ring_mul k (ring_pow k l (e - SUC i))
                               (ring_mul k v (ring_sub k x r))) (t:A)))"
    let r17 ← RING_RULE q16
    let q18 ← q r"SUC i <= e ==> e = i + 1 + (e - SUC i)"
    let r19 ← ARITH_RULE q18
    let q20 ← q r"ring_pow k l e = ring_mul k (ring_pow k l i)
                             (ring_mul k l (ring_pow k l (e - SUC i))):A"
    let q21 ← q r"ring_pow k l i:A"
    let q22 ← q r"k:A ring"
    let q23 ← q r"ring_sub k (ring_mul k (ring_pow k l (e - SUC i))
                  (ring_mul k v (ring_sub k x r))) t:A"
    let q24 ← q r"c:A"
    let q25 ← q r"t:A"
    let q26 ← q r"c:A"
    let q27 ← q r"s:A"
    let q28 ← q r"(s:A) IN R"
    let v29 ← ASSUME q28
    let q30 ← q r"s:A"
    let q31 ← q r"r:A"
    let q35 ← q r"ring_mul k q x:A"
    let q36 ← q r"ring_0 k:A"
    let q37 ← q r"e:num"
    let q38 ← q r"!i. i <= e
          ==> ?r s. r IN R /\ s IN R /\
                    ring_mul k q (x:A) =
                    ring_add k (ring_mul k q r) (ring_mul k (ring_pow k l i) s)"
    let q39 ← q r"(l:A) IN ring_carrier k /\ (u:A) IN ring_carrier k /\
      (v:A) IN ring_carrier k /\ (x:A) IN ring_carrier k"
    let q40 ← q r"(!y:A. y IN R ==> y IN ring_carrier k) /\
      (!y:A. y IN W ==> y IN ring_carrier k)"
    let q41 ← q r"(S:A->bool) subring_of k"
    let v42 ← ASSUME q41
    let p43 ← prove r"!k:A ring R S W l q u v e x.
        (!s. s IN R
             ==> ?c t. c IN W /\ t IN R /\
                       s = ring_add k c (ring_mul k l t)) /\
        (!c y. c IN W /\ y IN S /\ c = ring_mul k l y
               ==> ?b. b IN W /\ c = ring_mul k q b) /\
        integral_domain k /\ R subring_of k /\ S subring_of k /\
        W SUBSET R /\ R SUBSET S /\ l IN R /\ ~(l = ring_0 k) /\
        q IN ring_carrier k /\ ~(q = ring_0 k) /\ u IN R /\ v IN R /\
        ring_mul k (ring_pow k l e) v = q /\ ring_pow k l e = ring_mul k q u /\
        x IN S /\ ring_mul k q x IN R
        ==> x IN R" (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "dec") (CONJUNCTS_THEN2 (LABEL_TAC "key") STRIP_ASSUME_TAC)) THEN MP_TAC v42 THEN REWRITE_TAC [subring_of, SUBSET] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN RULE_ASSUM_TAC (REWRITE_RULE [SUBSET]) THEN SUBGOAL_THEN q40 STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN q39 STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN q38 (MP_TAC o (SPEC q37)) THENL [INDUCT_TAC THENL [DISCH_TAC THEN MAP_EVERY EXISTS_TAC [q36, q35] THEN ASM_SIMP_TAC [IN_SUBRING_0, ring_pow, RING_MUL_RZERO, RING_ADD_LZERO, RING_MUL_LID, RING_MUL], ALL_TAC] THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun z32 => (do let z33 ← (do let z34 ← (pure z32); pure (concl z34)); pure (is_imp z33))))) THEN ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN q31 (X_CHOOSE_THEN q30 STRIP_ASSUME_TAC)) THEN USE_THEN "dec" (MP_TAC o ((← do let c := v29; pure (fun th => MP th c)) o (SPEC q27))) THEN DISCH_THEN (X_CHOOSE_THEN q26 (X_CHOOSE_THEN q25 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)))) THEN USE_THEN "key" (MP_TAC o (SPECL [q24, q23])) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [REPEAT (FIRST [MATCH_MP_TAC IN_SUBRING_SUB, MATCH_MP_TAC IN_SUBRING_MUL, MATCH_MP_TAC IN_SUBRING_POW, CONJ_TAC]) THEN ASM_SIMP_TAC [], ALL_TAC] THEN MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN MAP_EVERY EXISTS_TAC [q22, q21] THEN ASM_SIMP_TAC [RING_POW, INTEGRAL_DOMAIN_POW_EQ_0, RING_MUL, RING_SUB] THEN CONJ_TAC THENL [REPEAT (FIRST [MATCH_MP_TAC RING_SUB, MATCH_MP_TAC RING_MUL, MATCH_MP_TAC RING_POW, CONJ_TAC]) THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN q20 ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP r19)) THEN DISCH_THEN (fun th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN ASM_SIMP_TAC [RING_POW_ADD, RING_POW_1], ALL_TAC] THEN MP_TAC r17 THEN ANTS_TAC THENL [ASM_SIMP_TAC [], DISCH_THEN MATCH_MP_TAC] THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN q15 (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN MAP_EVERY EXISTS_TAC [q14, q13] THEN REWRITE_TAC [v12] THEN REPEAT CONJ_TAC THENL [ASM_SIMP_TAC [IN_SUBRING_ADD, IN_SUBRING_MUL, IN_SUBRING_POW], FIRST_ASSUM ACCEPT_TAC, FIRST_X_ASSUM (SUBST1_TAC o (checkM (fun th => (do let z11 ← (q r"ring_mul k q (x:A)"); let z10 ← (do let z8 ← (do let z9 ← (pure th); pure (concl z9)); liftExcept (lhand z8)); pure (z10 == z11))))) THEN W (fun (_, w) => tactic_of do pure (MP_TAC (← RING_RULE w))) THEN ASM_SIMP_TAC []], ALL_TAC] THEN REWRITE_TAC [LE_REFL] THEN DISCH_THEN (X_CHOOSE_THEN q7 (X_CHOOSE_THEN q6 STRIP_ASSUME_TAC)) THEN SUBGOAL_THEN q5 SUBST1_TAC THENL [MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN MAP_EVERY EXISTS_TAC [q4, q3] THEN REPEAT CONJ_TAC THEN TRY (ASM_SIMP_TAC [RING_ADD, RING_MUL] THEN NO_TAC) THEN MP_TAC r2 THEN ANTS_TAC THENL [ASM_SIMP_TAC [], DISCH_THEN MATCH_MP_TAC] THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC, ASM_SIMP_TAC [IN_SUBRING_ADD, IN_SUBRING_MUL]])
    let lemma := p43
    let q44 ← q r"e:num"
    let q45 ← q r"v:A"
    let q46 ← q r"u:A"
    let q47 ← q r"ring_of_num k p:A"
    let q48 ← q r"l:A"
    let q49 ← q r"W:A->bool"
    let q50 ← q r"ring_carrier(ring_of_integers k):A->bool"
    let q51 ← q r"k:A ring"
    let q52 ← q r"s:A"
    let q53 ← q r"m:num"
    let q54 ← q r"p EXP a"
    let q55 ← q r"z:A"
    let q56 ← q r"k:A ring"
    let v57 ← ISPECL [q56, q55, q54, q53, q52] SUBRING_GENERATED_POW_DECOMPOSE
    let q58 ← q r"s:A"
    let q59 ← q r"!s. s IN R
        ==> ?c t. c IN W /\ t IN R /\ s = ring_add k c (ring_mul k l t:A)"
    let q63 ← q r"ring_of_integers k:A ring"
    let v64 ← ISPEC q63 RING_POW
    let q65 ← q r"ring_of_integers k:A ring"
    let v66 ← ISPEC q65 RING_MUL
    let q67 ← q r"(y:A) IN ring_carrier k /\ (u:A) IN ring_carrier k"
    let q68 ← q r"e:num"
    let q69 ← q r"ring_mul k u (ring_pow k y e):A"
    let q70 ← q r"m:num"
    let q71 ← q r"!c y:A. c IN W /\ y IN ring_carrier(ring_of_integers k) /\
            c = ring_mul k l y
            ==> ?b. b IN W /\ c = ring_mul k (ring_of_num k p) b"
    let q72 ← q r"ring_order (k:A ring)"
    let q73 ← q r"(z:A) IN ring_carrier(subring_generated k {z})"
    let v74 ← GSYM SUBSET
    let q75 ← q r"(R:A->bool) subring_of k /\ (W:A->bool) subring_of k /\
    (!y:A. y IN W ==> y IN R) /\
    (!y:A. y IN R ==> y IN ring_carrier(ring_of_integers k)) /\
    (l:A) IN R /\ ~(l = ring_0 k) /\ l IN ring_carrier k"
    let q76 ← q r"e = phi(p EXP a)"
    let q77 ← q r"l = ring_sub k (ring_1 k) (ring_pow k z m:A)"
    let q78 ← q r"W = ring_carrier(subring_generated k {ring_pow k z (p EXP a):A})"
    let q79 ← q r"R = ring_carrier(subring_generated k {z:A})"
    let v84 ← CONJUNCT2 SUBRING_GENERATED
    let v85 ← CONJUNCT2 SUBRING_GENERATED
    let q86 ← q r"p /\ (p ==> q) ==> p /\ q"
    let r87 ← TAUT q86
    let q88 ← q r"a:num"
    let q89 ← q r"p:num"
    let q90 ← q r"ring_pow k z m:A"
    let q91 ← q r"subring_generated k {z:A}"
    let v92 ← ISPECL [q91, q90, q89, q88] RING_ASSOCIATES_PRIME_POWER_ORDER
    let q93 ← q r"cyclotomic_poly integer_ring (p EXP a * m)"
    let q94 ← q r"(z:A) IN ring_carrier(ring_of_integers k)"
    let q95 ← q r"(q:num) divides q * m"
    let v96 ← ExceptT.mk (NUMBER_RULE q95)
    let q97 ← q r"(m:num) divides q * m"
    let v98 ← ExceptT.mk (NUMBER_RULE q97)
    let q99 ← q r"ring_order k (ring_pow k (z:A) m) = p EXP a /\
    ring_order k (ring_pow k z (p EXP a)) = m"
    let q100 ← q r"~(m = 0)"
    let q101 ← q r"ring_of_num k p IN ring_carrier k /\ ~(ring_of_num k p = ring_0 (k:A ring))"
    prove
      r"!k:A ring z p a m x.
          number_field k /\ z IN ring_carrier k /\
          ring_order k z = p EXP a * m /\ prime p /\ ~(a = 0) /\
          ~(p divides m) /\
          x IN ring_carrier(ring_of_integers k) /\
          ring_mul k (ring_of_num k p) x IN ring_carrier(subring_generated k {z})
          ==> x IN ring_carrier(subring_generated k {z})"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_NZ)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_GE_2)) THEN SUBGOAL_THEN q101 STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_OF_NUM, RING_OF_NUM_EQ_0, DIVIDES_ZERO], ALL_TAC] THEN SUBGOAL_THEN q100 ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC [DIVIDES_0], ALL_TAC] THEN SUBGOAL_THEN q99 STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_ORDER_POW, EXP_EQ_0, v98, v96] THEN ASM_SIMP_TAC [DIV_MULT, EXP_EQ_0] THEN ONCE_REWRITE_TAC [MULT_SYM] THEN ASM_SIMP_TAC [DIV_MULT], ALL_TAC] THEN SUBGOAL_THEN q94 ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM, integral_element] THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC q93 THEN REWRITE_TAC [CYCLOTOMIC_POLY_IN_CARRIER, CYCLOTOMIC_POLY_MONIC] THEN MATCH_MP_TAC CYCLOTOMIC_POLY_INTEGER_ROOT THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, MULT_EQ_0, EXP_EQ_0], ALL_TAC] THEN MP_TAC v92 THEN ANTS_TAC THENL [ASM_SIMP_TAC [INTEGRAL_DOMAIN_SUBRING_GENERATED, FIELD_IMP_INTEGRAL_DOMAIN] THEN MATCH_MP_TAC r87 THEN CONJ_TAC THENL [MATCH_MP_TAC IN_SUBRING_POW THEN REWRITE_TAC [SUBRING_SUBRING_GENERATED] THEN MATCH_MP_TAC SUBRING_GENERATED_INC THEN ASM_REWRITE_TAC [SING_SUBSET, IN_SING], DISCH_TAC] THEN ASM_SIMP_TAC [RING_ORDER_UNIQUE] THEN REWRITE_TAC [RING_POW_SUBRING_GENERATED, v85] THEN ASM_SIMP_TAC [RING_POW_EQ_1, RING_POW], ALL_TAC] THEN REWRITE_TAC [ring_associates, ring_divides, RING_POW_SUBRING_GENERATED, RING_SUB_SUBRING_GENERATED, RING_OF_NUM_SUBRING_GENERATED, v84] THEN DISCH_THEN (CONJUNCTS_THEN2 (fun z82 => tactic_of do pure (X_CHOOSE_THEN (← q r"v:A") (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)) (← (do let z83 ← (pure (CONJUNCTS z82)); liftExcept (last z83))))) (fun z80 => tactic_of do pure (X_CHOOSE_THEN (← q r"u:A") STRIP_ASSUME_TAC (← (do let z81 ← (pure (CONJUNCTS z80)); liftExcept (last z81)))))) THEN ABBREV_TAC q79 THEN ABBREV_TAC q78 THEN ABBREV_TAC q77 THEN ABBREV_TAC q76 THEN SUBGOAL_THEN q75 STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["R", "W", "l"] THEN REWRITE_TAC [SUBRING_SUBRING_GENERATED, v74] THEN SUBGOAL_THEN q73 ASSUME_TAC THENL [MATCH_MP_TAC SUBRING_GENERATED_INC THEN ASM_REWRITE_TAC [SING_SUBSET, IN_SING], ALL_TAC] THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN ASM_SIMP_TAC [SING_SUBSET, SUBRING_SUBRING_GENERATED, IN_SUBRING_POW], MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET, RING_OF_INTEGERS_SUBRING], ASM_SIMP_TAC [IN_SUBRING_SUB, IN_SUBRING_1, IN_SUBRING_POW, SUBRING_SUBRING_GENERATED], ASM_SIMP_TAC [RING_SUB_EQ_0, RING_1, RING_POW] THEN DISCH_THEN (MP_TAC o (SYM o (AP_TERM q72))) THEN ASM_REWRITE_TAC [RING_ORDER_1, EXP_EQ_1] THEN ASM_ARITH_TAC, ASM_SIMP_TAC [RING_SUB, RING_1, RING_POW]], ALL_TAC] THEN SUBGOAL_THEN q71 ASSUME_TAC THENL [REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN EXPAND_TAC "W" THEN MATCH_MP_TAC SUBRING_GENERATED_ROOT_OF_UNITY_RADICAL THEN MAP_EVERY EXISTS_TAC [q70, q69, q68] THEN SUBGOAL_THEN q67 STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [RING_POW] THEN CONJ_TAC THENL [MP_TAC v66 THEN MP_TAC v64 THEN ASM_SIMP_TAC [RING_OF_INTEGERS], FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun z60 => (do let z61 ← (do let z62 ← (pure z60); pure (concl z62)); pure (is_eq z61)))))) THEN ASM_SIMP_TAC [RING_MUL_POW, RING_MUL_ASSOC, RING_OF_NUM, RING_POW]], ALL_TAC] THEN SUBGOAL_THEN q59 ASSUME_TAC THENL [X_GEN_TAC q58 THEN DISCH_TAC THEN MP_TAC v57 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_POW_EQ_1, DIVIDES_REFL] THEN ONCE_REWRITE_TAC [COPRIME_SYM] THEN ASM_SIMP_TAC [COPRIME_PRIMEPOW], ALL_TAC] THEN MATCH_MP_TAC lemma THEN MAP_EVERY EXISTS_TAC [q51, q50, q49, q48, q47, q46, q45, q44] THEN REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, RING_OF_INTEGERS_SUBRING, SUBSET])

  let SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"2 <= p ==> ~(p = 1)")
    prove
      r"!k:A ring z n p x.
          number_field k /\ z IN ring_carrier k /\
          ring_order k z = n /\ ~(n = 0) /\ prime p /\
          x IN ring_carrier(ring_of_integers k) /\
          ring_mul k (ring_of_num k p) x IN ring_carrier(subring_generated k {z})
          ==> x IN ring_carrier(subring_generated k {z})"
      (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"(p:num) divides n") THENL [ALL_TAC, MATCH_MP_TAC SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL_COPRIME THEN MAP_EVERY EXISTS_TAC [(← q r"n:num"), (← q r"p:num")] THEN ASM_REWRITE_TAC []] THEN MP_TAC (← SPECL [(← q r"n:num"), (← q r"p:num")] INDEX_DECOMPOSITION) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_GE_2)) THEN ASM_SIMP_TAC [r1] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"m:num") STRIP_ASSUME_TAC) THEN MATCH_MP_TAC SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL_DIVIDES THEN MAP_EVERY EXISTS_TAC [(← q r"p:num"), (← q r"index p n"), (← q r"m:num")] THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"p EXP index p n * m = n") THEN ASM_REWRITE_TAC [EXP, MULT_CLAUSES] THEN ASM_MESON_TAC [])

  let CYCLOTOMIC_FIELD_RING_OF_INTEGERS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r4 ← ARITH_RULE (← q r"e = 1 * e")
    prove
      r"!(k:A ring) z n.
          number_field k /\ z IN ring_carrier k /\
          ring_order k z = n /\ ~(n = 0) /\ subfield_generated k {z} = k
          ==> ring_of_integers k = subring_generated k {z}"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN REWRITE_TAC [RINGS_EQ, RING_OF_INTEGERS, (← CONJUNCT2 SUBRING_GENERATED)] THEN ABBREV_TAC (← q r"R = ring_carrier(subring_generated k {z:A})") THEN SUBGOAL_THEN (← q r"(R:A->bool) subring_of k") ASSUME_TAC THENL [EXPAND_TAC "R" THEN REWRITE_TAC [SUBRING_SUBRING_GENERATED], ALL_TAC] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [ALL_TAC, EXPAND_TAC "R" THEN MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN REWRITE_TAC [SING_SUBSET, RING_OF_INTEGERS_SUBRING] THEN REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM, integral_element] THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"cyclotomic_poly integer_ring n") THEN ASM_SIMP_TAC [CYCLOTOMIC_POLY_IN_CARRIER, CYCLOTOMIC_POLY_MONIC, CYCLOTOMIC_POLY_INTEGER_ROOT, FIELD_IMP_INTEGRAL_DOMAIN]] THEN SUBGOAL_THEN (← q r"!d. ~(d = 0)
          ==> !x:A. x IN ring_carrier(ring_of_integers k) /\
                    ring_mul k (ring_of_num k d) x IN R
                    ==> x IN R") ASSUME_TAC THENL [MATCH_MP_TAC num_WF THEN X_GEN_TAC (← q r"d:num") THEN REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"d = 1") THENL [UNDISCH_TAC (← q r"ring_mul k (ring_of_num k d) x IN (R:A->bool)") THEN ASM_SIMP_TAC [RING_OF_NUM_1, RING_MUL_LID, (← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET)], ALL_TAC] THEN FIRST_ASSUM ((X_CHOOSE_THEN (← q r"p:num") STRIP_ASSUME_TAC) o (MATCH_MP PRIME_FACTOR)) THEN FIRST_X_ASSUM ((X_CHOOSE_THEN (← q r"e:num") SUBST_ALL_TAC) o (GEN_REWRITE_RULE id [divides])) THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"e:num"))) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_GE_2)) THEN RULE_ASSUM_TAC (REWRITE_RULE [MULT_EQ_0, DE_MORGAN_THM]) THEN ANTS_TAC THENL [GEN_REWRITE_TAC LAND_CONV [r4] THEN ASM_REWRITE_TAC [LT_MULT_RCANCEL] THEN ASM_ARITH_TAC, ALL_TAC] THEN ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "R" THEN MATCH_MP_TAC SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL THEN MAP_EVERY EXISTS_TAC [(← q r"n:num"), (← q r"p:num")] THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_MUL) THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_OF_NUM) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN ASM_SIMP_TAC [], UNDISCH_TAC (← q r"ring_mul k (ring_of_num k (p * e)) x IN (R:A->bool)") THEN ASM_SIMP_TAC [RING_OF_NUM_MUL, RING_MUL_ASSOC, RING_OF_NUM, (← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET)]], ALL_TAC] THEN REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"phi n"), (← q r"\i. ring_pow k (z:A) i"), (← q r"{x:A}")] FREE_BASIS_PRIME_SUBFIELD_DENOMINATOR) THEN ASM_SIMP_TAC [CYCLOTOMIC_FIELD_FREE_BASIS, FINITE_SING, SING_SUBSET, FORALL_IN_INSERT, NOT_IN_EMPTY] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"d:int") (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC (← q r"c:num->int")))) THEN SUBGOAL_THEN (← q r"ring_mul k (ring_of_int k d) x IN (R:A->bool)") ASSUME_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (checkM (fun z1 => (do let z2 ← (do let z3 ← (pure z1); pure (concl z3)); pure (is_eq z2))))) THEN EXPAND_TAC "R" THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num")] SUBRING_GENERATED_ROOT_OF_UNITY_LINCOMB) THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [IN_ELIM_THM, IN_UNIV] THEN EXISTS_TAC (← q r"c:num->int") THEN REWRITE_TAC [], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"num_of_int(d * d)"))) THEN SUBGOAL_THEN (← q r"&0 <= d * d /\ ~(d * d = &0:int)") STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC [INT_LE_SQUARE, INT_ENTIRE], ALL_TAC] THEN ASM_SIMP_TAC [(← GSYM INT_OF_NUM_EQ), INT_OF_NUM_OF_INT, (← GSYM RING_OF_INT_OF_NUM)] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [RING_OF_INT_MUL] THEN SUBGOAL_THEN (← q r"ring_mul k (ring_mul k (ring_of_int k d) (ring_of_int k d)) x =
      ring_mul k (ring_of_int k d) (ring_mul k (ring_of_int k d) x):A") SUBST1_TAC THENL [MATCH_MP_TAC (← GSYM RING_MUL_ASSOC) THEN ASM_REWRITE_TAC [RING_OF_INT], MATCH_MP_TAC IN_SUBRING_MUL THEN REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN MATCH_MP_TAC IN_SUBRING_INT THEN FIRST_ASSUM ACCEPT_TAC])

  let CYCLOTOMIC_FIELD_INTEGRAL_BASIS ← prove
    r"!(k:A ring) z n.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = n /\ ~(n = 0) /\ subfield_generated k {z} = k
        ==> free_basis (integer_ring,ring_of_integers k) (ring_of_int k) (phi n)
                       (\i. ring_pow k z i)"
    (REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM (SUBST1_TAC o (MATCH_MP CYCLOTOMIC_FIELD_RING_OF_INTEGERS)) THEN POP_ASSUM STRIP_ASSUME_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN ONCE_REWRITE_TAC [(← GSYM SUBRING_GENERATED_BY_SUBRING_GENERATED)] THEN SIMP_TAC [FREE_BASIS_INTEGER_RING_SUBRING_GENERATED, SUBRING_SUBRING_GENERATED] THEN REPEAT CONJ_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_SUBRING_POW THEN REWRITE_TAC [SUBRING_SUBRING_GENERATED] THEN MATCH_MP_TAC SUBRING_GENERATED_INC THEN ASM_REWRITE_TAC [SING_SUBSET, IN_SING], ASM_SIMP_TAC [SUBRING_GENERATED_ROOT_OF_UNITY_LINCOMB, FIELD_IMP_INTEGRAL_DOMAIN] THEN REWRITE_TAC [FORALL_IN_GSPEC, IN_UNIV] THEN MESON_TAC [], X_GEN_TAC (← q r"c:num->int") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num")] CYCLOTOMIC_FIELD_FREE_BASIS) THEN ASM_REWRITE_TAC [free_basis] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"\i. ring_of_int k ((c:num->int) i):A")) o (CONJUNCT2 o CONJUNCT2))) THEN ASM_REWRITE_TAC [I_THM, RING_OF_INT_IN_SUBFIELD_GENERATED, (← CONJUNCT2 SUBFIELD_GENERATED)] THEN ASM_SIMP_TAC [RING_OF_INT_EQ_0_CHAR_0]])

  let CYCLOTOMIC_FIELD_SUBFIELD_POW ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"x IN ring_carrier (k:A ring) /\ ring_carrier k INTER {x} SUBSET t
      ==> x IN t")
    prove
      r"!(k:A ring) z n d.
          number_field k /\ z IN ring_carrier k /\ ring_order k z = n /\
          ~(n = 0) /\ d divides n
          ==> number_field (subfield_generated k {ring_pow k z d}) /\
              ring_pow k z d IN
              ring_carrier (subfield_generated k {ring_pow k z d}) /\
              ring_order (subfield_generated k {ring_pow k z d})
                         (ring_pow k z d) = n DIV d /\
              ~(n DIV d = 0) /\
              subfield_generated (subfield_generated k {ring_pow k z d})
                                 {ring_pow k z d} =
              subfield_generated k {ring_pow k z d} /\
              subfield_generated (subfield_generated k {ring_pow k z d})
                {ring_0 (subfield_generated k {ring_pow k z d})} =
              subfield_generated k {ring_0 k}"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM ((X_CHOOSE_THEN (← q r"e:num") SUBST_ALL_TAC) o (GEN_REWRITE_RULE id [divides])) THEN RULE_ASSUM_TAC (REWRITE_RULE [MULT_EQ_0, DE_MORGAN_THM]) THEN SUBGOAL_THEN (← q r"ring_pow k (z:A) d IN ring_carrier(subfield_generated k {ring_pow k z d})") ASSUME_TAC THENL [MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [RING_POW, SUBFIELD_GENERATED_SUBSET_CARRIER], ALL_TAC] THEN ASM_SIMP_TAC [NUMBER_FIELD_SUBFIELD_GENERATED, SUBFIELD_GENERATED_IDEMPOT, PRIME_SUBFIELD_SUBFIELD_GENERATED, NUMBER_FIELD_IMP_FIELD, RING_ORDER_SUBFIELD_GENERATED, RING_ORDER_POW, DIVIDES_RMUL, DIVIDES_REFL, DIV_MULT])

  let CYCLOTOMIC_FIELD_NORM_SUB ← prove
    r"!(k:A ring) z n c.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = n /\ ~(n = 0) /\ subfield_generated k {z} = k /\
        c IN ring_carrier(subfield_generated k {ring_0 k})
        ==> algebra_norm (subfield_generated k {ring_0 k},k) I
              (ring_sub k c z) =
            poly_eval k (cyclotomic_poly k n) c"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"c:A")] NUMBER_FIELD_NORM_SUB_MINIMAL_POLYNOMIAL) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num")] CYCLOTOMIC_FIELD_DEGREE) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num")] CYCLOTOMIC_POLY_MINIMAL_POLYNOMIAL) THEN ASM_REWRITE_TAC [] THEN REPEAT (DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC [CYCLOTOMIC_POLY_DEG, (← CONJUNCT2 SUBFIELD_GENERATED)] THEN ASM_SIMP_TAC [FIELD_NONTRIVIAL, NUMBER_FIELD_IMP_FIELD] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_0 k}:A ring"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"n:num")] CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE) THEN REWRITE_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION, I_O_ID] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC)

  let CYCLOTOMIC_FIELD_NORM_SUB_POW ← prove
    r"!(k:A ring) z n d c.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = n /\ ~(n = 0) /\ subfield_generated k {z} = k /\
        d divides n /\ c IN ring_carrier(subfield_generated k {ring_0 k})
        ==> algebra_norm (subfield_generated k {ring_0 k},k) I
              (ring_sub k c (ring_pow k z d)) =
            ring_pow k (poly_eval k (cyclotomic_poly k (n DIV d)) c)
                       (phi n DIV phi(n DIV d))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num"), (← q r"d:num")] CYCLOTOMIC_FIELD_SUBFIELD_POW) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num")] CYCLOTOMIC_FIELD_DEGREE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ABBREV_TAC (← q r"K = subfield_generated k {ring_pow k (z:A) d}") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(c:A) IN ring_carrier K") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"K:A ring"), (← q r"{ring_0 K:A}")] RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN ASM_REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sub k c (ring_pow k (z:A) d) IN ring_carrier K") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"K:A ring"), (← q r"c:A"), (← q r"ring_pow k (z:A) d")] RING_SUB) THEN ASM_REWRITE_TAC [] THEN SUBST1_TAC (← SYM (← ASSUME (← q r"subfield_generated k {ring_pow k (z:A) d} = K"))) THEN REWRITE_TAC [RING_SUB_SUBFIELD_GENERATED], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"K:A ring"), (← q r"ring_sub k c (ring_pow k (z:A) d)")] NUMBER_FIELD_NORM_TOWER) THEN ANTS_TAC THENL [SUBST1_TAC (← SYM (← ASSUME (← q r"subfield_generated k {ring_pow k (z:A) d} = K"))) THEN ASM_SIMP_TAC [FIELD_EXTENSION_SUBFIELD_GENERATED, NUMBER_FIELD_IMP_FIELD], DISCH_THEN SUBST1_TAC] THEN BINOP_TAC THENL [MP_TAC (← ISPECL [(← q r"K:A ring"), (← q r"ring_pow k (z:A) d"), (← q r"n DIV d"), (← q r"c:A")] CYCLOTOMIC_FIELD_NORM_SUB) THEN ASM_REWRITE_TAC [] THEN SUBST1_TAC (← SYM (← ASSUME (← q r"subfield_generated k {ring_pow k (z:A) d} = K"))) THEN REWRITE_TAC [RING_SUB_SUBFIELD_GENERATED] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_pow k (z:A) d}"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"n DIV d")] CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE) THEN REWRITE_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION, I_O_ID] THEN DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [(← SYM th)])) THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_pow k (z:A) d}"), (← q r"k:A ring"), (← q r"c:A"), (← q r"I:A->A"), (← q r"cyclotomic_poly (subfield_generated k {ring_pow k (z:A) d})
                                    (n DIV d)")] POLY_EVAL_HOMOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION, I_O_ID, I_THM, CYCLOTOMIC_POLY_IN_CARRIER], MP_TAC (← ISPECL [(← q r"K:A ring"), (← q r"ring_pow k (z:A) d"), (← q r"n DIV d")] CYCLOTOMIC_FIELD_DEGREE) THEN MP_TAC (← ISPECL [(← q r"K:A ring"), (← q r"k:A ring"), (← q r"I:A->A")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN SUBST1_TAC (← SYM (← ASSUME (← q r"subfield_generated k {ring_pow k (z:A) d} = K"))) THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, NUMBER_FIELD_IMP_FIELD, RING_HOMOMORPHISM_SUBFIELD_INCLUSION] THEN DISCH_THEN (SUBST1_TAC o CONJUNCT2) THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC DIV_MULT THEN ASM_REWRITE_TAC [PHI_EQ_0]])

  let CYCLOTOMIC_FIELD_DISCRIMINANT_DERIV ← prove
    r"!(k:A ring) z n.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = n /\ ~(n = 0) /\ subfield_generated k {z} = k
        ==> ring_of_int k (number_field_discriminant k) =
            ring_mul k
              (ring_pow k (ring_neg k (ring_1 k)) ((phi n * (phi n - 1)) DIV 2))
              (algebra_norm (subfield_generated k {ring_0 k},k) I
                 (poly_eval k (poly_deriv k (cyclotomic_poly k n)) z))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num")] CYCLOTOMIC_FIELD_INTEGRAL_BASIS) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num")] CYCLOTOMIC_FIELD_DEGREE) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num")] CYCLOTOMIC_POLY_MINIMAL_POLYNOMIAL) THEN ASM_REWRITE_TAC [] THEN REPEAT DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"phi n"), (← q r"\i. ring_pow k (z:A) i")] NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"minimal_polynomial (subfield_generated k {ring_0 k},k) I (z:A)"), (← q r"extension_degree (subfield_generated k {ring_0 k},k:A ring) I")] NUMBER_FIELD_DISCRIMINANT_POWER_BASIS) THEN ASM_REWRITE_TAC [CYCLOTOMIC_POLY_DEG, (← CONJUNCT2 SUBFIELD_GENERATED)] THEN ASM_SIMP_TAC [FIELD_NONTRIVIAL, NUMBER_FIELD_IMP_FIELD] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_0 k}:A ring"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"n:num")] CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE) THEN REWRITE_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION, I_O_ID] THEN DISCH_THEN SUBST1_TAC THEN SIMP_TAC [POLY_EXTEND_EVALUATE, RING_HOMOMORPHISM_SUBFIELD_INCLUSION] THEN REWRITE_TAC [I_O_ID, (← GSYM poly_eval)] THEN REWRITE_TAC [poly_deriv, (← CONJUNCT2 SUBFIELD_GENERATED), RING_OF_NUM_SUBFIELD_GENERATED])

  -- @@RETURN BEGIN
  return { SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL_DIVIDES,
           SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL, CYCLOTOMIC_FIELD_RING_OF_INTEGERS,
           CYCLOTOMIC_FIELD_INTEGRAL_BASIS, CYCLOTOMIC_FIELD_SUBFIELD_POW,
           CYCLOTOMIC_FIELD_NORM_SUB, CYCLOTOMIC_FIELD_NORM_SUB_POW,
           CYCLOTOMIC_FIELD_DISCRIMINANT_DERIV }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- cyclotomic_integers.ml phrases from line 1313 to 1739                  -/
/- ---------------------------------------------------------------------- -/

structure CyclotomicIntegers03 where
  -- @@FIELDS
  CYCLOTOMIC_FIELD_DISCRIMINANT_PRIME_POWER : thm
  CYCLOTOMIC_FIELD_PRODUCT_BASIS : thm
  CYCLOTOMIC_FIELD_DISCRIMINANT_COMPOSITUM : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupCyclotomicIntegers03 [HolBase] (D : CyclotomicIntegersDeps) (BCyclotomicIntegers01 : CyclotomicIntegers01) (BCyclotomicIntegers02 : CyclotomicIntegers02) :
    ExceptT String IO CyclotomicIntegers03 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INTEGER_RULE, MESON_TAC,
        NUMBER_RULE, NUMBER_TAC, RING_RULE, TAUT, .. } := D
  let { ADD_CLAUSES, ADD_EQ_0, ADD_SUB, ALGEBRA_TRACE_NORM_IN_CARRIER,
        ALGEBRA_TRACE_PRODUCT_BASIS, ARITH, ARITH_EQ, CONG_SOLVE, COPRIME_SYM,
        CYCLOTOMIC_FIELD_DEGREE, CYCLOTOMIC_FIELD_FREE_BASIS, CYCLOTOMIC_POLY_EVAL_0,
        CYCLOTOMIC_POLY_EVAL_1_PRIME_POWER, CYCLOTOMIC_POLY_IN_CARRIER,
        CYCLOTOMIC_POLY_PRODUCT, CYCLOTOMIC_POLY_ROOT, DE_MORGAN_THM, DIVIDES_LMUL,
        DIVIDES_PRIMEPOW, DIVIDES_REFL, DIVIDES_RMUL, DIV_MULT, DIV_UNIQ, EQ_EXP, EVEN,
        EVEN_EXISTS, EVEN_MULT, EVEN_OR_ODD, EVEN_SUB, EXP_1, EXP_ADD, EXP_EQ_0,
        EXP_MULT, EXTENSION, EXTENSION_LINCOMB_SUM, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_SUBFIELD_GENERATED, FINITE_DIVISORS, FINITE_NUMSEG_LT, FORALL_IN_GSPEC,
        FREE_BASIS_INDEPENDENT, FREE_BASIS_INTEGER_RING_SUBRING_GENERATED,
        FREE_BASIS_SPANNING_DEGREE, IMP_IMP, INTEGER_RING, INT_EQ_MUL_RCANCEL,
        INT_MUL_ASSOC, INT_OF_NUM_EQ, INT_OF_NUM_MUL, INT_OF_NUM_POW, INT_POW_NEG,
        INT_POW_ONE, IN_ELIM_THM, IN_INSERT, .. } := D.core1
  let { IN_SING, IN_UNIV, I_THM, LEFT_ADD_DISTRIB, LE_EXP, LE_TRANS, MULT_AC,
        MULT_ASSOC, MULT_CLAUSES, MULT_EQ_0, MULT_SYM,
        NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_NORM_MUL, NUMBER_FIELD_NORM_RATIONAL, ODD_EXISTS,
        PHI_MULTIPLICATIVE, PHI_PRIME, PHI_PRIMEPOW_ALT, POLY_DERIV_1, POLY_DERIV_MUL,
        POLY_DERIV_SUB, POLY_DERIV_VAR_POW, POLY_EVAL, POLY_EVAL_0, POLY_EVAL_1,
        POLY_EVAL_ADD, POLY_EVAL_CONST, POLY_EVAL_MUL, POLY_EVAL_POW, POLY_EVAL_SUB,
        POLY_EVAL_VAR, POLY_RING_CLAUSES, PRIME_GE_2, RIGHT_ADD_DISTRIB, RING_0,
        RING_1, RING_ADD_RZERO, RING_CARRIER_SUBFIELD_GENERATED_SUBSET, RING_DET_EQ,
        RING_DET_KRONECKER_MOD_DIV, RING_HOMOMORPHISM_INTEGER_RING_OF_INT,
        RING_HOMOMORPHISM_SUBFIELD_INCLUSION, .. } := D.core2
  let { RING_MUL, RING_MUL_ASSOC, RING_MUL_LID, RING_MUL_LZERO, RING_NEG, RING_OF_INT,
        RING_OF_INTEGERS_FREE_BASIS_FIELD, RING_OF_INT_1, RING_OF_INT_EQ,
        RING_OF_INT_EQ_0_CHAR_0, RING_OF_INT_MUL, RING_OF_INT_NEG, RING_OF_INT_OF_NUM,
        RING_OF_INT_POW, RING_OF_INT_SUBFIELD_GENERATED, RING_OF_NUM,
        RING_OF_NUM_SUBFIELD_GENERATED, RING_ORDER_POW, RING_POLYNOMIAL,
        RING_POLYNOMIAL_0, RING_POLYNOMIAL_1, RING_POLYNOMIAL_CONST,
        RING_POLYNOMIAL_IMP_POWERSERIES, RING_POLYNOMIAL_MUL,
        RING_POLYNOMIAL_POLY_DERIV, RING_POLYNOMIAL_POW, RING_POLYNOMIAL_SUB,
        RING_POLYNOMIAL_VAR, RING_POW, RING_POW_ADD, RING_POW_EQ_1, RING_POW_EQ_GEN,
        RING_POW_MUL, RING_POW_SUBFIELD_GENERATED, RING_POW_SUBRING_GENERATED,
        RING_PRODUCT_CLAUSES, RING_SUB, RING_SUB_RZERO, RING_SUM, RING_SUM_EQ,
        RING_SUM_MUL_MOD_DIV, SING_SUBSET, SKOLEM_THM, SUBFIELD_GENERATED,
        SUBRING_GENERATED_BY_SUBRING_GENERATED, SUBRING_GENERATED_INC,
        SUBRING_SUBRING_GENERATED, SUBSET, SUC_SUB1, basis_discriminant, free_basis,
        number_field, ring_pow, .. } := D.core3
  let { SUBRING_GENERATED_ROOT_OF_UNITY_LINCOMB, .. } := BCyclotomicIntegers01
  let { CYCLOTOMIC_FIELD_DISCRIMINANT_DERIV, CYCLOTOMIC_FIELD_INTEGRAL_BASIS,
        CYCLOTOMIC_FIELD_NORM_SUB, CYCLOTOMIC_FIELD_NORM_SUB_POW,
        CYCLOTOMIC_FIELD_RING_OF_INTEGERS, CYCLOTOMIC_FIELD_SUBFIELD_POW, .. } := BCyclotomicIntegers02
  -- @@SCOPE END

  let CYCLOTOMIC_FIELD_DISCRIMINANT_PRIME_POWER ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let v1 ← GSYM RING_POLYNOMIAL
    let p2 ← prove r"!(r:A ring) f g x.
        f IN ring_carrier(poly_ring r (:1)) /\
        g IN ring_carrier(poly_ring r (:1)) /\
        x IN ring_carrier r /\ poly_eval r f x = ring_0 r
        ==> poly_eval r (poly_deriv r (poly_mul r f g)) x =
            ring_mul r (poly_eval r (poly_deriv r f) x) (poly_eval r g x)" (REWRITE_TAC [v1] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [POLY_DERIV_MUL, RING_POLYNOMIAL_IMP_POWERSERIES, POLY_EVAL_ADD, POLY_EVAL_MUL, RING_POLYNOMIAL_MUL, RING_POLYNOMIAL_POLY_DERIV, RING_MUL_LZERO, POLY_EVAL, RING_ADD_RZERO, RING_MUL])
    let deriv_lemma := p2
    let q3 ← q r"0"
    let q4 ← q r"1"
    let q5 ← q r"SUC(2 * a) DIV 2 = a /\
                  (SUC(2 * a) * (SUC(2 * a) - 1)) DIV 2 = SUC(2 * a) * a"
    let q6 ← q r"~q ==> (p \/ q <=> p)"
    let r7 ← TAUT q6
    let q8 ← q r"a = 0"
    let v9 ← GSYM MULT_ASSOC
    let q10 ← q r"m:num"
    let v11 ← SPEC q10 EVEN_OR_ODD
    let v12 ← REWRITE_RULE [EVEN_EXISTS, ODD_EXISTS] v11
    let q13 ← q r"a:num"
    let p14 ← prove r"!m. EVEN((m * (m - 1)) DIV 2) <=> EVEN(m DIV 2)" (GEN_TAC THEN DISJ_CASES_THEN (X_CHOOSE_THEN q13 SUBST1_TAC) v12 THENL [REWRITE_TAC [v9] THEN SIMP_TAC [DIV_MULT, ARITH_EQ, EVEN_MULT, EVEN_SUB, ARITH] THEN ASM_CASES_TAC q8 THEN ASM_REWRITE_TAC [ARITH] THEN MATCH_MP_TAC r7 THEN ASM_ARITH_TAC, SUBGOAL_THEN q5 (fun th => REWRITE_TAC [th]) THENL [CONJ_TAC THEN MATCH_MP_TAC DIV_UNIQ THENL [EXISTS_TAC q4 THEN ARITH_TAC, EXISTS_TAC q3 THEN REWRITE_TAC [SUC_SUB1, ADD_CLAUSES, ARITH] THEN REWRITE_TAC [MULT_AC]], REWRITE_TAC [EVEN_MULT, EVEN] THEN REWRITE_TAC [EVEN_MULT, ARITH]]])
    let parity_lemma := p14
    let q15 ← q r"2 <= p ==> ~(p = 0)"
    let r16 ← ARITH_RULE q15
    let v17 ← GSYM INT_OF_NUM_MUL
    let q18 ← q r"(q + 2) * (v + 1) - v - 2 = q * v + q + v"
    let r19 ← ARITH_RULE q18
    let q20 ← q r"(q + 2) - 1 = q + 1"
    let r21 ← ARITH_RULE q20
    let q22 ← q r"p - 2"
    let q23 ← q r"?q. p = q + 2"
    let v24 ← GSYM EXP_MULT
    let v25 ← GSYM EXP_ADD
    let q26 ← q r"(p EXP (v + 1)) EXP (p EXP v * (p - 1)) =
    p EXP (p EXP v * (p * (v + 1) - v - 2)) * p EXP (p EXP v)"
    let v35 ← GSYM RING_OF_INT_EQ
    let q40 ← q r"!x y:int. (x == y) (mod &0) ==> x = y"
    let r41 ← INTEGER_RULE q40
    let q42 ← q r"number_field_discriminant (k:A ring) * &p pow (p EXP v) =
    (-- &1) pow ((phi (p EXP (v + 1)) * (phi (p EXP (v + 1)) - 1)) DIV 2) *
    &(p EXP (v + 1)) pow phi (p EXP (v + 1))"
    let v43 ← CONJUNCT2 SUBFIELD_GENERATED
    let q44 ← q r"subfield_generated k {ring_0 k}:A ring"
    let v45 ← ISPEC q44 RING_0
    let q46 ← q r"ring_0 k:A"
    let q47 ← q r"p EXP (v + 1)"
    let q48 ← q r"z:A"
    let q49 ← q r"k:A ring"
    let v50 ← ISPECL [q49, q48, q47, q46] CYCLOTOMIC_FIELD_NORM_SUB
    let q51 ← q r"ring_sub k (ring_0 k) z IN ring_carrier k /\
      ring_sub k (ring_1 k) (ring_pow k z (p EXP v)) IN ring_carrier (k:A ring)"
    let q52 ← q r"p EXP (v + 1)"
    let q53 ← q r"subfield_generated k {ring_0 k}:A ring"
    let v54 ← ISPECL [q53, q52] RING_OF_NUM
    let q55 ← q r"ring_of_num k (p EXP (v + 1)):A"
    let q56 ← q r"k:A ring"
    let v57 ← ISPECL [q56, q55] NUMBER_FIELD_NORM_RATIONAL
    let q62 ← q r"algebra_norm (subfield_generated (k:A ring) {ring_0 k},k) I"
    let q63 ← q r"1"
    let q64 ← q r"p:num"
    let q65 ← q r"k:A ring"
    let v66 ← ISPECL [q65, q64, q63] CYCLOTOMIC_POLY_EVAL_1_PRIME_POWER
    let v67 ← CONJUNCT2 SUBFIELD_GENERATED
    let q68 ← q r"subfield_generated k {ring_0 k}:A ring"
    let v69 ← ISPEC q68 RING_1
    let q70 ← q r"ring_1 k:A"
    let q71 ← q r"p EXP v"
    let q72 ← q r"p EXP (v + 1)"
    let q73 ← q r"z:A"
    let q74 ← q r"k:A ring"
    let v75 ← ISPECL [q74, q73, q72, q71, q70] CYCLOTOMIC_FIELD_NORM_SUB_POW
    let q76 ← q r"2 <= p ==> ~(p = 0)"
    let r77 ← ARITH_RULE q76
    let q78 ← q r"p EXP (v + 1) DIV p EXP v = p /\
          phi(p EXP (v + 1)) DIV phi p = p EXP v"
    let q79 ← q r"algebra_norm (subfield_generated k {ring_0 k},k) I
          (ring_sub k (ring_1 k) (ring_pow k z (p EXP v))) =
        ring_pow k (ring_of_num (k:A ring) p) (p EXP v)"
    let q80 ← q r"2 <= n ==> SUC(n - 1) = n"
    let r81 ← ARITH_RULE q80
    let v82 ← CONJUNCT2 ring_pow
    let v83 ← GSYM v82
    let q84 ← q r"ring_pow k (z:A) (p EXP (v + 1) - 1)"
    let q85 ← q r"ring_mul r a w = ring_mul r d (ring_sub r x (ring_1 r)) /\
          ring_mul r z w = ring_1 r
          ==> a = ring_mul r (ring_sub r (ring_0 r) z)
                    (ring_mul r d (ring_sub r (ring_1 r) (x:A)))"
    let r86 ← RING_RULE q85
    let v87 ← REWRITE_RULE [IMP_IMP] r86
    let v88 ← GEN_ALL v87
    let q89 ← q r"ring_of_num k (p EXP (v + 1)) =
        ring_mul k (ring_sub k (ring_0 k) z)
          (ring_mul k D (ring_sub k (ring_1 k) (ring_pow k (z:A) (p EXP v))))"
    let v90 ← GSYM RING_POLYNOMIAL
    let q91 ← q r"~(p EXP (v + 1) IN {d | d divides p EXP v})"
    let q92 ← q r"i <= v + 1 <=> i = v + 1 \/ i <= v"
    let r93 ← ARITH_RULE q92
    let q94 ← q r"{d | d divides p EXP (v + 1)} =
            p EXP (v + 1) INSERT {d | d divides p EXP v}"
    let q95 ← q r"~(p = 0) /\ ~(p = 1)"
    let q96 ← q r"p EXP (v + 1)"
    let q97 ← q r"k:A ring"
    let v98 ← ISPECL [q97, q96] CYCLOTOMIC_POLY_PRODUCT
    let q99 ← q r"p EXP v"
    let q100 ← q r"k:A ring"
    let v101 ← ISPECL [q100, q99] CYCLOTOMIC_POLY_PRODUCT
    let q102 ← q r"\P. poly_eval k (poly_deriv k P) (z:A)"
    let q103 ← q r"poly_sub k (poly_pow k (poly_var k one) (p EXP (v + 1))) (poly_1 k) =
          poly_mul k (cyclotomic_poly k (p EXP (v + 1)))
            (poly_sub k (poly_pow k (poly_var k one) (p EXP v))
                      (poly_1 (k:A ring)))"
    let q104 ← q r"ring_mul k (ring_of_num k (p EXP (v + 1)))
          (ring_pow k z (p EXP (v + 1) - 1)) =
        ring_mul k D (ring_sub k (ring_pow k z (p EXP v)) (ring_1 (k:A ring)))"
    let q105 ← q r"ring_pow k (ring_of_num k (p EXP (v + 1))) (phi (p EXP (v + 1))) =
    ring_mul k (algebra_norm (subfield_generated k {ring_0 k},k) I D)
               (ring_pow k (ring_of_num (k:A ring) p) (p EXP v))"
    let q106 ← q r"algebra_norm (subfield_generated k {ring_0 k},k) I D IN
    ring_carrier (k:A ring)"
    let q107 ← q r"(D:A) IN ring_carrier k"
    let q108 ← q r"D = poly_eval k (poly_deriv k (cyclotomic_poly k (p EXP (v + 1))))
                    (z:A)"
    let q109 ← q r"p EXP (v + 1)"
    let q110 ← q r"z:A"
    let q111 ← q r"k:A ring"
    let v112 ← ISPECL [q111, q110, q109] CYCLOTOMIC_FIELD_DISCRIMINANT_DERIV
    let q113 ← q r"p EXP (v + 1)"
    let q114 ← q r"z:A"
    let q115 ← q r"k:A ring"
    let v116 ← ISPECL [q115, q114, q113] CYCLOTOMIC_FIELD_DEGREE
    let q117 ← q r"p EXP 1"
    let q118 ← q r"~(p EXP (v + 1) = 0) /\ 2 <= p EXP (v + 1) /\ 2 <= p"
    prove
      r"!(k:A ring) z p v.
          number_field k /\ z IN ring_carrier k /\ prime p /\
          ring_order k z = p EXP (v + 1) /\ subfield_generated k {z} = k
          ==> number_field_discriminant k =
              (-- &1) pow (phi(p EXP (v + 1)) DIV 2) *
              &p pow (p EXP v * (p * (v + 1) - v - 2))"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN SUBGOAL_THEN q118 STRIP_ASSUME_TAC THENL [FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_GE_2)) THEN ASM_REWRITE_TAC [EXP_EQ_0] THEN CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN TRANS_TAC LE_TRANS q117 THEN ASM_REWRITE_TAC [EXP_1, LE_EXP] THEN ASM_ARITH_TAC, ALL_TAC] THEN MP_TAC v116 THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC v112 THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC q108 THEN SUBGOAL_THEN q107 ASSUME_TAC THENL [EXPAND_TAC "D" THEN REWRITE_TAC [POLY_EVAL], ALL_TAC] THEN DISCH_TAC THEN SUBGOAL_THEN q106 ASSUME_TAC THENL [MESON_TAC [ALGEBRA_TRACE_NORM_IN_CARRIER, RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN q105 ASSUME_TAC THENL [SUBGOAL_THEN q104 ASSUME_TAC THENL [SUBGOAL_THEN q103 (MP_TAC o (AP_TERM q102)) THENL [MP_TAC v101 THEN MP_TAC v98 THEN SUBGOAL_THEN q95 STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC, ASM_REWRITE_TAC [EXP_EQ_0]] THEN SUBGOAL_THEN q94 SUBST1_TAC THENL [REWRITE_TAC [EXTENSION, IN_INSERT, IN_ELIM_THM] THEN ASM_SIMP_TAC [DIVIDES_PRIMEPOW] THEN MESON_TAC [r93], ALL_TAC] THEN SUBGOAL_THEN q91 ASSUME_TAC THENL [ASM_SIMP_TAC [IN_ELIM_THM, DIVIDES_PRIMEPOW, EQ_EXP] THEN ARITH_TAC, ALL_TAC] THEN ASM_SIMP_TAC [RING_PRODUCT_CLAUSES, FINITE_DIVISORS, EXP_EQ_0, CYCLOTOMIC_POLY_IN_CARRIER] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [POLY_RING_CLAUSES], ALL_TAC] THEN REWRITE_TAC [] THEN wPart (rand o lhand) (lhand o rand) deriv_lemma THEN ASM_SIMP_TAC [CYCLOTOMIC_POLY_IN_CARRIER, CYCLOTOMIC_POLY_ROOT, FIELD_IMP_INTEGRAL_DOMAIN, v90, RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_POW, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_1] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [POLY_DERIV_SUB, POLY_DERIV_VAR_POW, POLY_DERIV_1, RING_POLYNOMIAL_IMP_POWERSERIES, RING_POLYNOMIAL_POW, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_1] THEN ASM_SIMP_TAC [POLY_EVAL_SUB, POLY_EVAL_MUL, POLY_EVAL_CONST, POLY_EVAL_POW, POLY_EVAL_VAR, POLY_EVAL_0, POLY_EVAL_1, RING_POLYNOMIAL_MUL, RING_POLYNOMIAL_CONST, RING_POLYNOMIAL_POW, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_0, RING_POLYNOMIAL_1, RING_OF_NUM, RING_SUB_RZERO, RING_MUL, RING_POW], ALL_TAC] THEN SUBGOAL_THEN q89 ASSUME_TAC THENL [MATCH_MP_TAC v88 THEN EXISTS_TAC q84 THEN ASM_SIMP_TAC [RING_OF_NUM, RING_POW] THEN REWRITE_TAC [v83] THEN ASM_SIMP_TAC [r81, RING_POW_EQ_1, DIVIDES_REFL], ALL_TAC] THEN SUBGOAL_THEN q79 ASSUME_TAC THENL [SUBGOAL_THEN q78 STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [PHI_PRIMEPOW_ALT, PHI_PRIME, ADD_EQ_0, ARITH_EQ, ADD_SUB] THEN REWRITE_TAC [EXP_ADD, EXP_1] THEN ASM_SIMP_TAC [DIV_MULT, EXP_EQ_0, r77] THEN ONCE_REWRITE_TAC [MULT_SYM] THEN MATCH_MP_TAC DIV_MULT THEN ASM_ARITH_TAC, ALL_TAC] THEN MP_TAC v75 THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [MP_TAC v69 THEN REWRITE_TAC [v67, EXP_ADD, EXP_1] THEN MESON_TAC [DIVIDES_RMUL, DIVIDES_REFL], DISCH_THEN SUBST1_TAC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN MP_TAC v66 THEN ASM_REWRITE_TAC [EXP_1, ARITH_EQ], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o ((AP_TERM q62) o (checkM (fun th => (do let z61 ← (q r"ring_of_num (k:A ring) (p EXP (v + 1))"); let z60 ← (do let z58 ← (do let z59 ← (pure th); pure (concl z59)); liftExcept (lhs z58)); pure (z60 == z61)))))) THEN MP_TAC v57 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN MP_TAC v54 THEN REWRITE_TAC [RING_OF_NUM_SUBFIELD_GENERATED], ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC] THEN SUBGOAL_THEN q51 STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_SUB, RING_0, RING_1, RING_POW], ALL_TAC] THEN ASM_SIMP_TAC [NUMBER_FIELD_NORM_MUL, RING_MUL] THEN MP_TAC v50 THEN MP_TAC v45 THEN ASM_SIMP_TAC [v43, CYCLOTOMIC_POLY_EVAL_0] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [RING_MUL_LID, RING_MUL, RING_POW, RING_OF_NUM], ALL_TAC] THEN SUBGOAL_THEN q42 MP_TAC THENL [MATCH_MP_TAC r41 THEN FIRST_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z39 ← (q r"ring_char (k:A ring)"); let z38 ← (do let z36 ← (do let z37 ← (pure th); pure (concl z37)); liftExcept (lhs z36)); pure (z38 == z39)))))) THEN REWRITE_TAC [v35] THEN REWRITE_TAC [RING_OF_INT_MUL, RING_OF_INT_POW, RING_OF_INT_NEG, RING_OF_INT_1, RING_OF_INT_OF_NUM] THEN FIRST_X_ASSUM (SUBST1_TAC o (checkM (fun th => (do let z34 ← (q r"ring_pow k (ring_of_num k (p EXP (v + 1)))                   (phi (p EXP (v + 1))):A"); let z33 ← (do let z31 ← (do let z32 ← (pure th); pure (concl z32)); liftExcept (lhs z31)); pure (z33 == z34))))) THEN FIRST_X_ASSUM (SUBST1_TAC o (checkM (fun th => (do let z30 ← (q r"ring_of_int k (number_field_discriminant (k:A ring))"); let z29 ← (do let z27 ← (do let z28 ← (pure th); pure (concl z28)); liftExcept (lhs z27)); pure (z29 == z30))))) THEN ASM_SIMP_TAC [RING_MUL_ASSOC, RING_POW, RING_NEG, RING_1, RING_OF_NUM], ALL_TAC] THEN REWRITE_TAC [INT_POW_NEG, INT_POW_ONE, parity_lemma] THEN ASM_SIMP_TAC [PHI_PRIMEPOW_ALT, ADD_EQ_0, ARITH_EQ, ADD_SUB] THEN SUBGOAL_THEN q26 ASSUME_TAC THENL [REWRITE_TAC [v25, v24] THEN AP_TERM_TAC THEN SUBGOAL_THEN q23 (CHOOSE_THEN SUBST1_TAC) THENL [EXISTS_TAC q22 THEN ASM_ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [r21, r19] THEN REWRITE_TAC [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_CLAUSES] THEN ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [INT_OF_NUM_POW] THEN ASM_REWRITE_TAC [v17] THEN REWRITE_TAC [INT_MUL_ASSOC] THEN ASM_SIMP_TAC [INT_EQ_MUL_RCANCEL, INT_OF_NUM_EQ, EXP_EQ_0, r16])

  let CYCLOTOMIC_FIELD_PRODUCT_BASIS ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"j:num"
    let q2 ← q r"x:A"
    let q3 ← q r"subring_generated k {x:A}"
    let v4 ← ISPECL [q3, q2, q1] RING_POW
    let q5 ← q r"ring_pow k (x:A) j IN ring_carrier(subring_generated k {x})"
    let q6 ← q r"j:num"
    let q7 ← q r"p /\ (p ==> q) ==> p /\ q"
    let r8 ← TAUT q7
    let p9 ← prove r"!(k:A ring) x m.
          integral_domain k /\ x IN ring_carrier k /\
          ring_order k x = m /\ ~(m = 0)
          ==> ring_carrier (subring_generated k {x}) =
              {ring_sum k {i | i < phi m}
                 (\i. ring_mul k (ring_of_int k (c i)) (ring_pow k x i)) |
               c IN (:num->int)} /\
              !j. ?c. ring_pow k x j =
                      ring_sum k {i | i < phi m}
                        (\i. ring_mul k (ring_of_int k (c i))
                                        (ring_pow k x i))" (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC r8 THEN CONJ_TAC THENL [MATCH_MP_TAC SUBRING_GENERATED_ROOT_OF_UNITY_LINCOMB THEN ASM_REWRITE_TAC [], DISCH_TAC] THEN X_GEN_TAC q6 THEN SUBGOAL_THEN q5 MP_TAC THENL [MP_TAC v4 THEN REWRITE_TAC [RING_POW_SUBRING_GENERATED] THEN DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC SUBRING_GENERATED_INC THEN ASM_REWRITE_TAC [SING_SUBSET, IN_SING], ASM_REWRITE_TAC [IN_ELIM_THM, IN_UNIV]])
    let span_lemma := p9
    let q10 ← q r"\t. ring_of_int k ((c:num->int) t):A"
    let q11 ← q r"B:num->A"
    let q12 ← q r"P:num * R"
    let q13 ← q r"k:A ring"
    let q14 ← q r"q:A ring"
    let q15 ← q r"I:A->A"
    let v16 ← ISPECL [q15, q14, q13, q12, q11, q10] FREE_BASIS_INDEPENDENT
    let q17 ← q r"c:num->int"
    let q18 ← q r"B:num->A"
    let q19 ← q r"C:num->num->int"
    let q20 ← q r"a:num->int"
    let q21 ← q r"{t:num | t < P * R}"
    let q22 ← q r"{i:num | i < P * R}"
    let q23 ← q r"k:A ring"
    let q24 ← q r"integer_ring"
    let q25 ← q r"ring_of_int k:int->A"
    let v26 ← ISPECL [q25, q24, q23, q22, q21, q20, q19, q18] EXTENSION_LINCOMB_SUM
    let q27 ← q r"\t. ring_sum integer_ring {i | i < P * R}
            (\i. ring_mul integer_ring ((a:num->int) i)
                   ((C:num->num->int) i t))"
    let q28 ← q r"a:num->int"
    let q29 ← q r"(z:A) IN ring_carrier k"
    let v30 ← ASSUME q29
    let q31 ← q r"(B:num->A) t = ring_pow k z (s * t MOD P + r * t DIV P)"
    let q32 ← q r"t:num"
    let v39 ← GSYM SUBRING_GENERATED_BY_SUBRING_GENERATED
    let q40 ← q r"phi s = R"
    let v41 ← ASSUME q40
    let q42 ← q r"phi r = P"
    let v43 ← ASSUME q42
    let q44 ← q r"coprime(r:num,s)"
    let v45 ← ASSUME q44
    let v46 ← MATCH_MP PHI_MULTIPLICATIVE v45
    let q47 ← q r"r:num * s"
    let q48 ← q r"z:A"
    let q49 ← q r"k:A ring"
    let v50 ← ISPECL [q49, q48, q47] span_lemma
    let q51 ← q r"B:num->A"
    let q52 ← q r"\i t. ring_of_int k ((C:num->num->int) i t):A"
    let q53 ← q r"c:num->A"
    let q54 ← q r"{t:num | t < P * R}"
    let q55 ← q r"{i:num | i < P * R}"
    let q56 ← q r"k:A ring"
    let q57 ← q r"q:A ring"
    let q58 ← q r"I:A->A"
    let v59 ← ISPECL [q58, q57, q56, q55, q54, q53, q52, q51] EXTENSION_LINCOMB_SUM
    let q60 ← q r"\t. ring_sum q {i | i < P * R}
            (\i. ring_mul q ((c:num->A) i)
                          (ring_of_int k ((C:num->num->int) i t)))"
    let q61 ← q r"c:num->A"
    let q65 ← q r"x:A"
    let q66 ← q r"x:A"
    let q67 ← q r"free_basis (q,k) I (P * R) (B:num->A)"
    let q68 ← q r"!t. (B:num->A) t IN ring_carrier k"
    let q69 ← q r"field(k:A ring)"
    let v70 ← ASSUME q69
    let v71 ← CONJUNCT2 SUBFIELD_GENERATED
    let q72 ← q r"subfield_generated k {ring_0 k:A} = q"
    let v73 ← ASSUME q72
    let v74 ← SYM v73
    let q75 ← q r"field q /\ ring_homomorphism(q,k) (I:A->A) /\
    (!x. ring_of_int k x IN ring_carrier q) /\ ring_0 q = ring_0 k"
    let q76 ← q r"C:num->num->int"
    let q77 ← q r"ring_mul r (ring_mul r a x) (ring_mul r b y) =
      ring_mul r (ring_mul r a b) (ring_mul r x (y:A))"
    let r78 ← RING_RULE q77
    let q79 ← q r"t:num"
    let q80 ← q r"\t. (a:num->int) (t MOD P) * b (t DIV P)"
    let q81 ← q r"phi s = R"
    let v82 ← ASSUME q81
    let q83 ← q r"phi r = P"
    let v84 ← ASSUME q83
    let q85 ← q r"u * j:num"
    let q86 ← q r"a:num->int"
    let q87 ← q r"r:num"
    let q88 ← q r"eta:A"
    let q89 ← q r"k:A ring"
    let v90 ← ISPECL [q89, q88, q87] span_lemma
    let q91 ← q r"v * j:num"
    let q92 ← q r"b:num->int"
    let q93 ← q r"s:num"
    let q94 ← q r"w:A"
    let q95 ← q r"k:A ring"
    let v96 ← ISPECL [q95, q94, q93] span_lemma
    let q97 ← q r"n:num"
    let q98 ← q r"r * s:num"
    let q99 ← q r"(s * u + r * v == 1) (mod (r * s))"
    let v100 ← GSYM RING_POW_ADD
    let v101 ← GSYM RING_POW_MUL
    let q102 ← q r"ring_pow k (z:A) j = ring_mul k (ring_pow k eta (u * j))
                                       (ring_pow k w (v * j))"
    let q103 ← q r"!r s u v. coprime(r,s) /\ (s * u == 1) (mod r) /\
                  (r * v == 1) (mod s)
                  ==> (s * u + r * v == 1) (mod (r * s))"
    let v104 ← ExceptT.mk (NUMBER_RULE q103)
    let q105 ← q r"v:num"
    let q106 ← q r"u:num"
    let q107 ← q r"u:num"
    let q108 ← q r"v:num"
    let q109 ← q r"coprime(s:num,r)"
    let q110 ← q r"s:num"
    let q111 ← q r"1"
    let q112 ← q r"r:num"
    let v113 ← SPECL [q112, q111, q110] CONG_SOLVE
    let q114 ← q r"r:num"
    let q115 ← q r"1"
    let q116 ← q r"s:num"
    let v117 ← SPECL [q116, q115, q114] CONG_SOLVE
    let q118 ← q r"?u v. (s * u + r * v == 1) (mod (r * s))"
    let q119 ← q r"j:num"
    let q120 ← q r"!j. ?c. ring_pow k (z:A) j =
            ring_sum k {t | t < P * R}
              (\t:num. ring_mul k (ring_of_int k (c t)) (B t))"
    let q121 ← q r"B = \t. ring_mul k (ring_pow k (eta:A) (t MOD P))
                        (ring_pow k w (t DIV P))"
    let q122 ← q r"(eta:A) IN ring_carrier k /\ (w:A) IN ring_carrier k"
    let q123 ← q r"q = subfield_generated k {ring_0 k:A}"
    let q124 ← q r"R = phi s"
    let q125 ← q r"P = phi r"
    let q126 ← q r"w = ring_pow k (z:A) r"
    let q127 ← q r"eta = ring_pow k (z:A) s"
    let q128 ← q r"(r * s) DIV s = r /\ (r * s) DIV r = s"
    let q129 ← q r"r:num * s"
    let q130 ← q r"z:A"
    let q131 ← q r"k:A ring"
    let v132 ← ISPECL [q131, q130, q129] CYCLOTOMIC_FIELD_DEGREE
    let q133 ← q r"r:num * s"
    let q134 ← q r"z:A"
    let q135 ← q r"k:A ring"
    let v136 ← ISPECL [q135, q134, q133] CYCLOTOMIC_FIELD_RING_OF_INTEGERS
    let q137 ← q r"r:num * s"
    let q138 ← q r"z:A"
    let q139 ← q r"k:A ring"
    let v140 ← ISPECL [q139, q138, q137] CYCLOTOMIC_FIELD_FREE_BASIS
    let q141 ← q r"r:num"
    let q142 ← q r"z:A"
    let q143 ← q r"k:A ring"
    let v144 ← ISPECL [q143, q142, q141] RING_ORDER_POW
    let q145 ← q r"s:num"
    let q146 ← q r"z:A"
    let q147 ← q r"k:A ring"
    let v148 ← ISPECL [q147, q146, q145] RING_ORDER_POW
    prove
      r"!(k:A ring) z r s.
          number_field k /\ z IN ring_carrier k /\
          ring_order k z = r * s /\ ~(r * s = 0) /\ coprime(r,s) /\
          subfield_generated k {z} = k
          ==> free_basis (integer_ring,ring_of_integers k) (ring_of_int k)
                (phi r * phi s)
                (\t. ring_mul k (ring_pow k (ring_pow k z s) (t MOD phi r))
                                (ring_pow k (ring_pow k z r) (t DIV phi r)))"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN RULE_ASSUM_TAC (REWRITE_RULE [MULT_EQ_0, DE_MORGAN_THM]) THEN MP_TAC v148 THEN MP_TAC v144 THEN MP_TAC v140 THEN MP_TAC v136 THEN MP_TAC v132 THEN ASM_SIMP_TAC [MULT_EQ_0, DIVIDES_LMUL, DIVIDES_RMUL, DIVIDES_REFL, PHI_MULTIPLICATIVE] THEN SUBGOAL_THEN q128 (fun th => REWRITE_TAC [th]) THENL [ONCE_REWRITE_TAC [MULT_SYM] THEN ASM_SIMP_TAC [DIV_MULT] THEN ONCE_REWRITE_TAC [MULT_SYM] THEN ASM_SIMP_TAC [DIV_MULT], ALL_TAC] THEN ABBREV_TAC q127 THEN ABBREV_TAC q126 THEN ABBREV_TAC q125 THEN ABBREV_TAC q124 THEN ABBREV_TAC q123 THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN q122 STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["eta", "w"] THEN ASM_SIMP_TAC [RING_POW], ALL_TAC] THEN ABBREV_TAC q121 THEN SUBGOAL_THEN q120 MP_TAC THENL [X_GEN_TAC q119 THEN SUBGOAL_THEN q118 STRIP_ASSUME_TAC THENL [MP_TAC v117 THEN MP_TAC v113 THEN SUBGOAL_THEN q109 (fun th => ASM_REWRITE_TAC [th]) THENL [ASM_MESON_TAC [COPRIME_SYM], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_TAC q108) THEN DISCH_THEN (X_CHOOSE_TAC q107) THEN MAP_EVERY EXISTS_TAC [q106, q105] THEN MATCH_MP_TAC v104 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN q102 SUBST1_TAC THENL [MAP_EVERY EXPAND_TAC ["eta", "w"] THEN ASM_SIMP_TAC [v101, v100, RING_POW_EQ_GEN, MULT_EQ_0] THEN UNDISCH_TAC q99 THEN SPEC_TAC (q98, q97) THEN NUMBER_TAC, ALL_TAC] THEN MP_TAC v96 THEN ANTS_TAC THENL [ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN], ALL_TAC] THEN DISCH_THEN ((X_CHOOSE_THEN q92 SUBST1_TAC) o ((SPEC q91) o CONJUNCT2)) THEN MP_TAC v90 THEN ANTS_TAC THENL [ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN], ALL_TAC] THEN DISCH_THEN ((X_CHOOSE_THEN q86 SUBST1_TAC) o ((SPEC q85) o CONJUNCT2)) THEN REWRITE_TAC [v84, v82] THEN EXISTS_TAC q80 THEN wPart lhand (lhand o rand) RING_SUM_MUL_MOD_DIV THEN ASM_SIMP_TAC [RING_MUL, RING_POW, RING_OF_INT] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC q79 THEN DISCH_TAC THEN EXPAND_TAC "B" THEN REWRITE_TAC [RING_OF_INT_MUL] THEN MATCH_MP_TAC r78 THEN ASM_SIMP_TAC [RING_OF_INT, RING_POW], ALL_TAC] THEN REWRITE_TAC [SKOLEM_THM] THEN DISCH_THEN (X_CHOOSE_TAC q76) THEN SUBGOAL_THEN q75 STRIP_ASSUME_TAC THENL [SUBST1_TAC v74 THEN SIMP_TAC [FIELD_SUBFIELD_GENERATED, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, v71, v70] THEN MESON_TAC [RING_OF_INT, RING_OF_INT_SUBFIELD_GENERATED], ALL_TAC] THEN SUBGOAL_THEN q68 ASSUME_TAC THENL [EXPAND_TAC "B" THEN ASM_SIMP_TAC [RING_MUL, RING_POW], ALL_TAC] THEN SUBGOAL_THEN q67 ASSUME_TAC THENL [MATCH_MP_TAC FREE_BASIS_SPANNING_DEGREE THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC q66 THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o ((SPEC q65) o (CONJUNCT1 o (CONJUNCT2 o ((GEN_REWRITE_RULE id [free_basis]) o (checkM (fun th => (do let z64 ← (q r"free_basis (q,k) I (P * R) (\i. ring_pow k (z:A) i)"); let z63 ← (do let z62 ← (pure th); pure (concl z62)); pure (z63 == z64))))))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN q61 STRIP_ASSUME_TAC) THEN EXISTS_TAC q60 THEN ASM_SIMP_TAC [RING_SUM] THEN MP_TAC v59 THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, I_THM] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_SUM_EQ THEN ASM_REWRITE_TAC [IN_ELIM_THM], ALL_TAC] THEN MP_TAC v50 THEN ANTS_TAC THENL [ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, MULT_EQ_0], ALL_TAC] THEN REWRITE_TAC [v46, v43, v41] THEN STRIP_TAC THEN ONCE_REWRITE_TAC [v39] THEN SIMP_TAC [FREE_BASIS_INTEGER_RING_SUBRING_GENERATED, SUBRING_SUBRING_GENERATED] THEN FIRST_ASSUM ((fun th => REWRITE_TAC [th]) o (checkM (fun th => (do if ← (do let z33 ← (do let z34 ← (pure th); pure (concl z34)); pure (is_eq z33)) then (do let z38 ← (q r"ring_carrier(subring_generated k {z:A})"); let z37 ← (do let z35 ← (do let z36 ← (pure th); pure (concl z36)); liftExcept (lhs z35)); pure (z37 == z38)) else pure false)))) THEN REWRITE_TAC [FORALL_IN_GSPEC, IN_UNIV, IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL [X_GEN_TAC q32 THEN DISCH_TAC THEN SUBGOAL_THEN q31 SUBST1_TAC THENL [MAP_EVERY EXPAND_TAC ["B", "eta", "w"] THEN SIMP_TAC [RING_POW_ADD, RING_POW_MUL, v30], FIRST_ASSUM MATCH_ACCEPT_TAC], X_GEN_TAC q28 THEN EXISTS_TAC q27 THEN MP_TAC v26 THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, INTEGER_RING, IN_UNIV, RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_SUM_EQ THEN ASM_REWRITE_TAC [IN_ELIM_THM], X_GEN_TAC q17 THEN DISCH_TAC THEN MP_TAC v16 THEN ASM_SIMP_TAC [I_THM, RING_OF_INT_EQ_0_CHAR_0]])

  let CYCLOTOMIC_FIELD_DISCRIMINANT_COMPOSITUM ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"\i. ring_pow k (ring_pow k (z:A) d) i"
    let q2 ← q r"phi(n DIV d)"
    let q3 ← q r"subfield_generated k {ring_pow k (z:A) d}"
    let v4 ← ISPECL [q3, q2, q1] NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD
    let q5 ← q r"n DIV d"
    let q6 ← q r"ring_pow k (z:A) d"
    let q7 ← q r"subfield_generated k {ring_pow k (z:A) d}"
    let v8 ← ISPECL [q7, q6, q5] CYCLOTOMIC_FIELD_FREE_BASIS
    let q9 ← q r"n DIV d"
    let q10 ← q r"ring_pow k (z:A) d"
    let q11 ← q r"subfield_generated k {ring_pow k (z:A) d}"
    let v12 ← ISPECL [q11, q10, q9] CYCLOTOMIC_FIELD_INTEGRAL_BASIS
    let p13 ← prove r"!(k:A ring) z n d.
          number_field k /\ z IN ring_carrier k /\ ring_order k z = n /\
          ~(n = 0) /\ d divides n
          ==> free_basis (subfield_generated k {ring_0 k},
                          subfield_generated k {ring_pow k z d}) I
                         (phi(n DIV d)) (\i. ring_pow k (ring_pow k z d) i) /\
              ring_of_int k
                (number_field_discriminant
                   (subfield_generated k {ring_pow k z d})) =
              basis_discriminant
                (subfield_generated k {ring_0 k},
                 subfield_generated k {ring_pow k z d}) I
                (phi(n DIV d)) (\i. ring_pow k (ring_pow k z d) i)" (REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP CYCLOTOMIC_FIELD_SUBFIELD_POW)) THEN MP_TAC v12 THEN MP_TAC v8 THEN ASM_REWRITE_TAC [RING_POW_SUBFIELD_GENERATED] THEN DISCH_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC v4 THEN ASM_REWRITE_TAC [RING_OF_INT_SUBFIELD_GENERATED])
    let subfield_lemma := p13
    let v14 ← GSYM RING_OF_INT_EQ
    let q19 ← q r"!x y:int. (x == y) (mod &0) ==> x = y"
    let r20 ← INTEGER_RULE q19
    let q21 ← q r"ring_pow k (w:A) (u DIV P)"
    let q22 ← q r"ring_pow k (w:A) (t DIV P)"
    let q23 ← q r"L:A ring"
    let v24 ← ISPECL [q23, q22, q21] RING_MUL
    let q25 ← q r"ring_pow k (eta:A) (u MOD P)"
    let q26 ← q r"ring_pow k (eta:A) (t MOD P)"
    let q27 ← q r"K:A ring"
    let v28 ← ISPECL [q27, q26, q25] RING_MUL
    let q29 ← q r"ring_mul r (ring_mul r a b) (ring_mul r c d) =
        ring_mul r (ring_mul r a c) (ring_mul r b (d:A))"
    let r30 ← RING_RULE q29
    let q31 ← q r"ring_mul k (B t) (B u) =
      ring_mul k (ring_mul k (ring_pow k eta (t MOD P))
                             (ring_pow k eta (u MOD P)))
                 (ring_mul k (ring_pow k w (t DIV P))
                             (ring_pow k (w:A) (u DIV P)))"
    let q32 ← q r"u:num"
    let q33 ← q r"t:num"
    let q34 ← q r"\i j. algebra_trace (q,L) I
               (ring_mul L (ring_pow k (w:A) i) (ring_pow k w j))"
    let q35 ← q r"\i j. algebra_trace (q,K) I
               (ring_mul K (ring_pow k (eta:A) i) (ring_pow k eta j))"
    let q36 ← q r"R:num"
    let q37 ← q r"P:num"
    let q38 ← q r"q:A ring"
    let v39 ← ISPECL [q38, q37, q36, q35, q34] RING_DET_KRONECKER_MOD_DIV
    let q40 ← q r"basis_discriminant (q,k) I (P * R) (B:num->A) =
    ring_mul k
      (ring_pow k (basis_discriminant (q,K) I P (\i. ring_pow k eta i)) R)
      (ring_pow k (basis_discriminant (q,L) I R (\i. ring_pow k w i)) P)"
    let q41 ← q r"i:num"
    let q42 ← q r"w:A"
    let q43 ← q r"L:A ring"
    let v44 ← ISPECL [q43, q42, q41] RING_POW
    let q45 ← q r"i:num"
    let q46 ← q r"eta:A"
    let q47 ← q r"K:A ring"
    let v48 ← ISPECL [q47, q46, q45] RING_POW
    let q49 ← q r"(!i. ring_pow k eta i IN ring_carrier K) /\
    (!i. ring_pow k w i IN ring_carrier (L:A ring))"
    let v50 ← CONJUNCT2 SUBFIELD_GENERATED
    let q51 ← q r"subfield_generated k {w:A} = L"
    let q52 ← q r"subfield_generated k {eta:A} = K"
    let q53 ← q r"subfield_generated k {ring_0 k:A} = q"
    let q54 ← q r"ring_mul q = ring_mul (k:A ring) /\ ring_pow q = ring_pow k /\
    ring_mul K = ring_mul k /\ ring_pow K = ring_pow k /\
    ring_mul L = ring_mul k /\ ring_pow L = ring_pow k"
    let q55 ← q r"y:A"
    let q56 ← q r"x:A"
    let q57 ← q r"\i. ring_pow k (w:A) i"
    let q58 ← q r"\i. ring_pow k (eta:A) i"
    let q59 ← q r"R:num"
    let q60 ← q r"P:num"
    let q61 ← q r"{w:A}"
    let q62 ← q r"{eta:A}"
    let q63 ← q r"k:A ring"
    let v64 ← ISPECL [q63, q62, q61, q60, q59, q58, q57, q56, q55] ALGEBRA_TRACE_PRODUCT_BASIS
    let q65 ← q r"!x y. x IN ring_carrier K /\ y IN ring_carrier L
          ==> algebra_trace (q,k) I (ring_mul k x y) =
              ring_mul k (algebra_trace (q,K) I x)
                         (algebra_trace (q,L) I (y:A))"
    let q66 ← q r"(eta:A) IN ring_carrier k /\ (w:A) IN ring_carrier k"
    let q67 ← q r"B = \t. ring_mul k (ring_pow k (eta:A) (t MOD P))
                        (ring_pow k w (t DIV P))"
    let q68 ← q r"L = subfield_generated k {w:A}"
    let q69 ← q r"K = subfield_generated k {eta:A}"
    let q70 ← q r"q = subfield_generated k {ring_0 k:A}"
    let q71 ← q r"R = phi s"
    let q72 ← q r"P = phi r"
    let q73 ← q r"w = ring_pow k (z:A) r"
    let q74 ← q r"eta = ring_pow k (z:A) s"
    let q75 ← q r"(r * s) DIV s = r /\ (r * s) DIV r = s"
    let q76 ← q r"r:num"
    let q77 ← q r"r:num * s"
    let q78 ← q r"z:A"
    let q79 ← q r"k:A ring"
    let v80 ← ISPECL [q79, q78, q77, q76] CYCLOTOMIC_FIELD_SUBFIELD_POW
    let q81 ← q r"s:num"
    let q82 ← q r"r:num * s"
    let q83 ← q r"z:A"
    let q84 ← q r"k:A ring"
    let v85 ← ISPECL [q84, q83, q82, q81] CYCLOTOMIC_FIELD_SUBFIELD_POW
    let q86 ← q r"r:num"
    let q87 ← q r"r:num * s"
    let q88 ← q r"z:A"
    let q89 ← q r"k:A ring"
    let v90 ← ISPECL [q89, q88, q87, q86] subfield_lemma
    let q91 ← q r"s:num"
    let q92 ← q r"r:num * s"
    let q93 ← q r"z:A"
    let q94 ← q r"k:A ring"
    let v95 ← ISPECL [q94, q93, q92, q91] subfield_lemma
    let q96 ← q r"number_field (k:A ring)"
    let v97 ← ASSUME q96
    let q98 ← q r"number_field (k:A ring)"
    let v99 ← ASSUME q98
    let q100 ← q r"s:num"
    let q101 ← q r"r:num"
    let q102 ← q r"z:A"
    let q103 ← q r"k:A ring"
    let v104 ← ISPECL [q103, q102, q101, q100] CYCLOTOMIC_FIELD_PRODUCT_BASIS
    prove
      r"!(k:A ring) z r s.
          number_field k /\ z IN ring_carrier k /\
          ring_order k z = r * s /\ ~(r * s = 0) /\ coprime(r,s) /\
          subfield_generated k {z} = k
          ==> number_field_discriminant k =
              number_field_discriminant
                (subfield_generated k {ring_pow k z s}) pow phi s *
              number_field_discriminant
                (subfield_generated k {ring_pow k z r}) pow phi r"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN MP_TAC v104 THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o (CONJUNCT2 o ((MATCH_MP RING_OF_INTEGERS_FREE_BASIS_FIELD) o (CONJ v99)))) THEN FIRST_ASSUM (MP_TAC o ((MATCH_MP NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD) o (CONJ v97))) THEN MP_TAC v95 THEN MP_TAC v90 THEN MP_TAC v85 THEN MP_TAC v80 THEN ASM_SIMP_TAC [DIVIDES_LMUL, DIVIDES_RMUL, DIVIDES_REFL] THEN RULE_ASSUM_TAC (REWRITE_RULE [MULT_EQ_0, DE_MORGAN_THM]) THEN SUBGOAL_THEN q75 (fun th => REWRITE_TAC [th]) THENL [ONCE_REWRITE_TAC [MULT_SYM] THEN ASM_SIMP_TAC [DIV_MULT] THEN ONCE_REWRITE_TAC [MULT_SYM] THEN ASM_SIMP_TAC [DIV_MULT], ALL_TAC] THEN ABBREV_TAC q74 THEN ABBREV_TAC q73 THEN ABBREV_TAC q72 THEN ABBREV_TAC q71 THEN ABBREV_TAC q70 THEN ABBREV_TAC q69 THEN ABBREV_TAC q68 THEN ABBREV_TAC q67 THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN q66 STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["eta", "w"] THEN ASM_SIMP_TAC [RING_POW], ALL_TAC] THEN SUBGOAL_THEN q65 ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC v64 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN q54 STRIP_ASSUME_TAC THENL [MAP_EVERY (fun t => tactic_of do pure (SUBST1_TAC (← SYM (← ASSUME t)))) [q53, q52, q51] THEN REWRITE_TAC [v50, RING_POW_SUBFIELD_GENERATED], ALL_TAC] THEN SUBGOAL_THEN q49 STRIP_ASSUME_TAC THENL [CONJ_TAC THEN GEN_TAC THENL [MP_TAC v48, MP_TAC v44] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN q40 ASSUME_TAC THENL [MP_TAC v39 THEN REWRITE_TAC [ALGEBRA_TRACE_NORM_IN_CARRIER] THEN ASM_REWRITE_TAC [basis_discriminant] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [q33, q32] THEN STRIP_TAC THEN SUBGOAL_THEN q31 SUBST1_TAC THENL [EXPAND_TAC "B" THEN REWRITE_TAC [] THEN MATCH_MP_TAC r30 THEN ASM_SIMP_TAC [RING_POW], FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL [MP_TAC v28, MP_TAC v24] THEN ASM_REWRITE_TAC []], ALL_TAC] THEN MATCH_MP_TAC r20 THEN FIRST_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z18 ← (q r"ring_char (k:A ring)"); let z17 ← (do let z15 ← (do let z16 ← (pure th); pure (concl z16)); liftExcept (lhs z15)); pure (z17 == z18)))))) THEN REWRITE_TAC [v14, RING_OF_INT_MUL, RING_OF_INT_POW] THEN ASM_REWRITE_TAC [])

  -- @@RETURN BEGIN
  return { CYCLOTOMIC_FIELD_DISCRIMINANT_PRIME_POWER, CYCLOTOMIC_FIELD_PRODUCT_BASIS,
           CYCLOTOMIC_FIELD_DISCRIMINANT_COMPOSITUM }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- cyclotomic_integers.ml phrases from line 1887 to 1887                  -/
/- ---------------------------------------------------------------------- -/

structure CyclotomicIntegers04 where
  -- @@FIELDS
  CYCLOTOMIC_FIELD_DISCRIMINANT : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupCyclotomicIntegers04 [HolBase] (D : CyclotomicIntegersDeps) (BCyclotomicIntegers02 : CyclotomicIntegers02) (BCyclotomicIntegers03 : CyclotomicIntegers03) :
    ExceptT String IO CyclotomicIntegers04 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INT_RING, MESON,
        MESON_TAC, NUM_REDUCE_CONV, .. } := D
  let { ADD_CLAUSES, ADD_EQ_0, ADD_SUB, ARITH, ARITH_EQ, COPRIME_1, COPRIME_LEXP,
        DISJOINT, DIVIDES_LMUL, DIVIDES_ONE, DIVIDES_PRIME_PRIME, DIVIDES_REFL,
        DIVIDES_RMUL, DIV_MULT, EVEN_ADD, EVEN_EXISTS, EVEN_MULT, EXP, EXP_1, EXP_ADD,
        EXP_EQ_0, EXP_MULT, EXP_ONE, EXTENSION, FINITE_INDUCT_STRONG,
        FINITE_SPECIAL_DIVISORS, INDEX_DECOMPOSITION_PRIME, INT_MUL_ASSOC,
        INT_OF_NUM_MUL, INT_OF_NUM_POW, INT_POW_1, INT_POW_ADD, INT_POW_MUL,
        INT_POW_NEG, INT_POW_ONE, INT_POW_POW, IN_ELIM_THM, IN_INTER, .. } := D.core1
  let { IN_SING, IN_UNION, LEFT_ADD_DISTRIB, LE_EXP, LE_TRANS, LT_MULT_LCANCEL,
        LT_MULT_RCANCEL, MULT_AC, MULT_ASSOC, MULT_CLAUSES, MULT_EXP, MULT_SYM,
        NOT_IN_EMPTY, NOT_ODD, NPRODUCT_CLAUSES, NPRODUCT_DELETE, NPRODUCT_EQ,
        NPRODUCT_SING, NPRODUCT_UNION, NUMBER_FIELD_DISCRIMINANT_NONZERO, ODD_PHI_EQ,
        PHI_1, PHI_2, PHI_EXPAND, PHI_MULTIPLICATIVE, PHI_PRIMEPOW_ALT, PRIME_1,
        PRIME_COPRIME_EQ, PRIME_DIVEXP, PRIME_DIVPROD_EQ, PRIME_FACTOR, PRIME_GE_2,
        PRIME_IMP_NZ, RIGHT_ADD_DISTRIB, .. } := D.core2
  let { RING_POW_1, divides, num_WF, .. } := D.core3
  let { CYCLOTOMIC_FIELD_SUBFIELD_POW, .. } := BCyclotomicIntegers02
  let { CYCLOTOMIC_FIELD_DISCRIMINANT_COMPOSITUM,
        CYCLOTOMIC_FIELD_DISCRIMINANT_PRIME_POWER, .. } := BCyclotomicIntegers03
  -- @@SCOPE END

  let CYCLOTOMIC_FIELD_DISCRIMINANT ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"q:num"
    let q2 ← q r"{p | prime p /\ p divides m}"
    let q3 ← q r"\p. p EXP (index p m - 1) * (p - 1)"
    let v4 ← ISPECL [q3, q2, q1] NPRODUCT_DELETE
    let p5 ← prove r"!q m. prime q /\ q divides m /\ ~(m = 0) ==> (q - 1) divides phi m" (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [PHI_EXPAND] THEN MP_TAC v4 THEN ASM_SIMP_TAC [FINITE_SPECIAL_DIVISORS, IN_ELIM_THM] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC DIVIDES_RMUL THEN MATCH_MP_TAC DIVIDES_LMUL THEN REWRITE_TAC [DIVIDES_REFL])
    let phi_lemma := p5
    let p6 ← prove r"!(g:num->num) e s. FINITE s
                          ==> nproduct s (\x. g x EXP e) = nproduct s g EXP e" (GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN SIMP_TAC [NPRODUCT_CLAUSES, EXP_ONE, MULT_EXP])
    let pow_lemma := p6
    let q7 ← q r"!u v w x s1 a1 s2 m1:int.
        u * v = s1 * a1 ==> w * x = s2 * m1
        ==> (u * w) * v * x = (s1 * s2) * a1 * m1"
    let r8 ← INT_RING q7
    let v9 ← GSYM INT_OF_NUM_POW
    let v10 ← GSYM INT_OF_NUM_MUL
    let q14 ← q r"\x:int. x pow R"
    let q18 ← q r"\x:int. x pow P"
    let q19 ← q r"(2 * c) * (2 * d) = 2 * (c * 2 * d)"
    let r20 ← ARITH_RULE q19
    let q21 ← q r"c:num"
    let q22 ← q r"d:num"
    let v23 ← GSYM NOT_ODD
    let q24 ← q r"(P = 1 \/ EVEN P) /\ (R = 1 \/ EVEN R)"
    let q25 ← q r"(a <=> b) ==> ((if a then x else y):int) = (if b then x else y)"
    let r26 ← MESON [] q25
    let v27 ← GSYM INT_POW_ADD
    let q28 ← q r"(-- &1:int) pow ((P * R) DIV 2) =
      ((-- &1) pow (P DIV 2)) pow R * ((-- &1) pow (R DIV 2)) pow P"
    let v29 ← GSYM EXP_MULT
    let q30 ← q r"q:num"
    let v31 ← GSYM MULT_ASSOC
    let q32 ← q r"!d x y. ~(d = 0) /\ d divides x ==> (x * y) DIV d = x DIV d * y"
    let v33 ← GSYM pow_lemma
    let q34 ← q r"nproduct {q | prime q /\ q divides p EXP a}
        (\q. q EXP ((P * R) DIV (q - 1))) =
      nproduct {q | prime q /\ q divides p EXP a}
        (\q. q EXP (P DIV (q - 1))) EXP R /\
      nproduct {q | prime q /\ q divides m}
        (\q. q EXP ((P * R) DIV (q - 1))) =
      nproduct {q | prime q /\ q divides m}
        (\q. q EXP (R DIV (q - 1))) EXP P"
    let q35 ← q r"q:num = p"
    let q36 ← q r"q:num"
    let q37 ← q r"{q | prime q /\ q divides p EXP a * m} =
      {q | prime q /\ q divides p EXP a} UNION {q | prime q /\ q divides m}"
    let q38 ← q r"R = phi m"
    let q39 ← q r"P = phi(p EXP a)"
    let q40 ← q r"coprime(p EXP a,m) /\ ~(p EXP a = 0)"
    let p41 ← prove r"!p a m (dK:int) (dL:int).
          prime p /\ ~(a = 0) /\ coprime(p,m) /\ ~(m = 0) /\
          dK * &(nproduct {q | prime q /\ q divides p EXP a}
                           (\q. q EXP (phi(p EXP a) DIV (q - 1)))) =
          (-- &1) pow (phi(p EXP a) DIV 2) * &((p EXP a) EXP phi(p EXP a)) /\
          dL * &(nproduct {q | prime q /\ q divides m}
                           (\q. q EXP (phi m DIV (q - 1)))) =
          (-- &1) pow (phi m DIV 2) * &(m EXP phi m)
          ==> (dK pow phi m * dL pow phi(p EXP a)) *
              &(nproduct {q | prime q /\ q divides p EXP a * m}
                         (\q. q EXP (phi(p EXP a * m) DIV (q - 1)))) =
              (-- &1) pow (phi(p EXP a * m) DIV 2) *
              &((p EXP a * m) EXP phi(p EXP a * m))" (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN q40 STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [COPRIME_LEXP, EXP_EQ_0, PRIME_IMP_NZ], ALL_TAC] THEN ASM_SIMP_TAC [PHI_MULTIPLICATIVE] THEN ABBREV_TAC q39 THEN ABBREV_TAC q38 THEN SUBGOAL_THEN q37 SUBST1_TAC THENL [REWRITE_TAC [EXTENSION, IN_UNION, IN_ELIM_THM] THEN MESON_TAC [PRIME_DIVPROD_EQ], ALL_TAC] THEN wPart (rand o rand o lhand) (lhand o rand) NPRODUCT_UNION THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_SPECIAL_DIVISORS] THEN REWRITE_TAC [DISJOINT, EXTENSION, IN_INTER, IN_ELIM_THM, NOT_IN_EMPTY] THEN X_GEN_TAC q36 THEN STRIP_TAC THEN SUBGOAL_THEN q35 SUBST_ALL_TAC THENL [ASM_MESON_TAC [PRIME_DIVEXP, DIVIDES_PRIME_PRIME], ALL_TAC] THEN ASM_MESON_TAC [PRIME_COPRIME_EQ], DISCH_THEN SUBST1_TAC] THEN SUBGOAL_THEN q34 (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_SIMP_TAC [v33, FINITE_SPECIAL_DIVISORS] THEN SUBGOAL_THEN q32 ASSUME_TAC THENL [REWRITE_TAC [divides] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [v31, DIV_MULT], ALL_TAC] THEN CONJ_TAC THEN MATCH_MP_TAC NPRODUCT_EQ THEN X_GEN_TAC q30 THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN REWRITE_TAC [v29] THEN AP_TERM_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_GE_2)) THENL [ALL_TAC, GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [MULT_SYM]] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN (CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC]) THEN MAP_EVERY EXPAND_TAC ["P", "R"] THEN MATCH_MP_TAC phi_lemma THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN q28 SUBST1_TAC THENL [REWRITE_TAC [INT_POW_POW, v27] THEN REWRITE_TAC [INT_POW_NEG, INT_POW_ONE] THEN MATCH_MP_TAC r26 THEN SUBGOAL_THEN q24 MP_TAC THENL [MAP_EVERY EXPAND_TAC ["P", "R"] THEN REWRITE_TAC [v23, ODD_PHI_EQ] THEN MESON_TAC [PHI_1, PHI_2], ALL_TAC] THEN STRIP_TAC THEN ASM_REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES] THEN FIRST_X_ASSUM ((X_CHOOSE_THEN q22 SUBST1_TAC) o (GEN_REWRITE_RULE id [EVEN_EXISTS])) THEN FIRST_X_ASSUM ((X_CHOOSE_THEN q21 SUBST1_TAC) o (GEN_REWRITE_RULE id [EVEN_EXISTS])) THEN REWRITE_TAC [r20] THEN SIMP_TAC [DIV_MULT, ARITH_EQ] THEN REWRITE_TAC [EVEN_ADD, EVEN_MULT, ARITH], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o ((AP_TERM q18) o (checkM (fun th => (do let z16 ← (do let z17 ← (pure th); pure (concl z17)); let z15 ← (q r"dL:int"); pure (free_in z15 z16)))))) THEN FIRST_X_ASSUM (MP_TAC o ((AP_TERM q14) o (checkM (fun th => (do let z12 ← (do let z13 ← (pure th); pure (concl z13)); let z11 ← (q r"dK:int"); pure (free_in z11 z12)))))) THEN REWRITE_TAC [v10, v9, INT_POW_MUL, INT_POW_POW] THEN REWRITE_TAC [MULT_AC] THEN MATCH_ACCEPT_TAC r8)
    let int_lemma := p41
    let q42 ← q r"p EXP a"
    let q43 ← q r"p EXP a * m"
    let q44 ← q r"z:A"
    let q45 ← q r"k:A ring"
    let v46 ← ISPECL [q45, q44, q43, q42] CYCLOTOMIC_FIELD_SUBFIELD_POW
    let q47 ← q r"ring_pow k (z:A) (p EXP a)"
    let q48 ← q r"m:num"
    let q49 ← q r"p EXP a * m"
    let q50 ← q r"z:A"
    let q51 ← q r"k:A ring"
    let v52 ← ISPECL [q51, q50, q49, q48] CYCLOTOMIC_FIELD_SUBFIELD_POW
    let q53 ← q r"ring_pow k (z:A) m"
    let q54 ← q r"~(p EXP a = 0)"
    let q55 ← q r"m:num"
    let q56 ← q r"p EXP a"
    let q57 ← q r"z:A"
    let q58 ← q r"k:A ring"
    let v59 ← ISPECL [q58, q57, q56, q55] CYCLOTOMIC_FIELD_DISCRIMINANT_COMPOSITUM
    let q60 ← q r"m = 1 * m"
    let r61 ← ARITH_RULE q60
    let q62 ← q r"x = x * 1"
    let r63 ← ARITH_RULE q62
    let q64 ← q r"x:num"
    let q65 ← q r"p EXP a"
    let q66 ← q r"~(m = 1)"
    let q67 ← q r"~(m = 0)"
    let q68 ← q r"p EXP 1"
    let q69 ← q r"2 <= p EXP a"
    let q70 ← q r"coprime(p EXP a,m) /\ p EXP a < p EXP a * m /\ m < p EXP a * m"
    let v71 ← GSYM INT_OF_NUM_POW
    let q72 ← q r"(q + 2) * (v + 1) - v - 2 = q * v + q + v"
    let r73 ← ARITH_RULE q72
    let q74 ← q r"(q + 2) - 1 = q + 1"
    let r75 ← ARITH_RULE q74
    let q76 ← q r"p - 2"
    let q77 ← q r"?q. p = q + 2"
    let v78 ← GSYM EXP_MULT
    let q79 ← q r"(p EXP (v + 1)) EXP (p EXP v * (p - 1)) =
      p EXP (p EXP v * (p * (v + 1) - v - 2) + p EXP v)"
    let q80 ← q r"(p EXP v * (p - 1)) DIV (p - 1) = p EXP v"
    let q81 ← q r"q:num"
    let q82 ← q r"{q | prime q /\ q divides p EXP (v + 1)} = {p}"
    let q83 ← q r"v:num"
    let q84 ← q r"p:num"
    let q85 ← q r"z:A"
    let q86 ← q r"k:A ring"
    let v87 ← ISPECL [q86, q85, q84, q83] CYCLOTOMIC_FIELD_DISCRIMINANT_PRIME_POWER
    let q88 ← q r"a - 1"
    let q89 ← q r"v:num"
    let q90 ← q r"?v. a = v + 1"
    let q91 ← q r"m = 1"
    let q92 ← q r"~(a = 0) /\ ~(m = 0)"
    let q93 ← q r"m:num"
    let q94 ← q r"a = index p n"
    let q95 ← q r"p:num"
    let q96 ← q r"n:num"
    let v97 ← SPECL [q96, q95] INDEX_DECOMPOSITION_PRIME
    let q98 ← q r"p:num"
    let q99 ← q r"{p | prime p /\ p divides 1} = {}"
    let q100 ← q r"k:A ring"
    let v101 ← ISPEC q100 NUMBER_FIELD_DISCRIMINANT_NONZERO
    let q102 ← q r"1"
    let q103 ← q r"1"
    let q104 ← q r"z:A"
    let q105 ← q r"k:A ring"
    let v106 ← ISPECL [q105, q104, q103, q102] CYCLOTOMIC_FIELD_DISCRIMINANT_COMPOSITUM
    let q107 ← q r"n = 1"
    let q108 ← q r"z:A"
    let q109 ← q r"k:A ring"
    let q110 ← q r"n:num"
    let q111 ← q r"!n. ~(n = 0)
        ==> !(k:A ring) z.
              number_field k /\ z IN ring_carrier k /\ ring_order k z = n /\
              subfield_generated k {z} = k
              ==> number_field_discriminant k *
                  &(nproduct {p | prime p /\ p divides n}
                             (\p. p EXP (phi n DIV (p - 1)))) =
                  (-- &1) pow (phi n DIV 2) * &(n EXP phi n)"
    prove
      r"!(k:A ring) z n.
          number_field k /\ z IN ring_carrier k /\
          ring_order k z = n /\ ~(n = 0) /\ subfield_generated k {z} = k
          ==> number_field_discriminant k *
              &(nproduct {p | prime p /\ p divides n}
                         (\p. p EXP (phi n DIV (p - 1)))) =
              (-- &1) pow (phi n DIV 2) * &(n EXP phi n)"
      (SUBGOAL_THEN q111 (fun th => MESON_TAC [th]) THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC q110 THEN DISCH_THEN (LABEL_TAC "ih") THEN DISCH_TAC THEN MAP_EVERY X_GEN_TAC [q109, q108] THEN STRIP_TAC THEN ASM_CASES_TAC q107 THENL [FIRST_X_ASSUM SUBST_ALL_TAC THEN MP_TAC v106 THEN ASM_SIMP_TAC [MULT_CLAUSES, ARITH_EQ, COPRIME_1, RING_POW_1, PHI_1, INT_POW_1] THEN MP_TAC v101 THEN SUBGOAL_THEN q99 SUBST1_TAC THENL [REWRITE_TAC [EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY, DIVIDES_ONE] THEN MESON_TAC [PRIME_1], ASM_REWRITE_TAC [NPRODUCT_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV] THEN CONV_TAC INT_RING, ALL_TAC] THEN FIRST_X_ASSUM ((X_CHOOSE_THEN q98 STRIP_ASSUME_TAC) o (MATCH_MP PRIME_FACTOR)) THEN MP_TAC v97 THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC q94 THEN DISCH_THEN (X_CHOOSE_THEN q93 (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN SUBGOAL_THEN q92 STRIP_ASSUME_TAC THENL [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL [RULE_ASSUM_TAC (REWRITE_RULE [EXP, MULT_CLAUSES]) THEN ASM_MESON_TAC [PRIME_COPRIME_EQ], ASM_MESON_TAC [MULT_CLAUSES]], ALL_TAC] THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_CASES_TAC q91 THENL [FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE [MULT_CLAUSES]) THEN REWRITE_TAC [MULT_CLAUSES] THEN SUBGOAL_THEN q90 (X_CHOOSE_THEN q89 SUBST_ALL_TAC) THENL [EXISTS_TAC q88 THEN ASM_ARITH_TAC, ALL_TAC] THEN MP_TAC v87 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN SUBGOAL_THEN q82 SUBST1_TAC THENL [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_SING] THEN X_GEN_TAC q81 THEN EQ_TAC THENL [ASM_MESON_TAC [PRIME_DIVEXP, DIVIDES_PRIME_PRIME], DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [EXP_ADD, EXP_1] THEN MESON_TAC [DIVIDES_LMUL, DIVIDES_REFL]], ALL_TAC] THEN REWRITE_TAC [NPRODUCT_SING] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_GE_2)) THEN ASM_SIMP_TAC [PHI_PRIMEPOW_ALT, ADD_EQ_0, ARITH_EQ, ADD_SUB] THEN SUBGOAL_THEN q80 SUBST1_TAC THENL [ONCE_REWRITE_TAC [MULT_SYM] THEN MATCH_MP_TAC DIV_MULT THEN ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN q79 SUBST1_TAC THENL [REWRITE_TAC [v78] THEN AP_TERM_TAC THEN SUBGOAL_THEN q77 (CHOOSE_THEN SUBST1_TAC) THENL [EXISTS_TAC q76 THEN ASM_ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [r75, r73] THEN REWRITE_TAC [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_CLAUSES] THEN ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [v71, INT_POW_ADD, INT_MUL_ASSOC], ALL_TAC] THEN SUBGOAL_THEN q70 STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC [COPRIME_LEXP] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_GE_2)) THEN SUBGOAL_THEN q69 MP_TAC THENL [TRANS_TAC LE_TRANS q68 THEN ASM_REWRITE_TAC [EXP_1, LE_EXP] THEN ASM_ARITH_TAC, ALL_TAC] THEN MAP_EVERY UNDISCH_TAC [q67, q66] THEN SPEC_TAC (q65, q64) THEN REPEAT STRIP_TAC THENL [GEN_REWRITE_TAC LAND_CONV [r63] THEN REWRITE_TAC [LT_MULT_LCANCEL], GEN_REWRITE_TAC LAND_CONV [r61] THEN REWRITE_TAC [LT_MULT_RCANCEL]] THEN ASM_ARITH_TAC, ALL_TAC] THEN MP_TAC v59 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC int_lemma THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN q54 ASSUME_TAC THENL [ASM_SIMP_TAC [EXP_EQ_0, PRIME_IMP_NZ], ALL_TAC] THEN CONJ_TAC THENL [USE_THEN "ih" (fun th => tactic_of do pure (MP_TAC (← MP (← MP (← SPEC (← q r"p EXP a") th) (← ASSUME (← q r"p EXP a < p EXP a * m"))) (← ASSUME (← q r"~(p EXP a = 0)"))))), USE_THEN "ih" (fun th => tactic_of do pure (MP_TAC (← MP (← MP (← SPEC (← q r"m:num") th) (← ASSUME (← q r"m < p EXP a * m"))) (← ASSUME (← q r"~(m = 0)")))))] THEN DISCH_THEN MATCH_MP_TAC THENL [EXISTS_TAC q53 THEN MP_TAC v52, EXISTS_TAC q47 THEN MP_TAC v46] THEN ASM_SIMP_TAC [DIVIDES_LMUL, DIVIDES_RMUL, DIVIDES_REFL, DIV_MULT] THEN ONCE_REWRITE_TAC [MULT_SYM] THEN ASM_SIMP_TAC [DIV_MULT])

  -- @@RETURN BEGIN
  return { CYCLOTOMIC_FIELD_DISCRIMINANT }
  -- @@RETURN END

end HolANT.CyclotomicIntegers
