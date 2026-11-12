/- ========================================================================= -/
/- ANT: Quadratic fields, abstractly (no complex numbers)                  -/
/- ========================================================================= -/
/- File: HolANT/Quadratic.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/quadratic.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antquadraticdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/products.ml, ANT/algmisc.ml, ANT/integral.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/discriminant.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.Quadratic fills them).

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
import HolLibrary.Isum
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

namespace HolANT.Quadratic

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ALGEBRAIC_OVER_IMAGE ALGEBRAIC_OVER_POW_EQ ALGEBRA_TRACE_ADD
   ALGEBRA_TRACE_FREE_BASIS ALGEBRA_TRACE_NORM_BASE_FREE_BASIS
   ALGEBRA_TRACE_NORM_IN_CARRIER ALGEBRA_TRACE_SCALAR ARITH ARITH_EQ
   BASIS_COORDINATES_BASIS BASIS_COORDINATES_LMUL
   BASIS_DISCRIMINANT_CHANGE_OF_BASIS COEFF_POLY_CONST COEFF_POLY_SUB
   COEFF_POLY_VARPOW DIVIDES_ZERO EQ_SYM_EQ EXISTS_OR_THM EXISTS_UNIQUE_THM
   EXTENSION EXTENSION_DEGREE_EQ_TOWER FIELD_EXTENSION_IMP_HOMOMORPHISM
   FIELD_EXTENSION_SUBFIELD_GENERATED FIELD_IMP_INTEGRAL_DOMAIN
   FIELD_IMP_NONTRIVIAL_RING FIELD_MUL_LINV FIELD_MUL_RINV FIELD_NONTRIVIAL
   FIELD_REAL_RING FIELD_RING_HOMOMORPHISM_MONOMORPHISM FIELD_SUBFIELD_GENERATED
   FINITE_EMPTY FINITE_IMP_FIELD_EXTENSION FINITE_INSERT FINITE_NUMSEG_LT
   FORALL_IN_INSERT FORALL_LT_2 FREE_BASIS_FIELD
   FREE_BASIS_INTEGER_RING_SUBRING_GENERATED FUN_IN_IMAGE IMAGE_EQ IMAGE_I
   IMP_CONJ INTEGER_RING INTEGRAL_DOMAIN_MUL_EQ_0 INTEGRAL_DOMAIN_MUL_LCANCEL
   INTEGRAL_DOMAIN_POW_EQ_0 INTEGRAL_DOMAIN_SQUARE_EQ
   INTEGRAL_ELEMENT_FROM_RELATION INTEGRAL_ELEMENT_PRIME_SUBFIELD INT_ABS_NUM
   INT_ABS_POS INT_ABS_POW INT_DIVIDES_NUM_OF_INT_ABS INT_DIVISION INT_ENTIRE
   INT_EQ_MUL_LCANCEL INT_LE_POW_2 INT_LE_RMUL INT_MUL_LID INT_NOT_LT
   INT_OF_NUM_EQ INT_OF_NUM_OF_INT INT_POW2_ABS INT_POW_LE2 INT_POW_ONE
   INT_REM_EQ INT_REM_EQ_0 INT_SQUAREFREE_DECOMPOSITION INT_SQUAREFREE_DIVPOW
   INT_SQUAREFREE_MUL_SQUARE INT_SUB_0 IN_ELIM_THM IN_IMAGE IN_INSERT IN_INTER
   IN_SING IN_SUBRING_MUL IN_SUBRING_POW IN_SUBRING_SUB IN_UNION IN_UNIV
   IRREDUCIBLE_IMP_POLY_DEG_NZ I_O_ID I_THM KRONECKER_SIMPLE_FIELD_EXTENSION
   LEFT_IMP_EXISTS_THM MINIMAL_POLYNOMIAL_DEG_EQ_1
   MINIMAL_POLYNOMIAL_DEG_LE_EXTENSION_DEGREE MINIMAL_POLYNOMIAL_IRREDUCIBLE
   MINIMAL_POLYNOMIAL_UNIQUE MONO_EXISTS NOT_EXISTS_THM NOT_IN_EMPTY
   NUMBER_FIELD_ALGEBRAIC NUMBER_FIELD_ALT NUMBER_FIELD_DEGREE_EQ_1
   NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD NUMBER_FIELD_FREE_BASIS_DEGREE
   NUMBER_FIELD_IMP_FIELD NUMBER_FIELD_TRACE_INTEGRAL_Q NUM_OF_INT_ABS_POW
   NUM_OF_INT_OF_NUM POLY_DEG_2_IRREDUCIBLE POLY_EVAL_VAR_POW_SUB_CONST
   POLY_EXTEND_CONST POLY_EXTEND_EVALUATE POLY_EXTEND_SUB POLY_EXTEND_VARPOW
   POLY_RING_CLAUSES POLY_VAR_POW_SUB_CONST PRIME_SUBFIELD_COMMON_DENOMINATOR : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (PRIME_SUBFIELD_HOMOMORPHISM_EXISTS PRIME_SUBFIELD_MONOMORPHIC_IMAGE
   PRIME_SUBFIELD_SUBFIELD_GENERATED REAL_RING_CHAR RIGHT_FORALL_IMP_THM
   RIGHT_OR_DISTRIB RING_0 RING_0_IN_SUBFIELD_GENERATED RING_1
   RING_1_IN_SUBFIELD_GENERATED RING_ADD RING_ADD_EQ_0
   RING_ADD_IN_SUBFIELD_GENERATED RING_ADD_IN_SUBRING_GENERATED
   RING_ADD_LDISTRIB RING_ADD_LZERO RING_ADD_RNEG RING_ADD_RZERO RING_ADD_SYM
   RING_CARRIER_SUBFIELD_GENERATED_SUBSET RING_CHAR_MONOMORPHIC_IMAGE
   RING_CHAR_SUBFIELD_GENERATED RING_DET_DIAGONAL RING_DET_LOWERTRIANGULAR
   RING_DIV RING_HOMOMORPHISM_ADD RING_HOMOMORPHISM_I
   RING_HOMOMORPHISM_INTEGER_RING_OF_INT RING_HOMOMORPHISM_IN_CARRIER
   RING_HOMOMORPHISM_MUL RING_HOMOMORPHISM_RING_OF_INT
   RING_HOMOMORPHISM_SUBFIELD_INCLUSION RING_INV RING_INV_IN_SUBFIELD_GENERATED
   RING_ISOMORPHISM_MONOMORPHISM_ALT RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_MUL
   RING_MUL_ASSOC RING_MUL_IN_SUBFIELD_GENERATED RING_MUL_IN_SUBRING_GENERATED
   RING_MUL_LID RING_MUL_LZERO RING_MUL_RID RING_MUL_RZERO RING_NEG
   RING_NEG_IN_SUBFIELD_GENERATED RING_OF_INT RING_OF_INTEGERS
   RING_OF_INTEGERS_CARRIER RING_OF_INTEGERS_PRIME_SUBFIELD
   RING_OF_INTEGERS_SUBRING RING_OF_INTEGERS_SUBSET RING_OF_INT_0 RING_OF_INT_1
   RING_OF_INT_ADD RING_OF_INT_EQ_0_CHAR_0 RING_OF_INT_EQ_CHAR_0
   RING_OF_INT_IN_RING_OF_INTEGERS RING_OF_INT_IN_SUBFIELD_GENERATED
   RING_OF_INT_MUL RING_OF_INT_NEG RING_OF_INT_OF_NUM RING_OF_INT_POW
   RING_OF_INT_SUB RING_OF_INT_SUBFIELD_GENERATED RING_OF_NUM RING_OF_NUM_EQ_0
   RING_OF_NUM_SUBFIELD_GENERATED RING_POLYNOMIAL_CONST RING_POLYNOMIAL_POW
   RING_POLYNOMIAL_VAR RING_POW RING_POW_0 RING_POW_1 RING_POW_2
   RING_POW_IN_SUBFIELD_GENERATED RING_POW_SUBFIELD_GENERATED RING_PRODUCT_LT_2
   RING_SIMPLE_ALGEBRAIC_EXTENSION_BASIS RING_SIMPLE_ALGEBRAIC_EXTENSION_SPAN
   RING_SPAN_SING RING_SPAN_UNION RING_SUB RING_SUB_EQ_0 RING_SUB_REFL
   RING_SUB_RZERO RING_SUM_LT_2 SIMPLE_ALGEBRAIC_EXTEND_HOMOMORPHISM_ROOT
   SIMPLE_IMAGE_GEN SQUAREFREE_0 SQUAREFREE_EXP SUBFIELD_GENERATED
   SUBFIELD_GENERATED_EQ SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC
   SUBRING_GENERATED_INC_GEN SUBRING_GENERATED_SUPERSET SUBSET UNWIND_THM2
   basis_discriminant field_extension free_basis int_congruent int_divides
   isomorphic_ring monic mul_matrix number_field poly_eval ring_div
   ring_monomorphism ring_sub squarefree : thm)
  deriving Inhabited

/-- What quadratic.ml uses from Session besides theorems. -/
structure QuadraticDeps where
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
/- quadratic.ml phrases from line 50 to 686                               -/
/- ---------------------------------------------------------------------- -/

structure Quadratic01 where
  -- @@FIELDS
  INT_SQUARE_SUB_MUL_SQUARE_MOD_4 : thm
  INT_NORM_FORM_4_IMAGINARY : thm
  IN_SUBFIELD_GENERATED_MUL_CANCEL : thm
  SUBFIELD_GENERATED_ADD_MUL_EQ_0 : thm
  SUBFIELD_GENERATED_HALF_SUCC : thm
  FREE_BASIS_SUBFIELD_GENERATED_2 : thm
  INTEGRAL_ELEMENT_QUADRATIC : thm
  PRIME_SUBFIELD_SQRT_INTEGER : thm
  PRIME_SUBFIELD_SQUAREFREE_MUL_SQUARE : thm
  SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD : thm
  QUADRATIC_FIELD_FREE_BASIS : thm
  QUADRATIC_FIELD_COORDINATES : thm
  QUADRATIC_FIELD_INT_COORDINATES_EQ : thm
  QUADRATIC_FIELD_INTEGER_SQUARE : thm
  QUADRATIC_FIELD_SQRT_EXISTS : thm
  QUADRATIC_FIELD_SQRT_UNIQUE : thm
  QUADRATIC_FIELD_SQRT : thm
  FIELD_EXTENSION_SQRT : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupQuadratic01 [HolBase] (D : QuadraticDeps) :
    ExceptT String IO Quadratic01 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_INT_ARITH_TAC, ASM_MESON_TAC, INTEGER_RULE,
        INTEGRAL_DOMAIN_RULE, INT_ARITH, INT_ARITH_TAC, INT_REDUCE_CONV, MESON_TAC,
        RING_RULE, RING_TAC, SET_TAC, TAUT, .. } := D
  let { ARITH_EQ, DIVIDES_ZERO, EXISTS_OR_THM, EXISTS_UNIQUE_THM, EXTENSION,
        EXTENSION_DEGREE_EQ_TOWER, FIELD_EXTENSION_IMP_HOMOMORPHISM,
        FIELD_EXTENSION_SUBFIELD_GENERATED, FIELD_IMP_INTEGRAL_DOMAIN, FIELD_MUL_LINV,
        FIELD_MUL_RINV, FIELD_NONTRIVIAL, FIELD_SUBFIELD_GENERATED, FINITE_EMPTY,
        FINITE_IMP_FIELD_EXTENSION, FINITE_INSERT, FORALL_IN_INSERT, FORALL_LT_2,
        FREE_BASIS_FIELD, IMAGE_EQ, IMAGE_I, IMP_CONJ, INTEGER_RING,
        INTEGRAL_DOMAIN_MUL_EQ_0, INTEGRAL_DOMAIN_MUL_LCANCEL,
        INTEGRAL_DOMAIN_POW_EQ_0, INTEGRAL_ELEMENT_FROM_RELATION,
        INTEGRAL_ELEMENT_PRIME_SUBFIELD, INT_ABS_NUM, INT_ABS_POS, INT_ABS_POW,
        INT_DIVISION, INT_ENTIRE, INT_EQ_MUL_LCANCEL, INT_LE_POW_2, INT_LE_RMUL,
        INT_MUL_LID, INT_NOT_LT, INT_OF_NUM_EQ, INT_OF_NUM_OF_INT, INT_POW2_ABS,
        INT_POW_LE2, INT_POW_ONE, INT_REM_EQ, INT_REM_EQ_0,
        INT_SQUAREFREE_DECOMPOSITION, INT_SQUAREFREE_DIVPOW, INT_SQUAREFREE_MUL_SQUARE,
        INT_SUB_0, IN_ELIM_THM, IN_SING, IN_UNION, IN_UNIV,
        IRREDUCIBLE_IMP_POLY_DEG_NZ, I_O_ID, I_THM, KRONECKER_SIMPLE_FIELD_EXTENSION,
        LEFT_IMP_EXISTS_THM, MINIMAL_POLYNOMIAL_DEG_EQ_1,
        MINIMAL_POLYNOMIAL_DEG_LE_EXTENSION_DEGREE, MINIMAL_POLYNOMIAL_IRREDUCIBLE,
        MONO_EXISTS, NOT_EXISTS_THM, NOT_IN_EMPTY, NUMBER_FIELD_ALGEBRAIC,
        NUMBER_FIELD_DEGREE_EQ_1, NUMBER_FIELD_IMP_FIELD, NUM_OF_INT_ABS_POW,
        NUM_OF_INT_OF_NUM, POLY_EVAL_VAR_POW_SUB_CONST, POLY_EXTEND_EVALUATE,
        POLY_RING_CLAUSES, POLY_VAR_POW_SUB_CONST, PRIME_SUBFIELD_COMMON_DENOMINATOR, .. } := D.core1
  let { RIGHT_FORALL_IMP_THM, RIGHT_OR_DISTRIB, RING_0, RING_0_IN_SUBFIELD_GENERATED,
        RING_1, RING_1_IN_SUBFIELD_GENERATED, RING_ADD, RING_ADD_EQ_0,
        RING_ADD_IN_SUBFIELD_GENERATED, RING_ADD_LZERO, RING_ADD_RNEG, RING_ADD_RZERO,
        RING_ADD_SYM, RING_CARRIER_SUBFIELD_GENERATED_SUBSET, RING_DIV,
        RING_HOMOMORPHISM_I, RING_HOMOMORPHISM_INTEGER_RING_OF_INT,
        RING_HOMOMORPHISM_IN_CARRIER, RING_INV, RING_INV_IN_SUBFIELD_GENERATED,
        RING_MUL, RING_MUL_ASSOC, RING_MUL_IN_SUBFIELD_GENERATED, RING_MUL_LID,
        RING_MUL_LZERO, RING_MUL_RID, RING_NEG, RING_NEG_IN_SUBFIELD_GENERATED,
        RING_OF_INT, RING_OF_INT_0, RING_OF_INT_1, RING_OF_INT_ADD,
        RING_OF_INT_EQ_0_CHAR_0, RING_OF_INT_EQ_CHAR_0,
        RING_OF_INT_IN_SUBFIELD_GENERATED, RING_OF_INT_MUL, RING_OF_INT_NEG,
        RING_OF_INT_OF_NUM, RING_OF_INT_POW, RING_OF_INT_SUB, RING_OF_NUM,
        RING_OF_NUM_EQ_0, RING_POW, RING_POW_0, RING_POW_1,
        RING_POW_IN_SUBFIELD_GENERATED, RING_SIMPLE_ALGEBRAIC_EXTENSION_BASIS,
        RING_SIMPLE_ALGEBRAIC_EXTENSION_SPAN, RING_SPAN_SING, RING_SPAN_UNION,
        RING_SUB, RING_SUB_EQ_0, RING_SUB_REFL, RING_SUM_LT_2, SIMPLE_IMAGE_GEN,
        SQUAREFREE_0, SQUAREFREE_EXP, SUBFIELD_GENERATED, SUBFIELD_GENERATED_EQ,
        SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC, SUBSET, UNWIND_THM2, field_extension,
        free_basis, int_divides, number_field, poly_eval, ring_div, ring_sub, .. } := D.core2
  -- @@SCOPE END

  let INT_SQUARE_SUB_MUL_SQUARE_MOD_4 ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← INTEGER_RULE (← q r"!q a s b n:int. n divides (q * n + a) - (s * n + b) <=>
                    n divides (a - b)")
    let r2 ← INTEGER_RULE (← q r"!t e n:int. n divides t * n + e <=> n divides e")
    let r3 ← INTEGER_RULE (← q r"!t e c n:int. (t * n + e == c) (mod n) <=> (e == c) (mod n)")
    prove
      r"!d A B N:int.
          ~(&4 divides d) /\ A pow 2 - d * B pow 2 = &4 * N
          ==> if (d == &1) (mod &4) then &2 divides (A - B)
              else &2 divides A /\ &2 divides B"
      (REPEAT GEN_TAC THEN MP_TAC (← SPECL [(← q r"A:int"), (← q r"&2:int")] INT_DIVISION) THEN MP_TAC (← SPECL [(← q r"B:int"), (← q r"&2:int")] INT_DIVISION) THEN MP_TAC (← SPECL [(← q r"d:int"), (← q r"&4:int")] INT_DIVISION) THEN REWRITE_TAC [INT_OF_NUM_EQ, ARITH_EQ, INT_ABS_NUM] THEN SPEC_TAC ((← q r"d rem &4"), (← q r"e:int")) THEN SPEC_TAC ((← q r"d div &4"), (← q r"t:int")) THEN SPEC_TAC ((← q r"B rem &2"), (← q r"b:int")) THEN SPEC_TAC ((← q r"B div &2"), (← q r"s:int")) THEN SPEC_TAC ((← q r"A rem &2"), (← q r"a:int")) THEN SPEC_TAC ((← q r"A div &2"), (← q r"q:int")) THEN REPEAT GEN_TAC THEN REPEAT (DISCH_THEN (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN REWRITE_TAC [r3, r2, r1] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"&4 divides ((a:int) pow 2 - e * b pow 2)") MP_TAC THENL [REWRITE_TAC [int_divides] THEN EXISTS_TAC (← q r"N - (q pow 2 + q * a - &4 * t * s pow 2 - &4 * t * s * b -
                       t * b pow 2 - e * s pow 2 - e * s * b):int") THEN ASM_INT_ARITH_TAC, UNDISCH_TAC (← q r"~(&4 divides (e:int))")] THEN SUBGOAL_THEN (← q r"((a:int) = &0 \/ a = &1) /\ ((b:int) = &0 \/ b = &1) /\
      ((e:int) = &0 \/ e = &1 \/ e = &2 \/ e = &3)") MP_TAC THENL [ASM_INT_ARITH_TAC, ALL_TAC] THEN DISCH_THEN (CONJUNCTS_THEN2 (DISJ_CASES_THEN SUBST_ALL_TAC) (CONJUNCTS_THEN2 (DISJ_CASES_THEN SUBST_ALL_TAC) (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC))) THEN REWRITE_TAC [(← GSYM INT_REM_EQ_0), (← GSYM INT_REM_EQ)] THEN CONV_TAC INT_REDUCE_CONV)

  let INT_NORM_FORM_4_IMAGINARY ← prove
    r"!A B d:int.
        d < &0 /\ ~(d = -- &4) /\ A pow 2 - d * B pow 2 = &4
        ==> B = &0 /\ (A = &2 \/ A = -- &2) \/
            d = -- &1 /\ A = &0 /\ (B = &2 \/ B = -- &2) \/
            d = -- &3 /\ (A = &1 \/ A = -- &1) /\ (B = &1 \/ B = -- &1)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!x:int. x pow 2 <= &4
                        ==> x = -- &2 \/ x = -- &1 \/ x = &0 \/ x = &1 \/
                            x = &2") ASSUME_TAC THENL [X_GEN_TAC (← q r"x:int") THEN ONCE_REWRITE_TAC [(← GSYM INT_POW2_ABS)] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"abs(x:int) <= &2") MP_TAC THENL [REWRITE_TAC [(← GSYM INT_NOT_LT)] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(&3:int) pow 2 <= abs x pow 2") MP_TAC THENL [MATCH_MP_TAC INT_POW_LE2 THEN ASM_INT_ARITH_TAC, ASM_INT_ARITH_TAC], INT_ARITH_TAC], ALL_TAC] THEN SUBGOAL_THEN (← q r"(A:int) pow 2 <= &4 /\ (B:int) pow 2 <= &4") STRIP_ASSUME_TAC THENL [MP_TAC (← SPEC (← q r"A:int") INT_LE_POW_2) THEN MP_TAC (← SPEC (← q r"B:int") INT_LE_POW_2) THEN SUBGOAL_THEN (← q r"(B:int) pow 2 <= --d * B pow 2") MP_TAC THENL [GEN_REWRITE_TAC LAND_CONV [(← GSYM INT_MUL_LID)] THEN MATCH_MP_TAC INT_LE_RMUL THEN REWRITE_TAC [INT_LE_POW_2] THEN ASM_INT_ARITH_TAC, ASM_INT_ARITH_TAC], ALL_TAC] THEN FIRST_X_ASSUM (fun th => tactic_of do pure (MP_TAC (← MATCH_MP th (← ASSUME (← q r"(A:int) pow 2 <= &4"))) THEN MP_TAC (← MATCH_MP th (← ASSUME (← q r"(B:int) pow 2 <= &4"))))) THEN REPEAT (DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC)) THEN RULE_ASSUM_TAC (CONV_RULE INT_REDUCE_CONV) THEN CONV_TAC INT_REDUCE_CONV THEN ASM_INT_ARITH_TAC)

  let IN_SUBFIELD_GENERATED_MUL_CANCEL ← prove
    r"!k:A ring s a y.
        field k /\ a IN ring_carrier(subfield_generated k s) /\
        ~(a = ring_0 k) /\ y IN ring_carrier k /\
        ring_mul k a y IN ring_carrier(subfield_generated k s)
        ==> y IN ring_carrier(subfield_generated k s)"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"y = ring_mul k (ring_inv k a) (ring_mul k a y:A)") SUBST1_TAC THENL [ASM_SIMP_TAC [RING_MUL_ASSOC, RING_INV, FIELD_MUL_LINV, RING_MUL_LID], ASM_SIMP_TAC [RING_MUL_IN_SUBFIELD_GENERATED, RING_INV_IN_SUBFIELD_GENERATED, FIELD_SUBFIELD_GENERATED]])

  let SUBFIELD_GENERATED_ADD_MUL_EQ_0 ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"(~q ==> F) /\ (q ==> p) ==> p /\ q")
    prove
      r"!k:A ring s a b x.
          field k /\ x IN ring_carrier k /\
          ~(x IN ring_carrier(subfield_generated k s)) /\
          a IN ring_carrier(subfield_generated k s) /\
          b IN ring_carrier(subfield_generated k s)
          ==> (ring_add k a (ring_mul k b x) = ring_0 k <=>
               a = ring_0 k /\ b = ring_0 k)"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"s:A->bool")] RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN REWRITE_TAC [SUBSET] THEN DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"a:A") th) THEN MP_TAC (← SPEC (← q r"b:A") th))) THEN ASM_REWRITE_TAC [] THEN REPEAT DISCH_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [RING_MUL_LZERO, RING_ADD_LZERO, RING_0] THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [DISCH_TAC THEN UNDISCH_TAC (← q r"~(x IN ring_carrier(subfield_generated k s:A ring))") THEN REWRITE_TAC [] THEN MATCH_MP_TAC IN_SUBFIELD_GENERATED_MUL_CANCEL THEN EXISTS_TAC (← q r"b:A") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ring_mul k b x = ring_neg k a:A") SUBST1_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"ring_mul k b x:A")] RING_ADD_EQ_0) THEN ASM_SIMP_TAC [RING_MUL] THEN MESON_TAC [], ASM_SIMP_TAC [RING_NEG_IN_SUBFIELD_GENERATED]], DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"ring_add k a (ring_mul k (ring_0 k) x) = ring_0 k:A") THEN ASM_SIMP_TAC [RING_MUL_LZERO, RING_ADD_RZERO]])

  let SUBFIELD_GENERATED_HALF_SUCC ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_sub (r:A ring) (ring_add r (ring_1 r) x) (ring_1 r) = x")
    let r2 ← RING_RULE (← q r"!k:A ring y h.
           ring_mul k (ring_of_num k 2) h = ring_1 k
           ==> ring_mul k (ring_of_num k 2) (ring_mul k y h) = y")
    let r3 ← TAUT (← q r"p /\ (p ==> q) /\ (p /\ q ==> r) ==> p /\ q /\ r")
    prove
      r"!k:A ring s x.
          field k /\ ~(ring_of_num k 2 = ring_0 k) /\ x IN ring_carrier k
          ==> ring_div k (ring_add k (ring_1 k) x) (ring_of_num k 2)
                IN ring_carrier k /\
              ring_mul k (ring_of_num k 2)
                (ring_div k (ring_add k (ring_1 k) x) (ring_of_num k 2)) =
              ring_add k (ring_1 k) x /\
              (ring_div k (ring_add k (ring_1 k) x) (ring_of_num k 2)
                 IN ring_carrier(subfield_generated k s) <=>
               x IN ring_carrier(subfield_generated k s))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN ABBREV_TAC (← q r"w = ring_div k (ring_add k (ring_1 k) x) (ring_of_num k 2):A") THEN MATCH_MP_TAC r3 THEN REPEAT CONJ_TAC THENL [EXPAND_TAC "w" THEN ASM_SIMP_TAC [RING_DIV, RING_ADD, RING_1, RING_OF_NUM], DISCH_TAC THEN EXPAND_TAC "w" THEN REWRITE_TAC [ring_div] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_of_num k 2:A")] FIELD_MUL_RINV) THEN ASM_SIMP_TAC [RING_OF_NUM] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_add k (ring_1 k) x:A"), (← q r"ring_inv k (ring_of_num k 2):A")] r2) THEN ASM_SIMP_TAC [RING_ADD, RING_1, RING_INV, RING_OF_NUM], STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL [SUBGOAL_THEN (← q r"x = ring_sub k (ring_mul k (ring_of_num k 2) w) (ring_1 k):A") SUBST1_TAC THENL [ASM_SIMP_TAC [RING_1, r1], ALL_TAC], EXPAND_TAC "w" THEN REWRITE_TAC [ring_div]] THEN REWRITE_TAC [ring_sub, (← GSYM RING_OF_INT_OF_NUM)] THEN ASM_SIMP_TAC [RING_ADD_IN_SUBFIELD_GENERATED, RING_NEG_IN_SUBFIELD_GENERATED, RING_MUL_IN_SUBFIELD_GENERATED, RING_1_IN_SUBFIELD_GENERATED, RING_INV_IN_SUBFIELD_GENERATED, FIELD_SUBFIELD_GENERATED, RING_OF_INT_IN_SUBFIELD_GENERATED]])

  let FREE_BASIS_SUBFIELD_GENERATED_2 ← prove
    r"!k:A ring s x.
        field k /\ x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k s)) /\
        (!z. z IN ring_carrier k
             ==> ?a b. a IN ring_carrier(subfield_generated k s) /\
                       b IN ring_carrier(subfield_generated k s) /\
                       z = ring_add k a (ring_mul k b x))
        ==> free_basis (subfield_generated k s,k) I 2
                       (\i. if i = 0 then ring_1 k else x)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"s:A->bool")] RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN REWRITE_TAC [SUBSET] THEN DISCH_TAC THEN REWRITE_TAC [free_basis, FORALL_LT_2, ARITH_EQ, I_THM] THEN ASM_REWRITE_TAC [RING_1] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"z:A") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (← do let c := (← ASSUME (← q r"(z:A) IN ring_carrier k")); pure (fun th => MATCH_MP th c))) THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN EXISTS_TAC (← q r"\i. if i = 0 then a else b:A") THEN ASM_SIMP_TAC [FORALL_LT_2, ARITH_EQ, RING_SUM_LT_2, RING_MUL, RING_1, RING_MUL_RID], X_GEN_TAC (← q r"c:num->A") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"s:A->bool"), (← q r"(c:num->A) 0"), (← q r"(c:num->A) 1"), (← q r"x:A")] SUBFIELD_GENERATED_ADD_MUL_EQ_0) THEN UNDISCH_TAC (← q r"ring_sum k {i | i < 2}
        (\i. ring_mul k (c i) (if i = 0 then ring_1 k else x)) =
      ring_0 k:A") THEN ASM_SIMP_TAC [RING_SUM_LT_2, RING_MUL, RING_1, ARITH_EQ, RING_MUL_RID, (← CONJUNCT2 SUBFIELD_GENERATED)]])

  let INTEGRAL_ELEMENT_QUADRATIC ← prove
    r"!k:A ring z b c.
        z IN ring_carrier k /\
        ring_add k (ring_pow k z 2)
                   (ring_add k (ring_mul k (ring_of_int k b) z)
                               (ring_of_int k c)) = ring_0 k
        ==> integral_element (integer_ring,k) (ring_of_int k) z"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_ELEMENT_FROM_RELATION THEN MAP_EVERY EXISTS_TAC [(← q r"2"), (← q r"\i. if i = 0 then c else b:int")] THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, INTEGER_RING, IN_UNIV, RING_SUM_LT_2, RING_MUL, RING_OF_INT, RING_POW, ARITH_EQ, RING_POW_0, RING_POW_1, RING_MUL_RID] THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [RING_ADD_SYM, RING_MUL, RING_OF_INT])

  let PRIME_SUBFIELD_SQRT_INTEGER ← prove
    r"!k:A ring x m.
        field k /\ ring_char k = 0 /\
        x IN ring_carrier(subfield_generated k {ring_0 k}) /\
        ring_pow k x 2 = ring_of_int k m
        ==> ?n. x = ring_of_int k n /\ m = n pow 2"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A")] INTEGRAL_ELEMENT_PRIME_SUBFIELD) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC INTEGRAL_ELEMENT_QUADRATIC THEN MAP_EVERY EXISTS_TAC [(← q r"&0:int"), (← q r"--m:int")] THEN ASM_SIMP_TAC [RING_OF_INT_0, RING_OF_INT_NEG, RING_MUL_LZERO, RING_ADD_LZERO, RING_NEG, RING_OF_INT, RING_ADD_RNEG], MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"n:int") THEN DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"ring_pow (k:A ring) (ring_of_int k n) 2 = ring_of_int k m") THEN ASM_SIMP_TAC [(← GSYM RING_OF_INT_POW), RING_OF_INT_EQ_CHAR_0] THEN MESON_TAC []])

  let PRIME_SUBFIELD_SQUAREFREE_MUL_SQUARE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← INT_ARITH (← q r"(d * t:int) pow 2 = d * d * t pow 2")
    let r2 ← RING_RULE (← q r"ring_pow (k:A ring) (ring_mul k d b) 2 =
      ring_mul k d (ring_mul k d (ring_pow k b 2))")
    prove
      r"!k:A ring b d m.
          field k /\ ring_char k = 0 /\
          b IN ring_carrier(subfield_generated k {ring_0 k}) /\
          squarefree(num_of_int(abs d)) /\
          ring_mul k (ring_of_int k d) (ring_pow k b 2) = ring_of_int k m
          ==> ?n. b = ring_of_int k n /\ m = d * n pow 2"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"(b:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(d:int = &0)") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"squarefree(num_of_int(abs(&0:int)))") THEN REWRITE_TAC [INT_ABS_NUM, NUM_OF_INT_OF_NUM, SQUAREFREE_0], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_mul k (ring_of_int k d) b:A"), (← q r"d * m:int")] PRIME_SUBFIELD_SQRT_INTEGER) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_MUL_IN_SUBFIELD_GENERATED, RING_OF_INT_IN_SUBFIELD_GENERATED, RING_OF_INT_MUL, RING_OF_INT, r2], DISCH_THEN (X_CHOOSE_THEN (← q r"n:int") STRIP_ASSUME_TAC)] THEN SUBGOAL_THEN (← q r"(d:int) divides n") MP_TAC THENL [MATCH_MP_TAC INT_SQUAREFREE_DIVPOW THEN EXISTS_TAC (← q r"2") THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN CONV_TAC INTEGER_RULE, REWRITE_TAC [int_divides] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"t:int") SUBST_ALL_TAC)] THEN EXISTS_TAC (← q r"t:int") THEN CONJ_TAC THENL [MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN MAP_EVERY EXISTS_TAC [(← q r"k:A ring"), (← q r"ring_of_int k d:A")] THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, RING_OF_INT, RING_OF_INT_EQ_0_CHAR_0, (← GSYM RING_OF_INT_MUL)], UNDISCH_TAC (← q r"d * m = (d * t:int) pow 2") THEN REWRITE_TAC [r1] THEN ASM_REWRITE_TAC [INT_EQ_MUL_LCANCEL]])

  let SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD ← prove
    r"!k:A ring x d.
        field k /\ ring_char k = 0 /\ ring_pow k x 2 = ring_of_int k d /\
        squarefree(num_of_int(abs d)) /\ ~(d = &1)
        ==> ~(x IN ring_carrier(subfield_generated k {ring_0 k}))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"d:int")] PRIME_SUBFIELD_SQRT_INTEGER) THEN ASM_REWRITE_TAC [NOT_EXISTS_THM] THEN X_GEN_TAC (← q r"n:int") THEN DISCH_THEN (SUBST_ALL_TAC o CONJUNCT2) THEN UNDISCH_TAC (← q r"squarefree(num_of_int(abs((n:int) pow 2)))") THEN REWRITE_TAC [INT_ABS_POW, NUM_OF_INT_ABS_POW, SQUAREFREE_EXP, ARITH_EQ] THEN DISCH_THEN (MP_TAC o (AP_TERM (← q r"int_of_num"))) THEN SIMP_TAC [INT_OF_NUM_OF_INT, INT_ABS_POS] THEN UNDISCH_TAC (← q r"~((n:int) pow 2 = &1)") THEN ONCE_REWRITE_TAC [(← GSYM INT_POW2_ABS)] THEN MESON_TAC [INT_POW_ONE])

  let QUADRATIC_FIELD_FREE_BASIS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"(p <=> q) /\ r ==> p ==> q /\ r")
    prove
      r"!k:A ring y.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
          y IN ring_carrier k /\
          ~(y IN ring_carrier(subfield_generated k {ring_0 k}))
          ==> free_basis (subfield_generated k {ring_0 k},k) I 2
                         (\i. if i = 0 then ring_1 k else y)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"y:A")] NUMBER_FIELD_ALGEBRAIC) THEN FIRST_ASSUM (MP_TAC o (CONJUNCT2 o (GEN_REWRITE_RULE id [number_field]))) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"q = subfield_generated (k:A ring) {ring_0 k}") THEN REPEAT DISCH_TAC THEN SUBGOAL_THEN (← q r"field(q:A ring) /\ field_extension(q,k) (I:A->A)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "q" THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, FIELD_EXTENSION_SUBFIELD_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"poly_deg q (minimal_polynomial (q,k) (I:A->A) y) = 2") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"q:A ring"), (← q r"k:A ring"), (← q r"y:A")] MINIMAL_POLYNOMIAL_DEG_LE_EXTENSION_DEGREE) THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"q:A ring"), (← q r"k:A ring"), (← q r"y:A")] MINIMAL_POLYNOMIAL_DEG_EQ_1) THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"q:A ring"), (← q r"k:A ring"), (← q r"y:A")] MINIMAL_POLYNOMIAL_IRREDUCIBLE) THEN ASM_SIMP_TAC [IMAGE_I] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o ((MATCH_MP IRREDUCIBLE_IMP_POLY_DEG_NZ) o (CONJ (← ASSUME (← q r"field(q:A ring)"))))) THEN ASM_ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"q:A ring"), (← q r"k:A ring"), (← q r"y:A")] SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC) THEN ASM_REWRITE_TAC [IMAGE_I] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"subfield_generated k ((y:A) INSERT ring_carrier q) = k") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"I:A->A"), (← q r"q:A ring"), (← q r"subfield_generated k ((y:A) INSERT ring_carrier q)"), (← q r"k:A ring")] EXTENSION_DEGREE_EQ_TOWER) THEN ASM_SIMP_TAC [FINITE_IMP_FIELD_EXTENSION, FIELD_EXTENSION_SUBFIELD_GENERATED, I_O_ID, IMAGE_I, SUBFIELD_GENERATED_EQ], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"q:A ring"), (← q r"k:A ring"), (← q r"y:A")] RING_SIMPLE_ALGEBRAIC_EXTENSION_BASIS) THEN ASM_REWRITE_TAC [IMAGE_I] THEN ASM_SIMP_TAC [FREE_BASIS_FIELD, FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [AP_TERM_TAC THEN GEN_REWRITE_TAC LAND_CONV [SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC IMAGE_EQ THEN REWRITE_TAC [IN_ELIM_THM, FORALL_LT_2, ARITH_EQ] THEN ASM_SIMP_TAC [RING_POW_0, RING_POW_1], REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_LT_2, ARITH_EQ] THEN SUBGOAL_THEN (← q r"ring_1 k IN ring_carrier(q:A ring)") MP_TAC THENL [EXPAND_TAC "q" THEN REWRITE_TAC [RING_1_IN_SUBFIELD_GENERATED], ASM_MESON_TAC []]])

  let QUADRATIC_FIELD_COORDINATES ← prove
    r"!k:A ring x z.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
        z IN ring_carrier k
        ==> ?a b. a IN ring_carrier(subfield_generated k {ring_0 k}) /\
                  b IN ring_carrier(subfield_generated k {ring_0 k}) /\
                  z = ring_add k a (ring_mul k b x)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A")] QUADRATIC_FIELD_FREE_BASIS) THEN ASM_REWRITE_TAC [free_basis] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"z:A")) o (CONJUNCT1 o CONJUNCT2))) THEN ASM_SIMP_TAC [FORALL_LT_2, ARITH_EQ, I_THM, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"c:num->A") THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"(c:num->A) 0"), (← q r"(c:num->A) 1")] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{ring_0 k:A}")] RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN REWRITE_TAC [SUBSET] THEN DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"(c:num->A) 0") th) THEN MP_TAC (← SPEC (← q r"(c:num->A) 1") th))) THEN ASM_SIMP_TAC [RING_SUM_LT_2, RING_MUL, RING_1, ARITH_EQ, RING_MUL_RID])

  let QUADRATIC_FIELD_INT_COORDINATES_EQ ← prove
    r"!k (x:A) a b a' b'.
        field k /\ ring_char k = 0 /\ x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k {ring_0 k}))
        ==> (ring_add k (ring_of_int k a) (ring_mul k (ring_of_int k b) x) =
             ring_add k (ring_of_int k a') (ring_mul k (ring_of_int k b') x) <=>
             a = a' /\ b = b')"
    (REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{ring_0 k:A}"), (← q r"ring_of_int k (a - a'):A"), (← q r"ring_of_int k (b - b'):A"), (← q r"x:A")] SUBFIELD_GENERATED_ADD_MUL_EQ_0) THEN ASM_REWRITE_TAC [RING_OF_INT_IN_SUBFIELD_GENERATED] THEN ASM_SIMP_TAC [RING_OF_INT_EQ_0_CHAR_0, INT_SUB_0] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [RING_OF_INT_SUB] THEN UNDISCH_TAC (← q r"ring_add k (ring_of_int k a) (ring_mul k (ring_of_int k b) x) =
    ring_add k (ring_of_int k a') (ring_mul k (ring_of_int k b') (x:A))") THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:int")] RING_OF_INT) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"b:int")] RING_OF_INT) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a':int")] RING_OF_INT) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"b':int")] RING_OF_INT) THEN UNDISCH_TAC (← q r"(x:A) IN ring_carrier k") THEN MAP_EVERY (fun t => tactic_of do pure (SPEC_TAC (t, (← (do let z1 ← (do let z2 ← (pure t); pure (type_of z2)); genvar z1))))) [(← q r"ring_of_int k a:A"), (← q r"ring_of_int k b:A"), (← q r"ring_of_int k a':A"), (← q r"ring_of_int k b':A"), (← q r"x:A")] THEN RING_TAC)

  let QUADRATIC_FIELD_INTEGER_SQUARE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!k:A ring y a b D m0 m1.
          ring_pow k y 2 = ring_add k a (ring_mul k b y) /\
          ring_mul k D a = m0 /\ ring_mul k D b = m1
          ==> ring_pow k (ring_sub k (ring_mul k (ring_mul k (ring_of_num k 2)
                                                             D) y) m1) 2 =
              ring_add k (ring_mul k (ring_of_num k 4) (ring_mul k D m0))
                         (ring_pow k m1 2)")
    let r2 ← RING_RULE (← q r"ring_add (r:A ring) (ring_sub r x y) y = x")
    prove
      r"!k:A ring.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2
          ==> ?w m. w IN ring_carrier k /\
                    ~(w IN ring_carrier(subfield_generated k {ring_0 k})) /\
                    ring_pow k w 2 = ring_of_int k m"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (fun th => tactic_of do pure (ASSUME_TAC (← MATCH_MP NUMBER_FIELD_IMP_FIELD th) THEN STRIP_ASSUME_TAC (← REWRITE_RULE [number_field] th))) THEN SUBGOAL_THEN (← q r"?y:A. y IN ring_carrier k /\
            ~(y IN ring_carrier(subfield_generated k {ring_0 k}))") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"k:A ring") NUMBER_FIELD_DEGREE_EQ_1) THEN ASM_REWRITE_TAC [ARITH_EQ] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{ring_0 k:A}")] RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"y:A"), (← q r"ring_pow k y 2:A")] QUADRATIC_FIELD_COORDINATES) THEN ASM_SIMP_TAC [RING_POW, LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{0,1}"), (← q r"\i. if i = 0 then a else b:A")] PRIME_SUBFIELD_COMMON_DENOMINATOR) THEN ASM_REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY, FORALL_IN_INSERT, NOT_IN_EMPTY, ARITH_EQ, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"D:int") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q r"m0:int")) (X_CHOOSE_TAC (← q r"m1:int")))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{ring_0 k:A}")] RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN REWRITE_TAC [SUBSET] THEN DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"a:A") th) THEN MP_TAC (← SPEC (← q r"b:A") th))) THEN ASM_REWRITE_TAC [] THEN REPEAT DISCH_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"ring_sub k (ring_mul k (ring_of_int k (&2 * D)) y) (ring_of_int k m1):A"), (← q r"(&4 * D * m0 + m1 pow 2):int")] THEN ASM_SIMP_TAC [RING_SUB, RING_MUL, RING_OF_INT] THEN CONJ_TAC THENL [DISCH_TAC THEN UNDISCH_TAC (← q r"~(y IN ring_carrier(subfield_generated k {ring_0 k:A}))") THEN REWRITE_TAC [] THEN MATCH_MP_TAC IN_SUBFIELD_GENERATED_MUL_CANCEL THEN EXISTS_TAC (← q r"ring_of_int k (&2 * D):A") THEN ASM_SIMP_TAC [RING_OF_INT_IN_SUBFIELD_GENERATED, RING_OF_INT_EQ_0_CHAR_0, INT_ENTIRE, INT_OF_NUM_EQ, ARITH_EQ] THEN SUBGOAL_THEN (← q r"ring_mul k (ring_of_int k (&2 * D)) y =
        ring_add k
         (ring_sub k (ring_mul k (ring_of_int k (&2 * D)) y) (ring_of_int k m1))
         (ring_of_int k m1):A") SUBST1_TAC THENL [ASM_SIMP_TAC [RING_MUL, RING_OF_INT, r2], ASM_SIMP_TAC [RING_ADD_IN_SUBFIELD_GENERATED, RING_OF_INT_IN_SUBFIELD_GENERATED]], MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"y:A"), (← q r"a:A"), (← q r"b:A"), (← q r"ring_of_int k D:A"), (← q r"ring_of_int k m0:A"), (← q r"ring_of_int k m1:A")] r1) THEN ASM_SIMP_TAC [RING_OF_INT, RING_OF_INT_MUL, RING_OF_INT_ADD, RING_OF_INT_POW, RING_OF_INT_OF_NUM]])

  let QUADRATIC_FIELD_SQRT_EXISTS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← INTEGRAL_DOMAIN_RULE (← q r"!r x:A. integral_domain r /\ x IN ring_carrier r /\
            ring_pow r x 2 = ring_1 r
            ==> x = ring_1 r \/ x = ring_neg r (ring_1 r)")
    let r2 ← RING_RULE (← q r"!k:A ring c x d.
           ring_pow k (ring_mul k c x) 2 = ring_mul k d (ring_pow k c 2)
           ==> ring_mul k (ring_pow k c 2) (ring_pow k x 2) =
               ring_mul k (ring_pow k c 2) d")
    prove
      r"!k:A ring.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2
          ==> ?d x. squarefree(num_of_int(abs d)) /\ ~(d = &1) /\
                    x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (fun th => tactic_of do pure (ASSUME_TAC (← MATCH_MP NUMBER_FIELD_IMP_FIELD th) THEN STRIP_ASSUME_TAC (← REWRITE_RULE [number_field] th))) THEN MP_TAC (← ISPEC (← q r"k:A ring") QUADRATIC_FIELD_INTEGER_SQUARE) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"w:A"), (← q r"m:int")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"~(m:int = &0)") MP_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~(w IN ring_carrier(subfield_generated k {ring_0 k:A}))") THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"w:A"), (← q r"2")] INTEGRAL_DOMAIN_POW_EQ_0) THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, RING_OF_INT_0, ARITH_EQ] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [RING_0_IN_SUBFIELD_GENERATED], DISCH_THEN (MP_TAC o (MATCH_MP INT_SQUAREFREE_DECOMPOSITION))] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"d:int"), (← q r"c:num")] THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN SUBGOAL_THEN (← q r"~(ring_of_num k c:A = ring_0 k)") ASSUME_TAC THENL [ASM_REWRITE_TAC [RING_OF_NUM_EQ_0, DIVIDES_ZERO], ALL_TAC] THEN SUBGOAL_THEN (← q r"?x:A. x IN ring_carrier k /\ ring_mul k (ring_of_num k c) x = w") STRIP_ASSUME_TAC THENL [EXISTS_TAC (← q r"ring_mul k (ring_inv k (ring_of_num k c)) w:A") THEN ASM_SIMP_TAC [RING_MUL, RING_INV, RING_MUL_ASSOC, RING_OF_NUM, FIELD_MUL_RINV, RING_MUL_LID], FIRST_X_ASSUM (SUBST_ALL_TAC o (SYM o (checkM (fun th => (do let z6 ← (q r"w:A"); let z5 ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); liftExcept (rhs z3)); pure (z5 == z6))))))] THEN SUBGOAL_THEN (← q r"ring_pow k x 2 = ring_of_int k d:A") ASSUME_TAC THENL [MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN MAP_EVERY EXISTS_TAC [(← q r"k:A ring"), (← q r"ring_pow k (ring_of_num k c) 2:A")] THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, RING_POW, RING_OF_NUM, RING_OF_INT, INTEGRAL_DOMAIN_POW_EQ_0, ARITH_EQ] THEN UNDISCH_TAC (← q r"ring_pow k (ring_mul k (ring_of_num k c) x) 2 =
        ring_of_int k (d * &c pow 2):A") THEN REWRITE_TAC [RING_OF_INT_MUL, RING_OF_INT_POW, RING_OF_INT_OF_NUM] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_of_num k c:A"), (← q r"x:A"), (← q r"ring_of_int k d:A")] r2) THEN ASM_SIMP_TAC [RING_OF_NUM, RING_OF_INT], ALL_TAC] THEN MAP_EVERY EXISTS_TAC [(← q r"d:int"), (← q r"x:A")] THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~(ring_mul k (ring_of_num k c) x IN
                   ring_carrier (subfield_generated k {ring_0 k:A}))") THEN REWRITE_TAC [] THEN MATCH_MP_TAC RING_MUL_IN_SUBFIELD_GENERATED THEN REWRITE_TAC [(← GSYM RING_OF_INT_OF_NUM), RING_OF_INT_IN_SUBFIELD_GENERATED] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A")] r1) THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, (← GSYM RING_OF_INT_1)] THEN STRIP_TAC THEN ASM_SIMP_TAC [RING_OF_INT_1, RING_1_IN_SUBFIELD_GENERATED, RING_NEG_IN_SUBFIELD_GENERATED])

  let QUADRATIC_FIELD_SQRT_UNIQUE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!k:A ring x b D E.
           ring_pow k x 2 = D /\
           ring_pow k (ring_add k (ring_0 k) (ring_mul k b x)) 2 = E
           ==> ring_mul k D (ring_pow k b 2) = E")
    let r2 ← RING_RULE (← q r"!k:A ring x a b D E.
             ring_pow k x 2 = D /\
             ring_pow k (ring_add k a (ring_mul k b x)) 2 = E
             ==> ring_add k
                  (ring_sub k (ring_add k (ring_pow k a 2)
                                          (ring_mul k (ring_pow k b 2) D)) E)
                  (ring_mul k (ring_mul k (ring_of_num k 2) (ring_mul k a b))
                              x) = ring_0 k")
    prove
      r"!k:A ring x y d e.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
          x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
          squarefree(num_of_int(abs d)) /\ ~(d = &1) /\
          y IN ring_carrier k /\ ring_pow k y 2 = ring_of_int k e /\
          squarefree(num_of_int(abs e)) /\ ~(e = &1)
          ==> d = e"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (fun th => tactic_of do pure (ASSUME_TAC (← MATCH_MP NUMBER_FIELD_IMP_FIELD th) THEN STRIP_ASSUME_TAC (← REWRITE_RULE [number_field] th))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"y:A"), (← q r"e:int")] SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"d:int")] SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD) THEN ASM_REWRITE_TAC [] THEN REPEAT DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"y:A")] QUADRATIC_FIELD_COORDINATES) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{ring_0 k:A}")] RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN REWRITE_TAC [SUBSET] THEN DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"a:A") th) THEN MP_TAC (← SPEC (← q r"b:A") th))) THEN ASM_REWRITE_TAC [] THEN REPEAT DISCH_TAC THEN SUBGOAL_THEN (← q r"a = ring_0 k:A") SUBST_ALL_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{ring_0 k:A}"), (← q r"ring_sub k (ring_add k (ring_pow k a 2)
                                (ring_mul k (ring_pow k b 2) (ring_of_int k d)))
                    (ring_of_int k e):A"), (← q r"ring_mul k (ring_of_num k 2) (ring_mul k a b):A"), (← q r"x:A")] SUBFIELD_GENERATED_ADD_MUL_EQ_0) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [ring_sub] THEN REPEAT (FIRST [CONJ_TAC, MATCH_MP_TAC RING_ADD_IN_SUBFIELD_GENERATED, MATCH_MP_TAC RING_NEG_IN_SUBFIELD_GENERATED, MATCH_MP_TAC RING_MUL_IN_SUBFIELD_GENERATED, MATCH_MP_TAC RING_POW_IN_SUBFIELD_GENERATED]) THEN ASM_REWRITE_TAC [RING_OF_INT_IN_SUBFIELD_GENERATED, (← GSYM RING_OF_INT_OF_NUM)], DISCH_THEN (fun z3 => tactic_of do pure (MP_TAC (← (do pure (Prod.fst (← (do pure (← EQ_IMP_RULE z3))))))))] THEN ANTS_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"a:A"), (← q r"b:A"), (← q r"ring_of_int k d:A"), (← q r"ring_of_int k e:A")] r2) THEN ASM_SIMP_TAC [RING_OF_INT], DISCH_THEN (MP_TAC o CONJUNCT2)] THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_MUL_EQ_0, FIELD_IMP_INTEGRAL_DOMAIN, RING_MUL, RING_OF_NUM, RING_OF_NUM_EQ_0, DIVIDES_ZERO, ARITH_EQ] THEN ASM_CASES_TAC (← q r"b = ring_0 k:A") THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"~(ring_add k a (ring_mul k b x) IN
                     ring_carrier(subfield_generated k {ring_0 k:A}))") THEN ASM_SIMP_TAC [RING_MUL_LZERO, RING_ADD_RZERO], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"b:A"), (← q r"d:int"), (← q r"e:int")] PRIME_SUBFIELD_SQUAREFREE_MUL_SQUARE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"b:A"), (← q r"ring_of_int k d:A"), (← q r"ring_of_int k e:A")] r1) THEN ASM_SIMP_TAC [RING_OF_INT], DISCH_THEN (X_CHOOSE_THEN (← q r"n:int") (SUBST_ALL_TAC o CONJUNCT2))] THEN MATCH_MP_TAC INT_SQUAREFREE_MUL_SQUARE THEN EXISTS_TAC (← q r"d * n:int") THEN ASM_REWRITE_TAC [] THEN INT_ARITH_TAC)

  let QUADRATIC_FIELD_SQRT ← prove
    r"!k:A ring.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2
        ==> ?!d. squarefree(num_of_int(abs d)) /\ ~(d = &1) /\
                 ?x. x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL [MP_TAC (← ISPEC (← q r"k:A ring") QUADRATIC_FIELD_SQRT_EXISTS) THEN ASM_REWRITE_TAC [] THEN MESON_TAC [], MAP_EVERY X_GEN_TAC [(← q r"d:int"), (← q r"e:int")] THEN STRIP_TAC THEN MATCH_MP_TAC QUADRATIC_FIELD_SQRT_UNIQUE THEN MAP_EVERY EXISTS_TAC [(← q r"k:A ring"), (← q r"x:A"), (← q r"x':A")] THEN ASM_REWRITE_TAC []])

  let FIELD_EXTENSION_SQRT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"n < 2 <=> n = 0 \/ n = 1")
    prove
      r"!k:A ring c.
          field k /\ c IN ring_carrier k /\
          ~(?y. y IN ring_carrier k /\ ring_pow k y 2 = c)
          ==> ?l h z:((1->num)->A)->bool.
                 field_extension(k,l) h /\ z IN ring_carrier l /\
                 ring_pow l z 2 = h c /\
                 !y. y IN ring_carrier l
                     ==> ?a b. a IN ring_carrier k /\ b IN ring_carrier k /\
                               y = ring_add l (h a) (ring_mul l (h b) z)"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"2"), (← q r"c:A")] POLY_VAR_POW_SUB_CONST) THEN ASM_SIMP_TAC [FIELD_NONTRIVIAL, ARITH_EQ] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"poly_sub k (poly_pow k (poly_var k one) 2) (poly_const k (c:A))")] KRONECKER_SIMPLE_FIELD_EXTENSION) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [ARITH_EQ, NOT_EXISTS_THM] THEN X_GEN_TAC (← q r"y:A") THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"k:A ring"), (← q r"k:A ring"), (← q r"2"), (← q r"c:A"), (← q r"y:A")] POLY_EVAL_VAR_POW_SUB_CONST) THEN ASM_CASES_TAC (← q r"(y:A) IN ring_carrier k") THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_I, I_O_ID, I_THM, RING_SUB_EQ_0, RING_POW] THEN ASM_MESON_TAC [], REWRITE_TAC [LEFT_IMP_EXISTS_THM]] THEN MAP_EVERY X_GEN_TAC [(← q r"l:(((1->num)->A)->bool) ring"), (← q r"h:A->((1->num)->A)->bool"), (← q r"z:((1->num)->A)->bool")] THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"l:(((1->num)->A)->bool) ring"), (← q r"h:A->((1->num)->A)->bool"), (← q r"z:((1->num)->A)->bool")] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FIELD_EXTENSION_IMP_HOMOMORPHISM)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [field_extension]))) THEN SUBGOAL_THEN (← q r"(h:A->((1->num)->A)->bool) c IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->((1->num)->A)->bool"), (← q r"k:A ring"), (← q r"l:(((1->num)->A)->bool) ring"), (← q r"2"), (← q r"c:A"), (← q r"z:((1->num)->A)->bool")] POLY_EVAL_VAR_POW_SUB_CONST) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o SYM) THEN ASM_SIMP_TAC [RING_SUB_EQ_0, RING_POW] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->((1->num)->A)->bool"), (← q r"k:A ring"), (← q r"l:(((1->num)->A)->bool) ring"), (← q r"poly_sub k (poly_pow k (poly_var k one) 2) (poly_const k (c:A))"), (← q r"z:((1->num)->A)->bool")] RING_SIMPLE_ALGEBRAIC_EXTENSION_SPAN) THEN ASM_SIMP_TAC [POLY_RING_CLAUSES, POLY_EXTEND_EVALUATE, (← GSYM poly_eval), RING_SUB_REFL] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN SUBGOAL_THEN (← q r"{ring_pow l z n | n < 2} =
                  {ring_1 l} UNION {z:((1->num)->A)->bool}") SUBST1_TAC THENL [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_UNION, IN_SING, UNWIND_THM2, r1, RIGHT_OR_DISTRIB, EXISTS_OR_THM] THEN ASM_SIMP_TAC [RING_POW_0, RING_POW_1], ASM_SIMP_TAC [RING_SPAN_UNION, RING_SPAN_SING, RING_1, IN_ELIM_THM]] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [RING_MUL_RID, RING_HOMOMORPHISM_IN_CARRIER])

  -- @@RETURN BEGIN
  return { INT_SQUARE_SUB_MUL_SQUARE_MOD_4, INT_NORM_FORM_4_IMAGINARY,
           IN_SUBFIELD_GENERATED_MUL_CANCEL, SUBFIELD_GENERATED_ADD_MUL_EQ_0,
           SUBFIELD_GENERATED_HALF_SUCC, FREE_BASIS_SUBFIELD_GENERATED_2,
           INTEGRAL_ELEMENT_QUADRATIC, PRIME_SUBFIELD_SQRT_INTEGER,
           PRIME_SUBFIELD_SQUAREFREE_MUL_SQUARE, SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD,
           QUADRATIC_FIELD_FREE_BASIS, QUADRATIC_FIELD_COORDINATES,
           QUADRATIC_FIELD_INT_COORDINATES_EQ, QUADRATIC_FIELD_INTEGER_SQUARE,
           QUADRATIC_FIELD_SQRT_EXISTS, QUADRATIC_FIELD_SQRT_UNIQUE,
           QUADRATIC_FIELD_SQRT, FIELD_EXTENSION_SQRT }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- quadratic.ml phrases from line 745 to 1376                             -/
/- ---------------------------------------------------------------------- -/

structure Quadratic02 where
  -- @@FIELDS
  QUADRATIC_FIELD_EXISTS : thm
  QUADRATIC_EXTEND_HOMOMORPHISM : thm
  QUADRATIC_FIELD_UNIQUE_EXPLICIT : thm
  QUADRATIC_FIELD_UNIQUE : thm
  QUADRATIC_FIELD_TRACE : thm
  QUADRATIC_FIELD_INTEGRAL_COORDINATES : thm
  QUADRATIC_FIELD_INTEGRAL_FREE_BASIS : thm
  QUADRATIC_FIELD_INTEGRAL_BASIS_SQRT : thm
  QUADRATIC_FIELD_INTEGRAL_BASIS_HALF : thm
  QUADRATIC_FIELD_INTEGRAL_BASIS : thm
  QUADRATIC_FIELD_BASIS_DISCRIMINANT : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupQuadratic02 [HolBase] (D : QuadraticDeps) (BQuadratic01 : Quadratic01) :
    ExceptT String IO Quadratic02 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, INT_ARITH, INT_ARITH_TAC, MESON_TAC, NUM_REDUCE_CONV, RING_RULE,
        SET_TAC, TAUT, .. } := D
  let { ALGEBRAIC_OVER_IMAGE, ALGEBRAIC_OVER_POW_EQ, ALGEBRA_TRACE_ADD,
        ALGEBRA_TRACE_FREE_BASIS, ALGEBRA_TRACE_NORM_BASE_FREE_BASIS,
        ALGEBRA_TRACE_NORM_IN_CARRIER, ALGEBRA_TRACE_SCALAR, ARITH, ARITH_EQ,
        BASIS_COORDINATES_BASIS, BASIS_COORDINATES_LMUL, COEFF_POLY_CONST,
        COEFF_POLY_SUB, COEFF_POLY_VARPOW, DIVIDES_ZERO, EQ_SYM_EQ, EXTENSION,
        FIELD_EXTENSION_IMP_HOMOMORPHISM, FIELD_EXTENSION_SUBFIELD_GENERATED,
        FIELD_IMP_INTEGRAL_DOMAIN, FIELD_IMP_NONTRIVIAL_RING, FIELD_NONTRIVIAL,
        FIELD_REAL_RING, FIELD_RING_HOMOMORPHISM_MONOMORPHISM,
        FIELD_SUBFIELD_GENERATED, FINITE_NUMSEG_LT, FORALL_LT_2,
        FREE_BASIS_INTEGER_RING_SUBRING_GENERATED, FUN_IN_IMAGE, IMAGE_I, IMP_CONJ,
        INTEGRAL_DOMAIN_MUL_LCANCEL, INTEGRAL_DOMAIN_SQUARE_EQ, INT_ABS_NUM,
        INT_DIVIDES_NUM_OF_INT_ABS, IN_ELIM_THM, IN_IMAGE, IN_INSERT, IN_INTER,
        IN_SUBRING_MUL, IN_SUBRING_POW, IN_SUBRING_SUB, IN_UNIV, I_O_ID, I_THM,
        LEFT_IMP_EXISTS_THM, MINIMAL_POLYNOMIAL_UNIQUE, MONO_EXISTS, NOT_EXISTS_THM,
        NUMBER_FIELD_ALT, NUMBER_FIELD_FREE_BASIS_DEGREE, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_TRACE_INTEGRAL_Q, NUM_OF_INT_OF_NUM, POLY_DEG_2_IRREDUCIBLE,
        POLY_EVAL_VAR_POW_SUB_CONST, POLY_EXTEND_CONST, POLY_EXTEND_SUB,
        POLY_EXTEND_VARPOW, POLY_VAR_POW_SUB_CONST, .. } := D.core1
  let { PRIME_SUBFIELD_HOMOMORPHISM_EXISTS, PRIME_SUBFIELD_MONOMORPHIC_IMAGE,
        PRIME_SUBFIELD_SUBFIELD_GENERATED, REAL_RING_CHAR, RIGHT_FORALL_IMP_THM,
        RING_0, RING_0_IN_SUBFIELD_GENERATED, RING_1, RING_1_IN_SUBFIELD_GENERATED,
        RING_ADD, RING_ADD_IN_SUBFIELD_GENERATED, RING_ADD_IN_SUBRING_GENERATED,
        RING_ADD_LZERO, RING_ADD_RNEG, RING_ADD_RZERO,
        RING_CARRIER_SUBFIELD_GENERATED_SUBSET, RING_CHAR_MONOMORPHIC_IMAGE,
        RING_CHAR_SUBFIELD_GENERATED, RING_DET_DIAGONAL, RING_HOMOMORPHISM_ADD,
        RING_HOMOMORPHISM_I, RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_RING_OF_INT,
        RING_HOMOMORPHISM_SUBFIELD_INCLUSION, RING_ISOMORPHISM_MONOMORPHISM_ALT,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL, RING_MUL_IN_SUBFIELD_GENERATED,
        RING_MUL_IN_SUBRING_GENERATED, RING_MUL_LID, RING_MUL_LZERO, RING_MUL_RID,
        RING_MUL_RZERO, RING_NEG, RING_NEG_IN_SUBFIELD_GENERATED, RING_OF_INT,
        RING_OF_INTEGERS, RING_OF_INTEGERS_CARRIER, RING_OF_INTEGERS_PRIME_SUBFIELD,
        RING_OF_INTEGERS_SUBRING, RING_OF_INTEGERS_SUBSET, RING_OF_INT_0,
        RING_OF_INT_ADD, RING_OF_INT_EQ_0_CHAR_0, RING_OF_INT_IN_RING_OF_INTEGERS,
        RING_OF_INT_IN_SUBFIELD_GENERATED, RING_OF_INT_MUL, RING_OF_INT_NEG,
        RING_OF_INT_OF_NUM, RING_OF_INT_POW, RING_OF_INT_SUBFIELD_GENERATED,
        RING_OF_NUM, RING_OF_NUM_EQ_0, RING_OF_NUM_SUBFIELD_GENERATED,
        RING_POLYNOMIAL_CONST, RING_POLYNOMIAL_POW, RING_POLYNOMIAL_VAR, RING_POW,
        RING_POW_2, RING_POW_IN_SUBFIELD_GENERATED, RING_POW_SUBFIELD_GENERATED,
        RING_PRODUCT_LT_2, RING_SUB_EQ_0, RING_SUB_REFL, RING_SUB_RZERO, RING_SUM_LT_2,
        SIMPLE_ALGEBRAIC_EXTEND_HOMOMORPHISM_ROOT, SUBFIELD_GENERATED,
        SUBRING_GENERATED_INC_GEN, SUBRING_GENERATED_SUPERSET, SUBSET,
        basis_discriminant, field_extension, int_congruent, int_divides,
        isomorphic_ring, monic, mul_matrix, number_field, ring_monomorphism, ring_sub,
        squarefree, .. } := D.core2
  let { FIELD_EXTENSION_SQRT, FREE_BASIS_SUBFIELD_GENERATED_2,
        INTEGRAL_ELEMENT_QUADRATIC, INT_SQUARE_SUB_MUL_SQUARE_MOD_4,
        PRIME_SUBFIELD_SQUAREFREE_MUL_SQUARE, QUADRATIC_FIELD_COORDINATES,
        QUADRATIC_FIELD_FREE_BASIS, SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD,
        SUBFIELD_GENERATED_ADD_MUL_EQ_0, SUBFIELD_GENERATED_HALF_SUCC, .. } := BQuadratic01
  -- @@SCOPE END

  let QUADRATIC_FIELD_EXISTS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!d. squarefree(num_of_int(abs d)) /\ ~(d = &1)
         ==> ?k:(((1->num)->real)->bool) ring x.
                 number_field k /\
                 extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
                 x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d"
      (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"q = subfield_generated real_ring {ring_0 real_ring}") THEN SUBGOAL_THEN (← q r"field(q:real ring) /\ ring_char q = 0") STRIP_ASSUME_TAC THENL [EXPAND_TAC "q" THEN SIMP_TAC [FIELD_SUBFIELD_GENERATED, FIELD_REAL_RING, RING_CHAR_SUBFIELD_GENERATED, REAL_RING_CHAR], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"q:real ring"), (← q r"ring_of_int q d:real")] FIELD_EXTENSION_SQRT) THEN ASM_REWRITE_TAC [RING_OF_INT] THEN ANTS_TAC THENL [REWRITE_TAC [NOT_EXISTS_THM] THEN X_GEN_TAC (← q r"y:real") THEN EXPAND_TAC "q" THEN REWRITE_TAC [RING_POW_SUBFIELD_GENERATED, RING_OF_INT_SUBFIELD_GENERATED] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"real_ring"), (← q r"y:real"), (← q r"d:int")] SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD) THEN ASM_REWRITE_TAC [FIELD_REAL_RING, REAL_RING_CHAR], REWRITE_TAC [LEFT_IMP_EXISTS_THM]] THEN MAP_EVERY X_GEN_TAC [(← q r"l:(((1->num)->real)->bool) ring"), (← q r"h:real->((1->num)->real)->bool"), (← q r"z:((1->num)->real)->bool")] THEN REWRITE_TAC [field_extension] THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"l:(((1->num)->real)->bool) ring"), (← q r"z:((1->num)->real)->bool")] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN RULE_ASSUM_TAC (REWRITE_RULE [(← MATCH_MP RING_HOMOMORPHISM_RING_OF_INT (← ASSUME (← q r"ring_homomorphism(q,l) (h:real->((1->num)->real)->bool)")))]) THEN SUBGOAL_THEN (← q r"ring_char(l:(((1->num)->real)->bool) ring) = 0") ASSUME_TAC THENL [FIRST_ASSUM (SUBST1_TAC o (SYM o (MATCH_MP RING_CHAR_MONOMORPHIC_IMAGE))) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"IMAGE (h:real->((1->num)->real)->bool) (ring_carrier q) =
      ring_carrier(subfield_generated l {ring_0 l})") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"q:real ring"), (← q r"l:(((1->num)->real)->bool) ring"), (← q r"h:real->((1->num)->real)->bool")] PRIME_SUBFIELD_MONOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN EXPAND_TAC "q" THEN REWRITE_TAC [PRIME_SUBFIELD_SUBFIELD_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(z IN ring_carrier(subfield_generated l
                           {ring_0 l:((1->num)->real)->bool}))") ASSUME_TAC THENL [MATCH_MP_TAC SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD THEN EXISTS_TAC (← q r"d:int") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"free_basis (subfield_generated l {ring_0 l},l) I 2
        (\i. if i = 0 then ring_1 l else z:((1->num)->real)->bool)") ASSUME_TAC THENL [MATCH_MP_TAC FREE_BASIS_SUBFIELD_GENERATED_2 THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"y:((1->num)->real)->bool") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (← do let c := (← ASSUME (← q r"(y:((1->num)->real)->bool) IN ring_carrier l")); pure (fun th => MATCH_MP th c))) THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:real"), (← q r"b:real")] THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"(h:real->((1->num)->real)->bool) a"), (← q r"(h:real->((1->num)->real)->bool) b")] THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z5 ← (q r"IMAGE (h:real->((1->num)->real)->bool) (ring_carrier q)"); let z4 ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); liftExcept (lhs z2)); pure (z4 == z5)))))) THEN ASM_SIMP_TAC [FUN_IN_IMAGE], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [ASM_REWRITE_TAC [NUMBER_FIELD_ALT] THEN MAP_EVERY EXISTS_TAC [(← q r"2"), (← q r"\i. if i = 0 then ring_1 l else z:((1->num)->real)->bool")] THEN ASM_REWRITE_TAC [], DISCH_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC NUMBER_FIELD_FREE_BASIS_DEGREE THEN EXISTS_TAC (← q r"\i. if i = 0 then ring_1 l else z:((1->num)->real)->bool") THEN ASM_REWRITE_TAC []])

  let QUADRATIC_EXTEND_HOMOMORPHISM ← prove
    r"!k:A ring l:B ring s h x y.
        field k /\ ring_homomorphism(subfield_generated k s,l) h /\
        x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k s)) /\
        ring_pow k x 2 IN ring_carrier(subfield_generated k s) /\
        (!z. z IN ring_carrier k
             ==> ?a b. a IN ring_carrier(subfield_generated k s) /\
                       b IN ring_carrier(subfield_generated k s) /\
                       z = ring_add k a (ring_mul k b x)) /\
        y IN ring_carrier l /\ ring_pow l y 2 = h(ring_pow k x 2)
        ==> ?g. ring_homomorphism(k,l) g /\ g x = y /\
                !a. a IN ring_carrier(subfield_generated k s) ==> g a = h a"
    (REPEAT GEN_TAC THEN ABBREV_TAC (← q r"K = subfield_generated k (s:A->bool)") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"field(K:A ring) /\ field_extension(K,k) (I:A->A) /\
    (!a:A. a IN ring_carrier K
           ==> a IN ring_carrier k /\ ring_neg k a IN ring_carrier K /\
               ring_pow K a 2 = ring_pow k a 2) /\
    (h:A->B)(ring_pow k x 2) IN ring_carrier l") STRIP_ASSUME_TAC THENL [EXPAND_TAC "K" THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, FIELD_EXTENSION_SUBFIELD_GENERATED, RING_NEG_IN_SUBFIELD_GENERATED, RING_POW_SUBFIELD_GENERATED] THEN ASM_MESON_TAC [RING_POW, RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"algebraic_over (K,k) (I:A->A) x") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"K:A ring"), (← q r"k:A ring"), (← q r"x:A"), (← q r"2")] ALGEBRAIC_OVER_POW_EQ) THEN ASM_REWRITE_TAC [ARITH_EQ] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_MESON_TAC [ALGEBRAIC_OVER_IMAGE, I_THM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"K:A ring"), (← q r"2"), (← q r"ring_pow k x 2:A")] POLY_VAR_POW_SUB_CONST) THEN ASM_SIMP_TAC [FIELD_NONTRIVIAL, ARITH_EQ] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"K:A ring"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"I:A->A"), (← q r"h:A->B"), (← q r"x:A"), (← q r"y:B")] SIMPLE_ALGEBRAIC_EXTEND_HOMOMORPHISM_ROOT) THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"minimal_polynomial (K,k) (I:A->A) x =
    poly_sub K (poly_pow K (poly_var K one) 2)
               (poly_const K (ring_pow k x 2))") SUBST1_TAC THENL [MATCH_MP_TAC MINIMAL_POLYNOMIAL_UNIQUE THEN ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL [ASM_REWRITE_TAC [monic, COEFF_POLY_SUB, COEFF_POLY_VARPOW, COEFF_POLY_CONST, ARITH_EQ] THEN SIMP_TAC [RING_SUB_RZERO, RING_1], MATCH_MP_TAC POLY_DEG_2_IRREDUCIBLE THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"K:A ring"), (← q r"K:A ring"), (← q r"2"), (← q r"ring_pow k x 2:A"), (← q r"a:A")] POLY_EVAL_VAR_POW_SUB_CONST) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_I, I_O_ID, I_THM] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [RING_SUB_EQ_0, RING_POW] THEN GEN_REWRITE_TAC RAND_CONV [EQ_SYM_EQ] THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_SQUARE_EQ, FIELD_IMP_INTEGRAL_DOMAIN] THEN ASM_MESON_TAC [], ASM_SIMP_TAC [POLY_EXTEND_SUB, POLY_EXTEND_VARPOW, POLY_EXTEND_CONST, RING_POLYNOMIAL_POW, RING_POLYNOMIAL_VAR, I_THM, RING_POLYNOMIAL_CONST, FIELD_EXTENSION_IMP_HOMOMORPHISM, RING_SUB_REFL, RING_POW]], ALL_TAC] THEN ASM_SIMP_TAC [POLY_EVAL_VAR_POW_SUB_CONST, RING_SUB_REFL, I_THM, IMAGE_I] THEN SUBGOAL_THEN (← q r"subring_generated k ((x:A) INSERT ring_carrier K) = k") SUBST1_TAC THENL [ALL_TAC, MESON_TAC []] THEN REWRITE_TAC [SUBRING_GENERATED_SUPERSET, SUBSET] THEN X_GEN_TAC (← q r"z:A") THEN DISCH_THEN (fun th => tactic_of do pure (FIRST_X_ASSUM (MP_TAC o (← do let c := th; pure (fun th => MATCH_MP th c))))) THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC RING_ADD_IN_SUBRING_GENERATED THEN CONJ_TAC THEN TRY (MATCH_MP_TAC RING_MUL_IN_SUBRING_GENERATED THEN CONJ_TAC) THEN MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN ASM_SIMP_TAC [IN_INSERT])

  let QUADRATIC_FIELD_UNIQUE_EXPLICIT ← prove
    r"!k:A ring l:B ring x y d.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        number_field l /\
        extension_degree (subfield_generated l {ring_0 l},l) I = 2 /\
        x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
        ring_pow k x 2 = ring_of_int k d /\
        y IN ring_carrier l /\ ring_pow l y 2 = ring_of_int l d
        ==> ?h. ring_isomorphism(k,l) h /\ h x = y"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"field(k:A ring) /\ field(l:B ring) /\
                ring_char k = 0 /\ ring_char l = 0") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [NUMBER_FIELD_IMP_FIELD, number_field], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring")] PRIME_SUBFIELD_HOMOMORPHISM_EXISTS) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"h0:A->B") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"{ring_0 k:A}"), (← q r"h0:A->B"), (← q r"x:A"), (← q r"y:B")] QUADRATIC_EXTEND_HOMOMORPHISM) THEN ASM_REWRITE_TAC [RING_OF_INT_IN_SUBFIELD_GENERATED] THEN ANTS_TAC THENL [ASM_SIMP_TAC [QUADRATIC_FIELD_COORDINATES] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP RING_HOMOMORPHISM_RING_OF_INT)) THEN REWRITE_TAC [RING_OF_INT_SUBFIELD_GENERATED] THEN SIMP_TAC [], MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"h:A->B") THEN STRIP_TAC THEN ASM_REWRITE_TAC []] THEN SUBGOAL_THEN (← q r"ring_monomorphism(k:A ring,l:B ring) h") ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_RING_HOMOMORPHISM_MONOMORPHISM, FIELD_IMP_NONTRIVIAL_RING], ASM_REWRITE_TAC [RING_ISOMORPHISM_MONOMORPHISM_ALT]] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] PRIME_SUBFIELD_MONOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{ring_0 k:A}")] RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN FIRST_ASSUM (MP_TAC o (CONJUNCT2 o (GEN_REWRITE_RULE id [ring_monomorphism]))) THEN DISCH_TAC THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"~((y:B) IN ring_carrier(subfield_generated l {ring_0 l}))") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN REWRITE_TAC [SUBSET, IN_IMAGE] THEN X_GEN_TAC (← q r"w:B") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"y:B"), (← q r"w:B")] QUADRATIC_FIELD_COORDINATES) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:B"), (← q r"b:B")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"?a' b'. a' IN ring_carrier(subfield_generated k {ring_0 k}) /\
            b' IN ring_carrier(subfield_generated k {ring_0 k}) /\
            (h:A->B) a' = a /\ h b' = b") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN EXISTS_TAC (← q r"ring_add k a' (ring_mul k b' x):A") THEN SUBGOAL_THEN (← q r"(a':A) IN ring_carrier k /\ (b':A) IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [RING_ADD, RING_MUL, (← MATCH_MP RING_HOMOMORPHISM_ADD th), (← MATCH_MP RING_HOMOMORPHISM_MUL th)])))

  let QUADRATIC_FIELD_UNIQUE ← prove
    r"!k:A ring l:B ring d.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        number_field l /\
        extension_degree (subfield_generated l {ring_0 l},l) I = 2 /\
        squarefree(num_of_int(abs d)) /\ ~(d = &1) /\
        (?x. x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d) /\
        (?y. y IN ring_carrier l /\ ring_pow l y 2 = ring_of_int l d)
        ==> k isomorphic_ring l"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [isomorphic_ring] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"x:A"), (← q r"y:B"), (← q r"d:int")] QUADRATIC_FIELD_UNIQUE_EXPLICIT) THEN ANTS_TAC THENL [ALL_TAC, MESON_TAC []] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD THEN EXISTS_TAC (← q r"d:int") THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [NUMBER_FIELD_IMP_FIELD, number_field])

  let QUADRATIC_FIELD_TRACE ← prove
    r"!k:A ring x a b.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
        ring_pow k x 2 IN ring_carrier(subfield_generated k {ring_0 k}) /\
        a IN ring_carrier(subfield_generated k {ring_0 k}) /\
        b IN ring_carrier(subfield_generated k {ring_0 k})
        ==> algebra_trace (subfield_generated k {ring_0 k},k) I
              (ring_add k a (ring_mul k b x)) =
            ring_mul k (ring_of_num k 2) a"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{ring_0 k:A}")] RING_HOMOMORPHISM_SUBFIELD_INCLUSION) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{ring_0 k:A}")] RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A")] QUADRATIC_FIELD_FREE_BASIS) THEN ASM_REWRITE_TAC [SUBSET] THEN ABBREV_TAC (← q r"q = subfield_generated (k:A ring) {ring_0 k}") THEN ABBREV_TAC (← q r"g = \i. if i = 0 then ring_1 k else x:A") THEN REPEAT DISCH_TAC THEN SUBGOAL_THEN (← q r"(g:num->A) 0 = ring_1 k /\ g 1 = x") STRIP_ASSUME_TAC THENL [EXPAND_TAC "g" THEN REWRITE_TAC [ARITH_EQ], ALL_TAC] THEN SUBGOAL_THEN (← q r"algebra_trace (q,k) (I:A->A) x = ring_0 k") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"q:A ring"), (← q r"k:A ring"), (← q r"2"), (← q r"g:num->A"), (← q r"x:A")] ALGEBRA_TRACE_FREE_BASIS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [mul_matrix] THEN SUBGOAL_THEN (← q r"basis_coordinates (q,k) (I:A->A) 2 g (ring_mul k x (g 0)) 0 = ring_0 k /\
      basis_coordinates (q,k) (I:A->A) 2 g (ring_mul k x (g 1)) 1 = ring_0 k") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [SUBGOAL_THEN (← q r"ring_mul k x ((g:num->A) 0) = g 1") SUBST1_TAC THENL [ASM_SIMP_TAC [RING_MUL_RID], ALL_TAC] THEN ASM_SIMP_TAC [BASIS_COORDINATES_BASIS, ARITH] THEN EXPAND_TAC "q" THEN REWRITE_TAC [SUBFIELD_GENERATED], SUBGOAL_THEN (← q r"ring_mul k x ((g:num->A) 1) = ring_mul k (I(ring_pow k x 2)) (g 0)") SUBST1_TAC THENL [ASM_SIMP_TAC [RING_MUL_RID, I_THM, RING_POW_2, RING_POW, RING_MUL], ALL_TAC] THEN ASM_SIMP_TAC [BASIS_COORDINATES_LMUL, BASIS_COORDINATES_BASIS, ARITH, RING_1] THEN EXPAND_TAC "q" THEN ASM_SIMP_TAC [SUBFIELD_GENERATED, RING_MUL_RZERO, RING_POW]], wPart lhand (lhand o rand) RING_SUM_LT_2 THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "q" THEN REWRITE_TAC [RING_0_IN_SUBFIELD_GENERATED, SUBFIELD_GENERATED] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [RING_ADD_LZERO, RING_0]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"q:A ring"), (← q r"k:A ring"), (← q r"b:A"), (← q r"x:A")] ALGEBRA_TRACE_SCALAR) THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"q:A ring"), (← q r"k:A ring"), (← q r"a:A"), (← q r"ring_mul k b x:A")] ALGEBRA_TRACE_ADD) THEN ASM_SIMP_TAC [I_THM, RING_MUL] THEN REPEAT (DISCH_THEN SUBST1_TAC) THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"q:A ring"), (← q r"k:A ring"), (← q r"2"), (← q r"g:num->A"), (← q r"a:A")] ALGEBRA_TRACE_NORM_BASE_FREE_BASIS) THEN ASM_SIMP_TAC [I_THM] THEN DISCH_THEN (SUBST1_TAC o CONJUNCT1) THEN EXPAND_TAC "q" THEN REWRITE_TAC [SUBFIELD_GENERATED, RING_OF_NUM_SUBFIELD_GENERATED] THEN ASM_SIMP_TAC [RING_MUL_RZERO, RING_ADD_RZERO, RING_MUL, RING_OF_NUM])

  let QUADRATIC_FIELD_INTEGRAL_COORDINATES ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!k:A ring x a b A' B'.
           ring_mul k (ring_of_num k 2) a = A' /\
           ring_mul k (ring_of_num k 2) b = B'
           ==> ring_mul k (ring_of_num k 2) (ring_add k a (ring_mul k b x)) =
               ring_add k A' (ring_mul k B' x)")
    let r2 ← RING_RULE (← q r"!k:A ring a b D A' U'.
           ring_mul k (ring_of_num k 2) a = A' /\
           ring_sub k (ring_mul k (ring_pow k b 2) D) (ring_pow k a 2) = U'
           ==> ring_mul k D (ring_pow k (ring_mul k (ring_of_num k 2) b) 2) =
               ring_add k (ring_mul k (ring_of_num k 4) U')
                          (ring_pow k A' 2)")
    let r3 ← RING_RULE (← q r"!k:A ring x a b D c.
             ring_pow k x 2 = D /\ ring_mul k (ring_of_num k 2) a = c
             ==> ring_sub k (ring_mul k (ring_pow k b 2) D) (ring_pow k a 2) =
                 ring_sub k (ring_pow k (ring_add k a (ring_mul k b x)) 2)
                   (ring_mul k c (ring_add k a (ring_mul k b x)))")
    prove
      r"!k:A ring x d z.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
          x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
          squarefree(num_of_int(abs d)) /\ ~(d = &1) /\
          z IN ring_carrier(ring_of_integers k)
          ==> ?A B N. ring_mul k (ring_of_num k 2) z =
                      ring_add k (ring_of_int k A)
                                 (ring_mul k (ring_of_int k B) x) /\
                      A pow 2 - d * B pow 2 = &4 * N"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (fun th => tactic_of do pure (ASSUME_TAC (← MATCH_MP NUMBER_FIELD_IMP_FIELD th) THEN STRIP_ASSUME_TAC (← REWRITE_RULE [number_field] th))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"d:int")] SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"z:A")] QUADRATIC_FIELD_COORDINATES) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_SUBSET) THEN ASM SET_TAC [], REWRITE_TAC [LEFT_IMP_EXISTS_THM]] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{ring_0 k:A}")] RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN REWRITE_TAC [SUBSET] THEN DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"a:A") th) THEN MP_TAC (← SPEC (← q r"b:A") th))) THEN ASM_REWRITE_TAC [] THEN REPEAT DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_add k a (ring_mul k b x):A")] NUMBER_FIELD_TRACE_INTEGRAL_Q) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"a:A"), (← q r"b:A")] QUADRATIC_FIELD_TRACE) THEN ASM_REWRITE_TAC [RING_OF_INT_IN_SUBFIELD_GENERATED] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN (X_CHOOSE_TAC (← q r"A:int")) THEN SUBGOAL_THEN (← q r"?U. ring_sub k (ring_mul k (ring_pow k b 2) (ring_of_int k d))
                     (ring_pow k a 2) = ring_of_int k U:A") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_PRIME_SUBFIELD) THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [EXTENSION, IN_INTER, IN_ELIM_THM, IN_UNIV] THEN DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM th)])) THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"a:A"), (← q r"b:A"), (← q r"ring_of_int k d:A"), (← q r"ring_of_int k A:A")] r3) THEN ASM_SIMP_TAC [RING_OF_INT] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← CONJUNCT1 RING_OF_INTEGERS_SUBRING) THEN DISCH_THEN (ASSUME_TAC o (SPEC (← q r"k:A ring"))) THEN ASM_SIMP_TAC [IN_SUBRING_SUB, IN_SUBRING_MUL, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS], REWRITE_TAC [ring_sub] THEN REPEAT (FIRST [MATCH_MP_TAC RING_ADD_IN_SUBFIELD_GENERATED, MATCH_MP_TAC RING_NEG_IN_SUBFIELD_GENERATED, MATCH_MP_TAC RING_MUL_IN_SUBFIELD_GENERATED, MATCH_MP_TAC RING_POW_IN_SUBFIELD_GENERATED, CONJ_TAC]) THEN ASM_REWRITE_TAC [RING_OF_INT_IN_SUBFIELD_GENERATED]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_mul k (ring_of_num k 2) b:A"), (← q r"d:int"), (← q r"(&4 * U + A pow 2):int")] PRIME_SUBFIELD_SQUAREFREE_MUL_SQUARE) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_MUL_IN_SUBFIELD_GENERATED, (← GSYM RING_OF_INT_OF_NUM), RING_OF_INT_IN_SUBFIELD_GENERATED] THEN REWRITE_TAC [RING_OF_INT_ADD, RING_OF_INT_MUL, RING_OF_INT_POW, RING_OF_INT_OF_NUM] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"b:A"), (← q r"ring_of_int k d:A"), (← q r"ring_of_int k A:A"), (← q r"ring_of_int k U:A")] r2) THEN ASM_SIMP_TAC [RING_OF_INT], DISCH_THEN (X_CHOOSE_THEN (← q r"B:int") STRIP_ASSUME_TAC)] THEN MAP_EVERY EXISTS_TAC [(← q r"A:int"), (← q r"B:int"), (← q r"--U:int")] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"a:A"), (← q r"b:A"), (← q r"ring_of_int k A:A"), (← q r"ring_of_int k B:A")] r1) THEN ASM_SIMP_TAC [RING_OF_INT], UNDISCH_TAC (← q r"&4 * U + A pow 2 = (d:int) * B pow 2") THEN INT_ARITH_TAC])

  let QUADRATIC_FIELD_INTEGRAL_FREE_BASIS ← prove
    r"!k:A ring w.
        number_field k /\
        w IN ring_carrier(ring_of_integers k) /\
        ~(w IN ring_carrier(subfield_generated k {ring_0 k})) /\
        (!z. z IN ring_carrier(ring_of_integers k)
             ==> ?a b. z = ring_add k (ring_of_int k a)
                                      (ring_mul k (ring_of_int k b) w))
        ==> free_basis (integer_ring,ring_of_integers k) (ring_of_int k) 2
                       (\i. if i = 0 then ring_1 k else w)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (fun th => tactic_of do pure (ASSUME_TAC (← MATCH_MP NUMBER_FIELD_IMP_FIELD th) THEN STRIP_ASSUME_TAC (← REWRITE_RULE [number_field] th))) THEN SUBGOAL_THEN (← q r"(w:A) IN ring_carrier k /\
                ring_1 k IN ring_carrier(ring_of_integers k)") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_1) THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_SUBSET) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS, SUBSET] THEN ASM_MESON_TAC [], ALL_TAC] THEN ONCE_REWRITE_TAC [(← GSYM (← CONJUNCT2 RING_OF_INTEGERS_SUBRING))] THEN SIMP_TAC [FREE_BASIS_INTEGER_RING_SUBRING_GENERATED, RING_OF_INTEGERS_SUBRING] THEN ASM_REWRITE_TAC [FORALL_LT_2, ARITH_EQ] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"z:A") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (← do let c := (← ASSUME (← q r"(z:A) IN ring_carrier(ring_of_integers k)")); pure (fun th => MATCH_MP th c))) THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:int"), (← q r"b:int")] THEN DISCH_THEN SUBST1_TAC THEN EXISTS_TAC (← q r"\i. if i = 0 then a else b:int") THEN ASM_SIMP_TAC [RING_SUM_LT_2, RING_MUL, RING_OF_INT, RING_1, ARITH_EQ, RING_MUL_RID], X_GEN_TAC (← q r"c:num->int") THEN ASM_SIMP_TAC [RING_SUM_LT_2, RING_MUL, RING_OF_INT, RING_1, ARITH_EQ, RING_MUL_RID] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{ring_0 k:A}"), (← q r"ring_of_int k (c 0):A"), (← q r"ring_of_int k (c 1):A"), (← q r"w:A")] SUBFIELD_GENERATED_ADD_MUL_EQ_0) THEN ASM_SIMP_TAC [RING_OF_INT_IN_SUBFIELD_GENERATED, RING_OF_INT_EQ_0_CHAR_0]])

  let QUADRATIC_FIELD_INTEGRAL_BASIS_SQRT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!k:A ring z x a b.
           ring_mul k (ring_of_num k 2) z =
           ring_add k (ring_mul k (ring_of_num k 2) a)
                      (ring_mul k (ring_mul k (ring_of_num k 2) b) x)
           ==> ring_mul k (ring_of_num k 2) z =
               ring_mul k (ring_of_num k 2)
                 (ring_add k a (ring_mul k b x))")
    prove
      r"!k:A ring x d.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
          x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
          squarefree(num_of_int(abs d)) /\ ~(d = &1) /\ ~((d == &1) (mod &4))
          ==> free_basis (integer_ring,ring_of_integers k) (ring_of_int k) 2
                (\i. if i = 0 then ring_1 k else x)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (fun th => tactic_of do pure (ASSUME_TAC (← MATCH_MP NUMBER_FIELD_IMP_FIELD th) THEN STRIP_ASSUME_TAC (← REWRITE_RULE [number_field] th))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"d:int")] SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"~(ring_of_num k 2:A = ring_0 k) /\ ~(&4 divides (d:int))") STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC [RING_OF_NUM_EQ_0, DIVIDES_ZERO, ARITH_EQ] THEN UNDISCH_TAC (← q r"squarefree(num_of_int(abs d))") THEN REWRITE_TAC [squarefree, INT_DIVIDES_NUM_OF_INT_ABS, INT_ABS_NUM, NUM_OF_INT_OF_NUM] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"2"))) THEN CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC [], ALL_TAC] THEN MATCH_MP_TAC QUADRATIC_FIELD_INTEGRAL_FREE_BASIS THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM] THEN MATCH_MP_TAC INTEGRAL_ELEMENT_QUADRATIC THEN MAP_EVERY EXISTS_TAC [(← q r"&0:int"), (← q r"--d:int")] THEN ASM_SIMP_TAC [RING_OF_INT_0, RING_OF_INT_NEG, RING_MUL_LZERO, RING_ADD_LZERO, RING_NEG, RING_OF_INT, RING_ADD_RNEG], X_GEN_TAC (← q r"z:A") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"d:int"), (← q r"z:A")] QUADRATIC_FIELD_INTEGRAL_COORDINATES) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"A:int"), (← q r"B:int"), (← q r"N:int")] THEN STRIP_TAC THEN MP_TAC (← SPECL [(← q r"d:int"), (← q r"A:int"), (← q r"B:int"), (← q r"N:int")] INT_SQUARE_SUB_MUL_SQUARE_MOD_4) THEN ASM_REWRITE_TAC [int_divides] THEN DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"a:int") SUBST_ALL_TAC) (X_CHOOSE_THEN (← q r"b:int") SUBST_ALL_TAC)) THEN MAP_EVERY EXISTS_TAC [(← q r"a:int"), (← q r"b:int")] THEN SUBGOAL_THEN (← q r"(z:A) IN ring_carrier k") ASSUME_TAC THENL [MATCH_MP_TAC (← REWRITE_RULE [SUBSET] (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_SUBSET)) THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN MAP_EVERY EXISTS_TAC [(← q r"k:A ring"), (← q r"ring_of_num k 2:A")] THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, RING_OF_NUM, RING_ADD, RING_MUL, RING_OF_INT] THEN UNDISCH_TAC (← q r"ring_mul k (ring_of_num k 2) z =
        ring_add k (ring_of_int k (&2 * a))
                   (ring_mul k (ring_of_int k (&2 * b)) x):A") THEN REWRITE_TAC [RING_OF_INT_MUL, RING_OF_INT_OF_NUM] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"x:A"), (← q r"ring_of_int k a:A"), (← q r"ring_of_int k b:A")] r1) THEN ASM_SIMP_TAC [RING_OF_INT]])

  let QUADRATIC_FIELD_INTEGRAL_BASIS_HALF ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!k:A ring z w x C B.
           ring_mul k (ring_of_num k 2) w = ring_add k (ring_1 k) x
           ==> ring_mul k (ring_of_num k 2) z =
               ring_add k (ring_add k (ring_mul k (ring_of_num k 2) C) B)
                          (ring_mul k B x)
           ==> ring_mul k (ring_of_num k 2) z =
               ring_mul k (ring_of_num k 2)
                 (ring_add k C (ring_mul k B w))")
    let r2 ← INT_ARITH (← q r"A - B = &2 * c ==> A = &2 * c + B:int")
    let r3 ← RING_RULE (← q r"!k:A ring w x T.
           ring_mul k (ring_of_num k 2) w = ring_add k (ring_1 k) x
           ==> ring_pow k x 2 =
               ring_add k (ring_of_num k 1) (ring_mul k (ring_of_num k 4) T)
           ==> ring_mul k (ring_of_num k 4)
                (ring_add k (ring_pow k w 2)
                   (ring_add k (ring_mul k (ring_neg k (ring_of_num k 1)) w)
                               (ring_neg k T))) =
               ring_mul k (ring_of_num k 4) (ring_0 k)")
    let r4 ← INT_ARITH (← q r"(d:int) - &1 = &4 * t ==> d = &1 + &4 * t")
    prove
      r"!k:A ring x d.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
          x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
          squarefree(num_of_int(abs d)) /\ ~(d = &1) /\ (d == &1) (mod &4)
          ==> free_basis (integer_ring,ring_of_integers k) (ring_of_int k) 2
                (\i. if i = 0 then ring_1 k
                     else ring_div k (ring_add k (ring_1 k) x)
                                     (ring_of_num k 2))"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (fun th => tactic_of do pure (ASSUME_TAC (← MATCH_MP NUMBER_FIELD_IMP_FIELD th) THEN STRIP_ASSUME_TAC (← REWRITE_RULE [number_field] th))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"d:int")] SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"~(ring_of_num k 2:A = ring_0 k) /\ ~(&4 divides (d:int))") STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC [RING_OF_NUM_EQ_0, DIVIDES_ZERO, ARITH_EQ] THEN UNDISCH_TAC (← q r"squarefree(num_of_int(abs d))") THEN REWRITE_TAC [squarefree, INT_DIVIDES_NUM_OF_INT_ABS, INT_ABS_NUM, NUM_OF_INT_OF_NUM] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"2"))) THEN CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC [], ALL_TAC] THEN MATCH_MP_TAC QUADRATIC_FIELD_INTEGRAL_FREE_BASIS THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{ring_0 k:A}"), (← q r"x:A")] SUBFIELD_GENERATED_HALF_SUCC) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"w = ring_div k (ring_add k (ring_1 k) x) (ring_of_num k 2):A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [UNDISCH_TAC (← q r"((d:int) == &1) (mod &4)") THEN REWRITE_TAC [int_congruent] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"t:int") (SUBST_ALL_TAC o (MATCH_MP r4))) THEN REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM] THEN MATCH_MP_TAC INTEGRAL_ELEMENT_QUADRATIC THEN MAP_EVERY EXISTS_TAC [(← q r"--(&1):int"), (← q r"--t:int")] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN MAP_EVERY EXISTS_TAC [(← q r"k:A ring"), (← q r"ring_of_num k 4:A")] THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, RING_OF_NUM, RING_OF_NUM_EQ_0, DIVIDES_ZERO, ARITH_EQ, RING_0, RING_ADD, RING_POW, RING_MUL, RING_OF_INT] THEN UNDISCH_TAC (← q r"ring_pow k x 2 = ring_of_int k (&1 + &4 * t):A") THEN REWRITE_TAC [RING_OF_INT_NEG, RING_OF_INT_ADD, RING_OF_INT_MUL, RING_OF_INT_OF_NUM] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"w:A"), (← q r"x:A"), (← q r"ring_of_int k t:A")] r3) THEN ASM_SIMP_TAC [RING_OF_INT], X_GEN_TAC (← q r"z:A") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"d:int"), (← q r"z:A")] QUADRATIC_FIELD_INTEGRAL_COORDINATES) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"A:int"), (← q r"B:int"), (← q r"N:int")] THEN STRIP_TAC THEN MP_TAC (← SPECL [(← q r"d:int"), (← q r"A:int"), (← q r"B:int"), (← q r"N:int")] INT_SQUARE_SUB_MUL_SQUARE_MOD_4) THEN ASM_REWRITE_TAC [int_divides] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:int") (SUBST_ALL_TAC o (MATCH_MP r2))) THEN MAP_EVERY EXISTS_TAC [(← q r"c:int"), (← q r"B:int")] THEN SUBGOAL_THEN (← q r"(z:A) IN ring_carrier k") ASSUME_TAC THENL [MATCH_MP_TAC (← REWRITE_RULE [SUBSET] (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_SUBSET)) THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN MAP_EVERY EXISTS_TAC [(← q r"k:A ring"), (← q r"ring_of_num k 2:A")] THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, RING_OF_NUM, RING_ADD, RING_MUL, RING_OF_INT] THEN UNDISCH_TAC (← q r"ring_mul k (ring_of_num k 2) z =
        ring_add k (ring_of_int k (&2 * c + B))
                   (ring_mul k (ring_of_int k B) x):A") THEN REWRITE_TAC [RING_OF_INT_ADD, RING_OF_INT_MUL, RING_OF_INT_OF_NUM] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"w:A"), (← q r"x:A"), (← q r"ring_of_int k c:A"), (← q r"ring_of_int k B:A")] r1) THEN ASM_SIMP_TAC [RING_OF_INT]])

  let QUADRATIC_FIELD_INTEGRAL_BASIS ← prove
    r"!k:A ring x d.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
        squarefree(num_of_int(abs d)) /\ ~(d = &1)
        ==> free_basis (integer_ring,ring_of_integers k) (ring_of_int k) 2
              (\i. if i = 0 then ring_1 k
                   else if (d == &1) (mod &4)
                        then ring_div k (ring_add k (ring_1 k) x)
                                        (ring_of_num k 2)
                        else x)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN COND_CASES_TAC THEN FIRST [MATCH_MP_TAC QUADRATIC_FIELD_INTEGRAL_BASIS_HALF, MATCH_MP_TAC QUADRATIC_FIELD_INTEGRAL_BASIS_SQRT] THEN EXISTS_TAC (← q r"d:int") THEN ASM_REWRITE_TAC [])

  let QUADRATIC_FIELD_BASIS_DISCRIMINANT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul (k:A ring) (ring_of_num k 2) (ring_mul k (ring_of_num k 2) D) =
    ring_mul k (ring_of_num k 4) D")
    prove
      r"!k:A ring x d.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
          x IN ring_carrier k /\
          ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
          ring_pow k x 2 = ring_of_int k d
          ==> basis_discriminant (subfield_generated k {ring_0 k},k) I 2
                (\i. if i = 0 then ring_1 k else x) =
              ring_of_int k (&4 * d)"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"!a b. a IN ring_carrier(subfield_generated k {ring_0 k}) /\
            b IN ring_carrier(subfield_generated k {ring_0 k})
            ==> algebra_trace (subfield_generated k {ring_0 k},k) (I:A->A)
                  (ring_add k a (ring_mul k b x)) =
                ring_mul k (ring_of_num k 2) a") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{ring_0 k:A}")] RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN REWRITE_TAC [SUBSET] THEN DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"a:A") th) THEN MP_TAC (← SPEC (← q r"b:A") th))) THEN ASM_REWRITE_TAC [] THEN REPEAT DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"a:A"), (← q r"b:A")] QUADRATIC_FIELD_TRACE) THEN ASM_SIMP_TAC [RING_OF_INT_IN_SUBFIELD_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"algebra_trace (subfield_generated k {ring_0 k},k)
        (I:A->A) (ring_1 k) = ring_of_num k 2 /\
      algebra_trace (subfield_generated k {ring_0 k},k) (I:A->A) x = ring_0 k /\
      algebra_trace (subfield_generated k {ring_0 k},k)
        (I:A->A) (ring_of_int k d) =
      ring_mul k (ring_of_num k 2) (ring_of_int k d)") STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THENL [FIRST_X_ASSUM (MP_TAC o (SPECL [(← q r"ring_1 k:A"), (← q r"ring_0 k:A")])), FIRST_X_ASSUM (MP_TAC o (SPECL [(← q r"ring_0 k:A"), (← q r"ring_1 k:A")])), FIRST_X_ASSUM (MP_TAC o (SPECL [(← q r"ring_of_int k d:A"), (← q r"ring_0 k:A")]))] THEN ASM_SIMP_TAC [RING_0_IN_SUBFIELD_GENERATED, RING_1_IN_SUBFIELD_GENERATED, RING_OF_INT_IN_SUBFIELD_GENERATED, RING_MUL_LZERO, RING_MUL_LID, RING_ADD_RZERO, RING_ADD_LZERO, RING_1, RING_OF_INT, RING_MUL_RID, RING_OF_NUM, RING_MUL_RZERO], ALL_TAC] THEN REWRITE_TAC [basis_discriminant] THEN wPart lhand (lhand o rand) RING_DET_DIAGONAL THEN REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_LT_2, ARITH_EQ] THEN ASM_SIMP_TAC [RING_MUL_LID, RING_MUL_RID, RING_1, SUBFIELD_GENERATED] THEN DISCH_THEN SUBST1_TAC THEN wPart lhand (lhand o rand) RING_PRODUCT_LT_2 THEN REWRITE_TAC [ALGEBRA_TRACE_NORM_IN_CARRIER] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [RING_MUL_LID, RING_1, (← GSYM RING_POW_2), SUBFIELD_GENERATED, ARITH_EQ] THEN REWRITE_TAC [RING_OF_INT_MUL, RING_OF_INT_OF_NUM] THEN ASM_SIMP_TAC [RING_OF_INT, r1])

  -- @@RETURN BEGIN
  return { QUADRATIC_FIELD_EXISTS, QUADRATIC_EXTEND_HOMOMORPHISM,
           QUADRATIC_FIELD_UNIQUE_EXPLICIT, QUADRATIC_FIELD_UNIQUE,
           QUADRATIC_FIELD_TRACE, QUADRATIC_FIELD_INTEGRAL_COORDINATES,
           QUADRATIC_FIELD_INTEGRAL_FREE_BASIS, QUADRATIC_FIELD_INTEGRAL_BASIS_SQRT,
           QUADRATIC_FIELD_INTEGRAL_BASIS_HALF, QUADRATIC_FIELD_INTEGRAL_BASIS,
           QUADRATIC_FIELD_BASIS_DISCRIMINANT }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- quadratic.ml phrases from line 1435 to 1515                            -/
/- ---------------------------------------------------------------------- -/

structure Quadratic03 where
  -- @@FIELDS
  QUADRATIC_FIELD_BASIS_DISCRIMINANT_HALF : thm
  QUADRATIC_FIELD_DISCRIMINANT : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupQuadratic03 [HolBase] (D : QuadraticDeps) (BQuadratic01 : Quadratic01) (BQuadratic02 : Quadratic02) :
    ExceptT String IO Quadratic03 := do
  -- @@SCOPE BEGIN
  let { RING_RULE, .. } := D
  let { ARITH, ARITH_EQ, BASIS_DISCRIMINANT_CHANGE_OF_BASIS, DIVIDES_ZERO,
        FIELD_MUL_RINV, FIELD_SUBFIELD_GENERATED, FINITE_NUMSEG_LT, FORALL_LT_2,
        IMP_CONJ, IN_ELIM_THM, I_THM, NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD,
        NUMBER_FIELD_IMP_FIELD, .. } := D.core1
  let { RIGHT_FORALL_IMP_THM, RING_0, RING_0_IN_SUBFIELD_GENERATED, RING_1,
        RING_1_IN_SUBFIELD_GENERATED, RING_ADD_LDISTRIB, RING_ADD_RZERO,
        RING_DET_LOWERTRIANGULAR, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, RING_INV,
        RING_INV_IN_SUBFIELD_GENERATED, RING_MUL, RING_MUL_LID, RING_MUL_LZERO,
        RING_OF_INT, RING_OF_INT_EQ_CHAR_0, RING_OF_INT_IN_SUBFIELD_GENERATED,
        RING_OF_INT_MUL, RING_OF_INT_OF_NUM, RING_OF_NUM_EQ_0,
        RING_POW_SUBFIELD_GENERATED, RING_PRODUCT_LT_2, RING_SUM_LT_2,
        SUBFIELD_GENERATED, number_field, .. } := D.core2
  let { QUADRATIC_FIELD_FREE_BASIS, SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD,
        SUBFIELD_GENERATED_HALF_SUCC, .. } := BQuadratic01
  let { QUADRATIC_FIELD_BASIS_DISCRIMINANT, QUADRATIC_FIELD_INTEGRAL_BASIS, .. } := BQuadratic02
  -- @@SCOPE END

  let QUADRATIC_FIELD_BASIS_DISCRIMINANT_HALF ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!k:A ring h D.
         ring_mul k (ring_of_num k 2) h = ring_1 k
         ==> ring_mul k (ring_pow k h 2) (ring_mul k (ring_of_num k 4) D) =
             D")
    let r2 ← RING_RULE (← q r"!k:A ring h w.
           ring_mul k (ring_of_num k 2) h = ring_1 k
           ==> w = ring_mul k h (ring_mul k (ring_of_num k 2) w)")
    prove
      r"!k:A ring x d.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
          x IN ring_carrier k /\
          ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
          ring_pow k x 2 = ring_of_int k d
          ==> basis_discriminant (subfield_generated k {ring_0 k},k) I 2
                (\i. if i = 0 then ring_1 k
                     else ring_div k (ring_add k (ring_1 k) x)
                                     (ring_of_num k 2)) =
              ring_of_int k d"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (fun th => tactic_of do pure (ASSUME_TAC (← MATCH_MP NUMBER_FIELD_IMP_FIELD th) THEN STRIP_ASSUME_TAC (← REWRITE_RULE [number_field] th))) THEN SUBGOAL_THEN (← q r"~(ring_of_num k 2:A = ring_0 k)") ASSUME_TAC THENL [ASM_REWRITE_TAC [RING_OF_NUM_EQ_0, DIVIDES_ZERO, ARITH_EQ], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{ring_0 k:A}"), (← q r"x:A")] SUBFIELD_GENERATED_HALF_SUCC) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"w = ring_div k (ring_add k (ring_1 k) x) (ring_of_num k 2):A") THEN STRIP_TAC THEN ABBREV_TAC (← q r"h = ring_inv k (ring_of_num k 2):A") THEN SUBGOAL_THEN (← q r"h IN ring_carrier(subfield_generated k {ring_0 k}) /\
      h IN ring_carrier k /\ ring_mul k (ring_of_num k 2) h = ring_1 k:A") STRIP_ASSUME_TAC THENL [EXPAND_TAC "h" THEN REWRITE_TAC [(← GSYM RING_OF_INT_OF_NUM)] THEN ASM_SIMP_TAC [RING_INV_IN_SUBFIELD_GENERATED, FIELD_SUBFIELD_GENERATED, RING_INV, RING_OF_INT, FIELD_MUL_RINV, RING_OF_INT_OF_NUM, RING_OF_INT_IN_SUBFIELD_GENERATED], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"2"), (← q r"\i. if i = 0 then ring_1 k else x:A"), (← q r"\i. if i = 0 then ring_1 k else w:A"), (← q r"\i j. if i = 0 then (if j = 0 then ring_1 k else ring_0 k) else h:A")] BASIS_DISCRIMINANT_CHANGE_OF_BASIS) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION, QUADRATIC_FIELD_FREE_BASIS, QUADRATIC_FIELD_BASIS_DISCRIMINANT] THEN ANTS_TAC THENL [REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_LT_2, ARITH_EQ, I_THM] THEN ASM_SIMP_TAC [RING_SUM_LT_2, RING_0_IN_SUBFIELD_GENERATED, RING_1_IN_SUBFIELD_GENERATED, RING_MUL, RING_1, RING_0, ARITH_EQ, RING_MUL_LID, RING_MUL_LZERO, RING_ADD_RZERO] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"h:A"), (← q r"w:A")] r2) THEN ASM_SIMP_TAC [RING_ADD_LDISTRIB, RING_1], DISCH_THEN SUBST1_TAC] THEN SUBGOAL_THEN (← q r"ring_det (subfield_generated k {ring_0 k}) {i | i < 2}
        (\i j. if i = 0 then if j = 0 then ring_1 k else ring_0 k else h) =
      h:A") SUBST1_TAC THENL [wPart lhand (lhand o rand) RING_DET_LOWERTRIANGULAR THEN REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN ANTS_TAC THENL [REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_LT_2, ARITH] THEN REWRITE_TAC [SUBFIELD_GENERATED], DISCH_THEN SUBST1_TAC] THEN wPart lhand (lhand o rand) RING_PRODUCT_LT_2 THEN ASM_REWRITE_TAC [ARITH_EQ, RING_1_IN_SUBFIELD_GENERATED] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [SUBFIELD_GENERATED, RING_MUL_LID], ALL_TAC] THEN REWRITE_TAC [SUBFIELD_GENERATED, RING_POW_SUBFIELD_GENERATED, RING_OF_INT_MUL, RING_OF_INT_OF_NUM] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"h:A"), (← q r"ring_of_int k d:A")] r1) THEN ASM_SIMP_TAC [RING_OF_INT])

  let QUADRATIC_FIELD_DISCRIMINANT ← prove
    r"!k:A ring x d.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
        squarefree(num_of_int(abs d)) /\ ~(d = &1)
        ==> number_field_discriminant k =
            if (d == &1) (mod &4) then d else &4 * d"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (fun th => tactic_of do pure (ASSUME_TAC (← MATCH_MP NUMBER_FIELD_IMP_FIELD th) THEN STRIP_ASSUME_TAC (← REWRITE_RULE [number_field] th))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"d:int")] SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← SPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"d:int")] QUADRATIC_FIELD_INTEGRAL_BASIS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (CONJ (← ASSUME (← q r"number_field(k:A ring)")))) THEN DISCH_THEN (MP_TAC o (MATCH_MP NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD)) THEN COND_CASES_TAC THEN ASM_SIMP_TAC [QUADRATIC_FIELD_BASIS_DISCRIMINANT, QUADRATIC_FIELD_BASIS_DISCRIMINANT_HALF, RING_OF_INT_EQ_CHAR_0])

  -- @@RETURN BEGIN
  return { QUADRATIC_FIELD_BASIS_DISCRIMINANT_HALF, QUADRATIC_FIELD_DISCRIMINANT }
  -- @@RETURN END

end HolANT.Quadratic
