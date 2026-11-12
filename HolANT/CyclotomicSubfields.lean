/- ========================================================================= -/
/- ANT: Subfields of cyclotomic fields and cyclotomic units                -/
/- ========================================================================= -/
/- File: HolANT/CyclotomicSubfields.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/cyclotomic_subfields.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antcyclotomicsubfieldsdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/products.ml, Library/multiplicative.ml, Library/frag.ml, Library/grouptheory.ml, Library/symmetric_group.ml, Library/galois.ml, Library/integer.ml, Library/isum.ml, Library/primitive.ml, Library/modmul_group.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/prime_split.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/norm_index.ml, ANT/classgroup.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/relative_split.ml, Library/ring_groups.ml, Library/finite_fields.ml, ANT/cyclotomic_poly.ml, ANT/relative_degree.ml, ANT/nf_valuation.ml, ANT/integrality.ml, ANT/dedekind_kummer.ml, ANT/power_basis.ml, ANT/cyclotomic_field.ml, ANT/cyclotomic_integers.ml, Library/cyclotomic.ml, ANT/cyclotomic_galois.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.CyclotomicSubfields fills them).

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
import HolLibrary.Multiplicative
import HolLibrary.Frag
import HolLibrary.GroupTheory
import HolLibrary.SymmetricGroup
import HolLibrary.Galois
import HolLibrary.Integer
import HolLibrary.Isum
import HolLibrary.Primitive
import HolLibrary.ModmulGroup
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
import HolANT.PrimeSplit
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.NormIndex
import HolANT.Classgroup
import HolANT.Discriminant
import HolANT.TraceForm
import HolANT.RelativeSplit
import HolLibrary.RingGroups
import HolLibrary.FiniteFields
import HolANT.CyclotomicPoly
import HolANT.RelativeDegree
import HolANT.NfValuation
import HolANT.Integrality
import HolANT.DedekindKummer
import HolANT.PowerBasis
import HolANT.CyclotomicField
import HolANT.CyclotomicIntegers
import HolLibrary.Cyclotomic
import HolANT.CyclotomicGalois

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
open HolANT.PrimeSplit
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.NormIndex
open HolANT.Classgroup
open HolANT.Discriminant
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.CyclotomicPoly
open HolANT.RelativeDegree
open HolANT.NfValuation
open HolANT.Integrality
open HolANT.DedekindKummer
open HolANT.PowerBasis
open HolANT.CyclotomicField
open HolANT.CyclotomicIntegers
open HolANT.CyclotomicGalois

namespace HolANT.CyclotomicSubfields

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (CARD_CLAUSES CARRIER_SUBFIELD_GENERATED_SUBFIELD CONG_SOLVE COPRIME_0
   COPRIME_1 CYCLOTOMIC_FIELD_DEGREE CYCLOTOMIC_FIELD_GALOIS_EXTENSION
   CYCLOTOMIC_FIELD_GALOIS_GROUP_EQ CYCLOTOMIC_FIELD_GALOIS_GROUP_EXISTS
   CYCLOTOMIC_FIELD_GALOIS_GROUP_HAS_SIZE CYCLOTOMIC_FIELD_GALOIS_GROUP_MODMUL
   CYCLOTOMIC_FIELD_RING_OF_INTEGERS CYCLOTOMIC_POLY_EVAL_1
   CYCLOTOMIC_POLY_SPLITS DE_MORGAN_THM DIVIDES_LE DIVIDES_LMUL DIVIDES_REFL
   DIVIDES_REXP DIVIDES_RMUL DIV_MULT EMPTY_SUBSET EQ_MULT_LCANCEL EQ_TRANS EXP
   EXTENSION EXTENSION_DEGREE_EQ_1 EXTENSION_DEGREE_TOWER_LAW FIELD_ADD_INV_EQ
   FIELD_DIV_EQ_MUL FIELD_EXTENSION_SUBFIELD_GENERATED_SUBSET
   FIELD_HOMOMORPHISM_INV FIELD_IMP_INTEGRAL_DOMAIN FIELD_MUL_LINV
   FIELD_NONTRIVIAL FIELD_SUBFIELD_GENERATED FIELD_UNIT FINITE_EMPTY
   FINITE_INSERT FINITE_NUMSEG_LT FINITE_SING FINITE_SUBSET FORALL_UNWIND_THM2
   FUNDAMENTAL_THEOREM_OF_GALOIS_THEORY GALOIS_COMPOSITUM_DEGREE
   GALOIS_CYCLIC_INTERMEDIATE_UNIQUE GALOIS_GROUP_I GALOIS_GROUP_IN_CARRIER
   GALOIS_GROUP_PERMUTES GALOIS_GROUP_RING_AUTOMORPHISM
   GALOIS_GROUP_RING_HOMOMORPHISM GALOIS_GROUP_RING_MONOMORPHISM GCD_ZERO
   HAS_SIZE IMAGE_I INSERT_SUBSET INTEGRAL_DOMAIN_ASSOCIATES
   INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING INTEGRAL_DOMAIN_REGULAR
   INTEGRAL_DOMAIN_RING_OF_INTEGERS IN_ELIM_THM IN_FIXED_FIELD
   IN_GALOIS_GROUP_SUBFIELD_GENERATED IN_INSERT IN_INTER IN_SING
   ISOMORPHIC_GROUP_CYCLICITY I_O_ID I_THM LCM_ZERO LEFT_IMP_EXISTS_THM
   MEMBER_NOT_EMPTY MONO_EXISTS MULT_CLAUSES MULT_EQ_0 MULT_SYM NOT_EXISTS_THM
   NOT_IN_EMPTY NUMBER_FIELD_IMP_FIELD NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q
   NUMBER_FIELD_SUBFIELD_GENERATED_ALGEBRAIC PERMUTES_I PHI_EQ_0 PHI_LCM_GCD
   POLY_EVAL_CONST POLY_EVAL_RING_PRODUCT POLY_EVAL_SUB POLY_EVAL_VAR
   PRIMEPOW_FACTOR PRIME_1 PRIME_2 PRIME_FACTOR PRIME_GE_2
   PRIME_SUBFIELD_MINIMAL PRIME_SUBFIELD_SUBFIELD_GENERATED RINGS_EQ RING_0 : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (RING_0_IN_SUBRING_GENERATED RING_1 RING_1_IN_SUBRING_GENERATED RING_ADD
   RING_ADD_IN_SUBRING_GENERATED RING_ADD_LZERO RING_ADD_RZERO RING_ADD_SYM
   RING_ASSOCIATES_PRIME_POWER_ORDER RING_ASSOCIATES_UNIT RING_AUTOMORPHISM_I
   RING_CARRIER_SUBFIELD_GENERATED_SUBSET RING_CARRIER_SUBRING_GENERATED_SUBSET
   RING_DIVIDES_SUB_POW RING_DIV_IN_SUBFIELD_GENERATED RING_HOMOMORPHISM_0
   RING_HOMOMORPHISM_ADD RING_HOMOMORPHISM_SUBFIELD_INCLUSION RING_INV
   RING_INV_INV RING_ISOMORPHISM_IMP_HOMOMORPHISM RING_MUL
   RING_MUL_IN_SUBRING_GENERATED RING_MUL_LID RING_MUL_LZERO
   RING_NEG_IN_SUBRING_GENERATED RING_OF_INTEGERS RING_OF_INTEGERS_ALGEBRAIC
   RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE_EQ RING_OF_INTEGERS_SUBSET RING_ORDER_1
   RING_ORDER_DIVIDES RING_ORDER_EQ_1 RING_ORDER_LCM_EXISTS RING_ORDER_POW
   RING_ORDER_SUBFIELD_GENERATED RING_ORDER_SUBRING_GENERATED RING_POLYNOMIAL
   RING_POLYNOMIAL_CONST RING_POLYNOMIAL_SUB RING_POLYNOMIAL_VAR RING_POW
   RING_POW_1 RING_POW_2 RING_POW_EQ RING_POW_IN_SUBRING_GENERATED RING_POW_ONE
   RING_POW_POW RING_POW_RING_ORDER RING_POW_SUBFIELD_GENERATED RING_POW_ZERO
   RING_PRODUCT RING_PRODUCT_DELETE RING_PRODUCT_EQ
   RING_PRODUCT_RING_OF_INTEGERS RING_RINV_UNIQUE RING_SUB RING_SUB_EQ_0
   RING_SUB_REFL RING_SUB_SUBFIELD_GENERATED RING_UNIT_0
   RING_UNIT_NOT_IN_PRIME_IDEAL RING_UNIT_POW ROOT_OF_UNITY_IN_RING_OF_INTEGERS
   SING_SUBSET SUBFIELD_GENERATED SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED
   SUBFIELD_GENERATED_IDEMPOT SUBFIELD_GENERATED_INC SUBFIELD_GENERATED_MINIMAL
   SUBFIELD_GENERATED_MONO SUBFIELD_GENERATED_ROOT_OF_UNITY
   SUBFIELD_GENERATED_ROOT_OF_UNITY_EQ SUBFIELD_GENERATED_SUBSET_EQ
   SUBFIELD_GENERATED_UNION SUBFIELD_OF_INTER SUBFIELD_SUBFIELD_GENERATED_EQ
   SUBRING_GENERATED SUBRING_GENERATED_INC_GEN SUBRING_GENERATED_MINIMAL
   SUBRING_SUBRING_GENERATED SUBRING_SUBSET_SUBFIELD_GENERATED SUBSET
   SUBSET_ANTISYM SUBSET_INTER coprime divides isomorphic_group number_field
   ring_associates ring_automorphism ring_monomorphism ring_of_integers ring_pow
   ring_sub ring_unit subring_of : thm)
  deriving Inhabited

/-- What cyclotomic_subfields.ml uses from Session besides theorems. -/
structure CyclotomicSubfieldsDeps where
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
  NUM_RING : ioconv
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
/- cyclotomic_subfields.ml phrases from line 88 to 557                    -/
/- ---------------------------------------------------------------------- -/

structure CyclotomicSubfields01 where
  -- @@FIELDS
  CYCLOTOMIC_SUBFIELD_COMPOSITUM : thm
  CYCLOTOMIC_SUBFIELD_DEGREE : thm
  CYCLOTOMIC_SUBFIELD_INTER : thm
  CYCLOTOMIC_FIELD_SUBFIELD_UNIQUE : thm
  CYCLOTOMIC_FIELD_INVERSION_EXISTS : thm
  CYCLOTOMIC_FIELD_REAL_SUBFIELD : thm
  CYCLOTOMIC_FIELD_REAL_SUBFIELD_RING_OF_INTEGERS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupCyclotomicSubfields01 [HolBase] (D : CyclotomicSubfieldsDeps) :
    ExceptT String IO CyclotomicSubfields01 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, MESON, MESON_TAC, NUMBER_RULE,
        NUM_REDUCE_CONV, NUM_RING, RING_RULE, SET_RULE, SET_TAC, TAUT, .. } := D
  let { CARD_CLAUSES, CARRIER_SUBFIELD_GENERATED_SUBFIELD, CYCLOTOMIC_FIELD_DEGREE,
        CYCLOTOMIC_FIELD_GALOIS_EXTENSION, CYCLOTOMIC_FIELD_GALOIS_GROUP_EQ,
        CYCLOTOMIC_FIELD_GALOIS_GROUP_EXISTS, CYCLOTOMIC_FIELD_GALOIS_GROUP_HAS_SIZE,
        CYCLOTOMIC_FIELD_GALOIS_GROUP_MODMUL, CYCLOTOMIC_FIELD_RING_OF_INTEGERS,
        DE_MORGAN_THM, DIVIDES_LE, DIV_MULT, EMPTY_SUBSET, EQ_MULT_LCANCEL, EQ_TRANS,
        EXTENSION, EXTENSION_DEGREE_EQ_1, EXTENSION_DEGREE_TOWER_LAW, FIELD_ADD_INV_EQ,
        FIELD_DIV_EQ_MUL, FIELD_EXTENSION_SUBFIELD_GENERATED_SUBSET,
        FIELD_HOMOMORPHISM_INV, FIELD_MUL_LINV, FIELD_NONTRIVIAL,
        FIELD_SUBFIELD_GENERATED, FIELD_UNIT, FINITE_EMPTY, FINITE_INSERT, FINITE_SING,
        FORALL_UNWIND_THM2, FUNDAMENTAL_THEOREM_OF_GALOIS_THEORY,
        GALOIS_COMPOSITUM_DEGREE, GALOIS_CYCLIC_INTERMEDIATE_UNIQUE, GALOIS_GROUP_I,
        GALOIS_GROUP_IN_CARRIER, GALOIS_GROUP_PERMUTES, GALOIS_GROUP_RING_AUTOMORPHISM,
        GALOIS_GROUP_RING_HOMOMORPHISM, GALOIS_GROUP_RING_MONOMORPHISM, GCD_ZERO,
        HAS_SIZE, IMAGE_I, INSERT_SUBSET, IN_ELIM_THM, IN_FIXED_FIELD,
        IN_GALOIS_GROUP_SUBFIELD_GENERATED, IN_INSERT, IN_INTER, IN_SING,
        ISOMORPHIC_GROUP_CYCLICITY, I_O_ID, I_THM, LCM_ZERO, LEFT_IMP_EXISTS_THM,
        MONO_EXISTS, MULT_EQ_0, MULT_SYM, NOT_IN_EMPTY, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_SUBFIELD_GENERATED_ALGEBRAIC, PERMUTES_I, PHI_EQ_0, PHI_LCM_GCD,
        PRIME_SUBFIELD_MINIMAL, PRIME_SUBFIELD_SUBFIELD_GENERATED, RINGS_EQ, RING_0, .. } := D.core1
  let { RING_0_IN_SUBRING_GENERATED, RING_1, RING_1_IN_SUBRING_GENERATED, RING_ADD,
        RING_ADD_IN_SUBRING_GENERATED, RING_ADD_LZERO, RING_ADD_RZERO, RING_ADD_SYM,
        RING_AUTOMORPHISM_I, RING_CARRIER_SUBFIELD_GENERATED_SUBSET,
        RING_CARRIER_SUBRING_GENERATED_SUBSET, RING_DIV_IN_SUBFIELD_GENERATED,
        RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_ADD,
        RING_HOMOMORPHISM_SUBFIELD_INCLUSION, RING_INV, RING_INV_INV,
        RING_ISOMORPHISM_IMP_HOMOMORPHISM, RING_MUL, RING_MUL_IN_SUBRING_GENERATED,
        RING_MUL_LID, RING_MUL_LZERO, RING_NEG_IN_SUBRING_GENERATED, RING_OF_INTEGERS,
        RING_OF_INTEGERS_ALGEBRAIC, RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE_EQ,
        RING_ORDER_DIVIDES, RING_ORDER_LCM_EXISTS, RING_ORDER_POW,
        RING_ORDER_SUBFIELD_GENERATED, RING_POW, RING_POW_2,
        RING_POW_IN_SUBRING_GENERATED, RING_POW_RING_ORDER,
        RING_POW_SUBFIELD_GENERATED, RING_POW_ZERO, RING_RINV_UNIQUE, RING_SUB,
        RING_SUB_SUBFIELD_GENERATED, ROOT_OF_UNITY_IN_RING_OF_INTEGERS, SING_SUBSET,
        SUBFIELD_GENERATED, SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED,
        SUBFIELD_GENERATED_IDEMPOT, SUBFIELD_GENERATED_INC, SUBFIELD_GENERATED_MINIMAL,
        SUBFIELD_GENERATED_MONO, SUBFIELD_GENERATED_ROOT_OF_UNITY,
        SUBFIELD_GENERATED_ROOT_OF_UNITY_EQ, SUBFIELD_GENERATED_SUBSET_EQ,
        SUBFIELD_GENERATED_UNION, SUBFIELD_OF_INTER, SUBFIELD_SUBFIELD_GENERATED_EQ,
        SUBRING_GENERATED, SUBRING_GENERATED_INC_GEN, SUBRING_GENERATED_MINIMAL,
        SUBRING_SUBRING_GENERATED, SUBRING_SUBSET_SUBFIELD_GENERATED, SUBSET,
        SUBSET_ANTISYM, SUBSET_INTER, divides, isomorphic_group, number_field,
        ring_automorphism, ring_monomorphism, ring_pow, ring_sub, subring_of, .. } := D.core2
  -- @@SCOPE END

  let CYCLOTOMIC_SUBFIELD_COMPOSITUM ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(s:A->bool) SUBSET t ==> (x:A) IN s ==> x IN t")
    let r2 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!(l:A ring) z w.
          field l /\ z IN ring_carrier l /\ w IN ring_carrier l /\
          ~(ring_order l z = 0) /\ ~(ring_order l w = 0)
          ==> (?v. v IN ring_carrier(subfield_generated l {z,w}) /\
                   ring_order l v = lcm(ring_order l z,ring_order l w)) /\
              !v. v IN ring_carrier l /\
                  ring_order l v = lcm(ring_order l z,ring_order l w)
                  ==> subfield_generated l {z,w} = subfield_generated l {v}"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(z:A) IN ring_carrier(subfield_generated l {z,w}) /\
      (w:A) IN ring_carrier(subfield_generated l {z,w})") STRIP_ASSUME_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC SUBFIELD_GENERATED_INC THEN ASM SET_TAC [], ALL_TAC] THEN MATCH_MP_TAC r2 THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"subfield_generated l {z:A,w}"), (← q r"z:A"), (← q r"w:A")] RING_ORDER_LCM_EXISTS) THEN ASM_SIMP_TAC [RING_ORDER_SUBFIELD_GENERATED] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"v:A") THEN MESON_TAC [RING_ORDER_SUBFIELD_GENERATED], DISCH_THEN (X_CHOOSE_THEN (← q r"u:A") STRIP_ASSUME_TAC)] THEN X_GEN_TAC (← q r"v:A") THEN STRIP_TAC THEN ABBREV_TAC (← q r"N = lcm(ring_order l (z:A),ring_order l w)") THEN SUBGOAL_THEN (← q r"~(N = 0)") ASSUME_TAC THENL [EXPAND_TAC "N" THEN ASM_REWRITE_TAC [LCM_ZERO], ALL_TAC] THEN SUBGOAL_THEN (← q r"(u:A) IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_pow l (z:A) N = ring_1 l /\ ring_pow l (w:A) N = ring_1 l") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"l:A ring"), (← q r"z:A"), (← q r"N:num")] RING_ORDER_DIVIDES) THEN MP_TAC (← ISPECL [(← q r"l:A ring"), (← q r"w:A"), (← q r"N:num")] RING_ORDER_DIVIDES) THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "N" THEN REWRITE_TAC [(← ExceptT.mk (NUMBER_RULE (← q r"!m n:num. m divides lcm(m,n) /\
                                         n divides lcm(m,n)")))] THEN SIMP_TAC [], ALL_TAC] THEN MATCH_MP_TAC SUBFIELD_GENERATED_SUBSET_EQ THEN ASM_REWRITE_TAC [INSERT_SUBSET, EMPTY_SUBSET] THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC SUBFIELD_GENERATED_ROOT_OF_UNITY THEN EXISTS_TAC (← q r"N:num") THEN ASM_REWRITE_TAC [], MATCH_MP_TAC SUBFIELD_GENERATED_ROOT_OF_UNITY THEN EXISTS_TAC (← q r"N:num") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"l:A ring"), (← q r"u:A"), (← q r"v:A")] SUBFIELD_GENERATED_ROOT_OF_UNITY_EQ) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(v:A) IN ring_carrier(subfield_generated l {u})") MP_TAC THENL [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SUBFIELD_GENERATED_INC THEN ASM SET_TAC [], ALL_TAC] THEN MATCH_MP_TAC r1 THEN MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED_EQ, FIELD_SUBFIELD_GENERATED] THEN ASM SET_TAC [])

  let CYCLOTOMIC_SUBFIELD_DEGREE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!(l:A ring) z n.
          field l /\ ring_char l = 0 /\ z IN ring_carrier l /\
          ring_order l z = n /\ ~(n = 0)
          ==> number_field(subfield_generated l {z}) /\
              extension_degree
                (subfield_generated l {ring_0 l},subfield_generated l {z}) I =
              phi n"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [MATCH_MP_TAC NUMBER_FIELD_SUBFIELD_GENERATED_ALGEBRAIC THEN ASM_REWRITE_TAC [FINITE_SING, IN_SING, FORALL_UNWIND_THM2] THEN MATCH_MP_TAC RING_OF_INTEGERS_ALGEBRAIC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC ROOT_OF_UNITY_IN_RING_OF_INTEGERS THEN EXISTS_TAC (← q r"n:num") THEN ASM_MESON_TAC [RING_POW_RING_ORDER], DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"subfield_generated l {z:A}"), (← q r"z:A"), (← q r"n:num")] CYCLOTOMIC_FIELD_DEGREE) THEN ASM_SIMP_TAC [PRIME_SUBFIELD_SUBFIELD_GENERATED, SUBFIELD_GENERATED_IDEMPOT, RING_ORDER_SUBFIELD_GENERATED, SUBFIELD_GENERATED_INC, SING_SUBSET, IN_SING])

  let CYCLOTOMIC_SUBFIELD_INTER ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"subfield_generated l (J:A->bool)"
    let q2 ← q r"subfield_generated l {u:A}"
    let q3 ← q r"I:A->A"
    let v4 ← ISPECL [q3, q2, q1] EXTENSION_DEGREE_EQ_1
    let q15 ← q r"phi g * t * phi n"
    let q16 ← q r"!a x:num. ~(a = 0) /\ a * x = a * 1 ==> x = 1"
    let r17 ← MESON [EQ_MULT_LCANCEL] q16
    let q18 ← q r"g:num"
    let v19 ← SPEC q18 PHI_EQ_0
    let q20 ← q r"N:num"
    let v21 ← SPEC q20 PHI_EQ_0
    let q22 ← q r"n:num"
    let q23 ← q r"m:num"
    let v24 ← SPECL [q23, q22] PHI_LCM_GCD
    let q25 ← q r"x = 1"
    let q26 ← q r"t = extension_degree
          (subfield_generated l J,subfield_generated l {z:A}) I"
    let q27 ← q r"x = extension_degree
          (subfield_generated l {u:A},subfield_generated l J) I"
    let q28 ← q r"subfield_generated l (J:A->bool)"
    let q29 ← q r"subfield_generated l {u:A}"
    let q30 ← q r"subfield_generated l {ring_0 l:A}"
    let q31 ← q r"I:A->A"
    let q32 ← q r"I:A->A"
    let v33 ← ISPECL [q32, q31, q30, q29, q28] EXTENSION_DEGREE_TOWER_LAW
    let q34 ← q r"subfield_generated l {z:A}"
    let q35 ← q r"subfield_generated l (J:A->bool)"
    let q36 ← q r"subfield_generated l {ring_0 l:A}"
    let q37 ← q r"I:A->A"
    let q38 ← q r"I:A->A"
    let v39 ← ISPECL [q38, q37, q36, q35, q34] EXTENSION_DEGREE_TOWER_LAW
    let q40 ← q r"subfield_generated l {v:A}"
    let q41 ← q r"subfield_generated l {w:A}"
    let q42 ← q r"subfield_generated l {ring_0 l:A}"
    let q43 ← q r"I:A->A"
    let q44 ← q r"I:A->A"
    let v45 ← ISPECL [q44, q43, q42, q41, q40] EXTENSION_DEGREE_TOWER_LAW
    let q50 ← q r"ring_carrier(subfield_generated l {w:A}) SUBSET
    ring_carrier(subfield_generated l {v}) /\
    ring_carrier(subfield_generated l {ring_0 l}) SUBSET J /\
    J SUBSET ring_carrier(subfield_generated l {z:A})"
    let q51 ← q r"{a:A} UNION {b} = {a,b}"
    let r52 ← SET_RULE q51
    let q53 ← q r"ring_carrier(subfield_generated l {w:A})"
    let q54 ← q r"ring_carrier(subfield_generated l {z:A})"
    let q55 ← q r"l:A ring"
    let q56 ← q r"subfield_generated l {ring_0 l:A}"
    let q57 ← q r"I:A->A"
    let v58 ← ISPECL [q57, q56, q55, q54, q53] GALOIS_COMPOSITUM_DEGREE
    let q59 ← q r"number_field(subfield_generated l {z:A})"
    let q60 ← q r"m:num"
    let q61 ← q r"z:A"
    let q62 ← q r"subfield_generated l {z:A}"
    let v63 ← ISPECL [q62, q61, q60] CYCLOTOMIC_FIELD_GALOIS_EXTENSION
    let q64 ← q r"finite_extension(subfield_generated l {ring_0 l},
                     subfield_generated l {z:A}) I /\
    galois_extension(subfield_generated l {ring_0 l},
                     subfield_generated l {z:A}) I"
    let q65 ← q r"N:num"
    let q66 ← q r"v:A"
    let q67 ← q r"l:A ring"
    let v68 ← ISPECL [q67, q66, q65] CYCLOTOMIC_SUBFIELD_DEGREE
    let q69 ← q r"g:num"
    let q70 ← q r"u:A"
    let q71 ← q r"l:A ring"
    let v72 ← ISPECL [q71, q70, q69] CYCLOTOMIC_SUBFIELD_DEGREE
    let q73 ← q r"n:num"
    let q74 ← q r"w:A"
    let q75 ← q r"l:A ring"
    let v76 ← ISPECL [q75, q74, q73] CYCLOTOMIC_SUBFIELD_DEGREE
    let q77 ← q r"m:num"
    let q78 ← q r"z:A"
    let q79 ← q r"l:A ring"
    let v80 ← ISPECL [q79, q78, q77] CYCLOTOMIC_SUBFIELD_DEGREE
    let q81 ← q r"u:A"
    let q82 ← q r"l:A ring"
    let v83 ← ISPECL [q82, q81] RING_ORDER_DIVIDES
    let q84 ← q r"n:num"
    let q85 ← q r"m:num"
    let q86 ← q r"ring_carrier(subfield_generated l {u:A}) SUBSET J"
    let q87 ← q r"(J:A->bool) subfield_of l"
    let q88 ← q r"J = ring_carrier(subfield_generated l {z:A}) INTER
        ring_carrier(subfield_generated l {w})"
    let q89 ← q r"!x:A. x IN ring_carrier l
          ==> ring_carrier(subfield_generated l {x}) subfield_of l /\
              ring_carrier(subfield_generated l {ring_0 l}) SUBSET
              ring_carrier(subfield_generated l {x})"
    let q90 ← q r"(v:A) IN ring_carrier l"
    let q91 ← q r"v:A"
    let q92 ← q r"v:A"
    let q93 ← q r"w:A"
    let q94 ← q r"z:A"
    let q95 ← q r"l:A ring"
    let v96 ← ISPECL [q95, q94, q93] CYCLOTOMIC_SUBFIELD_COMPOSITUM
    let q97 ← q r"~((N:num) = 0)"
    let q98 ← q r"N = lcm(m:num,n)"
    let q99 ← q r"u:A"
    let q100 ← q r"q:num"
    let q101 ← q r"z:A"
    let q102 ← q r"l:A ring"
    let v103 ← ISPECL [q102, q101, q100] RING_ORDER_POW
    let q104 ← q r"q:num"
    let q108 ← q r"m DIV g"
    let q109 ← q r"z:A"
    let q110 ← q r"subfield_generated l {z:A}"
    let v111 ← ISPECL [q110, q109, q108] RING_POW
    let q112 ← q r"ring_pow l (z:A) (m DIV g)"
    let q113 ← q r"~((g:num) = 0) /\ g divides m /\ g divides n"
    let q114 ← q r"g = gcd(m:num,n)"
    let q115 ← q r"n = ring_order l (w:A)"
    let q116 ← q r"m = ring_order l (z:A)"
    prove
      r"!(l:A ring) z w.
          field l /\ ring_char l = 0 /\
          z IN ring_carrier l /\ w IN ring_carrier l /\
          ~(ring_order l z = 0) /\ ~(ring_order l w = 0)
          ==> (?u. u IN ring_carrier(subfield_generated l {z}) /\
                   ring_order l u = gcd(ring_order l z,ring_order l w)) /\
              !u. u IN ring_carrier l /\
                  ring_order l u = gcd(ring_order l z,ring_order l w)
                  ==> ring_carrier(subfield_generated l {z}) INTER
                      ring_carrier(subfield_generated l {w}) =
                      ring_carrier(subfield_generated l {u})"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY ABBREV_TAC [q116, q115] THEN ABBREV_TAC q114 THEN SUBGOAL_THEN q113 STRIP_ASSUME_TAC THENL [EXPAND_TAC "g" THEN CONJ_TAC THENL [ASM_REWRITE_TAC [GCD_ZERO], CONV_TAC NUMBER_RULE], ALL_TAC] THEN CONJ_TAC THENL [EXISTS_TAC q112 THEN CONJ_TAC THENL [MP_TAC v111 THEN REWRITE_TAC [RING_POW_SUBFIELD_GENERATED] THEN DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC SUBFIELD_GENERATED_INC THEN ASM SET_TAC [], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o ((GEN_REWRITE_RULE id [divides]) o (checkM (fun th => (do let z107 ← (q r"(g:num) divides m"); let z106 ← (do let z105 ← (pure th); pure (concl z105)); pure (z106 == z107)))))) THEN DISCH_THEN (X_CHOOSE_THEN q104 SUBST_ALL_TAC) THEN RULE_ASSUM_TAC (REWRITE_RULE [MULT_EQ_0, DE_MORGAN_THM]) THEN ASM_SIMP_TAC [DIV_MULT] THEN MP_TAC v103 THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [CONV_TAC NUMBER_RULE, DISCH_THEN SUBST1_TAC] THEN ONCE_REWRITE_TAC [MULT_SYM] THEN ASM_SIMP_TAC [DIV_MULT], ALL_TAC] THEN X_GEN_TAC q99 THEN STRIP_TAC THEN ABBREV_TAC q98 THEN SUBGOAL_THEN q97 ASSUME_TAC THENL [EXPAND_TAC "N" THEN ASM_REWRITE_TAC [LCM_ZERO], ALL_TAC] THEN MP_TAC v96 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN q92 STRIP_ASSUME_TAC) (MP_TAC o (SPEC q91))) THEN SUBGOAL_THEN q90 ASSUME_TAC THENL [ASM_MESON_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBSET], ASM_REWRITE_TAC [] THEN DISCH_TAC] THEN SUBGOAL_THEN q89 ASSUME_TAC THENL [REPEAT STRIP_TAC THEN ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED_EQ, FIELD_SUBFIELD_GENERATED] THEN MATCH_MP_TAC PRIME_SUBFIELD_MINIMAL THEN ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED_EQ, FIELD_SUBFIELD_GENERATED], ALL_TAC] THEN ABBREV_TAC q88 THEN SUBGOAL_THEN q87 ASSUME_TAC THENL [EXPAND_TAC "J" THEN MATCH_MP_TAC SUBFIELD_OF_INTER THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN q86 ASSUME_TAC THENL [MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "J" THEN REWRITE_TAC [SING_SUBSET, IN_INTER] THEN CONJ_TAC THEN MATCH_MP_TAC SUBFIELD_GENERATED_ROOT_OF_UNITY THENL [EXISTS_TAC q85, EXISTS_TAC q84] THEN ASM_REWRITE_TAC [] THEN MP_TAC v83 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM th)])) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC v80 THEN MP_TAC v76 THEN MP_TAC v72 THEN MP_TAC v68 THEN ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN q64 STRIP_ASSUME_TAC THENL [MP_TAC v63 THEN UNDISCH_TAC q59 THEN SIMP_TAC [number_field, PRIME_SUBFIELD_SUBFIELD_GENERATED, SUBFIELD_GENERATED_IDEMPOT] THEN ASM_SIMP_TAC [RING_ORDER_SUBFIELD_GENERATED, SUBFIELD_GENERATED_INC, SING_SUBSET, IN_SING], ALL_TAC] THEN MP_TAC v58 THEN ASM_SIMP_TAC [IMAGE_I, SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED, SUBFIELD_GENERATED_UNION] THEN REWRITE_TAC [r52] THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN SUBGOAL_THEN q50 STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z49 ← (q r"subfield_generated l {v:A}"); let z48 ← (do let z46 ← (do let z47 ← (pure th); pure (concl z47)); liftExcept (rhs z46)); pure (z48 == z49)))))) THEN MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN SET_TAC [], EXPAND_TAC "J" THEN REWRITE_TAC [SUBSET_INTER] THEN ASM_SIMP_TAC [], EXPAND_TAC "J" THEN SET_TAC []], ALL_TAC] THEN MP_TAC v45 THEN MP_TAC v39 THEN MP_TAC v33 THEN ASM_SIMP_TAC [FIELD_EXTENSION_SUBFIELD_GENERATED_SUBSET, I_O_ID, CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN ABBREV_TAC q27 THEN ABBREV_TAC q26 THEN REPEAT DISCH_TAC THEN SUBGOAL_THEN q25 ASSUME_TAC THENL [MP_TAC v24 THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC v21 THEN MP_TAC v19 THEN ASM_REWRITE_TAC [] THEN REPEAT DISCH_TAC THEN MATCH_MP_TAC r17 THEN EXISTS_TAC q15 THEN CONJ_TAC THENL [REWRITE_TAC [MULT_EQ_0] THEN ASM_MESON_TAC [MULT_EQ_0], FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do if ← (do if ← (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); pure (is_eq z5)) then (do let z7 ← (do let z8 ← (do let z9 ← (pure th); pure (concl z9)); liftExcept (lhs z8)); pure (is_comb z7)) else pure false) then (do let z14 ← (q r"phi n"); let z13 ← (do let z10 ← (do let z11 ← (do let z12 ← (pure th); pure (concl z12)); liftExcept (lhs z11)); liftExcept (rand z10)); pure (z13 == z14)) else pure false)))) THEN CONV_TAC NUM_RING], ALL_TAC] THEN MP_TAC v4 THEN ASM_SIMP_TAC [FIELD_EXTENSION_SUBFIELD_GENERATED_SUBSET, CARRIER_SUBFIELD_GENERATED_SUBFIELD, IMAGE_I] THEN MESON_TAC [])

  let CYCLOTOMIC_FIELD_SUBFIELD_UNIQUE ← prove
    r"!(k:A ring) z n s t.
        number_field k /\ z IN ring_carrier k /\ ring_order k z = n /\
        ~(n = 0) /\ subfield_generated k {z} = k /\
        cyclic_group(modmul_group n) /\
        s subfield_of k /\ t subfield_of k /\
        extension_degree (subfield_generated k {ring_0 k},
                          subfield_generated k s) I =
        extension_degree (subfield_generated k {ring_0 k},
                          subfield_generated k t) I
        ==> s = t"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC GALOIS_CYCLIC_INTERMEDIATE_UNIQUE THEN MAP_EVERY EXISTS_TAC [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring")] THEN ASM_SIMP_TAC [IMAGE_I, PRIME_SUBFIELD_MINIMAL] THEN REPEAT CONJ_TAC THENL [ASM_MESON_TAC [number_field], MATCH_MP_TAC CYCLOTOMIC_FIELD_GALOIS_EXTENSION THEN MAP_EVERY EXISTS_TAC [(← q r"z:A"), (← q r"n:num")] THEN ASM_REWRITE_TAC [], MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num")] CYCLOTOMIC_FIELD_GALOIS_GROUP_MODMUL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"e:(A->A)->num") (ASSUME_TAC o CONJUNCT1)) THEN MP_TAC (← ISPECL [(← q r"galois_group(subfield_generated k {ring_0 k},k) (I:A->A)"), (← q r"modmul_group n")] ISOMORPHIC_GROUP_CYCLICITY) THEN ASM_REWRITE_TAC [isomorphic_group] THEN ANTS_TAC THENL [ASM_MESON_TAC [], SIMP_TAC []]])

  let CYCLOTOMIC_FIELD_INVERSION_EXISTS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"~(n = 0) ==> SUC(n - 1) = n")
    prove
      r"!(k:A ring) z n.
          number_field k /\ z IN ring_carrier k /\ ring_order k z = n /\
          ~(n = 0) /\ subfield_generated k {z} = k
          ==> ?c. c IN group_carrier
                    (galois_group (subfield_generated k {ring_0 k},k) I) /\
                  c z = ring_inv k z"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num"), (← q r"n - 1")] CYCLOTOMIC_FIELD_GALOIS_GROUP_EXISTS) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"n = (n - 1) + 1") (fun th => GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THENL [ASM_ARITH_TAC, CONV_TAC NUMBER_RULE], MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"c:A->A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_RINV_UNIQUE THEN ASM_SIMP_TAC [RING_POW] THEN REWRITE_TAC [(← GSYM (← CONJUNCT2 ring_pow))] THEN ASM_SIMP_TAC [r1] THEN ASM_MESON_TAC [RING_POW_RING_ORDER]])

  let CYCLOTOMIC_FIELD_REAL_SUBFIELD ← prove
    r"!(k:A ring) z n c.
        number_field k /\ z IN ring_carrier k /\ ring_order k z = n /\
        2 < n /\ subfield_generated k {z} = k /\
        c IN group_carrier
               (galois_group (subfield_generated k {ring_0 k},k) I) /\
        c z = ring_inv k z
        ==> ~(c = I) /\
            group_carrier(galois_group
              (subfield_generated k {ring_add k z (ring_inv k z)},k) I) =
            {I,c} /\
            ring_carrier(subfield_generated k {ring_add k z (ring_inv k z)}) =
            fixed_field k {c} /\
            extension_degree
              (subfield_generated k {ring_add k z (ring_inv k z)},k) I = 2 /\
            2 * extension_degree
                  (subfield_generated k {ring_0 k},
                   subfield_generated k {ring_add k z (ring_inv k z)}) I =
            phi n"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN (← q r"~((n:num) = 0) /\ ~(z = ring_0 (k:A ring))") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [ASM_ARITH_TAC, DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A")] RING_POW_RING_ORDER) THEN ASM_REWRITE_TAC [RING_POW_ZERO] THEN COND_CASES_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN ASM_MESON_TAC [FIELD_NONTRIVIAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_inv k z IN ring_carrier k /\ ~(ring_inv k z = z:A)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_INV] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_pow k (z:A) 2 = ring_1 k") MP_TAC THENL [ASM_SIMP_TAC [RING_POW_2] THEN FIRST_X_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [(← SYM th)])) THEN ASM_SIMP_TAC [FIELD_MUL_LINV], ALL_TAC] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"2")] RING_ORDER_DIVIDES) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (MATCH_MP DIVIDES_LE)) THEN ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"~(c:A->A = I)") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE [I_THM]) THEN ASM_MESON_TAC [], ASM_REWRITE_TAC []] THEN SUBGOAL_THEN (← q r"ring_add k z (ring_inv k z) IN ring_carrier(k:A ring)") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_ADD], ALL_TAC] THEN SUBGOAL_THEN (← q r"!g. g IN group_carrier
              (galois_group (subfield_generated k {ring_0 k},k) I)
        ==> g(ring_add k z (ring_inv k z)) =
            ring_add k (g z) (ring_inv k (g z)) /\
            g z IN ring_carrier k /\ ~(g z = ring_0 (k:A ring))") (LABEL_TAC "conj") THENL [X_GEN_TAC (← q r"g:A->A") THEN DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP GALOIS_GROUP_RING_MONOMORPHISM)) THEN REPEAT CONJ_TAC THENL [FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_ADD th), RING_INV])) THEN AP_TERM_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"k:A ring"), (← q r"g:A->A")] FIELD_HOMOMORPHISM_INV) THEN ASM_SIMP_TAC [], ASM_MESON_TAC [GALOIS_GROUP_IN_CARRIER], DISCH_TAC THEN UNDISCH_TAC (← q r"~(z = ring_0 (k:A ring))") THEN REWRITE_TAC [] THEN UNDISCH_TAC (← q r"ring_monomorphism(k,k) (g:A->A)") THEN REWRITE_TAC [ring_monomorphism] THEN DISCH_THEN (MATCH_MP_TAC o CONJUNCT2) THEN ASM_SIMP_TAC [RING_0] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_0]], ALL_TAC] THEN SUBGOAL_THEN (← q r"(c:A->A)(ring_add k z (ring_inv k z)) = ring_add k z (ring_inv k z)") ASSUME_TAC THENL [USE_THEN "conj" (MP_TAC o (SPEC (← q r"c:A->A"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN DISCH_THEN (SUBST1_TAC o CONJUNCT1) THEN FIRST_ASSUM (SUBST1_TAC o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_eq z1)) then (do let z6 ← (q r"(c:A->A) z"); let z5 ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); liftExcept (lhand z3)); pure (z5 == z6)) else pure false)))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A")] RING_INV_INV) THEN ASM_SIMP_TAC [FIELD_UNIT] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN MATCH_MP_TAC RING_ADD_SYM THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!f. f IN group_carrier(galois_group
             (subfield_generated k {ring_add k z (ring_inv k z)},k) I) <=>
        f = I \/ f = (c:A->A)") ASSUME_TAC THENL [X_GEN_TAC (← q r"f:A->A") THEN REWRITE_TAC [(← MATCH_MP IN_GALOIS_GROUP_SUBFIELD_GENERATED (← ASSUME (← q r"field(k:A ring)"))), IN_SING, FORALL_UNWIND_THM2] THEN EQ_TAC THENL [STRIP_TAC THEN SUBGOAL_THEN (← q r"f IN group_carrier
              (galois_group (subfield_generated k {ring_0 k},k) (I:A->A))") ASSUME_TAC THENL [REWRITE_TAC [(← MATCH_MP IN_GALOIS_GROUP_SUBFIELD_GENERATED (← ASSUME (← q r"field(k:A ring)"))), IN_SING, FORALL_UNWIND_THM2] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC RING_HOMOMORPHISM_0 THEN UNDISCH_TAC (← q r"ring_automorphism k (f:A->A)") THEN SIMP_TAC [ring_automorphism, RING_ISOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN REMOVE_THEN "conj" (MP_TAC o (SPEC (← q r"f:A->A"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"(f:A->A) z"), (← q r"z:A")] FIELD_ADD_INV_EQ) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN TRANS_TAC EQ_TRANS (← q r"(f:A->A)(ring_add k z (ring_inv k z))") THEN CONJ_TAC THEN FIRST_ASSUM (fun th => tactic_of do pure (ACCEPT_TAC th ORELSE ACCEPT_TAC (← SYM th))), ALL_TAC] THEN STRIP_TAC THENL [DISJ1_TAC, DISJ2_TAC] THEN MATCH_MP_TAC CYCLOTOMIC_FIELD_GALOIS_GROUP_EQ THEN EXISTS_TAC (← q r"k:A ring") THEN EXISTS_TAC (← q r"z:A") THEN ASM_REWRITE_TAC [GALOIS_GROUP_I, I_THM], STRIP_TAC THEN ASM_REWRITE_TAC [] THENL [REWRITE_TAC [PERMUTES_I, RING_AUTOMORPHISM_I, I_THM], ALL_TAC] THEN CONJ_TAC THENL [MATCH_MP_TAC GALOIS_GROUP_PERMUTES THEN MAP_EVERY EXISTS_TAC [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}")] THEN ASM_REWRITE_TAC [], MATCH_MP_TAC GALOIS_GROUP_RING_AUTOMORPHISM THEN MAP_EVERY EXISTS_TAC [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}")] THEN ASM_REWRITE_TAC []]], ALL_TAC] THEN SUBGOAL_THEN (← q r"group_carrier(galois_group
      (subfield_generated k {ring_add k z (ring_inv k z)},k) I) =
    {I,c:A->A}") ASSUME_TAC THENL [ASM_REWRITE_TAC [EXTENSION, IN_INSERT, NOT_IN_EMPTY], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring")] FUNDAMENTAL_THEOREM_OF_GALOIS_THEORY) THEN ANTS_TAC THENL [CONJ_TAC THENL [ASM_MESON_TAC [number_field], MATCH_MP_TAC CYCLOTOMIC_FIELD_GALOIS_EXTENSION THEN MAP_EVERY EXISTS_TAC [(← q r"z:A"), (← q r"n:num")] THEN ASM_REWRITE_TAC []], ALL_TAC] THEN DISCH_THEN (fun th => tactic_of do pure ((← do let th2 ← (do pure (← CONJUNCT1 (← CONJUNCT2 th))); pure (← do let th5 ← (do pure (← CONJUNCT1 (← funpowM 4 CONJUNCT2 th))); pure (MP_TAC (← SPEC (← q r"ring_carrier(subfield_generated k                    {ring_add k z (ring_inv k (z:A))})") th2) THEN MP_TAC (← SPEC (← q r"ring_carrier(subfield_generated k                    {ring_add k z (ring_inv k (z:A))})") th5)))))) THEN REWRITE_TAC [SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED, IMAGE_I] THEN ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED_EQ, FIELD_SUBFIELD_GENERATED, PRIME_SUBFIELD_MINIMAL] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num")] CYCLOTOMIC_FIELD_GALOIS_GROUP_HAS_SIZE) THEN ASM_REWRITE_TAC [HAS_SIZE] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY, IN_INSERT, NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN REWRITE_TAC [EXTENSION, IN_FIXED_FIELD, IN_INSERT, NOT_IN_EMPTY] THEN MESON_TAC [I_THM], ASM_ARITH_TAC])

  let CYCLOTOMIC_FIELD_REAL_SUBFIELD_RING_OF_INTEGERS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!r u v z:A. u IN ring_carrier r /\ v IN ring_carrier r /\
                    z IN ring_carrier r
                    ==> ring_sub r (ring_add r u (ring_mul r v z)) u =
                        ring_mul r v z")
    let r2 ← TAUT (← q r"p ==> ~p ==> q")
    let r12 ← RING_RULE (← q r"!r u v u' v' z w t:A.
          u IN ring_carrier r /\ v IN ring_carrier r /\
          u' IN ring_carrier r /\ v' IN ring_carrier r /\
          z IN ring_carrier r /\ w IN ring_carrier r /\
          ring_mul r w z = ring_1 r /\ ring_add r z w = t
          ==> ring_mul r (ring_add r u (ring_mul r v z))
                         (ring_add r u' (ring_mul r v' z)) =
              ring_add r (ring_sub r (ring_mul r u u') (ring_mul r v v'))
                (ring_mul r (ring_add r (ring_add r (ring_mul r u v')
                                                    (ring_mul r v u'))
                                        (ring_mul r (ring_mul r v v') t))
                            z)")
    let r13 ← RING_RULE (← q r"!r u v u' v' z:A.
          u IN ring_carrier r /\ v IN ring_carrier r /\
          u' IN ring_carrier r /\ v' IN ring_carrier r /\
          z IN ring_carrier r
          ==> ring_add r (ring_add r u (ring_mul r v z))
                         (ring_add r u' (ring_mul r v' z)) =
              ring_add r (ring_add r u u') (ring_mul r (ring_add r v v') z)")
    let r14 ← RING_RULE (← q r"!r u v z:A. u IN ring_carrier r /\ v IN ring_carrier r /\
                    z IN ring_carrier r
                    ==> ring_neg r (ring_add r u (ring_mul r v z)) =
                        ring_add r (ring_neg r u)
                                   (ring_mul r (ring_neg r v) z)")
    let r15 ← ARITH_RULE (← q r"~(n = 0) ==> SUC(n - 1) = n")
    prove
      r"!(k:A ring) z n.
          number_field k /\ z IN ring_carrier k /\ ring_order k z = n /\
          2 < n /\ subfield_generated k {z} = k
          ==> ring_of_integers
                (subfield_generated k {ring_add k z (ring_inv k z)}) =
              subring_generated k {ring_add k z (ring_inv k z)}"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN (← q r"~((n:num) = 0) /\ ~(z = ring_0 (k:A ring))") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [ASM_ARITH_TAC, DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A")] RING_POW_RING_ORDER) THEN ASM_REWRITE_TAC [RING_POW_ZERO] THEN COND_CASES_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN ASM_MESON_TAC [FIELD_NONTRIVIAL], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num")] CYCLOTOMIC_FIELD_INVERSION_EXISTS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:A->A") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num"), (← q r"c:A->A")] CYCLOTOMIC_FIELD_REAL_SUBFIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ABBREV_TAC (← q r"t = ring_add k z (ring_inv k z):A") THEN SUBGOAL_THEN (← q r"(t:A) IN ring_carrier k /\ ring_inv k z IN ring_carrier k") STRIP_ASSUME_TAC THENL [EXPAND_TAC "t" THEN ASM_SIMP_TAC [RING_ADD, RING_INV], ALL_TAC] THEN SUBGOAL_THEN (← q r"~((z:A) IN ring_carrier(subfield_generated k {t}))") ASSUME_TAC THENL [ASM_REWRITE_TAC [IN_FIXED_FIELD, IN_SING, FORALL_UNWIND_THM2] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"2")] RING_ORDER_DIVIDES) THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ring_pow k (z:A) 2 = ring_1 k") (fun th => REWRITE_TAC [th]) THENL [ASM_SIMP_TAC [RING_POW_2] THEN FIRST_X_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [(← SYM th)])) THEN ASM_SIMP_TAC [FIELD_MUL_LINV], DISCH_THEN (MP_TAC o (MATCH_MP DIVIDES_LE)) THEN ASM_ARITH_TAC], ALL_TAC] THEN ABBREV_TAC (← q r"Zt = ring_carrier(subring_generated k {t:A})") THEN ABBREV_TAC (← q r"Zz = ring_carrier(subring_generated k {z:A})") THEN SUBGOAL_THEN (← q r"Zt SUBSET ring_carrier(k:A ring) /\ (t:A) IN Zt") STRIP_ASSUME_TAC THENL [EXPAND_TAC "Zt" THEN REWRITE_TAC [RING_CARRIER_SUBRING_GENERATED_SUBSET] THEN MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN ASM_REWRITE_TAC [IN_SING], ALL_TAC] THEN SUBGOAL_THEN (← q r"(!u v. u IN Zt /\ v IN Zt
             ==> ring_add k u v IN Zt /\ ring_mul k u v IN Zt /\
                 ring_sub k u v IN Zt) /\
      (!u. u IN Zt ==> ring_neg k u IN Zt) /\
      ring_0 k IN Zt /\ ring_1 k IN (Zt:A->bool)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "Zt" THEN SIMP_TAC [RING_ADD_IN_SUBRING_GENERATED, RING_MUL_IN_SUBRING_GENERATED, RING_NEG_IN_SUBRING_GENERATED, RING_0_IN_SUBRING_GENERATED, RING_1_IN_SUBRING_GENERATED, ring_sub], ALL_TAC] THEN SUBGOAL_THEN (← q r"(Zt:A->bool) SUBSET Zz") ASSUME_TAC THENL [EXPAND_TAC "Zt" THEN MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN EXPAND_TAC "Zz" THEN REWRITE_TAC [SUBRING_SUBRING_GENERATED, SING_SUBSET] THEN EXPAND_TAC "t" THEN MATCH_MP_TAC RING_ADD_IN_SUBRING_GENERATED THEN CONJ_TAC THENL [MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN ASM_REWRITE_TAC [IN_SING], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_inv k z = ring_pow k (z:A) (n - 1)") SUBST1_TAC THENL [MATCH_MP_TAC RING_RINV_UNIQUE THEN ASM_SIMP_TAC [RING_POW] THEN REWRITE_TAC [(← GSYM (← CONJUNCT2 ring_pow))] THEN ASM_SIMP_TAC [r15] THEN ASM_MESON_TAC [RING_POW_RING_ORDER], MATCH_MP_TAC RING_POW_IN_SUBRING_GENERATED THEN MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN ASM_REWRITE_TAC [IN_SING]], ALL_TAC] THEN SUBGOAL_THEN (← q r"(Zt:A->bool) SUBSET ring_carrier(subfield_generated k {t})") ASSUME_TAC THENL [EXPAND_TAC "Zt" THEN REWRITE_TAC [SUBRING_SUBSET_SUBFIELD_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x. x IN Zz ==> ?u v. u IN Zt /\ v IN Zt /\
                            x = ring_add k u (ring_mul k v (z:A))") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"Zz SUBSET {x | ?u v. u IN Zt /\ v IN Zt /\
                             x = ring_add k u (ring_mul k v (z:A))}") (fun th => MP_TAC th THEN SET_TAC []) THEN EXPAND_TAC "Zz" THEN MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN REWRITE_TAC [SING_SUBSET, IN_ELIM_THM] THEN CONJ_TAC THENL [MAP_EVERY EXISTS_TAC [(← q r"ring_0 k:A"), (← q r"ring_1 k:A")] THEN ASM_SIMP_TAC [RING_ADD_LZERO, RING_MUL_LID, RING_MUL] THEN ASM_MESON_TAC [], ALL_TAC] THEN REWRITE_TAC [subring_of, SUBSET, IN_ELIM_THM] THEN SUBGOAL_THEN (← q r"!x:A. x IN Zt ==> x IN ring_carrier k") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN REPEAT CONJ_TAC THENL [REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"u:A"), (← q r"v:A")] THEN STRIP_TAC THEN ASM_SIMP_TAC [RING_ADD, RING_MUL], MAP_EVERY EXISTS_TAC [(← q r"ring_0 k:A"), (← q r"ring_0 k:A")] THEN ASM_SIMP_TAC [RING_MUL_LZERO, RING_ADD_LZERO, RING_0] THEN ASM_MESON_TAC [], MAP_EVERY EXISTS_TAC [(← q r"ring_1 k:A"), (← q r"ring_0 k:A")] THEN ASM_SIMP_TAC [RING_MUL_LZERO, RING_ADD_RZERO, RING_1] THEN ASM_MESON_TAC [], REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"u:A"), (← q r"v:A")] THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"ring_neg k u:A"), (← q r"ring_neg k v:A")] THEN ASM_SIMP_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"u:A"), (← q r"v:A"), (← q r"z:A")] r14) THEN ASM_SIMP_TAC [], MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"y:A")] THEN DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"u:A") (X_CHOOSE_THEN (← q r"v:A") STRIP_ASSUME_TAC)) (X_CHOOSE_THEN (← q r"u':A") (X_CHOOSE_THEN (← q r"v':A") STRIP_ASSUME_TAC))) THEN ASM_REWRITE_TAC [] THEN MAP_EVERY EXISTS_TAC [(← q r"ring_add k u u':A"), (← q r"ring_add k v v':A")] THEN ASM_SIMP_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"u:A"), (← q r"v:A"), (← q r"u':A"), (← q r"v':A"), (← q r"z:A")] r13) THEN ASM_SIMP_TAC [], MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"y:A")] THEN DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"u:A") (X_CHOOSE_THEN (← q r"v:A") STRIP_ASSUME_TAC)) (X_CHOOSE_THEN (← q r"u':A") (X_CHOOSE_THEN (← q r"v':A") STRIP_ASSUME_TAC))) THEN ASM_REWRITE_TAC [] THEN MAP_EVERY EXISTS_TAC [(← q r"ring_sub k (ring_mul k u u') (ring_mul k v v'):A"), (← q r"ring_add k (ring_add k (ring_mul k u v') (ring_mul k v u'))
                      (ring_mul k (ring_mul k v v') t):A")] THEN ASM_SIMP_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"u:A"), (← q r"v:A"), (← q r"u':A"), (← q r"v':A"), (← q r"z:A"), (← q r"ring_inv k z:A"), (← q r"t:A")] r12) THEN ASM_SIMP_TAC [FIELD_MUL_LINV]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num")] CYCLOTOMIC_FIELD_RING_OF_INTEGERS) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_carrier(ring_of_integers(subfield_generated k {t:A})) = Zt") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"subfield_generated k {t:A}"), (← q r"k:A ring"), (← q r"I:A->A")] RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE_EQ) THEN ANTS_TAC THENL [REWRITE_TAC [ring_monomorphism, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, I_THM] THEN MESON_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN ASM_REWRITE_TAC [I_THM] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:A") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"x:A")) o (checkM (fun th => (do if ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); pure (is_forall z3)) then (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); canM (fun z7 => (do let z8 ← (pure z7); find_termM (fun z9 => (do let z11 ← (pure z9); let z10 ← (q r"Zz:A->bool"); pure (z10 == z11))) z8)) z5) else pure false))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"u:A") (X_CHOOSE_THEN (← q r"v:A") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)))) THEN SUBGOAL_THEN (← q r"(u:A) IN ring_carrier k /\ (v:A) IN ring_carrier k /\
        (u:A) IN ring_carrier(subfield_generated k {t}) /\
        (v:A) IN ring_carrier(subfield_generated k {t})") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN ASM_CASES_TAC (← q r"v = ring_0 (k:A ring)") THENL [ASM_SIMP_TAC [RING_MUL_LZERO, RING_ADD_RZERO], ALL_TAC] THEN UNDISCH_TAC (← q r"~((z:A) IN ring_carrier(subfield_generated k {t}))") THEN MATCH_MP_TAC r2 THEN SUBGOAL_THEN (← q r"z = ring_div k (ring_sub k (ring_add k u (ring_mul k v z)) u) (v:A)") SUBST1_TAC THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FIELD_DIV_EQ_MUL THEN ASM_SIMP_TAC [RING_SUB, RING_ADD, RING_MUL] THEN MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MATCH_MP_TAC RING_DIV_IN_SUBFIELD_GENERATED THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED] THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {t:A}"), (← q r"ring_add k u (ring_mul k v z):A"), (← q r"u:A")] RING_SUB) THEN ASM_REWRITE_TAC [RING_SUB_SUBFIELD_GENERATED], ALL_TAC] THEN REWRITE_TAC [RINGS_EQ] THEN ASM_REWRITE_TAC [RING_OF_INTEGERS, (← CONJUNCT2 SUBFIELD_GENERATED), (← CONJUNCT2 SUBRING_GENERATED)])

  -- @@RETURN BEGIN
  return { CYCLOTOMIC_SUBFIELD_COMPOSITUM, CYCLOTOMIC_SUBFIELD_DEGREE,
           CYCLOTOMIC_SUBFIELD_INTER, CYCLOTOMIC_FIELD_SUBFIELD_UNIQUE,
           CYCLOTOMIC_FIELD_INVERSION_EXISTS, CYCLOTOMIC_FIELD_REAL_SUBFIELD,
           CYCLOTOMIC_FIELD_REAL_SUBFIELD_RING_OF_INTEGERS }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- cyclotomic_subfields.ml phrases from line 780 to 858                   -/
/- ---------------------------------------------------------------------- -/

structure CyclotomicSubfields02 where
  -- @@FIELDS
  CYCLOTOMIC_UNIT : thm
  ROOT_OF_UNITY_ONE_SUB_UNIT : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupCyclotomicSubfields02 [HolBase] (D : CyclotomicSubfieldsDeps) :
    ExceptT String IO CyclotomicSubfields02 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, NUMBER_RULE, SET_TAC, .. } := D
  let { CONG_SOLVE, COPRIME_0, COPRIME_1, CYCLOTOMIC_POLY_EVAL_1,
        CYCLOTOMIC_POLY_SPLITS, DIVIDES_LE, DIVIDES_LMUL, DIVIDES_REFL, DIVIDES_REXP,
        DIVIDES_RMUL, EXP, FIELD_DIV_EQ_MUL, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_NONTRIVIAL, FINITE_NUMSEG_LT, FINITE_SUBSET, INTEGRAL_DOMAIN_ASSOCIATES,
        INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING, INTEGRAL_DOMAIN_REGULAR,
        INTEGRAL_DOMAIN_RING_OF_INTEGERS, IN_ELIM_THM, LEFT_IMP_EXISTS_THM,
        MEMBER_NOT_EMPTY, MULT_CLAUSES, NOT_EXISTS_THM, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q, POLY_EVAL_CONST, POLY_EVAL_RING_PRODUCT,
        POLY_EVAL_SUB, POLY_EVAL_VAR, PRIMEPOW_FACTOR, PRIME_1, PRIME_2, PRIME_FACTOR,
        PRIME_GE_2, RING_0, .. } := D.core1
  let { RING_1, RING_ASSOCIATES_PRIME_POWER_ORDER, RING_ASSOCIATES_UNIT,
        RING_DIVIDES_SUB_POW, RING_OF_INTEGERS, RING_OF_INTEGERS_SUBSET, RING_ORDER_1,
        RING_ORDER_EQ_1, RING_ORDER_SUBRING_GENERATED, RING_POLYNOMIAL,
        RING_POLYNOMIAL_CONST, RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_VAR, RING_POW,
        RING_POW_1, RING_POW_EQ, RING_POW_ONE, RING_POW_POW, RING_POW_RING_ORDER,
        RING_POW_ZERO, RING_PRODUCT, RING_PRODUCT_DELETE, RING_PRODUCT_EQ,
        RING_PRODUCT_RING_OF_INTEGERS, RING_SUB, RING_SUB_EQ_0, RING_SUB_REFL,
        RING_UNIT_0, RING_UNIT_NOT_IN_PRIME_IDEAL, RING_UNIT_POW,
        ROOT_OF_UNITY_IN_RING_OF_INTEGERS, SUBSET, coprime, ring_associates,
        ring_of_integers, ring_unit, .. } := D.core2
  -- @@SCOPE END

  let CYCLOTOMIC_UNIT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"2 <= n ==> ~(n = 0)")
    prove
      r"!(k:A ring) z n a.
          number_field k /\ z IN ring_carrier k /\ ring_order k z = n /\
          2 <= n /\ coprime(a,n)
          ==> ring_associates (ring_of_integers k)
                (ring_sub k (ring_1 k) z)
                (ring_sub k (ring_1 k) (ring_pow k z a)) /\
              ring_unit (ring_of_integers k)
                (ring_div k (ring_sub k (ring_1 k) (ring_pow k z a))
                            (ring_sub k (ring_1 k) z))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP INTEGRAL_DOMAIN_RING_OF_INTEGERS)) THEN SUBGOAL_THEN (← q r"(z:A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [MATCH_MP_TAC ROOT_OF_UNITY_IN_RING_OF_INTEGERS THEN EXISTS_TAC (← q r"n:num") THEN ASM_SIMP_TAC [r1] THEN ASM_MESON_TAC [RING_POW_RING_ORDER], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(z = ring_1 (k:A ring)) /\ ~(z = ring_0 k)") STRIP_ASSUME_TAC THENL [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL [RULE_ASSUM_TAC (REWRITE_RULE [RING_ORDER_1]) THEN ASM_ARITH_TAC, MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_0 k:A")] RING_POW_RING_ORDER) THEN ASM_REWRITE_TAC [RING_POW_ZERO, RING_0] THEN COND_CASES_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN ASM_MESON_TAC [FIELD_NONTRIVIAL]], ALL_TAC] THEN SUBGOAL_THEN (← q r"~((a:num) = 0)") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE [COPRIME_0]) THEN ASM_ARITH_TAC, ALL_TAC] THEN MP_TAC (← SPECL [(← q r"a:num"), (← q r"1"), (← q r"n:num")] CONG_SOLVE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"b:num")) THEN SUBGOAL_THEN (← q r"~((b:num) = 0)") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE [MULT_CLAUSES, (← ExceptT.mk (NUMBER_RULE (← q r"(0 == 1) (mod n) <=> n = 1")))]) THEN ASM_ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_1) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"z:A")] RING_POW) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN REPEAT DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_associates (ring_of_integers k)
        (ring_sub k (ring_1 k) z)
        (ring_sub (k:A ring) (ring_1 k) (ring_pow k z a))") ASSUME_TAC THENL [REWRITE_TAC [ring_associates] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_1 k:A"), (← q r"z:A"), (← q r"a:num")] RING_DIVIDES_SUB_POW) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS, RING_POW_ONE], SUBGOAL_THEN (← q r"ring_pow k (ring_pow k (z:A) a) b = z") MP_TAC THENL [ASM_SIMP_TAC [RING_POW_POW] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"a * b:num"), (← q r"1")] RING_POW_EQ) THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_REGULAR, FIELD_IMP_INTEGRAL_DOMAIN, RING_POW_1], DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_1 k:A"), (← q r"ring_pow k z a:A"), (← q r"b:num")] RING_DIVIDES_SUB_POW) THEN ASM_SIMP_TAC [RING_OF_INTEGERS, RING_POW_ONE]], ASM_REWRITE_TAC []] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_sub k (ring_1 k) (z:A)"), (← q r"ring_sub k (ring_1 k) (ring_pow k z a):A")] INTEGRAL_DOMAIN_ASSOCIATES) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"u:A") STRIP_ASSUME_TAC))) THEN SUBGOAL_THEN (← q r"(u:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [ring_unit, RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_div k (ring_sub k (ring_1 k) (ring_pow k z a))
                 (ring_sub k (ring_1 k) z) = (u:A)") (fun th => ASM_REWRITE_TAC [th]) THEN MATCH_MP_TAC FIELD_DIV_EQ_MUL THEN ASM_SIMP_TAC [RING_SUB, RING_1, RING_POW, RING_SUB_EQ_0] THEN ASM_MESON_TAC [])

  let ROOT_OF_UNITY_ONE_SUB_UNIT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"1 <= e ==> ~(e = 0)")
    prove
      r"!(k:A ring) z n.
          number_field k /\ z IN ring_carrier k /\ ring_order k z = n /\
          ~(n = 0)
          ==> (ring_unit (ring_of_integers k) (ring_sub k (ring_1 k) z) <=>
               ~(?p j. prime p /\ n = p EXP j))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP INTEGRAL_DOMAIN_RING_OF_INTEGERS)) THEN SUBGOAL_THEN (← q r"(z:A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [MATCH_MP_TAC ROOT_OF_UNITY_IN_RING_OF_INTEGERS THEN EXISTS_TAC (← q r"n:num") THEN ASM_MESON_TAC [RING_POW_RING_ORDER], ALL_TAC] THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_1) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"z:A")] RING_POW) THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_SUB) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN REPEAT DISCH_TAC THEN EQ_TAC THENL [DISCH_TAC THEN REWRITE_TAC [NOT_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"p:num"), (← q r"j:num")] THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"j = 0") THENL [UNDISCH_TAC (← q r"ring_unit (ring_of_integers k) (ring_sub k (ring_1 k) (z:A))") THEN SUBGOAL_THEN (← q r"z = ring_1 (k:A ring)") SUBST1_TAC THENL [ASM_SIMP_TAC [(← GSYM RING_ORDER_EQ_1)] THEN ASM_REWRITE_TAC [EXP], ASM_SIMP_TAC [RING_SUB_REFL, RING_1]] THEN SUBGOAL_THEN (← q r"ring_0 k = ring_0 (ring_of_integers (k:A ring))") SUBST1_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN REWRITE_TAC [RING_UNIT_0] THEN ASM_MESON_TAC [INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_order (ring_of_integers k) (z:A) = n") ASSUME_TAC THENL [UNDISCH_TAC (← q r"(z:A) IN ring_carrier(ring_of_integers k)") THEN REWRITE_TAC [ring_of_integers] THEN SIMP_TAC [RING_ORDER_SUBRING_GENERATED] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_unit (ring_of_integers k) (ring_of_num k p:A)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"z:A"), (← q r"p:num"), (← q r"j:num")] RING_ASSOCIATES_PRIME_POWER_ORDER) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (MATCH_MP RING_ASSOCIATES_UNIT)) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_sub (ring_of_integers k)
                          (ring_1 (ring_of_integers k)) (z:A)"), (← q r"phi(p EXP j)")] RING_UNIT_POW) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"p:num")] NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q) THEN ASM_REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY), IN_ELIM_THM] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"P:A->bool") STRIP_ASSUME_TAC) o (CONJUNCT1 o CONJUNCT2)) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"ring_of_num k p:A")] RING_UNIT_NOT_IN_PRIME_IDEAL) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN REWRITE_TAC [NOT_EXISTS_THM] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"?p q. prime p /\ prime q /\ ~(p = q) /\
                        p divides n /\ q divides n") STRIP_ASSUME_TAC THENL [ASM_CASES_TAC (← q r"n = 1") THENL [FIRST_X_ASSUM (MP_TAC o (SPECL [(← q r"2"), (← q r"0")])) THEN ASM_REWRITE_TAC [PRIME_2, EXP], ALL_TAC] THEN MP_TAC (← SPEC (← q r"n:num") PRIMEPOW_FACTOR) THEN ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"p:num"), (← q r"e:num"), (← q r"m:num")] THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"m = 1") THENL [FIRST_X_ASSUM (MP_TAC o (SPECL [(← q r"p:num"), (← q r"e:num")])) THEN ASM_REWRITE_TAC [MULT_CLAUSES], ALL_TAC] THEN MP_TAC (← SPEC (← q r"m:num") PRIME_FACTOR) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"q:num") STRIP_ASSUME_TAC) THEN MAP_EVERY EXISTS_TAC [(← q r"p:num"), (← q r"q:num")] THEN ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"coprime(q:num,m)") THEN REWRITE_TAC [coprime] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"q:num"))) THEN ASM_REWRITE_TAC [DIVIDES_REFL] THEN ASM_MESON_TAC [PRIME_1], MATCH_MP_TAC DIVIDES_RMUL THEN MATCH_MP_TAC DIVIDES_REXP THEN ASM_SIMP_TAC [DIVIDES_REFL, r1], ASM_MESON_TAC [DIVIDES_LMUL]], ALL_TAC] THEN ABBREV_TAC (← q r"U = {j | j < (n:num) /\ coprime(j,n)}") THEN SUBGOAL_THEN (← q r"FINITE(U:num->bool) /\ 1 IN U") STRIP_ASSUME_TAC THENL [EXPAND_TAC "U" THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{j:num | j < n}") THEN REWRITE_TAC [FINITE_NUMSEG_LT] THEN SET_TAC [], REWRITE_TAC [IN_ELIM_THM, COPRIME_1] THEN MP_TAC (← SPECL [(← q r"p:num"), (← q r"n:num")] DIVIDES_LE) THEN MP_TAC (← SPECL [(← q r"q:num"), (← q r"n:num")] DIVIDES_LE) THEN ASM_REWRITE_TAC [] THEN MP_TAC (← SPEC (← q r"p:num") PRIME_GE_2) THEN MP_TAC (← SPEC (← q r"q:num") PRIME_GE_2) THEN ASM_REWRITE_TAC [] THEN ARITH_TAC], ALL_TAC] THEN SUBGOAL_THEN (← q r"!j. ring_sub k (ring_1 k) (ring_pow k z j) IN
          ring_carrier(ring_of_integers (k:A ring))") ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_product k U (\j. ring_sub k (ring_1 k) (ring_pow k (z:A) j)) =
      ring_1 k") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"p:num"), (← q r"q:num")] CYCLOTOMIC_POLY_EVAL_1) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [(← SYM th)])) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num")] CYCLOTOMIC_POLY_SPLITS) THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN] THEN DISCH_THEN SUBST1_TAC THEN wPart rand (lhand o rand) POLY_EVAL_RING_PRODUCT THEN ANTS_TAC THENL [ASM_SIMP_TAC [(← GSYM RING_POLYNOMIAL), RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_CONST, RING_POW, RING_1], DISCH_THEN SUBST1_TAC] THEN MATCH_MP_TAC RING_PRODUCT_EQ THEN ASM_SIMP_TAC [POLY_EVAL_SUB, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_CONST, RING_POW, POLY_EVAL_VAR, POLY_EVAL_CONST, RING_1], ALL_TAC] THEN REWRITE_TAC [ring_unit] THEN CONJ_TAC THENL [MP_TAC (← ISPEC (← q r"1") (← ASSUME (← q r"!j. ring_sub k (ring_1 k) (ring_pow k z j) IN
                            ring_carrier(ring_of_integers (k:A ring))"))) THEN ASM_SIMP_TAC [RING_POW_1], ALL_TAC] THEN EXISTS_TAC (← q r"ring_product k (U DELETE 1)
        (\j. ring_sub k (ring_1 k) (ring_pow k (z:A) j))") THEN SUBGOAL_THEN (← q r"ring_product k (U DELETE 1)
        (\j. ring_sub k (ring_1 k) (ring_pow k (z:A) j)) =
      ring_product (ring_of_integers k) (U DELETE 1)
        (\j. ring_sub k (ring_1 k) (ring_pow k (z:A) j))") SUBST1_TAC THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_PRODUCT_RING_OF_INTEGERS THEN ASM_REWRITE_TAC [], REWRITE_TAC [RING_PRODUCT]] THEN SIMP_TAC [RING_PRODUCT_RING_OF_INTEGERS, (← ASSUME (← q r"!j. ring_sub k (ring_1 k) (ring_pow k z j) IN
          ring_carrier(ring_of_integers (k:A ring))"))] THEN REWRITE_TAC [RING_OF_INTEGERS] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"\j. ring_sub k (ring_1 k) (ring_pow k (z:A) j)"), (← q r"U:num->bool"), (← q r"1")] RING_PRODUCT_DELETE) THEN ASM_SIMP_TAC [RING_POW_1, RING_SUB, RING_1])

  -- @@RETURN BEGIN
  return { CYCLOTOMIC_UNIT, ROOT_OF_UNITY_ONE_SUB_UNIT }
  -- @@RETURN END

end HolANT.CyclotomicSubfields
