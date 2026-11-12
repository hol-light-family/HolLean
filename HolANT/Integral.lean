/- ========================================================================= -/
/- ANT: Integral elements of ring extensions, integral closure and ...     -/
/- ========================================================================= -/
/- File: HolANT/Integral.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/integral.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antintegraldiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.Integral fills them).

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

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude

namespace HolANT.Integral

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ALGEBRAIC_OVER_IN_CARRIER ALGEBRA_NORM_1 ALGEBRA_NORM_MINIMAL_POLYNOMIAL
   ALGEBRA_NORM_MUL ALGEBRA_TRACE_MINIMAL_POLYNOMIAL ARITH
   CARRIER_SUBRING_GENERATED_SUBRING COEFF COEFF_COMPOSE COEFF_IN_CARRIER_ALT
   EMPTY_GSPEC EQ_IMP EQ_TRANS EXTENSION_DEGREE_EQ_0
   FIELD_EXTENSION_IMP_HOMOMORPHISM FIELD_EXTENSION_SUBFIELD_GENERATED
   FIELD_IMP_INTEGRAL_DOMAIN FIELD_IMP_NONTRIVIAL_RING FIELD_IMP_PID
   FIELD_MUL_LINV FIELD_MUL_RINV FIELD_OF_FRACTIONS_IMP_INTEGRAL_DOMAIN
   FIELD_REGULAR FIELD_SUBFIELD_GENERATED FIELD_UNIT FINITE_EMPTY
   FINITE_EXTENSION_SUBFIELD_GENERATED FINITE_IMAGE FINITE_IMP_FIELD_EXTENSION
   FINITE_INDUCT_STRONG FINITE_INSERT FINITE_NUMSEG FINITE_NUMSEG_LT
   FINITE_PRODUCT_DEPENDENT FINITE_SING FORALL_AND_THM FORALL_IN_GSPEC
   FORALL_IN_IMAGE FORALL_IN_INSERT FUN_EQ_THM IDEAL_GENERATED_ADJOIN_EXPLICIT
   IDEAL_GENERATED_INC IMP_CONJ INSERT_SUBSET INTEGER_RING
   INTEGRAL_DOMAIN_LOCALIZATION INTEGRAL_DOMAIN_MUL_EQ_0
   INTEGRAL_DOMAIN_POW_EQ_0 INTEGRAL_DOMAIN_REGULAR
   INTEGRAL_DOMAIN_SUBRING_GENERATED IN_ELIM_THM IN_IMAGE IN_INSERT IN_NUMSEG
   IN_RING_IDEAL_LMUL IN_RING_POLYNOMIAL_CARRIER_COMPOSE IN_SING IN_SUBRING_1
   IN_SUBRING_ADD IN_SUBRING_MUL IN_SUBRING_NEG IN_SUBRING_NUM IN_SUBRING_POW
   IN_SUBRING_SUM IN_UNIV IRREDUCIBLE_IMP_POLY_DEG_NZ I_DEF I_O_ID I_THM
   LEFT_AND_EXISTS_THM LEFT_IMP_EXISTS_THM LE_1 LOCALEQUIV_MUL_LCANCEL
   LOCALEQUIV_MUL_RCANCEL LT LT_0 MINIMAL_POLYNOMIAL MINIMAL_POLYNOMIAL_DIVIDES
   MINIMAL_POLYNOMIAL_IN_CARRIER MINIMAL_POLYNOMIAL_MONIC
   MONIC_HOMOMORPHIC_IMAGE MONIC_IMP_NONZERO MONIC_X_MINUS_A MONO_EXISTS
   NOT_IN_EMPTY NOT_SUC NUMSEG_LT PID_IMP_UFD POLY_DEG_MONOMORPHIC_IMAGE
   POLY_EVAL POLY_EVAL_MUL POLY_EXTEND POLY_EXTEND_CONST POLY_EXTEND_EVALUATE
   POLY_EXTEND_HOMOMORPHIC_IMAGE POLY_EXTEND_INTO_SUBRING_GENERATED
   POLY_EXTEND_MONIC_UNIVARIATE POLY_EXTEND_SUB POLY_EXTEND_VAR
   POLY_MONOMIAL_IN_CARRIER POLY_RING_CLAUSES POLY_SPLITS_IN_CARRIER
   POLY_SPLITS_IN_SUBRING_MONIC RIGHT_AND_EXISTS_THM RIGHT_FORALL_IMP_THM
   RIGHT_IMP_EXISTS_THM RING_0 RING_1 RING_ADD RING_ADD_LDISTRIB
   RING_ADD_RDISTRIB RING_ADD_RNEG RING_ADD_RZERO RING_ASSOCIATES_DIVIDES
   RING_ASSOCIATES_EQ_0 RING_ASSOCIATES_LMUL RING_ASSOCIATES_SYM
   RING_ASSOCIATES_TRANS RING_CARRIER_SUBRING_GENERATED_0 RING_CHARPOLY
   RING_CHARPOLY_EXTEND RING_CHARPOLY_MONIC RING_DET
   RING_DET_DEPENDENT_COLUMNS_MUL RING_DIVIDES_0 RING_DIVIDES_ADD
   RING_DIVIDES_HOMOMORPHIC_IMAGE RING_DIVIDES_LMUL : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (RING_DIVIDES_LMUL2 RING_DIVIDES_NEG RING_DIVIDES_REFL RING_DIVIDES_RMUL
   RING_DIVIDES_ZERO RING_FRACTIONATE_IN_CARRIER RING_HOMOMORPHISM_0
   RING_HOMOMORPHISM_1 RING_HOMOMORPHISM_ADD RING_HOMOMORPHISM_COMPOSE
   RING_HOMOMORPHISM_FRACTIONATE RING_HOMOMORPHISM_INCLUSION
   RING_HOMOMORPHISM_INTEGER_RING_OF_INT RING_HOMOMORPHISM_INTO_SUBRING_EQ
   RING_HOMOMORPHISM_IN_CARRIER RING_HOMOMORPHISM_MUL RING_HOMOMORPHISM_NEG
   RING_HOMOMORPHISM_POLY_RINGS RING_HOMOMORPHISM_POW RING_HOMOMORPHISM_SUM
   RING_IDEAL_CARRIER RING_IDEAL_IDEAL_GENERATED RING_INV
   RING_LOCALEQUIV_IN_CARRIER RING_LOCALIZATION_CARRIER
   RING_MONIC_RELATION_FACTOR RING_MONOMORPHISM_ALT RING_MONOMORPHISM_EQ_0
   RING_MONOMORPHISM_FRACTIONATE RING_MONOMORPHISM_FRACTIONATE_GEN
   RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_MONOMORPHISM_INTEGER_RING_OF_INT
   RING_MUL RING_MULTSYS RING_MULTSYS_REGULAR RING_MUL_ASSOC RING_MUL_LID
   RING_MUL_LINV RING_MUL_LNEG RING_MUL_LZERO RING_MUL_POW RING_MUL_RID
   RING_MUL_RNEG RING_MUL_RZERO RING_MUL_SYM RING_NEG
   RING_NEG_IN_SUBRING_GENERATED RING_OF_INT RING_POLYNOMIAL
   RING_POLYNOMIAL_CONST RING_POLYNOMIAL_SUB RING_POLYNOMIAL_VAR RING_POW
   RING_POW_ADD RING_POW_ONE RING_POW_ZERO RING_PRIME_DIVIDES_POW
   RING_REGULAR_IN_CARRIER RING_REGULAR_POW RING_RNEG_UNIQUE RING_SPAN_0
   RING_SPAN_ADD RING_SPAN_FINITE RING_SPAN_INC RING_SPAN_MUL RING_SPAN_NEG
   RING_SPAN_SUBSET RING_SPAN_SUM RING_SUB RING_SUB_EQ_0 RING_SUB_LDISTRIB
   RING_SUB_RDISTRIB RING_SUB_REFL RING_SUM RING_SUM_CLAUSES RING_SUM_CLOSED
   RING_SUM_DELTA RING_SUM_EQ RING_SUM_EQ_0 RING_SUM_LMUL RING_SUM_NEG
   RING_SUM_REFLECT RING_SUM_SUB RING_UNIT_1 RING_UNIT_DIVIDES_ANY
   RING_UNIT_FRACTIONATE RING_UNIT_IMP_REGULAR RING_UNIT_IN_CARRIER
   RING_UNIT_MUL_EQ RING_UNIT_NEG RING_UNIT_POW RING_UNIT_POW_EQ SING_SUBSET
   SKOLEM_THM SPLITTING_EXTENSION_EXISTS_BIGENOUGH SPLITTING_EXTENSION_SPLITS
   SPLITTING_IMP_FIELD_EXTENSION SUBFIELD_GENERATED_QUOTIENTS SUBRING_GENERATED
   SUBRING_GENERATED_INC_GEN SUBSET SUB_0 SUC_SUB1 UFD_IMP_INTEGRAL_DOMAIN
   UFD_INTEGER_RING UFD_PRIME_FACTOR_INDUCT algebraic_over field_extension
   field_of_fractions fraction_ring monic o_ASSOC o_THM poly_eval
   poly_splits_over ring_div ring_divides ring_monomorphism ring_multsys
   ring_pow ring_prime ring_regular ring_span_INDUCT ring_sub ring_unit
   ring_zerodivisor subring_of : thm)
  deriving Inhabited

/-- What integral.ml uses from Session besides theorems. -/
structure IntegralDeps where
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
/- integral.ml phrases from line 82 to 796                                -/
/- ---------------------------------------------------------------------- -/

structure Integral01 where
  -- @@FIELDS
  integral_element : thm
  integrally_closed : thm
  INTEGRAL_ELEMENT_IN_CARRIER : thm
  INTEGRAL_ELEMENT_IMAGE : thm
  INTEGRAL_ELEMENT_0 : thm
  INTEGRAL_ELEMENT_1 : thm
  INTEGRAL_ELEMENT_RELATION : thm
  INTEGRAL_ELEMENT_FINITE_MODULE : thm
  INTEGRAL_ELEMENT_MODULE : thm
  INTEGRAL_SPAN_LMUL : thm
  INTEGRAL_ELEMENT_SPAN : thm
  INTEGRAL_SPAN_ADJOIN : thm
  INTEGRAL_ELEMENT_FROM_RELATION : thm
  INTEGRAL_ELEMENT_OVER_SUBRING : thm
  INTEGRAL_SPAN_FINITE_SET : thm
  INTEGRAL_ELEMENT_EXPLICIT : thm
  INTEGRAL_ELEMENT_ADD : thm
  INTEGRAL_ELEMENT_MUL : thm
  INTEGRAL_ELEMENT_NEG : thm
  INTEGRAL_ELEMENT_SUB : thm
  INTEGRAL_ELEMENT_POW : thm
  INTEGRAL_CLOSURE_SUBRING : thm
  INTEGRAL_CLOSURE_SUPSET_IMAGE : thm
  INTEGRAL_ELEMENT_HOMOMORPHIC_IMAGE : thm
  INTEGRAL_ELEMENT_MONOMORPHIC_PREIMAGE : thm
  INTEGRAL_ELEMENT_SUBRING_GENERATED : thm
  INTEGRAL_ELEMENT_TRANS : thm
  INTEGRAL_CLOSURE_IDEMPOT : thm
  INTEGRAL_OVER_FIELD_EQ_ALGEBRAIC : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupIntegral01 [HolBase] (D : IntegralDeps) :
    ExceptT String IO Integral01 := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON, MESON_TAC, RING_RULE, SET_TAC,
        new_definition, .. } := D
  let { ALGEBRAIC_OVER_IN_CARRIER, ARITH, CARRIER_SUBRING_GENERATED_SUBRING,
        COEFF_IN_CARRIER_ALT, EMPTY_GSPEC, EQ_TRANS, FIELD_IMP_NONTRIVIAL_RING,
        FINITE_EMPTY, FINITE_IMAGE, FINITE_INDUCT_STRONG, FINITE_INSERT,
        FINITE_NUMSEG_LT, FINITE_PRODUCT_DEPENDENT, FINITE_SING, FORALL_IN_GSPEC,
        FORALL_IN_IMAGE, FORALL_IN_INSERT, FUN_EQ_THM, IMP_CONJ, IN_ELIM_THM, IN_SING,
        IN_UNIV, I_DEF, I_O_ID, I_THM, LEFT_IMP_EXISTS_THM, LE_1, LT,
        MINIMAL_POLYNOMIAL, MONIC_IMP_NONZERO, MONIC_X_MINUS_A, MONO_EXISTS,
        NOT_IN_EMPTY, POLY_EXTEND, POLY_EXTEND_CONST, POLY_EXTEND_HOMOMORPHIC_IMAGE,
        POLY_EXTEND_INTO_SUBRING_GENERATED, POLY_EXTEND_MONIC_UNIVARIATE,
        POLY_EXTEND_SUB, POLY_EXTEND_VAR, POLY_RING_CLAUSES, RIGHT_IMP_EXISTS_THM,
        RING_0, RING_1, RING_ADD, RING_ADD_LDISTRIB, RING_ADD_RDISTRIB, RING_ADD_RZERO,
        RING_CHARPOLY, RING_CHARPOLY_EXTEND, RING_CHARPOLY_MONIC, RING_DET,
        RING_DET_DEPENDENT_COLUMNS_MUL, .. } := D.core1
  let { RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_1, RING_HOMOMORPHISM_COMPOSE,
        RING_HOMOMORPHISM_INCLUSION, RING_HOMOMORPHISM_INTO_SUBRING_EQ,
        RING_HOMOMORPHISM_IN_CARRIER, RING_HOMOMORPHISM_NEG, RING_MUL, RING_MUL_ASSOC,
        RING_MUL_LID, RING_MUL_LNEG, RING_MUL_LZERO, RING_MUL_RID, RING_MUL_RNEG,
        RING_MUL_RZERO, RING_MUL_SYM, RING_NEG, RING_POLYNOMIAL, RING_POLYNOMIAL_CONST,
        RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_VAR, RING_POW, RING_RNEG_UNIQUE,
        RING_SPAN_0, RING_SPAN_ADD, RING_SPAN_FINITE, RING_SPAN_INC, RING_SPAN_MUL,
        RING_SPAN_NEG, RING_SPAN_SUBSET, RING_SPAN_SUM, RING_SUB, RING_SUB_RDISTRIB,
        RING_SUB_REFL, RING_SUM, RING_SUM_CLAUSES, RING_SUM_DELTA, RING_SUM_EQ,
        RING_SUM_EQ_0, RING_SUM_LMUL, RING_SUM_SUB, SING_SUBSET, SKOLEM_THM,
        SUBRING_GENERATED, SUBSET, algebraic_over, field_extension, o_THM,
        ring_monomorphism, ring_pow, ring_span_INDUCT, ring_sub, subring_of, .. } := D.core2
  -- @@SCOPE END

  let integral_element ← new_definition
    r"integral_element (r:A ring,r':B ring) (h:A->B) (x:B) <=>
  x IN ring_carrier r' /\
  ?p. p IN ring_carrier(poly_ring r (:1)) /\
      monic r p /\
      poly_extend (r,r') h (\v:1. x) p = ring_0 r'"

  let integrally_closed ← new_definition
    r"integrally_closed (r:A ring) <=>
  integral_domain r /\
  !x. integral_element
       (r,fraction_ring r) (ring_fractionate r {a | ring_regular r a}) x
      ==> x IN IMAGE (ring_fractionate r {a | ring_regular r a})
                      (ring_carrier r)"

  let INTEGRAL_ELEMENT_IN_CARRIER ← prove
    r"!r:A ring r':B ring h x.
        integral_element (r,r') h x ==> x IN ring_carrier r'"
    (SIMP_TAC [integral_element])

  let INTEGRAL_ELEMENT_IMAGE ← prove
    r"!r:A ring r':B ring h a.
        ring_homomorphism(r,r') h /\ a IN ring_carrier r
        ==> integral_element (r,r') h (h a)"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [integral_element] THEN SUBGOAL_THEN (← q r"(h:A->B) a IN ring_carrier r'") ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ASM_REWRITE_TAC []] THEN EXISTS_TAC (← q r"poly_sub r (poly_var r one) (poly_const r (a:A))") THEN ASM_SIMP_TAC [(← GSYM RING_POLYNOMIAL), RING_POLYNOMIAL_SUB, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_CONST, MONIC_X_MINUS_A, POLY_EXTEND_SUB, POLY_EXTEND_VAR, POLY_EXTEND_CONST, RING_SUB_REFL])

  let INTEGRAL_ELEMENT_0 ← prove
    r"!r:A ring r':B ring h.
        ring_homomorphism(r,r') h
        ==> integral_element (r,r') h (ring_0 r')"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (SUBST1_TAC o (SYM o (MATCH_MP RING_HOMOMORPHISM_0))) THEN MATCH_MP_TAC INTEGRAL_ELEMENT_IMAGE THEN ASM_REWRITE_TAC [RING_0])

  let INTEGRAL_ELEMENT_1 ← prove
    r"!r:A ring r':B ring h.
        ring_homomorphism(r,r') h
        ==> integral_element (r,r') h (ring_1 r')"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (SUBST1_TAC o (SYM o (MATCH_MP RING_HOMOMORPHISM_1))) THEN MATCH_MP_TAC INTEGRAL_ELEMENT_IMAGE THEN ASM_REWRITE_TAC [RING_1])

  let INTEGRAL_ELEMENT_RELATION ← prove
    r"!r:A ring r':B ring h x.
        ring_homomorphism(r,r') h /\ integral_element (r,r') h x
        ==> ?n c. (!i. i < n ==> c i IN ring_carrier r) /\
                  ring_add r' (ring_pow r' x n)
                    (ring_sum r' {i | i < n}
                       (\i. ring_mul r' (h(c i)) (ring_pow r' x i))) =
                  ring_0 r'"
    (REPEAT GEN_TAC THEN REWRITE_TAC [integral_element] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"p:(1->num)->A") STRIP_ASSUME_TAC))) THEN MAP_EVERY EXISTS_TAC [(← q r"poly_deg r (p:(1->num)->A)"), (← q r"\i. coeff i (p:(1->num)->A)")] THEN REWRITE_TAC [] THEN CONJ_TAC THENL [ASM_MESON_TAC [COEFF_IN_CARRIER_ALT, RING_POLYNOMIAL], ALL_TAC] THEN FIRST_X_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [(← SYM th)])) THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC POLY_EXTEND_MONIC_UNIVARIATE THEN ASM_REWRITE_TAC [])

  let INTEGRAL_ELEMENT_FINITE_MODULE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul r d (ring_mul r a b) = ring_mul r a (ring_mul r b (d:B))")
    prove
      r"!r:A ring r':B ring h x (t:K->bool) (e:K->B).
          ring_homomorphism(r,r') h /\ FINITE t /\ x IN ring_carrier r' /\
          (!i. i IN t ==> e i IN ring_carrier r') /\
          (?c. (!i. i IN t ==> c i IN ring_carrier r) /\
               ring_1 r' = ring_sum r' t (\i. ring_mul r' (h(c i)) (e i))) /\
          (!j. j IN t
               ==> ?c. (!i. i IN t ==> c i IN ring_carrier r) /\
                       ring_mul r' x (e j) =
                       ring_sum r' t (\i. ring_mul r' (h(c i)) (e i)))
          ==> integral_element (r,r') h x"
      (REPEAT GEN_TAC THEN DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN FIRST_X_ASSUM (MP_TAC o (GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM])) THEN REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"m:K->K->A") THEN DISCH_THEN (LABEL_TAC "m") THEN FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"c:K->A") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(!i j. i IN t /\ j IN t ==> (m:K->K->A) i j IN ring_carrier r) /\
      (!i j. i IN t /\ j IN t ==> (h:A->B)(m i j) IN ring_carrier r') /\
      (!i. i IN t ==> h((c:K->A) i) IN ring_carrier r')") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN REWRITE_TAC [integral_element] THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"ring_charpoly r t (m:K->K->A)") THEN ASM_SIMP_TAC [RING_CHARPOLY, RING_CHARPOLY_MONIC, RING_CHARPOLY_EXTEND] THEN ABBREV_TAC (← q r"d = ring_det r' (t:K->bool)
            (\i j. ring_sub r' (if i = j then x else ring_0 r')
                               ((h:A->B)(m i j)))") THEN SUBGOAL_THEN (← q r"!i. i IN t ==> ring_mul r' ((e:K->B) i) d = ring_0 r'") ASSUME_TAC THENL [X_GEN_TAC (← q r"i:K") THEN DISCH_TAC THEN EXPAND_TAC "d" THEN MATCH_MP_TAC RING_DET_DEPENDENT_COLUMNS_MUL THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [RING_SUB, RING_0], X_GEN_TAC (← q r"j:K") THEN DISCH_TAC] THEN TRANS_TAC EQ_TRANS (← q r"ring_sub r' (ring_sum r' t (\k:K. if k = j then ring_mul r' x (e j)
                                        else ring_0 r'))
                    (ring_sum r' t (\k. ring_mul r' ((h:A->B)((m:K->K->A) j k))
                                                    ((e:K->B) k)))") THEN CONJ_TAC THENL [wPart rand (rand o rand) RING_SUM_SUB THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"k:K") THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [RING_MUL, RING_0], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"k:K") THEN DISCH_TAC THEN REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"k:K = j") THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [RING_SUB_RDISTRIB, RING_MUL_LZERO, RING_0] THEN ASM_MESON_TAC [], REMOVE_THEN "m" (MP_TAC o (SPEC (← q r"j:K"))) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_SIMP_TAC [RING_SUM_DELTA, RING_MUL, RING_SUB_REFL, RING_SUM]], ALL_TAC] THEN SUBGOAL_THEN (← q r"(d:B) IN ring_carrier r'") ASSUME_TAC THENL [EXPAND_TAC "d" THEN REWRITE_TAC [RING_DET], ALL_TAC] THEN TRANS_TAC EQ_TRANS (← q r"ring_mul r' (d:B) (ring_1 r')") THEN CONJ_TAC THENL [ASM_SIMP_TAC [RING_MUL_RID], ALL_TAC] THEN ASM_SIMP_TAC [(← GSYM RING_SUM_LMUL), RING_MUL] THEN MATCH_MP_TAC RING_SUM_EQ_0 THEN X_GEN_TAC (← q r"i:K") THEN DISCH_TAC THEN REWRITE_TAC [] THEN TRANS_TAC EQ_TRANS (← q r"ring_mul r' ((h:A->B)((c:K->A) i)) (ring_mul r' ((e:K->B) i) d)") THEN CONJ_TAC THENL [MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [], ASM_SIMP_TAC [RING_MUL_RZERO]])

  let INTEGRAL_ELEMENT_MODULE ← prove
    r"!r:A ring r':B ring h z (e:num->B) (c:num->num->A) k.
        ring_homomorphism(r,r') h /\
        z IN ring_carrier r' /\
        0 < k /\
        e 0 = ring_1 r' /\
        (!j. j < k ==> e j IN ring_carrier r') /\
        (!i j. i < k /\ j < k ==> c i j IN ring_carrier r) /\
        (!j. j < k ==>
           ring_mul r' z (e j) =
           ring_sum r' {i | i < k}
             (\i. ring_mul r' (h(c j i)) (e i)))
        ==> integral_element (r,r') h z"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC (← INST_TYPE [((← qty r"num"), (← qty r"K"))] INTEGRAL_ELEMENT_FINITE_MODULE) THEN MAP_EVERY EXISTS_TAC [(← q r"{i:num | i < k}"), (← q r"e:num->B")] THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN CONJ_TAC THENL [EXISTS_TAC (← q r"\i:num. if i = 0 then ring_1 r else ring_0 r:A") THEN REWRITE_TAC [] THEN CONJ_TAC THENL [GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [RING_0, RING_1], ALL_TAC] THEN TRANS_TAC EQ_TRANS (← q r"ring_sum r' {i:num | i < k}
        (\i. if i = 0 then ring_1 r' else ring_0 (r':B ring))") THEN CONJ_TAC THENL [ASM_REWRITE_TAC [RING_SUM_DELTA, IN_ELIM_THM, RING_1], MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"i:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_1, RING_HOMOMORPHISM_0, RING_MUL_LZERO, RING_MUL_LID, RING_1]], X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN EXISTS_TAC (← q r"(c:num->num->A) j") THEN ASM_SIMP_TAC []])

  let INTEGRAL_SPAN_LMUL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul r w (ring_mul r a y) =
        ring_mul r a (ring_mul r w (y:B))")
    prove
      r"!r:A ring r':B ring h s s' w.
          w IN ring_carrier r' /\
          (!y. y IN s /\ y IN ring_carrier r'
               ==> ring_mul r' w y IN ring_span (r,r') h s')
          ==> !y. y IN ring_span (r,r') h s
                  ==> ring_mul r' w y IN ring_span (r,r') h s'"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!y. y IN ring_span (r,r') h s
          ==> y IN ring_carrier r' /\
              ring_mul r' w y IN ring_span (r,r') (h:A->B) s'") (fun th => MESON_TAC [th]) THEN MATCH_MP_TAC ring_span_INDUCT THEN ASM_SIMP_TAC [RING_MUL_RZERO, RING_SPAN_0, RING_0] THEN CONJ_TAC THENL [MAP_EVERY X_GEN_TAC [(← q r"y:B"), (← q r"z:B")] THEN STRIP_TAC THEN ASM_SIMP_TAC [RING_ADD, RING_ADD_LDISTRIB, RING_SPAN_ADD], MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"y:B")] THEN STRIP_TAC THEN ASM_SIMP_TAC [RING_MUL] THEN SUBGOAL_THEN (← q r"ring_mul r' w (ring_mul r' (h a) y) =
        ring_mul r' ((h:A->B) a) (ring_mul r' w y)") SUBST1_TAC THENL [MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC [], MATCH_MP_TAC RING_SPAN_MUL THEN ASM_REWRITE_TAC []]])

  let INTEGRAL_ELEMENT_SPAN ← prove
    r"!r:A ring r':B ring h g x.
        ring_homomorphism(r,r') h /\ FINITE g /\ g SUBSET ring_carrier r' /\
        ring_1 r' IN ring_span (r,r') h g /\ x IN ring_carrier r' /\
        (!y. y IN ring_span (r,r') h g
             ==> ring_mul r' x y IN ring_span (r,r') h g)
        ==> integral_element (r,r') h x"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"!y:B. y IN g ==> ring_mul r' x y IN ring_span (r,r') (h:A->B) g") MP_TAC THENL [ASM_MESON_TAC [RING_SPAN_INC, SUBSET], ALL_TAC] THEN UNDISCH_TAC (← q r"ring_1 r' IN ring_span (r,r') (h:A->B) g") THEN ASM_SIMP_TAC [RING_SPAN_FINITE, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC (← INST_TYPE [((← qty r"B"), (← qty r"K"))] INTEGRAL_ELEMENT_FINITE_MODULE) THEN MAP_EVERY EXISTS_TAC [(← q r"g:B->bool"), (← q r"\y:B. y")] THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [SUBSET])

  let INTEGRAL_SPAN_ADJOIN ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul r a (ring_mul r d p) = ring_mul r (ring_mul r d a) (p:B)")
    let r2 ← RING_RULE (← q r"ring_mul r z (ring_mul r a p) = ring_mul r a (ring_mul r z (p:B))")
    prove
      r"!r:A ring t:B ring k g z (d:num->B) m.
          ring_homomorphism(r,t) k /\ FINITE g /\ g SUBSET ring_carrier t /\
          ring_1 t IN ring_span (r,t) k g /\ z IN ring_carrier t /\
          (!j. j < m
               ==> d j IN ring_carrier t /\
                   !y. y IN ring_span (r,t) k g
                       ==> ring_mul t (d j) y IN ring_span (r,t) k g) /\
          ring_add t (ring_pow t z m)
            (ring_sum t {j | j < m} (\j. ring_mul t (d j) (ring_pow t z j))) =
          ring_0 t
          ==> ?g'. FINITE g' /\ g' SUBSET ring_carrier t /\
                   ring_1 t IN ring_span (r,t) k g' /\
                   (!y. y IN ring_span (r,t) k g'
                        ==> ring_mul t z y IN ring_span (r,t) k g') /\
                   (!w. w IN ring_carrier t /\
                        (!y. y IN ring_span (r,t) k g
                             ==> ring_mul t w y IN ring_span (r,t) k g)
                        ==> !y. y IN ring_span (r,t) k g'
                                ==> ring_mul t w y IN ring_span (r,t) k g')"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"m = 0") THENL [FIRST_X_ASSUM SUBST_ALL_TAC THEN EXISTS_TAC (← q r"g:B->bool") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"!y:B. y IN ring_carrier t ==> y IN ring_span (r,t) (k:A->B) g") ASSUME_TAC THENL [UNDISCH_TAC (← q r"ring_add t (ring_pow t z 0)
            (ring_sum t {j | j < 0}
              (\j. ring_mul t ((d:num->B) j) (ring_pow t z j))) = ring_0 t") THEN REWRITE_TAC [(← CONJUNCT1 LT), EMPTY_GSPEC, RING_SUM_CLAUSES, ring_pow] THEN SIMP_TAC [RING_ADD_RZERO, RING_1] THEN MESON_TAC [RING_MUL_RID, RING_MUL_RZERO, RING_SPAN_0], CONJ_TAC THENL [ALL_TAC, MESON_TAC []] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC RING_MUL THEN ASM_MESON_TAC [RING_SPAN_SUBSET, SUBSET]], ALL_TAC] THEN ABBREV_TAC (← q r"g' = {ring_mul t (a:B) (ring_pow t z j) |
                      a IN g /\ j IN {j:num | j < m}}") THEN SUBGOAL_THEN (← q r"!a:B. a IN g ==> a IN ring_carrier t") ASSUME_TAC THENL [ASM_REWRITE_TAC [(← GSYM SUBSET)], ALL_TAC] THEN SUBGOAL_THEN (← q r"!y. y IN g' <=>
          ?a j. a IN g /\ j < m /\ y = ring_mul t (a:B) (ring_pow t z j)") (LABEL_TAC "g'") THENL [EXPAND_TAC "g'" THEN REWRITE_TAC [IN_ELIM_THM] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!u j. u IN ring_span (r,t) k g /\ j < m
            ==> ring_mul t u (ring_pow t z j) IN ring_span (r,t) (k:A->B) g'") (LABEL_TAC "aux") THENL [REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"(u:B) IN ring_carrier t") ASSUME_TAC THENL [ASM_MESON_TAC [RING_SPAN_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul t u (ring_pow t z j) = ring_mul t (ring_pow t z j) (u:B)") SUBST1_TAC THENL [MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC [RING_POW], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"t:B ring"), (← q r"k:A->B"), (← q r"g:B->bool"), (← q r"g':B->bool"), (← q r"ring_pow t (z:B) j")] INTEGRAL_SPAN_LMUL) THEN ASM_SIMP_TAC [RING_POW] THEN ANTS_TAC THENL [X_GEN_TAC (← q r"y:B") THEN STRIP_TAC THEN MATCH_MP_TAC RING_SPAN_INC THEN ASM_SIMP_TAC [RING_MUL, RING_POW] THEN USE_THEN "g'" (fun th => REWRITE_TAC [th]) THEN MAP_EVERY EXISTS_TAC [(← q r"y:B"), (← q r"j:num")] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC [RING_POW], DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC []], ALL_TAC] THEN EXISTS_TAC (← q r"g':B->bool") THEN REPEAT CONJ_TAC THENL [EXPAND_TAC "g'" THEN MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT], EXPAND_TAC "g'" THEN REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN ASM_SIMP_TAC [RING_MUL, RING_POW], REMOVE_THEN "aux" (MP_TAC o (SPECL [(← q r"ring_1 t:B"), (← q r"0")])) THEN ASM_SIMP_TAC [LE_1, ring_pow, RING_MUL_LID, RING_1], ALL_TAC, X_GEN_TAC (← q r"w:B") THEN STRIP_TAC] THEN MATCH_MP_TAC INTEGRAL_SPAN_LMUL THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"y:B") THEN DISCH_THEN (MP_TAC o CONJUNCT1) THEN USE_THEN "g'" (fun th => REWRITE_TAC [th, LEFT_IMP_EXISTS_THM]) THEN MAP_EVERY X_GEN_TAC [(← q r"a:B"), (← q r"j:num")] THEN DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN FIRST_X_ASSUM SUBST1_TAC THENL [ALL_TAC, ASM_SIMP_TAC [RING_MUL_ASSOC, RING_POW] THEN USE_THEN "aux" MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_SPAN_INC]] THEN SUBGOAL_THEN (← q r"ring_mul t z (ring_mul t a (ring_pow t z j)) =
      ring_mul t a (ring_pow t (z:B) (SUC j))") SUBST1_TAC THENL [REWRITE_TAC [ring_pow] THEN MATCH_MP_TAC r2 THEN ASM_SIMP_TAC [RING_POW], ALL_TAC] THEN ASM_CASES_TAC (← q r"SUC j < m") THENL [USE_THEN "aux" MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_SPAN_INC], SUBGOAL_THEN (← q r"SUC j = m") SUBST1_TAC THENL [ASM_ARITH_TAC, ALL_TAC]] THEN SUBGOAL_THEN (← q r"ring_pow t z m =
      ring_neg t (ring_sum t {j | j < m}
                    (\j. ring_mul t ((d:num->B) j) (ring_pow t z j)))") SUBST1_TAC THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_RNEG_UNIQUE THEN ASM_SIMP_TAC [RING_POW, RING_SUM], ALL_TAC] THEN ASM_SIMP_TAC [RING_MUL_RNEG, RING_SUM, (← GSYM RING_SUM_LMUL), FINITE_NUMSEG_LT, IN_ELIM_THM, RING_MUL, RING_POW] THEN MATCH_MP_TAC RING_SPAN_NEG THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC RING_SPAN_SUM THEN X_GEN_TAC (← q r"i:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_mul t a (ring_mul t ((d:num->B) i) (ring_pow t z i)) =
      ring_mul t (ring_mul t (d i) a) (ring_pow t z i)") SUBST1_TAC THENL [MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [RING_POW], USE_THEN "aux" MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_SPAN_INC]])

  let INTEGRAL_ELEMENT_FROM_RELATION ← prove
    r"!r:A ring r':B ring h x n c.
        ring_homomorphism(r,r') h /\ x IN ring_carrier r' /\
        (!i. i < n ==> c i IN ring_carrier r) /\
        ring_add r' (ring_pow r' x n)
          (ring_sum r' {i | i < n}
             (\i. ring_mul r' (h(c i)) (ring_pow r' x i))) = ring_0 r'
        ==> integral_element (r,r') h x"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"r':B ring"), (← q r"h:A->B"), (← q r"{ring_1 r':B}"), (← q r"x:B"), (← q r"\i:num. (h:A->B)(c i)"), (← q r"n:num")] INTEGRAL_SPAN_ADJOIN) THEN ASM_SIMP_TAC [FINITE_SING, SING_SUBSET, RING_1, RING_SPAN_INC, IN_SING] THEN ANTS_TAC THENL [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(h:A->B)(c(i:num)) IN ring_carrier r'") ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ASM_REWRITE_TAC []] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_SPAN_MUL THEN ASM_SIMP_TAC [], DISCH_THEN (X_CHOOSE_THEN (← q r"g:B->bool") STRIP_ASSUME_TAC) THEN MATCH_MP_TAC INTEGRAL_ELEMENT_SPAN THEN EXISTS_TAC (← q r"g:B->bool") THEN ASM_REWRITE_TAC []])

  let INTEGRAL_ELEMENT_OVER_SUBRING ← prove
    r"!r s (h:A->B) t x.
        ring_homomorphism(r,s) h /\
        IMAGE h (ring_carrier r) SUBSET ring_carrier(subring_generated s t) /\
        integral_element (r,s) h x
        ==> integral_element (subring_generated s t,s) I x"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"h:A->B"), (← q r"x:B")] INTEGRAL_ELEMENT_RELATION) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"n:num"), (← q r"c:num->A")] THEN STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_ELEMENT_FROM_RELATION THEN MAP_EVERY EXISTS_TAC [(← q r"n:num"), (← q r"(h:A->B) o (c:num->A)")] THEN ASM_REWRITE_TAC [I_THM, o_THM] THEN REPEAT CONJ_TAC THENL [REWRITE_TAC [I_DEF, RING_HOMOMORPHISM_INCLUSION], ASM_MESON_TAC [INTEGRAL_ELEMENT_IN_CARRIER], ASM SET_TAC []])

  let INTEGRAL_SPAN_FINITE_SET ← prove
    r"!r:A ring t:B ring k b.
        ring_homomorphism(r,t) k /\ FINITE b /\
        (!y. y IN b ==> integral_element (r,t) k y)
        ==> ?g. FINITE g /\ g SUBSET ring_carrier t /\
                ring_1 t IN ring_span (r,t) k g /\
                !y. y IN b
                    ==> !z. z IN ring_span (r,t) k g
                            ==> ring_mul t y z IN ring_span (r,t) k g"
    (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN REWRITE_TAC [IMP_CONJ] THEN SPEC_TAC ((← q r"b:B->bool"), (← q r"b:B->bool")) THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL [DISCH_TAC THEN EXISTS_TAC (← q r"{ring_1 t:B}") THEN SIMP_TAC [FINITE_SING, SING_SUBSET, RING_1, RING_SPAN_INC, IN_SING, NOT_IN_EMPTY], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"a:B"), (← q r"b:B->bool")] THEN REWRITE_TAC [FORALL_IN_INSERT] THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN DISCH_THEN (fun ih => STRIP_TAC THEN MP_TAC ih) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"g:B->bool") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"t:B ring"), (← q r"k:A->B"), (← q r"a:B")] INTEGRAL_ELEMENT_RELATION) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"n:num"), (← q r"c:num->A")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"t:B ring"), (← q r"k:A->B"), (← q r"g:B->bool"), (← q r"a:B"), (← q r"\i:num. (k:A->B)(c i)"), (← q r"n:num")] INTEGRAL_SPAN_ADJOIN) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [CONJ_TAC THENL [ASM_MESON_TAC [INTEGRAL_ELEMENT_IN_CARRIER], ALL_TAC] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(k:A->B)(c(i:num)) IN ring_carrier t") ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ASM_REWRITE_TAC []] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_SPAN_MUL THEN ASM_SIMP_TAC [], MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"g':B->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC [INTEGRAL_ELEMENT_IN_CARRIER]])

  let INTEGRAL_ELEMENT_EXPLICIT ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"(!y. y IN ring_carrier r' ==> ring_mul r' y (ring_1 r') = y) /\
    (!y. y IN ring_carrier r' ==> ring_mul r' y (ring_0 r') = ring_0 r') /\
    ring_1 r' = ring_0 r' /\ a IN ring_carrier r'
    ==> a = ring_0 (r':B ring)"
    let r2 ← MESON [RING_MUL_RID, RING_MUL_RZERO] q1
    let q3 ← q r"ring_add r' (ring_pow r' x n)
      (ring_sum r' {i | i < n}
         (\i. ring_mul r' ((h:A->B)(c i)) (ring_pow r' x i))) =
    ring_0 r'"
    let q4 ← q r"\i:num. ring_0 r:A"
    let q5 ← q r"1"
    let q6 ← q r"c:num->A"
    let q7 ← q r"n:num"
    let q8 ← q r"n = 0"
    let q9 ← q r"c:num->A"
    let q10 ← q r"n:num"
    let q11 ← q r"x:B"
    let q12 ← q r"h:A->B"
    let q13 ← q r"r':B ring"
    let q14 ← q r"r:A ring"
    let v15 ← ISPECL [q14, q13, q12, q11] INTEGRAL_ELEMENT_RELATION
    let q16 ← q r"(x:B) IN ring_carrier r'"
    let q17 ← q r"c:num->A"
    let q18 ← q r"n:num"
    prove
      r"!r:A ring r':B ring h x.
          ring_homomorphism(r,r') h
          ==> (integral_element (r,r') h x <=>
               x IN ring_carrier r' /\
               ?n c. 0 < n /\
                     (!i. i < n ==> c(i) IN ring_carrier r) /\
                     ring_add r' (ring_pow r' x n)
                                 (ring_sum r' {i | i < n}
                                    (\i. ring_mul r' (h(c i))
                                                     (ring_pow r' x i)))
                     = ring_0 r')"
      (REPEAT STRIP_TAC THEN EQ_TAC THENL [ALL_TAC, STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_ELEMENT_FROM_RELATION THEN MAP_EVERY EXISTS_TAC [q18, q17] THEN ASM_REWRITE_TAC []] THEN DISCH_TAC THEN SUBGOAL_THEN q16 ASSUME_TAC THENL [ASM_MESON_TAC [INTEGRAL_ELEMENT_IN_CARRIER], ASM_REWRITE_TAC []] THEN MP_TAC v15 THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [q10, q9] THEN STRIP_TAC THEN ASM_CASES_TAC q8 THENL [ALL_TAC, MAP_EVERY EXISTS_TAC [q7, q6] THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC] THEN MAP_EVERY EXISTS_TAC [q5, q4] THEN REWRITE_TAC [ARITH, RING_0] THEN UNDISCH_TAC q3 THEN ASM_REWRITE_TAC [LT, EMPTY_GSPEC, RING_SUM_CLAUSES, ring_pow] THEN SIMP_TAC [RING_ADD_RZERO, RING_1] THEN DISCH_TAC THEN MATCH_MP_TAC r2 THEN ASM_SIMP_TAC [RING_MUL_RID, RING_MUL_RZERO, RING_ADD, RING_POW, RING_SUM])

  let INTEGRAL_ELEMENT_ADD ← prove
    r"!r:A ring r':B ring h x y.
        ring_homomorphism(r,r') h /\
        integral_element (r,r') h x /\ integral_element (r,r') h y
        ==> integral_element (r,r') h (ring_add r' x y)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"r':B ring"), (← q r"h:A->B"), (← q r"{x:B,y}")] INTEGRAL_SPAN_FINITE_SET) THEN ASM_REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY, FORALL_IN_INSERT, NOT_IN_EMPTY] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"g:B->bool") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier r' /\ y IN ring_carrier r'") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [INTEGRAL_ELEMENT_IN_CARRIER], ALL_TAC] THEN MATCH_MP_TAC INTEGRAL_ELEMENT_SPAN THEN EXISTS_TAC (← q r"g:B->bool") THEN ASM_SIMP_TAC [RING_ADD] THEN X_GEN_TAC (← q r"z:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(z:B) IN ring_carrier r'") ASSUME_TAC THENL [ASM_MESON_TAC [RING_SPAN_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [RING_ADD_RDISTRIB] THEN MATCH_MP_TAC RING_SPAN_ADD THEN ASM_SIMP_TAC [])

  let INTEGRAL_ELEMENT_MUL ← prove
    r"!r:A ring r':B ring h x y.
        ring_homomorphism(r,r') h /\
        integral_element (r,r') h x /\ integral_element (r,r') h y
        ==> integral_element (r,r') h (ring_mul r' x y)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"r':B ring"), (← q r"h:A->B"), (← q r"{x:B,y}")] INTEGRAL_SPAN_FINITE_SET) THEN ASM_REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY, FORALL_IN_INSERT, NOT_IN_EMPTY] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"g:B->bool") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier r' /\ y IN ring_carrier r'") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [INTEGRAL_ELEMENT_IN_CARRIER], ALL_TAC] THEN MATCH_MP_TAC INTEGRAL_ELEMENT_SPAN THEN EXISTS_TAC (← q r"g:B->bool") THEN ASM_SIMP_TAC [RING_MUL] THEN X_GEN_TAC (← q r"z:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(z:B) IN ring_carrier r'") ASSUME_TAC THENL [ASM_MESON_TAC [RING_SPAN_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [(← GSYM RING_MUL_ASSOC)])

  let INTEGRAL_ELEMENT_NEG ← prove
    r"!r:A ring r':B ring h x.
        ring_homomorphism(r,r') h /\
        integral_element (r,r') h x
        ==> integral_element (r,r') h (ring_neg r' x)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP INTEGRAL_ELEMENT_IN_CARRIER)) THEN SUBGOAL_THEN (← q r"ring_neg r' x = ring_mul r' ((h:A->B)(ring_neg r (ring_1 r))) (x:B)") SUBST1_TAC THENL [FIRST_ASSUM (fun th => tactic_of do pure (SIMP_TAC [RING_1, (← MATCH_MP RING_HOMOMORPHISM_NEG th), (← MATCH_MP RING_HOMOMORPHISM_1 th)])) THEN ASM_SIMP_TAC [RING_MUL_LNEG, RING_MUL_LID, RING_1], MATCH_MP_TAC INTEGRAL_ELEMENT_MUL THEN ASM_SIMP_TAC [INTEGRAL_ELEMENT_IMAGE, RING_NEG, RING_1]])

  let INTEGRAL_ELEMENT_SUB ← prove
    r"!r:A ring r':B ring h x y.
        ring_homomorphism(r,r') h /\
        integral_element (r,r') h x /\ integral_element (r,r') h y
        ==> integral_element (r,r') h (ring_sub r' x y)"
    (SIMP_TAC [ring_sub, INTEGRAL_ELEMENT_ADD, INTEGRAL_ELEMENT_NEG])

  let INTEGRAL_ELEMENT_POW ← prove
    r"!r:A ring r':B ring h x n.
        ring_homomorphism(r,r') h /\
        integral_element (r,r') h x
        ==> integral_element (r,r') h (ring_pow r' x n)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SPEC_TAC ((← q r"n:num"), (← q r"n:num")) THEN INDUCT_TAC THEN ASM_SIMP_TAC [ring_pow, INTEGRAL_ELEMENT_1, INTEGRAL_ELEMENT_MUL])

  let INTEGRAL_CLOSURE_SUBRING ← prove
    r"!r:A ring r':B ring h.
        ring_homomorphism(r,r') h
        ==> {x | integral_element (r,r') h x} subring_of r'"
    (SIMP_TAC [subring_of, SUBSET, IN_ELIM_THM, INTEGRAL_ELEMENT_IN_CARRIER, INTEGRAL_ELEMENT_0, INTEGRAL_ELEMENT_1, INTEGRAL_ELEMENT_NEG, INTEGRAL_ELEMENT_ADD, INTEGRAL_ELEMENT_MUL] THEN MESON_TAC [INTEGRAL_ELEMENT_IN_CARRIER])

  let INTEGRAL_CLOSURE_SUPSET_IMAGE ← prove
    r"!r:A ring r':B ring h.
        ring_homomorphism(r,r') h
        ==> IMAGE h (ring_carrier r) SUBSET {x | integral_element (r,r') h x}"
    (SIMP_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM, INTEGRAL_ELEMENT_IMAGE])

  let INTEGRAL_ELEMENT_HOMOMORPHIC_IMAGE ← prove
    r"!r:A ring r':B ring r'':C ring h g x.
        ring_homomorphism(r,r') h /\ ring_homomorphism(r',r'') g /\
        integral_element (r,r') h x
        ==> integral_element (r,r'') (g o h) (g x)"
    (REPEAT GEN_TAC THEN REWRITE_TAC [integral_element] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"p:(1->num)->A") STRIP_ASSUME_TAC)))) THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN EXISTS_TAC (← q r"p:(1->num)->A") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"r':B ring"), (← q r"r'':C ring"), (← q r"h:A->B"), (← q r"(:1)"), (← q r"\v:1. (x:B)"), (← q r"g:B->C"), (← q r"p:(1->num)->A")] POLY_EXTEND_HOMOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_UNIV] THEN SUBGOAL_THEN (← q r"(g:B->C) o (\v:1. x) = (\v. g x)") SUBST1_TAC THENL [REWRITE_TAC [FUN_EQ_THM, o_THM], DISCH_THEN (SUBST1_TAC o SYM)] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_0])

  let INTEGRAL_ELEMENT_MONOMORPHIC_PREIMAGE ← prove
    r"!r:A ring r':B ring r'':C ring h g x.
        ring_homomorphism(r,r') h /\ ring_monomorphism(r',r'') g /\
        x IN ring_carrier r' /\
        integral_element (r,r'') (g o h) (g x)
        ==> integral_element (r,r') h x"
    (REPEAT GEN_TAC THEN REWRITE_TAC [integral_element] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"p:(1->num)->A") STRIP_ASSUME_TAC))))) THEN REWRITE_TAC [ring_monomorphism] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"p:(1->num)->A") THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [POLY_EXTEND, RING_0] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"r':B ring"), (← q r"r'':C ring"), (← q r"h:A->B"), (← q r"(:1)"), (← q r"\v:1. (x:B)"), (← q r"g:B->C"), (← q r"p:(1->num)->A")] POLY_EXTEND_HOMOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_UNIV] THEN SUBGOAL_THEN (← q r"(g:B->C) o (\v:1. x) = (\v. g x)") SUBST1_TAC THENL [REWRITE_TAC [FUN_EQ_THM, o_THM], DISCH_THEN SUBST1_TAC] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_0])

  let INTEGRAL_ELEMENT_SUBRING_GENERATED ← prove
    r"!r:A ring r':B ring h s x.
        ring_homomorphism(r,r') h /\
        s subring_of r' /\ IMAGE h (ring_carrier r) SUBSET s
        ==> (integral_element (r,subring_generated r' s) h x <=>
             integral_element (r,r') h x /\ x IN s)"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [integral_element] THEN ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING] THEN REWRITE_TAC [SUBRING_GENERATED] THEN ASM_CASES_TAC (← q r"(x:B) IN s") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier r'") ASSUME_TAC THENL [ASM_MESON_TAC [subring_of, SUBSET], ASM_REWRITE_TAC []] THEN SUBGOAL_THEN (← q r"!p. p IN ring_carrier(poly_ring r (:1))
        ==> poly_extend (r,subring_generated r' s) (h:A->B) (\v:1. x) p =
            poly_extend (r,r') h (\v. x) p") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC POLY_EXTEND_INTO_SUBRING_GENERATED THEN EXISTS_TAC (← q r"(:1)") THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_INTO_SUBRING_EQ, CARRIER_SUBRING_GENERATED_SUBRING], EQ_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"p:(1->num)->A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC []])

  let INTEGRAL_ELEMENT_TRANS ← prove
    r"!r:A ring s:B ring t:C ring f g x.
        ring_homomorphism(r,s) f /\ ring_homomorphism(s,t) g /\
        (!y. y IN ring_carrier s ==> integral_element (r,s) f y) /\
        integral_element (s,t) g x
        ==> integral_element (r,t) (g o f) x"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_homomorphism(r:A ring,t:C ring) ((g:B->C) o (f:A->B))") ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_COMPOSE], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"t:C ring"), (← q r"g:B->C"), (← q r"x:C")] INTEGRAL_ELEMENT_RELATION) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"n:num"), (← q r"c:num->B")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"t:C ring"), (← q r"(g:B->C) o (f:A->B)"), (← q r"IMAGE (\i. (g:B->C)(c i)) {i:num | i < n}")] INTEGRAL_SPAN_FINITE_SET) THEN ASM_SIMP_TAC [FINITE_IMAGE, FINITE_NUMSEG_LT, FORALL_IN_IMAGE, IN_ELIM_THM] THEN ANTS_TAC THENL [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN MATCH_MP_TAC INTEGRAL_ELEMENT_HOMOMORPHIC_IMAGE THEN EXISTS_TAC (← q r"s:B ring") THEN ASM_SIMP_TAC [], DISCH_THEN (X_CHOOSE_THEN (← q r"g1:C->bool") STRIP_ASSUME_TAC)] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"t:C ring"), (← q r"(g:B->C) o (f:A->B)"), (← q r"g1:C->bool"), (← q r"x:C"), (← q r"\i:num. (g:B->C)(c i)"), (← q r"n:num")] INTEGRAL_SPAN_ADJOIN) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [CONJ_TAC THENL [ASM_MESON_TAC [INTEGRAL_ELEMENT_IN_CARRIER], ALL_TAC] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN ASM_SIMP_TAC [] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], DISCH_THEN (X_CHOOSE_THEN (← q r"g2:C->bool") STRIP_ASSUME_TAC)] THEN MATCH_MP_TAC INTEGRAL_ELEMENT_SPAN THEN EXISTS_TAC (← q r"g2:C->bool") THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [INTEGRAL_ELEMENT_IN_CARRIER])

  let INTEGRAL_CLOSURE_IDEMPOT ← prove
    r"!r:A ring r':B ring h x.
        ring_homomorphism(r,r') h /\
        integral_element
          (subring_generated r' {x | integral_element (r,r') h x},r') I x
        ==> integral_element (r,r') h x"
    (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"s = {x | integral_element (r:A ring,r':B ring) h x}") THEN SUBGOAL_THEN (← q r"(s:B->bool) subring_of r' /\ IMAGE (h:A->B) (ring_carrier r) SUBSET s") STRIP_ASSUME_TAC THENL [EXPAND_TAC "s" THEN ASM_SIMP_TAC [INTEGRAL_CLOSURE_SUBRING, INTEGRAL_CLOSURE_SUPSET_IMAGE], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"subring_generated r' (s:B->bool)"), (← q r"r':B ring"), (← q r"h:A->B"), (← q r"I:B->B"), (← q r"x:B")] INTEGRAL_ELEMENT_TRANS) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_INTO_SUBRING_EQ, I_O_ID, INTEGRAL_ELEMENT_SUBRING_GENERATED, CARRIER_SUBRING_GENERATED_SUBRING] THEN ANTS_TAC THENL [CONJ_TAC THENL [REWRITE_TAC [I_DEF, RING_HOMOMORPHISM_INCLUSION], EXPAND_TAC "s" THEN SIMP_TAC [IN_ELIM_THM]], EXPAND_TAC "s" THEN SIMP_TAC [IN_ELIM_THM]])

  let INTEGRAL_OVER_FIELD_EQ_ALGEBRAIC ← prove
    r"!k:A ring l:B ring h x.
        field_extension (k,l) h
        ==> (integral_element (k,l) h x <=> algebraic_over (k,l) h x)"
    (REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_extension])) THEN EQ_TAC THENL [REWRITE_TAC [integral_element, algebraic_over] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"p:(1->num)->A") THEN ASM_REWRITE_TAC [POLY_RING_CLAUSES] THEN MATCH_MP_TAC MONIC_IMP_NONZERO THEN ASM_SIMP_TAC [RING_POLYNOMIAL, FIELD_IMP_NONTRIVIAL_RING], DISCH_TAC THEN REWRITE_TAC [integral_element] THEN ASM_MESON_TAC [ALGEBRAIC_OVER_IN_CARRIER, MINIMAL_POLYNOMIAL]])

  -- @@RETURN BEGIN
  return { integral_element, integrally_closed, INTEGRAL_ELEMENT_IN_CARRIER,
           INTEGRAL_ELEMENT_IMAGE, INTEGRAL_ELEMENT_0, INTEGRAL_ELEMENT_1,
           INTEGRAL_ELEMENT_RELATION, INTEGRAL_ELEMENT_FINITE_MODULE,
           INTEGRAL_ELEMENT_MODULE, INTEGRAL_SPAN_LMUL, INTEGRAL_ELEMENT_SPAN,
           INTEGRAL_SPAN_ADJOIN, INTEGRAL_ELEMENT_FROM_RELATION,
           INTEGRAL_ELEMENT_OVER_SUBRING, INTEGRAL_SPAN_FINITE_SET,
           INTEGRAL_ELEMENT_EXPLICIT, INTEGRAL_ELEMENT_ADD, INTEGRAL_ELEMENT_MUL,
           INTEGRAL_ELEMENT_NEG, INTEGRAL_ELEMENT_SUB, INTEGRAL_ELEMENT_POW,
           INTEGRAL_CLOSURE_SUBRING, INTEGRAL_CLOSURE_SUPSET_IMAGE,
           INTEGRAL_ELEMENT_HOMOMORPHIC_IMAGE, INTEGRAL_ELEMENT_MONOMORPHIC_PREIMAGE,
           INTEGRAL_ELEMENT_SUBRING_GENERATED, INTEGRAL_ELEMENT_TRANS,
           INTEGRAL_CLOSURE_IDEMPOT, INTEGRAL_OVER_FIELD_EQ_ALGEBRAIC }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- integral.ml phrases from line 810 to 1516                              -/
/- ---------------------------------------------------------------------- -/

structure Integral02 where
  -- @@FIELDS
  INTEGRAL_ELEMENT_IN_ADJOIN_INV : thm
  INTEGRAL_HOMOGENEOUS_SCALE : thm
  INTEGRAL_HOMOGENEOUS_HOMOMORPHIC_IMAGE : thm
  RING_REGULAR_MUL_EQ_0 : thm
  INTEGRAL_HOMOGENEOUS_CLEAR : thm
  INTEGRAL_UFD_HOMOGENEOUS_DIVIDES : thm
  INTEGRAL_HOMOGENEOUS_RELATION : thm
  INTEGRAL_MONOMORPHISM_IN_IMAGE : thm
  INTEGRAL_FRACTION_RING_DENOMINATOR : thm
  INTEGRAL_FRACTION_RING_RELATION : thm
  INTEGRALLY_CLOSED_ALT : thm
  UFD_IMP_INTEGRALLY_CLOSED : thm
  PID_IMP_INTEGRALLY_CLOSED : thm
  FIELD_IMP_INTEGRALLY_CLOSED : thm
  INTEGRALLY_CLOSED_INTEGER_RING : thm
  INTEGRAL_ELEMENT_PRIME_SUBFIELD : thm
  INTEGRALLY_CLOSED_INTEGRAL_CLOSURE : thm
  INTEGRALLY_CLOSED_DIVIDES : thm
  INTEGRAL_ELEMENT_FRACTION_IN_IMAGE : thm
  INTEGRALLY_CLOSED_INTEGRAL_IMAGE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupIntegral02 [HolBase] (D : IntegralDeps) (BIntegral01 : Integral01) :
    ExceptT String IO Integral02 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, MESON, MESON_TAC, RING_RULE, TAUT, .. } := D
  let { CARRIER_SUBRING_GENERATED_SUBRING, EQ_TRANS, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_IMP_PID, FIELD_MUL_RINV, FIELD_REGULAR, FIELD_SUBFIELD_GENERATED,
        FIELD_UNIT, FINITE_NUMSEG, FINITE_NUMSEG_LT, IDEAL_GENERATED_ADJOIN_EXPLICIT,
        IDEAL_GENERATED_INC, INTEGER_RING, INTEGRAL_DOMAIN_MUL_EQ_0,
        INTEGRAL_DOMAIN_POW_EQ_0, INTEGRAL_DOMAIN_REGULAR,
        INTEGRAL_DOMAIN_SUBRING_GENERATED, IN_ELIM_THM, IN_IMAGE, IN_INSERT, IN_NUMSEG,
        IN_RING_IDEAL_LMUL, IN_UNIV, I_DEF, I_THM, LEFT_AND_EXISTS_THM,
        LEFT_IMP_EXISTS_THM, LOCALEQUIV_MUL_LCANCEL, LT, LT_0, MONO_EXISTS, NOT_SUC,
        NUMSEG_LT, PID_IMP_UFD, RIGHT_AND_EXISTS_THM, RING_1, RING_ADD,
        RING_ADD_LDISTRIB, RING_ADD_RNEG, RING_ADD_RZERO,
        RING_CARRIER_SUBRING_GENERATED_0, RING_DIVIDES_0, RING_DIVIDES_ADD,
        RING_DIVIDES_LMUL, .. } := D.core1
  let { RING_DIVIDES_LMUL2, RING_DIVIDES_NEG, RING_DIVIDES_REFL, RING_DIVIDES_RMUL,
        RING_DIVIDES_ZERO, RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_ADD,
        RING_HOMOMORPHISM_INCLUSION, RING_HOMOMORPHISM_INTEGER_RING_OF_INT,
        RING_HOMOMORPHISM_IN_CARRIER, RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_POW,
        RING_HOMOMORPHISM_SUM, RING_IDEAL_CARRIER, RING_IDEAL_IDEAL_GENERATED,
        RING_INV, RING_LOCALEQUIV_IN_CARRIER, RING_LOCALIZATION_CARRIER,
        RING_MONOMORPHISM_ALT, RING_MONOMORPHISM_EQ_0, RING_MONOMORPHISM_FRACTIONATE,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MONOMORPHISM_INTEGER_RING_OF_INT,
        RING_MUL, RING_MULTSYS_REGULAR, RING_MUL_ASSOC, RING_MUL_LINV, RING_MUL_LNEG,
        RING_MUL_POW, RING_MUL_RID, RING_MUL_RZERO, RING_MUL_SYM, RING_NEG,
        RING_NEG_IN_SUBRING_GENERATED, RING_OF_INT, RING_POW, RING_POW_ADD,
        RING_POW_ONE, RING_POW_ZERO, RING_PRIME_DIVIDES_POW, RING_REGULAR_IN_CARRIER,
        RING_REGULAR_POW, RING_RNEG_UNIQUE, RING_SUB, RING_SUB_EQ_0, RING_SUB_LDISTRIB,
        RING_SUB_REFL, RING_SUM, RING_SUM_CLOSED, RING_SUM_EQ, RING_SUM_EQ_0,
        RING_SUM_LMUL, RING_SUM_NEG, RING_SUM_REFLECT, RING_UNIT_DIVIDES_ANY,
        RING_UNIT_FRACTIONATE, RING_UNIT_IMP_REGULAR, SUBFIELD_GENERATED_QUOTIENTS,
        SUBRING_GENERATED, SUBRING_GENERATED_INC_GEN, SUBSET, SUB_0, SUC_SUB1,
        UFD_IMP_INTEGRAL_DOMAIN, UFD_INTEGER_RING, UFD_PRIME_FACTOR_INDUCT,
        fraction_ring, o_THM, ring_div, ring_divides, ring_monomorphism, ring_pow,
        ring_prime, ring_regular, ring_sub, ring_zerodivisor, subring_of, .. } := D.core2
  let { INTEGRAL_CLOSURE_IDEMPOT, INTEGRAL_CLOSURE_SUBRING, INTEGRAL_ELEMENT_EXPLICIT,
        INTEGRAL_ELEMENT_FROM_RELATION, INTEGRAL_ELEMENT_IN_CARRIER,
        INTEGRAL_ELEMENT_MONOMORPHIC_PREIMAGE, INTEGRAL_ELEMENT_RELATION,
        integrally_closed, .. } := BIntegral01
  -- @@SCOPE END

  let INTEGRAL_ELEMENT_IN_ADJOIN_INV ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul k b d = ring_1 k
      ==> ring_mul k (ring_mul k a b) (ring_mul k c d) = ring_mul k c (a:A)")
    let r9 ← TAUT (← q r"p /\ (q ==> r) ==> (p <=> q) ==> r")
    prove
      r"!(k:A ring) a x.
          field k /\ a subring_of k /\ x IN ring_carrier k /\ ~(x = ring_0 k) /\
          x IN ring_carrier(subring_generated k (ring_inv k x INSERT a))
          ==> integral_element (subring_generated k a,k) I x"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"a SUBSET ring_carrier k /\ ring_1 k IN a /\
      ring_carrier(subring_generated k a) = (a:A->bool) /\
      (!z. z IN a ==> ring_neg k z IN a)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING] THEN UNDISCH_TAC (← q r"(a:A->bool) subring_of k") THEN SIMP_TAC [subring_of], ALL_TAC] THEN ABBREV_TAC (← q r"y = ring_inv k (x:A)") THEN SUBGOAL_THEN (← q r"(y:A) IN ring_carrier k") ASSUME_TAC THENL [EXPAND_TAC "y" THEN ASM_SIMP_TAC [RING_INV], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. ring_mul k (ring_pow k x i) (ring_pow k (y:A) i) = ring_1 k") ASSUME_TAC THENL [EXPAND_TAC "y" THEN ASM_SIMP_TAC [(← GSYM RING_MUL_POW), RING_INV, FIELD_MUL_RINV, RING_POW_ONE], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A->bool"), (← q r"a:A->bool"), (← q r"y:A"), (← q r"x:A")] IDEAL_GENERATED_ADJOIN_EXPLICIT) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN MP_TAC (← ISPEC (← q r"subring_generated k (a:A->bool)") RING_IDEAL_CARRIER) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MATCH_MP_TAC r9 THEN CONJ_TAC THENL [SUBGOAL_THEN (← q r"x = ring_mul k x (ring_1 k:A)") SUBST1_TAC THENL [ASM_SIMP_TAC [RING_MUL_RID], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"subring_generated k ((y:A) INSERT a)"), (← q r"ideal_generated (subring_generated k ((y:A) INSERT a)) a"), (← q r"x:A"), (← q r"ring_1 k:A")] IN_RING_IDEAL_LMUL) THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, (← CONJUNCT2 SUBRING_GENERATED)] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [SUBSET] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN ASM_REWRITE_TAC [IN_INSERT] THEN UNDISCH_TAC (← q r"(a:A->bool) SUBSET ring_carrier k") THEN REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"n:num") (X_CHOOSE_THEN (← q r"c:num->A") (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))) THEN SUBGOAL_THEN (← q r"!i. (c:num->A) i IN a /\ c i IN ring_carrier k") ASSUME_TAC THENL [GEN_TAC THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"(a:A->bool) SUBSET ring_carrier k") THEN REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_pow k x (SUC n) =
      ring_sum k (0..n) (\i. ring_mul k ((c:num->A) i) (ring_pow k x (n - i)))") ASSUME_TAC THENL [TRANS_TAC EQ_TRANS (← q r"ring_mul k (ring_pow k x n)
         (ring_sum k (0..n)
           (\i. ring_mul k ((c:num->A) i) (ring_pow k (y:A) i)))") THEN CONJ_TAC THENL [FIRST_X_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← (do let z2 ← (pure th); checkM (fun th => (do if ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); pure (is_eq z3)) then (do let z8 ← (q r"x:A"); let z7 ← (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); liftExcept (rand z5)); pure (z7 == z8)) else pure false)) z2))])) THEN REWRITE_TAC [ring_pow] THEN MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC [RING_POW], ALL_TAC] THEN wPart lhand (rand o rand) RING_SUM_LMUL THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_NUMSEG, RING_MUL, RING_POW], ALL_TAC] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"i:num") THEN REWRITE_TAC [IN_NUMSEG] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_pow k (x:A) n = ring_mul k (ring_pow k x (n - i)) (ring_pow k x i)") SUBST1_TAC THENL [ASM_SIMP_TAC [(← GSYM RING_POW_ADD)] THEN AP_TERM_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN ASM_SIMP_TAC [RING_POW, r1], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_pow k x (SUC n) =
      ring_sum k (0..n) (\j. ring_mul k ((c:num->A) (n - j)) (ring_pow k x j))") ASSUME_TAC THENL [FIRST_X_ASSUM SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"\i. ring_mul k ((c:num->A) i) (ring_pow k (x:A) (n - i))"), (← q r"0"), (← q r"n:num")] RING_SUM_REFLECT) THEN ANTS_TAC THENL [REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL THEN ASM_SIMP_TAC [RING_POW], REWRITE_TAC [LT, SUB_0]] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"j:num") THEN REWRITE_TAC [IN_NUMSEG] THEN STRIP_TAC THEN REWRITE_TAC [] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"subring_generated k (a:A->bool)"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"x:A")] INTEGRAL_ELEMENT_EXPLICIT) THEN REWRITE_TAC [I_DEF, RING_HOMOMORPHISM_INCLUSION] THEN REWRITE_TAC [(← GSYM I_DEF), I_THM] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"SUC n") THEN EXISTS_TAC (← q r"\j. ring_neg k ((c:num->A) (n - j))") THEN ASM_SIMP_TAC [LT_0, RING_NEG_IN_SUBRING_GENERATED, SUBRING_GENERATED_INC_GEN, RING_NEG] THEN REWRITE_TAC [NUMSEG_LT, NOT_SUC, SUC_SUB1] THEN ASM_SIMP_TAC [RING_MUL_LNEG, RING_MUL, RING_POW] THEN ASM_SIMP_TAC [RING_SUM_NEG, FINITE_NUMSEG, RING_MUL, RING_POW] THEN ASM_SIMP_TAC [(← GSYM ring_sub), RING_SUB_EQ_0, RING_SUM, RING_POW] THEN ASM_MESON_TAC [])

  let INTEGRAL_HOMOGENEOUS_SCALE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul r c (ring_mul r (ring_mul r p a) (ring_mul r q b)) =
    ring_mul r (ring_mul r p q) (ring_mul r c (ring_mul r a (b:A)))")
    prove
      r"!r:A ring p a b c n.
          p IN ring_carrier r /\ a IN ring_carrier r /\ b IN ring_carrier r /\
          (!i. i < n ==> c i IN ring_carrier r)
          ==> ring_add r (ring_pow r (ring_mul r p a) n)
                (ring_sum r {i | i < n}
                   (\i. ring_mul r (c i)
                          (ring_mul r (ring_pow r (ring_mul r p a) i)
                                      (ring_pow r (ring_mul r p b) (n - i))))) =
              ring_mul r (ring_pow r p n)
                (ring_add r (ring_pow r a n)
                   (ring_sum r {i | i < n}
                      (\i. ring_mul r (c i)
                             (ring_mul r (ring_pow r a i)
                                         (ring_pow r b (n - i))))))"
      (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [RING_ADD_LDISTRIB, RING_POW, RING_SUM, RING_MUL_POW] THEN AP_TERM_TAC THEN wPart rand (rand o rand) RING_SUM_LMUL THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, RING_MUL, RING_POW] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"i:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_pow r p n = ring_mul r (ring_pow r p i) (ring_pow r (p:A) (n - i))") SUBST1_TAC THENL [ASM_SIMP_TAC [(← GSYM RING_POW_ADD)] THEN AP_TERM_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [RING_POW])

  let INTEGRAL_HOMOGENEOUS_HOMOMORPHIC_IMAGE ← prove
    r"!r:A ring t:B ring f a b c n.
        ring_homomorphism(r,t) f /\
        a IN ring_carrier r /\ b IN ring_carrier r /\
        (!i. i < n ==> c i IN ring_carrier r)
        ==> f(ring_add r (ring_pow r a n)
                (ring_sum r {i | i < n}
                   (\i. ring_mul r (c i)
                          (ring_mul r (ring_pow r a i)
                                      (ring_pow r b (n - i)))))) =
            ring_add t (ring_pow t (f a) n)
              (ring_sum t {i | i < n}
                 (\i. ring_mul t (f(c i))
                        (ring_mul t (ring_pow t (f a) i)
                                    (ring_pow t (f b) (n - i)))))"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_ADD th), (← MATCH_MP RING_HOMOMORPHISM_POW th), RING_POW, RING_SUM])) THEN AP_TERM_TAC THEN FIRST_ASSUM (fun th => tactic_of do pure (wPart lhand (lhand o rand) (← MATCH_MP RING_HOMOMORPHISM_SUM th))) THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, RING_MUL, RING_POW] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"i:num") THEN REWRITE_TAC [IN_ELIM_THM, o_THM] THEN DISCH_TAC THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL th), (← MATCH_MP RING_HOMOMORPHISM_POW th), RING_POW, RING_MUL])))

  let RING_REGULAR_MUL_EQ_0 ← prove
    r"!r a x:A.
        ring_regular r a /\ x IN ring_carrier r
        ==> (ring_mul r a x = ring_0 r <=> x = ring_0 r)"
    (REWRITE_TAC [ring_regular, ring_zerodivisor] THEN MESON_TAC [RING_MUL_RZERO])

  let INTEGRAL_HOMOGENEOUS_CLEAR ← prove
    r"!t:B ring x u d n.
        x IN ring_carrier t /\ ring_regular t u /\
        (!i. i < n ==> d i IN ring_carrier t)
        ==> (ring_add t (ring_pow t (ring_mul t x u) n)
               (ring_sum t {i | i < n}
                  (\i. ring_mul t (d i)
                         (ring_mul t (ring_pow t (ring_mul t x u) i)
                                     (ring_pow t u (n - i))))) = ring_0 t <=>
             ring_add t (ring_pow t x n)
               (ring_sum t {i | i < n}
                  (\i. ring_mul t (d i) (ring_pow t x i))) = ring_0 t)"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"(u:B) IN ring_carrier t") ASSUME_TAC THENL [ASM_MESON_TAC [ring_regular], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"t:B ring"), (← q r"u:B"), (← q r"x:B"), (← q r"ring_1 t:B"), (← q r"d:num->B"), (← q r"n:num")] INTEGRAL_HOMOGENEOUS_SCALE) THEN ASM_SIMP_TAC [RING_MUL_RID, RING_1, RING_POW_ONE] THEN SUBGOAL_THEN (← q r"ring_mul t u x = ring_mul t x (u:B)") SUBST1_TAC THENL [ASM_MESON_TAC [RING_MUL_SYM], DISCH_THEN SUBST1_TAC] THEN SUBGOAL_THEN (← q r"ring_sum t {i | i < n}
      (\i. ring_mul t ((d:num->B) i)
             (ring_mul t (ring_pow t x i) (ring_1 t))) =
    ring_sum t {i | i < n} (\i. ring_mul t (d i) (ring_pow t x i))") SUBST1_TAC THENL [MATCH_MP_TAC RING_SUM_EQ THEN SIMP_TAC [IN_ELIM_THM] THEN ASM_SIMP_TAC [RING_MUL_RID, RING_POW], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_regular t (ring_pow t (u:B) n)") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_REGULAR_POW], ALL_TAC] THEN ASM_SIMP_TAC [RING_REGULAR_MUL_EQ_0, RING_ADD, RING_POW, RING_SUM])

  let INTEGRAL_UFD_HOMOGENEOUS_DIVIDES ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"i < n ==> ~(n - i = 0)")
    prove
      r"!r:A ring a b c n.
          UFD r /\ a IN ring_carrier r /\ b IN ring_carrier r /\
          (!i. i < n ==> c i IN ring_carrier r) /\
          ring_add r (ring_pow r a n)
            (ring_sum r {i | i < n}
               (\i. ring_mul r (c i)
                      (ring_mul r (ring_pow r a i) (ring_pow r b (n - i))))) =
          ring_0 r
          ==> ring_divides r b a"
      (GEN_TAC THEN SUBGOAL_THEN (← q r"UFD (r:A ring)
      ==> !b. b IN ring_carrier r
              ==> !a c n. a IN ring_carrier r /\
                          (!i. i < n ==> c i IN ring_carrier r) /\
                          ring_add r (ring_pow r a n)
                            (ring_sum r {i | i < n}
                               (\i. ring_mul r (c i)
                                      (ring_mul r (ring_pow r a i)
                                                  (ring_pow r b (n - i))))) =
                          ring_0 r
                          ==> ring_divides r b a") (fun th => MESON_TAC [th]) THEN DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP UFD_IMP_INTEGRAL_DOMAIN)) THEN MATCH_MP_TAC UFD_PRIME_FACTOR_INDUCT THEN ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL [MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"c:num->A"), (← q r"n:num")] THEN STRIP_TAC THEN REWRITE_TAC [RING_DIVIDES_ZERO] THEN UNDISCH_TAC (← q r"ring_add r (ring_pow r a n)
          (ring_sum r {i | i < n}
            (\i. ring_mul r ((c:num->A) i)
                   (ring_mul r (ring_pow r a i)
                               (ring_pow r (ring_0 r) (n - i))))) =
        ring_0 r") THEN SUBGOAL_THEN (← q r"ring_sum r {i | i < n}
          (\i. ring_mul r ((c:num->A) i)
                 (ring_mul r (ring_pow r a i)
                             (ring_pow r (ring_0 r) (n - i)))) = ring_0 r") SUBST1_TAC THENL [MATCH_MP_TAC RING_SUM_EQ_0 THEN ASM_SIMP_TAC [IN_ELIM_THM, RING_POW_ZERO, r1, RING_MUL_RZERO, RING_POW], ASM_SIMP_TAC [RING_ADD_RZERO, RING_POW, INTEGRAL_DOMAIN_POW_EQ_0]], MESON_TAC [RING_UNIT_DIVIDES_ANY], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"p:A"), (← q r"b:A")] THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"c:num->A"), (← q r"n:num")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(p:A) IN ring_carrier r /\ ~(p = ring_0 r)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [ring_prime], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_divides r p (a:A)") MP_TAC THENL [MATCH_MP_TAC RING_PRIME_DIVIDES_POW THEN EXISTS_TAC (← q r"n:num") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ring_pow r a n =
        ring_neg r (ring_sum r {i | i < n}
         (\i. ring_mul r ((c:num->A) i)
               (ring_mul r (ring_pow r a i)
                           (ring_pow r (ring_mul r p b) (n - i)))))") SUBST1_TAC THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_RNEG_UNIQUE THEN ASM_SIMP_TAC [RING_POW, RING_SUM], MATCH_MP_TAC RING_DIVIDES_NEG] THEN MATCH_MP_TAC RING_SUM_CLOSED THEN SIMP_TAC [RING_DIVIDES_0, RING_DIVIDES_ADD] THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"i:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN REPEAT (MATCH_MP_TAC RING_DIVIDES_LMUL THEN ASM_SIMP_TAC [RING_POW, RING_MUL]) THEN SUBGOAL_THEN (← q r"n - i = SUC(n - i - 1)") SUBST1_TAC THENL [ASM_ARITH_TAC, REWRITE_TAC [ring_pow]] THEN ASM_SIMP_TAC [RING_MUL_POW, RING_POW] THEN MATCH_MP_TAC RING_DIVIDES_RMUL THEN ASM_SIMP_TAC [RING_POW, RING_MUL] THEN ASM_SIMP_TAC [RING_DIVIDES_RMUL, RING_DIVIDES_REFL], GEN_REWRITE_TAC LAND_CONV [ring_divides] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"a':A") STRIP_ASSUME_TAC) o (CONJUNCT2 o CONJUNCT2)) THEN FIRST_X_ASSUM SUBST_ALL_TAC] THEN MATCH_MP_TAC RING_DIVIDES_LMUL2 THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"c:num->A"), (← q r"n:num")] THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A"), (← q r"a':A"), (← q r"b:A"), (← q r"c:num->A"), (← q r"n:num")] INTEGRAL_HOMOGENEOUS_SCALE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o SYM) THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_MUL_EQ_0, RING_POW, RING_ADD, RING_SUM, INTEGRAL_DOMAIN_POW_EQ_0])

  let INTEGRAL_HOMOGENEOUS_RELATION ← prove
    r"!r:A ring t:B ring f a b x c n.
        ring_homomorphism(r,t) f /\
        a IN ring_carrier r /\ b IN ring_carrier r /\ x IN ring_carrier t /\
        ring_regular t (f b) /\ ring_mul t x (f b) = f a /\
        (!i. i < n ==> c i IN ring_carrier r)
        ==> (f(ring_add r (ring_pow r a n)
                (ring_sum r {i | i < n}
                   (\i. ring_mul r (c i)
                          (ring_mul r (ring_pow r a i)
                                      (ring_pow r b (n - i)))))) = ring_0 t <=>
             ring_add t (ring_pow t x n)
               (ring_sum t {i | i < n}
                  (\i. ring_mul t (f(c i)) (ring_pow t x i))) = ring_0 t)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"t:B ring"), (← q r"f:A->B"), (← q r"a:A"), (← q r"b:A"), (← q r"c:num->A"), (← q r"n:num")] INTEGRAL_HOMOGENEOUS_HOMOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN MATCH_MP_TAC INTEGRAL_HOMOGENEOUS_CLEAR THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER])

  let INTEGRAL_MONOMORPHISM_IN_IMAGE ← prove
    r"!r:A ring t:B ring f a b x.
        ring_monomorphism(r,t) f /\
        a IN ring_carrier r /\ b IN ring_carrier r /\ x IN ring_carrier t /\
        ring_regular t (f b) /\ ring_mul t x (f b) = f a
        ==> (x IN IMAGE f (ring_carrier r) <=> ring_divides r b a)"
    (REWRITE_TAC [ring_monomorphism] THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"!d. d IN ring_carrier r ==> (f:A->B) d IN ring_carrier t") ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN SUBGOAL_THEN (← q r"!d. d IN ring_carrier r
        ==> (f:A->B)(ring_mul r b d) = ring_mul t (f b) (f d)") ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_MUL], ALL_TAC] THEN REWRITE_TAC [IN_IMAGE, ring_divides] THEN ASM_REWRITE_TAC [] THEN EQ_TAC THEN DISCH_THEN (X_CHOOSE_THEN (← q r"d:A") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"d:A") THEN ASM_REWRITE_TAC [] THENL [FIRST_X_ASSUM (MATCH_MP_TAC o (checkM (fun z7 => (do let z8 ← (do let z9 ← (pure z7); pure (concl z9)); pure (is_forall z8))))) THEN ASM_SIMP_TAC [RING_MUL] THEN UNDISCH_TAC (← q r"ring_mul t x ((f:A->B) b) = f a") THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC [], SUBGOAL_THEN (← q r"ring_mul t ((f:A->B) b) (ring_sub t x (f d)) = ring_0 t") MP_TAC THENL [ASM_SIMP_TAC [RING_SUB_LDISTRIB] THEN SUBGOAL_THEN (← q r"ring_mul t ((f:A->B) b) x = f a") SUBST1_TAC THENL [ASM_MESON_TAC [RING_MUL_SYM], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"d:A")) o (checkM (fun z4 => (do let z5 ← (do let z6 ← (pure z4); pure (concl z6)); pure (is_forall z5)))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun z1 => (do let z2 ← (do let z3 ← (pure z1); pure (concl z3)); pure (is_eq z2)))))) THEN MATCH_MP_TAC RING_SUB_REFL THEN ASM_SIMP_TAC [RING_MUL], ASM_SIMP_TAC [RING_REGULAR_MUL_EQ_0, RING_SUB, RING_SUB_EQ_0]]])

  let INTEGRAL_FRACTION_RING_DENOMINATOR ← prove
    r"!r (x:(A#A)->bool).
        x IN ring_carrier(fraction_ring r)
        ==> ?a b. a IN ring_carrier r /\ ring_regular r b /\
                  ring_regular (fraction_ring r)
                    (ring_fractionate r {a | ring_regular r a} b) /\
                  ring_mul (fraction_ring r) x
                    (ring_fractionate r {a | ring_regular r a} b) =
                  ring_fractionate r {a | ring_regular r a} a"
    (REWRITE_TAC [fraction_ring] THEN SIMP_TAC [RING_LOCALIZATION_CARRIER, RING_MULTSYS_REGULAR] THEN REWRITE_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"r:A ring"), (← q r"x:(A#A)->bool"), (← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"a:A"), (← q r"b:A")] THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [MATCH_MP_TAC RING_UNIT_IMP_REGULAR THEN MATCH_MP_TAC RING_UNIT_FRACTIONATE THEN ASM_REWRITE_TAC [RING_MULTSYS_REGULAR, IN_ELIM_THM], MATCH_MP_TAC LOCALEQUIV_MUL_LCANCEL THEN ASM_REWRITE_TAC [RING_MULTSYS_REGULAR, IN_ELIM_THM]])

  let INTEGRAL_FRACTION_RING_RELATION ← prove
    r"!r (x:(A#A)->bool).
        integral_element
          (r,fraction_ring r) (ring_fractionate r {a | ring_regular r a}) x
        ==> ?a b c n. a IN ring_carrier r /\ ring_regular r b /\
                      ring_regular (fraction_ring r)
                        (ring_fractionate r {a | ring_regular r a} b) /\
                      ring_mul (fraction_ring r) x
                        (ring_fractionate r {a | ring_regular r a} b) =
                      ring_fractionate r {a | ring_regular r a} a /\
                      (!i. i < n ==> c i IN ring_carrier r) /\
                      ring_add r (ring_pow r a n)
                        (ring_sum r {i | i < n}
                          (\i. ring_mul r (c i)
                                 (ring_mul r (ring_pow r a i)
                                             (ring_pow r b (n - i))))) =
                      ring_0 r"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"r:A ring") RING_MONOMORPHISM_FRACTIONATE) THEN REWRITE_TAC [RING_MONOMORPHISM_ALT] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"x:(A#A)->bool")] INTEGRAL_FRACTION_RING_DENOMINATOR) THEN ANTS_TAC THENL [ASM_MESON_TAC [INTEGRAL_ELEMENT_IN_CARRIER], ALL_TAC] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"fraction_ring r:((A#A)->bool) ring"), (← q r"ring_fractionate r {a:A | ring_regular r a}"), (← q r"x:(A#A)->bool")] INTEGRAL_ELEMENT_RELATION) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"n:num"), (← q r"c:num->A")] THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"a:A"), (← q r"b:A"), (← q r"c:num->A"), (← q r"n:num")] THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN SUBGOAL_THEN (← q r"(b:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_REGULAR_IN_CARRIER], ALL_TAC] THEN ASM_SIMP_TAC [RING_ADD, RING_POW, RING_SUM] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"fraction_ring r:((A#A)->bool) ring"), (← q r"ring_fractionate r {a:A | ring_regular r a}"), (← q r"a:A"), (← q r"b:A"), (← q r"x:(A#A)->bool"), (← q r"c:num->A"), (← q r"n:num")] INTEGRAL_HOMOGENEOUS_RELATION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC [INTEGRAL_ELEMENT_IN_CARRIER])

  let INTEGRALLY_CLOSED_ALT ← prove
    r"!r:A ring.
        integrally_closed r <=>
        integral_domain r /\
        !a b c n.
          a IN ring_carrier r /\ b IN ring_carrier r /\ ~(b = ring_0 r) /\
          (!i. i < n ==> c i IN ring_carrier r) /\
          ring_add r (ring_pow r a n)
            (ring_sum r {i | i < n}
               (\i. ring_mul r (c i)
                      (ring_mul r (ring_pow r a i) (ring_pow r b (n - i))))) =
          ring_0 r
          ==> ring_divides r b a"
    (GEN_TAC THEN REWRITE_TAC [integrally_closed] THEN ASM_CASES_TAC (← q r"integral_domain(r:A ring)") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPEC (← q r"r:A ring") RING_MONOMORPHISM_FRACTIONATE) THEN DISCH_THEN (fun th => tactic_of do pure (ASSUME_TAC th THEN ASSUME_TAC (← MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM th))) THEN EQ_TAC THEN DISCH_TAC THENL [MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A"), (← q r"c:num->A"), (← q r"n:num")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_regular r (b:A)") ASSUME_TAC THENL [ASM_SIMP_TAC [INTEGRAL_DOMAIN_REGULAR], ALL_TAC] THEN ABBREV_TAC (← q r"x = ring_localequiv r {a:A | ring_regular r a} (a,b)") THEN SUBGOAL_THEN (← q r"x IN ring_carrier(fraction_ring r) /\
      ring_regular (fraction_ring r)
        (ring_fractionate r {a:A | ring_regular r a} b) /\
      ring_mul (fraction_ring r) x
        (ring_fractionate r {a:A | ring_regular r a} b) =
      ring_fractionate r {a | ring_regular r a} a") STRIP_ASSUME_TAC THENL [EXPAND_TAC "x" THEN REWRITE_TAC [fraction_ring] THEN ASM_SIMP_TAC [RING_LOCALEQUIV_IN_CARRIER, RING_MULTSYS_REGULAR, IN_ELIM_THM, LOCALEQUIV_MUL_LCANCEL] THEN MATCH_MP_TAC RING_UNIT_IMP_REGULAR THEN MATCH_MP_TAC RING_UNIT_FRACTIONATE THEN ASM_REWRITE_TAC [RING_MULTSYS_REGULAR, IN_ELIM_THM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"fraction_ring r:((A#A)->bool) ring"), (← q r"ring_fractionate r {a:A | ring_regular r a}"), (← q r"a:A"), (← q r"b:A"), (← q r"x:(A#A)->bool")] INTEGRAL_MONOMORPHISM_IN_IMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC INTEGRAL_ELEMENT_FROM_RELATION THEN MAP_EVERY EXISTS_TAC [(← q r"n:num"), (← q r"c:num->A")] THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"fraction_ring r:((A#A)->bool) ring"), (← q r"ring_fractionate r {a:A | ring_regular r a}"), (← q r"a:A"), (← q r"b:A"), (← q r"x:(A#A)->bool"), (← q r"c:num->A"), (← q r"n:num")] INTEGRAL_HOMOGENEOUS_RELATION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_MESON_TAC [RING_HOMOMORPHISM_0], X_GEN_TAC (← q r"x:(A#A)->bool") THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP INTEGRAL_FRACTION_RING_RELATION)) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A"), (← q r"c:num->A"), (← q r"n:num")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(b:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_REGULAR_IN_CARRIER], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"fraction_ring r:((A#A)->bool) ring"), (← q r"ring_fractionate r {a:A | ring_regular r a}"), (← q r"a:A"), (← q r"b:A"), (← q r"x:(A#A)->bool")] INTEGRAL_MONOMORPHISM_IN_IMAGE) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [ASM_MESON_TAC [INTEGRAL_ELEMENT_IN_CARRIER], DISCH_THEN SUBST1_TAC] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"c:num->A"), (← q r"n:num")] THEN ASM_MESON_TAC [INTEGRAL_DOMAIN_REGULAR]])

  let UFD_IMP_INTEGRALLY_CLOSED ← prove
    r"!r:A ring. UFD r ==> integrally_closed r"
    (SIMP_TAC [INTEGRALLY_CLOSED_ALT, UFD_IMP_INTEGRAL_DOMAIN] THEN MESON_TAC [INTEGRAL_UFD_HOMOGENEOUS_DIVIDES])

  let PID_IMP_INTEGRALLY_CLOSED ← prove
    r"!r:A ring. PID r ==> integrally_closed r"
    (SIMP_TAC [PID_IMP_UFD, UFD_IMP_INTEGRALLY_CLOSED])

  let FIELD_IMP_INTEGRALLY_CLOSED ← prove
    r"!r:A ring. field r ==> integrally_closed r"
    (SIMP_TAC [FIELD_IMP_PID, PID_IMP_INTEGRALLY_CLOSED])

  let INTEGRALLY_CLOSED_INTEGER_RING ← prove
    r"integrally_closed integer_ring"
    (SIMP_TAC [UFD_INTEGER_RING, UFD_IMP_INTEGRALLY_CLOSED])

  let INTEGRAL_ELEMENT_PRIME_SUBFIELD ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"q /\ (p ==> r) ==> (p <=> q) ==> r")
    prove
      r"!k:A ring x.
          field k /\ ring_char k = 0 /\
          x IN ring_carrier(subfield_generated k {ring_0 k}) /\
          integral_element (integer_ring,k) (ring_of_int k) x
          ==> ?n. x = ring_of_int k n"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{ring_0 k:A}"), (← q r"x:A")] SUBFIELD_GENERATED_QUOTIENTS) THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, RING_CARRIER_SUBRING_GENERATED_0] THEN REWRITE_TAC [IN_ELIM_THM, IN_UNIV] THEN REWRITE_TAC [LEFT_AND_EXISTS_THM, RIGHT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a':A"), (← q r"b':A"), (← q r"a:int"), (← q r"b:int")] THEN DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN REPEAT (FIRST_X_ASSUM (SUBST_ALL_TAC o (checkM (fun z2 => (do let z3 ← (do let z4 ← (do let z5 ← (pure z2); pure (concl z5)); liftExcept (lhs z4)); pure (is_var z3)))))) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN)) THEN SUBGOAL_THEN (← q r"ring_monomorphism(integer_ring,k) (ring_of_int k:int->A)") ASSUME_TAC THENL [ASM_REWRITE_TAC [RING_MONOMORPHISM_INTEGER_RING_OF_INT], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_regular k (ring_of_int k (b:int):A) /\
      ring_mul k x (ring_of_int k b) = ring_of_int k a") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [INTEGRAL_DOMAIN_REGULAR, RING_OF_INT] THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN REWRITE_TAC [ring_div] THEN SUBGOAL_THEN (← q r"ring_unit k (ring_of_int k (b:int):A)") ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_UNIT, RING_OF_INT], ALL_TAC] THEN ASM_SIMP_TAC [(← GSYM RING_MUL_ASSOC), RING_OF_INT, RING_INV, RING_MUL_LINV, RING_MUL_RID], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"k:A ring"), (← q r"ring_of_int k:int->A"), (← q r"a:int"), (← q r"b:int"), (← q r"x:A")] INTEGRAL_MONOMORPHISM_IN_IMAGE) THEN ASM_REWRITE_TAC [(← CONJUNCT1 INTEGER_RING), IN_UNIV] THEN ANTS_TAC THENL [ASM_MESON_TAC [INTEGRAL_ELEMENT_IN_CARRIER], ALL_TAC] THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [ALL_TAC, REWRITE_TAC [IN_IMAGE] THEN MESON_TAC []] THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"k:A ring"), (← q r"ring_of_int k:int->A"), (← q r"x:A")] INTEGRAL_ELEMENT_RELATION) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"n:num"), (← q r"c:num->int")] THEN STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UFD_HOMOGENEOUS_DIVIDES THEN MAP_EVERY EXISTS_TAC [(← q r"c:num->int"), (← q r"n:num")] THEN REWRITE_TAC [UFD_INTEGER_RING, (← CONJUNCT1 INTEGER_RING), IN_UNIV] THEN UNDISCH_TAC (← q r"ring_monomorphism(integer_ring,k) (ring_of_int k:int->A)") THEN REWRITE_TAC [RING_MONOMORPHISM_ALT] THEN DISCH_THEN (MATCH_MP_TAC o CONJUNCT2) THEN REWRITE_TAC [(← CONJUNCT1 INTEGER_RING), IN_UNIV] THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"k:A ring"), (← q r"ring_of_int k:int->A"), (← q r"a:int"), (← q r"b:int"), (← q r"x:A"), (← q r"c:num->int"), (← q r"n:num")] INTEGRAL_HOMOGENEOUS_RELATION) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, (← CONJUNCT1 INTEGER_RING), IN_UNIV] THEN ANTS_TAC THENL [ASM_MESON_TAC [INTEGRAL_ELEMENT_IN_CARRIER], ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [])

  let INTEGRALLY_CLOSED_INTEGRAL_CLOSURE ← prove
    r"!r:A ring l:B ring h.
        field l /\ ring_homomorphism(r,l) h
        ==> integrally_closed
              (subring_generated l {x | integral_element (r,l) h x})"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"!x. integral_element
          (subring_generated l {x | integral_element (r,l) h x},l) I x
        ==> x IN {x | integral_element (r:A ring,l:B ring) h x}") MP_TAC THENL [REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [INTEGRAL_CLOSURE_IDEMPOT], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] INTEGRAL_CLOSURE_SUBRING) THEN ASM_REWRITE_TAC [] THEN SPEC_TAC ((← q r"{x | integral_element (r:A ring,l:B ring) h x}"), (← q r"s:B->bool")) THEN GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN ABBREV_TAC (← q r"R = subring_generated l (s:B->bool)") THEN SUBGOAL_THEN (← q r"ring_carrier R = (s:B->bool) /\ ring_0 R = ring_0 l /\
    ring_mul R = ring_mul l /\ ring_homomorphism (R,l) (I:B->B)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "R" THEN SIMP_TAC [(← ASSUME (← q r"(s:B->bool) subring_of l")), CARRIER_SUBRING_GENERATED_SUBRING] THEN REWRITE_TAC [SUBRING_GENERATED, I_DEF, RING_HOMOMORPHISM_INCLUSION], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x:B. x IN s ==> x IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [subring_of, SUBSET], ALL_TAC] THEN REWRITE_TAC [INTEGRALLY_CLOSED_ALT] THEN CONJ_TAC THENL [EXPAND_TAC "R" THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_SUBRING_GENERATED, FIELD_IMP_INTEGRAL_DOMAIN], ASM_REWRITE_TAC []] THEN MAP_EVERY X_GEN_TAC [(← q r"a:B"), (← q r"b:B"), (← q r"c:num->B"), (← q r"n:num")] THEN STRIP_TAC THEN ABBREV_TAC (← q r"y = ring_mul l a (ring_inv l (b:B))") THEN SUBGOAL_THEN (← q r"(y:B) IN ring_carrier l /\ ring_mul l y b = a") STRIP_ASSUME_TAC THENL [EXPAND_TAC "y" THEN SUBGOAL_THEN (← q r"ring_unit l (b:B)") ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_UNIT], ALL_TAC] THEN ASM_SIMP_TAC [RING_MUL, RING_INV, (← GSYM RING_MUL_ASSOC), RING_MUL_LINV, RING_MUL_RID], ALL_TAC] THEN REWRITE_TAC [ring_divides] THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"y:B") THEN CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC INTEGRAL_ELEMENT_FROM_RELATION THEN MAP_EVERY EXISTS_TAC [(← q r"n:num"), (← q r"c:num->B")] THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"R:B ring"), (← q r"l:B ring"), (← q r"I:B->B"), (← q r"a:B"), (← q r"b:B"), (← q r"y:B"), (← q r"c:num->B"), (← q r"n:num")] INTEGRAL_HOMOGENEOUS_RELATION) THEN ASM_REWRITE_TAC [I_THM] THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_REGULAR, FIELD_IMP_INTEGRAL_DOMAIN], ASM_MESON_TAC [RING_MUL_SYM]])

  let INTEGRALLY_CLOSED_DIVIDES ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"ring_sum r s g = ring_neg r (ring_sum r s f)
    ==> ring_add r (ring_sum r (s:num->bool) f) (ring_sum r s g) =
        ring_0 (r:A ring)"
    let r2 ← MESON [RING_ADD_RNEG, RING_SUM] q1
    let q3 ← q r"n:num"
    let q4 ← q r"\i. ring_neg r ((c:num->A) i)"
    prove
      r"!r (a:A) b n c.
          integrally_closed r /\
          a IN ring_carrier r /\ b IN ring_carrier r /\ ~(b = ring_0 r) /\
          (!i. i < n ==> c(i) IN ring_carrier r) /\
          ring_pow r a n =
            ring_sum r {i | i < n}
              (\i. ring_mul r (c i)
                     (ring_mul r (ring_pow r a i) (ring_pow r b (n - i))))
          ==> ring_divides r b a"
      (REWRITE_TAC [INTEGRALLY_CLOSED_ALT] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [q4, q3] THEN ASM_SIMP_TAC [RING_NEG] THEN MATCH_MP_TAC r2 THEN wPart rand (rand o rand) RING_SUM_NEG THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, RING_MUL, RING_POW] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC [IN_ELIM_THM, RING_MUL_LNEG, RING_MUL, RING_POW])

  let INTEGRAL_ELEMENT_FRACTION_IN_IMAGE ← prove
    r"!(r:A ring) (w:W ring) u y.
        PID r /\ field w /\ ring_monomorphism(r,w) u /\
        (?p q. p IN ring_carrier r /\ q IN ring_carrier r /\
               ~(q = ring_0 r) /\ ring_mul w (u q) y = u p) /\
        integral_element (r,w) u y
        ==> y IN IMAGE u (ring_carrier r)"
    (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"p:A") (X_CHOOSE_THEN (← q r"q:A") STRIP_ASSUME_TAC)) MP_TAC)))) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [ring_monomorphism]))) THEN ASM_SIMP_TAC [INTEGRAL_ELEMENT_EXPLICIT] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"n:num") (X_CHOOSE_THEN (← q r"c:num->A") STRIP_ASSUME_TAC))) THEN SUBGOAL_THEN (← q r"ring_regular w ((u:A->W) q)") ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_REGULAR, RING_HOMOMORPHISM_IN_CARRIER] THEN ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0, RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"w:W ring"), (← q r"u:A->W"), (← q r"p:A"), (← q r"q:A"), (← q r"y:W")] INTEGRAL_MONOMORPHISM_IN_IMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [RING_MUL_SYM] THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_IN_CARRIER] THEN ASM_MESON_TAC [RING_MUL_SYM, RING_HOMOMORPHISM_IN_CARRIER], DISCH_THEN SUBST1_TAC] THEN MATCH_MP_TAC INTEGRAL_UFD_HOMOGENEOUS_DIVIDES THEN MAP_EVERY EXISTS_TAC [(← q r"c:num->A"), (← q r"n:num")] THEN ASM_SIMP_TAC [PID_IMP_UFD] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"w:W ring"), (← q r"u:A->W"), (← q r"p:A"), (← q r"q:A"), (← q r"y:W"), (← q r"c:num->A"), (← q r"n:num")] INTEGRAL_HOMOGENEOUS_RELATION) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [RING_MUL_SYM, RING_HOMOMORPHISM_IN_CARRIER], ASM_REWRITE_TAC [] THEN DISCH_TAC THEN W (fun (_asl, w) => tactic_of do pure (MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"w:W ring"), (← q r"u:A->W"), (← (do let z1 ← (pure w); liftExcept (lhs z1)))] RING_MONOMORPHISM_EQ_0))) THEN ASM_SIMP_TAC [RING_ADD, RING_POW, RING_SUM]])

  let INTEGRALLY_CLOSED_INTEGRAL_IMAGE ← prove
    r"!(r:A ring) (l:C ring) h y.
        integrally_closed r /\ ring_monomorphism(fraction_ring r,l) h /\
        y IN IMAGE h (ring_carrier(fraction_ring r)) /\
        integral_element (r,l) (h o ring_fractionate r {a | ring_regular r a})
                         y
        ==> y IN IMAGE (h o ring_fractionate r {a | ring_regular r a})
                       (ring_carrier r)"
    (REPEAT GEN_TAC THEN REWRITE_TAC [IN_IMAGE] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"q:A#A->bool") STRIP_ASSUME_TAC) MP_TAC))) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"fraction_ring(r:A ring)"), (← q r"l:C ring"), (← q r"ring_fractionate (r:A ring) {a | ring_regular r a}"), (← q r"h:(A#A->bool)->C"), (← q r"q:A#A->bool")] INTEGRAL_ELEMENT_MONOMORPHIC_PREIMAGE) THEN ASM_SIMP_TAC [RING_MONOMORPHISM_FRACTIONATE, RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"integrally_closed(r:A ring)") THEN REWRITE_TAC [integrally_closed] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"q:A#A->bool")) o CONJUNCT2)) THEN ASM_REWRITE_TAC [IN_IMAGE, o_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC [])

  -- @@RETURN BEGIN
  return { INTEGRAL_ELEMENT_IN_ADJOIN_INV, INTEGRAL_HOMOGENEOUS_SCALE,
           INTEGRAL_HOMOGENEOUS_HOMOMORPHIC_IMAGE, RING_REGULAR_MUL_EQ_0,
           INTEGRAL_HOMOGENEOUS_CLEAR, INTEGRAL_UFD_HOMOGENEOUS_DIVIDES,
           INTEGRAL_HOMOGENEOUS_RELATION, INTEGRAL_MONOMORPHISM_IN_IMAGE,
           INTEGRAL_FRACTION_RING_DENOMINATOR, INTEGRAL_FRACTION_RING_RELATION,
           INTEGRALLY_CLOSED_ALT, UFD_IMP_INTEGRALLY_CLOSED, PID_IMP_INTEGRALLY_CLOSED,
           FIELD_IMP_INTEGRALLY_CLOSED, INTEGRALLY_CLOSED_INTEGER_RING,
           INTEGRAL_ELEMENT_PRIME_SUBFIELD, INTEGRALLY_CLOSED_INTEGRAL_CLOSURE,
           INTEGRALLY_CLOSED_DIVIDES, INTEGRAL_ELEMENT_FRACTION_IN_IMAGE,
           INTEGRALLY_CLOSED_INTEGRAL_IMAGE }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- integral.ml phrases from line 1549 to 2060                             -/
/- ---------------------------------------------------------------------- -/

structure Integral03 where
  -- @@FIELDS
  RING_LOCALIZATION_COMMON_DENOMINATOR : thm
  INTEGRALLY_CLOSED_LOCALIZATION : thm
  INTEGRAL_ELEMENT_INTERMEDIATE : thm
  INTEGRAL_ELEMENT_MONIC_DIVISOR : thm
  INTEGRAL_ELEMENT_MINIMAL_POLYNOMIAL : thm
  ALGEBRA_TRACE_NORM_INTEGRAL : thm
  INTEGRALLY_CLOSED_FIELD_OF_FRACTIONS : thm
  INTEGRALLY_CLOSED_MINIMAL_POLYNOMIAL : thm
  INTEGRALLY_CLOSED_ALGEBRA_TRACE_NORM : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupIntegral03 [HolBase] (D : IntegralDeps) (BIntegral01 : Integral01) (BIntegral02 : Integral02) :
    ExceptT String IO Integral03 := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, RING_TAC, SET_TAC, TAUT, .. } := D
  let { ALGEBRAIC_OVER_IN_CARRIER, ALGEBRA_NORM_MINIMAL_POLYNOMIAL,
        ALGEBRA_TRACE_MINIMAL_POLYNOMIAL, CARRIER_SUBRING_GENERATED_SUBRING, COEFF,
        COEFF_COMPOSE, EQ_IMP, EQ_TRANS, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_IMP_NONTRIVIAL_RING, FIELD_MUL_LINV,
        FIELD_OF_FRACTIONS_IMP_INTEGRAL_DOMAIN, FINITE_IMAGE,
        FINITE_IMP_FIELD_EXTENSION, FINITE_INDUCT_STRONG, FINITE_INSERT,
        FINITE_NUMSEG_LT, FORALL_AND_THM, FORALL_IN_IMAGE, FORALL_IN_INSERT, IMP_CONJ,
        INSERT_SUBSET, INTEGRAL_DOMAIN_LOCALIZATION, INTEGRAL_DOMAIN_REGULAR,
        IN_ELIM_THM, IN_IMAGE, IN_RING_POLYNOMIAL_CARRIER_COMPOSE, IN_SUBRING_1,
        IN_SUBRING_MUL, IN_SUBRING_NEG, IN_SUBRING_NUM, IN_SUBRING_POW,
        LEFT_IMP_EXISTS_THM, LOCALEQUIV_MUL_RCANCEL, MINIMAL_POLYNOMIAL,
        MINIMAL_POLYNOMIAL_DIVIDES, MINIMAL_POLYNOMIAL_IN_CARRIER,
        MINIMAL_POLYNOMIAL_MONIC, MONIC_HOMOMORPHIC_IMAGE, MONIC_IMP_NONZERO,
        NOT_IN_EMPTY, POLY_DEG_MONOMORPHIC_IMAGE, POLY_EVAL, POLY_EVAL_MUL,
        POLY_EXTEND_EVALUATE, POLY_EXTEND_MONIC_UNIVARIATE, POLY_MONOMIAL_IN_CARRIER,
        POLY_RING_CLAUSES, POLY_SPLITS_IN_CARRIER, POLY_SPLITS_IN_SUBRING_MONIC,
        RIGHT_FORALL_IMP_THM, RIGHT_IMP_EXISTS_THM, RING_ADD, RING_ASSOCIATES_DIVIDES,
        RING_ASSOCIATES_EQ_0, RING_ASSOCIATES_LMUL, RING_ASSOCIATES_SYM,
        RING_ASSOCIATES_TRANS, RING_DIVIDES_HOMOMORPHIC_IMAGE, .. } := D.core1
  let { RING_FRACTIONATE_IN_CARRIER, RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_1,
        RING_HOMOMORPHISM_COMPOSE, RING_HOMOMORPHISM_FRACTIONATE,
        RING_HOMOMORPHISM_IN_CARRIER, RING_HOMOMORPHISM_MUL,
        RING_HOMOMORPHISM_POLY_RINGS, RING_HOMOMORPHISM_POW, RING_INV,
        RING_LOCALEQUIV_IN_CARRIER, RING_LOCALIZATION_CARRIER, RING_MONOMORPHISM_ALT,
        RING_MONOMORPHISM_EQ_0, RING_MONOMORPHISM_FRACTIONATE_GEN,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL, RING_MULTSYS, RING_MUL_ASSOC,
        RING_MUL_LZERO, RING_MUL_POW, RING_MUL_RID, RING_MUL_RZERO, RING_MUL_SYM,
        RING_POLYNOMIAL, RING_POW, RING_SUM, RING_SUM_EQ, RING_UNIT_FRACTIONATE,
        SKOLEM_THM, SPLITTING_EXTENSION_EXISTS_BIGENOUGH, SPLITTING_EXTENSION_SPLITS,
        SPLITTING_IMP_FIELD_EXTENSION, SUBSET, algebraic_over, field_extension,
        field_of_fractions, monic, o_ASSOC, o_THM, poly_eval, poly_splits_over,
        ring_divides, ring_multsys, ring_pow, .. } := D.core2
  let { INTEGRAL_CLOSURE_SUBRING, INTEGRAL_ELEMENT_EXPLICIT,
        INTEGRAL_ELEMENT_FROM_RELATION, INTEGRAL_ELEMENT_IN_CARRIER,
        INTEGRAL_ELEMENT_MONOMORPHIC_PREIMAGE, INTEGRAL_ELEMENT_RELATION,
        integral_element, .. } := BIntegral01
  let { INTEGRALLY_CLOSED_ALT, INTEGRAL_HOMOGENEOUS_HOMOMORPHIC_IMAGE,
        INTEGRAL_HOMOGENEOUS_RELATION, INTEGRAL_HOMOGENEOUS_SCALE,
        INTEGRAL_MONOMORPHISM_IN_IMAGE, .. } := BIntegral02
  -- @@SCOPE END

  let RING_LOCALIZATION_COMMON_DENOMINATOR ← prove
    r"!r s t:(A#A->bool)->bool.
        ring_multsys r s /\ FINITE t /\
        t SUBSET ring_carrier(ring_localization r s)
        ==> ?d. d IN s /\
                !x. x IN t
                    ==> ?a. a IN ring_carrier r /\
                            ring_mul (ring_localization r s)
                              (ring_fractionate r s d) x =
                            ring_fractionate r s a"
    (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [ring_multsys, SUBSET])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_HOMOMORPHISM_FRACTIONATE)) THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC [NOT_IN_EMPTY, INSERT_SUBSET, FORALL_IN_INSERT] THEN CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"y:A#A->bool"), (← q r"t:(A#A->bool)->bool")] THEN DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"d:A") STRIP_ASSUME_TAC) o CONJUNCT1) THEN UNDISCH_TAC (← q r"y IN ring_carrier(ring_localization r (s:A->bool))") THEN ASM_SIMP_TAC [RING_LOCALIZATION_CARRIER, IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN EXISTS_TAC (← q r"ring_mul r d b:A") THEN SUBGOAL_THEN (← q r"(d:A) IN ring_carrier r /\ (b:A) IN ring_carrier r") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [RING_MUL, (← MATCH_MP RING_HOMOMORPHISM_MUL th), (← GSYM RING_MUL_ASSOC), RING_FRACTIONATE_IN_CARRIER, RING_LOCALEQUIV_IN_CARRIER, LOCALEQUIV_MUL_RCANCEL])) THEN CONJ_TAC THENL [EXISTS_TAC (← q r"ring_mul r d a:A") THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [RING_MUL, (← MATCH_MP RING_HOMOMORPHISM_MUL th)])), ALL_TAC] THEN X_GEN_TAC (← q r"x:A#A->bool") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"x:A#A->bool"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:A") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"ring_mul r b c:A") THEN SUBGOAL_THEN (← q r"x IN ring_carrier(ring_localization r (s:A->bool))") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_localization r (s:A->bool)"), (← q r"ring_fractionate r s (d:A)"), (← q r"ring_fractionate r s (b:A)")] RING_MUL_SYM) THEN ASM_SIMP_TAC [RING_FRACTIONATE_IN_CARRIER] THEN DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [RING_MUL, (← MATCH_MP RING_HOMOMORPHISM_MUL th), (← GSYM RING_MUL_ASSOC), RING_FRACTIONATE_IN_CARRIER])))

  let INTEGRALLY_CLOSED_LOCALIZATION ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"(c:num->B) i IN ring_carrier t"
    let q2 ← q r"i:num"
    let q3 ← q r"!i:num. i < n ==> ring_mul t ((f:A->B) d) (c i) = f(e i)"
    let q4 ← q r"n - i = SUC(n - SUC i)"
    let q5 ← q r"i:num"
    let q6 ← q r"n:num"
    let q7 ← q r"c:num->B"
    let q8 ← q r"ring_mul t ((f:A->B) d) y"
    let q9 ← q r"ring_mul t ((f:A->B) d) x"
    let q10 ← q r"(f:A->B) d"
    let q11 ← q r"t:B ring"
    let v12 ← ISPECL [q11, q10, q9, q8, q7, q6] INTEGRAL_HOMOGENEOUS_SCALE
    let q13 ← q r"n:num"
    let q14 ← q r"c:num->B"
    let q15 ← q r"y:B"
    let q16 ← q r"x:B"
    let q17 ← q r"(f:A->B) d"
    let q18 ← q r"t:B ring"
    let v19 ← ISPECL [q18, q17, q16, q15, q14, q13] INTEGRAL_HOMOGENEOUS_SCALE
    let q20 ← q r"ring_mul t ((f:A->B) d) y = f b"
    let q21 ← q r"ring_mul t ((f:A->B) d) x = f a"
    let q22 ← q r"n:num"
    let q23 ← q r"\i. ring_mul r (ring_pow r d (n - SUC i)) ((e:num->A) i)"
    let q24 ← q r"b:A"
    let q25 ← q r"ring_mul r d a:A"
    let q26 ← q r"f:A->B"
    let q27 ← q r"t:B ring"
    let q28 ← q r"r:A ring"
    let v29 ← ISPECL [q28, q27, q26, q25, q24, q23, q22] INTEGRAL_HOMOGENEOUS_HOMOMORPHIC_IMAGE
    let v30 ← BETA_RULE v29
    let q31 ← q r"(f:A->B) d IN ring_carrier t"
    let q32 ← q r"p ==> q /\ r <=> (p ==> q) /\ (p ==> r)"
    let r33 ← TAUT q32
    let p34 ← prove r"!r t (f:A->B) d a b e x y c n.
        ring_homomorphism(r,t) f /\
        d IN ring_carrier r /\ a IN ring_carrier r /\ b IN ring_carrier r /\
        x IN ring_carrier t /\ y IN ring_carrier t /\
        ring_mul t (f d) x = f a /\ ring_mul t (f d) y = f b /\
        (!i. i < n ==> e i IN ring_carrier r /\ c i IN ring_carrier t /\
                       ring_mul t (f d) (c i) = f(e i))
        ==> f(ring_add r (ring_pow r (ring_mul r d a) n)
                (ring_sum r {i | i < n}
                   (\i. ring_mul r (ring_mul r (ring_pow r d (n - SUC i)) (e i))
                          (ring_mul r (ring_pow r (ring_mul r d a) i)
                                      (ring_pow r b (n - i)))))) =
            ring_mul t (ring_pow t (f d) n)
              (ring_mul t (ring_pow t (f d) n)
                (ring_add t (ring_pow t x n)
                  (ring_sum t {i | i < n}
                    (\i. ring_mul t (c i)
                           (ring_mul t (ring_pow t x i)
                                       (ring_pow t y (n - i)))))))" (REPEAT GEN_TAC THEN REWRITE_TAC [FORALL_AND_THM, r33] THEN STRIP_TAC THEN SUBGOAL_THEN q31 ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN MP_TAC v30 THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_MUL, RING_POW], DISCH_THEN SUBST1_TAC] THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL th)])) THEN UNDISCH_THEN q21 (SUBST1_TAC o SYM) THEN UNDISCH_THEN q20 (SUBST1_TAC o SYM) THEN MP_TAC v19 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN MP_TAC v12 THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_MUL], DISCH_THEN (SUBST1_TAC o SYM)] THEN AP_TERM_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC q5 THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN SUBGOAL_THEN q4 SUBST1_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL th), (← MATCH_MP RING_HOMOMORPHISM_POW th), RING_POW])) THEN UNDISCH_THEN q3 (MP_TAC o (SPEC q2)) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN SUBGOAL_THEN q1 ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [RING_MUL_POW, ring_pow, RING_MUL, RING_POW] THEN RING_TAC)
    let lemma := p34
    let q35 ← q r"ring_mul r d a:A"
    let q36 ← q r"b:A"
    let q37 ← q r"ring_fractionate r (s:A->bool)"
    let q38 ← q r"ring_localization r (s:A->bool)"
    let q39 ← q r"r:A ring"
    let v40 ← ISPECL [q39, q38, q37, q36, q35] RING_DIVIDES_HOMOMORPHIC_IMAGE
    let q41 ← q r"n:num"
    let q42 ← q r"c:num->A#A->bool"
    let q43 ← q r"y:A#A->bool"
    let q44 ← q r"x:A#A->bool"
    let q45 ← q r"e:num->A"
    let q46 ← q r"b:A"
    let q47 ← q r"a:A"
    let q48 ← q r"d:A"
    let q49 ← q r"ring_fractionate r (s:A->bool)"
    let q50 ← q r"ring_localization r (s:A->bool)"
    let q51 ← q r"r:A ring"
    let v52 ← ISPECL [q51, q50, q49, q48, q47, q46, q45, q44, q43, q42, q41] lemma
    let q53 ← q r"ring_associates (ring_localization r s) y
                        (ring_fractionate r s (b:A))"
    let v54 ← ASSUME q53
    let v55 ← MATCH_MP RING_ASSOCIATES_EQ_0 v54
    let q56 ← q r"n:num"
    let q57 ← q r"\i. ring_mul r (ring_pow r d (n - SUC i)) ((e:num->A) i)"
    let q58 ← q r"b:A"
    let q59 ← q r"ring_mul r d a:A"
    let q60 ← q r"ring_mul (ring_localization r s)
                    (ring_fractionate r s (d:A)) x"
    let q61 ← q r"ring_mul (ring_localization r s) (ring_fractionate r s d) y =
                  ring_fractionate r s (b:A)"
    let q62 ← q r"ring_mul (ring_localization r s) (ring_fractionate r s d) x =
                  ring_fractionate r s (a:A)"
    let q63 ← q r"ring_associates (ring_localization r s) y (ring_fractionate r s b) /\
    ring_associates (ring_localization r s) x
      (ring_fractionate r s (ring_mul r d a:A))"
    let q64 ← q r"ring_unit (ring_localization r s) (ring_fractionate r s (d:A)) /\
    ring_fractionate r s d IN ring_carrier (ring_localization r s)"
    let q65 ← q r"(d:A) IN ring_carrier r"
    let q66 ← q r"e:num->A"
    let q67 ← q r"b:A"
    let q68 ← q r"a:A"
    let q69 ← q r"d:A"
    let q70 ← q r"(x:A#A->bool) INSERT y INSERT IMAGE (c:num->A#A->bool) {i | i < n}"
    let q71 ← q r"s:A->bool"
    let q72 ← q r"r:A ring"
    let v73 ← ISPECL [q72, q71, q70] RING_LOCALIZATION_COMMON_DENOMINATOR
    let q74 ← q r"n:num"
    let q75 ← q r"c:num->A#A->bool"
    let q76 ← q r"y:A#A->bool"
    let q77 ← q r"x:A#A->bool"
    let q78 ← q r"ring_monomorphism (r,ring_localization r s)
                      (ring_fractionate r (s:A->bool))"
    prove
      r"!r s:A->bool.
          integrally_closed r /\ ring_multsys r s /\ ~(ring_0 r IN s)
          ==> integrally_closed (ring_localization r s)"
      (REPEAT GEN_TAC THEN REWRITE_TAC [INTEGRALLY_CLOSED_ALT] THEN DISCH_THEN (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "div")) STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_LOCALIZATION] THEN SUBGOAL_THEN q78 ASSUME_TAC THENL [ASM_SIMP_TAC [RING_MONOMORPHISM_FRACTIONATE_GEN, SUBSET, IN_ELIM_THM, INTEGRAL_DOMAIN_REGULAR] THEN ASM_MESON_TAC [RING_MULTSYS], FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM))] THEN MAP_EVERY X_GEN_TAC [q77, q76, q75, q74] THEN STRIP_TAC THEN MP_TAC v73 THEN ASM_SIMP_TAC [FINITE_INSERT, FINITE_IMAGE, FINITE_NUMSEG_LT, INSERT_SUBSET, SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM, FORALL_IN_INSERT] THEN DISCH_THEN (X_CHOOSE_THEN q69 (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN q68 STRIP_ASSUME_TAC) (CONJUNCTS_THEN2 (X_CHOOSE_THEN q67 STRIP_ASSUME_TAC) MP_TAC)) THEN GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC q66 THEN DISCH_TAC THEN SUBGOAL_THEN q65 ASSUME_TAC THENL [ASM_MESON_TAC [RING_MULTSYS], ALL_TAC] THEN SUBGOAL_THEN q64 STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_UNIT_FRACTIONATE, RING_FRACTIONATE_IN_CARRIER], ALL_TAC] THEN SUBGOAL_THEN q63 STRIP_ASSUME_TAC THENL [FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL th)])) THEN UNDISCH_THEN q62 (SUBST1_TAC o SYM) THEN UNDISCH_THEN q61 (SUBST1_TAC o SYM) THEN CONJ_TAC THENL [MATCH_MP_TAC RING_ASSOCIATES_LMUL THEN ASM_REWRITE_TAC [], MATCH_MP_TAC RING_ASSOCIATES_TRANS THEN EXISTS_TAC q60 THEN CONJ_TAC THEN MATCH_MP_TAC RING_ASSOCIATES_LMUL THEN ASM_SIMP_TAC [RING_MUL]], ALL_TAC] THEN REMOVE_THEN "div" (MP_TAC o (SPECL [q59, q58, q57, q56])) THEN REWRITE_TAC [] THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_MUL, RING_POW] THEN CONJ_TAC THENL [DISCH_TAC THEN MP_TAC v55 THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_0 th)])), FIRST_X_ASSUM (MATCH_MP_TAC o (CONJUNCT2 o (GEN_REWRITE_RULE id [RING_MONOMORPHISM_ALT]))) THEN ASM_SIMP_TAC [RING_ADD, RING_POW, RING_SUM, RING_MUL] THEN MP_TAC v52 THEN ANTS_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [RING_MUL_RZERO, RING_POW]], DISCH_TAC THEN MP_TAC v40 THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC RING_ASSOCIATES_DIVIDES THEN ONCE_REWRITE_TAC [RING_ASSOCIATES_SYM] THEN ASM_REWRITE_TAC []])

  let INTEGRAL_ELEMENT_INTERMEDIATE ← prove
    r"!r:A ring s:B ring t:C ring f g x.
        ring_homomorphism(r,s) f /\ ring_homomorphism(s,t) g /\
        integral_element (r,t) (g o f) x
        ==> integral_element (s,t) g x"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_homomorphism(r,t) ((g:B->C) o (f:A->B))") ASSUME_TAC THENL [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC (← q r"s:B ring") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"t:C ring"), (← q r"(g:B->C) o (f:A->B)"), (← q r"x:C")] INTEGRAL_ELEMENT_RELATION) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"n:num"), (← q r"c:num->A")] THEN REWRITE_TAC [o_THM] THEN STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_ELEMENT_FROM_RELATION THEN MAP_EVERY EXISTS_TAC [(← q r"n:num"), (← q r"(f:A->B) o (c:num->A)")] THEN ASM_REWRITE_TAC [o_THM] THEN CONJ_TAC THENL [ASM_MESON_TAC [INTEGRAL_ELEMENT_IN_CARRIER], ALL_TAC] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN EXISTS_TAC (← q r"r:A ring") THEN ASM_SIMP_TAC [])

  let INTEGRAL_ELEMENT_MONIC_DIVISOR ← prove
    r"!r:A ring k:B ring h p q.
        ring_homomorphism(r,k) h /\ field k /\
        p IN ring_carrier(poly_ring k (:1)) /\ monic k p /\
        q IN ring_carrier(poly_ring r (:1)) /\ monic r q /\
        ring_divides (poly_ring k (:1)) p (h o q)
        ==> !i. integral_element (r,k) h (coeff i p)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC (← q r"i:num") THEN MP_TAC (← ISPECL [(← q r"k:B ring"), (← q r"p:(1->num)->B")] SPLITTING_EXTENSION_EXISTS_BIGENOUGH) THEN ANTS_TAC THENL [ASM_MESON_TAC [MONIC_IMP_NONZERO, RING_POLYNOMIAL, FIELD_IMP_NONTRIVIAL_RING], REWRITE_TAC [LEFT_IMP_EXISTS_THM]] THEN MAP_EVERY X_GEN_TAC [(← q r"l:(B#num)ring"), (← q r"e:B->B#num")] THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP SPLITTING_EXTENSION_SPLITS)) THEN FIRST_ASSUM (MP_TAC o (MATCH_MP SPLITTING_IMP_FIELD_EXTENSION)) THEN REWRITE_TAC [poly_splits_over, field_extension] THEN STRIP_TAC THEN DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN SUBGOAL_THEN (← q r"ring_homomorphism(r,l) ((e:B->B#num) o (h:A->B))") ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_COMPOSE], ALL_TAC] THEN ABBREV_TAC (← q r"S = {x | integral_element (r,l) ((e:B->B#num) o (h:A->B)) x}") THEN SUBGOAL_THEN (← q r"(S:B#num->bool) subring_of l") ASSUME_TAC THENL [EXPAND_TAC "S" THEN MATCH_MP_TAC INTEGRAL_CLOSURE_SUBRING THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"monic l ((e:B->B#num) o (p:(1->num)->B))") ASSUME_TAC THENL [REWRITE_TAC [monic, COEFF_COMPOSE] THEN SUBGOAL_THEN (← q r"poly_deg l ((e:B->B#num) o (p:(1->num)->B)) = poly_deg k p") SUBST1_TAC THENL [MATCH_MP_TAC POLY_DEG_MONOMORPHIC_IMAGE THEN ASM_MESON_TAC [RING_POLYNOMIAL], ALL_TAC] THEN UNDISCH_TAC (← q r"monic k (p:(1->num)->B)") THEN REWRITE_TAC [monic] THEN DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC [RING_HOMOMORPHISM_1], ALL_TAC] THEN SUBGOAL_THEN (← q r"?s. s IN ring_carrier(poly_ring l (:1)) /\
        ((e:B->B#num) o (h:A->B)) o (q:(1->num)->A) =
        poly_mul l ((e:B->B#num) o (p:(1->num)->B)) s") STRIP_ASSUME_TAC THENL [REWRITE_TAC [(← GSYM o_ASSOC)] THEN MP_TAC (← ISPECL [(← q r"poly_ring (k:B ring) (:1)"), (← q r"poly_ring (l:(B#num)ring) (:1)"), (← q r"\p:(1->num)->B. (e:B->B#num) o p"), (← q r"p:(1->num)->B"), (← q r"(h:A->B) o (q:(1->num)->A)")] RING_DIVIDES_HOMOMORPHIC_IMAGE) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_POLY_RINGS] THEN REWRITE_TAC [ring_divides, POLY_RING_CLAUSES] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!z. z IN ring_carrier l /\
        poly_eval l ((e:B->B#num) o (p:(1->num)->B)) z = ring_0 l
        ==> z IN S") ASSUME_TAC THENL [X_GEN_TAC (← q r"z:B#num") THEN STRIP_TAC THEN EXPAND_TAC "S" THEN REWRITE_TAC [IN_ELIM_THM, integral_element] THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"q:(1->num)->A") THEN ASM_SIMP_TAC [POLY_EXTEND_EVALUATE, (← GSYM poly_eval)] THEN SUBGOAL_THEN (← q r"(e:B->B#num) o (p:(1->num)->B) IN ring_carrier(poly_ring l (:1))") ASSUME_TAC THENL [MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN EXISTS_TAC (← q r"k:B ring") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN wPart lhand (lhand o rand) POLY_EVAL_MUL THEN ASM_REWRITE_TAC [RING_POLYNOMIAL] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_MUL_LZERO THEN REWRITE_TAC [POLY_EVAL], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"l:(B#num)ring"), (← q r"S:B#num->bool"), (← q r"(e:B->B#num) o (p:(1->num)->B)")] POLY_SPLITS_IN_SUBRING_MONIC) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (MATCH_MP POLY_SPLITS_IN_CARRIER)) THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"(\v:1. i:num)")) o (MATCH_MP POLY_MONOMIAL_IN_CARRIER))) THEN ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING, o_THM] THEN EXPAND_TAC "S" THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"l:(B#num)ring"), (← q r"h:A->B"), (← q r"e:B->B#num"), (← q r"coeff i (p:(1->num)->B)")] INTEGRAL_ELEMENT_MONOMORPHIC_PREIMAGE) THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [COEFF] THEN ASM_MESON_TAC [POLY_MONOMIAL_IN_CARRIER])

  let INTEGRAL_ELEMENT_MINIMAL_POLYNOMIAL ← prove
    r"!r:A ring k:B ring l:C ring h g x.
        ring_homomorphism(r,k) h /\ field_extension(k,l) g /\
        integral_element (r,l) (g o h) x
        ==> algebraic_over (k,l) g x /\
            !i. integral_element (r,k) h
                  (coeff i (minimal_polynomial (k,l) g x))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_extension])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN SUBGOAL_THEN (← q r"ring_homomorphism(r,l) ((g:B->C) o (h:A->B))") ASSUME_TAC THENL [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC (← q r"k:B ring") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN FIRST_ASSUM (MP_TAC o (GEN_REWRITE_RULE id [integral_element])) THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"q:(1->num)->A") STRIP_ASSUME_TAC)) THEN SUBGOAL_THEN (← q r"(h:A->B) o (q:(1->num)->A) IN ring_carrier(poly_ring k (:1))") ASSUME_TAC THENL [MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN EXISTS_TAC (← q r"r:A ring") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"monic k ((h:A->B) o (q:(1->num)->A))") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"q:(1->num)->A")] MONIC_HOMOMORPHIC_IMAGE) THEN ASM_SIMP_TAC [FIELD_IMP_NONTRIVIAL_RING], ALL_TAC] THEN SUBGOAL_THEN (← q r"poly_extend (k,l) (g:B->C) (\v:1. x) ((h:A->B) o (q:(1->num)->A)) =
    ring_0 l") ASSUME_TAC THENL [FIRST_X_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [(← SYM th)])) THEN ASM_SIMP_TAC [POLY_EXTEND_EVALUATE, o_ASSOC], ALL_TAC] THEN SUBGOAL_THEN (← q r"algebraic_over (k,l) (g:B->C) x") ASSUME_TAC THENL [ASM_REWRITE_TAC [algebraic_over] THEN EXISTS_TAC (← q r"(h:A->B) o (q:(1->num)->A)") THEN ASM_REWRITE_TAC [POLY_RING_CLAUSES] THEN MATCH_MP_TAC MONIC_IMP_NONZERO THEN ASM_SIMP_TAC [RING_POLYNOMIAL, FIELD_IMP_NONTRIVIAL_RING], ASM_REWRITE_TAC []] THEN MATCH_MP_TAC INTEGRAL_ELEMENT_MONIC_DIVISOR THEN EXISTS_TAC (← q r"q:(1->num)->A") THEN ASM_SIMP_TAC [MINIMAL_POLYNOMIAL_DIVIDES, MINIMAL_POLYNOMIAL_IN_CARRIER, MINIMAL_POLYNOMIAL_MONIC])

  let ALGEBRA_TRACE_NORM_INTEGRAL ← prove
    r"!r:A ring k:B ring l:C ring h g x.
        ring_homomorphism(r,k) h /\ finite_extension(k,l) g /\
        integral_element (r,l) (g o h) x
        ==> integral_element (r,k) h (algebra_trace (k,l) g x) /\
            integral_element (r,k) h (algebra_norm (k,l) g x)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITE_IMP_FIELD_EXTENSION)) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"l:C ring"), (← q r"h:A->B"), (← q r"g:B->C"), (← q r"x:C")] INTEGRAL_ELEMENT_MINIMAL_POLYNOMIAL) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP INTEGRAL_ELEMENT_IN_CARRIER)) THEN ASM_SIMP_TAC [ALGEBRA_TRACE_MINIMAL_POLYNOMIAL, ALGEBRA_NORM_MINIMAL_POLYNOMIAL] THEN ABBREV_TAC (← q r"S = {y | integral_element (r,k) (h:A->B) y}") THEN SUBGOAL_THEN (← q r"(S:B->bool) subring_of k") ASSUME_TAC THENL [EXPAND_TAC "S" THEN MATCH_MP_TAC INTEGRAL_CLOSURE_SUBRING THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. coeff i (minimal_polynomial (k,l) (g:B->C) x) IN (S:B->bool)") MP_TAC THENL [EXPAND_TAC "S" THEN ASM_REWRITE_TAC [IN_ELIM_THM], ALL_TAC] THEN SUBGOAL_THEN (← q r"!y. integral_element (r,k) (h:A->B) y <=> y IN S") (fun th => REWRITE_TAC [th]) THENL [EXPAND_TAC "S" THEN REWRITE_TAC [IN_ELIM_THM], DISCH_TAC] THEN REPEAT (FIRST [CONJ_TAC, FIRST_ASSUM MATCH_ACCEPT_TAC, MATCH_MP_TAC IN_SUBRING_POW, MATCH_MP_TAC IN_SUBRING_MUL, MATCH_MP_TAC IN_SUBRING_NEG, MATCH_MP_TAC IN_SUBRING_NUM, MATCH_MP_TAC IN_SUBRING_1]))

  let INTEGRALLY_CLOSED_FIELD_OF_FRACTIONS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"(p <=> q) ==> p ==> q")
    prove
      r"!r:A ring k:B ring h.
          field_of_fractions (r,k) h
          ==> (integrally_closed r <=>
               !x. integral_element (r,k) h x
                   ==> x IN IMAGE h (ring_carrier r))"
      (REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_INTEGRAL_DOMAIN)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN SUBGOAL_THEN (← q r"!a:A. a IN ring_carrier r ==> (h:A->B) a IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN ASSUME_TAC (← MATCH_MP (← REWRITE_RULE [IMP_CONJ] RING_MONOMORPHISM_EQ_0) (← ASSUME (← q r"ring_monomorphism(r,k) (h:A->B)"))) THEN SUBGOAL_THEN (← q r"!b:A. b IN ring_carrier r /\ ~(b = ring_0 r)
           ==> ring_regular k ((h:A->B) b)") ASSUME_TAC THENL [ASM_SIMP_TAC [INTEGRAL_DOMAIN_REGULAR, FIELD_IMP_INTEGRAL_DOMAIN], ALL_TAC] THEN ASM_REWRITE_TAC [INTEGRALLY_CLOSED_ALT] THEN EQ_TAC THENL [DISCH_TAC THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP INTEGRAL_ELEMENT_IN_CARRIER)) THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"x:B")) o (checkM (fun th => (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); pure (is_forall z2)) then (do let z8 ← (pure "x"); let z7 ← (do pure (Prod.fst (← (do let z4 ← (do pure (Prod.fst (← (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); liftExcept (dest_forall z5))))); liftExcept (dest_var z4))))); pure (z7 == z8)) else pure false))))) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_mul k x ((h:A->B) b) = h a") ASSUME_TAC THENL [TRANS_TAC EQ_TRANS (← q r"ring_mul k ((h:A->B) b) x") THEN CONJ_TAC THENL [ALL_TAC, ASM_REWRITE_TAC []] THEN MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"x:B")] INTEGRAL_ELEMENT_EXPLICIT) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"n:num"), (← q r"c:num->A")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"a:A"), (← q r"b:A"), (← q r"x:B")] INTEGRAL_MONOMORPHISM_IN_IMAGE) THEN ASM_SIMP_TAC [] THEN DISCH_THEN SUBST1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"c:num->A"), (← q r"n:num")] THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"a:A"), (← q r"b:A"), (← q r"x:B"), (← q r"c:num->A"), (← q r"n:num")] INTEGRAL_HOMOGENEOUS_RELATION) THEN ASM_SIMP_TAC [] THEN MATCH_MP_TAC r1 THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_ADD, RING_POW, RING_SUM], DISCH_TAC THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A"), (← q r"c:num->A"), (← q r"n:num")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"~((h:A->B) b = ring_0 k)") ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"?x:B. x IN ring_carrier k /\ ring_mul k x (h b) = h(a:A)") STRIP_ASSUME_TAC THENL [EXISTS_TAC (← q r"ring_mul k ((h:A->B) a) (ring_inv k (h b))") THEN ASM_SIMP_TAC [RING_MUL, RING_INV] THEN ASM_SIMP_TAC [(← GSYM RING_MUL_ASSOC), RING_INV, FIELD_MUL_LINV, RING_MUL_RID], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"a:A"), (← q r"b:A"), (← q r"x:B")] INTEGRAL_MONOMORPHISM_IN_IMAGE) THEN ASM_SIMP_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC INTEGRAL_ELEMENT_FROM_RELATION THEN MAP_EVERY EXISTS_TAC [(← q r"n:num"), (← q r"c:num->A")] THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"a:A"), (← q r"b:A"), (← q r"x:B"), (← q r"c:num->A"), (← q r"n:num")] INTEGRAL_HOMOGENEOUS_RELATION) THEN ASM_SIMP_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_HOMOMORPHISM_0 THEN ASM_REWRITE_TAC []])

  let INTEGRALLY_CLOSED_MINIMAL_POLYNOMIAL ← prove
    r"!r:A ring k:B ring l:C ring h g x.
        integrally_closed r /\ field_of_fractions (r,k) h /\
        field_extension(k,l) g /\ algebraic_over (k,l) g x
        ==> (integral_element (r,l) (g o h) x <=>
             !i. coeff i (minimal_polynomial (k,l) g x) IN
                 IMAGE h (ring_carrier r))"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN EQ_TAC THENL [DISCH_TAC THEN X_GEN_TAC (← q r"i:num") THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B")] INTEGRALLY_CLOSED_FIELD_OF_FRACTIONS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"l:C ring"), (← q r"h:A->B"), (← q r"g:B->C"), (← q r"x:C")] INTEGRAL_ELEMENT_MINIMAL_POLYNOMIAL) THEN ASM_SIMP_TAC [], ALL_TAC] THEN REWRITE_TAC [IN_IMAGE, SKOLEM_THM] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"a:num->A")) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_extension])) THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) o (checkM (fun th => (do let z7 ← (q r"ring_monomorphism(k,l) (g:B->C)"); let z6 ← (do let z5 ← (pure th); pure (concl z5)); pure (z6 == z7)))))) THEN MP_TAC (← ISPECL [(← q r"g:B->C"), (← q r"k:B ring"), (← q r"l:C ring"), (← q r"x:C")] MINIMAL_POLYNOMIAL) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"p = minimal_polynomial (k,l) (g:B->C) x") THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP ALGEBRAIC_OVER_IN_CARRIER)) THEN MATCH_MP_TAC INTEGRAL_ELEMENT_FROM_RELATION THEN MAP_EVERY EXISTS_TAC [(← q r"poly_deg k (p:(1->num)->B)"), (← q r"a:num->A")] THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC (← q r"k:B ring") THEN ASM_REWRITE_TAC [], ASM_REWRITE_TAC [], ASM_MESON_TAC [], ALL_TAC] THEN FIRST_X_ASSUM ((fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [(← SYM th)])) o (checkM (fun th => (do let z4 ← (q r"ring_0 l:C"); let z3 ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); liftExcept (rand z1)); pure (z3 == z4))))) THEN ASM_SIMP_TAC [POLY_EXTEND_MONIC_UNIVARIATE, o_THM])

  let INTEGRALLY_CLOSED_ALGEBRA_TRACE_NORM ← prove
    r"!r:A ring k:B ring l:C ring h g x.
        integrally_closed r /\ field_of_fractions (r,k) h /\
        finite_extension(k,l) g /\ integral_element (r,l) (g o h) x
        ==> algebra_trace (k,l) g x IN IMAGE h (ring_carrier r) /\
            algebra_norm (k,l) g x IN IMAGE h (ring_carrier r)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_homomorphism(r,k) (h:A->B)") ASSUME_TAC THENL [ASM_MESON_TAC [field_of_fractions, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B")] INTEGRALLY_CLOSED_FIELD_OF_FRACTIONS) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"l:C ring"), (← q r"h:A->B"), (← q r"g:B->C"), (← q r"x:C")] ALGEBRA_TRACE_NORM_INTEGRAL) THEN ASM_SIMP_TAC [])

  -- @@RETURN BEGIN
  return { RING_LOCALIZATION_COMMON_DENOMINATOR, INTEGRALLY_CLOSED_LOCALIZATION,
           INTEGRAL_ELEMENT_INTERMEDIATE, INTEGRAL_ELEMENT_MONIC_DIVISOR,
           INTEGRAL_ELEMENT_MINIMAL_POLYNOMIAL, ALGEBRA_TRACE_NORM_INTEGRAL,
           INTEGRALLY_CLOSED_FIELD_OF_FRACTIONS, INTEGRALLY_CLOSED_MINIMAL_POLYNOMIAL,
           INTEGRALLY_CLOSED_ALGEBRA_TRACE_NORM }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- integral.ml phrases from line 2077 to 2288                             -/
/- ---------------------------------------------------------------------- -/

structure Integral04 where
  -- @@FIELDS
  INTEGRALLY_CLOSED_UNIT_NORM : thm
  INTEGRAL_CLOSURE_UNIT_NORM : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupIntegral04 [HolBase] (D : IntegralDeps) (BIntegral01 : Integral01) (BIntegral03 : Integral03) :
    ExceptT String IO Integral04 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, RING_RULE, SET_TAC, .. } := D
  let { ALGEBRA_NORM_1, ALGEBRA_NORM_MINIMAL_POLYNOMIAL, ALGEBRA_NORM_MUL,
        CARRIER_SUBRING_GENERATED_SUBRING, COEFF_IN_CARRIER_ALT, EQ_TRANS,
        EXTENSION_DEGREE_EQ_0, FIELD_EXTENSION_IMP_HOMOMORPHISM,
        FIELD_EXTENSION_SUBFIELD_GENERATED, FINITE_EXTENSION_SUBFIELD_GENERATED,
        FINITE_IMP_FIELD_EXTENSION, IN_ELIM_THM, IN_IMAGE, IN_SUBRING_ADD,
        IN_SUBRING_MUL, IN_SUBRING_NEG, IN_SUBRING_POW, IN_SUBRING_SUM,
        IRREDUCIBLE_IMP_POLY_DEG_NZ, MINIMAL_POLYNOMIAL, POLY_EXTEND_MONIC_UNIVARIATE,
        RING_1, RING_ADD, .. } := D.core1
  let { RING_HOMOMORPHISM_1, RING_HOMOMORPHISM_COMPOSE, RING_HOMOMORPHISM_IN_CARRIER,
        RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_NEG, RING_HOMOMORPHISM_POW,
        RING_MONIC_RELATION_FACTOR, RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL,
        RING_MUL_SYM, RING_NEG, RING_POLYNOMIAL, RING_POW, RING_SUM, RING_UNIT_1,
        RING_UNIT_IN_CARRIER, RING_UNIT_MUL_EQ, RING_UNIT_NEG, RING_UNIT_POW,
        RING_UNIT_POW_EQ, SKOLEM_THM, SUBRING_GENERATED, field_extension,
        field_of_fractions, o_THM, ring_monomorphism, ring_unit, .. } := D.core2
  let { INTEGRAL_CLOSURE_SUBRING, INTEGRAL_ELEMENT_IMAGE, INTEGRAL_ELEMENT_IN_CARRIER, .. } := BIntegral01
  let { INTEGRALLY_CLOSED_ALGEBRA_TRACE_NORM, INTEGRALLY_CLOSED_MINIMAL_POLYNOMIAL,
        INTEGRAL_ELEMENT_MINIMAL_POLYNOMIAL, .. } := BIntegral03
  -- @@SCOPE END

  let INTEGRALLY_CLOSED_UNIT_NORM ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul (l:C ring) b c = ring_1 l
    ==> ring_add l c (ring_mul l x s) = ring_0 l
        ==> ring_mul l x (ring_mul l (ring_neg l b) s) = ring_1 l")
    prove
      r"!r:A ring k:B ring l:C ring h g x.
          integrally_closed r /\ field_of_fractions (r,k) h /\
          finite_extension(k,l) g /\ integral_element (r,l) (g o h) x
          ==> ((?y. integral_element (r,l) (g o h) y /\
                    ring_mul l x y = ring_1 l) <=>
               ?u. ring_unit r u /\ algebra_norm (k,l) g x = h u)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITE_IMP_FIELD_EXTENSION)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o ((GEN_REWRITE_RULE id [field_extension]) o (checkM (fun th => (do let z34 ← (q r"field_extension(k,l) (g:B->C)"); let z33 ← (do let z32 ← (pure th); pure (concl z32)); pure (z33 == z34)))))) THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) o (checkM (fun th => (do let z31 ← (q r"ring_monomorphism(k,l) (g:B->C)"); let z30 ← (do let z29 ← (pure th); pure (concl z29)); pure (z30 == z31)))))) THEN SUBGOAL_THEN (← q r"ring_homomorphism(r,l) ((g:B->C) o (h:A->B))") ASSUME_TAC THENL [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC (← q r"k:B ring") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP INTEGRAL_ELEMENT_IN_CARRIER)) THEN EQ_TAC THENL [DISCH_THEN (X_CHOOSE_THEN (← q r"y:C") STRIP_ASSUME_TAC) THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP INTEGRAL_ELEMENT_IN_CARRIER) o (checkM (fun th => (do let z28 ← (q r"integral_element (r,l) ((g:B->C) o (h:A->B)) y"); let z27 ← (do let z26 ← (pure th); pure (concl z26)); pure (z27 == z28)))))) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"l:C ring"), (← q r"h:A->B"), (← q r"g:B->C"), (← q r"x:C")] INTEGRALLY_CLOSED_ALGEBRA_TRACE_NORM) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"l:C ring"), (← q r"h:A->B"), (← q r"g:B->C"), (← q r"y:C")] INTEGRALLY_CLOSED_ALGEBRA_TRACE_NORM) THEN ASM_REWRITE_TAC [IN_IMAGE] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"b:A") STRIP_ASSUME_TAC) o CONJUNCT2) THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"a:A") STRIP_ASSUME_TAC) o CONJUNCT2) THEN EXISTS_TAC (← q r"a:A") THEN ASM_REWRITE_TAC [ring_unit] THEN EXISTS_TAC (← q r"b:A") THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (MATCH_MP_TAC o (CONJUNCT2 o ((GEN_REWRITE_RULE id [ring_monomorphism]) o (checkM (fun th => (do let z25 ← (q r"ring_monomorphism(r,k) (h:A->B)"); let z24 ← (do let z23 ← (pure th); pure (concl z23)); pure (z24 == z25))))))) THEN ASM_SIMP_TAC [RING_MUL, RING_1] THEN TRANS_TAC EQ_TRANS (← q r"algebra_norm (k,l) (g:B->C) (ring_mul l x y)") THEN CONJ_TAC THENL [ASM_SIMP_TAC [ALGEBRA_NORM_MUL] THEN FIRST_ASSUM (MATCH_MP_TAC o ((MATCH_MP RING_HOMOMORPHISM_MUL) o (checkM (fun th => (do let z22 ← (q r"ring_homomorphism(r,k) (h:A->B)"); let z21 ← (do let z20 ← (pure th); pure (concl z20)); pure (z21 == z22)))))) THEN ASM_REWRITE_TAC [], ASM_SIMP_TAC [ALGEBRA_NORM_1] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_HOMOMORPHISM_1 THEN ASM_REWRITE_TAC []], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"u:A") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"l:C ring"), (← q r"h:A->B"), (← q r"g:B->C"), (← q r"x:C")] INTEGRAL_ELEMENT_MINIMAL_POLYNOMIAL) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"l:C ring"), (← q r"h:A->B"), (← q r"g:B->C"), (← q r"x:C")] INTEGRALLY_CLOSED_MINIMAL_POLYNOMIAL) THEN ASM_REWRITE_TAC [IN_IMAGE, SKOLEM_THM] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:num->A") (ASSUME_TAC o GSYM)) THEN MP_TAC (← ISPECL [(← q r"g:B->C"), (← q r"k:B ring"), (← q r"l:C ring"), (← q r"x:C")] MINIMAL_POLYNOMIAL) THEN MP_TAC (← ISPECL [(← q r"g:B->C"), (← q r"k:B ring"), (← q r"l:C ring"), (← q r"x:C")] ALGEBRA_NORM_MINIMAL_POLYNOMIAL) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"p = minimal_polynomial (k,l) (g:B->C) x") THEN ABBREV_TAC (← q r"m = extension_degree
           (subfield_generated l (x INSERT IMAGE (g:B->C) (ring_carrier k)),l)
           I") THEN ABBREV_TAC (← q r"d = poly_deg k (p:(1->num)->B)") THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"~(d = 0)") ASSUME_TAC THENL [EXPAND_TAC "d" THEN MATCH_MP_TAC IRREDUCIBLE_IMP_POLY_DEG_NZ THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(m = 0)") ASSUME_TAC THENL [EXPAND_TAC "m" THEN MP_TAC (← ISPECL [(← q r"g:B->C"), (← q r"k:B ring"), (← q r"l:C ring"), (← q r"x INSERT IMAGE (g:B->C) (ring_carrier k)")] FINITE_EXTENSION_SUBFIELD_GENERATED) THEN ANTS_TAC THENL [ASM SET_TAC [], STRIP_TAC] THEN ASM_SIMP_TAC [EXTENSION_DEGREE_EQ_0, FIELD_EXTENSION_SUBFIELD_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. (a:num->A) i IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_pow r (ring_neg r (ring_1 r)) d IN ring_carrier r /\
      ring_unit r (ring_pow r (ring_neg r (ring_1 r)) d) /\
      (h:A->B)(ring_pow r (ring_neg r (ring_1 r)) d) =
      ring_pow k (ring_neg k (ring_1 k)) d") STRIP_ASSUME_TAC THENL [SIMP_TAC [RING_POW, RING_NEG, RING_1, RING_UNIT_POW, RING_UNIT_NEG, RING_UNIT_1] THEN FIRST_ASSUM ((fun th => tactic_of do pure (SIMP_TAC (RING_NEG :: (RING_1 :: (← ([RING_HOMOMORPHISM_POW, RING_HOMOMORPHISM_NEG, RING_HOMOMORPHISM_1]).mapM (← do let c := th; pure (fun th => MATCH_MP th c))))))) o (checkM (fun th => (do let z19 ← (q r"ring_homomorphism(r,k) (h:A->B)"); let z18 ← (do let z17 ← (pure th); pure (concl z17)); pure (z18 == z19))))), ALL_TAC] THEN ABBREV_TAC (← q r"e = ring_pow (r:A ring) (ring_neg r (ring_1 r)) d") THEN SUBGOAL_THEN (← q r"ring_unit r ((a:num->A) 0)") MP_TAC THENL [SUBGOAL_THEN (← q r"u = ring_pow r (ring_mul r e ((a:num->A) 0)) m") SUBST_ALL_TAC THENL [FIRST_ASSUM (MATCH_MP_TAC o (CONJUNCT2 o ((GEN_REWRITE_RULE id [ring_monomorphism]) o (checkM (fun th => (do let z16 ← (q r"ring_monomorphism(r,k) (h:A->B)"); let z15 ← (do let z14 ← (pure th); pure (concl z14)); pure (z15 == z16))))))) THEN ASM_SIMP_TAC [RING_POW, RING_MUL, RING_UNIT_IN_CARRIER] THEN FIRST_ASSUM ((fun th => tactic_of do pure (ASM_SIMP_TAC (RING_MUL :: (← ([RING_HOMOMORPHISM_POW, RING_HOMOMORPHISM_MUL]).mapM (← do let c := th; pure (fun th => MATCH_MP th c)))))) o (checkM (fun th => (do let z13 ← (q r"ring_homomorphism(r,k) (h:A->B)"); let z12 ← (do let z11 ← (pure th); pure (concl z11)); pure (z12 == z13))))), ALL_TAC] THEN UNDISCH_TAC (← q r"ring_unit r (ring_pow r (ring_mul r e ((a:num->A) 0)) m)") THEN ASM_SIMP_TAC [RING_UNIT_POW_EQ, RING_UNIT_MUL_EQ, RING_MUL], REWRITE_TAC [ring_unit] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"a0:A") STRIP_ASSUME_TAC) o CONJUNCT2)] THEN SUBGOAL_THEN (← q r"ring_add l (ring_pow l x d)
        (ring_sum l {i | i < d}
          (\i. ring_mul l ((g:B->C) (coeff i p)) (ring_pow l x i))) =
      ring_0 l") MP_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z10 ← (q r"poly_extend (k,l) (g:B->C) (\v:1. x) p"); let z9 ← (do let z7 ← (do let z8 ← (pure th); pure (concl z8)); liftExcept (lhand z7)); pure (z9 == z10)))))) THEN EXPAND_TAC "d" THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC POLY_EXTEND_MONIC_UNIVARIATE THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"l:C ring"), (← q r"x:C"), (← q r"\i. (g:B->C) (coeff i (p:(1->num)->B))"), (← q r"d:num")] RING_MONIC_RELATION_FACTOR) THEN REWRITE_TAC [] THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN EXISTS_TAC (← q r"k:B ring") THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC COEFF_IN_CARRIER_ALT THEN ASM_REWRITE_TAC [RING_POLYNOMIAL], DISCH_THEN SUBST1_TAC] THEN ABBREV_TAC (← q r"s = ring_add l (ring_pow l x (d - 1))
            (ring_sum l {i | i < d - 1}
              (\i. ring_mul l ((g:B->C) (coeff (i + 1) p))
                              (ring_pow l x i)))") THEN DISCH_TAC THEN EXISTS_TAC (← q r"ring_mul l (ring_neg l ((g:B->C) ((h:A->B) a0))) s") THEN SUBGOAL_THEN (← q r"!c. c IN ring_carrier r ==> (g:B->C) ((h:A->B) c) IN ring_carrier l") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN EXISTS_TAC (← q r"k:B ring") THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN EXISTS_TAC (← q r"r:A ring") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN CONJ_TAC THENL [ABBREV_TAC (← q r"t = {y | integral_element (r,l) ((g:B->C) o (h:A->B)) y}") THEN SUBGOAL_THEN (← q r"(t:C->bool) subring_of l") ASSUME_TAC THENL [EXPAND_TAC "t" THEN MATCH_MP_TAC INTEGRAL_CLOSURE_SUBRING THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!c. c IN ring_carrier r ==> (g:B->C) ((h:A->B) c) IN t") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN EXPAND_TAC "t" THEN REWRITE_TAC [IN_ELIM_THM] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"l:C ring"), (← q r"(g:B->C) o (h:A->B)"), (← q r"c:A")] INTEGRAL_ELEMENT_IMAGE) THEN ASM_REWRITE_TAC [o_THM], ALL_TAC] THEN SUBGOAL_THEN (← q r"(x:C) IN t") ASSUME_TAC THENL [EXPAND_TAC "t" THEN ASM_REWRITE_TAC [IN_ELIM_THM], ALL_TAC] THEN SUBGOAL_THEN (← q r"(s:C) IN t") ASSUME_TAC THENL [EXPAND_TAC "s" THEN MATCH_MP_TAC IN_SUBRING_ADD THEN ASM_SIMP_TAC [IN_SUBRING_POW] THEN MATCH_MP_TAC IN_SUBRING_SUM THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_SIMP_TAC [IN_SUBRING_POW] THEN FIRST_ASSUM ((fun th => tactic_of do pure (REWRITE_TAC [(← GSYM (← CONJUNCT1 (← SPEC (← q r"i + 1:num") th)))])) o (checkM (fun th => (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); pure (is_forall z2)) then (do let z4 ← (do pure (Prod.snd (← (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); liftExcept (dest_forall z5))))); pure (is_conj z4)) else pure false)))) THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul l (ring_neg l ((g:B->C) ((h:A->B) a0))) s IN t") MP_TAC THENL [MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IN_SUBRING_NEG THEN ASM_SIMP_TAC [], EXPAND_TAC "t" THEN REWRITE_TAC [IN_ELIM_THM]], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul l ((g:B->C) ((h:A->B) a0)) (g (h ((a:num->A) 0))) = ring_1 l") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"l:C ring"), (← q r"(g:B->C) o (h:A->B)")] RING_HOMOMORPHISM_MUL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (SPECL [(← q r"a0:A"), (← q r"(a:num->A) 0")])) THEN ASM_REWRITE_TAC [o_THM] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN SUBGOAL_THEN (← q r"ring_mul r a0 ((a:num->A) 0) = ring_1 r") SUBST1_TAC THENL [ASM_MESON_TAC [RING_MUL_SYM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"l:C ring"), (← q r"(g:B->C) o (h:A->B)")] RING_HOMOMORPHISM_1) THEN ASM_REWRITE_TAC [o_THM], ALL_TAC] THEN SUBGOAL_THEN (← q r"(s:C) IN ring_carrier l") ASSUME_TAC THENL [EXPAND_TAC "s" THEN SIMP_TAC [RING_ADD, RING_POW, RING_SUM, (← ASSUME (← q r"(x:C) IN ring_carrier l"))], ALL_TAC] THEN SUBGOAL_THEN (← q r"(g:B->C) (coeff 0 p) = g ((h:A->B) ((a:num->A) 0))") SUBST_ALL_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN UNDISCH_TAC (← q r"ring_add l ((g:B->C) ((h:A->B) ((a:num->A) 0))) (ring_mul l x s) =
      ring_0 l") THEN UNDISCH_TAC (← q r"ring_mul l ((g:B->C) ((h:A->B) a0)) (g (h ((a:num->A) 0))) = ring_1 l") THEN MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [])

  let INTEGRAL_CLOSURE_UNIT_NORM ← prove
    r"!r:A ring k:B ring l:C ring h g x.
        integrally_closed r /\ field_of_fractions (r,k) h /\
        finite_extension(k,l) g
        ==> (ring_unit
              (subring_generated l {y | integral_element (r,l) (g o h) y})
              x <=>
             integral_element (r,l) (g o h) x /\
             ?u. ring_unit r u /\ algebra_norm (k,l) g x = h u)"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"{y | integral_element (r,l) ((g:B->C) o (h:A->B)) y} subring_of l") ASSUME_TAC THENL [MATCH_MP_TAC INTEGRAL_CLOSURE_SUBRING THEN MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC (← q r"k:B ring") THEN ASM_MESON_TAC [field_of_fractions, RING_MONOMORPHISM_IMP_HOMOMORPHISM, FINITE_IMP_FIELD_EXTENSION, FIELD_EXTENSION_IMP_HOMOMORPHISM], ALL_TAC] THEN GEN_REWRITE_TAC LAND_CONV [ring_unit] THEN ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING, (← CONJUNCT2 SUBRING_GENERATED), IN_ELIM_THM] THEN ASM_CASES_TAC (← q r"integral_element (r,l) ((g:B->C) o (h:A->B)) x") THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC INTEGRALLY_CLOSED_UNIT_NORM THEN ASM_REWRITE_TAC [])

  -- @@RETURN BEGIN
  return { INTEGRALLY_CLOSED_UNIT_NORM, INTEGRAL_CLOSURE_UNIT_NORM }
  -- @@RETURN END

end HolANT.Integral
