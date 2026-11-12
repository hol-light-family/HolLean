/- ========================================================================= -/
/- ANT: Valuation rings, intrinsically and as valuation subrings of ...    -/
/- ========================================================================= -/
/- File: HolANT/ValuationRing.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/valuation_ring.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antvaluationringdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, ANT/integral.ml, ANT/ideal_arith.ml, Library/products.ml, ANT/algmisc.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.ValuationRing fills them).

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
import HolANT.Integral
import HolANT.IdealArith
import HolLibrary.Products
import HolANT.Algmisc
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.DedekindLocal
import HolANT.DedekindValuation

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.Integral
open HolANT.IdealArith
open HolANT.Algmisc
open HolANT.Dedekind
open HolANT.DedekindStruct
open HolANT.DedekindLocal
open HolANT.DedekindValuation

namespace HolANT.ValuationRing

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD_CLAUSES ADD_SUB ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD BEZOUT_RING_2
   CARRIER_SUBFIELD_GENERATED_SUBFIELD CARRIER_SUBRING_GENERATED_SUBRING
   CARRIER_SUBRING_OF COEFF_ABOVE_DEG COEFF_COMPOSE COEFF_IN_CARRIER_ALT
   DEDEKIND_VALUATION_INV DEDEKIND_VALUATION_RING_LOCALIZATION DVR
   DVR_IDEALS_TOTALLY_ORDERED DVR_IDEAL_MAXIMAL_POW DVR_IFF_LOCAL_DEDEKIND
   EMPTY_GSPEC EMPTY_SUBSET EQ_SYM_EQ EQ_TRANS ETA_AX EXISTS_PAIR_THM
   EXISTS_UNIQUE EXTENSION FIELD_IMP_INTEGRAL_DOMAIN FIELD_INV_EQ_0
   FIELD_MUL_LINV FIELD_MUL_RINV FIELD_NONTRIVIAL FIELD_POW_EQ_0
   FIELD_SUBFIELD_GENERATED FIELD_UNIT FINITE_IMAGE FINITE_NUMSEG
   FINITE_NUMSEG_LT FINITE_SUBSET_UNIONS_CHAIN FORALL_IN_GSPEC FORALL_IN_IMAGE
   FORALL_PAIR_THM FST IDEAL_GENERATED_ADJOIN_EXPLICIT
   IDEAL_GENERATED_ADJOIN_INV IDEAL_GENERATED_ADJOIN_ROOT_UNIT
   IDEAL_GENERATED_EQ_0 IDEAL_GENERATED_EXPLICIT IDEAL_GENERATED_INC
   IDEAL_GENERATED_MINIMAL IDEAL_GENERATED_MONO IDEAL_GENERATED_RING_IDEAL
   IDEAL_POW_PRINCIPAL IMAGE_I IMP_CONJ IMP_IMP INSERT_SUBSET
   INTEGRALLY_CLOSED_ALT INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING
   INTEGRAL_DOMAIN_MUL_EQ_0 INTEGRAL_DOMAIN_POW_EQ_0
   INTEGRAL_DOMAIN_QUOTIENT_RING INTEGRAL_DOMAIN_SUBRING_GENERATED
   INTEGRAL_ELEMENT_EXPLICIT INTEGRAL_ELEMENT_IMAGE
   INTEGRAL_ELEMENT_IN_ADJOIN_INV INTEGRAL_ELEMENT_OVER_SUBRING IN_CROSS
   IN_ELIM_THM IN_IDEAL_GENERATED_SELF IN_IDEAL_GENERATED_SING
   IN_IDEAL_GENERATED_SING_EQ IN_IMAGE IN_INSERT IN_INTER IN_INTERS IN_NUMSEG
   IN_RING_IDEAL_0 IN_RING_IDEAL_LMUL IN_RING_IDEAL_RMUL
   IN_RING_POLYNOMIAL_CARRIER_COMPOSE IN_SING IN_SUBFIELD_INV IN_SUBRING_POW
   IN_UNIONS IN_UNIV I_DEF I_THM LE_0 LOCAL_RING_MAXIMAL_IDEAL_NONUNITS LT
   MAXIMAL_IDEAL_EXISTS MAXIMAL_IMP_PRIME_IDEAL MAXIMAL_IMP_RING_IDEAL
   MAXIMAL_SUPERIDEAL_EXISTS MEMBER_NOT_EMPTY MONO_EXISTS MONO_OR NOT_EXISTS_THM
   PAIR_EQ PID_EQ_NOETHERIAN_BEZOUT_DOMAIN PID_IMP_INTEGRAL_DOMAIN
   PID_IMP_NOETHERIAN_RING POLY_CONST POLY_EXTEND_CONST POLY_EXTEND_CONST_VARPOW
   POLY_EXTEND_EVALUATE POLY_EXTEND_RING_SUM POLY_EXTEND_UNIVARIATE
   POLY_EXTEND_VAR : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (POLY_TOP_EQ_0 POLY_VAR PRIME_IDEAL_IMP_SUBSET PRIME_IMP_RING_IDEAL PROD_RING
   PROPER_IDEAL_ALT PROPER_IDEAL_IDEAL_GENERATED_SING PSUBSET
   QUOTIENT_RING_CARRIER RIGHT_FORALL_IMP_THM RING_0 RING_1 RING_ADD
   RING_ADD_ASSOC RING_ADD_LDISTRIB RING_ADD_LNEG RING_ADD_RNEG RING_ADD_RZERO
   RING_DIVIDES_0 RING_DIVIDES_HOMOMORPHIC_IMAGE RING_HOMOMORPHISM_0
   RING_HOMOMORPHISM_INCLUSION RING_HOMOMORPHISM_PAIRED
   RING_HOMOMORPHISM_POLY_EXTEND RING_HOMOMORPHISM_POW
   RING_HOMOMORPHISM_RING_COSET RING_HOMOMORPHISM_SUM RING_IDEAL_IDEAL_GENERATED
   RING_IDEAL_IMP_SUBSET RING_IDEAL_POLY_COMMON_ROOT RING_IDEAL_RING_KERNEL
   RING_INV RING_INV_INV RING_INV_MUL RING_INV_SUBFIELD_GENERATED
   RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_MUL RING_MUL_ASSOC RING_MUL_LZERO
   RING_MUL_POW RING_MUL_RID RING_MUL_RZERO RING_NEG RING_POLYNOMIAL
   RING_POLYNOMIAL_CONST RING_POLYNOMIAL_MUL RING_POLYNOMIAL_POW
   RING_POLYNOMIAL_VAR RING_POW RING_POW_1 RING_POW_ADD RING_POW_IN_PRIME_IDEAL
   RING_POW_ONE RING_POW_SUBRING_GENERATED RING_SUB_EQ_0 RING_SUM RING_SUM_ADD
   RING_SUM_CLAUSES RING_SUM_CLAUSES_LEFT RING_SUM_CLAUSES_NUMSEG
   RING_SUM_CLAUSES_RIGHT RING_SUM_EQ RING_SUM_EQ_GENERAL_INVERSES RING_SUM_LMUL
   RING_SUM_RESTRICT_SET RING_SUM_SUBRING_GENERATED RING_UNIT_1
   RING_UNIT_NOT_IN_PRIME_IDEAL RING_UNIT_SUBRING_OF_FIELD SELECT_UNIQUE
   SING_SUBSET SUBFIELD_GENERATED SUBFIELD_IMP_SUBRING_OF SUBFIELD_OF_IMP_SUBSET
   SUBRING_GENERATED SUBRING_GENERATED_BY_SUBRING_GENERATED
   SUBRING_GENERATED_INC_GEN SUBRING_OF_HOMOMORPHIC_IMAGE SUBRING_OF_UNIONS
   SUBRING_RING_IMAGE SUBRING_SUBRING_GENERATED SUBSET SUBSET_ANTISYM
   SUBSET_REFL SUBSET_TRANS SUB_0 SUB_ADD TRIVIAL_RING_10
   ZL_SUBSETS_UNIONS_NONEMPTY dedekind_domain field_of_fractions local_ring
   maximal_ideal num_WF o_DEF poly_eval prime_ideal principal_ideal ring_divides
   ring_homomorphism ring_ideal ring_image ring_kernel ring_pow ring_sub
   subring_of : thm)
  deriving Inhabited

/-- What valuation_ring.ml uses from Session besides theorems. -/
structure ValuationRingDeps where
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
  GEN_BETA_CONV : ioconv
  SELECT_CONV : ioconv
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
/- valuation_ring.ml phrases from line 73 to 482                          -/
/- ---------------------------------------------------------------------- -/

structure ValuationRing01 where
  -- @@FIELDS
  valuation_ring : thm
  valuation_subring : thm
  VALUATION_RING_IMP_INTEGRAL_DOMAIN : thm
  VALUATION_RING_IDEALS_TOTALLY_ORDERED : thm
  VALUATION_RING_IMP_LOCAL : thm
  VALUATION_RING_IMP_INTEGRALLY_CLOSED : thm
  VALUATION_RING_QUOTIENT_RING : thm
  VALUATION_SUBRING_SUPERSET : thm
  VALUATION_SUBRING_IMP_VALUATION_RING : thm
  VALUATION_SUBRING_IMP_LOCAL : thm
  VALUATION_SUBRING_MAXIMAL_IDEAL : thm
  VALUATION_SUBRING_INV_MAXIMAL_IDEAL : thm
  VALUATION_SUBRING_SUBFIELD : thm
  VALUATION_SUBRING_INTEGRAL_ELEMENT : thm
  VALUATION_SUBRING_INTEGRAL_CLOSURE : thm
  IDEAL_GENERATED_ADJOIN_OR_INV : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupValuationRing01 [HolBase] (D : ValuationRingDeps) :
    ExceptT String IO ValuationRing01 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, RING_RULE,
        RING_TAC, SET_RULE, SET_TAC, TAUT, new_definition, .. } := D
  let { ADD_CLAUSES, ADD_SUB, CARRIER_SUBFIELD_GENERATED_SUBFIELD,
        CARRIER_SUBRING_GENERATED_SUBRING, EMPTY_GSPEC, EQ_SYM_EQ, EQ_TRANS,
        EXISTS_UNIQUE, EXTENSION, FIELD_IMP_INTEGRAL_DOMAIN, FIELD_INV_EQ_0,
        FIELD_MUL_LINV, FIELD_MUL_RINV, FIELD_SUBFIELD_GENERATED, FIELD_UNIT,
        FINITE_NUMSEG, FINITE_NUMSEG_LT, FORALL_IN_GSPEC,
        IDEAL_GENERATED_ADJOIN_EXPLICIT, IMP_CONJ, INTEGRALLY_CLOSED_ALT,
        INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING, INTEGRAL_DOMAIN_MUL_EQ_0,
        INTEGRAL_DOMAIN_POW_EQ_0, INTEGRAL_DOMAIN_QUOTIENT_RING,
        INTEGRAL_DOMAIN_SUBRING_GENERATED, INTEGRAL_ELEMENT_EXPLICIT,
        INTEGRAL_ELEMENT_IMAGE, IN_ELIM_THM, IN_INTER, IN_NUMSEG, IN_RING_IDEAL_RMUL,
        IN_SUBFIELD_INV, I_DEF, I_THM, LE_0, LOCAL_RING_MAXIMAL_IDEAL_NONUNITS, LT,
        MAXIMAL_IDEAL_EXISTS, MAXIMAL_IMP_RING_IDEAL, MONO_EXISTS, MONO_OR, .. } := D.core1
  let { PRIME_IMP_RING_IDEAL, PSUBSET, QUOTIENT_RING_CARRIER, RIGHT_FORALL_IMP_THM,
        RING_0, RING_1, RING_ADD, RING_ADD_ASSOC, RING_ADD_LDISTRIB, RING_ADD_LNEG,
        RING_ADD_RZERO, RING_DIVIDES_0, RING_DIVIDES_HOMOMORPHIC_IMAGE,
        RING_HOMOMORPHISM_INCLUSION, RING_HOMOMORPHISM_RING_COSET,
        RING_IDEAL_IMP_SUBSET, RING_INV, RING_INV_INV, RING_INV_MUL,
        RING_INV_SUBFIELD_GENERATED, RING_MUL, RING_MUL_POW, RING_MUL_RID,
        RING_MUL_RZERO, RING_NEG, RING_POW, RING_POW_1, RING_POW_ADD, RING_POW_ONE,
        RING_SUM, RING_SUM_ADD, RING_SUM_CLAUSES, RING_SUM_CLAUSES_LEFT,
        RING_SUM_CLAUSES_NUMSEG, RING_SUM_CLAUSES_RIGHT, RING_SUM_EQ,
        RING_SUM_EQ_GENERAL_INVERSES, RING_SUM_LMUL, RING_SUM_RESTRICT_SET,
        RING_SUM_SUBRING_GENERATED, RING_UNIT_SUBRING_OF_FIELD, SUBFIELD_GENERATED,
        SUBFIELD_IMP_SUBRING_OF, SUBFIELD_OF_IMP_SUBSET, SUBRING_GENERATED, SUBSET,
        SUBSET_ANTISYM, SUB_0, TRIVIAL_RING_10, local_ring, maximal_ideal, num_WF,
        ring_divides, ring_ideal, ring_pow, ring_sub, subring_of, .. } := D.core2
  -- @@SCOPE END

  let valuation_ring ← new_definition
    r"valuation_ring (r:A ring) <=>
        integral_domain r /\
        !a b. a IN ring_carrier r /\ b IN ring_carrier r
              ==> ring_divides r a b \/ ring_divides r b a"

  let valuation_subring ← new_definition
    r"valuation_subring (k:A ring) (b:A->bool) <=>
        field k /\ b subring_of k /\
        !x. x IN ring_carrier k /\ ~(x = ring_0 k)
            ==> x IN b \/ ring_inv k x IN b"

  let VALUATION_RING_IMP_INTEGRAL_DOMAIN ← prove
    r"!r:A ring. valuation_ring r ==> integral_domain r"
    (SIMP_TAC [valuation_ring])

  let VALUATION_RING_IDEALS_TOTALLY_ORDERED ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"s SUBSET t \/ t SUBSET s <=>
    ~(?a b:A. a IN s /\ ~(a IN t) /\ b IN t /\ ~(b IN s))")
    prove
      r"!r i j:A->bool.
          valuation_ring r /\ ring_ideal r i /\ ring_ideal r j
          ==> i SUBSET j \/ j SUBSET i"
      (REWRITE_TAC [valuation_ring] THEN REPEAT STRIP_TAC THEN REWRITE_TAC [r1] THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPECL [(← q r"a:A"), (← q r"b:A")])) THEN ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET, ring_divides, IN_RING_IDEAL_RMUL])

  let VALUATION_RING_IMP_LOCAL ← prove
    r"!r:A ring. valuation_ring r ==> local_ring r"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [local_ring, EXISTS_UNIQUE] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP VALUATION_RING_IMP_INTEGRAL_DOMAIN)) THEN MP_TAC (← ISPEC (← q r"r:A ring") MAXIMAL_IDEAL_EXISTS) THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"m:A->bool") THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"n:A->bool") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"n:A->bool")] VALUATION_RING_IDEALS_TOTALLY_ORDERED) THEN ASM_SIMP_TAC [MAXIMAL_IMP_RING_IDEAL] THEN ASM_MESON_TAC [maximal_ideal, PSUBSET, SUBSET_ANTISYM])

  let VALUATION_RING_IMP_INTEGRALLY_CLOSED ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_add r (ring_1 r) (ring_mul r d t) = ring_0 r
    ==> a = ring_mul r (ring_mul r a d) (ring_neg r (t:A))")
    let r2 ← RING_RULE (← q r"ring_mul r c (ring_mul r d x) = ring_mul r d (ring_mul r c (x:A))")
    let r3 ← RING_RULE (← q r"ring_mul r x (ring_add r (ring_1 r) y) =
      ring_add r x (ring_mul r x (y:A))")
    let r10 ← RING_RULE (← q r"ring_mul r c (ring_mul r x (ring_mul r y z)) =
      ring_mul r (ring_mul r x y) (ring_mul r c (z:A))")
    let r11 ← TAUT (← q r"(p ==> q) ==> p \/ q ==> q")
    prove
      r"!r:A ring. valuation_ring r ==> integrally_closed r"
      (GEN_TAC THEN REWRITE_TAC [valuation_ring, INTEGRALLY_CLOSED_ALT] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A"), (← q r"c:num->A"), (← q r"n:num")] THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPECL [(← q r"a:A"), (← q r"b:A")])) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r11 THEN GEN_REWRITE_TAC LAND_CONV [ring_divides] THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"d:A") STRIP_ASSUME_TAC) THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_CASES_TAC (← q r"a:A = ring_0 r") THENL [ASM_SIMP_TAC [RING_DIVIDES_0, RING_MUL, RING_0], ALL_TAC] THEN ABBREV_TAC (← q r"s = ring_sum r {i | i < n}
           (\i. ring_mul r (c i) (ring_pow r (d:A) (n - i)))") THEN SUBGOAL_THEN (← q r"(s:A) IN ring_carrier r") ASSUME_TAC THENL [EXPAND_TAC "s" THEN REWRITE_TAC [RING_SUM], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sum r {i | i < n}
       (\i. ring_mul r (c i) (ring_mul r (ring_pow r a i)
                      (ring_pow r (ring_mul r a d) (n - i)))) =
      ring_mul r (ring_pow r a n) (s:A)") ASSUME_TAC THENL [EXPAND_TAC "s" THEN wPart rand (rand o rand) RING_SUM_LMUL THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_POW, FINITE_NUMSEG_LT, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL THEN ASM_SIMP_TAC [RING_POW], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"i:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(c:num->A) i IN ring_carrier r") ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [RING_MUL_POW] THEN SUBGOAL_THEN (← q r"ring_pow r (a:A) n = ring_mul r (ring_pow r a i) (ring_pow r a (n - i))") SUBST1_TAC THENL [ASM_SIMP_TAC [(← GSYM RING_POW_ADD)] THEN AP_TERM_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN ASM_SIMP_TAC [RING_POW, r10], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_add r (ring_1 r) (s:A) = ring_0 r") ASSUME_TAC THENL [FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do if ← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); pure (is_eq z4)) then (do let z9 ← (q r"ring_0 r:A"); let z8 ← (do let z6 ← (do let z7 ← (pure th); pure (concl z7)); liftExcept (rand z6)); pure (z8 == z9)) else pure false)))) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ring_pow r (a:A) n"), (← q r"ring_add r (ring_1 r) (s:A)")] INTEGRAL_DOMAIN_MUL_EQ_0) THEN ASM_SIMP_TAC [RING_POW, RING_ADD, RING_1, INTEGRAL_DOMAIN_POW_EQ_0, r3], ALL_TAC] THEN ASM_CASES_TAC (← q r"n = 0") THENL [UNDISCH_TAC (← q r"ring_add r (ring_1 r) (s:A) = ring_0 r") THEN EXPAND_TAC "s" THEN REWRITE_TAC [(← ASSUME (← q r"n = 0")), LT, EMPTY_GSPEC, RING_SUM_CLAUSES] THEN ASM_SIMP_TAC [RING_ADD_RZERO, RING_1, (← GSYM TRIVIAL_RING_10), INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING], ALL_TAC] THEN ABBREV_TAC (← q r"t = ring_sum r {i | i < n}
           (\i. ring_mul r (c i) (ring_pow r (d:A) (n - 1 - i)))") THEN SUBGOAL_THEN (← q r"(t:A) IN ring_carrier r /\ s = ring_mul r d t") STRIP_ASSUME_TAC THENL [EXPAND_TAC "t" THEN REWRITE_TAC [RING_SUM] THEN EXPAND_TAC "s" THEN wPart rand (rand o rand) RING_SUM_LMUL THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL THEN ASM_SIMP_TAC [RING_POW], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"i:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(c:num->A) i IN ring_carrier r") ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"n - i = SUC(n - 1 - i)") SUBST1_TAC THENL [ASM_ARITH_TAC, REWRITE_TAC [ring_pow]] THEN ASM_SIMP_TAC [RING_POW, r2], ALL_TAC] THEN REWRITE_TAC [ring_divides] THEN ASM_SIMP_TAC [RING_MUL] THEN EXISTS_TAC (← q r"ring_neg r (t:A)") THEN ASM_SIMP_TAC [RING_NEG] THEN UNDISCH_TAC (← q r"ring_add r (ring_1 r) (s:A) = ring_0 r") THEN ASM_REWRITE_TAC [] THEN MP_TAC r1 THEN ASM_SIMP_TAC [])

  let VALUATION_RING_QUOTIENT_RING ← prove
    r"!r p:A->bool.
        valuation_ring r /\ prime_ideal r p
        ==> valuation_ring (quotient_ring r p)"
    (REPEAT GEN_TAC THEN REWRITE_TAC [valuation_ring] THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_QUOTIENT_RING, QUOTIENT_RING_CARRIER] THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_GSPEC] THEN X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN X_GEN_TAC (← q r"b:A") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPECL [(← q r"a:A"), (← q r"b:A")])) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_OR THEN CONJ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC RING_DIVIDES_HOMOMORPHIC_IMAGE THEN EXISTS_TAC (← q r"r:A ring") THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_COSET])

  let VALUATION_SUBRING_SUPERSET ← prove
    r"!k b c:A->bool.
        valuation_subring k b /\ b SUBSET c /\ c subring_of k
        ==> valuation_subring k c"
    (REWRITE_TAC [valuation_subring] THEN SET_TAC [])

  let VALUATION_SUBRING_IMP_VALUATION_RING ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul k y (ring_inv k y) = ring_1 k
      ==> x = ring_mul k y (ring_mul k (ring_inv k y) (x:A))")
    let r2 ← RING_RULE (← q r"ring_mul k x (ring_inv k x) = ring_1 k
      ==> y = ring_mul k x (ring_mul k y (ring_inv k (x:A)))")
    prove
      r"!k b:A->bool.
          valuation_subring k b ==> valuation_ring (subring_generated k b)"
      (REPEAT GEN_TAC THEN REWRITE_TAC [valuation_subring, valuation_ring] THEN STRIP_TAC THEN CONJ_TAC THENL [ASM_SIMP_TAC [INTEGRAL_DOMAIN_SUBRING_GENERATED, FIELD_IMP_INTEGRAL_DOMAIN], ALL_TAC] THEN ASM_SIMP_TAC [ring_divides, CARRIER_SUBRING_GENERATED_SUBRING, (← CONJUNCT2 SUBRING_GENERATED)] THEN MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"y:A")] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier k /\ y IN ring_carrier k /\
                  ring_0 k IN b") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [subring_of, SUBSET], ALL_TAC] THEN ASM_CASES_TAC (← q r"x:A = ring_0 k") THENL [DISJ2_TAC THEN EXISTS_TAC (← q r"ring_0 k:A") THEN ASM_SIMP_TAC [RING_MUL_RZERO], ALL_TAC] THEN ASM_CASES_TAC (← q r"y:A = ring_0 k") THENL [DISJ1_TAC THEN EXISTS_TAC (← q r"ring_0 k:A") THEN ASM_SIMP_TAC [RING_MUL_RZERO], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"ring_mul k y (ring_inv k x):A"))) THEN ASM_SIMP_TAC [RING_MUL, RING_INV, FIELD_IMP_INTEGRAL_DOMAIN, INTEGRAL_DOMAIN_MUL_EQ_0, FIELD_INV_EQ_0] THEN SUBGOAL_THEN (← q r"ring_unit k (x:A) /\ ring_unit k (y:A)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_UNIT], ALL_TAC] THEN ASM_SIMP_TAC [RING_INV_MUL, RING_INV, RING_INV_INV] THEN STRIP_TAC THENL [DISJ1_TAC THEN EXISTS_TAC (← q r"ring_mul k y (ring_inv k x):A") THEN ASM_REWRITE_TAC [] THEN MP_TAC r2 THEN ASM_SIMP_TAC [RING_INV, FIELD_MUL_RINV], DISJ2_TAC THEN EXISTS_TAC (← q r"ring_mul k (ring_inv k y) x:A") THEN ASM_REWRITE_TAC [] THEN MP_TAC r1 THEN ASM_SIMP_TAC [RING_INV, FIELD_MUL_RINV]])

  let VALUATION_SUBRING_IMP_LOCAL ← prove
    r"!k b:A->bool.
        valuation_subring k b ==> local_ring (subring_generated k b)"
    (SIMP_TAC [VALUATION_SUBRING_IMP_VALUATION_RING, VALUATION_RING_IMP_LOCAL])

  let VALUATION_SUBRING_MAXIMAL_IDEAL ← prove
    r"!k b m:A->bool.
        valuation_subring k b
        ==> (maximal_ideal (subring_generated k b) m <=>
             m = {x | x IN b /\ (x = ring_0 k \/ ~(ring_inv k x IN b))})"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [valuation_subring])) THEN ASM_SIMP_TAC [LOCAL_RING_MAXIMAL_IDEAL_NONUNITS, VALUATION_SUBRING_IMP_LOCAL, CARRIER_SUBRING_GENERATED_SUBRING] THEN AP_TERM_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:A") THEN ASM_CASES_TAC (← q r"(x:A) IN b") THEN ASM_SIMP_TAC [RING_UNIT_SUBRING_OF_FIELD] THEN CONV_TAC TAUT)

  let VALUATION_SUBRING_INV_MAXIMAL_IDEAL ← prove
    r"!(k:A ring) v m x.
        valuation_subring k v /\ maximal_ideal (subring_generated k v) m /\
        x IN ring_carrier k
        ==> (x IN v <=> x = ring_0 k \/ ~(ring_inv k x IN m))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"v:A->bool"), (← q r"m:A->bool")] VALUATION_SUBRING_MAXIMAL_IDEAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [valuation_subring])) THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_CASES_TAC (← q r"x:A = ring_0 k") THEN ASM_REWRITE_TAC [] THENL [ASM_MESON_TAC [subring_of], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(ring_inv k (x:A) = ring_0 k) /\ ring_inv k (ring_inv k x) = x") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_INV_EQ_0] THEN MATCH_MP_TAC RING_INV_INV THEN ASM_SIMP_TAC [FIELD_UNIT], ASM_REWRITE_TAC []] THEN ASM_MESON_TAC [])

  let VALUATION_SUBRING_SUBFIELD ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!(k:A ring) v m l.
          valuation_subring k v /\ maximal_ideal (subring_generated k v) m /\
          l subfield_of k
          ==> valuation_subring (subfield_generated k l) (v INTER l) /\
              maximal_ideal
               (subring_generated (subfield_generated k l) (v INTER l))
               (m INTER l)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [valuation_subring])) THEN SUBGOAL_THEN (← q r"field(subfield_generated k l) /\
      ring_carrier(subfield_generated k l) = (l:A->bool) /\
      l SUBSET ring_carrier k /\
      !x:A. x IN l /\ ~(x = ring_0 k)
            ==> ring_inv (subfield_generated k l) x = ring_inv k x /\
                ring_inv k x IN l") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, CARRIER_SUBFIELD_GENERATED_SUBFIELD, IN_SUBFIELD_INV, SUBFIELD_OF_IMP_SUBSET] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_INV_SUBFIELD_GENERATED THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, CARRIER_SUBFIELD_GENERATED_SUBFIELD], ALL_TAC] THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [ASM_REWRITE_TAC [valuation_subring, SUBFIELD_GENERATED] THEN CONJ_TAC THENL [UNDISCH_TAC (← q r"(v:A->bool) subring_of k") THEN FIRST_ASSUM (MP_TAC o (MATCH_MP SUBFIELD_IMP_SUBRING_OF)) THEN ASM_REWRITE_TAC [subring_of, SUBFIELD_GENERATED] THEN SET_TAC [], ASM_SIMP_TAC [IN_INTER] THEN ASM SET_TAC []], DISCH_TAC THEN ASM_SIMP_TAC [VALUATION_SUBRING_MAXIMAL_IDEAL] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"v:A->bool"), (← q r"m:A->bool")] VALUATION_SUBRING_MAXIMAL_IDEAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [SUBFIELD_GENERATED, EXTENSION, IN_INTER, IN_ELIM_THM] THEN ASM_MESON_TAC []])

  let VALUATION_SUBRING_INTEGRAL_ELEMENT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul k b d = ring_1 k
    ==> ring_mul k (ring_mul k a b) (ring_mul k c d) = ring_mul k c (a:A)")
    let r2 ← RING_RULE (← q r"ring_mul k a b = ring_1 k ==> ring_mul k a (ring_mul k b x) = (x:A)")
    let r9 ← RING_RULE (← q r"ring_add k x t = ring_0 k ==> x = ring_neg k (t:A)")
    let r10 ← TAUT (← q r"(~p ==> p) ==> p")
    prove
      r"!k b x:A.
          valuation_subring k b /\
          integral_element (subring_generated k b,k) I x
          ==> x IN b"
      (REPEAT STRIP_TAC THEN FIRST_X_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [valuation_subring])) THEN MP_TAC (← ISPECL [(← q r"subring_generated k (b:A->bool)"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"x:A")] INTEGRAL_ELEMENT_EXPLICIT) THEN REWRITE_TAC [I_DEF, RING_HOMOMORPHISM_INCLUSION] THEN REWRITE_TAC [(← GSYM I_DEF), I_THM] THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"n:num") (X_CHOOSE_THEN (← q r"c:num->A") STRIP_ASSUME_TAC))) THEN MATCH_MP_TAC r10 THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(!y:A. y IN b ==> y IN ring_carrier k) /\ ring_0 k IN b /\
      ring_1 k IN b /\ (!y:A. y IN b ==> ring_neg k y IN b) /\
      (!y z:A. y IN b /\ z IN b ==> ring_mul k y z IN b)") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"(b:A->bool) subring_of k") THEN SIMP_TAC [subring_of, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(x:A = ring_0 k)") ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"y = ring_inv k (x:A)") THEN SUBGOAL_THEN (← q r"(y:A) IN b /\ ring_mul k y x = ring_1 k") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [FIELD_MUL_LINV], ALL_TAC] THEN SUBGOAL_THEN (← q r"(y:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. i < n ==> (c:num->A) i IN ring_carrier k") ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. ring_mul k (ring_pow k y i) (ring_pow k x i) = ring_1 k:A") ASSUME_TAC THENL [ASM_SIMP_TAC [(← GSYM RING_MUL_POW), RING_POW_ONE], ALL_TAC] THEN ABBREV_TAC (← q r"t = ring_sum k {i | i < n}
           (\i. ring_mul k (c i) (ring_pow k (y:A) (n - 1 - i)))") THEN SUBGOAL_THEN (← q r"(t:A) IN b") ASSUME_TAC THENL [EXPAND_TAC "t" THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"b:A->bool"), (← q r"{i:num | i < n}"), (← q r"\i. ring_mul k (c i) (ring_pow k (y:A) (n - 1 - i))")] RING_SUM_SUBRING_GENERATED) THEN REWRITE_TAC [(← ASSUME (← q r"(b:A->bool) subring_of k"))] THEN SUBGOAL_THEN (← q r"{j | j IN {i:num | i < n} /\
             ring_mul k (c j) (ring_pow k (y:A) (n - 1 - j)) IN b} =
        {i | i < n}") SUBST1_TAC THENL [REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC (← q r"j:num") THEN EQ_TAC THEN SIMP_TAC [] THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC [] THEN SPEC_TAC ((← q r"n - 1 - j"), (← q r"m:num")) THEN INDUCT_TAC THEN ASM_SIMP_TAC [ring_pow], DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"subring_generated k (b:A->bool)"), (← q r"{i:num | i < n}"), (← q r"\i. ring_mul k (c i) (ring_pow k (y:A) (n - 1 - i))")] RING_SUM) THEN SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING, (← ASSUME (← q r"(b:A->bool) subring_of k"))]], ALL_TAC] THEN SUBGOAL_THEN (← q r"x = ring_neg k (t:A)") SUBST1_TAC THENL [ALL_TAC, ASM_SIMP_TAC []] THEN SUBGOAL_THEN (← q r"ring_add k x (t:A) = ring_0 k") MP_TAC THENL [ALL_TAC, MP_TAC r9 THEN ASM_SIMP_TAC []] THEN FIRST_X_ASSUM (MP_TAC o ((AP_TERM (← q r"ring_mul k (ring_pow k (y:A) (n - 1))")) o (checkM (fun th => (do if ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); pure (is_eq z3)) then (do let z8 ← (q r"ring_0 k:A"); let z7 ← (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); liftExcept (rand z5)); pure (z7 == z8)) else pure false))))) THEN ASM_SIMP_TAC [RING_MUL_RZERO, RING_POW] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [RING_ADD_LDISTRIB, RING_POW, RING_SUM] THEN BINOP_TAC THENL [SUBGOAL_THEN (← q r"n = (n - 1) + 1") SUBST1_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN ASM_SIMP_TAC [RING_POW_ADD, RING_POW_1, ADD_SUB, RING_POW, r2], ALL_TAC] THEN wPart rand (rand o rand) RING_SUM_LMUL THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_POW, FINITE_NUMSEG_LT, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL THEN ASM_SIMP_TAC [RING_POW], DISCH_THEN (SUBST1_TAC o SYM)] THEN EXPAND_TAC "t" THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"i:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_pow k (y:A) (n - 1) =
                  ring_mul k (ring_pow k y (n - 1 - i)) (ring_pow k y i)") SUBST1_TAC THENL [ASM_SIMP_TAC [(← GSYM RING_POW_ADD)] THEN AP_TERM_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"(c:num->A) i IN ring_carrier k") ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [RING_POW, r1])

  let VALUATION_SUBRING_INTEGRAL_CLOSURE ← prove
    r"!k b:A->bool.
        valuation_subring k b
        ==> {x | integral_element (subring_generated k b,k) I x} = b"
    (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:A") THEN EQ_TAC THENL [ASM_MESON_TAC [VALUATION_SUBRING_INTEGRAL_ELEMENT], ALL_TAC] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"subring_generated k (b:A->bool)"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"x:A")] INTEGRAL_ELEMENT_IMAGE) THEN REWRITE_TAC [I_THM] THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC [I_DEF, RING_HOMOMORPHISM_INCLUSION] THEN FIRST_X_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [valuation_subring])) THEN ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING])

  let IDEAL_GENERATED_ADJOIN_OR_INV ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let p1 ← prove r"!r cn dj a b e:A.
        cn IN ring_carrier r /\ dj IN ring_carrier r /\ a IN ring_carrier r /\
        b IN ring_carrier r /\ e IN ring_carrier r /\ ring_mul r b e = ring_1 r
        ==> ring_mul r (ring_mul r cn (ring_mul r a b)) (ring_mul r dj e) =
            ring_mul r (ring_mul r cn dj) a" (REPEAT STRIP_TAC THEN RING_TAC)
    let mul_lemma := p1
    let p2 ← prove r"!r cn d0 a s:A.
        cn IN ring_carrier r /\ d0 IN ring_carrier r /\ a IN ring_carrier r /\
        s IN ring_carrier r /\
        ring_add r (ring_mul r (ring_mul r cn d0) a) s = ring_mul r cn a
        ==> s = ring_mul r (ring_sub r (ring_1 r) d0) (ring_mul r cn a)" (REPEAT STRIP_TAC THEN RING_TAC)
    let split_lemma := p2
    let p3 ← prove r"!r w u ci e xi:A.
        w IN ring_carrier r /\ u IN ring_carrier r /\ ci IN ring_carrier r /\
        e IN ring_carrier r /\ xi IN ring_carrier r
        ==> ring_mul r (ring_mul r w (ring_add r (ring_mul r u ci) e)) xi =
            ring_mul r w (ring_add r (ring_mul r u (ring_mul r ci xi))
                                     (ring_mul r e xi))" (REPEAT STRIP_TAC THEN RING_TAC)
    let term1_lemma := p3
    let p4 ← prove r"!r w u ci xi:A.
        w IN ring_carrier r /\ u IN ring_carrier r /\ ci IN ring_carrier r /\
        xi IN ring_carrier r
        ==> ring_mul r (ring_mul r w (ring_add r (ring_mul r u ci) (ring_0 r)))
                       xi =
            ring_mul r w (ring_add r (ring_mul r u (ring_mul r ci xi))
                                     (ring_0 r))" (REPEAT STRIP_TAC THEN RING_TAC)
    let term0_lemma := p4
    let p5 ← prove r"!r w u s cx:A.
        w IN ring_carrier r /\ u IN ring_carrier r /\ s IN ring_carrier r /\
        cx IN ring_carrier r /\
        ring_mul r w u = ring_1 r /\ ring_add r s cx = ring_1 r
        ==> ring_mul r w (ring_add r (ring_mul r u s) (ring_mul r u cx)) =
            ring_1 r" (REPEAT STRIP_TAC THEN RING_TAC)
    let final_lemma := p5
    let q6 ← q r"i:num"
    let q7 ← q r"ring_sum k (0..n-1)
       (\i. ring_mul k (ring_inv k u)
             (ring_add k (ring_mul k u (ring_mul k ((c:num->A) i)
                                                   (ring_pow k x i)))
                (if n <= i + q
                 then ring_mul k (ring_mul k (c n) (d (n - i)))
                                 (ring_pow k x i)
                 else ring_0 k)))"
    let q8 ← q r"!i. ring_mul k ((c:num->A) i) (ring_pow k x i) IN ring_carrier k"
    let q9 ← q r"ring_inv k (u:A) IN ring_carrier k"
    let q10 ← q r"!i. (if n <= i + q
           then ring_mul k (ring_mul k ((c:num->A) n) (d (n - i)))
                           (ring_pow k x i)
           else ring_0 k) IN ring_carrier k"
    let q11 ← q r"(!i. (c:num->A) i IN ring_carrier k) /\
      (!j. (d:num->A) j IN ring_carrier k)"
    let q12 ← q r"n:num"
    let q13 ← q r"0"
    let q14 ← q r"\i. ring_mul k ((c:num->A) i) (ring_pow k x i)"
    let q15 ← q r"k:A ring"
    let v16 ← ISPECL [q15, q14, q13, q12] RING_SUM_CLAUSES_RIGHT
    let q17 ← q r"ring_sum k (0..n) (\i. ring_mul k ((c:num->A) i) (ring_pow k x i)) =
        ring_1 k"
    let q18 ← q r"ring_add k (ring_sum k (0..n-1)
                    (\i. ring_mul k ((c:num->A) i) (ring_pow k x i)))
                 (ring_mul k (c n) (ring_pow k x n)) = ring_1 k"
    let q19 ← q r"!x y:A. x IN m /\ y IN m ==> ring_add k x y IN m"
    let v20 ← ASSUME q19
    let q21 ← q r"!x y:A. x IN r /\ y IN m ==> ring_mul k x y IN m"
    let v22 ← ASSUME q21
    let q23 ← q r"i:num"
    let q24 ← q r"\i. ring_mul k (ring_inv k u)
           (ring_add k (ring_mul k u ((c:num->A) i))
              (if n <= i + q then ring_mul k (c n) (d (n - i))
               else ring_0 k))"
    let q25 ← q r"n - (n - i) = i:num"
    let q26 ← q r"i:num"
    let q27 ← q r"\j:num. n - j"
    let q28 ← q r"\i:num. n - i"
    let v29 ← GSYM RING_SUM_RESTRICT_SET
    let q30 ← q r"ring_sum k (1..q)
         (\j. ring_mul k (ring_mul k ((c:num->A) n) (d j))
                         (ring_pow k x (n - j))) =
        ring_mul k u (ring_mul k (c n) (ring_pow k x n))"
    let q31 ← q r"ring_sum k (0..n-1)
        (\i. if n <= i + q
             then ring_mul k (ring_mul k ((c:num->A) n) (d (n - i)))
                             (ring_pow k x i)
             else ring_0 k) =
      ring_mul k u (ring_mul k (c n) (ring_pow k x n))"
    let q32 ← q r"ring_sum k (1..q)
        (\j. ring_mul k (ring_mul k ((c:num->A) n) (d j))
                        (ring_pow k x (n - j))) =
      ring_mul k u (ring_mul k (c n) (ring_pow k x n))"
    let q33 ← q r"(d:num->A) 0 IN ring_carrier k"
    let q34 ← q r"q:num"
    let q35 ← q r"0"
    let q36 ← q r"\j. ring_mul k (ring_mul k ((c:num->A) n) (d j))
                                     (ring_pow k x (n - j))"
    let q37 ← q r"k:A ring"
    let v38 ← ISPECL [q37, q36, q35, q34] RING_SUM_CLAUSES_LEFT
    let q39 ← q r"ring_sum k (0..q)
         (\j. ring_mul k (ring_mul k ((c:num->A) n) (d j))
                         (ring_pow k x (n - j))) =
        ring_mul k (c n) (ring_pow k x n)"
    let q40 ← q r"ring_add k
       (ring_mul k (ring_mul k ((c:num->A) n) (d 0)) (ring_pow k x n))
       (ring_sum k (1..q)
         (\j. ring_mul k (ring_mul k (c n) (d j)) (ring_pow k x (n - j)))) =
      ring_mul k (c n) (ring_pow k x n)"
    let v41 ← GSYM RING_POW_ADD
    let q42 ← q r"ring_pow k x n =
        ring_mul k (ring_pow k x (n - j)) (ring_pow k (x:A) j)"
    let q43 ← q r"(d:num->A) j IN ring_carrier k"
    let q44 ← q r"j:num"
    let v45 ← GSYM RING_SUM_LMUL
    let q46 ← q r"ring_mul k (ring_mul k ((c:num->A) n) (ring_pow k x n))
                   (ring_sum k (0..q)
                      (\j. ring_mul k (d j) (ring_pow k (y:A) j)))"
    let q47 ← q r"ring_sum k (0..q)
        (\j. ring_mul k (ring_mul k ((c:num->A) n) (d j))
                        (ring_pow k x (n - j))) =
      ring_mul k (c n) (ring_pow k x n)"
    let q48 ← q r"(c:num->A) n IN ring_carrier k"
    let v49 ← GSYM RING_MUL_POW
    let q50 ← q r"!j. ring_mul k (ring_pow k x j) (ring_pow k (y:A) j) = ring_1 k"
    let q51 ← q r"ring_mul k (ring_inv k u) (u:A) = ring_1 k"
    let q52 ← q r"ring_inv k (u:A) IN r"
    let q53 ← q r"~(u:A = ring_0 k)"
    let q54 ← q r"(u:A) IN ring_carrier k"
    let v55 ← GSYM RING_ADD_ASSOC
    let q56 ← q r"ring_1 k = ring_add k (ring_add k (ring_1 k) (ring_neg k (d 0)))
                              ((d:num->A) 0)"
    let q57 ← q r"~(ring_1 k IN (m:A->bool))"
    let q58 ← q r"(d:num->A) 0 IN r /\ d 0 IN ring_carrier k"
    let q59 ← q r"(u:A) IN r /\ ~(u IN m)"
    let q60 ← q r"u = ring_sub k (ring_1 k) ((d:num->A) 0)"
    let q61 ← q r"ring_sum k (0..0) (\j. ring_mul k (d j) (ring_pow k (y:A) j)) =
        ring_1 k"
    let q62 ← q r"~(q = 0)"
    let q63 ← q r"!u:A. u IN m ==> u IN r /\ u IN ring_carrier k"
    let q64 ← q r"(r:A->bool) subring_of k"
    let v65 ← CONJUNCT2 SUBRING_GENERATED
    let q66 ← q r"ring_ideal (subring_generated k r) (m:A->bool)"
    let q67 ← q r"ring_carrier(subring_generated k r) = (r:A->bool)"
    let p68 ← prove r"!k r m x y (c:num->A) d n q.
        field k /\ r subring_of k /\ ring_ideal (subring_generated k r) m /\
        (!z. z IN r /\ ~(z IN m) ==> ring_inv k z IN r) /\ ~(ring_1 k IN m) /\
        x IN ring_carrier k /\ y IN ring_carrier k /\
        ring_mul k x y = ring_1 k /\
        (!i. c i IN m) /\ (!j. d j IN m) /\
        ring_sum k (0..n) (\i. ring_mul k (c i) (ring_pow k x i)) = ring_1 k /\
        ring_sum k (0..q) (\j. ring_mul k (d j) (ring_pow k y j)) = ring_1 k /\
        q <= n
        ==> ~(n = 0) /\
            ?c'. (!i. c' i IN m) /\
                 ring_sum k (0..n-1) (\i. ring_mul k (c' i) (ring_pow k x i)) =
                 ring_1 k" (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN q67 ASSUME_TAC THENL [ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING], ALL_TAC] THEN UNDISCH_TAC q66 THEN ASM_REWRITE_TAC [ring_ideal, v65] THEN STRIP_TAC THEN UNDISCH_TAC q64 THEN REWRITE_TAC [subring_of] THEN STRIP_TAC THEN SUBGOAL_THEN q63 ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN q62 ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC q61 THEN REWRITE_TAC [RING_SUM_CLAUSES_NUMSEG, ring_pow] THEN ASM_SIMP_TAC [RING_MUL_RID, RING_MUL, RING_1] THEN ASM_MESON_TAC [], ALL_TAC] THEN CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN ABBREV_TAC q60 THEN SUBGOAL_THEN q59 STRIP_ASSUME_TAC THENL [SUBGOAL_THEN q58 STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN EXPAND_TAC "u" THEN REWRITE_TAC [ring_sub] THEN CONJ_TAC THENL [ASM_MESON_TAC [], DISCH_TAC] THEN UNDISCH_TAC q57 THEN REWRITE_TAC [] THEN SUBGOAL_THEN q56 SUBST1_TAC THENL [ASM_SIMP_TAC [v55, RING_ADD_LNEG, RING_ADD_RZERO, RING_NEG, RING_1], ASM_MESON_TAC []], ALL_TAC] THEN SUBGOAL_THEN q54 ASSUME_TAC THENL [ASM_MESON_TAC [SUBSET], ALL_TAC] THEN SUBGOAL_THEN q53 ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN q52 ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN q51 ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_MUL_LINV], ALL_TAC] THEN SUBGOAL_THEN q50 ASSUME_TAC THENL [ASM_SIMP_TAC [v49, RING_POW_ONE], ALL_TAC] THEN SUBGOAL_THEN q48 ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN q47 ASSUME_TAC THENL [TRANS_TAC EQ_TRANS q46 THEN CONJ_TAC THENL [ALL_TAC, ASM_REWRITE_TAC [] THEN MATCH_MP_TAC RING_MUL_RID THEN ASM_MESON_TAC [RING_MUL, RING_POW]] THEN ASM_SIMP_TAC [v45, FINITE_NUMSEG, RING_MUL, RING_POW] THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC q44 THEN REWRITE_TAC [IN_NUMSEG] THEN STRIP_TAC THEN SUBGOAL_THEN q43 ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN q42 SUBST1_TAC THENL [ASM_SIMP_TAC [v41] THEN AP_TERM_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC mul_lemma THEN ASM_SIMP_TAC [RING_POW], ALL_TAC] THEN SUBGOAL_THEN q40 ASSUME_TAC THENL [UNDISCH_TAC q39 THEN DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [(← SYM th)])) THEN CONV_TAC SYM_CONV THEN MP_TAC v38 THEN REWRITE_TAC [LE_0, ADD_CLAUSES, SUB_0] THEN SUBGOAL_THEN q33 ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [RING_MUL, RING_POW], ALL_TAC] THEN SUBGOAL_THEN q32 ASSUME_TAC THENL [EXPAND_TAC "u" THEN MATCH_MP_TAC split_lemma THEN ASM_SIMP_TAC [RING_SUM, RING_POW] THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN q31 ASSUME_TAC THENL [UNDISCH_TAC q30 THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [v29] THEN MATCH_MP_TAC RING_SUM_EQ_GENERAL_INVERSES THEN MAP_EVERY EXISTS_TAC [q28, q27] THEN REWRITE_TAC [IN_ELIM_THM, IN_NUMSEG] THEN CONJ_TAC THEN X_GEN_TAC q26 THEN STRIP_TAC THENL [ASM_ARITH_TAC, SUBGOAL_THEN q25 SUBST1_TAC THENL [ASM_ARITH_TAC, REWRITE_TAC [] THEN ASM_ARITH_TAC]], ALL_TAC] THEN EXISTS_TAC q24 THEN REWRITE_TAC [] THEN CONJ_TAC THENL [X_GEN_TAC q23 THEN MATCH_MP_TAC v22 THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC v20 THEN CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN COND_CASES_TAC THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN q18 ASSUME_TAC THENL [UNDISCH_TAC q17 THEN MP_TAC v16 THEN ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN ASM_SIMP_TAC [RING_MUL, RING_POW], ALL_TAC] THEN SUBGOAL_THEN q11 STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN q10 ASSUME_TAC THENL [GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [RING_0, RING_MUL, RING_POW], ALL_TAC] THEN SUBGOAL_THEN q9 ASSUME_TAC THENL [ASM_MESON_TAC [SUBSET], ALL_TAC] THEN SUBGOAL_THEN q8 ASSUME_TAC THENL [ASM_SIMP_TAC [RING_MUL, RING_POW], ALL_TAC] THEN TRANS_TAC EQ_TRANS q7 THEN CONJ_TAC THENL [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC q6 THEN DISCH_TAC THEN REWRITE_TAC [] THEN COND_CASES_TAC THEN REWRITE_TAC [] THENL [MATCH_MP_TAC term1_lemma, MATCH_MP_TAC term0_lemma] THEN ASM_SIMP_TAC [RING_POW, RING_MUL], ALL_TAC] THEN ASM_SIMP_TAC [RING_SUM_LMUL, RING_SUM_ADD, FINITE_NUMSEG, RING_MUL, RING_POW, RING_ADD] THEN MATCH_MP_TAC final_lemma THEN ASM_SIMP_TAC [RING_SUM, RING_MUL, RING_POW])
    let reduce_lemma := p68
    let q69 ← q r"d':num->A"
    let q70 ← q r"c:num->A"
    let q71 ← q r"q - 1:num"
    let q72 ← q r"n:num"
    let q73 ← q r"n + (q - 1):num"
    let q74 ← q r"d':num->A"
    let q75 ← q r"n:num"
    let q76 ← q r"q:num"
    let q77 ← q r"c:num->A"
    let q78 ← q r"d:num->A"
    let q79 ← q r"x:A"
    let q80 ← q r"y:A"
    let q81 ← q r"m:A->bool"
    let q82 ← q r"r:A->bool"
    let q83 ← q r"k:A ring"
    let v84 ← ISPECL [q83, q82, q81, q80, q79, q78, q77, q76, q75] reduce_lemma
    let q85 ← q r"d:num->A"
    let q86 ← q r"c':num->A"
    let q87 ← q r"q:num"
    let q88 ← q r"n - 1:num"
    let q89 ← q r"(n - 1) + q:num"
    let q90 ← q r"c':num->A"
    let q91 ← q r"q:num"
    let q92 ← q r"n:num"
    let q93 ← q r"d:num->A"
    let q94 ← q r"c:num->A"
    let q95 ← q r"y:A"
    let q96 ← q r"x:A"
    let q97 ← q r"m:A->bool"
    let q98 ← q r"r:A->bool"
    let q99 ← q r"k:A ring"
    let v100 ← ISPECL [q99, q98, q97, q96, q95, q94, q93, q92, q91] reduce_lemma
    let q101 ← q r"q <= n \/ n <= q:num"
    let r102 ← ARITH_RULE q101
    let q103 ← q r"d:num->A"
    let q104 ← q r"c:num->A"
    let q105 ← q r"q:num"
    let q106 ← q r"n:num"
    let q107 ← q r"N:num"
    let q108 ← q r"!N n q (c:num->A) d.
        n + q = N /\ (!i. c i IN m) /\ (!j. d j IN m) /\
        ring_sum k (0..n) (\i. ring_mul k (c i) (ring_pow k x i)) = ring_1 k /\
        ring_sum k (0..q) (\j. ring_mul k (d j) (ring_pow k y j)) = ring_1 k
        ==> F"
    let q109 ← q r"y = ring_inv k (x:A)"
    let q110 ← q r"~p \/ ~q <=> ~(p /\ q)"
    let r111 ← TAUT q110
    let q112 ← q r"ring_inv k (x:A) IN ring_carrier k /\
    ring_mul k x (ring_inv k x) = ring_1 k /\
    ring_mul k (ring_inv k x) x = ring_1 k"
    prove
      r"!(k:A ring) r m x.
          field k /\ r subring_of k /\ ring_ideal (subring_generated k r) m /\
          (!z. z IN r /\ ~(z IN m) ==> ring_inv k z IN r) /\ ~(ring_1 k IN m) /\
          x IN ring_carrier k /\ ~(x = ring_0 k)
          ==> ~(ring_1 k IN
                ideal_generated (subring_generated k (x INSERT r)) m) \/
              ~(ring_1 k IN
                ideal_generated (subring_generated k (ring_inv k x INSERT r)) m)"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN q112 STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_INV, FIELD_MUL_RINV, FIELD_MUL_LINV], ALL_TAC] THEN ASM_SIMP_TAC [IDEAL_GENERATED_ADJOIN_EXPLICIT] THEN REWRITE_TAC [r111] THEN ABBREV_TAC q109 THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SUBGOAL_THEN q108 (fun th => MESON_TAC [th]) THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC q107 THEN DISCH_THEN (LABEL_TAC "ind") THEN MAP_EVERY X_GEN_TAC [q106, q105, q104, q103] THEN STRIP_TAC THEN DISJ_CASES_TAC r102 THENL [MP_TAC v100 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN q90 STRIP_ASSUME_TAC)) THEN USE_THEN "ind" (MP_TAC o (SPEC q89)) THEN ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN DISCH_THEN (MP_TAC o (SPECL [q88, q87, q86, q85])) THEN ASM_REWRITE_TAC [], MP_TAC v84 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN q74 STRIP_ASSUME_TAC)) THEN USE_THEN "ind" (MP_TAC o (SPEC q73)) THEN ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN DISCH_THEN (MP_TAC o (SPECL [q72, q71, q70, q69])) THEN ASM_REWRITE_TAC []])

  -- @@RETURN BEGIN
  return { valuation_ring, valuation_subring, VALUATION_RING_IMP_INTEGRAL_DOMAIN,
           VALUATION_RING_IDEALS_TOTALLY_ORDERED, VALUATION_RING_IMP_LOCAL,
           VALUATION_RING_IMP_INTEGRALLY_CLOSED, VALUATION_RING_QUOTIENT_RING,
           VALUATION_SUBRING_SUPERSET, VALUATION_SUBRING_IMP_VALUATION_RING,
           VALUATION_SUBRING_IMP_LOCAL, VALUATION_SUBRING_MAXIMAL_IDEAL,
           VALUATION_SUBRING_INV_MAXIMAL_IDEAL, VALUATION_SUBRING_SUBFIELD,
           VALUATION_SUBRING_INTEGRAL_ELEMENT, VALUATION_SUBRING_INTEGRAL_CLOSURE,
           IDEAL_GENERATED_ADJOIN_OR_INV }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- valuation_ring.ml phrases from line 799 to 956                         -/
/- ---------------------------------------------------------------------- -/

structure ValuationRing02 where
  -- @@FIELDS
  RING_HOMOMORPHISM_ADJOIN_ROOT : thm
  VALUATION_SUBRING_DOMINATES : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupValuationRing02 [HolBase] (D : ValuationRingDeps) (BValuationRing01 : ValuationRing01) :
    ExceptT String IO ValuationRing02 := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, RING_RULE, SET_RULE,
        SET_TAC, TAUT, .. } := D
  let { ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD, CARRIER_SUBRING_GENERATED_SUBRING,
        COEFF_ABOVE_DEG, COEFF_COMPOSE, COEFF_IN_CARRIER_ALT, EQ_TRANS, EXTENSION,
        FIELD_MUL_LINV, FINITE_IMAGE, FINITE_NUMSEG, FINITE_SUBSET_UNIONS_CHAIN,
        IDEAL_GENERATED_ADJOIN_EXPLICIT, IDEAL_GENERATED_ADJOIN_INV,
        IDEAL_GENERATED_ADJOIN_ROOT_UNIT, IDEAL_GENERATED_EXPLICIT,
        IDEAL_GENERATED_INC, IDEAL_GENERATED_MONO, IDEAL_GENERATED_RING_IDEAL,
        IN_ELIM_THM, IN_INSERT, IN_INTER, IN_RING_IDEAL_0, IN_RING_IDEAL_LMUL,
        IN_RING_POLYNOMIAL_CARRIER_COMPOSE, IN_UNIONS, I_DEF, MAXIMAL_IMP_PRIME_IDEAL,
        MAXIMAL_IMP_RING_IDEAL, MAXIMAL_SUPERIDEAL_EXISTS, MEMBER_NOT_EMPTY,
        MONO_EXISTS, NOT_EXISTS_THM, POLY_EXTEND_CONST_VARPOW, POLY_EXTEND_EVALUATE,
        POLY_EXTEND_RING_SUM, POLY_EXTEND_UNIVARIATE, .. } := D.core1
  let { POLY_TOP_EQ_0, PRIME_IDEAL_IMP_SUBSET, PRIME_IMP_RING_IDEAL, PROPER_IDEAL_ALT,
        RIGHT_FORALL_IMP_THM, RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_INCLUSION,
        RING_HOMOMORPHISM_POLY_EXTEND, RING_IDEAL_IDEAL_GENERATED,
        RING_IDEAL_IMP_SUBSET, RING_IDEAL_POLY_COMMON_ROOT, RING_IDEAL_RING_KERNEL,
        RING_INV, RING_MUL, RING_MUL_ASSOC, RING_POLYNOMIAL, RING_POLYNOMIAL_CONST,
        RING_POLYNOMIAL_MUL, RING_POLYNOMIAL_POW, RING_POLYNOMIAL_VAR, RING_POW,
        RING_POW_IN_PRIME_IDEAL, RING_POW_SUBRING_GENERATED, RING_SUM, RING_SUM_EQ,
        RING_SUM_LMUL, RING_SUM_SUBRING_GENERATED, RING_UNIT_1,
        RING_UNIT_NOT_IN_PRIME_IDEAL, SUBRING_GENERATED,
        SUBRING_GENERATED_BY_SUBRING_GENERATED, SUBRING_GENERATED_INC_GEN,
        SUBRING_OF_UNIONS, SUBRING_SUBRING_GENERATED, SUBSET, SUBSET_REFL,
        SUBSET_TRANS, ZL_SUBSETS_UNIONS_NONEMPTY, poly_eval, prime_ideal, ring_kernel,
        ring_pow, subring_of, .. } := D.core2
  let { IDEAL_GENERATED_ADJOIN_OR_INV, valuation_subring, .. } := BValuationRing01
  -- @@SCOPE END

  let RING_HOMOMORPHISM_ADJOIN_ROOT ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let v1 ← GSYM RING_POLYNOMIAL
    let p2 ← prove r"!(r:A ring) (r':C ring) h x (c:num->A) n.
        ring_homomorphism(r,r') h /\ x IN ring_carrier r' /\
        (!i. c i IN ring_carrier r)
        ==> poly_extend (r,r') h (\v:1. x)
              (ring_sum (poly_ring r (:1)) (0..n)
                 (\i. poly_mul r (poly_const r (c i))
                        (poly_pow r (poly_var r one) i))) =
            ring_sum r' (0..n) (\i. ring_mul r' (h(c i)) (ring_pow r' x i))" (REPEAT STRIP_TAC THEN wPart lhand (lhand o rand) POLY_EXTEND_RING_SUM THEN ASM_REWRITE_TAC [FINITE_NUMSEG, v1] THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_POLYNOMIAL_MUL, RING_POLYNOMIAL_CONST, RING_POLYNOMIAL_POW, RING_POLYNOMIAL_VAR], DISCH_THEN SUBST1_TAC] THEN MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC [POLY_EXTEND_CONST_VARPOW])
    let sum_lemma := p2
    let v3 ← GSYM poly_eval
    let q4 ← q r"ring_sum (poly_ring (subring_generated k s) (:1)) (0..n)
        (\i. poly_mul (subring_generated k s)
               (poly_const (subring_generated k s) ((a:num->A) i))
               (poly_pow (subring_generated k s)
                  (poly_var (subring_generated k s) one) i))"
    let q5 ← q r"\v:1. (w:B)"
    let q6 ← q r"g:A->B"
    let q7 ← q r"l:B ring"
    let q8 ← q r"subring_generated k (s:A->bool)"
    let v9 ← ISPECL [q8, q7, q6, q5, q4] POLY_EXTEND_EVALUATE
    let q19 ← q r"ring_sum (poly_ring (subring_generated k s) (:1)) (0..n)
      (\i. poly_mul (subring_generated k s)
             (poly_const (subring_generated k s) ((a:num->A) i))
             (poly_pow (subring_generated k s)
                (poly_var (subring_generated k s) one) i))"
    let q20 ← q r"a:num->A"
    let q21 ← q r"n:num"
    let q22 ← q r"w:B"
    let q23 ← q r"ring_inv k (coeff 0 (p:(1->num)->A))"
    let q24 ← q r"\i. coeff i (p:(1->num)->A)"
    let q25 ← q r"poly_deg (subring_generated k s) (p:(1->num)->A)"
    let q26 ← q r"~(ring_1 k IN ideal_generated (subring_generated k (y INSERT s))
                     {z:A | z IN s /\ (g:A->B) z = ring_0 l})"
    let q27 ← q r"p:(1->num)->A"
    let q28 ← q r"\v:1. (y:A)"
    let q29 ← q r"\x:A. x"
    let q30 ← q r"k:A ring"
    let q31 ← q r"subring_generated k (s:A->bool)"
    let v32 ← ISPECL [q31, q30, q29, q28, q27] POLY_EXTEND_UNIVARIATE
    let q33 ← q r"poly_extend (subring_generated k s,k) (\x:A. x) (\v:1. y) p =
        ring_0 k"
    let q34 ← q r"ring_sum k (0..poly_deg (subring_generated k s) p)
        (\i. ring_mul k (coeff i (p:(1->num)->A)) (ring_pow k y i)) =
      ring_0 k"
    let v35 ← CONJUNCT2 SUBRING_GENERATED
    let q36 ← q r"~((g:A->B)(coeff 0 (p:(1->num)->A)) = ring_0 l)"
    let q37 ← q r"(coeff 0 (p:(1->num)->A)) IN ring_carrier k /\
      ~(coeff 0 (p:(1->num)->A) = ring_0 k)"
    let q38 ← q r"(g:A->B) o (p:(1->num)->A)"
    let q39 ← q r"l:B ring"
    let v40 ← ISPECL [q39, q38] POLY_TOP_EQ_0
    let q41 ← q r"~(coeff 0 ((g:A->B) o (p:(1->num)->A)) = ring_0 l) /\
      (!i. 1 <= i ==> coeff i ((g:A->B) o (p:(1->num)->A)) = ring_0 l)"
    let q42 ← q r"ring_carrier(subring_generated k s) =
                             (s:A->bool)"
    let v43 ← ASSUME q42
    let v44 ← SYM v43
    let q45 ← q r"!i. coeff i (p:(1->num)->A) IN s"
    let q46 ← q r"subring_generated k (s:A->bool)"
    let q47 ← q r"ring_polynomial (subring_generated k s) (p:(1->num)->A) /\
      ring_polynomial l ((g:A->B) o p)"
    let q48 ← q r"(~p ==> F) ==> p"
    let r49 ← TAUT q48
    let q50 ← q r"p:(1->num)->A"
    let q51 ← q r"j:((1->num)->A)->bool"
    let q52 ← q r"g:A->B"
    let q53 ← q r"l:B ring"
    let q54 ← q r"subring_generated k (s:A->bool)"
    let v55 ← ISPECL [q54, q53, q52, q51] RING_IDEAL_POLY_COMMON_ROOT
    let q56 ← q r"j = ring_kernel (poly_ring (subring_generated k s) (:1),k)
          (poly_extend (subring_generated k s,k) (\x:A. x) (\v:1. y))"
    let q57 ← q r"{z:A | z IN s /\ (g:A->B) z = ring_0 l} =
      ring_kernel(subring_generated k s,l) g"
    let q58 ← q r"ring_ideal (subring_generated k s) {z:A | z IN s /\ (g:A->B) z = ring_0 l}"
    let q59 ← q r"ring_carrier(subring_generated k s) = (s:A->bool)"
    prove
      r"!(k:A ring) (l:B ring) s g y.
          field k /\ algebraically_closed_field l /\ s subring_of k /\
          ring_homomorphism(subring_generated k s,l) g /\
          (!z. z IN s /\ ~(g z = ring_0 l) ==> ring_inv k z IN s) /\
          y IN ring_carrier k /\
          ~(ring_1 k IN ideal_generated (subring_generated k (y INSERT s))
                         {z | z IN s /\ g z = ring_0 l})
          ==> ?w. w IN ring_carrier l /\
                  !n a. (!i. a i IN s) /\
                        ring_sum k (0..n)
                          (\i. ring_mul k (a i) (ring_pow k y i)) = ring_0 k
                        ==> ring_sum l (0..n)
                              (\i. ring_mul l (g(a i)) (ring_pow l w i)) =
                            ring_0 l"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN q59 ASSUME_TAC THENL [ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING], ALL_TAC] THEN SUBGOAL_THEN q58 ASSUME_TAC THENL [SUBGOAL_THEN q57 SUBST1_TAC THENL [ASM_REWRITE_TAC [ring_kernel], MATCH_MP_TAC RING_IDEAL_RING_KERNEL THEN ASM_REWRITE_TAC []], ALL_TAC] THEN ABBREV_TAC q56 THEN MP_TAC v55 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [EXPAND_TAC "j" THEN MATCH_MP_TAC RING_IDEAL_RING_KERNEL THEN MATCH_MP_TAC RING_HOMOMORPHISM_POLY_EXTEND THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INCLUSION], ALL_TAC] THEN X_GEN_TAC q50 THEN EXPAND_TAC "j" THEN REWRITE_TAC [ring_kernel, IN_ELIM_THM] THEN STRIP_TAC THEN MATCH_MP_TAC r49 THEN DISCH_TAC THEN SUBGOAL_THEN q47 STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC [RING_POLYNOMIAL] THEN MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN EXISTS_TAC q46 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN q45 ASSUME_TAC THENL [GEN_TAC THEN SUBST1_TAC v44 THEN MATCH_MP_TAC COEFF_IN_CARRIER_ALT THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN q41 MP_TAC THENL [CONJ_TAC THENL [MP_TAC v40 THEN ASM_REWRITE_TAC [], REPEAT STRIP_TAC THEN MATCH_MP_TAC COEFF_ABOVE_DEG THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC], REWRITE_TAC [COEFF_COMPOSE] THEN STRIP_TAC] THEN SUBGOAL_THEN q37 STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [ASM_MESON_TAC [subring_of, SUBSET], DISCH_TAC THEN UNDISCH_TAC q36 THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP RING_HOMOMORPHISM_0)) THEN REWRITE_TAC [v35]], ALL_TAC] THEN SUBGOAL_THEN q34 ASSUME_TAC THENL [UNDISCH_TAC q33 THEN MP_TAC v32 THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INCLUSION] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [], ALL_TAC] THEN UNDISCH_TAC q26 THEN REWRITE_TAC [] THEN MATCH_MP_TAC IDEAL_GENERATED_ADJOIN_ROOT_UNIT THEN MAP_EVERY EXISTS_TAC [q25, q24, q23] THEN ASM_SIMP_TAC [FIELD_MUL_LINV, IN_ELIM_THM], ALL_TAC] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC q22 THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MAP_EVERY X_GEN_TAC [q21, q20] THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC q19) o (checkM (fun th => (do if ← (do let z10 ← (do let z11 ← (pure th); pure (concl z11)); pure (is_forall z10)) then (do let z12 ← (do let z13 ← (pure th); pure (concl z13)); canM (fun z14 => (do let z15 ← (pure z14); find_termM (fun z16 => (do let z18 ← (pure z16); let z17 ← (q r"j:((1->num)->A)->bool"); pure (z17 == z18))) z15)) z12) else pure false))))) THEN EXPAND_TAC "j" THEN REWRITE_TAC [ring_kernel, IN_ELIM_THM, RING_SUM] THEN ASM_SIMP_TAC [sum_lemma, RING_HOMOMORPHISM_INCLUSION] THEN MP_TAC v9 THEN ASM_REWRITE_TAC [v3] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [sum_lemma])

  let VALUATION_SUBRING_DOMINATES ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!s. s SUBSET t /\ (x:A) IN s ==> x IN t")
    let r2 ← TAUT (← q r"(~p ==> F) ==> p")
    let r3 ← RING_RULE (← q r"ring_mul k (ring_inv k u) u = ring_1 k
        ==> ring_pow k z n =
            ring_mul k (ring_inv k u) (ring_mul k u (ring_pow k (z:A) n))")
    let r4 ← SET_RULE (← q r"s SUBSET t ==> (x:A) IN s ==> x IN t")
    prove
      r"!k a p:A->bool.
          field k /\ a subring_of k /\ prime_ideal (subring_generated k a) p
          ==> ?b m. valuation_subring k b /\ a SUBSET b /\
                    maximal_ideal (subring_generated k b) m /\ a INTER m = p"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"ring_carrier(subring_generated k a) = (a:A->bool)") ASSUME_TAC THENL [ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING], ALL_TAC] THEN SUBGOAL_THEN (← q r"p SUBSET a /\ a SUBSET ring_carrier k /\ ring_1 k IN a /\
      ring_0 k IN (p:A->bool) /\ ~(ring_1 k IN p) /\
      (!x y. x IN a /\ y IN a ==> ring_mul k x y IN a) /\
      (!x y. x IN a /\ y IN a /\ ring_mul k x y IN p ==> x IN p \/ y IN p)") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"subring_generated k (a:A->bool)"), (← q r"p:A->bool"), (← q r"ring_1(subring_generated k a):A")] RING_UNIT_NOT_IN_PRIME_IDEAL) THEN MP_TAC (← ISPECL [(← q r"subring_generated k (a:A->bool)"), (← q r"p:A->bool")] IN_RING_IDEAL_0) THEN MP_TAC (← ISPECL [(← q r"subring_generated k (a:A->bool)"), (← q r"p:A->bool")] PRIME_IDEAL_IMP_SUBSET) THEN UNDISCH_TAC (← q r"prime_ideal (subring_generated k a) (p:A->bool)") THEN UNDISCH_TAC (← q r"(a:A->bool) subring_of k") THEN ASM_SIMP_TAC [prime_ideal, (← CONJUNCT2 SUBRING_GENERATED), RING_UNIT_1] THEN SIMP_TAC [subring_of] THEN MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPEC (← q r"\R:A->bool. R subring_of k /\ a SUBSET R /\
                  !t. t IN a /\ ~(t IN p)
                      ==> ~(t IN ideal_generated (subring_generated k R) p)") ZL_SUBSETS_UNIONS_NONEMPTY) THEN REWRITE_TAC [] THEN ANTS_TAC THENL [CONJ_TAC THENL [EXISTS_TAC (← q r"a:A->bool") THEN ASM_SIMP_TAC [SUBSET_REFL] THEN ASM_SIMP_TAC [IDEAL_GENERATED_RING_IDEAL], ALL_TAC] THEN X_GEN_TAC (← q r"c:(A->bool)->bool") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "allP") (LABEL_TAC "chain"))) THEN SUBGOAL_THEN (← q r"UNIONS c subring_of (k:A ring)") ASSUME_TAC THENL [MATCH_MP_TAC SUBRING_OF_UNIONS THEN ASM_SIMP_TAC [(← GSYM MEMBER_NOT_EMPTY)] THEN USE_THEN "allP" (fun th => MESON_TAC [th]), ALL_TAC] THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [FIRST_X_ASSUM (X_CHOOSE_TAC (← q r"S0:A->bool")) THEN USE_THEN "allP" (MP_TAC o (SPEC (← q r"S0:A->bool"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN REWRITE_TAC [SUBSET, IN_UNIONS] THEN X_GEN_TAC (← q r"z:A") THEN DISCH_TAC THEN EXISTS_TAC (← q r"S0:A->bool") THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"(a:A->bool) SUBSET S0") THEN UNDISCH_TAC (← q r"(z:A) IN a") THEN SET_TAC [], ALL_TAC] THEN X_GEN_TAC (← q r"t:A") THEN STRIP_TAC THEN ASM_SIMP_TAC [IDEAL_GENERATED_EXPLICIT, CARRIER_SUBRING_GENERATED_SUBRING, IN_ELIM_THM, (← CONJUNCT2 SUBRING_GENERATED), NOT_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"K:A->bool"), (← q r"f:A->A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"IMAGE (f:A->A) K SUBSET UNIONS c") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"c:(A->bool)->bool"), (← q r"IMAGE (f:A->A) K")] FINITE_SUBSET_UNIONS_CHAIN) THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_IMAGE, (← GSYM MEMBER_NOT_EMPTY)], DISCH_THEN (X_CHOOSE_THEN (← q r"S:A->bool") STRIP_ASSUME_TAC)] THEN USE_THEN "allP" (MP_TAC o (SPEC (← q r"S:A->bool"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"t:A"))) THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [IDEAL_GENERATED_EXPLICIT, CARRIER_SUBRING_GENERATED_SUBRING, IN_ELIM_THM, (← CONJUNCT2 SUBRING_GENERATED)] THEN MAP_EVERY EXISTS_TAC [(← q r"K:A->bool"), (← q r"f:A->A")] THEN REPEAT CONJ_TAC THENL [ASM_REWRITE_TAC [], ASM_REWRITE_TAC [], ASM SET_TAC [], ASM SET_TAC [], ALL_TAC] THEN FIRST_X_ASSUM (SUBST1_TAC o (checkM (fun th => (do if ← (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); pure (is_eq z5)) then (do let z10 ← (q r"t:A"); let z9 ← (do let z7 ← (do let z8 ← (pure th); pure (concl z8)); liftExcept (lhs z7)); pure (z9 == z10)) else pure false)))) THEN SUBGOAL_THEN (← q r"UNIONS c SUBSET ring_carrier(k:A ring)") ASSUME_TAC THENL [UNDISCH_TAC (← q r"UNIONS c subring_of (k:A ring)") THEN SIMP_TAC [subring_of], ALL_TAC] THEN SUBGOAL_THEN (← q r"(S:A->bool) SUBSET UNIONS c") ASSUME_TAC THENL [REWRITE_TAC [SUBSET, IN_UNIONS] THEN MESON_TAC [(← ASSUME (← q r"(S:A->bool) IN c"))], ALL_TAC] THEN ASM_SIMP_TAC [RING_SUM_SUBRING_GENERATED] THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC (← q r"i:A") THEN ASM_CASES_TAC (← q r"(i:A) IN K") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(f:A->A) i IN S /\ (i:A) IN S") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN UNDISCH_TAC (← q r"(S:A->bool) subring_of k") THEN UNDISCH_TAC (← q r"UNIONS c subring_of (k:A ring)") THEN REWRITE_TAC [subring_of] THEN ASM SET_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"R:A->bool") (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "max"))) THEN SUBGOAL_THEN (← q r"p SUBSET (R:A->bool)") ASSUME_TAC THENL [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC (← q r"a:A->bool") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!t:A. t IN a ==> t IN R") ASSUME_TAC THENL [UNDISCH_TAC (← q r"(a:A->bool) SUBSET R") THEN REWRITE_TAC [SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"(!x:A. x IN R ==> x IN ring_carrier k) /\ ring_0 k IN R /\
      ring_1 k IN R /\ (!x y. x IN R /\ y IN R ==> ring_mul k x y IN R) /\
      ring_carrier(subring_generated k R) = R") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING] THEN UNDISCH_TAC (← q r"(R:A->bool) subring_of k") THEN SIMP_TAC [subring_of, SUBSET], ALL_TAC] THEN ABBREV_TAC (← q r"J = ideal_generated (subring_generated k R) (p:A->bool)") THEN SUBGOAL_THEN (← q r"ring_ideal (subring_generated k R) (J:A->bool) /\ p SUBSET J /\
      J SUBSET R") STRIP_ASSUME_TAC THENL [EXPAND_TAC "J" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN CONJ_TAC THENL [REWRITE_TAC [SUBSET] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN ASM_REWRITE_TAC [], MP_TAC (← ISPECL [(← q r"subring_generated k (R:A->bool)"), (← q r"ideal_generated (subring_generated k R) (p:A->bool)")] RING_IDEAL_IMP_SUBSET) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!u:A. u IN J ==> u IN R") ASSUME_TAC THENL [UNDISCH_TAC (← q r"(J:A->bool) SUBSET R") THEN REWRITE_TAC [SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"!y:A. y IN ring_carrier k /\
            (!t. t IN a /\ ~(t IN p)
                 ==> ~(t IN ideal_generated (subring_generated k (y INSERT R))
                                             p))
            ==> y IN R") (LABEL_TAC "H") THENL [REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"(R:A->bool) SUBSET ring_carrier(subring_generated k (y INSERT R))") ASSUME_TAC THENL [REWRITE_TAC [SUBSET] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN ASM_SIMP_TAC [IN_INSERT], ALL_TAC] THEN SUBGOAL_THEN (← q r"R = ring_carrier(subring_generated k ((y:A) INSERT R))") SUBST1_TAC THENL [USE_THEN "max" MATCH_MP_TAC THEN REWRITE_TAC [SUBRING_SUBRING_GENERATED, SUBRING_GENERATED_BY_SUBRING_GENERATED] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC (← q r"R:A->bool") THEN ASM_REWRITE_TAC [], MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN ASM_REWRITE_TAC [IN_INSERT]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!y u:A. u IN ideal_generated (subring_generated k (y INSERT R)) p
              ==> u IN ideal_generated (subring_generated k (y INSERT R)) J") ASSUME_TAC THENL [REPEAT GEN_TAC THEN MATCH_MP_TAC r4 THEN MATCH_MP_TAC IDEAL_GENERATED_MONO THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x y:A. x IN a /\ ~(x IN p) /\ y IN a /\ ~(y IN p)
              ==> ring_mul k x y IN a /\ ~(ring_mul k x y IN p)") ASSUME_TAC THENL [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"!x y:A. x IN a /\ y IN a /\ ring_mul k x y IN p ==> x IN p \/ y IN p") THEN DISCH_THEN (MP_TAC o (SPECL [(← q r"x:A"), (← q r"y:A")])) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!t:A n. t IN a /\ ~(t IN p)
              ==> ring_pow k t n IN a /\ ~(ring_pow k t n IN p)") ASSUME_TAC THENL [GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC [ring_pow], ALL_TAC] THEN SUBGOAL_THEN (← q r"!t:A. t IN a /\ ~(t IN p) ==> ~(t = ring_0 k) /\ ring_inv k t IN R") (LABEL_TAC "tunit") THENL [X_GEN_TAC (← q r"t:A") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"~(t:A = ring_0 k)") ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC (← q r"~((t:A) IN p)") THEN ASM_REWRITE_TAC [], ASM_REWRITE_TAC []] THEN SUBGOAL_THEN (← q r"(t:A) IN R /\ t IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN USE_THEN "H" MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_INV] THEN X_GEN_TAC (← q r"u:A") THEN STRIP_TAC THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"R:A->bool"), (← q r"J:A->bool"), (← q r"t:A"), (← q r"u:A")] IDEAL_GENERATED_ADJOIN_INV) THEN ANTS_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"n:num")) THEN SUBGOAL_THEN (← q r"ring_mul k u (ring_pow k t n) IN a /\
        ~(ring_mul k u (ring_pow k (t:A) n) IN p)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN UNDISCH_TAC (← q r"!t:A. t IN a /\ ~(t IN p) ==> ~(t IN J)") THEN DISCH_THEN (MP_TAC o (SPEC (← q r"ring_mul k u (ring_pow k (t:A) n)"))) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"proper_ideal (subring_generated k R) (J:A->bool)") ASSUME_TAC THENL [ASM_REWRITE_TAC [PROPER_IDEAL_ALT] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"!t:A. t IN a /\ ~(t IN p) ==> ~(t IN J)") THEN DISCH_THEN (MP_TAC o (SPEC (← q r"ring_1 k:A"))) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP MAXIMAL_SUPERIDEAL_EXISTS)) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"m:A->bool") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"prime_ideal (subring_generated k R) (m:A->bool) /\
      ring_ideal (subring_generated k R) m") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [MAXIMAL_IMP_PRIME_IDEAL, MAXIMAL_IMP_RING_IDEAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"m SUBSET R /\ ring_0 k IN m /\ ~(ring_1 k IN m) /\
      (!x y. x IN R /\ y IN m ==> ring_mul k x y IN m) /\
      (!x n. x IN R /\ ring_pow k x n IN m ==> x IN (m:A->bool))") STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"subring_generated k (R:A->bool)"), (← q r"m:A->bool")] RING_IDEAL_IMP_SUBSET) THEN ASM_REWRITE_TAC [], MP_TAC (← ISPECL [(← q r"subring_generated k (R:A->bool)"), (← q r"m:A->bool")] IN_RING_IDEAL_0) THEN ASM_REWRITE_TAC [(← CONJUNCT2 SUBRING_GENERATED)], MP_TAC (← ISPECL [(← q r"subring_generated k (R:A->bool)"), (← q r"m:A->bool"), (← q r"ring_1(subring_generated k R):A")] RING_UNIT_NOT_IN_PRIME_IDEAL) THEN ASM_REWRITE_TAC [RING_UNIT_1, (← CONJUNCT2 SUBRING_GENERATED)], MP_TAC (← ISPECL [(← q r"subring_generated k (R:A->bool)"), (← q r"m:A->bool")] IN_RING_IDEAL_LMUL) THEN ASM_REWRITE_TAC [(← CONJUNCT2 SUBRING_GENERATED)], REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"subring_generated k (R:A->bool)"), (← q r"m:A->bool"), (← q r"x:A"), (← q r"n:num")] RING_POW_IN_PRIME_IDEAL) THEN ASM_REWRITE_TAC [RING_POW_SUBRING_GENERATED] THEN MESON_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"!u:A. u IN J ==> u IN m") ASSUME_TAC THENL [UNDISCH_TAC (← q r"(J:A->bool) SUBSET m") THEN REWRITE_TAC [SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"!z:A. z IN R /\ ~(z IN m) ==> ~(z = ring_0 k) /\ ring_inv k z IN R") (LABEL_TAC "local") THENL [X_GEN_TAC (← q r"z:A") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"~(z:A = ring_0 k)") ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC (← q r"~((z:A) IN m)") THEN ASM_REWRITE_TAC [], ASM_REWRITE_TAC []] THEN SUBGOAL_THEN (← q r"(z:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN USE_THEN "H" MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_INV] THEN X_GEN_TAC (← q r"u:A") THEN STRIP_TAC THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"R:A->bool"), (← q r"J:A->bool"), (← q r"z:A"), (← q r"u:A")] IDEAL_GENERATED_ADJOIN_INV) THEN ANTS_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"n:num")) THEN USE_THEN "tunit" (MP_TAC o (SPEC (← q r"u:A"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN SUBGOAL_THEN (← q r"(u:A) IN R /\ u IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN UNDISCH_TAC (← q r"~(z:A IN m)") THEN REWRITE_TAC [] THEN UNDISCH_TAC (← q r"!x n. x IN R /\ ring_pow k x n IN m ==> x IN (m:A->bool)") THEN DISCH_THEN (MATCH_MP_TAC o (SPECL [(← q r"z:A"), (← q r"n:num")])) THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ring_pow k z n =
        ring_mul k (ring_inv k u) (ring_mul k u (ring_pow k (z:A) n))") SUBST1_TAC THENL [MP_TAC r3 THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_INV, RING_POW], ALL_TAC] THEN DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC FIELD_MUL_LINV THEN ASM_REWRITE_TAC [], UNDISCH_TAC (← q r"!x y:A. x IN R /\ y IN m ==> ring_mul k x y IN m") THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_homomorphism(subring_generated k R,k) (I:A->A)") ASSUME_TAC THENL [REWRITE_TAC [I_DEF, RING_HOMOMORPHISM_INCLUSION], ALL_TAC] THEN SUBGOAL_THEN (← q r"!u:A. u IN a /\ ~(u IN p) ==> ~(u IN m)") ASSUME_TAC THENL [X_GEN_TAC (← q r"u:A") THEN STRIP_TAC THEN DISCH_TAC THEN USE_THEN "tunit" (MP_TAC o (SPEC (← q r"u:A"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN UNDISCH_TAC (← q r"~(ring_1 k:A IN m)") THEN REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(u:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_1 k = ring_mul k (ring_inv k u) (u:A)") SUBST1_TAC THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FIELD_MUL_LINV THEN ASM_REWRITE_TAC [], UNDISCH_TAC (← q r"!x y:A. x IN R /\ y IN m ==> ring_mul k x y IN m") THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC []], ALL_TAC] THEN EXISTS_TAC (← q r"R:A->bool") THEN EXISTS_TAC (← q r"m:A->bool") THEN ASM_REWRITE_TAC [valuation_subring] THEN CONJ_TAC THENL [ALL_TAC, GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_INTER] THEN X_GEN_TAC (← q r"x:A") THEN EQ_TAC THENL [STRIP_TAC THEN MATCH_MP_TAC r2 THEN DISCH_TAC THEN UNDISCH_TAC (← q r"!u:A. u IN a /\ ~(u IN p) ==> ~(u IN m)") THEN DISCH_THEN (MP_TAC o (SPEC (← q r"x:A"))) THEN ASM_REWRITE_TAC [], DISCH_TAC THEN UNDISCH_TAC (← q r"p SUBSET (J:A->bool)") THEN UNDISCH_TAC (← q r"p SUBSET (a:A->bool)") THEN REWRITE_TAC [SUBSET] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"x:A"))) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN DISCH_THEN (MP_TAC o (SPEC (← q r"x:A"))) THEN ASM_SIMP_TAC []]] THEN X_GEN_TAC (← q r"x:A") THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"(x:A) IN R") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"?t:A. t IN a /\ ~(t IN p) /\
            t IN ideal_generated (subring_generated k (x INSERT R)) p") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"~((x:A) IN R)") THEN USE_THEN "H" (MP_TAC o (SPEC (← q r"x:A"))) THEN REWRITE_TAC [(← ASSUME (← q r"(x:A) IN ring_carrier k"))] THEN MESON_TAC [], ALL_TAC] THEN USE_THEN "tunit" (MP_TAC o (SPEC (← q r"t:A"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN SUBGOAL_THEN (← q r"(t:A) IN R /\ t IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"R:A->bool"), (← q r"J:A->bool"), (← q r"x:A"), (← q r"t:A")] IDEAL_GENERATED_ADJOIN_EXPLICIT) THEN ASM_SIMP_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"n:num") (X_CHOOSE_THEN (← q r"c:num->A") (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))) THEN SUBGOAL_THEN (← q r"!i. (c:num->A) i IN m /\ c i IN R /\ c i IN ring_carrier k") ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. ring_mul k (ring_inv k t) ((c:num->A) i) IN m") ASSUME_TAC THENL [GEN_TAC THEN UNDISCH_TAC (← q r"!x y:A. x IN R /\ y IN m ==> ring_mul k x y IN m") THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sum k (0..n)
       (\i. ring_mul k (ring_mul k (ring_inv k t) ((c:num->A) i))
                       (ring_pow k x i)) = ring_1 k") ASSUME_TAC THENL [TRANS_TAC EQ_TRANS (← q r"ring_mul k (ring_inv k t)
         (ring_sum k (0..n) (\i. ring_mul k ((c:num->A) i) (ring_pow k x i)))") THEN CONJ_TAC THENL [wPart rand (rand o rand) RING_SUM_LMUL THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_INV, FINITE_NUMSEG, RING_MUL, RING_POW], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN REWRITE_TAC [] THEN MATCH_MP_TAC (← GSYM RING_MUL_ASSOC) THEN ASM_SIMP_TAC [RING_INV, RING_POW], ASM_REWRITE_TAC [] THEN MATCH_MP_TAC FIELD_MUL_LINV THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_1 k IN ideal_generated (subring_generated k (x INSERT R)) (m:A->bool)") ASSUME_TAC THENL [ASM_SIMP_TAC [IDEAL_GENERATED_ADJOIN_EXPLICIT] THEN MAP_EVERY EXISTS_TAC [(← q r"n:num"), (← q r"\i. ring_mul k (ring_inv k t) ((c:num->A) i)")] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"R:A->bool"), (← q r"m:A->bool"), (← q r"x:A")] IDEAL_GENERATED_ADJOIN_OR_INV) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [USE_THEN "local" (fun th => MESON_TAC [th]), DISCH_TAC] THEN USE_THEN "H" MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_INV] THEN X_GEN_TAC (← q r"u:A") THEN STRIP_TAC THEN DISCH_TAC THEN UNDISCH_TAC (← q r"~(ring_1 k IN
        ideal_generated (subring_generated k (ring_inv k x INSERT R))
          (m:A->bool))") THEN REWRITE_TAC [] THEN USE_THEN "tunit" (MP_TAC o (SPEC (← q r"u:A"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN SUBGOAL_THEN (← q r"(u:A) IN R /\ u IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(u:A) IN ideal_generated (subring_generated k (ring_inv k x INSERT R)) m") ASSUME_TAC THENL [MATCH_MP_TAC r1 THEN EXISTS_TAC (← q r"ideal_generated (subring_generated k (ring_inv k x INSERT R))
          (p:A->bool)") THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IDEAL_GENERATED_MONO THEN ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_1 k = ring_mul k (ring_inv k u) (u:A)") SUBST1_TAC THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FIELD_MUL_LINV THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"subring_generated k (ring_inv k x INSERT (R:A->bool))"), (← q r"ideal_generated (subring_generated k
                      (ring_inv k x INSERT R)) (m:A->bool)"), (← q r"ring_inv k u:A"), (← q r"u:A")] IN_RING_IDEAL_LMUL) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, (← CONJUNCT2 SUBRING_GENERATED)] THEN DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN ASM_SIMP_TAC [RING_INV, IN_INSERT])

  -- @@RETURN BEGIN
  return { RING_HOMOMORPHISM_ADJOIN_ROOT, VALUATION_SUBRING_DOMINATES }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- valuation_ring.ml phrases from line 1359 to 1938                       -/
/- ---------------------------------------------------------------------- -/

structure ValuationRing03 where
  -- @@FIELDS
  VALUATION_SUBRING_EXTEND_HOMOMORPHISM : thm
  INTEGRAL_CLOSURE_EQ_INTERS_VALUATION_SUBRINGS : thm
  VALUATION_RING_IMP_BEZOUT_RING : thm
  DVR_IMP_VALUATION_RING : thm
  DVR_EQ_NOETHERIAN_VALUATION_RING : thm
  DVR_EQ_INTEGRALLY_CLOSED : thm
  DVR_DIVIDES_UNIFORMIZER_POW : thm
  VALUATION_SUBRING_DEDEKIND_VALUATION : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupValuationRing03 [HolBase] (D : ValuationRingDeps) (BValuationRing01 : ValuationRing01) (BValuationRing02 : ValuationRing02) :
    ExceptT String IO ValuationRing03 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, GEN_BETA_CONV, INT_ARITH_TAC, MESON, MESON_TAC, RING_RULE,
        SELECT_CONV, SET_RULE, SET_TAC, TAUT, .. } := D
  let { ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD, BEZOUT_RING_2,
        CARRIER_SUBRING_GENERATED_SUBRING, CARRIER_SUBRING_OF, COEFF_IN_CARRIER_ALT,
        DEDEKIND_VALUATION_INV, DEDEKIND_VALUATION_RING_LOCALIZATION, DVR,
        DVR_IDEALS_TOTALLY_ORDERED, DVR_IDEAL_MAXIMAL_POW, DVR_IFF_LOCAL_DEDEKIND,
        EMPTY_SUBSET, ETA_AX, EXISTS_PAIR_THM, EXTENSION, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_INV_EQ_0, FIELD_MUL_RINV, FIELD_NONTRIVIAL, FIELD_POW_EQ_0, FIELD_UNIT,
        FINITE_NUMSEG, FORALL_IN_IMAGE, FORALL_PAIR_THM, FST, IDEAL_GENERATED_EQ_0,
        IDEAL_GENERATED_INC, IDEAL_GENERATED_MINIMAL, IDEAL_GENERATED_MONO,
        IDEAL_POW_PRINCIPAL, IMAGE_I, IMP_IMP, INSERT_SUBSET, INTEGRAL_DOMAIN_MUL_EQ_0,
        INTEGRAL_ELEMENT_IMAGE, INTEGRAL_ELEMENT_IN_ADJOIN_INV,
        INTEGRAL_ELEMENT_OVER_SUBRING, IN_CROSS, IN_ELIM_THM, IN_IDEAL_GENERATED_SELF,
        IN_IDEAL_GENERATED_SING, IN_IDEAL_GENERATED_SING_EQ, IN_IMAGE, IN_INSERT,
        IN_INTERS, IN_NUMSEG, IN_RING_IDEAL_LMUL, IN_SING, IN_SUBRING_POW, IN_UNIONS,
        IN_UNIV, I_DEF, I_THM, MAXIMAL_IMP_PRIME_IDEAL, MAXIMAL_IMP_RING_IDEAL,
        MAXIMAL_SUPERIDEAL_EXISTS, MEMBER_NOT_EMPTY, PAIR_EQ,
        PID_EQ_NOETHERIAN_BEZOUT_DOMAIN, PID_IMP_INTEGRAL_DOMAIN,
        PID_IMP_NOETHERIAN_RING, POLY_CONST, POLY_EXTEND_CONST, POLY_EXTEND_UNIVARIATE,
        POLY_EXTEND_VAR, .. } := D.core1
  let { POLY_VAR, PROD_RING, PROPER_IDEAL_IDEAL_GENERATED_SING, RING_ADD_RNEG,
        RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_INCLUSION, RING_HOMOMORPHISM_PAIRED,
        RING_HOMOMORPHISM_POLY_EXTEND, RING_HOMOMORPHISM_POW, RING_HOMOMORPHISM_SUM,
        RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_RING_KERNEL, RING_INV, RING_INV_INV,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL, RING_MUL_LZERO, RING_MUL_POW,
        RING_MUL_RZERO, RING_POLYNOMIAL, RING_POW, RING_POW_ADD, RING_POW_ONE,
        RING_POW_SUBRING_GENERATED, RING_SUB_EQ_0, RING_SUM, RING_SUM_EQ,
        RING_SUM_LMUL, RING_SUM_SUBRING_GENERATED, RING_UNIT_1,
        RING_UNIT_NOT_IN_PRIME_IDEAL, RING_UNIT_SUBRING_OF_FIELD, SELECT_UNIQUE,
        SING_SUBSET, SUBRING_GENERATED, SUBRING_GENERATED_BY_SUBRING_GENERATED,
        SUBRING_GENERATED_INC_GEN, SUBRING_OF_HOMOMORPHIC_IMAGE, SUBRING_OF_UNIONS,
        SUBRING_RING_IMAGE, SUBRING_SUBRING_GENERATED, SUBSET, SUBSET_ANTISYM,
        SUBSET_REFL, SUBSET_TRANS, SUB_ADD, ZL_SUBSETS_UNIONS_NONEMPTY,
        dedekind_domain, field_of_fractions, o_DEF, principal_ideal, ring_divides,
        ring_homomorphism, ring_image, ring_kernel, ring_sub, subring_of, .. } := D.core2
  let { IDEAL_GENERATED_ADJOIN_OR_INV, VALUATION_RING_IMP_INTEGRAL_DOMAIN,
        VALUATION_RING_IMP_LOCAL, VALUATION_SUBRING_INTEGRAL_ELEMENT,
        VALUATION_SUBRING_MAXIMAL_IDEAL, valuation_ring, valuation_subring, .. } := BValuationRing01
  let { RING_HOMOMORPHISM_ADJOIN_ROOT, VALUATION_SUBRING_DOMINATES, .. } := BValuationRing02
  -- @@SCOPE END

  let VALUATION_SUBRING_EXTEND_HOMOMORPHISM ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"!r p q c u:C.
          ring_mul r q u = ring_1 r
          ==> ring_mul r (ring_mul r p q) (ring_mul r c u) =
              ring_mul r c p"
    let r2 ← RING_RULE q1
    let v3 ← REWRITE_RULE [IMP_IMP] r2
    let v4 ← GSYM RING_MUL_POW
    let q5 ← q r"ring_mul r (ring_pow r (t:C) i) (ring_pow r (ring_inv r t) i) = ring_1 r"
    let v6 ← GSYM RING_POW_ADD
    let q7 ← q r"ring_pow r (t:C) n = ring_mul r (ring_pow r t (n - i)) (ring_pow r t i)"
    let q8 ← q r"i:num"
    let p9 ← prove r"!(r:C ring) t (c:num->C) n.
          field r /\ t IN ring_carrier r /\ ~(t = ring_0 r) /\
          (!i. c i IN ring_carrier r)
          ==> ring_mul r (ring_pow r t n)
                (ring_sum r (0..n)
                   (\i. ring_mul r (c i) (ring_pow r (ring_inv r t) i))) =
              ring_sum r (0..n) (\i. ring_mul r (c i) (ring_pow r t (n - i)))" (REPEAT STRIP_TAC THEN wPart lhand (rand o rand) RING_SUM_LMUL THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_NUMSEG, RING_MUL, RING_POW, RING_INV], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC q8 THEN REWRITE_TAC [IN_NUMSEG] THEN STRIP_TAC THEN REWRITE_TAC [] THEN SUBGOAL_THEN q7 SUBST1_TAC THENL [ASM_SIMP_TAC [v6, SUB_ADD], ALL_TAC] THEN SUBGOAL_THEN q5 ASSUME_TAC THENL [ASM_SIMP_TAC [v4, RING_INV, FIELD_MUL_RINV, RING_POW_ONE], ALL_TAC] THEN MATCH_MP_TAC v3 THEN ASM_SIMP_TAC [RING_POW, RING_INV])
    let invpow_lemma := p9
    let q10 ← q r"ring_homomorphism(subring_generated k s,l) (g:A->B)"
    let v11 ← ASSUME q10
    let v12 ← MATCH_MP RING_HOMOMORPHISM_SUM v11
    let q13 ← q r"0..n"
    let q14 ← q r"h:num->A"
    let v15 ← ISPECL [q14, q13] v12
    let p16 ← prove r"!(k:A ring) (l:B ring) s g (h:num->A) n.
          s subring_of k /\ ring_homomorphism(subring_generated k s,l) g /\
          (!i. h i IN s)
          ==> g(ring_sum k (0..n) h) = ring_sum l (0..n) (\i. g(h i))" (REPEAT STRIP_TAC THEN MP_TAC v15 THEN ASM_SIMP_TAC [FINITE_NUMSEG, CARRIER_SUBRING_GENERATED_SUBRING, o_DEF] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN ASM_SIMP_TAC [RING_SUM_SUBRING_GENERATED] THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN ASM_MESON_TAC [])
    let hom_sum_lemma := p16
    let q17 ← q r"x:A"
    let q18 ← q r"field (l:B ring)"
    let v19 ← ASSUME q18
    let v20 ← MATCH_MP FIELD_NONTRIVIAL v19
    let q21 ← q r"ring_1 k = ring_mul k x (ring_inv k (x:A))"
    let q22 ← q r"(g:A->B)(ring_1 k) = ring_1 l"
    let v23 ← ASSUME q22
    let q24 ← q r"(x:A) IN ring_carrier k"
    let q25 ← q r"x:A = ring_0 k"
    let q26 ← q r"x:A"
    let q27 ← q r"g:A->B"
    let q28 ← q r"{x:A | x IN s /\ (x = ring_0 k \/ ~(ring_inv k x IN s))}"
    let q29 ← q r"s:A->bool"
    let q30 ← q r"x:A"
    let q31 ← q r"{z:A | z IN s /\ (g:A->B) z = ring_0 l}"
    let q32 ← q r"s:A->bool"
    let q33 ← q r"k:A ring"
    let v34 ← ISPECL [q33, q32, q31, q30] IDEAL_GENERATED_ADJOIN_OR_INV
    let q35 ← q r"x:A"
    let q36 ← q r"valuation_subring k (s:A->bool)"
    let q37 ← q r"n:num"
    let q38 ← q r"\i. (g:A->B)((a:num->A) i)"
    let q39 ← q r"(g:A->B) x"
    let q40 ← q r"l:B ring"
    let v41 ← ISPECL [q40, q39, q38, q37] invpow_lemma
    let q42 ← q r"n:num"
    let q43 ← q r"\i. ring_mul k ((a:num->A) i) (ring_pow k x (n - i))"
    let q44 ← q r"g:A->B"
    let q45 ← q r"s:A->bool"
    let q46 ← q r"l:B ring"
    let q47 ← q r"k:A ring"
    let v48 ← ISPECL [q47, q46, q45, q44, q43, q42] hom_sum_lemma
    let q49 ← q r"ring_sum l (0..n)
        (\i. ring_mul l ((g:A->B)((a:num->A) i)) (ring_pow l (g x) (n - i))) =
      ring_0 l"
    let q50 ← q r"n:num"
    let q51 ← q r"a:num->A"
    let q52 ← q r"x:A"
    let q53 ← q r"k:A ring"
    let v54 ← ISPECL [q53, q52, q51, q50] invpow_lemma
    let q55 ← q r"ring_sum k (0..n) (\i. ring_mul k ((a:num->A) i) (ring_pow k x (n - i))) =
      ring_0 k"
    let q56 ← q r"!i. (a:num->A) i IN ring_carrier k /\ (g:A->B)(a i) IN ring_carrier l"
    let q57 ← q r"a:num->A"
    let q58 ← q r"n:num"
    let q59 ← q r"ring_inv l ((g:A->B) x)"
    let q60 ← q r"~((g:A->B) x = ring_0 l)"
    let q61 ← q r"(x:A) IN ring_carrier k /\ ~(x = ring_0 k)"
    let q62 ← q r"x:A"
    let q63 ← q r"!x:A. x IN s /\ ~((g:A->B) x = ring_0 l) ==> ring_inv k x IN s"
    let q64 ← q r"poly_var (subring_generated k (s:A->bool)) one"
    let q65 ← q r"(G:A#B->bool) SUBSET G'"
    let q66 ← q r"!x. x IN r ==> (x,(f:A->B) x) IN G"
    let v67 ← ASSUME q66
    let q68 ← q r"G':A#B->bool"
    let q69 ← q r"(y:A,w:B) IN G"
    let q70 ← q r"p:(1->num)->A"
    let q71 ← q r"\u:1. (y:A)"
    let q72 ← q r"\x:A. x"
    let q73 ← q r"k:A ring"
    let q74 ← q r"subring_generated k (s:A->bool)"
    let v75 ← ISPECL [q74, q73, q72, q71, q70] POLY_EXTEND_UNIVARIATE
    let q76 ← q r"i:num"
    let q77 ← q r"p:(1->num)->A"
    let q78 ← q r"subring_generated k (s:A->bool)"
    let v79 ← ISPECL [q78, q77, q76] COEFF_IN_CARRIER_ALT
    let q89 ← q r"p:(1->num)->A"
    let q90 ← q r"\u:1. (w:B)"
    let q91 ← q r"g:A->B"
    let q92 ← q r"l:B ring"
    let q93 ← q r"subring_generated k (s:A->bool)"
    let v94 ← ISPECL [q93, q92, q91, q90, q89] POLY_EXTEND_UNIVARIATE
    let q95 ← q r"p:(1->num)->A"
    let q96 ← q r"z:B"
    let q97 ← q r"!z. (ring_0 k,z) IN (G':A#B->bool) ==> z = ring_0 l"
    let q98 ← q r"poly_const (subring_generated k s) (x:A):(1->num)->A"
    let q99 ← q r"z:B"
    let q100 ← q r"x:A"
    let q101 ← q r"(G:A#B->bool) SUBSET G'"
    let q102 ← q r"poly_ring (subring_generated k (s:A->bool)) (:1)"
    let q103 ← q r"(G':A#B->bool) subring_of prod_ring k l"
    let q104 ← q r"G' = IMAGE (\p:(1->num)->A.
                    poly_extend (subring_generated k s,k) (\x:A. x) (\u:1. y) p,
                    poly_extend (subring_generated k s,l) (g:A->B) (\u:1. w) p)
                 (ring_carrier(poly_ring (subring_generated k s) (:1)))"
    let q105 ← q r"w:B"
    let q106 ← q r"y:A"
    let q107 ← q r"!y. y IN ring_carrier k /\
        (?w. w IN ring_carrier l /\
             !n a. (!i. a i IN s) /\
                   ring_sum k (0..n)
                     (\i. ring_mul k (a i) (ring_pow k y i)) = ring_0 k
                   ==> ring_sum l (0..n)
                         (\i. ring_mul l ((g:A->B)(a i)) (ring_pow l w i)) =
                       ring_0 l)
        ==> y IN s"
    let q108 ← q r"{z:A | z IN s /\ (g:A->B) z = ring_0 l} =
      ring_kernel(subring_generated k s,l) g"
    let q109 ← q r"ring_ideal (subring_generated k s) {z:A | z IN s /\ (g:A->B) z = ring_0 l}"
    let q110 ← q r"!x. x IN r ==> (x,(f:A->B) x) IN G"
    let v111 ← ASSUME q110
    let q112 ← q r"(r:A->bool) SUBSET s /\ !x. x IN r ==> (g:A->B) x = f x"
    let q113 ← q r"ring_homomorphism(subring_generated k s,l) (g:A->B)"
    let v114 ← ASSUME q113
    let v115 ← MATCH_MP RING_HOMOMORPHISM_POW v114
    let q116 ← q r"!x:A n. x IN s ==> (g:A->B)(ring_pow k x n) = ring_pow l (g x) n"
    let v117 ← CONJUNCT2 SUBRING_GENERATED
    let q118 ← q r"ring_homomorphism(subring_generated k s,l) (g:A->B)"
    let q119 ← q r"(s:A->bool) subring_of k"
    let q120 ← q r"!x:A. x IN s ==> (x,(g:A->B) x) IN G"
    let q121 ← q r"(!x:A. x IN s ==> x IN ring_carrier k /\ (g:A->B) x IN ring_carrier l) /\
    (ring_0 k IN s /\ g(ring_0 k) = ring_0 l) /\
    (ring_1 k IN s /\ g(ring_1 k) = ring_1 l) /\
    (!x. x IN s ==> ring_neg k x IN s /\ g(ring_neg k x) = ring_neg l (g x)) /\
    (!x y. x IN s /\ y IN s
           ==> ring_add k x y IN s /\
               g(ring_add k x y) = ring_add l (g x) (g y)) /\
    (!x y. x IN s /\ y IN s
           ==> ring_mul k x y IN s /\
               g(ring_mul k x y) = ring_mul l (g x) (g y))"
    let q122 ← q r"b:B"
    let q123 ← q r"b:B"
    let q124 ← q r"a:A"
    let q125 ← q r"x:A"
    let q126 ← q r"u:B"
    let q127 ← q r"z:B"
    let q128 ← q r"x:A"
    let q129 ← q r"!x:A z:B. (x,z) IN G <=> x IN s /\ g x = z"
    let q130 ← q r"g = \x:A. @z:B. (x,z) IN G"
    let q131 ← q r"s = IMAGE FST (G:A#B->bool)"
    let q132 ← q r"z':B"
    let q133 ← q r"z:B"
    let q134 ← q r"l:B ring"
    let v135 ← ISPECL [q134, q133, q132] RING_SUB_EQ_0
    let q136 ← q r"ring_0 k = ring_add k (x:A) (ring_neg k x)"
    let q137 ← q r"(ring_0 k,ring_sub l z z') IN (G:A#B->bool)"
    let q138 ← q r"(x:A) IN ring_carrier k /\ (z:B) IN ring_carrier l /\
      (z':B) IN ring_carrier l"
    let q139 ← q r"!x:A z z':B. (x,z) IN G /\ (x,z') IN G ==> z = z'"
    let q140 ← q r"(G:A#B->bool) subring_of prod_ring k l"
    let q141 ← q r"(!x:A z:B. (x,z) IN G ==> x IN ring_carrier k /\ z IN ring_carrier l) /\
    (ring_0 k,ring_0 l) IN G /\ (ring_1 k,ring_1 l) IN G /\
    (!x z. (x,z) IN G ==> (ring_neg k x,ring_neg l z) IN G) /\
    (!x z x' z'. (x,z) IN G /\ (x',z') IN G
                 ==> (ring_add k x x',ring_add l z z') IN G) /\
    (!x z x' z'. (x,z) IN G /\ (x',z') IN G
                 ==> (ring_mul k x x',ring_mul l z z') IN G)"
    let q142 ← q r"G:A#B->bool"
    let v143 ← GSYM MEMBER_NOT_EMPTY
    let q144 ← q r"c:(A#B->bool)->bool"
    let q145 ← q r"subring_generated k (r:A->bool)"
    let q146 ← q r"IMAGE (\x:A. x,(f:A->B) x) r =
          IMAGE (\x. x,f x) (ring_carrier(subring_generated k r))"
    let q147 ← q r"IMAGE (\x:A. x,(f:A->B) x) r"
    let q148 ← q r"\G:A#B->bool. G subring_of prod_ring k l /\
                  (!z. (ring_0 k,z) IN G ==> z = ring_0 l) /\
                  (!x. x IN r ==> (x,(f:A->B) x) IN G)"
    let v149 ← ISPEC q148 ZL_SUBSETS_UNIONS_NONEMPTY
    let v150 ← CONJUNCT2 SUBRING_GENERATED
    let q151 ← q r"(f:A->B)(ring_0 k) = ring_0 l"
    prove
      r"!(k:A ring) (l:B ring) r f.
          field k /\ algebraically_closed_field l /\ r subring_of k /\
          ring_homomorphism(subring_generated k r,l) f
          ==> ?v m g. valuation_subring k v /\
                      maximal_ideal (subring_generated k v) m /\
                      r SUBSET v /\
                      ring_homomorphism(subring_generated k v,l) g /\
                      (!x. x IN r ==> g x = f x) /\
                      (!x. x IN v ==> (g x = ring_0 l <=> x IN m))"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN q151 ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP RING_HOMOMORPHISM_0)) THEN REWRITE_TAC [v150], ALL_TAC] THEN MP_TAC v149 THEN REWRITE_TAC [] THEN ANTS_TAC THENL [CONJ_TAC THENL [EXISTS_TAC q147 THEN REPEAT CONJ_TAC THENL [SUBGOAL_THEN q146 SUBST1_TAC THENL [ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING], ALL_TAC] THEN MATCH_MP_TAC SUBRING_OF_HOMOMORPHIC_IMAGE THEN EXISTS_TAC q145 THEN REWRITE_TAC [CARRIER_SUBRING_OF, RING_HOMOMORPHISM_PAIRED] THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INCLUSION], REWRITE_TAC [IN_IMAGE, PAIR_EQ] THEN ASM_MESON_TAC [], REWRITE_TAC [IN_IMAGE] THEN MESON_TAC []], X_GEN_TAC q144 THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC SUBRING_OF_UNIONS THEN REWRITE_TAC [v143] THEN ASM_MESON_TAC [], REWRITE_TAC [IN_UNIONS] THEN ASM_MESON_TAC [], REWRITE_TAC [IN_UNIONS] THEN ASM_MESON_TAC []]], DISCH_THEN (X_CHOOSE_THEN q142 (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "isg") ASSUME_TAC)) (fun th => tactic_of do pure (LABEL_TAC "maxp" (← MESON [th] (← q r"!G':A#B->bool p.
              G' subring_of prod_ring k l /\
              (!z. (ring_0 k,z) IN G' ==> z = ring_0 l) /\
              (!x. x IN r ==> (x,(f:A->B) x) IN G') /\
              G SUBSET G' /\ p IN G'
              ==> p IN G"))))))] THEN SUBGOAL_THEN q141 (CONJUNCTS_THEN2 (LABEL_TAC "gcar") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "gneg") (CONJUNCTS_THEN2 (LABEL_TAC "gadd") (LABEL_TAC "gmul")))))) THENL [UNDISCH_TAC q140 THEN REWRITE_TAC [subring_of, PROD_RING, SUBSET, FORALL_PAIR_THM, IN_CROSS] THEN CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN q139 (LABEL_TAC "func") THENL [REPEAT STRIP_TAC THEN SUBGOAL_THEN q138 STRIP_ASSUME_TAC THENL [USE_THEN "gcar" (fun th => tactic_of do pure (MP_TAC (← MATCH_MP th (← ASSUME (← q r"(x:A,z:B) IN G"))) THEN MP_TAC (← MATCH_MP th (← ASSUME (← q r"(x:A,z':B) IN G"))))) THEN SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN q137 MP_TAC THENL [SUBGOAL_THEN q136 SUBST1_TAC THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_ADD_RNEG THEN ASM_REWRITE_TAC [], ALL_TAC] THEN REWRITE_TAC [ring_sub] THEN USE_THEN "gadd" MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN USE_THEN "gneg" MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN USE_THEN "isg" (fun th => DISCH_THEN (MP_TAC o (MATCH_MP th))) THEN MP_TAC v135 THEN ASM_REWRITE_TAC [] THEN MESON_TAC [], ALL_TAC] THEN REMOVE_THEN "isg" (fun (_ : thm) => ALL_TAC) THEN ABBREV_TAC q131 THEN ABBREV_TAC q130 THEN SUBGOAL_THEN q129 (LABEL_TAC "gr") THENL [REPEAT GEN_TAC THEN MAP_EVERY EXPAND_TAC ["s", "g"] THEN REWRITE_TAC [IN_IMAGE, EXISTS_PAIR_THM, FST] THEN EQ_TAC THENL [DISCH_TAC THEN CONJ_TAC THENL [MAP_EVERY EXISTS_TAC [q128, q127] THEN ASM_REWRITE_TAC [], MATCH_MP_TAC SELECT_UNIQUE THEN REWRITE_TAC [] THEN X_GEN_TAC q126 THEN EQ_TAC THENL [DISCH_TAC THEN USE_THEN "func" MATCH_MP_TAC THEN EXISTS_TAC q125 THEN ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC []]], DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN q124 (X_CHOOSE_THEN q123 STRIP_ASSUME_TAC)) (SUBST1_TAC o SYM)) THEN CONV_TAC SELECT_CONV THEN EXISTS_TAC q122 THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN q121 STRIP_ASSUME_TAC THENL [SUBGOAL_THEN q120 (LABEL_TAC "gin") THENL [USE_THEN "gr" (fun th => SIMP_TAC [th]), ALL_TAC] THEN USE_THEN "gr" (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM th)])) THEN REPEAT CONJ_TAC THENL [GEN_TAC THEN DISCH_TAC THEN USE_THEN "gcar" MATCH_MP_TAC THEN USE_THEN "gin" MATCH_MP_TAC THEN ASM_REWRITE_TAC [], FIRST_ASSUM ACCEPT_TAC, FIRST_ASSUM ACCEPT_TAC, REPEAT STRIP_TAC THEN USE_THEN "gneg" MATCH_MP_TAC THEN USE_THEN "gin" MATCH_MP_TAC THEN ASM_REWRITE_TAC [], REPEAT STRIP_TAC THEN USE_THEN "gadd" MATCH_MP_TAC THEN CONJ_TAC THEN USE_THEN "gin" MATCH_MP_TAC THEN ASM_REWRITE_TAC [], REPEAT STRIP_TAC THEN USE_THEN "gmul" MATCH_MP_TAC THEN CONJ_TAC THEN USE_THEN "gin" MATCH_MP_TAC THEN ASM_REWRITE_TAC []], ALL_TAC] THEN MAP_EVERY (fun t => REMOVE_THEN t (fun (_ : thm) => ALL_TAC)) ["func", "gcar", "gneg", "gadd", "gmul"] THEN SUBGOAL_THEN q119 ASSUME_TAC THENL [REWRITE_TAC [subring_of, SUBSET] THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN q118 ASSUME_TAC THENL [ASM_SIMP_TAC [ring_homomorphism, CARRIER_SUBRING_GENERATED_SUBRING, v117, SUBSET, FORALL_IN_IMAGE], ALL_TAC] THEN SUBGOAL_THEN q116 ASSUME_TAC THENL [MP_TAC v115 THEN ASM_SIMP_TAC [RING_POW_SUBRING_GENERATED, CARRIER_SUBRING_GENERATED_SUBRING], ALL_TAC] THEN SUBGOAL_THEN q112 STRIP_ASSUME_TAC THENL [MP_TAC v111 THEN USE_THEN "gr" (fun th => REWRITE_TAC [th]) THEN REWRITE_TAC [SUBSET] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN q109 ASSUME_TAC THENL [SUBGOAL_THEN q108 SUBST1_TAC THENL [ASM_SIMP_TAC [ring_kernel, CARRIER_SUBRING_GENERATED_SUBRING], MATCH_MP_TAC RING_IDEAL_RING_KERNEL THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN q107 (LABEL_TAC "adj") THENL [X_GEN_TAC q106 THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN q105 STRIP_ASSUME_TAC)) THEN ABBREV_TAC q104 THEN SUBGOAL_THEN q103 ASSUME_TAC THENL [EXPAND_TAC "G'" THEN MATCH_MP_TAC SUBRING_OF_HOMOMORPHIC_IMAGE THEN EXISTS_TAC q102 THEN REWRITE_TAC [CARRIER_SUBRING_OF, RING_HOMOMORPHISM_PAIRED, ETA_AX] THEN CONJ_TAC THEN MATCH_MP_TAC RING_HOMOMORPHISM_POLY_EXTEND THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INCLUSION, IN_UNIV], ALL_TAC] THEN SUBGOAL_THEN q101 ASSUME_TAC THENL [REWRITE_TAC [SUBSET, FORALL_PAIR_THM] THEN MAP_EVERY X_GEN_TAC [q100, q99] THEN USE_THEN "gr" (fun th => REWRITE_TAC [th]) THEN STRIP_TAC THEN EXPAND_TAC "G'" THEN REWRITE_TAC [IN_IMAGE, PAIR_EQ] THEN EXISTS_TAC q98 THEN ASM_SIMP_TAC [POLY_CONST, POLY_EXTEND_CONST, RING_HOMOMORPHISM_INCLUSION, CARRIER_SUBRING_GENERATED_SUBRING], ALL_TAC] THEN SUBGOAL_THEN q97 ASSUME_TAC THENL [X_GEN_TAC q96 THEN EXPAND_TAC "G'" THEN REWRITE_TAC [IN_IMAGE, PAIR_EQ] THEN DISCH_THEN (X_CHOOSE_THEN q95 (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) SUBST1_TAC) ASSUME_TAC)) THEN MP_TAC v94 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [] THEN FIRST_X_ASSUM (MATCH_MP_TAC o (checkM (fun th => (do if ← (do let z80 ← (do let z81 ← (pure th); pure (concl z81)); pure (is_forall z80)) then (do let z82 ← (do let z83 ← (pure th); pure (concl z83)); canM (fun z84 => (do let z85 ← (pure z84); find_termM (fun z86 => (do let z88 ← (pure z86); let z87 ← (q r"w:B"); pure (z87 == z88))) z85)) z82) else pure false)))) THEN REWRITE_TAC [] THEN CONJ_TAC THENL [GEN_TAC THEN MP_TAC v79 THEN ASM_SIMP_TAC [RING_POLYNOMIAL, CARRIER_SUBRING_GENERATED_SUBRING], MP_TAC v75 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_HOMOMORPHISM_INCLUSION], ALL_TAC] THEN DISCH_THEN (SUBST1_TAC o (SYM o BETA_RULE)) THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN q69 MP_TAC THENL [USE_THEN "maxp" MATCH_MP_TAC THEN EXISTS_TAC q68 THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [MP_TAC v67 THEN UNDISCH_TAC q65 THEN REWRITE_TAC [SUBSET] THEN MESON_TAC [], EXPAND_TAC "G'" THEN REWRITE_TAC [IN_IMAGE, PAIR_EQ] THEN EXISTS_TAC q64 THEN ASM_SIMP_TAC [POLY_VAR, POLY_EXTEND_VAR, RING_HOMOMORPHISM_INCLUSION, IN_UNIV]], USE_THEN "gr" (fun th => REWRITE_TAC [th]) THEN SIMP_TAC []], ALL_TAC] THEN SUBGOAL_THEN q63 (LABEL_TAC "loc") THENL [X_GEN_TAC q62 THEN STRIP_TAC THEN REMOVE_THEN "adj" MATCH_MP_TAC THEN SUBGOAL_THEN q61 STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [ASM_SIMP_TAC [], DISCH_TAC THEN UNDISCH_TAC q60 THEN ASM_REWRITE_TAC []], ALL_TAC] THEN CONJ_TAC THENL [ASM_SIMP_TAC [RING_INV], ALL_TAC] THEN EXISTS_TAC q59 THEN CONJ_TAC THENL [ASM_SIMP_TAC [RING_INV], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [q58, q57] THEN STRIP_TAC THEN SUBGOAL_THEN q56 ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN q55 ASSUME_TAC THENL [MP_TAC v54 THEN ASM_SIMP_TAC [RING_MUL_RZERO, RING_POW] THEN DISCH_THEN (ACCEPT_TAC o SYM), ALL_TAC] THEN SUBGOAL_THEN q49 ASSUME_TAC THENL [MP_TAC v48 THEN ASM_SIMP_TAC [IN_SUBRING_POW] THEN DISCH_THEN (ACCEPT_TAC o SYM), ALL_TAC] THEN MP_TAC v41 THEN ASM_SIMP_TAC [] THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_MUL_EQ_0, FIELD_IMP_INTEGRAL_DOMAIN, RING_POW, RING_SUM, FIELD_POW_EQ_0], ALL_TAC] THEN SUBGOAL_THEN q36 ASSUME_TAC THENL [ASM_REWRITE_TAC [valuation_subring] THEN X_GEN_TAC q35 THEN STRIP_TAC THEN MP_TAC v34 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [IN_ELIM_THM] THEN CONJ_TAC THENL [USE_THEN "loc" (fun th => MESON_TAC [th]), MATCH_MP_TAC FIELD_NONTRIVIAL THEN ASM_REWRITE_TAC []], ALL_TAC] THEN DISCH_THEN (DISJ_CASES_THEN ASSUME_TAC) THENL [DISJ1_TAC, DISJ2_TAC] THEN REMOVE_THEN "adj" MATCH_MP_TAC THEN (CONJ_TAC THENL [ASM_SIMP_TAC [RING_INV], MATCH_MP_TAC RING_HOMOMORPHISM_ADJOIN_ROOT THEN ASM_SIMP_TAC [RING_INV]]), ALL_TAC] THEN REMOVE_THEN "adj" (fun (_ : thm) => ALL_TAC) THEN REMOVE_THEN "maxp" (fun (_ : thm) => ALL_TAC) THEN MAP_EVERY EXISTS_TAC [q29, q28, q27] THEN ASM_SIMP_TAC [VALUATION_SUBRING_MAXIMAL_IDEAL] THEN X_GEN_TAC q26 THEN DISCH_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_REWRITE_TAC [] THEN EQ_TAC THENL [DISCH_TAC THEN ASM_CASES_TAC q25 THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN q24 ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC v23 THEN SUBGOAL_THEN q21 SUBST1_TAC THENL [ASM_SIMP_TAC [FIELD_MUL_RINV], ALL_TAC] THEN ASM_SIMP_TAC [RING_MUL_LZERO] THEN MP_TAC v20 THEN MESON_TAC [], STRIP_TAC THENL [ASM_REWRITE_TAC [], REMOVE_THEN "loc" (MP_TAC o (SPEC q17)) THEN ASM_REWRITE_TAC []]])

  let INTEGRAL_CLOSURE_EQ_INTERS_VALUATION_SUBRINGS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r6 ← TAUT (← q r"(~p ==> F) ==> p")
    prove
      r"!k a:A->bool.
          field k /\ a subring_of k
          ==> {x | integral_element (subring_generated k a,k) I x} =
              INTERS {b | valuation_subring k b /\ a SUBSET b}"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_homomorphism(subring_generated k a,k) (I:A->A)") ASSUME_TAC THENL [REWRITE_TAC [I_DEF, RING_HOMOMORPHISM_INCLUSION], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_carrier(subring_generated k a) = (a:A->bool) /\
      a SUBSET ring_carrier k /\ ring_0 k IN a") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING] THEN UNDISCH_TAC (← q r"(a:A->bool) subring_of k") THEN SIMP_TAC [subring_of], ALL_TAC] THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_INTERS, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:A") THEN EQ_TAC THENL [DISCH_TAC THEN X_GEN_TAC (← q r"b:A->bool") THEN STRIP_TAC THEN MATCH_MP_TAC VALUATION_SUBRING_INTEGRAL_ELEMENT THEN EXISTS_TAC (← q r"k:A ring") THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC INTEGRAL_ELEMENT_OVER_SUBRING THEN MAP_EVERY EXISTS_TAC [(← q r"subring_generated k (a:A->bool)"), (← q r"I:A->A")] THEN ASM_REWRITE_TAC [IMAGE_I] THEN FIRST_X_ASSUM (STRIP_ASSUME_TAC o ((GEN_REWRITE_RULE id [valuation_subring]) o (checkM (fun th => (tryCatch (do let z11 ← (pure "valuation_subring"); let z10 ← (do pure (Prod.fst (← (do let z7 ← (do pure (Prod.fst (← (do let z8 ← (do let z9 ← (pure th); pure (concl z9)); pure (strip_comb z8))))); liftExcept (dest_const z7))))); pure (z10 == z11)) (fun _ => (pure false))))))) THEN ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING], DISCH_TAC] THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier k") ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [valuation_subring, CARRIER_SUBRING_OF] THEN REWRITE_TAC [SUBSET_REFL] THEN MESON_TAC [], ALL_TAC] THEN ASM_CASES_TAC (← q r"x:A = ring_0 k") THENL [MP_TAC (← ISPECL [(← q r"subring_generated k (a:A->bool)"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"ring_0 k:A")] INTEGRAL_ELEMENT_IMAGE) THEN ASM_REWRITE_TAC [I_THM], ALL_TAC] THEN MATCH_MP_TAC r6 THEN DISCH_TAC THEN ABBREV_TAC (← q r"y = ring_inv k (x:A)") THEN SUBGOAL_THEN (← q r"(y:A) IN ring_carrier k /\ ~(y = ring_0 k) /\
                  ring_inv k y = x") STRIP_ASSUME_TAC THENL [EXPAND_TAC "y" THEN ASM_SIMP_TAC [RING_INV, FIELD_INV_EQ_0, RING_INV_INV, FIELD_UNIT], ALL_TAC] THEN ABBREV_TAC (← q r"a' = ring_carrier(subring_generated k ((y:A) INSERT a))") THEN SUBGOAL_THEN (← q r"a' subring_of (k:A ring) /\ subring_generated k a' =
      subring_generated k ((y:A) INSERT a) /\ a SUBSET a' /\ (y:A) IN a' /\
      ~(x IN a')") STRIP_ASSUME_TAC THENL [EXPAND_TAC "a'" THEN REWRITE_TAC [SUBRING_SUBRING_GENERATED, SUBRING_GENERATED_BY_SUBRING_GENERATED] THEN REPEAT CONJ_TAC THENL [REWRITE_TAC [SUBSET] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN ASM_REWRITE_TAC [IN_INSERT] THEN ASM SET_TAC [], MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN ASM_REWRITE_TAC [IN_INSERT], DISCH_TAC THEN UNDISCH_TAC (← q r"~integral_element (subring_generated k a,k) I (x:A)") THEN REWRITE_TAC [] THEN MATCH_MP_TAC INTEGRAL_ELEMENT_IN_ADJOIN_INV THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "a'" THEN FIRST_ASSUM ACCEPT_TAC], ALL_TAC] THEN SUBGOAL_THEN (← q r"~ring_unit (subring_generated k a') (y:A)") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_UNIT_SUBRING_OF_FIELD], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"subring_generated k (a':A->bool)"), (← q r"ideal_generated (subring_generated k a') {y:A}")] MAXIMAL_SUPERIDEAL_EXISTS) THEN ANTS_TAC THENL [ASM_SIMP_TAC [PROPER_IDEAL_IDEAL_GENERATED_SING, CARRIER_SUBRING_GENERATED_SUBRING], DISCH_THEN (X_CHOOSE_THEN (← q r"m':A->bool") STRIP_ASSUME_TAC)] THEN SUBGOAL_THEN (← q r"(y:A) IN m'") ASSUME_TAC THENL [UNDISCH_TAC (← q r"ideal_generated (subring_generated k a') {y:A} SUBSET m'") THEN REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING, IN_SING, SING_SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a':A->bool"), (← q r"m':A->bool")] VALUATION_SUBRING_DOMINATES) THEN ANTS_TAC THENL [ASM_SIMP_TAC [MAXIMAL_IMP_PRIME_IDEAL], DISCH_THEN (X_CHOOSE_THEN (← q r"b:A->bool") (X_CHOOSE_THEN (← q r"m:A->bool") STRIP_ASSUME_TAC))] THEN SUBGOAL_THEN (← q r"(x:A) IN b /\ (y:A) IN m") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC (← q r"a':A->bool") THEN ASM_REWRITE_TAC [], UNDISCH_TAC (← q r"a' INTER m = (m':A->bool)") THEN UNDISCH_TAC (← q r"(y:A) IN m'") THEN SET_TAC []], ALL_TAC] THEN FIRST_ASSUM (STRIP_ASSUME_TAC o ((GEN_REWRITE_RULE id [valuation_subring]) o (checkM (fun th => (tryCatch (do let z5 ← (pure "valuation_subring"); let z4 ← (do pure (Prod.fst (← (do let z1 ← (do pure (Prod.fst (← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); pure (strip_comb z2))))); liftExcept (dest_const z1))))); pure (z4 == z5)) (fun _ => (pure false))))))) THEN MP_TAC (← ISPECL [(← q r"subring_generated k (b:A->bool)"), (← q r"m:A->bool"), (← q r"ring_1(subring_generated k b):A")] RING_UNIT_NOT_IN_PRIME_IDEAL) THEN ASM_SIMP_TAC [MAXIMAL_IMP_PRIME_IDEAL, RING_UNIT_1] THEN REWRITE_TAC [(← CONJUNCT2 SUBRING_GENERATED)] THEN SUBGOAL_THEN (← q r"ring_1 k = ring_mul k (x:A) y") SUBST1_TAC THENL [EXPAND_TAC "y" THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FIELD_MUL_RINV THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"subring_generated k (b:A->bool)"), (← q r"m:A->bool"), (← q r"x:A"), (← q r"y:A")] IN_RING_IDEAL_LMUL) THEN ASM_SIMP_TAC [MAXIMAL_IMP_RING_IDEAL, CARRIER_SUBRING_GENERATED_SUBRING, (← CONJUNCT2 SUBRING_GENERATED)])

  let VALUATION_RING_IMP_BEZOUT_RING ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"{a:A,b} = {b,a}")
    prove
      r"!r:A ring. valuation_ring r ==> bezout_ring r"
      (SUBGOAL_THEN (← q r"!r a b:A. b IN ring_carrier r /\ ring_divides r a b
                ==> ideal_generated r {a,b} = ideal_generated r {a}") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, INSERT_SUBSET, EMPTY_SUBSET] THEN CONJ_TAC THENL [ASM_MESON_TAC [ring_divides, IN_IDEAL_GENERATED_SELF], ASM_SIMP_TAC [IN_IDEAL_GENERATED_SING]], MATCH_MP_TAC IDEAL_GENERATED_MONO THEN SET_TAC []], ALL_TAC] THEN REWRITE_TAC [valuation_ring, BEZOUT_RING_2, principal_ideal] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPECL [(← q r"a:A"), (← q r"b:A")])) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THENL [EXISTS_TAC (← q r"a:A") THEN ASM_SIMP_TAC [], EXISTS_TAC (← q r"b:A") THEN ONCE_REWRITE_TAC [r1] THEN ASM_SIMP_TAC []])

  let DVR_IMP_VALUATION_RING ← prove
    r"!r:A ring. DVR r ==> valuation_ring r"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [valuation_ring] THEN CONJ_TAC THENL [ASM_MESON_TAC [DVR, PID_IMP_INTEGRAL_DOMAIN], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_generated r {a:A}"), (← q r"ideal_generated r {b:A}")] DVR_IDEALS_TOTALLY_ORDERED) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN DISCH_THEN DISJ_CASES_TAC THENL [DISJ2_TAC, DISJ1_TAC] THEN ASM_SIMP_TAC [(← GSYM IN_IDEAL_GENERATED_SING_EQ)] THEN FIRST_X_ASSUM (MATCH_MP_TAC o (REWRITE_RULE [SUBSET])) THEN ASM_REWRITE_TAC [IN_IDEAL_GENERATED_SELF])

  let DVR_EQ_NOETHERIAN_VALUATION_RING ← prove
    r"!r:A ring. DVR r <=> valuation_ring r /\ noetherian_ring r /\ ~(field r)"
    (GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL [ASM_SIMP_TAC [DVR_IMP_VALUATION_RING] THEN ASM_MESON_TAC [DVR, PID_IMP_NOETHERIAN_RING], ASM_SIMP_TAC [DVR, VALUATION_RING_IMP_LOCAL, PID_EQ_NOETHERIAN_BEZOUT_DOMAIN, VALUATION_RING_IMP_BEZOUT_RING, VALUATION_RING_IMP_INTEGRAL_DOMAIN]])

  let DVR_EQ_INTEGRALLY_CLOSED ← prove
    r"!r:A ring.
        integral_domain r /\ noetherian_ring r /\ local_ring r /\
        ~(field r) /\
        (!p. prime_ideal r p /\ ~(p = {ring_0 r}) ==> maximal_ideal r p)
        ==> (DVR r <=> integrally_closed r) /\ (DVR r <=> valuation_ring r)"
    (REPEAT STRIP_TAC THENL [ASM_SIMP_TAC [DVR_IFF_LOCAL_DEDEKIND, dedekind_domain], ASM_SIMP_TAC [DVR_EQ_NOETHERIAN_VALUATION_RING]])

  let DVR_DIVIDES_UNIFORMIZER_POW ← prove
    r"!r (q:A) a.
        DVR r /\ maximal_ideal r (ideal_generated r {q}) /\
        q IN ring_carrier r /\ a IN ring_carrier r /\ ~(a = ring_0 r)
        ==> ?s d. d IN ring_carrier r /\ ring_mul r a d = ring_pow r q s"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_generated r {q:A}"), (← q r"ideal_generated r {a:A}")] DVR_IDEAL_MAXIMAL_POW) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"n:num")) THEN MAP_EVERY EXISTS_TAC [(← q r"n:num")] THEN SUBGOAL_THEN (← q r"ring_pow r (q:A) n IN ideal_generated r {a}") MP_TAC THENL [ASM_SIMP_TAC [IDEAL_POW_PRINCIPAL, IN_IDEAL_GENERATED_SELF, RING_POW], ALL_TAC] THEN ASM_SIMP_TAC [IN_IDEAL_GENERATED_SING_EQ, ring_divides] THEN MESON_TAC [])

  let VALUATION_SUBRING_DEDEKIND_VALUATION ← prove
    r"!r k (h:A->B) P.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r})
        ==> valuation_subring k
             {x | x IN ring_carrier k /\
                  (x = ring_0 k \/ &0 <= dedekind_valuation (r,k) h P x)}"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN REWRITE_TAC [valuation_subring] THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool")] DEDEKIND_VALUATION_RING_LOCALIZATION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"g:(A#A->bool)->B") STRIP_ASSUME_TAC) THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"ring_localization r (ring_carrier r DIFF P:A->bool)"), (← q r"k:B ring"), (← q r"g:(A#A->bool)->B")] SUBRING_RING_IMAGE) THEN ASM_SIMP_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM, ring_image], ALL_TAC] THEN X_GEN_TAC (← q r"x:B") THEN STRIP_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_SIMP_TAC [RING_INV, FIELD_INV_EQ_0, DEDEKIND_VALUATION_INV] THEN INT_ARITH_TAC)

  -- @@RETURN BEGIN
  return { VALUATION_SUBRING_EXTEND_HOMOMORPHISM,
           INTEGRAL_CLOSURE_EQ_INTERS_VALUATION_SUBRINGS, VALUATION_RING_IMP_BEZOUT_RING,
           DVR_IMP_VALUATION_RING, DVR_EQ_NOETHERIAN_VALUATION_RING,
           DVR_EQ_INTEGRALLY_CLOSED, DVR_DIVIDES_UNIFORMIZER_POW,
           VALUATION_SUBRING_DEDEKIND_VALUATION }
  -- @@RETURN END

end HolANT.ValuationRing
