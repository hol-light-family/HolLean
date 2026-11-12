/- ========================================================================= -/
/- ANT: Discrete valuations of the fraction field k of a Dedekind ...      -/
/- ========================================================================= -/
/- File: HolANT/DedekindValuation.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/dedekind_valuation.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antdedekindvaluationdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/permutations.ml, Library/ring_det.ml, ANT/ideal_arith.ml, Library/products.ml, ANT/algmisc.ml, Library/matroids.ml, Library/fieldtheory.ml, ANT/integral.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/dedekind_local.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.DedekindValuation fills them).

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
import HolLibrary.Permutations
import HolLibrary.RingDet
import HolANT.IdealArith
import HolLibrary.Products
import HolANT.Algmisc
import HolLibrary.Matroids
import HolLibrary.FieldTheory
import HolANT.Integral
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.DedekindLocal

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
open HolANT.DedekindLocal

namespace HolANT.DedekindValuation

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (AND_FORALL_THM CONJ_ASSOC DEDEKIND_IDEAL_EQ_VALUATION
   DEDEKIND_IDEAL_FACTORIZATION DEDEKIND_IDEAL_SUBSET_VALUATION
   DEDEKIND_IMP_INTEGRAL_DOMAIN DEDEKIND_IN_IDEAL_POW_VALUATION
   DEDEKIND_LOCALIZATION DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL
   DEDEKIND_WEAK_APPROXIMATION DE_MORGAN_THM DVR DVR_IFF_LOCAL_DEDEKIND
   DVR_LOCALIZATION EQ_TRANS EXISTS_UNIQUE_DEF EXTENSION FIELD_EQ_TRIVIAL_IDEALS
   FIELD_IMP_INTEGRAL_DOMAIN FIELD_INV_EQ_0 FIELD_MUL_EQ_0 FIELD_MUL_LINV
   FIELD_MUL_RINV FIELD_NONTRIVIAL FIELD_POW_EQ_0 FIELD_UNIT FINITE_NUMSEG_LT
   FINITE_SUBSET FINITE_UNION FORALL_IN_GSPEC FORALL_IN_IMAGE
   FRACTION_FIELD_COMMON_DENOMINATOR FRACTION_FIELD_MAP IDEALS_GENERATED_SING_EQ
   IDEAL_GENERATED_EQ_0 IDEAL_GENERATED_MINIMAL IDEAL_GENERATED_MINIMAL_EQ
   IDEAL_GENERATED_RING_LOCALIZATION IDEAL_GENERATED_SING_EQ_CARRIER
   IDEAL_LOCALIZATION_EQ_ZERO IDEAL_POW_1 IDEAL_POW_EQ_ZERO IDEAL_POW_PRINCIPAL
   IDEAL_PRODUCT_EQ_ZERO IDEAL_PROD_EQ_ZERO IDEAL_VALUATION_CARRIER
   IDEAL_VALUATION_EQ_0 IDEAL_VALUATION_FINITE_SUPPORT IDEAL_VALUATION_IDEAL_POW
   IDEAL_VALUATION_IDEAL_PROD IDEAL_VALUATION_IDEAL_PRODUCT_MONOMIAL
   IDEAL_VALUATION_LOCALIZATION IDEAL_VALUATION_PRIME
   IDEAL_VALUATION_PRINCIPAL_ADD IDEAL_VALUATION_PRINCIPAL_MUL
   IDEAL_VALUATION_SETADD IMAGE_CLAUSES IMP_CONJ IMP_CONJ_ALT IMP_IMP
   INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING INTEGRAL_DOMAIN_MUL_EQ_0
   INTEGRAL_DOMAIN_MUL_LCANCEL INTEGRAL_DOMAIN_POW_EQ_0 INTEGRAL_DOMAIN_REGULAR
   INTER INT_ADD_LID INT_ADD_RINV INT_LE_REFL INT_LT_REFL INT_MUL_LZERO
   INT_OF_NUM_ADD INT_OF_NUM_EQ INT_OF_NUM_LE INT_OF_NUM_LT INT_OF_NUM_MIN
   INT_OF_NUM_OF_INT INT_OF_NUM_SUC INT_POS INT_SUB_LE INT_SUB_REFL
   INT_SUB_RZERO IN_DIFF IN_ELIM_THM IN_IDEAL_GENERATED_SING_EQ IN_IMAGE
   IN_RING_IDEAL_0 IN_SING IN_UNION ISOMORPHIC_RING_FIELDNESS
   ISOMORPHIC_RING_LOCALITY ISOMORPHIC_RING_PIDNESS LEFT_IMP_EXISTS_THM
   LOCALEQUIV_MUL_RCANCEL LT_NZ : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (MAXIMAL_IDEAL_0 MAXIMAL_IMP_PRIME_IDEAL MIN MONOMIAL_RESTRICT_EQ MONO_EXISTS
   NOT_EXISTS_THM NOT_FORALL_THM NOT_IMP PRIME_IDEAL_IMP_SUBSET
   PRIME_IDEAL_LOCALIZATION PRIME_IMP_PROPER_IDEAL PRIME_IMP_RING_IDEAL
   PROPER_IDEAL PROPER_IDEAL_ALT RIGHT_FORALL_IMP_THM RIGHT_IMP_EXISTS_THM
   RING_0 RING_1 RING_ADD RING_ADD_LZERO RING_ADD_RZERO RING_ASSOCIATES_NEG
   RING_ASSOCIATES_REFL RING_CARRIER_NONEMPTY RING_FRACTIONATE_EQ_0_GEN
   RING_FRACTIONATE_IN_CARRIER RING_HOMOMORPHISM_0 RING_HOMOMORPHISM_1
   RING_HOMOMORPHISM_ADD RING_HOMOMORPHISM_INV RING_HOMOMORPHISM_IN_CARRIER
   RING_HOMOMORPHISM_MUL RING_HOMOMORPHISM_NEG RING_HOMOMORPHISM_SUM_MUL
   RING_IDEAL_CARRIER RING_IDEAL_IDEAL_GENERATED RING_IDEAL_IDEAL_POW
   RING_IDEAL_IDEAL_PROD RING_IDEAL_IDEAL_PRODUCT RING_IDEAL_IMP_SUBSET
   RING_IDEAL_SETADD RING_INV RING_ISOMORPHISM_ONTO_IMAGE
   RING_LOCALEQUIV_EQ_0_GEN RING_LOCALEQUIV_IN_CARRIER RING_LOCALIZATION_CARRIER
   RING_LOCALIZATION_UNIVERSAL RING_MONOMORPHISM_ALT RING_MONOMORPHISM_COMPOSE
   RING_MONOMORPHISM_EQ_0 RING_MONOMORPHISM_IMP_HOMOMORPHISM
   RING_MONOMORPHISM_INJECTIVE_EQ RING_MUL RING_MULTSYS_IMP_SUBSET
   RING_MULTSYS_NONPRIME RING_MUL_ASSOC RING_MUL_LID RING_MUL_LZERO RING_MUL_RID
   RING_MUL_RZERO RING_NEG RING_NEG_EQ_0 RING_NEG_NEG RING_POW RING_SUM
   RING_SUM_EQ RING_SUM_LMUL RING_UNIT_0 RING_UNIT_1 RING_UNIT_IN_CARRIER
   SELECT_UNIQUE SING_SUBSET SKOLEM_THM SUBSET SUBSET_ANTISYM
   SUBSET_IDEALS_GENERATED_SING SUBSET_REFL TRIVIAL_RING_SUBSET
   field_of_fractions free_basis integral_domain isomorphic_ring local_ring
   monomial monomial_restrict monomial_vars o_THM prime_ideal proper_ideal
   ring_div ring_divides ring_image ring_pow ring_setadd ring_unit : thm)
  deriving Inhabited

/-- What dedekind_valuation.ml uses from Session besides theorems. -/
structure DedekindValuationDeps where
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
/- dedekind_valuation.ml phrases from line 68 to 794                      -/
/- ---------------------------------------------------------------------- -/

structure DedekindValuation01 where
  -- @@FIELDS
  dedekind_valuation : thm
  DEDEKIND_VALUATION : thm
  DEDEKIND_VALUATION_IMAGE : thm
  DEDEKIND_VALUATION_1 : thm
  FIELD_FRACTION_NONZERO : thm
  DEDEKIND_VALUATION_MUL : thm
  DEDEKIND_VALUATION_INV : thm
  DEDEKIND_VALUATION_DIV : thm
  DEDEKIND_VALUATION_POW : thm
  DEDEKIND_VALUATION_NEG : thm
  DEDEKIND_VALUATION_COMPATIBLE : thm
  DEDEKIND_VALUATION_ADD : thm
  DEDEKIND_VALUATION_ADD_STRICT : thm
  DEDEKIND_VALUATION_FINITE : thm
  DEDEKIND_VALUATION_INTEGRAL : thm
  DEDEKIND_VALUATION_UNIT : thm
  DEDEKIND_VALUATION_PRIME_IDEAL : thm
  DEDEKIND_VALUATION_EQ : thm
  DEDEKIND_IDEAL_PRESCRIBED_VALUATIONS : thm
  ideal_of_valuations : thm
  IDEAL_OF_VALUATIONS : thm
  IDEAL_OF_VALUATIONS_UNIQUE : thm
  IDEAL_OF_VALUATIONS_ADD : thm
  IDEAL_OF_VALUATIONS_0 : thm
  IDEAL_OF_VALUATIONS_EQ : thm
  DEDEKIND_VALUATION_WEAK_APPROXIMATION : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDedekindValuation01 [HolBase] (D : DedekindValuationDeps) :
    ExceptT String IO DedekindValuation01 := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_INT_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, INT_ARITH,
        INT_ARITH_TAC, RING_TAC, SELECT_CONV, SET_RULE, TAUT, new_definition, .. } := D
  let { AND_FORALL_THM, CONJ_ASSOC, DEDEKIND_IDEAL_EQ_VALUATION,
        DEDEKIND_IDEAL_FACTORIZATION, DEDEKIND_IDEAL_SUBSET_VALUATION,
        DEDEKIND_IMP_INTEGRAL_DOMAIN, DEDEKIND_WEAK_APPROXIMATION,
        FIELD_EQ_TRIVIAL_IDEALS, FIELD_IMP_INTEGRAL_DOMAIN, FIELD_INV_EQ_0,
        FIELD_MUL_LINV, FIELD_MUL_RINV, FIELD_NONTRIVIAL, FIELD_POW_EQ_0,
        FINITE_SUBSET, IDEALS_GENERATED_SING_EQ, IDEAL_GENERATED_EQ_0,
        IDEAL_GENERATED_MINIMAL_EQ, IDEAL_GENERATED_SING_EQ_CARRIER, IDEAL_POW_EQ_ZERO,
        IDEAL_PRODUCT_EQ_ZERO, IDEAL_PROD_EQ_ZERO, IDEAL_VALUATION_CARRIER,
        IDEAL_VALUATION_EQ_0, IDEAL_VALUATION_FINITE_SUPPORT,
        IDEAL_VALUATION_IDEAL_PROD, IDEAL_VALUATION_IDEAL_PRODUCT_MONOMIAL,
        IDEAL_VALUATION_PRINCIPAL_ADD, IDEAL_VALUATION_PRINCIPAL_MUL, IMP_CONJ,
        IMP_CONJ_ALT, INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING, INTEGRAL_DOMAIN_MUL_EQ_0,
        INTEGRAL_DOMAIN_MUL_LCANCEL, INTER, INT_ADD_LID, INT_ADD_RINV, INT_LT_REFL,
        INT_MUL_LZERO, INT_OF_NUM_ADD, INT_OF_NUM_EQ, INT_OF_NUM_LE, INT_OF_NUM_LT,
        INT_OF_NUM_MIN, INT_OF_NUM_OF_INT, INT_OF_NUM_SUC, INT_POS, INT_SUB_LE,
        INT_SUB_REFL, INT_SUB_RZERO, IN_ELIM_THM, IN_IMAGE, LEFT_IMP_EXISTS_THM, LT_NZ, .. } := D.core1
  let { MONOMIAL_RESTRICT_EQ, MONO_EXISTS, NOT_EXISTS_THM, PRIME_IMP_PROPER_IDEAL,
        PRIME_IMP_RING_IDEAL, PROPER_IDEAL_ALT, RIGHT_FORALL_IMP_THM, RING_1, RING_ADD,
        RING_ADD_LZERO, RING_ADD_RZERO, RING_ASSOCIATES_NEG, RING_ASSOCIATES_REFL,
        RING_CARRIER_NONEMPTY, RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_1,
        RING_HOMOMORPHISM_ADD, RING_HOMOMORPHISM_INV, RING_HOMOMORPHISM_IN_CARRIER,
        RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_NEG, RING_IDEAL_CARRIER,
        RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_POW, RING_IDEAL_IDEAL_PROD,
        RING_IDEAL_IDEAL_PRODUCT, RING_INV, RING_MONOMORPHISM_EQ_0,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MONOMORPHISM_INJECTIVE_EQ, RING_MUL,
        RING_MUL_ASSOC, RING_MUL_LID, RING_MUL_RID, RING_NEG, RING_NEG_EQ_0,
        RING_NEG_NEG, RING_POW, RING_UNIT_0, RING_UNIT_1, RING_UNIT_IN_CARRIER,
        SELECT_UNIQUE, SING_SUBSET, SUBSET, SUBSET_IDEALS_GENERATED_SING, SUBSET_REFL,
        TRIVIAL_RING_SUBSET, field_of_fractions, integral_domain, monomial,
        monomial_restrict, monomial_vars, prime_ideal, proper_ideal, ring_div,
        ring_divides, ring_pow, ring_unit, .. } := D.core2
  -- @@SCOPE END

  let dedekind_valuation ← new_definition
    r"dedekind_valuation (r:A ring,k:B ring) (h:A->B) (P:A->bool) (x:B) =
  @v:int. !a b. a IN ring_carrier r /\ b IN ring_carrier r /\
                ~(a = ring_0 r) /\ ~(b = ring_0 r) /\ ring_mul k (h b) x = h a
                ==> v = &(ideal_valuation r P (ideal_generated r {a})) -
                        &(ideal_valuation r P (ideal_generated r {b}))"

  let DEDEKIND_VALUATION ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← INT_ARITH (← q r"(a:int) - b = c - d <=> a + d = c + b")
    prove
      r"!r k (h:A->B) P x a b.
          dedekind_domain r /\ ring_monomorphism(r,k) h /\
          prime_ideal r P /\ ~(P = {ring_0 r}) /\ x IN ring_carrier k /\
          a IN ring_carrier r /\ b IN ring_carrier r /\
          ~(a = ring_0 r) /\ ~(b = ring_0 r) /\ ring_mul k (h b) x = h a
          ==> dedekind_valuation (r,k) h P x =
              &(ideal_valuation r P (ideal_generated r {a})) -
              &(ideal_valuation r P (ideal_generated r {b}))"
      (REPEAT STRIP_TAC THEN REWRITE_TAC [dedekind_valuation] THEN MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC (← q r"v:int") THEN BETA_TAC THEN EQ_TAC THENL [DISCH_THEN (MP_TAC o (SPECL [(← q r"a:A"), (← q r"b:A")])) THEN ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"c:A"), (← q r"d:A")] THEN STRIP_TAC THEN REWRITE_TAC [r1] THEN REWRITE_TAC [INT_OF_NUM_ADD, INT_OF_NUM_EQ] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN SUBGOAL_THEN (← q r"ring_mul r (a:A) d = ring_mul r c b") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"ring_mul r (a:A) d"), (← q r"ring_mul r (c:A) b")] RING_MONOMORPHISM_INJECTIVE_EQ) THEN ASM_SIMP_TAC [RING_MUL] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL th)])) THEN SUBGOAL_THEN (← q r"(h:A->B) a IN ring_carrier k /\ h b IN ring_carrier k /\
        h c IN ring_carrier k /\ h d IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], RING_TAC], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"a:A"), (← q r"d:A")] IDEAL_VALUATION_PRINCIPAL_MUL) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"c:A"), (← q r"b:A")] IDEAL_VALUATION_PRINCIPAL_MUL) THEN ASM_REWRITE_TAC [] THEN ARITH_TAC)

  let DEDEKIND_VALUATION_IMAGE ← prove
    r"!r k (h:A->B) P a.
        dedekind_domain r /\ ring_monomorphism(r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\
        a IN ring_carrier r /\ ~(a = ring_0 r)
        ==> dedekind_valuation (r,k) h P (h a) =
            &(ideal_valuation r P (ideal_generated r {a}))"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN SUBGOAL_THEN (← q r"(h:A->B) a IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"(h:A->B) a"), (← q r"a:A"), (← q r"ring_1 r:A")] DEDEKIND_VALUATION) THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_1 th)])) THEN ASM_SIMP_TAC [RING_1, RING_MUL_LID] THEN ANTS_TAC THENL [ASM_MESON_TAC [DEDEKIND_IMP_INTEGRAL_DOMAIN, integral_domain], DISCH_THEN SUBST1_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ring_1 r:A")] IDEAL_GENERATED_SING_EQ_CARRIER) THEN REWRITE_TAC [RING_1, RING_UNIT_1] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool")] IDEAL_VALUATION_CARRIER) THEN ANTS_TAC THENL [ASM_MESON_TAC [PRIME_IMP_PROPER_IDEAL, PROPER_IDEAL_ALT], DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [INT_SUB_RZERO]])

  let DEDEKIND_VALUATION_1 ← prove
    r"!r k (h:A->B) P.
        field k /\ ring_monomorphism(r,k) h
        ==> dedekind_valuation (r,k) h P (ring_1 k) = &0"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN REWRITE_TAC [dedekind_valuation] THEN MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC (← q r"v:int") THEN BETA_TAC THEN EQ_TAC THENL [DISCH_THEN (MP_TAC o (SPECL [(← q r"ring_1 r:A"), (← q r"ring_1 r:A")])) THEN REWRITE_TAC [INT_SUB_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_1 th)])) THEN ASM_SIMP_TAC [RING_1, RING_MUL_LID] THEN ASM_MESON_TAC [FIELD_NONTRIVIAL, RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_1], DISCH_THEN SUBST1_TAC THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(h:A->B) b IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN UNDISCH_TAC (← q r"ring_mul k ((h:A->B) b) (ring_1 k) = h a") THEN ASM_SIMP_TAC [RING_MUL_RID] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"b:A"), (← q r"a:A")] RING_MONOMORPHISM_INJECTIVE_EQ) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [INT_SUB_REFL]])

  let FIELD_FRACTION_NONZERO ← prove
    r"!r k (h:A->B) x.
        field_of_fractions (r,k) h /\
        x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> ?a b. a IN ring_carrier r /\ b IN ring_carrier r /\
                  ~(a = ring_0 r) /\ ~(b = ring_0 r) /\
                  ring_mul k (h b) x = h a"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"x:B"))) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"a:A") THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"b:A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"ring_mul k ((h:A->B) b) x = h (ring_0 r)") THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_0 th)])) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"b:A")] RING_MONOMORPHISM_EQ_0) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"b:A")] RING_HOMOMORPHISM_IN_CARRIER) THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_MUL_EQ_0, FIELD_IMP_INTEGRAL_DOMAIN])

  let DEDEKIND_VALUATION_MUL ← prove
    r"!r k (h:A->B) P x y.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\
        x IN ring_carrier k /\ ~(x = ring_0 k) /\
        y IN ring_carrier k /\ ~(y = ring_0 k)
        ==> dedekind_valuation (r,k) h P (ring_mul k x y) =
            dedekind_valuation (r,k) h P x + dedekind_valuation (r,k) h P y"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"y:B")] FIELD_FRACTION_NONZERO) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"x:B")] FIELD_FRACTION_NONZERO) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [(← q r"c:A"), (← q r"d:A")] THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN)) THEN SUBGOAL_THEN (← q r"ring_mul k ((h:A->B) (ring_mul r b d)) (ring_mul k x y) =
    h (ring_mul r a c)") ASSUME_TAC THENL [FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL th)])) THEN SUBGOAL_THEN (← q r"(h:A->B) a IN ring_carrier k /\ h b IN ring_carrier k /\
      h c IN ring_carrier k /\ h d IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], RING_TAC], ALL_TAC] THEN MAP_EVERY (fun (u, a, b) => tactic_of do pure (MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), u, a, b] DEDEKIND_VALUATION))) [((← q r"ring_mul k x y:B"), (← q r"ring_mul r a c:A"), (← q r"ring_mul r b d:A")), ((← q r"x:B"), (← q r"a:A"), (← q r"b:A")), ((← q r"y:B"), (← q r"c:A"), (← q r"d:A"))] THEN ASM_SIMP_TAC [RING_MUL, INTEGRAL_DOMAIN_MUL_EQ_0] THEN REPEAT (DISCH_THEN SUBST1_TAC) THEN ASM_SIMP_TAC [IDEAL_VALUATION_PRINCIPAL_MUL] THEN REWRITE_TAC [(← GSYM INT_OF_NUM_ADD)] THEN INT_ARITH_TAC)

  let DEDEKIND_VALUATION_INV ← prove
    r"!r k (h:A->B) P x.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\
        x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> dedekind_valuation (r,k) h P (ring_inv k x) =
            --(dedekind_valuation (r,k) h P x)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"x:B"), (← q r"ring_inv k x:B")] DEDEKIND_VALUATION_MUL) THEN ASM_SIMP_TAC [FIELD_MUL_RINV, DEDEKIND_VALUATION_1, RING_INV, FIELD_INV_EQ_0] THEN INT_ARITH_TAC)

  let DEDEKIND_VALUATION_DIV ← prove
    r"!r k (h:A->B) P x y.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\
        x IN ring_carrier k /\ ~(x = ring_0 k) /\
        y IN ring_carrier k /\ ~(y = ring_0 k)
        ==> dedekind_valuation (r,k) h P (ring_div k x y) =
            dedekind_valuation (r,k) h P x - dedekind_valuation (r,k) h P y"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN ASM_SIMP_TAC [ring_div, DEDEKIND_VALUATION_MUL, RING_INV, FIELD_INV_EQ_0, DEDEKIND_VALUATION_INV] THEN INT_ARITH_TAC)

  let DEDEKIND_VALUATION_POW ← prove
    r"!r k (h:A->B) P x n.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\
        x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> dedekind_valuation (r,k) h P (ring_pow k x n) =
            &n * dedekind_valuation (r,k) h P x"
    (REPLICATE_TAC 5 GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN INDUCT_TAC THEN ASM_SIMP_TAC [ring_pow, DEDEKIND_VALUATION_1, INT_MUL_LZERO] THEN ASM_SIMP_TAC [DEDEKIND_VALUATION_MUL, RING_POW, FIELD_POW_EQ_0, (← GSYM INT_OF_NUM_SUC)] THEN INT_ARITH_TAC)

  let DEDEKIND_VALUATION_NEG ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"(h:A->B) a IN ring_carrier k /\ h b IN ring_carrier k"
    let q2 ← q r"a:A"
    let q3 ← q r"a:A"
    let q4 ← q r"r:A ring"
    let v5 ← ISPECL [q4, q3, q2] RING_ASSOCIATES_NEG
    let q6 ← q r"a:A"
    let q7 ← q r"ring_neg r a:A"
    let q8 ← q r"r:A ring"
    let v9 ← ISPECL [q8, q7, q6] IDEALS_GENERATED_SING_EQ
    let q10 ← q r"b:A"
    let q11 ← q r"ring_neg r a:A"
    let q12 ← q r"b:A"
    let q13 ← q r"a:A"
    let p14 ← prove r"!r k (h:A->B) P x (v:int).
        ring_homomorphism(r,k) h /\ x IN ring_carrier k /\
        (!a b. a IN ring_carrier r /\ b IN ring_carrier r /\
               ~(a = ring_0 r) /\ ~(b = ring_0 r) /\ ring_mul k (h b) x = h a
               ==> v = &(ideal_valuation r P (ideal_generated r {a})) -
                       &(ideal_valuation r P (ideal_generated r {b})))
        ==> (!a b. a IN ring_carrier r /\ b IN ring_carrier r /\
                   ~(a = ring_0 r) /\ ~(b = ring_0 r) /\
                   ring_mul k (h b) (ring_neg k x) = h a
                   ==> v = &(ideal_valuation r P (ideal_generated r {a})) -
                           &(ideal_valuation r P (ideal_generated r {b})))" (REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [q13, q12] THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPECL [q11, q10])) THEN MP_TAC v9 THEN MP_TAC v5 THEN ASM_SIMP_TAC [RING_NEG, RING_NEG_EQ_0, RING_ASSOCIATES_REFL] THEN REPLICATE_TAC 2 DISCH_TAC THEN DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_NEG th)])) THEN SUBGOAL_THEN q1 STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], RING_TAC])
    let lemma := p14
    let q15 ← q r"v:int"
    let q16 ← q r"ring_neg k x:B"
    let q17 ← q r"P:A->bool"
    let q18 ← q r"h:A->B"
    let q19 ← q r"k:B ring"
    let q20 ← q r"r:A ring"
    let v21 ← ISPECL [q20, q19, q18, q17, q16, q15] lemma
    prove
      r"!r k (h:A->B) P x.
          ring_homomorphism(r,k) h /\ x IN ring_carrier k
          ==> dedekind_valuation (r,k) h P (ring_neg k x) =
              dedekind_valuation (r,k) h P x"
      (REPEAT STRIP_TAC THEN REWRITE_TAC [dedekind_valuation] THEN AP_TERM_TAC THEN ABS_TAC THEN EQ_TAC THEN DISCH_TAC THENL [MP_TAC v21 THEN ASM_SIMP_TAC [RING_NEG, RING_NEG_NEG], MATCH_MP_TAC lemma THEN ASM_REWRITE_TAC []])

  let DEDEKIND_VALUATION_COMPATIBLE ← prove
    r"!r k (h:A->B) P R l (j:C->D) m (i:A->C) (t:B->D) x.
        dedekind_domain r /\ prime_ideal r P /\ ~(P = {ring_0 r}) /\
        field_of_fractions (r,k) h /\
        dedekind_domain R /\ prime_ideal R m /\ ~(m = {ring_0 R}) /\
        ring_monomorphism(R,l) j /\ ring_monomorphism(r,R) i /\
        ring_homomorphism(k,l) t /\
        (!a. a IN ring_carrier r ==> t(h a) = j(i a)) /\
        (!a. a IN ring_carrier r /\ ~(a = ring_0 r)
             ==> ideal_valuation R m (ideal_generated R {i a}) =
                 ideal_valuation r P (ideal_generated r {a})) /\
        x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> dedekind_valuation (R,l) j m (t x) =
            dedekind_valuation (r,k) h P x"
    (REWRITE_TAC [field_of_fractions] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"x:B")] FIELD_FRACTION_NONZERO) THEN ASM_REWRITE_TAC [field_of_fractions] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:A") (X_CHOOSE_THEN (← q r"b:A") STRIP_ASSUME_TAC)) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"x:B"), (← q r"a:A"), (← q r"b:A")] DEDEKIND_VALUATION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ASSUME_TAC (← MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM (← ASSUME (← q r"ring_monomorphism(r,k) (h:A->B)"))) THEN ASSUME_TAC (← MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM (← ASSUME (← q r"ring_monomorphism(r,R) (i:A->C)"))) THEN SUBGOAL_THEN (← q r"(i:A->C) a IN ring_carrier R /\ i b IN ring_carrier R /\
    ~(i a = ring_0 R) /\ ~(i b = ring_0 R) /\
    (t:B->D) x IN ring_carrier l /\ (h:A->B) b IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, RING_MONOMORPHISM_EQ_0], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"R:C ring"), (← q r"l:D ring"), (← q r"j:C->D"), (← q r"m:C->bool"), (← q r"(t:B->D) x"), (← q r"(i:A->C) a"), (← q r"(i:A->C) b")] DEDEKIND_VALUATION) THEN ASM_SIMP_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN SUBGOAL_THEN (← q r"(j:C->D)((i:A->C) a) = (t:B->D)((h:A->B) a) /\
                j(i b) = t(h b)") (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"(h:A->B) b"), (← q r"x:B")] (← MATCH_MP RING_HOMOMORPHISM_MUL (← ASSUME (← q r"ring_homomorphism(k,l) (t:B->D)")))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ACCEPT_TAC o SYM))

  let DEDEKIND_VALUATION_ADD ← prove
    r"!r k (h:A->B) P x y.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\
        x IN ring_carrier k /\ y IN ring_carrier k /\
        ~(ring_add k x y = ring_0 k)
        ==> min (dedekind_valuation (r,k) h P x)
                (dedekind_valuation (r,k) h P y)
            <= dedekind_valuation (r,k) h P (ring_add k x y)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN ASM_CASES_TAC (← q r"x:B = ring_0 k") THENL [ASM_SIMP_TAC [RING_ADD_LZERO] THEN INT_ARITH_TAC, ALL_TAC] THEN ASM_CASES_TAC (← q r"y:B = ring_0 k") THENL [ASM_SIMP_TAC [RING_ADD_RZERO] THEN INT_ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"y:B")] FIELD_FRACTION_NONZERO) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"x:B")] FIELD_FRACTION_NONZERO) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [(← q r"c:A"), (← q r"d:A")] THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN)) THEN SUBGOAL_THEN (← q r"(h:A->B) a IN ring_carrier k /\ h b IN ring_carrier k /\
    h c IN ring_carrier k /\ h d IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul k ((h:A->B) (ring_mul r b d)) x = h (ring_mul r a d) /\
    ring_mul k (h (ring_mul r b d)) y = h (ring_mul r c b) /\
    ring_mul k (h (ring_mul r b d)) (ring_add k x y) =
    h (ring_add r (ring_mul r a d) (ring_mul r c b))") STRIP_ASSUME_TAC THENL [FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL th), (← MATCH_MP RING_HOMOMORPHISM_ADD th), RING_MUL])) THEN REPEAT CONJ_TAC THEN RING_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"~(ring_add r (ring_mul r a d) (ring_mul r c b) = ring_0 r:A)") ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC (← q r"ring_mul k ((h:A->B) (ring_mul r b d)) (ring_add k x y) =
      h (ring_add r (ring_mul r a d) (ring_mul r c b))") THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_0 th)])) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"ring_mul r b d:A")] RING_MONOMORPHISM_EQ_0) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"ring_mul r b d:A")] RING_HOMOMORPHISM_IN_CARRIER) THEN ASM_SIMP_TAC [RING_MUL, RING_ADD, INTEGRAL_DOMAIN_MUL_EQ_0, FIELD_IMP_INTEGRAL_DOMAIN], ALL_TAC] THEN MAP_EVERY (fun (u, a) => tactic_of do pure (MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), u, a, (← q r"ring_mul r b d:A")] DEDEKIND_VALUATION))) [((← q r"ring_add k x y:B"), (← q r"ring_add r (ring_mul r a d) (ring_mul r c b):A")), ((← q r"x:B"), (← q r"ring_mul r a d:A")), ((← q r"y:B"), (← q r"ring_mul r c b:A"))] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"ring_mul r a d:A"), (← q r"ring_mul r c b:A")] IDEAL_VALUATION_PRINCIPAL_ADD) THEN ASM_SIMP_TAC [RING_MUL, RING_ADD, INTEGRAL_DOMAIN_MUL_EQ_0] THEN REWRITE_TAC [(← GSYM INT_OF_NUM_LE), (← GSYM INT_OF_NUM_MIN)] THEN INT_ARITH_TAC)

  let DEDEKIND_VALUATION_ADD_STRICT ← prove
    r"!r k (h:A->B) P x y.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\
        x IN ring_carrier k /\ ~(x = ring_0 k) /\ y IN ring_carrier k /\
        dedekind_valuation (r,k) h P x < dedekind_valuation (r,k) h P y
        ==> dedekind_valuation (r,k) h P (ring_add k x y) =
            dedekind_valuation (r,k) h P x"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN ASM_CASES_TAC (← q r"y:B = ring_0 k") THEN ASM_SIMP_TAC [RING_ADD_RZERO] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN SUBGOAL_THEN (← q r"ring_add k (ring_add k x y) (ring_neg k y) = x:B") ASSUME_TAC THENL [RING_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"~(ring_add k x y = ring_0 k:B)") ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC (← q r"ring_add k (ring_add k x y) (ring_neg k y) = x:B") THEN ASM_SIMP_TAC [RING_ADD_LZERO, RING_NEG] THEN DISCH_THEN (SUBST_ALL_TAC o SYM) THEN UNDISCH_TAC (← q r"dedekind_valuation (r,k) h P (ring_neg k y:B) <
                 dedekind_valuation (r,k) (h:A->B) P y") THEN ASM_SIMP_TAC [DEDEKIND_VALUATION_NEG, INT_LT_REFL], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"x:B"), (← q r"y:B")] DEDEKIND_VALUATION_ADD) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"ring_add k x y:B"), (← q r"ring_neg k y:B")] DEDEKIND_VALUATION_ADD) THEN ASM_SIMP_TAC [RING_ADD, RING_NEG, DEDEKIND_VALUATION_NEG] THEN ASM_INT_ARITH_TAC)

  let DEDEKIND_VALUATION_FINITE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"(p <=> ~q) ==> (q <=> ~p)")
    prove
      r"!r k (h:A->B) x.
          dedekind_domain r /\ field_of_fractions (r,k) h /\
          x IN ring_carrier k /\ ~(x = ring_0 k)
          ==> FINITE {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
                          ~(dedekind_valuation (r,k) h P x = &0)}"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"x:B")] FIELD_FRACTION_NONZERO) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN)) THEN SUBGOAL_THEN (← q r"ring_mul r a b IN ring_carrier r /\ ~(ring_mul r a b = ring_0 r:A)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_MUL, INTEGRAL_DOMAIN_MUL_EQ_0], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_generated r {ring_mul r a b:A}")] DEDEKIND_IDEAL_FACTORIZATION) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0] THEN DISCH_THEN (MATCH_MP_TAC o ((MATCH_MP (← REWRITE_RULE [IMP_CONJ] FINITE_SUBSET)) o CONJUNCT1)) THEN GEN_REWRITE_TAC id [SUBSET] THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"ideal_generated r {ring_mul r a b:A}")] IDEAL_VALUATION_EQ_0) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0] THEN DISCH_THEN (SUBST1_TAC o (MATCH_MP r1)) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"a:A"), (← q r"b:A")] IDEAL_VALUATION_PRINCIPAL_MUL) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"x:B"), (← q r"a:A"), (← q r"b:A")] DEDEKIND_VALUATION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST_ALL_TAC THEN DISCH_THEN SUBST1_TAC THEN POP_ASSUM MP_TAC THEN REWRITE_TAC [(← GSYM INT_OF_NUM_EQ), (← GSYM INT_OF_NUM_ADD)] THEN INT_ARITH_TAC)

  let DEDEKIND_VALUATION_INTEGRAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r3 ← TAUT (← q r"q /\ (p ==> r) ==> (p <=> q) ==> r")
    prove
      r"!r k (h:A->B) x.
          dedekind_domain r /\ field_of_fractions (r,k) h /\
          x IN ring_carrier k /\ ~(x = ring_0 k)
          ==> (x IN IMAGE h (ring_carrier r) <=>
               !P. prime_ideal r P /\ ~(P = {ring_0 r})
                   ==> &0 <= dedekind_valuation (r,k) h P x)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN EQ_TAC THENL [REWRITE_TAC [IN_IMAGE] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:A") (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"~(c:A = ring_0 r)") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~((h:A->B)(ring_0 r) = ring_0 k)") THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_0 th)])), ASM_SIMP_TAC [DEDEKIND_VALUATION_IMAGE, INT_POS]], DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"x:B")] FIELD_FRACTION_NONZERO) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_generated r {a:A}"), (← q r"ideal_generated r {b:A}")] DEDEKIND_IDEAL_SUBSET_VALUATION) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0, SUBSET_IDEALS_GENERATED_SING] THEN MATCH_MP_TAC r3 THEN CONJ_TAC THENL [X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"x:B"), (← q r"a:A"), (← q r"b:A")] DEDEKIND_VALUATION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [INT_SUB_LE, INT_OF_NUM_LE], REWRITE_TAC [ring_divides] THEN DISCH_THEN (fun z1 => tactic_of do pure (X_CHOOSE_THEN (← q r"c:A") STRIP_ASSUME_TAC (← (do let z2 ← (pure (CONJUNCTS z1)); liftExcept (last z2))))) THEN REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC (← q r"c:A") THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN MAP_EVERY EXISTS_TAC [(← q r"k:B ring"), (← q r"(h:A->B) b")] THEN SUBGOAL_THEN (← q r"(h:A->B) b IN ring_carrier k /\ h c IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN] THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0], FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL th)]))]])

  let DEDEKIND_VALUATION_UNIT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← INT_ARITH (← q r"&0 <= x /\ &0 <= --x <=> x:int = &0")
    let r2 ← TAUT (← q r"(p ==> q) /\ (p ==> r) <=> p ==> q /\ r")
    prove
      r"!r k (h:A->B) x.
          dedekind_domain r /\ field_of_fractions (r,k) h /\
          x IN ring_carrier k
          ==> (x IN IMAGE h {u | ring_unit r u} <=>
               ~(x = ring_0 k) /\
               !P. prime_ideal r P /\ ~(P = {ring_0 r})
                   ==> dedekind_valuation (r,k) h P x = &0)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN ASM_CASES_TAC (← q r"x:B = ring_0 k") THEN ASM_REWRITE_TAC [] THENL [REWRITE_TAC [IN_IMAGE, IN_ELIM_THM, NOT_EXISTS_THM] THEN X_GEN_TAC (← q r"u:A") THEN STRIP_TAC THEN ASM_MESON_TAC [RING_UNIT_IN_CARRIER, RING_MONOMORPHISM_EQ_0, RING_UNIT_0, INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING, DEDEKIND_IMP_INTEGRAL_DOMAIN], ALL_TAC] THEN SUBGOAL_THEN (← q r"x IN IMAGE (h:A->B) {u | ring_unit r u} <=>
      x IN IMAGE h (ring_carrier r) /\ ring_inv k x IN IMAGE h (ring_carrier r)") SUBST1_TAC THENL [REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN EQ_TAC THENL [DISCH_THEN (X_CHOOSE_THEN (← q r"u:A") (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN CONJ_TAC THENL [EXISTS_TAC (← q r"u:A") THEN ASM_MESON_TAC [RING_UNIT_IN_CARRIER], EXISTS_TAC (← q r"ring_inv r u:A") THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_INV th), RING_INV, RING_UNIT_IN_CARRIER]))], DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"a:A") STRIP_ASSUME_TAC) (X_CHOOSE_THEN (← q r"c:A") STRIP_ASSUME_TAC)) THEN EXISTS_TAC (← q r"a:A") THEN ASM_REWRITE_TAC [ring_unit] THEN EXISTS_TAC (← q r"c:A") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"ring_mul r a c:A"), (← q r"ring_1 r:A")] RING_MONOMORPHISM_INJECTIVE_EQ) THEN ASM_SIMP_TAC [RING_MUL, RING_1] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL th), (← MATCH_MP RING_HOMOMORPHISM_1 th)])) THEN UNDISCH_TAC (← q r"ring_inv k x = (h:A->B) c") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN UNDISCH_TAC (← q r"x = (h:A->B) a") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [FIELD_MUL_RINV]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"ring_inv k x:B")] DEDEKIND_VALUATION_INTEGRAL) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"x:B")] DEDEKIND_VALUATION_INTEGRAL) THEN ASM_SIMP_TAC [RING_INV, FIELD_INV_EQ_0, DEDEKIND_VALUATION_INV] THEN REPEAT (DISCH_THEN (fun (_ : thm) => ALL_TAC)) THEN REWRITE_TAC [AND_FORALL_THM] THEN REWRITE_TAC [r2] THEN REWRITE_TAC [r1])

  let DEDEKIND_VALUATION_PRIME_IDEAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(x:A) IN s ==> s INTER {x} = {x}")
    prove
      r"!r k (h:A->B) P a.
          dedekind_domain r /\ ring_monomorphism(r,k) h /\
          prime_ideal r P /\ ~(P = {ring_0 r}) /\
          a IN ring_carrier r /\ ~(a = ring_0 r)
          ==> (a IN P <=> &0 < dedekind_valuation (r,k) h P (h a))"
      (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [DEDEKIND_VALUATION_IMAGE] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"ideal_generated r {a:A}")] IDEAL_VALUATION_EQ_0) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0, IDEAL_GENERATED_MINIMAL_EQ, PRIME_IMP_RING_IDEAL, r1, SING_SUBSET] THEN REWRITE_TAC [INT_OF_NUM_LT, LT_NZ] THEN CONV_TAC TAUT)

  let DEDEKIND_VALUATION_EQ ← prove
    r"!r k (h:A->B) x y.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        x IN ring_carrier k /\ ~(x = ring_0 k) /\
        y IN ring_carrier k /\ ~(y = ring_0 k)
        ==> ((!P. prime_ideal r P /\ ~(P = {ring_0 r})
                  ==> dedekind_valuation (r,k) h P x =
                      dedekind_valuation (r,k) h P y) <=>
             ?u. ring_unit r u /\ x = ring_mul k (h u) y)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN EQ_TAC THENL [DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"ring_mul k x (ring_inv k y):B")] DEDEKIND_VALUATION_UNIT) THEN ASM_SIMP_TAC [RING_MUL, RING_INV, INTEGRAL_DOMAIN_MUL_EQ_0, FIELD_IMP_INTEGRAL_DOMAIN, FIELD_INV_EQ_0, DEDEKIND_VALUATION_MUL, DEDEKIND_VALUATION_INV, INT_ADD_RINV] THEN REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"u:A") THEN DISCH_THEN (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN ASM_SIMP_TAC [(← GSYM RING_MUL_ASSOC), RING_INV, FIELD_MUL_LINV, RING_MUL_RID], DISCH_THEN (X_CHOOSE_THEN (← q r"u:A") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(h:A->B) u IN ring_carrier k /\ h u IN IMAGE h {u | ring_unit r u}") STRIP_ASSUME_TAC THENL [REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, RING_UNIT_IN_CARRIER], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"(h:A->B) u")] DEDEKIND_VALUATION_UNIT) THEN ASM_SIMP_TAC [DEDEKIND_VALUATION_MUL, INT_ADD_LID]])

  let DEDEKIND_IDEAL_PRESCRIBED_VALUATIONS ← prove
    r"!r f:(A->bool)->num.
        dedekind_domain r /\
        FINITE {p | prime_ideal r p /\ ~(p = {ring_0 r}) /\ ~(f p = 0)}
        ==> ?j. ring_ideal r j /\ ~(j = {ring_0 r}) /\
                !p. prime_ideal r p /\ ~(p = {ring_0 r})
                    ==> ideal_valuation r p j = f p"
    (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"g = monomial_restrict
                   {p:A->bool | prime_ideal r p /\ ~(p = {ring_0 r})} f") THEN SUBGOAL_THEN (← q r"monomial {p:A->bool | prime_ideal r p /\ ~(p = {ring_0 r})} g") ASSUME_TAC THENL [EXPAND_TAC "g" THEN ASM_REWRITE_TAC [MONOMIAL_RESTRICT_EQ, monomial_vars, INTER, IN_ELIM_THM, (← GSYM CONJ_ASSOC)], ALL_TAC] THEN EXISTS_TAC (← q r"ideal_product r (monomial_vars g)
                (\p:A->bool. ideal_pow r p (g p))") THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_PRODUCT, IDEAL_VALUATION_IDEAL_PRODUCT_MONOMIAL] THEN CONJ_TAC THENL [FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [monomial])) THEN ASM_SIMP_TAC [IDEAL_PRODUCT_EQ_ZERO, DEDEKIND_IMP_INTEGRAL_DOMAIN, RING_IDEAL_IDEAL_POW] THEN REWRITE_TAC [NOT_EXISTS_THM] THEN X_GEN_TAC (← q r"p:A->bool") THEN UNDISCH_TAC (← q r"monomial_vars g SUBSET
                 {p:A->bool | prime_ideal r p /\ ~(p = {ring_0 r})}") THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"p:A->bool"))) THEN ASM_CASES_TAC (← q r"(p:A->bool) IN monomial_vars g") THEN ASM_SIMP_TAC [IDEAL_POW_EQ_ZERO, DEDEKIND_IMP_INTEGRAL_DOMAIN, PRIME_IMP_RING_IDEAL], EXPAND_TAC "g" THEN SIMP_TAC [monomial_restrict, IN_ELIM_THM]])

  let ideal_of_valuations ← new_definition
    r"ideal_of_valuations (r:A ring) (e:(A->bool)->num) =
        @j. ring_ideal r j /\ ~(j = {ring_0 r}) /\
            !P. prime_ideal r P /\ ~(P = {ring_0 r})
                ==> ideal_valuation r P j = e P"

  let IDEAL_OF_VALUATIONS ← prove
    r"!r (e:(A->bool)->num).
        dedekind_domain r /\
        FINITE {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(e P = 0)}
        ==> ring_ideal r (ideal_of_valuations r e) /\
            ~(ideal_of_valuations r e = {ring_0 r}) /\
            !P. prime_ideal r P /\ ~(P = {ring_0 r})
                ==> ideal_valuation r P (ideal_of_valuations r e) = e P"
    (REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [ideal_of_valuations] THEN CONV_TAC SELECT_CONV THEN ASM_SIMP_TAC [DEDEKIND_IDEAL_PRESCRIBED_VALUATIONS])

  let IDEAL_OF_VALUATIONS_UNIQUE ← prove
    r"!r (e:(A->bool)->num) j.
        dedekind_domain r /\ ring_ideal r j /\ ~(j = {ring_0 r}) /\
        (!P. prime_ideal r P /\ ~(P = {ring_0 r})
             ==> ideal_valuation r P j = e P)
        ==> ideal_of_valuations r e = j"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"FINITE {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
                ~((e:(A->bool)->num) P = 0)}") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool")] IDEAL_VALUATION_FINITE_SUPPORT) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] FINITE_SUBSET) THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"e:(A->bool)->num")] IDEAL_OF_VALUATIONS) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_SIMP_TAC [DEDEKIND_IDEAL_EQ_VALUATION])

  let IDEAL_OF_VALUATIONS_ADD ← prove
    r"!r (e:(A->bool)->num) f.
        dedekind_domain r /\
        FINITE {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(e P = 0)} /\
        FINITE {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(f P = 0)}
        ==> ideal_of_valuations r (\P. e P + f P) =
            ideal_prod r (ideal_of_valuations r e) (ideal_of_valuations r f)"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC IDEAL_OF_VALUATIONS_UNIQUE THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"e:(A->bool)->num")] IDEAL_OF_VALUATIONS) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"f:(A->bool)->num")] IDEAL_OF_VALUATIONS) THEN ASM_REWRITE_TAC [] THEN REPEAT (DISCH_THEN STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_PROD, IDEAL_PROD_EQ_ZERO, DEDEKIND_IMP_INTEGRAL_DOMAIN, IDEAL_VALUATION_IDEAL_PROD])

  let IDEAL_OF_VALUATIONS_0 ← prove
    r"!r:A ring.
        dedekind_domain r ==> ideal_of_valuations r (\P. 0) = ring_carrier r"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC IDEAL_OF_VALUATIONS_UNIQUE THEN ASM_REWRITE_TAC [RING_IDEAL_CARRIER] THEN CONJ_TAC THENL [ASM_MESON_TAC [FIELD_EQ_TRIVIAL_IDEALS, DEDEKIND_IMP_INTEGRAL_DOMAIN, INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING, RING_CARRIER_NONEMPTY, TRIVIAL_RING_SUBSET, SUBSET_REFL], REPEAT STRIP_TAC THEN MATCH_MP_TAC IDEAL_VALUATION_CARRIER THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN ASM_MESON_TAC [PRIME_IMP_PROPER_IDEAL, PROPER_IDEAL_ALT, prime_ideal, proper_ideal]])

  let IDEAL_OF_VALUATIONS_EQ ← prove
    r"!r (e:(A->bool)->num) f.
        (!P. prime_ideal r P /\ ~(P = {ring_0 r}) ==> e P = f P)
        ==> ideal_of_valuations r e = ideal_of_valuations r f"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [ideal_of_valuations] THEN AP_TERM_TAC THEN ABS_TAC THEN ASM_MESON_TAC [])

  let DEDEKIND_VALUATION_WEAK_APPROXIMATION ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← INT_ARITH (← q r"&0 <= max (x:int) (&0)")
    prove
      r"!r k (h:A->B) s (e:(A->bool)->int).
          dedekind_domain r /\ field k /\ ring_monomorphism(r,k) h /\
          FINITE s /\ (!P. P IN s ==> prime_ideal r P /\ ~(P = {ring_0 r}))
          ==> ?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\
                  !P. P IN s ==> dedekind_valuation (r,k) h P x = e P"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:(A->bool)->bool"), (← q r"\P:A->bool. num_of_int(max (--(e P)) (&0))")] DEDEKIND_WEAK_APPROXIMATION) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:(A->bool)->bool"), (← q r"\P:A->bool. num_of_int(max (e P) (&0))")] DEDEKIND_WEAK_APPROXIMATION) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"a:A") THEN STRIP_TAC THEN X_GEN_TAC (← q r"b:A") THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN SUBGOAL_THEN (← q r"(h:A->B) a IN ring_carrier k /\ h b IN ring_carrier k /\
      ~(h a = ring_0 k) /\ ~(h b = ring_0 k)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, RING_MONOMORPHISM_EQ_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_inv k ((h:A->B) b) IN ring_carrier k /\
      ring_mul k (h b) (ring_inv k (h b)) = ring_1 k") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_INV, FIELD_MUL_RINV], ALL_TAC] THEN EXISTS_TAC (← q r"ring_mul k ((h:A->B) a) (ring_inv k (h b))") THEN ASM_SIMP_TAC [RING_MUL, INTEGRAL_DOMAIN_MUL_EQ_0, FIELD_IMP_INTEGRAL_DOMAIN, FIELD_INV_EQ_0] THEN X_GEN_TAC (← q r"P:A->bool") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"ring_mul k ((h:A->B) a) (ring_inv k (h b))"), (← q r"a:A"), (← q r"b:A")] DEDEKIND_VALUATION) THEN ASM_SIMP_TAC [RING_MUL] THEN ANTS_TAC THENL [RING_TAC, DISCH_THEN SUBST1_TAC] THEN ASM_SIMP_TAC [INT_OF_NUM_OF_INT, r1] THEN INT_ARITH_TAC)

  -- @@RETURN BEGIN
  return { dedekind_valuation, DEDEKIND_VALUATION, DEDEKIND_VALUATION_IMAGE,
           DEDEKIND_VALUATION_1, FIELD_FRACTION_NONZERO, DEDEKIND_VALUATION_MUL,
           DEDEKIND_VALUATION_INV, DEDEKIND_VALUATION_DIV, DEDEKIND_VALUATION_POW,
           DEDEKIND_VALUATION_NEG, DEDEKIND_VALUATION_COMPATIBLE, DEDEKIND_VALUATION_ADD,
           DEDEKIND_VALUATION_ADD_STRICT, DEDEKIND_VALUATION_FINITE,
           DEDEKIND_VALUATION_INTEGRAL, DEDEKIND_VALUATION_UNIT,
           DEDEKIND_VALUATION_PRIME_IDEAL, DEDEKIND_VALUATION_EQ,
           DEDEKIND_IDEAL_PRESCRIBED_VALUATIONS, ideal_of_valuations,
           IDEAL_OF_VALUATIONS, IDEAL_OF_VALUATIONS_UNIQUE, IDEAL_OF_VALUATIONS_ADD,
           IDEAL_OF_VALUATIONS_0, IDEAL_OF_VALUATIONS_EQ,
           DEDEKIND_VALUATION_WEAK_APPROXIMATION }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- dedekind_valuation.ml phrases from line 833 to 1337                    -/
/- ---------------------------------------------------------------------- -/

structure DedekindValuation02 where
  -- @@FIELDS
  DEDEKIND_VALUATION_APPROXIMATION : thm
  DEDEKIND_DENOMINATOR_IDEAL : thm
  DEDEKIND_IDEAL_MUL_INTEGRAL : thm
  DEDEKIND_VALUATION_POS : thm
  DEDEKIND_VALUATION_RING_LOCALIZATION : thm
  DEDEKIND_VALUATION_LOCALIZATION : thm
  ISOMORPHIC_RING_DVR : thm
  DEDEKIND_VALUATION_RING_DVR : thm
  DVR_DEDEKIND_VALUATION : thm
  DEDEKIND_UNIFORMIZER_CRITERION : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDedekindValuation02 [HolBase] (D : DedekindValuationDeps) (BDedekindValuation01 : DedekindValuation01) :
    ExceptT String IO DedekindValuation02 := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_INT_ARITH_TAC, ASM_MESON_TAC, INT_ARITH, INT_ARITH_TAC,
        MESON_TAC, RING_RULE, SET_RULE, SET_TAC, TAUT, .. } := D
  let { DEDEKIND_IDEAL_FACTORIZATION, DEDEKIND_IDEAL_SUBSET_VALUATION,
        DEDEKIND_IMP_INTEGRAL_DOMAIN, DEDEKIND_IN_IDEAL_POW_VALUATION,
        DEDEKIND_LOCALIZATION, DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL,
        DEDEKIND_WEAK_APPROXIMATION, DE_MORGAN_THM, DVR, DVR_IFF_LOCAL_DEDEKIND,
        DVR_LOCALIZATION, EXISTS_UNIQUE_DEF, EXTENSION, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_INV_EQ_0, FIELD_MUL_EQ_0, FIELD_MUL_RINV, FIELD_UNIT, FINITE_SUBSET,
        FINITE_UNION, FORALL_IN_GSPEC, FORALL_IN_IMAGE, IDEAL_GENERATED_EQ_0,
        IDEAL_GENERATED_MINIMAL, IDEAL_GENERATED_MINIMAL_EQ,
        IDEAL_GENERATED_RING_LOCALIZATION, IDEAL_LOCALIZATION_EQ_ZERO, IDEAL_POW_1,
        IDEAL_POW_EQ_ZERO, IDEAL_POW_PRINCIPAL, IDEAL_VALUATION_EQ_0,
        IDEAL_VALUATION_IDEAL_POW, IDEAL_VALUATION_LOCALIZATION, IDEAL_VALUATION_PRIME,
        IDEAL_VALUATION_PRINCIPAL_MUL, IDEAL_VALUATION_SETADD, IMAGE_CLAUSES, IMP_CONJ,
        INTEGRAL_DOMAIN_MUL_EQ_0, INTEGRAL_DOMAIN_MUL_LCANCEL,
        INTEGRAL_DOMAIN_POW_EQ_0, INTEGRAL_DOMAIN_REGULAR, INT_LE_REFL, INT_OF_NUM_EQ,
        INT_OF_NUM_LE, INT_OF_NUM_OF_INT, INT_SUB_REFL, IN_DIFF, IN_ELIM_THM,
        IN_IDEAL_GENERATED_SING_EQ, IN_IMAGE, IN_RING_IDEAL_0, IN_SING, IN_UNION,
        ISOMORPHIC_RING_FIELDNESS, ISOMORPHIC_RING_LOCALITY, ISOMORPHIC_RING_PIDNESS,
        LEFT_IMP_EXISTS_THM, LOCALEQUIV_MUL_RCANCEL, .. } := D.core1
  let { MAXIMAL_IDEAL_0, MAXIMAL_IMP_PRIME_IDEAL, MIN, MONO_EXISTS, NOT_EXISTS_THM,
        NOT_FORALL_THM, NOT_IMP, PRIME_IDEAL_IMP_SUBSET, PRIME_IDEAL_LOCALIZATION,
        PRIME_IMP_PROPER_IDEAL, PRIME_IMP_RING_IDEAL, PROPER_IDEAL,
        RIGHT_FORALL_IMP_THM, RING_0, RING_1, RING_ADD_LZERO,
        RING_FRACTIONATE_EQ_0_GEN, RING_FRACTIONATE_IN_CARRIER, RING_HOMOMORPHISM_0,
        RING_HOMOMORPHISM_1, RING_HOMOMORPHISM_IN_CARRIER, RING_HOMOMORPHISM_MUL,
        RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_POW, RING_IDEAL_IMP_SUBSET,
        RING_IDEAL_SETADD, RING_INV, RING_ISOMORPHISM_ONTO_IMAGE,
        RING_LOCALEQUIV_EQ_0_GEN, RING_LOCALEQUIV_IN_CARRIER,
        RING_LOCALIZATION_CARRIER, RING_LOCALIZATION_UNIVERSAL, RING_MONOMORPHISM_ALT,
        RING_MONOMORPHISM_EQ_0, RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL,
        RING_MULTSYS_IMP_SUBSET, RING_MULTSYS_NONPRIME, RING_MUL_LZERO, RING_MUL_RZERO,
        RING_POW, RING_UNIT_IN_CARRIER, SING_SUBSET, SUBSET, SUBSET_ANTISYM,
        field_of_fractions, isomorphic_ring, local_ring, ring_divides, ring_image,
        ring_setadd, .. } := D.core2
  let { DEDEKIND_IDEAL_PRESCRIBED_VALUATIONS, DEDEKIND_VALUATION,
        DEDEKIND_VALUATION_FINITE, DEDEKIND_VALUATION_IMAGE,
        DEDEKIND_VALUATION_INTEGRAL, DEDEKIND_VALUATION_MUL, DEDEKIND_VALUATION_UNIT,
        FIELD_FRACTION_NONZERO, .. } := BDedekindValuation01
  -- @@SCOPE END

  let DEDEKIND_VALUATION_APPROXIMATION ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← INT_ARITH (← q r"&0:int <= e + max (&0) (--e)")
    let r2 ← INT_ARITH (← q r"&0:int <= max (&0) x")
    let r3 ← RING_RULE (← q r"ring_mul (k:B ring) a b = ring_1 k
      ==> ring_mul k a (ring_mul k c b) = c")
    prove
      r"!r k (h:A->B) s (e:(A->bool)->int).
          dedekind_domain r /\ field k /\ ring_monomorphism(r,k) h /\
          FINITE s /\ (!P. P IN s ==> prime_ideal r P /\ ~(P = {ring_0 r}))
          ==> ?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\
                  (!P. P IN s ==> dedekind_valuation (r,k) h P x = e P) /\
                  (!P. prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(P IN s)
                       ==> &0 <= dedekind_valuation (r,k) h P x)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN ASSUME_TAC (← MATCH_MP (← REWRITE_RULE [IMP_CONJ] RING_MONOMORPHISM_EQ_0) (← ASSUME (← q r"ring_monomorphism(r,k) (h:A->B)"))) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:(A->bool)->bool"), (← q r"\P. num_of_int(max (&0) (--((e:(A->bool)->int) P)))")] DEDEKIND_WEAK_APPROXIMATION) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"d:A") THEN STRIP_TAC THEN ABBREV_TAC (← q r"t = s UNION {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
                       ideal_generated r {d:A} SUBSET P}") THEN SUBGOAL_THEN (← q r"FINITE(t:(A->bool)->bool)") ASSUME_TAC THENL [EXPAND_TAC "t" THEN REWRITE_TAC [FINITE_UNION] THEN ASM_SIMP_TAC [DEDEKIND_IDEAL_FACTORIZATION, RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"t:(A->bool)->bool"), (← q r"\P. if P IN s
                        then num_of_int((e:(A->bool)->int) P +
                                        max (&0) (--(e P)))
                        else ideal_valuation r P (ideal_generated r {d:A})")] DEDEKIND_WEAK_APPROXIMATION) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN EXPAND_TAC "t" THEN REWRITE_TAC [IN_UNION, IN_ELIM_THM] THEN ASM_MESON_TAC [], REWRITE_TAC [LEFT_IMP_EXISTS_THM]] THEN X_GEN_TAC (← q r"y:A") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"~((h:A->B) d = ring_0 k) /\ ~(h y = ring_0 k) /\
                  h d IN ring_carrier k /\ h y IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN EXISTS_TAC (← q r"ring_mul k ((h:A->B) y) (ring_inv k (h d))") THEN SUBGOAL_THEN (← q r"ring_mul k ((h:A->B) d) (ring_mul k (h y) (ring_inv k (h d))) = h y") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:B ring"), (← q r"(h:A->B) d")] FIELD_MUL_RINV) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r3 THEN ASM_SIMP_TAC [RING_INV], ALL_TAC] THEN ASM_SIMP_TAC [RING_MUL, RING_INV, FIELD_MUL_EQ_0, FIELD_INV_EQ_0] THEN SUBGOAL_THEN (← q r"!P. prime_ideal r P /\ ~(P = {ring_0 r})
          ==> dedekind_valuation (r,k) (h:A->B) P
               (ring_mul k (h y) (ring_inv k (h d))) =
              &(ideal_valuation r P (ideal_generated r {y})) -
              &(ideal_valuation r P (ideal_generated r {d}))") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC DEDEKIND_VALUATION THEN ASM_SIMP_TAC [RING_MUL, RING_INV], ALL_TAC] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"P:A->bool") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"prime_ideal r P /\ ~(P = {ring_0 r:A})") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ASM_SIMP_TAC []] THEN SUBGOAL_THEN (← q r"(P:A->bool) IN t") ASSUME_TAC THENL [EXPAND_TAC "t" THEN ASM_REWRITE_TAC [IN_UNION], ALL_TAC] THEN ASM_SIMP_TAC [] THEN SIMP_TAC [INT_OF_NUM_OF_INT, r2, r1] THEN INT_ARITH_TAC, ALL_TAC] THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN ASM_SIMP_TAC [] THEN ASM_CASES_TAC (← q r"(P:A->bool) IN t") THENL [ASM_SIMP_TAC [INT_SUB_REFL, INT_LE_REFL], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_valuation r P (ideal_generated r {d:A}) = 0") SUBST1_TAC THENL [ASM_SIMP_TAC [IDEAL_VALUATION_EQ_0, RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0] THEN UNDISCH_TAC (← q r"~((P:A->bool) IN t)") THEN EXPAND_TAC "t" THEN ASM_REWRITE_TAC [IN_UNION, IN_ELIM_THM], INT_ARITH_TAC])

  let DEDEKIND_DENOMINATOR_IDEAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← INT_ARITH (← q r"&0 <= max (&0) (x:int)")
    let r2 ← INT_ARITH (← q r"&0 <= max (&0) (x:int)")
    prove
      r"!r k (h:A->B) x.
          dedekind_domain r /\ field_of_fractions (r,k) h /\
          x IN ring_carrier k /\ ~(x = ring_0 k)
          ==> ?J. ring_ideal r J /\ ~(J = {ring_0 r}) /\
                  !P. prime_ideal r P /\ ~(P = {ring_0 r})
                      ==> &(ideal_valuation r P J):int =
                          max (&0) (--(dedekind_valuation (r,k) h P x))"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"\P:A->bool. num_of_int(max (&0)
                      (--(dedekind_valuation (r,k) (h:A->B) P x)))")] DEDEKIND_IDEAL_PRESCRIBED_VALUATIONS) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
                       ~(dedekind_valuation (r,k) (h:A->B) P x = &0)}") THEN ASM_SIMP_TAC [DEDEKIND_VALUATION_FINITE] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM, (← GSYM INT_OF_NUM_EQ)] THEN SIMP_TAC [INT_OF_NUM_OF_INT, r2] THEN INT_ARITH_TAC, MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [INT_OF_NUM_OF_INT, r1]])

  let DEDEKIND_IDEAL_MUL_INTEGRAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (q ==> r) ==> (p <=> q) ==> r")
    prove
      r"!r k (h:A->B) J x c.
          dedekind_domain r /\ field_of_fractions (r,k) h /\
          ring_ideal r J /\ x IN ring_carrier k /\
          (!P. prime_ideal r P /\ ~(P = {ring_0 r})
               ==> &0 <= &(ideal_valuation r P J) +
                         dedekind_valuation (r,k) h P x) /\
          c IN J
          ==> ring_mul k (h c) x IN IMAGE h (ring_carrier r)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN SUBGOAL_THEN (← q r"(c:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"(h:A->B) c IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN ASM_CASES_TAC (← q r"c:A = ring_0 r \/ x:B = ring_0 k") THENL [FIRST_X_ASSUM (DISJ_CASES_THEN SUBST_ALL_TAC) THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_0 th)])) THEN ASM_SIMP_TAC [RING_MUL_LZERO, RING_MUL_RZERO, IN_IMAGE] THEN EXISTS_TAC (← q r"ring_0 r:A") THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_0 th)])) THEN REWRITE_TAC [RING_0], FIRST_X_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [DE_MORGAN_THM]))] THEN SUBGOAL_THEN (← q r"~((h:A->B) c = ring_0 k)") ASSUME_TAC THENL [ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"ring_mul k ((h:A->B) c) x")] DEDEKIND_VALUATION_INTEGRAL) THEN ASM_SIMP_TAC [RING_MUL, INTEGRAL_DOMAIN_MUL_EQ_0, FIELD_IMP_INTEGRAL_DOMAIN] THEN DISCH_THEN SUBST1_TAC THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN ASM_SIMP_TAC [DEDEKIND_VALUATION_MUL, DEDEKIND_VALUATION_IMAGE] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_generated r {c:A}"), (← q r"J:A->bool")] DEDEKIND_IDEAL_SUBSET_VALUATION) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0] THEN DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"(c:A) IN {ring_0 r}") THEN ASM_REWRITE_TAC [IN_SING], ALL_TAC] THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET], DISCH_THEN (MP_TAC o (SPEC (← q r"P:A->bool")))] THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN REWRITE_TAC [(← GSYM INT_OF_NUM_LE)] THEN INT_ARITH_TAC)

  let DEDEKIND_VALUATION_POS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(x:A) IN s ==> s INTER {x} = {x}")
    prove
      r"!r k (h:A->B) P x.
          dedekind_domain r /\ field_of_fractions (r,k) h /\
          prime_ideal r P /\ ~(P = {ring_0 r}) /\ x IN ring_carrier k
          ==> ((x = ring_0 k \/ &0 <= dedekind_valuation (r,k) h P x) <=>
               ?a b. a IN ring_carrier r /\ b IN ring_carrier r /\ ~(b IN P) /\
                     ring_mul k (h b) x = h a)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN ASM_CASES_TAC (← q r"x:B = ring_0 k") THEN ASM_REWRITE_TAC [] THENL [MAP_EVERY EXISTS_TAC [(← q r"ring_0 r:A"), (← q r"ring_1 r:A")] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_0 th), (← MATCH_MP RING_HOMOMORPHISM_1 th)])) THEN ASM_SIMP_TAC [RING_0, RING_1, RING_MUL_RZERO] THEN ASM_MESON_TAC [PRIME_IMP_PROPER_IDEAL, PROPER_IDEAL], EQ_TAC] THENL [DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"x:B")] DEDEKIND_DENOMINATOR_IDEAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"J:A->bool") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"~(J SUBSET (P:A->bool))") MP_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"J:A->bool")] IDEAL_VALUATION_EQ_0) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [(← GSYM INT_OF_NUM_EQ)] THEN ASM_SIMP_TAC [] THEN ASM_INT_ARITH_TAC, REWRITE_TAC [SUBSET, NOT_FORALL_THM, NOT_IMP]] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:A") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"J:A->bool"), (← q r"x:B"), (← q r"c:A")] DEDEKIND_IDEAL_MUL_INTEGRAL) THEN ANTS_TAC THENL [ASM_SIMP_TAC [] THEN INT_ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [IN_IMAGE] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:A") STRIP_ASSUME_TAC) THEN MAP_EVERY EXISTS_TAC [(← q r"a:A"), (← q r"c:A")] THEN ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"~(b:A = ring_0 r)") ASSUME_TAC THENL [ASM_MESON_TAC [IN_RING_IDEAL_0, PRIME_IMP_RING_IDEAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(a:A = ring_0 r)") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"ring_mul k ((h:A->B) b) x = h (ring_0 r)") THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_0 th)])) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"b:A")] RING_MONOMORPHISM_EQ_0) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"b:A")] RING_HOMOMORPHISM_IN_CARRIER) THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_MUL_EQ_0, FIELD_IMP_INTEGRAL_DOMAIN], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"x:B"), (← q r"a:A"), (← q r"b:A")] DEDEKIND_VALUATION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"ideal_generated r {b:A}")] IDEAL_VALUATION_EQ_0) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0, IDEAL_GENERATED_MINIMAL_EQ, PRIME_IMP_RING_IDEAL, r1, SING_SUBSET] THEN DISCH_THEN SUBST1_TAC THEN INT_ARITH_TAC])

  let DEDEKIND_VALUATION_RING_LOCALIZATION ← prove
    r"!r k (h:A->B) P.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r})
        ==> ?g. ring_monomorphism
                 (ring_localization r (ring_carrier r DIFF P),k) g /\
                (!a. a IN ring_carrier r
                     ==> g(ring_fractionate r (ring_carrier r DIFF P) a) =
                         h a) /\
                IMAGE g (ring_carrier
                          (ring_localization r (ring_carrier r DIFF P))) =
                {x | x IN ring_carrier k /\
                     (x = ring_0 k \/ &0 <= dedekind_valuation (r,k) h P x)}"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN ABBREV_TAC (← q r"s = ring_carrier r DIFF (P:A->bool)") THEN SUBGOAL_THEN (← q r"ring_multsys r (s:A->bool)") ASSUME_TAC THENL [EXPAND_TAC "s" THEN ASM_SIMP_TAC [RING_MULTSYS_NONPRIME], ALL_TAC] THEN SUBGOAL_THEN (← q r"!b:A. b IN s <=> b IN ring_carrier r /\ ~(b IN P)") ASSUME_TAC THENL [EXPAND_TAC "s" THEN REWRITE_TAC [IN_DIFF], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:A->bool"), (← q r"k:B ring"), (← q r"h:A->B")] RING_LOCALIZATION_UNIVERSAL) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"b:A") THEN STRIP_TAC THEN ASM_SIMP_TAC [FIELD_UNIT] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, RING_MONOMORPHISM_EQ_0, IN_RING_IDEAL_0, PRIME_IMP_RING_IDEAL], MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"g:(A#A->bool)->B") THEN STRIP_TAC THEN ASM_REWRITE_TAC []] THEN SUBGOAL_THEN (← q r"!a b. a IN ring_carrier r /\ b IN s
          ==> g(ring_localequiv r s (a,b)) IN ring_carrier k /\
              ring_mul k ((h:A->B) b) (g(ring_localequiv r s (a,b))) = h a") ASSUME_TAC THENL [MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(b:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_localequiv r s (a:A,b) IN ring_carrier(ring_localization r s) /\
      ring_fractionate r s b IN ring_carrier(ring_localization r s)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_LOCALEQUIV_IN_CARRIER, RING_FRACTIONATE_IN_CARRIER], ALL_TAC] THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:A->bool"), (← q r"a:A"), (← q r"b:A")] LOCALEQUIV_MUL_RCANCEL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (AP_TERM (← q r"g:(A#A->bool)->B"))) THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL th)])), ALL_TAC] THEN CONJ_TAC THENL [ASM_REWRITE_TAC [RING_MONOMORPHISM_ALT] THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN ASM_SIMP_TAC [RING_LOCALIZATION_CARRIER, FORALL_IN_GSPEC] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"a:A = ring_0 r") SUBST1_TAC THENL [FIRST_X_ASSUM (MP_TAC o (SPECL [(← q r"a:A"), (← q r"b:A")])) THEN ASM_SIMP_TAC [RING_MUL_RZERO] THEN SUBGOAL_THEN (← q r"(h:A->B) b IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN ASM_SIMP_TAC [RING_MUL_RZERO] THEN ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0], ALL_TAC] THEN ASM_SIMP_TAC [RING_LOCALEQUIV_EQ_0_GEN, RING_0] THEN EXISTS_TAC (← q r"ring_1 r:A") THEN ASM_SIMP_TAC [RING_1, RING_MUL_RZERO] THEN ASM_MESON_TAC [PRIME_IMP_PROPER_IDEAL, PROPER_IDEAL], ALL_TAC] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [ASM_SIMP_TAC [SUBSET, FORALL_IN_IMAGE, RING_LOCALIZATION_CARRIER, FORALL_IN_GSPEC] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN FIRST_X_ASSUM (MP_TAC o (SPECL [(← q r"a:A"), (← q r"b:A")])) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"g(ring_localequiv r s (a:A,b)):B")] DEDEKIND_VALUATION_POS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"a:A"), (← q r"b:A")] THEN ASM_MESON_TAC [], REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"x:B")] DEDEKIND_VALUATION_POS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:A") (X_CHOOSE_THEN (← q r"b:A") STRIP_ASSUME_TAC)) THEN REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC (← q r"ring_localequiv r s (a:A,b)") THEN SUBGOAL_THEN (← q r"(b:A) IN s") ASSUME_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN CONJ_TAC THENL [FIRST_X_ASSUM (MP_TAC o (SPECL [(← q r"a:A"), (← q r"b:A")])) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN MAP_EVERY EXISTS_TAC [(← q r"k:B ring"), (← q r"(h:A->B) b")] THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, RING_MONOMORPHISM_EQ_0, IN_RING_IDEAL_0, PRIME_IMP_RING_IDEAL], ASM_SIMP_TAC [RING_LOCALIZATION_CARRIER] THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC []]])

  let DEDEKIND_VALUATION_LOCALIZATION ← prove
    r"!r k (h:A->B) g P x.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\
        ring_monomorphism(ring_localization r (ring_carrier r DIFF P),k) g /\
        (!a. a IN ring_carrier r
             ==> g(ring_fractionate r (ring_carrier r DIFF P) a) = h a) /\
        x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> dedekind_valuation
             (ring_localization r (ring_carrier r DIFF P),k) g
             {ring_localequiv r (ring_carrier r DIFF P) (a,b) | a,b |
              a IN P /\ b IN ring_carrier r DIFF P} x =
            dedekind_valuation (r,k) h P x"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"ring_multsys r (ring_carrier r DIFF P) /\
    ~(ring_0 r IN ring_carrier r DIFF P) /\
    ring_carrier r DIFF P SUBSET {a:A | ring_regular r a} /\
    P INTER (ring_carrier r DIFF P) = {} /\
    (P:A->bool) SUBSET ring_carrier r") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_MULTSYS_NONPRIME, IN_DIFF, IN_RING_IDEAL_0, SUBSET, IN_ELIM_THM, INTEGRAL_DOMAIN_REGULAR, PRIME_IDEAL_IMP_SUBSET] THEN CONJ_TAC THENL [ASM_MESON_TAC [IN_RING_IDEAL_0], SET_TAC []], ALL_TAC] THEN ABBREV_TAC (← q r"s = ring_carrier r DIFF (P:A->bool)") THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"x:B")] FIELD_FRACTION_NONZERO) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"x:B"), (← q r"a:A"), (← q r"b:A")] DEDEKIND_VALUATION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN SUBGOAL_THEN (← q r"!c:A. c IN ring_carrier r /\ ~(c = ring_0 r)
          ==> ring_fractionate r s c IN ring_carrier(ring_localization r s) /\
              ~(ring_fractionate r s c = ring_0(ring_localization r s)) /\
              ideal_generated (ring_localization r s)
                {ring_fractionate r s c} =
              {ring_localequiv r s (u,v) | u,v |
               u IN ideal_generated r {c} /\ v IN s}") ASSUME_TAC THENL [GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [RING_FRACTIONATE_IN_CARRIER] THEN CONJ_TAC THENL [ASM_SIMP_TAC [RING_FRACTIONATE_EQ_0_GEN, NOT_EXISTS_THM] THEN X_GEN_TAC (← q r"d:A") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(d:A) IN ring_carrier r /\ ~(d = ring_0 r)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_MULTSYS_IMP_SUBSET, SUBSET], ALL_TAC] THEN UNDISCH_TAC (← q r"ring_mul r d c = ring_0 r:A") THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_MUL_EQ_0], MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:A->bool"), (← q r"{c:A}")] IDEAL_GENERATED_RING_LOCALIZATION) THEN ASM_REWRITE_TAC [SING_SUBSET, IMAGE_CLAUSES]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_localization r (s:A->bool)"), (← q r"k:B ring"), (← q r"g:(A#A->bool)->B"), (← q r"{ring_localequiv r s (a,b) | a,b | a IN P /\ b IN (s:A->bool)}"), (← q r"x:B"), (← q r"ring_fractionate r s (a:A)"), (← q r"ring_fractionate r s (b:A)")] DEDEKIND_VALUATION) THEN ASM_SIMP_TAC [DEDEKIND_LOCALIZATION, PRIME_IDEAL_LOCALIZATION, IDEAL_LOCALIZATION_EQ_ZERO] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:A->bool"), (← q r"P:A->bool"), (← q r"ideal_generated r {b:A}")] IDEAL_VALUATION_LOCALIZATION) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:A->bool"), (← q r"P:A->bool"), (← q r"ideal_generated r {a:A}")] IDEAL_VALUATION_LOCALIZATION) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0] THEN REPEAT (DISCH_THEN SUBST1_TAC) THEN REFL_TAC)

  let ISOMORPHIC_RING_DVR ← prove
    r"!(r:A ring) (r':B ring). r isomorphic_ring r' ==> (DVR r <=> DVR r')"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [DVR] THEN ASM_MESON_TAC [ISOMORPHIC_RING_PIDNESS, ISOMORPHIC_RING_LOCALITY, ISOMORPHIC_RING_FIELDNESS])

  let DEDEKIND_VALUATION_RING_DVR ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"(p <=> q) ==> p ==> q")
    prove
      r"!r k (h:A->B) P.
          dedekind_domain r /\ field_of_fractions (r,k) h /\
          prime_ideal r P /\ ~(P = {ring_0 r})
          ==> DVR (subring_generated k
                    {x | x IN ring_carrier k /\
                         (x = ring_0 k \/
                          &0 <= dedekind_valuation (r,k) h P x)})"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool")] DEDEKIND_VALUATION_RING_LOCALIZATION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"g:(A#A->bool)->B") STRIP_ASSUME_TAC) THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"g:(A#A->bool)->B"), (← q r"ring_localization r (ring_carrier r DIFF P:A->bool)"), (← q r"k:B ring")] RING_ISOMORPHISM_ONTO_IMAGE) THEN ASM_REWRITE_TAC [ring_image] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool")] DVR_LOCALIZATION) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r1 THEN MATCH_MP_TAC ISOMORPHIC_RING_DVR THEN REWRITE_TAC [isomorphic_ring] THEN ASM_MESON_TAC [])

  let DVR_DEDEKIND_VALUATION ← prove
    r"!r k (h:A->B) m.
        DVR r /\ maximal_ideal r m /\ field_of_fractions (r,k) h
        ==> IMAGE h (ring_carrier r) =
            {x | x IN ring_carrier k /\
                 (x = ring_0 k \/ &0 <= dedekind_valuation (r,k) h m x)} /\
            IMAGE h {u | ring_unit r u} =
            {x | x IN ring_carrier k /\ ~(x = ring_0 k) /\
                 dedekind_valuation (r,k) h m x = &0}"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN FIRST_ASSUM (MP_TAC o (GEN_REWRITE_RULE id [DVR_IFF_LOCAL_DEDEKIND])) THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN SUBGOAL_THEN (← q r"!P. prime_ideal r P /\ ~(P = {ring_0 r}) <=> P = (m:A->bool)") ASSUME_TAC THENL [GEN_TAC THEN EQ_TAC THENL [STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (GEN_REWRITE_RULE id [local_ring])) THEN REWRITE_TAC [EXISTS_UNIQUE_DEF] THEN ASM_MESON_TAC [DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL], DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [MAXIMAL_IMP_PRIME_IDEAL] THEN ASM_MESON_TAC [MAXIMAL_IDEAL_0]], ALL_TAC] THEN SUBGOAL_THEN (← q r"prime_ideal r (m:A->bool) /\ ~(m = {ring_0 r})") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN CONJ_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"x:B") THEN REWRITE_TAC [IN_ELIM_THM] THENL [ASM_CASES_TAC (← q r"x:B = ring_0 k") THEN ASM_REWRITE_TAC [] THENL [REWRITE_TAC [RING_0, IN_IMAGE] THEN EXISTS_TAC (← q r"ring_0 r:A") THEN REWRITE_TAC [RING_0] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_0 th)])), ALL_TAC] THEN ASM_CASES_TAC (← q r"(x:B) IN ring_carrier k") THEN ASM_REWRITE_TAC [] THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"x:B")] DEDEKIND_VALUATION_INTEGRAL) THEN ASM_REWRITE_TAC [] THEN MESON_TAC [], REWRITE_TAC [IN_IMAGE] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER]], ASM_CASES_TAC (← q r"(x:B) IN ring_carrier k") THEN ASM_REWRITE_TAC [] THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"x:B")] DEDEKIND_VALUATION_UNIT) THEN ASM_REWRITE_TAC [] THEN MESON_TAC [], REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, RING_UNIT_IN_CARRIER]]])

  let DEDEKIND_UNIFORMIZER_CRITERION ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!s t z:A. t SUBSET s /\ s = {z} /\ z IN t ==> t = {z}")
    let r2 ← RING_RULE (← q r"ring_sub r (ring_add r y z) y = z:A")
    prove
      r"!r P (p:A).
          dedekind_domain r /\ prime_ideal r P /\ ~(P = {ring_0 r}) /\
          p IN P /\ ~(p IN ideal_pow r P 2)
          ==> (!n k a. a IN ideal_pow r P n
                       ==> ?b. b IN ring_carrier r /\
                               ring_sub r a (ring_mul r (ring_pow r p n) b) IN
                               ideal_pow r P (n + k)) /\
              (!n k b. b IN ring_carrier r /\
                       ring_mul r (ring_pow r p n) b IN ideal_pow r P (n + k)
                       ==> b IN ideal_pow r P k)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"(p:A) IN ring_carrier r /\ ~(p = ring_0 r)") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~(ring_0 r IN ideal_pow r (P:A->bool) 2)") THEN ASM_SIMP_TAC [IN_RING_IDEAL_0, RING_IDEAL_IDEAL_POW], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_valuation r P (ideal_generated r {p:A}) = 1") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"p:A"), (← q r"2:num")] DEDEKIND_IN_IDEAL_POW_VALUATION) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"p:A"), (← q r"1:num")] DEDEKIND_IN_IDEAL_POW_VALUATION) THEN ASM_SIMP_TAC [IDEAL_POW_1] THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"!n. ring_pow r (p:A) n IN ring_carrier r /\
          ~(ring_pow r p n = ring_0 r) /\
          ideal_valuation r P (ideal_generated r {ring_pow r p n}) = n") ASSUME_TAC THENL [GEN_TAC THEN ASM_SIMP_TAC [RING_POW, INTEGRAL_DOMAIN_POW_EQ_0] THEN ASM_SIMP_TAC [(← GSYM IDEAL_POW_PRINCIPAL), IDEAL_VALUATION_IDEAL_POW, RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0] THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"!m. ring_ideal r (ideal_pow r (P:A->bool) m) /\
          ~(ideal_pow r P m = {ring_0 r})") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, IDEAL_POW_EQ_ZERO], ALL_TAC] THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL [ALL_TAC, ASM_CASES_TAC (← q r"b = ring_0 (r:A ring)") THENL [ASM_SIMP_TAC [IN_RING_IDEAL_0], ALL_TAC] THEN UNDISCH_TAC (← q r"ring_mul r (ring_pow r p n) b IN ideal_pow r (P:A->bool) (n + k)") THEN ASM_SIMP_TAC [DEDEKIND_IN_IDEAL_POW_VALUATION, RING_MUL, INTEGRAL_DOMAIN_MUL_EQ_0, IDEAL_VALUATION_PRINCIPAL_MUL] THEN ARITH_TAC] THEN SUBGOAL_THEN (← q r"ideal_pow r P n SUBSET
      ring_setadd r (ideal_generated r {ring_pow r (p:A) n})
                    (ideal_pow r P (n + k))") MP_TAC THENL [ALL_TAC, REWRITE_TAC [SUBSET] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"a:A"))) THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [ring_setadd, IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"y:A"), (← q r"z:A")] THEN STRIP_TAC THEN UNDISCH_TAC (← q r"(y:A) IN ideal_generated r {ring_pow r p n}") THEN ASM_SIMP_TAC [IN_IDEAL_GENERATED_SING_EQ, ring_divides] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"b:A") STRIP_ASSUME_TAC)) THEN EXISTS_TAC (← q r"b:A") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(z:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [r2, RING_MUL]] THEN SUBGOAL_THEN (← q r"ideal_pow r P (n + k) SUBSET
      ring_setadd r (ideal_generated r {ring_pow r (p:A) n})
                    (ideal_pow r P (n + k))") ASSUME_TAC THENL [REWRITE_TAC [SUBSET, ring_setadd, IN_ELIM_THM] THEN X_GEN_TAC (← q r"z:A") THEN DISCH_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"ring_0 r:A"), (← q r"z:A")] THEN ASM_SIMP_TAC [IN_RING_IDEAL_0, RING_IDEAL_IDEAL_GENERATED] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_ADD_LZERO THEN ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_ideal r (ring_setadd r (ideal_generated r {ring_pow r (p:A) n})
                                 (ideal_pow r P (n + k))) /\
      ~(ring_setadd r (ideal_generated r {ring_pow r p n})
                      (ideal_pow r P (n + k)) = {ring_0 r})") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_SETADD, RING_IDEAL_IDEAL_GENERATED] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ideal_pow r P (n + k) = {ring_0 r:A}") MP_TAC THENL [MATCH_MP_TAC r1 THEN EXISTS_TAC (← q r"ring_setadd r (ideal_generated r {ring_pow r (p:A) n})
                        (ideal_pow r P (n + k))") THEN ASM_SIMP_TAC [IN_RING_IDEAL_0], ASM_REWRITE_TAC []], ALL_TAC] THEN ASM_SIMP_TAC [DEDEKIND_IDEAL_SUBSET_VALUATION] THEN X_GEN_TAC (← q r"q:A->bool") THEN STRIP_TAC THEN ASM_SIMP_TAC [IDEAL_VALUATION_SETADD, RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0, IDEAL_VALUATION_IDEAL_POW, IDEAL_VALUATION_PRIME, PRIME_IMP_RING_IDEAL] THEN ASM_CASES_TAC (← q r"P:A->bool = q") THENL [FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC [], ASM_REWRITE_TAC []] THEN REWRITE_TAC [MIN] THEN ARITH_TAC)

  -- @@RETURN BEGIN
  return { DEDEKIND_VALUATION_APPROXIMATION, DEDEKIND_DENOMINATOR_IDEAL,
           DEDEKIND_IDEAL_MUL_INTEGRAL, DEDEKIND_VALUATION_POS,
           DEDEKIND_VALUATION_RING_LOCALIZATION, DEDEKIND_VALUATION_LOCALIZATION,
           ISOMORPHIC_RING_DVR, DEDEKIND_VALUATION_RING_DVR, DVR_DEDEKIND_VALUATION,
           DEDEKIND_UNIFORMIZER_CRITERION }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- dedekind_valuation.ml phrases from line 1448 to 1448                   -/
/- ---------------------------------------------------------------------- -/

structure DedekindValuation03 where
  -- @@FIELDS
  FREE_BASIS_FRACTION_FIELD_MAP : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDedekindValuation03 [HolBase] (D : DedekindValuationDeps) :
    ExceptT String IO DedekindValuation03 := do
  -- @@SCOPE BEGIN
  let { RING_RULE, .. } := D
  let { CONJ_ASSOC, EQ_TRANS, FIELD_IMP_INTEGRAL_DOMAIN, FIELD_MUL_RINV,
        FINITE_NUMSEG_LT, FRACTION_FIELD_COMMON_DENOMINATOR, FRACTION_FIELD_MAP,
        IMP_CONJ, IMP_IMP, INTEGRAL_DOMAIN_MUL_EQ_0, INTEGRAL_DOMAIN_MUL_LCANCEL,
        IN_ELIM_THM, .. } := D.core1
  let { RIGHT_IMP_EXISTS_THM, RING_0, RING_HOMOMORPHISM_0,
        RING_HOMOMORPHISM_IN_CARRIER, RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_SUM_MUL,
        RING_INV, RING_MONOMORPHISM_COMPOSE, RING_MONOMORPHISM_EQ_0,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL, RING_MUL_RZERO, RING_SUM,
        RING_SUM_EQ, RING_SUM_LMUL, SKOLEM_THM, field_of_fractions, free_basis, o_THM, .. } := D.core2
  -- @@SCOPE END

  let FREE_BASIS_FRACTION_FIELD_MAP ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul (l:D ring) p q = m
        ==> ring_mul l m w = ring_mul l p (ring_mul l q w)")
    let r2 ← RING_RULE (← q r"ring_mul (k:C ring) x z = ring_1 k
        ==> ring_mul k x (ring_mul k y z) = y")
    let r3 ← RING_RULE (← q r"ring_mul (l:D ring) p q = m
      ==> ring_mul l m w = ring_mul l p (ring_mul l q w)")
    let r8 ← RING_RULE (← q r"ring_mul (l:D ring) p x = q
          ==> ring_mul l (ring_mul l p w) x = ring_mul l q w")
    prove
      r"!r s (h:A->B) n b k (u:A->C) l (v:B->D).
          ring_monomorphism(r,s) h /\ free_basis (r,s) h n b /\
          field_of_fractions (r,k) u /\ field_of_fractions (s,l) v /\
          (!d. d IN ring_carrier s /\ ~(d = ring_0 s)
               ==> ?c z. c IN ring_carrier r /\ ~(c = ring_0 r) /\
                         z IN ring_carrier s /\ ring_mul s d z = h c)
          ==> ring_monomorphism(k,l) (fraction_field_map (r,k) u l (v o h)) /\
              (!a. a IN ring_carrier r
                   ==> fraction_field_map (r,k) u l (v o h) (u a) = v(h a)) /\
              free_basis (k,l) (fraction_field_map (r,k) u l (v o h)) n
                         (v o b)"
      (REWRITE_TAC [field_of_fractions, (← GSYM CONJ_ASSOC)] THEN REPEAT GEN_TAC THEN REPLICATE_TAC 4 (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "kfrac") MP_TAC) THEN REPLICATE_TAC 2 (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "lfrac") (LABEL_TAC "div")) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:C ring"), (← q r"u:A->C"), (← q r"l:D ring"), (← q r"(v:B->D) o (h:A->B)")] FRACTION_FIELD_MAP) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [field_of_fractions] THEN MATCH_MP_TAC RING_MONOMORPHISM_COMPOSE THEN EXISTS_TAC (← q r"s:B ring") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"H = fraction_field_map (r,k) (u:A->C) l ((v:B->D) o (h:A->B))") THEN REWRITE_TAC [o_THM] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Hu")) THEN ASM_REWRITE_TAC [] THEN MAP_EVERY (fun t => tactic_of do pure (ASSUME_TAC (← MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM (← ASSUME t)))) [(← q r"ring_monomorphism(r,s) (h:A->B)"), (← q r"ring_monomorphism(r,k) (u:A->C)"), (← q r"ring_monomorphism(s,l) (v:B->D)"), (← q r"ring_monomorphism(k,l) (H:C->D)")] THEN MAP_EVERY (fun t => tactic_of do pure ((← do let th ← (do pure (← ASSUME t)); pure (MAP_EVERY (ASSUME_TAC o (← do let c := th; pure (fun th => MATCH_MP th c))) [RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_MUL, (← REWRITE_RULE [IMP_CONJ] RING_HOMOMORPHISM_IN_CARRIER)])))) [(← q r"ring_homomorphism(r,s) (h:A->B)"), (← q r"ring_homomorphism(r,k) (u:A->C)"), (← q r"ring_homomorphism(s,l) (v:B->D)"), (← q r"ring_homomorphism(k,l) (H:C->D)")] THEN MAP_EVERY (fun t => tactic_of do pure (ASSUME_TAC (← MATCH_MP (← REWRITE_RULE [IMP_CONJ] RING_MONOMORPHISM_EQ_0) (← ASSUME t)))) [(← q r"ring_monomorphism(r,s) (h:A->B)"), (← q r"ring_monomorphism(r,k) (u:A->C)"), (← q r"ring_monomorphism(s,l) (v:B->D)")] THEN MAP_EVERY (fun t => tactic_of do pure (ASSUME_TAC (← MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN (← ASSUME t)))) [(← q r"field(k:C ring)"), (← q r"field(l:D ring)")] THEN MP_TAC (← ASSUME (← q r"free_basis (r,s) (h:A->B) n b")) THEN REWRITE_TAC [free_basis] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "bspan") (LABEL_TAC "bind"))) THEN REWRITE_TAC [free_basis, o_THM] THEN REPEAT CONJ_TAC THENL [ASM_SIMP_TAC [], X_GEN_TAC (← q r"x:D") THEN DISCH_TAC THEN USE_THEN "lfrac" (MP_TAC o (← do let c := (← ASSUME (← q r"(x:D) IN ring_carrier l")); pure (fun th => MATCH_MP th c))) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"y:B") (X_CHOOSE_THEN (← q r"d:B") STRIP_ASSUME_TAC)) THEN USE_THEN "div" (MP_TAC o (← do let c := (← CONJ (← ASSUME (← q r"(d:B) IN ring_carrier s")) (← ASSUME (← q r"~((d:B) = ring_0 s)"))); pure (fun th => MATCH_MP th c))) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:A") (X_CHOOSE_THEN (← q r"z:B") STRIP_ASSUME_TAC)) THEN USE_THEN "bspan" (MP_TAC o (SPEC (← q r"ring_mul s y z:B"))) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_MUL], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:num->A") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(u:A->C) c IN ring_carrier k /\ ~(u c = ring_0 k)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_inv k ((u:A->C) c) IN ring_carrier k /\
        (H:C->D)(ring_inv k (u c)) IN ring_carrier l /\
        !i. i < n
            ==> (h:A->B)((a:num->A) i) IN ring_carrier s /\
                (v:B->D)(h(a i)) IN ring_carrier l /\
                ring_mul k (u(a i)) (ring_inv k (u c)) IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_INV, RING_MUL], ALL_TAC] THEN EXISTS_TAC (← q r"\i. ring_mul k ((u:A->C)((a:num->A) i)) (ring_inv k (u(c:A)))") THEN REWRITE_TAC [] THEN CONJ_TAC THENL [ASM_SIMP_TAC [RING_MUL, RING_INV], ALL_TAC] THEN MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN MAP_EVERY EXISTS_TAC [(← q r"l:D ring"), (← q r"(v:B->D)((h:A->B) c)")] THEN REPEAT CONJ_TAC THENL [ASM_REWRITE_TAC [], ASM_SIMP_TAC [], ASM_SIMP_TAC [], ASM_REWRITE_TAC [], REWRITE_TAC [RING_SUM], ALL_TAC] THEN TRANS_TAC EQ_TRANS (← q r"(v:B->D)(ring_mul s y z)") THEN CONJ_TAC THENL [SUBGOAL_THEN (← q r"(v:B->D)((h:A->B) c) = ring_mul l (v d) (v z) /\
          v(ring_mul s y z) = ring_mul l (v y) (v z)") (fun th => REWRITE_TAC [th]) THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z12 ← (q r"(h:A->B) c"); let z11 ← (do let z9 ← (do let z10 ← (pure th); pure (concl z10)); liftExcept (rhs z9)); pure (z11 == z12)))))) THEN ASM_SIMP_TAC [], UNDISCH_TAC (← q r"ring_mul l ((v:B->D) d) x = v y") THEN MATCH_MP_TAC r8 THEN ASM_SIMP_TAC []], ALL_TAC] THEN FIRST_X_ASSUM (SUBST1_TAC o (checkM (fun th => (do let z7 ← (q r"ring_mul s (y:B) z"); let z6 ← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); liftExcept (lhs z4)); pure (z6 == z7))))) THEN MP_TAC (← BETA_RULE (← ISPECL [(← q r"s:B ring"), (← q r"l:D ring"), (← q r"v:B->D"), (← q r"{i:num | i < n}"), (← q r"\i. (h:A->B)((a:num->A) i)"), (← q r"b:num->B")] RING_HOMOMORPHISM_SUM_MUL)) THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM], DISCH_THEN SUBST1_TAC] THEN wPart rand (rand o rand) RING_SUM_LMUL THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, RING_MUL, RING_INV], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"i:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [IMP_IMP] r3) THEN CONJ_TAC THENL [ASM_SIMP_TAC [RING_MUL, RING_INV], ALL_TAC] THEN TRANS_TAC EQ_TRANS (← q r"(H:C->D)(ring_mul k (u(c:A))
                  (ring_mul k (u((a:num->A) i)) (ring_inv k (u c))))") THEN CONJ_TAC THENL [ASM_SIMP_TAC [RING_MUL, RING_INV], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul k ((u:A->C) c)
          (ring_mul k (u((a:num->A) i)) (ring_inv k (u c))) = u(a i)") SUBST1_TAC THENL [MP_TAC (← ISPECL [(← q r"k:C ring"), (← q r"(u:A->C) c")] FIELD_MUL_RINV) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r2 THEN ASM_SIMP_TAC [RING_INV], ASM_SIMP_TAC []], X_GEN_TAC (← q r"q:num->C") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:C ring"), (← q r"u:A->C"), (← q r"q:num->C"), (← q r"{i:num | i < n}")] FRACTION_FIELD_COMMON_DENOMINATOR) THEN ASM_REWRITE_TAC [field_of_fractions, FINITE_NUMSEG_LT, IN_ELIM_THM] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:A") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:num->A") (LABEL_TAC "a")) THEN USE_THEN "bind" (MP_TAC o (SPEC (← q r"a:num->A"))) THEN ANTS_TAC THENL [CONJ_TAC THENL [USE_THEN "a" (fun th => SIMP_TAC [th]), ALL_TAC] THEN SUBGOAL_THEN (← q r"(v:B->D)(ring_sum s {i | i < n}
                    (\i. ring_mul s ((h:A->B)((a:num->A) i)) (b i))) =
          ring_0 l") MP_TAC THENL [ALL_TAC, ASM_SIMP_TAC [RING_SUM]] THEN MP_TAC (← BETA_RULE (← ISPECL [(← q r"s:B ring"), (← q r"l:D ring"), (← q r"v:B->D"), (← q r"{i:num | i < n}"), (← q r"\i. (h:A->B)((a:num->A) i)"), (← q r"b:num->B")] RING_HOMOMORPHISM_SUM_MUL)) THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM], DISCH_THEN SUBST1_TAC] THEN TRANS_TAC EQ_TRANS (← q r"ring_mul l ((H:C->D)(u(c:A)))
            (ring_sum l {i | i < n}
               (\i. ring_mul l (H((q:num->C) i)) (v((b:num->B) i))))") THEN CONJ_TAC THENL [ALL_TAC, ASM_REWRITE_TAC [] THEN MATCH_MP_TAC RING_MUL_RZERO THEN ASM_SIMP_TAC []] THEN wPart rand (rand o rand) RING_SUM_LMUL THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, RING_MUL], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"i:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [IMP_IMP] r1) THEN CONJ_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN TRANS_TAC EQ_TRANS (← q r"(H:C->D)(ring_mul k (u(c:A)) ((q:num->C) i))") THEN CONJ_TAC THENL [CONV_TAC SYM_CONV THEN ASM_SIMP_TAC [], ALL_TAC] THEN USE_THEN "a" (fun th => tactic_of do pure (REWRITE_TAC [(← CONJUNCT2 (← MATCH_MP th (← ASSUME (← q r"i:num < n"))))])) THEN USE_THEN "Hu" MATCH_MP_TAC THEN USE_THEN "a" (fun th => tactic_of do pure (REWRITE_TAC [(← CONJUNCT1 (← MATCH_MP th (← ASSUME (← q r"i:num < n"))))])), ALL_TAC] THEN DISCH_THEN (LABEL_TAC "a0") THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN REMOVE_THEN "a" (MP_TAC o (← do let c := (← ASSUME (← q r"i:num < n")); pure (fun th => MATCH_MP th c))) THEN REMOVE_THEN "a0" (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP th (← ASSUME (← q r"i:num < n")))])) THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_MUL_EQ_0, RING_0]])

  -- @@RETURN BEGIN
  return { FREE_BASIS_FRACTION_FIELD_MAP }
  -- @@RETURN END

end HolANT.DedekindValuation
