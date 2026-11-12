/- ========================================================================= -/
/- ANT: Further structure of Dedekind domains                              -/
/- ========================================================================= -/
/- File: HolANT/DedekindStruct.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/dedekind_struct.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antdedekindstructdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/permutations.ml, Library/ring_det.ml, ANT/ideal_arith.ml, Library/products.ml, ANT/algmisc.ml, Library/matroids.ml, Library/fieldtheory.ml, ANT/integral.ml, ANT/dedekind.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.DedekindStruct fills them).

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

namespace HolANT.DedekindStruct

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (CHINESE_REMAINDER_IDEALS COMAXIMAL_IDEAL_POW CONJ_ASSOC
   DEDEKIND_IDEAL_EQ_VALUATION DEDEKIND_IDEAL_FACTORIZATION
   DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE DEDEKIND_IDEAL_POW_SUBSET
   DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES DEDEKIND_IDEAL_SUBSET_VALUATION
   DEDEKIND_IMP_INTEGRAL_DOMAIN DEDEKIND_KRULL_DIMENSION_ONE
   DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL EMPTY_SUBSET EXISTS_UNIQUE_DEF
   EXISTS_UNIQUE_THM EXTENSION FIELD_EQ_TRIVIAL_IDEALS FINITE_UNION
   IDEAL_GENERATED_0 IDEAL_GENERATED_BY_EPIMORPHIC_IMAGE IDEAL_GENERATED_EQ_0
   IDEAL_GENERATED_INC_GEN IDEAL_GENERATED_INSERT_ZERO IDEAL_GENERATED_MINIMAL
   IDEAL_GENERATED_MINIMAL_EQ IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0
   IDEAL_GENERATED_RING_IDEAL IDEAL_GENERATED_SUBSET IDEAL_GENERATED_UNION
   IDEAL_POW_0 IDEAL_POW_1 IDEAL_POW_ANTIMONO IDEAL_POW_EQ_ZERO
   IDEAL_POW_PRINCIPAL IDEAL_POW_SUBSET_PRIME_IDEAL IDEAL_PROD_AC
   IDEAL_PROD_CARRIER IDEAL_PROD_EPIMORPHIC_IMAGE IDEAL_PROD_EQ_ZERO
   IDEAL_PROD_PRINCIPAL IDEAL_PROD_PRINCIPAL_CANCEL IDEAL_PROD_RZERO
   IDEAL_PROD_SCALE IDEAL_VALUATION_EQ_0 IDEAL_VALUATION_FINITE_SUPPORT
   IDEAL_VALUATION_IDEAL_POW IDEAL_VALUATION_IDEAL_PROD IDEAL_VALUATION_PRIME
   IDEAL_VALUATION_SETADD IDEAL_VALUATION_UNIQUE IMAGE_CLAUSES INSERT_INSERT
   INSERT_SUBSET INTEGRAL_DOMAIN_MUL_EQ_0 IN_ELIM_THM IN_IDEAL_GENERATED_SELF
   IN_IMAGE IN_INSERT IN_RING_IDEAL_0 IN_RING_IDEAL_ADD IN_RING_IDEAL_SUB
   IN_SING IN_UNION LEFT_IMP_EXISTS_THM LE_0 LE_CASES LE_REFL MAXIMAL_IDEAL_0
   MAXIMAL_IDEAL_COMAXIMAL MAXIMAL_IDEAL_CORRESPONDENCE MAXIMAL_IDEAL_EXISTS
   MAXIMAL_IDEAL_IMP_SUBSET MAXIMAL_IMP_PRIME_IDEAL MAXIMAL_IMP_PROPER_IDEAL
   MAXIMAL_IMP_RING_IDEAL MAXIMAL_SUPERIDEAL_EXISTS MEMBER_NOT_EMPTY MONO_EXISTS
   NOT_EXISTS_THM NOT_IN_EMPTY PID PID_EQ_NOETHERIAN_BEZOUT_DOMAIN
   PID_EQ_UFD_PRIME_MAXIMAL PID_IMP_DEDEKIND PRIME_IMP_PROPER_IDEAL
   PRIME_IMP_RING_IDEAL PRINCIPAL_IDEAL_0 PRINCIPAL_IDEAL_CARRIER
   PRINCIPAL_IDEAL_IDEAL_GENERATED_SING PROPER_IDEAL PROPER_IDEAL_ALT PSUBSET
   QUOTIENT_RING_0 QUOTIENT_RING_IDEAL_CORRESPONDENCE RIGHT_EXISTS_IMP_THM
   RING_0 RING_1 RING_COSET_EQ_IDEAL RING_EPIMORPHISM_RING_COSET
   RING_HOMOMORPHISM_IN_CARRIER RING_IDEAL_CARRIER RING_IDEAL_EPIMORPHIC_IMAGE
   RING_IDEAL_IDEAL_GENERATED RING_IDEAL_IDEAL_POW RING_IDEAL_IDEAL_PROD
   RING_IDEAL_IMP_SUBSET RING_IDEAL_SETADD RING_ISOMORPHISM_IMP_EPIMORPHISM
   RING_ISOMORPHISM_IMP_MONOMORPHISM RING_MONOMORPHISM_EQ_0
   RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_MUL RING_MUL_LID RING_POW
   RING_SETADD_SUPERSET_LEFT RING_SETADD_SUPERSET_RIGHT SING_SUBSET SKOLEM_THM
   SUBSET SUBSET_ANTISYM SUBSET_REFL SUBSET_TRANS TRIVIAL_QUOTIENT_RING
   TRIVIAL_RING_10 dedekind_domain integral_domain local_ring maximal_ideal
   pairwise principal_ideal proper_ideal trivial_ring : thm)
  deriving Inhabited

/-- What dedekind_struct.ml uses from Session besides theorems. -/
structure DedekindStructDeps where
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
/- dedekind_struct.ml phrases from line 37 to 643                         -/
/- ---------------------------------------------------------------------- -/

structure DedekindStruct where
  -- @@FIELDS
  DVR : thm
  DVR_IMP_DEDEKIND : thm
  DEDEKIND_LOCAL_IDEAL_MAXIMAL_POW : thm
  DVR_IFF_LOCAL_DEDEKIND : thm
  DVR_IDEAL_MAXIMAL_POW : thm
  DVR_IDEALS_TOTALLY_ORDERED : thm
  DEDEKIND_WEAK_APPROXIMATION : thm
  DEDEKIND_IDEAL_WEAK_APPROXIMATION : thm
  DEDEKIND_TWO_GENERATORS_STRONG : thm
  DEDEKIND_TWO_GENERATORS : thm
  DEDEKIND_QUOTIENT_PRINCIPAL : thm
  DEDEKIND_LOCAL_QUOTIENT_PRIME_POW : thm
  DEDEKIND_UFD_IFF_PID : thm
  DEDEKIND_BEZOUT_IFF_PID : thm
  ideal_class : thm
  IN_IDEAL_CLASS : thm
  IDEAL_CLASS_REFL : thm
  IDEAL_CLASS_SYM : thm
  IDEAL_CLASS_TRANS : thm
  IDEAL_CLASS_MUL : thm
  IN_IDEAL_CLASS_ISOMORPHIC_IMAGE : thm
  IDEAL_CLASS_PRINCIPAL : thm
  PRINCIPAL_IDEAL_CLASS : thm
  DEDEKIND_IDEAL_CLASS_INVERSE : thm
  DEDEKIND_PID_IFF_TRIVIAL_CLASS_GROUP : thm
  DEDEKIND_IDEAL_CLASS_COPRIME : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDedekindStruct [HolBase] (D : DedekindStructDeps) :
    ExceptT String IO DedekindStruct := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC,
        NUM_REDUCE_CONV, RING_RULE, SET_RULE, SET_TAC, TAUT, new_definition, .. } := D
  let { CHINESE_REMAINDER_IDEALS, COMAXIMAL_IDEAL_POW, CONJ_ASSOC,
        DEDEKIND_IDEAL_EQ_VALUATION, DEDEKIND_IDEAL_FACTORIZATION,
        DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE, DEDEKIND_IDEAL_POW_SUBSET,
        DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES, DEDEKIND_IDEAL_SUBSET_VALUATION,
        DEDEKIND_IMP_INTEGRAL_DOMAIN, DEDEKIND_KRULL_DIMENSION_ONE,
        DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL, EMPTY_SUBSET, EXISTS_UNIQUE_DEF,
        EXISTS_UNIQUE_THM, EXTENSION, FIELD_EQ_TRIVIAL_IDEALS, FINITE_UNION,
        IDEAL_GENERATED_0, IDEAL_GENERATED_BY_EPIMORPHIC_IMAGE, IDEAL_GENERATED_EQ_0,
        IDEAL_GENERATED_INC_GEN, IDEAL_GENERATED_INSERT_ZERO, IDEAL_GENERATED_MINIMAL,
        IDEAL_GENERATED_MINIMAL_EQ, IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0,
        IDEAL_GENERATED_RING_IDEAL, IDEAL_GENERATED_SUBSET, IDEAL_GENERATED_UNION,
        IDEAL_POW_0, IDEAL_POW_1, IDEAL_POW_ANTIMONO, IDEAL_POW_EQ_ZERO,
        IDEAL_POW_PRINCIPAL, IDEAL_POW_SUBSET_PRIME_IDEAL, IDEAL_PROD_AC,
        IDEAL_PROD_CARRIER, IDEAL_PROD_EPIMORPHIC_IMAGE, IDEAL_PROD_EQ_ZERO,
        IDEAL_PROD_PRINCIPAL, IDEAL_PROD_PRINCIPAL_CANCEL, IDEAL_PROD_RZERO,
        IDEAL_PROD_SCALE, IDEAL_VALUATION_EQ_0, IDEAL_VALUATION_FINITE_SUPPORT,
        IDEAL_VALUATION_IDEAL_POW, IDEAL_VALUATION_IDEAL_PROD, IDEAL_VALUATION_PRIME,
        IDEAL_VALUATION_SETADD, IDEAL_VALUATION_UNIQUE, IMAGE_CLAUSES, INSERT_INSERT,
        INSERT_SUBSET, INTEGRAL_DOMAIN_MUL_EQ_0, IN_ELIM_THM, IN_IDEAL_GENERATED_SELF,
        IN_IMAGE, IN_INSERT, IN_RING_IDEAL_0, IN_RING_IDEAL_ADD, IN_RING_IDEAL_SUB,
        IN_SING, IN_UNION, LEFT_IMP_EXISTS_THM, LE_0, LE_CASES, LE_REFL,
        MAXIMAL_IDEAL_0, MAXIMAL_IDEAL_COMAXIMAL, MAXIMAL_IDEAL_CORRESPONDENCE,
        MAXIMAL_IDEAL_EXISTS, MAXIMAL_IDEAL_IMP_SUBSET, MAXIMAL_IMP_PRIME_IDEAL,
        MAXIMAL_IMP_PROPER_IDEAL, MAXIMAL_IMP_RING_IDEAL, MAXIMAL_SUPERIDEAL_EXISTS,
        MEMBER_NOT_EMPTY, MONO_EXISTS, NOT_EXISTS_THM, NOT_IN_EMPTY, PID,
        PID_EQ_NOETHERIAN_BEZOUT_DOMAIN, PID_EQ_UFD_PRIME_MAXIMAL, PID_IMP_DEDEKIND,
        PRIME_IMP_PROPER_IDEAL, PRIME_IMP_RING_IDEAL, PRINCIPAL_IDEAL_0,
        PRINCIPAL_IDEAL_CARRIER, PRINCIPAL_IDEAL_IDEAL_GENERATED_SING, PROPER_IDEAL,
        PROPER_IDEAL_ALT, PSUBSET, QUOTIENT_RING_0, QUOTIENT_RING_IDEAL_CORRESPONDENCE,
        RIGHT_EXISTS_IMP_THM, RING_0, RING_1, RING_COSET_EQ_IDEAL,
        RING_EPIMORPHISM_RING_COSET, RING_HOMOMORPHISM_IN_CARRIER, RING_IDEAL_CARRIER,
        RING_IDEAL_EPIMORPHIC_IMAGE, RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_POW,
        RING_IDEAL_IDEAL_PROD, RING_IDEAL_IMP_SUBSET, RING_IDEAL_SETADD,
        RING_ISOMORPHISM_IMP_EPIMORPHISM, RING_ISOMORPHISM_IMP_MONOMORPHISM,
        RING_MONOMORPHISM_EQ_0, RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL,
        RING_MUL_LID, RING_POW, RING_SETADD_SUPERSET_LEFT, RING_SETADD_SUPERSET_RIGHT,
        SING_SUBSET, SKOLEM_THM, SUBSET, SUBSET_ANTISYM, SUBSET_REFL, SUBSET_TRANS,
        TRIVIAL_QUOTIENT_RING, TRIVIAL_RING_10, dedekind_domain, integral_domain,
        local_ring, maximal_ideal, pairwise, principal_ideal, proper_ideal,
        trivial_ring, .. } := D.core1
  -- @@SCOPE END

  let DVR ← new_definition
    r"DVR (r:A ring) <=> PID r /\ local_ring r /\ ~(field r)"

  let DVR_IMP_DEDEKIND ← prove
    r"!r:A ring. DVR r ==> dedekind_domain r"
    (SIMP_TAC [DVR, PID_IMP_DEDEKIND])

  let DEDEKIND_LOCAL_IDEAL_MAXIMAL_POW ← prove
    r"!r m j:A->bool.
        dedekind_domain r /\ local_ring r /\ maximal_ideal r m /\
        ring_ideal r j /\ ~(j = {ring_0 r})
        ==> ?n. j = ideal_pow r m n"
    (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"m = {ring_0 r:A}") THENL [EXISTS_TAC (← q r"0") THEN REWRITE_TAC [IDEAL_POW_0] THEN ASM_MESON_TAC [MAXIMAL_IDEAL_0, FIELD_EQ_TRIVIAL_IDEALS], EXISTS_TAC (← q r"ideal_valuation r m (j:A->bool)")] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_PRIME_IDEAL)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"ideal_pow r m (ideal_valuation r m (j:A->bool))")] DEDEKIND_IDEAL_EQ_VALUATION) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, IDEAL_POW_EQ_ZERO, DEDEKIND_IMP_INTEGRAL_DOMAIN] THEN DISCH_THEN SUBST1_TAC THEN X_GEN_TAC (← q r"p:A->bool") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"p:A->bool = m") SUBST1_TAC THENL [FIRST_X_ASSUM (MP_TAC o (GEN_REWRITE_RULE id [local_ring])) THEN REWRITE_TAC [EXISTS_UNIQUE_DEF] THEN ASM_MESON_TAC [DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL], ASM_SIMP_TAC [IDEAL_VALUATION_IDEAL_POW, IDEAL_VALUATION_PRIME] THEN ARITH_TAC])

  let DVR_IFF_LOCAL_DEDEKIND ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(t:A) IN s ==> (s INTER {t} SUBSET u <=> t IN u)")
    prove
      r"!r:A ring. DVR r <=> dedekind_domain r /\ local_ring r /\ ~(field r)"
      (GEN_TAC THEN EQ_TAC THENL [SIMP_TAC [DVR, PID_IMP_DEDEKIND], STRIP_TAC] THEN ASM_SIMP_TAC [DVR, PID, DEDEKIND_IMP_INTEGRAL_DOMAIN] THEN FIRST_ASSUM (MP_TAC o (GEN_REWRITE_RULE id [local_ring])) THEN REWRITE_TAC [EXISTS_UNIQUE_DEF] THEN DISCH_THEN ((X_CHOOSE_TAC (← q r"m:A->bool")) o CONJUNCT1) THEN SUBGOAL_THEN (← q r"ring_ideal r (m:A->bool) /\ ~(m = {ring_0 r}) /\
                  ~(m = ring_carrier r)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [MAXIMAL_IDEAL_0, MAXIMAL_IMP_PROPER_IDEAL, PROPER_IDEAL_ALT], ALL_TAC] THEN SUBGOAL_THEN (← q r"?t:A. t IN m /\ ~(t IN ideal_pow r m 2)") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"1"), (← q r"2")] DEDEKIND_IDEAL_POW_SUBSET) THEN ASM_SIMP_TAC [IDEAL_POW_1] THEN CONV_TAC NUM_REDUCE_CONV THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(t:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_generated r {t:A} = m") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"ideal_generated r {t:A} SUBSET m /\
        ~(ideal_generated r {t} SUBSET ideal_pow r m 2) /\
        ~(ideal_generated r {t} = {ring_0 r})") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [IDEAL_GENERATED_MINIMAL_EQ, RING_IDEAL_IDEAL_POW, IDEAL_GENERATED_EQ_0, r1] THEN DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~(ring_0 r IN ideal_pow r (m:A->bool) 2)") THEN ASM_SIMP_TAC [IN_RING_IDEAL_0, RING_IDEAL_IDEAL_POW], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"ideal_generated r {t:A}")] DEDEKIND_LOCAL_IDEAL_MAXIMAL_POW) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"v:num") SUBST_ALL_TAC) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"v:num"), (← q r"1")] DEDEKIND_IDEAL_POW_SUBSET) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"v:num"), (← q r"2")] DEDEKIND_IDEAL_POW_SUBSET) THEN ASM_SIMP_TAC [IDEAL_POW_1] THEN REPEAT DISCH_TAC THEN SUBGOAL_THEN (← q r"v = 1") (fun th => ASM_SIMP_TAC [th, IDEAL_POW_1]) THEN ASM_ARITH_TAC, ALL_TAC] THEN X_GEN_TAC (← q r"j:A->bool") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"j = {ring_0 r:A}") THEN ASM_REWRITE_TAC [PRINCIPAL_IDEAL_0] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"j:A->bool")] DEDEKIND_LOCAL_IDEAL_MAXIMAL_POW) THEN ASM_REWRITE_TAC [principal_ideal] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"n:num") SUBST1_TAC) THEN EXISTS_TAC (← q r"ring_pow r (t:A) n") THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [RING_POW, IDEAL_POW_PRINCIPAL])

  let DVR_IDEAL_MAXIMAL_POW ← prove
    r"!r m j:A->bool.
        DVR r /\ maximal_ideal r m /\ ring_ideal r j /\ ~(j = {ring_0 r})
        ==> ?n. j = ideal_pow r m n"
    (REWRITE_TAC [DVR_IFF_LOCAL_DEDEKIND] THEN MESON_TAC [DEDEKIND_LOCAL_IDEAL_MAXIMAL_POW])

  let DVR_IDEALS_TOTALLY_ORDERED ← prove
    r"!r j k:A->bool.
        DVR r /\ ring_ideal r j /\ ring_ideal r k
        ==> j SUBSET k \/ k SUBSET j"
    (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"j = {ring_0 r:A}") THENL [ASM_SIMP_TAC [SING_SUBSET, IN_RING_IDEAL_0], ALL_TAC] THEN ASM_CASES_TAC (← q r"k = {ring_0 r:A}") THENL [ASM_SIMP_TAC [SING_SUBSET, IN_RING_IDEAL_0], ALL_TAC] THEN FIRST_ASSUM (MP_TAC o (CONJUNCT1 o (CONJUNCT2 o (GEN_REWRITE_RULE id [DVR])))) THEN REWRITE_TAC [local_ring, EXISTS_UNIQUE_DEF] THEN DISCH_THEN ((X_CHOOSE_TAC (← q r"m:A->bool")) o CONJUNCT1) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"k:A->bool")] DVR_IDEAL_MAXIMAL_POW) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"j:A->bool")] DVR_IDEAL_MAXIMAL_POW) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"a:num") THEN DISCH_THEN SUBST1_TAC THEN X_GEN_TAC (← q r"b:num") THEN DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC [IDEAL_POW_ANTIMONO, LE_CASES, MAXIMAL_IDEAL_IMP_SUBSET])

  let DEDEKIND_WEAK_APPROXIMATION ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"ring_sub r y (ring_sub r y u) = (u:A)"
    let r2 ← RING_RULE q1
    let q3 ← q r"u = ring_sub r y (ring_sub r y u:A)"
    let q4 ← q r"~((u:A) IN k)"
    let q5 ← q r"ring_add r (ring_sub r y u) u = (y:A)"
    let r6 ← RING_RULE q5
    let q7 ← q r"y = ring_add r (ring_sub r y u) (u:A)"
    let q8 ← q r"(u:A) IN ring_carrier r"
    let p9 ← prove r"!r i k u y:A.
        ring_ideal r i /\ ring_ideal r k /\ k SUBSET i /\
        u IN i /\ ~(u IN k) /\ y IN ring_carrier r /\ ring_sub r y u IN k
        ==> y IN i /\ ~(y IN k)" (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN q8 ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], CONJ_TAC] THENL [SUBGOAL_THEN q7 SUBST1_TAC THENL [ASM_SIMP_TAC [r6], ASM_MESON_TAC [IN_RING_IDEAL_ADD, SUBSET]], DISCH_TAC THEN UNDISCH_TAC q4 THEN REWRITE_TAC [] THEN SUBGOAL_THEN q3 SUBST1_TAC THENL [ASM_SIMP_TAC [r2], ASM_SIMP_TAC [IN_RING_IDEAL_SUB]]])
    let lemma := p9
    let q10 ← q r"(y:A) IN s ==> (s INTER {y} SUBSET u <=> y IN u)"
    let r11 ← SET_RULE q10
    let q12 ← q r"p:A->bool"
    let v13 ← GSYM MEMBER_NOT_EMPTY
    let q14 ← q r"y:A"
    let q15 ← q r"n <= SUC n"
    let r16 ← ARITH_RULE q15
    let q17 ← q r"(x:(A->bool)->A) p"
    let q18 ← q r"r:A ring"
    let v19 ← ISPEC q18 lemma
    let q20 ← q r"p:A->bool"
    let q21 ← q r"!p:A->bool. p IN s
                ==> y IN ideal_pow r p (n p) /\
                    ~(y IN ideal_pow r p (SUC(n p)))"
    let q22 ← q r"y:A"
    let q23 ← q r"q:A->bool"
    let q24 ← q r"p:A->bool"
    let q25 ← q r"x:(A->bool)->A"
    let q26 ← q r"\p:A->bool. ideal_pow r p (SUC(n p))"
    let q27 ← q r"s:(A->bool)->bool"
    let q28 ← q r"r:A ring"
    let v29 ← ISPECL [q28, q27, q26, q25] CHINESE_REMAINDER_IDEALS
    let q30 ← q r"x:(A->bool)->A"
    let q31 ← q r"~(SUC n <= n)"
    let r32 ← ARITH_RULE q31
    let q33 ← q r"SUC((n:(A->bool)->num) p)"
    let q34 ← q r"(n:(A->bool)->num) p"
    let q35 ← q r"p:A->bool"
    let q36 ← q r"r:A ring"
    let v37 ← ISPECL [q36, q35, q34, q33] DEDEKIND_IDEAL_POW_SUBSET
    let q38 ← q r"p:A->bool"
    let q39 ← q r"!p. ?x:A. p IN s
              ==> x IN ideal_pow r p (n p) /\
                  ~(x IN ideal_pow r p (SUC(n p)))"
    let q40 ← q r"!p:A->bool. p IN s
                ==> ring_ideal r p /\ ~(p = ring_carrier r) /\
                    maximal_ideal r p"
    let q41 ← q r"ring_1 r:A"
    let q42 ← q r"s:(A->bool)->bool = {}"
    prove
      r"!r s (n:(A->bool)->num).
          dedekind_domain r /\ FINITE s /\
          (!p. p IN s ==> prime_ideal r p /\ ~(p = {ring_0 r}))
          ==> ?a. a IN ring_carrier r /\ ~(a = ring_0 r) /\
                  !p. p IN s
                      ==> ideal_valuation r p (ideal_generated r {a}) = n p"
      (REPEAT STRIP_TAC THEN ASM_CASES_TAC q42 THENL [EXISTS_TAC q41 THEN ASM_MESON_TAC [NOT_IN_EMPTY, RING_1, DEDEKIND_IMP_INTEGRAL_DOMAIN, integral_domain], ALL_TAC] THEN SUBGOAL_THEN q40 ASSUME_TAC THENL [ASM_MESON_TAC [PRIME_IMP_PROPER_IDEAL, PROPER_IDEAL_ALT, DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL], ALL_TAC] THEN SUBGOAL_THEN q39 MP_TAC THENL [X_GEN_TAC q38 THEN REWRITE_TAC [RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN MP_TAC v37 THEN ASM_SIMP_TAC [r32] THEN SET_TAC [], REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM]] THEN X_GEN_TAC q30 THEN DISCH_TAC THEN MP_TAC v29 THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW] THEN ANTS_TAC THENL [CONJ_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_POW, SUBSET], REWRITE_TAC [pairwise]] THEN MAP_EVERY X_GEN_TAC [q24, q23] THEN STRIP_TAC THEN MATCH_MP_TAC COMAXIMAL_IDEAL_POW THEN ASM_SIMP_TAC [MAXIMAL_IDEAL_COMAXIMAL] THEN ASM_MESON_TAC [DEDEKIND_KRULL_DIMENSION_ONE], DISCH_THEN (X_CHOOSE_THEN q22 STRIP_ASSUME_TAC)] THEN SUBGOAL_THEN q21 ASSUME_TAC THENL [X_GEN_TAC q20 THEN DISCH_TAC THEN MATCH_MP_TAC v19 THEN EXISTS_TAC q17 THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, IDEAL_POW_ANTIMONO, RING_IDEAL_IMP_SUBSET, r16], ALL_TAC] THEN EXISTS_TAC q14 THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN FIRST_X_ASSUM (MP_TAC o (GEN_REWRITE_RULE id [v13])) THEN ASM_MESON_TAC [IN_RING_IDEAL_0, RING_IDEAL_IDEAL_POW], X_GEN_TAC q12 THEN DISCH_TAC THEN MATCH_MP_TAC IDEAL_VALUATION_UNIQUE THEN ASM_SIMP_TAC [IDEAL_GENERATED_MINIMAL_EQ, RING_IDEAL_IDEAL_POW, r11]])

  let DEDEKIND_IDEAL_WEAK_APPROXIMATION ← prove
    r"!r s (J:A->bool).
        dedekind_domain r /\ FINITE s /\
        (!P. P IN s ==> prime_ideal r P /\ ~(P = {ring_0 r})) /\
        ring_ideal r J /\ ~(J = {ring_0 r})
        ==> ?x. x IN J /\ ~(x = ring_0 r) /\
                !P. P IN s
                    ==> ideal_valuation r P (ideal_generated r {x}) =
                        ideal_valuation r P J"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s UNION {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
                               ~(ideal_valuation r P (J:A->bool) = 0)}"), (← q r"\P. ideal_valuation r P (J:A->bool)")] DEDEKIND_WEAK_APPROXIMATION) THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_UNION, IDEAL_VALUATION_FINITE_SUPPORT] THEN REWRITE_TAC [IN_UNION, IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"a:A") THEN REWRITE_TAC [IN_UNION, IN_ELIM_THM] THEN STRIP_TAC THEN ASM_SIMP_TAC [] THEN SUBGOAL_THEN (← q r"ideal_generated r {a:A} SUBSET J") MP_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_generated r {a:A}"), (← q r"J:A->bool")] DEDEKIND_IDEAL_SUBSET_VALUATION) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0] THEN DISCH_THEN SUBST1_TAC THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"ideal_valuation r P (J:A->bool) = 0") THEN ASM_SIMP_TAC [LE_0, LE_REFL], REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [IN_IDEAL_GENERATED_SELF]])

  let DEDEKIND_TWO_GENERATORS_STRONG ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"{a:A,b} = {a} UNION {b}")
    let r2 ← ARITH_RULE (← q r"y <= x /\ x = 0 ==> x = 0 /\ y = 0")
    prove
      r"!r j (a:A).
          dedekind_domain r /\ ring_ideal r j /\ a IN j /\ ~(a = ring_0 r)
          ==> ?b. b IN j /\ ideal_generated r {a,b} = j"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier r /\ ~(j = {ring_0 r})") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET, IN_SING], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x:A. x IN ring_carrier r /\ ~(x = ring_0 r)
            ==> ring_ideal r (ideal_generated r {x}) /\
                ~(ideal_generated r {x} = {ring_0 r})") ASSUME_TAC THENL [SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"!p. prime_ideal r p /\ ~(p = {ring_0 r}) /\
          ~(ideal_generated r {a:A} SUBSET p)
          ==> ideal_valuation r p (ideal_generated r {a}) = 0 /\
              ideal_valuation r p j = 0") ASSUME_TAC THENL [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC r2 THEN ASM_SIMP_TAC [IDEAL_VALUATION_EQ_0] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_generated r {a:A}"), (← q r"j:A->bool")] DEDEKIND_IDEAL_SUBSET_VALUATION) THEN ASM_SIMP_TAC [IDEAL_GENERATED_MINIMAL, SING_SUBSET] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"p:A->bool"))) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_generated r {a:A}")] DEDEKIND_IDEAL_FACTORIZATION) THEN ASM_SIMP_TAC [] THEN DISCH_THEN (MP_TAC o CONJUNCT1) THEN ABBREV_TAC (← q r"s = {p | prime_ideal r p /\ ~(p = {ring_0 r}) /\
                         ideal_generated r {a:A} SUBSET p}") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"!p. prime_ideal r p /\ ~(p = {ring_0 r}) /\ ~(p IN s)
          ==> ~(ideal_generated r {a:A} SUBSET p)") ASSUME_TAC THENL [EXPAND_TAC "s" THEN REWRITE_TAC [IN_ELIM_THM] THEN MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:(A->bool)->bool"), (← q r"\p:A->bool. ideal_valuation r p j")] DEDEKIND_WEAK_APPROXIMATION) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN EXPAND_TAC "s" THEN SIMP_TAC [IN_ELIM_THM], DISCH_THEN ((X_CHOOSE_THEN (← q r"b:A") STRIP_ASSUME_TAC) o BETA_RULE)] THEN SUBGOAL_THEN (← q r"ideal_generated r {b:A} SUBSET j") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_generated r {b:A}"), (← q r"j:A->bool")] DEDEKIND_IDEAL_SUBSET_VALUATION) THEN ANTS_TAC THENL [ASM_SIMP_TAC [], DISCH_THEN SUBST1_TAC] THEN X_GEN_TAC (← q r"p:A->bool") THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"(p:A->bool) IN s") THEN ASM_SIMP_TAC [LE_REFL, LE_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"(b:A) IN j") ASSUME_TAC THENL [ASM_MESON_TAC [IN_IDEAL_GENERATED_SELF, SUBSET], ALL_TAC] THEN EXISTS_TAC (← q r"b:A") THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_SIMP_TAC [IDEAL_GENERATED_MINIMAL, INSERT_SUBSET, EMPTY_SUBSET] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"ideal_generated r {a:A,b}")] DEDEKIND_IDEAL_SUBSET_VALUATION) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN ASM_MESON_TAC [IDEAL_GENERATED_INC_GEN, IN_INSERT, IN_SING], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [r1, IDEAL_GENERATED_UNION] THEN X_GEN_TAC (← q r"p:A->bool") THEN STRIP_TAC THEN ASM_SIMP_TAC [IDEAL_VALUATION_SETADD] THEN ASM_CASES_TAC (← q r"(p:A->bool) IN s") THEN ASM_SIMP_TAC [] THEN ARITH_TAC)

  let DEDEKIND_TWO_GENERATORS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(z:A) IN s /\ ~(s = {z}) ==> ?a. a IN s /\ ~(a = z)")
    prove
      r"!r (j:A->bool).
      dedekind_domain r /\ ring_ideal r j
      ==> ?a b. a IN ring_carrier r /\ b IN ring_carrier r /\
                ideal_generated r {a, b} = j"
      (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"j = {ring_0 r:A}") THENL [MAP_EVERY EXISTS_TAC [(← q r"ring_0 r:A"), (← q r"ring_0 r:A")] THEN ASM_REWRITE_TAC [RING_0, INSERT_INSERT, IDEAL_GENERATED_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"?a:A. a IN j /\ ~(a = ring_0 r)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [IN_RING_IDEAL_0, r1], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"a:A")] DEDEKIND_TWO_GENERATORS_STRONG) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"b:A") STRIP_ASSUME_TAC) THEN MAP_EVERY EXISTS_TAC [(← q r"a:A"), (← q r"b:A")] THEN ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET])

  let DEDEKIND_QUOTIENT_PRINCIPAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(z:A) IN s /\ ~(s = {z}) ==> ?a. a IN s /\ ~(a = z)")
    prove
      r"!r (j:A->bool).
      dedekind_domain r /\ ring_ideal r j /\ ~(j = {ring_0 r})
      ==> !k. ring_ideal (quotient_ring r j) k
              ==> principal_ideal (quotient_ring r j) k"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [QUOTIENT_RING_IDEAL_CORRESPONDENCE, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"k:(A->bool)->bool") THEN X_GEN_TAC (← q r"i:A->bool") THEN STRIP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN SUBGOAL_THEN (← q r"?a:A. a IN j /\ ~(a = ring_0 r)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [IN_RING_IDEAL_0, r1], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"i:A->bool"), (← q r"a:A")] DEDEKIND_TWO_GENERATORS_STRONG) THEN ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"b:A") (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM))) THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier r /\ b IN ring_carrier r") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"quotient_ring r (j:A->bool)"), (← q r"ring_coset r (j:A->bool)"), (← q r"{a:A,b}")] IDEAL_GENERATED_BY_EPIMORPHIC_IMAGE) THEN ASM_SIMP_TAC [RING_EPIMORPHISM_RING_COSET, INSERT_SUBSET, EMPTY_SUBSET] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [IMAGE_CLAUSES] THEN SUBGOAL_THEN (← q r"ring_coset r j (a:A) = ring_0(quotient_ring r j)") SUBST1_TAC THENL [ASM_SIMP_TAC [QUOTIENT_RING_0, RING_COSET_EQ_IDEAL], ALL_TAC] THEN REWRITE_TAC [IDEAL_GENERATED_INSERT_ZERO, PRINCIPAL_IDEAL_IDEAL_GENERATED_SING])

  let DEDEKIND_LOCAL_QUOTIENT_PRIME_POW ← prove
    r"!r p:A->bool n.
        dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
        ~(n = 0)
        ==> local_ring (quotient_ring r (ideal_pow r p n))"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"ring_ideal r (ideal_pow r p n) /\ ideal_pow r (p:A->bool) n SUBSET p") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, IDEAL_POW_SUBSET_PRIME_IDEAL, RING_IDEAL_IMP_SUBSET, SUBSET_REFL], ALL_TAC] THEN REWRITE_TAC [local_ring, EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL [ASM_SIMP_TAC [MAXIMAL_IDEAL_EXISTS, TRIVIAL_QUOTIENT_RING, PROPER_IDEAL] THEN ASM_MESON_TAC [PRIME_IMP_PROPER_IDEAL, PROPER_IDEAL, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"!m. maximal_ideal (quotient_ring r (ideal_pow r p n)) m
        ==> m = IMAGE (ring_coset r (ideal_pow r p n)) (p:A->bool)") (fun th => MESON_TAC [th]) THEN X_GEN_TAC (← q r"m:(A->bool)->bool") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_pow r (p:A->bool) n"), (← q r"m:(A->bool)->bool")] QUOTIENT_RING_IDEAL_CORRESPONDENCE) THEN ASM_SIMP_TAC [MAXIMAL_IMP_RING_IDEAL, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"i:A->bool") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"maximal_ideal r (i:A->bool)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"quotient_ring r (ideal_pow r (p:A->bool) n)"), (← q r"ring_coset r (ideal_pow r (p:A->bool) n)"), (← q r"i:A->bool"), (← q r"m:(A->bool)->bool")] MAXIMAL_IDEAL_CORRESPONDENCE) THEN ASM_SIMP_TAC [RING_EPIMORPHISM_RING_COSET, MAXIMAL_IMP_RING_IDEAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"(p:A->bool) SUBSET i") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"i:A->bool"), (← q r"p:A->bool"), (← q r"n:num")] IDEAL_POW_SUBSET_PRIME_IDEAL) THEN ASM_SIMP_TAC [MAXIMAL_IMP_PRIME_IDEAL, RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"maximal_ideal r (p:A->bool)") MP_TAC THENL [ASM_MESON_TAC [DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL], ALL_TAC] THEN REWRITE_TAC [maximal_ideal, NOT_EXISTS_THM] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"i:A->bool")) o CONJUNCT2)) THEN ASM_SIMP_TAC [MAXIMAL_IMP_PROPER_IDEAL, PSUBSET] THEN DISCH_THEN (SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC [])

  let DEDEKIND_UFD_IFF_PID ← prove
    r"!r:A ring. dedekind_domain r ==> (UFD r <=> PID r)"
    (SIMP_TAC [dedekind_domain, PID_EQ_UFD_PRIME_MAXIMAL])

  let DEDEKIND_BEZOUT_IFF_PID ← prove
    r"!r:A ring. dedekind_domain r ==> (bezout_ring r <=> PID r)"
    (SIMP_TAC [dedekind_domain, PID_EQ_NOETHERIAN_BEZOUT_DOMAIN])

  let ideal_class ← new_definition
    r"ideal_class (r:A ring) (j:A->bool) =
    {k | ring_ideal r j /\ ring_ideal r k /\
         ~(j = {ring_0 r}) /\ ~(k = {ring_0 r}) /\
         ?a b. a IN ring_carrier r /\ b IN ring_carrier r /\
               ~(a = ring_0 r) /\ ~(b = ring_0 r) /\
               ideal_prod r (ideal_generated r {a}) j =
               ideal_prod r (ideal_generated r {b}) k}"

  let IN_IDEAL_CLASS ← prove
    r"!r:A ring j k.
        k IN ideal_class r j <=>
        ring_ideal r j /\ ring_ideal r k /\
        ~(j = {ring_0 r}) /\ ~(k = {ring_0 r}) /\
        ?a b. a IN ring_carrier r /\ b IN ring_carrier r /\
              ~(a = ring_0 r) /\ ~(b = ring_0 r) /\
              ideal_prod r (ideal_generated r {a}) j =
              ideal_prod r (ideal_generated r {b}) k"
    (REWRITE_TAC [ideal_class, IN_ELIM_THM])

  let IDEAL_CLASS_REFL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(z:A) IN s /\ ~(s = {z}) ==> ?a. a IN s /\ ~(a = z)")
    prove
      r"!r:A ring j.
          ring_ideal r j /\ ~(j = {ring_0 r})
          ==> j IN ideal_class r j"
      (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [IN_IDEAL_CLASS] THEN SUBGOAL_THEN (← q r"?a:A. a IN j /\ ~(a = ring_0 r)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [IN_RING_IDEAL_0, r1], MAP_EVERY EXISTS_TAC [(← q r"a:A"), (← q r"a:A")] THEN ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET]])

  let IDEAL_CLASS_SYM ← prove
    r"!r:A ring j k.
        k IN ideal_class r j ==> j IN ideal_class r k"
    (REWRITE_TAC [IN_IDEAL_CLASS] THEN MESON_TAC [])

  let IDEAL_CLASS_TRANS ← prove
    r"!r:A ring j k l.
        integral_domain r /\
        k IN ideal_class r j /\ l IN ideal_class r k
        ==> l IN ideal_class r j"
    (REPEAT GEN_TAC THEN REWRITE_TAC [IN_IDEAL_CLASS] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MAP_EVERY EXISTS_TAC [(← q r"ring_mul r a' a:A"), (← q r"ring_mul r b b':A")] THEN ASM_SIMP_TAC [RING_MUL, INTEGRAL_DOMAIN_MUL_EQ_0, (← GSYM IDEAL_PROD_PRINCIPAL)] THEN FIRST_X_ASSUM (MP_TAC o (AP_TERM (← q r"ideal_prod r (ideal_generated r {b:A})"))) THEN FIRST_X_ASSUM (MP_TAC o (AP_TERM (← q r"ideal_prod r (ideal_generated r {a':A})"))) THEN ASM_SIMP_TAC [IDEAL_PROD_AC, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_PROD, RING_IDEAL_IDEAL_GENERATED])

  let IDEAL_CLASS_MUL ← prove
    r"!r:A ring j1 j2 k1 k2.
        integral_domain r /\
        k1 IN ideal_class r j1 /\ k2 IN ideal_class r j2
        ==> ideal_prod r k1 k2 IN ideal_class r (ideal_prod r j1 j2)"
    (REPEAT GEN_TAC THEN REWRITE_TAC [IN_IDEAL_CLASS] THEN STRIP_TAC THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_PROD, IDEAL_PROD_EQ_ZERO] THEN MAP_EVERY EXISTS_TAC [(← q r"ring_mul r a a':A"), (← q r"ring_mul r b b':A")] THEN ASM_SIMP_TAC [RING_MUL, INTEGRAL_DOMAIN_MUL_EQ_0, (← GSYM IDEAL_PROD_PRINCIPAL)] THEN SUBGOAL_THEN (← q r"ideal_prod r (ideal_prod r (ideal_generated r {a}) j1)
                 (ideal_prod r (ideal_generated r {a'}) j2) =
    ideal_prod r (ideal_prod r (ideal_generated r {b:A}) k1)
                 (ideal_prod r (ideal_generated r {b'}) k2)") MP_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [IDEAL_PROD_AC, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_PROD, RING_IDEAL_IDEAL_GENERATED])

  let IN_IDEAL_CLASS_ISOMORPHIC_IMAGE ← prove
    r"!r s (h:A->B) j k.
        ring_isomorphism(r,s) h /\ k IN ideal_class r j
        ==> IMAGE h k IN ideal_class s (IMAGE h j)"
    (REPEAT GEN_TAC THEN REWRITE_TAC [IN_IDEAL_CLASS] THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_ISOMORPHISM_IMP_EPIMORPHISM)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_ISOMORPHISM_IMP_MONOMORPHISM)) THEN SUBGOAL_THEN (← q r"!i. ring_ideal r i
        ==> ring_ideal s (IMAGE (h:A->B) i) /\
            (IMAGE h i = {ring_0 s} <=> i = {ring_0 r})") (fun th => ASM_SIMP_TAC [th]) THENL [X_GEN_TAC (← q r"i:A->bool") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_ideal s (IMAGE (h:A->B) i)") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_EPIMORPHIC_IMAGE], ASM_REWRITE_TAC []] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"h:A->B"), (← q r"i:A->bool")] IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0) THEN ASM_SIMP_TAC [IDEAL_GENERATED_RING_IDEAL], MAP_EVERY EXISTS_TAC [(← q r"(h:A->B) a"), (← q r"(h:A->B) b")]] THEN REWRITE_TAC [CONJ_ASSOC] THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, RING_MONOMORPHISM_EQ_0, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN SUBGOAL_THEN (← q r"!c i. c IN ring_carrier r /\ ring_ideal r i
          ==> ideal_prod s (ideal_generated s {(h:A->B) c}) (IMAGE h i) =
              IMAGE h (ideal_prod r (ideal_generated r {c}) i)") (fun th => ASM_SIMP_TAC [th]) THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"h:A->B"), (← q r"{c:A}")] IDEAL_GENERATED_BY_EPIMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [SING_SUBSET, IMAGE_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC IDEAL_PROD_EPIMORPHIC_IMAGE THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, IDEAL_GENERATED_SUBSET])

  let IDEAL_CLASS_PRINCIPAL ← prove
    r"!r:A ring j.
        integral_domain r /\
        ring_carrier r IN ideal_class r j
        ==> principal_ideal r j"
    (REPEAT GEN_TAC THEN REWRITE_TAC [IN_IDEAL_CLASS] THEN STRIP_TAC THEN UNDISCH_TAC (← q r"ideal_prod r (ideal_generated r {a:A}) j =
    ideal_prod r (ideal_generated r {b}) (ring_carrier r)") THEN SIMP_TAC [IDEAL_PROD_CARRIER, RING_IDEAL_IDEAL_GENERATED] THEN ASM_SIMP_TAC [IDEAL_PROD_SCALE] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(b:A) IN IMAGE (ring_mul r a) j") MP_TAC THENL [ASM_REWRITE_TAC [IN_IDEAL_GENERATED_SELF], REWRITE_TAC [IN_IMAGE]] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"y:A") (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN SUBGOAL_THEN (← q r"(y:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN REWRITE_TAC [principal_ideal] THEN EXISTS_TAC (← q r"y:A") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"a:A"), (← q r"ideal_generated r {y:A}"), (← q r"j:A->bool")] IDEAL_PROD_PRINCIPAL_CANCEL) THEN ASM_SIMP_TAC [IDEAL_PROD_PRINCIPAL, RING_IDEAL_IDEAL_GENERATED] THEN ASM_SIMP_TAC [IDEAL_PROD_SCALE])

  let PRINCIPAL_IDEAL_CLASS ← prove
    r"!r:A ring j.
        ~(j = {ring_0 r}) /\ principal_ideal r j
        ==> ring_carrier r IN ideal_class r j"
    (REPEAT GEN_TAC THEN REWRITE_TAC [principal_ideal] THEN STRIP_TAC THEN FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN SUBGOAL_THEN (← q r"~(a = ring_0 r:A) /\ ~(ring_1 r = ring_0 r:A)") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [ASM_MESON_TAC [IDEAL_GENERATED_0], ALL_TAC] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"~(ideal_generated r {a:A} = {ring_0 r})") THEN REWRITE_TAC [IDEAL_GENERATED_EQ_0] THEN ASM_MESON_TAC [TRIVIAL_RING_10, trivial_ring, IN_SING], ALL_TAC] THEN ASM_REWRITE_TAC [IN_IDEAL_CLASS, RING_IDEAL_CARRIER, (← GSYM trivial_ring), RING_IDEAL_IDEAL_GENERATED, TRIVIAL_RING_10] THEN MAP_EVERY EXISTS_TAC [(← q r"ring_1 r:A"), (← q r"a:A")] THEN ASM_SIMP_TAC [RING_1, IDEAL_PROD_PRINCIPAL, IDEAL_PROD_CARRIER, RING_IDEAL_IDEAL_GENERATED, RING_MUL_LID])

  let DEDEKIND_IDEAL_CLASS_INVERSE ← prove
    r"!r:A ring j.
        dedekind_domain r /\ ring_ideal r j /\ ~(j = {ring_0 r})
        ==> ?k. ring_ideal r k /\ ~(k = {ring_0 r}) /\
                ring_carrier r IN ideal_class r (ideal_prod r j k)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool")] DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"k:A->bool") THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:A") STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC PRINCIPAL_IDEAL_CLASS THEN ASM_SIMP_TAC [IDEAL_GENERATED_EQ_0, PRINCIPAL_IDEAL_IDEAL_GENERATED_SING])

  let DEDEKIND_PID_IFF_TRIVIAL_CLASS_GROUP ← prove
    r"!r:A ring.
        dedekind_domain r
        ==> (PID r <=>
             !j. ring_ideal r j /\ ~(j = {ring_0 r}) /\ ~(j = ring_carrier r)
                 ==> ring_carrier r IN ideal_class r j)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN)) THEN ASM_REWRITE_TAC [PID] THEN EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC (← q r"j:A->bool") THEN STRIP_TAC THENL [MATCH_MP_TAC PRINCIPAL_IDEAL_CLASS THEN ASM_SIMP_TAC [], ASM_CASES_TAC (← q r"j = {ring_0 r:A}") THEN ASM_REWRITE_TAC [PRINCIPAL_IDEAL_0] THEN ASM_CASES_TAC (← q r"j:A->bool = ring_carrier r") THEN ASM_REWRITE_TAC [PRINCIPAL_IDEAL_CARRIER] THEN MATCH_MP_TAC IDEAL_CLASS_PRINCIPAL THEN ASM_SIMP_TAC []])

  let DEDEKIND_IDEAL_CLASS_COPRIME ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r8 ← TAUT (← q r"(~p ==> F) ==> p")
    let r21 ← ARITH_RULE (← q r"n = 0 ==> n <= m")
    prove
      r"!r i j:A->bool.
          dedekind_domain r /\ ring_ideal r i /\ ~(i = {ring_0 r}) /\
          ring_ideal r j /\ ~(j = {ring_0 r})
          ==> ?k. k IN ideal_class r i /\ ring_setadd r k j = ring_carrier r"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN)) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"i:A->bool")] DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"i':A->bool"), (← q r"b:A")] THEN STRIP_TAC THEN ABBREV_TAC (← q r"s = {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
               (j SUBSET P \/ (i':A->bool) SUBSET P)}") THEN SUBGOAL_THEN (← q r"FINITE(s:(A->bool)->bool)") ASSUME_TAC THENL [EXPAND_TAC "s" THEN SUBGOAL_THEN (← q r"{P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
             (j SUBSET P \/ (i':A->bool) SUBSET P)} =
        {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\ j SUBSET P} UNION
        {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\ i' SUBSET P}") SUBST1_TAC THENL [REWRITE_TAC [EXTENSION, IN_UNION, IN_ELIM_THM] THEN MESON_TAC [], ASM_SIMP_TAC [FINITE_UNION, DEDEKIND_IDEAL_FACTORIZATION]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:(A->bool)->bool"), (← q r"\P. ideal_valuation r P (i':A->bool)")] DEDEKIND_WEAK_APPROXIMATION) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN EXPAND_TAC "s" THEN SIMP_TAC [IN_ELIM_THM], REWRITE_TAC [LEFT_IMP_EXISTS_THM]] THEN X_GEN_TAC (← q r"a:A") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"~(ideal_generated r {a:A} = {ring_0 r})") ASSUME_TAC THENL [ASM_REWRITE_TAC [IDEAL_GENERATED_EQ_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_generated r {a:A} SUBSET i'") MP_TAC THENL [ASM_SIMP_TAC [DEDEKIND_IDEAL_SUBSET_VALUATION, RING_IDEAL_IDEAL_GENERATED] THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"(P:A->bool) IN s") THEN ASM_SIMP_TAC [LE_REFL] THEN MATCH_MP_TAC r21 THEN ASM_SIMP_TAC [IDEAL_VALUATION_EQ_0] THEN UNDISCH_TAC (← q r"~((P:A->bool) IN s)") THEN EXPAND_TAC "s" THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN MESON_TAC [], ASM_SIMP_TAC [DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES, RING_IDEAL_IDEAL_GENERATED, LEFT_IMP_EXISTS_THM]] THEN X_GEN_TAC (← q r"k:A->bool") THEN STRIP_TAC THEN EXISTS_TAC (← q r"k:A->bool") THEN SUBGOAL_THEN (← q r"~(k = {ring_0 r:A})") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~(ideal_generated r {a:A} = {ring_0 r})") THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z20 ← (q r"ideal_generated r {a:A}"); let z19 ← (do let z17 ← (do let z18 ← (pure th); pure (concl z18)); liftExcept (rand z17)); pure (z19 == z20)))))) THEN ASM_SIMP_TAC [IDEAL_PROD_RZERO, RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN CONJ_TAC THENL [ASM_REWRITE_TAC [IN_IDEAL_CLASS] THEN MAP_EVERY EXISTS_TAC [(← q r"a:A"), (← q r"b:A")] THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z16 ← (q r"ideal_generated r {a:A}"); let z15 ← (do let z13 ← (do let z14 ← (pure th); pure (concl z14)); liftExcept (rand z13)); pure (z15 == z16)))))) THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z12 ← (q r"ideal_generated r {b:A}"); let z11 ← (do let z9 ← (do let z10 ← (pure th); pure (concl z10)); liftExcept (rand z9)); pure (z11 == z12)))))) THEN ASM_SIMP_TAC [IDEAL_PROD_AC, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_PROD, RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN MATCH_MP_TAC r8 THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ring_setadd r k (j:A->bool)")] MAXIMAL_SUPERIDEAL_EXISTS) THEN ANTS_TAC THENL [ASM_SIMP_TAC [proper_ideal, RING_IDEAL_SETADD, PSUBSET] THEN ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, RING_IDEAL_SETADD], DISCH_THEN (X_CHOOSE_THEN (← q r"P:A->bool") STRIP_ASSUME_TAC)] THEN SUBGOAL_THEN (← q r"prime_ideal r (P:A->bool) /\ ~(P = {ring_0 r})") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [MAXIMAL_IMP_PRIME_IDEAL] THEN DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~(j = {ring_0 r:A})") THEN REWRITE_TAC [] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_SETADD_SUPERSET_RIGHT, SUBSET_TRANS, RING_IDEAL_IMP_SUBSET, IN_RING_IDEAL_0], ASM_MESON_TAC [IN_RING_IDEAL_0, SING_SUBSET]], ALL_TAC] THEN SUBGOAL_THEN (← q r"(P:A->bool) IN s") ASSUME_TAC THENL [EXPAND_TAC "s" THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN DISJ1_TAC THEN ASM_MESON_TAC [RING_SETADD_SUPERSET_RIGHT, SUBSET_TRANS, RING_IDEAL_IMP_SUBSET, IN_RING_IDEAL_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_valuation r P (k:A->bool) = 0") MP_TAC THENL [FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"P:A->bool")) o (checkM (fun z5 => (do let z6 ← (do let z7 ← (pure z5); pure (concl z7)); pure (is_forall z6)))))) THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z4 ← (q r"ideal_generated r {a:A}"); let z3 ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); liftExcept (rand z1)); pure (z3 == z4)))))) THEN ASM_SIMP_TAC [IDEAL_VALUATION_IDEAL_PROD] THEN ARITH_TAC, ASM_SIMP_TAC [IDEAL_VALUATION_EQ_0] THEN ASM_MESON_TAC [RING_SETADD_SUPERSET_LEFT, SUBSET_TRANS, RING_IDEAL_IMP_SUBSET, IN_RING_IDEAL_0]])

  -- @@RETURN BEGIN
  return { DVR, DVR_IMP_DEDEKIND, DEDEKIND_LOCAL_IDEAL_MAXIMAL_POW,
           DVR_IFF_LOCAL_DEDEKIND, DVR_IDEAL_MAXIMAL_POW, DVR_IDEALS_TOTALLY_ORDERED,
           DEDEKIND_WEAK_APPROXIMATION, DEDEKIND_IDEAL_WEAK_APPROXIMATION,
           DEDEKIND_TWO_GENERATORS_STRONG, DEDEKIND_TWO_GENERATORS,
           DEDEKIND_QUOTIENT_PRINCIPAL, DEDEKIND_LOCAL_QUOTIENT_PRIME_POW,
           DEDEKIND_UFD_IFF_PID, DEDEKIND_BEZOUT_IFF_PID, ideal_class, IN_IDEAL_CLASS,
           IDEAL_CLASS_REFL, IDEAL_CLASS_SYM, IDEAL_CLASS_TRANS, IDEAL_CLASS_MUL,
           IN_IDEAL_CLASS_ISOMORPHIC_IMAGE, IDEAL_CLASS_PRINCIPAL, PRINCIPAL_IDEAL_CLASS,
           DEDEKIND_IDEAL_CLASS_INVERSE, DEDEKIND_PID_IFF_TRIVIAL_CLASS_GROUP,
           DEDEKIND_IDEAL_CLASS_COPRIME }
  -- @@RETURN END

end HolANT.DedekindStruct
