/- ========================================================================= -/
/- ANT: Localization of Dedekind domains                                   -/
/- ========================================================================= -/
/- File: HolANT/DedekindLocal.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/dedekind_local.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antdedekindlocaldiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, ANT/integral.ml, ANT/ideal_arith.ml, Library/products.ml, ANT/algmisc.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.DedekindLocal fills them).

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

namespace HolANT.DedekindLocal

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES DEDEKIND_IDEAL_SUBSET_POW_VALUATION
   DEDEKIND_IMP_INTEGRAL_DOMAIN DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL DE_MORGAN_THM
   DVR_IDEAL_MAXIMAL_POW DVR_IFF_LOCAL_DEDEKIND DVR_IMP_DEDEKIND EXTENSION
   FIELD_EQ_TRIVIAL_IDEALS FORALL_IN_GSPEC FORALL_IN_IMAGE
   IDEAL_GENERATED_MINIMAL IDEAL_GENERATED_RING_LOCALIZATION IDEAL_POW_0
   IDEAL_POW_EQ_ZERO IDEAL_POW_SUC IDEAL_PROD_LZERO IDEAL_PROD_MINIMAL
   IDEAL_PROD_RZERO IDEAL_VALUATION_EQ_0 IDEAL_VALUATION_IDEAL_POW
   IDEAL_VALUATION_IDEAL_PROD IDEAL_VALUATION_PRIME IDEAL_VALUATION_UNIQUE
   IMP_CONJ INTEGRALLY_CLOSED_LOCALIZATION INTEGRAL_DOMAIN_LOCALIZATION
   INTEGRAL_DOMAIN_REGULAR IN_DIFF IN_ELIM_THM IN_INTER IN_RING_IDEAL_0 IN_SING
   LEFT_AND_EXISTS_THM LEFT_IMP_EXISTS_THM LE_REFL LOCAL_RING_LOCALIZATION
   MAXIMAL_AMONG_PRIME_IDEALS MAXIMAL_IMP_PRIME_IDEAL MAXIMAL_IMP_RING_IDEAL
   NOETHERIAN_RING_LOCALIZATION NOT_EXISTS_THM NOT_FORALL_THM NOT_IMP
   NOT_IN_EMPTY PRIME_IDEAL_IMP_SUBSET PRIME_IDEAL_LOCALIZATION
   PRIME_IDEAL_LOCALIZATION_CONTRACTION PRIME_IDEAL_LOCALIZATION_EXISTS
   PRIME_IMP_PROPER_IDEAL PRIME_IMP_RING_IDEAL PROPER_IDEAL_LOCALIZATION PSUBSET
   RIGHT_FORALL_IMP_THM RING_0 RING_1 RING_1_IN_MULTSYS
   RING_FRACTIONATE_IN_CARRIER RING_HOMOMORPHISM_FRACTIONATE
   RING_HOMOMORPHISM_MUL RING_IDEAL_0 RING_IDEAL_IDEAL_POW RING_IDEAL_IDEAL_PROD
   RING_IDEAL_IMP_SUBSET RING_IDEAL_LOCALIZATION RING_LOCALEQUIV_EQ_0_GEN
   RING_LOCALIZATION_0 RING_LOCALIZATION_CARRIER RING_LOCALIZATION_MUL
   RING_LOCALIZATION_PRIME_IDEAL_CORRESPONDENCE RING_MULTSYS
   RING_MULTSYS_NONPRIME RING_MUL_IN_IDEAL_PROD RING_MUL_IN_MULTSYS
   RING_MUL_RZERO RING_REGULAR_MUL_EQ_0 RING_SETMUL SING_SUBSET SUBSET
   SUBSET_ANTISYM SUBSET_REFL dedekind_domain ideal_prod maximal_ideal
   proper_ideal ring_fractionate ring_setmul : thm)
  deriving Inhabited

/-- What dedekind_local.ml uses from Session besides theorems. -/
structure DedekindLocalDeps where
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
/- dedekind_local.ml phrases from line 42 to 325                          -/
/- ---------------------------------------------------------------------- -/

structure DedekindLocal where
  -- @@FIELDS
  MAXIMAL_IDEAL_LOCALIZATION : thm
  IDEAL_LOCALIZATION_EQ_ZERO : thm
  IDEAL_PROD_LOCALIZATION : thm
  IDEAL_POW_LOCALIZATION : thm
  DEDEKIND_LOCALIZATION : thm
  DVR_LOCALIZATION : thm
  IDEAL_VALUATION_LOCALIZATION : thm
  DEDEKIND_LOCALIZATION_IDEAL_POW : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDedekindLocal [HolBase] (D : DedekindLocalDeps) :
    ExceptT String IO DedekindLocal := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON, SET_RULE, SET_TAC, .. } := D
  let { DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES, DEDEKIND_IDEAL_SUBSET_POW_VALUATION,
        DEDEKIND_IMP_INTEGRAL_DOMAIN, DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL,
        DE_MORGAN_THM, DVR_IDEAL_MAXIMAL_POW, DVR_IFF_LOCAL_DEDEKIND, DVR_IMP_DEDEKIND,
        EXTENSION, FIELD_EQ_TRIVIAL_IDEALS, FORALL_IN_GSPEC, FORALL_IN_IMAGE,
        IDEAL_GENERATED_MINIMAL, IDEAL_GENERATED_RING_LOCALIZATION, IDEAL_POW_0,
        IDEAL_POW_EQ_ZERO, IDEAL_POW_SUC, IDEAL_PROD_LZERO, IDEAL_PROD_MINIMAL,
        IDEAL_PROD_RZERO, IDEAL_VALUATION_EQ_0, IDEAL_VALUATION_IDEAL_POW,
        IDEAL_VALUATION_IDEAL_PROD, IDEAL_VALUATION_PRIME, IDEAL_VALUATION_UNIQUE,
        IMP_CONJ, INTEGRALLY_CLOSED_LOCALIZATION, INTEGRAL_DOMAIN_LOCALIZATION,
        INTEGRAL_DOMAIN_REGULAR, IN_DIFF, IN_ELIM_THM, IN_INTER, IN_RING_IDEAL_0,
        IN_SING, LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM, LE_REFL,
        LOCAL_RING_LOCALIZATION, MAXIMAL_AMONG_PRIME_IDEALS, MAXIMAL_IMP_PRIME_IDEAL,
        MAXIMAL_IMP_RING_IDEAL, NOETHERIAN_RING_LOCALIZATION, NOT_EXISTS_THM,
        NOT_FORALL_THM, NOT_IMP, NOT_IN_EMPTY, PRIME_IDEAL_IMP_SUBSET,
        PRIME_IDEAL_LOCALIZATION, PRIME_IDEAL_LOCALIZATION_CONTRACTION,
        PRIME_IDEAL_LOCALIZATION_EXISTS, PRIME_IMP_PROPER_IDEAL, PRIME_IMP_RING_IDEAL,
        PROPER_IDEAL_LOCALIZATION, PSUBSET, RIGHT_FORALL_IMP_THM, RING_0, RING_1,
        RING_1_IN_MULTSYS, RING_FRACTIONATE_IN_CARRIER, RING_HOMOMORPHISM_FRACTIONATE,
        RING_HOMOMORPHISM_MUL, RING_IDEAL_0, RING_IDEAL_IDEAL_POW,
        RING_IDEAL_IDEAL_PROD, RING_IDEAL_IMP_SUBSET, RING_IDEAL_LOCALIZATION,
        RING_LOCALEQUIV_EQ_0_GEN, RING_LOCALIZATION_0, RING_LOCALIZATION_CARRIER,
        RING_LOCALIZATION_MUL, RING_LOCALIZATION_PRIME_IDEAL_CORRESPONDENCE,
        RING_MULTSYS, RING_MULTSYS_NONPRIME, RING_MUL_IN_IDEAL_PROD,
        RING_MUL_IN_MULTSYS, RING_MUL_RZERO, RING_REGULAR_MUL_EQ_0, RING_SETMUL,
        SING_SUBSET, SUBSET, SUBSET_ANTISYM, SUBSET_REFL, dedekind_domain, ideal_prod,
        maximal_ideal, proper_ideal, ring_fractionate, ring_setmul, .. } := D.core1
  -- @@SCOPE END

  let MAXIMAL_IDEAL_LOCALIZATION ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(m:A->bool) SUBSET p /\ ~(m PSUBSET p) ==> p = m")
    prove
      r"!r s m:A->bool.
          ring_multsys r s /\ maximal_ideal r m /\ m INTER s = {}
          ==> maximal_ideal (ring_localization r s)
                {ring_localequiv r s (a,b) | a,b | a IN m /\ b IN s}"
      (REPEAT STRIP_TAC THEN REWRITE_TAC [MAXIMAL_AMONG_PRIME_IDEALS] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_PRIME_IDEAL)) THEN ASM_SIMP_TAC [PRIME_IDEAL_LOCALIZATION] THEN ASM_SIMP_TAC [RING_LOCALIZATION_PRIME_IDEAL_CORRESPONDENCE] THEN REWRITE_TAC [NOT_EXISTS_THM, LEFT_AND_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"q:(A#A->bool)->bool"), (← q r"p:A->bool")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"p:A->bool = m") SUBST_ALL_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [UNDISCH_THEN (← q r"{x | x IN ring_carrier r /\ ring_fractionate r s x IN q} = (p:A->bool)") (SUBST1_TAC o SYM) THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC [PRIME_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN FIRST_X_ASSUM (MATCH_MP_TAC o ((REWRITE_RULE [SUBSET]) o (CONJUNCT1 o (REWRITE_RULE [PSUBSET])))) THEN REWRITE_TAC [ring_fractionate, IN_ELIM_THM] THEN ASM_MESON_TAC [RING_1_IN_MULTSYS], FIRST_X_ASSUM (MP_TAC o (CONJUNCT2 o (GEN_REWRITE_RULE id [maximal_ideal]))) THEN ASM_MESON_TAC [PRIME_IMP_PROPER_IDEAL]])

  let IDEAL_LOCALIZATION_EQ_ZERO ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r5 ← SET_RULE (← q r"(!a:A. a IN j ==> a = z) /\ z IN j ==> j = {z}")
    prove
      r"!r s j:A->bool.
          ring_multsys r s /\ s SUBSET {a | ring_regular r a} /\
          j SUBSET ring_carrier r
          ==> ({ring_localequiv r s (a,b) | a,b | a IN j /\ b IN s} =
               {ring_0 (ring_localization r s)} <=>
               j = {ring_0 r})"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_1_IN_MULTSYS)) THEN SUBGOAL_THEN (← q r"!a b:A. a IN j /\ b IN s
              ==> (ring_localequiv r s (a,b) = ring_0 (ring_localization r s) <=>
                   a = ring_0 r)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier r") ASSUME_TAC THENL [ASM SET_TAC [], ASM_SIMP_TAC [RING_LOCALEQUIV_EQ_0_GEN]] THEN EQ_TAC THENL [DISCH_THEN (X_CHOOSE_THEN (← q r"c:A") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"c:A"), (← q r"a:A")] RING_REGULAR_MUL_EQ_0) THEN ANTS_TAC THENL [ASM SET_TAC [], ASM_MESON_TAC []], DISCH_THEN SUBST1_TAC THEN EXISTS_TAC (← q r"ring_1 r:A") THEN ASM_SIMP_TAC [RING_MUL_RZERO, RING_1]], ALL_TAC] THEN EQ_TAC THEN DISCH_TAC THENL [MATCH_MP_TAC r5 THEN FIRST_X_ASSUM (MP_TAC o (GEN_REWRITE_RULE id [EXTENSION])) THEN REWRITE_TAC [IN_SING, IN_ELIM_THM] THEN DISCH_TAC THEN CONJ_TAC THENL [X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"ring_localequiv r s (a:A,ring_1 r)"))) THEN ASM_MESON_TAC [], FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"ring_0(ring_localization r (s:A->bool))"))) THEN ASM_MESON_TAC []], FIRST_X_ASSUM (SUBST_ALL_TAC o (checkM (fun z1 => (do let z2 ← (do let z3 ← (do let z4 ← (pure z1); pure (concl z4)); liftExcept (lhand z3)); pure (is_var z2))))) THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM, IN_SING] THEN X_GEN_TAC (← q r"z:A#A->bool") THEN EQ_TAC THENL [STRIP_TAC THEN ASM_MESON_TAC [IN_SING], DISCH_THEN SUBST1_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"ring_0 r:A"), (← q r"ring_1 r:A")] THEN ASM_SIMP_TAC [RING_LOCALIZATION_0]]])

  let IDEAL_PROD_LOCALIZATION ← prove
    r"!r s j k:A->bool.
        ring_multsys r s /\ j SUBSET ring_carrier r /\ k SUBSET ring_carrier r
        ==> {ring_localequiv r s (a,b) | a,b |
             a IN ideal_prod r j k /\ b IN s} =
            ideal_prod (ring_localization r s)
              {ring_localequiv r s (a,b) | a,b | a IN j /\ b IN s}
              {ring_localequiv r s (a,b) | a,b | a IN k /\ b IN s}"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ideal_prod] THEN wPart lhand (rand o rand) IDEAL_GENERATED_RING_LOCALIZATION THEN ASM_SIMP_TAC [RING_SETMUL] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN REWRITE_TAC [RING_IDEAL_IDEAL_PROD, SUBSET, FORALL_IN_IMAGE] THEN REWRITE_TAC [ring_setmul, FORALL_IN_GSPEC] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier r /\ (b:A) IN ring_carrier r") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL (← MATCH_MP RING_HOMOMORPHISM_FRACTIONATE th))])) THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_PROD THEN ASM_SIMP_TAC [RING_FRACTIONATE_IN_CARRIER] THEN REWRITE_TAC [ring_fractionate, IN_ELIM_THM] THEN ASM_MESON_TAC [RING_1_IN_MULTSYS], MATCH_MP_TAC IDEAL_PROD_MINIMAL THEN ASM_SIMP_TAC [RING_IDEAL_LOCALIZATION, RING_IDEAL_IDEAL_PROD] THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_GSPEC] THEN X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN X_GEN_TAC (← q r"u:A") THEN DISCH_TAC THEN X_GEN_TAC (← q r"b:A") THEN DISCH_TAC THEN X_GEN_TAC (← q r"v:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier r /\ (b:A) IN ring_carrier r") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [RING_LOCALIZATION_MUL, IN_ELIM_THM] THEN MAP_EVERY EXISTS_TAC [(← q r"ring_mul r a b:A"), (← q r"ring_mul r u v:A")] THEN ASM_SIMP_TAC [RING_MUL_IN_IDEAL_PROD, RING_MUL_IN_MULTSYS]])

  let IDEAL_POW_LOCALIZATION ← prove
    r"!r s (j:A->bool) n.
        ring_multsys r s /\ j SUBSET ring_carrier r
        ==> {ring_localequiv r s (a,b) | a,b | a IN ideal_pow r j n /\ b IN s} =
            ideal_pow (ring_localization r s)
              {ring_localequiv r s (a,b) | a,b | a IN j /\ b IN s} n"
    (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN REWRITE_TAC [IDEAL_POW_0, IDEAL_POW_SUC] THEN ASM_SIMP_TAC [RING_LOCALIZATION_CARRIER, IDEAL_PROD_LOCALIZATION, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_POW])

  let DEDEKIND_LOCALIZATION ← prove
    r"!r s:A->bool.
        dedekind_domain r /\ ring_multsys r s /\ ~(ring_0 r IN s)
        ==> dedekind_domain (ring_localization r s)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [dedekind_domain])) THEN ASM_SIMP_TAC [dedekind_domain, INTEGRAL_DOMAIN_LOCALIZATION, NOETHERIAN_RING_LOCALIZATION, INTEGRALLY_CLOSED_LOCALIZATION] THEN X_GEN_TAC (← q r"q:(A#A->bool)->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:A->bool"), (← q r"q:(A#A->bool)->bool")] PRIME_IDEAL_LOCALIZATION_EXISTS) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"p:A->bool") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN MATCH_MP_TAC MAXIMAL_IDEAL_LOCALIZATION THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST_ALL_TAC THEN SUBGOAL_THEN (← q r"(s:A->bool) SUBSET {a | ring_regular r a}") ASSUME_TAC THENL [ASM_SIMP_TAC [SUBSET, IN_ELIM_THM, INTEGRAL_DOMAIN_REGULAR] THEN ASM_MESON_TAC [RING_MULTSYS], ALL_TAC] THEN UNDISCH_TAC (← q r"~({ring_localequiv r s (a,b) | a,b | a IN {ring_0 r} /\ b IN s} =
      {ring_0 (ring_localization r (s:A->bool))})") THEN ASM_SIMP_TAC [IDEAL_LOCALIZATION_EQ_ZERO, SING_SUBSET, RING_0])

  let DVR_LOCALIZATION ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(p:A->bool) INTER (c DIFF p) = {}")
    prove
      r"!r p:A->bool.
          dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r})
          ==> DVR (ring_localization r (ring_carrier r DIFF p))"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MULTSYS_NONPRIME)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"~(ring_0 r IN ring_carrier r DIFF (p:A->bool)) /\
                  ring_carrier r DIFF p SUBSET {a | ring_regular r a}") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [SUBSET, IN_DIFF, IN_ELIM_THM, INTEGRAL_DOMAIN_REGULAR, DEDEKIND_IMP_INTEGRAL_DOMAIN, IN_RING_IDEAL_0] THEN ASM_MESON_TAC [IN_RING_IDEAL_0], ALL_TAC] THEN ASM_SIMP_TAC [DVR_IFF_LOCAL_DEDEKIND, DEDEKIND_LOCALIZATION, LOCAL_RING_LOCALIZATION, FIELD_EQ_TRIVIAL_IDEALS] THEN REWRITE_TAC [DE_MORGAN_THM, NOT_FORALL_THM, NOT_IMP] THEN DISJ2_TAC THEN EXISTS_TAC (← q r"{ring_localequiv r (ring_carrier r DIFF p) (a,b) | a,b |
                 a IN p /\ b IN ring_carrier r DIFF (p:A->bool)}") THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ring_carrier r DIFF p:A->bool"), (← q r"p:A->bool")] PROPER_IDEAL_LOCALIZATION) THEN ASM_SIMP_TAC [r1, proper_ideal, IDEAL_LOCALIZATION_EQ_ZERO, RING_IDEAL_IMP_SUBSET] THEN SET_TAC [])

  let IDEAL_VALUATION_LOCALIZATION ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let p1 ← prove r"!r j:A->bool.
        ring_ideal r j /\ ~(j = {ring_0 r})
        ==> ideal_valuation r {ring_0 r} j = 0" (REPEAT STRIP_TAC THEN MATCH_MP_TAC IDEAL_VALUATION_UNIQUE THEN REWRITE_TAC [RING_IDEAL_0, IDEAL_POW_SUC, IDEAL_POW_0] THEN ASM_SIMP_TAC [IDEAL_PROD_LZERO, SUBSET_REFL, RING_IDEAL_IMP_SUBSET] THEN ASM_MESON_TAC [IN_RING_IDEAL_0, SUBSET_ANTISYM, SING_SUBSET])
    let lemma := p1
    let q2 ← q r"(x:A) IN ring_carrier r"
    let q3 ← q r"ring_fractionate r s (x:A)"
    let q4 ← q r"x:A"
    let q5 ← q r"~(l SUBSET (p:A->bool))"
    let q6 ← q r"ideal_valuation (ring_localization r s)
      {ring_localequiv r s (a,b) | a,b | a IN p /\ b IN s}
      {ring_localequiv r s (a,b) | a,b | a IN l /\ b IN (s:A->bool)} = 0"
    let q7 ← q r"dedekind_domain (ring_localization r (s:A->bool)) /\
    prime_ideal (ring_localization r s)
      {ring_localequiv r s (a,b) | a,b | a IN p /\ b IN s} /\
    ring_ideal (ring_localization r s)
      {ring_localequiv r s (a,b) | a,b | a IN l /\ b IN s} /\
    ~({ring_localequiv r s (a,b) | a,b | a IN p /\ b IN s} =
      {ring_0 (ring_localization r s)}) /\
    ~({ring_localequiv r s (a,b) | a,b | a IN l /\ b IN s} =
      {ring_0 (ring_localization r s)})"
    let q8 ← q r"l:A->bool"
    let q9 ← q r"ideal_pow r p v:A->bool"
    let q10 ← q r"s:A->bool"
    let q11 ← q r"r:A ring"
    let v12 ← ISPECL [q11, q10, q9, q8] IDEAL_PROD_LOCALIZATION
    let v13 ← GSYM IDEAL_VALUATION_EQ_0
    let q14 ← q r"l:A->bool"
    let q15 ← q r"ideal_pow r p v:A->bool"
    let q16 ← q r"p:A->bool"
    let q17 ← q r"r:A ring"
    let v18 ← ISPECL [q17, q16, q15, q14] IDEAL_VALUATION_IDEAL_PROD
    let q19 ← q r"~(l SUBSET (p:A->bool))"
    let q20 ← q r"~(j = {ring_0 r:A})"
    let q21 ← q r"~(l = {ring_0 r:A})"
    let q22 ← q r"l:A->bool"
    let q23 ← q r"ideal_pow r p v:A->bool"
    let q24 ← q r"j:A->bool"
    let q25 ← q r"r:A ring"
    let v26 ← ISPECL [q25, q24, q23] DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES
    let q27 ← q r"v = ideal_valuation r p (j:A->bool)"
    let q28 ← q r"x = 0 /\ y = 0 ==> x = y"
    let r29 ← MESON [] q28
    let q30 ← q r"{ring_0 r:A}"
    let q31 ← q r"s:A->bool"
    let q32 ← q r"r:A ring"
    let v33 ← ISPECL [q32, q31, q30] IDEAL_LOCALIZATION_EQ_ZERO
    let q34 ← q r"p = {ring_0 r:A}"
    let q35 ← q r"(s:A->bool) SUBSET {a | ring_regular r a}"
    let q36 ← q r"~(ring_0 r IN (s:A->bool))"
    prove
      r"!r s p j:A->bool.
          dedekind_domain r /\ ring_multsys r s /\
          prime_ideal r p /\ p INTER s = {} /\
          ring_ideal r j /\ ~(j = {ring_0 r})
          ==> ideal_valuation (ring_localization r s)
                {ring_localequiv r s (a,b) | a,b | a IN p /\ b IN s}
                {ring_localequiv r s (a,b) | a,b | a IN j /\ b IN s} =
              ideal_valuation r p j"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN q36 ASSUME_TAC THENL [ASM_MESON_TAC [IN_RING_IDEAL_0, IN_INTER, NOT_IN_EMPTY], ALL_TAC] THEN SUBGOAL_THEN q35 ASSUME_TAC THENL [ASM_SIMP_TAC [SUBSET, IN_ELIM_THM, INTEGRAL_DOMAIN_REGULAR] THEN ASM_MESON_TAC [RING_MULTSYS], ALL_TAC] THEN ASM_CASES_TAC q34 THENL [FIRST_X_ASSUM SUBST_ALL_TAC THEN MP_TAC v33 THEN ASM_SIMP_TAC [SING_SUBSET, RING_0] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC r29 THEN CONJ_TAC THEN MATCH_MP_TAC lemma THEN ASM_SIMP_TAC [RING_IDEAL_LOCALIZATION, IDEAL_LOCALIZATION_EQ_ZERO, RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN ABBREV_TAC q27 THEN MP_TAC v26 THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, DEDEKIND_IDEAL_SUBSET_POW_VALUATION, LE_REFL, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC q22 THEN STRIP_TAC THEN SUBGOAL_THEN q21 ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC q20 THEN EXPAND_TAC "j" THEN SIMP_TAC [IDEAL_PROD_RZERO, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_POW], ALL_TAC] THEN SUBGOAL_THEN q19 ASSUME_TAC THENL [MP_TAC v18 THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, IDEAL_POW_EQ_ZERO, IDEAL_VALUATION_IDEAL_POW, IDEAL_VALUATION_PRIME, v13] THEN ARITH_TAC, ALL_TAC] THEN MP_TAC v12 THEN ASM_SIMP_TAC [IDEAL_POW_LOCALIZATION, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_POW] THEN DISCH_THEN SUBST1_TAC THEN SUBGOAL_THEN q7 STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [DEDEKIND_LOCALIZATION, PRIME_IDEAL_LOCALIZATION, RING_IDEAL_LOCALIZATION, IDEAL_LOCALIZATION_EQ_ZERO, RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN SUBGOAL_THEN q6 ASSUME_TAC THENL [ASM_SIMP_TAC [IDEAL_VALUATION_EQ_0] THEN UNDISCH_TAC q5 THEN REWRITE_TAC [SUBSET, NOT_FORALL_THM, NOT_IMP] THEN DISCH_THEN (X_CHOOSE_THEN q4 STRIP_ASSUME_TAC) THEN EXISTS_TAC q3 THEN SUBGOAL_THEN q2 ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [PRIME_IDEAL_LOCALIZATION_CONTRACTION] THEN REWRITE_TAC [ring_fractionate, IN_ELIM_THM] THEN ASM_MESON_TAC [RING_1_IN_MULTSYS], ALL_TAC] THEN ASM_SIMP_TAC [IDEAL_VALUATION_IDEAL_PROD, IDEAL_VALUATION_IDEAL_POW, IDEAL_VALUATION_PRIME, RING_IDEAL_IDEAL_POW, IDEAL_POW_EQ_ZERO, DEDEKIND_IMP_INTEGRAL_DOMAIN, PRIME_IMP_RING_IDEAL] THEN ARITH_TAC)

  let DEDEKIND_LOCALIZATION_IDEAL_POW ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(p:A->bool) INTER (c DIFF p) = {}")
    prove
      r"!r p j:A->bool.
          dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
          ring_ideal r j /\ ~(j = {ring_0 r})
          ==> {ring_localequiv r (ring_carrier r DIFF p) (a,b) | a,b |
               a IN j /\ b IN ring_carrier r DIFF p} =
              ideal_pow (ring_localization r (ring_carrier r DIFF p))
                {ring_localequiv r (ring_carrier r DIFF p) (a,b) | a,b |
                 a IN p /\ b IN ring_carrier r DIFF p}
                (ideal_valuation r p j)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"ring_carrier r DIFF p SUBSET {a:A | ring_regular r a}") ASSUME_TAC THENL [ASM_SIMP_TAC [SUBSET, IN_DIFF, IN_ELIM_THM, INTEGRAL_DOMAIN_REGULAR, DEDEKIND_IMP_INTEGRAL_DOMAIN] THEN ASM_MESON_TAC [IN_RING_IDEAL_0], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool")] DVR_LOCALIZATION) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ring_carrier r DIFF p:A->bool"), (← q r"p:A->bool"), (← q r"j:A->bool")] IDEAL_VALUATION_LOCALIZATION) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ring_carrier r DIFF p:A->bool"), (← q r"p:A->bool")] MAXIMAL_IDEAL_LOCALIZATION) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ring_carrier r DIFF p:A->bool"), (← q r"p:A->bool")] IDEAL_LOCALIZATION_EQ_ZERO) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ring_carrier r DIFF p:A->bool"), (← q r"j:A->bool")] IDEAL_LOCALIZATION_EQ_ZERO) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ring_carrier r DIFF p:A->bool"), (← q r"j:A->bool")] RING_IDEAL_LOCALIZATION) THEN ASM_SIMP_TAC [RING_MULTSYS_NONPRIME, r1, DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL, RING_IDEAL_IMP_SUBSET] THEN ABBREV_TAC (← q r"l = ring_localization r (ring_carrier r DIFF p:A->bool)") THEN ABBREV_TAC (← q r"q = {ring_localequiv r (ring_carrier r DIFF p) (a,b) | a,b |
                     a IN p /\ b IN ring_carrier r DIFF (p:A->bool)}") THEN ABBREV_TAC (← q r"k = {ring_localequiv r (ring_carrier r DIFF p) (a,b) | a,b |
                     a IN j /\ b IN ring_carrier r DIFF (p:A->bool)}") THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"l:(A#A->bool)ring"), (← q r"q:(A#A->bool)->bool"), (← q r"k:(A#A->bool)->bool")] DVR_IDEAL_MAXIMAL_POW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"n:num") SUBST_ALL_TAC) THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN ASM_SIMP_TAC [IDEAL_VALUATION_IDEAL_POW, IDEAL_VALUATION_PRIME, DVR_IMP_DEDEKIND, MAXIMAL_IMP_PRIME_IDEAL, MAXIMAL_IMP_RING_IDEAL] THEN ARITH_TAC)

  -- @@RETURN BEGIN
  return { MAXIMAL_IDEAL_LOCALIZATION, IDEAL_LOCALIZATION_EQ_ZERO,
           IDEAL_PROD_LOCALIZATION, IDEAL_POW_LOCALIZATION, DEDEKIND_LOCALIZATION,
           DVR_LOCALIZATION, IDEAL_VALUATION_LOCALIZATION,
           DEDEKIND_LOCALIZATION_IDEAL_POW }
  -- @@RETURN END

end HolANT.DedekindLocal
