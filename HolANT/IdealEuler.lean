/- ========================================================================= -/
/- ANT: Euler and Fermat for ideals, and the number of units modulo ...    -/
/- ========================================================================= -/
/- File: HolANT/IdealEuler.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/ideal_euler.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antidealeulerdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/frag.ml, Library/grouptheory.ml, Library/ring_groups.ml, Library/products.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/symmetric_group.ml, Library/galois.ml, Library/finite_fields.ml, ANT/ideal_arith.ml, ANT/hensel.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.IdealEuler fills them).

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
import HolLibrary.Frag
import HolLibrary.GroupTheory
import HolLibrary.RingGroups
import HolLibrary.Products
import HolLibrary.Matroids
import HolLibrary.Permutations
import HolLibrary.RingDet
import HolLibrary.FieldTheory
import HolLibrary.SymmetricGroup
import HolLibrary.Galois
import HolLibrary.FiniteFields
import HolANT.IdealArith
import HolANT.Hensel
import HolANT.Algmisc
import HolANT.Integral
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.IdealNorm

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.IdealArith
open HolANT.Hensel
open HolANT.Algmisc
open HolANT.Integral
open HolANT.Dedekind
open HolANT.DedekindStruct
open HolANT.IdealNorm

namespace HolANT.IdealEuler

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (CARD_DELETE CARD_DIFF CARD_EQ_0 CARD_QUOTIENT_RING_CHAIN CARD_SING
   CARD_UNITS_PROD_RING CHINESE_REMAINDER_RING_ISOMORPHISM COMAXIMAL_IDEAL_POW
   COMAXIMAL_IDEAL_PRODUCT DEDEKIND_IDEAL_FACTORIZATION DEDEKIND_IMP_NOETHERIAN
   DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL DEDEKIND_PRIME_IDEAL_UNIFORMIZER
   EQ_MULT_LCANCEL EXP EXTENSION FIELD_QUOTIENT_RING FIELD_UNIT FINITE_CROSS
   FINITE_FIELD_PRIMITIVE_ROOT FINITE_INDUCT_STRONG
   FINITE_QUOTIENT_RING_IDEAL_PROD FINITE_QUOTIENT_RING_MONO FINITE_SING
   FINITE_SUBSET FORALL_IN_IMAGE FORALL_IN_INSERT GROUP_POW_GROUP_ORDER
   IDEAL_GENERATED_MINIMAL_EQ IDEAL_GENERATED_SING IDEAL_GENERATED_SUBSET
   IDEAL_NORM_FACTORIZATION IDEAL_NORM_GT_1 IDEAL_NORM_IDEAL_POW
   IDEAL_NORM_IN_IDEAL IDEAL_NORM_POS IDEAL_POW_1 IDEAL_POW_ANTIMONO
   IDEAL_PRODUCT_EMPTY IDEAL_PRODUCT_INSERT IDEAL_PROD_COMAXIMAL
   IDEAL_VALUATION_EQ_0 IMP_CONJ IN_DELETE IN_DIFF IN_ELIM_THM IN_IMAGE
   IN_RING_IDEAL_0 IN_RING_IDEAL_ADD IN_RING_IDEAL_LMUL IN_RING_IDEAL_NEG
   IN_RING_IDEAL_RMUL IN_RING_IDEAL_SUB IN_SING ISOMORPHIC_RING_CARD_UNITS
   ISOMORPHIC_RING_SYM LEFT_AND_EXISTS_THM LEFT_IMP_EXISTS_THM LEFT_SUB_DISTRIB
   LE_1 MAXIMAL_IDEAL_COMAXIMAL MAXIMAL_IMP_PROPER_IDEAL MAXIMAL_IMP_RING_IDEAL
   MULT_AC MULT_CLAUSES NOT_EXISTS_THM NOT_IN_EMPTY NPRODUCT_CLAUSES
   PRIME_IMP_PROPER_IDEAL PRIME_IMP_RING_IDEAL PRODUCT_EQ PRODUCT_MUL PROD_RING
   PROPER_IDEAL_ALT PSUBSET QUOTIENT_RING QUOTIENT_RING_0 QUOTIENT_RING_1
   QUOTIENT_RING_CARRIER REAL_OF_NUM_EQ REAL_OF_NUM_MUL REAL_OF_NUM_NPRODUCT
   REAL_OF_NUM_POW REAL_OF_NUM_SUB RIGHT_AND_EXISTS_THM RIGHT_FORALL_IMP_THM
   RING_0 RING_1 RING_ADD RING_COSET_EQ RING_COSET_EQ_IDEAL
   RING_HOMOMORPHISM_POW RING_HOMOMORPHISM_RING_COSET RING_IDEAL_CARRIER
   RING_IDEAL_IDEAL_GENERATED RING_IDEAL_IDEAL_POW RING_IDEAL_IDEAL_PRODUCT
   RING_IDEAL_IMP_SUBSET RING_MUL RING_MUL_IN_IDEAL_POW RING_NEG_SUB RING_OF_NUM
   RING_POW RING_POW_ADD_SQUARE_CONGRUENCE RING_SETADD_SYM RING_SUB_REFL
   RING_UNIT_IN_CARRIER RING_UNIT_QUOTIENT_RING_COSET
   RING_UNIT_QUOTIENT_RING_IDEAL_POW RING_UNIT_QUOTIENT_RING_MAXIMAL SUBSET
   SUB_ADD TRIVIAL_QUOTIENT_RING TRIVIAL_RING_10 UNIT_GROUP UNIT_GROUP_POW
   ideal_norm maximal_ideal real_pow ring_divides ring_pow ring_setadd ring_unit
   trivial_ring : thm)
  deriving Inhabited

/-- What ideal_euler.ml uses from Session besides theorems. -/
structure IdealEulerDeps where
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
/- ideal_euler.ml phrases from line 54 to 533                             -/
/- ---------------------------------------------------------------------- -/

structure IdealEuler where
  -- @@FIELDS
  IDEAL_EULER : thm
  CARD_UNITS_QUOTIENT_RING_MAXIMAL : thm
  IDEAL_NORM_FERMAT : thm
  MAXIMAL_IDEAL_FINITE_QUOTIENT_POW_CARD : thm
  DEDEKIND_RESIDUE_GENERATOR_UNIFORMIZER : thm
  CARD_UNITS_QUOTIENT_RING_COPRIME : thm
  CARD_UNITS_QUOTIENT_RING_PRIME_POW : thm
  CARD_UNITS_QUOTIENT_RING_PRIME_PRODUCT : thm
  DEDEKIND_CARD_UNITS_QUOTIENT_RING : thm
  DEDEKIND_CARD_UNITS_QUOTIENT_RING_REAL : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupIdealEuler [HolBase] (D : IdealEulerDeps) :
    ExceptT String IO IdealEuler := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, REAL_FIELD,
        RING_RULE, SET_RULE, SET_TAC, .. } := D
  let { CARD_DELETE, CARD_DIFF, CARD_EQ_0, CARD_QUOTIENT_RING_CHAIN, CARD_SING,
        CARD_UNITS_PROD_RING, CHINESE_REMAINDER_RING_ISOMORPHISM, COMAXIMAL_IDEAL_POW,
        COMAXIMAL_IDEAL_PRODUCT, DEDEKIND_IDEAL_FACTORIZATION, DEDEKIND_IMP_NOETHERIAN,
        DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL, DEDEKIND_PRIME_IDEAL_UNIFORMIZER,
        EQ_MULT_LCANCEL, EXP, EXTENSION, FIELD_QUOTIENT_RING, FIELD_UNIT, FINITE_CROSS,
        FINITE_FIELD_PRIMITIVE_ROOT, FINITE_INDUCT_STRONG,
        FINITE_QUOTIENT_RING_IDEAL_PROD, FINITE_QUOTIENT_RING_MONO, FINITE_SING,
        FINITE_SUBSET, FORALL_IN_IMAGE, FORALL_IN_INSERT, GROUP_POW_GROUP_ORDER,
        IDEAL_GENERATED_MINIMAL_EQ, IDEAL_GENERATED_SING, IDEAL_GENERATED_SUBSET,
        IDEAL_NORM_FACTORIZATION, IDEAL_NORM_GT_1, IDEAL_NORM_IDEAL_POW,
        IDEAL_NORM_IN_IDEAL, IDEAL_NORM_POS, IDEAL_POW_1, IDEAL_POW_ANTIMONO,
        IDEAL_PRODUCT_EMPTY, IDEAL_PRODUCT_INSERT, IDEAL_PROD_COMAXIMAL,
        IDEAL_VALUATION_EQ_0, IMP_CONJ, IN_DELETE, IN_DIFF, IN_ELIM_THM, IN_IMAGE,
        IN_RING_IDEAL_0, IN_RING_IDEAL_ADD, IN_RING_IDEAL_LMUL, IN_RING_IDEAL_NEG,
        IN_RING_IDEAL_RMUL, IN_RING_IDEAL_SUB, IN_SING, ISOMORPHIC_RING_CARD_UNITS,
        ISOMORPHIC_RING_SYM, LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM,
        LEFT_SUB_DISTRIB, LE_1, MAXIMAL_IDEAL_COMAXIMAL, MAXIMAL_IMP_PROPER_IDEAL,
        MAXIMAL_IMP_RING_IDEAL, MULT_AC, MULT_CLAUSES, NOT_EXISTS_THM, NOT_IN_EMPTY,
        NPRODUCT_CLAUSES, PRIME_IMP_PROPER_IDEAL, PRIME_IMP_RING_IDEAL, PRODUCT_EQ,
        PRODUCT_MUL, PROD_RING, PROPER_IDEAL_ALT, PSUBSET, QUOTIENT_RING,
        QUOTIENT_RING_0, QUOTIENT_RING_1, QUOTIENT_RING_CARRIER, REAL_OF_NUM_EQ,
        REAL_OF_NUM_MUL, REAL_OF_NUM_NPRODUCT, REAL_OF_NUM_POW, REAL_OF_NUM_SUB,
        RIGHT_AND_EXISTS_THM, RIGHT_FORALL_IMP_THM, RING_0, RING_1, RING_ADD,
        RING_COSET_EQ, RING_COSET_EQ_IDEAL, RING_HOMOMORPHISM_POW,
        RING_HOMOMORPHISM_RING_COSET, RING_IDEAL_CARRIER, RING_IDEAL_IDEAL_GENERATED,
        RING_IDEAL_IDEAL_POW, RING_IDEAL_IDEAL_PRODUCT, RING_IDEAL_IMP_SUBSET,
        RING_MUL, RING_MUL_IN_IDEAL_POW, RING_NEG_SUB, RING_OF_NUM, RING_POW,
        RING_POW_ADD_SQUARE_CONGRUENCE, RING_SETADD_SYM, RING_SUB_REFL,
        RING_UNIT_IN_CARRIER, RING_UNIT_QUOTIENT_RING_COSET,
        RING_UNIT_QUOTIENT_RING_IDEAL_POW, RING_UNIT_QUOTIENT_RING_MAXIMAL, SUBSET,
        SUB_ADD, TRIVIAL_QUOTIENT_RING, TRIVIAL_RING_10, UNIT_GROUP, UNIT_GROUP_POW,
        ideal_norm, maximal_ideal, real_pow, ring_divides, ring_pow, ring_setadd,
        ring_unit, trivial_ring, .. } := D.core1
  -- @@SCOPE END

  let IDEAL_EULER ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_sub r (ring_mul r x y) (ring_add r (ring_mul r x y) z) =
        ring_neg r (z:A)")
    prove
      r"!r j (x:A).
          ring_ideal r j /\ FINITE(ring_carrier(quotient_ring r j)) /\
          x IN ring_carrier r /\
          ring_setadd r (ideal_generated r {x}) j = ring_carrier r
          ==> ring_sub r
               (ring_pow r x (CARD {u | ring_unit (quotient_ring r j) u}))
               (ring_1 r) IN j"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_unit (quotient_ring r j) (ring_coset r j (x:A))") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_UNIT_QUOTIENT_RING_COSET] THEN UNDISCH_TAC (← q r"ring_setadd r (ideal_generated r {x:A}) j = ring_carrier r") THEN GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"ring_1 r:A"))) THEN REWRITE_TAC [RING_1, ring_setadd, IN_ELIM_THM] THEN ASM_SIMP_TAC [IDEAL_GENERATED_SING, IN_ELIM_THM] THEN REWRITE_TAC [ring_divides, LEFT_AND_EXISTS_THM, RIGHT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"z:A"), (← q r"y:A")] THEN STRIP_TAC THEN EXISTS_TAC (← q r"y:A") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(z:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sub r (ring_mul r x y) (ring_add r (ring_mul r x y) z) =
        ring_neg r (z:A)") SUBST1_TAC THENL [MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC [], ASM_SIMP_TAC [IN_RING_IDEAL_NEG]], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_HOMOMORPHISM_RING_COSET)) THEN MP_TAC (← ISPECL [(← q r"unit_group(quotient_ring r (j:A->bool))"), (← q r"ring_coset r j (x:A)")] GROUP_POW_GROUP_ORDER) THEN REWRITE_TAC [UNIT_GROUP, UNIT_GROUP_POW, IN_ELIM_THM] THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"ring_carrier(quotient_ring r (j:A->bool))") THEN ASM_REWRITE_TAC [SUBSET, IN_ELIM_THM, RING_UNIT_IN_CARRIER], ALL_TAC] THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← GSYM (← MATCH_MP RING_HOMOMORPHISM_POW th))])) THEN ASM_SIMP_TAC [QUOTIENT_RING_1, RING_COSET_EQ, RING_POW, RING_1])

  let CARD_UNITS_QUOTIENT_RING_MAXIMAL ← prove
    r"!r p:A->bool.
        maximal_ideal r p /\ FINITE(ring_carrier(quotient_ring r p))
        ==> CARD {u | ring_unit (quotient_ring r p) u} = ideal_norm r p - 1"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"field(quotient_ring r (p:A->bool))") ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_QUOTIENT_RING], ALL_TAC] THEN SUBGOAL_THEN (← q r"{u | ring_unit (quotient_ring r p) u} =
    ring_carrier(quotient_ring r (p:A->bool)) DELETE
    ring_0(quotient_ring r p)") SUBST1_TAC THENL [ASM_SIMP_TAC [EXTENSION, IN_ELIM_THM, IN_DELETE, FIELD_UNIT], ASM_SIMP_TAC [CARD_DELETE, RING_0, ideal_norm]])

  let IDEAL_NORM_FERMAT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_sub r (ring_mul r x y) x =
      ring_mul r x (ring_sub r y (ring_1 r:A))")
    let r2 ← SET_RULE (← q r"(x:A) IN s ==> (s INTER {x} SUBSET u <=> x IN u)")
    prove
      r"!r p (x:A).
          maximal_ideal r p /\ FINITE(ring_carrier(quotient_ring r p)) /\
          x IN ring_carrier r
          ==> ring_sub r (ring_pow r x (ideal_norm r p)) x IN p"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"1 <= ideal_norm r (p:A->bool)") ASSUME_TAC THENL [MATCH_MP_TAC IDEAL_NORM_POS THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_CASES_TAC (← q r"(x:A) IN p") THENL [MATCH_MP_TAC IN_RING_IDEAL_SUB THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ideal_norm r (p:A->bool) = SUC(ideal_norm r p - 1)") SUBST1_TAC THENL [ASM_ARITH_TAC, REWRITE_TAC [ring_pow]] THEN MATCH_MP_TAC IN_RING_IDEAL_RMUL THEN ASM_SIMP_TAC [RING_POW], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool"), (← q r"x:A")] IDEAL_EULER) THEN ASM_SIMP_TAC [CARD_UNITS_QUOTIENT_RING_MAXIMAL] THEN ANTS_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_generated r {x:A}"), (← q r"p:A->bool")] RING_SETADD_SYM) THEN ANTS_TAC THENL [ASM_SIMP_TAC [IDEAL_GENERATED_SUBSET, RING_IDEAL_IMP_SUBSET], DISCH_THEN SUBST1_TAC] THEN ASM_SIMP_TAC [MAXIMAL_IDEAL_COMAXIMAL, RING_IDEAL_IDEAL_GENERATED] THEN ASM_SIMP_TAC [IDEAL_GENERATED_MINIMAL_EQ, r2], DISCH_TAC] THEN SUBGOAL_THEN (← q r"ring_sub r (ring_pow r x (ideal_norm r p)) x =
      ring_mul r x (ring_sub r (ring_pow r x (ideal_norm r p - 1))
                               (ring_1 r:A))") SUBST1_TAC THENL [SUBGOAL_THEN (← q r"ideal_norm r (p:A->bool) = SUC(ideal_norm r p - 1)") (fun th => GEN_REWRITE_TAC (LAND_CONV o (LAND_CONV o RAND_CONV)) [th]) THENL [ASM_ARITH_TAC, REWRITE_TAC [ring_pow]] THEN MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [RING_POW], ASM_SIMP_TAC [IN_RING_IDEAL_LMUL]])

  let MAXIMAL_IDEAL_FINITE_QUOTIENT_POW_CARD ← prove
    r"!r j:A->bool.
        maximal_ideal r j /\ FINITE(ring_carrier(quotient_ring r j))
        ==> ring_of_num r (CARD(ring_carrier(quotient_ring r j))) IN j /\
            !x. x IN ring_carrier r
                ==> ring_sub r
                     (ring_pow r x (CARD(ring_carrier(quotient_ring r j)))) x
                    IN j"
    (REWRITE_TAC [(← GSYM ideal_norm)] THEN MESON_TAC [IDEAL_NORM_IN_IDEAL, IDEAL_NORM_FERMAT, MAXIMAL_IMP_RING_IDEAL])

  let DEDEKIND_RESIDUE_GENERATOR_UNIFORMIZER ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"t = ring_add r
           (ring_sub r
             (ring_add r (ring_sub r u (ring_add r v w)) w)
             (ring_sub r u (ring_add r a t)))
           (ring_sub r v (a:A))")
    let r2 ← ARITH_RULE (← q r"2 = 1 + 1")
    let r3 ← ARITH_RULE (← q r"2 = 1 + 1")
    let r4 ← RING_RULE (← q r"ring_sub r (ring_add r a t) a = (t:A)")
    prove
      r"!r p:A->bool.
          dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
          FINITE(ring_carrier(quotient_ring r p))
          ==> ?a. a IN ring_carrier r /\
                  (!y. y IN ring_carrier r
                       ==> y IN p \/ ?m. ring_sub r y (ring_pow r a m) IN p) /\
                  ring_sub r
                    (ring_pow r a (CARD(ring_carrier(quotient_ring r p)))) a
                  IN p /\
                  ~(ring_sub r
                     (ring_pow r a (CARD(ring_carrier(quotient_ring r p)))) a
                    IN ideal_pow r p 2)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"maximal_ideal r (p:A->bool)") ASSUME_TAC THENL [ASM_SIMP_TAC [DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"field(quotient_ring r (p:A->bool))") ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_QUOTIENT_RING], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool")] MAXIMAL_IDEAL_FINITE_QUOTIENT_POW_CARD) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"q = CARD(ring_carrier(quotient_ring r (p:A->bool)))") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"~(q:num = 0)") ASSUME_TAC THENL [EXPAND_TAC "q" THEN ASM_SIMP_TAC [CARD_EQ_0] THEN MESON_TAC [RING_0, NOT_IN_EMPTY], ALL_TAC] THEN MP_TAC (← ISPEC (← q r"quotient_ring r (p:A->bool)") FINITE_FIELD_PRIMITIVE_ROOT) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"g:A->bool") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"?a0:A. a0 IN ring_carrier r /\ ring_coset r p a0 = g") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"(g:A->bool) IN ring_carrier(quotient_ring r p)") THEN ASM_SIMP_TAC [QUOTIENT_RING, IN_ELIM_THM] THEN MESON_TAC [], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_HOMOMORPHISM_RING_COSET)) THEN SUBGOAL_THEN (← q r"!a:A. a IN ring_carrier r /\ ring_sub r a a0 IN p
            ==> !y. y IN ring_carrier r
                    ==> y IN p \/ ?m. ring_sub r y (ring_pow r a m) IN p") ASSUME_TAC THENL [X_GEN_TAC (← q r"a:A") THEN STRIP_TAC THEN X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"(y:A) IN p") THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"ring_coset r p (y:A)")) o (checkM (fun th => (do if ← (do let z14 ← (do let z15 ← (pure th); pure (concl z15)); pure (is_forall z14)) then (do let z16 ← (do let z17 ← (pure th); pure (concl z17)); canM (fun z18 => (do let z19 ← (pure z18); find_termM (fun z20 => (do let z22 ← (pure z20); let z21 ← (q r"ring_pow (quotient_ring r (p:A->bool))"); pure (z21 == z22))) z19)) z16) else pure false))))) THEN ANTS_TAC THENL [CONJ_TAC THENL [ASM_SIMP_TAC [QUOTIENT_RING, IN_ELIM_THM] THEN ASM_MESON_TAC [], ASM_SIMP_TAC [QUOTIENT_RING_0, RING_COSET_EQ_IDEAL]], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"m:num")) THEN EXISTS_TAC (← q r"m:num") THEN SUBGOAL_THEN (← q r"ring_coset r p (a:A) = g") ASSUME_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z13 ← (q r"ring_coset r p (a0:A) = g"); let z12 ← (do let z11 ← (pure th); pure (concl z11)); pure (z12 == z13)))))) THEN ASM_SIMP_TAC [RING_COSET_EQ], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_coset r p (ring_pow r (a:A) m) = ring_coset r p y") MP_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); pure (is_eq z5)) then (do let z10 ← (q r"ring_coset r p (y:A)"); let z9 ← (do let z7 ← (do let z8 ← (pure th); pure (concl z8)); liftExcept (rhs z7)); pure (z9 == z10)) else pure false))))) THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_POW th)])), ASM_SIMP_TAC [RING_COSET_EQ, RING_POW] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool"), (← q r"ring_sub r (ring_pow r (a:A) m) y")] IN_RING_IDEAL_NEG) THEN ASM_SIMP_TAC [RING_NEG_SUB, RING_POW]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool")] DEDEKIND_PRIME_IDEAL_UNIFORMIZER) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"t:A") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(t:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN ASM_CASES_TAC (← q r"ring_sub r (ring_pow r (a0:A) q) a0 IN ideal_pow r p 2") THENL [ALL_TAC, EXISTS_TAC (← q r"a0:A") THEN ASM_SIMP_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_SUB_REFL, IN_RING_IDEAL_0]] THEN EXISTS_TAC (← q r"ring_add r (a0:A) t") THEN ASM_SIMP_TAC [RING_ADD] THEN CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_ADD] THEN SUBGOAL_THEN (← q r"ring_sub r (ring_add r a0 t) a0 = (t:A)") SUBST1_TAC THENL [MATCH_MP_TAC r4 THEN ASM_REWRITE_TAC [], ASM_REWRITE_TAC []], DISCH_TAC] THEN SUBGOAL_THEN (← q r"ring_mul r (t:A) t IN ideal_pow r p 2") ASSUME_TAC THENL [REWRITE_TAC [r3] THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN ASM_SIMP_TAC [IDEAL_POW_1, RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_pow r p 2:A->bool"), (← q r"a0:A"), (← q r"t:A"), (← q r"q - 1")] RING_POW_ADD_SQUARE_CONGRUENCE) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, SUB_ADD, LE_1] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_mul r (ring_of_num r q) (ring_mul r (ring_pow r a0 (q - 1)) t) IN
      ideal_pow r p 2:A->bool") ASSUME_TAC THENL [REWRITE_TAC [r2] THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN ASM_SIMP_TAC [IDEAL_POW_1, RING_IDEAL_IMP_SUBSET] THEN MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN ASM_SIMP_TAC [RING_POW], ALL_TAC] THEN UNDISCH_TAC (← q r"~((t:A) IN ideal_pow r p 2)") THEN REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(t:A) =
      ring_add r
       (ring_sub r
         (ring_add r
           (ring_sub r (ring_pow r (ring_add r a0 t) q)
              (ring_add r (ring_pow r a0 q)
                 (ring_mul r (ring_of_num r q)
                    (ring_mul r (ring_pow r a0 (q - 1)) t))))
           (ring_mul r (ring_of_num r q) (ring_mul r (ring_pow r a0 (q - 1)) t)))
         (ring_sub r (ring_pow r (ring_add r a0 t) q) (ring_add r a0 t)))
       (ring_sub r (ring_pow r a0 q) a0)") SUBST1_TAC THENL [MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [RING_POW, RING_ADD, RING_MUL, RING_OF_NUM], ALL_TAC] THEN MATCH_MP_TAC IN_RING_IDEAL_ADD THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IN_RING_IDEAL_SUB THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN MATCH_MP_TAC IN_RING_IDEAL_ADD THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW])

  let CARD_UNITS_QUOTIENT_RING_COPRIME ← prove
    r"!r j k:A->bool.
        ring_ideal r j /\ ring_ideal r k /\
        ring_setadd r j k = ring_carrier r /\
        FINITE(ring_carrier(quotient_ring r j)) /\
        FINITE(ring_carrier(quotient_ring r k))
        ==> CARD {u | ring_unit (quotient_ring r (ideal_prod r j k)) u} =
            CARD {u | ring_unit (quotient_ring r j) u} *
            CARD {u | ring_unit (quotient_ring r k) u}"
    (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [IDEAL_PROD_COMAXIMAL] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"k:A->bool")] CHINESE_REMAINDER_RING_ISOMORPHISM) THEN ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [ISOMORPHIC_RING_SYM] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"prod_ring (quotient_ring r j) (quotient_ring r (k:A->bool))"), (← q r"quotient_ring r (j INTER k:A->bool)")] ISOMORPHIC_RING_CARD_UNITS) THEN ASM_SIMP_TAC [PROD_RING, FINITE_CROSS] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC CARD_UNITS_PROD_RING THEN ASM_REWRITE_TAC [])

  let CARD_UNITS_QUOTIENT_RING_PRIME_POW ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r13 ← RING_RULE (← q r"x:A = ring_add r (ring_sub r x z) z")
    prove
      r"!r p:A->bool n.
          dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
          FINITE(ring_carrier(quotient_ring r p)) /\ ~(n = 0)
          ==> CARD {u | ring_unit (quotient_ring r (ideal_pow r p n)) u} =
              ideal_norm r p EXP (n - 1) * (ideal_norm r p - 1)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"maximal_ideal r (p:A->bool)") ASSUME_TAC THENL [ASM_MESON_TAC [DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL], ALL_TAC] THEN ABBREV_TAC (← q r"q = ideal_pow r (p:A->bool) n") THEN SUBGOAL_THEN (← q r"ring_ideal r (q:A->bool) /\ q SUBSET p") STRIP_ASSUME_TAC THENL [EXPAND_TAC "q" THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool"), (← q r"1"), (← q r"n:num")] IDEAL_POW_ANTIMONO) THEN ASM_SIMP_TAC [IDEAL_POW_1, RING_IDEAL_IMP_SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool"), (← q r"n:num")] IDEAL_NORM_IDEAL_POW) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"{u | ring_unit (quotient_ring r q) u} =
      ring_carrier(quotient_ring r q) DIFF IMAGE (ring_coset r q) (p:A->bool)") SUBST1_TAC THENL [ASM_SIMP_TAC [QUOTIENT_RING_CARRIER] THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"y:A->bool") THEN REWRITE_TAC [IN_ELIM_THM, IN_DIFF, IN_IMAGE] THEN ASM_CASES_TAC (← q r"?x:A. x IN ring_carrier r /\ y = ring_coset r q x") THENL [FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"x:A") STRIP_ASSUME_TAC), ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (MATCH_MP RING_UNIT_IN_CARRIER)) THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, IN_ELIM_THM] THEN ASM_MESON_TAC []] THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool"), (← q r"n:num"), (← q r"x:A")] RING_UNIT_QUOTIENT_RING_IDEAL_POW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [RING_UNIT_QUOTIENT_RING_MAXIMAL] THEN SUBGOAL_THEN (← q r"?a:A. a IN ring_carrier r /\
                         ring_coset r q x = ring_coset r q a") (fun th => REWRITE_TAC [th]) THENL [ASM_MESON_TAC [], ALL_TAC] THEN AP_TERM_TAC THEN EQ_TAC THENL [DISCH_TAC THEN EXISTS_TAC (← q r"x:A") THEN ASM_REWRITE_TAC [], DISCH_THEN (X_CHOOSE_THEN (← q r"z:A") STRIP_ASSUME_TAC)] THEN SUBGOAL_THEN (← q r"(z:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sub r x (z:A) IN p") MP_TAC THENL [FIRST_X_ASSUM (MATCH_MP_TAC o ((REWRITE_RULE [SUBSET]) o (checkM (fun th => (do let z16 ← (q r"(q:A->bool) SUBSET p"); let z15 ← (do let z14 ← (pure th); pure (concl z14)); pure (z15 == z16)))))) THEN UNDISCH_TAC (← q r"ring_coset r q (x:A) = ring_coset r q z") THEN ASM_SIMP_TAC [RING_COSET_EQ], DISCH_TAC] THEN SUBGOAL_THEN (← q r"x:A = ring_add r (ring_sub r x z) z") SUBST1_TAC THENL [MATCH_MP_TAC r13 THEN ASM_REWRITE_TAC [], MATCH_MP_TAC IN_RING_IDEAL_ADD THEN ASM_REWRITE_TAC []], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"q:A->bool"), (← q r"p:A->bool")] CARD_QUOTIENT_RING_CHAIN) THEN ASM_REWRITE_TAC [(← GSYM ideal_norm)] THEN DISCH_TAC THEN wPart lhand (lhand o rand) CARD_DIFF THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [(← GSYM ideal_norm)] THEN SUBGOAL_THEN (← q r"~(ideal_norm r (p:A->bool) = 0)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool")] IDEAL_NORM_POS) THEN ASM_REWRITE_TAC [] THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"CARD(IMAGE (ring_coset r q) (p:A->bool)) = ideal_norm r p EXP (n - 1)") SUBST1_TAC THENL [FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do if ← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); pure (is_eq z4)) then (do let z6 ← (do let z7 ← (pure th); pure (concl z7)); canM (fun z8 => (do let z9 ← (pure z8); find_termM (fun z10 => (do let z12 ← (pure z10); let z11 ← (q r"CARD(IMAGE (ring_coset r q) (p:A->bool))"); pure (z11 == z12))) z9)) z6) else pure false)))) THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"n = SUC(n - 1)") (fun th => GEN_REWRITE_TAC (LAND_CONV o (LAND_CONV o RAND_CONV)) [th]) THENL [ASM_ARITH_TAC, REWRITE_TAC [EXP]] THEN ASM_SIMP_TAC [EQ_MULT_LCANCEL] THEN MESON_TAC [], ALL_TAC] THEN FIRST_X_ASSUM (SUBST1_TAC o (checkM (fun th => (do let z3 ← (q r"ideal_norm r (q:A->bool) = ideal_norm r p EXP n"); let z2 ← (do let z1 ← (pure th); pure (concl z1)); pure (z2 == z3))))) THEN SUBGOAL_THEN (← q r"n = SUC(n - 1)") (fun th => GEN_REWRITE_TAC (LAND_CONV o (LAND_CONV o RAND_CONV)) [th]) THENL [ASM_ARITH_TAC, REWRITE_TAC [EXP]] THEN REWRITE_TAC [LEFT_SUB_DISTRIB, MULT_CLAUSES] THEN REWRITE_TAC [MULT_AC])

  let CARD_UNITS_QUOTIENT_RING_PRIME_PRODUCT ← prove
    r"!r s (e:(A->bool)->num).
        dedekind_domain r /\ FINITE s /\
        (!p. p IN s
             ==> prime_ideal r p /\ ~(p = {ring_0 r}) /\ ~(e p = 0) /\
                 FINITE(ring_carrier(quotient_ring r p)))
        ==> FINITE(ring_carrier(quotient_ring r
                     (ideal_product r s (\p. ideal_pow r p (e p))))) /\
            CARD {u | ring_unit (quotient_ring r
                        (ideal_product r s (\p. ideal_pow r p (e p)))) u} =
            nproduct s (\p. ideal_norm r p EXP (e p - 1) *
                            (ideal_norm r p - 1))"
    (GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_IMP_NOETHERIAN)) THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [IDEAL_PRODUCT_EMPTY, NPRODUCT_CLAUSES] THEN SUBGOAL_THEN (← q r"trivial_ring(quotient_ring r (ring_carrier r:A->bool))") MP_TAC THENL [SIMP_TAC [TRIVIAL_QUOTIENT_RING, RING_IDEAL_CARRIER, PROPER_IDEAL_ALT], REWRITE_TAC [trivial_ring] THEN DISCH_TAC] THEN ASM_REWRITE_TAC [FINITE_SING] THEN SUBGOAL_THEN (← q r"{u | ring_unit (quotient_ring r (ring_carrier r:A->bool)) u} =
      {ring_0(quotient_ring r (ring_carrier r))}") SUBST1_TAC THENL [GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM, IN_SING] THEN X_GEN_TAC (← q r"u:A->bool") THEN REWRITE_TAC [ring_unit] THEN ASM_REWRITE_TAC [IN_SING] THEN ASM_MESON_TAC [TRIVIAL_RING_10, trivial_ring, RING_0, RING_MUL, IN_SING], REWRITE_TAC [CARD_SING]], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"q:A->bool"), (← q r"s:(A->bool)->bool")] THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN X_GEN_TAC (← q r"e:(A->bool)->num") THEN REWRITE_TAC [FORALL_IN_INSERT] THEN STRIP_TAC THEN REMOVE_THEN "ih" (MP_TAC o (SPEC (← q r"e:(A->bool)->num"))) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_ideal r (ideal_pow r q ((e:(A->bool)->num) q)) /\
    FINITE(ring_carrier(quotient_ring r (ideal_pow r q (e q))))") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, IDEAL_NORM_IDEAL_POW, PRIME_IMP_RING_IDEAL], ALL_TAC] THEN ASM_SIMP_TAC [IDEAL_PRODUCT_INSERT, NPRODUCT_CLAUSES] THEN SUBGOAL_THEN (← q r"ring_setadd r (ideal_pow r q ((e:(A->bool)->num) q))
      (ideal_product r s (\p. ideal_pow r p (e p))) = ring_carrier r") ASSUME_TAC THENL [MATCH_MP_TAC COMAXIMAL_IDEAL_PRODUCT THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN X_GEN_TAC (← q r"p:A->bool") THEN DISCH_TAC THEN MATCH_MP_TAC COMAXIMAL_IDEAL_POW THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN SUBGOAL_THEN (← q r"maximal_ideal r (q:A->bool) /\ maximal_ideal r p") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL], ALL_TAC] THEN ASM_SIMP_TAC [MAXIMAL_IDEAL_COMAXIMAL, PRIME_IMP_RING_IDEAL] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"p:A->bool = q") (fun th => ASM_MESON_TAC [th]) THEN FIRST_X_ASSUM (MP_TAC o ((GEN_REWRITE_RULE id [maximal_ideal]) o (checkM (fun th => (do let z3 ← (q r"maximal_ideal r (p:A->bool)"); let z2 ← (do let z1 ← (pure th); pure (concl z1)); pure (z2 == z3)))))) THEN REWRITE_TAC [NOT_EXISTS_THM] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"q:A->bool")) o CONJUNCT2)) THEN ASM_SIMP_TAC [MAXIMAL_IMP_PROPER_IDEAL, PSUBSET] THEN SET_TAC [], ALL_TAC] THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_QUOTIENT_RING_IDEAL_PROD THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_PRODUCT], ASM_SIMP_TAC [CARD_UNITS_QUOTIENT_RING_COPRIME, RING_IDEAL_IDEAL_PRODUCT, CARD_UNITS_QUOTIENT_RING_PRIME_POW]])

  let DEDEKIND_CARD_UNITS_QUOTIENT_RING ← prove
    r"!r j:A->bool.
        dedekind_domain r /\ ring_ideal r j /\ ~(j = {ring_0 r}) /\
        FINITE(ring_carrier(quotient_ring r j))
        ==> CARD {u | ring_unit (quotient_ring r j) u} =
            nproduct {p | prime_ideal r p /\ ~(p = {ring_0 r}) /\ j SUBSET p}
                     (\p. ideal_norm r p EXP (ideal_valuation r p j - 1) *
                          (ideal_norm r p - 1))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool")] DEDEKIND_IDEAL_FACTORIZATION) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"{p | prime_ideal r p /\ ~(p = {ring_0 r}) /\ (j:A->bool) SUBSET p}"), (← q r"\p:A->bool. ideal_valuation r p (j:A->bool)")] CARD_UNITS_QUOTIENT_RING_PRIME_PRODUCT) THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN ANTS_TAC THENL [X_GEN_TAC (← q r"p:A->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [IDEAL_VALUATION_EQ_0] THEN MATCH_MP_TAC FINITE_QUOTIENT_RING_MONO THEN EXISTS_TAC (← q r"j:A->bool") THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC []])

  let DEDEKIND_CARD_UNITS_QUOTIENT_RING_REAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"2 <= n ==> 1 <= n")
    let r2 ← ARITH_RULE (← q r"1 < n ==> 2 <= n")
    prove
      r"!r j:A->bool.
          dedekind_domain r /\ ring_ideal r j /\ ~(j = {ring_0 r}) /\
          FINITE(ring_carrier(quotient_ring r j))
          ==> &(CARD {u | ring_unit (quotient_ring r j) u}) =
              &(ideal_norm r j) *
              product {p | prime_ideal r p /\ ~(p = {ring_0 r}) /\ j SUBSET p}
                      (\p. &1 - inv(&(ideal_norm r p)))"
      (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [DEDEKIND_CARD_UNITS_QUOTIENT_RING, IDEAL_NORM_FACTORIZATION] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool")] DEDEKIND_IDEAL_FACTORIZATION) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"s = {p | prime_ideal r p /\ ~(p = {ring_0 r}) /\
                         (j:A->bool) SUBSET p}") THEN STRIP_TAC THEN ASM_SIMP_TAC [REAL_OF_NUM_NPRODUCT] THEN ASM_SIMP_TAC [(← GSYM PRODUCT_MUL)] THEN MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC (← q r"p:A->bool") THEN EXPAND_TAC "s" THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"~(ideal_valuation r p (j:A->bool) = 0)") ASSUME_TAC THENL [ASM_SIMP_TAC [IDEAL_VALUATION_EQ_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"2 <= ideal_norm r (p:A->bool)") ASSUME_TAC THENL [MATCH_MP_TAC r2 THEN MATCH_MP_TAC IDEAL_NORM_GT_1 THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN CONJ_TAC THENL [ASM_MESON_TAC [PRIME_IMP_PROPER_IDEAL, PROPER_IDEAL_ALT], MATCH_MP_TAC FINITE_QUOTIENT_RING_MONO THEN EXISTS_TAC (← q r"j:A->bool") THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL]], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_valuation r p (j:A->bool) = SUC(ideal_valuation r p j - 1)") (fun th => GEN_REWRITE_TAC (RAND_CONV o (LAND_CONV o (RAND_CONV o RAND_CONV))) [th]) THENL [ASM_ARITH_TAC, ALL_TAC] THEN ASM_SIMP_TAC [(← GSYM REAL_OF_NUM_MUL), (← GSYM REAL_OF_NUM_POW), (← GSYM REAL_OF_NUM_SUB), r1] THEN REWRITE_TAC [real_pow] THEN SUBGOAL_THEN (← q r"~((&(ideal_norm r (p:A->bool)):real) = &0)") MP_TAC THENL [REWRITE_TAC [REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC, CONV_TAC REAL_FIELD])

  -- @@RETURN BEGIN
  return { IDEAL_EULER, CARD_UNITS_QUOTIENT_RING_MAXIMAL, IDEAL_NORM_FERMAT,
           MAXIMAL_IDEAL_FINITE_QUOTIENT_POW_CARD,
           DEDEKIND_RESIDUE_GENERATOR_UNIFORMIZER, CARD_UNITS_QUOTIENT_RING_COPRIME,
           CARD_UNITS_QUOTIENT_RING_PRIME_POW, CARD_UNITS_QUOTIENT_RING_PRIME_PRODUCT,
           DEDEKIND_CARD_UNITS_QUOTIENT_RING, DEDEKIND_CARD_UNITS_QUOTIENT_RING_REAL }
  -- @@RETURN END

end HolANT.IdealEuler
