/- ========================================================================= -/
/- ANT: Dedekind domains                                                   -/
/- ========================================================================= -/
/- File: HolANT/Dedekind.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/dedekind.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antdedekinddiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/products.ml, ANT/algmisc.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, ANT/integral.ml, ANT/ideal_arith.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.Dedekind fills them).

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
import HolLibrary.Products
import HolANT.Algmisc
import HolLibrary.Matroids
import HolLibrary.Permutations
import HolLibrary.RingDet
import HolLibrary.FieldTheory
import HolANT.Integral
import HolANT.IdealArith

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.Algmisc
open HolANT.Integral
open HolANT.IdealArith

namespace HolANT.Dedekind

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD1 ADD_CLAUSES ADD_SYM ARITH ARITH_EQ COMAXIMAL_IDEAL_POW CONJ_ASSOC
   CONTRAPOS_THM DE_MORGAN_THM EQ_TRANS EXISTS_UNIQUE_THM EXTENSION
   FIELD_IMP_PID FINITE_DELETE FINITE_INDUCT_STRONG FINITE_INSERT FINITE_SUBSET
   FINITE_UNION FORALL_IN_GSPEC FORALL_IN_IMAGE FORALL_IN_INSERT FUN_EQ_THM
   HAS_SIZE_IMAGE_INJ HAS_SIZE_NUMSEG_LE IDEAL_GENERATED_EQ_0
   IDEAL_GENERATED_FINITE IDEAL_GENERATED_INC IDEAL_GENERATED_INC_GEN
   IDEAL_GENERATED_MINIMAL IDEAL_GENERATED_MINIMAL_EQ IDEAL_GENERATED_SING_ALT
   IDEAL_GENERATED_SING_EQ_CARRIER IDEAL_GENERATED_SUBSET IDEAL_POW_0
   IDEAL_POW_1 IDEAL_POW_ADD IDEAL_POW_ANTIMONO IDEAL_POW_CARRIER
   IDEAL_POW_EQ_ZERO IDEAL_POW_PRINCIPAL IDEAL_POW_SUBSET_PRIME_IDEAL
   IDEAL_POW_SUC IDEAL_PRODUCT_EMPTY IDEAL_PRODUCT_EQ IDEAL_PRODUCT_EQ_ZERO
   IDEAL_PRODUCT_INSERT IDEAL_PRODUCT_MONOMIAL_MUL IDEAL_PRODUCT_PRINCIPAL
   IDEAL_PRODUCT_SING IDEAL_PRODUCT_SUBSET IDEAL_PRODUCT_SUBSET_PRIME_IDEAL
   IDEAL_PRODUCT_SUPERSET IDEAL_PROD_AC IDEAL_PROD_ASSOC IDEAL_PROD_CARRIER
   IDEAL_PROD_CARRIER_LEFT IDEAL_PROD_COMAXIMAL IDEAL_PROD_COMM
   IDEAL_PROD_EQ_ZERO IDEAL_PROD_EXPLICIT IDEAL_PROD_IDEAL_GENERATED
   IDEAL_PROD_LZERO IDEAL_PROD_MINIMAL IDEAL_PROD_MONO IDEAL_PROD_PRINCIPAL
   IDEAL_PROD_PRINCIPAL_CANCEL IDEAL_PROD_PRINCIPAL_FACTOR
   IDEAL_PROD_PRINCIPAL_SUBSET_CANCEL IDEAL_PROD_RZERO IDEAL_PROD_SCALE
   IDEAL_PROD_SETADD_RDISTRIB IDEAL_PROD_SUBSET_INTER IDEAL_PROD_SUBSET_LEFT
   IDEAL_PROD_SUBSET_RIGHT IDEAL_SUBSET_IDEAL_QUOTIENT IMP_CONJ IMP_CONJ_ALT
   IMP_IMP INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING INTEGRAL_DOMAIN_MUL_EQ_0
   INTEGRAL_DOMAIN_NONTRIVIAL INTEGRAL_DOMAIN_REGULAR
   INTEGRAL_ELEMENT_FINITE_MODULE INTER_IDEMPOT INTER_SUBSET IN_DELETE
   IN_ELIM_THM IN_IDEAL_GENERATED_SELF IN_IDEAL_GENERATED_SING_EQ IN_IMAGE
   IN_INSERT IN_RING_IDEAL_0 IN_RING_IDEAL_ADD IN_RING_IDEAL_LMUL
   IN_RING_IDEAL_NEG IN_RING_IDEAL_RMUL IN_RING_IDEAL_SUB IN_SING IN_SUBRING_0
   IN_SUBRING_ADD IN_SUBRING_MUL IN_SUBRING_POW IN_UNION LE LEFT_IMP_EXISTS_THM
   LE_0 LE_ANTISYM LE_MULT_RCANCEL LE_REFL LT_EXISTS MAXIMAL_AMONG_PRIME_IDEALS
   MAXIMAL_IDEAL_COMAXIMAL MAXIMAL_IDEAL_COMAXIMAL_MUL MAXIMAL_IMP_PRIME_IDEAL
   MAXIMAL_IMP_RING_IDEAL MAXIMAL_SUPERIDEAL_EXISTS MONOMIAL_1 : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (MONOMIAL_DIV MONOMIAL_DIV_LMUL MONOMIAL_INDUCT MONOMIAL_MUL MONOMIAL_VAR
   MONOMIAL_VARS_1 MONOMIAL_VARS_VAR MONO_EXISTS MULT_CLAUSES
   NOETHERIAN_PRIME_PRODUCT_SUBSET NOETHERIAN_RING_INDUCT NOT_EXISTS_THM
   NOT_FORALL_THM NOT_IMP NOT_LE NOT_LT NSUM_CLAUSES ONE
   PID_IMP_INTEGRALLY_CLOSED PID_IMP_INTEGRAL_DOMAIN PID_IMP_NOETHERIAN_RING
   PID_INTEGER_RING PID_MAXIMAL_EQ_PRIME_IDEAL PRIME_IDEAL_IMP_PSUBSET
   PRIME_IDEAL_IMP_SUBSET PRIME_IMP_PROPER_IDEAL PRIME_IMP_RING_IDEAL
   PROPER_IDEAL PROPER_IDEAL_ALT PSUBSET QUOTIENT_RING_REDUCED
   RADICAL_PRIME_IDEAL RADICAL_SUBSET RIGHT_EXISTS_IMP_THM RIGHT_FORALL_IMP_THM
   RING_0 RING_1 RING_ADD RING_ADD_LZERO RING_ADD_RDISTRIB RING_ADD_RZERO
   RING_DIVIDES_ZERO RING_HOMOMORPHISM_IN_CARRIER RING_HOMOMORPHISM_MUL
   RING_HOMOMORPHISM_SUM RING_IDEAL_0 RING_IDEAL_CARRIER
   RING_IDEAL_IDEAL_GENERATED RING_IDEAL_IDEAL_POW RING_IDEAL_IDEAL_PROD
   RING_IDEAL_IDEAL_PRODUCT RING_IDEAL_IDEAL_QUOTIENT RING_IDEAL_IMP_SUBSET
   RING_IDEAL_INTER RING_IDEAL_SETADD RING_MONOMORPHISM_FRACTIONATE
   RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_MONOMORPHISM_INJECTIVE_EQ RING_MUL
   RING_MULTSYS_REGULAR RING_MUL_ASSOC RING_MUL_IN_IDEAL_POW
   RING_MUL_IN_IDEAL_PROD RING_MUL_LID RING_MUL_LNEG RING_MUL_LZERO RING_MUL_SYM
   RING_NEG RING_POW RING_POW_2 RING_POW_IN_IDEAL_POW RING_SETADD_LZERO
   RING_SETADD_RZERO RING_SETADD_SUBSET_IDEAL RING_SETADD_SUPERSET_LEFT
   RING_SETADD_SUPERSET_RIGHT RING_SUB RING_SUB_REFL RING_SUM_EQ RING_SUM_RMUL
   RING_UNIT_1 RING_UNIT_FRACTIONATE SELECT_UNIQUE SIMPLE_IMAGE_GEN SING_SUBSET
   SKOLEM_THM SUBSET SUBSET_ANTISYM SUBSET_ANTISYM_EQ
   SUBSET_IDEALS_GENERATED_SING SUBSET_IDEAL_QUOTIENT SUBSET_INTER SUBSET_REFL
   SUBSET_TRANS UNION_SUBSET finitely_generated_ideal fraction_ring
   integrally_closed maximal_ideal monomial monomial_1 monomial_divides
   monomial_mul monomial_var monomial_vars noetherian_ring num_CASES o_THM
   prime_ideal proper_ideal radical ring_divides ring_ideal ring_pow ring_unit
   subring_of trivial_ring : thm)
  deriving Inhabited

/-- What dedekind.ml uses from Session besides theorems. -/
structure DedekindDeps where
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
  REFUTE_THEN : thm_tactic → tactic
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
/- dedekind.ml phrases from line 91 to 823                                -/
/- ---------------------------------------------------------------------- -/

structure Dedekind01 where
  -- @@FIELDS
  dedekind_domain : thm
  DEDEKIND_IMP_INTEGRAL_DOMAIN : thm
  DEDEKIND_IMP_NOETHERIAN : thm
  DEDEKIND_IMP_INTEGRALLY_CLOSED : thm
  DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL : thm
  DEDEKIND_MAXIMAL_EQ_PRIME_IDEAL : thm
  DEDEKIND_KRULL_DIMENSION_ONE : thm
  PID_IMP_DEDEKIND : thm
  FIELD_IMP_DEDEKIND : thm
  DEDEKIND_INTEGER_RING : thm
  INTEGRALLY_CLOSED_DIVIDES_IDEAL : thm
  IDEAL_PRODUCT_MONOMIAL_VAR : thm
  IDEAL_PRODUCT_PRIME_MONOMIAL_MUL : thm
  DEDEKIND_IDEAL_QUOTIENT_MAXIMAL_PSUBSET : thm
  DEDEKIND_MAXIMAL_IDEAL_INVERSE : thm
  IDEAL_PROD_PRINCIPAL_COFACTOR : thm
  DEDEKIND_IDEAL_FACTORIZATION_EXISTS : thm
  DEDEKIND_IDEAL_INDUCT : thm
  DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE : thm
  DEDEKIND_IDEAL_INVERTIBLE : thm
  DEDEKIND_IDEAL_PROD_SUBSET_CANCEL : thm
  DEDEKIND_IDEAL_PROD_CANCEL : thm
  DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES : thm
  DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDedekind01 [HolBase] (D : DedekindDeps) :
    ExceptT String IO Dedekind01 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, RING_RULE, SET_RULE, SET_TAC, TAUT,
        new_definition, .. } := D
  let { CONJ_ASSOC, FIELD_IMP_PID, FINITE_DELETE, FINITE_INSERT, FORALL_IN_GSPEC,
        FORALL_IN_IMAGE, FORALL_IN_INSERT, IDEAL_GENERATED_FINITE,
        IDEAL_GENERATED_INC_GEN, IDEAL_GENERATED_MINIMAL,
        IDEAL_GENERATED_SING_EQ_CARRIER, IDEAL_GENERATED_SUBSET, IDEAL_POW_0,
        IDEAL_POW_1, IDEAL_POW_EQ_ZERO, IDEAL_POW_SUBSET_PRIME_IDEAL, IDEAL_POW_SUC,
        IDEAL_PRODUCT_EMPTY, IDEAL_PRODUCT_EQ_ZERO, IDEAL_PRODUCT_INSERT,
        IDEAL_PRODUCT_MONOMIAL_MUL, IDEAL_PRODUCT_SING,
        IDEAL_PRODUCT_SUBSET_PRIME_IDEAL, IDEAL_PRODUCT_SUPERSET, IDEAL_PROD_AC,
        IDEAL_PROD_CARRIER, IDEAL_PROD_CARRIER_LEFT, IDEAL_PROD_COMM,
        IDEAL_PROD_EQ_ZERO, IDEAL_PROD_EXPLICIT, IDEAL_PROD_LZERO, IDEAL_PROD_MONO,
        IDEAL_PROD_PRINCIPAL, IDEAL_PROD_PRINCIPAL_CANCEL, IDEAL_PROD_PRINCIPAL_FACTOR,
        IDEAL_PROD_PRINCIPAL_SUBSET_CANCEL, IDEAL_PROD_SCALE, IDEAL_PROD_SUBSET_LEFT,
        IDEAL_SUBSET_IDEAL_QUOTIENT, IMP_CONJ, IMP_IMP,
        INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING, INTEGRAL_DOMAIN_MUL_EQ_0,
        INTEGRAL_DOMAIN_NONTRIVIAL, INTEGRAL_DOMAIN_REGULAR,
        INTEGRAL_ELEMENT_FINITE_MODULE, IN_DELETE, IN_ELIM_THM,
        IN_IDEAL_GENERATED_SELF, IN_IDEAL_GENERATED_SING_EQ, IN_IMAGE, IN_INSERT,
        IN_RING_IDEAL_0, IN_UNION, LEFT_IMP_EXISTS_THM, MAXIMAL_AMONG_PRIME_IDEALS,
        MAXIMAL_IMP_PRIME_IDEAL, MAXIMAL_IMP_RING_IDEAL, MAXIMAL_SUPERIDEAL_EXISTS,
        MONOMIAL_1, .. } := D.core1
  let { MONOMIAL_INDUCT, MONOMIAL_MUL, MONOMIAL_VAR, MONOMIAL_VARS_1,
        MONOMIAL_VARS_VAR, MONO_EXISTS, NOETHERIAN_PRIME_PRODUCT_SUBSET,
        NOETHERIAN_RING_INDUCT, NOT_EXISTS_THM, PID_IMP_INTEGRALLY_CLOSED,
        PID_IMP_INTEGRAL_DOMAIN, PID_IMP_NOETHERIAN_RING, PID_INTEGER_RING,
        PID_MAXIMAL_EQ_PRIME_IDEAL, PRIME_IDEAL_IMP_SUBSET, PRIME_IMP_RING_IDEAL,
        PROPER_IDEAL_ALT, PSUBSET, RIGHT_FORALL_IMP_THM, RING_1, RING_DIVIDES_ZERO,
        RING_HOMOMORPHISM_IN_CARRIER, RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_SUM,
        RING_IDEAL_CARRIER, RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_POW,
        RING_IDEAL_IDEAL_PROD, RING_IDEAL_IDEAL_PRODUCT, RING_IDEAL_IDEAL_QUOTIENT,
        RING_IDEAL_IMP_SUBSET, RING_MONOMORPHISM_FRACTIONATE,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MONOMORPHISM_INJECTIVE_EQ, RING_MUL,
        RING_MULTSYS_REGULAR, RING_MUL_ASSOC, RING_MUL_IN_IDEAL_PROD, RING_MUL_LZERO,
        RING_SUM_EQ, RING_SUM_RMUL, RING_UNIT_1, RING_UNIT_FRACTIONATE, SING_SUBSET,
        SUBSET, SUBSET_ANTISYM, SUBSET_IDEAL_QUOTIENT, SUBSET_REFL, SUBSET_TRANS,
        finitely_generated_ideal, fraction_ring, integrally_closed, maximal_ideal,
        monomial, monomial_var, monomial_vars, noetherian_ring, o_THM, ring_divides,
        ring_unit, trivial_ring, .. } := D.core2
  -- @@SCOPE END

  let dedekind_domain ← new_definition
    r"dedekind_domain (r:A ring) <=>
  integral_domain r /\
  noetherian_ring r /\
  integrally_closed r /\
  !p. prime_ideal r p /\ ~(p = {ring_0 r}) ==> maximal_ideal r p"

  let DEDEKIND_IMP_INTEGRAL_DOMAIN ← prove
    r"!r:A ring. dedekind_domain r ==> integral_domain r"
    (SIMP_TAC [dedekind_domain])

  let DEDEKIND_IMP_NOETHERIAN ← prove
    r"!r:A ring. dedekind_domain r ==> noetherian_ring r"
    (SIMP_TAC [dedekind_domain])

  let DEDEKIND_IMP_INTEGRALLY_CLOSED ← prove
    r"!r:A ring. dedekind_domain r ==> integrally_closed r"
    (SIMP_TAC [dedekind_domain])

  let DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL ← prove
    r"!r:A ring p.
        dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r})
        ==> maximal_ideal r p"
    (SIMP_TAC [dedekind_domain])

  let DEDEKIND_MAXIMAL_EQ_PRIME_IDEAL ← prove
    r"!r p:A->bool.
        dedekind_domain r /\ ~(p = {ring_0 r})
        ==> (maximal_ideal r p <=> prime_ideal r p)"
    (MESON_TAC [MAXIMAL_IMP_PRIME_IDEAL, DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL])

  let DEDEKIND_KRULL_DIMENSION_ONE ← prove
    r"!r (p:A->bool) q.
    dedekind_domain r /\ prime_ideal r p /\ prime_ideal r q /\ q SUBSET p
    ==> q = {ring_0 r} \/ q = p"
    (MESON_TAC [DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL, MAXIMAL_AMONG_PRIME_IDEALS, PSUBSET])

  let PID_IMP_DEDEKIND ← prove
    r"!r:A ring. PID r ==> dedekind_domain r"
    (SIMP_TAC [dedekind_domain, PID_IMP_INTEGRAL_DOMAIN, PID_IMP_NOETHERIAN_RING, PID_IMP_INTEGRALLY_CLOSED, PID_MAXIMAL_EQ_PRIME_IDEAL])

  let FIELD_IMP_DEDEKIND ← prove
    r"!r:A ring. field r ==> dedekind_domain r"
    (SIMP_TAC [FIELD_IMP_PID, PID_IMP_DEDEKIND])

  let DEDEKIND_INTEGER_RING ← prove
    r"dedekind_domain integer_ring"
    (SIMP_TAC [PID_INTEGER_RING, PID_IMP_DEDEKIND])

  let INTEGRALLY_CLOSED_DIVIDES_IDEAL ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"!r:B ring hx u hg w ha hy.
          ring_mul r ha u = ring_1 r /\ ring_mul r hx hg = ring_mul r ha hy
          ==> ring_mul r (ring_mul r hx u) (ring_mul r hg w) =
              ring_mul r hy w"
    let r2 ← RING_RULE q1
    let q3 ← q r"(h:A->B) y"
    let q4 ← q r"(h:A->B) a"
    let q5 ← q r"w:B"
    let q6 ← q r"(h:A->B) g"
    let q7 ← q r"u:B"
    let q8 ← q r"(h:A->B) x"
    let q9 ← q r"r':B ring"
    let v10 ← ISPECL [q9, q8, q7, q6, q5, q4, q3] r2
    let q11 ← q r"c:A->A"
    let q12 ← q r"y:A"
    let q13 ← q r"(y:A) IN ring_carrier r"
    let q14 ← q r"y:A"
    let q15 ← q r"g:A"
    let q16 ← q r"g:A"
    let q17 ← q r"b:A"
    let q18 ← q r"\g:A. ring_mul r' ((h:A->B) g) w"
    let q19 ← q r"t:A->bool"
    let q20 ← q r"ring_mul r' ((h:A->B) x) u"
    let q21 ← q r"h:A->B"
    let q22 ← q r"r':B ring"
    let q23 ← q r"r:A ring"
    let v24 ← ISPECL [q23, q22, q21, q20, q19, q18] INTEGRAL_ELEMENT_FINITE_MODULE
    let q25 ← q r"t:A->bool"
    let q26 ← q r"\i:A. ring_mul r (c i:A) i"
    let q27 ← q r"c:A->A"
    let q28 ← q r"c:A->A"
    let q29 ← q r"t:A->bool"
    let q30 ← q r"r:A ring"
    let v31 ← ISPECL [q30, q29] IDEAL_GENERATED_FINITE
    let q32 ← q r"!y. y IN ideal_generated r t
          ==> ?c. (!i. i IN t ==> c i IN ring_carrier r) /\
                  ring_mul r' ((h:A->B) y) w =
                  ring_sum r' t
                   (\i. ring_mul r' (h(c i)) (ring_mul r' (h i) w))"
    let q33 ← q r"!i:A. i IN t ==> i IN ring_carrier r"
    let q34 ← q r"!y. y IN ring_carrier r ==> (h:A->B) y IN ring_carrier r'"
    let p35 ← prove r"!r r' (h:A->B) t a b x u w.
        ring_homomorphism(r,r') h /\ FINITE t /\ t SUBSET ring_carrier r /\
        a IN ring_carrier r /\ x IN ring_carrier r /\
        b IN ideal_generated r t /\
        u IN ring_carrier r' /\ ring_mul r' (h a) u = ring_1 r' /\
        w IN ring_carrier r' /\ ring_mul r' (h b) w = ring_1 r'
        ==> (!y. y IN ideal_generated r t
                 ==> ?z. ring_mul r x y = ring_mul r a z /\
                         z IN ideal_generated r t)
            ==> integral_element (r,r') h (ring_mul r' (h x) u)" (REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_THEN (LABEL_TAC "mul") THEN SUBGOAL_THEN q34 ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN SUBGOAL_THEN q33 ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN q32 (LABEL_TAC "span") THENL [MP_TAC v31 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [FORALL_IN_GSPEC] THEN X_GEN_TAC q28 THEN DISCH_TAC THEN EXISTS_TAC q27 THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (MP_TAC o ((ISPECL [q26, q25]) o (MATCH_MP RING_HOMOMORPHISM_SUM))) THEN ASM_SIMP_TAC [RING_MUL] THEN DISCH_THEN SUBST1_TAC THEN wPart lhand (rand o rand) RING_SUM_RMUL THEN ASM_SIMP_TAC [o_THM, RING_MUL] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_SUM_EQ THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [o_THM, RING_MUL_ASSOC, (← MATCH_MP RING_HOMOMORPHISM_MUL th)])), ALL_TAC] THEN MP_TAC v24 THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_MUL] THEN CONJ_TAC THENL [REMOVE_THEN "span" (MP_TAC o (SPEC q17)) THEN ASM_REWRITE_TAC [], X_GEN_TAC q16 THEN DISCH_TAC THEN REMOVE_THEN "mul" (MP_TAC o (SPEC q15)) THEN ASM_SIMP_TAC [IDEAL_GENERATED_INC_GEN] THEN DISCH_THEN (X_CHOOSE_THEN q14 STRIP_ASSUME_TAC) THEN SUBGOAL_THEN q13 ASSUME_TAC THENL [ASM_MESON_TAC [IDEAL_GENERATED_SUBSET, SUBSET], ALL_TAC] THEN REMOVE_THEN "span" (MP_TAC o (SPEC q12)) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC q11 THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN ASM_REWRITE_TAC [] THEN MP_TAC v10 THEN DISCH_THEN (MATCH_MP_TAC o (REWRITE_RULE [IMP_IMP])) THEN ASM_SIMP_TAC [] THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← GSYM (← MATCH_MP RING_HOMOMORPHISM_MUL th))]))])
    let lemma := p35
    let q36 ← q r"!r:B ring hx u ha hc.
      ring_mul r ha u = ring_1 r /\ ring_mul r hx u = hc
      ==> hx = ring_mul r ha hc"
    let r37 ← RING_RULE q36
    let q38 ← q r"(h:A->A#A->bool) c"
    let q39 ← q r"(h:A->A#A->bool) a"
    let q40 ← q r"u:A#A->bool"
    let q41 ← q r"(h:A->A#A->bool) x"
    let q42 ← q r"r':(A#A->bool)ring"
    let v43 ← ISPECL [q42, q41, q40, q39, q38] r37
    let v44 ← REWRITE_RULE [IMP_CONJ] RING_MONOMORPHISM_INJECTIVE_EQ
    let q45 ← q r"ring_mul r a c:A"
    let q46 ← q r"x:A"
    let q47 ← q r"c:A"
    let q48 ← q r"c:A"
    let q49 ← q r"w:A#A->bool"
    let q50 ← q r"u:A#A->bool"
    let q51 ← q r"x:A"
    let q52 ← q r"b:A"
    let q53 ← q r"a:A"
    let q54 ← q r"t:A->bool"
    let q55 ← q r"h:A->A#A->bool"
    let q56 ← q r"r':(A#A->bool)ring"
    let q57 ← q r"r:A ring"
    let v58 ← ISPECL [q57, q56, q55, q54, q53, q52, q51, q50, q49] lemma
    let q59 ← q r"u:A#A->bool"
    let q60 ← q r"w:A#A->bool"
    let q61 ← q r"!y:A. y IN ring_carrier r ==> (h:A->A#A->bool) y IN ring_carrier r'"
    let q62 ← q r"h:A->A#A->bool"
    let q63 ← q r"r':(A#A->bool)ring"
    let q64 ← q r"r':(A#A->bool)ring"
    let q65 ← q r"fraction_ring r:(A#A->bool)ring"
    let q66 ← q r"h:A->A#A->bool"
    let q67 ← q r"ring_fractionate r {a:A | ring_regular r a}"
    let q68 ← q r"!c:A. c IN ring_carrier r /\ ~(c = ring_0 r)
          ==> ring_unit (fraction_ring r)
                (ring_fractionate r {a | ring_regular r a} c)"
    let q69 ← q r"r:A ring"
    let v70 ← ISPEC q69 RING_MONOMORPHISM_FRACTIONATE
    let q71 ← q r"ring_mul r x b = ring_0 r:A"
    let q72 ← q r"y:A"
    let q76 ← q r"b:A"
    let q77 ← q r"a:A = ring_0 r"
    let q78 ← q r"(b:A) IN ring_carrier r"
    let q79 ← q r"b:A"
    let q80 ← q r"!j z:A. ~(j = {z}) /\ z IN j ==> ?b. b IN j /\ ~(b = z)"
    let r81 ← SET_RULE q80
    let q82 ← q r"ring_0 r:A"
    let q83 ← q r"ideal_generated r t:A->bool"
    let v84 ← SPECL [q83, q82] r81
    let q85 ← q r"t:A->bool"
    prove
      r"!r j (a:A) x.
          integrally_closed r /\ finitely_generated_ideal r j /\
          ~(j = {ring_0 r}) /\ a IN ring_carrier r /\ x IN ring_carrier r /\
          IMAGE (ring_mul r x) j SUBSET IMAGE (ring_mul r a) j
          ==> ring_divides r a x"
      (REPEAT GEN_TAC THEN REWRITE_TAC [finitely_generated_ideal, IMP_CONJ, LEFT_IMP_EXISTS_THM] THEN DISCH_TAC THEN X_GEN_TAC q85 THEN REPLICATE_TAC 2 DISCH_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REPLICATE_TAC 3 DISCH_TAC THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_IMAGE] THEN DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [integrally_closed]))) THEN MP_TAC v84 THEN ASM_SIMP_TAC [IN_RING_IDEAL_0, RING_IDEAL_IDEAL_GENERATED] THEN DISCH_THEN (X_CHOOSE_THEN q79 STRIP_ASSUME_TAC) THEN SUBGOAL_THEN q78 ASSUME_TAC THENL [ASM_MESON_TAC [IDEAL_GENERATED_SUBSET, SUBSET], ALL_TAC] THEN ASM_CASES_TAC q77 THENL [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC [RING_DIVIDES_ZERO] THEN FIRST_X_ASSUM (MP_TAC o ((SPEC q76) o (checkM (fun z73 => (do let z74 ← (do let z75 ← (pure z73); pure (concl z75)); pure (is_forall z74)))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN q72 STRIP_ASSUME_TAC) THEN SUBGOAL_THEN q71 MP_TAC THENL [ASM_MESON_TAC [RING_MUL_LZERO, IDEAL_GENERATED_SUBSET, SUBSET], ASM_SIMP_TAC [INTEGRAL_DOMAIN_MUL_EQ_0]], ALL_TAC] THEN MP_TAC v70 THEN FIRST_X_ASSUM (MP_TAC o (CONJUNCT2 o (GEN_REWRITE_RULE id [integrally_closed]))) THEN SUBGOAL_THEN q68 MP_TAC THENL [REPEAT STRIP_TAC THEN REWRITE_TAC [fraction_ring] THEN MATCH_MP_TAC RING_UNIT_FRACTIONATE THEN ASM_SIMP_TAC [RING_MULTSYS_REGULAR, IN_ELIM_THM, INTEGRAL_DOMAIN_REGULAR], ALL_TAC] THEN SPEC_TAC (q67, q66) THEN SPEC_TAC (q65, q64) THEN X_GEN_TAC q63 THEN X_GEN_TAC q62 THEN DISCH_THEN (LABEL_TAC "unit") THEN REPEAT DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN SUBGOAL_THEN q61 ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN REMOVE_THEN "unit" (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"a:A") th) THEN MP_TAC (← SPEC (← q r"b:A") th))) THEN ASM_REWRITE_TAC [ring_unit] THEN DISCH_THEN ((X_CHOOSE_THEN q60 STRIP_ASSUME_TAC) o CONJUNCT2) THEN DISCH_THEN ((X_CHOOSE_THEN q59 STRIP_ASSUME_TAC) o CONJUNCT2) THEN MP_TAC v58 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => tactic_of do pure (FIRST_X_ASSUM (MP_TAC o (← do let c := th; pure (fun th => MATCH_MP th c))))) THEN REWRITE_TAC [IN_IMAGE, ring_divides] THEN DISCH_THEN (X_CHOOSE_THEN q48 STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC q47 THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (MP_TAC o ((SPECL [q46, q45]) o (MATCH_MP v44))) THEN ASM_SIMP_TAC [RING_MUL] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL th)])) THEN MP_TAC v43 THEN ASM_SIMP_TAC [IMP_IMP])

  let IDEAL_PRODUCT_MONOMIAL_VAR ← prove
    r"!r p:A->bool.
        ring_ideal r p
        ==> ideal_product r (monomial_vars(monomial_var p))
                            (\q. ideal_pow r q (monomial_var p q)) = p"
    (SIMP_TAC [MONOMIAL_VARS_VAR, IDEAL_PRODUCT_SING, RING_IDEAL_IDEAL_POW] THEN SIMP_TAC [monomial_var, IDEAL_POW_1])

  let IDEAL_PRODUCT_PRIME_MONOMIAL_MUL ← prove
    r"!r e f:(A->bool)->num.
        monomial {p | prime_ideal r p /\ ~(p = {ring_0 r})} e /\
        monomial {p | prime_ideal r p /\ ~(p = {ring_0 r})} f
        ==> ideal_product r (monomial_vars(monomial_mul e f))
                            (\p. ideal_pow r p (monomial_mul e f p)) =
            ideal_prod r
              (ideal_product r (monomial_vars e) (\p. ideal_pow r p (e p)))
              (ideal_product r (monomial_vars f) (\p. ideal_pow r p (f p)))"
    (REWRITE_TAC [monomial, SUBSET, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC IDEAL_PRODUCT_MONOMIAL_MUL THEN ASM_MESON_TAC [IN_UNION, PRIME_IMP_RING_IDEAL])

  let DEDEKIND_IDEAL_QUOTIENT_MAXIMAL_PSUBSET ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!x:A s t. x IN s /\ s SUBSET t ==> x IN t")
    let r2 ← TAUT (← q r"p /\ ~q ==> ~(p <=> q)")
    let r3 ← SET_RULE (← q r"!x:A->bool s. s SUBSET x INSERT s")
    let r4 ← SET_RULE (← q r"!x:A->bool s. x INSERT (s DELETE x) = x INSERT s")
    let r5 ← SET_RULE (← q r"!s P. s SUBSET {x:A->bool | P x} <=> !x. x IN s ==> P x")
    let r6 ← SET_RULE (← q r"!s t:A->bool. s SUBSET t /\ ~(t SUBSET s) ==> s PSUBSET t")
    prove
      r"!r m (a:A).
          dedekind_domain r /\ maximal_ideal r m /\ a IN m /\ ~(a = ring_0 r)
          ==> ideal_generated r {a} PSUBSET
              ideal_quotient r (ideal_generated r {a}) m"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN MATCH_MP_TAC r6 THEN ASM_SIMP_TAC [IDEAL_SUBSET_IDEAL_QUOTIENT, RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IMP_SUBSET] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"!n b. ring_ideal r b /\
            ideal_prod r (ideal_pow r m n) b SUBSET ideal_generated r {a:A}
            ==> b SUBSET ideal_generated r {a}") ASSUME_TAC THENL [INDUCT_TAC THENL [SIMP_TAC [IDEAL_POW_0, IDEAL_PROD_CARRIER_LEFT, IMP_CONJ], ALL_TAC] THEN X_GEN_TAC (← q r"b:A->bool") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"ideal_prod r b (m:A->bool)"))) THEN ANTS_TAC THENL [REWRITE_TAC [RING_IDEAL_IDEAL_PROD] THEN UNDISCH_TAC (← q r"ideal_prod r (ideal_pow r m (SUC n)) b SUBSET
                     ideal_generated r {a:A}") THEN ASM_SIMP_TAC [IDEAL_POW_SUC, IDEAL_PROD_AC, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_POW, RING_IDEAL_IDEAL_PROD], DISCH_TAC] THEN TRANS_TAC SUBSET_TRANS (← q r"ideal_quotient r (ideal_generated r {a:A}) m") THEN ASM_SIMP_TAC [SUBSET_IDEAL_QUOTIENT, RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_generated r {a:A}")] NOETHERIAN_PRIME_PRODUCT_SUBSET) THEN ASM_SIMP_TAC [DEDEKIND_IMP_NOETHERIAN, RING_IDEAL_IDEAL_GENERATED] THEN REWRITE_TAC [monomial, (← GSYM CONJ_ASSOC), r5] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"e:(A->bool)->num") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "vars") MP_TAC))) THEN SUBGOAL_THEN (← q r"!p:A->bool. p IN m INSERT monomial_vars e
                              ==> ring_ideal r (ideal_pow r p (e p))") ASSUME_TAC THENL [REWRITE_TAC [FORALL_IN_INSERT] THEN ASM_MESON_TAC [RING_IDEAL_IDEAL_POW, PRIME_IMP_RING_IDEAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_product r (monomial_vars e) (\p:A->bool. ideal_pow r p (e p)) =
      ideal_prod r (ideal_pow r m (e m))
       (ideal_product r (monomial_vars e DELETE m) (\p. ideal_pow r p (e p)))") SUBST1_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"monomial_vars e DELETE (m:A->bool)"), (← q r"\p:A->bool. ideal_pow r p (e p)"), (← q r"m:A->bool")] IDEAL_PRODUCT_INSERT) THEN ASM_SIMP_TAC [FINITE_DELETE, IN_DELETE, IN_INSERT] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [r4] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC IDEAL_PRODUCT_SUPERSET THEN ASM_REWRITE_TAC [FINITE_INSERT, r3] THEN SIMP_TAC [IN_INSERT, monomial_vars, IN_ELIM_THM, IDEAL_POW_0], ALL_TAC] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ideal_product r (monomial_vars e DELETE m)
        (\p:A->bool. ideal_pow r p (e p)) SUBSET ideal_generated r {a}") ASSUME_TAC THENL [FIRST_X_ASSUM (MATCH_MP_TAC o (SPEC (← q r"e(m:A->bool):num"))) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_PRODUCT], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"monomial_vars e DELETE (m:A->bool)"), (← q r"\p:A->bool. ideal_pow r p (e p)")] IDEAL_PRODUCT_SUBSET_PRIME_IDEAL) THEN ASM_SIMP_TAC [MAXIMAL_IMP_PRIME_IDEAL, FINITE_DELETE, IN_DELETE, IN_INSERT] THEN MATCH_MP_TAC r2 THEN CONJ_TAC THENL [TRANS_TAC SUBSET_TRANS (← q r"ideal_generated r {a:A}") THEN ASM_SIMP_TAC [IDEAL_GENERATED_MINIMAL, SING_SUBSET], REWRITE_TAC [NOT_EXISTS_THM] THEN X_GEN_TAC (← q r"p:A->bool") THEN STRIP_TAC] THEN USE_THEN "vars" (STRIP_ASSUME_TAC o (← do let c := (← ASSUME (← q r"(p:A->bool) IN monomial_vars e")); pure (fun th => MATCH_MP th c))) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"p:A->bool")] DEDEKIND_KRULL_DIMENSION_ONE) THEN UNDISCH_TAC (← q r"ideal_pow r p (e p) SUBSET (m:A->bool)") THEN ASM_SIMP_TAC [IDEAL_POW_SUBSET_PRIME_IDEAL, MAXIMAL_IMP_PRIME_IDEAL, PRIME_IDEAL_IMP_SUBSET] THEN SUBGOAL_THEN (← q r"(a:A) IN p") MP_TAC THENL [MATCH_MP_TAC r1 THEN EXISTS_TAC (← q r"ideal_generated r {a:A}") THEN ASM_REWRITE_TAC [IN_IDEAL_GENERATED_SELF], MAP_EVERY UNDISCH_TAC [(← q r"(a:A) IN m"), (← q r"~(a:A = ring_0 r)")] THEN SET_TAC []])

  let DEDEKIND_MAXIMAL_IDEAL_INVERSE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r6 ← SET_RULE (← q r"!a z s:A->bool. a IN s /\ ~(a = z) ==> ~(s = {z})")
    let r7 ← TAUT (← q r"~p ==> p ==> q")
    let r8 ← SET_RULE (← q r"!s t:A->bool. s = t ==> s SUBSET t")
    let r9 ← SET_RULE (← q r"!s t:A->bool. s PSUBSET t ==> ~(t SUBSET s)")
    prove
      r"!r m (a:A).
          dedekind_domain r /\ maximal_ideal r m /\ a IN m /\ ~(a = ring_0 r)
          ==> ?q. ring_ideal r q /\ ideal_generated r {a} SUBSET q /\
                  ideal_prod r m q = ideal_generated r {a} /\
                  !j. ring_ideal r j /\ ~(j = {ring_0 r})
                      ==> ~(ideal_prod r j q SUBSET
                            ideal_prod r (ideal_generated r {a}) j)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_RING_IDEAL)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN)) THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← SPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"a:A")] DEDEKIND_IDEAL_QUOTIENT_MAXIMAL_PSUBSET) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o (MATCH_MP r9)) THEN EXISTS_TAC (← q r"ideal_quotient r (ideal_generated r {a:A}) m") THEN ABBREV_TAC (← q r"q = ideal_quotient r (ideal_generated r {a:A}) m") THEN SUBGOAL_THEN (← q r"ring_ideal r (q:A->bool) /\ ideal_generated r {a} SUBSET q") STRIP_ASSUME_TAC THENL [EXPAND_TAC "q" THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_QUOTIENT, IDEAL_SUBSET_IDEAL_QUOTIENT, RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"!j. ring_ideal r j /\ ~(j = {ring_0 r})
          ==> ~(ideal_prod r j q SUBSET
                ideal_prod r (ideal_generated r {a:A}) j)") (LABEL_TAC "strict") THENL [X_GEN_TAC (← q r"j:A->bool") THEN STRIP_TAC THEN DISCH_TAC THEN UNDISCH_TAC (← q r"~(q SUBSET ideal_generated r {a:A})") THEN REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [IN_IDEAL_GENERATED_SING_EQ] THEN MATCH_MP_TAC INTEGRALLY_CLOSED_DIVIDES_IDEAL THEN EXISTS_TAC (← q r"j:A->bool") THEN ASM_SIMP_TAC [DEDEKIND_IMP_INTEGRALLY_CLOSED, (← GSYM IDEAL_PROD_SCALE)] THEN CONJ_TAC THENL [ASM_MESON_TAC [noetherian_ring, DEDEKIND_IMP_NOETHERIAN], ALL_TAC] THEN TRANS_TAC SUBSET_TRANS (← q r"ideal_prod r j (q:A->bool)") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ideal_prod r (ideal_generated r {x}) j =
                    ideal_prod r j (ideal_generated r {x:A})") SUBST1_TAC THENL [MATCH_MP_TAC IDEAL_PROD_COMM THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, IDEAL_GENERATED_SUBSET], MATCH_MP_TAC IDEAL_PROD_MONO THEN ASM_SIMP_TAC [SUBSET_REFL, IDEAL_GENERATED_MINIMAL, SING_SUBSET]], ASM_REWRITE_TAC []] THEN SUBGOAL_THEN (← q r"ideal_prod r m q SUBSET ideal_generated r {a:A}") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_generated r {a:A}"), (← q r"m:A->bool"), (← q r"q:A->bool")] SUBSET_IDEAL_QUOTIENT) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IMP_SUBSET, SUBSET_REFL] THEN ASM_SIMP_TAC [IDEAL_PROD_COMM, RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"a:A"), (← q r"ideal_prod r m q:A->bool")] IDEAL_PROD_PRINCIPAL_FACTOR) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_PROD] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"l:A->bool") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"m SUBSET (l:A->bool)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"a:A"), (← q r"m:A->bool"), (← q r"l:A->bool")] IDEAL_PROD_PRINCIPAL_SUBSET_CANCEL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN TRANS_TAC SUBSET_TRANS (← q r"ideal_prod r m (ideal_generated r {a:A})") THEN ASM_SIMP_TAC [IDEAL_PROD_MONO, SUBSET_REFL] THEN MATCH_MP_TAC r8 THEN MATCH_MP_TAC IDEAL_PROD_COMM THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, IDEAL_GENERATED_SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"l = (m:A->bool) \/ l = ring_carrier r") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"maximal_ideal r (m:A->bool)") THEN REWRITE_TAC [maximal_ideal, PROPER_IDEAL_ALT, NOT_EXISTS_THM] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"l:A->bool")) o CONJUNCT2)) THEN ASM_REWRITE_TAC [PSUBSET] THEN MESON_TAC [], REMOVE_THEN "strict" (MP_TAC o (SPEC (← q r"m:A->bool"))) THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC [SUBSET_REFL] THEN MATCH_MP_TAC r7 THEN MATCH_MP_TAC r6 THEN EXISTS_TAC (← q r"a:A") THEN ASM_REWRITE_TAC [], FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun z1 => (do let z5 ← (do let z2 ← (do let z3 ← (pure z1); pure (concl z3)); liftExcept (rand z2)); let z4 ← (q r"ideal_prod r m (q:A->bool)"); pure (z4 == z5)))))) THEN ASM_SIMP_TAC [IDEAL_PROD_CARRIER, RING_IDEAL_IDEAL_GENERATED]])

  let IDEAL_PROD_PRINCIPAL_COFACTOR ← prove
    r"!r (a:A) j k q l.
        integral_domain r /\ a IN ring_carrier r /\ ~(a = ring_0 r) /\
        ring_ideal r j /\ ring_ideal r k /\ ring_ideal r q /\ ring_ideal r l /\
        ideal_prod r k q = ideal_generated r {a} /\
        ideal_prod r (ideal_generated r {a}) l = ideal_prod r j q
        ==> ideal_prod r k l = j"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"a:A"), (← q r"ideal_prod r k l:A->bool"), (← q r"j:A->bool")] IDEAL_PROD_PRINCIPAL_CANCEL) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_PROD] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN UNDISCH_THEN (← q r"ideal_prod r k q = ideal_generated r {a:A}") (fun th => tactic_of do pure (GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [(← SYM th)])) THEN UNDISCH_THEN (← q r"ideal_prod r (ideal_generated r {a:A}) l = ideal_prod r j q") (MP_TAC o (AP_TERM (← q r"ideal_prod r (k:A->bool)"))) THEN ASM_SIMP_TAC [IDEAL_PROD_AC, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_PROD])

  let DEDEKIND_IDEAL_FACTORIZATION_EXISTS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!a z s:A->bool. a IN s /\ ~(a = z) ==> ~(s = {z})")
    let r2 ← SET_RULE (← q r"!s t:A->bool. s = t ==> s SUBSET t")
    let r7 ← SET_RULE (← q r"!j z:A. ~(j = {z}) ==> z IN j ==> ?a. a IN j /\ ~(a = z)")
    prove
      r"!r j:A->bool.
          dedekind_domain r /\ ring_ideal r j /\ ~(j = {ring_0 r})
          ==> ?e. monomial {p | prime_ideal r p /\ ~(p = {ring_0 r})} e /\
                  ideal_product r (monomial_vars e) (\p. ideal_pow r p (e p)) =
                  j"
      (GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN MATCH_MP_TAC NOETHERIAN_RING_INDUCT THEN ASM_SIMP_TAC [DEDEKIND_IMP_NOETHERIAN] THEN X_GEN_TAC (← q r"j:A->bool") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ind")) THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"j = ring_carrier(r:A ring)") THENL [EXISTS_TAC (← q r"monomial_1:(A->bool)->num") THEN ASM_REWRITE_TAC [MONOMIAL_1, MONOMIAL_VARS_1, IDEAL_PRODUCT_EMPTY], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool")] MAXIMAL_SUPERIDEAL_EXISTS) THEN ASM_REWRITE_TAC [PROPER_IDEAL_ALT] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"m:A->bool") STRIP_ASSUME_TAC) THEN FIRST_ASSUM (MP_TAC o (MATCH_MP r7)) THEN ANTS_TAC THENL [ASM_SIMP_TAC [IN_RING_IDEAL_0], STRIP_TAC] THEN SUBGOAL_THEN (← q r"(a:A) IN m /\ a IN ring_carrier r") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"a:A")] DEDEKIND_MAXIMAL_IDEAL_INVERSE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"q:A->bool") STRIP_ASSUME_TAC) THEN FIRST_X_ASSUM ((LABEL_TAC "strict") o (checkM (fun z4 => (do let z5 ← (do let z6 ← (pure z4); pure (concl z6)); pure (is_forall z5))))) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"a:A"), (← q r"ideal_prod r j q:A->bool")] IDEAL_PROD_PRINCIPAL_FACTOR) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_PROD] THEN DISCH_THEN (fun z3 => tactic_of do pure (MP_TAC (← (do pure (Prod.fst (← (do pure (← EQ_IMP_RULE z3)))))))) THEN ANTS_TAC THENL [UNDISCH_THEN (← q r"ideal_prod r m q = ideal_generated r {a:A}") (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [IDEAL_PROD_MONO, SUBSET_REFL], DISCH_THEN (X_CHOOSE_THEN (← q r"l:A->bool") STRIP_ASSUME_TAC)] THEN SUBGOAL_THEN (← q r"ideal_prod r m l = (j:A->bool)") ASSUME_TAC THENL [MATCH_MP_TAC IDEAL_PROD_PRINCIPAL_COFACTOR THEN MAP_EVERY EXISTS_TAC [(← q r"a:A"), (← q r"q:A->bool")] THEN ASM_SIMP_TAC [DEDEKIND_IMP_INTEGRAL_DOMAIN, MAXIMAL_IMP_RING_IDEAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"(j:A->bool) PSUBSET l") ASSUME_TAC THENL [REWRITE_TAC [PSUBSET] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"a:A"), (← q r"j:A->bool"), (← q r"l:A->bool")] IDEAL_PROD_PRINCIPAL_SUBSET_CANCEL) THEN ASM_SIMP_TAC [DEDEKIND_IMP_INTEGRAL_DOMAIN] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN TRANS_TAC SUBSET_TRANS (← q r"ideal_prod r j (ideal_generated r {a:A})") THEN ASM_SIMP_TAC [IDEAL_PROD_MONO, SUBSET_REFL] THEN MATCH_MP_TAC r2 THEN MATCH_MP_TAC IDEAL_PROD_COMM THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, IDEAL_GENERATED_SUBSET], DISCH_THEN SUBST_ALL_TAC THEN REMOVE_THEN "strict" (MP_TAC o (SPEC (← q r"l:A->bool"))) THEN ASM_REWRITE_TAC [SUBSET_REFL]], ALL_TAC] THEN REMOVE_THEN "ind" (MP_TAC o (SPEC (← q r"l:A->bool"))) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"e:(A->bool)->num") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"prime_ideal r m /\ ~(m = {ring_0(r:A ring)})") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [MAXIMAL_IMP_PRIME_IDEAL] THEN MATCH_MP_TAC r1 THEN EXISTS_TAC (← q r"a:A") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN EXISTS_TAC (← q r"monomial_mul (monomial_var m) (e:(A->bool)->num)") THEN ASM_SIMP_TAC [MONOMIAL_MUL, MONOMIAL_VAR, IN_ELIM_THM, PRIME_IMP_RING_IDEAL, IDEAL_PRODUCT_PRIME_MONOMIAL_MUL, IDEAL_PRODUCT_MONOMIAL_VAR])

  let DEDEKIND_IDEAL_INDUCT ← prove
    r"!r:A ring P.
        dedekind_domain r /\ P (ring_carrier r) /\
        (!p j. prime_ideal r p /\ ~(p = {ring_0 r}) /\
               ring_ideal r j /\ ~(j = {ring_0 r}) /\ P j
               ==> P (ideal_prod r p j))
        ==> !j. ring_ideal r j /\ ~(j = {ring_0 r}) ==> P j"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC (← q r"j:A->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool")] DEDEKIND_IDEAL_FACTORIZATION_EXISTS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"e:(A->bool)->num") (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN)) THEN SPEC_TAC ((← q r"e:(A->bool)->num"), (← q r"e:(A->bool)->num")) THEN MATCH_MP_TAC MONOMIAL_INDUCT THEN CONJ_TAC THENL [ASM_REWRITE_TAC [MONOMIAL_VARS_1, IDEAL_PRODUCT_EMPTY], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"e:(A->bool)->num"), (← q r"p:A->bool")] THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"monomial {p | prime_ideal r p /\ ~(p = {ring_0 r})}
             (monomial_var (p:A->bool))") ASSUME_TAC THENL [REWRITE_TAC [MONOMIAL_VAR] THEN ASM_REWRITE_TAC [IN_ELIM_THM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"monomial_var (p:A->bool)"), (← q r"e:(A->bool)->num")] IDEAL_PRODUCT_PRIME_MONOMIAL_MUL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [IDEAL_PRODUCT_MONOMIAL_VAR, PRIME_IMP_RING_IDEAL] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"!q. q IN monomial_vars (e:(A->bool)->num)
        ==> prime_ideal r q /\ ~(q = {ring_0 r})") ASSUME_TAC THENL [RULE_ASSUM_TAC (REWRITE_RULE [monomial]) THEN ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"FINITE(monomial_vars (e:(A->bool)->num))") ASSUME_TAC THENL [ASM_MESON_TAC [monomial], ALL_TAC] THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_PRODUCT, RING_IDEAL_IDEAL_POW, PRIME_IMP_RING_IDEAL, IDEAL_PRODUCT_EQ_ZERO, IDEAL_POW_EQ_ZERO] THEN REWRITE_TAC [NOT_EXISTS_THM] THEN X_GEN_TAC (← q r"q:A->bool") THEN ASM_CASES_TAC (← q r"(q:A->bool) IN monomial_vars e") THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"q:A->bool"))) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_SIMP_TAC [IDEAL_POW_EQ_ZERO, PRIME_IMP_RING_IDEAL])

  let DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r6 ← SET_RULE (← q r"!a z s:A->bool. a IN s /\ ~(a = z) ==> ~(s = {z})")
    let r7 ← SET_RULE (← q r"!x:A s t. x IN s /\ s SUBSET t ==> x IN t")
    let r8 ← SET_RULE (← q r"!j z:A. ~(j = {z}) /\ z IN j ==> ?a. a IN j /\ ~(a = z)")
    prove
      r"!r (j:A->bool).
      dedekind_domain r /\ ring_ideal r j /\ ~(j = {ring_0 r})
      ==> ?k a. ring_ideal r k /\ ~(k = {ring_0 r}) /\
                a IN ring_carrier r /\ ~(a = ring_0 r) /\
                ideal_prod r j k = ideal_generated r {a}"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool")] DEDEKIND_IDEAL_FACTORIZATION_EXISTS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"e:(A->bool)->num") (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN)) THEN SPEC_TAC ((← q r"e:(A->bool)->num"), (← q r"e:(A->bool)->num")) THEN MATCH_MP_TAC MONOMIAL_INDUCT THEN CONJ_TAC THENL [MAP_EVERY EXISTS_TAC [(← q r"ring_carrier r:A->bool"), (← q r"ring_1 r:A")] THEN SUBGOAL_THEN (← q r"ideal_generated r {ring_1 r:A} = ring_carrier r") SUBST1_TAC THENL [SIMP_TAC [IDEAL_GENERATED_SING_EQ_CARRIER, RING_1, RING_UNIT_1], ALL_TAC] THEN ASM_SIMP_TAC [MONOMIAL_VARS_1, IDEAL_PRODUCT_EMPTY, IDEAL_PROD_CARRIER, RING_IDEAL_CARRIER, RING_1, (← GSYM trivial_ring), INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING, INTEGRAL_DOMAIN_NONTRIVIAL], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"e:(A->bool)->num"), (← q r"p:A->bool")] THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"k:A->bool") (X_CHOOSE_THEN (← q r"a:A") STRIP_ASSUME_TAC)) STRIP_ASSUME_TAC)) THEN MP_TAC (← SPECL [(← q r"p:A->bool"), (← q r"ring_0 r:A")] r8) THEN ANTS_TAC THENL [ASM_SIMP_TAC [IN_RING_IDEAL_0, PRIME_IMP_RING_IDEAL], DISCH_THEN (X_CHOOSE_THEN (← q r"b:A") STRIP_ASSUME_TAC)] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool"), (← q r"b:A")] DEDEKIND_MAXIMAL_IDEAL_INVERSE) THEN ANTS_TAC THENL [ASM_SIMP_TAC [DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL], DISCH_THEN (X_CHOOSE_THEN (← q r"q:A->bool") STRIP_ASSUME_TAC)] THEN SUBGOAL_THEN (← q r"(b:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [PRIME_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"(b:A) IN q") ASSUME_TAC THENL [MATCH_MP_TAC r7 THEN EXISTS_TAC (← q r"ideal_generated r {b:A}") THEN ASM_REWRITE_TAC [IN_IDEAL_GENERATED_SELF], ALL_TAC] THEN MAP_EVERY EXISTS_TAC [(← q r"ideal_prod r q (k:A->bool)"), (← q r"ring_mul r b a:A")] THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_PROD, RING_MUL, IDEAL_PROD_EQ_ZERO, INTEGRAL_DOMAIN_MUL_EQ_0] THEN CONJ_TAC THENL [MATCH_MP_TAC r6 THEN EXISTS_TAC (← q r"b:A") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [IDEAL_PRODUCT_PRIME_MONOMIAL_MUL, MONOMIAL_VAR, IN_ELIM_THM, IDEAL_PRODUCT_MONOMIAL_VAR, PRIME_IMP_RING_IDEAL, (← GSYM IDEAL_PROD_PRINCIPAL)] THEN UNDISCH_THEN (← q r"ideal_prod r p q = ideal_generated r {b:A}") (SUBST1_TAC o SYM) THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun z1 => (do let z5 ← (do let z2 ← (do let z3 ← (pure z1); pure (concl z3)); liftExcept (rand z2)); let z4 ← (q r"ideal_generated r {a:A}"); pure (z4 == z5)))))) THEN ASM_SIMP_TAC [IDEAL_PROD_AC, RING_IDEAL_IMP_SUBSET, PRIME_IMP_RING_IDEAL, RING_IDEAL_IDEAL_PRODUCT, RING_IDEAL_IDEAL_PROD])

  let DEDEKIND_IDEAL_INVERTIBLE ← prove
    r"!r j:A->bool.
        dedekind_domain r /\ ring_ideal r j /\ ~(j = {ring_0 r})
        ==> ?c n u v.
              c IN ring_carrier r /\ ~(c = ring_0 r) /\
              (!i. i < n:num
                   ==> u i IN j /\ v i IN ring_carrier r /\
                       !a. a IN j ==> ring_divides r c (ring_mul r a (v i))) /\
              ring_sum r {i | i < n} (\i. ring_mul r (u i) (v i)) = c"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool")] DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"l:A->bool"), (← q r"c:A")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"l:A->bool")] IDEAL_PROD_EXPLICIT) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (AP_TERM (← q r"(IN) (c:A)"))) THEN ASM_REWRITE_TAC [IN_IDEAL_GENERATED_SELF, IN_ELIM_THM] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"n:num") (X_CHOOSE_THEN (← q r"u:num->A") (X_CHOOSE_THEN (← q r"v:num->A") (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))))) THEN MAP_EVERY EXISTS_TAC [(← q r"c:A"), (← q r"n:num"), (← q r"u:num->A"), (← q r"v:num->A")] THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(u:num->A) i IN j /\ (v:num->A) i IN l") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [], ASM_REWRITE_TAC []] THEN SUBGOAL_THEN (← q r"(v:num->A) i IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ASM_REWRITE_TAC []] THEN X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN ASM_SIMP_TAC [(← GSYM IN_IDEAL_GENERATED_SING_EQ)] THEN UNDISCH_TAC (← q r"ideal_prod r j l = ideal_generated r {c:A}") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_PROD THEN ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET])

  let DEDEKIND_IDEAL_PROD_SUBSET_CANCEL ← prove
    r"!r j k l:A->bool.
        dedekind_domain r /\ ring_ideal r j /\ ~(j = {ring_0 r}) /\
        ring_ideal r k /\ ring_ideal r l
        ==> (ideal_prod r j k SUBSET ideal_prod r j l <=> k SUBSET l)"
    (REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC [IDEAL_PROD_MONO, SUBSET_REFL] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool")] DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"j':A->bool"), (← q r"a:A")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"a:A"), (← q r"k:A->bool"), (← q r"l:A->bool")] IDEAL_PROD_PRINCIPAL_SUBSET_CANCEL) THEN ASM_SIMP_TAC [DEDEKIND_IMP_INTEGRAL_DOMAIN] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN UNDISCH_THEN (← q r"ideal_prod r j j' = ideal_generated r {a:A}") (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j':A->bool"), (← q r"j':A->bool"), (← q r"ideal_prod r j k:A->bool"), (← q r"ideal_prod r j l:A->bool")] IDEAL_PROD_MONO) THEN ASM_REWRITE_TAC [SUBSET_REFL] THEN ASM_SIMP_TAC [IDEAL_PROD_AC, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_PROD])

  let DEDEKIND_IDEAL_PROD_CANCEL ← prove
    r"!r:A ring j k l.
        dedekind_domain r /\ ring_ideal r j /\ ~(j = {ring_0 r}) /\
        ring_ideal r k /\ ring_ideal r l /\
        ideal_prod r j k = ideal_prod r j l
        ==> k = l"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"k:A->bool"), (← q r"l:A->bool")] DEDEKIND_IDEAL_PROD_SUBSET_CANCEL) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"l:A->bool"), (← q r"k:A->bool")] DEDEKIND_IDEAL_PROD_SUBSET_CANCEL) THEN ASM_REWRITE_TAC [SUBSET_REFL] THEN SET_TAC [])

  let DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES ← prove
    r"!r:A ring j k.
        dedekind_domain r /\ ring_ideal r j /\ ring_ideal r k
        ==> (j SUBSET k <=>
             ?l. ring_ideal r l /\ ideal_prod r k l = j)"
    (REPEAT STRIP_TAC THEN EQ_TAC THENL [DISCH_TAC, DISCH_THEN (X_CHOOSE_THEN (← q r"l:A->bool") (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM))) THEN ASM_SIMP_TAC [IDEAL_PROD_SUBSET_LEFT, RING_IDEAL_IMP_SUBSET]] THEN ASM_CASES_TAC (← q r"k = {ring_0 r:A}") THENL [EXISTS_TAC (← q r"ring_carrier r:A->bool") THEN ASM_SIMP_TAC [RING_IDEAL_CARRIER, IDEAL_PROD_LZERO, SUBSET_REFL] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool")] IN_RING_IDEAL_0) THEN ASM SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:A->bool")] DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"k':A->bool"), (← q r"a:A")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"a:A"), (← q r"ideal_prod r j k':A->bool")] IDEAL_PROD_PRINCIPAL_FACTOR) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_PROD] THEN DISCH_THEN (fun z1 => tactic_of do pure (MP_TAC (← (do pure (Prod.fst (← (do pure (← EQ_IMP_RULE z1)))))))) THEN ANTS_TAC THENL [UNDISCH_THEN (← q r"ideal_prod r k k' = ideal_generated r {a:A}") (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [IDEAL_PROD_MONO, SUBSET_REFL], MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"l:A->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IDEAL_PROD_PRINCIPAL_COFACTOR THEN MAP_EVERY EXISTS_TAC [(← q r"a:A"), (← q r"k':A->bool")] THEN ASM_SIMP_TAC [DEDEKIND_IMP_INTEGRAL_DOMAIN]])

  let DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!s t:A->bool. s = t ==> s SUBSET t")
    prove
      r"!r j k:A->bool.
          dedekind_domain r /\ ring_ideal r j /\ ring_ideal r k /\ j SUBSET k
          ==> ideal_prod r k (ideal_quotient r j k) = j"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_ideal r (ideal_quotient r j (k:A->bool))") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IDEAL_QUOTIENT, RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"k:A->bool"), (← q r"ideal_quotient r j k:A->bool")] SUBSET_IDEAL_QUOTIENT) THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, SUBSET_REFL] THEN ASM_SIMP_TAC [IDEAL_PROD_COMM, RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"k:A->bool")] DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"l:A->bool") STRIP_ASSUME_TAC) THEN FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN MATCH_MP_TAC IDEAL_PROD_MONO THEN REWRITE_TAC [SUBSET_REFL] THEN ASM_SIMP_TAC [SUBSET_IDEAL_QUOTIENT, RING_IDEAL_IMP_SUBSET] THEN MATCH_MP_TAC r1 THEN MATCH_MP_TAC IDEAL_PROD_COMM THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET])

  -- @@RETURN BEGIN
  return { dedekind_domain, DEDEKIND_IMP_INTEGRAL_DOMAIN, DEDEKIND_IMP_NOETHERIAN,
           DEDEKIND_IMP_INTEGRALLY_CLOSED, DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL,
           DEDEKIND_MAXIMAL_EQ_PRIME_IDEAL, DEDEKIND_KRULL_DIMENSION_ONE,
           PID_IMP_DEDEKIND, FIELD_IMP_DEDEKIND, DEDEKIND_INTEGER_RING,
           INTEGRALLY_CLOSED_DIVIDES_IDEAL, IDEAL_PRODUCT_MONOMIAL_VAR,
           IDEAL_PRODUCT_PRIME_MONOMIAL_MUL, DEDEKIND_IDEAL_QUOTIENT_MAXIMAL_PSUBSET,
           DEDEKIND_MAXIMAL_IDEAL_INVERSE, IDEAL_PROD_PRINCIPAL_COFACTOR,
           DEDEKIND_IDEAL_FACTORIZATION_EXISTS, DEDEKIND_IDEAL_INDUCT,
           DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE, DEDEKIND_IDEAL_INVERTIBLE,
           DEDEKIND_IDEAL_PROD_SUBSET_CANCEL, DEDEKIND_IDEAL_PROD_CANCEL,
           DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES, DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- dedekind.ml phrases from line 847 to 1562                              -/
/- ---------------------------------------------------------------------- -/

structure Dedekind02 where
  -- @@FIELDS
  DEDEKIND_IDEAL_QUOTIENT_CANCEL : thm
  DEDEKIND_IDEAL_MEMBER_PRINCIPAL_MULTIPLE : thm
  DEDEKIND_PRIMITIVE_MULTIPLE : thm
  DEDEKIND_IDEAL_POW_SUBSET : thm
  DEDEKIND_IDEAL_POW_EQ : thm
  DEDEKIND_PRIME_IDEAL_UNIFORMIZER : thm
  ideal_valuation : thm
  IDEAL_VALUATION_UNIQUE : thm
  IDEAL_VALUATION_CARRIER : thm
  IDEAL_PRODUCT_PRIME_MONOMIAL_DIVIDES : thm
  DEDEKIND_IDEAL_PRODUCT_SUBSET_POW : thm
  IDEAL_VALUATION_IDEAL_PRODUCT_MONOMIAL : thm
  DEDEKIND_IDEAL_FACTORIZATION : thm
  DEDEKIND_IDEAL_FACTORIZATION_UNIQUE : thm
  DEDEKIND_IDEAL_SUBSET_POW_VALUATION : thm
  IDEAL_VALUATION_EQ_0 : thm
  IDEAL_VALUATION_FINITE_SUPPORT : thm
  DEDEKIND_IDEAL_PRODUCT_PRIME_POW_UNIQUE : thm
  DEDEKIND_IDEAL_PRODUCT_PRIME_POWERS : thm
  IDEAL_VALUATION_IDEAL_PROD : thm
  IDEAL_VALUATION_PRINCIPAL_MUL : thm
  IDEAL_VALUATION_IDEAL_POW : thm
  IDEAL_VALUATION_PRINCIPAL_POW : thm
  IDEAL_VALUATION_IDEAL_PRODUCT : thm
  IDEAL_VALUATION_PRINCIPAL_PRODUCT : thm
  IDEAL_VALUATION_PRIME : thm
  DEDEKIND_IDEAL_SUBSET_VALUATION : thm
  DEDEKIND_IDEAL_EQ_VALUATION : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDedekind02 [HolBase] (D : DedekindDeps) (BDedekind01 : Dedekind01) :
    ExceptT String IO Dedekind02 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, REFUTE_THEN,
        SET_RULE, SET_TAC, TAUT, new_definition, .. } := D
  let { ADD_CLAUSES, ARITH, COMAXIMAL_IDEAL_POW, CONJ_ASSOC, CONTRAPOS_THM, EQ_TRANS,
        EXISTS_UNIQUE_THM, EXTENSION, FINITE_INDUCT_STRONG, FINITE_SUBSET,
        FORALL_IN_IMAGE, FUN_EQ_THM, IDEAL_GENERATED_EQ_0, IDEAL_GENERATED_INC,
        IDEAL_GENERATED_MINIMAL, IDEAL_GENERATED_SING_ALT, IDEAL_POW_0, IDEAL_POW_1,
        IDEAL_POW_ADD, IDEAL_POW_ANTIMONO, IDEAL_POW_EQ_ZERO, IDEAL_POW_PRINCIPAL,
        IDEAL_POW_SUBSET_PRIME_IDEAL, IDEAL_POW_SUC, IDEAL_PRODUCT_EMPTY,
        IDEAL_PRODUCT_EQ, IDEAL_PRODUCT_EQ_ZERO, IDEAL_PRODUCT_INSERT,
        IDEAL_PRODUCT_PRINCIPAL, IDEAL_PRODUCT_SUBSET, IDEAL_PRODUCT_SUPERSET,
        IDEAL_PROD_ASSOC, IDEAL_PROD_CARRIER, IDEAL_PROD_CARRIER_LEFT, IDEAL_PROD_COMM,
        IDEAL_PROD_IDEAL_GENERATED, IDEAL_PROD_MINIMAL, IDEAL_PROD_PRINCIPAL,
        IDEAL_PROD_SETADD_RDISTRIB, IDEAL_PROD_SUBSET_LEFT, IDEAL_PROD_SUBSET_RIGHT,
        IMP_CONJ, IMP_CONJ_ALT, INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING, IN_ELIM_THM,
        IN_IDEAL_GENERATED_SELF, IN_IDEAL_GENERATED_SING_EQ, IN_RING_IDEAL_0,
        IN_RING_IDEAL_RMUL, IN_SING, LE, LEFT_IMP_EXISTS_THM, LE_0, LE_ANTISYM,
        LE_REFL, LT_EXISTS, MAXIMAL_IDEAL_COMAXIMAL, .. } := D.core1
  let { MONOMIAL_DIV, MONOMIAL_DIV_LMUL, MONOMIAL_INDUCT, MONOMIAL_MUL, MONOMIAL_VAR,
        MONOMIAL_VARS_1, MONO_EXISTS, MULT_CLAUSES, NOT_EXISTS_THM, NOT_FORALL_THM,
        NOT_IMP, NOT_LE, NSUM_CLAUSES, ONE, PRIME_IDEAL_IMP_PSUBSET,
        PRIME_IDEAL_IMP_SUBSET, PRIME_IMP_PROPER_IDEAL, PRIME_IMP_RING_IDEAL,
        PROPER_IDEAL, PROPER_IDEAL_ALT, PSUBSET, RIGHT_EXISTS_IMP_THM,
        RIGHT_FORALL_IMP_THM, RING_0, RING_1, RING_ADD, RING_ADD_RDISTRIB,
        RING_IDEAL_CARRIER, RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_POW,
        RING_IDEAL_IDEAL_PROD, RING_IDEAL_IDEAL_PRODUCT, RING_IDEAL_IDEAL_QUOTIENT,
        RING_IDEAL_IMP_SUBSET, RING_MUL, RING_MUL_ASSOC, RING_MUL_IN_IDEAL_PROD,
        RING_MUL_LNEG, RING_MUL_LZERO, RING_MUL_SYM, RING_NEG,
        RING_SETADD_SUBSET_IDEAL, SELECT_UNIQUE, SING_SUBSET, SKOLEM_THM, SUBSET,
        SUBSET_ANTISYM, SUBSET_ANTISYM_EQ, SUBSET_IDEAL_QUOTIENT, SUBSET_REFL,
        SUBSET_TRANS, monomial, monomial_1, monomial_divides, monomial_mul,
        monomial_var, monomial_vars, num_CASES, prime_ideal, proper_ideal,
        ring_divides, ring_ideal, trivial_ring, .. } := D.core2
  let { DEDEKIND_IDEAL_FACTORIZATION_EXISTS, DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE,
        DEDEKIND_IDEAL_PROD_SUBSET_CANCEL, DEDEKIND_IMP_INTEGRAL_DOMAIN,
        DEDEKIND_KRULL_DIMENSION_ONE, DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL,
        IDEAL_PRODUCT_MONOMIAL_VAR, IDEAL_PRODUCT_PRIME_MONOMIAL_MUL, .. } := BDedekind01
  -- @@SCOPE END

  let DEDEKIND_IDEAL_QUOTIENT_CANCEL ← prove
    r"!r j k:A->bool.
        dedekind_domain r /\ ring_ideal r j /\ ring_ideal r k /\
        ~(k = {ring_0 r})
        ==> ideal_quotient r (ideal_prod r j k) k = j"
    (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"q = ideal_quotient r (ideal_prod r j k) (k:A->bool)") THEN SUBGOAL_THEN (← q r"ring_ideal r (q:A->bool)") ASSUME_TAC THENL [EXPAND_TAC "q" THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_QUOTIENT, RING_IDEAL_IDEAL_PROD, RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_prod r j k:A->bool"), (← q r"k:A->bool")] SUBSET_IDEAL_QUOTIENT) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_PROD, RING_IDEAL_IMP_SUBSET] THEN DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"q:A->bool") th) THEN MP_TAC (← SPEC (← q r"j:A->bool") th))) THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, SUBSET_REFL] THEN DISCH_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:A->bool"), (← q r"q:A->bool"), (← q r"j:A->bool")] DEDEKIND_IDEAL_PROD_SUBSET_CANCEL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN UNDISCH_TAC (← q r"ideal_prod r q k SUBSET ideal_prod r j (k:A->bool)") THEN ASM_SIMP_TAC [IDEAL_PROD_COMM, RING_IDEAL_IMP_SUBSET])

  let DEDEKIND_IDEAL_MEMBER_PRINCIPAL_MULTIPLE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (q ==> r) ==> (p <=> q) ==> r")
    prove
      r"!r p t (c:A) u.
          dedekind_domain r /\ ring_ideal r p /\ t SUBSET ring_carrier r /\
          ~(ideal_generated r t = {ring_0 r}) /\ c IN ring_carrier r /\
          ideal_prod r p (ideal_generated r t) = ideal_generated r {c} /\
          u IN ring_carrier r
          ==> (u IN p <=>
               !y. y IN t ==> ring_mul r y u IN ideal_generated r {c})"
      (REPEAT STRIP_TAC THEN EQ_TAC THENL [REPEAT STRIP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); pure (is_eq z2)) then (do let z7 ← (q r"ideal_generated r {c:A}"); let z6 ← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); liftExcept (rand z4)); pure (z6 == z7)) else pure false))))) THEN SUBGOAL_THEN (← q r"(y:A) IN ring_carrier r") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul r y u = ring_mul r u (y:A)") SUBST1_TAC THENL [MATCH_MP_TAC RING_MUL_SYM THEN ASM_REWRITE_TAC [], MATCH_MP_TAC RING_MUL_IN_IDEAL_PROD THEN ASM_SIMP_TAC [IDEAL_GENERATED_INC]], DISCH_TAC] THEN ABBREV_TAC (← q r"b = ideal_generated r (t:A->bool)") THEN SUBGOAL_THEN (← q r"ring_ideal r (b:A->bool)") ASSUME_TAC THENL [EXPAND_TAC "b" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"!y. y IN b ==> ring_mul r y u IN ideal_generated r {c:A}") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"b SUBSET {y | y IN ring_carrier r /\
                      ring_mul r y u IN ideal_generated r {c:A}}") MP_TAC THENL [ALL_TAC, SET_TAC []] THEN EXPAND_TAC "b" THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"{c:A}")] RING_IDEAL_IDEAL_GENERATED) THEN REWRITE_TAC [ring_ideal, SUBSET, IN_ELIM_THM] THEN STRIP_TAC THEN ASM_SIMP_TAC [RING_0, RING_NEG, RING_ADD, RING_MUL, RING_MUL_LZERO, RING_MUL_LNEG, RING_ADD_RDISTRIB, (← GSYM RING_MUL_ASSOC)], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"b:A->bool"), (← q r"ideal_generated r {u:A}"), (← q r"p:A->bool")] DEDEKIND_IDEAL_PROD_SUBSET_CANCEL) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [ALL_TAC, DISCH_TAC THEN FIRST_X_ASSUM (MATCH_MP_TAC o (REWRITE_RULE [SUBSET])) THEN ASM_REWRITE_TAC [IN_IDEAL_GENERATED_SELF]] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"b:A->bool"), (← q r"p:A->bool")] IDEAL_PROD_COMM) THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IDEAL_PROD_MINIMAL THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN MAP_EVERY X_GEN_TAC [(← q r"y:A"), (← q r"v:A")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"u:A")] IDEAL_GENERATED_SING_ALT) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => tactic_of do pure (UNDISCH_TAC (← q r"(v:A) IN ideal_generated r {u}") THEN REWRITE_TAC [th, IN_ELIM_THM])) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"s:A") STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(y:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul r y (ring_mul r u s) = ring_mul r (ring_mul r y u) (s:A)") SUBST1_TAC THENL [MATCH_MP_TAC RING_MUL_ASSOC THEN ASM_REWRITE_TAC [], MATCH_MP_TAC IN_RING_IDEAL_RMUL THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED]])

  let DEDEKIND_PRIMITIVE_MULTIPLE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (q ==> r) ==> (p <=> q) ==> r")
    let r2 ← TAUT (← q r"p /\ ~q <=> ~(p ==> q)")
    let r6 ← SET_RULE (← q r"!P s (b:K->A) q z i0.
        P /\ (!i. i IN s ==> b i IN q) /\ i0 IN s /\ ~(b i0 = z)
        ==> P /\ (!i. i IN s ==> b i IN q) /\ ~(q = {z})")
    prove
      r"!r j s (b:K->A).
          dedekind_domain r /\ ring_ideal r j /\ ~(j = ring_carrier r) /\
          (!i. i IN s ==> b i IN ring_carrier r) /\
          (?i. i IN s /\ ~(b i = ring_0 r))
          ==> ?t e u. t IN ring_carrier r /\
                      e IN ring_carrier r /\ ~(e = ring_0 r) /\
                      (!i. i IN s
                           ==> u i IN ring_carrier r /\
                               ring_mul r (b i) t = ring_mul r e (u i)) /\
                      ?i. i IN s /\ ~(u i IN j)"
      (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"q = ideal_generated r (IMAGE (b:K->A) s)") THEN SUBGOAL_THEN (← q r"ring_ideal r (q:A->bool) /\ (!i. i IN s ==> (b:K->A) i IN q) /\
      ~(q = {ring_0 r})") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r6 THEN EXISTS_TAC (← q r"i:K") THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "q" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN ASM SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"q:A->bool")] DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"c:A->bool"), (← q r"e:A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"?t:A. t IN c /\ ~(t IN ideal_prod r c j)") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"c:A->bool"), (← q r"ring_carrier r:A->bool"), (← q r"j:A->bool")] DEDEKIND_IDEAL_PROD_SUBSET_CANCEL) THEN ASM_SIMP_TAC [IDEAL_PROD_CARRIER, RING_IDEAL_CARRIER] THEN FIRST_ASSUM (MP_TAC o ((MATCH_MP RING_IDEAL_IMP_SUBSET) o (checkM (fun th => (do let z5 ← (q r"ring_ideal r (j:A->bool)"); let z4 ← (do let z3 ← (pure th); pure (concl z3)); pure (z4 == z5)))))) THEN UNDISCH_TAC (← q r"~(j = ring_carrier r:A->bool)") THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(t:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN MAP_EVERY EXISTS_TAC [(← q r"t:A"), (← q r"e:A")] THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"?u:K->A. !i. i IN s
                   ==> u i IN ring_carrier r /\
                       ring_mul r ((b:K->A) i) t = ring_mul r e (u i)") MP_TAC THENL [REWRITE_TAC [(← GSYM SKOLEM_THM), RIGHT_EXISTS_IMP_THM] THEN X_GEN_TAC (← q r"x:K") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"q:A->bool"), (← q r"c:A->bool"), (← q r"(b:K->A) x"), (← q r"t:A")] RING_MUL_IN_IDEAL_PROD) THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, IN_IDEAL_GENERATED_SING_EQ, ring_divides] THEN MESON_TAC [], MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"u:K->A") THEN STRIP_TAC] THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [r2, (← GSYM NOT_FORALL_THM)] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"~((t:A) IN ideal_prod r c j)") THEN REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"q:A->bool"), (← q r"ideal_generated r {t:A}"), (← q r"ideal_prod r c j:A->bool")] DEDEKIND_IDEAL_PROD_SUBSET_CANCEL) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_PROD] THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC [IN_IDEAL_GENERATED_SELF, SUBSET]] THEN wPart rand (lhand o rand) IDEAL_PROD_ASSOC THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET] THEN DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "q" THEN wPart lhand (lhand o rand) IDEAL_PROD_IDEAL_GENERATED THEN ANTS_TAC THENL [REWRITE_TAC [SING_SUBSET, SUBSET, FORALL_IN_IMAGE] THEN ASM_SIMP_TAC [], DISCH_THEN SUBST1_TAC] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IDEAL_PROD_MINIMAL THEN REWRITE_TAC [RING_IDEAL_IDEAL_PROD, IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_IMAGE, IN_SING] THEN X_GEN_TAC (← q r"x:K") THEN DISCH_TAC THEN X_GEN_TAC (← q r"y:A") THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [] THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_PROD THEN ASM_SIMP_TAC [IN_IDEAL_GENERATED_SELF])

  let DEDEKIND_IDEAL_POW_SUBSET ← prove
    r"!r j:A->bool m n.
        dedekind_domain r /\ ring_ideal r j /\
        ~(j = {ring_0 r}) /\ ~(j = ring_carrier r)
        ==> (ideal_pow r j m SUBSET ideal_pow r j n <=> n <= m)"
    (REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC [IDEAL_POW_ANTIMONO, RING_IDEAL_IMP_SUBSET] THEN ONCE_REWRITE_TAC [(← GSYM CONTRAPOS_THM)] THEN REWRITE_TAC [NOT_LE, LT_EXISTS] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"d:num") SUBST1_TAC) THEN ASM_SIMP_TAC [IDEAL_POW_ADD, RING_IDEAL_IMP_SUBSET] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_pow r j m:A->bool"), (← q r"ring_carrier r:A->bool"), (← q r"ideal_pow r j (SUC d):A->bool")] DEDEKIND_IDEAL_PROD_SUBSET_CANCEL) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, RING_IDEAL_CARRIER, IDEAL_POW_EQ_ZERO, DEDEKIND_IMP_INTEGRAL_DOMAIN, IDEAL_PROD_CARRIER] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [IDEAL_POW_SUC] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"~(j = ring_carrier(r:A ring))") THEN REWRITE_TAC [] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET] THEN TRANS_TAC SUBSET_TRANS (← q r"ideal_prod r j (ideal_pow r j d):A->bool") THEN ASM_SIMP_TAC [IDEAL_PROD_SUBSET_LEFT, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_POW])

  let DEDEKIND_IDEAL_POW_EQ ← prove
    r"!r j:A->bool m n.
        dedekind_domain r /\ ring_ideal r j /\
        ~(j = {ring_0 r}) /\ ~(j = ring_carrier r)
        ==> (ideal_pow r j m = ideal_pow r j n <=> m = n)"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [(← GSYM SUBSET_ANTISYM_EQ)] THEN ASM_SIMP_TAC [DEDEKIND_IDEAL_POW_SUBSET] THEN ARITH_TAC)

  let DEDEKIND_PRIME_IDEAL_UNIFORMIZER ← prove
    r"!r p:A->bool.
        dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r})
        ==> ?t. t IN p /\ ~(t IN ideal_pow r p 2)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool"), (← q r"1:num"), (← q r"2:num")] DEDEKIND_IDEAL_POW_SUBSET) THEN ASM_SIMP_TAC [IDEAL_POW_1, PRIME_IMP_RING_IDEAL, ARITH] THEN ANTS_TAC THENL [ASM_MESON_TAC [PRIME_IMP_PROPER_IDEAL, proper_ideal, PSUBSET], SET_TAC []])

  let ideal_valuation ← new_definition
    r"ideal_valuation (r:A ring) (p:A->bool) (j:A->bool) =
  @n. j SUBSET ideal_pow r p n /\ ~(j SUBSET ideal_pow r p (SUC n))"

  let IDEAL_VALUATION_UNIQUE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"~(m = n) ==> SUC m <= n \/ SUC n <= m")
    prove
      r"!r p (j:A->bool) n.
          ring_ideal r p /\
          j SUBSET ideal_pow r p n /\ ~(j SUBSET ideal_pow r p (SUC n))
          ==> ideal_valuation r p j = n"
      (REPEAT STRIP_TAC THEN REWRITE_TAC [ideal_valuation] THEN MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC (← q r"m:num") THEN EQ_TAC THEN SIMP_TAC [] THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN REFUTE_THEN (DISJ_CASES_TAC o (MATCH_MP r1)) THEN ASM_MESON_TAC [IDEAL_POW_ANTIMONO, RING_IDEAL_IMP_SUBSET, SUBSET_TRANS])

  let IDEAL_VALUATION_CARRIER ← prove
    r"!r p:A->bool.
        ring_ideal r p /\ ~(p = ring_carrier r)
        ==> ideal_valuation r p (ring_carrier r) = 0"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC IDEAL_VALUATION_UNIQUE THEN ASM_SIMP_TAC [IDEAL_POW_0, IDEAL_POW_1, SUBSET_REFL, (← GSYM ONE)] THEN ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET_ANTISYM])

  let IDEAL_PRODUCT_PRIME_MONOMIAL_DIVIDES ← prove
    r"!r e f:(A->bool)->num.
        monomial {p | prime_ideal r p /\ ~(p = {ring_0 r})} e /\
        monomial {p | prime_ideal r p /\ ~(p = {ring_0 r})} f /\
        monomial_divides f e
        ==> ideal_product r (monomial_vars e) (\p. ideal_pow r p (e p)) SUBSET
            ideal_product r (monomial_vars f) (\p. ideal_pow r p (f p))"
    (REPEAT STRIP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (MATCH_MP MONOMIAL_DIV_LMUL))) THEN ASM_SIMP_TAC [IDEAL_PRODUCT_PRIME_MONOMIAL_MUL, MONOMIAL_DIV] THEN SIMP_TAC [IDEAL_PROD_SUBSET_LEFT, RING_IDEAL_IDEAL_PRODUCT, RING_IDEAL_IMP_SUBSET])

  let DEDEKIND_IDEAL_PRODUCT_SUBSET_POW ← prove
    r"!r p (e:(A->bool)->num) n.
        dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
        monomial {q | prime_ideal r q /\ ~(q = {ring_0 r})} e
        ==> (ideal_product r (monomial_vars e) (\q. ideal_pow r q (e q))
             SUBSET ideal_pow r p n <=> n <= e p)"
    (GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN REPEAT DISCH_TAC THEN MATCH_MP_TAC MONOMIAL_INDUCT THEN CONJ_TAC THENL [REWRITE_TAC [MONOMIAL_VARS_1, IDEAL_PRODUCT_EMPTY, monomial_1, LE] THEN X_GEN_TAC (← q r"n:num") THEN ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [IDEAL_POW_0, SUBSET_REFL] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool"), (← q r"p:A->bool"), (← q r"n:num")] IDEAL_POW_SUBSET_PRIME_IDEAL) THEN ASM_SIMP_TAC [PRIME_IDEAL_IMP_SUBSET, SUBSET_REFL] THEN ASM_MESON_TAC [SUBSET_TRANS, PRIME_IDEAL_IMP_PSUBSET, PSUBSET, SUBSET_ANTISYM], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"e:(A->bool)->num"), (← q r"q:A->bool")] THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN ASM_SIMP_TAC [IDEAL_PRODUCT_PRIME_MONOMIAL_MUL, MONOMIAL_VAR, IN_ELIM_THM, IDEAL_PRODUCT_MONOMIAL_VAR, PRIME_IMP_RING_IDEAL] THEN REWRITE_TAC [monomial_mul, monomial_var] THEN ABBREV_TAC (← q r"k = ideal_product r (monomial_vars e)
          (\q:A->bool. ideal_pow r q (e q))") THEN SUBGOAL_THEN (← q r"ring_ideal r (k:A->bool)") ASSUME_TAC THENL [EXPAND_TAC "k" THEN REWRITE_TAC [RING_IDEAL_IDEAL_PRODUCT], ALL_TAC] THEN ASM_CASES_TAC (← q r"p:A->bool = q") THENL [FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN REWRITE_TAC [] THEN X_GEN_TAC (← q r"n:num") THEN STRUCT_CASES_TAC (← SPEC (← q r"n:num") num_CASES) THEN ASM_SIMP_TAC [IDEAL_POW_0, LE_0, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_PROD] THEN ASM_SIMP_TAC [IDEAL_POW_SUC, DEDEKIND_IDEAL_PROD_SUBSET_CANCEL, RING_IDEAL_IDEAL_POW, PRIME_IMP_RING_IDEAL] THEN ARITH_TAC, ASM_REWRITE_TAC [ADD_CLAUSES] THEN X_GEN_TAC (← q r"n:num") THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (SPEC (← q r"n:num")))) THEN EQ_TAC THEN DISCH_TAC THENL [ALL_TAC, TRANS_TAC SUBSET_TRANS (← q r"k:A->bool") THEN ASM_SIMP_TAC [IDEAL_PROD_SUBSET_RIGHT, PRIME_IDEAL_IMP_SUBSET]]] THEN SUBGOAL_THEN (← q r"ring_setadd r q (ideal_pow r p n) = ring_carrier(r:A ring)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"q:A->bool"), (← q r"p:A->bool"), (← q r"1"), (← q r"n:num")] COMAXIMAL_IDEAL_POW) THEN ASM_SIMP_TAC [IDEAL_POW_1, PRIME_IMP_RING_IDEAL] THEN DISCH_THEN MATCH_MP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"q:A->bool"), (← q r"p:A->bool")] MAXIMAL_IDEAL_COMAXIMAL) THEN ASM_SIMP_TAC [DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL, PRIME_IMP_RING_IDEAL] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"q:A->bool"), (← q r"p:A->bool")] DEDEKIND_KRULL_DIMENSION_ONE) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"q:A->bool"), (← q r"ideal_pow r p n:A->bool"), (← q r"k:A->bool")] IDEAL_PROD_SETADD_RDISTRIB) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, RING_IDEAL_IDEAL_POW, RING_IDEAL_IMP_SUBSET, IDEAL_PROD_CARRIER_LEFT] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SETADD_SUBSET_IDEAL THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, PRIME_IMP_RING_IDEAL, IDEAL_PROD_SUBSET_LEFT, RING_IDEAL_IMP_SUBSET])

  let IDEAL_VALUATION_IDEAL_PRODUCT_MONOMIAL ← prove
    r"!r (e:(A->bool)->num) p.
     dedekind_domain r /\
     monomial {p | prime_ideal r p /\ ~(p = {ring_0 r})} e /\
     prime_ideal r p /\ ~(p = {ring_0 r})
     ==> ideal_valuation r p
           (ideal_product r (monomial_vars e)
                                 (\q. ideal_pow r q (e q))) = e p"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC IDEAL_VALUATION_UNIQUE THEN ASM_SIMP_TAC [DEDEKIND_IDEAL_PRODUCT_SUBSET_POW, PRIME_IMP_RING_IDEAL] THEN ARITH_TAC)

  let DEDEKIND_IDEAL_FACTORIZATION ← prove
    r"!r j:A->bool.
     dedekind_domain r /\ ring_ideal r j /\ ~(j = {ring_0 r})
     ==> FINITE {p | prime_ideal r p /\ ~(p = {ring_0 r}) /\ j SUBSET p} /\
         ideal_product r
           {p | prime_ideal r p /\ ~(p = {ring_0 r}) /\ j SUBSET p}
           (\p. ideal_pow r p (ideal_valuation r p j)) = j"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool")] DEDEKIND_IDEAL_FACTORIZATION_EXISTS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"e:(A->bool)->num") (CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM))) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [monomial, SUBSET, IN_ELIM_THM])) THEN SUBGOAL_THEN (← q r"{p | prime_ideal r p /\ ~(p = {ring_0 r}) /\
         ideal_product r (monomial_vars e) (\p. ideal_pow r p (e p))
         SUBSET p} =
    monomial_vars (e:(A->bool)->num)") SUBST1_TAC THENL [GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM, CONJ_ASSOC] THEN X_GEN_TAC (← q r"p:A->bool") THEN ASM_CASES_TAC (← q r"prime_ideal r (p:A->bool) /\ ~(p = {ring_0 r})") THEN ASM_REWRITE_TAC [] THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool"), (← q r"e:(A->bool)->num"), (← q r"1")] DEDEKIND_IDEAL_PRODUCT_SUBSET_POW) THEN ASM_SIMP_TAC [IDEAL_POW_1, PRIME_IMP_RING_IDEAL] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN REWRITE_TAC [monomial_vars, IN_ELIM_THM] THEN ARITH_TAC, ASM_MESON_TAC []], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IDEAL_PRODUCT_EQ THEN X_GEN_TAC (← q r"p:A->bool") THEN DISCH_TAC THEN REWRITE_TAC [] THEN AP_TERM_TAC THEN MATCH_MP_TAC IDEAL_VALUATION_IDEAL_PRODUCT_MONOMIAL THEN ASM_SIMP_TAC [])

  let DEDEKIND_IDEAL_FACTORIZATION_UNIQUE ← prove
    r"!r j:A->bool.
     dedekind_domain r /\ ring_ideal r j /\ ~(j = {ring_0 r})
     ==> ?!e. monomial {p | prime_ideal r p /\ ~(p = {ring_0 r})} e /\
              ideal_product r (monomial_vars e)
                                   (\p. ideal_pow r p (e p)) = j"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [EXISTS_UNIQUE_THM] THEN ASM_SIMP_TAC [DEDEKIND_IDEAL_FACTORIZATION_EXISTS] THEN MAP_EVERY X_GEN_TAC [(← q r"e:(A->bool)->num"), (← q r"f:(A->bool)->num")] THEN STRIP_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"p:A->bool") THEN ASM_CASES_TAC (← q r"prime_ideal r (p:A->bool) /\ ~(p = {ring_0 r})") THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"e:(A->bool)->num"), (← q r"p:A->bool")] IDEAL_VALUATION_IDEAL_PRODUCT_MONOMIAL) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"f:(A->bool)->num"), (← q r"p:A->bool")] IDEAL_VALUATION_IDEAL_PRODUCT_MONOMIAL) THEN ASM_REWRITE_TAC [] THEN ARITH_TAC, RULE_ASSUM_TAC (REWRITE_RULE [monomial, SUBSET, monomial_vars, IN_ELIM_THM]) THEN ASM_MESON_TAC []])

  let DEDEKIND_IDEAL_SUBSET_POW_VALUATION ← prove
    r"!r p (j:A->bool) n.
        dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
        ring_ideal r j /\ ~(j = {ring_0 r})
        ==> (j SUBSET ideal_pow r p n <=> n <= ideal_valuation r p j)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool")] DEDEKIND_IDEAL_FACTORIZATION_EXISTS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"e:(A->bool)->num") (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM))) THEN ASM_SIMP_TAC [IDEAL_VALUATION_IDEAL_PRODUCT_MONOMIAL, DEDEKIND_IDEAL_PRODUCT_SUBSET_POW])

  let IDEAL_VALUATION_EQ_0 ← prove
    r"!r p j:A->bool.
     dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
     ring_ideal r j /\ ~(j = {ring_0 r})
     ==> (ideal_valuation r p j = 0 <=> ~(j SUBSET p))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool"), (← q r"j:A->bool"), (← q r"1")] DEDEKIND_IDEAL_SUBSET_POW_VALUATION) THEN ASM_SIMP_TAC [IDEAL_POW_1, PRIME_IMP_RING_IDEAL] THEN DISCH_THEN SUBST1_TAC THEN ARITH_TAC)

  let IDEAL_VALUATION_FINITE_SUPPORT ← prove
    r"!r j:A->bool.
        dedekind_domain r /\ ring_ideal r j /\ ~(j = {ring_0 r})
        ==> FINITE {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
                        ~(ideal_valuation r P j = 0)}"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool")] DEDEKIND_IDEAL_FACTORIZATION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o CONJUNCT1) THEN MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] FINITE_SUBSET) THEN GEN_REWRITE_TAC id [SUBSET] THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"j:A->bool")] IDEAL_VALUATION_EQ_0) THEN ASM_REWRITE_TAC [])

  let DEDEKIND_IDEAL_PRODUCT_PRIME_POW_UNIQUE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"q /\ (q ==> p) ==> p /\ q")
    let r2 ← SET_RULE (← q r"ring_0 r IN j /\ ~(j = {ring_0 r}) /\ j SUBSET P
      ==> j SUBSET P /\ ~(P = {ring_0 r:A})")
    prove
      r"!r s (e:(A->bool)->num).
          dedekind_domain r /\ FINITE s /\
          (!P. P IN s ==> prime_ideal r P /\ ~(e P = 0)) /\
          ~(ideal_product r s (\P. ideal_pow r P (e P)) = {ring_0 r})
          ==> (!Q. Q IN s <=>
                   prime_ideal r Q /\ ~(Q = {ring_0 r}) /\
                   ideal_product r s (\P. ideal_pow r P (e P)) SUBSET Q) /\
              (!Q. prime_ideal r Q /\ ~(Q = {ring_0 r})
                   ==> ideal_valuation r Q
                         (ideal_product r s (\P. ideal_pow r P (e P))) =
                       if Q IN s then e Q else 0)"
      (REPEAT GEN_TAC THEN ABBREV_TAC (← q r"j = ideal_product r s (\P:A->bool. ideal_pow r P (e P))") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_ideal r (j:A->bool)") ASSUME_TAC THENL [EXPAND_TAC "j" THEN REWRITE_TAC [RING_IDEAL_IDEAL_PRODUCT], ALL_TAC] THEN SUBGOAL_THEN (← q r"!P:A->bool. P IN s ==> j SUBSET P /\ ~(P = {ring_0 r})") ASSUME_TAC THENL [X_GEN_TAC (← q r"P:A->bool") THEN DISCH_TAC THEN MATCH_MP_TAC r2 THEN ASM_SIMP_TAC [IN_RING_IDEAL_0] THEN EXPAND_TAC "j" THEN TRANS_TAC SUBSET_TRANS (← q r"ideal_pow r (P:A->bool) (e P)") THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:(A->bool)->bool"), (← q r"\P. ideal_pow r P ((e:(A->bool)->num) P)"), (← q r"P:A->bool")] IDEAL_PRODUCT_SUBSET) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW], MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"P:A->bool"), (← q r"(e:(A->bool)->num) P")] IDEAL_POW_SUBSET_PRIME_IDEAL) THEN ASM_SIMP_TAC [SUBSET_REFL, PRIME_IDEAL_IMP_SUBSET]], ALL_TAC] THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [X_GEN_TAC (← q r"Q:A->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"\P:A->bool. if P IN s then e P else 0"), (← q r"Q:A->bool")] IDEAL_VALUATION_IDEAL_PRODUCT_MONOMIAL) THEN SUBGOAL_THEN (← q r"monomial_vars (\P:A->bool. if P IN s then e P else 0) = s") ASSUME_TAC THENL [REWRITE_TAC [monomial_vars, EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC (← q r"P:A->bool") THEN COND_CASES_TAC THEN ASM_SIMP_TAC [], ASM_SIMP_TAC [monomial, SUBSET, IN_ELIM_THM]] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN EXPAND_TAC "j" THEN MATCH_MP_TAC IDEAL_PRODUCT_EQ THEN SIMP_TAC [], DISCH_TAC THEN X_GEN_TAC (← q r"Q:A->bool") THEN ASM_CASES_TAC (← q r"(Q:A->bool) IN s") THEN ASM_SIMP_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"Q:A->bool"), (← q r"j:A->bool")] IDEAL_VALUATION_EQ_0) THEN ASM_SIMP_TAC []])

  let DEDEKIND_IDEAL_PRODUCT_PRIME_POWERS ← prove
    r"!r t (e:(A->bool)->num).
        dedekind_domain r /\ FINITE t /\
        (!P. P IN t ==> prime_ideal r P /\ ~(P = {ring_0 r}))
        ==> ring_ideal r (ideal_product r t (\P. ideal_pow r P (e P))) /\
            ~(ideal_product r t (\P. ideal_pow r P (e P)) = {ring_0 r}) /\
            !Q. prime_ideal r Q /\ ~(Q = {ring_0 r})
                ==> ideal_valuation r Q
                      (ideal_product r t (\P. ideal_pow r P (e P))) =
                    if Q IN t then e Q else 0"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [RING_IDEAL_IDEAL_PRODUCT] THEN CONJ_TAC THENL [FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN)) THEN ASM_SIMP_TAC [IDEAL_PRODUCT_EQ_ZERO, RING_IDEAL_IDEAL_POW] THEN REWRITE_TAC [NOT_EXISTS_THM] THEN X_GEN_TAC (← q r"P:A->bool") THEN ASM_CASES_TAC (← q r"(P:A->bool) IN t") THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [IDEAL_POW_EQ_ZERO, PRIME_IMP_RING_IDEAL], ALL_TAC] THEN ABBREV_TAC (← q r"f = \P:A->bool. if P IN t then (e:(A->bool)->num) P else 0") THEN SUBGOAL_THEN (← q r"ideal_product r t (\P. ideal_pow r P ((e:(A->bool)->num) P)) =
    ideal_product r (monomial_vars f) (\P. ideal_pow r P (f P))") SUBST1_TAC THENL [TRANS_TAC EQ_TRANS (← q r"ideal_product r t (\P:A->bool. ideal_pow r P (f P))") THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_PRODUCT_EQ THEN EXPAND_TAC "f" THEN SIMP_TAC [], MATCH_MP_TAC IDEAL_PRODUCT_SUPERSET THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN EXPAND_TAC "f" THEN REWRITE_TAC [monomial_vars, SUBSET, IN_ELIM_THM] THEN CONJ_TAC THENL [MESON_TAC [], ALL_TAC] THEN SIMP_TAC [IDEAL_POW_0]], ALL_TAC] THEN SUBGOAL_THEN (← q r"monomial {P | prime_ideal r P /\ ~(P = {ring_0 r})} (f:(A->bool)->num)") ASSUME_TAC THENL [REWRITE_TAC [monomial, monomial_vars] THEN EXPAND_TAC "f" THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"t:(A->bool)->bool") THEN ASM_REWRITE_TAC [] THEN SET_TAC [], REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC []], ALL_TAC] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [IDEAL_VALUATION_IDEAL_PRODUCT_MONOMIAL] THEN EXPAND_TAC "f" THEN REWRITE_TAC [])

  let IDEAL_VALUATION_IDEAL_PROD ← prove
    r"!r p j k:A->bool.
     dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
     ring_ideal r j /\ ~(j = {ring_0 r}) /\
     ring_ideal r k /\ ~(k = {ring_0 r})
     ==> ideal_valuation r p (ideal_prod r j k) =
         ideal_valuation r p j + ideal_valuation r p k"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:A->bool")] DEDEKIND_IDEAL_FACTORIZATION_EXISTS) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool")] DEDEKIND_IDEAL_FACTORIZATION_EXISTS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"e:(A->bool)->num") (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM))) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"f:(A->bool)->num") (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM))) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"e:(A->bool)->num"), (← q r"f:(A->bool)->num")] IDEAL_PRODUCT_PRIME_MONOMIAL_MUL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [IDEAL_VALUATION_IDEAL_PRODUCT_MONOMIAL, MONOMIAL_MUL] THEN REWRITE_TAC [monomial_mul])

  let IDEAL_VALUATION_PRINCIPAL_MUL ← prove
    r"!r p a b:A.
        dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
        a IN ring_carrier r /\ ~(a = ring_0 r) /\
        b IN ring_carrier r /\ ~(b = ring_0 r)
        ==> ideal_valuation r p (ideal_generated r {ring_mul r a b}) =
            ideal_valuation r p (ideal_generated r {a}) +
            ideal_valuation r p (ideal_generated r {b})"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"a:A"), (← q r"b:A")] IDEAL_PROD_PRINCIPAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC IDEAL_VALUATION_IDEAL_PROD THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0])

  let IDEAL_VALUATION_IDEAL_POW ← prove
    r"!r p j:A->bool n.
        dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
        ring_ideal r j /\ ~(j = {ring_0 r})
        ==> ideal_valuation r p (ideal_pow r j n) =
            n * ideal_valuation r p j"
    (REPLICATE_TAC 3 GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN STRIP_TAC THEN INDUCT_TAC THENL [REWRITE_TAC [IDEAL_POW_0, MULT_CLAUSES] THEN MATCH_MP_TAC IDEAL_VALUATION_CARRIER THEN ASM_MESON_TAC [PRIME_IMP_PROPER_IDEAL, PROPER_IDEAL_ALT], ALL_TAC] THEN ASM_SIMP_TAC [IDEAL_POW_SUC, IDEAL_VALUATION_IDEAL_PROD, RING_IDEAL_IDEAL_POW, IDEAL_POW_EQ_ZERO, DEDEKIND_IMP_INTEGRAL_DOMAIN] THEN ARITH_TAC)

  let IDEAL_VALUATION_PRINCIPAL_POW ← prove
    r"!r p (a:A) n.
        dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
        a IN ring_carrier r /\ ~(a = ring_0 r)
        ==> ideal_valuation r p (ideal_generated r {ring_pow r a n}) =
            n * ideal_valuation r p (ideal_generated r {a})"
    (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [(← GSYM IDEAL_POW_PRINCIPAL)] THEN MATCH_MP_TAC IDEAL_VALUATION_IDEAL_POW THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0])

  let IDEAL_VALUATION_IDEAL_PRODUCT ← prove
    r"!r:A ring p (s:K->bool) f.
        dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
        FINITE s /\
        (!i. i IN s ==> ring_ideal r (f i) /\ ~(f i = {ring_0 r}))
        ==> ideal_valuation r p (ideal_product r s f) =
            nsum s (\i. ideal_valuation r p (f i))"
    (REPEAT GEN_TAC THEN REWRITE_TAC [IMP_CONJ] THEN REPLICATE_TAC 3 DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN)) THEN SPEC_TAC ((← q r"f:K->A->bool"), (← q r"f:K->A->bool")) THEN SPEC_TAC ((← q r"s:K->bool"), (← q r"s:K->bool")) THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL [GEN_TAC THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN REWRITE_TAC [IDEAL_PRODUCT_EMPTY, NSUM_CLAUSES] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool"), (← q r"ring_carrier r:A->bool")] IDEAL_VALUATION_EQ_0) THEN ASM_REWRITE_TAC [RING_IDEAL_CARRIER] THEN ANTS_TAC THENL [ASM_MESON_TAC [INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING, trivial_ring], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [SUBSET, NOT_FORALL_THM, NOT_IMP] THEN EXISTS_TAC (← q r"ring_1 r:A") THEN REWRITE_TAC [RING_1] THEN FIRST_X_ASSUM (MP_TAC o (GEN_REWRITE_RULE id [prime_ideal])) THEN SIMP_TAC [PROPER_IDEAL], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"a:K"), (← q r"t:K->bool")] THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "*") STRIP_ASSUME_TAC) THEN X_GEN_TAC (← q r"f:K->A->bool") THEN DISCH_TAC THEN REMOVE_THEN "*" (MP_TAC o (SPEC (← q r"f:K->A->bool"))) THEN ANTS_TAC THENL [ASM SET_TAC [], DISCH_TAC] THEN SUBGOAL_THEN (← q r"ring_ideal r ((f:K->A->bool) a) /\ ~(f a = {ring_0 r})") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_ideal r (ideal_product r t (f:K->A->bool)) /\
    ~(ideal_product r t f = {ring_0 r})") STRIP_ASSUME_TAC THENL [REWRITE_TAC [RING_IDEAL_IDEAL_PRODUCT] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"t:K->bool"), (← q r"f:K->A->bool")] IDEAL_PRODUCT_EQ_ZERO) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [ASM SET_TAC [], DISCH_THEN SUBST1_TAC THEN ASM SET_TAC []], ALL_TAC] THEN ASM_SIMP_TAC [IDEAL_PRODUCT_INSERT, NSUM_CLAUSES, IDEAL_VALUATION_IDEAL_PROD])

  let IDEAL_VALUATION_PRINCIPAL_PRODUCT ← prove
    r"!r p (x:K->A) s.
        dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
        FINITE s /\ (!i. i IN s ==> x i IN ring_carrier r /\ ~(x i = ring_0 r))
        ==> ideal_valuation r p (ideal_generated r {ring_product r s x}) =
            nsum s (\i. ideal_valuation r p (ideal_generated r {x i}))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:K->bool"), (← q r"x:K->A")] IDEAL_PRODUCT_PRINCIPAL) THEN ASM_SIMP_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC IDEAL_VALUATION_IDEAL_PRODUCT THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0, SING_SUBSET, IN_SING])

  let IDEAL_VALUATION_PRIME ← prove
    r"!r p q:A->bool.
        dedekind_domain r /\
        prime_ideal r p /\ ~(p = {ring_0 r}) /\
        prime_ideal r q /\ ~(q = {ring_0 r})
        ==> ideal_valuation r p q = if q = p then 1 else 0"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"monomial_var q:(A->bool)->num"), (← q r"p:A->bool")] IDEAL_VALUATION_IDEAL_PRODUCT_MONOMIAL) THEN ASM_SIMP_TAC [IDEAL_PRODUCT_MONOMIAL_VAR, PRIME_IMP_RING_IDEAL, MONOMIAL_VAR, IN_ELIM_THM] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [monomial_var] THEN MESON_TAC [])

  let DEDEKIND_IDEAL_SUBSET_VALUATION ← prove
    r"!r j k:A->bool.
     dedekind_domain r /\
     ring_ideal r j /\ ~(j = {ring_0 r}) /\
     ring_ideal r k /\ ~(k = {ring_0 r})
     ==> (j SUBSET k <=>
          !p. prime_ideal r p /\ ~(p = {ring_0 r})
              ==> ideal_valuation r p k <= ideal_valuation r p j)"
    (REPEAT STRIP_TAC THEN EQ_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool"), (← q r"j:A->bool"), (← q r"ideal_valuation r p (k:A->bool)")] DEDEKIND_IDEAL_SUBSET_POW_VALUATION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN TRANS_TAC SUBSET_TRANS (← q r"k:A->bool") THEN ASM_SIMP_TAC [DEDEKIND_IDEAL_SUBSET_POW_VALUATION, LE_REFL], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:A->bool")] DEDEKIND_IDEAL_FACTORIZATION_EXISTS) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool")] DEDEKIND_IDEAL_FACTORIZATION_EXISTS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"e:(A->bool)->num") (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM))) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"f:(A->bool)->num") (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM))) THEN ASM_SIMP_TAC [IDEAL_VALUATION_IDEAL_PRODUCT_MONOMIAL] THEN DISCH_TAC THEN MATCH_MP_TAC IDEAL_PRODUCT_PRIME_MONOMIAL_DIVIDES THEN ASM_REWRITE_TAC [monomial_divides] THEN X_GEN_TAC (← q r"p:A->bool") THEN ASM_CASES_TAC (← q r"prime_ideal r (p:A->bool) /\ ~(p = {ring_0 r})") THEN ASM_SIMP_TAC [] THEN UNDISCH_TAC (← q r"monomial {p:A->bool | prime_ideal r p /\ ~(p = {ring_0 r})} f") THEN REWRITE_TAC [monomial, SUBSET, monomial_vars, IN_ELIM_THM] THEN ASM_MESON_TAC [LE_0])

  let DEDEKIND_IDEAL_EQ_VALUATION ← prove
    r"!r j k:A->bool.
        dedekind_domain r /\
        ring_ideal r j /\ ~(j = {ring_0 r}) /\
        ring_ideal r k /\ ~(k = {ring_0 r})
        ==> (j = k <=>
             !p. prime_ideal r p /\ ~(p = {ring_0 r})
                 ==> ideal_valuation r p j = ideal_valuation r p k)"
    (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [(← GSYM SUBSET_ANTISYM_EQ)] THEN ASM_SIMP_TAC [DEDEKIND_IDEAL_SUBSET_VALUATION] THEN REWRITE_TAC [(← GSYM LE_ANTISYM)] THEN MESON_TAC [])

  -- @@RETURN BEGIN
  return { DEDEKIND_IDEAL_QUOTIENT_CANCEL, DEDEKIND_IDEAL_MEMBER_PRINCIPAL_MULTIPLE,
           DEDEKIND_PRIMITIVE_MULTIPLE, DEDEKIND_IDEAL_POW_SUBSET, DEDEKIND_IDEAL_POW_EQ,
           DEDEKIND_PRIME_IDEAL_UNIFORMIZER, ideal_valuation, IDEAL_VALUATION_UNIQUE,
           IDEAL_VALUATION_CARRIER, IDEAL_PRODUCT_PRIME_MONOMIAL_DIVIDES,
           DEDEKIND_IDEAL_PRODUCT_SUBSET_POW, IDEAL_VALUATION_IDEAL_PRODUCT_MONOMIAL,
           DEDEKIND_IDEAL_FACTORIZATION, DEDEKIND_IDEAL_FACTORIZATION_UNIQUE,
           DEDEKIND_IDEAL_SUBSET_POW_VALUATION, IDEAL_VALUATION_EQ_0,
           IDEAL_VALUATION_FINITE_SUPPORT, DEDEKIND_IDEAL_PRODUCT_PRIME_POW_UNIQUE,
           DEDEKIND_IDEAL_PRODUCT_PRIME_POWERS, IDEAL_VALUATION_IDEAL_PROD,
           IDEAL_VALUATION_PRINCIPAL_MUL, IDEAL_VALUATION_IDEAL_POW,
           IDEAL_VALUATION_PRINCIPAL_POW, IDEAL_VALUATION_IDEAL_PRODUCT,
           IDEAL_VALUATION_PRINCIPAL_PRODUCT, IDEAL_VALUATION_PRIME,
           DEDEKIND_IDEAL_SUBSET_VALUATION, DEDEKIND_IDEAL_EQ_VALUATION }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- dedekind.ml phrases from line 1574 to 2256                             -/
/- ---------------------------------------------------------------------- -/

structure Dedekind03 where
  -- @@FIELDS
  IDEAL_VALUATION_SETADD : thm
  IDEAL_VALUATION_INTER : thm
  DEDEKIND_IDEAL_PROD_EQ_INTER : thm
  DEDEKIND_FINITE_MAXIMAL_IDEALS_ABOVE : thm
  DEDEKIND_IDEAL_SUPERSET_PRIME_POW : thm
  DEDEKIND_RADICAL_IDEAL_VALUATION : thm
  DEDEKIND_RADICAL_IDEAL : thm
  DEDEKIND_QUOTIENT_RING_REDUCED : thm
  DEDEKIND_IDEAL_PROD_SETADD_INTER : thm
  DEDEKIND_IDEAL_PROD_INTER : thm
  DEDEKIND_IDEAL_COPRIME_PROD_POW : thm
  DEDEKIND_IDEALS_SUPERSET_PRIME_POW : thm
  DEDEKIND_IN_IDEAL_POW_VALUATION : thm
  DEDEKIND_RING_DIVIDES_VALUATION : thm
  IDEAL_VALUATION_PRINCIPAL_ADD : thm
  IDEAL_VALUATION_PRINCIPAL_ADD_STRICT : thm
  DEDEKIND_IDEAL_POW_MUL_CANCEL : thm
  DEDEKIND_PRIME_IDEAL_LOCAL_GENERATOR : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDedekind03 [HolBase] (D : DedekindDeps) (BDedekind01 : Dedekind01) (BDedekind02 : Dedekind02) :
    ExceptT String IO Dedekind03 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, RING_RULE,
        SET_RULE, SET_TAC, TAUT, num_CONV, .. } := D
  let { ADD_CLAUSES, ARITH_EQ, DE_MORGAN_THM, EXTENSION, FINITE_SUBSET, FINITE_UNION,
        HAS_SIZE_IMAGE_INJ, HAS_SIZE_NUMSEG_LE, IDEAL_GENERATED_EQ_0,
        IDEAL_GENERATED_INC, IDEAL_GENERATED_MINIMAL, IDEAL_GENERATED_MINIMAL_EQ,
        IDEAL_POW_1, IDEAL_POW_ANTIMONO, IDEAL_POW_CARRIER, IDEAL_POW_EQ_ZERO,
        IDEAL_POW_SUC, IDEAL_PROD_COMAXIMAL, IDEAL_PROD_EQ_ZERO, IDEAL_PROD_LZERO,
        IDEAL_PROD_MONO, IDEAL_PROD_RZERO, IDEAL_PROD_SUBSET_INTER,
        IDEAL_SUBSET_IDEAL_QUOTIENT, IMP_CONJ, INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING,
        INTEGRAL_DOMAIN_MUL_EQ_0, INTER_IDEMPOT, INTER_SUBSET, IN_ELIM_THM,
        IN_IDEAL_GENERATED_SELF, IN_IDEAL_GENERATED_SING_EQ, IN_RING_IDEAL_0,
        IN_RING_IDEAL_ADD, IN_RING_IDEAL_SUB, IN_SING, LE_0, LE_MULT_RCANCEL, LE_REFL,
        MAXIMAL_IMP_PRIME_IDEAL, .. } := D.core1
  let { MONOMIAL_MUL, MONO_EXISTS, MULT_CLAUSES, NOT_FORALL_THM, NOT_IMP, NOT_LT,
        PRIME_IDEAL_IMP_SUBSET, PRIME_IMP_PROPER_IDEAL, PRIME_IMP_RING_IDEAL,
        PROPER_IDEAL_ALT, QUOTIENT_RING_REDUCED, RADICAL_PRIME_IDEAL, RADICAL_SUBSET,
        RING_ADD, RING_ADD_LZERO, RING_ADD_RZERO, RING_IDEAL_0, RING_IDEAL_CARRIER,
        RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_POW, RING_IDEAL_IDEAL_PROD,
        RING_IDEAL_IDEAL_PRODUCT, RING_IDEAL_IDEAL_QUOTIENT, RING_IDEAL_IMP_SUBSET,
        RING_IDEAL_INTER, RING_IDEAL_SETADD, RING_MUL, RING_MUL_IN_IDEAL_PROD,
        RING_MUL_SYM, RING_POW_2, RING_SETADD_LZERO, RING_SETADD_RZERO,
        RING_SETADD_SUBSET_IDEAL, RING_SETADD_SUPERSET_LEFT,
        RING_SETADD_SUPERSET_RIGHT, SIMPLE_IMAGE_GEN, SING_SUBSET, SUBSET,
        SUBSET_ANTISYM, SUBSET_ANTISYM_EQ, SUBSET_IDEALS_GENERATED_SING, SUBSET_INTER,
        SUBSET_REFL, SUBSET_TRANS, UNION_SUBSET, monomial, monomial_divides,
        monomial_mul, monomial_vars, prime_ideal, proper_ideal, radical, ring_divides,
        trivial_ring, .. } := D.core2
  let { DEDEKIND_IDEAL_FACTORIZATION_EXISTS, DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT,
        DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES, DEDEKIND_IMP_INTEGRAL_DOMAIN,
        IDEAL_PRODUCT_PRIME_MONOMIAL_MUL, .. } := BDedekind01
  let { DEDEKIND_IDEAL_EQ_VALUATION, DEDEKIND_IDEAL_FACTORIZATION,
        DEDEKIND_IDEAL_POW_EQ, DEDEKIND_IDEAL_SUBSET_POW_VALUATION,
        DEDEKIND_IDEAL_SUBSET_VALUATION, IDEAL_PRODUCT_PRIME_MONOMIAL_DIVIDES,
        IDEAL_VALUATION_CARRIER, IDEAL_VALUATION_EQ_0, IDEAL_VALUATION_IDEAL_POW,
        IDEAL_VALUATION_IDEAL_PROD, IDEAL_VALUATION_IDEAL_PRODUCT_MONOMIAL,
        IDEAL_VALUATION_PRIME, IDEAL_VALUATION_PRINCIPAL_MUL, .. } := BDedekind02
  -- @@SCOPE END

  let IDEAL_VALUATION_SETADD ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"n <= MIN a b <=> n <= a /\ n <= b")
    let r2 ← SET_RULE (← q r"!j k z:A. j SUBSET k /\ ~(j = {z}) /\ z IN j ==> ~(k = {z})")
    prove
      r"!r p j k:A->bool.
          dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
          ring_ideal r j /\ ~(j = {ring_0 r}) /\
          ring_ideal r k /\ ~(k = {ring_0 r})
          ==> ideal_valuation r p (ring_setadd r j k) =
              MIN (ideal_valuation r p j) (ideal_valuation r p k)"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_ideal r (ring_setadd r j k) /\
                  (j:A->bool) SUBSET ring_setadd r j k /\
                  k SUBSET ring_setadd r j k") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_SETADD, RING_SETADD_SUPERSET_LEFT, RING_SETADD_SUPERSET_RIGHT, RING_IDEAL_IMP_SUBSET, IN_RING_IDEAL_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(ring_setadd r j k = {ring_0(r:A ring)})") ASSUME_TAC THENL [MATCH_MP_TAC r2 THEN EXISTS_TAC (← q r"j:A->bool") THEN ASM_SIMP_TAC [IN_RING_IDEAL_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"!n. n <= ideal_valuation r p (ring_setadd r j (k:A->bool)) <=>
          n <= MIN (ideal_valuation r p j) (ideal_valuation r p k)") MP_TAC THENL [X_GEN_TAC (← q r"n:num") THEN REWRITE_TAC [r1] THEN MAP_EVERY (fun t => tactic_of do pure (MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool"), t, (← q r"n:num")] DEDEKIND_IDEAL_SUBSET_POW_VALUATION))) [(← q r"j:A->bool"), (← q r"k:A->bool"), (← q r"ring_setadd r j k:A->bool")] THEN ASM_REWRITE_TAC [] THEN REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN EQ_TAC THEN STRIP_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC (← q r"ring_setadd r j (k:A->bool)") THEN ASM_REWRITE_TAC [], MATCH_MP_TAC RING_SETADD_SUBSET_IDEAL THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, PRIME_IMP_RING_IDEAL]], DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"ideal_valuation r p (ring_setadd r j (k:A->bool))") th) THEN MP_TAC (← SPEC (← q r"MIN (ideal_valuation r p (j:A->bool))
                         (ideal_valuation r p k)") th))) THEN REWRITE_TAC [LE_REFL] THEN ARITH_TAC])

  let IDEAL_VALUATION_INTER ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!j k z:A. j SUBSET k /\ ~(j = {z}) /\ z IN j ==> ~(k = {z})")
    let r2 ← SET_RULE (← q r"{x:A->bool | ~(P x /\ Q x)} = {x | ~P x} UNION {x | ~Q x}")
    let r3 ← ARITH_RULE (← q r"MAX a b = 0 <=> a = 0 /\ b = 0")
    prove
      r"!r p j k:A->bool.
          dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
          ring_ideal r j /\ ~(j = {ring_0 r}) /\
          ring_ideal r k /\ ~(k = {ring_0 r})
          ==> ideal_valuation r p (j INTER k) =
              MAX (ideal_valuation r p j) (ideal_valuation r p k)"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:A->bool")] DEDEKIND_IDEAL_FACTORIZATION_EXISTS) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool")] DEDEKIND_IDEAL_FACTORIZATION_EXISTS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"e:(A->bool)->num") STRIP_ASSUME_TAC) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"f:(A->bool)->num") STRIP_ASSUME_TAC) THEN ABBREV_TAC (← q r"g = \p:A->bool. MAX (e p) (f p)") THEN SUBGOAL_THEN (← q r"monomial {p:A->bool | prime_ideal r p /\ ~(p = {ring_0 r})} g /\
      monomial_divides e g /\ monomial_divides f g /\
      monomial_divides g (monomial_mul e f)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "g" THEN REWRITE_TAC [monomial_divides, monomial_mul] THEN REPEAT (CONJ_TAC THENL [ALL_TAC, ARITH_TAC]) THEN MAP_EVERY UNDISCH_TAC [(← q r"monomial {p:A->bool | prime_ideal r p /\ ~(p = {ring_0 r})} e"), (← q r"monomial {p:A->bool | prime_ideal r p /\ ~(p = {ring_0 r})} f")] THEN REWRITE_TAC [monomial, monomial_vars, r3, r2] THEN SIMP_TAC [FINITE_UNION, UNION_SUBSET], ALL_TAC] THEN ABBREV_TAC (← q r"l = ideal_product r (monomial_vars g)
            (\p:A->bool. ideal_pow r p (g p))") THEN SUBGOAL_THEN (← q r"l SUBSET j INTER (k:A->bool) /\ ideal_prod r j k SUBSET l") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [MAP_EVERY EXPAND_TAC ["j", "k", "l"] THEN ASM_SIMP_TAC [SUBSET_INTER, IDEAL_PRODUCT_PRIME_MONOMIAL_DIVIDES], MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"e:(A->bool)->num"), (← q r"f:(A->bool)->num")] IDEAL_PRODUCT_PRIME_MONOMIAL_MUL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN EXPAND_TAC "l" THEN ASM_SIMP_TAC [IDEAL_PRODUCT_PRIME_MONOMIAL_DIVIDES, MONOMIAL_MUL]], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(ideal_prod r j k = {ring_0(r:A ring)})") ASSUME_TAC THENL [ASM_SIMP_TAC [IDEAL_PROD_EQ_ZERO, DEDEKIND_IMP_INTEGRAL_DOMAIN], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_ideal r (l:A->bool) /\ ring_ideal r (j INTER k)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "l" THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_PRODUCT, RING_IDEAL_INTER], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(l = {ring_0(r:A ring)}) /\ ~(j INTER k = {ring_0 r})") STRIP_ASSUME_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC r1 THEN EXISTS_TAC (← q r"ideal_prod r j (k:A->bool)") THEN ASM_SIMP_TAC [IN_RING_IDEAL_0, RING_IDEAL_IDEAL_PROD, IDEAL_PROD_SUBSET_INTER], ALL_TAC] THEN MAP_EVERY (fun (s, t) => tactic_of do pure (MP_TAC (← ISPECL [(← q r"r:A ring"), s, t] DEDEKIND_IDEAL_SUBSET_VALUATION) THEN ASM_REWRITE_TAC [INTER_SUBSET] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"p:A->bool"))) THEN ASM_REWRITE_TAC [])) [((← q r"j INTER k:A->bool"), (← q r"j:A->bool")), ((← q r"j INTER k:A->bool"), (← q r"k:A->bool")), ((← q r"l:A->bool"), (← q r"j INTER k:A->bool"))] THEN MAP_EVERY (fun t => tactic_of do pure (MP_TAC (← ISPECL [(← q r"r:A ring"), t, (← q r"p:A->bool")] IDEAL_VALUATION_IDEAL_PRODUCT_MONOMIAL))) [(← q r"e:(A->bool)->num"), (← q r"f:(A->bool)->num"), (← q r"g:(A->bool)->num")] THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "g" THEN ARITH_TAC)

  let DEDEKIND_IDEAL_PROD_EQ_INTER ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!j k z:A. j SUBSET k /\ ~(j = {z}) /\ z IN j ==> ~(k = {z})")
    prove
      r"!r j k:A->bool.
          dedekind_domain r /\
          ring_ideal r j /\ ~(j = {ring_0 r}) /\
          ring_ideal r k /\ ~(k = {ring_0 r})
          ==> (ideal_prod r j k = j INTER k <=>
               ring_setadd r j k = ring_carrier r)"
      (REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC [IDEAL_PROD_COMAXIMAL] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_ideal r (ring_setadd r j k) /\
                  (j:A->bool) SUBSET ring_setadd r j k") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_SETADD, RING_SETADD_SUPERSET_LEFT, RING_IDEAL_IMP_SUBSET, IN_RING_IDEAL_0], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ring_setadd r j k:A->bool"), (← q r"ring_carrier r:A->bool")] DEDEKIND_IDEAL_EQ_VALUATION) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_CARRIER, (← GSYM trivial_ring), INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING, DEDEKIND_IMP_INTEGRAL_DOMAIN] THEN MATCH_MP_TAC r1 THEN EXISTS_TAC (← q r"j:A->bool") THEN ASM_SIMP_TAC [IN_RING_IDEAL_0], DISCH_THEN SUBST1_TAC] THEN X_GEN_TAC (← q r"p:A->bool") THEN STRIP_TAC THEN MAP_EVERY (fun th => tactic_of do pure (MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool"), (← q r"j:A->bool"), (← q r"k:A->bool")] th))) [IDEAL_VALUATION_SETADD, IDEAL_VALUATION_IDEAL_PROD, IDEAL_VALUATION_INTER] THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool")] IDEAL_VALUATION_CARRIER) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN ANTS_TAC THENL [ASM_MESON_TAC [PRIME_IMP_PROPER_IDEAL, PROPER_IDEAL_ALT], DISCH_THEN SUBST1_TAC] THEN ARITH_TAC)

  let DEDEKIND_FINITE_MAXIMAL_IDEALS_ABOVE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!j k z:A. j SUBSET k /\ ~(j = {z}) /\ z IN j ==> ~(k = {z})")
    prove
      r"!r (j:A->bool).
       dedekind_domain r /\ ring_ideal r j /\ ~(j = {ring_0 r})
       ==> FINITE {m | maximal_ideal r m /\ j SUBSET m}"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool")] DEDEKIND_IDEAL_FACTORIZATION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MATCH_MP_TAC o ((MATCH_MP (← REWRITE_RULE [IMP_CONJ] FINITE_SUBSET)) o CONJUNCT1)) THEN GEN_REWRITE_TAC id [SUBSET] THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"m:A->bool") THEN STRIP_TAC THEN ASM_SIMP_TAC [MAXIMAL_IMP_PRIME_IDEAL] THEN MATCH_MP_TAC r1 THEN EXISTS_TAC (← q r"j:A->bool") THEN ASM_SIMP_TAC [IN_RING_IDEAL_0])

  let DEDEKIND_IDEAL_SUPERSET_PRIME_POW ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!j k z:A. j SUBSET k /\ ~(j = {z}) /\ z IN j ==> ~(k = {z})")
    prove
      r"!r p j:A->bool n.
          dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
          ring_ideal r j /\ ideal_pow r p n SUBSET j
          ==> ?k. k <= n /\ j = ideal_pow r p k"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_ideal r (ideal_pow r p n) /\
                  ~(ideal_pow r p n = {ring_0(r:A ring)}) /\
                  ~(j = {ring_0 r})") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, IDEAL_POW_EQ_ZERO, PRIME_IMP_RING_IDEAL, DEDEKIND_IMP_INTEGRAL_DOMAIN] THEN MATCH_MP_TAC r1 THEN EXISTS_TAC (← q r"ideal_pow r p n:A->bool") THEN ASM_SIMP_TAC [IN_RING_IDEAL_0, RING_IDEAL_IDEAL_POW, PRIME_IMP_RING_IDEAL, IDEAL_POW_EQ_ZERO, DEDEKIND_IMP_INTEGRAL_DOMAIN], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_pow r p n:A->bool"), (← q r"j:A->bool")] DEDEKIND_IDEAL_SUBSET_VALUATION) THEN ASM_SIMP_TAC [IDEAL_VALUATION_IDEAL_POW, IDEAL_VALUATION_PRIME, PRIME_IMP_RING_IDEAL] THEN DISCH_TAC THEN EXISTS_TAC (← q r"ideal_valuation r p (j:A->bool)") THEN CONJ_TAC THENL [FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"p:A->bool"))) THEN ASM_REWRITE_TAC [] THEN ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"ideal_pow r p (ideal_valuation r p (j:A->bool))")] DEDEKIND_IDEAL_EQ_VALUATION) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, IDEAL_POW_EQ_ZERO, PRIME_IMP_RING_IDEAL, DEDEKIND_IMP_INTEGRAL_DOMAIN, IDEAL_VALUATION_IDEAL_POW, IDEAL_VALUATION_PRIME] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN X_GEN_TAC (← q r"q:A->bool") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"q:A->bool"))) THEN ASM_REWRITE_TAC [] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN ARITH_TAC)

  let DEDEKIND_RADICAL_IDEAL_VALUATION ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!s t. x IN s /\ s SUBSET t ==> (x:A) IN t")
    let r2 ← SET_RULE (← q r"~(k SUBSET j) ==> ?x:A. x IN k /\ ~(x IN j)")
    prove
      r"!r j P:A->bool.
          dedekind_domain r /\ ring_ideal r j /\ ~(j = {ring_0 r}) /\
          radical r j = j /\ prime_ideal r P /\ ~(P = {ring_0 r})
          ==> ideal_valuation r P j <= 1"
      (REPEAT STRIP_TAC THEN REWRITE_TAC [(← GSYM NOT_LT)] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(j:A->bool) SUBSET P") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"j:A->bool"), (← q r"1")] DEDEKIND_IDEAL_SUBSET_POW_VALUATION) THEN ASM_SIMP_TAC [IDEAL_POW_1, PRIME_IMP_RING_IDEAL] THEN ASM_ARITH_TAC, ALL_TAC] THEN ABBREV_TAC (← q r"k = ideal_quotient r j (P:A->bool)") THEN SUBGOAL_THEN (← q r"ring_ideal r (k:A->bool) /\ (j:A->bool) SUBSET k") STRIP_ASSUME_TAC THENL [EXPAND_TAC "k" THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_QUOTIENT, IDEAL_SUBSET_IDEAL_QUOTIENT, PRIME_IDEAL_IMP_SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(k = {ring_0 r:A})") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~(j = {ring_0 r:A})") THEN REWRITE_TAC [] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_SIMP_TAC [SING_SUBSET, IN_RING_IDEAL_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_prod r P k = (j:A->bool)") ASSUME_TAC THENL [EXPAND_TAC "k" THEN MATCH_MP_TAC DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_valuation r P (j:A->bool) = 1 + ideal_valuation r P k") ASSUME_TAC THENL [FIRST_X_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [(← SYM th)])) THEN ASM_SIMP_TAC [IDEAL_VALUATION_IDEAL_PROD, IDEAL_VALUATION_PRIME, PRIME_IMP_RING_IDEAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"(k:A->bool) SUBSET P") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"k:A->bool"), (← q r"1")] DEDEKIND_IDEAL_SUBSET_POW_VALUATION) THEN ASM_SIMP_TAC [IDEAL_POW_1, PRIME_IMP_RING_IDEAL] THEN ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"?x:A. x IN k /\ ~(x IN j)") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r2 THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"k:A->bool = j") SUBST_ALL_TAC THENL [ASM_REWRITE_TAC [(← GSYM SUBSET_ANTISYM_EQ)], ASM_ARITH_TAC], ALL_TAC] THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier r") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:A->bool")] RING_IDEAL_IMP_SUBSET) THEN ASM_REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(x:A) IN radical r j") MP_TAC THENL [REWRITE_TAC [radical, IN_ELIM_THM] THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"2") THEN ASM_SIMP_TAC [RING_POW_2, ARITH_EQ] THEN UNDISCH_THEN (← q r"ideal_prod r P k = (j:A->bool)") (SUBST1_TAC o SYM) THEN MATCH_MP_TAC r1 THEN EXISTS_TAC (← q r"ideal_prod r k (k:A->bool)") THEN ASM_SIMP_TAC [RING_MUL_IN_IDEAL_PROD, IDEAL_PROD_MONO, SUBSET_REFL], ASM_REWRITE_TAC []])

  let DEDEKIND_RADICAL_IDEAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"x IN s ==> s SUBSET t ==> (x:A) IN t")
    prove
      r"!r j:A->bool.
          dedekind_domain r /\ ring_ideal r j /\ ~(j = {ring_0 r})
          ==> (radical r j = j <=>
               !P. prime_ideal r P /\ ~(P = {ring_0 r})
                   ==> ideal_valuation r P j <= 1)"
      (REPEAT STRIP_TAC THEN EQ_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC DEDEKIND_RADICAL_IDEAL_VALUATION THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!P. prime_ideal r P /\ ~(P = {ring_0 r})
          ==> (j SUBSET P <=> 1 <= ideal_valuation r P (j:A->bool))") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"j:A->bool"), (← q r"1")] DEDEKIND_IDEAL_SUBSET_POW_VALUATION) THEN ASM_SIMP_TAC [IDEAL_POW_1, PRIME_IMP_RING_IDEAL], ALL_TAC] THEN DISCH_TAC THEN REWRITE_TAC [(← GSYM SUBSET_ANTISYM_EQ)] THEN ASM_SIMP_TAC [RADICAL_SUBSET, RING_IDEAL_IMP_SUBSET] THEN REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"x:A") THEN REWRITE_TAC [radical, IN_ELIM_THM] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"N:num") STRIP_ASSUME_TAC)) THEN ASM_CASES_TAC (← q r"x = ring_0 r:A") THEN ASM_SIMP_TAC [IN_RING_IDEAL_0] THEN SUBGOAL_THEN (← q r"ideal_generated r {x:A} SUBSET j") MP_TAC THENL [ALL_TAC, MATCH_MP_TAC r1 THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN ASM_REWRITE_TAC [SING_SUBSET, IN_SING]] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_generated r {x:A}"), (← q r"j:A->bool")] DEDEKIND_IDEAL_SUBSET_VALUATION) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0] THEN DISCH_THEN SUBST1_TAC THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN ASM_REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"ideal_valuation r P (j:A->bool) = 0") THEN ASM_REWRITE_TAC [LE_0] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ideal_valuation r P (j:A->bool) = 1") SUBST1_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"ideal_generated r {x:A}"), (← q r"1")] DEDEKIND_IDEAL_SUBSET_POW_VALUATION) THEN ASM_SIMP_TAC [IDEAL_POW_1, PRIME_IMP_RING_IDEAL, RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, SING_SUBSET] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool")] RADICAL_PRIME_IDEAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [radical, IN_ELIM_THM] THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"N:num") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(j:A->bool) SUBSET P") MP_TAC THENL [FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC, REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC []])

  let DEDEKIND_QUOTIENT_RING_REDUCED ← prove
    r"!r j:A->bool.
        dedekind_domain r /\ ring_ideal r j /\ ~(j = {ring_0 r})
        ==> ((!x. ring_nilpotent (quotient_ring r j) x
                  ==> x = ring_0(quotient_ring r j)) <=>
             !P. prime_ideal r P /\ ~(P = {ring_0 r})
                 ==> ideal_valuation r P j <= 1)"
    (SIMP_TAC [QUOTIENT_RING_REDUCED, DEDEKIND_RADICAL_IDEAL])

  let DEDEKIND_IDEAL_PROD_SETADD_INTER ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!j k z:A. j SUBSET k /\ ~(j = {z}) /\ z IN j ==> ~(k = {z})")
    let r2 ← SET_RULE (← q r"(z:A) IN j ==> j INTER {z} = {z}")
    let r3 ← SET_RULE (← q r"(z:A) IN k ==> {z} INTER k = {z}")
    prove
      r"!r j k:A->bool.
          dedekind_domain r /\ ring_ideal r j /\ ring_ideal r k
          ==> ideal_prod r (ring_setadd r j k) (j INTER k) = ideal_prod r j k"
      (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"j = {ring_0 r:A}") THENL [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC [RING_SETADD_LZERO, IDEAL_PROD_LZERO, IDEAL_PROD_RZERO, RING_IDEAL_IMP_SUBSET, IN_RING_IDEAL_0, r3], ALL_TAC] THEN ASM_CASES_TAC (← q r"k = {ring_0 r:A}") THENL [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC [RING_SETADD_RZERO, IDEAL_PROD_RZERO, RING_IDEAL_IMP_SUBSET, IN_RING_IDEAL_0, r2], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_ideal r (ring_setadd r j k) /\ ~(ring_setadd r j k = {ring_0 r}) /\
      ring_ideal r (j INTER k) /\ ~(j INTER k = {ring_0 r:A})") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_SETADD, RING_IDEAL_INTER] THEN CONJ_TAC THEN MATCH_MP_TAC r1 THENL [EXISTS_TAC (← q r"j:A->bool") THEN ASM_SIMP_TAC [RING_SETADD_SUPERSET_LEFT, RING_IDEAL_IMP_SUBSET, IN_RING_IDEAL_0], EXISTS_TAC (← q r"ideal_prod r j k:A->bool") THEN ASM_SIMP_TAC [IDEAL_PROD_SUBSET_INTER, IDEAL_PROD_EQ_ZERO, DEDEKIND_IMP_INTEGRAL_DOMAIN, IN_RING_IDEAL_0, RING_IDEAL_IDEAL_PROD]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_prod r (ring_setadd r j k) (j INTER k):A->bool"), (← q r"ideal_prod r j k:A->bool")] DEDEKIND_IDEAL_EQ_VALUATION) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_PROD, IDEAL_PROD_EQ_ZERO, DEDEKIND_IMP_INTEGRAL_DOMAIN] THEN DISCH_THEN SUBST1_TAC THEN X_GEN_TAC (← q r"p:A->bool") THEN STRIP_TAC THEN ASM_SIMP_TAC [IDEAL_VALUATION_IDEAL_PROD, IDEAL_VALUATION_SETADD, IDEAL_VALUATION_INTER] THEN ARITH_TAC)

  let DEDEKIND_IDEAL_PROD_INTER ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!j k z:A. j SUBSET k /\ ~(j = {z}) /\ z IN j ==> ~(k = {z})")
    let r2 ← SET_RULE (← q r"(z:A) IN k ==> k INTER {z} = {z}")
    let r3 ← SET_RULE (← q r"(z:A) IN k ==> {z} INTER k = {z}")
    prove
      r"!r j k l:A->bool.
          dedekind_domain r /\
          ring_ideal r j /\ ring_ideal r k /\ ring_ideal r l
          ==> ideal_prod r j (k INTER l) =
              ideal_prod r j k INTER ideal_prod r j l"
      (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"j = {ring_0 r:A}") THENL [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC [IDEAL_PROD_LZERO, RING_IDEAL_IMP_SUBSET, RING_IDEAL_INTER, INTER_IDEMPOT], ALL_TAC] THEN ASM_CASES_TAC (← q r"k = {ring_0 r:A}") THENL [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC [IDEAL_PROD_RZERO, RING_IDEAL_IMP_SUBSET, IN_RING_IDEAL_0, RING_IDEAL_IDEAL_PROD, r3], ALL_TAC] THEN ASM_CASES_TAC (← q r"l = {ring_0 r:A}") THENL [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC [IDEAL_PROD_RZERO, RING_IDEAL_IMP_SUBSET, IN_RING_IDEAL_0, RING_IDEAL_IDEAL_PROD, r2], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_ideal r (k INTER l) /\ ~(k INTER l = {ring_0 r:A}) /\
      ring_ideal r (ideal_prod r j k INTER ideal_prod r j l) /\
      ~(ideal_prod r j k INTER ideal_prod r j l = {ring_0 r})") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_INTER, RING_IDEAL_IDEAL_PROD] THEN CONJ_TAC THEN MATCH_MP_TAC r1 THENL [EXISTS_TAC (← q r"ideal_prod r k l:A->bool"), EXISTS_TAC (← q r"ideal_prod r (ideal_prod r j k) (ideal_prod r j l):A->bool")] THEN ASM_SIMP_TAC [IDEAL_PROD_SUBSET_INTER, IDEAL_PROD_EQ_ZERO, DEDEKIND_IMP_INTEGRAL_DOMAIN, IN_RING_IDEAL_0, RING_IDEAL_IDEAL_PROD], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_prod r j (k INTER l):A->bool"), (← q r"ideal_prod r j k INTER ideal_prod r j l:A->bool")] DEDEKIND_IDEAL_EQ_VALUATION) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_PROD, IDEAL_PROD_EQ_ZERO, DEDEKIND_IMP_INTEGRAL_DOMAIN] THEN DISCH_THEN SUBST1_TAC THEN X_GEN_TAC (← q r"p:A->bool") THEN STRIP_TAC THEN ASM_SIMP_TAC [IDEAL_VALUATION_IDEAL_PROD, IDEAL_VALUATION_INTER, RING_IDEAL_IDEAL_PROD, IDEAL_PROD_EQ_ZERO, DEDEKIND_IMP_INTEGRAL_DOMAIN] THEN ARITH_TAC)

  let DEDEKIND_IDEAL_COPRIME_PROD_POW ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"x <= y ==> MIN y x = x"
    let r2 ← ARITH_RULE q1
    let q3 ← q r"MIN 0 x = 0"
    let r4 ← ARITH_RULE q3
    let q8 ← q r"1 * x <= y ==> x <= y:num"
    let r9 ← ARITH_RULE q8
    let q10 ← q r"vc <= n * vc:num"
    let p11 ← prove r"!n vi vj vc.
        ~(n = 0) /\ vi + vj = n * vc /\ (vi = 0 \/ vj = 0)
        ==> vi = n * MIN vi vc /\ vj = n * MIN vj vc /\
            vc = MIN vi vc + MIN vj vc" (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN SUBGOAL_THEN q10 ASSUME_TAC THENL [MATCH_MP_TAC r9 THEN REWRITE_TAC [LE_MULT_RCANCEL] THEN ASM_ARITH_TAC, ALL_TAC] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (DISJ_CASES_THEN SUBST_ALL_TAC)) THEN RULE_ASSUM_TAC (REWRITE_RULE [ADD_CLAUSES]) THEN FIRST_X_ASSUM (SUBST_ALL_TAC o (checkM (fun z5 => (do let z6 ← (do let z7 ← (pure z5); pure (concl z7)); pure (is_eq z6))))) THEN ASM_SIMP_TAC [r4, r2, MULT_CLAUSES, ADD_CLAUSES])
    let lemma := p11
    let q12 ← q r"~(n = 0)"
    let v13 ← ASSUME q12
    let q23 ← q r"P:A->bool"
    let q24 ← q r"P:A->bool"
    let q25 ← q r"~(j = {ring_0 r:A})"
    let q26 ← q r"~(i = {ring_0 r:A})"
    let q27 ← q r"~(ring_setadd r i c = {ring_0 r:A}) /\ ~(ring_setadd r j c = {ring_0 r})"
    let q28 ← q r"ring_setadd r j (c:A->bool)"
    let q29 ← q r"ring_setadd r i (c:A->bool)"
    let q30 ← q r"prime_ideal r (P:A->bool)"
    let q31 ← q r"ring_setadd r i j SUBSET (P:A->bool)"
    let v32 ← GSYM DE_MORGAN_THM
    let q37 ← q r"ideal_valuation r (P:A->bool)"
    let q38 ← q r"P:A->bool"
    let q39 ← q r"!P. prime_ideal r P /\ ~(P = {ring_0 r:A})
        ==> ideal_valuation r P i + ideal_valuation r P j =
            n * ideal_valuation r P c /\
            (ideal_valuation r P i = 0 \/ ideal_valuation r P j = 0)"
    let q40 ← q r"j:A->bool"
    let q41 ← q r"i:A->bool"
    let q42 ← q r"r:A ring"
    let v43 ← ISPECL [q42, q41, q40] IDEAL_PROD_EQ_ZERO
    let q44 ← q r"~(i = {ring_0 r:A}) /\ ~(j = {ring_0 r})"
    let q45 ← q r"{ring_0 r:A}"
    let q46 ← q r"ring_carrier r:A->bool"
    let q54 ← q r"i = ring_carrier r:A->bool"
    let q55 ← q r"ring_carrier r:A->bool"
    let q56 ← q r"{ring_0 r:A}"
    let q64 ← q r"j = ring_carrier r:A->bool"
    let q65 ← q r"ideal_pow r {ring_0 r:A} n = {ring_0 r}"
    let q66 ← q r"j:A->bool"
    let q67 ← q r"i:A->bool"
    let q68 ← q r"r:A ring"
    let v69 ← ISPECL [q68, q67, q66] IDEAL_PROD_EQ_ZERO
    let q70 ← q r"c = {ring_0 r:A}"
    prove
      r"!r i j c:A->bool n.
          dedekind_domain r /\ ring_ideal r i /\ ring_ideal r j /\
          ring_ideal r c /\ ~(n = 0) /\
          ring_setadd r i j = ring_carrier r /\
          ideal_prod r i j = ideal_pow r c n
          ==> ?a b. ring_ideal r a /\ ring_ideal r b /\
                    i = ideal_pow r a n /\ j = ideal_pow r b n /\
                    c = ideal_prod r a b"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN)) THEN ASM_CASES_TAC q70 THENL [MP_TAC v69 THEN ASM_SIMP_TAC [IDEAL_POW_EQ_ZERO, RING_IDEAL_0] THEN SUBGOAL_THEN q65 ASSUME_TAC THENL [ASM_SIMP_TAC [IDEAL_POW_EQ_ZERO, RING_IDEAL_0], ALL_TAC] THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL [SUBGOAL_THEN q64 SUBST1_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o ((checkM (fun z61 => (do let z62 ← (do let z63 ← (pure z61); pure (concl z63)); pure (is_eq z62)))) o (checkM (fun th => (do let z60 ← (q r"ring_carrier r:A->bool"); let z59 ← (do let z57 ← (do let z58 ← (pure th); pure (concl z58)); liftExcept (rand z57)); pure (z59 == z60))))))) THEN ASM_SIMP_TAC [RING_SETADD_LZERO, RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN MAP_EVERY EXISTS_TAC [q56, q55] THEN ASM_SIMP_TAC [RING_IDEAL_0, RING_IDEAL_CARRIER, IDEAL_POW_EQ_ZERO, IDEAL_POW_CARRIER, IDEAL_PROD_LZERO, SUBSET_REFL], SUBGOAL_THEN q54 SUBST1_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o ((checkM (fun z51 => (do let z52 ← (do let z53 ← (pure z51); pure (concl z53)); pure (is_eq z52)))) o (checkM (fun th => (do let z50 ← (q r"ring_carrier r:A->bool"); let z49 ← (do let z47 ← (do let z48 ← (pure th); pure (concl z48)); liftExcept (rand z47)); pure (z49 == z50))))))) THEN ASM_SIMP_TAC [RING_SETADD_RZERO, RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN MAP_EVERY EXISTS_TAC [q46, q45] THEN ASM_SIMP_TAC [RING_IDEAL_0, RING_IDEAL_CARRIER, IDEAL_POW_EQ_ZERO, IDEAL_POW_CARRIER, IDEAL_PROD_RZERO, SUBSET_REFL]], ALL_TAC] THEN SUBGOAL_THEN q44 STRIP_ASSUME_TAC THENL [MP_TAC v43 THEN ASM_SIMP_TAC [IDEAL_POW_EQ_ZERO] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN q39 ASSUME_TAC THENL [X_GEN_TAC q38 THEN STRIP_TAC THEN CONJ_TAC THENL [FIRST_X_ASSUM (MP_TAC o ((AP_TERM q37) o (checkM (fun th => (do let z36 ← (q r"ideal_prod r i (j:A->bool)"); let z35 ← (do let z33 ← (do let z34 ← (pure th); pure (concl z34)); liftExcept (lhand z33)); pure (z35 == z36)))))) THEN ASM_SIMP_TAC [IDEAL_VALUATION_IDEAL_PROD, IDEAL_VALUATION_IDEAL_POW], ASM_SIMP_TAC [IDEAL_VALUATION_EQ_0] THEN REWRITE_TAC [v32] THEN STRIP_TAC THEN SUBGOAL_THEN q31 MP_TAC THENL [MATCH_MP_TAC RING_SETADD_SUBSET_IDEAL THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], ASM_REWRITE_TAC [] THEN UNDISCH_TAC q30 THEN REWRITE_TAC [prime_ideal, proper_ideal] THEN SET_TAC []]], ALL_TAC] THEN MAP_EVERY EXISTS_TAC [q29, q28] THEN ASM_SIMP_TAC [RING_IDEAL_SETADD] THEN SUBGOAL_THEN q27 STRIP_ASSUME_TAC THENL [CONJ_TAC THEN DISCH_TAC THENL [UNDISCH_TAC q26, UNDISCH_TAC q25] THEN REWRITE_TAC [] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN (CONJ_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_SETADD_SUPERSET_LEFT THEN ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, IN_RING_IDEAL_0], ASM_MESON_TAC [IN_RING_IDEAL_0, SING_SUBSET]]), ALL_TAC] THEN REPEAT CONJ_TAC THEN wPart Except.ok (lhand o rand) DEDEKIND_IDEAL_EQ_VALUATION THEN ASM_SIMP_TAC [RING_IDEAL_SETADD, RING_IDEAL_IDEAL_POW, RING_IDEAL_IDEAL_PROD, IDEAL_POW_EQ_ZERO, IDEAL_PROD_EQ_ZERO] THEN DISCH_THEN SUBST1_TAC THEN X_GEN_TAC q24 THEN STRIP_TAC THEN ASM_SIMP_TAC [IDEAL_VALUATION_IDEAL_POW, IDEAL_VALUATION_IDEAL_PROD, IDEAL_VALUATION_SETADD, RING_IDEAL_SETADD] THEN FIRST_X_ASSUM (MP_TAC o ((SPEC q23) o (checkM (fun th => (do if ← (do if ← (do let z14 ← (do let z15 ← (pure th); pure (concl z15)); pure (is_forall z14)) then (do let z16 ← (do pure (Prod.snd (← (do let z17 ← (do let z18 ← (pure th); pure (concl z18)); liftExcept (dest_forall z17))))); pure (is_imp z16)) else pure false) then (do let z19 ← (do let z20 ← (do pure (Prod.snd (← (do let z21 ← (do let z22 ← (pure th); pure (concl z22)); liftExcept (dest_forall z21))))); liftExcept (rand z20)); pure (is_conj z19)) else pure false))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o ((MATCH_MP lemma) o (CONJ v13))) THEN MESON_TAC [])

  let DEDEKIND_IDEALS_SUPERSET_PRIME_POW ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!r p:A->bool n.
          dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r})
          ==> {j | ring_ideal r j /\ ideal_pow r p n SUBSET j} =
              {ideal_pow r p m | m <= n} /\
              {j | ring_ideal r j /\ ideal_pow r p n SUBSET j} HAS_SIZE (n + 1)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"j:A->bool") THEN EQ_TAC THENL [STRIP_TAC THEN MATCH_MP_TAC DEDEKIND_IDEAL_SUPERSET_PRIME_POW THEN ASM_REWRITE_TAC [], DISCH_THEN (X_CHOOSE_THEN (← q r"m:num") STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, PRIME_IMP_RING_IDEAL, IDEAL_POW_ANTIMONO, PRIME_IDEAL_IMP_SUBSET]], DISCH_THEN SUBST1_TAC THEN ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN REWRITE_TAC [HAS_SIZE_NUMSEG_LE] THEN SUBGOAL_THEN (← q r"~(p = ring_carrier r:A->bool)") ASSUME_TAC THENL [ASM_MESON_TAC [PRIME_IMP_PROPER_IDEAL, PROPER_IDEAL_ALT], ASM_SIMP_TAC [DEDEKIND_IDEAL_POW_EQ, PRIME_IMP_RING_IDEAL]]])

  let DEDEKIND_IN_IDEAL_POW_VALUATION ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(x:A) IN s ==> s INTER {x} = {x}")
    prove
      r"!r p (x:A) n.
          dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
          x IN ring_carrier r /\ ~(x = ring_0 r)
          ==> (x IN ideal_pow r p n <=>
               n <= ideal_valuation r p (ideal_generated r {x}))"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool"), (← q r"ideal_generated r {x:A}"), (← q r"n:num")] DEDEKIND_IDEAL_SUBSET_POW_VALUATION) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [IDEAL_GENERATED_MINIMAL_EQ, RING_IDEAL_IDEAL_POW, PRIME_IMP_RING_IDEAL, SING_SUBSET, r1])

  let DEDEKIND_RING_DIVIDES_VALUATION ← prove
    r"!r a b:A.
        dedekind_domain r /\
        a IN ring_carrier r /\ ~(a = ring_0 r) /\
        b IN ring_carrier r /\ ~(b = ring_0 r)
        ==> (ring_divides r a b <=>
             !p. prime_ideal r p /\ ~(p = {ring_0 r})
                 ==> ideal_valuation r p (ideal_generated r {a}) <=
                     ideal_valuation r p (ideal_generated r {b}))"
    (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [(← GSYM SUBSET_IDEALS_GENERATED_SING)] THEN MATCH_MP_TAC DEDEKIND_IDEAL_SUBSET_VALUATION THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0])

  let IDEAL_VALUATION_PRINCIPAL_ADD ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"MIN m n <= m")
    let r2 ← ARITH_RULE (← q r"MIN m n <= n")
    prove
      r"!r p a b:A.
          dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
          a IN ring_carrier r /\ b IN ring_carrier r /\
          ~(ring_add r a b = ring_0 r)
          ==> MIN (ideal_valuation r p (ideal_generated r {a}))
                  (ideal_valuation r p (ideal_generated r {b})) <=
              ideal_valuation r p (ideal_generated r {ring_add r a b})"
      (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"a = ring_0 r:A") THEN ASM_SIMP_TAC [RING_ADD_LZERO, r2] THEN ASM_CASES_TAC (← q r"b = ring_0 r:A") THEN ASM_SIMP_TAC [RING_ADD_RZERO, r1] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool"), (← q r"ring_add r a b:A"), (← q r"MIN (ideal_valuation r p (ideal_generated r {a:A}))
                        (ideal_valuation r p (ideal_generated r {b}))")] DEDEKIND_IN_IDEAL_POW_VALUATION) THEN ASM_SIMP_TAC [RING_ADD] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC IN_RING_IDEAL_ADD THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, PRIME_IMP_RING_IDEAL, DEDEKIND_IN_IDEAL_POW_VALUATION] THEN ARITH_TAC)

  let IDEAL_VALUATION_PRINCIPAL_ADD_STRICT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_sub r (ring_add r x y) y = x:A")
    prove
      r"!r p a b:A.
          dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
          a IN ring_carrier r /\ ~(a = ring_0 r) /\ b IN ring_carrier r /\
          ideal_valuation r p (ideal_generated r {a}) <
          ideal_valuation r p (ideal_generated r {b})
          ==> ideal_valuation r p (ideal_generated r {ring_add r a b}) =
              ideal_valuation r p (ideal_generated r {a})"
      (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"b = ring_0 r:A") THEN ASM_SIMP_TAC [RING_ADD_RZERO] THEN ABBREV_TAC (← q r"n = ideal_valuation r p (ideal_generated r {a:A})") THEN SUBGOAL_THEN (← q r"ring_ideal r (ideal_pow r p (SUC n):A->bool)") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, PRIME_IMP_RING_IDEAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"~((ring_add r a b:A) IN ideal_pow r p (SUC n))") ASSUME_TAC THENL [DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_pow r p (SUC n):A->bool"), (← q r"ring_add r a b:A"), (← q r"b:A")] IN_RING_IDEAL_SUB) THEN ASM_SIMP_TAC [r1, DEDEKIND_IN_IDEAL_POW_VALUATION] THEN ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"~(ring_add r a b = ring_0 r:A)") ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC (← q r"~((ring_add r a b:A) IN ideal_pow r p (SUC n))") THEN ASM_SIMP_TAC [IN_RING_IDEAL_0], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool"), (← q r"a:A"), (← q r"b:A")] IDEAL_VALUATION_PRINCIPAL_ADD) THEN UNDISCH_TAC (← q r"~((ring_add r a b:A) IN ideal_pow r p (SUC n))") THEN ASM_SIMP_TAC [DEDEKIND_IN_IDEAL_POW_VALUATION, RING_ADD] THEN ASM_ARITH_TAC)

  let DEDEKIND_IDEAL_POW_MUL_CANCEL ← prove
    r"!r p (s:A) x m n.
        dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
        s IN ring_carrier r /\ ~(s IN ideal_pow r p (m + 1)) /\
        x IN ring_carrier r /\ ring_mul r s x IN ideal_pow r p (m + n)
        ==> x IN ideal_pow r p n"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN)) THEN ASM_CASES_TAC (← q r"x:A = ring_0 r") THENL [ASM_MESON_TAC [IN_RING_IDEAL_0, RING_IDEAL_IDEAL_POW], ALL_TAC] THEN ASM_CASES_TAC (← q r"s:A = ring_0 r") THENL [ASM_MESON_TAC [IN_RING_IDEAL_0, RING_IDEAL_IDEAL_POW], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(ring_mul r s x:A = ring_0 r)") ASSUME_TAC THENL [ASM_SIMP_TAC [INTEGRAL_DOMAIN_MUL_EQ_0], ALL_TAC] THEN MAP_EVERY UNDISCH_TAC [(← q r"ring_mul r (s:A) x IN ideal_pow r p (m + n)"), (← q r"~((s:A) IN ideal_pow r p (m + 1))")] THEN ASM_SIMP_TAC [DEDEKIND_IN_IDEAL_POW_VALUATION, RING_MUL, IDEAL_VALUATION_PRINCIPAL_MUL] THEN ARITH_TAC)

  let DEDEKIND_PRIME_IDEAL_LOCAL_GENERATOR ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(x:A) IN s ==> s SUBSET t ==> x IN t")
    prove
      r"!r p (t:A).
          dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
          t IN p /\ ~(t IN ideal_pow r p 2)
          ==> ?s. s IN ring_carrier r /\ ~(s IN p) /\
                  !y. y IN p
                      ==> ?z. z IN ring_carrier r /\
                              ring_mul r s y = ring_mul r t z"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"(t:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_generated r {t:A} SUBSET p") MP_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET], ASM_SIMP_TAC [DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES, RING_IDEAL_IDEAL_GENERATED]] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"j:A->bool") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"~(j SUBSET (p:A->bool))") MP_TAC THENL [DISCH_TAC THEN UNDISCH_TAC (← q r"~((t:A) IN ideal_pow r p 2)") THEN REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ideal_prod r p (j:A->bool) SUBSET ideal_pow r p 2") MP_TAC THENL [REWRITE_TAC [(← ExceptT.mk (num_CONV (← q r"2:num"))), IDEAL_POW_SUC] THEN MATCH_MP_TAC IDEAL_PROD_MONO THEN ASM_SIMP_TAC [IDEAL_POW_1, SUBSET_REFL], ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC [IN_IDEAL_GENERATED_SELF]], ALL_TAC] THEN REWRITE_TAC [SUBSET, NOT_FORALL_THM, NOT_IMP] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"s:A") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(s:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(y:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool"), (← q r"j:A->bool"), (← q r"y:A"), (← q r"s:A")] RING_MUL_IN_IDEAL_PROD) THEN ASM_SIMP_TAC [IN_IDEAL_GENERATED_SING_EQ, ring_divides, RING_MUL] THEN ASM_MESON_TAC [RING_MUL_SYM])

  -- @@RETURN BEGIN
  return { IDEAL_VALUATION_SETADD, IDEAL_VALUATION_INTER, DEDEKIND_IDEAL_PROD_EQ_INTER,
           DEDEKIND_FINITE_MAXIMAL_IDEALS_ABOVE, DEDEKIND_IDEAL_SUPERSET_PRIME_POW,
           DEDEKIND_RADICAL_IDEAL_VALUATION, DEDEKIND_RADICAL_IDEAL,
           DEDEKIND_QUOTIENT_RING_REDUCED, DEDEKIND_IDEAL_PROD_SETADD_INTER,
           DEDEKIND_IDEAL_PROD_INTER, DEDEKIND_IDEAL_COPRIME_PROD_POW,
           DEDEKIND_IDEALS_SUPERSET_PRIME_POW, DEDEKIND_IN_IDEAL_POW_VALUATION,
           DEDEKIND_RING_DIVIDES_VALUATION, IDEAL_VALUATION_PRINCIPAL_ADD,
           IDEAL_VALUATION_PRINCIPAL_ADD_STRICT, DEDEKIND_IDEAL_POW_MUL_CANCEL,
           DEDEKIND_PRIME_IDEAL_LOCAL_GENERATOR }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- dedekind.ml phrases from line 2297 to 2419                             -/
/- ---------------------------------------------------------------------- -/

structure Dedekind04 where
  -- @@FIELDS
  DEDEKIND_IDEAL_POW_UNIFORMIZER_SPLIT : thm
  DEDEKIND_IDEAL_POW_UNIFORMIZER_POW : thm
  DEDEKIND_SUBRING_DENSE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDedekind04 [HolBase] (D : DedekindDeps) (BDedekind01 : Dedekind01) (BDedekind03 : Dedekind03) :
    ExceptT String IO Dedekind04 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, RING_RULE, SET_TAC, .. } := D
  let { ADD1, ADD_CLAUSES, ADD_SYM, ARITH, IDEAL_POW_0, IDEAL_POW_1,
        IDEAL_POW_ANTIMONO, IDEAL_POW_CARRIER, IMP_CONJ, IN_RING_IDEAL_0,
        IN_RING_IDEAL_ADD, IN_RING_IDEAL_LMUL, IN_RING_IDEAL_NEG, IN_SUBRING_0,
        IN_SUBRING_ADD, IN_SUBRING_MUL, IN_SUBRING_POW, LEFT_IMP_EXISTS_THM,
        MAXIMAL_IDEAL_COMAXIMAL, MAXIMAL_IDEAL_COMAXIMAL_MUL, .. } := D.core1
  let { PRIME_IMP_PROPER_IDEAL, PRIME_IMP_RING_IDEAL, PSUBSET, RIGHT_FORALL_IMP_THM,
        RING_0, RING_1, RING_IDEAL_CARRIER, RING_IDEAL_IDEAL_POW,
        RING_IDEAL_IMP_SUBSET, RING_MUL_IN_IDEAL_POW, RING_MUL_LID, RING_POW,
        RING_POW_IN_IDEAL_POW, RING_SUB, RING_SUB_REFL, SUBSET, SUBSET_ANTISYM,
        proper_ideal, ring_pow, subring_of, .. } := D.core2
  let { DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL, .. } := BDedekind01
  let { DEDEKIND_IDEAL_POW_MUL_CANCEL, DEDEKIND_PRIME_IDEAL_LOCAL_GENERATOR, .. } := BDedekind03
  -- @@SCOPE END

  let DEDEKIND_IDEAL_POW_UNIFORMIZER_SPLIT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!r s y t z u:A.
        s IN ring_carrier r /\ y IN ring_carrier r /\ t IN ring_carrier r /\
        z IN ring_carrier r /\ u IN ring_carrier r /\
        ring_mul r s y = ring_mul r t z
        ==> y = ring_add r (ring_mul r t (ring_mul r u z))
                  (ring_neg r (ring_mul r
                     (ring_sub r (ring_mul r s u) (ring_1 r)) y))")
    prove
      r"!r p (t:A) y n.
          dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
          t IN p /\ ~(t IN ideal_pow r p 2) /\ y IN ideal_pow r p (n + 1)
          ==> ?a w. a IN ideal_pow r p n /\ w IN ideal_pow r p (n + 2) /\
                    y = ring_add r (ring_mul r t a) w"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"maximal_ideal r (p:A->bool)") ASSUME_TAC THENL [ASM_MESON_TAC [DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_pow r p (n + 1) SUBSET (p:A->bool)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool"), (← q r"1:num"), (← q r"n + 1:num")] IDEAL_POW_ANTIMONO) THEN ASM_SIMP_TAC [IDEAL_POW_1, RING_IDEAL_IMP_SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"(t:A) IN ring_carrier r /\ (y:A) IN p /\ y IN ring_carrier r") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool"), (← q r"t:A")] DEDEKIND_PRIME_IDEAL_LOCAL_GENERATOR) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"s:A") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o (SPEC (← q r"y:A")))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"z:A") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(z:A) IN ideal_pow r p n") ASSUME_TAC THENL [MATCH_MP_TAC DEDEKIND_IDEAL_POW_MUL_CANCEL THEN MAP_EVERY EXISTS_TAC [(← q r"t:A"), (← q r"1:num")] THEN ASM_REWRITE_TAC [ARITH] THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN ONCE_REWRITE_TAC [ADD_SYM] THEN MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool"), (← q r"ring_carrier r:A->bool"), (← q r"s:A"), (← q r"ring_1 r:A")] MAXIMAL_IDEAL_COMAXIMAL_MUL) THEN ASM_SIMP_TAC [MAXIMAL_IDEAL_COMAXIMAL, RING_IDEAL_CARRIER, RING_1] THEN ANTS_TAC THENL [ASM_MESON_TAC [PRIME_IMP_PROPER_IDEAL, proper_ideal, PSUBSET, SUBSET_ANTISYM], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"u:A") STRIP_ASSUME_TAC) THEN MAP_EVERY EXISTS_TAC [(← q r"ring_mul r u z:A"), (← q r"ring_neg r
        (ring_mul r (ring_sub r (ring_mul r s u) (ring_1 r)) y):A")] THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW], MATCH_MP_TAC IN_RING_IDEAL_NEG THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN SUBGOAL_THEN (← q r"n + 2 = 1 + (n + 1:num)") SUBST1_TAC THENL [ARITH_TAC, ALL_TAC] THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN ASM_SIMP_TAC [IDEAL_POW_1, RING_IDEAL_IMP_SUBSET], MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC []])

  let DEDEKIND_IDEAL_POW_UNIFORMIZER_POW ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"n + 2 = (n + 1) + 1")
    let r5 ← ARITH_RULE (← q r"(n + 1) + 1 = 1 + n + 1")
    let r6 ← RING_RULE (← q r"ring_sub r (ring_add r (ring_mul r t b) v)
                 (ring_mul r (ring_mul r t u) c) =
      ring_add r (ring_mul r t (ring_sub r b (ring_mul r u c))) (v:A)")
    prove
      r"!r p (t:A) n w.
          dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
          t IN p /\ ~(t IN ideal_pow r p 2) /\ w IN ideal_pow r p n
          ==> ?c. c IN ring_carrier r /\
                  ring_sub r w (ring_mul r (ring_pow r t n) c) IN
                  ideal_pow r p (n + 1)"
      (REPLICATE_TAC 3 GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM, IMP_CONJ] THEN REPEAT DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"(p:A->bool) SUBSET ring_carrier r") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"(t:A) IN ring_carrier r") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN INDUCT_TAC THENL [X_GEN_TAC (← q r"w:A") THEN REWRITE_TAC [IDEAL_POW_0] THEN DISCH_TAC THEN EXISTS_TAC (← q r"w:A") THEN ASM_SIMP_TAC [ring_pow, RING_MUL_LID, RING_SUB_REFL, ADD_CLAUSES, IDEAL_POW_1] THEN ASM_SIMP_TAC [IN_RING_IDEAL_0], ALL_TAC] THEN X_GEN_TAC (← q r"w:A") THEN REWRITE_TAC [ADD1] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool"), (← q r"t:A"), (← q r"w:A"), (← q r"n:num")] DEDEKIND_IDEAL_POW_UNIFORMIZER_SPLIT) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"b:A"), (← q r"v:A")] THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"b:A"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:A") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"c:A") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(b:A) IN ring_carrier r /\ (v:A) IN ring_carrier r") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [IDEAL_POW_CARRIER, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_POW, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sub r (ring_add r (ring_mul r t b) v)
        (ring_mul r (ring_pow r t (n + 1)) c) =
      ring_add r (ring_mul r t (ring_sub r b (ring_mul r (ring_pow r t n) c)))
                 (v:A)") SUBST1_TAC THENL [REWRITE_TAC [(← GSYM ADD1), ring_pow] THEN MATCH_MP_TAC r6 THEN ASM_SIMP_TAC [RING_POW], ALL_TAC] THEN MATCH_MP_TAC IN_RING_IDEAL_ADD THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN CONJ_TAC THENL [REWRITE_TAC [r5] THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN ASM_SIMP_TAC [IDEAL_POW_1], FIRST_ASSUM (MP_TAC o (checkM (fun th => (do let z4 ← (q r"(v:A) IN ideal_pow r p (n + 2)"); let z3 ← (do let z2 ← (pure th); pure (concl z2)); pure (z3 == z4))))) THEN REWRITE_TAC [r1]])

  let DEDEKIND_SUBRING_DENSE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_sub r y (ring_add r z (ring_mul r u c')) =
      ring_add r (ring_sub r (ring_sub r y z) (ring_mul r u c))
                 (ring_mul r u (ring_sub r c (c':A)))")
    prove
      r"!r p (t:A) S n y.
          dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
          S subring_of r /\ t IN S /\ t IN p /\ ~(t IN ideal_pow r p 2) /\
          (!y. y IN ring_carrier r ==> ?z. z IN S /\ ring_sub r y z IN p) /\
          y IN ring_carrier r
          ==> ?z. z IN S /\ ring_sub r y z IN ideal_pow r p n"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"(S:A->bool) SUBSET ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [subring_of], ALL_TAC] THEN SUBGOAL_THEN (← q r"(t:A) IN ring_carrier r") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SPEC_TAC ((← q r"n:num"), (← q r"n:num")) THEN INDUCT_TAC THENL [EXISTS_TAC (← q r"ring_0 r:A") THEN ASM_SIMP_TAC [IN_SUBRING_0, IDEAL_POW_0, RING_SUB, RING_0], ALL_TAC] THEN FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"z:A") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool"), (← q r"t:A"), (← q r"n:num"), (← q r"ring_sub r y (z:A)")] DEDEKIND_IDEAL_POW_UNIFORMIZER_POW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:A") STRIP_ASSUME_TAC) THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"c:A")) o (checkM (fun th => (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); pure (is_forall z2)) then (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); canM (fun z6 => (do let z7 ← (pure z6); find_termM (fun z8 => (do let z10 ← (pure z8); let z9 ← (q r"S:A->bool"); pure (z9 == z10))) z7)) z4) else pure false))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c':A") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"ring_add r z (ring_mul r (ring_pow r t n) (c':A))") THEN CONJ_TAC THENL [MATCH_MP_TAC IN_SUBRING_ADD THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_SIMP_TAC [IN_SUBRING_POW], ALL_TAC] THEN SUBGOAL_THEN (← q r"(z:A) IN ring_carrier r /\ (c':A) IN ring_carrier r") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sub r y (ring_add r z (ring_mul r (ring_pow r t n) c')) =
      ring_add r (ring_sub r (ring_sub r y z) (ring_mul r (ring_pow r t n) c))
                 (ring_mul r (ring_pow r t n) (ring_sub r c (c':A)))") SUBST1_TAC THENL [MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [RING_POW], ALL_TAC] THEN REWRITE_TAC [ADD1] THEN MATCH_MP_TAC IN_RING_IDEAL_ADD THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, RING_POW_IN_IDEAL_POW, IDEAL_POW_1])

  -- @@RETURN BEGIN
  return { DEDEKIND_IDEAL_POW_UNIFORMIZER_SPLIT, DEDEKIND_IDEAL_POW_UNIFORMIZER_POW,
           DEDEKIND_SUBRING_DENSE }
  -- @@RETURN END

end HolANT.Dedekind
