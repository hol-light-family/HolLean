/- ========================================================================= -/
/- ANT: Ideal arithmetic in an arbitrary (commutative) ring                -/
/- ========================================================================= -/
/- File: HolANT/IdealArith.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/ideal_arith.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antidealarithdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/permutations.ml, Library/ring_det.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.IdealArith fills them).

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

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude

namespace HolANT.IdealArith

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD_CLAUSES ADD_EQ_0 CARD_DELETE CARD_EQ_0 COMAXIMAL_RADICALS EQ_IMP
   EQ_SYM_EQ EQ_TRANS ETA_AX EXISTS_IN_INSERT EXISTS_UNIQUE_DEF
   EXISTS_UNIQUE_THM EXTENSION FINITELY_GENERATED_IMP_RING_IDEAL FINITE_DELETE
   FINITE_EMPTY FINITE_INDUCT_STRONG FINITE_SUBSET FINITE_UNION
   FIRST_RING_EPIMORPHISM_THEOREM FORALL_IN_GSPEC FORALL_IN_IMAGE
   FORALL_IN_INSERT FORALL_PAIR_THM FUN_IN_IMAGE HAS_SIZE HAS_SIZE_INDEX
   IDEAL_GENERATED_0 IDEAL_GENERATED_BY_HOMOMORPHIC_IMAGE
   IDEAL_GENERATED_BY_IDEAL_GENERATED IDEAL_GENERATED_EXPLICIT
   IDEAL_GENERATED_FINITE IDEAL_GENERATED_INC IDEAL_GENERATED_INC_GEN
   IDEAL_GENERATED_INDUCT IDEAL_GENERATED_MINIMAL IDEAL_GENERATED_MONO
   IDEAL_GENERATED_RING_IDEAL IDEAL_GENERATED_SCALE IDEAL_GENERATED_SING_ALT
   IDEAL_GENERATED_SING_EQ_CARRIER IDEAL_GENERATED_SUBSET
   IDEAL_GENERATED_SUBSET_CARRIER IDEAL_GENERATED_SUBSET_CARRIER_SUBSET
   IMAGE_CLAUSES IMAGE_SUBSET IMP_CONJ INSERT_DELETE INSERT_SUBSET
   INTEGRAL_DOMAIN_MUL_EQ_0 INTEGRAL_DOMAIN_MUL_LCANCEL
   INTEGRAL_DOMAIN_NONTRIVIAL INTERS_0 INTERS_GSPEC INTERS_INSERT INTER_IDEMPOT
   INTER_UNIV IN_CARTESIAN_PRODUCT IN_CROSS IN_DELETE IN_ELIM_THM
   IN_IDEAL_GENERATED_SING_EQ IN_IMAGE IN_INSERT IN_INTER IN_RING_IDEAL_0
   IN_RING_IDEAL_ADD IN_RING_IDEAL_LMUL IN_RING_IDEAL_MUL IN_RING_IDEAL_NEG
   IN_RING_IDEAL_RMUL IN_RING_IDEAL_SUB IN_RING_IDEAL_SUM IN_SING IN_UNION
   IN_UNIONS ITLIST JACOBSON_RADICAL_LOCAL_RING LEFT_AND_EXISTS_THM
   LEFT_IMP_EXISTS_THM LOCAL_RING_JACOBSON_RADICAL MAXIMAL_IDEAL_EXISTS
   MAXIMAL_IDEAL_IMP_SUBSET MAXIMAL_IMP_PROPER_IDEAL MAXIMAL_IMP_RING_IDEAL
   MAXIMAL_SUPERIDEAL_EXISTS MONOMIAL_1 MONOMIAL_MONO MONOMIAL_VAR
   MONOMIAL_VARS_1 MONOMIAL_VARS_MUL MONOMIAL_VARS_VAR MONO_EXISTS MULT_CLAUSES
   NOETHERIAN_RING NOT_EXISTS_THM NOT_FORALL_THM NOT_IMP NOT_IN_EMPTY NOT_SUC
   PAIRWISE_INSERT PAIR_EQ PRIME_IDEAL_IMP_PSUBSET PRIME_IMP_RING_IDEAL
   PRINCIPAL_IDEAL_IDEAL_GENERATED_SING PRINCIPAL_IMP_FINITELY_GENERATED_IDEAL
   PRODUCT_RING PROD_RING PROPER_IDEAL PROPER_IDEAL_ALT PROPER_IDEAL_IMP_PSUBSET
   PROPER_IMP_RING_IDEAL PSUBSET_ALT QUOTIENT_RING_0 QUOTIENT_RING_1
   QUOTIENT_RING_CARRIER QUOTIENT_RING_UNIVERSAL_EXPLICIT RADICAL_INTER
   RADICAL_MONO RADICAL_PRIME_IDEAL REPLICATE RESTRICTION RESTRICTION_EXTENSION
   RESTRICTION_IN_CARTESIAN_PRODUCT RESTRICTION_IN_EXTENSIONAL
   RESTRICTION_UNIQUE RIGHT_AND_EXISTS_THM RIGHT_EXISTS_IMP_THM
   RIGHT_FORALL_IMP_THM RIGHT_IMP_EXISTS_THM RING_0 RING_1 RING_1_IN_MULTSYS
   RING_1_NOT_IN_PRIME_IDEAL RING_ADD RING_ADD_LDISTRIB : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (RING_ADD_LZERO RING_ADD_RDISTRIB RING_ADD_RZERO RING_ADD_SYM RING_COMAXIMAL
   RING_COSET_EQ RING_COSET_EQ_IDEAL RING_DET
   RING_DET_DEPENDENT_COLUMNS_MUL_IDEAL RING_DET_EQ RING_DET_HOMOMORPHISM
   RING_DET_I RING_EPIMORPHISM_IMP_HOMOMORPHISM RING_FRACTIONATE_IN_CARRIER
   RING_HOMOMORPHISM_0 RING_HOMOMORPHISM_1 RING_HOMOMORPHISM_COMPONENTWISE
   RING_HOMOMORPHISM_FRACTIONATE RING_HOMOMORPHISM_IN_CARRIER
   RING_HOMOMORPHISM_MUL RING_HOMOMORPHISM_NEG RING_HOMOMORPHISM_PAIRED
   RING_HOMOMORPHISM_RING_COSET RING_IDEAL_0 RING_IDEAL_CARRIER
   RING_IDEAL_EPIMORPHIC_IMAGE RING_IDEAL_EQ_CARRIER
   RING_IDEAL_HOMOMORPHIC_PREIMAGE RING_IDEAL_IDEAL_GENERATED
   RING_IDEAL_IMP_NONEMPTY RING_IDEAL_IMP_SUBSET RING_IDEAL_INTER
   RING_IDEAL_ISOMORPHIC_IMAGE_EQ RING_IDEAL_QUOTIENT_LMUL RING_IDEAL_SETADD
   RING_INV RING_ISOMORPHISM RING_ISOMORPHISM_IMP_HOMOMORPHISM
   RING_LOCALEQUIV_IN_CARRIER RING_LOCALEQUIV_SPLIT_EXPLICIT
   RING_MONOMORPHISM_EPIMORPHISM RING_MONOMORPHISM_EQ_0
   RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_MUL RING_MUL_ASSOC
   RING_MUL_IN_PRIME_IDEAL RING_MUL_IN_SETMUL RING_MUL_LID RING_MUL_LINV
   RING_MUL_LNEG RING_MUL_LZERO RING_MUL_RID RING_MUL_RZERO RING_MUL_SYM
   RING_NEG RING_POW RING_POW_ADD RING_PRODUCT RING_PRODUCT_CLAUSES
   RING_PRODUCT_CLOSED RING_PRODUCT_EQ RING_PRODUCT_IMAGE RING_SCALE_SETMUL
   RING_SETADD RING_SETADD_LSUBSET RING_SETADD_LZERO RING_SETADD_RSUBSET
   RING_SETADD_SUBSET_IDEAL RING_SETADD_SUPERSET_LEFT RING_SETADD_SUPERSET_RIGHT
   RING_SETMUL RING_SETMUL_ASSOC RING_SETMUL_MONO RING_SETMUL_SING
   RING_SETMUL_SUBSET_IDEAL RING_SETMUL_SYM RING_SUB RING_SUB_EQ_0
   RING_SUB_LZERO RING_SUB_RDISTRIB RING_SUB_REFL RING_SUB_RZERO RING_SUM
   RING_SUM_0 RING_SUM_ADD RING_SUM_CLAUSES RING_SUM_CLOSED RING_SUM_DELTA
   RING_SUM_EQ RING_SUM_IMAGE RING_SUM_LMUL RING_SUM_NEG RING_SUM_SUB
   RING_UNIT_1 SELECT_UNIQUE SIMPLE_IMAGE SING_SUBSET SKOLEM_THM SUBSET
   SUBSET_ANTISYM SUBSET_ANTISYM_EQ SUBSET_INTER SUBSET_REFL SUBSET_TRANS
   SUBSET_UNION TRANSITIVE_STEPWISE_LE TRIVIAL_RING_10 UNIONS_MAXIMAL_IDEALS
   UNION_EMPTY UNION_SUBSET WF_IND finitely_generated_ideal local_ring
   maximal_ideal monomial monomial_mul monomial_var monomial_vars num_RECURSION
   o_DEF o_THM prime_ideal radical ring_divides ring_epimorphism
   ring_fractionate ring_homomorphism ring_ideal ring_kernel ring_monomorphism
   ring_pow ring_setadd ring_setmul ring_unit trivial_ring : thm)
  deriving Inhabited

/-- What ideal_arith.ml uses from Session besides theorems. -/
structure IdealArithDeps where
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
  WF_INDUCT_TAC : term → tactic
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
/- ideal_arith.ml phrases from line 67 to 828                             -/
/- ---------------------------------------------------------------------- -/

structure IdealArith01 where
  -- @@FIELDS
  ideal_prod : thm
  RING_IDEAL_IDEAL_PROD : thm
  RING_MUL_IN_IDEAL_PROD : thm
  IDEAL_PROD_MINIMAL : thm
  IDEAL_PROD_EXPLICIT : thm
  IDEAL_PROD_MONO : thm
  IDEAL_PROD_COMM : thm
  IDEAL_PROD_IDEAL_GENERATED : thm
  IDEAL_PROD_AC : thm
  IDEAL_PROD_ASSOC : thm
  IDEAL_PROD_SUBSET_LEFT : thm
  IDEAL_PROD_SUBSET_RIGHT : thm
  IDEAL_PROD_CARRIER : thm
  IDEAL_PROD_CARRIER_LEFT : thm
  IDEAL_PROD_LZERO : thm
  IDEAL_PROD_RZERO : thm
  IDEAL_PROD_SUBSET_INTER : thm
  IDEAL_PROD_EQ_CARRIER : thm
  IDEAL_PROD_EQ_ZERO : thm
  IDEAL_PROD_PRINCIPAL : thm
  IDEAL_PROD_SCALE : thm
  IDEAL_PROD_PRINCIPAL_SUBSET_CANCEL : thm
  IDEAL_PROD_PRINCIPAL_CANCEL : thm
  IDEAL_PROD_PRINCIPAL_FACTOR : thm
  IDEAL_PROD_SETADD_LDISTRIB : thm
  IDEAL_PROD_SETADD_RDISTRIB : thm
  IDEAL_PROD_SUBSET_PRIME_IDEAL : thm
  IDEAL_PROD_SETADD_SUBSET : thm
  MAXIMAL_IDEAL_COMAXIMAL : thm
  MAXIMAL_IDEAL_COMAXIMAL_MUL : thm
  IDEAL_PROD_COMAXIMAL : thm
  COMAXIMAL_IDEAL_PROD : thm
  CHINESE_REMAINDER_RING_ISOMORPHISM : thm
  RING_ISOMORPHISM_PROD_QUOTIENT_RING : thm
  RING_ISOMORPHISM_QUOTIENT_RING_INTER : thm
  ideal_quotient : thm
  RING_IDEAL_IDEAL_QUOTIENT : thm
  SUBSET_IDEAL_QUOTIENT : thm
  IDEAL_SUBSET_IDEAL_QUOTIENT : thm
  IDEAL_QUOTIENT_MONO : thm
  IDEAL_QUOTIENT_EQ_CARRIER : thm
  IDEAL_QUOTIENT_CARRIER : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupIdealArith01 [HolBase] (D : IdealArithDeps) :
    ExceptT String IO IdealArith01 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON, MESON_TAC, RING_RULE, RING_TAC, SET_RULE, SET_TAC, TAUT,
        new_definition, .. } := D
  let { ETA_AX, EXISTS_UNIQUE_THM, EXTENSION, FIRST_RING_EPIMORPHISM_THEOREM,
        FORALL_IN_GSPEC, FORALL_IN_IMAGE, FORALL_PAIR_THM, HAS_SIZE, HAS_SIZE_INDEX,
        IDEAL_GENERATED_BY_IDEAL_GENERATED, IDEAL_GENERATED_EXPLICIT,
        IDEAL_GENERATED_INC_GEN, IDEAL_GENERATED_MINIMAL, IDEAL_GENERATED_MONO,
        IDEAL_GENERATED_RING_IDEAL, IDEAL_GENERATED_SCALE, IDEAL_GENERATED_SING_ALT,
        IDEAL_GENERATED_SUBSET, IDEAL_GENERATED_SUBSET_CARRIER_SUBSET, IMP_CONJ,
        INTEGRAL_DOMAIN_MUL_EQ_0, INTEGRAL_DOMAIN_MUL_LCANCEL, IN_CROSS, IN_ELIM_THM,
        IN_IDEAL_GENERATED_SING_EQ, IN_IMAGE, IN_INTER, IN_RING_IDEAL_0,
        IN_RING_IDEAL_ADD, IN_RING_IDEAL_LMUL, IN_RING_IDEAL_NEG, IN_RING_IDEAL_RMUL,
        IN_RING_IDEAL_SUM, IN_SING, LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM,
        MAXIMAL_IMP_RING_IDEAL, MONO_EXISTS, NOT_EXISTS_THM, PAIR_EQ,
        PRIME_IMP_RING_IDEAL, PROD_RING, PROPER_IDEAL_ALT, PROPER_IDEAL_IMP_PSUBSET,
        PROPER_IMP_RING_IDEAL, QUOTIENT_RING_0, QUOTIENT_RING_CARRIER,
        QUOTIENT_RING_UNIVERSAL_EXPLICIT, RIGHT_AND_EXISTS_THM, RIGHT_EXISTS_IMP_THM,
        RIGHT_FORALL_IMP_THM, RING_0, RING_1, RING_ADD, RING_ADD_LDISTRIB, .. } := D.core1
  let { RING_ADD_RDISTRIB, RING_COMAXIMAL, RING_COSET_EQ, RING_COSET_EQ_IDEAL,
        RING_HOMOMORPHISM_PAIRED, RING_HOMOMORPHISM_RING_COSET, RING_IDEAL_0,
        RING_IDEAL_CARRIER, RING_IDEAL_EQ_CARRIER, RING_IDEAL_IDEAL_GENERATED,
        RING_IDEAL_IMP_SUBSET, RING_IDEAL_INTER, RING_IDEAL_QUOTIENT_LMUL,
        RING_IDEAL_SETADD, RING_ISOMORPHISM, RING_MONOMORPHISM_EPIMORPHISM, RING_MUL,
        RING_MUL_ASSOC, RING_MUL_IN_PRIME_IDEAL, RING_MUL_IN_SETMUL, RING_MUL_LID,
        RING_MUL_LNEG, RING_MUL_LZERO, RING_MUL_RID, RING_MUL_RZERO, RING_NEG,
        RING_SCALE_SETMUL, RING_SETADD, RING_SETADD_SUBSET_IDEAL,
        RING_SETADD_SUPERSET_LEFT, RING_SETADD_SUPERSET_RIGHT, RING_SETMUL,
        RING_SETMUL_ASSOC, RING_SETMUL_MONO, RING_SETMUL_SING,
        RING_SETMUL_SUBSET_IDEAL, RING_SETMUL_SYM, RING_SUB, RING_SUB_EQ_0,
        RING_SUM_EQ, RING_SUM_IMAGE, SING_SUBSET, SKOLEM_THM, SUBSET, SUBSET_ANTISYM,
        SUBSET_ANTISYM_EQ, SUBSET_INTER, SUBSET_REFL, maximal_ideal, o_DEF,
        ring_divides, ring_epimorphism, ring_ideal, ring_kernel, ring_monomorphism,
        ring_setadd, ring_setmul, .. } := D.core2
  -- @@SCOPE END

  let ideal_prod ← new_definition
    r"ideal_prod (r:A ring) (j:A->bool) (k:A->bool) =
  ideal_generated r (ring_setmul r j k)"

  let RING_IDEAL_IDEAL_PROD ← prove
    r"!r:A ring j k. ring_ideal r (ideal_prod r j k)"
    (REWRITE_TAC [ideal_prod, RING_IDEAL_IDEAL_GENERATED])

  let RING_MUL_IN_IDEAL_PROD ← prove
    r"!r j k a b:A.
        a IN j /\ b IN k /\ a IN ring_carrier r /\ b IN ring_carrier r
        ==> ring_mul r a b IN ideal_prod r j k"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [ideal_prod] THEN MATCH_MP_TAC IDEAL_GENERATED_INC_GEN THEN ASM_SIMP_TAC [RING_MUL, RING_MUL_IN_SETMUL])

  let IDEAL_PROD_MINIMAL ← prove
    r"!r j k l:A->bool.
        ring_ideal r l /\ (!a b. a IN j /\ b IN k ==> ring_mul r a b IN l)
        ==> ideal_prod r j k SUBSET l"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [ideal_prod] THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_SIMP_TAC [ring_setmul, SUBSET, FORALL_IN_GSPEC])

  let IDEAL_PROD_EXPLICIT ← prove
    r"!r j k:A->bool.
        ring_ideal r j /\ ring_ideal r k
        ==> ideal_prod r j k =
            {ring_sum r {i | i < n} (\i:num. ring_mul r (u i) (v i)) | n,u,v |
             !i. i < n ==> u i IN j /\ v i IN k}"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [ALL_TAC, REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_RING_IDEAL_SUM THEN REWRITE_TAC [RING_IDEAL_IDEAL_PROD, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_PROD THEN ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET]] THEN REWRITE_TAC [SUBSET, ideal_prod, IDEAL_GENERATED_EXPLICIT, FORALL_IN_GSPEC] THEN MAP_EVERY X_GEN_TAC [(← q r"t:A->bool"), (← q r"cf:A->A")] THEN STRIP_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN SUBGOAL_THEN (← q r"!x:A. ?p q. x IN t
                ==> p IN j /\ q IN k /\ p IN ring_carrier r /\
                    q IN ring_carrier r /\ ring_mul r p q = x") MP_TAC THENL [X_GEN_TAC (← q r"x:A") THEN REWRITE_TAC [RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:A) IN ring_setmul r j k") MP_TAC THENL [ASM SET_TAC [], REWRITE_TAC [ring_setmul, IN_ELIM_THM]] THEN ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM]] THEN MAP_EVERY X_GEN_TAC [(← q r"p:A->A"), (← q r"q:A->A")] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_sum r t (\i. ring_mul r (cf i) i) =
    ring_sum r t (\x. ring_mul r (ring_mul r (cf x) (p x)) (q x:A))") SUBST1_TAC THENL [MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC [(← GSYM RING_MUL_ASSOC)], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"t:A->bool"), (← q r"CARD(t:A->bool)")] HAS_SIZE_INDEX) THEN ASM_REWRITE_TAC [HAS_SIZE, EXISTS_UNIQUE_THM] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"f:num->A") STRIP_ASSUME_TAC) THEN MAP_EVERY EXISTS_TAC [(← q r"CARD(t:A->bool)"), (← q r"\i. ring_mul r (cf((f:num->A) i)) (p(f i):A)"), (← q r"\i. (q:A->A)((f:num->A) i)")] THEN REWRITE_TAC [] THEN CONJ_TAC THENL [ASM_MESON_TAC [IN_RING_IDEAL_LMUL], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"f:num->A"), (← q r"\x:A. ring_mul r (ring_mul r (cf x) (p x)) (q x:A)"), (← q r"{i:num | i < CARD(t:A->bool)}")] RING_SUM_IMAGE) THEN ANTS_TAC THENL [REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"IMAGE (f:num->A) {i | i < CARD(t:A->bool)} = t") SUBST1_TAC THENL [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [o_DEF]])

  let IDEAL_PROD_MONO ← prove
    r"!r j j' k k':A->bool.
        j SUBSET j' /\ k SUBSET k'
        ==> ideal_prod r j k SUBSET ideal_prod r j' k'"
    (SIMP_TAC [ideal_prod, IDEAL_GENERATED_MONO, RING_SETMUL_MONO])

  let IDEAL_PROD_COMM ← prove
    r"!r:A ring j k.
        j SUBSET ring_carrier r /\ k SUBSET ring_carrier r
        ==> ideal_prod r j k = ideal_prod r k j"
    (SIMP_TAC [ideal_prod, RING_SETMUL_SYM])

  let IDEAL_PROD_IDEAL_GENERATED ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"t:A->bool"
    let q2 ← q r"{x:A | x IN ring_carrier r /\
                     ring_mul r a x IN ideal_prod r s t}"
    let q3 ← q r"r:A ring"
    let v4 ← ISPECL [q3, q2, q1] IDEAL_GENERATED_MINIMAL
    let q5 ← q r"(a:A) IN ring_carrier r"
    let q6 ← q r"b:A"
    let q7 ← q r"a:A"
    let p8 ← prove r"!r s t:A->bool.
        s SUBSET ring_carrier r /\ t SUBSET ring_carrier r
        ==> ideal_prod r s (ideal_generated r t) = ideal_prod r s t" (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_SIMP_TAC [IDEAL_PROD_MONO, SUBSET_REFL, IDEAL_GENERATED_SUBSET_CARRIER_SUBSET] THEN MATCH_MP_TAC IDEAL_PROD_MINIMAL THEN REWRITE_TAC [RING_IDEAL_IDEAL_PROD] THEN MAP_EVERY X_GEN_TAC [q7, q6] THEN STRIP_TAC THEN SUBGOAL_THEN q5 ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN MP_TAC v4 THEN ASM_SIMP_TAC [RING_IDEAL_QUOTIENT_LMUL, RING_IDEAL_IDEAL_PROD] THEN ANTS_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC [RING_MUL_IN_IDEAL_PROD, SUBSET])
    let lemma := p8
    prove
      r"!r s t:A->bool.
          s SUBSET ring_carrier r /\ t SUBSET ring_carrier r
          ==> ideal_prod r (ideal_generated r s) (ideal_generated r t) =
              ideal_prod r s t"
      (MESON_TAC [lemma, IDEAL_PROD_COMM, IDEAL_GENERATED_SUBSET])

  let IDEAL_PROD_AC ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let v1 ← GSYM ideal_prod
    let p2 ← prove r"!r s t:A->bool.
        s SUBSET ring_carrier r /\ t SUBSET ring_carrier r
        ==> ideal_generated r (ring_setmul r (ideal_generated r s) t) =
            ideal_generated r (ring_setmul r s t) /\
            ideal_generated r (ring_setmul r s (ideal_generated r t)) =
            ideal_generated r (ring_setmul r s t)" (REWRITE_TAC [v1] THEN MESON_TAC [IDEAL_PROD_IDEAL_GENERATED, IDEAL_GENERATED_BY_IDEAL_GENERATED, IDEAL_GENERATED_SUBSET])
    let lemma := p2
    let p3 ← prove r"!r j k l:A->bool.
        j SUBSET ring_carrier r /\ k SUBSET ring_carrier r /\
        l SUBSET ring_carrier r
        ==> ideal_prod r (ideal_prod r j k) l =
            ideal_prod r j (ideal_prod r k l)" (SIMP_TAC [ideal_prod, lemma, RING_SETMUL, RING_SETMUL_ASSOC])
    let assoc := p3
    prove
      r"!r:A ring.
          (!j k. j SUBSET ring_carrier r /\ k SUBSET ring_carrier r
                 ==> ideal_prod r j k = ideal_prod r k j) /\
          (!j k l. j SUBSET ring_carrier r /\ k SUBSET ring_carrier r /\
                   l SUBSET ring_carrier r
                   ==> ideal_prod r (ideal_prod r j k) l =
                       ideal_prod r j (ideal_prod r k l)) /\
          (!j k l. j SUBSET ring_carrier r /\ k SUBSET ring_carrier r /\
                   l SUBSET ring_carrier r
                   ==> ideal_prod r j (ideal_prod r k l) =
                       ideal_prod r k (ideal_prod r j l))"
      (MESON_TAC [IDEAL_PROD_COMM, assoc, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_PROD])

  let IDEAL_PROD_ASSOC ← prove
    r"!r p q s:A->bool.
        p SUBSET ring_carrier r /\ q SUBSET ring_carrier r /\
        s SUBSET ring_carrier r
        ==> ideal_prod r p (ideal_prod r q s) =
            ideal_prod r (ideal_prod r p q) s"
    (MESON_TAC [IDEAL_PROD_AC])

  let IDEAL_PROD_SUBSET_LEFT ← prove
    r"!r j k:A->bool.
        ring_ideal r j /\ k SUBSET ring_carrier r
        ==> ideal_prod r j k SUBSET j"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [ideal_prod] THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_SIMP_TAC [RING_SETMUL_SUBSET_IDEAL, SUBSET_REFL])

  let IDEAL_PROD_SUBSET_RIGHT ← prove
    r"!r j k:A->bool.
        j SUBSET ring_carrier r /\ ring_ideal r k
        ==> ideal_prod r j k SUBSET k"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [ideal_prod] THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_SIMP_TAC [RING_SETMUL_SUBSET_IDEAL, SUBSET_REFL])

  let IDEAL_PROD_CARRIER ← prove
    r"!r:A ring j.
        ring_ideal r j
        ==> ideal_prod r j (ring_carrier r) = j"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_SIMP_TAC [IDEAL_PROD_SUBSET_LEFT, SUBSET_REFL, SUBSET] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN FIRST_ASSUM (SUBST1_TAC o (SYM o (MATCH_MP RING_MUL_RID))) THEN ASM_SIMP_TAC [RING_MUL_IN_IDEAL_PROD, RING_1])

  let IDEAL_PROD_CARRIER_LEFT ← prove
    r"!r j:A->bool.
        ring_ideal r j ==> ideal_prod r (ring_carrier r) j = j"
    (MESON_TAC [IDEAL_PROD_CARRIER, IDEAL_PROD_COMM, SUBSET_REFL, RING_IDEAL_IMP_SUBSET])

  let IDEAL_PROD_LZERO ← prove
    r"!r j:A->bool.
        j SUBSET ring_carrier r ==> ideal_prod r {ring_0 r} j = {ring_0 r}"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN SIMP_TAC [SING_SUBSET, IN_RING_IDEAL_0, RING_IDEAL_IDEAL_PROD] THEN MATCH_MP_TAC IDEAL_PROD_MINIMAL THEN REWRITE_TAC [RING_IDEAL_0, IN_SING] THEN ASM_MESON_TAC [RING_MUL_LZERO, SUBSET])

  let IDEAL_PROD_RZERO ← prove
    r"!r j:A->bool.
        j SUBSET ring_carrier r ==> ideal_prod r j {ring_0 r} = {ring_0 r}"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN SIMP_TAC [SING_SUBSET, IN_RING_IDEAL_0, RING_IDEAL_IDEAL_PROD] THEN MATCH_MP_TAC IDEAL_PROD_MINIMAL THEN REWRITE_TAC [RING_IDEAL_0, IN_SING] THEN ASM_MESON_TAC [RING_MUL_RZERO, SUBSET])

  let IDEAL_PROD_SUBSET_INTER ← prove
    r"!r:A ring j k.
        ring_ideal r j /\ ring_ideal r k
        ==> ideal_prod r j k SUBSET (j INTER k)"
    (SIMP_TAC [SUBSET_INTER, IDEAL_PROD_SUBSET_LEFT, IDEAL_PROD_SUBSET_RIGHT, RING_IDEAL_IMP_SUBSET])

  let IDEAL_PROD_EQ_CARRIER ← prove
    r"!r j k:A->bool.
        ring_ideal r j /\ ring_ideal r k
        ==> (ideal_prod r j k = ring_carrier r <=>
             j = ring_carrier r /\ k = ring_carrier r)"
    (REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC [IDEAL_PROD_CARRIER, RING_IDEAL_CARRIER] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"k:A->bool")] IDEAL_PROD_SUBSET_INTER) THEN MP_TAC (← ISPEC (← q r"r:A ring") RING_IDEAL_IMP_SUBSET) THEN ASM SET_TAC [])

  let IDEAL_PROD_EQ_ZERO ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"(~p /\ ~q ==> F) ==> p \/ q")
    prove
      r"!r:A ring j k.
          integral_domain r /\ ring_ideal r j /\ ring_ideal r k
          ==> (ideal_prod r j k = {ring_0 r} <=>
               j = {ring_0 r} \/ k = {ring_0 r})"
      (REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [IDEAL_PROD_LZERO, IDEAL_PROD_RZERO, RING_IDEAL_IMP_SUBSET] THEN MATCH_MP_TAC r1 THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"?a b:A. a IN j /\ b IN k /\ ~(a = ring_0 r) /\ ~(b = ring_0 r)") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool")] IN_RING_IDEAL_0) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:A->bool")] IN_RING_IDEAL_0) THEN ASM SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"k:A->bool"), (← q r"a:A"), (← q r"b:A")] RING_MUL_IN_IDEAL_PROD) THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier r /\ b IN ring_carrier r") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [IN_SING, INTEGRAL_DOMAIN_MUL_EQ_0])

  let IDEAL_PROD_PRINCIPAL ← prove
    r"!r (a:A) b.
        a IN ring_carrier r /\ b IN ring_carrier r
        ==> ideal_prod r (ideal_generated r {a}) (ideal_generated r {b}) =
            ideal_generated r {ring_mul r a b}"
    (SIMP_TAC [IDEAL_PROD_IDEAL_GENERATED, SING_SUBSET] THEN REWRITE_TAC [ideal_prod, RING_SETMUL_SING])

  let IDEAL_PROD_SCALE ← prove
    r"!r (a:A) j.
        a IN ring_carrier r /\ ring_ideal r j
        ==> ideal_prod r (ideal_generated r {a}) j = IMAGE (ring_mul r a) j"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [(← GSYM (← MATCH_MP IDEAL_GENERATED_RING_IDEAL th))])) THEN ASM_SIMP_TAC [IDEAL_PROD_IDEAL_GENERATED, SING_SUBSET, RING_IDEAL_IMP_SUBSET] THEN ASM_SIMP_TAC [ideal_prod, (← GSYM RING_SCALE_SETMUL), IDEAL_GENERATED_SCALE, RING_IDEAL_IMP_SUBSET, IDEAL_GENERATED_RING_IDEAL])

  let IDEAL_PROD_PRINCIPAL_SUBSET_CANCEL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!s (f:A->A) j k.
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        j SUBSET s /\ k SUBSET s
        ==> (IMAGE f j SUBSET IMAGE f k <=> j SUBSET k)")
    prove
      r"!r (a:A) j k.
          integral_domain r /\ a IN ring_carrier r /\ ~(a = ring_0 r) /\
          ring_ideal r j /\ ring_ideal r k
          ==> (ideal_prod r (ideal_generated r {a}) j SUBSET
               ideal_prod r (ideal_generated r {a}) k <=>
               j SUBSET k)"
      (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [IDEAL_PROD_SCALE] THEN MATCH_MP_TAC r1 THEN EXISTS_TAC (← q r"ring_carrier r:A->bool") THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET] THEN ASM_MESON_TAC [INTEGRAL_DOMAIN_MUL_LCANCEL])

  let IDEAL_PROD_PRINCIPAL_CANCEL ← prove
    r"!r (a:A) j k.
        integral_domain r /\ a IN ring_carrier r /\ ~(a = ring_0 r) /\
        ring_ideal r j /\ ring_ideal r k
        ==> (ideal_prod r (ideal_generated r {a}) j =
             ideal_prod r (ideal_generated r {a}) k <=>
             j = k)"
    (SIMP_TAC [(← GSYM SUBSET_ANTISYM_EQ), IDEAL_PROD_PRINCIPAL_SUBSET_CANCEL])

  let IDEAL_PROD_PRINCIPAL_FACTOR ← prove
    r"!r (a:A) j.
        a IN ring_carrier r /\ ring_ideal r j
        ==> (j SUBSET ideal_generated r {a} <=>
             ?k. ring_ideal r k /\ ideal_prod r (ideal_generated r {a}) k = j)"
    (REPEAT STRIP_TAC THEN EQ_TAC THENL [DISCH_TAC THEN EXISTS_TAC (← q r"{x:A | x IN ring_carrier r /\ ring_mul r a x IN j}") THEN ASM_SIMP_TAC [RING_IDEAL_QUOTIENT_LMUL, IDEAL_PROD_SCALE] THEN REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN X_GEN_TAC (← q r"y:A") THEN EQ_TAC THENL [MESON_TAC [], DISCH_TAC] THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"y:A")) o (REWRITE_RULE [SUBSET]))) THEN ASM_SIMP_TAC [IN_IDEAL_GENERATED_SING_EQ, ring_divides] THEN ASM_MESON_TAC [], STRIP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [IDEAL_PROD_SUBSET_LEFT, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_GENERATED]])

  let IDEAL_PROD_SETADD_LDISTRIB ← prove
    r"!r j k l:A->bool.
        j SUBSET ring_carrier r /\ ring_ideal r k /\ ring_ideal r l
        ==> ideal_prod r j (ring_setadd r k l) =
            ring_setadd r (ideal_prod r j k) (ideal_prod r j l)"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_PROD_MINIMAL THEN SIMP_TAC [RING_IDEAL_SETADD, RING_IDEAL_IDEAL_PROD] THEN REWRITE_TAC [ring_setadd, IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"y:A") (X_CHOOSE_THEN (← q r"z:A") STRIP_ASSUME_TAC))) THEN MAP_EVERY EXISTS_TAC [(← q r"ring_mul r a y:A"), (← q r"ring_mul r a z:A")] THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier r /\ y IN ring_carrier r /\ z IN ring_carrier r") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [SUBSET, RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [RING_MUL_IN_IDEAL_PROD, RING_ADD_LDISTRIB], MATCH_MP_TAC RING_SETADD_SUBSET_IDEAL THEN REWRITE_TAC [RING_IDEAL_IDEAL_PROD] THEN CONJ_TAC THEN MATCH_MP_TAC IDEAL_PROD_MONO THEN ASM_SIMP_TAC [SUBSET_REFL, RING_SETADD_SUPERSET_LEFT, RING_SETADD_SUPERSET_RIGHT, RING_IDEAL_IMP_SUBSET, IN_RING_IDEAL_0]])

  let IDEAL_PROD_SETADD_RDISTRIB ← prove
    r"!r j k l:A->bool.
        ring_ideal r j /\ ring_ideal r k /\ l SUBSET ring_carrier r
        ==> ideal_prod r (ring_setadd r j k) l =
            ring_setadd r (ideal_prod r j l) (ideal_prod r k l)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"l:A->bool"), (← q r"j:A->bool"), (← q r"k:A->bool")] IDEAL_PROD_SETADD_LDISTRIB) THEN ASM_SIMP_TAC [IDEAL_PROD_AC, RING_SETADD, RING_IDEAL_IMP_SUBSET])

  let IDEAL_PROD_SUBSET_PRIME_IDEAL ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let v1 ← GSYM RING_MUL_IN_PRIME_IDEAL
    let q2 ← q r"(x:A) IN ring_carrier r /\ y IN ring_carrier r"
    let q3 ← q r"y:A"
    let q4 ← q r"x:A"
    let q5 ← q r"!P Q R:A->bool. (!x y. P x /\ Q y ==> R x \/ R y)
                      ==> (!x. P x ==> R x) \/ (!y. Q y ==> R y)"
    let r6 ← MESON [] q5
    prove
      r"!r p j k:A->bool.
          prime_ideal r p /\ j SUBSET ring_carrier r /\ k SUBSET ring_carrier r
          ==> (ideal_prod r j k SUBSET p <=> j SUBSET p \/ k SUBSET p)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN EQ_TAC THENL [REWRITE_TAC [SUBSET] THEN DISCH_TAC THEN MATCH_MP_TAC r6 THEN MAP_EVERY X_GEN_TAC [q4, q3] THEN STRIP_TAC THEN SUBGOAL_THEN q2 STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [v1] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_MUL_IN_IDEAL_PROD], STRIP_TAC THEN MATCH_MP_TAC IDEAL_PROD_MINIMAL THEN ASM_MESON_TAC [IN_RING_IDEAL_RMUL, IN_RING_IDEAL_LMUL, SUBSET]])

  let IDEAL_PROD_SETADD_SUBSET ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul r (ring_add r x1 y1) (ring_add r x2 y2) =
    ring_add r (ring_add r (ring_mul r x1 (ring_add r x2 y2))
                           (ring_mul r y1 x2))
               (ring_mul r y1 (y2:A))")
    prove
      r"!r i j k:A->bool.
          ring_ideal r i /\ ring_ideal r j /\ ring_ideal r k
          ==> ideal_prod r (ring_setadd r i j) (ring_setadd r i k) SUBSET
              ring_setadd r i (ideal_prod r j k)"
      (REPEAT STRIP_TAC THEN MATCH_MP_TAC IDEAL_PROD_MINIMAL THEN ASM_SIMP_TAC [RING_IDEAL_SETADD, RING_IDEAL_IDEAL_PROD] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN REWRITE_TAC [ring_setadd, IN_ELIM_THM] THEN DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"x1:A") (X_CHOOSE_THEN (← q r"y1:A") STRIP_ASSUME_TAC)) (X_CHOOSE_THEN (← q r"x2:A") (X_CHOOSE_THEN (← q r"y2:A") STRIP_ASSUME_TAC))) THEN MAP_EVERY EXISTS_TAC [(← q r"ring_add r (ring_mul r x1 (ring_add r x2 y2)) (ring_mul r y1 x2):A"), (← q r"ring_mul r y1 y2:A")] THEN SUBGOAL_THEN (← q r"(x1:A) IN ring_carrier r /\ x2 IN ring_carrier r /\
      y1 IN ring_carrier r /\ y2 IN ring_carrier r") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [RING_MUL_IN_IDEAL_PROD, IN_RING_IDEAL_ADD, IN_RING_IDEAL_RMUL, IN_RING_IDEAL_LMUL, RING_ADD] THEN ASM_SIMP_TAC [r1])

  let MAXIMAL_IDEAL_COMAXIMAL ← prove
    r"!r m j:A->bool.
        maximal_ideal r m /\ ring_ideal r j
        ==> (ring_setadd r m j = ring_carrier r <=> ~(j SUBSET m))"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [maximal_ideal])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PROPER_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"m SUBSET ring_setadd r m j /\ j SUBSET ring_setadd r m (j:A->bool)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_SETADD_SUPERSET_LEFT, RING_SETADD_SUPERSET_RIGHT, RING_IDEAL_IMP_SUBSET, IN_RING_IDEAL_0], EQ_TAC THEN DISCH_TAC] THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"m:A->bool"), (← q r"j:A->bool")] RING_SETADD_SUBSET_IDEAL) THEN FIRST_ASSUM (MP_TAC o (MATCH_MP PROPER_IDEAL_IMP_PSUBSET)) THEN ASM_REWRITE_TAC [SUBSET_REFL] THEN SET_TAC [], FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"ring_setadd r m (j:A->bool)")) o (REWRITE_RULE [NOT_EXISTS_THM]))) THEN ASM_SIMP_TAC [PROPER_IDEAL_ALT, RING_IDEAL_SETADD] THEN ASM SET_TAC []])

  let MAXIMAL_IDEAL_COMAXIMAL_MUL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!a b y v w x:A.
        a IN ring_carrier r /\ b IN ring_carrier r /\ y IN ring_carrier r /\
        v IN ring_carrier r /\ w IN ring_carrier r /\ x IN ring_carrier r /\
        ring_add r a (ring_mul r x v) = ring_1 r /\
        ring_mul r w v = ring_add r b y
        ==> ring_sub r (ring_mul r x y) w =
            ring_neg r (ring_add r (ring_mul r w a) (ring_mul r x b))")
    let r2 ← TAUT (← q r"~s /\ (e ==> g) ==> (e <=> ~s) ==> g")
    prove
      r"!r m j x w:A.
          maximal_ideal r m /\ ring_ideal r j /\
          ring_setadd r m j = ring_carrier r /\
          x IN ring_carrier r /\ ~(x IN m) /\ w IN ring_carrier r
          ==> ?y. y IN j /\ ring_sub r (ring_mul r x y) w IN m"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"?a v:A. a IN m /\ v IN ring_carrier r /\
              ring_add r a (ring_mul r x v) = ring_1 r") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"ideal_generated r {x:A}")] MAXIMAL_IDEAL_COMAXIMAL) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, RING_COMAXIMAL] THEN MATCH_MP_TAC r2 THEN CONJ_TAC THENL [REWRITE_TAC [SUBSET] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"x:A"))) THEN ASM_SIMP_TAC [IDEAL_GENERATED_INC_GEN, IN_SING], ASM_SIMP_TAC [IDEAL_GENERATED_SING_ALT, IN_ELIM_THM] THEN MESON_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul r w v IN ring_setadd r m (j:A->bool)") MP_TAC THENL [ASM_SIMP_TAC [RING_MUL], ALL_TAC] THEN REWRITE_TAC [ring_setadd, IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"b:A"), (← q r"y:A")] THEN STRIP_TAC THEN EXISTS_TAC (← q r"y:A") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier r /\ b IN ring_carrier r /\
                  y IN ring_carrier r") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sub r (ring_mul r x y) w =
      ring_neg r (ring_add r (ring_mul r w a) (ring_mul r (x:A) b))") SUBST1_TAC THENL [MATCH_MP_TAC r1 THEN EXISTS_TAC (← q r"v:A") THEN ASM_REWRITE_TAC [], ASM_SIMP_TAC [IN_RING_IDEAL_NEG, IN_RING_IDEAL_ADD, IN_RING_IDEAL_LMUL]])

  let IDEAL_PROD_COMAXIMAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!a b x:A. a IN ring_carrier r /\ b IN ring_carrier r /\
                x IN ring_carrier r /\ ring_add r a b = ring_1 r
                ==> x = ring_add r (ring_mul r a x) (ring_mul r x b)")
    prove
      r"!r j k:A->bool.
          ring_ideal r j /\ ring_ideal r k /\
          ring_setadd r j k = ring_carrier r
          ==> ideal_prod r j k = j INTER k"
      (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_SIMP_TAC [IDEAL_PROD_SUBSET_INTER] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"k:A->bool")] RING_COMAXIMAL) THEN ASM_REWRITE_TAC [SUBSET, IN_INTER, LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN X_GEN_TAC (← q r"x:A") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier r /\ b IN ring_carrier r /\ x IN ring_carrier r") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"x = ring_add r (ring_mul r a x) (ring_mul r x b):A") SUBST1_TAC THENL [MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC [], MATCH_MP_TAC IN_RING_IDEAL_ADD THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_PROD, RING_MUL_IN_IDEAL_PROD]])

  let COMAXIMAL_IDEAL_PROD ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!a b c d:A. a IN ring_carrier r /\ b IN ring_carrier r /\
                  c IN ring_carrier r /\ d IN ring_carrier r /\
                  ring_add r a b = ring_1 r /\ ring_add r c d = ring_1 r
                  ==> ring_add r (ring_add r a (ring_mul r b c))
                                 (ring_mul r b d) = ring_1 r")
    prove
      r"!r j k l:A->bool.
          ring_ideal r j /\ ring_ideal r k /\ ring_ideal r l
          ==> (ring_setadd r j (ideal_prod r k l) = ring_carrier r <=>
               ring_setadd r j k = ring_carrier r /\
               ring_setadd r j l = ring_carrier r)"
      (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [RING_COMAXIMAL, RING_IDEAL_IDEAL_PROD] THEN EQ_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:A->bool"), (← q r"l:A->bool")] IDEAL_PROD_SUBSET_INTER) THEN ASM_REWRITE_TAC [SUBSET, IN_INTER] THEN MESON_TAC [], REWRITE_TAC [LEFT_IMP_EXISTS_THM, RIGHT_AND_EXISTS_THM, LEFT_AND_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A"), (← q r"c:A"), (← q r"d:A")] THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"ring_add r a (ring_mul r b c):A"), (← q r"ring_mul r b d:A")] THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier r /\ b IN ring_carrier r /\
        c IN ring_carrier r /\ d IN ring_carrier r") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [IN_RING_IDEAL_ADD, IN_RING_IDEAL_LMUL, RING_MUL_IN_IDEAL_PROD] THEN MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC []])

  let CHINESE_REMAINDER_RING_ISOMORPHISM ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!a b c d:A. a IN ring_carrier r /\ b IN ring_carrier r /\
                  c IN ring_carrier r /\ d IN ring_carrier r /\
                  ring_add r c d = ring_1 r
                  ==> ring_sub r a (ring_add r (ring_mul r a d)
                                               (ring_mul r b c)) =
                      ring_mul r (ring_sub r a b) c /\
                      ring_sub r b (ring_add r (ring_mul r a d)
                                               (ring_mul r b c)) =
                      ring_mul r (ring_sub r b a) d")
    prove
      r"!r (j:A->bool) k.
      ring_ideal r j /\ ring_ideal r k /\
      ring_setadd r j k = ring_carrier r
      ==> quotient_ring r (j INTER k) isomorphic_ring
          prod_ring (quotient_ring r j) (quotient_ring r k)"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_kernel (r,prod_ring (quotient_ring r j) (quotient_ring r k))
                  (\x:A. ring_coset r j x,ring_coset r k x) = j INTER k") (SUBST1_TAC o SYM) THENL [ASM_SIMP_TAC [ring_kernel, PROD_RING, QUOTIENT_RING_0, PAIR_EQ] THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"x:A") THEN REWRITE_TAC [IN_ELIM_THM, IN_INTER] THEN ASM_CASES_TAC (← q r"(x:A) IN ring_carrier r") THEN ASM_SIMP_TAC [RING_COSET_EQ_IDEAL] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool")] RING_IDEAL_IMP_SUBSET) THEN ASM SET_TAC [], MATCH_MP_TAC FIRST_RING_EPIMORPHISM_THEOREM] THEN ASM_SIMP_TAC [ring_epimorphism, RING_HOMOMORPHISM_PAIRED, ETA_AX, RING_HOMOMORPHISM_RING_COSET, PROD_RING, QUOTIENT_RING_CARRIER] THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [FORALL_PAIR_THM, IN_IMAGE, IN_CROSS, PAIR_EQ, IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"u:A->bool"), (← q r"v:A->bool")] THEN EQ_TAC THENL [MESON_TAC [], ALL_TAC] THEN DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"a:A") STRIP_ASSUME_TAC) (X_CHOOSE_THEN (← q r"b:A") STRIP_ASSUME_TAC)) THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"k:A->bool")] RING_COMAXIMAL) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"c:A"), (← q r"d:A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(c:A) IN ring_carrier r /\ d IN ring_carrier r") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN EXISTS_TAC (← q r"ring_add r (ring_mul r a d) (ring_mul r b c):A") THEN ASM_SIMP_TAC [RING_COSET_EQ, RING_ADD, RING_MUL] THEN SUBGOAL_THEN (← q r"ring_sub r a (ring_add r (ring_mul r a d) (ring_mul r b c)) =
      ring_mul r (ring_sub r a b) c /\
      ring_sub r b (ring_add r (ring_mul r a d) (ring_mul r b c)) =
      ring_mul r (ring_sub r b a) (d:A)") (CONJUNCTS_THEN SUBST1_TAC) THENL [MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC [], ASM_SIMP_TAC [IN_RING_IDEAL_LMUL, RING_SUB]])

  let RING_ISOMORPHISM_PROD_QUOTIENT_RING ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!a b c d:A. a IN ring_carrier r /\ b IN ring_carrier r /\
                    c IN ring_carrier r /\ d IN ring_carrier r /\
                    ring_add r c d = ring_1 r
                    ==> ring_sub r a (ring_add r (ring_mul r a d)
                                                 (ring_mul r b c)) =
                        ring_mul r (ring_sub r a b) c /\
                        ring_sub r b (ring_add r (ring_mul r a d)
                                                 (ring_mul r b c)) =
                        ring_mul r (ring_sub r b a) d")
    prove
      r"!r j k:A->bool.
          ring_ideal r j /\ ring_ideal r k /\
          ring_setadd r j k = ring_carrier r /\ j INTER k = {ring_0 r}
          ==> ring_isomorphism
               (r,prod_ring (quotient_ring r j) (quotient_ring r k))
               (\x. ring_coset r j x,ring_coset r k x)"
      (REPEAT STRIP_TAC THEN REWRITE_TAC [RING_ISOMORPHISM, PAIR_EQ] THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_PAIRED, ETA_AX, RING_HOMOMORPHISM_RING_COSET, RING_COSET_EQ] THEN CONJ_TAC THENL [ASM_SIMP_TAC [PROD_RING, QUOTIENT_RING_CARRIER] THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [FORALL_PAIR_THM, IN_IMAGE, IN_CROSS, PAIR_EQ, IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"u:A->bool"), (← q r"v:A->bool")] THEN EQ_TAC THENL [MESON_TAC [], ALL_TAC] THEN DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"a:A") STRIP_ASSUME_TAC) (X_CHOOSE_THEN (← q r"b:A") STRIP_ASSUME_TAC)) THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"k:A->bool")] RING_COMAXIMAL) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"c:A"), (← q r"d:A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(c:A) IN ring_carrier r /\ d IN ring_carrier r") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN EXISTS_TAC (← q r"ring_add r (ring_mul r a d) (ring_mul r b c):A") THEN ASM_SIMP_TAC [RING_COSET_EQ, RING_ADD, RING_MUL] THEN SUBGOAL_THEN (← q r"ring_sub r a (ring_add r (ring_mul r a d) (ring_mul r b c)) =
        ring_mul r (ring_sub r a b) c /\
        ring_sub r b (ring_add r (ring_mul r a d) (ring_mul r b c)) =
        ring_mul r (ring_sub r b a) (d:A)") (CONJUNCTS_THEN SUBST1_TAC) THENL [MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC [], ASM_SIMP_TAC [IN_RING_IDEAL_LMUL, RING_SUB]], MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"y:A")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"x:A"), (← q r"y:A")] RING_COSET_EQ) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:A->bool"), (← q r"x:A"), (← q r"y:A")] RING_COSET_EQ) THEN ASM_REWRITE_TAC [] THEN REPEAT DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_sub r x y IN (j INTER k:A->bool)") MP_TAC THENL [ASM_REWRITE_TAC [IN_INTER], ASM_SIMP_TAC [IN_SING, RING_SUB_EQ_0]]])

  let RING_ISOMORPHISM_QUOTIENT_RING_INTER ← prove
    r"!r j k:A->bool.
        ring_ideal r j /\ ring_ideal r k /\ ring_setadd r j k = ring_carrier r
        ==> ?g. ring_isomorphism
                 (quotient_ring r (j INTER k),
                  prod_ring (quotient_ring r j) (quotient_ring r k)) g /\
                !x. x IN ring_carrier r
                    ==> g(ring_coset r (j INTER k) x) =
                        (ring_coset r j x,ring_coset r k x)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"prod_ring (quotient_ring r j) (quotient_ring r (k:A->bool))"), (← q r"j INTER k:A->bool"), (← q r"\x:A. ring_coset r j x,ring_coset r k x")] QUOTIENT_RING_UNIVERSAL_EXPLICIT) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_HOMOMORPHISM_PAIRED, ETA_AX, RING_HOMOMORPHISM_RING_COSET, RING_IDEAL_INTER] THEN REPEAT STRIP_TAC THEN UNDISCH_TAC (← q r"ring_coset r (j INTER k) x = ring_coset r
                 (j INTER k) (y:A)") THEN ASM_SIMP_TAC [RING_COSET_EQ, RING_IDEAL_INTER, PAIR_EQ, IN_INTER], MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"g:(A->bool)->(A->bool)#(A->bool)") THEN STRIP_TAC THEN ASM_REWRITE_TAC []] THEN REWRITE_TAC [(← GSYM RING_MONOMORPHISM_EPIMORPHISM)] THEN ASM_REWRITE_TAC [ring_monomorphism, ring_epimorphism] THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, RING_IDEAL_INTER] THEN CONJ_TAC THENL [REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_GSPEC] THEN X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN X_GEN_TAC (← q r"b:A") THEN DISCH_TAC THEN ASM_SIMP_TAC [PAIR_EQ, RING_COSET_EQ, RING_IDEAL_INTER, IN_INTER], ALL_TAC] THEN REWRITE_TAC [PROD_RING] THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, FORALL_IN_GSPEC] THEN ASM_SIMP_TAC [IN_CROSS, IN_ELIM_THM] THEN MESON_TAC [], ALL_TAC] THEN REWRITE_TAC [SUBSET, FORALL_PAIR_THM, IN_CROSS, IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_GSPEC] THEN X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN X_GEN_TAC (← q r"b:A") THEN DISCH_TAC THEN UNDISCH_TAC (← q r"ring_setadd r j k = ring_carrier(r:A ring)") THEN REWRITE_TAC [EXTENSION] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"ring_1 r:A"))) THEN REWRITE_TAC [RING_1, ring_setadd, IN_ELIM_THM] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"s:A") (X_CHOOSE_THEN (← q r"t:A") STRIP_ASSUME_TAC)) THEN SUBGOAL_THEN (← q r"(s:A) IN ring_carrier r /\ (t:A) IN ring_carrier r") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_add r (ring_mul r a t) (ring_mul r b s) IN ring_carrier(r:A ring)") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_ADD, RING_MUL], ALL_TAC] THEN REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC (← q r"ring_coset r (j INTER k)
               (ring_add r (ring_mul r a t) (ring_mul r b s)):A->bool") THEN CONJ_TAC THENL [ALL_TAC, REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC []] THEN ASM_SIMP_TAC [PAIR_EQ, RING_COSET_EQ] THEN CONJ_TAC THENL [SUBGOAL_THEN (← q r"ring_sub r a (ring_add r (ring_mul r a t) (ring_mul r b s)) =
      ring_mul r (ring_sub r a b) (s:A)") SUBST1_TAC THENL [RING_TAC, ASM_SIMP_TAC [IN_RING_IDEAL_LMUL, RING_SUB]], SUBGOAL_THEN (← q r"ring_sub r b (ring_add r (ring_mul r a t) (ring_mul r b s)) =
      ring_mul r (ring_sub r b a) (t:A)") SUBST1_TAC THENL [RING_TAC, ASM_SIMP_TAC [IN_RING_IDEAL_LMUL, RING_SUB]]])

  let ideal_quotient ← new_definition
    r"ideal_quotient (r:A ring) (j:A->bool) (k:A->bool) =
  {x | x IN ring_carrier r /\
       !y. y IN k ==> ring_mul r x y IN j}"

  let RING_IDEAL_IDEAL_QUOTIENT ← prove
    r"!r:A ring j k.
        ring_ideal r j /\ k SUBSET ring_carrier r
        ==> ring_ideal r (ideal_quotient r j k)"
    (REWRITE_TAC [ring_ideal, ideal_quotient, SUBSET, IN_ELIM_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [RING_0, RING_MUL_LZERO, RING_NEG, RING_MUL_LNEG, RING_ADD, RING_ADD_RDISTRIB, RING_MUL, (← GSYM RING_MUL_ASSOC)])

  let SUBSET_IDEAL_QUOTIENT ← prove
    r"!r j k l:A->bool.
        ring_ideal r j /\ k SUBSET ring_carrier r /\ l SUBSET ring_carrier r
        ==> (l SUBSET ideal_quotient r j k <=> ideal_prod r l k SUBSET j)"
    (REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL [MATCH_MP_TAC IDEAL_PROD_MINIMAL THEN RULE_ASSUM_TAC (REWRITE_RULE [SUBSET, ideal_quotient, IN_ELIM_THM]) THEN ASM_MESON_TAC [], REWRITE_TAC [SUBSET, ideal_quotient, IN_ELIM_THM] THEN ASM_MESON_TAC [SUBSET, RING_MUL_IN_IDEAL_PROD]])

  let IDEAL_SUBSET_IDEAL_QUOTIENT ← prove
    r"!r j k:A->bool.
        ring_ideal r j /\ k SUBSET ring_carrier r
        ==> j SUBSET ideal_quotient r j k"
    (REWRITE_TAC [ideal_quotient, SUBSET, IN_ELIM_THM] THEN MESON_TAC [IN_RING_IDEAL_RMUL, RING_IDEAL_IMP_SUBSET, SUBSET])

  let IDEAL_QUOTIENT_MONO ← prove
    r"!r j j' k k':A->bool.
        j SUBSET j' /\ k' SUBSET k
        ==> ideal_quotient r j k SUBSET ideal_quotient r j' k'"
    (REWRITE_TAC [ideal_quotient] THEN SET_TAC [])

  let IDEAL_QUOTIENT_EQ_CARRIER ← prove
    r"!r j k:A->bool.
        ring_ideal r j /\ k SUBSET ring_carrier r
        ==> (ideal_quotient r j k = ring_carrier r <=> k SUBSET j)"
    (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [RING_IDEAL_EQ_CARRIER, RING_IDEAL_IDEAL_QUOTIENT] THEN REWRITE_TAC [ideal_quotient, IN_ELIM_THM, RING_1] THEN ASM_MESON_TAC [RING_MUL_LID, SUBSET])

  let IDEAL_QUOTIENT_CARRIER ← prove
    r"!r j:A->bool.
        ring_ideal r j ==> ideal_quotient r j (ring_carrier r) = j"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [ideal_quotient, EXTENSION, IN_ELIM_THM] THEN ASM_MESON_TAC [RING_MUL_RID, RING_1, IN_RING_IDEAL_RMUL, RING_IDEAL_IMP_SUBSET, SUBSET])

  -- @@RETURN BEGIN
  return { ideal_prod, RING_IDEAL_IDEAL_PROD, RING_MUL_IN_IDEAL_PROD, IDEAL_PROD_MINIMAL,
           IDEAL_PROD_EXPLICIT, IDEAL_PROD_MONO, IDEAL_PROD_COMM,
           IDEAL_PROD_IDEAL_GENERATED, IDEAL_PROD_AC, IDEAL_PROD_ASSOC,
           IDEAL_PROD_SUBSET_LEFT, IDEAL_PROD_SUBSET_RIGHT, IDEAL_PROD_CARRIER,
           IDEAL_PROD_CARRIER_LEFT, IDEAL_PROD_LZERO, IDEAL_PROD_RZERO,
           IDEAL_PROD_SUBSET_INTER, IDEAL_PROD_EQ_CARRIER, IDEAL_PROD_EQ_ZERO,
           IDEAL_PROD_PRINCIPAL, IDEAL_PROD_SCALE, IDEAL_PROD_PRINCIPAL_SUBSET_CANCEL,
           IDEAL_PROD_PRINCIPAL_CANCEL, IDEAL_PROD_PRINCIPAL_FACTOR,
           IDEAL_PROD_SETADD_LDISTRIB, IDEAL_PROD_SETADD_RDISTRIB,
           IDEAL_PROD_SUBSET_PRIME_IDEAL, IDEAL_PROD_SETADD_SUBSET,
           MAXIMAL_IDEAL_COMAXIMAL, MAXIMAL_IDEAL_COMAXIMAL_MUL, IDEAL_PROD_COMAXIMAL,
           COMAXIMAL_IDEAL_PROD, CHINESE_REMAINDER_RING_ISOMORPHISM,
           RING_ISOMORPHISM_PROD_QUOTIENT_RING, RING_ISOMORPHISM_QUOTIENT_RING_INTER,
           ideal_quotient, RING_IDEAL_IDEAL_QUOTIENT, SUBSET_IDEAL_QUOTIENT,
           IDEAL_SUBSET_IDEAL_QUOTIENT, IDEAL_QUOTIENT_MONO, IDEAL_QUOTIENT_EQ_CARRIER,
           IDEAL_QUOTIENT_CARRIER }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- ideal_arith.ml phrases from line 837 to 1607                           -/
/- ---------------------------------------------------------------------- -/

structure IdealArith02 where
  -- @@FIELDS
  IDEAL_QUOTIENT_IDEAL_PROD : thm
  IDEAL_QUOTIENT_SETADD : thm
  IDEAL_QUOTIENT_INTER : thm
  IDEAL_QUOTIENT_PRIME_IDEAL : thm
  ideal_pow : thm
  IDEAL_POW_0 : thm
  IDEAL_POW_SUC : thm
  IDEAL_POW_ALT : thm
  IDEAL_POW_1 : thm
  IDEAL_POW_CARRIER : thm
  RING_IDEAL_IDEAL_POW : thm
  IDEAL_POW_ADD : thm
  IDEAL_POW_MUL : thm
  RING_MUL_IN_IDEAL_POW : thm
  RING_POW_IN_IDEAL_POW : thm
  IDEAL_POW_MONO : thm
  IDEAL_POW_ANTIMONO : thm
  IDEAL_POW_SUC_SUBSET : thm
  IDEAL_POW_HOMOMORPHIC_IMAGE_SUBSET : thm
  IDEAL_POW_IDEAL_PROD : thm
  IDEAL_POW_PRINCIPAL : thm
  IDEAL_POW_EQ_ZERO : thm
  IDEAL_POW_SUBSET_PRIME_IDEAL : thm
  RADICAL_IDEAL_PROD : thm
  RADICAL_IDEAL_POW : thm
  RADICAL_PRIME_IDEAL_POW : thm
  COMAXIMAL_IDEAL_POW : thm
  IDEAL_POW_SETADD_SUBSET : thm
  ideal_product : thm
  RING_IDEAL_IDEAL_PRODUCT : thm
  RING_PRODUCT_IN_IDEAL_PRODUCT : thm
  IDEAL_PRODUCT_EMPTY : thm
  IDEAL_PRODUCT_EQ : thm
  IDEAL_PRODUCT_INSERT : thm
  IDEAL_PRODUCT_SING : thm
  IDEAL_PRODUCT_MONO : thm
  IDEAL_PRODUCT_SUBSET : thm
  IDEAL_PRODUCT_SUPERSET : thm
  IDEAL_PRODUCT_MUL : thm
  IDEAL_PRODUCT_EQ_ZERO : thm
  IDEAL_PRODUCT_SUBSET_PRIME_IDEAL : thm
  COMAXIMAL_IDEAL_PRODUCT : thm
  CHINESE_REMAINDER_IDEALS : thm
  IDEAL_PRODUCT_MONOMIAL_MUL : thm
  IDEAL_PRODUCT_SETADD_SUBSET : thm
  IDEAL_PRODUCT_PRINCIPAL : thm
  IDEAL_PRODUCT_POW_SETADD_SUBSET : thm
  IDEAL_PRODUCT_IMAGE : thm
  IDEAL_GENERATED_IMAGE_IDEAL_GENERATED : thm
  IDEAL_PROD_HOMOMORPHIC_IMAGE : thm
  IDEAL_PROD_EPIMORPHIC_IMAGE : thm
  RING_FRACTIONATE_IN_IDEAL_PROD : thm
  RING_LOCALIZATION_IDEAL_PROD_SUBSET : thm
  IDEAL_POW_HOMOMORPHIC_IMAGE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupIdealArith02 [HolBase] (D : IdealArithDeps) (BIdealArith01 : IdealArith01) :
    ExceptT String IO IdealArith02 := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, RING_RULE, SET_RULE, SET_TAC,
        TAUT, new_definition, new_recursive_definition, num_CONV, .. } := D
  let { ADD_CLAUSES, ADD_EQ_0, COMAXIMAL_RADICALS, EQ_IMP, EQ_SYM_EQ, EQ_TRANS, ETA_AX,
        EXISTS_IN_INSERT, EXTENSION, FINITE_DELETE, FINITE_EMPTY, FINITE_INDUCT_STRONG,
        FINITE_SUBSET, FINITE_UNION, FORALL_IN_GSPEC, FORALL_IN_IMAGE,
        FORALL_IN_INSERT, FUN_IN_IMAGE, IDEAL_GENERATED_BY_HOMOMORPHIC_IMAGE,
        IDEAL_GENERATED_INC_GEN, IDEAL_GENERATED_MINIMAL, IDEAL_GENERATED_MONO,
        IDEAL_GENERATED_RING_IDEAL, IDEAL_GENERATED_SING_EQ_CARRIER,
        IDEAL_GENERATED_SUBSET_CARRIER_SUBSET, IMAGE_SUBSET, IMP_CONJ, INSERT_SUBSET,
        INTEGRAL_DOMAIN_NONTRIVIAL, INTER_IDEMPOT, IN_DELETE, IN_ELIM_THM, IN_IMAGE,
        IN_INTER, IN_RING_IDEAL_0, IN_RING_IDEAL_ADD, IN_RING_IDEAL_LMUL,
        IN_RING_IDEAL_RMUL, IN_UNION, ITLIST, LEFT_IMP_EXISTS_THM, MONOMIAL_VARS_MUL,
        MULT_CLAUSES, NOT_FORALL_THM, NOT_IMP, NOT_IN_EMPTY, NOT_SUC, PAIRWISE_INSERT,
        PRIME_IDEAL_IMP_PSUBSET, PRIME_IMP_RING_IDEAL, RADICAL_INTER, RADICAL_MONO,
        RADICAL_PRIME_IDEAL, REPLICATE, RIGHT_FORALL_IMP_THM, RING_0, RING_1,
        RING_1_IN_MULTSYS, RING_ADD, RING_ADD_LDISTRIB, .. } := D.core1
  let { RING_ADD_LZERO, RING_ADD_RZERO, RING_COMAXIMAL,
        RING_EPIMORPHISM_IMP_HOMOMORPHISM, RING_FRACTIONATE_IN_CARRIER,
        RING_HOMOMORPHISM_1, RING_HOMOMORPHISM_FRACTIONATE, RING_HOMOMORPHISM_MUL,
        RING_IDEAL_CARRIER, RING_IDEAL_EPIMORPHIC_IMAGE, RING_IDEAL_EQ_CARRIER,
        RING_IDEAL_HOMOMORPHIC_PREIMAGE, RING_IDEAL_IDEAL_GENERATED,
        RING_IDEAL_IMP_NONEMPTY, RING_IDEAL_IMP_SUBSET, RING_IDEAL_QUOTIENT_LMUL,
        RING_IDEAL_SETADD, RING_LOCALEQUIV_IN_CARRIER, RING_LOCALEQUIV_SPLIT_EXPLICIT,
        RING_MUL, RING_MUL_IN_PRIME_IDEAL, RING_POW, RING_POW_ADD, RING_PRODUCT,
        RING_PRODUCT_CLAUSES, RING_PRODUCT_EQ, RING_PRODUCT_IMAGE, RING_SETADD_LSUBSET,
        RING_SETADD_RSUBSET, RING_SETADD_SUBSET_IDEAL, RING_SETMUL, RING_SUB,
        RING_UNIT_1, SELECT_UNIQUE, SING_SUBSET, SUBSET, SUBSET_ANTISYM, SUBSET_REFL,
        SUBSET_TRANS, SUBSET_UNION, TRANSITIVE_STEPWISE_LE, TRIVIAL_RING_10,
        UNION_EMPTY, monomial_mul, monomial_vars, num_RECURSION, o_THM, radical,
        ring_fractionate, ring_homomorphism, ring_pow, ring_setadd, ring_setmul,
        trivial_ring, .. } := D.core2
  let { COMAXIMAL_IDEAL_PROD, IDEAL_PROD_AC, IDEAL_PROD_ASSOC, IDEAL_PROD_CARRIER,
        IDEAL_PROD_CARRIER_LEFT, IDEAL_PROD_COMM, IDEAL_PROD_EQ_ZERO,
        IDEAL_PROD_IDEAL_GENERATED, IDEAL_PROD_MINIMAL, IDEAL_PROD_MONO,
        IDEAL_PROD_PRINCIPAL, IDEAL_PROD_SETADD_SUBSET, IDEAL_PROD_SUBSET_INTER,
        IDEAL_PROD_SUBSET_LEFT, IDEAL_PROD_SUBSET_PRIME_IDEAL, IDEAL_PROD_SUBSET_RIGHT,
        IDEAL_SUBSET_IDEAL_QUOTIENT, RING_IDEAL_IDEAL_PROD, RING_IDEAL_IDEAL_QUOTIENT,
        RING_MUL_IN_IDEAL_PROD, SUBSET_IDEAL_QUOTIENT, ideal_prod, ideal_quotient, .. } := BIdealArith01
  -- @@SCOPE END

  let IDEAL_QUOTIENT_IDEAL_PROD ← prove
    r"!r j k l:A->bool.
        ring_ideal r j /\ k SUBSET ring_carrier r /\ l SUBSET ring_carrier r
        ==> ideal_quotient r j (ideal_prod r k l) =
            ideal_quotient r (ideal_quotient r j k) l"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [EXTENSION] THEN X_GEN_TAC (← q r"x:A") THEN ASM_CASES_TAC (← q r"(x:A) IN ring_carrier r") THENL [ONCE_REWRITE_TAC [(← GSYM SING_SUBSET)], ASM_REWRITE_TAC [ideal_quotient, IN_ELIM_THM]] THEN SUBGOAL_THEN (← q r"{x:A} SUBSET ring_carrier r") ASSUME_TAC THENL [ASM_REWRITE_TAC [SING_SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [SUBSET_IDEAL_QUOTIENT, RING_IDEAL_IDEAL_QUOTIENT, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_PROD] THEN ASM_SIMP_TAC [IDEAL_PROD_AC, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_PROD])

  let IDEAL_QUOTIENT_SETADD ← prove
    r"!r j k l:A->bool.
        ring_ideal r j /\ ring_ideal r k /\ ring_ideal r l
        ==> ideal_quotient r j (ring_setadd r k l) =
            ideal_quotient r j k INTER ideal_quotient r j l"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [ideal_quotient, ring_setadd, EXTENSION, IN_INTER, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:A") THEN ASM_CASES_TAC (← q r"(x:A) IN ring_carrier r") THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:A->bool")] RING_IDEAL_IMP_SUBSET) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"l:A->bool")] RING_IDEAL_IMP_SUBSET) THEN ASM_REWRITE_TAC [SUBSET] THEN REPEAT STRIP_TAC THEN EQ_TAC THENL [DISCH_TAC THEN CONJ_TAC THEN X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THENL [MAP_EVERY EXISTS_TAC [(← q r"y:A"), (← q r"ring_0 r:A")], MAP_EVERY EXISTS_TAC [(← q r"ring_0 r:A"), (← q r"y:A")]] THEN ASM_SIMP_TAC [IN_RING_IDEAL_0, RING_ADD_RZERO, RING_ADD_LZERO], STRIP_TAC THEN MAP_EVERY X_GEN_TAC [(← q r"y:A"), (← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN ASM_SIMP_TAC [RING_ADD_LDISTRIB, IN_RING_IDEAL_ADD]])

  let IDEAL_QUOTIENT_INTER ← prove
    r"!r j k l:A->bool.
        ideal_quotient r (j INTER k) l =
        ideal_quotient r j l INTER ideal_quotient r k l"
    (REWRITE_TAC [ideal_quotient, EXTENSION, IN_INTER, IN_ELIM_THM] THEN MESON_TAC [])

  let IDEAL_QUOTIENT_PRIME_IDEAL ← prove
    r"!r p j:A->bool.
        prime_ideal r p /\ j SUBSET ring_carrier r /\ ~(j SUBSET p)
        ==> ideal_quotient r p j = p"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_SIMP_TAC [IDEAL_SUBSET_IDEAL_QUOTIENT, PRIME_IMP_RING_IDEAL] THEN FIRST_X_ASSUM ((X_CHOOSE_TAC (← q r"y:A")) o (REWRITE_RULE [SUBSET, NOT_FORALL_THM, NOT_IMP])) THEN REWRITE_TAC [ideal_quotient, SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC [RING_MUL_IN_PRIME_IDEAL, SUBSET])

  let ideal_pow ← new_recursive_definition num_RECURSION
    r"(ideal_pow (r:A ring) (j:A->bool) 0 = ring_carrier r) /\
  (ideal_pow r j (SUC n) = ideal_prod r j (ideal_pow r j n))"

  let IDEAL_POW_0 ← prove
    r"!r:A ring j. ideal_pow r j 0 = ring_carrier r"
    (REWRITE_TAC [ideal_pow])

  let IDEAL_POW_SUC ← prove
    r"!r:A ring j n.
        ideal_pow r j (SUC n) = ideal_prod r j (ideal_pow r j n)"
    (REWRITE_TAC [ideal_pow])

  let IDEAL_POW_ALT ← prove
    r"!r:A ring j n.
        ideal_pow r j n =
        if n = 0 then ring_carrier r
        else ITLIST (ideal_prod r) (REPLICATE n j) (ring_carrier r)"
    (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [ideal_pow, REPLICATE, ITLIST, NOT_SUC] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [REPLICATE, ITLIST])

  let IDEAL_POW_1 ← prove
    r"!r:A ring j.
        ring_ideal r j
        ==> ideal_pow r j 1 = j"
    (SIMP_TAC [(← ExceptT.mk (num_CONV (← q r"1"))), ideal_pow, IDEAL_PROD_CARRIER])

  let IDEAL_POW_CARRIER ← prove
    r"!r:A ring n. ideal_pow r (ring_carrier r) n = ring_carrier r"
    (GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC [IDEAL_POW_0, IDEAL_POW_SUC, IDEAL_PROD_CARRIER, RING_IDEAL_CARRIER])

  let RING_IDEAL_IDEAL_POW ← prove
    r"!r:A ring j n. ring_ideal r (ideal_pow r j n)"
    (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC [ideal_pow, RING_IDEAL_CARRIER, RING_IDEAL_IDEAL_PROD])

  let IDEAL_POW_ADD ← prove
    r"!r:A ring j m n.
        j SUBSET ring_carrier r
        ==> ideal_pow r j (m + n) =
            ideal_prod r (ideal_pow r j m) (ideal_pow r j n)"
    (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC [ADD_CLAUSES, ideal_pow, IDEAL_PROD_CARRIER_LEFT, RING_IDEAL_IDEAL_POW, IDEAL_PROD_ASSOC, RING_IDEAL_IMP_SUBSET])

  let IDEAL_POW_MUL ← prove
    r"!r:A ring j m n.
        j SUBSET ring_carrier r
        ==> ideal_pow r j (m * n) = ideal_pow r (ideal_pow r j m) n"
    (REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC ((← q r"n:num"), (← q r"n:num")) THEN INDUCT_TAC THEN ASM_REWRITE_TAC [MULT_CLAUSES, IDEAL_POW_0, IDEAL_POW_SUC] THEN ASM_SIMP_TAC [IDEAL_POW_ADD] THEN MATCH_ACCEPT_TAC IDEAL_PROD_COMM)

  let RING_MUL_IN_IDEAL_POW ← prove
    r"!r j (x:A) y m n.
        j SUBSET ring_carrier r /\
        x IN ideal_pow r j m /\ y IN ideal_pow r j n
        ==> ring_mul r x y IN ideal_pow r j (m + n)"
    (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [IDEAL_POW_ADD] THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_PROD THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [RING_IDEAL_IDEAL_POW, RING_IDEAL_IMP_SUBSET, SUBSET])

  let RING_POW_IN_IDEAL_POW ← prove
    r"!r (j:A->bool) x n.
        ring_ideal r j /\ x IN j ==> ring_pow r x n IN ideal_pow r j n"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SPEC_TAC ((← q r"n:num"), (← q r"n:num")) THEN INDUCT_TAC THEN REWRITE_TAC [ring_pow, IDEAL_POW_0, RING_1] THEN REWRITE_TAC [IDEAL_POW_SUC] THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_PROD THEN ASM_SIMP_TAC [RING_POW])

  let IDEAL_POW_MONO ← prove
    r"!r j k:A->bool n.
        j SUBSET k ==> ideal_pow r j n SUBSET ideal_pow r k n"
    (GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC [ideal_pow, SUBSET_REFL, IDEAL_PROD_MONO])

  let IDEAL_POW_ANTIMONO ← prove
    r"!r j:A->bool m n.
        j SUBSET ring_carrier r /\ m <= n
        ==> ideal_pow r j n SUBSET ideal_pow r j m"
    (GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN REWRITE_TAC [SUBSET_REFL] THEN CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [ideal_pow, IDEAL_PROD_SUBSET_RIGHT, RING_IDEAL_IDEAL_POW])

  let IDEAL_POW_SUC_SUBSET ← prove
    r"!r j:A->bool n.
        ring_ideal r j ==> ideal_pow r j (SUC n) SUBSET ideal_pow r j n"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC IDEAL_POW_ANTIMONO THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET] THEN ARITH_TAC)

  let IDEAL_POW_HOMOMORPHIC_IMAGE_SUBSET ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!t. s SUBSET {x | x IN t /\ (f:A->B) x IN u} ==> IMAGE f s SUBSET u")
    prove
      r"!r r' (f:A->B) j j' n.
          ring_homomorphism(r,r') f /\ ring_ideal r j /\ ring_ideal r' j' /\
          IMAGE f j SUBSET j'
          ==> IMAGE f (ideal_pow r j n) SUBSET ideal_pow r' j' n"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SPEC_TAC ((← q r"n:num"), (← q r"n:num")) THEN INDUCT_TAC THENL [REWRITE_TAC [IDEAL_POW_0] THEN ASM_MESON_TAC [ring_homomorphism], ALL_TAC] THEN REWRITE_TAC [IDEAL_POW_SUC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"r':B ring"), (← q r"f:A->B"), (← q r"ideal_prod r' j' (ideal_pow r' j' n):B->bool")] RING_IDEAL_HOMOMORPHIC_PREIMAGE) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_PROD] THEN DISCH_TAC THEN MATCH_MP_TAC r1 THEN EXISTS_TAC (← q r"ring_carrier r:A->bool") THEN MATCH_MP_TAC IDEAL_PROD_MINIMAL THEN ASM_REWRITE_TAC [] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier r /\ (b:A) IN ring_carrier r") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_POW, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [IN_ELIM_THM, RING_MUL] THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL th)])) THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_PROD THEN ASM_MESON_TAC [ring_homomorphism, SUBSET, FUN_IN_IMAGE])

  let IDEAL_POW_IDEAL_PROD ← prove
    r"!r j k:A->bool n.
        j SUBSET ring_carrier r /\ k SUBSET ring_carrier r
        ==> ideal_pow r (ideal_prod r j k) n =
            ideal_prod r (ideal_pow r j n) (ideal_pow r k n)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SPEC_TAC ((← q r"n:num"), (← q r"n:num")) THEN INDUCT_TAC THEN ASM_SIMP_TAC [ideal_pow, IDEAL_PROD_CARRIER, RING_IDEAL_CARRIER] THEN ASM_SIMP_TAC [IDEAL_PROD_AC, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_PROD, RING_IDEAL_IDEAL_POW])

  let IDEAL_POW_PRINCIPAL ← prove
    r"!r (a:A) n.
        a IN ring_carrier r
        ==> ideal_pow r (ideal_generated r {a}) n =
            ideal_generated r {ring_pow r a n}"
    (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC [ideal_pow, ring_pow, IDEAL_PROD_PRINCIPAL, RING_POW] THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SIMP_TAC [IDEAL_GENERATED_SING_EQ_CARRIER, RING_1, RING_UNIT_1])

  let IDEAL_POW_EQ_ZERO ← prove
    r"!r j:A->bool n.
        integral_domain r /\ ring_ideal r j
        ==> (ideal_pow r j n = {ring_0 r} <=> j = {ring_0 r} /\ ~(n = 0))"
    (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC [ideal_pow, IDEAL_PROD_EQ_ZERO, RING_IDEAL_IDEAL_POW, NOT_SUC] THEN SIMP_TAC [(← GSYM trivial_ring), TRIVIAL_RING_10, INTEGRAL_DOMAIN_NONTRIVIAL] THEN CONV_TAC TAUT)

  let IDEAL_POW_SUBSET_PRIME_IDEAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!s t:A->bool. s PSUBSET t ==> ~(t SUBSET s)")
    prove
      r"!r p j:A->bool n.
          prime_ideal r p /\ j SUBSET ring_carrier r
          ==> (ideal_pow r j n SUBSET p <=> j SUBSET p /\ ~(n = 0))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SPEC_TAC ((← q r"n:num"), (← q r"n:num")) THEN INDUCT_TAC THEN ASM_SIMP_TAC [ideal_pow, IDEAL_PROD_SUBSET_PRIME_IDEAL, NOT_SUC, RING_IDEAL_IDEAL_POW, RING_IDEAL_IMP_SUBSET] THENL [ASM_MESON_TAC [PRIME_IDEAL_IMP_PSUBSET, r1], CONV_TAC TAUT])

  let RADICAL_IDEAL_PROD ← prove
    r"!r j k:A->bool.
        ring_ideal r j /\ ring_ideal r k
        ==> radical r (ideal_prod r j k) = radical r j INTER radical r k"
    (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [(← GSYM RADICAL_INTER)] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_SIMP_TAC [RADICAL_MONO, IDEAL_PROD_SUBSET_INTER] THEN REWRITE_TAC [radical, SUBSET, IN_ELIM_THM, IN_INTER] THEN X_GEN_TAC (← q r"x:A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"n + n:num") THEN ASM_SIMP_TAC [RING_POW_ADD, ADD_EQ_0] THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_PROD THEN ASM_SIMP_TAC [RING_POW])

  let RADICAL_IDEAL_POW ← prove
    r"!r j:A->bool n.
        ring_ideal r j /\ ~(n = 0)
        ==> radical r (ideal_pow r j n) = radical r j"
    (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC [NOT_SUC] THEN ASM_CASES_TAC (← q r"n = 0") THEN ASM_SIMP_TAC [ideal_pow, IDEAL_PROD_CARRIER, RADICAL_IDEAL_PROD, RING_IDEAL_IDEAL_POW, INTER_IDEMPOT])

  let RADICAL_PRIME_IDEAL_POW ← prove
    r"!r p:A->bool n.
        prime_ideal r p /\ ~(n = 0) ==> radical r (ideal_pow r p n) = p"
    (SIMP_TAC [RADICAL_IDEAL_POW, PRIME_IMP_RING_IDEAL, RADICAL_PRIME_IDEAL])

  let COMAXIMAL_IDEAL_POW ← prove
    r"!r j k:A->bool m n.
        ring_ideal r j /\ ring_ideal r k /\
        ring_setadd r j k = ring_carrier r
        ==> ring_setadd r (ideal_pow r j m) (ideal_pow r k n) =
            ring_carrier r"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"ideal_pow r j m SUBSET ring_carrier r /\ ~(ideal_pow r j m = {}) /\
    ideal_pow r k n SUBSET ring_carrier r /\ ~(ideal_pow r k n:A->bool = {})") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IDEAL_POW, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IMP_NONEMPTY], ALL_TAC] THEN ASM_CASES_TAC (← q r"m = 0") THEN ASM_SIMP_TAC [IDEAL_POW_0, RING_SETADD_RSUBSET, RING_IDEAL_CARRIER] THEN ASM_CASES_TAC (← q r"n = 0") THEN ASM_SIMP_TAC [IDEAL_POW_0, RING_SETADD_LSUBSET, RING_IDEAL_CARRIER] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_pow r j m:A->bool"), (← q r"ideal_pow r k n:A->bool")] COMAXIMAL_RADICALS) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, RADICAL_IDEAL_POW] THEN ASM_SIMP_TAC [COMAXIMAL_RADICALS])

  let IDEAL_POW_SETADD_SUBSET ← prove
    r"!r i j:A->bool n.
        ring_ideal r i /\ ring_ideal r j
        ==> ideal_pow r (ring_setadd r i j) n SUBSET
            ring_setadd r i (ideal_pow r j n)"
    (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN REWRITE_TAC [IDEAL_POW_0, IDEAL_POW_SUC] THENL [REWRITE_TAC [SUBSET, ring_setadd, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"ring_0 r:A"), (← q r"x:A")] THEN ASM_SIMP_TAC [IN_RING_IDEAL_0, RING_ADD_LZERO], TRANS_TAC SUBSET_TRANS (← q r"ideal_prod r (ring_setadd r i j)
                   (ring_setadd r i (ideal_pow r j n)):A->bool") THEN ASM_SIMP_TAC [IDEAL_PROD_MONO, SUBSET_REFL, IDEAL_PROD_SETADD_SUBSET, RING_IDEAL_IDEAL_POW]])

  let ideal_product ← new_definition
    r"ideal_product (r:A ring) (s:K->bool) (f:K->A->bool) =
  ideal_generated r {ring_product r s a | a | !i. i IN s ==> a i IN f i}"

  let RING_IDEAL_IDEAL_PRODUCT ← prove
    r"!r:A ring s (f:K->A->bool). ring_ideal r (ideal_product r s f)"
    (REWRITE_TAC [ideal_product, RING_IDEAL_IDEAL_GENERATED])

  let RING_PRODUCT_IN_IDEAL_PRODUCT ← prove
    r"!r s (f:K->A->bool) (a:K->A).
        (!i. i IN s ==> a i IN f i)
        ==> ring_product r s a IN ideal_product r s f"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [ideal_product] THEN MATCH_MP_TAC IDEAL_GENERATED_INC_GEN THEN REWRITE_TAC [RING_PRODUCT, IN_ELIM_THM] THEN ASM_MESON_TAC [])

  let IDEAL_PRODUCT_EMPTY ← prove
    r"!r:A ring (f:K->A->bool). ideal_product r {} f = ring_carrier r"
    (REPEAT GEN_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"{}:K->bool"), (← q r"f:K->A->bool"), (← q r"\i:K. ring_1 r:A")] RING_PRODUCT_IN_IDEAL_PRODUCT) THEN SIMP_TAC [RING_IDEAL_EQ_CARRIER, RING_IDEAL_IDEAL_PRODUCT, NOT_IN_EMPTY, RING_PRODUCT_CLAUSES])

  let IDEAL_PRODUCT_EQ ← prove
    r"!r:A ring s (f:K->A->bool) g.
        (!i. i IN s ==> f i = g i)
        ==> ideal_product r s f = ideal_product r s g"
    (SIMP_TAC [ideal_product])

  let IDEAL_PRODUCT_INSERT ← prove
    r"!r:A ring s (f:K->A->bool) a.
        FINITE s /\ ~(a IN s) /\ ring_ideal r (f a)
        ==> ideal_product r (a INSERT s) f =
            ideal_prod r (f a) (ideal_product r s f)"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [GEN_REWRITE_TAC LAND_CONV [ideal_product] THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN REWRITE_TAC [RING_IDEAL_IDEAL_PROD, SUBSET, FORALL_IN_GSPEC] THEN X_GEN_TAC (← q r"x:K->A") THEN REWRITE_TAC [FORALL_IN_INSERT] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(x:K->A) a IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [RING_PRODUCT_CLAUSES] THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_PROD THEN ASM_SIMP_TAC [RING_PRODUCT, RING_PRODUCT_IN_IDEAL_PRODUCT], MATCH_MP_TAC IDEAL_PROD_MINIMAL THEN REWRITE_TAC [RING_IDEAL_IDEAL_PRODUCT] THEN X_GEN_TAC (← q r"u:A") THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(u:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"{v:A | v IN ring_carrier r /\
              ring_mul r u v IN ideal_product r ((a:K) INSERT s) f}"), (← q r"{ring_product r s x | x | !i. i IN s ==> (x:K->A) i IN f i}")] IDEAL_GENERATED_MINIMAL) THEN ASM_SIMP_TAC [RING_IDEAL_QUOTIENT_LMUL, RING_IDEAL_IDEAL_PRODUCT, (← GSYM ideal_product)] THEN ANTS_TAC THENL [ALL_TAC, SET_TAC []] THEN REWRITE_TAC [SUBSET, FORALL_IN_GSPEC, IN_ELIM_THM, RING_PRODUCT] THEN X_GEN_TAC (← q r"x:K->A") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"(a:K) INSERT s"), (← q r"f:K->A->bool"), (← q r"\i. if i = a then u else (x:K->A) i")] RING_PRODUCT_IN_IDEAL_PRODUCT) THEN ANTS_TAC THENL [REWRITE_TAC [FORALL_IN_INSERT] THEN ASM_MESON_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [RING_PRODUCT_CLAUSES] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC RING_PRODUCT_EQ THEN ASM_MESON_TAC []])

  let IDEAL_PRODUCT_SING ← prove
    r"!r:A ring (f:K->A->bool) a.
        ring_ideal r (f a) ==> ideal_product r {a} f = f a"
    (SIMP_TAC [IDEAL_PRODUCT_INSERT, FINITE_EMPTY, NOT_IN_EMPTY, IDEAL_PRODUCT_EMPTY, IDEAL_PROD_CARRIER])

  let IDEAL_PRODUCT_MONO ← prove
    r"!r s (f:K->A->bool) g.
        (!i. i IN s ==> f i SUBSET g i)
        ==> ideal_product r s f SUBSET ideal_product r s g"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [ideal_product] THEN MATCH_MP_TAC IDEAL_GENERATED_MONO THEN REWRITE_TAC [SUBSET, FORALL_IN_GSPEC, IN_ELIM_THM] THEN ASM_MESON_TAC [SUBSET])

  let IDEAL_PRODUCT_SUBSET ← prove
    r"!r s (f:K->A->bool) a.
        FINITE s /\ (!i. i IN s ==> ring_ideal r (f i)) /\ a IN s
        ==> ideal_product r s f SUBSET f a"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"s = (a:K) INSERT (s DELETE a)") SUBST1_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [IDEAL_PRODUCT_INSERT, FINITE_DELETE, IN_DELETE] THEN MATCH_MP_TAC IDEAL_PROD_SUBSET_LEFT THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_PRODUCT])

  let IDEAL_PRODUCT_SUPERSET ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!s t:K->bool. s SUBSET t ==> s UNION t = t")
    let r2 ← SET_RULE (← q r"!b:K s u. s UNION (b INSERT u) = b INSERT (s UNION u)")
    let r3 ← SET_RULE (← q r"!b:K s u. b IN s ==> s UNION (b INSERT u) = s UNION u")
    prove
      r"!r:A ring s t (f:K->A->bool).
          FINITE t /\ s SUBSET t /\
          (!i. i IN t ==> ring_ideal r (f i)) /\
          (!i. i IN t /\ ~(i IN s) ==> f i = ring_carrier r)
          ==> ideal_product r t f = ideal_product r s f"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"!u. FINITE u
          ==> u SUBSET t
              ==> ideal_product r (s UNION u) (f:K->A->bool) =
                  ideal_product r s f") (MP_TAC o (SPEC (← q r"t:K->bool"))) THENL [MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC [UNION_EMPTY, INSERT_SUBSET] THEN MAP_EVERY X_GEN_TAC [(← q r"b:K"), (← q r"u:K->bool")] THEN REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"(b:K) IN s") THENL [ASM_SIMP_TAC [r3], REWRITE_TAC [r2]] THEN wPart lhand (lhand o rand) IDEAL_PRODUCT_INSERT THEN ANTS_TAC THENL [ASM_REWRITE_TAC [IN_UNION, FINITE_UNION] THEN ASM_MESON_TAC [FINITE_SUBSET, SUBSET, IN_UNION], DISCH_THEN SUBST1_TAC] THEN ASM_SIMP_TAC [IDEAL_PROD_CARRIER_LEFT, RING_IDEAL_IDEAL_PRODUCT], ASM_SIMP_TAC [SUBSET_REFL, r1]])

  let IDEAL_PRODUCT_MUL ← prove
    r"!r:A ring s (f:K->A->bool) g.
        FINITE s /\ (!i. i IN s ==> ring_ideal r (f i) /\ ring_ideal r (g i))
        ==> ideal_product r s (\i. ideal_prod r (f i) (g i)) =
            ideal_prod r (ideal_product r s f) (ideal_product r s g)"
    (GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN SIMP_TAC [IDEAL_PRODUCT_EMPTY, IDEAL_PROD_CARRIER, RING_IDEAL_CARRIER] THEN MAP_EVERY X_GEN_TAC [(← q r"a:K"), (← q r"s:K->bool")] THEN STRIP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC [FORALL_IN_INSERT] THEN STRIP_TAC THEN ASM_SIMP_TAC [IDEAL_PRODUCT_INSERT, RING_IDEAL_IDEAL_PROD] THEN ASM_SIMP_TAC [IDEAL_PROD_AC, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_PROD, RING_IDEAL_IDEAL_PRODUCT])

  let IDEAL_PRODUCT_EQ_ZERO ← prove
    r"!r s (f:K->A->bool).
        integral_domain r /\ FINITE s /\ (!i. i IN s ==> ring_ideal r (f i))
        ==> (ideal_product r s f = {ring_0 r} <=>
             ?i. i IN s /\ f i = {ring_0 r})"
    (GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL [REWRITE_TAC [IDEAL_PRODUCT_EMPTY, NOT_IN_EMPTY, (← GSYM trivial_ring)] THEN ASM_SIMP_TAC [TRIVIAL_RING_10, INTEGRAL_DOMAIN_NONTRIVIAL], REPEAT STRIP_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE [FORALL_IN_INSERT]) THEN ASM_SIMP_TAC [IDEAL_PRODUCT_INSERT, IDEAL_PROD_EQ_ZERO, RING_IDEAL_IDEAL_PRODUCT, EXISTS_IN_INSERT]])

  let IDEAL_PRODUCT_SUBSET_PRIME_IDEAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!s t:A->bool. s PSUBSET t ==> ~(t SUBSET s)")
    prove
      r"!r p s (f:K->A->bool).
          prime_ideal r p /\ FINITE s /\ (!i. i IN s ==> ring_ideal r (f i))
          ==> (ideal_product r s f SUBSET p <=> ?i. i IN s /\ f i SUBSET p)"
      (GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL [REWRITE_TAC [IDEAL_PRODUCT_EMPTY, NOT_IN_EMPTY] THEN ASM_MESON_TAC [PRIME_IDEAL_IMP_PSUBSET, r1], REPEAT STRIP_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE [FORALL_IN_INSERT]) THEN ASM_SIMP_TAC [IDEAL_PRODUCT_INSERT, IDEAL_PROD_SUBSET_PRIME_IDEAL, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_PRODUCT, EXISTS_IN_INSERT]])

  let COMAXIMAL_IDEAL_PRODUCT ← prove
    r"!r j s (f:K->A->bool).
        ring_ideal r j /\ FINITE s /\
        (!i. i IN s ==> ring_ideal r (f i) /\
                        ring_setadd r j (f i) = ring_carrier r)
        ==> ring_setadd r j (ideal_product r s f) = ring_carrier r"
    (GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL [REWRITE_TAC [IDEAL_PRODUCT_EMPTY, NOT_IN_EMPTY] THEN MATCH_MP_TAC RING_SETADD_LSUBSET THEN ASM_MESON_TAC [RING_IDEAL_CARRIER, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IMP_NONEMPTY], REPEAT STRIP_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE [FORALL_IN_INSERT]) THEN ASM_SIMP_TAC [IDEAL_PRODUCT_INSERT, COMAXIMAL_IDEAL_PROD, RING_IDEAL_IDEAL_PRODUCT]])

  let CHINESE_REMAINDER_IDEALS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!u y c d z:A.
          u IN ring_carrier r /\ y IN ring_carrier r /\
          c IN ring_carrier r /\ d IN ring_carrier r /\
          z IN ring_carrier r /\ ring_add r c d = ring_1 r
          ==> ring_sub r (ring_add r (ring_mul r u d) (ring_mul r y c)) z =
              ring_add r (ring_mul r (ring_sub r u y) d) (ring_sub r y z)")
    let r2 ← RING_RULE (← q r"!u y c d:A.
          u IN ring_carrier r /\ y IN ring_carrier r /\
          c IN ring_carrier r /\ d IN ring_carrier r /\
          ring_add r c d = ring_1 r
          ==> ring_sub r (ring_add r (ring_mul r u d) (ring_mul r y c)) u =
              ring_mul r (ring_sub r y u) c")
    prove
      r"!r s (j:K->A->bool) (a:K->A).
          FINITE s /\
          (!i. i IN s ==> ring_ideal r (j i) /\ a i IN ring_carrier r) /\
          pairwise (\i i'. ring_setadd r (j i) (j i') = ring_carrier r) s
          ==> ?x. x IN ring_carrier r /\
                  !i. i IN s ==> ring_sub r x (a i) IN j i"
      (GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL [MESON_TAC [RING_0, NOT_IN_EMPTY], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"b:K"), (← q r"s:K->bool")] THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [(← q r"j:K->A->bool"), (← q r"a:K->A")] THEN REWRITE_TAC [FORALL_IN_INSERT, PAIRWISE_INSERT] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPECL [(← q r"j:K->A->bool"), (← q r"a:K->A")])) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"y:A") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"(j:K->A->bool) b"), (← q r"s:K->bool"), (← q r"j:K->A->bool")] COMAXIMAL_IDEAL_PRODUCT) THEN ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [RING_COMAXIMAL, RING_IDEAL_IDEAL_PRODUCT, LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"c:A"), (← q r"d:A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(c:A) IN ring_carrier r /\ d IN ring_carrier r") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_PRODUCT, SUBSET], ALL_TAC] THEN EXISTS_TAC (← q r"ring_add r (ring_mul r ((a:K->A) b) d) (ring_mul r y c)") THEN ASM_SIMP_TAC [RING_ADD, RING_MUL] THEN CONJ_TAC THENL [SUBGOAL_THEN (← q r"ring_sub r (ring_add r (ring_mul r (a b) d) (ring_mul r y c))
                   ((a:K->A) b) =
        ring_mul r (ring_sub r y (a b)) c") SUBST1_TAC THENL [MATCH_MP_TAC r2 THEN ASM_REWRITE_TAC [], ASM_SIMP_TAC [IN_RING_IDEAL_LMUL, RING_SUB]], X_GEN_TAC (← q r"i:K") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_sub r (ring_add r (ring_mul r (a b) d) (ring_mul r y c))
                   ((a:K->A) i) =
        ring_add r (ring_mul r (ring_sub r (a b) y) d) (ring_sub r y (a i))") SUBST1_TAC THENL [MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [], MATCH_MP_TAC IN_RING_IDEAL_ADD THEN ASM_SIMP_TAC [] THEN MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN ASM_SIMP_TAC [RING_SUB] THEN ASM_MESON_TAC [IDEAL_PRODUCT_SUBSET, SUBSET]]])

  let IDEAL_PRODUCT_MONOMIAL_MUL ← prove
    r"!r (e:(A->bool)->num) f.
        FINITE(monomial_vars e) /\ FINITE(monomial_vars f) /\
        (!p. p IN monomial_vars e UNION monomial_vars f ==> ring_ideal r p)
        ==> ideal_product r (monomial_vars(monomial_mul e f))
                            (\p. ideal_pow r p (monomial_mul e f p)) =
            ideal_prod r
              (ideal_product r (monomial_vars e) (\p. ideal_pow r p (e p)))
              (ideal_product r (monomial_vars f) (\p. ideal_pow r p (f p)))"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [MONOMIAL_VARS_MUL] THEN TRANS_TAC EQ_TRANS (← q r"ideal_product r (monomial_vars e UNION monomial_vars f)
      (\p. ideal_prod r (ideal_pow r p (e p))
                        (ideal_pow r p ((f:(A->bool)->num) p)))") THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_PRODUCT_EQ THEN ASM_SIMP_TAC [monomial_mul, IDEAL_POW_ADD, RING_IDEAL_IMP_SUBSET], ASM_SIMP_TAC [IDEAL_PRODUCT_MUL, FINITE_UNION, RING_IDEAL_IDEAL_POW] THEN BINOP_TAC THEN MATCH_MP_TAC IDEAL_PRODUCT_SUPERSET THEN ASM_SIMP_TAC [FINITE_UNION, RING_IDEAL_IDEAL_POW, SUBSET_UNION] THEN REWRITE_TAC [monomial_vars, IN_ELIM_THM] THEN SIMP_TAC [ideal_pow]])

  let IDEAL_PRODUCT_SETADD_SUBSET ← prove
    r"!r i s (f:K->A->bool).
        FINITE s /\ ring_ideal r i /\ (!x. x IN s ==> ring_ideal r (f x))
        ==> ideal_product r s (\x. ring_setadd r i (f x)) SUBSET
            ring_setadd r i (ideal_product r s f)"
    (GEN_TAC THEN GEN_TAC THEN ASM_CASES_TAC (← q r"ring_ideal r (i:A->bool)") THEN ASM_REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL [REPEAT STRIP_TAC THEN REWRITE_TAC [IDEAL_PRODUCT_EMPTY] THEN REWRITE_TAC [SUBSET, ring_setadd, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"ring_0 r:A"), (← q r"x:A")] THEN ASM_SIMP_TAC [IN_RING_IDEAL_0, RING_ADD_LZERO], MAP_EVERY X_GEN_TAC [(← q r"a:K"), (← q r"s:K->bool")] THEN STRIP_TAC THEN X_GEN_TAC (← q r"f:K->A->bool") THEN REWRITE_TAC [FORALL_IN_INSERT] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [IDEAL_PRODUCT_INSERT, RING_IDEAL_SETADD] THEN TRANS_TAC SUBSET_TRANS (← q r"ideal_prod r (ring_setadd r i ((f:K->A->bool) a))
                   (ring_setadd r i (ideal_product r s f))") THEN ASM_SIMP_TAC [IDEAL_PROD_MONO, SUBSET_REFL, IDEAL_PROD_SETADD_SUBSET, RING_IDEAL_IDEAL_PRODUCT]])

  let IDEAL_PRODUCT_PRINCIPAL ← prove
    r"!r s (a:K->A).
        FINITE s /\ (!i. i IN s ==> a i IN ring_carrier r)
        ==> ideal_product r s (\i. ideal_generated r {a i}) =
            ideal_generated r {ring_product r s a}"
    (GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN SIMP_TAC [IDEAL_PRODUCT_EMPTY, RING_PRODUCT_CLAUSES, FORALL_IN_INSERT] THEN CONJ_TAC THENL [ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SIMP_TAC [IDEAL_GENERATED_SING_EQ_CARRIER, RING_1, RING_UNIT_1], REPEAT STRIP_TAC] THEN ASM_SIMP_TAC [IDEAL_PRODUCT_INSERT, RING_IDEAL_IDEAL_GENERATED, IDEAL_PROD_PRINCIPAL, RING_PRODUCT])

  let IDEAL_PRODUCT_POW_SETADD_SUBSET ← prove
    r"!r q s (x:K->A) e.
        ring_ideal r q /\ FINITE s /\ (!i. i IN s ==> x i IN ring_carrier r) /\
        ring_product r s (\i. ring_pow r (x i) (e i)) IN q
        ==> ideal_product r s
              (\i. ideal_pow r (ring_setadd r q (ideal_generated r {x i}))
                             (e i)) SUBSET q"
    (REPEAT STRIP_TAC THEN TRANS_TAC SUBSET_TRANS (← q r"ideal_product r s
      (\i. ring_setadd r q
             (ideal_generated r {ring_pow r ((x:K->A) i) (e i)}))") THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_PRODUCT_MONO THEN ASM_SIMP_TAC [(← GSYM IDEAL_POW_PRINCIPAL), IDEAL_POW_SETADD_SUBSET, RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN TRANS_TAC SUBSET_TRANS (← q r"ring_setadd r q
      (ideal_product r s
        (\i. ideal_generated r {ring_pow r ((x:K->A) i) (e i)}))") THEN ASM_SIMP_TAC [IDEAL_PRODUCT_SETADD_SUBSET, RING_IDEAL_IDEAL_GENERATED] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:K->bool"), (← q r"\i. ring_pow r ((x:K->A) i) (e i)")] IDEAL_PRODUCT_PRINCIPAL) THEN ASM_SIMP_TAC [RING_POW] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SETADD_SUBSET_IDEAL THEN ASM_REWRITE_TAC [SUBSET_REFL] THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET])

  let IDEAL_PRODUCT_IMAGE ← prove
    r"!r (f:K->L) s (g:L->A->bool).
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> ideal_product r (IMAGE f s) g = ideal_product r s (g o f)"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [ideal_product] THEN AP_TERM_TAC THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_PRODUCT_IMAGE th)])) THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM, FORALL_IN_IMAGE, o_THM] THEN X_GEN_TAC (← q r"z:A") THEN EQ_TAC THEN STRIP_TAC THENL [EXISTS_TAC (← q r"(a:L->A) o (f:K->L)") THEN ASM_REWRITE_TAC [o_THM], EXISTS_TAC (← q r"\y:L. (a:K->A) (@x. x IN s /\ (f:K->L) x = y)") THEN SUBGOAL_THEN (← q r"!x. x IN s ==> (@x'. x' IN s /\ (f:K->L) x' = f x) = x") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC [], ASM_SIMP_TAC [] THEN MATCH_MP_TAC RING_PRODUCT_EQ THEN ASM_SIMP_TAC [o_THM]]])

  let IDEAL_GENERATED_IMAGE_IDEAL_GENERATED ← prove
    r"!r s (h:A->B) t.
        ring_homomorphism(r,s) h /\ t SUBSET ring_carrier r
        ==> ideal_generated s (IMAGE h (ideal_generated r t)) =
            ideal_generated s (IMAGE h t)"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_SIMP_TAC [IDEAL_GENERATED_BY_HOMOMORPHIC_IMAGE, RING_IDEAL_IDEAL_GENERATED], MATCH_MP_TAC IDEAL_GENERATED_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_SIMP_TAC [IDEAL_GENERATED_SUBSET_CARRIER_SUBSET]])

  let IDEAL_PROD_HOMOMORPHIC_IMAGE ← prove
    r"!r s (h:A->B) j k.
        ring_homomorphism(r,s) h /\
        j SUBSET ring_carrier r /\ k SUBSET ring_carrier r
        ==> ideal_generated s (IMAGE h (ideal_prod r j k)) =
            ideal_prod s (ideal_generated s (IMAGE h j))
                         (ideal_generated s (IMAGE h k))"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [ring_homomorphism])) THEN SUBGOAL_THEN (← q r"IMAGE (h:A->B) j SUBSET ring_carrier s /\
                IMAGE h k SUBSET ring_carrier s") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [ideal_prod, IDEAL_GENERATED_IMAGE_IDEAL_GENERATED, RING_SETMUL, IDEAL_PROD_IDEAL_GENERATED] THEN AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, ring_setmul, IN_IMAGE, IN_ELIM_THM] THEN ASM SET_TAC [])

  let IDEAL_PROD_EPIMORPHIC_IMAGE ← prove
    r"!r s (h:A->B) j k.
        ring_epimorphism(r,s) h /\
        j SUBSET ring_carrier r /\ k SUBSET ring_carrier r
        ==> IMAGE h (ideal_prod r j k) = ideal_prod s (IMAGE h j) (IMAGE h k)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_EPIMORPHISM_IMP_HOMOMORPHISM)) THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (← q r"ideal_generated s (IMAGE (h:A->B) (ideal_prod r j k))") THEN CONJ_TAC THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC IDEAL_GENERATED_RING_IDEAL THEN MATCH_MP_TAC RING_IDEAL_EPIMORPHIC_IMAGE THEN EXISTS_TAC (← q r"r:A ring") THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_PROD], ASM_SIMP_TAC [IDEAL_PROD_HOMOMORPHIC_IMAGE] THEN MATCH_MP_TAC IDEAL_PROD_IDEAL_GENERATED THEN RULE_ASSUM_TAC (REWRITE_RULE [ring_homomorphism]) THEN ASM SET_TAC []])

  let RING_FRACTIONATE_IN_IDEAL_PROD ← prove
    r"!r s j k (z:A).
        ring_multsys r s /\ j SUBSET ring_carrier r /\
        k SUBSET ring_carrier r /\ z IN ideal_prod r j k
        ==> ring_fractionate r s z IN
            ideal_prod (ring_localization r s)
              {ring_localequiv r s (a,b) | a,b | a IN j /\ b IN s}
              {ring_localequiv r s (a,b) | a,b | a IN k /\ b IN s}"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ideal_prod r j k SUBSET
    {z:A | z IN ring_carrier r /\
           ring_fractionate r s z IN
           ideal_prod (ring_localization r s)
             {ring_localequiv r s (a,b) | a,b | a IN j /\ b IN s}
             {ring_localequiv r s (a,b) | a,b | a IN k /\ b IN s}}") MP_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN GEN_REWRITE_TAC LAND_CONV [ideal_prod] THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN CONJ_TAC THENL [REWRITE_TAC [SUBSET, ring_setmul, FORALL_IN_GSPEC] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier r /\ (b:A) IN ring_carrier r") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_SIMP_TAC [RING_MUL] THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL (← MATCH_MP RING_HOMOMORPHISM_FRACTIONATE th))])) THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_PROD THEN ASM_SIMP_TAC [RING_FRACTIONATE_IN_CARRIER] THEN REWRITE_TAC [ring_fractionate, IN_ELIM_THM] THEN ASM_MESON_TAC [RING_1_IN_MULTSYS], MATCH_MP_TAC RING_IDEAL_HOMOMORPHIC_PREIMAGE THEN EXISTS_TAC (← q r"ring_localization r (s:A->bool)") THEN REWRITE_TAC [ETA_AX] THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_FRACTIONATE, RING_IDEAL_IDEAL_PROD]])

  let RING_LOCALIZATION_IDEAL_PROD_SUBSET ← prove
    r"!r s j k:A->bool.
        ring_multsys r s /\ j SUBSET ring_carrier r /\ k SUBSET ring_carrier r
        ==> {ring_localequiv r s (a,b) | a,b |
             a IN ideal_prod r j k /\ b IN s} SUBSET
            ideal_prod (ring_localization r s)
              {ring_localequiv r s (a,b) | a,b | a IN j /\ b IN s}
              {ring_localequiv r s (a,b) | a,b | a IN k /\ b IN s}"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_PROD, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [RING_LOCALEQUIV_SPLIT_EXPLICIT] THEN MATCH_MP_TAC IN_RING_IDEAL_RMUL THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_PROD, RING_LOCALEQUIV_IN_CARRIER, RING_1, RING_FRACTIONATE_IN_IDEAL_PROD])

  let IDEAL_POW_HOMOMORPHIC_IMAGE ← prove
    r"!r s (h:A->B) j n.
        ring_homomorphism(r,s) h /\ j SUBSET ring_carrier r
        ==> ideal_generated s (IMAGE h (ideal_pow r j n)) =
            ideal_pow s (ideal_generated s (IMAGE h j)) n"
    (REPLICATE_TAC 4 GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN STRIP_TAC THEN INDUCT_TAC THEN REWRITE_TAC [IDEAL_POW_0, IDEAL_POW_SUC] THENL [SIMP_TAC [RING_IDEAL_EQ_CARRIER, RING_IDEAL_IDEAL_GENERATED] THEN MATCH_MP_TAC IDEAL_GENERATED_INC_GEN THEN REWRITE_TAC [RING_1] THEN FIRST_ASSUM (SUBST1_TAC o (SYM o (MATCH_MP RING_HOMOMORPHISM_1))) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC [RING_1], ASM_SIMP_TAC [IDEAL_PROD_HOMOMORPHIC_IMAGE, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_POW]])

  -- @@RETURN BEGIN
  return { IDEAL_QUOTIENT_IDEAL_PROD, IDEAL_QUOTIENT_SETADD, IDEAL_QUOTIENT_INTER,
           IDEAL_QUOTIENT_PRIME_IDEAL, ideal_pow, IDEAL_POW_0, IDEAL_POW_SUC,
           IDEAL_POW_ALT, IDEAL_POW_1, IDEAL_POW_CARRIER, RING_IDEAL_IDEAL_POW,
           IDEAL_POW_ADD, IDEAL_POW_MUL, RING_MUL_IN_IDEAL_POW, RING_POW_IN_IDEAL_POW,
           IDEAL_POW_MONO, IDEAL_POW_ANTIMONO, IDEAL_POW_SUC_SUBSET,
           IDEAL_POW_HOMOMORPHIC_IMAGE_SUBSET, IDEAL_POW_IDEAL_PROD, IDEAL_POW_PRINCIPAL,
           IDEAL_POW_EQ_ZERO, IDEAL_POW_SUBSET_PRIME_IDEAL, RADICAL_IDEAL_PROD,
           RADICAL_IDEAL_POW, RADICAL_PRIME_IDEAL_POW, COMAXIMAL_IDEAL_POW,
           IDEAL_POW_SETADD_SUBSET, ideal_product, RING_IDEAL_IDEAL_PRODUCT,
           RING_PRODUCT_IN_IDEAL_PRODUCT, IDEAL_PRODUCT_EMPTY, IDEAL_PRODUCT_EQ,
           IDEAL_PRODUCT_INSERT, IDEAL_PRODUCT_SING, IDEAL_PRODUCT_MONO,
           IDEAL_PRODUCT_SUBSET, IDEAL_PRODUCT_SUPERSET, IDEAL_PRODUCT_MUL,
           IDEAL_PRODUCT_EQ_ZERO, IDEAL_PRODUCT_SUBSET_PRIME_IDEAL,
           COMAXIMAL_IDEAL_PRODUCT, CHINESE_REMAINDER_IDEALS, IDEAL_PRODUCT_MONOMIAL_MUL,
           IDEAL_PRODUCT_SETADD_SUBSET, IDEAL_PRODUCT_PRINCIPAL,
           IDEAL_PRODUCT_POW_SETADD_SUBSET, IDEAL_PRODUCT_IMAGE,
           IDEAL_GENERATED_IMAGE_IDEAL_GENERATED, IDEAL_PROD_HOMOMORPHIC_IMAGE,
           IDEAL_PROD_EPIMORPHIC_IMAGE, RING_FRACTIONATE_IN_IDEAL_PROD,
           RING_LOCALIZATION_IDEAL_PROD_SUBSET, IDEAL_POW_HOMOMORPHIC_IMAGE }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- ideal_arith.ml phrases from line 1621 to 2324                          -/
/- ---------------------------------------------------------------------- -/

structure IdealArith03 where
  -- @@FIELDS
  RING_ISOMORPHISM_IDEAL_POW : thm
  IDEAL_PRODUCT_HOMOMORPHIC_IMAGE : thm
  IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0 : thm
  IDEAL_EXTENSION_POW_SUPPLEMENT : thm
  IDEAL_PRODUCT_COMAXIMAL : thm
  CHINESE_REMAINDER_PRODUCT_RING : thm
  NOETHERIAN_RING_INDUCT : thm
  NOETHERIAN_PRIME_PRODUCT_SUBSET : thm
  PRIME_AVOIDANCE : thm
  IDEAL_PROD_IDEAL_GENERATED_FINITE : thm
  NAKAYAMA_LEMMA : thm
  NAKAYAMA_LEMMA_MAXIMAL : thm
  NAKAYAMA_LEMMA_LOCAL : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupIdealArith03 [HolBase] (D : IdealArithDeps) (BIdealArith01 : IdealArith01) (BIdealArith02 : IdealArith02) :
    ExceptT String IO IdealArith03 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, RING_RULE, SET_RULE, SET_TAC,
        TAUT, WF_INDUCT_TAC, .. } := D
  let { CARD_DELETE, CARD_EQ_0, EQ_IMP, ETA_AX, EXISTS_UNIQUE_DEF, EXTENSION,
        FINITELY_GENERATED_IMP_RING_IDEAL, FINITE_DELETE, FINITE_INDUCT_STRONG,
        FINITE_UNION, FIRST_RING_EPIMORPHISM_THEOREM, FORALL_IN_GSPEC, FORALL_IN_IMAGE,
        FORALL_IN_INSERT, FUN_IN_IMAGE, IDEAL_GENERATED_0, IDEAL_GENERATED_FINITE,
        IDEAL_GENERATED_INC, IDEAL_GENERATED_INC_GEN, IDEAL_GENERATED_INDUCT,
        IDEAL_GENERATED_MINIMAL, IDEAL_GENERATED_MONO, IDEAL_GENERATED_RING_IDEAL,
        IDEAL_GENERATED_SING_EQ_CARRIER, IDEAL_GENERATED_SUBSET_CARRIER,
        IDEAL_GENERATED_SUBSET_CARRIER_SUBSET, IMAGE_CLAUSES, IMP_CONJ, INSERT_SUBSET,
        INTERS_0, INTERS_GSPEC, INTERS_INSERT, INTER_UNIV, IN_CARTESIAN_PRODUCT,
        IN_DELETE, IN_ELIM_THM, IN_IMAGE, IN_INSERT, IN_INTER, IN_RING_IDEAL_0,
        IN_RING_IDEAL_ADD, IN_RING_IDEAL_LMUL, IN_RING_IDEAL_MUL, IN_RING_IDEAL_NEG,
        IN_RING_IDEAL_RMUL, IN_RING_IDEAL_SUB, IN_RING_IDEAL_SUM, IN_UNION, IN_UNIONS,
        LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM, MAXIMAL_IDEAL_EXISTS,
        MAXIMAL_IDEAL_IMP_SUBSET, MAXIMAL_IMP_PROPER_IDEAL, MAXIMAL_IMP_RING_IDEAL,
        MAXIMAL_SUPERIDEAL_EXISTS, MONOMIAL_1, MONOMIAL_MONO, MONOMIAL_VAR,
        MONOMIAL_VARS_1, MONOMIAL_VARS_MUL, MONOMIAL_VARS_VAR, MONO_EXISTS,
        NOETHERIAN_RING, NOT_EXISTS_THM, NOT_FORALL_THM, NOT_IMP, PAIRWISE_INSERT,
        PRIME_IMP_RING_IDEAL, PRODUCT_RING, PROPER_IDEAL, PROPER_IDEAL_ALT,
        PSUBSET_ALT, QUOTIENT_RING_0, QUOTIENT_RING_1, QUOTIENT_RING_CARRIER,
        RESTRICTION, RESTRICTION_EXTENSION, RESTRICTION_IN_CARTESIAN_PRODUCT,
        RESTRICTION_IN_EXTENSIONAL, RESTRICTION_UNIQUE, RIGHT_AND_EXISTS_THM,
        RIGHT_EXISTS_IMP_THM, RIGHT_FORALL_IMP_THM, RIGHT_IMP_EXISTS_THM, RING_0,
        RING_1, RING_1_NOT_IN_PRIME_IDEAL, RING_ADD, .. } := D.core1
  let { RING_ADD_RDISTRIB, RING_ADD_SYM, RING_COSET_EQ, RING_COSET_EQ_IDEAL, RING_DET,
        RING_DET_DEPENDENT_COLUMNS_MUL_IDEAL, RING_DET_EQ, RING_DET_HOMOMORPHISM,
        RING_DET_I, RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_1,
        RING_HOMOMORPHISM_COMPONENTWISE, RING_HOMOMORPHISM_IN_CARRIER,
        RING_HOMOMORPHISM_NEG, RING_HOMOMORPHISM_RING_COSET,
        RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IMP_SUBSET,
        RING_IDEAL_ISOMORPHIC_IMAGE_EQ, RING_IDEAL_QUOTIENT_LMUL,
        RING_ISOMORPHISM_IMP_HOMOMORPHISM, RING_MONOMORPHISM_EQ_0,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL, RING_MUL_ASSOC,
        RING_MUL_IN_PRIME_IDEAL, RING_MUL_LID, RING_MUL_LNEG, RING_MUL_LZERO,
        RING_MUL_RID, RING_MUL_SYM, RING_NEG, RING_PRODUCT, RING_PRODUCT_CLAUSES,
        RING_PRODUCT_CLOSED, RING_SUB, RING_SUB_LZERO, RING_SUB_RDISTRIB,
        RING_SUB_REFL, RING_SUB_RZERO, RING_SUM, RING_SUM_0, RING_SUM_ADD,
        RING_SUM_DELTA, RING_SUM_EQ, RING_SUM_LMUL, RING_SUM_NEG, RING_SUM_SUB,
        RING_UNIT_1, SIMPLE_IMAGE, SING_SUBSET, SKOLEM_THM, SUBSET, SUBSET_ANTISYM,
        SUBSET_ANTISYM_EQ, SUBSET_REFL, SUBSET_TRANS, UNIONS_MAXIMAL_IDEALS,
        UNION_SUBSET, WF_IND, finitely_generated_ideal, local_ring, monomial,
        monomial_var, prime_ideal, ring_epimorphism, ring_ideal, ring_kernel,
        ring_setadd, ring_unit, trivial_ring, .. } := D.core2
  let { IDEAL_PROD_COMAXIMAL, IDEAL_PROD_IDEAL_GENERATED, IDEAL_PROD_MINIMAL,
        IDEAL_PROD_MONO, RING_IDEAL_IDEAL_PROD, RING_MUL_IN_IDEAL_PROD, .. } := BIdealArith01
  let { CHINESE_REMAINDER_IDEALS, COMAXIMAL_IDEAL_PRODUCT, IDEAL_POW_0, IDEAL_POW_1,
        IDEAL_POW_HOMOMORPHIC_IMAGE, IDEAL_POW_SUC, IDEAL_PRODUCT_EMPTY,
        IDEAL_PRODUCT_INSERT, IDEAL_PRODUCT_MONOMIAL_MUL, IDEAL_PRODUCT_SING,
        IDEAL_PROD_HOMOMORPHIC_IMAGE, RING_IDEAL_IDEAL_POW, RING_IDEAL_IDEAL_PRODUCT, .. } := BIdealArith02
  -- @@SCOPE END

  let RING_ISOMORPHISM_IDEAL_POW ← prove
    r"!r r' (f:A->B) j n.
        ring_isomorphism(r,r') f /\ ring_ideal r j
        ==> IMAGE f (ideal_pow r j n) = ideal_pow r' (IMAGE f j) n"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"r':B ring"), (← q r"f:A->B"), (← q r"j:A->bool"), (← q r"n:num")] IDEAL_POW_HOMOMORPHIC_IMAGE) THEN ASM_SIMP_TAC [RING_ISOMORPHISM_IMP_HOMOMORPHISM, RING_IDEAL_IMP_SUBSET] THEN SUBGOAL_THEN (← q r"!i:A->bool. ring_ideal r i ==> ideal_generated r' (IMAGE (f:A->B) i) =
                                   IMAGE f i") (fun th => ASM_SIMP_TAC [th, RING_IDEAL_IDEAL_POW]) THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC IDEAL_GENERATED_RING_IDEAL THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"r':B ring"), (← q r"f:A->B"), (← q r"i:A->bool")] RING_IDEAL_ISOMORPHIC_IMAGE_EQ) THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET])

  let IDEAL_PRODUCT_HOMOMORPHIC_IMAGE ← prove
    r"!r s (h:A->B) t (f:K->A->bool).
        ring_homomorphism(r,s) h /\ FINITE t /\
        (!i. i IN t ==> ring_ideal r (f i))
        ==> ideal_generated s (IMAGE h (ideal_product r t f)) =
            ideal_product s t (\i. ideal_generated s (IMAGE h (f i)))"
    (REPLICATE_TAC 3 GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL [GEN_TAC THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"h:A->B"), (← q r"ring_carrier r:A->bool"), (← q r"0")] IDEAL_POW_HOMOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [IDEAL_PRODUCT_EMPTY, IDEAL_POW_0, SUBSET_REFL], MAP_EVERY X_GEN_TAC [(← q r"a:K"), (← q r"t:K->bool")] THEN STRIP_TAC THEN X_GEN_TAC (← q r"f:K->A->bool") THEN REWRITE_TAC [FORALL_IN_INSERT] THEN STRIP_TAC THEN ASM_SIMP_TAC [IDEAL_PRODUCT_INSERT, RING_IDEAL_IDEAL_GENERATED] THEN ASM_SIMP_TAC [IDEAL_PROD_HOMOMORPHIC_IMAGE, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_PRODUCT]])

  let IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0 ← prove
    r"!r s (h:A->B) j.
        ring_monomorphism(r,s) h /\ ring_ideal r j
        ==> (ideal_generated s (IMAGE h j) = {ring_0 s} <=> j = {ring_0 r})"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN EQ_TAC THENL [DISCH_TAC, DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [IMAGE_CLAUSES] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_0 th)])) THEN REWRITE_TAC [IDEAL_GENERATED_0]] THEN MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"IMAGE (h:A->B) j")] IDEAL_GENERATED_SUBSET_CARRIER) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"h:A->B")] RING_HOMOMORPHISM_IN_CARRIER) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"h:A->B")] RING_MONOMORPHISM_EQ_0) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool")] IN_RING_IDEAL_0) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool")] RING_IDEAL_IMP_SUBSET) THEN ASM_REWRITE_TAC [] THEN SET_TAC [])

  let IDEAL_EXTENSION_POW_SUPPLEMENT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"x = ring_add (r:B ring) m (ring_sub r x m)")
    let r2 ← RING_RULE (← q r"ring_mul (r:B ring) (ring_mul r x y) z =
          ring_mul r y (ring_mul r x z)")
    let r3 ← RING_RULE (← q r"ring_sub (r:B ring) (ring_mul r a z) (ring_mul r a m) =
          ring_mul r a (ring_sub r z m)")
    let r4 ← RING_RULE (← q r"ring_sub (r:B ring) (ring_neg r x) (ring_neg r m) =
        ring_neg r (ring_sub r x m)")
    let r5 ← RING_RULE (← q r"ring_sub (r:B ring) (ring_add r x y) (ring_add r m n) =
        ring_add r (ring_sub r x m) (ring_sub r y n)")
    let r6 ← SET_RULE (← q r"!x:B s t. x IN s /\ s SUBSET t ==> x IN t")
    prove
      r"!r:A ring s:B ring h j M.
          ring_homomorphism(r,s) h /\ j SUBSET ring_carrier r /\
          M SUBSET ring_carrier s /\ ring_0 s IN M /\
          (!x y. x IN M /\ y IN M ==> ring_add s x y IN M) /\
          (!a x. a IN ring_carrier r /\ x IN M ==> ring_mul s (h a) x IN M) /\
          (!x. x IN ring_carrier s
               ==> ?m. m IN M /\
                       ring_sub s x m IN ideal_generated s (IMAGE h j))
          ==> !t x. x IN ring_carrier s
                    ==> ?m. m IN M /\
                            ring_sub s x m IN
                            ideal_generated s (IMAGE h (ideal_pow r j t))"
      (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "add") (CONJUNCTS_THEN2 (LABEL_TAC "smul") (LABEL_TAC "one"))))))) THEN SUBGOAL_THEN (← q r"!x:B. x IN M ==> ring_neg s x IN M") (LABEL_TAC "neg") THENL [X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier s") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_neg s x = ring_mul s ((h:A->B) (ring_neg r (ring_1 r))) (x:B)") SUBST1_TAC THENL [ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_NEG (← ASSUME (← q r"ring_homomorphism(r:A ring,s:B ring) h"))), (← MATCH_MP RING_HOMOMORPHISM_1 (← ASSUME (← q r"ring_homomorphism(r:A ring,s:B ring) h"))), RING_1, RING_MUL_LNEG, RING_MUL_LID], USE_THEN "smul" MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_NEG, RING_1]], ALL_TAC] THEN INDUCT_TAC THENL [X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN EXISTS_TAC (← q r"ring_0 s:B") THEN ASM_SIMP_TAC [RING_SUB_RZERO, IDEAL_POW_0] THEN MATCH_MP_TAC r6 THEN EXISTS_TAC (← q r"ideal_generated s {ring_1 s:B}") THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"ring_1 s:B")] IDEAL_GENERATED_SING_EQ_CARRIER) THEN REWRITE_TAC [RING_1, RING_UNIT_1] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [], MATCH_MP_TAC IDEAL_GENERATED_MONO THEN REWRITE_TAC [SING_SUBSET] THEN REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC (← q r"ring_1 r:A") THEN ASM_MESON_TAC [RING_HOMOMORPHISM_1, RING_1]], POP_ASSUM (LABEL_TAC "ih")] THEN ABBREV_TAC (← q r"E = ideal_generated s (IMAGE (h:A->B) (ideal_pow r j (SUC t)))") THEN SUBGOAL_THEN (← q r"ring_ideal s (E:B->bool)") ASSUME_TAC THENL [EXPAND_TAC "E" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN ABBREV_TAC (← q r"S = {y | y IN ring_carrier s /\
               ?m:B. m IN M /\ ring_sub s y m IN E}") THEN SUBGOAL_THEN (← q r"!x:B. x IN ring_carrier s ==> x IN S") (fun th => tactic_of do pure (X_GEN_TAC (← q r"x:B") THEN DISCH_THEN (MP_TAC o (MATCH_MP th)) THEN EXPAND_TAC "S" THEN SIMP_TAC [IN_ELIM_THM])) THEN SUBGOAL_THEN (← q r"ring_0 s IN (S:B->bool)") ASSUME_TAC THENL [EXPAND_TAC "S" THEN REWRITE_TAC [IN_ELIM_THM, RING_0] THEN EXISTS_TAC (← q r"ring_0 s:B") THEN ASM_SIMP_TAC [RING_SUB_REFL, RING_0, IN_RING_IDEAL_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x y. x IN S /\ y IN S ==> ring_add s x y IN (S:B->bool)") ASSUME_TAC THENL [EXPAND_TAC "S" THEN REWRITE_TAC [IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"x:B"), (← q r"y:B")] THEN DISCH_THEN (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"m:B") STRIP_ASSUME_TAC)) (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"m':B") STRIP_ASSUME_TAC))) THEN ASM_SIMP_TAC [RING_ADD] THEN EXISTS_TAC (← q r"ring_add s m m':B") THEN CONJ_TAC THENL [USE_THEN "add" MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sub s (ring_add s x y) (ring_add s m m') =
        ring_add s (ring_sub s x m) (ring_sub s y (m':B))") SUBST1_TAC THENL [MATCH_MP_TAC r5 THEN ASM_MESON_TAC [SUBSET], ASM_SIMP_TAC [IN_RING_IDEAL_ADD]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x. x IN S ==> ring_neg s x IN (S:B->bool)") ASSUME_TAC THENL [EXPAND_TAC "S" THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"m:B") STRIP_ASSUME_TAC)) THEN ASM_SIMP_TAC [RING_NEG] THEN EXISTS_TAC (← q r"ring_neg s m:B") THEN CONJ_TAC THENL [USE_THEN "neg" MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sub s (ring_neg s x) (ring_neg s m) =
        ring_neg s (ring_sub s x (m:B))") SUBST1_TAC THENL [MATCH_MP_TAC r4 THEN ASM_MESON_TAC [SUBSET], ASM_SIMP_TAC [IN_RING_IDEAL_NEG]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x. x IN ideal_generated s (IMAGE (h:A->B) j)
          ==> x IN ring_carrier s /\
              !z. z IN ring_carrier s ==> ring_mul s x z IN S") (LABEL_TAC "gen") THENL [MATCH_MP_TAC IDEAL_GENERATED_INDUCT THEN REPEAT CONJ_TAC THENL [X_GEN_TAC (← q r"y:B") THEN REWRITE_TAC [IN_IMAGE] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"a:A") (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier r") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"z:B") THEN DISCH_TAC THEN USE_THEN "ih" (MP_TAC o (← do let c := (← ASSUME (← q r"(z:B) IN ring_carrier s")); pure (fun th => MATCH_MP th c))) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"m:B") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(m:B) IN ring_carrier s") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN EXPAND_TAC "S" THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_SIMP_TAC [RING_MUL] THEN EXISTS_TAC (← q r"ring_mul s ((h:A->B) a) m") THEN CONJ_TAC THENL [USE_THEN "smul" MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sub s (ring_mul s ((h:A->B) a) z) (ring_mul s (h a) m) =
          ring_mul s (h a) (ring_sub s z m)") SUBST1_TAC THENL [MATCH_MP_TAC r3 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN EXPAND_TAC "E" THEN REWRITE_TAC [IDEAL_POW_SUC] THEN wPart rand (lhand o rand) IDEAL_PROD_HOMOMORPHIC_IMAGE THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_POW] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_PROD THEN ASM_SIMP_TAC [RING_SUB] THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN ASM_SIMP_TAC [FUN_IN_IMAGE] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, SUBSET], REWRITE_TAC [RING_0], ASM_SIMP_TAC [RING_MUL_LZERO], SIMP_TAC [RING_NEG, RING_MUL_LNEG] THEN ASM_MESON_TAC [], SIMP_TAC [RING_ADD, RING_ADD_RDISTRIB] THEN ASM_MESON_TAC [], SIMP_TAC [RING_MUL] THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_mul s (ring_mul s x y) z =
                      ring_mul s y (ring_mul s x (z:B))") SUBST1_TAC THENL [MATCH_MP_TAC r2 THEN ASM_REWRITE_TAC [], ASM_SIMP_TAC [RING_MUL]]], ALL_TAC] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN USE_THEN "one" (MP_TAC o (← do let c := (← ASSUME (← q r"(x:B) IN ring_carrier s")); pure (fun th => MATCH_MP th c))) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"m:B") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(m:B) IN ring_carrier s") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sub s x (m:B) IN S") ASSUME_TAC THENL [USE_THEN "gen" (MP_TAC o (← do let c := (← ASSUME (← q r"ring_sub s x (m:B) IN ideal_generated s (IMAGE (h:A->B) j)")); pure (fun th => MATCH_MP th c))) THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"ring_1 s:B")) o CONJUNCT2)) THEN REWRITE_TAC [RING_1] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC RING_MUL_RID THEN ASM_SIMP_TAC [RING_SUB], ALL_TAC] THEN SUBGOAL_THEN (← q r"(m:B) IN S") ASSUME_TAC THENL [EXPAND_TAC "S" THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"m:B") THEN ASM_SIMP_TAC [RING_SUB_REFL, IN_RING_IDEAL_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"x:B = ring_add s m (ring_sub s x m)") SUBST1_TAC THENL [MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC [], ASM_SIMP_TAC []])

  let IDEAL_PRODUCT_COMAXIMAL ← prove
    r"!r s (f:K->A->bool).
        FINITE s /\ (!i. i IN s ==> ring_ideal r (f i)) /\
        pairwise (\i i'. ring_setadd r (f i) (f i') = ring_carrier r) s
        ==> ideal_product r s f = ring_carrier r INTER INTERS {f i | i IN s}"
    (GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC [IDEAL_PRODUCT_EMPTY, SIMPLE_IMAGE, IMAGE_CLAUSES, INTERS_0, INTER_UNIV] THEN MAP_EVERY X_GEN_TAC [(← q r"a:K"), (← q r"s:K->bool")] THEN STRIP_TAC THEN X_GEN_TAC (← q r"f:K->A->bool") THEN REWRITE_TAC [FORALL_IN_INSERT, PAIRWISE_INSERT] THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:K->bool"), (← q r"f:K->A->bool"), (← q r"a:K")] IDEAL_PRODUCT_INSERT) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN wPart lhand (lhand o rand) IDEAL_PROD_COMAXIMAL THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_IDEAL_IDEAL_PRODUCT] THEN MATCH_MP_TAC COMAXIMAL_IDEAL_PRODUCT THEN ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"f:K->A->bool"))) THEN ASM_REWRITE_TAC [SIMPLE_IMAGE] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [INTERS_INSERT] THEN SET_TAC [])

  let CHINESE_REMAINDER_PRODUCT_RING ← prove
    r"!r s (j:K->A->bool).
        FINITE s /\ (!i. i IN s ==> ring_ideal r (j i)) /\
        pairwise (\i i'. ring_setadd r (j i) (j i') = ring_carrier r) s
        ==> quotient_ring r (ring_carrier r INTER INTERS {j i | i IN s})
            isomorphic_ring product_ring s (\i. quotient_ring r (j i))"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_kernel (r,product_ring s (\i. quotient_ring r ((j:K->A->bool) i)))
                (\x:A. RESTRICTION s (\i. ring_coset r (j i) x)) =
    ring_carrier r INTER INTERS {j i | i IN s}") (SUBST1_TAC o SYM) THENL [REWRITE_TAC [ring_kernel, PRODUCT_RING, RESTRICTION_EXTENSION] THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM, IN_INTER, INTERS_GSPEC] THEN X_GEN_TAC (← q r"x:A") THEN ASM_CASES_TAC (← q r"(x:A) IN ring_carrier r") THEN ASM_SIMP_TAC [QUOTIENT_RING_0, RING_COSET_EQ_IDEAL], MATCH_MP_TAC FIRST_RING_EPIMORPHISM_THEOREM] THEN REWRITE_TAC [ring_epimorphism, RING_HOMOMORPHISM_COMPONENTWISE] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, RESTRICTION_IN_EXTENSIONAL] THEN ASM_SIMP_TAC [RESTRICTION, ETA_AX, RING_HOMOMORPHISM_RING_COSET] THEN REWRITE_TAC [(← GSYM SUBSET_ANTISYM_EQ), SUBSET, FORALL_IN_IMAGE] THEN ASM_SIMP_TAC [PRODUCT_RING, RESTRICTION_IN_CARTESIAN_PRODUCT, IN_CARTESIAN_PRODUCT, QUOTIENT_RING_CARRIER] THEN CONJ_TAC THENL [SET_TAC [], X_GEN_TAC (← q r"y:K->A->bool")] THEN REWRITE_TAC [IN_ELIM_THM, RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC (← q r"a:K->A"))) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:K->bool"), (← q r"j:K->A->bool"), (← q r"a:K->A")] CHINESE_REMAINDER_IDEALS) THEN ASM_SIMP_TAC [IN_IMAGE] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"x:A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONV_TAC SYM_CONV THEN REWRITE_TAC [RESTRICTION_UNIQUE] THEN ASM_SIMP_TAC [RING_COSET_EQ])

  let NOETHERIAN_RING_INDUCT ← prove
    r"!r (P:(A->bool)->bool).
        noetherian_ring r /\
        (!j. ring_ideal r j /\ (!k. ring_ideal r k /\ j PSUBSET k ==> P k)
             ==> P j)
        ==> !j. ring_ideal r j ==> P j"
    (REPEAT GEN_TAC THEN REWRITE_TAC [NOETHERIAN_RING, WF_IND] THEN DISCH_THEN (CONJUNCTS_THEN2 (MP_TAC o (SPEC (← q r"\j:A->bool. ring_ideal r j ==> P j"))) ASSUME_TAC) THEN REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC [])

  let NOETHERIAN_PRIME_PRODUCT_SUBSET ← prove
    r"!r j:A->bool.
        noetherian_ring r /\ ring_ideal r j
        ==> ?e. monomial {p | prime_ideal r p /\ j SUBSET p} e /\
                ideal_product r (monomial_vars e) (\p. ideal_pow r p (e p))
                SUBSET j"
    (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC NOETHERIAN_RING_INDUCT THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"j:A->bool") THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"j = ring_carrier (r:A ring)") THENL [EXISTS_TAC (← q r"monomial_1:(A->bool)->num") THEN ASM_REWRITE_TAC [MONOMIAL_1, MONOMIAL_VARS_1, IDEAL_PRODUCT_EMPTY, SUBSET_REFL], ALL_TAC] THEN ASM_CASES_TAC (← q r"prime_ideal r (j:A->bool)") THENL [EXISTS_TAC (← q r"monomial_var (j:A->bool)") THEN ASM_REWRITE_TAC [MONOMIAL_VAR, MONOMIAL_VARS_VAR, IN_ELIM_THM, SUBSET_REFL] THEN ASM_SIMP_TAC [IDEAL_PRODUCT_SING, monomial_var, IDEAL_POW_1, RING_IDEAL_IDEAL_POW, SUBSET_REFL], ALL_TAC] THEN SUBGOAL_THEN (← q r"?a b:A. a IN ring_carrier r /\ b IN ring_carrier r /\
            ring_mul r a b IN j /\ ~(a IN j) /\ ~(b IN j)") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"~prime_ideal r (j:A->bool)") THEN ASM_REWRITE_TAC [prime_ideal, PROPER_IDEAL_ALT] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!c:A. c IN ring_carrier r /\ ~(c IN j)
          ==> ?e. monomial {p | prime_ideal r p /\ j SUBSET p} e /\
                  ideal_product r (monomial_vars e) (\p. ideal_pow r p (e p))
                  SUBSET ideal_generated r (c INSERT j)") MP_TAC THENL [REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"(c:A) INSERT j SUBSET ring_carrier r") ASSUME_TAC THENL [ASM_SIMP_TAC [INSERT_SUBSET, RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"(j:A->bool) SUBSET ideal_generated r (c INSERT j)") ASSUME_TAC THENL [TRANS_TAC SUBSET_TRANS (← q r"(c:A) INSERT j") THEN ASM_SIMP_TAC [IDEAL_GENERATED_SUBSET_CARRIER_SUBSET] THEN SET_TAC [], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"ideal_generated r ((c:A) INSERT j)"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, PSUBSET_ALT] THEN EXISTS_TAC (← q r"c:A") THEN ASM_SIMP_TAC [IDEAL_GENERATED_INC_GEN, IN_INSERT], MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"e:(A->bool)->num") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MATCH_MP_TAC o (MATCH_MP (← REWRITE_RULE [IMP_CONJ] MONOMIAL_MONO))) THEN ASM SET_TAC []], ALL_TAC] THEN DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"b:A") th) THEN MP_TAC (← SPEC (← q r"a:A") th))) THEN ASM_REWRITE_TAC [monomial] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"e1:(A->bool)->num") STRIP_ASSUME_TAC) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"e2:(A->bool)->num") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"monomial_mul e1 e2:(A->bool)->num") THEN ASM_REWRITE_TAC [MONOMIAL_VARS_MUL, FINITE_UNION, UNION_SUBSET] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"e1:(A->bool)->num"), (← q r"e2:(A->bool)->num")] IDEAL_PRODUCT_MONOMIAL_MUL) THEN REWRITE_TAC [MONOMIAL_VARS_MUL] THEN ANTS_TAC THENL [RULE_ASSUM_TAC (REWRITE_RULE [SUBSET, IN_ELIM_THM]) THEN ASM_MESON_TAC [IN_UNION, PRIME_IMP_RING_IDEAL], DISCH_THEN SUBST1_TAC] THEN TRANS_TAC SUBSET_TRANS (← q r"ideal_prod r (ideal_generated r (a INSERT j))
                 (ideal_generated r ((b:A) INSERT j))") THEN ASM_SIMP_TAC [IDEAL_PROD_MONO, IDEAL_PROD_IDEAL_GENERATED, INSERT_SUBSET, RING_IDEAL_IMP_SUBSET] THEN MATCH_MP_TAC IDEAL_PROD_MINIMAL THEN ASM_REWRITE_TAC [IN_INSERT] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [IN_RING_IDEAL_LMUL, IN_RING_IDEAL_RMUL, IN_RING_IDEAL_MUL])

  let PRIME_AVOIDANCE ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"(x:K->A) q IN ring_carrier r"
    let q2 ← q r"t = (q:K) INSERT (t DELETE q)"
    let p3 ← prove r"!r t (x:K->A) q i.
        FINITE t /\ q IN t /\ ring_ideal r i /\ x q IN i
        ==> ring_product r t x IN i" (REPEAT STRIP_TAC THEN SUBGOAL_THEN q2 SUBST1_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN q1 ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [RING_PRODUCT_CLAUSES, FINITE_DELETE, IN_DELETE, IN_RING_IDEAL_RMUL, RING_PRODUCT])
    let lemma1 := p3
    let q4 ← q r"!u v:A. u IN ring_carrier r /\ v IN ring_carrier r
                ==> v = ring_sub r (ring_add r u v) u"
    let r5 ← RING_RULE q4
    let q6 ← q r"v = ring_sub r (ring_add r u v) (u:A)"
    let q7 ← q r"(u:A) IN ring_carrier r"
    let p8 ← prove r"!r i u v:A.
        ring_ideal r i /\ u IN i /\ v IN ring_carrier r
        ==> (ring_add r u v IN i <=> v IN i) /\
            (ring_add r v u IN i <=> v IN i)" (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN q7 ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [RING_ADD_SYM] THEN EQ_TAC THEN ASM_SIMP_TAC [IN_RING_IDEAL_ADD] THEN DISCH_TAC THEN SUBGOAL_THEN q6 SUBST1_TAC THENL [MATCH_MP_TAC r5 THEN ASM_REWRITE_TAC [], ASM_SIMP_TAC [IN_RING_IDEAL_SUB]])
    let lemma2 := p8
    let q9 ← q r"q:A->bool"
    let q10 ← q r"ring_product r (s DELETE p1) (x:(A->bool)->A) IN q"
    let q11 ← q r"s DELETE (p1:A->bool)"
    let q12 ← q r"x:(A->bool)->A"
    let q13 ← q r"\z:A. ~(z IN p1)"
    let q14 ← q r"r:A ring"
    let v15 ← ISPECL [q14, q13, q12, q11] RING_PRODUCT_CLOSED
    let q16 ← q r"q:A->bool = p1"
    let q17 ← q r"q:A->bool"
    let q18 ← q r"p2:A->bool"
    let q19 ← q r"(y:A) IN j /\ !q. q IN s ==> ~(y IN q)"
    let q20 ← q r"y = ring_add r ((x:(A->bool)->A) p1) (ring_product r (s DELETE p1) x)"
    let q21 ← q r"!p:A->bool. p IN s ==> (x:(A->bool)->A) p IN ring_carrier r"
    let q22 ← q r"x:(A->bool)->A"
    let q23 ← q r"x:A"
    let q24 ← q r"~q /\ (~p ==> r) ==> (p ==> q) ==> r"
    let r25 ← TAUT q24
    let q26 ← q r"n - 1 < n <=> ~(n = 0)"
    let r27 ← ARITH_RULE q26
    let q28 ← q r"s DELETE (p:A->bool)"
    let q29 ← q r"p:A->bool"
    let q30 ← q r"!p. p IN s ==> ?x:A. x IN j /\ x IN p /\
                         !q. q IN s /\ ~(q = p) ==> ~(x IN q)"
    let q31 ← q r"j:A->bool"
    let q32 ← q r"r:A ring"
    let v33 ← ISPECL [q32, q31] IN_RING_IDEAL_0
    let q34 ← q r"?p1 p2:A->bool. p1 IN s /\ p2 IN s /\ ~(p2 = p1)"
    let q35 ← q r"~(p /\ q) <=> p ==> ~q"
    let r36 ← TAUT q35
    let q37 ← q r"(~p ==> F) ==> p"
    let r38 ← TAUT q37
    let q39 ← q r"CARD(s:(A->bool)->bool)"
    prove
      r"!r (j:A->bool) s.
          ring_ideal r j /\ FINITE s /\ (!p. p IN s ==> prime_ideal r p) /\
          j SUBSET UNIONS s
          ==> ?p. p IN s /\ j SUBSET p"
      (REPLICATE_TAC 3 GEN_TAC THEN WF_INDUCT_TAC q39 THEN STRIP_TAC THEN MATCH_MP_TAC r38 THEN DISCH_THEN (ASSUME_TAC o (REWRITE_RULE [NOT_EXISTS_THM, r36])) THEN SUBGOAL_THEN q34 STRIP_ASSUME_TAC THENL [MP_TAC v33 THEN ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN q30 MP_TAC THENL [X_GEN_TAC q29 THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC q28)) THEN ASM_SIMP_TAC [CARD_DELETE, FINITE_DELETE, IN_DELETE, CARD_EQ_0, r27] THEN ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN MATCH_MP_TAC r25 THEN CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN REWRITE_TAC [SUBSET, NOT_FORALL_THM, NOT_IMP, IN_UNIONS, IN_DELETE] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC q23 THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN RULE_ASSUM_TAC (REWRITE_RULE [SUBSET, IN_UNIONS]) THEN ASM_MESON_TAC [], REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN DISCH_THEN (X_CHOOSE_TAC q22)] THEN SUBGOAL_THEN q21 ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN ABBREV_TAC q20 THEN SUBGOAL_THEN q19 MP_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN EXPAND_TAC "y" THEN CONJ_TAC THENL [MATCH_MP_TAC IN_RING_IDEAL_ADD THEN ASM_SIMP_TAC [] THEN MATCH_MP_TAC lemma1 THEN EXISTS_TAC q18 THEN ASM_SIMP_TAC [FINITE_DELETE, IN_DELETE], X_GEN_TAC q17 THEN DISCH_TAC THEN ASM_CASES_TAC q16 THENL [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC [lemma2, PRIME_IMP_RING_IDEAL, RING_PRODUCT] THEN MP_TAC v15 THEN REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_1_NOT_IN_PRIME_IDEAL, RING_MUL_IN_PRIME_IDEAL, IN_DELETE], SUBGOAL_THEN q10 ASSUME_TAC THENL [MATCH_MP_TAC lemma1 THEN EXISTS_TAC q9 THEN ASM_SIMP_TAC [FINITE_DELETE, IN_DELETE, PRIME_IMP_RING_IDEAL], ASM_SIMP_TAC [lemma2, PRIME_IMP_RING_IDEAL]]]])

  let IDEAL_PROD_IDEAL_GENERATED_FINITE ← prove
    r"!r i t:A->bool.
        ring_ideal r i /\ FINITE t /\ t SUBSET ring_carrier r
        ==> ideal_prod r i (ideal_generated r t) =
            {ring_sum r t (\x. ring_mul r (c x) x) | c |
             !x. x IN t ==> c x IN i}"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"(!x:A. x IN i ==> x IN ring_carrier r) /\
                (!x:A. x IN t ==> x IN ring_carrier r)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_PROD_MINIMAL, REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_RING_IDEAL_SUM THEN REWRITE_TAC [RING_IDEAL_IDEAL_PROD] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_PROD THEN ASM_SIMP_TAC [IDEAL_GENERATED_INC]] THEN SUBGOAL_THEN (← q r"{ring_sum r t (\x. ring_mul r (c x) x) | c | !x:A. x IN t ==> c x IN i} =
    {ring_sum r t (\x. ring_mul r (c x) x) | c |
     !x. x IN t ==> c x IN i /\ c x IN ring_carrier r}") SUBST1_TAC THENL [REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [IDEAL_GENERATED_FINITE] THEN REWRITE_TAC [ring_ideal, SUBSET, IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_GSPEC, RING_SUM] THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL [EXISTS_TAC (← q r"\x:A. ring_0 r:A"), X_GEN_TAC (← q r"c:A->A") THEN DISCH_TAC THEN EXISTS_TAC (← q r"\x:A. ring_neg r ((c:A->A) x)"), X_GEN_TAC (← q r"c:A->A") THEN DISCH_TAC THEN X_GEN_TAC (← q r"d:A->A") THEN DISCH_TAC THEN EXISTS_TAC (← q r"\x:A. ring_add r ((c:A->A) x) (d x)"), X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN X_GEN_TAC (← q r"c:A->A") THEN DISCH_TAC THEN EXISTS_TAC (← q r"\x:A. ring_mul r a ((c:A->A) x)"), X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN X_GEN_TAC (← q r"c:A->A") THEN DISCH_TAC THEN EXISTS_TAC (← q r"\x:A. ring_mul r a ((c:A->A) x)")] THEN ASM_SIMP_TAC [IN_RING_IDEAL_0, IN_RING_IDEAL_NEG, IN_RING_IDEAL_ADD, IN_RING_IDEAL_LMUL, IN_RING_IDEAL_RMUL, RING_0, RING_NEG, RING_ADD, RING_MUL] THEN ASM_SIMP_TAC [RING_MUL_LZERO, RING_SUM_0, RING_MUL_LNEG, RING_ADD_RDISTRIB, (← GSYM RING_MUL_ASSOC), RING_SUM_NEG, RING_SUM_ADD, RING_SUM_LMUL, RING_MUL])

  let NAKAYAMA_LEMMA ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (q ==> r) ==> (p ==> q) ==> r")
    let r2 ← RING_RULE (← q r"x IN ring_carrier r /\ y IN ring_carrier r
        ==> ring_sub r (ring_sub r x y) x = ring_neg r (y:A)")
    let r3 ← RING_RULE (← q r"y IN ring_carrier r /\ s IN ring_carrier r
      ==> ring_sub r (ring_add r y s) s = (y:A)")
    prove
      r"!r i j k:A->bool.
          ring_ideal r i /\ ring_ideal r k /\ finitely_generated_ideal r j /\
          j SUBSET ring_setadd r k (ideal_prod r i j)
          ==> ?a. a IN ring_carrier r /\ ring_sub r (ring_1 r) a IN i /\
                  !x. x IN j ==> ring_mul r a x IN k"
      (REPEAT GEN_TAC THEN REWRITE_TAC [finitely_generated_ideal] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"t:A->bool") STRIP_ASSUME_TAC) MP_TAC))) THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN SUBGOAL_THEN (← q r"!x:A. x IN t ==> x IN ring_carrier r") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [IDEAL_PROD_IDEAL_GENERATED_FINITE, SUBSET, ring_setadd, IN_ELIM_THM] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"!g:A. ?c. g IN t
                ==> (!h. h IN t ==> c h IN i /\ c h IN ring_carrier r) /\
                    ring_sub r g (ring_sum r t (\h. ring_mul r (c h) h)) IN k") MP_TAC THENL [X_GEN_TAC (← q r"g:A") THEN REWRITE_TAC [RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"g:A"))) THEN ASM_SIMP_TAC [IDEAL_GENERATED_INC_GEN] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM, LEFT_AND_EXISTS_THM, RIGHT_AND_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"y:A"), (← q r"s:A"), (← q r"c:A->A")] THEN STRIP_TAC THEN EXISTS_TAC (← q r"c:A->A") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(y:A) IN ring_carrier r /\ !h. h IN t ==> (c:A->A) h IN ring_carrier r") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [RING_SUM, r3], REWRITE_TAC [SKOLEM_THM] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"b:A->A->A"))] THEN ABBREV_TAC (← q r"M = \g h:A. ring_sub r (if g = h then ring_1 r else ring_0 r)
                            ((b:A->A->A) g h)") THEN SUBGOAL_THEN (← q r"!g h:A. g IN t /\ h IN t ==> (M:A->A->A) g h IN ring_carrier r") ASSUME_TAC THENL [EXPAND_TAC "M" THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_SUB THEN ASM_SIMP_TAC [] THEN COND_CASES_TAC THEN REWRITE_TAC [RING_0, RING_1], ALL_TAC] THEN EXISTS_TAC (← q r"ring_det r t (M:A->A->A)") THEN REWRITE_TAC [RING_DET] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"quotient_ring r (i:A->bool)"), (← q r"ring_coset r (i:A->bool)"), (← q r"t:A->bool"), (← q r"M:A->A->A")] RING_DET_HOMOMORPHISM) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_COSET] THEN SUBGOAL_THEN (← q r"ring_det (quotient_ring r i) t (\g h. ring_coset r i ((M:A->A->A) g h)) =
        ring_det (quotient_ring r i) t
          (\g h. if g = h then ring_1 (quotient_ring r i)
                 else ring_0 (quotient_ring r i))") SUBST1_TAC THENL [MATCH_MP_TAC RING_DET_EQ THEN MAP_EVERY X_GEN_TAC [(← q r"g:A"), (← q r"h:A")] THEN STRIP_TAC THEN EXPAND_TAC "M" THEN COND_CASES_TAC THEN ASM_SIMP_TAC [QUOTIENT_RING_1, QUOTIENT_RING_0, RING_COSET_EQ, RING_COSET_EQ_IDEAL, RING_SUB, RING_0, RING_1, RING_NEG, RING_SUB_LZERO, IN_RING_IDEAL_NEG, r2], ASM_SIMP_TAC [RING_DET_I, QUOTIENT_RING_1] THEN DISCH_THEN (MP_TAC o SYM) THEN ASM_SIMP_TAC [RING_COSET_EQ, RING_1, RING_DET]], MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"{x:A | x IN ring_carrier r /\
                ring_mul r (ring_det r t (M:A->A->A)) x IN k}"), (← q r"t:A->bool")] IDEAL_GENERATED_MINIMAL) THEN ASM_SIMP_TAC [RING_IDEAL_QUOTIENT_LMUL, RING_DET] THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [ALL_TAC, SET_TAC []] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC (← q r"l:A") THEN DISCH_TAC THEN ASM_SIMP_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:A->bool"), (← q r"t:A->bool"), (← q r"M:A->A->A"), (← q r"\h:A. h"), (← q r"l:A")] RING_DET_DEPENDENT_COLUMNS_MUL_IDEAL) THEN ASM_SIMP_TAC [RING_DET, RING_MUL_SYM] THEN DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC (← q r"g:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_sum r t (\h. ring_mul r ((M:A->A->A) g h) h) =
        ring_sub r (ring_sum r t (\h. if h = g then g else ring_0 r))
                   (ring_sum r t (\h. ring_mul r (b g h) h))") SUBST1_TAC THENL [wPart rand (rand o rand) RING_SUM_SUB THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_MUL] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [RING_0], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"h:A") THEN DISCH_TAC THEN EXPAND_TAC "M" THEN ASM_CASES_TAC (← q r"h:A = g") THEN ASM_SIMP_TAC [RING_SUB_RDISTRIB, RING_MUL_LID, RING_MUL_LZERO, RING_0, RING_1], ASM_SIMP_TAC [RING_SUM_DELTA]]])

  let NAKAYAMA_LEMMA_MAXIMAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"a IN ring_carrier r /\ v IN ring_carrier r /\ x IN ring_carrier r /\
      ring_mul r a v = ring_1 r
      ==> x = ring_mul r v (ring_mul r a (x:A))")
    let r2 ← RING_RULE (← q r"a IN ring_carrier r
        ==> ring_1 r = ring_add r (ring_sub r (ring_1 r) a) (a:A)")
    let r3 ← TAUT (← q r"(~p ==> F) ==> p")
    prove
      r"!r i j k:A->bool.
          (!m. maximal_ideal r m ==> i SUBSET m) /\ ring_ideal r k /\
          finitely_generated_ideal r j /\
          j SUBSET ring_setadd r k (ideal_prod r i j)
          ==> j SUBSET k"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITELY_GENERATED_IMP_RING_IDEAL)) THEN ASM_CASES_TAC (← q r"trivial_ring(r:A ring)") THENL [RULE_ASSUM_TAC (REWRITE_RULE [trivial_ring]) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool")] RING_IDEAL_IMP_SUBSET) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:A->bool")] IN_RING_IDEAL_0) THEN ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(i:A->bool) SUBSET ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [MAXIMAL_IDEAL_EXISTS, MAXIMAL_IDEAL_IMP_SUBSET, SUBSET_TRANS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_generated r (i:A->bool)"), (← q r"j:A->bool"), (← q r"k:A->bool")] NAKAYAMA_LEMMA) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"i:A->bool"), (← q r"j:A->bool")] IDEAL_PROD_IDEAL_GENERATED) THEN ASM_SIMP_TAC [IDEAL_GENERATED_RING_IDEAL, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_GENERATED] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:A") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"ring_unit r (a:A)") MP_TAC THENL [MATCH_MP_TAC r3 THEN DISCH_TAC THEN MP_TAC (← ISPEC (← q r"r:A ring") UNIONS_MAXIMAL_IDEALS) THEN REWRITE_TAC [EXTENSION, IN_UNIONS, IN_ELIM_THM] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"a:A"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"m:A->bool") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"ideal_generated r i SUBSET (m:A->bool)") ASSUME_TAC THENL [ASM_MESON_TAC [IDEAL_GENERATED_MINIMAL, MAXIMAL_IMP_RING_IDEAL], ALL_TAC] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP MAXIMAL_IMP_PROPER_IDEAL)) THEN REWRITE_TAC [PROPER_IDEAL] THEN STRIP_TAC THEN UNDISCH_TAC (← q r"~(ring_1 r IN (m:A->bool))") THEN REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ring_1 r = ring_add r (ring_sub r (ring_1 r) a) (a:A)") SUBST1_TAC THENL [MATCH_MP_TAC r2 THEN ASM_REWRITE_TAC [], MATCH_MP_TAC IN_RING_IDEAL_ADD THEN ASM SET_TAC []], REWRITE_TAC [ring_unit] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"v:A") STRIP_ASSUME_TAC) o CONJUNCT2)] THEN REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"x = ring_mul r v (ring_mul r a (x:A))") SUBST1_TAC THENL [MATCH_MP_TAC r1 THEN ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ASM_SIMP_TAC [IN_RING_IDEAL_LMUL]])

  let NAKAYAMA_LEMMA_LOCAL ← prove
    r"!r i j k:A->bool.
        local_ring r /\ proper_ideal r i /\ ring_ideal r k /\
        finitely_generated_ideal r j /\
        j SUBSET ring_setadd r k (ideal_prod r i j)
        ==> j SUBSET k"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC NAKAYAMA_LEMMA_MAXIMAL THEN MAP_EVERY EXISTS_TAC [(← q r"r:A ring"), (← q r"i:A->bool")] THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MP_TAC o (MATCH_MP MAXIMAL_SUPERIDEAL_EXISTS)) THEN FIRST_X_ASSUM (MP_TAC o (GEN_REWRITE_RULE id [local_ring])) THEN REWRITE_TAC [EXISTS_UNIQUE_DEF] THEN MESON_TAC [])

  -- @@RETURN BEGIN
  return { RING_ISOMORPHISM_IDEAL_POW, IDEAL_PRODUCT_HOMOMORPHIC_IMAGE,
           IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0, IDEAL_EXTENSION_POW_SUPPLEMENT,
           IDEAL_PRODUCT_COMAXIMAL, CHINESE_REMAINDER_PRODUCT_RING,
           NOETHERIAN_RING_INDUCT, NOETHERIAN_PRIME_PRODUCT_SUBSET, PRIME_AVOIDANCE,
           IDEAL_PROD_IDEAL_GENERATED_FINITE, NAKAYAMA_LEMMA, NAKAYAMA_LEMMA_MAXIMAL,
           NAKAYAMA_LEMMA_LOCAL }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- ideal_arith.ml phrases from line 2339 to 2446                          -/
/- ---------------------------------------------------------------------- -/

structure IdealArith04 where
  -- @@FIELDS
  LOCAL_RING_GENERATORS_EXCHANGE : thm
  FINITELY_GENERATED_IDEAL_IDEMPOTENT : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupIdealArith04 [HolBase] (D : IdealArithDeps) (BIdealArith01 : IdealArith01) (BIdealArith03 : IdealArith03) :
    ExceptT String IO IdealArith04 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON, MESON_TAC, RING_RULE, SET_TAC, .. } := D
  let { EQ_TRANS, EXTENSION, FINITELY_GENERATED_IMP_RING_IDEAL, FINITE_DELETE,
        IDEAL_GENERATED_FINITE, IDEAL_GENERATED_INC, IDEAL_GENERATED_INC_GEN,
        IDEAL_GENERATED_MINIMAL, INSERT_DELETE, IN_DELETE, IN_ELIM_THM,
        IN_RING_IDEAL_0, IN_RING_IDEAL_ADD, IN_RING_IDEAL_LMUL, IN_RING_IDEAL_SUB,
        IN_SING, JACOBSON_RADICAL_LOCAL_RING, LOCAL_RING_JACOBSON_RADICAL,
        MAXIMAL_IMP_RING_IDEAL, PRINCIPAL_IDEAL_IDEAL_GENERATED_SING,
        PRINCIPAL_IMP_FINITELY_GENERATED_IDEAL, RING_1, .. } := D.core1
  let { RING_IDEAL_0, RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IMP_SUBSET, RING_INV,
        RING_MUL, RING_MUL_LID, RING_MUL_LINV, RING_SETADD_LZERO, RING_SUB, RING_SUM,
        RING_SUM_CLAUSES, RING_SUM_CLOSED, SING_SUBSET, SUBSET, SUBSET_ANTISYM,
        SUBSET_REFL, SUBSET_TRANS, .. } := D.core2
  let { IDEAL_PROD_PRINCIPAL, RING_IDEAL_IDEAL_PROD, RING_MUL_IN_IDEAL_PROD, .. } := BIdealArith01
  let { NAKAYAMA_LEMMA, .. } := BIdealArith03
  -- @@SCOPE END

  let LOCAL_RING_GENERATORS_EXCHANGE ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"i:A = y"
    let q2 ← q r"i:A"
    let q6 ← q r"ring_mul r (ring_mul r (ring_inv r ((c:A->A) y)) (c y)) (y:A)"
    let q17 ← q r"y = ring_mul r (ring_inv r ((c:A->A) y)) (ring_sub r x q)"
    let q18 ← q r"ring_inv r ((c:A->A) y) IN ring_carrier r"
    let q19 ← q r"(c:A->A) y"
    let q20 ← q r"r:A ring"
    let v21 ← ISPECL [q20, q19] RING_MUL_LINV
    let q22 ← q r"(y:A) IN K"
    let q23 ← q r"(y:A) IN s"
    let v24 ← ASSUME q23
    let q25 ← q r"s:A->bool"
    let q26 ← q r"y:A"
    let v27 ← ISPECL [q26, q25] INSERT_DELETE
    let q35 ← q r"ring_add r (ring_mul r ((c:A->A) y) y) q = x"
    let q36 ← q r"\a:A. a IN K"
    let q37 ← q r"r:A ring"
    let v38 ← ISPECL [q37, q36] RING_SUM_CLOSED
    let v39 ← REWRITE_RULE [] v38
    let q40 ← q r"(q:A) IN ring_carrier r /\ q IN K"
    let q41 ← q r"q = ring_sum r (s DELETE y) (\i. ring_mul r ((c:A->A) i) i)"
    let q42 ← q r"ring_ideal r (K:A->bool) /\ (x:A) IN K /\ (!i. i IN s DELETE y ==> i IN K)"
    let q43 ← q r"K = ideal_generated r ((x:A) INSERT (s DELETE y))"
    let q44 ← q r"y:A"
    let q45 ← q r"(c:A->A) y"
    let q46 ← q r"m:A->bool"
    let q47 ← q r"r:A ring"
    let v48 ← ISPECL [q47, q46] LOCAL_RING_JACOBSON_RADICAL
    let q49 ← q r"ring_unit r ((c:A->A) y)"
    let q50 ← q r"(y:A) IN ring_carrier r /\ (c:A->A) y IN ring_carrier r"
    let q51 ← q r"i:A"
    let q52 ← q r"\a:A. a IN ideal_prod r m m"
    let q53 ← q r"r:A ring"
    let v54 ← ISPECL [q53, q52] RING_SUM_CLOSED
    let v55 ← REWRITE_RULE [] v54
    let q60 ← q r"~((x:A) IN ideal_prod r m m)"
    let q61 ← q r"~(!y:A. y IN s ==> (c:A->A) y IN m) ==> ?y. y IN s /\ ~(c y IN m)"
    let r62 ← MESON [] q61
    let q63 ← q r"?y:A. y IN s /\ ~((c:A->A) y IN m)"
    let q64 ← q r"s:A->bool"
    let q65 ← q r"r:A ring"
    let v66 ← ISPECL [q65, q64] IDEAL_GENERATED_FINITE
    let q67 ← q r"?c. (!i. i IN s ==> (c:A->A) i IN ring_carrier r) /\
        ring_sum r s (\i. ring_mul r (c i) i) = x"
    let q68 ← q r"(x:A) IN ring_carrier r"
    let q69 ← q r"(m:A->bool) SUBSET ring_carrier r /\ s SUBSET ring_carrier r"
    prove
      r"!r m s x:A.
          local_ring r /\ maximal_ideal r m /\
          FINITE s /\ s SUBSET m /\ ideal_generated r s = m /\
          x IN m /\ ~(x IN ideal_prod r m m)
          ==> ?y. y IN s /\ ideal_generated r (x INSERT (s DELETE y)) = m"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_RING_IDEAL)) THEN SUBGOAL_THEN q69 STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET_TRANS], ALL_TAC] THEN SUBGOAL_THEN q68 ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN q67 STRIP_ASSUME_TAC THENL [MP_TAC v66 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => tactic_of do pure (UNDISCH_TAC (← q r"(x:A) IN m") THEN REWRITE_TAC [th, IN_ELIM_THM])) THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN q63 STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r62 THEN DISCH_TAC THEN UNDISCH_TAC q60 THEN REWRITE_TAC [] THEN FIRST_X_ASSUM ((fun th => tactic_of do pure (GEN_REWRITE_TAC LAND_CONV [(← SYM th)])) o (checkM (fun th => (do let z59 ← (q r"x:A"); let z58 ← (do let z56 ← (do let z57 ← (pure th); pure (concl z57)); liftExcept (rhs z56)); pure (z58 == z59))))) THEN MATCH_MP_TAC v55 THEN SIMP_TAC [IN_RING_IDEAL_0, IN_RING_IDEAL_ADD, RING_IDEAL_IDEAL_PROD] THEN X_GEN_TAC q51 THEN DISCH_TAC THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_PROD THEN ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN q50 STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN q49 ASSUME_TAC THENL [MP_TAC v48 THEN ASM_SIMP_TAC [JACOBSON_RADICAL_LOCAL_RING] THEN DISCH_THEN (MP_TAC o ((SPEC q45) o (REWRITE_RULE [EXTENSION]))) THEN ASM_SIMP_TAC [IN_ELIM_THM], ALL_TAC] THEN EXISTS_TAC q44 THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC q43 THEN SUBGOAL_THEN q42 STRIP_ASSUME_TAC THENL [EXPAND_TAC "K" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN ASM SET_TAC [], ALL_TAC] THEN ABBREV_TAC q41 THEN SUBGOAL_THEN q40 STRIP_ASSUME_TAC THENL [EXPAND_TAC "q" THEN REWRITE_TAC [RING_SUM] THEN MATCH_MP_TAC v39 THEN ASM_SIMP_TAC [IN_RING_IDEAL_0, IN_RING_IDEAL_ADD] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN ASM_SIMP_TAC [] THEN ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN q35 ASSUME_TAC THENL [FIRST_ASSUM ((fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [(← SYM th)])) o (checkM (fun th => (do if ← (do let z31 ← (q r"x:A"); let z30 ← (do let z28 ← (do let z29 ← (pure th); pure (concl z29)); liftExcept (rhs z28)); pure (z30 == z31)) then (do let z32 ← (do let z33 ← (do let z34 ← (pure th); pure (concl z34)); liftExcept (lhs z33)); pure (is_comb z32)) else pure false)))) THEN MP_TAC v27 THEN REWRITE_TAC [v24] THEN DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [(← SYM th)])) THEN EXPAND_TAC "q" THEN ASM_SIMP_TAC [RING_SUM_CLAUSES, FINITE_DELETE, IN_DELETE, RING_MUL], ALL_TAC] THEN SUBGOAL_THEN q22 ASSUME_TAC THENL [MP_TAC v21 THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN q18 ASSUME_TAC THENL [ASM_SIMP_TAC [RING_INV], ALL_TAC] THEN SUBGOAL_THEN q17 SUBST1_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do if ← (do let z10 ← (q r"x:A"); let z9 ← (do let z7 ← (do let z8 ← (pure th); pure (concl z8)); liftExcept (rhs z7)); pure (z9 == z10)) then (do let z11 ← (do let z12 ← (do let z13 ← (pure th); pure (concl z13)); liftExcept (lhs z12)); pure (is_comb z11)) else pure false) then (do let z15 ← (do let z16 ← (pure th); pure (concl z16)); let z14 ← (q r"q:A"); pure (free_in z14 z15)) else pure false))))) THEN TRANS_TAC EQ_TRANS q6 THEN CONJ_TAC THENL [ASM_SIMP_TAC [RING_MUL_LID], W (fun (_asl, w) => tactic_of do pure ((← do let th ← (do pure (← RING_RULE w)); pure (MATCH_ACCEPT_TAC th ORELSE (MATCH_MP_TAC th THEN ASM_SIMP_TAC [])))))], MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN ASM_SIMP_TAC [IN_RING_IDEAL_SUB]], ALL_TAC] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [EXPAND_TAC "K" THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM SET_TAC [], FIRST_ASSUM ((fun th => tactic_of do pure (GEN_REWRITE_TAC LAND_CONV [(← SYM th)])) o (checkM (fun th => (do let z5 ← (q r"ideal_generated r (s:A->bool) = m"); let z4 ← (do let z3 ← (pure th); pure (concl z3)); pure (z4 == z5))))) THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [SUBSET] THEN X_GEN_TAC q2 THEN DISCH_TAC THEN ASM_CASES_TAC q1 THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [IN_DELETE]])

  let FINITELY_GENERATED_IDEAL_IDEMPOTENT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"a IN ring_carrier r /\ x IN ring_carrier r /\
          ring_mul r a x = ring_0 r
          ==> x = ring_mul r x (ring_sub r (ring_1 r) (a:A))")
    let r2 ← RING_RULE (← q r"a IN ring_carrier r /\
        ring_mul r a (ring_sub r (ring_1 r) a) = ring_0 r
        ==> ring_mul r (ring_sub r (ring_1 r) a) (ring_sub r (ring_1 r) a) =
            ring_sub r (ring_1 r) (a:A)")
    prove
      r"!r j:A->bool.
          finitely_generated_ideal r j /\ ideal_prod r j j = j <=>
          ?e. e IN ring_carrier r /\ ring_mul r e e = e /\
              ideal_generated r {e} = j"
      (REPEAT GEN_TAC THEN EQ_TAC THENL [STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITELY_GENERATED_IMP_RING_IDEAL)) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"j:A->bool"), (← q r"{ring_0 r:A}")] NAKAYAMA_LEMMA) THEN ASM_SIMP_TAC [RING_IDEAL_0, RING_SETADD_LZERO, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_PROD, IN_SING, SUBSET_REFL] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:A") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"ring_sub r (ring_1 r) a:A") THEN ASM_SIMP_TAC [RING_SUB, RING_1] THEN CONJ_TAC THENL [MATCH_MP_TAC r2 THEN ASM_SIMP_TAC [], MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_SIMP_TAC [IDEAL_GENERATED_MINIMAL, SING_SUBSET] THEN REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"x = ring_mul r x (ring_sub r (ring_1 r) a:A)") SUBST1_TAC THENL [MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [], MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_INC_GEN, IN_SING, RING_SUB, RING_1]]], DISCH_THEN (X_CHOOSE_THEN (← q r"e:A") STRIP_ASSUME_TAC) THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [IDEAL_PROD_PRINCIPAL, PRINCIPAL_IMP_FINITELY_GENERATED_IDEAL, PRINCIPAL_IDEAL_IDEAL_GENERATED_SING]])

  -- @@RETURN BEGIN
  return { LOCAL_RING_GENERATORS_EXCHANGE, FINITELY_GENERATED_IDEAL_IDEMPOTENT }
  -- @@RETURN END

end HolANT.IdealArith
