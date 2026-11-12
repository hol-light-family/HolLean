/- ========================================================================= -/
/- ANT: Norms of extended ideals and the relative fundamental identity     -/
/- ========================================================================= -/
/- File: HolANT/RelativeDegree.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/relative_degree.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antrelativedegreediff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/products.ml, ANT/algmisc.ml, ANT/ideal_arith.ml, ANT/integral.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/classgroup.ml, ANT/prime_split.ml, ANT/relative_split.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.RelativeDegree fills them).

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
import HolANT.IdealArith
import HolANT.Integral
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.IdealNorm
import HolLibrary.Isum
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolANT.RingOfIntegers
import HolANT.NormIndex
import HolANT.Discriminant
import HolANT.TraceForm
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.Classgroup
import HolANT.PrimeSplit
import HolANT.RelativeSplit

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.Algmisc
open HolANT.IdealArith
open HolANT.Integral
open HolANT.Dedekind
open HolANT.DedekindStruct
open HolANT.IdealNorm
open HolANT.Zlattice
open HolANT.Numfield
open HolANT.RingOfIntegers
open HolANT.NormIndex
open HolANT.Discriminant
open HolANT.TraceForm
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.Classgroup
open HolANT.PrimeSplit
open HolANT.RelativeSplit

namespace HolANT.RelativeDegree

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (CARD_EQ_0 CARD_EQ_NSUM CARD_IMAGE_INJ CARD_NUMSEG_LT
   DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES DEDEKIND_IDEAL_SUBSET_POW_VALUATION
   DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL DEDEKIND_PRIMITIVE_MULTIPLE
   DEDEKIND_RING_OF_INTEGERS EQ_EXP EQ_IMP_LE EQ_TRANS EXP EXP_EXP EXP_NSUM
   EXP_ONE EXTENSION EXTENSION_LINCOMB_LMUL FIELD_IMP_INTEGRAL_DOMAIN
   FIELD_MUL_LINV FIELD_QUOTIENT_RING FINITE_EXTENSION_RING_MATROID
   FINITE_NUMSEG_LT FREE_BASIS_EXISTS FREE_BASIS_FIELD FREE_BASIS_HAS_SIZE
   FREE_BASIS_INDEPENDENT FREE_BASIS_INDEPENDENT_EQ FREE_BASIS_IN_CARRIER
   HAS_SIZE IDEAL_GENERATED_IMAGE_IDEAL_GENERATED IDEAL_GENERATED_MINIMAL
   IDEAL_GENERATED_SUBSET_CARRIER IDEAL_NORM_CARRIER IDEAL_NORM_GT_1
   IDEAL_NORM_IDEAL_POW IDEAL_NORM_IDEAL_PRODUCT IDEAL_NORM_POS IDEAL_POW_1
   IDEAL_POW_EQ_ZERO IDEAL_PROD_HOMOMORPHIC_IMAGE IDEAL_PROD_RZERO IMAGE_CLAUSES
   IMP_CONJ IMP_CONJ_ALT INTEGRAL_DOMAIN_MUL_EQ_0
   INTEGRAL_DOMAIN_RING_OF_INTEGERS IN_ELIM_THM IN_IDEAL_GENERATED_SELF IN_SING
   LE_ANTISYM LE_EXP LE_MULT2 LE_MULT_LCANCEL LE_MULT_RCANCEL LE_REFL
   LT_MULT_RCANCEL MATROID_DIMENSION_GE_FINITE_CARD MAXIMAL_IDEAL_IMP_PSUBSET
   MAXIMAL_IMP_PRIME_IDEAL MAXIMAL_IMP_RING_IDEAL MAXIMAL_SUPERIDEAL_EXISTS
   MEMBER_NOT_EMPTY MONO_EXISTS MONO_FORALL MULT_EQ_0 MULT_EXP MULT_SYM
   NOT_FORALL_THM NOT_IMP NPRODUCT_EQ NSUM_LE NSUM_POS_BOUND
   NUMBER_FIELD_HOMOMORPHIC_PREIMAGE NUMBER_FIELD_IDEAL_NORM_MUL_Q
   NUMBER_FIELD_IMP_FIELD NUMBER_FIELD_PRIME_FACTORIZATION
   NUMBER_FIELD_PRIME_IDEALS_ABOVE NUMBER_FIELD_TOWER_LAW
   PRIME_IDEAL_IMP_PSUBSET PRIME_IDEAL_IMP_SUBSET PRIME_IMP_RING_IDEAL PSUBSET
   QUOTIENT_RING_0 QUOTIENT_RING_CARRIER RESIDUE_DEGREE_QUOTIENT_RING
   RIGHT_EXISTS_IMP_THM RING_COSET_0 RING_COSET_EQ_IDEAL
   RING_HOMOMORPHISM_IN_CARRIER RING_HOMOMORPHISM_RING_COSET
   RING_HOMOMORPHISM_RING_OF_INT RING_HOMOMORPHISM_RING_OF_INTEGERS
   RING_HOMOMORPHISM_SUM_MUL RING_IDEAL_IDEAL_GENERATED RING_IDEAL_IDEAL_POW
   RING_IDEAL_IMP_NONEMPTY RING_IDEAL_IMP_SUBSET RING_INV
   RING_MATROID_INDEPENDENT RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_MUL
   RING_MUL_RZERO RING_OF_INTEGERS RING_OF_INTEGERS_COMMON_DENOMINATOR
   RING_OF_INTEGERS_FINITE_QUOTIENT RING_OF_INTEGERS_IDEAL_EXTENSION
   RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME RING_OF_INTEGERS_IDEAL_INTEGER
   RING_OF_INTEGERS_IDEAL_NORM_INTEGER RING_OF_INTEGERS_IDEAL_NORM_PRIME
   RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION RING_OF_INTEGERS_SUBSET
   RING_OF_INT_EQ_0_CHAR_0 RING_OF_INT_IN_RING_OF_INTEGERS RING_SPAN_SELF
   RING_SUM_EQ RING_SUM_RING_OF_INTEGERS SING_SUBSET SKOLEM_THM SUBSET
   SUBSET_REFL extension_degree ideal_norm number_field proper_ideal
   ramification_index ring_spanning : thm)
  deriving Inhabited

/-- What relative_degree.ml uses from Session besides theorems. -/
structure RelativeDegreeDeps where
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

/-- RingTheory's `wPart` (copied verbatim).  `W(MP_TAC o PART_MATCH f th o g
    o snd)`: match `th`'s part `f` against the part `g` of the goal, and
    MP_TAC the instance. -/
def wPart [HolBase] (g : term → Except String term) (f : term → Except String term)
    (th : thm) : tactic := fun gl =>
  ExceptT.run do
    let t ← liftExcept (g gl.2)
    ExceptT.mk (MP_TAC (← PART_MATCH f th t) gl)



/- ---------------------------------------------------------------------- -/
/- relative_degree.ml phrases from line 65 to 619                         -/
/- ---------------------------------------------------------------------- -/

structure RelativeDegree where
  -- @@FIELDS
  NUMBER_FIELD_INDEPENDENT_MOD_IDEAL : thm
  RING_OF_INTEGERS_QUOTIENT_FREE_BASIS_LE : thm
  RING_OF_INTEGERS_IDEAL_EXTENSION_CONTRACTION_PRIME : thm
  NUMBER_FIELD_IDEAL_NORM_EXTENSION_PRIME_LE : thm
  NUMBER_FIELD_IDEAL_NORM_EXTENSION_LE : thm
  NUMBER_FIELD_IDEAL_NORM_EXTENSION_Q : thm
  NUMBER_FIELD_FUNDAMENTAL_IDENTITY : thm
  NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS : thm
  NUMBER_FIELD_CARD_PRIME_IDEALS_ABOVE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupRelativeDegree [HolBase] (D : RelativeDegreeDeps) :
    ExceptT String IO RelativeDegree := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, RING_TAC,
        SET_TAC, TAUT, WF_INDUCT_TAC, .. } := D
  let { CARD_EQ_0, CARD_EQ_NSUM, CARD_IMAGE_INJ, CARD_NUMSEG_LT,
        DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES, DEDEKIND_IDEAL_SUBSET_POW_VALUATION,
        DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL, DEDEKIND_PRIMITIVE_MULTIPLE,
        DEDEKIND_RING_OF_INTEGERS, EQ_EXP, EQ_IMP_LE, EQ_TRANS, EXP, EXP_EXP, EXP_NSUM,
        EXP_ONE, EXTENSION, EXTENSION_LINCOMB_LMUL, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_MUL_LINV, FIELD_QUOTIENT_RING, FINITE_EXTENSION_RING_MATROID,
        FINITE_NUMSEG_LT, FREE_BASIS_EXISTS, FREE_BASIS_FIELD, FREE_BASIS_HAS_SIZE,
        FREE_BASIS_INDEPENDENT, FREE_BASIS_INDEPENDENT_EQ, FREE_BASIS_IN_CARRIER,
        HAS_SIZE, IDEAL_GENERATED_IMAGE_IDEAL_GENERATED, IDEAL_GENERATED_MINIMAL,
        IDEAL_GENERATED_SUBSET_CARRIER, IDEAL_NORM_CARRIER, IDEAL_NORM_GT_1,
        IDEAL_NORM_IDEAL_POW, IDEAL_NORM_IDEAL_PRODUCT, IDEAL_NORM_POS, IDEAL_POW_1,
        IDEAL_POW_EQ_ZERO, IDEAL_PROD_HOMOMORPHIC_IMAGE, IDEAL_PROD_RZERO,
        IMAGE_CLAUSES, IMP_CONJ, IMP_CONJ_ALT, INTEGRAL_DOMAIN_MUL_EQ_0,
        INTEGRAL_DOMAIN_RING_OF_INTEGERS, IN_ELIM_THM, IN_IDEAL_GENERATED_SELF,
        IN_SING, LE_ANTISYM, LE_EXP, LE_MULT2, LE_MULT_LCANCEL, LE_MULT_RCANCEL,
        LE_REFL, LT_MULT_RCANCEL, MATROID_DIMENSION_GE_FINITE_CARD,
        MAXIMAL_IDEAL_IMP_PSUBSET, MAXIMAL_IMP_PRIME_IDEAL, MAXIMAL_IMP_RING_IDEAL,
        MAXIMAL_SUPERIDEAL_EXISTS, MEMBER_NOT_EMPTY, MONO_EXISTS, MONO_FORALL,
        MULT_EQ_0, MULT_EXP, MULT_SYM, NOT_FORALL_THM, NOT_IMP, NPRODUCT_EQ, NSUM_LE,
        NSUM_POS_BOUND, NUMBER_FIELD_HOMOMORPHIC_PREIMAGE,
        NUMBER_FIELD_IDEAL_NORM_MUL_Q, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_PRIME_FACTORIZATION, NUMBER_FIELD_PRIME_IDEALS_ABOVE,
        NUMBER_FIELD_TOWER_LAW, PRIME_IDEAL_IMP_PSUBSET, PRIME_IDEAL_IMP_SUBSET,
        PRIME_IMP_RING_IDEAL, PSUBSET, QUOTIENT_RING_0, QUOTIENT_RING_CARRIER,
        RESIDUE_DEGREE_QUOTIENT_RING, RIGHT_EXISTS_IMP_THM, RING_COSET_0,
        RING_COSET_EQ_IDEAL, RING_HOMOMORPHISM_IN_CARRIER,
        RING_HOMOMORPHISM_RING_COSET, RING_HOMOMORPHISM_RING_OF_INT,
        RING_HOMOMORPHISM_RING_OF_INTEGERS, RING_HOMOMORPHISM_SUM_MUL,
        RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_POW, RING_IDEAL_IMP_NONEMPTY,
        RING_IDEAL_IMP_SUBSET, RING_INV, RING_MATROID_INDEPENDENT,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL, RING_MUL_RZERO, RING_OF_INTEGERS,
        RING_OF_INTEGERS_COMMON_DENOMINATOR, RING_OF_INTEGERS_FINITE_QUOTIENT,
        RING_OF_INTEGERS_IDEAL_EXTENSION, RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME,
        RING_OF_INTEGERS_IDEAL_INTEGER, RING_OF_INTEGERS_IDEAL_NORM_INTEGER,
        RING_OF_INTEGERS_IDEAL_NORM_PRIME, RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION,
        RING_OF_INTEGERS_SUBSET, RING_OF_INT_EQ_0_CHAR_0,
        RING_OF_INT_IN_RING_OF_INTEGERS, RING_SPAN_SELF, RING_SUM_EQ,
        RING_SUM_RING_OF_INTEGERS, SING_SUBSET, SKOLEM_THM, SUBSET, SUBSET_REFL,
        extension_degree, ideal_norm, number_field, proper_ideal, ramification_index,
        ring_spanning, .. } := D.core1
  -- @@SCOPE END

  let NUMBER_FIELD_INDEPENDENT_MOD_IDEAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p <=> ~ ~p")
    prove
      r"!k:A ring l:B ring h j s (w:K->B).
          number_field k /\ ring_homomorphism(k,l) h /\
          ring_ideal (ring_of_integers k) j /\
          ~(j = ring_carrier(ring_of_integers k)) /\
          FINITE s /\ (!i. i IN s ==> w i IN ring_carrier l) /\
          (!u. (!i. i IN s ==> u i IN ring_carrier(ring_of_integers k)) /\
               ring_sum l s (\i. ring_mul l (h(u i)) (w i)) = ring_0 l
               ==> !i. i IN s ==> u i IN j)
          ==> !c. (!i. i IN s ==> c i IN ring_carrier k) /\
                  ring_sum l s (\i. ring_mul l (h(c i)) (w i)) = ring_0 l
                  ==> !i. i IN s ==> c i = ring_0 k"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC (← q r"c:K->A") THEN STRIP_TAC THEN GEN_REWRITE_TAC id [r1] THEN PURE_REWRITE_TAC [NOT_FORALL_THM, NOT_IMP] THEN DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_SUBSET) THEN REWRITE_TAC [SUBSET] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"s:K->bool"), (← q r"c:K->A")] RING_OF_INTEGERS_COMMON_DENOMINATOR) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"d:A") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"j:A->bool"), (← q r"s:K->bool"), (← q r"\i. ring_mul k d ((c:K->A) i)")] DEDEKIND_PRIMITIVE_MULTIPLE) THEN ANTS_TAC THENL [ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_OF_INTEGERS] THEN UNDISCH_TAC (← q r"?i. i IN s /\ ~((c:K->A) i = ring_0 k)") THEN MATCH_MP_TAC MONO_EXISTS THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_MUL_EQ_0, FIELD_IMP_INTEGRAL_DOMAIN], DISCH_THEN (X_CHOOSE_THEN (← q r"t:A") (X_CHOOSE_THEN (← q r"e:A") (X_CHOOSE_THEN (← q r"u:K->A") (STRIP_ASSUME_TAC o (REWRITE_RULE [RING_OF_INTEGERS])))))] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"u:K->A"))) THEN ANTS_TAC THENL [CONJ_TAC THENL [ASM_SIMP_TAC [], ALL_TAC], ASM_MESON_TAC []] THEN SUBGOAL_THEN (← q r"(d:A) IN ring_carrier k /\ (t:A) IN ring_carrier k /\
      (e:A) IN ring_carrier k /\
      ring_mul k (ring_inv k e) (ring_mul k d t) IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_MUL, RING_INV], ALL_TAC] THEN TRANS_TAC EQ_TRANS (← q r"ring_sum l s (\i. ring_mul l ((h:A->B)
        (ring_mul k (ring_mul k (ring_inv k e) (ring_mul k d t)) ((c:K->A) i)))
        ((w:K->B) i))") THEN CONJ_TAC THENL [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"x:K") THEN DISCH_TAC THEN REWRITE_TAC [] THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"e:A")] FIELD_MUL_LINV) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"e:A")] RING_INV) THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"x:K"))) THEN ASM_SIMP_TAC [] THEN REPEAT STRIP_TAC THEN RING_TAC THEN ASM_SIMP_TAC [], ASM_SIMP_TAC [EXTENSION_LINCOMB_LMUL] THEN MATCH_MP_TAC RING_MUL_RZERO THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER]])

  let RING_OF_INTEGERS_QUOTIENT_FREE_BASIS_LE ← prove
    r"!k:A ring l:B ring h p J (g:(A->bool)->(B->bool)) m G.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        maximal_ideal (ring_of_integers k) p /\
        ring_ideal (ring_of_integers l) J /\
        ring_homomorphism(quotient_ring (ring_of_integers k) p,
                          quotient_ring (ring_of_integers l) J) g /\
        (!y. y IN ring_carrier(ring_of_integers k)
             ==> g(ring_coset (ring_of_integers k) p y) =
                 ring_coset (ring_of_integers l) J (h y)) /\
        free_basis (quotient_ring (ring_of_integers k) p,
                    quotient_ring (ring_of_integers l) J) g m G
        ==> m <= extension_degree(k,l) h"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_RING_IDEAL)) THEN FIRST_ASSUM (MP_TAC o (MATCH_MP MAXIMAL_IDEAL_IMP_PSUBSET)) THEN REWRITE_TAC [PSUBSET] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"field(quotient_ring (ring_of_integers k) (p:A->bool))") ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_QUOTIENT_RING], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o (MATCH_MP (← REWRITE_RULE [IMP_CONJ] RING_HOMOMORPHISM_IN_CARRIER))) THEN MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_MUL)) THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"?w:num->B. !i. i < m
                   ==> w i IN ring_carrier(ring_of_integers l) /\
                       G i = ring_coset (ring_of_integers l) J (w i)") STRIP_ASSUME_TAC THENL [REWRITE_TAC [(← GSYM SKOLEM_THM), RIGHT_EXISTS_IMP_THM] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o ((SPEC (← q r"i:num")) o (MATCH_MP FREE_BASIS_IN_CARRIER))) THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, IN_ELIM_THM] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. i < m ==> (w:num->B) i IN ring_carrier l") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [SUBSET] (← ISPEC (← q r"l:B ring") RING_OF_INTEGERS_SUBSET)) THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i j. i < m /\ j < m /\ (w:num->B) i = w j ==> i = j") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"g:(A->bool)->(B->bool)"), (← q r"quotient_ring (ring_of_integers k) (p:A->bool)"), (← q r"quotient_ring (ring_of_integers l) (J:B->bool)"), (← q r"m:num"), (← q r"G:num->(B->bool)")] FREE_BASIS_FIELD) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o CONJUNCT2) THEN REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN DISCH_THEN (fun th => STRIP_TAC THEN MATCH_MP_TAC th) THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_independent (k,l) (h:A->B) (IMAGE (w:num->B) {i | i < m})") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"m:num"), (← q r"w:num->B")] FREE_BASIS_INDEPENDENT_EQ) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"{i:num | i < m}"), (← q r"w:num->B")] NUMBER_FIELD_INDEPENDENT_MOD_IDEAL) THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC (← q r"u:num->A") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"g:(A->bool)->(B->bool)"), (← q r"quotient_ring (ring_of_integers k) (p:A->bool)"), (← q r"quotient_ring (ring_of_integers l) (J:B->bool)"), (← q r"m:num"), (← q r"G:num->(B->bool)"), (← q r"\i. ring_coset (ring_of_integers k) p ((u:num->A) i)")] FREE_BASIS_INDEPENDENT) THEN SIMP_TAC [QUOTIENT_RING_0, RING_COSET_EQ_IDEAL, (← ASSUME (← q r"ring_ideal (ring_of_integers k) (p:A->bool)")), (← ASSUME (← q r"ring_ideal (ring_of_integers l) (J:B->bool)")), (← ASSUME (← q r"!i. i < m
                         ==> (u:num->A) i IN ring_carrier(ring_of_integers k)")), (← ASSUME (← q r"free_basis (quotient_ring (ring_of_integers k) p,
                                 quotient_ring (ring_of_integers l) J)
                                (g:(A->bool)->(B->bool)) m G"))] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, IN_ELIM_THM] THEN EXISTS_TAC (← q r"(u:num->A) i") THEN ASM_SIMP_TAC [], ALL_TAC] THEN TRANS_TAC EQ_TRANS (← q r"ring_sum (quotient_ring (ring_of_integers l) J) {i | i < m}
        (\i. ring_mul (quotient_ring (ring_of_integers l) J)
               (ring_coset (ring_of_integers l) J ((h:A->B)((u:num->A) i)))
               (ring_coset (ring_of_integers l) J (w i)))") THEN CONJ_TAC THENL [MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC [IN_ELIM_THM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"quotient_ring (ring_of_integers l) (J:B->bool)"), (← q r"ring_coset (ring_of_integers l) (J:B->bool)"), (← q r"{i:num | i < m}"), (← q r"\i. (h:A->B)((u:num->A) i)"), (← q r"w:num->B")] RING_HOMOMORPHISM_SUM_MUL) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_COSET, FINITE_NUMSEG_LT, IN_ELIM_THM] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN wPart (rand o lhand) (lhand o rand) RING_SUM_RING_OF_INTEGERS THEN ASM_SIMP_TAC [IN_ELIM_THM] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"J:B->bool")] RING_COSET_0) THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [FINITE_EXTENSION_RING_MATROID] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_matroid(k,l) (h:A->B)"), (← q r"IMAGE (w:num->B) {i | i < m}")] MATROID_DIMENSION_GE_FINITE_CARD) THEN ASM_SIMP_TAC [RING_MATROID_INDEPENDENT, extension_degree] THEN MP_TAC (← ISPECL [(← q r"w:num->B"), (← q r"{i:num | i < m}")] CARD_IMAGE_INJ) THEN ASM_REWRITE_TAC [IN_ELIM_THM, FINITE_NUMSEG_LT, CARD_NUMSEG_LT] THEN SIMP_TAC [])

  let RING_OF_INTEGERS_IDEAL_EXTENSION_CONTRACTION_PRIME ← prove
    r"!k:A ring l:B ring h p.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
        ==> {x | x IN ring_carrier(ring_of_integers k) /\
                 h x IN ideal_generated (ring_of_integers l) (IMAGE h p)} = p"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_PRIME_IDEALS_ABOVE) THEN ASM_REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY), IN_ELIM_THM] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"P:B->bool") STRIP_ASSUME_TAC) o CONJUNCT2) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"P:B->bool"), (← q r"IMAGE (h:A->B) p")] IDEAL_GENERATED_MINIMAL) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"P:B->bool")] RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN DISCH_THEN (MP_TAC o (MATCH_MP (← REWRITE_RULE [IMP_CONJ] RING_HOMOMORPHISM_IN_CARRIER))) THEN MP_TAC (← MATCH_MP PRIME_IDEAL_IMP_SUBSET (← ASSUME (← q r"prime_ideal (ring_of_integers k) (p:A->bool)"))) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"IMAGE (h:A->B) p")] IDEAL_GENERATED_SUBSET_CARRIER) THEN SET_TAC [])

  let NUMBER_FIELD_IDEAL_NORM_EXTENSION_PRIME_LE ← prove
    r"!k:A ring l:B ring h p.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
        ==> ideal_norm (ring_of_integers l)
              (ideal_generated (ring_of_integers l) (IMAGE h p)) <=
            ideal_norm (ring_of_integers k) p EXP extension_degree(k,l) h"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] RING_OF_INTEGERS_IDEAL_EXTENSION_CONTRACTION_PRIME) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] RING_OF_INTEGERS_IDEAL_EXTENSION) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"J = ideal_generated (ring_of_integers l) (IMAGE (h:A->B) p)") THEN SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers l) (J:B->bool)") ASSUME_TAC THENL [EXPAND_TAC "J" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring"), (← q r"h:A->B"), (← q r"J:B->bool")] RESIDUE_DEGREE_QUOTIENT_RING) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_OF_INTEGERS] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"g:(A->bool)->(B->bool)") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"maximal_ideal (ring_of_integers k) (p:A->bool)") ASSUME_TAC THENL [MATCH_MP_TAC DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"field(quotient_ring (ring_of_integers k) (p:A->bool)) /\
    FINITE(ring_carrier(quotient_ring (ring_of_integers k) (p:A->bool))) /\
    FINITE(ring_carrier(quotient_ring (ring_of_integers l) (J:B->bool)))") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_QUOTIENT_RING, PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS_FINITE_QUOTIENT], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN MP_TAC (← ISPECL [(← q r"quotient_ring (ring_of_integers k) (p:A->bool)"), (← q r"quotient_ring (ring_of_integers l) (J:B->bool)"), (← q r"g:(A->bool)->(B->bool)"), (← q r"ring_carrier(quotient_ring (ring_of_integers l) (J:B->bool))")] FREE_BASIS_EXISTS) THEN ASM_REWRITE_TAC [ring_spanning, SUBSET_REFL, RING_SPAN_SELF] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"G:num->(B->bool)")) THEN MP_TAC (← ISPECL [(← q r"g:(A->bool)->(B->bool)"), (← q r"quotient_ring (ring_of_integers k) (p:A->bool)"), (← q r"quotient_ring (ring_of_integers l) (J:B->bool)"), (← q r"extension_degree
                   (quotient_ring (ring_of_integers k) (p:A->bool),
                    quotient_ring (ring_of_integers l) (J:B->bool))
                   (g:(A->bool)->(B->bool))"), (← q r"G:num->(B->bool)")] FREE_BASIS_HAS_SIZE) THEN ASM_REWRITE_TAC [HAS_SIZE, (← GSYM ideal_norm)] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:A->bool")] IDEAL_NORM_POS) THEN ASM_REWRITE_TAC [LE_EXP] THEN DISCH_TAC THEN COND_CASES_TAC THENL [ASM_ARITH_TAC, DISJ2_TAC] THEN MATCH_MP_TAC RING_OF_INTEGERS_QUOTIENT_FREE_BASIS_LE THEN MAP_EVERY EXISTS_TAC [(← q r"p:A->bool"), (← q r"J:B->bool"), (← q r"g:(A->bool)->(B->bool)"), (← q r"G:num->(B->bool)")] THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_IDEAL_NORM_EXTENSION_LE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"1 <= n ==> ~(n = 0)")
    let r2 ← ARITH_RULE (← q r"1 * b < a * b ==> b < a * b")
    prove
      r"!k:A ring l:B ring h j.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
          ==> ideal_norm (ring_of_integers l)
                (ideal_generated (ring_of_integers l) (IMAGE h j)) <=
              ideal_norm (ring_of_integers k) j EXP extension_degree(k,l) h"
      (REPEAT GEN_TAC THEN WF_INDUCT_TAC (← q r"ideal_norm (ring_of_integers k) (j:A->bool)") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"j:A->bool")] RING_OF_INTEGERS_IDEAL_EXTENSION) THEN ASM_REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"j = ring_carrier(ring_of_integers k:A ring)") THEN ASM_SIMP_TAC [IDEAL_NORM_CARRIER, EXP_ONE, LE_REFL] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"j:A->bool")] MAXIMAL_SUPERIDEAL_EXISTS) THEN ASM_SIMP_TAC [proper_ideal, PSUBSET, RING_IDEAL_IMP_SUBSET] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"p:A->bool") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"prime_ideal (ring_of_integers k) (p:A->bool) /\ ~(p = {ring_0 k})") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [MAXIMAL_IMP_PRIME_IDEAL] THEN MP_TAC (← MATCH_MP RING_IDEAL_IMP_NONEMPTY (← ASSUME (← q r"ring_ideal (ring_of_integers k) (j:A->bool)"))) THEN MAP_EVERY UNDISCH_TAC [(← q r"(j:A->bool) SUBSET p"), (← q r"~(j = {ring_0 k:A})")] THEN SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"j:A->bool"), (← q r"p:A->bool")] DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES) THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, MAXIMAL_IMP_RING_IDEAL] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:A->bool") (CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM))) THEN SUBGOAL_THEN (← q r"~(c = {ring_0 k:A})") ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC (← q r"~(ideal_prod (ring_of_integers k) p c = {ring_0 k:A})") THEN ASM_SIMP_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") IDEAL_PROD_RZERO)), MAXIMAL_IMP_RING_IDEAL, RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"p:A->bool"), (← q r"c:A->bool")] NUMBER_FIELD_IDEAL_NORM_MUL_Q) THEN ASM_SIMP_TAC [MAXIMAL_IMP_RING_IDEAL] THEN DISCH_THEN SUBST_ALL_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"c:A->bool")] RING_OF_INTEGERS_IDEAL_EXTENSION) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] RING_OF_INTEGERS_IDEAL_EXTENSION) THEN ASM_SIMP_TAC [MAXIMAL_IMP_RING_IDEAL] THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"c:A->bool")] IDEAL_PROD_HOMOMORPHIC_IMAGE) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_OF_INTEGERS, MAXIMAL_IMP_RING_IDEAL, RING_IDEAL_IMP_SUBSET] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"ideal_generated (ring_of_integers l) (IMAGE (h:A->B) p)"), (← q r"ideal_generated (ring_of_integers l) (IMAGE (h:A->B) c)")] NUMBER_FIELD_IDEAL_NORM_MUL_Q) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [MULT_EXP] THEN MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THENL [MATCH_MP_TAC NUMBER_FIELD_IDEAL_NORM_EXTENSION_PRIME_LE THEN ASM_REWRITE_TAC [], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (SPECL [(← q r"k:A ring"), (← q r"c:A->bool")])) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC r2 THEN REWRITE_TAC [LT_MULT_RCANCEL] THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_NORM_GT_1 THEN ASM_SIMP_TAC [MAXIMAL_IMP_RING_IDEAL, RING_OF_INTEGERS_FINITE_QUOTIENT] THEN ASM_MESON_TAC [MAXIMAL_IDEAL_IMP_PSUBSET, PSUBSET], MATCH_MP_TAC r1 THEN MATCH_MP_TAC IDEAL_NORM_POS THEN ASM_SIMP_TAC [RING_OF_INTEGERS_FINITE_QUOTIENT]])

  let NUMBER_FIELD_IDEAL_NORM_EXTENSION_Q ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"c:num"
    let q2 ← q r"a:num"
    let q3 ← q r"b:num"
    let v4 ← SPECL [q3, q2, q1] LE_MULT_RCANCEL
    let v5 ← GSYM LE_ANTISYM
    let p6 ← prove r"!a b c d. a <= b /\ c <= d /\ ~(c = 0) /\ a * c = b * d ==> a = b" (REPEAT STRIP_TAC THEN REWRITE_TAC [v5] THEN ASM_REWRITE_TAC [] THEN MP_TAC v4 THEN ASM_REWRITE_TAC [LE_MULT_LCANCEL] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC [])
    let lemma := p6
    let q7 ← q r"ring_homomorphism(k:A ring,l:B ring) h"
    let v8 ← ASSUME q7
    let v9 ← MATCH_MP RING_HOMOMORPHISM_RING_OF_INT v8
    let q10 ← q r"c:A->bool"
    let q11 ← q r"j:A->bool"
    let q12 ← q r"h:A->B"
    let q13 ← q r"ring_of_integers l:B ring"
    let q14 ← q r"ring_of_integers k:A ring"
    let v15 ← ISPECL [q14, q13, q12, q11, q10] IDEAL_PROD_HOMOMORPHIC_IMAGE
    let q16 ← q r"ideal_generated (ring_of_integers l) (IMAGE (h:A->B) c)"
    let q17 ← q r"ideal_generated (ring_of_integers l) (IMAGE (h:A->B) j)"
    let q18 ← q r"l:B ring"
    let v19 ← ISPECL [q18, q17, q16] NUMBER_FIELD_IDEAL_NORM_MUL_Q
    let q20 ← q r"c:A->bool"
    let q21 ← q r"j:A->bool"
    let q22 ← q r"k:A ring"
    let v23 ← ISPECL [q22, q21, q20] NUMBER_FIELD_IDEAL_NORM_MUL_Q
    let v24 ← GSYM MULT_EXP
    let q25 ← q r"1 <= n ==> ~(n = 0)"
    let r26 ← ARITH_RULE q25
    let q27 ← q r"ideal_norm (ring_of_integers k) c EXP
              extension_degree(k:A ring,l:B ring) h"
    let q28 ← q r"ideal_norm (ring_of_integers l)
                (ideal_generated (ring_of_integers l) (IMAGE (h:A->B) c))"
    let q29 ← q r"c:A->bool"
    let q30 ← q r"h:A->B"
    let q31 ← q r"l:B ring"
    let q32 ← q r"k:A ring"
    let v33 ← ISPECL [q32, q31, q30, q29] RING_OF_INTEGERS_IDEAL_EXTENSION
    let q34 ← q r"j:A->bool"
    let q35 ← q r"h:A->B"
    let q36 ← q r"l:B ring"
    let q37 ← q r"k:A ring"
    let v38 ← ISPECL [q37, q36, q35, q34] RING_OF_INTEGERS_IDEAL_EXTENSION
    let q39 ← q r"number_field(k:A ring)"
    let v40 ← ASSUME q39
    let q41 ← q r"ring_of_int k m:A"
    let q42 ← q r"ring_ideal (ring_of_integers k) (j:A->bool)"
    let v43 ← ASSUME q42
    let q44 ← q r"ring_of_integers k:A ring"
    let v45 ← ISPEC q44 IDEAL_PROD_RZERO
    let v46 ← REWRITE_RULE [RING_OF_INTEGERS] v45
    let q47 ← q r"ideal_prod (ring_of_integers k) j {ring_0 k} =
                 ideal_generated (ring_of_integers k) {ring_of_int k m:A}"
    let q48 ← q r"~(c = {ring_0 k:A})"
    let q49 ← q r"c:A->bool"
    let q50 ← q r"j:A->bool"
    let q51 ← q r"ideal_generated (ring_of_integers k) {ring_of_int k m:A}"
    let q52 ← q r"ring_of_integers k:A ring"
    let v53 ← ISPECL [q52, q51, q50] DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES
    let q54 ← q r"m:int"
    let q55 ← q r"j:A->bool"
    let q56 ← q r"k:A ring"
    let v57 ← ISPECL [q56, q55] RING_OF_INTEGERS_IDEAL_INTEGER
    let q58 ← q r"h:A->B"
    let q59 ← q r"l:B ring"
    let q60 ← q r"k:A ring"
    let v61 ← ISPECL [q60, q59, q58] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE
    prove
      r"!k:A ring l:B ring h j.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
          ==> ideal_norm (ring_of_integers l)
                (ideal_generated (ring_of_integers l) (IMAGE h j)) =
              ideal_norm (ring_of_integers k) j EXP extension_degree(k,l) h"
      (REPEAT STRIP_TAC THEN MP_TAC v61 THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC v57 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN q54 STRIP_ASSUME_TAC) THEN MP_TAC v53 THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_MINIMAL, SING_SUBSET] THEN DISCH_THEN (X_CHOOSE_THEN q49 STRIP_ASSUME_TAC) THEN SUBGOAL_THEN q48 ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC q47 THEN SIMP_TAC [v46, RING_IDEAL_IMP_SUBSET, v43] THEN DISCH_THEN (MP_TAC o ((SPEC q41) o (REWRITE_RULE [EXTENSION]))) THEN REWRITE_TAC [IN_SING, IN_IDEAL_GENERATED_SELF, RING_OF_INT_IN_RING_OF_INTEGERS] THEN MP_TAC v40 THEN SIMP_TAC [number_field, RING_OF_INT_EQ_0_CHAR_0] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC v38 THEN MP_TAC v33 THEN ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma THEN EXISTS_TAC q28 THEN EXISTS_TAC q27 THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_EXTENSION_LE] THEN CONJ_TAC THENL [MATCH_MP_TAC r26 THEN ASM_SIMP_TAC [IDEAL_NORM_POS, RING_OF_INTEGERS_FINITE_QUOTIENT, RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN REWRITE_TAC [v24] THEN MP_TAC v23 THEN MP_TAC v19 THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN MP_TAC v15 THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_OF_INTEGERS, RING_IDEAL_IMP_SUBSET] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [IDEAL_GENERATED_IMAGE_IDEAL_GENERATED, IMAGE_CLAUSES, RING_HOMOMORPHISM_RING_OF_INTEGERS, SING_SUBSET, RING_OF_INT_IN_RING_OF_INTEGERS] THEN REWRITE_TAC [v9] THEN ASM_SIMP_TAC [RING_OF_INTEGERS_IDEAL_NORM_INTEGER, NUMBER_FIELD_TOWER_LAW, EXP_EXP])

  let NUMBER_FIELD_FUNDAMENTAL_IDENTITY ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"1 < n ==> ~(n = 0) /\ ~(n = 1)")
    let r2 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!k:A ring l:B ring h p.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
          ==> nsum {P | prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P}
                   (\P. ramification_index
                          (ring_of_integers k,ring_of_integers l) h P *
                        residue_degree
                          (ring_of_integers k,ring_of_integers l) h P) =
              extension_degree(k,l) h"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_PRIME_IDEALS_ABOVE) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!P. P IN {P | prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P}
          ==> prime_ideal (ring_of_integers l) P /\ ~(P = {ring_0 l}) /\
              IMAGE (h:A->B) p SUBSET P") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o ((GEN_REWRITE_RULE id [EXTENSION]) o (CONJUNCT2 o CONJUNCT2))) THEN REWRITE_TAC [IN_ELIM_THM] THEN MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_IDEAL_NORM_EXTENSION_Q) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, NUMBER_FIELD_PRIME_FACTORIZATION] THEN wPart (lhand o lhand) (lhand o rand o rand) IDEAL_NORM_IDEAL_PRODUCT THEN ANTS_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS] THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_IDEAL_IDEAL_POW] THEN X_GEN_TAC (← q r"P:B->bool") THEN DISCH_THEN (fun th => tactic_of do pure (FIRST_ASSUM (STRIP_ASSUME_TAC o (← do let c := th; pure (fun th => MATCH_MP th c))))) THEN MATCH_MP_TAC r2 THEN CONJ_TAC THENL [ASM_SIMP_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") IDEAL_POW_EQ_ZERO)), INTEGRAL_DOMAIN_RING_OF_INTEGERS, NUMBER_FIELD_IMP_FIELD, PRIME_IMP_RING_IDEAL], ASM_SIMP_TAC [RING_OF_INTEGERS_FINITE_QUOTIENT, RING_IDEAL_IDEAL_POW]], DISCH_THEN (SUBST1_TAC o CONJUNCT2)] THEN REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"!P. P IN {P | prime_ideal (ring_of_integers l) P /\
                    IMAGE (h:A->B) p SUBSET P}
          ==> ideal_norm (ring_of_integers l)
                (ideal_pow (ring_of_integers l) P
                   (ramification_index
                      (ring_of_integers k,ring_of_integers l) h P)) =
              ideal_norm (ring_of_integers k) p EXP
              (ramification_index
                 (ring_of_integers k,ring_of_integers l) h P *
               residue_degree
                 (ring_of_integers k,ring_of_integers l) h P)") (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP NPRODUCT_EQ th)])) THENL [X_GEN_TAC (← q r"P:B->bool") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"P:B->bool"))) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"P:B->bool")] RING_OF_INTEGERS_IDEAL_NORM_PRIME) THEN ASM_SIMP_TAC [IDEAL_NORM_IDEAL_POW, DEDEKIND_RING_OF_INTEGERS, PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS_FINITE_QUOTIENT, RING_OF_INTEGERS] THEN REWRITE_TAC [EXP_EXP, MULT_SYM], ASM_SIMP_TAC [(← GSYM EXP_NSUM)] THEN SUBGOAL_THEN (← q r"1 < ideal_norm (ring_of_integers k) (p:A->bool)") MP_TAC THENL [MATCH_MP_TAC IDEAL_NORM_GT_1 THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS_FINITE_QUOTIENT] THEN ASM_MESON_TAC [PRIME_IDEAL_IMP_PSUBSET, PSUBSET], SIMP_TAC [EQ_EXP, r1] THEN MESON_TAC []]])

  let NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"1 < n ==> ~(n = 1)")
    let r2 ← ARITH_RULE (← q r"1 <= n <=> ~(n = 0)")
    prove
      r"!k:A ring l:B ring h p P.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
          prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P
          ==> 1 <= ramification_index
                     (ring_of_integers k,ring_of_integers l) h P /\
              1 <= residue_degree
                     (ring_of_integers k,ring_of_integers l) h P /\
              ramification_index
                (ring_of_integers k,ring_of_integers l) h P *
              residue_degree
                (ring_of_integers k,ring_of_integers l) h P
              <= extension_degree(k,l) h"
      (REPEAT STRIP_TAC THENL [ALL_TAC, ALL_TAC, MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_FUNDAMENTAL_IDENTITY) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_PRIME_IDEALS_ABOVE) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN DISCH_THEN (MP_TAC o (MATCH_MP EQ_IMP_LE)) THEN DISCH_THEN (MP_TAC o (MATCH_MP (← REWRITE_RULE [IMP_CONJ_ALT] NSUM_POS_BOUND))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"P:B->bool"))) THEN ASM_REWRITE_TAC [IN_ELIM_THM]] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"P:B->bool")) o ((GEN_REWRITE_RULE id [EXTENSION]) o (CONJUNCT2 o CONJUNCT2)))) THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"P:B->bool")] RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN ASM_REWRITE_TAC [ramification_index] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] RING_OF_INTEGERS_IDEAL_EXTENSION) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"P:B->bool"), (← q r"ideal_generated (ring_of_integers l) (IMAGE (h:A->B) p)"), (← q r"1")] DEDEKIND_IDEAL_SUBSET_POW_VALUATION) THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED, IDEAL_POW_1, PRIME_IMP_RING_IDEAL, IDEAL_GENERATED_MINIMAL, RING_OF_INTEGERS], MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"P:B->bool")] RING_OF_INTEGERS_IDEAL_NORM_PRIME) THEN ASM_REWRITE_TAC [r2] THEN ASM_CASES_TAC (← q r"residue_degree (ring_of_integers k,ring_of_integers l)
                                (h:A->B) P = 0") THEN ASM_REWRITE_TAC [EXP] THEN MATCH_MP_TAC r1 THEN MATCH_MP_TAC IDEAL_NORM_GT_1 THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS_FINITE_QUOTIENT] THEN MP_TAC (← MATCH_MP PRIME_IDEAL_IMP_PSUBSET (← ASSUME (← q r"prime_ideal (ring_of_integers l) (P:B->bool)"))) THEN SIMP_TAC [PSUBSET]])

  let NUMBER_FIELD_CARD_PRIME_IDEALS_ABOVE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"1 <= n <=> ~(n = 0)")
    let r2 ← ARITH_RULE (← q r"1 <= n <=> ~(n = 0)")
    prove
      r"!k:A ring l:B ring h p.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
          ==> 1 <= CARD {P | prime_ideal (ring_of_integers l) P /\
                             IMAGE h p SUBSET P} /\
              CARD {P | prime_ideal (ring_of_integers l) P /\
                        IMAGE h p SUBSET P}
              <= extension_degree(k,l) h"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_PRIME_IDEALS_ABOVE) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_SIMP_TAC [r2, CARD_EQ_0] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_FUNDAMENTAL_IDENTITY) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [CARD_EQ_NSUM] THEN MATCH_MP_TAC NSUM_LE THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"P:B->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"P:B->bool")] NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS) THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [r1, MULT_EQ_0] THEN ARITH_TAC)

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_INDEPENDENT_MOD_IDEAL, RING_OF_INTEGERS_QUOTIENT_FREE_BASIS_LE,
           RING_OF_INTEGERS_IDEAL_EXTENSION_CONTRACTION_PRIME,
           NUMBER_FIELD_IDEAL_NORM_EXTENSION_PRIME_LE,
           NUMBER_FIELD_IDEAL_NORM_EXTENSION_LE, NUMBER_FIELD_IDEAL_NORM_EXTENSION_Q,
           NUMBER_FIELD_FUNDAMENTAL_IDENTITY, NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS,
           NUMBER_FIELD_CARD_PRIME_IDEALS_ABOVE }
  -- @@RETURN END

end HolANT.RelativeDegree
