/- ========================================================================= -/
/- ANT: The decomposition of primes in a cyclotomic field k = Q(z) ...     -/
/- ========================================================================= -/
/- File: HolANT/CyclotomicSplit.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/cyclotomic_split.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antcyclotomicsplitdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, ANT/ideal_arith.ml, Library/isum.ml, Library/products.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/prime_split.ml, ANT/norm_index.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/finite_field_trace.ml, ANT/ramification.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/classgroup.ml, ANT/relative_split.ml, ANT/relative_degree.ml, ANT/nf_valuation.ml, ANT/integrality.ml, ANT/dedekind_kummer.ml, ANT/splitting_types.ml, Library/frag.ml, Library/grouptheory.ml, Library/symmetric_group.ml, Library/galois.ml, Library/ring_groups.ml, Library/finite_fields.ml, Library/integer.ml, Library/multiplicative.ml, Library/primitive.ml, ANT/cyclotomic_poly.ml, ANT/power_basis.ml, ANT/cyclotomic_field.ml, ANT/cyclotomic_integers.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.CyclotomicSplit fills them).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left.  The `do` macro of HolCore/OcamlOrder.lean
  (HolLight.Syntax) binds each statement's `(← ...)` actions in that order,
  so quotations and rules (MESON, ARITH_RULE, ...) run as in HOL Light;
  where a rule is bound by a `let` before the proof, it is bound in OCaml's
  order.
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
import HolANT.IdealArith
import HolLibrary.Isum
import HolLibrary.Products
import HolANT.Algmisc
import HolANT.Integral
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.IdealNorm
import HolANT.RingOfIntegers
import HolANT.PrimeSplit
import HolANT.NormIndex
import HolANT.Discriminant
import HolANT.TraceForm
import HolANT.FiniteFieldTrace
import HolANT.Ramification
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.Classgroup
import HolANT.RelativeSplit
import HolANT.RelativeDegree
import HolANT.NfValuation
import HolANT.Integrality
import HolANT.DedekindKummer
import HolANT.SplittingTypes
import HolLibrary.Frag
import HolLibrary.GroupTheory
import HolLibrary.SymmetricGroup
import HolLibrary.Galois
import HolLibrary.RingGroups
import HolLibrary.FiniteFields
import HolLibrary.Integer
import HolLibrary.Multiplicative
import HolLibrary.Primitive
import HolANT.CyclotomicPoly
import HolANT.PowerBasis
import HolANT.CyclotomicField
import HolANT.CyclotomicIntegers

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.IdealArith
open HolANT.Algmisc
open HolANT.Integral
open HolANT.Zlattice
open HolANT.Numfield
open HolANT.Dedekind
open HolANT.DedekindStruct
open HolANT.IdealNorm
open HolANT.RingOfIntegers
open HolANT.PrimeSplit
open HolANT.NormIndex
open HolANT.Discriminant
open HolANT.TraceForm
open HolANT.FiniteFieldTrace
open HolANT.Ramification
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.Classgroup
open HolANT.RelativeSplit
open HolANT.RelativeDegree
open HolANT.NfValuation
open HolANT.Integrality
open HolANT.DedekindKummer
open HolANT.SplittingTypes
open HolANT.CyclotomicPoly
open HolANT.PowerBasis
open HolANT.CyclotomicField
open HolANT.CyclotomicIntegers

namespace HolANT.CyclotomicSplit

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD_EQ_0 ARITH ARITH_EQ CARD_IMAGE_INJ CARD_INTEGER_MOD_RING
   CARRIER_SUBRING_OF CONTRAPOS_THM COPRIME_SYM CYCLOTOMIC_FIELD_DEGREE
   CYCLOTOMIC_FIELD_RING_OF_INTEGERS CYCLOTOMIC_POLY_1 CYCLOTOMIC_POLY_DEG
   CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE CYCLOTOMIC_POLY_IN_CARRIER
   CYCLOTOMIC_POLY_IRREDUCIBLE_FACTORIZATION CYCLOTOMIC_POLY_MONIC
   CYCLOTOMIC_POLY_RING_CHAR CYCLOTOMIC_POLY_ROOT DEDEKIND_KUMMER_EPIMORPHISM_Q
   DEDEKIND_KUMMER_Q DIVIDES_0 DIVIDES_ONE DIVIDES_REFL DIVIDES_REXP
   DIVIDES_RMUL EQ_MULT_LCANCEL EXP EXP_ADD EXP_EQ_0 FIELD_IMP_INTEGRAL_DOMAIN
   FIELD_INTEGER_MOD_RING FINITE_INTEGER_MOD_RING FINITE_SING FORALL_UNWIND_THM2
   IDEALS_GENERATED_SUBSET IDEAL_GENERATED_INC_GEN IDEAL_GENERATED_NONEMPTY
   IDEAL_GENERATED_SUBSET IDEAL_PRODUCT_SING IMP_CONJ INDEX_DECOMPOSITION
   INTEGER_MOD_RING_CHAR INTEGER_RING INTEGRAL_DOMAIN_RING_OF_INTEGERS
   INT_OF_NUM_EQ IN_ELIM_THM IN_IDEAL_GENERATED_SELF IN_IDEAL_GENERATED_SING
   IN_IMAGE IN_INSERT IN_INTER IN_RING_IDEAL_SUB IN_SING LE_1 LE_MULT2 LT_REFL
   MEMBER_NOT_EMPTY MULT_CLAUSES MULT_EQ_0 NOT_IN_EMPTY NUMBER_FIELD_IMP_FIELD
   NUMBER_FIELD_PRIME_DECOMPOSITION_Q NUMBER_FIELD_RAMIFIED_DISCRIMINANT
   NUMBER_FIELD_TOTALLY_SPLIT_CARD ORDER_EQ_1 PHI_1 PHI_EQ_0
   PHI_LOWERBOUND_1_STRONG PHI_PRIMEPOW_ALT POLY_DEG_1_IMP_IRREDUCIBLE
   POLY_EVAL_1 POLY_EVAL_SUB POLY_EVAL_VAR POLY_EXTEND_EVALUATE
   POLY_EXTEND_RING_OF_INTEGERS POLY_RING_CLAUSES
   POLY_RING_INTEGER_MOD_RING_SUBSET PRIME_COPRIME_EQ PRIME_GE_2 PRIME_IMP_NZ
   RING_1 RING_ASSOCIATES_PRIME_POWER_ORDER RING_COSET_EQ RING_DIVIDES_REFL
   RING_DIVIDES_RMUL RING_DIVIDES_TRANS RING_HOMOMORPHISM_INTEGER_RING_OF_INT
   RING_IDEAL_IDEAL_GENERATED RING_IDEAL_IDEAL_POW RING_OF_INTEGERS
   RING_OF_INTEGERS_SUBSET RING_OF_NUM RING_ORDER_DIVIDES RING_ORDER_UNIQUE
   RING_POLYNOMIAL_1 RING_POLYNOMIAL_VAR RING_POW RING_PRODUCT_POW
   RING_PRODUCT_SING RING_SETADD_RSUBSET RING_SUB SUBRING_GENERATED_INC_GEN
   SUBSET SUBSET_ANTISYM_EQ TRIVIAL_INTEGER_MOD_RING TRIVIAL_RING_10 divides
   poly_eval ring_associates ring_pow : thm)
  deriving Inhabited

/-- What cyclotomic_split.ml uses from Session besides theorems. -/
structure CyclotomicSplitDeps where
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
/- cyclotomic_split.ml phrases from line 66 to 258                        -/
/- ---------------------------------------------------------------------- -/

structure CyclotomicSplit where
  -- @@FIELDS
  CYCLOTOMIC_FIELD_DEDEKIND_KUMMER : thm
  CYCLOTOMIC_FIELD_PRIME_DECOMPOSITION : thm
  CYCLOTOMIC_FIELD_RAMIFIED : thm
  CYCLOTOMIC_FIELD_TOTALLY_SPLIT : thm
  CYCLOTOMIC_FIELD_PRIME_POWER_RAMIFIED : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupCyclotomicSplit [HolBase] (D : CyclotomicSplitDeps) :
    ExceptT String IO CyclotomicSplit := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON, MESON_TAC,
        NUMBER_RULE, NUM_REDUCE_CONV, RING_RULE, .. } := D
  let { ADD_EQ_0, ARITH, ARITH_EQ, CARD_IMAGE_INJ, CARD_INTEGER_MOD_RING,
        CARRIER_SUBRING_OF, CONTRAPOS_THM, COPRIME_SYM, CYCLOTOMIC_FIELD_DEGREE,
        CYCLOTOMIC_FIELD_RING_OF_INTEGERS, CYCLOTOMIC_POLY_1, CYCLOTOMIC_POLY_DEG,
        CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE, CYCLOTOMIC_POLY_IN_CARRIER,
        CYCLOTOMIC_POLY_IRREDUCIBLE_FACTORIZATION, CYCLOTOMIC_POLY_MONIC,
        CYCLOTOMIC_POLY_RING_CHAR, CYCLOTOMIC_POLY_ROOT, DEDEKIND_KUMMER_EPIMORPHISM_Q,
        DEDEKIND_KUMMER_Q, DIVIDES_0, DIVIDES_ONE, DIVIDES_REFL, DIVIDES_REXP,
        DIVIDES_RMUL, EQ_MULT_LCANCEL, EXP, EXP_ADD, EXP_EQ_0,
        FIELD_IMP_INTEGRAL_DOMAIN, FIELD_INTEGER_MOD_RING, FINITE_INTEGER_MOD_RING,
        FINITE_SING, FORALL_UNWIND_THM2, IDEALS_GENERATED_SUBSET,
        IDEAL_GENERATED_INC_GEN, IDEAL_GENERATED_NONEMPTY, IDEAL_GENERATED_SUBSET,
        IDEAL_PRODUCT_SING, IMP_CONJ, INDEX_DECOMPOSITION, INTEGER_MOD_RING_CHAR,
        INTEGER_RING, INTEGRAL_DOMAIN_RING_OF_INTEGERS, INT_OF_NUM_EQ, IN_ELIM_THM,
        IN_IDEAL_GENERATED_SELF, IN_IDEAL_GENERATED_SING, IN_IMAGE, IN_INSERT,
        IN_INTER, IN_RING_IDEAL_SUB, IN_SING, LE_1, LE_MULT2, LT_REFL,
        MEMBER_NOT_EMPTY, MULT_CLAUSES, MULT_EQ_0, NOT_IN_EMPTY,
        NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_PRIME_DECOMPOSITION_Q,
        NUMBER_FIELD_RAMIFIED_DISCRIMINANT, NUMBER_FIELD_TOTALLY_SPLIT_CARD,
        ORDER_EQ_1, PHI_1, PHI_EQ_0, PHI_LOWERBOUND_1_STRONG, PHI_PRIMEPOW_ALT,
        POLY_DEG_1_IMP_IRREDUCIBLE, POLY_EVAL_1, POLY_EVAL_SUB, POLY_EVAL_VAR,
        POLY_EXTEND_EVALUATE, POLY_EXTEND_RING_OF_INTEGERS, POLY_RING_CLAUSES,
        POLY_RING_INTEGER_MOD_RING_SUBSET, PRIME_COPRIME_EQ, PRIME_GE_2, PRIME_IMP_NZ,
        RING_1, RING_ASSOCIATES_PRIME_POWER_ORDER, RING_COSET_EQ, RING_DIVIDES_REFL,
        RING_DIVIDES_RMUL, RING_DIVIDES_TRANS, RING_HOMOMORPHISM_INTEGER_RING_OF_INT,
        RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_POW, RING_OF_INTEGERS,
        RING_OF_INTEGERS_SUBSET, RING_OF_NUM, RING_ORDER_DIVIDES, RING_ORDER_UNIQUE,
        RING_POLYNOMIAL_1, RING_POLYNOMIAL_VAR, RING_POW, RING_PRODUCT_POW,
        RING_PRODUCT_SING, RING_SETADD_RSUBSET, RING_SUB, SUBRING_GENERATED_INC_GEN,
        SUBSET, SUBSET_ANTISYM_EQ, TRIVIAL_INTEGER_MOD_RING, TRIVIAL_RING_10, divides,
        poly_eval, ring_associates, ring_pow, .. } := D.core1
  -- @@SCOPE END

  let CYCLOTOMIC_FIELD_DEDEKIND_KUMMER ← prove
    r"!(k:A ring) z p a m s P.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = p EXP a * m /\ subfield_generated k {z} = k /\
        prime p /\ ~(p divides m) /\ FINITE s /\
        (!g. g IN s
             ==> g IN ring_carrier(poly_ring (integer_mod_ring p) (:1)) /\
                 monic (integer_mod_ring p) g /\
                 ring_irreducible (poly_ring (integer_mod_ring p) (:1)) g) /\
        cyclotomic_poly (integer_mod_ring p) m =
        ring_product (poly_ring (integer_mod_ring p) (:1)) s (\g. g) /\
        (!g. P g =
             ideal_generated (ring_of_integers k)
               {ring_of_num k p,
                poly_extend (integer_ring,k) (ring_of_int k) (\v. z) g})
        ==> ideal_generated (ring_of_integers k) {ring_of_num k p} =
            ideal_product (ring_of_integers k) s
              (\g. ideal_pow (ring_of_integers k) (P g) (phi(p EXP a))) /\
            {Q | prime_ideal (ring_of_integers k) Q /\ ring_of_num k p IN Q} =
            IMAGE P s /\
            (!g h. g IN s /\ h IN s /\ P g = P h ==> g = h) /\
            (!g. g IN s
                 ==> prime_ideal (ring_of_integers k) (P g) /\
                     residue_degree (integer_ring,ring_of_integers k)
                       (ring_of_int k) (P g) =
                     poly_deg (integer_mod_ring p) g /\
                     ramification_index (integer_ring,ring_of_integers k)
                       (ring_of_int k) (P g) =
                     phi(p EXP a))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN ABBREV_TAC (← q r"n = p EXP a * m") THEN SUBGOAL_THEN (← q r"~(n = 0)") ASSUME_TAC THENL [EXPAND_TAC "n" THEN REWRITE_TAC [MULT_EQ_0, EXP_EQ_0] THEN ASM_MESON_TAC [PRIME_IMP_NZ, DIVIDES_0], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"p:num"), (← q r"cyclotomic_poly integer_ring n"), (← q r"s:((1->num)->int)->bool"), (← q r"\g:(1->num)->int. g"), (← q r"\g:(1->num)->int. phi(p EXP a)"), (← q r"P:((1->num)->int)->A->bool")] DEDEKIND_KUMMER_Q) THEN REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [CYCLOTOMIC_POLY_IN_CARRIER, CYCLOTOMIC_POLY_MONIC] THEN ASM_SIMP_TAC [PHI_EQ_0, EXP_EQ_0, PRIME_IMP_NZ] THEN REPEAT CONJ_TAC THENL [REWRITE_TAC [CYCLOTOMIC_POLY_DEG, INTEGER_RING, INT_OF_NUM_EQ, ARITH_EQ] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CYCLOTOMIC_FIELD_DEGREE THEN EXISTS_TAC (← q r"z:A") THEN ASM_REWRITE_TAC [], SIMP_TAC [POLY_EXTEND_EVALUATE, RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN REWRITE_TAC [(← GSYM poly_eval), (← MATCH_MP CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE (← ISPEC (← q r"k:A ring") RING_HOMOMORPHISM_INTEGER_RING_OF_INT))] THEN MATCH_MP_TAC CYCLOTOMIC_POLY_ROOT THEN ASM_SIMP_TAC [NUMBER_FIELD_IMP_FIELD, FIELD_IMP_INTEGRAL_DOMAIN], MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num")] CYCLOTOMIC_FIELD_RING_OF_INTEGERS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_SETADD_RSUBSET THEN REWRITE_TAC [CARRIER_SUBRING_OF, IDEAL_GENERATED_SUBSET, IDEAL_GENERATED_NONEMPTY], REWRITE_TAC [(← MATCH_MP CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE (← ISPEC (← q r"integer_mod_ring p") RING_HOMOMORPHISM_INTEGER_RING_OF_INT))] THEN EXPAND_TAC "n" THEN ASM_SIMP_TAC [CYCLOTOMIC_POLY_RING_CHAR, INTEGER_MOD_RING_CHAR] THEN REWRITE_TAC [(← GSYM (← ISPECL [(← q r"integer_mod_ring p"), (← q r"(:1)")] (← (do let z1 ← (pure (CONJUNCTS POLY_RING_CLAUSES)); let z2 ← (pure 7); liftExcept (el z2 z1)))))] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_PRODUCT_POW THEN ASM_SIMP_TAC []])

  let CYCLOTOMIC_FIELD_PRIME_DECOMPOSITION ← prove
    r"!(k:A ring) z n p a m.
        number_field k /\ z IN ring_carrier k /\ ring_order k z = n /\
        subfield_generated k {z} = k /\
        prime p /\ n = p EXP a * m /\ ~(p divides m)
        ==> (!P. prime_ideal (ring_of_integers k) P /\ ring_of_num k p IN P
                 ==> ramification_index (integer_ring,ring_of_integers k)
                       (ring_of_int k) P = phi(p EXP a) /\
                     residue_degree (integer_ring,ring_of_integers k)
                       (ring_of_int k) P = order m p) /\
            CARD {P | prime_ideal (ring_of_integers k) P /\
                      ring_of_num k p IN P} * order m p = phi m"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM (SUBST_ALL_TAC o (checkM (fun z1 => (do let z2 ← (do let z3 ← (do let z4 ← (pure z1); pure (concl z4)); liftExcept (lhs z3)); pure (is_var z2))))) THEN MP_TAC (← ISPECL [(← q r"integer_mod_ring p"), (← q r"m:num")] CYCLOTOMIC_POLY_IRREDUCIBLE_FACTORIZATION) THEN ASM_SIMP_TAC [FIELD_INTEGER_MOD_RING, FINITE_INTEGER_MOD_RING, CARD_INTEGER_MOD_RING, PRIME_IMP_NZ, (← ONCE_REWRITE_RULE [COPRIME_SYM] PRIME_COPRIME_EQ)] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"s:((1->num)->int)->bool") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"p:num"), (← q r"a:num"), (← q r"m:num"), (← q r"s:((1->num)->int)->bool"), (← q r"\g. ideal_generated (ring_of_integers k)
                        {ring_of_num (k:A ring) p,
                         poly_extend (integer_ring,k) (ring_of_int k) (\v. z)
                           (g:(1->num)->int)}")] CYCLOTOMIC_FIELD_DEDEKIND_KUMMER) THEN ASM_SIMP_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 (fun (_ : thm) => ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)) THEN CONJ_TAC THENL [X_GEN_TAC (← q r"Q:A->bool") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(Q:A->bool) IN
      {Q | prime_ideal (ring_of_integers k) Q /\ ring_of_num (k:A ring) p IN Q}") MP_TAC THENL [REWRITE_TAC [IN_ELIM_THM] THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC, ASM_REWRITE_TAC [IN_IMAGE]] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"g:(1->num)->int") (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN ASM_SIMP_TAC [], ASM_REWRITE_TAC [] THEN wPart (lhand o lhand) (lhand o rand) CARD_IMAGE_INJ THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC []])

  let CYCLOTOMIC_FIELD_RAMIFIED ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let lemma := (← prove r"!p a m.
        prime p /\ ~(p divides m)
        ==> (1 < phi(p EXP a) <=>
             p divides p EXP a * m /\ ~(p = 2 /\ ~(4 divides p EXP a * m)))" (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [PHI_PRIMEPOW_ALT] THEN ASM_CASES_TAC (← q r"a = 0") THEN ASM_REWRITE_TAC [EXP, MULT_CLAUSES, LT_REFL] THEN ASM_SIMP_TAC [DIVIDES_RMUL, DIVIDES_REXP, DIVIDES_REFL] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_GE_2)) THEN ASM_CASES_TAC (← q r"p = 2") THEN ASM_REWRITE_TAC [] THENL [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_CASES_TAC (← q r"a = 1") THEN ASM_REWRITE_TAC [] THENL [CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC (← q r"~(2 divides m)") THEN REWRITE_TAC [CONTRAPOS_THM, divides] THEN STRIP_TAC THEN EXISTS_TAC (← q r"x:num") THEN ASM_ARITH_TAC, SUBGOAL_THEN (← q r"?b. a = b + 2") (CHOOSE_THEN SUBST1_TAC) THENL [EXISTS_TAC (← q r"a - 2") THEN ASM_ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [(← ARITH_RULE (← q r"(b + 2) - 1 = b + 1")), EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [(← ARITH_RULE (← q r"1 < (x * 2) * 1 <=> ~(x = 0)")), EXP_EQ_0] THEN CONV_TAC NUMBER_RULE], MATCH_MP_TAC (← ARITH_RULE (← q r"1 * 2 <= x * y ==> 1 < x * y")) THEN MATCH_MP_TAC LE_MULT2 THEN ASM_SIMP_TAC [LE_1, EXP_EQ_0, PRIME_IMP_NZ] THEN ASM_ARITH_TAC]))
    prove
      r"!(k:A ring) z n p.
          number_field k /\ z IN ring_carrier k /\
          ring_order k z = n /\ ~(n = 0) /\ subfield_generated k {z} = k /\
          prime p
          ==> (&p divides number_field_discriminant k <=>
               p divides n /\ ~(p = 2 /\ ~(4 divides n)))"
      (REPEAT STRIP_TAC THEN MP_TAC (← SPECL [(← q r"n:num"), (← q r"p:num")] INDEX_DECOMPOSITION) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_GE_2)) THEN ASM_SIMP_TAC [(← ARITH_RULE (← q r"2 <= p ==> ~(p = 1)"))] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"m:num") STRIP_ASSUME_TAC) THEN MP_TAC (← SPECL [(← q r"p:num"), (← q r"index p n"), (← q r"m:num")] lemma) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [(← GSYM NUMBER_FIELD_RAMIFIED_DISCRIMINANT)] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num"), (← q r"p:num"), (← q r"index p n"), (← q r"m:num")] CYCLOTOMIC_FIELD_PRIME_DECOMPOSITION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"p:num")] NUMBER_FIELD_PRIME_DECOMPOSITION_Q) THEN ASM_REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY), IN_ELIM_THM] THEN DISCH_THEN ((X_CHOOSE_TAC (← q r"P:A->bool")) o (CONJUNCT1 o CONJUNCT2)) THEN ASM_MESON_TAC [])

  let CYCLOTOMIC_FIELD_TOTALLY_SPLIT ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    prove
      r"!(k:A ring) z n p.
          number_field k /\ z IN ring_carrier k /\
          ring_order k z = n /\ ~(n = 0) /\ subfield_generated k {z} = k /\
          prime p /\ ~(p divides n)
          ==> (totally_split (integer_ring,ring_of_integers k)
                 (ring_of_int k) (ideal_generated integer_ring {&p}) <=>
               (p == 1) (mod n))"
      (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_TOTALLY_SPLIT_CARD, (← GSYM ORDER_EQ_1)] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num")] CYCLOTOMIC_FIELD_DEGREE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num"), (← q r"p:num"), (← q r"0"), (← q r"n:num")] CYCLOTOMIC_FIELD_PRIME_DECOMPOSITION) THEN ASM_REWRITE_TAC [EXP, MULT_CLAUSES] THEN DISCH_THEN (MP_TAC o CONJUNCT2) THEN MP_TAC (← SPEC (← q r"n:num") PHI_EQ_0) THEN ASM_REWRITE_TAC [] THEN MATCH_ACCEPT_TAC (← MESON [MULT_CLAUSES, EQ_MULT_LCANCEL] (← q r"!c t f:num. ~(f = 0) ==> c * t = f ==> (c = f <=> t = 1)")))

  let CYCLOTOMIC_FIELD_PRIME_POWER_RAMIFIED ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let lemma1 := (← prove r"!(r:A ring) z p b.
        integral_domain r /\ z IN ring_carrier r /\ prime p /\
        ring_order r z = p EXP (b + 1)
        ==> ring_divides r (ring_sub r (ring_1 r) z) (ring_of_num r p)" (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"z:A"), (← q r"p:num"), (← q r"b + 1")] RING_ASSOCIATES_PRIME_POWER_ORDER) THEN ASM_REWRITE_TAC [ADD_EQ_0, ARITH_EQ, ring_associates] THEN DISCH_THEN (MP_TAC o CONJUNCT1) THEN MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] RING_DIVIDES_TRANS) THEN MP_TAC (← SPEC (← q r"p EXP (b + 1)") PHI_LOWERBOUND_1_STRONG) THEN ASM_SIMP_TAC [LE_1, EXP_EQ_0, PRIME_IMP_NZ] THEN SPEC_TAC ((← q r"phi(p EXP (b + 1))"), (← q r"n:num")) THEN INDUCT_TAC THEN REWRITE_TAC [ARITH, ring_pow] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN MATCH_MP_TAC RING_DIVIDES_RMUL THEN ASM_SIMP_TAC [RING_DIVIDES_REFL, RING_SUB, RING_1, RING_POW]))
    let lemma2 := (← prove r"!(k:A ring) a p.
        number_field k /\ prime p /\ a IN ring_carrier(ring_of_integers k) /\
        ring_setadd (ring_of_integers k) (ring_carrier(subring_generated k {a}))
          (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
        ring_carrier(ring_of_integers k)
        ==> poly_extend (integer_ring,k) (ring_of_int k) (\v. a)
              (cyclotomic_poly (integer_mod_ring p) 1) IN
            ring_carrier(ring_of_integers k) /\
            !j. ring_ideal (ring_of_integers k) j /\ ring_of_num k p IN j
                ==> (poly_extend (integer_ring,k) (ring_of_int k) (\v. a)
                       (cyclotomic_poly (integer_mod_ring p) 1) IN j <=>
                     ring_sub k (ring_1 k) a IN j)" (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"\v:1. (a:A)"), (← q r"cyclotomic_poly (integer_mod_ring p) 1")] POLY_EXTEND_RING_OF_INTEGERS) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [POLY_RING_INTEGER_MOD_RING_SUBSET, SUBSET, CYCLOTOMIC_POLY_IN_CARRIER], DISCH_THEN (ASSUME_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC []] THEN ABBREV_TAC (← q r"x = poly_extend (integer_ring,k:A ring) (ring_of_int k)
                      (\v. a) (cyclotomic_poly (integer_mod_ring p) 1)") THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_SUB) THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_1) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN REPEAT DISCH_TAC THEN X_GEN_TAC (← q r"j:A->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"p:num"), (← q r"j:A->bool")] DEDEKIND_KUMMER_EPIMORPHISM_Q) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"cyclotomic_poly integer_ring 1")) o CONJUNCT2)) THEN REWRITE_TAC [CYCLOTOMIC_POLY_IN_CARRIER, (← MATCH_MP CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE (← ISPEC (← q r"integer_mod_ring p") RING_HOMOMORPHISM_INTEGER_RING_OF_INT))] THEN ASM_REWRITE_TAC [] THEN SIMP_TAC [POLY_EXTEND_EVALUATE, RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN REWRITE_TAC [(← GSYM poly_eval), (← MATCH_MP CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE (← ISPEC (← q r"k:A ring") RING_HOMOMORPHISM_INTEGER_RING_OF_INT))] THEN ASM_SIMP_TAC [CYCLOTOMIC_POLY_1, POLY_EVAL_SUB, POLY_EVAL_VAR, POLY_EVAL_1, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_1, RING_COSET_EQ] THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_TAC THEN MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"j:A->bool")] IN_RING_IDEAL_SUB)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"a:A")] (← RING_RULE (← q r"!r x a:A. ring_sub r (ring_sub r x (ring_sub r a (ring_1 r))) x =
                ring_sub r (ring_1 r) a /\
                ring_sub r (ring_sub r x (ring_sub r a (ring_1 r)))
                  (ring_sub r (ring_1 r) a) = x"))) THEN ANTS_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ASM_MESON_TAC []]))
    let lemma3 := (← prove r"!(k:A ring) z p b.
        number_field k /\ z IN ring_carrier k /\ prime p /\
        ring_order k z = p EXP (b + 1) /\ subfield_generated k {z} = k
        ==> ideal_generated (ring_of_integers k)
              {ring_of_num k p,
               poly_extend (integer_ring,k) (ring_of_int k) (\v. z)
                 (cyclotomic_poly (integer_mod_ring p) 1)} =
            ideal_generated (ring_of_integers k) {ring_sub k (ring_1 k) z}" (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(z:A) IN ring_carrier(ring_of_integers k) /\
      ring_setadd (ring_of_integers k) (ring_carrier(subring_generated k {z}))
        (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
      ring_carrier(ring_of_integers k)") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"p EXP (b + 1)")] CYCLOTOMIC_FIELD_RING_OF_INTEGERS) THEN ASM_SIMP_TAC [EXP_EQ_0, PRIME_IMP_NZ] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [SUBRING_GENERATED_INC_GEN, IN_SING] THEN MATCH_MP_TAC RING_SETADD_RSUBSET THEN REWRITE_TAC [CARRIER_SUBRING_OF, IDEAL_GENERATED_SUBSET, IDEAL_GENERATED_NONEMPTY], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_of_num k p IN
      ideal_generated (ring_of_integers k) {ring_sub k (ring_1 k) (z:A)}") ASSUME_TAC THENL [MATCH_MP_TAC IN_IDEAL_GENERATED_SING THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"z:A"), (← q r"p:num"), (← q r"b:num")] lemma1) THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_RING_OF_INTEGERS, NUMBER_FIELD_IMP_FIELD, RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_ORDER_UNIQUE, RING_OF_INTEGERS] THEN X_GEN_TAC (← q r"d:num") THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"d:num")] RING_ORDER_DIVIDES) THEN ASM_REWRITE_TAC [] THEN MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_SUB) THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_1) THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_OF_NUM) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN REPEAT DISCH_TAC THEN MP_TAC (← SPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"p:num")] lemma2) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN REWRITE_TAC [(← GSYM SUBSET_ANTISYM_EQ), IDEALS_GENERATED_SUBSET] THEN REWRITE_TAC [SUBSET, IN_INTER, IN_INSERT, NOT_IN_EMPTY] THEN CONJ_TAC THEN X_GEN_TAC (← q r"w:A") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC)) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, IN_IDEAL_GENERATED_SELF] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"ideal_generated (ring_of_integers k)
        {ring_of_num k p,
         poly_extend (integer_ring,k) (ring_of_int k) (\v. z)
           (cyclotomic_poly (integer_mod_ring p) 1):A}"))) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_INC_GEN, IN_INSERT]))
    prove
      r"!(k:A ring) z p v.
          number_field k /\ z IN ring_carrier k /\ prime p /\
          ring_order k z = p EXP (v + 1) /\ subfield_generated k {z} = k
          ==> prime_ideal (ring_of_integers k)
                (ideal_generated (ring_of_integers k)
                   {ring_sub k (ring_1 k) z}) /\
              residue_degree (integer_ring,ring_of_integers k) (ring_of_int k)
                (ideal_generated (ring_of_integers k)
                   {ring_sub k (ring_1 k) z}) = 1 /\
              ideal_generated (ring_of_integers k) {ring_of_num k p} =
              ideal_pow (ring_of_integers k)
                (ideal_generated (ring_of_integers k) {ring_sub k (ring_1 k) z})
                (phi(p EXP (v + 1)))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← SPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"p:num"), (← q r"v:num")] lemma3) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_GE_2)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"p:num"), (← q r"v + 1"), (← q r"1"), (← q r"{cyclotomic_poly (integer_mod_ring p) 1}"), (← q r"\g. ideal_generated (ring_of_integers k)
                          {ring_of_num (k:A ring) p,
                           poly_extend (integer_ring,k) (ring_of_int k) (\v. z)
                             (g:(1->num)->int)}")] CYCLOTOMIC_FIELD_DEDEKIND_KUMMER) THEN ANTS_TAC THENL [ASM_SIMP_TAC [MULT_CLAUSES, DIVIDES_ONE, FINITE_SING, IN_SING, FORALL_UNWIND_THM2, CYCLOTOMIC_POLY_IN_CARRIER, CYCLOTOMIC_POLY_MONIC, RING_PRODUCT_SING, (← ARITH_RULE (← q r"2 <= p ==> ~(p = 1)"))] THEN MATCH_MP_TAC POLY_DEG_1_IMP_IRREDUCIBLE, ALL_TAC] THEN ASM_SIMP_TAC [IN_SING, FORALL_UNWIND_THM2, IDEAL_PRODUCT_SING, RING_IDEAL_IDEAL_POW, CYCLOTOMIC_POLY_DEG, CYCLOTOMIC_POLY_IN_CARRIER, FIELD_INTEGER_MOD_RING, (← GSYM TRIVIAL_RING_10), TRIVIAL_INTEGER_MOD_RING, PHI_1, (← ARITH_RULE (← q r"2 <= p ==> ~(p = 1)"))])

  -- @@RETURN BEGIN
  return { CYCLOTOMIC_FIELD_DEDEKIND_KUMMER, CYCLOTOMIC_FIELD_PRIME_DECOMPOSITION,
           CYCLOTOMIC_FIELD_RAMIFIED, CYCLOTOMIC_FIELD_TOTALLY_SPLIT,
           CYCLOTOMIC_FIELD_PRIME_POWER_RAMIFIED }
  -- @@RETURN END

end HolANT.CyclotomicSplit
