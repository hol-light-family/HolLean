/- ========================================================================= -/
/- ANT: Eisenstein polynomials                                             -/
/- ========================================================================= -/
/- File: HolANT/Eisenstein.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/eisenstein.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/anteisensteindiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/products.ml, ANT/algmisc.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, ANT/integral.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/prime_split.ml, ANT/norm_index.ml, ANT/discriminant.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/classgroup.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/relative_degree.ml, ANT/nf_valuation.ml, ANT/integrality.ml, ANT/dedekind_kummer.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.Eisenstein fills them).

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
import HolLibrary.Products
import HolANT.Algmisc
import HolLibrary.Matroids
import HolLibrary.Permutations
import HolLibrary.RingDet
import HolLibrary.FieldTheory
import HolANT.Integral
import HolANT.IdealArith
import HolANT.Dedekind
import HolLibrary.Isum
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolANT.DedekindStruct
import HolANT.IdealNorm
import HolANT.RingOfIntegers
import HolANT.PrimeSplit
import HolANT.NormIndex
import HolANT.Discriminant
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.Classgroup
import HolANT.TraceForm
import HolANT.RelativeSplit
import HolANT.RelativeDegree
import HolANT.NfValuation
import HolANT.Integrality
import HolANT.DedekindKummer

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.Algmisc
open HolANT.Integral
open HolANT.IdealArith
open HolANT.Dedekind
open HolANT.Zlattice
open HolANT.Numfield
open HolANT.DedekindStruct
open HolANT.IdealNorm
open HolANT.RingOfIntegers
open HolANT.PrimeSplit
open HolANT.NormIndex
open HolANT.Discriminant
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.Classgroup
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.RelativeDegree
open HolANT.NfValuation
open HolANT.Integrality
open HolANT.DedekindKummer

namespace HolANT.Eisenstein

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD1 COEFF_ABOVE_DEG COEFF_COMPOSE COEFF_POLY_VARPOW CONTRAPOS_THM
   DEDEKIND_IDEAL_SUBSET_POW_VALUATION DEDEKIND_IMP_INTEGRAL_DOMAIN
   DEDEKIND_IN_IDEAL_POW_VALUATION DEDEKIND_KUMMER_Q DEDEKIND_RING_OF_INTEGERS
   EMPTY_GSPEC EXTENSION FIELD_IMP_INTEGRAL_DOMAIN FIELD_IMP_NONTRIVIAL_RING
   FIELD_INTEGER_MOD_RING FINITE_NUMSEG_LT FINITE_SING FORALL_IN_IMAGE
   FUN_EQ_COEFF FUN_EQ_THM HAS_SIZE HAS_SIZE_FUNSPACE HAS_SIZE_IMAGE_INJ
   HAS_SIZE_NUMSEG_LT IDEAL_GENERATED_EQ_0 IDEAL_GENERATED_MINIMAL IDEAL_POW_1
   IDEAL_POW_ANTIMONO IDEAL_POW_SUC IDEAL_PRODUCT_SING IDEAL_VALUATION_EQ_0
   IDEAL_VALUATION_PRINCIPAL_MUL IDEAL_VALUATION_PRINCIPAL_POW IMAGE_CLAUSES
   INTEGER_MOD_RING_CHAR INTEGER_MOD_RING_CLAUSES INTEGER_RING
   INTEGRAL_DOMAIN_MUL_EQ_0 INTEGRAL_DOMAIN_POW_EQ_0 INT_ABS_NUM INT_DIVIDES_LE
   INT_ENTIRE INT_OF_NUM_EQ INT_OF_NUM_LT INT_POS INT_POW_2 INT_REM_EQ_SELF
   IN_DELETE IN_ELIM_THM IN_IDEAL_GENERATED_SELF IN_IDEAL_GENERATED_SING
   IN_IMAGE IN_RING_IDEAL_ADD IN_RING_IDEAL_LMUL IN_RING_IDEAL_NEG
   IN_RING_IDEAL_RMUL IN_RING_IDEAL_SUB IN_RING_IDEAL_SUM IN_SING IN_SUBRING_MUL
   IN_SUBRING_POW IN_SUBRING_SUM IN_UNIV LEFT_IMP_EXISTS_THM LE_ANTISYM LE_REFL
   LT LT_NZ MEMBER_NOT_EMPTY MONIC_POLY_VAR MONO_EXISTS MULT_CLAUSES NOT_IMP
   NOT_LT NUMBER_FIELD_DEGREE_POS NUMBER_FIELD_IMP_FIELD
   NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (NUM_OF_INT_OF_NUM POLY_DEG_VAR POLY_EXTEND_MONIC_UNIVARIATE POLY_EXTEND_VAR
   POLY_RING_CLAUSES PRIME_GE_2 PRIME_IDEAL_IMP_SUBSET PRIME_IMP_NZ
   PRIME_IMP_RING_IDEAL QUOTIENT_RING_CARRIER RAMIFICATION_INDEX_INTEGER_RING
   RAMIFICATION_INDEX_PRIME RING_0 RING_1 RING_ADD RING_ADD_LZERO RING_ADD_RZERO
   RING_COSET_EQ RING_HOMOMORPHISM_INTEGER_RING_OF_INT
   RING_IDEAL_IDEAL_GENERATED RING_IDEAL_IDEAL_POW RING_IDEAL_IMP_SUBSET
   RING_IRREDUCIBLE_POLY_VAR RING_MUL RING_MUL_IN_IDEAL_PROD RING_MUL_RID
   RING_MUL_RZERO RING_OF_INT RING_OF_INTEGERS RING_OF_INTEGERS_CARRIER
   RING_OF_INTEGERS_FINITE_QUOTIENT RING_OF_INTEGERS_IDEAL_NORM_INTEGER
   RING_OF_INTEGERS_SUBRING RING_OF_INTEGERS_SUBSET RING_OF_INT_0 RING_OF_INT_1
   RING_OF_INT_EQ_0 RING_OF_INT_EQ_0_CHAR_0 RING_OF_INT_IN_PRIME_IDEAL
   RING_OF_INT_IN_RING_OF_INTEGERS RING_OF_INT_MUL RING_OF_INT_OF_NUM
   RING_OF_INT_SUB RING_OF_NUM_IN_PRIME_IDEAL RING_POLYNOMIAL
   RING_POLYNOMIAL_VAR RING_POW RING_POW_ADD RING_POW_IN_PRIME_IDEAL
   RING_POW_ZERO RING_PRODUCT_SING RING_SUB_RDISTRIB RING_SUM RING_SUM_CLAUSES
   RING_SUM_DELETE RING_SUM_EQ RING_SUM_EQ_0 RING_SUM_LMUL
   RING_SUM_RING_OF_INTEGERS RING_SUM_SUB SING_SUBSET
   SUBRING_GENERATED_INDEX_COPRIME SUBRING_GENERATED_INT_LINCOMB SUBSET SUC_SUB1
   SURJECTIVE_IFF_INJECTIVE_GEN TRIVIAL_RING_10 ideal_norm int_divides
   integral_element monic num_WOP number_field poly_var ring_divides ring_pow
   ring_setadd : thm)
  deriving Inhabited

/-- What eisenstein.ml uses from Session besides theorems. -/
structure EisensteinDeps where
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
/- eisenstein.ml phrases from line 71 to 564                              -/
/- ---------------------------------------------------------------------- -/

structure Eisenstein01 where
  -- @@FIELDS
  NUMBER_FIELD_EISENSTEIN_VALUATION : thm
  NUMBER_FIELD_EISENSTEIN_POW : thm
  IDEAL_VALUATION_RING_OF_INT_COPRIME : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupEisenstein01 [HolBase] (D : EisensteinDeps) :
    ExceptT String IO Eisenstein01 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INTEGER_RULE, RING_RULE,
        SET_TAC, .. } := D
  let { ADD1, CONTRAPOS_THM, DEDEKIND_IMP_INTEGRAL_DOMAIN,
        DEDEKIND_IN_IDEAL_POW_VALUATION, DEDEKIND_RING_OF_INTEGERS, EMPTY_GSPEC,
        FIELD_IMP_NONTRIVIAL_RING, FINITE_NUMSEG_LT, IDEAL_GENERATED_EQ_0,
        IDEAL_GENERATED_MINIMAL, IDEAL_POW_1, IDEAL_POW_ANTIMONO, IDEAL_POW_SUC,
        IDEAL_VALUATION_EQ_0, IDEAL_VALUATION_PRINCIPAL_MUL,
        IDEAL_VALUATION_PRINCIPAL_POW, INTEGRAL_DOMAIN_POW_EQ_0, INT_ENTIRE,
        INT_OF_NUM_EQ, INT_POW_2, IN_DELETE, IN_ELIM_THM, IN_IDEAL_GENERATED_SELF,
        IN_IDEAL_GENERATED_SING, IN_RING_IDEAL_ADD, IN_RING_IDEAL_NEG,
        IN_RING_IDEAL_RMUL, IN_RING_IDEAL_SUM, IN_SUBRING_MUL, IN_SUBRING_POW,
        IN_SUBRING_SUM, LE_ANTISYM, LE_REFL, LT, LT_NZ, MONO_EXISTS, NOT_LT,
        NUMBER_FIELD_IMP_FIELD, .. } := D.core1
  let { POLY_EXTEND_MONIC_UNIVARIATE, PRIME_IDEAL_IMP_SUBSET, PRIME_IMP_NZ,
        PRIME_IMP_RING_IDEAL, RAMIFICATION_INDEX_INTEGER_RING, RING_0, RING_1,
        RING_ADD_LZERO, RING_ADD_RZERO, RING_HOMOMORPHISM_INTEGER_RING_OF_INT,
        RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_POW, RING_MUL,
        RING_MUL_IN_IDEAL_PROD, RING_MUL_RID, RING_MUL_RZERO, RING_OF_INT,
        RING_OF_INTEGERS, RING_OF_INTEGERS_CARRIER, RING_OF_INTEGERS_SUBRING,
        RING_OF_INTEGERS_SUBSET, RING_OF_INT_EQ_0_CHAR_0, RING_OF_INT_IN_PRIME_IDEAL,
        RING_OF_INT_IN_RING_OF_INTEGERS, RING_OF_INT_MUL, RING_OF_INT_OF_NUM,
        RING_OF_NUM_IN_PRIME_IDEAL, RING_POW, RING_POW_IN_PRIME_IDEAL, RING_POW_ZERO,
        RING_SUM, RING_SUM_CLAUSES, RING_SUM_DELETE, RING_SUM_EQ_0,
        RING_SUM_RING_OF_INTEGERS, SING_SUBSET, SUBSET, TRIVIAL_RING_10, int_divides,
        integral_element, number_field, ring_divides, ring_pow, .. } := D.core2
  -- @@SCOPE END

  let NUMBER_FIELD_EISENSTEIN_VALUATION ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let lemma := (← prove r"!r x y z:A.
        x IN ring_carrier r /\ y IN ring_carrier r /\ z IN ring_carrier r /\
        ring_add r x (ring_add r y z) = ring_0 r
        ==> x = ring_neg r (ring_add r y z) /\
            y = ring_neg r (ring_add r x z)" (REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do if ← (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); pure (is_eq z5)) then (do let z10 ← (q r"ring_0 r:A"); let z9 ← (do let z7 ← (do let z8 ← (pure th); pure (concl z8)); liftExcept (rhs z7)); pure (z9 == z10)) else pure false)))) THENL [MATCH_MP_TAC (← RING_RULE (← q r"ring_add r x (ring_add r y z) = ring_0 r
        ==> x = ring_neg r (ring_add r y (z:A))")), MATCH_MP_TAC (← RING_RULE (← q r"ring_add r x (ring_add r y z) = ring_0 r
        ==> y = ring_neg r (ring_add r x (z:A))"))] THEN ASM_REWRITE_TAC []))
    prove
      r"!(k:A ring) a m p P.
          number_field k /\ a IN ring_carrier k /\
          m IN ring_carrier(poly_ring integer_ring (:1)) /\
          monic integer_ring m /\
          poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m = ring_0 k /\
          prime p /\
          (!i. i < poly_deg integer_ring m ==> &p divides coeff i m) /\
          ~(&p pow 2 divides coeff 0 m) /\
          prime_ideal (ring_of_integers k) P /\ ring_of_num k p IN P
          ==> a IN ring_carrier(ring_of_integers k) /\ ~(a = ring_0 k) /\
              1 <= ideal_valuation (ring_of_integers k) P
                     (ideal_generated (ring_of_integers k) {a}) /\
              poly_deg integer_ring m *
              ideal_valuation (ring_of_integers k) P
                (ideal_generated (ring_of_integers k) {a}) =
              ramification_index (integer_ring,ring_of_integers k)
                (ring_of_int k) P"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_RING_OF_INTEGERS)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FIELD_IMP_NONTRIVIAL_RING)) THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM, integral_element] THEN ASM_MESON_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"n = poly_deg integer_ring (m:(1->num)->int)") THEN SUBGOAL_THEN (← q r"ring_carrier(ring_of_integers k) subring_of (k:A ring)") ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_SUBRING], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers k) (P:A->bool)") ASSUME_TAC THENL [ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(ring_of_num k p = ring_0 (k:A ring))") ASSUME_TAC THENL [REWRITE_TAC [(← GSYM RING_OF_INT_OF_NUM)] THEN ASM_SIMP_TAC [RING_OF_INT_EQ_0_CHAR_0, INT_OF_NUM_EQ, PRIME_IMP_NZ], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(P = {ring_0 (ring_of_integers k:A ring)})") ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS] THEN ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ramification_index (integer_ring,ring_of_integers k) (ring_of_int k) P =
    ideal_valuation (ring_of_integers k) P
      (ideal_generated (ring_of_integers k) {ring_of_num k p:A})") SUBST1_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool")] RAMIFICATION_INDEX_INTEGER_RING) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"p:num")] RING_OF_NUM_IN_PRIME_IDEAL) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN SIMP_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"e = ideal_valuation (ring_of_integers k) P
          (ideal_generated (ring_of_integers k) {ring_of_num k p:A})") THEN SUBGOAL_THEN (← q r"(ring_of_num k p:A) IN ideal_pow (ring_of_integers k) P e") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"ring_of_num k p:A"), (← q r"e:num")] DEDEKIND_IN_IDEAL_POW_VALUATION) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS, (← GSYM RING_OF_INT_OF_NUM), RING_OF_INT_IN_RING_OF_INTEGERS] THEN ASM_REWRITE_TAC [RING_OF_INT_OF_NUM, LE_REFL], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_add k (ring_pow k a n)
      (ring_sum k {i | i < n}
         (\i. ring_mul k (ring_of_int k (coeff i m)) (ring_pow k a i))) =
    ring_0 (k:A ring)") ASSUME_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z221 ← (do let z222 ← (pure th); pure (concl z222)); pure (is_eq z221)) then (do let z226 ← (q r"ring_0 k:A"); let z225 ← (do let z223 ← (do let z224 ← (pure th); pure (concl z224)); liftExcept (rhs z223)); pure (z225 == z226)) else pure false))))) THEN EXPAND_TAC "n" THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC POLY_EXTEND_MONIC_UNIVARIATE THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(n = 0)") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"ring_add k (ring_pow k a 0)
        (ring_sum k {i | i < 0}
           (\i. ring_mul k (ring_of_int k (coeff i m)) (ring_pow k a i))) =
      ring_0 (k:A ring)") THEN REWRITE_TAC [LT, EMPTY_GSPEC, RING_SUM_CLAUSES, ring_pow] THEN ASM_SIMP_TAC [RING_ADD_RZERO, RING_1, (← GSYM TRIVIAL_RING_10)], ALL_TAC] THEN ABBREV_TAC (← q r"S = ring_sum k ({i | i < n} DELETE 0)
          (\i. ring_mul k (ring_of_int k (coeff i m))
                 (ring_pow k (a:A) i))") THEN SUBGOAL_THEN (← q r"ring_add k (ring_pow k a n) (ring_add k (ring_of_int k (coeff 0 m)) S) =
    ring_0 (k:A ring)") ASSUME_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z210 ← (do let z211 ← (pure th); pure (concl z211)); pure (is_eq z210)) then (do let z215 ← (q r"ring_0 k:A"); let z214 ← (do let z212 ← (do let z213 ← (pure th); pure (concl z213)); liftExcept (rhs z212)); pure (z214 == z215)) else pure false))))) THEN AP_TERM_TAC THEN EXPAND_TAC "S" THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"\i. ring_mul k (ring_of_int k (coeff i (m:(1->num)->int)))
                      (ring_pow k (a:A) i)"), (← q r"{i:num | i < n}"), (← q r"0")] RING_SUM_DELETE) THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, LT_NZ, RING_MUL, RING_OF_INT, RING_POW] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [ring_pow] THEN ASM_SIMP_TAC [RING_MUL_RID, RING_OF_INT] THEN MATCH_MP_TAC (← RING_RULE (← q r"ring_add r x (ring_sub r y x) = (y:A)")) THEN ASM_SIMP_TAC [RING_OF_INT, RING_SUM], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. i < n
        ==> ring_mul k (ring_of_int k (coeff i m)) (ring_pow k a i) IN
            ideal_generated (ring_of_integers k) {ring_of_num k p:A}") ASSUME_TAC THENL [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"i:num")) o (checkM (fun th => (do if ← (do let z191 ← (do let z192 ← (pure th); pure (concl z192)); pure (is_forall z191)) then (do let z193 ← (do let z194 ← (pure th); pure (concl z194)); canM (fun z195 => (do let z196 ← (pure z195); find_termM (fun z197 => (do let z199 ← (pure z197); let z198 ← (q r"(divides):int->int->bool"); pure (z198 == z199))) z196)) z193) else pure false))))) THEN ASM_REWRITE_TAC [int_divides] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"t:int") SUBST1_TAC) THEN MATCH_MP_TAC IN_IDEAL_GENERATED_SING THEN REWRITE_TAC [ring_divides, RING_OF_INTEGERS] THEN REWRITE_TAC [RING_OF_INT_MUL, (← GSYM RING_OF_INT_OF_NUM)] THEN ASM_SIMP_TAC [IN_SUBRING_MUL, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS] THEN EXISTS_TAC (← q r"ring_mul k (ring_of_int k t) (ring_pow k a i):A") THEN ASM_SIMP_TAC [IN_SUBRING_MUL, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS] THEN MATCH_MP_TAC (← RING_RULE (← q r"ring_mul r (ring_mul r x y) z = ring_mul r x (ring_mul r y (z:A))")) THEN ASM_SIMP_TAC [RING_OF_INT, RING_POW], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_generated (ring_of_integers k) {ring_of_num k p:A} SUBSET P") ASSUME_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_of_int k (coeff 0 m) IN (P:A->bool)") ASSUME_TAC THENL [FIRST_X_ASSUM (MATCH_MP_TAC o (REWRITE_RULE [SUBSET])) THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"0")) o (checkM (fun th => (do if ← (do let z174 ← (do let z175 ← (pure th); pure (concl z175)); pure (is_forall z174)) then (do let z176 ← (do let z177 ← (pure th); pure (concl z177)); canM (fun z178 => (do let z179 ← (pure z178); find_termM (fun z180 => (do let z182 ← (pure z180); let z181 ← (q r"ideal_generated:(A ring)->(A->bool)->A->bool"); pure (z181 == z182))) z179)) z176) else pure false))))) THEN ASM_REWRITE_TAC [LT_NZ, ring_pow] THEN ASM_SIMP_TAC [RING_MUL_RID, RING_OF_INT], ALL_TAC] THEN SUBGOAL_THEN (← q r"(S:A) IN P") ASSUME_TAC THENL [EXPAND_TAC "S" THEN wPart lhand (rand o rand) RING_SUM_RING_OF_INTEGERS THEN ANTS_TAC THENL [REWRITE_TAC [IN_DELETE, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [IN_SUBRING_MUL, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC IN_RING_IDEAL_SUM THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [IN_DELETE, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MATCH_MP_TAC o ((REWRITE_RULE [SUBSET]) o (checkM (fun th => (do if ← (do let z167 ← (do let z168 ← (pure th); pure (concl z168)); pure (is_comb z167)) then (do let z172 ← (q r"P:A->bool"); let z171 ← (do let z169 ← (do let z170 ← (pure th); pure (concl z170)); liftExcept (rand z169)); pure (z171 == z172)) else pure false))))) THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_of_int k (coeff 0 m) IN ring_carrier(ring_of_integers k) /\
    (S:A) IN ring_carrier(ring_of_integers k) /\
    ring_pow k a n IN ring_carrier(ring_of_integers k)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS] THEN ASM_MESON_TAC [PRIME_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_of_int k (coeff 0 m) IN ring_carrier k /\
    (S:A) IN ring_carrier k /\ ring_pow k a n IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"(a:A) IN P") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"a:A"), (← q r"n:num")] RING_POW_IN_PRIME_IDEAL) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_pow k a n:A"), (← q r"ring_of_int k (coeff 0 m):A"), (← q r"S:A")] lemma) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (SUBST1_TAC o CONJUNCT1)] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"ring_add k (ring_of_int k (coeff 0 m)) (S:A)")] IN_RING_IDEAL_NEG) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"ring_of_int k (coeff 0 m):A"), (← q r"S:A")] IN_RING_IDEAL_ADD) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(S:A) IN ideal_pow (ring_of_integers k) P (e + 1)") ASSUME_TAC THENL [EXPAND_TAC "S" THEN wPart lhand (rand o rand) RING_SUM_RING_OF_INTEGERS THEN ANTS_TAC THENL [REWRITE_TAC [IN_DELETE, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [IN_SUBRING_MUL, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC IN_RING_IDEAL_SUM THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN REWRITE_TAC [IN_DELETE, IN_ELIM_THM] THEN X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"i:num")) o (checkM (fun th => (do if ← (do let z133 ← (do let z134 ← (pure th); pure (concl z134)); pure (is_forall z133)) then (do let z135 ← (do let z136 ← (pure th); pure (concl z136)); canM (fun z137 => (do let z138 ← (pure z137); find_termM (fun z139 => (do let z141 ← (pure z139); let z140 ← (q r"(divides):int->int->bool"); pure (z140 == z141))) z138)) z135) else pure false))))) THEN ASM_REWRITE_TAC [int_divides] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"t:int") SUBST1_TAC) THEN SUBGOAL_THEN (← q r"ring_mul k (ring_of_int k (&p * t)) (ring_pow k a i) =
      ring_mul k a (ring_mul k (ring_of_num k p)
        (ring_mul k (ring_of_int k t) (ring_pow k a (i - 1)))):A") SUBST1_TAC THENL [SUBGOAL_THEN (← q r"i = SUC(i - 1)") (fun th => GEN_REWRITE_TAC (LAND_CONV o (RAND_CONV o RAND_CONV)) [th]) THENL [ASM_ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [ring_pow, RING_OF_INT_MUL, (← GSYM RING_OF_INT_OF_NUM)] THEN MATCH_MP_TAC (← RING_RULE (← q r"ring_mul r (ring_mul r p t) (ring_mul r a x) =
        ring_mul r a (ring_mul r p (ring_mul r t (x:A)))")) THEN ASM_SIMP_TAC [RING_OF_INT, RING_POW], ALL_TAC] THEN REWRITE_TAC [(← GSYM ADD1), IDEAL_POW_SUC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"ideal_pow (ring_of_integers k) P e:A->bool"), (← q r"a:A"), (← q r"ring_mul k (ring_of_num k p)
                      (ring_mul k (ring_of_int k t)
                         (ring_pow k a (i - 1))):A")] RING_MUL_IN_IDEAL_PROD) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ring_mul k (ring_of_int k t) (ring_pow k a (i - 1)):A IN
      ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [ASM_SIMP_TAC [IN_SUBRING_MUL, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS], ALL_TAC] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ideal_pow (ring_of_integers k) P e:A->bool"), (← q r"ring_of_num k p:A"), (← q r"ring_mul k (ring_of_int k t)
                        (ring_pow k a (i - 1)):A")] IN_RING_IDEAL_RMUL) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS, RING_IDEAL_IDEAL_POW], MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [(← GSYM RING_OF_INT_OF_NUM), RING_OF_INT_IN_RING_OF_INTEGERS]], ALL_TAC] THEN SUBGOAL_THEN (← q r"?u. coeff 0 (m:(1->num)->int) = &p * u /\ ~(&p divides u)") STRIP_ASSUME_TAC THENL [FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"0")) o (checkM (fun th => (do if ← (do let z102 ← (do let z103 ← (pure th); pure (concl z103)); pure (is_forall z102)) then (do let z104 ← (do let z105 ← (pure th); pure (concl z105)); canM (fun z106 => (do let z107 ← (pure z106); find_termM (fun z108 => (do let z110 ← (pure z108); let z109 ← (q r"(divides):int->int->bool"); pure (z109 == z110))) z107)) z104) else pure false))))) THEN ASM_REWRITE_TAC [LT_NZ, int_divides] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"u:int") THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"~(&p pow 2 divides coeff 0 (m:(1->num)->int))") THEN ASM_REWRITE_TAC [INT_POW_2, CONTRAPOS_THM] THEN CONV_TAC INTEGER_RULE, ALL_TAC] THEN SUBGOAL_THEN (← q r"~(u:int = &0)") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~((&p:int) divides &0)") THEN REWRITE_TAC [(← INTEGER_RULE (← q r"!d:int. d divides &0"))], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(ring_of_int k u:A = ring_0 k) /\ ~(ring_of_int k u:A IN P)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_OF_INT_EQ_0_CHAR_0] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"p:num")] RING_OF_INT_IN_PRIME_IDEAL) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_valuation (ring_of_integers k) P
      (ideal_generated (ring_of_integers k)
         {ring_of_int k (coeff 0 m):A}) = e") ASSUME_TAC THENL [ASM_REWRITE_TAC [RING_OF_INT_MUL, (← GSYM RING_OF_INT_OF_NUM)] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"ring_of_int k (&p):A"), (← q r"ring_of_int k u:A")] IDEAL_VALUATION_PRINCIPAL_MUL) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS, RING_OF_INT_IN_RING_OF_INTEGERS] THEN ASM_REWRITE_TAC [RING_OF_INT_OF_NUM] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC (← ARITH_RULE (← q r"y = 0 ==> e + y = e")) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"ideal_generated (ring_of_integers k) {ring_of_int k u:A}")] IDEAL_VALUATION_EQ_0) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0, RING_OF_INTEGERS, RING_OF_INT_IN_RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN UNDISCH_TAC (← q r"~(ring_of_int k u:A IN P)") THEN REWRITE_TAC [] THEN FIRST_X_ASSUM (MATCH_MP_TAC o (REWRITE_RULE [SUBSET])) THEN REWRITE_TAC [IN_IDEAL_GENERATED_SELF, RING_OF_INT_IN_RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(ring_of_int k (coeff 0 m) = ring_0 (k:A ring))") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_OF_INT_EQ_0_CHAR_0, INT_ENTIRE, INT_OF_NUM_EQ, PRIME_IMP_NZ], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(a = ring_0 (k:A ring))") ASSUME_TAC THENL [DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_pow k a n = ring_0 (k:A ring) /\ S = ring_0 k") STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC [RING_POW_ZERO] THEN EXPAND_TAC "S" THEN MATCH_MP_TAC RING_SUM_EQ_0 THEN REWRITE_TAC [IN_DELETE, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [RING_POW_ZERO, RING_MUL_RZERO, RING_OF_INT], ALL_TAC] THEN UNDISCH_TAC (← q r"~(ring_of_int k (coeff 0 m) = ring_0 (k:A ring))") THEN REWRITE_TAC [] THEN UNDISCH_TAC (← q r"ring_add k (ring_pow k a n) (ring_add k (ring_of_int k (coeff 0 m)) S) =
      ring_0 (k:A ring)") THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [RING_ADD_LZERO, RING_ADD_RZERO, RING_0, RING_OF_INT], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"w = ideal_valuation (ring_of_integers k) P
          (ideal_generated (ring_of_integers k) {a:A})") THEN SUBGOAL_THEN (← q r"1 <= w") ASSUME_TAC THENL [EXPAND_TAC "w" THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"a:A"), (← q r"1")] DEDEKIND_IN_IDEAL_POW_VALUATION) THEN ASM_SIMP_TAC [RING_OF_INTEGERS, IDEAL_POW_1], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ideal_valuation (ring_of_integers k) P
      (ideal_generated (ring_of_integers k) {ring_pow k a n:A}) = n * w") ASSUME_TAC THENL [EXPAND_TAC "w" THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"a:A"), (← q r"n:num")] IDEAL_VALUATION_PRINCIPAL_POW) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(ring_pow k a n = ring_0 (k:A ring))") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"a:A"), (← q r"n:num")] INTEGRAL_DOMAIN_POW_EQ_0) THEN ASM_SIMP_TAC [RING_OF_INTEGERS, DEDEKIND_IMP_INTEGRAL_DOMAIN], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x j. x IN ring_carrier(ring_of_integers k) /\ ~(x = ring_0 k)
          ==> (x IN ideal_pow (ring_of_integers k) P j <=>
               j <= ideal_valuation (ring_of_integers k) P
                      (ideal_generated (ring_of_integers k) {x:A}))") (LABEL_TAC "mem") THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC DEDEKIND_IN_IDEAL_POW_VALUATION THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN REWRITE_TAC [(← GSYM LE_ANTISYM), (← GSYM NOT_LT)] THEN CONJ_TAC THEN DISCH_TAC THENL [SUBGOAL_THEN (← q r"ring_pow k (a:A) n IN ideal_pow (ring_of_integers k) P (e + 1)") ASSUME_TAC THENL [USE_THEN "mem" (fun th => ASM_SIMP_TAC [th]) THEN ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_of_int k (coeff 0 m):A IN
      ideal_pow (ring_of_integers k) P (e + 1)") MP_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_pow k a n:A"), (← q r"ring_of_int k (coeff 0 m):A"), (← q r"S:A")] lemma) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (SUBST1_TAC o CONJUNCT2)] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ideal_pow (ring_of_integers k) P (e + 1):A->bool"), (← q r"ring_add k (ring_pow k a n) (S:A)")] IN_RING_IDEAL_NEG) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ideal_pow (ring_of_integers k) P (e + 1):A->bool"), (← q r"ring_pow k a n:A"), (← q r"S:A")] IN_RING_IDEAL_ADD) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS, RING_IDEAL_IDEAL_POW] THEN SIMP_TAC [], USE_THEN "mem" (fun th => ASM_SIMP_TAC [th]) THEN ARITH_TAC], SUBGOAL_THEN (← q r"ring_pow k (a:A) n IN ideal_pow (ring_of_integers k) P e") MP_TAC THENL [ALL_TAC, USE_THEN "mem" (fun th => ASM_SIMP_TAC [th]) THEN ASM_ARITH_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_pow k a n:A"), (← q r"ring_of_int k (coeff 0 m):A"), (← q r"S:A")] lemma) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (SUBST1_TAC o CONJUNCT1)] THEN SUBGOAL_THEN (← q r"(S:A) IN ideal_pow (ring_of_integers k) P e /\
      ring_of_int k (coeff 0 m) IN ideal_pow (ring_of_integers k) P e") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"e:num"), (← q r"e + 1")] IDEAL_POW_ANTIMONO) THEN ASM_SIMP_TAC [PRIME_IDEAL_IMP_SUBSET, (← ARITH_RULE (← q r"e <= e + 1"))] THEN ASM SET_TAC [], USE_THEN "mem" (fun th => ASM_SIMP_TAC [th, LE_REFL])], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ideal_pow (ring_of_integers k) P e:A->bool"), (← q r"ring_add k (ring_of_int k (coeff 0 m)) (S:A)")] IN_RING_IDEAL_NEG) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ideal_pow (ring_of_integers k) P e:A->bool"), (← q r"ring_of_int k (coeff 0 m):A"), (← q r"S:A")] IN_RING_IDEAL_ADD) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS, RING_IDEAL_IDEAL_POW] THEN SIMP_TAC []])

  let NUMBER_FIELD_EISENSTEIN_POW ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    prove
      r"!(k:A ring) a m p.
          number_field k /\ a IN ring_carrier k /\
          m IN ring_carrier(poly_ring integer_ring (:1)) /\
          monic integer_ring m /\
          poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m = ring_0 k /\
          (!i. i < poly_deg integer_ring m ==> &p divides coeff i m)
          ==> a IN ring_carrier(ring_of_integers k) /\
              ring_pow k a (poly_deg integer_ring m) IN
              ideal_generated (ring_of_integers k) {ring_of_num k p}"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM, integral_element] THEN ASM_MESON_TAC [], ASM_REWRITE_TAC []] THEN ABBREV_TAC (← q r"n = poly_deg integer_ring (m:(1->num)->int)") THEN SUBGOAL_THEN (← q r"ring_carrier(ring_of_integers k) subring_of (k:A ring)") ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_SUBRING], ALL_TAC] THEN ABBREV_TAC (← q r"S = ring_sum k {i | i < n}
            (\i. ring_mul k (ring_of_int k (coeff i m))
                   (ring_pow k (a:A) i))") THEN SUBGOAL_THEN (← q r"(S:A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [EXPAND_TAC "S" THEN MATCH_MP_TAC IN_SUBRING_SUM THEN ASM_SIMP_TAC [IN_SUBRING_MUL, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_pow k a n = ring_neg k (S:A)") SUBST1_TAC THENL [MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"k:A ring"), (← q r"ring_of_int k:int->A"), (← q r"a:A"), (← q r"m:(1->num)->int")] POLY_EXTEND_MONIC_UNIVARIATE) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN MATCH_MP_TAC (← RING_RULE (← q r"ring_0 r = ring_add r x y ==> x = ring_neg r (y:A)")) THEN ASM_SIMP_TAC [RING_POW] THEN ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ideal_generated (ring_of_integers k) {ring_of_num k p:A}"), (← q r"S:A")] IN_RING_IDEAL_NEG) THEN REWRITE_TAC [RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED] THEN DISCH_THEN MATCH_MP_TAC THEN EXPAND_TAC "S" THEN wPart lhand (rand o rand) RING_SUM_RING_OF_INTEGERS THEN ANTS_TAC THENL [REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [IN_SUBRING_MUL, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC IN_RING_IDEAL_SUM THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, IN_ELIM_THM] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"i:num")) o (checkM (fun th => (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); pure (is_forall z2)) then (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); canM (fun z6 => (do let z7 ← (pure z6); find_termM (fun z8 => (do let z10 ← (pure z8); let z9 ← (q r"(divides):int->int->bool"); pure (z9 == z10))) z7)) z4) else pure false))))) THEN ASM_REWRITE_TAC [int_divides] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"t:int") SUBST1_TAC) THEN MATCH_MP_TAC IN_IDEAL_GENERATED_SING THEN REWRITE_TAC [ring_divides, RING_OF_INTEGERS] THEN REWRITE_TAC [RING_OF_INT_MUL, (← GSYM RING_OF_INT_OF_NUM)] THEN ASM_SIMP_TAC [IN_SUBRING_MUL, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS] THEN EXISTS_TAC (← q r"ring_mul k (ring_of_int k t) (ring_pow k a i):A") THEN ASM_SIMP_TAC [IN_SUBRING_MUL, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS] THEN MATCH_MP_TAC (← RING_RULE (← q r"ring_mul r (ring_mul r x y) z = ring_mul r x (ring_mul r y (z:A))")) THEN ASM_SIMP_TAC [RING_OF_INT, RING_POW] THEN ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET])

  let IDEAL_VALUATION_RING_OF_INT_COPRIME ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    prove
      r"!(k:A ring) P p u.
          number_field k /\ prime p /\
          prime_ideal (ring_of_integers k) P /\ ring_of_num k p IN P /\
          ~(&p divides u)
          ==> ~(ring_of_int k u = ring_0 k) /\
              ideal_valuation (ring_of_integers k) P
                (ideal_generated (ring_of_integers k) {ring_of_int k u}) = 0"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN SUBGOAL_THEN (← q r"~(u:int = &0)") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~((&p:int) divides &0)") THEN REWRITE_TAC [(← INTEGER_RULE (← q r"!d:int. d divides &0"))], ALL_TAC] THEN ASM_SIMP_TAC [RING_OF_INT_EQ_0_CHAR_0] THEN SUBGOAL_THEN (← q r"~(ring_of_int k u:A IN P)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"p:num")] RING_OF_INT_IN_PRIME_IDEAL) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(ring_of_num k p = ring_0 (k:A ring))") ASSUME_TAC THENL [REWRITE_TAC [(← GSYM RING_OF_INT_OF_NUM)] THEN ASM_SIMP_TAC [RING_OF_INT_EQ_0_CHAR_0, INT_OF_NUM_EQ, PRIME_IMP_NZ], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"ideal_generated (ring_of_integers k) {ring_of_int k u:A}")] IDEAL_VALUATION_EQ_0) THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0, RING_OF_INTEGERS, RING_OF_INT_IN_RING_OF_INTEGERS, RING_OF_INT_EQ_0_CHAR_0] THEN ANTS_TAC THENL [ASM SET_TAC [], DISCH_THEN SUBST1_TAC] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"~(ring_of_int k u:A IN P)") THEN REWRITE_TAC [] THEN FIRST_X_ASSUM (MATCH_MP_TAC o (REWRITE_RULE [SUBSET])) THEN REWRITE_TAC [IN_IDEAL_GENERATED_SELF, RING_OF_INT_IN_RING_OF_INTEGERS])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_EISENSTEIN_VALUATION, NUMBER_FIELD_EISENSTEIN_POW,
           IDEAL_VALUATION_RING_OF_INT_COPRIME }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- eisenstein.ml phrases from line 606 to 1170                            -/
/- ---------------------------------------------------------------------- -/

structure Eisenstein02 where
  -- @@FIELDS
  NUMBER_FIELD_EISENSTEIN_INDEPENDENT : thm
  NUMBER_FIELD_EISENSTEIN_INDEX_COPRIME : thm
  NUMBER_FIELD_EISENSTEIN : thm
  NUMBER_FIELD_EISENSTEIN_INDEX : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupEisenstein02 [HolBase] (D : EisensteinDeps) (BEisenstein01 : Eisenstein01) :
    ExceptT String IO Eisenstein02 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INT_ARITH_TAC, MESON,
        MESON_TAC, RING_RULE, SET_TAC, TAUT, .. } := D
  let { COEFF_ABOVE_DEG, COEFF_COMPOSE, COEFF_POLY_VARPOW,
        DEDEKIND_IDEAL_SUBSET_POW_VALUATION, DEDEKIND_IMP_INTEGRAL_DOMAIN,
        DEDEKIND_IN_IDEAL_POW_VALUATION, DEDEKIND_KUMMER_Q, DEDEKIND_RING_OF_INTEGERS,
        EXTENSION, FIELD_IMP_INTEGRAL_DOMAIN, FIELD_IMP_NONTRIVIAL_RING,
        FIELD_INTEGER_MOD_RING, FINITE_NUMSEG_LT, FINITE_SING, FORALL_IN_IMAGE,
        FUN_EQ_COEFF, FUN_EQ_THM, HAS_SIZE, HAS_SIZE_FUNSPACE, HAS_SIZE_IMAGE_INJ,
        HAS_SIZE_NUMSEG_LT, IDEAL_GENERATED_EQ_0, IDEAL_PRODUCT_SING,
        IDEAL_VALUATION_PRINCIPAL_MUL, IDEAL_VALUATION_PRINCIPAL_POW, IMAGE_CLAUSES,
        INTEGER_MOD_RING_CHAR, INTEGER_MOD_RING_CLAUSES, INTEGER_RING,
        INTEGRAL_DOMAIN_MUL_EQ_0, INTEGRAL_DOMAIN_POW_EQ_0, INT_ABS_NUM,
        INT_DIVIDES_LE, INT_OF_NUM_EQ, INT_OF_NUM_LT, INT_POS, INT_REM_EQ_SELF,
        IN_DELETE, IN_ELIM_THM, IN_IDEAL_GENERATED_SELF, IN_IDEAL_GENERATED_SING,
        IN_IMAGE, IN_RING_IDEAL_LMUL, IN_RING_IDEAL_NEG, IN_RING_IDEAL_RMUL,
        IN_RING_IDEAL_SUB, IN_RING_IDEAL_SUM, IN_SING, IN_SUBRING_MUL, IN_SUBRING_POW,
        IN_SUBRING_SUM, IN_UNIV, LEFT_IMP_EXISTS_THM, LE_REFL, MEMBER_NOT_EMPTY,
        MONIC_POLY_VAR, MULT_CLAUSES, NOT_IMP, NUMBER_FIELD_DEGREE_POS,
        NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q,
        NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q, .. } := D.core1
  let { NUM_OF_INT_OF_NUM, POLY_DEG_VAR, POLY_EXTEND_VAR, POLY_RING_CLAUSES,
        PRIME_GE_2, PRIME_IMP_NZ, QUOTIENT_RING_CARRIER, RAMIFICATION_INDEX_PRIME,
        RING_ADD, RING_COSET_EQ, RING_HOMOMORPHISM_INTEGER_RING_OF_INT,
        RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_POW, RING_IDEAL_IMP_SUBSET,
        RING_IRREDUCIBLE_POLY_VAR, RING_MUL, RING_OF_INT, RING_OF_INTEGERS,
        RING_OF_INTEGERS_FINITE_QUOTIENT, RING_OF_INTEGERS_IDEAL_NORM_INTEGER,
        RING_OF_INTEGERS_SUBRING, RING_OF_INTEGERS_SUBSET, RING_OF_INT_0,
        RING_OF_INT_1, RING_OF_INT_EQ_0, RING_OF_INT_EQ_0_CHAR_0,
        RING_OF_INT_IN_RING_OF_INTEGERS, RING_OF_INT_MUL, RING_OF_INT_OF_NUM,
        RING_OF_INT_SUB, RING_POLYNOMIAL, RING_POLYNOMIAL_VAR, RING_POW, RING_POW_ADD,
        RING_PRODUCT_SING, RING_SUB_RDISTRIB, RING_SUM, RING_SUM_DELETE, RING_SUM_EQ,
        RING_SUM_LMUL, RING_SUM_RING_OF_INTEGERS, RING_SUM_SUB,
        SUBRING_GENERATED_INDEX_COPRIME, SUBRING_GENERATED_INT_LINCOMB, SUBSET,
        SUC_SUB1, SURJECTIVE_IFF_INJECTIVE_GEN, TRIVIAL_RING_10, ideal_norm,
        int_divides, monic, num_WOP, number_field, poly_var, ring_divides, ring_setadd, .. } := D.core2
  let { IDEAL_VALUATION_RING_OF_INT_COPRIME, NUMBER_FIELD_EISENSTEIN_POW,
        NUMBER_FIELD_EISENSTEIN_VALUATION, .. } := BEisenstein01
  -- @@SCOPE END

  let NUMBER_FIELD_EISENSTEIN_INDEPENDENT ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let v79 ← ASSUME (← q r"i:num < j")
    prove
      r"!(k:A ring) a m p c.
          number_field k /\ a IN ring_carrier k /\
          m IN ring_carrier(poly_ring integer_ring (:1)) /\
          monic integer_ring m /\
          poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m = ring_0 k /\
          prime p /\
          (!i. i < poly_deg integer_ring m ==> &p divides coeff i m) /\
          ~(&p pow 2 divides coeff 0 m) /\
          ring_sum k {i | i < poly_deg integer_ring m}
            (\i. ring_mul k (ring_of_int k (c i)) (ring_pow k a i)) IN
          ideal_generated (ring_of_integers k) {ring_of_num k p}
          ==> !i. i < poly_deg integer_ring m ==> &p divides c i"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_RING_OF_INTEGERS)) THEN SUBGOAL_THEN (← q r"ring_carrier(ring_of_integers k) subring_of (k:A ring)") ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_SUBRING], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"m:(1->num)->int"), (← q r"p:num")] NUMBER_FIELD_EISENSTEIN_POW) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"p:num")] NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q) THEN ASM_REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY), IN_ELIM_THM] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"P:A->bool") STRIP_ASSUME_TAC) o (CONJUNCT1 o CONJUNCT2)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"m:(1->num)->int"), (← q r"p:num"), (← q r"P:A->bool")] NUMBER_FIELD_EISENSTEIN_VALUATION) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"P:A->bool"), (← q r"p:num")] NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"p:num")] RAMIFICATION_INDEX_PRIME) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN STRIP_TAC THEN ABBREV_TAC (← q r"n = poly_deg integer_ring (m:(1->num)->int)") THEN ABBREV_TAC (← q r"w = ideal_valuation (ring_of_integers k) P
          (ideal_generated (ring_of_integers k) {a:A})") THEN ABBREV_TAC (← q r"e = ideal_valuation (ring_of_integers k) P
          (ideal_generated (ring_of_integers k) {ring_of_num k p:A})") THEN SUBGOAL_THEN (← q r"~(ring_of_num k p = ring_0 (k:A ring))") ASSUME_TAC THENL [REWRITE_TAC [(← GSYM RING_OF_INT_OF_NUM)] THEN ASM_SIMP_TAC [RING_OF_INT_EQ_0_CHAR_0, INT_OF_NUM_EQ, PRIME_IMP_NZ], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(P = {ring_0 (ring_of_integers k:A ring)})") ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS] THEN ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(ring_of_num k p:A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [REWRITE_TAC [(← GSYM RING_OF_INT_OF_NUM), RING_OF_INT_IN_RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_generated (ring_of_integers k) {ring_of_num k p:A} SUBSET
    ideal_pow (ring_of_integers k) P e") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"ideal_generated (ring_of_integers k) {ring_of_num k p:A}"), (← q r"e:num")] DEDEKIND_IDEAL_SUBSET_POW_VALUATION) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0, RING_OF_INTEGERS, LE_REFL], ALL_TAC] THEN GEN_REWRITE_TAC id [(← MESON [] (← q r"(!i:num. P i) <=> ~(?i. ~P i)"))] THEN REWRITE_TAC [NOT_IMP] THEN ONCE_REWRITE_TAC [num_WOP] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"j:num") (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "min"))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"P:A->bool"), (← q r"p:num"), (← q r"(c:num->int) j")] IDEAL_VALUATION_RING_OF_INT_COPRIME) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_mul k (ring_of_int k ((c:num->int) j)) (ring_pow k a (n - 1)):A IN
    ideal_generated (ring_of_integers k) {ring_of_num k p}") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"!i. ring_mul k (ring_of_int k ((c:num->int) i))
            (ring_pow k a (i + (n - 1 - j))):A IN
          ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [ASM_SIMP_TAC [IN_SUBRING_MUL, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sum k {i | i < n}
        (\i. ring_mul k (ring_of_int k ((c:num->int) i))
               (ring_pow k a (i + (n - 1 - j)))) IN
      ideal_generated (ring_of_integers k) {ring_of_num k p:A}") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"ring_sum k {i | i < n}
          (\i. ring_mul k (ring_of_int k ((c:num->int) i))
                 (ring_pow k a (i + (n - 1 - j)))) =
        ring_mul k (ring_pow k a (n - 1 - j))
          (ring_sum k {i | i < n}
             (\i. ring_mul k (ring_of_int k (c i)) (ring_pow k (a:A) i)))") SUBST1_TAC THENL [ASM_SIMP_TAC [(← GSYM RING_SUM_LMUL), FINITE_NUMSEG_LT, RING_MUL, RING_OF_INT, RING_POW] THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"i:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC [] THEN ASM_SIMP_TAC [RING_POW_ADD] THEN MATCH_MP_TAC (← RING_RULE (← q r"ring_mul r c (ring_mul r x y) =
          ring_mul r y (ring_mul r c (x:A))")) THEN ASM_SIMP_TAC [RING_OF_INT, RING_POW], MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ideal_generated (ring_of_integers k)
                          {ring_of_num k p:A}"), (← q r"ring_pow k a (n - 1 - j):A"), (← q r"ring_sum k {i | i < n}
                          (\i. ring_mul k (ring_of_int k ((c:num->int) i))
                                 (ring_pow k (a:A) i))")] IN_RING_IDEAL_LMUL) THEN ASM_SIMP_TAC [RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED, IN_SUBRING_POW]], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sum k ({i | i < n} DELETE j)
        (\i. ring_mul k (ring_of_int k ((c:num->int) i))
               (ring_pow k a (i + (n - 1 - j)))) IN
      ideal_generated (ring_of_integers k) {ring_of_num k p:A}") ASSUME_TAC THENL [wPart lhand (rand o rand) RING_SUM_RING_OF_INTEGERS THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC IN_RING_IDEAL_SUM THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, IN_DELETE, IN_ELIM_THM] THEN X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"i:num < j") THENL [USE_THEN "min" (MP_TAC o ((← do let c := v79; pure (fun th => MP th c)) o (SPEC (← q r"i:num")))) THEN ASM_REWRITE_TAC [int_divides] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"t:int") SUBST1_TAC) THEN MATCH_MP_TAC IN_IDEAL_GENERATED_SING THEN REWRITE_TAC [ring_divides, RING_OF_INTEGERS] THEN REWRITE_TAC [RING_OF_INT_MUL, (← GSYM RING_OF_INT_OF_NUM)] THEN ASM_SIMP_TAC [IN_SUBRING_MUL, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS] THEN EXISTS_TAC (← q r"ring_mul k (ring_of_int k t) (ring_pow k a (i + (n - 1 - j))):A") THEN ASM_SIMP_TAC [IN_SUBRING_MUL, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS] THEN MATCH_MP_TAC (← RING_RULE (← q r"ring_mul r (ring_mul r x y) z =
          ring_mul r x (ring_mul r y (z:A))")) THEN ASM_SIMP_TAC [RING_OF_INT, RING_POW], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_pow k a (i + (n - 1 - j)) =
        ring_mul k (ring_pow k a n) (ring_pow k (a:A) (i - j - 1))") SUBST1_TAC THENL [ASM_SIMP_TAC [(← GSYM RING_POW_ADD)] THEN AP_TERM_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ideal_generated (ring_of_integers k)
                        {ring_of_num k p:A}"), (← q r"ring_of_int k ((c:num->int) i):A"), (← q r"ring_mul k (ring_pow k a n)
                        (ring_pow k (a:A) (i - j - 1))")] IN_RING_IDEAL_LMUL) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ideal_generated (ring_of_integers k)
                        {ring_of_num k p:A}"), (← q r"ring_pow k a n:A"), (← q r"ring_pow k (a:A) (i - j - 1)")] IN_RING_IDEAL_RMUL) THEN ASM_SIMP_TAC [RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"\i. ring_mul k (ring_of_int k ((c:num->int) i))
                      (ring_pow k (a:A) (i + (n - 1 - j)))"), (← q r"{i:num | i < n}"), (← q r"j:num")] RING_SUM_DELETE) THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, RING_MUL, RING_OF_INT, RING_POW], ALL_TAC] THEN REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"j + (n - 1 - j) = n - 1") (fun th => REWRITE_TAC [th]) THENL [ASM_ARITH_TAC, ALL_TAC] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ideal_generated (ring_of_integers k) {ring_of_num k p:A}"), (← q r"ring_sum k {i | i < n}
                      (\i. ring_mul k (ring_of_int k ((c:num->int) i))
                             (ring_pow k (a:A) (i + (n - 1 - j))))"), (← q r"ring_sum k ({i | i < n} DELETE j)
                      (\i. ring_mul k (ring_of_int k ((c:num->int) i))
                             (ring_pow k (a:A) (i + (n - 1 - j))))")] IN_RING_IDEAL_SUB) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED] THEN MATCH_MP_TAC (← MESON [] (← q r"(a:A) = b ==> a IN s ==> b IN s")) THEN MATCH_MP_TAC (← RING_RULE (← q r"ring_sub r y (ring_sub r y x) = (x:A)")) THEN ASM_SIMP_TAC [RING_SUM, RING_MUL, RING_OF_INT, RING_POW], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(ring_pow k a (n - 1) = ring_0 (k:A ring)) /\
    ~(ring_mul k (ring_of_int k ((c:num->int) j)) (ring_pow k a (n - 1)) =
      ring_0 (k:A ring))") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_int k ((c:num->int) j):A"), (← q r"ring_pow k a (n - 1):A")] INTEGRAL_DOMAIN_MUL_EQ_0) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"a:A"), (← q r"n - 1")] INTEGRAL_DOMAIN_POW_EQ_0) THEN ASM_SIMP_TAC [RING_OF_INTEGERS, DEDEKIND_IMP_INTEGRAL_DOMAIN, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"e <= ideal_valuation (ring_of_integers k) P
           (ideal_generated (ring_of_integers k)
              {ring_mul k (ring_of_int k ((c:num->int) j))
                 (ring_pow k a (n - 1)):A})") MP_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"ring_mul k (ring_of_int k ((c:num->int) j))
                      (ring_pow k a (n - 1)):A"), (← q r"e:num")] DEDEKIND_IN_IDEAL_POW_VALUATION) THEN ASM_SIMP_TAC [RING_OF_INTEGERS, IN_SUBRING_MUL, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN FIRST_X_ASSUM (MATCH_MP_TAC o ((REWRITE_RULE [SUBSET]) o (checkM (fun th => (do if ← (do if ← (do let z20 ← (do let z21 ← (pure th); pure (concl z21)); pure (is_comb z20)) then (do let z22 ← (do let z23 ← (do let z24 ← (pure th); pure (concl z24)); liftExcept (rator z23)); pure (is_comb z22)) else pure false) then (do let z29 ← (pure "SUBSET"); let z28 ← (do pure (Prod.fst (← (do let z25 ← (do pure (Prod.fst (← (do let z26 ← (do let z27 ← (pure th); pure (concl z27)); pure (strip_comb z26))))); liftExcept (dest_const z25))))); pure (z28 == z29)) else pure false))))) THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"ring_of_int k ((c:num->int) j):A"), (← q r"ring_pow k a (n - 1):A")] IDEAL_VALUATION_PRINCIPAL_MUL) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"a:A"), (← q r"n - 1")] IDEAL_VALUATION_PRINCIPAL_POW) THEN ASM_SIMP_TAC [RING_OF_INTEGERS, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN DISCH_THEN SUBST1_TAC THEN SUBGOAL_THEN (← q r"n = SUC(n - 1)") MP_TAC THENL [MATCH_MP_TAC (← ARITH_RULE (← q r"~(n = 0) ==> n = SUC(n - 1)")) THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN DISCH_THEN (fun th => tactic_of do pure (FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th' => (do if ← (do let z1 ← (do let z2 ← (pure th'); pure (concl z2)); pure (is_eq z1)) then (do let z6 ← (q r"n * w:num"); let z5 ← (do let z3 ← (do let z4 ← (pure th'); pure (concl z4)); liftExcept (lhs z3)); pure (z5 == z6)) else pure false))))) THEN SUBST1_TAC th)) THEN REWRITE_TAC [MULT_CLAUSES, SUC_SUB1] THEN ASM_ARITH_TAC)

  let NUMBER_FIELD_EISENSTEIN_INDEX_COPRIME ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let v38 ← ASSUME (← q r"i:num < n")
    let v41 ← ASSUME (← q r"i:num < n")
    prove
      r"!(k:A ring) a m p.
          number_field k /\ a IN ring_carrier k /\
          m IN ring_carrier(poly_ring integer_ring (:1)) /\
          monic integer_ring m /\
          poly_deg integer_ring m =
          extension_degree (subfield_generated k {ring_0 k},k) I /\
          poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m = ring_0 k /\
          prime p /\
          (!i. i < poly_deg integer_ring m ==> &p divides coeff i m) /\
          ~(&p pow 2 divides coeff 0 m)
          ==> ring_setadd (ring_of_integers k)
                (ring_carrier(subring_generated k {a}))
                (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
              ring_carrier(ring_of_integers k)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN ABBREV_TAC (← q r"n = poly_deg integer_ring (m:(1->num)->int)") THEN FIRST_X_ASSUM (ASSUME_TAC o (SYM o (checkM (fun th => (do if ← (do let z108 ← (do let z109 ← (pure th); pure (concl z109)); pure (is_eq z108)) then (do let z113 ← (q r"n:num"); let z112 ← (do let z110 ← (do let z111 ← (pure th); pure (concl z111)); liftExcept (lhs z110)); pure (z112 == z113)) else pure false))))) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN SUBGOAL_THEN (← q r"ring_carrier(ring_of_integers k) subring_of (k:A ring)") ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_SUBRING], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x:A. x IN ring_carrier(ring_of_integers k) ==> x IN ring_carrier k") (LABEL_TAC "sub") THENL [MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"m:(1->num)->int"), (← q r"p:num")] NUMBER_FIELD_EISENSTEIN_POW) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"m:(1->num)->int")] SUBRING_GENERATED_INT_LINCOMB) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"m:(1->num)->int"), (← q r"p:num")] NUMBER_FIELD_EISENSTEIN_INDEPENDENT) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (LABEL_TAC "ind") THEN ABBREV_TAC (← q r"J = ideal_generated (ring_of_integers k) {ring_of_num k p:A}") THEN SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers k) (J:A->bool)") ASSUME_TAC THENL [EXPAND_TAC "J" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"!c. ring_sum k {i | i < n}
          (\i. ring_mul k (ring_of_int k (c i)) (ring_pow k a i)) IN
        ring_carrier(ring_of_integers k:A ring)") ASSUME_TAC THENL [GEN_TAC THEN MATCH_MP_TAC IN_SUBRING_SUM THEN ASM_SIMP_TAC [IN_SUBRING_MUL, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_carrier(quotient_ring (ring_of_integers k) (J:A->bool))
    HAS_SIZE p EXP n") ASSUME_TAC THENL [REWRITE_TAC [HAS_SIZE] THEN CONJ_TAC THENL [MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "J" THEN REWRITE_TAC [(← GSYM RING_OF_INT_OF_NUM)] THEN DISCH_THEN (MP_TAC o (AP_TERM (← q r"\s:A->bool. ring_of_int k (&p):A IN s"))) THEN REWRITE_TAC [IN_IDEAL_GENERATED_SELF, IN_SING, RING_OF_INT_IN_RING_OF_INTEGERS] THEN ASM_SIMP_TAC [RING_OF_INT_EQ_0_CHAR_0, INT_OF_NUM_EQ, PRIME_IMP_NZ], MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"&p:int")] RING_OF_INTEGERS_IDEAL_NORM_INTEGER) THEN ASM_SIMP_TAC [INT_OF_NUM_EQ, PRIME_IMP_NZ, RING_OF_INT_OF_NUM, INT_ABS_NUM, NUM_OF_INT_OF_NUM] THEN REWRITE_TAC [ideal_norm]], ALL_TAC] THEN ABBREV_TAC (← q r"D = {c:num->int | (!i. i IN {i | i < n} ==> c i IN IMAGE (&) {j | j < p}) /\
                      (!i. ~(i IN {i | i < n}) ==> c i = &0)}") THEN SUBGOAL_THEN (← q r"(D:(num->int)->bool) HAS_SIZE p EXP n") ASSUME_TAC THENL [EXPAND_TAC "D" THEN MATCH_MP_TAC HAS_SIZE_FUNSPACE THEN REWRITE_TAC [HAS_SIZE_NUMSEG_LT] THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN REWRITE_TAC [HAS_SIZE_NUMSEG_LT, INT_OF_NUM_EQ] THEN MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"D:(num->int)->bool"), (← q r"ring_carrier(quotient_ring (ring_of_integers k) (J:A->bool))"), (← q r"\c:num->int. ring_coset (ring_of_integers k) J
                    (ring_sum k {i | i < n}
                       (\i. ring_mul k (ring_of_int k (c i))
                              (ring_pow k (a:A) i)))")] SURJECTIVE_IFF_INJECTIVE_GEN) THEN ANTS_TAC THENL [RULE_ASSUM_TAC (REWRITE_RULE [HAS_SIZE]) THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER] THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"c:num->int") THEN DISCH_TAC THEN EXISTS_TAC (← q r"ring_sum k {i | i < n}
      (\i. ring_mul k (ring_of_int k ((c:num->int) i))
                       (ring_pow k (a:A) i))") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MATCH_MP_TAC (← TAUT (← q r"q /\ (p ==> r) ==> (p <=> q) ==> r")) THEN CONJ_TAC THENL [MAP_EVERY X_GEN_TAC [(← q r"c:num->int"), (← q r"d:num->int")] THEN EXPAND_TAC "D" THEN REWRITE_TAC [IN_ELIM_THM, IN_IMAGE] THEN DISCH_THEN (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "c1") (LABEL_TAC "c2")) (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "d1") (LABEL_TAC "d2")) ASSUME_TAC)) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"J:A->bool"), (← q r"ring_sum k {i | i < n}
         (\i. ring_mul k (ring_of_int k ((c:num->int) i))
                (ring_pow k (a:A) i))"), (← q r"ring_sum k {i | i < n}
         (\i. ring_mul k (ring_of_int k ((d:num->int) i))
                (ring_pow k (a:A) i))")] RING_COSET_EQ) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"i:num") THEN ASM_CASES_TAC (← q r"i:num < n") THENL [ALL_TAC, USE_THEN "c2" (MP_TAC o (SPEC (← q r"i:num"))) THEN USE_THEN "d2" (MP_TAC o (SPEC (← q r"i:num"))) THEN ASM_SIMP_TAC []] THEN USE_THEN "ind" (MP_TAC o (SPEC (← q r"\i. (c:num->int) i - d i"))) THEN ANTS_TAC THENL [EXPAND_TAC "J" THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do if ← (do let z47 ← (do let z48 ← (pure th); pure (concl z48)); canM (fun z49 => (do let z50 ← (pure z49); find_termM (fun z51 => (do let z53 ← (pure z51); let z52 ← (q r"J:A->bool"); pure (z52 == z53))) z50)) z47) then (do let z54 ← (do let z55 ← (pure th); pure (concl z55)); canM (fun z56 => (do let z57 ← (pure z56); find_termM (fun z58 => (do let z60 ← (pure z58); let z59 ← (q r"ring_sub:(A ring)->A->A->A"); pure (z59 == z60))) z57)) z54) else pure false)))) THEN EXPAND_TAC "J" THEN MATCH_MP_TAC (← MESON [] (← q r"(a:A) = b ==> a IN s ==> b IN s")) THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier k") ASSUME_TAC THENL [USE_THEN "sub" MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [(← GSYM RING_SUM_SUB), FINITE_NUMSEG_LT, RING_MUL, RING_OF_INT, RING_POW] THEN MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN REWRITE_TAC [RING_OF_INT_SUB] THEN ASM_SIMP_TAC [RING_SUB_RDISTRIB, RING_OF_INT, RING_POW], DISCH_THEN (MP_TAC o (SPEC (← q r"i:num"))) THEN ASM_REWRITE_TAC []] THEN USE_THEN "c1" (MP_TAC o ((← do let c := v41; pure (fun th => MP th c)) o (SPEC (← q r"i:num")))) THEN USE_THEN "d1" (MP_TAC o ((← do let c := v38; pure (fun th => MP th c)) o (SPEC (← q r"i:num")))) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"v:num") STRIP_ASSUME_TAC) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"u:num") STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (MATCH_MP INT_DIVIDES_LE)) THEN MP_TAC (← SPEC (← q r"u:num") INT_POS) THEN MP_TAC (← SPEC (← q r"v:num") INT_POS) THEN UNDISCH_TAC (← q r"u:num < p") THEN UNDISCH_TAC (← q r"v:num < p") THEN REWRITE_TAC [(← GSYM INT_OF_NUM_LT)] THEN INT_ARITH_TAC, ALL_TAC] THEN DISCH_TAC THEN REWRITE_TAC [ring_setadd, EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:A") THEN EQ_TAC THENL [REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"y:A"), (← q r"z:A")] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_ADD) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (MATCH_MP_TAC o ((REWRITE_RULE [SUBSET]) o (MATCH_MP RING_IDEAL_IMP_SUBSET))) THEN ASM_REWRITE_TAC [], DISCH_TAC] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"ring_coset (ring_of_integers k) J (x:A)"))) THEN ANTS_TAC THENL [ASM_SIMP_TAC [QUOTIENT_RING_CARRIER] THEN REWRITE_TAC [IN_ELIM_THM] THEN EXISTS_TAC (← q r"x:A") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:num->int") (STRIP_ASSUME_TAC o BETA_RULE)) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"J:A->bool"), (← q r"ring_sum k {i | i < n}
       (\i. ring_mul k (ring_of_int k ((c:num->int) i))
              (ring_pow k (a:A) i))"), (← q r"x:A")] RING_COSET_EQ) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_TAC THEN EXISTS_TAC (← q r"ring_sum k {i | i < n}
      (\i. ring_mul k (ring_of_int k ((c:num->int) i))
             (ring_pow k (a:A) i))") THEN EXISTS_TAC (← q r"ring_sub k x
      (ring_sum k {i | i < n}
         (\i. ring_mul k (ring_of_int k ((c:num->int) i))
                (ring_pow k (a:A) i)))") THEN REPEAT CONJ_TAC THENL [EXISTS_TAC (← q r"c:num->int") THEN REWRITE_TAC [IN_UNIV], MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"J:A->bool"), (← q r"ring_sub k
         (ring_sum k {i | i < n}
            (\i. ring_mul k (ring_of_int k ((c:num->int) i))
                   (ring_pow k (a:A) i))) x")] IN_RING_IDEAL_NEG) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN MATCH_MP_TAC (← MESON [] (← q r"(a:A) = b ==> a IN s ==> b IN s")) THEN MATCH_MP_TAC (← RING_RULE (← q r"ring_neg r (ring_sub r y x) = ring_sub r x (y:A)")) THEN CONJ_TAC THEN USE_THEN "sub" MATCH_MP_TAC THEN ASM_REWRITE_TAC [], CONV_TAC SYM_CONV THEN MATCH_MP_TAC (← RING_RULE (← q r"ring_add r y (ring_sub r x y) = (x:A)")) THEN CONJ_TAC THEN USE_THEN "sub" MATCH_MP_TAC THEN ASM_REWRITE_TAC []])

  let NUMBER_FIELD_EISENSTEIN ← prove
    r"!(k:A ring) a m p.
        number_field k /\ a IN ring_carrier k /\
        m IN ring_carrier(poly_ring integer_ring (:1)) /\
        monic integer_ring m /\
        poly_deg integer_ring m =
        extension_degree (subfield_generated k {ring_0 k},k) I /\
        poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m = ring_0 k /\
        prime p /\
        (!i. i < poly_deg integer_ring m ==> &p divides coeff i m) /\
        ~(&p pow 2 divides coeff 0 m)
        ==> prime_ideal (ring_of_integers k)
              (ideal_generated (ring_of_integers k) {ring_of_num k p, a}) /\
            {P | prime_ideal (ring_of_integers k) P /\ ring_of_num k p IN P} =
            {ideal_generated (ring_of_integers k) {ring_of_num k p, a}} /\
            ideal_generated (ring_of_integers k) {ring_of_num k p} =
            ideal_pow (ring_of_integers k)
              (ideal_generated (ring_of_integers k) {ring_of_num k p, a})
              (poly_deg integer_ring m) /\
            ramification_index (integer_ring,ring_of_integers k)
              (ring_of_int k)
              (ideal_generated (ring_of_integers k) {ring_of_num k p, a}) =
            poly_deg integer_ring m /\
            residue_degree (integer_ring,ring_of_integers k) (ring_of_int k)
              (ideal_generated (ring_of_integers k) {ring_of_num k p, a}) =
            1 /\
            ring_setadd (ring_of_integers k)
              (ring_carrier(subring_generated k {a}))
              (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
            ring_carrier(ring_of_integers k)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"m:(1->num)->int"), (← q r"p:num")] NUMBER_FIELD_EISENSTEIN_INDEX_COPRIME) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"n = poly_deg integer_ring (m:(1->num)->int)") THEN FIRST_X_ASSUM (ASSUME_TAC o (SYM o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_eq z1)) then (do let z6 ← (q r"n:num"); let z5 ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); liftExcept (lhs z3)); pure (z5 == z6)) else pure false))))) THEN SUBGOAL_THEN (← q r"~(n = 0)") ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"k:A ring") NUMBER_FIELD_DEGREE_POS) THEN ASM_REWRITE_TAC [] THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"field(integer_mod_ring p)") ASSUME_TAC THENL [ASM_REWRITE_TAC [FIELD_INTEGER_MOD_RING], ALL_TAC] THEN SUBGOAL_THEN (← q r"poly_extend (integer_ring,k) (ring_of_int k) (\v. a)
      (poly_var (integer_mod_ring p) one) = (a:A)") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"poly_var (integer_mod_ring p) one = poly_var integer_ring one") SUBST1_TAC THENL [REWRITE_TAC [poly_var, INTEGER_MOD_RING_CLAUSES, INTEGER_RING] THEN SUBGOAL_THEN (← q r"&1 rem &p = &1") (fun th => REWRITE_TAC [th]) THEN REWRITE_TAC [INT_REM_EQ_SELF, INT_ABS_NUM, INT_OF_NUM_LT, INT_POS, INT_OF_NUM_EQ] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP PRIME_GE_2)) THEN ARITH_TAC, MATCH_MP_TAC POLY_EXTEND_VAR THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT]], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_of_int (integer_mod_ring p) o (m:(1->num)->int) =
    poly_pow (integer_mod_ring p) (poly_var (integer_mod_ring p) one) n") ASSUME_TAC THENL [REWRITE_TAC [(← GSYM FUN_EQ_COEFF), COEFF_COMPOSE, COEFF_POLY_VARPOW] THEN X_GEN_TAC (← q r"d:num") THEN ASM_CASES_TAC (← q r"d:num < n") THENL [SUBGOAL_THEN (← q r"~(d:num = n)") (fun th => REWRITE_TAC [th]) THENL [ASM_ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [RING_OF_INT_EQ_0, INTEGER_MOD_RING_CHAR] THEN ASM_SIMP_TAC [], ALL_TAC] THEN ASM_CASES_TAC (← q r"d:num = n") THENL [UNDISCH_TAC (← q r"monic integer_ring (m:(1->num)->int)") THEN ASM_REWRITE_TAC [monic, INTEGER_RING] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [RING_OF_INT_1], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"m:(1->num)->int"), (← q r"d:num")] COEFF_ABOVE_DEG) THEN ASM_REWRITE_TAC [RING_POLYNOMIAL] THEN ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [INTEGER_RING] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [RING_OF_INT_0], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"p:num"), (← q r"m:(1->num)->int"), (← q r"{0}"), (← q r"\i:num. poly_var (integer_mod_ring p) one"), (← q r"\i:num. (n:num)"), (← q r"\i:num. ideal_generated (ring_of_integers k) {ring_of_num k p, a:A}")] DEDEKIND_KUMMER_Q) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [FINITE_SING, IN_SING] THEN REPEAT CONJ_TAC THENL [GEN_TAC THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN REWRITE_TAC [(← GSYM RING_POLYNOMIAL), RING_POLYNOMIAL_VAR, MONIC_POLY_VAR] THEN MATCH_MP_TAC RING_IRREDUCIBLE_POLY_VAR THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, IN_UNIV], MESON_TAC [], SUBGOAL_THEN (← q r"ring_pow (poly_ring (integer_mod_ring p) (:1))
          (poly_var (integer_mod_ring p) one) n IN
        ring_carrier(poly_ring (integer_mod_ring p) (:1))") ASSUME_TAC THENL [MATCH_MP_TAC RING_POW THEN REWRITE_TAC [(← GSYM RING_POLYNOMIAL), RING_POLYNOMIAL_VAR], ASM_REWRITE_TAC [RING_PRODUCT_SING] THEN REWRITE_TAC [POLY_RING_CLAUSES]]], ALL_TAC] THEN REWRITE_TAC [IN_SING, IMAGE_CLAUSES] THEN SIMP_TAC [IDEAL_PRODUCT_SING, RING_IDEAL_IDEAL_POW] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o (SPEC (← q r"0"))))) THEN REWRITE_TAC [POLY_DEG_VAR] THEN SUBGOAL_THEN (← q r"~(ring_1 (integer_mod_ring p) = ring_0 (integer_mod_ring p))") (fun th => REWRITE_TAC [th]) THENL [ASM_MESON_TAC [FIELD_IMP_NONTRIVIAL_RING, TRIVIAL_RING_10], ALL_TAC] THEN STRIP_TAC THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_EISENSTEIN_INDEX ← prove
    r"!(k:A ring) a m p N.
        number_field k /\ a IN ring_carrier k /\
        m IN ring_carrier(poly_ring integer_ring (:1)) /\
        monic integer_ring m /\
        poly_deg integer_ring m =
        extension_degree (subfield_generated k {ring_0 k},k) I /\
        poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m = ring_0 k /\
        prime p /\
        (!i. i < poly_deg integer_ring m ==> &p divides coeff i m) /\
        ~(&p pow 2 divides coeff 0 m) /\
        {ring_coset (ring_of_integers k)
           (ring_carrier(subring_generated k {a})) x |
         x | x IN ring_carrier(ring_of_integers k)} HAS_SIZE N
        ==> ~(p divides N)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"p:num"), (← q r"N:num")] SUBRING_GENERATED_INDEX_COPRIME) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"m:(1->num)->int"), (← q r"p:num")] NUMBER_FIELD_EISENSTEIN_INDEX_COPRIME) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"m:(1->num)->int"), (← q r"p:num")] NUMBER_FIELD_EISENSTEIN_POW) THEN ASM_SIMP_TAC [])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_EISENSTEIN_INDEPENDENT, NUMBER_FIELD_EISENSTEIN_INDEX_COPRIME,
           NUMBER_FIELD_EISENSTEIN, NUMBER_FIELD_EISENSTEIN_INDEX }
  -- @@RETURN END

end HolANT.Eisenstein
