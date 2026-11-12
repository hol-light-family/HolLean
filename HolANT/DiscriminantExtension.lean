/- ========================================================================= -/
/- ANT: The relative discriminant of an extension of number fields         -/
/- ========================================================================= -/
/- File: HolANT/DiscriminantExtension.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/discriminant_extension.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antdiscriminantextensiondiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, ANT/ideal_arith.ml, Library/products.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/discriminant.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/classgroup.ml, ANT/prime_split.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/relative_degree.ml, ANT/nf_valuation.ml, ANT/integrality.ml, ANT/different.ml, ANT/finite_field_trace.ml, ANT/different_extension.ml, Library/frag.ml, Library/grouptheory.ml, Library/symmetric_group.ml, Library/galois.ml, Library/ring_groups.ml, Library/finite_fields.ml, ANT/decomposition.ml, ANT/ramification.ml, ANT/splitting_types.ml, ANT/nf_decomposition.ml, ANT/conjugate_ideals.ml, Library/integer.ml, Library/multiplicative.ml, Library/primitive.ml, ANT/dedekind_kummer.ml, ANT/decomposition_field.ml, ANT/split_primes.ml, ANT/ideal_norm_extension.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.DiscriminantExtension fills them).

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
import HolANT.IdealArith
import HolLibrary.Products
import HolANT.Algmisc
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
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.Classgroup
import HolANT.PrimeSplit
import HolANT.TraceForm
import HolANT.RelativeSplit
import HolANT.RelativeDegree
import HolANT.NfValuation
import HolANT.Integrality
import HolANT.Different
import HolANT.FiniteFieldTrace
import HolANT.DifferentExtension
import HolLibrary.Frag
import HolLibrary.GroupTheory
import HolLibrary.SymmetricGroup
import HolLibrary.Galois
import HolLibrary.RingGroups
import HolLibrary.FiniteFields
import HolANT.Decomposition
import HolANT.Ramification
import HolANT.SplittingTypes
import HolANT.NfDecomposition
import HolANT.ConjugateIdeals
import HolLibrary.Integer
import HolLibrary.Multiplicative
import HolLibrary.Primitive
import HolANT.DedekindKummer
import HolANT.DecompositionField
import HolANT.SplitPrimes
import HolANT.IdealNormExtension

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
open HolANT.IdealNorm
open HolANT.Zlattice
open HolANT.Numfield
open HolANT.RingOfIntegers
open HolANT.NormIndex
open HolANT.Discriminant
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.Classgroup
open HolANT.PrimeSplit
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.RelativeDegree
open HolANT.NfValuation
open HolANT.Integrality
open HolANT.Different
open HolANT.FiniteFieldTrace
open HolANT.DifferentExtension
open HolANT.Decomposition
open HolANT.Ramification
open HolANT.SplittingTypes
open HolANT.NfDecomposition
open HolANT.ConjugateIdeals
open HolANT.DedekindKummer
open HolANT.DecompositionField
open HolANT.SplitPrimes
open HolANT.IdealNormExtension

namespace HolANT.DiscriminantExtension

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ALGEBRA_NORM_EQ_0 ALGEBRA_NORM_INV ALGEBRA_NORM_MUL
   ALGEBRA_TRACE_DUAL_BASIS_EXISTS ALGEBRA_TRACE_LINCOMB_MUL
   ALGEBRA_TRACE_NORM_BASE ALGEBRA_TRACE_NORM_IN_CARRIER ALGEBRA_TRACE_SCALAR
   BASIS_DISCRIMINANT_MUL CARD_NUMSEG_LT CONTRAPOS_THM
   DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES DEDEKIND_IDEAL_SUBSET_POW_VALUATION
   DEDEKIND_IDEAL_SUBSET_VALUATION DEDEKIND_IDEAL_WEAK_APPROXIMATION
   DEDEKIND_IN_IDEAL_POW_VALUATION DEDEKIND_RING_OF_INTEGERS DE_MORGAN_THM
   EQ_TRANS FIELD_IMP_INTEGRAL_DOMAIN FIELD_MUL_LINV FIELD_MUL_RINV
   FIELD_SUBFIELD_GENERATED FIELD_UNIT FINITE_IMP_FIELD_EXTENSION
   FINITE_NUMSEG_LT FORALL_IN_GSPEC FREE_BASIS_EXTENSION_DEGREE FUN_EQ_THM
   IDEAL_GENERATED_INC IDEAL_GENERATED_MINIMAL IDEAL_GENERATED_MINIMAL_EQ
   IDEAL_GENERATED_MONO IDEAL_GENERATED_SING_ALT IDEAL_POW_1 IDEAL_PROD_COMM
   IDEAL_PROD_RZERO IDEAL_VALUATION_EQ_0 IDEAL_VALUATION_IDEAL_PROD
   IDEAL_VALUATION_PRINCIPAL_MUL IDEAL_VALUATION_PRINCIPAL_POW IMAGE_I IMAGE_o
   INTEGRAL_DOMAIN_MUL_EQ_0 INTEGRAL_DOMAIN_POW_EQ_0 INT_ABS_POS INT_ABS_POW
   INT_OF_NUM_MUL INT_OF_NUM_OF_INT INT_OF_NUM_POW IN_ELIM_THM
   IN_IDEAL_GENERATED_SELF IN_RING_IDEAL_0 IN_RING_IDEAL_LMUL IN_SING
   IN_SUBRING_MUL IN_SUBRING_SUM LEFT_IMP_EXISTS_THM MULT_CLAUSES MULT_EQ_0
   MULT_SYM NOT_EXISTS_THM NOT_FORALL_THM NOT_IMP NSUM_EQ NSUM_EQ_0
   NSUM_EQ_0_IFF NUMBER_FIELD_CODIFFERENT_BASIS_DISCRIMINANT
   NUMBER_FIELD_CODIFFERENT_DIFFERENT NUMBER_FIELD_CODIFFERENT_EQ_IMAGE
   NUMBER_FIELD_DIFFERENT_NONZERO NUMBER_FIELD_DIFFERENT_RAMIFIED
   NUMBER_FIELD_DIFFERENT_TOWER NUMBER_FIELD_FREE_BASIS_INTEGRAL
   NUMBER_FIELD_HOMOMORPHIC_PREIMAGE NUMBER_FIELD_IDEAL_NORM_DIFFERENT
   NUMBER_FIELD_IDEAL_NORM_EQ_0 NUMBER_FIELD_IDEAL_NORM_EXTENSION
   NUMBER_FIELD_IDEAL_NORM_EXTENSION_Q NUMBER_FIELD_IDEAL_NORM_IDEAL
   NUMBER_FIELD_IDEAL_NORM_IDEAL_NORM NUMBER_FIELD_IDEAL_NORM_MUL
   NUMBER_FIELD_IDEAL_NORM_MUL_Q NUMBER_FIELD_IDEAL_NORM_POW
   NUMBER_FIELD_IDEAL_NORM_TOWER NUMBER_FIELD_IDEAL_NORM_VALUATION
   NUMBER_FIELD_IMP_FIELD NUMBER_FIELD_NORM_INTEGRAL NUMBER_FIELD_NORM_MULTIPLE
   NUMBER_FIELD_NORM_VALUATION NUMBER_FIELD_PRIME_IDEALS_ABOVE
   NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO
   NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS NUMBER_FIELD_TOWER_LAW
   PRIME_IMP_RING_IDEAL PRIME_SUBFIELD_MONOMORPHIC_IMAGE RIGHT_EXISTS_IMP_THM
   RING_0 RING_1 RING_DET RING_DET_DIAGONAL RING_DET_EQ RING_DET_MUL
   RING_DET_SUBRING RING_HOMOMORPHISM_COMPOSE RING_HOMOMORPHISM_IN_CARRIER
   RING_HOMOMORPHISM_MUL RING_HOMOMORPHISM_POW
   RING_HOMOMORPHISM_SUBFIELD_INCLUSION RING_IDEAL_IDEAL_GENERATED
   RING_IDEAL_IDEAL_POW RING_IDEAL_IDEAL_PROD RING_IDEAL_IMP_SUBSET
   RING_IDEAL_NUMBER_FIELD_DIFFERENT RING_INV RING_MUL RING_MUL_ASSOC
   RING_MUL_IN_IDEAL_PROD RING_MUL_IN_PRIME_IDEAL RING_MUL_LID RING_MUL_RID
   RING_MUL_RZERO RING_OF_INTEGERS RING_OF_INTEGERS_IDEAL_EXTENSION
   RING_OF_INTEGERS_IDEAL_GENERATED_SING_EQ_0 RING_OF_INTEGERS_LOCAL_BASIS
   RING_OF_INTEGERS_SUBRING RING_OF_INTEGERS_SUBSET
   RING_OF_INTEGERS_SUBSET_CODIFFERENT RING_POW RING_POW_IN_PRIME_IDEAL
   RING_PRODUCT_CONST RING_SUM_EQ SING_SUBSET SKOLEM_THM SUBSET
   SUBSET_ANTISYM_EQ SUBSET_TRANS basis_discriminant field_extension
   number_field_codifferent number_field_different number_field_ideal_norm : thm)
  deriving Inhabited

/-- What discriminant_extension.ml uses from Session besides theorems. -/
structure DiscriminantExtensionDeps where
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
/- discriminant_extension.ml phrases from line 82 to 517                  -/
/- ---------------------------------------------------------------------- -/

structure DiscriminantExtension01 where
  -- @@FIELDS
  NUMBER_FIELD_BASIS_DISCRIMINANT_TWIST : thm
  NUMBER_FIELD_DIFFERENT_LOCAL_GENERATOR : thm
  NUMBER_FIELD_BASIS_DISCRIMINANT_IN_NORM_DIFFERENT : thm
  NUMBER_FIELD_CODIFFERENT_LOCAL_DUAL : thm
  NUMBER_FIELD_BASIS_DISCRIMINANT_TWIST_LOCAL : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDiscriminantExtension01 [HolBase] (D : DiscriminantExtensionDeps) :
    ExceptT String IO DiscriminantExtension01 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, RING_RULE, SET_RULE, SET_TAC, TAUT, .. } := D
  let { ALGEBRA_NORM_EQ_0, ALGEBRA_NORM_INV, ALGEBRA_NORM_MUL,
        ALGEBRA_TRACE_DUAL_BASIS_EXISTS, ALGEBRA_TRACE_LINCOMB_MUL,
        ALGEBRA_TRACE_NORM_BASE, ALGEBRA_TRACE_NORM_IN_CARRIER, ALGEBRA_TRACE_SCALAR,
        BASIS_DISCRIMINANT_MUL, CARD_NUMSEG_LT, CONTRAPOS_THM,
        DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES, DEDEKIND_IDEAL_SUBSET_POW_VALUATION,
        DEDEKIND_IDEAL_SUBSET_VALUATION, DEDEKIND_IDEAL_WEAK_APPROXIMATION,
        DEDEKIND_RING_OF_INTEGERS, EQ_TRANS, FIELD_IMP_INTEGRAL_DOMAIN, FIELD_MUL_LINV,
        FIELD_MUL_RINV, FIELD_UNIT, FINITE_IMP_FIELD_EXTENSION, FINITE_NUMSEG_LT,
        FORALL_IN_GSPEC, FREE_BASIS_EXTENSION_DEGREE, IDEAL_GENERATED_MINIMAL,
        IDEAL_GENERATED_MINIMAL_EQ, IDEAL_GENERATED_SING_ALT, IDEAL_POW_1,
        IDEAL_PROD_RZERO, IDEAL_VALUATION_EQ_0, IDEAL_VALUATION_IDEAL_PROD,
        IDEAL_VALUATION_PRINCIPAL_MUL, IDEAL_VALUATION_PRINCIPAL_POW,
        INTEGRAL_DOMAIN_MUL_EQ_0, INTEGRAL_DOMAIN_POW_EQ_0, IN_ELIM_THM,
        IN_IDEAL_GENERATED_SELF, IN_RING_IDEAL_0, IN_SUBRING_MUL, IN_SUBRING_SUM,
        LEFT_IMP_EXISTS_THM, MULT_CLAUSES, NOT_EXISTS_THM, NSUM_EQ, NSUM_EQ_0,
        NUMBER_FIELD_CODIFFERENT_BASIS_DISCRIMINANT,
        NUMBER_FIELD_CODIFFERENT_DIFFERENT, NUMBER_FIELD_DIFFERENT_NONZERO,
        NUMBER_FIELD_HOMOMORPHIC_PREIMAGE, NUMBER_FIELD_IDEAL_NORM_EQ_0,
        NUMBER_FIELD_IDEAL_NORM_IDEAL, NUMBER_FIELD_IDEAL_NORM_VALUATION,
        NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_NORM_INTEGRAL, NUMBER_FIELD_NORM_MULTIPLE,
        NUMBER_FIELD_NORM_VALUATION, NUMBER_FIELD_PRIME_IDEALS_ABOVE,
        NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO, NUMBER_FIELD_TOWER_LAW,
        PRIME_IMP_RING_IDEAL, RIGHT_EXISTS_IMP_THM, RING_0, RING_1, RING_DET,
        RING_DET_DIAGONAL, RING_DET_EQ, RING_DET_MUL, RING_DET_SUBRING,
        RING_HOMOMORPHISM_IN_CARRIER, RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_POW,
        RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IMP_SUBSET,
        RING_IDEAL_NUMBER_FIELD_DIFFERENT, RING_INV, RING_MUL, RING_MUL_ASSOC,
        RING_MUL_IN_IDEAL_PROD, RING_MUL_LID, RING_MUL_RID, RING_MUL_RZERO,
        RING_OF_INTEGERS, RING_OF_INTEGERS_IDEAL_GENERATED_SING_EQ_0,
        RING_OF_INTEGERS_SUBRING, RING_OF_INTEGERS_SUBSET,
        RING_OF_INTEGERS_SUBSET_CODIFFERENT, RING_POW, RING_PRODUCT_CONST, RING_SUM_EQ,
        SING_SUBSET, SKOLEM_THM, SUBSET, basis_discriminant, field_extension,
        number_field_codifferent, number_field_different, number_field_ideal_norm, .. } := D.core1
  -- @@SCOPE END

  let NUMBER_FIELD_BASIS_DISCRIMINANT_TWIST ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul (r:A ring) a b = ring_1 r
    ==> ring_mul r a (ring_mul r (ring_mul r c b) e) = ring_mul r c e")
    prove
      r"!k:A ring l:B ring h n w t d.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          free_basis (k,l) h n w /\
          t IN ring_carrier k /\ d IN ring_carrier l /\ ~(d = ring_0 l)
          ==> ring_mul k (algebra_norm (k,l) h d)
                (ring_det k {i | i < n}
                  (\i j. algebra_trace (k,l) h
                           (ring_mul l (ring_mul l (h t) (ring_inv l d))
                                       (ring_mul l (w i) (w j))))) =
              ring_mul k (ring_pow k t n) (basis_discriminant (k,l) h n w)"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITE_IMP_FIELD_EXTENSION)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o ((REWRITE_RULE [field_extension]) o (checkM (fun th => (do let z4 ← (q r"field_extension(k:A ring,l:B ring) h"); let z3 ← (do let z2 ← (pure th); pure (concl z2)); pure (z3 == z4)))))) THEN SUBGOAL_THEN (← q r"n = extension_degree(k:A ring,l:B ring) h") ASSUME_TAC THENL [MATCH_MP_TAC FREE_BASIS_EXTENSION_DEGREE THEN EXISTS_TAC (← q r"w:num->B") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(h:A->B) t IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN ASM_SIMP_TAC [BASIS_DISCRIMINANT_MUL, RING_MUL, RING_INV] THEN ASM_SIMP_TAC [ALGEBRA_NORM_MUL, RING_INV, ALGEBRA_NORM_INV, ALGEBRA_TRACE_NORM_BASE] THEN SUBGOAL_THEN (← q r"~(algebra_norm (k,l) (h:A->B) d = ring_0 k)") ASSUME_TAC THENL [ASM_SIMP_TAC [ALGEBRA_NORM_EQ_0], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"algebra_norm (k,l) (h:A->B) d")] FIELD_MUL_RINV) THEN ASM_REWRITE_TAC [ALGEBRA_TRACE_NORM_IN_CARRIER] THEN MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [RING_POW, RING_INV, ALGEBRA_TRACE_NORM_IN_CARRIER] THEN REWRITE_TAC [basis_discriminant, RING_DET])

  let NUMBER_FIELD_DIFFERENT_LOCAL_GENERATOR ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul (r:B ring) (ring_mul r a b) c =
        ring_mul r b (ring_mul r c a)")
    let r8 ← SET_RULE (← q r"s SUBSET t ==> (x:B) IN s ==> x IN t")
    let r9 ← TAUT (← q r"~(p /\ ~q) <=> p ==> q")
    let r19 ← ARITH_RULE (← q r"(n:num) = 0 ==> ~(1 <= n)")
    let r20 ← TAUT (← q r"p /\ (q ==> r) ==> (p <=> q) ==> r")
    prove
      r"!k:A ring l:B ring h p.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
          ==> ?d t. d IN number_field_different (k,l) h /\ ~(d = ring_0 l) /\
                    ideal_valuation (ring_of_integers k) p
                      (ideal_generated (ring_of_integers k)
                         {algebra_norm (k,l) h d}) =
                    ideal_valuation (ring_of_integers k) p
                      (number_field_ideal_norm (k,l) h
                         (number_field_different (k,l) h)) /\
                    t IN ring_carrier(ring_of_integers k) /\ ~(t IN p) /\
                    ring_mul l (h t) (ring_inv l d) IN
                    number_field_codifferent (k,l) h"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP NUMBER_FIELD_IMP_FIELD) o (checkM (fun th => (do let z23 ← (q r"number_field(l:B ring)"); let z22 ← (do let z21 ← (pure th); pure (concl z21)); pure (z22 == z23)))))) THEN SUBGOAL_THEN (← q r"dedekind_domain(ring_of_integers k:A ring) /\
      dedekind_domain(ring_of_integers l:B ring)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_IDEAL_NUMBER_FIELD_DIFFERENT) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_DIFFERENT_NONZERO) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_CODIFFERENT_DIFFERENT) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"D = number_field_different (k:A ring,l:B ring) h") THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(D:B->bool) SUBSET ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_PRIME_IDEALS_ABOVE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN SUBGOAL_THEN (← q r"!P. prime_ideal (ring_of_integers l) P /\ IMAGE (h:A->B) p SUBSET P
          ==> ~(P = {ring_0 l})") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"P:B->bool")] NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"{P | prime_ideal (ring_of_integers l) P /\
                         IMAGE (h:A->B) p SUBSET P}"), (← q r"D:B->bool")] DEDEKIND_IDEAL_WEAK_APPROXIMATION) THEN ASM_SIMP_TAC [RING_OF_INTEGERS, IN_ELIM_THM] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"d:B") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(d:B) IN ring_carrier(ring_of_integers l) /\
                  d IN ring_carrier l") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_valuation (ring_of_integers k) p
        (ideal_generated (ring_of_integers k) {algebra_norm (k,l) (h:A->B) d}) =
      ideal_valuation (ring_of_integers k) p
        (number_field_ideal_norm (k,l) h D)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"d:B")] NUMBER_FIELD_NORM_VALUATION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_VALUATION] THEN MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_SIMP_TAC [], ALL_TAC] THEN EXISTS_TAC (← q r"d:B") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"ideal_generated (ring_of_integers l) {d:B}"), (← q r"D:B->bool")] DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN MATCH_MP_TAC r20 THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET], DISCH_THEN (X_CHOOSE_THEN (← q r"J:B->bool") STRIP_ASSUME_TAC)] THEN SUBGOAL_THEN (← q r"~(J = {ring_0 l:B})") ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC (← q r"ideal_prod (ring_of_integers l) D J =
        ideal_generated (ring_of_integers l) {d:B}") THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") IDEAL_PROD_RZERO))] THEN DISCH_THEN (MP_TAC o SYM) THEN ASM_SIMP_TAC [RING_OF_INTEGERS_IDEAL_GENERATED_SING_EQ_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"!P. prime_ideal (ring_of_integers l) P /\ IMAGE (h:A->B) p SUBSET P
          ==> ideal_valuation (ring_of_integers l) P J = 0") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"P:B->bool"), (← q r"D:B->bool"), (← q r"J:B->bool")] IDEAL_VALUATION_IDEAL_PROD) THEN ASM_SIMP_TAC [RING_OF_INTEGERS] THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"~(number_field_ideal_norm (k,l) (h:A->B) J SUBSET p)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:A->bool"), (← q r"number_field_ideal_norm (k:A ring,l:B ring) h J"), (← q r"1")] DEDEKIND_IDEAL_SUBSET_POW_VALUATION) THEN ASM_SIMP_TAC [IDEAL_POW_1, PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS, NUMBER_FIELD_IDEAL_NORM_IDEAL, NUMBER_FIELD_IDEAL_NORM_EQ_0, NUMBER_FIELD_IDEAL_NORM_VALUATION] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN MATCH_MP_TAC r19 THEN MATCH_MP_TAC NSUM_EQ_0 THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_SIMP_TAC [MULT_CLAUSES], ALL_TAC] THEN SUBGOAL_THEN (← q r"?y. y IN J /\ ~(algebra_norm (k,l) (h:A->B) y IN p)") STRIP_ASSUME_TAC THENL [FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do if ← (do let z10 ← (do let z11 ← (pure th); pure (concl z11)); pure (is_neg z10)) then (do let z12 ← (do let z13 ← (pure th); pure (concl z13)); canM (fun z14 => (do let z15 ← (pure z14); find_termM (fun z16 => (do let z18 ← (pure z16); let z17 ← (q r"number_field_ideal_norm:(A ring#B ring)->(A->B)->                             (B->bool)->A->bool"); pure (z17 == z18))) z15)) z12) else pure false)))) THEN ONCE_REWRITE_TAC [(← GSYM CONTRAPOS_THM)] THEN REWRITE_TAC [NOT_EXISTS_THM, r9] THEN DISCH_TAC THEN REWRITE_TAC [number_field_ideal_norm] THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, SUBSET, FORALL_IN_GSPEC], ALL_TAC] THEN SUBGOAL_THEN (← q r"(y:B) IN ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN EXISTS_TAC (← q r"algebra_norm (k,l) (h:A->B) y") THEN ASM_SIMP_TAC [NUMBER_FIELD_NORM_INTEGRAL] THEN ABBREV_TAC (← q r"t = algebra_norm (k,l) (h:A->B) y") THEN SUBGOAL_THEN (← q r"(h:A->B) t IN J") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"y:B")] NUMBER_FIELD_NORM_MULTIPLE) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r8 THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"(h:A->B) t IN ring_carrier(ring_of_integers l) /\
                  h t IN ring_carrier l") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET, RING_OF_INTEGERS_SUBSET], ALL_TAC] THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN ASM_SIMP_TAC [RING_MUL, RING_INV] THEN X_GEN_TAC (← q r"z:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(z:B) IN ring_carrier(ring_of_integers l) /\
                  z IN ring_carrier l") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul l z ((h:A->B) t) IN ideal_generated (ring_of_integers l) {d}") MP_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); pure (is_eq z2)) then (do let z7 ← (q r"ideal_generated (ring_of_integers l) {d:B}"); let z6 ← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); liftExcept (rand z4)); pure (z6 == z7)) else pure false))))) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"D:B->bool"), (← q r"J:B->bool"), (← q r"z:B"), (← q r"(h:A->B) t")] RING_MUL_IN_IDEAL_PROD) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN ASM_SIMP_TAC [IDEAL_GENERATED_SING_ALT, IN_ELIM_THM] THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"w:B") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(w:B) IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul l (ring_mul l ((h:A->B) t) (ring_inv l d)) z =
      ring_mul l (ring_mul l (ring_inv l d) d) w") SUBST1_TAC THENL [TRANS_TAC EQ_TRANS (← q r"ring_mul l (ring_inv l d) (ring_mul l z ((h:A->B) t))") THEN CONJ_TAC THENL [MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [RING_INV], ASM_REWRITE_TAC [] THEN MATCH_MP_TAC RING_MUL_ASSOC THEN ASM_SIMP_TAC [RING_INV]], ASM_SIMP_TAC [FIELD_MUL_LINV, RING_MUL_LID]])

  let NUMBER_FIELD_BASIS_DISCRIMINANT_IN_NORM_DIFFERENT ← prove
    r"!k:A ring l:B ring h n w.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        free_basis (k,l) h n w /\
        (!i. i < n ==> w i IN ring_carrier(ring_of_integers l))
        ==> basis_discriminant (k,l) h n w IN
            number_field_ideal_norm (k,l) h (number_field_different (k,l) h)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP NUMBER_FIELD_IMP_FIELD) o (checkM (fun th => (do let z20 ← (q r"number_field(l:B ring)"); let z19 ← (do let z18 ← (pure th); pure (concl z18)); pure (z19 == z20)))))) THEN SUBGOAL_THEN (← q r"dedekind_domain(ring_of_integers k:A ring) /\
    dedekind_domain(ring_of_integers l:B ring)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"n:num"), (← q r"w:num->B"), (← q r"ring_1 l:B")] NUMBER_FIELD_CODIFFERENT_BASIS_DISCRIMINANT) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_OF_INTEGERS_SUBSET_CODIFFERENT) THEN ASM_REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_1))], STRIP_TAC] THEN ABBREV_TAC (← q r"e = basis_discriminant (k,l) (h:A->B) n w") THEN ABBREV_TAC (← q r"N = number_field_ideal_norm (k,l) (h:A->B)
          (number_field_different (k,l) h)") THEN SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers k) (N:A->bool) /\ ~(N = {ring_0 k})") STRIP_ASSUME_TAC THENL [EXPAND_TAC "N" THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_IDEAL, NUMBER_FIELD_IDEAL_NORM_EQ_0, RING_IDEAL_NUMBER_FIELD_DIFFERENT, NUMBER_FIELD_DIFFERENT_NONZERO], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_generated (ring_of_integers k) {e:A} SUBSET N") MP_TAC THENL [ALL_TAC, REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [IN_IDEAL_GENERATED_SELF]] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ideal_generated (ring_of_integers k) {e:A}"), (← q r"N:A->bool")] DEDEKIND_IDEAL_SUBSET_VALUATION) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, RING_OF_INTEGERS, RING_OF_INTEGERS_IDEAL_GENERATED_SING_EQ_0] THEN DISCH_THEN SUBST1_TAC THEN X_GEN_TAC (← q r"p:A->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_DIFFERENT_LOCAL_GENERATOR) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"d:B"), (← q r"t:A")] THEN STRIP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z11 ← (do let z12 ← (pure th); pure (concl z12)); pure (is_eq z11)) then (do let z17 ← (q r"N:A->bool"); let z16 ← (do let z13 ← (do let z14 ← (do let z15 ← (pure th); pure (concl z15)); liftExcept (rand z14)); liftExcept (rand z13)); pure (z16 == z17)) else pure false))))) THEN ABBREV_TAC (← q r"u = ring_mul l ((h:A->B) t) (ring_inv l d)") THEN SUBGOAL_THEN (← q r"(d:B) IN ring_carrier l /\ (t:A) IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET, RING_IDEAL_IMP_SUBSET, RING_IDEAL_NUMBER_FIELD_DIFFERENT], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i j. i < n /\ j < n
          ==> algebra_trace (k,l) (h:A->B)
                (ring_mul l u (ring_mul l ((w:num->B) i) (w j)))
              IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN UNDISCH_TAC (← q r"(u:B) IN number_field_codifferent (k,l) (h:A->B)") THEN REWRITE_TAC [number_field_codifferent, IN_ELIM_THM] THEN DISCH_THEN (MATCH_MP_TAC o CONJUNCT2) THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_MUL)) THEN ASM_SIMP_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"a = ring_det k {i | i < n}
          (\i j. algebra_trace (k,l) (h:A->B)
                   (ring_mul l u (ring_mul l ((w:num->B) i) (w j))))") THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [EXPAND_TAC "a" THEN MATCH_MP_TAC RING_DET_SUBRING THEN ASM_SIMP_TAC [RING_OF_INTEGERS_SUBRING, IN_ELIM_THM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"n:num"), (← q r"w:num->B"), (← q r"t:A"), (← q r"d:B")] NUMBER_FIELD_BASIS_DISCRIMINANT_TWIST) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"algebra_norm (k,l) (h:A->B) d IN ring_carrier(ring_of_integers k) /\
    ~(algebra_norm (k,l) h d = ring_0 k)") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [MATCH_MP_TAC NUMBER_FIELD_NORM_INTEGRAL THEN ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET, RING_IDEAL_NUMBER_FIELD_DIFFERENT], MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_SIMP_TAC [ALGEBRA_NORM_EQ_0]], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(t = ring_0 k:A)") ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC (← q r"~((t:A) IN p)") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:A->bool")] IN_RING_IDEAL_0) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_pow k t n IN ring_carrier(ring_of_integers k) /\
    ~(ring_pow k t n = ring_0 k:A)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") RING_POW))] THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_POW_EQ_0, FIELD_IMP_INTEGRAL_DOMAIN], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(a = ring_0 k:A)") ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC (← q r"ring_mul k (algebra_norm (k,l) (h:A->B) d) a =
      ring_mul k (ring_pow k t n) e") THEN ASM_SIMP_TAC [RING_MUL_RZERO, ALGEBRA_TRACE_NORM_IN_CARRIER] THEN DISCH_THEN (MP_TAC o SYM) THEN SUBGOAL_THEN (← q r"(e:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_MUL_EQ_0, FIELD_IMP_INTEGRAL_DOMAIN, RING_POW], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_valuation (ring_of_integers k) p
      (ideal_generated (ring_of_integers k) {t:A}) = 0") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:A->bool"), (← q r"ideal_generated (ring_of_integers k) {t:A}")] IDEAL_VALUATION_EQ_0) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, RING_OF_INTEGERS, RING_OF_INTEGERS_IDEAL_GENERATED_SING_EQ_0, IDEAL_GENERATED_MINIMAL_EQ, PRIME_IMP_RING_IDEAL] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN ASM SET_TAC [], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o ((AP_TERM (← q r"\x:A. ideal_valuation (ring_of_integers k) p
            (ideal_generated (ring_of_integers k) {x})")) o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_eq z1)) then (do let z3 ← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); liftExcept (lhs z4)); canM (fun z6 => (do let z7 ← (pure z6); find_termM (fun z8 => (do let z10 ← (pure z8); let z9 ← (q r"a:A"); pure (z9 == z10))) z7)) z3) else pure false))))) THEN REWRITE_TAC [] THEN ASM_SIMP_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") IDEAL_VALUATION_PRINCIPAL_MUL)), (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") IDEAL_VALUATION_PRINCIPAL_POW))] THEN ARITH_TAC)

  let NUMBER_FIELD_CODIFFERENT_LOCAL_DUAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul (r:B ring) (ring_mul r a b) c =
      ring_mul r (ring_mul r a c) b")
    prove
      r"!k:A ring l:B ring h (n:num) (w:num->B) s x.
          ring_homomorphism(k,l) h /\ s IN ring_carrier k /\
          (!i. i < n ==> w i IN ring_carrier l) /\
          (!y. y IN ring_carrier(ring_of_integers l)
               ==> ?c. (!i. c i IN ring_carrier(ring_of_integers k)) /\
                       ring_mul l (h s) y =
                       ring_sum l {i | i < n} (\i. ring_mul l (h(c i)) (w i))) /\
          x IN ring_carrier l /\
          (!i. i < n
               ==> algebra_trace (k,l) h (ring_mul l (w i) x) IN
                   ring_carrier(ring_of_integers k))
          ==> ring_mul l (h s) x IN number_field_codifferent (k,l) h"
      (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "loc") STRIP_ASSUME_TAC)))) THEN SUBGOAL_THEN (← q r"(h:A->B) s IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN REWRITE_TAC [number_field_codifferent, IN_ELIM_THM] THEN ASM_SIMP_TAC [RING_MUL] THEN X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(y:B) IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN REMOVE_THEN "loc" (MP_TAC o ((← do let c := (← ASSUME (← q r"(y:B) IN ring_carrier(ring_of_integers l)")); pure (fun th => MATCH_MP th c)) o (SPEC (← q r"y:B")))) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:num->A") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"ring_mul l (ring_mul l ((h:A->B) s) x) y =
      ring_mul l (ring_mul l (h s) y) x") SUBST1_TAC THENL [MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC [], ASM_REWRITE_TAC []] THEN SUBGOAL_THEN (← q r"!i. (c:num->A) i IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"{i:num | i < n}"), (← q r"c:num->A"), (← q r"w:num->B"), (← q r"x:B")] ALGEBRA_TRACE_LINCOMB_MUL) THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC IN_SUBRING_SUM THEN REWRITE_TAC [RING_OF_INTEGERS_SUBRING, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_SIMP_TAC [RING_OF_INTEGERS_SUBRING])

  let NUMBER_FIELD_BASIS_DISCRIMINANT_TWIST_LOCAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul (r:B ring) x1 x2 = ring_1 r
        ==> ring_mul r (ring_mul r x3 (ring_mul r x1 (ring_mul r x3 x5)))
             (ring_mul r (ring_mul r x6 x2) x7) =
            ring_mul r (ring_mul r x6 (ring_pow r x3 2)) (ring_mul r x7 x5)")
    let r21 ← RING_RULE (← q r"ring_mul (r:B ring) a (ring_mul r b c) =
        ring_mul r b (ring_mul r a c)")
    prove
      r"!k:A ring l:B ring h n w s d t.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          free_basis (k,l) h n w /\
          (!i. i < n ==> w i IN ring_carrier(ring_of_integers l)) /\
          s IN ring_carrier k /\
          (!x. x IN ring_carrier(ring_of_integers l)
               ==> ?c. (!i. c i IN ring_carrier(ring_of_integers k)) /\
                       ring_mul l (h s) x =
                       ring_sum l {i | i < n} (\i. ring_mul l (h(c i)) (w i))) /\
          d IN number_field_different (k,l) h /\ ~(d = ring_0 l) /\
          t IN ring_carrier k
          ==> ?b. b IN ring_carrier(ring_of_integers k) /\
                  ring_mul k b
                   (ring_det k {i | i < n}
                     (\i j. algebra_trace (k,l) h
                              (ring_mul l (ring_mul l (h t) (ring_inv l d))
                                          (ring_mul l (w i) (w j))))) =
                  ring_pow k (ring_mul k t (ring_pow k s 2)) n"
      (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "loc") STRIP_ASSUME_TAC))))))) THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP NUMBER_FIELD_IMP_FIELD) o (checkM (fun th => (do let z24 ← (q r"number_field(l:B ring)"); let z23 ← (do let z22 ← (pure th); pure (concl z22)); pure (z23 == z24)))))) THEN SUBGOAL_THEN (← q r"!i. i < n ==> (w:num->B) i IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"(d:B) IN ring_carrier l /\ (h:A->B) s IN ring_carrier l /\
      h t IN ring_carrier l") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET, RING_IDEAL_IMP_SUBSET, RING_IDEAL_NUMBER_FIELD_DIFFERENT, RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"n:num"), (← q r"w:num->B"), (← q r"ring_1 l:B")] NUMBER_FIELD_CODIFFERENT_BASIS_DISCRIMINANT) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_OF_INTEGERS_SUBSET_CODIFFERENT) THEN ASM_REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_1))], STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"n:num"), (← q r"w:num->B")] ALGEBRA_TRACE_DUAL_BASIS_EXISTS) THEN ANTS_TAC THENL [ASM_SIMP_TAC [FIELD_UNIT] THEN ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], DISCH_THEN (X_CHOOSE_THEN (← q r"v:num->B") STRIP_ASSUME_TAC)] THEN SUBGOAL_THEN (← q r"!i. i < n
          ==> ring_mul l d (ring_mul l ((h:A->B) s) ((v:num->B) i)) IN
              ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN UNDISCH_TAC (← q r"(d:B) IN number_field_different (k,l) (h:A->B)") THEN REWRITE_TAC [number_field_different, IN_ELIM_THM] THEN DISCH_THEN (MATCH_MP_TAC o CONJUNCT2) THEN MATCH_MP_TAC NUMBER_FIELD_CODIFFERENT_LOCAL_DUAL THEN MAP_EVERY EXISTS_TAC [(← q r"n:num"), (← q r"w:num->B")] THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN ASM_SIMP_TAC [] THEN COND_CASES_TAC THEN REWRITE_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") RING_0)), (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") RING_1))], ALL_TAC] THEN SUBGOAL_THEN (← q r"?B. !i. i < n
              ==> (!m. (B:num->num->A) i m IN
                       ring_carrier(ring_of_integers k)) /\
                  ring_mul l ((h:A->B) s)
                    (ring_mul l d (ring_mul l (h s) ((v:num->B) i))) =
                  ring_sum l {m | m < n} (\m. ring_mul l (h(B i m)) (w m))") STRIP_ASSUME_TAC THENL [REWRITE_TAC [(← GSYM SKOLEM_THM), RIGHT_EXISTS_IMP_THM] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN USE_THEN "loc" MATCH_MP_TAC THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i j. i < n /\ j < n ==> (B:num->num->A) i j IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN ABBREV_TAC (← q r"u = ring_mul l ((h:A->B) t) (ring_inv l d)") THEN SUBGOAL_THEN (← q r"(u:B) IN ring_carrier l") ASSUME_TAC THENL [EXPAND_TAC "u" THEN ASM_SIMP_TAC [RING_MUL, RING_INV], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i j. i < n /\ j < n
            ==> ring_sum k {m | m < n}
                  (\m. ring_mul k ((B:num->num->A) i m)
                         (algebra_trace (k,l) (h:A->B)
                            (ring_mul l u (ring_mul l (w m) (w j))))) =
                if i = j then ring_mul k t (ring_pow k s 2) else ring_0 k") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS (← q r"algebra_trace (k,l) (h:A->B)
          (ring_mul l
            (ring_sum l {m | m < n}
               (\m. ring_mul l (h((B:num->num->A) i m)) (w m)))
            (ring_mul l u ((w:num->B) j)))") THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"{m:num | m < n}"), (← q r"(B:num->num->A) i"), (← q r"w:num->B"), (← q r"ring_mul l u ((w:num->B) j)")] ALGEBRA_TRACE_LINCOMB_MUL) THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, RING_MUL] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"m:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN REPEAT AP_TERM_TAC THEN MATCH_MP_TAC r21 THEN ASM_SIMP_TAC [], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"i:num")) o (checkM (fun th => (do if ← (do if ← (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); pure (is_forall z5)) then (do let z7 ← (do let z8 ← (pure th); pure (concl z8)); canM (fun z9 => (do let z10 ← (pure z9); find_termM (fun z11 => (do let z13 ← (pure z11); let z12 ← (q r"B:num->num->A"); pure (z12 == z13))) z10)) z7) else pure false) then (do let z14 ← (do let z15 ← (pure th); pure (concl z15)); canM (fun z16 => (do let z17 ← (pure z16); find_termM (fun z18 => (do let z20 ← (pure z18); let z19 ← (q r"ring_mul l ((h:A->B) s)"); pure (z19 == z20))) z17)) z14) else pure false))))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (SUBST1_TAC o (SYM o CONJUNCT2))] THEN SUBGOAL_THEN (← q r"ring_mul l (ring_mul l ((h:A->B) s)
                      (ring_mul l d (ring_mul l (h s) ((v:num->B) i))))
          (ring_mul l u ((w:num->B) j)) =
        ring_mul l (h(ring_mul k t (ring_pow k s 2)))
          (ring_mul l (w j) (v i))") SUBST1_TAC THENL [FIRST_ASSUM ((fun th => tactic_of do pure (ASM_SIMP_TAC [RING_POW, (← MATCH_MP RING_HOMOMORPHISM_MUL th), (← MATCH_MP RING_HOMOMORPHISM_POW th)])) o (checkM (fun th => (do let z4 ← (q r"ring_homomorphism(k:A ring,l:B ring) h"); let z3 ← (do let z2 ← (pure th); pure (concl z2)); pure (z3 == z4))))) THEN EXPAND_TAC "u" THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"d:B")] FIELD_MUL_RINV) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [RING_INV], ALL_TAC] THEN ASM_SIMP_TAC [ALGEBRA_TRACE_SCALAR, RING_MUL, RING_POW] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [RING_MUL_RID, RING_MUL_RZERO, RING_MUL, RING_POW], ALL_TAC] THEN EXISTS_TAC (← q r"ring_det k {i | i < n} (B:num->num->A)") THEN CONJ_TAC THENL [MATCH_MP_TAC RING_DET_SUBRING THEN REWRITE_TAC [RING_OF_INTEGERS_SUBRING, IN_ELIM_THM] THEN ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{i:num | i < n}"), (← q r"B:num->num->A"), (← q r"\i j. algebra_trace (k,l) (h:A->B)
                            (ring_mul l u (ring_mul l ((w:num->B) i) (w j)))")] RING_DET_MUL) THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, ALGEBRA_TRACE_NORM_IN_CARRIER] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN TRANS_TAC EQ_TRANS (← q r"ring_det k {i:num | i < n}
        (\i j. if i = j then ring_mul k (t:A) (ring_pow k s 2)
               else ring_0 k)") THEN CONJ_TAC THENL [MATCH_MP_TAC RING_DET_EQ THEN ASM_SIMP_TAC [IN_ELIM_THM], ALL_TAC] THEN SIMP_TAC [RING_DET_DIAGONAL, FINITE_NUMSEG_LT, IN_ELIM_THM] THEN ASM_SIMP_TAC [RING_PRODUCT_CONST, FINITE_NUMSEG_LT, CARD_NUMSEG_LT, RING_MUL, RING_POW])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_BASIS_DISCRIMINANT_TWIST, NUMBER_FIELD_DIFFERENT_LOCAL_GENERATOR,
           NUMBER_FIELD_BASIS_DISCRIMINANT_IN_NORM_DIFFERENT,
           NUMBER_FIELD_CODIFFERENT_LOCAL_DUAL,
           NUMBER_FIELD_BASIS_DISCRIMINANT_TWIST_LOCAL }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- discriminant_extension.ml phrases from line 696 to 1146                -/
/- ---------------------------------------------------------------------- -/

structure DiscriminantExtension02 where
  -- @@FIELDS
  NUMBER_FIELD_NORM_DIFFERENT_LOCAL_BASIS : thm
  NUMBER_FIELD_DISCRIMINANT_BASES : thm
  NUMBER_FIELD_DISCRIMINANT_RAMIFIED : thm
  NUMBER_FIELD_DISCRIMINANT_TOWER : thm
  NUMBER_FIELD_DISCRIMINANT_TOWER_Q : thm
  NUMBER_FIELD_DISCRIMINANT_POW_DIVIDES : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDiscriminantExtension02 [HolBase] (D : DiscriminantExtensionDeps) (BDiscriminantExtension01 : DiscriminantExtension01) :
    ExceptT String IO DiscriminantExtension02 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INTEGER_RULE,
        NUM_REDUCE_CONV, SET_TAC, TAUT, .. } := D
  let { ALGEBRA_NORM_EQ_0, DEDEKIND_IDEAL_SUBSET_POW_VALUATION,
        DEDEKIND_IDEAL_SUBSET_VALUATION, DEDEKIND_IN_IDEAL_POW_VALUATION,
        DEDEKIND_RING_OF_INTEGERS, DE_MORGAN_THM, FIELD_SUBFIELD_GENERATED,
        FINITE_IMP_FIELD_EXTENSION, FORALL_IN_GSPEC, FUN_EQ_THM, IDEAL_GENERATED_INC,
        IDEAL_GENERATED_MINIMAL, IDEAL_GENERATED_MONO, IDEAL_POW_1, IDEAL_PROD_COMM,
        IDEAL_VALUATION_PRINCIPAL_MUL, IMAGE_I, IMAGE_o, INT_ABS_POS, INT_ABS_POW,
        INT_OF_NUM_MUL, INT_OF_NUM_OF_INT, INT_OF_NUM_POW, IN_ELIM_THM,
        IN_RING_IDEAL_0, IN_RING_IDEAL_LMUL, IN_SING, LEFT_IMP_EXISTS_THM, MULT_EQ_0,
        MULT_SYM, NOT_FORALL_THM, NOT_IMP, NSUM_EQ_0_IFF,
        NUMBER_FIELD_CODIFFERENT_BASIS_DISCRIMINANT, NUMBER_FIELD_CODIFFERENT_EQ_IMAGE,
        NUMBER_FIELD_DIFFERENT_NONZERO, NUMBER_FIELD_DIFFERENT_RAMIFIED,
        NUMBER_FIELD_DIFFERENT_TOWER, NUMBER_FIELD_FREE_BASIS_INTEGRAL,
        NUMBER_FIELD_HOMOMORPHIC_PREIMAGE, NUMBER_FIELD_IDEAL_NORM_DIFFERENT,
        NUMBER_FIELD_IDEAL_NORM_EQ_0, NUMBER_FIELD_IDEAL_NORM_EXTENSION,
        NUMBER_FIELD_IDEAL_NORM_EXTENSION_Q, NUMBER_FIELD_IDEAL_NORM_IDEAL,
        NUMBER_FIELD_IDEAL_NORM_IDEAL_NORM, NUMBER_FIELD_IDEAL_NORM_MUL,
        NUMBER_FIELD_IDEAL_NORM_MUL_Q, NUMBER_FIELD_IDEAL_NORM_POW,
        NUMBER_FIELD_IDEAL_NORM_TOWER, NUMBER_FIELD_IDEAL_NORM_VALUATION,
        NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_NORM_INTEGRAL,
        NUMBER_FIELD_PRIME_IDEALS_ABOVE, NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO,
        NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS, NUMBER_FIELD_TOWER_LAW,
        PRIME_IMP_RING_IDEAL, PRIME_SUBFIELD_MONOMORPHIC_IMAGE, RING_1,
        RING_DET_SUBRING, RING_HOMOMORPHISM_COMPOSE,
        RING_HOMOMORPHISM_SUBFIELD_INCLUSION, RING_IDEAL_IDEAL_GENERATED,
        RING_IDEAL_IDEAL_POW, RING_IDEAL_IDEAL_PROD, RING_IDEAL_IMP_SUBSET,
        RING_IDEAL_NUMBER_FIELD_DIFFERENT, RING_MUL, RING_MUL_IN_PRIME_IDEAL,
        RING_OF_INTEGERS, RING_OF_INTEGERS_IDEAL_EXTENSION,
        RING_OF_INTEGERS_IDEAL_GENERATED_SING_EQ_0, RING_OF_INTEGERS_LOCAL_BASIS,
        RING_OF_INTEGERS_SUBRING, RING_OF_INTEGERS_SUBSET,
        RING_OF_INTEGERS_SUBSET_CODIFFERENT, RING_POW, RING_POW_IN_PRIME_IDEAL, SUBSET,
        SUBSET_ANTISYM_EQ, SUBSET_TRANS, field_extension, number_field_codifferent, .. } := D.core1
  let { NUMBER_FIELD_BASIS_DISCRIMINANT_IN_NORM_DIFFERENT,
        NUMBER_FIELD_BASIS_DISCRIMINANT_TWIST,
        NUMBER_FIELD_BASIS_DISCRIMINANT_TWIST_LOCAL,
        NUMBER_FIELD_DIFFERENT_LOCAL_GENERATOR, .. } := BDiscriminantExtension01
  -- @@SCOPE END

  let NUMBER_FIELD_NORM_DIFFERENT_LOCAL_BASIS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r7 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    let r14 ← TAUT (← q r"(p ==> F) /\ q ==> ~p /\ q")
    prove
      r"!k:A ring l:B ring h p.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
          ==> ?w. free_basis (k,l) h (extension_degree(k,l) h) w /\
                  (!i. i < extension_degree(k,l) h
                       ==> w i IN ring_carrier(ring_of_integers l)) /\
                  ideal_valuation (ring_of_integers k) p
                    (ideal_generated (ring_of_integers k)
                       {basis_discriminant (k,l) h (extension_degree(k,l) h) w}) =
                  ideal_valuation (ring_of_integers k) p
                    (number_field_ideal_norm (k,l) h
                       (number_field_different (k,l) h))"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN SUBGOAL_THEN (← q r"dedekind_domain(ring_of_integers k:A ring)") ASSUME_TAC THENL [ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] RING_OF_INTEGERS_LOCAL_BASIS) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"n = extension_degree(k:A ring,l:B ring) h") THEN DISCH_THEN (X_CHOOSE_THEN (← q r"w:num->B") (X_CHOOSE_THEN (← q r"s:A") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (fun (_ : thm) => ALL_TAC) (CONJUNCTS_THEN2 (fun (_ : thm) => ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))))) THEN EXISTS_TAC (← q r"w:num->B") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_DIFFERENT_LOCAL_GENERATOR) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"d:B"), (← q r"t:A")] THEN STRIP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z15 ← (do let z16 ← (pure th); pure (concl z16)); pure (is_eq z15)) then (do let z17 ← (do let z18 ← (do let z19 ← (pure th); pure (concl z19)); liftExcept (rand z18)); canM (fun z20 => (do let z21 ← (pure z20); find_termM (fun z22 => (do let z24 ← (pure z22); let z23 ← (q r"number_field_different (k:A ring,l:B ring) h"); pure (z23 == z24))) z21)) z17) else pure false))))) THEN SUBGOAL_THEN (← q r"(t:A) IN ring_carrier k /\ (s:A) IN ring_carrier k /\
      (d:B) IN ring_carrier(ring_of_integers l) /\ d IN ring_carrier l") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET, RING_IDEAL_IMP_SUBSET, RING_IDEAL_NUMBER_FIELD_DIFFERENT], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"n:num"), (← q r"w:num->B"), (← q r"s:A"), (← q r"d:B"), (← q r"t:A")] NUMBER_FIELD_BASIS_DISCRIMINANT_TWIST_LOCAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"b:A") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"n:num"), (← q r"w:num->B"), (← q r"t:A"), (← q r"d:B")] NUMBER_FIELD_BASIS_DISCRIMINANT_TWIST) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ABBREV_TAC (← q r"a = ring_det k {i | i < n}
            (\i j. algebra_trace (k,l) (h:A->B)
                     (ring_mul l (ring_mul l (h t) (ring_inv l d))
                                 (ring_mul l ((w:num->B) i) (w j))))") THEN ABBREV_TAC (← q r"e = basis_discriminant (k,l) (h:A->B) n w") THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [EXPAND_TAC "a" THEN MATCH_MP_TAC RING_DET_SUBRING THEN REWRITE_TAC [RING_OF_INTEGERS_SUBRING, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN UNDISCH_TAC (← q r"ring_mul l ((h:A->B) t) (ring_inv l d) IN
                   number_field_codifferent (k,l) h") THEN REWRITE_TAC [number_field_codifferent, IN_ELIM_THM] THEN DISCH_THEN (MATCH_MP_TAC o CONJUNCT2) THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_MUL)) THEN ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"n:num"), (← q r"w:num->B"), (← q r"ring_1 l:B")] NUMBER_FIELD_CODIFFERENT_BASIS_DISCRIMINANT) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_OF_INTEGERS_SUBSET_CODIFFERENT) THEN ASM_REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_1))], ASM_REWRITE_TAC [] THEN STRIP_TAC] THEN SUBGOAL_THEN (← q r"ring_mul k t (ring_pow k s 2) IN ring_carrier(ring_of_integers k) /\
      ring_pow k t n IN ring_carrier(ring_of_integers (k:A ring)) /\
      algebra_norm (k,l) (h:A->B) d IN ring_carrier(ring_of_integers k) /\
      ~(algebra_norm (k,l) h d = ring_0 k)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") RING_POW)), (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") RING_MUL)), NUMBER_FIELD_NORM_INTEGRAL, ALGEBRA_NORM_EQ_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"~((a:A) IN p) /\ ~(ring_pow k t n IN (p:A->bool))") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r14 THEN CONJ_TAC THENL [DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_pow k (ring_mul k t (ring_pow k s 2)) n IN (p:A->bool)") MP_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z8 ← (do let z9 ← (pure th); pure (concl z9)); pure (is_eq z8)) then (do let z13 ← (q r"ring_mul k (b:A) a"); let z12 ← (do let z10 ← (do let z11 ← (pure th); pure (concl z11)); liftExcept (lhand z10)); pure (z12 == z13)) else pure false))))) THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") IN_RING_IDEAL_LMUL)) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], ALL_TAC], ALL_TAC] THEN ASM_SIMP_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") RING_POW_IN_PRIME_IDEAL)), (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") RING_MUL_IN_PRIME_IDEAL)), (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") RING_POW))] THEN CONV_TAC NUM_REDUCE_CONV, ALL_TAC] THEN SUBGOAL_THEN (← q r"!x:A. x IN ring_carrier(ring_of_integers k) /\ ~(x IN p)
            ==> ~(x = ring_0 k) /\
                ideal_valuation (ring_of_integers k) p
                  (ideal_generated (ring_of_integers k) {x}) = 0") ASSUME_TAC THENL [X_GEN_TAC (← q r"x:A") THEN STRIP_TAC THEN MATCH_MP_TAC r7 THEN CONJ_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~(ring_0 k IN (p:A->bool))") THEN REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:A->bool")] IN_RING_IDEAL_0) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS], DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:A->bool"), (← q r"x:A"), (← q r"1")] DEDEKIND_IN_IDEAL_POW_VALUATION) THEN ASM_SIMP_TAC [IDEAL_POW_1, PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS] THEN ARITH_TAC, ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o ((AP_TERM (← q r"\x:A. ideal_valuation (ring_of_integers k) p
              (ideal_generated (ring_of_integers k) {x})")) o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_eq z1)) then (do let z6 ← (q r"ring_mul k (algebra_norm (k,l) (h:A->B) d) a"); let z5 ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); liftExcept (lhand z3)); pure (z5 == z6)) else pure false))))) THEN REWRITE_TAC [] THEN ASM_SIMP_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") IDEAL_VALUATION_PRINCIPAL_MUL))] THEN ARITH_TAC)

  let NUMBER_FIELD_DISCRIMINANT_BASES ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (q ==> r) ==> (p <=> q) ==> r")
    let r2 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!k:A ring l:B ring h.
          field k /\ number_field l /\ ring_homomorphism(k,l) h
          ==> number_field_ideal_norm (k,l) h (number_field_different (k,l) h) =
              ideal_generated (ring_of_integers k)
                {basis_discriminant (k,l) h (extension_degree(k,l) h) w |
                 w | free_basis (k,l) h (extension_degree(k,l) h) w /\
                     !i. i < extension_degree(k,l) h
                         ==> w i IN ring_carrier(ring_of_integers l)}"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN SUBGOAL_THEN (← q r"dedekind_domain(ring_of_integers k:A ring)") ASSUME_TAC THENL [ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS], ALL_TAC] THEN ABBREV_TAC (← q r"n = extension_degree(k:A ring,l:B ring) h") THEN ABBREV_TAC (← q r"S = {basis_discriminant (k,l) (h:A->B) n w |
           w | free_basis (k,l) h n w /\
               !i. i < n ==> w i IN ring_carrier(ring_of_integers l)}") THEN ABBREV_TAC (← q r"N = number_field_ideal_norm (k,l) (h:A->B)
            (number_field_different (k,l) h)") THEN SUBGOAL_THEN (← q r"(S:A->bool) SUBSET N") ASSUME_TAC THENL [EXPAND_TAC "S" THEN EXPAND_TAC "N" THEN REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC NUMBER_FIELD_BASIS_DISCRIMINANT_IN_NORM_DIFFERENT THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers k) (N:A->bool) /\
                  ~(N = {ring_0 k})") STRIP_ASSUME_TAC THENL [EXPAND_TAC "N" THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_IDEAL, NUMBER_FIELD_IDEAL_NORM_EQ_0, RING_IDEAL_NUMBER_FIELD_DIFFERENT, NUMBER_FIELD_DIFFERENT_NONZERO], ALL_TAC] THEN SUBGOAL_THEN (← q r"(S:A->bool) SUBSET ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET_TRANS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_FREE_BASIS_INTEGRAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"w0:num->B") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"basis_discriminant (k,l) (h:A->B) n w0 IN S /\
      ~(basis_discriminant (k,l) h n w0 = ring_0 k)") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [EXPAND_TAC "S" THEN REWRITE_TAC [IN_ELIM_THM] THEN EXISTS_TAC (← q r"w0:num->B") THEN ASM_REWRITE_TAC [], MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"n:num"), (← q r"w0:num->B"), (← q r"ring_1 l:B")] NUMBER_FIELD_CODIFFERENT_BASIS_DISCRIMINANT) THEN ANTS_TAC THENL [ALL_TAC, SIMP_TAC []] THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_OF_INTEGERS_SUBSET_CODIFFERENT) THEN ASM_REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_1))]], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(ideal_generated (ring_of_integers k) S = {ring_0 k:A})") ASSUME_TAC THENL [DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"S:A->bool"), (← q r"basis_discriminant (k,l) (h:A->B) n w0")] IDEAL_GENERATED_INC) THEN ASM_REWRITE_TAC [IN_SING], ALL_TAC] THEN REWRITE_TAC [(← GSYM SUBSET_ANTISYM_EQ)] THEN CONJ_TAC THENL [ALL_TAC, MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC []] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"N:A->bool"), (← q r"ideal_generated (ring_of_integers k) (S:A->bool)")] DEDEKIND_IDEAL_SUBSET_VALUATION) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN X_GEN_TAC (← q r"p:A->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_NORM_DIFFERENT_LOCAL_BASIS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"w:num->B") STRIP_ASSUME_TAC) THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); pure (is_eq z3)) then (do let z9 ← (q r"N:A->bool"); let z8 ← (do let z5 ← (do let z6 ← (do let z7 ← (pure th); pure (concl z7)); liftExcept (rand z6)); liftExcept (rand z5)); pure (z8 == z9)) else pure false))))) THEN SUBGOAL_THEN (← q r"basis_discriminant (k,l) (h:A->B) n w IN S /\
      basis_discriminant (k,l) h n w IN ring_carrier(ring_of_integers k) /\
      ~(basis_discriminant (k,l) h n w = ring_0 k)") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r2 THEN CONJ_TAC THENL [EXPAND_TAC "S" THEN REWRITE_TAC [IN_ELIM_THM] THEN EXISTS_TAC (← q r"w:num->B") THEN ASM_REWRITE_TAC [], DISCH_TAC THEN CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC]] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"n:num"), (← q r"w:num->B"), (← q r"ring_1 l:B")] NUMBER_FIELD_CODIFFERENT_BASIS_DISCRIMINANT) THEN ANTS_TAC THENL [ALL_TAC, SIMP_TAC []] THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_OF_INTEGERS_SUBSET_CODIFFERENT) THEN ASM_REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_1))], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ideal_generated (ring_of_integers k)
                      {basis_discriminant (k,l) (h:A->B) n w}"), (← q r"ideal_generated (ring_of_integers k) (S:A->bool)")] DEDEKIND_IDEAL_SUBSET_VALUATION) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, RING_OF_INTEGERS, RING_OF_INTEGERS_IDEAL_GENERATED_SING_EQ_0] THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_MONO THEN ASM SET_TAC [], DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC []])

  let NUMBER_FIELD_DISCRIMINANT_RAMIFIED ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"1 <= (n:num) <=> ~(n = 0)")
    prove
      r"!k:A ring l:B ring h p.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
          ==> (number_field_ideal_norm (k,l) h (number_field_different (k,l) h)
               SUBSET p <=>
               ?P. prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P /\
                   1 < ramification_index
                         (ring_of_integers k,ring_of_integers l) h P)"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN SUBGOAL_THEN (← q r"dedekind_domain(ring_of_integers k:A ring) /\
      dedekind_domain(ring_of_integers l:B ring)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_IDEAL_NUMBER_FIELD_DIFFERENT) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_DIFFERENT_NONZERO) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"D = number_field_different (k:A ring,l:B ring) h") THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:A->bool"), (← q r"number_field_ideal_norm (k:A ring,l:B ring) h D"), (← q r"1")] DEDEKIND_IDEAL_SUBSET_POW_VALUATION) THEN ASM_SIMP_TAC [IDEAL_POW_1, PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS, NUMBER_FIELD_IDEAL_NORM_IDEAL, NUMBER_FIELD_IDEAL_NORM_EQ_0] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_VALUATION] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_PRIME_IDEALS_ABOVE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN REWRITE_TAC [r1] THEN ASM_SIMP_TAC [NSUM_EQ_0_IFF, IN_ELIM_THM, MULT_EQ_0] THEN REWRITE_TAC [NOT_FORALL_THM, NOT_IMP, DE_MORGAN_THM] THEN AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"P:B->bool") THEN ASM_CASES_TAC (← q r"prime_ideal (ring_of_integers l) (P:B->bool)") THEN ASM_REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"IMAGE (h:A->B) p SUBSET P") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"~(P = {ring_0 l:B})") ASSUME_TAC THENL [MATCH_MP_TAC NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO THEN MAP_EVERY EXISTS_TAC [(← q r"k:A ring"), (← q r"h:A->B"), (← q r"p:A->bool")] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"P:B->bool")] NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"P:B->bool")] NUMBER_FIELD_DIFFERENT_RAMIFIED) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"P:B->bool"), (← q r"D:B->bool"), (← q r"1")] DEDEKIND_IDEAL_SUBSET_POW_VALUATION) THEN ASM_SIMP_TAC [IDEAL_POW_1, PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC)

  let NUMBER_FIELD_DISCRIMINANT_TOWER ← prove
    r"!k:A ring l:B ring m:C ring h1 h2.
        field k /\ field l /\ number_field m /\
        ring_homomorphism(k,l) h1 /\ ring_homomorphism(l,m) h2
        ==> number_field_ideal_norm (k,m) (h2 o h1)
              (number_field_different (k,m) (h2 o h1)) =
            ideal_prod (ring_of_integers k)
              (ideal_pow (ring_of_integers k)
                 (number_field_ideal_norm (k,l) h1
                    (number_field_different (k,l) h1))
                 (extension_degree(l,m) h2))
              (number_field_ideal_norm (k,l) h1
                 (number_field_ideal_norm (l,m) h2
                    (number_field_different (l,m) h2)))"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"number_field(l:B ring)") ASSUME_TAC THENL [ASM_MESON_TAC [NUMBER_FIELD_HOMOMORPHIC_PREIMAGE], ALL_TAC] THEN ASM_SIMP_TAC [NUMBER_FIELD_DIFFERENT_TOWER, RING_IDEAL_IDEAL_PROD, NUMBER_FIELD_IDEAL_NORM_TOWER] THEN SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers l) (number_field_different (k,l) (h1:A->B)) /\
    ring_ideal (ring_of_integers m) (number_field_different (l,m) (h2:B->C))") STRIP_ASSUME_TAC THENL [REWRITE_TAC [RING_IDEAL_NUMBER_FIELD_DIFFERENT], ALL_TAC] THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_MUL, RING_IDEAL_IDEAL_GENERATED, NUMBER_FIELD_IDEAL_NORM_EXTENSION, NUMBER_FIELD_IDEAL_NORM_IDEAL, RING_IDEAL_IDEAL_POW, NUMBER_FIELD_IDEAL_NORM_POW] THEN MATCH_MP_TAC IDEAL_PROD_COMM THEN CONJ_TAC THEN MATCH_MP_TAC RING_IDEAL_IMP_SUBSET THEN REWRITE_TAC [NUMBER_FIELD_IDEAL_NORM_IDEAL, RING_IDEAL_IDEAL_POW])

  let NUMBER_FIELD_DISCRIMINANT_TOWER_Q ← prove
    r"!k:A ring l:B ring h.
        field k /\ number_field l /\ ring_homomorphism(k,l) h
        ==> abs(number_field_discriminant l) =
            abs(number_field_discriminant k) pow extension_degree(k,l) h *
            &(ideal_norm (ring_of_integers k)
                (number_field_ideal_norm (k,l) h
                   (number_field_different (k,l) h)))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP NUMBER_FIELD_IMP_FIELD) o (checkM (fun th => (do let z3 ← (q r"number_field(l:B ring)"); let z2 ← (do let z1 ← (pure th); pure (concl z1)); pure (z2 == z3)))))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o ((MATCH_MP FINITE_IMP_FIELD_EXTENSION) o CONJUNCT1)) THEN SUBGOAL_THEN (← q r"ideal_norm (ring_of_integers l)
      (number_field_different (subfield_generated l {ring_0 l},l) (I:B->B)) =
    ideal_norm (ring_of_integers k)
      (number_field_different (subfield_generated k {ring_0 k},k) (I:A->A))
    EXP extension_degree(k,l) (h:A->B) *
    ideal_norm (ring_of_integers k)
      (number_field_ideal_norm (k,l) h (number_field_different (k,l) h))") MP_TAC THENL [ALL_TAC, ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_DIFFERENT] THEN DISCH_THEN (MP_TAC o (AP_TERM (← q r"int_of_num"))) THEN REWRITE_TAC [(← GSYM INT_OF_NUM_MUL), (← GSYM INT_OF_NUM_POW)] THEN SIMP_TAC [INT_OF_NUM_OF_INT, INT_ABS_POS]] THEN SUBGOAL_THEN (← q r"number_field_different (subfield_generated l {ring_0 l},l) (I:B->B) =
    number_field_different (subfield_generated k {ring_0 k},l)
      ((h:A->B) o I)") SUBST1_TAC THENL [CONV_TAC SYM_CONV THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_0 k:A}"), (← q r"subfield_generated l {ring_0 l:B}"), (← q r"l:B ring"), (← q r"(h:A->B) o I"), (← q r"I:B->B")] NUMBER_FIELD_CODIFFERENT_EQ_IMAGE) THEN ANTS_TAC THENL [ALL_TAC, SIMP_TAC []] THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, IMAGE_I] THEN CONJ_TAC THENL [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC (← q r"k:A ring") THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION], REWRITE_TAC [IMAGE_o, IMAGE_I] THEN MATCH_MP_TAC PRIME_SUBFIELD_MONOMORPHIC_IMAGE THEN ASM_MESON_TAC [field_extension]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"I:A->A"), (← q r"h:A->B")] NUMBER_FIELD_DIFFERENT_TOWER) THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, RING_HOMOMORPHISM_SUBFIELD_INCLUSION] THEN DISCH_THEN SUBST1_TAC THEN SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers k)
      (number_field_different (subfield_generated k {ring_0 k},k) (I:A->A)) /\
    ~(number_field_different (subfield_generated k {ring_0 k},k) (I:A->A) =
      {ring_0 k}) /\
    ring_ideal (ring_of_integers l) (number_field_different (k,l) (h:A->B)) /\
    ~(number_field_different (k,l) (h:A->B) = {ring_0 l})") STRIP_ASSUME_TAC THENL [REWRITE_TAC [RING_IDEAL_NUMBER_FIELD_DIFFERENT] THEN ASM_SIMP_TAC [NUMBER_FIELD_DIFFERENT_NONZERO, FIELD_SUBFIELD_GENERATED, NUMBER_FIELD_IMP_FIELD, RING_HOMOMORPHISM_SUBFIELD_INCLUSION], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"number_field_different (subfield_generated k {ring_0 k},k)
                    (I:A->A)")] RING_OF_INTEGERS_IDEAL_EXTENSION) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"number_field_different (k,l) (h:A->B)"), (← q r"ideal_generated (ring_of_integers l)
                   (IMAGE (h:A->B)
                     (number_field_different
                       (subfield_generated k {ring_0 k},k) I))")] NUMBER_FIELD_IDEAL_NORM_MUL_Q) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_EXTENSION_Q, NUMBER_FIELD_IDEAL_NORM_IDEAL_NORM] THEN REWRITE_TAC [MULT_SYM])

  let NUMBER_FIELD_DISCRIMINANT_POW_DIVIDES ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← INTEGER_RULE (← q r"abs(a:int) divides abs(b) ==> a divides b")
    prove
      r"!k:A ring l:B ring h.
          field k /\ number_field l /\ ring_homomorphism(k,l) h
          ==> (number_field_discriminant k pow extension_degree(k,l) h) divides
              number_field_discriminant l"
      (REPEAT STRIP_TAC THEN MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [NUMBER_FIELD_DISCRIMINANT_TOWER_Q, INT_ABS_POW] THEN CONV_TAC INTEGER_RULE)

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_NORM_DIFFERENT_LOCAL_BASIS, NUMBER_FIELD_DISCRIMINANT_BASES,
           NUMBER_FIELD_DISCRIMINANT_RAMIFIED, NUMBER_FIELD_DISCRIMINANT_TOWER,
           NUMBER_FIELD_DISCRIMINANT_TOWER_Q, NUMBER_FIELD_DISCRIMINANT_POW_DIVIDES }
  -- @@RETURN END

end HolANT.DiscriminantExtension
