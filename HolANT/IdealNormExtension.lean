/- ========================================================================= -/
/- ANT: The ideal norm of an extension of number fields                    -/
/- ========================================================================= -/
/- File: HolANT/IdealNormExtension.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/ideal_norm_extension.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antidealnormextensiondiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/frag.ml, Library/grouptheory.ml, Library/symmetric_group.ml, Library/galois.ml, ANT/ideal_arith.ml, Library/products.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/ideal_norm.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/prime_split.ml, ANT/classgroup.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/relative_degree.ml, ANT/nf_valuation.ml, ANT/integrality.ml, Library/ring_groups.ml, Library/finite_fields.ml, ANT/decomposition.ml, ANT/finite_field_trace.ml, ANT/ramification.ml, ANT/splitting_types.ml, ANT/nf_decomposition.ml, ANT/conjugate_ideals.ml, Library/integer.ml, Library/multiplicative.ml, Library/primitive.ml, ANT/dedekind_kummer.ml, ANT/decomposition_field.ml, ANT/split_primes.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.IdealNormExtension fills them).

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
import HolLibrary.Frag
import HolLibrary.GroupTheory
import HolLibrary.SymmetricGroup
import HolLibrary.Galois
import HolANT.IdealArith
import HolLibrary.Products
import HolANT.Algmisc
import HolANT.Integral
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.IdealNorm
import HolLibrary.Isum
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolANT.RingOfIntegers
import HolANT.NormIndex
import HolANT.PrimeSplit
import HolANT.Classgroup
import HolANT.Discriminant
import HolANT.TraceForm
import HolANT.RelativeSplit
import HolANT.RelativeDegree
import HolANT.NfValuation
import HolANT.Integrality
import HolLibrary.RingGroups
import HolLibrary.FiniteFields
import HolANT.Decomposition
import HolANT.FiniteFieldTrace
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
open HolANT.DedekindValuation
open HolANT.IdealNorm
open HolANT.Zlattice
open HolANT.Numfield
open HolANT.RingOfIntegers
open HolANT.NormIndex
open HolANT.PrimeSplit
open HolANT.Classgroup
open HolANT.Discriminant
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.RelativeDegree
open HolANT.NfValuation
open HolANT.Integrality
open HolANT.Decomposition
open HolANT.FiniteFieldTrace
open HolANT.Ramification
open HolANT.SplittingTypes
open HolANT.NfDecomposition
open HolANT.ConjugateIdeals
open HolANT.DedekindKummer
open HolANT.DecompositionField
open HolANT.SplitPrimes

namespace HolANT.IdealNormExtension

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ALGEBRA_NORM_EQ_0 ALGEBRA_NORM_MUL ALGEBRA_TRACE_NORM_GALOIS
   ALGEBRA_TRACE_NORM_INTERMEDIATE CONTRAPOS_THM DEDEKIND_IDEAL_EQ_VALUATION
   DEDEKIND_IDEAL_INDUCT DEDEKIND_IDEAL_SUBSET_POW_VALUATION
   DEDEKIND_IDEAL_SUBSET_VALUATION DEDEKIND_IDEAL_WEAK_APPROXIMATION
   DEDEKIND_IMP_INTEGRAL_DOMAIN DEDEKIND_IN_IDEAL_POW_VALUATION
   DEDEKIND_RING_OF_INTEGERS EQ_MULT_LCANCEL EQ_TRANS EXISTS_UNIQUE_THM
   EXTENSION EXTENSION_DEGREE_EQ_0 FINITE_GALOIS_GROUP
   FINITE_IMP_FIELD_EXTENSION FORALL_IN_GSPEC FORALL_IN_IMAGE FUN_IN_IMAGE
   GALOIS_GROUP_IMAGE_IDEAL_GENERATED GALOIS_GROUP_RING_OF_INTEGERS_AUTOMORPHISM
   GALOIS_GROUP_RING_OF_INTEGERS_IDEAL GALOIS_IMP_FIELD_EXTENSION
   IDEAL_GENERATED_0 IDEAL_GENERATED_EQ_0 IDEAL_GENERATED_IMAGE_IDEAL_GENERATED
   IDEAL_GENERATED_INC IDEAL_GENERATED_MINIMAL IDEAL_NORM_CARRIER
   IDEAL_NORM_IDEAL_POW IDEAL_OF_VALUATIONS_UNIQUE IDEAL_POW_0 IDEAL_POW_CARRIER
   IDEAL_POW_EQ_ZERO IDEAL_POW_SUC IDEAL_PRODUCT_EQ IDEAL_PRODUCT_EQ_ZERO
   IDEAL_PRODUCT_PRINCIPAL IDEAL_PROD_EQ_ZERO IDEAL_PROD_LZERO IDEAL_PROD_RZERO
   IDEAL_VALUATION_CARRIER IDEAL_VALUATION_IDEAL_POW IDEAL_VALUATION_IDEAL_PROD
   IDEAL_VALUATION_IDEAL_PRODUCT IDEAL_VALUATION_PRIME
   IDEAL_VALUATION_PRINCIPAL_POW IMAGE_CLAUSES IMAGE_o IMP_CONJ IN_ELIM_THM
   IN_IDEAL_GENERATED_SELF IN_IDEAL_GENERATED_SING_EQ IN_RING_IDEAL_0 IN_SING
   LEFT_ADD_DISTRIB LEFT_IMP_EXISTS_THM LE_ANTISYM LE_MULT_LCANCEL
   MEMBER_NOT_EMPTY MULT_CLAUSES NSUM_ADD NSUM_DELTA NSUM_EQ NSUM_EQ_0
   NSUM_GROUP NSUM_LE NSUM_LMUL NSUM_RMUL NUMBER_FIELD_FUNDAMENTAL_IDENTITY
   NUMBER_FIELD_GALOIS_CLOSURE NUMBER_FIELD_GALOIS_PRODUCT_PRIME
   NUMBER_FIELD_HOMOMORPHIC_PREIMAGE NUMBER_FIELD_IDEAL_NORM_MUL_Q
   NUMBER_FIELD_IDEAL_VALUATION_EXTENSION NUMBER_FIELD_IMP_FIELD
   NUMBER_FIELD_NORM_INTEGRAL NUMBER_FIELD_NORM_MULTIPLE
   NUMBER_FIELD_PRIME_IDEALS_ABOVE NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO
   NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS NUMBER_FIELD_RESIDUE_DEGREE_TOWER
   NUMBER_FIELD_TOWER_LAW PRIME_IDEAL_IMP_SUBSET PRIME_IMP_PROPER_IDEAL
   PRIME_IMP_RING_IDEAL PROPER_IDEAL_ALT RIGHT_FORALL_IMP_THM RING_0
   RING_HOMOMORPHISM_0 RING_HOMOMORPHISM_COMPOSE RING_HOMOMORPHISM_IN_CARRIER
   RING_HOMOMORPHISM_RING_OF_INTEGERS RING_IDEAL_CARRIER
   RING_IDEAL_IDEAL_GENERATED RING_IDEAL_IDEAL_POW RING_IDEAL_IDEAL_PROD
   RING_IDEAL_IDEAL_PRODUCT RING_IDEAL_IMP_SUBSET RING_MONOMORPHISM_EQ_0
   RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_MONOMORPHISM_RING_OF_INTEGERS
   RING_OF_INTEGERS RING_OF_INTEGERS_FINITE_QUOTIENT
   RING_OF_INTEGERS_IDEAL_EXTENSION RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME
   RING_OF_INTEGERS_IDEAL_GENERATED_SING_EQ_0 RING_OF_INTEGERS_IDEAL_NORM_PRIME
   RING_OF_INTEGERS_PRIME_IDEAL_BELOW RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION
   RING_OF_INTEGERS_SUBSET RING_PRODUCT_RING_OF_INTEGERS SING_SUBSET SUBSET
   SUBSET_ANTISYM_EQ field_extension o_THM ring_divides : thm)
  deriving Inhabited

/-- What ideal_norm_extension.ml uses from Session besides theorems. -/
structure IdealNormExtensionDeps where
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
/- ideal_norm_extension.ml phrases from line 102 to 627                   -/
/- ---------------------------------------------------------------------- -/

structure IdealNormExtension01 where
  -- @@FIELDS
  RING_OF_INTEGERS_IDEAL_EXTENSION_CONTRACTION : thm
  NUMBER_FIELD_NORM_EXPONENT_ADD : thm
  NUMBER_FIELD_NORM_EXPONENT_PRIME : thm
  NUMBER_FIELD_NORM_EXPONENT_EXTENSION : thm
  NUMBER_FIELD_NORM_EXPONENT_MONO : thm
  NUMBER_FIELD_NORM_EXPONENT_TOWER : thm
  NUMBER_FIELD_GALOIS_PRODUCT_VALUATION : thm
  NUMBER_FIELD_GALOIS_NORM_VALUATION : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupIdealNormExtension01 [HolBase] (D : IdealNormExtensionDeps) :
    ExceptT String IO IdealNormExtension01 := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON, MESON_TAC, SET_TAC, TAUT, .. } := D
  let { ALGEBRA_NORM_EQ_0, ALGEBRA_TRACE_NORM_GALOIS, DEDEKIND_IDEAL_INDUCT,
        DEDEKIND_IDEAL_SUBSET_VALUATION, DEDEKIND_RING_OF_INTEGERS, EQ_MULT_LCANCEL,
        EQ_TRANS, EXISTS_UNIQUE_THM, EXTENSION, FINITE_GALOIS_GROUP,
        FINITE_IMP_FIELD_EXTENSION, FORALL_IN_IMAGE, FUN_IN_IMAGE,
        GALOIS_GROUP_IMAGE_IDEAL_GENERATED, GALOIS_GROUP_RING_OF_INTEGERS_AUTOMORPHISM,
        GALOIS_GROUP_RING_OF_INTEGERS_IDEAL, GALOIS_IMP_FIELD_EXTENSION,
        IDEAL_GENERATED_0, IDEAL_GENERATED_EQ_0, IDEAL_GENERATED_IMAGE_IDEAL_GENERATED,
        IDEAL_GENERATED_INC, IDEAL_GENERATED_MINIMAL, IDEAL_PRODUCT_EQ,
        IDEAL_PRODUCT_PRINCIPAL, IDEAL_VALUATION_CARRIER, IDEAL_VALUATION_IDEAL_POW,
        IDEAL_VALUATION_IDEAL_PROD, IDEAL_VALUATION_IDEAL_PRODUCT,
        IDEAL_VALUATION_PRIME, IMAGE_CLAUSES, IMAGE_o, IMP_CONJ, IN_ELIM_THM,
        IN_IDEAL_GENERATED_SELF, IN_RING_IDEAL_0, IN_SING, LEFT_ADD_DISTRIB,
        LE_MULT_LCANCEL, MEMBER_NOT_EMPTY, MULT_CLAUSES, NSUM_ADD, NSUM_DELTA, NSUM_EQ,
        NSUM_EQ_0, NSUM_GROUP, NSUM_LE, NSUM_LMUL, NSUM_RMUL,
        NUMBER_FIELD_FUNDAMENTAL_IDENTITY, NUMBER_FIELD_GALOIS_PRODUCT_PRIME,
        NUMBER_FIELD_HOMOMORPHIC_PREIMAGE, NUMBER_FIELD_IDEAL_VALUATION_EXTENSION,
        NUMBER_FIELD_NORM_INTEGRAL, NUMBER_FIELD_PRIME_IDEALS_ABOVE,
        NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO,
        NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS, NUMBER_FIELD_RESIDUE_DEGREE_TOWER,
        NUMBER_FIELD_TOWER_LAW, PRIME_IDEAL_IMP_SUBSET, PRIME_IMP_PROPER_IDEAL,
        PRIME_IMP_RING_IDEAL, PROPER_IDEAL_ALT, RING_HOMOMORPHISM_0,
        RING_HOMOMORPHISM_COMPOSE, RING_HOMOMORPHISM_IN_CARRIER,
        RING_HOMOMORPHISM_RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED,
        RING_IDEAL_IMP_SUBSET, RING_MONOMORPHISM_EQ_0,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MONOMORPHISM_RING_OF_INTEGERS,
        RING_OF_INTEGERS, RING_OF_INTEGERS_IDEAL_EXTENSION,
        RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME,
        RING_OF_INTEGERS_IDEAL_GENERATED_SING_EQ_0, RING_OF_INTEGERS_PRIME_IDEAL_BELOW,
        RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION, RING_OF_INTEGERS_SUBSET,
        RING_PRODUCT_RING_OF_INTEGERS, SING_SUBSET, SUBSET, field_extension, o_THM, .. } := D.core1
  -- @@SCOPE END

  let RING_OF_INTEGERS_IDEAL_EXTENSION_CONTRACTION ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (q ==> r) ==> (p <=> q) ==> r")
    let r4 ← TAUT (← q r"q /\ (p ==> r) ==> (p <=> q) ==> r")
    prove
      r"!k:A ring l:B ring h j.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          ring_ideal (ring_of_integers k) j
          ==> {x | x IN ring_carrier(ring_of_integers k) /\
                   h x IN ideal_generated (ring_of_integers l) (IMAGE h j)} =
              j"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (MP_TAC o ((MATCH_MP FINITE_IMP_FIELD_EXTENSION) o CONJUNCT1)) THEN REWRITE_TAC [field_extension] THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_RING_OF_INTEGERS)) THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) o (checkM (fun th => (do let z10 ← (q r"ring_monomorphism(ring_of_integers k,ring_of_integers l) (h:A->B)"); let z9 ← (do let z8 ← (pure th); pure (concl z8)); pure (z9 == z10)))))) THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP (← REWRITE_RULE [IMP_CONJ] RING_HOMOMORPHISM_IN_CARRIER)) o (checkM (fun th => (do let z7 ← (q r"ring_homomorphism(ring_of_integers k,ring_of_integers l) (h:A->B)"); let z6 ← (do let z5 ← (pure th); pure (concl z5)); pure (z6 == z7)))))) THEN ABBREV_TAC (← q r"J = ideal_generated (ring_of_integers l) (IMAGE (h:A->B) j)") THEN SUBGOAL_THEN (← q r"(j:A->bool) SUBSET ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"x:A") THEN REWRITE_TAC [IN_ELIM_THM] THEN EQ_TAC THENL [STRIP_TAC, DISCH_TAC THEN CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN EXPAND_TAC "J" THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN ASM_SIMP_TAC [FUN_IN_IMAGE] THEN ASM SET_TAC []] THEN ASM_CASES_TAC (← q r"x = ring_0 k:A") THENL [ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"j:A->bool")] IN_RING_IDEAL_0) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN ASM_CASES_TAC (← q r"j = {ring_0 k:A}") THENL [UNDISCH_TAC (← q r"(h:A->B) x IN J") THEN EXPAND_TAC "J" THEN REWRITE_TAC [(← ASSUME (← q r"j = {ring_0 k:A}")), IMAGE_CLAUSES] THEN REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_0 (← ASSUME (← q r"ring_homomorphism(k:A ring,l:B ring) h")))] THEN REWRITE_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") IDEAL_GENERATED_0)), IN_SING] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"x:A")] RING_MONOMORPHISM_EQ_0) THEN ANTS_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [IN_SING], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ideal_generated (ring_of_integers k) {x:A}"), (← q r"j:A->bool")] DEDEKIND_IDEAL_SUBSET_VALUATION) THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0, RING_OF_INTEGERS] THEN MATCH_MP_TAC r4 THEN CONJ_TAC THENL [ALL_TAC, DISCH_THEN (MATCH_MP_TAC o (REWRITE_RULE [SUBSET])) THEN ASM_REWRITE_TAC [IN_IDEAL_GENERATED_SELF]] THEN X_GEN_TAC (← q r"p:A->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_PRIME_IDEALS_ABOVE) THEN ASM_REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY), IN_ELIM_THM] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"P:B->bool") STRIP_ASSUME_TAC) o CONJUNCT2) THEN SUBGOAL_THEN (← q r"~(P = {ring_0 l:B})") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME) THEN ASM_REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN DISCH_THEN (fun z2 => tactic_of do pure (MP_TAC (← SPEC (← q r"P:B->bool") (← (do let z3 ← (pure (CONJUNCTS z2)); liftExcept (last z3)))))) THEN ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"P:B->bool")] NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"P:B->bool"), (← q r"ideal_generated (ring_of_integers k) {x:A}")] NUMBER_FIELD_IDEAL_VALUATION_EXTENSION) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"P:B->bool"), (← q r"j:A->bool")] NUMBER_FIELD_IDEAL_VALUATION_EXTENSION) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") IDEAL_GENERATED_EQ_0))] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring"), (← q r"h:A->B"), (← q r"{x:A}")] IDEAL_GENERATED_IMAGE_IDEAL_GENERATED) THEN ASM_SIMP_TAC [SING_SUBSET, IMAGE_CLAUSES] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN REPEAT DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"ideal_generated (ring_of_integers l) {(h:A->B) x}"), (← q r"J:B->bool")] DEDEKIND_IDEAL_SUBSET_VALUATION) THEN ANTS_TAC THENL [ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0, RING_OF_INTEGERS] THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0, RING_OF_INTEGERS_SUBSET, SUBSET], EXPAND_TAC "J" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"j:A->bool")] RING_OF_INTEGERS_IDEAL_EXTENSION) THEN ASM_SIMP_TAC []], ALL_TAC] THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET] THEN EXPAND_TAC "J" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED], DISCH_THEN (MP_TAC o (SPEC (← q r"P:B->bool")))] THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN SIMP_TAC [LE_MULT_LCANCEL] THEN ASM_ARITH_TAC)

  let NUMBER_FIELD_NORM_EXPONENT_ADD ← prove
    r"!k:A ring l:B ring h p J1 J2.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        ring_ideal (ring_of_integers l) J1 /\ ~(J1 = {ring_0 l}) /\
        ring_ideal (ring_of_integers l) J2 /\ ~(J2 = {ring_0 l})
        ==> nsum {P | prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P}
              (\P. residue_degree (ring_of_integers k,ring_of_integers l) h P *
                   ideal_valuation (ring_of_integers l) P
                     (ideal_prod (ring_of_integers l) J1 J2)) =
            nsum {P | prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P}
              (\P. residue_degree (ring_of_integers k,ring_of_integers l) h P *
                   ideal_valuation (ring_of_integers l) P J1) +
            nsum {P | prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P}
              (\P. residue_degree (ring_of_integers k,ring_of_integers l) h P *
                   ideal_valuation (ring_of_integers l) P J2)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_PRIME_IDEALS_ABOVE) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_SIMP_TAC [(← GSYM NSUM_ADD)] THEN MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC (← q r"P:B->bool") THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN REWRITE_TAC [(← GSYM LEFT_ADD_DISTRIB)] THEN AP_TERM_TAC THEN MATCH_MP_TAC IDEAL_VALUATION_IDEAL_PROD THEN ASM_SIMP_TAC [RING_OF_INTEGERS, DEDEKIND_RING_OF_INTEGERS] THEN MATCH_MP_TAC NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO THEN MAP_EVERY EXISTS_TAC [(← q r"k:A ring"), (← q r"h:A->B"), (← q r"p:A->bool")] THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_NORM_EXPONENT_PRIME ← prove
    r"!k:A ring l:B ring h p q Q.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers k) q /\ ~(q = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) Q /\ IMAGE h q SUBSET Q
        ==> nsum {P | prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P}
              (\P. residue_degree (ring_of_integers k,ring_of_integers l) h P *
                   ideal_valuation (ring_of_integers l) P Q) =
            if q = p
            then residue_degree (ring_of_integers k,ring_of_integers l) h Q
            else 0"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"~(Q = {ring_0 l:B})") ASSUME_TAC THENL [MATCH_MP_TAC NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO THEN MAP_EVERY EXISTS_TAC [(← q r"k:A ring"), (← q r"h:A->B"), (← q r"q:A->bool")] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN TRANS_TAC EQ_TRANS (← q r"nsum {P | prime_ideal (ring_of_integers l) P /\ IMAGE (h:A->B) p SUBSET P}
         (\P. if P = Q
              then residue_degree (ring_of_integers k,ring_of_integers l) h Q
              else 0)") THEN CONJ_TAC THENL [MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC (← q r"P:B->bool") THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"P:B->bool"), (← q r"Q:B->bool")] IDEAL_VALUATION_PRIME) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_OF_INTEGERS, DEDEKIND_RING_OF_INTEGERS] THEN MATCH_MP_TAC NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO THEN MAP_EVERY EXISTS_TAC [(← q r"k:A ring"), (← q r"h:A->B"), (← q r"p:A->bool")] THEN ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN ASM_CASES_TAC (← q r"P:B->bool = Q") THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN ASM_MESON_TAC [], ALL_TAC] THEN REWRITE_TAC [NSUM_DELTA, IN_ELIM_THM] THEN ASM_REWRITE_TAC [] THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"Q:B->bool")] RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"q:A->bool"), (← q r"Q:B->bool")] RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN ASM_REWRITE_TAC [] THEN MESON_TAC [])

  let NUMBER_FIELD_NORM_EXPONENT_EXTENSION ← prove
    r"!k:A ring l:B ring h p j.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
        ==> nsum {P | prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P}
              (\P. residue_degree (ring_of_integers k,ring_of_integers l) h P *
                   ideal_valuation (ring_of_integers l) P
                     (ideal_generated (ring_of_integers l) (IMAGE h j))) =
            extension_degree(k,l) h * ideal_valuation (ring_of_integers k) p j"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_FUNDAMENTAL_IDENTITY) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [(← GSYM NSUM_RMUL)] THEN MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC (← q r"P:B->bool") THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"P:B->bool"), (← q r"j:A->bool")] NUMBER_FIELD_IDEAL_VALUATION_EXTENSION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ARITH_TAC)

  let NUMBER_FIELD_NORM_EXPONENT_MONO ← prove
    r"!k:A ring l:B ring h p J1 J2.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        ring_ideal (ring_of_integers l) J1 /\ ~(J1 = {ring_0 l}) /\
        ring_ideal (ring_of_integers l) J2 /\ J1 SUBSET J2
        ==> nsum {P | prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P}
              (\P. residue_degree (ring_of_integers k,ring_of_integers l) h P *
                   ideal_valuation (ring_of_integers l) P J2) <=
            nsum {P | prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P}
              (\P. residue_degree (ring_of_integers k,ring_of_integers l) h P *
                   ideal_valuation (ring_of_integers l) P J1)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_PRIME_IDEALS_ABOVE) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MATCH_MP_TAC NSUM_LE THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"P:B->bool") THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN REWRITE_TAC [LE_MULT_LCANCEL] THEN DISJ2_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"J1:B->bool"), (← q r"J2:B->bool")] DEDEKIND_IDEAL_SUBSET_VALUATION) THEN ASM_SIMP_TAC [RING_OF_INTEGERS, DEDEKIND_RING_OF_INTEGERS] THEN ANTS_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"J1:B->bool")] IN_RING_IDEAL_0) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN ASM SET_TAC [], DISCH_THEN MATCH_MP_TAC] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO THEN MAP_EVERY EXISTS_TAC [(← q r"k:A ring"), (← q r"h:A->B"), (← q r"p:A->bool")] THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_NORM_EXPONENT_TOWER ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"(q ==> p) ==> (p /\ q <=> q)")
    prove
      r"!k:A ring l:B ring m:C ring h1 h2 p J.
          field k /\ field l /\ number_field m /\
          ring_homomorphism(k,l) h1 /\ ring_homomorphism(l,m) h2 /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
          ==> nsum {Q | prime_ideal (ring_of_integers m) Q /\
                        IMAGE (h2 o h1) p SUBSET Q}
                (\Q. residue_degree (ring_of_integers k,ring_of_integers m)
                       (h2 o h1) Q *
                     ideal_valuation (ring_of_integers m) Q J) =
              nsum {P | prime_ideal (ring_of_integers l) P /\ IMAGE h1 p SUBSET P}
                (\P. residue_degree (ring_of_integers k,ring_of_integers l) h1 P *
                     nsum {Q | prime_ideal (ring_of_integers m) Q /\
                               IMAGE h2 P SUBSET Q}
                       (\Q. residue_degree
                              (ring_of_integers l,ring_of_integers m) h2 Q *
                            ideal_valuation (ring_of_integers m) Q J))"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"number_field(l:B ring)") ASSUME_TAC THENL [ASM_MESON_TAC [NUMBER_FIELD_HOMOMORPHIC_PREIMAGE], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_homomorphism(k:A ring,m:C ring) ((h2:B->C) o (h1:A->B))") ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_COMPOSE], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"m:C ring"), (← q r"(h2:B->C) o (h1:A->B)"), (← q r"p:A->bool")] NUMBER_FIELD_PRIME_IDEALS_ABOVE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN SUBGOAL_THEN (← q r"!x. x IN ring_carrier(ring_of_integers k)
          ==> (h1:A->B) x IN ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h1:A->B")] RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN ASM_REWRITE_TAC [] THEN MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN SUBGOAL_THEN (← q r"!Q. prime_ideal (ring_of_integers m) Q /\
          IMAGE ((h2:B->C) o (h1:A->B)) p SUBSET Q
          ==> prime_ideal (ring_of_integers l)
                {x | x IN ring_carrier(ring_of_integers l) /\ h2 x IN Q} /\
              IMAGE h1 p SUBSET
                {x | x IN ring_carrier(ring_of_integers l) /\ h2 x IN Q}") ASSUME_TAC THENL [X_GEN_TAC (← q r"Q:C->bool") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"~(Q = {ring_0 m:C})") ASSUME_TAC THENL [MATCH_MP_TAC NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO THEN MAP_EVERY EXISTS_TAC [(← q r"k:A ring"), (← q r"(h2:B->C) o (h1:A->B)"), (← q r"p:A->bool")] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"m:C ring"), (← q r"h2:B->C"), (← q r"Q:C->bool")] RING_OF_INTEGERS_PRIME_IDEAL_BELOW) THEN ASM_REWRITE_TAC [EXISTS_UNIQUE_THM] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"P0:B->bool") STRIP_ASSUME_TAC) o CONJUNCT1) THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"m:C ring"), (← q r"h2:B->C"), (← q r"P0:B->bool"), (← q r"Q:C->bool")] RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [], UNDISCH_TAC (← q r"IMAGE ((h2:B->C) o (h1:A->B)) p SUBSET Q") THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM, o_THM] THEN DISCH_TAC THEN X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN ASM_SIMP_TAC [] THEN ASM_MESON_TAC [PRIME_IDEAL_IMP_SUBSET, SUBSET]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!P Q. prime_ideal (ring_of_integers l) P /\ IMAGE (h1:A->B) p SUBSET P /\
            prime_ideal (ring_of_integers m) Q
            ==> (IMAGE ((h2:B->C) o h1) p SUBSET Q /\
                 {x | x IN ring_carrier(ring_of_integers l) /\ h2 x IN Q} = P <=>
                 IMAGE h2 P SUBSET Q)") (LABEL_TAC "F2") THENL [REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"m:C ring"), (← q r"h2:B->C"), (← q r"P:B->bool"), (← q r"Q:C->bool")] RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO THEN MAP_EVERY EXISTS_TAC [(← q r"k:A ring"), (← q r"h1:A->B"), (← q r"p:A->bool")] THEN ASM_REWRITE_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC r1 THEN REWRITE_TAC [IMAGE_o] THEN ASM SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"\Q. {x | x IN ring_carrier(ring_of_integers l) /\ (h2:B->C) x IN Q}"), (← q r"\Q. residue_degree (ring_of_integers k,ring_of_integers m)
             ((h2:B->C) o (h1:A->B)) Q *
           ideal_valuation (ring_of_integers m) Q J"), (← q r"{Q | prime_ideal (ring_of_integers m) Q /\
            IMAGE ((h2:B->C) o (h1:A->B)) p SUBSET Q}"), (← q r"{P | prime_ideal (ring_of_integers l) P /\ IMAGE (h1:A->B) p SUBSET P}")] NSUM_GROUP) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN GEN_REWRITE_TAC id [SUBSET] THEN REWRITE_TAC [FORALL_IN_IMAGE] THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_SIMP_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC (← q r"P:B->bool") THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN TRANS_TAC EQ_TRANS (← q r"nsum {Q | prime_ideal (ring_of_integers m) Q /\
                IMAGE (h2:B->C) P SUBSET Q}
           (\Q. residue_degree (ring_of_integers k,ring_of_integers m)
                  ((h2:B->C) o (h1:A->B)) Q *
                ideal_valuation (ring_of_integers m) Q J)") THEN CONJ_TAC THENL [AP_THM_TAC THEN AP_TERM_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"Q:C->bool") THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_CASES_TAC (← q r"prime_ideal (ring_of_integers m) (Q:C->bool)") THEN ASM_REWRITE_TAC [] THEN USE_THEN "F2" (MATCH_MP_TAC o (SPECL [(← q r"P:B->bool"), (← q r"Q:C->bool")])) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN REWRITE_TAC [(← GSYM NSUM_LMUL)] THEN MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC (← q r"Q:C->bool") THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"m:C ring"), (← q r"h1:A->B"), (← q r"h2:B->C"), (← q r"P:B->bool"), (← q r"Q:C->bool")] NUMBER_FIELD_RESIDUE_DEGREE_TOWER) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO THEN MAP_EVERY EXISTS_TAC [(← q r"k:A ring"), (← q r"h1:A->B"), (← q r"p:A->bool")] THEN ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC THEN ARITH_TAC])

  let NUMBER_FIELD_GALOIS_PRODUCT_VALUATION ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"p0:A->bool = p"
    let q2 ← q r"p0:A->bool"
    let q3 ← q r"p:A->bool"
    let q4 ← q r"ring_of_integers k:A ring"
    let v5 ← ISPECL [q4, q3, q2] IDEAL_VALUATION_PRIME
    let q6 ← q r"p0:A->bool"
    let q7 ← q r"Q:B->bool"
    let q8 ← q r"p:A->bool"
    let q9 ← q r"h:A->B"
    let q10 ← q r"l:B ring"
    let q11 ← q r"k:A ring"
    let v12 ← ISPECL [q11, q10, q9, q8, q7, q6] NUMBER_FIELD_IDEAL_VALUATION_EXTENSION
    let q13 ← q r"p0:A->bool"
    let q14 ← q r"h:A->B"
    let q15 ← q r"l:B ring"
    let q16 ← q r"k:A ring"
    let v17 ← ISPECL [q16, q15, q14, q13] RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME
    let q18 ← q r"residue_degree (ring_of_integers k,ring_of_integers l)
                      (h:A->B) P0"
    let q19 ← q r"ideal_generated (ring_of_integers l) (IMAGE (h:A->B) p0)"
    let q20 ← q r"Q:B->bool"
    let q21 ← q r"ring_of_integers l:B ring"
    let v22 ← ISPECL [q21, q20, q19, q18] IDEAL_VALUATION_IDEAL_POW
    let q23 ← q r"P0:B->bool"
    let q24 ← q r"p0:A->bool"
    let q25 ← q r"l:B ring"
    let q26 ← q r"k:A ring"
    let q27 ← q r"h:A->B"
    let v28 ← ISPECL [q27, q26, q25, q24, q23] NUMBER_FIELD_GALOIS_PRODUCT_PRIME
    let q29 ← q r"P0:B->bool"
    let q30 ← q r"nsum (group_carrier(galois_group(k:A ring,l:B ring) h))
      (\g. ideal_valuation (ring_of_integers l) Q (IMAGE g P0)) =
    residue_degree (ring_of_integers k,ring_of_integers l) h P0 *
    ramification_index (ring_of_integers k,ring_of_integers l) h Q *
    (if (p0:A->bool) = p then 1 else 0)"
    let q31 ← q r"P0:B->bool"
    let q32 ← q r"p0:A->bool"
    let q33 ← q r"p:A->bool"
    let q34 ← q r"h:A->B"
    let q35 ← q r"l:B ring"
    let q36 ← q r"k:A ring"
    let v37 ← ISPECL [q36, q35, q34, q33, q32, q31] NUMBER_FIELD_NORM_EXPONENT_PRIME
    let q38 ← q r"J:B->bool"
    let q39 ← q r"P0:B->bool"
    let q40 ← q r"p:A->bool"
    let q41 ← q r"h:A->B"
    let q42 ← q r"l:B ring"
    let q43 ← q r"k:A ring"
    let v44 ← ISPECL [q43, q42, q41, q40, q39, q38] NUMBER_FIELD_NORM_EXPONENT_ADD
    let q45 ← q r"P0:B->bool"
    let q46 ← q r"g:B->B"
    let q47 ← q r"l:B ring"
    let q48 ← q r"k:A ring"
    let q49 ← q r"h:A->B"
    let v50 ← ISPECL [q49, q48, q47, q46, q45] GALOIS_GROUP_RING_OF_INTEGERS_IDEAL
    let q51 ← q r"g:B->B"
    let q52 ← q r"nsum (group_carrier(galois_group(k:A ring,l:B ring) h))
      (\g. ideal_valuation (ring_of_integers l) Q (IMAGE g P0) +
           ideal_valuation (ring_of_integers l) Q (IMAGE g J))"
    let q53 ← q r"p0:A->bool"
    let q54 ← q r"P0:B->bool"
    let q55 ← q r"h:A->B"
    let q56 ← q r"l:B ring"
    let q57 ← q r"k:A ring"
    let v58 ← ISPECL [q57, q56, q55, q54] RING_OF_INTEGERS_PRIME_IDEAL_BELOW
    let q59 ← q r"J:B->bool"
    let q60 ← q r"P0:B->bool"
    let q61 ← q r"P:B->bool"
    let q62 ← q r"g:B->B"
    let q63 ← q r"l:B ring"
    let q64 ← q r"k:A ring"
    let q65 ← q r"h:A->B"
    let v66 ← ISPECL [q65, q64, q63, q62] GALOIS_GROUP_RING_OF_INTEGERS_AUTOMORPHISM
    let q67 ← q r"g:B->B"
    let q68 ← q r"!P. prime_ideal (ring_of_integers l) P
          ==> ideal_valuation (ring_of_integers l) P
                (ring_carrier(ring_of_integers l:B ring)) = 0"
    let q69 ← q r"(a:num) = 0 /\ (b:num) = 0 ==> a = c * b"
    let r70 ← MESON [MULT_CLAUSES] q69
    let q71 ← q r"ring_of_integers l:B ring"
    let v72 ← ISPEC q71 DEDEKIND_IDEAL_INDUCT
    let q73 ← q r"J:B->bool"
    let q74 ← q r"J:B->bool"
    let q75 ← q r"\g:B->B. IMAGE g (J:B->bool)"
    let q76 ← q r"group_carrier(galois_group(k:A ring,l:B ring) h)"
    let q77 ← q r"Q:B->bool"
    let q78 ← q r"ring_of_integers l:B ring"
    let v79 ← ISPECL [q78, q77, q76, q75] IDEAL_VALUATION_IDEAL_PRODUCT
    let q80 ← q r"!J. ring_ideal (ring_of_integers l) J /\ ~(J = {ring_0 l})
        ==> ideal_valuation (ring_of_integers l) Q
              (ideal_product (ring_of_integers l)
                 (group_carrier(galois_group(k:A ring,l:B ring) h))
                 (\g. IMAGE g J)) =
            nsum (group_carrier(galois_group(k,l) h))
              (\g. ideal_valuation (ring_of_integers l) Q (IMAGE g J))"
    let q81 ← q r"!g J. g IN group_carrier(galois_group(k:A ring,l:B ring) h) /\
          ring_ideal (ring_of_integers l) J /\ ~(J = {ring_0 l})
          ==> ring_ideal (ring_of_integers l) (IMAGE g J) /\
              ~(IMAGE g J = {ring_0 l})"
    let q82 ← q r"dedekind_domain(ring_of_integers k:A ring) /\
    dedekind_domain(ring_of_integers l:B ring)"
    let q83 ← q r"p:A->bool"
    let q84 ← q r"h:A->B"
    let q85 ← q r"k:A ring"
    let q86 ← q r"~(Q = {ring_0 l:B})"
    let q87 ← q r"h:A->B"
    let q88 ← q r"l:B ring"
    let q89 ← q r"k:A ring"
    let v90 ← ISPECL [q89, q88, q87] NUMBER_FIELD_TOWER_LAW
    let q91 ← q r"h:A->B"
    let q92 ← q r"l:B ring"
    let q93 ← q r"k:A ring"
    let v94 ← ISPECL [q93, q92, q91] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE
    let q95 ← q r"field k /\ ring_homomorphism(k,l) (h:A->B)"
    let q96 ← q r"a1 /\ a2 /\ a3 /\ a4 /\ a5 /\ a6 /\ a7 /\ a8 ==> b <=>
                    a1 /\ a2 /\ a3 /\ a4 /\ a5 /\ a6 ==> a7 /\ a8 ==> b"
    let r97 ← TAUT q96
    prove
      r"!k:A ring l:B ring h p Q J.
          number_field l /\ galois_extension(k,l) h /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
          prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q /\
          ring_ideal (ring_of_integers l) J /\ ~(J = {ring_0 l})
          ==> ideal_valuation (ring_of_integers l) Q
                (ideal_product (ring_of_integers l)
                   (group_carrier(galois_group(k,l) h)) (\g. IMAGE g J)) =
              ramification_index (ring_of_integers k,ring_of_integers l) h Q *
              nsum {P | prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P}
                (\P. residue_degree (ring_of_integers k,ring_of_integers l) h P *
                     ideal_valuation (ring_of_integers l) P J)"
      (REPEAT GEN_TAC THEN REWRITE_TAC [r97] THEN STRIP_TAC THEN SUBGOAL_THEN q95 STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_IMP_FIELD_EXTENSION)) THEN SIMP_TAC [field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN MP_TAC v94 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN MP_TAC v90 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITE_GALOIS_GROUP)) THEN SUBGOAL_THEN q86 ASSUME_TAC THENL [MATCH_MP_TAC NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO THEN MAP_EVERY EXISTS_TAC [q85, q84, q83] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN q82 STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN q81 ASSUME_TAC THENL [MESON_TAC [GALOIS_GROUP_RING_OF_INTEGERS_IDEAL], ALL_TAC] THEN SUBGOAL_THEN q80 (LABEL_TAC "sumform") THENL [REPEAT STRIP_TAC THEN MP_TAC v79 THEN REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_OF_INTEGERS], ALL_TAC] THEN USE_THEN "sumform" (fun th => SIMP_TAC [th]) THEN SPEC_TAC (q74, q73) THEN MP_TAC v72 THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [MATCH_MP_TAC r70 THEN SUBGOAL_THEN q68 ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC IDEAL_VALUATION_CARRIER THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN ASM_MESON_TAC [PRIME_IMP_PROPER_IDEAL, PROPER_IDEAL_ALT], ALL_TAC] THEN CONJ_TAC THEN MATCH_MP_TAC NSUM_EQ_0 THENL [X_GEN_TAC q67 THEN DISCH_TAC THEN MP_TAC v66 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o CONJUNCT1) THEN ASM_SIMP_TAC [], X_GEN_TAC q61 THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN ASM_SIMP_TAC [MULT_CLAUSES]], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [q60, q59] THEN STRIP_TAC THEN MP_TAC v58 THEN ASM_REWRITE_TAC [EXISTS_UNIQUE_THM] THEN DISCH_THEN ((X_CHOOSE_THEN q53 STRIP_ASSUME_TAC) o CONJUNCT1) THEN TRANS_TAC EQ_TRANS q52 THEN CONJ_TAC THENL [MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC q51 THEN DISCH_TAC THEN REWRITE_TAC [] THEN MP_TAC v50 THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, RING_IDEAL_IMP_SUBSET] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN MATCH_MP_TAC IDEAL_VALUATION_IDEAL_PROD THEN ASM_SIMP_TAC [RING_OF_INTEGERS, PRIME_IMP_RING_IDEAL], ALL_TAC] THEN ASM_SIMP_TAC [NSUM_ADD] THEN MP_TAC v44 THEN ANTS_TAC THENL [ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], DISCH_THEN SUBST1_TAC] THEN MP_TAC v37 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN SUBGOAL_THEN q30 SUBST1_TAC THENL [USE_THEN "sumform" (MP_TAC o (SPEC q29)) THEN ANTS_TAC THENL [ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], DISCH_THEN (SUBST1_TAC o SYM)] THEN MP_TAC v28 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC v22 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED] THEN MP_TAC v17 THEN ASM_SIMP_TAC [], DISCH_THEN SUBST1_TAC] THEN MP_TAC v12 THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC v5 THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [], ALL_TAC] THEN ASM_CASES_TAC q1 THEN ASM_REWRITE_TAC [] THEN ARITH_TAC)

  let NUMBER_FIELD_GALOIS_NORM_VALUATION ← prove
    r"!k:A ring l:B ring h p x.
        number_field l /\ galois_extension(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        x IN ring_carrier(ring_of_integers l) /\ ~(x = ring_0 l)
        ==> ideal_valuation (ring_of_integers k) p
              (ideal_generated (ring_of_integers k)
                 {algebra_norm (k,l) h x}) =
            nsum {P | prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P}
              (\P. residue_degree (ring_of_integers k,ring_of_integers l) h P *
                   ideal_valuation (ring_of_integers l) P
                     (ideal_generated (ring_of_integers l) {x}))"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"field k /\ ring_homomorphism(k,l) (h:A->B)") STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_IMP_FIELD_EXTENSION)) THEN SIMP_TAC [field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITE_GALOIS_GROUP)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o ((REWRITE_RULE [field_extension]) o (MATCH_MP FINITE_IMP_FIELD_EXTENSION))) THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_PRIME_IDEALS_ABOVE) THEN ASM_REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY), IN_ELIM_THM] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"Q:B->bool") STRIP_ASSUME_TAC) o CONJUNCT2) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"algebra_norm (k,l) (h:A->B) x IN ring_carrier(ring_of_integers k) /\
    ~(algebra_norm (k,l) h x = ring_0 k)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [ALGEBRA_NORM_EQ_0] THEN MATCH_MP_TAC NUMBER_FIELD_NORM_INTEGRAL THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!g. g IN group_carrier(galois_group(k:A ring,l:B ring) h)
        ==> g x IN ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"g:B->B")] GALOIS_GROUP_RING_OF_INTEGERS_AUTOMORPHISM) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o CONJUNCT1) THEN ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_generated (ring_of_integers l)
      (IMAGE (h:A->B)
        (ideal_generated (ring_of_integers k) {algebra_norm (k,l) h x})) =
    ideal_product (ring_of_integers l) (group_carrier(galois_group(k,l) h))
      (\g. IMAGE g (ideal_generated (ring_of_integers l) {x}))") (LABEL_TAC "ext") THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring"), (← q r"h:A->B"), (← q r"{algebra_norm (k,l) (h:A->B) x}")] IDEAL_GENERATED_IMAGE_IDEAL_GENERATED) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_OF_INTEGERS, SING_SUBSET] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [IMAGE_CLAUSES] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"x:B")] ALGEBRA_TRACE_NORM_GALOIS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o CONJUNCT1) THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"group_carrier(galois_group(k:A ring,l:B ring) h)"), (← q r"\g:B->B. g x")] RING_PRODUCT_RING_OF_INTEGERS) THEN ASM_SIMP_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"group_carrier(galois_group(k:A ring,l:B ring) h)"), (← q r"\g:B->B. g x")] IDEAL_PRODUCT_PRINCIPAL) THEN ASM_SIMP_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC IDEAL_PRODUCT_EQ THEN X_GEN_TAC (← q r"g:B->B") THEN DISCH_TAC THEN REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"g:B->B"), (← q r"{x:B}")] GALOIS_GROUP_IMAGE_IDEAL_GENERATED) THEN ASM_REWRITE_TAC [SING_SUBSET, IMAGE_CLAUSES] THEN DISCH_THEN (fun th => REWRITE_TAC [th]), ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"Q:B->bool"), (← q r"ideal_generated (ring_of_integers l) {x:B}")] NUMBER_FIELD_GALOIS_PRODUCT_VALUATION) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, RING_OF_INTEGERS_IDEAL_GENERATED_SING_EQ_0] THEN REMOVE_THEN "ext" (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"Q:B->bool"), (← q r"ideal_generated (ring_of_integers k)
                    {algebra_norm (k,l) (h:A->B) x}")] NUMBER_FIELD_IDEAL_VALUATION_EXTENSION) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, RING_OF_INTEGERS_IDEAL_GENERATED_SING_EQ_0] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [EQ_MULT_LCANCEL] THEN ASM_ARITH_TAC)

  -- @@RETURN BEGIN
  return { RING_OF_INTEGERS_IDEAL_EXTENSION_CONTRACTION, NUMBER_FIELD_NORM_EXPONENT_ADD,
           NUMBER_FIELD_NORM_EXPONENT_PRIME, NUMBER_FIELD_NORM_EXPONENT_EXTENSION,
           NUMBER_FIELD_NORM_EXPONENT_MONO, NUMBER_FIELD_NORM_EXPONENT_TOWER,
           NUMBER_FIELD_GALOIS_PRODUCT_VALUATION, NUMBER_FIELD_GALOIS_NORM_VALUATION }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- ideal_norm_extension.ml phrases from line 726 to 1385                  -/
/- ---------------------------------------------------------------------- -/

structure IdealNormExtension02 where
  -- @@FIELDS
  NUMBER_FIELD_NORM_VALUATION : thm
  number_field_ideal_norm : thm
  NUMBER_FIELD_IDEAL_NORM_IDEAL : thm
  NUMBER_FIELD_IDEAL_NORM_PRINCIPAL : thm
  NUMBER_FIELD_IDEAL_NORM_EXTENSION_SUBSET : thm
  NUMBER_FIELD_IDEAL_NORM_VALUATION : thm
  NUMBER_FIELD_IDEAL_NORM_0 : thm
  NUMBER_FIELD_IDEAL_NORM_EQ_0 : thm
  NUMBER_FIELD_IDEAL_NORM_VALUATIONS : thm
  NUMBER_FIELD_IDEAL_NORM_MUL : thm
  NUMBER_FIELD_IDEAL_NORM_PRIME : thm
  NUMBER_FIELD_IDEAL_NORM_EXTENSION : thm
  NUMBER_FIELD_IDEAL_NORM_CARRIER : thm
  NUMBER_FIELD_IDEAL_NORM_POW : thm
  NUMBER_FIELD_IDEAL_NORM_TOWER : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupIdealNormExtension02 [HolBase] (D : IdealNormExtensionDeps) (BIdealNormExtension01 : IdealNormExtension01) :
    ExceptT String IO IdealNormExtension02 := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, SET_RULE, SET_TAC, TAUT,
        new_definition, .. } := D
  let { ALGEBRA_NORM_EQ_0, ALGEBRA_NORM_MUL, ALGEBRA_TRACE_NORM_INTERMEDIATE,
        CONTRAPOS_THM, DEDEKIND_IDEAL_EQ_VALUATION,
        DEDEKIND_IDEAL_SUBSET_POW_VALUATION, DEDEKIND_IDEAL_SUBSET_VALUATION,
        DEDEKIND_IDEAL_WEAK_APPROXIMATION, DEDEKIND_IMP_INTEGRAL_DOMAIN,
        DEDEKIND_IN_IDEAL_POW_VALUATION, DEDEKIND_RING_OF_INTEGERS, EQ_MULT_LCANCEL,
        EXTENSION_DEGREE_EQ_0, FINITE_IMP_FIELD_EXTENSION, FORALL_IN_GSPEC,
        FORALL_IN_IMAGE, IDEAL_GENERATED_0, IDEAL_GENERATED_IMAGE_IDEAL_GENERATED,
        IDEAL_GENERATED_INC, IDEAL_GENERATED_MINIMAL, IDEAL_OF_VALUATIONS_UNIQUE,
        IDEAL_POW_0, IDEAL_POW_CARRIER, IDEAL_POW_EQ_ZERO, IDEAL_POW_SUC,
        IDEAL_PROD_EQ_ZERO, IDEAL_PROD_LZERO, IDEAL_PROD_RZERO,
        IDEAL_VALUATION_IDEAL_POW, IDEAL_VALUATION_IDEAL_PROD, IDEAL_VALUATION_PRIME,
        IDEAL_VALUATION_PRINCIPAL_POW, IMAGE_CLAUSES, IN_ELIM_THM,
        IN_IDEAL_GENERATED_SELF, IN_IDEAL_GENERATED_SING_EQ, IN_RING_IDEAL_0, IN_SING,
        LEFT_IMP_EXISTS_THM, LE_ANTISYM, MULT_CLAUSES, NSUM_EQ, NSUM_LMUL,
        NUMBER_FIELD_GALOIS_CLOSURE, NUMBER_FIELD_HOMOMORPHIC_PREIMAGE,
        NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_NORM_INTEGRAL, NUMBER_FIELD_NORM_MULTIPLE,
        NUMBER_FIELD_PRIME_IDEALS_ABOVE, NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO,
        NUMBER_FIELD_TOWER_LAW, PRIME_IMP_RING_IDEAL, RIGHT_FORALL_IMP_THM, RING_0,
        RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_COMPOSE, RING_HOMOMORPHISM_IN_CARRIER,
        RING_HOMOMORPHISM_RING_OF_INTEGERS, RING_IDEAL_CARRIER,
        RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_POW, RING_IDEAL_IDEAL_PROD,
        RING_IDEAL_IMP_SUBSET, RING_MONOMORPHISM_EQ_0, RING_OF_INTEGERS,
        RING_OF_INTEGERS_IDEAL_EXTENSION, RING_OF_INTEGERS_IDEAL_GENERATED_SING_EQ_0,
        RING_OF_INTEGERS_SUBSET, SING_SUBSET, SUBSET, SUBSET_ANTISYM_EQ,
        field_extension, ring_divides, .. } := D.core1
  let { NUMBER_FIELD_GALOIS_NORM_VALUATION, NUMBER_FIELD_NORM_EXPONENT_ADD,
        NUMBER_FIELD_NORM_EXPONENT_EXTENSION, NUMBER_FIELD_NORM_EXPONENT_MONO,
        NUMBER_FIELD_NORM_EXPONENT_PRIME, NUMBER_FIELD_NORM_EXPONENT_TOWER, .. } := BIdealNormExtension01
  -- @@SCOPE END

  let NUMBER_FIELD_NORM_VALUATION ← prove
    r"!k:A ring l:B ring h p x.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        x IN ring_carrier(ring_of_integers l) /\ ~(x = ring_0 l)
        ==> ideal_valuation (ring_of_integers k) p
              (ideal_generated (ring_of_integers k)
                 {algebra_norm (k,l) h x}) =
            nsum {P | prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P}
              (\P. residue_degree (ring_of_integers k,ring_of_integers l) h P *
                   ideal_valuation (ring_of_integers l) P
                     (ideal_generated (ring_of_integers l) {x}))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_GALOIS_CLOSURE) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"m:(B#num)ring"), (← q r"j:B->B#num")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP NUMBER_FIELD_IMP_FIELD) o (checkM (fun th => (do let z3 ← (q r"number_field(l:B ring)"); let z2 ← (do let z1 ← (pure th); pure (concl z1)); pure (z2 == z3)))))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"m:(B#num)ring"), (← q r"j:B->B#num")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN SUBGOAL_THEN (← q r"field_extension(k:A ring,l:B ring) h /\
    field_extension(l:B ring,m:(B#num)ring) j") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [FINITE_IMP_FIELD_EXTENSION], ALL_TAC] THEN ABBREV_TAC (← q r"n = extension_degree(l:B ring,m:(B#num)ring) j") THEN SUBGOAL_THEN (← q r"~(n = 0)") ASSUME_TAC THENL [EXPAND_TAC "n" THEN ASM_SIMP_TAC [EXTENSION_DEGREE_EQ_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_homomorphism(k:A ring,m:(B#num)ring) ((j:B->B#num) o (h:A->B))") ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_COMPOSE], ALL_TAC] THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"algebra_norm (k,l) (h:A->B) x IN ring_carrier(ring_of_integers k) /\
    ~(algebra_norm (k,l) h x = ring_0 k)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [ALGEBRA_NORM_EQ_0] THEN MATCH_MP_TAC NUMBER_FIELD_NORM_INTEGRAL THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(j:B->B#num) x IN ring_carrier(ring_of_integers m) /\ ~(j x = ring_0 m)") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"m:(B#num)ring"), (← q r"j:B->B#num")] RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0, field_extension]], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_valuation (ring_of_integers k) p
      (ideal_generated (ring_of_integers k)
         {algebra_norm (k,m) ((j:B->B#num) o (h:A->B)) (j x)}) =
    n * ideal_valuation (ring_of_integers k) p
          (ideal_generated (ring_of_integers k) {algebra_norm (k,l) h x})") MP_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"j:B->B#num"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"m:(B#num)ring"), (← q r"x:B")] ALGEBRA_TRACE_NORM_INTERMEDIATE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o CONJUNCT2) THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") IDEAL_VALUATION_PRINCIPAL_POW)) THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"m:(B#num)ring"), (← q r"(j:B->B#num) o (h:A->B)"), (← q r"p:A->bool"), (← q r"(j:B->B#num) x")] NUMBER_FIELD_GALOIS_NORM_VALUATION) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"m:(B#num)ring"), (← q r"h:A->B"), (← q r"j:B->B#num"), (← q r"p:A->bool"), (← q r"ideal_generated (ring_of_integers m) {(j:B->B#num) x}")] NUMBER_FIELD_NORM_EXPONENT_TOWER) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN SUBGOAL_THEN (← q r"!P. prime_ideal (ring_of_integers l) P /\ IMAGE (h:A->B) p SUBSET P
        ==> nsum {Q | prime_ideal (ring_of_integers m) Q /\
                      IMAGE (j:B->B#num) P SUBSET Q}
              (\Q. residue_degree (ring_of_integers l,ring_of_integers m) j Q *
                   ideal_valuation (ring_of_integers m) Q
                     (ideal_generated (ring_of_integers m) {j x})) =
            n * ideal_valuation (ring_of_integers l) P
                  (ideal_generated (ring_of_integers l) {x})") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"ring_of_integers m:(B#num)ring"), (← q r"j:B->B#num"), (← q r"{x:B}")] IDEAL_GENERATED_IMAGE_IDEAL_GENERATED) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_OF_INTEGERS, SING_SUBSET, IMAGE_CLAUSES] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN EXPAND_TAC "n" THEN MATCH_MP_TAC NUMBER_FIELD_NORM_EXPONENT_EXTENSION THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, RING_OF_INTEGERS_IDEAL_GENERATED_SING_EQ_0] THEN MATCH_MP_TAC NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO THEN MAP_EVERY EXISTS_TAC [(← q r"k:A ring"), (← q r"h:A->B"), (← q r"p:A->bool")] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"nsum {P | prime_ideal (ring_of_integers l) P /\ IMAGE (h:A->B) p SUBSET P}
      (\P. residue_degree (ring_of_integers k,ring_of_integers l) h P *
           nsum {Q | prime_ideal (ring_of_integers m) Q /\
                     IMAGE (j:B->B#num) P SUBSET Q}
             (\Q. residue_degree (ring_of_integers l,ring_of_integers m) j Q *
                  ideal_valuation (ring_of_integers m) Q
                    (ideal_generated (ring_of_integers m) {j x}))) =
    n * nsum {P | prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P}
          (\P. residue_degree (ring_of_integers k,ring_of_integers l) h P *
               ideal_valuation (ring_of_integers l) P
                 (ideal_generated (ring_of_integers l) {x}))") SUBST1_TAC THENL [GEN_REWRITE_TAC RAND_CONV [(← GSYM NSUM_LMUL)] THEN MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC (← q r"P:B->bool") THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN ASM_SIMP_TAC [] THEN ARITH_TAC, ALL_TAC] THEN ASM_REWRITE_TAC [EQ_MULT_LCANCEL] THEN MESON_TAC [])

  let number_field_ideal_norm ← new_definition
    r"number_field_ideal_norm (k:A ring,l:B ring) (h:A->B) J =
        ideal_generated (ring_of_integers k)
          {algebra_norm (k,l) h x | x IN J}"

  let NUMBER_FIELD_IDEAL_NORM_IDEAL ← prove
    r"!k:A ring l:B ring h J.
        ring_ideal (ring_of_integers k) (number_field_ideal_norm (k,l) h J)"
    (REWRITE_TAC [number_field_ideal_norm, RING_IDEAL_IDEAL_GENERATED])

  let NUMBER_FIELD_IDEAL_NORM_PRINCIPAL ← prove
    r"!k:A ring l:B ring h x.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        x IN ring_carrier(ring_of_integers l)
        ==> number_field_ideal_norm (k,l) h
              (ideal_generated (ring_of_integers l) {x}) =
            ideal_generated (ring_of_integers k) {algebra_norm (k,l) h x}"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"!y. y IN ring_carrier(ring_of_integers l)
        ==> algebra_norm (k,l) (h:A->B) y IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC NUMBER_FIELD_NORM_INTEGRAL THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_generated (ring_of_integers l) {x:B} SUBSET
    ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [MATCH_MP_TAC RING_IDEAL_IMP_SUBSET THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN REWRITE_TAC [number_field_ideal_norm] THEN REWRITE_TAC [(← GSYM SUBSET_ANTISYM_EQ)] THEN CONJ_TAC THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THENL [REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(y:B) IN ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN UNDISCH_TAC (← q r"(y:B) IN ideal_generated (ring_of_integers l) {x}") THEN ASM_SIMP_TAC [IN_IDEAL_GENERATED_SING_EQ, ring_divides] THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"z:B") STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier l /\ (z:B) IN ring_carrier l") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [ALGEBRA_NORM_MUL] THEN EXISTS_TAC (← q r"algebra_norm (k,l) (h:A->B) z") THEN ASM_SIMP_TAC [], REWRITE_TAC [SING_SUBSET] THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN REWRITE_TAC [SUBSET, FORALL_IN_GSPEC, IN_ELIM_THM] THEN CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN EXISTS_TAC (← q r"x:B") THEN ASM_REWRITE_TAC [IN_IDEAL_GENERATED_SELF]])

  let NUMBER_FIELD_IDEAL_NORM_EXTENSION_SUBSET ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"s SUBSET t ==> (a:B) IN s ==> a IN t")
    prove
      r"!k:A ring l:B ring h J.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          ring_ideal (ring_of_integers l) J
          ==> ideal_generated (ring_of_integers l)
                (IMAGE h (number_field_ideal_norm (k,l) h J)) SUBSET J"
      (REPEAT STRIP_TAC THEN REWRITE_TAC [number_field_ideal_norm] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring"), (← q r"h:A->B"), (← q r"{algebra_norm (k,l) (h:A->B) x | x IN J}")] IDEAL_GENERATED_IMAGE_IDEAL_GENERATED) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_OF_INTEGERS, SUBSET, FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC NUMBER_FIELD_NORM_INTEGRAL THEN ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], DISCH_THEN SUBST1_TAC] THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, FORALL_IN_GSPEC] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"x:B")] NUMBER_FIELD_NORM_MULTIPLE) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r1 THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET])

  let NUMBER_FIELD_IDEAL_NORM_VALUATION ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (q ==> r) ==> (p <=> q) ==> r")
    prove
      r"!k:A ring l:B ring h J p.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          ring_ideal (ring_of_integers l) J /\ ~(J = {ring_0 l}) /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
          ==> ideal_valuation (ring_of_integers k) p
                (number_field_ideal_norm (k,l) h J) =
              nsum {P | prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P}
                (\P. residue_degree (ring_of_integers k,ring_of_integers l) h P *
                     ideal_valuation (ring_of_integers l) P J)"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN SUBGOAL_THEN (← q r"dedekind_domain(ring_of_integers k:A ring) /\
      dedekind_domain(ring_of_integers l:B ring)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"(J:B->bool) SUBSET ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x. x IN J
          ==> algebra_norm (k,l) (h:A->B) x IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC NUMBER_FIELD_NORM_INTEGRAL THEN ASM_REWRITE_TAC [] THEN ASM SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_PRIME_IDEALS_ABOVE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"{P | prime_ideal (ring_of_integers l) P /\
                         IMAGE (h:A->B) p SUBSET P}"), (← q r"J:B->bool")] DEDEKIND_IDEAL_WEAK_APPROXIMATION) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_OF_INTEGERS, IN_ELIM_THM] THEN X_GEN_TAC (← q r"P:B->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO THEN MAP_EVERY EXISTS_TAC [(← q r"k:A ring"), (← q r"h:A->B"), (← q r"p:A->bool")] THEN ASM_REWRITE_TAC [], REWRITE_TAC [RING_OF_INTEGERS, IN_ELIM_THM] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"x0:B") STRIP_ASSUME_TAC)] THEN SUBGOAL_THEN (← q r"(x0:B) IN ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"x0:B")] NUMBER_FIELD_NORM_VALUATION) THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"nsum {P | prime_ideal (ring_of_integers l) P /\ IMAGE (h:A->B) p SUBSET P}
        (\P. residue_degree (ring_of_integers k,ring_of_integers l) h P *
             ideal_valuation (ring_of_integers l) P
               (ideal_generated (ring_of_integers l) {x0})) =
      nsum {P | prime_ideal (ring_of_integers l) P /\ IMAGE (h:A->B) p SUBSET P}
        (\P. residue_degree (ring_of_integers k,ring_of_integers l) h P *
             ideal_valuation (ring_of_integers l) P J)") SUBST1_TAC THENL [MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_SIMP_TAC [], DISCH_TAC] THEN SUBGOAL_THEN (← q r"algebra_norm (k,l) (h:A->B) x0 IN number_field_ideal_norm (k,l) h J /\
      ~(algebra_norm (k,l) (h:A->B) x0 = ring_0 k)") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [REWRITE_TAC [number_field_ideal_norm] THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN REWRITE_TAC [SUBSET, FORALL_IN_GSPEC, IN_ELIM_THM] THEN ASM_MESON_TAC [], MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"x0:B")] ALGEBRA_NORM_EQ_0) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET]], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(number_field_ideal_norm (k,l) (h:A->B) J = {ring_0 k})") ASSUME_TAC THENL [ASM_MESON_TAC [IN_SING], ALL_TAC] THEN REWRITE_TAC [(← GSYM LE_ANTISYM)] THEN CONJ_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); pure (is_eq z2)) then (do let z4 ← (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); liftExcept (lhs z5)); canM (fun z7 => (do let z8 ← (pure z7); find_termM (fun z9 => (do let z11 ← (pure z9); let z10 ← (q r"algebra_norm (k,l) (h:A->B) x0"); pure (z10 == z11))) z8)) z4) else pure false))))) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ideal_generated (ring_of_integers k)
                        {algebra_norm (k,l) (h:A->B) x0}"), (← q r"number_field_ideal_norm (k,l) (h:A->B) J")] DEDEKIND_IDEAL_SUBSET_VALUATION) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, RING_OF_INTEGERS, RING_OF_INTEGERS_IDEAL_GENERATED_SING_EQ_0, NUMBER_FIELD_IDEAL_NORM_IDEAL] THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET, NUMBER_FIELD_IDEAL_NORM_IDEAL], DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC []], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:A->bool"), (← q r"number_field_ideal_norm (k,l) (h:A->B) J"), (← q r"nsum {P | prime_ideal (ring_of_integers l) P /\
                              IMAGE (h:A->B) p SUBSET P}
                      (\P. residue_degree
                             (ring_of_integers k,ring_of_integers l) h P *
                           ideal_valuation (ring_of_integers l) P J)")] DEDEKIND_IDEAL_SUBSET_POW_VALUATION) THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_IDEAL, RING_OF_INTEGERS] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [number_field_ideal_norm] THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, PRIME_IMP_RING_IDEAL] THEN GEN_REWRITE_TAC id [SUBSET] THEN REWRITE_TAC [FORALL_IN_GSPEC] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN ASM_CASES_TAC (← q r"x = ring_0 l:B") THENL [SUBGOAL_THEN (← q r"algebra_norm (k,l) (h:A->B) x = ring_0 k") SUBST1_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"x:B")] ALGEBRA_NORM_EQ_0) THEN ASM_REWRITE_TAC [RING_0], MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ideal_pow (ring_of_integers k) p
                          (nsum {P | prime_ideal (ring_of_integers l) P /\
                                     IMAGE (h:A->B) p SUBSET P}
                            (\P. residue_degree
                                   (ring_of_integers k,ring_of_integers l) h P *
                                 ideal_valuation (ring_of_integers l) P J))")] IN_RING_IDEAL_0) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:A->bool"), (← q r"algebra_norm (k,l) (h:A->B) x"), (← q r"nsum {P | prime_ideal (ring_of_integers l) P /\
                              IMAGE (h:A->B) p SUBSET P}
                      (\P. residue_degree
                             (ring_of_integers k,ring_of_integers l) h P *
                           ideal_valuation (ring_of_integers l) P J)")] DEDEKIND_IN_IDEAL_POW_VALUATION) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_OF_INTEGERS] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"x:B")] ALGEBRA_NORM_EQ_0) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], DISCH_THEN SUBST1_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"x:B")] NUMBER_FIELD_NORM_VALUATION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC NUMBER_FIELD_NORM_EXPONENT_MONO THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, RING_OF_INTEGERS_IDEAL_GENERATED_SING_EQ_0] THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET])

  let NUMBER_FIELD_IDEAL_NORM_0 ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"{(f:B->A) x | x IN {a}} = {f a}")
    prove
      r"!k:A ring l:B ring h.
          field k /\ number_field l /\ ring_homomorphism(k,l) h
          ==> number_field_ideal_norm (k,l) h {ring_0 l} = {ring_0 k}"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN REWRITE_TAC [number_field_ideal_norm, r1] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"ring_0 l:B")] ALGEBRA_NORM_EQ_0) THEN ASM_REWRITE_TAC [RING_0] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") IDEAL_GENERATED_0))])

  let NUMBER_FIELD_IDEAL_NORM_EQ_0 ← prove
    r"!k:A ring l:B ring h J.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        ring_ideal (ring_of_integers l) J
        ==> (number_field_ideal_norm (k,l) h J = {ring_0 k} <=>
             J = {ring_0 l})"
    (REPEAT STRIP_TAC THEN EQ_TAC THENL [ALL_TAC, DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_0]] THEN ONCE_REWRITE_TAC [(← GSYM CONTRAPOS_THM)] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"?x:B. x IN J /\ ~(x = ring_0 l)") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"J:B->bool")] IN_RING_IDEAL_0) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN ASM SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN SUBGOAL_THEN (← q r"(J:B->bool) SUBSET ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"algebra_norm (k,l) (h:A->B) x IN number_field_ideal_norm (k,l) h J /\
    ~(algebra_norm (k,l) h x = ring_0 k)") MP_TAC THENL [ALL_TAC, SET_TAC []] THEN CONJ_TAC THENL [REWRITE_TAC [number_field_ideal_norm] THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN REWRITE_TAC [SUBSET, FORALL_IN_GSPEC, IN_ELIM_THM] THEN CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC NUMBER_FIELD_NORM_INTEGRAL THEN ASM_REWRITE_TAC [] THEN ASM SET_TAC [], MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"x:B")] ALGEBRA_NORM_EQ_0) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET]])

  let NUMBER_FIELD_IDEAL_NORM_VALUATIONS ← prove
    r"!k:A ring l:B ring h J.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        ring_ideal (ring_of_integers l) J /\ ~(J = {ring_0 l})
        ==> number_field_ideal_norm (k,l) h J =
            ideal_of_valuations (ring_of_integers k)
              (\p. nsum {P | prime_ideal (ring_of_integers l) P /\
                             IMAGE h p SUBSET P}
                        (\P. residue_degree
                               (ring_of_integers k,ring_of_integers l) h P *
                             ideal_valuation (ring_of_integers l) P J))"
    (REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC IDEAL_OF_VALUATIONS_UNIQUE THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_IDEAL, RING_OF_INTEGERS, NUMBER_FIELD_IDEAL_NORM_EQ_0, NUMBER_FIELD_IDEAL_NORM_VALUATION] THEN MATCH_MP_TAC DEDEKIND_RING_OF_INTEGERS THEN ASM_MESON_TAC [NUMBER_FIELD_HOMOMORPHIC_PREIMAGE])

  let NUMBER_FIELD_IDEAL_NORM_MUL ← prove
    r"!k:A ring l:B ring h J1 J2.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        ring_ideal (ring_of_integers l) J1 /\
        ring_ideal (ring_of_integers l) J2
        ==> number_field_ideal_norm (k,l) h
              (ideal_prod (ring_of_integers l) J1 J2) =
            ideal_prod (ring_of_integers k)
              (number_field_ideal_norm (k,l) h J1)
              (number_field_ideal_norm (k,l) h J2)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN SUBGOAL_THEN (← q r"dedekind_domain(ring_of_integers k:A ring) /\
    dedekind_domain(ring_of_integers l:B ring)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS], ALL_TAC] THEN ASM_CASES_TAC (← q r"J1 = {ring_0 l:B}") THENL [ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_0, RING_IDEAL_IMP_SUBSET, (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") IDEAL_PROD_LZERO))] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") IDEAL_PROD_LZERO)) THEN MATCH_MP_TAC RING_IDEAL_IMP_SUBSET THEN REWRITE_TAC [NUMBER_FIELD_IDEAL_NORM_IDEAL], ALL_TAC] THEN ASM_CASES_TAC (← q r"J2 = {ring_0 l:B}") THENL [ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_0, RING_IDEAL_IMP_SUBSET, (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") IDEAL_PROD_RZERO))] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") IDEAL_PROD_RZERO)) THEN MATCH_MP_TAC RING_IDEAL_IMP_SUBSET THEN REWRITE_TAC [NUMBER_FIELD_IDEAL_NORM_IDEAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers l) (ideal_prod (ring_of_integers l) J1 J2) /\
    ~(ideal_prod (ring_of_integers l) J1 J2 = {ring_0 l:B})") STRIP_ASSUME_TAC THENL [REWRITE_TAC [RING_IDEAL_IDEAL_PROD] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"J1:B->bool"), (← q r"J2:B->bool")] IDEAL_PROD_EQ_ZERO) THEN ASM_SIMP_TAC [DEDEKIND_IMP_INTEGRAL_DOMAIN, RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"number_field_ideal_norm (k,l) (h:A->B)
                    (ideal_prod (ring_of_integers l) J1 J2)"), (← q r"ideal_prod (ring_of_integers k)
                    (number_field_ideal_norm (k,l) (h:A->B) J1)
                    (number_field_ideal_norm (k,l) (h:A->B) J2)")] DEDEKIND_IDEAL_EQ_VALUATION) THEN ANTS_TAC THENL [ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_IDEAL, RING_OF_INTEGERS, NUMBER_FIELD_IDEAL_NORM_EQ_0, RING_IDEAL_IDEAL_PROD, (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") IDEAL_PROD_EQ_ZERO)), DEDEKIND_IMP_INTEGRAL_DOMAIN], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [RING_OF_INTEGERS] THEN X_GEN_TAC (← q r"p:A->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:A->bool"), (← q r"number_field_ideal_norm (k,l) (h:A->B) J1"), (← q r"number_field_ideal_norm (k,l) (h:A->B) J2")] IDEAL_VALUATION_IDEAL_PROD) THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_IDEAL, RING_OF_INTEGERS, NUMBER_FIELD_IDEAL_NORM_EQ_0] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_VALUATION] THEN MATCH_MP_TAC NUMBER_FIELD_NORM_EXPONENT_ADD THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_IDEAL_NORM_PRIME ← prove
    r"!k:A ring l:B ring h p P.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P
        ==> number_field_ideal_norm (k,l) h P =
            ideal_pow (ring_of_integers k) p
              (residue_degree (ring_of_integers k,ring_of_integers l) h P)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN SUBGOAL_THEN (← q r"dedekind_domain(ring_of_integers k:A ring) /\
    dedekind_domain(ring_of_integers l:B ring)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(P = {ring_0 l:B})") ASSUME_TAC THENL [MATCH_MP_TAC NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO THEN MAP_EVERY EXISTS_TAC [(← q r"k:A ring"), (← q r"h:A->B"), (← q r"p:A->bool")] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"number_field_ideal_norm (k,l) (h:A->B) P"), (← q r"ideal_pow (ring_of_integers k) p
                   (residue_degree (ring_of_integers k,ring_of_integers l)
                      (h:A->B) P)")] DEDEKIND_IDEAL_EQ_VALUATION) THEN ANTS_TAC THENL [ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_IDEAL, RING_OF_INTEGERS, NUMBER_FIELD_IDEAL_NORM_EQ_0, RING_IDEAL_IDEAL_POW, PRIME_IMP_RING_IDEAL, DEDEKIND_IMP_INTEGRAL_DOMAIN, (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") IDEAL_POW_EQ_ZERO))], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [RING_OF_INTEGERS] THEN X_GEN_TAC (← q r"q:A->bool") THEN STRIP_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_VALUATION, PRIME_IMP_RING_IDEAL] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"q:A->bool"), (← q r"p:A->bool"), (← q r"P:B->bool")] NUMBER_FIELD_NORM_EXPONENT_PRIME) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"q:A->bool"), (← q r"p:A->bool"), (← q r"residue_degree (ring_of_integers k,ring_of_integers l)
                    (h:A->B) P")] IDEAL_VALUATION_IDEAL_POW) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"q:A->bool"), (← q r"p:A->bool")] IDEAL_VALUATION_PRIME) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [MULT_CLAUSES])

  let NUMBER_FIELD_IDEAL_NORM_EXTENSION ← prove
    r"!k:A ring l:B ring h j.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        ring_ideal (ring_of_integers k) j
        ==> number_field_ideal_norm (k,l) h
              (ideal_generated (ring_of_integers l) (IMAGE h j)) =
            ideal_pow (ring_of_integers k) j (extension_degree(k,l) h)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN SUBGOAL_THEN (← q r"dedekind_domain(ring_of_integers k:A ring) /\
    dedekind_domain(ring_of_integers l:B ring)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN SUBGOAL_THEN (← q r"~(extension_degree(k:A ring,l:B ring) h = 0)") ASSUME_TAC THENL [ASM_SIMP_TAC [EXTENSION_DEGREE_EQ_0, FINITE_IMP_FIELD_EXTENSION], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"j:A->bool")] RING_OF_INTEGERS_IDEAL_EXTENSION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT2) THEN ASM_CASES_TAC (← q r"j = {ring_0 k:A}") THENL [UNDISCH_THEN (← q r"j = {ring_0 k:A}") SUBST_ALL_TAC THEN REWRITE_TAC [IMAGE_CLAUSES] THEN REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_0 (← ASSUME (← q r"ring_homomorphism(k:A ring,l:B ring) h")))] THEN REWRITE_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") IDEAL_GENERATED_0))] THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_0] THEN CONV_TAC SYM_CONV THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"{ring_0 k:A}"), (← q r"extension_degree(k:A ring,l:B ring) h")] IDEAL_POW_EQ_ZERO) THEN ASM_SIMP_TAC [DEDEKIND_IMP_INTEGRAL_DOMAIN, RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"number_field_ideal_norm (k,l) (h:A->B)
                    (ideal_generated (ring_of_integers l) (IMAGE h j))"), (← q r"ideal_pow (ring_of_integers k) j
                    (extension_degree(k:A ring,l:B ring) h)")] DEDEKIND_IDEAL_EQ_VALUATION) THEN ANTS_TAC THENL [ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_IDEAL, RING_OF_INTEGERS, NUMBER_FIELD_IDEAL_NORM_EQ_0, RING_IDEAL_IDEAL_POW, DEDEKIND_IMP_INTEGRAL_DOMAIN, RING_IDEAL_IDEAL_GENERATED, (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") IDEAL_POW_EQ_ZERO))], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [RING_OF_INTEGERS] THEN X_GEN_TAC (← q r"q:A->bool") THEN STRIP_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_VALUATION, RING_IDEAL_IDEAL_GENERATED, NUMBER_FIELD_NORM_EXPONENT_EXTENSION] THEN MATCH_MP_TAC (← GSYM IDEAL_VALUATION_IDEAL_POW) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS])

  let NUMBER_FIELD_IDEAL_NORM_CARRIER ← prove
    r"!k:A ring l:B ring h.
        field k /\ number_field l /\ ring_homomorphism(k,l) h
        ==> number_field_ideal_norm (k,l) h
              (ring_carrier(ring_of_integers l)) =
            ring_carrier(ring_of_integers k)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"ring_carrier(ring_of_integers k:A ring)")] NUMBER_FIELD_IDEAL_NORM_EXTENSION) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"ring_carrier(ring_of_integers k:A ring)")] RING_OF_INTEGERS_IDEAL_EXTENSION) THEN ASM_REWRITE_TAC [RING_IDEAL_CARRIER] THEN DISCH_THEN (SUBST1_TAC o CONJUNCT1) THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [IDEAL_POW_CARRIER])

  let NUMBER_FIELD_IDEAL_NORM_POW ← prove
    r"!k:A ring l:B ring h J n.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        ring_ideal (ring_of_integers l) J
        ==> number_field_ideal_norm (k,l) h
              (ideal_pow (ring_of_integers l) J n) =
            ideal_pow (ring_of_integers k)
              (number_field_ideal_norm (k,l) h J) n"
    (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC [IDEAL_POW_0, IDEAL_POW_SUC, RING_IDEAL_IDEAL_POW, NUMBER_FIELD_IDEAL_NORM_CARRIER, NUMBER_FIELD_IDEAL_NORM_MUL])

  let NUMBER_FIELD_IDEAL_NORM_TOWER ← prove
    r"!k:A ring l:B ring m:C ring h1 h2 J.
        field k /\ field l /\ number_field m /\
        ring_homomorphism(k,l) h1 /\ ring_homomorphism(l,m) h2 /\
        ring_ideal (ring_of_integers m) J
        ==> number_field_ideal_norm (k,m) (h2 o h1) J =
            number_field_ideal_norm (k,l) h1
              (number_field_ideal_norm (l,m) h2 J)"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"number_field(l:B ring)") ASSUME_TAC THENL [ASM_MESON_TAC [NUMBER_FIELD_HOMOMORPHIC_PREIMAGE], ALL_TAC] THEN SUBGOAL_THEN (← q r"number_field(k:A ring)") ASSUME_TAC THENL [ASM_MESON_TAC [NUMBER_FIELD_HOMOMORPHIC_PREIMAGE], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_homomorphism(k:A ring,m:C ring) ((h2:B->C) o (h1:A->B))") ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_COMPOSE], ALL_TAC] THEN SUBGOAL_THEN (← q r"dedekind_domain(ring_of_integers k:A ring) /\
    dedekind_domain(ring_of_integers l:B ring)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS], ALL_TAC] THEN ASM_CASES_TAC (← q r"J = {ring_0 m:C}") THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_0] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"number_field_ideal_norm (k,m) ((h2:B->C) o (h1:A->B)) J"), (← q r"number_field_ideal_norm (k,l) (h1:A->B)
                    (number_field_ideal_norm (l,m) (h2:B->C) J)")] DEDEKIND_IDEAL_EQ_VALUATION) THEN ANTS_TAC THENL [ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_IDEAL, RING_OF_INTEGERS, NUMBER_FIELD_IDEAL_NORM_EQ_0], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [RING_OF_INTEGERS] THEN X_GEN_TAC (← q r"p:A->bool") THEN STRIP_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_VALUATION, NUMBER_FIELD_IDEAL_NORM_IDEAL, NUMBER_FIELD_IDEAL_NORM_EQ_0] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"m:C ring"), (← q r"h1:A->B"), (← q r"h2:B->C"), (← q r"p:A->bool"), (← q r"J:C->bool")] NUMBER_FIELD_NORM_EXPONENT_TOWER) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC (← q r"P:B->bool") THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN REWRITE_TAC [] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC NUMBER_FIELD_IDEAL_NORM_VALUATION THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO THEN MAP_EVERY EXISTS_TAC [(← q r"k:A ring"), (← q r"h1:A->B"), (← q r"p:A->bool")] THEN ASM_REWRITE_TAC [])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_NORM_VALUATION, number_field_ideal_norm,
           NUMBER_FIELD_IDEAL_NORM_IDEAL, NUMBER_FIELD_IDEAL_NORM_PRINCIPAL,
           NUMBER_FIELD_IDEAL_NORM_EXTENSION_SUBSET, NUMBER_FIELD_IDEAL_NORM_VALUATION,
           NUMBER_FIELD_IDEAL_NORM_0, NUMBER_FIELD_IDEAL_NORM_EQ_0,
           NUMBER_FIELD_IDEAL_NORM_VALUATIONS, NUMBER_FIELD_IDEAL_NORM_MUL,
           NUMBER_FIELD_IDEAL_NORM_PRIME, NUMBER_FIELD_IDEAL_NORM_EXTENSION,
           NUMBER_FIELD_IDEAL_NORM_CARRIER, NUMBER_FIELD_IDEAL_NORM_POW,
           NUMBER_FIELD_IDEAL_NORM_TOWER }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- ideal_norm_extension.ml phrases from line 1436 to 1501                 -/
/- ---------------------------------------------------------------------- -/

structure IdealNormExtension03 where
  -- @@FIELDS
  NUMBER_FIELD_IDEAL_NORM_IDEAL_NORM : thm
  NUMBER_FIELD_GALOIS_PRODUCT_IDEAL_NORM : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupIdealNormExtension03 [HolBase] (D : IdealNormExtensionDeps) (BIdealNormExtension01 : IdealNormExtension01) (BIdealNormExtension02 : IdealNormExtension02) :
    ExceptT String IO IdealNormExtension03 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, TAUT, .. } := D
  let { DEDEKIND_IDEAL_EQ_VALUATION, DEDEKIND_IDEAL_INDUCT,
        DEDEKIND_IMP_INTEGRAL_DOMAIN, DEDEKIND_RING_OF_INTEGERS, EXISTS_UNIQUE_THM,
        FINITE_GALOIS_GROUP, GALOIS_GROUP_RING_OF_INTEGERS_IDEAL,
        GALOIS_IMP_FIELD_EXTENSION, IDEAL_NORM_CARRIER, IDEAL_NORM_IDEAL_POW,
        IDEAL_POW_EQ_ZERO, IDEAL_PRODUCT_EQ_ZERO, NUMBER_FIELD_HOMOMORPHIC_PREIMAGE,
        NUMBER_FIELD_IDEAL_NORM_MUL_Q, NUMBER_FIELD_IDEAL_VALUATION_EXTENSION,
        NUMBER_FIELD_TOWER_LAW, PRIME_IMP_RING_IDEAL, RING_IDEAL_IDEAL_GENERATED,
        RING_IDEAL_IDEAL_POW, RING_IDEAL_IDEAL_PRODUCT,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_OF_INTEGERS,
        RING_OF_INTEGERS_FINITE_QUOTIENT, RING_OF_INTEGERS_IDEAL_EXTENSION,
        RING_OF_INTEGERS_IDEAL_NORM_PRIME, RING_OF_INTEGERS_PRIME_IDEAL_BELOW,
        field_extension, .. } := D.core1
  let { NUMBER_FIELD_GALOIS_PRODUCT_VALUATION, .. } := BIdealNormExtension01
  let { NUMBER_FIELD_IDEAL_NORM_CARRIER, NUMBER_FIELD_IDEAL_NORM_EQ_0,
        NUMBER_FIELD_IDEAL_NORM_IDEAL, NUMBER_FIELD_IDEAL_NORM_MUL,
        NUMBER_FIELD_IDEAL_NORM_PRIME, NUMBER_FIELD_IDEAL_NORM_VALUATION, .. } := BIdealNormExtension02
  -- @@SCOPE END

  let NUMBER_FIELD_IDEAL_NORM_IDEAL_NORM ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"a /\ b /\ c /\ d /\ e ==> f <=>
                    a /\ b /\ c ==> d /\ e ==> f")
    prove
      r"!k:A ring l:B ring h J.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          ring_ideal (ring_of_integers l) J /\ ~(J = {ring_0 l})
          ==> ideal_norm (ring_of_integers k)
                (number_field_ideal_norm (k,l) h J) =
              ideal_norm (ring_of_integers l) J"
      (REPEAT GEN_TAC THEN REWRITE_TAC [r1] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN SUBGOAL_THEN (← q r"dedekind_domain(ring_of_integers k:A ring) /\
      dedekind_domain(ring_of_integers l:B ring)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS], ALL_TAC] THEN SPEC_TAC ((← q r"J:B->bool"), (← q r"J:B->bool")) THEN MP_TAC (← ISPEC (← q r"ring_of_integers l:B ring") DEDEKIND_IDEAL_INDUCT) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_CARRIER, IDEAL_NORM_CARRIER] THEN MAP_EVERY X_GEN_TAC [(← q r"P:B->bool"), (← q r"J:B->bool")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"P:B->bool")] RING_OF_INTEGERS_PRIME_IDEAL_BELOW) THEN ASM_REWRITE_TAC [EXISTS_UNIQUE_THM] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"p:A->bool") STRIP_ASSUME_TAC) o CONJUNCT1) THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_MUL, PRIME_IMP_RING_IDEAL] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"P:B->bool")] NUMBER_FIELD_IDEAL_NORM_PRIME) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ideal_pow (ring_of_integers k) p
                      (residue_degree (ring_of_integers k,ring_of_integers l)
                         (h:A->B) P)"), (← q r"number_field_ideal_norm (k,l) (h:A->B) J")] NUMBER_FIELD_IDEAL_NORM_MUL_Q) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, NUMBER_FIELD_IDEAL_NORM_IDEAL, NUMBER_FIELD_IDEAL_NORM_EQ_0, PRIME_IMP_RING_IDEAL, DEDEKIND_IMP_INTEGRAL_DOMAIN, (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") IDEAL_POW_EQ_ZERO))], DISCH_THEN SUBST1_TAC] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"P:B->bool"), (← q r"J:B->bool")] NUMBER_FIELD_IDEAL_NORM_MUL_Q) THEN ANTS_TAC THENL [ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], DISCH_THEN SUBST1_TAC] THEN ASM_REWRITE_TAC [] THEN AP_THM_TAC THEN AP_TERM_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"P:B->bool")] RING_OF_INTEGERS_IDEAL_NORM_PRIME) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:A->bool"), (← q r"residue_degree (ring_of_integers k,ring_of_integers l)
                      (h:A->B) P")] IDEAL_NORM_IDEAL_POW) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS, RING_OF_INTEGERS_FINITE_QUOTIENT])

  let NUMBER_FIELD_GALOIS_PRODUCT_IDEAL_NORM ← prove
    r"!k:A ring l:B ring h J.
        number_field l /\ galois_extension(k,l) h /\
        ring_ideal (ring_of_integers l) J /\ ~(J = {ring_0 l})
        ==> ideal_product (ring_of_integers l)
              (group_carrier(galois_group(k,l) h)) (\g. IMAGE g J) =
            ideal_generated (ring_of_integers l)
              (IMAGE h (number_field_ideal_norm (k,l) h J))"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"field k /\ ring_homomorphism(k,l) (h:A->B)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [GALOIS_IMP_FIELD_EXTENSION, field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITE_GALOIS_GROUP)) THEN SUBGOAL_THEN (← q r"dedekind_domain(ring_of_integers k:A ring) /\
    dedekind_domain(ring_of_integers l:B ring)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"!g. g IN group_carrier(galois_group(k:A ring,l:B ring) h)
        ==> ring_ideal (ring_of_integers l) (IMAGE g J) /\
            ~(IMAGE g J = {ring_0 l})") ASSUME_TAC THENL [ASM_MESON_TAC [GALOIS_GROUP_RING_OF_INTEGERS_IDEAL], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"number_field_ideal_norm (k,l) (h:A->B) J")] RING_OF_INTEGERS_IDEAL_EXTENSION) THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_IDEAL, NUMBER_FIELD_IDEAL_NORM_EQ_0] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT2) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"ideal_product (ring_of_integers l)
                    (group_carrier(galois_group(k:A ring,l:B ring) h))
                    (\g. IMAGE g (J:B->bool))"), (← q r"ideal_generated (ring_of_integers l)
                    (IMAGE (h:A->B) (number_field_ideal_norm (k,l) h J))")] DEDEKIND_IDEAL_EQ_VALUATION) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_PRODUCT] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"group_carrier(galois_group(k:A ring,l:B ring) h)"), (← q r"\g:B->B. IMAGE g (J:B->bool)")] IDEAL_PRODUCT_EQ_ZERO) THEN ASM_SIMP_TAC [DEDEKIND_IMP_INTEGRAL_DOMAIN, RING_OF_INTEGERS] THEN ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [RING_OF_INTEGERS] THEN X_GEN_TAC (← q r"Q:B->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"Q:B->bool")] RING_OF_INTEGERS_PRIME_IDEAL_BELOW) THEN ASM_REWRITE_TAC [EXISTS_UNIQUE_THM] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"q:A->bool") STRIP_ASSUME_TAC) o CONJUNCT1) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"q:A->bool"), (← q r"Q:B->bool"), (← q r"J:B->bool")] NUMBER_FIELD_GALOIS_PRODUCT_VALUATION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"q:A->bool"), (← q r"Q:B->bool"), (← q r"number_field_ideal_norm (k,l) (h:A->B) J")] NUMBER_FIELD_IDEAL_VALUATION_EXTENSION) THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_IDEAL, NUMBER_FIELD_IDEAL_NORM_EQ_0] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_VALUATION])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_IDEAL_NORM_IDEAL_NORM, NUMBER_FIELD_GALOIS_PRODUCT_IDEAL_NORM }
  -- @@RETURN END

end HolANT.IdealNormExtension
