/- ========================================================================= -/
/- ANT: The different of an extension of number fields                     -/
/- ========================================================================= -/
/- File: HolANT/DifferentExtension.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/different_extension.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antdifferentextensiondiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, ANT/ideal_arith.ml, Library/products.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/prime_split.ml, ANT/norm_index.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/finite_field_trace.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/classgroup.ml, ANT/relative_split.ml, ANT/relative_degree.ml, ANT/nf_valuation.ml, ANT/integrality.ml, ANT/different.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.DifferentExtension fills them).

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
import HolANT.PrimeSplit
import HolANT.NormIndex
import HolANT.Discriminant
import HolANT.TraceForm
import HolANT.FiniteFieldTrace
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.Classgroup
import HolANT.RelativeSplit
import HolANT.RelativeDegree
import HolANT.NfValuation
import HolANT.Integrality
import HolANT.Different

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
open HolANT.PrimeSplit
open HolANT.NormIndex
open HolANT.Discriminant
open HolANT.TraceForm
open HolANT.FiniteFieldTrace
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.Classgroup
open HolANT.RelativeSplit
open HolANT.RelativeDegree
open HolANT.NfValuation
open HolANT.Integrality
open HolANT.Different

namespace HolANT.DifferentExtension

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ALGEBRA_TRACE_FREE_BASIS_MATRIX ALGEBRA_TRACE_NILPOTENT
   ALGEBRA_TRACE_NORM_IN_CARRIER ALGEBRA_TRACE_NORM_TOWER
   ALGEBRA_TRACE_QUOTIENT_COMAXIMAL_NONZERO ALGEBRA_TRACE_SCALAR
   BASIS_COORDINATES_EXPAND BASIS_COORDINATES_IN_CARRIER
   BASIS_DISCRIMINANT_TIMES_COORD CARD_IMAGE_INJ CARD_NUMSEG_LT
   DEDEKIND_IDEAL_MEMBER_PRINCIPAL_MULTIPLE DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT
   DEDEKIND_IDEAL_PROD_SUBSET_CANCEL DEDEKIND_IDEAL_SUBSET_POW_VALUATION
   DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL DEDEKIND_RING_OF_INTEGERS EQ_EXP EQ_TRANS
   EXISTS_UNIQUE_THM EXTENSION EXTENSION_LINCOMB_ADD EXTENSION_LINCOMB_LMUL
   FIELD_HOMOMORPHISM_INV FIELD_IMP_INTEGRAL_DOMAIN FIELD_QUOTIENT_RING
   FINITE_EXTENSION_RING_MATROID FINITE_IMP_FIELD_EXTENSION FINITE_NUMSEG_LT
   FORALL_IN_GSPEC FORALL_IN_IMAGE FREE_BASIS_EXISTS FREE_BASIS_FIELD
   FREE_BASIS_HAS_SIZE FREE_BASIS_INDEPENDENT FREE_BASIS_INDEPENDENT_EQ
   FREE_BASIS_IN_CARRIER FUN_IN_IMAGE HAS_SIZE IDEAL_EXTENSION_POW_SUPPLEMENT
   IDEAL_GENERATED_EQ_0 IDEAL_GENERATED_IMAGE_IDEAL_GENERATED
   IDEAL_GENERATED_INC IDEAL_GENERATED_MINIMAL IDEAL_GENERATED_RING_IDEAL
   IDEAL_GENERATED_SING_ALT IDEAL_NORM_GT_1 IDEAL_POW_0 IDEAL_POW_1
   IDEAL_POW_ANTIMONO IDEAL_POW_MONO IDEAL_POW_PRINCIPAL IDEAL_POW_SUC
   IDEAL_PROD_CARRIER IDEAL_PROD_COMAXIMAL IDEAL_PROD_COMM IDEAL_PROD_EQ_ZERO
   IDEAL_PROD_HOMOMORPHIC_IMAGE IDEAL_PROD_IDEAL_GENERATED IDEAL_PROD_MINIMAL
   IDEAL_PROD_MONO IDEAL_PROD_RZERO IMAGE_CLAUSES IMP_CONJ
   INTEGRAL_DOMAIN_MUL_LCANCEL INTEGRAL_DOMAIN_RING_OF_INTEGERS IN_ELIM_THM
   IN_IDEAL_GENERATED_SELF IN_IMAGE IN_RING_IDEAL_0 IN_RING_IDEAL_RMUL IN_SING
   IN_SUBRING_0 IN_SUBRING_1 IN_SUBRING_ADD IN_SUBRING_MUL IN_SUBRING_POW
   IN_SUBRING_SUB LE_REFL MATROID_BASIS_LARGE_INDEPENDENT
   MAXIMAL_IDEAL_COMAXIMAL MAXIMAL_IDEAL_IMP_PSUBSET MAXIMAL_IMP_RING_IDEAL
   MONO_EXISTS MONO_FORALL NOT_FORALL_THM NOT_IMP NOT_LE : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (NUMBER_FIELD_CODIFFERENT_BASIS_DISCRIMINANT
   NUMBER_FIELD_CODIFFERENT_DIFFERENT NUMBER_FIELD_CODIFFERENT_DIV
   NUMBER_FIELD_DIFFERENT_NONZERO NUMBER_FIELD_HOMOMORPHIC_PREIMAGE
   NUMBER_FIELD_IDEAL_NORM_EXTENSION_Q NUMBER_FIELD_IMP_FIELD
   NUMBER_FIELD_INDEPENDENT_MOD_IDEAL NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS
   NUMBER_FIELD_TOWER_LAW NUMBER_FIELD_TRACE_INTEGRAL PRIME_IDEAL_IMP_PSUBSET
   PRIME_IDEAL_IMP_SUBSET PRIME_IMP_RING_IDEAL PSUBSET PSUBSET_IRREFL
   QUOTIENT_RING_0 QUOTIENT_RING_CARRIER QUOTIENT_RING_MUL
   RESIDUE_DEGREE_QUOTIENT_RING RIGHT_EXISTS_IMP_THM RING_ADD_LDISTRIB
   RING_COSET_EQ RING_COSET_EQ_IDEAL RING_HOMOMORPHISM_0
   RING_HOMOMORPHISM_COMPOSE RING_HOMOMORPHISM_IN_CARRIER RING_HOMOMORPHISM_MUL
   RING_HOMOMORPHISM_POW RING_HOMOMORPHISM_RING_COSET
   RING_HOMOMORPHISM_RING_OF_INTEGERS RING_HOMOMORPHISM_SUM
   RING_HOMOMORPHISM_SUM_MUL RING_IDEAL_IDEAL_GENERATED RING_IDEAL_IDEAL_POW
   RING_IDEAL_IDEAL_PROD RING_IDEAL_IDEAL_QUOTIENT RING_IDEAL_IMP_NONEMPTY
   RING_IDEAL_IMP_SUBSET RING_IDEAL_NUMBER_FIELD_DIFFERENT RING_INV
   RING_MATROID_BASIS RING_MATROID_INDEPENDENT RING_MONOMORPHISM_EQ_0
   RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_MUL RING_MUL_ASSOC
   RING_MUL_IN_IDEAL_PROD RING_MUL_LZERO RING_MUL_RID RING_MUL_RNEG
   RING_MUL_RZERO RING_MUL_SYM RING_NILPOTENT RING_OF_INTEGERS
   RING_OF_INTEGERS_FINITE_QUOTIENT RING_OF_INTEGERS_IDEAL_EXTENSION
   RING_OF_INTEGERS_IDEAL_EXTENSION_CONTRACTION_PRIME
   RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME
   RING_OF_INTEGERS_IN_IDEAL_GENERATED_SING RING_OF_INTEGERS_PRIME_IDEAL_BELOW
   RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION RING_OF_INTEGERS_SUBRING
   RING_OF_INTEGERS_SUBSET RING_OF_INTEGERS_SUBSET_CODIFFERENT RING_POW
   RING_SPAN_SELF RING_SUM RING_SUM_EQ RING_SUM_EQ_0 RING_SUM_RING_OF_INTEGERS
   SING_SUBSET SKOLEM_THM SUBSET SUBSET_REFL SUBSET_TRANS extension_degree
   field_extension free_basis ideal_norm ideal_quotient number_field_codifferent
   number_field_different o_DEF ramification_index ring_ideal ring_spanning
   subring_of : thm)
  deriving Inhabited

/-- What different_extension.ml uses from Session besides theorems. -/
structure DifferentExtensionDeps where
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
/- different_extension.ml phrases from line 81 to 378                     -/
/- ---------------------------------------------------------------------- -/

structure DifferentExtension01 where
  -- @@FIELDS
  RING_OF_INTEGERS_BASIS_MOD_PRIME : thm
  RING_OF_INTEGERS_BASIS_MOD_PRIME_FREE : thm
  RING_OF_INTEGERS_LOCAL_BASIS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDifferentExtension01 [HolBase] (D : DifferentExtensionDeps) :
    ExceptT String IO DifferentExtension01 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, MESON, MESON_TAC, RING_RULE, SET_TAC,
        TAUT, .. } := D
  let { BASIS_COORDINATES_EXPAND, BASIS_COORDINATES_IN_CARRIER,
        BASIS_DISCRIMINANT_TIMES_COORD, CARD_IMAGE_INJ, CARD_NUMSEG_LT,
        DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT, DEDEKIND_IDEAL_SUBSET_POW_VALUATION,
        DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL, DEDEKIND_RING_OF_INTEGERS, EQ_EXP,
        EQ_TRANS, EXTENSION_LINCOMB_ADD, EXTENSION_LINCOMB_LMUL, FIELD_QUOTIENT_RING,
        FINITE_EXTENSION_RING_MATROID, FINITE_NUMSEG_LT, FORALL_IN_IMAGE,
        FREE_BASIS_EXISTS, FREE_BASIS_FIELD, FREE_BASIS_HAS_SIZE,
        FREE_BASIS_INDEPENDENT, FREE_BASIS_INDEPENDENT_EQ, FREE_BASIS_IN_CARRIER,
        FUN_IN_IMAGE, HAS_SIZE, IDEAL_EXTENSION_POW_SUPPLEMENT, IDEAL_GENERATED_EQ_0,
        IDEAL_GENERATED_IMAGE_IDEAL_GENERATED, IDEAL_GENERATED_INC,
        IDEAL_GENERATED_SING_ALT, IDEAL_NORM_GT_1, IDEAL_POW_SUC, IDEAL_PROD_COMM,
        IDEAL_PROD_HOMOMORPHIC_IMAGE, IDEAL_PROD_MONO, IMAGE_CLAUSES, IMP_CONJ,
        IN_ELIM_THM, IN_RING_IDEAL_0, IN_SUBRING_0, IN_SUBRING_1, IN_SUBRING_ADD,
        IN_SUBRING_MUL, IN_SUBRING_SUB, LE_REFL, MATROID_BASIS_LARGE_INDEPENDENT,
        MAXIMAL_IDEAL_IMP_PSUBSET, MAXIMAL_IMP_RING_IDEAL, MONO_FORALL, NOT_FORALL_THM,
        NOT_IMP, .. } := D.core1
  let { NUMBER_FIELD_CODIFFERENT_BASIS_DISCRIMINANT, NUMBER_FIELD_HOMOMORPHIC_PREIMAGE,
        NUMBER_FIELD_IDEAL_NORM_EXTENSION_Q, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_INDEPENDENT_MOD_IDEAL, NUMBER_FIELD_TOWER_LAW,
        NUMBER_FIELD_TRACE_INTEGRAL, PRIME_IDEAL_IMP_PSUBSET, PRIME_IDEAL_IMP_SUBSET,
        PRIME_IMP_RING_IDEAL, PSUBSET, PSUBSET_IRREFL, QUOTIENT_RING_0,
        QUOTIENT_RING_CARRIER, RESIDUE_DEGREE_QUOTIENT_RING, RIGHT_EXISTS_IMP_THM,
        RING_COSET_EQ, RING_COSET_EQ_IDEAL, RING_HOMOMORPHISM_0,
        RING_HOMOMORPHISM_IN_CARRIER, RING_HOMOMORPHISM_RING_COSET,
        RING_HOMOMORPHISM_RING_OF_INTEGERS, RING_HOMOMORPHISM_SUM_MUL,
        RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_POW, RING_IDEAL_IDEAL_QUOTIENT,
        RING_IDEAL_IMP_SUBSET, RING_MATROID_BASIS, RING_MATROID_INDEPENDENT,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL, RING_MUL_IN_IDEAL_PROD,
        RING_MUL_LZERO, RING_OF_INTEGERS, RING_OF_INTEGERS_FINITE_QUOTIENT,
        RING_OF_INTEGERS_IDEAL_EXTENSION_CONTRACTION_PRIME,
        RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME, RING_OF_INTEGERS_SUBRING,
        RING_OF_INTEGERS_SUBSET, RING_OF_INTEGERS_SUBSET_CODIFFERENT, RING_SPAN_SELF,
        RING_SUM, RING_SUM_EQ, RING_SUM_EQ_0, RING_SUM_RING_OF_INTEGERS, SING_SUBSET,
        SKOLEM_THM, SUBSET, SUBSET_REFL, extension_degree, free_basis, ideal_norm,
        ring_spanning, .. } := D.core2
  -- @@SCOPE END

  let RING_OF_INTEGERS_BASIS_MOD_PRIME ← prove
    r"!k:A ring l:B ring h p.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
        ==> ?w. (!i. i < extension_degree(k,l) h
                     ==> w i IN ring_carrier(ring_of_integers l)) /\
                (!i j. i < extension_degree(k,l) h /\
                       j < extension_degree(k,l) h /\ w i = w j
                       ==> i = j) /\
                (!x. x IN ring_carrier(ring_of_integers l)
                     ==> ?c. (!i. c i IN ring_carrier(ring_of_integers k)) /\
                             ring_sub l x
                              (ring_sum l {i | i < extension_degree(k,l) h}
                                 (\i. ring_mul l (h(c i)) (w i))) IN
                             ideal_generated (ring_of_integers l)
                               (IMAGE h p)) /\
                (!c. (!i. c i IN ring_carrier(ring_of_integers k)) /\
                     ring_sum l {i | i < extension_degree(k,l) h}
                       (\i. ring_mul l (h(c i)) (w i)) IN
                     ideal_generated (ring_of_integers l) (IMAGE h p)
                     ==> !i. i < extension_degree(k,l) h ==> c i IN p)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ABBREV_TAC (← q r"n = extension_degree(k:A ring,l:B ring) h") THEN ABBREV_TAC (← q r"J = ideal_generated (ring_of_integers l) (IMAGE (h:A->B) p)") THEN SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers l) (J:B->bool)") ASSUME_TAC THENL [EXPAND_TAC "J" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] RING_OF_INTEGERS_IDEAL_EXTENSION_CONTRACTION_PRIME) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"maximal_ideal (ring_of_integers k) (p:A->bool)") ASSUME_TAC THENL [MATCH_MP_TAC DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_OF_INTEGERS], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_RING_IDEAL)) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring"), (← q r"h:A->B"), (← q r"J:B->bool")] RESIDUE_DEGREE_QUOTIENT_RING) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_OF_INTEGERS] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"g:(A->bool)->(B->bool)") STRIP_ASSUME_TAC) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN SUBGOAL_THEN (← q r"field(quotient_ring (ring_of_integers k) (p:A->bool)) /\
    FINITE(ring_carrier(quotient_ring (ring_of_integers k) (p:A->bool))) /\
    FINITE(ring_carrier(quotient_ring (ring_of_integers l) (J:B->bool)))") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_QUOTIENT_RING, RING_OF_INTEGERS_FINITE_QUOTIENT, MAXIMAL_IMP_RING_IDEAL], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"quotient_ring (ring_of_integers k) (p:A->bool)"), (← q r"quotient_ring (ring_of_integers l) (J:B->bool)"), (← q r"g:(A->bool)->(B->bool)"), (← q r"ring_carrier(quotient_ring (ring_of_integers l) (J:B->bool))")] FREE_BASIS_EXISTS) THEN ASM_REWRITE_TAC [ring_spanning, SUBSET_REFL, RING_SPAN_SELF] THEN ABBREV_TAC (← q r"m = extension_degree
         (quotient_ring (ring_of_integers k) (p:A->bool),
          quotient_ring (ring_of_integers l) (J:B->bool))
         (g:(A->bool)->(B->bool))") THEN DISCH_THEN (X_CHOOSE_TAC (← q r"G:num->(B->bool)")) THEN SUBGOAL_THEN (← q r"m:num = n") SUBST_ALL_TAC THENL [MP_TAC (← ISPECL [(← q r"g:(A->bool)->(B->bool)"), (← q r"quotient_ring (ring_of_integers k) (p:A->bool)"), (← q r"quotient_ring (ring_of_integers l) (J:B->bool)"), (← q r"m:num"), (← q r"G:num->(B->bool)")] FREE_BASIS_HAS_SIZE) THEN ASM_REWRITE_TAC [HAS_SIZE, (← GSYM ideal_norm)] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_IDEAL_NORM_EXTENSION_Q) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:A->bool")] IDEAL_NORM_GT_1) THEN ASM_SIMP_TAC [RING_OF_INTEGERS_FINITE_QUOTIENT, PRIME_IMP_RING_IDEAL] THEN ANTS_TAC THENL [ASM_MESON_TAC [MAXIMAL_IDEAL_IMP_PSUBSET, PSUBSET], ALL_TAC] THEN REWRITE_TAC [EQ_EXP] THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"?w:num->B. !i. i < n
                   ==> w i IN ring_carrier(ring_of_integers l) /\
                       G i = ring_coset (ring_of_integers l) J (w i)") STRIP_ASSUME_TAC THENL [REWRITE_TAC [(← GSYM SKOLEM_THM), RIGHT_EXISTS_IMP_THM] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o ((SPEC (← q r"i:num")) o (MATCH_MP FREE_BASIS_IN_CARRIER))) THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, IN_ELIM_THM] THEN MESON_TAC [], ALL_TAC] THEN EXISTS_TAC (← q r"w:num->B") THEN ASM_SIMP_TAC [] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"g:(A->bool)->(B->bool)"), (← q r"quotient_ring (ring_of_integers k) (p:A->bool)"), (← q r"quotient_ring (ring_of_integers l) (J:B->bool)"), (← q r"n:num"), (← q r"G:num->(B->bool)")] FREE_BASIS_FIELD) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o CONJUNCT2) THEN REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN DISCH_THEN (fun th => STRIP_TAC THEN MATCH_MP_TAC th) THEN ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o (MATCH_MP (← REWRITE_RULE [IMP_CONJ] RING_HOMOMORPHISM_IN_CARRIER))) THEN SUBGOAL_THEN (← q r"!c:num->A. (!i. i < n ==> c i IN ring_carrier(ring_of_integers k))
        ==> ring_coset (ring_of_integers l) J
              (ring_sum l {i | i < n}
                 (\i. ring_mul l ((h:A->B)(c i)) ((w:num->B) i))) =
            ring_sum (quotient_ring (ring_of_integers l) J) {i | i < n}
              (\i. ring_mul (quotient_ring (ring_of_integers l) J)
                     (g(ring_coset (ring_of_integers k) p (c i))) (G i))") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS (← q r"ring_sum (quotient_ring (ring_of_integers l) J) {i | i < n}
        (\i. ring_mul (quotient_ring (ring_of_integers l) J)
               (ring_coset (ring_of_integers l) J ((h:A->B)((c:num->A) i)))
               (ring_coset (ring_of_integers l) J (w i)))") THEN CONJ_TAC THENL [ALL_TAC, MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC [IN_ELIM_THM]] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"quotient_ring (ring_of_integers l) (J:B->bool)"), (← q r"ring_coset (ring_of_integers l) (J:B->bool)"), (← q r"{i:num | i < n}"), (← q r"\i. (h:A->B)((c:num->A) i)"), (← q r"w:num->B")] RING_HOMOMORPHISM_SUM_MUL) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_COSET, FINITE_NUMSEG_LT, IN_ELIM_THM] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_RING_OF_INTEGERS THEN ASM_SIMP_TAC [IN_ELIM_THM, (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_MUL))], ALL_TAC] THEN SUBGOAL_THEN (← q r"!c:num->A. (!i. i < n ==> c i IN ring_carrier(ring_of_integers k))
        ==> ring_sum l {i | i < n}
              (\i. ring_mul l ((h:A->B)(c i)) ((w:num->B) i)) IN
            ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN wPart lhand (rand o rand) RING_SUM_RING_OF_INTEGERS THEN ASM_SIMP_TAC [IN_ELIM_THM, (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_MUL))] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [RING_SUM], ALL_TAC] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o ((SPEC (← q r"ring_coset (ring_of_integers l) J (x:B)")) o (CONJUNCT1 o (CONJUNCT2 o (GEN_REWRITE_RULE id [free_basis]))))) THEN ANTS_TAC THENL [ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:num->A->bool") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"?c. !i. c i IN ring_carrier(ring_of_integers k) /\
              (i < n ==> (a:num->A->bool) i =
                         ring_coset (ring_of_integers k) p (c i))") STRIP_ASSUME_TAC THENL [REWRITE_TAC [(← GSYM SKOLEM_THM)] THEN X_GEN_TAC (← q r"i:num") THEN ASM_CASES_TAC (← q r"i:num < n") THEN ASM_REWRITE_TAC [] THENL [FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"i:num"))) THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, IN_ELIM_THM] THEN MESON_TAC [], MESON_TAC [IN_SUBRING_0, RING_OF_INTEGERS_SUBRING]], ALL_TAC] THEN EXISTS_TAC (← q r"c:num->A") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"J:B->bool"), (← q r"x:B"), (← q r"ring_sum l {i | i < n}
                     (\i. ring_mul l ((h:A->B)(c i)) ((w:num->B) i))")] RING_COSET_EQ) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_OF_INTEGERS], DISCH_THEN (SUBST1_TAC o (SYM o (REWRITE_RULE [RING_OF_INTEGERS])))] THEN FIRST_X_ASSUM (SUBST1_TAC o (checkM (fun th => (do if ← (do let z19 ← (do let z20 ← (pure th); pure (concl z20)); pure (is_eq z19)) then (do let z24 ← (q r"ring_coset (ring_of_integers l) J (x:B)"); let z23 ← (do let z21 ← (do let z22 ← (pure th); pure (concl z22)); liftExcept (lhs z21)); pure (z23 == z24)) else pure false)))) THEN FIRST_ASSUM (MP_TAC o ((SPEC (← q r"c:num->A")) o (checkM (fun th => (do if ← (do let z10 ← (do let z11 ← (pure th); pure (concl z11)); pure (is_forall z10)) then (do let z12 ← (do let z13 ← (pure th); pure (concl z13)); canM (fun z14 => (do let z15 ← (pure z14); find_termM (fun z16 => (do let z18 ← (pure z16); let z17 ← (q r"ring_coset (ring_of_integers l) (J:B->bool)"); pure (z17 == z18))) z15)) z12) else pure false))))) THEN ANTS_TAC THENL [ASM_SIMP_TAC [], DISCH_THEN SUBST1_TAC] THEN MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC [IN_ELIM_THM], ALL_TAC] THEN X_GEN_TAC (← q r"c:num->A") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"g:(A->bool)->(B->bool)"), (← q r"quotient_ring (ring_of_integers k) (p:A->bool)"), (← q r"quotient_ring (ring_of_integers l) (J:B->bool)"), (← q r"n:num"), (← q r"G:num->(B->bool)"), (← q r"\i. ring_coset (ring_of_integers k) p ((c:num->A) i)")] FREE_BASIS_INDEPENDENT) THEN ASM_SIMP_TAC [QUOTIENT_RING_0, RING_COSET_EQ_IDEAL] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"c:num->A")) o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_forall z1)) then (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); canM (fun z5 => (do let z6 ← (pure z5); find_termM (fun z7 => (do let z9 ← (pure z7); let z8 ← (q r"ring_coset (ring_of_integers l) (J:B->bool)"); pure (z8 == z9))) z6)) z3) else pure false))))) THEN ASM_SIMP_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"J:B->bool"), (← q r"ring_sum l {i | i < n}
                   (\i. ring_mul l ((h:A->B)(c i)) ((w:num->B) i))")] RING_COSET_EQ_IDEAL) THEN ASM_SIMP_TAC [])

  let RING_OF_INTEGERS_BASIS_MOD_PRIME_FREE ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"{i:num | i < n}"
    let q2 ← q r"w:num->B"
    let v3 ← ISPECL [q2, q1] CARD_IMAGE_INJ
    let q4 ← q r"extension_degree(k:A ring,l:B ring) h = n"
    let q5 ← q r"finite_extension(k:A ring,l:B ring) h"
    let q6 ← q r"l:B ring"
    let q7 ← q r"k:A ring"
    let q8 ← q r"h:A->B"
    let v9 ← ISPECL [q8, q7, q6] RING_MATROID_BASIS
    let q10 ← q r"w:num->B"
    let q11 ← q r"n:num"
    let q12 ← q r"l:B ring"
    let q13 ← q r"k:A ring"
    let q14 ← q r"h:A->B"
    let v15 ← ISPECL [q14, q13, q12, q11, q10] FREE_BASIS_FIELD
    let q16 ← q r"ideal_generated (ring_of_integers l)
                        (IMAGE (h:A->B) p)"
    let q17 ← q r"ring_of_integers l:B ring"
    let v18 ← ISPECL [q17, q16] IN_RING_IDEAL_0
    let q19 ← q r"ring_0 l:B"
    let q20 ← q r"!a b s. (a:B) = b /\ b IN s ==> a IN s"
    let r21 ← MESON [] q20
    let q22 ← q r"i:num"
    let q23 ← q r"\i. if i < n then (u:num->A) i else ring_0 k"
    let q24 ← q r"u:num->A"
    let q25 ← q r"p /\ q /\ r ==> p /\ q /\ r"
    let r26 ← TAUT q25
    let q27 ← q r"w:num->B"
    let q28 ← q r"{i:num | i < n}"
    let q29 ← q r"p:A->bool"
    let q30 ← q r"h:A->B"
    let q31 ← q r"l:B ring"
    let q32 ← q r"k:A ring"
    let v33 ← ISPECL [q32, q31, q30, q29, q28, q27] NUMBER_FIELD_INDEPENDENT_MOD_IDEAL
    let q34 ← q r"w:num->B"
    let q35 ← q r"n:num"
    let q36 ← q r"l:B ring"
    let q37 ← q r"k:A ring"
    let q38 ← q r"h:A->B"
    let v39 ← ISPECL [q38, q37, q36, q35, q34] FREE_BASIS_INDEPENDENT_EQ
    let q40 ← q r"ring_independent (k,l) (h:A->B) (IMAGE (w:num->B) {i | i < n})"
    let q41 ← q r"!i. i < n ==> (w:num->B) i IN ring_carrier l"
    let q42 ← q r"n = extension_degree(k:A ring,l:B ring) h"
    let q43 ← q r"h:A->B"
    let q44 ← q r"l:B ring"
    let q45 ← q r"k:A ring"
    let v46 ← ISPECL [q45, q44, q43] NUMBER_FIELD_TOWER_LAW
    let q47 ← q r"h:A->B"
    let q48 ← q r"l:B ring"
    let q49 ← q r"k:A ring"
    let v50 ← ISPECL [q49, q48, q47] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE
    prove
      r"!k:A ring l:B ring h p w.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          prime_ideal (ring_of_integers k) p /\
          (!i. i < extension_degree(k,l) h
               ==> w i IN ring_carrier(ring_of_integers l)) /\
          (!i j. i < extension_degree(k,l) h /\ j < extension_degree(k,l) h /\
                 w i = w j ==> i = j) /\
          (!c. (!i. c i IN ring_carrier(ring_of_integers k)) /\
               ring_sum l {i | i < extension_degree(k,l) h}
                 (\i. ring_mul l (h(c i)) (w i)) IN
               ideal_generated (ring_of_integers l) (IMAGE h p)
               ==> !i. i < extension_degree(k,l) h ==> c i IN p)
          ==> free_basis (k,l) h (extension_degree(k,l) h) w"
      (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))))) THEN MP_TAC v50 THEN MP_TAC v46 THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN DISCH_TAC THEN ABBREV_TAC q42 THEN SUBGOAL_THEN q41 ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN DISCH_THEN (LABEL_TAC "indep") THEN SUBGOAL_THEN q40 ASSUME_TAC THENL [MP_TAC v39 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC v33 THEN REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN ANTS_TAC THENL [ALL_TAC, SIMP_TAC []] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r26 THEN CONJ_TAC THENL [MATCH_MP_TAC PRIME_IMP_RING_IDEAL THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN CONJ_TAC THENL [ASM_MESON_TAC [PRIME_IDEAL_IMP_PSUBSET, PSUBSET_IRREFL], ALL_TAC] THEN X_GEN_TAC q24 THEN STRIP_TAC THEN USE_THEN "indep" (MP_TAC o (SPEC q23)) THEN REWRITE_TAC [] THEN ANTS_TAC THENL [ALL_TAC, SIMP_TAC []] THEN CONJ_TAC THENL [X_GEN_TAC q22 THEN COND_CASES_TAC THEN ASM_SIMP_TAC [] THEN SIMP_TAC [IN_SUBRING_0, RING_OF_INTEGERS_SUBRING], ALL_TAC] THEN MATCH_MP_TAC r21 THEN EXISTS_TAC q19 THEN CONJ_TAC THENL [FIRST_X_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [(← SYM th)])) THEN MATCH_MP_TAC RING_SUM_EQ THEN SIMP_TAC [IN_ELIM_THM], MP_TAC v18 THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, RING_OF_INTEGERS]], ALL_TAC] THEN MP_TAC v15 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC v9 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC MATROID_BASIS_LARGE_INDEPENDENT THEN UNDISCH_TAC q5 THEN ASM_SIMP_TAC [FINITE_EXTENSION_RING_MATROID, RING_MATROID_INDEPENDENT] THEN STRIP_TAC THEN UNDISCH_TAC q4 THEN ASM_REWRITE_TAC [extension_degree] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC v3 THEN ASM_REWRITE_TAC [IN_ELIM_THM, FINITE_NUMSEG_LT, CARD_NUMSEG_LT] THEN SIMP_TAC [LE_REFL])

  let RING_OF_INTEGERS_LOCAL_BASIS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r13 ← RING_RULE (← q r"ring_mul (r:B ring) a x =
      ring_add r (ring_mul r a m) (ring_mul r a (ring_sub r x m))")
    let r29 ← ARITH_RULE (← q r"~(SUC t <= t)")
    let r30 ← TAUT (← q r"p /\ (p ==> q) /\ (p /\ q ==> r) ==> p /\ q /\ r")
    prove
      r"!k:A ring l:B ring h p.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
          ==> ?w s. free_basis (k,l) h (extension_degree(k,l) h) w /\
                    (!i. i < extension_degree(k,l) h
                         ==> w i IN ring_carrier(ring_of_integers l)) /\
                    (!x. x IN ring_carrier(ring_of_integers l)
                         ==> ?c. (!i. c i IN ring_carrier(ring_of_integers k)) /\
                                 ring_sub l x
                                  (ring_sum l {i | i < extension_degree(k,l) h}
                                     (\i. ring_mul l (h(c i)) (w i))) IN
                                 ideal_generated (ring_of_integers l)
                                   (IMAGE h p)) /\
                    (!c. (!i. c i IN ring_carrier(ring_of_integers k)) /\
                         ring_sum l {i | i < extension_degree(k,l) h}
                           (\i. ring_mul l (h(c i)) (w i)) IN
                         ideal_generated (ring_of_integers l) (IMAGE h p)
                         ==> !i. i < extension_degree(k,l) h ==> c i IN p) /\
                    s IN ring_carrier(ring_of_integers k) /\ ~(s IN p) /\
                    !x. x IN ring_carrier(ring_of_integers l)
                        ==> ?c. (!i. c i IN ring_carrier(ring_of_integers k)) /\
                                ring_mul l (h s) x =
                                ring_sum l {i | i < extension_degree(k,l) h}
                                  (\i. ring_mul l (h(c i)) (w i))"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] RING_OF_INTEGERS_BASIS_MOD_PRIME) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"w:num->B") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"w:num->B")] RING_OF_INTEGERS_BASIS_MOD_PRIME_FREE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN EXISTS_TAC (← q r"w:num->B") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP NUMBER_FIELD_IMP_FIELD) o (checkM (fun th => (do let z52 ← (q r"number_field(l:B ring)"); let z51 ← (do let z50 ← (pure th); pure (concl z50)); pure (z51 == z52)))))) THEN ABBREV_TAC (← q r"n = extension_degree(k:A ring,l:B ring) h") THEN MP_TAC (← ISPEC (← q r"l:B ring") (← CONJUNCT1 RING_OF_INTEGERS_SUBRING)) THEN MP_TAC (← ISPEC (← q r"k:A ring") (← CONJUNCT1 RING_OF_INTEGERS_SUBRING)) THEN REPEAT DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP (← REWRITE_RULE [IMP_CONJ] RING_HOMOMORPHISM_IN_CARRIER))) THEN SUBGOAL_THEN (← q r"!i. i < n ==> (w:num->B) i IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN ABBREV_TAC (← q r"M = {y | ?c. (!i. c i IN ring_carrier(ring_of_integers k)) /\
                   y = ring_sum l {i | i < n}
                         (\i. ring_mul l ((h:A->B)(c i)) ((w:num->B) i))}") THEN SUBGOAL_THEN (← q r"!c. (!i. c i IN ring_carrier(ring_of_integers k))
          ==> ring_sum l {i | i < n}
                (\i. ring_mul l ((h:A->B)(c i)) ((w:num->B) i)) IN
              ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN wPart lhand (rand o rand) RING_SUM_RING_OF_INTEGERS THEN ASM_SIMP_TAC [IN_ELIM_THM, (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_MUL))] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [RING_SUM], ALL_TAC] THEN SUBGOAL_THEN (← q r"M SUBSET ring_carrier(ring_of_integers l) /\ ring_0 l IN M /\
      (!x y. x IN M /\ y IN M ==> ring_add l x y IN M) /\
      (!a x. a IN ring_carrier(ring_of_integers k) /\ x IN M
             ==> ring_mul l ((h:A->B) a) x IN M)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "M" THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL [GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [], EXISTS_TAC (← q r"\i:num. ring_0 k:A") THEN SIMP_TAC [IN_SUBRING_0, RING_OF_INTEGERS_SUBRING] THEN REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_0 (← ASSUME (← q r"ring_homomorphism(k:A ring,l:B ring) h")))] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_EQ_0 THEN ASM_SIMP_TAC [IN_ELIM_THM, RING_MUL_LZERO], MAP_EVERY X_GEN_TAC [(← q r"x:B"), (← q r"y:B")] THEN DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"c:num->A") STRIP_ASSUME_TAC) (X_CHOOSE_THEN (← q r"d:num->A") STRIP_ASSUME_TAC)) THEN EXISTS_TAC (← q r"\i. ring_add k ((c:num->A) i) (d i)") THEN ASM_SIMP_TAC [IN_SUBRING_ADD] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXTENSION_LINCOMB_ADD THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"x:B")] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"c:num->A") STRIP_ASSUME_TAC)) THEN EXISTS_TAC (← q r"\i. ring_mul k (a:A) ((c:num->A) i)") THEN ASM_SIMP_TAC [IN_SUBRING_MUL] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXTENSION_LINCOMB_LMUL THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"n:num"), (← q r"w:num->B"), (← q r"ring_1 l:B")] NUMBER_FIELD_CODIFFERENT_BASIS_DISCRIMINANT) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_OF_INTEGERS_SUBSET_CODIFFERENT) THEN ASM_REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN SIMP_TAC [IN_SUBRING_1, RING_OF_INTEGERS_SUBRING], ALL_TAC] THEN ABBREV_TAC (← q r"d = basis_discriminant (k:A ring,l:B ring) h n w") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!y. y IN ring_carrier(ring_of_integers l)
          ==> ring_mul l ((h:A->B) d) y IN M") ASSUME_TAC THENL [X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(y:B) IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"n:num"), (← q r"w:num->B"), (← q r"ring_carrier(ring_of_integers k:A ring)"), (← q r"y:B")] BASIS_DISCRIMINANT_TIMES_COORD) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [CONJ_TAC THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC NUMBER_FIELD_TRACE_INTEGRAL THEN ASM_SIMP_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_MUL))], DISCH_TAC] THEN EXPAND_TAC "M" THEN REWRITE_TAC [IN_ELIM_THM] THEN EXISTS_TAC (← q r"\i. if i < n
            then ring_mul k (d:A) (basis_coordinates (k,l) (h:A->B) n w y i)
            else ring_0 k") THEN REWRITE_TAC [] THEN CONJ_TAC THENL [GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [IN_SUBRING_0], ALL_TAC] THEN TRANS_TAC EQ_TRANS (← q r"ring_sum l {i | i < n}
          (\i. ring_mul l ((h:A->B)
                 (ring_mul k d (basis_coordinates (k,l) h n w y i)))
               ((w:num->B) i))") THEN CONJ_TAC THENL [ALL_TAC, MATCH_MP_TAC RING_SUM_EQ THEN SIMP_TAC [IN_ELIM_THM]] THEN SUBGOAL_THEN (← q r"(d:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [EXTENSION_LINCOMB_LMUL, BASIS_COORDINATES_IN_CARRIER, FINITE_NUMSEG_LT, IN_ELIM_THM] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC BASIS_COORDINATES_EXPAND THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"J = ideal_generated (ring_of_integers l) (IMAGE (h:A->B) p)") THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"M:B->bool")] IDEAL_EXTENSION_POW_SUPPLEMENT) THEN ASM_SIMP_TAC [PRIME_IDEAL_IMP_SUBSET, RING_OF_INTEGERS] THEN ANTS_TAC THENL [X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((← do let c := (← ASSUME (← q r"(x:B) IN ring_carrier(ring_of_integers l)")); pure (fun th => MATCH_MP th c)) o (checkM (fun th => (do if ← (do if ← (do let z34 ← (do let z35 ← (pure th); pure (concl z35)); pure (is_forall z34)) then (do let z36 ← (do let z37 ← (pure th); pure (concl z37)); canM (fun z38 => (do let z39 ← (pure z38); find_termM (fun z40 => (do let z42 ← (pure z40); let z41 ← (q r"J:B->bool"); pure (z41 == z42))) z39)) z36) else pure false) then (do let z43 ← (do let z44 ← (pure th); pure (concl z44)); canM (fun z45 => (do let z46 ← (pure z45); find_termM (fun z47 => (do let z49 ← (pure z47); let z48 ← (q r"ring_sub:B ring->B->B->B"); pure (z48 == z49))) z46)) z43) else pure false))))) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:num->A") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"ring_sum l {i | i < n}
          (\i. ring_mul l ((h:A->B)(c i)) ((w:num->B) i))") THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "M" THEN REWRITE_TAC [IN_ELIM_THM] THEN EXISTS_TAC (← q r"c:num->A") THEN ASM_REWRITE_TAC [], DISCH_TAC] THEN ABBREV_TAC (← q r"t = ideal_valuation (ring_of_integers k) p
            (ideal_generated (ring_of_integers k) {d:A})") THEN ABBREV_TAC (← q r"b = ideal_quotient (ring_of_integers k)
            (ideal_generated (ring_of_integers k) {d:A})
            (ideal_pow (ring_of_integers k) p t)") THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP PRIME_IMP_RING_IDEAL) o (checkM (fun th => (do let z33 ← (q r"prime_ideal (ring_of_integers k) (p:A->bool)"); let z32 ← (do let z31 ← (pure th); pure (concl z31)); pure (z32 == z33)))))) THEN SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers k) (b:A->bool) /\
      ideal_prod (ring_of_integers k) (ideal_pow (ring_of_integers k) p t) b =
      ideal_generated (ring_of_integers k) {d:A} /\
      ~(b SUBSET p)") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:A->bool"), (← q r"ideal_generated (ring_of_integers k) {d:A}")] DEDEKIND_IDEAL_SUBSET_POW_VALUATION) THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0, RING_OF_INTEGERS] THEN DISCH_TAC THEN MATCH_MP_TAC r30 THEN REPEAT CONJ_TAC THENL [EXPAND_TAC "b" THEN MATCH_MP_TAC RING_IDEAL_IDEAL_QUOTIENT THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN MESON_TAC [RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_POW], DISCH_TAC THEN EXPAND_TAC "b" THEN MATCH_MP_TAC DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_POW, LE_REFL], STRIP_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"SUC t"))) THEN REWRITE_TAC [r29] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z23 ← (do let z24 ← (pure th); pure (concl z24)); pure (is_eq z23)) then (do let z28 ← (q r"ideal_generated (ring_of_integers k) {d:A}"); let z27 ← (do let z25 ← (do let z26 ← (pure th); pure (concl z26)); liftExcept (rhs z25)); pure (z27 == z28)) else pure false))))) THEN REWRITE_TAC [IDEAL_POW_SUC] THEN wPart rand (lhand o rand) IDEAL_PROD_COMM THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_POW] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC IDEAL_PROD_MONO THEN ASM_REWRITE_TAC [SUBSET_REFL]], ALL_TAC] THEN UNDISCH_TAC (← q r"~((b:A->bool) SUBSET p)") THEN REWRITE_TAC [SUBSET, NOT_FORALL_THM, NOT_IMP] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"s:A") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(s:A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN EXISTS_TAC (← q r"s:A") THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPECL [(← q r"t:num"), (← q r"x:B")]) o (checkM (fun th => (do if ← (do let z14 ← (do let z15 ← (pure th); pure (concl z15)); pure (is_forall z14)) then (do let z16 ← (do let z17 ← (pure th); pure (concl z17)); canM (fun z18 => (do let z19 ← (pure z18); find_termM (fun z20 => (do let z22 ← (pure z20); let z21 ← (q r"ideal_pow (ring_of_integers k) (p:A->bool)"); pure (z21 == z22))) z19)) z16) else pure false))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"m:B") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"ring_mul l ((h:A->B) s) x IN M") MP_TAC THENL [ALL_TAC, EXPAND_TAC "M" THEN REWRITE_TAC [IN_ELIM_THM]] THEN SUBGOAL_THEN (← q r"(m:B) IN ring_carrier(ring_of_integers l) /\
      (h:A->B) s IN ring_carrier(ring_of_integers l)") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul l ((h:A->B) s) x =
      ring_add l (ring_mul l (h s) m) (ring_mul l (h s) (ring_sub l x m))") SUBST1_TAC THENL [MATCH_MP_TAC r13 THEN ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_generated (ring_of_integers l) {(h:A->B) d} =
      ideal_prod (ring_of_integers l)
        (ideal_generated (ring_of_integers l) (IMAGE h b))
        (ideal_generated (ring_of_integers l)
           (IMAGE h (ideal_pow (ring_of_integers k) p t)))") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring"), (← q r"h:A->B"), (← q r"b:A->bool"), (← q r"ideal_pow (ring_of_integers k) p t:A->bool")] IDEAL_PROD_HOMOMORPHIC_IMAGE) THEN ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN CONJ_TAC THEN MATCH_MP_TAC RING_IDEAL_IMP_SUBSET THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN FIRST_ASSUM ACCEPT_TAC, DISCH_THEN (SUBST1_TAC o SYM)] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"b:A->bool"), (← q r"ideal_pow (ring_of_integers k) p t:A->bool")] IDEAL_PROD_COMM) THEN ANTS_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC RING_IDEAL_IMP_SUBSET THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN FIRST_ASSUM ACCEPT_TAC, DISCH_THEN SUBST1_TAC] THEN FIRST_ASSUM (SUBST1_TAC o (checkM (fun th => (do if ← (do let z7 ← (do let z8 ← (pure th); pure (concl z8)); pure (is_eq z7)) then (do let z12 ← (q r"ideal_generated (ring_of_integers k) {d:A}"); let z11 ← (do let z9 ← (do let z10 ← (pure th); pure (concl z10)); liftExcept (rhs z9)); pure (z11 == z12)) else pure false)))) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring"), (← q r"h:A->B"), (← q r"{d:A}")] IDEAL_GENERATED_IMAGE_IDEAL_GENERATED) THEN ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN ASM_REWRITE_TAC [SING_SUBSET], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [IMAGE_CLAUSES], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul l ((h:A->B) s) (ring_sub l x m) IN
      ideal_generated (ring_of_integers l) {h d}") MP_TAC THENL [FIRST_ASSUM (SUBST1_TAC o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_eq z1)) then (do let z6 ← (q r"ideal_generated (ring_of_integers l) {(h:A->B) d}"); let z5 ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); liftExcept (lhs z3)); pure (z5 == z6)) else pure false)))) THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_MUL_IN_IDEAL_PROD)) THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_INC THEN CONJ_TAC THENL [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN MP_TAC (← MATCH_MP RING_IDEAL_IMP_SUBSET (← ASSUME (← q r"ring_ideal (ring_of_integers k) (b:A->bool)"))) THEN REWRITE_TAC [SUBSET] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"y:A"))) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC, MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC], FIRST_ASSUM ACCEPT_TAC, FIRST_ASSUM ACCEPT_TAC, MATCH_MP_TAC IN_SUBRING_SUB THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"(h:A->B) d IN ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"(h:A->B) d")] IDEAL_GENERATED_SING_ALT) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [IN_ELIM_THM, RING_OF_INTEGERS] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"y:B") STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC)

  -- @@RETURN BEGIN
  return { RING_OF_INTEGERS_BASIS_MOD_PRIME, RING_OF_INTEGERS_BASIS_MOD_PRIME_FREE,
           RING_OF_INTEGERS_LOCAL_BASIS }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- different_extension.ml phrases from line 693 to 1167                   -/
/- ---------------------------------------------------------------------- -/

structure DifferentExtension02 where
  -- @@FIELDS
  RING_OF_INTEGERS_QUOTIENT_TRACE : thm
  NUMBER_FIELD_TRACE_NILPOTENT : thm
  NUMBER_FIELD_TRACE_COMAXIMAL : thm
  NUMBER_FIELD_CODIFFERENT_TRACE_DIV : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDifferentExtension02 [HolBase] (D : DifferentExtensionDeps) (BDifferentExtension01 : DifferentExtension01) :
    ExceptT String IO DifferentExtension02 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_TAC, TAUT, .. } := D
  let { ALGEBRA_TRACE_FREE_BASIS_MATRIX, ALGEBRA_TRACE_NILPOTENT,
        ALGEBRA_TRACE_NORM_IN_CARRIER, ALGEBRA_TRACE_QUOTIENT_COMAXIMAL_NONZERO,
        ALGEBRA_TRACE_SCALAR, DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL,
        DEDEKIND_RING_OF_INTEGERS, EQ_TRANS, FIELD_HOMOMORPHISM_INV,
        FIELD_IMP_INTEGRAL_DOMAIN, FIELD_QUOTIENT_RING, FINITE_IMP_FIELD_EXTENSION,
        FINITE_NUMSEG_LT, FORALL_IN_GSPEC, IMP_CONJ, INTEGRAL_DOMAIN_MUL_LCANCEL,
        IN_ELIM_THM, IN_SUBRING_0, MAXIMAL_IMP_RING_IDEAL, MONO_EXISTS, .. } := D.core1
  let { NUMBER_FIELD_CODIFFERENT_DIV, NUMBER_FIELD_HOMOMORPHIC_PREIMAGE,
        NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_TOWER_LAW, NUMBER_FIELD_TRACE_INTEGRAL,
        QUOTIENT_RING_0, QUOTIENT_RING_CARRIER, QUOTIENT_RING_MUL,
        RESIDUE_DEGREE_QUOTIENT_RING, RIGHT_EXISTS_IMP_THM, RING_COSET_EQ,
        RING_COSET_EQ_IDEAL, RING_HOMOMORPHISM_IN_CARRIER, RING_HOMOMORPHISM_MUL,
        RING_HOMOMORPHISM_POW, RING_HOMOMORPHISM_RING_COSET,
        RING_HOMOMORPHISM_RING_OF_INTEGERS, RING_HOMOMORPHISM_SUM,
        RING_HOMOMORPHISM_SUM_MUL, RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IMP_SUBSET,
        RING_IDEAL_NUMBER_FIELD_DIFFERENT, RING_INV, RING_MONOMORPHISM_EQ_0,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL, RING_MUL_ASSOC, RING_NILPOTENT,
        RING_OF_INTEGERS, RING_OF_INTEGERS_FINITE_QUOTIENT,
        RING_OF_INTEGERS_IDEAL_EXTENSION_CONTRACTION_PRIME,
        RING_OF_INTEGERS_IN_IDEAL_GENERATED_SING, RING_OF_INTEGERS_SUBRING,
        RING_OF_INTEGERS_SUBSET, RING_POW, RING_SUM, RING_SUM_EQ,
        RING_SUM_RING_OF_INTEGERS, SKOLEM_THM, SUBSET, field_extension, free_basis,
        number_field_codifferent, o_DEF, .. } := D.core2
  let { RING_OF_INTEGERS_LOCAL_BASIS, .. } := BDifferentExtension01
  -- @@SCOPE END

  let RING_OF_INTEGERS_QUOTIENT_TRACE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r69 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!k:A ring l:B ring h p.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
          ==> ?g G.
                ring_homomorphism
                 (quotient_ring (ring_of_integers k) p,
                  quotient_ring (ring_of_integers l)
                    (ideal_generated (ring_of_integers l) (IMAGE h p))) g /\
                (!y. y IN ring_carrier(ring_of_integers k)
                     ==> g(ring_coset (ring_of_integers k) p y) =
                         ring_coset (ring_of_integers l)
                          (ideal_generated (ring_of_integers l) (IMAGE h p))
                          (h y)) /\
                free_basis
                 (quotient_ring (ring_of_integers k) p,
                  quotient_ring (ring_of_integers l)
                    (ideal_generated (ring_of_integers l) (IMAGE h p)))
                 g (extension_degree(k,l) h) G /\
                !x. x IN ring_carrier(ring_of_integers l)
                    ==> algebra_trace
                         (quotient_ring (ring_of_integers k) p,
                          quotient_ring (ring_of_integers l)
                            (ideal_generated (ring_of_integers l) (IMAGE h p)))
                         g
                         (ring_coset (ring_of_integers l)
                           (ideal_generated (ring_of_integers l) (IMAGE h p)) x) =
                        ring_coset (ring_of_integers k) p
                          (algebra_trace (k,l) h x)"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] RING_OF_INTEGERS_LOCAL_BASIS) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"n = extension_degree(k:A ring,l:B ring) h") THEN ABBREV_TAC (← q r"J = ideal_generated (ring_of_integers l) (IMAGE (h:A->B) p)") THEN DISCH_THEN (X_CHOOSE_THEN (← q r"w:num->B") (X_CHOOSE_THEN (← q r"s:A") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "span") (CONJUNCTS_THEN2 (LABEL_TAC "indep") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc"))))))))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] RING_OF_INTEGERS_IDEAL_EXTENSION_CONTRACTION_PRIME) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers l) (J:B->bool)") ASSUME_TAC THENL [EXPAND_TAC "J" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN SUBGOAL_THEN (← q r"maximal_ideal (ring_of_integers k) (p:A->bool)") ASSUME_TAC THENL [MATCH_MP_TAC DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_OF_INTEGERS], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_RING_IDEAL)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP (← REWRITE_RULE [IMP_CONJ] RING_HOMOMORPHISM_IN_CARRIER))) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring"), (← q r"h:A->B"), (← q r"J:B->bool")] RESIDUE_DEGREE_QUOTIENT_RING) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"g:(A->bool)->(B->bool)") STRIP_ASSUME_TAC) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN EXISTS_TAC (← q r"g:(A->bool)->(B->bool)") THEN EXISTS_TAC (← q r"\i. ring_coset (ring_of_integers l) J ((w:num->B) i)") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"field(quotient_ring (ring_of_integers k) (p:A->bool))") ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_QUOTIENT_RING], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. i < n ==> (w:num->B) i IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"!c. (!i. i < n ==> c i IN ring_carrier(ring_of_integers k))
          ==> ring_sum l {i | i < n}
                (\i. ring_mul l ((h:A->B)(c i)) ((w:num->B) i)) IN
              ring_carrier(ring_of_integers l) /\
              ring_coset (ring_of_integers l) J
                (ring_sum l {i | i < n} (\i. ring_mul l (h(c i)) (w i))) =
              ring_sum (quotient_ring (ring_of_integers l) J) {i | i < n}
                (\i. ring_mul (quotient_ring (ring_of_integers l) J)
                       (g(ring_coset (ring_of_integers k) p (c i)))
                       (ring_coset (ring_of_integers l) J (w i)))") (LABEL_TAC "cosum") THENL [X_GEN_TAC (← q r"c:num->A") THEN DISCH_TAC THEN MATCH_MP_TAC r69 THEN CONJ_TAC THENL [wPart lhand (rand o rand) RING_SUM_RING_OF_INTEGERS THEN ASM_SIMP_TAC [IN_ELIM_THM, (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_MUL))] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [RING_SUM], DISCH_TAC] THEN TRANS_TAC EQ_TRANS (← q r"ring_sum (quotient_ring (ring_of_integers l) J) {i | i < n}
          (\i. ring_mul (quotient_ring (ring_of_integers l) J)
                 (ring_coset (ring_of_integers l) J ((h:A->B)((c:num->A) i)))
                 (ring_coset (ring_of_integers l) J (w i)))") THEN CONJ_TAC THENL [ALL_TAC, MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC [IN_ELIM_THM]] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"quotient_ring (ring_of_integers l) (J:B->bool)"), (← q r"ring_coset (ring_of_integers l) (J:B->bool)"), (← q r"{i:num | i < n}"), (← q r"\i. (h:A->B)((c:num->A) i)"), (← q r"w:num->B")] RING_HOMOMORPHISM_SUM_MUL) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_COSET, FINITE_NUMSEG_LT, IN_ELIM_THM] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_RING_OF_INTEGERS THEN ASM_SIMP_TAC [IN_ELIM_THM, (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_MUL))], ALL_TAC] THEN SUBGOAL_THEN (← q r"free_basis
       (quotient_ring (ring_of_integers k) (p:A->bool),
        quotient_ring (ring_of_integers l) J) (g:(A->bool)->(B->bool)) n
       (\i. ring_coset (ring_of_integers l) J ((w:num->B) i))") ASSUME_TAC THENL [REWRITE_TAC [free_basis] THEN REPEAT CONJ_TAC THENL [ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, IN_ELIM_THM] THEN ASM_MESON_TAC [], ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, IMP_CONJ, FORALL_IN_GSPEC] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN USE_THEN "span" (MP_TAC o (← do let c := (← ASSUME (← q r"(x:B) IN ring_carrier(ring_of_integers l)")); pure (fun th => MATCH_MP th c))) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:num->A") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"\i. ring_coset (ring_of_integers k) p ((c:num->A) i)") THEN REWRITE_TAC [] THEN CONJ_TAC THENL [ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN USE_THEN "cosum" (MP_TAC o (SPEC (← q r"c:num->A"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"J:B->bool"), (← q r"x:B"), (← q r"ring_sum l {i | i < n}
                         (\i. ring_mul l ((h:A->B)(c i)) ((w:num->B) i))")] RING_COSET_EQ) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN FIRST_ASSUM ACCEPT_TAC, DISCH_THEN (SUBST1_TAC o (REWRITE_RULE [RING_OF_INTEGERS]))] THEN FIRST_ASSUM ACCEPT_TAC, X_GEN_TAC (← q r"a:num->A->bool") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"?c. !i. c i IN ring_carrier(ring_of_integers k) /\
                  (i < n ==> (a:num->A->bool) i =
                             ring_coset (ring_of_integers k) p (c i))") STRIP_ASSUME_TAC THENL [REWRITE_TAC [(← GSYM SKOLEM_THM)] THEN X_GEN_TAC (← q r"i:num") THEN ASM_CASES_TAC (← q r"i:num < n") THEN ASM_REWRITE_TAC [] THENL [FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"i:num")) o (checkM (fun th => (do if ← (do let z60 ← (do let z61 ← (pure th); pure (concl z61)); pure (is_forall z60)) then (do let z62 ← (do let z63 ← (pure th); pure (concl z63)); canM (fun z64 => (do let z65 ← (pure z64); find_termM (fun z66 => (do let z68 ← (pure z66); let z67 ← (q r"a:num->A->bool"); pure (z67 == z68))) z65)) z62) else pure false))))) THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, IN_ELIM_THM] THEN MESON_TAC [], MESON_TAC [IN_SUBRING_0, RING_OF_INTEGERS_SUBRING]], ALL_TAC] THEN USE_THEN "indep" (MP_TAC o (SPEC (← q r"c:num->A"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN USE_THEN "cosum" (MP_TAC o (SPEC (← q r"c:num->A"))) THEN ANTS_TAC THENL [ASM_MESON_TAC [], STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"J:B->bool"), (← q r"ring_sum l {i | i < n}
                           (\i. ring_mul l ((h:A->B)(c i)) ((w:num->B) i))")] RING_COSET_EQ_IDEAL) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN FIRST_ASSUM (SUBST1_TAC o (checkM (fun th => (do if ← (do let z54 ← (do let z55 ← (pure th); pure (concl z55)); pure (is_eq z54)) then (do let z57 ← (q r"ring_coset (ring_of_integers l) J             (ring_sum l {i | i < n}               (\i. ring_mul l ((h:A->B)(c i)) ((w:num->B) i)))"); let z56 ← (do let z58 ← (do let z59 ← (pure th); pure (concl z59)); liftExcept (lhs z58)); pure (aconv z56 z57)) else pure false)))) THEN TRANS_TAC EQ_TRANS (← q r"ring_0 (quotient_ring (ring_of_integers l) (J:B->bool))") THEN CONJ_TAC THENL [FIRST_ASSUM ((fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [(← SYM th)])) o (checkM (fun th => (do if ← (do let z48 ← (do let z49 ← (pure th); pure (concl z49)); pure (is_eq z48)) then (do let z53 ← (q r"ring_0 (quotient_ring (ring_of_integers l) (J:B->bool))"); let z52 ← (do let z50 ← (do let z51 ← (pure th); pure (concl z51)); liftExcept (rhs z50)); pure (z52 == z53)) else pure false)))) THEN MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC [IN_ELIM_THM], MATCH_MP_TAC QUOTIENT_RING_0 THEN FIRST_ASSUM ACCEPT_TAC], DISCH_TAC] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN ASM_SIMP_TAC [QUOTIENT_RING_0] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:A->bool"), (← q r"(c:num->A) i")] RING_COSET_EQ_IDEAL) THEN ASM_SIMP_TAC []], ASM_REWRITE_TAC []] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"?C:num->num->A. !j. j < n
              ==> (!i. C j i IN ring_carrier(ring_of_integers k)) /\
                  ring_mul l ((h:A->B) s) (ring_mul l x ((w:num->B) j)) =
                  ring_sum l {i | i < n} (\i. ring_mul l (h(C j i)) (w i))") STRIP_ASSUME_TAC THENL [REWRITE_TAC [(← GSYM SKOLEM_THM), RIGHT_EXISTS_IMP_THM] THEN X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN USE_THEN "loc" MATCH_MP_TAC THEN REWRITE_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_MUL))] THEN ASM_MESON_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_MUL))], ALL_TAC] THEN SUBGOAL_THEN (← q r"(s:A) IN ring_carrier k /\ (h:A->B) s IN ring_carrier l") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul k s (algebra_trace (k,l) (h:A->B) x) =
      ring_sum k {i | i < n} (\i. (C:num->num->A) i i)") ASSUME_TAC THENL [wPart lhand (rand o rand) ALGEBRA_TRACE_SCALAR THEN ASM_SIMP_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC ALGEBRA_TRACE_FREE_BASIS_MATRIX THEN EXISTS_TAC (← q r"w:num->B") THEN ASM_SIMP_TAC [RING_MUL] THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"j:num")) o (checkM (fun th => (do if ← (do let z39 ← (do let z40 ← (pure th); pure (concl z40)); pure (is_forall z39)) then (do let z41 ← (do let z42 ← (pure th); pure (concl z42)); canM (fun z43 => (do let z44 ← (pure z43); find_termM (fun z45 => (do let z47 ← (pure z45); let z46 ← (q r"C:num->num->A"); pure (z46 == z47))) z44)) z41) else pure false))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o (SYM o CONJUNCT2)) THEN MATCH_MP_TAC (← GSYM RING_MUL_ASSOC) THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"algebra_trace (k,l) (h:A->B) x IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [MATCH_MP_TAC NUMBER_FIELD_TRACE_INTEGRAL THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. i < n ==> (C:num->num->A) i i IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"algebra_trace
       (quotient_ring (ring_of_integers k) p,
        quotient_ring (ring_of_integers l) J) (g:(A->bool)->(B->bool))
       (ring_coset (ring_of_integers l) J (ring_mul l ((h:A->B) s) x)) =
      ring_coset (ring_of_integers k) p
       (ring_mul k s (algebra_trace (k,l) h x))") MP_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (checkM (fun th => (do if ← (do let z33 ← (do let z34 ← (pure th); pure (concl z34)); pure (is_eq z33)) then (do let z38 ← (q r"ring_mul k s (algebra_trace (k,l) (h:A->B) x)"); let z37 ← (do let z35 ← (do let z36 ← (pure th); pure (concl z36)); liftExcept (lhs z35)); pure (z37 == z38)) else pure false)))) THEN MP_TAC (← ISPECL [(← q r"g:(A->bool)->(B->bool)"), (← q r"quotient_ring (ring_of_integers k) (p:A->bool)"), (← q r"quotient_ring (ring_of_integers l) (J:B->bool)"), (← q r"n:num"), (← q r"\i. ring_coset (ring_of_integers l) J ((w:num->B) i)"), (← q r"\j i. ring_coset (ring_of_integers k) p ((C:num->num->A) j i)"), (← q r"ring_coset (ring_of_integers l) J (ring_mul l ((h:A->B) s) x)")] ALGEBRA_TRACE_FREE_BASIS_MATRIX) THEN REWRITE_TAC [] THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, IN_ELIM_THM] THEN EXISTS_TAC (← q r"ring_mul l ((h:A->B) s) x") THEN REWRITE_TAC [] THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_MUL)) THEN ASM_SIMP_TAC [], ALL_TAC] THEN CONJ_TAC THENL [ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"j:num")) o (checkM (fun th => (do if ← (do if ← (do let z17 ← (do let z18 ← (pure th); pure (concl z18)); pure (is_forall z17)) then (do let z19 ← (do let z20 ← (pure th); pure (concl z20)); canM (fun z21 => (do let z22 ← (pure z21); find_termM (fun z23 => (do let z25 ← (pure z23); let z24 ← (q r"C:num->num->A"); pure (z24 == z25))) z22)) z19) else pure false) then (do let z26 ← (do let z27 ← (pure th); pure (concl z27)); canM (fun z28 => (do let z29 ← (pure z28); find_termM (fun z30 => (do let z32 ← (pure z30); let z31 ← (q r"ring_mul l ((h:A->B) s)"); pure (z31 == z32))) z29)) z26) else pure false))))) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN USE_THEN "cosum" (MP_TAC o (SPEC (← q r"(C:num->num->A) j"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (SUBST1_TAC o (SYM o CONJUNCT2))] THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN SUBGOAL_THEN (← q r"ring_mul l x ((w:num->B) j) IN
                      ring_carrier(ring_of_integers l) /\
                      ring_mul l ((h:A->B) s) x IN
                      ring_carrier(ring_of_integers l)") STRIP_ASSUME_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_MUL)) THEN ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"J:B->bool"), (← q r"ring_mul l ((h:A->B) s) x"), (← q r"(w:num->B) j")] QUOTIENT_RING_MUL) THEN ASM_SIMP_TAC [RING_OF_INTEGERS] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN AP_TERM_TAC THEN MATCH_MP_TAC (← GSYM RING_MUL_ASSOC) THEN ASM_SIMP_TAC [], DISCH_THEN SUBST1_TAC] THEN MP_TAC (← ISPECL [(← q r"\i. (C:num->num->A) i i"), (← q r"{i:num | i < n}")] (← MATCH_MP RING_HOMOMORPHISM_SUM (← MATCH_MP RING_HOMOMORPHISM_RING_COSET (← ASSUME (← q r"ring_ideal (ring_of_integers k) (p:A->bool)"))))) THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, o_DEF] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN MATCH_MP_TAC RING_SUM_RING_OF_INTEGERS THEN ASM_SIMP_TAC [IN_ELIM_THM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"J:B->bool"), (← q r"(h:A->B) s"), (← q r"x:B")] QUOTIENT_RING_MUL) THEN ASM_SIMP_TAC [RING_OF_INTEGERS] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN FIRST_ASSUM ((fun th => tactic_of do pure (REWRITE_TAC [(← GSYM (← MATCH_MP th (← ASSUME (← q r"(s:A) IN ring_carrier(ring_of_integers k)"))))])) o (checkM (fun th => (do if ← (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_forall z1)) then (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); canM (fun z5 => (do let z6 ← (pure z5); find_termM (fun z7 => (do let z9 ← (pure z7); let z8 ← (q r"g:(A->bool)->(B->bool)"); pure (z8 == z9))) z6)) z3) else pure false) then (do let z10 ← (do let z11 ← (pure th); pure (concl z11)); canM (fun z12 => (do let z13 ← (pure z12); find_termM (fun z14 => (do let z16 ← (pure z14); let z15 ← (q r"ring_coset (ring_of_integers k) (p:A->bool)"); pure (z15 == z16))) z13)) z10) else pure false)))) THEN SUBGOAL_THEN (← q r"ring_coset (ring_of_integers k) p (s:A) IN
      ring_carrier(quotient_ring (ring_of_integers k) p) /\
      ring_coset (ring_of_integers l) J (x:B) IN
      ring_carrier(quotient_ring (ring_of_integers l) J) /\
      ring_coset (ring_of_integers k) p (algebra_trace (k,l) (h:A->B) x) IN
      ring_carrier(quotient_ring (ring_of_integers k) p)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN wPart (lhand o lhand) (lhand o rand) ALGEBRA_TRACE_SCALAR THEN ASM_SIMP_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:A->bool"), (← q r"s:A"), (← q r"algebra_trace (k,l) (h:A->B) x")] QUOTIENT_RING_MUL) THEN ASM_SIMP_TAC [RING_OF_INTEGERS] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN DISCH_TAC THEN MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN MAP_EVERY EXISTS_TAC [(← q r"quotient_ring (ring_of_integers k) (p:A->bool)"), (← q r"ring_coset (ring_of_integers k) p (s:A)")] THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, ALGEBRA_TRACE_NORM_IN_CARRIER, QUOTIENT_RING_0] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:A->bool"), (← q r"s:A")] RING_COSET_EQ_IDEAL) THEN ASM_SIMP_TAC [])

  let NUMBER_FIELD_TRACE_NILPOTENT ← prove
    r"!k:A ring l:B ring h p x m.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        x IN ring_carrier(ring_of_integers l) /\
        ring_pow l x m IN ideal_generated (ring_of_integers l) (IMAGE h p)
        ==> algebra_trace (k,l) h x IN p"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] RING_OF_INTEGERS_QUOTIENT_TRACE) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"J = ideal_generated (ring_of_integers l) (IMAGE (h:A->B) p)") THEN DISCH_THEN (X_CHOOSE_THEN (← q r"g:(A->bool)->(B->bool)") (X_CHOOSE_THEN (← q r"G:num->(B->bool)") STRIP_ASSUME_TAC)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers l) (J:B->bool)") ASSUME_TAC THENL [EXPAND_TAC "J" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"maximal_ideal (ring_of_integers k) (p:A->bool)") ASSUME_TAC THENL [MATCH_MP_TAC DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_OF_INTEGERS], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"algebra_trace (k,l) (h:A->B) x IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [MATCH_MP_TAC NUMBER_FIELD_TRACE_INTEGRAL THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:A->bool"), (← q r"algebra_trace (k,l) (h:A->B) x")] RING_COSET_EQ_IDEAL) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o ((← do let c := (← ASSUME (← q r"(x:B) IN ring_carrier(ring_of_integers l)")); pure (fun th => MATCH_MP th c)) o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_forall z1)) then (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); canM (fun z5 => (do let z6 ← (pure z5); find_termM (fun z7 => (do let z9 ← (pure z7); let z8 ← (q r"algebra_trace:(A->bool)ring#(B->bool)ring->                             ((A->bool)->(B->bool))->(B->bool)->A->bool"); pure (z8 == z9))) z6)) z3) else pure false)))))) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:A->bool")] QUOTIENT_RING_0) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [(← SYM th)]))] THEN MATCH_MP_TAC ALGEBRA_TRACE_NILPOTENT THEN MAP_EVERY EXISTS_TAC [(← q r"extension_degree(k:A ring,l:B ring) h"), (← q r"G:num->(B->bool)")] THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, FIELD_QUOTIENT_RING] THEN REWRITE_TAC [RING_NILPOTENT] THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, IN_ELIM_THM] THEN CONJ_TAC THENL [ASM_MESON_TAC [], EXISTS_TAC (← q r"m:num")] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"quotient_ring (ring_of_integers l) (J:B->bool)"), (← q r"ring_coset (ring_of_integers l) (J:B->bool)")] RING_HOMOMORPHISM_POW) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_COSET] THEN DISCH_THEN (MP_TAC o (SPECL [(← q r"x:B"), (← q r"m:num")])) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"J:B->bool")] QUOTIENT_RING_0) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"J:B->bool"), (← q r"ring_pow l (x:B) m")] RING_COSET_EQ_IDEAL) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_POW)) THEN ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC []])

  let NUMBER_FIELD_TRACE_COMAXIMAL ← prove
    r"!k:A ring l:B ring h p P Q.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        maximal_ideal (ring_of_integers l) P /\
        ring_ideal (ring_of_integers l) Q /\
        ring_setadd (ring_of_integers l) P Q =
        ring_carrier(ring_of_integers l) /\
        P INTER Q = ideal_generated (ring_of_integers l) (IMAGE h p)
        ==> ?x. x IN Q /\ ~(algebra_trace (k,l) h x IN p)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] RING_OF_INTEGERS_QUOTIENT_TRACE) THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z17 ← (do let z18 ← (pure th); pure (concl z18)); pure (is_eq z17)) then (do let z22 ← (q r"(P:B->bool) INTER Q"); let z21 ← (do let z19 ← (do let z20 ← (pure th); pure (concl z20)); liftExcept (lhs z19)); pure (z21 == z22)) else pure false))))) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"g:(A->bool)->(B->bool)") (X_CHOOSE_THEN (← q r"G:num->(B->bool)") STRIP_ASSUME_TAC)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN SUBGOAL_THEN (← q r"maximal_ideal (ring_of_integers k) (p:A->bool)") ASSUME_TAC THENL [MATCH_MP_TAC DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_OF_INTEGERS], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_RING_IDEAL)) THEN MP_TAC (← ISPECL [(← q r"quotient_ring (ring_of_integers k) (p:A->bool)"), (← q r"ring_of_integers l:B ring"), (← q r"g:(A->bool)->(B->bool)"), (← q r"extension_degree(k:A ring,l:B ring) h"), (← q r"G:num->(B->bool)"), (← q r"P:B->bool"), (← q r"Q:B->bool")] ALGEBRA_TRACE_QUOTIENT_COMAXIMAL_NONZERO) THEN ASM_SIMP_TAC [FIELD_QUOTIENT_RING, RING_OF_INTEGERS_FINITE_QUOTIENT, NUMBER_FIELD_IMP_FIELD] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"x:B") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"algebra_trace (k,l) (h:A->B) x IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [MATCH_MP_TAC NUMBER_FIELD_TRACE_INTEGRAL THEN ASM_REWRITE_TAC [], ALL_TAC] THEN UNDISCH_TAC (← q r"~(algebra_trace
       (quotient_ring (ring_of_integers k) p,
        quotient_ring (ring_of_integers l) ((P:B->bool) INTER Q))
       (g:(A->bool)->(B->bool))
       (ring_coset (ring_of_integers l) (P INTER Q) x) =
      ring_0 (quotient_ring (ring_of_integers k) (p:A->bool)))") THEN FIRST_ASSUM (SUBST1_TAC o ((← do let c := (← ASSUME (← q r"(x:B) IN ring_carrier(ring_of_integers l)")); pure (fun th => MATCH_MP th c)) o (checkM (fun th => (do if ← (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_forall z1)) then (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); canM (fun z5 => (do let z6 ← (pure z5); find_termM (fun z7 => (do let z9 ← (pure z7); let z8 ← (q r"ring_coset (ring_of_integers k) (p:A->bool)"); pure (z8 == z9))) z6)) z3) else pure false) then (do let z10 ← (do let z11 ← (pure th); pure (concl z11)); canM (fun z12 => (do let z13 ← (pure z12); find_termM (fun z14 => (do let z16 ← (pure z14); let z15 ← (q r"algebra_trace (k:A ring,l:B ring) h"); pure (z15 == z16))) z13)) z10) else pure false))))) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:A->bool")] QUOTIENT_RING_0) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:A->bool"), (← q r"algebra_trace (k,l) (h:A->B) x")] RING_COSET_EQ_IDEAL) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [])

  let NUMBER_FIELD_CODIFFERENT_TRACE_DIV ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"(p ==> (q <=> r)) ==> (p ==> q <=> p ==> r)")
    prove
      r"!k:A ring l:B ring h c y x.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          c IN ring_carrier(ring_of_integers k) /\ ~(c = ring_0 k) /\
          y IN ring_carrier(ring_of_integers k) /\
          x IN ring_carrier(ring_of_integers l)
          ==> ((!z. z IN ring_carrier(ring_of_integers l)
                    ==> ring_mul k y (algebra_trace (k,l) h (ring_mul l x z)) IN
                        ideal_generated (ring_of_integers k) {c}) <=>
               (!d. d IN number_field_different (k,l) h
                    ==> ring_mul l (h y) (ring_mul l x d) IN
                        ideal_generated (ring_of_integers l) {h c}))"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP NUMBER_FIELD_IMP_FIELD) o (checkM (fun th => (do let z4 ← (q r"number_field(l:B ring)"); let z3 ← (do let z2 ← (pure th); pure (concl z2)); pure (z3 == z4)))))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (MP_TAC o ((MATCH_MP FINITE_IMP_FIELD_EXTENSION) o CONJUNCT1)) THEN REWRITE_TAC [field_extension] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN SUBGOAL_THEN (← q r"(c:A) IN ring_carrier k /\ (y:A) IN ring_carrier k /\
      (x:B) IN ring_carrier l /\
      (h:A->B) c IN ring_carrier(ring_of_integers l) /\
      h c IN ring_carrier l /\ ~(h c = ring_0 l) /\ h y IN ring_carrier l") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET, RING_MONOMORPHISM_EQ_0, RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"(h:A->B) c"), (← q r"ring_mul l ((h:A->B) y) x")] NUMBER_FIELD_CODIFFERENT_DIV) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_MUL], ALL_TAC] THEN SUBGOAL_THEN (← q r"!d. d IN number_field_different (k,l) (h:A->B) ==> d IN ring_carrier l") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_IDEAL_NUMBER_FIELD_DIFFERENT) THEN DISCH_THEN (MP_TAC o (MATCH_MP RING_IDEAL_IMP_SUBSET)) THEN MP_TAC (← ISPEC (← q r"l:B ring") RING_OF_INTEGERS_SUBSET) THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!d. d IN number_field_different (k,l) (h:A->B)
          ==> ring_mul l (ring_mul l (h y) x) d =
              ring_mul l (h y) (ring_mul l x d)") (fun th => SIMP_TAC [th]) THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC (← GSYM RING_MUL_ASSOC) THEN ASM_SIMP_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN REWRITE_TAC [number_field_codifferent, IN_ELIM_THM] THEN SUBGOAL_THEN (← q r"ring_mul k (ring_inv k c) (y:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_MUL, RING_INV], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul l (ring_inv l ((h:A->B) c)) (ring_mul l (h y) x) =
      ring_mul l (h(ring_mul k (ring_inv k c) y)) x") SUBST1_TAC THENL [ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL (← ASSUME (← q r"ring_homomorphism(k:A ring,l:B ring) h"))), RING_INV] THEN ASM_SIMP_TAC [(← MATCH_MP FIELD_HOMOMORPHISM_INV (← CONJ (← ASSUME (← q r"field(k:A ring)")) (← ASSUME (← q r"ring_homomorphism(k:A ring,l:B ring) h"))))] THEN MATCH_MP_TAC RING_MUL_ASSOC THEN ASM_SIMP_TAC [RING_INV], ALL_TAC] THEN SUBGOAL_THEN (← q r"(h:A->B)(ring_mul k (ring_inv k c) y) IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN ASM_SIMP_TAC [RING_MUL] THEN AP_TERM_TAC THEN ABS_TAC THEN MATCH_MP_TAC r1 THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(z:B) IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul l (ring_mul l ((h:A->B) (ring_mul k (ring_inv k c) y)) x) z =
      ring_mul l (h (ring_mul k (ring_inv k c) y)) (ring_mul l x z)") SUBST1_TAC THENL [MATCH_MP_TAC (← GSYM RING_MUL_ASSOC) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [ALGEBRA_TRACE_SCALAR, RING_MUL] THEN SUBGOAL_THEN (← q r"algebra_trace (k,l) (h:A->B) (ring_mul l x z) IN ring_carrier k") ASSUME_TAC THENL [REWRITE_TAC [ALGEBRA_TRACE_NORM_IN_CARRIER], ALL_TAC] THEN ASM_SIMP_TAC [RING_OF_INTEGERS_IN_IDEAL_GENERATED_SING, RING_MUL, RING_MUL_ASSOC, RING_INV])

  -- @@RETURN BEGIN
  return { RING_OF_INTEGERS_QUOTIENT_TRACE, NUMBER_FIELD_TRACE_NILPOTENT,
           NUMBER_FIELD_TRACE_COMAXIMAL, NUMBER_FIELD_CODIFFERENT_TRACE_DIV }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- different_extension.ml phrases from line 1257 to 1736                  -/
/- ---------------------------------------------------------------------- -/

structure DifferentExtension03 where
  -- @@FIELDS
  NUMBER_FIELD_DIFFERENT_TRACE : thm
  NUMBER_FIELD_DIFFERENT_SUBSET_RAMIFICATION : thm
  NUMBER_FIELD_DIFFERENT_RAMIFIED : thm
  RING_OF_INTEGERS_IDEAL_DOUBLE_DUAL : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDifferentExtension03 [HolBase] (D : DifferentExtensionDeps) (BDifferentExtension02 : DifferentExtension02) :
    ExceptT String IO DifferentExtension03 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, RING_RULE, SET_RULE,
        SET_TAC, TAUT, num_CONV, .. } := D
  let { DEDEKIND_IDEAL_MEMBER_PRINCIPAL_MULTIPLE, DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT,
        DEDEKIND_IDEAL_PROD_SUBSET_CANCEL, DEDEKIND_IDEAL_SUBSET_POW_VALUATION,
        DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL, DEDEKIND_RING_OF_INTEGERS,
        EXISTS_UNIQUE_THM, EXTENSION, FORALL_IN_IMAGE,
        IDEAL_GENERATED_IMAGE_IDEAL_GENERATED, IDEAL_GENERATED_MINIMAL,
        IDEAL_GENERATED_RING_IDEAL, IDEAL_GENERATED_SING_ALT, IDEAL_POW_0, IDEAL_POW_1,
        IDEAL_POW_ANTIMONO, IDEAL_POW_MONO, IDEAL_POW_PRINCIPAL, IDEAL_POW_SUC,
        IDEAL_PROD_CARRIER, IDEAL_PROD_COMAXIMAL, IDEAL_PROD_COMM, IDEAL_PROD_EQ_ZERO,
        IDEAL_PROD_HOMOMORPHIC_IMAGE, IDEAL_PROD_MINIMAL, IDEAL_PROD_MONO,
        IDEAL_PROD_RZERO, IMAGE_CLAUSES, INTEGRAL_DOMAIN_RING_OF_INTEGERS, IN_ELIM_THM,
        IN_IDEAL_GENERATED_SELF, IN_RING_IDEAL_0, IN_RING_IDEAL_RMUL, IN_SING,
        IN_SUBRING_1, IN_SUBRING_POW, LE_REFL, MAXIMAL_IDEAL_COMAXIMAL, NOT_LE, .. } := D.core1
  let { NUMBER_FIELD_HOMOMORPHIC_PREIMAGE, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS, NUMBER_FIELD_TRACE_INTEGRAL,
        PRIME_IMP_RING_IDEAL, RING_HOMOMORPHISM_IN_CARRIER,
        RING_HOMOMORPHISM_RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED,
        RING_IDEAL_IDEAL_POW, RING_IDEAL_IDEAL_QUOTIENT, RING_IDEAL_IMP_NONEMPTY,
        RING_IDEAL_IMP_SUBSET, RING_IDEAL_NUMBER_FIELD_DIFFERENT, RING_INV, RING_MUL,
        RING_MUL_IN_IDEAL_PROD, RING_MUL_RID, RING_MUL_SYM, RING_OF_INTEGERS,
        RING_OF_INTEGERS_IDEAL_EXTENSION, RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME,
        RING_OF_INTEGERS_IN_IDEAL_GENERATED_SING, RING_OF_INTEGERS_PRIME_IDEAL_BELOW,
        RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION, RING_OF_INTEGERS_SUBRING,
        RING_OF_INTEGERS_SUBSET, SING_SUBSET, SUBSET, SUBSET_REFL, SUBSET_TRANS,
        ideal_quotient, ramification_index, .. } := D.core2
  let { NUMBER_FIELD_CODIFFERENT_TRACE_DIV, NUMBER_FIELD_TRACE_COMAXIMAL,
        NUMBER_FIELD_TRACE_NILPOTENT, .. } := BDifferentExtension02
  -- @@SCOPE END

  let NUMBER_FIELD_DIFFERENT_TRACE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"a /\ (b ==> c) ==> (a <=> b) ==> c")
    let r2 ← TAUT (← q r"b /\ (a ==> c) ==> (a <=> b) ==> c")
    let r3 ← TAUT (← q r"p /\ q /\ (p /\ q ==> r) ==> p /\ q /\ r")
    prove
      r"!k:A ring l:B ring h p x.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
          x IN ring_carrier(ring_of_integers l)
          ==> ((!d. d IN number_field_different (k,l) h
                    ==> ring_mul l x d IN
                        ideal_generated (ring_of_integers l) (IMAGE h p)) <=>
               (!y. y IN ring_carrier(ring_of_integers l)
                    ==> algebra_trace (k,l) h (ring_mul l x y) IN p))"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP PRIME_IMP_RING_IDEAL) o (checkM (fun th => (do let z6 ← (q r"prime_ideal (ring_of_integers k) (p:A->bool)"); let z5 ← (do let z4 ← (pure th); pure (concl z4)); pure (z5 == z6)))))) THEN SUBGOAL_THEN (← q r"?c:A. c IN p /\ ~(c = ring_0 k)") STRIP_ASSUME_TAC THENL [MP_TAC (← MATCH_MP RING_IDEAL_IMP_NONEMPTY (← ASSUME (← q r"ring_ideal (ring_of_integers k) (p:A->bool)"))) THEN UNDISCH_TAC (← q r"~(p = {ring_0 k:A})") THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:A->bool")] IN_RING_IDEAL_0) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(c:A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN ABBREV_TAC (← q r"b = ideal_quotient (ring_of_integers k)
            (ideal_generated (ring_of_integers k) {c:A}) p") THEN SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers k) (b:A->bool) /\
      ideal_prod (ring_of_integers k) p b =
      ideal_generated (ring_of_integers k) {c:A} /\
      ~(b = {ring_0 k})") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r3 THEN REPEAT CONJ_TAC THENL [EXPAND_TAC "b" THEN MATCH_MP_TAC RING_IDEAL_IDEAL_QUOTIENT THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IMP_SUBSET], EXPAND_TAC "b" THEN MATCH_MP_TAC DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED] THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET], STRIP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"ideal_prod (ring_of_integers k) p {ring_0 k} =
          ideal_generated (ring_of_integers k) {c:A}") THEN ASM_SIMP_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") IDEAL_PROD_RZERO)), RING_IDEAL_IMP_SUBSET] THEN DISCH_THEN (MP_TAC o (AP_TERM (← q r"\s:A->bool. (c:A) IN s"))) THEN ASM_REWRITE_TAC [IN_SING, IN_IDEAL_GENERATED_SELF]], ALL_TAC] THEN ABBREV_TAC (← q r"J = ideal_generated (ring_of_integers l) (IMAGE (h:A->B) p)") THEN SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers l) (J:B->bool) /\
      IMAGE (h:A->B) b SUBSET ring_carrier(ring_of_integers l) /\
      ~(ideal_generated (ring_of_integers l) (IMAGE h b) = {ring_0 l}) /\
      h c IN ring_carrier(ring_of_integers l) /\
      ideal_prod (ring_of_integers l) J
        (ideal_generated (ring_of_integers l) (IMAGE h b)) =
      ideal_generated (ring_of_integers l) {h c}") STRIP_ASSUME_TAC THENL [EXPAND_TAC "J" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN REPEAT CONJ_TAC THENL [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, RING_IDEAL_IMP_SUBSET, SUBSET], MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"b:A->bool")] RING_OF_INTEGERS_IDEAL_EXTENSION) THEN ASM_REWRITE_TAC [] THEN SIMP_TAC [], ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"b:A->bool")] IDEAL_PROD_HOMOMORPHIC_IMAGE) THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring"), (← q r"h:A->B"), (← q r"{c:A}")] IDEAL_GENERATED_IMAGE_IDEAL_GENERATED) THEN ASM_REWRITE_TAC [SING_SUBSET, IMAGE_CLAUSES], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:A->bool"), (← q r"b:A->bool"), (← q r"c:A")] DEDEKIND_IDEAL_MEMBER_PRINCIPAL_MULTIPLE) THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_IDEAL_IMP_SUBSET, IDEAL_GENERATED_RING_IDEAL, RING_OF_INTEGERS] THEN DISCH_THEN (LABEL_TAC "a") THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"J:B->bool"), (← q r"IMAGE (h:A->B) b"), (← q r"(h:A->B) c")] DEDEKIND_IDEAL_MEMBER_PRINCIPAL_MULTIPLE) THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_OF_INTEGERS] THEN REWRITE_TAC [FORALL_IN_IMAGE] THEN DISCH_THEN (LABEL_TAC "b") THEN SUBGOAL_THEN (← q r"!y:A. y IN b
            ==> ((!z. z IN ring_carrier(ring_of_integers l)
                      ==> ring_mul k y (algebra_trace (k,l) h (ring_mul l x z))
                          IN ideal_generated (ring_of_integers k) {c}) <=>
                 (!d. d IN number_field_different (k,l) h
                      ==> ring_mul l ((h:A->B) y) (ring_mul l x d) IN
                          ideal_generated (ring_of_integers l) {h c}))") (LABEL_TAC "c") THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC NUMBER_FIELD_CODIFFERENT_TRACE_DIV THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"!d. d IN number_field_different (k,l) (h:A->B)
          ==> ring_mul l (x:B) d IN ring_carrier(ring_of_integers l)") (LABEL_TAC "xd") THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_MUL)) THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_IDEAL_NUMBER_FIELD_DIFFERENT) THEN DISCH_THEN (MP_TAC o (MATCH_MP RING_IDEAL_IMP_SUBSET)) THEN ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!z. z IN ring_carrier(ring_of_integers l)
          ==> algebra_trace (k,l) (h:A->B) (ring_mul l (x:B) z) IN
              ring_carrier(ring_of_integers k)") (LABEL_TAC "tr") THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC NUMBER_FIELD_TRACE_INTEGRAL THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_MUL)) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN EQ_TAC THEN DISCH_TAC THENL [X_GEN_TAC (← q r"z:B") THEN DISCH_TAC THEN USE_THEN "tr" (MP_TAC o (← do let c := (← ASSUME (← q r"(z:B) IN ring_carrier(ring_of_integers l)")); pure (fun th => MATCH_MP th c))) THEN DISCH_THEN (fun th => tactic_of do pure (USE_THEN "a" (SUBST1_TAC o (← do let c := th; pure (fun th => MATCH_MP th c))))) THEN X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN USE_THEN "c" (MP_TAC o (← do let c := (← ASSUME (← q r"(y:A) IN b")); pure (fun th => MATCH_MP th c))) THEN MATCH_MP_TAC r2 THEN CONJ_TAC THENL [X_GEN_TAC (← q r"d:B") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (← do let c := (← ASSUME (← q r"(d:B) IN number_field_different (k,l) (h:A->B)")); pure (fun th => MATCH_MP th c))) THEN USE_THEN "xd" (MP_TAC o (← do let c := (← ASSUME (← q r"(d:B) IN number_field_different (k,l) (h:A->B)")); pure (fun th => MATCH_MP th c))) THEN DISCH_THEN (fun th => tactic_of do pure (USE_THEN "b" (SUBST1_TAC o (← do let c := th; pure (fun th => MATCH_MP th c))))) THEN DISCH_THEN (ACCEPT_TAC o (← do let c := (← ASSUME (← q r"(y:A) IN b")); pure (fun th => MATCH_MP th c))), DISCH_THEN (ACCEPT_TAC o (← do let c := (← ASSUME (← q r"(z:B) IN ring_carrier(ring_of_integers l)")); pure (fun th => MATCH_MP th c)))], X_GEN_TAC (← q r"d:B") THEN DISCH_TAC THEN USE_THEN "xd" (MP_TAC o (← do let c := (← ASSUME (← q r"(d:B) IN number_field_different (k,l) (h:A->B)")); pure (fun th => MATCH_MP th c))) THEN DISCH_THEN (fun th => tactic_of do pure (USE_THEN "b" (SUBST1_TAC o (← do let c := th; pure (fun th => MATCH_MP th c))))) THEN X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN USE_THEN "c" (MP_TAC o (← do let c := (← ASSUME (← q r"(y:A) IN b")); pure (fun th => MATCH_MP th c))) THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [X_GEN_TAC (← q r"z:B") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (← do let c := (← ASSUME (← q r"(z:B) IN ring_carrier(ring_of_integers l)")); pure (fun th => MATCH_MP th c))) THEN USE_THEN "tr" (MP_TAC o (← do let c := (← ASSUME (← q r"(z:B) IN ring_carrier(ring_of_integers l)")); pure (fun th => MATCH_MP th c))) THEN DISCH_THEN (fun th => tactic_of do pure (USE_THEN "a" (SUBST1_TAC o (← do let c := th; pure (fun th => MATCH_MP th c))))) THEN DISCH_THEN (ACCEPT_TAC o (← do let c := (← ASSUME (← q r"(y:A) IN b")); pure (fun th => MATCH_MP th c))), DISCH_THEN (ACCEPT_TAC o (← do let c := (← ASSUME (← q r"(d:B) IN number_field_different (k,l) (h:A->B)")); pure (fun th => MATCH_MP th c)))]])

  let NUMBER_FIELD_DIFFERENT_SUBSET_RAMIFICATION ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r10 ← TAUT (← q r"q /\ (p ==> r) ==> (p <=> q) ==> r")
    let r11 ← SET_RULE (← q r"(s:B->bool) = t ==> s SUBSET t")
    let r12 ← ARITH_RULE (← q r"1 <= e ==> SUC(e - 1) = e")
    let r13 ← SET_RULE (← q r"!x:B s t. x IN s /\ s SUBSET t ==> x IN t")
    let r14 ← ARITH_RULE (← q r"1 <= e ==> SUC(e - 1) = e")
    prove
      r"!k:A ring l:B ring h P.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          prime_ideal (ring_of_integers l) P /\ ~(P = {ring_0 l})
          ==> number_field_different (k,l) h SUBSET
              ideal_pow (ring_of_integers l) P
                (ramification_index (ring_of_integers k,ring_of_integers l) h P
                 - 1)"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"P:B->bool")] RING_OF_INTEGERS_PRIME_IDEAL_BELOW) THEN ASM_REWRITE_TAC [EXISTS_UNIQUE_THM] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"p:A->bool") STRIP_ASSUME_TAC) o CONJUNCT1) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"P:B->bool")] RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"P:B->bool")] NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"q = ideal_generated (ring_of_integers l) (IMAGE (h:A->B) p)") THEN STRIP_TAC THEN STRIP_TAC THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ideal_valuation (ring_of_integers l) P (q:B->bool) =
      ramification_index (ring_of_integers k,ring_of_integers l) (h:A->B) P") ASSUME_TAC THENL [ASM_REWRITE_TAC [ramification_index], ALL_TAC] THEN ABBREV_TAC (← q r"e = ramification_index (ring_of_integers k,ring_of_integers l)
            (h:A->B) P") THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP NUMBER_FIELD_IMP_FIELD) o (checkM (fun th => (do let z26 ← (q r"number_field(l:B ring)"); let z25 ← (do let z24 ← (pure th); pure (concl z24)); pure (z25 == z26)))))) THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP DEDEKIND_RING_OF_INTEGERS) o (checkM (fun th => (do let z23 ← (q r"number_field(l:B ring)"); let z22 ← (do let z21 ← (pure th); pure (concl z21)); pure (z22 == z23)))))) THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP INTEGRAL_DOMAIN_RING_OF_INTEGERS) o (checkM (fun th => (do let z20 ← (q r"field(l:B ring)"); let z19 ← (do let z18 ← (pure th); pure (concl z18)); pure (z19 == z20)))))) THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP PRIME_IMP_RING_IDEAL) o (checkM (fun th => (do let z17 ← (q r"prime_ideal (ring_of_integers l) (P:B->bool)"); let z16 ← (do let z15 ← (pure th); pure (concl z15)); pure (z16 == z17)))))) THEN SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers l) (q:B->bool)") ASSUME_TAC THENL [EXPAND_TAC "q" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"!m. q SUBSET ideal_pow (ring_of_integers (l:B ring)) P m <=> m <= e") ASSUME_TAC THENL [ASM_SIMP_TAC [DEDEKIND_IDEAL_SUBSET_POW_VALUATION, RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"?a. ring_ideal (ring_of_integers l) a /\
          ideal_prod (ring_of_integers l)
            (ideal_pow (ring_of_integers l) P (e - 1)) a = (q:B->bool)") (X_CHOOSE_THEN (← q r"a:B->bool") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "aq"))) THENL [EXISTS_TAC (← q r"ideal_quotient (ring_of_integers l) q
                    (ideal_pow (ring_of_integers l) P (e - 1)):B->bool") THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_QUOTIENT, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_POW] THEN MATCH_MP_TAC DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"~(ideal_pow (ring_of_integers l) P (e - 1) = {ring_0 (l:B ring)}) /\
      ~(a = {ring_0 (l:B ring)})") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"ideal_pow (ring_of_integers l) P (e - 1):B->bool"), (← q r"a:B->bool")] IDEAL_PROD_EQ_ZERO) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS, RING_IDEAL_IDEAL_POW] THEN CONV_TAC TAUT, ALL_TAC] THEN SUBGOAL_THEN (← q r"(a:B->bool) SUBSET P") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"ideal_pow (ring_of_integers l) P (e - 1):B->bool"), (← q r"a:B->bool"), (← q r"P:B->bool")] DEDEKIND_IDEAL_PROD_SUBSET_CANCEL) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW, RING_OF_INTEGERS] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN SUBGOAL_THEN (← q r"ideal_prod (ring_of_integers l)
          (ideal_pow (ring_of_integers l) P (e - 1)) P =
        ideal_pow (ring_of_integers l) (P:B->bool) e") SUBST1_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"P:B->bool"), (← q r"e - 1")] IDEAL_POW_SUC) THEN ASM_SIMP_TAC [r14] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC IDEAL_PROD_COMM THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_POW], ASM_REWRITE_TAC [LE_REFL]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x. x IN a ==> ring_pow l x e IN (q:B->bool)") ASSUME_TAC THENL [X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN MATCH_MP_TAC r13 THEN EXISTS_TAC (← q r"ideal_generated (ring_of_integers l) {ring_pow l x e:B}") THEN CONJ_TAC THENL [REWRITE_TAC [IN_IDEAL_GENERATED_SELF] THEN MATCH_MP_TAC IN_SUBRING_POW THEN ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBRING], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"x:B"), (← q r"e:num")] IDEAL_POW_PRINCIPAL) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN TRANS_TAC SUBSET_TRANS (← q r"ideal_pow (ring_of_integers l) a e:B->bool") THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_POW_MONO THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"a:B->bool"), (← q r"e - 1")] IDEAL_POW_SUC) THEN ASM_SIMP_TAC [r12] THEN DISCH_THEN SUBST1_TAC THEN USE_THEN "aq" (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [(← SYM th)])) THEN TRANS_TAC SUBSET_TRANS (← q r"ideal_prod (ring_of_integers l) a
          (ideal_pow (ring_of_integers l) P (e - 1)):B->bool") THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_PROD_MONO THEN ASM_SIMP_TAC [IDEAL_POW_MONO, SUBSET_REFL], MATCH_MP_TAC r11 THEN MATCH_MP_TAC IDEAL_PROD_COMM THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_POW]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x d. x IN a /\ d IN number_field_different (k,l) (h:A->B)
            ==> ring_mul l x d IN (q:B->bool)") (LABEL_TAC "div") THENL [REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"x:B")] NUMBER_FIELD_DIFFERENT_TRACE) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r10 THEN CONJ_TAC THENL [ALL_TAC, DISCH_THEN (MP_TAC o (SPEC (← q r"d:B"))) THEN ASM_REWRITE_TAC []] THEN X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN MATCH_MP_TAC NUMBER_FIELD_TRACE_NILPOTENT THEN EXISTS_TAC (← q r"e:num") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ring_mul l x y IN (a:B->bool)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"a:B->bool"), (← q r"x:B"), (← q r"y:B")] IN_RING_IDEAL_RMUL) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"ring_mul l x (y:B)")) o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_forall z1)) then (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); canM (fun z5 => (do let z6 ← (pure z5); find_termM (fun z7 => (do let z9 ← (pure z7); let z8 ← (q r"ring_pow:B ring->B->num->B"); pure (z8 == z9))) z6)) z3) else pure false))))) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"a:B->bool"), (← q r"number_field_different (k,l) (h:A->B)"), (← q r"ideal_pow (ring_of_integers l) P (e - 1):B->bool")] DEDEKIND_IDEAL_PROD_SUBSET_CANCEL) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW, RING_IDEAL_NUMBER_FIELD_DIFFERENT, RING_OF_INTEGERS] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN SUBGOAL_THEN (← q r"ideal_prod (ring_of_integers l) a
        (ideal_pow (ring_of_integers l) P (e - 1)) = (q:B->bool)") SUBST1_TAC THENL [USE_THEN "aq" (SUBST1_TAC o SYM) THEN MATCH_MP_TAC IDEAL_PROD_COMM THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_POW], ALL_TAC] THEN MATCH_MP_TAC IDEAL_PROD_MINIMAL THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN MAP_EVERY X_GEN_TAC [(← q r"x:B"), (← q r"d:B")] THEN STRIP_TAC THEN USE_THEN "div" MATCH_MP_TAC THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_DIFFERENT_RAMIFIED ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (q ==> r) ==> (p <=> q) ==> r")
    let r2 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    let r3 ← ARITH_RULE (← q r"~(2 <= 1)")
    let r13 ← SET_RULE (← q r"t SUBSET u ==> s SUBSET t ==> (s:B->bool) SUBSET u")
    prove
      r"!k:A ring l:B ring h P.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          prime_ideal (ring_of_integers l) P /\ ~(P = {ring_0 l})
          ==> (number_field_different (k,l) h SUBSET P <=>
               1 < ramification_index (ring_of_integers k,ring_of_integers l)
                     h P)"
      (REPEAT STRIP_TAC THEN EQ_TAC THENL [DISCH_TAC, DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"P:B->bool")] NUMBER_FIELD_DIFFERENT_SUBSET_RAMIFICATION) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r13 THEN FIRST_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [(← GSYM (← MATCH_MP IDEAL_POW_1 (← MATCH_MP PRIME_IMP_RING_IDEAL th)))])) THEN MATCH_MP_TAC IDEAL_POW_ANTIMONO THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, RING_IDEAL_IMP_SUBSET] THEN ASM_ARITH_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"P:B->bool")] RING_OF_INTEGERS_PRIME_IDEAL_BELOW) THEN ASM_REWRITE_TAC [EXISTS_UNIQUE_THM] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"p:A->bool") STRIP_ASSUME_TAC) o CONJUNCT1) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"P:B->bool")] RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"P:B->bool")] NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"q = ideal_generated (ring_of_integers l) (IMAGE (h:A->B) p)") THEN STRIP_TAC THEN STRIP_TAC THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ideal_valuation (ring_of_integers l) P (q:B->bool) =
      ramification_index (ring_of_integers k,ring_of_integers l) (h:A->B) P") ASSUME_TAC THENL [ASM_REWRITE_TAC [ramification_index], ALL_TAC] THEN ABBREV_TAC (← q r"e = ramification_index (ring_of_integers k,ring_of_integers l)
            (h:A->B) P") THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP NUMBER_FIELD_IMP_FIELD) o (checkM (fun th => (do let z12 ← (q r"number_field(l:B ring)"); let z11 ← (do let z10 ← (pure th); pure (concl z10)); pure (z11 == z12)))))) THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP DEDEKIND_RING_OF_INTEGERS) o (checkM (fun th => (do let z9 ← (q r"number_field(l:B ring)"); let z8 ← (do let z7 ← (pure th); pure (concl z7)); pure (z8 == z9)))))) THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP PRIME_IMP_RING_IDEAL) o (checkM (fun th => (do let z6 ← (q r"prime_ideal (ring_of_integers l) (P:B->bool)"); let z5 ← (do let z4 ← (pure th); pure (concl z4)); pure (z5 == z6)))))) THEN SUBGOAL_THEN (← q r"maximal_ideal (ring_of_integers l) (P:B->bool)") ASSUME_TAC THENL [MATCH_MP_TAC DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers l) (q:B->bool)") ASSUME_TAC THENL [EXPAND_TAC "q" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"!m. q SUBSET ideal_pow (ring_of_integers (l:B ring)) P m <=> m <= e") ASSUME_TAC THENL [ASM_SIMP_TAC [DEDEKIND_IDEAL_SUBSET_POW_VALUATION, RING_OF_INTEGERS], ALL_TAC] THEN REWRITE_TAC [(← GSYM NOT_LE)] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"e = 1") SUBST_ALL_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"?Q. ring_ideal (ring_of_integers l) Q /\
          ideal_prod (ring_of_integers l) P Q = (q:B->bool)") (X_CHOOSE_THEN (← q r"Q:B->bool") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pq"))) THENL [EXISTS_TAC (← q r"ideal_quotient (ring_of_integers l) q (P:B->bool)") THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_QUOTIENT, RING_IDEAL_IMP_SUBSET] THEN MATCH_MP_TAC DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"1"))) THEN ASM_SIMP_TAC [IDEAL_POW_1, LE_REFL], ALL_TAC] THEN SUBGOAL_THEN (← q r"~((Q:B->bool) SUBSET P)") ASSUME_TAC THENL [DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"2"))) THEN REWRITE_TAC [r3] THEN USE_THEN "pq" (SUBST1_TAC o SYM) THEN REWRITE_TAC [(← ExceptT.mk (num_CONV (← q r"2"))), (← ExceptT.mk (num_CONV (← q r"1"))), IDEAL_POW_SUC, IDEAL_POW_0] THEN SIMP_TAC [IDEAL_PROD_CARRIER, (← ASSUME (← q r"ring_ideal (ring_of_integers l) (P:B->bool)"))] THEN MATCH_MP_TAC IDEAL_PROD_MONO THEN ASM_REWRITE_TAC [SUBSET_REFL], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_setadd (ring_of_integers l) P Q = ring_carrier(ring_of_integers l) /\
      P INTER Q = (q:B->bool)") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r2 THEN CONJ_TAC THENL [ASM_SIMP_TAC [MAXIMAL_IDEAL_COMAXIMAL], DISCH_TAC THEN USE_THEN "pq" (SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC IDEAL_PROD_COMAXIMAL THEN ASM_REWRITE_TAC []], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"P:B->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_TRACE_COMAXIMAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"y:B") STRIP_ASSUME_TAC) THEN UNDISCH_TAC (← q r"~(algebra_trace (k,l) (h:A->B) y IN p)") THEN REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(y:B) IN ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"y:B")] NUMBER_FIELD_DIFFERENT_TRACE) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [ALL_TAC, DISCH_THEN (MP_TAC o (SPEC (← q r"ring_1 l:B"))) THEN SIMP_TAC [IN_SUBRING_1, RING_OF_INTEGERS_SUBRING] THEN SUBGOAL_THEN (← q r"(y:B) IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ASM_SIMP_TAC [RING_MUL_RID]]] THEN X_GEN_TAC (← q r"d:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(d:B) IN P /\ d IN ring_carrier(ring_of_integers l)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [SUBSET, RING_IDEAL_IMP_SUBSET, RING_IDEAL_NUMBER_FIELD_DIFFERENT], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul l y d = ring_mul l d (y:B)") SUBST1_TAC THENL [MATCH_MP_TAC RING_MUL_SYM THEN ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN USE_THEN "pq" (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"P:B->bool"), (← q r"Q:B->bool"), (← q r"d:B"), (← q r"y:B")] RING_MUL_IN_IDEAL_PROD) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [])

  let RING_OF_INTEGERS_IDEAL_DOUBLE_DUAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul (r:B ring) i (ring_mul r f (ring_mul r y t)) =
      ring_mul r t (ring_mul r y (ring_mul r i f))")
    let r2 ← RING_RULE (← q r"ring_mul (r:B ring) (ring_mul r i f) e =
        ring_mul r i (ring_mul r f e)")
    let r12 ← TAUT (← q r"p /\ (q ==> r) ==> (p <=> q) ==> r")
    let r13 ← TAUT (← q r"p /\ q /\ (p /\ q ==> r) ==> p /\ q /\ r")
    prove
      r"!l:B ring E.
          number_field l /\ ring_ideal (ring_of_integers l) E /\
          ~(E = {ring_0 l})
          ==> {y | y IN ring_carrier(ring_of_integers l) /\
                   !x. x IN ring_carrier l /\
                       (!e. e IN E
                            ==> ring_mul l x e IN
                                ring_carrier(ring_of_integers l))
                       ==> ring_mul l y x IN ring_carrier(ring_of_integers l)} =
              E"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_RING_OF_INTEGERS)) THEN SUBGOAL_THEN (← q r"E SUBSET ring_carrier(ring_of_integers(l:B ring))") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"y:B") THEN REWRITE_TAC [IN_ELIM_THM] THEN EQ_TAC THENL [STRIP_TAC, DISCH_TAC THEN CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN X_GEN_TAC (← q r"x:B") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_mul l y x = ring_mul l x (y:B)") SUBST1_TAC THENL [MATCH_MP_TAC RING_MUL_SYM THEN ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ASM_SIMP_TAC []]] THEN SUBGOAL_THEN (← q r"?d:B. d IN E /\ ~(d = ring_0 l)") STRIP_ASSUME_TAC THENL [MP_TAC (← MATCH_MP RING_IDEAL_IMP_NONEMPTY (← ASSUME (← q r"ring_ideal (ring_of_integers l) (E:B->bool)"))) THEN UNDISCH_TAC (← q r"~(E = {ring_0 l:B})") THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"E:B->bool")] IN_RING_IDEAL_0) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(d:B) IN ring_carrier(ring_of_integers l) /\
                  d IN ring_carrier l") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN ABBREV_TAC (← q r"G = ideal_quotient (ring_of_integers l)
            (ideal_generated (ring_of_integers l) {d:B}) E") THEN SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers l) (G:B->bool) /\
      ideal_prod (ring_of_integers l) E G =
      ideal_generated (ring_of_integers l) {d:B} /\
      ~(G = {ring_0 l})") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r13 THEN REPEAT CONJ_TAC THENL [EXPAND_TAC "G" THEN MATCH_MP_TAC RING_IDEAL_IDEAL_QUOTIENT THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED], EXPAND_TAC "G" THEN MATCH_MP_TAC DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET], STRIP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"ideal_prod (ring_of_integers l) E {ring_0 l} =
          ideal_generated (ring_of_integers l) {d:B}") THEN ASM_SIMP_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") IDEAL_PROD_RZERO))] THEN DISCH_THEN (MP_TAC o (AP_TERM (← q r"\s:B->bool. (d:B) IN s"))) THEN ASM_REWRITE_TAC [IN_SING, IN_IDEAL_GENERATED_SELF]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"G:B->bool"), (← q r"ideal_generated (ring_of_integers l) {y:B}"), (← q r"E:B->bool")] DEDEKIND_IDEAL_PROD_SUBSET_CANCEL) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, RING_OF_INTEGERS] THEN MATCH_MP_TAC r12 THEN CONJ_TAC THENL [ALL_TAC, DISCH_THEN (MATCH_MP_TAC o (REWRITE_RULE [SUBSET])) THEN ASM_REWRITE_TAC [IN_IDEAL_GENERATED_SELF]] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"G:B->bool"), (← q r"E:B->bool")] IDEAL_PROD_COMM) THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IDEAL_PROD_MINIMAL THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN MAP_EVERY X_GEN_TAC [(← q r"f:B"), (← q r"v:B")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"y:B")] IDEAL_GENERATED_SING_ALT) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => tactic_of do pure (UNDISCH_TAC (← q r"(v:B) IN ideal_generated (ring_of_integers l) {y}") THEN REWRITE_TAC [th, IN_ELIM_THM, RING_OF_INTEGERS])) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"t:B") STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(f:B) IN ring_carrier(ring_of_integers l) /\
                  f IN ring_carrier l /\ t IN ring_carrier l /\
                  y IN ring_carrier l") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET, RING_OF_INTEGERS_SUBSET], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"ring_mul l (ring_inv l d) (f:B)")) o (checkM (fun th => (do if ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); pure (is_forall z3)) then (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); canM (fun z7 => (do let z8 ← (pure z7); find_termM (fun z9 => (do let z11 ← (pure z9); let z10 ← (q r"y:B"); pure (z10 == z11))) z8)) z5) else pure false))))) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_MUL, RING_INV] THEN X_GEN_TAC (← q r"e:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(e:B) IN ring_carrier(ring_of_integers l) /\
                    e IN ring_carrier l") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul l (ring_mul l (ring_inv l d) f) e =
        ring_mul l (ring_inv l d) (ring_mul l f (e:B))") SUBST1_TAC THENL [MATCH_MP_TAC r2 THEN ASM_SIMP_TAC [RING_INV], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"d:B"), (← q r"ring_mul l f (e:B)")] RING_OF_INTEGERS_IN_IDEAL_GENERATED_SING) THEN ASM_SIMP_TAC [RING_MUL] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN UNDISCH_TAC (← q r"(f:B) IN G") THEN EXPAND_TAC "G" THEN REWRITE_TAC [ideal_quotient, IN_ELIM_THM, RING_OF_INTEGERS] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"e:B")) o CONJUNCT2)) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"d:B"), (← q r"ring_mul l f (ring_mul l y (t:B))")] RING_OF_INTEGERS_IN_IDEAL_GENERATED_SING) THEN ASM_SIMP_TAC [RING_MUL] THEN DISCH_THEN SUBST1_TAC THEN SUBGOAL_THEN (← q r"ring_mul l (ring_inv l d) (ring_mul l f (ring_mul l y t)) =
      ring_mul l t (ring_mul l y (ring_mul l (ring_inv l d) (f:B)))") SUBST1_TAC THENL [MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [RING_INV], MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_MUL)) THEN ASM_REWRITE_TAC []])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_DIFFERENT_TRACE, NUMBER_FIELD_DIFFERENT_SUBSET_RAMIFICATION,
           NUMBER_FIELD_DIFFERENT_RAMIFIED, RING_OF_INTEGERS_IDEAL_DOUBLE_DUAL }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- different_extension.ml phrases from line 1869 to 2124                  -/
/- ---------------------------------------------------------------------- -/

structure DifferentExtension04 where
  -- @@FIELDS
  NUMBER_FIELD_CODIFFERENT_TOWER : thm
  NUMBER_FIELD_DIFFERENT_TOWER : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDifferentExtension04 [HolBase] (D : DifferentExtensionDeps) (BDifferentExtension03 : DifferentExtension03) :
    ExceptT String IO DifferentExtension04 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, RING_RULE, SET_TAC, .. } := D
  let { ALGEBRA_TRACE_NORM_IN_CARRIER, ALGEBRA_TRACE_NORM_TOWER, ALGEBRA_TRACE_SCALAR,
        EQ_TRANS, EXTENSION, FINITE_IMP_FIELD_EXTENSION, FUN_IN_IMAGE,
        IDEAL_GENERATED_RING_IDEAL, IDEAL_PROD_EQ_ZERO, IDEAL_PROD_IDEAL_GENERATED,
        IDEAL_PROD_MINIMAL, IMP_CONJ, INTEGRAL_DOMAIN_RING_OF_INTEGERS, IN_ELIM_THM,
        IN_IMAGE, IN_SUBRING_1, .. } := D.core1
  let { NUMBER_FIELD_CODIFFERENT_DIFFERENT, NUMBER_FIELD_DIFFERENT_NONZERO,
        NUMBER_FIELD_HOMOMORPHIC_PREIMAGE, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_TOWER_LAW, RING_ADD_LDISTRIB, RING_HOMOMORPHISM_COMPOSE,
        RING_HOMOMORPHISM_IN_CARRIER, RING_HOMOMORPHISM_RING_OF_INTEGERS,
        RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_PROD, RING_IDEAL_IMP_SUBSET,
        RING_IDEAL_NUMBER_FIELD_DIFFERENT, RING_MUL, RING_MUL_IN_IDEAL_PROD,
        RING_MUL_RID, RING_MUL_RNEG, RING_MUL_RZERO, RING_MUL_SYM, RING_OF_INTEGERS,
        RING_OF_INTEGERS_IDEAL_EXTENSION, RING_OF_INTEGERS_SUBRING,
        RING_OF_INTEGERS_SUBSET, SUBSET, number_field_codifferent,
        number_field_different, ring_ideal, subring_of, .. } := D.core2
  let { RING_OF_INTEGERS_IDEAL_DOUBLE_DUAL, .. } := BDifferentExtension03
  -- @@SCOPE END

  let NUMBER_FIELD_CODIFFERENT_TOWER ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul (r:C ring) (ring_mul r x a) e =
      ring_mul r x (ring_mul r e a)")
    let r2 ← RING_RULE (← q r"ring_mul (r:C ring) (ring_mul r x a) z =
          ring_mul r a (ring_mul r x z)")
    let r3 ← RING_RULE (← q r"ring_mul (r:C ring) x (ring_mul r z a) =
            ring_mul r a (ring_mul r x z)")
    let r4 ← RING_RULE (← q r"ring_mul (r:C ring) x (ring_mul r a z) =
          ring_mul r a (ring_mul r x z)")
    prove
      r"!k:A ring l:B ring m:C ring h1 h2.
          field k /\ field l /\ number_field m /\
          ring_homomorphism(k,l) h1 /\ ring_homomorphism(l,m) h2
          ==> number_field_codifferent (k,m) (h2 o h1) =
              {x | x IN ring_carrier m /\
                   !e. e IN ideal_prod (ring_of_integers m)
                              (number_field_different (l,m) h2)
                              (ideal_generated (ring_of_integers m)
                                (IMAGE h2 (number_field_different (k,l) h1)))
                       ==> ring_mul m x e IN ring_carrier(ring_of_integers m)}"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"m:C ring"), (← q r"h2:B->C")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"m:C ring"), (← q r"h2:B->C")] NUMBER_FIELD_TOWER_LAW) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h1:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o ((MATCH_MP FINITE_IMP_FIELD_EXTENSION) o CONJUNCT1)) THEN DISCH_THEN (ASSUME_TAC o ((MATCH_MP FINITE_IMP_FIELD_EXTENSION) o CONJUNCT1)) THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP NUMBER_FIELD_IMP_FIELD) o (checkM (fun th => (do let z10 ← (q r"number_field(m:C ring)"); let z9 ← (do let z8 ← (pure th); pure (concl z8)); pure (z9 == z10)))))) THEN SUBGOAL_THEN (← q r"ring_homomorphism(k:A ring,m:C ring) ((h2:B->C) o (h1:A->B))") ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_COMPOSE], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h1:A->B")] RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"m:C ring"), (← q r"h2:B->C")] RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN ASM_REWRITE_TAC [] THEN REPEAT DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP (← REWRITE_RULE [IMP_CONJ] RING_HOMOMORPHISM_IN_CARRIER)) o (checkM (fun th => (do let z7 ← (q r"ring_homomorphism                    (ring_of_integers l,ring_of_integers m) (h2:B->C)"); let z6 ← (do let z5 ← (pure th); pure (concl z5)); pure (z6 == z7)))))) THEN ABBREV_TAC (← q r"D1 = number_field_different (k,l) (h1:A->B)") THEN ABBREV_TAC (← q r"D2 = number_field_different (l,m) (h2:B->C)") THEN SUBGOAL_THEN (← q r"(D1:B->bool) SUBSET ring_carrier(ring_of_integers (l:B ring)) /\
      (D2:C->bool) SUBSET ring_carrier(ring_of_integers(m:C ring))") STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["D1", "D2"] THEN SIMP_TAC [RING_IDEAL_IMP_SUBSET, RING_IDEAL_NUMBER_FIELD_DIFFERENT], ALL_TAC] THEN SUBGOAL_THEN (← q r"IMAGE (h2:B->C) D1 SUBSET ring_carrier(ring_of_integers m)") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x. x IN ring_carrier m
          ==> ((!e. e IN ideal_prod (ring_of_integers m) D2
                           (ideal_generated (ring_of_integers m)
                              (IMAGE (h2:B->C) D1))
                    ==> ring_mul m x e IN ring_carrier(ring_of_integers m)) <=>
               (!e1 e2. e1 IN D1 /\ e2 IN D2
                        ==> ring_mul m x (ring_mul m e2 (h2 e1)) IN
                            ring_carrier(ring_of_integers m)))") (LABEL_TAC "gen") THENL [X_GEN_TAC (← q r"x:C") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ideal_prod (ring_of_integers m) D2
          (ideal_generated (ring_of_integers m) (IMAGE (h2:B->C) D1)) =
        ideal_prod (ring_of_integers m) D2 (IMAGE h2 D1)") SUBST1_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers m:C ring"), (← q r"D2:C->bool"), (← q r"IMAGE (h2:B->C) D1")] IDEAL_PROD_IDEAL_GENERATED) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC IDEAL_GENERATED_RING_IDEAL THEN EXPAND_TAC "D2" THEN REWRITE_TAC [RING_IDEAL_NUMBER_FIELD_DIFFERENT], ALL_TAC] THEN EQ_TAC THEN DISCH_TAC THENL [MAP_EVERY X_GEN_TAC [(← q r"e1:B"), (← q r"e2:C")] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers m:C ring") RING_MUL_IN_IDEAL_PROD)) THEN ASM_SIMP_TAC [FUN_IN_IMAGE] THEN ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_prod (ring_of_integers m) D2 (IMAGE (h2:B->C) D1) SUBSET
        {e | e IN ring_carrier(ring_of_integers m) /\
             ring_mul m x e IN ring_carrier(ring_of_integers m)}") MP_TAC THENL [ALL_TAC, SET_TAC []] THEN MATCH_MP_TAC IDEAL_PROD_MINIMAL THEN CONJ_TAC THENL [REWRITE_TAC [ring_ideal, SUBSET, IN_ELIM_THM, RING_OF_INTEGERS] THEN MP_TAC (← ISPEC (← q r"m:C ring") (← CONJUNCT1 RING_OF_INTEGERS_SUBRING)) THEN REWRITE_TAC [subring_of, SUBSET] THEN STRIP_TAC THEN ASM_SIMP_TAC [RING_MUL_RZERO, RING_MUL_RNEG, RING_ADD_LDISTRIB] THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_mul m x (ring_mul m x' y) =
                      ring_mul m x' (ring_mul (m:C ring) x y)") SUBST1_TAC THENL [MATCH_MP_TAC r4 THEN ASM_SIMP_TAC [], ASM_SIMP_TAC []], MAP_EVERY X_GEN_TAC [(← q r"e2:C"), (← q r"b:C")] THEN REWRITE_TAC [IN_IMAGE, IN_ELIM_THM, RING_OF_INTEGERS] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"e1:B") STRIP_ASSUME_TAC)) THEN ASM_SIMP_TAC [] THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers m:C ring") RING_MUL)) THEN ASM SET_TAC []], ALL_TAC] THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:C") THEN REWRITE_TAC [number_field_codifferent, IN_ELIM_THM] THEN ASM_CASES_TAC (← q r"(x:C) IN ring_carrier m") THEN ASM_REWRITE_TAC [] THEN USE_THEN "gen" (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP th (← ASSUME (← q r"(x:C) IN ring_carrier m")))])) THEN SUBGOAL_THEN (← q r"!z. z IN ring_carrier m
          ==> algebra_trace (k,m) ((h2:B->C) o (h1:A->B)) z =
              algebra_trace (k,l) h1 (algebra_trace (l,m) h2 z)") (fun th => tactic_of do pure (SIMP_TAC [th, RING_MUL, (← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET), (← ASSUME (← q r"(x:C) IN ring_carrier m"))])) THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h1:A->B"), (← q r"h2:B->C"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"m:C ring"), (← q r"z:C")] ALGEBRA_TRACE_NORM_TOWER) THEN ASM_SIMP_TAC [], ALL_TAC] THEN TRANS_TAC EQ_TRANS (← q r"!z. z IN ring_carrier(ring_of_integers m)
          ==> algebra_trace (l,m) (h2:B->C) (ring_mul m x z) IN
              number_field_codifferent (k,l) (h1:A->B)") THEN CONJ_TAC THENL [EQ_TAC THEN DISCH_TAC THENL [X_GEN_TAC (← q r"z:C") THEN DISCH_TAC THEN REWRITE_TAC [number_field_codifferent, IN_ELIM_THM, ALGEBRA_TRACE_NORM_IN_CARRIER] THEN X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(z:C) IN ring_carrier m /\ (y:B) IN ring_carrier l /\
          (h2:B->C) y IN ring_carrier(ring_of_integers m) /\
          h2 y IN ring_carrier m") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET, RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul l (algebra_trace (l,m) (h2:B->C) (ring_mul m x z)) y =
          algebra_trace (l,m) h2 (ring_mul m x (ring_mul m z (h2 y)))") SUBST1_TAC THENL [MP_TAC (← ISPECL [(← q r"h2:B->C"), (← q r"l:B ring"), (← q r"m:C ring"), (← q r"y:B"), (← q r"ring_mul m x (z:C)")] ALGEBRA_TRACE_SCALAR) THEN ASM_SIMP_TAC [RING_MUL] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN CONV_TAC SYM_CONV THEN SUBGOAL_THEN (← q r"ring_mul m x (ring_mul m z ((h2:B->C) y)) =
            ring_mul m (h2 y) (ring_mul m x z)") SUBST1_TAC THENL [MATCH_MP_TAC r3 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h2:B->C"), (← q r"l:B ring"), (← q r"m:C ring"), (← q r"y:B"), (← q r"ring_mul m x (z:C)")] ALGEBRA_TRACE_SCALAR) THEN ASM_SIMP_TAC [RING_MUL] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_MUL_SYM THEN ASM_REWRITE_TAC [ALGEBRA_TRACE_NORM_IN_CARRIER], ALL_TAC] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers m:C ring") RING_MUL)) THEN ASM_REWRITE_TAC [], X_GEN_TAC (← q r"z:C") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (← do let c := (← ASSUME (← q r"(z:C) IN ring_carrier(ring_of_integers m)")); pure (fun th => MATCH_MP th c))) THEN REWRITE_TAC [number_field_codifferent, IN_ELIM_THM] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"ring_1 l:B")) o CONJUNCT2)) THEN SIMP_TAC [IN_SUBRING_1, RING_OF_INTEGERS_SUBRING] THEN SIMP_TAC [RING_MUL_RID, ALGEBRA_TRACE_NORM_IN_CARRIER]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h1:A->B")] NUMBER_FIELD_CODIFFERENT_DIFFERENT) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [IN_ELIM_THM, ALGEBRA_TRACE_NORM_IN_CARRIER] THEN TRANS_TAC EQ_TRANS (← q r"!e1. e1 IN D1
           ==> ring_mul m x ((h2:B->C) e1) IN
               number_field_codifferent (l,m) h2") THEN CONJ_TAC THENL [REWRITE_TAC [number_field_codifferent, IN_ELIM_THM] THEN SUBGOAL_THEN (← q r"!e1. e1 IN D1 ==> ring_mul m x ((h2:B->C) e1) IN ring_carrier m") (fun th => SIMP_TAC [th]) THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"!z e1. z IN ring_carrier(ring_of_integers m) /\ e1 IN D1
               ==> ring_mul l
                     (algebra_trace (l,m) (h2:B->C) (ring_mul m x z)) e1 =
                   algebra_trace (l,m) h2 (ring_mul m (ring_mul m x (h2 e1)) z)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"(z:C) IN ring_carrier m /\ (e1:B) IN ring_carrier l /\
          (h2:B->C) e1 IN ring_carrier m") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET, RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul m (ring_mul m x ((h2:B->C) e1)) z =
          ring_mul m (h2 e1) (ring_mul m x z)") SUBST1_TAC THENL [MATCH_MP_TAC r2 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h2:B->C"), (← q r"l:B ring"), (← q r"m:C ring"), (← q r"e1:B"), (← q r"ring_mul m x (z:C)")] ALGEBRA_TRACE_SCALAR) THEN ASM_SIMP_TAC [RING_MUL] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_MUL_SYM THEN ASM_REWRITE_TAC [ALGEBRA_TRACE_NORM_IN_CARRIER], ALL_TAC] THEN ASM_SIMP_TAC [] THEN MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"m:C ring"), (← q r"h2:B->C")] NUMBER_FIELD_CODIFFERENT_DIFFERENT) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN SUBGOAL_THEN (← q r"!e1 e2. e1 IN D1 /\ e2 IN D2
              ==> ring_mul m (ring_mul m x ((h2:B->C) e1)) e2 =
                  ring_mul m x (ring_mul m e2 (h2 e1))") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"!e1. e1 IN D1 ==> ring_mul m x ((h2:B->C) e1) IN ring_carrier m") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [] THEN MESON_TAC [])

  let NUMBER_FIELD_DIFFERENT_TOWER ← prove
    r"!k:A ring l:B ring m:C ring h1 h2.
        field k /\ field l /\ number_field m /\
        ring_homomorphism(k,l) h1 /\ ring_homomorphism(l,m) h2
        ==> number_field_different (k,m) (h2 o h1) =
            ideal_prod (ring_of_integers m)
              (number_field_different (l,m) h2)
              (ideal_generated (ring_of_integers m)
                 (IMAGE h2 (number_field_different (k,l) h1)))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"m:C ring"), (← q r"h2:B->C")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN ABBREV_TAC (← q r"E = ideal_prod (ring_of_integers m)
          (number_field_different (l,m) (h2:B->C))
          (ideal_generated (ring_of_integers m)
             (IMAGE h2 (number_field_different (k,l) (h1:A->B))))") THEN SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers m) (E:C->bool) /\ ~(E = {ring_0 m})") STRIP_ASSUME_TAC THENL [EXPAND_TAC "E" THEN REWRITE_TAC [RING_IDEAL_IDEAL_PROD] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers m:C ring"), (← q r"number_field_different (l,m) (h2:B->C)"), (← q r"ideal_generated (ring_of_integers (m:C ring))
                     (IMAGE (h2:B->C)
                       (number_field_different (k,l) (h1:A->B)))")] IDEAL_PROD_EQ_ZERO) THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_RING_OF_INTEGERS, NUMBER_FIELD_IMP_FIELD, RING_IDEAL_NUMBER_FIELD_DIFFERENT, RING_IDEAL_IDEAL_GENERATED, RING_OF_INTEGERS] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"m:C ring"), (← q r"h2:B->C"), (← q r"number_field_different (k,l) (h1:A->B)")] RING_OF_INTEGERS_IDEAL_EXTENSION) THEN ASM_REWRITE_TAC [RING_IDEAL_NUMBER_FIELD_DIFFERENT] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN ASM_SIMP_TAC [NUMBER_FIELD_DIFFERENT_NONZERO], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"m:C ring"), (← q r"E:C->bool")] RING_OF_INTEGERS_IDEAL_DOUBLE_DUAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [number_field_different] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"m:C ring"), (← q r"h1:A->B"), (← q r"h2:B->C")] NUMBER_FIELD_CODIFFERENT_TOWER) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN MESON_TAC [])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_CODIFFERENT_TOWER, NUMBER_FIELD_DIFFERENT_TOWER }
  -- @@RETURN END

end HolANT.DifferentExtension
