/- ========================================================================= -/
/- ANT: Decomposition and inertia groups and Frobenius elements in a ...   -/
/- ========================================================================= -/
/- File: HolANT/NfDecomposition.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/nf_decomposition.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antnfdecompositiondiff; the rest is by hand.  Its `needs` closure is
  Library/frag.ml, Library/wo.ml, Library/card.ml, Library/prime.ml, Library/grouptheory.ml, Library/matroids.ml, Library/binomial.ml, Library/iter.ml, Library/pocklington.ml, Library/ringtheory.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/symmetric_group.ml, Library/galois.ml, Library/ring_groups.ml, Library/finite_fields.ml, ANT/ideal_arith.ml, ANT/decomposition.ml, Library/isum.ml, Library/products.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/norm_index.ml, ANT/classgroup.ml, ANT/nf_valuation.ml, ANT/prime_split.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/relative_degree.ml, ANT/finite_field_trace.ml, ANT/ramification.ml, ANT/splitting_types.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.NfDecomposition fills them).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left; where a proof applies rules that print or use
  counters (MESON, ARITH_RULE, ...) they are bound first, in OCaml's order.
-/

import HolANT.Prelude
import HolLibrary.Frag
import HolLibrary.Wo
import HolLibrary.Card
import HolLibrary.Prime
import HolLibrary.GroupTheory
import HolLibrary.Matroids
import HolLibrary.Binomial
import HolLibrary.Iter
import HolLibrary.Pocklington
import HolLibrary.RingTheory
import HolLibrary.Permutations
import HolLibrary.RingDet
import HolLibrary.FieldTheory
import HolLibrary.SymmetricGroup
import HolLibrary.Galois
import HolLibrary.RingGroups
import HolLibrary.FiniteFields
import HolANT.IdealArith
import HolANT.Decomposition
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
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.NormIndex
import HolANT.Classgroup
import HolANT.NfValuation
import HolANT.PrimeSplit
import HolANT.Discriminant
import HolANT.TraceForm
import HolANT.RelativeSplit
import HolANT.RelativeDegree
import HolANT.FiniteFieldTrace
import HolANT.Ramification
import HolANT.SplittingTypes

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.IdealArith
open HolANT.Decomposition
open HolANT.Algmisc
open HolANT.Integral
open HolANT.Zlattice
open HolANT.Numfield
open HolANT.Dedekind
open HolANT.DedekindStruct
open HolANT.IdealNorm
open HolANT.RingOfIntegers
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.NormIndex
open HolANT.Classgroup
open HolANT.NfValuation
open HolANT.PrimeSplit
open HolANT.Discriminant
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.RelativeDegree
open HolANT.FiniteFieldTrace
open HolANT.Ramification
open HolANT.SplittingTypes

namespace HolANT.NfDecomposition

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (BIJECTIONS_CARD_EQ CARD_DECOMPOSITION_GROUP CARD_EQ_0 CARD_IMAGE_INJ
   CARD_SING CARD_SUBSET_EQ CARRIER_SUBFIELD_GENERATED_SUBFIELD
   DECOMPOSITION_GROUP DECOMPOSITION_GROUP_IMAGE_RING_COSET
   DECOMPOSITION_GROUP_INDEX DECOMPOSITION_GROUP_RESIDUE_EPIMORPHISM
   DECOMPOSITION_GROUP_RESIDUE_HOMOMORPHISM DEDEKIND_IDEAL_INDUCT
   DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL DEDEKIND_RING_OF_INTEGERS
   DEDEKIND_VALUATION EQ_MULT_LCANCEL EQ_MULT_RCANCEL EQ_TRANS EXISTS_UNIQUE_THM
   EXTENSION EXTENSION_DEGREE_RESIDUE_CONJUGATE FIELD_IMP_INTEGRAL_DOMAIN
   FIELD_IMP_NONTRIVIAL_RING FIELD_QUOTIENT_RING
   FIELD_RING_HOMOMORPHISM_MONOMORPHISM FIELD_SUBFIELD_GENERATED
   FINITE_GALOIS_GROUP FINITE_IMAGE FINITE_INTEGRAL_DOMAIN_IMP_FIELD
   FINITE_QUOTIENT_RING_HOMOMORPHIC_PREIMAGE FINITE_RESTRICT
   FINITE_SUBRING_GENERATED FINITE_SUBSET FORALL_IN_IMAGE FROBENIUS_ELEMENT
   FROBENIUS_ELEMENT_CONJUGATE FUN_EQ_THM GALOIS_EXTENSION_SUBFIELD_GENERATED
   GALOIS_GROUP GALOIS_GROUP_COMPOSE GALOIS_GROUP_FINITE_FIELD
   GALOIS_GROUP_FIXED_FIELD GALOIS_GROUP_FIXES GALOIS_GROUP_INVERSE
   GALOIS_GROUP_PERMUTES GALOIS_GROUP_PRIME_IDEAL_IMAGE
   GALOIS_GROUP_RING_AUTOMORPHISM GALOIS_GROUP_RING_HOMOMORPHISM
   GALOIS_GROUP_SUBRING_IMAGE GALOIS_GROUP_TRANSITIVE_PRIME_IDEALS
   GALOIS_IMP_FIELD_EXTENSION GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET
   GROUP_ELEMENT_ORDER_MONOMORPHIC_IMAGE GROUP_ELEMENT_ORDER_SUBGROUP_GENERATED
   GROUP_ID GROUP_INV GROUP_MONOMORPHISM IDEAL_GENERATED_BY_EPIMORPHIC_IMAGE
   IDEAL_GENERATED_IMAGE_IDEAL_GENERATED IDEAL_GENERATED_INC_GEN
   IDEAL_GENERATED_RING_IDEAL IDEAL_PROD_EPIMORPHIC_IMAGE
   IDEAL_VALUATION_HOMOMORPHIC_IMAGE IDEAL_VALUATION_PRIME IMAGE_CLAUSES
   IMAGE_EQ IMAGE_I IMAGE_o IMP_CONJ INERTIA_GROUP INTEGRAL_DOMAIN_MUL_EQ_0
   INTEGRAL_DOMAIN_SUBRING_GENERATED IN_ELIM_THM IN_IMAGE IN_RING_IDEAL_0
   IN_SING I_DEF I_O_ID I_THM MAXIMAL_IMP_PRIME_IDEAL : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (MAXIMAL_IMP_RING_IDEAL MEMBER_NOT_EMPTY MONO_EXISTS MULT_CLAUSES
   NOT_FORALL_THM NSUM_CONST NSUM_EQ NUMBER_FIELD_FUNDAMENTAL_IDENTITY
   NUMBER_FIELD_HOMOMORPHIC_PREIMAGE NUMBER_FIELD_IDEAL_NORM_MUL_Q
   NUMBER_FIELD_IMP_FIELD NUMBER_FIELD_PRIME_IDEAL_ABOVE NUMBER_FIELD_TOWER_LAW
   PERMUTES_INVERSE PERMUTES_INVERSES PERMUTES_IN_IMAGE PRIME_IDEAL_IMP_SUBSET
   PRIME_IMP_RING_IDEAL QUOTIENT_RING_CARRIER RAMIFICATION_INDEX_TOWER
   RESIDUE_DEGREE_QUOTIENT_RING RING_0 RING_CARRIER_SUBRING_GENERATED_SUBSET
   RING_COSET_EQ RING_EPIMORPHISM_IMP_HOMOMORPHISM RING_EPIMORPHISM_RING_COSET
   RING_HOMOMORPHISM_0 RING_HOMOMORPHISM_POW RING_HOMOMORPHISM_RING_OF_INTEGERS
   RING_HOMOMORPHISM_SUBFIELD_INCLUSION RING_IDEAL_IDEAL_GENERATED
   RING_IDEAL_IMP_SUBSET RING_ISOMORPHISM_IMP_EPIMORPHISM
   RING_ISOMORPHISM_IMP_HOMOMORPHISM RING_ISOMORPHISM_IMP_MONOMORPHISM
   RING_MONOMORPHISM_EQ_0 RING_MONOMORPHISM_IMP_HOMOMORPHISM
   RING_MONOMORPHISM_INCLUSION RING_MONOMORPHISM_INTO_SUBRING
   RING_MONOMORPHISM_RING_OF_INTEGERS RING_OF_INTEGERS
   RING_OF_INTEGERS_FINITE_QUOTIENT RING_OF_INTEGERS_FRACTION_FIELD
   RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE_EQ RING_OF_INTEGERS_PRIME_IDEAL_BELOW
   RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION RING_OF_INTEGERS_SUBRING
   RING_OF_INTEGERS_SUBSET RING_POW RING_POW_SUBRING_GENERATED
   RING_SUB_SUBRING_GENERATED SING_SUBSET SUBFIELD_OF_IMP_SUBSET
   SUBGROUP_GENERATED_ELEMENT_ORDER SUBGROUP_GENERATED_IDEMPOT_GEN
   SUBGROUP_GENERATED_INC SUBGROUP_GENERATED_MINIMAL SUBGROUP_SUBGROUP_GENERATED
   SUBRING_GENERATED_BY_SUBFIELD_GENERATED SUBRING_GENERATED_QUOTIENT_RING_IMAGE
   SUBSET SUBSET_ANTISYM SUBSET_REFL UNRAMIFIED_IMP_WEAKLY_UNRAMIFIED
   decomposition_group field_extension field_of_fractions finite_extension
   group_conjugation group_epimorphism ideal_norm inertia_group o_ASSOC o_THM
   ramification_index residue_degree ring_automorphism ring_homomorphism
   ring_monomorphism subgroup_of weakly_unramified : thm)
  deriving Inhabited

/-- What nf_decomposition.ml uses from Session besides theorems. -/
structure NfDecompositionDeps where
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
/- nf_decomposition.ml phrases from line 75 to 489                        -/
/- ---------------------------------------------------------------------- -/

structure NfDecomposition01 where
  -- @@FIELDS
  GALOIS_GROUP_RING_OF_INTEGERS : thm
  DECOMPOSITION_GROUP_RING_OF_INTEGERS : thm
  GALOIS_GROUP_RING_OF_INTEGERS_AUTOMORPHISM : thm
  GALOIS_GROUP_RING_OF_INTEGERS_IDEAL : thm
  GALOIS_GROUP_IMAGE_IDEAL_GENERATED : thm
  NUMBER_FIELD_GALOIS_GROUP_TRANSITIVE : thm
  CARD_GALOIS_GROUP_IMAGE_FIBER : thm
  IDEAL_NORM_RESIDUE_IMAGE : thm
  NUMBER_FIELD_RAMIFICATION_INDEX_CONJUGATE : thm
  NUMBER_FIELD_IDEAL_NORM_CONJUGATE : thm
  NUMBER_FIELD_IDEAL_NORM_GALOIS_IMAGE : thm
  NUMBER_FIELD_DECOMPOSITION_GROUP : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupNfDecomposition01 [HolBase] (D : NfDecompositionDeps) :
    ExceptT String IO NfDecomposition01 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, TAUT, .. } := D
  let { BIJECTIONS_CARD_EQ, CARD_DECOMPOSITION_GROUP, CARD_EQ_0, CARD_IMAGE_INJ,
        DECOMPOSITION_GROUP, DECOMPOSITION_GROUP_INDEX, DEDEKIND_IDEAL_INDUCT,
        DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL, DEDEKIND_RING_OF_INTEGERS, EQ_MULT_LCANCEL,
        EQ_MULT_RCANCEL, EQ_TRANS, EXTENSION, EXTENSION_DEGREE_RESIDUE_CONJUGATE,
        FINITE_GALOIS_GROUP, FINITE_QUOTIENT_RING_HOMOMORPHIC_PREIMAGE,
        FINITE_RESTRICT, FINITE_SUBSET, FORALL_IN_IMAGE, FUN_EQ_THM, GALOIS_GROUP,
        GALOIS_GROUP_COMPOSE, GALOIS_GROUP_FIXES, GALOIS_GROUP_INVERSE,
        GALOIS_GROUP_PERMUTES, GALOIS_GROUP_PRIME_IDEAL_IMAGE,
        GALOIS_GROUP_RING_AUTOMORPHISM, GALOIS_GROUP_RING_HOMOMORPHISM,
        GALOIS_GROUP_SUBRING_IMAGE, GALOIS_GROUP_TRANSITIVE_PRIME_IDEALS,
        GALOIS_IMP_FIELD_EXTENSION, GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET, GROUP_ID,
        GROUP_INV, IDEAL_GENERATED_BY_EPIMORPHIC_IMAGE, IDEAL_GENERATED_RING_IDEAL,
        IDEAL_PROD_EPIMORPHIC_IMAGE, IDEAL_VALUATION_PRIME, IMAGE_CLAUSES, IMAGE_EQ,
        IMAGE_I, IMAGE_o, IN_ELIM_THM, IN_IMAGE, IN_RING_IDEAL_0, IN_SING, I_O_ID,
        I_THM, MAXIMAL_IMP_PRIME_IDEAL, .. } := D.core1
  let { MEMBER_NOT_EMPTY, MONO_EXISTS, MULT_CLAUSES, NOT_FORALL_THM, NSUM_CONST,
        NSUM_EQ, NUMBER_FIELD_FUNDAMENTAL_IDENTITY, NUMBER_FIELD_IDEAL_NORM_MUL_Q,
        NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_PRIME_IDEAL_ABOVE, NUMBER_FIELD_TOWER_LAW,
        PERMUTES_INVERSE, PERMUTES_INVERSES, PERMUTES_IN_IMAGE, PRIME_IDEAL_IMP_SUBSET,
        PRIME_IMP_RING_IDEAL, QUOTIENT_RING_CARRIER, RAMIFICATION_INDEX_TOWER,
        RESIDUE_DEGREE_QUOTIENT_RING, RING_0, RING_HOMOMORPHISM_0,
        RING_HOMOMORPHISM_RING_OF_INTEGERS, RING_IDEAL_IMP_SUBSET,
        RING_ISOMORPHISM_IMP_EPIMORPHISM, RING_ISOMORPHISM_IMP_HOMOMORPHISM,
        RING_ISOMORPHISM_IMP_MONOMORPHISM, RING_MONOMORPHISM_IMP_HOMOMORPHISM,
        RING_MONOMORPHISM_RING_OF_INTEGERS, RING_OF_INTEGERS,
        RING_OF_INTEGERS_FINITE_QUOTIENT, RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE_EQ,
        RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION, RING_OF_INTEGERS_SUBRING,
        RING_OF_INTEGERS_SUBSET, SING_SUBSET, SUBSET, SUBSET_ANTISYM, SUBSET_REFL,
        decomposition_group, field_extension, finite_extension, ideal_norm, o_ASSOC,
        o_THM, ramification_index, residue_degree, ring_automorphism,
        ring_homomorphism, ring_monomorphism, .. } := D.core2
  -- @@SCOPE END

  let GALOIS_GROUP_RING_OF_INTEGERS ← prove
    r"!(h:A->B) k l f.
        f IN group_carrier(galois_group(k,l) h)
        ==> IMAGE f (ring_carrier(ring_of_integers l)) SUBSET
            ring_carrier(ring_of_integers l)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_GROUP_RING_AUTOMORPHISM)) THEN REWRITE_TAC [ring_automorphism] THEN DISCH_THEN (MP_TAC o (MATCH_MP RING_ISOMORPHISM_IMP_HOMOMORPHISM)) THEN DISCH_THEN (MP_TAC o (MATCH_MP RING_HOMOMORPHISM_RING_OF_INTEGERS)) THEN SIMP_TAC [ring_homomorphism])

  let DECOMPOSITION_GROUP_RING_OF_INTEGERS ← prove
    r"!(h:A->B) k l Q f.
        f IN group_carrier(decomposition_group(k,l) h Q)
        ==> IMAGE f (ring_carrier(ring_of_integers l)) SUBSET
            ring_carrier(ring_of_integers l)"
    (REWRITE_TAC [DECOMPOSITION_GROUP, IN_ELIM_THM] THEN MESON_TAC [GALOIS_GROUP_RING_OF_INTEGERS])

  let GALOIS_GROUP_RING_OF_INTEGERS_AUTOMORPHISM ← prove
    r"!(h:A->B) k l f.
        f IN group_carrier(galois_group(k,l) h)
        ==> IMAGE f (ring_carrier(ring_of_integers l)) =
            ring_carrier(ring_of_integers l) /\
            ring_isomorphism(ring_of_integers l,ring_of_integers l) f"
    (REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC GALOIS_GROUP_SUBRING_IMAGE THEN MAP_EVERY EXISTS_TAC [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring")] THEN ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBRING] THEN MESON_TAC [GALOIS_GROUP_RING_OF_INTEGERS])

  let GALOIS_GROUP_RING_OF_INTEGERS_IDEAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!f (g:B->B) s a. (!x. g(f x) = x) /\ f a = a
                       ==> (a IN s ==> (IMAGE f s = {a} <=> s = {a}))")
    prove
      r"!(h:A->B) k l f j.
          f IN group_carrier(galois_group(k,l) h) /\
          ring_ideal (ring_of_integers l) j
          ==> ring_ideal (ring_of_integers l) (IMAGE f j) /\
              (IMAGE f j = {ring_0 l} <=> j = {ring_0 l}) /\
              (prime_ideal (ring_of_integers l) (IMAGE f j) <=>
               prime_ideal (ring_of_integers l) j) /\
              (!j'. j' SUBSET ring_carrier(ring_of_integers l)
                    ==> IMAGE f (ideal_prod (ring_of_integers l) j j') =
                        ideal_prod (ring_of_integers l)
                          (IMAGE f j) (IMAGE f j'))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!f. f IN group_carrier(galois_group(k:A ring,l:B ring) h)
          ==> IMAGE f (ring_carrier(ring_of_integers l)) SUBSET
              ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [MESON_TAC [GALOIS_GROUP_RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"ring_of_integers l:B ring"), (← q r"f:B->B")] GALOIS_GROUP_SUBRING_IMAGE) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"ring_of_integers l:B ring"), (← q r"f:B->B"), (← q r"j:B->bool")] GALOIS_GROUP_PRIME_IDEAL_IMAGE) THEN ASM_SIMP_TAC [RING_OF_INTEGERS_SUBRING, RING_IDEAL_IMP_SUBSET] THEN REPEAT STRIP_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP RING_ISOMORPHISM_IMP_HOMOMORPHISM)) THEN DISCH_THEN (ASSUME_TAC o (MATCH_MP RING_HOMOMORPHISM_0)) THEN FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_GROUP_PERMUTES)) THEN DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP PERMUTES_INVERSES)) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"j:B->bool")] IN_RING_IDEAL_0) THEN RULE_ASSUM_TAC (REWRITE_RULE [RING_OF_INTEGERS]) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN MATCH_MP_TAC r1 THEN EXISTS_TAC (← q r"inverse(f:B->B)") THEN ASM_REWRITE_TAC [], MATCH_MP_TAC IDEAL_PROD_EPIMORPHIC_IMAGE THEN ASM_SIMP_TAC [RING_ISOMORPHISM_IMP_EPIMORPHISM, RING_IDEAL_IMP_SUBSET]])

  let GALOIS_GROUP_IMAGE_IDEAL_GENERATED ← prove
    r"!(h:A->B) k l f t.
        f IN group_carrier(galois_group(k,l) h) /\
        t SUBSET ring_carrier(ring_of_integers l)
        ==> IMAGE f (ideal_generated (ring_of_integers l) t) =
            ideal_generated (ring_of_integers l) (IMAGE f t)"
    (REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC IDEAL_GENERATED_BY_EPIMORPHIC_IMAGE THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC RING_ISOMORPHISM_IMP_EPIMORPHISM THEN ASM_MESON_TAC [GALOIS_GROUP_RING_OF_INTEGERS_AUTOMORPHISM])

  let NUMBER_FIELD_GALOIS_GROUP_TRANSITIVE ← prove
    r"!(h:A->B) k l p P P'.
        number_field l /\ galois_extension(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P /\
        prime_ideal (ring_of_integers l) P' /\ IMAGE h p SUBSET P'
        ==> ?f. f IN group_carrier(galois_group(k,l) h) /\ IMAGE f P = P'"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"field k /\ ring_homomorphism(k,l) (h:A->B)") STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_IMP_FIELD_EXTENSION)) THEN SIMP_TAC [field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"P:B->bool")] NUMBER_FIELD_PRIME_IDEAL_ABOVE) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"P':B->bool")] NUMBER_FIELD_PRIME_IDEAL_ABOVE) THEN ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC GALOIS_GROUP_TRANSITIVE_PRIME_IDEALS THEN EXISTS_TAC (← q r"ring_of_integers l:B ring") THEN ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBRING] THEN MESON_TAC [GALOIS_GROUP_RING_OF_INTEGERS])

  let CARD_GALOIS_GROUP_IMAGE_FIBER ← prove
    r"!(h:A->B) k l Q g.
        FINITE(group_carrier(galois_group(k,l) h)) /\
        g IN group_carrier(galois_group(k,l) h)
        ==> CARD {f | f IN group_carrier(galois_group(k,l) h) /\
                      IMAGE f Q = IMAGE g Q} =
            CARD(group_carrier(decomposition_group(k,l) h Q))"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [DECOMPOSITION_GROUP] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC BIJECTIONS_CARD_EQ THEN EXISTS_TAC (← q r"\d:B->B. (g:B->B) o d") THEN EXISTS_TAC (← q r"\f:B->B. inverse(g:B->B) o f") THEN FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_GROUP_PERMUTES)) THEN DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP PERMUTES_INVERSES)) THEN SUBGOAL_THEN (← q r"inverse(g:B->B) o g = I /\ g o inverse g = I") STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM], ALL_TAC] THEN REWRITE_TAC [IN_ELIM_THM, o_ASSOC, I_O_ID, IMAGE_o] THEN ASM_REWRITE_TAC [I_O_ID, (← GSYM IMAGE_o), IMAGE_I] THEN CONJ_TAC THENL [DISJ1_TAC THEN ASM_SIMP_TAC [FINITE_RESTRICT], ALL_TAC] THEN ASM_SIMP_TAC [GALOIS_GROUP_COMPOSE, GALOIS_GROUP_INVERSE] THEN REWRITE_TAC [IMAGE_o] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [(← GSYM IMAGE_o)] THEN ASM_REWRITE_TAC [IMAGE_I])

  let IDEAL_NORM_RESIDUE_IMAGE ← prove
    r"!(h:A->B) k l p Q.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q
        ==> CARD {ring_coset (ring_of_integers l) Q (h a) | a |
                  a IN ring_carrier k /\
                  h a IN ring_carrier(ring_of_integers l)} =
            ideal_norm (ring_of_integers k) p"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN SUBGOAL_THEN (← q r"ring_monomorphism(k:A ring,l:B ring) h") ASSUME_TAC THENL [ASM_MESON_TAC [finite_extension, field_extension], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_homomorphism(ring_of_integers k,ring_of_integers l) (h:A->B)") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"Q:B->bool")] RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring"), (← q r"h:A->B"), (← q r"Q:B->bool")] RESIDUE_DEGREE_QUOTIENT_RING) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"g:(A->bool)->(B->bool)") STRIP_ASSUME_TAC) THEN REWRITE_TAC [ideal_norm] THEN SUBGOAL_THEN (← q r"{ring_coset (ring_of_integers l) Q ((h:A->B) a) | a |
     a IN ring_carrier k /\ h a IN ring_carrier(ring_of_integers l)} =
    IMAGE g (ring_carrier(quotient_ring (ring_of_integers k) p))") SUBST1_TAC THENL [ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, PRIME_IMP_RING_IDEAL] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE_EQ) THEN ASM_REWRITE_TAC [] THEN GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL [UNDISCH_TAC (← q r"ring_monomorphism (quotient_ring (ring_of_integers k) p,
                         quotient_ring (ring_of_integers l) Q)
                        (g:(A->bool)->(B->bool))") THEN REWRITE_TAC [ring_monomorphism] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(Q = {ring_0(l:B ring)})") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~(p = {ring_0(k:A ring)})") THEN REWRITE_TAC [] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [UNDISCH_TAC (← q r"IMAGE (h:A->B) p SUBSET {ring_0 l}") THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_SING] THEN DISCH_TAC THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [PRIME_IDEAL_IMP_SUBSET, RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_HOMOMORPHISM_0) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"ring_monomorphism(k:A ring,l:B ring) h") THEN REWRITE_TAC [ring_monomorphism] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_0], REWRITE_TAC [SING_SUBSET] THEN ASM_MESON_TAC [IN_RING_IDEAL_0, PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring"), (← q r"h:A->B"), (← q r"Q:B->bool")] FINITE_QUOTIENT_RING_HOMOMORPHIC_PREIMAGE) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS_FINITE_QUOTIENT])

  let NUMBER_FIELD_RAMIFICATION_INDEX_CONJUGATE ← prove
    r"!(h:A->B) k l f Q.
        number_field l /\ ring_monomorphism(k,l) h /\
        f IN group_carrier(galois_group(k,l) h) /\
        prime_ideal (ring_of_integers l) Q /\
        ~({x | x IN ring_carrier(ring_of_integers k) /\ h x IN Q} =
          {ring_0 k})
        ==> ramification_index (ring_of_integers k,ring_of_integers l) h
              (IMAGE f Q) =
            ramification_index (ring_of_integers k,ring_of_integers l) h Q"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"dedekind_domain(ring_of_integers l:B ring) /\
    ring_monomorphism(ring_of_integers k,ring_of_integers l) (h:A->B) /\
    ring_monomorphism(ring_of_integers l,ring_of_integers l) (f:B->B) /\
    subring_generated l (ring_carrier(ring_of_integers l)) =
    ring_of_integers l /\
    ring_carrier(ring_of_integers k) SUBSET ring_carrier k /\
    ring_0(ring_of_integers l) = ring_0 l /\
    ring_0(ring_of_integers k) = ring_0 k /\
    (!f. f IN group_carrier(galois_group(k,l) h)
         ==> IMAGE f (ring_carrier(ring_of_integers l)) SUBSET
             ring_carrier(ring_of_integers l))") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_MONOMORPHISM_RING_OF_INTEGERS, RING_OF_INTEGERS_SUBRING, RING_OF_INTEGERS_SUBSET, RING_OF_INTEGERS] THEN CONJ_TAC THENL [ALL_TAC, MESON_TAC [GALOIS_GROUP_RING_OF_INTEGERS]] THEN MATCH_MP_TAC RING_MONOMORPHISM_RING_OF_INTEGERS THEN ASM_MESON_TAC [GALOIS_GROUP_RING_AUTOMORPHISM, ring_automorphism, RING_ISOMORPHISM_IMP_MONOMORPHISM], ALL_TAC] THEN FIRST_ASSUM (MP_TAC o ((MATCH_MP GALOIS_GROUP_PERMUTES) o (checkM (fun th => (do let z3 ← (q r"f IN group_carrier(galois_group(k,l) (h:A->B))"); let z2 ← (do let z1 ← (pure th); pure (concl z1)); pure (z2 == z3)))))) THEN DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP PERMUTES_INVERSES)) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"ring_of_integers l:B ring"), (← q r"f:B->B"), (← q r"Q:B->bool")] GALOIS_GROUP_PRIME_IDEAL_IMAGE) THEN ANTS_TAC THENL [ASM_SIMP_TAC [PRIME_IDEAL_IMP_SUBSET], STRIP_TAC] THEN ABBREV_TAC (← q r"s = ring_of_integers(l:B ring)") THEN ABBREV_TAC (← q r"r = ring_of_integers(k:A ring)") THEN SUBGOAL_THEN (← q r"!x. x IN ring_carrier r ==> (f:B->B) ((h:A->B) x) = h x") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"f:B->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"x:A")] GALOIS_GROUP_FIXES) THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!y. (f:B->B) y IN IMAGE f Q <=> y IN Q") ASSUME_TAC THENL [REWRITE_TAC [IN_IMAGE] THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"?x. x IN ring_carrier r /\ (h:A->B) x IN Q /\ ~(h x = ring_0 l)") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"~({x | x IN ring_carrier r /\ (h:A->B) x IN Q} = {ring_0 k})") THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_SING, NOT_FORALL_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"x:A") THEN ASM_CASES_TAC (← q r"x = ring_0(k:A ring)") THEN ASM_REWRITE_TAC [] THENL [ASM_MESON_TAC [RING_0, PRIME_IMP_RING_IDEAL, IN_RING_IDEAL_0, RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_HOMOMORPHISM_0], STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring")] RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o (MATCH_MP RING_HOMOMORPHISM_0)) THEN UNDISCH_TAC (← q r"ring_monomorphism(k:A ring,l:B ring) h") THEN REWRITE_TAC [ring_monomorphism] THEN DISCH_THEN (MP_TAC o ((SPECL [(← q r"x:A"), (← q r"ring_0 k:A")]) o CONJUNCT2)) THEN ASM_SIMP_TAC [RING_0] THEN ASM SET_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"(h:A->B) x IN IMAGE (f:B->B) Q") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"(h:A->B) x = (f:B->B) (h x)") SUBST1_TAC THENL [ASM_SIMP_TAC [], ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(IMAGE (f:B->B) Q = {ring_0 s})") ASSUME_TAC THENL [DISCH_THEN (fun th => tactic_of do pure (UNDISCH_TAC (← q r"(h:A->B) x IN IMAGE (f:B->B) Q") THEN REWRITE_TAC [th, IN_SING])) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ramification_index (s,s) (f:B->B) (IMAGE f Q) = 1") ASSUME_TAC THENL [REWRITE_TAC [ramification_index] THEN SUBGOAL_THEN (← q r"{y | y IN ring_carrier s /\ (f:B->B) y IN IMAGE f Q} = Q") SUBST1_TAC THENL [ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"Q:B->bool")] PRIME_IDEAL_IMP_SUBSET) THEN ASM_REWRITE_TAC [] THEN SET_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [IDEAL_GENERATED_RING_IDEAL, PRIME_IMP_RING_IDEAL] THEN MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"IMAGE (f:B->B) Q"), (← q r"IMAGE (f:B->B) Q")] IDEAL_VALUATION_PRIME) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"s:B ring"), (← q r"h:A->B"), (← q r"f:B->B"), (← q r"IMAGE (f:B->B) Q")] RAMIFICATION_INDEX_TOWER) THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"{y | y IN ring_carrier s /\ y IN Q} = (Q:B->bool)") SUBST1_TAC THENL [MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"Q:B->bool")] PRIME_IDEAL_IMP_SUBSET) THEN ASM_REWRITE_TAC [] THEN SET_TAC [], ALL_TAC] THEN REWRITE_TAC [MULT_CLAUSES] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [ramification_index] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (← q r"IMAGE (h:A->B)
    {x | x IN ring_carrier r /\ ((f:B->B) o h) x IN IMAGE f Q}") THEN CONJ_TAC THENL [AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM, o_THM] THEN ASM_MESON_TAC [], MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC [IN_ELIM_THM, o_THM]])

  let NUMBER_FIELD_IDEAL_NORM_CONJUGATE ← prove
    r"!(h:A->B) k l f Q.
        number_field l /\ f IN group_carrier(galois_group(k,l) h) /\
        prime_ideal (ring_of_integers l) Q /\ ~(Q = {ring_0 l})
        ==> ideal_norm (ring_of_integers l) (IMAGE f Q) =
            ideal_norm (ring_of_integers l) Q"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN (← q r"ring_homomorphism(l,l) (f:B->B)") ASSUME_TAC THENL [ASM_MESON_TAC [GALOIS_GROUP_RING_AUTOMORPHISM, ring_automorphism, RING_ISOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"f:B->B"), (← q r"k:A ring"), (← q r"l:B ring")] GALOIS_GROUP_PERMUTES) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP PERMUTES_INVERSES)) THEN SUBGOAL_THEN (← q r"inverse(f:B->B) IN group_carrier(galois_group(k,l) (h:A->B))") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"galois_group(k,l) (h:A->B)"), (← q r"f:B->B")] GROUP_INV) THEN ASM_REWRITE_TAC [(← CONJUNCT1 (← CONJUNCT2 (← CONJUNCT2 GALOIS_GROUP)))], ALL_TAC] THEN SUBGOAL_THEN (← q r"!g. g IN group_carrier(galois_group(k,l) (h:A->B))
        ==> IMAGE g (ring_carrier(ring_of_integers l)) SUBSET
            ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [MESON_TAC [GALOIS_GROUP_RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"ring_of_integers l:B ring"), (← q r"f:B->B"), (← q r"Q:B->bool")] GALOIS_GROUP_PRIME_IDEAL_IMAGE) THEN ASM_SIMP_TAC [RING_OF_INTEGERS_SUBRING, PRIME_IDEAL_IMP_SUBSET] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"f:B->B"), (← q r"l:B ring"), (← q r"l:B ring"), (← q r"Q:B->bool"), (← q r"IMAGE (f:B->B) Q")] IDEAL_NORM_RESIDUE_IMAGE) THEN ASM_REWRITE_TAC [SUBSET_REFL] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [ideal_norm] THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, PRIME_IMP_RING_IDEAL] THEN AP_TERM_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"c:B->bool") THEN REWRITE_TAC [IN_ELIM_THM] THEN EQ_TAC THENL [DISCH_THEN (X_CHOOSE_THEN (← q r"b:B") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"inverse(f:B->B) b") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"f:B->B"), (← q r"k:A ring"), (← q r"l:B ring")] GALOIS_GROUP_PERMUTES) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (MATCH_MP PERMUTES_INVERSE)) THEN SIMP_TAC [PERMUTES_IN_IMAGE] THEN DISCH_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET) THEN FIRST_ASSUM ACCEPT_TAC, DISCH_THEN (X_CHOOSE_THEN (← q r"a:B") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"(f:B->B) a") THEN ASM_REWRITE_TAC []])

  let NUMBER_FIELD_IDEAL_NORM_GALOIS_IMAGE ← prove
    r"!(h:A->B) k l f j.
        number_field l /\ f IN group_carrier(galois_group(k,l) h) /\
        ring_ideal (ring_of_integers l) j
        ==> ideal_norm (ring_of_integers l) (IMAGE f j) =
            ideal_norm (ring_of_integers l) j"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"j = {ring_0(l:B ring)}") THENL [ASM_REWRITE_TAC [IMAGE_CLAUSES] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM)) THEN DISCH_THEN (SUBST1_TAC o (MATCH_MP RING_HOMOMORPHISM_0)) THEN REFL_TAC, ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_RING_OF_INTEGERS)) THEN SUBGOAL_THEN (← q r"!j. ring_ideal (ring_of_integers l) j /\
        ~(j = {ring_0(ring_of_integers l)})
        ==> ideal_norm (ring_of_integers l) (IMAGE (f:B->B) j) =
            ideal_norm (ring_of_integers l) j") (fun th => ASM_SIMP_TAC [th, RING_OF_INTEGERS]) THEN MATCH_MP_TAC DEDEKIND_IDEAL_INDUCT THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN CONJ_TAC THENL [ASM_MESON_TAC [GALOIS_GROUP_RING_OF_INTEGERS_AUTOMORPHISM], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"q:B->bool"), (← q r"i:B->bool")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"f:B->B"), (← q r"q:B->bool")] GALOIS_GROUP_RING_OF_INTEGERS_IDEAL) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"f:B->B"), (← q r"i:B->bool")] GALOIS_GROUP_RING_OF_INTEGERS_IDEAL) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, RING_IDEAL_IMP_SUBSET] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_MUL_Q, PRIME_IMP_RING_IDEAL] THEN ASM_MESON_TAC [NUMBER_FIELD_IDEAL_NORM_CONJUGATE])

  let NUMBER_FIELD_DECOMPOSITION_GROUP ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r57 ← TAUT (← q r"p /\ (p ==> q /\ r) /\ s ==> p /\ q /\ r /\ s")
    prove
      r"!(h:A->B) k l p Q.
          number_field l /\ galois_extension(k,l) h /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
          prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q
          ==> CARD(group_carrier(decomposition_group(k,l) h Q)) =
              ramification_index (ring_of_integers k,ring_of_integers l) h Q *
              residue_degree (ring_of_integers k,ring_of_integers l) h Q /\
              CARD(group_carrier(inertia_group(k,l) h (ring_of_integers l) Q)) =
              ramification_index (ring_of_integers k,ring_of_integers l) h Q /\
              CARD {P | prime_ideal (ring_of_integers l) P /\
                        IMAGE h p SUBSET P} *
              ramification_index (ring_of_integers k,ring_of_integers l) h Q *
              residue_degree (ring_of_integers k,ring_of_integers l) h Q =
              extension_degree(k,l) h"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"field k /\ ring_homomorphism(k,l) (h:A->B)") STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_IMP_FIELD_EXTENSION)) THEN SIMP_TAC [field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN SUBGOAL_THEN (← q r"ring_monomorphism(k:A ring,l:B ring) h") ASSUME_TAC THENL [ASM_MESON_TAC [finite_extension, field_extension], ALL_TAC] THEN SUBGOAL_THEN (← q r"subring_generated l (ring_carrier(ring_of_integers l)) =
      ring_of_integers l /\
      (!f. f IN group_carrier(galois_group(k,l) h)
           ==> IMAGE f (ring_carrier(ring_of_integers l)) SUBSET
               ring_carrier(ring_of_integers l)) /\
      (!P. P SUBSET ring_carrier(ring_of_integers l)
           ==> {a | a IN ring_carrier k /\ (h:A->B) a IN P} =
               {x | x IN ring_carrier(ring_of_integers k) /\ h x IN P}) /\
      dedekind_domain(ring_of_integers l) /\
      ring_0(ring_of_integers l) = ring_0 l /\
      ring_0(ring_of_integers k) = ring_0 k") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_OF_INTEGERS_SUBRING, DEDEKIND_RING_OF_INTEGERS, RING_OF_INTEGERS] THEN CONJ_TAC THENL [MESON_TAC [GALOIS_GROUP_RING_OF_INTEGERS], ALL_TAC] THEN X_GEN_TAC (← q r"P:B->bool") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE_EQ) THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_SUBSET) THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM, SUBSET] THEN UNDISCH_TAC (← q r"P SUBSET ring_carrier(ring_of_integers(l:B ring))") THEN REWRITE_TAC [SUBSET] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x. x IN p ==> x IN ring_carrier k /\
                     ((h:A->B) x = ring_0 l <=> x = ring_0 k)") ASSUME_TAC THENL [X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [PRIME_IDEAL_IMP_SUBSET, RING_OF_INTEGERS_SUBSET, SUBSET], ASM_REWRITE_TAC []] THEN UNDISCH_TAC (← q r"ring_monomorphism(k:A ring,l:B ring) h") THEN REWRITE_TAC [ring_monomorphism] THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_HOMOMORPHISM_0)) THEN ASM_MESON_TAC [RING_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"!P. prime_ideal (ring_of_integers l) P /\ IMAGE (h:A->B) p SUBSET P
          ==> ~(P = {ring_0 l}) /\ maximal_ideal (ring_of_integers l) P /\
              FINITE(ring_carrier(quotient_ring (ring_of_integers l) P)) /\
              {a | a IN ring_carrier k /\ h a IN P} = p") ASSUME_TAC THENL [X_GEN_TAC (← q r"P:B->bool") THEN STRIP_TAC THEN MATCH_MP_TAC r57 THEN REPEAT CONJ_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~(p = {ring_0(k:A ring)})") THEN REWRITE_TAC [] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [UNDISCH_TAC (← q r"IMAGE (h:A->B) p SUBSET {ring_0 l}") THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_SING] THEN ASM_MESON_TAC [], REWRITE_TAC [SING_SUBSET] THEN ASM_MESON_TAC [IN_RING_IDEAL_0, PRIME_IMP_RING_IDEAL]], DISCH_TAC THEN CONJ_TAC THENL [MATCH_MP_TAC DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL THEN ASM_REWRITE_TAC [], MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL]], ASM_SIMP_TAC [PRIME_IDEAL_IMP_SUBSET] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"P:B->bool")] RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN ASM_REWRITE_TAC []], ALL_TAC] THEN FIRST_ASSUM (MP_TAC o (← do let c := (← CONJ (← ASSUME (← q r"prime_ideal (ring_of_integers l) (Q:B->bool)")) (← ASSUME (← q r"IMAGE (h:A->B) p SUBSET Q"))); pure (fun th => MATCH_MP th c))) THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN SUBGOAL_THEN (← q r"{P | prime_ideal (ring_of_integers l) P /\ IMAGE (h:A->B) p SUBSET P} =
      {Q' | maximal_ideal (ring_of_integers l) Q' /\
            {a | a IN ring_carrier k /\ h a IN Q'} =
            {a | a IN ring_carrier k /\ h a IN Q}}") ASSUME_TAC THENL [ASM_REWRITE_TAC [] THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"P:B->bool") THEN REWRITE_TAC [IN_ELIM_THM] THEN EQ_TAC THENL [ASM_MESON_TAC [], DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)] THEN ASM_SIMP_TAC [MAXIMAL_IMP_PRIME_IDEAL] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN UNDISCH_TAC (← q r"{a | a IN ring_carrier k /\ (h:A->B) a IN P} = p") THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"x:A"))) THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!P. residue_degree (ring_of_integers k,ring_of_integers l) (h:A->B) P =
          extension_degree
           (subring_generated (quotient_ring (ring_of_integers l) P)
             (IMAGE (ring_coset (ring_of_integers l) P o h)
                    {a | a IN ring_carrier k /\
                         h a IN ring_carrier(ring_of_integers l)}),
            quotient_ring (ring_of_integers l) P) I") ASSUME_TAC THENL [GEN_TAC THEN REWRITE_TAC [residue_degree] THEN ASM_SIMP_TAC [RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE_EQ], ALL_TAC] THEN SUBGOAL_THEN (← q r"{x | x IN ring_carrier(ring_of_integers k) /\ (h:A->B) x IN Q} = p") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"Q:B->bool")] RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool")] DECOMPOSITION_GROUP_INDEX) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM (← (do let z46 ← (pure th); checkM (fun th => (do if ← (do let z47 ← (do let z48 ← (pure th); pure (concl z48)); pure (is_eq z47)) then (do let z49 ← (do let z50 ← (do let z51 ← (pure th); pure (concl z51)); liftExcept (lhs z50)); canM (fun z52 => (do let z53 ← (pure z52); find_termM (fun z54 => (do let z56 ← (pure z54); let z55 ← (q r"prime_ideal:(B)ring->(B->bool)->bool"); pure (z55 == z56))) z53)) z49) else pure false)) z46)))])) THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!P. P IN {P | prime_ideal (ring_of_integers l) P /\
                    IMAGE (h:A->B) p SUBSET P}
          ==> ramification_index (ring_of_integers k,ring_of_integers l) h P =
              ramification_index (ring_of_integers k,ring_of_integers l) h Q /\
              residue_degree (ring_of_integers k,ring_of_integers l) h P =
              residue_degree (ring_of_integers k,ring_of_integers l) h Q") ASSUME_TAC THENL [X_GEN_TAC (← q r"P:B->bool") THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o ((← do let c := (← CONJ (← ASSUME (← q r"prime_ideal (ring_of_integers l) (P:B->bool)")) (← ASSUME (← q r"IMAGE (h:A->B) p SUBSET P"))); pure (fun th => MATCH_MP th c)) o (checkM (fun th => (do if ← (do let z37 ← (do let z38 ← (pure th); pure (concl z38)); pure (is_forall z37)) then (do let z39 ← (do let z40 ← (pure th); pure (concl z40)); canM (fun z41 => (do let z42 ← (pure z41); find_termM (fun z43 => (do let z45 ← (pure z43); let z44 ← (q r"maximal_ideal:(B)ring->(B->bool)->bool"); pure (z44 == z45))) z42)) z39) else pure false))))) THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool"), (← q r"P:B->bool")] GALOIS_GROUP_TRANSITIVE_PRIME_IDEALS) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"f:B->B") (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM))) THEN CONJ_TAC THENL [MATCH_MP_TAC NUMBER_FIELD_RAMIFICATION_INDEX_CONJUGATE THEN ASM_REWRITE_TAC [], ASM_REWRITE_TAC [] THEN MATCH_MP_TAC EXTENSION_DEGREE_RESIDUE_CONJUGATE THEN EXISTS_TAC (← q r"l:B ring") THEN ASM_REWRITE_TAC []], ALL_TAC] THEN FIRST_X_ASSUM (ASSUME_TAC o ((SPEC (← q r"Q:B->bool")) o (checkM (fun th => (do if ← (do if ← (do let z19 ← (do let z20 ← (pure th); pure (concl z20)); pure (is_forall z19)) then (do let z21 ← (do let z22 ← (pure th); pure (concl z22)); canM (fun z23 => (do let z24 ← (pure z23); find_termM (fun t => (do if ← (do let z25 ← (pure t); pure (is_const z25)) then (do let z28 ← (pure "residue_degree"); let z27 ← (do pure (Prod.fst (← (do let z26 ← (pure t); liftExcept (dest_const z26))))); pure (z27 == z28)) else pure false)) z24)) z21) else pure false) then (do pure !(← (do let z29 ← (do let z30 ← (pure th); pure (concl z30)); canM (fun z31 => (do let z32 ← (pure z31); find_termM (fun t => (do if ← (do let z33 ← (pure t); pure (is_const z33)) then (do let z36 ← (pure "ramification_index"); let z35 ← (do pure (Prod.fst (← (do let z34 ← (pure t); liftExcept (dest_const z34))))); pure (z35 == z36)) else pure false)) z32)) z29))) else pure false))))) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool")] CARD_DECOMPOSITION_GROUP) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM (← (do let z7 ← (pure th); checkM (fun th => (do if ← (do let z8 ← (do let z9 ← (pure th); pure (concl z9)); pure (is_eq z8)) then (do let z10 ← (do let z11 ← (do let z12 ← (pure th); pure (concl z12)); liftExcept (lhs z11)); canM (fun z13 => (do let z14 ← (pure z13); find_termM (fun t => (do if ← (do let z15 ← (pure t); pure (is_const z15)) then (do let z18 ← (pure "residue_degree"); let z17 ← (do pure (Prod.fst (← (do let z16 ← (pure t); liftExcept (dest_const z16))))); pure (z17 == z18)) else pure false)) z14)) z10) else pure false)) z7)))])) THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_FUNDAMENTAL_IDENTITY) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"S = {P | prime_ideal (ring_of_integers l) P /\
               IMAGE (h:A->B) p SUBSET P}") THEN ABBREV_TAC (← q r"e = ramification_index (ring_of_integers k,ring_of_integers l)
            (h:A->B) Q") THEN ABBREV_TAC (← q r"fd = residue_degree (ring_of_integers k,ring_of_integers l)
             (h:A->B) Q") THEN SUBGOAL_THEN (← q r"nsum S (\P. ramification_index (ring_of_integers k,ring_of_integers l)
                    (h:A->B) P *
                  residue_degree (ring_of_integers k,ring_of_integers l) h P) =
      CARD S * e * fd") SUBST1_TAC THENL [ASM_SIMP_TAC [(← GSYM NSUM_CONST)] THEN MATCH_MP_TAC NSUM_EQ THEN ASM_SIMP_TAC [], DISCH_TAC] THEN FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_eq z1)) then (do let z6 ← (q r"fd:num"); let z5 ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); liftExcept (lhs z3)); pure (z5 == z6)) else pure false)))) THEN SUBGOAL_THEN (← q r"~(CARD(S:(B->bool)->bool) = 0)") ASSUME_TAC THENL [ASM_SIMP_TAC [CARD_EQ_0, (← GSYM MEMBER_NOT_EMPTY)] THEN EXISTS_TAC (← q r"Q:B->bool") THEN EXPAND_TAC "S" THEN ASM_REWRITE_TAC [IN_ELIM_THM], ALL_TAC] THEN SUBGOAL_THEN (← q r"CARD(group_carrier(decomposition_group(k,l) (h:A->B) Q)) =
      (e:num) * (fd:num)") ASSUME_TAC THENL [MP_TAC (← SPECL [(← q r"CARD(S:(B->bool)->bool)"), (← q r"CARD(group_carrier(decomposition_group(k,l) (h:A->B) Q))"), (← q r"(e:num) * (fd:num)")] EQ_MULT_LCANCEL) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"~(CARD(group_carrier(decomposition_group(k,l) (h:A->B) Q)) = 0)") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"FINITE(group_carrier(decomposition_group(k,l) (h:A->B) Q))") ASSUME_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"group_carrier(galois_group(k,l) (h:A->B))") THEN ASM_SIMP_TAC [FINITE_GALOIS_GROUP] THEN REWRITE_TAC [decomposition_group, GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET], ASM_SIMP_TAC [CARD_EQ_0, (← GSYM MEMBER_NOT_EMPTY)] THEN EXISTS_TAC (← q r"group_id(decomposition_group(k,l) (h:A->B) Q)") THEN REWRITE_TAC [GROUP_ID]], ALL_TAC] THEN MP_TAC (← SPECL [(← q r"CARD(group_carrier(inertia_group(k,l) (h:A->B) (ring_of_integers l) Q))"), (← q r"e:num"), (← q r"fd:num")] EQ_MULT_RCANCEL) THEN SUBGOAL_THEN (← q r"~((fd:num) = 0)") ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC (← q r"~(CARD(group_carrier(decomposition_group(k,l) (h:A->B) Q)) = 0)") THEN ASM_REWRITE_TAC [MULT_CLAUSES], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_MESON_TAC [])

  -- @@RETURN BEGIN
  return { GALOIS_GROUP_RING_OF_INTEGERS, DECOMPOSITION_GROUP_RING_OF_INTEGERS,
           GALOIS_GROUP_RING_OF_INTEGERS_AUTOMORPHISM,
           GALOIS_GROUP_RING_OF_INTEGERS_IDEAL, GALOIS_GROUP_IMAGE_IDEAL_GENERATED,
           NUMBER_FIELD_GALOIS_GROUP_TRANSITIVE, CARD_GALOIS_GROUP_IMAGE_FIBER,
           IDEAL_NORM_RESIDUE_IMAGE, NUMBER_FIELD_RAMIFICATION_INDEX_CONJUGATE,
           NUMBER_FIELD_IDEAL_NORM_CONJUGATE, NUMBER_FIELD_IDEAL_NORM_GALOIS_IMAGE,
           NUMBER_FIELD_DECOMPOSITION_GROUP }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- nf_decomposition.ml phrases from line 745 to 1380                      -/
/- ---------------------------------------------------------------------- -/

structure NfDecomposition02 where
  -- @@FIELDS
  NUMBER_FIELD_INERTIA_FIELD : thm
  NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP : thm
  NUMBER_FIELD_DEDEKIND_VALUATION_CONJUGATE : thm
  NUMBER_FIELD_FROBENIUS_ELEMENT : thm
  DECOMPOSITION_GROUP_FROBENIUS_GENERATED : thm
  NUMBER_FIELD_DECOMPOSITION_GROUP_FROBENIUS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupNfDecomposition02 [HolBase] (D : NfDecompositionDeps) (BNfDecomposition01 : NfDecomposition01) :
    ExceptT String IO NfDecomposition02 := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_MESON_TAC, MESON, MESON_TAC, SET_RULE, SET_TAC, TAUT, .. } := D
  let { CARD_DECOMPOSITION_GROUP, CARD_EQ_0, CARD_SING, CARD_SUBSET_EQ,
        CARRIER_SUBFIELD_GENERATED_SUBFIELD, DECOMPOSITION_GROUP,
        DECOMPOSITION_GROUP_IMAGE_RING_COSET, DECOMPOSITION_GROUP_RESIDUE_EPIMORPHISM,
        DECOMPOSITION_GROUP_RESIDUE_HOMOMORPHISM, DEDEKIND_RING_OF_INTEGERS,
        DEDEKIND_VALUATION, EQ_MULT_LCANCEL, EXISTS_UNIQUE_THM, EXTENSION,
        FIELD_IMP_INTEGRAL_DOMAIN, FIELD_IMP_NONTRIVIAL_RING, FIELD_QUOTIENT_RING,
        FIELD_RING_HOMOMORPHISM_MONOMORPHISM, FIELD_SUBFIELD_GENERATED,
        FINITE_GALOIS_GROUP, FINITE_IMAGE, FINITE_INTEGRAL_DOMAIN_IMP_FIELD,
        FINITE_SUBRING_GENERATED, FINITE_SUBSET, FORALL_IN_IMAGE, FROBENIUS_ELEMENT,
        FROBENIUS_ELEMENT_CONJUGATE, FUN_EQ_THM, GALOIS_EXTENSION_SUBFIELD_GENERATED,
        GALOIS_GROUP_FINITE_FIELD, GALOIS_GROUP_FIXED_FIELD, GALOIS_GROUP_PERMUTES,
        GALOIS_GROUP_PRIME_IDEAL_IMAGE, GALOIS_GROUP_RING_AUTOMORPHISM,
        GALOIS_IMP_FIELD_EXTENSION, GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET,
        GROUP_ELEMENT_ORDER_MONOMORPHIC_IMAGE, GROUP_ELEMENT_ORDER_SUBGROUP_GENERATED,
        GROUP_ID, GROUP_MONOMORPHISM, IDEAL_GENERATED_IMAGE_IDEAL_GENERATED,
        IDEAL_GENERATED_INC_GEN, IDEAL_GENERATED_RING_IDEAL,
        IDEAL_VALUATION_HOMOMORPHIC_IMAGE, IDEAL_VALUATION_PRIME, IMAGE_CLAUSES,
        IMAGE_I, IMP_CONJ, INERTIA_GROUP, INTEGRAL_DOMAIN_MUL_EQ_0,
        INTEGRAL_DOMAIN_SUBRING_GENERATED, IN_ELIM_THM, IN_IMAGE, IN_RING_IDEAL_0,
        IN_SING, I_DEF, I_O_ID, I_THM, .. } := D.core1
  let { MAXIMAL_IMP_RING_IDEAL, MEMBER_NOT_EMPTY, MULT_CLAUSES,
        NUMBER_FIELD_HOMOMORPHIC_PREIMAGE, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_PRIME_IDEAL_ABOVE, NUMBER_FIELD_TOWER_LAW, PERMUTES_INVERSES,
        PERMUTES_IN_IMAGE, PRIME_IDEAL_IMP_SUBSET, PRIME_IMP_RING_IDEAL,
        QUOTIENT_RING_CARRIER, RAMIFICATION_INDEX_TOWER,
        RING_CARRIER_SUBRING_GENERATED_SUBSET, RING_COSET_EQ,
        RING_EPIMORPHISM_IMP_HOMOMORPHISM, RING_EPIMORPHISM_RING_COSET,
        RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_POW,
        RING_HOMOMORPHISM_SUBFIELD_INCLUSION, RING_IDEAL_IDEAL_GENERATED,
        RING_IDEAL_IMP_SUBSET, RING_ISOMORPHISM_IMP_HOMOMORPHISM,
        RING_ISOMORPHISM_IMP_MONOMORPHISM, RING_MONOMORPHISM_EQ_0,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MONOMORPHISM_INCLUSION,
        RING_MONOMORPHISM_INTO_SUBRING, RING_MONOMORPHISM_RING_OF_INTEGERS,
        RING_OF_INTEGERS, RING_OF_INTEGERS_FRACTION_FIELD,
        RING_OF_INTEGERS_PRIME_IDEAL_BELOW, RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION,
        RING_OF_INTEGERS_SUBRING, RING_OF_INTEGERS_SUBSET, RING_POW,
        RING_POW_SUBRING_GENERATED, RING_SUB_SUBRING_GENERATED, SING_SUBSET,
        SUBFIELD_OF_IMP_SUBSET, SUBGROUP_GENERATED_ELEMENT_ORDER,
        SUBGROUP_GENERATED_IDEMPOT_GEN, SUBGROUP_SUBGROUP_GENERATED,
        SUBRING_GENERATED_BY_SUBFIELD_GENERATED, SUBRING_GENERATED_QUOTIENT_RING_IMAGE,
        SUBSET, decomposition_group, field_extension, field_of_fractions,
        finite_extension, group_epimorphism, inertia_group, ramification_index,
        ring_automorphism, ring_homomorphism, subgroup_of, .. } := D.core2
  let { DECOMPOSITION_GROUP_RING_OF_INTEGERS, GALOIS_GROUP_RING_OF_INTEGERS,
        IDEAL_NORM_RESIDUE_IMAGE, NUMBER_FIELD_DECOMPOSITION_GROUP, .. } := BNfDecomposition01
  -- @@SCOPE END

  let NUMBER_FIELD_INERTIA_FIELD ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"f = 1"
    let q2 ← q r"f:num"
    let q3 ← q r"x:num"
    let q4 ← q r"d:num"
    let v5 ← SPECL [q4, q3, q2] EQ_MULT_LCANCEL
    let q6 ← q r"1"
    let q7 ← q r"f:num"
    let q8 ← q r"d:num"
    let v9 ← SPECL [q8, q7, q6] EQ_MULT_LCANCEL
    let p10 ← prove r"!(c:num) (d:num) (f:num) (e:num) (x:num).
          ~(d = 0) /\ d * f = e /\ e = d * x /\ c = d /\ c = d * f
          ==> x = 1 /\ f = 1" (REPEAT GEN_TAC THEN REWRITE_TAC [IMP_CONJ] THEN DISCH_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THEN DISCH_TAC THEN DISCH_THEN SUBST1_TAC THEN MP_TAC v9 THEN MP_TAC v5 THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN REPEAT DISCH_TAC THEN SUBGOAL_THEN q1 SUBST_ALL_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN ASM_MESON_TAC [])
    let lemma := p10
    let q11 ← q r"ramification_index (ring_of_integers k,ring_of_integers l)
                        (h:A->B) Q"
    let q12 ← q r"ramification_index (ring_of_integers M,ring_of_integers l) (I:B->B) Q"
    let q13 ← q r"CARD(G:(B->B)->bool)"
    let q14 ← q r"CARD(G:(B->B)->bool) =
      ramification_index (ring_of_integers M,ring_of_integers l)
                         (I:B->B) Q"
    let v15 ← ASSUME q14
    let q16 ← q r"~(CARD(G:(B->B)->bool) = 0)"
    let v17 ← ASSUME q16
    let q18 ← q r"~(ramification_index (ring_of_integers M,ring_of_integers l) (I:B->B) Q =
      0)"
    let q29 ← q r"Q:B->bool"
    let q30 ← q r"p:A->bool"
    let q31 ← q r"h:A->B"
    let q32 ← q r"l:B ring"
    let q33 ← q r"k:A ring"
    let v34 ← ISPECL [q33, q32, q31, q30, q29] RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION
    let q35 ← q r"Q:B->bool"
    let q36 ← q r"I:B->B"
    let q37 ← q r"h:A->B"
    let q38 ← q r"ring_of_integers l:B ring"
    let q39 ← q r"ring_of_integers M:B ring"
    let q40 ← q r"ring_of_integers k:A ring"
    let v41 ← ISPECL [q40, q39, q38, q37, q36, q35] RAMIFICATION_INDEX_TOWER
    let q63 ← q r"group_carrier(galois_group(k,l) (h:A->B))"
    let q64 ← q r"FINITE (s:A->bool) /\ ~(s = {}) ==> ~(CARD s = 0)"
    let r65 ← MESON [CARD_EQ_0] q64
    let q66 ← q r"~(CARD(G:(B->B)->bool) = 0)"
    let q67 ← q r"Q:B->bool"
    let q68 ← q r"p:A->bool"
    let q69 ← q r"l:B ring"
    let q70 ← q r"k:A ring"
    let q71 ← q r"h:A->B"
    let v72 ← ISPECL [q71, q70, q69, q68, q67] NUMBER_FIELD_DECOMPOSITION_GROUP
    let q73 ← q r"Q:B->bool"
    let q74 ← q r"q:B->bool"
    let q75 ← q r"l:B ring"
    let q76 ← q r"M:B ring"
    let q77 ← q r"I:B->B"
    let v78 ← ISPECL [q77, q76, q75, q74, q73] NUMBER_FIELD_DECOMPOSITION_GROUP
    let q85 ← q r"Q INTER ring_carrier(ring_of_integers M) = (q:B->bool)"
    let q86 ← q r"Q:B->bool"
    let q87 ← q r"q:B->bool"
    let q88 ← q r"I:B->B"
    let q89 ← q r"l:B ring"
    let q90 ← q r"M:B ring"
    let v91 ← ISPECL [q90, q89, q88, q87, q86] RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION
    let q92 ← q r"q:B->bool"
    let q93 ← q r"Q:B->bool"
    let q94 ← q r"I:B->B"
    let q95 ← q r"l:B ring"
    let q96 ← q r"M:B ring"
    let v97 ← ISPECL [q96, q95, q94, q93] RING_OF_INTEGERS_PRIME_IDEAL_BELOW
    let q98 ← q r"(h:A->B) a IN {ring_0(l:B ring)}"
    let q99 ← q r"~(Q = {ring_0(l:B ring)})"
    let q100 ← q r"a:A"
    let q101 ← q r"h:A->B"
    let q102 ← q r"l:B ring"
    let q103 ← q r"k:A ring"
    let v104 ← ISPECL [q103, q102, q101, q100] RING_MONOMORPHISM_EQ_0
    let q105 ← q r"a:A"
    let q106 ← q r"IMAGE (h:A->B) p SUBSET Q"
    let q107 ← q r"(h:A->B) a IN Q /\ ~(h a = ring_0 l)"
    let q108 ← q r"k:A ring"
    let v109 ← ISPEC q108 RING_OF_INTEGERS_SUBSET
    let q110 ← q r"p:A->bool"
    let q111 ← q r"ring_of_integers k:A ring"
    let v112 ← ISPECL [q111, q110] RING_IDEAL_IMP_SUBSET
    let q113 ← q r"(a:A) IN ring_carrier k"
    let q114 ← q r"p:A->bool"
    let q115 ← q r"ring_of_integers k:A ring"
    let v116 ← ISPECL [q115, q114] IN_RING_IDEAL_0
    let q117 ← q r"(z:A) IN s ==> ~(s = {z}) ==> ?a. a IN s /\ ~(a = z)"
    let r118 ← SET_RULE q117
    let q119 ← q r"~(p = {ring_0(k:A ring)})"
    let q120 ← q r"?a:A. a IN p /\ ~(a = ring_0 k)"
    let q121 ← q r"ring_carrier M = (Ti:B->bool)"
    let q122 ← q r"M = subring_generated l (Ti:B->bool)"
    let q123 ← q r"ring_monomorphism(k,M) (h:A->B) /\ ring_monomorphism(M,l) (I:B->B)"
    let q124 ← q r"l:B ring"
    let q125 ← q r"k:A ring"
    let q126 ← q r"h:A->B"
    let v127 ← ISPECL [q126, q125, q124] GALOIS_IMP_FIELD_EXTENSION
    let q128 ← q r"ring_monomorphism(k,l) (h:A->B)"
    let v135 ← CONJUNCT1 INERTIA_GROUP
    let q136 ← q r"Q:B->bool"
    let q137 ← q r"ring_of_integers l:B ring"
    let q138 ← q r"l:B ring"
    let q139 ← q r"M:B ring"
    let q140 ← q r"I:B->B"
    let v141 ← ISPECL [q140, q139, q138, q137, q136] v135
    let q142 ← q r"group_carrier(decomposition_group(M,l) (I:B->B) Q) = G /\
    group_carrier(inertia_group(M,l) (I:B->B) (ring_of_integers l) Q) = G"
    let v143 ← CONJUNCT1 INERTIA_GROUP
    let q144 ← q r"group_carrier(inertia_group(k,l) (h:A->B) (ring_of_integers l) Q) =
    {f | f IN group_carrier(galois_group(k,l) h) /\
         IMAGE f Q = Q /\
         !x. x IN ring_carrier(ring_of_integers l)
             ==> ring_sub l (f x) x IN Q}"
    let q145 ← q r"k:A ring"
    let q146 ← q r"h:A->B"
    let q147 ← q r"galois_extension(M,l) (I:B->B)"
    let q148 ← q r"I:B->B"
    let q149 ← q r"l:B ring"
    let q150 ← q r"M:B ring"
    let v151 ← ISPECL [q150, q149, q148] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE
    let q152 ← q r"number_field(M:B ring)"
    let q153 ← q r"field(l:B ring) /\ field M /\ ring_carrier M = Ti /\
    Ti SUBSET ring_carrier l /\ ring_homomorphism(M,l) (I:B->B)"
    let q154 ← q r"M = subfield_generated l (Ti:B->bool)"
    let q155 ← q r"Ti = fixed_field l (G:(B->B)->bool)"
    let q156 ← q r"G:(B->B)->bool"
    let q157 ← q r"l:B ring"
    let q158 ← q r"k:A ring"
    let q159 ← q r"h:A->B"
    let v160 ← ISPECL [q159, q158, q157, q156] GALOIS_GROUP_FIXED_FIELD
    let q161 ← q r"(G:(B->B)->bool) subgroup_of galois_group(k,l) (h:A->B)"
    let q162 ← q r"finite_extension(k,l) (h:A->B)"
    let q163 ← q r"G = group_carrier(inertia_group(k,l) (h:A->B) (ring_of_integers l) Q)"
    let q164 ← q r"field k /\ ring_homomorphism(k,l) (h:A->B)"
    prove
      r"!(h:A->B) k l p Q.
          number_field l /\ galois_extension(k,l) h /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
          prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q
          ==> ramification_index
               (ring_of_integers k,
                ring_of_integers(subfield_generated l
                 (fixed_field l (group_carrier
                   (inertia_group(k,l) h (ring_of_integers l) Q))))) h
               (Q INTER
                ring_carrier(ring_of_integers(subfield_generated l
                 (fixed_field l (group_carrier
                   (inertia_group(k,l) h (ring_of_integers l) Q)))))) = 1 /\
              residue_degree
               (ring_of_integers(subfield_generated l
                 (fixed_field l (group_carrier
                   (inertia_group(k,l) h (ring_of_integers l) Q)))),
                ring_of_integers l)
               I Q = 1"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN q164 STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_IMP_FIELD_EXTENSION)) THEN SIMP_TAC [field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN ABBREV_TAC q163 THEN SUBGOAL_THEN q162 ASSUME_TAC THENL [ASM_MESON_TAC [NUMBER_FIELD_TOWER_LAW], ALL_TAC] THEN SUBGOAL_THEN q161 ASSUME_TAC THENL [EXPAND_TAC "G" THEN REWRITE_TAC [inertia_group, SUBGROUP_SUBGROUP_GENERATED], ALL_TAC] THEN MP_TAC v160 THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ABBREV_TAC q155 THEN ABBREV_TAC q154 THEN SUBGOAL_THEN q153 STRIP_ASSUME_TAC THENL [EXPAND_TAC "M" THEN ASM_SIMP_TAC [NUMBER_FIELD_IMP_FIELD, FIELD_SUBFIELD_GENERATED, CARRIER_SUBFIELD_GENERATED_SUBFIELD, SUBFIELD_OF_IMP_SUBSET, RING_HOMOMORPHISM_SUBFIELD_INCLUSION], ALL_TAC] THEN SUBGOAL_THEN q152 ASSUME_TAC THENL [MATCH_MP_TAC v151 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN q147 ASSUME_TAC THENL [EXPAND_TAC "M" THEN MATCH_MP_TAC GALOIS_EXTENSION_SUBFIELD_GENERATED THEN MAP_EVERY EXISTS_TAC [q146, q145] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN q144 MP_TAC THENL [MATCH_MP_TAC v143 THEN REWRITE_TAC [RING_OF_INTEGERS_SUBRING, DECOMPOSITION_GROUP_RING_OF_INTEGERS] THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], ASM_REWRITE_TAC [] THEN DISCH_TAC] THEN SUBGOAL_THEN q142 STRIP_ASSUME_TAC THENL [REWRITE_TAC [DECOMPOSITION_GROUP] THEN MP_TAC v141 THEN ANTS_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_SUBRING, DECOMPOSITION_GROUP_RING_OF_INTEGERS] THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL]] THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN MESON_TAC [], ALL_TAC] THEN FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o (checkM (fun th => (do if ← (do let z129 ← (do let z130 ← (pure th); pure (concl z130)); pure (is_eq z129)) then (do let z134 ← (q r"G:(B->B)->bool"); let z133 ← (do let z131 ← (do let z132 ← (pure th); pure (concl z132)); liftExcept (lhs z131)); pure (z133 == z134)) else pure false)))) THEN SUBGOAL_THEN q128 ASSUME_TAC THENL [MP_TAC v127 THEN ASM_SIMP_TAC [field_extension], ALL_TAC] THEN SUBGOAL_THEN q123 STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [SUBGOAL_THEN q122 SUBST1_TAC THENL [EXPAND_TAC "M" THEN UNDISCH_TAC q121 THEN EXPAND_TAC "M" THEN DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [(← SYM th)])) THEN REWRITE_TAC [SUBRING_GENERATED_BY_SUBFIELD_GENERATED], MATCH_MP_TAC RING_MONOMORPHISM_INTO_SUBRING THEN ASM_REWRITE_TAC []], MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN ASM_SIMP_TAC [FIELD_IMP_NONTRIVIAL_RING]], ALL_TAC] THEN SUBGOAL_THEN q120 STRIP_ASSUME_TAC THENL [UNDISCH_TAC q119 THEN MATCH_MP_TAC r118 THEN MP_TAC v116 THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN q113 ASSUME_TAC THENL [MP_TAC v112 THEN MP_TAC v109 THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN REWRITE_TAC [SUBSET] THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN q107 STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [UNDISCH_TAC q106 THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN DISCH_THEN (MP_TAC o (SPEC q105)) THEN ASM_REWRITE_TAC [], MP_TAC v104 THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN q99 ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC q98 THEN ASM_REWRITE_TAC [IN_SING], ALL_TAC] THEN MP_TAC v97 THEN ASM_SIMP_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN REWRITE_TAC [EXISTS_UNIQUE_THM, IMAGE_I] THEN DISCH_THEN ((X_CHOOSE_THEN q92 STRIP_ASSUME_TAC) o CONJUNCT1) THEN MP_TAC v91 THEN ASM_SIMP_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM, IMAGE_I, I_THM] THEN DISCH_TAC THEN SUBGOAL_THEN q85 ASSUME_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z79 ← (do let z80 ← (pure th); pure (concl z80)); pure (is_eq z79)) then (do let z84 ← (q r"q:B->bool"); let z83 ← (do let z81 ← (do let z82 ← (pure th); pure (concl z82)); liftExcept (rand z81)); pure (z83 == z84)) else pure false))))) THEN SET_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN MP_TAC v78 THEN ASM_REWRITE_TAC [IMAGE_I] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o CONJUNCT1)) THEN MP_TAC v72 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o (CONJUNCT1 o CONJUNCT2)) THEN SUBGOAL_THEN q66 ASSUME_TAC THENL [MATCH_MP_TAC r65 THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC q63 THEN ASM_SIMP_TAC [FINITE_GALOIS_GROUP] THEN ASM_MESON_TAC [subgroup_of], FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do if ← (do if ← (do let z42 ← (do let z43 ← (pure th); pure (concl z43)); pure (is_eq z42)) then (do let z47 ← (q r"G:(B->B)->bool"); let z46 ← (do let z44 ← (do let z45 ← (pure th); pure (concl z45)); liftExcept (rand z44)); pure (z46 == z47)) else pure false) then (do let z48 ← (do let z49 ← (pure th); pure (concl z49)); canM (fun z50 => (do let z51 ← (pure z50); find_termM (fun t => (do if ← (do let z52 ← (pure t); pure (is_const z52)) then (do let z55 ← (pure "inertia_group"); let z54 ← (do pure (Prod.fst (← (do let z53 ← (pure t); liftExcept (dest_const z53))))); pure (z54 == z55)) else pure false)) z51)) z48) else pure false) then (do let z56 ← (do let z57 ← (pure th); pure (concl z57)); canM (fun z58 => (do let z59 ← (pure z58); find_termM (fun z60 => (do let z62 ← (pure z60); let z61 ← (q r"k:A ring"); pure (z61 == z62))) z59)) z56) else pure false))))) THEN MESON_TAC [GROUP_ID, MEMBER_NOT_EMPTY]], ALL_TAC] THEN MP_TAC v41 THEN ASM_SIMP_TAC [RING_MONOMORPHISM_RING_OF_INTEGERS, DEDEKIND_RING_OF_INTEGERS, I_O_ID, I_THM, RING_OF_INTEGERS] THEN DISCH_TAC THEN MP_TAC v34 THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do if ← (do let z19 ← (do let z20 ← (pure th); pure (concl z20)); pure (is_imp z19)) then (do let z21 ← (do let z22 ← (pure th); pure (concl z22)); canM (fun z23 => (do let z24 ← (pure z23); find_termM (fun t => (do if ← (do let z25 ← (pure t); pure (is_const z25)) then (do let z28 ← (pure "ramification_index"); let z27 ← (do pure (Prod.fst (← (do let z26 ← (pure t); liftExcept (dest_const z26))))); pure (z27 == z28)) else pure false)) z24)) z21) else pure false)))) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN q18 ASSUME_TAC THENL [MP_TAC v17 THEN MP_TAC v15 THEN ARITH_TAC, ALL_TAC] THEN MATCH_MP_TAC lemma THEN MAP_EVERY EXISTS_TAC [q13, q12, q11] THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC)

  let NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP ← prove
    r"!(h:A->B) k l p Q.
        number_field l /\ galois_extension(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q
        ==> (ramification_index (ring_of_integers k,ring_of_integers l) h Q =
             1 <=>
             group_carrier(inertia_group(k,l) h (ring_of_integers l) Q) =
             {I})"
    (REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o (CONJUNCT1 o (CONJUNCT2 o (MATCH_MP NUMBER_FIELD_DECOMPOSITION_GROUP)))) THEN DISCH_THEN (SUBST1_TAC o SYM) THEN FIRST_X_ASSUM STRIP_ASSUME_TAC THEN SUBGOAL_THEN (← q r"field k /\ ring_homomorphism(k,l) (h:A->B)") STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_IMP_FIELD_EXTENSION)) THEN SIMP_TAC [field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN SUBGOAL_THEN (← q r"FINITE(group_carrier
            (inertia_group(k,l) (h:A->B) (ring_of_integers l) Q)) /\
    I IN group_carrier(inertia_group(k,l) h (ring_of_integers l) Q)") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"group_carrier(galois_group(k,l) (h:A->B))") THEN ASM_SIMP_TAC [FINITE_GALOIS_GROUP] THEN REWRITE_TAC [inertia_group, GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET], MP_TAC (← ISPEC (← q r"inertia_group(k,l) (h:A->B) (ring_of_integers l) Q") GROUP_ID) THEN REWRITE_TAC [INERTIA_GROUP]], ALL_TAC] THEN EQ_TAC THENL [ALL_TAC, SIMP_TAC [CARD_SING]] THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN ASM_REWRITE_TAC [SING_SUBSET, CARD_SING])

  let NUMBER_FIELD_DEDEKIND_VALUATION_CONJUGATE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ q /\ (p /\ q ==> r) ==> p /\ q /\ r")
    let r2 ← SET_RULE (← q r"(z:B) IN Q ==> ~(Q = {z}) ==> ?y. y IN Q /\ ~(y = z)")
    prove
      r"!(h:A->B) k l f Q x.
          number_field l /\ f IN group_carrier(galois_group(k,l) h) /\
          prime_ideal (ring_of_integers l) Q /\ ~(Q = {ring_0 l}) /\
          x IN ring_carrier l /\ ~(x = ring_0 l)
          ==> dedekind_valuation (ring_of_integers l,l) I (IMAGE f Q) (f x) =
              dedekind_valuation (ring_of_integers l,l) I Q x"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPEC (← q r"l:B ring") RING_OF_INTEGERS_FRACTION_FIELD) THEN ASM_REWRITE_TAC [field_of_fractions, RING_OF_INTEGERS, I_THM] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"x:B")) o (checkM (fun z13 => (do let z14 ← (do let z15 ← (pure z13); pure (concl z15)); pure (is_forall z14)))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:B") (X_CHOOSE_THEN (← q r"c:B") STRIP_ASSUME_TAC)) THEN SUBGOAL_THEN (← q r"ring_homomorphism(l,l) (f:B->B) /\
      ring_monomorphism(ring_of_integers l,ring_of_integers l) f /\
      subring_generated l (ring_carrier(ring_of_integers l)) =
      ring_of_integers l /\
      (!g. g IN group_carrier(galois_group(k,l) (h:A->B))
           ==> IMAGE g (ring_carrier(ring_of_integers l)) SUBSET
               ring_carrier(ring_of_integers l)) /\
      ring_0(ring_of_integers l) = ring_0 l /\
      ring_carrier(ring_of_integers l) SUBSET ring_carrier l") STRIP_ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_SUBRING, RING_OF_INTEGERS, RING_OF_INTEGERS_SUBSET] THEN REPEAT CONJ_TAC THENL [ASM_MESON_TAC [GALOIS_GROUP_RING_AUTOMORPHISM, ring_automorphism, RING_ISOMORPHISM_IMP_HOMOMORPHISM], MATCH_MP_TAC RING_MONOMORPHISM_RING_OF_INTEGERS THEN ASM_MESON_TAC [GALOIS_GROUP_RING_AUTOMORPHISM, ring_automorphism, RING_ISOMORPHISM_IMP_MONOMORPHISM], MESON_TAC [GALOIS_GROUP_RING_OF_INTEGERS]], ALL_TAC] THEN FIRST_ASSUM (MP_TAC o ((MATCH_MP GALOIS_GROUP_PERMUTES) o (checkM (fun th => (do let z12 ← (q r"f IN group_carrier(galois_group(k,l) (h:A->B))"); let z11 ← (do let z10 ← (pure th); pure (concl z10)); pure (z11 == z12)))))) THEN DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP PERMUTES_INVERSES)) THEN SUBGOAL_THEN (← q r"!y:B. (f:B->B) y IN IMAGE f Q <=> y IN Q") ASSUME_TAC THENL [REWRITE_TAC [IN_IMAGE] THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!y. y IN ring_carrier l ==> ((f:B->B) y = ring_0 l <=> y = ring_0 l)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"l:B ring"), (← q r"f:B->B")] RING_HOMOMORPHISM_0) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN EQ_TAC THEN DISCH_TAC THENL [FIRST_X_ASSUM (MP_TAC o ((AP_TERM (← q r"inverse(f:B->B)")) o (checkM (fun th => (do let z9 ← (q r"(f:B->B) y = ring_0 l"); let z8 ← (do let z7 ← (pure th); pure (concl z7)); pure (z8 == z9)))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [(← SYM (← (do let z3 ← (pure th); checkM (fun th => (do let z6 ← (q r"(f:B->B)(ring_0 l) = ring_0 l"); let z5 ← (do let z4 ← (pure th); pure (concl z4)); pure (z5 == z6))) z3)))])) THEN ASM_REWRITE_TAC [], ASM_REWRITE_TAC []], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"ring_of_integers l:B ring"), (← q r"f:B->B"), (← q r"Q:B->bool")] GALOIS_GROUP_PRIME_IDEAL_IMAGE) THEN ANTS_TAC THENL [ASM_SIMP_TAC [PRIME_IDEAL_IMP_SUBSET], STRIP_TAC] THEN SUBGOAL_THEN (← q r"?y. y IN Q /\ ~(y = ring_0(l:B ring))") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"~(Q = {ring_0(l:B ring)})") THEN MATCH_MP_TAC r2 THEN ASM_MESON_TAC [IN_RING_IDEAL_0, PRIME_IMP_RING_IDEAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"(y:B) IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [PRIME_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"prime_ideal (ring_of_integers l) (IMAGE (f:B->B) Q) /\
                  ~(IMAGE f Q = {ring_0 l})") STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (AP_TERM (← q r"\s. (f:B->B) y IN s"))) THEN ASM_SIMP_TAC [IN_SING], ALL_TAC] THEN SUBGOAL_THEN (← q r"{y | y IN ring_carrier(ring_of_integers l) /\ y IN Q} = (Q:B->bool)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool")] PRIME_IDEAL_IMP_SUBSET) THEN ASM_REWRITE_TAC [] THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ramification_index (ring_of_integers l,ring_of_integers l) (f:B->B)
        (IMAGE f Q) = 1") ASSUME_TAC THENL [REWRITE_TAC [ramification_index] THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [IDEAL_GENERATED_RING_IDEAL, PRIME_IMP_RING_IDEAL] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"IMAGE (f:B->B) Q"), (← q r"IMAGE (f:B->B) Q")] IDEAL_VALUATION_PRIME) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!z. z IN ring_carrier(ring_of_integers l) /\ ~(z = ring_0 l)
          ==> ideal_valuation (ring_of_integers l) (IMAGE (f:B->B) Q)
               (ideal_generated (ring_of_integers l) {f z}) =
              ideal_valuation (ring_of_integers l) Q
               (ideal_generated (ring_of_integers l) {z})") ASSUME_TAC THENL [X_GEN_TAC (← q r"z:B") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"ring_of_integers l:B ring"), (← q r"f:B->B"), (← q r"IMAGE (f:B->B) Q"), (← q r"ideal_generated (ring_of_integers l) {z:B}")] IDEAL_VALUATION_HOMOMORPHIC_IMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN DISCH_THEN (MP_TAC o (AP_TERM (← q r"\s. (z:B) IN s"))) THEN ASM_SIMP_TAC [IN_SING, IDEAL_GENERATED_INC_GEN, IN_SING], ALL_TAC] THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"ring_of_integers l:B ring"), (← q r"f:B->B"), (← q r"{z:B}")] IDEAL_GENERATED_IMAGE_IDEAL_GENERATED) THEN ASM_SIMP_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM, SING_SUBSET, IMAGE_CLAUSES], ALL_TAC] THEN SUBGOAL_THEN (← q r"(a:B) IN ring_carrier l /\ (c:B) IN ring_carrier l /\
      ~(a = ring_0 l)") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r1 THEN REPEAT CONJ_TAC THENL [ASM SET_TAC [], ASM SET_TAC [], STRIP_TAC] THEN UNDISCH_TAC (← q r"ring_mul l c x = (a:B)") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_MUL_EQ_0, FIELD_IMP_INTEGRAL_DOMAIN], ALL_TAC] THEN SUBGOAL_THEN (← q r"(f:B->B) x IN ring_carrier l /\
      f a IN ring_carrier(ring_of_integers l) /\
      f c IN ring_carrier(ring_of_integers l) /\
      ~(f a = ring_0 l) /\ ~(f c = ring_0 l) /\
      ring_mul l (f c) (f x) = f a") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [] THEN REPEAT CONJ_TAC THENL [ASM_MESON_TAC [GALOIS_GROUP_PERMUTES, PERMUTES_IN_IMAGE], ASM SET_TAC [], ASM SET_TAC [], UNDISCH_TAC (← q r"ring_mul l c x = (a:B)") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN UNDISCH_TAC (← q r"ring_homomorphism(l:B ring,l) f") THEN SIMP_TAC [ring_homomorphism] THEN ASM_SIMP_TAC []], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"l:B ring"), (← q r"I:B->B"), (← q r"Q:B->bool"), (← q r"x:B"), (← q r"a:B"), (← q r"c:B")] DEDEKIND_VALUATION) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"l:B ring"), (← q r"I:B->B"), (← q r"IMAGE (f:B->B) Q"), (← q r"(f:B->B) x"), (← q r"(f:B->B) a"), (← q r"(f:B->B) c")] DEDEKIND_VALUATION) THEN ASM_REWRITE_TAC [I_THM] THEN REPEAT (DISCH_THEN SUBST1_TAC) THEN ASM_SIMP_TAC [])

  let NUMBER_FIELD_FROBENIUS_ELEMENT ← prove
    r"!(h:A->B) k l p Q.
        number_field l /\ galois_extension(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q /\
        ramification_index (ring_of_integers k,ring_of_integers l) h Q = 1
        ==> frobenius_element (k,l) h (ring_of_integers l) Q
            IN group_carrier(decomposition_group(k,l) h Q) /\
            (!f. f IN group_carrier(galois_group(k,l) h) /\
                 (!x. x IN ring_carrier(ring_of_integers l)
                      ==> ring_sub l (f x)
                           (ring_pow l x (ideal_norm (ring_of_integers k) p))
                          IN Q)
                 <=> f = frobenius_element (k,l) h (ring_of_integers l) Q) /\
            (!f. f IN group_carrier(galois_group(k,l) h)
                 ==> frobenius_element (k,l) h (ring_of_integers l)
                       (IMAGE f Q) =
                     f o frobenius_element (k,l) h (ring_of_integers l) Q o
                     inverse f)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"field k /\ ring_homomorphism(k,l) (h:A->B)") STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_IMP_FIELD_EXTENSION)) THEN SIMP_TAC [field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_PRIME_IDEAL_ABOVE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool")] IDEAL_NORM_RESIDUE_IMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN SUBGOAL_THEN (← q r"subring_generated l (ring_carrier(ring_of_integers l)) =
    ring_of_integers l /\
    (!f. f IN group_carrier(galois_group(k,l) (h:A->B))
         ==> IMAGE f (ring_carrier(ring_of_integers l)) SUBSET
             ring_carrier(ring_of_integers (l:B ring)))") STRIP_ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_SUBRING] THEN MESON_TAC [GALOIS_GROUP_RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool")] FROBENIUS_ELEMENT) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC FROBENIUS_ELEMENT_CONJUGATE THEN ASM_REWRITE_TAC [])

  let DECOMPOSITION_GROUP_FROBENIUS_GENERATED ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r11 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!(h:A->B) k l b Q.
          finite_extension(k,l) h /\ galois_extension(k,l) h /\
          subring_generated l (ring_carrier b) = b /\
          (!f. f IN group_carrier(galois_group(k,l) h)
               ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
          maximal_ideal b Q /\ FINITE(ring_carrier(quotient_ring b Q)) /\
          group_carrier(inertia_group(k,l) h b Q) = {I}
          ==> group_carrier(subgroup_generated (galois_group(k,l) h)
                             {frobenius_element (k,l) h b Q}) =
              group_carrier(decomposition_group(k,l) h Q) /\
              group_element_order (galois_group(k,l) h)
                (frobenius_element (k,l) h b Q) =
              CARD(group_carrier(decomposition_group(k,l) h Q))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!f. f IN group_carrier(decomposition_group(k,l) (h:A->B) Q)
          ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b") ASSUME_TAC THENL [REWRITE_TAC [DECOMPOSITION_GROUP, IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_RING_IDEAL)) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool")] FROBENIUS_ELEMENT) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"Fr = frobenius_element (k,l) (h:A->B) b Q") THEN ABBREV_TAC (← q r"q = CARD {ring_coset b Q ((h:A->B) a) | a |
                a IN ring_carrier k /\ h a IN ring_carrier b}") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o (SPEC (← q r"Fr:B->B")))) THEN REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_carrier b SUBSET ring_carrier l /\
      ring_sub b = ring_sub l /\ ring_pow b = ring_pow (l:B ring)") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"subring_generated l (ring_carrier b) = (b:B ring)") THEN DISCH_THEN (fun th => tactic_of do pure (ONCE_REWRITE_TAC [(← SYM th)])) THEN REWRITE_TAC [RING_CARRIER_SUBRING_GENERATED_SUBSET, RING_SUB_SUBRING_GENERATED, RING_POW_SUBRING_GENERATED], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool")] DECOMPOSITION_GROUP_RESIDUE_EPIMORPHISM) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool")] DECOMPOSITION_GROUP_RESIDUE_HOMOMORPHISM) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool")] CARD_DECOMPOSITION_GROUP) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool")] SUBRING_GENERATED_QUOTIENT_RING_IMAGE) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [ASM_MESON_TAC [finite_extension, field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN ABBREV_TAC (← q r"kP = subring_generated (quotient_ring b Q)
            (IMAGE (ring_coset b Q o (h:A->B))
                   {a | a IN ring_carrier k /\ h a IN ring_carrier b})") THEN ABBREV_TAC (← q r"rho = \f X. if X IN ring_carrier(quotient_ring b Q)
                  then IMAGE (f:B->B) X else X") THEN ASM_REWRITE_TAC [CARD_SING, MULT_CLAUSES] THEN REPEAT DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"I:(B->bool)->(B->bool)"), (← q r"kP:(B->bool)ring"), (← q r"quotient_ring b (Q:B->bool)")] GALOIS_GROUP_FINITE_FIELD) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [field_extension] THEN SUBGOAL_THEN (← q r"field(quotient_ring b (Q:B->bool))") ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_QUOTIENT_RING], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "kP" THEN REWRITE_TAC [(← REWRITE_RULE [(← GSYM I_DEF)] RING_MONOMORPHISM_INCLUSION)] THEN MATCH_MP_TAC FINITE_INTEGRAL_DOMAIN_IMP_FIELD THEN ASM_SIMP_TAC [FINITE_SUBRING_GENERATED, INTEGRAL_DOMAIN_SUBRING_GENERATED, FIELD_IMP_INTEGRAL_DOMAIN], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"frobq = \X. if X IN ring_carrier(quotient_ring b Q)
                then ring_pow (quotient_ring b Q) X q else (X:B->bool)") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(rho:(B->B)->(B->bool)->(B->bool)) Fr = frobq") ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["rho", "frobq"] THEN GEN_REWRITE_TAC id [FUN_EQ_THM] THEN X_GEN_TAC (← q r"X:B->bool") THEN REWRITE_TAC [] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do let z19 ← (q r"X IN ring_carrier(quotient_ring b (Q:B->bool))"); let z18 ← (do let z17 ← (pure th); pure (concl z17)); pure (z18 == z19))))) THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, IN_ELIM_THM] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"x:B") STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"Fr:B->B"), (← q r"x:B")] DECOMPOSITION_GROUP_IMAGE_RING_COSET) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"quotient_ring b (Q:B->bool)"), (← q r"ring_coset b (Q:B->bool)")] RING_HOMOMORPHISM_POW) THEN ASM_SIMP_TAC [RING_EPIMORPHISM_RING_COSET, RING_EPIMORPHISM_IMP_HOMOMORPHISM] THEN DISCH_THEN (MP_TAC o (SPECL [(← q r"x:B"), (← q r"q:num")])) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN SUBGOAL_THEN (← q r"(Fr:B->B) x IN ring_carrier b /\ ring_pow l x q IN ring_carrier b") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"ring_pow b = ring_pow (l:B ring)") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [RING_POW] THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"Fr:B->B")) o (checkM (fun th => (do if ← (do let z12 ← (do let z13 ← (pure th); pure (concl z13)); pure (is_forall z12)) then (do let z15 ← (do let z16 ← (pure th); pure (concl z16)); let z14 ← (q r"galois_group(k:A ring,l:B ring) h"); pure (free_in z14 z15)) else pure false))))) THEN ASM SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"(Fr:B->B) x"), (← q r"ring_pow l x q:B")] RING_COSET_EQ) THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"FINITE(group_carrier(decomposition_group(k,l) (h:A->B) Q)) /\
      FINITE(group_carrier(galois_group(kP,quotient_ring b (Q:B->bool)) I))") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r11 THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"group_carrier(galois_group(k,l) (h:A->B))") THEN ASM_SIMP_TAC [FINITE_GALOIS_GROUP] THEN REWRITE_TAC [DECOMPOSITION_GROUP] THEN SET_TAC [], FIRST_X_ASSUM (MP_TAC o ((GEN_REWRITE_RULE id [group_epimorphism]) o (checkM (fun th => (do let hd ← (do pure (Prod.fst (← (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); pure (strip_comb z5))))); (do if ← (do let z7 ← (pure hd); pure (is_const z7)) then (do let z10 ← (pure "group_epimorphism"); let z9 ← (do pure (Prod.fst (← (do let z8 ← (pure hd); liftExcept (dest_const z8))))); pure (z9 == z10)) else pure false)))))) THEN DISCH_THEN (SUBST1_TAC o (SYM o CONJUNCT2)) THEN SIMP_TAC [FINITE_IMAGE]], ALL_TAC] THEN SUBGOAL_THEN (← q r"group_monomorphism
       (decomposition_group(k,l) (h:A->B) Q,
        galois_group(kP,quotient_ring b (Q:B->bool)) I) rho") ASSUME_TAC THENL [ASM_REWRITE_TAC [GROUP_MONOMORPHISM, DECOMPOSITION_GROUP], ALL_TAC] THEN SUBGOAL_THEN (← q r"group_element_order (decomposition_group(k,l) (h:A->B) Q) Fr =
      extension_degree (kP,quotient_ring b (Q:B->bool)) I") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"rho:(B->B)->(B->bool)->(B->bool)"), (← q r"decomposition_group(k,l) (h:A->B) Q"), (← q r"galois_group(kP,quotient_ring b (Q:B->bool)) I"), (← q r"Fr:B->B")] GROUP_ELEMENT_ORDER_MONOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"galois_group(kP,quotient_ring b (Q:B->bool)) I"), (← q r"frobq:(B->bool)->(B->bool)")] SUBGROUP_GENERATED_ELEMENT_ORDER) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"decomposition_group(k,l) (h:A->B) Q"), (← q r"Fr:B->B")] SUBGROUP_GENERATED_ELEMENT_ORDER) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [decomposition_group] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUBGROUP_GENERATED_IDEMPOT_GEN THEN REWRITE_TAC [(← GSYM decomposition_group)] THEN ASM SET_TAC [], FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z4 ← (q r"group_element_order          (decomposition_group(k,l) (h:A->B) Q) Fr"); let z3 ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); liftExcept (lhand z1)); pure (z3 == z4)))))) THEN REWRITE_TAC [decomposition_group, GROUP_ELEMENT_ORDER_SUBGROUP_GENERATED]])

  let NUMBER_FIELD_DECOMPOSITION_GROUP_FROBENIUS ← prove
    r"!(h:A->B) k l p Q.
        number_field l /\ galois_extension(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q /\
        ramification_index (ring_of_integers k,ring_of_integers l) h Q = 1
        ==> group_carrier(subgroup_generated (galois_group(k,l) h)
                {frobenius_element (k,l) h (ring_of_integers l) Q}) =
            group_carrier(decomposition_group(k,l) h Q) /\
            group_element_order (galois_group(k,l) h)
              (frobenius_element (k,l) h (ring_of_integers l) Q) =
            residue_degree (ring_of_integers k,ring_of_integers l) h Q"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"field k /\ ring_homomorphism(k,l) (h:A->B)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [GALOIS_IMP_FIELD_EXTENSION, field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_PRIME_IDEAL_ABOVE) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_DECOMPOSITION_GROUP) THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN DISCH_THEN (SUBST1_TAC o (SYM o CONJUNCT1)) THEN MATCH_MP_TAC DECOMPOSITION_GROUP_FROBENIUS_GENERATED THEN ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBRING] THEN MESON_TAC [GALOIS_GROUP_RING_OF_INTEGERS])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_INERTIA_FIELD, NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP,
           NUMBER_FIELD_DEDEKIND_VALUATION_CONJUGATE, NUMBER_FIELD_FROBENIUS_ELEMENT,
           DECOMPOSITION_GROUP_FROBENIUS_GENERATED,
           NUMBER_FIELD_DECOMPOSITION_GROUP_FROBENIUS }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- nf_decomposition.ml phrases from line 1413 to 1413                     -/
/- ---------------------------------------------------------------------- -/

structure NfDecomposition03 where
  -- @@FIELDS
  NUMBER_FIELD_FROBENIUS_CONJUGATE_PRIME : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupNfDecomposition03 [HolBase] (D : NfDecompositionDeps) (BNfDecomposition01 : NfDecomposition01) (BNfDecomposition02 : NfDecomposition02) :
    ExceptT String IO NfDecomposition03 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, TAUT, .. } := D
  let { DECOMPOSITION_GROUP, FORALL_IN_IMAGE, GALOIS_GROUP,
        GALOIS_GROUP_PRIME_IDEAL_IMAGE, IN_ELIM_THM, IN_IMAGE, IN_SING, .. } := D.core1
  let { PRIME_IDEAL_IMP_SUBSET, RING_OF_INTEGERS_SUBRING, RING_OF_INTEGERS_SUBSET,
        SING_SUBSET, SUBGROUP_GENERATED_INC, SUBGROUP_GENERATED_MINIMAL, SUBSET,
        UNRAMIFIED_IMP_WEAKLY_UNRAMIFIED, group_conjugation, weakly_unramified, .. } := D.core2
  let { GALOIS_GROUP_RING_OF_INTEGERS, .. } := BNfDecomposition01
  let { NUMBER_FIELD_DECOMPOSITION_GROUP_FROBENIUS, NUMBER_FIELD_FROBENIUS_ELEMENT, .. } := BNfDecomposition02
  -- @@SCOPE END

  let NUMBER_FIELD_FROBENIUS_CONJUGATE_PRIME ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(x:B->B) IN s ==> s SUBSET t ==> x IN t")
    let r2 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    let r5 ← TAUT (← q r"p /\ q /\ (p /\ q ==> r /\ s) ==> p /\ q /\ r /\ s")
    prove
      r"!(h:A->B) k l H p Q g.
          number_field l /\ galois_extension(k,l) h /\
          H subgroup_of galois_group(k,l) h /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
          unramified (ring_of_integers k,ring_of_integers l) h p /\
          prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q /\
          g IN group_carrier(galois_group(k,l) h)
          ==> prime_ideal (ring_of_integers l) (IMAGE g Q) /\
              IMAGE h p SUBSET IMAGE g Q /\
              frobenius_element (k,l) h (ring_of_integers l) (IMAGE g Q) =
              group_conjugation (galois_group(k,l) h) g
                (frobenius_element (k,l) h (ring_of_integers l) Q) /\
              (group_carrier(decomposition_group(k,l) h (IMAGE g Q)) SUBSET H <=>
               group_conjugation (galois_group(k,l) h) g
                 (frobenius_element (k,l) h (ring_of_integers l) Q) IN H)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC r5 THEN REPEAT CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"ring_of_integers l:B ring"), (← q r"g:B->B"), (← q r"Q:B->bool")] GALOIS_GROUP_PRIME_IDEAL_IMAGE) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_OF_INTEGERS_SUBRING, PRIME_IDEAL_IMP_SUBSET] THEN MESON_TAC [GALOIS_GROUP_RING_OF_INTEGERS], ASM_SIMP_TAC []], REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC (← q r"(h:A->B) x") THEN CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN CONV_TAC SYM_CONV THEN UNDISCH_TAC (← q r"g IN group_carrier(galois_group(k,l) (h:A->B))") THEN REWRITE_TAC [GALOIS_GROUP, IN_ELIM_THM] THEN DISCH_THEN (fun z3 => tactic_of do pure (MATCH_MP_TAC (← (do let z4 ← (pure (CONJUNCTS z3)); liftExcept (last z4))))) THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") PRIME_IDEAL_IMP_SUBSET) THEN DISCH_THEN (MP_TAC o (SPEC (← q r"p:A->bool"))) THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_SUBSET) THEN ASM SET_TAC [], STRIP_TAC] THEN SUBGOAL_THEN (← q r"!P. prime_ideal (ring_of_integers l) P /\ IMAGE (h:A->B) p SUBSET P
          ==> ramification_index (ring_of_integers k,ring_of_integers l) h P = 1") ASSUME_TAC THENL [ASM_MESON_TAC [UNRAMIFIED_IMP_WEAKLY_UNRAMIFIED, weakly_unramified], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_FROBENIUS_ELEMENT) THEN ASM_SIMP_TAC [] THEN STRIP_TAC THEN MATCH_MP_TAC r2 THEN CONJ_TAC THENL [ASM_SIMP_TAC [group_conjugation, GALOIS_GROUP], DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"IMAGE (g:B->B) Q")] NUMBER_FIELD_DECOMPOSITION_GROUP_FROBENIUS) THEN ASM_SIMP_TAC [] THEN DISCH_THEN (SUBST1_TAC o (SYM o CONJUNCT1)) THEN FIRST_ASSUM (SUBST1_TAC o SYM) THEN EQ_TAC THENL [MATCH_MP_TAC r1 THEN MATCH_MP_TAC SUBGROUP_GENERATED_INC THEN REWRITE_TAC [IN_SING] THEN REWRITE_TAC [SING_SUBSET] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"IMAGE (g:B->B) Q")] NUMBER_FIELD_FROBENIUS_ELEMENT) THEN ASM_SIMP_TAC [] THEN DISCH_THEN (MP_TAC o CONJUNCT1) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"IMAGE (g:B->B) Q")] (← CONJUNCT1 DECOMPOSITION_GROUP)) THEN DISCH_THEN SUBST1_TAC THEN SIMP_TAC [IN_ELIM_THM], DISCH_TAC THEN MATCH_MP_TAC SUBGROUP_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET]])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_FROBENIUS_CONJUGATE_PRIME }
  -- @@RETURN END

end HolANT.NfDecomposition
